import Audit.Wire3.WhirQuicksort
import Audit.Wire3.WhirSampling
import Mathlib.Data.List.Sort

/-!
# Recursive correctness of the concrete indexed WHIR quicksort runner

The imported executable runner is unchanged. Its first real midpoint-based
swap supplies strict recursive-range decrease; no external sorted-partition
assumption is used. The proved depth budget gives successful execution on all
lists; successful runs are sorted and preserve multiplicities. Only after
these facts are established is equality to WhirSampling.sortReference derived.
Results concern this Nat/List execution, not uint256, Solidity memory, gas,
or a machine-checked source translation. Transcript/sampling/PCS soundness
and the separate dedup loop are not proved by this file.
-/
namespace Audit.Wire3.WhirQuicksortCorrectness
open Audit.Wire3.WhirQuicksort

theorem initial_iteration_strict (xs : List Nat) (lo hi : Nat) (hlt : lo < hi)
    (hhi : hi < xs.length) (result : Transition)
    (h : iteration (xs.getD ((lo+hi)/2) 0) (xs.length+1) ⟨xs,lo,hi⟩ = .ok result) :
    lo < result.state.i ∧ result.state.j < hi := by
  obtain ⟨left,right,hl,hr,hlo,hlmid,hmr,hrhi,_,_⟩ :=
    initial_scans_succeed xs lo hi (by omega) hhi
  have hcross : left ≤ right := by omega
  let out := (xs.set left (xs.getD right 0)).set right (xs.getD left 0)
  have hswap : swapCells xs left right = .ok out :=
    swap_in_bounds_executes xs left right (by omega) (by omega)
  by_cases hz : right = 0
  · have he : Transition.finished ⟨out,left+1,right⟩ = result := by
      simpa only [iteration,hl,hr,except_ok_bind,if_pos hcross,hswap,if_pos hz,
        except_pure,Except.ok.injEq] using h
    subst result
    constructor <;> simp only [Transition.state] <;> omega
  · have he : Transition.again ⟨out,left+1,right-1⟩ = result := by
      simpa only [iteration,hl,hr,except_ok_bind,if_pos hcross,hswap,if_neg hz,
        except_pure,Except.ok.injEq] using h
    subst result
    constructor <;> simp only [Transition.state] <;> omega

theorem source_partition_strict (xs : List Nat) (lo hi fuel : Nat) (hlt : lo < hi)
    (hhi : hi < xs.length) (result : State)
    (h : partition (xs.getD ((lo+hi)/2) 0) (xs.length+1) fuel ⟨xs,lo,hi⟩ = .ok result) :
    lo < result.i ∧ result.j < hi := by
  have ha : lo ≤ hi := by omega
  cases fuel with
  | zero =>
      simp only [partition,if_pos ha] at h
  | succ fuel =>
      cases hit : iteration (xs.getD ((lo+hi)/2) 0) (xs.length+1) ⟨xs,lo,hi⟩ with
      | error err =>
          simp only [partition,if_pos ha,hit,except_error_bind] at h
      | ok next =>
          have hstrict := initial_iteration_strict xs lo hi hlt hhi next hit
          cases next with
          | finished next =>
              have he : next = result := by
                simpa only [partition,if_pos ha,hit,except_ok_bind,except_pure,Except.ok.injEq] using h
              simpa only [Transition.state,he] using hstrict
          | again next =>
              have hn : partition (xs.getD ((lo+hi)/2) 0) (xs.length+1) fuel next = .ok result := by
                simpa only [partition,if_pos ha,hit,except_ok_bind] using h
              have hfacts := partition_success_facts _ _ _ next result hn
              exact ⟨Nat.lt_of_lt_of_le hstrict.1 hfacts.2.1,
                Nat.lt_of_le_of_lt hfacts.2.2.1 hstrict.2⟩

theorem source_recursive_widths_decrease (xs : List Nat) (lo hi fuel : Nat)
    (hlt : lo < hi) (hhi : hi < xs.length) (result : State)
    (h : partition (xs.getD ((lo+hi)/2) 0) (xs.length+1) fuel ⟨xs,lo,hi⟩ = .ok result) :
    result.j-lo < hi-lo ∧ hi-result.i < hi-lo := by
  have hs := source_partition_strict xs lo hi fuel hlt hhi result h
  omega

/-- The explicit recursion-depth fuel is sufficient for every valid array
range. Ordinary examples are not used to establish this general termination. -/
theorem quicksort_total (fuel : Nat) (xs : List Nat) (lo hi : Nat)
    (hhi : hi < xs.length) (hf : hi-lo < fuel) :
    ∃ result, quicksort fuel xs lo hi = .ok result := by
  induction fuel generalizing xs lo hi with
  | zero => omega
  | succ fuel ih =>
      by_cases hc : hi ≤ lo
      · exact ⟨xs,by simp [quicksort,hc]⟩
      · have hlt : lo < hi := by omega
        have hm := middle_pivot_bounds lo hi (by omega)
        have hp := lookup_self xs ((lo+hi)/2) (by omega)
        obtain ⟨state,hs⟩ := source_partition_total xs lo hi (by omega) hhi
        have hwidth := source_recursive_widths_decrease xs lo hi (hi-lo+2) hlt hhi state hs
        have hstrict := source_partition_strict xs lo hi (hi-lo+2) hlt hhi state hs
        have hlen := partition_success_length _ _ _ _ state hs
        change state.buffer.length = xs.length at hlen
        by_cases hleft : lo < state.j
        · obtain ⟨buffer,hl⟩ := ih state.buffer lo state.j (by omega) (by omega)
          have hlen' := quicksort_success_length fuel state.buffer buffer lo state.j hl
          by_cases hright : state.i < hi
          · obtain ⟨result,hr⟩ := ih buffer state.i hi (by omega) (by omega)
            exact ⟨result,by simp only [quicksort,if_neg hc,hp,except_ok_bind,hs,
              if_pos hleft,hl,if_pos hright,hr]⟩
          · exact ⟨buffer,by simp only [quicksort,if_neg hc,hp,except_ok_bind,hs,
              if_pos hleft,hl,if_neg hright]⟩
        · by_cases hright : state.i < hi
          · obtain ⟨result,hr⟩ := ih state.buffer state.i hi (by omega) (by omega)
            exact ⟨result,by simp only [quicksort,if_neg hc,hp,except_ok_bind,hs,
              if_neg hleft,if_pos hright,hr]⟩
          · exact ⟨state.buffer,by simp only [quicksort,if_neg hc,hp,except_ok_bind,hs,
              if_neg hleft,if_neg hright]⟩

theorem full_quicksort_total (xs : List Nat) :
    ∃ result, quicksort (xs.length+1) xs 0 (xs.length-1) = .ok result := by
  cases xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs => exact quicksort_total _ _ _ _ (by simp) (by simp only [List.length_cons]; omega)

theorem frame_trans (lo hi : Nat) (a b c : List Nat)
    (hab : SameOutside lo hi a b) (hbc : SameOutside lo hi b c) :
    SameOutside lo hi a c := fun k hk => (hbc k hk).trans (hab k hk)

theorem frame_widen (lo hi innerLo innerHi : Nat) (a b : List Nat)
    (hl : lo ≤ innerLo) (hh : innerHi ≤ hi) (hf : SameOutside innerLo innerHi a b) :
    SameOutside lo hi a b := by
  intro k hk
  exact hf k (by omega)

theorem quicksort_success_frame (fuel : Nat) (xs result : List Nat) (lo hi : Nat)
    (h : quicksort fuel xs lo hi = .ok result) : SameOutside lo hi xs result := by
  induction fuel generalizing xs result lo hi with
  | zero =>
      by_cases hc : hi ≤ lo
      · have he : xs = result := by simpa only [quicksort,if_pos hc,Except.ok.injEq] using h
        subst result; exact fun _ _ => rfl
      · simp only [quicksort,if_neg hc] at h
  | succ fuel ih =>
      by_cases hc : hi ≤ lo
      · have he : xs = result := by simpa only [quicksort,if_pos hc,Except.ok.injEq] using h
        subst result; exact fun _ _ => rfl
      · cases hp : xs[(lo+hi)/2]? with
        | none => simp only [quicksort,if_neg hc,hp,except_error_bind] at h
        | some pivot =>
            cases hs : partition pivot (xs.length+1) (hi-lo+2) ⟨xs,lo,hi⟩ with
            | error err =>
                simp only [quicksort,if_neg hc,hp,except_ok_bind,hs,except_error_bind] at h
            | ok state =>
                have hframe := partition_success_frame pivot (xs.length+1) (hi-lo+2) lo hi
                  ⟨xs,lo,hi⟩ state (Nat.le_refl _) (Nat.le_refl _) hs
                have hfacts := partition_success_facts _ _ _ _ state hs
                have hli : lo ≤ state.i := hfacts.2.1
                have hjh : state.j ≤ hi := hfacts.2.2.1
                by_cases hleft : lo < state.j
                · cases hl : quicksort fuel state.buffer lo state.j with
                  | error err =>
                      simp only [quicksort,if_neg hc,hp,except_ok_bind,hs,if_pos hleft,hl,except_error_bind] at h
                  | ok buffer =>
                      have hlframe := frame_widen lo hi lo state.j state.buffer buffer
                        (Nat.le_refl _) hjh (ih state.buffer buffer lo state.j hl)
                      by_cases hright : state.i < hi
                      · have hr : quicksort fuel buffer state.i hi = .ok result := by
                          simpa only [quicksort,if_neg hc,hp,except_ok_bind,hs,if_pos hleft,hl,if_pos hright] using h
                        have hrframe := frame_widen lo hi state.i hi buffer result hli (Nat.le_refl _)
                          (ih buffer result state.i hi hr)
                        exact frame_trans _ _ _ _ _ hframe (frame_trans _ _ _ _ _ hlframe hrframe)
                      · have he : buffer = result := by
                          simpa only [quicksort,if_neg hc,hp,except_ok_bind,hs,if_pos hleft,hl,
                            if_neg hright,Except.ok.injEq] using h
                        subst result; exact frame_trans _ _ _ _ _ hframe hlframe
                · by_cases hright : state.i < hi
                  · have hr : quicksort fuel state.buffer state.i hi = .ok result := by
                      simpa only [quicksort,if_neg hc,hp,except_ok_bind,hs,if_neg hleft,if_pos hright] using h
                    have hrframe := frame_widen lo hi state.i hi state.buffer result hli (Nat.le_refl _)
                      (ih state.buffer result state.i hi hr)
                    exact frame_trans _ _ _ _ _ hframe hrframe
                  · have he : state.buffer = result := by
                      simpa only [quicksort,if_neg hc,hp,except_ok_bind,hs,if_neg hleft,
                        if_neg hright,Except.ok.injEq] using h
                    subst result; exact hframe

theorem getD_at (xs : List Nat) (k : Nat) (h : k < xs.length) : xs.getD k 0 = xs[k] := by
  simp only [List.getD_eq_getElem?,List.getElem?_eq_getElem h,Option.getD_some]

theorem frame_prefix (xs result : List Nat) (lo hi : Nat)
    (hlen : result.length = xs.length) (hframe : SameOutside lo hi xs result) :
    result.take lo = xs.take lo := by
  apply List.ext_getElem (by simp only [List.length_take,hlen])
  intro k hkr hkx
  have hkl : k < lo := by simp only [List.length_take] at hkr; omega
  have hb : k < result.length := by simp only [List.length_take] at hkr; omega
  have hb' : k < xs.length := by omega
  rw [← List.getElem_take result hb hkl,← List.getElem_take xs hb' hkl]
  simpa only [getD_at result k hb,getD_at xs k hb'] using hframe k (Or.inl hkl)

theorem frame_suffix (xs result : List Nat) (lo hi : Nat)
    (hlen : result.length = xs.length) (hframe : SameOutside lo hi xs result) :
    result.drop (hi+1) = xs.drop (hi+1) := by
  apply List.ext_getElem (by simp only [List.length_drop,hlen])
  intro k hkr hkx
  have hb : hi+1+k < result.length := by simp only [List.length_drop] at hkr; omega
  have hb' : hi+1+k < xs.length := by omega
  rw [← List.getElem_drop result hb,← List.getElem_drop xs hb']
  simpa only [getD_at result (hi+1+k) hb,getD_at xs (hi+1+k) hb'] using
    hframe (hi+1+k) (Or.inr (by omega))

def slice (xs : List Nat) (lo hi : Nat) : List Nat := (xs.drop lo).take (hi+1-lo)

theorem slice_decompose (xs : List Nat) (lo hi : Nat) (hlo : lo ≤ hi+1) :
    (xs.take lo ++ slice xs lo hi) ++ xs.drop (hi+1) = xs := by
  unfold slice
  rw [← List.take_add]
  have he : lo+(hi+1-lo) = hi+1 := by omega
  rw [he,List.take_append_drop]

theorem slice_perm_of_frame (xs result : List Nat) (lo hi : Nat) (hlo : lo ≤ hi+1)
    (hp : List.Perm result xs) (hf : SameOutside lo hi xs result) :
    List.Perm (slice result lo hi) (slice xs lo hi) := by
  have hpre := frame_prefix xs result lo hi hp.length_eq hf
  have hsuf := frame_suffix xs result lo hi hp.length_eq hf
  have hp' := hp
  rw [← slice_decompose result lo hi hlo,← slice_decompose xs lo hi hlo,
    hpre,hsuf,List.append_assoc,List.append_assoc] at hp'
  exact (List.perm_append_right_iff (xs.drop (hi+1))).mp
    ((List.perm_append_left_iff (xs.take lo)).mp hp')

theorem slice_membership (xs : List Nat) (lo hi value : Nat) :
    value ∈ slice xs lo hi ↔
      ∃ k, lo ≤ k ∧ k ≤ hi ∧ k < xs.length ∧ xs.getD k 0 = value := by
  constructor
  · intro hm
    obtain ⟨j,hj,hv⟩ := List.mem_iff_getElem.mp hm
    have hj' : j < hi+1-lo ∧ j < xs.length-lo := by
      simpa only [slice,List.length_take,List.length_drop,Nat.lt_min] using hj
    have hb : lo+j < xs.length := by omega
    refine ⟨lo+j,by omega,by omega,hb,?_⟩
    rw [getD_at xs (lo+j) hb,List.getElem_drop xs hb,
      List.getElem_take (xs.drop lo) (by simp only [List.length_drop]; omega) hj'.1]
    exact hv
  · rintro ⟨k,hlo,hhi,hb,hv⟩
    have hj : k-lo < (slice xs lo hi).length := by
      simp only [slice,List.length_take,List.length_drop]; omega
    refine List.mem_iff_getElem.mpr ⟨k-lo,hj,?_⟩
    have he : lo+(k-lo) = k := by omega
    rw [getD_at xs k hb] at hv
    change ((xs.drop lo).take (hi+1-lo))[k-lo] = value
    rw [← List.getElem_take (xs.drop lo) (i := k-lo) (j := hi+1-lo)
        (by simp only [List.length_drop]; omega) (by omega),
      ← List.getElem_drop xs (by omega)]
    simpa only [he] using hv

def RangeAll (P : Nat → Prop) (xs : List Nat) (lo hi : Nat) : Prop :=
  ∀ k, lo ≤ k → k ≤ hi → k < xs.length → P (xs.getD k 0)

theorem range_all_perm_frame (P : Nat → Prop) (xs result : List Nat) (lo hi : Nat)
    (hlo : lo ≤ hi+1) (hp : List.Perm result xs) (hf : SameOutside lo hi xs result)
    (hall : RangeAll P xs lo hi) : RangeAll P result lo hi := by
  intro k hkl hkh hkb
  have hm : result.getD k 0 ∈ slice result lo hi :=
    (slice_membership result lo hi _).mpr ⟨k,hkl,hkh,hkb,rfl⟩
  have hm' := (slice_perm_of_frame xs result lo hi hlo hp hf).mem_iff.mp hm
  obtain ⟨j,hjl,hjh,hjb,hv⟩ := (slice_membership xs lo hi _).mp hm'
  rw [← hv]
  exact hall j hjl hjh hjb

theorem quicksort_success_range_all (P : Nat → Prop) (fuel : Nat)
    (xs result : List Nat) (lo hi : Nat) (hlo : lo ≤ hi+1)
    (h : quicksort fuel xs lo hi = .ok result) (hall : RangeAll P xs lo hi) :
    RangeAll P result lo hi :=
  range_all_perm_frame P xs result lo hi hlo (quicksort_success_perm _ _ _ _ _ h)
    (quicksort_success_frame _ _ _ _ _ h) hall

theorem left_reorder_classified (pivot lo hi i j : Nat) (xs result : List Nat)
    (hhi : hi < xs.length) (hlo : lo ≤ j) (hcross : j < i)
    (hc : Classified pivot lo hi ⟨xs,i,j⟩) (hp : List.Perm result xs)
    (hf : SameOutside lo j xs result) : Classified pivot lo hi ⟨result,i,j⟩ := by
  have hall : RangeAll (fun value => value ≤ pivot) xs lo j := by
    intro k hkl hkj _
    exact hc.2.2.1 k hkl (by change k < i; omega) (by have hh := hc.2.1; dsimp at hh; omega)
  have hall' := range_all_perm_frame _ xs result lo j (by omega) hp hf hall
  have hlen := hp.length_eq
  refine ⟨hc.1,hc.2.1,?_,?_⟩
  · intro k hkl hki hkh
    change k < i at hki
    change result.getD k 0 ≤ pivot
    by_cases hkj : k ≤ j
    · exact hall' k hkl hkj (by omega)
    · rw [hf k (Or.inr (by omega))]
      exact hc.2.2.1 k hkl hki hkh
  · intro k hkl hjk hkh
    change j < k at hjk
    change pivot ≤ result.getD k 0
    rw [hf k (Or.inr hjk)]
    exact hc.2.2.2 k hkl hjk hkh

theorem right_reorder_classified (pivot lo hi i j : Nat) (xs result : List Nat)
    (hhi : hi < xs.length) (hih : i ≤ hi) (hcross : j < i)
    (hc : Classified pivot lo hi ⟨xs,i,j⟩) (hp : List.Perm result xs)
    (hf : SameOutside i hi xs result) : Classified pivot lo hi ⟨result,i,j⟩ := by
  have hall : RangeAll (fun value => pivot ≤ value) xs i hi := by
    intro k hik hkh _
    exact hc.2.2.2 k (by have hh := hc.1; dsimp at hh; omega) (by change j < k; omega) hkh
  have hall' := range_all_perm_frame _ xs result i hi (by omega) hp hf hall
  have hlen := hp.length_eq
  refine ⟨hc.1,hc.2.1,?_,?_⟩
  · intro k hkl hki hkh
    change k < i at hki
    change result.getD k 0 ≤ pivot
    rw [hf k (Or.inl hki)]
    exact hc.2.2.1 k hkl hki hkh
  · intro k hkl hjk hkh
    change j < k at hjk
    change pivot ≤ result.getD k 0
    by_cases hki : i ≤ k
    · exact hall' k hki hkh (by omega)
    · rw [hf k (Or.inl (by omega))]
      exact hc.2.2.2 k hkl hjk hkh

def RangeSorted (xs : List Nat) (lo hi : Nat) : Prop :=
  ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → xs.getD a 0 ≤ xs.getD b 0

theorem small_range_sorted (xs : List Nat) (lo hi : Nat) (h : hi ≤ lo) :
    RangeSorted xs lo hi := by
  intro a b hla hab hbh
  have he : a = b := by omega
  rw [he]

theorem left_sorted_after_right_frame (xs result : List Nat) (lo j i hi : Nat)
    (hcross : j < i) (hf : SameOutside i hi xs result) (hs : RangeSorted xs lo j) :
    RangeSorted result lo j := by
  intro a b hla hab hbj
  rw [hf a (Or.inl (by omega)),hf b (Or.inl (by omega))]
  exact hs a b hla hab hbj

theorem sorted_of_classified_halves (pivot lo hi i j : Nat) (xs : List Nat)
    (hc : Classified pivot lo hi ⟨xs,i,j⟩)
    (hleft : RangeSorted xs lo j) (hright : RangeSorted xs i hi) :
    RangeSorted xs lo hi := by
  intro a b hla hab hbh
  by_cases hbj : b ≤ j
  · exact hleft a b hla hab hbj
  · by_cases hia : i ≤ a
    · exact hright a b hia hab hbh
    · exact Nat.le_trans (hc.2.2.1 a hla (by dsimp; omega) (by omega))
        (hc.2.2.2 b (by omega) (by dsimp; omega) hbh)

/-- Sortedness is proved by induction on the very same fuel-indexed recursive
execution. The smaller calls retain their actual frames and permutations. -/
theorem quicksort_success_sorted (fuel : Nat) (xs result : List Nat) (lo hi : Nat)
    (hhi : hi < xs.length) (h : quicksort fuel xs lo hi = .ok result) :
    RangeSorted result lo hi := by
  induction fuel generalizing xs result lo hi with
  | zero =>
      by_cases hc : hi ≤ lo
      · have he : xs = result := by simpa only [quicksort,if_pos hc,Except.ok.injEq] using h
        subst result; exact small_range_sorted xs lo hi hc
      · simp only [quicksort,if_neg hc] at h
  | succ fuel ih =>
      by_cases hc : hi ≤ lo
      · have he : xs = result := by simpa only [quicksort,if_pos hc,Except.ok.injEq] using h
        subst result; exact small_range_sorted xs lo hi hc
      · have hlo : lo ≤ hi := by omega
        have hm := middle_pivot_bounds lo hi hlo
        have hp := lookup_self xs ((lo+hi)/2) (by omega)
        cases hs : partition (xs.getD ((lo+hi)/2) 0) (xs.length+1) (hi-lo+2) ⟨xs,lo,hi⟩ with
        | error err =>
            simp only [quicksort,if_neg hc,hp,except_ok_bind,hs,except_error_bind] at h
        | ok state =>
            have hcl := partition_success_classified _ _ _ lo hi _ state
              (initial_sentinels xs lo hi hlo hhi) (by dsimp; omega)
              (initial_classified xs _ lo hi) hs
            have hfacts := partition_success_facts _ _ _ _ state hs
            have hcross : state.j < state.i := hfacts.2.2.2
            have hlen : state.buffer.length = xs.length := hfacts.1.length_eq
            have hjh : state.j ≤ hi := hfacts.2.2.1
            let leftRun := if lo < state.j then quicksort fuel state.buffer lo state.j else .ok state.buffer
            have hexec : quicksort (fuel+1) xs lo hi =
                (leftRun >>= fun buffer => if state.i < hi then quicksort fuel buffer state.i hi else .ok buffer) := by
              by_cases hleft : lo < state.j
              · simp only [leftRun,quicksort,if_neg hc,hp,except_ok_bind,hs,if_pos hleft]
              · simp only [leftRun,quicksort,if_neg hc,hp,except_ok_bind,hs,if_neg hleft]
            rw [hexec] at h
            cases hl : leftRun with
            | error err =>
                rw [hl,except_error_bind] at h
                cases h
            | ok buffer =>
                rw [hl,except_ok_bind] at h
                have hmid : Classified (xs.getD ((lo+hi)/2) 0) lo hi ⟨buffer,state.i,state.j⟩ ∧
                    RangeSorted buffer lo state.j ∧ buffer.length = xs.length := by
                  by_cases hleft : lo < state.j
                  · have hl' : quicksort fuel state.buffer lo state.j = .ok buffer := by
                      simpa only [leftRun,if_pos hleft] using hl
                    have hperm := quicksort_success_perm _ _ _ _ _ hl'
                    have hframe := quicksort_success_frame _ _ _ _ _ hl'
                    exact ⟨left_reorder_classified _ _ _ _ _ state.buffer buffer (by omega)
                      (by omega) hcross hcl hperm hframe,
                      ih state.buffer buffer lo state.j (by omega) hl',hperm.length_eq.trans hlen⟩
                  · have he : state.buffer = buffer := by
                      simpa only [leftRun,if_neg hleft,Except.ok.injEq] using hl
                    subst buffer
                    exact ⟨hcl,small_range_sorted _ _ _ (by omega),hlen⟩
                by_cases hright : state.i < hi
                · have hr : quicksort fuel buffer state.i hi = .ok result := by
                    simpa only [if_pos hright] using h
                  have hperm := quicksort_success_perm _ _ _ _ _ hr
                  have hframe := quicksort_success_frame _ _ _ _ _ hr
                  have hclfinal := right_reorder_classified _ _ _ _ _ buffer result (by omega)
                    (by omega) hcross hmid.1 hperm hframe
                  have hleftfinal := left_sorted_after_right_frame buffer result lo state.j state.i hi
                    hcross hframe hmid.2.1
                  have hrightfinal := ih buffer result state.i hi (by omega) hr
                  exact sorted_of_classified_halves _ _ _ _ _ result hclfinal hleftfinal hrightfinal
                · have he : buffer = result := by
                    simpa only [if_neg hright,Except.ok.injEq] using h
                  subst result
                  exact sorted_of_classified_halves _ _ _ _ _ buffer hmid.1 hmid.2.1
                    (small_range_sorted _ _ _ (by omega))

theorem full_quicksort_success_sorted (fuel : Nat) (xs result : List Nat)
    (h : quicksort fuel xs 0 (xs.length-1) = .ok result) :
    List.Sorted (fun a b : Nat => a ≤ b) result := by
  cases xs with
  | nil =>
      have he : [] = result := by cases fuel <;> simpa only [quicksort,List.length_nil,Nat.zero_sub,
        Nat.le_refl,if_true,Except.ok.injEq] using h
      subst result
      exact List.Pairwise.nil
  | cons x xs =>
      have hhi : (x::xs).length-1 < (x::xs).length := by simp
      have hs := quicksort_success_sorted fuel (x::xs) result 0 ((x::xs).length-1) hhi h
      have hlen := quicksort_success_length _ _ _ _ _ h
      apply List.pairwise_iff_getElem.mpr
      intro a b ha hb hab
      have hv := hs a b (Nat.zero_le _) (by omega) (by omega)
      simpa only [getD_at result a ha,getD_at result b hb] using hv

theorem reference_insert_perm (value : Nat) (xs : List Nat) :
    List.Perm (Audit.Wire3.WhirSampling.insertReference value xs) (value::xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      by_cases hx : value ≤ x
      · simpa only [Audit.Wire3.WhirSampling.insertReference,if_pos hx] using List.Perm.refl (value::x::xs)
      · simpa only [Audit.Wire3.WhirSampling.insertReference,if_neg hx] using
          (List.Perm.cons x ih).trans (List.Perm.swap _ _ _)

theorem reference_sort_perm (xs : List Nat) :
    List.Perm (Audit.Wire3.WhirSampling.sortReference xs) xs := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      exact (reference_insert_perm x (Audit.Wire3.WhirSampling.sortReference xs)).trans (List.Perm.cons x ih)

theorem reference_nondecreasing_is_sorted (xs : List Nat)
    (h : Audit.Wire3.WhirSampling.Nondecreasing xs) :
    List.Sorted (fun a b : Nat => a ≤ b) xs := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons x xs ih => exact List.pairwise_cons.mpr ⟨h.1,ih h.2⟩

/-- Both algorithms are kept distinct. Equality follows only after the real
indexed runner's sortedness and full multiplicity preservation have been proved. -/
theorem full_quicksort_success_eq_reference (fuel : Nat) (xs result : List Nat)
    (h : quicksort fuel xs 0 (xs.length-1) = .ok result) :
    result = Audit.Wire3.WhirSampling.sortReference xs := by
  apply List.eq_of_perm_of_sorted (r := fun a b : Nat => a ≤ b)
    ((quicksort_success_perm _ _ _ _ _ h).trans (reference_sort_perm xs).symm)
    (full_quicksort_success_sorted fuel xs result h)
  exact reference_nondecreasing_is_sorted _ (Audit.Wire3.WhirSampling.sort_reference_sorted xs)

/-- General executable equality, including the empty and singleton cases,
with a proved sufficient recursion fuel. It does not rely on large-fuel tests. -/
theorem full_quicksort_exact_reference (xs : List Nat) :
    quicksort (xs.length+1) xs 0 (xs.length-1) =
      .ok (Audit.Wire3.WhirSampling.sortReference xs) := by
  obtain ⟨result,hr⟩ := full_quicksort_total xs
  have he := full_quicksort_success_eq_reference _ xs result hr
  simpa only [he] using hr

theorem complete_empty_example : quicksort 1 [] 0 0 = .ok [] := rfl

theorem complete_duplicate_example :
    quicksort 7 [3,1,3,2,1,3] 0 5 = .ok [1,1,2,3,3,3] := rfl

theorem complete_subrange_example :
    quicksort 3 [9,3,2,1,8] 1 3 = .ok [9,1,2,3,8] := rfl

end Audit.Wire3.WhirQuicksortCorrectness
