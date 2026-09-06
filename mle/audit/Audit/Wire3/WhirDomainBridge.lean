import Audit.Wire3.GoldilocksDomain
import Audit.Wire3.WhirIntermediate
import Audit.Wire3.WhirPolynomial

/-!
# Actual WHIR domain points and deterministic distinct-index agreement bounds

The source point is WhirIntermediate.domainPoint, the manual Nat-power model
of SpongefishWhirVerify._computeEvalPoints / _glPow. No independently selected
abstract point replaces it: its c0 is proved equal to the existing fixed-domain
transposedPoint's canonical value, and its same raw triple is wrapped in the
constructed GoldilocksExt3Field.Element. The actual WhirTerminal.polynomial
Horner evaluator is retained for both fixed coefficient vectors.

Every injectivity/cardinality/bound theorem states k<=32, equality of the ACTUAL
OpenParams generator to the fixed generator's canonical value, positive coset
dimensions and their product=2^k. Merely shape-valid domain parameters do not
establish these hypotheses. The query domain is a Finset (Fin (2^k)): distinct
bounded indices, NOT a list with repeated samples. The proof counts the image
without losing cardinality, then applies the existing fixed-polynomial theorem.

These are deterministic TWO-FIXED-VECTOR statements, not independence, entropy,
Fiat--Shamir probability, Merkle binding or WHIR/PCS soundness. The actual source
query range and its codewordLength=2^k correspondence, fixed config/protocol
derivation, production root construction, _glPow instruction/word refinement,
ABI/memory/allocation/overflow and source quicksort remain separate boundaries.
-/
namespace Audit.Wire3.WhirDomainBridge
open Audit.Wire3
open GoldilocksExt3Field

attribute [local instance 2000] instPowNat

theorem actual_domain_point_canonical (o : WhirIntermediate.OpenParams) (index : Nat) :
    Arithmetic.Canonical (WhirIntermediate.domainPoint o index) :=
  Arithmetic.fromBase_canonical _

theorem actual_domain_point_base_limbs (o : WhirIntermediate.OpenParams) (index : Nat) :
    (WhirIntermediate.domainPoint o index).c1 = 0 ∧
      (WhirIntermediate.domainPoint o index).c2 = 0 := ⟨rfl,rfl⟩

theorem actual_c0_is_transposed_canonical_value (o : WhirIntermediate.OpenParams) (k : Nat)
    (hg : o.domainGenerator.val = (GoldilocksDomain.generator k).val) (index : Fin (2^k)) :
    (WhirIntermediate.domainPoint o index.val).c0 =
      (GoldilocksDomain.transposedPoint k o.cosetSize o.numCosets index).val := by
  unfold WhirIntermediate.domainPoint Arithmetic.fromBase Arithmetic.reduce
  rw [hg]
  exact (GoldilocksDomain.transposed_point_canonical_value k o.cosetSize o.numCosets index).symm

theorem actual_raw_point_is_same_transposed_base (o : WhirIntermediate.OpenParams) (k : Nat)
    (hg : o.domainGenerator.val = (GoldilocksDomain.generator k).val) (index : Fin (2^k)) :
    WhirIntermediate.domainPoint o index.val =
      ⟨(GoldilocksDomain.transposedPoint k o.cosetSize o.numCosets index).val,0,0⟩ := by
  have h := actual_c0_is_transposed_canonical_value o k hg index
  exact congrArg (fun c0 => Arithmetic.Ext3.mk c0 0 0) h

theorem actual_c0_injective (o : WhirIntermediate.OpenParams) (k : Nat) (hk : k ≤ 32)
    (hg : o.domainGenerator.val = (GoldilocksDomain.generator k).val)
    (hc : 0 < o.cosetSize) (hn : 0 < o.numCosets) (hsize : o.cosetSize*o.numCosets = 2^k) :
    Function.Injective (fun index : Fin (2^k) => (WhirIntermediate.domainPoint o index.val).c0) := by
  intro i j hij
  apply GoldilocksDomain.transposed_canonical_values_injective k o.cosetSize o.numCosets hk hc hn hsize
  simpa only [actual_c0_is_transposed_canonical_value o k hg] using hij

theorem actual_domain_points_injective (o : WhirIntermediate.OpenParams) (k : Nat) (hk : k ≤ 32)
    (hg : o.domainGenerator.val = (GoldilocksDomain.generator k).val)
    (hc : 0 < o.cosetSize) (hn : 0 < o.numCosets) (hsize : o.cosetSize*o.numCosets = 2^k) :
    Function.Injective (fun index : Fin (2^k) => WhirIntermediate.domainPoint o index.val) := by
  intro i j hij
  exact actual_c0_injective o k hk hg hc hn hsize (congrArg Arithmetic.Ext3.c0 hij)

/-- Wrap exactly the actual canonical raw point. This is not a freely chosen
abstract evaluation-point function or a new field embedding assumption. -/
def actualElement (o : WhirIntermediate.OpenParams) (k : Nat) (index : Fin (2^k)) : Element :=
  ⟨⟨WhirIntermediate.domainPoint o index.val,actual_domain_point_canonical o index.val⟩⟩

theorem actual_element_raw_exact (o : WhirIntermediate.OpenParams) (k : Nat) (index : Fin (2^k)) :
    WhirPolynomial.raw (actualElement o k index) = WhirIntermediate.domainPoint o index.val := rfl

theorem actual_elements_injective (o : WhirIntermediate.OpenParams) (k : Nat) (hk : k ≤ 32)
    (hg : o.domainGenerator.val = (GoldilocksDomain.generator k).val)
    (hc : 0 < o.cosetSize) (hn : 0 < o.numCosets) (hsize : o.cosetSize*o.numCosets = 2^k) :
    Function.Injective (actualElement o k) := by
  intro i j hij
  apply actual_domain_points_injective o k hk hg hc hn hsize
  exact congrArg WhirPolynomial.raw hij

theorem actual_point_equality_iff_same_index (o : WhirIntermediate.OpenParams) (k : Nat) (hk : k ≤ 32)
    (hg : o.domainGenerator.val = (GoldilocksDomain.generator k).val)
    (hc : 0 < o.cosetSize) (hn : 0 < o.numCosets) (hsize : o.cosetSize*o.numCosets = 2^k)
    (i j : Fin (2^k)) :
    WhirIntermediate.domainPoint o i.val = WhirIntermediate.domainPoint o j.val ↔ i = j :=
  ⟨fun h => actual_domain_points_injective o k hk hg hc hn hsize h,fun h => congrArg (fun index =>
    WhirIntermediate.domainPoint o index.val) h⟩

def queryPoints (o : WhirIntermediate.OpenParams) (k : Nat) (queries : Finset (Fin (2^k))) : Finset Element :=
  queries.image (actualElement o k)

theorem query_image_card_preserved (o : WhirIntermediate.OpenParams) (k : Nat) (hk : k ≤ 32)
    (hg : o.domainGenerator.val = (GoldilocksDomain.generator k).val)
    (hc : 0 < o.cosetSize) (hn : 0 < o.numCosets) (hsize : o.cosetSize*o.numCosets = 2^k)
    (queries : Finset (Fin (2^k))) : (queryPoints o k queries).card = queries.card :=
  Finset.card_image_of_injective queries (actual_elements_injective o k hk hg hc hn hsize)

theorem query_points_membership_is_actual_image (o : WhirIntermediate.OpenParams) (k : Nat)
    (queries : Finset (Fin (2^k))) (point : Element) :
    point ∈ queryPoints o k queries ↔ ∃ index ∈ queries, actualElement o k index = point :=
  Finset.mem_image

def agreeingIndices (o : WhirIntermediate.OpenParams) (k : Nat)
    (cs ds : List Arithmetic.Ext3) (queries : Finset (Fin (2^k))) : Finset (Fin (2^k)) :=
  queries.filter (fun index => WhirTerminal.polynomial cs (WhirIntermediate.domainPoint o index.val) =
    WhirTerminal.polynomial ds (WhirIntermediate.domainPoint o index.val))

theorem agreeing_indices_membership_exact (o : WhirIntermediate.OpenParams) (k : Nat)
    (cs ds : List Arithmetic.Ext3) (queries : Finset (Fin (2^k))) (index : Fin (2^k)) :
    index ∈ agreeingIndices o k cs ds queries ↔ index ∈ queries ∧
      WhirTerminal.polynomial cs (WhirIntermediate.domainPoint o index.val) =
        WhirTerminal.polynomial ds (WhirIntermediate.domainPoint o index.val) := Finset.mem_filter

theorem agreement_image_is_actual_horner_agreement_set (o : WhirIntermediate.OpenParams) (k : Nat)
    (cs ds : List Arithmetic.Ext3) (queries : Finset (Fin (2^k))) :
    (agreeingIndices o k cs ds queries).image (actualElement o k) =
      WhirPolynomial.rawTerminalAgreementPoints cs ds (queryPoints o k queries) := by
  apply Finset.ext
  intro point
  simp only [agreeingIndices,WhirPolynomial.rawTerminalAgreementPoints,queryPoints,
    Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨index,⟨hi,he⟩,rfl⟩
    exact ⟨⟨index,hi,rfl⟩,he⟩
  · rintro ⟨⟨index,hi,rfl⟩,he⟩
    exact ⟨index,⟨hi,he⟩,rfl⟩

theorem agreement_card_preserved_at_actual_points (o : WhirIntermediate.OpenParams) (k : Nat) (hk : k ≤ 32)
    (hg : o.domainGenerator.val = (GoldilocksDomain.generator k).val)
    (hc : 0 < o.cosetSize) (hn : 0 < o.numCosets) (hsize : o.cosetSize*o.numCosets = 2^k)
    (cs ds : List Arithmetic.Ext3) (queries : Finset (Fin (2^k))) :
    (agreeingIndices o k cs ds queries).card =
      (WhirPolynomial.rawTerminalAgreementPoints cs ds (queryPoints o k queries)).card := by
  have h := Finset.card_image_of_injective (agreeingIndices o k cs ds queries)
    (actual_elements_injective o k hk hg hc hn hsize)
  rw [agreement_image_is_actual_horner_agreement_set] at h
  exact h.symm

/-- Distinct FIXED canonical vectors of the SAME length. Count is over distinct
bounded source indices, evaluated at their actual derived domain points. -/
theorem fixed_canonical_vectors_agree_at_most_length_sub_one_queries
    (o : WhirIntermediate.OpenParams) (k : Nat) (hk : k ≤ 32)
    (hg : o.domainGenerator.val = (GoldilocksDomain.generator k).val)
    (hcoset : 0 < o.cosetSize) (hnum : 0 < o.numCosets) (hsize : o.cosetSize*o.numCosets = 2^k)
    (cs ds : List Arithmetic.Ext3) (hc : ∀ c ∈ cs, Arithmetic.Canonical c)
    (hd : ∀ d ∈ ds, Arithmetic.Canonical d) (hlen : cs.length = ds.length) (hne : cs ≠ ds)
    (queries : Finset (Fin (2^k))) : (agreeingIndices o k cs ds queries).card ≤ cs.length-1 := by
  rw [agreement_card_preserved_at_actual_points o k hk hg hcoset hnum hsize]
  exact WhirPolynomial.fixed_canonical_raw_vectors_agreement_bound cs ds hc hd hlen hne (queryPoints o k queries)

theorem actual_horner_evaluation_is_canonical (o : WhirIntermediate.OpenParams) (index : Nat)
    (cs : List Arithmetic.Ext3) (hc : ∀ c ∈ cs, Arithmetic.Canonical c) :
    Arithmetic.Canonical (WhirTerminal.polynomial cs (WhirIntermediate.domainPoint o index)) := by
  rw [WhirPolynomial.canonical_raw_horner_is_polynomial_eval cs hc
    ⟨WhirIntermediate.domainPoint o index,actual_domain_point_canonical o index⟩]
  exact WhirPolynomial.raw_canonical _

def checkedAgreeingIndices (o : WhirIntermediate.OpenParams) (k : Nat)
    (cs ds : List Arithmetic.Ext3) (queries : Finset (Fin (2^k))) : Finset (Fin (2^k)) :=
  queries.filter (fun index => Arithmetic.eq
    (WhirTerminal.polynomial cs (WhirIntermediate.domainPoint o index.val))
    (WhirTerminal.polynomial ds (WhirIntermediate.domainPoint o index.val)) = true)

theorem checked_agreement_is_raw_equality (o : WhirIntermediate.OpenParams) (k : Nat)
    (cs ds : List Arithmetic.Ext3) (hc : ∀ c ∈ cs, Arithmetic.Canonical c)
    (hd : ∀ d ∈ ds, Arithmetic.Canonical d) (queries : Finset (Fin (2^k))) :
    checkedAgreeingIndices o k cs ds queries = agreeingIndices o k cs ds queries := by
  apply Finset.ext
  intro index
  simp only [checkedAgreeingIndices,agreeingIndices,Finset.mem_filter,
    Arithmetic.canonical_equality_iff (actual_horner_evaluation_is_canonical o index.val cs hc)
      (actual_horner_evaluation_is_canonical o index.val ds hd)]

theorem fixed_canonical_vectors_checked_agreement_bound
    (o : WhirIntermediate.OpenParams) (k : Nat) (hk : k ≤ 32)
    (hg : o.domainGenerator.val = (GoldilocksDomain.generator k).val)
    (hcoset : 0 < o.cosetSize) (hnum : 0 < o.numCosets) (hsize : o.cosetSize*o.numCosets = 2^k)
    (cs ds : List Arithmetic.Ext3) (hc : ∀ c ∈ cs, Arithmetic.Canonical c)
    (hd : ∀ d ∈ ds, Arithmetic.Canonical d) (hlen : cs.length = ds.length) (hne : cs ≠ ds)
    (queries : Finset (Fin (2^k))) : (checkedAgreeingIndices o k cs ds queries).card ≤ cs.length-1 := by
  rw [checked_agreement_is_raw_equality o k cs ds hc hd]
  exact fixed_canonical_vectors_agree_at_most_length_sub_one_queries o k hk hg hcoset hnum hsize cs ds hc hd hlen hne queries

theorem enough_distinct_queries_separate_fixed_vectors
    (o : WhirIntermediate.OpenParams) (k : Nat) (hk : k ≤ 32)
    (hg : o.domainGenerator.val = (GoldilocksDomain.generator k).val)
    (hcoset : 0 < o.cosetSize) (hnum : 0 < o.numCosets) (hsize : o.cosetSize*o.numCosets = 2^k)
    (cs ds : List Arithmetic.Ext3) (hc : ∀ c ∈ cs, Arithmetic.Canonical c)
    (hd : ∀ d ∈ ds, Arithmetic.Canonical d) (hlen : cs.length = ds.length) (hne : cs ≠ ds)
    (queries : Finset (Fin (2^k))) (hq : cs.length-1 < queries.card) :
    ∃ index ∈ queries,
      WhirTerminal.polynomial cs (WhirIntermediate.domainPoint o index.val) ≠
        WhirTerminal.polynomial ds (WhirIntermediate.domainPoint o index.val) := by
  by_contra h
  push_neg at h
  have he : agreeingIndices o k cs ds queries = queries := by
    apply Finset.filter_eq_self.mpr
    exact h
  have hb := fixed_canonical_vectors_agree_at_most_length_sub_one_queries o k hk hg hcoset hnum hsize
    cs ds hc hd hlen hne queries
  rw [he] at hb
  omega

theorem actual_zero_index_is_one (o : WhirIntermediate.OpenParams) :
    WhirIntermediate.domainPoint o 0 = Arithmetic.one := by
  simp [WhirIntermediate.domainPoint,Arithmetic.fromBase,Arithmetic.reduce,Arithmetic.one,Arithmetic.modulus]

theorem empty_query_set_has_no_agreements (o : WhirIntermediate.OpenParams) (k : Nat)
    (cs ds : List Arithmetic.Ext3) : agreeingIndices o k cs ds ∅ = ∅ := rfl

end Audit.Wire3.WhirDomainBridge
