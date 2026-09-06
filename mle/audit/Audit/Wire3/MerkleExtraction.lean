import Audit.Wire3.Merkle

/-!
Path extraction from the SAME successful layered Merkle execution, not from
separately supplied single-path witnesses. The paired and hint-read branches
both give each input node a parent edge; iteration gives a depth-sized path
to the root actually checked by Merkle.verify. No hash injectivity assumption
is made. Source: SpongefishMerkle.verify/_processLayerInto at becfe98e.

Functional-list execution is the existing manually translated model. This
does not prove Yul/memory refinement, leaf-row serialization injectivity,
random-oracle sampling, or a collision probability. The collision conclusion
is a concrete unequal input pair for the supplied deterministic Hash.
-/
namespace Audit.Wire3.MerkleExtraction
open Merkle

theorem sibling_index_same_parent (index : Nat) : (Nat.xor index 1) / 2 = index / 2 := by
  change (index ^^^ 1) / 2 = index / 2
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_succ 1]
  simp [Nat.testBit_succ]

theorem sibling_index_opposite_parity (index : Nat) :
    (Nat.xor index 1) % 2 = 1 - index % 2 := by
  change (index ^^^ 1) % 2 = 1 - index % 2
  have h := Nat.testBit_xor index 1 0
  rcases Nat.mod_two_eq_zero_or_one index with hi | hi <;>
    rcases Nat.mod_two_eq_zero_or_one (index ^^^ 1) with hs | hs <;>
    simp_all [Nat.testBit_zero]

theorem paired_parent_digest (hash : Hash) (index : Nat) (a b : Digest) :
    parent hash (Nat.xor index 1) b a = parent hash index a b := by
  unfold parent parentInput
  rw [sibling_index_opposite_parity]
  rcases Nat.mod_two_eq_zero_or_one index with hi | hi <;> simp [hi]

/-- Every node gets an edge from this actual processLayer execution, including
the second node of a pair (which consumes no separate hint). -/
theorem successful_layer_gives_each_parent (hash : Hash) (hints : Bytes)
    (nodes parents : List Node) (offset next : Nat)
    (h : processLayer hash hints nodes offset = some (parents,next)) :
    ∀ node ∈ nodes, ∃ p ∈ parents, ∃ sibling : Digest,
      p.index = node.index / 2 ∧ p.digest = parent hash node.index node.digest sibling := by
  cases nodes with
  | nil => simp
  | cons a rest =>
      cases rest with
      | nil =>
          cases hr : readDigest hints offset with
          | none => simp [processLayer,hr] at h
          | some pair =>
              rcases pair with ⟨sibling,afterRead⟩
              simp only [processLayer,hr,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              intro node hn
              have hn : node = a := by simpa using hn
              subst node
              exact ⟨merged hash a sibling,by simp,sibling,rfl,rfl⟩
      | cons b tail =>
          by_cases hp : b.index = Nat.xor a.index 1
          · cases ht : processLayer hash hints tail offset with
            | none => simp [processLayer,hp,ht] at h
            | some pair =>
                rcases pair with ⟨remaining,afterLayer⟩
                simp only [processLayer,hp,↓reduceIte,ht,bind,Option.bind,pure,
                  Option.some.injEq,Prod.mk.injEq] at h
                rcases h with ⟨rfl,rfl⟩
                intro node hn
                rcases List.mem_cons.mp hn with heq | hn
                · subst node
                  exact ⟨merged hash a b.digest,by simp,b.digest,rfl,rfl⟩
                rcases List.mem_cons.mp hn with heq | hn
                · subst node
                  refine ⟨merged hash a b.digest,by simp,a.digest,?_,?_⟩
                  · simp only [merged,hp,sibling_index_same_parent]
                  · simp only [merged,hp,paired_parent_digest]
                obtain ⟨p,hp',s,hi,hd⟩ := successful_layer_gives_each_parent hash hints tail remaining
                  offset afterLayer ht node hn
                exact ⟨p,List.mem_cons_of_mem _ hp',s,hi,hd⟩
          · cases hr : readDigest hints offset with
            | none => simp [processLayer,hp,hr] at h
            | some pair =>
                rcases pair with ⟨sibling,afterRead⟩
                cases ht : processLayer hash hints (b :: tail) afterRead with
                | none => simp [processLayer,hp,hr,ht] at h
                | some pair =>
                    rcases pair with ⟨remaining,afterLayer⟩
                    simp only [processLayer,hp,↓reduceIte,hr,ht,bind,Option.bind,pure,
                      Option.some.injEq,Prod.mk.injEq] at h
                    rcases h with ⟨rfl,rfl⟩
                    intro node hn
                    rcases List.mem_cons.mp hn with heq | hn
                    · subst node
                      exact ⟨merged hash a sibling,by simp,sibling,rfl,rfl⟩
                    obtain ⟨p,hp',s,hi,hd⟩ := successful_layer_gives_each_parent hash hints (b :: tail)
                      remaining afterRead afterLayer ht node hn
                    exact ⟨p,List.mem_cons_of_mem _ hp',s,hi,hd⟩
termination_by nodes.length

/-- Extraction composes over all layers, without requiring any fresh hint or
assuming a single-path proof that was not part of the multiproof execution. -/
theorem successful_layers_extract_paths (hash : Hash) (hints : Bytes) (depth : Nat)
    (nodes finalNodes : List Node) (offset next : Nat)
    (h : runLayers hash hints depth nodes offset = some (finalNodes,next)) :
    ∀ node ∈ nodes, ∃ last ∈ finalNodes, ∃ siblings : List Digest,
      siblings.length = depth ∧ pathRoot hash node.index node.digest siblings = last.digest := by
  induction depth generalizing nodes offset with
  | zero =>
      cases h
      intro node hn
      exact ⟨node,hn,[],rfl,rfl⟩
  | succ depth ih =>
      cases hl : processLayer hash hints nodes offset with
      | none => simp [runLayers,hl] at h
      | some pair =>
          rcases pair with ⟨parents,afterLayer⟩
          simp only [runLayers,hl,bind,Option.bind] at h
          intro node hn
          obtain ⟨p,hp,s,hi,hd⟩ := successful_layer_gives_each_parent hash hints nodes parents
            offset afterLayer hl node hn
          obtain ⟨last,hlast,ss,hlen,hroot⟩ := ih parents afterLayer h p hp
          refine ⟨last,hlast,s :: ss,by simp [hlen],?_⟩
          simpa only [pathRoot,←hi,←hd] using hroot

theorem accepted_nonempty_opening_extracts_paths (hash : Hash) (root : Digest) (depth : Nat)
    (indices : List Nat) (leaves : List Digest) (hints : Bytes) (offset next : Nat)
    (hne : indices.isEmpty = false)
    (h : verify hash root depth indices leaves hints offset = some next) :
    ∀ pair ∈ indices.zip leaves, ∃ siblings : List Digest,
      siblings.length = depth ∧ pathRoot hash pair.1 pair.2 siblings = root := by
  have hs := nonempty_acceptance_requires_computed_root hash root depth indices leaves hints offset next hne h
  intro pair hp
  have hn : Node.mk pair.1 pair.2 ∈ (indices.zip leaves).map (fun p => Node.mk p.1 p.2) :=
    List.mem_map_of_mem (fun p : Nat × Digest => Node.mk p.1 p.2) hp
  obtain ⟨last,hlast,ss,hlen,hroot⟩ := successful_layers_extract_paths hash hints depth _ _ offset next
    hs.2.2 _ hn
  have hlast : last = Node.mk 0 root := by simpa using hlast
  subst last
  exact ⟨ss,hlen,hroot⟩

/-- Two accepted multiproof leaves at the same index and depth bind to the same
leaf digest unless their extracted paths expose an actual compression collision. -/
theorem two_accepted_openings_bind_or_compression_collision (hash : Hash) (root : Digest) (depth index : Nat)
    (indices otherIndices : List Nat) (leaves otherLeaves : List Digest)
    (hints otherHints : Bytes) (offset next otherOffset otherNext : Nat) (leaf otherLeaf : Digest)
    (h : verify hash root depth indices leaves hints offset = some next)
    (h' : verify hash root depth otherIndices otherLeaves otherHints otherOffset = some otherNext)
    (hm : (index,leaf) ∈ indices.zip leaves) (hm' : (index,otherLeaf) ∈ otherIndices.zip otherLeaves) :
    leaf = otherLeaf ∨ ∃ a b : Bytes, a.length = 64 ∧ b.length = 64 ∧ a ≠ b ∧ hash a = hash b := by
  have hne : indices.isEmpty = false := by cases indices <;> simp_all
  have hne' : otherIndices.isEmpty = false := by cases otherIndices <;> simp_all
  obtain ⟨ss,hlen,hroot⟩ := accepted_nonempty_opening_extracts_paths hash root depth indices leaves hints
    offset next hne h (index,leaf) hm
  obtain ⟨ts,tlen,troot⟩ := accepted_nonempty_opening_extracts_paths hash root depth otherIndices otherLeaves otherHints
    otherOffset otherNext hne' h' (index,otherLeaf) hm'
  rcases same_root_same_leaf_or_path_collision hash ss index leaf otherLeaf ts
    (hlen.trans tlen.symm) (hroot.trans troot.symm) with heq | hcollision
  · exact Or.inl heq
  · exact Or.inr (path_collision_exposes_hash_collision hash ss index leaf otherLeaf ts hcollision)

/-- Binding for the actual raw leaf inputs. A differing accepted row exposes
either a leaf-hash collision on those two rows or a 64-byte compression
collision from the extracted paths. No serialization injectivity is assumed. -/
theorem accepted_raw_rows_bind_or_hash_collision (hash : Hash) (root : Digest) (depth index : Nat)
    (indices otherIndices : List Nat) (leaves otherLeaves : List Digest)
    (hints otherHints row otherRow : Bytes) (offset next otherOffset otherNext : Nat)
    (h : verify hash root depth indices leaves hints offset = some next)
    (h' : verify hash root depth otherIndices otherLeaves otherHints otherOffset = some otherNext)
    (hm : (index,hash row) ∈ indices.zip leaves)
    (hm' : (index,hash otherRow) ∈ otherIndices.zip otherLeaves) :
    row = otherRow ∨
      (row ≠ otherRow ∧ hash row = hash otherRow) ∨
      ∃ a b : Bytes, a.length = 64 ∧ b.length = 64 ∧ a ≠ b ∧ hash a = hash b := by
  by_cases heq : row = otherRow
  · exact Or.inl heq
  · right
    rcases two_accepted_openings_bind_or_compression_collision hash root depth index indices otherIndices
      leaves otherLeaves hints otherHints offset next otherOffset otherNext (hash row) (hash otherRow)
      h h' hm hm' with hleaf | hc
    · exact Or.inl ⟨heq,hleaf⟩
    · exact Or.inr hc

/-- Ordinary mixed pair/lone-node execution: three leaves, one hint digest,
and two layers. Projection hash exercises bytes and is not a crypto fixture. -/
theorem positive_three_leaf_opening :
    let a := exampleDigest ⟨3,by decide⟩
    let b := exampleDigest ⟨7,by decide⟩
    let c := exampleDigest ⟨11,by decide⟩
    let d := exampleDigest ⟨13,by decide⟩
    let ab := parent exampleHash 0 a b
    let cd := parent exampleHash 2 c d
    verify exampleHash (parent exampleHash 0 ab cd) 2 [0,1,2] [a,b,c] d.val 0 = some 32 := by
  have h0 : Nat.xor 0 1 = 1 := by decide
  simp [verify,runLayers,processLayer,ascending,merged,readDigest,exampleDigest,h0]

end Audit.Wire3.MerkleExtraction
