module

public import Sarkozy.F3Kernel.MaskLayouts

/-!
# Compressed roots with a row arm and a column arm

The kind-zero roots of the checker are case (B) of the paper's compressed partition.
The rank is the transposed bit position. This file identifies their mask formula with
`datumB`, including the removal of present bits from the absent mask.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

def edgeRank (e : Fin 36 × Fin 36) : ℕ := 64 * e.2.val + e.1.val

theorem edgeRank_injective : Function.Injective edgeRank := by
  intro e f he
  exact Prod.swap_injective (posM_injective he)

/-- The three present edges themselves have the compressed case-(B) description. -/
theorem datumB_of_arms (Ex : Finset (Fin 36 × Fin 36)) (e f g : Fin 36 × Fin 36)
    (hf : f ≠ e ∧ f.1 = e.1) (hg : g ≠ e ∧ g.2 = e.2)
    (hef : edgeRank e < edgeRank f) (heg : edgeRank e < edgeRank g) :
    IsCompressedDatum edgeRank Ex {e, f, g} (datumB edgeRank Ex e f g) := by
  have hfx : f.2 ≠ e.2 := fun h => hf.1 (Prod.ext hf.2 h)
  have hgx : g.1 ≠ e.1 := fun h => hg.1 (Prod.ext h hg.2)
  refine ⟨e, ⟨by simp, ?_⟩, Or.inr ⟨?_, f, g, ?_, ?_, rfl⟩⟩
  · intro q hq
    simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact le_rfl
    · exact hef.le
    · exact heg.le
  · intro q hq
    simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · simp [PairDisj]
    · simp [PairDisj, hf.2]
    · simp [PairDisj, hg.2]
  · have heq : rowArms ({e, f, g} : Finset _) e = {f} := by
      ext q
      simp only [rowArms, mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hq, hne, hx⟩
        rcases hq with rfl | rfl | rfl
        · exact False.elim (hne rfl)
        · rfl
        · exact False.elim (hgx hx)
      · rintro rfl
        exact ⟨Or.inr (Or.inl rfl), hf⟩
    rw [heq]
    exact ⟨mem_singleton_self _, fun q hq => (mem_singleton.mp hq) ▸ le_rfl⟩
  · have heq : colArms ({e, f, g} : Finset _) e = {g} := by
      ext q
      simp only [colArms, mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hq, hne, hy⟩
        rcases hq with rfl | rfl | rfl
        · exact False.elim (hne rfl)
        · exact False.elim (hfx hy)
        · rfl
      · rintro rfl
        exact ⟨Or.inr (Or.inr rfl), hg⟩
    rw [heq]
    exact ⟨mem_singleton_self _, fun q hq => (mem_singleton.mp hq) ▸ le_rfl⟩

def classBP (e f g : Fin 36 × Fin 36) : ℕ :=
  Nat.lor (Nat.shiftLeft 1 (edgeRank e))
    (Nat.lor (Nat.shiftLeft 1 (edgeRank f)) (Nat.shiftLeft 1 (edgeRank g)))

def disjointT (G : Consts) (e : Fin 36 × Fin 36) : ℕ :=
  Nat.xor G.ET (Nat.lor (rowT G e.1.val) (colT G e.2.val))

def classBA (G : Consts) (e f g : Fin 36 × Fin 36) : ℕ :=
  Nat.lor (disjointT G e) (Nat.lor (beforeT G (edgeRank e))
    (Nat.lor (Nat.land (rowT G e.1.val) (beforeT G (edgeRank f)))
      (Nat.land (colT G e.2.val) (beforeT G (edgeRank g)))))

theorem decT_zero : decT 0 = ∅ := by
  ext e
  simp only [mem_decT, bit_eq_testBit, Nat.zero_testBit, Bool.false_eq_true, notMem_empty]

theorem decT_single (e : Fin 36 × Fin 36) :
    decT (Nat.shiftLeft 1 (edgeRank e)) = {e} := by
  have he := decT_insert 0 e
  change decT (0 ||| (1 <<< edgeRank e)) = insert e (decT 0) at he
  rw [Nat.zero_or, decT_zero] at he
  exact he

theorem decT_classBP (e f g : Fin 36 × Fin 36) : decT (classBP e f g) = {e, f, g} := by
  simp only [classBP, decT_lor, decT_single]
  ext q
  simp only [mem_union, mem_singleton, mem_insert]

theorem decT_disjointT (G : Consts) (e : Fin 36 × Fin 36) :
    decT (disjointT G e) = (decT G.ET).filter (PairDisj e) := by
  have hs : decT (Nat.lor (rowT G e.1.val) (colT G e.2.val)) ⊆ decT G.ET := by
    rw [decT_lor, decT_row G e.1.isLt, decT_col]
    exact union_subset (filter_subset _ _) (filter_subset _ _)
  rw [disjointT, decT_xor hs, decT_lor, decT_row G e.1.isLt, decT_col]
  ext q
  simp only [mem_sdiff, mem_union, mem_filter, PairDisj, Fin.val_inj]
  tauto

theorem decT_row_before (G : Consts) (e f : Fin 36 × Fin 36)
    (he : e ∈ decT G.ET) (hef : edgeRank e < edgeRank f) :
    decT (Nat.land (rowT G e.1.val) (beforeT G (edgeRank f))) =
      ((rowArms (decT G.ET) e).filter (fun q => edgeRank q < edgeRank f)) ∪ {e} := by
  rw [decT_land, decT_row G e.1.isLt, decT_before]
  ext q
  simp only [mem_inter, mem_filter, mem_union, mem_singleton, rowArms, Fin.val_inj]
  change (q ∈ decT G.ET ∧ q.1 = e.1) ∧
    (q ∈ decT G.ET ∧ edgeRank q < edgeRank f) ↔
    (q ∈ decT G.ET ∧ q ≠ e ∧ q.1 = e.1) ∧ edgeRank q < edgeRank f ∨ q = e
  by_cases hq : q = e
  · subst q
    simp [he, hef]
  · tauto

theorem decT_col_before (G : Consts) (e g : Fin 36 × Fin 36)
    (he : e ∈ decT G.ET) (heg : edgeRank e < edgeRank g) :
    decT (Nat.land (colT G e.2.val) (beforeT G (edgeRank g))) =
      ((colArms (decT G.ET) e).filter (fun q => edgeRank q < edgeRank g)) ∪ {e} := by
  rw [decT_land, decT_col, decT_before]
  ext q
  simp only [mem_inter, mem_filter, mem_union, mem_singleton, colArms, Fin.val_inj]
  change (q ∈ decT G.ET ∧ q.2 = e.2) ∧
    (q ∈ decT G.ET ∧ edgeRank q < edgeRank g) ↔
    (q ∈ decT G.ET ∧ q ≠ e ∧ q.2 = e.2) ∧ edgeRank q < edgeRank g ∨ q = e
  by_cases hq : q = e
  · subst q
    simp [he, heg]
  · tauto

theorem decT_classBA (G : Consts) (e f g : Fin 36 × Fin 36)
    (he : e ∈ decT G.ET) (hef : edgeRank e < edgeRank f)
    (heg : edgeRank e < edgeRank g) :
    decT (classBA G e f g) = (datumB edgeRank (decT G.ET) e f g).2 ∪ {e} := by
  rw [classBA, decT_lor, decT_lor, decT_lor, decT_disjointT, decT_before,
    decT_row_before G e f he hef, decT_col_before G e g he heg]
  ext q
  simp only [datumB, mem_union, mem_filter, mem_singleton, edgeRank]
  tauto

/-- Removing the present bits leaves exactly the absent set of case (B). -/
theorem decT_classB_absent (G : Consts) (e f g : Fin 36 × Fin 36)
    (he : e ∈ decT G.ET) (hfE : f ∈ decT G.ET) (hgE : g ∈ decT G.ET)
    (hf : f ≠ e ∧ f.1 = e.1) (hg : g ≠ e ∧ g.2 = e.2)
    (hef : edgeRank e < edgeRank f) (heg : edgeRank e < edgeRank g) :
    decT (Nat.xor (classBA G e f g) (Nat.land (classBA G e f g) (classBP e f g))) =
      (datumB edgeRank (decT G.ET) e f g).2 := by
  have hS : ({e, f, g} : Finset _) ⊆ decT G.ET := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨he, hfE, hgE⟩
  have hv := (datumB_of_arms (decT G.ET) e f g hf hg hef heg).isClassDatum edgeRank hS
  have hd : Disjoint ({e, f, g} : Finset _) (datumB edgeRank (decT G.ET) e f g).2 := hv.2.2
  rw [decT_xor_land, decT_classBA G e f g he hef heg, decT_classBP]
  ext q
  simp only [mem_sdiff, mem_union, mem_singleton, mem_insert]
  have hne := disjoint_left.mp hd
  constructor
  · rintro ⟨hq | rfl, hn⟩
    · exact hq
    · exact False.elim (hn (Or.inl rfl))
  · intro hq
    exact ⟨Or.inl hq, fun hp => hne (by simpa only [mem_insert, mem_singleton] using hp) hq⟩

end Sarkozy.F3Kernel
