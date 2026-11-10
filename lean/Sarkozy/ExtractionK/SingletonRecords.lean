module

public import Sarkozy.ExtractionK.Compressed

/-!
# Singleton extraction records

Every nonstar monomial is a fully decided class with a two-edge witness.
The complement of the witness endpoints supplies a cover. These records
give a uniform bound for small cross graphs without enumerating classes.
-/

@[expose] public section

namespace Sarkozy.ExtractionK

open Finset Sarkozy.Extraction Sarkozy.Labellings

variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] in
theorem cls_singleton (S : Finset (U × U)) : cls S S ∅ = {S} := by
  ext T
  rw [mem_cls, mem_singleton, sdiff_empty]
  exact ⟨fun h => Subset.antisymm h.2 h.1, fun h => by subst T; exact ⟨le_rfl, le_rfl⟩⟩

omit [Fintype U] in
theorem singleton_witness {S : Finset (U × U)} (hS : IsNonstar S) :
    ∃ w : Fin 2 → U × U, IsWitness S S ∅ w := by
  obtain ⟨e, he, f, hf, hd⟩ := isNonstar_iff.mp hS
  refine ⟨![e, f], ?_⟩
  constructor
  · intro i
    fin_cases i
    · exact he
    · exact hf
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [PairDisj]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [PairDisj]
  · intro a ha _ _
    exact Or.inl ha

omit [Fintype U] in
theorem witness_card_fst {S : Finset (U × U)} {k : ℕ} {w : Fin k → U × U}
    (hw : IsWitness S S ∅ w) : (witV w).card = k := by
  rw [witV, card_image_of_injective _ hw.injective_fst, card_univ, Fintype.card_fin]

omit [Fintype U] in
theorem witness_card_snd {S : Finset (U × U)} {k : ℕ} {w : Fin k → U × U}
    (hw : IsWitness S S ∅ w) : (witW w).card = k := by
  rw [witW, card_image_of_injective _ hw.injective_snd, card_univ, Fintype.card_fin]

theorem singleton_cover (S : Finset (U × U)) {k : ℕ} (w : Fin k → U × U) :
    IsCover S S ∅ w (univ \ witV w) (univ \ witW w) := by
  have hV : univ \ witV w = univ.filter (fun j => ∀ i, (w i).1 ≠ j) := by
    ext j
    simp only [witV, mem_sdiff, mem_univ, mem_image, true_and, not_exists, mem_filter]
  have hW : univ \ witW w = univ.filter (fun j => ∀ i, (w i).2 ≠ j) := by
    ext j
    simp only [witW, mem_sdiff, mem_univ, mem_image, true_and, not_exists, mem_filter]
  rw [hV, hW]
  exact isCover_compl S S ∅ w

end Sarkozy.ExtractionK
