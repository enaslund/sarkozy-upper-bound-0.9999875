module

public import Sarkozy.Labellings.Extension

/-!
# A character mean under fixed quadratic conditions

An extra root outside the pinned roots converts a character-weighted soft
count into the difference of two ordinary soft counts. Removing excluded
labels then gives a bound on the character sum over the allowed set.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Labellings

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def softCountError (F : Type*) [Fintype F] (d : ℕ) : ℝ :=
  gradedA d * Real.sqrt (Fintype.card F) + gradedB d

theorem soft_character_sum_bound (hW : WeilBound F) (β : I → F)
    (hβ : Function.Injective β) (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (t : F) (ht : ∀ i, t ≠ β i) :
    |((∑ x, quadraticChar F (x - t) *
      ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) : ℝ)| ≤
      softCountError F (Fintype.card I + 1) + softCountError F (Fintype.card I) := by
  let β' : Option I → F := fun o => match o with
    | none => t
    | some i => β i
  let s' : Option I → ℤ := fun o => match o with
    | none => 1
    | some i => s i
  have hinj : Function.Injective β' := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some j => exact False.elim (ht j hab)
    | some i =>
      cases b with
      | none => exact False.elim (ht i hab.symm)
      | some j => exact congrArg some (hβ hab)
  have hs' : ∀ o, s' o = 1 ∨ s' o = -1 := by
    intro o
    cases o with
    | none => exact Or.inl rfl
    | some i => exact hs i
  have h0 := soft_count_bound hW β hβ s hs
  have h1 := soft_count_bound hW β' hinj s' hs'
  have heq : (∑ x, quadraticChar F (x - t) *
      ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) =
      (∑ x, ∏ o, (1 + s' o * quadraticChar F (x - β' o))) -
        ∑ x, ∏ i, (1 + s i * quadraticChar F (x - β i)) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro x _
    rw [Fintype.prod_option]
    dsimp [β', s']
    ring
  rw [heq, Int.cast_sub]
  have heqR : ((∑ x, ∏ o, (1 + s' o * quadraticChar F (x - β' o)) : ℤ) : ℝ) -
      ((∑ x, ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) : ℝ) =
      (((∑ x, ∏ o, (1 + s' o * quadraticChar F (x - β' o)) : ℤ) : ℝ) -
        Fintype.card F) -
      (((∑ x, ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) : ℝ) -
        Fintype.card F) := by ring
  rw [heqR]
  exact ((abs_sub _ _).trans (add_le_add h1 h0)).trans_eq (by
    simp only [softCountError, Fintype.card_option])

theorem character_admissible_split (β : I → F) (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (M : Finset F) (hM : ∀ i, β i ∈ M) (t : F) :
    (2 ^ Fintype.card I * ∑ x ∈ admissible β s M, quadraticChar F (x - t) : ℤ) =
      (∑ x, quadraticChar F (x - t) *
        ∏ i, (1 + s i * quadraticChar F (x - β i))) -
      ∑ x ∈ M, quadraticChar F (x - t) *
        ∏ i, (1 + s i * quadraticChar F (x - β i)) := by
  rw [← sum_compl_add_sum M, add_sub_cancel_right]
  have hpoint (x : F) (hx : x ∈ Mᶜ) :
      quadraticChar F (x - t) * (∏ i, (1 + s i * quadraticChar F (x - β i))) =
        if ∀ i, quadraticChar F (x - β i) = s i then
          2 ^ Fintype.card I * quadraticChar F (x - t) else 0 := by
    rw [prod_soft_eq β s hs (x := x) (fun i h => (mem_compl.mp hx) (h.symm ▸ hM i))]
    split_ifs <;> ring
  rw [sum_congr rfl hpoint, ← sum_filter, ← mul_sum]
  congr 2
  ext x
  simp only [admissible, mem_filter, mem_univ, mem_compl, true_and]

theorem abs_character_soft_le (β : I → F) (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (t x : F) :
    |quadraticChar F (x - t) * ∏ i, (1 + s i * quadraticChar F (x - β i))| ≤
      (2 : ℤ) ^ Fintype.card I := by
  have hχ : |quadraticChar F (x - t)| ≤ 1 := by
    rcases quadraticChar_isQuadratic F (x - t) with h | h | h <;> simp [h]
  have hP := prod_soft_nonneg_le β s hs x
  rw [abs_mul, abs_of_nonneg hP.1]
  exact (mul_le_mul hχ hP.2 hP.1 zero_le_one).trans_eq (one_mul _)

theorem character_admissible_bound (hW : WeilBound F) (β : I → F)
    (hβ : Function.Injective β) (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (M : Finset F) (hM : ∀ i, β i ∈ M) (t : F) (ht : ∀ i, t ≠ β i) :
    (2 : ℝ) ^ Fintype.card I *
      |((∑ x ∈ admissible β s M, quadraticChar F (x - t) : ℤ) : ℝ)| ≤
      softCountError F (Fintype.card I + 1) + softCountError F (Fintype.card I) +
        2 ^ Fintype.card I * M.card := by
  have hsplit := character_admissible_split β s hs M hM t
  have hsoft := soft_character_sum_bound hW β hβ s hs t ht
  have hMsum : |(∑ x ∈ M, quadraticChar F (x - t) *
      ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ)| ≤
        2 ^ Fintype.card I * M.card := by
    calc
      _ ≤ ∑ _x ∈ M, (2 : ℤ) ^ Fintype.card I :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => abs_character_soft_le β s hs t x)
      _ = _ := by simp [mul_comm]
  have hsplitR : (2 : ℝ) ^ Fintype.card I *
      ((∑ x ∈ admissible β s M, quadraticChar F (x - t) : ℤ) : ℝ) =
      ((∑ x, quadraticChar F (x - t) *
        ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) : ℝ) -
      ((∑ x ∈ M, quadraticChar F (x - t) *
        ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) : ℝ) := by
    exact_mod_cast hsplit
  have hMR : |((∑ x ∈ M, quadraticChar F (x - t) *
      ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) : ℝ)| ≤
        (2 : ℝ) ^ Fintype.card I * M.card := by exact_mod_cast hMsum
  calc
    _ = |(2 : ℝ) ^ Fintype.card I *
        ((∑ x ∈ admissible β s M, quadraticChar F (x - t) : ℤ) : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ Fintype.card I)]
    _ ≤ _ := by rw [hsplitR]; exact (abs_sub _ _).trans (add_le_add hsoft hMR)

end Sarkozy.Labellings
