module

public import Sarkozy.F7Repair.TwoLayer

@[expose] public section

/-!
# Non-vacuity of the one-way repair data

* `toyν`, `toyμ`, **`toyData : OneWayData toyν toyμ toyμ`**: the uniform law on `Bool × Bool`
  with the targets `(3/5, 2/5)` on both halves: `U = 1/5`, `ρ = 0`, `K_∞ = 1`, so
  `F = 2/5` and `2F = 4/5 < 1`. All hypotheses hold with a genuine change of marginals.
* **`toy_repair_marginals`**: the repaired law `(1 + f + g)ν` exists, is positive, and has the
  marginals `(3/5, 2/5)`, which `ν` does not have: the construction is not vacuous.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.Recentering Sarkozy.Structured

/-- The uniform law on `Bool × Bool`. -/
noncomputable def toyν : FiniteLaw (Bool × Bool) where
  weight _ := 1 / 4
  nonneg _ := by norm_num
  total := by simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_bool]; norm_num

/-- The target law `(3/5, 2/5)` on `Bool`. -/
noncomputable def toyμ : FiniteLaw Bool where
  weight b := if b then 3 / 5 else 2 / 5
  nonneg b := by split_ifs <;> norm_num
  total := by simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]; norm_num

theorem toy_mX (x : Bool) : mX toyν x = 1 / 2 := by
  unfold mX toyν
  simp only [Fintype.sum_bool]
  norm_num

theorem toy_mY (y : Bool) : mY toyν y = 1 / 2 := by
  unfold mY toyν
  simp only [Fintype.sum_bool]
  norm_num

/-- **A one-way repair datum with a genuine change of marginals**: `U = 1/5`, `ρ = 0`, `K = 1`. -/
noncomputable def toyData : OneWayData toyν toyμ toyμ where
  U := 1 / 5
  ρ := 0
  K := 1
  U_nonneg := by norm_num
  ρ_nonneg := le_rfl
  ρ_lt_one := by norm_num
  K_nonneg := by norm_num
  twoF_lt := by norm_num
  dens_X x := by
    rw [toy_mX]
    unfold toyμ
    cases x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> norm_num [abs_le]
  dens_Y y := by
    rw [toy_mY]
    unfold toyμ
    cases y <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> norm_num [abs_le]
  corr h k hh hk := by
    have hh' : h true + h false = 0 := by
      have : (margX toyν).expect h = 1 / 2 * h true + 1 / 2 * h false := by
        unfold FiniteLaw.expect
        simp only [Fintype.sum_bool]
        change mX toyν true * h true + mX toyν false * h false = _
        rw [toy_mX, toy_mX]
      linarith
    have e : toyν.expect (fun p => h p.1 * k p.2) =
        1 / 4 * (h true + h false) * (k true + k false) := by
      unfold FiniteLaw.expect toyν
      simp only [Fintype.sum_prod_type, Fintype.sum_bool]
      ring
    rw [e, hh']
    simp
  sup x y := by
    rw [toy_mX, toy_mY]
    unfold toyν
    norm_num

/-- **The toy repair changes the marginals and is positive**: `(1 + f + g)ν` is positive and has
both marginals `(3/5, 2/5)`, while `ν` has `(1/2, 1/2)`. -/
theorem toy_repair_marginals :
    (∀ x y, 0 < 1 + toyData.f x + toyData.g y) ∧
      (∀ φ : Bool → ℝ, toyν.expect (fun p => (1 + toyData.f p.1 + toyData.g p.2) * φ p.1) =
        3 / 5 * φ true + 2 / 5 * φ false) ∧
      (∀ φ : Bool → ℝ, toyν.expect (fun p => (1 + toyData.f p.1 + toyData.g p.2) * φ p.2) =
        3 / 5 * φ true + 2 / 5 * φ false) ∧
      mX toyν true ≠ 3 / 5 := by
  refine ⟨toyData.one_add_pos, fun φ => ?_, fun φ => ?_, ?_⟩
  · rw [toyData.marg_fst]
    unfold FiniteLaw.expect toyμ
    simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
  · rw [toyData.marg_snd]
    unfold FiniteLaw.expect toyμ
    simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
  · rw [toy_mX]
    norm_num

end Sarkozy.F7Repair
