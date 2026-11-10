module

public import Sarkozy.TraceMixing.Paley

/-!
# The Paley operator on the mean-zero functions (`lem:paley-triple`(c), second half)

`paper/sections/12_labellings.tex`, `lem:paley-triple`(c): for `q ≡ 3 (mod 4)` the Paley
operator `(P h)(s) = E_t χ(t - s) h(t)` maps every function to a mean-zero function
(`paleyOp_mean`), and on the mean-zero functions `P² = -q⁻¹ I` (`paleyOp_sq`; the paper's
`pP² = -I` with `q = p`). With `‖P h‖² = q⁻¹ ‖h‖²` on `H_0` (`norm_paleyOp`) and `P^* = -P`
(`paleyOp_adjoint`), `P/r` (`r = q^{-1/2}`) is an orthogonal map of `H_0` with square `-I`:
the real form of "`P/r` is unitary with eigenvalues `± i`".
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

open Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer. -/
local notation "χ" => quadraticChar F

/-- **`P` maps into the mean-zero functions**: `∑_s (P h)(s) = 0`. -/
theorem paleyOp_mean (hF : ringChar F ≠ 2) (h : F → ℝ) : ∑ s, paleyOp h s = 0 := by
  unfold paleyOp
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h1 (t : F) : ∑ s, (χ (t - s) : ℝ) * h t = h t * ∑ s, (χ (t - s) : ℝ) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro s _
    ring
  have h2 (t : F) : ∑ s, (χ (t - s) : ℝ) = 0 := by
    have : ∑ s, χ (t - s) = 0 := by
      rw [← quadraticChar_sum_zero hF]
      exact Equiv.sum_comp (Equiv.subLeft t) (fun x => χ x)
    exact_mod_cast this
  simp only [h1, h2, mul_zero, sum_const_zero]

/-- **`P² = -q⁻¹ I` on the mean-zero functions** (`q ≡ 3 (mod 4)`). -/
theorem paleyOp_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h : F → ℝ)
    (hh : ∑ s, h s = 0) (s : F) :
    paleyOp (paleyOp h) s = -(Fintype.card F : ℝ)⁻¹ * h s := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : q ≠ 0 := by rw [hq]; exact_mod_cast Fintype.card_ne_zero
  have hcorr (u : F) : ∑ t, (χ (t - s) : ℝ) * (χ (u - t) : ℝ) = 1 - (if s = u then q else 0) := by
    have h1 : ∑ t, (χ (t - s) : ℝ) * (χ (u - t) : ℝ) = -∑ t, (χ (t - s) : ℝ) * (χ (t - u) : ℝ) := by
      rw [← Finset.sum_neg_distrib]
      apply sum_congr rfl
      intro t _
      have : (χ (u - t) : ℝ) = -(χ (t - u) : ℝ) := by exact_mod_cast chi_swap h3 u t
      rw [this]
      ring
    have h2 : ∑ t, (χ (t - s) : ℝ) * (χ (t - u) : ℝ) = (if s = u then q else 0) - 1 := by
      have := sum_chi_mul_chi hF s u
      have e : ∑ t, (χ (t - s) : ℝ) * (χ (t - u) : ℝ) =
          (((if s = u then (Fintype.card F : ℤ) else 0) - 1 : ℤ) : ℝ) := by
        rw [← this]
        push_cast
        rfl
      rw [e]
      split_ifs <;> push_cast <;> ring
    rw [h1, h2]
    ring
  unfold paleyOp
  have hexp : ∑ t, (χ (t - s) : ℝ) * (q⁻¹ * ∑ u, (χ (u - t) : ℝ) * h u) =
      q⁻¹ * ∑ u, h u * ∑ t, (χ (t - s) : ℝ) * (χ (u - t) : ℝ) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro t _
    ring
  rw [hexp]
  simp only [hcorr, mul_sub, mul_one, mul_ite, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, mem_univ, ite_true, hh]
  field_simp
  ring

end Sarkozy.TraceMixing
