module

public import Sarkozy.SpectralC.Gauss

@[expose] public section

/-!
# The Paley star sums `S_J` (`lem:spec2:paley`(c))

`paper/sections/14_spectral.tex`, the Paley part of `subsec:spec:coupling`. For a set `J` of
coordinates and labels `x`, `g_J(a; x) = ∏_{j∈J} χ(a − x_j)` (`gJ`) and
`S_J(x_J) = ⟨g_J, C g_J⟩ = E_{a,b} g_J(a) χ(b − a) g_J(b)` (`SJ`).

`lem:spec2:paley`(c): `S_J = 0` if `|J| = 1` (`SJ_singleton`), `|S_J| ≤ r` for every `J`
(`norm_SJ_le`; also the first claim of `lem:spec2:paley-one`), and `S_J = 0` for every `J` if
`p ≡ 3 (mod 4)` (`SJ_eq_zero_of_three`).

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*}

/-- `g_J(a; x) = ∏_{j ∈ J} χ(a − x_j)`. -/
noncomputable def gJ (J : Finset U) (x : U → ZMod p) (a : ZMod p) : ℂ :=
  ∏ j ∈ J, chiC p (a - x j)

/-- `S_J(x_J) = ⟨g_J, C g_J⟩`. -/
noncomputable def SJ (J : Finset U) (x : U → ZMod p) : ℂ := ip (gJ J x) (gaussOp (gJ J x))

lemma conj_gJ (J : Finset U) (x : U → ZMod p) (a : ZMod p) : conj (gJ J x a) = gJ J x a := by
  unfold gJ
  rw [map_prod]
  exact prod_congr rfl fun j _ => conj_chiC _

lemma norm_gJ_le (J : Finset U) (x : U → ZMod p) (a : ZMod p) : ‖gJ J x a‖ ≤ 1 := by
  unfold gJ
  rw [norm_prod]
  apply prod_le_one₀ (fun j _ => norm_nonneg _)
  intro j _
  by_cases h : a - x j = 0
  · rw [h, chiC_zero, norm_zero]; exact zero_le_one
  · rw [norm_chiC h]

lemma l2sq_nonneg (h : ZMod p → ℂ) : 0 ≤ l2sq h := by
  unfold l2sq; positivity

/-- Cauchy–Schwarz in `L²(𝔽_p)`: `|⟨f, g⟩| ≤ ‖f‖ ‖g‖`. -/
lemma norm_ip_le (f g : ZMod p → ℂ) : ‖ip f g‖ ≤ Real.sqrt (l2sq f) * Real.sqrt (l2sq g) := by
  unfold ip l2sq
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (p : ℝ)⁻¹ * ‖∑ a, conj (f a) * g a‖ ≤ (p : ℝ)⁻¹ * ∑ a, ‖f a‖ * ‖g a‖ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        apply sum_congr rfl; intro a _
        rw [norm_mul, Complex.norm_conj]
    _ ≤ (p : ℝ)⁻¹ * (Real.sqrt (∑ a, ‖f a‖ ^ 2) * Real.sqrt (∑ a, ‖g a‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (by positivity)
    _ = Real.sqrt ((p : ℝ)⁻¹ * ∑ a, ‖f a‖ ^ 2) * Real.sqrt ((p : ℝ)⁻¹ * ∑ a, ‖g a‖ ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
        have h1 : Real.sqrt (p : ℝ)⁻¹ * Real.sqrt (p : ℝ)⁻¹ = (p : ℝ)⁻¹ :=
          Real.mul_self_sqrt (by positivity)
        rw [show Real.sqrt (p : ℝ)⁻¹ * Real.sqrt (∑ a, ‖f a‖ ^ 2) *
            (Real.sqrt (p : ℝ)⁻¹ * Real.sqrt (∑ a, ‖g a‖ ^ 2)) =
            (Real.sqrt (p : ℝ)⁻¹ * Real.sqrt (p : ℝ)⁻¹) *
              (Real.sqrt (∑ a, ‖f a‖ ^ 2) * Real.sqrt (∑ a, ‖g a‖ ^ 2)) by ring, h1]

/-- **`lem:spec2:paley`(c)**: `|S_J| ≤ r` for every `J` (`‖g_J‖ ≤ 1`, `‖C‖ = r`). -/
theorem norm_SJ_le (hp2 : p ≠ 2) (J : Finset U) (x : U → ZMod p) : ‖SJ J x‖ ≤ rp p := by
  unfold SJ
  have hg : l2sq (gJ J x) ≤ 1 := by
    unfold l2sq
    have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    calc (p : ℝ)⁻¹ * ∑ a, ‖gJ J x a‖ ^ 2 ≤ (p : ℝ)⁻¹ * ∑ _a : ZMod p, (1 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply sum_le_sum; intro a _
          have := norm_gJ_le J x a
          nlinarith [norm_nonneg (gJ J x a)]
      _ = 1 := by
          rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]
          exact inv_mul_cancel₀ hp.ne'
  have hC := l2sq_gaussOp_le hp2 (gJ J x)
  have hr : 0 ≤ rp p := by unfold rp; positivity
  have hsq : Real.sqrt (l2sq (gaussOp (gJ J x))) ≤ rp p * Real.sqrt (l2sq (gJ J x)) := by
    rw [← Real.sqrt_sq hr, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt hC
  have h0 := l2sq_nonneg (gJ J x)
  calc ‖ip (gJ J x) (gaussOp (gJ J x))‖
      ≤ Real.sqrt (l2sq (gJ J x)) * Real.sqrt (l2sq (gaussOp (gJ J x))) := norm_ip_le _ _
    _ ≤ Real.sqrt (l2sq (gJ J x)) * (rp p * Real.sqrt (l2sq (gJ J x))) :=
        mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
    _ = rp p * l2sq (gJ J x) := by
        rw [mul_left_comm, Real.mul_self_sqrt h0]
    _ ≤ rp p * 1 := mul_le_mul_of_nonneg_left hg hr
    _ = rp p := mul_one _

/-- **`lem:spec2:paley`(c)**: for `p ≡ 3 (mod 4)`, `C` is real antisymmetric, so `S_J = 0`. -/
theorem SJ_eq_zero_of_three (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (J : Finset U) (x : U → ZMod p) :
    SJ J x = 0 := by
  have hm1 : chiC p (-1) = -1 := by
    rw [chiC_neg_one hp2, ZMod.χ₄_nat_three_mod_four hp3]
    simp
  set g := gJ J x with hg
  have hS : SJ J x = (p : ℂ)⁻¹ * (p : ℂ)⁻¹ * ∑ a, ∑ b, g a * chiC p (b - a) * g b := by
    have hcg : ∀ a, conj (g a) = g a := fun a => conj_gJ J x a
    simp only [SJ, ip, gaussOp, ← hg]
    simp_rw [hcg]
    simp only [mul_sum]
    apply sum_congr rfl; intro a _
    apply sum_congr rfl; intro b _
    ring
  have hT : ∑ a, ∑ b, g a * chiC p (b - a) * g b = -∑ a, ∑ b, g a * chiC p (b - a) * g b := by
    conv_lhs => rw [sum_comm]
    rw [← sum_neg_distrib]
    apply sum_congr rfl; intro y _
    rw [← sum_neg_distrib]
    apply sum_congr rfl; intro z _
    have : chiC p (y - z) = -chiC p (z - y) := by
      rw [show y - z = -1 * (z - y) by ring, map_mul, hm1]; ring
    rw [this]
    ring
  have hT0 : ∑ a, ∑ b, g a * chiC p (b - a) * g b = 0 := by
    have h2 : (2 : ℂ) * ∑ a, ∑ b, g a * chiC p (b - a) * g b = 0 := by linear_combination hT
    rcases mul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h
  rw [hS, hT0, mul_zero]

/-- **`lem:spec2:paley`(c)**: `S_J = 0` if `|J| = 1`. -/
theorem SJ_singleton (hp2 : p ≠ 2) (j : U) (x : U → ZMod p) : SJ {j} x = 0 := by
  unfold SJ
  rw [ip_eq_sum_fcoef]
  simp_rw [fcoef_gaussOp hp2]
  -- the coefficients of `χ(· − x_j)`
  have hcoef : ∀ ξ, fcoef (gJ {j} x) ξ =
      (p : ℂ)⁻¹ * conj (ech ξ (x j)) * (chiC p (-ξ) * Gchi p) := by
    intro ξ
    unfold fcoef ip gJ
    simp only [prod_singleton]
    have hre : ∑ a, conj (ech ξ a) * chiC p (a - x j) =
        ∑ t, conj (ech ξ (t + x j)) * chiC p t :=
      (Fintype.sum_equiv (Equiv.addRight (x j)) _ _ (fun t => by simp)).symm
    rw [hre]
    have h1 : ∀ t, conj (ech ξ (t + x j)) * chiC p t =
        conj (ech ξ (x j)) * (chiC p t * ech (-ξ) t) := by
      intro t
      rw [ech_add_right, map_mul, conj_ech ξ t]
      ring
    simp_rw [h1]
    rw [← mul_sum, sum_chiC_ech hp2, mul_assoc]
  simp_rw [hcoef]
  have hterm : ∀ ξ, conj ((p : ℂ)⁻¹ * conj (ech ξ (x j)) * (chiC p (-ξ) * Gchi p)) *
      (gaussEig ξ * ((p : ℂ)⁻¹ * conj (ech ξ (x j)) * (chiC p (-ξ) * Gchi p))) =
      ((p : ℂ)⁻¹ * (p : ℂ)⁻¹ * (conj (Gchi p) * Gchi p) * (epsG p * (rp p : ℂ))) *
        chiC p ξ := by
    intro ξ
    have he : conj (conj (ech ξ (x j))) * conj (ech ξ (x j)) = 1 := by
      rw [Complex.conj_conj, Complex.mul_conj', norm_ech]; simp
    have hχ : conj (chiC p (-ξ)) * chiC p (-ξ) * chiC p ξ = chiC p ξ := by
      rw [conj_chiC, show -ξ = -1 * ξ by ring, map_mul]
      by_cases hξ : ξ = 0
      · rw [hξ, chiC_zero]; ring
      · have h1 : chiC p (-1) * chiC p (-1) = 1 := by
          rw [← map_mul]; norm_num
        have h2 : chiC p ξ * chiC p ξ * chiC p ξ = chiC p ξ := by
          rw [chiC_apply]
          rcases quadraticChar_dichotomy hξ with h | h <;> rw [h] <;> push_cast <;> ring
        linear_combination (chiC p ξ * chiC p ξ * chiC p ξ) * h1 + h2
    unfold gaussEig
    rw [map_mul, map_mul, map_mul, map_inv₀, Complex.conj_natCast]
    linear_combination ((p : ℂ)⁻¹ * (p : ℂ)⁻¹ * conj (Gchi p) * Gchi p * epsG p * (rp p : ℂ) *
      (conj (chiC p (-ξ)) * chiC p (-ξ) * chiC p ξ)) * he +
      ((p : ℂ)⁻¹ * (p : ℂ)⁻¹ * conj (Gchi p) * Gchi p * epsG p * (rp p : ℂ)) * hχ
  simp_rw [hterm]
  rw [← mul_sum, sum_chiC hp2, mul_zero]

end Sarkozy.SpectralC
