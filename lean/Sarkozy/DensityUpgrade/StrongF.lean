module

public import Sarkozy.DensityUpgrade.ConditioningRange
public import Sarkozy.Moments.UniformConvexity
public import Sarkozy.ProbabilityConstructions

/-!
# Moments for weighted fold restoration (`lem:density:strong-F`)

`paper/sections/31_density_induction_upgrade.tex`, Lemma "Moments for weighted fold
restoration" (`lem:density:strong-F`). The analytic steps of the proof are proved here, in
WP-FI's formalization of `def:density:mixed-moment` (`conditioningUnitMixed`: weights on
`Fin d → X`, norms for the uniform probability on the finite alphabet `X`). The
construction-specific inputs are named hypotheses:

* the centered bilinear bounds of the uniform ordered-distinct pair (`L^{9/8}` norm
  `(p-1)^{-2/9} ≤ 1/8`) and of a strict Paley edge in class three (`L^{4/3}` norm
  `(p+1)^{3/4}/(p-1) ≤ 2p^{-1/4}`). In the paper these come from the exact `L¹`, `L²` norms by
  interpolation, which is not formalized here;
* the pair marginals of the `K_{2,2}` outer core (the Paley-graph count of common
  neighbours, which makes both objects uniform ordered-distinct pairs);
* the decomposition of the adjoined law into the native fold and the excluded event, with
  its mass (`≤ 8/p`, resp. `≤ 2/p`) and the uniform marginals on the excluded event
  (translation invariance).

For the uniform ordered-distinct pair itself (`distinctPair`) the uniform marginals and the
centered `L²` bound are proved; only the interpolated `L^{9/8}` bound remains an input.

The proved steps:

* `strongF_pair_unit_mixed`: a two-coordinate law with uniform marginals whose centered
  bilinear `L^r` norm is at most `r - 1` (`1 < r ≤ 2`) has unit mixed `L^r`. This is the
  paper's use of `lem:density:uniform-convexity` with `√((1-m²)(1-n²)) ≤ 1 - mn`.
* `strongF_double_unit_mixed`: "Cauchy–Schwarz between the two objects": if both pair
  marginals of a four-label law have unit mixed `L^r`, the law has unit mixed `L^{2r}`.
* `strongF_prod_unit_mixed`: products of laws with unit mixed `L^r` have unit mixed `L^r`;
  with `conditioningUnitMixed.mono` this adjoins the independent middle labels.
* `strongF_two_layer`: the native two-layer fold has unit mixed `L^{5/2}` (conditioning with
  `s = 9/4`, `r = 5/2`, `α = 2/27`, `1281 · 8/p ≤ 2/27` for `p ≥ 2^18`).
* `strongF_one_layer`: the native one-layer (three-label) fold has unit mixed `L^{7/5}`
  (`s = 4/3`, `r = 7/5`, `α = 1/8`, `1025 · 2/p < 1/8`, `6 p^{-1/4} ≤ 3/32` for `p ≥ 2^24`).
* `strongF_emission_double`, `strongF_emission_quad`, `strongF_emissions`: Hölder within a
  repeated label. Repeating every label twice doubles the exponent (`5/2 → 5`), four times
  quadruples it (`7/5 → 28/5`): the twelve-slot emissions.
* `strongF_density_endpoints`: the endpoints `12/5` and `15/7` exceed `2θ_*`.
* `uniformCoords_prod`, `uniformCoords_of_pairs`: the uniform marginals of the adjoined laws
  are derived, not assumed.
* `distinctPair`, `distinctPair_uniformCoords`, `distinctPair_centered_L2`: the actual uniform
  ordered-distinct pair, its uniform marginals and its centered bilinear `L²` norm `1/(p - 1)`
  (the `L²` endpoint of the paper's interpolation); `strongF_two_layer_distinct` is the
  two-layer statement for it.

Not formalized: the interpolation step, the Paley counts, and the identification of the folds
with the paper's constructions.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.DensityUpgrade

section Norms

variable {X : Type*} [Fintype X]

theorem conditioningNorm_nonneg (r : ℝ) (g : X → ℝ) : 0 ≤ conditioningNorm r g :=
  Real.rpow_nonneg (div_nonneg (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _))
    (Nat.cast_nonneg _)) _

/-- `conditioningNorm` is the `L^r` norm of the uniform probability on `X`. -/
theorem conditioningNorm_eq_lpNorm [Nonempty X] (r : ℝ) (g : X → ℝ) :
    conditioningNorm r g = (FiniteLaw.uniform X).lpNorm r g := by
  unfold conditioningNorm FiniteLaw.lpNorm FiniteLaw.moment
  rw [FiniteLaw.expect_uniform, one_div]

/-- `‖f²‖_r = ‖f‖_{2r}²`. -/
theorem conditioningNorm_sq {r : ℝ} (hr : 0 < r) (f : X → ℝ) :
    conditioningNorm r (fun a => f a ^ 2) = conditioningNorm (2 * r) f ^ 2 := by
  unfold conditioningNorm
  have hS : 0 ≤ (∑ a, |f a| ^ (2 * r)) / (Fintype.card X : ℝ) :=
    div_nonneg (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (abs_nonneg _) _))
      (Nat.cast_nonneg _)
  have e : ∀ a, |f a ^ 2| ^ r = |f a| ^ (2 * r) := fun a => by
    rw [abs_pow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
  simp only [e]
  have hr' : r ≠ 0 := hr.ne'
  rw [← Real.rpow_natCast, ← Real.rpow_mul hS]
  congr 1
  push_cast
  field_simp

/-- Hölder within a repeated label: `‖g h‖_r ≤ ‖g‖_{2r} ‖h‖_{2r}`. -/
theorem conditioningNorm_mul_le [Nonempty X] {r : ℝ} (hr : 0 < r) (g h : X → ℝ) :
    conditioningNorm r (fun a => g a * h a) ≤
      conditioningNorm (2 * r) g * conditioningNorm (2 * r) h := by
  have hN : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  set A := (∑ a, |g a| ^ (2 * r)) / (Fintype.card X : ℝ) with hA
  set B := (∑ a, |h a| ^ (2 * r)) / (Fintype.card X : ℝ) with hB
  have hA0 : 0 ≤ A := div_nonneg (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (abs_nonneg _) _))
    hN.le
  have hB0 : 0 ≤ B := div_nonneg (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (abs_nonneg _) _))
    hN.le
  set C := (∑ a, |g a * h a| ^ r) / (Fintype.card X : ℝ) with hC
  have hC0 : 0 ≤ C := div_nonneg (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (abs_nonneg _) _))
    hN.le
  -- Cauchy–Schwarz: `C² ≤ A B`
  have hCS : C ^ 2 ≤ A * B := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => |g a| ^ r)
      (fun a => |h a| ^ r)
    have e1 : ∀ a, |g a * h a| ^ r = |g a| ^ r * |h a| ^ r := fun a => by
      rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    have e2g : ∀ a, (|g a| ^ r) ^ 2 = |g a| ^ (2 * r) := fun a => by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      congr 1
      push_cast
      ring
    have e2h : ∀ a, (|h a| ^ r) ^ 2 = |h a| ^ (2 * r) := fun a => by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      congr 1
      push_cast
      ring
    simp only [e2g, e2h] at hcs
    rw [hC, hA, hB, Finset.sum_congr rfl (fun a _ => e1 a), div_pow, div_mul_div_comm,
      sq (Fintype.card X : ℝ)]
    exact div_le_div_of_nonneg_right hcs (mul_nonneg hN.le hN.le)
  -- take `r`-th roots: `C^{1/r} ≤ (A B)^{1/(2r)}`
  unfold conditioningNorm
  rw [← hA, ← hB, ← hC]
  have hr0 : 0 < 2 * r := by linarith
  have hC' : C = (C ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hC0]
    norm_num
  calc C ^ r⁻¹ = ((C ^ 2) ^ ((1 : ℝ) / 2)) ^ r⁻¹ := by rw [← hC']
    _ ≤ ((A * B) ^ ((1 : ℝ) / 2)) ^ r⁻¹ :=
        Real.rpow_le_rpow (Real.rpow_nonneg (sq_nonneg _) _)
          (Real.rpow_le_rpow (sq_nonneg _) hCS (by norm_num)) (inv_nonneg.2 hr.le)
    _ = A ^ (2 * r)⁻¹ * B ^ (2 * r)⁻¹ := by
        have hr' : r ≠ 0 := hr.ne'
        rw [← Real.rpow_mul (mul_nonneg hA0 hB0), Real.mul_rpow hA0 hB0,
          show (1 : ℝ) / 2 * r⁻¹ = (2 * r)⁻¹ by field_simp]

end Norms

section Mixed

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

omit [DecidableEq X] [Nonempty X] in
theorem conditioningNorm_abs (r : ℝ) (g : X → ℝ) :
    conditioningNorm r (fun a => |g a|) = conditioningNorm r g := by
  simp only [conditioningNorm, abs_abs]

omit [DecidableEq X] in
/-- Unit mixed `L^r` is monotone in `r`. -/
theorem conditioningUnitMixed.mono {d : ℕ} {π : (Fin d → X) → ℝ} {r r' : ℝ} (hr : 0 < r)
    (hrr : r ≤ r') (h : conditioningUnitMixed π r) : conditioningUnitMixed π r' := by
  intro f
  refine (h f).trans (Finset.prod_le_prod₀ (fun v _ => conditioningNorm_nonneg _ _) (fun v _ => ?_))
  rw [conditioningNorm_eq_lpNorm, conditioningNorm_eq_lpNorm]
  exact FiniteLaw.lpNorm_mono _ hr hrr _

/-- **`lem:density:strong-F`, the uniform-convexity step.** Let `π` be a law on `X × X`
(weights on `Fin 2 → X`) with uniform marginals, whose centered bilinear `L^r` norm is at most
`c`: `|E_π f(x₀) g(x₁)| ≤ c ‖f‖_r ‖g‖_r` for mean-zero `f`, `g`. If `1 < r ≤ 2` and
`c ≤ r - 1`, then `π` has unit mixed `L^r`. This is `lem:density:uniform-convexity`
with `√((1 - m²)(1 - n²)) ≤ 1 - mn`. -/
theorem strongF_pair_unit_mixed (π : (Fin 2 → X) → ℝ) (hπ : ∀ x, 0 ≤ π x)
    (hπu : conditioningUniformCoords π) {r c : ℝ} (hr : 1 < r) (hr2 : r ≤ 2) (hc : c ≤ r - 1)
    (hcent : ∀ f g : X → ℝ, ∑ a, f a = 0 → ∑ a, g a = 0 →
      |∑ x, π x * (f (x 0) * g (x 1))| ≤ c * conditioningNorm r f * conditioningNorm r g) :
    conditioningUnitMixed π r := by
  intro f
  have hN : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  obtain ⟨F, hF⟩ : ∃ F : X → ℝ, F = fun a => |f 0 a| := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : X → ℝ, G = fun a => |f 1 a| := ⟨_, rfl⟩
  have hF0 : ∀ a, 0 ≤ F a := fun a => by rw [hF]; exact abs_nonneg _
  have hG0 : ∀ a, 0 ≤ G a := fun a => by rw [hG]; exact abs_nonneg _
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (FiniteLaw.uniform X).expect F := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (FiniteLaw.uniform X).expect G := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; exact FiniteLaw.expect_nonneg _ hF0
  have hn0 : 0 ≤ n := by rw [hn]; exact FiniteLaw.expect_nonneg _ hG0
  have hmarg : ∀ v (g : X → ℝ), ∑ x, π x * g (x v) = (∑ a, g a) / Fintype.card X := fun v g => by
    rw [conditioning_marginal_sum π hπu v g, div_eq_mul_inv]
  have hsum1 : ∑ x, π x = 1 := by
    have h := hmarg 0 (fun _ => 1)
    simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    rw [h]
    field_simp
  have hFc : ∑ a, (F a - m) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm,
      FiniteLaw.expect_uniform]
    field_simp
    ring
  have hGc : ∑ a, (G a - n) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn,
      FiniteLaw.expect_uniform]
    field_simp
    ring
  -- the expansion `E_π F G = m n + E_π (F - m)(G - n)`
  have hexp : ∑ x, π x * (F (x 0) * G (x 1)) =
      m * n + ∑ x, π x * ((F (x 0) - m) * (G (x 1) - n)) := by
    have e : ∀ x, π x * (F (x 0) * G (x 1)) = m * n * π x + m * (π x * (G (x 1) - n)) +
        n * (π x * (F (x 0) - m)) + π x * ((F (x 0) - m) * (G (x 1) - n)) := fun x => by ring
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsum1,
      hmarg 1 (fun a => G a - n), hmarg 0 (fun a => F a - m), hGc, hFc]
    ring
  -- uniform convexity
  have hUF := (FiniteLaw.uniform X).lpNorm_uniform_convexity hr hr2 F hF0
  have hUG := (FiniteLaw.uniform X).lpNorm_uniform_convexity hr hr2 G hG0
  rw [← hm, ← conditioningNorm_eq_lpNorm, ← conditioningNorm_eq_lpNorm] at hUF
  rw [← hn, ← conditioningNorm_eq_lpNorm, ← conditioningNorm_eq_lpNorm] at hUG
  have haF : conditioningNorm r F = conditioningNorm r (f 0) := by
    rw [hF, conditioningNorm_abs]
  have haG : conditioningNorm r G = conditioningNorm r (f 1) := by
    rw [hG, conditioningNorm_abs]
  rw [haF] at hUF
  rw [haG] at hUG
  have hcF := hcent (fun a => F a - m) (fun a => G a - n) hFc hGc
  set a := conditioningNorm r (f 0)
  set b := conditioningNorm r (f 1)
  set P := conditioningNorm r (fun a => F a - m)
  set Q := conditioningNorm r (fun a => G a - n)
  have ha0 : 0 ≤ a := conditioningNorm_nonneg _ _
  have hb0 : 0 ≤ b := conditioningNorm_nonneg _ _
  have hP0 : 0 ≤ P := conditioningNorm_nonneg _ _
  have hQ0 : 0 ≤ Q := conditioningNorm_nonneg _ _
  set t := r - 1 with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  -- `m ≤ a`, `n ≤ b`
  have hma : m ≤ a := by
    have : m ^ 2 ≤ a ^ 2 := by nlinarith [mul_nonneg ht0.le (sq_nonneg P)]
    exact (pow_le_pow_iff_left₀ hm0 ha0 (by norm_num)).1 this
  have hnb : n ≤ b := by
    have : n ^ 2 ≤ b ^ 2 := by nlinarith [mul_nonneg ht0.le (sq_nonneg Q)]
    exact (pow_le_pow_iff_left₀ hn0 hb0 (by norm_num)).1 this
  -- `t P Q ≤ a b - m n`
  have hkey : t * P * Q ≤ a * b - m * n := by
    have h1 : (t * P * Q) ^ 2 ≤ (a * b - m * n) ^ 2 := by
      have hA : t * P ^ 2 ≤ a ^ 2 - m ^ 2 := by linarith
      have hB : t * Q ^ 2 ≤ b ^ 2 - n ^ 2 := by linarith
      have hA0 : 0 ≤ t * P ^ 2 := mul_nonneg ht0.le (sq_nonneg P)
      have hB0 : 0 ≤ t * Q ^ 2 := mul_nonneg ht0.le (sq_nonneg Q)
      calc (t * P * Q) ^ 2 = (t * P ^ 2) * (t * Q ^ 2) := by ring
        _ ≤ (a ^ 2 - m ^ 2) * (b ^ 2 - n ^ 2) := mul_le_mul hA hB hB0 (le_trans hA0 hA)
        _ ≤ (a * b - m * n) ^ 2 := by nlinarith [sq_nonneg (a * n - b * m)]
    have hab : 0 ≤ a * b - m * n := by nlinarith [mul_le_mul hma hnb hn0 ha0]
    exact (pow_le_pow_iff_left₀ (by positivity) hab (by norm_num)).1 h1
  have hcPQ : c * P * Q ≤ t * P * Q := by
    have := mul_le_mul_of_nonneg_right hc (mul_nonneg hP0 hQ0)
    linarith [this]
  -- conclusion
  have hprod : ∀ x, |π x * ∏ v, f v (x v)| = π x * (F (x 0) * G (x 1)) := fun x => by
    rw [abs_mul, abs_of_nonneg (hπ x), Fin.prod_univ_two, abs_mul, hF, hG]
  calc |∑ x, π x * ∏ v, f v (x v)| ≤ ∑ x, |π x * ∏ v, f v (x v)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, π x * (F (x 0) * G (x 1)) := Finset.sum_congr rfl (fun x _ => hprod x)
    _ = m * n + ∑ x, π x * ((F (x 0) - m) * (G (x 1) - n)) := hexp
    _ ≤ m * n + c * P * Q := by
        have := le_abs_self (∑ x, π x * ((F (x 0) - m) * (G (x 1) - n)))
        linarith
    _ ≤ a * b := by linarith
    _ = ∏ v, conditioningNorm r (f v) := by rw [Fin.prod_univ_two]

omit [DecidableEq X] [Nonempty X] in
/-- Cauchy–Schwarz for a nonnegative weight: `(∑ π A B)² ≤ (∑ π A²)(∑ π B²)`. -/
theorem strongF_weighted_cs {Ω : Type*} [Fintype Ω] (π : Ω → ℝ) (hπ : ∀ x, 0 ≤ π x)
    (A B : Ω → ℝ) :
    (∑ x, π x * (A x * B x)) ^ 2 ≤ (∑ x, π x * A x ^ 2) * ∑ x, π x * B x ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x => Real.sqrt (π x) * A x)
    (fun x => Real.sqrt (π x) * B x)
  have e1 : ∀ x, Real.sqrt (π x) * A x * (Real.sqrt (π x) * B x) = π x * (A x * B x) :=
    fun x => by
      have := Real.mul_self_sqrt (hπ x)
      calc Real.sqrt (π x) * A x * (Real.sqrt (π x) * B x)
          = (Real.sqrt (π x) * Real.sqrt (π x)) * (A x * B x) := by ring
        _ = π x * (A x * B x) := by rw [this]
  have e2 : ∀ (C : Ω → ℝ) x, (Real.sqrt (π x) * C x) ^ 2 = π x * C x ^ 2 := fun C x => by
    rw [mul_pow, Real.sq_sqrt (hπ x)]
  simp only [e1, e2] at h
  exact h

omit [DecidableEq X] [Nonempty X] in
/-- **`lem:density:strong-F`, "Cauchy–Schwarz between the two objects".** If a law `π` on four
labels (weights on `Fin 4 → X`) has both pair marginals, on the labels `0, 1` and on the labels
`2, 3`, equal to a law `ν` with unit mixed `L^r`, then `π` has unit mixed `L^{2r}`. -/
theorem strongF_double_unit_mixed (π : (Fin 4 → X) → ℝ) (hπ : ∀ x, 0 ≤ π x)
    (ν : (Fin 2 → X) → ℝ)
    (h01 : ∀ h : (Fin 2 → X) → ℝ, ∑ x, π x * h ![x 0, x 1] = ∑ y, ν y * h y)
    (h23 : ∀ h : (Fin 2 → X) → ℝ, ∑ x, π x * h ![x 2, x 3] = ∑ y, ν y * h y)
    {r : ℝ} (hr : 0 < r) (hν : conditioningUnitMixed ν r) :
    conditioningUnitMixed π (2 * r) := by
  intro f
  set A : (Fin 4 → X) → ℝ := fun x => |f 0 (x 0) * f 1 (x 1)|
  set B : (Fin 4 → X) → ℝ := fun x => |f 2 (x 2) * f 3 (x 3)|
  -- the two squared pair integrals
  have hpair : ∀ (u v : Fin 4) (huv : ∀ h : (Fin 2 → X) → ℝ,
      ∑ x, π x * h ![x u, x v] = ∑ y, ν y * h y),
      ∑ x, π x * |f u (x u) * f v (x v)| ^ 2 ≤
        (conditioningNorm (2 * r) (f u) * conditioningNorm (2 * r) (f v)) ^ 2 := by
    intro u v huv
    have e := huv (fun y => f u (y 0) ^ 2 * f v (y 1) ^ 2)
    have e' : ∀ x, π x * |f u (x u) * f v (x v)| ^ 2 =
        π x * (fun y : Fin 2 → X => f u (y 0) ^ 2 * f v (y 1) ^ 2) ![x u, x v] := fun x => by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sq_abs, mul_pow]
    rw [Finset.sum_congr rfl (fun x _ => e' x), e]
    have hν' := hν (fun i a => if i = 0 then f u a ^ 2 else f v a ^ 2)
    simp only [Fin.prod_univ_two, Fin.isValue, ite_true, one_ne_zero, ite_false] at hν'
    rw [conditioningNorm_sq hr, conditioningNorm_sq hr] at hν'
    calc ∑ y, ν y * (f u (y 0) ^ 2 * f v (y 1) ^ 2)
        ≤ |∑ y, ν y * (f u (y 0) ^ 2 * f v (y 1) ^ 2)| := le_abs_self _
      _ ≤ conditioningNorm (2 * r) (f u) ^ 2 * conditioningNorm (2 * r) (f v) ^ 2 := hν'
      _ = (conditioningNorm (2 * r) (f u) * conditioningNorm (2 * r) (f v)) ^ 2 := by ring
  have hA := hpair 0 1 h01
  have hB := hpair 2 3 h23
  have hcs := strongF_weighted_cs π hπ A B
  have hS0 : 0 ≤ ∑ x, π x * (A x * B x) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hπ x) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  set n0 := conditioningNorm (2 * r) (f 0)
  set n1 := conditioningNorm (2 * r) (f 1)
  set n2 := conditioningNorm (2 * r) (f 2)
  set n3 := conditioningNorm (2 * r) (f 3)
  have hn : 0 ≤ n0 * n1 * (n2 * n3) := by
    have := conditioningNorm_nonneg (2 * r) (f 0)
    have := conditioningNorm_nonneg (2 * r) (f 1)
    have := conditioningNorm_nonneg (2 * r) (f 2)
    have := conditioningNorm_nonneg (2 * r) (f 3)
    positivity
  have hle : ∑ x, π x * (A x * B x) ≤ n0 * n1 * (n2 * n3) := by
    have h2 : (∑ x, π x * (A x * B x)) ^ 2 ≤ (n0 * n1 * (n2 * n3)) ^ 2 := by
      calc (∑ x, π x * (A x * B x)) ^ 2 ≤ (∑ x, π x * A x ^ 2) * ∑ x, π x * B x ^ 2 := hcs
        _ ≤ (n0 * n1) ^ 2 * (n2 * n3) ^ 2 :=
            mul_le_mul hA hB (Finset.sum_nonneg (fun x _ => mul_nonneg (hπ x) (sq_nonneg _)))
              (sq_nonneg _)
        _ = (n0 * n1 * (n2 * n3)) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ hS0 hn (by norm_num)).1 h2
  calc |∑ x, π x * ∏ v, f v (x v)| ≤ ∑ x, |π x * ∏ v, f v (x v)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, π x * (A x * B x) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [abs_mul, abs_of_nonneg (hπ x), Fin.prod_univ_four]
        simp only [A, B, ← abs_mul]
        ring_nf
    _ ≤ n0 * n1 * (n2 * n3) := hle
    _ = ∏ v, conditioningNorm (2 * r) (f v) := by rw [Fin.prod_univ_four]; ring

omit [DecidableEq X] [Nonempty X] in
/-- Products of laws with unit mixed `L^r` have unit mixed `L^r`: the law of
`(x, y) ∈ (Fin a → X) × (Fin b → X)`, written on `Fin (a + b) → X` with `Fin.append`. -/
theorem strongF_prod_unit_mixed {a b : ℕ} (π₁ : (Fin a → X) → ℝ) (π₂ : (Fin b → X) → ℝ)
    {r : ℝ} (h₁ : conditioningUnitMixed π₁ r) (h₂ : conditioningUnitMixed π₂ r) :
    conditioningUnitMixed (fun x : Fin (a + b) → X =>
      π₁ (fun i => x (Fin.castAdd b i)) * π₂ (fun j => x (Fin.natAdd a j))) r := by
  intro f
  have e : ∑ x : Fin (a + b) → X, π₁ (fun i => x (Fin.castAdd b i)) *
      π₂ (fun j => x (Fin.natAdd a j)) * ∏ v, f v (x v) =
      (∑ u, π₁ u * ∏ i, f (Fin.castAdd b i) (u i)) *
        ∑ w, π₂ w * ∏ j, f (Fin.natAdd a j) (w j) := by
    rw [← Fintype.sum_equiv (Fin.appendEquiv a b) (fun uw : (Fin a → X) × (Fin b → X) =>
      π₁ uw.1 * π₂ uw.2 * ((∏ i, f (Fin.castAdd b i) (uw.1 i)) *
        ∏ j, f (Fin.natAdd a j) (uw.2 j))) _ (fun uw => by
          simp only [Fin.appendEquiv_apply, Fin.append_left, Fin.append_right, Fin.prod_univ_add])]
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun w _ => ?_))
    ring
  rw [e, abs_mul, Fin.prod_univ_add]
  exact mul_le_mul (h₁ _) (h₂ _) (abs_nonneg _)
    (Finset.prod_nonneg (fun i _ => conditioningNorm_nonneg _ _))

omit [DecidableEq X] in
/-- The uniform law of one label has unit mixed `L^r` for `r ≥ 1`. -/
theorem strongF_uniform_unit_mixed {r : ℝ} (hr : 1 ≤ r) :
    conditioningUnitMixed (fun _ : Fin 1 → X => ((Fintype.card (Fin 1 → X) : ℝ))⁻¹) r := by
  intro f
  rw [Fin.prod_univ_one]
  have hN : (0 : ℝ) < Fintype.card (Fin 1 → X) := by exact_mod_cast Fintype.card_pos
  have e : ∑ x : Fin 1 → X, (Fintype.card (Fin 1 → X) : ℝ)⁻¹ * ∏ v, f v (x v) =
      (FiniteLaw.uniform X).expect (f 0) := by
    rw [FiniteLaw.expect_uniform, ← Finset.mul_sum,
      ← Fintype.sum_equiv (Equiv.funUnique (Fin 1) X).symm (fun a => f 0 a) _ (fun a => by simp)]
    have hc : (Fintype.card (Fin 1 → X) : ℝ) = Fintype.card X := by
      rw [Fintype.card_fun, Fintype.card_fin, pow_one]
    rw [hc]
    ring
  rw [e, conditioningNorm_eq_lpNorm]
  calc |(FiniteLaw.uniform X).expect (f 0)|
      ≤ (FiniteLaw.uniform X).expect (fun a => |f 0 a|) := FiniteLaw.abs_expect_le _ _
    _ = (FiniteLaw.uniform X).lpNorm 1 (f 0) := by
        simp [FiniteLaw.lpNorm, FiniteLaw.moment]
    _ ≤ (FiniteLaw.uniform X).lpNorm r (f 0) := FiniteLaw.lpNorm_mono _ one_pos hr _

omit [DecidableEq X] in
/-- **Hölder within a repeated label.** If `π` has unit mixed `L^r`, its emission that repeats
every label twice has unit mixed `L^{2r}`:
`|E_π ∏_v f_{v,0}(x_v) f_{v,1}(x_v)| ≤ ∏_v ‖f_{v,0}‖_{2r} ‖f_{v,1}‖_{2r}`. -/
theorem strongF_emission_double {d : ℕ} (π : (Fin d → X) → ℝ) {r : ℝ} (hr : 0 < r)
    (h : conditioningUnitMixed π r) (f : Fin d → Fin 2 → X → ℝ) :
    |∑ x, π x * ∏ v, ∏ j, f v j (x v)| ≤ ∏ v, ∏ j, conditioningNorm (2 * r) (f v j) := by
  have h1 := h (fun v a => f v 0 a * f v 1 a)
  simp only [Fin.prod_univ_two]
  refine h1.trans (Finset.prod_le_prod₀ (fun v _ => conditioningNorm_nonneg _ _)
    (fun v _ => conditioningNorm_mul_le hr _ _))

omit [DecidableEq X] in
/-- **Hölder within a label repeated four times**: unit mixed `L^r` gives unit mixed `L^{4r}` for
the emission that repeats every label four times. -/
theorem strongF_emission_quad {d : ℕ} (π : (Fin d → X) → ℝ) {r : ℝ} (hr : 0 < r)
    (h : conditioningUnitMixed π r) (f : Fin d → Fin 4 → X → ℝ) :
    |∑ x, π x * ∏ v, ∏ j, f v j (x v)| ≤ ∏ v, ∏ j, conditioningNorm (4 * r) (f v j) := by
  have h1 := h (fun v a => f v 0 a * f v 1 a * (f v 2 a * f v 3 a))
  have e : ∀ x : Fin d → X, ∏ v, ∏ j, f v j (x v) =
      ∏ v, (fun v a => f v 0 a * f v 1 a * (f v 2 a * f v 3 a)) v (x v) := fun x => by
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [Fin.prod_univ_four]
    ring
  simp only [e]
  refine h1.trans (Finset.prod_le_prod₀ (fun v _ => conditioningNorm_nonneg _ _) (fun v _ => ?_))
  have hr2 : 0 < 2 * r := by linarith
  have h4 : 2 * (2 * r) = 4 * r := by ring
  have hA := conditioningNorm_mul_le hr2 (f v 0) (f v 1)
  have hB := conditioningNorm_mul_le hr2 (f v 2) (f v 3)
  rw [h4] at hA hB
  calc conditioningNorm r (fun a => f v 0 a * f v 1 a * (f v 2 a * f v 3 a))
      ≤ conditioningNorm (2 * r) (fun a => f v 0 a * f v 1 a) *
          conditioningNorm (2 * r) (fun a => f v 2 a * f v 3 a) :=
        conditioningNorm_mul_le hr (fun a => f v 0 a * f v 1 a) (fun a => f v 2 a * f v 3 a)
    _ ≤ (conditioningNorm (4 * r) (f v 0) * conditioningNorm (4 * r) (f v 1)) *
          (conditioningNorm (4 * r) (f v 2) * conditioningNorm (4 * r) (f v 3)) :=
        mul_le_mul hA hB (conditioningNorm_nonneg _ _)
          (mul_nonneg (conditioningNorm_nonneg _ _) (conditioningNorm_nonneg _ _))
    _ = ∏ j, conditioningNorm (4 * r) (f v j) := by rw [Fin.prod_univ_four]; ring

end Mixed

section Numerics

/-- `(p - 1)^{-2/9} ≤ 1/8` for `p ≥ 2^18` (the interpolated pair bound is at most `9/8 - 1`). -/
theorem strongF_pair_numeric {p : ℝ} (hp : 2 ^ 18 ≤ p) : (p - 1) ^ (-(2 / 9 : ℝ)) ≤ 1 / 8 := by
  have h17 : (2 : ℝ) ^ 17 ≤ p - 1 := by norm_num at hp ⊢; linarith
  have hpos : 0 < p - 1 := lt_of_lt_of_le (by positivity) h17
  rw [Real.rpow_neg hpos.le, one_div]
  apply inv_anti₀ (by norm_num)
  calc (8 : ℝ) = (2 : ℝ) ^ ((3 : ℕ) : ℝ) := by norm_num
    _ ≤ (2 : ℝ) ^ ((17 : ℝ) * (2 / 9)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = ((2 : ℝ) ^ ((17 : ℕ) : ℝ)) ^ (2 / 9 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num)]
        norm_num
    _ ≤ (p - 1) ^ (2 / 9 : ℝ) := by
        rw [Real.rpow_natCast]
        exact Real.rpow_le_rpow (by positivity) h17 (by norm_num)

/-- `2 p^{-1/4} ≤ 1/3` for `p ≥ 2^24` (the Paley edge bound is at most `4/3 - 1`; the paper
writes `6 p^{-1/4} ≤ 3/32`). -/
theorem strongF_edge_numeric {p : ℝ} (hp : 2 ^ 24 ≤ p) : 2 * p ^ (-(1 / 4 : ℝ)) ≤ 1 / 3 := by
  have hpos : 0 < p := lt_of_lt_of_le (by positivity) hp
  have h64 : (64 : ℝ) ≤ p ^ (1 / 4 : ℝ) := by
    calc (64 : ℝ) = ((2 : ℝ) ^ ((24 : ℕ) : ℝ)) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ p ^ (1 / 4 : ℝ) := by
          rw [Real.rpow_natCast]
          exact Real.rpow_le_rpow (by positivity) hp (by norm_num)
  rw [Real.rpow_neg hpos.le]
  have hq : 0 < p ^ (1 / 4 : ℝ) := by linarith
  rw [← div_eq_mul_inv, div_le_iff₀ hq]
  linarith

end Numerics


section Coords

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- A weight with uniform coordinates (and at least one coordinate) sums to one. -/
theorem uniformCoords_sum_one {d : ℕ} {π : (Fin d → X) → ℝ} (h : conditioningUniformCoords π)
    (v₀ : Fin d) : ∑ x, π x = 1 := by
  have e := conditioning_marginal_sum π h v₀ (fun _ => 1)
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at e
  rw [e]
  have hN : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

omit [Nonempty X] in
/-- Products of weights with uniform coordinates have uniform coordinates. -/
theorem uniformCoords_prod {a b : ℕ} (π₁ : (Fin a → X) → ℝ) (π₂ : (Fin b → X) → ℝ)
    (h₁ : conditioningUniformCoords π₁) (h₂ : conditioningUniformCoords π₂)
    (h₁1 : ∑ u, π₁ u = 1) (h₂1 : ∑ w, π₂ w = 1) :
    conditioningUniformCoords (fun x : Fin (a + b) → X =>
      π₁ (fun i => x (Fin.castAdd b i)) * π₂ (fun j => x (Fin.natAdd a j))) := by
  intro v c
  rw [Finset.sum_filter]
  have key : ∑ x : Fin (a + b) → X, (if x v = c then
      π₁ (fun i => x (Fin.castAdd b i)) * π₂ (fun j => x (Fin.natAdd a j)) else 0) =
      ∑ uw : (Fin a → X) × (Fin b → X),
        (if Fin.append uw.1 uw.2 v = c then π₁ uw.1 * π₂ uw.2 else 0) := by
    refine (Fintype.sum_equiv (Fin.appendEquiv a b) _ _ (fun uw => ?_)).symm
    simp [Fin.appendEquiv_apply, Fin.append_left, Fin.append_right]
  rw [key, Fintype.sum_prod_type]
  obtain ⟨i, rfl⟩ | ⟨j, rfl⟩ : (∃ i, v = Fin.castAdd b i) ∨ (∃ j, v = Fin.natAdd a j) :=
    Fin.addCases (fun i => Or.inl ⟨i, rfl⟩) (fun j => Or.inr ⟨j, rfl⟩) v
  · simp only [Fin.append_left]
    have e : ∀ u : Fin a → X, ∑ w : Fin b → X, (if u i = c then π₁ u * π₂ w else 0) =
        (if u i = c then π₁ u else 0) := by
      intro u
      split_ifs
      · rw [← Finset.mul_sum, h₂1, mul_one]
      · simp
    simp only [e]
    rw [← Finset.sum_filter]
    exact h₁ i c
  · simp only [Fin.append_right]
    have e : ∀ u : Fin a → X, ∑ w : Fin b → X, (if w j = c then π₁ u * π₂ w else 0) =
        π₁ u * ∑ w ∈ Finset.univ.filter (fun w : Fin b → X => w j = c), π₂ w := by
      intro u
      rw [Finset.sum_filter, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun w _ => by split_ifs <;> simp)
    simp only [e]
    rw [← Finset.sum_mul, h₁1, one_mul]
    exact h₂ j c

omit [Nonempty X] in
/-- The core's coordinates are uniform when its two objects have a law with uniform
coordinates. -/
theorem uniformCoords_of_pairs (κ : (Fin 4 → X) → ℝ) (ν : (Fin 2 → X) → ℝ)
    (hνu : conditioningUniformCoords ν)
    (h01 : ∀ h : (Fin 2 → X) → ℝ, ∑ x, κ x * h ![x 0, x 1] = ∑ y, ν y * h y)
    (h23 : ∀ h : (Fin 2 → X) → ℝ, ∑ x, κ x * h ![x 2, x 3] = ∑ y, ν y * h y) :
    conditioningUniformCoords κ := by
  intro v c
  rw [Finset.sum_filter]
  have c01 : ∀ k : Fin 2, ∑ x, (if (![x 0, x 1] : Fin 2 → X) k = c then κ x else 0) =
      1 / Fintype.card X := by
    intro k
    have e := h01 (fun y => if y k = c then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero] at e
    rw [e, ← Finset.sum_filter]
    exact hνu k c
  have c23 : ∀ k : Fin 2, ∑ x, (if (![x 2, x 3] : Fin 2 → X) k = c then κ x else 0) =
      1 / Fintype.card X := by
    intro k
    have e := h23 (fun y => if y k = c then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero] at e
    rw [e, ← Finset.sum_filter]
    exact hνu k c
  have hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by fin_cases v <;> simp
  rcases hv with rfl | rfl | rfl | rfl
  · rw [← c01 0]
    exact Finset.sum_congr rfl (fun x _ => by simp; congr)
  · rw [← c01 1]
    exact Finset.sum_congr rfl (fun x _ => by simp)
  · rw [← c23 0]
    exact Finset.sum_congr rfl (fun x _ => by simp; congr)
  · rw [← c23 1]
    exact Finset.sum_congr rfl (fun x _ => by simp)

omit [Nonempty X] in
/-- The uniform law of one label has uniform coordinates. -/
theorem uniformCoords_uniform_one :
    conditioningUniformCoords (fun _ : Fin 1 → X => ((Fintype.card (Fin 1 → X) : ℝ))⁻¹) := by
  intro v c
  have hv : v = 0 := Subsingleton.elim v 0
  subst hv
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun x : Fin 1 → X => x 0 = c)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨fun _ => c, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hx
      funext i
      rw [Subsingleton.elim i 0, hx]
    · intro hx
      rw [hx]
  rw [hcard, Fintype.card_fun, Fintype.card_fin, pow_one]
  simp

end Coords



section DistinctPair

variable (X : Type*) [Fintype X] [DecidableEq X]

/-- The uniform law on ordered distinct pairs of `X` (weights on `Fin 2 → X`). -/
noncomputable def distinctPair : (Fin 2 → X) → ℝ :=
  fun y => if y 0 = y 1 then 0 else ((Fintype.card X : ℝ) * ((Fintype.card X : ℝ) - 1))⁻¹

variable {X}

/-- Sums against `distinctPair` as double sums over distinct pairs. -/
theorem sum_distinctPair (F : X → X → ℝ) :
    ∑ y, distinctPair X y * F (y 0) (y 1) =
      ((Fintype.card X : ℝ) * ((Fintype.card X : ℝ) - 1))⁻¹ *
        ∑ a, ∑ b, (if a = b then 0 else F a b) := by
  rw [Fintype.sum_equiv (finTwoArrowEquiv X) _ (fun ab : X × X =>
    (if ab.1 = ab.2 then 0 else ((Fintype.card X : ℝ) * ((Fintype.card X : ℝ) - 1))⁻¹) *
      F ab.1 ab.2) (fun y => by simp [distinctPair]), Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  split_ifs <;> simp

theorem distinctPair_nonneg (y : Fin 2 → X) : 0 ≤ distinctPair X y := by
  unfold distinctPair
  split_ifs
  · exact le_rfl
  · rcases Nat.eq_zero_or_pos (Fintype.card X) with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast h
      exact inv_nonneg.2 (mul_nonneg (by linarith) (by linarith))

/-- The uniform ordered-distinct pair has uniform coordinates (`|X| ≥ 2`). -/
theorem distinctPair_uniformCoords (hX : 2 ≤ Fintype.card X) :
    conditioningUniformCoords (distinctPair X) := by
  intro v c
  have hN : (2 : ℝ) ≤ Fintype.card X := by exact_mod_cast hX
  have hN0 : (Fintype.card X : ℝ) ≠ 0 := by linarith
  have hN1 : (Fintype.card X : ℝ) - 1 ≠ 0 := by linarith
  rw [Finset.sum_filter]
  have hv : v = 0 ∨ v = 1 := by fin_cases v <;> simp
  have hcount : ∑ b : X, (if c = b then (0 : ℝ) else 1) = (Fintype.card X : ℝ) - 1 := by
    have h1 : ∑ b : X, (if c = b then (0 : ℝ) else 1) = ∑ b : X, (1 - if c = b then 1 else 0) :=
      Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
    rw [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp
  rcases hv with rfl | rfl
  · have e := sum_distinctPair (X := X) (fun a _ => if a = c then (1 : ℝ) else 0)
    have e' : ∑ y, (if y 0 = c then distinctPair X y else 0) =
        ∑ y, distinctPair X y * (fun a (_ : X) => if a = c then (1 : ℝ) else 0) (y 0) (y 1) :=
      Finset.sum_congr rfl (fun y _ => by by_cases h : y 0 = c <;> simp [h])
    rw [e', e]
    have e2 : ∑ a : X, ∑ b : X, (if a = b then 0 else
        (fun a (_ : X) => if a = c then (1 : ℝ) else 0) a b) =
        ∑ b : X, (if c = b then (0 : ℝ) else 1) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.sum_eq_single c (fun a _ ha => by simp [ha])
        (fun h => absurd (Finset.mem_univ c) h)]
      simp
    rw [e2, hcount]
    field_simp
  · have e := sum_distinctPair (X := X) (fun _ b => if b = c then (1 : ℝ) else 0)
    have e' : ∑ y, (if y 1 = c then distinctPair X y else 0) =
        ∑ y, distinctPair X y * (fun (_ : X) b => if b = c then (1 : ℝ) else 0) (y 0) (y 1) :=
      Finset.sum_congr rfl (fun y _ => by by_cases h : y 1 = c <;> simp [h])
    rw [e', e]
    have e2 : ∑ a : X, ∑ b : X, (if a = b then 0 else
        (fun (_ : X) b => if b = c then (1 : ℝ) else 0) a b) =
        ∑ a : X, (if c = a then (0 : ℝ) else 1) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ c) h)]
      by_cases h : a = c
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [e2, hcount]
    field_simp

/-- **The centered bilinear `L²` norm of the uniform ordered-distinct pair is `1/(|X| - 1)`**:
for mean-zero `g` (and any `f`), `E f(x) g(y) = -E_{unif}[f g]/(|X| - 1)`, so
`|E f(x) g(y)| ≤ ‖f‖₂ ‖g‖₂/(|X| - 1)`. (The paper's `L²` endpoint of the interpolation.) -/
theorem distinctPair_centered_L2 (hX : 2 ≤ Fintype.card X) (f g : X → ℝ)
    (hg : ∑ a, g a = 0) :
    |∑ y, distinctPair X y * (f (y 0) * g (y 1))| ≤
      ((Fintype.card X : ℝ) - 1)⁻¹ * conditioningNorm 2 f * conditioningNorm 2 g := by
  have hN : (2 : ℝ) ≤ Fintype.card X := by exact_mod_cast hX
  have hN0 : (0 : ℝ) < Fintype.card X := by linarith
  have hN1 : (0 : ℝ) < (Fintype.card X : ℝ) - 1 := by linarith
  have e := sum_distinctPair (X := X) (fun a b => f a * g b)
  have hfg : ∑ a : X, ∑ b : X, (if a = b then 0 else f a * g b) = -∑ a, f a * g a := by
    have h1 : ∀ a : X, ∑ b : X, (if a = b then 0 else f a * g b) = f a * ∑ b, g b - f a * g a := by
      intro a
      have : ∑ b : X, (if a = b then 0 else f a * g b) =
          ∑ b : X, (f a * g b - if a = b then f a * g b else 0) :=
        Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
      rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, ← Finset.mul_sum]
      simp
    simp only [h1, hg, mul_zero, zero_sub, Finset.sum_neg_distrib]
  rw [e, hfg]
  -- Cauchy–Schwarz
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  set Sf := ∑ a, f a ^ 2
  set Sg := ∑ a, g a ^ 2
  have hSf : 0 ≤ Sf := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hSg : 0 ≤ Sg := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have habs : |∑ a, f a * g a| ≤ Real.sqrt Sf * Real.sqrt Sg := by
    rw [← Real.sqrt_mul hSf]
    exact Real.abs_le_sqrt hcs
  have hnorm : ∀ u : X → ℝ, conditioningNorm 2 u = Real.sqrt ((∑ a, u a ^ 2) / Fintype.card X) := by
    intro u
    unfold conditioningNorm
    rw [Real.sqrt_eq_rpow]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    · norm_num
  rw [hnorm f, hnorm g, Real.sqrt_div hSf, Real.sqrt_div hSg]
  have hsN : 0 < Real.sqrt (Fintype.card X) := Real.sqrt_pos.2 hN0
  have hsN2 : Real.sqrt (Fintype.card X) * Real.sqrt (Fintype.card X) = Fintype.card X :=
    Real.mul_self_sqrt hN0.le
  rw [abs_mul, abs_neg, abs_of_nonneg (inv_nonneg.2 (mul_nonneg hN0.le hN1.le))]
  calc ((Fintype.card X : ℝ) * ((Fintype.card X : ℝ) - 1))⁻¹ * |∑ a, f a * g a|
      ≤ ((Fintype.card X : ℝ) * ((Fintype.card X : ℝ) - 1))⁻¹ * (Real.sqrt Sf * Real.sqrt Sg) :=
        mul_le_mul_of_nonneg_left habs (inv_nonneg.2 (mul_nonneg hN0.le hN1.le))
    _ = ((Fintype.card X : ℝ) - 1)⁻¹ * (Real.sqrt Sf / Real.sqrt (Fintype.card X)) *
          (Real.sqrt Sg / Real.sqrt (Fintype.card X)) := by
        field_simp
        rw [Real.sq_sqrt hN0.le]
        ring

end DistinctPair

section Folds

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- **`lem:density:strong-F`, the native two-layer fold: unit mixed field `L^{5/2}`.**

Inputs (construction-specific, named):
* `ν` is the uniform ordered-distinct pair law, with uniform marginals, and `hνcent` is its
  centered bilinear `L^{9/8}` bound `(p - 1)^{-2/9}` (the paper interpolates between the
  centered `L¹` norm `≤ 1` and the `L²` norm `1/(p-1)`);
* `κ` is the strict four-label `K_{2,2}` outer core, whose two objects (labels `0, 1` and
  `2, 3`) have law `ν` (`h01`, `h23`: the Paley count of common neighbours);
* the adjoined law `κ ⊗ ν` (the core and an independent ordered-distinct middle pair, on
  `Fin (4 + 2) → X`) is `(1 - η) π + η ρ`. Here `π` is the native two-layer fold (the middle
  pair conditioned to avoid the four core labels), `η ≤ 8/p` is the excluded mass, and the
  excluded part `ρ` has uniform coordinates (translation invariance). The uniform coordinates
  of `κ ⊗ ν` are derived (`uniformCoords_of_pairs`, `uniformCoords_prod`).

Proved chain: `ν` has unit mixed `L^{9/8}` (`strongF_pair_unit_mixed`, since
`(p-1)^{-2/9} ≤ 1/8`); `κ` has unit field `L^{9/4}` (`strongF_double_unit_mixed`); `κ ⊗ ν` has
unit mixed `L^{9/4}` (`strongF_prod_unit_mixed`); `lem:density:conditioning` with `s = 9/4`,
`r = 5/2` (`α = 2/27 ≥ 1281 · 8/p` for `p ≥ 2^18`). -/
theorem strongF_two_layer (ν : (Fin 2 → X) → ℝ) (hν : ∀ x, 0 ≤ ν x)
    (hνu : conditioningUniformCoords ν) {p : ℝ} (hp : 2 ^ 18 ≤ p)
    (hνcent : ∀ f g : X → ℝ, ∑ a, f a = 0 → ∑ a, g a = 0 →
      |∑ x, ν x * (f (x 0) * g (x 1))| ≤
        (p - 1) ^ (-(2 / 9 : ℝ)) * conditioningNorm (9 / 8) f * conditioningNorm (9 / 8) g)
    (κ : (Fin 4 → X) → ℝ) (hκ : ∀ x, 0 ≤ κ x)
    (h01 : ∀ h : (Fin 2 → X) → ℝ, ∑ x, κ x * h ![x 0, x 1] = ∑ y, ν y * h y)
    (h23 : ∀ h : (Fin 2 → X) → ℝ, ∑ x, κ x * h ![x 2, x 3] = ∑ y, ν y * h y)
    (π ρ : (Fin (4 + 2) → X) → ℝ) (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 8 / p)
    (hmix : ∀ x, κ (fun i => x (Fin.castAdd 2 i)) * ν (fun j => x (Fin.natAdd 4 j)) =
      (1 - η) * π x + η * ρ x)
    (hρu : conditioningUniformCoords ρ) :
    conditioningUnitMixed π (5 / 2) := by
  have hκu := uniformCoords_of_pairs κ ν hνu h01 h23
  have hπ₀u := uniformCoords_prod κ ν hκu hνu (uniformCoords_sum_one hκu 0)
    (uniformCoords_sum_one hνu 0)
  have hνmix : conditioningUnitMixed ν (9 / 8) :=
    strongF_pair_unit_mixed ν hν hνu (by norm_num) (by norm_num)
      (by linarith [strongF_pair_numeric hp]) hνcent
  have hκmix : conditioningUnitMixed κ (2 * (9 / 8)) :=
    strongF_double_unit_mixed κ hκ ν h01 h23 (by norm_num) hνmix
  have hκ' : conditioningUnitMixed κ (9 / 4) := by
    have e : (2 : ℝ) * (9 / 8) = 9 / 4 := by norm_num
    rw [e] at hκmix
    exact hκmix
  have hν' : conditioningUnitMixed ν (9 / 4) := hνmix.mono (by norm_num) (by norm_num)
  have h0 := strongF_prod_unit_mixed κ ν hκ' hν'
  have hp0 : (0 : ℝ) < 2 ^ 18 := by positivity
  have hη8 : η ≤ 8 / 2 ^ 18 := hη.trans (div_le_div_of_nonneg_left (by norm_num) hp0 hp)
  refine conditioning_unit_mixed (by norm_num) _ π ρ hπ hπ1 hρ hρ1 hη0
    (lt_of_le_of_lt hη8 (by norm_num)) hmix hπ₀u hρu (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h0 ?_
  have := mul_le_mul_of_nonneg_left hη8 (by norm_num : (0 : ℝ) ≤ 1280 + 1)
  refine this.trans ?_
  norm_num

/-- **`lem:density:strong-F`, the native one-layer (three-label) fold: unit mixed field
`L^{7/5}`.**

Inputs (construction-specific, named):
* `ε` is the strict Paley edge law in class three, with uniform marginals, and `hεcent` is its
  centered bilinear `L^{4/3}` bound `2 p^{-1/4}` (the paper's interpolation at `4/3` gives
  `(p+1)^{3/4}/(p-1) ≤ 2p^{-1/4}`);
* the adjoined law `ε ⊗ unif` (an independent middle label, on `Fin (2 + 1) → X`) is
  `(1 - η) π + η ρ`. Here `π` is the native fold (the two endpoint coincidences removed),
  `η ≤ 2/p`, and `ρ` has uniform coordinates.

Proved chain: `ε` has unit mixed `L^{4/3}` (`strongF_pair_unit_mixed`, since
`2p^{-1/4} ≤ 1/3`); the uniform label has unit mixed `L^{4/3}`; the product
(`strongF_prod_unit_mixed`); `lem:density:conditioning`, second range, with `s = 4/3`,
`r = 7/5` (`α = 1/8 ≥ 1025 · 2/p` for `p ≥ 2^24`). -/
theorem strongF_one_layer (ε : (Fin 2 → X) → ℝ) (hε : ∀ x, 0 ≤ ε x)
    (hεu : conditioningUniformCoords ε) {p : ℝ} (hp : 2 ^ 24 ≤ p)
    (hεcent : ∀ f g : X → ℝ, ∑ a, f a = 0 → ∑ a, g a = 0 →
      |∑ x, ε x * (f (x 0) * g (x 1))| ≤
        2 * p ^ (-(1 / 4 : ℝ)) * conditioningNorm (4 / 3) f * conditioningNorm (4 / 3) g)
    (π ρ : (Fin (2 + 1) → X) → ℝ) (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 2 / p)
    (hmix : ∀ x, ε (fun i => x (Fin.castAdd 1 i)) * (Fintype.card (Fin 1 → X) : ℝ)⁻¹ =
      (1 - η) * π x + η * ρ x)
    (hρu : conditioningUniformCoords ρ) :
    conditioningUnitMixed π (7 / 5) := by
  have hUu := uniformCoords_uniform_one (X := X)
  have hπ₀u := uniformCoords_prod ε _ hεu hUu (uniformCoords_sum_one hεu 0)
    (uniformCoords_sum_one hUu 0)
  have hεmix : conditioningUnitMixed ε (4 / 3) :=
    strongF_pair_unit_mixed ε hε hεu (by norm_num) (by norm_num)
      (by linarith [strongF_edge_numeric hp]) hεcent
  have hu := strongF_uniform_unit_mixed (X := X) (r := 4 / 3) (by norm_num)
  have h0 := strongF_prod_unit_mixed ε _ hεmix hu
  have hp0 : (0 : ℝ) < 2 ^ 24 := by positivity
  have hη2 : η ≤ 2 / 2 ^ 24 := hη.trans (div_le_div_of_nonneg_left (by norm_num) hp0 hp)
  refine conditioning_unit_mixed_small_exponent (by norm_num) _ π ρ hπ hπ1 hρ hρ1 hη0
    (lt_of_le_of_lt hη2 (by norm_num)) hmix hπ₀u hρu (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h0 ?_
  have := mul_le_mul_of_nonneg_left hη2 (by norm_num : (0 : ℝ) ≤ 1024 + 1)
  refine this.trans ?_
  norm_num

omit [DecidableEq X] in
/-- **`lem:density:strong-F`, the emissions.** The twelve-slot emission of the two-layer fold
(each of the six labels repeated twice) has unit mixed `L^5`, and that of the one-layer fold
(each of the three labels repeated four times) has unit mixed `L^{28/5}`. -/
theorem strongF_emissions {π₂ : (Fin (4 + 2) → X) → ℝ} {π₁ : (Fin (2 + 1) → X) → ℝ}
    (h₂ : conditioningUnitMixed π₂ (5 / 2)) (h₁ : conditioningUnitMixed π₁ (7 / 5)) :
    (∀ f : Fin (4 + 2) → Fin 2 → X → ℝ,
      |∑ x, π₂ x * ∏ v, ∏ j, f v j (x v)| ≤ ∏ v, ∏ j, conditioningNorm 5 (f v j)) ∧
    (∀ f : Fin (2 + 1) → Fin 4 → X → ℝ,
      |∑ x, π₁ x * ∏ v, ∏ j, f v j (x v)| ≤ ∏ v, ∏ j, conditioningNorm (28 / 5) (f v j)) := by
  refine ⟨fun f => ?_, fun f => ?_⟩
  · have h := strongF_emission_double π₂ (by norm_num) h₂ f
    have e : (2 : ℝ) * (5 / 2) = 5 := by norm_num
    rw [e] at h
    exact h
  · have h := strongF_emission_quad π₁ (by norm_num) h₁ f
    have e : (4 : ℝ) * (7 / 5) = 28 / 5 := by norm_num
    rw [e] at h
    exact h

/-- **`lem:density:strong-F`, "in particular".** The density endpoint of a unit mixed `L^r` bound
on `d` slots is `d/r` (`30_density_moment_upgrade.tex`). For the twelve-slot emissions it is
`12/5` and `12/(28/5) = 15/7`, both larger than `2θ_*` with `θ_* = 1014587/1000000`
(`eq:density:parameter-range`). -/
theorem strongF_density_endpoints :
    (12 : ℝ) / 5 = 12 / 5 ∧ 2 * (1014587 / 1000000 : ℝ) < 12 / 5 ∧
      (12 : ℝ) / (28 / 5) = 15 / 7 ∧ 2 * (1014587 / 1000000 : ℝ) < 15 / 7 := by
  norm_num

/-- `strongF_two_layer` with the middle pair the actual uniform ordered-distinct pair
`distinctPair X` (`|X| ≥ 2`). Its nonnegativity and uniform coordinates are proved
(`distinctPair_nonneg`, `distinctPair_uniformCoords`), and so is its centered `L²` bound
(`distinctPair_centered_L2`). The remaining pair input is the interpolated `L^{9/8}` bound. -/
theorem strongF_two_layer_distinct (hX : 2 ≤ Fintype.card X) {p : ℝ} (hp : 2 ^ 18 ≤ p)
    (hνcent : ∀ f g : X → ℝ, ∑ a, f a = 0 → ∑ a, g a = 0 →
      |∑ x, distinctPair X x * (f (x 0) * g (x 1))| ≤
        (p - 1) ^ (-(2 / 9 : ℝ)) * conditioningNorm (9 / 8) f * conditioningNorm (9 / 8) g)
    (κ : (Fin 4 → X) → ℝ) (hκ : ∀ x, 0 ≤ κ x)
    (h01 : ∀ h : (Fin 2 → X) → ℝ, ∑ x, κ x * h ![x 0, x 1] = ∑ y, distinctPair X y * h y)
    (h23 : ∀ h : (Fin 2 → X) → ℝ, ∑ x, κ x * h ![x 2, x 3] = ∑ y, distinctPair X y * h y)
    (π ρ : (Fin (4 + 2) → X) → ℝ) (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 8 / p)
    (hmix : ∀ x, κ (fun i => x (Fin.castAdd 2 i)) *
      distinctPair X (fun j => x (Fin.natAdd 4 j)) = (1 - η) * π x + η * ρ x)
    (hρu : conditioningUniformCoords ρ) :
    conditioningUnitMixed π (5 / 2) :=
  strongF_two_layer (distinctPair X) distinctPair_nonneg (distinctPair_uniformCoords hX) hp
    hνcent κ hκ h01 h23 π ρ hπ hπ1 hρ hρ1 hη0 hη hmix hρu

end Folds

end Sarkozy.DensityUpgrade
