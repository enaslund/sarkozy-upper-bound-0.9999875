module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The two-feature spectral calculation (`lem:two-feature-spectrum`)

`paper/sections/21_middle_records.tex`, `subsec:middle-records:notation`,
`lem:two-feature-spectrum`. Let `V : H₀ → 𝓗` be an isometry and `A : H₀ → 𝓗` satisfy
`V^* A = a I + b P` and `A^* A = c I`, where `P^* = -P` and `P^* P = q I` on `H₀`, and `r = √q`.
Then `δ = c - a² - b² q ≥ 0`,
* `‖A V^* + V A^*‖ = |a| + √(c - b² q)` (`TwoFeature.sym_norm_le`, `TwoFeature.sym_attained`,
  and `TwoFeature.opNorm_symOp` for the operator norm in finite dimension);
* `‖A V^* - V A^*‖ = |b| r + √(c - a²)` (`TwoFeature.skew_norm_le`, `TwoFeature.skew_attained`,
  `TwoFeature.opNorm_skewOp`);
* every eigenvalue of `A V^* + V A^*` lies in `{0, a ± √(c - b² q)}` (`TwoFeature.sym_eigen`),
  so in finite dimension its spectrum does (`TwoFeature.spectrum_symOp_subset`).

**The setting.** `H₀` and `𝓗` are arbitrary real inner product spaces; the adjoints `V^*`, `A^*`
are given as linear maps `Vs`, `As` with the adjoint relations as fields (`TwoFeature`), so that
no completeness is needed. The paper's `H₀` (mean-zero functions on `𝔽_p`) is nontrivial; the
norm formulas and `δ ≥ 0` assume `Nontrivial H₀` (for `H₀ = 0` every operator vanishes and the
formulas fail), the eigenvalue statement does not.

**The proof** follows the paper's: `A_⊥ = A - V M` with `M = V^* A` (`TwoFeature.Aperp`) has
`V^* A_⊥ = 0` and `A_⊥^* A_⊥ = δ I` (`norm_Aperp_sq`), and both operators act on `V h`, `A_⊥ h` by
the paper's `2 × 2` matrices (`symOp_V`, `symOp_Aperp`, `skewOp_V`, `skewOp_Aperp`). The paper
diagonalizes the skew matrix on the eigenspaces of `P` over `ℂ`; here the upper bounds are a
real Bessel inequality (`norm_gam_sq_le`) and a scalar inequality (`scalar_bound`), and the
attaining vectors are the real and imaginary parts of the paper's eigenvectors. The paper's
case split `δ > 0` / `δ = 0` is not needed.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.MiddleRecords

/-- **The data of `lem:two-feature-spectrum`.** An isometry `V : H₀ → 𝓗` and a map
`A : H₀ → 𝓗` with their adjoints `Vs = V^*`, `As = A^*` (the adjoint relations are the fields
`adjV`, `adjA`), and an operator `P` on `H₀`, with the Gram identities `V^* V = I`,
`V^* A = a I + b P`, `A^* A = c I`, `P^* = -P`, `P^* P = q I`. -/
structure TwoFeature (H₀ H : Type*) [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- The isometry `V`. -/
  V : H₀ →ₗ[ℝ] H
  /-- Its adjoint `V^*`. -/
  Vs : H →ₗ[ℝ] H₀
  /-- The feature map `A`. -/
  A : H₀ →ₗ[ℝ] H
  /-- Its adjoint `A^*`. -/
  As : H →ₗ[ℝ] H₀
  /-- The operator `P` (the Paley operator in the paper). -/
  P : H₀ →ₗ[ℝ] H₀
  /-- The coefficients of `V^* A = a I + b P`. -/
  a : ℝ
  /-- See `a`. -/
  b : ℝ
  /-- `A^* A = c I`. -/
  c : ℝ
  /-- `P^* P = q I`. -/
  q : ℝ
  adjV : ∀ x w, ⟪V x, w⟫_ℝ = ⟪x, Vs w⟫_ℝ
  adjA : ∀ x w, ⟪A x, w⟫_ℝ = ⟪x, As w⟫_ℝ
  isom : ∀ x, Vs (V x) = x
  gramVA : ∀ x, Vs (A x) = a • x + b • P x
  gramAA : ∀ x, As (A x) = c • x
  skewP : ∀ x y, ⟪P x, y⟫_ℝ = -⟪x, P y⟫_ℝ
  gramP : ∀ x y, ⟪P x, P y⟫_ℝ = q * ⟪x, y⟫_ℝ

namespace TwoFeature

variable {H₀ H : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] (D : TwoFeature H₀ H)

/-- The symmetric star `A V^* + V A^*`. -/
def symOp : H →ₗ[ℝ] H := D.A ∘ₗ D.Vs + D.V ∘ₗ D.As

/-- The skew star `A V^* - V A^*`. -/
def skewOp : H →ₗ[ℝ] H := D.A ∘ₗ D.Vs - D.V ∘ₗ D.As

/-- `δ = c - a² - b² q`. -/
def delta : ℝ := D.c - D.a ^ 2 - D.b ^ 2 * D.q

/-- `M = V^* A = a I + b P`. -/
def M : H₀ →ₗ[ℝ] H₀ := D.a • LinearMap.id + D.b • D.P

/-- `A_⊥ = A - V M`, the part of `A` orthogonal to the range of `V`. -/
def Aperp : H₀ →ₗ[ℝ] H := D.A - D.V ∘ₗ D.M

theorem M_apply (x : H₀) : D.M x = D.a • x + D.b • D.P x := rfl

theorem Aperp_apply (x : H₀) : D.Aperp x = D.A x - D.V (D.a • x + D.b • D.P x) := rfl

theorem symOp_apply (w : H) : D.symOp w = D.A (D.Vs w) + D.V (D.As w) := rfl

theorem skewOp_apply (w : H) : D.skewOp w = D.A (D.Vs w) - D.V (D.As w) := rfl

/-! ## Gram identities -/

theorem inner_V_V (x y : H₀) : ⟪D.V x, D.V y⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [D.adjV, D.isom]

theorem norm_V (x : H₀) : ‖D.V x‖ = ‖x‖ := by
  have h := D.inner_V_V x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem inner_self_P (x : H₀) : ⟪x, D.P x⟫_ℝ = 0 := by
  have h := D.skewP x x
  rw [real_inner_comm] at h
  linarith

theorem norm_P_sq (x : H₀) : ‖D.P x‖ ^ 2 = D.q * ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, D.gramP]

/-- `P² = -q I`, from `P^* = -P` and `P^* P = q I`. -/
theorem P_P (x : H₀) : D.P (D.P x) = (-D.q) • x := by
  apply ext_inner_right ℝ
  intro y
  rw [D.skewP, D.gramP, inner_smul_left]
  simp

/-- `A^* V = a I - b P`, the adjoint of `V^* A = a I + b P`. -/
theorem As_V (x : H₀) : D.As (D.V x) = D.a • x - D.b • D.P x := by
  apply ext_inner_left ℝ
  intro y
  rw [← D.adjA, real_inner_comm, D.adjV, D.gramVA, inner_add_right, inner_sub_right,
    inner_smul_right, inner_smul_right, inner_smul_right, inner_smul_right,
    real_inner_comm x y, real_inner_comm (D.P x) y, D.skewP]
  ring

theorem Vs_Aperp (x : H₀) : D.Vs (D.Aperp x) = 0 := by
  rw [Aperp_apply, map_sub, D.gramVA, D.isom, sub_self]

theorem inner_V_Aperp (x y : H₀) : ⟪D.V x, D.Aperp y⟫_ℝ = 0 := by
  rw [D.adjV, D.Vs_Aperp, inner_zero_right]

theorem As_Aperp (x : H₀) : D.As (D.Aperp x) = D.delta • x := by
  rw [Aperp_apply, map_sub, D.gramAA, D.As_V, map_add, map_smul, map_smul, D.P_P, delta]
  module

theorem inner_Aperp_left (x : H₀) (z : H) :
    ⟪D.Aperp x, z⟫_ℝ = ⟪D.A x, z⟫_ℝ - ⟪D.V (D.a • x + D.b • D.P x), z⟫_ℝ := by
  rw [Aperp_apply, inner_sub_left]

theorem norm_Aperp_sq (x : H₀) : ‖D.Aperp x‖ ^ 2 = D.delta * ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  have h1 : ⟪D.Aperp x, D.Aperp x⟫_ℝ = ⟪D.A x, D.Aperp x⟫_ℝ := by
    rw [D.inner_Aperp_left x (D.Aperp x), D.inner_V_Aperp, sub_zero]
  rw [h1, D.adjA, D.As_Aperp, inner_smul_right]

/-- **`δ ≥ 0`** (`lem:two-feature-spectrum`, first claim). -/
theorem delta_nonneg [Nontrivial H₀] : 0 ≤ D.delta := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H₀)
  have h := D.norm_Aperp_sq x
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  by_contra hneg
  push Not at hneg
  have : D.delta * ‖x‖ ^ 2 < 0 := mul_neg_of_neg_of_pos hneg hx2
  nlinarith [sq_nonneg ‖D.Aperp x‖]

theorem q_nonneg [Nontrivial H₀] : 0 ≤ D.q := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H₀)
  have h := D.norm_P_sq x
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  by_contra hneg
  push Not at hneg
  have : D.q * ‖x‖ ^ 2 < 0 := mul_neg_of_neg_of_pos hneg hx2
  nlinarith [sq_nonneg ‖D.P x‖]

/-- `‖A_⊥ x + V y‖² = δ ‖x‖² + ‖y‖²`. -/
theorem norm_Aperp_add_V_sq (x y : H₀) :
    ‖D.Aperp x + D.V y‖ ^ 2 = D.delta * ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
    real_inner_self_eq_norm_sq, D.norm_Aperp_sq, real_inner_comm, D.inner_V_Aperp,
    real_inner_self_eq_norm_sq, D.norm_V]
  ring

/-! ## The action on `V h` and `A_⊥ h` (the paper's `2 × 2` matrices) -/

theorem symOp_V (h : H₀) : D.symOp (D.V h) = (2 * D.a) • D.V h + D.Aperp h := by
  rw [symOp_apply, D.isom, D.As_V, Aperp_apply]
  simp only [map_sub, map_add, map_smul]
  module

theorem symOp_Aperp (h : H₀) : D.symOp (D.Aperp h) = D.delta • D.V h := by
  rw [symOp_apply, D.Vs_Aperp, map_zero, zero_add, D.As_Aperp, map_smul]

theorem skewOp_V (h : H₀) : D.skewOp (D.V h) = D.Aperp h + (2 * D.b) • D.V (D.P h) := by
  rw [skewOp_apply, D.isom, D.As_V, Aperp_apply]
  simp only [map_sub, map_add, map_smul]
  module

theorem skewOp_Aperp (h : H₀) : D.skewOp (D.Aperp h) = -(D.delta • D.V h) := by
  rw [skewOp_apply, D.Vs_Aperp, map_zero, zero_sub, D.As_Aperp, map_smul]

/-! ## The decomposition of a general vector -/

/-- `γ = A_⊥^* w = A^* w - M^* V^* w`. -/
def gam (w : H) : H₀ := D.As w - (D.a • D.Vs w - D.b • D.P (D.Vs w))

theorem inner_gam (w : H) (x : H₀) : ⟪D.gam w, x⟫_ℝ = ⟪w, D.Aperp x⟫_ℝ := by
  have e1 : ⟪D.As w, x⟫_ℝ = ⟪w, D.A x⟫_ℝ :=
    calc ⟪D.As w, x⟫_ℝ = ⟪x, D.As w⟫_ℝ := real_inner_comm _ _
      _ = ⟪D.A x, w⟫_ℝ := (D.adjA x w).symm
      _ = ⟪w, D.A x⟫_ℝ := real_inner_comm _ _
  have e2 : ⟪D.Vs w, x⟫_ℝ = ⟪w, D.V x⟫_ℝ :=
    calc ⟪D.Vs w, x⟫_ℝ = ⟪x, D.Vs w⟫_ℝ := real_inner_comm _ _
      _ = ⟪D.V x, w⟫_ℝ := (D.adjV x w).symm
      _ = ⟪w, D.V x⟫_ℝ := real_inner_comm _ _
  have e3 : ⟪D.P (D.Vs w), x⟫_ℝ = -⟪w, D.V (D.P x)⟫_ℝ :=
    calc ⟪D.P (D.Vs w), x⟫_ℝ = -⟪D.Vs w, D.P x⟫_ℝ := D.skewP _ _
      _ = -⟪D.P x, D.Vs w⟫_ℝ := by rw [real_inner_comm]
      _ = -⟪D.V (D.P x), w⟫_ℝ := by rw [D.adjV]
      _ = -⟪w, D.V (D.P x)⟫_ℝ := by rw [real_inner_comm]
  rw [gam, Aperp_apply, inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    e1, e2, e3, map_add, map_smul, map_smul, inner_sub_right, inner_add_right,
    real_inner_smul_right,
    real_inner_smul_right]
  ring

theorem symOp_eq (w : H) :
    D.symOp w = D.Aperp (D.Vs w) + D.V ((2 * D.a) • D.Vs w + D.gam w) := by
  rw [symOp_apply, gam, Aperp_apply]
  simp only [map_sub, map_add, map_smul]
  module

theorem skewOp_eq (w : H) :
    D.skewOp w = D.Aperp (D.Vs w) + D.V ((2 * D.b) • D.P (D.Vs w) - D.gam w) := by
  rw [skewOp_apply, gam, Aperp_apply]
  simp only [map_sub, map_add, map_smul]
  module

/-- `‖w‖² = ‖V^* w‖² + ‖w - V V^* w‖²`. -/
theorem norm_sub_V_sq (w : H) : ‖w - D.V (D.Vs w)‖ ^ 2 = ‖w‖ ^ 2 - ‖D.Vs w‖ ^ 2 := by
  rw [norm_sub_sq_real, D.norm_V, real_inner_comm, D.adjV, real_inner_self_eq_norm_sq]
  ring

theorem norm_Vs_sq_le (w : H) : ‖D.Vs w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  have h := D.norm_sub_V_sq w
  nlinarith [sq_nonneg ‖w - D.V (D.Vs w)‖]

/-- **The Bessel inequality** `‖A_⊥^* w‖² ≤ δ (‖w‖² - ‖V^* w‖²)`. -/
theorem norm_gam_sq_le (hδ : 0 ≤ D.delta) (w : H) :
    ‖D.gam w‖ ^ 2 ≤ D.delta * (‖w‖ ^ 2 - ‖D.Vs w‖ ^ 2) := by
  set w' := w - D.V (D.Vs w) with hw'
  have hinner : ⟪D.gam w, D.gam w⟫_ℝ = ⟪w', D.Aperp (D.gam w)⟫_ℝ := by
    rw [D.inner_gam, hw', inner_sub_left, D.inner_V_Aperp, sub_zero]
  have hcs := abs_real_inner_le_norm w' (D.Aperp (D.gam w))
  rw [← hinner, real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hcs
  have hA := D.norm_Aperp_sq (D.gam w)
  have hw2 := D.norm_sub_V_sq w
  rw [← hw'] at hw2
  rw [← hw2]
  -- `‖γ‖⁴ ≤ ‖w'‖² ‖A_⊥ γ‖² = δ ‖w'‖² ‖γ‖²`
  have h4 : (‖D.gam w‖ ^ 2) ^ 2 ≤ ‖w'‖ ^ 2 * (D.delta * ‖D.gam w‖ ^ 2) := by
    rw [← hA]
    have := mul_self_le_mul_self (sq_nonneg _) hcs
    nlinarith [this]
  by_cases hg : ‖D.gam w‖ = 0
  · rw [hg]
    have : 0 ≤ D.delta * ‖w'‖ ^ 2 := mul_nonneg hδ (sq_nonneg _)
    simpa using this
  · have hg2 : 0 < ‖D.gam w‖ ^ 2 := by positivity
    have h5 : ‖D.gam w‖ ^ 2 * ‖D.gam w‖ ^ 2 ≤ (D.delta * ‖w'‖ ^ 2) * ‖D.gam w‖ ^ 2 := by
      nlinarith [h4]
    exact le_of_mul_le_mul_right h5 hg2

/-! ## The scalar inequality -/

/-- **The scalar inequality behind both norms**: for `t, δ, s ≥ 0` with `s² = t² + δ`, and
`y ≥ 0`, `x² ≤ W²`, `y² ≤ δ (W² - x²)`, `δ x² + (2 t x + y)² ≤ (t + s)² W²`. This is
the largest eigenvalue `(t + s)²` of the form `(4t² + δ, 2t√δ; 2t√δ, δ)`. No sign of `x` is
needed. -/
theorem scalar_bound {t δ s x y W : ℝ} (ht : 0 ≤ t) (hδ : 0 ≤ δ) (hs : 0 ≤ s)
    (hs2 : s ^ 2 = t ^ 2 + δ) (hy : 0 ≤ y) (hxW : x ^ 2 ≤ W ^ 2)
    (hyW : y ^ 2 ≤ δ * (W ^ 2 - x ^ 2)) :
    δ * x ^ 2 + (2 * t * x + y) ^ 2 ≤ (t + s) ^ 2 * W ^ 2 := by
  rcases hδ.lt_or_eq with hδ' | hδ'
  · have hspos : 0 < s := by
      have : 0 < s ^ 2 := by rw [hs2]; positivity
      rcases hs.lt_or_eq with h | h
      · exact h
      · rw [← h] at this; simp at this
    have hst : 0 < s + t := by linarith
    have hB : 0 ≤ (s - t) * δ * x ^ 2 + (t + s) * y ^ 2 - 2 * δ * x * y := by
      have h1 : (s + t) * ((s - t) * δ * x ^ 2 + (t + s) * y ^ 2 - 2 * δ * x * y) =
          (δ * x - (s + t) * y) ^ 2 := by
        linear_combination (δ * x ^ 2) * hs2
      have h2 : 0 ≤ (s + t) * ((s - t) * δ * x ^ 2 + (t + s) * y ^ 2 - 2 * δ * x * y) := by
        rw [h1]; exact sq_nonneg _
      exact (mul_nonneg_iff_of_pos_left hst).mp h2
    have key : δ * ((t + s) ^ 2 * W ^ 2 - (δ * x ^ 2 + (2 * t * x + y) ^ 2)) =
        (t + s) ^ 2 * (δ * (W ^ 2 - x ^ 2) - y ^ 2) +
          2 * t * ((s - t) * δ * x ^ 2 + (t + s) * y ^ 2 - 2 * δ * x * y) := by
      linear_combination (δ * x ^ 2 + y ^ 2) * hs2
    have hpos : 0 ≤ δ * ((t + s) ^ 2 * W ^ 2 - (δ * x ^ 2 + (2 * t * x + y) ^ 2)) := by
      rw [key]
      have := sub_nonneg.mpr hyW
      positivity
    have := (mul_nonneg_iff_of_pos_left hδ').mp hpos
    linarith
  · subst hδ'
    have hy0 : y = 0 := by nlinarith
    have hst : s = t := by
      have : s ^ 2 = t ^ 2 := by linarith
      exact (sq_eq_sq₀ hs ht).mp this
    subst hy0 hst
    nlinarith [mul_nonneg ht ht]

/-! ## The two norms -/

/-- `c - b² q = a² + δ`. -/
theorem symConst_eq : D.c - D.b ^ 2 * D.q = D.a ^ 2 + D.delta := by
  rw [delta]; ring

/-- `c - a² = b² q + δ`. -/
theorem skewConst_eq : D.c - D.a ^ 2 = D.b ^ 2 * D.q + D.delta := by
  rw [delta]; ring

/-- **Upper bound `‖A V^* + V A^*‖ ≤ |a| + √(c - b² q)`** (`lem:two-feature-spectrum`). -/
theorem sym_norm_le [Nontrivial H₀] (w : H) :
    ‖D.symOp w‖ ≤ (|D.a| + Real.sqrt (D.c - D.b ^ 2 * D.q)) * ‖w‖ := by
  have hδ := D.delta_nonneg
  set s := Real.sqrt (D.c - D.b ^ 2 * D.q) with hs_def
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = |D.a| ^ 2 + D.delta := by
    rw [hs_def, Real.sq_sqrt (by rw [D.symConst_eq]; positivity), D.symConst_eq, sq_abs]
  set x := ‖D.Vs w‖
  set y := ‖D.gam w‖
  have hnorm : ‖D.symOp w‖ ^ 2 ≤ D.delta * x ^ 2 + (2 * |D.a| * x + y) ^ 2 := by
    rw [D.symOp_eq, D.norm_Aperp_add_V_sq]
    have htri : ‖(2 * D.a) • D.Vs w + D.gam w‖ ≤ 2 * |D.a| * x + y := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
    have h0 : 0 ≤ ‖(2 * D.a) • D.Vs w + D.gam w‖ := norm_nonneg _
    have := mul_self_le_mul_self h0 htri
    nlinarith
  have hb := scalar_bound (abs_nonneg D.a) hδ hs hs2 (norm_nonneg _)
    (D.norm_Vs_sq_le w) (D.norm_gam_sq_le hδ w) (W := ‖w‖)
  have hfin : ‖D.symOp w‖ ^ 2 ≤ ((|D.a| + s) * ‖w‖) ^ 2 := by
    rw [mul_pow]; linarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hfin

/-- **Upper bound `‖A V^* - V A^*‖ ≤ |b| r + √(c - a²)`**, `r = √q`
(`lem:two-feature-spectrum`). -/
theorem skew_norm_le [Nontrivial H₀] (w : H) :
    ‖D.skewOp w‖ ≤ (|D.b| * Real.sqrt D.q + Real.sqrt (D.c - D.a ^ 2)) * ‖w‖ := by
  have hδ := D.delta_nonneg
  have hq := D.q_nonneg
  set s := Real.sqrt (D.c - D.a ^ 2) with hs_def
  set t := |D.b| * Real.sqrt D.q with ht_def
  have ht : 0 ≤ t := by positivity
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = t ^ 2 + D.delta := by
    rw [hs_def, Real.sq_sqrt (by rw [D.skewConst_eq]; positivity), D.skewConst_eq, ht_def,
      mul_pow, sq_abs, Real.sq_sqrt hq]
  set x := ‖D.Vs w‖
  set y := ‖D.gam w‖
  have hPx : ‖D.P (D.Vs w)‖ = Real.sqrt D.q * x := by
    rw [← Real.sqrt_sq (norm_nonneg (D.P (D.Vs w))), D.norm_P_sq, Real.sqrt_mul hq,
      Real.sqrt_sq (norm_nonneg _)]
  have hnorm : ‖D.skewOp w‖ ^ 2 ≤ D.delta * x ^ 2 + (2 * t * x + y) ^ 2 := by
    rw [D.skewOp_eq, D.norm_Aperp_add_V_sq]
    have htri : ‖(2 * D.b) • D.P (D.Vs w) - D.gam w‖ ≤ 2 * t * x + y := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_two, hPx, ht_def]
      nlinarith [norm_nonneg (D.gam w)]
    have h0 : 0 ≤ ‖(2 * D.b) • D.P (D.Vs w) - D.gam w‖ := norm_nonneg _
    have := mul_self_le_mul_self h0 htri
    nlinarith
  have hb := scalar_bound ht hδ hs hs2 (norm_nonneg _)
    (D.norm_Vs_sq_le w) (D.norm_gam_sq_le hδ w) (W := ‖w‖)
  have hfin : ‖D.skewOp w‖ ^ 2 ≤ ((t + s) * ‖w‖) ^ 2 := by
    rw [mul_pow]; linarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hfin

/-- **The symmetric norm is attained**: some `w ≠ 0` has
`‖(A V^* + V A^*) w‖ = (|a| + √(c - b² q)) ‖w‖` (`lem:two-feature-spectrum`). It is an
eigenvector `λ V h + A_⊥ h` of eigenvalue `λ = a ± √(c - b² q)`, the sign that of `a`. -/
theorem sym_attained [Nontrivial H₀] :
    ∃ w : H, w ≠ 0 ∧ ‖D.symOp w‖ = (|D.a| + Real.sqrt (D.c - D.b ^ 2 * D.q)) * ‖w‖ := by
  obtain ⟨h, hh⟩ := exists_ne (0 : H₀)
  have hδ := D.delta_nonneg
  set s := Real.sqrt (D.c - D.b ^ 2 * D.q) with hs_def
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = D.a ^ 2 + D.delta := by
    rw [hs_def, Real.sq_sqrt (by rw [D.symConst_eq]; positivity), D.symConst_eq]
  set l : ℝ := if 0 ≤ D.a then D.a + s else D.a - s with hl
  have hlabs : |l| = |D.a| + s := by
    by_cases ha : 0 ≤ D.a
    · simp only [hl, ha, ↓reduceIte, abs_of_nonneg ha]
      exact abs_of_nonneg (by linarith)
    · push Not at ha
      simp only [hl, show ¬ (0 ≤ D.a) from not_le.mpr ha, ↓reduceIte, abs_of_neg ha]
      rw [abs_of_neg (by linarith)]
      ring
  have hlsq : l ^ 2 = 2 * D.a * l + D.delta := by
    by_cases ha : 0 ≤ D.a
    · simp only [hl, ha, ↓reduceIte]; linear_combination hs2
    · simp only [hl, ha, ↓reduceIte]; linear_combination hs2
  by_cases hl0 : l = 0
  · refine ⟨D.V h, ?_, ?_⟩
    · intro h0
      have := D.norm_V h
      rw [h0, norm_zero] at this
      exact hh (norm_eq_zero.mp this.symm)
    · have hN : |D.a| + s = 0 := by rw [← hlabs, hl0, abs_zero]
      have ha0 : D.a = 0 := by
        have := abs_nonneg D.a
        exact abs_eq_zero.mp (by linarith)
      have hd0 : D.delta = 0 := by
        have hs0 : s = 0 := by linarith [abs_nonneg D.a]
        rw [hs0, ha0] at hs2; linarith
      have hA0 : D.Aperp h = 0 := by
        have := D.norm_Aperp_sq h
        rw [hd0, zero_mul] at this
        exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
      rw [hN, zero_mul, D.symOp_V, hA0, ha0]
      simp
  · refine ⟨l • D.V h + D.Aperp h, ?_, ?_⟩
    · intro h0
      have hn := D.norm_Aperp_add_V_sq h (l • h)
      rw [add_comm, map_smul, h0, norm_zero, norm_smul, Real.norm_eq_abs] at hn
      have hh2 : 0 < ‖h‖ ^ 2 := by
        have : 0 < ‖h‖ := norm_pos_iff.mpr hh
        positivity
      have hl2 : 0 < |l| ^ 2 := by
        have : 0 < |l| := abs_pos.mpr hl0
        positivity
      nlinarith [mul_nonneg hδ hh2.le, mul_pos hl2 hh2]
    · have heig : D.symOp (l • D.V h + D.Aperp h) = l • (l • D.V h + D.Aperp h) := by
        have hll : l * l = l * (2 * D.a) + D.delta := by linear_combination hlsq
        rw [map_add, map_smul, D.symOp_V, D.symOp_Aperp, smul_add, smul_add, smul_smul,
          smul_smul, hll]
        module
      rw [heig, norm_smul, Real.norm_eq_abs, hlabs]

/-- **The skew norm is attained**: some `w ≠ 0` has
`‖(A V^* - V A^*) w‖ = (|b| r + √(c - a²)) ‖w‖` (`lem:two-feature-spectrum`). It is the real part
`κ V(P h) + r A_⊥ h` of the paper's eigenvector on the `P`-eigenspace of eigenvalue `i r`
(multiplied by `r`), with `κ = b r ± √(c - a²)`, the sign that of `b`. -/
theorem skew_attained [Nontrivial H₀] :
    ∃ w : H, w ≠ 0 ∧
      ‖D.skewOp w‖ = (|D.b| * Real.sqrt D.q + Real.sqrt (D.c - D.a ^ 2)) * ‖w‖ := by
  obtain ⟨h, hh⟩ := exists_ne (0 : H₀)
  have hδ := D.delta_nonneg
  have hq := D.q_nonneg
  set r := Real.sqrt D.q with hr_def
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = D.q := Real.sq_sqrt hq
  set s := Real.sqrt (D.c - D.a ^ 2) with hs_def
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = D.b ^ 2 * r ^ 2 + D.delta := by
    rw [hs_def, Real.sq_sqrt (by rw [D.skewConst_eq]; positivity), D.skewConst_eq, hr2]
  have hh2 : 0 < ‖h‖ ^ 2 := by
    have : 0 < ‖h‖ := norm_pos_iff.mpr hh
    positivity
  have hVh : D.V h ≠ 0 := by
    intro h0
    have := D.norm_V h
    rw [h0, norm_zero] at this
    exact hh (norm_eq_zero.mp this.symm)
  -- the case `q = 0`: `P = 0` and `w = V h` attains `√δ`
  rcases hq.lt_or_eq with hqpos | hq0
  · set k : ℝ := if 0 ≤ D.b then D.b * r + s else D.b * r - s with hk
    have hkabs : |k| = |D.b| * r + s := by
      by_cases hb : 0 ≤ D.b
      · simp only [hk, hb, ↓reduceIte, abs_of_nonneg hb]
        exact abs_of_nonneg (by positivity)
      · push Not at hb
        simp only [hk, show ¬ (0 ≤ D.b) from not_le.mpr hb, ↓reduceIte, abs_of_neg hb]
        rw [abs_of_neg (by nlinarith)]
        ring
    have hksq : k ^ 2 = 2 * D.b * r * k + D.delta := by
      by_cases hb : 0 ≤ D.b
      · simp only [hk, hb, ↓reduceIte]; linear_combination hs2
      · simp only [hk, hb, ↓reduceIte]; linear_combination hs2
    by_cases hN : |D.b| * r + s = 0
    · refine ⟨D.V h, hVh, ?_⟩
      rw [hN, zero_mul]
      have hk0 : k = 0 := abs_eq_zero.mp (by rw [hkabs, hN])
      have hd0 : D.delta = 0 := by rw [hk0] at hksq; linarith
      have hb0 : D.b * r = 0 := by
        have h1 : |D.b| * r = 0 := by linarith [hs, mul_nonneg (abs_nonneg D.b) hr]
        rcases mul_eq_zero.mp h1 with h | h
        · rw [abs_eq_zero.mp h, zero_mul]
        · rw [h, mul_zero]
      have hb0' : D.b = 0 := by
        rcases mul_eq_zero.mp hb0 with h | h
        · exact h
        · rw [h] at hr2; linarith
      have hA0 : D.Aperp h = 0 := by
        have := D.norm_Aperp_sq h
        rw [hd0, zero_mul] at this
        exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
      rw [D.skewOp_V, hA0, hb0']
      simp
    · have hk0 : k ≠ 0 := by
        intro h0; apply hN; rw [← hkabs, h0, abs_zero]
      set w := k • D.V (D.P h) + r • D.Aperp h with hw
      set w' := (k * r) • D.V h - D.Aperp (D.P h) with hw'
      have hTw : D.skewOp w = -(k • w') := by
        rw [hw, hw', map_add, map_smul, map_smul, D.skewOp_V, D.skewOp_Aperp, D.P_P, map_smul]
        have hcoef : (2 * D.b) * (-D.q) * k - r * D.delta = -(k * (k * r)) := by
          rw [← hr2]; linear_combination r * hksq
        rw [smul_add, smul_smul, smul_smul, smul_neg, smul_smul]
        have hc2 : k * (2 * D.b) * -D.q = r * D.delta - k * (k * r) := by
          linear_combination hcoef
        rw [hc2]
        module
      have hnw : ‖w‖ ^ 2 = D.q * (k ^ 2 + D.delta) * ‖h‖ ^ 2 := by
        rw [hw, add_comm, ← map_smul, ← map_smul, D.norm_Aperp_add_V_sq, norm_smul, norm_smul,
          Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs, D.norm_P_sq, hr2]
        ring
      have hnw' : ‖w'‖ ^ 2 = D.q * (k ^ 2 + D.delta) * ‖h‖ ^ 2 := by
        have : w' = D.Aperp (-D.P h) + D.V ((k * r) • h) := by
          rw [hw', map_neg, map_smul]; abel
        rw [this, D.norm_Aperp_add_V_sq, norm_neg, D.norm_P_sq, norm_smul, Real.norm_eq_abs,
          mul_pow, sq_abs, mul_pow, hr2]
        ring
      have hww' : ‖w'‖ = ‖w‖ := by
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hnw, hnw']
      refine ⟨w, ?_, ?_⟩
      · intro h0
        rw [h0, norm_zero] at hnw
        have hk2 : 0 < k ^ 2 := by positivity
        have : 0 < D.q * (k ^ 2 + D.delta) * ‖h‖ ^ 2 := by positivity
        linarith
      · rw [hTw, norm_neg, norm_smul, Real.norm_eq_abs, hww', hkabs]
  · -- `q = 0`
    have hP0 : D.P h = 0 := by
      have := D.norm_P_sq h
      rw [← hq0, zero_mul] at this
      exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
    refine ⟨D.V h, hVh, ?_⟩
    have hr0 : r = 0 := by rw [hr_def, ← hq0, Real.sqrt_zero]
    rw [D.skewOp_V, hP0, map_zero, smul_zero, add_zero, hr0, mul_zero, zero_add, D.norm_V]
    rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), D.norm_Aperp_sq, mul_pow,
      Real.sq_sqrt (by rw [D.skewConst_eq]; positivity), D.skewConst_eq, ← hq0]
    ring

/-! ## Eigenvalues and the spectrum -/

/-- **The eigenvalues of `A V^* + V A^*`** lie in `{0, a ± √(c - b² q)}`
(`lem:two-feature-spectrum`, the spectral inclusion; no nontriviality is needed). -/
theorem sym_eigen {μ : ℝ} {w : H} (hw : w ≠ 0) (hμw : D.symOp w = μ • w) :
    μ = 0 ∨ μ = D.a + Real.sqrt (D.c - D.b ^ 2 * D.q) ∨
      μ = D.a - Real.sqrt (D.c - D.b ^ 2 * D.q) := by
  by_cases hμ : μ = 0
  · exact Or.inl hμ
  right
  set α := D.Vs w
  set β := D.As w
  have E1 : D.a • α + D.b • D.P α + β = μ • α := by
    have := congrArg D.Vs hμw
    rw [symOp_apply, map_add, D.gramVA, D.isom, map_smul] at this
    exact this
  have E2 : D.c • α + (D.a • β - D.b • D.P β) = μ • β := by
    have := congrArg D.As hμw
    rw [symOp_apply, map_add, D.gramAA, D.As_V, map_smul] at this
    exact this
  have hβ : β = μ • α - D.a • α - D.b • D.P α := by
    rw [← E1]; abel
  have hkey : (D.c - D.b ^ 2 * D.q - (μ - D.a) ^ 2) • α = 0 := by
    have E2' := E2
    rw [hβ, map_sub, map_sub, map_smul, map_smul, map_smul, D.P_P] at E2'
    have : (D.c - D.b ^ 2 * D.q - (μ - D.a) ^ 2) • α =
        (D.c • α + (D.a • (μ • α - D.a • α - D.b • D.P α) -
          D.b • (μ • D.P α - D.a • D.P α - D.b • (-D.q) • α))) -
          μ • (μ • α - D.a • α - D.b • D.P α) := by
      module
    rw [this, E2', sub_self]
  have hα : α ≠ 0 := by
    intro h0
    have hβ0 : β = 0 := by rw [hβ, h0]; simp
    apply hw
    have h1 : μ • w = 0 := by
      rw [← hμw, symOp_apply]
      change D.A α + D.V β = 0
      rw [h0, hβ0, map_zero, map_zero, add_zero]
    exact (smul_eq_zero.mp h1).resolve_left hμ
  have hsq : D.c - D.b ^ 2 * D.q = (μ - D.a) ^ 2 := by
    have := (smul_eq_zero.mp hkey).resolve_right hα
    linarith
  rw [hsq, Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 (μ - D.a) with h | h
  · left; rw [abs_of_nonneg h]; ring
  · right; rw [abs_of_neg h]; ring

/-- **The spectrum** of `A V^* + V A^*` on a finite-dimensional `𝓗` lies in
`{0, a ± √(c - b² q)}` (`lem:two-feature-spectrum`). -/
theorem spectrum_symOp_subset [FiniteDimensional ℝ H] :
    spectrum ℝ D.symOp ⊆ {0, D.a + Real.sqrt (D.c - D.b ^ 2 * D.q),
      D.a - Real.sqrt (D.c - D.b ^ 2 * D.q)} := by
  intro μ hμ
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have h := D.sym_eigen hw.2 (Module.End.mem_eigenspace_iff.mp hw.1)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact h

/-! ## The operator norms in finite dimension -/

/-- **`‖A V^* + V A^*‖ = |a| + √(c - b² q)`** as an operator norm (`lem:two-feature-spectrum`). -/
theorem opNorm_symOp [FiniteDimensional ℝ H] [Nontrivial H₀] :
    ‖LinearMap.toContinuousLinearMap D.symOp‖ = |D.a| + Real.sqrt (D.c - D.b ^ 2 * D.q) := by
  have hN : 0 ≤ |D.a| + Real.sqrt (D.c - D.b ^ 2 * D.q) := by positivity
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ hN fun w => D.sym_norm_le w
  · obtain ⟨w, hw, heq⟩ := D.sym_attained
    have hle := (LinearMap.toContinuousLinearMap D.symOp).le_opNorm w
    rw [LinearMap.coe_toContinuousLinearMap', heq] at hle
    exact le_of_mul_le_mul_right hle (norm_pos_iff.mpr hw)

/-- **`‖A V^* - V A^*‖ = |b| r + √(c - a²)`** as an operator norm, `r = √q`
(`lem:two-feature-spectrum`). -/
theorem opNorm_skewOp [FiniteDimensional ℝ H] [Nontrivial H₀] :
    ‖LinearMap.toContinuousLinearMap D.skewOp‖ =
      |D.b| * Real.sqrt D.q + Real.sqrt (D.c - D.a ^ 2) := by
  have hN : 0 ≤ |D.b| * Real.sqrt D.q + Real.sqrt (D.c - D.a ^ 2) := by positivity
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ hN fun w => D.skew_norm_le w
  · obtain ⟨w, hw, heq⟩ := D.skew_attained
    have hle := (LinearMap.toContinuousLinearMap D.skewOp).le_opNorm w
    rw [LinearMap.coe_toContinuousLinearMap', heq] at hle
    exact le_of_mul_le_mul_right hle (norm_pos_iff.mpr hw)

end TwoFeature

end Sarkozy.MiddleRecords
