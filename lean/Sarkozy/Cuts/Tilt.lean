module

public import Sarkozy.Cuts.Actual
public import Sarkozy.ProbabilityProducts

/-!
# Cuts, IV: marginals of a positive quadratic tilt (`lem:tilt-marginals`)

`13_cuts_correlations.tex`, paragraph "Positive quadratic tilts". Here `(X, ν)` is a finite
probability space, and `K ≥ 0` is a symmetric kernel relative to `ν ⊗ ν` with mass one. Its
marginal density is `m = K1` (`rowFun`). The scores `η₀, η₁, η₂` are permuted among themselves by
the swap. `η̄` is their mean (`etaBar`), and `V` is either the mean of their squares or `η̄²`.

* `tilt_marginals`: the main part. The tilted kernel `T = (K + 2u K_η̄ + u² K_V)/Z` is
  nonnegative, symmetric and of mass one. Also `Z ≥ z`,
  `‖T1 - 1‖ ≤ (sδ₀ + 2uℓ + u²e)/z`, and `T1(x) ≤ R (1 + ub)²/(1 - uc)² T1(x')`.
* `tensor_kmass`, `rowFun_tensor`, `tensor_range`, `tensor_chiSq`: the product clause.

Operator bounds are stated as bounds on forms (`kernelForm`). The range ratio
`sup m / inf m ≤ R` is stated as `m(x) ≤ R m(x')` for all `x, x'`.

Of the paper's standing constants `c_V, e, ℓ, h, c, b ≥ 0`, only `c_V ≥ 0` and `e ≥ 0` are used.
Full support of `ν` and `m > 0` are not needed either: the range clause uses `m > 0` only through
`m(x) ≤ R m(x')`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering

section L2

variable {X : Type*} [Fintype X]

theorem nrm_nonneg (ν : FiniteLaw X) (f : X → ℝ) : 0 ≤ nrm ν f := Real.sqrt_nonneg _

theorem nrm_sq_eq (ν : FiniteLaw X) (f : X → ℝ) : nrm ν f ^ 2 = ip ν f f := by
  unfold nrm
  exact Real.sq_sqrt (ν.expect_nonneg (fun x => mul_self_nonneg _))

theorem nrm_one (ν : FiniteLaw X) : nrm ν (fun _ => 1) = 1 := by
  unfold nrm ip
  simp only [mul_one]
  rw [expect_one, Real.sqrt_one]

theorem nrm_smul (ν : FiniteLaw X) (a : ℝ) (f : X → ℝ) :
    nrm ν (fun x => a * f x) = |a| * nrm ν f := by
  unfold nrm ip
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg a)]
  congr 1
  rw [← FiniteLaw.expect_const_mul]
  exact ν.expect_congr (fun x => by ring)

/-- The triangle inequality in `L²(ν)`. -/
theorem nrm_add_le (ν : FiniteLaw X) (f g : X → ℝ) :
    nrm ν (fun x => f x + g x) ≤ nrm ν f + nrm ν g := by
  have h0 := nrm_nonneg ν f
  have h1 := nrm_nonneg ν g
  have hsq : nrm ν (fun x => f x + g x) ^ 2 ≤ (nrm ν f + nrm ν g) ^ 2 := by
    rw [nrm_sq_eq]
    have e : ip ν (fun x => f x + g x) (fun x => f x + g x) =
        ip ν f f + 2 * ip ν f g + ip ν g g := by
      unfold ip FiniteLaw.expect
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [e]
    have hc := abs_ip_le ν f g
    have := le_abs_self (ip ν f g)
    nlinarith [nrm_sq_eq ν f, nrm_sq_eq ν g]
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

/-- The row function `K1(x) = E_{y ∼ ν} K(x, y)`. -/
noncomputable def rowFun (ν : FiniteLaw X) (K : X → X → ℝ) : X → ℝ :=
  fun x => ν.expect (fun y => K x y)

/-- The `ν ⊗ ν`-mass `⟨1, K1⟩`. -/
noncomputable def kmass (ν : FiniteLaw X) (K : X → X → ℝ) : ℝ := ν.expect (rowFun ν K)

theorem kmass_eq_kernelForm (ν : FiniteLaw X) (K : X → X → ℝ) :
    kmass ν K = kernelForm ν ν K (fun _ => 1) (fun _ => 1) := by
  rw [kernelForm_one_right, ip_one_left]
  rfl

/-- An operator bound `‖G‖ ≤ e` bounds the row function: `‖G1‖ ≤ e`. -/
theorem nrm_rowFun_le (ν : FiniteLaw X) (G : X → X → ℝ) {e : ℝ} (he0 : 0 ≤ e)
    (he : ∀ f g, |kernelForm ν ν G f g| ≤ e * nrm ν f * nrm ν g) : nrm ν (rowFun ν G) ≤ e := by
  have h1 := he (rowFun ν G) (fun _ => 1)
  rw [kernelForm_one_right, nrm_one, mul_one] at h1
  change |ip ν (rowFun ν G) (rowFun ν G)| ≤ _ at h1
  rw [← nrm_sq_eq, abs_of_nonneg (sq_nonneg _)] at h1
  have h0 := nrm_nonneg ν (rowFun ν G)
  nlinarith

end L2

section Tilt

variable {X : Type*} [Fintype X]

/-- The mean of the three scores, `η̄ = (η₀ + η₁ + η₂)/3`. -/
noncomputable def etaBar (η : Fin 3 → X → X → ℝ) : X → X → ℝ :=
  fun x y => (1 / 3) * ∑ j, η j x y

/-- The tilt numerator `K + 2u K_η̄ + u² K_V`. -/
noncomputable def tiltNum (K : X → X → ℝ) (η : Fin 3 → X → X → ℝ) (V : X → X → ℝ) (u : ℝ) :
    X → X → ℝ :=
  fun x y => K x y + 2 * u * (K x y * etaBar η x y) + u ^ 2 * (K x y * V x y)

/-- The tilted kernel `T = (K + 2u K_η̄ + u² K_V)/Z`. -/
noncomputable def tiltKernel (ν : FiniteLaw X) (K : X → X → ℝ) (η : Fin 3 → X → X → ℝ)
    (V : X → X → ℝ) (u : ℝ) : X → X → ℝ :=
  fun x y => tiltNum K η V u x y / kmass ν (tiltNum K η V u)

omit [Fintype X] in
theorem etaBar_symm (η : Fin 3 → X → X → ℝ) (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ j x y, η j y x = η (σ j) x y) (x y : X) : etaBar η y x = etaBar η x y := by
  unfold etaBar
  congr 1
  rw [Finset.sum_congr rfl (fun j _ => hσ j x y)]
  exact Equiv.sum_comp σ (fun j => η j x y)

omit [Fintype X] in
theorem sqMean_symm (η : Fin 3 → X → X → ℝ) (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ j x y, η j y x = η (σ j) x y) (x y : X) :
    (1 / 3) * ∑ j, η j y x ^ 2 = (1 / 3) * ∑ j, η j x y ^ 2 := by
  congr 1
  rw [Finset.sum_congr rfl (fun j _ => by rw [hσ j x y])]
  exact Equiv.sum_comp σ (fun j => η j x y ^ 2)

/-- The admissible `V`: the mean of the squares or the square of the mean. -/
def IsTiltV (η : Fin 3 → X → X → ℝ) (V : X → X → ℝ) : Prop :=
  V = (fun x y => (1 / 3) * ∑ j, η j x y ^ 2) ∨ V = (fun x y => etaBar η x y ^ 2)

omit [Fintype X] in
theorem IsTiltV.symm {η : Fin 3 → X → X → ℝ} {V : X → X → ℝ} (hV : IsTiltV η V)
    (σ : Equiv.Perm (Fin 3)) (hσ : ∀ j x y, η j y x = η (σ j) x y) (x y : X) :
    V y x = V x y := by
  rcases hV with rfl | rfl
  · exact sqMean_symm η σ hσ x y
  · simp only [etaBar_symm η σ hσ x y]

omit [Fintype X] in
/-- In both cases `V ≥ η̄²` (Cauchy–Schwarz for the mean of the squares). -/
theorem IsTiltV.sq_le {η : Fin 3 → X → X → ℝ} {V : X → X → ℝ} (hV : IsTiltV η V) (x y : X) :
    etaBar η x y ^ 2 ≤ V x y := by
  rcases hV with rfl | rfl
  · simp only [etaBar, Fin.sum_univ_three]
    nlinarith [sq_nonneg (η 0 x y - η 1 x y), sq_nonneg (η 1 x y - η 2 x y),
      sq_nonneg (η 0 x y - η 2 x y)]
  · exact le_refl _

omit [Fintype X] in
/-- On `{K > 0}`, `w = 1 + 2uη̄ + u²V ≤ (1 + ub)²` in both cases. -/
theorem IsTiltV.weight_le {η : Fin 3 → X → X → ℝ} {V : X → X → ℝ} (hV : IsTiltV η V)
    {u b : ℝ} (hu : 0 ≤ u) {x y : X} (hb : ∀ j, |η j x y| ≤ b) :
    1 + 2 * u * etaBar η x y + u ^ 2 * V x y ≤ (1 + u * b) ^ 2 := by
  have hq : ∀ a : ℝ, |a| ≤ b → (1 + u * a) ^ 2 ≤ (1 + u * b) ^ 2 := by
    intro a ha
    obtain ⟨l, r⟩ := abs_le.mp ha
    have h1 := mul_le_mul_of_nonneg_left r hu
    have h2 := mul_le_mul_of_nonneg_left l hu
    apply sq_le_sq' <;> nlinarith
  have q0 := hq _ (hb 0)
  have q1 := hq _ (hb 1)
  have q2 := hq _ (hb 2)
  rcases hV with rfl | rfl
  · simp only [etaBar, Fin.sum_univ_three]
    have e : 1 + 2 * u * (1 / 3 * (η 0 x y + η 1 x y + η 2 x y)) +
        u ^ 2 * (1 / 3 * (η 0 x y ^ 2 + η 1 x y ^ 2 + η 2 x y ^ 2)) =
        (1 / 3) * ((1 + u * η 0 x y) ^ 2 + (1 + u * η 1 x y) ^ 2 + (1 + u * η 2 x y) ^ 2) := by
      ring
    rw [e]
    linarith
  · have hm : |etaBar η x y| ≤ b := by
      simp only [etaBar, Fin.sum_univ_three]
      obtain ⟨l0, r0⟩ := abs_le.mp (hb 0)
      obtain ⟨l1, r1⟩ := abs_le.mp (hb 1)
      obtain ⟨l2, r2⟩ := abs_le.mp (hb 2)
      rw [abs_le]
      constructor <;> linarith
    have e : 1 + 2 * u * etaBar η x y + u ^ 2 * etaBar η x y ^ 2 = (1 + u * etaBar η x y) ^ 2 := by
      ring
    rw [e]
    exact hq _ hm

theorem rowFun_tiltNum (ν : FiniteLaw X) (K : X → X → ℝ) (η : Fin 3 → X → X → ℝ)
    (V : X → X → ℝ) (u cV : ℝ) (x : X) :
    rowFun ν (tiltNum K η V u) x = (1 + cV * u ^ 2) * rowFun ν K x +
      2 * u * rowFun ν (fun x y => K x y * etaBar η x y) x +
      u ^ 2 * rowFun ν (fun x y => K x y * V x y - cV * K x y) x := by
  simp only [rowFun, tiltNum, FiniteLaw.expect]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun y _ => by ring)

omit [Fintype X] in
theorem tiltNum_eq (K : X → X → ℝ) (η : Fin 3 → X → X → ℝ) (V : X → X → ℝ) (u : ℝ) (x y : X) :
    tiltNum K η V u x y = K x y * (1 + 2 * u * etaBar η x y + u ^ 2 * V x y) := by
  unfold tiltNum
  ring

/-- The pointwise range of the tilted row function: `(1 - uc)² m ≤ N1 ≤ (1 + ub)² m`. -/
theorem tilt_row_bounds (ν : FiniteLaw X) (K : X → X → ℝ) (hK0 : ∀ x y, 0 ≤ K x y)
    (η : Fin 3 → X → X → ℝ) (V : X → X → ℝ) (hV : IsTiltV η V) {c b u : ℝ} (hu : 0 ≤ u)
    (huc : u * c < 1)
    (hc : ∀ x, |rowFun ν (fun x y => K x y * etaBar η x y) x| ≤ c * rowFun ν K x)
    (hb : ∀ j x y, 0 < K x y → |η j x y| ≤ b) (x : X) :
    (1 - u * c) ^ 2 * rowFun ν K x ≤ rowFun ν (tiltNum K η V u) x ∧
      rowFun ν (tiltNum K η V u) x ≤ (1 + u * b) ^ 2 * rowFun ν K x := by
  constructor
  · set a := 1 - u * c with ha_def
    have ha : 0 < a := by rw [ha_def]; linarith
    have hA : ν.expect (fun y => K x y * (1 + u * etaBar η x y) ^ 2) ≤
        rowFun ν (tiltNum K η V u) x := by
      unfold rowFun
      refine ν.expect_mono (fun y => ?_)
      rw [tiltNum_eq]
      have h1 := hV.sq_le x y
      have hK := hK0 x y
      have e : K x y * (1 + 2 * u * etaBar η x y + u ^ 2 * V x y) -
          K x y * (1 + u * etaBar η x y) ^ 2 =
          K x y * (u ^ 2 * (V x y - etaBar η x y ^ 2)) := by ring
      have : 0 ≤ K x y * (u ^ 2 * (V x y - etaBar η x y ^ 2)) :=
        mul_nonneg hK (mul_nonneg (sq_nonneg u) (by linarith))
      linarith
    have hB : a * rowFun ν K x ≤ ν.expect (fun y => K x y * (1 + u * etaBar η x y)) := by
      have e1 : ν.expect (fun y => K x y * (1 + u * etaBar η x y)) =
          rowFun ν K x + u * rowFun ν (fun x y => K x y * etaBar η x y) x := by
        simp only [rowFun, FiniteLaw.expect]
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun y _ => by ring)
      rw [e1, ha_def]
      have h1 := hc x
      have h2 := neg_abs_le (rowFun ν (fun x y => K x y * etaBar η x y) x)
      have h3 : -(u * (c * rowFun ν K x)) ≤ u * rowFun ν (fun x y => K x y * etaBar η x y) x := by
        have := mul_le_mul_of_nonneg_left (show -(c * rowFun ν K x) ≤
          rowFun ν (fun x y => K x y * etaBar η x y) x by linarith) hu
        linarith
      nlinarith
    have hC : 0 ≤ ν.expect (fun y => K x y * (1 + u * etaBar η x y) ^ 2) -
        2 * a * ν.expect (fun y => K x y * (1 + u * etaBar η x y)) + a ^ 2 * rowFun ν K x := by
      have e : ν.expect (fun y => K x y * (1 + u * etaBar η x y) ^ 2) -
          2 * a * ν.expect (fun y => K x y * (1 + u * etaBar η x y)) + a ^ 2 * rowFun ν K x =
          ν.expect (fun y => K x y * (1 + u * etaBar η x y - a) ^ 2) := by
        simp only [rowFun, FiniteLaw.expect]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun y _ => by ring)
      rw [e]
      exact ν.expect_nonneg (fun y => mul_nonneg (hK0 x y) (sq_nonneg _))
    nlinarith [mul_le_mul_of_nonneg_left hB ha.le]
  · unfold rowFun
    rw [← FiniteLaw.expect_const_mul]
    refine ν.expect_mono (fun y => ?_)
    rw [tiltNum_eq]
    rcases (hK0 x y).lt_or_eq with hK | hK
    · have := hV.weight_le hu (fun j => hb j x y hK)
      nlinarith
    · rw [← hK]
      simp

/-- **`lem:tilt-marginals`, main part.** Let `K ≥ 0` be symmetric with mass one, marginal
density `m = K1`, `m(x) ≤ R m(x')` and `‖m - 1‖ ≤ δ₀`. Let `η₀, η₁, η₂` be permuted by the swap,
and `V` the mean of their squares or `η̄²`. Suppose `‖K_V - c_V K‖ ≤ e`, `‖P₀ K_η̄ 1‖ ≤ ℓ`,
`|⟨1, K_η̄ 1⟩| ≤ h`, `|K_η̄ 1| ≤ c K1`, and `|η_j| ≤ b` on `{K > 0}`. For `u ≥ 0` put
`s = 1 + c_V u²`, and assume `uc < 1` and `z = s - 2uh - u²e > 0`. Then
`T = (K + 2u K_η̄ + u² K_V)/Z` is nonnegative, symmetric and of mass one, and
`Z ≥ z`, `‖T1 - 1‖ ≤ (sδ₀ + 2uℓ + u²e)/z`, `T1(x) ≤ R (1 + ub)²/(1 - uc)² T1(x')`. -/
theorem tilt_marginals (ν : FiniteLaw X) (K : X → X → ℝ) (hK0 : ∀ x y, 0 ≤ K x y)
    (hKs : ∀ x y, K y x = K x y) (hKm : kmass ν K = 1) {R δ₀ : ℝ}
    (hR : ∀ x x', rowFun ν K x ≤ R * rowFun ν K x')
    (hδ₀ : nrm ν (fun x => rowFun ν K x - 1) ≤ δ₀)
    (η : Fin 3 → X → X → ℝ) (σ : Equiv.Perm (Fin 3)) (hσ : ∀ j x y, η j y x = η (σ j) x y)
    (V : X → X → ℝ) (hV : IsTiltV η V) {cV e l h c b u : ℝ} (hcV : 0 ≤ cV) (he0 : 0 ≤ e)
    (he : ∀ f g, |kernelForm ν ν (fun x y => K x y * V x y - cV * K x y) f g| ≤
      e * nrm ν f * nrm ν g)
    (hl : nrm ν (center ν (rowFun ν (fun x y => K x y * etaBar η x y))) ≤ l)
    (hh : |kmass ν (fun x y => K x y * etaBar η x y)| ≤ h)
    (hc : ∀ x, |rowFun ν (fun x y => K x y * etaBar η x y) x| ≤ c * rowFun ν K x)
    (hb : ∀ j x y, 0 < K x y → |η j x y| ≤ b)
    (hu : 0 ≤ u) (huc : u * c < 1) (hz : 0 < 1 + cV * u ^ 2 - 2 * u * h - u ^ 2 * e) :
    (∀ x y, 0 ≤ tiltKernel ν K η V u x y) ∧
    (∀ x y, tiltKernel ν K η V u y x = tiltKernel ν K η V u x y) ∧
    kmass ν (tiltKernel ν K η V u) = 1 ∧
    1 + cV * u ^ 2 - 2 * u * h - u ^ 2 * e ≤ kmass ν (tiltNum K η V u) ∧
    nrm ν (fun x => rowFun ν (tiltKernel ν K η V u) x - 1) ≤
      ((1 + cV * u ^ 2) * δ₀ + 2 * u * l + u ^ 2 * e) / (1 + cV * u ^ 2 - 2 * u * h - u ^ 2 * e) ∧
    ∀ x x', rowFun ν (tiltKernel ν K η V u) x ≤
      R * ((1 + u * b) ^ 2 / (1 - u * c) ^ 2) * rowFun ν (tiltKernel ν K η V u) x' := by
  set N := tiltNum K η V u with hN
  set Z := kmass ν N with hZ
  set z := 1 + cV * u ^ 2 - 2 * u * h - u ^ 2 * e with hz_def
  set G : X → X → ℝ := fun x y => K x y * V x y - cV * K x y with hG
  set r := rowFun ν (fun x y => K x y * etaBar η x y) with hr
  -- the mass
  have hZeq : Z = (1 + cV * u ^ 2) * kmass ν K + 2 * u * kmass ν (fun x y => K x y * etaBar η x y) +
      u ^ 2 * kmass ν G := by
    rw [hZ]
    unfold kmass
    have : rowFun ν N = fun x => (1 + cV * u ^ 2) * rowFun ν K x + 2 * u * r x +
        u ^ 2 * rowFun ν G x := funext (fun x => rowFun_tiltNum ν K η V u cV x)
    rw [this]
    simp only [FiniteLaw.expect]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  have hGm : |kmass ν G| ≤ e := by
    have := he (fun _ => 1) (fun _ => 1)
    rw [nrm_one, mul_one, mul_one] at this
    rw [kmass_eq_kernelForm]
    exact this
  have hZz : z ≤ Z := by
    rw [hZeq, hKm, hz_def]
    have h1 := neg_abs_le (kmass ν (fun x y => K x y * etaBar η x y))
    have h2 := neg_abs_le (kmass ν G)
    have h3 : -(2 * u * h) ≤ 2 * u * kmass ν (fun x y => K x y * etaBar η x y) := by
      have := mul_le_mul_of_nonneg_left (show -h ≤ kmass ν (fun x y => K x y * etaBar η x y) by
        linarith) (by linarith : (0 : ℝ) ≤ 2 * u)
      linarith
    have h4 : -(u ^ 2 * e) ≤ u ^ 2 * kmass ν G := by
      have := mul_le_mul_of_nonneg_left (show -e ≤ kmass ν G by linarith) (sq_nonneg u)
      linarith
    linarith
  have hZ0 : 0 < Z := lt_of_lt_of_le hz hZz
  -- the kernel
  have hT : ∀ x y, tiltKernel ν K η V u x y = N x y / Z := fun x y => rfl
  have hN0 : ∀ x y, 0 ≤ N x y := by
    intro x y
    rw [hN, tiltNum_eq]
    have h1 := hV.sq_le x y
    have : 0 ≤ 1 + 2 * u * etaBar η x y + u ^ 2 * V x y := by
      nlinarith [sq_nonneg (1 + u * etaBar η x y), sq_nonneg u]
    exact mul_nonneg (hK0 x y) this
  have hrowT : ∀ x, rowFun ν (tiltKernel ν K η V u) x = rowFun ν N x / Z := by
    intro x
    unfold rowFun
    simp only [hT]
    exact Sarkozy.Peyre.expect_div_const ν (fun y => N x y) Z
  have hmassT : kmass ν (tiltKernel ν K η V u) = 1 := by
    unfold kmass
    rw [show rowFun ν (tiltKernel ν K η V u) = fun x => rowFun ν N x / Z from funext hrowT,
      Sarkozy.Peyre.expect_div_const]
    exact div_self hZ0.ne'
  refine ⟨fun x y => div_nonneg (hN0 x y) hZ0.le, fun x y => ?_, hmassT, hZz, ?_, ?_⟩
  · rw [hT, hT, hN, tiltNum_eq, tiltNum_eq, hKs, etaBar_symm η σ hσ, hV.symm σ hσ]
  · -- the centred marginal
    have hc1 : ∀ x, rowFun ν (tiltKernel ν K η V u) x - 1 =
        Z⁻¹ * ((1 + cV * u ^ 2) * center ν (rowFun ν K) x + 2 * u * center ν r x +
          u ^ 2 * center ν (rowFun ν G) x) := by
      intro x
      have hN1 : rowFun ν N x = (1 + cV * u ^ 2) * rowFun ν K x + 2 * u * r x +
          u ^ 2 * rowFun ν G x := rowFun_tiltNum ν K η V u cV x
      rw [hrowT, hN1]
      simp only [center]
      have hmK : ν.expect (rowFun ν K) = 1 := hKm
      have hmr : ν.expect r = kmass ν (fun x y => K x y * etaBar η x y) := rfl
      have hmG : ν.expect (rowFun ν G) = kmass ν G := rfl
      rw [hmK, hmr, hmG]
      have hZ' : (1 + cV * u ^ 2) * 1 + 2 * u * kmass ν (fun x y => K x y * etaBar η x y) +
          u ^ 2 * kmass ν G = Z := by rw [hZeq, hKm]
      have key : Z⁻¹ * ((1 + cV * u ^ 2) * (rowFun ν K x - 1) +
          2 * u * (r x - kmass ν (fun x y => K x y * etaBar η x y)) +
          u ^ 2 * (rowFun ν G x - kmass ν G)) = Z⁻¹ * (((1 + cV * u ^ 2) * rowFun ν K x +
          2 * u * r x + u ^ 2 * rowFun ν G x) - Z) := by
        rw [← hZ']
        ring
      rw [key, div_sub_one hZ0.ne', div_eq_inv_mul]
    rw [show (fun x => rowFun ν (tiltKernel ν K η V u) x - 1) = fun x => Z⁻¹ *
        ((1 + cV * u ^ 2) * center ν (rowFun ν K) x + 2 * u * center ν r x +
          u ^ 2 * center ν (rowFun ν G) x) from funext hc1, nrm_smul,
      abs_of_pos (inv_pos.mpr hZ0)]
    have hm1 : nrm ν (center ν (rowFun ν K)) ≤ δ₀ := by
      have : center ν (rowFun ν K) = fun x => rowFun ν K x - 1 := by
        funext x
        simp only [center]
        rw [show ν.expect (rowFun ν K) = 1 from hKm]
      rw [this]
      exact hδ₀
    have hq1 : nrm ν (center ν (rowFun ν G)) ≤ e :=
      (nrm_center_le ν _).trans (nrm_rowFun_le ν G he0 he)
    have hs0 : 0 ≤ 1 + cV * u ^ 2 := by positivity
    have hsum : nrm ν (fun x => (1 + cV * u ^ 2) * center ν (rowFun ν K) x + 2 * u * center ν r x +
        u ^ 2 * center ν (rowFun ν G) x) ≤ (1 + cV * u ^ 2) * δ₀ + 2 * u * l + u ^ 2 * e := by
      refine (nrm_add_le ν _ _).trans ?_
      refine (add_le_add (nrm_add_le ν _ _) le_rfl).trans ?_
      rw [nrm_smul, nrm_smul, nrm_smul, abs_of_nonneg hs0, abs_of_nonneg (by linarith),
        abs_of_nonneg (sq_nonneg u)]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hm1 hs0)
        (mul_le_mul_of_nonneg_left hl (by linarith))) (mul_le_mul_of_nonneg_left hq1 (sq_nonneg u))
    have hB0 : 0 ≤ (1 + cV * u ^ 2) * δ₀ + 2 * u * l + u ^ 2 * e :=
      le_trans (nrm_nonneg ν _) hsum
    rw [inv_mul_eq_div]
    calc _ ≤ ((1 + cV * u ^ 2) * δ₀ + 2 * u * l + u ^ 2 * e) / Z :=
          div_le_div_of_nonneg_right hsum hZ0.le
      _ ≤ ((1 + cV * u ^ 2) * δ₀ + 2 * u * l + u ^ 2 * e) / z :=
          div_le_div_of_nonneg_left hB0 hz hZz
  · -- the range
    intro x x'
    rw [hrowT, hrowT]
    obtain ⟨_, hup⟩ := tilt_row_bounds ν K hK0 η V hV hu huc hc hb x
    obtain ⟨hlow, _⟩ := tilt_row_bounds ν K hK0 η V hV hu huc hc hb x'
    have ha : 0 < (1 - u * c) ^ 2 := by
      have : 0 < 1 - u * c := by linarith
      positivity
    have hR0 : 0 ≤ R := by
      have hX : 0 ≤ rowFun ν K x := ν.expect_nonneg (fun y => hK0 x y)
      by_contra hneg
      push Not at hneg
      have := hR x' x'
      have hx' : 0 ≤ rowFun ν K x' := ν.expect_nonneg (fun y => hK0 x' y)
      -- `m(x') ≤ R m(x')` with `R < 0` forces `m(x') = 0`, then `m ≡ 0` contradicts mass one
      have hm0 : ∀ w, rowFun ν K w = 0 := by
        intro w
        have h1 := hR w w
        have h2 : 0 ≤ rowFun ν K w := ν.expect_nonneg (fun y => hK0 w y)
        nlinarith
      have : kmass ν K = 0 := by
        unfold kmass
        rw [show rowFun ν K = fun _ => 0 from funext hm0, FiniteLaw.expect_const]
      rw [hKm] at this
      exact one_ne_zero this
    have hBb : 0 ≤ (1 + u * b) ^ 2 := sq_nonneg _
    have hac : 1 - u * c ≠ 0 := (by linarith : (0 : ℝ) < 1 - u * c).ne'
    have hstep : rowFun ν N x ≤ (1 + u * b) ^ 2 * (R * rowFun ν K x') :=
      hup.trans (mul_le_mul_of_nonneg_left (hR x x') hBb)
    have key : rowFun ν N x ≤ R * ((1 + u * b) ^ 2 / (1 - u * c) ^ 2) * rowFun ν N x' :=
      calc rowFun ν N x ≤ (1 + u * b) ^ 2 * (R * rowFun ν K x') := hstep
        _ = R * ((1 + u * b) ^ 2 / (1 - u * c) ^ 2) * ((1 - u * c) ^ 2 * rowFun ν K x') := by
            field_simp
        _ ≤ R * ((1 + u * b) ^ 2 / (1 - u * c) ^ 2) * rowFun ν N x' :=
            mul_le_mul_of_nonneg_left hlow (mul_nonneg hR0 (div_nonneg hBb ha.le))
    rw [mul_div_assoc' (R * ((1 + u * b) ^ 2 / (1 - u * c) ^ 2)) (rowFun ν N x') Z]
    exact div_le_div_of_nonneg_right key hZ0.le

end Tilt

section Products

variable {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*} [∀ i, Fintype (Ω i)]

/-- The tensor product `⊗_i T_i` of kernels. -/
noncomputable def tensorKernel (T : ∀ i, Ω i → Ω i → ℝ) : (∀ i, Ω i) → (∀ i, Ω i) → ℝ :=
  fun x y => ∏ i, T i (x i) (y i)

/-- The marginal density of `⊗_i T_i` is `⊗_i T_i 1`. -/
theorem rowFun_tensor (ν : ∀ i, FiniteLaw (Ω i)) (T : ∀ i, Ω i → Ω i → ℝ) (x : ∀ i, Ω i) :
    rowFun (FiniteLaw.pi ν) (tensorKernel T) x = ∏ i, rowFun (ν i) (T i) (x i) :=
  FiniteLaw.expect_pi_product ν (fun i y => T i (x i) y)

/-- `⊗_i T_i` has mass `∏_i` (mass of `T_i`). -/
theorem tensor_kmass (ν : ∀ i, FiniteLaw (Ω i)) (T : ∀ i, Ω i → Ω i → ℝ) :
    kmass (FiniteLaw.pi ν) (tensorKernel T) = ∏ i, kmass (ν i) (T i) := by
  unfold kmass
  rw [show rowFun (FiniteLaw.pi ν) (tensorKernel T) = fun x => ∏ i, rowFun (ν i) (T i) (x i) from
    funext (rowFun_tensor ν T)]
  exact FiniteLaw.expect_pi_product ν (fun i => rowFun (ν i) (T i))

omit [DecidableEq I] [∀ i, Fintype (Ω i)] in
/-- **`lem:tilt-marginals`, product clause, range.** The range ratio of a product of nonnegative
functions is at most the product of the ratios. -/
theorem tensor_range (g : ∀ i, Ω i → ℝ) (R : I → ℝ) (hg : ∀ i y, 0 ≤ g i y)
    (hR : ∀ i y y', g i y ≤ R i * g i y') (x x' : ∀ i, Ω i) :
    ∏ i, g i (x i) ≤ (∏ i, R i) * ∏ i, g i (x' i) := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun i _ => hg i _) (fun i _ => hR i _ _)

/-- **`lem:tilt-marginals`, product clause, chi-square.** If `E g_i = 1` and
`‖g_i - 1‖² ≤ δ_i²`, then `‖⊗_i g_i - 1‖² ≤ ∏_i (1 + δ_i²) - 1`. -/
theorem tensor_chiSq (ν : ∀ i, FiniteLaw (Ω i)) (g : ∀ i, Ω i → ℝ) (δ : I → ℝ)
    (hg1 : ∀ i, (ν i).expect (g i) = 1)
    (hδ : ∀ i, (ν i).expect (fun y => (g i y - 1) ^ 2) ≤ δ i ^ 2) :
    (FiniteLaw.pi ν).expect (fun x => (∏ i, g i (x i) - 1) ^ 2) ≤ ∏ i, (1 + δ i ^ 2) - 1 := by
  have hsq : ∀ i, (ν i).expect (fun y => g i y ^ 2) = 1 + (ν i).expect (fun y => (g i y - 1) ^ 2) := by
    intro i
    have e : (fun y => (g i y - 1) ^ 2) = fun y => (g i y ^ 2 - 2 * g i y) + 1 := by
      funext y; ring
    rw [e, FiniteLaw.expect_add, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
      FiniteLaw.expect_const, hg1 i]
    ring
  have e1 : (FiniteLaw.pi ν).expect (fun x => (∏ i, g i (x i) - 1) ^ 2) =
      (FiniteLaw.pi ν).expect (fun x => ∏ i, g i (x i) ^ 2) -
        2 * (FiniteLaw.pi ν).expect (fun x => ∏ i, g i (x i)) + 1 := by
    have e : (fun x : ∀ i, Ω i => (∏ i, g i (x i) - 1) ^ 2) =
        fun x => (∏ i, g i (x i) ^ 2 - 2 * ∏ i, g i (x i)) + 1 := by
      funext x
      rw [Finset.prod_pow]
      ring
    rw [e, FiniteLaw.expect_add, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
      FiniteLaw.expect_const]
  rw [e1, FiniteLaw.expect_pi_product ν (fun i y => g i y ^ 2), FiniteLaw.expect_pi_product ν g]
  simp only [hg1, Finset.prod_const_one]
  have : ∏ i, (ν i).expect (fun y => g i y ^ 2) ≤ ∏ i, (1 + δ i ^ 2) := by
    refine Finset.prod_le_prod₀ (fun i _ => (ν i).expect_nonneg (fun y => sq_nonneg _))
      (fun i _ => ?_)
    rw [hsq i]
    linarith [hδ i]
  linarith

end Products

end Sarkozy.Cuts
