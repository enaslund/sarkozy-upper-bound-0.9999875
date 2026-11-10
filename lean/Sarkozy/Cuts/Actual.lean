module

public import Sarkozy.Comparison.Recentering
public import Sarkozy.Peyre.Correlation





@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The bilinear form of a kernel `K` relative to `ν ⊗ μ`:
`𝔟(f, h) = ∑_{x,y} ν(x) μ(y) f(x) K(x, y) h(y)`. -/
noncomputable def kernelForm (ν : FiniteLaw X) (μ : FiniteLaw Y) (K : X → Y → ℝ) :
    (X → ℝ) →ₗ[ℝ] (Y → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f h => ∑ x, ∑ y, ν.weight x * μ.weight y * f x * K x y * h y)
    (fun f₁ f₂ h => by
      simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib])
    (fun c f h => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring)))
    (fun f h₁ h₂ => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c f h => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring)))

theorem kernelForm_apply (ν : FiniteLaw X) (μ : FiniteLaw Y) (K : X → Y → ℝ) (f : X → ℝ)
    (h : Y → ℝ) : kernelForm ν μ K f h =
      ν.expect (fun x => f x * μ.expect (fun y => K x y * h y)) := by
  simp only [kernelForm, LinearMap.mk₂_apply, FiniteLaw.expect, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))

theorem kernelForm_one_right (ν : FiniteLaw X) (μ : FiniteLaw Y) (K : X → Y → ℝ)
    (f : X → ℝ) : kernelForm ν μ K f (fun _ => 1) =
      ip ν f (fun x => μ.expect (fun y => K x y)) := by
  rw [kernelForm_apply]
  unfold ip
  exact ν.expect_congr (fun x => by simp only [mul_one])

theorem kernelForm_one_left (ν : FiniteLaw X) (μ : FiniteLaw Y) (K : X → Y → ℝ)
    (h : Y → ℝ) : kernelForm ν μ K (fun _ => 1) h =
      ip μ (fun y => ν.expect (fun x => K x y)) h := by
  rw [kernelForm_apply]
  unfold ip FiniteLaw.expect
  simp only [one_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => by ring))

/-- A pointwise bound `|δ| ≤ η` bounds the norm: `‖δ‖_ν ≤ η`. -/
theorem nrm_le_of_abs_le (ν : FiniteLaw X) {δ : X → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ x, |δ x| ≤ η) : nrm ν δ ≤ η := by
  unfold nrm ip
  rw [← Real.sqrt_sq hη]
  apply Real.sqrt_le_sqrt
  apply ν.expect_le_const
  intro x
  have := h x
  nlinarith [abs_mul_abs_self (δ x), abs_nonneg (δ x)]

/-- Norms relative to `ν` against norms relative to `ψν` with `ψ ≥ l > 0`:
`‖f‖_ν² ≤ ‖f‖²_{ψν} / l`. -/
theorem expect_sq_le_of_density_ge (ν : FiniteLaw X) {ψ : X → ℝ} {l : ℝ} (hl : 0 < l)
    (hψ : ∀ x, l ≤ ψ x) (f : X → ℝ) :
    ν.expect (fun x => f x ^ 2) ≤ ν.expect (fun x => ψ x * f x ^ 2) / l := by
  rw [le_div_iff₀ hl, ← FiniteLaw.expect_mul_const]
  exact ν.expect_mono (fun x => by nlinarith [sq_nonneg (f x), hψ x])

theorem nrm_le_of_density_ge (ν : FiniteLaw X) {ψ : X → ℝ} {l : ℝ} (hl : 0 < l)
    (hψ : ∀ x, l ≤ ψ x) (f : X → ℝ) :
    nrm ν f ≤ √(ν.expect (fun x => ψ x * f x ^ 2)) / √l := by
  unfold nrm ip
  rw [← Real.sqrt_div' _ hl.le]
  apply Real.sqrt_le_sqrt
  have h := expect_sq_le_of_density_ge ν hl hψ f
  have e : ν.expect (fun x => f x * f x) = ν.expect (fun x => f x ^ 2) :=
    ν.expect_congr (fun x => by ring)
  rw [e]
  exact h

/-- **`lem:record:actual-correlation` (a).** Let `K` be a kernel relative to `ν ⊗ ν` with total
mass one and marginals `m_L = (1 + δ_L)ν`, `m_R = (1 + δ_R)ν`, `|δ_L|, |δ_R| ≤ η < 1`. Let `H`
be any set of functions (the paper's space containing the constants; the closure property is
not needed in this form). Assume `|𝔟(Πf, Πg)| ≤ κ ‖Πf‖ ‖Πg‖` for `f, g ∈ H`. Then for `f, g ∈ H` with `E_{m_L} f = E_{m_R} g = 0`,
`|𝔟(f, g)| ≤ (κ + η²)/(1 - η) ‖f‖_{m_L} ‖g‖_{m_R}`. -/
theorem actual_correlation (ν : FiniteLaw X) (K : X → X → ℝ) {η κ : ℝ} (hη0 : 0 ≤ η)
    (hη1 : η < 1) (hκ : 0 ≤ κ) (δL δR : X → ℝ)
    (hmass : ν.expect (fun x => ν.expect (fun y => K x y)) = 1)
    (hmL : ∀ x, ν.expect (fun y => K x y) = 1 + δL x)
    (hmR : ∀ y, ν.expect (fun x => K x y) = 1 + δR y)
    (hδL : ∀ x, |δL x| ≤ η) (hδR : ∀ y, |δR y| ≤ η)
    (H : (X → ℝ) → Prop)
    (hcen : ∀ f g, H f → H g → |kernelForm ν ν K (center ν f) (center ν g)| ≤
      κ * nrm ν (center ν f) * nrm ν (center ν g))
    {f g : X → ℝ} (hf : H f) (hg : H g)
    (hf0 : ν.expect (fun x => (1 + δL x) * f x) = 0)
    (hg0 : ν.expect (fun y => (1 + δR y) * g y) = 0) :
    |kernelForm ν ν K f g| ≤ (κ + η ^ 2) / (1 - η) *
      √(ν.expect (fun x => (1 + δL x) * f x ^ 2)) *
      √(ν.expect (fun y => (1 + δR y) * g y ^ 2)) := by
  set ρL : X → ℝ := fun x => 1 + δL x with hρL
  set ρR : X → ℝ := fun y => 1 + δR y with hρR
  have h11 : kernelForm ν ν K (fun _ => 1) (fun _ => 1) = 1 := by
    rw [kernelForm_one_right]
    unfold ip
    simp only [one_mul]
    exact hmass
  have hL : ∀ f, kernelForm ν ν K f (fun _ => 1) = ip ν f ρL := by
    intro f
    rw [kernelForm_one_right]
    unfold ip
    exact ν.expect_congr (fun x => by simp only [hmL x, hρL])
  have hR : ∀ h, kernelForm ν ν K (fun _ => 1) h = ip ν ρR h := by
    intro h
    rw [kernelForm_one_left]
    unfold ip
    exact ν.expect_congr (fun y => by simp only [hmR y, hρR])
  have hfL : ip ν f ρL = 0 := by
    unfold ip
    rw [← hf0]
    exact ν.expect_congr (fun x => by simp only [hρL]; ring_nf)
  have hgR : ip ν ρR g = 0 := by
    unfold ip
    rw [← hg0]
  have hid := recentering_identity ν ν (kernelForm ν ν K) ρL ρR h11 hL hR hfL hgR
  have hcf := hcen f g hf hg
  have hδLn : nrm ν (fun x => ρL x - 1) ≤ η :=
    nrm_le_of_abs_le ν hη0 (fun x => by simp only [hρL, add_sub_cancel_left]; exact hδL x)
  have hδRn : nrm ν (fun y => ρR y - 1) ≤ η :=
    nrm_le_of_abs_le ν hη0 (fun y => by simp only [hρR, add_sub_cancel_left]; exact hδR y)
  have hfn := nrm_center_le ν f
  have hgn := nrm_center_le ν g
  have hcf0 : 0 ≤ nrm ν (center ν f) := Real.sqrt_nonneg _
  have hcg0 : 0 ≤ nrm ν (center ν g) := Real.sqrt_nonneg _
  have h2 : |ip ν (fun x => ρL x - 1) (center ν f) * ip ν (fun y => ρR y - 1) (center ν g)| ≤
      η * nrm ν (center ν f) * (η * nrm ν (center ν g)) := by
    rw [abs_mul]
    apply mul_le_mul _ _ (abs_nonneg _) (by positivity)
    · exact (abs_ip_le ν _ _).trans (mul_le_mul_of_nonneg_right hδLn hcf0)
    · exact (abs_ip_le ν _ _).trans (mul_le_mul_of_nonneg_right hδRn hcg0)
  have hstep : |kernelForm ν ν K f g| ≤ (κ + η ^ 2) * (nrm ν f * nrm ν g) := by
    rw [hid]
    calc _ ≤ |kernelForm ν ν K (center ν f) (center ν g)| +
          |ip ν (fun x => ρL x - 1) (center ν f) * ip ν (fun y => ρR y - 1) (center ν g)| :=
          abs_sub _ _
      _ ≤ κ * nrm ν (center ν f) * nrm ν (center ν g) +
          η * nrm ν (center ν f) * (η * nrm ν (center ν g)) := add_le_add hcf h2
      _ = (κ + η ^ 2) * (nrm ν (center ν f) * nrm ν (center ν g)) := by ring
      _ ≤ (κ + η ^ 2) * (nrm ν f * nrm ν g) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hfn hgn hcg0 (Real.sqrt_nonneg _))
            (by positivity)
  have hl : 0 < 1 - η := by linarith
  have hψL : ∀ x, 1 - η ≤ ρL x := fun x => by
    have := hδL x
    simp only [hρL]
    linarith [neg_abs_le (δL x)]
  have hψR : ∀ y, 1 - η ≤ ρR y := fun y => by
    have := hδR y
    simp only [hρR]
    linarith [neg_abs_le (δR y)]
  have hnf := nrm_le_of_density_ge ν hl hψL f
  have hng := nrm_le_of_density_ge ν hl hψR g
  have hs : √(1 - η) * √(1 - η) = 1 - η := Real.mul_self_sqrt hl.le
  have hs0 : 0 < √(1 - η) := Real.sqrt_pos.mpr hl
  calc |kernelForm ν ν K f g| ≤ (κ + η ^ 2) * (nrm ν f * nrm ν g) := hstep
    _ ≤ (κ + η ^ 2) * ((√(ν.expect (fun x => ρL x * f x ^ 2)) / √(1 - η)) *
          (√(ν.expect (fun y => ρR y * g y ^ 2)) / √(1 - η))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hnf hng (Real.sqrt_nonneg _)
          (div_nonneg (Real.sqrt_nonneg _) hs0.le)) (by positivity)
    _ = (κ + η ^ 2) / (1 - η) * √(ν.expect (fun x => ρL x * f x ^ 2)) *
          √(ν.expect (fun y => ρR y * g y ^ 2)) := by
        rw [div_mul_div_comm, hs]
        ring

/-- `W f = ψ^{1/2} f` is an isometry `L²(ψν) → L²(ν)`. -/
theorem nrm_sqrt_mul (ν : FiniteLaw X) {ψ : X → ℝ} (hψ : ∀ x, 0 ≤ ψ x) (f : X → ℝ) :
    nrm ν (fun x => √(ψ x) * f x) = √(ν.expect (fun x => ψ x * f x ^ 2)) := by
  unfold nrm ip
  congr 1
  exact ν.expect_congr (fun x => by
    have := Real.mul_self_sqrt (hψ x)
    nlinarith [this])

/-- **`lem:record:actual-correlation` (b), density transport.** If the form of a kernel `t`
relative to `ν ⊗ ν` has norm at most `c` on `L²(ν)`, then on `L²(m)` with `m = ψν`,
`ψ ≥ l > 0` (for instance `l = 1 - η`), it has norm at most `c / l`. That is,
`‖T_m‖ ≤ ‖T‖ / min ψ`. -/
theorem density_transport (ν : FiniteLaw X) (t : X → X → ℝ) {ψ : X → ℝ} {l c : ℝ} (hl : 0 < l)
    (hψ : ∀ x, l ≤ ψ x) (hc : 0 ≤ c)
    (hT : ∀ f h, |kernelForm ν ν t f h| ≤ c * nrm ν f * nrm ν h) (f h : X → ℝ) :
    |kernelForm ν ν t f h| ≤ c / l * √(ν.expect (fun x => ψ x * f x ^ 2)) *
      √(ν.expect (fun x => ψ x * h x ^ 2)) := by
  have hnf := nrm_le_of_density_ge ν hl hψ f
  have hnh := nrm_le_of_density_ge ν hl hψ h
  have hs : √l * √l = l := Real.mul_self_sqrt hl.le
  have hs0 : 0 < √l := Real.sqrt_pos.mpr hl
  calc |kernelForm ν ν t f h| ≤ c * nrm ν f * nrm ν h := hT f h
    _ = c * (nrm ν f * nrm ν h) := by ring
    _ ≤ c * ((√(ν.expect (fun x => ψ x * f x ^ 2)) / √l) *
          (√(ν.expect (fun x => ψ x * h x ^ 2)) / √l)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hnf hnh (Real.sqrt_nonneg _)
          (div_nonneg (Real.sqrt_nonneg _) hs0.le)) hc
    _ = c / l * √(ν.expect (fun x => ψ x * f x ^ 2)) *
          √(ν.expect (fun x => ψ x * h x ^ 2)) := by
        rw [div_mul_div_comm, hs]
        ring

/-- The transposed kernel gives the adjoint: `𝔟_{tᵀ}(h, f) = 𝔟_t(f, h)`. -/
theorem kernelForm_transpose (ν : FiniteLaw X) (μ : FiniteLaw Y) (t : X → Y → ℝ) (f : X → ℝ)
    (h : Y → ℝ) : kernelForm μ ν (fun y x => t x y) h f = kernelForm ν μ t f h := by
  simp only [kernelForm, LinearMap.mk₂_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))

end Sarkozy.Cuts
