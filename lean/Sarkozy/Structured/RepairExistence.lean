module

public import Sarkozy.Structured.MarginalRepair
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Existence and uniqueness for the repair equations (`lem:tr:repair`(a))

`lem:tr:repair`(a) (`paper/sections/17_completion_repair.tex`, brief F): for centred targets
`u`, `v`, the equations `f + Ag = u`, `g + A*f = v` have exactly one solution with `f`, `g`
centred (`repair_exists_unique`).

The paper writes the solution as `f = (I - AA*)^{-1}(u - Av)`, `g = v - A*f`. Here the
existence comes from finite dimension instead. On `(X → ℝ) × (Y → ℝ)` the linear map
`Φ(f, g) = (P f + A(P g) + (E f)𝟙, P g + A*(P f) + (E g)𝟙)`, with `P` the centring, is
injective: the means are preserved, since `E[Ak] = E k`, and the norm bounds `ρ < 1`
force `f = g = 0` (`repair_unique`). So `Φ` is surjective. The full support of the marginals
is used to pass from `‖f‖ = 0` to `f = 0`. `repair_swap` is (e): by uniqueness, a symmetric
system has `f = g`. `repair_invariant` is the invariance claim of (a), also by uniqueness: the
conditional operators commute with an action preserving `ν` (`condOp_equivariant`).
`repair_coupling_difference` is the last claim of (f): `ν' - π` has zero marginals and norm
at most `ρ' + ρ(π)` (`coupling_difference`, `abs_form_le_of_zero_marginals`).
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

open Sarkozy.Recentering

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- `‖f‖ = 0` forces `f = 0` when the law has full support. -/
theorem eq_zero_of_nrm_eq_zero (μ : FiniteLaw X) (hμ : ∀ x, 0 < μ.weight x) (f : X → ℝ)
    (hf : nrm μ f = 0) : f = 0 := by
  unfold nrm ip at hf
  have h0 : μ.expect (fun x => f x * f x) = 0 := by
    have hnn : 0 ≤ μ.expect (fun x => f x * f x) := μ.expect_nonneg fun x => mul_self_nonneg _
    rcases hnn.lt_or_eq with h | h
    · exact absurd hf (Real.sqrt_pos.mpr h).ne'
    · exact h.symm
  unfold FiniteLaw.expect at h0
  funext x
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
    mul_nonneg (μ.nonneg x) (mul_self_nonneg (f x)))).mp h0 x (mem_univ x)
  rcases mul_eq_zero.mp hterm with h | h
  · exact absurd h (hμ x).ne'
  · exact mul_self_eq_zero.mp h

/-- `E[Ak] = E k` (the conditional operator preserves means). -/
theorem expect_condOp (ν : FiniteLaw (X × Y)) (νX : FiniteLaw X) (νY : FiniteLaw Y)
    (hmY : ∀ φ : Y → ℝ, ν.expect (fun p => φ p.2) = νY.expect φ)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (hA : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νX h (A k))
    (k : Y → ℝ) : νX.expect (A k) = νY.expect k := by
  have h := hA (fun _ => 1) k
  rw [ip_one_left] at h
  rw [← h, ← hmY]
  exact ν.expect_congr fun p => one_mul _

/-- `E[A*h] = E h`. -/
theorem expect_condOp' (ν : FiniteLaw (X × Y)) (νX : FiniteLaw X) (νY : FiniteLaw Y)
    (hmX : ∀ φ : X → ℝ, ν.expect (fun p => φ p.1) = νX.expect φ)
    (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ)) (hB : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νY (B h) k)
    (h : X → ℝ) : νY.expect (B h) = νX.expect h := by
  have h1 := hB h (fun _ => 1)
  rw [ip_comm, ip_one_left] at h1
  rw [← h1, ← hmX]
  exact ν.expect_congr fun p => mul_one _

/-- **Uniqueness** (`lem:tr:repair`(a)): a centred solution of the homogeneous equations
`f + Ag = 0`, `g + A*f = 0` vanishes. -/
theorem repair_unique (νX : FiniteLaw X) (νY : FiniteLaw Y) (hνX : ∀ x, 0 < νX.weight x)
    (hνY : ∀ y, 0 < νY.weight y) (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hAρ : ∀ k, νY.expect k = 0 → nrm νX (A k) ≤ ρ * nrm νY k)
    (hBρ : ∀ h, νX.expect h = 0 → nrm νY (B h) ≤ ρ * nrm νX h)
    (f : X → ℝ) (g : Y → ℝ) (hf0 : νX.expect f = 0) (hg0 : νY.expect g = 0)
    (hfu : ∀ x, f x + A g x = 0) (hgv : ∀ y, g y + B f y = 0) : f = 0 ∧ g = 0 := by
  have hu : nrm νX (fun _ => (0 : ℝ)) ≤ 0 := by
    unfold nrm ip
    simp
  have hv : nrm νY (fun _ => (0 : ℝ)) ≤ 0 := by
    unfold nrm ip
    simp
  obtain ⟨h1, h2⟩ := repair_norm_bounds νX νY A B hρ hρ1 hAρ hBρ f g (fun _ => 0) (fun _ => 0)
    hf0 hg0 hfu hgv hu hv
  simp only [mul_zero, add_zero, zero_div] at h1 h2
  exact ⟨eq_zero_of_nrm_eq_zero νX hνX f (le_antisymm h1 (Real.sqrt_nonneg _)),
    eq_zero_of_nrm_eq_zero νY hνY g (le_antisymm h2 (Real.sqrt_nonneg _))⟩

/-- The centring as a linear map. -/
noncomputable def centerMap (μ : FiniteLaw X) : (X → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun f := center μ f
  map_add' f g := by
    funext x
    simp only [center, Pi.add_apply]
    have h : μ.expect (f + g) = μ.expect f + μ.expect g := μ.expect_add f g
    rw [h]
    ring
  map_smul' a f := by
    funext x
    simp only [center, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have h : μ.expect (a • f) = a * μ.expect f := μ.expect_const_mul a f
    rw [h]
    ring

theorem centerMap_apply (μ : FiniteLaw X) (f : X → ℝ) : centerMap μ f = center μ f := rfl

/-- The mean as a linear functional. -/
noncomputable def meanMap (μ : FiniteLaw X) : (X → ℝ) →ₗ[ℝ] ℝ where
  toFun f := μ.expect f
  map_add' f g := μ.expect_add f g
  map_smul' a f := μ.expect_const_mul a f

/-- **Existence and uniqueness** (`lem:tr:repair`(a)): for centred `u`, `v`, the equations
`f + Ag = u`, `g + A*f = v` have exactly one centred solution. -/
theorem repair_exists_unique (ν : FiniteLaw (X × Y)) (νX : FiniteLaw X) (νY : FiniteLaw Y)
    (hmX : ∀ φ : X → ℝ, ν.expect (fun p => φ p.1) = νX.expect φ)
    (hmY : ∀ φ : Y → ℝ, ν.expect (fun p => φ p.2) = νY.expect φ)
    (hνX : ∀ x, 0 < νX.weight x) (hνY : ∀ y, 0 < νY.weight y)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ))
    (hA : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νX h (A k))
    (hB : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νY (B h) k)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hAρ : ∀ k, νY.expect k = 0 → nrm νX (A k) ≤ ρ * nrm νY k)
    (hBρ : ∀ h, νX.expect h = 0 → nrm νY (B h) ≤ ρ * nrm νX h)
    (u : X → ℝ) (v : Y → ℝ) (hu0 : νX.expect u = 0) (hv0 : νY.expect v = 0) :
    (∃ f : X → ℝ, ∃ g : Y → ℝ, νX.expect f = 0 ∧ νY.expect g = 0 ∧
      (∀ x, f x + A g x = u x) ∧ (∀ y, g y + B f y = v y)) ∧
    (∀ f f' : X → ℝ, ∀ g g' : Y → ℝ, νX.expect f = 0 → νY.expect g = 0 →
      νX.expect f' = 0 → νY.expect g' = 0 →
      (∀ x, f x + A g x = u x) → (∀ y, g y + B f y = v y) →
      (∀ x, f' x + A g' x = u x) → (∀ y, g' y + B f' y = v y) → f = f' ∧ g = g') := by
  -- the linear map `Φ`
  set oneX : X → ℝ := fun _ => 1
  set oneY : Y → ℝ := fun _ => 1
  set Φ : ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ((X → ℝ) × (Y → ℝ)) :=
    LinearMap.prod
      (centerMap νX ∘ₗ LinearMap.fst ℝ _ _ + A ∘ₗ centerMap νY ∘ₗ LinearMap.snd ℝ _ _ +
        (LinearMap.smulRight (meanMap νX) oneX) ∘ₗ LinearMap.fst ℝ _ _)
      (centerMap νY ∘ₗ LinearMap.snd ℝ _ _ + B ∘ₗ centerMap νX ∘ₗ LinearMap.fst ℝ _ _ +
        (LinearMap.smulRight (meanMap νY) oneY) ∘ₗ LinearMap.snd ℝ _ _) with hΦ
  have hΦ1 : ∀ p : (X → ℝ) × (Y → ℝ), (Φ p).1 =
      fun x => center νX p.1 x + A (center νY p.2) x + νX.expect p.1 := by
    intro p
    funext x
    simp [hΦ, centerMap_apply, meanMap, oneX]
  have hΦ2 : ∀ p : (X → ℝ) × (Y → ℝ), (Φ p).2 =
      fun y => center νY p.2 y + B (center νX p.1) y + νY.expect p.2 := by
    intro p
    funext y
    simp [hΦ, centerMap_apply, meanMap, oneY]
  -- `Φ` preserves the means
  have hmean1 : ∀ p : (X → ℝ) × (Y → ℝ), νX.expect (Φ p).1 = νX.expect p.1 := by
    intro p
    rw [hΦ1, show (fun x => center νX p.1 x + A (center νY p.2) x + νX.expect p.1) =
      fun x => (center νX p.1 x + A (center νY p.2) x) + νX.expect p.1 from rfl,
      νX.expect_add, νX.expect_add, νX.expect_const, expect_center,
      expect_condOp ν νX νY hmY A hA, expect_center]
    ring
  have hmean2 : ∀ p : (X → ℝ) × (Y → ℝ), νY.expect (Φ p).2 = νY.expect p.2 := by
    intro p
    rw [hΦ2, show (fun y => center νY p.2 y + B (center νX p.1) y + νY.expect p.2) =
      fun y => (center νY p.2 y + B (center νX p.1) y) + νY.expect p.2 from rfl,
      νY.expect_add, νY.expect_add, νY.expect_const, expect_center,
      expect_condOp' ν νX νY hmX B hB, expect_center]
    ring
  -- on centred pairs, `Φ` is the repair map
  have hcen : ∀ (f : X → ℝ), νX.expect f = 0 → center νX f = f := by
    intro f hf
    funext x
    simp [center, hf]
  have hcen' : ∀ (g : Y → ℝ), νY.expect g = 0 → center νY g = g := by
    intro g hg
    funext y
    simp [center, hg]
  -- `Φ` is injective
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    have hf0 : νX.expect p.1 = 0 := by
      rw [← hmean1 p, hp]
      exact νX.expect_const 0
    have hg0 : νY.expect p.2 = 0 := by
      rw [← hmean2 p, hp]
      exact νY.expect_const 0
    have e1 := congrArg Prod.fst hp
    have e2 := congrArg Prod.snd hp
    rw [hΦ1, hcen p.1 hf0, hcen' p.2 hg0, hf0] at e1
    rw [hΦ2, hcen p.1 hf0, hcen' p.2 hg0, hg0] at e2
    obtain ⟨h1, h2⟩ := repair_unique νX νY hνX hνY A B hρ hρ1 hAρ hBρ p.1 p.2 hf0 hg0
      (fun x => by have := congrFun e1 x; simpa using this)
      (fun y => by have := congrFun e2 y; simpa using this)
    exact Prod.ext h1 h2
  have hsurj : Function.Surjective Φ := LinearMap.injective_iff_surjective.mp hinj
  constructor
  · obtain ⟨p, hp⟩ := hsurj (u, v)
    have hf0 : νX.expect p.1 = 0 := by rw [← hmean1 p, hp]; exact hu0
    have hg0 : νY.expect p.2 = 0 := by rw [← hmean2 p, hp]; exact hv0
    refine ⟨p.1, p.2, hf0, hg0, ?_, ?_⟩
    · intro x
      have e1 := congrArg Prod.fst hp
      rw [hΦ1, hcen p.1 hf0, hcen' p.2 hg0, hf0] at e1
      have := congrFun e1 x
      simpa using this
    · intro y
      have e2 := congrArg Prod.snd hp
      rw [hΦ2, hcen p.1 hf0, hcen' p.2 hg0, hg0] at e2
      have := congrFun e2 y
      simpa using this
  · intro f f' g g' hf hg hf' hg' h1 h2 h3 h4
    have hd := repair_unique νX νY hνX hνY A B hρ hρ1 hAρ hBρ (fun x => f x - f' x)
      (fun y => g y - g' y)
      (by rw [νX.expect_sub f f', hf, hf', sub_zero])
      (by rw [νY.expect_sub g g', hg, hg', sub_zero])
      (fun x => by
        have := h1 x; have := h3 x
        rw [show (fun y => g y - g' y) = g - g' from rfl, map_sub]
        simp only [Pi.sub_apply]
        linarith)
      (fun y => by
        have := h2 y; have := h4 y
        rw [show (fun x => f x - f' x) = f - f' from rfl, map_sub]
        simp only [Pi.sub_apply]
        linarith)
    constructor
    · funext x
      have := congrFun hd.1 x
      simp only [Pi.zero_apply] at this
      linarith
    · funext y
      have := congrFun hd.2 y
      simp only [Pi.zero_apply] at this
      linarith

/-- **`lem:tr:repair`(e), swap symmetry**: if `X = Y`, `A* = A` (a swap-invariant `ν`) and
the two targets agree, the centred solution has `f = g = s` with `(I + A)s = u`. -/
theorem repair_swap (ν : FiniteLaw (X × X)) (νX : FiniteLaw X)
    (hmX : ∀ φ : X → ℝ, ν.expect (fun p => φ p.1) = νX.expect φ)
    (hmY : ∀ φ : X → ℝ, ν.expect (fun p => φ p.2) = νX.expect φ)
    (hνX : ∀ x, 0 < νX.weight x) (A : (X → ℝ) →ₗ[ℝ] (X → ℝ))
    (hA : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νX h (A k))
    (hB : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νX (A h) k)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hAρ : ∀ k, νX.expect k = 0 → nrm νX (A k) ≤ ρ * nrm νX k)
    (u : X → ℝ) (f g : X → ℝ) (hf0 : νX.expect f = 0) (hg0 : νX.expect g = 0)
    (hfu : ∀ x, f x + A g x = u x) (hgv : ∀ y, g y + A f y = u y) :
    f = g ∧ ∀ x, f x + A f x = u x := by
  have hu0 : νX.expect u = 0 := by
    have : u = fun x => f x + A g x := funext fun x => (hfu x).symm
    rw [this, νX.expect_add, hf0, expect_condOp ν νX νX hmY A hA, hg0, add_zero]
  have huniq := (repair_exists_unique ν νX νX hmX hmY hνX hνX A A hA hB hρ hρ1 hAρ hAρ u u hu0
    hu0).2 f g g f hf0 hg0 hg0 hf0 hfu hgv hgv hfu
  refine ⟨huniq.1, fun x => ?_⟩
  have := hfu x
  rw [← huniq.1] at this
  exact this

/-! ### Invariance (`lem:tr:repair`(a), last claim) -/

/-- Two functions with the same inner products against every test function agree, under a
law of full support. -/
theorem eq_of_ip_eq (μ : FiniteLaw X) (hμ : ∀ x, 0 < μ.weight x) {a b : X → ℝ}
    (h : ∀ t : X → ℝ, ip μ t a = ip μ t b) : a = b := by
  classical
  funext x
  have hx := h (fun x' => if x' = x then 1 else 0)
  unfold ip FiniteLaw.expect at hx
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, sum_ite_eq', mem_univ,
    ite_true] at hx
  exact mul_left_cancel₀ (hμ x).ne' hx

/-- A law on `X × Y` invariant under `(x, y) ↦ (σ_X x, σ_Y y)` has a `σ_X`-invariant
`X`-marginal. -/
theorem marginal_invariant (ν : FiniteLaw (X × Y)) (νX : FiniteLaw X)
    (hmX : ∀ φ : X → ℝ, ν.expect (fun p => φ p.1) = νX.expect φ) (σX : X ≃ X) (σY : Y ≃ Y)
    (hν : ∀ F : X × Y → ℝ, ν.expect (fun p => F (σX p.1, σY p.2)) = ν.expect F)
    (φ : X → ℝ) : νX.expect (fun x => φ (σX x)) = νX.expect φ := by
  rw [← hmX, ← hmX]
  exact hν (fun p => φ p.1)

/-- The conditional operator commutes with an action preserving `ν`:
`A(k ∘ σ_Y) = (Ak) ∘ σ_X`. -/
theorem condOp_equivariant (ν : FiniteLaw (X × Y)) (νX : FiniteLaw X) (hνX : ∀ x, 0 < νX.weight x)
    (hmX : ∀ φ : X → ℝ, ν.expect (fun p => φ p.1) = νX.expect φ)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (hA : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νX h (A k))
    (σX : X ≃ X) (σY : Y ≃ Y)
    (hν : ∀ F : X × Y → ℝ, ν.expect (fun p => F (σX p.1, σY p.2)) = ν.expect F) (k : Y → ℝ) :
    A (fun y => k (σY y)) = fun x => A k (σX x) := by
  apply eq_of_ip_eq νX hνX
  intro t
  rw [← hA]
  have h1 : ν.expect (fun p => t p.1 * k (σY p.2)) =
      ν.expect (fun p => t (σX.symm p.1) * k p.2) := by
    rw [← hν (fun p => t (σX.symm p.1) * k p.2)]
    simp only [Equiv.symm_apply_apply]
  rw [h1, hA (fun x => t (σX.symm x)) k]
  unfold ip
  rw [← marginal_invariant ν νX hmX σX σY hν (fun x => t (σX.symm x) * A k x)]
  simp only [Equiv.symm_apply_apply]

/-- The adjoint commutes with the action: `A*(h ∘ σ_X) = (A*h) ∘ σ_Y`. -/
theorem condOp_equivariant' (ν : FiniteLaw (X × Y)) (νY : FiniteLaw Y) (hνY : ∀ y, 0 < νY.weight y)
    (hmY : ∀ φ : Y → ℝ, ν.expect (fun p => φ p.2) = νY.expect φ)
    (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ)) (hB : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νY (B h) k)
    (σX : X ≃ X) (σY : Y ≃ Y)
    (hν : ∀ F : X × Y → ℝ, ν.expect (fun p => F (σX p.1, σY p.2)) = ν.expect F) (h : X → ℝ) :
    B (fun x => h (σX x)) = fun y => B h (σY y) := by
  apply eq_of_ip_eq νY hνY
  intro t
  rw [ip_comm, ← hB]
  have h1 : ν.expect (fun p => h (σX p.1) * t p.2) =
      ν.expect (fun p => h p.1 * t (σY.symm p.2)) := by
    rw [← hν (fun p => h p.1 * t (σY.symm p.2))]
    simp only [Equiv.symm_apply_apply]
  have hYinv : ∀ φ : Y → ℝ, νY.expect (fun y => φ (σY y)) = νY.expect φ := by
    intro φ
    rw [← hmY, ← hmY]
    exact hν (fun p => φ p.2)
  rw [h1, hB h (fun y => t (σY.symm y))]
  unfold ip
  rw [← hYinv (fun y => B h y * t (σY.symm y))]
  simp only [Equiv.symm_apply_apply]
  exact νY.expect_congr fun y => mul_comm _ _

/-- **`lem:tr:repair`(a), invariance**: if `(x, y) ↦ (σ_X x, σ_Y y)` preserves `ν` and the
targets are invariant (`u ∘ σ_X = u`, `v ∘ σ_Y = v`; equivalently, the actions preserve `μ_X`
and `μ_Y`), then the centred solution is invariant, and so is `ν' = (1 + f + g)ν`. One
group element is treated at a time. -/
theorem repair_invariant (ν : FiniteLaw (X × Y)) (νX : FiniteLaw X) (νY : FiniteLaw Y)
    (hmX : ∀ φ : X → ℝ, ν.expect (fun p => φ p.1) = νX.expect φ)
    (hmY : ∀ φ : Y → ℝ, ν.expect (fun p => φ p.2) = νY.expect φ)
    (hνX : ∀ x, 0 < νX.weight x) (hνY : ∀ y, 0 < νY.weight y)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ))
    (hA : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νX h (A k))
    (hB : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νY (B h) k)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hAρ : ∀ k, νY.expect k = 0 → nrm νX (A k) ≤ ρ * nrm νY k)
    (hBρ : ∀ h, νX.expect h = 0 → nrm νY (B h) ≤ ρ * nrm νX h)
    (u : X → ℝ) (v : Y → ℝ) (f : X → ℝ) (g : Y → ℝ) (hf0 : νX.expect f = 0)
    (hg0 : νY.expect g = 0) (hfu : ∀ x, f x + A g x = u x) (hgv : ∀ y, g y + B f y = v y)
    (σX : X ≃ X) (σY : Y ≃ Y)
    (hν : ∀ F : X × Y → ℝ, ν.expect (fun p => F (σX p.1, σY p.2)) = ν.expect F)
    (hu : ∀ x, u (σX x) = u x) (hv : ∀ y, v (σY y) = v y) :
    (∀ x, f (σX x) = f x) ∧ (∀ y, g (σY y) = g y) ∧
      ∀ F : X × Y → ℝ, ν.expect (fun p => (1 + f p.1 + g p.2) * F (σX p.1, σY p.2)) =
        ν.expect (fun p => (1 + f p.1 + g p.2) * F p) := by
  have hu0 : νX.expect u = 0 := by
    have : u = fun x => f x + A g x := funext fun x => (hfu x).symm
    rw [this, νX.expect_add, hf0, expect_condOp ν νX νY hmY A hA, hg0, add_zero]
  have hv0 : νY.expect v = 0 := by
    have : v = fun y => g y + B f y := funext fun y => (hgv y).symm
    rw [this, νY.expect_add, hg0, expect_condOp' ν νX νY hmX B hB, hf0, add_zero]
  have hA' := condOp_equivariant ν νX hνX hmX A hA σX σY hν g
  have hB' := condOp_equivariant' ν νY hνY hmY B hB σX σY hν f
  have hf0' : νX.expect (fun x => f (σX x)) = 0 := by
    rw [marginal_invariant ν νX hmX σX σY hν f, hf0]
  have hg0' : νY.expect (fun y => g (σY y)) = 0 := by
    have : νY.expect (fun y => g (σY y)) = νY.expect g := by
      rw [← hmY, ← hmY]
      exact hν (fun p => g p.2)
    rw [this, hg0]
  have huniq := (repair_exists_unique ν νX νY hmX hmY hνX hνY A B hA hB hρ hρ1 hAρ hBρ u v hu0
    hv0).2 f (fun x => f (σX x)) g (fun y => g (σY y)) hf0 hg0 hf0' hg0' hfu hgv
    (fun x => by rw [hA']; exact (hfu (σX x)).trans (hu x))
    (fun y => by rw [hB']; exact (hgv (σY y)).trans (hv y))
  have hfi : ∀ x, f (σX x) = f x := fun x => (congrFun huniq.1 x).symm
  have hgi : ∀ y, g (σY y) = g y := fun y => (congrFun huniq.2 y).symm
  refine ⟨hfi, hgi, fun F => ?_⟩
  have := hν (fun p => (1 + f p.1 + g p.2) * F p)
  simp only [hfi, hgi] at this
  exact this

/-! ### The difference with a coupling (`lem:tr:repair`(f), last claim) -/

/-- A bilinear form with zero marginals sees only the centred parts of its arguments, so a
bound on centred functions holds on all functions. -/
theorem abs_form_le_of_zero_marginals (μX : FiniteLaw X) (μY : FiniteLaw Y)
    (D : (X → ℝ) →ₗ[ℝ] (Y → ℝ) →ₗ[ℝ] ℝ) (hD1 : ∀ φ, D φ (fun _ => 1) = 0)
    (hD2 : ∀ ψ, D (fun _ => 1) ψ = 0) {r : ℝ} (hr : 0 ≤ r)
    (hDr : ∀ h k, μX.expect h = 0 → μY.expect k = 0 → |D h k| ≤ r * nrm μX h * nrm μY k)
    (φ : X → ℝ) (ψ : Y → ℝ) : |D φ ψ| ≤ r * nrm μX φ * nrm μY ψ := by
  have hφ : φ = center μX φ + μX.expect φ • (fun _ => (1 : ℝ)) := by
    funext x; simp [center]
  have hψ : ψ = center μY ψ + μY.expect ψ • (fun _ => (1 : ℝ)) := by
    funext y; simp [center]
  have hsplit : D φ ψ = D (center μX φ) (center μY ψ) := by
    conv_lhs => rw [hφ, hψ]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hD1, hD2,
      smul_eq_mul, mul_zero, add_zero]
  rw [hsplit]
  refine (hDr _ _ (expect_center μX φ) (expect_center μY ψ)).trans ?_
  have h0 : 0 ≤ nrm μY (center μY ψ) := Real.sqrt_nonneg _
  calc r * nrm μX (center μX φ) * nrm μY (center μY ψ) ≤
        r * nrm μX φ * nrm μY (center μY ψ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (nrm_center_le μX φ) hr) h0
    _ ≤ r * nrm μX φ * nrm μY ψ :=
        mul_le_mul_of_nonneg_left (nrm_center_le μY ψ) (mul_nonneg hr (Real.sqrt_nonneg _))

/-- **`lem:tr:repair`(f), last claim**: if two bilinear forms `P` (e.g. `ν'`) and `Q` (a
coupling `π`) both have the marginals `μ_X`, `μ_Y`, with centred norms at most `r` (e.g. `ρ'`)
and `s` (`ρ(π)`), then `P - Q` has zero marginals and norm at most `r + s` as a form on all
of `L²(μ_X) × L²(μ_Y)`. -/
theorem coupling_difference (μX : FiniteLaw X) (μY : FiniteLaw Y)
    (P Q : (X → ℝ) →ₗ[ℝ] (Y → ℝ) →ₗ[ℝ] ℝ)
    (hP1 : ∀ φ, P φ (fun _ => 1) = μX.expect φ) (hP2 : ∀ ψ, P (fun _ => 1) ψ = μY.expect ψ)
    (hQ1 : ∀ φ, Q φ (fun _ => 1) = μX.expect φ) (hQ2 : ∀ ψ, Q (fun _ => 1) ψ = μY.expect ψ)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hPr : ∀ h k, μX.expect h = 0 → μY.expect k = 0 → |P h k| ≤ r * nrm μX h * nrm μY k)
    (hQs : ∀ h k, μX.expect h = 0 → μY.expect k = 0 → |Q h k| ≤ s * nrm μX h * nrm μY k) :
    (∀ φ, (P - Q) φ (fun _ => 1) = 0) ∧ (∀ ψ, (P - Q) (fun _ => 1) ψ = 0) ∧
      ∀ φ ψ, |(P - Q) φ ψ| ≤ (r + s) * nrm μX φ * nrm μY ψ := by
  have hD1 : ∀ φ, (P - Q) φ (fun _ => 1) = 0 := by
    intro φ
    simp only [LinearMap.sub_apply, hP1, hQ1, sub_self]
  have hD2 : ∀ ψ, (P - Q) (fun _ => 1) ψ = 0 := by
    intro ψ
    simp only [LinearMap.sub_apply, hP2, hQ2, sub_self]
  refine ⟨hD1, hD2, abs_form_le_of_zero_marginals μX μY (P - Q) hD1 hD2 (add_nonneg hr hs) ?_⟩
  intro h k hh hk
  simp only [LinearMap.sub_apply]
  calc |P h k - Q h k| ≤ |P h k| + |Q h k| := abs_sub _ _
    _ ≤ r * nrm μX h * nrm μY k + s * nrm μX h * nrm μY k :=
        add_le_add (hPr h k hh hk) (hQs h k hh hk)
    _ = (r + s) * nrm μX h * nrm μY k := by ring

/-- **`lem:tr:repair`(f), last claim, for the repaired law**: let `μ_X = (1 + u)ν_X` and
`μ_Y = (1 + v)ν_Y` be the target laws, and `π` a coupling of them (a bilinear form with these
marginals) whose centred norm is at most `ρ(π)`. Then `ν' - π` has zero marginals and norm at
most `ρ' + ρ(π)` on all functions, with `ρ'` the centred norm of (f). -/
theorem repair_coupling_difference (ν : FiniteLaw (X × Y)) (νX : FiniteLaw X)
    (νY : FiniteLaw Y)
    (hmX : ∀ φ : X → ℝ, ν.expect (fun p => φ p.1) = νX.expect φ)
    (hmY : ∀ φ : Y → ℝ, ν.expect (fun p => φ p.2) = νY.expect φ)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ))
    (hA : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νX h (A k))
    (hB : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νY (B h) k)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hAρ : ∀ k, νY.expect k = 0 → nrm νX (A k) ≤ ρ * nrm νY k)
    (hBρ : ∀ h, νX.expect h = 0 → nrm νY (B h) ≤ ρ * nrm νX h)
    (f : X → ℝ) (g : Y → ℝ) (u : X → ℝ) (v : Y → ℝ) (hf0 : νX.expect f = 0)
    (hg0 : νY.expect g = 0) (hfu : ∀ x, f x + A g x = u x) (hgv : ∀ y, g y + B f y = v y)
    {UX UY eX eY FX FY : ℝ} (hUX : UX < 1) (hUY : UY < 1) (huU : ∀ x, -UX ≤ u x)
    (hvU : ∀ y, -UY ≤ v y) (he : nrm νX u * nrm νY v ≤ eX * eY)
    (hFX : 0 ≤ FX) (hFY : 0 ≤ FY) (hfF : ∀ x, |f x| ≤ FX) (hgF : ∀ y, |g y| ≤ FY)
    (heX : 0 ≤ eX) (heY : 0 ≤ eY)
    (μX : FiniteLaw X) (μY : FiniteLaw Y)
    (hμX : ∀ φ : X → ℝ, μX.expect φ = νX.expect (fun x => (1 + u x) * φ x))
    (hμY : ∀ φ : Y → ℝ, μY.expect φ = νY.expect (fun y => (1 + v y) * φ y))
    (π : (X → ℝ) →ₗ[ℝ] (Y → ℝ) →ₗ[ℝ] ℝ)
    (hπ1 : ∀ φ, π φ (fun _ => 1) = μX.expect φ) (hπ2 : ∀ ψ, π (fun _ => 1) ψ = μY.expect ψ)
    {ρπ : ℝ} (hρπ : 0 ≤ ρπ)
    (hπρ : ∀ h k, μX.expect h = 0 → μY.expect k = 0 → |π h k| ≤ ρπ * nrm μX h * nrm μY k) :
    (∀ φ, (reweightForm ν f g - π) φ (fun _ => 1) = 0) ∧
      (∀ ψ, (reweightForm ν f g - π) (fun _ => 1) ψ = 0) ∧
      ∀ φ ψ, |(reweightForm ν f g - π) φ ψ| ≤
        ((ρ * (1 + FX + FY) + eX * eY) / Real.sqrt ((1 - UX) * (1 - UY)) + ρπ) *
          nrm μX φ * nrm μY ψ := by
  obtain ⟨hu, hv⟩ := repair_marginals ν νX νY hmX hmY A B hA hB f g u v hfu hgv
  have hnX : ∀ h : X → ℝ, nrm μX h = Real.sqrt (νX.expect (fun x => (1 + u x) * h x ^ 2)) := by
    intro h
    unfold nrm ip
    rw [hμX]
    congr 1
    exact νX.expect_congr fun x => by ring
  have hnY : ∀ k : Y → ℝ, nrm μY k = Real.sqrt (νY.expect (fun y => (1 + v y) * k y ^ 2)) := by
    intro k
    unfold nrm ip
    rw [hμY]
    congr 1
    exact νY.expect_congr fun y => by ring
  have hr : 0 ≤ (ρ * (1 + FX + FY) + eX * eY) / Real.sqrt ((1 - UX) * (1 - UY)) := by
    apply div_nonneg _ (Real.sqrt_nonneg _)
    have : 0 ≤ ρ * (1 + FX + FY) := mul_nonneg hρ (by linarith)
    nlinarith [mul_nonneg heX heY]
  refine coupling_difference μX μY (reweightForm ν f g) π ?_ ?_ hπ1 hπ2 hr hρπ ?_ hπρ
  · intro φ
    rw [hu, hμX]
    unfold ip
    exact νX.expect_congr fun x => by ring
  · intro ψ
    rw [hv, hμY]
    unfold ip
    exact νY.expect_congr fun y => by ring
  · intro h k hh hk
    rw [hnX, hnY]
    refine repair_centred_norm ν νX νY hmX hmY A B hA hB hρ hAρ hBρ f g u v hf0 hg0 hfu hgv hUX
      hUY huU hvU he hFX hFY hfF hgF h k ?_ ?_
    · rw [hμX] at hh
      unfold ip
      rw [← hh]
      exact νX.expect_congr fun x => by ring
    · rw [hμY] at hk
      unfold ip
      exact hk

end Sarkozy.Structured
