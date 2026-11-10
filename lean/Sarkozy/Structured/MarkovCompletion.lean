module

public import Sarkozy.Structured.MarginalRepair

/-!
# Completion by mixing in a coupling of the target marginals (`cor:markov-completion`)

`cor:markov-completion` (`paper/sections/17_completion_repair.tex`, brief F). The setting:
* `m_X`, `m_Y` are probability measures on finite sets;
* `R ≥ 0` is a density relative to `m_X ⊗ m_Y` with marginal defects `α = 1 - R𝟙`,
  `β = 1 - R*𝟙`, `|α|, |β| ≤ M`;
* `J ≥ 0` is a coupling density (`J𝟙 = 𝟙`, `J*𝟙 = 𝟙`) with `Jβ = 0` and `J*α = 0`.

Then `P = (R + J(α(x) + β(y)) + 2MJ)/(1 + 2M)` is a probability density with marginals `m_X`,
`m_Y`. It vanishes where `R` and `J` both vanish, and
`‖Q(P - R)Q‖ ≤ 2M(‖QRQ‖ + 2‖QJQ‖)`.

Kernels are functions on `X × Y` (densities relative to `m_X ⊗ m_Y`). The operator norm of a
compression `QKQ` is stated as the bound of its bilinear form on centred functions,
`|∫∫ φ(x)ψ(y)K(x,y)| ≤ c ‖φ‖ ‖ψ‖` for `E φ = E ψ = 0` (`kform`). This is how the bound is
used.

* `markov_completion_nonneg`, `markov_completion_marginals`, `markov_completion_support`;
* `markov_completion_norm`: the norm bound. The proof is the paper's: `J` maps centred
  functions to centred functions, so `Q M_α J Q = Q M_α (QJQ)` and
  `Q J M_β Q = (QJQ)(Q M_β Q)`.

* `markov_completion_invariant`: the invariance statement, for one group element at a time.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

open Sarkozy.Recentering

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The bilinear form `∫∫ φ(x) ψ(y) K(x,y) dm_X dm_Y` of a kernel. -/
noncomputable def kform (mX : FiniteLaw X) (mY : FiniteLaw Y) (K : X × Y → ℝ) (φ : X → ℝ)
    (ψ : Y → ℝ) : ℝ :=
  mX.expect (fun x => mY.expect (fun y => φ x * ψ y * K (x, y)))

/-- The completed kernel `P = (R + J(α + β) + 2MJ)/(1 + 2M)`. -/
noncomputable def markovCompletion (R J : X × Y → ℝ) (α : X → ℝ) (β : Y → ℝ) (M : ℝ) :
    X × Y → ℝ :=
  fun p => (R p + J p * (α p.1 + β p.2) + 2 * M * J p) / (1 + 2 * M)

omit [Fintype X] [Fintype Y] in
/-- `P ≥ 0`. -/
theorem markov_completion_nonneg (R J : X × Y → ℝ) (α : X → ℝ) (β : Y → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hR : ∀ p, 0 ≤ R p) (hJ : ∀ p, 0 ≤ J p) (hα : ∀ x, |α x| ≤ M)
    (hβ : ∀ y, |β y| ≤ M) (p : X × Y) : 0 ≤ markovCompletion R J α β M p := by
  unfold markovCompletion
  apply div_nonneg _ (by linarith)
  have h1 := abs_le.mp (hα p.1)
  have h2 := abs_le.mp (hβ p.2)
  have h3 : 0 ≤ J p * (α p.1 + β p.2 + 2 * M) := mul_nonneg (hJ p) (by linarith)
  nlinarith [hR p]

omit [Fintype X] [Fintype Y] in
/-- `P` vanishes wherever `R` and `J` both vanish. -/
theorem markov_completion_support (R J : X × Y → ℝ) (α : X → ℝ) (β : Y → ℝ) (M : ℝ)
    (p : X × Y) (hRp : R p = 0) (hJp : J p = 0) : markovCompletion R J α β M p = 0 := by
  unfold markovCompletion
  rw [hRp, hJp]
  ring

/-- **The marginals of `P`** are `m_X` and `m_Y`. -/
theorem markov_completion_marginals (mX : FiniteLaw X) (mY : FiniteLaw Y)
    (R J : X × Y → ℝ) (α : X → ℝ) (β : Y → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hαdef : ∀ x, α x = 1 - mY.expect (fun y => R (x, y)))
    (hβdef : ∀ y, β y = 1 - mX.expect (fun x => R (x, y)))
    (hJ1 : ∀ x, mY.expect (fun y => J (x, y)) = 1) (hJ1' : ∀ y, mX.expect (fun x => J (x, y)) = 1)
    (hJβ : ∀ x, mY.expect (fun y => J (x, y) * β y) = 0)
    (hJα : ∀ y, mX.expect (fun x => J (x, y) * α x) = 0) :
    (∀ x, mY.expect (fun y => markovCompletion R J α β M (x, y)) = 1) ∧
      (∀ y, mX.expect (fun x => markovCompletion R J α β M (x, y)) = 1) := by
  have hpos : (1 + 2 * M) ≠ 0 := by linarith
  constructor
  · intro x
    unfold markovCompletion
    have e : (fun y => (R (x, y) + J (x, y) * (α x + β y) + 2 * M * J (x, y)) / (1 + 2 * M)) =
        fun y => (1 + 2 * M)⁻¹ * (R (x, y) + (α x + 2 * M) * J (x, y) + J (x, y) * β y) := by
      funext y; field_simp; ring
    rw [e, mY.expect_const_mul, mY.expect_add, mY.expect_add, mY.expect_const_mul, hJ1, hJβ,
      hαdef x]
    field_simp
    ring
  · intro y
    unfold markovCompletion
    have e : (fun x => (R (x, y) + J (x, y) * (α x + β y) + 2 * M * J (x, y)) / (1 + 2 * M)) =
        fun x => (1 + 2 * M)⁻¹ * (R (x, y) + (β y + 2 * M) * J (x, y) + J (x, y) * α x) := by
      funext x; field_simp; ring
    rw [e, mX.expect_const_mul, mX.expect_add, mX.expect_add, mX.expect_const_mul, hJ1', hJα,
      hβdef y]
    field_simp
    ring

/-! ### Linearity of `kform` in the kernel -/

theorem kform_congr (mX : FiniteLaw X) (mY : FiniteLaw Y) {K K' : X × Y → ℝ}
    (h : ∀ p, K p = K' p) (φ : X → ℝ) (ψ : Y → ℝ) : kform mX mY K φ ψ = kform mX mY K' φ ψ := by
  unfold kform
  exact mX.expect_congr fun x => mY.expect_congr fun y => by rw [h]

theorem kform_add (mX : FiniteLaw X) (mY : FiniteLaw Y) (K K' : X × Y → ℝ) (φ : X → ℝ)
    (ψ : Y → ℝ) :
    kform mX mY (fun p => K p + K' p) φ ψ = kform mX mY K φ ψ + kform mX mY K' φ ψ := by
  unfold kform
  rw [← mX.expect_add]
  exact mX.expect_congr fun x => by rw [← mY.expect_add]; exact mY.expect_congr fun y => by ring

theorem kform_sub (mX : FiniteLaw X) (mY : FiniteLaw Y) (K K' : X × Y → ℝ) (φ : X → ℝ)
    (ψ : Y → ℝ) :
    kform mX mY (fun p => K p - K' p) φ ψ = kform mX mY K φ ψ - kform mX mY K' φ ψ := by
  unfold kform
  rw [← mX.expect_sub]
  exact mX.expect_congr fun x => by rw [← mY.expect_sub]; exact mY.expect_congr fun y => by ring

theorem kform_const_mul (mX : FiniteLaw X) (mY : FiniteLaw Y) (c : ℝ) (K : X × Y → ℝ)
    (φ : X → ℝ) (ψ : Y → ℝ) : kform mX mY (fun p => c * K p) φ ψ = c * kform mX mY K φ ψ := by
  unfold kform
  rw [← mX.expect_const_mul]
  exact mX.expect_congr fun x => by
    rw [← mY.expect_const_mul]; exact mY.expect_congr fun y => by ring

theorem kform_mul_left (mX : FiniteLaw X) (mY : FiniteLaw Y) (α : X → ℝ) (K : X × Y → ℝ)
    (φ : X → ℝ) (ψ : Y → ℝ) :
    kform mX mY (fun p => α p.1 * K p) φ ψ = kform mX mY K (fun x => α x * φ x) ψ := by
  unfold kform
  exact mX.expect_congr fun x => mY.expect_congr fun y => by ring

theorem kform_mul_right (mX : FiniteLaw X) (mY : FiniteLaw Y) (β : Y → ℝ) (K : X × Y → ℝ)
    (φ : X → ℝ) (ψ : Y → ℝ) :
    kform mX mY (fun p => K p * β p.2) φ ψ = kform mX mY K φ (fun y => β y * ψ y) := by
  unfold kform
  exact mX.expect_congr fun x => mY.expect_congr fun y => by ring

/-- The bilinear form of `(1 + 2M)(P - R) = M_α J + J M_β + 2MJ - 2MR`. -/
theorem kform_markovCompletion (mX : FiniteLaw X) (mY : FiniteLaw Y) (R J : X × Y → ℝ)
    (α : X → ℝ) (β : Y → ℝ) {M : ℝ} (hM : 0 ≤ M) (φ : X → ℝ) (ψ : Y → ℝ) :
    (1 + 2 * M) * (kform mX mY (markovCompletion R J α β M) φ ψ - kform mX mY R φ ψ) =
      kform mX mY J (fun x => α x * φ x) ψ + kform mX mY J φ (fun y => β y * ψ y) +
        2 * M * kform mX mY J φ ψ - 2 * M * kform mX mY R φ ψ := by
  have hpos : (1 + 2 * M) ≠ 0 := by linarith
  rw [← kform_sub, ← kform_const_mul]
  rw [kform_congr mX mY (K' := fun p => ((fun p => α p.1 * J p) p + (fun p => J p * β p.2) p +
      (fun p => 2 * M * J p) p) - (fun p => 2 * M * R p) p) (fun p => by
        unfold markovCompletion; field_simp; ring)]
  rw [kform_sub, kform_add, kform_add, kform_mul_left, kform_mul_right, kform_const_mul,
    kform_const_mul]

/-- `J` maps centred functions to centred functions: for `E ψ = 0`, the form of `J` at
`(φ, ψ)` only sees the centred part of `φ`. -/
theorem kform_center_left (mX : FiniteLaw X) (mY : FiniteLaw Y) (J : X × Y → ℝ)
    (hJ1' : ∀ y, mX.expect (fun x => J (x, y)) = 1) (φ : X → ℝ) (ψ : Y → ℝ)
    (hψ : mY.expect ψ = 0) : kform mX mY J φ ψ = kform mX mY J (center mX φ) ψ := by
  unfold kform center
  have h : ∀ x, mY.expect (fun y => (φ x - mX.expect φ) * ψ y * J (x, y)) =
      mY.expect (fun y => φ x * ψ y * J (x, y)) -
        mX.expect φ * mY.expect (fun y => ψ y * J (x, y)) := by
    intro x
    rw [← mY.expect_const_mul, ← mY.expect_sub]
    exact mY.expect_congr fun y => by ring
  simp_rw [h]
  rw [mX.expect_sub, mX.expect_const_mul]
  -- `E_x E_y ψ(y) J(x,y) = E_y ψ(y) E_x J(x,y) = E ψ = 0`
  have hswap : mX.expect (fun x => mY.expect (fun y => ψ y * J (x, y))) =
      mY.expect (fun y => ψ y * mX.expect (fun x => J (x, y))) := by
    unfold FiniteLaw.expect
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro y _
    apply sum_congr rfl
    intro x _
    ring
  rw [hswap]
  simp_rw [hJ1', mul_one]
  rw [hψ, mul_zero, sub_zero]

/-- The same on the right. -/
theorem kform_center_right (mX : FiniteLaw X) (mY : FiniteLaw Y) (J : X × Y → ℝ)
    (hJ1 : ∀ x, mY.expect (fun y => J (x, y)) = 1) (φ : X → ℝ) (ψ : Y → ℝ)
    (hφ : mX.expect φ = 0) : kform mX mY J φ ψ = kform mX mY J φ (center mY ψ) := by
  unfold kform center
  have h : ∀ x, mY.expect (fun y => φ x * (ψ y - mY.expect ψ) * J (x, y)) =
      mY.expect (fun y => φ x * ψ y * J (x, y)) -
        mY.expect ψ * (φ x * mY.expect (fun y => J (x, y))) := by
    intro x
    rw [← mY.expect_const_mul, ← mY.expect_const_mul, ← mY.expect_sub]
    exact mY.expect_congr fun y => by ring
  simp_rw [h, hJ1, mul_one]
  rw [mX.expect_sub, mX.expect_const_mul, hφ, mul_zero, sub_zero]

/-- **`cor:markov-completion`, the norm bound**: if `‖QRQ‖ ≤ r` and `‖QJQ‖ ≤ j` (as bilinear
forms on centred functions), then `‖Q(P - R)Q‖ ≤ 2M(r + 2j)/(1 + 2M) ≤ 2M(r + 2j)`. -/
theorem markov_completion_norm (mX : FiniteLaw X) (mY : FiniteLaw Y) (R J : X × Y → ℝ)
    (α : X → ℝ) (β : Y → ℝ) {M r j : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r) (hj : 0 ≤ j)
    (hα : ∀ x, |α x| ≤ M) (hβ : ∀ y, |β y| ≤ M)
    (hJ1 : ∀ x, mY.expect (fun y => J (x, y)) = 1) (hJ1' : ∀ y, mX.expect (fun x => J (x, y)) = 1)
    (hRr : ∀ φ ψ, mX.expect φ = 0 → mY.expect ψ = 0 →
      |kform mX mY R φ ψ| ≤ r * nrm mX φ * nrm mY ψ)
    (hJj : ∀ φ ψ, mX.expect φ = 0 → mY.expect ψ = 0 →
      |kform mX mY J φ ψ| ≤ j * nrm mX φ * nrm mY ψ)
    (φ : X → ℝ) (ψ : Y → ℝ) (hφ : mX.expect φ = 0) (hψ : mY.expect ψ = 0) :
    |kform mX mY (markovCompletion R J α β M) φ ψ - kform mX mY R φ ψ| ≤
      2 * M * (r + 2 * j) * nrm mX φ * nrm mY ψ := by
  have hpos : 0 < 1 + 2 * M := by linarith
  have hn1 : 0 ≤ nrm mX φ := Real.sqrt_nonneg _
  have hn2 : 0 ≤ nrm mY ψ := Real.sqrt_nonneg _
  -- the term with `α`
  have t1 : |kform mX mY J (fun x => α x * φ x) ψ| ≤ j * (M * nrm mX φ) * nrm mY ψ := by
    rw [kform_center_left mX mY J hJ1' _ ψ hψ]
    refine (hJj _ ψ (expect_center mX _) hψ).trans ?_
    apply mul_le_mul_of_nonneg_right _ hn2
    apply mul_le_mul_of_nonneg_left _ hj
    exact (nrm_center_le mX _).trans (nrm_mul_le mX α φ hM hα)
  -- the term with `β`
  have t2 : |kform mX mY J φ (fun y => β y * ψ y)| ≤ j * nrm mX φ * (M * nrm mY ψ) := by
    rw [kform_center_right mX mY J hJ1 φ _ hφ]
    refine (hJj φ _ hφ (expect_center mY _)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hj hn1)
    exact (nrm_center_le mY _).trans (nrm_mul_le mY β ψ hM hβ)
  have t3 := hJj φ ψ hφ hψ
  have t4 := hRr φ ψ hφ hψ
  have hid := kform_markovCompletion mX mY R J α β hM φ ψ
  have hbound : |(1 + 2 * M) * (kform mX mY (markovCompletion R J α β M) φ ψ -
      kform mX mY R φ ψ)| ≤ 2 * M * (r + 2 * j) * nrm mX φ * nrm mY ψ := by
    rw [hid]
    have a1 := abs_le.mp t1
    have a2 := abs_le.mp t2
    have a3 := abs_le.mp t3
    have a4 := abs_le.mp t4
    have hM3 : 0 ≤ 2 * M := by linarith
    have b3 := mul_le_mul_of_nonneg_left a3.2 hM3
    have b3' := mul_le_mul_of_nonneg_left a3.1 hM3
    have b4 := mul_le_mul_of_nonneg_left a4.2 hM3
    have b4' := mul_le_mul_of_nonneg_left a4.1 hM3
    rw [abs_le]
    constructor <;> nlinarith
  rw [abs_mul, abs_of_pos hpos] at hbound
  have hK : 0 ≤ 2 * M * (r + 2 * j) * nrm mX φ * nrm mY ψ := by positivity
  have h1 : 1 ≤ 1 + 2 * M := by linarith
  calc |kform mX mY (markovCompletion R J α β M) φ ψ - kform mX mY R φ ψ|
      ≤ (1 + 2 * M) * |kform mX mY (markovCompletion R J α β M) φ ψ - kform mX mY R φ ψ| := by
        nlinarith [abs_nonneg (kform mX mY (markovCompletion R J α β M) φ ψ -
          kform mX mY R φ ψ)]
    _ ≤ 2 * M * (r + 2 * j) * nrm mX φ * nrm mY ψ := hbound

/-- **`cor:markov-completion`, invariance**: if `σ_X`, `σ_Y` preserve `m_X`, `m_Y` and the
diagonal action preserves `R` and `J`, then the defects `α = 𝟙 - R𝟙`, `β = 𝟙 - R*𝟙` are
invariant, and so is `P`. One group element is treated at a time. -/
theorem markov_completion_invariant (mX : FiniteLaw X) (mY : FiniteLaw Y)
    (R J : X × Y → ℝ) (α : X → ℝ) (β : Y → ℝ) (M : ℝ)
    (hαdef : ∀ x, α x = 1 - mY.expect (fun y => R (x, y)))
    (hβdef : ∀ y, β y = 1 - mX.expect (fun x => R (x, y)))
    (σX : X ≃ X) (σY : Y ≃ Y)
    (hmX : ∀ φ : X → ℝ, mX.expect (fun x => φ (σX x)) = mX.expect φ)
    (hmY : ∀ φ : Y → ℝ, mY.expect (fun y => φ (σY y)) = mY.expect φ)
    (hR : ∀ x y, R (σX x, σY y) = R (x, y)) (hJ : ∀ x y, J (σX x, σY y) = J (x, y))
    (x : X) (y : Y) :
    markovCompletion R J α β M (σX x, σY y) = markovCompletion R J α β M (x, y) := by
  have hα : α (σX x) = α x := by
    rw [hαdef, hαdef, ← hmY (fun y => R (σX x, y))]
    simp only [hR]
  have hβ : β (σY y) = β y := by
    rw [hβdef, hβdef, ← hmX (fun x => R (x, σY y))]
    simp only [hR]
  unfold markovCompletion
  simp only [hR, hJ, hα, hβ]

end Sarkozy.Structured
