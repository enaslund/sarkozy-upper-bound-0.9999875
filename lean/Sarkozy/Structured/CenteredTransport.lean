module

public import Sarkozy.Structured.CenteredCorrection

/-!
# The centred operators of the corrected kernel (`lem:record:centered-correction`(b),(c))

`lem:record:centered-correction` (`paper/sections/17_completion_repair.tex`, brief F),
parts (b) and (c). Part (a) is `Sarkozy/Structured/CenteredCorrection.lean`. The setting:
* `K' = (1 + f(x) + g(y))K` has both half marginals `m = (1 + u₀)ν`, with
  `1 + u₀ ≥ e^{-ℓ_m}` and `‖u₀‖²_ν ≤ b₀`;
* the centred operator `𝒞_κ` on `L²(m)` is given by its form
  `⟨φ, 𝒞_κ ψ⟩_m = ∫∫ φ(x)ψ(y)κ(x,y) ν(dx)ν(dy) - E_m φ E_m ψ` (`centredForm`).

As in parts (a), operators are bilinear forms (`kform`). The symmetric and skew parts of
`𝒞` are the forms `(B(φ,ψ) ± B(ψ,φ))/2`. Norms on `L²(ν)` are bounds on `ν`-centred
functions; norms on `L²(m)` are bounds on all functions, with `‖φ‖_m` (`mnrm`).

The density transport is proved here directly. The paper cites
`lem:record:actual-correlation`(b) for it. A kernel whose rows and columns have `ν`-mean
zero sees only the centred parts of its arguments (`kform_center_left_zero`,
`kform_center_right_zero`), and `‖φ‖_ν ≤ e^{ℓ_m/2}‖φ‖_m` (`nrm_le_mnrm`). So a bound `C` on
`L²_0(ν)` becomes `e^{ℓ_m} C` on `L²(m)` (`kform_transport`).

* `centered_transport_identity`: (b)'s identity `K' - (1+u₀)⊗(1+u₀) = K_c + D - u₀⊗u₀`, on
  centred functions.
* `centered_transport_norms`: (b), the three bounds for `𝒞_{K'}`, its symmetric part and
  its skew part.
* `centered_transport_difference`: (c), the identity `K' - O = Π_⊥(K - O)Π_⊥ + D` on
  centred functions, and the bounds for the symmetric and skew parts of `𝒞_{K'} - 𝒞_O`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

open Sarkozy.Recentering

variable {X : Type*} [Fintype X]

/-- `‖φ‖_m = (E_ν[(1 + u₀)φ²])^{1/2}` for `m = (1 + u₀)ν`. -/
noncomputable def mnrm (ν : FiniteLaw X) (u0 : X → ℝ) (φ : X → ℝ) : ℝ :=
  Real.sqrt (ν.expect (fun x => (1 + u0 x) * φ x ^ 2))

/-- `E_m φ = E_ν[(1 + u₀)φ]`. -/
noncomputable def mexp (ν : FiniteLaw X) (u0 : X → ℝ) (φ : X → ℝ) : ℝ :=
  ν.expect (fun x => (1 + u0 x) * φ x)

/-- The form of the centred operator `𝒞_κ` on `L²(m)`:
`⟨φ, 𝒞_κ ψ⟩_m = ∫∫ φψκ d(ν⊗ν) - E_m φ E_m ψ`. -/
noncomputable def centredForm (ν : FiniteLaw X) (u0 : X → ℝ) (κ : X × X → ℝ)
    (φ ψ : X → ℝ) : ℝ :=
  kform ν ν κ φ ψ - mexp ν u0 φ * mexp ν u0 ψ

/-- The form of a rank-one kernel `a ⊗ b`. -/
theorem kform_rank_one (ν : FiniteLaw X) (a b φ ψ : X → ℝ) :
    kform ν ν (fun p => a p.1 * b p.2) φ ψ =
      ν.expect (fun x => φ x * a x) * ν.expect (fun y => ψ y * b y) := by
  unfold kform
  rw [← ν.expect_mul_const]
  exact ν.expect_congr fun x => by
    rw [← ν.expect_const_mul]; exact ν.expect_congr fun y => by ring

/-- The transposed kernel has the transposed form. -/
theorem kform_transpose (ν : FiniteLaw X) (κ : X × X → ℝ) (φ ψ : X → ℝ) :
    kform ν ν (fun p => κ (p.2, p.1)) φ ψ = kform ν ν κ ψ φ := by
  unfold kform
  rw [expect_swap ν (fun x y => φ x * ψ y * κ (y, x))]
  exact ν.expect_congr fun y => ν.expect_congr fun x => by ring

/-- On centred functions, `K` and `K_c` have the same form (`K` has mass one). -/
theorem kform_eq_centeredKernel (ν : FiniteLaw X) (K : X × X → ℝ) (φ ψ : X → ℝ)
    (hφ : ν.expect φ = 0) (hψ : ν.expect ψ = 0) :
    kform ν ν K φ ψ = kform ν ν (centeredKernel ν K) φ ψ := by
  have e : ∀ p : X × X, K p = centeredKernel ν K p + (1 + deltaL ν K p.1) * 1 +
      1 * deltaR ν K p.2 := by
    intro p; unfold centeredKernel; ring
  rw [kform_congr ν ν e, kform_add, kform_add,
    kform_rank_one ν (fun x => 1 + deltaL ν K x) (fun _ => 1),
    kform_rank_one ν (fun _ => 1) (deltaR ν K)]
  have h1 : ν.expect (fun y => ψ y * (1 : ℝ)) = 0 := by
    rw [show (fun y => ψ y * (1 : ℝ)) = ψ from funext fun y => mul_one _, hψ]
  have h2 : ν.expect (fun x => φ x * (1 : ℝ)) = 0 := by
    rw [show (fun x => φ x * (1 : ℝ)) = φ from funext fun x => mul_one _, hφ]
  rw [h1, h2]
  ring

/-- `E_m φ = E_ν[u₀φ]` for `ν`-centred `φ`. -/
theorem mexp_of_centred (ν : FiniteLaw X) (u0 φ : X → ℝ) (hφ : ν.expect φ = 0) :
    mexp ν u0 φ = ν.expect (fun x => u0 x * φ x) := by
  unfold mexp
  have : (fun x => (1 + u0 x) * φ x) = fun x => φ x + u0 x * φ x := by funext x; ring
  rw [this, ν.expect_add, hφ, zero_add]

/-- `‖φ‖_ν ≤ e^{ℓ/2}‖φ‖_m` when `1 + u₀ ≥ e^{-ℓ}`. -/
theorem nrm_le_mnrm (ν : FiniteLaw X) (u0 : X → ℝ) {ℓ : ℝ}
    (hu : ∀ x, Real.exp (-ℓ) ≤ 1 + u0 x) (φ : X → ℝ) :
    nrm ν φ ≤ Real.sqrt (Real.exp ℓ) * mnrm ν u0 φ := by
  unfold nrm ip mnrm
  rw [← Real.sqrt_mul (Real.exp_pos ℓ).le]
  apply Real.sqrt_le_sqrt
  rw [← ν.expect_const_mul]
  apply ν.expect_mono
  intro x
  have h1 : 1 ≤ Real.exp ℓ * (1 + u0 x) := by
    have := mul_le_mul_of_nonneg_left (hu x) (Real.exp_pos ℓ).le
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
  nlinarith [sq_nonneg (φ x)]

/-- **The density transport**: a kernel whose rows and columns have `ν`-mean zero, with norm
at most `C` on `L²_0(ν)`, has norm at most `e^ℓ C` on `L²(m)` when `1 + u₀ ≥ e^{-ℓ}`. -/
theorem kform_transport (ν : FiniteLaw X) (u0 : X → ℝ) {ℓ C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ x, Real.exp (-ℓ) ≤ 1 + u0 x) (κ : X × X → ℝ)
    (hrow : ∀ x, ν.expect (fun y => κ (x, y)) = 0) (hcol : ∀ y, ν.expect (fun x => κ (x, y)) = 0)
    (hκ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |kform ν ν κ φ ψ| ≤ C * nrm ν φ * nrm ν ψ)
    (φ ψ : X → ℝ) :
    |kform ν ν κ φ ψ| ≤ Real.exp ℓ * C * mnrm ν u0 φ * mnrm ν u0 ψ := by
  rw [kform_center_left_zero ν κ hcol, kform_center_right_zero ν κ hrow]
  refine (hκ _ _ (expect_center ν φ) (expect_center ν ψ)).trans ?_
  have h1 := (nrm_center_le ν φ).trans (nrm_le_mnrm ν u0 hu φ)
  have h2 := (nrm_center_le ν ψ).trans (nrm_le_mnrm ν u0 hu ψ)
  have hs : Real.sqrt (Real.exp ℓ) * Real.sqrt (Real.exp ℓ) = Real.exp ℓ :=
    Real.mul_self_sqrt (Real.exp_pos ℓ).le
  have hn1 : 0 ≤ nrm ν (center ν φ) := Real.sqrt_nonneg _
  have hn2 : 0 ≤ nrm ν (center ν ψ) := Real.sqrt_nonneg _
  calc C * nrm ν (center ν φ) * nrm ν (center ν ψ) ≤
        C * (Real.sqrt (Real.exp ℓ) * mnrm ν u0 φ) * (Real.sqrt (Real.exp ℓ) * mnrm ν u0 ψ) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) h2 hn2
        exact mul_nonneg hC ((Real.sqrt_nonneg _).trans h1)
    _ = (Real.sqrt (Real.exp ℓ) * Real.sqrt (Real.exp ℓ)) * C * mnrm ν u0 φ * mnrm ν u0 ψ := by
        ring
    _ = Real.exp ℓ * C * mnrm ν u0 φ * mnrm ν u0 ψ := by rw [hs]

/-- A kernel with both half marginals `m = (1 + u₀)ν`, minus `(1+u₀)⊗(1+u₀)`, has rows and
columns of mean zero (`E_ν u₀ = 0`). -/
theorem marginal_kernel_rows (ν : FiniteLaw X) (u0 : X → ℝ) (hu00 : ν.expect u0 = 0)
    (κ : X × X → ℝ) (hm1 : ∀ x, ν.expect (fun y => κ (x, y)) = 1 + u0 x)
    (hm2 : ∀ y, ν.expect (fun x => κ (x, y)) = 1 + u0 y) :
    (∀ x, ν.expect (fun y => κ (x, y) - (1 + u0 x) * (1 + u0 y)) = 0) ∧
      (∀ y, ν.expect (fun x => κ (x, y) - (1 + u0 x) * (1 + u0 y)) = 0) := by
  have hE : ν.expect (fun y => 1 + u0 y) = 1 := by
    rw [ν.expect_add, ν.expect_const, hu00, add_zero]
  constructor
  · intro x
    rw [ν.expect_sub, hm1, ν.expect_const_mul, hE, mul_one, sub_self]
  · intro y
    rw [ν.expect_sub, hm2, ν.expect_mul_const, hE, one_mul, sub_self]

/-- `𝒞_κ` is the form of `κ - (1+u₀)⊗(1+u₀)`. -/
theorem centredForm_eq_kform (ν : FiniteLaw X) (u0 : X → ℝ) (κ : X × X → ℝ) (φ ψ : X → ℝ) :
    centredForm ν u0 κ φ ψ =
      kform ν ν (fun p => κ p - (1 + u0 p.1) * (1 + u0 p.2)) φ ψ := by
  unfold centredForm mexp
  rw [kform_sub, kform_rank_one ν (fun x => 1 + u0 x) (fun y => 1 + u0 y)]
  congr 2
  · exact ν.expect_congr fun x => mul_comm _ _
  · exact ν.expect_congr fun y => mul_comm _ _

/-- **(b), the identity**: on `ν`-centred functions,
`K' - (1+u₀)⊗(1+u₀) = K_c + D - u₀⊗u₀`, with `D` the form of `(f(x) + g(y))K`. -/
theorem centered_transport_identity (ν : FiniteLaw X) (K : X × X → ℝ) (f g u0 : X → ℝ)
    (φ ψ : X → ℝ) (hφ : ν.expect φ = 0) (hψ : ν.expect ψ = 0) :
    centredForm ν u0 (fun p => (1 + f p.1 + g p.2) * K p) φ ψ =
      kform ν ν (centeredKernel ν K) φ ψ + kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ -
        ν.expect (fun x => u0 x * φ x) * ν.expect (fun y => u0 y * ψ y) := by
  unfold centredForm
  rw [mexp_of_centred ν u0 φ hφ, mexp_of_centred ν u0 ψ hψ]
  have e : ∀ p : X × X, (1 + f p.1 + g p.2) * K p = K p + (f p.1 + g p.2) * K p := by
    intro p; ring
  rw [kform_congr ν ν e, kform_add, kform_eq_centeredKernel ν K φ ψ hφ hψ]

/-- The symmetric and antisymmetric parts of a form. -/
theorem kform_sym (ν : FiniteLaw X) (κ : X × X → ℝ) (σ : ℝ) (φ ψ : X → ℝ) :
    kform ν ν (fun p => (κ p + σ * κ (p.2, p.1)) / 2) φ ψ =
      (kform ν ν κ φ ψ + σ * kform ν ν κ ψ φ) / 2 := by
  have e : ∀ p : X × X, (κ p + σ * κ (p.2, p.1)) / 2 =
      (fun p : X × X => (1 / 2 : ℝ) * κ p) p +
        (fun p : X × X => (σ / 2) * (fun q : X × X => κ (q.2, q.1)) p) p := by
    intro p; ring
  rw [kform_congr ν ν e, kform_add, kform_const_mul, kform_const_mul, kform_transpose]
  ring

/-- The rows and columns of `(κ + σκᵀ)/2` have mean zero if those of `κ` do. -/
theorem sym_rows (ν : FiniteLaw X) (κ : X × X → ℝ) (σ : ℝ)
    (hrow : ∀ x, ν.expect (fun y => κ (x, y)) = 0) (hcol : ∀ y, ν.expect (fun x => κ (x, y)) = 0) :
    (∀ x, ν.expect (fun y => (κ (x, y) + σ * κ (y, x)) / 2) = 0) ∧
      (∀ y, ν.expect (fun x => (κ (x, y) + σ * κ (y, x)) / 2) = 0) := by
  constructor
  · intro x
    have : (fun y => (κ (x, y) + σ * κ (y, x)) / 2) =
        fun y => (1 / 2 : ℝ) * κ (x, y) + (σ / 2) * κ (y, x) := by funext y; ring
    rw [this, ν.expect_add, ν.expect_const_mul, ν.expect_const_mul, hrow x, hcol x]
    ring
  · intro y
    have : (fun x => (κ (x, y) + σ * κ (y, x)) / 2) =
        fun x => (1 / 2 : ℝ) * κ (x, y) + (σ / 2) * κ (y, x) := by funext x; ring
    rw [this, ν.expect_add, ν.expect_const_mul, ν.expect_const_mul, hcol y, hrow y]
    ring

/-- The bound `2F(c + e)` of (a) for `D(φ,ψ) ± D(ψ,φ)`, halved. -/
theorem centered_correction_sym (ν : FiniteLaw X) (K : X × X → ℝ)
    (hK : ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1) {c e F : ℝ} (hc : 0 ≤ c)
    (hF : 0 ≤ F)
    (hKc : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |kform ν ν (centeredKernel ν K) φ ψ| ≤ c * nrm ν φ * nrm ν ψ)
    (hδL : nrm ν (deltaL ν K) ≤ e) (hδR : nrm ν (deltaR ν K) ≤ e)
    (f g : X → ℝ) (hf : ∀ x, |f x| ≤ F) (hg : ∀ y, |g y| ≤ F) {σ : ℝ} (hσ : |σ| ≤ 1)
    (φ ψ : X → ℝ) (hφ : ν.expect φ = 0) (hψ : ν.expect ψ = 0) :
    |(kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ +
        σ * kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ) / 2| ≤
      2 * F * (c + e) * nrm ν φ * nrm ν ψ := by
  have h1 := centered_correction_norm ν K hK hc hF hKc hδL hδR f g hf hg φ ψ hφ hψ
  have h2 := centered_correction_norm ν K hK hc hF hKc hδL hδR f g hf hg ψ φ hψ hφ
  have hB : 0 ≤ 2 * F * (c + e) * nrm ν φ * nrm ν ψ := by
    have he : 0 ≤ e := (Real.sqrt_nonneg _).trans hδL
    have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hF)
      (add_nonneg hc he)) (Real.sqrt_nonneg (ip ν φ φ))) (Real.sqrt_nonneg (ip ν ψ ψ))
    exact this
  rw [abs_div, abs_two]
  have h3 : |σ * kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ| ≤
      2 * F * (c + e) * nrm ν φ * nrm ν ψ := by
    rw [abs_mul]
    calc |σ| * |kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ| ≤
          1 * (2 * F * (c + e) * nrm ν ψ * nrm ν φ) :=
          mul_le_mul hσ h2 (abs_nonneg _) zero_le_one
      _ = 2 * F * (c + e) * nrm ν φ * nrm ν ψ := by ring
  have h4 := abs_add_le (kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ)
    (σ * kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ)
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- The form of `K' - (1+u₀)⊗(1+u₀)` on centred functions: `K_c + D - u₀⊗u₀`. -/
theorem transport_kernel_centred (ν : FiniteLaw X) (K K' : X × X → ℝ) (f g u0 : X → ℝ)
    (hK' : ∀ p, K' p = (1 + f p.1 + g p.2) * K p) (φ ψ : X → ℝ) (hφ : ν.expect φ = 0)
    (hψ : ν.expect ψ = 0) :
    kform ν ν (fun p => K' p - (1 + u0 p.1) * (1 + u0 p.2)) φ ψ =
      kform ν ν (centeredKernel ν K) φ ψ + kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ -
        ν.expect (fun x => u0 x * φ x) * ν.expect (fun y => u0 y * ψ y) := by
  rw [← centredForm_eq_kform, ← centered_transport_identity ν K f g u0 φ ψ hφ hψ]
  unfold centredForm
  rw [kform_congr ν ν hK']

/-- **`lem:record:centered-correction`(b)**: let `K'` have both half marginals
`m = (1 + u₀)ν`, with `E_ν u₀ = 0` (given the marginals, this is the paper's "`K'` has mass
one"), `1 + u₀ ≥ e^{-ℓ}` and `‖u₀‖²_ν ≤ b₀`. Let `‖K_c‖ ≤ c`,
`‖Sym K_c‖ ≤ s`, `‖Skew K_c‖ ≤ a`, `‖δ_L‖, ‖δ_R‖ ≤ e` and `|f|, |g| ≤ F`. Then on `L²(m)`
`‖𝒞_{K'}‖ ≤ e^ℓ(c + 2F(c+e) + b₀)`, `‖Sym 𝒞_{K'}‖ ≤ e^ℓ(s + 2F(c+e) + b₀)` and
`‖Skew 𝒞_{K'}‖ ≤ e^ℓ(a + 2F(c+e))`. -/
theorem centered_transport_norms (ν : FiniteLaw X) (K K' : X × X → ℝ)
    (hK : ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1) {c s a e F b0 ℓ : ℝ}
    (hc : 0 ≤ c) (hs : 0 ≤ s) (ha : 0 ≤ a) (hF : 0 ≤ F)
    (hKc : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |kform ν ν (centeredKernel ν K) φ ψ| ≤ c * nrm ν φ * nrm ν ψ)
    (hKs : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |(kform ν ν (centeredKernel ν K) φ ψ + kform ν ν (centeredKernel ν K) ψ φ) / 2| ≤
        s * nrm ν φ * nrm ν ψ)
    (hKa : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |(kform ν ν (centeredKernel ν K) φ ψ - kform ν ν (centeredKernel ν K) ψ φ) / 2| ≤
        a * nrm ν φ * nrm ν ψ)
    (hδL : nrm ν (deltaL ν K) ≤ e) (hδR : nrm ν (deltaR ν K) ≤ e)
    (f g : X → ℝ) (hf : ∀ x, |f x| ≤ F) (hg : ∀ y, |g y| ≤ F)
    (hK' : ∀ p, K' p = (1 + f p.1 + g p.2) * K p)
    (u0 : X → ℝ) (hu00 : ν.expect u0 = 0)
    (hm1 : ∀ x, ν.expect (fun y => K' (x, y)) = 1 + u0 x)
    (hm2 : ∀ y, ν.expect (fun x => K' (x, y)) = 1 + u0 y)
    (hu : ∀ x, Real.exp (-ℓ) ≤ 1 + u0 x) (hb : nrm ν u0 ^ 2 ≤ b0) (φ ψ : X → ℝ) :
    |centredForm ν u0 K' φ ψ| ≤
        Real.exp ℓ * (c + 2 * F * (c + e) + b0) * mnrm ν u0 φ * mnrm ν u0 ψ ∧
      |(centredForm ν u0 K' φ ψ + centredForm ν u0 K' ψ φ) / 2| ≤
        Real.exp ℓ * (s + 2 * F * (c + e) + b0) * mnrm ν u0 φ * mnrm ν u0 ψ ∧
      |(centredForm ν u0 K' φ ψ - centredForm ν u0 K' ψ φ) / 2| ≤
        Real.exp ℓ * (a + 2 * F * (c + e)) * mnrm ν u0 φ * mnrm ν u0 ψ := by
  set Xk : X × X → ℝ := fun p => K' p - (1 + u0 p.1) * (1 + u0 p.2) with hXk
  obtain ⟨hrow, hcol⟩ := marginal_kernel_rows ν u0 hu00 K' hm1 hm2
  have he : 0 ≤ e := (Real.sqrt_nonneg _).trans hδL
  have hb0 : 0 ≤ b0 := (sq_nonneg _).trans hb
  have hD : 0 ≤ 2 * F * (c + e) := mul_nonneg (mul_nonneg (by norm_num) hF) (add_nonneg hc he)
  -- the `u₀ ⊗ u₀` term
  have huu : ∀ φ ψ : X → ℝ, |ν.expect (fun x => u0 x * φ x) * ν.expect (fun y => u0 y * ψ y)| ≤
      b0 * nrm ν φ * nrm ν ψ := by
    intro φ ψ
    rw [abs_mul]
    have h1 : |ν.expect (fun x => u0 x * φ x)| ≤ nrm ν u0 * nrm ν φ := abs_ip_le ν u0 φ
    have h2 : |ν.expect (fun y => u0 y * ψ y)| ≤ nrm ν u0 * nrm ν ψ := abs_ip_le ν u0 ψ
    have hn0 : 0 ≤ nrm ν u0 := Real.sqrt_nonneg _
    calc |ν.expect (fun x => u0 x * φ x)| * |ν.expect (fun y => u0 y * ψ y)| ≤
          (nrm ν u0 * nrm ν φ) * (nrm ν u0 * nrm ν ψ) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hn0 (Real.sqrt_nonneg _))
      _ = nrm ν u0 ^ 2 * nrm ν φ * nrm ν ψ := by ring
      _ ≤ b0 * nrm ν φ * nrm ν ψ := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _)
  have hcent := fun φ ψ hφ hψ => transport_kernel_centred ν K K' f g u0 hK' φ ψ hφ hψ
  have hDb := fun φ ψ hφ hψ =>
    centered_correction_norm ν K hK hc hF hKc hδL hδR f g hf hg φ ψ hφ hψ
  refine ⟨?_, ?_, ?_⟩
  · -- the full norm
    rw [centredForm_eq_kform]
    refine kform_transport ν u0 (add_nonneg (add_nonneg hc hD) hb0) hu Xk hrow hcol ?_ φ ψ
    intro φ ψ hφ hψ
    rw [hcent φ ψ hφ hψ]
    have h1 := hKc φ ψ hφ hψ
    have h2 := hDb φ ψ hφ hψ
    have h3 := huu φ ψ
    have t := abs_sub (kform ν ν (centeredKernel ν K) φ ψ +
      kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ)
      (ν.expect (fun x => u0 x * φ x) * ν.expect (fun y => u0 y * ψ y))
    have t2 := abs_add_le (kform ν ν (centeredKernel ν K) φ ψ)
      (kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ)
    nlinarith
  · -- the symmetric part
    have hsym := sym_rows ν Xk 1 hrow hcol
    have hform : (centredForm ν u0 K' φ ψ + centredForm ν u0 K' ψ φ) / 2 =
        kform ν ν (fun p => (Xk p + 1 * Xk (p.2, p.1)) / 2) φ ψ := by
      rw [kform_sym, centredForm_eq_kform, centredForm_eq_kform, one_mul]
    rw [hform]
    refine kform_transport ν u0 (add_nonneg (add_nonneg hs hD) hb0) hu _ hsym.1 hsym.2 ?_ φ ψ
    intro φ ψ hφ hψ
    rw [kform_sym, one_mul, hcent φ ψ hφ hψ, hcent ψ φ hψ hφ]
    have h1 := hKs φ ψ hφ hψ
    have h2 := centered_correction_sym ν K hK hc hF hKc hδL hδR f g hf hg
      (σ := 1) (by norm_num) φ ψ hφ hψ
    have h3 := huu φ ψ
    have e1 : (kform ν ν (centeredKernel ν K) φ ψ + kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ -
        ν.expect (fun x => u0 x * φ x) * ν.expect (fun y => u0 y * ψ y) +
        (kform ν ν (centeredKernel ν K) ψ φ + kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ -
        ν.expect (fun x => u0 x * ψ x) * ν.expect (fun y => u0 y * φ y))) / 2 =
        (kform ν ν (centeredKernel ν K) φ ψ + kform ν ν (centeredKernel ν K) ψ φ) / 2 +
        (kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ +
          1 * kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ) / 2 -
        ν.expect (fun x => u0 x * φ x) * ν.expect (fun y => u0 y * ψ y) := by ring
    rw [e1]
    have t := abs_sub
      ((kform ν ν (centeredKernel ν K) φ ψ + kform ν ν (centeredKernel ν K) ψ φ) / 2 +
        (kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ +
          1 * kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ) / 2)
      (ν.expect (fun x => u0 x * φ x) * ν.expect (fun y => u0 y * ψ y))
    have t2 := abs_add_le
      ((kform ν ν (centeredKernel ν K) φ ψ + kform ν ν (centeredKernel ν K) ψ φ) / 2)
      ((kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ +
          1 * kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ) / 2)
    nlinarith
  · -- the skew part
    have hsk := sym_rows ν Xk (-1) hrow hcol
    have hform : (centredForm ν u0 K' φ ψ - centredForm ν u0 K' ψ φ) / 2 =
        kform ν ν (fun p => (Xk p + (-1) * Xk (p.2, p.1)) / 2) φ ψ := by
      rw [kform_sym, centredForm_eq_kform, centredForm_eq_kform]
      ring
    rw [hform]
    refine kform_transport ν u0 (add_nonneg ha hD) hu _ hsk.1 hsk.2 ?_ φ ψ
    intro φ ψ hφ hψ
    rw [kform_sym, hcent φ ψ hφ hψ, hcent ψ φ hψ hφ]
    have h1 := hKa φ ψ hφ hψ
    have h2 := centered_correction_sym ν K hK hc hF hKc hδL hδR f g hf hg
      (σ := -1) (by norm_num) φ ψ hφ hψ
    have e1 : (kform ν ν (centeredKernel ν K) φ ψ + kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ -
        ν.expect (fun x => u0 x * φ x) * ν.expect (fun y => u0 y * ψ y) +
        (-1) * (kform ν ν (centeredKernel ν K) ψ φ +
          kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ -
        ν.expect (fun x => u0 x * ψ x) * ν.expect (fun y => u0 y * φ y))) / 2 =
        (kform ν ν (centeredKernel ν K) φ ψ - kform ν ν (centeredKernel ν K) ψ φ) / 2 +
        (kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ +
          (-1) * kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ) / 2 := by ring
    rw [e1]
    have t2 := abs_add_le
      ((kform ν ν (centeredKernel ν K) φ ψ - kform ν ν (centeredKernel ν K) ψ φ) / 2)
      ((kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ +
          (-1) * kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ) / 2)
    nlinarith

/-- **`lem:record:centered-correction`(c)**: let `O` be a kernel with the same half marginals
`m` as `K'`. Then `K' - O = (K - O) + D` (on centred functions the form of `K - O` is that of
`Π_⊥(K - O)Π_⊥`), and the symmetric and skew parts of `𝒞_{K'} - 𝒞_O` have norms on `L²(m)`
at most `e^ℓ(s_O + 2F(c+e))` and `e^ℓ(a_O + 2F(c+e))`, where `s_O`, `a_O` bound the symmetric
and skew parts of `Π_⊥(K - O)Π_⊥`. There is no marginal-variance term. -/
theorem centered_transport_difference (ν : FiniteLaw X) (K K' O : X × X → ℝ)
    (hK : ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1) {c e F sO aO ℓ : ℝ}
    (hc : 0 ≤ c) (hF : 0 ≤ F) (hsO : 0 ≤ sO) (haO : 0 ≤ aO)
    (hKc : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |kform ν ν (centeredKernel ν K) φ ψ| ≤ c * nrm ν φ * nrm ν ψ)
    (hδL : nrm ν (deltaL ν K) ≤ e) (hδR : nrm ν (deltaR ν K) ≤ e)
    (f g : X → ℝ) (hf : ∀ x, |f x| ≤ F) (hg : ∀ y, |g y| ≤ F)
    (hK' : ∀ p, K' p = (1 + f p.1 + g p.2) * K p) (u0 : X → ℝ)
    (hm1 : ∀ x, ν.expect (fun y => K' (x, y)) = 1 + u0 x)
    (hm2 : ∀ y, ν.expect (fun x => K' (x, y)) = 1 + u0 y)
    (hO1 : ∀ x, ν.expect (fun y => O (x, y)) = 1 + u0 x)
    (hO2 : ∀ y, ν.expect (fun x => O (x, y)) = 1 + u0 y)
    (hu : ∀ x, Real.exp (-ℓ) ≤ 1 + u0 x)
    (hKOs : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |(kform ν ν (fun p => K p - O p) φ ψ + kform ν ν (fun p => K p - O p) ψ φ) / 2| ≤
        sO * nrm ν φ * nrm ν ψ)
    (hKOa : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |(kform ν ν (fun p => K p - O p) φ ψ - kform ν ν (fun p => K p - O p) ψ φ) / 2| ≤
        aO * nrm ν φ * nrm ν ψ)
    (φ ψ : X → ℝ) :
    kform ν ν (fun p => K' p - O p) φ ψ =
        kform ν ν (fun p => K p - O p) φ ψ + kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ ∧
      |((centredForm ν u0 K' φ ψ - centredForm ν u0 O φ ψ) +
          (centredForm ν u0 K' ψ φ - centredForm ν u0 O ψ φ)) / 2| ≤
        Real.exp ℓ * (sO + 2 * F * (c + e)) * mnrm ν u0 φ * mnrm ν u0 ψ ∧
      |((centredForm ν u0 K' φ ψ - centredForm ν u0 O φ ψ) -
          (centredForm ν u0 K' ψ φ - centredForm ν u0 O ψ φ)) / 2| ≤
        Real.exp ℓ * (aO + 2 * F * (c + e)) * mnrm ν u0 φ * mnrm ν u0 ψ := by
  set Yk : X × X → ℝ := fun p => K' p - O p with hYk
  have he : 0 ≤ e := (Real.sqrt_nonneg _).trans hδL
  have hD : 0 ≤ 2 * F * (c + e) := mul_nonneg (mul_nonneg (by norm_num) hF) (add_nonneg hc he)
  have hrow : ∀ x, ν.expect (fun y => Yk (x, y)) = 0 := by
    intro x
    rw [hYk, ν.expect_sub, hm1, hO1, sub_self]
  have hcol : ∀ y, ν.expect (fun x => Yk (x, y)) = 0 := by
    intro y
    rw [hYk, ν.expect_sub, hm2, hO2, sub_self]
  have hid : ∀ φ ψ : X → ℝ, kform ν ν Yk φ ψ =
      kform ν ν (fun p => K p - O p) φ ψ + kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ := by
    intro φ ψ
    have e1 : ∀ p : X × X, Yk p = (K p - O p) + (f p.1 + g p.2) * K p := by
      intro p
      rw [hYk]
      dsimp only
      rw [hK' p]
      ring
    rw [kform_congr ν ν e1, kform_add]
  have hdiff : ∀ φ ψ : X → ℝ, centredForm ν u0 K' φ ψ - centredForm ν u0 O φ ψ =
      kform ν ν Yk φ ψ := by
    intro φ ψ
    unfold centredForm
    rw [hYk, kform_sub]
    ring
  refine ⟨hid φ ψ, ?_, ?_⟩
  · have hsym := sym_rows ν Yk 1 hrow hcol
    have hform : ((centredForm ν u0 K' φ ψ - centredForm ν u0 O φ ψ) +
        (centredForm ν u0 K' ψ φ - centredForm ν u0 O ψ φ)) / 2 =
        kform ν ν (fun p => (Yk p + 1 * Yk (p.2, p.1)) / 2) φ ψ := by
      rw [kform_sym, hdiff, hdiff, one_mul]
    rw [hform]
    refine kform_transport ν u0 (add_nonneg hsO hD) hu _ hsym.1 hsym.2 ?_ φ ψ
    intro φ ψ hφ hψ
    rw [kform_sym, hid, hid]
    have h1 := hKOs φ ψ hφ hψ
    have h2 := centered_correction_sym ν K hK hc hF hKc hδL hδR f g hf hg
      (σ := 1) (by norm_num) φ ψ hφ hψ
    have e1 : (kform ν ν (fun p => K p - O p) φ ψ + kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ +
        1 * (kform ν ν (fun p => K p - O p) ψ φ +
          kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ)) / 2 =
        (kform ν ν (fun p => K p - O p) φ ψ + kform ν ν (fun p => K p - O p) ψ φ) / 2 +
        (kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ +
          1 * kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ) / 2 := by ring
    rw [e1]
    have t2 := abs_add_le
      ((kform ν ν (fun p => K p - O p) φ ψ + kform ν ν (fun p => K p - O p) ψ φ) / 2)
      ((kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ +
          1 * kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ) / 2)
    nlinarith
  · have hsk := sym_rows ν Yk (-1) hrow hcol
    have hform : ((centredForm ν u0 K' φ ψ - centredForm ν u0 O φ ψ) -
        (centredForm ν u0 K' ψ φ - centredForm ν u0 O ψ φ)) / 2 =
        kform ν ν (fun p => (Yk p + (-1) * Yk (p.2, p.1)) / 2) φ ψ := by
      rw [kform_sym, hdiff, hdiff]
      ring
    rw [hform]
    refine kform_transport ν u0 (add_nonneg haO hD) hu _ hsk.1 hsk.2 ?_ φ ψ
    intro φ ψ hφ hψ
    rw [kform_sym, hid, hid]
    have h1 := hKOa φ ψ hφ hψ
    have h2 := centered_correction_sym ν K hK hc hF hKc hδL hδR f g hf hg
      (σ := -1) (by norm_num) φ ψ hφ hψ
    have e1 : (kform ν ν (fun p => K p - O p) φ ψ + kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ +
        (-1) * (kform ν ν (fun p => K p - O p) ψ φ +
          kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ)) / 2 =
        (kform ν ν (fun p => K p - O p) φ ψ - kform ν ν (fun p => K p - O p) ψ φ) / 2 +
        (kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ +
          (-1) * kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ) / 2 := by ring
    rw [e1]
    have t2 := abs_add_le
      ((kform ν ν (fun p => K p - O p) φ ψ - kform ν ν (fun p => K p - O p) ψ φ) / 2)
      ((kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ +
          (-1) * kform ν ν (fun p => (f p.1 + g p.2) * K p) ψ φ) / 2)
    nlinarith

end Sarkozy.Structured
