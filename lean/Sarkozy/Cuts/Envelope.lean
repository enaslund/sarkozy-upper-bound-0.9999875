module

public import Sarkozy.Cuts.Tilt

/-!
# Cuts, VII: from mean-zero bounds to operator bounds

`13_cuts_correlations.tex`, `subsec:cuts:blocks`.

* `block_lower_scalar`, `block_upper_scalar`, `block_completion_lower`,
  `block_completion_upper`: `lem:block-completion` (b). Here
  `T = [[A, B*], [B, D]]` on `H₁ ⊕ H₂` enters through its quadratic form
  `⟨(x,y), T(x,y)⟩ = ⟨x, Ax⟩ + 2⟨y, Bx⟩ + ⟨y, Dy⟩`.
* `envelope_upper`, `envelope_lower`: `prop:matching:positive` (a), (a′).
* `normalized_kernel`: `prop:matching:positive` (b).
* `threshold_factor`, `envelope_threshold`: `prop:matching:positive` (c).

A self-adjoint operator `A` on `L²(ν)` is given by its symmetric bilinear form `𝔞`. Then
`⟨1, A1⟩ = 𝔞(1, 1)`. The bound `‖P₀A1‖ ≤ e` is `|𝔞(f, 1)| ≤ e‖f‖` for centred `f`, and
`P₀AP₀ ⪯ βP₀` is `𝔞(f, f) ≤ β‖f‖²` for centred `f`.

Part (a″) of `prop:matching:positive` (translation sectors) is in `Sarkozy.Cuts.Sectors`, and
part (a) of `lem:block-completion` (the Schur complement) is in `Sarkozy.Cuts.BlockSchur`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering

/-! ### `lem:block-completion` (b) -/

/-- The scalar core of `lem:block-completion` (b), lower bound. -/
theorem block_lower_scalar {a d b X Y qA qD c : ℝ} (had : d < a) (hA : a * X ^ 2 ≤ qA)
    (hD : d * Y ^ 2 ≤ qD) (hc : |c| ≤ b * X * Y) :
    (d - b ^ 2 / (a - d)) * (X ^ 2 + Y ^ 2) ≤ qA + 2 * c + qD := by
  have hα : 0 < a - d := by linarith
  set α := a - d with hα_def
  have hc' : -(b * X * Y) ≤ c := by linarith [neg_abs_le c]
  have key : 0 ≤ (α + b ^ 2 / α) * X ^ 2 - 2 * (b * X * Y) + b ^ 2 / α * Y ^ 2 := by
    have e : (α + b ^ 2 / α) * X ^ 2 - 2 * (b * X * Y) + b ^ 2 / α * Y ^ 2 =
        ((α * X - b * Y) ^ 2 + b ^ 2 * X ^ 2) / α := by
      field_simp
      ring
    rw [e]
    positivity
  have e2 : (d - b ^ 2 / α) * (X ^ 2 + Y ^ 2) = a * X ^ 2 + d * Y ^ 2 -
      ((α + b ^ 2 / α) * X ^ 2 - 2 * (b * X * Y) + b ^ 2 / α * Y ^ 2) - 2 * (b * X * Y) := by
    rw [hα_def]
    ring
  rw [e2]
  linarith

/-- The scalar core of `lem:block-completion` (b), upper bound. -/
theorem block_upper_scalar {a d b X Y qA qD c : ℝ} (had : d < a) (hA : qA ≤ a * X ^ 2)
    (hD : qD ≤ d * Y ^ 2) (hc : |c| ≤ b * X * Y) :
    qA + 2 * c + qD ≤ (a + b ^ 2 / (a - d)) * (X ^ 2 + Y ^ 2) := by
  have h := block_lower_scalar (a := -d) (d := -a) (b := b) (X := Y) (Y := X) (qA := -qD)
    (qD := -qA) (c := -c) (by linarith) (by linarith) (by linarith)
    (by rw [abs_neg]; linarith)
  have e : -a - b ^ 2 / (-d - -a) = -(a + b ^ 2 / (a - d)) := by
    rw [show -d - -a = a - d by ring]
    ring
  rw [e] at h
  nlinarith

section InnerProduct

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]

/-- **`lem:block-completion` (b), lower bound.** If `A ⪰ aI`, `D ⪰ dI`, `‖B‖ ≤ b` and `a > d`,
then `T ⪰ (d - b²/(a - d)) I`, in the form
`⟨x, Ax⟩ + 2⟨y, Bx⟩ + ⟨y, Dy⟩ ≥ (d - b²/(a - d))(‖x‖² + ‖y‖²)`. -/
theorem block_completion_lower (A : E₁ →ₗ[ℝ] E₁) (B : E₁ →ₗ[ℝ] E₂) (D : E₂ →ₗ[ℝ] E₂)
    {a d b : ℝ} (had : d < a) (hA : ∀ x, a * ‖x‖ ^ 2 ≤ inner ℝ x (A x))
    (hD : ∀ y, d * ‖y‖ ^ 2 ≤ inner ℝ y (D y)) (hB : ∀ x, ‖B x‖ ≤ b * ‖x‖) (x : E₁) (y : E₂) :
    (d - b ^ 2 / (a - d)) * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤
      inner ℝ x (A x) + 2 * inner ℝ y (B x) + inner ℝ y (D y) := by
  refine block_lower_scalar had (hA x) (hD y) ?_
  calc |inner ℝ y (B x)| ≤ ‖y‖ * ‖B x‖ := abs_real_inner_le_norm y (B x)
    _ ≤ ‖y‖ * (b * ‖x‖) := mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)
    _ = b * ‖x‖ * ‖y‖ := by ring

/-- **`lem:block-completion` (b), upper bound.** If `A ⪯ aI`, `D ⪯ dI`, `‖B‖ ≤ b` and `a > d`,
then `T ⪯ (a + b²/(a - d)) I`. -/
theorem block_completion_upper (A : E₁ →ₗ[ℝ] E₁) (B : E₁ →ₗ[ℝ] E₂) (D : E₂ →ₗ[ℝ] E₂)
    {a d b : ℝ} (had : d < a) (hA : ∀ x, inner ℝ x (A x) ≤ a * ‖x‖ ^ 2)
    (hD : ∀ y, inner ℝ y (D y) ≤ d * ‖y‖ ^ 2) (hB : ∀ x, ‖B x‖ ≤ b * ‖x‖) (x : E₁) (y : E₂) :
    inner ℝ x (A x) + 2 * inner ℝ y (B x) + inner ℝ y (D y) ≤
      (a + b ^ 2 / (a - d)) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  refine block_upper_scalar had (hA x) (hD y) ?_
  calc |inner ℝ y (B x)| ≤ ‖y‖ * ‖B x‖ := abs_real_inner_le_norm y (B x)
    _ ≤ ‖y‖ * (b * ‖x‖) := mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)
    _ = b * ‖x‖ * ‖y‖ := by ring

end InnerProduct

/-! ### `prop:matching:positive` -/

variable {Ω : Type*} [Fintype Ω]

/-- The decomposition `f = (E f) 1 + P₀f` in a symmetric form. -/
theorem form_decomp (ν : FiniteLaw Ω) (𝔞 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hsym : ∀ f g, 𝔞 f g = 𝔞 g f) (f : Ω → ℝ) :
    𝔞 f f = ν.expect f ^ 2 * 𝔞 (fun _ => 1) (fun _ => 1) +
      2 * (ν.expect f * 𝔞 (center ν f) (fun _ => 1)) + 𝔞 (center ν f) (center ν f) := by
  have hf : f = ν.expect f • (fun _ : Ω => (1 : ℝ)) + center ν f := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, center]
    ring
  conv_lhs => rw [hf]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hsym (fun _ => 1) (center ν f)]
  ring

/-- Pythagoras: `‖f‖² = (E f)² + ‖P₀ f‖²`. -/
theorem nrm_sq_decomp (ν : FiniteLaw Ω) (f : Ω → ℝ) :
    nrm ν f ^ 2 = ν.expect f ^ 2 + nrm ν (center ν f) ^ 2 := by
  rw [nrm_sq_eq, nrm_sq_eq]
  unfold ip center
  have h := FiniteLaw.expect_sq_sub_mean (μ := ν) f
  have e1 : ν.expect (fun x => f x * f x) = ν.expect (fun x => f x ^ 2) :=
    ν.expect_congr (fun x => by ring)
  have e2 : ν.expect (fun x => (f x - ν.expect f) * (f x - ν.expect f)) =
      ν.expect (fun x => (f x - ν.expect f) ^ 2) := ν.expect_congr (fun x => by ring)
  rw [e1, e2, h]
  ring

/-- **`prop:matching:positive` (a).** If `A` is self-adjoint with `⟨1, A1⟩ = 1`,
`‖P₀A1‖ ≤ e` and `P₀AP₀ ⪯ βP₀` with `β < 1`, then `A ⪯ (1 + e²/(1 - β)) I`. -/
theorem envelope_upper (ν : FiniteLaw Ω) (𝔞 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hsym : ∀ f g, 𝔞 f g = 𝔞 g f) (h11 : 𝔞 (fun _ => 1) (fun _ => 1) = 1) {e β : ℝ}
    (hβ : β < 1) (he : ∀ f, ν.expect f = 0 → |𝔞 f (fun _ => 1)| ≤ e * nrm ν f)
    (hP : ∀ f, ν.expect f = 0 → 𝔞 f f ≤ β * nrm ν f ^ 2) (f : Ω → ℝ) :
    𝔞 f f ≤ (1 + e ^ 2 / (1 - β)) * nrm ν f ^ 2 := by
  rw [form_decomp ν 𝔞 hsym f, h11, nrm_sq_decomp ν f, ← sq_abs (ν.expect f)]
  refine block_upper_scalar (a := 1) (d := β) (b := e) hβ (by rw [one_mul, sq_abs]; linarith)
    (hP _ (expect_center ν f)) ?_
  rw [abs_mul]
  calc |ν.expect f| * |𝔞 (center ν f) (fun _ => 1)|
      ≤ |ν.expect f| * (e * nrm ν (center ν f)) :=
        mul_le_mul_of_nonneg_left (he _ (expect_center ν f)) (abs_nonneg _)
    _ = e * |ν.expect f| * nrm ν (center ν f) := by ring

/-- **`prop:matching:positive` (a′), lower envelope.** If `‖P₀A1‖ ≤ e` and
`P₀AP₀ ⪰ -gP₀` with `g ≥ 0`, then `A ⪰ -(g + e²/(1 + g)) I`. -/
theorem envelope_lower (ν : FiniteLaw Ω) (𝔞 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hsym : ∀ f g, 𝔞 f g = 𝔞 g f) (h11 : 𝔞 (fun _ => 1) (fun _ => 1) = 1) {e g : ℝ}
    (hg : 0 ≤ g) (he : ∀ f, ν.expect f = 0 → |𝔞 f (fun _ => 1)| ≤ e * nrm ν f)
    (hP : ∀ f, ν.expect f = 0 → -g * nrm ν f ^ 2 ≤ 𝔞 f f) (f : Ω → ℝ) :
    -(g + e ^ 2 / (1 + g)) * nrm ν f ^ 2 ≤ 𝔞 f f := by
  rw [form_decomp ν 𝔞 hsym f, h11, nrm_sq_decomp ν f, ← sq_abs (ν.expect f)]
  have h := block_lower_scalar (a := 1) (d := -g) (b := e) (X := |ν.expect f|)
    (Y := nrm ν (center ν f)) (qA := |ν.expect f| ^ 2 * 1)
    (qD := 𝔞 (center ν f) (center ν f)) (c := ν.expect f * 𝔞 (center ν f) (fun _ => 1))
    (by linarith) (by rw [one_mul, mul_one]) (hP _ (expect_center ν f)) ?_
  · have e1 : -g - e ^ 2 / (1 - -g) = -(g + e ^ 2 / (1 + g)) := by
      rw [show (1 : ℝ) - -g = 1 + g by ring]
      ring
    rw [e1] at h
    rw [sq_abs] at h ⊢
    linarith
  · rw [abs_mul]
    calc |ν.expect f| * |𝔞 (center ν f) (fun _ => 1)|
        ≤ |ν.expect f| * (e * nrm ν (center ν f)) :=
          mul_le_mul_of_nonneg_left (he _ (expect_center ν f)) (abs_nonneg _)
      _ = e * |ν.expect f| * nrm ν (center ν f) := by ring

/-- The kernel form is symmetric for a symmetric kernel. -/
theorem kernelForm_symm (ν : FiniteLaw Ω) (K : Ω → Ω → ℝ) (hK : ∀ x y, K y x = K x y)
    (f h : Ω → ℝ) : kernelForm ν ν K f h = kernelForm ν ν K h f := by
  rw [← kernelForm_transpose ν ν K f h]
  simp only [kernelForm, LinearMap.mk₂_apply, hK]

/-- **`prop:matching:positive` (b), normalized kernels.** Let `K` be a symmetric kernel with
`‖T_K - kJ‖ ≤ kε`, `k > 0`, `0 ≤ ε < 1`. Put `z = ⟨1, T_K 1⟩/k`, `A = T_K/(kz)` and
`ε̂ = ε/(1 - ε)`. Then `|z - 1| ≤ ε`, `⟨1, A1⟩ = 1`, `‖P₀A1‖ ≤ ε̂`, `‖P₀AP₀‖ ≤ ε̂` and
`A ⪰ -ε̂ I`; if `ε̂ < 1`, then `A ⪯ (1 + ε̂²/(1 - ε̂)) I`. The form of `A` is
`kernelForm ν ν K f h / (k z)`. Nonnegativity of `K` is not needed. -/
theorem normalized_kernel (ν : FiniteLaw Ω) (K : Ω → Ω → ℝ) (hK : ∀ x y, K y x = K x y)
    {k ε : ℝ} (hk : 0 < k) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hD : ∀ f h, |kernelForm ν ν K f h - k * (ν.expect f * ν.expect h)| ≤
      k * ε * nrm ν f * nrm ν h) :
    let z := kernelForm ν ν K (fun _ => 1) (fun _ => 1) / k
    let εh := ε / (1 - ε)
    |z - 1| ≤ ε ∧
    kernelForm ν ν K (fun _ => 1) (fun _ => 1) / (k * z) = 1 ∧
    (∀ f, ν.expect f = 0 → |kernelForm ν ν K f (fun _ => 1) / (k * z)| ≤ εh * nrm ν f) ∧
    (∀ f h, ν.expect f = 0 → ν.expect h = 0 →
      |kernelForm ν ν K f h / (k * z)| ≤ εh * nrm ν f * nrm ν h) ∧
    (∀ f, -εh * nrm ν f ^ 2 ≤ kernelForm ν ν K f f / (k * z)) ∧
    (εh < 1 → ∀ f, kernelForm ν ν K f f / (k * z) ≤ (1 + εh ^ 2 / (1 - εh)) * nrm ν f ^ 2) := by
  intro z εh
  have h11 := hD (fun _ => 1) (fun _ => 1)
  rw [expect_one, nrm_one, mul_one, mul_one, mul_one, mul_one] at h11
  have hkz : k * z = kernelForm ν ν K (fun _ => 1) (fun _ => 1) := by
    simp only [z]
    field_simp
  have hz : |z - 1| ≤ ε := by
    have e : z - 1 = (kernelForm ν ν K (fun _ => 1) (fun _ => 1) - k) / k := by
      simp only [z]
      field_simp
    rw [e, abs_div, abs_of_pos hk, div_le_iff₀ hk]
    linarith
  have hzpos : 1 - ε ≤ z := by linarith [neg_abs_le (z - 1)]
  have hz0 : 0 < z := by linarith
  have hkz0 : 0 < k * z := mul_pos hk hz0
  have hε1' : 0 < 1 - ε := by linarith
  -- `ε/z ≤ ε̂`
  have hratio : ε / z ≤ εh := div_le_div_of_nonneg_left hε0 hε1' hzpos
  have hcent : ∀ f h, ν.expect f = 0 →
      |kernelForm ν ν K f h / (k * z)| ≤ εh * nrm ν f * nrm ν h := by
    intro f h hf
    have := hD f h
    rw [hf, zero_mul, mul_zero, sub_zero] at this
    rw [abs_div, abs_of_pos hkz0, div_le_iff₀ hkz0]
    have hn : 0 ≤ nrm ν f * nrm ν h := mul_nonneg (nrm_nonneg _ _) (nrm_nonneg _ _)
    calc |kernelForm ν ν K f h| ≤ k * ε * nrm ν f * nrm ν h := this
      _ = (ε / z) * nrm ν f * nrm ν h * (k * z) := by field_simp
      _ ≤ εh * nrm ν f * nrm ν h * (k * z) := by
          have := mul_le_mul_of_nonneg_right hratio hn
          nlinarith
  have hlow : ∀ f, -εh * nrm ν f ^ 2 ≤ kernelForm ν ν K f f / (k * z) := by
    intro f
    have := hD f f
    have hsq : 0 ≤ k * (ν.expect f * ν.expect f) := mul_nonneg hk.le (mul_self_nonneg _)
    have h1 : -(k * ε * nrm ν f * nrm ν f) ≤ kernelForm ν ν K f f := by
      linarith [neg_abs_le (kernelForm ν ν K f f - k * (ν.expect f * ν.expect f))]
    rw [le_div_iff₀ hkz0]
    have hn : 0 ≤ nrm ν f ^ 2 := sq_nonneg _
    have : ε / z * nrm ν f ^ 2 ≤ εh * nrm ν f ^ 2 := mul_le_mul_of_nonneg_right hratio hn
    have e : k * ε * nrm ν f * nrm ν f = ε / z * nrm ν f ^ 2 * (k * z) := by field_simp
    nlinarith
  refine ⟨hz, ?_, fun f hf => ?_, fun f h hf _ => hcent f h hf, hlow, ?_⟩
  · rw [hkz]
    exact div_self (by rw [← hkz]; exact hkz0.ne')
  · have := hcent f (fun _ => 1) hf
    rwa [nrm_one, mul_one] at this
  · intro hεh f
    let 𝔞 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) →ₗ[ℝ] ℝ := (k * z)⁻¹ • kernelForm ν ν K
    have h𝔞 : ∀ f h, 𝔞 f h = kernelForm ν ν K f h / (k * z) := by
      intro f h
      simp only [𝔞, LinearMap.smul_apply, smul_eq_mul]
      ring
    have hsym : ∀ f h, 𝔞 f h = 𝔞 h f := by
      intro f h
      rw [h𝔞, h𝔞, kernelForm_symm ν K hK]
    have h11' : 𝔞 (fun _ => 1) (fun _ => 1) = 1 := by
      rw [h𝔞, hkz]
      exact div_self (by rw [← hkz]; exact hkz0.ne')
    have he : ∀ f, ν.expect f = 0 → |𝔞 f (fun _ => 1)| ≤ εh * nrm ν f := by
      intro f hf
      have := hcent f (fun _ => 1) hf
      rw [nrm_one, mul_one] at this
      rwa [h𝔞]
    have hP : ∀ f, ν.expect f = 0 → 𝔞 f f ≤ εh * nrm ν f ^ 2 := by
      intro f hf
      have := hcent f f hf
      rw [h𝔞]
      have e : εh * nrm ν f * nrm ν f = εh * nrm ν f ^ 2 := by ring
      linarith [le_abs_self (kernelForm ν ν K f f / (k * z))]
    have := envelope_upper ν 𝔞 hsym h11' hεh he hP f
    rwa [h𝔞] at this

/-- **`prop:matching:positive` (c), the threshold factor.** If `0 < r ≤ r₀`, `g ≥ 0`, `g r₀ < 1`,
`e(r) ≥ 0` and `e(r)/r ≤ e(r₀)/r₀`, then `e(r)²/(1 - g r) ≤ r² · r₀⁻² e(r₀)²/(1 - g r₀)`. With
`r = p^{-1/2}` and `r₀ = p₀^{-1/2}` the right side is `B⁺/p`, `B⁺ = p₀ e(r₀)²/(1 - g r₀)`. -/
theorem threshold_factor {r r₀ g er er₀ : ℝ} (hr : 0 < r) (hrr : r ≤ r₀) (hg : 0 ≤ g)
    (hg1 : g * r₀ < 1) (her : 0 ≤ er) (hmono : er / r ≤ er₀ / r₀) :
    er ^ 2 / (1 - g * r) ≤ r ^ 2 * (er₀ ^ 2 / r₀ ^ 2 / (1 - g * r₀)) := by
  have hr0 : 0 < r₀ := lt_of_lt_of_le hr hrr
  have h1 : 0 < 1 - g * r₀ := by linarith
  have h2 : 1 - g * r₀ ≤ 1 - g * r := by nlinarith
  have h3 : er = r * (er / r) := by field_simp
  have h4 : 0 ≤ er / r := div_nonneg her hr.le
  have h5 : er ^ 2 ≤ r ^ 2 * (er₀ / r₀) ^ 2 := by
    rw [h3, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h4 hmono 2) (sq_nonneg r)
  calc er ^ 2 / (1 - g * r) ≤ r ^ 2 * (er₀ / r₀) ^ 2 / (1 - g * r) :=
        div_le_div_of_nonneg_right h5 (by linarith)
    _ ≤ r ^ 2 * (er₀ / r₀) ^ 2 / (1 - g * r₀) :=
        div_le_div_of_nonneg_left (by positivity) h1 h2
    _ = r ^ 2 * (er₀ ^ 2 / r₀ ^ 2 / (1 - g * r₀)) := by
        rw [div_pow]
        ring

/-- **`prop:matching:positive` (c).** For `p ≥ p₀ > 0` put `r = p^{-1/2}`, `r₀ = p₀^{-1/2}`. Let `A`
satisfy (a) with `e = e(r)` and `β = g r`, where `e(r)/r ≤ e(r₀)/r₀` and `g r₀ < 1`. Then
`A ⪯ (1 + B⁺/p) I` with `B⁺ = p₀ e(r₀)²/(1 - g r₀)`. -/
theorem envelope_threshold (ν : FiniteLaw Ω) (𝔞 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hsym : ∀ f g, 𝔞 f g = 𝔞 g f) (h11 : 𝔞 (fun _ => 1) (fun _ => 1) = 1) {p p₀ g er er₀ : ℝ}
    (hp₀ : 0 < p₀) (hpp : p₀ ≤ p) (hg : 0 ≤ g) (hg1 : g * (√p₀)⁻¹ < 1) (her : 0 ≤ er)
    (hmono : er / (√p)⁻¹ ≤ er₀ / (√p₀)⁻¹)
    (he : ∀ f, ν.expect f = 0 → |𝔞 f (fun _ => 1)| ≤ er * nrm ν f)
    (hP : ∀ f, ν.expect f = 0 → 𝔞 f f ≤ g * (√p)⁻¹ * nrm ν f ^ 2) (f : Ω → ℝ) :
    𝔞 f f ≤ (1 + p₀ * er₀ ^ 2 / (1 - g * (√p₀)⁻¹) / p) * nrm ν f ^ 2 := by
  have hp : 0 < p := lt_of_lt_of_le hp₀ hpp
  have hr : 0 < (√p)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hp)
  have hrr : (√p)⁻¹ ≤ (√p₀)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr hp₀) (Real.sqrt_le_sqrt hpp)
  have hβ : g * (√p)⁻¹ < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hrr hg) hg1
  have hA := envelope_upper ν 𝔞 hsym h11 hβ he hP f
  have hT := threshold_factor hr hrr hg hg1 her hmono
  have e1 : (√p)⁻¹ ^ 2 = 1 / p := by
    rw [inv_pow, Real.sq_sqrt hp.le, one_div]
  have e2 : (√p₀)⁻¹ ^ 2 = 1 / p₀ := by
    rw [inv_pow, Real.sq_sqrt hp₀.le, one_div]
  rw [e1, e2] at hT
  have e3 : 1 / p * (er₀ ^ 2 / (1 / p₀) / (1 - g * (√p₀)⁻¹)) =
      p₀ * er₀ ^ 2 / (1 - g * (√p₀)⁻¹) / p := by
    field_simp
  rw [e3] at hT
  refine hA.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  linarith

end Sarkozy.Cuts
