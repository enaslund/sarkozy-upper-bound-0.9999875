module

public import Sarkozy.Spectral.Criterion
public import Sarkozy.Spectral.Monotone

/-!
# `thm:spectral-criterion`, uniformly in `p`

`thm:spectral-criterion` (`paper/sections/14_spectral.tex`) is stated for every prime
`p ≥ p₀` of the class, with every input a function of `r ∈ (0, r₀]` and the certificate checked
once, at `r₀ = p₀^{-1/2}`. `spectral_criterion_uniform` is that form of
`Sarkozy.Spectral.spectral_criterion_routeA`: the quantities `c_⊥`, `η_Q`, `η_B`, `ε_V` and
`ε_ϱ/r` are admissible functions on the box `(0, r₀]` (`Sarkozy.Majorant.Admissible`, supplied
by `lem:spectral-monotone`), the bounds `c̄_⊥`, `η̄_Q`, `η̄_B`, `ε̄_V` are bounds of their values at
`r₀` only, and the matrix tests are those at `r₀`. The bounds at `r = p^{-1/2}` then follow by
`Majorant.endpoint_le`.
-/

@[expose] public section

open scoped InnerProductSpace Matrix ComplexOrder
open RCLike Sarkozy.Majorant

namespace Sarkozy.Spectral

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- **`thm:spectral-criterion`, uniformly in `p`.** The certificate (the bounds `hc0`, `hηQ0`,
`hηB0`, `hεV0` at the endpoint `top = r₀` and the two matrix tests) is checked once; the inputs
at the prime `p ≥ p₀` are the values at `r = p^{-1/2}` of admissible functions. -/
theorem spectral_criterion_uniform [FiniteDimensional 𝕜 H] {T : H →ₗ[𝕜] H} {one : H}
    {V Sp Sm : Submodule 𝕜 H} {Ξ n : Type*} [Fintype Ξ] [Fintype n] [DecidableEq n]
    {sgn : Ξ → Prop} [DecidablePred sgn] {coef : H → Ξ → n → 𝕜}
    (Aplus X : Matrix n n 𝕜) {p p₀ : ℝ} (hp₀ : 0 < p₀) (hpp : p₀ ≤ p)
    (cperp ηQf ηBf εVf ερr : Set.Ioc (0 : ℝ) (1 / √p₀) → ℝ)
    (hcA : Admissible cperp) (hηQA : Admissible ηQf) (hηBA : Admissible ηBf)
    (hεVA : Admissible εVf) (hρA : Admissible ερr)
    (hr : 0 < 1 / √p ∧ 1 / √p ≤ 1 / √p₀) (top : Set.Ioc (0 : ℝ) (1 / √p₀))
    (htop : top.1 = 1 / √p₀) {aperp : ℝ}
    (hin : RouteAInputs T one V Sp Sm sgn coef
      (fun ξ x => re (star x ⬝ᵥ ((if sgn ξ then Aplus else -Aplus) *ᵥ x)))
      (fun _ x => re (star x ⬝ᵥ (X *ᵥ x))) (1 / √p) (ηQf ⟨1 / √p, hr⟩) (ηBf ⟨1 / √p, hr⟩)
      (εVf ⟨1 / √p, hr⟩) (1 / √p * ερr ⟨1 / √p, hr⟩) aperp)
    (hcp : (aperp + (1 / √p * ερr ⟨1 / √p, hr⟩) ^ 2) / (1 / √p) = cperp ⟨1 / √p, hr⟩)
    {cbar ηQbar ηBbar εVbar τp τm g g' : ℝ} (hcbar0 : 0 ≤ cbar) (hc0 : cperp top ≤ cbar)
    (hηQ0 : ηQf top ≤ ηQbar) (hηB0 : ηBf top ≤ ηBbar) (hεV0 : εVf top ≤ εVbar)
    (hεVbar0 : 0 ≤ εVbar) (hεV1 : εVbar < 1) (hτp : 0 < τp) (hτm : 0 < τm)
    (htestp : (Aplus - ((τp⁻¹ : ℝ) : 𝕜) • X +
      ((cbar + τp - ηQbar - ηBbar / τp : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)).PosSemidef)
    (htestm : (-Aplus - ((τm⁻¹ : ℝ) : 𝕜) • X +
      ((cbar + τm - ηQbar - ηBbar / τm : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)).PosSemidef)
    (hgp : (cbar + τp) / (1 - εVbar) ≤ g) (hgm : (cbar + τm) / (1 - εVbar) ≤ g)
    (hgg' : g ≤ g') (hg'r : g' * (1 / √p₀) < 1) :
    (∀ F : H, -(g * (1 / √p)) * ‖F‖ ^ 2 ≤ re ⟪F, T F⟫) ∧
    (∀ h : H, ⟪one, h⟫ = 0 → |re ⟪h, T h⟫| ≤ g * (1 / √p) * ‖h‖ ^ 2) ∧
    (‖T one - one‖ ≤ 1 / √p * ερr ⟨1 / √p, hr⟩ ∧
      p * (1 / √p * ερr ⟨1 / √p, hr⟩) ^ 2 ≤ p₀ * (1 / √p₀ * ερr top) ^ 2) ∧
    (∀ F : H, re ⟪F, T F⟫ ≤
      (1 + p₀ * (1 / √p₀ * ερr top) ^ 2 / (1 - g' * (1 / √p₀)) / p) * ‖F‖ ^ 2) := by
  have hxt : (⟨1 / √p, hr⟩ : Set.Ioc (0 : ℝ) (1 / √p₀)) ≤ top := by
    show 1 / √p ≤ top.1
    rw [htop]
    exact hr.2
  have hr₀ : 0 < 1 / √p₀ := by positivity
  have h1 : (aperp + (1 / √p * ερr ⟨1 / √p, hr⟩) ^ 2) / (1 / √p) ≤ cbar := by
    rw [hcp]
    exact (endpoint_le hcA hxt).trans hc0
  have hmono : 1 / √p * ερr ⟨1 / √p, hr⟩ / (1 / √p) ≤ 1 / √p₀ * ερr top / (1 / √p₀) := by
    rw [mul_div_cancel_left₀ _ hr.1.ne', mul_div_cancel_left₀ _ hr₀.ne']
    exact endpoint_le hρA hxt
  exact spectral_criterion_routeA Aplus X hp₀ hpp hin hcbar0 h1
    ((endpoint_le hηQA hxt).trans hηQ0) ((endpoint_le hηBA hxt).trans hηB0)
    ((endpoint_le hεVA hxt).trans hεV0) hεVbar0 hεV1 hτp hτm htestp htestm hgp hgm hmono hgg' hg'r

end Sarkozy.Spectral
