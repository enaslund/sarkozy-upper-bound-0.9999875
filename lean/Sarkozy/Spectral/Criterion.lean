module

public import Sarkozy.Spectral.RouteA
public import Mathlib.Analysis.Matrix.PosDef

/-!
# `thm:spectral-criterion` (Route A): the assembled criterion

The abstract Route A argument of `Sarkozy.Spectral.RouteA` with the finite test stated as in
`eq:spectral-test`, as positive semidefiniteness of the matrices
`M_{𝔠,±}(s) = A_{𝔠,±} - (H⁺ - (Δ^E)ᵀΔ^E)/s + (c̄_⊥ + s - η̄_Q - η̄_B/s) I`, and with the
numerical conclusions (c), (d) of `thm:spectral-criterion`.

* `finiteTest_of_posSemidef`: `M(s) ⪰ 0` gives the quadratic-form test `FiniteTest`.
* `spectral_criterion_routeA`: (a) `Op ⪰ -g r I`; (b) `|⟪h, Op h⟫| ≤ g r ‖h‖²` on `h ⊥ 1`;
  (c) `‖ϱ - 1‖ ≤ ε_ϱ` and `p ε_ϱ(r)² ≤ p₀ ε_ϱ(r₀)²`; (d) `Op ⪯ (1 + B⁺/p) I` with
  `B⁺ = p₀ ε_ϱ(r₀)²/(1 - g' r₀)` for every `g' ≥ g` with `g' r₀ < 1`.

The two signs: `A_{𝔠,-} = -A_{𝔠,+}` (`def:coupling-model`), so for `-Op` the modes `Ξ_±` use
the test of the opposite sign; no further test is needed for (b), as in the paper.

The hypotheses that the paper takes from the certificates (the matrix tests, the bounds
`c_⊥(r) ≤ c̄_⊥`, `η_Q(r) ≤ η̄_Q`, `η_B(r) ≤ η̄_B`, `ε_V(r) ≤ ε̄_V < 1`, `ε_ϱ(r)/r ≤ ε_ϱ(r₀)/r₀`
from `lem:spectral-monotone`, and `g' r₀ < 1`) are explicit numerical hypotheses here.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate Matrix ComplexOrder
open RCLike

namespace Sarkozy.Spectral

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `re (x^* x) = ∑_k |x_k|²`. -/
theorem re_star_dotProduct_self {n : Type*} [Fintype n] (x : n → 𝕜) :
    re (star x ⬝ᵥ x) = sqn x := by
  rw [sqn, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- **The matrix test gives the quadratic-form test**: if
`A - X/s + (c̄_⊥ + s - η̄_Q - η̄_B/s) I ⪰ 0`, then `FiniteTest` holds for the forms of `A` and
`X` (in the application `X = H⁺ - (Δ^E)ᵀΔ^E`). -/
theorem finiteTest_of_posSemidef {n : Type*} [Fintype n] [DecidableEq n] (A X : Matrix n n 𝕜)
    {cbar s ηQbar ηBbar : ℝ}
    (h : (A - ((s⁻¹ : ℝ) : 𝕜) • X +
      ((cbar + s - ηQbar - ηBbar / s : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)).PosSemidef) :
    FiniteTest (fun x => re (star x ⬝ᵥ (A *ᵥ x))) (fun x => re (star x ⬝ᵥ (X *ᵥ x)))
      cbar s ηQbar ηBbar := by
  intro x
  have h0 := h.re_dotProduct_nonneg x
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_add, dotProduct_sub, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, map_add, map_sub, RCLike.re_ofReal_mul, RCLike.re_ofReal_mul,
    re_star_dotProduct_self] at h0
  rw [div_eq_mul_inv, mul_comm (re (star x ⬝ᵥ (X *ᵥ x))) s⁻¹]
  linarith

section Assembled

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]
  {T : H →ₗ[𝕜] H} {one : H} {V Sp Sm : Submodule 𝕜 H}
  {Ξ n : Type*} [Fintype Ξ] [Fintype n] [DecidableEq n] {sgn : Ξ → Prop} [DecidablePred sgn]
  {coef : H → Ξ → n → 𝕜}

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- **`thm:spectral-criterion` (Route A), abstract form, at one prime `p ≥ p₀`.** The operator
`T = Op` satisfies the Route A inputs at `r = p^{-1/2}` (`RouteAInputs`), with Fourier matrices
`A(ξ) = A₊` on `Ξ₊` and `A₋ = -A₊` on `Ξ₋`, coupling matrix `X = H⁺ - A₊^* A₊`, and the
finite tests `M_{𝔠,±}(τ_±) ⪰ 0` hold at the certified values `c̄_⊥, η̄_Q, η̄_B, ε̄_V`. Then
(a) `Op ⪰ -g r I`, (b) `|⟪h, Op h⟫| ≤ g r ‖h‖²` for `h ⊥ 1`, (c) `‖ϱ - 1‖ ≤ ε_ϱ(r)` and
`p ε_ϱ(r)² ≤ p₀ ε_ϱ(r₀)²`, and (d) `Op ⪯ (1 + B⁺/p) I` with `B⁺ = p₀ ε_ϱ(r₀)²/(1 - g' r₀)`. -/
theorem spectral_criterion_routeA (Aplus X : Matrix n n 𝕜) {p p₀ : ℝ} (hp₀ : 0 < p₀)
    (hpp : p₀ ≤ p) {ηQ ηB εV ερ ερ₀ aperp : ℝ}
    (hin : RouteAInputs T one V Sp Sm sgn coef
      (fun ξ x => re (star x ⬝ᵥ ((if sgn ξ then Aplus else -Aplus) *ᵥ x)))
      (fun _ x => re (star x ⬝ᵥ (X *ᵥ x))) (1 / √p) ηQ ηB εV ερ aperp)
    {cbar ηQbar ηBbar εVbar τp τm g g' : ℝ}
    (hcbar0 : 0 ≤ cbar) (hcperp : (aperp + ερ ^ 2) / (1 / √p) ≤ cbar)
    (hηQ : ηQ ≤ ηQbar) (hηB : ηB ≤ ηBbar) (hεV : εV ≤ εVbar) (hεV0 : 0 ≤ εVbar)
    (hεV1 : εVbar < 1) (hτp : 0 < τp) (hτm : 0 < τm)
    (htestp : (Aplus - ((τp⁻¹ : ℝ) : 𝕜) • X +
      ((cbar + τp - ηQbar - ηBbar / τp : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)).PosSemidef)
    (htestm : (-Aplus - ((τm⁻¹ : ℝ) : 𝕜) • X +
      ((cbar + τm - ηQbar - ηBbar / τm : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)).PosSemidef)
    (hgp : (cbar + τp) / (1 - εVbar) ≤ g) (hgm : (cbar + τm) / (1 - εVbar) ≤ g)
    (hρmono : ερ / (1 / √p) ≤ ερ₀ / (1 / √p₀)) (hgg' : g ≤ g') (hg'r : g' * (1 / √p₀) < 1) :
    (∀ F : H, -(g * (1 / √p)) * ‖F‖ ^ 2 ≤ re ⟪F, T F⟫) ∧
    (∀ h : H, ⟪one, h⟫ = 0 → |re ⟪h, T h⟫| ≤ g * (1 / √p) * ‖h‖ ^ 2) ∧
    (‖T one - one‖ ≤ ερ ∧ p * ερ ^ 2 ≤ p₀ * ερ₀ ^ 2) ∧
    (∀ F : H, re ⟪F, T F⟫ ≤ (1 + p₀ * ερ₀ ^ 2 / (1 - g' * (1 / √p₀)) / p) * ‖F‖ ^ 2) := by
  have hp : 0 < p := lt_of_lt_of_le hp₀ hpp
  set r := 1 / √p with hrdef
  set r₀ := 1 / √p₀ with hr₀def
  have hr : 0 < r := by rw [hrdef]; positivity
  have hr₀ : 0 < r₀ := by rw [hr₀def]; positivity
  have hrr₀ : r ≤ r₀ := by
    rw [hrdef, hr₀def]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hp₀) (Real.sqrt_le_sqrt hpp)
  have hr2 : r ^ 2 = 1 / p := by rw [hrdef, div_pow, Real.sq_sqrt hp.le, one_pow]
  have hr₀2 : r₀ ^ 2 = 1 / p₀ := by rw [hr₀def, div_pow, Real.sq_sqrt hp₀.le, one_pow]
  have hcbar : aperp + ερ ^ 2 ≤ cbar * r := by
    rw [div_le_iff₀ hr] at hcperp
    exact hcperp
  -- the finite tests, as quadratic forms, on the two families of modes
  have tp := finiteTest_of_posSemidef Aplus X htestp
  have tm := finiteTest_of_posSemidef (-Aplus) X htestm
  have htp : ∀ ξ, sgn ξ → FiniteTest (fun x => re (star x ⬝ᵥ ((if sgn ξ then Aplus else
      -Aplus) *ᵥ x))) (fun x => re (star x ⬝ᵥ (X *ᵥ x))) cbar τp ηQbar ηBbar := by
    intro ξ hξ
    simp only [ite_eq_left hξ]
    exact tp
  have htm : ∀ ξ, ¬ sgn ξ → FiniteTest (fun x => re (star x ⬝ᵥ ((if sgn ξ then Aplus else
      -Aplus) *ᵥ x))) (fun x => re (star x ⬝ᵥ (X *ᵥ x))) cbar τm ηQbar ηBbar := by
    intro ξ hξ
    simp only [ite_eq_right hξ]
    exact tm
  -- for `-Op`: the negated forms are the forms of the opposite sign
  have hneg : ∀ (M : Matrix n n 𝕜) (x : n → 𝕜),
      -re (star x ⬝ᵥ (M *ᵥ x)) = re (star x ⬝ᵥ ((-M) *ᵥ x)) := by
    intro M x
    rw [Matrix.neg_mulVec, dotProduct_neg, map_neg]
  have htp' : ∀ ξ, sgn ξ → FiniteTest (fun x => -re (star x ⬝ᵥ ((if sgn ξ then Aplus else
      -Aplus) *ᵥ x))) (fun x => re (star x ⬝ᵥ (X *ᵥ x))) cbar τm ηQbar ηBbar := by
    intro ξ hξ x
    simp only [ite_eq_left hξ, hneg]
    exact tm x
  have htm' : ∀ ξ, ¬ sgn ξ → FiniteTest (fun x => -re (star x ⬝ᵥ ((if sgn ξ then Aplus else
      -Aplus) *ᵥ x))) (fun x => re (star x ⬝ᵥ (X *ᵥ x))) cbar τp ηQbar ηBbar := by
    intro ξ hξ x
    simp only [ite_eq_right hξ, hneg, neg_neg]
    exact tp x
  have ha := routeA_lower hin hr hcbar0 hcbar hηQ hηB hεV hεV0 hεV1 hτp hτm htp htm hgp hgm
  have hb : ∀ h : H, ⟪one, h⟫ = 0 → |re ⟪h, T h⟫| ≤ g * r * ‖h‖ ^ 2 := fun h h1 =>
    routeA_compression hin hr hcbar0 hcbar hηQ hηB hεV hεV0 hεV1 hτp hτm hτm hτp htp htm htp'
      htm' hgp hgm hgm hgp h1
  -- (c)
  have hρ0 : 0 ≤ ερ := (norm_nonneg _).trans hin.rho_bound
  have hc2 : p * ερ ^ 2 ≤ p₀ * ερ₀ ^ 2 := by
    have h1 : 0 ≤ ερ / r := div_nonneg hρ0 hr.le
    have h2 := pow_le_pow_left₀ h1 hρmono 2
    have e1 : (ερ / r) ^ 2 = p * ερ ^ 2 := by
      rw [hrdef, div_div_eq_mul_div, div_one, mul_pow, Real.sq_sqrt hp.le, mul_comm]
    have e2 : (ερ₀ / r₀) ^ 2 = p₀ * ερ₀ ^ 2 := by
      rw [hr₀def, div_div_eq_mul_div, div_one, mul_pow, Real.sq_sqrt hp₀.le, mul_comm]
    rwa [e1, e2] at h2
  -- (d)
  have hg0 : 0 ≤ g := le_trans (div_nonneg (by linarith) (by linarith)) hgp
  have hg'0 : 0 ≤ g' := hg0.trans hgg'
  have hβ : g' * r < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hrr₀ hg'0) hg'r
  have hb' : ∀ h : H, ⟪one, h⟫ = 0 → |re ⟪h, T h⟫| ≤ (g' * r) * ‖h‖ ^ 2 := fun h h1 =>
    (hb h h1).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hgg' hr.le)
      (sq_nonneg _))
  have hd := upper_of_compression hin.symm hin.norm_one hin.rho_mean hin.rho_bound hβ hb'
  refine ⟨ha, hb, ⟨hin.rho_bound, hc2⟩, fun F => (hd F).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  -- `ε_ϱ²/(1 - g' r) ≤ B⁺/p`
  have hd1 : 0 < 1 - g' * r := by linarith
  have hd0 : 0 < 1 - g' * r₀ := by linarith
  have hden : 1 - g' * r₀ ≤ 1 - g' * r := by
    have : g' * r ≤ g' * r₀ := mul_le_mul_of_nonneg_left hrr₀ hg'0
    linarith
  have hnum : ερ ^ 2 ≤ p₀ * ερ₀ ^ 2 / p := by
    rw [le_div_iff₀ hp]
    linarith
  have : ερ ^ 2 / (1 - g' * r) ≤ p₀ * ερ₀ ^ 2 / (1 - g' * r₀) / p := by
    rw [div_div, mul_comm (1 - g' * r₀) p, ← div_div]
    calc ερ ^ 2 / (1 - g' * r) ≤ (p₀ * ερ₀ ^ 2 / p) / (1 - g' * r) :=
          div_le_div_of_nonneg_right hnum hd1.le
      _ ≤ (p₀ * ερ₀ ^ 2 / p) / (1 - g' * r₀) :=
          div_le_div_of_nonneg_left (by positivity) hd0 hden
  linarith

end Assembled

end Sarkozy.Spectral
