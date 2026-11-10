module

public import Sarkozy.Spectral.Uniform
public import Sarkozy.Spectral.Monotone
public import Sarkozy.UpperReference.MonotoneEndpoint

/-!
# `lem:upper-completed-root`: the Route A root caps from `2⁵²` on

`paper/sections/25_upper_reference.tex`, `lem:upper-completed-root`. From `2⁵²` on, the caps of
the root cuts LL20 and LL22 come from the Route A criterion `thm:spectral-criterion` with the
following inputs, as functions of `r ∈ (0, r₀]`, `r₀ = p₀^{-1/2}`:

* (i) perpendicular inputs: `N_ns = ∑_{k=2}^4 C_k(Q) r^k` (fixed `Q ≤ p₀`),
  `D_col = min(D_ord, D_nat)`, `M_⋆` the larger of the two classes' bounds, and
  `ε_Z = min(2(P_st + W_st) + N_ns + D_nat, Z_⋆ + N_ns + D_col)` with `Z_⋆` twice the larger
  `z_⋆` and the constants `P_st/r²`, `W_st/r`;
* (ii) coupling inputs `ε_H = min(ε'_H + ε_X, ε^loc_H)`, `Γ_E = min(Ê², Γ^loc_E)`, `ζ̄` a minimum,
  and `ε_ϱ = R_Z(M_⋆ + N_ns + D_col)`.

This file proves:

* `completed_epsZ_admissible`, `completed_inputs_admissible`: **the admissibility claims of the
  proof**: `ε_Z` (a minimum of two admissible forms) is admissible, and then (by
  `lem:spectral-monotone`(c), `Sarkozy.Spectral.spectral_monotone_c`) so are `R_Z`, `ε_ϱ/r`,
  `ε_ϱ` and `c_⊥ = R_Z(N_ns/r + D_col/r) + r(ε_ϱ/r)²`;
  `completed_coupling_admissible`: the three minima of (ii) are admissible.
* `upper_completed_root_prime`: **the conclusions of `thm:spectral-criterion` at every prime
  `p ≥ p₀`** with these inputs (`Sarkozy.Spectral.spectral_criterion_uniform`): `Op ⪰ -g r`,
  `|⟪h, Op h⟫| ≤ g r ‖h‖²` on `h ⊥ 1`, `‖ϱ - 1‖ ≤ ε_ϱ` with `p ε_ϱ² ≤ p₀ ε_ϱ(r₀)²`, and
  `Op ⪯ 1 + B_top/p` with `B_top = p₀ ε_ϱ(r₀)²/(1 - g r₀)`.
* `upper_completed_root_block`: **the block statement**: `⊗_{p∈𝔅} Op ⪰ -d b^{-1/2}` with
  `d = g exp(B_top L_u/(X log X))`, from the per-prime bounds (`cut_block_cap`).

**Hypotheses.** That the listed numbers bound the operators they stand for (`cor:extraction-leaf`(b)
for `N_ns`, `lem:oct24-collision`(e) for `D_col` and `D_nat`, `lem:star-mean` with
`prop:advance:ordered-star` for `M_⋆, z_⋆`, the coupling lemmas for (ii)) enters through
`RouteAInputs` at `p` and the admissibility of the normalized inputs, as in
`spectral_criterion_uniform`; `lem:spectral-monotone`(a),(b),(d) (admissibility of `η_Q`, `η_B`,
`ε_V` from the coupling inputs, and `ℓ^loc_k > 0` on the box) are hypotheses (`hηQA`, `hηBA`,
`hεVA`). The realization of the class-three Route A operator as the real cut operator of
`cut_block_cap` is not formalized: the block theorem takes the per-prime bounds of `cutOp` as
hypotheses (for class three, S1's `Sarkozy.SpectralD.Cx.spectral_criterion_cut_S1` gives the
lower bound for the actual cut operator).
-/

@[expose] public section

open scoped InnerProductSpace Matrix ComplexOrder
open RCLike Sarkozy.Majorant

namespace Sarkozy.UpperReference

open Sarkozy Sarkozy.Spectral

/-- The box `(0, r₀]`, `r₀ = p₀^{-1/2}`, of `thm:spectral-criterion`. -/
abbrev Box (p₀ : ℝ) : Type := Set.Ioc (0 : ℝ) (1 / √p₀)

/-- The coordinate `r` of the box is admissible. -/
theorem admissible_coord (p₀ : ℝ) : Admissible (fun x : Box p₀ => x.1) :=
  ⟨fun _ _ h => h, fun x => x.2.1.le⟩

section Inputs

variable {p₀ : ℝ}

/-- **`ε_Z` of `lem:upper-completed-root`(i)**: the smaller of
`2(P_st + W_st) + N_ns + D_nat` and `Z_⋆ + N_ns + D_col`, with `P_st = c_P r²`, `W_st = c_W r`,
`N_ns = r nN`, `D_nat = r nDnat`, `D_col = r min(nDord, nDnat)` and
`Z_⋆ = 2 r² max(nz₁, nz₃)` (the larger `z_⋆` of the two classes, doubled). -/
noncomputable def completedEpsZ (cP cW : ℝ) (nN nDord nDnat nz₁ nz₃ : Box p₀ → ℝ)
    (x : Box p₀) : ℝ :=
  min (2 * (cP * x.1 ^ 2 + cW * x.1) + x.1 * nN x + x.1 * nDnat x)
    (2 * (x.1 ^ 2 * max (nz₁ x) (nz₃ x)) + x.1 * nN x + x.1 * min (nDord x) (nDnat x))

/-- `ε_ϱ/r = R_Z(M_⋆/r + N_ns/r + D_col/r)`, with `M_⋆/r = max(nM₁, nM₃)` (the larger over the
two classes) and `D_col/r = min(nDord, nDnat)`. -/
noncomputable def completedRhoR (cP cW : ℝ) (nN nDord nDnat nM₁ nM₃ nz₁ nz₃ : Box p₀ → ℝ)
    (x : Box p₀) : ℝ :=
  1 / (1 - completedEpsZ cP cW nN nDord nDnat nz₁ nz₃ x) *
    (max (nM₁ x) (nM₃ x) + nN x + min (nDord x) (nDnat x))

/-- `c_⊥ = R_Z(N_ns/r + D_col/r) + r (ε_ϱ/r)²`. -/
noncomputable def completedCperp (cP cW : ℝ) (nN nDord nDnat nM₁ nM₃ nz₁ nz₃ : Box p₀ → ℝ)
    (x : Box p₀) : ℝ :=
  1 / (1 - completedEpsZ cP cW nN nDord nDnat nz₁ nz₃ x) * (nN x + min (nDord x) (nDnat x)) +
    x.1 * completedRhoR cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃ x ^ 2

/-- **`lem:upper-completed-root`, proof of (ii): `ε_Z` is admissible** (`lem:majorant`(ii)): both
forms are admissible (the constants `P_st/r²`, `W_st/r`, `lem:spectral-monotone`(c), and the
admissible `N_ns/r`, `D_nat/r`, `D_col/r`, `z_⋆/r²`), and so is their minimum. -/
theorem completed_epsZ_admissible {cP cW : ℝ} (hcP : 0 ≤ cP) (hcW : 0 ≤ cW)
    {nN nDord nDnat nz₁ nz₃ : Box p₀ → ℝ} (hN : Admissible nN) (hDo : Admissible nDord)
    (hDn : Admissible nDnat) (hz₁ : Admissible nz₁) (hz₃ : Admissible nz₃) :
    Admissible (completedEpsZ cP cW nN nDord nDnat nz₁ nz₃) := by
  have hr := admissible_coord p₀
  have hz := admissible_max hz₁ hz₃
  have hD := admissible_min hDo hDn
  have h1 : Admissible (fun x : Box p₀ =>
      2 * (cP * x.1 ^ 2 + cW * x.1) + x.1 * nN x + x.1 * nDnat x) := by
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · have r0 := hr.2 x
      have r1 : x.1 ≤ y.1 := hxy
      have a1 : cP * x.1 ^ 2 ≤ cP * y.1 ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ r0 r1 2) hcP
      have a2 : cW * x.1 ≤ cW * y.1 := mul_le_mul_of_nonneg_left r1 hcW
      have a3 : x.1 * nN x ≤ y.1 * nN y := mul_le_mul r1 (hN.1 hxy) (hN.2 x) (r0.trans r1)
      have a4 : x.1 * nDnat x ≤ y.1 * nDnat y := mul_le_mul r1 (hDn.1 hxy) (hDn.2 x) (r0.trans r1)
      linarith
    · have r0 := hr.2 x
      have := hN.2 x
      have := hDn.2 x
      positivity
  have h2 : Admissible (fun x : Box p₀ =>
      2 * (x.1 ^ 2 * max (nz₁ x) (nz₃ x)) + x.1 * nN x + x.1 * min (nDord x) (nDnat x)) := by
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · have r0 := hr.2 x
      have r1 : x.1 ≤ y.1 := hxy
      have a1 : x.1 ^ 2 * max (nz₁ x) (nz₃ x) ≤ y.1 ^ 2 * max (nz₁ y) (nz₃ y) :=
        mul_le_mul (pow_le_pow_left₀ r0 r1 2) (hz.1 hxy) (hz.2 x) (sq_nonneg _)
      have a3 : x.1 * nN x ≤ y.1 * nN y := mul_le_mul r1 (hN.1 hxy) (hN.2 x) (r0.trans r1)
      have a4 : x.1 * min (nDord x) (nDnat x) ≤ y.1 * min (nDord y) (nDnat y) :=
        mul_le_mul r1 (hD.1 hxy) (hD.2 x) (r0.trans r1)
      linarith
    · have r0 := hr.2 x
      have := hN.2 x
      have := hz.2 x
      have := hD.2 x
      positivity
  exact admissible_min h1 h2

/-- **`lem:upper-completed-root`, proof of (i)–(ii), the derived inputs**: with `ε_Z(r₀) < 1`,
`R_Z = 1/(1 - ε_Z)`, `ε_ϱ/r`, `ε_ϱ = r(ε_ϱ/r)` and `c_⊥` are admissible
(`lem:spectral-monotone`(c)). -/
theorem completed_inputs_admissible {cP cW : ℝ} (hcP : 0 ≤ cP) (hcW : 0 ≤ cW)
    {nN nDord nDnat nM₁ nM₃ nz₁ nz₃ : Box p₀ → ℝ} (hN : Admissible nN)
    (hDo : Admissible nDord) (hDn : Admissible nDnat) (hM₁ : Admissible nM₁)
    (hM₃ : Admissible nM₃) (hz₁ : Admissible nz₁) (hz₃ : Admissible nz₃) (top : Box p₀)
    (htop : ∀ x, x ≤ top) (hZ1 : completedEpsZ cP cW nN nDord nDnat nz₁ nz₃ top < 1) :
    Admissible (fun x => 1 / (1 - completedEpsZ cP cW nN nDord nDnat nz₁ nz₃ x)) ∧
    Admissible (completedRhoR cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃) ∧
    Admissible (fun x : Box p₀ => x.1 * completedRhoR cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃ x) ∧
    Admissible (completedCperp cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃) := by
  have hZ := completed_epsZ_admissible hcP hcW hN hDo hDn hz₁ hz₃
  have h := spectral_monotone_c (fun x : Box p₀ => x.1) nN (fun x => min (nDord x) (nDnat x))
    (fun x => max (nM₁ x) (nM₃ x)) _ (admissible_coord p₀) hN (admissible_min hDo hDn)
    (admissible_max hM₁ hM₃) hZ top htop hZ1
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- **`lem:upper-completed-root`(ii), the coupling inputs**: the minima
`ε_H = min(ε'_H + ε_X, ε^loc_H)`, `Γ_E = min(Ê², Γ^loc_E)` and `ζ̄ = min(ζ₁, ζ₂)` of admissible
functions are admissible (`lem:majorant`(ii)). -/
theorem completed_coupling_admissible {Δ : Type*} [Preorder Δ]
    {εH' εX εHloc E2 ΓEloc ζ₁ ζ₂ : Δ → ℝ} (h1 : Admissible εH') (h2 : Admissible εX)
    (h3 : Admissible εHloc) (h4 : Admissible E2) (h5 : Admissible ΓEloc) (h6 : Admissible ζ₁)
    (h7 : Admissible ζ₂) :
    Admissible (fun x => min (εH' x + εX x) (εHloc x)) ∧
    Admissible (fun x => min (E2 x) (ΓEloc x)) ∧ Admissible (fun x => min (ζ₁ x) (ζ₂ x)) :=
  ⟨admissible_min (admissible_add h1 h2) h3, admissible_min h4 h5, admissible_min h6 h7⟩

end Inputs

section Criterion

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- **`lem:upper-completed-root`, the conclusions at every prime `p ≥ p₀`** (of the class whose
tests are given). The Route A data at `p` (`RouteAInputs`) carry the perpendicular bound
`a_⊥ = R_Z(N_ns + D_col)` and `ε_ϱ = R_Z(M_⋆ + N_ns + D_col)` formed with the inputs (i) at
`r = p^{-1/2}`; `η_Q`, `η_B`, `ε_V` are admissible (`lem:spectral-monotone`(a),(b),(d), with the
coupling inputs (ii)); the endpoint values give `ε_Z < 1`, `c_⊥ ≤ c̄_⊥`, `η_Q ≤ η̄_Q`, `η_B ≤ η̄_B`,
`ε_V ≤ ε̄_V < 1`, and the matrix tests `eq:spectral-test` hold for both signs at `r₀`. Then, with
`g ≥ g_𝔠` and `g' ≥ g` with `g' r₀ < 1`: `Op ⪰ -g r`, `|⟪h, Op h⟫| ≤ g r ‖h‖²` on `h ⊥ 1`,
`‖ϱ - 1‖ ≤ ε_ϱ` with `p ε_ϱ² ≤ p₀ ε_ϱ(r₀)²`, and `Op ⪯ 1 + B_top/p`,
`B_top = p₀ ε_ϱ(r₀)²/(1 - g' r₀)`. -/
theorem upper_completed_root_prime [FiniteDimensional 𝕜 H] {T : H →ₗ[𝕜] H} {one : H}
    {V Sp Sm : Submodule 𝕜 H} {Ξ n : Type*} [Fintype Ξ] [Fintype n] [DecidableEq n]
    {sgn : Ξ → Prop} [DecidablePred sgn] {coef : H → Ξ → n → 𝕜}
    (Aplus X : Matrix n n 𝕜) {p p₀ : ℝ} (hp₀ : 0 < p₀) (hpp : p₀ ≤ p)
    {cP cW : ℝ} (hcP : 0 ≤ cP) (hcW : 0 ≤ cW)
    (nN nDord nDnat nM₁ nM₃ nz₁ nz₃ : Box p₀ → ℝ) (hN : Admissible nN)
    (hDo : Admissible nDord) (hDn : Admissible nDnat) (hM₁ : Admissible nM₁)
    (hM₃ : Admissible nM₃) (hz₁ : Admissible nz₁) (hz₃ : Admissible nz₃)
    (ηQf ηBf εVf : Box p₀ → ℝ) (hηQA : Admissible ηQf) (hηBA : Admissible ηBf)
    (hεVA : Admissible εVf)
    (hr : 0 < 1 / √p ∧ 1 / √p ≤ 1 / √p₀) (top : Box p₀) (htop : top.1 = 1 / √p₀)
    (hZ1 : completedEpsZ cP cW nN nDord nDnat nz₁ nz₃ top < 1)
    (hin : RouteAInputs T one V Sp Sm sgn coef
      (fun ξ x => re (star x ⬝ᵥ ((if sgn ξ then Aplus else -Aplus) *ᵥ x)))
      (fun _ x => re (star x ⬝ᵥ (X *ᵥ x))) (1 / √p) (ηQf ⟨1 / √p, hr⟩) (ηBf ⟨1 / √p, hr⟩)
      (εVf ⟨1 / √p, hr⟩)
      (1 / √p * completedRhoR cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃ ⟨1 / √p, hr⟩)
      (1 / √p * (1 / (1 - completedEpsZ cP cW nN nDord nDnat nz₁ nz₃ ⟨1 / √p, hr⟩) *
        (nN ⟨1 / √p, hr⟩ + min (nDord ⟨1 / √p, hr⟩) (nDnat ⟨1 / √p, hr⟩)))))
    {cbar ηQbar ηBbar εVbar τp τm g g' : ℝ} (hcbar0 : 0 ≤ cbar)
    (hc0 : completedCperp cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃ top ≤ cbar)
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
    (‖T one - one‖ ≤ 1 / √p * completedRhoR cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃ ⟨1 / √p, hr⟩ ∧
      p * (1 / √p * completedRhoR cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃ ⟨1 / √p, hr⟩) ^ 2 ≤
        p₀ * (1 / √p₀ * completedRhoR cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃ top) ^ 2) ∧
    (∀ F : H, re ⟪F, T F⟫ ≤
      (1 + p₀ * (1 / √p₀ * completedRhoR cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃ top) ^ 2 /
        (1 - g' * (1 / √p₀)) / p) * ‖F‖ ^ 2) := by
  have htop' : ∀ x : Box p₀, x ≤ top := fun x => by
    show x.1 ≤ top.1
    rw [htop]
    exact x.2.2
  obtain ⟨-, hρA, -, hcA⟩ := completed_inputs_admissible hcP hcW hN hDo hDn hM₁ hM₃ hz₁ hz₃ top
    htop' hZ1
  have hcp : (1 / √p * (1 / (1 - completedEpsZ cP cW nN nDord nDnat nz₁ nz₃ ⟨1 / √p, hr⟩) *
        (nN ⟨1 / √p, hr⟩ + min (nDord ⟨1 / √p, hr⟩) (nDnat ⟨1 / √p, hr⟩))) +
      (1 / √p * completedRhoR cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃ ⟨1 / √p, hr⟩) ^ 2) /
        (1 / √p) = completedCperp cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃ ⟨1 / √p, hr⟩ := by
    have key : ∀ (r a ρ : ℝ), r ≠ 0 → (r * a + (r * ρ) ^ 2) / r = a + r * ρ ^ 2 := by
      intro r a ρ hr0
      field_simp
    exact key _ _ _ hr.1.ne'
  exact spectral_criterion_uniform Aplus X hp₀ hpp
    (completedCperp cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃) ηQf ηBf εVf
    (completedRhoR cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃) hcA hηQA hηBA hεVA hρA hr top htop hin
    hcp hcbar0 hc0 hηQ0 hηB0 hεV0 hεVbar0 hεV1 hτp hτm htestp htestm hgp hgm hgg' hg'r

end Criterion

/-- **`lem:upper-completed-root`, the block statement.** If at every prime `p_i` of a block
(`p_i ≥ b ≥ X ≥ p₀`, `b` the least prime, `∑ log p_i ≤ L_u`) the root cut operator satisfies the
two conclusions `Op ⪰ -g p^{-1/2}` and `Op ⪯ 1 + B_top/p` of `upper_completed_root_prime`, with
`B_top = p₀ ε_ϱ(r₀)²/(1 - g r₀)` and `g r₀ < 1`, then the normalized block root operator is at
least `-d b^{-1/2}`, `d = g exp(B_top L_u/(X log X))` (`cor:spectral-criterion-blocks` with
`P = X`). -/
theorem upper_completed_root_block {U : Type*} [Fintype U] [DecidableEq U]
    (D : Sarkozy.Cuts.SpecData U) {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
    [∀ i, Fact (p i).Prime] (hne : ∀ i, (Labellings.injLabellings (ZMod (p i)) D.G).Nonempty)
    {g ερ₀ p₀ X L b : ℝ} (hg : 0 ≤ g) (hp₀ : 0 < p₀) (hp₀X : p₀ ≤ X) (hX : 1 < X)
    (hXb : X ≤ b) (hbp : ∀ i, b ≤ p i) (hL : ∑ i, Real.log (p i) ≤ L)
    (hgr₀ : g * (1 / √p₀) < 1)
    (hlow : ∀ i v, -(g * (√(p i : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp D (hne i) v⟫_ℝ)
    (hup : ∀ i v, ⟪v, Spectral.cutOp D (hne i) v⟫_ℝ ≤
      (1 + p₀ * ερ₀ ^ 2 / (1 - g * (1 / √p₀)) / p i) * ‖v‖ ^ 2)
    (Fn : (∀ i, D.cut.Half → ZMod (p i)) → ℝ) :
    -(g * Real.exp (p₀ * ερ₀ ^ 2 / (1 - g * (1 / √p₀)) * L / (X * Real.log X)) * (√b)⁻¹) *
        Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hne i)) Fn ^ 2 ≤
      Sarkozy.Cuts.kernelForm (FiniteLaw.pi fun i => D.halfLaw (hne i))
        (FiniteLaw.pi fun i => D.halfLaw (hne i))
        (fun x y => ∏ i, D.cutK (x i) (y i) / D.cutZ (hne i)) Fn Fn := by
  have hB : 0 ≤ p₀ * ερ₀ ^ 2 / (1 - g * (1 / √p₀)) :=
    div_nonneg (mul_nonneg hp₀.le (sq_nonneg _)) (by linarith)
  refine monotone_endpoint_block D p hne hg hB hp₀ hp₀X hX hXb hbp hL ?_ hlow hup Fn
  rwa [one_div] at hgr₀

end Sarkozy.UpperReference
