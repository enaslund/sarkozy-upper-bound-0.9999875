module

public import Sarkozy.SpectralD.CxRealization
public import Sarkozy.SpectralD.RootCuts
public import Sarkozy.UpperReference.MonotoneEndpoint
public import Sarkozy.UpperReference.CompletedRoot

/-!
# The root caps of LL20 and LL22 for the concrete root cuts

`paper/sections/25_upper_reference.tex`, `subsec:record:upper_root`:
`lem:record:monotone-endpoint` (Route B, the bands below `2⁵²`) and `lem:upper-completed-root`
(Route A, from `2⁵²` on), specialized to S1's concrete root cuts `SpectralD.Root.LL20` and
`SpectralD.Root.LL22` (`Cuts.SpecData Slot`).

* `RouteBData`: **the Route B data of a cut at one prime, as a named hypothesis.** For the
  complex realization `Cx.cutOpC D` of the cut operator (`SpectralD/CxRealization.lean`), with
  the mode index `Ξ`, the matrices `D = ε_G Δ^E` and `𝐑`: (H1) on every mode with the frame
  numbers `ε_V, ε_×, ε_𝐁` of `lem:record:frame-inputs`, the mode identity defining `𝐋`, and the
  decomposition (b) of `thm:record:direct-star` with the inputs (H3) of
  `lem:record:direct-star-inputs`. The kernel identity (b) (`lem:spec:stars`, the explicit-stars
  mode) and (H1) for the root cuts are not formalized; this structure names them.
* `real_bounds_of_complex`: bounds on `cutOpC` give the same bounds on WP-A's real `cutOp`
  (`Cx.inner_embedR_cutOp`).
* `rootcut_prime`: `lem:record:monotone-endpoint` at one prime for a concrete cut: from
  `RouteBData` at `p`, frame numbers at most the endpoint ones, the endpoint Schur tests and the
  endpoint inputs, `-g₀ r ⪯ cutOp ⪯ 1 + B₀ r²` on the real cut operator.
* `LL20_routeB_block`, `LL22_routeB_block`: the block statement of
  `lem:record:monotone-endpoint` for the concrete root cuts: with the data at every prime of the
  block, `⊗ Op ⪰ -g₀ exp(B₀ L/(X log X)) b^{-1/2}`.
* `LL20_routeA_block`, `LL22_routeA_block`: the block statement of `lem:upper-completed-root`
  for the concrete root cuts, from the per-prime Route A bounds (for instance S1's
  `SpectralD.Root.LL20_criterion` for the lower bound at `p ≥ 2⁵²`).

**Named hypotheses** (not formalized, see S1's report, "Follow-up 3"): the Route B kernel
identity below `2⁵²` (`RouteBData`, labels `thm:record:direct-star`(b), `lem:spec:stars`,
`lem:record:frame-inputs`); the refined coupling inputs of `lem:upper-completed-root`(ii),
`Γ^loc_E` (`lem:projection-diagonal` with `lem:push:localvariance`) and `ε^loc_H`
(`lem:push:conditionalgram`), which enter Route A through the per-prime bounds (`hlow`, `hup`).
-/

@[expose] public section

open scoped BigOperators InnerProductSpace ComplexConjugate Matrix ComplexOrder
open RCLike

namespace Sarkozy.UpperReference

open Sarkozy Sarkozy.Spectral

section Data

variable {U : Type*} [Fintype U] [DecidableEq U]

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

/-- **The Route B data of the cut `D` at the prime `p`** (named hypothesis:
`thm:record:direct-star`(H1) with the numbers of `lem:record:frame-inputs`, the mode identity of
`𝐋`, and the decomposition (b), with the inputs (H3) of `lem:record:direct-star-inputs`), for the
complex cut operator `Cx.cutOpC D hne` on `L²(λ(G⁺))`. The fields are the hypotheses of
`Sarkozy.Spectral.direct_star_explicit` other than the Schur test (H2) and `ε_Z < 1`. -/
structure RouteBData (D : Cuts.SpecData U) {p : ℕ} [Fact p.Prime]
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) (Ξ : Type*) [Fintype Ξ]
    (n : Type*) [Fintype n] (Dm R : Matrix n n ℂ)
    (εV εx εB Λ r εsoft Mstar zstar Nns Dcol : ℝ) : Prop where
  data : ∃ (E Bn : Ξ → (n → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (D.cut.Half → ZMod p))
    (cE cB : EuclideanSpace ℂ (D.cut.Half → ZMod p) → Ξ → n → ℂ) (A : Ξ → Matrix n n ℂ)
    (Hm : Matrix n n ℂ)
    (K₀ L Soft Tns Tcoll : EuclideanSpace ℂ (D.cut.Half → ZMod p) →ₗ[ℂ]
      EuclideanSpace ℂ (D.cut.Half → ZMod p)) (hs : EuclideanSpace ℂ (D.cut.Half → ZMod p))
    (Z₀ : ℝ),
    (∀ f ξ z, ⟪E ξ z, f⟫ = star z ⬝ᵥ cE f ξ) ∧
    (∀ f ξ z, ⟪Bn ξ z, f⟫ = star z ⬝ᵥ cB f ξ) ∧
    (∀ ξ ξ', ξ ≠ ξ' → ∀ u v u' v', ⟪E ξ u + Bn ξ v, E ξ' u' + Bn ξ' v'⟫ = 0) ∧
    (∀ ξ, A ξ = Dm ∨ A ξ = -Dm) ∧
    (∀ v, sqn (Dm *ᵥ v) ≤ Λ ^ 2 * sqn v) ∧
    (∀ v, qform R v v = qform Hm v v - sqn (Dm *ᵥ v)) ∧
    (∀ ξ u w, ‖⟪E ξ u, E ξ w⟫ - star u ⬝ᵥ w‖ ≤ εV * √(sqn u) * √(sqn w)) ∧
    (∀ ξ u v, ‖⟪E ξ u, Bn ξ v⟫ - star u ⬝ᵥ (A ξ *ᵥ v)‖ ≤ εx * √(sqn u) * √(sqn v)) ∧
    (∀ ξ v, ‖Bn ξ v‖ ^ 2 ≤ qform Hm v v + εB * sqn v) ∧
    (∀ f, re ⟪f, L f⟫ = r * ∑ ξ, (qform (A ξ) (cE f ξ) (cE f ξ) +
      2 * re (star (cE f ξ) ⬝ᵥ (cB f ξ - (A ξ)ᴴ *ᵥ cE f ξ)))) ∧
    (∀ x, SpectralD.Cx.cutOpC D hne x = ((Z₀⁻¹ : ℝ) : ℂ) • K₀ x) ∧
    ⟪SpectralD.Cx.cutOneC D hne, K₀ (SpectralD.Cx.cutOneC D hne)⟫ = (Z₀ : ℂ) ∧
    (∀ x, K₀ x = ⟪SpectralD.Cx.cutOneC D hne + hs, x⟫ • (SpectralD.Cx.cutOneC D hne + hs) +
      L x + (Soft x - ⟪hs, x⟫ • hs + (Tns x - Tcoll x))) ∧
    L (SpectralD.Cx.cutOneC D hne) = 0 ∧ Soft (SpectralD.Cx.cutOneC D hne) = 0 ∧
    (∀ x, ‖Soft x‖ ≤ εsoft * ‖x‖) ∧ (∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) ∧
    (∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖) ∧
    ‖hs - ⟪SpectralD.Cx.cutOneC D hne, hs⟫ • SpectralD.Cx.cutOneC D hne‖ ≤ Mstar ∧
    ‖⟪SpectralD.Cx.cutOneC D hne, hs⟫‖ ≤ zstar

/-- `‖1‖ = 1` in the complex realization. -/
theorem norm_cutOneC (D : Cuts.SpecData U) {p : ℕ} [Fact p.Prime]
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) :
    ‖SpectralD.Cx.cutOneC D hne‖ = 1 := by
  rw [← SpectralD.Cx.embedR_cutOne, SpectralD.Cx.norm_embedR, Spectral.norm_cutOne]

/-- **Bounds on the complex cut operator give the bounds on the real one** (the real quadratic
form is the complex one on embedded vectors, `Cx.inner_embedR_cutOp`). -/
theorem real_bounds_of_complex (D : Cuts.SpecData U) {p : ℕ} [Fact p.Prime]
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) {a b : ℝ}
    (hlow : ∀ F, -a * ‖F‖ ^ 2 ≤ re ⟪F, SpectralD.Cx.cutOpC D hne F⟫)
    (hup : ∀ F, re ⟪F, SpectralD.Cx.cutOpC D hne F⟫ ≤ b * ‖F‖ ^ 2) :
    (∀ v, -a * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp D hne v⟫_ℝ) ∧
      (∀ v, ⟪v, Spectral.cutOp D hne v⟫_ℝ ≤ b * ‖v‖ ^ 2) := by
  constructor
  · intro v
    have h := hlow (SpectralD.Cx.embedR v)
    rwa [SpectralD.Cx.inner_embedR_cutOp, SpectralD.Cx.norm_embedR, RCLike.re_to_complex,
      Complex.ofReal_re] at h
  · intro v
    have h := hup (SpectralD.Cx.embedR v)
    rwa [SpectralD.Cx.inner_embedR_cutOp, SpectralD.Cx.norm_embedR, RCLike.re_to_complex,
      Complex.ofReal_re] at h

/-- **`lem:record:monotone-endpoint` at one prime, for a concrete cut** (`D = LL20` or `LL22`):
from the Route B data at `p` (`RouteBData`), frame numbers at most those of the endpoint, the
endpoint Schur tests for both signs, `𝐑 ⪰ 0`, `ε_𝐁 > 0`, and inputs with `ε_Z < 1`,
`g_root(p) ≤ g₀`, `ε_ϱ(p)/r ≤ e₀`, `r ≤ r₀`, `g₀ r₀ < 1`, the real cut operator satisfies
`-g₀ r ⪯ cutOp ⪯ 1 + (e₀²/(1 - g₀ r₀)) r²`. -/
theorem rootcut_prime (D : Cuts.SpecData U) {p : ℕ} [Fact p.Prime]
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) {Ξ : Type*} [Fintype Ξ]
    [DecidableEq Ξ] {n : Type*} [Fintype n] [DecidableEq n] (Dm R : Matrix n n ℂ)
    {εV εx εB εV₀ εx₀ εB₀ Λ s g r εsoft Mstar zstar Nns Dcol : ℝ}
    (hdata : RouteBData D hne Ξ n Dm R εV εx εB Λ r εsoft Mstar zstar Nns Dcol)
    (hRpsd : R.PosSemidef) (hεV : 0 ≤ εV) (hεx : 0 ≤ εx) (hεB : 0 < εB) (hΛ0 : 0 ≤ Λ)
    (hs0 : 0 < s) (hg : 0 < g) (hr : 0 < r) (hV : εV ≤ εV₀) (hx : εx ≤ εx₀) (hB : εB ≤ εB₀)
    (htestp₀ : (Dm + ((g / (1 + εV₀ + s) : ℝ) : ℂ) • (1 : Matrix n n ℂ) - ((1 / g : ℝ) : ℂ) •
      (R + ((εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s : ℝ) : ℂ) •
        (1 : Matrix n n ℂ))).PosSemidef)
    (htestm₀ : (-Dm + ((g / (1 + εV₀ + s) : ℝ) : ℂ) • (1 : Matrix n n ℂ) - ((1 / g : ℝ) : ℂ) •
      (R + ((εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s : ℝ) : ℂ) •
        (1 : Matrix n n ℂ))).PosSemidef)
    (hεZ : 2 * zstar + Nns + Dcol < 1) {g₀ e₀ r₀ : ℝ}
    (hgR : (g + (Nns + Dcol + Mstar ^ 2 + zstar ^ 2 + εsoft) / r) /
      (1 - (2 * zstar + Nns + Dcol)) ≤ g₀)
    (her : (Mstar + Nns + Dcol) / (1 - (2 * zstar + Nns + Dcol)) / r ≤ e₀)
    (hrr₀ : r ≤ r₀) (hgr₀ : g₀ * r₀ < 1) :
    (∀ v, -(g₀ * r) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp D hne v⟫_ℝ) ∧
      (∀ v, ⟪v, Spectral.cutOp D hne v⟫_ℝ ≤ (1 + e₀ ^ 2 / (1 - g₀ * r₀) * r ^ 2) * ‖v‖ ^ 2) := by
  obtain ⟨E, Bn, cE, cB, A, Hm, K₀, L, Soft, Tns, Tcoll, hs, Z₀, hcE, hcB, horth, hA, hΛ, hR,
    h1a, h1b, h1c, hL, hT, hZ₀, hb, hL1, hSoft1, hSoft, hns, hcoll, hM, hz⟩ := hdata.data
  have hzs : 2 * ‖⟪SpectralD.Cx.cutOneC D hne, hs⟫‖ ≤ 2 * zstar := by linarith
  obtain ⟨-, hlow, -, hup⟩ := monotone_endpoint_prime (SpectralD.Cx.cutOpC D hne) K₀ L Soft Tns
    Tcoll (SpectralD.Cx.cutOneC D hne) hs (norm_cutOneC D hne) E Bn cE cB hcE hcB horth Dm A hA
    Hm R hRpsd hεV hεx hεB hΛ0 hs0 hg hr hΛ hR h1a h1b h1c hV hx hB htestp₀ htestm₀ hL hT hZ₀
    (SpectralD.Cx.cutOpC_isSymmetric D hne) hb hL1 hSoft1 hSoft hns hcoll hM hz hzs hεZ hgR her
    hrr₀ hgr₀
  exact real_bounds_of_complex D hne hlow hup

end Data

/-! ## The block statements for LL20 and LL22 -/

section Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`lem:record:monotone-endpoint`, the block, for a concrete root cut** (`D = LL20` or `LL22`).
Let the block consist of the primes `p_i ≥ b ≥ X ≥ p₀` with `∑ log p_i ≤ L`, and at every `p_i`
let the Route B data hold (`RouteBData`) with frame numbers at most the endpoint ones and inputs
giving `g_root(p_i) ≤ g₀`, `ε_ϱ(p_i)/r_i ≤ e₀` (`endpoint_numbers`), `r_i = p_i^{-1/2}`,
`r₀ = p₀^{-1/2}`, `g₀ r₀ < 1`. With the endpoint Schur tests, the normalized block root operator
is at least `-d b^{-1/2}`, `d = g₀ exp(B₀ L/(X log X))`, `B₀ = e₀²/(1 - g₀ r₀)`. -/
theorem rootcut_routeB_block {U : Type*} [Fintype U] [DecidableEq U] (D : Cuts.SpecData U)
    (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hne : ∀ i, (Labellings.injLabellings (ZMod (p i)) D.G).Nonempty)
    {Ξ : ι → Type*} [∀ i, Fintype (Ξ i)] [∀ i, DecidableEq (Ξ i)] {n : Type*} [Fintype n]
    [DecidableEq n] (Dm R : Matrix n n ℂ)
    (εV εx εB εsoft Mstar zstar Nns Dcol : ι → ℝ) {εV₀ εx₀ εB₀ Λ s g g₀ e₀ p₀ X L b : ℝ}
    (hdata : ∀ i, RouteBData D (hne i) (Ξ i) n Dm R (εV i) (εx i) (εB i) Λ (√(p i : ℝ))⁻¹
      (εsoft i) (Mstar i) (zstar i) (Nns i) (Dcol i))
    (hRpsd : R.PosSemidef) (hεV : ∀ i, 0 ≤ εV i) (hεx : ∀ i, 0 ≤ εx i) (hεB : ∀ i, 0 < εB i)
    (hΛ0 : 0 ≤ Λ) (hs0 : 0 < s) (hg : 0 < g)
    (hV : ∀ i, εV i ≤ εV₀) (hx : ∀ i, εx i ≤ εx₀) (hB : ∀ i, εB i ≤ εB₀)
    (htestp₀ : (Dm + ((g / (1 + εV₀ + s) : ℝ) : ℂ) • (1 : Matrix n n ℂ) - ((1 / g : ℝ) : ℂ) •
      (R + ((εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s : ℝ) : ℂ) •
        (1 : Matrix n n ℂ))).PosSemidef)
    (htestm₀ : (-Dm + ((g / (1 + εV₀ + s) : ℝ) : ℂ) • (1 : Matrix n n ℂ) - ((1 / g : ℝ) : ℂ) •
      (R + ((εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s : ℝ) : ℂ) •
        (1 : Matrix n n ℂ))).PosSemidef)
    (hεZ : ∀ i, 2 * zstar i + Nns i + Dcol i < 1)
    (hgR : ∀ i, (g + (Nns i + Dcol i + Mstar i ^ 2 + zstar i ^ 2 + εsoft i) / (√(p i : ℝ))⁻¹) /
      (1 - (2 * zstar i + Nns i + Dcol i)) ≤ g₀)
    (her : ∀ i, (Mstar i + Nns i + Dcol i) / (1 - (2 * zstar i + Nns i + Dcol i)) /
      (√(p i : ℝ))⁻¹ ≤ e₀)
    (hp₀ : 0 < p₀) (hp₀X : p₀ ≤ X) (hX : 1 < X) (hXb : X ≤ b) (hbp : ∀ i, b ≤ p i)
    (hL : ∑ i, Real.log (p i) ≤ L) (hg₀ : 0 ≤ g₀) (hgr₀ : g₀ * (√p₀)⁻¹ < 1)
    (Fn : (∀ i, D.cut.Half → ZMod (p i)) → ℝ) :
    -(g₀ * Real.exp (e₀ ^ 2 / (1 - g₀ * (√p₀)⁻¹) * L / (X * Real.log X)) * (√b)⁻¹) *
        Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hne i)) Fn ^ 2 ≤
      Sarkozy.Cuts.kernelForm (FiniteLaw.pi fun i => D.halfLaw (hne i))
        (FiniteLaw.pi fun i => D.halfLaw (hne i))
        (fun x y => ∏ i, D.cutK (x i) (y i) / D.cutZ (hne i)) Fn Fn := by
  have hpi : ∀ i, p₀ ≤ (p i : ℝ) := fun i => hp₀X.trans (hXb.trans (hbp i))
  have hppos : ∀ i, 0 < (p i : ℝ) := fun i => lt_of_lt_of_le hp₀ (hpi i)
  have hrr : ∀ i, (√(p i : ℝ))⁻¹ ≤ (√p₀)⁻¹ := fun i =>
    inv_anti₀ (Real.sqrt_pos.mpr hp₀) (Real.sqrt_le_sqrt (hpi i))
  have hB₀ : 0 ≤ e₀ ^ 2 / (1 - g₀ * (√p₀)⁻¹) := div_nonneg (sq_nonneg _) (by linarith)
  have hprime := fun i => rootcut_prime D (hne i) Dm R (hdata i) hRpsd (hεV i) (hεx i) (hεB i)
    hΛ0 hs0 hg (inv_pos.mpr (Real.sqrt_pos.mpr (hppos i))) (hV i) (hx i) (hB i) htestp₀
    htestm₀ (hεZ i) (hgR i) (her i) (hrr i) hgr₀
  refine monotone_endpoint_block D p hne hg₀ hB₀ hp₀ hp₀X hX hXb hbp hL hgr₀
    (fun i v => (hprime i).1 v) (fun i v => ?_) Fn
  have h := (hprime i).2 v
  have hsq : ((√(p i : ℝ))⁻¹) ^ 2 = 1 / (p i : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (hppos i).le, one_div]
  rw [hsq] at h
  calc ⟪v, Spectral.cutOp D (hne i) v⟫_ℝ ≤
        (1 + e₀ ^ 2 / (1 - g₀ * (√p₀)⁻¹) * (1 / (p i : ℝ))) * ‖v‖ ^ 2 := h
    _ = (1 + e₀ ^ 2 / (1 - g₀ * (√p₀)⁻¹) / (p i : ℝ)) * ‖v‖ ^ 2 := by ring

/-- **`lem:record:monotone-endpoint`, the block, for the root cut LL20.** -/
theorem LL20_routeB_block (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hne : ∀ i, (Labellings.injLabellings (ZMod (p i)) SpectralD.Root.LL20.G).Nonempty)
    {Ξ : ι → Type*} [∀ i, Fintype (Ξ i)] [∀ i, DecidableEq (Ξ i)] {n : Type*} [Fintype n]
    [DecidableEq n] (Dm R : Matrix n n ℂ)
    (εV εx εB εsoft Mstar zstar Nns Dcol : ι → ℝ) {εV₀ εx₀ εB₀ Λ s g g₀ e₀ p₀ X L b : ℝ}
    (hdata : ∀ i, RouteBData SpectralD.Root.LL20 (hne i) (Ξ i) n Dm R (εV i) (εx i) (εB i) Λ
      (√(p i : ℝ))⁻¹ (εsoft i) (Mstar i) (zstar i) (Nns i) (Dcol i))
    (hRpsd : R.PosSemidef) (hεV : ∀ i, 0 ≤ εV i) (hεx : ∀ i, 0 ≤ εx i) (hεB : ∀ i, 0 < εB i)
    (hΛ0 : 0 ≤ Λ) (hs0 : 0 < s) (hg : 0 < g)
    (hV : ∀ i, εV i ≤ εV₀) (hx : ∀ i, εx i ≤ εx₀) (hB : ∀ i, εB i ≤ εB₀)
    (htestp₀ : (Dm + ((g / (1 + εV₀ + s) : ℝ) : ℂ) • (1 : Matrix n n ℂ) - ((1 / g : ℝ) : ℂ) •
      (R + ((εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s : ℝ) : ℂ) •
        (1 : Matrix n n ℂ))).PosSemidef)
    (htestm₀ : (-Dm + ((g / (1 + εV₀ + s) : ℝ) : ℂ) • (1 : Matrix n n ℂ) - ((1 / g : ℝ) : ℂ) •
      (R + ((εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s : ℝ) : ℂ) •
        (1 : Matrix n n ℂ))).PosSemidef)
    (hεZ : ∀ i, 2 * zstar i + Nns i + Dcol i < 1)
    (hgR : ∀ i, (g + (Nns i + Dcol i + Mstar i ^ 2 + zstar i ^ 2 + εsoft i) / (√(p i : ℝ))⁻¹) /
      (1 - (2 * zstar i + Nns i + Dcol i)) ≤ g₀)
    (her : ∀ i, (Mstar i + Nns i + Dcol i) / (1 - (2 * zstar i + Nns i + Dcol i)) /
      (√(p i : ℝ))⁻¹ ≤ e₀)
    (hp₀ : 0 < p₀) (hp₀X : p₀ ≤ X) (hX : 1 < X) (hXb : X ≤ b) (hbp : ∀ i, b ≤ p i)
    (hL : ∑ i, Real.log (p i) ≤ L) (hg₀ : 0 ≤ g₀) (hgr₀ : g₀ * (√p₀)⁻¹ < 1)
    (Fn : (∀ i, SpectralD.Root.LL20.cut.Half → ZMod (p i)) → ℝ) :
    -(g₀ * Real.exp (e₀ ^ 2 / (1 - g₀ * (√p₀)⁻¹) * L / (X * Real.log X)) * (√b)⁻¹) *
        Recentering.nrm (FiniteLaw.pi fun i => SpectralD.Root.LL20.halfLaw (hne i)) Fn ^ 2 ≤
      Sarkozy.Cuts.kernelForm (FiniteLaw.pi fun i => SpectralD.Root.LL20.halfLaw (hne i))
        (FiniteLaw.pi fun i => SpectralD.Root.LL20.halfLaw (hne i))
        (fun x y => ∏ i, SpectralD.Root.LL20.cutK (x i) (y i) /
          SpectralD.Root.LL20.cutZ (hne i)) Fn Fn :=
  rootcut_routeB_block SpectralD.Root.LL20 p hne Dm R εV εx εB εsoft Mstar zstar Nns Dcol hdata
    hRpsd hεV hεx hεB hΛ0 hs0 hg hV hx hB htestp₀ htestm₀ hεZ hgR her hp₀ hp₀X hX hXb hbp hL hg₀
    hgr₀ Fn

/-- **`lem:record:monotone-endpoint`, the block, for the root cut LL22.** -/
theorem LL22_routeB_block (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hne : ∀ i, (Labellings.injLabellings (ZMod (p i)) SpectralD.Root.LL22.G).Nonempty)
    {Ξ : ι → Type*} [∀ i, Fintype (Ξ i)] [∀ i, DecidableEq (Ξ i)] {n : Type*} [Fintype n]
    [DecidableEq n] (Dm R : Matrix n n ℂ)
    (εV εx εB εsoft Mstar zstar Nns Dcol : ι → ℝ) {εV₀ εx₀ εB₀ Λ s g g₀ e₀ p₀ X L b : ℝ}
    (hdata : ∀ i, RouteBData SpectralD.Root.LL22 (hne i) (Ξ i) n Dm R (εV i) (εx i) (εB i) Λ
      (√(p i : ℝ))⁻¹ (εsoft i) (Mstar i) (zstar i) (Nns i) (Dcol i))
    (hRpsd : R.PosSemidef) (hεV : ∀ i, 0 ≤ εV i) (hεx : ∀ i, 0 ≤ εx i) (hεB : ∀ i, 0 < εB i)
    (hΛ0 : 0 ≤ Λ) (hs0 : 0 < s) (hg : 0 < g)
    (hV : ∀ i, εV i ≤ εV₀) (hx : ∀ i, εx i ≤ εx₀) (hB : ∀ i, εB i ≤ εB₀)
    (htestp₀ : (Dm + ((g / (1 + εV₀ + s) : ℝ) : ℂ) • (1 : Matrix n n ℂ) - ((1 / g : ℝ) : ℂ) •
      (R + ((εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s : ℝ) : ℂ) •
        (1 : Matrix n n ℂ))).PosSemidef)
    (htestm₀ : (-Dm + ((g / (1 + εV₀ + s) : ℝ) : ℂ) • (1 : Matrix n n ℂ) - ((1 / g : ℝ) : ℂ) •
      (R + ((εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s : ℝ) : ℂ) •
        (1 : Matrix n n ℂ))).PosSemidef)
    (hεZ : ∀ i, 2 * zstar i + Nns i + Dcol i < 1)
    (hgR : ∀ i, (g + (Nns i + Dcol i + Mstar i ^ 2 + zstar i ^ 2 + εsoft i) / (√(p i : ℝ))⁻¹) /
      (1 - (2 * zstar i + Nns i + Dcol i)) ≤ g₀)
    (her : ∀ i, (Mstar i + Nns i + Dcol i) / (1 - (2 * zstar i + Nns i + Dcol i)) /
      (√(p i : ℝ))⁻¹ ≤ e₀)
    (hp₀ : 0 < p₀) (hp₀X : p₀ ≤ X) (hX : 1 < X) (hXb : X ≤ b) (hbp : ∀ i, b ≤ p i)
    (hL : ∑ i, Real.log (p i) ≤ L) (hg₀ : 0 ≤ g₀) (hgr₀ : g₀ * (√p₀)⁻¹ < 1)
    (Fn : (∀ i, SpectralD.Root.LL22.cut.Half → ZMod (p i)) → ℝ) :
    -(g₀ * Real.exp (e₀ ^ 2 / (1 - g₀ * (√p₀)⁻¹) * L / (X * Real.log X)) * (√b)⁻¹) *
        Recentering.nrm (FiniteLaw.pi fun i => SpectralD.Root.LL22.halfLaw (hne i)) Fn ^ 2 ≤
      Sarkozy.Cuts.kernelForm (FiniteLaw.pi fun i => SpectralD.Root.LL22.halfLaw (hne i))
        (FiniteLaw.pi fun i => SpectralD.Root.LL22.halfLaw (hne i))
        (fun x y => ∏ i, SpectralD.Root.LL22.cutK (x i) (y i) /
          SpectralD.Root.LL22.cutZ (hne i)) Fn Fn :=
  rootcut_routeB_block SpectralD.Root.LL22 p hne Dm R εV εx εB εsoft Mstar zstar Nns Dcol hdata
    hRpsd hεV hεx hεB hΛ0 hs0 hg hV hx hB htestp₀ htestm₀ hεZ hgR her hp₀ hp₀X hX hXb hbp hL hg₀
    hgr₀ Fn

/-- **`lem:upper-completed-root`, the block, for the root cut LL20** (from `2⁵²` on): from the
per-prime Route A bounds `Op ⪰ -g p^{-1/2}` (for instance `SpectralD.Root.LL20_criterion`) and
`Op ⪯ 1 + B_top/p`, `B_top = p₀ ε_ϱ(r₀)²/(1 - g r₀)`. -/
theorem LL20_routeA_block (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hne : ∀ i, (Labellings.injLabellings (ZMod (p i)) SpectralD.Root.LL20.G).Nonempty)
    {g ερ₀ p₀ X L b : ℝ} (hg : 0 ≤ g) (hp₀ : 0 < p₀) (hp₀X : p₀ ≤ X) (hX : 1 < X)
    (hXb : X ≤ b) (hbp : ∀ i, b ≤ p i) (hL : ∑ i, Real.log (p i) ≤ L)
    (hgr₀ : g * (1 / √p₀) < 1)
    (hlow : ∀ i v, -(g * (√(p i : ℝ))⁻¹) * ‖v‖ ^ 2 ≤
      ⟪v, Spectral.cutOp SpectralD.Root.LL20 (hne i) v⟫_ℝ)
    (hup : ∀ i v, ⟪v, Spectral.cutOp SpectralD.Root.LL20 (hne i) v⟫_ℝ ≤
      (1 + p₀ * ερ₀ ^ 2 / (1 - g * (1 / √p₀)) / p i) * ‖v‖ ^ 2)
    (Fn : (∀ i, SpectralD.Root.LL20.cut.Half → ZMod (p i)) → ℝ) :
    -(g * Real.exp (p₀ * ερ₀ ^ 2 / (1 - g * (1 / √p₀)) * L / (X * Real.log X)) * (√b)⁻¹) *
        Recentering.nrm (FiniteLaw.pi fun i => SpectralD.Root.LL20.halfLaw (hne i)) Fn ^ 2 ≤
      Sarkozy.Cuts.kernelForm (FiniteLaw.pi fun i => SpectralD.Root.LL20.halfLaw (hne i))
        (FiniteLaw.pi fun i => SpectralD.Root.LL20.halfLaw (hne i))
        (fun x y => ∏ i, SpectralD.Root.LL20.cutK (x i) (y i) /
          SpectralD.Root.LL20.cutZ (hne i)) Fn Fn :=
  upper_completed_root_block SpectralD.Root.LL20 p hne hg hp₀ hp₀X hX hXb hbp hL hgr₀ hlow hup Fn

/-- **`lem:upper-completed-root`, the block, for the root cut LL22.** -/
theorem LL22_routeA_block (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hne : ∀ i, (Labellings.injLabellings (ZMod (p i)) SpectralD.Root.LL22.G).Nonempty)
    {g ερ₀ p₀ X L b : ℝ} (hg : 0 ≤ g) (hp₀ : 0 < p₀) (hp₀X : p₀ ≤ X) (hX : 1 < X)
    (hXb : X ≤ b) (hbp : ∀ i, b ≤ p i) (hL : ∑ i, Real.log (p i) ≤ L)
    (hgr₀ : g * (1 / √p₀) < 1)
    (hlow : ∀ i v, -(g * (√(p i : ℝ))⁻¹) * ‖v‖ ^ 2 ≤
      ⟪v, Spectral.cutOp SpectralD.Root.LL22 (hne i) v⟫_ℝ)
    (hup : ∀ i v, ⟪v, Spectral.cutOp SpectralD.Root.LL22 (hne i) v⟫_ℝ ≤
      (1 + p₀ * ερ₀ ^ 2 / (1 - g * (1 / √p₀)) / p i) * ‖v‖ ^ 2)
    (Fn : (∀ i, SpectralD.Root.LL22.cut.Half → ZMod (p i)) → ℝ) :
    -(g * Real.exp (p₀ * ερ₀ ^ 2 / (1 - g * (1 / √p₀)) * L / (X * Real.log X)) * (√b)⁻¹) *
        Recentering.nrm (FiniteLaw.pi fun i => SpectralD.Root.LL22.halfLaw (hne i)) Fn ^ 2 ≤
      Sarkozy.Cuts.kernelForm (FiniteLaw.pi fun i => SpectralD.Root.LL22.halfLaw (hne i))
        (FiniteLaw.pi fun i => SpectralD.Root.LL22.halfLaw (hne i))
        (fun x y => ∏ i, SpectralD.Root.LL22.cutK (x i) (y i) /
          SpectralD.Root.LL22.cutZ (hne i)) Fn Fn :=
  upper_completed_root_block SpectralD.Root.LL22 p hne hg hp₀ hp₀X hX hXb hbp hL hgr₀ hlow hup Fn

end Blocks

end Sarkozy.UpperReference
