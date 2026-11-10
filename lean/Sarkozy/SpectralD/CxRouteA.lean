module

public import Sarkozy.SpectralD.CxSectors

@[expose] public section

/-!
# Route A in the complex realization (`thm:spectral-criterion`, inputs (R1)–(R3))

`paper/sections/14_spectral.tex`, `thm:spectral-criterion` (Route A) and WP-A's abstract form
`Sarkozy.Spectral.RouteAInputs` / `routeA_lower`. In the complex realization of
`CxRealization` (`H = EuclideanSpace ℂ (U → 𝔽_p)`, `T = kernelOpC μ k`, `1 = l2MapC μ 1`,
`𝒱 = degSpace μ`, `coef = degCoef μ`, sectors `secP`, `secM`, `sgn ξ = (ξ ∈ Q, ξ ≠ 0)`):

* `routeAInputs_cx`: **every field of `RouteAInputs`** is proved from the paper's inputs, except
  `rho_bound` (`‖ϱ − 1‖ ≤ ε_ϱ`, `prop:spec2:mucentre`(c3)) and `perp_bound`
  (`|⟪h, Op h⟫| ≤ a_⊥‖h‖²` on `H_⊥`, `prop:spec2:mucentre`(c4)), which stay hypotheses, and the
  coupling bound `CouplingBoundCx` (supplied by `couplingBound_cx` from the coupling data of
  instance (A) and the certified numbers). The degree-one fields are fork D's
  (`CxDegreeOne.cx_degone_fields`), the sectors and the coupling field S1's (`CxSectors`).
* `routeA_lower_cx`: WP-A's criterion `Op ⪰ −g r I` in the complex realization.
* `kernelOp_lower_of_complex`, `cutOp_lower_of_complex`: **the real statement follows**. WP-A's
  real realization embeds (`embedR`), and `⟪f, Op f⟫_ℝ = re⟪embedR f, Op_ℂ embedR f⟫`, so the
  bound for complex `F` gives the bound for the real functions the paper uses.
* `isSquare_neg_iff` and `gSec_conj_three`: for `p ≡ 3 (mod 4)`, `ξ ↦ −ξ` exchanges the two
  sectors, so the sector parts of a real `F_V` are complex conjugates of each other; this is why
  the split needs the complex space.

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate InnerProductSpace

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- **`RouteAInputs` in the complex realization** (`thm:spectral-criterion`, Route A, inputs
(R1)–(R3)). Hypotheses: the half law `μ` (`hμ0`, `hμ1`, `hinv`, `hinj`); the kernel `k`
(symmetric, translation invariant) with its cut law `Λ = cutLaw μ k` (`hΛ1`, `hΛinv`, `hΛinj`,
as in `lem:spec:degone`(a)); the certified bounds `hE` (`‖E_Q(ξ)‖ ≤ η_Q`, `lem:spec:degone`(b))
and `hN` (`‖𝐍(ξ) − I‖ ≤ ε_V`, (c)); `eq:spec:coupling` for every `F_V` (`hbound`, from
`couplingBound_cx`); and the two inputs of `prop:spec2:mucentre`, `hρ` and `hperp`. -/
theorem routeAInputs_cx (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (k : (U → ZMod p) → (U → ZMod p) → ℝ) (hk : ∀ x x', k x x' = k x' x)
    (hkt : ∀ c x x', k (fun j => x j + c) (fun j => x' j + c) = k x x')
    (hΛ1 : ∑ z, cutLaw μ k z = 1)
    (hΛinv : ∀ (s c : ZMod p) (z : (U → ZMod p) × (U → ZMod p)), s ≠ 0 → IsSquare s →
      cutLaw μ k (affLab s c z.1, affLab s c z.2) = cutLaw μ k z)
    (hΛinj : ∀ (z : (U → ZMod p) × (U → ZMod p)) (a b : U), cutLaw μ k z ≠ 0 → z.1 a ≠ z.2 b)
    (ς : U → U → ZMod p) {ηQ εV : ℝ}
    (hE : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (errQ (cutLaw μ k) ς ξ) ηQ)
    (hN : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (fun k l => degoneN μ ξ k l - if k = l then 1 else 0) εV)
    (qX : ZMod p → (U → ℂ) → ℝ) (hqX0 : ∀ ξ, qX ξ 0 = 0) {ηB : ℝ}
    (hbound : CouplingBoundCx μ k qX ηB) {ερ aperp : ℝ}
    (hρ : ‖kernelOpC μ k (l2MapC μ (fun _ => 1)) - l2MapC μ (fun _ => 1)‖ ≤ ερ)
    (hperp : ∀ h, ⟪l2MapC μ (fun _ => 1), h⟫_ℂ = 0 → (∀ v ∈ degSpace μ, ⟪v, h⟫_ℂ = 0) →
      |RCLike.re ⟪h, kernelOpC μ k h⟫_ℂ| ≤ aperp * ‖h‖ ^ 2) :
    Sarkozy.Spectral.RouteAInputs (kernelOpC μ k) (l2MapC μ (fun _ => 1)) (degSpace μ)
      (secP p U) (secM p U) (fun ξ : ZMod p => IsSquare ξ ∧ ξ ≠ 0) (degCoef μ)
      (fun ξ x => (qform (azero ς ξ) x).re) qX (rp p) ηQ ηB εV ερ aperp := by
  obtain ⟨hsymm, hone, hV1, hmean, hρV, hlow, hup, hnorm⟩ :=
    cx_degone_fields hp2 μ hμ0 hμ1 hinv hinj k hk hΛ1 hΛinv hΛinj ς hE hN
  exact ⟨hsymm, hone, hV1, sectors_ortho, hmean, hρV, hρ, hperp, hlow, hup, hnorm,
    cx_coupling μ hinv k hkt qX hqX0 hbound⟩

/-- **`thm:spectral-criterion`(a) in the complex realization**: with `routeAInputs_cx` and
WP-A's finite tests, `Op ⪰ −g r I` on all complex `F`. -/
theorem routeA_lower_cx (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (k : (U → ZMod p) → (U → ZMod p) → ℝ) (hk : ∀ x x', k x x' = k x' x)
    (hkt : ∀ c x x', k (fun j => x j + c) (fun j => x' j + c) = k x x')
    (hΛ1 : ∑ z, cutLaw μ k z = 1)
    (hΛinv : ∀ (s c : ZMod p) (z : (U → ZMod p) × (U → ZMod p)), s ≠ 0 → IsSquare s →
      cutLaw μ k (affLab s c z.1, affLab s c z.2) = cutLaw μ k z)
    (hΛinj : ∀ (z : (U → ZMod p) × (U → ZMod p)) (a b : U), cutLaw μ k z ≠ 0 → z.1 a ≠ z.2 b)
    (ς : U → U → ZMod p) {ηQ εV : ℝ}
    (hE : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (errQ (cutLaw μ k) ς ξ) ηQ)
    (hN : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (fun k l => degoneN μ ξ k l - if k = l then 1 else 0) εV)
    (qX : ZMod p → (U → ℂ) → ℝ) (hqX0 : ∀ ξ, qX ξ 0 = 0) {ηB : ℝ}
    (hbound : CouplingBoundCx μ k qX ηB) {ερ aperp : ℝ}
    (hρ : ‖kernelOpC μ k (l2MapC μ (fun _ => 1)) - l2MapC μ (fun _ => 1)‖ ≤ ερ)
    (hperp : ∀ h, ⟪l2MapC μ (fun _ => 1), h⟫_ℂ = 0 → (∀ v ∈ degSpace μ, ⟪v, h⟫_ℂ = 0) →
      |RCLike.re ⟪h, kernelOpC μ k h⟫_ℂ| ≤ aperp * ‖h‖ ^ 2)
    {cbar ηQbar ηBbar εVbar sp sm g : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : aperp + ερ ^ 2 ≤ cbar * rp p) (hηQ : ηQ ≤ ηQbar) (hηB : ηB ≤ ηBbar)
    (hεV : εV ≤ εVbar) (hεV0 : 0 ≤ εVbar) (hεV1 : εVbar < 1) (hsp : 0 < sp) (hsm : 0 < sm)
    (htp : ∀ ξ : ZMod p, (IsSquare ξ ∧ ξ ≠ 0) →
      Sarkozy.Spectral.FiniteTest (fun x => (qform (azero ς ξ) x).re) (qX ξ) cbar sp ηQbar ηBbar)
    (htm : ∀ ξ : ZMod p, ¬ (IsSquare ξ ∧ ξ ≠ 0) →
      Sarkozy.Spectral.FiniteTest (fun x => (qform (azero ς ξ) x).re) (qX ξ) cbar sm ηQbar ηBbar)
    (hgp : (cbar + sp) / (1 - εVbar) ≤ g) (hgm : (cbar + sm) / (1 - εVbar) ≤ g)
    (F : EuclideanSpace ℂ (U → ZMod p)) :
    -(g * rp p) * ‖F‖ ^ 2 ≤ RCLike.re ⟪F, kernelOpC μ k F⟫_ℂ := by
  have hr : 0 < rp p := by
    unfold rp
    exact inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos))
  exact Sarkozy.Spectral.routeA_lower
    (routeAInputs_cx hp2 μ hμ0 hμ1 hinv hinj k hk hkt hΛ1 hΛinv hΛinj ς hE hN qX hqX0 hbound
      hρ hperp) hr hcbar0 hcbar hηQ hηB hεV hεV0 hεV1 hsp hsm htp htm hgp hgm F

/-! ## The real statements agree -/

/-- **The real form bound follows from the complex one**: a lower bound
`−c‖F‖² ≤ re⟪F, Op_ℂ F⟫` for all complex `F` gives `−c‖f‖² ≤ ⟪f, Op f⟫` on WP-A's real
realization (`f` real; `embedR` is isometric and carries `kernelOp` to `kernelOpC`). -/
theorem kernelOp_lower_of_complex {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (k : Ω → Ω → ℝ)
    {c : ℝ} (h : ∀ F : EuclideanSpace ℂ Ω, -c * ‖F‖ ^ 2 ≤ RCLike.re ⟪F, kernelOpC μ.weight k F⟫_ℂ)
    (f : EuclideanSpace ℝ Ω) : -c * ‖f‖ ^ 2 ≤ ⟪f, Sarkozy.Spectral.kernelOp μ k f⟫_ℝ := by
  have h1 := h (embedR f)
  rw [re_inner_embedR_kernelOp, norm_embedR, RCLike.re_to_complex, Complex.ofReal_re] at h1
  exact h1

/-- **For the cut operator**: the complex criterion for `cutOpC` gives the real one for WP-A's
`cutOp` (`thm:spectral-criterion` is stated for real `F`). -/
theorem cutOp_lower_of_complex {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hne : (Labellings.injLabellings F D.G).Nonempty) {c : ℝ}
    (h : ∀ v : EuclideanSpace ℂ (D.cut.Half → F), -c * ‖v‖ ^ 2 ≤ RCLike.re ⟪v, cutOpC D hne v⟫_ℂ)
    (f : EuclideanSpace ℝ (D.cut.Half → F)) :
    -c * ‖f‖ ^ 2 ≤ ⟪f, Sarkozy.Spectral.cutOp D hne f⟫_ℝ :=
  kernelOp_lower_of_complex _ _ h f

/-! ## For `p ≡ 3 (mod 4)` the sectors of a real `F_V` are conjugate -/

/-- For `p ≡ 3 (mod 4)` and `ξ ≠ 0`: `−ξ` is a square if and only if `ξ` is not. -/
theorem isSquare_neg_iff (hp3 : p % 4 = 3) {ξ : ZMod p} (hξ : ξ ≠ 0) :
    IsSquare (-ξ) ↔ ¬ IsSquare ξ := by
  have hp2 : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; intro h; rw [h] at hp3; norm_num at hp3
  have hm1 : quadraticChar (ZMod p) (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr
      (fun h => (FiniteField.isSquare_neg_one_iff (F := ZMod p)).mp h (by rw [ZMod.card]; exact hp3))
  have hneg : quadraticChar (ZMod p) (-ξ) = -quadraticChar (ZMod p) ξ := by
    rw [show -ξ = -1 * ξ by ring, map_mul, hm1, neg_one_mul]
  have hnξ : -ξ ≠ 0 := neg_ne_zero.mpr hξ
  rw [← quadraticChar_one_iff_isSquare hnξ, hneg, ← quadraticChar_neg_one_iff_not_isSquare]
  constructor <;> intro h <;> linarith

omit [Fintype U] [DecidableEq U] in
/-- **The sector parts of a real `g` are conjugate** (`p ≡ 3 (mod 4)`): for real-valued mean-zero
`g`, `\overline{gSec_{Q}} = gSec_{non-squares}`, hence (by `gSec_add`) `F_V = v_+ + \bar v_+`. -/
theorem gSec_conj_three (hp3 : p % 4 = 3) {g : U → ZMod p → ℂ}
    (hreal : ∀ l a, conj (g l a) = g l a) (hg : ∀ l, ∑ a, g l a = 0) (l : U) (a : ZMod p) :
    conj (gSec (fun ξ : ZMod p => IsSquare ξ ∧ ξ ≠ 0) g l a) =
      gSec (fun ξ : ZMod p => ¬ (IsSquare ξ ∧ ξ ≠ 0)) g l a := by
  rw [gSec_conj _ hreal]
  have e : ∀ ξ : ZMod p, ξ ≠ 0 →
      ((IsSquare (-ξ) ∧ -ξ ≠ 0) ↔ ¬ (IsSquare ξ ∧ ξ ≠ 0)) := by
    intro ξ hξ
    rw [isSquare_neg_iff hp3 hξ]
    constructor
    · rintro ⟨h1, _⟩ ⟨h2, _⟩; exact h1 h2
    · intro h; exact ⟨fun h2 => h ⟨h2, hξ⟩, neg_ne_zero.mpr hξ⟩
  unfold gSec
  rw [sum_filter, sum_filter]
  refine sum_congr rfl fun ξ _ => ?_
  by_cases hξ : ξ = 0
  · subst hξ
    rw [fcoef_zero, hg l]
    simp
  · by_cases h1 : IsSquare (-ξ) ∧ -ξ ≠ 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true ((e ξ hξ).mp h1))]
    · have h2 : ¬ ¬ (IsSquare ξ ∧ ξ ≠ 0) := fun h => h1 ((e ξ hξ).mpr h)
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]

end Sarkozy.SpectralD.Cx
