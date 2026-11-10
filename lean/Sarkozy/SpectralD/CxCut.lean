module

public import Sarkozy.SpectralD.CxRouteA
public import Sarkozy.SpectralD.GraphLawBridge

@[expose] public section

/-!
# Route A for the cut operator, in the complex realization

`paper/sections/14_spectral.tex`, `thm:spectral-criterion` (Route A) for the cut operator
`Op = T_{K/Z}` of `lem:spec:cutkernel` (WP-P's `Cuts.SpecData`: `cutK`, `cutZ`, `halfLaw`),
over `𝔽_p`. The hypotheses of `routeAInputs_cx` on the half law and the kernel are discharged
for the cut:

* `halfLaw_hyps`: `μ = λ(G⁺)` is a probability, `Aff_p`-invariant and injective on its support
  (`GraphLawBridge.graphWeight_hyps`);
* `cutOK_affLab`, `cutK_affLab`: the cut kernel is invariant under the square-affine maps
  (`lem:spec:cutkernel`(d)); hence `cutK_shift` (translations);
* `cutLaw_total` (`∑ Λ = 1`: `Z = E_{μ⊗μ}K`), `cutLaw_inv`, `cutLaw_inj` (injectivity across the
  cut, from `CutOK`).

`routeAInputs_cut`: `RouteAInputs` for the complex cut operator `cutOpC`, with only the paper's
numerical inputs left (`hE`, `hN`, the coupling bound, `prop:spec2:mucentre`'s `hρ`, `hperp`).
`cut_lower_real`: with WP-A's finite tests, `⟪f, Op f⟫ ≥ −g r ‖f‖²` for **real** `f` in WP-A's
real cut realization (`Spectral.cutOp`), the statement of `thm:spectral-criterion`(a).

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate InnerProductSpace

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- The half law `μ = λ(G⁺)` satisfies the standing hypotheses. -/
theorem halfLaw_hyps (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) :
    (∀ x, 0 ≤ (D.halfLaw hne).weight x) ∧ (∑ x, (D.halfLaw hne).weight x = 1) ∧
      (∀ (s c : ZMod p) (x : D.cut.Half → ZMod p), s ≠ 0 → IsSquare s →
        (D.halfLaw hne).weight (affLab s c x) = (D.halfLaw hne).weight x) ∧
      (∀ (x : D.cut.Half → ZMod p) (k l : D.cut.Half), (D.halfLaw hne).weight x ≠ 0 → k ≠ l →
        x k ≠ x l) :=
  graphWeight_hyps D.halfGraph (D.half_nonempty hne)

/-- **The cut constraints are square-affine invariant.** -/
theorem cutOK_affLab {s c : ZMod p} (hs : s ≠ 0) (hsq : IsSquare s)
    (x x' : D.cut.Half → ZMod p) :
    D.CutOK (affLab s c x) (affLab s c x') ↔ D.CutOK x x' := by
  have hq : quadraticChar (ZMod p) s = 1 := (quadraticChar_one_iff_isSquare hs).mpr hsq
  have hcross : ∀ (σ : ZMod p) (a b : D.cut.Half),
      quadraticChar (ZMod p) (σ * (affLab s c x' b - affLab s c x a)) =
        quadraticChar (ZMod p) (σ * (x' b - x a)) := by
    intro σ a b
    rw [show σ * (affLab s c x' b - affLab s c x a) = s * (σ * (x' b - x a)) by
      unfold affLab; ring, map_mul, hq, one_mul]
  have hinj : ∀ a b : ZMod p, s * a + c = s * b + c ↔ a = b := by
    intro a b
    constructor
    · intro h; exact mul_left_cancel₀ hs (add_right_cancel h)
    · intro h; rw [h]
  unfold Cuts.SpecData.CutOK
  simp only [hcross]
  constructor
  · rintro ⟨hd, hc⟩
    refine ⟨?_, hc⟩
    rw [disjoint_left] at hd ⊢
    intro a ha ha'
    obtain ⟨i, -, rfl⟩ := mem_image.mp ha
    obtain ⟨j, -, hj⟩ := mem_image.mp ha'
    apply hd (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
    exact mem_image.mpr ⟨j, mem_univ _, by unfold affLab; rw [hj]⟩
  · rintro ⟨hd, hc⟩
    refine ⟨?_, hc⟩
    rw [disjoint_left] at hd ⊢
    intro a ha ha'
    obtain ⟨i, -, rfl⟩ := mem_image.mp ha
    obtain ⟨j, -, hj⟩ := mem_image.mp ha'
    apply hd (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
    exact mem_image.mpr ⟨j, mem_univ _, (hinj _ _).mp hj⟩

/-- **The cut kernel is square-affine invariant** (`lem:spec:cutkernel`(d)). -/
theorem cutK_affLab {s c : ZMod p} (hs : s ≠ 0) (hsq : IsSquare s)
    (x x' : D.cut.Half → ZMod p) :
    D.cutK (affLab s c x) (affLab s c x') = D.cutK x x' := by
  classical
  unfold Cuts.SpecData.cutK
  by_cases h : D.CutOK x x'
  · simp only [h, (cutOK_affLab D hs hsq x x').mpr h, ↓reduceIte]
  · have h' : ¬ D.CutOK (affLab s c x) (affLab s c x') := fun h' =>
      h ((cutOK_affLab D hs hsq x x').mp h')
    simp only [h, h', ↓reduceIte]

/-- The cut kernel is translation invariant. -/
theorem cutK_shift (c : ZMod p) (x x' : D.cut.Half → ZMod p) :
    D.cutK (fun j => x j + c) (fun j => x' j + c) = D.cutK x x' := by
  have e : ∀ y : D.cut.Half → ZMod p, (fun j => y j + c) = affLab 1 c y := by
    intro y; funext j; unfold affLab; ring
  rw [e, e]
  exact cutK_affLab D one_ne_zero ⟨1, by ring⟩ x x'

/-- The normalized kernel `K/Z`. -/
noncomputable def cutKn (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (x x' : D.cut.Half → ZMod p) : ℝ :=
  D.cutK x x' / D.cutZ hne

/-- **`∑ Λ = 1`**: the cut law `μ ⊗ μ · K/Z` is a probability (`Z = E_{μ⊗μ}K`). -/
theorem cutLaw_total (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) :
    ∑ z, cutLaw (D.halfLaw hne).weight (cutKn D hne) z = 1 := by
  have hZ := D.cutZ_pos hne
  have e : D.cutZ hne = ∑ z : (D.cut.Half → ZMod p) × (D.cut.Half → ZMod p),
      (D.halfLaw hne).weight z.1 * (D.halfLaw hne).weight z.2 * D.cutK z.1 z.2 := by
    unfold Cuts.SpecData.cutZ
    rfl
  unfold cutLaw cutKn
  have e2 : ∀ z : (D.cut.Half → ZMod p) × (D.cut.Half → ZMod p),
      (D.halfLaw hne).weight z.1 * (D.halfLaw hne).weight z.2 * (D.cutK z.1 z.2 / D.cutZ hne) =
        (D.halfLaw hne).weight z.1 * (D.halfLaw hne).weight z.2 * D.cutK z.1 z.2 /
          D.cutZ hne := fun z => by ring
  rw [sum_congr rfl fun z _ => e2 z, ← sum_div, ← e, div_self hZ.ne']

/-- **`Λ` is square-affine invariant.** -/
theorem cutLaw_inv (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) (s c : ZMod p)
    (z : (D.cut.Half → ZMod p) × (D.cut.Half → ZMod p)) (hs : s ≠ 0) (hsq : IsSquare s) :
    cutLaw (D.halfLaw hne).weight (cutKn D hne) (affLab s c z.1, affLab s c z.2) =
      cutLaw (D.halfLaw hne).weight (cutKn D hne) z := by
  obtain ⟨-, -, hinv, -⟩ := halfLaw_hyps D hne
  unfold cutLaw cutKn
  dsimp only
  rw [hinv s c z.1 hs hsq, hinv s c z.2 hs hsq, cutK_affLab D hs hsq]

/-- **Injectivity across the cut**: on the support of `Λ`, `x_a ≠ x'_b`. -/
theorem cutLaw_inj (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (z : (D.cut.Half → ZMod p) × (D.cut.Half → ZMod p)) (a b : D.cut.Half)
    (hz : cutLaw (D.halfLaw hne).weight (cutKn D hne) z ≠ 0) : z.1 a ≠ z.2 b := by
  classical
  have hK : D.cutK z.1 z.2 ≠ 0 := by
    intro h0
    apply hz
    unfold cutLaw cutKn
    rw [h0, zero_div, mul_zero]
  have hok : D.CutOK z.1 z.2 := by
    by_contra h
    apply hK
    unfold Cuts.SpecData.cutK
    simp only [h, ↓reduceIte]
  intro hab
  have hd := hok.1
  rw [disjoint_left] at hd
  exact hd (mem_image.mpr ⟨a, mem_univ _, rfl⟩) (mem_image.mpr ⟨b, mem_univ _, hab.symm⟩)

/-- **`RouteAInputs` for the cut operator** (complex realization, `thm:spectral-criterion`,
Route A). The half law, the kernel and the cut law are discharged from WP-P's cut data; the
remaining hypotheses are the paper's numerical inputs: `hE` (`‖E_Q(ξ)‖ ≤ η_Q`,
`lem:spec:degone`(b)), `hN` (`‖𝐍(ξ) − I‖ ≤ ε_V`, (c)), the coupling bound `hbound`
(`cor:spec2:coupling`, from `couplingBound_cx`), and `hρ`, `hperp` (`prop:spec2:mucentre`). -/
theorem routeAInputs_cut (hp2 : p ≠ 2) (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (ς : D.cut.Half → D.cut.Half → ZMod p) {ηQ εV : ℝ}
    (hE : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (errQ (cutLaw (D.halfLaw hne).weight (cutKn D hne)) ς ξ) ηQ)
    (hN : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (fun k l => degoneN (D.halfLaw hne).weight ξ k l -
      if k = l then 1 else 0) εV)
    (qX : ZMod p → (D.cut.Half → ℂ) → ℝ) (hqX0 : ∀ ξ, qX ξ 0 = 0) {ηB : ℝ}
    (hbound : CouplingBoundCx (D.halfLaw hne).weight (cutKn D hne) qX ηB) {ερ aperp : ℝ}
    (hρ : ‖cutOpC D hne (cutOneC D hne) - cutOneC D hne‖ ≤ ερ)
    (hperp : ∀ h, ⟪cutOneC D hne, h⟫_ℂ = 0 → (∀ v ∈ degSpace (D.halfLaw hne).weight,
      ⟪v, h⟫_ℂ = 0) → |RCLike.re ⟪h, cutOpC D hne h⟫_ℂ| ≤ aperp * ‖h‖ ^ 2) :
    Sarkozy.Spectral.RouteAInputs (cutOpC D hne) (cutOneC D hne)
      (degSpace (D.halfLaw hne).weight) (secP p D.cut.Half) (secM p D.cut.Half)
      (fun ξ : ZMod p => IsSquare ξ ∧ ξ ≠ 0) (degCoef (D.halfLaw hne).weight)
      (fun ξ x => (qform (azero ς ξ) x).re) qX (rp p) ηQ ηB εV ερ aperp := by
  obtain ⟨h0, h1, hinv, hinj⟩ := halfLaw_hyps D hne
  exact routeAInputs_cx hp2 (D.halfLaw hne).weight h0 h1 hinv hinj (cutKn D hne)
    (fun x x' => by unfold cutKn; rw [D.cutK_symm])
    (fun c x x' => by unfold cutKn; rw [cutK_shift D c x x'])
    (cutLaw_total D hne) (fun s c z hs hsq => cutLaw_inv D hne s c z hs hsq)
    (fun z a b hz => cutLaw_inj D hne z a b hz) ς hE hN qX hqX0 hbound hρ hperp

/-- **`thm:spectral-criterion`(a) for the cut, real form**: under the hypotheses of
`routeAInputs_cut` and WP-A's finite tests, `⟪f, Op f⟫ ≥ −g r ‖f‖²` for every real `f` of WP-A's
real cut realization (`Spectral.cutOp`). The complex realization is used only inside the proof
(the two translation sectors of a real `F_V` are complex conjugates, `gSec_conj_three`). -/
theorem cut_lower_real (hp2 : p ≠ 2) (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (ς : D.cut.Half → D.cut.Half → ZMod p) {ηQ εV : ℝ}
    (hE : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (errQ (cutLaw (D.halfLaw hne).weight (cutKn D hne)) ς ξ) ηQ)
    (hN : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (fun k l => degoneN (D.halfLaw hne).weight ξ k l -
      if k = l then 1 else 0) εV)
    (qX : ZMod p → (D.cut.Half → ℂ) → ℝ) (hqX0 : ∀ ξ, qX ξ 0 = 0) {ηB : ℝ}
    (hbound : CouplingBoundCx (D.halfLaw hne).weight (cutKn D hne) qX ηB) {ερ aperp : ℝ}
    (hρ : ‖cutOpC D hne (cutOneC D hne) - cutOneC D hne‖ ≤ ερ)
    (hperp : ∀ h, ⟪cutOneC D hne, h⟫_ℂ = 0 → (∀ v ∈ degSpace (D.halfLaw hne).weight,
      ⟪v, h⟫_ℂ = 0) → |RCLike.re ⟪h, cutOpC D hne h⟫_ℂ| ≤ aperp * ‖h‖ ^ 2)
    {cbar ηQbar ηBbar εVbar sp sm g : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : aperp + ερ ^ 2 ≤ cbar * rp p) (hηQ : ηQ ≤ ηQbar) (hηB : ηB ≤ ηBbar)
    (hεV : εV ≤ εVbar) (hεV0 : 0 ≤ εVbar) (hεV1 : εVbar < 1) (hsp : 0 < sp) (hsm : 0 < sm)
    (htp : ∀ ξ : ZMod p, (IsSquare ξ ∧ ξ ≠ 0) →
      Sarkozy.Spectral.FiniteTest (fun x => (qform (azero ς ξ) x).re) (qX ξ) cbar sp ηQbar ηBbar)
    (htm : ∀ ξ : ZMod p, ¬ (IsSquare ξ ∧ ξ ≠ 0) →
      Sarkozy.Spectral.FiniteTest (fun x => (qform (azero ς ξ) x).re) (qX ξ) cbar sm ηQbar ηBbar)
    (hgp : (cbar + sp) / (1 - εVbar) ≤ g) (hgm : (cbar + sm) / (1 - εVbar) ≤ g)
    (f : EuclideanSpace ℝ (D.cut.Half → ZMod p)) :
    -(g * rp p) * ‖f‖ ^ 2 ≤ ⟪f, Sarkozy.Spectral.cutOp D hne f⟫_ℝ := by
  have hr : 0 < rp p := by
    unfold rp
    exact inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos))
  have hin := routeAInputs_cut D hp2 hne ς hE hN qX hqX0 hbound hρ hperp
  exact cutOp_lower_of_complex D hne
    (fun v => Sarkozy.Spectral.routeA_lower hin hr hcbar0 hcbar hηQ hηB hεV hεV0 hεV1 hsp hsm
      htp htm hgp hgm v) f

end Sarkozy.SpectralD.Cx
