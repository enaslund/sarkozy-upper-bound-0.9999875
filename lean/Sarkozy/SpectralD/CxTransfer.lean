module

public import Sarkozy.SpectralD.CxCut

@[expose] public section

/-!
# From the real realization to the complex one: `rho_bound` and `perp_bound`

`paper/sections/14_spectral.tex`, Conventions: "`Op` has a real symmetric kernel, so its
quadratic form is determined by real functions". The two fields of `RouteAInputs` that come from
`prop:spec2:mucentre` (`rho_bound`, (c3), and `perp_bound`, (c4)) are proved elsewhere in WP-A's
**real** realization. This file transfers them to the complex realization of `CxRealization`:

* `rePart`, `imPart`, `eq_re_add_im` (`h = embedR(Re h) + i·embedR(Im h)`), `norm_sq_re_im`
  (`‖h‖² = ‖Re h‖² + ‖Im h‖²`), `inner_embedR_left`;
* `re_inner_kernelOpC` (`re⟪h, Op h⟫ = ⟪Re h, Op Re h⟫ + ⟪Im h, Op Im h⟫`);
* `rho_bound_of_real` (`‖Op 1 − 1‖` is the same in both realizations) and
  `perp_bound_of_real`: a real bound `|⟪h, Op h⟫| ≤ a_⊥‖h‖²` on the real `H_⊥` (orthogonal to
  `1` and to a real degree-one space `V_ℝ`) gives the complex bound on the complex `H_⊥`
  whenever `embedR V_ℝ ⊆ V_ℂ`;
* `realDegSpace` (the real degree-one space) with `embedR_realDegSpace` (`embedR V_ℝ ⊆ 𝒱`).

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate InnerProductSpace

section Transfer

variable {Ω : Type*} [Fintype Ω]

/-- The real part of a vector of the complex realization. -/
noncomputable def rePart (h : EuclideanSpace ℂ Ω) : EuclideanSpace ℝ Ω :=
  WithLp.toLp 2 (fun x => (h.ofLp x).re)

/-- The imaginary part. -/
noncomputable def imPart (h : EuclideanSpace ℂ Ω) : EuclideanSpace ℝ Ω :=
  WithLp.toLp 2 (fun x => (h.ofLp x).im)

omit [Fintype Ω] in
theorem eq_re_add_im (h : EuclideanSpace ℂ Ω) :
    h = embedR (rePart h) + Complex.I • embedR (imPart h) := by
  ext x
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, embedR_ofLp, rePart, imPart]
  rw [mul_comm]
  exact (Complex.re_add_im (h.ofLp x)).symm

theorem norm_sq_re_im (h : EuclideanSpace ℂ Ω) :
    ‖h‖ ^ 2 = ‖rePart h‖ ^ 2 + ‖imPart h‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _), Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _), ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  simp only [rePart, imPart, Real.norm_eq_abs, sq_abs]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- `⟪embedR u, h⟫ = ⟪u, Re h⟫ + i⟪u, Im h⟫`. -/
theorem inner_embedR_left (u : EuclideanSpace ℝ Ω) (h : EuclideanSpace ℂ Ω) :
    ⟪embedR u, h⟫_ℂ = ((⟪u, rePart h⟫_ℝ : ℝ) : ℂ) + Complex.I * ((⟪u, imPart h⟫_ℝ : ℝ) : ℂ) := by
  conv_lhs => rw [eq_re_add_im h]
  rw [inner_add_right, inner_smul_right, inner_embedR, inner_embedR]

/-- **The real part of the complex form** of a real kernel is the sum of the real forms of the
real and imaginary parts. -/
theorem re_inner_kernelOpC (μ : FiniteLaw Ω) (k : Ω → Ω → ℝ) (h : EuclideanSpace ℂ Ω) :
    RCLike.re ⟪h, kernelOpC μ.weight k h⟫_ℂ =
      ⟪rePart h, Spectral.kernelOp μ k (rePart h)⟫_ℝ +
        ⟪imPart h, Spectral.kernelOp μ k (imPart h)⟫_ℝ := by
  set a := rePart h
  set b := imPart h
  have e := eq_re_add_im h
  rw [e, map_add, map_smul, inner_add_left, inner_add_right, inner_add_right, inner_smul_left,
    inner_smul_left, inner_smul_right, inner_smul_right, re_inner_embedR_kernelOp,
    re_inner_embedR_kernelOp, re_inner_embedR_kernelOp, re_inner_embedR_kernelOp,
    RCLike.re_to_complex]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.mul_im]
  ring

/-- **`rho_bound` transfers**: `‖Op 1 − 1‖` is the same in both realizations. -/
theorem rho_bound_of_real (μ : FiniteLaw Ω) (k : Ω → Ω → ℝ) (v : EuclideanSpace ℝ Ω) {ερ : ℝ}
    (h : ‖Spectral.kernelOp μ k v - v‖ ≤ ερ) :
    ‖kernelOpC μ.weight k (embedR v) - embedR v‖ ≤ ερ := by
  rw [← embedR_kernelOp, ← map_sub, norm_embedR]
  exact h

/-- **`perp_bound` transfers**: if `|⟪f, Op f⟫| ≤ a_⊥‖f‖²` for real `f ⊥ 1, V_ℝ`, then
`|re⟪h, Op h⟫| ≤ a_⊥‖h‖²` for complex `h ⊥ 1, V_ℂ`, whenever `embedR V_ℝ ⊆ V_ℂ`. -/
theorem perp_bound_of_real (μ : FiniteLaw Ω) (k : Ω → Ω → ℝ) (one : EuclideanSpace ℝ Ω)
    (Vr : Submodule ℝ (EuclideanSpace ℝ Ω)) (Vc : Submodule ℂ (EuclideanSpace ℂ Ω))
    (hV : ∀ v ∈ Vr, embedR v ∈ Vc) {aperp : ℝ}
    (hreal : ∀ f, ⟪one, f⟫_ℝ = 0 → (∀ v ∈ Vr, ⟪v, f⟫_ℝ = 0) →
      |⟪f, Spectral.kernelOp μ k f⟫_ℝ| ≤ aperp * ‖f‖ ^ 2)
    (h : EuclideanSpace ℂ Ω) (h1 : ⟪embedR one, h⟫_ℂ = 0) (hVh : ∀ v ∈ Vc, ⟪v, h⟫_ℂ = 0) :
    |RCLike.re ⟪h, kernelOpC μ.weight k h⟫_ℂ| ≤ aperp * ‖h‖ ^ 2 := by
  have hsplit : ∀ u : EuclideanSpace ℝ Ω, ⟪embedR u, h⟫_ℂ = 0 →
      ⟪u, rePart h⟫_ℝ = 0 ∧ ⟪u, imPart h⟫_ℝ = 0 := by
    intro u hu
    rw [inner_embedR_left] at hu
    have hre := congrArg Complex.re hu
    have him := congrArg Complex.im hu
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re, Complex.add_im, Complex.mul_im, Complex.zero_im]
      at hre him
    constructor <;> linarith
  obtain ⟨ha1, hb1⟩ := hsplit one h1
  have haV : ∀ v ∈ Vr, ⟪v, rePart h⟫_ℝ = 0 := fun v hv => (hsplit v (hVh _ (hV v hv))).1
  have hbV : ∀ v ∈ Vr, ⟪v, imPart h⟫_ℝ = 0 := fun v hv => (hsplit v (hVh _ (hV v hv))).2
  rw [re_inner_kernelOpC, norm_sq_re_im, mul_add]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact hreal _ ha1 haV
  · exact hreal _ hb1 hbV

end Transfer

/-! ## The real degree-one space -/

section RealDegree

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- **The real degree-one space** `V_ℝ = {l2Map(∑_k g_k(x_k)) : g_k real, mean zero}` of WP-A's
real realization. -/
noncomputable def realDegSpace (μ : FiniteLaw (U → ZMod p)) :
    Submodule ℝ (EuclideanSpace ℝ (U → ZMod p)) where
  carrier := {v | ∃ g : U → ZMod p → ℝ, (∀ l, ∑ a, g l a = 0) ∧
    v = InfluenceGlue.l2Map μ (fun x => ∑ l, g l (x l))}
  add_mem' {u v} hu hv := by
    obtain ⟨g, hg, rfl⟩ := hu
    obtain ⟨h, hh, rfl⟩ := hv
    refine ⟨g + h, fun l => ?_, ?_⟩
    · simp only [Pi.add_apply, sum_add_distrib, hg l, hh l, add_zero]
    · rw [← map_add]
      congr 1
      funext x
      simp only [Pi.add_apply, sum_add_distrib]
  zero_mem' := ⟨0, fun l => by simp, by rw [show (fun x : U → ZMod p => ∑ l, (0 : U → ZMod p → ℝ) l (x l)) = 0 from by funext x; simp, map_zero]⟩
  smul_mem' c v hv := by
    obtain ⟨g, hg, rfl⟩ := hv
    refine ⟨c • g, fun l => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum, hg l, mul_zero]
    · rw [← map_smul]
      congr 1
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, mul_sum]

/-- **`embedR V_ℝ ⊆ 𝒱`**: the real degree-one space embeds into the complex one. -/
theorem embedR_realDegSpace (μ : FiniteLaw (U → ZMod p)) {v : EuclideanSpace ℝ (U → ZMod p)}
    (hv : v ∈ realDegSpace μ) : embedR v ∈ degSpace μ.weight := by
  obtain ⟨g, hg, rfl⟩ := hv
  have e : embedR (InfluenceGlue.l2Map μ (fun x => ∑ l, g l (x l))) =
      degMap μ.weight (fun l a => ((g l a : ℝ) : ℂ)) := by
    rw [embedR_l2Map, degMap_apply]
    congr 1
    funext x
    unfold degFun
    push_cast
    rfl
  rw [e]
  refine degMap_mem μ.weight fun l => ?_
  have := congrArg (fun t : ℝ => (t : ℂ)) (hg l)
  simpa using this

end RealDegree

/-! ## Route A for the cut with the real inputs of `prop:spec2:mucentre` -/

section CutReal

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- **`thm:spectral-criterion`(a) for the cut, from real inputs**: WP-A's real realization
supplies `‖ϱ − 1‖ ≤ ε_ϱ` (`hρ`) and the bound on `H_⊥` relative to the real degree-one space
(`hperp`, `prop:spec2:mucentre`(c3), (c4)); with `hE`, `hN` (`lem:spec:degone`(b), (c)), the
coupling bound (`cor:spec2:coupling`) and WP-A's finite tests,
`⟪f, Op f⟫ ≥ −g r ‖f‖²` for every real `f`. -/
theorem cut_lower_real_of_real (hp2 : p ≠ 2)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (ς : D.cut.Half → D.cut.Half → ZMod p) {ηQ εV : ℝ}
    (hE : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (errQ (cutLaw (D.halfLaw hne).weight (cutKn D hne)) ς ξ) ηQ)
    (hN : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (fun k l => degoneN (D.halfLaw hne).weight ξ k l -
      if k = l then 1 else 0) εV)
    (qX : ZMod p → (D.cut.Half → ℂ) → ℝ) (hqX0 : ∀ ξ, qX ξ 0 = 0) {ηB : ℝ}
    (hbound : CouplingBoundCx (D.halfLaw hne).weight (cutKn D hne) qX ηB) {ερ aperp : ℝ}
    (hρ : ‖Spectral.cutOp D hne (Spectral.cutOne D hne) - Spectral.cutOne D hne‖ ≤ ερ)
    (hperp : ∀ f, ⟪Spectral.cutOne D hne, f⟫_ℝ = 0 →
      (∀ v ∈ realDegSpace (D.halfLaw hne), ⟪v, f⟫_ℝ = 0) →
      |⟪f, Spectral.cutOp D hne f⟫_ℝ| ≤ aperp * ‖f‖ ^ 2)
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
  have hρC : ‖cutOpC D hne (cutOneC D hne) - cutOneC D hne‖ ≤ ερ := by
    rw [← embedR_cutOne, ← embedR_cutOp, ← map_sub, norm_embedR]
    exact hρ
  have hperpC : ∀ h, ⟪cutOneC D hne, h⟫_ℂ = 0 → (∀ v ∈ degSpace (D.halfLaw hne).weight,
      ⟪v, h⟫_ℂ = 0) → |RCLike.re ⟪h, cutOpC D hne h⟫_ℂ| ≤ aperp * ‖h‖ ^ 2 := by
    intro h h1 hV
    rw [← embedR_cutOne] at h1
    exact perp_bound_of_real (D.halfLaw hne) (cutKn D hne) (Spectral.cutOne D hne)
      (realDegSpace (D.halfLaw hne)) (degSpace (D.halfLaw hne).weight)
      (fun v hv => embedR_realDegSpace (D.halfLaw hne) hv) hperp h h1 hV
  exact cut_lower_real D hp2 hne ς hE hN qX hqX0 hbound hρC hperpC hcbar0 hcbar hηQ hηB hεV
    hεV0 hεV1 hsp hsm htp htm hgp hgm f

end CutReal

end Sarkozy.SpectralD.Cx
