module

public import Sarkozy.SpectralD.CxSmallCut

@[expose] public section

/-!
# The character expansion of the cut operator (`lem:spec:expansion`)

`paper/sections/14_spectral.tex`, `lem:spec:expansion` and `eq:record:root-kernel`:
`2^{m_×} K = ∏_{e ∈ E_×}(1 + χ_e) − K_coll`, where `K_coll = 1[x(U⁺) ∩ x'(U⁺) ≠ ∅] ∏_e (1 + χ_e)`
(`cutK_expansion`, from WP-A's `prod_one_add_char_eq`), and
`∏_e (1 + χ_e) = 1 + K_star + K_ns` with `K_ns = ∏_e(1 + χ_e) − 1 − K_star` (the nonstar part,
by WP-A's `prod_one_add_char` the sum of `χ_S` over the nonempty non-star `S ⊆ E_×`). Hence, in
WP-A's real realization (`Spectral.kernelOp`):
* `cutOp_eq_K0`: `Op = K₀/Z₀`, `K₀ = T_{2^{m_×} K}`, `Z₀ = 2^{m_×} Z`;
* `K0_expansion`: `K₀ = 1 ⊗ 1 + T_star + T_ns − T_coll` with `T_ns = T_{K_ns}`,
  `T_coll = T_{K_coll}`;
* `Z0_lower`: `Z₀ ≥ 1 − (2Z_⋆ + N_ns + D_col)` (`prop:spec2:mucentre`(c1), WP-A's `mucentre_Z`
  and `glue_mucentre_star_closed`);
* `spectral_criterion_cut_exp`: `spectral_criterion_cut_small` with these, so that of the
  expansion inputs only the operator bounds `‖T_ns‖ ≤ N_ns`, `‖T_coll‖ ≤ D_col` for these explicit
  kernels remain (with `ε_Z ≥ 2Z_⋆ + N_ns + D_col`).

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC Sarkozy.Characters
open scoped BigOperators InnerProductSpace

section KernelOp

variable {Ω : Type*} [Fintype Ω]

lemma kernelOp_add_ker (μ : FiniteLaw Ω) (k₁ k₂ : Ω → Ω → ℝ) (v : EuclideanSpace ℝ Ω) :
    Spectral.kernelOp μ (fun x x' => k₁ x x' + k₂ x x') v =
      Spectral.kernelOp μ k₁ v + Spectral.kernelOp μ k₂ v := by
  ext x
  simp only [Spectral.kernelOp_ofLp, PiLp.add_apply, ← sum_add_distrib]
  exact sum_congr rfl fun x' _ => by ring

lemma kernelOp_sub_ker (μ : FiniteLaw Ω) (k₁ k₂ : Ω → Ω → ℝ) (v : EuclideanSpace ℝ Ω) :
    Spectral.kernelOp μ (fun x x' => k₁ x x' - k₂ x x') v =
      Spectral.kernelOp μ k₁ v - Spectral.kernelOp μ k₂ v := by
  ext x
  simp only [Spectral.kernelOp_ofLp, PiLp.sub_apply, ← sum_sub_distrib]
  exact sum_congr rfl fun x' _ => by ring

lemma kernelOp_smul_ker (μ : FiniteLaw Ω) (c : ℝ) (k : Ω → Ω → ℝ) (v : EuclideanSpace ℝ Ω) :
    Spectral.kernelOp μ (fun x x' => c * k x x') v = c • Spectral.kernelOp μ k v := by
  ext x
  simp only [Spectral.kernelOp_ofLp, PiLp.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun x' _ => by ring

lemma kernelOp_one (μ : FiniteLaw Ω) (v : EuclideanSpace ℝ Ω) :
    Spectral.kernelOp μ (fun _ _ => 1) v =
      ⟪InfluenceGlue.l2Map μ (fun _ => 1), v⟫_ℝ • InfluenceGlue.l2Map μ (fun _ => 1) := by
  ext x
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Spectral.kernelOp_ofLp, PiLp.smul_apply, smul_eq_mul, InfluenceGlue.l2Map_ofLp,
    dotProduct, star_trivial, sum_mul]
  exact sum_congr rfl fun x' _ => by ring

end KernelOp

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- `∏_{e ∈ E_×} (1 + χ_e(x, x'))`, `χ_{(j,k)} = χ(ς_jk(x'_k − x_j))`. -/
noncomputable def prodKer (x x' : D.cut.Half → ZMod p) : ℝ :=
  ∏ q ∈ D.crossPairs, (1 + (quadraticChar (ZMod p) (Spectral.sgnF D q.1 q.2 * (x' q.2 - x q.1)) : ℝ))

/-- The collision kernel `K_coll = 1[x(U⁺) ∩ x'(U⁺) ≠ ∅] ∏_e (1 + χ_e)`. -/
noncomputable def collKer (x x' : D.cut.Half → ZMod p) : ℝ := by
  classical
  exact if Disjoint (univ.image x) (univ.image x') then 0 else prodKer D x x'

/-- The nonstar kernel `K_ns = ∏_e(1 + χ_e) − 1 − K_star`. -/
noncomputable def nsKer (x x' : D.cut.Half → ZMod p) : ℝ :=
  prodKer D x x' - 1 - Spectral.starKer D x x'

/-- **`lem:spec:expansion`**: `2^{m_×} K = ∏_e (1 + χ_e) − K_coll`. -/
theorem cutK_expansion (hp2 : p ≠ 2) (x x' : D.cut.Half → ZMod p) :
    (2 : ℝ) ^ D.crossPairs.card * D.cutK x x' = prodKer D x x' - collKer D x x' := by
  classical
  unfold collKer
  by_cases hd : Disjoint (univ.image x) (univ.image x')
  · simp only [hd, ↓reduceIte, sub_zero]
    have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
    have hy : ∀ q ∈ D.crossPairs, Spectral.sgnF D q.1 q.2 * (x' q.2 - x q.1) ≠ 0 := by
      intro q hq
      have hs : D.sgn q.1 q.2 ≠ 0 := by
        simp only [Cuts.SpecData.crossPairs, mem_filter, mem_univ, true_and] at hq; exact hq
      have hs' : Spectral.sgnF (p := p) D q.1 q.2 ≠ 0 := by
        have h1 : D.sgn q.1 q.2 = 1 ∨ D.sgn q.1 q.2 = -1 := by
          unfold Cuts.SpecData.sgn at hs ⊢
          split_ifs at hs ⊢ <;> simp_all
        unfold Spectral.sgnF
        rcases h1 with h | h <;> rw [h] <;> simp
      have hne : x' q.2 - x q.1 ≠ 0 := by
        intro h0
        have h1 : x q.1 ∈ univ.image x := mem_image_of_mem x (mem_univ _)
        have h2 : x q.1 ∈ univ.image x' := by
          rw [← sub_eq_zero.mp h0]; exact mem_image_of_mem x' (mem_univ _)
        exact (Finset.disjoint_left.mp hd) h1 h2
      exact mul_ne_zero hs' hne
    unfold prodKer
    rw [Spectral.prod_one_add_char_eq hF D.crossPairs _ hy]
    congr 1
    unfold Cuts.SpecData.cutK Cuts.SpecData.CutOK
    by_cases hall : ∀ q ∈ D.crossPairs,
        quadraticChar (ZMod p) ((D.sgn q.1 q.2 : ZMod p) * (x' q.2 - x q.1)) = 1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hd, hall⟩)]
      symm
      refine prod_eq_one fun q hq => ?_
      have hsq : IsSquare (Spectral.sgnF D q.1 q.2 * (x' q.2 - x q.1)) :=
        (quadraticChar_one_iff_isSquare (hy q hq)).mp (hall q hq)
      simp only [hsq, ↓reduceIte]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hall h.2))]
      simp only [not_forall] at hall
      obtain ⟨q, hq, hq1⟩ := hall
      symm
      refine prod_eq_zero hq ?_
      have hns : ¬ IsSquare (Spectral.sgnF D q.1 q.2 * (x' q.2 - x q.1)) := fun hsq =>
        hq1 ((quadraticChar_one_iff_isSquare (hy q hq)).mpr hsq)
      simp only [hns, ↓reduceIte]
  · simp only [hd, ↓reduceIte, sub_self]
    have hK : D.cutK x x' = 0 := by
      unfold Cuts.SpecData.cutK
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hd h.1))]
    rw [hK, mul_zero]

variable (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)

/-- `K₀ = T_{2^{m_×} K}`. -/
noncomputable def K0op : EuclideanSpace ℝ (D.cut.Half → ZMod p) →ₗ[ℝ]
    EuclideanSpace ℝ (D.cut.Half → ZMod p) :=
  Spectral.kernelOp (D.halfLaw hne) (fun x x' => (2 : ℝ) ^ D.crossPairs.card * D.cutK x x')

/-- `T_ns = T_{K_ns}`. -/
noncomputable def nsOp : EuclideanSpace ℝ (D.cut.Half → ZMod p) →ₗ[ℝ]
    EuclideanSpace ℝ (D.cut.Half → ZMod p) :=
  Spectral.kernelOp (D.halfLaw hne) (nsKer D)

/-- `T_coll = T_{K_coll}`. -/
noncomputable def collOp : EuclideanSpace ℝ (D.cut.Half → ZMod p) →ₗ[ℝ]
    EuclideanSpace ℝ (D.cut.Half → ZMod p) :=
  Spectral.kernelOp (D.halfLaw hne) (collKer D)

/-- `Z₀ = 2^{m_×} Z`. -/
noncomputable def Z0 : ℝ := (2 : ℝ) ^ D.crossPairs.card * D.cutZ hne

/-- **`Op = K₀/Z₀`**. -/
theorem cutOp_eq_K0 (x : EuclideanSpace ℝ (D.cut.Half → ZMod p)) :
    Spectral.cutOp D hne x = ((Z0 D hne)⁻¹ : ℝ) • K0op D hne x := by
  have hZ := D.cutZ_pos hne
  have h2 : (0 : ℝ) < 2 ^ D.crossPairs.card := by positivity
  have hk : (fun y y' : D.cut.Half → ZMod p => D.cutK y y' / D.cutZ hne) =
      fun y y' => (Z0 D hne)⁻¹ * ((2 : ℝ) ^ D.crossPairs.card * D.cutK y y') := by
    funext y y'
    unfold Z0
    field_simp
  unfold Spectral.cutOp K0op
  rw [hk, kernelOp_smul_ker]

/-- **`K₀ = 1 ⊗ 1 + T_star + T_ns − T_coll`** (`eq:record:root-kernel`). -/
theorem K0_expansion (hp2 : p ≠ 2) (x : EuclideanSpace ℝ (D.cut.Half → ZMod p)) :
    K0op D hne x = ⟪Spectral.cutOne D hne, x⟫_ℝ • Spectral.cutOne D hne +
      Spectral.starOp D hne x + nsOp D hne x - collOp D hne x := by
  have hk : (fun y y' : D.cut.Half → ZMod p => (2 : ℝ) ^ D.crossPairs.card * D.cutK y y') =
      fun y y' => ((fun _ _ => (1 : ℝ)) y y' + Spectral.starKer D y y' + nsKer D y y') -
        collKer D y y' := by
    funext y y'
    rw [cutK_expansion D hp2 y y']
    unfold nsKer
    ring
  unfold K0op nsOp collOp Spectral.starOp
  rw [hk, kernelOp_sub_ker, kernelOp_add_ker, kernelOp_add_ker, kernelOp_one]
  rfl

/-- `⟪1, K₀ 1⟫ = Z₀` (from `⟪1, Op 1⟫ = 1`). -/
theorem inner_K0_one :
    ⟪Spectral.cutOne D hne, K0op D hne (Spectral.cutOne D hne)⟫_ℝ = Z0 D hne := by
  have hZ := D.cutZ_pos hne
  have hZ0 : Z0 D hne ≠ 0 := by unfold Z0; positivity
  have h := Spectral.cutOp_mean D hne
  rw [cutOp_eq_K0 D hne, inner_smul_right] at h
  field_simp at h
  linarith

/-- **`prop:spec2:mucentre`(c1)**: `Z₀ ≥ 1 − (2Z_⋆ + N_ns + D_col)`. -/
theorem Z0_lower [LinearOrder D.cut.Half] (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hp2 : p ≠ 2) (he : ∀ i, SecondOrder.graphCountError (p := p) D.halfGraph i < 1)
    {Nns Dcol : ℝ} (hns : ∀ x, ‖nsOp D hne x‖ ≤ Nns * ‖x‖)
    (hcoll : ∀ x, ‖collOp D hne x‖ ≤ Dcol * ‖x‖) :
    1 - (2 * Spectral.starZstar (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2)
        D.halfGraph (D.half_nonempty hne) he) D.Nset (Spectral.starCoef (p := p) D) + Nns + Dcol) ≤
      Z0 D hne := by
  obtain ⟨-, hstar, hZs⟩ := Spectral.glue_mucentre_star_closed D hW hMR hp2 hne he
  have h := Spectral.mucentre_Z (𝕜 := ℝ) (K0op D hne) (Spectral.starOp D hne) (nsOp D hne)
    (collOp D hne) (Spectral.cutOne D hne) (Spectral.norm_cutOne D hne)
    (fun x => K0_expansion D hne hp2 x) (hstar.trans (by simp)) hZs hns hcoll
  rw [inner_K0_one] at h
  have h2 := h.2
  rw [Real.norm_eq_abs, abs_le] at h2
  linarith [h2.1]

/-- **`thm:spectral-criterion`(a) for the cut laws `λ_p(G⁺)` at `p ≡ 3 (mod 4)`**, with the
character expansion discharged: as `spectral_criterion_cut_small`, with `K₀ = T_{2^{m_×}K}`,
`Z₀ = 2^{m_×}Z`, `T_ns = nsOp`, `T_coll = collOp` and `Z₀ ≥ 1 − ε_Z` proved; the operator bounds
`hns`, `hcoll` for these explicit kernels (`lem:matching:extractionk`, `lem:oct24-collision`) and
the scalar `hεZc` remain. -/
theorem spectral_criterion_cut_exp [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) (hp3 : p % 4 = 3) {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    -- error conditions
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
    (hS1 : TraceMixing.coarseErr p Δ nn < 1)
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    -- the character expansion: bounds for the explicit nonstar and collision operators
    {εZ Nns Dcol : ℝ} (hεZ : εZ < 1)
    (hns : ∀ x, ‖nsOp D hne x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖collOp D hne x‖ ≤ Dcol * ‖x‖)
    (hεZc : 2 * Spectral.starZstar (SecondOrder.graphPinned
        (Labellings.weilBound_of_target hW p hp2) D.halfGraph (D.half_nonempty hne)
        (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) + Nns + Dcol ≤
        εZ)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE lamH εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (D.Nset k).card *
          (1 + TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) *
          devConst (Rprime p D nn l k)
            (TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) ^ 2 +
        (Fintype.card D.cut.Half : ℝ) * 4 ^ (D.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) (Rprime p D nn l) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ lamH + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : D.cut.Half,
      D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) ^ 2 *
        (2 ^ Labellings.nbrCount D.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase j) j)
            (Fintype.card D.cut.Half))) - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ ρ)
    (hlam : ∀ w : D.cut.Half → ℂ,
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
    -- the certified numbers of `lem:spec:degone`
    {ΛD ηQ εV : ℝ} (hΛD : 0 ≤ ΛD) (hηQ0 : 0 ≤ ηQ) (hDE : NormLe (deltaE (sgnZ (p := p) D)) ΛD)
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) D k l = 0 then mXcut p D k l else 0) ≤ ρs)
    (hηQc : ΛD / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card D.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mVcut p D k l) ≤ ρv)
    (hεVc : ((Fintype.card D.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) +
        (p : ℝ) / ((p : ℝ) - 1) * rp p * ρv ≤ εV) (hεV : 0 ≤ εV)
    -- WP-A's finite tests
    {cbar ηQbar ηBbar εVbar sp sm g : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2)
          D.halfGraph (D.half_nonempty hne)
          (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) +
          Nns + Dcol) / (1 - εZ)) ^ 2 ≤ cbar * rp p)
    (hηQ : ηQ ≤ ηQbar)
    (hηB : etaBcx p (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) ^ 2 *
        (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn))⁻¹)
        lamH εH θ ρ ΓE lamH 1
        ((PaleyB.ncSets Adj).card * Fintype.card D.cut.Half : ℝ) εV ΛD ηQ ≤ ηBbar)
    (hεVb : εV ≤ εVbar) (hεV0 : 0 ≤ εVbar) (hεV1 : εVbar < 1) (hsp : 0 < sp) (hsm : 0 < sm)
    (htp : ∀ ξ : ZMod p, (IsSquare ξ ∧ ξ ≠ 0) →
      Sarkozy.Spectral.FiniteTest (fun x => (qform (azero (sgnZ (p := p) D) ξ) x).re)
        (qXcx Adj D.Nset (sgnZ (p := p) D) ξ) cbar sp ηQbar ηBbar)
    (htm : ∀ ξ : ZMod p, ¬ (IsSquare ξ ∧ ξ ≠ 0) →
      Sarkozy.Spectral.FiniteTest (fun x => (qform (azero (sgnZ (p := p) D) ξ) x).re)
        (qXcx Adj D.Nset (sgnZ (p := p) D) ξ) cbar sm ηQbar ηBbar)
    (hgp : (cbar + sp) / (1 - εVbar) ≤ g) (hgm : (cbar + sm) / (1 - εVbar) ≤ g)
    (f : EuclideanSpace ℝ (D.cut.Half → ZMod p)) :
    -(g * rp p) * ‖f‖ ^ 2 ≤ ⟪f, Spectral.cutOp D hne f⟫_ℝ := by
  have he := (errors_of_S1 D hn hdeg hS1).2.2.1
  have hZ : 1 - εZ ≤ Z0 D hne := le_trans (by linarith) (Z0_lower D hne hW hMR hp2 he hns hcoll)
  exact spectral_criterion_cut_small D hW hMR Adj hp2 hp3 hn hne hdeg hS1 l hnd hcov hdisj
    (K0op D hne) (nsOp D hne) (collOp D hne) hεZ hZ (cutOp_eq_K0 D hne) (K0_expansion D hne hp2)
    hns hcoll hΓc hrow hrowX hεH hΛ0 hθ0 hθ hρ hlam hΛD hηQ0 hDE hrowS hηQc hrowV hεVc hεV hcbar0
    hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

end Sarkozy.SpectralD.Cx
