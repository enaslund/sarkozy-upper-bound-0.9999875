module

public import Sarkozy.SpectralD.CxSmall

@[expose] public section

/-!
# `lem:spec:small`(a) for the cut law, and the small-pair matrices

`paper/sections/14_spectral.tex`, `lem:spec:small`(a): for `k, l ∈ U⁺` with `ς_kl = 0`
(including `k = l`), `|E_Λ χ(x'_l − x_k)| ≤ min(δ^×_k, δ^×_l)`. The cut law `Λ = μ ⊗ μ · K/Z` is
the law of the two halves under `λ_p(G)` (WP-P's `expect_halves`; `sum_cutLaw_eq`), and
`x'_l − x_k = y_{ϑl} − y_k` with `k`, `ϑl` distinct and non-adjacent in `G`, so
`graph_pair_corr` applies to `G` (`2n` vertices). The swap symmetry of `Λ` gives the other
bound (`norm_deltaX_swap`).

* `sum_cutLaw_eq`, `sgnZ_eq_zero_iff`, `deltaX_small`, `norm_deltaX_swap`, `deltaX_small_min`;
* `deltaXConst`, `deltaMuConst`, `mXcut`, `mVcut`: the constants and matrices of
  `lem:spec:degone` with the paper's choices (`m^μ_kl = 1` on the internal edges);
* `hsmall_cut`, `hDeltaMu_cut`: the hypotheses `hsmall`, `hΔμ` of the criterion for these
  matrices, under the error condition (S1).

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC Sarkozy.Characters
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- **`Λ` is the law of the halves under `λ_p(G)`**: `∑_z Λ(z) Φ(z) = E_λ Φ(y|_{U⁺}, y|_{ϑU⁺})`. -/
lemma sum_cutLaw_eq (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (Φ : (D.cut.Half → ZMod p) × (D.cut.Half → ZMod p) → ℝ) :
    ∑ z, cutLaw (D.halfLaw hne).weight (cutKn D hne) z * Φ z =
      ∑ y, graphWeight D.G hne y * Φ (D.halfL y, D.halfR y) := by
  have h := D.expect_halves hne (fun x x' => Φ (x, x'))
  have e1 : (Labellings.graphLaw D.G hne).expect (fun y => Φ (D.halfL y, D.halfR y)) =
      ∑ y, graphWeight D.G hne y * Φ (D.halfL y, D.halfR y) := rfl
  have e2 : ((D.halfLaw hne).product (D.halfLaw hne)).expect
      (fun q => D.cutK q.1 q.2 * Φ (q.1, q.2)) =
      ∑ z, (D.halfLaw hne).weight z.1 * (D.halfLaw hne).weight z.2 * (D.cutK z.1 z.2 * Φ z) :=
    rfl
  rw [e1, e2, sum_div] at h
  rw [h]
  refine sum_congr rfl fun z _ => ?_
  unfold cutLaw cutKn
  ring

/-- `ς_kl = 0` iff `k` and `ϑl` are not adjacent in `G`. -/
lemma sgnZ_eq_zero_iff (k l : D.cut.Half) :
    sgnZ (p := p) D k l = 0 ↔ (k.1, D.cut.flip l.1) ∉ D.G.E ∧ (D.cut.flip l.1, k.1) ∉ D.G.E := by
  unfold sgnZ Cuts.SpecData.sgn
  by_cases h1 : (k.1, D.cut.flip l.1) ∈ D.G.E
  · simp [h1]
  · by_cases h2 : (D.cut.flip l.1, k.1) ∈ D.G.E
    · simp [h1, h2]
    · simp [h1, h2]

/-- **`lem:spec:small`(a)**: for `ς_kl = 0`, `|δ^×_kl| ≤ δ^×_l`, the constant of the vertex `ϑl`
of `G`, with `e_t = e_t(p, |W|)`. -/
theorem deltaX_small (hW : Labellings.WeilBound (ZMod p))
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) {k l : D.cut.Half}
    (hkl : sgnZ (p := p) D k l = 0)
    (he : TraceMixing.coarseErr p
      (Labellings.nbrCount D.G (univ.erase (D.cut.flip l.1)) (D.cut.flip l.1))
      (Fintype.card W) < 1) :
    ‖deltaX (cutLaw (D.halfLaw hne).weight (cutKn D hne)) k l‖ ≤
      smallConst p (Labellings.nbrCount D.G (univ.erase (D.cut.flip l.1)) (D.cut.flip l.1))
        (Fintype.card W) := by
  obtain ⟨h1, h2⟩ := (sgnZ_eq_zero_iff D k l).mp hkl
  have huv : k.1 ≠ D.cut.flip l.1 := by
    intro h
    have hm : D.cut.flip l.1 ∈ D.cut.half := h ▸ k.2
    exact (D.cut.crosses l.1).mp hm l.2
  have hcorr := graph_pair_corr hW D.G hne huv h1 h2 he
  have hreal : deltaX (cutLaw (D.halfLaw hne).weight (cutKn D hne)) k l =
      ((∑ z, cutLaw (D.halfLaw hne).weight (cutKn D hne) z *
        ((quadraticChar (ZMod p) (z.2 l - z.1 k) : ℤ) : ℝ) : ℝ) : ℂ) := by
    unfold deltaX
    push_cast
    refine sum_congr rfl fun z _ => ?_
    simp only [chiC, MulChar.ringHomComp_apply, eq_intCast]
  rw [hreal, sum_cutLaw_eq D hne (fun z => ((quadraticChar (ZMod p) (z.2 l - z.1 k) : ℤ) : ℝ))]
  convert hcorr using 2
  push_cast
  refine sum_congr rfl fun y _ => ?_
  simp only [Cuts.SpecData.halfL, Cuts.SpecData.halfR, chiC, MulChar.ringHomComp_apply,
    eq_intCast]

/-- `|δ^×_lk| = |δ^×_kl|` (the swap symmetry of `Λ` and `χ(−x) = χ(−1)χ(x)`). -/
lemma norm_deltaX_swap (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (k l : D.cut.Half) :
    ‖deltaX (cutLaw (D.halfLaw hne).weight (cutKn D hne)) l k‖ =
      ‖deltaX (cutLaw (D.halfLaw hne).weight (cutKn D hne)) k l‖ := by
  set Λ := cutLaw (D.halfLaw hne).weight (cutKn D hne) with hΛ
  have hsym : ∀ z : (D.cut.Half → ZMod p) × (D.cut.Half → ZMod p), Λ z.swap = Λ z := by
    intro z
    rw [hΛ]
    unfold cutLaw cutKn
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [D.cutK_symm]
    ring
  unfold deltaX
  rw [← (Equiv.prodComm _ _).sum_comp]
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, hsym]
  have e : ∀ z : (D.cut.Half → ZMod p) × (D.cut.Half → ZMod p),
      (Λ z : ℂ) * chiC p (z.1 k - z.2 l) = chiC p (-1) * ((Λ z : ℂ) * chiC p (z.2 l - z.1 k)) := by
    intro z
    rw [show z.1 k - z.2 l = -1 * (z.2 l - z.1 k) by ring, map_mul]
    ring
  rw [sum_congr rfl fun z _ => e z, ← mul_sum, norm_mul,
    norm_chiC (fun h => one_ne_zero (neg_eq_zero.mp h)), one_mul]

/-- **`lem:spec:small`(a)**, both bounds: `|δ^×_kl| ≤ min(δ^×_k, δ^×_l)` for `ς_kl = 0`. -/
theorem deltaX_small_min (hW : Labellings.WeilBound (ZMod p))
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) {k l : D.cut.Half}
    (hkl : sgnZ (p := p) D k l = 0)
    (hek : TraceMixing.coarseErr p
      (Labellings.nbrCount D.G (univ.erase (D.cut.flip k.1)) (D.cut.flip k.1))
      (Fintype.card W) < 1)
    (hel : TraceMixing.coarseErr p
      (Labellings.nbrCount D.G (univ.erase (D.cut.flip l.1)) (D.cut.flip l.1))
      (Fintype.card W) < 1) :
    ‖deltaX (cutLaw (D.halfLaw hne).weight (cutKn D hne)) k l‖ ≤
      min (smallConst p (Labellings.nbrCount D.G (univ.erase (D.cut.flip k.1)) (D.cut.flip k.1))
          (Fintype.card W))
        (smallConst p (Labellings.nbrCount D.G (univ.erase (D.cut.flip l.1)) (D.cut.flip l.1))
          (Fintype.card W)) := by
  refine le_min ?_ (deltaX_small D hW hne hkl hel)
  rw [← norm_deltaX_swap D hne]
  exact deltaX_small D hW hne ((sgnZ_zero_iff D k l).mp hkl) hek

variable (p) in
/-- `δ^×_k = (e_{d_k} + e_{d_k+1})/(1 − e_{d_k})`, `d_k` the degree of `ϑk` in `G`,
`e_t = e_t(p, |W|)`. -/
noncomputable def deltaXConst (k : D.cut.Half) : ℝ :=
  smallConst p (Labellings.nbrCount D.G (univ.erase (D.cut.flip k.1)) (D.cut.flip k.1))
    (Fintype.card W)

variable (p) in
/-- `δ^μ_k = (e_{d⁰_k} + e_{d⁰_k+1})/(1 − e_{d⁰_k})`, `d⁰_k` the degree of `k` in `G⁺`,
`e_t = e_t(p, |U⁺|)`. -/
noncomputable def deltaMuConst (k : D.cut.Half) : ℝ :=
  smallConst p (Labellings.nbrCount D.halfGraph (univ.erase k) k) (Fintype.card D.cut.Half)

variable (p) in
/-- The small-pair matrix of `lem:spec:degone`(b): `min(δ^×_k, δ^×_l)` where `ς_kl = 0`. -/
noncomputable def mXcut (k l : D.cut.Half) : ℝ := by
  classical
  exact if sgnZ (p := p) D k l = 0 then min (deltaXConst p D k) (deltaXConst p D l) else 0

variable (p) in
/-- The matrix of `lem:spec:degone`(c): `1` on the internal edges, `min(δ^μ_k, δ^μ_l)` on the
other pairs `k ≠ l`. -/
noncomputable def mVcut (k l : D.cut.Half) : ℝ := by
  classical
  exact if k = l then 0 else
    if (k, l) ∈ D.halfGraph.E ∨ (l, k) ∈ D.halfGraph.E then 1
    else min (deltaMuConst p D k) (deltaMuConst p D l)

section Errors

variable {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
  (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
  (hS1 : TraceMixing.coarseErr p Δ nn < 1)
include hn hdeg hS1

omit hn hS1 in
/-- The degrees of `G` are at most `Δ`. -/
lemma nbrCount_G_le (v : W) : Labellings.nbrCount D.G (univ.erase v) v ≤ Δ := by
  classical
  unfold Labellings.nbrCount
  refine le_trans (card_le_card fun w hw => ?_) (hdeg v)
  simp only [mem_filter, mem_univ, true_and, mem_erase] at hw ⊢
  rcases hw.2 with h | h
  · exact Or.inr h
  · exact Or.inl h

lemma eX_lt (k : D.cut.Half) : TraceMixing.coarseErr p
    (Labellings.nbrCount D.G (univ.erase (D.cut.flip k.1)) (D.cut.flip k.1))
    (Fintype.card W) < 1 := by
  have hq0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  exact lt_of_le_of_lt (TraceMixing.coarseErr_mono hq0
    (nbrCount_G_le D hdeg _) hn) hS1

lemma eMu_lt (k : D.cut.Half) : TraceMixing.coarseErr p
    (Labellings.nbrCount D.halfGraph (univ.erase k) k) (Fintype.card D.cut.Half) < 1 := by
  have hq0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hU : Fintype.card D.cut.Half ≤ nn :=
    (Fintype.card_le_of_injective (fun u : D.cut.Half => u.1) fun a b h => Subtype.ext h).trans hn
  exact lt_of_le_of_lt (TraceMixing.coarseErr_mono hq0 (nbrCount_half_le D hdeg k) hU) hS1

lemma mXcut_nonneg (k l : D.cut.Half) : 0 ≤ mXcut p D k l := by
  unfold mXcut
  split_ifs
  · exact le_min (smallConst_nonneg (eX_lt D hn hdeg hS1 k))
      (smallConst_nonneg (eX_lt D hn hdeg hS1 l))
  · exact le_refl 0

lemma mVcut_nonneg (k l : D.cut.Half) : 0 ≤ mVcut p D k l := by
  unfold mVcut
  split_ifs
  · exact le_refl 0
  · exact zero_le_one
  · exact le_min (smallConst_nonneg (eMu_lt D hn hdeg hS1 k))
      (smallConst_nonneg (eMu_lt D hn hdeg hS1 l))

omit hn hdeg hS1 in
lemma mXcut_symm (k l : D.cut.Half) : mXcut p D k l = mXcut p D l k := by
  unfold mXcut
  by_cases h : sgnZ (p := p) D k l = 0
  · have h' : sgnZ (p := p) D l k = 0 := (sgnZ_zero_iff D k l).mp h
    simp only [h, h', ↓reduceIte, min_comm]
  · have h' : ¬ sgnZ (p := p) D l k = 0 := fun h'' => h ((sgnZ_zero_iff D k l).mpr h'')
    simp only [h, h', ↓reduceIte]

omit hn hdeg hS1 [Fact p.Prime] in
lemma mVcut_symm (k l : D.cut.Half) : mVcut p D k l = mVcut p D l k := by
  unfold mVcut
  by_cases h : k = l
  · subst h; rfl
  · have h' : l ≠ k := fun h'' => h h''.symm
    by_cases ha : (k, l) ∈ D.halfGraph.E ∨ (l, k) ∈ D.halfGraph.E
    · have ha' : (l, k) ∈ D.halfGraph.E ∨ (k, l) ∈ D.halfGraph.E := ha.symm
      simp only [h, h', ha, ha', ↓reduceIte]
    · have ha' : ¬ ((l, k) ∈ D.halfGraph.E ∨ (k, l) ∈ D.halfGraph.E) := fun h'' => ha h''.symm
      simp only [h, h', ha, ha', ↓reduceIte, min_comm]

/-- **`hsmall`** for `m^× = mXcut` (`lem:spec:small`(a)). -/
theorem hsmall_cut (hW : Labellings.WeilBound (ZMod p))
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) (k l : D.cut.Half)
    (hkl : sgnZ (p := p) D k l = 0) :
    ‖deltaX (cutLaw (D.halfLaw hne).weight (cutKn D hne)) k l‖ ≤ mXcut p D k l := by
  have h := deltaX_small_min D hW hne hkl (eX_lt D hn hdeg hS1 k) (eX_lt D hn hdeg hS1 l)
  unfold mXcut
  simp only [hkl, ↓reduceIte]
  exact h

/-- **`hΔμ`** for `m^μ = mVcut` (`lem:spec:small`(b)). -/
theorem hDeltaMu_cut (hW : Labellings.WeilBound (ZMod p))
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) (k l : D.cut.Half) (hkl : k ≠ l) :
    ‖deltaMu (D.halfLaw hne).weight k l‖ ≤ mVcut p D k l := by
  unfold mVcut
  simp only [hkl, ↓reduceIte]
  split_ifs with ha
  · exact norm_deltaMu_le_one D _ (D.halfLaw hne).nonneg (D.halfLaw hne).total k l
  · rw [not_or] at ha
    exact deltaMu_small_min D hW hne hkl ha.1 ha.2 (eMu_lt D hn hdeg hS1 k)
      (eMu_lt D hn hdeg hS1 l)

end Errors

open scoped InnerProductSpace in
/-- **`thm:spectral-criterion`(a) for the cut laws `λ_p(G⁺)` at `p ≡ 3 (mod 4)`**, with
`lem:spec:small` discharged: as `spectral_criterion_cut_S1`, with the paper's small-pair
matrices `m^× = mXcut`, `m^μ = mVcut` (`hsmall_cut`, `hDeltaMu_cut`); their row sums (`hrowS`,
`hrowV`) and the scalar conditions `hηQc`, `hεVc` remain. -/
theorem spectral_criterion_cut_small [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) (hp3 : p % 4 = 3) {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    -- error conditions
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
    (hS1 : TraceMixing.coarseErr p Δ nn < 1)
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    -- the character expansion
    (K₀ Tns Tcoll : EuclideanSpace ℝ (D.cut.Half → ZMod p) →ₗ[ℝ]
      EuclideanSpace ℝ (D.cut.Half → ZMod p))
    {Z₀ εZ Nns Dcol : ℝ} (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z₀)
    (hT : ∀ x, Spectral.cutOp D hne x = (Z₀⁻¹ : ℝ) • K₀ x)
    (hK : ∀ x, K₀ x = ⟪Spectral.cutOne D hne, x⟫_ℝ • Spectral.cutOne D hne +
      Spectral.starOp D hne x + Tns x - Tcoll x)
    (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖)
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
  have hWB := Labellings.weilBound_of_target hW p hp2
  exact spectral_criterion_cut_S1 D hW hMR Adj hp2 hp3 hn hne hdeg hS1 l hnd hcov hdisj K₀ Tns
    Tcoll hεZ hZ hT hK hns hcoll hΓc hrow hrowX hεH hΛ0 hθ0 hθ hρ hlam hΛD hηQ0 hDE (mXcut p D)
    (mXcut_nonneg D hn hdeg hS1) (mXcut_symm D) (fun k l h => hsmall_cut D hn hdeg hS1 hWB hne k l h)
    hrowS hηQc (mVcut p D) (mVcut_nonneg D hn hdeg hS1) (mVcut_symm D)
    (fun k l h => hDeltaMu_cut D hn hdeg hS1 hWB hne k l h) hrowV hεVc hεV hcbar0 hcbar hηQ hηB
    hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

end Sarkozy.SpectralD.Cx
