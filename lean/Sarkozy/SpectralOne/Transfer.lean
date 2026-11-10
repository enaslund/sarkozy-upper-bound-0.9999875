module

public import Sarkozy.SpectralOne.Rfull

@[expose] public section

/-!
# `lem:spec2:parity-transfer` for the cut laws

`paper/sections/14_spectral.tex`, `lem:spec2:parity-transfer`: "Let `p ≡ 1 (mod 4)`, take
instance (A), and let `ε_ϱ ≥ ‖ϱ − 1‖_μ`. Then for every `J` with `|J| ≥ 2` that is not
coverable, `|t_J|/r ≤ R_full − 1 + n/((p − n) r) + ε_ϱ`. Consequently
`ζ̄ = min{ζ, R_full − 1 + n/((p − n) r) + ε_ϱ}` is admissible in `cor:spec2:coupling`." The
certificate uses the transfer at the root cuts LL20 and LL22, whose class-one caps are inputs of
the tail law (`lem:tail-law`(i)).

* `tJ_noncov_le`: the isolated-vertex bound for `ν = ϱ λ(G⁺)` with any density
  `ϱ ∈ [R₀⁻¹, R₀]` on `Inj_p(G⁺)`, with the paper's `R_full` (`R₀ = R_cut` is `hzeta_cut_paper`,
  `R₀ = 1` the case `ν = μ` of the transfer);
* **`hzeta_cut_transfer`**: the transfer bound, from WP-K's `parity_transfer_bound`
  (Cauchy–Schwarz, `‖S_J‖ ≤ r`);
* **`hzeta_cut_min`**: `ζ̄ = min{ζ, ζ_tr}` is admissible: S1's hypothesis `hζ` with this `ζ̄`.

`ε_ϱ` is a hypothesis in the paper's form `‖ϱ − 1‖_{L²(μ)} ≤ ε_ϱ` (the paper takes
`ε_ϱ = R_Z(M_⋆ + N_ns + D_col)`, `prop:spec2:mucentre`(c3)).

New material for this paper.
-/

namespace Sarkozy.SpectralOne

attribute [local instance] feasibleDec

open Finset Sarkozy.SpectralC Sarkozy.Labellings

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- The completion counts of the labellings of `J` lie in `[L_J, U_J]` (`lem:extension`). -/
lemma hcnt_cut (hW : WeilBound (ZMod p)) {m : ℕ} (hm : Fintype.card D.cut.Half ≤ m)
    (J : Finset D.cut.Half) :
    ∀ y ∈ feasCfgs (p := p) D.halfGraph J,
      lowJ (p := p) D m J ≤ extCount D.halfGraph J y ∧
        (extCount D.halfGraph J y : ℝ) ≤ upJ (p := p) D J := by
  intro y hy
  exact extCount_bounds hW D.halfGraph hm _ _ y (nodup_toList _)
    (fun w => by
      by_cases hw : w ∈ J
      · exact Or.inl hw
      · exact Or.inr (mem_toList.mpr (mem_sdiff.mpr ⟨mem_univ _, hw⟩)))
    (fun w hw => (mem_sdiff.mp (mem_toList.mp hw)).2) (mem_filter.mp hy).2

/-- **The non-coverable Paley averages for `ν = ϱ λ(G⁺)`** (`lem:spec2:paley-one`): for every
density `ϱ ∈ [R₀⁻¹, R₀]` on `Inj_p(G⁺)`, `|t_J| ≤ ((R₀ R_full − 1) + m/((p − m) r)) r` on the
non-coverable `J` (every non-coverable `J` has an isolated vertex), with the paper's `R_full`. -/
theorem tJ_noncov_le (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (hne : (injLabellings (ZMod p) D.G).Nonempty) (ϱ : (D.cut.Half → ZMod p) → ℝ) {R₀ : ℝ}
    (hR₀ : 1 ≤ R₀) (hϱ : ∀ x ∈ injLabellings (ZMod p) D.halfGraph, R₀⁻¹ ≤ ϱ x ∧ ϱ x ≤ R₀)
    {m : ℕ} (hm : Fintype.card D.cut.Half ≤ m) (hmp : m < p)
    (he : ∀ i, TraceMixing.coarseErr p (deg0 D i) m < 1)
    (Adj : D.cut.Half → D.cut.Half → Prop)
    (hAdj : ∀ i j : D.cut.Half, (i, j) ∈ D.halfGraph.E ∨ (j, i) ∈ D.halfGraph.E → Adj i j)
    (J : Finset D.cut.Half) (hnc : ¬ SpectralD.PaleyB.Coverable Adj J) :
    ‖SpectralD.PaleyB.tJ (fun x => (D.halfLaw hne).weight x * ϱ x) J‖ ≤
      ((R₀ * RfullPaper (p := p) D m - 1) + (m : ℝ) / (((p : ℝ) - m) * rp p)) * rp p := by
  -- an isolated vertex
  have hiso : ∃ j ∈ J, ∀ i ∈ J, i ≠ j → ¬ Adj i j := by
    by_contra h
    push Not at h
    exact hnc fun j hj => by
      obtain ⟨i, hi, hij, hadj⟩ := h j hj
      exact ⟨i, hi, hij, hadj⟩
  obtain ⟨j, hjJ, hjiso⟩ := hiso
  set J' := J.erase j with hJ'
  have hJeq : insert j J' = J := insert_erase hjJ
  have hj' : j ∉ J' := notMem_erase j J
  have hiso' : ∀ i ∈ J', (i, j) ∉ D.halfGraph.E ∧ (j, i) ∉ D.halfGraph.E := by
    intro i hi
    have hij : i ≠ j := ne_of_mem_erase hi
    have hna := hjiso i (mem_of_mem_erase hi) hij
    exact ⟨fun h => hna (hAdj i j (Or.inl h)), fun h => hna (hAdj i j (Or.inr h))⟩
  rw [← hJeq]
  have hL := lowJ_pos D he (insert j J')
  have h := tJ_graph_le hp2 D.halfGraph (D.half_nonempty hne) ϱ hR₀ hϱ hj' hiso' hL
    (hcnt_cut D hW hm (insert j J'))
  have hr : 0 < rp p := by
    unfold rp
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  -- `U_J/L_J ≤ R_full`
  have hratio : upJ (p := p) D (insert j J') / lowJ (p := p) D m (insert j J') ≤
      RfullPaper (p := p) D m := by
    rw [div_le_iff₀ hL]; exact upJ_le_RfullPaper D he _
  have h1 : (R₀ * (upJ (p := p) D (insert j J') / lowJ (p := p) D m (insert j J')) - 1) * rp p ≤
      (R₀ * RfullPaper (p := p) D m - 1) * rp p := by
    apply mul_le_mul_of_nonneg_right _ hr.le
    have := mul_le_mul_of_nonneg_left hratio (by linarith : (0 : ℝ) ≤ R₀)
    linarith
  -- `(|J'| + 1)/(p − |J'|) ≤ m/(p − m)`
  have hJcard : J'.card + 1 ≤ m := by
    have h1 : J'.card + 1 = J.card := by rw [hJ']; exact card_erase_add_one hjJ
    have h2 : J.card ≤ Fintype.card D.cut.Half := card_le_univ J
    omega
  have hmpR : (m : ℝ) < p := by exact_mod_cast hmp
  have h2 : ((J'.card : ℝ) + 1) / ((p : ℝ) - J'.card) ≤ (m : ℝ) / ((p : ℝ) - m) := by
    have hc : (J'.card : ℝ) + 1 ≤ m := by exact_mod_cast hJcard
    have hd : (p : ℝ) - m ≤ (p : ℝ) - J'.card := by linarith
    have hpm : (0 : ℝ) < (p : ℝ) - m := by linarith
    calc ((J'.card : ℝ) + 1) / ((p : ℝ) - J'.card) ≤ (m : ℝ) / ((p : ℝ) - J'.card) :=
          div_le_div_of_nonneg_right hc (by linarith)
      _ ≤ (m : ℝ) / ((p : ℝ) - m) := div_le_div_of_nonneg_left (by positivity) hpm hd
  have h3 : (m : ℝ) / ((p : ℝ) - m) = (m : ℝ) / (((p : ℝ) - m) * rp p) * rp p := by
    field_simp
  calc ‖SpectralD.PaleyB.tJ (fun x => (D.halfLaw hne).weight x * ϱ x) (insert j J')‖
      ≤ (R₀ * (upJ (p := p) D (insert j J') / lowJ (p := p) D m (insert j J')) - 1) * rp p +
          ((J'.card : ℝ) + 1) / ((p : ℝ) - J'.card) := h
    _ ≤ (R₀ * RfullPaper (p := p) D m - 1) * rp p +
          (m : ℝ) / (((p : ℝ) - m) * rp p) * rp p := by
        rw [← h3]; exact add_le_add h1 h2
    _ = ((R₀ * RfullPaper (p := p) D m - 1) + (m : ℝ) / (((p : ℝ) - m) * rp p)) * rp p := by
        ring

/-- **`lem:spec2:parity-transfer`** (instance (A) of the cut): with `ε_ϱ ≥ ‖ϱ − 1‖_μ`,
`|t_J| ≤ (R_full − 1 + m/((p − m) r) + ε_ϱ) r` for every non-coverable `J`, `|J| ≥ 2`. -/
theorem hzeta_cut_transfer (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (hne : (injLabellings (ZMod p) D.G).Nonempty)
    {m : ℕ} (hm : Fintype.card D.cut.Half ≤ m) (hmp : m < p)
    (he : ∀ i, TraceMixing.coarseErr p (deg0 D i) m < 1)
    (Adj : D.cut.Half → D.cut.Half → Prop)
    (hAdj : ∀ i j : D.cut.Half, (i, j) ∈ D.halfGraph.E ∨ (j, i) ∈ D.halfGraph.E → Adj i j)
    {ερ : ℝ} (hερ : Real.sqrt (∑ x, (D.halfLaw hne).weight x *
      (SpectralD.Cx.rhoK (D.halfLaw hne).weight (SpectralD.Cx.cutKn D hne) x - 1) ^ 2) ≤ ερ) :
    ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ SpectralD.PaleyB.Coverable Adj J →
      ‖SpectralD.PaleyB.tJ (SpectralD.Cx.nuA D hne) J‖ ≤
        ((RfullPaper (p := p) D m - 1) + (m : ℝ) / (((p : ℝ) - m) * rp p) + ερ) * rp p := by
  intro J _ hnc
  set μ := (D.halfLaw hne).weight with hμ
  -- the bound for `ν = μ` (`R₀ = 1`)
  have hB := tJ_noncov_le D hW hp2 hne (fun _ => 1) le_rfl
    (fun x _ => by norm_num) hm hmp he Adj hAdj J hnc
  have hB' : ‖∑ x, (μ x : ℂ) * SJ J x‖ ≤
      ((RfullPaper (p := p) D m - 1) + (m : ℝ) / (((p : ℝ) - m) * rp p)) * rp p := by
    have e : SpectralD.PaleyB.tJ (fun x => (D.halfLaw hne).weight x * 1) J =
        ∑ x, (μ x : ℂ) * SJ J x := by
      unfold SpectralD.PaleyB.tJ
      simp only [mul_one, hμ]
    rw [← e]
    simpa only [one_mul] using hB
  have h := parity_transfer_bound μ
    (SpectralD.Cx.rhoK (D.halfLaw hne).weight (SpectralD.Cx.cutKn D hne)) (SJ J)
    (D.halfLaw hne).nonneg (D.halfLaw hne).total (fun x => norm_SJ_le hp2 J x) hερ hB'
  exact h

/-- **`ζ̄ = min{ζ, R_full − 1 + m/((p − m) r) + ε_ϱ}` is admissible** (`lem:spec2:parity-transfer`,
consequence): S1's hypothesis `hζ` of `cor:spec2:coupling` with this `ζ̄`. -/
theorem hzeta_cut_min (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2) {nn : ℕ}
    (hn : Fintype.card W ≤ nn) (hne : (injLabellings (ZMod p) D.G).Nonempty)
    (he1 : ∀ i, TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) nn < 1)
    {m : ℕ} (hm : Fintype.card D.cut.Half ≤ m) (hmp : m < p)
    (he : ∀ i, TraceMixing.coarseErr p (deg0 D i) m < 1)
    (Adj : D.cut.Half → D.cut.Half → Prop)
    (hAdj : ∀ i j : D.cut.Half, (i, j) ∈ D.halfGraph.E ∨ (j, i) ∈ D.halfGraph.E → Adj i j)
    {ερ : ℝ} (hερ : Real.sqrt (∑ x, (D.halfLaw hne).weight x *
      (SpectralD.Cx.rhoK (D.halfLaw hne).weight (SpectralD.Cx.cutKn D hne) x - 1) ^ 2) ≤ ερ) :
    ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ SpectralD.PaleyB.Coverable Adj J →
      ‖SpectralD.PaleyB.tJ (SpectralD.Cx.nuA D hne) J‖ ≤
        min ((D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) *
              RfullPaper (p := p) D m - 1) + (m : ℝ) / (((p : ℝ) - m) * rp p))
          ((RfullPaper (p := p) D m - 1) + (m : ℝ) / (((p : ℝ) - m) * rp p) + ερ) * rp p := by
  intro J hJ2 hnc
  have h1 := hzeta_cut_paper D hW hp2 hn hne he1 hm hmp he Adj hAdj J hJ2 hnc
  have h2 := hzeta_cut_transfer D hW hp2 hne hm hmp he Adj hAdj hερ J hJ2 hnc
  rw [min_mul_of_nonneg _ _ (by unfold rp; positivity)]
  exact le_min h1 h2

end Sarkozy.SpectralOne
