module

public import Sarkozy.SpectralD.SmallTailErrors
public import Sarkozy.SpectralD.TailAtMost
public import Sarkozy.SpectralD.ParityAtMost
public import Sarkozy.SpectralD.TailEtaBOne
public import Sarkozy.SpectralOne.ChainGen

/-!
# A tail criterion for smaller spectral cuts

The graph size and degree bounds supply the analytic inputs. What
remains is the finite model test for each Fourier character.
-/

@[expose] public section

namespace Sarkozy.SpectralD.AtMost

open Finset Sarkozy.SpectralC Sarkozy.SpectralD.Cx Sarkozy.Labellings
open scoped InnerProductSpace

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W]

theorem tail_criterion (D : Cuts.SpecData W) [LinearOrder D.cut.Half]
    (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hAdj : ∀ i j, (i, j) ∈ D.halfGraph.E ∨ (j, i) ∈ D.halfGraph.E → Adj i j)
    (hW : Target.Weil) (hMR : Target.MovingRoot) (h4 : Extraction.FourCycleBound p)
    (hp : 2 ^ 512 ≤ p) (hne : (injLabellings (ZMod p) D.G).Nonempty)
    (hnW : Fintype.card W ≤ 72) (hn : Fintype.card D.cut.Half ≤ 18)
    (hm : D.crossPairs.card ≤ 96)
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ 20)
    (hd : ∀ j, nbrCount D.halfGraph (univ.erase j) j ≤ 10)
    (hr : ∀ k, (D.Nset k).card ≤ 12)
    (he : ∀ i, SecondOrder.graphCountError (p := p) D.halfGraph i < 1)
    (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ 301768740)
    (hlam : ∀ x, (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) x).re ≤
      8928 * ∑ j, ‖x j‖ ^ 2)
    (hplus : ∀ x, (qform (PaleyB.hplusM Adj D.Nset (sgnZ (p := p) D)) x).re ≤
      12384 * ∑ j, ‖x j‖ ^ 2)
    (hDE : NormLe (deltaE (sgnZ (p := p) D)) 12)
    {s g : ℝ} (hs : 0 < s)
    (hfinite : ∀ ξ : ZMod p,
      Spectral.FiniteTest (fun x => (qform (azero (sgnZ D) ξ) x).re)
        (qXcx Adj D.Nset (sgnZ D) ξ) (1 / 4) s (1 / 1000) (3 / 20))
    (hcap : ((1 / 4 : ℝ) + s) / (1 - 1 / 100) ≤ g)
    (v : EuclideanSpace ℝ (D.cut.Half → ZMod p)) :
    -(g * rp p) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp D hne v⟫_ℝ := by
  have hn36 : Fintype.card D.cut.Half ≤ 36 := by omega
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hExp := small_tail_expansion_bounds D (weilBound_of_target hW p (by omega))
    h4 hp hn hm hd hr hne he
  have ha := tail_analytic_inputs D hp hnW hn36 hdeg hd hr
  have ht : ∀ i, D.tdeg i ≤ 24 := fun i => (tdeg_le D hdeg i).trans (by norm_num)
  have hζ := noncoverable_tail D (weilBound_of_target hW p (by omega)) hp hnW
    hn36 ht (fun j => (hd j).trans (by norm_num)) hne Adj hAdj
  apply SpectralOne.spectral_criterion_cut_exp_gen D hW hMR Adj
    (by omega) hnW hne hdeg (by
      exact (coarseErr_tail hp (by norm_num : 20 ≤ 24) le_rfl).trans_lt (by norm_num))
    (restList D) (restList_nodup D) (restList_cover D) (restList_disj D)
    (εZ := 1 / 100) (Nns := 2⁻¹ ^ 50 * (Real.sqrt p)⁻¹)
    (Dcol := 2⁻¹ ^ 50 * (Real.sqrt p)⁻¹)
    (ΓE := 1 / 100000000) (lamH := 8928) (εH := 1 / 1000)
    (ρβ := 1 / 2000) (ρX := 1 / 2000) (θ := 64) (ρ := 301768740)
    (ζ := 2⁻¹ ^ 80) (Λp := 12384) (ΛD := 12) (ηQ := 1 / 1000) (εV := 1 / 100000)
    (ρs := 2⁻¹ ^ 40) (ρv := 36) (cbar := 1 / 4) (ηQbar := 1 / 1000)
    (ηBbar := 3 / 20) (εVbar := 1 / 100) (sp := s) (sm := s)
    (by norm_num) hExp.1 hExp.2.1 hExp.2.2.1 ha.coupling ha.beta ha.cross
    (by norm_num) (by norm_num) (by norm_num) ha.theta hρ hlam
    (by positivity) (fun _ => hζ) _ (by norm_num) (by norm_num) hDE ha.smallX
    (by
      have hnum : (Fintype.card D.cut.Half : ℝ) ≤ 36 := by exact_mod_cast hn36
      apply le_trans _ (tail_etaQ hp (d := 12) le_rfl)
      unfold rp
      gcongr)
    ha.smallV (by
      have hnum : (Fintype.card D.cut.Half : ℝ) ≤ 36 := by exact_mod_cast hn36
      apply le_trans _ (tail_epsilonV hp)
      unfold rp
      gcongr)
    (by norm_num) (by norm_num) hExp.2.2.2 le_rfl _
    (by norm_num) (by norm_num) (by norm_num) hs hs
    (fun ξ _ => hfinite ξ) (fun ξ _ => hfinite ξ) hcap hcap v
  · intro x
    simpa only [PaleyB.qform_hplusM_re] using hplus x
  · apply etaB_tail_with_parity hp ha.density (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity) (by positivity)
    exact parity_term_tail Adj hn36 le_rfl

end Sarkozy.SpectralD.AtMost
