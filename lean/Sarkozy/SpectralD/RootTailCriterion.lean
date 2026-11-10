module

public import Sarkozy.SpectralD.RootOneGeometry
public import Sarkozy.SpectralD.TailAnalyticInputs
public import Sarkozy.SpectralD.TailParityInputs
public import Sarkozy.SpectralD.TailEtaBOne
public import Sarkozy.SpectralOne.ChainGen

/-!
# A root tail criterion with all scalar allowances supplied

The remaining inputs are the character expansion and the finite model
matrices. The counting, parity, coupling, and degree-one allowances are
provided uniformly for both 36-vertex root halves.
-/

@[expose] public section

namespace Sarkozy.SpectralD.Root

open Finset Sarkozy.SpectralC Sarkozy.SpectralD.Cx Sarkozy.Labellings
open scoped InnerProductSpace

variable {p : ℕ} [Fact p.Prime]

theorem tail_criterion (D : Cuts.SpecData Slot) [LinearOrder D.cut.Half]
    (hG : D.G = rootGraph) (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hp : 2 ^ 512 ≤ p) (hne : (injLabellings (ZMod p) D.G).Nonempty)
    (hn : Fintype.card D.cut.Half = 36)
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ 20)
    (hd : ∀ j, nbrCount D.halfGraph (univ.erase j) j ≤ 10)
    (hr : ∀ k, (D.Nset k).card ≤ 12)
    (he : ∀ i, SecondOrder.graphCountError (p := p) D.halfGraph i < 1)
    (hExp :
      let a := 2⁻¹ ^ 200 * (Real.sqrt p)⁻¹
      let L := SecondOrder.graphPinned (weilBound_of_target hW p (by omega))
        D.halfGraph (D.half_nonempty hne) he
      (∀ v, ‖nsOp D hne v‖ ≤ a * ‖v‖) ∧
      (∀ v, ‖collOp D hne v‖ ≤ a * ‖v‖) ∧
      2 * Spectral.starZstar L D.Nset (Spectral.starCoef (p := p) D) + a + a ≤ 1 / 100 ∧
      (a + a) / (1 - 1 / 100) +
        ((Spectral.starMstar L D.Nset (Spectral.starCoef (p := p) D) +
          a + a) / (1 - 1 / 100)) ^ 2 ≤ 1 / 4 * rp p)
    (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ 301768740)
    (hlam : ∀ x, (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) x).re ≤
      8928 * ∑ j, ‖x j‖ ^ 2)
    (hplus : ∀ x, (qform (PaleyB.hplusM halfAdjB D.Nset (sgnZ (p := p) D)) x).re ≤
      12384 * ∑ j, ‖x j‖ ^ 2)
    (hDE : NormLe (deltaE (sgnZ (p := p) D)) 12)
    {s g : ℝ} (hs : 0 < s)
    (hfinite : ∀ ξ : ZMod p,
      Spectral.FiniteTest (fun x => (qform (azero (sgnZ D) ξ) x).re)
        (qXcx halfAdjB D.Nset (sgnZ D) ξ) (1 / 4) s (1 / 1000) (3 / 20))
    (hcap : ((1 / 4 : ℝ) + s) / (1 - 1 / 100) ≤ g)
    (v : EuclideanSpace ℝ (D.cut.Half → ZMod p)) :
    -(g * rp p) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp D hne v⟫_ℝ := by
  have hp52 : 2 ^ 52 ≤ p := by omega
  have ha := tail_analytic_inputs D hp card_slot.le hn hdeg hd hr
  have ht : ∀ i, D.tdeg i ≤ 24 := fun i => (tdeg_le D hdeg i).trans (by norm_num)
  have hζ := noncoverable_tail D (weilBound_of_target hW p (by omega)) hp card_slot.le
    hn ht (fun j => (hd j).trans (by norm_num)) hne halfAdjB (halfAdjB_contains D hG)
  apply SpectralOne.spectral_criterion_cut_exp_gen D hW hMR halfAdjB
    (by omega) card_slot.le hne hdeg (coarseErr_root_lt_nat hp52)
    (restList D) (restList_nodup D) (restList_cover D) (restList_disj D)
    (εZ := 1 / 100) (Nns := 2⁻¹ ^ 200 * (Real.sqrt p)⁻¹)
    (Dcol := 2⁻¹ ^ 200 * (Real.sqrt p)⁻¹)
    (ΓE := 1 / 100000000) (lamH := 8928) (εH := 1 / 1000)
    (ρβ := 1 / 2000) (ρX := 1 / 2000) (θ := 64) (ρ := 301768740)
    (ζ := 2⁻¹ ^ 80) (Λp := 12384) (ΛD := 12) (ηQ := 1 / 1000) (εV := 1 / 100000)
    (ρs := 2⁻¹ ^ 40) (ρv := 36) (cbar := 1 / 4) (ηQbar := 1 / 1000)
    (ηBbar := 3 / 20) (εVbar := 1 / 100) (sp := s) (sm := s)
    (by norm_num) hExp.1 hExp.2.1 hExp.2.2.1 ha.coupling ha.beta ha.cross
    (by norm_num) (by norm_num) (by norm_num) ha.theta hρ hlam
    (by positivity) (fun _ => hζ) _ (by norm_num) (by norm_num) hDE ha.smallX
    (by simpa only [hn, Nat.cast_ofNat, rp] using tail_etaQ hp (d := 12) le_rfl)
    ha.smallV (by simpa only [hn, Nat.cast_ofNat, rp] using tail_epsilonV hp)
    (by norm_num) (by norm_num) hExp.2.2.2 le_rfl _
    (by norm_num) (by norm_num) (by norm_num) hs hs
    (fun ξ _ => hfinite ξ) (fun ξ _ => hfinite ξ) hcap hcap v
  · intro x
    simpa only [PaleyB.qform_hplusM_re] using hplus x
  · apply etaB_tail_with_parity hp ha.density (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity) (by positivity)
    exact parity_term_tail halfAdjB hn le_rfl

end Sarkozy.SpectralD.Root
