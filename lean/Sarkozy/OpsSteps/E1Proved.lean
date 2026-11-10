module

public import Sarkozy.OpsSteps.E1Diag
public import Sarkozy.E1Closure.Main

@[expose] public section

/-!
# The envelope bound (E1) of all selections, proved at the paper's data (OPS-S)

`paper/sections/10_comparison_lemmas.tex`, `lem:bracket-energy`, (E1), "Fixed selections and
summed remainders" (ll. 126–140); `paper/sections/09_comparison_theorem.tex`, `def:cp4`(b).

EC (`Sarkozy.E1Closure`) proved the three fields of F1P's `E1InputsAgg` at the paper's tails:
`E1Sub`, `E1Coup` at the canonical remainders, and `E1Rem` by the split by the full union
(`e1SubSmall_proved`, `e1CoupSmall_proved`, `e1Large_proved`). F1P's `E1InputsAgg.toE1` turns them
into `ComparisonData.EnvelopeBoundNonneg`: for **every** selection `ω`, in a class or not,

`Y[(⊗_{𝔟 ∈ X} D^{ε_𝔟}_{𝔟,t_𝔟}) ⊗ Ñ_{-X}] ≤ (B + ε_E) C_X Y + r_E(ω)`,
`∑_ω π̃_ω r_E(ω) ≤ c_E L^{-σ} α`.

* **`envelopeBoundNonneg_proved`**: this, for any comparison data on the paper's tails with
  `a ≥ 0`, the pairwise coprimality of the joined moduli, the parity condition,
  `blockSel ≤ selPre` and nonempty blocks (EC's hypotheses);
* **`envelopeBoundNonneg_front`**: at the data `(F.X hB hRR).data` of the companion obligations
  (from the front `F` alone, with the paper-data facts that EC's `CompanionObligationsEC.subS`,
  `coupS`, `large` use). So, at the obligations' data, the inputs `hE1` of B11's `paperDegreeOps`
  and `hDN` of B10's `VarStepsAt.ofRecords` follow from `E1Diag.lean`'s `hE1_of_envelope`,
  `hDN_of_envelope`, given the identification `D^ε_{𝔟,t} = Diag_ι(m_{t,𝔟})` of the objects;
* **`sum_r0X_le`**: the summed subset-term remainders `∑_ω π̃_ω ∑_f r0X ≤ c L^{-σ} α`, the
  remainders of `Uniform.step4_uniform`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.OpsSteps

open Sarkozy.E1Closure Sarkozy.SharpFirst Sarkozy.TheoremCBlock Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.EnvelopeInputs Sarkozy.DensityChain2 Sarkozy.CancellationSteps Sarkozy.BlockFrame
  Sarkozy.Functional Sarkozy.BlockAnchor
open Sarkozy.MainFinalF1b (E1InputsAgg)
open Sarkozy.CompanionND (CompanionFrontND)
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.AnalyticCells (f1Cell)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **(E1) for the envelope laws of all selections, proved** (EC's `E1Sub`, `E1Coup`, `E1Rem`
through F1P's `E1InputsAgg.toE1`), at `ε_E = u_L` (`sfEps`) and the canonical remainders. -/
theorem envelopeBoundNonneg_proved (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β) (hne : ∀ β, ∃ i, blk i = β) :
    D.EnvelopeBoundNonneg := by
  obtain ⟨c₁, hc₁, h1⟩ := e1SubSmall_proved D hpair ha hpar hsel hne
  obtain ⟨c₂, hc₂, h2⟩ := e1CoupSmall_proved D hpair ha hpar hsel hne
  obtain ⟨c₃, hc₃, h3⟩ := e1Large_proved D ha
  exact (Companion.E1InputsAgg.ofFields D (sfEps D) (sfEps_nonneg D) (tendsto_sfEps D)
    (c₁ + c₂ + c₃) (add_nonneg (add_nonneg hc₁ hc₂) hc₃) (r0X D (sfEps D)) (rX D (sfEps D))
    (e1Sub_r0X D (sfEps D)) (e1Coup_rX D (sfEps D)) (e1RemX_of_split D (sfEps_nonneg D) h1 h2 h3)
    (rX_nonneg D (sfEps D)) (r0X_nonneg D (sfEps D))).toE1

/-- **(E1) for the envelope laws of all selections at the data of the companion obligations**
(the front `F` of `CompanionObligationsEC`; the same paper-data facts as EC's `subS`, `coupS`,
`large`). -/
theorem envelopeBoundNonneg_front {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {UpT : UpperRecordTables}
    (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) :
    (F.X hB hRR).data.EnvelopeBoundNonneg :=
  envelopeBoundNonneg_proved _ paper_pairwise TargetLedger.targetDecay_nonneg
    (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (ThetaOne.paperAtomMap_paperBlockOf_surjective f1Cell)

omit [DecidableEq P] in
/-- **The summed subset-term remainders** (the part of EC's `E1Rem` used by
`Uniform.step4_uniform`): `∑_ω π̃_ω ∑_f r0X_{ω,f} ≤ c L^{-σ} α` at every least counterexample, at
`ε_E = u_L`. -/
theorem sum_r0X_le (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β) (hne : ∀ β, ∃ i, blk i = β) :
    ∃ c : ℝ, 0 ≤ c ∧ Param.AtCounterexamples (Param.Params.ofDecay a) D.Y (fun L A =>
      ∑ ω ∈ Finset.univ.filter (fun ω : RecordExpansion.Choice (D.CL.T L) =>
          RecordExpansion.Choice.IsSelection ω),
        RecordExpansion.monomial (D.CL.πt L) ω *
          ∑ f : BlockAtom Bk PaperJt L → Bool, r0X D (sfEps D) L A ω f ≤
        Comparison.remainder c L A) := by
  obtain ⟨c₁, hc₁, h1⟩ := e1SubSmall_proved D hpair ha hpar hsel hne
  obtain ⟨c₂, hc₂, h2⟩ := e1CoupSmall_proved D hpair ha hpar hsel hne
  obtain ⟨c₃, hc₃, h3⟩ := e1Large_proved D ha
  refine ⟨c₁ + c₂ + c₃, add_nonneg (add_nonneg hc₁ hc₂) hc₃, ?_⟩
  have hrem := e1RemX_of_split D (sfEps_nonneg D) h1 h2 h3
  unfold E1RemX Companion.E1Rem at hrem
  filter_upwards [hrem] with L hL
  intro C hC hk A hA hY
  refine le_trans (Finset.sum_le_sum fun ω _ => ?_) (hL C hC hk A hA hY)
  refine mul_le_mul_of_nonneg_left ?_
    (RecordExpansion.monomial_nonneg (D.CL.πt_nonneg L) ω)
  refine le_add_of_nonneg_right (Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun f _ => mul_nonneg (Finset.prod_nonneg fun b _ => abs_nonneg _) ?_)
  exact rX_nonneg D (sfEps D) L A ω σ j f

end Sarkozy.OpsSteps
