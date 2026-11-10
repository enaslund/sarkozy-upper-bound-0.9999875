module

public import Sarkozy.BlockAdapter.Middle
public import Sarkozy.BlockSpecPaper.Joint

@[expose] public section

/-!
# The joint main statement with the middle root envelopes from per-prime certificates

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(ii); B1's
`main_target_paper_joint_B1` (`BlockSpecPaper/Joint.lean`).

`paperAnalyticInputs_roots` builds B1's analytic inputs `A : PaperAnalyticInputs cell` from
* the budget `PaperBudget cell` (combinatorial, `def:record:exact-blocks`(c),(d));
* the upper band lemmas `UpperBandLemma k` (`lem:upper-reference-rp`(ii), 310 bands);
* the middle rests `MiddleUniformRest i`, `MiddleIndividualRest i u` (rows, layer caps, and the
  L20 envelope of the individual root);
* the **per-prime** root certificates `MiddleRootCaps (Fin 2) 0 i` (L20, uniform pieces) and
  `MiddleRootCaps (Fin 1) 1 i` (L10, all pieces),

through the block adapter (`Root.lean`, `Middle.lean`). `main_target_paper_joint_B6_roots` is
`main_target_paper_joint_B1` with this `A`. Since `PaperAnalyticInputs cell` is a `Prop`, the
obligations `O` do not depend on how `A` is proved.
-/

namespace Sarkozy.BlockAdapter

open Sarkozy Sarkozy.BlockSpecPaper

variable {cell : ℕ → ℕ}

/-- **B1's analytic inputs from the per-prime root certificates** and the remaining lemma forms. -/
theorem paperAnalyticInputs_roots (hbud : PaperBudget cell) (hU : ∀ k, UpperBandLemma k)
    (hM : ∀ i, allpIndividual i = none → MiddleUniformRest i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualRest i u)
    (h20 : ∀ i, allpIndividual i = none → MiddleRootCaps (Fin 2) 0 i)
    (h10 : ∀ i, MiddleRootCaps (Fin 1) 1 i) : PaperAnalyticInputs cell :=
  paperAnalyticInputs_of_lemmas hbud hU
    (fun i hi => middleUniformLemma_of_cap (middleUniformCapLemma_of_rest (hM i hi) (h20 i hi)
      (h10 i)))
    (fun i u hi => middleIndividualLemma_of_cap (middleIndividualCapLemma_of_rest (hI i u hi)
      (h10 i)))

/-- **The main statement at `ε = a_T/71`, joint form, with the middle root envelopes L20 and L10
reduced to per-prime cut certificates** (`thm:main` at `ε = a_T/71`, `cor:joint-closing`,
`def:construction`(b) in the ALLp configuration, `lem:front12:reference`(ii)). Remaining: the data
`cell`, `PaperBudget cell`, the 310 upper band lemmas, the middle rests, the per-prime root
certificates `h20` (31 uniform pieces) and `h10` (33 pieces), and B1's 11 joint obligations. -/
theorem main_target_paper_joint_B6_roots (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (cell : ℕ → ℕ) (hbud : PaperBudget cell)
    (hU : ∀ k, UpperBandLemma k)
    (hM : ∀ i, allpIndividual i = none → MiddleUniformRest i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualRest i u)
    (h20 : ∀ i, allpIndividual i = none → MiddleRootCaps (Fin 2) 0 i)
    (h10 : ∀ i, MiddleRootCaps (Fin 1) 1 i)
    (O : B1JointFinalObligations cell hWeil hMovingRoot hFourCycle
      (paperAnalyticInputs_roots hbud hU hM hI h20 h10)) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_B1 hWeil hMovingRoot hFourCycle hThetaSmallRR cell _ O

end Sarkozy.BlockAdapter
