module

public import Sarkozy.BlockAdapter.E21
public import Sarkozy.BlockAdapter.MainRoots

@[expose] public section

/-!
# The joint main statement with the middle caps reduced to per-prime certificates

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(i),(ii); B1's
`main_target_paper_joint_B1` (`BlockSpecPaper/Joint.lean`).

Through the block adapter (`Root.lean`, `Layer.lean`) every middle root envelope of the uniform
root (L20, L10) and every middle layer cap of block-cap form (L21 for the uniform root, E21 for
the matching, merge and constant types on all pieces) is derived from **per-prime** certificates
at the recorded ALLp constants `(g, B)`. What remains at the block level on the middle pieces:

* `MiddleUniformBlockInputs i` (31 uniform pieces): the rows at `j = 2, 1`
  (`lem:front12:reference`(i)) and the fold-type layer caps at the recorded `k_D` (F21,
  `lem:old-f-law`(e); not of block-cap form);
* `MiddleIndividualBlockInputs i u` (pieces `2³⁶`, `2⁴⁰`): the rows, the L20 envelope and the L21
  layer cap of the individual-square root (`def:positive-root`, `cert:positive-root-caps`; a
  reweighted law, not a graph law), and the F21 caps.

`paperAnalyticInputs_B6` builds `A` from these, the four per-prime certificate families
`MiddleRootCaps (Fin 2) 0` (L20), `MiddleRootCaps (Fin 1) 1` (L10), `MiddleL21Caps`,
`MiddleE21Caps`, B1's `UpperBandLemma` on the 310 bands, and `PaperBudget cell`. The E21 family is
**proved** (`middleE21Caps_proved`, `E21.lean`), so `main_target_paper_joint_B6_middle` takes
only the three families L20, L10, L21. (`UpperMain.lean`, `UpperSwap.lean` add the upper
reductions: `main_target_paper_joint_B6`.)
-/

open Finset

namespace Sarkozy.BlockAdapter

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.BlockSpecPaper
  Sarkozy.BlockSpecPaper.AllpData

/-- **The block-level middle inputs of a uniform-root piece** that are not of per-prime cap form:
the rows at `j = 2, 1` (`lem:front12:reference`(i)) and the F21 caps at the recorded `k_D`, for
every block of the piece. *Hypothesis* (spectral). 3 conjuncts. -/
def MiddleUniformBlockInputs (i : Fin 33) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i) →
    (∑ j, Real.log (pr j) ≤ middleBudget) → (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ hne : MiddleNonempty pr,
      RowBounds (fieldDatum (middleBlock_datumHyp₂ pr hne)) (allpInputs i).f₂ (allpInputs i).h₂
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) (allpInputs i).f₁ (allpInputs i).h₁
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      FoldLayerCaps pr hne ((allpInputs i).k .D) ((b : ℝ) ^ (-(1 / 2 : ℝ)))

/-- **The block-level middle inputs of an individual-square-root piece**: the rows, the L20
envelope and the L21 layer cap of the individual root, and the F21 caps. *Hypothesis*
(spectral). 5 conjuncts. -/
def MiddleIndividualBlockInputs (i : Fin 33) (u : ℚ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i) →
    (∑ j, Real.log (pr j) ≤ middleBudget) → (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ hne : MiddleNonempty pr,
      RowBounds (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)) (allpInputs i).f₂
        (allpInputs i).h₂ ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) (allpInputs i).f₁ (allpInputs i).h₁
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RootEnvelope (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)) (capVal i 0)
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      IndividualRootLayerCap pr u hne (capK i .L) ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      FoldLayerCaps pr hne ((allpInputs i).k .D) ((b : ℝ) ^ (-(1 / 2 : ℝ)))

theorem middleUniformRest_of_block {i : Fin 33} (hB : MiddleUniformBlockInputs i)
    (hL21 : MiddleL21Caps i) (hE21 : MiddleE21Caps i) : MiddleUniformRest i := by
  intro ι _ _ pr _ b hinj h3 hpc hbud hb hb' hne
  obtain ⟨r2, r1, hD⟩ := hB ι pr b hinj h3 hpc hbud hb hb' hne
  exact ⟨r2, r1,
    middleLayerCaps_uniform_of_cutCaps pr b hL21 hE21 h3 hpc hbud hb hb' hne hD⟩

theorem middleIndividualRest_of_block {i : Fin 33} {u : ℚ} (hB : MiddleIndividualBlockInputs i u)
    (hE21 : MiddleE21Caps i) : MiddleIndividualRest i u := by
  intro ι _ _ pr _ b hinj h3 hpc hbud hb hb' hne
  obtain ⟨r2, r1, e2, hLt, hD⟩ := hB ι pr b hinj h3 hpc hbud hb hb' hne
  exact ⟨r2, r1, e2,
    middleLayerCaps_individual_of_cutCaps pr b hE21 h3 hpc hbud hb hb' hne hLt hD⟩

variable {cell : ℕ → ℕ}

/-- **B1's analytic inputs `A` from the per-prime middle certificates** and the remaining
block-level inputs. -/
theorem paperAnalyticInputs_B6 (hbud : PaperBudget cell) (hU : ∀ k, UpperBandLemma k)
    (hMB : ∀ i, allpIndividual i = none → MiddleUniformBlockInputs i)
    (hIB : ∀ i u, allpIndividual i = some u → MiddleIndividualBlockInputs i u)
    (h20 : ∀ i, allpIndividual i = none → MiddleRootCaps (Fin 2) 0 i)
    (h10 : ∀ i, MiddleRootCaps (Fin 1) 1 i)
    (h21 : ∀ i, allpIndividual i = none → MiddleL21Caps i)
    (hE21 : ∀ i, MiddleE21Caps i) : PaperAnalyticInputs cell :=
  paperAnalyticInputs_roots hbud hU
    (fun i hi => middleUniformRest_of_block (hMB i hi) (h21 i hi) (hE21 i))
    (fun i u hi => middleIndividualRest_of_block (hIB i u hi) (hE21 i)) h20 h10

/-- **The main statement at `ε = a_T/71`, joint form, with the middle root envelopes and the
middle layer caps of block-cap form reduced to per-prime cut certificates** (`thm:main` at
`ε = 3/250000`, `cor:joint-closing`, `def:construction`(b) in the ALLp configuration,
`lem:front12:reference`(i),(ii), `lem:upper-reference-rp`(ii)).

Remaining, besides the literature hypotheses:
* the data `cell` and `PaperBudget cell` (combinatorial);
* `hU`: `lem:upper-reference-rp`(ii) on the 310 upper bands (B1's `UpperBandLemma`);
* `hMB`, `hIB`: the block-level middle inputs (rows; F21 at `k_D`; on `2³⁶`, `2⁴⁰` also the L20
  envelope and L21 cap of the individual root);
* the per-prime certificates `h20` (L20, 31 uniform pieces), `h10` (L10, 33 pieces) and `h21`
  (L21, 31 uniform pieces), at the recorded `(g, B)` of `AllpConsts` (the E21 certificates are
  proved, `middleE21Caps_proved`);
* B1's 11 joint obligations `O`. -/
theorem main_target_paper_joint_B6_middle (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (cell : ℕ → ℕ) (hbud : PaperBudget cell)
    (hU : ∀ k, UpperBandLemma k)
    (hMB : ∀ i, allpIndividual i = none → MiddleUniformBlockInputs i)
    (hIB : ∀ i u, allpIndividual i = some u → MiddleIndividualBlockInputs i u)
    (h20 : ∀ i, allpIndividual i = none → MiddleRootCaps (Fin 2) 0 i)
    (h10 : ∀ i, MiddleRootCaps (Fin 1) 1 i)
    (h21 : ∀ i, allpIndividual i = none → MiddleL21Caps i)
    (O : B1JointFinalObligations cell hWeil hMovingRoot hFourCycle
      (paperAnalyticInputs_B6 hbud hU hMB hIB h20 h10 h21 middleE21Caps_proved)) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_B1 hWeil hMovingRoot hFourCycle hThetaSmallRR cell _ O

end Sarkozy.BlockAdapter
