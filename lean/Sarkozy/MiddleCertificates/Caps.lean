module

public import Sarkozy.MiddleCertificates.GraphFacts
public import Sarkozy.BlockAdapter.Final

/-!
# Constructors for B6's per-prime certificates `h10` and `h21` (`lem:layer12-caps`(a))

`paper/sections/20_middle_reference.tex`, `lem:layer12-caps`(a) for the cuts L10 and L21:
`-g_X p^{-1/2} ⪯ A_p ⪯ (1 + c⁺_X/p)` at every prime `p ≥ X`, `p ≡ 3 (mod 4)`, with the constants
of `cert:layer12-grid` at the piece start `X`. The proof is route A
(`thm:spectral-criterion`(a),(d)) with the finite tests at `X`.

* `MidPrimeInputs c i p`: the two **open** per-prime inputs of cut `c` on piece `i` at `p`:
  the analytic parts of route A, (a) and (d), at the bars of `X = pieceStart i` (`RouteALower`,
  `RouteAUpper`; sufficient conditions `routeALower_mid`, `routeAUpper_mid`: the inputs of
  `spectral_criterion_cut_full` at `p` bounded by the bars, with the graph facts proved);
* **`cutCaps_of_inputs`**: from them, the kernel-checked finite tests of both signs
  (`finiteTest_three`, `finiteTest_three_neg`), `g ≤ allpG` (`g_le_allpG`) and
  `allpG p^{-1/2} < 1`, the two-sided per-prime cap at `(allpG, allpB)`;
* **`rootCutCap_l10`**, **`layerCutCap_l21`**: B6's `RootCutCap (Fin 1)` and `LayerCutCap` for
  `G_{L,2}`;
* **`middleRootCaps_l10`**, **`middleL21Caps_of_inputs`**: B6's fields `h10` (all 33 pieces) and
  `h21` (the 31 uniform pieces);
* **`main_target_paper_joint_C8`**: B6's main statement with `h10`, `h21` replaced by these inputs.

The L20 field `h20` is unchanged: its ALLp constants are those of `prop:l20-collisions`
(`cert:l20-grid`), which are smaller than the route-A constants of L20 in the grid (`6.233` against
`5.500` at `Q₃`), so route A cannot supply them.
-/

@[expose] public section

namespace Sarkozy.MiddleCertificates

open Finset Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.BlockAdapter Sarkozy.PartV
  Sarkozy.BlockSpecPaper Sarkozy.BlockSpecPaper.AllpData Sarkozy.Labellings MidCut
open scoped InnerProductSpace

/-- **The open per-prime inputs of the cut `c` on piece `i` at the prime `p`**
(`lem:layer12-caps`(a) by route A): the analytic parts of `thm:spectral-criterion`(a) and (d) at
the bars `(c̄_⊥, τ, η̄_Q, η̄_B, ε̄_V)` recorded at the piece start `X` (`cert:layer12-grid`), with
`g = allpG i c` and `B = allpB i c`. *Hypothesis*; sufficient conditions `routeALower_mid`,
`routeAUpper_mid` (the inputs of `spectral_criterion_cut_full` at `p`, bounded by the bars). -/
structure MidPrimeInputs (c : MidCut) (i : Fin 33) (p : ℕ) [Fact p.Prime] : Prop where
  lower : RouteALower (p := p) c.data (FiniteModel.Adj c.edge c.data.cut) (cbar c i) (tau c i)
    (etaQ c i) (etaB c i) (epsV c i)
  upper : RouteAUpper (p := p) c.data (FiniteModel.Adj c.edge c.data.cut) (cbar c i) (tau c i)
    (etaQ c i) (etaB c i) (epsV c i) (allpG i c.allpIdx) (allpB i c.allpIdx)

/-- **The two-sided per-prime cap of L10 or L21 at the ALLp constants**, from the open inputs and
the kernel-checked class-three tests of the piece start (both signs). -/
theorem cutCaps_of_inputs (c : MidCut) (i : Fin 33) {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3)
    (hX : pieceStart i ≤ p) (h : MidPrimeInputs c i p)
    (hne : (Labellings.injLabellings (ZMod p) c.data.G).Nonempty)
    (v : EuclideanSpace ℝ (c.data.cut.Half → ZMod p)) :
    -((allpG i c.allpIdx : ℝ) * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp c.data hne v⟫_ℝ ∧
      ⟪v, Spectral.cutOp c.data hne v⟫_ℝ ≤ (1 + (allpB i c.allpIdx : ℝ) / p) * ‖v‖ ^ 2 :=
  ⟨h.lower hne _ (fun ξ => finiteTest_three c i hp3 ξ) (g_le_allpG c i).1 v,
    h.upper hne (fun ξ => finiteTest_three c i hp3 ξ) (fun ξ => finiteTest_three_neg c i hp3 ξ)
      (g_le_allpG c i).1 (allpG_mul_lt_one i c.allpIdx hX) v⟩

/-- **B6's `RootCutCap` for L10 at `(allpG i 1, allpB i 1)`** (`lem:layer12-caps`(a)). -/
theorem rootCutCap_l10 (i : Fin 33) {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3)
    (hX : pieceStart i ≤ p) (h : MidPrimeInputs .l10 i p) :
    RootCutCap (Fin 1) (allpG i 1) (allpB i 1) p :=
  fun hne v => cutCaps_of_inputs .l10 i hp3 hX h hne v

/-- **B6's `LayerCutCap` for L21 at `(allpG i 2, allpB i 2)`** (`lem:layer12-caps`(a)). -/
theorem layerCutCap_l21 (i : Fin 33) {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3)
    (hX : pieceStart i ≤ p) (h : MidPrimeInputs .l21 i p) :
    LayerCutCap (ZMod 6) (recordGraph (Fin 2)) recordGraph_swap (allpG i 2) (allpB i 2) p :=
  fun hne v => cutCaps_of_inputs .l21 i hp3 hX h hne v

/-- The open inputs of cut `c` at every class-three prime of piece `i`. *Hypothesis.* -/
def MidInputs (c : MidCut) (i : Fin 33) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i →
    MidPrimeInputs c i p

/-- **B6's field `h10` on piece `i`** (`MiddleRootCaps (Fin 1) 1 i`), from the open inputs. -/
theorem middleRootCaps_l10 {i : Fin 33} (h : MidInputs .l10 i) : MiddleRootCaps (Fin 1) 1 i :=
  fun p _ hp3 hX hY => rootCutCap_l10 i hp3 hX (h p hp3 hX hY)

/-- **B6's field `h21` on piece `i`** (`MiddleL21Caps i`), from the open inputs. -/
theorem middleL21Caps_of_inputs {i : Fin 33} (h : MidInputs .l21 i) : MiddleL21Caps i :=
  fun p _ hp3 hX hY => layerCutCap_l21 i hp3 hX (h p hp3 hX hY)

/-- **B6's main statement with the per-prime certificates of L10 and L21 reduced to route A**:
`main_target_paper_joint_B6` with `h10` and `h21` built from the open inputs `MidInputs` (the
analytic part of route A at the recorded bars, and the upper bound at the recorded `B`); the
finite tests of `cert:layer12-grid` are proved. `h20` is B6's. -/
theorem main_target_paper_joint_C8 (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR) (cell : ℕ → ℕ)
    (hbud : PaperBudget cell) (hUR : ∀ k, UpperBandRowsNonEE k) (hUC : ∀ k, UpperRootCaps k)
    (hMB : ∀ i, allpIndividual i = none → MiddleUniformBlockInputs i)
    (hIB : ∀ i u, allpIndividual i = some u → MiddleIndividualBlockInputs i u)
    (h20 : ∀ i, allpIndividual i = none → MiddleRootCaps (Fin 2) 0 i)
    (h10 : ∀ i, MidInputs .l10 i)
    (h21 : ∀ i, allpIndividual i = none → MidInputs .l21 i)
    (O : B1JointFinalObligations cell hWeil hMovingRoot hFourCycle
      (paperAnalyticInputs_B6 hbud
        (fun k => upperBandLemma_of_rest
          (upperBandRest_of_rows (upperBandRows_of_nonEE (hUR k)) (hUC k)) (hUC k))
        hMB hIB h20 (fun i => middleRootCaps_l10 (h10 i))
        (fun i hi => middleL21Caps_of_inputs (h21 i hi)) middleE21Caps_proved)) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_B6 hWeil hMovingRoot hFourCycle hThetaSmallRR cell hbud hUR
    hUC hMB hIB h20 (fun i => middleRootCaps_l10 (h10 i))
    (fun i hi => middleL21Caps_of_inputs (h21 i hi)) O

end Sarkozy.MiddleCertificates
