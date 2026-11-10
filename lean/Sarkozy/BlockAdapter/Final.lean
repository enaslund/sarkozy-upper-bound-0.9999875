module

public import Sarkozy.BlockAdapter.UpperSwap
public import Sarkozy.BlockAdapter.UpperEE

@[expose] public section

/-!
# B6's main statement (`thm:main` at `ε = a_T/71`, joint form)

B1's `main_target_paper_joint_B1` with its analytic inputs `A` built through the block adapter:

* middle (`Root`, `Layer`, `Middle`, `MiddleLayer`): the root envelopes L20, L10 and the layer caps
  L21, E21 from per-prime certificates at the recorded ALLp constants; the E21 certificates are
  proved (`E21.lean`);
* upper (`Upper`, `UpperMain`, `UpperSwap`, `UpperEE`): the root envelopes of both coordinates
  from per-prime certificates of the chamber cuts (coordinate exchange for coordinate `1`); the
  layer caps of the nine `E × E` type pairs are proved (`UpperEE.lean`).

`UpperBandRowsNonEE k`: the fields `rows20`, `rows10` of `ValidInputs` and the layer caps of the
16 type pairs other than `E × E`. *Hypothesis* (spectral; `lem:upper-reference-rp`(ii), (V2),
(V3)).
-/

open Finset

namespace Sarkozy.BlockAdapter

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws Sarkozy.BlockSpecPaper

/-- The upper layer caps (V3) of the type pairs other than `E × E`. -/
def UpperLayerCapsNonEE {X : Type} [Fintype X] [DecidableEq X] (F : UpperFieldLaws X)
    (k : PType → PType → ℝ) (r : ℝ) : Prop :=
  ∀ (t : PType × PType) (φ : t.1.Pat × t.2.Pat), ¬ IsEE t →
    reservedCut.Below (-(k t.1 t.2 * r) • signedIntegral (upComponent F (false, ⟨t, φ⟩)).weight)
      (signedIntegral (upComponent F (true, ⟨t, φ⟩)).weight)

/-- **`lem:upper-reference-rp`(ii) on band `k`, what remains at the block level**: the
coordinate-`0` rows (V2) and the layer caps (V3) of the 16 type pairs other than `E × E`.
*Hypothesis* (spectral). 3 fields. -/
def UpperBandRowsNonEE (k : Fin 310) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, (bandOf k).1 ≤ pr j ∧ pr j < (bandOf k).2) →
    (∑ j, Real.log (pr j) ≤ (UpperRecords.CompletionData.record k).budget) →
    (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ (hne : UpperNonempty pr) (hW' : ∀ i, WeilBound (ZMod (pr i)))
      (hp' : ∀ i, (2 : ℝ) ^ 20 ≤ pr i),
      (∀ f', ValidRows (rowD0 (lam2 (upperBlockFieldLaws pr hne)) f'
        ((block_upperDatumHyp pr hW' hp' hne).two0 f')) ((b : ℝ) ^ (-(1 / 2 : ℝ)))
          (UpperRecords.bandOrd k f').f (UpperRecords.bandOrd k f').h
          (UpperRecords.bandOrd k f').M) ∧
      (∀ f', ValidRows (rowD0 (lam1 (upperBlockFieldLaws pr hne)) f'
        ((block_upperDatumHyp pr hW' hp' hne).one0 f')) ((b : ℝ) ^ (-(1 / 2 : ℝ)))
          (UpperRecords.bandRes k f').f (UpperRecords.bandRes k f').h
          (UpperRecords.bandRes k f').M) ∧
      UpperLayerCapsNonEE (upperBlockFieldLaws pr hne) (UpperRecords.bandCap k)
        ((b : ℝ) ^ (-(1 / 2 : ℝ)))

/-- `UpperBandRows k` from the non-`E × E` part and the proved `E × E` caps. -/
theorem upperBandRows_of_nonEE {k : Fin 310} (hR : UpperBandRowsNonEE k) : UpperBandRows k := by
  intro ι _ _ pr _ b hinj h3 hband hbud hb hb' hne hW' hp'
  obtain ⟨w20, w10, caps⟩ := hR ι pr b hinj h3 hband hbud hb hb' hne hW' hp'
  refine ⟨w20, w10, fun t φ => ?_⟩
  by_cases ht : IsEE t
  · exact upperLayerCaps_EE k pr b hband hb hb' hne t φ ht
  · exact caps t φ ht

/-- **The main statement at `ε = a_T/71`, joint form, through the block adapter**
(`thm:main` at `ε = a_T/71`, `cor:joint-closing`, `def:construction`(b) in the ALLp
configuration, `lem:front12:reference`(i),(ii), `lem:upper-reference-rp`(ii)).

Remaining, besides the literature hypotheses:
* the data `cell` and `PaperBudget cell` (combinatorial);
* upper bands (310): `hUR` (`UpperBandRowsNonEE`: the rows `rows20`, `rows10` and the layer caps of
  the 16 type pairs other than `E × E`) and `hUC` (`UpperRootCaps`: per-prime certificates of the
  chamber cuts with per-band constants, `cert:upper-root-caps`);
* middle pieces: `hMB`, `hIB` (block level: the rows; F21 at `k_D`; on `2³⁶`, `2⁴⁰` the L20
  envelope and L21 cap of the individual root) and the per-prime certificates `h20` (L20, 31
  uniform pieces), `h10` (L10, 33 pieces), `h21` (L21, 31 uniform pieces);
* B1's 11 joint obligations `O`.

Proved through the adapter: every middle root envelope and layer cap of block-cap form from its
per-prime certificate, the E21 certificates (33 pieces), the upper root envelopes of both
coordinates from their per-prime certificates, and the upper `E × E` layer caps (310 bands). -/
theorem main_target_paper_joint_B6 (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR) (cell : ℕ → ℕ)
    (hbud : PaperBudget cell) (hUR : ∀ k, UpperBandRowsNonEE k) (hUC : ∀ k, UpperRootCaps k)
    (hMB : ∀ i, allpIndividual i = none → MiddleUniformBlockInputs i)
    (hIB : ∀ i u, allpIndividual i = some u → MiddleIndividualBlockInputs i u)
    (h20 : ∀ i, allpIndividual i = none → MiddleRootCaps (Fin 2) 0 i)
    (h10 : ∀ i, MiddleRootCaps (Fin 1) 1 i)
    (h21 : ∀ i, allpIndividual i = none → MiddleL21Caps i)
    (O : B1JointFinalObligations cell hWeil hMovingRoot hFourCycle
      (paperAnalyticInputs_B6 hbud
        (fun k => upperBandLemma_of_rest
          (upperBandRest_of_rows (upperBandRows_of_nonEE (hUR k)) (hUC k)) (hUC k))
        hMB hIB h20 h10 h21 middleE21Caps_proved)) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_B1 hWeil hMovingRoot hFourCycle hThetaSmallRR cell _ O

end Sarkozy.BlockAdapter
