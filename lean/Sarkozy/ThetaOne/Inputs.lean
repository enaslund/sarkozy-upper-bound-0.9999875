module

public import Sarkozy.ThetaOne.SharpFirstWhole
public import Sarkozy.MainFinal2.Obligations
public import Sarkozy.ThetaOne.MeansTheta1
public import Sarkozy.DensityChain2.PaperData

@[expose] public section

/-!
# The baseline inputs of `SF`, `fix`, `env` (`ϑ = 1`)

TH (7 November 2026). At the baseline `ϑ = 1` the sharp first-stage terms (`SF`) go through the
paper's folded-energy proof of `lem:sharp-first` (`ThetaOne.sharpFirstTerms_of_wholeFolded`),
not through the coupled fibre moments of `prop:density:production` (upgrade only).

* **`SharpFirstBaseInputs D`**: the inputs of `sharpFirstTerms_of_wholeFolded`. Data: the sharp
  decompositions `dec`, the relative error `ε_L → 0`, the remainder constant `c ≥ 0` and the
  remainders `r_±`. Hypotheses: `hfold` (`prop:record:density-structured` on the folded energies
  of the whole pieces) and `hrem` (the summation of the remainders, density-linear).
  `toSharpFirstInputs` gives the obligation `SF`.
* **`SharpPartsBase D`**: `SF` on the baseline route, with B9's mean-bound forms `fixM`, `envM`
  of `fixC`, `envC`, which are baseline (DC2 §1: `lem:sharp-first` for the bracket of
  `lem:bracket-energy`), their mean bounds `hm` (fields 28–31) reduced at `ϑ = 1`
  (`FixMeansTheta1`, `EnvMeansTheta1`: the per-atom moment inputs of `lem:density:packets` are
  proved, the parity condition and `blockSel ≤ selPre` are proved for the paper's standing data,
  nonempty blocks for the paper's layout).
  `toSharpParts2` gives the generic `MainFinal2.SharpParts2`.

Compared with the upgrade route `MainFinal2.SharpParts2U` this drops `θ`, `hθ`, `hθ'` (`θ = 1`)
and **`fibre`** (`CoupledFibreMoment`, `prop:density:production`, upgrade only), and with it the
per-block stage moments `paperStageMoments_proved` that only the coupled route needs.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ThetaOne

open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeInputsBlock
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.Structured ReflectionCut
open Sarkozy.MainFinal Sarkozy.MainFinal2
open Sarkozy.PartV Sarkozy.JointClosing
open Sarkozy.EnvelopeEnergiesPaper (paper_pairwise)
open Sarkozy.CancellationSteps (PaperJ0)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The baseline inputs of `SF`** (`lem:sharp-first` by `lem:record:folded-energy` and
`prop:record:density-structured`, the paper's proof at `θ ≤ 1`): the hypotheses of
`sharpFirstTerms_of_wholeFolded`.
* `dec`: sharp decompositions of the differences (data; they exist, `nonempty_decFamily`);
* `ε → 0`, `c ≥ 0`, nonnegative remainders `rp`, `rm` (data);
* `hfold`: at every least counterexample, for every nonempty choice `σ`, tag `j` present and
  choice `f` of whole pieces, `𝔈_±(f) ≤ (∏ g)(1 + ε_L) Y + r_±(f)`.
  *Open*: `prop:record:density-structured` for the folded laws (`μ_𝔟`, half-marginal diagonal
  laws of positive records, and the full folded laws of whole differences);
* `hrem`: the weighted remainders sum to at most `c L^{-σ} α`. *Open*: the summation of
  `lem:sharp-first` (`lem:record:density-dc`, `lem:record:density-lp` for the error terms). -/
structure SharpFirstBaseInputs (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) where
  /-- The sharp decompositions of the differences. -/
  dec : ∀ L, DecFamily D L
  /-- The relative error `ε_L → 0`. -/
  ε : ℕ → ℝ
  hε0 : ∀ L, 0 ≤ ε L
  hεt : Tendsto ε atTop (𝓝 0)
  /-- The constant of the density-linear remainders. -/
  c : ℝ
  hc : 0 ≤ c
  /-- The remainders of the two folded energies. -/
  rp : ∀ L, Finset ℤ → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag → (∀ b, WPiece D L b) → ℝ
  rm : ∀ L, Finset ℤ → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag → (∀ b, WPiece D L b) → ℝ
  hr0 : ∀ L A σ j f, 0 ≤ rp L A σ j f ∧ 0 ≤ rm L A σ j f
  /-- `prop:record:density-structured` on the folded energies of the whole pieces. *Open*. -/
  hfold : Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ σ : (∀ b, Option (D.FS.Ib L b)),
    σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j → ∀ f,
    foldedPlus (D.FS.cut j) (wpieceLp (dec L) j) (fun _ => blockLift m₀ blk p L A) f ≤
        (∏ b, wpieceG D L b (f b)) * ((1 + ε L) * D.Y L A) + rp L A σ j f ∧
      foldedMinus (D.FS.cut j) (wpieceLm (dec L) j) (fun _ => blockLift m₀ blk p L A) f ≤
        (∏ b, wpieceG D L b (f b)) * ((1 + ε L) * D.Y L A) + rm L A σ j f)
  /-- The summation of the remainders (density-linear). *Open*. -/
  hrem : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ j, ∑ f, choiceWeight (wpieceCoef σ j) (wpieceD D L) f *
        ((rp L A σ j f + rm L A σ j f) / 2) ≤ remainder c L A)

omit [DecidableEq P] in
/-- **`SharpFirstTerms` on the baseline route.** -/
theorem SharpFirstBaseInputs.sharpFirstTerms
    {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} (I : SharpFirstBaseInputs D) :
    D.SharpFirstTerms :=
  sharpFirstTerms_of_wholeFolded D I.dec I.ε I.hε0 I.hεt I.hc I.rp I.rm I.hr0 I.hfold I.hrem

/-- **The obligation `SF` from the baseline inputs.** -/
def SharpFirstBaseInputs.toSharpFirstInputs
    {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} (I : SharpFirstBaseInputs D) :
    SharpFirstInputs D :=
  ⟨fun _ => I.sharpFirstTerms⟩

/-- **The baseline inputs of `SF`, `fix`, `env`** (`ϑ = 1`): `SF` by the folded-energy route,
and B9's mean-bound forms of `fixC`, `envC` with the mean bounds reduced at `ϑ = 1`. 3 fields. -/
structure SharpPartsBase {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {hW : Target.Weil} (D : JointBlockDataTarget blockOf hW) where
  /-- `SF` on the baseline route (`lem:sharp-first`, `lem:record:folded-energy`). *Open*:
  `SF.hfold`, `SF.hrem`. -/
  SF : SharpFirstBaseInputs D.data
  /-- `fixC` in B9's mean-bound form with the mean bounds reduced at `ϑ = 1`
  (`lem:envelope-energy`, `lem:twointerval`(ii); `FixMeansTheta1`). *Open*: `hdiffL/R`, `hzu`,
  `hr2L/R`. -/
  fixM : FixMeansTheta1 (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise
  /-- `envC` in B9's mean-bound form with the mean bounds reduced at `ϑ = 1`
  (`lem:envelope-energy`, `lem:hyb:moment`; `EnvMeansTheta1`). *Open*: `hdiffL/R`, `hzu`,
  `hr2L/R`. -/
  envM : EnvMeansTheta1 (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise

/-- The baseline route to the generic sharp inputs, given that every block of the layout is
nonempty (`def:construction`(b); `paperAtomMap_paperBlockOf_surjective` for the paper's layout).
The parity condition and `blockSel ≤ selPre` hold for the paper's standing data. -/
noncomputable def SharpPartsBase.toSharpParts2 {B : Type} [Fintype B] [DecidableEq B]
    {blockOf : PaperJ0 → B} {hW : Target.Weil} {D : JointBlockDataTarget blockOf hW}
    (hne : ∀ β, ∃ i, PartVLaws.paperAtomMap blockOf i = β)
    (S : SharpPartsBase D) : SharpParts2 D where
  SF := S.SF.toSharpFirstInputs
  fixM := S.fixM.toFixMeansInputs TargetLedger.targetDecay_nonneg
    (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _) hne
    (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
  envM := S.envM.toEnvMeansInputs TargetLedger.targetDecay_nonneg
    (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _) hne
    (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)

end Sarkozy.ThetaOne
