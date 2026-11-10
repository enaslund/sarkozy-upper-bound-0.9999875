module

public import Sarkozy.SharpSums.InputsY
public import Sarkozy.SharpSums.YBound

@[expose] public section

/-!
# `YBound` proved, and the final constructor of `SharpBaseInputsPT`

SUM (7 November 2026).

* **`yBound_of_data`**: `∃ C_Y ≥ 0, YBound D C_Y` for every comparison datum on the paper's tails
  (`dataY_le_lp` at `ε = 40/825`, so that `Q^ε = (KL)^{2/825}`; the scale conditions eventually,
  `exists_scaleThreshold` at `M₀ = Q_cl = Q_pre = 1`; the primes `D.S.p_prime`, `D.S.p_inj`);
* **`SharpSumInputsP D`**: the remaining inputs: `SF`, the four main-price means `PriceMeans*`
  (constant `C_P`) and the four large-piece sums `LargeSumPT*` (constant `c_L`);
* **`SharpSumInputsP.toSharpBaseInputsPT`**: SH2's `SharpBaseInputsPT D`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.SharpSums

open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.SharpBase2 Sarkozy.SharpBase
open Sarkozy.Param (Params)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- `Q(KL)^{40σ} = K^{2σ} L^{2σ}` (`Q = N^{1/20}`). -/
theorem paperCutoff_rpow_eq (L : ℕ) (σ : ℝ) :
    paperCutoff (blockScale * L) ^ (40 * σ) =
      (blockScale : ℝ) ^ (2 * σ) * (L : ℝ) ^ (2 * σ) := by
  unfold paperCutoff liftExponent
  rw [← Real.rpow_mul (Nat.cast_nonneg _), Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  have e : (1 : ℝ) / 20 * (40 * σ) = 2 * σ := by ring
  rw [e]

omit [DecidableEq P] in
/-- **`Y ≲ L^{2σ} α` at counterexamples, proved** (the input `hY` of `crossSumPT*_of_bounds`;
`lem:record:density-lp`, first step, at the reference law, and `lem:record:lift-moments`(c)): in
fact `Y(L, A) ≤ C_Y L^{2/825} α` for every large `L` and every `A`. -/
theorem yBound_of_data (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j)) :
    ∃ CY : ℝ, 0 ≤ CY ∧ YBound D CY := by
  obtain ⟨C, hC, hc⟩ := dataY_le_lp (a := a) (m₀ := m₀) (blk := blk) (p := paperTail) (pr := pr)
    (h := h) (E := E) (40 * Sarkozy.cancellationDecay)
    (by norm_num [Sarkozy.cancellationDecay])
  obtain ⟨Lstar, -, hLs⟩ := exists_scaleThreshold blockScale 1 1 1 0 0
    (by norm_num [blockScale]) le_rfl le_rfl
  refine ⟨(Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * C *
    (blockScale : ℝ) ^ (2 * Sarkozy.cancellationDecay) * blockScale, by positivity, ?_⟩
  unfold YBound
  filter_upwards [eventually_ge_atTop (max Lstar 1)] with L hL
  intro C' _ _ A _ _
  have hY := hc D hpair (A := A) (hLs L (le_of_max_le_left hL)) (le_of_max_le_right hL) le_rfl
    (D.S.p_prime L) (D.S.p_inj L)
  rw [paperCutoff_rpow_eq, Nat.cast_one, one_pow, one_mul] at hY
  refine hY.trans (le_of_eq ?_)
  ring

end Sarkozy.SharpSums

namespace Sarkozy.SharpSums

open Sarkozy.PartV Sarkozy.JointClosing Sarkozy.BlockSpecPaper Sarkozy.MainCombined
  Sarkozy.MainCombined2 Sarkozy.SharpBase Sarkozy.SharpBase2
open Sarkozy.EnvelopeEnergiesPaper (paper_pairwise)
open Sarkozy.CancellationSteps (PaperJ0)

/-- **The remaining inputs of SH2's four summations after SUM** (`lem:sharp-first`, the error
terms): `SF`; the means of the main prices of the folds (`PriceMeans*`, B9's local-density means,
constant `C_P`); the four large-piece sums (`LargeSumPT*`, `lem:record:density-lp`, constant
`c_L`). The chain² parts are proved (`chainSum_*_le`); the cross terms are reduced to the price
means (`crossSumPT*_of_bounds`) with `Y ≲ L^{2σ} α` proved (`yBound_of_data`). 11 fields. -/
structure SharpSumInputsP {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {hW : Target.Weil} (D : JointBlockDataTarget blockOf hW) where
  /-- `SF` on the baseline route (TH's `SharpFirstBaseInputs`). *Open*: `SF.hfold`, `SF.hrem`. -/
  SF : ThetaOne.SharpFirstBaseInputs D.data
  /-- The constant of the main-price means. -/
  CP : ℝ
  /-- The main-price means of `fixC` (L). *Open*. -/
  hPFixL : PriceMeansFixL (BlockAnchor.index_coprime_block D.data) D.data CP
  /-- The main-price means of `fixC` (R). *Open*. -/
  hPFixR : PriceMeansFixR (BlockAnchor.index_coprime_block D.data) D.data CP
  /-- The main-price means of `envC` (L). *Open*. -/
  hPEnvL : PriceMeansEnvL (BlockAnchor.index_coprime_block D.data) D.data CP
  /-- The main-price means of `envC` (R). *Open*. -/
  hPEnvR : PriceMeansEnvR (BlockAnchor.index_coprime_block D.data) D.data CP
  /-- The constant of the large-piece sums. -/
  cL : ℝ
  hcL : 0 ≤ cL
  /-- The large pieces of `Sh.fixM.hr2L`. *Open*. -/
  largeFixL : LargeSumPTFixL (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cL
  /-- The large pieces of `Sh.fixM.hr2R`. *Open*. -/
  largeFixR : LargeSumPTFixR (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cL
  /-- The large pieces of `Sh.envM.hr2L`. *Open*. -/
  largeEnvL : LargeSumPTEnvL (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cL
  /-- The large pieces of `Sh.envM.hr2R`. *Open*. -/
  largeEnvR : LargeSumPTEnvR (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cL

/-- `SharpSumInputsY` from `SharpSumInputsP`: `C_Y` and `hY` from `yBound_of_data`. -/
noncomputable def SharpSumInputsP.toSharpSumInputsY {B : Type} [Fintype B] [DecidableEq B]
    {blockOf : PaperJ0 → B} {hW : Target.Weil} {D : JointBlockDataTarget blockOf hW}
    (I : SharpSumInputsP D) : SharpSumInputsY D where
  SF := I.SF
  CY := (yBound_of_data D.data paper_pairwise).choose
  hCY := (yBound_of_data D.data paper_pairwise).choose_spec.1
  hY := (yBound_of_data D.data paper_pairwise).choose_spec.2
  CP := I.CP
  hPFixL := I.hPFixL
  hPFixR := I.hPFixR
  hPEnvL := I.hPEnvL
  hPEnvR := I.hPEnvR
  cL := I.cL
  hcL := I.hcL
  largeFixL := I.largeFixL
  largeFixR := I.largeFixR
  largeEnvL := I.largeEnvL
  largeEnvR := I.largeEnvR

/-- **The constructor of SH2's `SharpBaseInputsPT`** (`lem:sharp-first`, the error-term
summation) from the remaining inputs `SharpSumInputsP`: chain² parts and `Y ≲ L^{2σ} α` proved,
cross terms reduced to the main-price means, large pieces open. -/
noncomputable def SharpSumInputsP.toSharpBaseInputsPT {B : Type} [Fintype B] [DecidableEq B]
    {blockOf : PaperJ0 → B} {hW : Target.Weil} {D : JointBlockDataTarget blockOf hW}
    (I : SharpSumInputsP D) : SharpBaseInputsPT D :=
  I.toSharpSumInputsY.toSharpBaseInputsPT

end Sarkozy.SharpSums
