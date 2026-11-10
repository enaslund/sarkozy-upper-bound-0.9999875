module

public import Sarkozy.LargeSums.Fix

@[expose] public section

/-!
# SUM's `LargeSumPTEnvL` and `LargeSumPTEnvR`, proved

LP (8 November 2026). **`largeSumPTEnvL_proved`**, **`largeSumPTEnvR_proved`**: as
`largeSumPTFixL_proved` (`LargeSums.Fix`), at the large folded pieces of `envC`, with the
envelope increments `envIncL/R` (masses at most `T_L`, `T_R`) and the revealed inputs of `envC`
(`envInputs_moment_le`).

**The depth vectors with an unrevealed interval** (`𝒥_e(none) = 0` for some `e`, SUM's item
(iii)): there every piece is "not small" by the definition of `largePTEnv*`, and the revealed input
is not the paper's input, so neither the moment bound nor Rankin applies. These depth vectors have
zero query weight (`queryLaw_weight_eq_zero`: the interval coordinate has the tail
`Tails.bernoulli 1`), so they do not enter the expectation (`expect_le_of_weight_ne_zero`). At a
depth vector of positive weight every interval is revealed, so "not small" is `¬ smallPiece` and
the argument of `fixC` applies verbatim.
-/

namespace Sarkozy.LargeSums

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.DensityFibre
open Sarkozy.Param (Params)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **`LargeSumPTEnvL`, proved** (`lem:record:density-lp` at the large folded pieces of `envC`;
the depth vectors with an unrevealed interval have zero query weight). -/
theorem largeSumPTEnvL_proved (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) :
    ∃ c : ℝ, 0 ≤ c ∧ Sarkozy.SharpSums.LargeSumPTEnvL hcop D hpair dec c := by
  obtain ⟨C, hC, hc⟩ := envInputs_moment_le (m₀ := m₀) (blk := blk) (p := paperTail) (E := E)
    hcop ((1 : ℝ) / 2000) (by norm_num)
  have hM0 : 1 ≤ modulus pr h := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  obtain ⟨Lstar, -, hLs⟩ := exists_scaleThreshold blockScale (modulus pr h) 1 1 0 0
    (by norm_num [blockScale]) hM0 le_rfl
  refine ⟨largeConst D C, largeConst_nonneg D hC.le, ?_⟩
  unfold Sarkozy.SharpSums.LargeSumPTEnvL
  filter_upwards [eventually_ge_atTop (max Lstar 1)] with L hL
  intro C' _ _ A _ _
  have hL1 : 1 ≤ L := le_of_max_le_right hL
  have hsc := hLs L (le_of_max_le_left hL)
  have hPi := prod_atomPr_le_exp D L ha (TheoremCBlock.Structured.envIncL D L)
    (fun b => TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (isPositiveRecord_envIncL D L b).1)
    (fun b => mass_envIncL_le D L ha b)
  refine (expect_le_of_weight_ne_zero _ fun Jq hw => large_core (FiniteLaw.uniform _) D L
    (D.S.p_prime L) (TheoremCBlock.Structured.envIncL D L) (isPositiveRecord_envIncL D L) (dec L)
    (crtLabelEquiv blk (prefix_pairwise (hpair L)) L)
    (fun ω => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
      (revealedInputCRT blk hcop D L A Jq)
      (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω)
    (lpB_nonneg hL1 A hC.le)
    (fun v => hc D D.index.u hsc hL1 hM0 (D.S.p_prime L) (D.S.p_inj L) dvd_rfl Jq
      (fun e h0 => hw (queryLaw_weight_eq_zero D Jq e h0)) v)
    (atomQR D L) (atomQR_nonneg D L) (stageT_pos L hL1)
    (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)
    (fun φ hφ => large_of_not_small D hpair hpar L φ fun hs =>
      hφ ⟨fun e h0 => hw (queryLaw_weight_eq_zero D Jq e h0), hs⟩) _).trans ?_
  unfold largeConst
  exact final_le hL1 (Nat.cast_nonneg _) hC.le (density_nonneg _ _) hPi

/-- **`LargeSumPTEnvR`, proved** (`lem:record:density-lp` at the large folded pieces of `envC`;
the depth vectors with an unrevealed interval have zero query weight). -/
theorem largeSumPTEnvR_proved (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) :
    ∃ c : ℝ, 0 ≤ c ∧ Sarkozy.SharpSums.LargeSumPTEnvR hcop D hpair dec c := by
  obtain ⟨C, hC, hc⟩ := envInputs_moment_le (m₀ := m₀) (blk := blk) (p := paperTail) (E := E)
    hcop ((1 : ℝ) / 2000) (by norm_num)
  have hM0 : 1 ≤ modulus pr h := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  obtain ⟨Lstar, -, hLs⟩ := exists_scaleThreshold blockScale (modulus pr h) 1 1 0 0
    (by norm_num [blockScale]) hM0 le_rfl
  refine ⟨largeConst D C, largeConst_nonneg D hC.le, ?_⟩
  unfold Sarkozy.SharpSums.LargeSumPTEnvR
  filter_upwards [eventually_ge_atTop (max Lstar 1)] with L hL
  intro C' _ _ A _ _
  have hL1 : 1 ≤ L := le_of_max_le_right hL
  have hsc := hLs L (le_of_max_le_left hL)
  have hPi := prod_atomPr_le_exp D L ha (TheoremCBlock.Structured.envIncR D L)
    (fun b => TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (isPositiveRecord_envIncR D L b).1)
    (fun b => mass_envIncR_le D L ha b)
  refine (expect_le_of_weight_ne_zero _ fun Jq hw => large_core (FiniteLaw.uniform _) D L
    (D.S.p_prime L) (TheoremCBlock.Structured.envIncR D L) (isPositiveRecord_envIncR D L) (dec L)
    (crtLabelEquiv blk (prefix_pairwise (hpair L)) L)
    (fun ω => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
      (revealedInputCRT blk hcop D L A Jq)
      (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω)
    (lpB_nonneg hL1 A hC.le)
    (fun v => hc D D.index.w hsc hL1 hM0 (D.S.p_prime L) (D.S.p_inj L) dvd_rfl Jq
      (fun e h0 => hw (queryLaw_weight_eq_zero D Jq e h0)) v)
    (atomQR D L) (atomQR_nonneg D L) (stageT_pos L hL1)
    (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)
    (fun φ hφ => large_of_not_small D hpair hpar L φ fun hs =>
      hφ ⟨fun e h0 => hw (queryLaw_weight_eq_zero D Jq e h0), hs⟩) _).trans ?_
  unfold largeConst
  exact final_le hL1 (Nat.cast_nonneg _) hC.le (density_nonneg _ _) hPi

end Sarkozy.LargeSums
