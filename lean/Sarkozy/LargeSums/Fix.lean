module

public import Sarkozy.LargeSums.Moments
public import Sarkozy.SharpSums.Sums

@[expose] public section

/-!
# SUM's `LargeSumPTFixL` and `LargeSumPTFixR`, proved

LP (8 November 2026). **`largeSumPTFixL_proved`**, **`largeSumPTFixR_proved`**: for every
comparison datum on the paper's tails with the parity condition and `a ≥ 0`, there is `c ≥ 0`
with `LargeSumPTFixL hcop D hpair dec c` (resp. `R`). This is `lem:record:density-lp` at the
large folded pieces of `fixC` (`lem:sharp-first`, the error terms), in the paper's three steps
(`large_core`):

* Hölder in `L^{72}` per fold, with the uniform marginals of the folded positive records and the
  `72`-th moments of the revealed inputs (`fixInputs_moment_le`, `ε = 1/2000`);
* Rankin over the large pieces (`q_E > N^τ`, `large_of_not_small`) and the sums over the choices;
* `Π_H ≤ exp(D.SM.bound)` (`def:cp8`(c), `prod_atomPr_le_exp`, the wrapping increments having
  masses at most `s + a`), and (S4): `Q^{1/2000} N^{-τ/4} ≤ L^{-1/825}` (`lp_decay_le`).

The bound holds at every large `L` and every `A`, uniformly in the depth vector, so the
counterexample hypotheses are not used. The constant is
`c = |𝔗| M₀^{72} |X₀|^{72} C_ε K e^{D.SM.bound}`, `M₀ = modulus pr h`.
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

/-- **The constants** of the four large-piece sums: from `Π ≤ e^W` and (S4),
`|𝔗| B T^{-1/4} Π ≤ (|𝔗| M₀^{72} |X₀|^{72} C K e^W) L^{-1/825} α`. -/
theorem final_le {L : ℕ} (hL : 1 ≤ L) {nT M0 X C W Pi α : ℝ} (hnT : 0 ≤ nT) (hC : 0 ≤ C)
    (hα : 0 ≤ α) (hPi : Pi ≤ Real.exp W) :
    nT * ((M0 ^ 72 * (X ^ 72 * C * paperCutoff (blockScale * L) ^ ((1 : ℝ) / 2000) *
        ((blockScale : ℝ) * α))) *
        ((((blockScale * L : ℕ) : ℝ) ^ stageTau) ^ (-((1 : ℝ) / 4)) * Pi)) ≤
      nT * (M0 ^ 72 * (X ^ 72 * C * blockScale)) * Real.exp W *
        (L : ℝ) ^ (-Sarkozy.cancellationDecay) * α := by
  have key := lp_decay_le hL
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hQ0 : 0 ≤ paperCutoff (blockScale * L) ^ ((1 : ℝ) / 2000) *
      ((((blockScale * L : ℕ) : ℝ) ^ stageTau) ^ (-((1 : ℝ) / 4))) :=
    mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one (one_le_paperCutoff hKL)) _)
      (Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _)
  have h0 : 0 ≤ nT * M0 ^ 72 * X ^ 72 * C * (blockScale : ℝ) * α := by positivity
  calc _ = (nT * M0 ^ 72 * X ^ 72 * C * (blockScale : ℝ) * α) * Pi *
        (paperCutoff (blockScale * L) ^ ((1 : ℝ) / 2000) *
          ((((blockScale * L : ℕ) : ℝ) ^ stageTau) ^ (-((1 : ℝ) / 4)))) := by ring
    _ ≤ (nT * M0 ^ 72 * X ^ 72 * C * (blockScale : ℝ) * α) * Real.exp W *
          (L : ℝ) ^ (-Sarkozy.cancellationDecay) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hPi h0) key hQ0
          (mul_nonneg h0 (Real.exp_nonneg _))
    _ = _ := by ring

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- The constant of the large-piece sums: `|𝔗| M₀^{72} |X₀|^{72} C K e^{D.SM.bound}`. -/
noncomputable def largeConst (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (C : ℝ) : ℝ :=
  (Fintype.card D.FS.Tag : ℝ) * (((modulus pr h : ℕ) : ℝ) ^ 72 *
    ((Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * C * blockScale)) *
    Real.exp D.SM.bound

omit [DecidableEq P] in
theorem largeConst_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) {C : ℝ}
    (hC : 0 ≤ C) : 0 ≤ largeConst D C := by
  unfold largeConst
  positivity

/-- The common bound `B = M₀^{72} |X₀|^{72} C Q^ε K α` is nonnegative. -/
theorem lpB_nonneg {L : ℕ} (hL : 1 ≤ L) (A : Finset ℤ) {M0 X C : ℝ} (hC : 0 ≤ C) :
    0 ≤ M0 ^ 72 * (X ^ 72 * C * paperCutoff (blockScale * L) ^ ((1 : ℝ) / 2000) *
      ((blockScale : ℝ) * density (blockScale * L) A)) := by
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have := Real.rpow_nonneg (le_trans zero_le_one (one_le_paperCutoff hKL)) ((1 : ℝ) / 2000)
  have := density_nonneg (blockScale * L) A
  have : (0 : ℝ) ≤ blockScale := Nat.cast_nonneg _
  positivity

theorem stageT_pos (L : ℕ) (hL : 1 ≤ L) : 0 < (((blockScale * L : ℕ) : ℝ) ^ stageTau) := by
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  exact Real.rpow_pos_of_pos (by exact_mod_cast hKL) _

/-- **`LargeSumPTFixL`, proved** (`lem:record:density-lp` at the large folded pieces of `fixC`;
see the module docstring). -/
theorem largeSumPTFixL_proved (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) :
    ∃ c : ℝ, 0 ≤ c ∧ Sarkozy.SharpSums.LargeSumPTFixL hcop D hpair dec c := by
  obtain ⟨C, hC, hc⟩ := fixInputs_moment_le (m₀ := m₀) (blk := blk) (p := paperTail) (E := E)
    hcop ((1 : ℝ) / 2000) (by norm_num)
  have hM0 : 1 ≤ modulus pr h := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  obtain ⟨Lstar, -, hLs⟩ := exists_scaleThreshold blockScale (modulus pr h) 1 1 0 0
    (by norm_num [blockScale]) hM0 le_rfl
  refine ⟨largeConst D C, largeConst_nonneg D hC.le, ?_⟩
  unfold Sarkozy.SharpSums.LargeSumPTFixL
  filter_upwards [eventually_ge_atTop (max Lstar 1)] with L hL
  intro C' _ _ A _ _ S _
  have hL1 : 1 ≤ L := le_of_max_le_right hL
  have hsc := hLs L (le_of_max_le_left hL)
  have hPi := prod_atomPr_le_exp D L ha (TheoremCBlock.Structured.wrapInc D L)
    (fun b => TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (isPositiveRecord_wrapInc D L b).1)
    (fun b => mass_wrapInc_le D L ha b)
  refine (FiniteLaw.expect_le_const _ fun Jq => large_core (FiniteLaw.uniform _) D L
    (D.S.p_prime L) (TheoremCBlock.Structured.wrapInc D L) (isPositiveRecord_wrapInc D L) (dec L)
    (crtLabelEquiv blk (prefix_pairwise (hpair L)) L)
    (fun ω => pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
      (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
      (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω)
    (lpB_nonneg hL1 A hC.le)
    (fun v => hc D.S.Q.u 0 hsc hL1 hM0 (D.S.p_prime L) (D.S.p_inj L) dvd_rfl S Jq v)
    (atomQR D L) (atomQR_nonneg D L) (stageT_pos L hL1) (smallPiece m₀ blk D L)
    (fun φ hφ => large_of_not_small D hpair hpar L φ hφ) _).trans ?_
  unfold largeConst
  exact final_le hL1 (Nat.cast_nonneg _) hC.le (density_nonneg _ _) hPi

/-- **`LargeSumPTFixR`, proved** (as `largeSumPTFixL_proved`, at `t = 1` and the queries `w`). -/
theorem largeSumPTFixR_proved (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) :
    ∃ c : ℝ, 0 ≤ c ∧ Sarkozy.SharpSums.LargeSumPTFixR hcop D hpair dec c := by
  obtain ⟨C, hC, hc⟩ := fixInputs_moment_le (m₀ := m₀) (blk := blk) (p := paperTail) (E := E)
    hcop ((1 : ℝ) / 2000) (by norm_num)
  have hM0 : 1 ≤ modulus pr h := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  obtain ⟨Lstar, -, hLs⟩ := exists_scaleThreshold blockScale (modulus pr h) 1 1 0 0
    (by norm_num [blockScale]) hM0 le_rfl
  refine ⟨largeConst D C, largeConst_nonneg D hC.le, ?_⟩
  unfold Sarkozy.SharpSums.LargeSumPTFixR
  filter_upwards [eventually_ge_atTop (max Lstar 1)] with L hL
  intro C' _ _ A _ _ S _
  have hL1 : 1 ≤ L := le_of_max_le_right hL
  have hsc := hLs L (le_of_max_le_left hL)
  have hPi := prod_atomPr_le_exp D L ha (TheoremCBlock.Structured.wrapInc D L)
    (fun b => TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (isPositiveRecord_wrapInc D L b).1)
    (fun b => mass_wrapInc_le D L ha b)
  refine (FiniteLaw.expect_le_const _ fun Jq => large_core (FiniteLaw.uniform _) D L
    (D.S.p_prime L) (TheoremCBlock.Structured.wrapInc D L) (isPositiveRecord_wrapInc D L) (dec L)
    (crtLabelEquiv blk (prefix_pairwise (hpair L)) L)
    (fun ω => pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
      (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
      (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω)
    (lpB_nonneg hL1 A hC.le)
    (fun v => hc D.S.Q.w 1 hsc hL1 hM0 (D.S.p_prime L) (D.S.p_inj L) dvd_rfl S Jq v)
    (atomQR D L) (atomQR_nonneg D L) (stageT_pos L hL1) (smallPiece m₀ blk D L)
    (fun φ hφ => large_of_not_small D hpair hpar L φ hφ) _).trans ?_
  unfold largeConst
  exact final_le hL1 (Nat.cast_nonneg _) hC.le (density_nonneg _ _) hPi

end Sarkozy.LargeSums
