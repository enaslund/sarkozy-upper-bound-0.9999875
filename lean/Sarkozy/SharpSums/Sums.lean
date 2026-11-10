module

public import Sarkozy.SharpSums.Parts
public import Sarkozy.SharpSums.Chain2
public import Sarkozy.SharpBase2.Fields

@[expose] public section

/-!
# The four summations `RchSumPT*` reduced to the cross and large-piece terms

SUM (7 November 2026). With `SharpSums.Parts`, each per-choice remainder `rchPT*` is
`∑_j (√C cross_j + C chain_j + large_j)`. Here:

* **`chainSum_*_le`**: the chain² sums of the four summations, **proved** from the data:
  `∑_f ∑_{σ≠∅} ∑_j chain_j ≤ |𝔗| e^{T_* + U₀ + ∑_j (d_j + v_j)}` (`chain2_total_le`, DC3's piece
  prices, the totals `TL_total`, `TR_total`, `wrapEnvelope_price`, `U₀_total`,
  `sum_prices_le_totals`); `T_* = T` for the envelopes and `S + A` for the wrapping;
* **`rchSumPT*_of_parts`**: `RchSumPT*` with `c₂ = c_X + c_L + C_dc |𝔗| e^{…}` from two labelled
  inputs, the summed cross terms (`c_X`) and the summed large pieces (`c_L`).
-/

namespace Sarkozy.SharpSums

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.SharpBase2 Sarkozy.SharpBase
open Sarkozy.Param (Params)

section Algebra

/-- `c(1+s) + (1+u+s) ≤ e^{c+u+s}` for `c, u, s ≥ 0`. -/
theorem factor_le_exp {c u s : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u) (hs : 0 ≤ s) :
    c * (1 + s) + (1 + u + s) ≤ Real.exp (c + u + s) := by
  have hcu := mul_nonneg hc hu
  have hcus := mul_nonneg hcu hs
  have hus := mul_nonneg hu hs
  have h1 : c * (1 + s) + (1 + u + s) ≤ (1 + c) * (1 + u) * (1 + s) := by nlinarith
  have h2 : (1 + c) * (1 + u) * (1 + s) ≤ Real.exp c * Real.exp u * Real.exp s := by
    have ec := Real.add_one_le_exp c
    have eu := Real.add_one_le_exp u
    have es := Real.add_one_le_exp s
    have : (1 + c) * (1 + u) ≤ Real.exp c * Real.exp u :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (Real.exp_nonneg _)
    exact mul_le_mul this (by linarith) (by linarith) (by positivity)
  rw [Real.exp_add, Real.exp_add]
  linarith

/-- **The product of the atom factors, by the totals**: for nonnegative `c, u, s` with
`∑ c ≤ T`, `∑ u ≤ U`, `∑ s ≤ V`, `∏_𝔟 (c_𝔟 (1 + s_𝔟) + 1 + u_𝔟 + s_𝔟) ≤ e^{T + U + V}`. -/
theorem prod_factor_le_exp {ι : Type} [Fintype ι] (c u s : ι → ℝ) (hc : ∀ b, 0 ≤ c b)
    (hu : ∀ b, 0 ≤ u b) (hs : ∀ b, 0 ≤ s b) {T U V : ℝ} (hT : ∑ b, c b ≤ T) (hU : ∑ b, u b ≤ U)
    (hV : ∑ b, s b ≤ V) :
    ∏ b, (c b * (1 + s b) + (1 + u b + s b)) ≤ Real.exp (T + U + V) := by
  calc ∏ b, (c b * (1 + s b) + (1 + u b + s b)) ≤ ∏ b, Real.exp (c b + u b + s b) :=
        prod_le_prod₀ (fun b _ => by have := hc b; have := hu b; have := hs b; positivity)
          fun b _ => factor_le_exp (hc b) (hu b) (hs b)
    _ = Real.exp (∑ b, c b + ∑ b, u b + ∑ b, s b) := by
        rw [← Real.exp_sum, sum_add_distrib, sum_add_distrib]
    _ ≤ Real.exp (T + U + V) := Real.exp_le_exp.mpr (by linarith)

/-- **The final combination**: `X + Y + C K ≤ (c_X + c_L + C_dc K) L^{-σ} α` when
`X ≤ c_X L^{-σ} α`, `Y ≤ c_L L^{-σ} α` and `C = C_dc L^{-4σ} α`, `L ≥ 1`. -/
theorem final_combine {X Y Cd K cX cL α σ : ℝ} {L : ℕ} (hL : 1 ≤ L) (hσ : 0 ≤ σ) (hCd : 0 ≤ Cd)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hX : X ≤ cX * (L : ℝ) ^ (-σ) * α)
    (hY : Y ≤ cL * (L : ℝ) ^ (-σ) * α) :
    X + Y + Cd * (L : ℝ) ^ (-(4 * σ)) * α * K ≤ (cX + cL + Cd * K) * (L : ℝ) ^ (-σ) * α := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hpow : (L : ℝ) ^ (-(4 * σ)) ≤ (L : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h3 : Cd * (L : ℝ) ^ (-(4 * σ)) * α * K ≤ Cd * (L : ℝ) ^ (-σ) * α * K := by
    have := mul_le_mul_of_nonneg_left hpow hCd
    have := mul_le_mul_of_nonneg_right this hα
    exact mul_le_mul_of_nonneg_right this hK
  nlinarith

end Algebra

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- The atom sums `s_𝔟 = ∑_i (d_{𝔟,i} + v_{𝔟,i})` add up to the tag totals. -/
theorem sum_s_le (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (L : ℕ) :
    ∑ b, ∑ i, (D.FS.dprice L b i + D.FS.vprice L b i) ≤ ∑ j, (D.FS.dT j + D.FS.vT j) :=
  TheoremCBlock.Structured.sum_prices_le_totals D L

omit [DecidableEq P] in
theorem sum_uprice_le (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (L : ℕ) :
    ∑ b, D.GB.uprice L b ≤ D.GB.U₀ :=
  D.GB.U₀_total L

/-- The constant `C_dc` of the chain remainders at `C₁₀`, `C₇₁₀`. -/
noncomputable def cdc0 (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) : ℝ :=
  dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
    (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1₀ C71₀

omit [DecidableEq P] in
theorem cdc0_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) :
    0 ≤ cdc0 D :=
  dcConstant_nonneg (by exact_mod_cast (prefixConductor_pos blk _).le) (Nat.cast_nonneg _)
    C1₀_pos.le C71₀_pos.le

omit [DecidableEq P] in
theorem crDC_eq (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (L : ℕ)
    (A : Finset ℤ) :
    crDC D C1₀ C71₀ sigmaR L A =
      cdc0 D * (L : ℝ) ^ (-(4 * Sarkozy.cancellationDecay)) * density (blockScale * L) A := by
  unfold crDC cdc0 sigmaR
  rfl

omit [DecidableEq P] in
theorem crDC_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (L : ℕ)
    (A : Finset ℤ) : 0 ≤ crDC D C1₀ C71₀ sigmaR L A := by
  rw [crDC_eq]
  exact mul_nonneg (mul_nonneg (cdc0_nonneg D) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (density_nonneg _ _)

theorem cancellationDecay_nonneg : (0 : ℝ) ≤ Sarkozy.cancellationDecay := by
  norm_num [Sarkozy.cancellationDecay]

/-- **The chain² constant of `Sh.envM`**: `C_dc |𝔗| e^{T + U₀ + ∑_j (d_j + v_j)}`. -/
noncomputable def chainConstEnv (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) :
    ℝ :=
  cdc0 D * ((Fintype.card D.FS.Tag : ℝ) *
    Real.exp (D.ME.T + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)))

/-- **The chain² constant of `Sh.fixM`**: `C_dc |𝔗| e^{S + A + U₀ + ∑_j (d_j + v_j)}`. -/
noncomputable def chainConstFix (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) :
    ℝ :=
  cdc0 D * ((Fintype.card D.FS.Tag : ℝ) *
    Real.exp (D.CL.S + D.CL.A + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)))

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **The chain² sum of `RchSumPTEnvL`, proved** (`lem:sharp-first`, the products of the two
chain remainders): `∑_f ∑_{σ≠∅} ∑_j chain_j ≤ |𝔗| e^{T + U₀ + ∑_j (d_j + v_j)}`, at every
`𝒥`, `ω`
(DC3's piece prices with `uQ = envPriceL`, `PriceMatch`, the data totals). -/
theorem chainSum_envL_le (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) :
    ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ j : D.FS.Tag, chainPTEnvL hcop D hpair dec C1 C71 σ' L A Jq ω f σ j ≤
    (Fintype.card D.FS.Tag : ℝ) *
      Real.exp (D.ME.T + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) := by
  have hselF := hselF_of_parity D (prefix_pairwise (hpair 0)) hpar hsel L
  unfold chainPTEnvL rchChain
  refine (chain2_total_le D L (hpair L) (TheoremCBlock.Structured.envIncL D L)
    (isPositiveRecord_envIncL D L) (dec L) ha hselF (TheoremCBlock.Structured.envPriceL D L)
    (fun b => TheoremCBlock.Structured.envPriceL_nonneg D L b)
    (fun b => envIncL_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b))
    (fun _ φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact prod_factor_le_exp _ _ _ (fun b => TheoremCBlock.Structured.envPriceL_nonneg D L b)
    (fun b => TheoremCBlock.Structured.uprice_nonneg D L b)
    (fun b => sum_nonneg fun i _ => add_nonneg (TheoremCBlock.Structured.dprice_nonneg D L b i)
      (TheoremCBlock.Structured.vprice_nonneg D L b i))
    (D.ME.TL_total L) (sum_uprice_le D L) (sum_s_le D L)

/-- **The summed cross terms of `RchSumPTEnvL`** (`lem:sharp-first`: main term of one fold times
the chain remainder of the other, `prop:record:density-structured`): at counterexamples,
`E_𝒥 E_ω ∑_f ∑_{σ≠∅} ∑_j √C cross_j ≤ c_X L^{-1/825} α`. *Open* (needs `Y ≲ α` and
`E √P_± ≤ C`, see the report). -/
def CrossSumPTEnvL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (cX : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
            σ ≠ fun _ => none), ∑ j : D.FS.Tag, Real.sqrt (crDC D C1₀ C71₀ sigmaR L A) *
              crossPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j)) ≤
        cX * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- **The summed large pieces of `RchSumPTEnvL`** (`lem:record:density-lp`: the terms
`a_E (I⁺_E I⁻_E)^{1/2}` with `q_E > N^τ`, and the unrevealed intervals): at counterexamples,
`E_𝒥 E_ω ∑_f ∑_{σ≠∅} ∑_j large_j ≤ c_L L^{-1/825} α`. *Open* (Hölder `L^{72}` + Rankin, see the
report). -/
def LargeSumPTEnvL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (cL : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
            σ ≠ fun _ => none), ∑ j : D.FS.Tag,
              largePTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j)) ≤
        cL * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- **`RchSumPTEnvL` from the cross and large-piece sums** (`lem:sharp-first`, the error terms;
field 30): the chain² part is proved (`chainSum_envL_le`); the two labelled inputs are
* `hX`: the summed cross terms `√C ∑ cross_j ≤ c_X L^{-1/825} α` (main × chain remainder;
  `prop:record:density-structured` with `Y ≲ α`, open);
* `hLg`: the summed large pieces `∑ large_j ≤ c_L L^{-1/825} α` (`lem:record:density-lp`, open).
Then `RchSumPTEnvL` holds with `c₂ = c_X + c_L + C_dc |𝔗| e^{T + U₀ + ∑_j (d_j + v_j)}`. -/
theorem rchSumPTEnvL_of_parts (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    {cX cL : ℝ}
    (hX : CrossSumPTEnvL hcop D hpair dec cX) (hLg : LargeSumPTEnvL hcop D hpair dec cL) :
    RchSumPTEnvL hcop D hpair dec (cX + cL + chainConstEnv D) := by
  unfold CrossSumPTEnvL at hX
  unfold LargeSumPTEnvL at hLg
  unfold RchSumPTEnvL
  filter_upwards [hX, hLg, eventually_ge_atTop 1] with L hXL hLL hL1
  intro C hC hk A hA hY
  have hXA := hXL C hC hk A hA hY
  have hLA := hLL C hC hk A hA hY
  set K := (Fintype.card D.FS.Tag : ℝ) *
    Real.exp (D.ME.T + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) with hKdef
  have hK0 : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hCr0 := crDC_nonneg D L A
  set Cr := crDC D C1₀ C71₀ sigmaR L A with hCrdef
  have hpt : ∀ Jq ω, (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
      σ ≠ fun _ => none), rchPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ) ≤
      (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j : D.FS.Tag, Real.sqrt Cr *
          crossPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j) +
      (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j : D.FS.Tag, largePTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j) +
      Cr * K := by
    intro Jq ω
    have hch := chainSum_envL_le hcop D hpair dec ha hpar hsel C1₀ C71₀ sigmaR L A Jq ω
    have e1 : ∀ f σ, rchPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ =
        ∑ j : D.FS.Tag, (Real.sqrt Cr *
          crossPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j +
          Cr * chainPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j +
          largePTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j) :=
      fun f σ => rchPTEnvL_eq_parts hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ hCr0
    have e2 : (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
        σ ≠ fun _ => none), rchPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ) =
        (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j : D.FS.Tag, Real.sqrt Cr *
            crossPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j) +
        (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j : D.FS.Tag, largePTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j) +
        Cr * (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
          σ ≠ fun _ => none), ∑ j : D.FS.Tag,
            chainPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j) := by
      simp only [e1, sum_add_distrib, mul_sum]
      ring
    rw [e2]
    have := mul_le_mul_of_nonneg_left hch hCr0
    linarith
  refine (expect2_le_of_pt _ _ _ _ _ _ hpt).trans ?_
  rw [hCrdef, crDC_eq]
  unfold chainConstEnv
  rw [← hKdef]
  exact final_combine hL1 cancellationDecay_nonneg (cdc0_nonneg D) hK0 (density_nonneg _ _) hXA hLA

/-- **The chain² sum of `RchSumPTEnvR`, proved** (`lem:sharp-first`, the products of the two
chain remainders): `∑_f ∑_{σ≠∅} ∑_j chain_j ≤ |𝔗| e^{T + U₀ + ∑_j (d_j + v_j)}`, at every
`𝒥`, `ω`
(DC3's piece prices with `uQ = envPriceR`, `PriceMatch`, the data totals). -/
theorem chainSum_envR_le (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) :
    ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ j : D.FS.Tag, chainPTEnvR hcop D hpair dec C1 C71 σ' L A Jq ω f σ j ≤
    (Fintype.card D.FS.Tag : ℝ) *
      Real.exp (D.ME.T + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) := by
  have hselF := hselF_of_parity D (prefix_pairwise (hpair 0)) hpar hsel L
  unfold chainPTEnvR rchChain
  refine (chain2_total_le D L (hpair L) (TheoremCBlock.Structured.envIncR D L)
    (isPositiveRecord_envIncR D L) (dec L) ha hselF (TheoremCBlock.Structured.envPriceR D L)
    (fun b => TheoremCBlock.Structured.envPriceR_nonneg D L b)
    (fun b => envIncR_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b))
    (fun _ φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact prod_factor_le_exp _ _ _ (fun b => TheoremCBlock.Structured.envPriceR_nonneg D L b)
    (fun b => TheoremCBlock.Structured.uprice_nonneg D L b)
    (fun b => sum_nonneg fun i _ => add_nonneg (TheoremCBlock.Structured.dprice_nonneg D L b i)
      (TheoremCBlock.Structured.vprice_nonneg D L b i))
    (D.ME.TR_total L) (sum_uprice_le D L) (sum_s_le D L)

/-- **The summed cross terms of `RchSumPTEnvR`** (`lem:sharp-first`: main term of one fold times
the chain remainder of the other, `prop:record:density-structured`): at counterexamples,
`E_𝒥 E_ω ∑_f ∑_{σ≠∅} ∑_j √C cross_j ≤ c_X L^{-1/825} α`. *Open* (needs `Y ≲ α` and
`E √P_± ≤ C`, see the report). -/
def CrossSumPTEnvR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (cX : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
            σ ≠ fun _ => none), ∑ j : D.FS.Tag, Real.sqrt (crDC D C1₀ C71₀ sigmaR L A) *
              crossPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j)) ≤
        cX * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- **The summed large pieces of `RchSumPTEnvR`** (`lem:record:density-lp`: the terms
`a_E (I⁺_E I⁻_E)^{1/2}` with `q_E > N^τ`, and the unrevealed intervals): at counterexamples,
`E_𝒥 E_ω ∑_f ∑_{σ≠∅} ∑_j large_j ≤ c_L L^{-1/825} α`. *Open* (Hölder `L^{72}` + Rankin, see the
report). -/
def LargeSumPTEnvR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (cL : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
            σ ≠ fun _ => none), ∑ j : D.FS.Tag,
              largePTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j)) ≤
        cL * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- **`RchSumPTEnvR` from the cross and large-piece sums** (`lem:sharp-first`, the error terms;
field 31): the chain² part is proved (`chainSum_envR_le`); the two labelled inputs are
* `hX`: the summed cross terms `√C ∑ cross_j ≤ c_X L^{-1/825} α` (main × chain remainder;
  `prop:record:density-structured` with `Y ≲ α`, open);
* `hLg`: the summed large pieces `∑ large_j ≤ c_L L^{-1/825} α` (`lem:record:density-lp`, open).
Then `RchSumPTEnvR` holds with `c₂ = c_X + c_L + C_dc |𝔗| e^{T + U₀ + ∑_j (d_j + v_j)}`. -/
theorem rchSumPTEnvR_of_parts (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    {cX cL : ℝ}
    (hX : CrossSumPTEnvR hcop D hpair dec cX) (hLg : LargeSumPTEnvR hcop D hpair dec cL) :
    RchSumPTEnvR hcop D hpair dec (cX + cL + chainConstEnv D) := by
  unfold CrossSumPTEnvR at hX
  unfold LargeSumPTEnvR at hLg
  unfold RchSumPTEnvR
  filter_upwards [hX, hLg, eventually_ge_atTop 1] with L hXL hLL hL1
  intro C hC hk A hA hY
  have hXA := hXL C hC hk A hA hY
  have hLA := hLL C hC hk A hA hY
  set K := (Fintype.card D.FS.Tag : ℝ) *
    Real.exp (D.ME.T + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) with hKdef
  have hK0 : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hCr0 := crDC_nonneg D L A
  set Cr := crDC D C1₀ C71₀ sigmaR L A with hCrdef
  have hpt : ∀ Jq ω, (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
      σ ≠ fun _ => none), rchPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ) ≤
      (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j : D.FS.Tag, Real.sqrt Cr *
          crossPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j) +
      (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j : D.FS.Tag, largePTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j) +
      Cr * K := by
    intro Jq ω
    have hch := chainSum_envR_le hcop D hpair dec ha hpar hsel C1₀ C71₀ sigmaR L A Jq ω
    have e1 : ∀ f σ, rchPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ =
        ∑ j : D.FS.Tag, (Real.sqrt Cr *
          crossPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j +
          Cr * chainPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j +
          largePTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j) :=
      fun f σ => rchPTEnvR_eq_parts hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ hCr0
    have e2 : (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
        σ ≠ fun _ => none), rchPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ) =
        (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j : D.FS.Tag, Real.sqrt Cr *
            crossPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j) +
        (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j : D.FS.Tag, largePTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j) +
        Cr * (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
          σ ≠ fun _ => none), ∑ j : D.FS.Tag,
            chainPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j) := by
      simp only [e1, sum_add_distrib, mul_sum]
      ring
    rw [e2]
    have := mul_le_mul_of_nonneg_left hch hCr0
    linarith
  refine (expect2_le_of_pt _ _ _ _ _ _ hpt).trans ?_
  rw [hCrdef, crDC_eq]
  unfold chainConstEnv
  rw [← hKdef]
  exact final_combine hL1 cancellationDecay_nonneg (cdc0_nonneg D) hK0 (density_nonneg _ _) hXA hLA

/-- **The chain² sum of `RchSumPTFixL`, proved** (`lem:sharp-first`, the products of the two
chain remainders): `∑_f ∑_{σ≠∅} ∑_j chain_j ≤ |𝔗| e^{S + A + U₀ + ∑_j (d_j + v_j)}`, at
every `𝒥`, `ω`
(DC3's piece prices with `uQ = wrapPrice`, `PriceMatch`, the data totals). -/
theorem chainSum_fixL_le (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) :
    ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ j : D.FS.Tag, chainPTFixL hcop D hpair dec C1 C71 σ' L A S Jq ω f σ j ≤
    (Fintype.card D.FS.Tag : ℝ) *
      Real.exp (D.CL.S + D.CL.A + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) := by
  have hselF := hselF_of_parity D (prefix_pairwise (hpair 0)) hpar hsel L
  unfold chainPTFixL rchChain
  refine (chain2_total_le D L (hpair L) (TheoremCBlock.Structured.wrapInc D L)
    (isPositiveRecord_wrapInc D L) (dec L) ha hselF (TheoremCBlock.Structured.wrapPrice D L)
    (fun b => TheoremCBlock.Structured.wrapPrice_nonneg D L b)
    (fun b => wrapInc_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b))
    (fun _ φ => smallPiece m₀ blk D L φ)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact prod_factor_le_exp _ _ _ (fun b => TheoremCBlock.Structured.wrapPrice_nonneg D L b)
    (fun b => TheoremCBlock.Structured.uprice_nonneg D L b)
    (fun b => sum_nonneg fun i _ => add_nonneg (TheoremCBlock.Structured.dprice_nonneg D L b i)
      (TheoremCBlock.Structured.vprice_nonneg D L b i))
    (D.wrapEnvelope_price L) (sum_uprice_le D L) (sum_s_le D L)

/-- **The summed cross terms of `RchSumPTFixL`** (`lem:sharp-first`: main term of one fold times
the chain remainder of the other, `prop:record:density-structured`): at counterexamples,
`E_𝒥 E_ω ∑_f ∑_{σ≠∅} ∑_j √C cross_j ≤ c_X L^{-1/825} α`. *Open* (needs `Y ≲ α` and
`E √P_± ≤ C`, see the report). -/
def CrossSumPTFixL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (cX : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
            σ ≠ fun _ => none), ∑ j : D.FS.Tag, Real.sqrt (crDC D C1₀ C71₀ sigmaR L A) *
              crossPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j)) ≤
        cX * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- **The summed large pieces of `RchSumPTFixL`** (`lem:record:density-lp`: the terms
`a_E (I⁺_E I⁻_E)^{1/2}` with `q_E > N^τ`, and the unrevealed intervals): at counterexamples,
`E_𝒥 E_ω ∑_f ∑_{σ≠∅} ∑_j large_j ≤ c_L L^{-1/825} α`. *Open* (Hölder `L^{72}` + Rankin, see the
report). -/
def LargeSumPTFixL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (cL : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
            σ ≠ fun _ => none), ∑ j : D.FS.Tag,
              largePTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j)) ≤
        cL * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- **`RchSumPTFixL` from the cross and large-piece sums** (`lem:sharp-first`, the error terms;
`Sh.fixM.hdiffL`): the chain² part is proved (`chainSum_fixL_le`); the two labelled inputs are
* `hX`: the summed cross terms `√C ∑ cross_j ≤ c_X L^{-1/825} α` (main × chain remainder;
  `prop:record:density-structured` with `Y ≲ α`, open);
* `hLg`: the summed large pieces `∑ large_j ≤ c_L L^{-1/825} α` (`lem:record:density-lp`, open).
Then `RchSumPTFixL` holds with `c₂ = c_X + c_L + C_dc |𝔗| e^{S + A + U₀ + ∑_j (d_j + v_j)}`. -/
theorem rchSumPTFixL_of_parts (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    {cX cL : ℝ}
    (hX : CrossSumPTFixL hcop D hpair dec cX) (hLg : LargeSumPTFixL hcop D hpair dec cL) :
    RchSumPTFixL hcop D hpair dec (cX + cL + chainConstFix D) := by
  unfold CrossSumPTFixL at hX
  unfold LargeSumPTFixL at hLg
  unfold RchSumPTFixL
  filter_upwards [hX, hLg, eventually_ge_atTop 1] with L hXL hLL hL1
  intro C hC hk A hA hY S hS
  have hXA := hXL C hC hk A hA hY S hS
  have hLA := hLL C hC hk A hA hY S hS
  set K := (Fintype.card D.FS.Tag : ℝ) *
    Real.exp (D.CL.S + D.CL.A + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) with hKdef
  have hK0 : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hCr0 := crDC_nonneg D L A
  set Cr := crDC D C1₀ C71₀ sigmaR L A with hCrdef
  have hpt : ∀ Jq ω, (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
      σ ≠ fun _ => none), rchPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ) ≤
      (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j : D.FS.Tag, Real.sqrt Cr *
          crossPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j) +
      (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j : D.FS.Tag, largePTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j) +
      Cr * K := by
    intro Jq ω
    have hch := chainSum_fixL_le hcop D hpair dec ha hpar hsel C1₀ C71₀ sigmaR L A S Jq ω
    have e1 : ∀ f σ, rchPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ =
        ∑ j : D.FS.Tag, (Real.sqrt Cr *
          crossPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j +
          Cr * chainPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j +
          largePTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j) :=
      fun f σ => rchPTFixL_eq_parts hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ hCr0
    have e2 : (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
        σ ≠ fun _ => none), rchPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ) =
        (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j : D.FS.Tag, Real.sqrt Cr *
            crossPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j) +
        (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j : D.FS.Tag, largePTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j) +
        Cr * (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
          σ ≠ fun _ => none), ∑ j : D.FS.Tag,
            chainPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j) := by
      simp only [e1, sum_add_distrib, mul_sum]
      ring
    rw [e2]
    have := mul_le_mul_of_nonneg_left hch hCr0
    linarith
  refine (expect2_le_of_pt _ _ _ _ _ _ hpt).trans ?_
  rw [hCrdef, crDC_eq]
  unfold chainConstFix
  rw [← hKdef]
  exact final_combine hL1 cancellationDecay_nonneg (cdc0_nonneg D) hK0 (density_nonneg _ _) hXA hLA

/-- **The chain² sum of `RchSumPTFixR`, proved** (`lem:sharp-first`, the products of the two
chain remainders): `∑_f ∑_{σ≠∅} ∑_j chain_j ≤ |𝔗| e^{S + A + U₀ + ∑_j (d_j + v_j)}`, at
every `𝒥`, `ω`
(DC3's piece prices with `uQ = wrapPrice`, `PriceMatch`, the data totals). -/
theorem chainSum_fixR_le (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) :
    ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ j : D.FS.Tag, chainPTFixR hcop D hpair dec C1 C71 σ' L A S Jq ω f σ j ≤
    (Fintype.card D.FS.Tag : ℝ) *
      Real.exp (D.CL.S + D.CL.A + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) := by
  have hselF := hselF_of_parity D (prefix_pairwise (hpair 0)) hpar hsel L
  unfold chainPTFixR rchChain
  refine (chain2_total_le D L (hpair L) (TheoremCBlock.Structured.wrapInc D L)
    (isPositiveRecord_wrapInc D L) (dec L) ha hselF (TheoremCBlock.Structured.wrapPrice D L)
    (fun b => TheoremCBlock.Structured.wrapPrice_nonneg D L b)
    (fun b => wrapInc_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b))
    (fun _ φ => smallPiece m₀ blk D L φ)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact prod_factor_le_exp _ _ _ (fun b => TheoremCBlock.Structured.wrapPrice_nonneg D L b)
    (fun b => TheoremCBlock.Structured.uprice_nonneg D L b)
    (fun b => sum_nonneg fun i _ => add_nonneg (TheoremCBlock.Structured.dprice_nonneg D L b i)
      (TheoremCBlock.Structured.vprice_nonneg D L b i))
    (D.wrapEnvelope_price L) (sum_uprice_le D L) (sum_s_le D L)

/-- **The summed cross terms of `RchSumPTFixR`** (`lem:sharp-first`: main term of one fold times
the chain remainder of the other, `prop:record:density-structured`): at counterexamples,
`E_𝒥 E_ω ∑_f ∑_{σ≠∅} ∑_j √C cross_j ≤ c_X L^{-1/825} α`. *Open* (needs `Y ≲ α` and
`E √P_± ≤ C`, see the report). -/
def CrossSumPTFixR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (cX : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
            σ ≠ fun _ => none), ∑ j : D.FS.Tag, Real.sqrt (crDC D C1₀ C71₀ sigmaR L A) *
              crossPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j)) ≤
        cX * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- **The summed large pieces of `RchSumPTFixR`** (`lem:record:density-lp`: the terms
`a_E (I⁺_E I⁻_E)^{1/2}` with `q_E > N^τ`, and the unrevealed intervals): at counterexamples,
`E_𝒥 E_ω ∑_f ∑_{σ≠∅} ∑_j large_j ≤ c_L L^{-1/825} α`. *Open* (Hölder `L^{72}` + Rankin, see the
report). -/
def LargeSumPTFixR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (cL : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
            σ ≠ fun _ => none), ∑ j : D.FS.Tag,
              largePTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j)) ≤
        cL * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- **`RchSumPTFixR` from the cross and large-piece sums** (`lem:sharp-first`, the error terms;
`Sh.fixM.hdiffR`): the chain² part is proved (`chainSum_fixR_le`); the two labelled inputs are
* `hX`: the summed cross terms `√C ∑ cross_j ≤ c_X L^{-1/825} α` (main × chain remainder;
  `prop:record:density-structured` with `Y ≲ α`, open);
* `hLg`: the summed large pieces `∑ large_j ≤ c_L L^{-1/825} α` (`lem:record:density-lp`, open).
Then `RchSumPTFixR` holds with `c₂ = c_X + c_L + C_dc |𝔗| e^{S + A + U₀ + ∑_j (d_j + v_j)}`. -/
theorem rchSumPTFixR_of_parts (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    {cX cL : ℝ}
    (hX : CrossSumPTFixR hcop D hpair dec cX) (hLg : LargeSumPTFixR hcop D hpair dec cL) :
    RchSumPTFixR hcop D hpair dec (cX + cL + chainConstFix D) := by
  unfold CrossSumPTFixR at hX
  unfold LargeSumPTFixR at hLg
  unfold RchSumPTFixR
  filter_upwards [hX, hLg, eventually_ge_atTop 1] with L hXL hLL hL1
  intro C hC hk A hA hY S hS
  have hXA := hXL C hC hk A hA hY S hS
  have hLA := hLL C hC hk A hA hY S hS
  set K := (Fintype.card D.FS.Tag : ℝ) *
    Real.exp (D.CL.S + D.CL.A + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) with hKdef
  have hK0 : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hCr0 := crDC_nonneg D L A
  set Cr := crDC D C1₀ C71₀ sigmaR L A with hCrdef
  have hpt : ∀ Jq ω, (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
      σ ≠ fun _ => none), rchPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ) ≤
      (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j : D.FS.Tag, Real.sqrt Cr *
          crossPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j) +
      (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j : D.FS.Tag, largePTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j) +
      Cr * K := by
    intro Jq ω
    have hch := chainSum_fixR_le hcop D hpair dec ha hpar hsel C1₀ C71₀ sigmaR L A S Jq ω
    have e1 : ∀ f σ, rchPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ =
        ∑ j : D.FS.Tag, (Real.sqrt Cr *
          crossPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j +
          Cr * chainPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j +
          largePTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j) :=
      fun f σ => rchPTFixR_eq_parts hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ hCr0
    have e2 : (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
        σ ≠ fun _ => none), rchPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ) =
        (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j : D.FS.Tag, Real.sqrt Cr *
            crossPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j) +
        (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j : D.FS.Tag, largePTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j) +
        Cr * (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
          σ ≠ fun _ => none), ∑ j : D.FS.Tag,
            chainPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j) := by
      simp only [e1, sum_add_distrib, mul_sum]
      ring
    rw [e2]
    have := mul_le_mul_of_nonneg_left hch hCr0
    linarith
  refine (expect2_le_of_pt _ _ _ _ _ _ hpt).trans ?_
  rw [hCrdef, crDC_eq]
  unfold chainConstFix
  rw [← hKdef]
  exact final_combine hL1 cancellationDecay_nonneg (cdc0_nonneg D) hK0 (density_nonneg _ _) hXA hLA

end Sarkozy.SharpSums
