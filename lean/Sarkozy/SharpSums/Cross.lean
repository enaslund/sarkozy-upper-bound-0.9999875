module

public import Sarkozy.SharpSums.Inputs

@[expose] public section

/-!
# The cross terms of `lem:sharp-first`, reduced to `Y ≲ L^{2σ} α` and `E P_± ≤ C_P`

SUM (7 November 2026). The cross term of a small piece is
`√C (√(BG M₊ G₋) + √(G₊ BG M₋))` with `M_± = K₀ P_±`, `K₀ = (1 + u) Y ∏_{f} π_𝔟` and
`G_± ≤ BG ∏_f π_𝔟` (DC3's piece prices, `uQ = π`). So (`crossPart_le`)
`cross ≤ √((1 + u) Y) (√P₊ + √P₋) ∏_f π · ∑_φ w BG`, and the weight sum is the one of the chain²
part (`weight_total_le`). Here:

* `expect_sqrt_le`, `expect2_sqrt_le`: `E √X ≤ √(E X)` (Cauchy–Schwarz);
* `crossPT*_le`: the pointwise bound of one cross part;
* `crossSum_*_pt`: `∑_f ∑_{σ≠∅} ∑_j cross_j ≤ √((1 + u) Y) e^{…} ∑_j (√P₊(j) + √P₋(j))`;
* **`crossSumPT*_of_bounds`**: `CrossSumPT*` with `c_X = √(2 C_dc C_Y) e^{…} · 2|𝔗| √C_P` from two
  labelled inputs at counterexamples:
  - `hY`: `Y ≤ C_Y L^{2/825} α` (the paper: `Y ≤ C_ε N^ε α` by Hölder in `L^{72}` and
    `lem:record:lift-moments`(c), as in the proof of `lem:record:density-lp`);
  - `hP`: `E_𝒥 E_ω P_±(j) ≤ C_P` at every tag (B9's local-density means with the per-query
    exponents of the folds);
  and `u_L → 0` (`tendsto_scaleU_stage`).
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

/-- **Jensen for `√`**: `E √X ≤ √(E X)` for `X ≥ 0`. -/
theorem expect_sqrt_le {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (hX : ∀ ω, 0 ≤ X ω) : μ.expect (fun ω => Real.sqrt (X ω)) ≤ Real.sqrt (μ.expect X) := by
  have h := μ.cauchy_schwarz_sq (fun ω => Real.sqrt (X ω)) (fun _ => 1)
  simp only [mul_one, one_pow, FiniteLaw.expect_const] at h
  have e : μ.expect (fun ω => Real.sqrt (X ω) ^ 2) = μ.expect X :=
    FiniteLaw.expect_congr _ fun ω => Real.sq_sqrt (hX ω)
  rw [e] at h
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

/-- `E_x E_y √X ≤ √(E_x E_y X)` for `X ≥ 0`. -/
theorem expect2_sqrt_le {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] (μ : FiniteLaw Ω₁)
    (ν : FiniteLaw Ω₂) (X : Ω₁ → Ω₂ → ℝ) (hX : ∀ x y, 0 ≤ X x y) :
    μ.expect (fun x => ν.expect (fun y => Real.sqrt (X x y))) ≤
      Real.sqrt (μ.expect (fun x => ν.expect (X x))) := by
  refine (μ.expect_mono fun x => expect_sqrt_le ν (X x) (hX x)).trans ?_
  exact expect_sqrt_le μ _ fun x => ν.expect_nonneg (hX x)

/-- The final arithmetic of the cross terms: `√(C K') ≤ √(2 C_dc C_Y) L^{-σ} α` when
`C = C_dc L^{-4σ} α`, `K' = (1 + u) Y`, `u ≤ 1`, `0 ≤ Y ≤ C_Y L^{2σ} α`. -/
theorem sqrt_cross_const_le {Cd CY u Y α σ : ℝ} {L : ℕ} (hL : 1 ≤ L) (hCd : 0 ≤ Cd)
    (hCY0 : 0 ≤ CY) (hu : u ≤ 1) (hY0 : 0 ≤ Y) (hα : 0 ≤ α)
    (hY : Y ≤ CY * (L : ℝ) ^ (2 * σ) * α) :
    Real.sqrt (Cd * (L : ℝ) ^ (-(4 * σ)) * α) * Real.sqrt ((1 + u) * Y) ≤
      Real.sqrt (2 * Cd * CY) * (L : ℝ) ^ (-σ) * α := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hp1 : 0 ≤ (L : ℝ) ^ (-(4 * σ)) := Real.rpow_nonneg hL0.le _
  have hp2 : 0 ≤ (L : ℝ) ^ (-σ) := Real.rpow_nonneg hL0.le _
  have hpow : (L : ℝ) ^ (-(4 * σ)) * (L : ℝ) ^ (2 * σ) = ((L : ℝ) ^ (-σ)) ^ 2 := by
    rw [← Real.rpow_add hL0, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1
    push_cast
    ring
  have hprod : Cd * (L : ℝ) ^ (-(4 * σ)) * α * ((1 + u) * Y) ≤
      2 * Cd * CY * ((L : ℝ) ^ (-σ) * α) ^ 2 := by
    have h1 : (1 + u) * Y ≤ 2 * (CY * (L : ℝ) ^ (2 * σ) * α) := by nlinarith
    have h2 : 0 ≤ Cd * (L : ℝ) ^ (-(4 * σ)) * α := by positivity
    calc Cd * (L : ℝ) ^ (-(4 * σ)) * α * ((1 + u) * Y)
        ≤ Cd * (L : ℝ) ^ (-(4 * σ)) * α * (2 * (CY * (L : ℝ) ^ (2 * σ) * α)) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = 2 * Cd * CY * ((L : ℝ) ^ (-(4 * σ)) * (L : ℝ) ^ (2 * σ)) * α ^ 2 := by ring
      _ = 2 * Cd * CY * ((L : ℝ) ^ (-σ) * α) ^ 2 := by rw [hpow]; ring
  rw [← Real.sqrt_mul (by positivity)]
  have h2CY : 0 ≤ 2 * Cd * CY := by positivity
  calc Real.sqrt (Cd * (L : ℝ) ^ (-(4 * σ)) * α * ((1 + u) * Y))
      ≤ Real.sqrt (2 * Cd * CY * ((L : ℝ) ^ (-σ) * α) ^ 2) := Real.sqrt_le_sqrt hprod
    _ = Real.sqrt (2 * Cd * CY) * ((L : ℝ) ^ (-σ) * α) := by
        rw [Real.sqrt_mul h2CY, Real.sqrt_sq (by positivity)]
    _ = _ := by ring

/-- Swapping the tag sum outside: `∑_f ∑_{σ∈s} ∑_j c_j g = ∑_j c_j ∑_f ∑_{σ∈s} g`. -/
theorem sum3_swap {α β γ : Type*} [Fintype α] [Fintype γ] (s : Finset β) (c : γ → ℝ)
    (g : α → β → γ → ℝ) :
    ∑ f, ∑ σ ∈ s, ∑ j, c j * g f σ j = ∑ j, c j * ∑ f, ∑ σ ∈ s, g f σ j := by
  simp_rw [mul_sum]
  refine (sum_congr rfl fun f _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **One cross part of `rchPTEnvL`** (`lem:sharp-first`): with DC3's piece prices
(`uQ = envPriceL`), `cross_j ≤ √((1 + u) Y) (√P₊ + √P₋) ∏_f π · ∑_φ w_φ BG(φ)`. -/
theorem crossPTEnvL_le (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (hK' : 0 ≤ (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
      D.Y L A) :
    crossPTEnvL hcop D hpair dec C1 C71 σ' L A Jq ω f σ j ≤
      Real.sqrt ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
        D.Y L A) *
        (Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldPlus) +
          Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldMinus)) *
        ((∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)) *
          ∑ φ : (∀ b, DensityFibre.HPiece D L b),
            choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
              ∏ b, DensityFibre.bpieceG D L b (φ b)) := by
  have hselF := hselF_of_parity D (prefix_pairwise (hpair 0)) hpar hsel L
  unfold crossPTEnvL rchCross
  set Kf := ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1) with hKf
  have hKf0 : 0 ≤ Kf := prod_nonneg fun b _ => by
    split_ifs
    · exact TheoremCBlock.Structured.envPriceL_nonneg D L b
    · exact zero_le_one
  set K' := (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
    D.Y L A with hK'def
  have hK0 : 0 ≤ K' * Kf := mul_nonneg hK' hKf0
  have hc := crossPart_le (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ) hK0
    (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.u L A Jq ω
      (D.FS.cut j).foldPlus)
    (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.u L A Jq ω
      (D.FS.cut j).foldMinus)
    (fun φ => choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ)
    (fun φ => ∏ b, DensityFibre.bpieceG D L b (φ b))
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncL D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncL D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun _ => Kf) (fun φ => choiceWeight_nonneg' D L f σ j φ)
    (fun φ => prod_nonneg fun b _ => DensityFibre.bpieceG_nonneg D L b (φ b)) (fun _ => hKf0)
    (fun φ hw => piecePrice_plus_le_one D L (hpair L) (TheoremCBlock.Structured.envIncL D L)
      (isPositiveRecord_envIncL D L) (dec L) ha j f σ φ
      (coef_ne_zero_of_weight_ne_zero D L f σ j φ hw) hselF
      (TheoremCBlock.Structured.envPriceL D L)
      (fun b => envIncL_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b)))
    (fun φ hw => piecePrice_minus_le_one D L (hpair L) (TheoremCBlock.Structured.envIncL D L)
      (isPositiveRecord_envIncL D L) (dec L) ha j f σ φ
      (coef_ne_zero_of_weight_ne_zero D L f σ j φ hw) hselF
      (TheoremCBlock.Structured.envPriceL D L)
      (fun b => envIncL_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b)))
  refine (le_of_eq ?_).trans (hc.trans (le_of_eq ?_))
  · rfl
  · have e : ∑ φ : (∀ b, DensityFibre.HPiece D L b),
        choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
          ((∏ b, DensityFibre.bpieceG D L b (φ b)) * Real.sqrt Kf) =
        Real.sqrt Kf * ∑ φ : (∀ b, DensityFibre.HPiece D L b),
          choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
            ∏ b, DensityFibre.bpieceG D L b (φ b) := by
      rw [mul_sum]
      exact sum_congr rfl fun φ _ => by ring
    rw [e, Real.sqrt_mul hK' Kf]
    have hsq : Real.sqrt Kf * Real.sqrt Kf = Kf := Real.mul_self_sqrt hKf0
    generalize Real.sqrt Kf = r at hsq ⊢
    rw [← hsq]
    ring

/-- **The summed cross parts of `rchPTEnvL`, pointwise**: `∑_f ∑_{σ≠∅} ∑_j cross_j ≤
√((1 + u) Y) e^{T + U₀ + ∑_j (d_j + v_j)} ∑_j (√P₊(j) + √P₋(j))`. -/
theorem crossSum_envL_pt (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (hK' : 0 ≤ (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
      D.Y L A) :
    ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ j : D.FS.Tag, crossPTEnvL hcop D hpair dec C1 C71 σ' L A Jq ω f σ j ≤
    Real.sqrt ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
        D.Y L A) * Real.exp (D.ME.T + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) *
      ∑ j : D.FS.Tag,
        (Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldPlus) +
          Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldMinus)) := by
  set K' := (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
    D.Y L A with hK'def
  set X : D.FS.Tag → ℝ := fun j =>
    Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldPlus) +
      Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldMinus)
    with hXdef
  have hX0 : ∀ j, 0 ≤ X j := fun j => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc _ ≤ ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ j : D.FS.Tag, (Real.sqrt K' * X j) *
        ((∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)) *
          ∑ φ : (∀ b, DensityFibre.HPiece D L b),
            choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
              ∏ b, DensityFibre.bpieceG D L b (φ b)) :=
        sum_le_sum fun f _ => sum_le_sum fun σ _ => sum_le_sum fun j _ =>
          crossPTEnvL_le hcop D hpair dec ha hpar hsel C1 C71 σ' L A Jq ω f σ j hK'
    _ = ∑ j : D.FS.Tag, (Real.sqrt K' * X j) *
        ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ((∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)) *
            ∑ φ : (∀ b, DensityFibre.HPiece D L b),
              choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
                ∏ b, DensityFibre.bpieceG D L b (φ b)) := sum3_swap _ _ _
    _ ≤ ∑ j : D.FS.Tag, (Real.sqrt K' * X j) *
        Real.exp (D.ME.T + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) := by
        refine sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (Real.sqrt_nonneg _) (hX0 j))
        refine (weight_total_le D L j _
          (fun b => TheoremCBlock.Structured.envPriceL_nonneg D L b)).trans ?_
        exact prod_factor_le_exp _ _ _ (fun b => TheoremCBlock.Structured.envPriceL_nonneg D L b)
          (fun b => TheoremCBlock.Structured.uprice_nonneg D L b)
          (fun b => sum_nonneg fun i _ => add_nonneg
            (TheoremCBlock.Structured.dprice_nonneg D L b i)
            (TheoremCBlock.Structured.vprice_nonneg D L b i))
          (D.ME.TL_total L) (sum_uprice_le D L) (sum_s_le D L)
    _ = _ := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by ring

/-- **The cross sums of `RchSumPTEnvL` from `Y ≲ L^{2σ} α` and `E P_± ≤ C_P`**
(`lem:sharp-first`, the cross terms; `prop:record:density-structured`): `CrossSumPTEnvL` with
`c_X = √(2 C_dc C_Y) e^{T + U₀ + ∑_j (d_j + v_j)} · 2|𝔗| √C_P`. The two inputs are labelled:
`hY` (`Y ≤ C_Y L^{2/825} α` at counterexamples; the paper's Hölder bound `Y ≤ C_ε N^ε α`) and
`hP` (the means of the main prices of the folds, B9's local-density means). -/
theorem crossSumPTEnvL_of_bounds (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    {CY CP : ℝ} (hCY : 0 ≤ CY)
    (hY : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      D.Y L A ≤ CY * (L : ℝ) ^ (2 * Sarkozy.cancellationDecay) * density (blockScale * L) A))
    (hP : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ j : D.FS.Tag,
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldPlus)) ≤
        CP ∧
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldMinus)) ≤
        CP)) :
    CrossSumPTEnvL hcop D hpair dec (Real.sqrt (2 * cdc0 D * CY) *
      Real.exp (D.ME.T + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) *
      (2 * (Fintype.card D.FS.Tag : ℝ) * Real.sqrt CP)) := by
  unfold CrossSumPTEnvL
  have hu : ∀ᶠ L : ℕ in atTop,
      scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L < 1 :=
    (tendsto_order.1 (tendsto_scaleU_stage (M0 := modulus pr h) (Qcl := cliqueConstant m₀ D.S.ep)
      (by norm_num [blockScale]))).2 1 one_pos
  filter_upwards [hY, hP, hu, eventually_ge_atTop 1] with L hYL hPL huL hL1
  intro C hC hk A hA hYc
  have hYA := hYL C hC hk A hA hYc
  have hPA := hPL C hC hk A hA hYc
  have hY0 : 0 ≤ D.Y L A := (Param.counterexample_pos _ hC hYc).le
  have hu0 := scaleU_nonneg' blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) L
  have hK' : 0 ≤ (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
      D.Y L A := mul_nonneg (by linarith) hY0
  set ex := Real.exp (D.ME.T + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) with hex
  set K' := (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
    D.Y L A with hK'def
  set Cr := crDC D C1₀ C71₀ sigmaR L A with hCr
  have hpt : ∀ Jq ω, (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
      σ ≠ fun _ => none), ∑ j : D.FS.Tag, Real.sqrt Cr *
        crossPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j) ≤
      Real.sqrt Cr * (Real.sqrt K' * ex * ∑ j : D.FS.Tag,
        (Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldPlus) +
          Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω
            (D.FS.cut j).foldMinus))) := by
    intro Jq ω
    simp_rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left
      (crossSum_envL_pt hcop D hpair dec ha hpar hsel C1₀ C71₀ sigmaR L A Jq ω hK')
      (Real.sqrt_nonneg _)
  refine ((queryLaw D.index.C D.index.t).expect_mono fun Jq =>
    (FiniteLaw.uniform _).expect_mono fun ω => hpt Jq ω).trans ?_
  simp only [FiniteLaw.expect_const_mul, FiniteLaw.expect_sum, FiniteLaw.expect_add]
  have hj : ∀ j : D.FS.Tag,
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω
            (D.FS.cut j).foldPlus))) +
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω
            (D.FS.cut j).foldMinus))) ≤ 2 * Real.sqrt CP := by
    intro j
    have h1 := expect2_sqrt_le (queryLaw D.index.C D.index.t)
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j))
      (fun Jq ω => envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldPlus)
      (fun Jq ω => envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.u L A Jq ω _)
    have h2 := expect2_sqrt_le (queryLaw D.index.C D.index.t)
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j))
      (fun Jq ω => envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldMinus)
      (fun Jq ω => envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.u L A Jq ω _)
    have h3 := Real.sqrt_le_sqrt (hPA j).1
    have h4 := Real.sqrt_le_sqrt (hPA j).2
    linarith
  have hsum := sum_le_sum fun j (_ : j ∈ (univ : Finset D.FS.Tag)) => hj j
  rw [sum_const, card_univ, nsmul_eq_mul] at hsum
  have hc := sqrt_cross_const_le (Cd := cdc0 D) (CY := CY) (u := scaleU blockScale (modulus pr h)
    (cliqueConstant m₀ D.S.ep) stageTau L) (σ := Sarkozy.cancellationDecay) hL1 (cdc0_nonneg D)
    hCY huL.le hY0 (density_nonneg _ _) hYA
  rw [← crDC_eq] at hc
  have hex0 : 0 ≤ ex := Real.exp_nonneg _
  have hsc : 0 ≤ Real.sqrt Cr * (Real.sqrt K' * ex) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hex0)
  calc Real.sqrt Cr * (Real.sqrt K' * ex * ∑ j : D.FS.Tag, _)
      ≤ Real.sqrt Cr *
          (Real.sqrt K' * ex * ((Fintype.card D.FS.Tag : ℝ) * (2 * Real.sqrt CP))) := by
        have hm := mul_le_mul_of_nonneg_left hsum hsc
        exact le_trans (le_of_eq (by ring)) (hm.trans (le_of_eq (by ring)))
    _ = (Real.sqrt Cr * Real.sqrt K') *
          (ex * (2 * (Fintype.card D.FS.Tag : ℝ) * Real.sqrt CP)) := by
        ring
    _ ≤ (Real.sqrt (2 * cdc0 D * CY) * (L : ℝ) ^ (-Sarkozy.cancellationDecay) *
          density (blockScale * L) A) * (ex * (2 * (Fintype.card D.FS.Tag : ℝ) * Real.sqrt CP)) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg hex0 (mul_nonneg (by positivity)
          (Real.sqrt_nonneg _)))
    _ = _ := by ring

/-- **One cross part of `rchPTEnvR`** (`lem:sharp-first`): with DC3's piece prices
(`uQ = envPriceR`), `cross_j ≤ √((1 + u) Y) (√P₊ + √P₋) ∏_f π · ∑_φ w_φ BG(φ)`. -/
theorem crossPTEnvR_le (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (hK' : 0 ≤ (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
      D.Y L A) :
    crossPTEnvR hcop D hpair dec C1 C71 σ' L A Jq ω f σ j ≤
      Real.sqrt ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
        D.Y L A) *
        (Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldPlus) +
          Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldMinus)) *
        ((∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)) *
          ∑ φ : (∀ b, DensityFibre.HPiece D L b),
            choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
              ∏ b, DensityFibre.bpieceG D L b (φ b)) := by
  have hselF := hselF_of_parity D (prefix_pairwise (hpair 0)) hpar hsel L
  unfold crossPTEnvR rchCross
  set Kf := ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1) with hKf
  have hKf0 : 0 ≤ Kf := prod_nonneg fun b _ => by
    split_ifs
    · exact TheoremCBlock.Structured.envPriceR_nonneg D L b
    · exact zero_le_one
  set K' := (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
    D.Y L A with hK'def
  have hK0 : 0 ≤ K' * Kf := mul_nonneg hK' hKf0
  have hc := crossPart_le (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ) hK0
    (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.w L A Jq ω
      (D.FS.cut j).foldPlus)
    (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.w L A Jq ω
      (D.FS.cut j).foldMinus)
    (fun φ => choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ)
    (fun φ => ∏ b, DensityFibre.bpieceG D L b (φ b))
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncR D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncR D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun _ => Kf) (fun φ => choiceWeight_nonneg' D L f σ j φ)
    (fun φ => prod_nonneg fun b _ => DensityFibre.bpieceG_nonneg D L b (φ b)) (fun _ => hKf0)
    (fun φ hw => piecePrice_plus_le_one D L (hpair L) (TheoremCBlock.Structured.envIncR D L)
      (isPositiveRecord_envIncR D L) (dec L) ha j f σ φ
      (coef_ne_zero_of_weight_ne_zero D L f σ j φ hw) hselF
      (TheoremCBlock.Structured.envPriceR D L)
      (fun b => envIncR_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b)))
    (fun φ hw => piecePrice_minus_le_one D L (hpair L) (TheoremCBlock.Structured.envIncR D L)
      (isPositiveRecord_envIncR D L) (dec L) ha j f σ φ
      (coef_ne_zero_of_weight_ne_zero D L f σ j φ hw) hselF
      (TheoremCBlock.Structured.envPriceR D L)
      (fun b => envIncR_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b)))
  refine (le_of_eq ?_).trans (hc.trans (le_of_eq ?_))
  · rfl
  · have e : ∑ φ : (∀ b, DensityFibre.HPiece D L b),
        choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
          ((∏ b, DensityFibre.bpieceG D L b (φ b)) * Real.sqrt Kf) =
        Real.sqrt Kf * ∑ φ : (∀ b, DensityFibre.HPiece D L b),
          choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
            ∏ b, DensityFibre.bpieceG D L b (φ b) := by
      rw [mul_sum]
      exact sum_congr rfl fun φ _ => by ring
    rw [e, Real.sqrt_mul hK' Kf]
    have hsq : Real.sqrt Kf * Real.sqrt Kf = Kf := Real.mul_self_sqrt hKf0
    generalize Real.sqrt Kf = r at hsq ⊢
    rw [← hsq]
    ring

/-- **The summed cross parts of `rchPTEnvR`, pointwise**: `∑_f ∑_{σ≠∅} ∑_j cross_j ≤
√((1 + u) Y) e^{T + U₀ + ∑_j (d_j + v_j)} ∑_j (√P₊(j) + √P₋(j))`. -/
theorem crossSum_envR_pt (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (hK' : 0 ≤ (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
      D.Y L A) :
    ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ j : D.FS.Tag, crossPTEnvR hcop D hpair dec C1 C71 σ' L A Jq ω f σ j ≤
    Real.sqrt ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
        D.Y L A) * Real.exp (D.ME.T + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) *
      ∑ j : D.FS.Tag,
        (Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldPlus) +
          Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldMinus)) := by
  set K' := (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
    D.Y L A with hK'def
  set X : D.FS.Tag → ℝ := fun j =>
    Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldPlus) +
      Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldMinus)
    with hXdef
  have hX0 : ∀ j, 0 ≤ X j := fun j => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc _ ≤ ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ j : D.FS.Tag, (Real.sqrt K' * X j) *
        ((∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)) *
          ∑ φ : (∀ b, DensityFibre.HPiece D L b),
            choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
              ∏ b, DensityFibre.bpieceG D L b (φ b)) :=
        sum_le_sum fun f _ => sum_le_sum fun σ _ => sum_le_sum fun j _ =>
          crossPTEnvR_le hcop D hpair dec ha hpar hsel C1 C71 σ' L A Jq ω f σ j hK'
    _ = ∑ j : D.FS.Tag, (Real.sqrt K' * X j) *
        ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ((∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)) *
            ∑ φ : (∀ b, DensityFibre.HPiece D L b),
              choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
                ∏ b, DensityFibre.bpieceG D L b (φ b)) := sum3_swap _ _ _
    _ ≤ ∑ j : D.FS.Tag, (Real.sqrt K' * X j) *
        Real.exp (D.ME.T + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) := by
        refine sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (Real.sqrt_nonneg _) (hX0 j))
        refine (weight_total_le D L j _
          (fun b => TheoremCBlock.Structured.envPriceR_nonneg D L b)).trans ?_
        exact prod_factor_le_exp _ _ _ (fun b => TheoremCBlock.Structured.envPriceR_nonneg D L b)
          (fun b => TheoremCBlock.Structured.uprice_nonneg D L b)
          (fun b => sum_nonneg fun i _ => add_nonneg
            (TheoremCBlock.Structured.dprice_nonneg D L b i)
            (TheoremCBlock.Structured.vprice_nonneg D L b i))
          (D.ME.TR_total L) (sum_uprice_le D L) (sum_s_le D L)
    _ = _ := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by ring

/-- **The cross sums of `RchSumPTEnvR` from `Y ≲ L^{2σ} α` and `E P_± ≤ C_P`**
(`lem:sharp-first`, the cross terms; `prop:record:density-structured`): `CrossSumPTEnvR` with
`c_X = √(2 C_dc C_Y) e^{T + U₀ + ∑_j (d_j + v_j)} · 2|𝔗| √C_P`. The two inputs are labelled:
`hY` (`Y ≤ C_Y L^{2/825} α` at counterexamples; the paper's Hölder bound `Y ≤ C_ε N^ε α`) and
`hP` (the means of the main prices of the folds, B9's local-density means). -/
theorem crossSumPTEnvR_of_bounds (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    {CY CP : ℝ} (hCY : 0 ≤ CY)
    (hY : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      D.Y L A ≤ CY * (L : ℝ) ^ (2 * Sarkozy.cancellationDecay) * density (blockScale * L) A))
    (hP : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ j : D.FS.Tag,
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldPlus)) ≤
        CP ∧
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldMinus)) ≤
        CP)) :
    CrossSumPTEnvR hcop D hpair dec (Real.sqrt (2 * cdc0 D * CY) *
      Real.exp (D.ME.T + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) *
      (2 * (Fintype.card D.FS.Tag : ℝ) * Real.sqrt CP)) := by
  unfold CrossSumPTEnvR
  have hu : ∀ᶠ L : ℕ in atTop,
      scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L < 1 :=
    (tendsto_order.1 (tendsto_scaleU_stage (M0 := modulus pr h) (Qcl := cliqueConstant m₀ D.S.ep)
      (by norm_num [blockScale]))).2 1 one_pos
  filter_upwards [hY, hP, hu, eventually_ge_atTop 1] with L hYL hPL huL hL1
  intro C hC hk A hA hYc
  have hYA := hYL C hC hk A hA hYc
  have hPA := hPL C hC hk A hA hYc
  have hY0 : 0 ≤ D.Y L A := (Param.counterexample_pos _ hC hYc).le
  have hu0 := scaleU_nonneg' blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) L
  have hK' : 0 ≤ (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
      D.Y L A := mul_nonneg (by linarith) hY0
  set ex := Real.exp (D.ME.T + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) with hex
  set K' := (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
    D.Y L A with hK'def
  set Cr := crDC D C1₀ C71₀ sigmaR L A with hCr
  have hpt : ∀ Jq ω, (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
      σ ≠ fun _ => none), ∑ j : D.FS.Tag, Real.sqrt Cr *
        crossPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j) ≤
      Real.sqrt Cr * (Real.sqrt K' * ex * ∑ j : D.FS.Tag,
        (Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldPlus) +
          Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω
            (D.FS.cut j).foldMinus))) := by
    intro Jq ω
    simp_rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left
      (crossSum_envR_pt hcop D hpair dec ha hpar hsel C1₀ C71₀ sigmaR L A Jq ω hK')
      (Real.sqrt_nonneg _)
  refine ((queryLaw D.index.C D.index.t).expect_mono fun Jq =>
    (FiniteLaw.uniform _).expect_mono fun ω => hpt Jq ω).trans ?_
  simp only [FiniteLaw.expect_const_mul, FiniteLaw.expect_sum, FiniteLaw.expect_add]
  have hj : ∀ j : D.FS.Tag,
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω
            (D.FS.cut j).foldPlus))) +
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => Real.sqrt (envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω
            (D.FS.cut j).foldMinus))) ≤ 2 * Real.sqrt CP := by
    intro j
    have h1 := expect2_sqrt_le (queryLaw D.index.C D.index.t)
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j))
      (fun Jq ω => envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldPlus)
      (fun Jq ω => envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.w L A Jq ω _)
    have h2 := expect2_sqrt_le (queryLaw D.index.C D.index.t)
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j))
      (fun Jq ω => envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldMinus)
      (fun Jq ω => envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.w L A Jq ω _)
    have h3 := Real.sqrt_le_sqrt (hPA j).1
    have h4 := Real.sqrt_le_sqrt (hPA j).2
    linarith
  have hsum := sum_le_sum fun j (_ : j ∈ (univ : Finset D.FS.Tag)) => hj j
  rw [sum_const, card_univ, nsmul_eq_mul] at hsum
  have hc := sqrt_cross_const_le (Cd := cdc0 D) (CY := CY) (u := scaleU blockScale (modulus pr h)
    (cliqueConstant m₀ D.S.ep) stageTau L) (σ := Sarkozy.cancellationDecay) hL1 (cdc0_nonneg D)
    hCY huL.le hY0 (density_nonneg _ _) hYA
  rw [← crDC_eq] at hc
  have hex0 : 0 ≤ ex := Real.exp_nonneg _
  have hsc : 0 ≤ Real.sqrt Cr * (Real.sqrt K' * ex) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hex0)
  calc Real.sqrt Cr * (Real.sqrt K' * ex * ∑ j : D.FS.Tag, _)
      ≤ Real.sqrt Cr *
          (Real.sqrt K' * ex * ((Fintype.card D.FS.Tag : ℝ) * (2 * Real.sqrt CP))) := by
        have hm := mul_le_mul_of_nonneg_left hsum hsc
        exact le_trans (le_of_eq (by ring)) (hm.trans (le_of_eq (by ring)))
    _ = (Real.sqrt Cr * Real.sqrt K') *
          (ex * (2 * (Fintype.card D.FS.Tag : ℝ) * Real.sqrt CP)) := by
        ring
    _ ≤ (Real.sqrt (2 * cdc0 D * CY) * (L : ℝ) ^ (-Sarkozy.cancellationDecay) *
          density (blockScale * L) A) * (ex * (2 * (Fintype.card D.FS.Tag : ℝ) * Real.sqrt CP)) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg hex0 (mul_nonneg (by positivity)
          (Real.sqrt_nonneg _)))
    _ = _ := by ring

/-- **One cross part of `rchPTFixL`** (`lem:sharp-first`): with DC3's piece prices
(`uQ = wrapPrice`), `cross_j ≤ √((1 + u) Y) (√P₊ + √P₋) ∏_f π · ∑_φ w_φ BG(φ)`. -/
theorem crossPTFixL_le (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (hK' : 0 ≤ (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
      D.Y L A) :
    crossPTFixL hcop D hpair dec C1 C71 σ' L A S Jq ω f σ j ≤
      Real.sqrt ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
        D.Y L A) *
        (Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldPlus) +
          Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldMinus)) *
        ((∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) *
          ∑ φ : (∀ b, DensityFibre.HPiece D L b),
            choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
              ∏ b, DensityFibre.bpieceG D L b (φ b)) := by
  have hselF := hselF_of_parity D (prefix_pairwise (hpair 0)) hpar hsel L
  unfold crossPTFixL rchCross
  set Kf := ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) with hKf
  have hKf0 : 0 ≤ Kf := prod_nonneg fun b _ => by
    split_ifs
    · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
    · exact zero_le_one
  set K' := (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
    D.Y L A with hK'def
  have hK0 : 0 ≤ K' * Kf := mul_nonneg hK' hKf0
  have hc := crossPart_le (smallPiece m₀ blk D L) hK0
    (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.u L A S 0 Jq ω
      (D.FS.cut j).foldPlus)
    (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.u L A S 0 Jq ω
      (D.FS.cut j).foldMinus)
    (fun φ => choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ)
    (fun φ => ∏ b, DensityFibre.bpieceG D L b (φ b))
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun _ => Kf) (fun φ => choiceWeight_nonneg' D L f σ j φ)
    (fun φ => prod_nonneg fun b _ => DensityFibre.bpieceG_nonneg D L b (φ b)) (fun _ => hKf0)
    (fun φ hw => piecePrice_plus_le_one D L (hpair L) (TheoremCBlock.Structured.wrapInc D L)
      (isPositiveRecord_wrapInc D L) (dec L) ha j f σ φ
      (coef_ne_zero_of_weight_ne_zero D L f σ j φ hw) hselF
      (TheoremCBlock.Structured.wrapPrice D L)
      (fun b => wrapInc_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b)))
    (fun φ hw => piecePrice_minus_le_one D L (hpair L) (TheoremCBlock.Structured.wrapInc D L)
      (isPositiveRecord_wrapInc D L) (dec L) ha j f σ φ
      (coef_ne_zero_of_weight_ne_zero D L f σ j φ hw) hselF
      (TheoremCBlock.Structured.wrapPrice D L)
      (fun b => wrapInc_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b)))
  refine (le_of_eq ?_).trans (hc.trans (le_of_eq ?_))
  · rfl
  · have e : ∑ φ : (∀ b, DensityFibre.HPiece D L b),
        choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
          ((∏ b, DensityFibre.bpieceG D L b (φ b)) * Real.sqrt Kf) =
        Real.sqrt Kf * ∑ φ : (∀ b, DensityFibre.HPiece D L b),
          choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
            ∏ b, DensityFibre.bpieceG D L b (φ b) := by
      rw [mul_sum]
      exact sum_congr rfl fun φ _ => by ring
    rw [e, Real.sqrt_mul hK' Kf]
    have hsq : Real.sqrt Kf * Real.sqrt Kf = Kf := Real.mul_self_sqrt hKf0
    generalize Real.sqrt Kf = r at hsq ⊢
    rw [← hsq]
    ring

/-- **The summed cross parts of `rchPTFixL`, pointwise**: `∑_f ∑_{σ≠∅} ∑_j cross_j ≤
√((1 + u) Y) e^{S + A + U₀ + ∑_j (d_j + v_j)} ∑_j (√P₊(j) + √P₋(j))`. -/
theorem crossSum_fixL_pt (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (hK' : 0 ≤ (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
      D.Y L A) :
    ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ j : D.FS.Tag, crossPTFixL hcop D hpair dec C1 C71 σ' L A S Jq ω f σ j ≤
    Real.sqrt ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
        D.Y L A) * Real.exp (D.CL.S + D.CL.A + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) *
      ∑ j : D.FS.Tag,
        (Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldPlus) +
          Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω
            (D.FS.cut j).foldMinus)) := by
  set K' := (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
    D.Y L A with hK'def
  set X : D.FS.Tag → ℝ := fun j =>
    Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldPlus) +
      Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldMinus)
    with hXdef
  have hX0 : ∀ j, 0 ≤ X j := fun j => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc _ ≤ ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ j : D.FS.Tag, (Real.sqrt K' * X j) *
        ((∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) *
          ∑ φ : (∀ b, DensityFibre.HPiece D L b),
            choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
              ∏ b, DensityFibre.bpieceG D L b (φ b)) :=
        sum_le_sum fun f _ => sum_le_sum fun σ _ => sum_le_sum fun j _ =>
          crossPTFixL_le hcop D hpair dec ha hpar hsel C1 C71 σ' L A S Jq ω f σ j hK'
    _ = ∑ j : D.FS.Tag, (Real.sqrt K' * X j) *
        ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ((∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) *
            ∑ φ : (∀ b, DensityFibre.HPiece D L b),
              choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
                ∏ b, DensityFibre.bpieceG D L b (φ b)) := sum3_swap _ _ _
    _ ≤ ∑ j : D.FS.Tag, (Real.sqrt K' * X j) *
        Real.exp (D.CL.S + D.CL.A + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) := by
        refine sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (Real.sqrt_nonneg _) (hX0 j))
        refine (weight_total_le D L j _
          (fun b => TheoremCBlock.Structured.wrapPrice_nonneg D L b)).trans ?_
        exact prod_factor_le_exp _ _ _ (fun b => TheoremCBlock.Structured.wrapPrice_nonneg D L b)
          (fun b => TheoremCBlock.Structured.uprice_nonneg D L b)
          (fun b => sum_nonneg fun i _ => add_nonneg
            (TheoremCBlock.Structured.dprice_nonneg D L b i)
            (TheoremCBlock.Structured.vprice_nonneg D L b i))
          (D.wrapEnvelope_price L) (sum_uprice_le D L) (sum_s_le D L)
    _ = _ := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by ring

/-- **The cross sums of `RchSumPTFixL` from `Y ≲ L^{2σ} α` and `E P_± ≤ C_P`**
(`lem:sharp-first`, the cross terms; `prop:record:density-structured`): `CrossSumPTFixL` with
`c_X = √(2 C_dc C_Y) e^{S + A + U₀ + ∑_j (d_j + v_j)} · 2|𝔗| √C_P`. The two inputs are labelled:
`hY` (`Y ≤ C_Y L^{2/825} α` at counterexamples; the paper's Hölder bound `Y ≤ C_ε N^ε α`) and
`hP` (the means of the main prices of the folds, B9's local-density means). -/
theorem crossSumPTFixL_of_bounds (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    {CY CP : ℝ} (hCY : 0 ≤ CY)
    (hY : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      D.Y L A ≤ CY * (L : ℝ) ^ (2 * Sarkozy.cancellationDecay) * density (blockScale * L) A))
    (hP : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ S : Finset E, S ≠ ∅ → ∀ j : D.FS.Tag,
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldPlus)) ≤
        CP ∧
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldMinus)) ≤
        CP)) :
    CrossSumPTFixL hcop D hpair dec (Real.sqrt (2 * cdc0 D * CY) *
      Real.exp (D.CL.S + D.CL.A + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) *
      (2 * (Fintype.card D.FS.Tag : ℝ) * Real.sqrt CP)) := by
  unfold CrossSumPTFixL
  have hu : ∀ᶠ L : ℕ in atTop,
      scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L < 1 :=
    (tendsto_order.1 (tendsto_scaleU_stage (M0 := modulus pr h) (Qcl := cliqueConstant m₀ D.S.ep)
      (by norm_num [blockScale]))).2 1 one_pos
  filter_upwards [hY, hP, hu, eventually_ge_atTop 1] with L hYL hPL huL hL1
  intro C hC hk A hA hYc S hS
  have hYA := hYL C hC hk A hA hYc
  have hPA := hPL C hC hk A hA hYc S hS
  have hY0 : 0 ≤ D.Y L A := (Param.counterexample_pos _ hC hYc).le
  have hu0 := scaleU_nonneg' blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) L
  have hK' : 0 ≤ (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
      D.Y L A := mul_nonneg (by linarith) hY0
  set ex := Real.exp (D.CL.S + D.CL.A + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) with hex
  set K' := (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
    D.Y L A with hK'def
  set Cr := crDC D C1₀ C71₀ sigmaR L A with hCr
  have hpt : ∀ Jq ω, (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
      σ ≠ fun _ => none), ∑ j : D.FS.Tag, Real.sqrt Cr *
        crossPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j) ≤
      Real.sqrt Cr * (Real.sqrt K' * ex * ∑ j : D.FS.Tag,
        (Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldPlus) +
          Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω
            (D.FS.cut j).foldMinus))) := by
    intro Jq ω
    simp_rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left
      (crossSum_fixL_pt hcop D hpair dec ha hpar hsel C1₀ C71₀ sigmaR L A S Jq ω hK')
      (Real.sqrt_nonneg _)
  refine ((queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect_mono fun Jq =>
    (FiniteLaw.uniform _).expect_mono fun ω => hpt Jq ω).trans ?_
  simp only [FiniteLaw.expect_const_mul, FiniteLaw.expect_sum, FiniteLaw.expect_add]
  have hj : ∀ j : D.FS.Tag,
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω
            (D.FS.cut j).foldPlus))) +
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω
            (D.FS.cut j).foldMinus))) ≤ 2 * Real.sqrt CP := by
    intro j
    have h1 := expect2_sqrt_le (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e)))
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j))
      (fun Jq ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldPlus)
      (fun Jq ω => fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.u L A S 0 Jq ω _)
    have h2 := expect2_sqrt_le (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e)))
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j))
      (fun Jq ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldMinus)
      (fun Jq ω => fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.u L A S 0 Jq ω _)
    have h3 := Real.sqrt_le_sqrt (hPA j).1
    have h4 := Real.sqrt_le_sqrt (hPA j).2
    linarith
  have hsum := sum_le_sum fun j (_ : j ∈ (univ : Finset D.FS.Tag)) => hj j
  rw [sum_const, card_univ, nsmul_eq_mul] at hsum
  have hc := sqrt_cross_const_le (Cd := cdc0 D) (CY := CY) (u := scaleU blockScale (modulus pr h)
    (cliqueConstant m₀ D.S.ep) stageTau L) (σ := Sarkozy.cancellationDecay) hL1 (cdc0_nonneg D)
    hCY huL.le hY0 (density_nonneg _ _) hYA
  rw [← crDC_eq] at hc
  have hex0 : 0 ≤ ex := Real.exp_nonneg _
  have hsc : 0 ≤ Real.sqrt Cr * (Real.sqrt K' * ex) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hex0)
  calc Real.sqrt Cr * (Real.sqrt K' * ex * ∑ j : D.FS.Tag, _)
      ≤ Real.sqrt Cr *
          (Real.sqrt K' * ex * ((Fintype.card D.FS.Tag : ℝ) * (2 * Real.sqrt CP))) := by
        have hm := mul_le_mul_of_nonneg_left hsum hsc
        exact le_trans (le_of_eq (by ring)) (hm.trans (le_of_eq (by ring)))
    _ = (Real.sqrt Cr * Real.sqrt K') *
          (ex * (2 * (Fintype.card D.FS.Tag : ℝ) * Real.sqrt CP)) := by
        ring
    _ ≤ (Real.sqrt (2 * cdc0 D * CY) * (L : ℝ) ^ (-Sarkozy.cancellationDecay) *
          density (blockScale * L) A) * (ex * (2 * (Fintype.card D.FS.Tag : ℝ) * Real.sqrt CP)) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg hex0 (mul_nonneg (by positivity)
          (Real.sqrt_nonneg _)))
    _ = _ := by ring

/-- **One cross part of `rchPTFixR`** (`lem:sharp-first`): with DC3's piece prices
(`uQ = wrapPrice`), `cross_j ≤ √((1 + u) Y) (√P₊ + √P₋) ∏_f π · ∑_φ w_φ BG(φ)`. -/
theorem crossPTFixR_le (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (hK' : 0 ≤ (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
      D.Y L A) :
    crossPTFixR hcop D hpair dec C1 C71 σ' L A S Jq ω f σ j ≤
      Real.sqrt ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
        D.Y L A) *
        (Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldPlus) +
          Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldMinus)) *
        ((∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) *
          ∑ φ : (∀ b, DensityFibre.HPiece D L b),
            choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
              ∏ b, DensityFibre.bpieceG D L b (φ b)) := by
  have hselF := hselF_of_parity D (prefix_pairwise (hpair 0)) hpar hsel L
  unfold crossPTFixR rchCross
  set Kf := ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) with hKf
  have hKf0 : 0 ≤ Kf := prod_nonneg fun b _ => by
    split_ifs
    · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
    · exact zero_le_one
  set K' := (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
    D.Y L A with hK'def
  have hK0 : 0 ≤ K' * Kf := mul_nonneg hK' hKf0
  have hc := crossPart_le (smallPiece m₀ blk D L) hK0
    (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.w L A S 1 Jq ω
      (D.FS.cut j).foldPlus)
    (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.w L A S 1 Jq ω
      (D.FS.cut j).foldMinus)
    (fun φ => choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ)
    (fun φ => ∏ b, DensityFibre.bpieceG D L b (φ b))
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun _ => Kf) (fun φ => choiceWeight_nonneg' D L f σ j φ)
    (fun φ => prod_nonneg fun b _ => DensityFibre.bpieceG_nonneg D L b (φ b)) (fun _ => hKf0)
    (fun φ hw => piecePrice_plus_le_one D L (hpair L) (TheoremCBlock.Structured.wrapInc D L)
      (isPositiveRecord_wrapInc D L) (dec L) ha j f σ φ
      (coef_ne_zero_of_weight_ne_zero D L f σ j φ hw) hselF
      (TheoremCBlock.Structured.wrapPrice D L)
      (fun b => wrapInc_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b)))
    (fun φ hw => piecePrice_minus_le_one D L (hpair L) (TheoremCBlock.Structured.wrapInc D L)
      (isPositiveRecord_wrapInc D L) (dec L) ha j f σ φ
      (coef_ne_zero_of_weight_ne_zero D L f σ j φ hw) hselF
      (TheoremCBlock.Structured.wrapPrice D L)
      (fun b => wrapInc_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b)))
  refine (le_of_eq ?_).trans (hc.trans (le_of_eq ?_))
  · rfl
  · have e : ∑ φ : (∀ b, DensityFibre.HPiece D L b),
        choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
          ((∏ b, DensityFibre.bpieceG D L b (φ b)) * Real.sqrt Kf) =
        Real.sqrt Kf * ∑ φ : (∀ b, DensityFibre.HPiece D L b),
          choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
            ∏ b, DensityFibre.bpieceG D L b (φ b) := by
      rw [mul_sum]
      exact sum_congr rfl fun φ _ => by ring
    rw [e, Real.sqrt_mul hK' Kf]
    have hsq : Real.sqrt Kf * Real.sqrt Kf = Kf := Real.mul_self_sqrt hKf0
    generalize Real.sqrt Kf = r at hsq ⊢
    rw [← hsq]
    ring

/-- **The summed cross parts of `rchPTFixR`, pointwise**: `∑_f ∑_{σ≠∅} ∑_j cross_j ≤
√((1 + u) Y) e^{S + A + U₀ + ∑_j (d_j + v_j)} ∑_j (√P₊(j) + √P₋(j))`. -/
theorem crossSum_fixR_pt (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (hK' : 0 ≤ (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
      D.Y L A) :
    ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ j : D.FS.Tag, crossPTFixR hcop D hpair dec C1 C71 σ' L A S Jq ω f σ j ≤
    Real.sqrt ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
        D.Y L A) * Real.exp (D.CL.S + D.CL.A + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) *
      ∑ j : D.FS.Tag,
        (Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldPlus) +
          Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω
            (D.FS.cut j).foldMinus)) := by
  set K' := (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
    D.Y L A with hK'def
  set X : D.FS.Tag → ℝ := fun j =>
    Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldPlus) +
      Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldMinus)
    with hXdef
  have hX0 : ∀ j, 0 ≤ X j := fun j => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc _ ≤ ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ j : D.FS.Tag, (Real.sqrt K' * X j) *
        ((∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) *
          ∑ φ : (∀ b, DensityFibre.HPiece D L b),
            choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
              ∏ b, DensityFibre.bpieceG D L b (φ b)) :=
        sum_le_sum fun f _ => sum_le_sum fun σ _ => sum_le_sum fun j _ =>
          crossPTFixR_le hcop D hpair dec ha hpar hsel C1 C71 σ' L A S Jq ω f σ j hK'
    _ = ∑ j : D.FS.Tag, (Real.sqrt K' * X j) *
        ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ((∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) *
            ∑ φ : (∀ b, DensityFibre.HPiece D L b),
              choiceWeight (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ *
                ∏ b, DensityFibre.bpieceG D L b (φ b)) := sum3_swap _ _ _
    _ ≤ ∑ j : D.FS.Tag, (Real.sqrt K' * X j) *
        Real.exp (D.CL.S + D.CL.A + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) := by
        refine sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (Real.sqrt_nonneg _) (hX0 j))
        refine (weight_total_le D L j _
          (fun b => TheoremCBlock.Structured.wrapPrice_nonneg D L b)).trans ?_
        exact prod_factor_le_exp _ _ _ (fun b => TheoremCBlock.Structured.wrapPrice_nonneg D L b)
          (fun b => TheoremCBlock.Structured.uprice_nonneg D L b)
          (fun b => sum_nonneg fun i _ => add_nonneg
            (TheoremCBlock.Structured.dprice_nonneg D L b i)
            (TheoremCBlock.Structured.vprice_nonneg D L b i))
          (D.wrapEnvelope_price L) (sum_uprice_le D L) (sum_s_le D L)
    _ = _ := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by ring

/-- **The cross sums of `RchSumPTFixR` from `Y ≲ L^{2σ} α` and `E P_± ≤ C_P`**
(`lem:sharp-first`, the cross terms; `prop:record:density-structured`): `CrossSumPTFixR` with
`c_X = √(2 C_dc C_Y) e^{S + A + U₀ + ∑_j (d_j + v_j)} · 2|𝔗| √C_P`. The two inputs are labelled:
`hY` (`Y ≤ C_Y L^{2/825} α` at counterexamples; the paper's Hölder bound `Y ≤ C_ε N^ε α`) and
`hP` (the means of the main prices of the folds, B9's local-density means). -/
theorem crossSumPTFixR_of_bounds (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    {CY CP : ℝ} (hCY : 0 ≤ CY)
    (hY : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      D.Y L A ≤ CY * (L : ℝ) ^ (2 * Sarkozy.cancellationDecay) * density (blockScale * L) A))
    (hP : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ S : Finset E, S ≠ ∅ → ∀ j : D.FS.Tag,
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldPlus)) ≤
        CP ∧
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldMinus)) ≤
        CP)) :
    CrossSumPTFixR hcop D hpair dec (Real.sqrt (2 * cdc0 D * CY) *
      Real.exp (D.CL.S + D.CL.A + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) *
      (2 * (Fintype.card D.FS.Tag : ℝ) * Real.sqrt CP)) := by
  unfold CrossSumPTFixR
  have hu : ∀ᶠ L : ℕ in atTop,
      scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L < 1 :=
    (tendsto_order.1 (tendsto_scaleU_stage (M0 := modulus pr h) (Qcl := cliqueConstant m₀ D.S.ep)
      (by norm_num [blockScale]))).2 1 one_pos
  filter_upwards [hY, hP, hu, eventually_ge_atTop 1] with L hYL hPL huL hL1
  intro C hC hk A hA hYc S hS
  have hYA := hYL C hC hk A hA hYc
  have hPA := hPL C hC hk A hA hYc S hS
  have hY0 : 0 ≤ D.Y L A := (Param.counterexample_pos _ hC hYc).le
  have hu0 := scaleU_nonneg' blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) L
  have hK' : 0 ≤ (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
      D.Y L A := mul_nonneg (by linarith) hY0
  set ex := Real.exp (D.CL.S + D.CL.A + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) with hex
  set K' := (1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
    D.Y L A with hK'def
  set Cr := crDC D C1₀ C71₀ sigmaR L A with hCr
  have hpt : ∀ Jq ω, (∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
      σ ≠ fun _ => none), ∑ j : D.FS.Tag, Real.sqrt Cr *
        crossPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j) ≤
      Real.sqrt Cr * (Real.sqrt K' * ex * ∑ j : D.FS.Tag,
        (Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldPlus) +
          Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω
            (D.FS.cut j).foldMinus))) := by
    intro Jq ω
    simp_rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left
      (crossSum_fixR_pt hcop D hpair dec ha hpar hsel C1₀ C71₀ sigmaR L A S Jq ω hK')
      (Real.sqrt_nonneg _)
  refine ((queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect_mono fun Jq =>
    (FiniteLaw.uniform _).expect_mono fun ω => hpt Jq ω).trans ?_
  simp only [FiniteLaw.expect_const_mul, FiniteLaw.expect_sum, FiniteLaw.expect_add]
  have hj : ∀ j : D.FS.Tag,
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω
            (D.FS.cut j).foldPlus))) +
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => Real.sqrt (fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω
            (D.FS.cut j).foldMinus))) ≤ 2 * Real.sqrt CP := by
    intro j
    have h1 := expect2_sqrt_le (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e)))
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j))
      (fun Jq ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldPlus)
      (fun Jq ω => fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.w L A S 1 Jq ω _)
    have h2 := expect2_sqrt_le (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e)))
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j))
      (fun Jq ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldMinus)
      (fun Jq ω => fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.w L A S 1 Jq ω _)
    have h3 := Real.sqrt_le_sqrt (hPA j).1
    have h4 := Real.sqrt_le_sqrt (hPA j).2
    linarith
  have hsum := sum_le_sum fun j (_ : j ∈ (univ : Finset D.FS.Tag)) => hj j
  rw [sum_const, card_univ, nsmul_eq_mul] at hsum
  have hc := sqrt_cross_const_le (Cd := cdc0 D) (CY := CY) (u := scaleU blockScale (modulus pr h)
    (cliqueConstant m₀ D.S.ep) stageTau L) (σ := Sarkozy.cancellationDecay) hL1 (cdc0_nonneg D)
    hCY huL.le hY0 (density_nonneg _ _) hYA
  rw [← crDC_eq] at hc
  have hex0 : 0 ≤ ex := Real.exp_nonneg _
  have hsc : 0 ≤ Real.sqrt Cr * (Real.sqrt K' * ex) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hex0)
  calc Real.sqrt Cr * (Real.sqrt K' * ex * ∑ j : D.FS.Tag, _)
      ≤ Real.sqrt Cr *
          (Real.sqrt K' * ex * ((Fintype.card D.FS.Tag : ℝ) * (2 * Real.sqrt CP))) := by
        have hm := mul_le_mul_of_nonneg_left hsum hsc
        exact le_trans (le_of_eq (by ring)) (hm.trans (le_of_eq (by ring)))
    _ = (Real.sqrt Cr * Real.sqrt K') *
          (ex * (2 * (Fintype.card D.FS.Tag : ℝ) * Real.sqrt CP)) := by
        ring
    _ ≤ (Real.sqrt (2 * cdc0 D * CY) * (L : ℝ) ^ (-Sarkozy.cancellationDecay) *
          density (blockScale * L) A) * (ex * (2 * (Fintype.card D.FS.Tag : ℝ) * Real.sqrt CP)) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg hex0 (mul_nonneg (by positivity)
          (Real.sqrt_nonneg _)))
    _ = _ := by ring

end Sarkozy.SharpSums
