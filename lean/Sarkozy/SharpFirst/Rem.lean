module

public import Sarkozy.SharpFirst.Chain
public import Sarkozy.Companion.Kinds
public import Sarkozy.LargeSums.Fix

@[expose] public section

/-!
# `SF.hfold` and `SF.hrem` of `lem:sharp-first`, with constructed `ε`, `rp`, `rm`, `c`

SR (8 November 2026). TH's two open fields of the baseline route of `lem:sharp-first`
(`Companion.SFFold`, `Companion.SFRem`) are joint: `hfold` bounds each folded energy `𝔈_±(f)` of a
whole-difference piece by `(∏ g)(1 + ε)Y + r_±(f)`, and `hrem` sums the remainders `r_±`. Here the
data are **constructed**, following the paper's proof of `lem:sharp-first`:

* `ε = u_L` (`sfEps`, the scale term of `lem:scale-conditions` at `M₀ = modulus`, `Q_cl = Q_cl⁰`);
* `r_±(f) = max(0, 𝔈_±(f) − (∏ g)(1 + ε)Y)` (`sfRp`, `sfRm`), the excess of each folded energy
  over its main term. Then **`sfFold_proved`** is immediate, and all the content is in the
  summation;
* **`sfRem_proved`**: there is `c ≥ 0` with `SFRem D c rp rm`, for every comparison datum on the
  paper's tails with `a ≥ 0`, the parity condition, `blockSel ≤ selPre` and nonempty blocks.

The proof of `sfRem_proved` is the paper's:
* a piece `f` with `q_E ≤ N^τ` (`wSmall`): `prop:record:density-structured` once per folded
  energy (`whole_chain`) gives `𝔈_±(f) ≤ m(f)((1 + u) sq(D_E)^a Y + C_dc L^{-1/825} α)`, and the
  price bookkeeping `m(f) sq(D_E)^a ≤ ∏ g` (`wPrice_le`) leaves the excess
  `≤ m(f) C_dc L^{-1/825} α` (`excess_le`);
* a piece with `q_E > N^τ`: the excess is at most `|𝔈_±(f)| ≤ m(f) B` (`whole_holder`), and these
  terms form the large-product remainder of `lem:record:density-lp`: Rankin over the large pieces
  (`large_of_not_wSmall`, `sum_large_pieces_le`), `Π_H ≤ e^{D.SM.bound}` (`prod_wPr_le_exp`)
  and (S4) (`lp_decay_le`);
* the sums over the choices `σ`, `j` (`sum_choices_le`).
The constant is `c = |𝔗| (C_dc + M₀^{72} |X₀|^{72} C_ε K) e^{D.SM.bound}`.
-/

namespace Sarkozy.SharpFirst

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.DensityFibre Sarkozy.ThetaOne Sarkozy.LargeSums Sarkozy.EnvelopeInputsBlock
  Sarkozy.RecordExpansion
open Sarkozy.Param (Params)
open Sarkozy.Companion (SFR SFFold SFRem)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Data

variable {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

/-- **The relative error of `SF`**: the scale term `u_L` of `lem:scale-conditions` at
`M₀ = modulus`, `Q_cl = Q_cl⁰` (DC3's `ε_L`). -/
noncomputable def sfEps : ℕ → ℝ :=
  scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau

omit [DecidableEq P] in
theorem sfEps_nonneg (L : ℕ) : 0 ≤ sfEps D L := scaleU_nonneg _ _ _ _ _

omit [DecidableEq P] in
theorem tendsto_sfEps : Tendsto (sfEps D) atTop (𝓝 0) :=
  tendsto_scaleU_stage (by norm_num [blockScale])

variable (dec : ∀ L, DecFamily D L)

/-- **The remainders of the plus folded energies**: the excess over the main term. -/
noncomputable def sfRp : SFR D := fun L A _ j f =>
  max 0 (foldedPlus (D.FS.cut j) (wpieceLp (dec L) j) (fun _ => blockLift m₀ blk p L A) f -
    (∏ b, wpieceG D L b (f b)) * ((1 + sfEps D L) * D.Y L A))

/-- **The remainders of the minus folded energies**: the excess over the main term. -/
noncomputable def sfRm : SFR D := fun L A _ j f =>
  max 0 (foldedMinus (D.FS.cut j) (wpieceLm (dec L) j) (fun _ => blockLift m₀ blk p L A) f -
    (∏ b, wpieceG D L b (f b)) * ((1 + sfEps D L) * D.Y L A))

omit [DecidableEq P] in
theorem sfRpm_nonneg : ∀ L A σ j f, 0 ≤ sfRp D dec L A σ j f ∧ 0 ≤ sfRm D dec L A σ j f :=
  fun _ _ _ _ _ => ⟨le_max_left _ _, le_max_left _ _⟩

omit [DecidableEq P] in
/-- **`SF.hfold` at the constructed data** (immediate: the remainders are the excesses). -/
theorem sfFold_proved : SFFold D dec (sfEps D) (sfRp D dec) (sfRm D dec) := by
  unfold SFFold
  refine Param.AtCounterexamples.of_forall _ fun L A σ _ j _ f => ⟨?_, ?_⟩
  · exact le_add_of_sub_left_le (le_max_right _ _)
  · exact le_add_of_sub_left_le (le_max_right _ _)

end Data

section Paper

variable (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)

/-- **A small piece** (`def:record:structured-energy`(a) with `q_E ≤ N^τ`): the modulus
conditions of DC1's chain on the selected atoms `E` of the piece. -/
def wSmall (L : ℕ) (f : ∀ b, WPiece D L b) : Prop :=
  ∃ qE cE : ℕ, ∏ b ∈ wAtoms D L f, crtModuli m₀ blk paperTail L b = qE * cE ∧
    Squarefree qE ∧ IsSquare cE ∧ cE ≠ 0 ∧ cE ≤ cliqueConstant m₀ D.S.ep ∧ qE.Coprime cE ∧
    (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau

omit [DecidableEq P] in
/-- **A piece that is not small is large** (DC1's `moduli_dichotomy` through DC3's
`moduli_paper`): `N^τ < ∏_𝔟 qf_𝔟(f_𝔟)`. -/
theorem large_of_not_wSmall
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hpar : ParityCondition D.S.ep) (L : ℕ) (f : ∀ b, WPiece D L b) (hf : ¬ wSmall D L f) :
    ((blockScale * L : ℕ) : ℝ) ^ stageTau < ∏ b, wqf D L (atomQR D L) b (f b) := by
  rcases moduli_paper D hpair hpar le_rfl L (((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (wAtoms D L f) with hs | hl
  · exact absurd hs hf
  · refine hl.trans_le (le_of_eq (prod_congr rfl fun b _ => ?_))
    unfold wqf atomQR wAtoms
    cases hb : wIsMu D L b (f b) <;> simp [hb]

omit [DecidableEq P] in
/-- **The price bookkeeping** (`lem:sharp-first`: "the geometric mean retains `Π(T')`"):
`m(f) sq(D_E)^a ≤ ∏_𝔟 g_𝔟(f_𝔟)`, from `sq(D_𝔟)^a ≤ sel_𝔟` (DC3's `hselF_of_parity`). -/
theorem wPrice_le
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (L : ℕ) (f : ∀ b, WPiece D L b) :
    (∏ b, wMass D L b (f b)) *
        ((leastSquare (∏ b ∈ wAtoms D L f, crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a ≤
      ∏ b, wpieceG D L b (f b) := by
  have hsq : ((leastSquare (∏ b ∈ wAtoms D L f, crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a =
      ∏ b ∈ wAtoms D L f, ((leastSquare (crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a := by
    rw [leastSquare_prod_coprime (crtModuli m₀ blk paperTail L) (crtModuli_pairwise blk (hpair L)),
      Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _)]
  rw [hsq]
  unfold wAtoms
  rw [prod_filter, ← prod_mul_distrib]
  refine prod_le_prod₀ (fun b _ => mul_nonneg (wMass_nonneg D L b (f b)) ?_) fun b _ => ?_
  · split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · exact zero_le_one
  · cases hb : wIsMu D L b (f b)
    · simp only [↓reduceIte]
      exact wMass_mul_le_wpieceG b (f b) hb
        (hselF_of_parity D (prefix_pairwise (hpair L)) hpar hsel L b)
    · simp only [Bool.true_eq_false, ↓reduceIte, mul_one]
      rw [wMass_of_mu b (f b) hb, wpieceG_of_mu b (f b) hb]

omit [DecidableEq P] in
/-- The masses of the selected folded laws are the mass of the piece. -/
theorem prod_mass_wAtoms (L : ℕ)
    (Λf : ∀ b, WPiece D L b → TheoremCBlock.AtomMeasure m₀ blk paperTail L b)
    (hΛm : ∀ b x, mass (Λf b x) = wMass D L b x) (f : ∀ b, WPiece D L b) :
    ∏ b ∈ wAtoms D L f, mass (Λf b (f b)) = ∏ b, wMass D L b (f b) := by
  unfold wAtoms
  rw [prod_filter]
  refine prod_congr rfl fun b _ => ?_
  cases hb : wIsMu D L b (f b)
  · simp only [↓reduceIte, hΛm]
  · simp only [Bool.true_eq_false, ↓reduceIte]
    rw [wMass_of_mu b (f b) hb]

omit [DecidableEq P] in
/-- A choice of pieces with nonzero weight at a nonempty choice `σ` selects some atom. -/
theorem wAtoms_nonempty {L : ℕ} (σ : ∀ b, Option (D.FS.Ib L b)) (hσ : σ ≠ fun _ => none)
    (j : D.FS.Tag) (f : ∀ b, WPiece D L b)
    (hw : choiceWeight (wpieceCoef σ j) (wpieceD D L) f ≠ 0) : (wAtoms D L f).Nonempty := by
  obtain ⟨b, hb⟩ : ∃ b, σ b ≠ none := by
    by_contra hc
    exact hσ (funext fun b => by
      by_contra hb
      exact hc ⟨b, hb⟩)
  refine ⟨b, ?_⟩
  simp only [wAtoms, mem_filter, mem_univ, true_and]
  by_contra hmu
  apply hw
  unfold choiceWeight
  refine prod_eq_zero (mem_univ b) ?_
  have hc : wpieceCoef σ j b (f b) = 0 := by
    revert hmu
    rcases f b with (_ | hh) | ⟨i, _ | t⟩ <;> intro hmu <;> simp_all [wIsMu, wpieceCoef]
  rw [hc, abs_zero, zero_mul]

omit [DecidableEq P] in
/-- **The excess of one folded energy over its main term** (see the module docstring): at most
`m(f) (C_dc L^{-σ} α + [f not small] B)`. -/
theorem excess_le {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71) (hC1 : 0 ≤ C1) (hC71 : 0 ≤ C71)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β) (hne : ∀ β, ∃ i, blk i = β)
    {C0 : ℝ} {L : ℕ} {A : Finset ℤ} (hcex : IsLeastCounterexample D.Y a densityExponent C0 L A)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) {M0 Qpre N0 N0' : ℕ}
    (hsc : ScaleConditionsAt blockScale M0 (cliqueConstant m₀ D.S.ep) Qpre N0 N0' L)
    (hM0 : 1 ≤ M0) {σ : ℝ} (hσ : 0 ≤ σ) (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (Λf : ∀ b, WPiece D L b → TheoremCBlock.AtomMeasure m₀ blk paperTail L b)
    (hΛμ : ∀ b x, wIsMu D L b x = true → Λf b x = D.R.law paperTail L b)
    (hΛp : ∀ b x, IsPositiveRecord (Λf b x)) (hΛm : ∀ b x, mass (Λf b x) = wMass D L b x)
    (f : ∀ b, WPiece D L b) (hEs : (wAtoms D L f).Nonempty) {B : ℝ}
    (hB : |multilinearIntegral (tensorLaw fun b => Λf b (f b))
        (fun _ => blockLift m₀ blk paperTail L A)| ≤ (∏ b, mass (Λf b (f b))) * B) :
    open Classical in
    multilinearIntegral (tensorLaw fun b => Λf b (f b)) (fun _ => blockLift m₀ blk paperTail L A) -
        (∏ b, wpieceG D L b (f b)) * ((1 + scaleU blockScale M0 (cliqueConstant m₀ D.S.ep)
          stageTau L) * D.Y L A) ≤
      (∏ b, wMass D L b (f b)) *
        (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A + (if wSmall D L f then 0 else B)) := by
  classical
  have hY0 : 0 ≤ D.Y L A := le_trans (mul_nonneg (mul_nonneg hC0
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (density_nonneg _ _) _))
    hcex.lower.le
  have hu0 := scaleU_nonneg blockScale M0 (cliqueConstant m₀ D.S.ep) stageTau L
  have huY : 0 ≤ (1 + scaleU blockScale M0 (cliqueConstant m₀ D.S.ep) stageTau L) * D.Y L A :=
    mul_nonneg (by linarith) hY0
  have hm0 : 0 ≤ ∏ b, wMass D L b (f b) := prod_nonneg fun b _ => wMass_nonneg D L b (f b)
  have hG0 : 0 ≤ ∏ b, wpieceG D L b (f b) := prod_nonneg fun b _ => wpieceG_nonneg b (f b)
  have hK10 : 0 ≤ dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
      (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
      (L : ℝ) ^ (-σ) * density (blockScale * L) A :=
    mul_nonneg (mul_nonneg (dcConstant_nonneg
      (by exact_mod_cast (prefixConductor_pos blk _).le) (Nat.cast_nonneg _) hC1 hC71)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (density_nonneg _ _)
  by_cases hs : wSmall D L f
  · simp only [hs, ↓reduceIte, add_zero]
    obtain ⟨qE, cE, hDE, hqE, hcE, hcE0, hcQ, hcopE, hqN⟩ := hs
    have hE : ∀ b ∉ wAtoms D L f, Λf b (f b) = D.R.law paperTail L b := by
      intro b hb
      simp only [wAtoms, mem_filter, mem_univ, true_and, Bool.not_eq_false] at hb
      exact hΛμ b (f b) hb
    have hch := whole_chain hdcb D hpair hcex ha hC0 hL hsc hM0 (fun b => Λf b (f b))
      (wAtoms D L f) hE (fun b _ => hΛp b (f b)) (prod_crtModuli_ne_one D hne hEs) hDE hqE hcE
      hcE0 hcQ hcopE hqN hσ hS1
    rw [prod_mass_wAtoms D L Λf hΛm f] at hch
    have hpr := wPrice_le D hpair hpar hsel L f
    have key : ∀ {X m G s c Y K : ℝ}, |X| ≤ m * (c * s * Y + K) → m * s ≤ G → 0 ≤ c * Y →
        X - G * (c * Y) ≤ m * K := by
      intro X m G s c Y K h1 h2 h3
      have h4 : m * (c * s * Y) ≤ G * (c * Y) := by
        calc m * (c * s * Y) = (m * s) * (c * Y) := by ring
          _ ≤ G * (c * Y) := mul_le_mul_of_nonneg_right h2 h3
      rw [mul_add] at h1
      linarith [le_abs_self X]
    exact key hch hpr huY
  · simp only [hs, ↓reduceIte]
    simp only [hΛm] at hB
    have key : ∀ {X m G cY K B : ℝ}, |X| ≤ m * B → 0 ≤ G * cY → 0 ≤ m * K →
        X - G * cY ≤ m * (K + B) := by
      intro X m G cY K B h1 h2 h3
      rw [mul_add]
      linarith [le_abs_self X]
    exact key hB (mul_nonneg hG0 huY) (mul_nonneg hm0 hK10)

omit [DecidableEq P] in
/-- The Rankin weights are at least one (`q_𝔟 ≥ 1`: a squarefree number). -/
theorem one_le_wqf (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j)) (L : ℕ) (b : BlockAtom Bk PaperJt L) (x : WPiece D L b) :
    1 ≤ wqf D L (atomQR D L) b x := by
  unfold wqf
  split_ifs
  · exact le_rfl
  · unfold atomQR
    have hsq := squarefree_atomQ (blk := blk) (p := paperTail) D.S.m₀_eq D.S.pp_prime D.S.ep_pos
      (prefix_pairwise (hpair L)) D.S.p_prime L b
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hsq.ne_zero

omit [DecidableEq P] in
/-- **`SF.hrem` at the constructed data** (`lem:sharp-first`, the error terms; see the module
docstring). -/
theorem sfRem_proved
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, DecFamily D L) (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β) (hne : ∀ β, ∃ i, blk i = β) :
    ∃ c : ℝ, 0 ≤ c ∧ SFRem D c (sfRp D dec) (sfRm D dec) := by
  classical
  obtain ⟨C1, C71, hC1, hC71, hdcb⟩ := density_dc_block' (1 / 10 : ℝ) (by norm_num)
  obtain ⟨CH, hCH, hH⟩ := whole_holder (m₀ := m₀) (blk := blk) ((1 : ℝ) / 2000) (by norm_num)
  have hM0 : 1 ≤ modulus pr h := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hQ1 : 1 ≤ cliqueConstant m₀ D.S.ep :=
    Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i _ => NeZero.ne _)
  set Cdc := dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ
    (modulus pr h) (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 with hCdc
  have hCdc0 : 0 ≤ Cdc := dcConstant_nonneg (by exact_mod_cast (prefixConductor_pos blk _).le)
    (Nat.cast_nonneg _) hC1.le hC71.le
  set CB := ((modulus pr h : ℕ) : ℝ) ^ 72 *
    ((Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * CH * blockScale) with hCB
  have hCB0 : 0 ≤ CB := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hCH.le) (Nat.cast_nonneg _))
  set nT : ℝ := ((Fintype.card D.FS.Tag : ℕ) : ℝ) with hnT
  have hnT0 : 0 ≤ nT := Nat.cast_nonneg _
  refine ⟨nT * (Cdc + CB) * Real.exp D.SM.bound,
    mul_nonneg (mul_nonneg hnT0 (add_nonneg hCdc0 hCB0)) (Real.exp_nonneg _), ?_⟩
  unfold SFRem
  filter_upwards [eventually_scaleConditions blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep)
    1 0 0 (by norm_num [blockScale]) hM0 hQ1, eventually_ge_atTop 2] with L hsc hL
  intro C hC hk A hA hY
  have hcex : IsLeastCounterexample D.Y a densityExponent C L A :=
    ⟨hA, hY, fun ℓ h1 h2 => hk ℓ h1 h2⟩
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
  have hL1 : 1 ≤ L := by omega
  have hcd : (0 : ℝ) ≤ Sarkozy.cancellationDecay := by
    unfold Sarkozy.cancellationDecay; norm_num
  have hα0 := density_nonneg (blockScale * L) A
  set α := density (blockScale * L) A with hα
  set K1 := Cdc * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * α with hK1
  have hK10 : 0 ≤ K1 := mul_nonneg (mul_nonneg hCdc0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hα0
  set B := ((modulus pr h : ℕ) : ℝ) ^ 72 *
    ((Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * CH *
      paperCutoff (blockScale * L) ^ ((1 : ℝ) / 2000) * ((blockScale : ℝ) * α)) with hBdef
  have hB0 : 0 ≤ B := lpB_nonneg hL1 A hCH.le
  set T := ((blockScale * L : ℕ) : ℝ) ^ stageTau with hT
  have hT0 : 0 < T := stageT_pos L hL1
  set Pi := ∏ b, (1 + atomQR D L b ^ ((1 : ℝ) / 4) * wPr D L b) with hPi
  have hPi_le : Pi ≤ Real.exp D.SM.bound := prod_wPr_le_exp D L ha
  set Φ : (∀ b, WPiece D L b) → ℝ := fun f => K1 + (if wSmall D L f then 0 else B) with hΦ
  have hΦ0 : ∀ f, 0 ≤ Φ f := fun f =>
    add_nonneg hK10 (by split_ifs <;> first | exact le_rfl | exact hB0)
  set G0 : ∀ b, WPiece D L b → ℝ := fun b x => wCmax b x * wpieceD D L b x * wMass D L b x
    with hG0
  have hG00 : ∀ b x, 0 ≤ G0 b x := fun b x => mul_nonneg (mul_nonneg (wCmax_nonneg b x)
    (wpieceD_nonneg b x)) (wMass_nonneg D L b x)
  -- Step A: one term
  have hterm : ∀ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∀ j f, choiceWeight (wpieceCoef σ j) (wpieceD D L) f *
        ((sfRp D dec L A σ j f + sfRm D dec L A σ j f) / 2) ≤
      choiceWeight (wpieceCoef σ j) (wpieceD D L) f * (∏ b, wMass D L b (f b)) * Φ f := by
    intro σ hσ j f
    have hσ' : σ ≠ fun _ => none := (mem_filter.mp hσ).2
    have hw0 := choiceWeight_w_nonneg σ j f
    by_cases hw : choiceWeight (wpieceCoef σ j) (wpieceD D L) f = 0
    · rw [hw]
      simp
    · have hEs := wAtoms_nonempty D σ hσ' j f hw
      have hm0 : 0 ≤ (∏ b, wMass D L b (f b)) * Φ f :=
        mul_nonneg (prod_nonneg fun b _ => wMass_nonneg D L b (f b)) (hΦ0 f)
      have hp := excess_le D hdcb hC1.le hC71.le hpair ha hpar hsel hne hcex hC0 hL hsc hM0 hcd
        S1_at_cancellationDecay (wpieceLp (dec L) j) (wpieceLp_of_mu (dec L) j)
        (isPositiveRecord_wpieceLp (dec L) (D.S.p_prime L) j) (mass_wpieceLp (dec L) j) f hEs
        (hH hpair A hsc hL1 hM0 (D.S.p_prime L) (D.S.p_inj L) _
          (fun b => isPositiveRecord_wpieceLp (dec L) (D.S.p_prime L) j b (f b)))
      have hm := excess_le D hdcb hC1.le hC71.le hpair ha hpar hsel hne hcex hC0 hL hsc hM0 hcd
        S1_at_cancellationDecay (wpieceLm (dec L) j) (wpieceLm_of_mu (dec L) j)
        (isPositiveRecord_wpieceLm (dec L) (D.S.p_prime L) j) (mass_wpieceLm (dec L) j) f hEs
        (hH hpair A hsc hL1 hM0 (D.S.p_prime L) (D.S.p_inj L) _
          (fun b => isPositiveRecord_wpieceLm (dec L) (D.S.p_prime L) j b (f b)))
      have hrp : sfRp D dec L A σ j f ≤ (∏ b, wMass D L b (f b)) * Φ f := max_le hm0 hp
      have hrm : sfRm D dec L A σ j f ≤ (∏ b, wMass D L b (f b)) * Φ f := max_le hm0 hm
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith) hw0
  -- Step D: one tag
  have hone : ∀ j : D.FS.Tag, ∑ σ : (∀ b, Option (D.FS.Ib L b)), ∑ f : (∀ b, WPiece D L b),
      choiceWeight (wpieceCoef σ j) (wpieceD D L) f * (∏ b, wMass D L b (f b)) * Φ f ≤
      K1 * Pi + B * (T ^ (-((1 : ℝ) / 4)) * Pi) := by
    intro j
    refine (sum_choices_le j Φ hΦ0).trans ?_
    have hW1 : ∀ b x, G0 b x ≤ G0 b x * wqf D L (atomQR D L) b x ^ ((1 : ℝ) / 4) := fun b x =>
      le_mul_of_one_le_right (hG00 b x) (Real.one_le_rpow (one_le_wqf D hpair L b x) (by norm_num))
    have hPiE : ∏ b, ∑ x, G0 b x * wqf D L (atomQR D L) b x ^ ((1 : ℝ) / 4) = Pi := by
      refine prod_congr rfl fun b _ => ?_
      exact sum_atom_eq D L (atomQR D L) b
    have hall : ∑ f : (∀ b, WPiece D L b), ∏ b, G0 b (f b) ≤ Pi := by
      rw [← hPiE, Fintype.prod_sum (fun b x => G0 b x * wqf D L (atomQR D L) b x ^ ((1 : ℝ) / 4))]
      exact sum_le_sum fun f _ => prod_le_prod₀ (fun b _ => hG00 b (f b)) fun b _ => hW1 b (f b)
    have hlarge : ∑ f ∈ univ.filter (fun f : (∀ b, WPiece D L b) => ¬ wSmall D L f),
        ∏ b, G0 b (f b) ≤ T ^ (-((1 : ℝ) / 4)) * Pi := by
      rw [← hPiE]
      refine le_trans ?_ (Sarkozy.SharpSums.sum_large_pieces_le G0
        (fun b x => wqf D L (atomQR D L) b x) hG00
        (fun b x => wqf_nonneg D L (atomQR_nonneg D L) b x) hT0)
      refine sum_le_sum_of_subset_of_nonneg ?_ fun f _ _ => prod_nonneg fun b _ => hG00 b (f b)
      intro f hf
      rw [mem_filter] at hf ⊢
      exact ⟨hf.1, large_of_not_wSmall D hpair hpar L f hf.2⟩
    have e1 : ∑ f : (∀ b, WPiece D L b), (∏ b, G0 b (f b)) * Φ f =
        K1 * ∑ f : (∀ b, WPiece D L b), ∏ b, G0 b (f b) +
          B * ∑ f ∈ univ.filter (fun f : (∀ b, WPiece D L b) => ¬ wSmall D L f),
            ∏ b, G0 b (f b) := by
      rw [mul_sum, mul_sum, sum_filter, ← sum_add_distrib]
      refine sum_congr rfl fun f _ => ?_
      simp only [hΦ]
      split_ifs <;> ring
    change ∑ f : (∀ b, WPiece D L b), (∏ b, G0 b (f b)) * Φ f ≤ _
    rw [e1]
    exact add_le_add (mul_le_mul_of_nonneg_left hall hK10)
      (mul_le_mul_of_nonneg_left hlarge hB0)
  -- the sums
  have hnn : ∀ σ : (∀ b, Option (D.FS.Ib L b)), 0 ≤ ∑ j : D.FS.Tag, ∑ f : (∀ b, WPiece D L b),
      choiceWeight (wpieceCoef σ j) (wpieceD D L) f * (∏ b, wMass D L b (f b)) * Φ f :=
    fun σ => sum_nonneg fun j _ => sum_nonneg fun f _ => mul_nonneg (mul_nonneg
      (choiceWeight_w_nonneg σ j f) (prod_nonneg fun b _ => wMass_nonneg D L b (f b))) (hΦ0 f)
  calc _ ≤ ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j : D.FS.Tag, ∑ f : (∀ b, WPiece D L b),
          choiceWeight (wpieceCoef σ j) (wpieceD D L) f * (∏ b, wMass D L b (f b)) * Φ f :=
        sum_le_sum fun σ hσ => sum_le_sum fun j _ => sum_le_sum fun f _ => hterm σ hσ j f
    _ ≤ ∑ σ : (∀ b, Option (D.FS.Ib L b)), ∑ j : D.FS.Tag, ∑ f : (∀ b, WPiece D L b),
          choiceWeight (wpieceCoef σ j) (wpieceD D L) f * (∏ b, wMass D L b (f b)) * Φ f :=
        sum_le_univ_sum_of_nonneg hnn
    _ = ∑ j : D.FS.Tag, ∑ σ : (∀ b, Option (D.FS.Ib L b)), ∑ f : (∀ b, WPiece D L b),
          choiceWeight (wpieceCoef σ j) (wpieceD D L) f * (∏ b, wMass D L b (f b)) * Φ f :=
        sum_comm
    _ ≤ ∑ _j : D.FS.Tag, (K1 * Pi + B * (T ^ (-((1 : ℝ) / 4)) * Pi)) :=
        sum_le_sum fun j _ => hone j
    _ = nT * (K1 * Pi) + nT * (B * (T ^ (-((1 : ℝ) / 4)) * Pi)) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        ring
    _ ≤ nT * Cdc * Real.exp D.SM.bound * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * α +
          nT * CB * Real.exp D.SM.bound * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * α := by
        refine add_le_add ?_ (final_le hL1 hnT0 hCH.le hα0 hPi_le)
        have h0 : 0 ≤ nT * Cdc * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * α :=
          mul_nonneg (mul_nonneg (mul_nonneg hnT0 hCdc0) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
            hα0
        calc nT * (K1 * Pi) = (nT * Cdc * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * α) * Pi := by
              rw [hK1]; ring
          _ ≤ (nT * Cdc * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * α) * Real.exp D.SM.bound :=
              mul_le_mul_of_nonneg_left hPi_le h0
          _ = _ := by ring
    _ = remainder (nT * (Cdc + CB) * Real.exp D.SM.bound) L A := by
        unfold remainder
        ring

end Paper

end Sarkozy.SharpFirst
