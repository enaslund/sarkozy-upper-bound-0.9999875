module

public import Sarkozy.OpsSteps.FineE1

@[expose] public section

/-!
# The finer (E1) of Step 4 (i): the summed remainders (OPS-S)

`paper/sections/10_comparison_lemmas.tex`, "Fixed selections and summed remainders"
(ll. 126–140), `prop:record:density-structured`, `lem:record:density-lp`.

* `subBnd`, **`sum_subBnd_le`**: EC's two summations of the subset terms (G1's
  `sum_subset_remainder_le`, `sum_selection_remainder_le` on the small unions; Hölder and Rankin,
  EC's `sub_large_le`, on the large ones), for the law-independent bound
  `(rem or B) · ∏_𝔟 ‖subLaw_𝔟‖`;
* **`fX_le_fineBnd`**: a finer term's canonical remainder is at most the same bound with the finer
  masses (`fineSmallPT_proved` on a small union, Hölder on a large one);
* **`fX_summable`**: hence `∑_ω π̃_ω ∑_g fX_{ω,g} ≤ c L^{-σ} α` at every least counterexample,
  through `collapse_sum` (the finer masses add up to EC's).
-/

namespace Sarkozy.OpsSteps

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.DensityFibre Sarkozy.EnvelopeInputsBlock Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.E1Closure
open Sarkozy.Param (Params)
open Sarkozy.SharpFirst (sfEps sfEps_nonneg)
open Sarkozy.LargeSums (atomQR atomQR_nonneg atomPr)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (L : ℕ)

/-- The law-independent bound of a subset term: `(rem or B) · ∏ ‖subLaw‖`. -/
noncomputable def subBnd (rem B : ℝ) (ω : Choice (D.CL.T L))
    (f : BlockAtom Bk PaperJt L → Bool) : ℝ :=
  (if SubSmall D L ω f then rem else B) * ∏ b, mass (subLaw D L b (ω b) (f b))

omit [DecidableEq P] in
theorem prod_mass_subLaw (ω : Choice (D.CL.T L)) (f : BlockAtom Bk PaperJt L → Bool) :
    ∏ b, mass (subLaw D L b (ω b) (f b)) =
      ∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1) := by
  refine prod_congr rfl fun b _ => ?_
  rcases hf : f b
  · simp only [Bool.false_eq_true, ↓reduceIte, subLaw]
    exact mass_entryFactor D L b (ω b)
  · simp only [↓reduceIte, subLaw]
    split_ifs
    · exact mass_zero_measure
    · rfl

omit [DecidableEq P] in
/-- **The law-independent summation of the subset terms** (EC's two summations). -/
theorem sum_subBnd_le (ha : 0 ≤ a) (A : Finset ℤ) {c₁ B : ℝ} (hc₁ : 0 ≤ c₁) (hB0 : 0 ≤ B)
    (hT : 0 < stageT L) :
    ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω), monomial (D.CL.πt L) ω *
        ∑ f, subBnd D L (remainder c₁ L A) B ω f ≤
      remainder (Real.exp D.CL.S * Real.cosh D.CL.A * (Real.exp D.GB.U₀ * c₁)) L A +
        B * (stageT L ^ (-((1 : ℝ) / 4)) * ∏ b, atomW D L b) := by
  have hp := D.S.p_prime L
  set rem := remainder c₁ L A with hremdef
  have hrem0 : 0 ≤ rem := E1Closure.remainder_nonneg' hc₁ L A
  have hm0 : ∀ (ω : Choice (D.CL.T L)) (f : BlockAtom Bk PaperJt L → Bool),
      0 ≤ ∏ b, mass (subLaw D L b (ω b) (f b)) := fun ω f =>
    prod_nonneg fun b _ => TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg
      (isPositiveRecord_subLaw D L hp b (ω b) (f b)).1
  have hsplit : ∀ (ω : Choice (D.CL.T L)) (f : BlockAtom Bk PaperJt L → Bool),
      subBnd D L rem B ω f =
      (if SubSmall D L ω f then (∏ b, mass (subLaw D L b (ω b) (f b))) * rem else 0) +
        (if SubSmall D L ω f then 0 else (∏ b, mass (subLaw D L b (ω b) (f b))) * B) := by
    intro ω f
    unfold subBnd
    split_ifs <;> ring
  simp only [hsplit, sum_add_distrib, mul_add]
  refine add_le_add ?_ ?_
  · -- small: G1's summations
    refine TheoremCBlock.Structured.sum_selection_remainder_le D ha L A _
      (mul_nonneg (Real.exp_pos _).le hc₁) fun ω _ => ?_
    refine le_trans (sum_le_sum fun f _ => ?_)
      (TheoremCBlock.Structured.sum_subset_remainder_le D ha L A ω hc₁)
    rw [← prod_mass_subLaw D L ω f]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hm0 ω f) hrem0
  · -- large: Hölder and Rankin (EC's `sub_large_le`, without the law)
    set T := stageT L with hTdef
    set g : ∀ b : BlockAtom Bk PaperJt L, Option (D.CL.T L b × ChangeType) → Bool → ℝ :=
      fun b o y => entryPrice (D.CL.πt L b) o * mass (subLaw D L b o y) *
        subQ D L b o y ^ ((1 : ℝ) / 4) with hg
    have hw0 : ∀ b o y, 0 ≤ entryPrice (D.CL.πt L b) o * mass (subLaw D L b o y) := fun b o y =>
      mul_nonneg (entryPrice_nonneg (D.CL.πt_nonneg L b) o)
        (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg
          (isPositiveRecord_subLaw D L hp b o y).1)
    have hg0 : ∀ b o y, 0 ≤ g b o y := fun b o y =>
      mul_nonneg (hw0 b o y) (Real.rpow_nonneg (subQ_nonneg D L b o y) _)
    have hT4 : 0 ≤ T ^ (-((1 : ℝ) / 4)) := Real.rpow_nonneg hT.le _
    have hterm : ∀ (ω : Choice (D.CL.T L)) (f : BlockAtom Bk PaperJt L → Bool),
        monomial (D.CL.πt L) ω *
          (if SubSmall D L ω f then 0 else (∏ b, mass (subLaw D L b (ω b) (f b))) * B) ≤
          B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, g b (ω b) (f b)) := by
      intro ω f
      split_ifs with hs
      · rw [mul_zero]
        exact mul_nonneg hB0 (mul_nonneg hT4 (prod_nonneg fun b _ => hg0 b (ω b) (f b)))
      · have h2 := rankin_term univ
          (fun b => entryPrice (D.CL.πt L b) (ω b) * mass (subLaw D L b (ω b) (f b)))
          (fun b => subQ D L b (ω b) (f b)) (fun b _ => hw0 b (ω b) (f b))
          (fun b _ => subQ_nonneg D L b (ω b) (f b)) hT (lt_of_not_ge hs)
        have hm : monomial (D.CL.πt L) ω = ∏ b, entryPrice (D.CL.πt L b) (ω b) := rfl
        calc monomial (D.CL.πt L) ω * ((∏ b, mass (subLaw D L b (ω b) (f b))) * B)
            = B * ∏ b, (entryPrice (D.CL.πt L b) (ω b) * mass (subLaw D L b (ω b) (f b))) := by
              rw [hm, prod_mul_distrib]
              ring
          _ ≤ B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, g b (ω b) (f b)) :=
              mul_le_mul_of_nonneg_left h2 hB0
    calc ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω), monomial (D.CL.πt L) ω *
          ∑ f, (if SubSmall D L ω f then 0 else (∏ b, mass (subLaw D L b (ω b) (f b))) * B)
        ≤ ∑ ω : Choice (D.CL.T L), monomial (D.CL.πt L) ω *
          ∑ f, (if SubSmall D L ω f then 0 else (∏ b, mass (subLaw D L b (ω b) (f b))) * B) := by
          refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun ω _ _ =>
            mul_nonneg (monomial_nonneg (D.CL.πt_nonneg L) ω) (sum_nonneg fun f _ => ?_)
          split_ifs
          · exact le_rfl
          · exact mul_nonneg (hm0 ω f) hB0
      _ = ∑ ω : Choice (D.CL.T L), ∑ f : BlockAtom Bk PaperJt L → Bool, monomial (D.CL.πt L) ω *
          (if SubSmall D L ω f then 0 else (∏ b, mass (subLaw D L b (ω b) (f b))) * B) := by
          simp only [mul_sum]
      _ ≤ ∑ ω : Choice (D.CL.T L), ∑ f : BlockAtom Bk PaperJt L → Bool,
          B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, g b (ω b) (f b)) :=
          sum_le_sum fun ω _ => sum_le_sum fun f _ => hterm ω f
      _ = B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, ∑ o, ∑ y, g b o y) := by
          rw [← sum_sum_prod g]
          simp only [mul_sum]
      _ ≤ B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, atomW D L b) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hT4) hB0
          exact prod_le_prod₀ (fun b _ => sum_nonneg fun o _ => sum_nonneg fun y _ => hg0 b o y)
            fun b _ => subAtom_le D L b

omit [DecidableEq P] in
/-- **A finer term's canonical remainder is at most the law-independent bound.** -/
theorem fX_le_fineBnd (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool) {A : Finset ℤ}
    (hY : 0 ≤ D.Y L A) {rem B : ℝ} (hrem : 0 ≤ rem) (hB0 : 0 ≤ B)
    (hB : (FiniteLaw.uniform (∀ b : BlockAtom Bk PaperJt L, BlockLabel m₀ blk paperTail L b)).moment
      72 (blockLift m₀ blk paperTail L A) ≤ B)
    (ω : Choice (D.CL.T L)) (g : BlockAtom Bk PaperJt L → Option Bool)
    (hpt : SubSmall D L ω (collapse L g) →
      |fineInt D L isG A ω g| ≤ fineMain D L isG (sfEps D) A ω g +
        (∏ b, mass (fineLaw D L isG b (ω b) (g b))) * rem) :
    fX D L isG (sfEps D) A ω g ≤
      (if SubSmall D L ω (collapse L g) then rem else B) *
        ∏ b, mass (fineLaw D L isG b (ω b) (g b)) := by
  have hp := D.S.p_prime L
  have hm0 : 0 ≤ ∏ b, mass (fineLaw D L isG b (ω b) (g b)) :=
    prod_nonneg fun b _ => TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg
      (isPositiveRecord_fineLaw D L isG hp b (ω b) (g b)).1
  have hmain0 : 0 ≤ fineMain D L isG (sfEps D) A ω g := by
    unfold fineMain
    refine mul_nonneg (mul_nonneg (mul_nonneg (by linarith [sfEps_nonneg D L])
      (prod_nonneg fun b _ => D.selectionFactor_nonneg L b)) hY) (prod_nonneg fun b _ => ?_)
    rcases g b with _ | gg
    · exact zero_le_one
    · unfold finePr
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg
          (isPositiveRecord_sum _ _ fun i _ => D.GB.κu_pos L b i).1) (D.selectionFactor_nonneg L b)
  unfold fX
  split_ifs with hs
  · have := hpt hs
    exact max_le (mul_nonneg hrem hm0) (by linarith)
  · have h1 : |fineInt D L isG A ω g| ≤ (∏ b, mass (fineLaw D L isG b (ω b) (g b))) * B :=
      abs_diag_le_dom _ _ (fun b => isPositiveRecord_fineLaw D L isG hp b (ω b) (g b))
        (fun b z => le_of_eq (abs_of_nonneg (lawDensity_nonneg
          (isPositiveRecord_fineLaw D L isG hp b (ω b) (g b)).1 z))) _ hB
    rw [mul_comm]
    exact max_le (mul_nonneg hm0 hB0) (by linarith)

omit [DecidableEq P] in
/-- **The finer (E1) of Step 4 (i) has summable remainders**: on the paper's tails there is
`c ≥ 0` such that at every least counterexample and for every split `isG` of the bracket records,
`∑_ω π̃_ω ∑_g fX_{ω,g} ≤ c L^{-σ} α`. -/
theorem fX_summable
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β) (hne : ∀ β, ∃ i, blk i = β) :
    ∃ c : ℝ, 0 ≤ c ∧ Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool,
      ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω), monomial (D.CL.πt L) ω *
        ∑ g : BlockAtom Bk PaperJt L → Option Bool, fX D L isG (sfEps D) A ω g ≤
        remainder c L A) := by
  obtain ⟨c₁, hc₁, hPT⟩ := fineSmallPT_proved D hpair ha hpar hsel hne
  obtain ⟨C, hC, hmom⟩ := blockLift_moment_le (m₀ := m₀) (blk := blk) (p := paperTail)
  set X : ℝ := (Fintype.card (ResidueSpace m₀) : ℝ) with hX
  refine ⟨Real.exp D.CL.S * Real.cosh D.CL.A * (Real.exp D.GB.U₀ * c₁) +
    1 * ((1 : ℝ) ^ 72 * (X ^ 72 * C * blockScale)) * Real.exp (2 * D.SM.bound),
    add_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le)
      (mul_nonneg (Real.exp_pos _).le hc₁)) (by positivity), ?_⟩
  filter_upwards [hPT, eventually_ge_atTop (2 ^ 20 * blockScale)] with L hPTL hL
  intro Cc hCc hk A hA hYc isG
  have hY : 0 ≤ D.Y L A := (Param.counterexample_pos (Params.ofDecay a) hCc hYc).le
  have hL1 : 1 ≤ L := le_trans (by norm_num [blockScale]) hL
  have hB := hmom L hL (D.S.p_prime L) (D.S.p_inj L) A
  have hB0 := Sarkozy.LargeSums.lpB_nonneg (M0 := 1) (X := X) hL1 A hC.le
  have hT : 0 < stageT L := Sarkozy.LargeSums.stageT_pos L hL1
  set B := (1 : ℝ) ^ 72 * (X ^ 72 * C * Functional.paperCutoff (blockScale * L) ^ ((1 : ℝ) / 2000) *
    ((blockScale : ℝ) * density (blockScale * L) A)) with hBdef
  set rem := remainder c₁ L A with hremdef
  have hrem0 : 0 ≤ rem := E1Closure.remainder_nonneg' hc₁ L A
  have hper : ∀ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      ∑ g : BlockAtom Bk PaperJt L → Option Bool, fX D L isG (sfEps D) A ω g ≤
        ∑ f, subBnd D L rem B ω f := by
    intro ω hω
    have hsel' : IsSelection ω := (mem_filter.mp hω).2
    calc _ ≤ ∑ g : BlockAtom Bk PaperJt L → Option Bool,
          (if SubSmall D L ω (collapse L g) then rem else B) *
            ∏ b, mass (fineLaw D L isG b (ω b) (g b)) :=
          sum_le_sum fun g _ => fX_le_fineBnd D L isG hY hrem0 hB0 hB ω g
            (fun hs => hPTL Cc hCc hk A hA hYc isG ω hsel' g hs)
      _ = ∑ f, subBnd D L rem B ω f := by
          rw [collapse_sum D L isG ω (fun f => if SubSmall D L ω f then rem else B)]
          rfl
  have h1 := sum_subBnd_le D L ha A hc₁ hB0 hT
  have hPi := prod_atomW_le D L ha
  have key := Sarkozy.LargeSums.final_le hL1 zero_le_one hC.le (density_nonneg (blockScale * L) A)
    hPi (M0 := 1) (X := X)
  calc _ ≤ ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω * ∑ f, subBnd D L rem B ω f :=
        sum_le_sum fun ω hω => mul_le_mul_of_nonneg_left (hper ω hω)
          (monomial_nonneg (D.CL.πt_nonneg L) ω)
    _ ≤ _ := h1
    _ ≤ _ := by
        rw [E1Closure.remainder_add]
        refine add_le_add le_rfl ?_
        unfold stageT
        unfold remainder
        exact le_of_eq_of_le (by ring) (key.trans_eq (by ring))

end Sarkozy.OpsSteps
