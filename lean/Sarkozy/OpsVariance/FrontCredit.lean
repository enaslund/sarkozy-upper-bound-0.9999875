module

public import Sarkozy.OpsVariance.Restoration
public import Sarkozy.OpsVariance.Front

@[expose] public section

/-!
# The restoration field at the obligations' data: (E1) with `μ` outside from EC

`paper/sections/22_variance.tex`, proof of `lem:var-gain`(a) ("(E1) bounds the last energy by
`(1 + o(1)) C_X Y`"); `paper/sections/10_comparison_lemmas.tex`, (E1) (first bound, `μ` outside),
`lem:bracket-energy`, "Fixed selections and summed remainders".

`hres_of_restoration` (`Restoration.lean`) takes (E1) with `μ` outside for the selected diagonals,
`Y[Diag_X(envM ω) ⊗ μ] ≤ (1 + z₂) C_X Y + r_μ(ω)`. At the norm envelopes this is EC's subset term
`E1Sub` at the empty atom set `f = ∅` (the envelope `⊗_X D` with `μ` outside):

* `diagFam_envM_eq`: `Diag_X(envM ω) ⊗ μ_{−X}` is the subset-term law of `ω` at `f = ∅`;
* `e1mu_of_sub`: (E1) with `μ` outside from any `E1Sub D ε_E r0`, with `r_μ(ω) = r0(ω, ∅)`;
* **`e1mu_front`**: at the obligations' data, with EC's `ε_E = u_L` (`sfEps`) and canonical
  remainders `r0X`: (E1) with `μ` outside for every selection, and the remainder budget
  `∑_ω π̃_ω r0X(ω, ∅) ≤ c L^{-σ} α` (from EC's `E1Rem`);
* **`hres_front`**: `hres` at the obligations' data, at every least counterexample, for every class
  with common support and prices, from the eligible record laws, (Cen) and (Res) alone; the
  remainder is `r₀ = γ₀ κ/(1 − κ) ∑_R r0X(ω, ∅)`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.E1Closure Sarkozy.SharpFirst Sarkozy.TheoremCBlock Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.EnvelopeInputs Sarkozy.DensityChain2 Sarkozy.CancellationSteps Sarkozy.BlockFrame
  Sarkozy.Functional Sarkozy.BlockAnchor
open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC
  Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.EnvelopeSteps Sarkozy.Variance
open Sarkozy.Param (Params)
open Sarkozy.CompanionND (CompanionFrontND)
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.Companion (E1Sub E1Rem)

section Generic

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}

omit [DecidableEq P] in
/-- `Diag_X(envM ω) ⊗ μ_{−X}` is the law `⊗_𝔅 entryFactor(μ_𝔅, D_𝔅, ω(𝔅))` of the subset term of `ω`
at the empty atom set. -/
theorem diagFam_envM_eq (L : ℕ) (ω : Choice (D.CL.T L)) :
    tensorLaw (diagFam reservedCut (D.R.law p L) (Choice.support ω) (Choice.support ω)
      (envM D L ω)) = tensorLaw fun b => entryFactor (D.R.law p L b) (D.CL.D L b) (ω b) := by
  congr 1
  funext b
  unfold diagFam
  by_cases hb : b ∈ Choice.support ω
  · simp only [hb, ↓reduceIte]
    rcases hω : ω b with _ | ⟨t, e⟩
    · exact absurd (by simpa [Choice.support] using hb) (by simp [hω])
    · exact diagonalLaw_envM hω
  · simp only [hb, ↓reduceIte]
    rw [eq_none_of_not_mem_support' hb]
    rfl

omit [DecidableEq P] in
/-- **(E1) with `μ` outside for the selected diagonals from the subset terms** (`E1Sub` at
`f = ∅`): `Y[Diag_X(envM ω) ⊗ μ] ≤ (1 + ε_E) C_X Y + r0(ω, ∅)`. -/
theorem e1mu_of_sub {εE : ℕ → ℝ} {r0 : Companion.E1R0 D} (hsub : E1Sub D εE r0) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ ω : Choice (D.CL.T L), IsSelection ω →
        diagonalIntegral (tensorLaw (diagFam reservedCut (D.R.law p L) (Choice.support ω)
          (Choice.support ω) (envM D L ω))) (blockLift m₀ blk p L A) ≤
        (1 + εE L) * selProd D L ω * D.Y L A + r0 L A ω (fun _ => false)) := by
  filter_upwards [hsub] with L hL
  intro C hC hind A hA hcount ω hω
  have h := hL C hC hind A hA hcount ω hω (fun _ => false)
  simp only [Bool.false_eq_true, ↓reduceIte, prod_const_one, mul_one] at h
  rw [diagFam_envM_eq]
  exact (le_abs_self _).trans h

omit [DecidableEq P] in
/-- **The budget of the remainders at `f = ∅`**: under `E1Rem`, with nonnegative remainders,
`∑_ω π̃_ω r0(ω, ∅) ≤ c_E L^{-σ} α`. -/
theorem sum_r0_empty_le {cE : ℝ} {r0 : Companion.E1R0 D} {r : Companion.E1R D}
    (hrem : E1Rem D cE r0 r) (hs0 : ∀ L A ω f, 0 ≤ r0 L A ω f)
    (hr0 : ∀ L A ω σ j f, 0 ≤ r L A ω σ j f) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω * r0 L A ω (fun _ => false) ≤ Comparison.remainder cE L A) := by
  filter_upwards [hrem] with L hL
  intro C hC hind A hA hcount
  refine le_trans (sum_le_sum fun ω _ => ?_) (hL C hC hind A hA hcount)
  apply mul_le_mul_of_nonneg_left _ (monomial_πt_nonneg L ω)
  have hf : r0 L A ω (fun _ => false) ≤ ∑ f, r0 L A ω f :=
    single_le_sum (fun f _ => hs0 L A ω f) (mem_univ _)
  have hσ : 0 ≤ ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ j, ∑ f, (∏ b, |EnvelopeInputsBlock.ecpieceCoef D L ω σ j b (f b)|) * r L A ω σ j f :=
    sum_nonneg fun σ _ => sum_nonneg fun j _ => sum_nonneg fun f _ =>
      mul_nonneg (prod_nonneg fun b _ => abs_nonneg _) (hr0 L A ω σ j f)
  linarith

/-- **The restoration field of every credit class from (Cen) and (Res)** (the conclusion of
`hres_of_sub`): at every least counterexample, for every class `R` of selections with common support
`X` and price `γ₀`, eligible record laws `w` with half marginals `envM`, (Cen) with `κ < 1` and
(Res) with `μ` outside, `hres` holds with `b̃ = l̄ = (l₀/C − κ)/(1 − κ)`, any
`z ≥ (z₁ + κ ε_E)/(1 − κ)`
and `r₀ = γ₀ κ/(1 − κ) ∑_R r0(ω, ∅)`. -/
def HresFromRestoration (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (εE : ℕ → ℝ)
    (r0 : Companion.E1R0 D) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    ∀ (R : Finset (Choice (D.CL.T L))), R.Nonempty → (∀ ω ∈ R, IsSelection ω) →
    ∀ (X : Finset (BlockAtom Bk J L)), (∀ ω ∈ R, Choice.support ω = X) →
    ∀ (γ₀ : ℝ), (∀ ω ∈ R, monomial (D.CL.πt L) ω = γ₀) →
    ∀ (w : Choice (D.CL.T L) → ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ),
    (∀ ω ∈ R, ∀ b ∈ X, ∀ z, 0 ≤ w ω b z) →
    (∀ ω ∈ R, ∀ b ∈ X, plusMarginal reservedCut (w ω b) = envM D L ω b) →
    (∀ ω ∈ R, ∀ b ∈ X, minusMarginal reservedCut (w ω b) = envM D L ω b) →
    (∀ ω ∈ R, ∀ b ∈ X, ∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ,
      reservedCut.form (signedIntegral (w ω b)) G H =
        reservedCut.form (signedIntegral (w ω b)) H G) →
    ∀ (κj : Choice (D.CL.T L) → BlockAtom Bk J L → ℝ),
    (∀ ω ∈ R, ∀ b ∈ X,
      CentredNormLe reservedCut (signedIntegral (w ω b)) (envM D L ω b) (κj ω b)) →
    ∀ (κ : ℝ), 0 ≤ κ → κ < 1 → (∀ ω ∈ R, ∀ b ∈ X, κj ω b ≤ κ) →
    ∀ (C l₀ z₁ z : ℝ), 1 ≤ ∏ b ∈ X, selectionFactor a p D.S.selPre L b →
    ∏ b ∈ X, selectionFactor a p D.S.selPre L b ≤ C → 0 ≤ z₁ →
    (z₁ + κ * εE L) / (1 - κ) ≤ z →
    (l₀ - z₁) * D.Y L A * R.card ≤ ∑ ω ∈ R,
      diagonalIntegral (tensorLaw (recFam reservedCut (D.R.law p L) X X (w ω) (envM D L ω)))
        (blockLift m₀ blk p L A) →
    (gainBar l₀ C κ - z) * (∑ ω ∈ R, monomial (D.CL.π L) ω) * D.Y L A -
        γ₀ * (κ / (1 - κ)) * ∑ ω ∈ R, r0 L A ω (fun _ => false) ≤
      ∑ ω ∈ R, monomial (D.CL.πt L) ω * varJ0 D L A ω (envM D L ω))

omit [DecidableEq P] in
/-- **`hres` from (Cen) and (Res), with (E1) at `μ` from the subset terms** (`hres_of_restoration`
with `e1mu_of_sub`). -/
theorem hres_of_sub {εE : ℕ → ℝ} {r0 : Companion.E1R0 D} (hsub : E1Sub D εE r0)
    (hs0 : ∀ L A ω f, 0 ≤ r0 L A ω f) (hε0 : ∀ L, 0 ≤ εE L) : HresFromRestoration D εE r0 := by
  filter_upwards [e1mu_of_sub hsub] with L hL
  intro C' hC' hind A hA hcount R hR hsel X hX γ₀ hγ w hw hp hn ht κj hcen κ hκ0 hκ1 hκ C l₀ z₁
    z hCX hC hz₁ hz hRes
  have hY : 0 ≤ D.Y L A := (TheoremCParam.counterexample_pos hC' hcount).le
  exact hres_of_restoration R hR X hX hγ w hw hp hn ht κj hcen hκ0 hκ1 hκ
    (fun ω => r0 L A ω (fun _ => false)) (fun ω _ => hs0 L A ω _) hY hCX hC hz₁ (hε0 L) hz hRes
    (fun ω hω => by
      have h := hL C' hC' hind A hA hcount ω (hsel ω hω)
      rw [hX ω hω] at h
      simpa [selProd, hX ω hω] using h)

end Generic

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperRecordTables}

/-- **(E1) with `μ` outside for the selected diagonals at the obligations' data**, with EC's
`ε_E = u_L` (`sfEps`) and canonical remainders `r0X(ω, ∅)`, and their budget
`∑_ω π̃_ω r0X(ω, ∅) ≤ c L^{-σ} α` (EC's `E1Rem`, through `e1RemX_of_split`). -/
theorem e1mu_front (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) :
    Param.AtCounterexamples (Params.ofDecay TargetLedger.targetDecay) (F.X hB hRR).data.Y
      (fun L A => ∀ ω : Choice ((F.X hB hRR).data.CL.T L), IsSelection ω →
        diagonalIntegral (tensorLaw (diagFam reservedCut ((F.X hB hRR).data.R.law paperTail L)
          (Choice.support ω) (Choice.support ω) (envM (F.X hB hRR).data L ω)))
          (blockLift paperM0 _ paperTail L A) ≤
        (1 + sfEps (F.X hB hRR).data L) * selProd (F.X hB hRR).data L ω *
            (F.X hB hRR).data.Y L A +
          r0X (F.X hB hRR).data (sfEps (F.X hB hRR).data) L A ω (fun _ => false)) ∧
    ∃ c : ℝ, 0 ≤ c ∧
      Param.AtCounterexamples (Params.ofDecay TargetLedger.targetDecay) (F.X hB hRR).data.Y
        (fun L A => ∑ ω ∈ univ.filter (fun ω : Choice ((F.X hB hRR).data.CL.T L) => IsSelection ω),
          monomial ((F.X hB hRR).data.CL.πt L) ω *
            r0X (F.X hB hRR).data (sfEps (F.X hB hRR).data) L A ω (fun _ => false) ≤
          Comparison.remainder c L A) := by
  refine ⟨e1mu_of_sub (e1Sub_r0X _ _), ?_⟩
  obtain ⟨c₁, hc₁, h1⟩ := e1SubSmall_proved (F.X hB hRR).data paper_pairwise
    TargetLedger.targetDecay_nonneg
    (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (ThetaOne.paperAtomMap_paperBlockOf_surjective f1Cell)
  obtain ⟨c₂, hc₂, h2⟩ := e1CoupSmall_proved (F.X hB hRR).data paper_pairwise
    TargetLedger.targetDecay_nonneg
    (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
    (ThetaOne.paperAtomMap_paperBlockOf_surjective f1Cell)
  obtain ⟨c₃, hc₃, h3⟩ := e1Large_proved (F.X hB hRR).data TargetLedger.targetDecay_nonneg
  have hrem := e1RemX_of_split (F.X hB hRR).data (sfEps_nonneg _) h1 h2 h3
  exact ⟨c₁ + c₂ + c₃, add_nonneg (add_nonneg hc₁ hc₂) hc₃,
    sum_r0_empty_le hrem (r0X_nonneg _ _) (rX_nonneg _ _)⟩

/-- **`hres` at the obligations' data** (`hres_of_sub` at EC's `ε_E = u_L` and canonical
remainders `r0X`): the restoration field of a credit class follows from its eligible record laws,
(Cen) and (Res) alone; the remainder `γ₀ κ/(1 − κ) ∑_R r0X(ω, ∅)` is within the budget of
`e1mu_front`. -/
theorem hres_front (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) :
    HresFromRestoration (F.X hB hRR).data (sfEps (F.X hB hRR).data)
      (r0X (F.X hB hRR).data (sfEps (F.X hB hRR).data)) :=
  hres_of_sub (D := (F.X hB hRR).data) (e1Sub_r0X _ (sfEps _)) (r0X_nonneg _ _) (sfEps_nonneg _)

end Sarkozy.OpsVariance
