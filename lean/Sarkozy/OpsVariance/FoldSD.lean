module

public import Sarkozy.OpsVariance.HresFront

@[expose] public section

/-!
# Fold (Cen) at the obligations' data from PG's field `SD`

`paper/sections/21_middle_records.tex`, `lem:record:old-f-marginal`(c), (d),
`lem:record:conditional-collision`(d); `paper/sections/22_variance.tex`, `lem:var-gain` (Cen).

The obligations already carry PG's field `SD : SignedDecompInputsC` (`FrontK.SD`: the collision
bound, the signed decomposition, the component norms and the gates at every prime of every middle
block). Its gate gives a norm `ρ₀ ∈ [0, 1]` with `min(1, (Γ_p + e_{o,p} r_p) r_p) ≤ ρ₀` at every
prime, and its collision bound gives `‖T_old − 𝒥‖ ≤ (Γ_p + e_{o,p} r_p) r_p` (`centredNorm_old`).
So the fold (Cen) hypothesis `FoldCenAt ρ₀` of every middle block follows from `SD`, with no new
input; the variance credit still needs `κ < 1` above these `ρ₀` on the class (a numerical gate;
the paper's `ρ₀ = (Γ_A + e_o r_b) r_b` is of order `p^{-1/2}`).

* `FoldCenPr.mono`, `FoldCenAt.mono`;
* **`foldCenPr_of_decompGate`**: `FoldCenPr ρ₀` from PG's `DecompGateAtC` at a middle block;
* **`foldCenAt_of_specDecomp`**: the same per block specification (`SpecDecompC`);
* **`foldCenAt_front`**: at the obligations' data, every middle block `b` (site `.inl i`) has
  `FoldCenAt ρ₀ (specF hW A b)` for some `ρ₀ ∈ [0, 1]`, from `F.toK.SD`;
* `foldCenPr_lt_of_decompGate`, `paperSide_mem`, **`foldCenAt_lt_front`**: the gate is strict,
  `ρ₀ < 1`, since PG's gate gives `ρ₀² ≤ r d / H_𝔅` and at the paper's scale `r² b = 1`,
  `b ≥ 2²⁴`, `d ≤ 3`; **`foldCen_global_front`**: one `κ_F < 1` for all blocks;
* **`hres_fold_front`**: `hres` for a fold class at the obligations' data, given (Cen) at its
  blocks and only the restoration bound `hRes` (`lem:record:restoration`).
-/

open Finset

namespace Sarkozy.OpsVariance

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.FirstStagePaper
open Sarkozy.CancellationSteps (PaperJ0)
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes paperAtomMap)
open Sarkozy.SignedGram (CentredNorm mP oldP oldP_coupling mP_nonneg centredNorm_one)
open Sarkozy.SignedComponents (K0 FoldComponents)
open Sarkozy.PrimeGram (rP gammaP eoP CollisionBound DecompGateAtC SpecDecompC centredNorm_mono)
open Sarkozy.MainFinalF1 (bOf Blk SignedSpec specF)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg)

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

omit [Fintype ι] [DecidableEq ι] in
theorem FoldCenPr.mono {hne : MiddleNonempty pr} {κ κ' : ℝ} (h : FoldCenPr pr hne κ)
    (hle : κ ≤ κ') : FoldCenPr pr hne κ' := by
  obtain ⟨δ, h0, hc, hk⟩ := h
  exact ⟨δ, h0, hc, fun i => (hk i).trans hle⟩

/-- **Fold (Cen) at a middle block from PG's collision bounds and gates**, with the gate's
`ρ₀² ≤ σ = r d / H_𝔅`. -/
theorem foldCenPr_of_decompGate' (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (hne : MiddleNonempty pr) (C : FoldComponents pr hne) {r d : ℝ}
    (h : DecompGateAtC pr hne C r d) :
    ∃ ρ₀ : ℝ, 0 ≤ ρ₀ ∧ ρ₀ ≤ 1 ∧ ρ₀ ^ 2 ≤ r * d / SignedGram.Hblock pr ∧
      FoldCenPr pr hne ρ₀ := by
  obtain ⟨ccol, esg, cp, D, G⟩ := h
  obtain ⟨-, ρ₀, ρ₁, h0, h01, -, -, hρ₀, -, hs⟩ := G
  have ht : 0 ≤ (1 + tPaper) * ρ₁ ^ 2 :=
    mul_nonneg (by linarith [tPaper_nonneg]) (sq_nonneg _)
  refine ⟨ρ₀, h0, h01, by linarith, fun _ => ρ₀, fun _ => h0, fun i => ?_, fun _ => le_rfl⟩
  have hco := oldP_coupling hne
  have hrP : 0 ≤ rP pr i := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hδ : 0 ≤ (gammaP pr i + eoP pr ccol i * rP pr i) * rP pr i := by
    have := PrimeGram.eoP_nonneg h19 D.ccol_nonneg i
    have := PrimeGram.gammaP_nonneg h19 i
    positivity
  have hρ := hρ₀ i
  rcases le_total 1 ((gammaP pr i + eoP pr ccol i * rP pr i) * rP pr i) with hc | hc
  · rw [min_eq_left hc] at hρ
    exact centredNorm_mono (mP_nonneg hne i)
      (centredNorm_one (fun a b => (K0 (hne.F2 i)).nonneg _) (mP_nonneg hne i) (hco.row i)
        (hco.col i)) zero_le_one hρ
  · rw [min_eq_right hc] at hρ
    exact centredNorm_mono (mP_nonneg hne i) (centredNorm_old pr hne h3 h19 D.col i) hδ hρ

/-- **Fold (Cen) at a middle block from PG's collision bounds and gates**. -/
theorem foldCenPr_of_decompGate (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (hne : MiddleNonempty pr) (C : FoldComponents pr hne) {r d : ℝ}
    (h : DecompGateAtC pr hne C r d) : ∃ ρ₀ : ℝ, 0 ≤ ρ₀ ∧ ρ₀ ≤ 1 ∧ FoldCenPr pr hne ρ₀ := by
  obtain ⟨ρ₀, h0, h1, -, hf⟩ := foldCenPr_of_decompGate' pr h3 h19 hne C h
  exact ⟨ρ₀, h0, h1, hf⟩

omit [DecidableEq ι] [∀ i, Fact (pr i).Prime] in
theorem one_le_Hblock (h19 : ∀ i, 19 ≤ pr i) : 1 ≤ SignedGram.Hblock pr := by
  unfold SignedGram.Hblock
  apply one_le_prod₀
  intro i _
  have h5 : (5 : ℝ) ≤ (pr i : ℝ) := by
    have := h19 i
    exact_mod_cast (by omega : 5 ≤ pr i)
  have := SignedEstimates.e0_nonneg h5
  linarith

/-- **The fold gate is strict when the shift is small**: if `r d < 1`, then `ρ₀ < 1`. -/
theorem foldCenPr_lt_of_decompGate (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (hne : MiddleNonempty pr) (C : FoldComponents pr hne) {r d : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d)
    (hrd : r * d < 1) (h : DecompGateAtC pr hne C r d) :
    ∃ ρ₀ : ℝ, 0 ≤ ρ₀ ∧ ρ₀ < 1 ∧ FoldCenPr pr hne ρ₀ := by
  obtain ⟨ρ₀, h0, -, hsq, hf⟩ := foldCenPr_of_decompGate' pr h3 h19 hne C h
  have hH := one_le_Hblock pr h19
  have hσ : r * d / SignedGram.Hblock pr ≤ r * d :=
    div_le_self (mul_nonneg hr hd) hH
  refine ⟨ρ₀, h0, ?_, hf⟩
  nlinarith

end Frame

section Spec

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

omit [Fintype B] in
theorem FoldCenAt.mono {b : B} {κ κ' : ℝ} (S : PaperBlockSpec blockOf b) (h : FoldCenAt κ S)
    (hle : κ ≤ κ') : FoldCenAt κ' S := by
  cases S with
  | upper U => trivial
  | middleUniform M => exact FoldCenPr.mono _ (show FoldCenPr _ M.hne κ from h) hle
  | middleIndividual M => exact FoldCenPr.mono _ (show FoldCenPr _ M.hne κ from h) hle
  | middleCoherent M => exact FoldCenPr.mono _ (show FoldCenPr _ M.hne κ from h) hle

variable (hW : Target.Weil) (In : FirstStageInputs bOf)

/-- **Fold (Cen) of a block from PG's `SpecDecompC`**. -/
theorem foldCenAt_of_specDecomp {b : Blk} (d : ℝ) (S : PaperBlockSpec bOf b)
    (E : SignedSpec hW S) (h : SpecDecompC hW In d S E) :
    ∃ ρ₀ : ℝ, 0 ≤ ρ₀ ∧ ρ₀ ≤ 1 ∧ FoldCenAt ρ₀ S := by
  cases S with
  | upper U => exact ⟨0, le_rfl, zero_le_one, trivial⟩
  | middleUniform M =>
    exact foldCenPr_of_decompGate _ (fun i => (blockPrimes_mod_ge b i).1)
      (SignedComponents.blockPrimes_ge19 b) M.hne _ h
  | middleIndividual M =>
    exact foldCenPr_of_decompGate _ (fun i => (blockPrimes_mod_ge b i).1)
      (SignedComponents.blockPrimes_ge19 b) M.hne _ h
  | middleCoherent M =>
    exact foldCenPr_of_decompGate _ (fun i => (blockPrimes_mod_ge b i).1)
      (SignedComponents.blockPrimes_ge19 b) M.hne _ h

omit [Fintype B] [DecidableEq B] in
theorem sideTab_le (n : ℕ) : MiddleRefinement.sideTab.getD n 0 ≤ 30000000 := by
  have hall : ∀ x ∈ MiddleRefinement.sideTab, x ≤ 30000000 := by
    intro x hx
    simp only [MiddleRefinement.sideTab, List.mem_cons, List.not_mem_nil, or_false] at hx
    omega
  rw [List.getD_eq_getElem?_getD]
  cases h : MiddleRefinement.sideTab[n]? with
  | none => simp
  | some v =>
    simp only [Option.getD_some]
    exact hall v (List.mem_of_getElem? h)

omit [Fintype B] [DecidableEq B] in
/-- The chosen sides are in `[0, 3]` (they are `≈ 2.41`). -/
theorem paperSide_mem (i : Fin 33) :
    0 ≤ MiddleRefinement.paperSide i ∧ MiddleRefinement.paperSide i ≤ 3 := by
  unfold MiddleRefinement.paperSide MiddleRefinement.sideQ
  have h := sideTab_le i.val
  constructor
  · positivity
  · have h' : ((MiddleRefinement.sideTab.getD i.val 0 : ℕ) : ℝ) ≤ 30000000 := by exact_mod_cast h
    push_cast
    rw [div_le_iff₀ (by norm_num)]
    linarith

/-- **Fold (Cen) of a block from PG's `SpecDecompC`, with a strict gate**: at the paper's scale
`r² b = 1`, `b ≥ 2²⁴`, and a side `d ≤ 3`, the norm `ρ₀` is `< 1`. -/
theorem foldCenAt_lt_of_specDecomp {b : Blk} (d : ℝ) (hd0 : 0 ≤ d) (hd : d ≤ 3)
    (S : PaperBlockSpec bOf b) (E : SignedSpec hW S) (h : SpecDecompC hW In d S E)
    (hsc : GramBracketPaper.specScale In S) (hb : (2 : ℝ) ^ 24 ≤ In.bmin b) :
    ∃ ρ₀ : ℝ, 0 ≤ ρ₀ ∧ ρ₀ < 1 ∧ FoldCenAt ρ₀ S := by
  cases S with
  | upper U => exact ⟨0, le_rfl, zero_lt_one, trivial⟩
  | middleUniform M =>
    have hsc' : M.r ^ 2 * In.bmin b = 1 := hsc
    have hr : M.r * d < 1 := by nlinarith [M.hr]
    exact foldCenPr_lt_of_decompGate _ (fun i => (blockPrimes_mod_ge b i).1)
      (SignedComponents.blockPrimes_ge19 b) M.hne _ (r := M.r) M.hr hd0 hr h
  | middleIndividual M =>
    have hsc' : M.r ^ 2 * In.bmin b = 1 := hsc
    have hr : M.r * d < 1 := by nlinarith [M.hr]
    exact foldCenPr_lt_of_decompGate _ (fun i => (blockPrimes_mod_ge b i).1)
      (SignedComponents.blockPrimes_ge19 b) M.hne _ (r := M.r) M.hr hd0 hr h
  | middleCoherent M =>
    have hsc' : M.r ^ 2 * In.bmin b = 1 := hsc
    have hr : M.r * d < 1 := by nlinarith [M.hr]
    exact foldCenPr_lt_of_decompGate _ (fun i => (blockPrimes_mod_ge b i).1)
      (SignedComponents.blockPrimes_ge19 b) M.hne _ (r := M.r) M.hr hd0 hr h

end Spec

section Front

open Sarkozy.BlockSpecPaper (PaperAnalyticInputs paperIn blockSite)
open Sarkozy.MiddleRefinement (paperSide)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.CompanionND (CompanionFrontND)
open Sarkozy.UpperCapsPaper (UpperRecordTables)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **Fold (Cen) at every middle block from `SignedDecompInputsC`**. -/
theorem foldCenAt_of_SD {C : ComparisonPartsTC hW hMR hFour A}
    (G : PrimeGram.SignedDecompInputsC C) (b : Blk) (i : _) (hb : blockSite b = .inl i) :
    ∃ ρ₀ : ℝ, 0 ≤ ρ₀ ∧ ρ₀ ≤ 1 ∧ FoldCenAt ρ₀ (specF hW A b) :=
  foldCenAt_of_specDecomp hW (paperIn f1Cell) (paperSide i) (specF hW A b) (C.blk b)
    (G.decomp b i hb)

/-- **Fold (Cen) with a strict gate at every middle block**, from `SignedDecompInputsC`. -/
theorem foldCenAt_lt_of_SD {C : ComparisonPartsTC hW hMR hFour A}
    (G : PrimeGram.SignedDecompInputsC C) (b : Blk) (i : _) (hb : blockSite b = .inl i) :
    ∃ ρ₀ : ℝ, 0 ≤ ρ₀ ∧ ρ₀ < 1 ∧ FoldCenAt ρ₀ (specF hW A b) := by
  have h24 : (2 : ℝ) ^ 24 ≤ (paperIn f1Cell).bmin b := by
    show (2 : ℝ) ^ 24 ≤ (BlockSpecPaper.blockLeast b : ℝ)
    exact_mod_cast BlockSpecPaper.two_pow_24_le_blockLeast b
  exact foldCenAt_lt_of_specDecomp hW (paperIn f1Cell) (paperSide i) (paperSide_mem i).1
    (paperSide_mem i).2 (specF hW A b) (C.blk b) (G.decomp b i hb)
    (BlockSpecPaper.paperSpec_scale hW A b) h24

variable {UpT : UpperRecordTables}

/-- **Fold (Cen) at the obligations' data** (from the existing field `F.toK.SD`). -/
theorem foldCenAt_front (F : CompanionFrontND hW hMR hFour UpT) (b : Blk) (i : _)
    (hb : blockSite b = .inl i) :
    ∃ ρ₀ : ℝ, 0 ≤ ρ₀ ∧ ρ₀ ≤ 1 ∧
      FoldCenAt ρ₀ (specF hW (MainFinalF1.analyticInputs
        (F.toK.PCu.toPC2'.toPC hW hMR hFour) F.toK.BA) b) :=
  foldCenAt_of_SD F.toK.SD b i hb

/-- **Fold (Cen) at the obligations' data, with a strict gate** (from `F.toK.SD`): every middle
block has `FoldCenAt ρ₀` for some `ρ₀ < 1`. -/
theorem foldCenAt_lt_front (F : CompanionFrontND hW hMR hFour UpT) (b : Blk) (i : _)
    (hb : blockSite b = .inl i) :
    ∃ ρ₀ : ℝ, 0 ≤ ρ₀ ∧ ρ₀ < 1 ∧
      FoldCenAt ρ₀ (specF hW (MainFinalF1.analyticInputs
        (F.toK.PCu.toPC2'.toPC hW hMR hFour) F.toK.BA) b) :=
  foldCenAt_lt_of_SD F.toK.SD b i hb

/-- **One fold constant for the whole construction** (from `F.toK.SD`): some `κ_F < 1` is above
the prime centred norms of every middle block, so `FoldCenAt κ_F` holds at every block (upper
blocks trivially). The fold gate `κ < 1` of `hres_fold_front` is therefore satisfiable. -/
theorem foldCen_global_front (F : CompanionFrontND hW hMR hFour UpT) :
    ∃ κ : ℝ, 0 ≤ κ ∧ κ < 1 ∧ ∀ b : Blk,
      FoldCenAt κ (specF hW (MainFinalF1.analyticInputs
        (F.toK.PCu.toPC2'.toPC hW hMR hFour) F.toK.BA) b) := by
  classical
  have hb : ∀ b : Blk, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      FoldCenAt ρ (specF hW (MainFinalF1.analyticInputs
        (F.toK.PCu.toPC2'.toPC hW hMR hFour) F.toK.BA) b) := by
    intro b
    rcases h : blockSite b with i | k
    · exact foldCenAt_lt_front F b i h
    · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
      have key : ∀ (s : BlockSpecPaper.Site) (hs : blockSite b = s), s = .inr k →
          FoldCenAt (0 : ℝ) (BlockSpecPaper.siteSpec hW (MainFinalF1.analyticInputs
            (F.toK.PCu.toPC2'.toPC hW hMR hFour) F.toK.BA) b s hs) := by
        rintro s hs rfl
        exact True.intro
      exact key _ rfl h
  have hall : ∀ T : Finset Blk, ∃ κ : ℝ, 0 ≤ κ ∧ κ < 1 ∧ ∀ b ∈ T,
      FoldCenAt κ (specF hW (MainFinalF1.analyticInputs
        (F.toK.PCu.toPC2'.toPC hW hMR hFour) F.toK.BA) b) := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨0, le_rfl, zero_lt_one, fun b hb => absurd hb (notMem_empty b)⟩
    | insert a T _ ih =>
      obtain ⟨κ, hκ0, hκ1, hκ⟩ := ih
      obtain ⟨ρ, hρ0, hρ1, hρ⟩ := hb a
      refine ⟨max κ ρ, le_max_of_le_left hκ0, max_lt hκ1 hρ1, fun b hbT => ?_⟩
      rcases mem_insert.mp hbT with rfl | hbT
      · exact FoldCenAt.mono _ hρ (le_max_right _ _)
      · exact FoldCenAt.mono _ (hκ b hbT) (le_max_left _ _)
  obtain ⟨κ, hκ0, hκ1, hκ⟩ := hall univ
  exact ⟨κ, hκ0, hκ1, fun b => hκ b (mem_univ b)⟩

open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.Variance Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.EnvelopeSteps
open Sarkozy.CancellationSteps (paperM0 paperTail)
open Sarkozy.E1Closure (r0X)
open Sarkozy.SharpFirst (sfEps)
open Sarkozy.Param (Params)

/-- **`hres` for a fold class at the obligations' data** (`cor:var-classes`(i)): at every least
counterexample, for a selection `ω` with support `X` whose records are fold records (`InFold`),
with (Cen) `FoldCenAt κ` at its middle blocks (from `foldCenAt_front` and `FoldCenAt.mono` when
`κ` is above their `ρ₀`) and `κ < 1`, `hres` holds with the record laws `Π_{F_j}`
(`wSel … wFold`), given only the restoration bound `hRes` (`lem:record:restoration`). -/
theorem hres_fold_front (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) :
    Param.AtCounterexamples (Params.ofDecay TargetLedger.targetDecay) (F.X hB hRR).data.Y
      (fun L A => ∀ ω : Choice ((F.X hB hRR).data.CL.T L), IsSelection ω →
        (∀ b t e, ω b = some (t, e) → InFold (F.toK.Up.toCmp hMR hFour) L b t) →
        ∀ X, Choice.support ω = X →
        ∀ κ : ℝ, 0 ≤ κ → κ < 1 →
        (∀ b' : Blk, (.inl (.inr b') : BlockAtom _ _ L) ∈ X →
          FoldCenAt κ (specF hW (MainFinalF1.analyticInputs
            (F.toK.PCu.toPC2'.toPC hW hMR hFour) F.toK.BA) b')) →
        ∀ (C l₀ z₁ z : ℝ),
        1 ≤ selProd (F.X hB hRR).data L ω → selProd (F.X hB hRR).data L ω ≤ C → 0 ≤ z₁ →
        (z₁ + κ * sfEps (F.X hB hRR).data L) / (1 - κ) ≤ z →
        (l₀ - z₁) * (F.X hB hRR).data.Y L A ≤ energyX (F.X hB hRR).data L A X
          (wSel (F.toK.Up.toCmp hMR hFour) L (wFold (F.toK.Up.toCmp hMR hFour) L) ω) →
        (gainBar l₀ C κ - z) * monomial ((F.X hB hRR).data.CL.π L) ω *
            (F.X hB hRR).data.Y L A -
          monomial ((F.X hB hRR).data.CL.πt L) ω * (κ / (1 - κ)) *
            r0X (F.X hB hRR).data (sfEps (F.X hB hRR).data) L A ω (fun _ => false) ≤
        monomial ((F.X hB hRR).data.CL.πt L) ω *
          varJ0 (F.X hB hRR).data L A ω (envM (F.X hB hRR).data L ω)) := by
  filter_upwards [hres_front_laws F hB hRR] with L hL
  intro C' hC' hind A hA hcount ω hs hf X hX κ hκ0 hκ1 hcen C l₀ z₁ z hCX hC hz₁ hz hRes
  set Cm := F.toK.Up.toCmp hMR hFour
  have hsp : selProd (F.X hB hRR).data L ω =
      ∏ b ∈ X,
        selectionFactor TargetLedger.targetDecay paperTail (F.X hB hRR).data.S.selPre L b := by
    unfold selProd
    rw [hX]
  rw [hsp] at hCX hC
  have h := hL C' hC' hind A hA hcount {ω} (singleton_nonempty ω)
    (fun ω' hω' => by rw [mem_singleton.mp hω']; exact hs) X
    (fun ω' hω' => by rw [mem_singleton.mp hω']; exact hX) (monomial _ ω)
    (fun ω' hω' => by rw [mem_singleton.mp hω'])
    (fun ω' => wSel Cm L (wFold Cm L) ω') (fun _ _ => κ)
    (fun ω' hω' b hb t e hωb => by
      rw [mem_singleton.mp hω'] at hωb ⊢
      exact recordLawIs_wSel_fold Cm L ω b t e hωb (hf b t e hωb) hκ0 hκ1.le
        (fun b' hb' => hcen b' (hb' ▸ hb)))
    κ hκ0 hκ1 (fun _ _ _ _ => le_rfl) C l₀ z₁ z hCX hC hz₁ hz
    (by rw [card_singleton, sum_singleton, recFam_self]; push_cast; rw [mul_one]; exact hRes)
  simpa only [sum_singleton] using h

end Front

end Sarkozy.OpsVariance
