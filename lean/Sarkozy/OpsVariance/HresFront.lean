module

public import Sarkozy.OpsVariance.FrontCredit
public import Sarkozy.OpsVariance.AlignedRes
public import Sarkozy.OpsVariance.FoldFront

@[expose] public section

/-!
# `hres` at the obligations' data from the record laws: aligned matchings and folds

`paper/sections/22_variance.tex`, `lem:var-gain`(a), `cor:var-classes`(i), (ii),
`lem:record:paired-e-joint`(b), `lem:record:restoration`.

`hres_front` (`FrontCredit`) gives `hres` at the obligations' data from five record-law inputs,
(Cen) and (Res), with (E1) already discharged by EC. Here the record-law inputs and (Cen) are
discharged at the paper's records, so only (Res) is left:

* `HresFromRecordLaws`, **`hresFromRecordLaws`**: `HresFromRestoration` with the five inputs
  replaced by `RecordLawIs`; **`hres_front_laws`** at the obligations' data;
* `wMatch`, `wFold`, `wSel`, `κE`: the matching / fold record laws of a choice at the paper's
  comparison law, and the matching constant `3/(b − 3)`;
* **`recordLawIs_wSel_match`**, **`recordLawIs_wSel_fold`**: they are record laws;
* **`hres_aligned_front`**: `hres` for an aligned matching pair at the obligations' data, given
  only the polarization order `hord`, the fold restorations `hF` and the merge bounds `hMg`;
* **`hres_fold_front`**: `hres` for a fold class `{ω}`, given (Cen) per block (`FoldCenAt`,
  e.g. from PG's collision bounds) and the restoration bound `hRes`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.TheoremCBlock Sarkozy.CancellationSteps Sarkozy.BlockFrame
open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC
  Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.EnvelopeSteps Sarkozy.Variance
open Sarkozy.Param (Params)
open Sarkozy.CompanionND (CompanionFrontND)
open Sarkozy.UpperCapsPaper (UpperRecordTables)

section Generic

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The restoration field from record laws, (Cen) and (Res)**: `HresFromRestoration` with the
record-law inputs `hw`, `hp`, `hn`, `ht`, `hcen` replaced by `RecordLawIs`. -/
def HresFromRecordLaws (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (εE : ℕ → ℝ)
    (r0 : Companion.E1R0 D) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    ∀ (R : Finset (Choice (D.CL.T L))), R.Nonempty → (∀ ω ∈ R, IsSelection ω) →
    ∀ (X : Finset (BlockAtom Bk J L)), (∀ ω ∈ R, Choice.support ω = X) →
    ∀ (γ₀ : ℝ), (∀ ω ∈ R, monomial (D.CL.πt L) ω = γ₀) →
    ∀ (w : Choice (D.CL.T L) → ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ)
      (κj : Choice (D.CL.T L) → BlockAtom Bk J L → ℝ),
    (∀ ω ∈ R, ∀ b ∈ X, ∀ t e, ω b = some (t, e) → RecordLawIs (w ω b) (D.CL.D L b t) (κj ω b)) →
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
theorem hresFromRecordLaws {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {εE : ℕ → ℝ}
    {r0 : Companion.E1R0 D} (H : HresFromRestoration D εE r0) : HresFromRecordLaws D εE r0 := by
  filter_upwards [H] with L hL
  intro C' hC' hind A hA hcount R hR hsel X hX γ₀ hγ w κj hrec κ hκ0 hκ1 hκ C l₀ z₁ z hCX hC
    hz₁ hz hRes
  have key : ∀ ω ∈ R, ∀ b ∈ X, (∀ z, 0 ≤ w ω b z) ∧
      plusMarginal reservedCut (w ω b) = envM D L ω b ∧
      minusMarginal reservedCut (w ω b) = envM D L ω b ∧
      (∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ,
        reservedCut.form (signedIntegral (w ω b)) G H =
          reservedCut.form (signedIntegral (w ω b)) H G) ∧
      CentredNormLe reservedCut (signedIntegral (w ω b)) (envM D L ω b) (κj ω b) :=
    fun ω hω b hb => by
      obtain ⟨t, e, hωb⟩ := exists_of_mem_support ω (b := b) (by rw [hX ω hω]; exact hb)
      exact recordLaw_inputs ω hωb (hrec ω hω b hb t e hωb)
  exact hL C' hC' hind A hA hcount R hR hsel X hX γ₀ hγ w (fun ω hω b hb => (key ω hω b hb).1)
    (fun ω hω b hb => (key ω hω b hb).2.1) (fun ω hω b hb => (key ω hω b hb).2.2.1)
    (fun ω hω b hb => (key ω hω b hb).2.2.2.1) κj (fun ω hω b hb => (key ω hω b hb).2.2.2.2)
    κ hκ0 hκ1 hκ C l₀ z₁ z hCX hC hz₁ hz hRes

end Generic

/-! ## At the obligations' data -/

open Sarkozy.MainFinalF1 (ComparisonParts bOf specF Blk)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.PartVLaws (paperAtomMap PaperAtom)
open Sarkozy.E1Closure (r0X)
open Sarkozy.SharpFirst (sfEps)
open Sarkozy.EnvelopeInputs Sarkozy.Functional
open Sarkozy.BlockSpecPaper (PaperAnalyticInputs blockLeast)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperRecordTables}

/-- **`hres` from record laws at the obligations' data** (`hres_front` through
`hresFromRecordLaws`). -/
theorem hres_front_laws (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) :
    HresFromRecordLaws (F.X hB hRR).data (sfEps (F.X hB hRR).data)
      (r0X (F.X hB hRR).data (sfEps (F.X hB hRR).data)) :=
  hresFromRecordLaws (hres_front F hB hRR)

section Laws

variable {A : PaperAnalyticInputs AnalyticCells.f1Cell}

/-- The matching record law of a record of the comparison law (`0` off the middle blocks). -/
noncomputable def wMatch (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) :
    (b : BlockAtom (PaperAtom Blk) PaperJt L) → C.toK1.CL.T L b →
      (Slot → BlockFrame.BlockLabel paperM0 (paperAtomMap bOf) paperTail L b) → ℝ
  | .inl (.inr b), t => matchLawCL C L b t
  | _, _ => fun _ => 0

/-- The fold record law of a record of the comparison law (`0` off the middle blocks). -/
noncomputable def wFold (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) :
    (b : BlockAtom (PaperAtom Blk) PaperJt L) → C.toK1.CL.T L b →
      (Slot → BlockFrame.BlockLabel paperM0 (paperAtomMap bOf) paperTail L b) → ℝ
  | .inl (.inr b), t => foldLawCL C L b t
  | _, _ => fun _ => 0

/-- The record law of the record selected by a choice at an atom (`0` where none is). -/
noncomputable def wSel (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ)
    (wr : (b : BlockAtom (PaperAtom Blk) PaperJt L) → C.toK1.CL.T L b →
      (Slot → BlockFrame.BlockLabel paperM0 (paperAtomMap bOf) paperTail L b) → ℝ)
    (ω : Choice (C.toK1.CL.T L)) (b : BlockAtom (PaperAtom Blk) PaperJt L) :
    (Slot → BlockFrame.BlockLabel paperM0 (paperAtomMap bOf) paperTail L b) → ℝ :=
  match ω b with
  | some (t, _) => wr b t
  | none => fun _ => 0

/-- The matching constant `3/(b − 3)` of a middle block (`0` at the other atoms). -/
noncomputable def κE (L : ℕ) : BlockAtom (PaperAtom Blk) PaperJt L → ℝ
  | .inl (.inr b) => 3 / ((blockLeast b : ℝ) - 3)
  | _ => 0

/-- **The matching gate is automatic**: `κ_E(𝔅) = 3/(b − 3) ≤ 3/4` at every atom (`b ≥ 7`), so
`κ = 3/4` (or the largest `3/(b − 3)` on the class) satisfies `κ < 1`. -/
theorem κE_le (L : ℕ) (b : BlockAtom (PaperAtom Blk) PaperJt L) : κE L b ≤ 3 / 4 := by
  rcases b with (q | b) | j
  · show (0 : ℝ) ≤ 3 / 4
    norm_num
  · show 3 / ((blockLeast b : ℝ) - 3) ≤ 3 / 4
    have h7 : (7 : ℝ) ≤ blockLeast b := by exact_mod_cast (blockLeast_facts' b).1
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  · show (0 : ℝ) ≤ 3 / 4
    norm_num

theorem κE_nonneg (L : ℕ) (b : BlockAtom (PaperAtom Blk) PaperJt L) : 0 ≤ κE L b := by
  rcases b with (q | b) | j
  · exact le_rfl
  · show 0 ≤ 3 / ((blockLeast b : ℝ) - 3)
    have h7 : (7 : ℝ) ≤ blockLeast b := by exact_mod_cast (blockLeast_facts' b).1
    exact div_nonneg (by norm_num) (by linarith)
  · exact le_rfl

/-- The fold records of the comparison law: `foldCL` at the middle blocks. -/
def InFold (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) :
    (b : BlockAtom (PaperAtom Blk) PaperJt L) → C.toK1.CL.T L b → Prop
  | .inl (.inr b), t => t ∈ foldCL C L b
  | _, _ => False

/-- **The matching record laws of a choice are record laws** with `κ = 3/(b − 3)`. -/
theorem recordLawIs_wSel_match (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ)
    (ω : Choice (C.toK1.CL.T L)) (b : BlockAtom (PaperAtom Blk) PaperJt L) (t : C.toK1.CL.T L b)
    (e : ChangeType) (hωb : ω b = some (t, e)) (hm : InMatch C L b t) :
    RecordLawIs (wSel C L (wMatch C L) ω b) (C.toK1.CL.D L b t) (κE L b) := by
  unfold wSel
  rw [hωb]
  rcases b with (q | b) | j
  · exact absurd hm id
  · exact matchRecord_CL C L b t hm
  · exact absurd hm id

/-- **The fold record laws of a choice are record laws**, given (Cen) at its blocks. -/
theorem recordLawIs_wSel_fold (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ)
    (ω : Choice (C.toK1.CL.T L)) (b : BlockAtom (PaperAtom Blk) PaperJt L) (t : C.toK1.CL.T L b)
    (e : ChangeType) (hωb : ω b = some (t, e)) (hf : InFold C L b t) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ1 : κ ≤ 1) (hcen : ∀ b' : Blk, b = .inl (.inr b') → FoldCenAt κ (specF hW A b')) :
    RecordLawIs (wSel C L (wFold C L) ω b) (C.toK1.CL.D L b t) κ := by
  unfold wSel
  rw [hωb]
  rcases b with (q | b) | j
  · exact absurd hf id
  · exact foldRecord_CL C L b hκ0 hκ1 (hcen b rfl) t hf
  · exact absurd hf id

/-- **`hres` for an aligned matching pair at the obligations' data** (`cor:var-classes`(ii)):
at every least counterexample, for two selections `ω₀ ≠ ω₁` with support `X`, the same change
types and matching records at every block (`InMatch`), with `κ < 1` above `3/(b − 3)` on `X`,
`hres` holds at `l₀ − C ε − z_m ε C` with the record laws `Π_{E_s}` (`wSel … wMatch`), given only
the polarization order `hord` (`lem:record:paired-e-joint`(a)), the fold restorations `hF`
(`lem:record:restoration`, `j = 1, 2`) and the merge bounds `hMg` ((E1)). The common price is
`alignedPrice_front`; (E1) for the diagonals and its remainders are EC's (`hres_front`). -/
theorem hres_aligned_front (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) :
    Param.AtCounterexamples (Params.ofDecay TargetLedger.targetDecay) (F.X hB hRR).data.Y
      (fun L A => ∀ ω₀ ω₁ : Choice ((F.X hB hRR).data.CL.T L), ω₀ ≠ ω₁ → IsSelection ω₀ →
        IsSelection ω₁ →
        (∀ b, (ω₀ b = none ∧ ω₁ b = none) ∨ ∃ t₀ t₁ e, ω₀ b = some (t₀, e) ∧
          ω₁ b = some (t₁, e) ∧ InMatch (F.toK.Up.toCmp hMR hFour) L b t₀ ∧
          InMatch (F.toK.Up.toCmp hMR hFour) L b t₁) →
        ∀ X, Choice.support ω₀ = X → Choice.support ω₁ = X →
        ∀ κ : ℝ, 0 ≤ κ → κ < 1 → (∀ b ∈ X, κE L b ≤ κ) →
        ∀ (wF wA : Fin 2 → ∀ b, (Slot → BlockFrame.BlockLabel paperM0 (paperAtomMap bOf)
          paperTail L b) → ℝ) (C ε l₀ z₁ z zm : ℝ),
        1 ≤ selProd (F.X hB hRR).data L ω₀ → selProd (F.X hB hRR).data L ω₀ ≤ C → 0 ≤ ε →
        0 ≤ zm → 0 ≤ z₁ → (z₁ + κ * sfEps (F.X hB hRR).data L) / (1 - κ) ≤ z →
        energyX (F.X hB hRR).data L A X (wF 0) + energyX (F.X hB hRR).data L A X (wF 1) ≤
          energyX (F.X hB hRR).data L A X (wA 0) + energyX (F.X hB hRR).data L A X (wA 1) →
        (∀ j, (l₀ - z₁) * (F.X hB hRR).data.Y L A ≤ energyX (F.X hB hRR).data L A X (wF j)) →
        energyX (F.X hB hRR).data L A X (wA 0) -
            energyX (F.X hB hRR).data L A X
              (wSel (F.toK.Up.toCmp hMR hFour) L (wMatch (F.toK.Up.toCmp hMR hFour) L) ω₀) ≤
          (1 + zm) * ε * selProd (F.X hB hRR).data L ω₀ * (F.X hB hRR).data.Y L A →
        energyX (F.X hB hRR).data L A X (wA 1) -
            energyX (F.X hB hRR).data L A X
              (wSel (F.toK.Up.toCmp hMR hFour) L (wMatch (F.toK.Up.toCmp hMR hFour) L) ω₁) ≤
          (1 + zm) * ε * selProd (F.X hB hRR).data L ω₀ * (F.X hB hRR).data.Y L A →
        (gainBar (l₀ - C * ε - zm * ε * C) C κ - z) *
            (∑ ω ∈ ({ω₀, ω₁} : Finset _), monomial ((F.X hB hRR).data.CL.π L) ω) *
            (F.X hB hRR).data.Y L A -
          monomial ((F.X hB hRR).data.CL.πt L) ω₀ * (κ / (1 - κ)) *
            ∑ ω ∈ ({ω₀, ω₁} : Finset _),
              r0X (F.X hB hRR).data (sfEps (F.X hB hRR).data) L A ω (fun _ => false) ≤
        ∑ ω ∈ ({ω₀, ω₁} : Finset _), monomial ((F.X hB hRR).data.CL.πt L) ω *
          varJ0 (F.X hB hRR).data L A ω (envM (F.X hB hRR).data L ω)) := by
  filter_upwards [hres_front_laws F hB hRR] with L hL
  intro C' hC' hind A hA hcount ω₀ ω₁ h01 hs0 hs1 hal X hX0 hX1 κ hκ0 hκ1 hκ wF wA C ε l₀ z₁ z
    zm hCX hC hε hzm hz₁ hz hord hF hMg0 hMg1
  have hY : 0 ≤ (F.X hB hRR).data.Y L A := (TheoremCParam.counterexample_pos hC' hcount).le
  set Cm := F.toK.Up.toCmp hMR hFour
  have hX : ∀ ω ∈ ({ω₀, ω₁} : Finset _), Choice.support ω = X := by
    intro ω hω
    rcases mem_insert.mp hω with rfl | hω
    · exact hX0
    · rw [mem_singleton.mp hω]; exact hX1
  have hsp : selProd (F.X hB hRR).data L ω₀ =
      ∏ b ∈ X,
        selectionFactor TargetLedger.targetDecay paperTail (F.X hB hRR).data.S.selPre L b := by
    unfold selProd
    rw [hX0]
  have hrec : ∀ ω ∈ ({ω₀, ω₁} : Finset _), ∀ b ∈ X, ∀ t e, ω b = some (t, e) →
      RecordLawIs (wSel Cm L (wMatch Cm L) ω b) ((F.X hB hRR).data.CL.D L b t) (κE L b) := by
    intro ω hω b _ t e hωb
    rcases mem_insert.mp hω with rfl | hω
    · rcases hal b with ⟨h0, -⟩ | ⟨t₀, t₁, e', h0, -, m0, -⟩
      · rw [h0] at hωb; exact absurd hωb (by simp)
      · rw [h0] at hωb
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hωb).symm
        exact recordLawIs_wSel_match Cm L ω b _ e' h0 m0
    · rw [mem_singleton.mp hω] at hωb ⊢
      rcases hal b with ⟨-, h1⟩ | ⟨t₀, t₁, e', -, h1, -, m1⟩
      · rw [h1] at hωb; exact absurd hωb (by simp)
      · rw [h1] at hωb
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hωb).symm
        exact recordLawIs_wSel_match Cm L ω₁ b _ e' h1 m1
  have hγ : ∀ ω ∈ ({ω₀, ω₁} : Finset _),
      monomial ((F.X hB hRR).data.CL.πt L) ω = monomial ((F.X hB hRR).data.CL.πt L) ω₀ := by
    intro ω hω
    rcases mem_insert.mp hω with rfl | hω
    · rfl
    · rw [mem_singleton.mp hω]
      exact (alignedPrice_front F hB hRR L ω₀ ω₁ hal).symm
  have hsel : ∀ ω ∈ ({ω₀, ω₁} : Finset _), IsSelection ω := by
    intro ω hω
    rcases mem_insert.mp hω with rfl | hω
    · exact hs0
    · rw [mem_singleton.mp hω]; exact hs1
  rw [hsp] at hCX hC hMg0 hMg1
  exact hL C' hC' hind A hA hcount {ω₀, ω₁} (insert_nonempty _ _) hsel X hX _ hγ
    (fun ω => wSel Cm L (wMatch Cm L) ω) (fun _ b => κE L b) hrec κ hκ0 hκ1
    (fun _ _ b hb => hκ b hb) C _ z₁ z hCX hC hz₁ hz
    (hRes_aligned ω₀ ω₁ h01 X _ wF wA hY hC hε hzm hord hF hMg0 hMg1)

end Laws

end Sarkozy.OpsVariance
