module

public import Sarkozy.E1Closure.Split
public import Sarkozy.E1Closure.Tools

@[expose] public section

/-!
# The atom data of the (E1) terms for `lem:record:density-lp` (EC)

EC, 8 November 2026. Each (E1) term is a tensor over the atoms, and every factor depends on the
atom only through the local choices `o = ω_𝔟` (selection), `s = σ_𝔟` (first stage) and the
local piece. Here:

* `cK`, `cDom`, `ccoef`: the local coupled law, a dominating positive record (`κ' + κ` for the
  whole difference `κ' − κ`) and the local coefficient; `ecpieceK_eq`, `ecpieceCoef_eq`;
* `compat`, **`sum_abs_ccoef_le`**: a piece is used by at most one local first-stage choice,
  `∑_s |c(o, s, x)| ≤ compat(o, x) ∈ {0, 1}`;
* positivity, domination and masses of the local laws (`subLaw`, `cDom`);
* **`subAtom_le`**, **`coupAtom_le`**: the per-atom Rankin sums are at most `1 + 2 q_𝔟^{1/4} Pr_𝔟`,
  with LP's `atomPr` at the wrapping increment `∑_t (π̃^s_t D^s_t + π̃^a_t D^a_t)` (whose mass is
  the selection price `∑_{t,ε} π̃^ε_t`).
-/

namespace Sarkozy.E1Closure

open Finset Function
open scoped BigOperators
open Sarkozy.EnvelopeInputsBlock Sarkozy.EnvelopeInputs
open Sarkozy.BlockFrame
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.Structured ReflectionCut
open Sarkozy.LargeSums (atomQR atomQR_nonneg atomPr)
open Sarkozy.DensityChain (isPositiveRecord_add isPositiveRecord_sum isPositiveRecord_zero)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)

/-! ## Local laws and coefficients -/

/-- The local coupled law (`ecpieceK` at `ω_𝔟 = o`). -/
noncomputable def cK (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) :
    CEPiece D L b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => entryFactor (D.R.law p L b) (D.CL.D L b) o
  | Sum.inl (some i) => D.GB.κu L b i
  | Sum.inr (i, none) => D.FS.κ' L b i - D.FS.κ L b i
  | Sum.inr (i, some t) => if t then D.FS.κ' L b i else D.FS.κ L b i

/-- The dominating positive record of a local coupled law: `κ' + κ` for the whole difference. -/
noncomputable def cDom (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) :
    CEPiece D L b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => entryFactor (D.R.law p L b) (D.CL.D L b) o
  | Sum.inl (some i) => D.GB.κu L b i
  | Sum.inr (i, none) => D.FS.κ' L b i + D.FS.κ L b i
  | Sum.inr (i, some t) => if t then D.FS.κ' L b i else D.FS.κ L b i

/-- The local coefficient (`ecpieceCoef` at `ω_𝔟 = o`, `σ_𝔟 = s`). -/
noncomputable def ccoef (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (s : Option (D.FS.Ib L b)) (j : D.FS.Tag) : CEPiece D L b → ℝ
  | Sum.inl none => if s = none then 1 else 0
  | Sum.inl (some _) => if s = none ∧ o = none then 1 else 0
  | Sum.inr (i, none) => if s = some i ∧ D.FS.tag L b i = j ∧ o = none then 1 else 0
  | Sum.inr (i, some t) =>
      if s = some i ∧ D.FS.tag L b i ≠ j ∧ o = none then (if t then 1 else -1) else 0

/-- The first-stage choice that a piece requires: `none` for the entry factor and the bracket
records, `some i` for the pieces of the difference `i`. -/
def sReq (b : BlockAtom Bk J L) : CEPiece D L b → Option (D.FS.Ib L b)
  | Sum.inl _ => none
  | Sum.inr (i, _) => some i

/-- Whether a piece is compatible with the local selection `o`: the entry factor always, the
other pieces only off the selected set. -/
noncomputable def compat (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) :
    CEPiece D L b → ℝ
  | Sum.inl none => 1
  | _ => if o = none then 1 else 0

omit [DecidableEq P] in
theorem ecpieceK_eq (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) (x : CEPiece D L b) :
    ecpieceK D L ω b x = cK D L b (ω b) x := by
  rcases x with (_ | i) | ⟨i, _ | t⟩ <;> rfl

omit [DecidableEq P] in
theorem ecpieceCoef_eq (ω : Choice (D.CL.T L)) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (b : BlockAtom Bk J L) (x : CEPiece D L b) :
    ecpieceCoef D L ω σ j b x = ccoef D L b (ω b) (σ b) j x := by
  rcases x with (_ | i) | ⟨i, _ | t⟩ <;> rfl

omit [DecidableEq P] in
theorem ccoef_eq_zero (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (s : Option (D.FS.Ib L b)) (j : D.FS.Tag) (x : CEPiece D L b) (hs : s ≠ sReq D L b x) :
    ccoef D L b o s j x = 0 := by
  rcases x with (_ | i) | ⟨i, _ | t⟩ <;> simp_all [ccoef, sReq]

omit [DecidableEq P] in
theorem abs_ccoef_le (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (s : Option (D.FS.Ib L b)) (j : D.FS.Tag) (x : CEPiece D L b) :
    |ccoef D L b o s j x| ≤ compat D L b o x := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · unfold ccoef compat
    split_ifs <;> norm_num
  · unfold ccoef compat
    split_ifs <;> simp_all
  · unfold ccoef compat
    by_cases ho : o = none
    · simp only [ho, and_true, ↓reduceIte]
      split_ifs <;> norm_num
    · simp [ho]
  · unfold ccoef compat
    by_cases ho : o = none
    · simp only [ho, and_true, ↓reduceIte]
      split_ifs <;> norm_num
    · simp [ho]

omit [DecidableEq P] in
/-- **A piece is used by at most one local first-stage choice.** -/
theorem sum_abs_ccoef_le (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (j : D.FS.Tag) (x : CEPiece D L b) :
    ∑ s, |ccoef D L b o s j x| ≤ compat D L b o x := by
  rw [sum_eq_single (sReq D L b x) (fun s _ hs => by rw [ccoef_eq_zero D L b o s j x hs,
    abs_zero]) (by simp)]
  exact abs_ccoef_le D L b o _ j x

omit [DecidableEq P] in
theorem compat_nonneg (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType))
    (x : CEPiece D L b) : 0 ≤ compat D L b o x := by
  rcases x with (_ | i) | ⟨i, _ | t⟩ <;> unfold compat <;> split_ifs <;> norm_num

/-! ## Positivity, domination, masses -/

omit [DecidableEq P] in
theorem lawDensity_nonneg {X : Type} [Fintype X] [DecidableEq X] {κ : SlotMeasure X}
    (hκ : IsNonneg κ) (z : Slot → X) : 0 ≤ lawDensity κ z :=
  hκ _ fun y => by split_ifs <;> norm_num

omit [DecidableEq P] in
theorem isPositiveRecord_entryFactor (hp : ∀ j, (p L j).Prime) (b : BlockAtom Bk J L)
    (o : Option (D.CL.T L b × ChangeType)) :
    IsPositiveRecord (entryFactor (D.R.law p L b) (D.CL.D L b) o) := by
  rcases o with _ | ⟨t, e⟩
  · exact Sarkozy.DensityChain.isPositiveRecord_muLaw D L hp b
  · exact ⟨(D.CL.D_prob L b t e).1, D.CL.D_unif L b t e⟩

omit [DecidableEq P] in
theorem mass_entryFactor (b : BlockAtom Bk J L) (o : Option (D.CL.T L b × ChangeType)) :
    mass (entryFactor (D.R.law p L b) (D.CL.D L b) o) = 1 := by
  rcases o with _ | ⟨t, e⟩
  · exact Sarkozy.LargeSums.mass_refLaw D L b
  · exact (D.CL.D_prob L b t e).2

omit [DecidableEq P] in
theorem isPositiveRecord_subLaw (hp : ∀ j, (p L j).Prime) (b : BlockAtom Bk J L)
    (o : Option (D.CL.T L b × ChangeType)) (y : Bool) : IsPositiveRecord (subLaw D L b o y) := by
  unfold subLaw
  split_ifs
  · exact isPositiveRecord_zero
  · exact isPositiveRecord_sum _ _ fun i _ => D.GB.κu_pos L b i
  · exact isPositiveRecord_entryFactor D L hp b o

omit [DecidableEq P] in
theorem isPositiveRecord_cDom (hp : ∀ j, (p L j).Prime) (b : BlockAtom Bk J L)
    (o : Option (D.CL.T L b × ChangeType)) (x : CEPiece D L b) :
    IsPositiveRecord (cDom D L b o x) := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · exact isPositiveRecord_entryFactor D L hp b o
  · exact D.GB.κu_pos L b i
  · exact isPositiveRecord_add (D.FS.κ'_pos L b i) (D.FS.κ_pos L b i)
  · cases t
    · exact D.FS.κ_pos L b i
    · exact D.FS.κ'_pos L b i

omit [DecidableEq P] in
theorem cK_dom (hp : ∀ j, (p L j).Prime) (b : BlockAtom Bk J L)
    (o : Option (D.CL.T L b × ChangeType)) (x : CEPiece D L b)
    (z : Slot → BlockLabel m₀ blk p L b) :
    |lawDensity (cK D L b o x) z| ≤ lawDensity (cDom D L b o x) z := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · exact le_of_eq (abs_of_nonneg (lawDensity_nonneg
      (isPositiveRecord_entryFactor D L hp b o).1 z))
  · exact le_of_eq (abs_of_nonneg (lawDensity_nonneg (D.GB.κu_pos L b i).1 z))
  · have h1 := lawDensity_nonneg (D.FS.κ'_pos L b i).1 z
    have h2 := lawDensity_nonneg (D.FS.κ_pos L b i).1 z
    change |lawDensity (D.FS.κ' L b i) z - lawDensity (D.FS.κ L b i) z| ≤
      lawDensity (D.FS.κ' L b i) z + lawDensity (D.FS.κ L b i) z
    rw [abs_le]
    constructor <;> linarith
  · cases t
    · exact le_of_eq (abs_of_nonneg (lawDensity_nonneg (D.FS.κ_pos L b i).1 z))
    · exact le_of_eq (abs_of_nonneg (lawDensity_nonneg (D.FS.κ'_pos L b i).1 z))

omit [DecidableEq P] in
theorem subLaw_dom (hp : ∀ j, (p L j).Prime) (b : BlockAtom Bk J L)
    (o : Option (D.CL.T L b × ChangeType)) (y : Bool) (z : Slot → BlockLabel m₀ blk p L b) :
    |lawDensity (subLaw D L b o y) z| ≤ lawDensity (subLaw D L b o y) z :=
  le_of_eq (abs_of_nonneg (lawDensity_nonneg (isPositiveRecord_subLaw D L hp b o y).1 z))

omit [DecidableEq P] in
theorem mass_sum_measure {X : Type} [Fintype X] {I : Type} [Fintype I] (κ : I → SlotMeasure X) :
    mass (∑ i, κ i) = ∑ i, mass (κ i) := by
  unfold mass
  rw [LinearMap.sum_apply]

omit [DecidableEq P] in
theorem mass_wrapInc (b : BlockAtom Bk J L) :
    mass (TheoremCBlock.Structured.wrapInc D L b) =
      ∑ te : D.CL.T L b × ChangeType, D.CL.πt L b te.1 te.2 := by
  unfold TheoremCBlock.Structured.wrapInc
  rw [mass_sum_measure, Fintype.sum_prod_type]
  refine sum_congr rfl fun t _ => ?_
  rw [sum_changeType]
  unfold mass
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have h1 := (D.CL.D_prob L b t .sym).2
  have h2 := (D.CL.D_prob L b t .skew).2
  unfold mass at h1 h2
  rw [h1, h2, mul_one, mul_one]

/-! ## The per-atom Rankin sums -/

omit [DecidableEq P] in
theorem atomPr_ge (b : BlockAtom Bk J L) :
    ∑ k, mass (D.GB.κu L b k) + mass (TheoremCBlock.Structured.wrapInc D L b) +
      ∑ i, (mass (D.FS.κ' L b i) + mass (D.FS.κ L b i)) ≤
      atomPr D L (TheoremCBlock.Structured.wrapInc D L) b := by
  unfold atomPr
  have : ∑ i, (mass (D.FS.κ' L b i) + mass (D.FS.κ L b i)) ≤
      ∑ i, (D.FS.dconst L b i * mass (D.FS.κ L b i) +
        (mass (D.FS.κ' L b i) + mass (D.FS.κ L b i))) :=
    sum_le_sum fun i _ => le_add_of_nonneg_left (mul_nonneg (D.FS.dconst_nonneg L b i)
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1))
  linarith

end Sarkozy.E1Closure
