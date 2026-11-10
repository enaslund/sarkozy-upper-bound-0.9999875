module

public import Sarkozy.E1Closure.Atoms

@[expose] public section

/-!
# The per-atom Rankin sums of the (E1) terms (EC)

EC, 8 November 2026. With `q = q_𝔟^{1/4}` and LP's `Pr_𝔟 = atomPr` at the wrapping increment:

* **`subAtom_le`**: `∑_{o, y} π̃(o) ‖subLaw(o, y)‖ q(o, y)^{1/4} ≤ 1 + 2 q_𝔟^{1/4} Pr_𝔟`
  (the subset terms; exactly `1 + q_𝔟^{1/4}(∑_k ‖κu_k‖ + ∑_{t,ε} π̃^ε_t)`);
* **`coupAtom_le`**: `∑_{o, x} π̃(o) compat(o, x) ‖cDom(o, x)‖ q(o, x)^{1/4} ≤ 1 + 2 q_𝔟^{1/4} Pr_𝔟`
  (the coupled pieces; exactly `1 + q_𝔟^{1/4}(∑_k ‖κu_k‖ + 2 ∑_i (‖κ'_i‖ + ‖κ_i‖) + ∑ π̃)`).
-/

namespace Sarkozy.E1Closure

open Finset Function
open scoped BigOperators
open Sarkozy.EnvelopeInputsBlock Sarkozy.EnvelopeInputs
open Sarkozy.BlockFrame
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.Structured ReflectionCut
open Sarkozy.LargeSums (atomQR atomQR_nonneg atomPr)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)

omit [DecidableEq P] in
theorem mass_zero_measure {X : Type} [Fintype X] : mass (0 : SlotMeasure X) = 0 := rfl

omit [DecidableEq P] in
theorem mass_add_measure {X : Type} [Fintype X] (κ₁ κ₂ : SlotMeasure X) :
    mass (κ₁ + κ₂) = mass κ₁ + mass κ₂ := rfl

omit [DecidableEq P] in
theorem atomPr_nonneg (b : BlockAtom Bk J L) :
    0 ≤ atomPr D L (TheoremCBlock.Structured.wrapInc D L) b := by
  refine le_trans ?_ (atomPr_ge D L b)
  have h1 : 0 ≤ ∑ k, mass (D.GB.κu L b k) := sum_nonneg fun k _ =>
    TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b k).1
  have h2 : 0 ≤ mass (TheoremCBlock.Structured.wrapInc D L b) :=
    TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg
      (Sarkozy.DensityChain.isPositiveRecord_wrapInc D L b).1
  have h3 : 0 ≤ ∑ i, (mass (D.FS.κ' L b i) + mass (D.FS.κ L b i)) := sum_nonneg fun i _ =>
    add_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1)
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
  linarith

omit [DecidableEq P] in
/-- **The per-atom Rankin sum of the subset terms.** -/
theorem subAtom_le (b : BlockAtom Bk J L) :
    ∑ o, ∑ y : Bool, entryPrice (D.CL.πt L b) o * mass (subLaw D L b o y) *
        subQ D L b o y ^ ((1 : ℝ) / 4) ≤
      1 + 2 * (atomQR D L b ^ ((1 : ℝ) / 4) *
        atomPr D L (TheoremCBlock.Structured.wrapInc D L) b) := by
  set q4 := atomQR D L b ^ ((1 : ℝ) / 4) with hq4
  have hq0 : 0 ≤ q4 := Real.rpow_nonneg (atomQR_nonneg D L b) _
  have hnone : ∑ y : Bool, entryPrice (D.CL.πt L b) none * mass (subLaw D L b none y) *
      subQ D L b none y ^ ((1 : ℝ) / 4) = 1 + q4 * ∑ k, mass (D.GB.κu L b k) := by
    rw [Fintype.sum_bool]
    simp only [entryPrice, subLaw, subQ, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      or_false, or_self, Real.one_rpow, one_mul, mul_one, mass_sum_measure]
    rw [mass_entryFactor]
    ring
  have hsome : ∀ te : D.CL.T L b × ChangeType, ∑ y : Bool, entryPrice (D.CL.πt L b) (some te) *
      mass (subLaw D L b (some te) y) * subQ D L b (some te) y ^ ((1 : ℝ) / 4) =
      q4 * D.CL.πt L b te.1 te.2 := by
    intro te
    rw [Fintype.sum_bool]
    simp only [entryPrice, subLaw, subQ, Option.isSome_some, ↓reduceIte, or_true,
      mass_zero_measure, mul_zero, zero_mul, zero_add, Bool.false_eq_true]
    rw [mass_entryFactor]
    ring
  rw [Fintype.sum_option, hnone, sum_congr rfl fun te _ => hsome te, ← mul_sum,
    ← mass_wrapInc]
  have := atomPr_ge D L b
  have h3 : 0 ≤ ∑ i, (mass (D.FS.κ' L b i) + mass (D.FS.κ L b i)) := sum_nonneg fun i _ =>
    add_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1)
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
  have hPr := atomPr_nonneg D L b
  nlinarith [mul_le_mul_of_nonneg_left this hq0, mul_nonneg hq0 hPr]

omit [DecidableEq P] in
/-- **The per-atom Rankin sum of the coupled pieces.** -/
theorem coupAtom_le (b : BlockAtom Bk J L) :
    ∑ o, ∑ x : CEPiece D L b, entryPrice (D.CL.πt L b) o * compat D L b o x *
        mass (cDom D L b o x) * coupQ D L b o x ^ ((1 : ℝ) / 4) ≤
      1 + 2 * (atomQR D L b ^ ((1 : ℝ) / 4) *
        atomPr D L (TheoremCBlock.Structured.wrapInc D L) b) := by
  set q4 := atomQR D L b ^ ((1 : ℝ) / 4) with hq4
  have hq0 : 0 ≤ q4 := Real.rpow_nonneg (atomQR_nonneg D L b) _
  have hnone : ∑ x : CEPiece D L b, entryPrice (D.CL.πt L b) none * compat D L b none x *
      mass (cDom D L b none x) * coupQ D L b none x ^ ((1 : ℝ) / 4) =
      1 + q4 * (∑ k, mass (D.GB.κu L b k) +
        2 * ∑ i, (mass (D.FS.κ' L b i) + mass (D.FS.κ L b i))) := by
    rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type]
    simp only [Fintype.sum_option, Fintype.sum_bool]
    simp only [entryPrice, compat, cDom, coupQ, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, Real.one_rpow, one_mul, mul_one, mass_add_measure]
    rw [mass_entryFactor, ← hq4, ← sum_mul]
    have e2 : ∑ i, ((mass (D.FS.κ' L b i) + mass (D.FS.κ L b i)) * q4 +
        (mass (D.FS.κ' L b i) * q4 + mass (D.FS.κ L b i) * q4)) =
        (2 * ∑ i, (mass (D.FS.κ' L b i) + mass (D.FS.κ L b i))) * q4 := by
      rw [mul_sum, sum_mul]
      exact sum_congr rfl fun _ _ => by ring
    rw [e2]
    ring
  have hsome : ∀ te : D.CL.T L b × ChangeType, ∑ x : CEPiece D L b,
      entryPrice (D.CL.πt L b) (some te) * compat D L b (some te) x *
        mass (cDom D L b (some te) x) * coupQ D L b (some te) x ^ ((1 : ℝ) / 4) =
      q4 * D.CL.πt L b te.1 te.2 := by
    intro te
    rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type]
    simp only [Fintype.sum_option, Fintype.sum_bool]
    simp only [entryPrice, compat, cDom, coupQ, Option.isSome_some, reduceCtorEq,
      ↓reduceIte, mul_zero, zero_mul, sum_const_zero, add_zero]
    rw [mass_entryFactor]
    ring
  rw [Fintype.sum_option, hnone, sum_congr rfl fun te _ => hsome te, ← mul_sum,
    ← mass_wrapInc]
  have := atomPr_ge D L b
  have hPr := atomPr_nonneg D L b
  have h1 : 0 ≤ ∑ k, mass (D.GB.κu L b k) := sum_nonneg fun k _ =>
    TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b k).1
  have h2 : 0 ≤ mass (TheoremCBlock.Structured.wrapInc D L b) :=
    TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg
      (Sarkozy.DensityChain.isPositiveRecord_wrapInc D L b).1
  nlinarith [mul_le_mul_of_nonneg_left this hq0, mul_nonneg hq0 hPr, mul_nonneg hq0 h1,
    mul_nonneg hq0 h2]

end Sarkozy.E1Closure
