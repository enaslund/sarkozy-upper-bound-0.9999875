module

public import Sarkozy.ComparisonLawPaper.Deletion
public import Sarkozy.ComparisonLawPaper.Tail
public import Sarkozy.UpperComparison.UpperLaw
public import Sarkozy.UpperComparison.Symmetry
public import Sarkozy.UpperComparison.Sanity
public import Sarkozy.UpperComparison.PaperPrices

@[expose] public section

/-!
# (CP4) at an upper block from W8's `prop:record:upper`(i)

`paper/sections/26_upper_comparison.tex`, `def:upper-comparison`, `prop:record:upper`(i). On an
upper block with primes `pr`, the comparison law keeps the records of V1's upper reference that
accept the six queries, replaces the nonaccepting two-layer records of degree two and three by the
replacing laws `new ρ`, deletes the others, and divides by `P_μ(r)`. W8 (`Sarkozy.UpperComparison`)
proves on V1's records: the components and weights (`compLaw`, `retainedCoeff`), the exact
decomposition `ν_𝔅 - μ_𝔅 = ∑_ρ P_μ⁻¹ Δ_ρ` (`upper_change_normalized`), acceptance and uniform
marginals of the components (`upperNu_component_accepts`, `_uniform`, from those of the replacing
laws), the envelopes `Diag_ι(m_+)` of the old records (`upper_envelope`), the brackets of the
deleted records (`deleted_record_bracket_paper`) and the vanishing skew part of their change
(`skew_recordChange_deleted`).

* `UpperAtomInputs pr hne W r`: what is left: the replacing laws `new ρ` (one-way repairs (F7),
  `prop:dense-comparison`, `prop:le-mixture`), their acceptance and uniform marginals, and for every
  changed record the prices `π̃^ε_ρ ≥ 0` with the brackets of its change against the envelope of the
  old record (`prop:forest-records`, `prop:dense-comparison`(b), `prop:le-mixture`; W8's
  `oldRecord_sym_bracket`, `_skew_bracket` reduce these to analytic bounds).
* **`UpperAtomInputs.toAtom`**: the `AtomComparison` of the block, relative to `λ_𝔅 = μ_𝔅`: the
  components are the retained records (`retainedCoeff ≠ 0`) with coefficient one and mass
  `c_ρ/P_μ(r)`; the changes are `P_μ⁻¹ Δ_ρ` for every record; the prices are `0` (kept),
  `c_ρ/P_μ(r)` and `0` (deleted, symmetric and skew), `π̃_ρ` (changed). The acceptance relation is
  "`y_p - x_p` is a nonzero square at every prime of the block" (`blockSquareAccepted`).
* `UpperAtomInputs.toAtom_sprice`, `toAtom_aprice`: the prices; `toAtom_coeff_nonneg`: the law is a
  nonnegative combination (coefficients one).
* **`UpperAtomInputs.prices_le_poly`** (`prop:record:upper`(i), W8's `paper_block_poly`): if the
  prices of the changed records are at most the ledger coefficients over `P_μ(r)`
  (`π̃^s_ρ ≤ w_ρ C^s_ρ r^{deg+1}/P_μ`, `π̃^a_ρ ≤ w_ρ C^a_ρ r^{deg+1}/P_μ`), then
  `s_𝔅 ≤ (∑_d c^s_d r^d) q^{2a}` and `a_𝔅 ≤ (∑_d c^a_d r^d) q^{2a}` with the ledger polynomials; the
  deleted records are charged exactly their ledger coefficients (W8's `deleted_coef_eq`). This is
  the per-block hypothesis `hs`, `ha` of `SAExplicit_of_bands`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.ComparisonLawPaper

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.UpperComparison

/-! ## Changes and their parts -/

section Parts

variable {X : Type} [Fintype X]

theorem changePart_smul (e : ChangeType) (a : ℝ) (L : SlotMeasure X) :
    changePart e (a • L) = a • changePart e L := by
  cases e <;>
  · simp only [changePart, symPart, skewPart, reflect_smul]
    apply LinearMap.ext
    intro f
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, smul_eq_mul]
    ring

theorem changePart_zero (e : ChangeType) : changePart e (0 : SlotMeasure X) = 0 := by
  have h := changePart_smul e 0 (0 : SlotMeasure X)
  rwa [zero_smul, zero_smul] at h

theorem symPart_of_symmetric {L : SlotMeasure X} (h : IsSymmetricAt reservedCut L) :
    symPart reservedCut L = L := by
  unfold symPart
  rw [h]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
  ring

end Parts

/-! ## The acceptance relation of a block of primes -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- Acceptance at a block of primes `pr` with `e_p = 1` (`def:cp4`(a)): `y_p - x_p` is a nonzero
square at every prime. -/
def blockSquareAccepted (x y : BlockLabel pr) : Prop := ∀ i, y i - x i ≠ 0 ∧ IsSquare (y i - x i)

/-! ## The inputs and the atom -/

/-- The envelope `Diag_ι(m_+(Π_ρ))` of the record `ρ` of an upper block (W8's `upper_envelope`). -/
noncomputable abbrev upperEnv (hne : UpperNonempty pr) (ρ : UpIdx) : SlotMeasure (BlockLabel pr) :=
  reservedCut.diagonalLaw
    (plusMarginal reservedCut (upComponent (upperBlockFieldLaws pr hne) ρ).weight)

/-- The normalized change `P_μ(r)⁻¹ Δ_ρ` of the record `ρ`. -/
noncomputable abbrev upperDelta (hne : UpperNonempty pr) (W : UpperWeights)
    (new : UpIdx → FiniteLaw (Slot → BlockLabel pr)) (r : ℝ) (ρ : UpIdx) :
    SlotMeasure (BlockLabel pr) :=
  (upPoly W r)⁻¹ • recordChange (upperBlockFieldLaws pr hne) W new r ρ

/-- **The inputs of (CP4) at an upper block** (`prop:record:upper`(i)), beyond what W8 proves:
* `new`, `new_accepts`, `new_uniform`: the replacing laws of the changed records with acceptance of
  the six queries at every prime of the block and uniform one-slot marginals (one-way repairs (F7),
  `prop:dense-comparison`(a), `prop:le-mixture`);
* `π`, `π_nonneg`, `bracket`: for every changed record and type, the price `π̃^ε_ρ ≥ 0` and the
  bracket `(π̃ D  ζ; ζ*  π̃ D) ⪰_ι 0` of its normalized change against the envelope
  `D = Diag_ι(m_+(Π_ρ))` of the old record (`prop:forest-records`(a),(b),
  `prop:dense-comparison`(b), `prop:le-mixture`, through W8's `upRecord_sym_bracket`). -/
structure UpperAtomInputs (hne : UpperNonempty pr) (W : UpperWeights) (r : ℝ) where
  new : UpIdx → FiniteLaw (Slot → BlockLabel pr)
  new_accepts : ∀ ρ, upperFate ρ = .changed → ∀ z, (new ρ).weight z ≠ 0 → ∀ (j : Chamber) (i : ι),
    quadraticChar (ZMod (pr i)) (z (queryTarget j) i - z (querySource j) i) = 1
  new_uniform : ∀ ρ, upperFate ρ = .changed → HasUniformMarginals (new ρ)
  π : UpIdx → ChangeType → ℝ
  π_nonneg : ∀ ρ e, 0 ≤ π ρ e
  bracket : ∀ ρ, upperFate ρ = .changed → ∀ e,
    reservedCut.Bracket (π ρ e • upperEnv pr hne ρ) (changePart e (upperDelta pr hne W new r ρ))
      (π ρ e • upperEnv pr hne ρ)

namespace UpperAtomInputs

variable {pr} {hne : UpperNonempty pr} {W : UpperWeights} {r : ℝ} (D : UpperAtomInputs pr hne W r)

/-- The unpriced prices of the records: `0` (kept), `c_ρ/P_μ(r)` and `0` (deleted), `π̃_ρ`
(changed). -/
noncomputable def piT (ρ : UpIdx) (e : ChangeType) : ℝ :=
  if upperFate ρ = .changed then D.π ρ e
  else if upperFate ρ = .deleted then (if e = .sym then upCoeff W r ρ / upPoly W r else 0)
  else 0

theorem piT_nonneg (hr : 0 ≤ r) (ρ : UpIdx) (e : ChangeType) : 0 ≤ D.piT ρ e := by
  unfold piT
  split_ifs
  · exact D.π_nonneg ρ e
  · exact div_nonneg (upCoeff_nonneg W hr ρ) (lt_of_lt_of_le one_pos (one_le_upPoly W hr)).le
  · exact le_rfl
  · exact le_rfl

theorem bracket_all (hr : 0 ≤ r) (ρ : UpIdx) (e : ChangeType) :
    reservedCut.Bracket (D.piT ρ e • upperEnv pr hne ρ)
      (changePart e (upperDelta pr hne W D.new r ρ)) (D.piT ρ e • upperEnv pr hne ρ) := by
  have hP := lt_of_lt_of_le one_pos (one_le_upPoly W hr)
  by_cases hc : upperFate ρ = .changed
  · have h := D.bracket ρ hc e
    unfold piT
    simp only [hc, ↓reduceIte]
    exact h
  by_cases hd : upperFate ρ = .deleted
  · have hsym := upComponent_symmetric pr hne ρ
    have hdel : recordChange (upperBlockFieldLaws pr hne) W D.new r ρ =
        -(upCoeff W r ρ • signedIntegral (upComponent (upperBlockFieldLaws pr hne) ρ).weight) := by
      unfold recordChange
      rw [hd]
    cases e
    · unfold piT
      simp only [hd, ↓reduceIte]
      have hω : 0 ≤ upCoeff W r ρ / upPoly W r := div_nonneg (upCoeff_nonneg W hr ρ) hP.le
      have heq : changePart .sym (upperDelta pr hne W D.new r ρ) =
          -((upCoeff W r ρ / upPoly W r) •
            signedIntegral (upComponent (upperBlockFieldLaws pr hne) ρ).weight) := by
        unfold upperDelta
        rw [changePart_smul, hdel]
        change (upPoly W r)⁻¹ • symPart reservedCut _ = _
        rw [symPart_of_symmetric]
        · rw [smul_neg, smul_smul, inv_mul_eq_div]
        · have := hsym.smul (upCoeff W r ρ)
          unfold IsSymmetricAt at this ⊢
          rw [reflect_neg, this]
      rw [heq]
      exact deleted_record_bracket_paper pr hne ρ hω
    · unfold piT
      simp only [hd, ↓reduceIte, reduceCtorEq]
      unfold upperDelta
      rw [changePart_smul]
      change reservedCut.Bracket _ ((upPoly W r)⁻¹ • skewPart reservedCut _) _
      rw [skew_recordChange_deleted pr hne W D.new r hd, smul_zero, zero_smul]
      exact DeletionInputs.zero_positive.bracket_self
  · have hk : upperFate ρ = .kept := by
      cases h : upperFate ρ
      · rfl
      · exact absurd h hc
      · exact absurd h hd
    unfold piT
    simp only [hc, hd, ↓reduceIte]
    unfold upperDelta recordChange
    rw [hk, smul_zero, changePart_zero, zero_smul]
    exact DeletionInputs.zero_positive.bracket_self

theorem retained_pos (hr : 0 ≤ r) (ρ : {ρ : UpIdx // retainedCoeff W r ρ ≠ 0}) :
    0 < retainedCoeff W r ρ.1 / upPoly W r :=
  div_pos (lt_of_le_of_ne (retainedCoeff_nonneg W hr ρ.1) (Ne.symm ρ.2))
    (lt_of_lt_of_le one_pos (one_le_upPoly W hr))

/-- The root record is retained with coefficient one. -/
theorem retainedCoeff_root : retainedCoeff W r UpperComparison.rootIdx = 1 := by
  unfold retainedCoeff
  rw [root_kept]
  simp [upCoeff, UpperComparison.rootIdx, PType.deg, W.w_LL]

/-- The sum over the retained records is the sum over all records. -/
theorem sum_retained {M : Type} [AddCommMonoid M] (f : UpIdx → M)
    (hf : ∀ ρ, retainedCoeff W r ρ = 0 → f ρ = 0) :
    ∑ ρ : {ρ : UpIdx // retainedCoeff W r ρ ≠ 0}, f ρ.1 = ∑ ρ, f ρ := by
  rw [← Finset.sum_subtype (univ.filter fun ρ => retainedCoeff W r ρ ≠ 0) (by simp) f]
  exact Finset.sum_filter_of_ne fun ρ _ h => fun h0 => h (hf ρ h0)

/-- **The `AtomComparison` of an upper block** (`def:upper-comparison`, `prop:record:upper`(i)),
relative to `λ_𝔅 = μ_𝔅` (an upper block is not a first-stage atom). -/
noncomputable def toAtom (hr : 0 < r) :
    AtomComparison (signedIntegral (upperBlockReference pr hne W hr.le).weight)
      (blockSquareAccepted pr) MainAnchor.paperQueries where
  I := {ρ : UpIdx // retainedCoeff W r ρ ≠ 0}
  c _ := 1
  w ρ := retainedCoeff W r ρ.1 / upPoly W r
  law ρ := compLaw (upperBlockFieldLaws pr hne) D.new ρ.1
  w_pos ρ := retained_pos hr.le ρ
  mass_pos := by
    have hroot : retainedCoeff W r UpperComparison.rootIdx ≠ 0 := by
      rw [retainedCoeff_root]; exact one_ne_zero
    refine lt_of_lt_of_le (by simpa using retained_pos hr.le ⟨UpperComparison.rootIdx, hroot⟩)
      (single_le_sum (f := fun ρ : {ρ : UpIdx // retainedCoeff W r ρ ≠ 0} =>
        1 * (retainedCoeff W r ρ.1 / upPoly W r))
        (fun ρ _ => mul_nonneg zero_le_one (retained_pos hr.le ρ).le)
        (mem_univ ⟨UpperComparison.rootIdx, hroot⟩))
  accept ρ z hz e i := by
    rw [paperQueries_source_eq, paperQueries_target_eq]
    exact (quadraticChar_eq_one_iff _).mp
      (upperNu_component_accepts pr hne W D.new r D.new_accepts ρ.1 ρ.2 hz e i)
  unif ρ := upperNu_component_uniform pr hne D.new D.new_uniform ρ.1
  T := UpIdx
  Δ ρ := upperDelta pr hne W D.new r ρ
  change := by
    have h := upper_change_normalized (upperBlockFieldLaws pr hne) W D.new hr.le
    have hs := sum_retained (W := W) (r := r) (M := SlotMeasure (BlockLabel pr))
      (fun ρ => (retainedCoeff W r ρ / upPoly W r) •
        signedIntegral (compLaw (upperBlockFieldLaws pr hne) D.new ρ).weight)
      (fun ρ h0 => by rw [h0, zero_div, zero_smul])
    simp only [one_mul]
    rw [hs]
    have e1 : signedIntegral (upperBlockReference pr hne W hr.le).weight =
      signedIntegral (upperReference (upperBlockFieldLaws pr hne) W hr.le).weight := rfl
    rw [e1]
    convert h using 2
  D ρ _ := upperEnv pr hne ρ
  D_prob ρ _ := (upper_envelope pr hne ρ).1
  D_diag ρ _ := (upper_envelope pr hne ρ).2.1
  D_unif ρ _ := (upper_envelope pr hne ρ).2.2
  πt := D.piT
  πt_nonneg := D.piT_nonneg hr.le
  bracket := D.bracket_all hr.le

/-- The upper block law is a nonnegative combination: all coefficients are one. -/
theorem toAtom_coeff_nonneg (hr : 0 < r) (i : (D.toAtom hr).I) : 0 ≤ (D.toAtom hr).c i :=
  zero_le_one

/-- The symmetric price of an upper block: `s_𝔅 = ∑_ρ π̃^s_ρ q^{2a}`, with `π̃^s_ρ = c_ρ/P_μ(r)` for
a deleted record and `0` for a kept one. -/
theorem toAtom_sprice (hr : 0 < r) (sel : ℝ) :
    (D.toAtom hr).sprice sel = ∑ ρ, D.piT ρ .sym * sel := rfl

/-- The skew price of an upper block: `a_𝔅 = ∑_ρ π̃^a_ρ q^{2a}` (only changed records
contribute). -/
theorem toAtom_aprice (hr : 0 < r) (sel : ℝ) :
    (D.toAtom hr).aprice sel = ∑ ρ, D.piT ρ .skew * sel := rfl

/-- **`prop:record:upper`(i) for the assembled upper block**: per-record bounds on the prices of the
changed records by the ledger coefficients give the ledger polynomials (W8's `paper_block_poly`). -/
theorem prices_le_poly (hr : 0 < r) (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i)
    (hCa : ∀ i, 0 ≤ Ca i)
    (hπs : ∀ ρ, upperFate ρ = .changed →
      D.π ρ .sym ≤ (upperLedger W Cs Ca hCs hCa).symCoef r ρ / upPoly W r)
    (hπa : ∀ ρ, upperFate ρ = .changed →
      D.π ρ .skew ≤ (upperLedger W Cs Ca hCs hCa).skewCoef r ρ / upPoly W r)
    {sel : ℝ} (hsel : 0 ≤ sel) :
    (D.toAtom hr).sprice sel ≤ polyEval (upperLedger W Cs Ca hCs hCa).coefS r * sel ∧
      (D.toAtom hr).aprice sel ≤ polyEval (upperLedger W Cs Ca hCs hCa).coefA r * sel := by
  have hP := lt_of_lt_of_le one_pos (one_le_upPoly W hr.le)
  have hs : ∀ ρ, D.piT ρ .sym ≤ (upperLedger W Cs Ca hCs hCa).symCoef r ρ / upPoly W r := by
    intro ρ
    unfold piT
    by_cases hc : upperFate ρ = .changed
    · simp only [hc, ↓reduceIte]
      exact hπs ρ hc
    by_cases hd : upperFate ρ = .deleted
    · simp only [hd, ↓reduceIte]
      exact le_of_eq (deleted_coef_eq W Cs Ca hCs hCa r hd).1
    · simp only [hc, hd, ↓reduceIte]
      exact div_nonneg ((upperLedger W Cs Ca hCs hCa).symCoef_nonneg hr.le ρ) hP.le
  have ha : ∀ ρ, D.piT ρ .skew ≤ (upperLedger W Cs Ca hCs hCa).skewCoef r ρ / upPoly W r := by
    intro ρ
    unfold piT
    by_cases hc : upperFate ρ = .changed
    · simp only [hc, ↓reduceIte]
      exact hπa ρ hc
    by_cases hd : upperFate ρ = .deleted
    · simp only [hd, ↓reduceIte, reduceCtorEq]
      exact div_nonneg ((upperLedger W Cs Ca hCs hCa).skewCoef_nonneg hr.le ρ) hP.le
    · simp only [hc, hd, ↓reduceIte]
      exact div_nonneg ((upperLedger W Cs Ca hCs hCa).skewCoef_nonneg hr.le ρ) hP.le
  have h := paper_block_poly W Cs Ca hCs hCa hr.le hsel (fun ρ => D.piT ρ .sym)
    (fun ρ => D.piT ρ .skew) hs ha
  rw [toAtom_sprice, toAtom_aprice, ← sum_mul, ← sum_mul]
  exact h

end UpperAtomInputs

end Sarkozy.ComparisonLawPaper
