module

public import Sarkozy.TailPrices.Records
public import Sarkozy.TailPrices.Polynomials

@[expose] public section

/-!
# The tail atom from its records (`lem:tail-prices`(i),(ii))

`paper/sections/27_tail_index.tex`, `lem:tail-prices` and its proof, with `def:upper-comparison`
and `prop:record:upper`(i) at the single prime `{p}`. The comparison law at a tail prime keeps the
accepting records of the tail law `μ_p`, replaces nonaccepting two-layer records of degree two and
three by replacing laws, deletes the others, and divides by `P_μ(r)`. This file assembles B2's
tail atom (`TailAtomData`, hence `TailAtomInputs`) from the per-record inputs of the changed records
only, on W8's record calculus (`compLaw`, `retainedCoeff`, `recordChange`,
`upper_change_normalized`) at the tail field laws:

* `TailRecordInputs p hne`: for every changed record (`upperFate ρ = changed`), the replacing law
  `new ρ` (the one-way repair of `lem:tr:repair` with the all-prime cap, `cert:tail-caps`), its
  acceptance of `𝓔₆` and square-affine invariance, and the price `π̃^ε_ρ ≥ 0` with the bracket of
  its change against `Diag_ι(m_+(Π_ρ))`. *Hypotheses* (analytic).
* **`TailRecordInputs.toData`**: the tail atom: one component
  `ν̄_p = ∑_ρ c_ρ Π'_ρ / ∑_ρ c_ρ` (`c_ρ = retainedCoeff`, `Π'_ρ = compLaw`) of mass
  `w = ∑_ρ c_ρ / P_μ(r)`; its nonroot part `ρ_p = ∑_{ρ ≠ root} c_ρ Π'_ρ` with
  `0 < h'_p ≤ h_p` (`rest_h'_pos`: the kept degree-one record `(LD, 0)` of weight `113 r`;
  `rest_h'_le`: `c_ρ ≤ c_ρ^μ`), invariant and accepting (kept records: `Records`; changed
  records: the hypotheses); the changes `P_μ⁻¹ Δ_ρ`; the envelopes `Diag_ι(m_+(Π_ρ))`; the prices
  `π̃_ρ` (changed), `c_ρ/P_μ(r)` and `0` (deleted), `0` (kept); the brackets (`bracket_all`).
* `TailRecordPrices R`: `lem:tail-prices`(ii) in per-record form: the changed prices sum to at most
  `Π^{rep}(r)` (symmetric and skew), the deleted masses `∑_{deleted} c_ρ/P_μ(r)` to at most
  `Π^{del}(r)`. *Hypotheses* (the first two analytic, `cert:tail-caps`; the third numerical).
* **`TailRecordPrices.sym_le`, `skew_le`**: the two price fields of `TailPriceInputs`.

**The fate.** The fate used is W8's `upperFate` (kept iff the record edge-accepts the six queries
`𝓔₆`, `lem:six-query-retention`), as at an upper block; the paper's tail law keeps a record iff it
accepts the twelve queries `eq:upper-twelve` and repairs 94 records. Every record that accepts the
twelve queries accepts `𝓔₆`, so the records changed or deleted here are among those the paper
changes or deletes, and (CP4) at the tail asks only `𝓔₆` (`paperQueries`); see the report.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.TailPrices

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.Mixing Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.Labellings Sarkozy.UpperComparison
open Sarkozy.ComparisonLawPaper (changePart_smul changePart_zero symPart_of_symmetric
  DeletionInputs)

variable {p : ℕ} [Fact p.Prime]

/-- The normalized change `P_μ(r)⁻¹ Δ_ρ` of the record `ρ` of the tail law. -/
noncomputable abbrev tailDelta (hne : TailNonempty p) (new : UpIdx → FiniteLaw (Slot → ZMod p))
    (ρ : UpIdx) : SlotMeasure (ZMod p) :=
  (upPoly tailWeights (tailR p))⁻¹ • recordChange (tailFieldLaws p hne) tailWeights new (tailR p) ρ

/-- The weight `c_ρ` of a record in the tail comparison law (`0` if deleted). -/
noncomputable abbrev tailC (p : ℕ) (ρ : UpIdx) : ℝ := retainedCoeff tailWeights (tailR p) ρ

/-- **The inputs of the tail atom: the changed records** (`lem:tail-prices`(i),(ii), proof):
* `new`, `new_accepts`, `new_inv`: the replacing law of every changed record (the one-way repair
  `lem:tr:repair`(a)–(c) with the all-prime cap), accepting `𝓔₆` and square-affine invariant;
* `π`, `π_nonneg`, `bracket`: its prices `π̃^ε_ρ ≥ 0` and the bracket
  `(π̃ D  ζ; ζ*  π̃ D) ⪰_ι 0` of its normalized change against `D = Diag_ι(m_+(Π_ρ))`
  (`lem:tr:repair`(f) with (F7), `cert:tail-caps`).
*Hypotheses*. -/
structure TailRecordInputs (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) where
  new : UpIdx → FiniteLaw (Slot → ZMod p)
  new_accepts : ∀ ρ, upperFate ρ = .changed → ∀ z, (new ρ).weight z ≠ 0 → ∀ j : Chamber,
    quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1
  new_inv : ∀ ρ, upperFate ρ = .changed → AffineInvariant p (new ρ).weight
  π : UpIdx → ChangeType → ℝ
  π_nonneg : ∀ ρ e, 0 ≤ π ρ e
  bracket : ∀ ρ, upperFate ρ = .changed → ∀ e,
    reservedCut.Bracket (π ρ e • tailEnv p hne ρ) (changePart e (tailDelta hne new ρ))
      (π ρ e • tailEnv p hne ρ)

omit [Fact p.Prime] in
/-- The root record has weight one. -/
theorem tailC_root : tailC p UpperComparison.rootIdx = 1 := by
  unfold tailC retainedCoeff
  rw [root_kept]
  simp [upCoeff, UpperComparison.rootIdx, PType.deg, tailWeights.w_LL]

/-- The kept degree-one record `(LD, 0)`. -/
def ldIdx : UpIdx := (true, ⟨(.L, .D), ((), (0 : Fin 3))⟩)

theorem ld_kept : upperFate ldIdx = .kept := by decide +kernel

theorem ld_ne_root : ldIdx ≠ UpperComparison.rootIdx := by decide

/-- The record `(LD, 0)` has weight `113 r > 0`. -/
theorem tailC_ld_pos : 0 < tailC p ldIdx := by
  unfold tailC retainedCoeff
  rw [ld_kept]
  have hr := tailR_pos p
  simp only [reduceCtorEq, ↓reduceIte, upCoeff, ldIdx, tailWeights, tailW, PType.deg]
  positivity

namespace TailRecordInputs

variable {hne : TailNonempty p} (R : TailRecordInputs p hne)

/-- The component `Π'_ρ` of a record (`new ρ` if changed, `Π_ρ` otherwise). -/
noncomputable abbrev comp (ρ : UpIdx) : FiniteLaw (Slot → ZMod p) :=
  compLaw (tailFieldLaws p hne) R.new ρ

theorem comp_inv (ρ : UpIdx) : AffineInvariant p (R.comp ρ).weight := by
  unfold comp compLaw
  split_ifs with h
  · exact R.new_inv ρ h
  · exact tail_component_invariant p hne ρ

theorem comp_accepts (ρ : UpIdx) (hρ : tailC p ρ ≠ 0) (z : Slot → ZMod p)
    (hz : (R.comp ρ).weight z ≠ 0) (j : Chamber) :
    quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1 := by
  unfold comp compLaw at hz
  unfold tailC retainedCoeff at hρ
  cases h : upperFate ρ
  · rw [h] at hz
    simp only [reduceCtorEq, ↓reduceIte] at hz
    exact tail_kept_accepts p hne ρ h hz j
  · rw [h] at hz
    simp only [↓reduceIte] at hz
    exact R.new_accepts ρ h z hz j
  · rw [h] at hρ
    simp at hρ

theorem comp_root : R.comp UpperComparison.rootIdx = tailRootComponent p hne := by
  unfold comp compLaw
  rw [root_kept]
  simp only [reduceCtorEq, ↓reduceIte]
  rfl

/-- The nonroot mass `h'_p = ∑_{ρ ≠ root} c_ρ`. -/
noncomputable def hRest : ℝ := ∑ ρ ∈ univ.erase UpperComparison.rootIdx, tailC p ρ

/-- The nonroot part `ρ_p = ∑_{ρ ≠ root} c_ρ Π'_ρ`. -/
noncomputable def ρRest (z : Slot → ZMod p) : ℝ :=
  ∑ ρ ∈ univ.erase UpperComparison.rootIdx, tailC p ρ * (R.comp ρ).weight z

theorem rest_h'_pos : 0 < hRest (p := p) := by
  unfold hRest
  have hmem : ldIdx ∈ univ.erase UpperComparison.rootIdx := mem_erase.mpr ⟨ld_ne_root, mem_univ _⟩
  exact lt_of_lt_of_le tailC_ld_pos
    (single_le_sum (f := tailC p) (fun ρ _ => retainedCoeff_nonneg _ (tailR_nonneg p) ρ) hmem)

omit [Fact p.Prime] in
theorem rest_h'_le : hRest (p := p) ≤ tailH p := by
  unfold hRest tailH
  have hr := tailR_nonneg p
  have h1 : ∑ ρ ∈ univ.erase UpperComparison.rootIdx, tailC p ρ ≤
      ∑ ρ ∈ univ.erase UpperComparison.rootIdx, upCoeff tailWeights (tailR p) ρ :=
    sum_le_sum fun ρ _ => retainedCoeff_le _ hr ρ
  have h2 := add_sum_erase univ (upCoeff tailWeights (tailR p)) (mem_univ UpperComparison.rootIdx)
  rw [sum_upCoeff] at h2
  have h3 : upCoeff tailWeights (tailR p) UpperComparison.rootIdx = 1 := by
    have := tailC_root (p := p)
    unfold tailC retainedCoeff at this
    rwa [root_kept] at this
  linarith

theorem decomp (z : Slot → ZMod p) :
    (tailRootComponent p hne).weight z + R.ρRest z = ∑ ρ, tailC p ρ * (R.comp ρ).weight z := by
  unfold ρRest
  rw [← add_sum_erase univ (fun ρ => tailC p ρ * (R.comp ρ).weight z)
    (mem_univ UpperComparison.rootIdx), tailC_root, one_mul, R.comp_root]

/-- **The nonroot part of the tail comparison law** as `TailRestData`. -/
noncomputable def rest : TailRestData p hne where
  h' := hRest (p := p)
  ρt := R.ρRest
  ρt_nonneg z := sum_nonneg fun ρ _ =>
    mul_nonneg (retainedCoeff_nonneg _ (tailR_nonneg p) ρ) ((R.comp ρ).nonneg z)
  ρt_mass := by
    unfold ρRest hRest
    rw [sum_comm]
    refine sum_congr rfl fun ρ _ => ?_
    rw [← mul_sum, (R.comp ρ).total, mul_one]
  h'_pos := rest_h'_pos
  h'_le := rest_h'_le
  ρt_inv α β hα z := by
    unfold ρRest
    exact sum_congr rfl fun ρ _ => by rw [R.comp_inv ρ α β hα z]
  ρt_acc z hz j := by
    obtain ⟨ρ, _, hρ⟩ := exists_ne_zero_of_sum_ne_zero hz
    exact R.comp_accepts ρ (left_ne_zero_of_mul hρ) z (right_ne_zero_of_mul hρ) j

/-- `w ν̄_p = ∑_ρ (c_ρ/P_μ(r)) Π'_ρ`. -/
theorem smul_law :
    ((1 + hRest (p := p)) / upPoly tailWeights (tailR p)) • signedIntegral R.rest.law.weight =
      ∑ ρ, (tailC p ρ / upPoly tailWeights (tailR p)) • signedIntegral (R.comp ρ).weight := by
  have h1 : (1 + hRest (p := p)) ≠ 0 := by linarith [rest_h'_pos (p := p)]
  have hP : upPoly tailWeights (tailR p) ≠ 0 :=
    (lt_of_lt_of_le one_pos (one_le_upPoly tailWeights (tailR_nonneg p))).ne'
  have hsi : ∀ (w : (Slot → ZMod p) → ℝ) (f : (Slot → ZMod p) → ℝ),
      signedIntegral w f = ∑ z, w z * f z := fun _ _ => rfl
  have hw : ∀ z, R.rest.law.weight z =
      (∑ ρ, tailC p ρ * (R.comp ρ).weight z) / (1 + hRest (p := p)) := fun z => by
    rw [← R.decomp]
    rfl
  apply LinearMap.ext
  intro f
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul, hsi, hw]
  rw [mul_sum]
  have e1 : ∀ z, (1 + hRest (p := p)) / upPoly tailWeights (tailR p) *
      ((∑ ρ, tailC p ρ * (R.comp ρ).weight z) / (1 + hRest (p := p)) * f z) =
        ∑ ρ, tailC p ρ / upPoly tailWeights (tailR p) * ((R.comp ρ).weight z * f z) := by
    intro z
    rw [sum_div, sum_mul, mul_sum]
    refine sum_congr rfl fun ρ _ => ?_
    field_simp
  simp only [e1]
  rw [sum_comm]
  refine sum_congr rfl fun ρ _ => ?_
  rw [mul_sum]

/-- **`ν_p - μ_p = ∑_ρ P_μ(r)⁻¹ Δ_ρ`** (the field `change` of (CP4)(b) at the tail). -/
theorem change_eq :
    ((1 + hRest (p := p)) / upPoly tailWeights (tailR p)) • signedIntegral R.rest.law.weight -
        signedIntegral (tailLaw p hne).weight = ∑ ρ, tailDelta hne R.new ρ := by
  rw [R.smul_law]
  have h := upper_change_normalized (tailFieldLaws p hne) tailWeights R.new (tailR_nonneg p)
  have e1 : signedIntegral (tailLaw p hne).weight =
      signedIntegral (upperReference (tailFieldLaws p hne) tailWeights (tailR_nonneg p)).weight :=
    rfl
  rw [e1]
  convert h using 2

/-- The unpriced prices of the records: `π̃_ρ` (changed), `c_ρ/P_μ(r)` and `0` (deleted,
symmetric and skew), `0` (kept). -/
noncomputable def piT (ρ : UpIdx) (e : ChangeType) : ℝ :=
  if upperFate ρ = .changed then R.π ρ e
  else if upperFate ρ = .deleted then
    (if e = .sym then upCoeff tailWeights (tailR p) ρ / upPoly tailWeights (tailR p) else 0)
  else 0

theorem piT_nonneg (ρ : UpIdx) (e : ChangeType) : 0 ≤ R.piT ρ e := by
  have hr := tailR_nonneg p
  unfold piT
  split_ifs
  · exact R.π_nonneg ρ e
  · exact div_nonneg (upCoeff_nonneg _ hr ρ) (lt_of_lt_of_le one_pos (one_le_upPoly _ hr)).le
  · exact le_rfl
  · exact le_rfl

/-- **The brackets of all records** (`prop:record:upper`(i) at the tail): changed records by
hypothesis, deleted records charged their mass in the symmetric total, kept records nothing. -/
theorem bracket_all (ρ : UpIdx) (e : ChangeType) :
    reservedCut.Bracket (R.piT ρ e • tailEnv p hne ρ) (changePart e (tailDelta hne R.new ρ))
      (R.piT ρ e • tailEnv p hne ρ) := by
  have hr := tailR_nonneg p
  have hP := lt_of_lt_of_le one_pos (one_le_upPoly tailWeights hr)
  by_cases hc : upperFate ρ = .changed
  · have h := R.bracket ρ hc e
    unfold piT
    simp only [hc, ↓reduceIte]
    exact h
  by_cases hd : upperFate ρ = .deleted
  · have hsym := tail_upComponent_symmetric p hne ρ
    have hdel : recordChange (tailFieldLaws p hne) tailWeights R.new (tailR p) ρ =
        -(upCoeff tailWeights (tailR p) ρ •
          signedIntegral (upComponent (tailFieldLaws p hne) ρ).weight) := by
      unfold recordChange
      rw [hd]
    cases e
    · unfold piT
      simp only [hd, ↓reduceIte]
      have hω : 0 ≤ upCoeff tailWeights (tailR p) ρ / upPoly tailWeights (tailR p) :=
        div_nonneg (upCoeff_nonneg _ hr ρ) hP.le
      have heq : changePart .sym (tailDelta hne R.new ρ) =
          -((upCoeff tailWeights (tailR p) ρ / upPoly tailWeights (tailR p)) •
            signedIntegral (upComponent (tailFieldLaws p hne) ρ).weight) := by
        unfold tailDelta
        rw [changePart_smul, hdel]
        change (upPoly tailWeights (tailR p))⁻¹ • symPart reservedCut _ = _
        rw [symPart_of_symmetric]
        · rw [smul_neg, smul_smul, inv_mul_eq_div]
        · have := hsym.smul (upCoeff tailWeights (tailR p) ρ)
          unfold IsSymmetricAt at this ⊢
          rw [reflect_neg, this]
      rw [heq]
      exact tail_deleted_bracket p hne ρ hω
    · unfold piT
      simp only [hd, ↓reduceIte, reduceCtorEq]
      unfold tailDelta
      rw [changePart_smul]
      change reservedCut.Bracket _ ((upPoly tailWeights (tailR p))⁻¹ • skewPart reservedCut _) _
      rw [tail_skew_recordChange_deleted p hne tailWeights R.new (tailR p) hd, smul_zero,
        zero_smul]
      exact DeletionInputs.zero_positive.bracket_self
  · have hk : upperFate ρ = .kept := by
      cases h : upperFate ρ
      · rfl
      · exact absurd h hc
      · exact absurd h hd
    unfold piT
    simp only [hc, hd, ↓reduceIte]
    unfold tailDelta recordChange
    rw [hk, smul_zero, changePart_zero, zero_smul]
    exact DeletionInputs.zero_positive.bracket_self

/-- **The tail atom from its records** (`lem:tail-prices`(i),(ii)), relative to the tail law
`μ_p` (`def:tail-law`). -/
noncomputable def toData : TailAtomData p hne (signedIntegral (tailLaw p hne).weight) where
  rest := R.rest
  w := (1 + hRest (p := p)) / upPoly tailWeights (tailR p)
  w_pos := div_pos (by linarith [rest_h'_pos (p := p)])
    (lt_of_lt_of_le one_pos (one_le_upPoly tailWeights (tailR_nonneg p)))
  T := UpIdx
  Δ := tailDelta hne R.new
  change := R.change_eq
  D ρ _ := tailEnv p hne ρ
  D_prob ρ _ := (tail_envelope p hne ρ).1
  D_diag ρ _ := (tail_envelope p hne ρ).2.1
  D_unif ρ _ := (tail_envelope p hne ρ).2.2
  πt := R.piT
  πt_nonneg := R.piT_nonneg
  bracket := R.bracket_all

theorem toData_πt : R.toData.πt = R.piT := rfl

/-- The symmetric total splits into the changed prices and the deleted masses. -/
theorem sum_piT_sym : ∑ ρ, R.piT ρ .sym =
    ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed), R.π ρ .sym +
      ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .deleted),
        upCoeff tailWeights (tailR p) ρ / upPoly tailWeights (tailR p) := by
  rw [sum_filter, sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun ρ _ => ?_
  unfold piT
  cases upperFate ρ <;> simp

/-- The skew total is the sum of the changed skew prices. -/
theorem sum_piT_skew : ∑ ρ, R.piT ρ .skew =
    ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed), R.π ρ .skew := by
  rw [sum_filter]
  refine sum_congr rfl fun ρ _ => ?_
  unfold piT
  cases upperFate ρ <;> simp

end TailRecordInputs

/-- **`lem:tail-prices`(ii) in per-record form** at `r = p^{-1/2}`:
* `rep_sym`, `rep_skew`: the changed (repaired) records cost at most `Π^{rep}(r)` in each part
  (each repair bound included in full in both totals; `cert:tail-caps`, `eq:tail-polynomials`);
* `del`: the deleted records cost at most `Π^{del}(r)` (numerical: `c^{del}_d` of
  `eq:tail-polynomials` bounds the weight of the deleted records of each overall degree).
*Hypotheses*. -/
structure TailRecordPrices {hne : TailNonempty p} (R : TailRecordInputs p hne) : Prop where
  rep_sym : ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed), R.π ρ .sym ≤ piRep (tailR p)
  rep_skew : ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed), R.π ρ .skew ≤ piRep (tailR p)
  del : ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .deleted),
    upCoeff tailWeights (tailR p) ρ / upPoly tailWeights (tailR p) ≤ piDel (tailR p)

namespace TailRecordPrices

variable {hne : TailNonempty p} {R : TailRecordInputs p hne} (H : TailRecordPrices R)
include H

theorem sym_le : ∑ ρ, R.toData.πt ρ .sym ≤ piRep (tailR p) + piDel (tailR p) := by
  change ∑ ρ : UpIdx, R.piT ρ .sym ≤ _
  rw [R.sum_piT_sym]
  exact add_le_add H.rep_sym H.del

theorem skew_le : ∑ ρ, R.toData.πt ρ .skew ≤ piRep (tailR p) := by
  change ∑ ρ : UpIdx, R.piT ρ .skew ≤ _
  rw [R.sum_piT_skew]
  exact H.rep_skew

end TailRecordPrices

end Sarkozy.TailPrices
