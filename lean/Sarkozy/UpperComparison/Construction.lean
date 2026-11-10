module

public import Sarkozy.UpperComparison.Ledger

@[expose] public section

/-!
# The upper comparison law as a measure (`def:upper-comparison`, `prop:record:upper`(i))

`paper/sections/26_upper_comparison.tex`, `def:upper-comparison` and the proof of
`prop:record:upper`(i) ("Records kept", "Records repaired", "Records replaced", "Records
deleted").

On V1's upper reference `μ̃_𝔅 = ∑_ρ c_ρ Π_ρ` (`PartV.upperTilde`, `c_ρ = upCoeff W r ρ`, the
components `Π_ρ = upComponent F ρ`), the comparison law is obtained record by record
(`upperNuTilde`): a kept record keeps its component, a changed record is replaced by a given
probability law `new ρ` (its one-way repair, dense law or LE mixture), and a deleted record is
dropped. The replacing laws are parameters: their construction is (F7) and
`prop:dense-comparison`, `prop:le-mixture`.

**Proved.**
* `upperNuTilde_sub`: the change is the sum of the record changes,
  `ν̃_𝔅 - μ̃_𝔅 = ∑_ρ Δ_ρ`, with `Δ_ρ = c_ρ (new ρ - Π_ρ)` for a changed record,
  `Δ_ρ = -c_ρ Π_ρ` for a deleted one and `0` for a kept one; this is the decomposition of
  `(CP4)(b)` (`TheoremCParam.ComparisonLaw.change`) for an upper block, before the division by
  `P_μ(r)`;
* `upperNuTilde_mass`, `upperNuTilde_mass_le`: `ν̃_𝔅(1)` is the total weight of the retained
  records, at most `P_μ(r)`, so `ν_𝔅 = ν̃_𝔅/P_μ(r)` has the normalizing denominator of `μ_𝔅`;
* `upperNuTilde_nonneg`: `ν̃_𝔅` is a nonnegative measure;
* `recordChange_mass`: every record change of a changed record has mass zero (both laws are
  probability laws), and a deleted record's change has mass `-c_ρ`;
* `recordChange_half_marginal`: if a replacing law has the actual half marginal of the old record
  on a test function of a half (hypothesis), the change annihilates that test function: the
  zero-marginal property of `prop:record:upper`(i).
-/

open Finset

namespace Sarkozy.UpperComparison

open Sarkozy.PartV

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The component of a record in the comparison law: the replacing law `new ρ` for a changed
record, V1's component otherwise (a deleted record has weight zero, `retainedCoeff`). -/
noncomputable def compLaw (F : UpperFieldLaws X) (new : UpIdx → FiniteLaw (Slot → X))
    (ρ : UpIdx) : FiniteLaw (Slot → X) :=
  if upperFate ρ = .changed then new ρ else upComponent F ρ

/-- The weight of a record in the comparison law: `c_ρ` for a kept or changed record, `0` for a
deleted one. -/
noncomputable def retainedCoeff (W : UpperWeights) (r : ℝ) (ρ : UpIdx) : ℝ :=
  if upperFate ρ = .deleted then 0 else upCoeff W r ρ

/-- **The unnormalized upper comparison law** `ν̃_𝔅` (`def:upper-comparison`); the comparison law
is `ν_𝔅 = ν̃_𝔅 / P_μ(r)`. -/
noncomputable def upperNuTilde (F : UpperFieldLaws X) (W : UpperWeights)
    (new : UpIdx → FiniteLaw (Slot → X)) (r : ℝ) : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ :=
  tildeMeasure (retainedCoeff W r) (compLaw F new)

/-- **The change of a record** (proof of `prop:record:upper`(i)). -/
noncomputable def recordChange (F : UpperFieldLaws X) (W : UpperWeights)
    (new : UpIdx → FiniteLaw (Slot → X)) (r : ℝ) (ρ : UpIdx) : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ :=
  match upperFate ρ with
  | .kept => 0
  | .changed => upCoeff W r ρ •
      (signedIntegral (new ρ).weight - signedIntegral (upComponent F ρ).weight)
  | .deleted => -(upCoeff W r ρ • signedIntegral (upComponent F ρ).weight)

/-- **`ν̃_𝔅 - μ̃_𝔅` is the sum of the record changes** (`prop:record:upper`(i)). -/
theorem upperNuTilde_sub (F : UpperFieldLaws X) (W : UpperWeights)
    (new : UpIdx → FiniteLaw (Slot → X)) (r : ℝ) :
    upperNuTilde F W new r - upperTilde F W r = ∑ ρ, recordChange F W new r ρ := by
  unfold upperNuTilde upperTilde tildeMeasure
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  unfold recordChange retainedCoeff compLaw
  cases h : upperFate ρ
  · simp
  · simp [smul_sub]
  · simp

theorem retainedCoeff_nonneg (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) (ρ : UpIdx) :
    0 ≤ retainedCoeff W r ρ := by
  unfold retainedCoeff
  split_ifs
  · exact le_rfl
  · exact upCoeff_nonneg W hr ρ

theorem retainedCoeff_le (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) (ρ : UpIdx) :
    retainedCoeff W r ρ ≤ upCoeff W r ρ := by
  unfold retainedCoeff
  split_ifs
  · exact upCoeff_nonneg W hr ρ
  · exact le_rfl

/-- `ν̃_𝔅(1)` is the total weight of the retained records. -/
theorem upperNuTilde_mass (F : UpperFieldLaws X) (W : UpperWeights)
    (new : UpIdx → FiniteLaw (Slot → X)) (r : ℝ) :
    upperNuTilde F W new r (fun _ => 1) = ∑ ρ, retainedCoeff W r ρ :=
  tildeMeasure_mass _ _

/-- **The normalizer**: `ν̃_𝔅(1) ≤ P_μ(r)`, so `ν_𝔅 = ν̃_𝔅/P_μ(r)` is a nonnegative measure of mass
at most one with the normalizing denominator of `μ_𝔅`. -/
theorem upperNuTilde_mass_le (F : UpperFieldLaws X) (W : UpperWeights)
    (new : UpIdx → FiniteLaw (Slot → X)) {r : ℝ} (hr : 0 ≤ r) :
    upperNuTilde F W new r (fun _ => 1) ≤ upPoly W r := by
  rw [upperNuTilde_mass, ← sum_upCoeff]
  exact Finset.sum_le_sum fun ρ _ => retainedCoeff_le W hr ρ

/-- **`ν̃_𝔅` is a nonnegative measure.** -/
theorem upperNuTilde_nonneg (F : UpperFieldLaws X) (W : UpperWeights)
    (new : UpIdx → FiniteLaw (Slot → X)) {r : ℝ} (hr : 0 ≤ r) {f : (Slot → X) → ℝ}
    (hf : ∀ z, 0 ≤ f z) : 0 ≤ upperNuTilde F W new r f := by
  unfold upperNuTilde tildeMeasure
  rw [LinearMap.sum_apply]
  refine Finset.sum_nonneg fun ρ _ => ?_
  rw [LinearMap.smul_apply, smul_eq_mul, ← FiniteLaw.expect_eq_signedIntegral]
  exact mul_nonneg (retainedCoeff_nonneg W hr ρ) ((compLaw F new ρ).expect_nonneg hf)

/-- **The masses of the record changes**: zero for a kept or changed record (the replacing law
is a probability law), `-c_ρ` for a deleted record. -/
theorem recordChange_mass (F : UpperFieldLaws X) (W : UpperWeights)
    (new : UpIdx → FiniteLaw (Slot → X)) (r : ℝ) (ρ : UpIdx) :
    recordChange F W new r ρ (fun _ => 1) =
      if upperFate ρ = .deleted then -upCoeff W r ρ else 0 := by
  unfold recordChange
  cases h : upperFate ρ
  · simp
  · simp only [LinearMap.smul_apply, LinearMap.sub_apply, ← FiniteLaw.expect_eq_signedIntegral,
      FiniteLaw.expect_const, sub_self, smul_zero]
    simp
  · simp only [LinearMap.neg_apply, LinearMap.smul_apply, ← FiniteLaw.expect_eq_signedIntegral,
      FiniteLaw.expect_const, smul_eq_mul, mul_one]
    simp

/-- **Zero marginals of a changed record**: if the replacing law has the same integral as the old
component on a test function `f` (for instance a function of one half at the record's cut, when
the actual half marginals agree, `(F7)`, `prop:dense-comparison`(a), `prop:le-mixture`), the
change annihilates `f`. -/
theorem recordChange_half_marginal (F : UpperFieldLaws X) (W : UpperWeights)
    (new : UpIdx → FiniteLaw (Slot → X)) (r : ℝ) {ρ : UpIdx} (hρ : upperFate ρ = .changed)
    {f : (Slot → X) → ℝ} (hf : (new ρ).expect f = (upComponent F ρ).expect f) :
    recordChange F W new r ρ f = 0 := by
  unfold recordChange
  rw [hρ]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, ← FiniteLaw.expect_eq_signedIntegral, hf,
    sub_self, smul_zero]

end Sarkozy.UpperComparison
