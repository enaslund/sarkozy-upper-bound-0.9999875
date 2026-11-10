module

public import Sarkozy.ComparisonLawPaper.Assembly
public import Sarkozy.UpperComparison.Envelope

@[expose] public section

/-!
# (CP4) at an atom whose comparison law deletes one symmetric record

`rem:cp:charging`(i) and `lem:frontier:iidenergy`(ii) (`paper/sections/19_prefix.tex`): at a
square-clique atom `{p}` the comparison law is `ν_p = λ_p - λ^ex_p`, the deletion of the exception
`λ^ex_p` of the queries; the change `-λ^ex_p` is symmetric at `ι` and is charged to its symmetric
part with `π̃^s = λ^ex_p(1)`, `π̃^a = 0`.

* `DeletionInputs μ acc Q`: a reference law `μ`, the normalized deleted record `κ̄` (a law,
  symmetric at `ι`, with uniform one-slot marginals), its mass `ω ∈ [0, 1)`, and the normalized
  retained law `ν̄` with `(1 - ω) ν̄ = μ - ω κ̄`, accepted. Its uniform one-slot marginals follow
  from those of `μ` and `κ̄` (`DeletionInputs.unif_of`).
* **`DeletionInputs.toAtom`**: the `AtomComparison` of the atom, relative to `λ = μ`: one component
  `(1 - ω) ν̄`, one change `Δ = -ω κ̄`, the envelope `D = Diag_ι(m_+(κ̄))` for both types (W8's
  `envelope_of_law`), `π̃^s = ω`, `π̃^a = 0`; the brackets from W8's `deleted_record_bracket`
  (`rem:cp:charging`(i)) and the vanishing skew part.
* `toAtom_sprice`, `toAtom_aprice`: the prices `s = ω q^{2a}`, `a = 0`; `toAtom_single`.
* `AtomComparison.congrLam`: transport along an equality of first-stage laws (same prices).
* Non-vacuity: `DeletionInputs.trivial` (no deletion, `ν̄ = κ̄ = μ`, `ω = 0`) for any symmetric
  accepted law with uniform marginals.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.ComparisonLawPaper

open Sarkozy.TheoremC Sarkozy.RecordExpansion

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]

/-- **Transport of atom data along an equality of first-stage laws.** The prices are unchanged
(`congrLam_sprice`, `congrLam_aprice` are `rfl`). -/
def AtomComparison.congrLam {lam lam' : SlotMeasure X} {acc : X → X → Prop} {E : Type}
    {Q : Queries E} (C : AtomComparison lam acc Q) (h : lam = lam') :
    AtomComparison lam' acc Q where
  I := C.I
  c := C.c
  w := C.w
  law := C.law
  w_pos := C.w_pos
  mass_pos := C.mass_pos
  accept := C.accept
  unif := C.unif
  T := C.T
  Δ := C.Δ
  change := h ▸ C.change
  D := C.D
  D_prob := C.D_prob
  D_diag := C.D_diag
  D_unif := C.D_unif
  πt := C.πt
  πt_nonneg := C.πt_nonneg
  bracket := C.bracket

theorem AtomComparison.congrLam_sprice {lam lam' : SlotMeasure X} {acc : X → X → Prop} {E : Type}
    {Q : Queries E} (C : AtomComparison lam acc Q) (h : lam = lam') (sel : ℝ) :
    (C.congrLam h).sprice sel = C.sprice sel := rfl

theorem AtomComparison.congrLam_aprice {lam lam' : SlotMeasure X} {acc : X → X → Prop} {E : Type}
    {Q : Queries E} (C : AtomComparison lam acc Q) (h : lam = lam') (sel : ℝ) :
    (C.congrLam h).aprice sel = C.aprice sel := rfl

/-- **The data of an atom whose comparison law deletes one symmetric record** (`rem:cp:charging`(i),
`lem:frontier:iidenergy`(ii)), relative to the reference law `μ` (the atom's first-stage law). -/
structure DeletionInputs (μ : FiniteLaw (Slot → X)) (acc : X → X → Prop) {E : Type}
    (Q : Queries E) where
  /-- The normalized deleted record `κ̄ = λ^ex/λ^ex(1)`. -/
  κ : FiniteLaw (Slot → X)
  /-- The deleted mass `ω = λ^ex(1)`. -/
  ω : ℝ
  ω_nonneg : 0 ≤ ω
  ω_lt_one : ω < 1
  /-- The normalized retained law `ν̄ = (μ - ω κ̄)/(1 - ω)`. -/
  ν : FiniteLaw (Slot → X)
  /-- `(1 - ω) ν̄ = μ - ω κ̄`. -/
  decomp : ∀ z, (1 - ω) * ν.weight z = μ.weight z - ω * κ.weight z
  /-- The deleted record is symmetric at `ι`. -/
  κ_sym : IsSymmetricAt reservedCut (signedIntegral κ.weight)
  /-- The deleted record has uniform one-slot marginals. -/
  κ_unif : HasUniformMarginals κ
  /-- Every query is accepted by the retained law, almost surely. -/
  accept : ∀ z, ν.weight z ≠ 0 → ∀ e, acc (z (Q.source e)) (z (Q.target e))

namespace DeletionInputs

variable {μ : FiniteLaw (Slot → X)} {acc : X → X → Prop} {E : Type} {Q : Queries E}
  (D : DeletionInputs μ acc Q)

omit [DecidableEq X] in
/-- **The retained law has uniform one-slot marginals** if the reference law has: `(1 - ω) ν̄ =
μ - ω κ̄` and both `μ`, `κ̄` have uniform one-slot marginals. -/
theorem unif_of (hμ : HasUniformMarginals μ) : HasUniformMarginals D.ν := by
  intro v f
  have hω : (1 - D.ω) ≠ 0 := by linarith [D.ω_lt_one]
  have h1 := hμ v f
  have h2 := D.κ_unif v f
  unfold FiniteLaw.expect at h1 h2 ⊢
  apply mul_left_cancel₀ hω
  rw [mul_sum]
  have hs : ∑ z, (1 - D.ω) * (D.ν.weight z * f (z v)) =
      ∑ z, μ.weight z * f (z v) - D.ω * ∑ z, D.κ.weight z * f (z v) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun z _ => ?_
    have := D.decomp z
    linear_combination f (z v) * this
  rw [hs, h1, h2]
  ring

/-- The change `Δ = -ω κ̄`. -/
noncomputable def delta : SlotMeasure X := -(D.ω • signedIntegral D.κ.weight)

omit [DecidableEq X] in
theorem symPart_delta : symPart reservedCut D.delta = D.delta := by
  unfold delta symPart
  rw [reflect_neg, reflect_smul, D.κ_sym]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.neg_apply, smul_eq_mul]
  ring

omit [DecidableEq X] in
theorem skewPart_delta : skewPart reservedCut D.delta = 0 := by
  unfold delta skewPart
  rw [reflect_neg, reflect_smul, D.κ_sym]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply, smul_eq_mul,
    LinearMap.zero_apply]
  ring

/-- The envelope `Diag_ι(m_+(κ̄))`. -/
noncomputable def env : SlotMeasure X :=
  reservedCut.diagonalLaw (plusMarginal reservedCut D.κ.weight)

/-- The unpriced prices: `π̃^s = ω`, `π̃^a = 0`. -/
noncomputable def piT : ChangeType → ℝ
  | .sym => D.ω
  | .skew => 0

omit [DecidableEq X] [Nonempty X] in
theorem zero_positive : reservedCut.Positive (0 : SlotMeasure X) :=
  ⟨fun _ _ => by simp [ReflectionCut.form], fun _ => by simp [ReflectionCut.form]⟩

/-- **The `AtomComparison` of a deletion**: one component `(1 - ω) ν̄`, one change `-ω κ̄`. -/
noncomputable def toAtom (hμ : HasUniformMarginals μ) :
    AtomComparison (signedIntegral μ.weight) acc Q where
  I := Unit
  c _ := 1
  w _ := 1 - D.ω
  law _ := D.ν
  w_pos _ := by linarith [D.ω_lt_one]
  mass_pos := by simp only [Finset.univ_unique, sum_singleton, one_mul]; linarith [D.ω_lt_one]
  accept _ := D.accept
  unif _ := D.unif_of hμ
  T := Unit
  Δ _ := D.delta
  change := by
    apply LinearMap.ext
    intro f
    simp only [Finset.univ_unique, sum_singleton, one_mul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, delta, LinearMap.neg_apply]
    change (1 - D.ω) * ∑ z, D.ν.weight z * f z - ∑ z, μ.weight z * f z =
      -(D.ω * ∑ z, D.κ.weight z * f z)
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_neg_distrib]
    refine sum_congr rfl fun z _ => ?_
    have := D.decomp z
    linear_combination f z * this
  D _ _ := D.env
  D_prob _ _ := (UpperComparison.envelope_of_law reservedCut D.κ D.κ_unif).1
  D_diag _ _ := (UpperComparison.envelope_of_law reservedCut D.κ D.κ_unif).2.1
  D_unif _ _ := (UpperComparison.envelope_of_law reservedCut D.κ D.κ_unif).2.2
  πt _ := D.piT
  πt_nonneg _ e := by cases e <;> simp [piT, D.ω_nonneg]
  bracket _ e := by
    cases e
    · change reservedCut.Bracket (D.ω • D.env) (symPart reservedCut D.delta) (D.ω • D.env)
      rw [symPart_delta]
      exact UpperComparison.deleted_record_bracket reservedCut D.κ.nonneg D.κ_sym D.ω_nonneg
    · change reservedCut.Bracket ((0 : ℝ) • D.env) (skewPart reservedCut D.delta)
        ((0 : ℝ) • D.env)
      rw [skewPart_delta, zero_smul]
      exact zero_positive.bracket_self

/-- The deletion is one nonnegative component. -/
theorem toAtom_single (hμ : HasUniformMarginals μ) : (D.toAtom hμ).IsSingle :=
  ⟨Fintype.card_unit, fun _ => zero_le_one⟩

/-- The symmetric price of a deletion: `s = ω q^{2a}`. -/
theorem toAtom_sprice (hμ : HasUniformMarginals μ) (sel : ℝ) :
    (D.toAtom hμ).sprice sel = D.ω * sel := by
  change ∑ _t : Unit, D.piT .sym * sel = _
  simp [piT]

/-- The skew price of a deletion is zero. -/
theorem toAtom_aprice (hμ : HasUniformMarginals μ) (sel : ℝ) :
    (D.toAtom hμ).aprice sel = 0 := by
  change ∑ _t : Unit, D.piT .skew * sel = _
  simp [piT]

end DeletionInputs

/-- **Non-vacuity of `DeletionInputs`**: no deletion (`ω = 0`, `κ̄ = ν̄ = μ`), for a law `μ` that is
symmetric at `ι`, has uniform one-slot marginals and is accepted. -/
noncomputable def DeletionInputs.trivial {μ : FiniteLaw (Slot → X)} {acc : X → X → Prop}
    {E : Type} {Q : Queries E} (hsym : IsSymmetricAt reservedCut (signedIntegral μ.weight))
    (hunif : HasUniformMarginals μ)
    (hacc : ∀ z, μ.weight z ≠ 0 → ∀ e, acc (z (Q.source e)) (z (Q.target e))) :
    DeletionInputs μ acc Q where
  κ := μ
  ω := 0
  ω_nonneg := le_rfl
  ω_lt_one := zero_lt_one
  ν := μ
  decomp z := by ring
  κ_sym := hsym
  κ_unif := hunif
  accept := hacc

end Sarkozy.ComparisonLawPaper
