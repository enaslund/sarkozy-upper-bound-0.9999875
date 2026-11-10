module

public import Sarkozy.ComparisonLawPaper.Upper
public import Sarkozy.UpperComparison.OldRecords
public import Sarkozy.RecordExpansion.Bound

@[expose] public section

/-!
# A replacing two-layer law of a changed upper record, and B2's `UpperAtomInputs` from them

`paper/sections/26_upper_comparison.tex`, `prop:record:upper`(i), "Records repaired" and "Records
replaced", with (F7), `prop:dense-comparison`(a) and `prop:le-mixture`. Every one of the `92`
changed records of an upper block is replaced by a two-layer law `π^new` on the labellings of the
record's two layers, which

* lives where the half law `λ_H` of the record is (both layers);
* has **both half marginals equal to `μ^old`**, the actual half marginal of the old record (the
  one-way repair (F7) by construction; `K₁'` of `prop:dense-comparison`(a) and the mixture of
  `prop:le-mixture` are couplings of `m₀ = μ^old` with itself);
* charges only labellings on which the six queries of `𝓔₆` have nonzero square differences at
  every prime of the block (`new_accepts`);
* has its change of centred pair forms `𝒞_{π^new} − 𝒞_{π^old}` bounded, symmetric part by `C^s`
  and skew part by `C^a`, relative to `μ^old` ((F7): `C^s = ρ_old + ρ'`, `C^a = ρ'`;
  `prop:dense-comparison`(b), `prop:le-mixture`: `d_s`, `d_a`).

This file proves that these data give all of B2's `UpperAtomInputs` at the block:

* `ReplRecord pr hne t φ`: the data above for the record `(t, φ)`;
* `ReplRecord.new_accepts`: the emitted law accepts `𝓔₆` at every prime of the block;
* **`ReplRecord.new_uniform`**: the emitted law has uniform one-slot marginals. This is *proved*
  from the two half-marginal identities and the vertex uniformity of V1's block field laws; it is
  the property "`ν_𝔅` has uniform one-slot marginals" of `prop:record:upper`(i);
* `ReplRecord.bracket_sym`, `bracket_skew`: W8's `oldRecord_sym_bracket`, `_skew_bracket`;
* `BlockRepl pr hne`: a replacing record for every changed record of the block;
* **`BlockRepl.toInputs`**: B2's `UpperAtomInputs pr hne W r`, with prices
  `π̃^ε_ρ = (c_ρ/P_μ(r)) C^ε_ρ` on the changed records;
* **`BlockRepl.price_le`**: if `C^s_ρ ≤ Cs_ρ r` and `C^a_ρ ≤ Ca_ρ r` for every changed record, the
  prices are at most W8's ledger coefficients (`SpecUpperRec`'s two conditions, through W8's
  `changed_sym_coef_eq`, `changed_skew_coef_eq`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.UpperRepair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison Sarkozy.Structured
open Sarkozy.ComparisonLawPaper (UpperAtomInputs upperEnv upperDelta changePart_smul)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- The emission `e_φ` of the record `(t, φ)`. -/
abbrev recEm (t : PType × PType) (φ : t.1.Pat × t.2.Pat) :
    Slot → t.1.field.Obj × t.2.field.Obj × Fin 2 :=
  upEmission (t.1.pat φ.1) (t.2.pat φ.2)

/-- **A replacing two-layer law of a changed upper record** (`prop:record:upper`(i); (F7),
`prop:dense-comparison`(a),(b), `prop:le-mixture`). The new law `lamN` on the labellings of the
two layers of the record `(t, φ)`, supported where the half law `λ_H` is, with both half marginals
the actual half marginal `μ^old` of the old record, accepting `𝓔₆` at every prime of the block,
and with symmetric and skew bounds `Cs`, `Ca` on the change of centred pair forms relative to
`μ^old`. -/
structure ReplRecord (hne : UpperNonempty pr) (t : PType × PType) (φ : t.1.Pat × t.2.Pat) where
  /-- The new two-layer law `π^new`. -/
  lamN : FiniteLaw (t.1.field.Obj × t.2.field.Obj × Fin 2 → BlockLabel pr)
  /-- Both layers of `π^new` lie where `λ_H` is. -/
  supp : LayersSupported lamN (recHalf pr hne t)
  /-- The layer-`0` marginal of `π^new` is `μ^old`. -/
  half0 : ∀ g : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ,
    lamN.expect (fun y => g (layerOf y 0)) = (recOld pr hne t).expect (fun y => g (layerOf y 0))
  /-- The layer-`1` marginal of `π^new` is `μ^old`. -/
  half1 : ∀ g : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ,
    lamN.expect (fun y => g (layerOf y 1)) = (recOld pr hne t).expect (fun y => g (layerOf y 0))
  /-- `π^new` accepts the six queries of `𝓔₆` at every prime of the block. -/
  accepts : ∀ y, lamN.weight y ≠ 0 → ∀ (j : Chamber) (i : ι),
    quadraticChar (ZMod (pr i))
      (y (recEm t φ (queryTarget j)) i - y (recEm t φ (querySource j)) i) = 1
  /-- The bound of the symmetric part of the change. -/
  Cs : ℝ
  /-- The bound of the skew part of the change. -/
  Ca : ℝ
  Cs_nonneg : 0 ≤ Cs
  Ca_nonneg : 0 ≤ Ca
  /-- The symmetric part of `𝒞_{π^new} − 𝒞_{π^old}` relative to `μ^old` is at most `Cs`. -/
  sym : ∀ φ' ψ', |(recChangeForm pr hne t lamN φ' ψ' + recChangeForm pr hne t lamN ψ' φ') / 2| ≤
    Cs * mnrm (recHalf pr hne t) (recU pr hne t) φ' * mnrm (recHalf pr hne t) (recU pr hne t) ψ'
  /-- The skew part of `𝒞_{π^new} − 𝒞_{π^old}` relative to `μ^old` is at most `Ca`. -/
  skew : ∀ φ' ψ', |(recChangeForm pr hne t lamN φ' ψ' - recChangeForm pr hne t lamN ψ' φ') / 2| ≤
    Ca * mnrm (recHalf pr hne t) (recU pr hne t) φ' * mnrm (recHalf pr hne t) (recU pr hne t) ψ'

namespace ReplRecord

variable {pr} {hne : UpperNonempty pr} {t : PType × PType} {φ : t.1.Pat × t.2.Pat}
  (R : ReplRecord pr hne t φ)

/-- The emitted replacing law `Π_new = e_φ(π^new)` on the slots. -/
noncomputable def new : FiniteLaw (Slot → BlockLabel pr) := emit R.lamN (recEm t φ)

/-- **The emitted law accepts `𝓔₆`** at every prime of the block (`prop:record:upper`(i),
"Acceptance and admissibility"). -/
theorem new_accepts {z : Slot → BlockLabel pr} (hz : R.new.weight z ≠ 0) (j : Chamber) (i : ι) :
    quadraticChar (ZMod (pr i)) (z (queryTarget j) i - z (querySource j) i) = 1 := by
  change (∑ y, if (fun y => y ∘ recEm t φ) y = z then R.lamN.weight y else 0) ≠ 0 at hz
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hφ : y ∘ recEm t φ = z := by
    by_contra hne'
    simp only [hne', ↓reduceIte] at hy
    exact hy rfl
  simp only [hφ, ↓reduceIte] at hy
  subst hφ
  exact R.accepts y hy j i

/-- **The emitted law has uniform one-slot marginals** (`prop:record:upper`(i)): every vertex of
the two layers has the law of a vertex of the old record, by the half-marginal identities, and the
vertex marginals of V1's block field laws are uniform. -/
theorem new_uniform : HasUniformMarginals R.new := by
  apply emit_uniform
  rintro ⟨o₀, o₁, ℓ⟩ g
  have hu := blockGraphLaw_vertex_uniform pr (fieldGraph t.1.field t.2.field (Fin 2))
    (hne.two _ _) (o₀, o₁, 0) g
  fin_cases ℓ
  · have h := R.half0 (fun x => g (x (o₀, o₁)))
    exact h.trans hu
  · have h := R.half1 (fun x => g (x (o₀, o₁)))
    exact h.trans hu

/-- The bracket of the symmetric part of `Π_new − Π_{𝔱,φ}` (W8's `oldRecord_sym_bracket`). -/
theorem bracket_sym :
    reservedCut.Bracket (R.Cs • upperEnv pr hne (true, ⟨t, φ⟩))
      (symPart reservedCut (signedIntegral R.new.weight -
        signedIntegral (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight))
      (R.Cs • upperEnv pr hne (true, ⟨t, φ⟩)) :=
  oldRecord_sym_bracket pr hne t φ R.lamN R.supp R.Cs_nonneg R.sym

/-- The bracket of the skew part of `Π_new − Π_{𝔱,φ}` (W8's `oldRecord_skew_bracket`). -/
theorem bracket_skew :
    reservedCut.Bracket (R.Ca • upperEnv pr hne (true, ⟨t, φ⟩))
      (skewPart reservedCut (signedIntegral R.new.weight -
        signedIntegral (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight))
      (R.Ca • upperEnv pr hne (true, ⟨t, φ⟩)) :=
  oldRecord_skew_bracket pr hne t φ R.lamN R.supp R.Ca_nonneg R.skew

/-- The bound of the part `e` of the change. -/
def C : ChangeType → ℝ
  | .sym => R.Cs
  | .skew => R.Ca

theorem C_nonneg : ∀ e, 0 ≤ R.C e
  | .sym => R.Cs_nonneg
  | .skew => R.Ca_nonneg

theorem bracket (e : ChangeType) :
    reservedCut.Bracket (R.C e • upperEnv pr hne (true, ⟨t, φ⟩))
      (changePart e (signedIntegral R.new.weight -
        signedIntegral (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight))
      (R.C e • upperEnv pr hne (true, ⟨t, φ⟩)) := by
  cases e
  · exact R.bracket_sym
  · exact R.bracket_skew

end ReplRecord

/-! ## A block -/

/-- **The replacing laws of an upper block**: a `ReplRecord` for every changed record. (Changed
records are two-layer records, `HsumProof.changed_layer`.) -/
def BlockRepl (hne : UpperNonempty pr) : Type :=
  ∀ (t : PType × PType) (φ : t.1.Pat × t.2.Pat), upperFate (true, ⟨t, φ⟩) = .changed →
    ReplRecord pr hne t φ

namespace BlockRepl

variable {pr} {hne : UpperNonempty pr} (R : BlockRepl pr hne)

/-- The replacing laws `new ρ` of the block (V1's component on the records that are not changed,
which `compLaw` never reads). -/
noncomputable def newLaw : UpIdx → FiniteLaw (Slot → BlockLabel pr)
  | (true, ⟨t, φ⟩) => if h : upperFate (true, ⟨t, φ⟩) = .changed then (R t φ h).new
      else upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)
  | (false, ⟨t, φ⟩) => upComponent (upperBlockFieldLaws pr hne) (false, ⟨t, φ⟩)

/-- The bounds `C^ε_ρ` of the block (`0` on the records that are not changed). -/
noncomputable def coef : UpIdx → ChangeType → ℝ
  | (true, ⟨t, φ⟩), e => if h : upperFate (true, ⟨t, φ⟩) = .changed then (R t φ h).C e else 0
  | (false, _), _ => 0

theorem coef_nonneg (ρ : UpIdx) (e : ChangeType) : 0 ≤ R.coef ρ e := by
  rcases ρ with ⟨b, t, φ⟩
  cases b
  · exact le_rfl
  · show 0 ≤ (if h : upperFate (true, ⟨t, φ⟩) = .changed then (R t φ h).C e else 0)
    split_ifs with h
    · exact (R t φ h).C_nonneg e
    · exact le_rfl

/-- Changed records are two-layer records (`def:upper-comparison`(b)). -/
theorem changed_true : ∀ ρ : UpIdx, upperFate ρ = .changed → ρ.1 = true := by
  decide +kernel

theorem newLaw_eq (t : PType × PType) (φ : t.1.Pat × t.2.Pat)
    (h : upperFate (true, ⟨t, φ⟩) = .changed) : R.newLaw (true, ⟨t, φ⟩) = (R t φ h).new := by
  simp only [newLaw, h, ↓reduceDIte]

theorem coef_eq (t : PType × PType) (φ : t.1.Pat × t.2.Pat)
    (h : upperFate (true, ⟨t, φ⟩) = .changed) (e : ChangeType) :
    R.coef (true, ⟨t, φ⟩) e = (R t φ h).C e := by
  simp only [coef, h, ↓reduceDIte]

theorem new_accepts : ∀ ρ, upperFate ρ = .changed → ∀ z, (R.newLaw ρ).weight z ≠ 0 →
    ∀ (j : Chamber) (i : ι),
      quadraticChar (ZMod (pr i)) (z (queryTarget j) i - z (querySource j) i) = 1 := by
  rintro ⟨b, t, φ⟩ h z hz j i
  obtain rfl : b = true := changed_true _ h
  rw [R.newLaw_eq t φ h] at hz
  exact (R t φ h).new_accepts hz j i

theorem new_uniform : ∀ ρ, upperFate ρ = .changed → HasUniformMarginals (R.newLaw ρ) := by
  rintro ⟨b, t, φ⟩ h
  obtain rfl : b = true := changed_true _ h
  rw [R.newLaw_eq t φ h]
  exact (R t φ h).new_uniform

/-- The prices `π̃^ε_ρ = (c_ρ/P_μ(r)) C^ε_ρ`. -/
noncomputable def price (W : UpperWeights) (r : ℝ) (ρ : UpIdx) (e : ChangeType) : ℝ :=
  upCoeff W r ρ / upPoly W r * R.coef ρ e

theorem price_nonneg (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) (ρ : UpIdx) (e : ChangeType) :
    0 ≤ R.price W r ρ e :=
  mul_nonneg (div_nonneg (upCoeff_nonneg W hr ρ)
    (lt_of_lt_of_le one_pos (one_le_upPoly W hr)).le) (R.coef_nonneg ρ e)

/-- **The bracket of a changed record** (`prop:record:upper`(i)): the part `e` of the normalized
change `P_μ(r)⁻¹ Δ_ρ` lies in the bracket of `π̃^ε_ρ Diag(m_+(Π_ρ))`. -/
theorem bracket (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) :
    ∀ ρ, upperFate ρ = .changed → ∀ e,
      reservedCut.Bracket (R.price W r ρ e • upperEnv pr hne ρ)
        (changePart e (upperDelta pr hne W R.newLaw r ρ))
        (R.price W r ρ e • upperEnv pr hne ρ) := by
  rintro ⟨b, t, φ⟩ h e
  obtain rfl : b = true := changed_true _ h
  set a := upCoeff W r (true, ⟨t, φ⟩) / upPoly W r with ha_def
  have ha : 0 ≤ a := div_nonneg (upCoeff_nonneg W hr _)
    (lt_of_lt_of_le one_pos (one_le_upPoly W hr)).le
  have hΔ : upperDelta pr hne W R.newLaw r (true, ⟨t, φ⟩) =
      a • (signedIntegral (R t φ h).new.weight -
        signedIntegral (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight) := by
    unfold upperDelta recordChange
    rw [h]
    simp only [R.newLaw_eq t φ h]
    rw [smul_smul, inv_mul_eq_div]
  have hB := bracket_smul ((R t φ h).bracket e) ha
  rw [smul_smul, ← changePart_smul] at hB
  rw [hΔ]
  have hp : R.price W r (true, ⟨t, φ⟩) e = a * (R t φ h).C e := by
    unfold price
    rw [R.coef_eq t φ h e]
  rw [hp]
  exact hB

/-- **B2's `UpperAtomInputs` of the block** from its replacing laws (`prop:record:upper`(i)). -/
noncomputable def toInputs (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) :
    UpperAtomInputs pr hne W r where
  new := R.newLaw
  new_accepts := R.new_accepts
  new_uniform := R.new_uniform
  π := R.price W r
  π_nonneg := R.price_nonneg W hr
  bracket := R.bracket W hr

theorem toInputs_π (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) :
    (R.toInputs W hr).π = R.price W r := rfl

/-- **The prices against W8's ledger** (`SpecUpperRec`'s conditions): if every changed record has
`C^s_ρ ≤ Cs_ρ r` and `C^a_ρ ≤ Ca_ρ r`, its prices are at most the ledger coefficients over
`P_μ(r)`. -/
theorem price_le (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) (Cs Ca : UpIdx → ℝ)
    (hCs : ∀ i, 0 ≤ Cs i) (hCa : ∀ i, 0 ≤ Ca i)
    (hs : ∀ ρ, upperFate ρ = .changed → R.coef ρ .sym ≤ Cs ρ * r)
    (ha : ∀ ρ, upperFate ρ = .changed → R.coef ρ .skew ≤ Ca ρ * r) :
    (∀ ρ, upperFate ρ = .changed →
      (R.toInputs W hr).π ρ .sym ≤ (upperLedger W Cs Ca hCs hCa).symCoef r ρ / upPoly W r) ∧
    (∀ ρ, upperFate ρ = .changed →
      (R.toInputs W hr).π ρ .skew ≤ (upperLedger W Cs Ca hCs hCa).skewCoef r ρ / upPoly W r) := by
  have hw : ∀ ρ, 0 ≤ upCoeff W r ρ / upPoly W r := fun ρ =>
    div_nonneg (upCoeff_nonneg W hr ρ) (lt_of_lt_of_le one_pos (one_le_upPoly W hr)).le
  refine ⟨fun ρ h => ?_, fun ρ h => ?_⟩
  · rw [toInputs_π, ← changed_sym_coef_eq W Cs Ca hCs hCa r h]
    exact mul_le_mul_of_nonneg_left (hs ρ h) (hw ρ)
  · rw [toInputs_π, ← changed_skew_coef_eq W Cs Ca hCs hCa r h]
    exact mul_le_mul_of_nonneg_left (ha ρ h) (hw ρ)

end BlockRepl

end Sarkozy.UpperRepair
