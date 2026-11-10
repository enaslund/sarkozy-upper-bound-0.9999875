module

public import Sarkozy.PartVRecords.OneStageBlock
public import Sarkozy.Comparison.FoldedEnergy

@[expose] public section

/-!
# Eligible records and repairs (`def:record:eligible`)

`paper/sections/22_variance.tex`, `def:record:eligible` and `eq:record:zero-marginal`.

The **eligible records** of a middle block are `φ ∈ {F₁, F₂, E₀, E₁}` (`Eligible`). For such `φ`:
* `Π_{φ,𝔅}` is the normalized reference record, the two-layer component of `φ`
  (`FrameData.refRec`; V1's `midComponent F (true, ⟨t, φ⟩)`);
* `m_{φ,𝔅}` is its actual half marginal at `ι` (`FrameData.halfLaw`, the plus-half marginal
  `Sarkozy.Comparison.halfMarginalPlus`; the paper notes it is the same on both halves, which is
  the layer-swap symmetry of the record and is not used here);
* `D_{φ,𝔅} = Diag_ι(m_{φ,𝔅})` is its *selected diagonal* (`FrameData.selDiag`, through
  `ReflectionCut.diagonalLaw`);
* `J_{φ,𝔅}` is the law under which the two `ι`-halves are independent with law `m_{φ,𝔅}` each, the
  *product of the actual half marginals* (`FrameData.halfProd`);
* a *repair* of `φ` (`FrameData.IsRepair`) is a signed measure `Π'` of mass one that is a finite
  real combination of nonnegative measures, each invariant (here: under a given predicate `Inv`,
  for block labels the square-affine maps acting independently at the primes,
  `SquareAffineInvariant`) and with actual half marginal `m_{φ,𝔅}` on both sides of `ι`;
* the *record difference* `Δ_{φ,𝔅}` is given by its bilinear form
  `⟨ψ, Δψ'⟩ = ∫ ψ(z₊) ψ'(z₋) d(Π' - Π)(z)` (`FrameData.recDiffForm`, the cut form
  `reservedCut.form (Π' - Π)`), with symmetric and skew parts `recDiffSym`, `recDiffSkew`.

**Proved:** `eq:record:zero-marginal`, `Δ 1 = Δ^* 1 = 0`, in the form
`⟨ψ, Δ 1⟩ = ⟨1, Δ ψ'⟩ = 0` for every repair (`recDiffForm_one_right`, `recDiffForm_one_left`),
and the same for the symmetric and skew parts; and the decomposition of the form into its
symmetric and skew parts.

**Interpretation choices.**
1. The nonnegative measures of a repair are taken of mass one (probability measures with half
   marginals exactly `m_φ`); a nonnegative measure with half marginals `c · m_φ` is `c` times
   such a law, so this is no restriction.
2. The operator `Δ_{φ,𝔅}` on `L²(m_{φ,𝔅})` is represented by its bilinear form, which is what
   every later use reads; the operator itself is not constructed.
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.Labellings Sarkozy.PartV Sarkozy.TheoremC Sarkozy.Comparison

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **The eligible records** `F₁, F₂, E₀, E₁` of a middle block. -/
inductive Eligible where
  | F1 | F2 | E0 | E1
  deriving DecidableEq

/-- The pattern of an eligible record: `F₁ = (D, 1)`, `F₂ = (D, 2)`, `E₀ = (S, 0)`,
`E₁ = (S, 1)`. -/
def Eligible.idx : Eligible → Σ t : PType, t.Pat
  | F1 => ⟨.D, (1 : Fin 3)⟩
  | F2 => ⟨.D, (2 : Fin 3)⟩
  | E0 => ⟨.S, (0 : Fin 2)⟩
  | E1 => ⟨.S, (1 : Fin 2)⟩

/-- The plus-half marginal is linear in the measure. -/
theorem halfMarginalPlus_sub (c : ReflectionCut Slot) (K L : SlotMeasure X) (x : c.Half → X) :
    halfMarginalPlus c (K - L) x = halfMarginalPlus c K x - halfMarginalPlus c L x := rfl

theorem halfMarginalMinus_sub (c : ReflectionCut Slot) (K L : SlotMeasure X) (x : c.Half → X) :
    halfMarginalMinus c (K - L) x = halfMarginalMinus c K x - halfMarginalMinus c L x := rfl

/-- The cut form against the constant on the right reads the plus-half marginal. -/
theorem form_one_right (c : ReflectionCut Slot) (K : SlotMeasure X) (ψ : (c.Half → X) → ℝ) :
    c.form K ψ (fun _ => 1) = ∑ x, ψ x * halfMarginalPlus c K x := by
  unfold ReflectionCut.form halfMarginalPlus
  have he : (fun z : Slot → X => ψ (fun v => z v.1) * 1) =
      ∑ x, ψ x • (fun z : Slot → X => if (fun v : c.Half => z v.1) = x then (1 : ℝ) else 0) := by
    funext z
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      mem_univ, ↓reduceIte]
  rw [he, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- The cut form against the constant on the left reads the minus-half marginal. -/
theorem form_one_left (c : ReflectionCut Slot) (K : SlotMeasure X) (ψ : (c.Half → X) → ℝ) :
    c.form K (fun _ => 1) ψ = ∑ x, ψ x * halfMarginalMinus c K x := by
  unfold ReflectionCut.form halfMarginalMinus
  have he : (fun z : Slot → X => 1 * ψ (fun v => z (c.flip v.1))) =
      ∑ x, ψ x • (fun z : Slot → X =>
        if (fun v : c.Half => z (c.flip v.1)) = x then (1 : ℝ) else 0) := by
    funext z
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, one_mul, Finset.sum_ite_eq,
      mem_univ, ↓reduceIte]
  rw [he, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Invariance of a slot measure on block labels under the square-affine maps
`z_{v,p} ↦ α_p z_{v,p} + β_p`, `χ_p(α_p) = 1`, acting independently at the primes. -/
def SquareAffineInvariant {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ)
    [∀ i, Fact (pr i).Prime] (κ : SlotMeasure (BlockLabel pr)) : Prop :=
  ∀ (α β : BlockLabel pr), (∀ i, quadraticChar (ZMod (pr i)) (α i) = 1) →
    ∀ H : (Slot → BlockLabel pr) → ℝ, κ (fun z => H (fun v i => α i * z v i + β i)) = κ H

namespace FrameData

variable (D : FrameData X)

/-- **The normalized reference record** `Π_{φ,𝔅}` of an eligible record (a probability law). -/
noncomputable def refRec (φ : Eligible) : SlotMeasure X :=
  signedIntegral (midComponent D.F (true, φ.idx)).weight

/-- **The actual half marginal** `m_{φ,𝔅}` of `Π_{φ,𝔅}` at `ι` (plus half). -/
noncomputable def halfLaw (φ : Eligible) : (reservedCut.Half → X) → ℝ :=
  halfMarginalPlus reservedCut (D.refRec φ)

/-- **The selected diagonal** `D_{φ,𝔅} = Diag_ι(m_{φ,𝔅})`. -/
noncomputable def selDiag (φ : Eligible) : SlotMeasure X :=
  reservedCut.diagonalLaw (D.halfLaw φ)

/-- **The product of the actual half marginals** `J_{φ,𝔅}`: the two `ι`-halves independent with
law `m_{φ,𝔅}` each. -/
noncomputable def halfProd (φ : Eligible) : SlotMeasure X :=
  sampleIntegral (fun p : (reservedCut.Half → X) × (reservedCut.Half → X) =>
    D.halfLaw φ p.1 * D.halfLaw φ p.2) (fun p => reservedCut.join p.1 p.2)

/-- **A repair of `φ`** (`def:record:eligible`): a signed measure of mass one that is a finite real
combination `∑ cᵢ κᵢ` of probability measures `κᵢ`, each satisfying the invariance `Inv` and with
actual half marginal `m_{φ,𝔅}` on both sides of `ι`. -/
def IsRepair (Inv : SlotMeasure X → Prop) (φ : Eligible) (Rep : SlotMeasure X) : Prop :=
  mass Rep = 1 ∧ ∃ (n : ℕ) (c : Fin n → ℝ) (κ : Fin n → SlotMeasure X),
    Rep = ∑ i, c i • κ i ∧ ∀ i, IsProbability (κ i) ∧ Inv (κ i) ∧
      halfMarginalPlus reservedCut (κ i) = D.halfLaw φ ∧
      halfMarginalMinus reservedCut (κ i) = D.halfLaw φ

/-- **The record difference** `Δ_{φ,𝔅}`, through its bilinear form
`⟨ψ, Δψ'⟩ = ∫ ψ(z₊) ψ'(z₋) d(Π' - Π)(z)`. -/
noncomputable def recDiffForm (φ : Eligible) (Rep : SlotMeasure X)
    (ψ ψ' : (reservedCut.Half → X) → ℝ) : ℝ :=
  reservedCut.form (Rep - D.refRec φ) ψ ψ'

/-- The symmetric part `Δ^s` of the record difference. -/
noncomputable def recDiffSym (φ : Eligible) (Rep : SlotMeasure X)
    (ψ ψ' : (reservedCut.Half → X) → ℝ) : ℝ :=
  (D.recDiffForm φ Rep ψ ψ' + D.recDiffForm φ Rep ψ' ψ) / 2

/-- The skew part `Δ^a` of the record difference. -/
noncomputable def recDiffSkew (φ : Eligible) (Rep : SlotMeasure X)
    (ψ ψ' : (reservedCut.Half → X) → ℝ) : ℝ :=
  (D.recDiffForm φ Rep ψ ψ' - D.recDiffForm φ Rep ψ' ψ) / 2

theorem recDiff_sym_add_skew (φ : Eligible) (Rep : SlotMeasure X)
    (ψ ψ' : (reservedCut.Half → X) → ℝ) :
    D.recDiffSym φ Rep ψ ψ' + D.recDiffSkew φ Rep ψ ψ' = D.recDiffForm φ Rep ψ ψ' := by
  unfold recDiffSym recDiffSkew
  ring

/-- The half marginals of a repair are those of its components. -/
theorem IsRepair.halfMarginals {Inv : SlotMeasure X → Prop} {φ : Eligible} {Rep : SlotMeasure X}
    (h : D.IsRepair Inv φ Rep) :
    halfMarginalPlus reservedCut Rep = D.halfLaw φ ∧
      halfMarginalMinus reservedCut Rep = D.halfLaw φ := by
  obtain ⟨hm, n, c, κ, rfl, hκ⟩ := h
  have hmass : ∑ i, c i = 1 := by
    rw [← hm]
    unfold mass
    rw [LinearMap.sum_apply]
    refine sum_congr rfl fun i _ => ?_
    have h1 : κ i (fun _ => 1) = 1 := (hκ i).1.2
    rw [LinearMap.smul_apply, smul_eq_mul, h1, mul_one]
  constructor
  · funext x
    unfold halfMarginalPlus at hκ ⊢
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, smul_eq_mul]
    have hx : ∀ i, κ i (fun z => if (fun v : reservedCut.Half => z v.1) = x then 1 else 0) =
        D.halfLaw φ x := fun i => congrFun (hκ i).2.2.1 x
    simp only [hx, ← sum_mul, hmass, one_mul]
  · funext x
    unfold halfMarginalMinus at hκ ⊢
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, smul_eq_mul]
    have hx : ∀ i, κ i (fun z => if (fun v : reservedCut.Half => z (reservedCut.flip v.1)) = x
        then 1 else 0) = D.halfLaw φ x := fun i => congrFun (hκ i).2.2.2 x
    simp only [hx, ← sum_mul, hmass, one_mul]

/-- **`eq:record:zero-marginal`, `Δ^* 1 = 0`**: `⟨ψ, Δ 1⟩ = 0` for every repair, since the repair
and the reference record have the same plus-half marginal. -/
theorem recDiffForm_one_right {Inv : SlotMeasure X → Prop} {φ : Eligible} {Rep : SlotMeasure X}
    (h : D.IsRepair Inv φ Rep) (ψ : (reservedCut.Half → X) → ℝ) :
    D.recDiffForm φ Rep ψ (fun _ => 1) = 0 := by
  unfold recDiffForm
  rw [form_one_right]
  have hm := h.halfMarginals.1
  simp only [halfMarginalPlus_sub, hm]
  unfold halfLaw
  simp

/-- **`eq:record:zero-marginal`, `Δ 1 = 0`** on the other side, given that the reference record has
the same minus-half marginal (`hsym`, the layer-swap symmetry of the record). -/
theorem recDiffForm_one_left {Inv : SlotMeasure X → Prop} {φ : Eligible} {Rep : SlotMeasure X}
    (h : D.IsRepair Inv φ Rep)
    (hsym : halfMarginalMinus reservedCut (D.refRec φ) = D.halfLaw φ)
    (ψ : (reservedCut.Half → X) → ℝ) :
    D.recDiffForm φ Rep (fun _ => 1) ψ = 0 := by
  unfold recDiffForm
  rw [form_one_left]
  have hm := h.halfMarginals.2
  simp only [halfMarginalMinus_sub, hm, hsym, sub_self, mul_zero, sum_const_zero]

/-- The symmetric and skew parts also annihilate the constants (`eq:record:zero-marginal`). -/
theorem recDiff_parts_one {Inv : SlotMeasure X → Prop} {φ : Eligible} {Rep : SlotMeasure X}
    (h : D.IsRepair Inv φ Rep)
    (hsym : halfMarginalMinus reservedCut (D.refRec φ) = D.halfLaw φ)
    (ψ : (reservedCut.Half → X) → ℝ) :
    D.recDiffSym φ Rep ψ (fun _ => 1) = 0 ∧ D.recDiffSkew φ Rep ψ (fun _ => 1) = 0 := by
  unfold recDiffSym recDiffSkew
  rw [D.recDiffForm_one_right h, D.recDiffForm_one_left h hsym]
  norm_num

/-- The reference record is a probability law. -/
theorem refRec_isProbability (φ : Eligible) : IsProbability (D.refRec φ) :=
  ⟨isNonneg_law _, mass_law _⟩

end FrameData

end Sarkozy.PartVRecords
