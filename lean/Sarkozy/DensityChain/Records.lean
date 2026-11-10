module

public import Sarkozy.BracketEnergy.EnvFirst
public import Sarkozy.TheoremCBlock.StructuredEnvelopeEnergyGlue

@[expose] public section

/-!
# Condition (b) of `def:record:structured-energy` for the selected laws, from the data

`def:record:structured-energy`(b) asks that the variation `|ρ|` of the selected law have every
one-slot marginal equal to `‖ρ‖ Unif(X_E)`. In the chain this is the hypothesis
`selectedMarginalsUniform (selectedWeight E (crtLaws … (termLaw …)))` (`hsel`). This file proves
it from the data:

* positive records (`def:cp:records`: nonnegative, uniform one-slot marginals) are closed under
  sums and nonnegative multiples (`isPositiveRecord_add`, `_smul`, `_sum`) and under the CRT
  relabelling (`isPositiveRecord_pullLaw`);
* a positive record satisfies (b) (`selectedMarginalsUniform_lawDensity`);
* (b) is stable under products over atoms (`selectedMarginalsUniform_prod`);
* the selected laws of the data are positive records: the reserved records `Ñ_{0,𝔟} − μ_𝔟 =
  ∑_i κ^u_i` (`isPositiveRecord_recLaw`), the envelope increments `∑_i c_i κ_i`
  (`isPositiveRecord_envIncL`, `_envIncR`) and the wrapping increments
  `∑_t (π^s D^s + π^a D^a)` (`isPositiveRecord_wrapInc`);
* **`hsel_of_positive`**: hence (b) holds for every term `(f, g)` whose increments `Q_𝔟` are
  positive records.
-/

namespace Sarkozy.DensityChain

open Finset Function
open scoped BigOperators
open Sarkozy.TheoremC Sarkozy.Structured Sarkozy.EnvelopeEnergiesPaper Sarkozy.BlockFrame
open Sarkozy.BracketEnergy

section General

variable {X : Type} [Fintype X]

theorem isPositiveRecord_zero : IsPositiveRecord (0 : SlotMeasure X) := by
  refine ⟨fun f _ => le_refl _, fun v g => ?_⟩
  simp [mass]

theorem isPositiveRecord_add {κ₁ κ₂ : SlotMeasure X} (h₁ : IsPositiveRecord κ₁)
    (h₂ : IsPositiveRecord κ₂) : IsPositiveRecord (κ₁ + κ₂) := by
  refine ⟨fun f hf => ?_, fun v g => ?_⟩
  · rw [LinearMap.add_apply]
    exact add_nonneg (h₁.1 f hf) (h₂.1 f hf)
  · rw [LinearMap.add_apply, h₁.2 v g, h₂.2 v g]
    unfold mass
    rw [LinearMap.add_apply]
    ring

theorem isPositiveRecord_smul {κ : SlotMeasure X} (h : IsPositiveRecord κ) {c : ℝ} (hc : 0 ≤ c) :
    IsPositiveRecord (c • κ) := by
  refine ⟨fun f hf => ?_, fun v g => ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg hc (h.1 f hf)
  · rw [LinearMap.smul_apply, smul_eq_mul, h.2 v g]
    unfold mass
    rw [LinearMap.smul_apply, smul_eq_mul]
    ring

theorem isPositiveRecord_sum {I : Type*} (s : Finset I) (κ : I → SlotMeasure X)
    (h : ∀ i ∈ s, IsPositiveRecord (κ i)) : IsPositiveRecord (∑ i ∈ s, κ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPositiveRecord_zero
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact isPositiveRecord_add (h i (mem_insert_self i s))
      (ih fun j hj => h j (mem_insert_of_mem hj))

/-- The CRT relabelling of a positive record is a positive record. -/
theorem isPositiveRecord_pullLaw {X' : Type} [Fintype X'] (e : X' ≃ X)
    {Λ : SlotMeasure X} (h : IsPositiveRecord Λ) : IsPositiveRecord (pullLaw e Λ) := by
  refine ⟨fun f hf => ?_, fun v g => ?_⟩
  · rw [pullLaw_apply]
    exact h.1 _ fun x => hf _
  · rw [pullLaw_apply]
    have h1 := h.2 v (fun x => g (e.symm x))
    rw [h1]
    unfold mass
    rw [pullLaw_apply]
    congr 2
    · exact Equiv.sum_comp e.symm g
    · exact_mod_cast (Fintype.card_congr e).symm

/-- A linear functional on a finite function space is the sum against its point weights. -/
theorem apply_eq_sum_lawDensity' [DecidableEq (Slot → X)] (κ : SlotMeasure X)
    (F : (Slot → X) → ℝ) : κ F = ∑ w, lawDensity κ w * F w := by
  have hf : F = ∑ w, F w • (fun y => if y = w then (1 : ℝ) else 0) := by
    funext y
    simp [Finset.sum_apply]
  conv_lhs => rw [hf]
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

/-- **A positive record satisfies condition (b)** of `def:record:structured-energy`. -/
theorem selectedMarginalsUniform_lawDensity [DecidableEq X] [Nonempty X] {κ : SlotMeasure X}
    (h : IsPositiveRecord κ) : selectedMarginalsUniform (lawDensity κ) := by
  have hpos : ∀ z, 0 ≤ lawDensity κ z := fun z => h.1 _ fun y => by split_ifs <;> norm_num
  have htv : totalVariation (lawDensity κ) = mass κ := by
    unfold totalVariation mass
    rw [apply_eq_sum_lawDensity' κ (fun _ => 1)]
    exact sum_congr rfl fun z _ => by rw [abs_of_nonneg (hpos z), mul_one]
  intro v x
  rw [htv]
  have h1 := h.2 v (fun y => if y = x then (1 : ℝ) else 0)
  rw [apply_eq_sum_lawDensity' κ] at h1
  simp only [sum_ite_eq', mem_univ, ite_true] at h1
  rw [sum_filter]
  rw [show (mass κ / (Fintype.card X : ℝ)) = mass κ * (1 / Fintype.card X) by ring, ← h1]
  apply sum_congr rfl
  intro z _
  split_ifs <;> simp [abs_of_nonneg (hpos z)]

end General

/-- **Condition (b) is stable under products over atoms.** -/
theorem selectedMarginalsUniform_prod {I : Type*} [Fintype I] [DecidableEq I] {Y : I → Type*}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] (ρ : ∀ i, (Slot → Y i) → ℝ)
    (h : ∀ i, selectedMarginalsUniform (ρ i)) :
    selectedMarginalsUniform (fun z : Slot → ∀ i, Y i => ∏ i, ρ i (fun v => z v i)) := by
  set e : (Slot → ∀ i, Y i) ≃ (∀ i, Slot → Y i) := Equiv.piComm (fun (_ : Slot) (i : I) => Y i)
    with he
  have hsum : ∀ F : (Slot → ∀ i, Y i) → ℝ, ∑ z, F z = ∑ w, F (e.symm w) :=
    fun F => (Equiv.sum_comp e.symm F).symm
  have hprod : ∀ K : ∀ i, (Slot → Y i) → ℝ,
      ∑ w : ∀ i, Slot → Y i, ∏ i, K i (w i) = ∏ i, ∑ y, K i y := by
    intro K
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have htv : totalVariation (fun z : Slot → ∀ i, Y i => ∏ i, ρ i (fun v => z v i)) =
      ∏ i, totalVariation (ρ i) := by
    unfold totalVariation
    rw [hsum]
    simp_rw [Finset.abs_prod]
    exact hprod (fun i y => |ρ i y|)
  intro v x
  rw [htv, sum_filter, hsum]
  have hpt : ∀ w : ∀ i, Slot → Y i,
      (if e.symm w v = x then |∏ i, ρ i (fun v' => e.symm w v' i)| else 0) =
        ∏ i, (if w i v = x i then |ρ i (w i)| else 0) := by
    intro w
    rw [prod_ite_zero]
    have hiff : e.symm w v = x ↔ ∀ i ∈ (univ : Finset I), w i v = x i := by
      constructor
      · intro hx i _
        rw [← hx]
        rfl
      · intro hx
        funext i
        exact hx i (mem_univ i)
    by_cases hx : e.symm w v = x
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hx),
        ite_eq_left_of_eq_true _ _ (eq_true (hiff.mp hx)), Finset.abs_prod]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hx),
        ite_eq_right_of_eq_false _ _ (eq_false (fun h => hx (hiff.mpr h)))]
  simp_rw [hpt]
  rw [hprod (fun i y => if y v = x i then |ρ i y| else 0)]
  have hi : ∀ i, ∑ y : Slot → Y i, (if y v = x i then |ρ i y| else 0) =
      totalVariation (ρ i) / (Fintype.card (Y i) : ℝ) := by
    intro i
    rw [← h i v (x i), sum_filter]
  simp_rw [hi]
  rw [prod_div_distrib, Fintype.card_pi]
  push_cast
  rfl

section Data

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- The reserved records `Ñ_{0,𝔟} − μ_𝔟 = ∑_i κ^u_i` of (CP3) form a positive record. -/
theorem isPositiveRecord_recLaw (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) : IsPositiveRecord (recLaw D L b) :=
  isPositiveRecord_sum _ _ fun i _ => D.GB.κu_pos L b i

omit [DecidableEq P] in
/-- The left envelope increment `∑_i c_{L,i} κ_{L,i}` is a positive record. -/
theorem isPositiveRecord_envIncL (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) : IsPositiveRecord (TheoremCBlock.Structured.envIncL D L b) :=
  isPositiveRecord_sum _ _ fun i _ =>
    isPositiveRecord_smul (D.ME.κL_pos L b i) (D.ME.cL_nonneg L b i)

omit [DecidableEq P] in
/-- The right envelope increment `∑_i c_{R,i} κ_{R,i}` is a positive record. -/
theorem isPositiveRecord_envIncR (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) : IsPositiveRecord (TheoremCBlock.Structured.envIncR D L b) :=
  isPositiveRecord_sum _ _ fun i _ =>
    isPositiveRecord_smul (D.ME.κR_pos L b i) (D.ME.cR_nonneg L b i)

omit [DecidableEq P] in
/-- The wrapping increment `∑_t (π^s_t D^s_t + π^a_t D^a_t)` is a positive record (the
`D^ε_t` are probability laws with uniform one-slot marginals, `π ≥ 0`). -/
theorem isPositiveRecord_wrapInc (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) : IsPositiveRecord (TheoremCBlock.Structured.wrapInc D L b) :=
  isPositiveRecord_sum _ _ fun t _ => isPositiveRecord_add
    (isPositiveRecord_smul ⟨(D.CL.D_prob L b t _).1, D.CL.D_unif L b t _⟩
      (D.CL.πt_nonneg L b t _))
    (isPositiveRecord_smul ⟨(D.CL.D_prob L b t _).1, D.CL.D_unif L b t _⟩
      (D.CL.πt_nonneg L b t _))

omit [DecidableEq P] in
/-- **Condition (b) of `def:record:structured-energy` for every term of the bracket
expansion**, when the increments `Q_𝔟` are positive records (the reserved records are, by
`isPositiveRecord_recLaw`). This discharges the hypothesis `hsel` of `env_term_chain` and
`fix_term_chain`. -/
theorem hsel_of_positive (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (hQ : ∀ b, IsPositiveRecord (Qb b))
    (f g : BlockAtom Bk J L → Bool) :
    selectedMarginalsUniform (selectedWeight (termSet f g)
      (crtLaws blk h0 L (BracketEnergy.termLaw D L Qb f g))) := by
  unfold selectedWeight
  apply selectedMarginalsUniform_prod
    (fun b : {b // b ∈ termSet f g} => lawDensity (crtLaws blk h0 L
      (BracketEnergy.termLaw D L Qb f g) b.1))
  intro b
  apply selectedMarginalsUniform_lawDensity
  unfold crtLaws
  apply isPositiveRecord_pullLaw
  have hb := b.2
  unfold termSet at hb
  simp only [mem_filter, mem_univ, true_and] at hb
  unfold BracketEnergy.termLaw
  by_cases hf : f b.1 = true
  · simp only [hf, ↓reduceIte]
    exact hQ b.1
  · have hg : g b.1 = true := by
      rcases hb with h1 | h1
      · exact absurd h1 hf
      · exact h1
    simp only [hf, hg, Bool.false_eq_true, ↓reduceIte]
    exact isPositiveRecord_recLaw D L b.1

end Data

end Sarkozy.DensityChain
