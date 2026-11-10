module

public import Sarkozy.DensityFibre.FoldedChoice
public import Sarkozy.DensityFibre.HTermBound
public import Sarkozy.DensityChain.Records
public import Sarkozy.DensityChain.LargeProducts

@[expose] public section

/-!
# The folded laws are positive records (`lem:record:folded-energy`(b)); `hatom` at `ϑ = 1`

* `diagonalLaw_halfMarginalPlus_slot`, `diagonalLaw_halfMarginalMinus_slot`. This is
  **`lem:record:folded-energy`(b)** for one law: the one-slot marginal at `v` of the folded law
  `Diag(m_±(K))` is the marginal of `K` at the slot `φ_±(v)` that the fold copies.
* `isPositiveRecord_diag_plus`, `_minus`: the folded laws of a positive record are positive
  records.
* `isPositiveRecord_fullFold_plus`, `_minus`: the full folded law `κ(1) ∑_s π_s Diag(m_±(κ_s))`
  of a sharp decomposition of a positive record `κ = κ(1) ∑_s π_s κ_s` is a positive record. The
  components `κ_s` need not have uniform marginals; their mixture has.
* **`bpieceLp_positiveRecord`**, **`bpieceLm_positiveRecord`**: every non-`μ` folded piece of the
  baseline route (`DensityFibre.FoldedChoice`) is a positive record, for positive-record
  increments `Q`. DC1's `isPositiveRecord_envIncL/R`, `_wrapInc` cover the data's increments.
* **`mixedLp_one_of_positiveRecord`**: at `θ = 1`, the moment input `hatom` of the
  revealed-input chain (unit mixed `L^{72/θ}` of the variation law) holds for every positive
  record. It follows from uniform one-slot marginals, through DC1's
  `hasUniformMarginals_variationLaw` and `selectedMarginalsUniform_lawDensity`, and
  `mixedLpBound_of_uniform_marginals`.

So at `ϑ = 1` the inputs `hatom` of `env_fold_le_chain` and `fix_fold_le_chain` are proved for
the folded terms (`hatom_fold_one`). With DC1's `selectedMarginalsUniform_prod`, so is
condition (b) of `def:record:structured-energy` for the folded selected measures.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.DensityFibre

open Sarkozy.BracketEnergy
open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper Sarkozy.EnvelopeInputsBlock
open Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.TheoremC Sarkozy.Structured Sarkozy.Comparison ReflectionCut

section Marginals

variable {X : Type} [Fintype X] [DecidableEq X] (c : ReflectionCut Slot)

/-- The plus-half slot read at `v` by the plus fold. -/
def foldHalf (v : Slot) : c.Half :=
  if hv : v ∈ c.half then ⟨v, hv⟩ else ⟨c.flip v, (c.crosses v).mpr hv⟩

theorem foldHalf_val (v : Slot) : (foldHalf c v).1 = c.foldPlus v := by
  unfold foldHalf foldPlus
  split_ifs <;> rfl

omit [Fintype X] [DecidableEq X] in
theorem join_self_apply (x : c.Half → X) (v : Slot) : c.join x x v = x (foldHalf c v) := by
  unfold join foldHalf
  split_ifs <;> rfl

/-- **`lem:record:folded-energy`(b), plus fold**: the one-slot marginal of `Diag(m₊(K))` at `v` is
the marginal of `K` at `φ₊(v)`. -/
theorem diagonalLaw_halfMarginalPlus_slot (K : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ) (g : X → ℝ)
    (v : Slot) :
    c.diagonalLaw (halfMarginalPlus c K) (fun z => g (z v)) =
      K (fun z => g (z (c.foldPlus v))) := by
  change ∑ x, halfMarginalPlus c K x * g (c.join x x v) = _
  simp only [join_self_apply]
  have hfun : (fun z : Slot → X => g (z (c.foldPlus v))) =
      ∑ x : c.Half → X, g (x (foldHalf c v)) •
        (fun z : Slot → X => if (fun u : c.Half => z u.1) = x then (1 : ℝ) else 0) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [foldHalf_val]
  rw [hfun, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

/-- **`lem:record:folded-energy`(b), minus fold**: the one-slot marginal of `Diag(m₋(K))` at `v`
is the marginal of `K` at the mirror slot `ι φ₊(v)`. -/
theorem diagonalLaw_halfMarginalMinus_slot (K : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ) (g : X → ℝ)
    (v : Slot) :
    c.diagonalLaw (halfMarginalMinus c K) (fun z => g (z v)) =
      K (fun z => g (z (c.flip (c.foldPlus v)))) := by
  change ∑ x, halfMarginalMinus c K x * g (c.join x x v) = _
  simp only [join_self_apply]
  have hfun : (fun z : Slot → X => g (z (c.flip (c.foldPlus v)))) =
      ∑ x : c.Half → X, g (x (foldHalf c v)) •
        (fun z : Slot → X => if (fun u : c.Half => z (c.flip u.1)) = x then (1 : ℝ) else 0) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [foldHalf_val]
  rw [hfun, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

omit [DecidableEq X] in
theorem diagonalLaw_nonneg {m : (c.Half → X) → ℝ} (hm : ∀ x, 0 ≤ m x) :
    IsNonneg (c.diagonalLaw m) := by
  intro f hf
  change 0 ≤ ∑ x, m x * f (c.join x x)
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hm x) (hf _)

/-- The plus folded law of a positive record is a positive record. -/
theorem isPositiveRecord_diag_plus {κ : SlotMeasure X} (hκ : IsPositiveRecord κ) :
    IsPositiveRecord (c.diagonalLaw (halfMarginalPlus c κ)) := by
  refine ⟨diagonalLaw_nonneg c (halfMarginalPlus_nonneg c hκ.1), fun v g => ?_⟩
  have hmass : mass (c.diagonalLaw (halfMarginalPlus c κ)) = mass κ := by
    have h := diagonalLaw_halfMarginalPlus_slot c κ (fun _ => (1 : ℝ)) v
    exact h
  rw [diagonalLaw_halfMarginalPlus_slot, hκ.2, hmass]

/-- The minus folded law of a positive record is a positive record. -/
theorem isPositiveRecord_diag_minus {κ : SlotMeasure X} (hκ : IsPositiveRecord κ) :
    IsPositiveRecord (c.diagonalLaw (halfMarginalMinus c κ)) := by
  refine ⟨diagonalLaw_nonneg c (halfMarginalMinus_nonneg c hκ.1), fun v g => ?_⟩
  have hmass : mass (c.diagonalLaw (halfMarginalMinus c κ)) = mass κ := by
    have h := diagonalLaw_halfMarginalMinus_slot c κ (fun _ => (1 : ℝ)) v
    exact h
  rw [diagonalLaw_halfMarginalMinus_slot, hκ.2, hmass]

/-- **The full plus folded law of a sharp decomposition is a positive record**: for
`κ = κ(1) ∑_s π_s κ_s` with probability components and `κ` a positive record,
`κ(1) ∑_s π_s Diag(m₊(κ_s))` is a positive record. -/
theorem isPositiveRecord_fullFold_plus {S : Type} [Fintype S] {κ : SlotMeasure X}
    (hκ : IsPositiveRecord κ) (π : FiniteLaw S) (κs : S → SlotMeasure X)
    (hprob : ∀ s, IsProbability (κs s)) (hdec : κ = mass κ • ∑ s, π.weight s • κs s) :
    IsPositiveRecord (mass κ • ∑ s, π.weight s •
      c.diagonalLaw (halfMarginalPlus c (κs s))) := by
  have hm0 : 0 ≤ mass κ := TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg hκ.1
  have hslot : ∀ (g : X → ℝ) (v : Slot),
      (mass κ • ∑ s, π.weight s • c.diagonalLaw (halfMarginalPlus c (κs s)))
        (fun z => g (z v)) = κ (fun z => g (z (c.foldPlus v))) := by
    intro g v
    conv_rhs => rw [hdec]
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, diagonalLaw_halfMarginalPlus_slot]
  refine ⟨fun f hf => ?_, fun v g => ?_⟩
  · simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
    exact mul_nonneg hm0 (Finset.sum_nonneg fun s _ => mul_nonneg (π.nonneg s)
      (diagonalLaw_nonneg c (halfMarginalPlus_nonneg c (hprob s).1) f hf))
  · have hmass : mass (mass κ • ∑ s, π.weight s • c.diagonalLaw (halfMarginalPlus c (κs s))) =
        mass κ := hslot (fun _ => 1) v
    rw [hslot, hκ.2, hmass]

/-- The full minus folded law of a sharp decomposition is a positive record. -/
theorem isPositiveRecord_fullFold_minus {S : Type} [Fintype S] {κ : SlotMeasure X}
    (hκ : IsPositiveRecord κ) (π : FiniteLaw S) (κs : S → SlotMeasure X)
    (hprob : ∀ s, IsProbability (κs s)) (hdec : κ = mass κ • ∑ s, π.weight s • κs s) :
    IsPositiveRecord (mass κ • ∑ s, π.weight s •
      c.diagonalLaw (halfMarginalMinus c (κs s))) := by
  have hm0 : 0 ≤ mass κ := TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg hκ.1
  have hslot : ∀ (g : X → ℝ) (v : Slot),
      (mass κ • ∑ s, π.weight s • c.diagonalLaw (halfMarginalMinus c (κs s)))
        (fun z => g (z v)) = κ (fun z => g (z (c.flip (c.foldPlus v)))) := by
    intro g v
    conv_rhs => rw [hdec]
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, diagonalLaw_halfMarginalMinus_slot]
  refine ⟨fun f hf => ?_, fun v g => ?_⟩
  · simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
    exact mul_nonneg hm0 (Finset.sum_nonneg fun s _ => mul_nonneg (π.nonneg s)
      (diagonalLaw_nonneg c (halfMarginalMinus_nonneg c (hprob s).1) f hf))
  · have hmass : mass (mass κ • ∑ s, π.weight s • c.diagonalLaw (halfMarginalMinus c (κs s))) =
        mass κ := hslot (fun _ => 1) v
    rw [hslot, hκ.2, hmass]

variable [Nonempty X]

/-- **`hatom` at `θ = 1` for a positive record**: the variation law of a positive record has unit
mixed `L^{72}` (Hölder with uniform one-slot marginals). -/
theorem mixedLp_one_of_positiveRecord {κ : SlotMeasure X} (hκ : IsPositiveRecord κ)
    (hb : 0 < totalVariation (lawDensity κ)) :
    MixedLpBound (variationLaw (lawDensity κ) hb) (72 / 1) 1 := by
  have hu := Sarkozy.DensityChain.hasUniformMarginals_variationLaw (lawDensity κ) hb
    (Sarkozy.DensityChain.selectedMarginalsUniform_lawDensity hκ)
  have hm := mixedLpBound_of_uniform_marginals _ hu
  rw [card_slot] at hm
  norm_num
  exact_mod_cast hm

end Marginals

section Pieces

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
  (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (dec : DecFamily D L)

omit [DecidableEq P] in
/-- **Every non-`μ` plus folded piece of the baseline route is a positive record**, for
positive-record increments `Q`. -/
theorem bpieceLp_positiveRecord (hQ : ∀ b, IsPositiveRecord (Qb b)) (j : D.FS.Tag)
    (b : BlockAtom Bk J L) (x : HPiece D L b) (hx : hpieceIsMu D L b x = false) :
    IsPositiveRecord (bpieceLp D L Qb dec j b x) := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · simp [hpieceIsMu] at hx
  · exact isPositiveRecord_diag_plus _ (D.GB.κu_pos L b k)
  · exact isPositiveRecord_fullFold_plus _ (D.FS.κ_pos L b i) (dec b i).π (dec b i).κs
      (dec b i).prob (dec b i).hκ
  · cases t
    · exact isPositiveRecord_diag_plus _ (D.FS.κ_pos L b i)
    · exact isPositiveRecord_diag_plus _ (D.FS.κ'_pos L b i)
  · exact isPositiveRecord_diag_plus _ (hQ b)

omit [DecidableEq P] in
/-- **Every non-`μ` minus folded piece of the baseline route is a positive record.** -/
theorem bpieceLm_positiveRecord (hQ : ∀ b, IsPositiveRecord (Qb b)) (j : D.FS.Tag)
    (b : BlockAtom Bk J L) (x : HPiece D L b) (hx : hpieceIsMu D L b x = false) :
    IsPositiveRecord (bpieceLm D L Qb dec j b x) := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · simp [hpieceIsMu] at hx
  · exact isPositiveRecord_diag_minus _ (D.GB.κu_pos L b k)
  · exact isPositiveRecord_fullFold_minus _ (D.FS.κ_pos L b i) (dec b i).π (dec b i).κs
      (dec b i).prob (dec b i).hκ
  · cases t
    · exact isPositiveRecord_diag_minus _ (D.FS.κ_pos L b i)
    · exact isPositiveRecord_diag_minus _ (D.FS.κ'_pos L b i)
  · exact isPositiveRecord_diag_minus _ (hQ b)

omit [DecidableEq P] in
/-- **`hatom` of the folded terms at `θ = 1`** (the input of `env_fold_le_chain`,
`fix_fold_le_chain` at `θ = 1`): at every term atom (non-`μ` piece), the variation law of the
plus folded law has unit mixed `L^{72}`. -/
theorem hatom_fold_one (hQ : ∀ b, IsPositiveRecord (Qb b)) (j : D.FS.Tag)
    (φ : ∀ b, HPiece D L b) :
    ∀ b ∈ hTermAtoms D L φ, ∀ hb : 0 < totalVariation (lawDensity (bpieceLp D L Qb dec j b (φ b))),
      MixedLpBound (variationLaw _ hb) (72 / 1) 1 := by
  intro b hb hb'
  have hx : hpieceIsMu D L b (φ b) = false := (Finset.mem_filter.mp hb).2
  exact mixedLp_one_of_positiveRecord (bpieceLp_positiveRecord D L Qb dec hQ j b (φ b) hx) hb'

end Pieces

end Sarkozy.DensityFibre
