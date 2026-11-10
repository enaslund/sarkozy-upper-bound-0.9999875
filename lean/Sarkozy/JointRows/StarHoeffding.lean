module

public import Sarkozy.FiveType.JointBlocks

/-!
# The Hoeffding decomposition of a product law (`prop:conditional-star`, Step 1)

Source: `paper/sections/16_extraction.tex`, proof of `prop:conditional-star`, Step 1: "The
product law gives the orthogonal decomposition `L²(ν_X) = ⊕_{R⊆X} H_R`, where `H_R` consists of
the functions of `x_R` whose conditional mean in every coordinate of `R` vanishes; `U_i` maps
into `H_{{i}}` and `W_S` into `H_S`. ... As the ranges are orthogonal, ..."

For the product law `ν = ⊗_i ν_i` (`Blocks.blockLaw`) on `∏_i X_i`:
* `expect_condMean`: integrating out one coordinate preserves the expectation,
  `E_ν[E_i h] = E_ν[h]` with `(E_i h)(x) = ∑_t ν_i(t) h(x[i ↦ t])`;
* `ExactSupport R f`: `f` depends only on `x_R` and has conditional mean zero in each coordinate
  of `R` (the space `H_R`);
* `hoeffding_orthogonal`: **functions with different exact supports are orthogonal**,
  `E_ν[f g] = 0` for `f ∈ H_R`, `g ∈ H_{R'}`, `R ≠ R'`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.Star

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Xp : ι → Type*} [∀ i, Fintype (Xp i)]
  [∀ i, DecidableEq (Xp i)]

/-- The conditional mean in the coordinate `i`: `(E_i h)(x) = ∑_t ν_i(t) h(x[i ↦ t])`. -/
noncomputable def condMean (νp : ∀ i, FiniteLaw (Xp i)) (i : ι) (h : ((j : ι) → Xp j) → ℝ)
    (x : (j : ι) → Xp j) : ℝ :=
  ∑ t, (νp i).weight t * h (Function.update x i t)

/-- The fibre of the coordinate `i` at `t`, and the splitting `x ↦ (x_i, x[i ↦ t])`. -/
def splitAt (i : ι) (t : Xp i) : ((j : ι) → Xp j) ≃ Xp i × {y : (j : ι) → Xp j // y i = t} where
  toFun x := (x i, ⟨Function.update x i t, by simp⟩)
  invFun p := Function.update p.2.1 i p.1
  left_inv x := by simp
  right_inv p := by
    obtain ⟨s, y, hy⟩ := p
    simp only [Function.update_self, Prod.mk.injEq, true_and]
    apply Subtype.ext
    simp only [Function.update_idem]
    rw [← hy, Function.update_eq_self]

omit [∀ i, DecidableEq (Xp i)] in
theorem blockWeight_update (νp : ∀ i, FiniteLaw (Xp i)) (x : (j : ι) → Xp j) (i : ι) (t : Xp i) :
    (blockLaw νp).weight (Function.update x i t) * (νp i).weight (x i) =
      (blockLaw νp).weight x * (νp i).weight t := by
  simp only [blockLaw]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => (νp j).weight (x j)) (Finset.mem_univ i)]
  have hrest : ∏ j ∈ Finset.univ.erase i, (νp j).weight (Function.update x i t j) =
      ∏ j ∈ Finset.univ.erase i, (νp j).weight (x j) :=
    Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hrest, Function.update_self]
  ring

/-- **Integrating out one coordinate preserves the expectation.** -/
theorem expect_condMean (νp : ∀ i, FiniteLaw (Xp i)) (i : ι) (h : ((j : ι) → Xp j) → ℝ) :
    (blockLaw νp).expect (condMean νp i h) = (blockLaw νp).expect h := by
  unfold condMean FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- for fixed `t`, split `x ↦ (x_i, x[i ↦ t])`
  have key : ∀ t : Xp i,
      ∑ x, (blockLaw νp).weight x * ((νp i).weight t * h (Function.update x i t)) =
      ∑ y : {y : (j : ι) → Xp j // y i = t}, (blockLaw νp).weight y.1 * h y.1 := by
    intro t
    rw [← Fintype.sum_equiv (splitAt i t).symm
      (fun p => (blockLaw νp).weight (Function.update p.2.1 i p.1) *
        ((νp i).weight t * h (Function.update (Function.update p.2.1 i p.1) i t))) _
      (fun _ => rfl), Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hy : Function.update y.1 i t = y.1 := Function.update_eq_self_iff.mpr y.2.symm
    have hw : ∀ s, (blockLaw νp).weight (Function.update y.1 i s) * (νp i).weight t =
        (blockLaw νp).weight y.1 * (νp i).weight s := fun s => by
      have := blockWeight_update νp (Function.update y.1 i s) i t
      rw [Function.update_idem, hy, Function.update_self] at this
      rw [this]
    calc ∑ s, (blockLaw νp).weight (Function.update y.1 i s) *
          ((νp i).weight t * h (Function.update (Function.update y.1 i s) i t))
        = ∑ s, (blockLaw νp).weight y.1 * (νp i).weight s * h y.1 := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Function.update_idem, hy, ← mul_assoc, hw s]
      _ = (blockLaw νp).weight y.1 * h y.1 := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, (νp i).total, mul_one]
  simp_rw [key]
  -- reassemble the fibres
  rw [← Fintype.sum_equiv (Equiv.sigmaFiberEquiv (fun x : (j : ι) → Xp j => x i))
    (fun p => (blockLaw νp).weight p.2.1 * h p.2.1) _ (fun _ => rfl), Fintype.sum_sigma]

/-- **`H_R`**: `f` depends only on `x_R` and has conditional mean zero in each coordinate of `R`. -/
structure ExactSupport (νp : ∀ i, FiniteLaw (Xp i)) (R : Finset ι) (f : ((j : ι) → Xp j) → ℝ) :
    Prop where
  depends : ∀ x x' : (j : ι) → Xp j, (∀ j ∈ R, x j = x' j) → f x = f x'
  centred : ∀ i ∈ R, ∀ x, condMean νp i f x = 0

/-- **The Hoeffding components are orthogonal**: `E_ν[f g] = 0` for `f ∈ H_R`, `g ∈ H_{R'}`,
`R ≠ R'`. -/
theorem hoeffding_orthogonal (νp : ∀ i, FiniteLaw (Xp i)) {R R' : Finset ι} (hRR : R ≠ R')
    {f g : ((j : ι) → Xp j) → ℝ} (hf : ExactSupport νp R f) (hg : ExactSupport νp R' g) :
    (blockLaw νp).expect (fun x => f x * g x) = 0 := by
  -- a coordinate in one support and not the other
  have key : ∀ {R R' : Finset ι} {f g : ((j : ι) → Xp j) → ℝ}, ExactSupport νp R f →
      ExactSupport νp R' g → ∀ i ∈ R, i ∉ R' →
      (blockLaw νp).expect (fun x => f x * g x) = 0 := by
    intro R R' f g hf hg i hi hi'
    rw [← expect_condMean νp i]
    have : ∀ x, condMean νp i (fun x => f x * g x) x = 0 := fun x => by
      unfold condMean
      have hgx : ∀ t, g (Function.update x i t) = g x := fun t =>
        hg.depends _ _ fun j hj => by
          rw [Function.update_of_ne (by rintro rfl; exact hi' hj)]
      simp_rw [hgx, ← mul_assoc, ← Finset.sum_mul]
      have := hf.centred i hi x
      unfold condMean at this
      rw [this, zero_mul]
    rw [show condMean νp i (fun x => f x * g x) = fun _ => 0 from funext this,
      FiniteLaw.expect_const]
  by_cases h : ∃ i ∈ R, i ∉ R'
  · obtain ⟨i, hi, hi'⟩ := h
    exact key hf hg i hi hi'
  · push Not at h
    have hsub : R ⊆ R' := fun i hi => h i hi
    obtain ⟨i, hi', hi⟩ : ∃ i ∈ R', i ∉ R := by
      by_contra hc
      push Not at hc
      exact hRR (Finset.Subset.antisymm hsub fun i hi => hc i hi)
    have := key hg hf i hi' hi
    rw [← this]
    exact (blockLaw νp).expect_congr fun x => mul_comm _ _

end Sarkozy.JointRows.Star
