module

public import Sarkozy.Moments.Mixed
public import Sarkozy.ProbabilityProducts

/-!
# Tensorization of mixed `Lᵖ` bounds over finitely many atoms

The reference law is a product over atoms (`def:record:functional`(d)), and the proof of
`lem:density:global-moment` tensorizes mixed `L³⁶` bounds over all atoms ("tensorizing
with the unit tail"). For laws `μ_j` on labellings `V → X_j` with mixed `Lᵖ` constants
`C_j`, the tensor law (`Sarkozy.FiniteLaw.tensor`) on `V → ∀ j, X_j` has constant
`∏_j C_j`. The two-factor case is `Sarkozy.MixedLpBound.slotProduct`.

The proof integrates out one atom at a time. A *partial expectation* over a set `s` of
atoms freezes the coordinates outside `s` (by indicators, so that no subtypes or
re-indexing are needed); integrating one more atom is a finite Fubini identity.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

namespace PartialExpectation

variable {J : Type*} [Fintype J] [DecidableEq J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]
  [∀ j, DecidableEq (Ω j)]

/-- Integrate the coordinates in `s` against the weights `w`, freezing the others at `y`. -/
noncomputable def pe (w : ∀ j, Ω j → ℝ) (s : Finset J) (F : (∀ j, Ω j) → ℝ)
    (y : ∀ j, Ω j) : ℝ :=
  ∑ z : ∀ j, Ω j, ((∏ j ∈ s, w j (z j)) *
    ∏ j ∈ Finset.univ \ s, (if z j = y j then (1 : ℝ) else 0)) * F z

theorem pe_univ (w : ∀ j, Ω j → ℝ) (F : (∀ j, Ω j) → ℝ) (y : ∀ j, Ω j) :
    pe w Finset.univ F y = ∑ z : ∀ j, Ω j, (∏ j, w j (z j)) * F z := by
  unfold pe
  simp

theorem pe_empty (w : ∀ j, Ω j → ℝ) (F : (∀ j, Ω j) → ℝ) (y : ∀ j, Ω j) :
    pe w ∅ F y = F y := by
  unfold pe
  simp only [Finset.prod_empty, one_mul, Finset.sdiff_empty]
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    have hne : ∃ j, z j ≠ y j := by
      by_contra h
      push Not at h
      exact hz (funext h)
    obtain ⟨j, hj⟩ := hne
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ y) h

/-- Integrating one more atom. -/
theorem pe_insert (w : ∀ j, Ω j → ℝ) {a : J} {s : Finset J} (ha : a ∉ s)
    (F : (∀ j, Ω j) → ℝ) (y : ∀ j, Ω j) :
    pe w (insert a s) F y = ∑ x : Ω a, w a x * pe w s F (Function.update y a x) := by
  unfold pe
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  have has : a ∈ Finset.univ \ s := Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩
  have hsd : Finset.univ \ insert a s = (Finset.univ \ s).erase a := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_erase, not_or]
  -- Split off the factor at `a` in the frozen product.
  have hsplit (x : Ω a) : ∏ j ∈ Finset.univ \ s,
      (if z j = Function.update y a x j then (1 : ℝ) else 0) =
      (if z a = x then 1 else 0) *
        ∏ j ∈ Finset.univ \ insert a s, (if z j = y j then (1 : ℝ) else 0) := by
    rw [← Finset.mul_prod_erase _ _ has, hsd]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun j hj => ?_
      have hja : j ≠ a := (Finset.mem_erase.mp hj).1
      rw [Function.update_of_ne hja]
  simp_rw [hsplit]
  rw [Finset.sum_eq_single (z a)]
  · rw [Finset.prod_insert ha]
    simp only [↓reduceIte]
    ring
  · intro x _ hx
    have : z a ≠ x := fun h => hx h.symm
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem pe_nonneg (w : ∀ j, Ω j → ℝ) (hw : ∀ j x, 0 ≤ w j x) (s : Finset J)
    {F : (∀ j, Ω j) → ℝ} (hF : ∀ z, 0 ≤ F z) (y : ∀ j, Ω j) : 0 ≤ pe w s F y := by
  unfold pe
  refine Finset.sum_nonneg fun z _ => mul_nonneg (mul_nonneg ?_ ?_) (hF z)
  · exact Finset.prod_nonneg fun j _ => hw j _
  · exact Finset.prod_nonneg fun j _ => by split_ifs <;> norm_num

end PartialExpectation

open PartialExpectation

section Norms

variable {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)]
  [∀ j, DecidableEq (X j)]

/-- The uniform weights of each atom alphabet. -/
noncomputable def uniformWeights (X : J → Type*) [∀ j, Fintype (X j)] : ∀ j, X j → ℝ :=
  fun j _ => (Fintype.card (X j) : ℝ)⁻¹

/-- The `Lᵖ` norm in the coordinates of `s`, the others frozen at `x`. -/
noncomputable def partialNorm (p : ℝ) (s : Finset J) (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) : ℝ :=
  pe (uniformWeights X) s (fun z => |f z| ^ p) x ^ (1 / p)

theorem partialMoment_nonneg (p : ℝ) (s : Finset J) (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    0 ≤ pe (uniformWeights X) s (fun z => |f z| ^ p) x :=
  pe_nonneg _ (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) s
    (fun _ => Real.rpow_nonneg (abs_nonneg _) _) x

theorem partialNorm_nonneg (p : ℝ) (s : Finset J) (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    0 ≤ partialNorm p s f x :=
  Real.rpow_nonneg (partialMoment_nonneg p s f x) _

theorem partialNorm_empty {p : ℝ} (hp : 0 < p) (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    partialNorm p ∅ f x = |f x| := by
  unfold partialNorm
  rw [pe_empty, ← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem partialNorm_univ [∀ j, Nonempty (X j)] {p : ℝ} (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    partialNorm p Finset.univ f x = (FiniteLaw.uniform (∀ j, X j)).lpNorm p f := by
  unfold partialNorm FiniteLaw.lpNorm FiniteLaw.moment
  rw [pe_univ, FiniteLaw.expect_uniform]
  congr 1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [uniformWeights]
  rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib, div_eq_mul_inv, mul_comm]

theorem partialNorm_insert [∀ j, Nonempty (X j)] {p : ℝ} (hp : 0 < p) {a : J} {s : Finset J} (ha : a ∉ s)
    (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    partialNorm p (insert a s) f x =
      (FiniteLaw.uniform (X a)).lpNorm p (fun ξ => partialNorm p s f (Function.update x a ξ)) := by
  unfold FiniteLaw.lpNorm FiniteLaw.moment
  conv_lhs => unfold partialNorm
  rw [pe_insert _ ha, FiniteLaw.expect_uniform]
  congr 1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [abs_of_nonneg (partialNorm_nonneg p s f _)]
  unfold partialNorm
  rw [← Real.rpow_mul (partialMoment_nonneg p s f _), one_div_mul_cancel hp.ne', Real.rpow_one]
  simp only [uniformWeights]
  field_simp

end Norms

variable {V : Type*} [Fintype V] [DecidableEq V]
  {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)]
  [∀ j, DecidableEq (X j)] [∀ j, Nonempty (X j)]

omit [Fintype V] [DecidableEq V] [Fintype J] [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
  [∀ j, Nonempty (X j)] in
theorem update_transpose (y : ∀ j, V → X j) (a : J) (x : V → X a) (v : V) :
    (fun j => Function.update y a x j v) = Function.update (fun j => y j v) a (x v) := by
  funext j
  by_cases hj : j = a
  · subst hj
    simp
  · simp [Function.update_of_ne hj]

/-- **The tensorized mixed bound over a set of atoms**, by induction on the set. -/
theorem pe_mixed_bound (μ : ∀ j, FiniteLaw (V → X j)) {p : ℝ} (hp : 0 < p) (C : J → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hμ : ∀ j, MixedLpBound (μ j) p (C j)) (s : Finset J) :
    ∀ (y : ∀ j, V → X j) (f : V → (∀ j, X j) → ℝ),
      |pe (fun j => (μ j).weight) s (fun z => ∏ v, f v (fun j => z j v)) y| ≤
        (∏ j ∈ s, C j) * ∏ v, partialNorm p s (f v) (fun j => y j v) := by
  induction s using Finset.induction_on with
  | empty =>
    intro y f
    rw [pe_empty, Finset.prod_empty, one_mul, Finset.abs_prod]
    exact le_of_eq (Finset.prod_congr rfl fun v _ => (partialNorm_empty hp (f v) _).symm)
  | @insert a s ha ih =>
    intro y f
    rw [pe_insert _ ha]
    set g : V → X a → ℝ := fun v ξ =>
      partialNorm p s (f v) (Function.update (fun j => y j v) a ξ) with hg
    have hstep (x : V → X a) :
        |pe (fun j => (μ j).weight) s (fun z => ∏ v, f v (fun j => z j v))
          (Function.update y a x)| ≤ (∏ j ∈ s, C j) * ∏ v, g v (x v) := by
      refine (ih (Function.update y a x) f).trans_eq ?_
      congr 1
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [hg]
      simp only
      rw [update_transpose]
    have hg0 (x : V → X a) : 0 ≤ ∏ v, g v (x v) :=
      Finset.prod_nonneg fun v _ => partialNorm_nonneg p s (f v) _
    calc |∑ x : V → X a, (μ a).weight x *
          pe (fun j => (μ j).weight) s (fun z => ∏ v, f v (fun j => z j v)) (Function.update y a x)|
        ≤ ∑ x : V → X a, (μ a).weight x * ((∏ j ∈ s, C j) * ∏ v, g v (x v)) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
          rw [abs_mul, abs_of_nonneg ((μ a).nonneg x)]
          exact mul_le_mul_of_nonneg_left (hstep x) ((μ a).nonneg x)
      _ = (∏ j ∈ s, C j) * (μ a).expect (fun x => ∏ v, g v (x v)) := by
          unfold FiniteLaw.expect
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
      _ ≤ (∏ j ∈ s, C j) * (C a * ∏ v, (FiniteLaw.uniform (X a)).lpNorm p (g v)) := by
          apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun j _ => hC j)
          have h := hμ a g
          rwa [abs_of_nonneg ((μ a).expect_nonneg hg0)] at h
      _ = (∏ j ∈ insert a s, C j) *
            ∏ v, partialNorm p (insert a s) (f v) (fun j => y j v) := by
          rw [Finset.prod_insert ha]
          have hnorm : ∀ v, (FiniteLaw.uniform (X a)).lpNorm p (g v) =
              partialNorm p (insert a s) (f v) (fun j => y j v) := by
            intro v
            rw [partialNorm_insert hp ha]
          simp only [hnorm]
          ring

/-- **Tensorization of mixed `Lᵖ` bounds.** -/
theorem MixedLpBound.tensor (μ : ∀ j, FiniteLaw (V → X j)) {p : ℝ} (hp : 0 < p) (C : J → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hμ : ∀ j, MixedLpBound (μ j) p (C j)) :
    MixedLpBound (FiniteLaw.tensor μ) p (∏ j, C j) := by
  intro f
  have hexp : (FiniteLaw.tensor μ).expect (fun z => ∏ v, f v (z v)) =
      pe (fun j => (μ j).weight) Finset.univ (fun z => ∏ v, f v (fun j => z j v))
        (fun j _ => Classical.choice inferInstance) := by
    rw [pe_univ, FiniteLaw.expect_eq_signedIntegral, FiniteLaw.signedIntegral_tensor]
    unfold tensorLaw
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [lawDensity, signedIntegral]
  rw [hexp]
  refine (pe_mixed_bound μ hp C hC hμ Finset.univ _ f).trans_eq ?_
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  exact partialNorm_univ (f v) _

end Sarkozy
