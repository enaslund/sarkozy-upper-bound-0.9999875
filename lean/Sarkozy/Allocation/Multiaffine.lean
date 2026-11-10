module

public import Sarkozy.Parameters
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Finset.Powerset

/-!
# Multiaffine functions on a box

A function affine in each coordinate is a convex combination of its endpoint
values in that coordinate. Iterating this fact reduces nonnegativity on a
finite box to its vertices. This supplies the reduction used for the joint
mean allocation constants in Section 24a.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Allocation

variable {ι : Type*} [DecidableEq ι]

def MultiAffine (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ i z a b t, f (Function.update z i ((1 - t) * a + t * b)) =
    (1 - t) * f (Function.update z i a) + t * f (Function.update z i b)

theorem MultiAffine.const (c : ℝ) : MultiAffine (fun _ : ι → ℝ => c) := by
  intro i z a b t
  ring

theorem MultiAffine.add {f g : (ι → ℝ) → ℝ} (hf : MultiAffine f) (hg : MultiAffine g) :
    MultiAffine (fun z => f z + g z) := by
  intro i z a b t
  dsimp only
  rw [hf, hg]
  ring

theorem MultiAffine.sub {f g : (ι → ℝ) → ℝ} (hf : MultiAffine f) (hg : MultiAffine g) :
    MultiAffine (fun z => f z - g z) := by
  intro i z a b t
  dsimp only
  rw [hf, hg]
  ring

theorem MultiAffine.const_mul {f : (ι → ℝ) → ℝ} (hf : MultiAffine f) (c : ℝ) :
    MultiAffine (fun z => c * f z) := by
  intro i z a b t
  dsimp only
  rw [hf]
  ring

theorem MultiAffine.sum {J : Type*} (s : Finset J) {f : J → (ι → ℝ) → ℝ}
    (hf : ∀ j ∈ s, MultiAffine (f j)) : MultiAffine (fun z => ∑ j ∈ s, f j z) := by
  intro i z a b t
  dsimp only
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j hj => hf j hj i z a b t)

theorem MultiAffine.monomial (s : Finset ι) : MultiAffine (fun z => ∏ i ∈ s, z i) := by
  intro i z a b t
  by_cases hi : i ∈ s
  · simp only [Finset.prod_update_of_mem hi]
    ring
  · simp only [Finset.prod_update_of_notMem hi]
    ring

theorem MultiAffine.translate {f : (ι → ℝ) → ℝ} (hf : MultiAffine f) (c : ι → ℝ) :
    MultiAffine (fun z => f (fun i => z i + c i)) := by
  intro i z a b t
  have he (q : ℝ) : (fun j => Function.update z i q j + c j) =
      Function.update (fun j => z j + c j) i (q + c i) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  simp only [he]
  rw [show (1 - t) * a + t * b + c i = (1 - t) * (a + c i) + t * (b + c i) by ring]
  exact hf i _ _ _ t

/-- An affine function of finitely many independent coordinates is nonnegative
on a box if it is nonnegative at every vertex. Degenerate boxes are included. -/
theorem MultiAffine.nonneg_of_vertices [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hf : MultiAffine f) {l u : ℝ} (hlu : l ≤ u)
    (hv : ∀ z : ι → ℝ, (∀ i, z i = l ∨ z i = u) → 0 ≤ f z)
    {z : ι → ℝ} (hz : ∀ i, l ≤ z i ∧ z i ≤ u) : 0 ≤ f z := by
  by_cases heq : l = u
  · apply hv z
    intro i
    exact Or.inl (le_antisymm ((hz i).2.trans_eq heq.symm) (hz i).1)
  have hwidth : 0 < u - l := sub_pos.mpr (lt_of_le_of_ne hlu heq)
  have hgen (s : Finset ι) : ∀ z : ι → ℝ,
      (∀ i ∈ s, l ≤ z i ∧ z i ≤ u) →
      (∀ i ∉ s, z i = l ∨ z i = u) → 0 ≤ f z := by
    induction s using Finset.induction_on with
    | empty =>
      intro z _ hb
      exact hv z (fun i => hb i (by simp))
    | @insert i s hi ih =>
      intro z hinside houtside
      have hendpoint (a : ℝ) (ha : a = l ∨ a = u) : 0 ≤ f (Function.update z i a) := by
        apply ih
        · intro j hj
          have hji : j ≠ i := by intro h; subst j; exact hi hj
          simpa only [Function.update_of_ne hji] using hinside j (Finset.mem_insert_of_mem hj)
        · intro j hj
          by_cases hji : j = i
          · subst j
            simpa using ha
          · rw [Function.update_of_ne hji]
            exact houtside j (by simp [hji, hj])
      have hlow := hendpoint l (Or.inl rfl)
      have hupp := hendpoint u (Or.inr rfl)
      let t : ℝ := (z i - l) / (u - l)
      have hit := hinside i (Finset.mem_insert_self _ _)
      have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hit.1) hwidth.le
      have ht1 : t ≤ 1 := (div_le_one hwidth).mpr (by linarith)
      have hmix : (1 - t) * l + t * u = z i := by
        dsimp [t]
        field_simp
        ring
      have h := hf i z l u t
      rw [hmix, Function.update_eq_self] at h
      rw [h]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hlow) (mul_nonneg ht0 hupp)
  exact hgen Finset.univ z (fun i _ => hz i) (by simp)

end Sarkozy.Allocation
