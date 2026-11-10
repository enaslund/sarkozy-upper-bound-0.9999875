module

public import Sarkozy.Moments.Normalization

/-!
# Grouping repeated labels in a mixed moment

These estimates are used when several slots see the same label. Hölder is
applied within the repeated group, without an independence assumption.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiniteLaw

variable {Ω I : Type*} [Fintype Ω] [Fintype I] (μ : FiniteLaw Ω)

theorem moment_rpow_of_nonneg (p q : ℝ) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) :
    μ.moment p (fun x => f x ^ q) = μ.moment (q * p) f := by
  unfold moment
  apply μ.expect_congr
  intro x
  rw [abs_of_nonneg (Real.rpow_nonneg (hf x) _), ← Real.rpow_mul (hf x),
    abs_of_nonneg (hf x)]

theorem lpNorm_prod_le_one_of_moments [Nonempty I] {p : ℝ} (hp : 0 < p)
    (f : I → Ω → ℝ) (hf : ∀ i x, 0 ≤ f i x)
    (hm : ∀ i, μ.moment (p * Fintype.card I) (f i) ≤ 1) :
    μ.lpNorm p (fun x => ∏ i, f i x) ≤ 1 := by
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  apply μ.lpNorm_le_one_of_moment_le_one hp
  have hpoint (x : Ω) : |∏ i, f i x| ^ p = ∏ i, f i x ^ p := by
    rw [abs_of_nonneg (Finset.prod_nonneg (fun i _ => hf i x))]
    exact (Real.finsetProd_rpow Finset.univ (fun i => f i x) (fun i _ => hf i x) p).symm
  unfold moment
  simp only [hpoint]
  apply μ.expect_prod_le_one_of_moments (fun _ : I => Fintype.card I)
    (fun _ => hc) (by simp [hc.ne']) (fun i x => f i x ^ p)
    (fun i x => Real.rpow_nonneg (hf i x) _)
  intro i
  have he (x : Ω) : (f i x ^ p) ^ (Fintype.card I : ℝ) = |f i x| ^ (p * Fintype.card I) := by
    rw [← Real.rpow_mul (hf i x), abs_of_nonneg (hf i x)]
  simpa only [moment, he] using hm i

end Sarkozy.FiniteLaw

namespace Sarkozy

/-- The pair hypothesis is stated for its actual joint distribution. -/
def PairLpBound {Ω X : Type*} [Fintype Ω] [Fintype X] [Nonempty X]
    (μ : FiniteLaw Ω) (x y : Ω → X) (q : ℝ) : Prop :=
  ∀ f g : X → ℝ, |μ.expect (fun ω => f (x ω) * g (y ω))| ≤
    (FiniteLaw.uniform X).lpNorm q f * (FiniteLaw.uniform X).lpNorm q g

theorem repeated_pair_group_moment {Ω X I : Type*} [Fintype Ω] [Fintype X]
    [Nonempty X] [Fintype I] [Nonempty I]
    (μ : FiniteLaw Ω) (x y : Ω → X) {q p : ℝ} (hq : 0 < q)
    (hpair : PairLpBound μ x y q) (f g : I → X → ℝ)
    (hf : ∀ i a, 0 ≤ f i a) (hg : ∀ i a, 0 ≤ g i a)
    (hfm : ∀ i, (FiniteLaw.uniform X).moment (p * (q * Fintype.card I)) (f i) ≤ 1)
    (hgm : ∀ i, (FiniteLaw.uniform X).moment (p * (q * Fintype.card I)) (g i) ≤ 1) :
    μ.expect (fun ω => ((∏ i, f i (x ω)) * ∏ i, g i (y ω)) ^ p) ≤ 1 := by
  let F : X → ℝ := fun a => ∏ i, f i a ^ p
  let G : X → ℝ := fun a => ∏ i, g i a ^ p
  have hFn : (FiniteLaw.uniform X).lpNorm q F ≤ 1 := by
    apply (FiniteLaw.uniform X).lpNorm_prod_le_one_of_moments hq
      (fun i a => f i a ^ p) (fun i a => Real.rpow_nonneg (hf i a) _)
    intro i
    rw [FiniteLaw.moment_rpow_of_nonneg _ _ _ (hf i)]
    exact hfm i
  have hGn : (FiniteLaw.uniform X).lpNorm q G ≤ 1 := by
    apply (FiniteLaw.uniform X).lpNorm_prod_le_one_of_moments hq
      (fun i a => g i a ^ p) (fun i a => Real.rpow_nonneg (hg i a) _)
    intro i
    rw [FiniteLaw.moment_rpow_of_nonneg _ _ _ (hg i)]
    exact hgm i
  have he (ω : Ω) : ((∏ i, f i (x ω)) * ∏ i, g i (y ω)) ^ p = F (x ω) * G (y ω) := by
    rw [Real.mul_rpow (Finset.prod_nonneg (fun i _ => hf i _))
      (Finset.prod_nonneg (fun i _ => hg i _))]
    rw [← Real.finsetProd_rpow Finset.univ (fun i => f i (x ω)) (fun i _ => hf i _) p,
      ← Real.finsetProd_rpow Finset.univ (fun i => g i (y ω)) (fun i _ => hg i _) p]
  simp only [he]
  apply (le_abs_self _).trans ((hpair F G).trans _)
  simpa only [mul_one] using mul_le_mul hFn hGn
    ((FiniteLaw.uniform X).lpNorm_nonneg q G) (by norm_num : (0 : ℝ) ≤ 1)

end Sarkozy
