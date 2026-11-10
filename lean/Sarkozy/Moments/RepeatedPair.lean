module

public import Sarkozy.Moments.Grouping

/-!
# The repeated-pair improvement

If two labels each occupy t slots, and their actual pair law has unit mixed
Lq norm, then adjoining n arbitrary uniformly distributed slots gives unit
mixed L^(tq+n). No independence of the residual labels is assumed.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

def repeatedConfiguration {Ω X I K : Type*} (x y : Ω → X) (z : K → Ω → X)
    (ω : Ω) : (I ⊕ I) ⊕ K → X :=
  Sum.elim (Sum.elim (fun _ => x ω) (fun _ => y ω)) (fun k => z k ω)

theorem mixedLpBound_repeated_pair {Ω X I K : Type*} [Fintype Ω]
    [Fintype X] [DecidableEq X] [Nonempty X] [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype K] [DecidableEq K]
    (μ : FiniteLaw Ω) (x y : Ω → X) (z : K → Ω → X) {q : ℝ} (hq : 0 < q)
    (hpair : PairLpBound μ x y q)
    (hz : ∀ k f, μ.expect (fun ω => f (z k ω)) = (FiniteLaw.uniform X).expect f) :
    MixedLpBound (μ.map (repeatedConfiguration (I := I) x y z))
      ((Fintype.card I : ℝ) * q + Fintype.card K) 1 := by
  let R : ℝ := Fintype.card I * q + Fintype.card K
  have ht : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have htq : 0 < (Fintype.card I : ℝ) * q := mul_pos ht hq
  have hR : 0 < R := add_pos_of_pos_of_nonneg htq (Nat.cast_nonneg _)
  have hp : 0 < R / (Fintype.card I * q) := div_pos hR htq
  apply mixedLpBound_of_normalized _ hR
  intro f hf hnorm
  let H : Option K → Ω → ℝ := fun k => match k with
    | none => fun ω => (∏ i, f (Sum.inl (Sum.inl i)) (x ω)) *
        ∏ i, f (Sum.inl (Sum.inr i)) (y ω)
    | some k => fun ω => f (Sum.inr k) (z k ω)
  let P : Option K → ℝ := fun k => match k with
    | none => R / (Fintype.card I * q)
    | some _ => R
  have hP : ∀ k, 0 < P k := by
    intro k
    cases k with
    | none => exact hp
    | some k => exact hR
  have hsum : ∑ k, 1 / P k = 1 := by
    rw [Fintype.sum_option]
    simp only [P, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hR.ne', htq.ne']
    rfl
  have hH : ∀ k ω, 0 ≤ H k ω := by
    intro k ω
    cases k with
    | none =>
      exact mul_nonneg (Finset.prod_nonneg (fun _ _ => hf _ _))
        (Finset.prod_nonneg (fun _ _ => hf _ _))
    | some k => exact hf _ _
  have hm : ∀ k, μ.expect (fun ω => H k ω ^ P k) ≤ 1 := by
    intro k
    cases k with
    | none =>
      apply repeated_pair_group_moment μ x y hq hpair
        (fun i => f (Sum.inl (Sum.inl i))) (fun i => f (Sum.inl (Sum.inr i)))
        (fun _ _ => hf _ _) (fun _ _ => hf _ _)
      all_goals
        intro i
        have he : R / (Fintype.card I * q) * (q * Fintype.card I) = R := by
          field_simp [htq.ne', ht.ne', hq.ne']
        rw [he]
        exact ((FiniteLaw.uniform X).moment_eq_one_of_lpNorm_eq_one hR.ne' (hnorm _)).le
    | some k =>
      change μ.expect (fun ω => f (Sum.inr k) (z k ω) ^ R) ≤ 1
      rw [hz k (fun a => f (Sum.inr k) a ^ R)]
      have he := (FiniteLaw.uniform X).moment_eq_one_of_lpNorm_eq_one hR.ne' (hnorm (Sum.inr k))
      simpa only [FiniteLaw.moment, abs_of_nonneg (hf _ _)] using he.le
  have h := μ.expect_prod_le_one_of_moments P hP hsum H hH hm
  rw [FiniteLaw.expect_map]
  simpa only [Function.comp_def, repeatedConfiguration, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr, Fintype.prod_option, H] using h

/-- The exponent is d − (2 − q)t when d = 2t + n. -/
theorem repeated_pair_exponent (t n : ℕ) (q : ℝ) :
    (t : ℝ) * q + n = (2 * t + n : ℕ) - (2 - q) * t := by
  push_cast
  ring

theorem repeated_pair_selected_exponents :
    (2 : ℝ) * (3 / 2) + 8 = 11 ∧
    (4 : ℝ) * (3 / 2) + 64 = 70 ∧
    (1 : ℝ) * (3 / 2) + 10 = 23 / 2 := by norm_num

end Sarkozy
