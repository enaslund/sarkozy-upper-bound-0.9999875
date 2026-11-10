module

public import Sarkozy.Cuts.Restriction
public import Sarkozy.ProbabilityProducts

/-!
# Cuts, III′: the injectivity event of a product law (`lem:restriction` (d))

`13_cuts_correlations.tex`, `lem:restriction` (d). Let `λ_X = ⊗_{i ∈ M} λ_i` be a product of laws
on a finite label set `L` (the paper: `L = 𝔽_p`, `|L| = p`), each of density at most `κ` relative
to the uniform law, that is `λ_i(a) ≤ κ/|L|`. Let `I_X` be the event that the `m = |M|`
coordinates are distinct. Then `P_X ≥ 1 - (m choose 2) κ/|L|` (`prob_injective_ge`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Peyre

variable {M L : Type*} [Fintype M] [DecidableEq M] [Fintype L] [DecidableEq L]

omit [DecidableEq L] in
/-- Two distinct coordinates of a product law are independent. -/
theorem expect_pi_pair (lam : M → FiniteLaw L) {i j : M} (hij : i ≠ j) (f g : L → ℝ) :
    (FiniteLaw.pi lam).expect (fun x => f (x i) * g (x j)) = (lam i).expect f * (lam j).expect g := by
  have h := FiniteLaw.expect_pi_product lam
    (fun k => if k = i then f else if k = j then g else fun _ => 1)
  have e1 : (fun x : M → L => ∏ k, (if k = i then f else if k = j then g else fun _ => 1) (x k)) =
      fun x => f (x i) * g (x j) := by
    funext x
    have : ∀ k, (if k = i then f else if k = j then g else fun _ => (1 : ℝ)) (x k) =
        (if k = i then f (x i) else 1) * (if k = j then g (x j) else 1) := by
      intro k
      by_cases hki : k = i
      · subst hki
        simp only [ite_true, ite_eq_right hij, mul_one]
      · by_cases hkj : k = j
        · subst hkj
          simp only [ite_eq_right hki, ite_true, one_mul]
        · simp only [ite_eq_right hki, ite_eq_right hkj, mul_one]
    simp only [this, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  have e2 : ∏ k, (lam k).expect (if k = i then f else if k = j then g else fun _ => 1) =
      (lam i).expect f * (lam j).expect g := by
    have : ∀ k, (lam k).expect (if k = i then f else if k = j then g else fun _ => 1) =
        (if k = i then (lam i).expect f else 1) * (if k = j then (lam j).expect g else 1) := by
      intro k
      by_cases hki : k = i
      · subst hki
        simp only [ite_true, ite_eq_right hij, mul_one]
      · by_cases hkj : k = j
        · subst hkj
          simp only [ite_eq_right hki, ite_true, one_mul]
        · simp only [ite_eq_right hki, ite_eq_right hkj, mul_one]
          exact FiniteLaw.expect_const _ 1
    simp only [this, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  rw [e1] at h
  rw [h, e2]

theorem expect_indicator_eq (μ : FiniteLaw L) (a : L) :
    μ.expect (fun b => if b = a then (1 : ℝ) else 0) = μ.weight a := by
  unfold FiniteLaw.expect
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Two distinct coordinates with laws of density at most `κ` coincide with probability at most
`κ/|L|`. -/
theorem prob_coord_eq_le (lam : M → FiniteLaw L) {κ : ℝ}
    (hκ : ∀ i a, (lam i).weight a ≤ κ / Fintype.card L) {i j : M} (hij : i ≠ j) :
    (FiniteLaw.pi lam).expect (fun x => if x i = x j then (1 : ℝ) else 0) ≤ κ / Fintype.card L := by
  have e : (fun x : M → L => if x i = x j then (1 : ℝ) else 0) =
      fun x => ∑ a, (if x i = a then (1 : ℝ) else 0) * (if x j = a then 1 else 0) := by
    funext x
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
  rw [e, expect_sum]
  have hterm : ∀ a, (FiniteLaw.pi lam).expect
      (fun x => (if x i = a then (1 : ℝ) else 0) * (if x j = a then 1 else 0)) =
      (lam i).weight a * (lam j).weight a := by
    intro a
    have := expect_pi_pair lam hij (fun b => if b = a then (1 : ℝ) else 0)
      (fun b => if b = a then (1 : ℝ) else 0)
    rw [expect_indicator_eq, expect_indicator_eq] at this
    exact this
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  calc ∑ a, (lam i).weight a * (lam j).weight a ≤ ∑ a, (lam i).weight a * (κ / Fintype.card L) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hκ j a) ((lam i).nonneg a))
    _ = κ / Fintype.card L := by rw [← Finset.sum_mul, (lam i).total, one_mul]

/-- **`lem:restriction` (d).** If `λ_X = ⊗_{i ∈ M} λ_i` with `λ_i(a) ≤ κ/|L|`, the event that the
coordinates are distinct has probability `P_X ≥ 1 - (m choose 2) κ/|L|`, `m = |M|`. -/
theorem prob_injective_ge (lam : M → FiniteLaw L) {κ : ℝ}
    (hκ : ∀ i a, (lam i).weight a ≤ κ / Fintype.card L) :
    1 - ((Fintype.card M).choose 2 : ℝ) * (κ / Fintype.card L) ≤
      prob (FiniteLaw.pi lam) (fun x => Function.Injective x) := by
  set μ := FiniteLaw.pi lam
  -- pointwise union bound over ordered pairs
  have hpt : ∀ x : M → L, ind (fun x : M → L => ¬ Function.Injective x) x ≤
      (1 / 2) * ∑ q ∈ (Finset.univ : Finset M).offDiag,
        (if x q.1 = x q.2 then (1 : ℝ) else 0) := by
    intro x
    have hnn : 0 ≤ ∑ q ∈ (Finset.univ : Finset M).offDiag, (if x q.1 = x q.2 then (1 : ℝ) else 0) :=
      Finset.sum_nonneg (fun q _ => by split_ifs <;> norm_num)
    by_cases hx : Function.Injective x
    · rw [ind_of_neg (E := fun x : M → L => ¬ Function.Injective x) (not_not.mpr hx)]
      positivity
    · rw [ind_of_pos (E := fun x : M → L => ¬ Function.Injective x) hx]
      obtain ⟨i, j, hxij, hij⟩ : ∃ i j, x i = x j ∧ i ≠ j := by
        by_contra hc
        push Not at hc
        exact hx (fun i j h => hc i j h)
      have hsub : ({(i, j), (j, i)} : Finset (M × M)) ⊆ (Finset.univ : Finset M).offDiag := by
        intro q hq
        rw [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩
        · exact Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hij.symm⟩
      have hne : ((i, j) : M × M) ≠ (j, i) := fun h => hij (Prod.mk.inj h).1
      have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := fun q => if x q.1 = x q.2 then (1 : ℝ) else 0)
        (fun q _ _ => by split_ifs <;> norm_num)
      rw [Finset.sum_pair hne] at h2
      simp only [ite_eq_left hxij, ite_eq_left hxij.symm] at h2
      linarith
  have hcomp : prob μ (fun x => Function.Injective x) =
      1 - prob μ (fun x : M → L => ¬ Function.Injective x) := by
    unfold prob
    rw [eq_sub_iff_add_eq]
    have hsum : ∀ x : M → L, ind (fun x : M → L => Function.Injective x) x +
        ind (fun x : M → L => ¬ Function.Injective x) x = 1 := by
      intro x
      by_cases hx : Function.Injective x
      · rw [ind_of_pos (E := fun x : M → L => Function.Injective x) hx,
          ind_of_neg (E := fun x : M → L => ¬ Function.Injective x) (not_not.mpr hx)]
        ring
      · rw [ind_of_neg (E := fun x : M → L => Function.Injective x) hx,
          ind_of_pos (E := fun x : M → L => ¬ Function.Injective x) hx]
        ring
    calc μ.expect (ind (fun x : M → L => Function.Injective x)) +
          μ.expect (ind (fun x : M → L => ¬ Function.Injective x))
        = μ.expect (fun x => ind (fun x : M → L => Function.Injective x) x +
            ind (fun x : M → L => ¬ Function.Injective x) x) := by rw [FiniteLaw.expect_add]
      _ = μ.expect (fun _ => (1 : ℝ)) := μ.expect_congr hsum
      _ = 1 := FiniteLaw.expect_const _ 1
  have hbound : prob μ (fun x : M → L => ¬ Function.Injective x) ≤
      (1 / 2) * ∑ q ∈ (Finset.univ : Finset M).offDiag, κ / Fintype.card L := by
    unfold prob
    calc μ.expect (ind (fun x : M → L => ¬ Function.Injective x))
        ≤ μ.expect (fun x => (1 / 2) * ∑ q ∈ (Finset.univ : Finset M).offDiag,
            (if x q.1 = x q.2 then (1 : ℝ) else 0)) := μ.expect_mono hpt
      _ = (1 / 2) * ∑ q ∈ (Finset.univ : Finset M).offDiag,
            μ.expect (fun x => if x q.1 = x q.2 then (1 : ℝ) else 0) := by
          rw [FiniteLaw.expect_const_mul, expect_sum]
      _ ≤ (1 / 2) * ∑ q ∈ (Finset.univ : Finset M).offDiag, κ / Fintype.card L := by
          gcongr with q hq
          exact prob_coord_eq_le lam hκ (Finset.mem_offDiag.mp hq).2.2
  have hcard : (1 / 2) * ∑ q ∈ (Finset.univ : Finset M).offDiag, κ / Fintype.card L =
      ((Fintype.card M).choose 2 : ℝ) * (κ / Fintype.card L) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.offDiag_card, Nat.cast_choose_two,
      Finset.card_univ]
    have hle : Fintype.card M ≤ Fintype.card M * Fintype.card M :=
      Nat.le_mul_self (Fintype.card M)
    rw [Nat.cast_sub hle, Nat.cast_mul]
    ring
  rw [hcomp]
  linarith

end Sarkozy.Cuts
