module

public import Sarkozy.DensityMoments.Unconditional
public import Sarkozy.DensityMoments.PrefixEqualityEvents

/-!
# The laws of `thm:density:iid-prefix`(b) obtained from the reference

`paper/sections/30_density_moment_upgrade.tex`, `thm:density:iid-prefix`(b) and the proofs of
(b)–(d). Two laws derived from the replacement prefix `μ_p = cliqueIidLaw p ℓ`:

* the diagonal copy `Diag_ι(h_p)` of its actual reserved half (`diagLaw reservedCut
  (halfMarginal p ℓ)`): it is the copy law with `σ = halfIndex reservedCut`, 36 draws each used
  twice (`diagLaw_eq_copy`), so it has unit mixed `L^{1200/17}` (`diagLaw_halfMarginal_moment`);
* an individual query-equality measure `E_{p,j} = μ_p · 1[z_{s_j} = z_{t_j}]`: it has mass
  `2^{-ℓ}` (`queryEqMeasure_mass`) and, after normalization, is the copy law identifying the two
  labels of query `j` (`queryEqMeasure_eq_copy`), so `|E_{p,j}(⊗_v f_v)| ≤ 2^{-ℓ} ∏_v ‖f_v‖_{1200/17}`
  (`queryEqMeasure_moment`). The union measure `E_p` is dominated by the sum of the six
  (`deletedWeight_le_sum`): the positive-spectator price of the proof, without a unit moment
  for `E_p/η`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DensityMoments

open CliqueCopies ReflectionCut

variable (p : ℕ) [hp : Fact p.Prime] (ℓ : ℕ)

/-- Each half slot is read by exactly two slots, itself and its mirror. -/
theorem halfIndex_fiber_card (t : reservedCut.Half) :
    (univ.filter (fun v => halfIndex reservedCut v = t)).card ≤ 2 := by
  refine (Finset.card_le_card (s := univ.filter (fun v => halfIndex reservedCut v = t))
    (t := {t.1, reservedCut.flip t.1}) ?_).trans Finset.card_le_two
  intro v hv
  have hv' : halfIndex reservedCut v = t := (mem_filter.mp hv).2
  unfold halfIndex at hv'
  by_cases h : v ∈ reservedCut.half
  · rw [dite_eq_left h] at hv'
    rw [← congrArg Subtype.val hv']
    exact mem_insert_self _ _
  · rw [dite_eq_right h] at hv'
    have : reservedCut.flip v = t.1 := congrArg Subtype.val hv'
    rw [← this, reservedCut.flip_flip]
    exact mem_insert_of_mem (mem_singleton_self _)

/-- **The diagonal copy of the reserved half is a copy law** (36 draws, each used twice), on
product test functions. -/
theorem diagLaw_eq_copy (f : Slot → ZMod (p ^ (2 * ℓ)) → ℝ) :
    (diagLaw reservedCut (halfMarginal p ℓ)).expect (fun z => ∏ v, f v (z v)) =
      (cliqueCopyLaw p ℓ (halfIndex reservedCut)).expect (fun z => ∏ v, f v (z v)) := by
  rw [expect_cliqueCopyLaw_prod]
  unfold diagLaw
  rw [FiniteLaw.expect_map, expect_halfMarginal_split]
  rfl

/-- **`thm:density:iid-prefix`(b), the diagonal copy of the actual reserved half**: unit mixed
`L^{1200/17}` at every odd prime `2^16 ≤ p < 2^512`. -/
theorem diagLaw_halfMarginal_moment (hp2 : p ≠ 2) (h16 : 2 ^ 16 ≤ p) (h512 : p < 2 ^ 512) :
    MixedLpBound (diagLaw reservedCut (halfMarginal p ℓ)) (1200 / 17) 1 := by
  have h := cliqueCopyLaw_moment_proved p ℓ hp2 h16 h512 (halfIndex reservedCut)
    halfIndex_fiber_card
  intro f
  rw [diagLaw_eq_copy]
  exact h f

/-- An individual query-equality measure `E_{p,j}`. -/
noncomputable def queryEqWeight (j : Chamber) (z : Slot → ZMod (p ^ (2 * ℓ))) : ℝ :=
  if z (querySource j) = z (queryTarget j) then (cliqueIidLaw p ℓ).weight z else 0

/-- The union measure is dominated by the sum of the six query-equality measures. -/
theorem deletedWeight_le_sum (z : Slot → ZMod (p ^ (2 * ℓ))) :
    deletedWeight p ℓ z ≤ ∑ j, queryEqWeight p ℓ j z := by
  unfold deletedWeight
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    have hle : queryEqWeight p ℓ j z ≤ ∑ j, queryEqWeight p ℓ j z :=
      Finset.single_le_sum (f := fun j => queryEqWeight p ℓ j z)
        (fun j _ => by unfold queryEqWeight; split_ifs; exacts [(cliqueIidLaw p ℓ).nonneg z, le_rfl])
        (mem_univ j)
    have : queryEqWeight p ℓ j z = (cliqueIidLaw p ℓ).weight z := by
      unfold queryEqWeight
      simp only [hj, ↓reduceIte]
    linarith
  · exact Finset.sum_nonneg fun j _ => by
      unfold queryEqWeight; split_ifs; exacts [(cliqueIidLaw p ℓ).nonneg z, le_rfl]

/-- The slot map identifying the target of query `j` with its source. -/
def mergeQuery (j : Chamber) (v : Slot) : Slot := if v = queryTarget j then querySource j else v

theorem mergeQuery_fiber_card (j : Chamber) (t : Slot) :
    (univ.filter (fun v => mergeQuery j v = t)).card ≤ 2 := by
  refine (Finset.card_le_card (s := univ.filter (fun v => mergeQuery j v = t))
    (t := {t, queryTarget j}) ?_).trans Finset.card_le_two
  intro v hv
  have hv' : mergeQuery j v = t := (mem_filter.mp hv).2
  unfold mergeQuery at hv'
  by_cases h : v = queryTarget j
  · rw [h]
    exact mem_insert_of_mem (mem_singleton_self _)
  · simp only [h, ↓reduceIte] at hv'
    rw [hv']
    exact mem_insert_self _ _

/-- Restricting uniform choice vectors to the equality of two coordinates is the copy law
merging them, with mass `1/|B|`. -/
theorem expect_uniform_eq_merge {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    {s t : Slot} (hst : s ≠ t) (Φ : (Slot → B) → ℝ) :
    (FiniteLaw.uniform (Slot → B)).expect (fun x => if x s = x t then Φ x else 0) =
      (1 / (Fintype.card B : ℝ)) *
        (FiniteLaw.uniform (Slot → B)).expect (fun y => Φ (fun v => if v = t then y s else y v)) := by
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  -- sum over `y` by the value `y t`, which the merged labelling ignores
  set m : (Slot → B) → (Slot → B) := fun y v => if v = t then y s else y v with hm
  have hfib : ∀ x : Slot → B, ∑ y, (if m y = x then (1 : ℝ) else 0) =
      if x s = x t then (Fintype.card B : ℝ) else 0 := by
    intro x
    by_cases hx : x s = x t
    · simp only [hx, ↓reduceIte]
      -- the preimages of `x` are `Function.update x t b`, `b ∈ B`
      have hbij : (univ.filter (fun y => m y = x)).card = Fintype.card B := by
        rw [← Finset.card_univ (α := B)]
        refine Finset.card_nbij' (fun y => y t) (fun b => Function.update x t b) ?_ ?_ ?_ ?_
        · intro y _
          exact mem_coe.mpr (mem_univ _)
        · intro b _
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
          funext v
          simp only [hm]
          by_cases hv : v = t
          · simp only [hv, ↓reduceIte, Function.update_of_ne hst, hx]
          · simp only [hv, ↓reduceIte, Function.update_of_ne hv]
        · intro y hy
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy
          show Function.update x t (y t) = y
          funext v
          by_cases hv : v = t
          · rw [hv, Function.update_self]
          · rw [Function.update_of_ne hv, ← hy]
            simp only [hm, hv, ↓reduceIte]
        · intro b _
          exact Function.update_self t b x
      rw [Finset.sum_boole, hbij]
    · simp only [hx, ↓reduceIte]
      refine Finset.sum_eq_zero fun y _ => ?_
      have hne : m y ≠ x := by
        intro hy
        apply hx
        rw [← hy]
        simp only [hm, hst, ↓reduceIte]
      simp only [hne, ↓reduceIte]
  have hsum : ∑ y, Φ (m y) = ∑ x, (if x s = x t then (Fintype.card B : ℝ) else 0) * Φ x := by
    simp_rw [← hfib, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun y _ => ?_
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [mem_univ, ↓reduceIte]
  rw [hsum]
  have hl : ∑ x, (if x s = x t then Φ x else 0) =
      ∑ x, (if x s = x t then (Fintype.card B : ℝ) else 0) * Φ x / Fintype.card B := by
    refine sum_congr rfl fun x _ => ?_
    split_ifs
    · field_simp
    · simp
  rw [hl, ← Finset.sum_div]
  field_simp

/-- **An individual query-equality measure, normalized, is the copy law merging the query.** -/
theorem queryEqMeasure_eq_copy (j : Chamber) (f : Slot → ZMod (p ^ (2 * ℓ)) → ℝ) :
    ∑ z, queryEqWeight p ℓ j z * ∏ v, f v (z v) =
      (1 / (2 : ℝ) ^ ℓ) * (cliqueCopyLaw p ℓ (mergeQuery j)).expect (fun z => ∏ v, f v (z v)) := by
  have hst : querySource j ≠ queryTarget j := by
    intro h
    exact absurd (query_endpoints_injective (a₁ := (j, false)) (a₂ := (j, true))
      (by simpa using h)) (by simp)
  have hL : ∑ z, queryEqWeight p ℓ j z * ∏ v, f v (z v) = (cliqueIidLaw p ℓ).expect
      (fun z => if z (querySource j) = z (queryTarget j) then ∏ v, f v (z v) else 0) := by
    unfold FiniteLaw.expect queryEqWeight
    refine sum_congr rfl fun z _ => ?_
    by_cases h : z (querySource j) = z (queryTarget j) <;>
      simp only [h, ↓reduceIte, mul_zero, zero_mul]
  rw [hL, expect_cliqueIidLaw, expect_cliqueCopyLaw_prod, ← FiniteLaw.expect_const_mul]
  refine FiniteLaw.expect_congr _ fun q => ?_
  have hinj := prefixLabel_injective p ℓ q
  have hc : ∀ x : Slot → Fin ℓ → Bool,
      (if prefixLabel p ℓ q (x (querySource j)) = prefixLabel p ℓ q (x (queryTarget j)) then
        ∏ v, f v (prefixLabel p ℓ q (x v)) else 0) =
      (if x (querySource j) = x (queryTarget j) then ∏ v, f v (prefixLabel p ℓ q (x v)) else 0) := by
    intro x
    by_cases h : x (querySource j) = x (queryTarget j)
    · simp only [h, ↓reduceIte]
    · have h' : prefixLabel p ℓ q (x (querySource j)) ≠ prefixLabel p ℓ q (x (queryTarget j)) :=
        fun h' => h (hinj h')
      simp only [h, h', ↓reduceIte]
  simp only [hc]
  rw [expect_uniform_eq_merge hst, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  push_cast
  congr 1
  refine FiniteLaw.expect_congr _ fun y => ?_
  refine Finset.prod_congr rfl fun v _ => ?_
  unfold mergeQuery
  by_cases hv : v = queryTarget j
  · simp only [hv, ↓reduceIte]
  · simp only [hv, ↓reduceIte]

/-- **The mass of a query-equality measure is `2^{-ℓ}`.** -/
theorem queryEqMeasure_mass (j : Chamber) :
    ∑ z, queryEqWeight p ℓ j z = 1 / (2 : ℝ) ^ ℓ := by
  have h := queryEqMeasure_eq_copy p ℓ j (fun _ _ => 1)
  simp only [prod_const_one, mul_one, FiniteLaw.expect_const] at h
  exact h

/-- **The query-equality measure has the moment of (b)**: `|E_{p,j}(⊗_v f_v)| ≤ 2^{-ℓ}
∏_v ‖f_v‖_{1200/17}`. -/
theorem queryEqMeasure_moment (hp2 : p ≠ 2) (h16 : 2 ^ 16 ≤ p) (h512 : p < 2 ^ 512) (j : Chamber)
    (f : Slot → ZMod (p ^ (2 * ℓ)) → ℝ) :
    |∑ z, queryEqWeight p ℓ j z * ∏ v, f v (z v)| ≤
      (1 / (2 : ℝ) ^ ℓ) * ∏ v, (FiniteLaw.uniform (ZMod (p ^ (2 * ℓ)))).lpNorm (1200 / 17) (f v) := by
  have h := cliqueCopyLaw_moment_proved p ℓ hp2 h16 h512 (mergeQuery j) (mergeQuery_fiber_card j) f
  rw [queryEqMeasure_eq_copy, abs_mul, abs_of_nonneg (by positivity)]
  rw [one_mul] at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

end Sarkozy.DensityMoments
