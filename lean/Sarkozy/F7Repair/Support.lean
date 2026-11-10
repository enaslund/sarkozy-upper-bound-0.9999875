module

public import Sarkozy.Structured.RepairExistence

@[expose] public section

/-!
# The repair equations on the support of a pair law (`lem:tr:repair`(a), without full support)

`paper/sections/17_completion_repair.tex`, `lem:tr:repair`. WP-R's `Structured/RepairExistence`
and `Structured/MarginalRepair` prove the lemma for marginal laws `ν_X`, `ν_Y` of *full support*
(`hνX : ∀ x, 0 < ν_X x`). The one-way repairs of (F7) are applied to the uniform law
`π^new = λ_p(G^new)` of a repaired graph on the space of all labellings of the two halves; its half
marginals live only on the injective labellings. This file passes to the supports:

* `mX`, `mY`, `margX`, `margY`: the marginal weights and laws of a pair law `ν` on `X × Y`;
* `SX ν`, `SY ν`: the supports of the two marginals, as subtypes;
* `resX`, `resY`, `resP`: the restricted laws, of full support on `SX`, `SY` (`resX_pos`);
* `condA`, `condB`: the conditional operators `A`, `A* ` on the supports, and the identities
  `hmX`, `hmY`, `hA`, `hB` that WP-R's lemmas ask for (`resP_fst`, `resP_snd`, `resP_condA`,
  `resP_condB`);
* `sum_res_pair`: a sum against `ν` is the same sum over the supports.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.Recentering Sarkozy.Structured

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The first marginal weight `ν_X(x) = ∑_y ν(x, y)`. -/
noncomputable def mX (ν : FiniteLaw (X × Y)) (x : X) : ℝ := ∑ y, ν.weight (x, y)

/-- The second marginal weight `ν_Y(y) = ∑_x ν(x, y)`. -/
noncomputable def mY (ν : FiniteLaw (X × Y)) (y : Y) : ℝ := ∑ x, ν.weight (x, y)

variable (ν : FiniteLaw (X × Y))

theorem mX_nonneg (x : X) : 0 ≤ mX ν x := sum_nonneg fun _ _ => ν.nonneg _

theorem mY_nonneg (y : Y) : 0 ≤ mY ν y := sum_nonneg fun _ _ => ν.nonneg _

theorem weight_eq_zero_of_mX {x : X} (h : mX ν x = 0) (y : Y) : ν.weight (x, y) = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => ν.nonneg (x, y))).mp h y (mem_univ y)

theorem weight_eq_zero_of_mY {y : Y} (h : mY ν y = 0) (x : X) : ν.weight (x, y) = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => ν.nonneg (x, y))).mp h x (mem_univ x)

theorem sum_mX : ∑ x, mX ν x = 1 := by
  unfold mX
  rw [← Fintype.sum_prod_type' (fun x y => ν.weight (x, y))]
  exact ν.total

theorem sum_mY : ∑ y, mY ν y = 1 := by
  unfold mY
  rw [Finset.sum_comm, ← Fintype.sum_prod_type' (fun x y => ν.weight (x, y))]
  exact ν.total

/-- The first marginal law. -/
noncomputable def margX : FiniteLaw X := ⟨mX ν, mX_nonneg ν, sum_mX ν⟩

/-- The second marginal law. -/
noncomputable def margY : FiniteLaw Y := ⟨mY ν, mY_nonneg ν, sum_mY ν⟩

theorem expect_fst (φ : X → ℝ) : ν.expect (fun p => φ p.1) = (margX ν).expect φ := by
  unfold FiniteLaw.expect
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  show _ = mX ν x * φ x
  unfold mX
  rw [sum_mul]

theorem expect_snd (φ : Y → ℝ) : ν.expect (fun p => φ p.2) = (margY ν).expect φ := by
  unfold FiniteLaw.expect
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine sum_congr rfl fun y _ => ?_
  show _ = mY ν y * φ y
  unfold mY
  rw [sum_mul]

/-- The support of the first marginal. -/
abbrev SX : Type _ := {x : X // mX ν x ≠ 0}

/-- The support of the second marginal. -/
abbrev SY : Type _ := {y : Y // mY ν y ≠ 0}

/-- A sum over `X` of a function vanishing off the support is the sum over the support. -/
theorem sum_SX (F : X → ℝ) (hF : ∀ x, mX ν x = 0 → F x = 0) :
    ∑ x : SX ν, F x.1 = ∑ x, F x := by
  classical
  rw [← Finset.sum_subtype (univ.filter fun x => mX ν x ≠ 0) (by simp) F]
  refine Finset.sum_filter_of_ne fun x _ hx h => hx (hF x h)

theorem sum_SY (F : Y → ℝ) (hF : ∀ y, mY ν y = 0 → F y = 0) :
    ∑ y : SY ν, F y.1 = ∑ y, F y := by
  classical
  rw [← Finset.sum_subtype (univ.filter fun y => mY ν y ≠ 0) (by simp) F]
  refine Finset.sum_filter_of_ne fun y _ hy h => hy (hF y h)

/-- **A sum against `ν` is the same sum over the two supports.** -/
theorem sum_res_pair (G : X × Y → ℝ) :
    ∑ p : SX ν × SY ν, ν.weight (p.1.1, p.2.1) * G (p.1.1, p.2.1) = ∑ p, ν.weight p * G p := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [← sum_SX ν (fun x => ∑ y, ν.weight (x, y) * G (x, y))
    (fun _ h => sum_eq_zero fun _ _ => by rw [weight_eq_zero_of_mX ν h, zero_mul])]
  refine sum_congr rfl fun x _ => ?_
  exact sum_SY ν (fun y => ν.weight (x.1, y) * G (x.1, y))
    (fun _ h => by rw [weight_eq_zero_of_mY ν h, zero_mul])

theorem sum_SY_weight (x : X) : ∑ y : SY ν, ν.weight (x, y.1) = mX ν x :=
  sum_SY ν (fun y => ν.weight (x, y)) (fun _ h => weight_eq_zero_of_mY ν h x)

theorem sum_SX_weight (y : Y) : ∑ x : SX ν, ν.weight (x.1, y) = mY ν y :=
  sum_SX ν (fun x => ν.weight (x, y)) (fun _ h => weight_eq_zero_of_mX ν h y)

/-- The first marginal restricted to its support. -/
noncomputable def resX : FiniteLaw (SX ν) where
  weight x := mX ν x.1
  nonneg x := mX_nonneg ν x.1
  total := by rw [sum_SX ν (mX ν) (fun x h => h)]; exact sum_mX ν

/-- The second marginal restricted to its support. -/
noncomputable def resY : FiniteLaw (SY ν) where
  weight y := mY ν y.1
  nonneg y := mY_nonneg ν y.1
  total := by rw [sum_SY ν (mY ν) (fun y h => h)]; exact sum_mY ν

theorem resX_pos (x : SX ν) : 0 < (resX ν).weight x := lt_of_le_of_ne (mX_nonneg ν x.1) (Ne.symm x.2)

theorem resY_pos (y : SY ν) : 0 < (resY ν).weight y := lt_of_le_of_ne (mY_nonneg ν y.1) (Ne.symm y.2)

/-- The pair law restricted to the product of the supports. -/
noncomputable def resP : FiniteLaw (SX ν × SY ν) where
  weight p := ν.weight (p.1.1, p.2.1)
  nonneg p := ν.nonneg _
  total := by
    have h := sum_res_pair ν (fun _ => 1)
    simp only [mul_one] at h
    rw [h]
    exact ν.total

/-- Expectations under `resP` are expectations under `ν`. -/
theorem resP_expect (G : X × Y → ℝ) :
    (resP ν).expect (fun p => G (p.1.1, p.2.1)) = ν.expect G :=
  sum_res_pair ν G

/-- The conditional operator `A`, `(Ak)(x) = E_ν[k(y) | x]`, on the supports. -/
noncomputable def condA : (SY ν → ℝ) →ₗ[ℝ] (SX ν → ℝ) where
  toFun k x := (∑ y : SY ν, ν.weight (x.1, y.1) * k y) / mX ν x.1
  map_add' k k' := by
    funext x
    simp only [Pi.add_apply, mul_add, sum_add_distrib, add_div]
  map_smul' c k := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    exact sum_congr rfl fun y _ => by ring

/-- The adjoint conditional operator `A*`, `(A*h)(y) = E_ν[h(x) | y]`, on the supports. -/
noncomputable def condB : (SX ν → ℝ) →ₗ[ℝ] (SY ν → ℝ) where
  toFun h y := (∑ x : SX ν, ν.weight (x.1, y.1) * h x) / mY ν y.1
  map_add' h h' := by
    funext y
    simp only [Pi.add_apply, mul_add, sum_add_distrib, add_div]
  map_smul' c h := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    exact sum_congr rfl fun x _ => by ring

theorem condA_apply (k : SY ν → ℝ) (x : SX ν) :
    condA ν k x = (∑ y : SY ν, ν.weight (x.1, y.1) * k y) / mX ν x.1 := rfl

theorem condB_apply (h : SX ν → ℝ) (y : SY ν) :
    condB ν h y = (∑ x : SX ν, ν.weight (x.1, y.1) * h x) / mY ν y.1 := rfl

theorem resP_fst (φ : SX ν → ℝ) :
    (resP ν).expect (fun p => φ p.1) = (resX ν).expect φ := by
  unfold FiniteLaw.expect
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  show ∑ y : SY ν, ν.weight (x.1, y.1) * φ x = mX ν x.1 * φ x
  rw [← sum_mul, sum_SY_weight]

theorem resP_snd (φ : SY ν → ℝ) :
    (resP ν).expect (fun p => φ p.2) = (resY ν).expect φ := by
  unfold FiniteLaw.expect
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine sum_congr rfl fun y _ => ?_
  show ∑ x : SX ν, ν.weight (x.1, y.1) * φ y = mY ν y.1 * φ y
  rw [← sum_mul, sum_SX_weight]

theorem resP_condA (h : SX ν → ℝ) (k : SY ν → ℝ) :
    (resP ν).expect (fun p => h p.1 * k p.2) = ip (resX ν) h (condA ν k) := by
  unfold ip FiniteLaw.expect
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  show ∑ y : SY ν, ν.weight (x.1, y.1) * (h x * k y) =
    mX ν x.1 * (h x * ((∑ y : SY ν, ν.weight (x.1, y.1) * k y) / mX ν x.1))
  have hx : mX ν x.1 ≠ 0 := x.2
  field_simp
  rw [Finset.mul_sum]
  exact sum_congr rfl fun y _ => by ring

theorem resP_condB (h : SX ν → ℝ) (k : SY ν → ℝ) :
    (resP ν).expect (fun p => h p.1 * k p.2) = ip (resY ν) (condB ν h) k := by
  unfold ip FiniteLaw.expect
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine sum_congr rfl fun y _ => ?_
  show ∑ x : SX ν, ν.weight (x.1, y.1) * (h x * k y) =
    mY ν y.1 * (((∑ x : SX ν, ν.weight (x.1, y.1) * h x) / mY ν y.1) * k y)
  have hy : mY ν y.1 ≠ 0 := y.2
  field_simp
  rw [Finset.mul_sum]
  exact sum_congr rfl fun x _ => by ring

/-- Extension by zero from the first support. -/
noncomputable def extX (h : SX ν → ℝ) (x : X) : ℝ := if hx : mX ν x ≠ 0 then h ⟨x, hx⟩ else 0

/-- Extension by zero from the second support. -/
noncomputable def extY (k : SY ν → ℝ) (y : Y) : ℝ := if hy : mY ν y ≠ 0 then k ⟨y, hy⟩ else 0

@[simp] theorem extX_val (h : SX ν → ℝ) (x : SX ν) : extX ν h x.1 = h x := by
  unfold extX
  simp only [ne_eq, x.2, not_false_eq_true, ↓reduceDIte]

@[simp] theorem extY_val (k : SY ν → ℝ) (y : SY ν) : extY ν k y.1 = k y := by
  unfold extY
  simp only [ne_eq, y.2, not_false_eq_true, ↓reduceDIte]

theorem extX_zero (h : SX ν → ℝ) {x : X} (hx : mX ν x = 0) : extX ν h x = 0 := by
  unfold extX
  simp only [ne_eq, hx, not_true_eq_false, ↓reduceDIte]

theorem extY_zero (k : SY ν → ℝ) {y : Y} (hy : mY ν y = 0) : extY ν k y = 0 := by
  unfold extY
  simp only [ne_eq, hy, not_true_eq_false, ↓reduceDIte]

/-- The restricted mean of a function is its mean under the marginal. -/
theorem resX_expect_val (F : X → ℝ) : (resX ν).expect (fun x => F x.1) = (margX ν).expect F := by
  unfold FiniteLaw.expect
  rw [show (∑ x : SX ν, (resX ν).weight x * F x.1) = ∑ x, mX ν x * F x from
    sum_SX ν (fun x => mX ν x * F x) (fun x h => by rw [h, zero_mul])]
  rfl

theorem resY_expect_val (F : Y → ℝ) : (resY ν).expect (fun y => F y.1) = (margY ν).expect F := by
  unfold FiniteLaw.expect
  rw [show (∑ y : SY ν, (resY ν).weight y * F y.1) = ∑ y, mY ν y * F y from
    sum_SY ν (fun y => mY ν y * F y) (fun y h => by rw [h, zero_mul])]
  rfl

theorem margX_expect_extX (h : SX ν → ℝ) :
    (margX ν).expect (extX ν h) = (resX ν).expect h := by
  rw [← resX_expect_val]
  exact (resX ν).expect_congr fun x => extX_val ν h x

theorem margY_expect_extY (k : SY ν → ℝ) :
    (margY ν).expect (extY ν k) = (resY ν).expect k := by
  rw [← resY_expect_val]
  exact (resY ν).expect_congr fun y => extY_val ν k y

theorem nrm_margX_extX (h : SX ν → ℝ) : nrm (margX ν) (extX ν h) = nrm (resX ν) h := by
  unfold nrm ip
  rw [← resX_expect_val ν (fun x => extX ν h x * extX ν h x)]
  simp only [extX_val]

theorem nrm_margY_extY (k : SY ν → ℝ) : nrm (margY ν) (extY ν k) = nrm (resY ν) k := by
  unfold nrm ip
  rw [← resY_expect_val ν (fun y => extY ν k y * extY ν k y)]
  simp only [extY_val]

end Sarkozy.F7Repair
