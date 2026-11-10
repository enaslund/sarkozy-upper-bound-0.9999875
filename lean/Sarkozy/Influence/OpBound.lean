module

public import Sarkozy.Peyre.Main

/-!
# Pinned influence, II: operator bounds of finite matrices

The matrix algebra used by `prop:middle-negative` and `cor:influence-schur`
(`13_cuts_correlations.tex`).

Matrices are functions `A : U → V → ℝ`. A block is selected by Finsets `R ⊆ U` (rows) and
`C ⊆ V` (columns). `OpBound R C A Λ` says that the block `(A i j)_{i ∈ R, j ∈ C}` has
`ℓ²(C) → ℓ²(R)` norm at most `Λ`; for `Λ ≥ 0` this is `‖A_{RC}‖ ≤ Λ`. No subtypes are needed.

* Monotonicity, sub-blocks, the triangle inequality (`OpBound.add`), products
  (`OpBound.comp`), and entries (`|A_ij| ≤ ‖A‖`, `OpBound.abs_entry_le`).
* The Schur test `‖A‖² ≤ (max row sum)(max column sum)` for `A ≥ 0` (`opBound_schur`).
* The conversion to the subtype-indexed form used by `peyre_finite` (`OpBound.toSubtype`).
* The inverse `Q = (I - E)^{-1}` on `F`, characterized by `Q = I + E Q` on `F × F`:
  `Q = I + E + E² Q`, and `‖E² Q‖ ≤ e²/(1-e)` when `‖E‖ ≤ e < 1` (`inverse_split`).
  The proof uses no Neumann series. `E² Q` satisfies the fixed-point identity
  `E² Q = E² + E (E² Q)`, and `opBound_of_fixed` bounds any solution of such an identity.
  `exists_inverse` gives existence.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Influence

variable {U V W : Type*}

/-- `OpBound R C A Λ`: `∑_{i ∈ R} (∑_{j ∈ C} A_ij x_j)² ≤ Λ² ∑_{j ∈ C} x_j²` for all `x`, i.e.
`‖A_{RC}‖_{ℓ²(C) → ℓ²(R)} ≤ Λ` when `Λ ≥ 0`. -/
def OpBound (R : Finset U) (C : Finset V) (A : U → V → ℝ) (Λ : ℝ) : Prop :=
  ∀ x : V → ℝ, ∑ i ∈ R, (∑ j ∈ C, A i j * x j) ^ 2 ≤ Λ ^ 2 * ∑ j ∈ C, x j ^ 2

/-- The Euclidean norm of `x` on the Finset `C`. -/
noncomputable def vnorm (C : Finset V) (x : V → ℝ) : ℝ := √(∑ j ∈ C, x j ^ 2)

theorem vnorm_nonneg (C : Finset V) (x : V → ℝ) : 0 ≤ vnorm C x := Real.sqrt_nonneg _

theorem vnorm_sq (C : Finset V) (x : V → ℝ) : vnorm C x ^ 2 = ∑ j ∈ C, x j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (x j)))

theorem vnorm_congr {C : Finset V} {x y : V → ℝ} (h : ∀ j ∈ C, x j = y j) :
    vnorm C x = vnorm C y := by
  unfold vnorm
  rw [Finset.sum_congr rfl (fun j hj => by rw [h j hj])]

/-- Minkowski's inequality on a Finset. -/
theorem vnorm_add_le (C : Finset V) (x y : V → ℝ) :
    vnorm C (fun j => x j + y j) ≤ vnorm C x + vnorm C y := by
  have hx := vnorm_nonneg C x
  have hy := vnorm_nonneg C y
  have hcs : ∑ j ∈ C, x j * y j ≤ vnorm C x * vnorm C y := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq C x y
    rw [← vnorm_sq, ← vnorm_sq, ← mul_pow] at h
    exact (abs_le_of_sq_le_sq' h (mul_nonneg hx hy)).2
  have h2 : ∑ j ∈ C, (x j + y j) ^ 2 ≤ (vnorm C x + vnorm C y) ^ 2 := by
    have e : ∑ j ∈ C, (x j + y j) ^ 2 =
        ∑ j ∈ C, x j ^ 2 + 2 * ∑ j ∈ C, x j * y j + ∑ j ∈ C, y j ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [e, ← vnorm_sq, ← vnorm_sq]
    nlinarith
  unfold vnorm at h2 ⊢
  calc √(∑ j ∈ C, (x j + y j) ^ 2) ≤ √((√(∑ j ∈ C, x j ^ 2) + √(∑ j ∈ C, y j ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt h2
    _ = _ := Real.sqrt_sq (add_nonneg hx hy)

theorem OpBound.vnorm_le {R : Finset U} {C : Finset V} {A : U → V → ℝ} {Λ : ℝ}
    (h : OpBound R C A Λ) (hΛ : 0 ≤ Λ) (x : V → ℝ) :
    vnorm R (fun i => ∑ j ∈ C, A i j * x j) ≤ Λ * vnorm C x := by
  unfold vnorm
  rw [← Real.sqrt_sq hΛ, ← Real.sqrt_mul (sq_nonneg Λ)]
  exact Real.sqrt_le_sqrt (h x)

theorem OpBound.of_vnorm {R : Finset U} {C : Finset V} {A : U → V → ℝ} {Λ : ℝ}
    (h : ∀ x : V → ℝ, vnorm R (fun i => ∑ j ∈ C, A i j * x j) ≤ Λ * vnorm C x) :
    OpBound R C A Λ := by
  intro x
  have h2 := pow_le_pow_left₀ (vnorm_nonneg _ _) (h x) 2
  rw [mul_pow, vnorm_sq, vnorm_sq] at h2
  exact h2

theorem OpBound.mono {R : Finset U} {C : Finset V} {A : U → V → ℝ} {Λ Λ' : ℝ}
    (h : OpBound R C A Λ) (hΛ : 0 ≤ Λ) (hle : Λ ≤ Λ') : OpBound R C A Λ' := by
  intro x
  refine (h x).trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun j _ => sq_nonneg _)))
  exact pow_le_pow_left₀ hΛ hle 2

/-- A sub-block has the same bound. -/
theorem OpBound.subset {R R' : Finset U} {C C' : Finset V} {A : U → V → ℝ} {Λ : ℝ}
    (h : OpBound R C A Λ) (hR : R' ⊆ R) (hC : C' ⊆ C) : OpBound R' C' A Λ := by
  classical
  intro x
  set x' : V → ℝ := fun j => if j ∈ C' then x j else 0 with hx'
  have e1 : ∀ i, ∑ j ∈ C', A i j * x j = ∑ j ∈ C, A i j * x' j := by
    intro i
    rw [← Finset.sum_subset hC (fun j _ hj' => by simp only [hx', hj', ite_false, mul_zero])]
    exact Finset.sum_congr rfl (fun j hj => by simp only [hx', hj, ite_true])
  have e2 : ∑ j ∈ C', x j ^ 2 = ∑ j ∈ C, x' j ^ 2 := by
    rw [← Finset.sum_subset hC (fun j _ hj' => by simp only [hx', hj', ite_false]; ring)]
    exact Finset.sum_congr rfl (fun j hj => by simp only [hx', hj, ite_true])
  calc ∑ i ∈ R', (∑ j ∈ C', A i j * x j) ^ 2 = ∑ i ∈ R', (∑ j ∈ C, A i j * x' j) ^ 2 := by
        simp_rw [e1]
    _ ≤ ∑ i ∈ R, (∑ j ∈ C, A i j * x' j) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hR (fun _ _ _ => sq_nonneg _)
    _ ≤ Λ ^ 2 * ∑ j ∈ C, x' j ^ 2 := h x'
    _ = Λ ^ 2 * ∑ j ∈ C', x j ^ 2 := by rw [e2]

/-- The triangle inequality. -/
theorem OpBound.add {R : Finset U} {C : Finset V} {A B : U → V → ℝ} {a b : ℝ}
    (hA : OpBound R C A a) (hB : OpBound R C B b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    OpBound R C (fun i j => A i j + B i j) (a + b) := by
  apply OpBound.of_vnorm
  intro x
  have e : (fun i => ∑ j ∈ C, (A i j + B i j) * x j) =
      fun i => (∑ j ∈ C, A i j * x j) + ∑ j ∈ C, B i j * x j := by
    funext i
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [e]
  calc _ ≤ vnorm R (fun i => ∑ j ∈ C, A i j * x j) + vnorm R (fun i => ∑ j ∈ C, B i j * x j) :=
        vnorm_add_le _ _ _
    _ ≤ a * vnorm C x + b * vnorm C x := add_le_add (hA.vnorm_le ha x) (hB.vnorm_le hb x)
    _ = (a + b) * vnorm C x := by ring

/-- A product of blocks: `‖A B‖ ≤ ‖A‖ ‖B‖`, the product summing over `M`. -/
theorem OpBound.comp {R : Finset U} {M : Finset W} {C : Finset V} {A : U → W → ℝ}
    {B : W → V → ℝ} {a b : ℝ} (hA : OpBound R M A a) (hB : OpBound M C B b) :
    OpBound R C (fun i j => ∑ l ∈ M, A i l * B l j) (a * b) := by
  intro x
  have e : ∀ i, ∑ j ∈ C, (∑ l ∈ M, A i l * B l j) * x j =
      ∑ l ∈ M, A i l * (∑ j ∈ C, B l j * x j) := by
    intro i
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun j _ => by ring))
  simp_rw [e]
  calc ∑ i ∈ R, (∑ l ∈ M, A i l * (∑ j ∈ C, B l j * x j)) ^ 2 ≤
        a ^ 2 * ∑ l ∈ M, (∑ j ∈ C, B l j * x j) ^ 2 := hA _
    _ ≤ a ^ 2 * (b ^ 2 * ∑ j ∈ C, x j ^ 2) := mul_le_mul_of_nonneg_left (hB x) (sq_nonneg a)
    _ = (a * b) ^ 2 * ∑ j ∈ C, x j ^ 2 := by ring

/-- Entries are bounded by the norm. -/
theorem OpBound.abs_entry_le {R : Finset U} {C : Finset V} {A : U → V → ℝ} {Λ : ℝ}
    (h : OpBound R C A Λ) (hΛ : 0 ≤ Λ) {i : U} {j : V} (hi : i ∈ R) (hj : j ∈ C) :
    |A i j| ≤ Λ := by
  classical
  have h1 := h (fun j' => if j' = j then 1 else 0)
  have e1 : ∀ i', ∑ j' ∈ C, A i' j' * (if j' = j then 1 else 0) = A i' j := by
    intro i'
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' C j, ite_eq_left hj]
  have e2 : ∑ j' ∈ C, (if j' = j then (1 : ℝ) else 0) ^ 2 = 1 := by
    simp only [ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw [Finset.sum_ite_eq' C j, ite_eq_left hj]
  simp_rw [e1] at h1
  rw [e2, mul_one] at h1
  have h2 : A i j ^ 2 ≤ Λ ^ 2 :=
    le_trans (Finset.single_le_sum (f := fun i' => A i' j ^ 2) (fun _ _ => sq_nonneg _) hi) h1
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hΛ]
  exact Real.sqrt_le_sqrt h2

/-- The Schur test: for `A ≥ 0` with row sums `≤ ρ` and column sums `≤ γ`,
`‖A‖ ≤ √(ργ)`. -/
theorem opBound_schur {R : Finset U} {C : Finset V} {A : U → V → ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {ρ γ : ℝ} (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ) (hrow : ∀ i ∈ R, ∑ j ∈ C, A i j ≤ ρ)
    (hcol : ∀ j ∈ C, ∑ i ∈ R, A i j ≤ γ) : OpBound R C A (√(ρ * γ)) := by
  intro x
  rw [Real.sq_sqrt (mul_nonneg hρ hγ)]
  have h1 : ∀ i ∈ R, (∑ j ∈ C, A i j * x j) ^ 2 ≤ ρ * ∑ j ∈ C, A i j * x j ^ 2 := by
    intro i hi
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul C (r := fun j => A i j * x j)
      (f := fun j => A i j) (g := fun j => A i j * x j ^ 2) (fun j _ => hA i j)
      (fun j _ => mul_nonneg (hA i j) (sq_nonneg _)) (fun j _ => le_of_eq (by ring))
    exact hcs.trans (mul_le_mul_of_nonneg_right (hrow i hi)
      (Finset.sum_nonneg (fun j _ => mul_nonneg (hA i j) (sq_nonneg _))))
  calc ∑ i ∈ R, (∑ j ∈ C, A i j * x j) ^ 2 ≤ ∑ i ∈ R, ρ * ∑ j ∈ C, A i j * x j ^ 2 :=
        Finset.sum_le_sum h1
    _ = ρ * ∑ j ∈ C, (∑ i ∈ R, A i j) * x j ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ ρ * ∑ j ∈ C, γ * x j ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j hj =>
          mul_le_mul_of_nonneg_right (hcol j hj) (sq_nonneg _))) hρ
    _ = ρ * γ * ∑ j ∈ C, x j ^ 2 := by rw [← Finset.mul_sum]; ring

/-- The subtype-indexed form of an operator bound, as used by `peyre_finite`. -/
theorem OpBound.toSubtype {R : Finset U} {C : Finset V} {A : U → V → ℝ} {Λ : ℝ}
    (h : OpBound R C A Λ) (x : C → ℝ) :
    ∑ i : R, (∑ j : C, A i j * x j) ^ 2 ≤ Λ ^ 2 * ∑ j : C, x j ^ 2 := by
  classical
  set x' : V → ℝ := fun v => if hv : v ∈ C then x ⟨v, hv⟩ else 0 with hx'
  have e1 : ∀ i, ∑ j : C, A i j * x j = ∑ j ∈ C, A i j * x' j := by
    intro i
    rw [← Finset.sum_coe_sort C]
    exact Finset.sum_congr rfl (fun j _ => by simp only [hx', j.2, dite_true])
  have e2 : ∑ j : C, x j ^ 2 = ∑ j ∈ C, x' j ^ 2 := by
    rw [← Finset.sum_coe_sort C]
    exact Finset.sum_congr rfl (fun j _ => by simp only [hx', j.2, dite_true])
  simp_rw [e1]
  rw [e2, Finset.sum_coe_sort R (fun i => (∑ j ∈ C, A i j * x' j) ^ 2)]
  exact h x'

/-! ### The inverse of `I - E` on a Finset -/

/-- A solution `R` of the fixed-point identity `R = E₂ + E R` on `F × F` satisfies
`‖R‖ ≤ ‖E₂‖ / (1 - e)` when `‖E‖ ≤ e < 1`. -/
theorem opBound_of_fixed (F : Finset U) {E E₂ R : U → U → ℝ} {e c : ℝ} (he0 : 0 ≤ e)
    (he1 : e < 1) (hc : 0 ≤ c) (hE : OpBound F F E e) (hE₂ : OpBound F F E₂ c)
    (hR : ∀ i ∈ F, ∀ j ∈ F, R i j = E₂ i j + ∑ l ∈ F, E i l * R l j) :
    OpBound F F R (c / (1 - e)) := by
  have h1e : 0 < 1 - e := by linarith
  apply OpBound.of_vnorm
  intro x
  set Rx : U → ℝ := fun i => ∑ j ∈ F, R i j * x j with hRx
  have hdecomp : ∀ i ∈ F, Rx i = (∑ j ∈ F, E₂ i j * x j) + ∑ l ∈ F, E i l * Rx l := by
    intro i hi
    have e1 : Rx i = ∑ j ∈ F, (E₂ i j + ∑ l ∈ F, E i l * R l j) * x j :=
      Finset.sum_congr rfl (fun j hj => by rw [hR i hi j hj])
    have e2 : ∑ l ∈ F, E i l * Rx l = ∑ j ∈ F, (∑ l ∈ F, E i l * R l j) * x j := by
      simp only [hRx, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => by ring))
    rw [e1, e2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have h1 : vnorm F Rx ≤ c * vnorm F x + e * vnorm F Rx :=
    calc vnorm F Rx = vnorm F (fun i => (∑ j ∈ F, E₂ i j * x j) + ∑ l ∈ F, E i l * Rx l) :=
          vnorm_congr hdecomp
      _ ≤ _ := (vnorm_add_le _ _ _).trans
          (add_le_add (hE₂.vnorm_le hc x) (hE.vnorm_le he0 Rx))
  rw [div_mul_eq_mul_div, le_div_iff₀ h1e]
  have e3 : vnorm F Rx * (1 - e) = vnorm F Rx - e * vnorm F Rx := by ring
  rw [e3]
  linarith

/-- `E² = (∑_{l ∈ F} E_il E_lj)_{ij}`. -/
noncomputable def sqMat (F : Finset U) (E : U → U → ℝ) (i j : U) : ℝ := ∑ l ∈ F, E i l * E l j

/-- `Q = (I - E)^{-1}` on `F` (`Q = I + E Q` on `F × F`) splits as `Q = I + E + R` with
`R = E² Q`, and `R` satisfies `R = E² + E R` on `F × F`. -/
theorem inverse_identities [DecidableEq U] (F : Finset U) (E Q : U → U → ℝ)
    (hQ : ∀ i ∈ F, ∀ j ∈ F, Q i j = (if i = j then 1 else 0) + ∑ l ∈ F, E i l * Q l j) :
    (∀ i ∈ F, ∀ j ∈ F, Q i j =
        (if i = j then 1 else 0) + E i j + ∑ l ∈ F, sqMat F E i l * Q l j) ∧
      (∀ i ∈ F, ∀ j ∈ F, ∑ l ∈ F, sqMat F E i l * Q l j =
        sqMat F E i j + ∑ l ∈ F, E i l * ∑ m ∈ F, sqMat F E l m * Q m j) := by
  constructor
  · intro i hi j hj
    rw [hQ i hi j hj, add_assoc]
    congr 1
    have e1 : ∑ l ∈ F, E i l * Q l j =
        ∑ l ∈ F, (E i l * (if l = j then 1 else 0) + E i l * ∑ m ∈ F, E l m * Q m j) :=
      Finset.sum_congr rfl (fun l hl => by rw [hQ l hl j hj, mul_add])
    rw [e1, Finset.sum_add_distrib]
    congr 1
    · simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' F j, ite_eq_left hj]
    · simp only [sqMat, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun l _ => by ring))
  · intro i hi j hj
    have e1 : ∑ l ∈ F, sqMat F E i l * Q l j = ∑ l ∈ F, (sqMat F E i l *
        (if l = j then 1 else 0) + sqMat F E i l * ∑ m ∈ F, E l m * Q m j) :=
      Finset.sum_congr rfl (fun l hl => by rw [hQ l hl j hj, mul_add])
    rw [e1, Finset.sum_add_distrib]
    congr 1
    · simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' F j, ite_eq_left hj]
    · have hassoc : ∀ m, ∑ l ∈ F, sqMat F E i l * E l m = ∑ l ∈ F, E i l * sqMat F E l m := by
        intro m
        simp only [sqMat, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun l _ => by ring))
      calc ∑ l ∈ F, sqMat F E i l * ∑ m ∈ F, E l m * Q m j
          = ∑ m ∈ F, (∑ l ∈ F, sqMat F E i l * E l m) * Q m j := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun l _ => by ring))
        _ = ∑ m ∈ F, (∑ l ∈ F, E i l * sqMat F E l m) * Q m j := by simp_rw [hassoc]
        _ = ∑ l ∈ F, E i l * ∑ m ∈ F, sqMat F E l m * Q m j := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun m _ => by ring))

/-- `prop:middle-negative` (a), matrix part: if `‖E‖ ≤ e < 1` on `F` and `Q = (I - E)^{-1}` on
`F` (i.e. `Q = I + E Q` on `F × F`), then `Q = I + E + R` on `F × F` with
`‖R‖ ≤ e²/(1-e)`. -/
theorem inverse_split [DecidableEq U] (F : Finset U) (E Q : U → U → ℝ) {e : ℝ} (he0 : 0 ≤ e)
    (he1 : e < 1) (hE : OpBound F F E e)
    (hQ : ∀ i ∈ F, ∀ j ∈ F, Q i j = (if i = j then 1 else 0) + ∑ l ∈ F, E i l * Q l j) :
    (∀ i ∈ F, ∀ j ∈ F, Q i j =
        (if i = j then 1 else 0) + E i j + ∑ l ∈ F, sqMat F E i l * Q l j) ∧
      OpBound F F (fun i j => ∑ l ∈ F, sqMat F E i l * Q l j) (e ^ 2 / (1 - e)) := by
  obtain ⟨h1, h2⟩ := inverse_identities F E Q hQ
  refine ⟨h1, ?_⟩
  have hE2 : OpBound F F (sqMat F E) (e * e) := hE.comp hE
  rw [sq]
  exact opBound_of_fixed F he0 he1 (mul_nonneg he0 he0) hE hE2 (fun i hi j hj => h2 i hi j hj)

/-- `prop:middle-negative` (a), last inequality: off the diagonal,
`[(I - E)^{-1}]_ij ≤ ε_ij + e²/(1-e)`. -/
theorem inverse_offdiag_le [DecidableEq U] (F : Finset U) (E Q : U → U → ℝ) {e : ℝ}
    (he0 : 0 ≤ e) (he1 : e < 1) (hE : OpBound F F E e)
    (hQ : ∀ i ∈ F, ∀ j ∈ F, Q i j = (if i = j then 1 else 0) + ∑ l ∈ F, E i l * Q l j)
    {i j : U} (hi : i ∈ F) (hj : j ∈ F) (hij : i ≠ j) : Q i j ≤ E i j + e ^ 2 / (1 - e) := by
  obtain ⟨h1, h2⟩ := inverse_split F E Q he0 he1 hE hQ
  have hR := h2.abs_entry_le (div_nonneg (sq_nonneg e) (by linarith)) hi hj
  rw [h1 i hi j hj, ite_eq_right hij, zero_add]
  have := le_abs_self (∑ l ∈ F, sqMat F E i l * Q l j)
  linarith

/-- Existence of `(I - E)^{-1}` on `F` when `‖E‖ ≤ e < 1`. -/
theorem exists_inverse [DecidableEq U] (F : Finset U) (E : U → U → ℝ) {e : ℝ} (he0 : 0 ≤ e)
    (he1 : e < 1) (hE : OpBound F F E e) :
    ∃ Q : U → U → ℝ,
      ∀ i ∈ F, ∀ j ∈ F, Q i j = (if i = j then 1 else 0) + ∑ l ∈ F, E i l * Q l j := by
  classical
  let A : Matrix F F ℝ := fun i j => (if i = j then 1 else 0) - E i j
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hd : A.mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    set d : F → ℝ := x - y with hd_def
    set d' : U → ℝ := fun u => if hu : u ∈ F then d ⟨u, hu⟩ else 0 with hd'
    have hfix : ∀ i ∈ F, d' i = ∑ l ∈ F, E i l * d' l := by
      intro i hi
      have h0 := congrFun hd ⟨i, hi⟩
      simp only [Matrix.mulVec, dotProduct, A, sub_mul, Finset.sum_sub_distrib, ite_mul,
        one_mul, zero_mul, Pi.zero_apply] at h0
      rw [Finset.sum_ite_eq (Finset.univ : Finset F) (⟨i, hi⟩ : F),
        ite_eq_left (Finset.mem_univ _)] at h0
      have e1 : ∑ l ∈ F, E i l * d' l = ∑ l : F, E i l * d l := by
        rw [← Finset.sum_coe_sort F]
        exact Finset.sum_congr rfl (fun l _ => by simp only [hd', l.2, dite_true])
      rw [e1]
      simp only [hd', hi, dite_true]
      linarith
    have hb := hE d'
    have hsum : ∑ i ∈ F, d' i ^ 2 = ∑ i ∈ F, (∑ l ∈ F, E i l * d' l) ^ 2 :=
      Finset.sum_congr rfl (fun i hi => by rw [← hfix i hi])
    rw [← hsum] at hb
    have hnn : 0 ≤ ∑ i ∈ F, d' i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have he2 : e ^ 2 < 1 := by nlinarith
    have hzero : ∑ i ∈ F, d' i ^ 2 = 0 := by nlinarith
    have hz : ∀ i ∈ F, d' i ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hzero
    have hdz : d = 0 := by
      funext l
      have := hz l l.2
      simp only [hd', l.2, dite_true] at this
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    have : x - y = 0 := hdz
    exact sub_eq_zero.mp this
  have hunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hunit)
  refine ⟨fun i j => if h : i ∈ F ∧ j ∈ F then A⁻¹ ⟨i, h.1⟩ ⟨j, h.2⟩ else 0, ?_⟩
  intro i hi j hj
  have h0 := congrFun (congrFun hmul ⟨i, hi⟩) ⟨j, hj⟩
  rw [Matrix.mul_apply, Matrix.one_apply] at h0
  have hA : ∀ l : F, A ⟨i, hi⟩ l = (if (⟨i, hi⟩ : F) = l then 1 else 0) - E i l :=
    fun l => rfl
  simp only [hA, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul] at h0
  rw [Finset.sum_ite_eq (Finset.univ : Finset F) (⟨i, hi⟩ : F),
    ite_eq_left (Finset.mem_univ _)] at h0
  have e1 : ∑ l ∈ F, E i l * (fun i j => if h : i ∈ F ∧ j ∈ F then A⁻¹ ⟨i, h.1⟩ ⟨j, h.2⟩
      else 0) l j = ∑ l : F, E i l * A⁻¹ l ⟨j, hj⟩ := by
    rw [← Finset.sum_coe_sort F]
    exact Finset.sum_congr rfl (fun l _ => by simp only [l.2, hj, and_self, dite_true])
  rw [e1]
  simp only [hi, hj, and_self, dite_true]
  have hij : (if (⟨i, hi⟩ : F) = ⟨j, hj⟩ then (1 : ℝ) else 0) = if i = j then 1 else 0 := by
    by_cases h : i = j
    · subst h
      simp
    · have : (⟨i, hi⟩ : F) ≠ ⟨j, hj⟩ := fun h' => h (congrArg Subtype.val h')
      rw [ite_eq_right this, ite_eq_right h]
  rw [← hij]
  linarith

end Sarkozy.Influence
