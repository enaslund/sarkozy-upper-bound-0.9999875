module

public import Sarkozy.Influence.OpBound

/-!
# Pinned influence, III: the fully pinned pair (`lem:mid:pinpair`, linear-algebra core)

In the proof of `lem:mid:pinpair` (`13_cuts_correlations.tex`), the two free labels
`(y_i, y_j)` are uniform on `{(x, x') ∈ S_i × S_j : K(x, x') = 1}`. Let
`a(x) = ∑_{x'} K(x, x')` and `b(x') = ∑_x K(x, x')`. The paper bounds the maximal correlation
by the second singular value of `D_a^{-1/2} K D_b^{-1/2}`, which is at most
`‖K - kJ‖ / √(min a · min b)`.

`maxCorr_kernelLaw_le` proves this bound for the law `kernelLaw K` proportional to any
nonnegative kernel `K` supported on `S_i × S_j`. It takes lower bounds `A ≤ a`, `B ≤ b` and
an operator bound `L` for the block `(K(x,x') - k)_{S_i × S_j}`. The proof avoids singular
values: `pair_core` is the elementary two-dimensional argument. One combines a centred `g`
with the constant function so as to kill the rank-one part `kJ`, and then uses that the
conditional expectation is a contraction.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Influence

open Sarkozy Sarkozy.Peyre

variable {T : Type*} [Fintype T]

/-- The law on `T × T` proportional to a nonnegative kernel `K`. It is uniform on `{K = 1}`
for a `0/1` kernel. -/
noncomputable def kernelLaw (K : T → T → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hZ : 0 < ∑ x, ∑ y, K x y) : FiniteLaw (T × T) where
  weight q := K q.1 q.2 / ∑ x, ∑ y, K x y
  nonneg q := div_nonneg (hK _ _) hZ.le
  total := by
    rw [← Finset.sum_div, Fintype.sum_prod_type]
    exact div_self hZ.ne'

theorem kernelLaw_expect (K : T → T → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hZ : 0 < ∑ x, ∑ y, K x y) (F : T × T → ℝ) :
    (kernelLaw K hK hZ).expect F = (∑ x, ∑ y, K x y * F (x, y)) / ∑ x, ∑ y, K x y := by
  unfold FiniteLaw.expect
  rw [Fintype.sum_prod_type, Finset.sum_div]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp only [kernelLaw]
  ring

/-- Sums against a kernel supported on `Si × Sj` reduce to `Si × Sj`. -/
theorem sum_kernel_supp (K : T → T → ℝ) (Si Sj : Finset T)
    (hsupp : ∀ x y, K x y ≠ 0 → x ∈ Si ∧ y ∈ Sj) (G : T → T → ℝ) :
    ∑ x, ∑ y, K x y * G x y = ∑ x ∈ Si, ∑ y ∈ Sj, K x y * G x y := by
  have h1 : ∀ x, ∑ y, K x y * G x y = ∑ y ∈ Sj, K x y * G x y := by
    intro x
    refine (Finset.sum_subset (Finset.subset_univ Sj) (fun y _ hy => ?_)).symm
    by_cases hK0 : K x y = 0
    · rw [hK0, zero_mul]
    · exact absurd (hsupp x y hK0).2 hy
  simp_rw [h1]
  refine (Finset.sum_subset (Finset.subset_univ Si) (fun x _ hx => ?_)).symm
  refine Finset.sum_eq_zero (fun y _ => ?_)
  by_cases hK0 : K x y = 0
  · rw [hK0, zero_mul]
  · exact absurd (hsupp x y hK0).1 hx

omit [Fintype T] in
/-- The linear-algebra core of `lem:mid:pinpair`. Write `a(x) = ∑_{y ∈ S_j} K x y`,
`b(y) = ∑_{x ∈ S_i} K x y` and `c = L²/(AB)`. If `∑_y b(y) g(y) = 0`, then
`∑_{x ∈ S_i} (∑_y K x y g y)² / a(x) ≤ c ∑_y b(y) g(y)²`. Equivalently,
`‖E[g(y_j) | y_i]‖² ≤ c ‖g(y_j)‖²` for centred `g`. -/
theorem pair_core (K : T → T → ℝ) (hK : ∀ x y, 0 ≤ K x y) (Si Sj : Finset T)
    {A B k L : ℝ} (hA : 0 < A) (hB : 0 < B)
    (ha : ∀ x ∈ Si, A ≤ ∑ y ∈ Sj, K x y) (hb : ∀ y ∈ Sj, B ≤ ∑ x ∈ Si, K x y)
    (hop : OpBound Si Sj (fun x y => K x y - k) L) (g : T → ℝ)
    (hg : ∑ y ∈ Sj, (∑ x ∈ Si, K x y) * g y = 0) :
    ∑ x ∈ Si, (∑ y ∈ Sj, K x y * g y) ^ 2 / (∑ y ∈ Sj, K x y) ≤
      L ^ 2 / (A * B) * ∑ y ∈ Sj, (∑ x ∈ Si, K x y) * g y ^ 2 := by
  set a : T → ℝ := fun x => ∑ y ∈ Sj, K x y with ha_def
  set b : T → ℝ := fun y => ∑ x ∈ Si, K x y with hb_def
  set u : T → ℝ := fun x => ∑ y ∈ Sj, K x y * g y with hu_def
  set c : ℝ := L ^ 2 / (A * B) with hc_def
  have hc0 : 0 ≤ c := div_nonneg (sq_nonneg L) (mul_pos hA hB).le
  have hapos : ∀ x ∈ Si, 0 < a x := fun x hx => lt_of_lt_of_le hA (ha x hx)
  have hbpos : ∀ y ∈ Sj, 0 < b y := fun y hy => lt_of_lt_of_le hB (hb y hy)
  set Φ := ∑ x ∈ Si, u x ^ 2 / a x with hΦ
  set N := ∑ y ∈ Sj, b y * g y ^ 2 with hN
  set Z := ∑ x ∈ Si, a x with hZ
  have hZb : Z = ∑ y ∈ Sj, b y := by
    simp only [hZ, ha_def, hb_def]
    exact Finset.sum_comm
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg (fun x hx => (hapos x hx).le)
  have hN0 : 0 ≤ N := Finset.sum_nonneg (fun y hy => mul_nonneg (hbpos y hy).le (sq_nonneg _))
  have hsumu : ∑ x ∈ Si, u x = 0 := by
    rw [← hg]
    simp only [hu_def, Finset.sum_mul]
    exact Finset.sum_comm
  -- contraction: `Φ ≤ N`
  have hcontr : Φ ≤ N := by
    have h1 : ∀ x ∈ Si, u x ^ 2 / a x ≤ ∑ y ∈ Sj, K x y * g y ^ 2 := by
      intro x hx
      rw [div_le_iff₀ (hapos x hx)]
      have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Sj (r := fun y => K x y * g y)
        (f := fun y => K x y) (g := fun y => K x y * g y ^ 2) (fun y _ => hK x y)
        (fun y _ => mul_nonneg (hK x y) (sq_nonneg _)) (fun y _ => le_of_eq (by ring))
      simp only [hu_def, ha_def]
      linarith
    calc Φ ≤ ∑ x ∈ Si, ∑ y ∈ Sj, K x y * g y ^ 2 := Finset.sum_le_sum h1
      _ = N := by
        simp only [hN, hb_def, Finset.sum_mul]
        exact Finset.sum_comm
  -- the combination `g' = α + β g` with `∑_y g' y = 0`
  set m : ℝ := (Sj.card : ℝ) with hm
  set α : ℝ := -(∑ y ∈ Sj, g y) with hα
  set g' : T → ℝ := fun y => α + m * g y with hg'
  have hsumg' : ∑ y ∈ Sj, g' y = 0 := by
    simp only [hg', Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      hα, hm]
    ring
  have hKg' : ∀ x, ∑ y ∈ Sj, K x y * g' y = α * a x + m * u x := by
    intro x
    simp only [hg', ha_def, hu_def, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun y _ => by ring)
    · exact Finset.sum_congr rfl (fun y _ => by ring)
  have hKk : ∀ x, ∑ y ∈ Sj, (K x y - k) * g' y = ∑ y ∈ Sj, K x y * g' y := by
    intro x
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsumg', mul_zero, sub_zero]
  -- `Φ' = α² Z + m² Φ` and `N' = α² Z + m² N`
  have hΦ' : ∑ x ∈ Si, (∑ y ∈ Sj, K x y * g' y) ^ 2 / a x = α ^ 2 * Z + m ^ 2 * Φ := by
    have e : ∀ x ∈ Si, (∑ y ∈ Sj, K x y * g' y) ^ 2 / a x =
        α ^ 2 * a x + 2 * α * m * u x + m ^ 2 * (u x ^ 2 / a x) := by
      intro x hx
      rw [hKg' x]
      have := (hapos x hx).ne'
      field_simp
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsumu]
    ring
  have hN' : ∑ y ∈ Sj, b y * g' y ^ 2 = α ^ 2 * Z + m ^ 2 * N := by
    have e : ∀ y ∈ Sj, b y * g' y ^ 2 = α ^ 2 * b y + 2 * α * m * (b y * g y) +
        m ^ 2 * (b y * g y ^ 2) := by
      intro y _
      simp only [hg']
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hZb]
    have hg2 : ∑ y ∈ Sj, b y * g y = 0 := hg
    rw [hg2]
    ring
  -- the operator bound for `g'`
  have hbound : α ^ 2 * Z + m ^ 2 * Φ ≤ c * (α ^ 2 * Z + m ^ 2 * N) := by
    rw [← hΦ', ← hN']
    have h1 : ∑ x ∈ Si, (∑ y ∈ Sj, K x y * g' y) ^ 2 / a x ≤
        (1 / A) * ∑ x ∈ Si, (∑ y ∈ Sj, (K x y - k) * g' y) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun x hx => ?_)
      rw [hKk x, one_div_mul_eq_div]
      exact div_le_div_of_nonneg_left (sq_nonneg _) hA (ha x hx)
    have h2 := hop g'
    have h3 : ∑ y ∈ Sj, g' y ^ 2 ≤ (1 / B) * ∑ y ∈ Sj, b y * g' y ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun y hy => ?_)
      rw [one_div_mul_eq_div, le_div_iff₀ hB]
      have := hb y hy
      nlinarith [sq_nonneg (g' y)]
    calc ∑ x ∈ Si, (∑ y ∈ Sj, K x y * g' y) ^ 2 / a x
        ≤ (1 / A) * ∑ x ∈ Si, (∑ y ∈ Sj, (K x y - k) * g' y) ^ 2 := h1
      _ ≤ (1 / A) * (L ^ 2 * ∑ y ∈ Sj, g' y ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (1 / A) * (L ^ 2 * ((1 / B) * ∑ y ∈ Sj, b y * g' y ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (sq_nonneg L))
            (by positivity)
      _ = c * ∑ y ∈ Sj, b y * g' y ^ 2 := by
          rw [hc_def]
          field_simp
  -- conclusion
  show Φ ≤ c * N
  rcases (Nat.cast_nonneg Sj.card : (0 : ℝ) ≤ Sj.card).eq_or_lt with hm0 | hm0
  · -- `S_j = ∅`
    have hSj : Sj = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast hm0.symm)
    have hΦ0 : Φ = 0 := by
      simp only [hΦ, hu_def, hSj, Finset.sum_empty]
      simp
    rw [hΦ0]
    exact mul_nonneg hc0 hN0
  · have hm2 : 0 < m ^ 2 := by positivity
    rcases le_or_gt 1 c with hc1 | hc1
    · nlinarith
    · have hα2 : 0 ≤ α ^ 2 * Z := mul_nonneg (sq_nonneg α) hZ0
      have h4 : m ^ 2 * Φ ≤ m ^ 2 * (c * N) := by nlinarith
      exact le_of_mul_le_mul_left h4 hm2

/-- **`lem:mid:pinpair`, linear-algebra core.** Let `K ≥ 0` be supported on `S_i × S_j`, with
row sums `a ≥ A > 0` on `S_i` and column sums `b ≥ B > 0` on `S_j`. If the block
`(K - k)_{S_i × S_j}` has operator norm at most `L`, then the two coordinates of the law
proportional to `K` have maximal correlation at most `L / √(A B)`. -/
theorem maxCorr_kernelLaw_le (K : T → T → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hZ : 0 < ∑ x, ∑ y, K x y) (Si Sj : Finset T) (hsupp : ∀ x y, K x y ≠ 0 → x ∈ Si ∧ y ∈ Sj)
    {A B k L : ℝ} (hA : 0 < A) (hB : 0 < B) (hL : 0 ≤ L)
    (ha : ∀ x ∈ Si, A ≤ ∑ y ∈ Sj, K x y) (hb : ∀ y ∈ Sj, B ≤ ∑ x ∈ Si, K x y)
    (hop : OpBound Si Sj (fun x y => K x y - k) L) :
    maxCorr (kernelLaw K hK hZ) Prod.fst Prod.snd ≤ L / √(A * B) := by
  have hAB : 0 < A * B := mul_pos hA hB
  apply maxCorr_le_of_corrLe (div_nonneg hL (Real.sqrt_nonneg _))
  intro f g _ hg
  set Z := ∑ x, ∑ y, K x y with hZdef
  -- expectations as sums over `Si × Sj`
  have hE : ∀ G : T → T → ℝ, (kernelLaw K hK hZ).expect (fun q => G q.1 q.2) =
      (∑ x ∈ Si, ∑ y ∈ Sj, K x y * G x y) / Z := by
    intro G
    rw [kernelLaw_expect, sum_kernel_supp K Si Sj hsupp G]
  have hg0 : ∑ y ∈ Sj, (∑ x ∈ Si, K x y) * g y = 0 := by
    have h := hE (fun _ y => g y)
    rw [hg] at h
    have h' : (∑ x ∈ Si, ∑ y ∈ Sj, K x y * g y) = 0 := by
      have hZ' : Z ≠ 0 := hZ.ne'
      field_simp at h
      linarith
    rw [← h']
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  have hcore := pair_core K hK Si Sj hA hB ha hb hop g hg0
  set a : T → ℝ := fun x => ∑ y ∈ Sj, K x y with ha_def
  have hapos : ∀ x ∈ Si, 0 < a x := fun x hx => lt_of_lt_of_le hA (ha x hx)
  -- `E[f g] = (1/Z) ∑_x f x u x`
  have hfg : (kernelLaw K hK hZ).expect (fun q => f q.1 * g q.2) =
      (∑ x ∈ Si, f x * ∑ y ∈ Sj, K x y * g y) / Z := by
    rw [hE (fun x y => f x * g y)]
    congr 1
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  have hf2 : (kernelLaw K hK hZ).expect (fun q => f q.1 ^ 2) =
      (∑ x ∈ Si, a x * f x ^ 2) / Z := by
    rw [hE (fun x _ => f x ^ 2)]
    congr 1
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [ha_def, Finset.sum_mul]
  have hg2 : (kernelLaw K hK hZ).expect (fun q => g q.2 ^ 2) =
      (∑ y ∈ Sj, (∑ x ∈ Si, K x y) * g y ^ 2) / Z := by
    rw [hE (fun _ y => g y ^ 2)]
    congr 1
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  -- Cauchy–Schwarz with weights `a`
  have hcs : (∑ x ∈ Si, f x * ∑ y ∈ Sj, K x y * g y) ^ 2 ≤
      (∑ x ∈ Si, a x * f x ^ 2) * ∑ x ∈ Si, (∑ y ∈ Sj, K x y * g y) ^ 2 / a x := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Si
      (fun x hx => mul_nonneg (hapos x hx).le (sq_nonneg _))
      (fun x hx => div_nonneg (sq_nonneg _) (hapos x hx).le) (fun x hx => le_of_eq ?_)
    have := (hapos x hx).ne'
    field_simp
  set P := ∑ x ∈ Si, a x * f x ^ 2 with hP
  set Φ := ∑ x ∈ Si, (∑ y ∈ Sj, K x y * g y) ^ 2 / a x with hΦ
  set N := ∑ y ∈ Sj, (∑ x ∈ Si, K x y) * g y ^ 2 with hN
  have hP0 : 0 ≤ P := Finset.sum_nonneg (fun x hx => mul_nonneg (hapos x hx).le (sq_nonneg _))
  have hN0 : 0 ≤ N := Finset.sum_nonneg (fun y _ =>
    mul_nonneg (Finset.sum_nonneg (fun x _ => hK x y)) (sq_nonneg _))
  set c := L ^ 2 / (A * B) with hc
  have hc0 : 0 ≤ c := div_nonneg (sq_nonneg L) hAB.le
  have hsq : (∑ x ∈ Si, f x * ∑ y ∈ Sj, K x y * g y) ^ 2 ≤ (P * (c * N)) :=
    hcs.trans (mul_le_mul_of_nonneg_left hcore hP0)
  have hsqrt : |∑ x ∈ Si, f x * ∑ y ∈ Sj, K x y * g y| ≤ √c * (√P * √N) := by
    rw [← Real.sqrt_mul hP0, ← Real.sqrt_mul hc0, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hLc : L / √(A * B) = √c := by
    rw [hc, Real.sqrt_div (sq_nonneg L), Real.sqrt_sq hL]
  rw [hfg, hf2, hg2, hLc, abs_div, abs_of_pos hZ, Real.sqrt_div hP0,
    Real.sqrt_div hN0]
  have hsZ : 0 < √Z := Real.sqrt_pos.mpr hZ
  have hZZ : √Z * √Z = Z := Real.mul_self_sqrt hZ.le
  rw [div_le_iff₀ hZ]
  calc |∑ x ∈ Si, f x * ∑ y ∈ Sj, K x y * g y| ≤ √c * (√P * √N) := hsqrt
    _ = √c * (√P / √Z) * (√N / √Z) * Z := by
        field_simp
        rw [Real.sq_sqrt hZ.le]

end Sarkozy.Influence
