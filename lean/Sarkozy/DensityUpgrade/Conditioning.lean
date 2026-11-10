module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Algebra.Order.Chebyshev

/-!
# A collision conditioning bound (`lem:density:conditioning`)

`paper/sections/31_density_induction_upgrade.tex`, Lemma "A collision conditioning
bound" (`lem:density:conditioning`). Its first assertion reads:

> For `d₀ ≤ 6` nonnegative functions `f_i`, each depending on one coordinate and
> normalized by `‖f_i‖_r = 1` under its own marginal `μ_i`, put `M = ∏_i E_{μ_i} f_i`.
> Under any joint law (coupling) on the product space whose one-coordinate marginals
> are exactly the `μ_i`, `E ∏_i f_i ≥ M − B_r (1 − M)`, where one may take
> `B_r = 1280` for `2 ≤ r ≤ 6`, or `B_r = 1024` for `4/3 ≤ r ≤ 3/2`.

Only the joint law enters, so the statement is formalized for nonnegative real random
variables `X i` (`i : Fin d`) on a finite probability space `(Ω, p)`, with
`E (X i)^r = 1` (real power) and `M = ∏ i, E (X i)`. The marginal hypothesis of the
paper is exactly the statement that `X i` has the moments of `μ_i`.

This file proves the range `2 ≤ r` (`conditioning_collision_bound`, with `B_r = 1280`
and `d ≤ 6`, as in the paper; the general form `conditioning_collision_bound_of_two_le`
gives any `B ≥ max 1 d`, for every `r ≥ 2`, so `r ≤ 6` is not needed). The proof follows
the paper's pointwise inequality `∏ x_i ≥ (1 − W)(1 + Z) = 1 + ∑ (x_i − 1) − W Z`
with `w = (1 − x)_+`, `z = (x − 1)_+`, applied to `x_i = X i / m_i`, `m_i = E X i`, when
`M ≥ 1/2`; positivity handles `M < 1/2`. For `r ≥ 2` the opposite-deviation term is
controlled through the second moment: `4 W Z ≤ (W + Z)^2 = (∑ |x_i − 1|)^2 ≤ d ∑ (x_i − 1)^2`,
and `E X_i^2 ≤ (E X_i^r)^{2/r} = 1`. This replaces the paper's bound by `φ_r` and
gives the smaller constant `d`; the stated constant `1280` follows.

The range `4/3 ≤ r ≤ 3/2` and the conditioning assertion are not formalized here.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.DensityUpgrade

/-- `1 + ∑ a_i ≤ ∏ (1 + a_i)` for nonnegative `a_i`. -/
theorem conditioning_one_add_sum_le_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) : 1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have hs : ∀ i ∈ s, 0 ≤ a i := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have h1 := ih hs
    have h2 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg hs
    have h3 : 0 ≤ a j := ha j (Finset.mem_insert_self j s)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + a j) (sub_nonneg.2 h1),
      mul_nonneg h3 h2]

/-- Weierstrass product inequality: `1 - ∑ w_i ≤ ∏ (1 - w_i)` for `0 ≤ w_i ≤ 1`. -/
theorem conditioning_one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∀ i ∈ s, w i ≤ 1) :
    1 - ∑ i ∈ s, w i ≤ ∏ i ∈ s, (1 - w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have h0 : ∀ i ∈ s, 0 ≤ w i := fun i hi => hw0 i (Finset.mem_insert_of_mem hi)
    have h1 : ∀ i ∈ s, w i ≤ 1 := fun i hi => hw1 i (Finset.mem_insert_of_mem hi)
    have hih := ih h0 h1
    have h2 : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg h0
    have h3 : 0 ≤ w j := hw0 j (Finset.mem_insert_self j s)
    have h4 : w j ≤ 1 := hw1 j (Finset.mem_insert_self j s)
    nlinarith [mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 hih), mul_nonneg h3 h2]

/-- The paper's pointwise inequality, in the second-moment form used for `r ≥ 2`:
for nonnegative `y_i` (`i : Fin d`),
`∏ y_i ≥ (1 - W)(1 + Z) = 1 + ∑ (y_i - 1) - W Z ≥ 1 + ∑ (y_i - 1) - (d/4) ∑ (y_i - 1)^2`,
where `W = ∑ (1 - y_i)_+` and `Z = ∑ (y_i - 1)_+`. -/
theorem conditioning_pointwise {d : ℕ} (y : Fin d → ℝ) (hy : ∀ i, 0 ≤ y i) :
    1 + ∑ i, (y i - 1) - ((d : ℝ) / 4) * ∑ i, (y i - 1) ^ 2 ≤ ∏ i, y i := by
  obtain ⟨w, hw⟩ : ∃ w : Fin d → ℝ, ∀ i, w i = max (1 - y i) 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : Fin d → ℝ, ∀ i, z i = max (y i - 1) 0 := ⟨_, fun _ => rfl⟩
  have hcase : ∀ i, (w i = 1 - y i ∧ z i = 0) ∨ (w i = 0 ∧ z i = y i - 1) := by
    intro i
    rw [hw i, hz i]
    rcases le_total (y i) 1 with h | h
    · left; exact ⟨max_eq_left (by linarith), max_eq_right (by linarith)⟩
    · right; exact ⟨max_eq_right (by linarith), max_eq_left (by linarith)⟩
  have hw0 : ∀ i, 0 ≤ w i := fun i => by
    rcases hcase i with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [hw i]; exact le_max_right _ _
    · rw [h1]
  have hw1 : ∀ i, w i ≤ 1 := fun i => by
    rcases hcase i with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; linarith [hy i]
    · rw [h1]; exact zero_le_one
  have hz0 : ∀ i, 0 ≤ z i := fun i => by rw [hz i]; exact le_max_right _ _
  have hfac : ∀ i, y i = (1 - w i) * (1 + z i) := fun i => by
    rcases hcase i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> ring
  have hdiff : ∀ i, y i - 1 = z i - w i := fun i => by
    rcases hcase i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> ring
  have habs : ∀ i, (w i + z i) ^ 2 = (y i - 1) ^ 2 := fun i => by
    rcases hcase i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> ring
  have hprod : ∏ i, y i = (∏ i, (1 - w i)) * ∏ i, (1 + z i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hfac i)
  have hA := conditioning_one_sub_sum_le_prod Finset.univ w (fun i _ => hw0 i)
    (fun i _ => hw1 i)
  have hB := conditioning_one_add_sum_le_prod Finset.univ z (fun i _ => hz0 i)
  have hW0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw0 i)
  have hZ0 : 0 ≤ ∑ i, z i := Finset.sum_nonneg (fun i _ => hz0 i)
  have hmain : (1 - ∑ i, w i) * (1 + ∑ i, z i) ≤ ∏ i, y i := by
    rcases le_total (∑ i, w i) 1 with h | h
    · rw [hprod]
      calc (1 - ∑ i, w i) * (1 + ∑ i, z i)
          ≤ (1 - ∑ i, w i) * ∏ i, (1 + z i) :=
            mul_le_mul_of_nonneg_left hB (by linarith)
        _ ≤ (∏ i, (1 - w i)) * ∏ i, (1 + z i) :=
            mul_le_mul_of_nonneg_right hA (by linarith)
    · have : 0 ≤ ∏ i, y i := Finset.prod_nonneg (fun i _ => hy i)
      nlinarith
  have hsum : ∑ i, (y i - 1) = ∑ i, z i - ∑ i, w i := by
    rw [Finset.sum_congr rfl (fun i _ => hdiff i), Finset.sum_sub_distrib]
  have hcs : (∑ i, w i + ∑ i, z i) ^ 2 ≤ (d : ℝ) * ∑ i, (y i - 1) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => w i + z i)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    rw [Finset.sum_add_distrib] at h
    rw [← Finset.sum_congr rfl (fun i _ => habs i)]
    exact h
  rw [hsum]
  nlinarith [sq_nonneg (∑ i, w i - ∑ i, z i)]

/-- Jensen for a real power `t ≥ 1`: if `E u^t ≤ 1` then `E u ≤ 1`. -/
theorem conditioning_mean_le_one {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (u : Ω → ℝ) (hu : ∀ ω, 0 ≤ u ω) {t : ℝ}
    (ht : 1 ≤ t) (hnorm : ∑ ω, p ω * u ω ^ t ≤ 1) : ∑ ω, p ω * u ω ≤ 1 := by
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow (s := Finset.univ) p u
    (fun ω _ => hp ω) hp1 (fun ω _ => hu ω) ht
  by_contra h
  rw [not_le] at h
  have := Real.one_lt_rpow h (by linarith : (0 : ℝ) < t)
  linarith

/-- For `r ≥ 2`, `E X^r = 1` gives `E X^2 ≤ 1` (Jensen with exponent `r/2`). -/
theorem conditioning_second_moment_le_one {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) {r : ℝ}
    (hr : 2 ≤ r) (hnorm : ∑ ω, p ω * X ω ^ r = 1) : ∑ ω, p ω * X ω ^ 2 ≤ 1 := by
  refine conditioning_mean_le_one p hp hp1 (fun ω => X ω ^ 2) (fun ω => by positivity)
    (t := r / 2) (by linarith) (le_of_eq ?_)
  rw [← hnorm]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (hX ω)]
  congr 1
  push_cast
  ring

/-- The two normalized moments: with `m = E x ≠ 0`, `E (x/m - 1) = 0` and
`E (x/m - 1)^2 = E x^2 / m^2 - 1`. -/
theorem conditioning_normalized_moments {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp1 : ∑ ω, p ω = 1) (x : Ω → ℝ) {m : ℝ} (hm : ∑ ω, p ω * x ω = m) (hm0 : m ≠ 0) :
    ∑ ω, p ω * (x ω / m - 1) = 0 ∧
      ∑ ω, p ω * (x ω / m - 1) ^ 2 = (∑ ω, p ω * x ω ^ 2) / m ^ 2 - 1 := by
  constructor
  · have h : ∀ ω, p ω * (x ω / m - 1) = (p ω * x ω) * m⁻¹ - p ω := fun ω => by ring
    rw [Finset.sum_congr rfl (fun ω _ => h ω), Finset.sum_sub_distrib, ← Finset.sum_mul, hp1,
      hm, mul_inv_cancel₀ hm0]
    ring
  · have h : ∀ ω, p ω * (x ω / m - 1) ^ 2
        = (p ω * x ω ^ 2) * (m ^ 2)⁻¹ - 2 * ((p ω * x ω) * m⁻¹) + p ω := fun ω => by
      field_simp
      ring
    rw [Finset.sum_congr rfl (fun ω _ => h ω), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, hp1, hm, mul_inv_cancel₀ hm0]
    field_simp
    ring

/-- `lem:density:conditioning`, first assertion, general form for `r ≥ 2`.
For nonnegative real random variables `X i` (`i : Fin d`) on a finite probability
space `(Ω, p)` with `E (X i)^r = 1` (real power, `r ≥ 2`), and any `B ≥ max 1 d`,
`E ∏ X i ≥ M - B (1 - M)` where `M = ∏ i, E (X i)`. -/
theorem conditioning_collision_bound_of_two_le {Ω : Type*} [Fintype Ω] {d : ℕ}
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : Fin d → Ω → ℝ) (hX : ∀ i ω, 0 ≤ X i ω) {r : ℝ} (hr : 2 ≤ r)
    (hnorm : ∀ i, ∑ ω, p ω * X i ω ^ r = 1) {B : ℝ} (hB1 : 1 ≤ B) (hBd : (d : ℝ) ≤ B) :
    (∏ i, ∑ ω, p ω * X i ω) - B * (1 - ∏ i, ∑ ω, p ω * X i ω)
      ≤ ∑ ω, p ω * ∏ i, X i ω := by
  obtain ⟨m, hm⟩ : ∃ m : Fin d → ℝ, ∀ i, ∑ ω, p ω * X i ω = m i := ⟨_, fun _ => rfl⟩
  simp only [hm]
  have hm0 : ∀ i, 0 ≤ m i := fun i => by
    rw [← hm i]; exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hp ω) (hX i ω))
  have hq1 : ∀ i, ∑ ω, p ω * X i ω ^ 2 ≤ 1 := fun i =>
    conditioning_second_moment_le_one p hp hp1 (X i) (hX i) hr (hnorm i)
  have hm1 : ∀ i, m i ≤ 1 := fun i => by
    rw [← hm i]
    exact conditioning_mean_le_one p hp hp1 (X i) (hX i) (by linarith) (hnorm i).le
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∏ i, m i = M := ⟨_, rfl⟩
  rw [hM]
  have hM0 : 0 ≤ M := by rw [← hM]; exact Finset.prod_nonneg (fun i _ => hm0 i)
  have hM1 : M ≤ 1 := by rw [← hM]; exact Finset.prod_le_one₀ (fun i _ => hm0 i) (fun i _ => hm1 i)
  have hE0 : 0 ≤ ∑ ω, p ω * ∏ i, X i ω :=
    Finset.sum_nonneg (fun ω _ => mul_nonneg (hp ω) (Finset.prod_nonneg (fun i _ => hX i ω)))
  rcases lt_or_ge M (1 / 2) with hsmall | hlarge
  · nlinarith
  have hmpos : ∀ i, 0 < m i := by
    intro i
    rcases (hm0 i).lt_or_eq with h | h
    · exact h
    · exfalso
      have : M = 0 := by rw [← hM]; exact Finset.prod_eq_zero (Finset.mem_univ i) h.symm
      linarith
  -- the normalized variables `Y i = X i / m i`
  have hpt : ∀ ω, 1 + ∑ i, (X i ω / m i - 1) - ((d : ℝ) / 4) * ∑ i, (X i ω / m i - 1) ^ 2
      ≤ ∏ i, (X i ω / m i) := fun ω =>
    conditioning_pointwise (fun i => X i ω / m i) (fun i => div_nonneg (hX i ω) (hm0 i))
  have hmom := fun i => conditioning_normalized_moments p hp1 (X i) (hm i) (hmpos i).ne'
  have hexp : ∑ ω, p ω * (1 + ∑ i, (X i ω / m i - 1)
        - ((d : ℝ) / 4) * ∑ i, (X i ω / m i - 1) ^ 2)
      = 1 + ∑ i, ∑ ω, p ω * (X i ω / m i - 1)
        - ((d : ℝ) / 4) * ∑ i, ∑ ω, p ω * (X i ω / m i - 1) ^ 2 := by
    have h : ∀ ω, p ω * (1 + ∑ i, (X i ω / m i - 1)
        - ((d : ℝ) / 4) * ∑ i, (X i ω / m i - 1) ^ 2)
        = p ω + ∑ i, p ω * (X i ω / m i - 1)
          - ((d : ℝ) / 4) * ∑ i, p ω * (X i ω / m i - 1) ^ 2 := fun ω => by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl (fun ω _ => h ω), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      hp1, ← Finset.mul_sum, Finset.sum_comm (f := fun ω i => p ω * (X i ω / m i - 1)),
      Finset.sum_comm (f := fun ω i => p ω * (X i ω / m i - 1) ^ 2)]
  set S := ∑ i, ((∑ ω, p ω * X i ω ^ 2) / m i ^ 2 - 1) with hS
  have hEY : 1 - ((d : ℝ) / 4) * S ≤ ∑ ω, p ω * ∏ i, (X i ω / m i) := by
    have h1 : 1 - ((d : ℝ) / 4) * S
        = ∑ ω, p ω * (1 + ∑ i, (X i ω / m i - 1)
          - ((d : ℝ) / 4) * ∑ i, (X i ω / m i - 1) ^ 2) := by
      rw [hexp, Finset.sum_congr rfl (fun i _ => (hmom i).1),
        Finset.sum_congr rfl (fun i _ => (hmom i).2), Finset.sum_const_zero, hS]
      ring
    rw [h1]
    exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hp ω))
  have hEXY : ∑ ω, p ω * ∏ i, X i ω = M * ∑ ω, p ω * ∏ i, (X i ω / m i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    have : ∏ i, X i ω = M * ∏ i, (X i ω / m i) := by
      rw [← hM, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      field_simp [(hmpos i).ne']
    rw [this]
    ring
  -- `S ≤ 1/M^2 - 1`
  have hMpos : 0 < M := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / M := ⟨_, rfl⟩
  have huM : u * M = 1 := by rw [hu]; field_simp
  have hu2 : u ≤ 2 := by
    rw [hu, div_le_iff₀ hMpos]; linarith
  have hS1 : S ≤ u ^ 2 - 1 := by
    have h1 : S ≤ ∑ i, (1 / m i ^ 2 - 1) := by
      rw [hS]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have := pow_pos (hmpos i) 2
      have := hq1 i
      gcongr
    have h2 := conditioning_one_add_sum_le_prod Finset.univ (fun i => 1 / m i ^ 2 - 1)
      (fun i _ => by
        have h := hmpos i
        have h' := hm1 i
        rw [sub_nonneg, le_div_iff₀ (by positivity)]
        nlinarith)
    have h3 : ∏ i, (1 + (1 / m i ^ 2 - 1)) = u ^ 2 := by
      rw [Finset.prod_congr rfl (fun i _ => (by ring : 1 + (1 / m i ^ 2 - 1) = 1 / m i ^ 2)),
        Finset.prod_div_distrib, Finset.prod_const_one, Finset.prod_pow, hM, hu]
      ring
    linarith
  have hS0 : 0 ≤ S := by
    rw [hS]
    refine Finset.sum_nonneg (fun i _ => ?_)
    rw [← (hmom i).2]
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hp ω) (sq_nonneg _))
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [hEXY]
  -- `M S ≤ M (u^2 - 1) = u - M ≤ 3 (1 - M)`
  have hMS : M * S ≤ u - M := by
    have : M * S ≤ M * (u ^ 2 - 1) := mul_le_mul_of_nonneg_left hS1 hM0
    nlinarith
  have hu3 : u - M ≤ 3 * (1 - M) := by nlinarith
  have hstep : M * (1 - ((d : ℝ) / 4) * S) ≤ M * ∑ ω, p ω * ∏ i, (X i ω / m i) :=
    mul_le_mul_of_nonneg_left hEY hM0
  nlinarith

/-- `lem:density:conditioning`, first assertion, range `2 ≤ r ≤ 6` with the paper's constant
`B_r = 1280` and `d₀ ≤ 6`: for nonnegative real random variables `X i` (`i : Fin d`,
`d ≤ 6`) on a finite probability space `(Ω, p)` with `E (X i)^r = 1`,
`E ∏ X i ≥ M - 1280 (1 - M)`, `M = ∏ i, E (X i)`. The upper bound `r ≤ 6` is not used. -/
theorem conditioning_collision_bound {Ω : Type*} [Fintype Ω] {d : ℕ} (hd : d ≤ 6)
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : Fin d → Ω → ℝ) (hX : ∀ i ω, 0 ≤ X i ω) {r : ℝ} (hr : 2 ≤ r) (_hr6 : r ≤ 6)
    (hnorm : ∀ i, ∑ ω, p ω * X i ω ^ r = 1) :
    (∏ i, ∑ ω, p ω * X i ω) - 1280 * (1 - ∏ i, ∑ ω, p ω * X i ω)
      ≤ ∑ ω, p ω * ∏ i, X i ω :=
  conditioning_collision_bound_of_two_le p hp hp1 X hX hr hnorm (by norm_num)
    (by have : (d : ℝ) ≤ 6 := by exact_mod_cast hd
        linarith)

end Sarkozy.DensityUpgrade
