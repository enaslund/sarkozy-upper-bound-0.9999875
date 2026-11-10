module

public import Sarkozy.F7Repair.Support

@[expose] public section

/-!
# The one-way repair of a pair law (`lem:tr:repair`(a)–(d),(f), no full support)

`paper/sections/17_completion_repair.tex`, `lem:tr:repair`, parts (a)–(d) and (f), in the
one-way form (d) used by (F7) (`paper/sections/26_upper_comparison.tex`). The data
(`OneWayData ν μX μY`):
* a pair law `ν` on `X × Y` (in (F7), `π^new = λ_p(G^new)` read on its two halves);
* target laws `μX`, `μY` (in (F7), both the old half marginal `μ^old`) with
  `|μX − ν_X| ≤ U ν_X`, `|μY − ν_Y| ≤ U ν_Y` (so `1 + u = dμX/dν_X` has `|u| ≤ U`);
* the centred correlation bound `ρ < 1` of `ν` relative to its own marginals;
* the bound `ν(x, y) ≤ K² ν_X(x) ν_Y(y)`, whence `K_∞ = K` (`lem:tr:repair`(b), "one may take
  `K_∞ = (sup dν/d(ν_X ⊗ ν_Y))^{1/2}`");
* the gate `2F < 1`, `F = U(1 + K/(1 − ρ))`.

No full support of `ν_X`, `ν_Y` is assumed: the equations are solved on the supports
(`Support.lean`) with WP-R's `repair_exists_unique`, and the solution is extended by `0`.

Proved (`OneWayData.f`, `OneWayData.g` are the centred solution):
* `abs_f_le`, `abs_g_le`: `‖f‖_∞, ‖g‖_∞ ≤ F` (`lem:tr:repair`(b),(d));
* `one_add_pos`: `1 + f + g ≥ 1 − 2F > 0` (`lem:tr:repair`(c));
* `marg_fst`, `marg_snd`: `(1 + f + g)ν` has the marginals `μX`, `μY` (`lem:tr:repair`(a));
* `centred`: its centred form relative to `μX`, `μY` has norm at most
  `ρ' = (ρ(1 + 2F) + U²)/(1 − U)` (`lem:tr:repair`(f), case (d));
* `invariant`: `f`, `g` are invariant under every pair of bijections preserving `ν`, `μX`, `μY`
  (`lem:tr:repair`(a), last claim).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.Recentering Sarkozy.Structured

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- **The centred correlation bound**: `|E_ν[h(x)k(y)]| ≤ ρ ‖h‖_{μX} ‖k‖_{μY}` for `μX`-centred `h`
and `μY`-centred `k`. -/
def CentredBound (ν : FiniteLaw (X × Y)) (μX : FiniteLaw X) (μY : FiniteLaw Y) (ρ : ℝ) : Prop :=
  ∀ h k, μX.expect h = 0 → μY.expect k = 0 →
    |ν.expect (fun p => h p.1 * k p.2)| ≤ ρ * nrm μX h * nrm μY k

/-- **Weighted Cauchy–Schwarz**: if `0 ≤ w ≤ c m` with `m > 0` and `∑ w = M`, then
`|∑ w k| ≤ √(cM) (∑ m k²)^{1/2}`. -/
theorem cs_weighted {ι : Type*} [Fintype ι] (w m k : ι → ℝ) {c M : ℝ} (hm : ∀ i, 0 < m i)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ i, w i ≤ c * m i) (hsum : ∑ i, w i = M) :
    |∑ i, w i * k i| ≤ Real.sqrt (c * M) * Real.sqrt (∑ i, m i * (k i * k i)) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => w i / Real.sqrt (m i))
    (fun i => Real.sqrt (m i) * k i)
  have e1 : ∀ i, w i / Real.sqrt (m i) * (Real.sqrt (m i) * k i) = w i * k i := by
    intro i
    have := Real.sqrt_pos.mpr (hm i)
    field_simp
  have e2 : ∀ i, (w i / Real.sqrt (m i)) ^ 2 = w i ^ 2 / m i := by
    intro i
    rw [div_pow, Real.sq_sqrt (hm i).le]
  have e3 : ∀ i, (Real.sqrt (m i) * k i) ^ 2 = m i * (k i * k i) := by
    intro i
    rw [mul_pow, Real.sq_sqrt (hm i).le]
    ring
  simp only [e1, e2, e3] at hcs
  have h4 : ∑ i, w i ^ 2 / m i ≤ c * M := by
    rw [← hsum, mul_sum]
    refine sum_le_sum fun i _ => ?_
    rw [div_le_iff₀ (hm i)]
    nlinarith [hw i, hw0 i]
  have hB : 0 ≤ ∑ i, m i * (k i * k i) :=
    sum_nonneg fun i _ => mul_nonneg (hm i).le (mul_self_nonneg _)
  calc |∑ i, w i * k i| ≤ Real.sqrt ((∑ i, w i ^ 2 / m i) * ∑ i, m i * (k i * k i)) :=
        Real.abs_le_sqrt hcs
    _ ≤ Real.sqrt ((c * M) * ∑ i, m i * (k i * k i)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h4 hB)
    _ = _ := Real.sqrt_mul' _ hB

/-- **The data of a one-way repair** (`lem:tr:repair`(d), (F7)). *All fields are hypotheses*; in
(F7) they are the density, correlation and `L^∞` bounds of `π^new` and the gate `2F < 1`. -/
structure OneWayData (ν : FiniteLaw (X × Y)) (μX : FiniteLaw X) (μY : FiniteLaw Y) where
  /-- The density deviation `U` (`U = e^{ℓ_U} − 1` in (F7)). -/
  U : ℝ
  /-- The centred correlation `ρ` of `ν` (`ρ_new` in (F7)). -/
  ρ : ℝ
  /-- The `L² → L^∞` constant `K_∞`. -/
  K : ℝ
  U_nonneg : 0 ≤ U
  ρ_nonneg : 0 ≤ ρ
  ρ_lt_one : ρ < 1
  K_nonneg : 0 ≤ K
  /-- The gate `2F < 1` of `lem:tr:repair`(d). -/
  twoF_lt : 2 * (U * (1 + K / (1 - ρ))) < 1
  /-- `|dμX/dν_X − 1| ≤ U`. -/
  dens_X : ∀ x, |μX.weight x - mX ν x| ≤ U * mX ν x
  /-- `|dμY/dν_Y − 1| ≤ U`. -/
  dens_Y : ∀ y, |μY.weight y - mY ν y| ≤ U * mY ν y
  /-- The centred correlation of `ν` relative to its marginals is at most `ρ`. -/
  corr : CentredBound ν (margX ν) (margY ν) ρ
  /-- `dν/d(ν_X ⊗ ν_Y) ≤ K²`. -/
  sup : ∀ x y, ν.weight (x, y) ≤ K ^ 2 * mX ν x * mY ν y

/-- The target density `u = dμX/dν_X − 1` on the support. -/
noncomputable def tu (ν : FiniteLaw (X × Y)) (μX : FiniteLaw X) (x : SX ν) : ℝ :=
  μX.weight x.1 / mX ν x.1 - 1

/-- The target density `v = dμY/dν_Y − 1` on the support. -/
noncomputable def tv (ν : FiniteLaw (X × Y)) (μY : FiniteLaw Y) (y : SY ν) : ℝ :=
  μY.weight y.1 / mY ν y.1 - 1

theorem ip_self_nonneg {Z : Type*} [Fintype Z] (μ : FiniteLaw Z) (h : Z → ℝ) : 0 ≤ ip μ h h :=
  μ.expect_nonneg fun _ => mul_self_nonneg _

namespace OneWayData

variable {ν : FiniteLaw (X × Y)} {μX : FiniteLaw X} {μY : FiniteLaw Y} (D : OneWayData ν μX μY)

include D

/-- `F = U(1 + K_∞/(1 − ρ))` (`lem:tr:repair`(d)). -/
noncomputable def F : ℝ := D.U * (1 + D.K / (1 - D.ρ))

/-- `ρ' = (ρ(1 + 2F) + U²)/(1 − U)` (`lem:tr:repair`(f), case (d)). -/
noncomputable def ρ' : ℝ := (D.ρ * (1 + 2 * D.F) + D.U ^ 2) / (1 - D.U)

theorem one_sub_ρ_pos : 0 < 1 - D.ρ := by linarith [D.ρ_lt_one]

theorem F_nonneg : 0 ≤ D.F :=
  mul_nonneg D.U_nonneg (by have := div_nonneg D.K_nonneg D.one_sub_ρ_pos.le; linarith)

theorem U_le_F : D.U ≤ D.F := by
  unfold F
  have := div_nonneg D.K_nonneg D.one_sub_ρ_pos.le
  nlinarith [D.U_nonneg]

theorem twoF_lt' : 2 * D.F < 1 := D.twoF_lt

theorem U_lt_one : D.U < 1 := by linarith [D.U_le_F, D.twoF_lt', D.F_nonneg]

theorem ρ'_nonneg : 0 ≤ D.ρ' := by
  unfold ρ'
  apply div_nonneg _ (by linarith [D.U_lt_one])
  have := mul_nonneg D.ρ_nonneg (by linarith [D.F_nonneg] : (0 : ℝ) ≤ 1 + 2 * D.F)
  nlinarith [sq_nonneg D.U]

theorem μX_zero {x : X} (h : mX ν x = 0) : μX.weight x = 0 := by
  have := D.dens_X x
  rw [h, mul_zero, sub_zero] at this
  exact abs_nonpos_iff.mp this

theorem μY_zero {y : Y} (h : mY ν y = 0) : μY.weight y = 0 := by
  have := D.dens_Y y
  rw [h, mul_zero, sub_zero] at this
  exact abs_nonpos_iff.mp this

theorem abs_u_le (x : SX ν) : |(tu ν μX) x| ≤ D.U := by
  have hm : 0 < mX ν x.1 := resX_pos ν x
  unfold tu
  rw [show μX.weight x.1 / mX ν x.1 - 1 = (μX.weight x.1 - mX ν x.1) / mX ν x.1 by
    field_simp, abs_div, abs_of_pos hm, div_le_iff₀ hm]
  exact D.dens_X x.1

theorem abs_v_le (y : SY ν) : |(tv ν μY) y| ≤ D.U := by
  have hm : 0 < mY ν y.1 := resY_pos ν y
  unfold tv
  rw [show μY.weight y.1 / mY ν y.1 - 1 = (μY.weight y.1 - mY ν y.1) / mY ν y.1 by
    field_simp, abs_div, abs_of_pos hm, div_le_iff₀ hm]
  exact D.dens_Y y.1

/-- `E_{ν_X}[(1 + u)F] = E_{μX} F`. -/
theorem resX_one_add_u (G : X → ℝ) :
    (resX ν).expect (fun x => (1 + (tu ν μX) x) * G x.1) = μX.expect G := by
  unfold FiniteLaw.expect
  rw [← sum_SX ν (fun x => μX.weight x * G x) (fun x h => by rw [D.μX_zero h, zero_mul])]
  refine sum_congr rfl fun x _ => ?_
  show mX ν x.1 * ((1 + (μX.weight x.1 / mX ν x.1 - 1)) * G x.1) = μX.weight x.1 * G x.1
  have hx : mX ν x.1 ≠ 0 := x.2
  field_simp
  ring

/-- `E_{ν_Y}[(1 + v)F] = E_{μY} F`. -/
theorem resY_one_add_v (G : Y → ℝ) :
    (resY ν).expect (fun y => (1 + (tv ν μY) y) * G y.1) = μY.expect G := by
  unfold FiniteLaw.expect
  rw [← sum_SY ν (fun y => μY.weight y * G y) (fun y h => by rw [D.μY_zero h, zero_mul])]
  refine sum_congr rfl fun y _ => ?_
  show mY ν y.1 * ((1 + (μY.weight y.1 / mY ν y.1 - 1)) * G y.1) = μY.weight y.1 * G y.1
  have hy : mY ν y.1 ≠ 0 := y.2
  field_simp
  ring

theorem expect_u : (resX ν).expect (tu ν μX) = 0 := by
  have h := D.resX_one_add_u (fun _ => 1)
  simp only [mul_one, FiniteLaw.expect_const] at h
  have e : (resX ν).expect (fun x => 1 + (tu ν μX) x) = 1 + (resX ν).expect (tu ν μX) := by
    rw [FiniteLaw.expect_add, FiniteLaw.expect_const]
  linarith

theorem expect_v : (resY ν).expect (tv ν μY) = 0 := by
  have h := D.resY_one_add_v (fun _ => 1)
  simp only [mul_one, FiniteLaw.expect_const] at h
  have e : (resY ν).expect (fun y => 1 + (tv ν μY) y) = 1 + (resY ν).expect (tv ν μY) := by
    rw [FiniteLaw.expect_add, FiniteLaw.expect_const]
  linarith

/-- `‖A k‖ ≤ ρ ‖k‖` on centred `k`, on the supports. -/
theorem hAρ (k : SY ν → ℝ) (hk : (resY ν).expect k = 0) :
    nrm (resX ν) (condA ν k) ≤ D.ρ * nrm (resY ν) k := by
  set H := condA ν k with hHdef
  have hH0 : (resX ν).expect H = 0 := by
    have h1 := resP_condA ν (fun _ => 1) k
    unfold ip at h1
    simp only [one_mul] at h1
    rw [resP_snd, hk] at h1
    exact h1.symm
  have key := D.corr (extX ν H) (extY ν k) (by rw [margX_expect_extX]; exact hH0)
    (by rw [margY_expect_extY]; exact hk)
  rw [nrm_margX_extX, nrm_margY_extY] at key
  have e : ν.expect (fun p => extX ν H p.1 * extY ν k p.2) = nrm (resX ν) H ^ 2 := by
    rw [← resP_expect ν (fun p => extX ν H p.1 * extY ν k p.2)]
    simp only [extX_val, extY_val]
    rw [resP_condA]
    unfold nrm
    rw [Real.sq_sqrt (ip_self_nonneg _ _)]
  rw [e, abs_of_nonneg (sq_nonneg _)] at key
  rcases eq_or_lt_of_le (Real.sqrt_nonneg _ : 0 ≤ nrm (resX ν) H) with h0 | hpos
  · rw [show nrm (resX ν) H = 0 from h0.symm]
    exact mul_nonneg D.ρ_nonneg (Real.sqrt_nonneg _)
  · have key' : nrm (resX ν) H * nrm (resX ν) H ≤ (D.ρ * nrm (resY ν) k) * nrm (resX ν) H := by
      nlinarith [key]
    exact le_of_mul_le_mul_right key' hpos

/-- `‖A* h‖ ≤ ρ ‖h‖` on centred `h`, on the supports. -/
theorem hBρ (h : SX ν → ℝ) (hh : (resX ν).expect h = 0) :
    nrm (resY ν) (condB ν h) ≤ D.ρ * nrm (resX ν) h := by
  set H := condB ν h with hHdef
  have hH0 : (resY ν).expect H = 0 := by
    have h1 := resP_condB ν h (fun _ => 1)
    unfold ip at h1
    simp only [mul_one] at h1
    rw [resP_fst, hh] at h1
    exact h1.symm
  have key := D.corr (extX ν h) (extY ν H) (by rw [margX_expect_extX]; exact hh)
    (by rw [margY_expect_extY]; exact hH0)
  rw [nrm_margX_extX, nrm_margY_extY] at key
  have e : ν.expect (fun p => extX ν h p.1 * extY ν H p.2) = nrm (resY ν) H ^ 2 := by
    rw [← resP_expect ν (fun p => extX ν h p.1 * extY ν H p.2)]
    simp only [extX_val, extY_val]
    rw [resP_condB]
    unfold nrm
    rw [Real.sq_sqrt (ip_self_nonneg _ _)]
  rw [e, abs_of_nonneg (sq_nonneg _)] at key
  rcases eq_or_lt_of_le (Real.sqrt_nonneg _ : 0 ≤ nrm (resY ν) H) with h0 | hpos
  · rw [show nrm (resY ν) H = 0 from h0.symm]
    exact mul_nonneg D.ρ_nonneg (Real.sqrt_nonneg _)
  · have key' : nrm (resY ν) H * nrm (resY ν) H ≤ (D.ρ * nrm (resX ν) h) * nrm (resY ν) H := by
      nlinarith [key]
    exact le_of_mul_le_mul_right key' hpos

/-- `|A k| ≤ K ‖k‖` (`lem:tr:repair`(b), `K_∞ = (sup dν/d(ν_X ⊗ ν_Y))^{1/2}`). -/
theorem hAK (k : SY ν → ℝ) (x : SX ν) : |condA ν k x| ≤ D.K * nrm (resY ν) k := by
  have hx : 0 < mX ν x.1 := resX_pos ν x
  have hcs := cs_weighted (fun y : SY ν => ν.weight (x.1, y.1)) (fun y => mY ν y.1) k
    (c := D.K ^ 2 * mX ν x.1) (M := mX ν x.1) (fun y => resY_pos ν y) (fun _ => ν.nonneg _)
    (fun y => D.sup x.1 y.1) (sum_SY_weight ν x.1)
  have hs : Real.sqrt (D.K ^ 2 * mX ν x.1 * mX ν x.1) = D.K * mX ν x.1 := by
    rw [show D.K ^ 2 * mX ν x.1 * mX ν x.1 = (D.K * mX ν x.1) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg D.K_nonneg hx.le)
  rw [hs] at hcs
  rw [condA_apply, abs_div, abs_of_pos hx, div_le_iff₀ hx]
  have hn : nrm (resY ν) k = Real.sqrt (∑ y : SY ν, mY ν y.1 * (k y * k y)) := rfl
  rw [hn]
  linarith [hcs]

/-- `|A* h| ≤ K ‖h‖`. -/
theorem hBK (h : SX ν → ℝ) (y : SY ν) : |condB ν h y| ≤ D.K * nrm (resX ν) h := by
  have hy : 0 < mY ν y.1 := resY_pos ν y
  have hcs := cs_weighted (fun x : SX ν => ν.weight (x.1, y.1)) (fun x => mX ν x.1) h
    (c := D.K ^ 2 * mY ν y.1) (M := mY ν y.1) (fun x => resX_pos ν x) (fun _ => ν.nonneg _)
    (fun x => by have := D.sup x.1 y.1; linarith) (sum_SX_weight ν y.1)
  have hs : Real.sqrt (D.K ^ 2 * mY ν y.1 * mY ν y.1) = D.K * mY ν y.1 := by
    rw [show D.K ^ 2 * mY ν y.1 * mY ν y.1 = (D.K * mY ν y.1) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg D.K_nonneg hy.le)
  rw [hs] at hcs
  rw [condB_apply, abs_div, abs_of_pos hy, div_le_iff₀ hy]
  have hn : nrm (resX ν) h = Real.sqrt (∑ x : SX ν, mX ν x.1 * (h x * h x)) := rfl
  rw [hn]
  linarith [hcs]

/-- **Existence of the centred solution on the supports** (`lem:tr:repair`(a)). -/
theorem exists_sol : ∃ f : SX ν → ℝ, ∃ g : SY ν → ℝ, (resX ν).expect f = 0 ∧
    (resY ν).expect g = 0 ∧ (∀ x, f x + condA ν g x = (tu ν μX) x) ∧
      (∀ y, g y + condB ν f y = (tv ν μY) y) :=
  (repair_exists_unique (resP ν) (resX ν) (resY ν) (resP_fst ν) (resP_snd ν) (resX_pos ν)
    (resY_pos ν) (condA ν) (condB ν) (resP_condA ν) (resP_condB ν) D.ρ_nonneg D.ρ_lt_one
    D.hAρ D.hBρ (tu ν μX) (tv ν μY) D.expect_u D.expect_v).1

/-- The solution `f` on the support. -/
noncomputable def f' : SX ν → ℝ := Classical.choose D.exists_sol

/-- The solution `g` on the support. -/
noncomputable def g' : SY ν → ℝ := Classical.choose (Classical.choose_spec D.exists_sol)

theorem spec' : (resX ν).expect D.f' = 0 ∧ (resY ν).expect D.g' = 0 ∧
    (∀ x, D.f' x + condA ν D.g' x = (tu ν μX) x) ∧ (∀ y, D.g' y + condB ν D.f' y = (tv ν μY) y) :=
  Classical.choose_spec (Classical.choose_spec D.exists_sol)

/-- **The repair function `f`** (extended by `0` off the support). -/
noncomputable def f : X → ℝ := extX ν D.f'

/-- **The repair function `g`** (extended by `0` off the support). -/
noncomputable def g : Y → ℝ := extY ν D.g'

theorem norms' : nrm (resX ν) D.f' ≤ D.U / (1 - D.ρ) ∧ nrm (resY ν) D.g' ≤ D.U / (1 - D.ρ) := by
  obtain ⟨hf0, hg0, hfu, hgv⟩ := D.spec'
  exact repair_one_way (resX ν) (resY ν) (condA ν) (condB ν) D.ρ_nonneg D.ρ_lt_one D.hAρ D.hBρ
    D.f' D.g' (tu ν μX) (tv ν μY) hf0 hg0 hfu hgv D.U_nonneg D.abs_u_le D.abs_v_le

theorem abs_f'_le (x : SX ν) : |D.f' x| ≤ D.F := by
  obtain ⟨_, _, hfu, _⟩ := D.spec'
  calc |D.f' x| ≤ D.U + D.K * nrm (resY ν) D.g' :=
        repair_sup_bounds (resY ν) (condA ν) D.hAK D.f' D.g' (tu ν μX) hfu D.abs_u_le x
    _ ≤ D.U + D.K * (D.U / (1 - D.ρ)) := by
        have := mul_le_mul_of_nonneg_left D.norms'.2 D.K_nonneg
        linarith
    _ = D.F := by unfold F; ring

theorem abs_g'_le (y : SY ν) : |D.g' y| ≤ D.F := by
  obtain ⟨_, _, _, hgv⟩ := D.spec'
  calc |D.g' y| ≤ D.U + D.K * nrm (resX ν) D.f' :=
        repair_sup_bounds (resX ν) (condB ν) D.hBK D.g' D.f' (tv ν μY) hgv D.abs_v_le y
    _ ≤ D.U + D.K * (D.U / (1 - D.ρ)) := by
        have := mul_le_mul_of_nonneg_left D.norms'.1 D.K_nonneg
        linarith
    _ = D.F := by unfold F; ring

/-- **`‖f‖_∞ ≤ F`** (`lem:tr:repair`(b),(d)). -/
theorem abs_f_le (x : X) : |D.f x| ≤ D.F := by
  unfold f extX
  split_ifs with h
  · exact D.abs_f'_le _
  · simp only [abs_zero]
    exact D.F_nonneg

/-- **`‖g‖_∞ ≤ F`** (`lem:tr:repair`(b),(d)). -/
theorem abs_g_le (y : Y) : |D.g y| ≤ D.F := by
  unfold g extY
  split_ifs with h
  · exact D.abs_g'_le _
  · simp only [abs_zero]
    exact D.F_nonneg

/-- **Positivity** (`lem:tr:repair`(c)): `1 + f + g ≥ 1 − 2F > 0`. -/
theorem one_add_pos (x : X) (y : Y) : 0 < 1 + D.f x + D.g y := by
  have h1 := abs_le.mp (D.abs_f_le x)
  have h2 := abs_le.mp (D.abs_g_le y)
  linarith [D.twoF_lt']

/-- A `ν`-expectation of the reweighted law is the restricted reweight form. -/
theorem expect_reweight (G : X × Y → ℝ) :
    ν.expect (fun p => (1 + D.f p.1 + D.g p.2) * G p) =
      (resP ν).expect (fun p => (1 + D.f' p.1 + D.g' p.2) * G (p.1.1, p.2.1)) := by
  rw [← resP_expect ν (fun p => (1 + D.f p.1 + D.g p.2) * G p)]
  simp only [f, g, extX_val, extY_val]

/-- **The first marginal of `(1 + f + g)ν` is `μX`** (`lem:tr:repair`(a)). -/
theorem marg_fst (φ : X → ℝ) :
    ν.expect (fun p => (1 + D.f p.1 + D.g p.2) * φ p.1) = μX.expect φ := by
  obtain ⟨_, _, hfu, hgv⟩ := D.spec'
  have hm := (repair_marginals (resP ν) (resX ν) (resY ν) (resP_fst ν) (resP_snd ν) (condA ν)
    (condB ν) (resP_condA ν) (resP_condB ν) D.f' D.g' (tu ν μX) (tv ν μY) hfu hgv).1 (fun x => φ x.1)
  rw [reweightForm_apply] at hm
  simp only [mul_one] at hm
  rw [D.expect_reweight (fun p => φ p.1), hm, ← D.resX_one_add_u φ]
  unfold ip
  exact (resX ν).expect_congr fun x => by ring

/-- **The second marginal of `(1 + f + g)ν` is `μY`** (`lem:tr:repair`(a)). -/
theorem marg_snd (φ : Y → ℝ) :
    ν.expect (fun p => (1 + D.f p.1 + D.g p.2) * φ p.2) = μY.expect φ := by
  obtain ⟨_, _, hfu, hgv⟩ := D.spec'
  have hm := (repair_marginals (resP ν) (resX ν) (resY ν) (resP_fst ν) (resP_snd ν) (condA ν)
    (condB ν) (resP_condA ν) (resP_condB ν) D.f' D.g' (tu ν μX) (tv ν μY) hfu hgv).2 (fun y => φ y.1)
  rw [reweightForm_apply] at hm
  simp only [one_mul] at hm
  rw [D.expect_reweight (fun p => φ p.2), hm, ← D.resY_one_add_v φ]
  unfold ip
  rfl

/-- **The centred norm of the repaired law** (`lem:tr:repair`(f), case (d)):
`|E_{(1+f+g)ν}[h k]| ≤ ρ' ‖h‖_{μX} ‖k‖_{μY}` for centred `h`, `k`, with
`ρ' = (ρ(1 + 2F) + U²)/(1 − U)`. -/
theorem centred (h : X → ℝ) (k : Y → ℝ) (hh : μX.expect h = 0) (hk : μY.expect k = 0) :
    |ν.expect (fun p => (1 + D.f p.1 + D.g p.2) * (h p.1 * k p.2))| ≤
      D.ρ' * nrm μX h * nrm μY k := by
  obtain ⟨hf0, hg0, hfu, hgv⟩ := D.spec'
  have he : nrm (resX ν) (tu ν μX) * nrm (resY ν) (tv ν μY) ≤ D.U * D.U :=
    mul_le_mul (nrm_le_of_abs_le _ _ D.U_nonneg D.abs_u_le)
      (nrm_le_of_abs_le _ _ D.U_nonneg D.abs_v_le) (Real.sqrt_nonneg _) D.U_nonneg
  have hh' : ip (resX ν) (fun x => h x.1) (fun x => 1 + (tu ν μX) x) = 0 := by
    have e := D.resX_one_add_u h
    rw [hh] at e
    unfold ip
    refine ((resX ν).expect_congr fun x => ?_).trans e
    simp only
    ring
  have hk' : ip (resY ν) (fun y => 1 + (tv ν μY) y) (fun y => k y.1) = 0 := by
    have e := D.resY_one_add_v k
    rw [hk] at e
    unfold ip
    exact ((resY ν).expect_congr fun y => rfl).trans e
  have key := repair_centred_norm (resP ν) (resX ν) (resY ν) (resP_fst ν) (resP_snd ν) (condA ν)
    (condB ν) (resP_condA ν) (resP_condB ν) D.ρ_nonneg D.hAρ D.hBρ D.f' D.g' (tu ν μX) (tv ν μY) hf0 hg0
    hfu hgv D.U_lt_one D.U_lt_one (fun x => (abs_le.mp (D.abs_u_le x)).1)
    (fun y => (abs_le.mp (D.abs_v_le y)).1) he D.F_nonneg D.F_nonneg D.abs_f'_le D.abs_g'_le
    (fun x => h x.1) (fun y => k y.1) hh' hk'
  rw [reweightForm_apply] at key
  have hX : (resX ν).expect (fun x => (1 + (tu ν μX) x) * h x.1 ^ 2) = ip μX h h := by
    unfold ip
    rw [← D.resX_one_add_u (fun x => h x * h x)]
    exact (resX ν).expect_congr fun x => by ring
  have hY : (resY ν).expect (fun y => (1 + (tv ν μY) y) * k y.1 ^ 2) = ip μY k k := by
    unfold ip
    rw [← D.resY_one_add_v (fun y => k y * k y)]
    exact (resY ν).expect_congr fun y => by ring
  rw [hX, hY] at key
  have hU : Real.sqrt ((1 - D.U) * (1 - D.U)) = 1 - D.U :=
    Real.sqrt_mul_self (by linarith [D.U_lt_one])
  rw [hU] at key
  rw [D.expect_reweight (fun p => h p.1 * k p.2)]
  have hc : (D.ρ * (1 + D.F + D.F) + D.U * D.U) / (1 - D.U) = D.ρ' := by
    unfold ρ'
    ring
  rw [hc] at key
  exact key

omit D in
/-- The marginal weight is invariant under a bijection preserving `ν`. -/
theorem mX_inv (σX : X ≃ X) (σY : Y ≃ Y)
    (hν : ∀ x y, ν.weight (σX x, σY y) = ν.weight (x, y)) (x : X) : mX ν (σX x) = mX ν x := by
  unfold mX
  rw [← Equiv.sum_comp σY (fun y => ν.weight (σX x, y))]
  exact sum_congr rfl fun y _ => hν x y

omit D in
theorem mY_inv (σX : X ≃ X) (σY : Y ≃ Y)
    (hν : ∀ x y, ν.weight (σX x, σY y) = ν.weight (x, y)) (y : Y) : mY ν (σY y) = mY ν y := by
  unfold mY
  rw [← Equiv.sum_comp σX (fun x => ν.weight (x, σY y))]
  exact sum_congr rfl fun x _ => hν x y

/-- **Invariance** (`lem:tr:repair`(a), last claim): if `(x, y) ↦ (σX x, σY y)` preserves `ν`,
and `σX`, `σY` preserve `μX`, `μY`, then `f ∘ σX = f` and `g ∘ σY = g`. -/
theorem invariant (σX : X ≃ X) (σY : Y ≃ Y)
    (hν : ∀ x y, ν.weight (σX x, σY y) = ν.weight (x, y))
    (hμX : ∀ x, μX.weight (σX x) = μX.weight x) (hμY : ∀ y, μY.weight (σY y) = μY.weight y) :
    (∀ x, D.f (σX x) = D.f x) ∧ (∀ y, D.g (σY y) = D.g y) := by
  obtain ⟨hf0, hg0, hfu, hgv⟩ := D.spec'
  have hmx := mX_inv σX σY hν
  have hmy := mY_inv σX σY hν
  let σX' : SX ν ≃ SX ν := σX.subtypeEquiv (fun x => by rw [hmx x])
  let σY' : SY ν ≃ SY ν := σY.subtypeEquiv (fun y => by rw [hmy y])
  have hν' : ∀ G : SX ν × SY ν → ℝ,
      (resP ν).expect (fun p => G (σX' p.1, σY' p.2)) = (resP ν).expect G := by
    intro G
    unfold FiniteLaw.expect
    rw [← Equiv.sum_comp (σX'.prodCongr σY') (fun p => (resP ν).weight p * G p)]
    refine sum_congr rfl fun p _ => ?_
    show ν.weight (p.1.1, p.2.1) * G (σX' p.1, σY' p.2) =
      ν.weight (σX p.1.1, σY p.2.1) * G (σX' p.1, σY' p.2)
    rw [hν]
  have hu' : ∀ x, (tu ν μX) (σX' x) = (tu ν μX) x := by
    intro x
    show μX.weight (σX x.1) / mX ν (σX x.1) - 1 = μX.weight x.1 / mX ν x.1 - 1
    rw [hμX, hmx]
  have hv' : ∀ y, (tv ν μY) (σY' y) = (tv ν μY) y := by
    intro y
    show μY.weight (σY y.1) / mY ν (σY y.1) - 1 = μY.weight y.1 / mY ν y.1 - 1
    rw [hμY, hmy]
  obtain ⟨hfi, hgi, _⟩ := repair_invariant (resP ν) (resX ν) (resY ν) (resP_fst ν) (resP_snd ν)
    (resX_pos ν) (resY_pos ν) (condA ν) (condB ν) (resP_condA ν) (resP_condB ν) D.ρ_nonneg
    D.ρ_lt_one D.hAρ D.hBρ (tu ν μX) (tv ν μY) D.f' D.g' hf0 hg0 hfu hgv σX' σY' hν' hu' hv'
  constructor
  · intro x
    by_cases h : mX ν x = 0
    · have h' : mX ν (σX x) = 0 := by rw [hmx]; exact h
      unfold f
      rw [extX_zero ν _ h, extX_zero ν _ h']
    · unfold f
      have e1 : extX ν D.f' (σX x) = D.f' (σX' ⟨x, h⟩) := extX_val ν D.f' (σX' ⟨x, h⟩)
      have e2 : extX ν D.f' x = D.f' ⟨x, h⟩ := extX_val ν D.f' ⟨x, h⟩
      rw [e1, e2]
      exact hfi ⟨x, h⟩
  · intro y
    by_cases h : mY ν y = 0
    · have h' : mY ν (σY y) = 0 := by rw [hmy]; exact h
      unfold g
      rw [extY_zero ν _ h, extY_zero ν _ h']
    · unfold g
      have e1 : extY ν D.g' (σY y) = D.g' (σY' ⟨y, h⟩) := extY_val ν D.g' (σY' ⟨y, h⟩)
      have e2 : extY ν D.g' y = D.g' ⟨y, h⟩ := extY_val ν D.g' ⟨y, h⟩
      rw [e1, e2]
      exact hgi ⟨y, h⟩

end OneWayData

end Sarkozy.F7Repair
