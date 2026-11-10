module

public import Sarkozy.SignedComponents.Fold

@[expose] public section

/-!
# The marginal repair of a positive kernel (`cor:markov-completion`, generic form)

`paper/sections/21_middle_records.tex`, `lem:signed-components`(c),(d), which applies
`cor:markov-completion` with `m_X = m_Y = m₀`, `R = R_{uv}`, `J = J_C`, `M = M_c`.

On a finite set `A` with a law `m`, take a nonnegative weight `W` on `A × A` of positive mass `Z`,
charging only pairs in the support of `m ⊗ m`, and a nonnegative density `J` relative to
`m ⊗ m` with both marginals `m` (`J_row`, `J_col`). With the marginal defects
`α(x) = 1 - a(x)/m(x)`, `β(y) = 1 - b(y)/m(y)` of `W/Z` (`a`, `b` its marginals), and
`J β = 0`, `J* α = 0` (`hJβ`, `hJα`), the measure

  `μ(x, y) = (W(x, y)/Z + J(x, y) (α(x) + β(y) + 2M) m(x) m(y)) / (1 + 2M)`

(the density `P = (R + J(α ⊕ β) + 2MJ)/(1 + 2M)` of `lem:signed-components`(d) relative to
`m ⊗ m`, with `R = W/(Z m ⊗ m)`) is, for every `M ≥ 0` with `|α|, |β| ≤ M` on the support of
`m`:
* nonnegative (`repair_nonneg`), with both marginals `m` (`repair_row`, `repair_col`) and mass
  one (`repair_total`): **`repairLaw`**;
* supported where `W` or `J` is (`repair_support`).

The paper takes `M = M_c` and proves `|α|, |β| ≤ M_c` (`lem:signed-components`(c)); here `M` is a
parameter and the bound a hypothesis.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedComponents

variable {A : Type} [Fintype A] [DecidableEq A]

/-- **The data of the marginal repair**: a law `m`, a nonnegative weight `W` of positive mass on
the support of `m ⊗ m`, and a nonnegative coupling density `J` relative to `m ⊗ m` with both
marginals `m`. -/
structure RepairInput (A : Type) [Fintype A] [DecidableEq A] where
  m : FiniteLaw A
  W : A × A → ℝ
  W_nonneg : ∀ p, 0 ≤ W p
  W_pos : 0 < ∑ p, W p
  W_supp : ∀ x y, W (x, y) ≠ 0 → 0 < m.weight x ∧ 0 < m.weight y
  J : A × A → ℝ
  J_nonneg : ∀ p, 0 ≤ J p
  J_row : ∀ x, ∑ y, J (x, y) * m.weight y = 1
  J_col : ∀ y, ∑ x, J (x, y) * m.weight x = 1

namespace RepairInput

variable (R : RepairInput A)

/-- The mass `Z = ∑ W`. -/
noncomputable def Z : ℝ := ∑ p, R.W p

/-- The row marginal `a(x) = ∑_y W(x, y)/Z`. -/
noncomputable def a (x : A) : ℝ := ∑ y, R.W (x, y) / R.Z

/-- The column marginal `b(y) = ∑_x W(x, y)/Z`. -/
noncomputable def b (y : A) : ℝ := ∑ x, R.W (x, y) / R.Z

/-- The row defect `α(x) = 1 - a(x)/m(x)` (`α = 1 - R1`). -/
noncomputable def α (x : A) : ℝ := 1 - R.a x / R.m.weight x

/-- The column defect `β(y) = 1 - b(y)/m(y)` (`β = 1 - R*1`). -/
noncomputable def β (y : A) : ℝ := 1 - R.b y / R.m.weight y

theorem a_eq_zero {x : A} (hx : R.m.weight x = 0) : R.a x = 0 := by
  unfold a
  refine sum_eq_zero fun y _ => ?_
  by_cases hW : R.W (x, y) = 0
  · rw [hW, zero_div]
  · exact absurd hx (R.W_supp x y hW).1.ne'

theorem b_eq_zero {y : A} (hy : R.m.weight y = 0) : R.b y = 0 := by
  unfold b
  refine sum_eq_zero fun x _ => ?_
  by_cases hW : R.W (x, y) = 0
  · rw [hW, zero_div]
  · exact absurd hy (R.W_supp x y hW).2.ne'

/-- `m α = m - a` everywhere. -/
theorem m_mul_α (x : A) : R.m.weight x * R.α x = R.m.weight x - R.a x := by
  rcases (R.m.nonneg x).lt_or_eq with hx | hx
  · unfold α
    field_simp
  · rw [← hx, R.a_eq_zero hx.symm]
    ring

/-- `m β = m - b` everywhere. -/
theorem m_mul_β (y : A) : R.m.weight y * R.β y = R.m.weight y - R.b y := by
  rcases (R.m.nonneg y).lt_or_eq with hy | hy
  · unfold β
    field_simp
  · rw [← hy, R.b_eq_zero hy.symm]
    ring

theorem sum_a : ∑ x, R.a x = 1 := by
  have hZ : R.Z ≠ 0 := R.W_pos.ne'
  unfold a
  rw [← sum_div_sum_eq_sum_div R]
  exact div_self hZ
where
  sum_div_sum_eq_sum_div (R : RepairInput A) :
      (∑ p, R.W p) / R.Z = ∑ x, ∑ y, R.W (x, y) / R.Z := by
    rw [Fintype.sum_prod_type, sum_div]
    exact sum_congr rfl fun x _ => by rw [sum_div]

theorem sum_b : ∑ y, R.b y = 1 := by
  have hZ : R.Z ≠ 0 := R.W_pos.ne'
  unfold b
  rw [sum_comm, ← sum_a.sum_div_sum_eq_sum_div R]
  exact div_self hZ

/-- **The repaired weight** `μ(x, y) = (W/Z + J (α(x) + β(y) + 2M) m(x) m(y))/(1 + 2M)`. -/
noncomputable def repair (M : ℝ) (p : A × A) : ℝ :=
  (R.W p / R.Z + R.J p * (R.α p.1 + R.β p.2 + 2 * M) * R.m.weight p.1 * R.m.weight p.2) /
    (1 + 2 * M)

/-- The bound `|α|, |β| ≤ M` on the support of `m` (`lem:signed-components`(c) with `M = M_c`). -/
def DefectBound (M : ℝ) : Prop :=
  ∀ x, 0 < R.m.weight x → |R.α x| ≤ M ∧ |R.β x| ≤ M

theorem repair_nonneg {M : ℝ} (hM0 : 0 ≤ M) (hM : R.DefectBound M) (p : A × A) :
    0 ≤ R.repair M p := by
  unfold repair
  refine div_nonneg (add_nonneg (div_nonneg (R.W_nonneg p) R.W_pos.le) ?_) (by linarith)
  rcases (R.m.nonneg p.1).lt_or_eq with h1 | h1
  · rcases (R.m.nonneg p.2).lt_or_eq with h2 | h2
    · have ha := abs_le.mp (hM p.1 h1).1
      have hb := abs_le.mp (hM p.2 h2).2
      have : 0 ≤ R.α p.1 + R.β p.2 + 2 * M := by linarith [ha.1, hb.1]
      exact mul_nonneg (mul_nonneg (mul_nonneg (R.J_nonneg p) this) h1.le) h2.le
    · rw [← h2, mul_zero]
  · rw [← h1, mul_zero, zero_mul]

/-- **The row marginal of the repair is `m`** (uses `J1 = 1` and `Jβ = 0`). -/
theorem repair_row {M : ℝ} (hM0 : 0 ≤ M)
    (hJβ : ∀ x, ∑ y, R.J (x, y) * R.β y * R.m.weight y = 0) (x : A) :
    ∑ y, R.repair M (x, y) = R.m.weight x := by
  unfold repair
  rw [← sum_div]
  have h1 : ∑ y, (R.W (x, y) / R.Z + R.J (x, y) * (R.α x + R.β y + 2 * M) * R.m.weight x *
      R.m.weight y) = R.a x + R.m.weight x * (R.α x * ∑ y, R.J (x, y) * R.m.weight y +
        ∑ y, R.J (x, y) * R.β y * R.m.weight y + 2 * M * ∑ y, R.J (x, y) * R.m.weight y) := by
    rw [sum_add_distrib]
    unfold a
    congr 1
    simp only [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun y _ => by ring
  rw [h1, R.J_row x, hJβ x, mul_one, add_zero, mul_one, mul_add, R.m_mul_α]
  have : (1 + 2 * M) ≠ 0 := by linarith
  field_simp
  ring

/-- **The column marginal of the repair is `m`** (uses `J*1 = 1` and `J*α = 0`). -/
theorem repair_col {M : ℝ} (hM0 : 0 ≤ M)
    (hJα : ∀ y, ∑ x, R.J (x, y) * R.α x * R.m.weight x = 0) (y : A) :
    ∑ x, R.repair M (x, y) = R.m.weight y := by
  unfold repair
  rw [← sum_div]
  have h1 : ∑ x, (R.W (x, y) / R.Z + R.J (x, y) * (R.α x + R.β y + 2 * M) * R.m.weight x *
      R.m.weight y) = R.b y + R.m.weight y * (∑ x, R.J (x, y) * R.α x * R.m.weight x +
        R.β y * ∑ x, R.J (x, y) * R.m.weight x + 2 * M * ∑ x, R.J (x, y) * R.m.weight x) := by
    rw [sum_add_distrib]
    unfold b
    congr 1
    simp only [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun x _ => by ring
  rw [h1, R.J_col y, hJα y, mul_one, zero_add, mul_one, mul_add, R.m_mul_β]
  have : (1 + 2 * M) ≠ 0 := by linarith
  field_simp
  ring

theorem repair_total {M : ℝ} (hM0 : 0 ≤ M)
    (hJβ : ∀ x, ∑ y, R.J (x, y) * R.β y * R.m.weight y = 0) :
    ∑ p, R.repair M p = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [R.repair_row hM0 hJβ]
  exact R.m.total

/-- **The repaired law** (`lem:signed-components`(d), `cor:markov-completion`). -/
noncomputable def repairLaw {M : ℝ} (hM0 : 0 ≤ M) (hM : R.DefectBound M)
    (hJβ : ∀ x, ∑ y, R.J (x, y) * R.β y * R.m.weight y = 0) : FiniteLaw (A × A) where
  weight := R.repair M
  nonneg := R.repair_nonneg hM0 hM
  total := R.repair_total hM0 hJβ

/-- The repair is supported where `W` or `J` is. -/
theorem repair_support {M : ℝ} {p : A × A} (hp : R.repair M p ≠ 0) : R.W p ≠ 0 ∨ R.J p ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hp
  unfold repair
  rw [hcon.1, hcon.2]
  ring

/-- `M = ∑|α| + ∑|β|` (over the support) satisfies the defect bound: the repair exists without
any analytic input. -/
noncomputable def Mmax : ℝ := ∑ x, |R.α x| + ∑ x, |R.β x|

theorem Mmax_nonneg : 0 ≤ R.Mmax :=
  add_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (sum_nonneg fun _ _ => abs_nonneg _)

theorem defectBound_Mmax : R.DefectBound R.Mmax := by
  intro x _
  have h1 : |R.α x| ≤ ∑ x, |R.α x| :=
    single_le_sum (f := fun x => |R.α x|) (fun _ _ => abs_nonneg _) (mem_univ x)
  have h2 : |R.β x| ≤ ∑ x, |R.β x| :=
    single_le_sum (f := fun x => |R.β x|) (fun _ _ => abs_nonneg _) (mem_univ x)
  have h3 : 0 ≤ ∑ x, |R.α x| := sum_nonneg fun _ _ => abs_nonneg _
  have h4 : 0 ≤ ∑ x, |R.β x| := sum_nonneg fun _ _ => abs_nonneg _
  unfold Mmax
  constructor <;> linarith

end RepairInput

end Sarkozy.SignedComponents
