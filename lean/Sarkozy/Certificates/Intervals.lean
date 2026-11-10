module

public import Sarkozy.Parameters
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Rational interval certificates

Intervals have rational endpoints. Certificate validity is a decidable rational
proposition, and soundness is proved over the reals. In particular, external
programs may propose endpoints, but cannot supply unverified real inequalities.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Certificates

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

def Interval.Contains (I : Interval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def Interval.Widens (I J : Interval) : Prop := J.lo ≤ I.lo ∧ I.hi ≤ J.hi

theorem Interval.Contains.widen {I J : Interval} {x : ℝ}
    (hx : I.Contains x) (h : I.Widens J) : J.Contains x := by
  constructor
  · exact (show (J.lo : ℝ) ≤ I.lo by exact_mod_cast h.1).trans hx.1
  · exact hx.2.trans (by exact_mod_cast h.2)

theorem Interval.contains_point (q : ℚ) : (Interval.mk q q).Contains (q : ℝ) := ⟨le_rfl, le_rfl⟩

theorem Interval.Contains.nonneg {I : Interval} {x : ℝ} (h : I.Contains x)
    (hlo : 0 ≤ I.lo) : 0 ≤ x := (show (0 : ℝ) ≤ I.lo by exact_mod_cast hlo).trans h.1

theorem Interval.Contains.pos {I : Interval} {x : ℝ} (h : I.Contains x)
    (hlo : 0 < I.lo) : 0 < x := (show (0 : ℝ) < I.lo by exact_mod_cast hlo).trans_le h.1

def Interval.AddValid (I J K : Interval) : Prop :=
  K.lo ≤ I.lo + J.lo ∧ I.hi + J.hi ≤ K.hi

theorem Interval.add_sound {I J K : Interval} {x y : ℝ}
    (h : I.AddValid J K) (hx : I.Contains x) (hy : J.Contains y) : K.Contains (x + y) := by
  constructor
  · have hh : (K.lo : ℝ) ≤ I.lo + J.lo := by exact_mod_cast h.1
    exact hh.trans (add_le_add hx.1 hy.1)
  · have hh : (I.hi : ℝ) + J.hi ≤ K.hi := by exact_mod_cast h.2
    exact (add_le_add hx.2 hy.2).trans hh

def Interval.SubValid (I J K : Interval) : Prop :=
  K.lo ≤ I.lo - J.hi ∧ I.hi - J.lo ≤ K.hi

theorem Interval.sub_sound {I J K : Interval} {x y : ℝ}
    (h : I.SubValid J K) (hx : I.Contains x) (hy : J.Contains y) : K.Contains (x - y) := by
  constructor
  · have hh : (K.lo : ℝ) ≤ I.lo - J.hi := by exact_mod_cast h.1
    exact hh.trans (sub_le_sub hx.1 hy.2)
  · have hh : (I.hi : ℝ) - J.lo ≤ K.hi := by exact_mod_cast h.2
    exact (sub_le_sub hx.2 hy.1).trans hh

theorem mul_between {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) (y : ℝ) :
    min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
  by_cases hy : 0 ≤ y
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right ha hy),
      (mul_le_mul_of_nonneg_right hb hy).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hb (le_of_not_ge hy)),
      (mul_le_mul_of_nonpos_right ha (le_of_not_ge hy)).trans (le_max_left _ _)⟩

/-- Corner bounds enclose the product of two arbitrary signed intervals. -/
theorem mul_corner_bounds {a b c d l u x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hlo : l ≤ a * c ∧ l ≤ a * d ∧ l ≤ b * c ∧ l ≤ b * d)
    (hhi : a * c ≤ u ∧ a * d ≤ u ∧ b * c ≤ u ∧ b * d ≤ u) :
    l ≤ x * y ∧ x * y ≤ u := by
  have ha := mul_between hy.1 hy.2 a
  have hb := mul_between hy.1 hy.2 b
  have hxy := mul_between hx.1 hx.2 y
  have hal : l ≤ a * y := by
    simpa only [mul_comm] using (le_min hlo.1 hlo.2.1).trans
      (by simpa only [mul_comm] using ha.1)
  have hbl : l ≤ b * y := by
    simpa only [mul_comm] using (le_min hlo.2.2.1 hlo.2.2.2).trans
      (by simpa only [mul_comm] using hb.1)
  have hau : a * y ≤ u := by
    exact (show a * y ≤ max (a * c) (a * d) by simpa only [mul_comm] using ha.2).trans
      (max_le hhi.1 hhi.2.1)
  have hbu : b * y ≤ u := by
    exact (show b * y ≤ max (b * c) (b * d) by simpa only [mul_comm] using hb.2).trans
      (max_le hhi.2.2.1 hhi.2.2.2)
  exact ⟨(le_min hal hbl).trans hxy.1, hxy.2.trans (max_le hau hbu)⟩

def Interval.MulValid (I J K : Interval) : Prop :=
  (K.lo ≤ I.lo * J.lo ∧ K.lo ≤ I.lo * J.hi ∧
    K.lo ≤ I.hi * J.lo ∧ K.lo ≤ I.hi * J.hi) ∧
  (I.lo * J.lo ≤ K.hi ∧ I.lo * J.hi ≤ K.hi ∧
    I.hi * J.lo ≤ K.hi ∧ I.hi * J.hi ≤ K.hi)

theorem Interval.mul_sound {I J K : Interval} {x y : ℝ}
    (h : I.MulValid J K) (hx : I.Contains x) (hy : J.Contains y) : K.Contains (x * y) := by
  exact mul_corner_bounds hx hy (by exact_mod_cast h.1) (by exact_mod_cast h.2)

def Interval.InvValid (I K : Interval) : Prop :=
  0 < I.lo ∧ K.lo ≤ I.hi⁻¹ ∧ I.lo⁻¹ ≤ K.hi

theorem Interval.inv_sound {I K : Interval} {x : ℝ}
    (h : I.InvValid K) (hx : I.Contains x) : K.Contains x⁻¹ := by
  have hlo : (0 : ℝ) < I.lo := by exact_mod_cast h.1
  constructor
  · have hh : (K.lo : ℝ) ≤ (I.hi : ℝ)⁻¹ := by exact_mod_cast h.2.1
    exact hh.trans (inv_anti₀ (hlo.trans_le hx.1) hx.2)
  · have hh : (I.lo : ℝ)⁻¹ ≤ K.hi := by exact_mod_cast h.2.2
    exact (inv_anti₀ hlo hx.1).trans hh

def Interval.PowValid (I K : Interval) (n : ℕ) : Prop :=
  0 ≤ I.lo ∧ K.lo ≤ I.lo ^ n ∧ I.hi ^ n ≤ K.hi

theorem Interval.pow_sound {I K : Interval} {x : ℝ} {n : ℕ}
    (h : I.PowValid K n) (hx : I.Contains x) : K.Contains (x ^ n) := by
  have hlo : (0 : ℝ) ≤ I.lo := by exact_mod_cast h.1
  constructor
  · have hh : (K.lo : ℝ) ≤ (I.lo : ℝ) ^ n := by exact_mod_cast h.2.1
    exact hh.trans (pow_le_pow_left₀ hlo hx.1 n)
  · have hh : (I.hi : ℝ) ^ n ≤ K.hi := by exact_mod_cast h.2.2
    exact (pow_le_pow_left₀ (hlo.trans hx.1) hx.2 n).trans hh

def Interval.SqrtValid (I K : Interval) : Prop :=
  0 ≤ I.lo ∧ 0 ≤ K.lo ∧ 0 ≤ K.hi ∧ K.lo ^ 2 ≤ I.lo ∧ I.hi ≤ K.hi ^ 2

theorem Interval.sqrt_sound {I K : Interval} {x : ℝ}
    (h : I.SqrtValid K) (hx : I.Contains x) : K.Contains (Real.sqrt x) := by
  have hx0 : 0 ≤ x := hx.nonneg h.1
  have hl0 : (0 : ℝ) ≤ K.lo := by exact_mod_cast h.2.1
  have hu0 : (0 : ℝ) ≤ K.hi := by exact_mod_cast h.2.2.1
  have hl : (K.lo : ℝ) ^ 2 ≤ x :=
    (show (K.lo : ℝ) ^ 2 ≤ I.lo by exact_mod_cast h.2.2.2.1).trans hx.1
  have hu : x ≤ (K.hi : ℝ) ^ 2 := hx.2.trans (by exact_mod_cast h.2.2.2.2)
  constructor
  · exact (Real.le_sqrt hl0 hx0).mpr hl
  · exact (Real.sqrt_le_iff).mpr ⟨hu0, hu⟩

end Sarkozy.Certificates
