module

public import Sarkozy.L20Cap.Rectangle

/-!
# The mean of `𝖪` and the row mass (`prop:l20-rectangular`(d), `‖𝔯‖ ≤ s_p`)

`paper/sections/20_middle_reference.tex`, proof of `prop:l20-rectangular`(d). Notation of
`Sarkozy.L20Cap.Rectangle`; `p = |F|`, `q = 1/p`, `r = p^{-1/2}`.

* **`Kbar_dev`** (with `thm:weil`, `Labellings.WeilBound`): for four distinct core labels,
  `|\bar𝖪(C) - 1| ≤ η = 2q + 11r`. In the star expansion of `𝖪` the singletons average to `0`,
  the six two-element supports to `-q` each with `∑σ_S = -2` (so `2q`), and the four three-root
  sums and the one four-root sum are bounded by Weil (`2r` and `3r`).
* **`rmass_norm_le`**: if `|\bar𝖪 - 1| ≤ η` on the admissible cores and
  `m_𝖪 = E_{μ^core}\bar𝖪 - 1 ≤ 𝔪`, then
  `‖𝔯‖ ≤ s_p = [1 + 4𝔪 + (6 + 4η + η²)η² + 256q²(1 + 2𝔪 + η²)]^{1/2}/(1 - q)`.

The bound `m_𝖪 ≤ 𝔪_+ = 2q + m_⋆/4` is `prop:l20-rank4`, from `lem:l20-star-mean` and
`lem:record:weighted-moment` (not formalized here); it is the hypothesis `hm`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Root sums of the core -/

theorem sum_chi_shift (hF : ringChar F ≠ 2) (y : F) : ∑ z, chi (z - y) = 0 := by
  have h := quadraticChar_sum_zero hF
  have e : ∑ z, chi (z - y) = ((∑ a : F, quadraticChar F a : ℤ) : ℝ) := by
    rw [Int.cast_sum]
    exact Fintype.sum_equiv (Equiv.subRight y) _ _ fun z => rfl
  rw [e, h, Int.cast_zero]

theorem sum_chi3 (hW : WeilBound F) {y₁ y₂ y₃ : F} (h12 : y₁ ≠ y₂) (h13 : y₁ ≠ y₃)
    (h23 : y₂ ≠ y₃) :
    |∑ z, chi (z - y₁) * chi (z - y₂) * chi (z - y₃)| ≤ 2 * Real.sqrt (Fintype.card F) := by
  have hS : ({y₁, y₂, y₃} : Finset F).card = 3 := by
    rw [card_insert_of_notMem (by simp [h12, h13]), card_pair h23]
  have e : ∑ z, chi (z - y₁) * chi (z - y₂) * chi (z - y₃) =
      (rootSum ({y₁, y₂, y₃} : Finset F) : ℝ) := by
    unfold rootSum
    rw [Int.cast_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [prod_insert (by simp [h12, h13]), prod_pair h23]
    show _ = chi ((z - y₁) * ((z - y₂) * (z - y₃)))
    rw [chi_mul, chi_mul]
    ring
  rw [e]
  have := hW ({y₁, y₂, y₃} : Finset F) (insert_nonempty _ _)
  rw [hS] at this
  calc _ ≤ ((3 : ℕ) - 1 : ℝ) * Real.sqrt (Fintype.card F) := by exact_mod_cast this
    _ = 2 * Real.sqrt (Fintype.card F) := by norm_num

theorem sum_chi4 (hW : WeilBound F) {C : Fin 4 → F} (hC : Function.Injective C) :
    |∑ z, chi (z - C 0) * chi (z - C 1) * chi (z - C 2) * chi (z - C 3)| ≤
      3 * Real.sqrt (Fintype.card F) := by
  have hS : (univ.image C).card = 4 := by rw [card_image_of_injective _ hC]; simp
  have e : ∑ z, chi (z - C 0) * chi (z - C 1) * chi (z - C 2) * chi (z - C 3) =
      (rootSum (univ.image C) : ℝ) := by
    unfold rootSum
    rw [Int.cast_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [prod_image fun a _ b _ h => hC h, Fin.prod_univ_four]
    show _ = chi ((z - C 0) * (z - C 1) * (z - C 2) * (z - C 3))
    rw [chi_mul, chi_mul, chi_mul]
  rw [e]
  have := hW (univ.image C) (by simp)
  rw [hS] at this
  calc _ ≤ ((4 : ℕ) - 1 : ℝ) * Real.sqrt (Fintype.card F) := by exact_mod_cast this
    _ = 3 * Real.sqrt (Fintype.card F) := by norm_num

/-- **`|\bar𝖪(C) - 1| ≤ 2q + 11r`** for four distinct core labels (`thm:weil`, `eq:two-root`;
proof of `prop:l20-rectangular`(d)). -/
theorem Kbar_dev (hF : ringChar F ≠ 2) (hW : WeilBound F) {C : Fin 4 → F}
    (hC : Function.Injective C) :
    |Kbar C - 1| ≤ 2 / (Fintype.card F : ℝ) + 11 / Real.sqrt (Fintype.card F) := by
  have hp1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hp0 : (0 : ℝ) < Fintype.card F := by linarith
  have hsq : 0 < Real.sqrt (Fintype.card F) := Real.sqrt_pos.mpr hp0
  have hsqsq : Real.sqrt (Fintype.card F) * Real.sqrt (Fintype.card F) = Fintype.card F :=
    Real.mul_self_sqrt hp0.le
  set a : F → ℝ := fun z => chi (z - C 0)
  set b : F → ℝ := fun z => chi (z - C 1)
  set c : F → ℝ := fun z => chi (z - C 2)
  set d : F → ℝ := fun z => chi (z - C 3)
  have hK : ∀ z, Kz z C = 1 + c z + d z + c z * d z - a z - a z * c z - a z * d z -
      a z * c z * d z - b z - b z * c z - b z * d z - b z * c z * d z + a z * b z +
      a z * b z * c z + a z * b z * d z + a z * b z * c z * d z := by
    intro z
    rw [Kz_four]
    ring
  have hne : ∀ i j : Fin 4, i ≠ j → C i ≠ C j := fun i j h => hC.ne h
  have p2 : ∀ i j : Fin 4, i ≠ j → ∑ z, chi (z - C i) * chi (z - C j) = -1 := by
    intro i j h
    rw [sum_chi_mul_chi hF]
    simp only [hne i j h, ↓reduceIte]
  have s1 : ∀ i : Fin 4, ∑ z, chi (z - C i) = 0 := fun i => sum_chi_shift hF (C i)
  have t012 := sum_chi3 hW (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide))
  have t013 := sum_chi3 hW (hne 0 1 (by decide)) (hne 0 3 (by decide)) (hne 1 3 (by decide))
  have t023 := sum_chi3 hW (hne 0 2 (by decide)) (hne 0 3 (by decide)) (hne 2 3 (by decide))
  have t123 := sum_chi3 hW (hne 1 2 (by decide)) (hne 1 3 (by decide)) (hne 2 3 (by decide))
  have t4 := sum_chi4 hW hC
  have hsum : ∑ z, Kz z C = Fintype.card F + 2 +
      ((∑ z, a z * b z * c z) + (∑ z, a z * b z * d z) - (∑ z, a z * c z * d z) -
        (∑ z, b z * c z * d z) + ∑ z, a z * b z * c z * d z) := by
    rw [sum_congr rfl fun z _ => hK z]
    simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
    simp only [a, b, c, d]
    rw [s1, s1, s1, s1, p2 2 3 (by decide), p2 0 2 (by decide), p2 0 3 (by decide),
      p2 1 2 (by decide), p2 1 3 (by decide), p2 0 1 (by decide)]
    ring
  set T := (∑ z, a z * b z * c z) + (∑ z, a z * b z * d z) - (∑ z, a z * c z * d z) -
    (∑ z, b z * c z * d z) + ∑ z, a z * b z * c z * d z with hT
  have hTb : |T| ≤ 11 * Real.sqrt (Fintype.card F) := by
    have e1 := abs_add_le ((∑ z, a z * b z * c z) + (∑ z, a z * b z * d z) -
      (∑ z, a z * c z * d z) - (∑ z, b z * c z * d z)) (∑ z, a z * b z * c z * d z)
    have e2 := abs_sub ((∑ z, a z * b z * c z) + (∑ z, a z * b z * d z) -
      (∑ z, a z * c z * d z)) (∑ z, b z * c z * d z)
    have e3 := abs_sub ((∑ z, a z * b z * c z) + (∑ z, a z * b z * d z))
      (∑ z, a z * c z * d z)
    have e4 := abs_add_le (∑ z, a z * b z * c z) (∑ z, a z * b z * d z)
    rw [hT]
    linarith
  have hKbar : Kbar C - 1 = 2 / (Fintype.card F : ℝ) + T / Fintype.card F := by
    rw [Kbar, hsum]
    field_simp
    ring
  rw [hKbar]
  have hq : 0 ≤ 2 / (Fintype.card F : ℝ) := by positivity
  have hTq : |T / Fintype.card F| ≤ 11 / Real.sqrt (Fintype.card F) := by
    rw [abs_div, abs_of_pos hp0, div_le_div_iff₀ hp0 hsq]
    calc |T| * Real.sqrt (Fintype.card F) ≤ 11 * Real.sqrt (Fintype.card F) *
          Real.sqrt (Fintype.card F) := mul_le_mul_of_nonneg_right hTb hsq.le
      _ = 11 * Fintype.card F := by rw [mul_assoc, hsqsq]
  calc |2 / (Fintype.card F : ℝ) + T / Fintype.card F|
      ≤ |2 / (Fintype.card F : ℝ)| + |T / Fintype.card F| := abs_add_le _ _
    _ ≤ 2 / (Fintype.card F : ℝ) + 11 / Real.sqrt (Fintype.card F) := by
        rw [abs_of_nonneg hq]; linarith

/-! ## The row mass -/

variable [Nonempty (CoreT F)] [Nonempty (PairT F)]

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
theorem Kbar_nonneg (hm1 : quadraticChar F (-1) = -1) {C : Fin 4 → F} (hC : Adm C) :
    0 ≤ Kbar C := by
  unfold Kbar
  exact div_nonneg (sum_nonneg fun z _ => Kz_nonneg hm1 hC z) (Nat.cast_nonneg _)

/-- **`‖𝔯‖ ≤ s_p`** (`prop:l20-rectangular`(d)): with `\bar𝖪 = 1 + y`, `|y| ≤ η` and `E y ≤ 𝔪`,
`E\bar𝖪⁴ ≤ 1 + 4𝔪 + (6 + 4η + η²)η²`, `E\bar𝖪² ≤ 1 + 2𝔪 + η²`, and the term `-32q\bar𝖪³ ≤ 0`
of `(1 - q)²𝔯²` is dropped. -/
theorem rmass_norm_le (hm1 : quadraticChar F (-1) = -1) {η m : ℝ}
    (hη : ∀ C : CoreT F, |Kbar C.1 - 1| ≤ η)
    (hm : (coreLaw (F := F)).expect (fun C => Kbar C.1 - 1) ≤ m) :
    nrm (coreLaw (F := F)) rmass ≤
      Real.sqrt (1 + 4 * m + (6 + 4 * η + η ^ 2) * η ^ 2 +
        256 * (Fintype.card F : ℝ)⁻¹ ^ 2 * (1 + 2 * m + η ^ 2)) /
        (1 - (Fintype.card F : ℝ)⁻¹) := by
  have hp1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  set q := (Fintype.card F : ℝ)⁻¹ with hqdef
  have hq0 : 0 < q := inv_pos.mpr (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hp1
  have h1q : 0 < 1 - q := by linarith
  set N := 1 + 4 * m + (6 + 4 * η + η ^ 2) * η ^ 2 + 256 * q ^ 2 * (1 + 2 * m + η ^ 2) with hN
  -- pointwise bound on `(1 - q)² 𝔯²`
  have hpt : ∀ C : CoreT F, ((1 - q) * rmass C) ^ 2 ≤
      (1 + 4 * (Kbar C.1 - 1) + (6 + 4 * η + η ^ 2) * η ^ 2) +
        256 * q ^ 2 * (1 + 2 * (Kbar C.1 - 1) + η ^ 2) := by
    intro C
    have hr : (1 - q) * rmass C = Kbar C.1 ^ 2 - 16 * q * Kbar C.1 := by
      have e : rmass C = (Kbar C.1 ^ 2 - 16 * q * Kbar C.1) / (1 - q) := rmass_eq hm1 C
      have h1q' : 1 - q ≠ 0 := h1q.ne'
      rw [e]
      field_simp
    rw [hr]
    set y := Kbar C.1 - 1 with hy
    have hK : Kbar C.1 = 1 + y := by rw [hy]; ring
    have hK0 : 0 ≤ Kbar C.1 := Kbar_nonneg hm1 C.2
    have hyb := hη C
    rw [← hy] at hyb
    have hy2 : y ^ 2 ≤ η ^ 2 := sq_le_sq' (abs_le.mp hyb).1 (abs_le.mp hyb).2
    have hy3 : y ^ 3 ≤ η ^ 3 := by
      have : |y| ^ 3 ≤ η ^ 3 := pow_le_pow_left₀ (abs_nonneg y) hyb 3
      have h' : y ^ 3 ≤ |y| ^ 3 := by
        rw [← abs_pow]; exact le_abs_self _
      linarith
    have hy4 : y ^ 4 ≤ η ^ 4 := by
      have : |y| ^ 4 ≤ η ^ 4 := pow_le_pow_left₀ (abs_nonneg y) hyb 4
      have e : y ^ 4 = |y| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      linarith
    have hK3 : 0 ≤ Kbar C.1 ^ 3 := pow_nonneg hK0 3
    have expand : (Kbar C.1 ^ 2 - 16 * q * Kbar C.1) ^ 2 =
        Kbar C.1 ^ 4 - 32 * q * Kbar C.1 ^ 3 + 256 * q ^ 2 * Kbar C.1 ^ 2 := by ring
    rw [expand, hK]
    have e4 : (1 + y) ^ 4 = 1 + 4 * y + 6 * y ^ 2 + 4 * y ^ 3 + y ^ 4 := by ring
    have e2 : (1 + y) ^ 2 = 1 + 2 * y + y ^ 2 := by ring
    rw [e4, e2]
    have hK3' : 0 ≤ (1 + y) ^ 3 := by rw [← hK]; exact hK3
    have : (6 + 4 * η + η ^ 2) * η ^ 2 = 6 * η ^ 2 + 4 * η ^ 3 + η ^ 4 := by ring
    rw [this]
    nlinarith [mul_nonneg hq0.le hK3', sq_nonneg q]
  -- integrate
  have hE : (coreLaw (F := F)).expect (fun C => ((1 - q) * rmass C) ^ 2) ≤ N := by
    calc (coreLaw (F := F)).expect (fun C => ((1 - q) * rmass C) ^ 2)
        ≤ (coreLaw (F := F)).expect (fun C => (1 + 4 * (Kbar C.1 - 1) +
            (6 + 4 * η + η ^ 2) * η ^ 2) + 256 * q ^ 2 * (1 + 2 * (Kbar C.1 - 1) + η ^ 2)) :=
          (coreLaw (F := F)).expect_mono hpt
      _ = 1 + 4 * (coreLaw (F := F)).expect (fun C => Kbar C.1 - 1) + (6 + 4 * η + η ^ 2) * η ^ 2 +
            256 * q ^ 2 * (1 + 2 * (coreLaw (F := F)).expect (fun C => Kbar C.1 - 1) + η ^ 2) := by
          simp only [FiniteLaw.expect_add, FiniteLaw.expect_const_mul, FiniteLaw.expect_const]
      _ ≤ N := by
          rw [hN]
          nlinarith [sq_nonneg q]
  have hE' : nrm (coreLaw (F := F)) (fun C => (1 - q) * rmass C) ^ 2 ≤ N := by
    rw [nrm_sq_expect]; exact hE
  have hN0 : 0 ≤ N := le_trans (sq_nonneg _) hE'
  rw [nrm_smul, abs_of_pos h1q] at hE'
  have hsq : (1 - q) * nrm (coreLaw (F := F)) rmass ≤ Real.sqrt N :=
    Real.le_sqrt_of_sq_le hE'
  rw [le_div_iff₀ h1q]
  linarith

end Sarkozy.L20Cap
