module

public import Sarkozy.L20Cap.Mass

/-!
# Admissible cores exist for every `p ≥ 11` with `χ(-1) = -1`

The theorems of `Sarkozy.L20Cap` take `[Nonempty (CoreT F)]` and `[Nonempty (PairT F)]` as
instance arguments (the laws `μ^core`, `μ^pair` are uniform on these types). They can be met at
every finite field of odd characteristic with `χ(-1) = -1` and at least `11` elements:

* `card_consecutive_squares`: `4·#{c : χ(c) = χ(c - 1) = 1} = p - 3` (from
  `∑_c(1 + χ(c))(1 + χ(c - 1)) = p - 1`, `sum_chi_mul_chi`);
* **`coreT_nonempty`**: the core `(0, 1, c, c')`, with `c ≠ c'` both in that set, is admissible;
* `pairT_nonempty`: `(0, 1)` is a distinct pair;
* `mean_Kbar_le_eta`: the hypothesis `hm` of the caps holds with `𝔪 = η` (Weil alone).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The consecutive squares**: `4·#{c : χ(c) = χ(c - 1) = 1} = p - 3` when `χ(-1) = -1`. -/
theorem card_consecutive_squares (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2) :
    4 * ((univ.filter fun c : F => quadraticChar F c = 1 ∧ quadraticChar F (c - 1) = 1).card : ℝ) =
      (Fintype.card F : ℝ) - 3 := by
  set S := univ.filter fun c : F => quadraticChar F c = 1 ∧ quadraticChar F (c - 1) = 1 with hS
  have hpt : ∀ c : F, (1 + chi c) * (1 + chi (c - 1)) =
      (if c ∈ S then (4 : ℝ) else 0) + (if c = 1 then (2 : ℝ) else 0) := by
    intro c
    by_cases h0 : c = 0
    · subst h0
      have h1 : (1 : F) ≠ 0 := one_ne_zero
      have : chi (-1 : F) = -1 := by simp [chi, hm1]
      have hn : (0 : F) ∉ S := by simp [hS]
      simp [chi_zero, this, hn, h1.symm]
    · by_cases h1 : c = 1
      · subst h1
        have hn : (1 : F) ∉ S := by simp [hS]
        simp [chi, hn]
        norm_num
      · have hc1 : c - 1 ≠ 0 := sub_ne_zero.mpr h1
        rcases chi_of_ne h0 with ha | ha <;> rcases chi_of_ne hc1 with hb | hb
        · have hm : c ∈ S := by
            simp only [hS, mem_filter, mem_univ, true_and]
            simp only [chi] at ha hb
            exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩
          simp [ha, hb, hm, h1]
          norm_num
        · have hm : c ∉ S := by
            simp only [hS, mem_filter, mem_univ, true_and, not_and]
            intro _ h2'
            simp only [chi, h2'] at hb
            norm_num at hb
          simp [ha, hb, hm, h1]
        · have hm : c ∉ S := by
            simp only [hS, mem_filter, mem_univ, true_and, not_and]
            intro h1' _
            simp only [chi, h1'] at ha
            norm_num at ha
          simp [ha, hb, hm, h1]
        · have hm : c ∉ S := by
            simp only [hS, mem_filter, mem_univ, true_and, not_and]
            intro h1' _
            simp only [chi, h1'] at ha
            norm_num at ha
          simp [ha, hb, hm, h1]
  have hsum : ∑ c : F, (1 + chi c) * (1 + chi (c - 1)) = (Fintype.card F : ℝ) - 1 := by
    have e : ∀ c : F, (1 + chi c) * (1 + chi (c - 1)) =
        1 + chi (c - 0) + chi (c - 1) + chi (c - 0) * chi (c - 1) := by
      intro c; rw [sub_zero]; ring
    rw [sum_congr rfl fun c _ => e c, sum_add_distrib, sum_add_distrib, sum_add_distrib,
      sum_chi_shift hF, sum_chi_shift hF, sum_chi_mul_chi hF]
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, zero_ne_one, ↓reduceIte, add_zero]
    ring
  rw [sum_congr rfl fun c _ => hpt c, sum_add_distrib, sum_ite_mem, sum_ite_eq'] at hsum
  simp only [univ_inter, sum_const, nsmul_eq_mul, mem_univ, ↓reduceIte] at hsum
  linarith

/-- **Admissible cores exist** for `p ≥ 11` with `χ(-1) = -1`. -/
theorem coreT_nonempty (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2)
    (h11 : 11 ≤ Fintype.card F) : Nonempty (CoreT F) := by
  have hc := card_consecutive_squares hm1 hF
  have hp : (11 : ℝ) ≤ Fintype.card F := by exact_mod_cast h11
  set S := univ.filter fun c : F => quadraticChar F c = 1 ∧ quadraticChar F (c - 1) = 1 with hS
  have h2 : 1 < S.card := by
    have : (2 : ℝ) ≤ S.card := by linarith
    exact_mod_cast this
  obtain ⟨c, hcS, c', hc'S, hne⟩ := one_lt_card.mp h2
  simp only [hS, mem_filter, mem_univ, true_and] at hcS hc'S
  have c0 : c ≠ 0 := fun h => by rw [h, quadraticChar_zero] at hcS; exact zero_ne_one hcS.1
  have c'0 : c' ≠ 0 := fun h => by rw [h, quadraticChar_zero] at hc'S; exact zero_ne_one hc'S.1
  have c1 : c ≠ 1 := fun h => by
    rw [h, sub_self, quadraticChar_zero] at hcS; exact zero_ne_one hcS.2
  have c'1 : c' ≠ 1 := fun h => by
    rw [h, sub_self, quadraticChar_zero] at hc'S; exact zero_ne_one hc'S.2
  refine ⟨⟨![0, 1, c, c'], ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      first
      | exact absurd hij zero_ne_one | exact absurd hij.symm zero_ne_one
      | exact absurd hij.symm c0 | exact absurd hij c0
      | exact absurd hij.symm c'0 | exact absurd hij c'0
      | exact absurd hij.symm c1 | exact absurd hij c1
      | exact absurd hij.symm c'1 | exact absurd hij c'1
      | exact absurd hij hne | exact absurd hij.symm hne
  · simpa using hcS.1
  · simpa using hc'S.1
  · simpa using hcS.2
  · simpa using hc'S.2

/-- `(0, 1)` is a distinct pair. -/
theorem pairT_nonempty : Nonempty (PairT F) := ⟨⟨(0, 1), zero_ne_one⟩⟩

/-- **Non-vacuity of `hm`**: by Weil alone, `E_{μ^core}\bar𝖪 - 1 ≤ η = 2q + 11r`. (The paper's
sharper `𝔪₊ = 2q + m_⋆/4` comes from `lem:l20-star-mean`.) -/
theorem mean_Kbar_le_eta [Nonempty (CoreT F)] (hF : ringChar F ≠ 2)
    (hW : Sarkozy.Labellings.WeilBound F) :
    (coreLaw (F := F)).expect (fun C => Kbar C.1 - 1) ≤
      2 / (Fintype.card F : ℝ) + 11 / Real.sqrt (Fintype.card F) :=
  (coreLaw (F := F)).expect_le_const fun C => (le_abs_self _).trans (Kbar_dev hF hW C.2.1)

end Sarkozy.L20Cap
