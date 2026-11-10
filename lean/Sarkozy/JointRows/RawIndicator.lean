module

public import Sarkozy.JointRows.CollExpansion

/-! The raw pinned kernel is an exact constant times the compatibility indicator. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.Coll

open Finset Sarkozy.ExtractionK

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

def Compatible (ς : Fin n → Fin n → ℤ) (x y : Fin n → F) : Prop :=
  (∀ i j, x i ≠ y j) ∧
    ∀ e ∈ pairSet ς, quadraticChar F ((ς e.1 e.2 : F) * (y e.2 - x e.1)) = 1

noncomputable instance (ς : Fin n → Fin n → ℤ) (x y : Fin n → F) :
    Decidable (Compatible ς x y) := Classical.propDecidable _

theorem rawKer_indicator (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (x y : Fin n → F) :
    rawKer ς x y = if Compatible ς x y then (2 : ℝ) ^ (pairSet ς).card else 0 := by
  classical
  unfold rawKer
  rw [prod_pinOmega]
  by_cases hxy : ∃ i j, x i = y j
  · have hc : ¬ Compatible ς x y := by
      rintro ⟨h, _⟩
      obtain ⟨i, j, hij⟩ := hxy
      exact h i j hij
    simp only [hxy, hc, ↓reduceIte, zero_mul]
  · have hsep : ∀ i j, x i ≠ y j := by simpa only [not_exists] using hxy
    have hfactor (e : Fin n × Fin n) (he : e ∈ pairSet ς) :
        1 + chiPair ς e x y = if quadraticChar F ((ς e.1 e.2 : F) *
          (y e.2 - x e.1)) = 1 then 2 else 0 := by
      have hsign : ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1 := by
        rcases hς e.1 e.2 with h0 | h1 | h1
        · exact False.elim ((mem_filter.mp he).2 h0)
        · exact Or.inl h1
        · exact Or.inr h1
      have hne : (ς e.1 e.2 : F) * (y e.2 - x e.1) ≠ 0 :=
        mul_ne_zero (pin_char_cast_ne_zero hsign) (sub_ne_zero.mpr (hsep _ _).symm)
      rcases quadraticChar_dichotomy hne with h | h <;> norm_num [chiPair, h]
    simp only [hxy, ↓reduceIte, one_mul]
    rw [prod_congr rfl hfactor]
    by_cases hc : Compatible ς x y
    · simp only [hc, ↓reduceIte]
      rw [prod_congr rfl fun e he => ite_eq_left (hc.2 e he), prod_const]
    · rw [ite_eq_right hc]
      have hfail : ¬ ∀ e ∈ pairSet ς,
          quadraticChar F ((ς e.1 e.2 : F) * (y e.2 - x e.1)) = 1 :=
        fun h => hc ⟨hsep, h⟩
      push Not at hfail
      obtain ⟨e, he, hne⟩ := hfail
      exact prod_eq_zero he (ite_eq_right hne)

end Sarkozy.JointRows.Coll
