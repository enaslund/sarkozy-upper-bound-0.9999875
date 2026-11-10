module

public import Sarkozy.Parameters
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Sets, density, and the statement to be proved

`PowerSavingBound` is a proposition, not an assertion that it has been proved.
The square-difference predicate uses the convention of the OpenAI development.
See `NOTICES.md` for attribution of the square-step lemmas.
-/

namespace Sarkozy

/-- No ordered pair in A has difference equal to a nonzero natural square. -/
def IsSquareDifferenceFree (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ m : ℕ, 1 ≤ m → a - b ≠ (m : ℤ) ^ 2

def Admissible (N : ℕ) (A : Finset ℤ) : Prop :=
  A ⊆ Finset.Icc 1 (N : ℤ) ∧ IsSquareDifferenceFree A

@[simp] theorem admissible_empty (N : ℕ) : Admissible N ∅ := by
  simp [Admissible, IsSquareDifferenceFree]

noncomputable def density (N : ℕ) (A : Finset ℤ) : ℝ :=
  (A.card : ℝ) / (N : ℝ)

theorem density_nonneg (N : ℕ) (A : Finset ℤ) : 0 ≤ density N A := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem card_le_length {N : ℕ} {A : Finset ℤ}
    (hA : A ⊆ Finset.Icc 1 (N : ℤ)) : A.card ≤ N := by
  have h := Finset.card_le_card hA
  simpa using h

theorem density_le_one {N : ℕ} {A : Finset ℤ} (hN : 1 ≤ N)
    (hA : A ⊆ Finset.Icc 1 (N : ℤ)) : density N A ≤ 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (div_le_one hn).2
  exact_mod_cast card_le_length hA

/-- A uniform cardinality bound for all square-difference-free subsets of [1,N]. -/
def CardinalityBound (exponent : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℤ,
    Admissible N A → (A.card : ℝ) ≤ C * (N : ℝ) ^ exponent

/-- Exact target of the paper. No unconditional proof is supplied by this milestone. -/
def PowerSavingBound : Prop := CardinalityBound (1 - saving)

/-- The rounded exponent in the title is a slightly weaker target. -/
def TitleBound : Prop := CardinalityBound titleExponent

theorem titleBound_of_powerSavingBound (h : PowerSavingBound) : TitleBound := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, ?_⟩
  intro N hN A hA
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact (h N hN A hA).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hn exact_exponent_lt_title.le) hC.le)

/-- Pull A back along a square-step progression. -/
noncomputable def squareStepChild (A : Finset ℤ) (L D : ℕ) (c : ℤ) : Finset ℤ :=
  (Finset.Icc 1 (L : ℤ)).filter (fun n => (D : ℤ) ^ 2 * n + c ∈ A)

theorem squareStepChild_subset (A : Finset ℤ) (L D : ℕ) (c : ℤ) :
    squareStepChild A L D c ⊆ Finset.Icc 1 (L : ℤ) := Finset.filter_subset _ _

/-- Square-step children preserve the hypothesis needed for induction. -/
theorem squareStepChild_free {A : Finset ℤ} (hA : IsSquareDifferenceFree A)
    (L D : ℕ) (hD : 1 ≤ D) (c : ℤ) :
    IsSquareDifferenceFree (squareStepChild A L D c) := by
  intro a ha b hb m hm he
  have h := hA _ (Finset.mem_filter.mp ha).2 _ (Finset.mem_filter.mp hb).2
    (D * m) (by nlinarith)
  apply h
  push_cast
  calc
    (D : ℤ) ^ 2 * a + c - ((D : ℤ) ^ 2 * b + c) =
        (D : ℤ) ^ 2 * (a - b) := by ring
    _ = _ := by rw [he]; ring

theorem squareStepChild_admissible {A : Finset ℤ} (hA : IsSquareDifferenceFree A)
    (L D : ℕ) (hD : 1 ≤ D) (c : ℤ) : Admissible L (squareStepChild A L D c) :=
  ⟨squareStepChild_subset A L D c, squareStepChild_free hA L D hD c⟩

end Sarkozy
