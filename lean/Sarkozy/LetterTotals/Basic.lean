module

public import Sarkozy.MeanCredit.Completion

@[expose] public section

/-!
# Letter totals of one change type (HX)

HX, 8 November 2026. The field `hX : TotalsLe` of the companion statement bounds every letter
total `X_l = ∑_{ℓ(e) = l} π_e` (`MeanCredit.letterTotal`) of the lettering `ℓ` of the record
expansion. This file relates letter totals to the totals of one change type,
`∑_𝔟 s_𝔟 = ∑_𝔟 ∑_t π^s_{𝔟,t}` and `∑_𝔟 a_𝔟 = ∑_𝔟 ∑_t π^a_{𝔟,t}` (`symTotal`, `skewTotal`),
which are what the price lemmas bound (`def:cp4`(b), `def:closing-quantities`).

* `letterTotal_nonneg`;
* `sum_entries_type`: the entries of change type `e₀` carry the total `∑_𝔟 ∑_t π_{𝔟,t,e₀}`;
* **`letterTotal_eq_of_exact`**: a letter carried by exactly the entries of type `e₀` has that
  total (`letterTotal_eq_symTotal`, `letterTotal_eq_skewTotal`);
* **`sum_letterTotal_le_of_pure`**: letters carried only by entries of type `e₀` have, together,
  at most that total (`sum_letterTotal_le_symTotal`, `sum_letterTotal_le_skewTotal`).
-/

namespace Sarkozy.LetterTotals

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion Sarkozy.MeanCredit

variable {J : Type*} [Fintype J] {T : J → Type*} [∀ b, Fintype (T b)]
  {Λ : Type*} [DecidableEq Λ]

/-- Letter totals of nonnegative prices are nonnegative. -/
theorem letterTotal_nonneg (ℓ : Entry T → Λ) {π : ∀ b, T b → ChangeType → ℝ}
    (hπ : ∀ b t e, 0 ≤ π b t e) (l : Λ) : 0 ≤ letterTotal ℓ π l :=
  sum_nonneg fun _ _ => hπ _ _ _

/-- **The entries of one change type** carry the total `∑_𝔟 ∑_t π_{𝔟,t,e₀}`. -/
theorem sum_entries_type (π : ∀ b, T b → ChangeType → ℝ) (e₀ : ChangeType) :
    ∑ e ∈ univ.filter (fun e : Entry T => e.2.2 = e₀), π e.1 e.2.1 e.2.2 =
      ∑ b, ∑ t, π b t e₀ := by
  classical
  rw [sum_filter, Fintype.sum_sigma]
  refine sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun t _ => ?_
  rw [Fintype.sum_eq_single e₀ fun e he => by simp [he]]
  simp

/-- **A letter carried by exactly the entries of change type `e₀`** has the total of that type. -/
theorem letterTotal_eq_of_exact (ℓ : Entry T → Λ) (π : ∀ b, T b → ChangeType → ℝ) (σ : Λ)
    (e₀ : ChangeType) (h : ∀ e, ℓ e = σ ↔ e.2.2 = e₀) :
    letterTotal ℓ π σ = ∑ b, ∑ t, π b t e₀ := by
  unfold letterTotal
  rw [← sum_entries_type π e₀]
  exact sum_congr (filter_congr fun e _ => h e) fun _ _ => rfl

/-- The symmetric case of `letterTotal_eq_of_exact`: the total is `∑_𝔟 s_𝔟`. -/
theorem letterTotal_eq_symTotal [DecidableEq J] [∀ b, DecidableEq (T b)] (ℓ : Entry T → Λ)
    (π : ∀ b, T b → ChangeType → ℝ) (σ : Λ) (h : ∀ e, ℓ e = σ ↔ e.2.2 = .sym) :
    letterTotal ℓ π σ = ∑ b, symTotal π b :=
  letterTotal_eq_of_exact ℓ π σ .sym h

/-- The skew case of `letterTotal_eq_of_exact`: the total is `∑_𝔟 a_𝔟`. -/
theorem letterTotal_eq_skewTotal [DecidableEq J] [∀ b, DecidableEq (T b)] (ℓ : Entry T → Λ)
    (π : ∀ b, T b → ChangeType → ℝ) (α : Λ) (h : ∀ e, ℓ e = α ↔ e.2.2 = .skew) :
    letterTotal ℓ π α = ∑ b, skewTotal π b :=
  letterTotal_eq_of_exact ℓ π α .skew h

/-- **Letters carried only by entries of change type `e₀`** have, together, at most the total of
that type (nonnegative prices). -/
theorem sum_letterTotal_le_of_pure (ℓ : Entry T → Λ) {π : ∀ b, T b → ChangeType → ℝ}
    (hπ : ∀ b t e, 0 ≤ π b t e) (s : Finset Λ) (e₀ : ChangeType)
    (h : ∀ e, ℓ e ∈ s → e.2.2 = e₀) :
    ∑ l ∈ s, letterTotal ℓ π l ≤ ∑ b, ∑ t, π b t e₀ := by
  classical
  unfold letterTotal
  have e1 : ∑ l ∈ s, ∑ e ∈ univ.filter (fun e : Entry T => ℓ e = l), π e.1 e.2.1 e.2.2 =
      ∑ e ∈ univ.filter (fun e : Entry T => ℓ e ∈ s), π e.1 e.2.1 e.2.2 := by
    rw [sum_filter]
    simp_rw [sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun e _ => ?_
    rw [sum_ite_eq]
  rw [e1, ← sum_entries_type π e₀]
  refine sum_le_sum_of_subset_of_nonneg (fun e he => ?_) fun _ _ _ => hπ _ _ _
  rw [mem_filter] at he ⊢
  exact ⟨he.1, h e he.2⟩

/-- The symmetric case of `sum_letterTotal_le_of_pure`. -/
theorem sum_letterTotal_le_symTotal [DecidableEq J] [∀ b, DecidableEq (T b)]
    (ℓ : Entry T → Λ) {π : ∀ b, T b → ChangeType → ℝ} (hπ : ∀ b t e, 0 ≤ π b t e)
    (s : Finset Λ) (h : ∀ e, ℓ e ∈ s → e.2.2 = .sym) :
    ∑ l ∈ s, letterTotal ℓ π l ≤ ∑ b, symTotal π b :=
  sum_letterTotal_le_of_pure ℓ hπ s .sym h

/-- The skew case of `sum_letterTotal_le_of_pure`. -/
theorem sum_letterTotal_le_skewTotal [DecidableEq J] [∀ b, DecidableEq (T b)]
    (ℓ : Entry T → Λ) {π : ∀ b, T b → ChangeType → ℝ} (hπ : ∀ b t e, 0 ≤ π b t e)
    (s : Finset Λ) (h : ∀ e, ℓ e ∈ s → e.2.2 = .skew) :
    ∑ l ∈ s, letterTotal ℓ π l ≤ ∑ b, skewTotal π b :=
  sum_letterTotal_le_of_pure ℓ hπ s .skew h

end Sarkozy.LetterTotals
