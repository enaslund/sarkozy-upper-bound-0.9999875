module

public import Sarkozy.Companion.ClassFields
public import Sarkozy.LetterTotals.Basic

@[expose] public section

/-!
# The supremal letter totals (HX2)

HX2, 8 November 2026. In the companion obligations the lettering `ℓ` and the letter bounds `X` are
both free data (D), and `hX : TotalsLe D ℓ X` is the only field that relates them. `X` enters only
through `hX0`, `hX` and the comparison series `hC`, `hCv`, and the series is monotone in `X`
(`c ≥ 0`). So the smallest admissible `X` is determined by `ℓ`: the **supremal letter totals**

  `letterSup D ℓ l = sup_L X_l(L)`, `X_l(L) = ∑_{ℓ_L(e) = l} π_{L,e}` (`MeanCredit.letterTotal`).

This file proves, in the generic context of `Companion.ClassFields` (so that the statements are
elaborated with the instances of `TotalsLe`):

* `letterTotal_le_types`: every letter total is at most the two type totals together;
* `TotalsBdd` (the letter totals are bounded above in `L`); `totalsBdd_of_totalsLe`;
  **`totalsBdd_of_types`**: bounded as soon as the two change types are (every lettering);
* **`totalsLe_letterSup`**: `TotalsLe D ℓ (letterSup D ℓ)` for every bounded lettering;
* **`letterSup_le`**: `TotalsLe D ℓ X → letterSup D ℓ ≤ X`; `letterSup_nonneg`;
* `letterSup_le_types`, `letterSup_le_of_sym`, `letterSup_le_of_skew`: the bounds that the type
  totals give for every lettering, and for a letter carried by exactly one change type;
* **`series_mono`**: the completed comparison series `∑_d c(d) ∏_l X_l^{d_l}/d_l!` at
  `0 ≤ X' ≤ X` converges, with sum at most the sum at `X` (`eq:final-joint-closing` is monotone in
  the price bounds; `rem:cp:monotone`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.LetterTotals2

open Sarkozy.RecordExpansion Sarkozy.MeanCredit Sarkozy.MeanCredit2 Sarkozy.TheoremC
open Sarkozy.Companion (TotalsLe)
open Sarkozy.CancellationSteps (PaperJ0)
open Sarkozy.LetterTotals (letterTotal_nonneg sum_entries_type letterTotal_eq_of_exact)

/-! ## One record expansion -/

section Entries

variable {J : Type*} [Fintype J] {T : J → Type*} [∀ b, Fintype (T b)]
  {Λ : Type*} [DecidableEq Λ]

/-- **Every letter total is at most the two type totals together** (nonnegative prices):
`X_l ≤ ∑_𝔟 ∑_t π^s_{𝔟,t} + ∑_𝔟 ∑_t π^a_{𝔟,t}`, whatever the lettering. -/
theorem letterTotal_le_types (ℓ : Entry T → Λ) {π : ∀ b, T b → ChangeType → ℝ}
    (hπ : ∀ b t e, 0 ≤ π b t e) (l : Λ) :
    letterTotal ℓ π l ≤ ∑ b, ∑ t, π b t .sym + ∑ b, ∑ t, π b t .skew := by
  classical
  have h1 : letterTotal ℓ π l ≤ ∑ e : Entry T, π e.1 e.2.1 e.2.2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => hπ _ _ _
  have h2 : ∑ e : Entry T, π e.1 e.2.1 e.2.2 =
      ∑ e ∈ univ.filter (fun e : Entry T => e.2.2 = .sym), π e.1 e.2.1 e.2.2 +
        ∑ e ∈ univ.filter (fun e : Entry T => e.2.2 = .skew), π e.1 e.2.1 e.2.2 := by
    rw [← sum_filter_add_sum_filter_not univ (fun e : Entry T => e.2.2 = .sym)]
    congr 1
    refine sum_congr (filter_congr fun e _ => ?_) fun _ _ => rfl
    rcases e.2.2 with _ | _ <;> simp
  rw [h2, sum_entries_type, sum_entries_type] at h1
  exact h1

end Entries

/-! ## The supremal letter totals -/

section Sup

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
  {C : Type} [DecidableEq C]

/-- **The letter totals are bounded uniformly in the scale.** -/
def TotalsBdd (D : CD blockOf) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C) : Prop :=
  ∀ l, BddAbove (Set.range fun L => letterTotal (ℓ L) (D.CL.π L) l)

/-- **The supremal letter totals** `sup_L X_l(L)` of the lettering `ℓ`: the smallest bounds `X`
with `TotalsLe D ℓ X` (`totalsLe_letterSup`, `letterSup_le`). -/
noncomputable def letterSup (D : CD blockOf) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C)
    (l : MLetter ⊕ C) : ℝ :=
  ⨆ L, letterTotal (ℓ L) (D.CL.π L) l

/-- Bounds `X` bound the letter totals uniformly. -/
theorem totalsBdd_of_totalsLe (D : CD blockOf) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C)
    (X : MLetter ⊕ C → ℝ) (hX : TotalsLe D ℓ X) : TotalsBdd D ℓ :=
  fun l => ⟨X l, by rintro _ ⟨L, rfl⟩; exact hX L l⟩

/-- **`TotalsLe` at the supremal totals**: for every lettering whose totals are bounded. -/
theorem totalsLe_letterSup (D : CD blockOf) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C)
    (h : TotalsBdd D ℓ) : TotalsLe D ℓ (letterSup D ℓ) :=
  fun L l => le_ciSup (h l) L

/-- **The supremal totals are the smallest bounds**: `TotalsLe D ℓ X` gives `letterSup ≤ X`. -/
theorem letterSup_le (D : CD blockOf) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C)
    (X : MLetter ⊕ C → ℝ) (hX : TotalsLe D ℓ X) (l : MLetter ⊕ C) : letterSup D ℓ l ≤ X l :=
  ciSup_le fun L => hX L l

/-- The supremal totals of nonnegative prices are nonnegative. -/
theorem letterSup_nonneg (D : CD blockOf) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C)
    (hπ : ∀ L b t e, 0 ≤ D.CL.π L b t e) (l : MLetter ⊕ C) : 0 ≤ letterSup D ℓ l :=
  Real.iSup_nonneg fun L => letterTotal_nonneg (ℓ L) (hπ L) l

/-- **The letter totals of every lettering are at most the two type totals together**. -/
theorem letterTotal_le_types' (D : CD blockOf) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C)
    (hπ : ∀ L b t e, 0 ≤ D.CL.π L b t e) (Sb Ab : ℝ)
    (hS : ∀ L, ∑ b, symTotal (D.CL.π L) b ≤ Sb) (hA : ∀ L, ∑ b, skewTotal (D.CL.π L) b ≤ Ab)
    (L : ℕ) (l : MLetter ⊕ C) : letterTotal (ℓ L) (D.CL.π L) l ≤ Sb + Ab :=
  (letterTotal_le_types (ℓ L) (hπ L) l).trans (add_le_add (hS L) (hA L))

/-- **Every lettering has bounded totals** once the two type totals are bounded uniformly. -/
theorem totalsBdd_of_types (D : CD blockOf) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C)
    (hπ : ∀ L b t e, 0 ≤ D.CL.π L b t e) (Sb Ab : ℝ)
    (hS : ∀ L, ∑ b, symTotal (D.CL.π L) b ≤ Sb) (hA : ∀ L, ∑ b, skewTotal (D.CL.π L) b ≤ Ab) :
    TotalsBdd D ℓ :=
  totalsBdd_of_totalsLe D ℓ (fun _ => Sb + Ab)
    (fun L l => letterTotal_le_types' D ℓ hπ Sb Ab hS hA L l)

/-- **The supremal totals of every lettering are at most the two type bounds together.** -/
theorem letterSup_le_types (D : CD blockOf) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C)
    (hπ : ∀ L b t e, 0 ≤ D.CL.π L b t e) (Sb Ab : ℝ)
    (hS : ∀ L, ∑ b, symTotal (D.CL.π L) b ≤ Sb) (hA : ∀ L, ∑ b, skewTotal (D.CL.π L) b ≤ Ab)
    (l : MLetter ⊕ C) : letterSup D ℓ l ≤ Sb + Ab :=
  letterSup_le D ℓ (fun _ => Sb + Ab) (fun L l => letterTotal_le_types' D ℓ hπ Sb Ab hS hA L l) l

/-- **A letter carried by exactly the symmetric entries** has supremal total at most the symmetric
bound. -/
theorem letterSup_le_of_sym (D : CD blockOf) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C)
    (σ : MLetter ⊕ C) (hσ : ∀ L e, ℓ L e = σ ↔ e.2.2 = .sym) (Sb : ℝ)
    (hS : ∀ L, ∑ b, symTotal (D.CL.π L) b ≤ Sb) : letterSup D ℓ σ ≤ Sb :=
  ciSup_le fun L => (letterTotal_eq_of_exact (ℓ L) (D.CL.π L) σ .sym (hσ L)).le.trans (hS L)

/-- **A letter carried by exactly the skew entries** has supremal total at most the skew bound. -/
theorem letterSup_le_of_skew (D : CD blockOf) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C)
    (α : MLetter ⊕ C) (hα : ∀ L e, ℓ L e = α ↔ e.2.2 = .skew) (Ab : ℝ)
    (hA : ∀ L, ∑ b, skewTotal (D.CL.π L) b ≤ Ab) : letterSup D ℓ α ≤ Ab :=
  ciSup_le fun L => (letterTotal_eq_of_exact (ℓ L) (D.CL.π L) α .skew (hα L)).le.trans (hA L)

end Sup

/-! ## The completed series is monotone in the totals -/

section Series

variable {Λ : Type*} [Fintype Λ]

/-- **The completed comparison series is monotone in the letter bounds**: if it converges to `Cv`
at `X` (with `c ≥ 0`), then at any `0 ≤ X' ≤ X` it converges, to a sum at most `Cv`. -/
theorem series_mono (c : (Λ → ℕ) → ℝ) (hc0 : ∀ d, 0 ≤ c d) (X X' : Λ → ℝ)
    (h0 : ∀ l, 0 ≤ X' l) (hle : ∀ l, X' l ≤ X l) {Cv : ℝ}
    (hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv) :
    HasSum (fun d => c d * ∏ l, X' l ^ d l / (d l).factorial)
        (∑' d, c d * ∏ l, X' l ^ d l / (d l).factorial) ∧
      (∑' d, c d * ∏ l, X' l ^ d l / (d l).factorial) ≤ Cv := by
  have hnn : ∀ d : Λ → ℕ, 0 ≤ c d * ∏ l, X' l ^ d l / (d l).factorial := fun d =>
    mul_nonneg (hc0 d) (prod_nonneg fun l _ => div_nonneg (pow_nonneg (h0 l) _)
      (Nat.cast_nonneg _))
  have hle' : ∀ d : Λ → ℕ, c d * ∏ l, X' l ^ d l / (d l).factorial ≤
      c d * ∏ l, X l ^ d l / (d l).factorial := fun d =>
    mul_le_mul_of_nonneg_left (prod_le_prod₀
      (fun l _ => div_nonneg (pow_nonneg (h0 l) _) (Nat.cast_nonneg _))
      fun l _ => div_le_div_of_nonneg_right (pow_le_pow_left₀ (h0 l) (hle l) _)
        (Nat.cast_nonneg _)) (hc0 d)
  have hs : Summable fun d : Λ → ℕ => c d * ∏ l, X' l ^ d l / (d l).factorial :=
    Summable.of_nonneg_of_le hnn hle' hC.summable
  exact ⟨hs.hasSum, hasSum_le hle' hs.hasSum hC⟩

end Series

end Sarkozy.LetterTotals2
