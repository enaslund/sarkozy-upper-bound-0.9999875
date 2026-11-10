module

public import Sarkozy.FiniteProbability
public import Mathlib.Data.Fintype.Perm

/-!
# Exact pin counts and weighted event bounds in a finite cube

Specifying `r` distinct coordinates in a cube over `q` labels has uniform
mass `q⁻ʳ`. The weighted form allows a bounded density and a positive kernel.
-/

@[expose] public section

namespace Sarkozy.PartV.CubePins

open Finset

variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

theorem card_pins (s : Finset I) (a : I → A) :
    (univ.filter fun y : I → A => ∀ i ∈ s, y i = a i).card =
      Fintype.card A ^ (Fintype.card I - s.card) := by
  have hset : (univ.filter fun y : I → A => ∀ i ∈ s, y i = a i) =
      Fintype.piFinset (fun i => if i ∈ s then {a i} else univ) := by
    ext y
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i ∈ s <;> simp [hi, h]
    · intro h i hi
      simpa [hi] using h i
  rw [hset, Fintype.card_piFinset]
  simp only [apply_ite card, card_singleton, card_univ]
  rw [prod_ite]
  simp only [prod_const_one, one_mul, prod_const]
  have hc : (univ.filter fun i => i ∉ s) = sᶜ := by ext; simp
  rw [hc, card_compl]

/-- Weights need not sum to one: a kernel times a probability density is allowed. -/
theorem mass_pins [Nonempty A] (s : Finset I) (a : I → A)
    (w : (I → A) → ℝ) (M : ℝ)
    (hw : ∀ y, w y ≤ M / (Fintype.card A : ℝ) ^ Fintype.card I) :
    (∑ y ∈ univ.filter (fun y : I → A => ∀ i ∈ s, y i = a i), w y) ≤
      M / (Fintype.card A : ℝ) ^ s.card := by
  have hq : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ ∑ _y ∈ univ.filter (fun y : I → A => ∀ i ∈ s, y i = a i),
        M / (Fintype.card A : ℝ) ^ Fintype.card I :=
      sum_le_sum (fun y _ => hw y)
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, card_pins, Nat.cast_pow]
      have hi : Fintype.card I = (Fintype.card I - s.card) + s.card :=
        (Nat.sub_add_cancel (card_le_univ s)).symm
      have hpow : (Fintype.card A : ℝ) ^ Fintype.card I =
          (Fintype.card A : ℝ) ^ (Fintype.card I - s.card) *
            (Fintype.card A : ℝ) ^ s.card := by
        conv_lhs => rw [hi, pow_add]
      rw [hpow]
      field_simp

variable {X : Type*} [Fintype X]

noncomputable def mass (w : X → ℝ) (E : X → Prop) : ℝ := by
  classical
  exact ∑ x ∈ univ.filter E, w x

theorem mass_mono (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {E F : X → Prop} (h : ∀ x, E x → F x) : mass w E ≤ mass w F := by
  classical
  apply sum_le_sum_of_subset_of_nonneg _ (fun x _ _ => hw x)
  intro x hx
  exact mem_filter.mpr ⟨mem_univ x, h x (mem_filter.mp hx).2⟩

theorem mass_union (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (E F : X → Prop) :
    mass w (fun x => E x ∨ F x) ≤ mass w E + mass w F := by
  classical
  unfold mass
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_le_sum
  intro x _
  by_cases hE : E x <;> by_cases hF : F x <;> simp [hE, hF, hw x]

theorem mass_exists_list {J : Type*} (l : List J) (E : J → X → Prop)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    mass w (fun x => ∃ j ∈ l, E j x) ≤ (l.map fun j => mass w (E j)).sum := by
  classical
  induction l with
  | nil => simp [mass]
  | cons j l ih =>
    simp only [List.mem_cons, exists_eq_or_imp, List.map_cons, List.sum_cons]
    exact (mass_union w hw _ _).trans (add_le_add_right ih _)

theorem mass_exists_fintype {J : Type*} [Fintype J] (E : J → X → Prop)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    mass w (fun x => ∃ j, E j x) ≤ ∑ j, mass w (E j) := by
  classical
  simpa using mass_exists_list (univ : Finset J).toList E w hw

theorem mass_pins_subtype [Nonempty A] (s : Finset I) (a : s → A)
    (w : (I → A) → ℝ) (M : ℝ)
    (hw : ∀ y, w y ≤ M / (Fintype.card A : ℝ) ^ Fintype.card I) :
    mass w (fun y => ∀ i : s, y i.val = a i) ≤
      M / (Fintype.card A : ℝ) ^ s.card := by
  classical
  let b (i : I) := if hi : i ∈ s then a ⟨i, hi⟩ else Classical.arbitrary A
  have he : (fun y : I → A => ∀ i : s, y i.val = a i) =
      (fun y : I → A => ∀ i ∈ s, y i = b i) := by
    funext y
    apply propext
    constructor
    · intro h i hi
      simpa [b, hi] using h ⟨i, hi⟩
    · intro h i
      simpa [b, i.property] using h i.val i.property
  rw [he]
  unfold mass
  convert mass_pins s b w M hw using 1
  apply sum_congr
  · ext y
    simp
  · intro y _
    rfl

/-- A union over all bijections costs at most `r!` prescribed-coordinate events. -/
theorem mass_matchings {L : Type*} [Fintype L] [Nonempty A]
    (s : Finset I) (a : L → A) (w : (I → A) → ℝ)
    (hw0 : ∀ y, 0 ≤ w y) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ y, w y ≤ M / (Fintype.card A : ℝ) ^ Fintype.card I) :
    mass w (fun y => ∃ e : L ≃ s, ∀ i, y (e i).val = a i) ≤
      (s.card.factorial : ℝ) * (M / (Fintype.card A : ℝ) ^ s.card) := by
  classical
  have he (e : L ≃ s) : (fun y : I → A => ∀ i, y (e i).val = a i) =
      (fun y : I → A => ∀ i : s, y i.val = a (e.symm i)) := by
    funext y
    apply propext
    constructor
    · intro h i
      simpa using h (e.symm i)
    · intro h i
      simpa using h (e i)
  have hc : Fintype.card (L ≃ s) ≤ s.card.factorial := by
    by_cases h : Nonempty (L ≃ s)
    · obtain ⟨e⟩ := h
      rw [Fintype.card_equiv e, Fintype.card_congr e, Fintype.card_coe]
    · have : IsEmpty (L ≃ s) := not_nonempty_iff.mp h
      simp
  calc
    _ ≤ ∑ e : L ≃ s, mass w (fun y => ∀ i, y (e i).val = a i) :=
      mass_exists_fintype _ w hw0
    _ ≤ ∑ _e : L ≃ s, M / (Fintype.card A : ℝ) ^ s.card := by
      apply sum_le_sum
      intro e _
      rw [he e]
      exact mass_pins_subtype s (a ∘ e.symm) w M hw
    _ ≤ _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)

def matchingCount (m n : ℕ) : ℕ := if m = n then n.factorial else 0

theorem mass_matchings_budget {L : Type*} [Fintype L] [Nonempty A]
    (s : Finset I) (a : L → A) (w : (I → A) → ℝ)
    (hw0 : ∀ y, 0 ≤ w y) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ y, w y ≤ M / (Fintype.card A : ℝ) ^ Fintype.card I) :
    mass w (fun y => ∃ e : L ≃ s, ∀ i, y (e i).val = a i) ≤
      (matchingCount (Fintype.card L) s.card : ℝ) *
        (M / (Fintype.card A : ℝ) ^ s.card) := by
  classical
  by_cases h : Fintype.card L = s.card
  · simpa only [matchingCount, h, ite_true] using mass_matchings s a w hw0 M hM hw
  · have he : ∀ y : I → A, ¬∃ e : L ≃ s, ∀ i, y (e i).val = a i := by
      rintro y ⟨e, _⟩
      exact h ((Fintype.card_congr e).trans (Fintype.card_coe s))
    simp [mass, he, matchingCount, h]

end Sarkozy.PartV.CubePins
