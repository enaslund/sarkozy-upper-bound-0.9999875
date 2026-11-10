module

public import Mathlib

/-!
# The disjoint-triple operator: the lower bound (`sec:frontier:empty-triple-negative`(b))

`paper/sections/12_labellings.tex`, lemma `sec:frontier:empty-triple-negative`(b), on the
functions of the unordered triple: on `3`-subsets of a set with `n ≥ 6` elements, the
disjointness form `⟨K f, f⟩ = ∑_{S ∩ S' = ∅} f(S) f(S')` (`disjForm`) satisfies
`⟨K f, f⟩ ≥ -C(n-4, 2) ∑ f²` (`disjForm_ge`), i.e. `T̄ = K/C(n-3, 3) ⪰ -3/(n-3) I`
(`disjOp_ge`).

**This replaces the paper's harmonic decomposition** by an elementary Cauchy–Schwarz argument.
With the shadows `N₁(x) = ∑_{S ∋ x} f(S)` (`shadow1`) and `g(A) = ∑_{S ⊇ A} f(S)` (`shadow2`,
`A` a `2`-set):

* inclusion–exclusion over `|S ∩ S'| ∈ {0,…,3}` (`disj_indicator`, `disjForm_eq`):
  `⟨Kf,f⟩ = (∑f)² - ∑ N₁² + ∑ g² - ∑ f²`;
* for `u` on `2`-sets with `∑ u = 0`, `∑_x (∑_{A ∋ x} u(A))² ≤ (n-2) ∑ u²` (`up2_sq_le`,
  Cauchy–Schwarz against `A ↦ ∑_{x ∈ A} h(x)`);
* `∑_S (∑_{A ⊆ S} u(A))² = (n-4) ∑ u² + ∑_x (∑_{A ∋ x} u(A))²` (`lift23_sq`), hence
  `∑ g² ≤ (2n-6) ∑ f²` when `∑ f = 0` (`shadow2_sq_le`);
* `∑_{A ∋ x} g(A) = 2 N₁(x)` (`up2_shadow2`), so `∑ N₁² ≤ (n-2)/4 · ∑ g²`;
* for `∑ f = 0` this gives `⟨Kf,f⟩ ≥ (1 - (n-2)/4)(2n-6) ∑f² - ∑ f² = -C(n-4,2) ∑ f²`, and the
  constants (eigenvalue `C(n-3,3) > 0`) are split off with `card_disjoint_triples`.

Further results of (a), (b) on the `3`-sets:
* `disjForm_le_of_mean_zero` (`n ≥ 7`): `⟨Kf,f⟩ ≤ C(n-4,2) ∑ f²` for `∑ f = 0`, from
  `a² ≤ F((n-4)a + b)`; hence `disjOp_abs_le`: **`‖T̄ - J‖ ≤ 3/(n-3)`**.
* `disjOp_eigen`: `g = [x₀ ∈ ·] - 3/n` satisfies `T̄ g = -3/(n-3) g`; `disjOp_attained`: `g` has mean
  zero and is nonzero, so **the lower constant is attained and `‖T̄ - J‖ = 3/(n-3)`**.
* `disjOp_one` (`T̄ 1 = 1`) and `disjOp_fixed` (`n ≥ 7`): **the eigenvalue `1` has the constants as
  its eigenspace**.
* The other eigenvalues of (a), with explicit eigenfunctions: `disjOp_eigen` (`λ₁ = -3/(n-3)`),
  `disjForm_eigen2` (`K f = (n-5) f` for `f = ([x₁∈·]-[y₁∈·])([x₂∈·]-[y₂∈·])`, i.e.
  `λ₂ = 6/((n-3)(n-4))`), `disjForm_eigen3` (`K h = -h` for `h = ∏_i ([x_i∈·]-[y_i∈·])`, i.e.
  `λ₃ = -6/((n-3)(n-4)(n-5))`). That these four eigenvalues exhaust the spectrum is not
  formalized (and not needed for (b)).

The transfer to ordered triples is `Sarkozy.TraceMixing.DisjointTripleOrdered`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `2`-subsets. -/
local notation "P2" =>
  Finset.filter (fun A : Finset α => Finset.card A = 2) (Finset.univ : Finset (Finset α))

/-- The `3`-subsets. -/
local notation "P3" =>
  Finset.filter (fun S : Finset α => Finset.card S = 3) (Finset.univ : Finset (Finset α))

/-- `N₁(x) = ∑_{S ∋ x} f(S)`. -/
noncomputable def shadow1 (f : Finset α → ℝ) (x : α) : ℝ := ∑ S ∈ P3, if x ∈ S then f S else 0

/-- `g(A) = ∑_{S ⊇ A} f(S)`. -/
noncomputable def shadow2 (f : Finset α → ℝ) (A : Finset α) : ℝ :=
  ∑ S ∈ P3, if A ⊆ S then f S else 0

/-- `(W u)(x) = ∑_{A ∋ x} u(A)` for `u` on `2`-sets. -/
noncomputable def up2 (u : Finset α → ℝ) (x : α) : ℝ := ∑ A ∈ P2, if x ∈ A then u A else 0

/-- `∑_{A ⊆ S} u(A)` for `u` on `2`-sets. -/
noncomputable def lift23 (u : Finset α → ℝ) (S : Finset α) : ℝ :=
  ∑ A ∈ P2, if A ⊆ S then u A else 0

/-- The disjointness form `∑_{S ∩ S' = ∅} f(S) f(S')` on `3`-sets. -/
noncomputable def disjForm (f : Finset α → ℝ) : ℝ :=
  ∑ S ∈ P3, ∑ S' ∈ P3, (if Disjoint S S' then 1 else 0) * (f S * f S')

/-- Expanding a sum of squares of "shadow" sums as a double sum with an incidence count. -/
theorem sum_sq_incidence {ι β : Type*} [DecidableEq β] (I : Finset ι) (Q : Finset β)
    (p : ι → β → Prop) [∀ i b, Decidable (p i b)] (f : β → ℝ) :
    ∑ i ∈ I, (∑ b ∈ Q, if p i b then f b else 0) ^ 2 =
      ∑ b ∈ Q, ∑ b' ∈ Q, ((I.filter fun i => p i b ∧ p i b').card : ℝ) * (f b * f b') := by
  simp only [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun b' _ => ?_
  rw [← Finset.sum_boole, Finset.sum_mul]
  refine sum_congr rfl fun i _ => ?_
  by_cases h1 : p i b <;> by_cases h2 : p i b' <;> simp [h1, h2]

omit [Fintype α] in
/-- The `2`-subsets of `U` through `x ∈ U`: `|U| - 1` of them. -/
theorem card_pairs_mem {U : Finset α} {x : α} (hx : x ∈ U) :
    ((U.powersetCard 2).filter fun A => x ∈ A).card = U.card - 1 := by
  have e : ((U.powersetCard 2).filter fun A => x ∈ A) = (U.erase x).image fun y => {x, y} := by
    ext A
    simp only [mem_filter, mem_powersetCard, mem_image, mem_erase]
    constructor
    · rintro ⟨⟨hAU, hA⟩, hxA⟩
      obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hA
      rw [mem_insert, mem_singleton] at hxA
      rcases hxA with rfl | rfl
      · exact ⟨b, ⟨Ne.symm hab, hAU (by simp)⟩, rfl⟩
      · exact ⟨a, ⟨hab, hAU (by simp)⟩, pair_comm _ _⟩
    · rintro ⟨y, ⟨hyx, hyU⟩, rfl⟩
      refine ⟨⟨?_, card_pair (Ne.symm hyx)⟩, by simp⟩
      intro z hz
      rw [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hyU
  rw [e, card_image_of_injOn, card_erase_of_mem hx]
  intro y hy y' _ h
  have h' : ({x, y} : Finset α) = {x, y'} := h
  have hy1 : y ∈ ({x, y'} : Finset α) := by
    rw [← h']
    simp
  rw [mem_insert, mem_singleton] at hy1
  rcases hy1 with h1 | h1
  · exact absurd h1 (mem_erase.mp (mem_coe.mp hy)).1
  · exact h1

/-- The `2`-sets through two distinct points: exactly one. -/
theorem card_pairs_through {x y : α} (hxy : x ≠ y) :
    ((P2).filter fun A => x ∈ A ∧ y ∈ A).card = 1 := by
  rw [card_eq_one]
  refine ⟨{x, y}, ?_⟩
  ext A
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨hA, hx, hy⟩
    symm
    apply eq_of_subset_of_card_le
    · intro z hz
      rw [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    · rw [hA, card_pair hxy]
  · rintro rfl
    exact ⟨card_pair hxy, mem_insert_self _ _, mem_insert_of_mem (mem_singleton_self _)⟩

/-- The `2`-sets through `x`: `n - 1` of them. -/
theorem card_pairs_univ (x : α) :
    ((P2).filter fun A => x ∈ A).card = Fintype.card α - 1 := by
  have e : ((P2).filter fun A => x ∈ A) =
      ((univ : Finset α).powersetCard 2).filter fun A => x ∈ A := by
    ext A
    simp [mem_powersetCard]
  rw [e, card_pairs_mem (mem_univ x), card_univ]

/-- The `2`-subsets of a `3`-set through a point of it: two of them. -/
theorem card_pairs_in_triple {S : Finset α} (hS : S.card = 3) {x : α} :
    ((P2).filter fun A => x ∈ A ∧ A ⊆ S).card = if x ∈ S then 2 else 0 := by
  have e : ((P2).filter fun A => x ∈ A ∧ A ⊆ S) = (S.powersetCard 2).filter fun A => x ∈ A := by
    ext A
    simp only [mem_filter, mem_univ, true_and, mem_powersetCard]
    tauto
  rw [e]
  split_ifs with hx
  · rw [card_pairs_mem hx, hS]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro A hA hxA
    exact hx ((mem_powersetCard.mp hA).1 hxA)

/-- The `2`-subsets of a `3`-set: three of them. -/
theorem card_pairs_sub {S : Finset α} (hS : S.card = 3) :
    ((P2).filter fun A => A ⊆ S).card = 3 := by
  have e : ((P2).filter fun A => A ⊆ S) = S.powersetCard 2 := by
    ext A
    simp only [mem_filter, mem_univ, true_and, mem_powersetCard]
    tauto
  rw [e, card_powersetCard, hS]
  rfl

/-- The `3`-sets containing a `2`-set `B`: `n - 2` of them. -/
theorem card_triples_over_pair {B : Finset α} (hB : B.card = 2) :
    ((P3).filter fun S => B ⊆ S).card = Fintype.card α - 2 := by
  have e : ((P3).filter fun S => B ⊆ S) = (univ \ B).image fun z => insert z B := by
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_sdiff]
    constructor
    · rintro ⟨hS, hBS⟩
      have hcard : (S \ B).card = 1 := by
        rw [card_sdiff_of_subset hBS, hS, hB]
      obtain ⟨z, hz⟩ := card_eq_one.mp hcard
      have hzS : z ∈ S \ B := by rw [hz]; exact mem_singleton_self z
      refine ⟨z, (mem_sdiff.mp hzS).2, ?_⟩
      ext w
      simp only [mem_insert]
      constructor
      · rintro (rfl | hw)
        · exact (mem_sdiff.mp hzS).1
        · exact hBS hw
      · intro hw
        by_cases hwB : w ∈ B
        · exact Or.inr hwB
        · have : w ∈ S \ B := mem_sdiff.mpr ⟨hw, hwB⟩
          rw [hz, mem_singleton] at this
          exact Or.inl this
    · rintro ⟨z, hzB, rfl⟩
      exact ⟨by rw [card_insert_of_notMem hzB, hB], subset_insert _ _⟩
  rw [e, card_image_of_injOn, card_sdiff_of_subset (subset_univ _), card_univ, hB]
  intro z hz z' hz' h
  have h' : insert z B = insert z' B := h
  have hzB : z ∉ B := (mem_sdiff.mp (mem_coe.mp hz)).2
  have : z ∈ insert z' B := by rw [← h']; exact mem_insert_self z B
  rcases mem_insert.mp this with h1 | h1
  · exact h1
  · exact absurd h1 hzB

/-- **The number of `3`-sets containing two `2`-sets** `A, A'`:
`(n - 4)[A = A'] + |A ∩ A'|`. -/
theorem card_triples_over_two (hn : 4 ≤ Fintype.card α) {A A' : Finset α} (hA : A.card = 2)
    (hA' : A'.card = 2) :
    (((P3).filter fun S => A ⊆ S ∧ A' ⊆ S).card : ℝ) =
      (if A = A' then (Fintype.card α : ℝ) - 4 else 0) + ((A ∩ A').card : ℝ) := by
  have e : ((P3).filter fun S => A ⊆ S ∧ A' ⊆ S) = (P3).filter fun S => A ∪ A' ⊆ S := by
    ext S
    simp [union_subset_iff]
  rw [e]
  have hU : (A ∪ A').card + (A ∩ A').card = 4 := by
    rw [card_union_add_card_inter, hA, hA']
  by_cases hAA : A = A'
  · subst hAA
    rw [union_self, inter_self, hA, ite_eq_left rfl, card_triples_over_pair hA]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  · rw [ite_eq_right hAA, zero_add]
    have hi : (A ∩ A').card ≤ 1 := by
      by_contra hc
      push Not at hc
      have h2 : (A ∩ A').card = 2 := le_antisymm (hA ▸ card_le_card inter_subset_left) hc
      have h3 : A ∩ A' = A := eq_of_subset_of_card_le inter_subset_left (by rw [h2, hA])
      have h4 : A ∩ A' = A' := eq_of_subset_of_card_le inter_subset_right (by rw [h2, hA'])
      exact hAA (h3.symm.trans h4)
    interval_cases hk : (A ∩ A').card
    · -- `|A ∪ A'| = 4`: no `3`-set contains it
      have h4 : (A ∪ A').card = 4 := by omega
      rw [Nat.cast_zero]
      norm_cast
      rw [card_eq_zero, filter_eq_empty_iff]
      intro S hS hsub
      have := card_le_card hsub
      rw [h4, (mem_filter.mp hS).2] at this
      omega
    · -- `|A ∪ A'| = 3`: exactly one
      have h3 : (A ∪ A').card = 3 := by omega
      rw [Nat.cast_one]
      norm_cast
      rw [card_eq_one]
      refine ⟨A ∪ A', ?_⟩
      ext S
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨hS, hsub⟩
        exact (eq_of_subset_of_card_le hsub (by rw [hS, h3])).symm
      · rintro rfl
        exact ⟨h3, subset_rfl⟩

omit [Fintype α] in
/-- **Inclusion–exclusion for disjointness of `3`-sets.** -/
theorem disj_indicator {S S' : Finset α} (hS : S.card = 3) (hS' : S'.card = 3) :
    (if Disjoint S S' then (1 : ℝ) else 0) =
      1 - ((S ∩ S').card : ℝ) + (((S ∩ S').card.choose 2 : ℕ) : ℝ) - (if S = S' then 1 else 0) := by
  have hk : (S ∩ S').card ≤ 3 := hS ▸ card_le_card inter_subset_left
  have hdisj : Disjoint S S' ↔ (S ∩ S').card = 0 := by
    rw [card_eq_zero, disjoint_iff_inter_eq_empty]
  have heq : S = S' ↔ (S ∩ S').card = 3 := by
    constructor
    · rintro rfl
      rw [inter_self, hS]
    · intro h3
      have h1 : S ∩ S' = S := eq_of_subset_of_card_le inter_subset_left (by rw [h3, hS])
      have h2 : S ∩ S' = S' := eq_of_subset_of_card_le inter_subset_right (by rw [h3, hS'])
      exact h1.symm.trans h2
  by_cases h0 : (S ∩ S').card = 0
  · rw [ite_eq_left (hdisj.mpr h0), ite_eq_right (fun h => by rw [heq.mp h] at h0; exact absurd h0 (by norm_num)),
      h0]
    norm_num
  · rw [ite_eq_right (fun h => h0 (hdisj.mp h))]
    by_cases h3 : (S ∩ S').card = 3
    · rw [ite_eq_left (heq.mpr h3), h3]
      norm_num [Nat.choose]
    · rw [ite_eq_right (fun h => h3 (heq.mp h))]
      have : (S ∩ S').card = 1 ∨ (S ∩ S').card = 2 := by omega
      rcases this with h | h
      · rw [h]
        norm_num
      · rw [h]
        norm_num [Nat.choose]

/-- **Inclusion–exclusion**: `⟨Kf,f⟩ = (∑f)² - ∑ N₁² + ∑ g² - ∑ f²`. -/
theorem disjForm_eq (f : Finset α → ℝ) :
    disjForm f = (∑ S ∈ P3, f S) ^ 2 - ∑ x, shadow1 f x ^ 2 + ∑ A ∈ P2, shadow2 f A ^ 2 -
      ∑ S ∈ P3, f S ^ 2 := by
  have h1 : ∑ x, shadow1 f x ^ 2 =
      ∑ S ∈ P3, ∑ S' ∈ P3, ((S ∩ S').card : ℝ) * (f S * f S') := by
    unfold shadow1
    rw [sum_sq_incidence univ (P3) (fun x S => x ∈ S) f]
    refine sum_congr rfl fun S _ => sum_congr rfl fun S' _ => ?_
    have e : ((univ : Finset α).filter fun x => x ∈ S ∧ x ∈ S').card = (S ∩ S').card := by
      congr 1
      ext x
      simp
    rw [e]
  have h2 : ∑ A ∈ P2, shadow2 f A ^ 2 =
      ∑ S ∈ P3, ∑ S' ∈ P3, (((S ∩ S').card.choose 2 : ℕ) : ℝ) * (f S * f S') := by
    unfold shadow2
    rw [sum_sq_incidence (P2) (P3) (fun A S => A ⊆ S) f]
    refine sum_congr rfl fun S _ => sum_congr rfl fun S' _ => ?_
    have e : ((P2).filter fun A => A ⊆ S ∧ A ⊆ S').card = (S ∩ S').card.choose 2 := by
      rw [← card_powersetCard]
      congr 1
      ext A
      simp only [mem_filter, mem_univ, true_and, mem_powersetCard, subset_inter_iff]
      tauto
    rw [e]
  have h3 : (∑ S ∈ P3, f S) ^ 2 = ∑ S ∈ P3, ∑ S' ∈ P3, (1 : ℝ) * (f S * f S') := by
    rw [sq, Finset.sum_mul_sum]
    simp only [one_mul]
  have h4 : ∑ S ∈ P3, f S ^ 2 =
      ∑ S ∈ P3, ∑ S' ∈ P3, (if S = S' then (1 : ℝ) else 0) * (f S * f S') := by
    refine sum_congr rfl fun S hS => ?_
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, hS, ite_true]
    ring
  rw [h1, h2, h3, h4]
  unfold disjForm
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun S hS => sum_congr rfl fun S' hS' => ?_
  rw [disj_indicator (mem_filter.mp hS).2 (mem_filter.mp hS').2]
  ring

/-- `∑_x (∑_{A ∋ x} u(A))² ≤ (n-2) ∑ u²` for `u` on `2`-sets with `∑ u = 0`. -/
theorem up2_sq_le (hn : 2 ≤ Fintype.card α) (u : Finset α → ℝ) (hu : ∑ A ∈ P2, u A = 0) :
    ∑ x, up2 u x ^ 2 ≤ ((Fintype.card α : ℝ) - 2) * ∑ A ∈ P2, u A ^ 2 := by
  have hi : ∑ x, up2 u x ^ 2 = ∑ A ∈ P2, u A * ∑ x, (if x ∈ A then up2 u x else 0) := by
    have e1 (x : α) : up2 u x ^ 2 = ∑ A ∈ P2, (if x ∈ A then u A * up2 u x else 0) := by
      rw [sq]
      nth_rewrite 1 [up2]
      rw [Finset.sum_mul]
      refine sum_congr rfl fun A _ => ?_
      split_ifs <;> ring
    simp only [e1]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun A _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  have hii : ∑ A ∈ P2, (∑ x, if x ∈ A then up2 u x else 0) ^ 2 =
      ((Fintype.card α : ℝ) - 2) * ∑ x, up2 u x ^ 2 + (∑ x, up2 u x) ^ 2 := by
    rw [sum_sq_incidence (P2) univ (fun A x => x ∈ A) (up2 u)]
    have hc (x y : α) : (((P2).filter fun A => x ∈ A ∧ y ∈ A).card : ℝ) =
        if x = y then (Fintype.card α : ℝ) - 1 else 1 := by
      split_ifs with hxy
      · subst hxy
        simp only [and_self]
        rw [card_pairs_univ x, Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨x⟩), Nat.cast_one]
      · rw [card_pairs_through hxy, Nat.cast_one]
    simp only [hc]
    have e2 (x : α) : ∑ y, (if x = y then (Fintype.card α : ℝ) - 1 else 1) * (up2 u x * up2 u y) =
        up2 u x * ∑ y, up2 u y + ((Fintype.card α : ℝ) - 2) * up2 u x ^ 2 := by
      have e3 (y : α) : (if x = y then (Fintype.card α : ℝ) - 1 else 1) * (up2 u x * up2 u y) =
          up2 u x * up2 u y +
            (if x = y then ((Fintype.card α : ℝ) - 2) * (up2 u x * up2 u y) else 0) := by
        split_ifs <;> ring
      simp only [e3, Finset.sum_add_distrib, Finset.sum_ite_eq, mem_univ, ite_true,
        ← Finset.mul_sum]
      ring
    simp only [e2, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hiii : ∑ x, up2 u x = 0 := by
    unfold up2
    rw [Finset.sum_comm]
    have e (A : Finset α) (hA : A ∈ P2) : ∑ x, (if x ∈ A then u A else 0) = 2 * u A := by
      rw [Finset.sum_ite_mem, univ_inter, sum_const, (mem_filter.mp hA).2, nsmul_eq_mul]
      norm_num
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, hu, mul_zero]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (P2) u
    (fun A => ∑ x, if x ∈ A then up2 u x else 0)
  rw [← hi, hii, hiii] at hcs
  have hH0 : 0 ≤ ∑ x, up2 u x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hU0 : 0 ≤ ∑ A ∈ P2, u A ^ 2 := Finset.sum_nonneg fun A _ => sq_nonneg _
  have hn' : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  rcases hH0.lt_or_eq with hpos | hzero
  · have : (∑ x, up2 u x ^ 2) * (∑ x, up2 u x ^ 2) ≤
        (((Fintype.card α : ℝ) - 2) * ∑ A ∈ P2, u A ^ 2) * (∑ x, up2 u x ^ 2) := by
      nlinarith [hcs]
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]
    exact mul_nonneg (by linarith) hU0

/-- `∑_S (∑_{A ⊆ S} u(A))² = (n-4) ∑ u² + ∑_x (∑_{A ∋ x} u(A))²`. -/
theorem lift23_sq (hn : 4 ≤ Fintype.card α) (u : Finset α → ℝ) :
    ∑ S ∈ P3, lift23 u S ^ 2 =
      ((Fintype.card α : ℝ) - 4) * ∑ A ∈ P2, u A ^ 2 + ∑ x, up2 u x ^ 2 := by
  unfold lift23 up2
  rw [sum_sq_incidence (P3) (P2) (fun S A => A ⊆ S) u,
    sum_sq_incidence univ (P2) (fun x A => x ∈ A) u]
  have hsq : ∑ A ∈ P2, u A ^ 2 =
      ∑ A ∈ P2, ∑ A' ∈ P2, (if A = A' then (1 : ℝ) else 0) * (u A * u A') := by
    refine sum_congr rfl fun A hA => ?_
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, hA, ite_true]
    ring
  rw [hsq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun A hA => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun A' hA' => ?_
  rw [card_triples_over_two hn (mem_filter.mp hA).2 (mem_filter.mp hA').2]
  have e : (((univ : Finset α).filter fun x => x ∈ A ∧ x ∈ A').card : ℝ) =
      ((A ∩ A').card : ℝ) := by
    congr 2
    ext x
    simp
  rw [e]
  split_ifs <;> ring

/-- `∑_{A} g(A) = 3 ∑ f`. -/
theorem shadow2_sum (f : Finset α → ℝ) : ∑ A ∈ P2, shadow2 f A = 3 * ∑ S ∈ P3, f S := by
  unfold shadow2
  rw [Finset.sum_comm, Finset.mul_sum]
  refine sum_congr rfl fun S hS => ?_
  rw [← Finset.sum_filter, sum_const, card_pairs_sub (mem_filter.mp hS).2, nsmul_eq_mul]
  norm_num

/-- `∑_{A ∋ x} g(A) = 2 N₁(x)`. -/
theorem up2_shadow2 (f : Finset α → ℝ) (x : α) : up2 (shadow2 f) x = 2 * shadow1 f x := by
  unfold up2 shadow2 shadow1
  have e (A : Finset α) : (if x ∈ A then ∑ S ∈ P3, (if A ⊆ S then f S else 0) else 0) =
      ∑ S ∈ P3, (if x ∈ A ∧ A ⊆ S then f S else 0) := by
    split_ifs with hx
    · exact sum_congr rfl fun S _ => by simp [hx]
    · simp [hx]
  simp only [e]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine sum_congr rfl fun S hS => ?_
  rw [← Finset.sum_filter, sum_const, card_pairs_in_triple (mem_filter.mp hS).2, nsmul_eq_mul]
  split_ifs <;> simp

/-- **`∑ g² ≤ (2n-6) ∑ f²`** for `∑ f = 0`. -/
theorem shadow2_sq_le (hn : 4 ≤ Fintype.card α) (f : Finset α → ℝ) (hf : ∑ S ∈ P3, f S = 0) :
    ∑ A ∈ P2, shadow2 f A ^ 2 ≤ (2 * (Fintype.card α : ℝ) - 6) * ∑ S ∈ P3, f S ^ 2 := by
  have hg0 : ∑ A ∈ P2, shadow2 f A = 0 := by rw [shadow2_sum, hf, mul_zero]
  have hG : ∑ A ∈ P2, shadow2 f A ^ 2 = ∑ S ∈ P3, f S * lift23 (shadow2 f) S := by
    have e1 (A : Finset α) :
        shadow2 f A ^ 2 = ∑ S ∈ P3, (if A ⊆ S then f S * shadow2 f A else 0) := by
      rw [sq]
      nth_rewrite 1 [shadow2]
      rw [Finset.sum_mul]
      refine sum_congr rfl fun S _ => ?_
      split_ifs <;> ring
    simp only [e1]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun S _ => ?_
    unfold lift23
    rw [Finset.mul_sum]
    refine sum_congr rfl fun A _ => ?_
    split_ifs <;> ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (P3) f (lift23 (shadow2 f))
  rw [← hG] at hcs
  have hL := lift23_sq hn (shadow2 f)
  have hup := up2_sq_le (by omega) (shadow2 f) hg0
  have hn' : (4 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hG0 : 0 ≤ ∑ A ∈ P2, shadow2 f A ^ 2 := Finset.sum_nonneg fun A _ => sq_nonneg _
  have hF0 : 0 ≤ ∑ S ∈ P3, f S ^ 2 := Finset.sum_nonneg fun S _ => sq_nonneg _
  have hlift : ∑ S ∈ P3, lift23 (shadow2 f) S ^ 2 ≤
      (2 * (Fintype.card α : ℝ) - 6) * ∑ A ∈ P2, shadow2 f A ^ 2 := by
    rw [hL]
    nlinarith [hup]
  have h2 : (∑ A ∈ P2, shadow2 f A ^ 2) ^ 2 ≤
      (∑ S ∈ P3, f S ^ 2) * ((2 * (Fintype.card α : ℝ) - 6) * ∑ A ∈ P2, shadow2 f A ^ 2) :=
    hcs.trans (mul_le_mul_of_nonneg_left hlift hF0)
  rcases hG0.lt_or_eq with hpos | hzero
  · have : (∑ A ∈ P2, shadow2 f A ^ 2) * (∑ A ∈ P2, shadow2 f A ^ 2) ≤
        ((2 * (Fintype.card α : ℝ) - 6) * ∑ S ∈ P3, f S ^ 2) * (∑ A ∈ P2, shadow2 f A ^ 2) := by
      nlinarith [h2]
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]
    exact mul_nonneg (by linarith) hF0

/-- **`⟨Kf,f⟩ ≥ -C(n-4,2) ∑ f²` for `∑ f = 0`** (`n ≥ 6`). -/
theorem disjForm_ge_of_mean_zero (hn : 6 ≤ Fintype.card α) (f : Finset α → ℝ)
    (hf : ∑ S ∈ P3, f S = 0) :
    -(((Fintype.card α : ℝ) - 4) * ((Fintype.card α : ℝ) - 5) / 2) * ∑ S ∈ P3, f S ^ 2 ≤
      disjForm f := by
  rw [disjForm_eq, hf]
  have hE : ∑ x, shadow1 f x ^ 2 = 1 / 4 * ∑ x, up2 (shadow2 f) x ^ 2 := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [up2_shadow2]
    ring
  have hg0 : ∑ A ∈ P2, shadow2 f A = 0 := by rw [shadow2_sum, hf, mul_zero]
  have hup := up2_sq_le (by omega) (shadow2 f) hg0
  have hsh := shadow2_sq_le (by omega) f hf
  have hn' : (6 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  rw [hE]
  have hint := mul_le_mul_of_nonneg_left hsh (by linarith : (0 : ℝ) ≤ ((Fintype.card α : ℝ) - 6) / 4)
  nlinarith [hup, hint]

/-- The `3`-sets disjoint from a `3`-set `S'`: `C(n-3, 3)` of them. -/
theorem card_disjoint_triples {S' : Finset α} (hS' : S'.card = 3) :
    ((P3).filter fun S => Disjoint S S').card = (Fintype.card α - 3).choose 3 := by
  have e : ((P3).filter fun S => Disjoint S S') = (univ \ S').powersetCard 3 := by
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_powersetCard]
    constructor
    · rintro ⟨hS, hd⟩
      exact ⟨fun z hz => mem_sdiff.mpr ⟨mem_univ z, disjoint_left.mp hd hz⟩, hS⟩
    · rintro ⟨hsub, hS⟩
      exact ⟨hS, disjoint_left.mpr fun z hz hz' => (mem_sdiff.mp (hsub hz)).2 hz'⟩
  rw [e, card_powersetCard, card_sdiff_of_subset (subset_univ _), card_univ, hS']

/-- **`sec:frontier:empty-triple-negative`(b) on `3`-sets: `⟨K f, f⟩ ≥ -C(n-4, 2) ∑ f²`**
(`n ≥ 6`), for every `f`. -/
theorem disjForm_ge (hn : 6 ≤ Fintype.card α) (f : Finset α → ℝ) :
    -(((Fintype.card α : ℝ) - 4) * ((Fintype.card α : ℝ) - 5) / 2) * ∑ S ∈ P3, f S ^ 2 ≤
      disjForm f := by
  by_cases hP : (P3).card = 0
  · rw [card_eq_zero] at hP
    simp [disjForm, hP]
  set N : ℝ := ((P3).card : ℝ) with hN
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact_mod_cast hP
  set m : ℝ := (∑ S ∈ P3, f S) / N with hm
  set f₀ : Finset α → ℝ := fun S => f S - m with hf₀def
  have hf₀ : ∑ S ∈ P3, f₀ S = 0 := by
    simp only [hf₀def, Finset.sum_sub_distrib, sum_const, nsmul_eq_mul]
    rw [← hN, hm, mul_div_cancel₀ _ hN0, sub_self]
  have h0 := disjForm_ge_of_mean_zero hn f₀ hf₀
  have hκ (S : Finset α) (hS : S ∈ P3) :
      ∑ S' ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) = ((Fintype.card α - 3).choose 3 : ℝ) := by
    rw [Finset.sum_boole]
    have e : ((P3).filter fun S' => Disjoint S S') = (P3).filter fun S' => Disjoint S' S := by
      ext S'
      simp [disjoint_comm]
    rw [e, card_disjoint_triples (mem_filter.mp hS).2]
  have hκ' (S' : Finset α) (hS' : S' ∈ P3) :
      ∑ S ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) = ((Fintype.card α - 3).choose 3 : ℝ) := by
    rw [Finset.sum_boole, card_disjoint_triples (mem_filter.mp hS').2]
  have hc : ∑ S' ∈ P3, f₀ S' * ∑ S ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) =
      ∑ S ∈ P3, ∑ S' ∈ P3, f₀ S' * (if Disjoint S S' then (1 : ℝ) else 0) := by
    rw [Finset.sum_comm]
    exact sum_congr rfl fun S' _ => by rw [Finset.mul_sum]
  have hexp : disjForm f = disjForm f₀ +
      m * ∑ S ∈ P3, f₀ S * ∑ S' ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) +
      m * ∑ S' ∈ P3, f₀ S' * ∑ S ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) +
      m ^ 2 * ∑ S ∈ P3, ∑ S' ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) := by
    rw [hc]
    unfold disjForm
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_congr rfl fun S _ => sum_congr rfl fun S' _ => ?_
    simp only [hf₀def]
    ring
  have hc1 : ∑ S ∈ P3, f₀ S * ∑ S' ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) = 0 := by
    have e : ∑ S ∈ P3, f₀ S * ∑ S' ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) =
        ∑ S ∈ P3, f₀ S * ((Fintype.card α - 3).choose 3 : ℝ) :=
      sum_congr rfl fun S hS => by rw [hκ S hS]
    rw [e, ← Finset.sum_mul, hf₀, zero_mul]
  have hc2 : ∑ S' ∈ P3, f₀ S' * ∑ S ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) = 0 := by
    have e : ∑ S' ∈ P3, f₀ S' * ∑ S ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) =
        ∑ S' ∈ P3, f₀ S' * ((Fintype.card α - 3).choose 3 : ℝ) :=
      sum_congr rfl fun S' hS' => by rw [hκ' S' hS']
    rw [e, ← Finset.sum_mul, hf₀, zero_mul]
  have hsq : ∑ S ∈ P3, f S ^ 2 = ∑ S ∈ P3, f₀ S ^ 2 + m ^ 2 * N := by
    have e : ∑ S ∈ P3, f S ^ 2 = ∑ S ∈ P3, (f₀ S ^ 2 + 2 * m * f₀ S + m ^ 2) :=
      sum_congr rfl fun S _ => by simp only [hf₀def]; ring
    rw [e, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hf₀, sum_const,
      nsmul_eq_mul, ← hN]
    ring
  have hD : 0 ≤ ∑ S ∈ P3, ∑ S' ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun S _ => Finset.sum_nonneg fun S' _ => by split_ifs <;> norm_num
  have hn' : (6 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hC : 0 ≤ ((Fintype.card α : ℝ) - 4) * ((Fintype.card α : ℝ) - 5) / 2 :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hNn : 0 ≤ N := by rw [hN]; exact Nat.cast_nonneg _
  rw [hexp, hc1, hc2, hsq]
  nlinarith [h0, mul_nonneg (sq_nonneg m) hD, mul_nonneg hC (mul_nonneg (sq_nonneg m) hNn)]

omit [Fintype α] [DecidableEq α] in
/-- `C(k + 3, 3) = (k + 3)(k + 2)(k + 1)/6`. -/
theorem choose_three_cast (k : ℕ) :
    (((k + 3).choose 3 : ℕ) : ℝ) = ((k : ℝ) + 3) * ((k : ℝ) + 2) * ((k : ℝ) + 1) / 6 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (k + 3) 3
  have hd : (k + 3).descFactorial 3 = (k + 3) * (k + 2) * (k + 1) := by
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
    have e1 : k + 3 - 2 = k + 1 := by omega
    have e2 : k + 3 - 1 = k + 2 := by omega
    rw [e1, e2, Nat.sub_zero]
    ring
  rw [hd] at h
  have h6 : (Nat.factorial 3) = 6 := rfl
  rw [h6] at h
  have hR : (((k + 3) * (k + 2) * (k + 1) : ℕ) : ℝ) = ((6 * (k + 3).choose 3 : ℕ) : ℝ) := by
    rw [h]
  push_cast at hR
  linarith

/-- `T̄ g(S) = C(n-3, 3)⁻¹ ∑_{S' ∩ S = ∅} g(S')`, the disjoint-triple operator on the functions
of the unordered triple. -/
noncomputable def disjOp (g : Finset α → ℝ) (S : Finset α) : ℝ :=
  (((Fintype.card α - 3).choose 3 : ℕ) : ℝ)⁻¹ * ∑ S' ∈ P3, (if Disjoint S S' then g S' else 0)

/-- **`T̄ ⪰ -3/(n-3) I`** on the functions of the unordered triple (`n ≥ 6`), for the uniform
(equivalently, counting) inner product on `3`-sets. -/
theorem disjOp_ge (hn : 6 ≤ Fintype.card α) (g : Finset α → ℝ) :
    -(3 / ((Fintype.card α : ℝ) - 3)) * ∑ S ∈ P3, g S ^ 2 ≤ ∑ S ∈ P3, g S * disjOp g S := by
  have hform : ∑ S ∈ P3, g S * disjOp g S =
      (((Fintype.card α - 3).choose 3 : ℕ) : ℝ)⁻¹ * disjForm g := by
    unfold disjOp disjForm
    rw [Finset.mul_sum]
    refine sum_congr rfl fun S _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun S' _ => ?_
    split_ifs <;> ring
  rw [hform]
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card α = k + 6 := ⟨Fintype.card α - 6, by omega⟩
  have hk3 : Fintype.card α - 3 = k + 3 := by omega
  have hcast : (Fintype.card α : ℝ) = (k : ℝ) + 6 := by rw [hk]; push_cast; ring
  have h := disjForm_ge hn g
  rw [hk3, choose_three_cast k]
  rw [hcast] at h ⊢
  have e1 : (k : ℝ) + 6 - 3 = (k : ℝ) + 3 := by ring
  have e2 : (k : ℝ) + 6 - 4 = (k : ℝ) + 2 := by ring
  have e3 : (k : ℝ) + 6 - 5 = (k : ℝ) + 1 := by ring
  rw [e1]
  rw [e2, e3] at h
  have hk3' : (k : ℝ) + 3 ≠ 0 := by positivity
  have hk2' : (k : ℝ) + 2 ≠ 0 := by positivity
  have hk1' : (k : ℝ) + 1 ≠ 0 := by positivity
  have hpos : 0 < ((k : ℝ) + 3) * ((k : ℝ) + 2) * ((k : ℝ) + 1) / 6 := by positivity
  calc -(3 / ((k : ℝ) + 3)) * ∑ S ∈ P3, g S ^ 2
      = (((k : ℝ) + 3) * ((k : ℝ) + 2) * ((k : ℝ) + 1) / 6)⁻¹ *
          (-(((k : ℝ) + 2) * ((k : ℝ) + 1) / 2) * ∑ S ∈ P3, g S ^ 2) := by
        field_simp
        ring
    _ ≤ (((k : ℝ) + 3) * ((k : ℝ) + 2) * ((k : ℝ) + 1) / 6)⁻¹ * disjForm g :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hpos.le)

/-- **`⟨Kf,f⟩ ≤ C(n-4,2) ∑ f²` for `∑ f = 0`** (`n ≥ 7`). With `a = ∑ g²`, `b = ∑_x (∑_{A∋x} g)²`
and `F = ∑ f²`, Cauchy–Schwarz gives `a² ≤ F((n-4)a + b)`, hence `16F(a - b/4) ≤ n²F²`, and
`⟨Kf,f⟩ = a - b/4 - F ≤ (n²/16 - 1)F ≤ C(n-4,2) F`. -/
theorem disjForm_le_of_mean_zero (hn : 7 ≤ Fintype.card α) (f : Finset α → ℝ)
    (hf : ∑ S ∈ P3, f S = 0) :
    disjForm f ≤
      ((Fintype.card α : ℝ) - 4) * ((Fintype.card α : ℝ) - 5) / 2 * ∑ S ∈ P3, f S ^ 2 := by
  rw [disjForm_eq, hf]
  have hE : ∑ x, shadow1 f x ^ 2 = 1 / 4 * ∑ x, up2 (shadow2 f) x ^ 2 := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [up2_shadow2]
    ring
  have hG : ∑ A ∈ P2, shadow2 f A ^ 2 = ∑ S ∈ P3, f S * lift23 (shadow2 f) S := by
    have e1 (A : Finset α) :
        shadow2 f A ^ 2 = ∑ S ∈ P3, (if A ⊆ S then f S * shadow2 f A else 0) := by
      rw [sq]
      nth_rewrite 1 [shadow2]
      rw [Finset.sum_mul]
      refine sum_congr rfl fun S _ => ?_
      split_ifs <;> ring
    simp only [e1]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun S _ => ?_
    unfold lift23
    rw [Finset.mul_sum]
    refine sum_congr rfl fun A _ => ?_
    split_ifs <;> ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (P3) f (lift23 (shadow2 f))
  rw [← hG, lift23_sq (by omega) (shadow2 f)] at hcs
  rw [hE]
  have hn' : (7 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hF0 : 0 ≤ ∑ S ∈ P3, f S ^ 2 := Finset.sum_nonneg fun S _ => sq_nonneg _
  have hb0 : 0 ≤ ∑ x, up2 (shadow2 f) x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have ha0 : 0 ≤ ∑ A ∈ P2, shadow2 f A ^ 2 := Finset.sum_nonneg fun A _ => sq_nonneg _
  set a := ∑ A ∈ P2, shadow2 f A ^ 2
  set b := ∑ x, up2 (shadow2 f) x ^ 2
  set Fq := ∑ S ∈ P3, f S ^ 2
  set n : ℝ := (Fintype.card α : ℝ)
  have key : 16 * Fq * (a - b / 4) ≤ n ^ 2 * Fq ^ 2 := by
    nlinarith [hcs, sq_nonneg (2 * a - n * Fq)]
  have hC : n ^ 2 / 16 - 1 ≤ (n - 4) * (n - 5) / 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n - 7) (by linarith : (0 : ℝ) ≤ 7 * n - 23)]
  rcases hF0.lt_or_eq with hpos | hzero
  · have h1 : a - b / 4 ≤ n ^ 2 / 16 * Fq := by
      have h2 : 16 * Fq * (a - b / 4) ≤ 16 * Fq * (n ^ 2 / 16 * Fq) := by nlinarith [key]
      exact le_of_mul_le_mul_left h2 (by positivity)
    nlinarith [h1, mul_le_mul_of_nonneg_right hC hF0]
  · have ha : a = 0 := by
      rw [← hzero] at hcs
      nlinarith [sq_nonneg a]
    rw [← hzero, ha]
    nlinarith [hb0]

/-- **`‖T̄ - J‖ ≤ 3/(n-3)`**: on the mean-zero functions of the unordered triple,
`|⟨T̄ g, g⟩| ≤ 3/(n-3) ‖g‖²` (`n ≥ 7`; `T̄` is self-adjoint, fixes the constants and preserves
the mean-zero functions). -/
theorem disjOp_abs_le (hn : 7 ≤ Fintype.card α) (g : Finset α → ℝ) (hg : ∑ S ∈ P3, g S = 0) :
    |∑ S ∈ P3, g S * disjOp g S| ≤ 3 / ((Fintype.card α : ℝ) - 3) * ∑ S ∈ P3, g S ^ 2 := by
  have hform : ∑ S ∈ P3, g S * disjOp g S =
      (((Fintype.card α - 3).choose 3 : ℕ) : ℝ)⁻¹ * disjForm g := by
    unfold disjOp disjForm
    rw [Finset.mul_sum]
    refine sum_congr rfl fun S _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun S' _ => ?_
    split_ifs <;> ring
  rw [hform]
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card α = k + 6 := ⟨Fintype.card α - 6, by omega⟩
  have hk3 : Fintype.card α - 3 = k + 3 := by omega
  have hcast : (Fintype.card α : ℝ) = (k : ℝ) + 6 := by rw [hk]; push_cast; ring
  have hlo := disjForm_ge_of_mean_zero (by omega) g hg
  have hhi := disjForm_le_of_mean_zero hn g hg
  rw [hk3, choose_three_cast k]
  rw [hcast] at hlo hhi ⊢
  have e1 : (k : ℝ) + 6 - 3 = (k : ℝ) + 3 := by ring
  have e2 : (k : ℝ) + 6 - 4 = (k : ℝ) + 2 := by ring
  have e3 : (k : ℝ) + 6 - 5 = (k : ℝ) + 1 := by ring
  rw [e1]
  rw [e2, e3] at hlo hhi
  have hk3' : (k : ℝ) + 3 ≠ 0 := by positivity
  have hpos : 0 < ((k : ℝ) + 3) * ((k : ℝ) + 2) * ((k : ℝ) + 1) / 6 := by positivity
  have hid : 3 / ((k : ℝ) + 3) * ∑ S ∈ P3, g S ^ 2 =
      (((k : ℝ) + 3) * ((k : ℝ) + 2) * ((k : ℝ) + 1) / 6)⁻¹ *
        (((k : ℝ) + 2) * ((k : ℝ) + 1) / 2 * ∑ S ∈ P3, g S ^ 2) := by
    field_simp
    ring
  rw [hid, abs_le]
  have hinv : 0 ≤ (((k : ℝ) + 3) * ((k : ℝ) + 2) * ((k : ℝ) + 1) / 6)⁻¹ := inv_nonneg.mpr hpos.le
  constructor
  · have := mul_le_mul_of_nonneg_left hlo hinv
    linarith
  · exact mul_le_mul_of_nonneg_left hhi hinv

/-- The `3`-sets through `x₀ ∉ S` disjoint from `S` (`|S| = 3`): `C(n-4, 2)` of them. -/
theorem card_disjoint_through {S : Finset α} (hS : S.card = 3) {x₀ : α} (hx₀ : x₀ ∉ S) :
    ((P3).filter fun S' => Disjoint S S' ∧ x₀ ∈ S').card = (Fintype.card α - 4).choose 2 := by
  have e : ((P3).filter fun S' => Disjoint S S' ∧ x₀ ∈ S') =
      ((univ \ insert x₀ S).powersetCard 2).image (insert x₀) := by
    ext S'
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_powersetCard]
    constructor
    · rintro ⟨hS', hd, hx⟩
      refine ⟨S'.erase x₀, ⟨fun z hz => ?_, ?_⟩, insert_erase hx⟩
      · rw [mem_erase] at hz
        rw [mem_sdiff, mem_insert]
        refine ⟨mem_univ z, fun h => ?_⟩
        rcases h with h | h
        · exact hz.1 h
        · exact disjoint_left.mp hd h hz.2
      · rw [card_erase_of_mem hx, hS']
    · rintro ⟨B, ⟨hB, hBc⟩, rfl⟩
      have hx₀B : x₀ ∉ B := fun h => (mem_sdiff.mp (hB h)).2 (mem_insert_self _ _)
      refine ⟨by rw [card_insert_of_notMem hx₀B, hBc], ?_, mem_insert_self _ _⟩
      rw [disjoint_left]
      intro z hzS hz
      rcases mem_insert.mp hz with h | h
      · exact hx₀ (h ▸ hzS)
      · exact (mem_sdiff.mp (hB h)).2 (mem_insert_of_mem hzS)
  rw [e, card_image_of_injOn, card_powersetCard, card_sdiff_of_subset (subset_univ _),
    card_univ, card_insert_of_notMem hx₀, hS]
  intro B hB B' hB' h
  have hB0 : x₀ ∉ B := fun hx => (mem_sdiff.mp ((mem_powersetCard.mp (mem_coe.mp hB)).1 hx)).2
    (mem_insert_self _ _)
  have hB0' : x₀ ∉ B' := fun hx => (mem_sdiff.mp ((mem_powersetCard.mp (mem_coe.mp hB')).1 hx)).2
    (mem_insert_self _ _)
  have h' : insert x₀ B = insert x₀ B' := h
  rw [← erase_insert hB0, h', erase_insert hB0']

/-- **The lower constant is attained** (`sec:frontier:empty-triple-negative`(a), (b)): for
`x₀ ∈ α`, `g(S) = [x₀ ∈ S] - 3/n` satisfies `T̄ g = -3/(n-3) g` on the `3`-sets (`n ≥ 6`). -/
theorem disjOp_eigen (hn : 6 ≤ Fintype.card α) (x₀ : α) {S : Finset α} (hS : S.card = 3) :
    disjOp (fun S' => (if x₀ ∈ S' then 1 else 0) - 3 / (Fintype.card α : ℝ)) S =
      -(3 / ((Fintype.card α : ℝ) - 3)) *
        ((if x₀ ∈ S then 1 else 0) - 3 / (Fintype.card α : ℝ)) := by
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card α = k + 6 := ⟨Fintype.card α - 6, by omega⟩
  have hk3 : Fintype.card α - 3 = k + 3 := by omega
  have hk4 : Fintype.card α - 4 = k + 2 := by omega
  have hcast : (Fintype.card α : ℝ) = (k : ℝ) + 6 := by rw [hk]; push_cast; ring
  have hκ : ∑ S' ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) = (((k + 3).choose 3 : ℕ) : ℝ) := by
    rw [Finset.sum_boole]
    have e : ((P3).filter fun S' => Disjoint S S') = (P3).filter fun S' => Disjoint S' S := by
      ext S'
      simp [disjoint_comm]
    rw [e, card_disjoint_triples hS, hk3]
  have hA : ∑ S' ∈ P3, (if Disjoint S S' ∧ x₀ ∈ S' then (1 : ℝ) else 0) =
      if x₀ ∈ S then 0 else (((k + 2).choose 2 : ℕ) : ℝ) := by
    rw [Finset.sum_boole]
    split_ifs with hx
    · rw [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
      intro S' _ h
      exact disjoint_left.mp h.1 hx h.2
    · rw [card_disjoint_through hS hx, hk4]
  have hsplit : disjOp (fun S' => (if x₀ ∈ S' then 1 else 0) - 3 / (Fintype.card α : ℝ)) S =
      (((k + 3).choose 3 : ℕ) : ℝ)⁻¹ *
        (∑ S' ∈ P3, (if Disjoint S S' ∧ x₀ ∈ S' then (1 : ℝ) else 0) -
          3 / (Fintype.card α : ℝ) * ∑ S' ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0)) := by
    unfold disjOp
    rw [hk3]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine sum_congr rfl fun S' _ => ?_
    by_cases hd : Disjoint S S' <;> by_cases hx : x₀ ∈ S' <;> simp [hd, hx]
  rw [hsplit, hA, hκ, choose_three_cast k]
  have h2 : (((k + 2).choose 2 : ℕ) : ℝ) = ((k : ℝ) + 2) * ((k : ℝ) + 1) / 2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  rw [hcast]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk6 : (k : ℝ) + 6 ≠ 0 := by positivity
  have hk3' : (k : ℝ) + 6 - 3 ≠ 0 := by
    have : (k : ℝ) + 6 - 3 = (k : ℝ) + 3 := by ring
    rw [this]
    positivity
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
  have hk3'' : (k : ℝ) + 3 ≠ 0 := by positivity
  split_ifs with hx
  · field_simp
    ring
  · rw [h2]
    field_simp
    ring

/-- **`T̄ 1 = 1`.** -/
theorem disjOp_one (hn : 6 ≤ Fintype.card α) {S : Finset α} (hS : S.card = 3) :
    disjOp (fun _ => (1 : ℝ)) S = 1 := by
  unfold disjOp
  have hκ : ∑ S' ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) =
      (((Fintype.card α - 3).choose 3 : ℕ) : ℝ) := by
    rw [Finset.sum_boole]
    have e : ((P3).filter fun S' => Disjoint S S') = (P3).filter fun S' => Disjoint S' S := by
      ext S'
      simp [disjoint_comm]
    rw [e, card_disjoint_triples hS]
  rw [hκ]
  have h0 : (((Fintype.card α - 3).choose 3 : ℕ) : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact (Nat.choose_pos (by omega)).ne'
  exact inv_mul_cancel₀ h0

/-- **The eigenvalue `1` has the constants as its eigenspace** (`n ≥ 7`): if `T̄ g = g` on the
`3`-sets then `g` is constant there. -/
theorem disjOp_fixed (hn : 7 ≤ Fintype.card α) (g : Finset α → ℝ)
    (hfix : ∀ S ∈ P3, disjOp g S = g S) :
    ∀ S ∈ P3, g S = (∑ S' ∈ P3, g S') / ((P3).card : ℝ) := by
  by_cases hP : (P3).card = 0
  · intro S hS
    exact absurd (card_eq_zero.mp hP ▸ hS) (notMem_empty S)
  set N : ℝ := ((P3).card : ℝ) with hN
  have hN0 : N ≠ 0 := by rw [hN]; exact_mod_cast hP
  set m : ℝ := (∑ S' ∈ P3, g S') / N with hm
  set g₀ : Finset α → ℝ := fun S => g S - m with hg₀
  have hmean : ∑ S ∈ P3, g₀ S = 0 := by
    simp only [hg₀, Finset.sum_sub_distrib, sum_const, nsmul_eq_mul]
    rw [← hN, hm, mul_div_cancel₀ _ hN0, sub_self]
  have hfix₀ : ∀ S ∈ P3, disjOp g₀ S = g₀ S := by
    intro S hS
    have hlin : disjOp g₀ S = disjOp g S - m * disjOp (fun _ => (1 : ℝ)) S := by
      unfold disjOp
      have e : ∑ S' ∈ P3, (if Disjoint S S' then g₀ S' else 0) =
          ∑ S' ∈ P3, (if Disjoint S S' then g S' else 0) -
            m * ∑ S' ∈ P3, (if Disjoint S S' then (fun _ => (1 : ℝ)) S' else 0) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine sum_congr rfl fun S' _ => ?_
        simp only [hg₀]
        split_ifs <;> ring
      rw [e]
      ring
    rw [hlin, disjOp_one (by omega) (mem_filter.mp hS).2, hfix S hS, mul_one]
  have hb := disjOp_abs_le hn g₀ hmean
  have heq : ∑ S ∈ P3, g₀ S * disjOp g₀ S = ∑ S ∈ P3, g₀ S ^ 2 :=
    sum_congr rfl fun S hS => by rw [hfix₀ S hS, sq]
  rw [heq] at hb
  have hQ0 : 0 ≤ ∑ S ∈ P3, g₀ S ^ 2 := Finset.sum_nonneg fun S _ => sq_nonneg _
  have hn' : (7 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hlt : 3 / ((Fintype.card α : ℝ) - 3) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hQ : ∑ S ∈ P3, g₀ S ^ 2 = 0 := by
    rw [abs_of_nonneg hQ0] at hb
    nlinarith
  intro S hS
  have h0 : g₀ S ^ 2 = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun S _ => sq_nonneg _).mp hQ S hS
  have : g₀ S = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
  simp only [hg₀] at this
  linarith

/-- The `3`-sets through `x₀`: `C(n-1, 2)` of them. -/
theorem card_triples_through (x₀ : α) :
    ((P3).filter fun S => x₀ ∈ S).card = (Fintype.card α - 1).choose 2 := by
  have e : ((P3).filter fun S => x₀ ∈ S) = ((univ.erase x₀).powersetCard 2).image (insert x₀) := by
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_powersetCard]
    constructor
    · rintro ⟨hS, hx⟩
      refine ⟨S.erase x₀, ⟨fun z hz => ?_, ?_⟩, insert_erase hx⟩
      · rw [mem_erase] at hz ⊢
        exact ⟨hz.1, mem_univ z⟩
      · rw [card_erase_of_mem hx, hS]
    · rintro ⟨B, ⟨hB, hBc⟩, rfl⟩
      have hx₀B : x₀ ∉ B := fun h => (mem_erase.mp (hB h)).1 rfl
      exact ⟨by rw [card_insert_of_notMem hx₀B, hBc], mem_insert_self _ _⟩
  rw [e, card_image_of_injOn, card_powersetCard, card_erase_of_mem (mem_univ _), card_univ]
  intro B hB B' hB' h
  have hB0 : x₀ ∉ B := fun hx =>
    (mem_erase.mp ((mem_powersetCard.mp (mem_coe.mp hB)).1 hx)).1 rfl
  have hB0' : x₀ ∉ B' := fun hx =>
    (mem_erase.mp ((mem_powersetCard.mp (mem_coe.mp hB')).1 hx)).1 rfl
  have h' : insert x₀ B = insert x₀ B' := h
  rw [← erase_insert hB0, h', erase_insert hB0']

omit [DecidableEq α] in
/-- `|P3| = C(n, 3)`. -/
theorem card_P3 : (P3).card = (Fintype.card α).choose 3 := by
  have e : (P3) = (univ : Finset α).powersetCard 3 := by
    ext S
    simp [mem_powersetCard]
  rw [e, card_powersetCard, card_univ]

/-- **`‖T̄ - J‖ = 3/(n-3)` is attained** (`n ≥ 6`): `g(S) = [x₀ ∈ S] - 3/n` has mean zero, is
nonzero, and `⟨T̄ g, g⟩ = -3/(n-3) ‖g‖²` (`disjOp_eigen`). -/
theorem disjOp_attained (hn : 6 ≤ Fintype.card α) (x₀ : α) :
    ∑ S ∈ P3, ((if x₀ ∈ S then 1 else 0) - 3 / (Fintype.card α : ℝ)) = 0 ∧
      0 < ∑ S ∈ P3, ((if x₀ ∈ S then 1 else 0) - 3 / (Fintype.card α : ℝ)) ^ 2 ∧
      ∑ S ∈ P3, ((if x₀ ∈ S then 1 else 0) - 3 / (Fintype.card α : ℝ)) *
          disjOp (fun S' => (if x₀ ∈ S' then 1 else 0) - 3 / (Fintype.card α : ℝ)) S =
        -(3 / ((Fintype.card α : ℝ) - 3)) *
          ∑ S ∈ P3, ((if x₀ ∈ S then 1 else 0) - 3 / (Fintype.card α : ℝ)) ^ 2 := by
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card α = k + 6 := ⟨Fintype.card α - 6, by omega⟩
  have hcast : (Fintype.card α : ℝ) = (k : ℝ) + 6 := by rw [hk]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_sub_distrib, Finset.sum_boole, card_triples_through, sum_const, card_P3,
      nsmul_eq_mul]
    have h1 : Fintype.card α - 1 = k + 5 := by omega
    rw [h1, hk, show k + 6 = (k + 3) + 3 by ring, choose_three_cast (k + 3), Nat.cast_choose_two]
    push_cast
    have hk6 : (k : ℝ) + 3 + 3 ≠ 0 := by positivity
    field_simp
    ring
  · have hpos : 0 < ((Fintype.card α - 1).choose 2) := Nat.choose_pos (by omega)
    rw [← card_triples_through x₀] at hpos
    obtain ⟨S, hS⟩ := card_pos.mp hpos
    have hSP : S ∈ P3 := (mem_filter.mp hS).1
    have hx : x₀ ∈ S := (mem_filter.mp hS).2
    apply Finset.sum_pos' (fun S _ => sq_nonneg _) ⟨S, hSP, ?_⟩
    rw [ite_eq_left hx, hcast]
    have : (0 : ℝ) < 1 - 3 / ((k : ℝ) + 6) := by
      rw [sub_pos, div_lt_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    positivity
  · rw [Finset.mul_sum]
    refine sum_congr rfl fun S hS => ?_
    rw [disjOp_eigen hn x₀ (mem_filter.mp hS).2]
    ring

omit [Fintype α] in
/-- `[x ∉ S] = 1 - [x ∈ S]`. -/
theorem ite_notMem_eq (S : Finset α) (x : α) :
    (if x ∈ S then (0 : ℝ) else 1) = 1 - (if x ∈ S then 1 else 0) := by
  split_ifs <;> ring

/-- For distinct `x, y, z`: `∑_{S' ∩ S = ∅} [x, y, z ∈ S'] = [x ∉ S][y ∉ S][z ∉ S]`. -/
theorem sum_disj_three (S : Finset α) {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∑ S' ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) *
        ((if x ∈ S' then 1 else 0) * (if y ∈ S' then 1 else 0) * (if z ∈ S' then 1 else 0)) =
      (if x ∈ S then 0 else 1) * (if y ∈ S then 0 else 1) * (if z ∈ S then 0 else 1) := by
  have hT : ({x, y, z} : Finset α).card = 3 := by
    rw [card_insert_of_notMem (by simp [hxy, hxz]), card_pair hyz]
  have e : ∀ S' ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) *
      ((if x ∈ S' then 1 else 0) * (if y ∈ S' then 1 else 0) * (if z ∈ S' then 1 else 0)) =
      if S' = {x, y, z} then (if Disjoint S {x, y, z} then 1 else 0) else 0 := by
    intro S' hS'
    by_cases h : S' = {x, y, z}
    · subst h
      simp
    · have hn : ¬(x ∈ S' ∧ y ∈ S' ∧ z ∈ S') := by
        rintro ⟨hx, hy, hz⟩
        apply h
        symm
        apply eq_of_subset_of_card_le
        · intro w hw
          simp only [mem_insert, mem_singleton] at hw
          rcases hw with rfl | rfl | rfl
          · exact hx
          · exact hy
          · exact hz
        · rw [(mem_filter.mp hS').2, hT]
      rw [ite_eq_right h]
      by_cases hx : x ∈ S' <;> by_cases hy : y ∈ S' <;> by_cases hz : z ∈ S' <;> simp_all
  rw [sum_congr rfl e, Finset.sum_ite_eq']
  have hTm : ({x, y, z} : Finset α) ∈ P3 := mem_filter.mpr ⟨mem_univ _, hT⟩
  rw [ite_eq_left hTm]
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> by_cases hz : z ∈ S <;>
    simp [hx, hy, hz, disjoint_insert_right, disjoint_singleton_right]

/-- **`λ₃` is an eigenvalue** (`sec:frontier:empty-triple-negative`(a)): for six distinct points
`x₀, y₀, x₁, y₁, x₂, y₂`, the function
`h(S) = ∏_i ([x_i ∈ S] - [y_i ∈ S])` (nonzero: `h({x₀, x₁, x₂}) = 1`) satisfies `K h = -h`, i.e.
`T̄ h = -C(n-3,3)⁻¹ h = λ₃ h`, `λ₃ = -6/((n-3)(n-4)(n-5))`. -/
theorem disjForm_eigen3 {x₀ y₀ x₁ y₁ x₂ y₂ : α} (hd : [x₀, y₀, x₁, y₁, x₂, y₂].Nodup)
    (S : Finset α) :
    ∑ S' ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) *
        (((if x₀ ∈ S' then 1 else 0) - (if y₀ ∈ S' then 1 else 0)) *
          ((if x₁ ∈ S' then 1 else 0) - (if y₁ ∈ S' then 1 else 0)) *
          ((if x₂ ∈ S' then 1 else 0) - (if y₂ ∈ S' then 1 else 0))) =
      -(((if x₀ ∈ S then 1 else 0) - (if y₀ ∈ S then 1 else 0)) *
          ((if x₁ ∈ S then 1 else 0) - (if y₁ ∈ S then 1 else 0)) *
          ((if x₂ ∈ S then 1 else 0) - (if y₂ ∈ S then 1 else 0))) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, ⟨h10, h11, h12⟩, ⟨h13, h14⟩, h15⟩ := hd
  have e : ∀ S' : Finset α, (if Disjoint S S' then (1 : ℝ) else 0) *
      (((if x₀ ∈ S' then 1 else 0) - (if y₀ ∈ S' then 1 else 0)) *
        ((if x₁ ∈ S' then 1 else 0) - (if y₁ ∈ S' then 1 else 0)) *
        ((if x₂ ∈ S' then 1 else 0) - (if y₂ ∈ S' then 1 else 0))) =
      (if Disjoint S S' then (1 : ℝ) else 0) * ((if x₀ ∈ S' then 1 else 0) *
          (if x₁ ∈ S' then 1 else 0) * (if x₂ ∈ S' then 1 else 0)) -
        (if Disjoint S S' then (1 : ℝ) else 0) * ((if x₀ ∈ S' then 1 else 0) *
          (if x₁ ∈ S' then 1 else 0) * (if y₂ ∈ S' then 1 else 0)) -
        (if Disjoint S S' then (1 : ℝ) else 0) * ((if x₀ ∈ S' then 1 else 0) *
          (if y₁ ∈ S' then 1 else 0) * (if x₂ ∈ S' then 1 else 0)) +
        (if Disjoint S S' then (1 : ℝ) else 0) * ((if x₀ ∈ S' then 1 else 0) *
          (if y₁ ∈ S' then 1 else 0) * (if y₂ ∈ S' then 1 else 0)) -
        (if Disjoint S S' then (1 : ℝ) else 0) * ((if y₀ ∈ S' then 1 else 0) *
          (if x₁ ∈ S' then 1 else 0) * (if x₂ ∈ S' then 1 else 0)) +
        (if Disjoint S S' then (1 : ℝ) else 0) * ((if y₀ ∈ S' then 1 else 0) *
          (if x₁ ∈ S' then 1 else 0) * (if y₂ ∈ S' then 1 else 0)) +
        (if Disjoint S S' then (1 : ℝ) else 0) * ((if y₀ ∈ S' then 1 else 0) *
          (if y₁ ∈ S' then 1 else 0) * (if x₂ ∈ S' then 1 else 0)) -
        (if Disjoint S S' then (1 : ℝ) else 0) * ((if y₀ ∈ S' then 1 else 0) *
          (if y₁ ∈ S' then 1 else 0) * (if y₂ ∈ S' then 1 else 0)) := fun S' => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_disj_three S h2 h4 h11, sum_disj_three S h2 h5 h12, sum_disj_three S h3 h4 h13,
    sum_disj_three S h3 h5 h14, sum_disj_three S h6 h8 h11, sum_disj_three S h6 h9 h12,
    sum_disj_three S h7 h8 h13, sum_disj_three S h7 h9 h14]
  simp only [ite_notMem_eq]
  ring

/-- For `x ≠ y` outside a `3`-set `S`: `#{S' ∩ S = ∅, x, y ∈ S'} = n - 5`. -/
theorem card_disjoint_through_two {S : Finset α} (hS : S.card = 3) {x y : α} (hxy : x ≠ y)
    (hx : x ∉ S) (hy : y ∉ S) :
    ((P3).filter fun S' => Disjoint S S' ∧ x ∈ S' ∧ y ∈ S').card = Fintype.card α - 5 := by
  have hB : ({x, y} : Finset α).card = 2 := card_pair hxy
  have e : ((P3).filter fun S' => Disjoint S S' ∧ x ∈ S' ∧ y ∈ S') =
      (univ \ insert x (insert y S)).image fun z => insert z {x, y} := by
    ext S'
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_sdiff, mem_insert, not_or]
    constructor
    · rintro ⟨hS', hd, hxS', hyS'⟩
      have hsub : ({x, y} : Finset α) ⊆ S' := by
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with h | h
        · rw [h]; exact hxS'
        · rw [h]; exact hyS'
      have hcard : (S' \ {x, y}).card = 1 := by rw [card_sdiff_of_subset hsub, hS', hB]
      obtain ⟨z, hz⟩ := card_eq_one.mp hcard
      have hzS' : z ∈ S' \ {x, y} := by rw [hz]; exact mem_singleton_self z
      have hz1 := mem_sdiff.mp hzS'
      refine ⟨z, ⟨fun h => hz1.2 (by rw [h]; simp), fun h => hz1.2 (by rw [h]; simp),
        fun h => disjoint_left.mp hd h hz1.1⟩, ?_⟩
      ext w
      simp only [mem_insert, mem_singleton]
      constructor
      · rintro (h | h | h)
        · rw [h]; exact hz1.1
        · rw [h]; exact hxS'
        · rw [h]; exact hyS'
      · intro hw
        by_cases hwB : w ∈ ({x, y} : Finset α)
        · simp only [mem_insert, mem_singleton] at hwB
          tauto
        · have : w ∈ S' \ {x, y} := mem_sdiff.mpr ⟨hw, hwB⟩
          rw [hz, mem_singleton] at this
          exact Or.inl this
    · rintro ⟨z, ⟨hzx, hzy, hzS⟩, rfl⟩
      refine ⟨?_, ?_, by simp, by simp⟩
      · rw [card_insert_of_notMem (by simp [hzx, hzy]), hB]
      · rw [disjoint_left]
        intro w hwS hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with h | h | h
        · exact hzS (h ▸ hwS)
        · exact hx (h ▸ hwS)
        · exact hy (h ▸ hwS)
  have hinj : Set.InjOn (fun z => insert z ({x, y} : Finset α))
      ↑(univ \ insert x (insert y S)) := by
    intro z hz z' _ h
    have h' : insert z ({x, y} : Finset α) = insert z' {x, y} := h
    have hz2 := (mem_sdiff.mp (mem_coe.mp hz)).2
    simp only [mem_insert, not_or] at hz2
    have hzB : z ∉ ({x, y} : Finset α) := by simp [hz2.1, hz2.2.1]
    have : z ∈ insert z' ({x, y} : Finset α) := by rw [← h']; exact mem_insert_self _ _
    rcases mem_insert.mp this with h1 | h1
    · exact h1
    · exact absurd h1 hzB
  have hc5 : (insert x (insert y S)).card = 5 := by
    rw [card_insert_of_notMem (by simp [hxy, hx]), card_insert_of_notMem hy, hS]
  rw [e, card_image_of_injOn hinj, card_sdiff_of_subset (subset_univ _), card_univ, hc5]

/-- `∑_{S' ∩ S = ∅} [x, y ∈ S'] = [x ∉ S][y ∉ S](n - 5)` for `x ≠ y`, `|S| = 3`, `n ≥ 5`. -/
theorem sum_disj_two (hn : 5 ≤ Fintype.card α) {S : Finset α} (hS : S.card = 3) {x y : α}
    (hxy : x ≠ y) :
    ∑ S' ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) *
        ((if x ∈ S' then 1 else 0) * (if y ∈ S' then 1 else 0)) =
      (if x ∈ S then 0 else 1) * (if y ∈ S then 0 else 1) * ((Fintype.card α : ℝ) - 5) := by
  have e : ∀ S' : Finset α, (if Disjoint S S' then (1 : ℝ) else 0) *
      ((if x ∈ S' then 1 else 0) * (if y ∈ S' then 1 else 0)) =
      if Disjoint S S' ∧ x ∈ S' ∧ y ∈ S' then 1 else 0 := by
    intro S'
    by_cases h1 : Disjoint S S' <;> by_cases h2 : x ∈ S' <;> by_cases h3 : y ∈ S' <;>
      simp [h1, h2, h3]
  simp only [e]
  rw [Finset.sum_boole]
  by_cases hx : x ∈ S
  · rw [ite_eq_left hx, zero_mul, zero_mul, Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
    intro S' _ h
    exact disjoint_left.mp h.1 hx h.2.1
  · by_cases hy : y ∈ S
    · rw [ite_eq_left hy, mul_zero, zero_mul, Nat.cast_eq_zero, card_eq_zero,
        filter_eq_empty_iff]
      intro S' _ h
      exact disjoint_left.mp h.1 hy h.2.2
    · rw [ite_eq_right hx, ite_eq_right hy, card_disjoint_through_two hS hxy hx hy,
        Nat.cast_sub hn]
      push_cast
      ring

/-- **`λ₂` is an eigenvalue** (`sec:frontier:empty-triple-negative`(a)): for four distinct points
`x₁, y₁, x₂, y₂`, `f(S) = ([x₁ ∈ S] - [y₁ ∈ S])([x₂ ∈ S] - [y₂ ∈ S])` (the lift of a harmonic
function on `2`-sets; `f({x₁, x₂, z}) = 1`) satisfies `K f = (n - 5) f`, i.e.
`T̄ f = (n-5)/C(n-3,3) f = λ₂ f`, `λ₂ = 6/((n-3)(n-4))`. -/
theorem disjForm_eigen2 (hn : 5 ≤ Fintype.card α) {x₁ y₁ x₂ y₂ : α}
    (hd : [x₁, y₁, x₂, y₂].Nodup) {S : Finset α} (hS : S.card = 3) :
    ∑ S' ∈ P3, (if Disjoint S S' then (1 : ℝ) else 0) *
        (((if x₁ ∈ S' then 1 else 0) - (if y₁ ∈ S' then 1 else 0)) *
          ((if x₂ ∈ S' then 1 else 0) - (if y₂ ∈ S' then 1 else 0))) =
      ((Fintype.card α : ℝ) - 5) *
        (((if x₁ ∈ S then 1 else 0) - (if y₁ ∈ S then 1 else 0)) *
          ((if x₂ ∈ S then 1 else 0) - (if y₂ ∈ S then 1 else 0))) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6⟩ := hd
  have e : ∀ S' : Finset α, (if Disjoint S S' then (1 : ℝ) else 0) *
      (((if x₁ ∈ S' then 1 else 0) - (if y₁ ∈ S' then 1 else 0)) *
        ((if x₂ ∈ S' then 1 else 0) - (if y₂ ∈ S' then 1 else 0))) =
      (if Disjoint S S' then (1 : ℝ) else 0) *
          ((if x₁ ∈ S' then 1 else 0) * (if x₂ ∈ S' then 1 else 0)) -
        (if Disjoint S S' then (1 : ℝ) else 0) *
          ((if x₁ ∈ S' then 1 else 0) * (if y₂ ∈ S' then 1 else 0)) -
        (if Disjoint S S' then (1 : ℝ) else 0) *
          ((if y₁ ∈ S' then 1 else 0) * (if x₂ ∈ S' then 1 else 0)) +
        (if Disjoint S S' then (1 : ℝ) else 0) *
          ((if y₁ ∈ S' then 1 else 0) * (if y₂ ∈ S' then 1 else 0)) := fun S' => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_disj_two hn hS h2, sum_disj_two hn hS h3, sum_disj_two hn hS h4,
    sum_disj_two hn hS h5]
  simp only [ite_notMem_eq]
  ring

end Sarkozy.TraceMixing
