module

public import Sarkozy.TraceMixing.Paley

/-!
# Class-three middle pairs (`lem:record:class-three` (i), (ii))

`paper/sections/20_middle_reference.tex`. Let `q = |F| ≡ 3 (mod 4)` and write `a → b` for
`χ(b − a) = 1`. Part (i), the `(q − 3)/4` common out- and in-neighbours of two distinct labels,
is `card_common_out` / `card_common_in` (`lem:paley-triple`(a), WP-S).

An *F-configuration* `(x₀, x₀', x₂, x₂', u, u')` consists of six distinct labels with `y → z`
for all `y ∈ {x₀, x₀'}` and `z ∈ {x₂, x₂'}`. Its outer labels are stored here as
`(x₂, x₂', x₀, x₀')`, and `fConfigs u u'` is the set of outer quadruples completing one with
middle pair `(u, u')`.

**(ii)**: every ordered pair `u ≠ u'` is the middle pair of exactly
`(q − 3)(q − 7)(q − 4)(q − 5)/16` F-configurations (`class_three_ii`).

The proof is the paper's:
* the count depends only on the unordered pair, since the middle labels are unconstrained
  (`fConfigs_swap`);
* the maps `z ↦ αz + β` with `χ(α) = 1` preserve `→` (`card_fConfigs_equiv`) and act
  transitively on ordered distinct pairs with a fixed `χ(u' − u)`;
* `χ(−1) = −1` joins the two classes, so all ordered pairs have the same count
  (`card_fConfigs_eq`);
* a double count of the six-tuples against the `q(q − 1)·λ₀(λ₀ − 1)` outer `K_{2,2}`
  embeddings (`λ₀ = (q − 3)/4`), each with `(q − 4)(q − 5)` middle pairs, gives the number.

The identity holds for every `q ≡ 3 (mod 4)`; the paper states it for `p ≥ 11`.

**(iii), counting part** (`class_three_iii_bounds`): for distinct `u, u'` and an ordered pair
`x₀ ≠ x₀'`, the number `N` of ordered pairs `(x₂, x₂')` completing an F-configuration, outside
`{u, u'}`, satisfies `(q − 11)(q − 15) ≤ 16 N ≤ (q − 3)(q − 7)` for `q ≥ 19`. The completing
pairs are the ordered distinct pairs of common out-neighbours of `x₀, x₀'` avoiding `u, u'`. Any
two counts therefore differ by at most the factor `R₂ = (q − 3)(q − 7)/((q − 11)(q − 15))`,
which is the density statement of (iii) in elementary form. The passage to the conditional
laws of `λ_p(G_{F,2})` is not formalized here.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-- The outer `K_{2,2}` condition on `(x₂, x₂', x₀, x₀')`: `x₂ ≠ x₂'`, `x₀ ≠ x₀'`, and `x₀ → x₂`,
`x₀ → x₂'`, `x₀' → x₂`, `x₀' → x₂'`. -/
def IsK22 (x : F × F × F × F) : Prop :=
  x.1 ≠ x.2.1 ∧ x.2.2.1 ≠ x.2.2.2 ∧
    χ (x.1 - x.2.2.1) = 1 ∧ χ (x.2.1 - x.2.2.1) = 1 ∧ χ (x.1 - x.2.2.2) = 1 ∧
      χ (x.2.1 - x.2.2.2) = 1

instance (x : F × F × F × F) : Decidable (IsK22 x) := by
  unfold IsK22
  infer_instance

/-- The four outer labels. -/
def outerSet (x : F × F × F × F) : Finset F := {x.1, x.2.1, x.2.2.1, x.2.2.2}

/-- The outer quadruples of the F-configurations with middle pair `(u, u')`. -/
def fConfigs (u u' : F) : Finset (F × F × F × F) :=
  univ.filter fun x => IsK22 x ∧ u ∉ outerSet x ∧ u' ∉ outerSet x

/-- The count does not depend on the order of the middle pair. -/
theorem fConfigs_swap (u u' : F) : fConfigs u u' = fConfigs u' u := by
  ext x
  simp only [fConfigs, mem_filter, mem_univ, true_and]
  tauto

/-- **A label bijection preserving the relation preserves the counts.** -/
theorem card_fConfigs_equiv (e : F ≃ F) (he : ∀ a b, χ (e a - e b) = χ (a - b)) (u u' : F) :
    (fConfigs (e u) (e u')).card = (fConfigs u u').card := by
  let e4 : F × F × F × F ≃ F × F × F × F := e.prodCongr (e.prodCongr (e.prodCongr e))
  have hmem : ∀ x, x ∈ fConfigs u u' ↔ e4 x ∈ fConfigs (e u) (e u') := by
    intro x
    simp only [fConfigs, mem_filter, mem_univ, true_and, IsK22, outerSet, mem_insert,
      mem_singleton, e4, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, he, ne_eq,
      e.injective.eq_iff]
  have hset : fConfigs (e u) (e u') = (fConfigs u u').map e4.toEmbedding := by
    ext y
    rw [Finset.mem_map_equiv]
    have h := hmem (e4.symm y)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  rw [hset, Finset.card_map]

/-- The affine map `z ↦ αz + β`, `α ≠ 0`. -/
def affineEquiv {α : F} (hα : α ≠ 0) (β : F) : F ≃ F where
  toFun z := α * z + β
  invFun z := α⁻¹ * (z - β)
  left_inv z := by
    change α⁻¹ * (α * z + β - β) = z
    rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ hα, one_mul]
  right_inv z := by
    change α * (α⁻¹ * (z - β)) + β = z
    rw [← mul_assoc, mul_inv_cancel₀ hα, one_mul, sub_add_cancel]

/-- Ordered distinct pairs in the same `χ`-class have the same count. -/
theorem card_fConfigs_same {u u' v v' : F} (hu : u ≠ u') (hv : v ≠ v')
    (hχ : χ (u' - u) = χ (v' - v)) : (fConfigs u u').card = (fConfigs v v').card := by
  have hd : u' - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hdv : v' - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  set α := (v' - v) / (u' - u) with hαdef
  have hα : α ≠ 0 := div_ne_zero hdv hd
  have hχα : χ α = 1 := by
    have h1 : χ α * χ (u' - u) = χ (v' - v) := by
      rw [← map_mul, hαdef]
      congr 1
      field_simp
    rw [← hχ] at h1
    rcases quadraticChar_dichotomy hd with h | h <;> rw [h] at h1 <;> linarith
  let e := affineEquiv hα (v - α * u)
  have he : ∀ a b, χ (e a - e b) = χ (a - b) := by
    intro a b
    change χ ((α * a + (v - α * u)) - (α * b + (v - α * u))) = χ (a - b)
    rw [show (α * a + (v - α * u)) - (α * b + (v - α * u)) = α * (a - b) by ring, map_mul, hχα,
      one_mul]
  have heu : e u = v := by
    change α * u + (v - α * u) = v
    ring
  have heu' : e u' = v' := by
    change α * u' + (v - α * u) = v'
    rw [hαdef]
    field_simp
    ring
  rw [← heu, ← heu']
  exact (card_fConfigs_equiv e he u u').symm

/-- **Every ordered pair of distinct labels has the same count** (`q ≡ 3 (mod 4)`). -/
theorem card_fConfigs_eq (h3 : Fintype.card F % 4 = 3) {u u' v v' : F} (hu : u ≠ u')
    (hv : v ≠ v') : (fConfigs u u').card = (fConfigs v v').card := by
  rcases quadraticChar_dichotomy (sub_ne_zero.mpr (Ne.symm hu)) with h1 | h1 <;>
    rcases quadraticChar_dichotomy (sub_ne_zero.mpr (Ne.symm hv)) with h2 | h2
  · exact card_fConfigs_same hu hv (h1.trans h2.symm)
  · rw [fConfigs_swap v v']
    exact card_fConfigs_same hu hv.symm (by rw [h1, chi_swap h3 v v', h2]; norm_num)
  · rw [fConfigs_swap v v']
    exact card_fConfigs_same hu hv.symm (by rw [h1, chi_swap h3 v v', h2])
  · exact card_fConfigs_same hu hv (h1.trans h2.symm)

theorem ne_of_chi_eq_one {a b : F} (h : χ (a - b) = 1) : a ≠ b := by
  rintro rfl
  rw [sub_self, quadraticChar_zero] at h
  exact zero_ne_one h

/-- The four outer labels of a `K_{2,2}` are distinct. -/
theorem card_outerSet {x : F × F × F × F} (hx : IsK22 x) : (outerSet x).card = 4 := by
  obtain ⟨h12, h34, h13, h23, h14, h24⟩ := hx
  have a13 := ne_of_chi_eq_one h13
  have a23 := ne_of_chi_eq_one h23
  have a14 := ne_of_chi_eq_one h14
  have a24 := ne_of_chi_eq_one h24
  unfold outerSet
  rw [card_insert_of_notMem (by simp [h12, a13, a14]),
    card_insert_of_notMem (by simp [a23, a24]),
    card_insert_of_notMem (by simp [h34]), card_singleton]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem card_offDiag_int {α : Type*} [DecidableEq α] (s : Finset α) :
    (s.offDiag.card : ℤ) = s.card * (s.card - 1) := by
  rw [Finset.offDiag_card, Nat.cast_sub (Nat.le_mul_self _)]
  push_cast
  ring

/-- A `K_{2,2}` leaves `(q − 4)(q − 5)` ordered middle pairs. -/
theorem card_middle_pairs {x : F × F × F × F} (hx : IsK22 x) :
    (((univ : Finset (F × F)).filter fun p =>
        p.1 ≠ p.2 ∧ p.1 ∉ outerSet x ∧ p.2 ∉ outerSet x).card : ℤ) =
      (Fintype.card F - 4) * (Fintype.card F - 5) := by
  have hset : ((univ : Finset (F × F)).filter fun p =>
      p.1 ≠ p.2 ∧ p.1 ∉ outerSet x ∧ p.2 ∉ outerSet x) = (univ \ outerSet x).offDiag := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_univ, true_and, mem_offDiag, mem_sdiff]
    tauto
  have hcard : ((univ \ outerSet x).card : ℤ) = Fintype.card F - 4 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_outerSet hx,
      Nat.cast_sub (by
        have := card_le_univ (outerSet x)
        rwa [card_outerSet hx] at this)]
    push_cast
    ring
  rw [hset, card_offDiag_int, hcard]
  ring

/-- **The number of outer `K_{2,2}` embeddings**: `16 K = q (q − 1)(q − 3)(q − 7)`. -/
theorem card_K22 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) :
    16 * (((univ : Finset (F × F × F × F)).filter IsK22).card : ℤ) =
      Fintype.card F * (Fintype.card F - 1) * (Fintype.card F - 3) * (Fintype.card F - 7) := by
  -- fibre over the targets `(x₂, x₂')`
  have hfib : ∀ a a' : F, (((univ : Finset (F × F)).filter fun p =>
      IsK22 (a, a', p.1, p.2)).card : ℤ) =
      if a = a' then 0 else
        ((univ.filter fun c => χ (a - c) = 1 ∧ χ (a' - c) = 1).card : ℤ) *
          (((univ.filter fun c => χ (a - c) = 1 ∧ χ (a' - c) = 1).card : ℤ) - 1) := by
    intro a a'
    split_ifs with haa
    · subst haa
      simp [IsK22]
    · have hs : ((univ : Finset (F × F)).filter fun p => IsK22 (a, a', p.1, p.2)) =
          (univ.filter fun c => χ (a - c) = 1 ∧ χ (a' - c) = 1).offDiag := by
        ext ⟨b, b'⟩
        rw [mem_filter, mem_offDiag, mem_filter, mem_filter]
        simp only [mem_univ, true_and]
        dsimp only [IsK22]
        constructor
        · rintro ⟨_, hbb, h1, h2, h3', h4⟩
          exact ⟨⟨h1, h2⟩, ⟨h3', h4⟩, hbb⟩
        · rintro ⟨⟨h1, h2⟩, ⟨h3', h4⟩, hbb⟩
          exact ⟨haa, hbb, h1, h2, h3', h4⟩
      rw [hs, card_offDiag_int]
  have hsplit : (((univ : Finset (F × F × F × F)).filter IsK22).card : ℤ) =
      ∑ a : F, ∑ a' : F, (((univ : Finset (F × F)).filter fun p =>
        IsK22 (a, a', p.1, p.2)).card : ℤ) := by
    rw [card_filter]
    push_cast
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun a' _ => ?_
    rw [card_filter]
    push_cast
    rw [Fintype.sum_prod_type]
  rw [hsplit]
  simp_rw [hfib]
  -- every fibre with `a ≠ a'` has `λ₀ (λ₀ - 1)` elements, `4 λ₀ = q - 3`
  have hconst : ∀ a a' : F, a ≠ a' →
      16 * (((univ.filter fun c => χ (a - c) = 1 ∧ χ (a' - c) = 1).card : ℤ) *
        (((univ.filter fun c => χ (a - c) = 1 ∧ χ (a' - c) = 1).card : ℤ) - 1)) =
      (Fintype.card F - 3) * (Fintype.card F - 7) := by
    intro a a' haa
    have hc := card_common_in hF h3 haa
    set m := ((univ.filter fun c => χ (a - c) = 1 ∧ χ (a' - c) = 1).card : ℤ)
    have : 16 * (m * (m - 1)) = (4 * m) * (4 * m - 4) := by ring
    rw [this, hc]
    ring
  rw [mul_sum]
  have hrow : ∀ a : F, 16 * ∑ a' : F, (if a = a' then (0 : ℤ) else
      ((univ.filter fun c => χ (a - c) = 1 ∧ χ (a' - c) = 1).card : ℤ) *
        (((univ.filter fun c => χ (a - c) = 1 ∧ χ (a' - c) = 1).card : ℤ) - 1)) =
      (Fintype.card F - 1) * ((Fintype.card F - 3) * (Fintype.card F - 7)) := by
    intro a
    rw [mul_sum]
    have h' : ∀ a' : F, 16 * (if a = a' then (0 : ℤ) else
        ((univ.filter fun c => χ (a - c) = 1 ∧ χ (a' - c) = 1).card : ℤ) *
          (((univ.filter fun c => χ (a - c) = 1 ∧ χ (a' - c) = 1).card : ℤ) - 1)) =
        if a = a' then (0 : ℤ) else ((Fintype.card F : ℤ) - 3) * ((Fintype.card F : ℤ) - 7) := by
      intro a'
      split_ifs with haa
      · ring
      · exact hconst a a' haa
    simp_rw [h']
    rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
    have hcount : ((univ.filter fun a' : F => ¬ a = a').card : ℤ) = Fintype.card F - 1 := by
      have he : (univ.filter fun a' : F => ¬ a = a') = univ.erase a := by
        ext x
        simp [eq_comm]
      rw [he, card_erase_of_mem (mem_univ a), card_univ,
        Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨a⟩)]
      push_cast
      ring
    rw [hcount]
  simp_rw [hrow]
  rw [sum_const, card_univ, nsmul_eq_mul]
  ring

/-- **`lem:record:class-three`(ii)**: for `q ≡ 3 (mod 4)`, every ordered pair `u ≠ u'` of labels
is the middle pair of exactly `(q − 3)(q − 7)(q − 4)(q − 5)/16` F-configurations. -/
theorem class_three_ii (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {u u' : F}
    (hu : u ≠ u') :
    16 * ((fConfigs u u').card : ℤ) =
      (Fintype.card F - 3) * (Fintype.card F - 7) * (Fintype.card F - 4) *
        (Fintype.card F - 5) := by
  set q : ℤ := (Fintype.card F : ℤ) with hq
  set N : ℤ := ((fConfigs u u').card : ℤ) with hN
  -- count the six-tuples in two ways
  let T : Finset ((F × F) × (F × F × F × F)) := univ.filter fun t =>
    t.1.1 ≠ t.1.2 ∧ IsK22 t.2 ∧ t.1.1 ∉ outerSet t.2 ∧ t.1.2 ∉ outerSet t.2
  have hT1 : (T.card : ℤ) = q * (q - 1) * N := by
    have hT : (T.card : ℤ) = ∑ p : F × F, if p.1 ≠ p.2 then ((fConfigs p.1 p.2).card : ℤ) else 0 := by
      rw [card_filter]
      push_cast
      rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun p _ => ?_
      split_ifs with hp
      · rw [fConfigs, card_filter]
        push_cast
        refine sum_congr rfl fun x _ => ?_
        simp only [hp, ne_eq, not_false_eq_true, true_and]
      · simp only [hp, false_and, ↓reduceIte, sum_const_zero]
    have hc : ∀ p : F × F, (if p.1 ≠ p.2 then ((fConfigs p.1 p.2).card : ℤ) else 0) =
        if p.1 ≠ p.2 then N else 0 := by
      intro p
      split_ifs with hp
      · rw [hN, card_fConfigs_eq h3 hp hu]
      · rfl
    rw [hT]
    simp_rw [hc]
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
    have hoff : ((univ.filter fun p : F × F => p.1 ≠ p.2).card : ℤ) = q * (q - 1) := by
      have h := card_offDiag_int (univ : Finset F)
      have hs : (univ.filter fun p : F × F => p.1 ≠ p.2) = (univ : Finset F).offDiag := by
        ext ⟨a, b⟩
        simp
      rw [hs, h, card_univ]
    rw [hoff]
  have hT2 : (T.card : ℤ) = (((univ : Finset (F × F × F × F)).filter IsK22).card : ℤ) *
      ((q - 4) * (q - 5)) := by
    have hT : (T.card : ℤ) = ∑ x : F × F × F × F, if IsK22 x then
        (((univ : Finset (F × F)).filter fun p =>
          p.1 ≠ p.2 ∧ p.1 ∉ outerSet x ∧ p.2 ∉ outerSet x).card : ℤ) else 0 := by
      rw [card_filter]
      push_cast
      rw [Fintype.sum_prod_type, sum_comm]
      refine sum_congr rfl fun x _ => ?_
      split_ifs with hx
      · rw [card_filter]
        push_cast
        refine sum_congr rfl fun p _ => ?_
        simp only [hx, true_and]
      · simp only [hx, false_and, and_false, ↓reduceIte, sum_const_zero]
    rw [hT]
    have hc : ∀ x : F × F × F × F, (if IsK22 x then
        (((univ : Finset (F × F)).filter fun p =>
          p.1 ≠ p.2 ∧ p.1 ∉ outerSet x ∧ p.2 ∉ outerSet x).card : ℤ) else 0) =
        if IsK22 x then (q - 4) * (q - 5) else 0 := by
      intro x
      split_ifs with hx
      · exact card_middle_pairs hx
      · rfl
    simp_rw [hc]
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  have hK := card_K22 hF h3
  have hq0 : q * (q - 1) ≠ 0 := by
    have h1 : (1 : ℤ) < q := by
      have := Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial F)
      rw [hq]
      exact_mod_cast this
    exact mul_ne_zero (by linarith) (by linarith)
  have key : q * (q - 1) * (16 * N) =
      q * (q - 1) * ((q - 3) * (q - 7) * (q - 4) * (q - 5)) := by
    have := hT1.symm.trans hT2
    calc q * (q - 1) * (16 * N) = 16 * (q * (q - 1) * N) := by ring
      _ = 16 * ((((univ : Finset (F × F × F × F)).filter IsK22).card : ℤ) * ((q - 4) * (q - 5))) := by
          rw [this]
      _ = (16 * (((univ : Finset (F × F × F × F)).filter IsK22).card : ℤ)) * ((q - 4) * (q - 5)) := by
          ring
      _ = _ := by rw [hK]; ring
  exact mul_left_cancel₀ hq0 key

/-- The ordered pairs `(x₂, x₂')` completing `(x₀, x₀')` to an F-configuration with middle pair
`(u, u')`. -/
def completions (u u' x₀ x₀' : F) : Finset (F × F) :=
  ((univ.filter fun c => χ (c - x₀) = 1 ∧ χ (c - x₀') = 1) \ {u, u'}).offDiag

/-- **`lem:record:class-three`(iii), counting part.** For `q ≡ 3 (mod 4)`, `q ≥ 19`, distinct
`x₀, x₀'` and any `u, u'`, the number of completing pairs satisfies
`(q − 11)(q − 15) ≤ 16 N ≤ (q − 3)(q − 7)`. -/
theorem class_three_iii_bounds (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (h19 : 19 ≤ Fintype.card F) {x₀ x₀' : F} (hx : x₀ ≠ x₀') (u u' : F) :
    ((Fintype.card F : ℤ) - 11) * ((Fintype.card F : ℤ) - 15) ≤
        16 * ((completions u u' x₀ x₀').card : ℤ) ∧
      16 * ((completions u u' x₀ x₀').card : ℤ) ≤
        ((Fintype.card F : ℤ) - 3) * ((Fintype.card F : ℤ) - 7) := by
  set C := (univ.filter fun c => χ (c - x₀) = 1 ∧ χ (c - x₀') = 1) with hC
  have hc : 4 * (C.card : ℤ) = Fintype.card F - 3 := card_common_out hF h3 hx
  have hsplit := card_sdiff_add_card_inter C ({u, u'} : Finset F)
  have hinter : (C ∩ {u, u'}).card ≤ 2 :=
    (card_le_card inter_subset_right).trans (card_insert_le _ _)
  set m : ℤ := ((C \ {u, u'}).card : ℤ) with hm
  set k : ℤ := ((C ∩ {u, u'}).card : ℤ) with hk
  have hmk : m + k = C.card := by
    rw [hm, hk]
    exact_mod_cast hsplit
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hk2 : k ≤ 2 := by
    rw [hk]
    exact_mod_cast hinter
  have hq : (19 : ℤ) ≤ Fintype.card F := by exact_mod_cast h19
  have hN : ((completions u u' x₀ x₀').card : ℤ) = m * (m - 1) := by
    rw [completions, ← hC, card_offDiag_int]
  rw [hN]
  constructor <;> nlinarith

/-- Any two completion counts differ by at most the factor `R₂`: in elementary form, the
conditional densities of (iii) lie in `[R₂⁻¹, R₂]` with `R₂ = (q − 3)(q − 7)/((q − 11)(q − 15))`. -/
theorem class_three_iii_ratio (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (h19 : 19 ≤ Fintype.card F) {x₀ x₀' y₀ y₀' : F} (hx : x₀ ≠ x₀') (hy : y₀ ≠ y₀')
    (u u' v v' : F) :
    ((Fintype.card F : ℤ) - 11) * ((Fintype.card F : ℤ) - 15) *
        ((completions u u' x₀ x₀').card : ℤ) ≤
      ((Fintype.card F : ℤ) - 3) * ((Fintype.card F : ℤ) - 7) *
        ((completions v v' y₀ y₀').card : ℤ) := by
  obtain ⟨hx1, hx2⟩ := class_three_iii_bounds hF h3 h19 hx u u'
  obtain ⟨hy1, hy2⟩ := class_three_iii_bounds hF h3 h19 hy v v'
  have hq : (19 : ℤ) ≤ Fintype.card F := by exact_mod_cast h19
  have hA : 0 ≤ ((Fintype.card F : ℤ) - 11) * ((Fintype.card F : ℤ) - 15) := by nlinarith
  have hNx : (0 : ℤ) ≤ (completions u u' x₀ x₀').card := Nat.cast_nonneg _
  nlinarith

end Sarkozy.TraceMixing
