module

public import Sarkozy.Variance.RootCountEven

/-!
# Assembling the root completion count (`eq:record:root-count`)

`paper/sections/22_variance.tex`, proof of `lem:record:root-marginal`, the last two steps of
"Even component". The completions of a half configuration `y` are counted as
`𝔑(y) = ∑_e A(y, e)`: the sum runs over the admissible even pairs `e = (y_{4,0}, y_{4,1})`, and
`A(y, e)` counts the odd completions that avoid the six even labels.

* `union_bound_avoid`: **the union bound**. If each of four free labels of the elements of a
  finite set `𝒪` takes any given value with relative frequency at most `𝔞`, then the elements
  avoiding a set `W` of forbidden values number at least `(1 - 4|W|𝔞)|𝒪|`. With the six even
  labels this is the factor `1 - 24𝔞_p`.
* `root_count_assembly`: if the number of even pairs lies between `(p/16)² L` and
  `(p/16)²(1 + υ₊)²` (`even_pairs_bounds`, with `L = (1 - υ×)(1 - υ× - 16q)`), and every
  `A(y, e)` lies between `(1 - 24𝔞)𝒵` and `𝒵`, then
  `(1 - υ×)(1 - υ× - 16q)(1 - 24𝔞) ≤ 𝔑(y)/(𝒵(p/16)²) ≤ (1 + υ₊)²`. This is
  `eq:record:root-count`.

**Still open:** the odd component, that is
* the count `𝒵 = |𝒪|`, with its independence of `(y_{1,0}, y_{1,1})` by affine maps;
* the per-value bound `𝔞_p` (`lem:record:signed-nbhd` with `k_p = (p-3)/4` common successors);
* the identification of `𝔑(y)` with the completions of the root law.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Variance

/-- **The union bound** of the even-component step: elements of `𝒪` whose four free labels avoid
a set `W` of values number at least `(1 - 4|W|𝔞)|𝒪|` when each label takes each value with
relative frequency at most `𝔞`. -/
theorem union_bound_avoid {α β : Type*} [DecidableEq β] (O : Finset α) (π : Fin 4 → α → β)
    (W : Finset β) {a : ℝ}
    (h : ∀ i v, ((O.filter fun o => π i o = v).card : ℝ) ≤ a * O.card) :
    (1 - 4 * W.card * a) * O.card ≤ ((O.filter fun o => ∀ i, π i o ∉ W).card : ℝ) := by
  classical
  -- the bad elements lie in the union of the fibres over the forbidden values
  have hsub : (O.filter fun o => ¬ ∀ i, π i o ∉ W) ⊆
      (univ ×ˢ W).biUnion fun iv => O.filter fun o => π iv.1 o = iv.2 := by
    intro o ho
    obtain ⟨hoO, hbad⟩ := mem_filter.mp ho
    push Not at hbad
    obtain ⟨i, hi⟩ := hbad
    exact mem_biUnion.mpr ⟨(i, π i o), mem_product.mpr ⟨mem_univ _, hi⟩,
      mem_filter.mpr ⟨hoO, rfl⟩⟩
  have hbad : ((O.filter fun o => ¬ ∀ i, π i o ∉ W).card : ℝ) ≤ 4 * W.card * a * O.card := by
    have h1 : (O.filter fun o => ¬ ∀ i, π i o ∉ W).card ≤
        ∑ iv ∈ univ ×ˢ W, (O.filter fun o => π iv.1 o = iv.2).card :=
      (card_le_card hsub).trans card_biUnion_le
    have h2 : (∑ iv ∈ univ ×ˢ W, ((O.filter fun o => π iv.1 o = iv.2).card : ℝ)) ≤
        ∑ _iv ∈ univ ×ˢ W, a * O.card := sum_le_sum fun iv _ => h iv.1 iv.2
    rw [sum_const, card_product, card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    have h3 : ((O.filter fun o => ¬ ∀ i, π i o ∉ W).card : ℝ) ≤
        ∑ iv ∈ univ ×ˢ W, ((O.filter fun o => π iv.1 o = iv.2).card : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    nlinarith
  have hsplit := card_filter_add_card_filter_not (s := O) (fun o => ∀ i, π i o ∉ W)
  have hsplit' : ((O.filter fun o => ∀ i, π i o ∉ W).card : ℝ) +
      ((O.filter fun o => ¬ ∀ i, π i o ∉ W).card : ℝ) = O.card := by
    exact_mod_cast hsplit
  nlinarith

/-- **`eq:record:root-count`, the assembly**: `𝔑 = ∑_{e ∈ E} A e` with
`(p/16)² L ≤ |E| ≤ (p/16)²(1 + υ₊)²` and `(1 - 24𝔞)𝒵 ≤ A e ≤ 𝒵` (`𝒵 > 0`, `1 - 24𝔞 ≥ 0`)
give `L (1 - 24𝔞) ≤ 𝔑/(𝒵 (p/16)²) ≤ (1 + υ₊)²`. -/
theorem root_count_assembly {ε : Type*} (E : Finset ε) (A : ε → ℝ) {Z p L υp a : ℝ}
    (hZ : 0 < Z) (hp : 0 < p) (ha : 0 ≤ 1 - 24 * a)
    (hElow : (p / 16) ^ 2 * L ≤ E.card) (hEup : (E.card : ℝ) ≤ (p / 16) ^ 2 * (1 + υp) ^ 2)
    (hA : ∀ e ∈ E, (1 - 24 * a) * Z ≤ A e ∧ A e ≤ Z) :
    L * (1 - 24 * a) ≤ (∑ e ∈ E, A e) / (Z * (p / 16) ^ 2) ∧
      (∑ e ∈ E, A e) / (Z * (p / 16) ^ 2) ≤ (1 + υp) ^ 2 := by
  have hq : 0 < (p / 16) ^ 2 := by positivity
  have hZq : 0 < Z * (p / 16) ^ 2 := mul_pos hZ hq
  have hlow : (E.card : ℝ) * ((1 - 24 * a) * Z) ≤ ∑ e ∈ E, A e := by
    have := sum_le_sum fun e he => (hA e he).1
    rw [sum_const, nsmul_eq_mul] at this
    exact this
  have hup : ∑ e ∈ E, A e ≤ (E.card : ℝ) * Z := by
    have := sum_le_sum fun e he => (hA e he).2
    rw [sum_const, nsmul_eq_mul] at this
    exact this
  constructor
  · rw [le_div_iff₀ hZq]
    have h1 : (p / 16) ^ 2 * L * ((1 - 24 * a) * Z) ≤ (E.card : ℝ) * ((1 - 24 * a) * Z) :=
      mul_le_mul_of_nonneg_right hElow (mul_nonneg ha hZ.le)
    nlinarith
  · rw [div_le_iff₀ hZq]
    have h1 : (E.card : ℝ) * Z ≤ (p / 16) ^ 2 * (1 + υp) ^ 2 * Z :=
      mul_le_mul_of_nonneg_right hEup hZ.le
    nlinarith

end Sarkozy.Variance
