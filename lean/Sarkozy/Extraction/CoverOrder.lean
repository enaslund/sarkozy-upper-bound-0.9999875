module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic

/-!
# An order with a bounded weighted extension sum (`lem:cover:order`)

`paper/sections/16_extraction.tex`, `lem:cover:order`: *For an integer `g ≥ 0` put
`av(g) = (2^{g+1} - 1)/(g + 1)`. If a vertex has `g` neighbours in a uniformly ordered vertex
set containing it, then the expected value of `2^t`, where `t` counts its earlier neighbours, is
`av(g)`. Consequently, for any fixed nonnegative weights `ω_v` on the vertices, some
deterministic order has `∑_v ω_v 2^{t_v} ≤ ∑_v ω_v av(g_v)`, where `g_v` is the number of
neighbours of `v` in the set.*

Formal setting. The ordered vertex set is a finite type `V` carrying a simple graph `G`. An order
is a bijection `σ : V ≃ Fin (Fintype.card V)` (`σ u` is the position of `u`), all orders being
equally likely. `earlier G σ v` is the number `t_v(σ)` of neighbours `u` of `v` with
`σ u < σ v`, and the number of neighbours of `v` is `G.degree v`. (For a vertex subset of a larger
graph, apply the results to the induced graph on that subset.)

* `av`: `av g = (2^{g+1} - 1)/(g + 1)`.
* `expect_two_pow_earlier`: the average of `2^{t_v(σ)}` over all orders `σ` is `av (G.degree v)`
  (`sum_two_pow_earlier`: `∑_σ 2^{t_v(σ)} = (number of orders) · av (G.degree v)`).
* `exists_order_weighted_le`: for nonnegative weights `ω`, some order has
  `∑_v ω_v 2^{t_v(σ)} ≤ ∑_v ω_v av(g_v)`; `exists_order_weighted_le'` is the same statement for
  arbitrary real weights.

Proof. Instead of the rank argument of the paper (`t_v` is uniform on `{0, …, g}`), we write
`2^{t_v(σ)}` as the number of sets `T` of neighbours of `v` that all come before `v`
(`sum_two_pow_earlier_nat`). For a fixed such `T` the orders in which `v` comes last among
`T ∪ {v}` form the fraction `1/(|T| + 1)` of all orders (`card_mul_card_isLast`: the classes
"`w` comes last among `S`", `w ∈ S`, partition the orders and are exchanged by transpositions), so
the average of `2^{t_v}` is `∑_{k=0}^{g} C(g,k)/(k+1) = av(g)` (`sum_choose_div_succ_eq_av`). The
existence of the order is linearity of the average together with "a finite average is at least
its minimum"; the nonnegativity of the weights is not needed for it.
-/

@[expose] public section

open Finset

namespace Sarkozy.Extraction

/-- `av g = (2^{g+1} - 1)/(g + 1)`, the average of `2^t` over `t ∈ {0, …, g}`. -/
noncomputable def av (g : ℕ) : ℝ := (2 ^ (g + 1) - 1) / (g + 1)

/-- `∑_{k=0}^{g} C(g,k)/(k+1) = (2^{g+1} - 1)/(g + 1) = av g`. -/
theorem sum_choose_div_succ_eq_av (g : ℕ) :
    ∑ k ∈ range (g + 1), (g.choose k : ℝ) / (k + 1) = av g := by
  have h1 : ∀ k : ℕ, (g.choose k : ℝ) / (k + 1) = ((g + 1).choose (k + 1) : ℝ) / (g + 1) := by
    intro k
    rw [div_eq_div_iff (by positivity) (by positivity)]
    have := Nat.add_one_mul_choose_eq g k
    have h : (((g + 1) * g.choose k : ℕ) : ℝ) = (((g + 1).choose (k + 1) * (k + 1) : ℕ) : ℝ) := by
      rw [this]
    push_cast at h
    linarith
  have h2 : (∑ k ∈ range (g + 1), ((g + 1).choose (k + 1) : ℝ)) + 1 = 2 ^ (g + 1) := by
    have := Nat.sum_range_choose (g + 1)
    rw [sum_range_succ', Nat.choose_zero_right] at this
    exact_mod_cast this
  rw [sum_congr rfl fun k _ => h1 k, ← sum_div, av]
  congr 1
  linarith

section Orders

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `t_v(σ)`: the number of neighbours `u` of `v` that come before `v` in the order `σ`. -/
def earlier (σ : V ≃ Fin (Fintype.card V)) (v : V) : ℕ :=
  #{u | G.Adj u v ∧ σ u < σ v}

variable [DecidableEq V]

omit [DecidableRel G.Adj] in
/-- For `v ∈ S`, the orders in which `v` comes last among `S` form the fraction `1/|S|` of all
orders: the classes "`w` comes last among `S`" (`w ∈ S`) partition the orders, and the
transposition of `v` and `w` exchanges the classes of `v` and `w`. -/
theorem card_mul_card_isLast {S : Finset V} {v : V} (hv : v ∈ S) :
    #S * #{σ : V ≃ Fin (Fintype.card V) | ∀ u ∈ S, σ u ≤ σ v} =
      Fintype.card (V ≃ Fin (Fintype.card V)) := by
  set n := Fintype.card V
  -- precomposing with the transposition of `a` and `b` moves "`b` last" to "`a` last"
  have hswap : ∀ {a b : V}, a ∈ S → b ∈ S → ∀ σ : V ≃ Fin n, (∀ u ∈ S, σ u ≤ σ b) →
      ∀ u ∈ S, ((Equiv.swap a b).trans σ) u ≤ ((Equiv.swap a b).trans σ) a := by
    intro a b ha hb σ hσ u hu
    simp only [Equiv.trans_apply, Equiv.swap_apply_left]
    apply hσ
    rcases eq_or_ne u a with rfl | hua
    · simpa using hb
    rcases eq_or_ne u b with rfl | hub
    · simpa using ha
    · rwa [Equiv.swap_apply_of_ne_of_ne hua hub]
  have hcard : ∀ w ∈ S, #{σ : V ≃ Fin n | ∀ u ∈ S, σ u ≤ σ w} =
      #{σ : V ≃ Fin n | ∀ u ∈ S, σ u ≤ σ v} := by
    intro w hw
    refine card_nbij' (fun σ => (Equiv.swap v w).trans σ) (fun σ => (Equiv.swap v w).trans σ)
      ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
      exact hswap hv hw σ hσ
    · intro σ hσ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
      rw [Equiv.swap_comm]
      exact hswap hw hv σ hσ
    · intro σ _
      ext u
      simp
    · intro σ _
      ext u
      simp
  have hcover : (univ : Finset (V ≃ Fin n)) =
      S.biUnion fun w => {σ : V ≃ Fin n | ∀ u ∈ S, σ u ≤ σ w} := by
    ext σ
    simp only [mem_univ, mem_biUnion, mem_filter, true_and, true_iff]
    exact S.exists_max_image σ ⟨v, hv⟩
  have h : #(S.biUnion fun w => {σ : V ≃ Fin n | ∀ u ∈ S, σ u ≤ σ w}) =
      ∑ w ∈ S, #{σ : V ≃ Fin n | ∀ u ∈ S, σ u ≤ σ w} := by
    apply card_biUnion
    intro w hw w' hw' hne
    refine Finset.disjoint_left.2 fun σ h1 h2 => ?_
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    exact hne (σ.injective (le_antisymm (h2 w hw) (h1 w' hw')))
  rw [← hcover, sum_congr rfl hcard, sum_const, smul_eq_mul, card_univ] at h
  exact h.symm

/-- For a set `T` of neighbours of `v`, the orders in which all of `T` comes before `v` form the
fraction `1/(|T| + 1)` of all orders. -/
theorem card_mul_card_allEarlier {T : Finset V} {v : V} (hT : T ⊆ G.neighborFinset v) :
    (#T + 1) * #{σ : V ≃ Fin (Fintype.card V) | ∀ u ∈ T, σ u < σ v} =
      Fintype.card (V ≃ Fin (Fintype.card V)) := by
  have hvT : v ∉ T := fun h => G.irrefl ((G.mem_neighborFinset v v).1 (hT h))
  rw [← card_insert_of_notMem hvT, ← card_mul_card_isLast (mem_insert_self v T)]
  congr 2
  ext σ
  simp only [mem_filter, mem_univ, true_and, mem_insert, forall_eq_or_imp, le_refl]
  refine forall₂_congr fun u hu => ?_
  have huv : u ≠ v := fun h => hvT (h ▸ hu)
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (σ.injective.ne huv)⟩

/-- `∑_σ 2^{t_v(σ)} = ∑_{T ⊆ N(v)} #{σ : all of T comes before v}`, since `2^{t_v(σ)}` counts the
sets of neighbours of `v` that all come before `v`. -/
theorem sum_two_pow_earlier_nat (v : V) :
    ∑ σ : V ≃ Fin (Fintype.card V), 2 ^ earlier G σ v =
      ∑ T ∈ (G.neighborFinset v).powerset,
        #{σ : V ≃ Fin (Fintype.card V) | ∀ u ∈ T, σ u < σ v} := by
  have h : ∀ σ : V ≃ Fin (Fintype.card V), 2 ^ earlier G σ v =
      ∑ T ∈ (G.neighborFinset v).powerset, if ∀ u ∈ T, σ u < σ v then 1 else 0 := by
    intro σ
    rw [← card_filter, earlier, ← card_powerset]
    congr 1
    ext T
    simp only [mem_powerset, mem_filter, subset_iff, mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    constructor
    · intro h
      exact ⟨fun u hu => (h hu).1.symm, fun u hu => (h hu).2⟩
    · rintro ⟨h1, h2⟩ u hu
      exact ⟨(h1 hu).symm, h2 u hu⟩
  rw [sum_congr rfl fun σ _ => h σ, sum_comm]
  refine sum_congr rfl fun T _ => ?_
  rw [card_filter]

/-- `∑_σ 2^{t_v(σ)} = (number of orders) · av(g_v)`. -/
theorem sum_two_pow_earlier (v : V) :
    ∑ σ : V ≃ Fin (Fintype.card V), (2 : ℝ) ^ earlier G σ v =
      Fintype.card (V ≃ Fin (Fintype.card V)) * av (G.degree v) := by
  set M := Fintype.card (V ≃ Fin (Fintype.card V))
  have h2 : ∀ T ∈ (G.neighborFinset v).powerset,
      (#{σ : V ≃ Fin (Fintype.card V) | ∀ u ∈ T, σ u < σ v} : ℝ) = M / (#T + 1) := by
    intro T hT
    rw [eq_div_iff (by positivity), mul_comm]
    exact_mod_cast card_mul_card_allEarlier G (mem_powerset.1 hT)
  calc ∑ σ : V ≃ Fin (Fintype.card V), (2 : ℝ) ^ earlier G σ v
      = ((∑ σ : V ≃ Fin (Fintype.card V), 2 ^ earlier G σ v : ℕ) : ℝ) := by push_cast; rfl
    _ = ∑ T ∈ (G.neighborFinset v).powerset, (M : ℝ) / (#T + 1) := by
        rw [sum_two_pow_earlier_nat]
        push_cast
        exact sum_congr rfl h2
    _ = ∑ k ∈ range (#(G.neighborFinset v) + 1),
          (#(G.neighborFinset v)).choose k • ((M : ℝ) / (k + 1)) :=
        sum_powerset_apply_card (fun k => (M : ℝ) / (k + 1))
    _ = M * av (G.degree v) := by
        rw [G.card_neighborFinset_eq_degree, ← sum_choose_div_succ_eq_av, mul_sum]
        refine sum_congr rfl fun k _ => ?_
        rw [nsmul_eq_mul]
        ring

/-- **`lem:cover:order`, first part.** If `v` has `g` neighbours, the expected value of `2^t`
over a uniformly random order, where `t` counts the neighbours of `v` before `v`, is `av(g)`. -/
theorem expect_two_pow_earlier (v : V) :
    (∑ σ : V ≃ Fin (Fintype.card V), (2 : ℝ) ^ earlier G σ v) /
      Fintype.card (V ≃ Fin (Fintype.card V)) = av (G.degree v) := by
  have hM : (0 : ℝ) < Fintype.card (V ≃ Fin (Fintype.card V)) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨Fintype.equivFin V⟩
  rw [sum_two_pow_earlier, mul_div_cancel_left₀ _ hM.ne']

omit [DecidableEq V] in
/-- Some order `σ` has `∑_v ω_v 2^{t_v(σ)} ≤ ∑_v ω_v av(g_v)`, for arbitrary real weights `ω`
(the average of the left side over all orders is the right side, by linearity and
`sum_two_pow_earlier`, and a finite average is at least its minimum). -/
theorem exists_order_weighted_le' (ω : V → ℝ) :
    ∃ σ : V ≃ Fin (Fintype.card V), ∑ v, ω v * 2 ^ earlier G σ v ≤ ∑ v, ω v * av (G.degree v) := by
  classical
  have hne : (univ : Finset (V ≃ Fin (Fintype.card V))).Nonempty :=
    ⟨Fintype.equivFin V, mem_univ _⟩
  have key : ∑ σ : V ≃ Fin (Fintype.card V), ∑ v, ω v * (2 : ℝ) ^ earlier G σ v =
      ∑ _σ : V ≃ Fin (Fintype.card V), ∑ v, ω v * av (G.degree v) := by
    calc ∑ σ : V ≃ Fin (Fintype.card V), ∑ v, ω v * (2 : ℝ) ^ earlier G σ v
        = ∑ v, ω v * ∑ σ : V ≃ Fin (Fintype.card V), (2 : ℝ) ^ earlier G σ v := by
          rw [sum_comm]
          exact sum_congr rfl fun v _ => (mul_sum _ _ _).symm
      _ = ∑ _σ : V ≃ Fin (Fintype.card V), ∑ v, ω v * av (G.degree v) := by
          rw [sum_const, card_univ, nsmul_eq_mul, mul_sum]
          refine sum_congr rfl fun v _ => ?_
          rw [sum_two_pow_earlier]
          ring
  obtain ⟨σ, -, hσ⟩ := exists_le_of_sum_le hne key.le
  exact ⟨σ, hσ⟩

omit [DecidableEq V] in
/-- **`lem:cover:order`, second part.** For any fixed nonnegative weights `ω_v` on the vertices,
some deterministic order `σ` has `∑_v ω_v 2^{t_v(σ)} ≤ ∑_v ω_v av(g_v)`, where `g_v` is the number
of neighbours of `v`. (The sign condition is not needed: see `exists_order_weighted_le'`.) -/
theorem exists_order_weighted_le (ω : V → ℝ) (_hω : ∀ v, 0 ≤ ω v) :
    ∃ σ : V ≃ Fin (Fintype.card V), ∑ v, ω v * 2 ^ earlier G σ v ≤ ∑ v, ω v * av (G.degree v) :=
  exists_order_weighted_le' G ω

end Orders

end Sarkozy.Extraction
