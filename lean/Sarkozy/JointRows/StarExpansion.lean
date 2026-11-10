module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The star expansion and the complementary means (`prop:conditional-star`, Steps 2 and 5)

Source: `paper/sections/16_extraction.tex`, proof of `prop:conditional-star`, Step 2 ("exact
supports") and Step 5 ("complementary means").

* `row_star_eq`: **Step 2, row stars.** Since `χ(-1) = -1` (`p ≡ 3 mod 4`),
  `∏_{j∈T} D_{ij} χ(y_j - x_i) = A_{iT} ∏_{j∈T} (m_{ν'_j}(x_i) + φ_{ν'_j}(x_i, y_j))`,
  `A_{iT} = (-1)^{|T|} ∏_{j∈T} D_{ij}`, where `φ_ν(t, y) = χ(t - y) - m_ν(t)`.
* `row_star_expand`: the expansion of the product over the exact supports `T' ⊆ T`:
  `A_{iT} ∑_{T' ⊆ T} ∏_{j ∈ T \ T'} m_{ν'_j}(x_i) ∏_{j∈T'} φ_{ν'_j}(x_i, y_j)`; the term
  `T' = T` is the pure part, `T' = ∅` is a function of `x_i` alone, and the others carry the
  complementary means.
* `column_star_eq`: **Step 2, column stars**, `∏_{i∈S} D_{ij} χ(y_j - x_i) =
  B_{jS} ∏_{i∈S} (m_{ν_i}(y_j) + φ_{ν_i}(y_j, x_i))`, `B_{jS} = ∏_{i∈S} D_{ij}` (no sign).
* `complementary_means`: **Step 5**, the row stars at a centre `i` with the exact support `T'`
  add up to `(-1)^{|T'|} ∏_{j∈T'} D_{ij} · c(x_i) ∏_{j∈T'} φ_{ν'_j}(x_i, y_j)`,
  `c(t) = ∏_{l∈N_X(i)\T'} (1 - D_{il} m_{ν'_l}(t)) - 1`.
* `abs_prod_one_add_sub_one_le`: **Step 5**, the bound on the complementary-mean coefficient:
  if `|u_l| ≤ β` then `|∏_{l∈L} (1 + u_l) - 1| ≤ (1 + β)^{|L|} - 1`; with
  `u_l = -D_{il} m_{ν'_l}(t)` and `|m_{ν'_l}(t)| ≤ β_χ` on `Ω` this is
  `|c(t)| ≤ (1 + β_χ)^{|N_X(i)| - |T'|} - 1`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.Star

variable {J : Type*} [DecidableEq J]

omit [DecidableEq J] in
/-- **Step 2, row stars**: `∏_{j∈T} D_j χ(y_j - x) = A_T ∏_{j∈T}(m_j(x) + φ_j(x, y_j))`, with
`χ` odd and `φ_j(t, y) = χ(t - y) - m_j(t)`. -/
theorem row_star_eq {R : Type*} [AddCommGroup R] (χ : R → ℝ) (hodd : ∀ u, χ (-u) = -χ u)
    (T : Finset J) (D : J → ℝ) (m : J → R → ℝ) (x : R) (y : J → R) :
    ∏ j ∈ T, D j * χ (y j - x) =
      ((-1) ^ T.card * ∏ j ∈ T, D j) * ∏ j ∈ T, (m j x + (χ (x - y j) - m j x)) := by
  have h : ∀ j, D j * χ (y j - x) = (-1) * D j * (m j x + (χ (x - y j) - m j x)) := fun j => by
    rw [show y j - x = -(x - y j) by abel, hodd]
    ring
  simp_rw [h, Finset.prod_mul_distrib, Finset.prod_const]

/-- **The expansion over the exact supports** `T' ⊆ T`. -/
theorem row_star_expand (T : Finset J) (A : ℝ) (mx φ : J → ℝ) :
    A * ∏ j ∈ T, (mx j + φ j) = A * ∑ T' ∈ T.powerset, (∏ j ∈ T \ T', mx j) * ∏ j ∈ T', φ j := by
  simp_rw [add_comm (mx _) (φ _)]
  rw [Finset.prod_add]
  congr 1
  refine Finset.sum_congr rfl fun T' _ => ?_
  ring

omit [DecidableEq J] in
/-- **Step 2, column stars**: `∏_{i∈S} D_i χ(y - x_i) = B_S ∏_{i∈S}(m_i(y) + φ_i(y, x_i))`. -/
theorem column_star_eq {R : Type*} [AddCommGroup R] (χ : R → ℝ) (S : Finset J) (D : J → ℝ)
    (m : J → R → ℝ) (y : R) (x : J → R) :
    ∏ i ∈ S, D i * χ (y - x i) = (∏ i ∈ S, D i) * ∏ i ∈ S, (m i y + (χ (y - x i) - m i y)) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

/-- `|∏(1 + u_l) - 1| ≤ ∏(1 + |u_l|) - 1`. -/
theorem abs_prod_one_add_sub_one_le' (L : Finset J) (u : J → ℝ) :
    |∏ l ∈ L, (1 + u l) - 1| ≤ ∏ l ∈ L, (1 + |u l|) - 1 := by
  induction L using Finset.induction_on with
  | empty => simp
  | @insert a L ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    set P := ∏ l ∈ L, (1 + u l)
    set Q := ∏ l ∈ L, (1 + |u l|)
    have hQ1 : 1 ≤ Q := by
      have := Finset.prod_le_prod₀ (s := L) (f := fun _ => (1 : ℝ)) (g := fun l => 1 + |u l|)
        (fun _ _ => zero_le_one) (fun l _ => by linarith [abs_nonneg (u l)])
      simpa using this
    have hP : |P| ≤ Q := by
      have := abs_sub_abs_le_abs_sub P 1
      rw [abs_one] at this
      linarith
    have e : (1 + u a) * P - 1 = (P - 1) + u a * P := by ring
    rw [e]
    calc |(P - 1) + u a * P| ≤ |P - 1| + |u a| * |P| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ (Q - 1) + |u a| * Q := by
          have := mul_le_mul_of_nonneg_left hP (abs_nonneg (u a))
          linarith
      _ = (1 + |u a|) * Q - 1 := by ring

/-- **Step 5**: `|∏_{l∈L}(1 + u_l) - 1| ≤ (1 + β)^{|L|} - 1` when `|u_l| ≤ β`. -/
theorem abs_prod_one_add_sub_one_le (L : Finset J) (u : J → ℝ) {β : ℝ}
    (hu : ∀ l ∈ L, |u l| ≤ β) : |∏ l ∈ L, (1 + u l) - 1| ≤ (1 + β) ^ L.card - 1 := by
  refine (abs_prod_one_add_sub_one_le' L u).trans ?_
  have : ∏ l ∈ L, (1 + |u l|) ≤ ∏ _l ∈ L, (1 + β) :=
    Finset.prod_le_prod₀ (fun l _ => by linarith [abs_nonneg (u l)])
      (fun l hl => by linarith [hu l hl])
  rw [Finset.prod_const] at this
  linarith

/-- **Step 5, the complementary means of the row stars at a centre**: for the exact support
`T' ⊆ N = N_X(i)`, the row stars `T = T' ∪ R` (`∅ ≠ R ⊆ N \ T'`) contribute
`∑_R A_{T'∪R} ∏_{j∈R} m_j = (-1)^{|T'|} ∏_{j∈T'} D_j · c`, `c = ∏_{l∈N\T'} (1 - D_l m_l) - 1`
(the factor `∏_{j∈T'} φ_j` is common). -/
theorem complementary_means (N T' : Finset J) (D m : J → ℝ) :
    ∑ R ∈ ((N \ T').powerset.erase ∅),
        ((-1) ^ (T' ∪ R).card * ∏ j ∈ T' ∪ R, D j) * ∏ j ∈ R, m j =
      (-1) ^ T'.card * (∏ j ∈ T', D j) * (∏ l ∈ N \ T', (1 - D l * m l) - 1) := by
  have hdisj : ∀ R ∈ (N \ T').powerset, Disjoint T' R := fun R hR =>
    Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hR) Finset.disjoint_sdiff
  have hterm : ∀ R ∈ (N \ T').powerset,
      ((-1) ^ (T' ∪ R).card * ∏ j ∈ T' ∪ R, D j) * ∏ j ∈ R, m j =
        (-1) ^ T'.card * (∏ j ∈ T', D j) * ∏ j ∈ R, (-(D j * m j)) := by
    intro R hR
    rw [Finset.card_union_of_disjoint (hdisj R hR), Finset.prod_union (hdisj R hR), pow_add]
    have : ∏ j ∈ R, (-(D j * m j)) = (-1) ^ R.card * ((∏ j ∈ R, D j) * ∏ j ∈ R, m j) := by
      rw [← Finset.prod_mul_distrib, show (-1 : ℝ) ^ R.card = ∏ _j ∈ R, (-1 : ℝ) by
        rw [Finset.prod_const], ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => by ring
    rw [this]
    ring
  have hsum : ∑ R ∈ (N \ T').powerset, ∏ j ∈ R, (-(D j * m j)) =
      ∏ l ∈ N \ T', (1 - D l * m l) := by
    have := Finset.prod_add (fun l => -(D l * m l)) (fun _ => (1 : ℝ)) (N \ T')
    simp only [Finset.prod_const_one, mul_one] at this
    rw [← this]
    exact Finset.prod_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun R hR => hterm R (Finset.mem_of_mem_erase hR), ← Finset.mul_sum]
  congr 1
  have h0 : ∅ ∈ (N \ T').powerset := Finset.empty_mem_powerset _
  rw [← hsum, ← Finset.add_sum_erase _ _ h0, Finset.prod_empty]
  ring

end Sarkozy.JointRows.Star
