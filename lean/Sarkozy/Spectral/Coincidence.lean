module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-!
# `lem:push:localvariance` (b): the coincidence bound

`paper/sections/14_spectral.tex`, proof of `lem:push:localvariance` (b), paragraph
*Coincidences*: for independent uniform labels `y_l ∈ 𝔽_p` (`l ∈ S`) and weights
`ρ_l = 2^{m_l+1} 1_{𝒜_l}`,
`E_y[∏_l ρ_l(y_l) 1_{y_i = y_j}] = ∏_l q_l · |𝒜_i ∩ 𝒜_j|/(|𝒜_i||𝒜_j|) ≤ ∏_l q_l · min(κ_i, κ_j)/p`
when `|𝒜_i| ≥ p/κ_i` and `|𝒜_j| ≥ p/κ_j`. Stated with sums over `y : S → F` (dividing both
sides by `p^{|S|}` gives the expectations).

* `sum_prod_coincidence`: the factorization
  `∑_y ∏_l ρ_l(y_l) [y_i = y_j] = (∑_t ρ_i(t) ρ_j(t)) ∏_{l ≠ i, j} ∑_s ρ_l(s)`, for any weights.
* `indicator_overlap_le`: for `ρ_l = c_l 1_{𝒜_l}`,
  `∑_t ρ_i ρ_j ≤ (min(κ_i, κ_j)/p) (∑ ρ_i)(∑ ρ_j)`.
* `coincidence_bound`: `∑_y ∏_l ρ_l(y_l) [y_i = y_j] ≤ (min(κ_i, κ_j)/p) ∑_y ∏_l ρ_l(y_l)`.
* `inj_indicator_le`, `coll_bound`: the term `Coll_k`. Replacing full injectivity by injectivity
  inside the two parts, and `T_∅` by `∏ q`, costs at most `M ∑_{cross pairs} C_T +
  ∑_{inside pairs} C_T` with `C_T` the coincidence sums (`M = 2^{|E(G⁺[S])|}` bounds the edge
  product), each bounded by `coincidence_bound` (`coin_pair`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Spectral

variable {S F : Type*} [Fintype S] [DecidableEq S] [Fintype F] [DecidableEq F]

/-- **The factorization** of a sum of products with one coincidence. -/
theorem sum_prod_coincidence (ρ : S → F → ℝ) {i j : S} (hij : i ≠ j) :
    ∑ y : S → F, (∏ l, ρ l (y l)) * (if y i = y j then 1 else 0) =
      (∑ t, ρ i t * ρ j t) * ∏ l ∈ (univ.erase i).erase j, ∑ s, ρ l s := by
  have hind : ∀ y : S → F, (if y i = y j then (1 : ℝ) else 0) =
      ∑ t, (if y i = t then 1 else 0) * (if y j = t then 1 else 0) := by
    intro y
    rw [Finset.sum_eq_single (y j)]
    · by_cases h : y i = y j <;> simp [h]
    · intro t _ ht
      simp [Ne.symm ht]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hj : j ∈ univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  -- the indicator factors as a product over the vertices
  have hprod : ∀ (t : F) (y : S → F), (∏ l, ρ l (y l)) *
      ((if y i = t then 1 else 0) * (if y j = t then 1 else 0)) =
      ∏ l, (ρ l (y l) * (if l = i ∨ l = j then (if y l = t then 1 else 0) else 1)) := by
    intro t y
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase (univ.erase i) _ hj, Finset.prod_eq_one]
    · simp [hij, Ne.symm hij]
    · intro l hl
      simp only [Finset.mem_erase] at hl
      simp [hl.1, hl.2.1]
  -- the sum over `y` of that product
  have hsum : ∀ t : F, ∑ s : S → F, ∏ l, ρ l (s l) * (if l = i ∨ l = j then
      (if s l = t then (1 : ℝ) else 0) else 1) =
      ρ i t * ρ j t * ∏ l ∈ (univ.erase i).erase j, ∑ s, ρ l s := by
    intro t
    rw [← Fintype.prod_sum (fun l s => ρ l s * (if l = i ∨ l = j then
      (if s = t then (1 : ℝ) else 0) else 1))]
    rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase (univ.erase i) _ hj]
    have e1 : ∑ s, ρ i s * (if i = i ∨ i = j then (if s = t then (1 : ℝ) else 0) else 1) =
        ρ i t := by simp
    have e2 : ∑ s, ρ j s * (if j = i ∨ j = j then (if s = t then (1 : ℝ) else 0) else 1) =
        ρ j t := by simp
    have e3 : ∏ l ∈ (univ.erase i).erase j, ∑ s, ρ l s * (if l = i ∨ l = j then
        (if s = t then (1 : ℝ) else 0) else 1) = ∏ l ∈ (univ.erase i).erase j, ∑ s, ρ l s := by
      refine Finset.prod_congr rfl fun l hl => ?_
      simp only [Finset.mem_erase] at hl
      simp [hl.1, hl.2.1]
    rw [e1, e2, e3]
    ring
  calc ∑ y : S → F, (∏ l, ρ l (y l)) * (if y i = y j then 1 else 0)
      = ∑ y : S → F, ∑ t, (∏ l, ρ l (y l)) *
          ((if y i = t then 1 else 0) * (if y j = t then 1 else 0)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hind, Finset.mul_sum]
    _ = ∑ t, ∑ y : S → F, ∏ l, (ρ l (y l) *
          (if l = i ∨ l = j then (if y l = t then 1 else 0) else 1)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun y _ => hprod t y
    _ = ∑ t, ρ i t * ρ j t * ∏ l ∈ (univ.erase i).erase j, ∑ s, ρ l s :=
        Finset.sum_congr rfl fun t _ => hsum t
    _ = _ := by rw [Finset.sum_mul]

/-- **The overlap of two indicator weights**: for `ρ_i = c_i 1_{𝒜_i}`, `ρ_j = c_j 1_{𝒜_j}` with
`c ≥ 0`, `|𝒜_i| ≥ p/κ_i` and `|𝒜_j| ≥ p/κ_j`,
`∑_t ρ_i ρ_j = c_i c_j |𝒜_i ∩ 𝒜_j| ≤ (min(κ_i, κ_j)/p) (c_i |𝒜_i|)(c_j |𝒜_j|)`. -/
theorem indicator_overlap_le (Ai Aj : Finset F) {ci cj κi κj p : ℝ} (hci : 0 ≤ ci)
    (hcj : 0 ≤ cj) (hp : 0 < p) (hκi : p ≤ κi * Ai.card) (hκj : p ≤ κj * Aj.card) :
    ∑ t, (ci * (if t ∈ Ai then 1 else 0)) * (cj * (if t ∈ Aj then 1 else 0)) ≤
      min κi κj / p * ((ci * Ai.card) * (cj * Aj.card)) := by
  have e : ∑ t, (ci * (if t ∈ Ai then (1 : ℝ) else 0)) * (cj * (if t ∈ Aj then 1 else 0)) =
      ci * cj * (Ai ∩ Aj).card := by
    have : ∀ t, (ci * (if t ∈ Ai then (1 : ℝ) else 0)) * (cj * (if t ∈ Aj then 1 else 0)) =
        ci * cj * (if t ∈ Ai ∩ Aj then 1 else 0) := fun t => by
      by_cases h1 : t ∈ Ai <;> by_cases h2 : t ∈ Aj <;> simp [h1, h2]
    rw [Finset.sum_congr rfl fun t _ => this t, ← Finset.mul_sum, Finset.sum_boole,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [e]
  have hI : ((Ai ∩ Aj).card : ℝ) ≤ Ai.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  have hJ : ((Ai ∩ Aj).card : ℝ) ≤ Aj.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hcc : 0 ≤ ci * cj := mul_nonneg hci hcj
  have hAi0 : (0 : ℝ) ≤ Ai.card := Nat.cast_nonneg _
  have hAj0 : (0 : ℝ) ≤ Aj.card := Nat.cast_nonneg _
  -- `p |𝒜_i ∩ 𝒜_j| ≤ κ |𝒜_i||𝒜_j|` for `κ = κ_i` and for `κ = κ_j`
  have h1 : p * (Ai ∩ Aj).card ≤ κi * (Ai.card * Aj.card) := by
    calc p * (Ai ∩ Aj).card ≤ (κi * Ai.card) * (Ai ∩ Aj).card :=
          mul_le_mul_of_nonneg_right hκi (Nat.cast_nonneg _)
      _ ≤ (κi * Ai.card) * Aj.card := by
          have : 0 ≤ κi * Ai.card := hp.le.trans hκi
          exact mul_le_mul_of_nonneg_left hJ this
      _ = κi * (Ai.card * Aj.card) := by ring
  have h2 : p * (Ai ∩ Aj).card ≤ κj * (Ai.card * Aj.card) := by
    calc p * (Ai ∩ Aj).card ≤ (κj * Aj.card) * (Ai ∩ Aj).card :=
          mul_le_mul_of_nonneg_right hκj (Nat.cast_nonneg _)
      _ ≤ (κj * Aj.card) * Ai.card := by
          have : 0 ≤ κj * Aj.card := hp.le.trans hκj
          exact mul_le_mul_of_nonneg_left hI this
      _ = κj * (Ai.card * Aj.card) := by ring
  have h3 : p * (Ai ∩ Aj).card ≤ min κi κj * (Ai.card * Aj.card) := by
    rcases min_choice κi κj with h | h <;> rw [h]
    · exact h1
    · exact h2
  rw [div_mul_eq_mul_div, le_div_iff₀ hp]
  calc ci * cj * (Ai ∩ Aj).card * p = ci * cj * (p * (Ai ∩ Aj).card) := by ring
    _ ≤ ci * cj * (min κi κj * (Ai.card * Aj.card)) := mul_le_mul_of_nonneg_left h3 hcc
    _ = min κi κj * (ci * Ai.card * (cj * Aj.card)) := by ring

/-- **The coincidence bound** of `lem:push:localvariance` (b): for weights `ρ_l ≥ 0` with
`ρ_i = c_i 1_{𝒜_i}`, `ρ_j = c_j 1_{𝒜_j}` (`i ≠ j`), `|𝒜_i| ≥ p/κ_i`, `|𝒜_j| ≥ p/κ_j`,
`∑_y ∏_l ρ_l(y_l) [y_i = y_j] ≤ (min(κ_i, κ_j)/p) ∑_y ∏_l ρ_l(y_l)`. -/
theorem coincidence_bound (ρ : S → F → ℝ) (hρ : ∀ l s, 0 ≤ ρ l s) {i j : S} (hij : i ≠ j)
    (Ai Aj : Finset F) {ci cj κi κj p : ℝ} (hci : 0 ≤ ci) (hcj : 0 ≤ cj) (hp : 0 < p)
    (hρi : ∀ s, ρ i s = ci * (if s ∈ Ai then 1 else 0))
    (hρj : ∀ s, ρ j s = cj * (if s ∈ Aj then 1 else 0))
    (hκi : p ≤ κi * Ai.card) (hκj : p ≤ κj * Aj.card) :
    ∑ y : S → F, (∏ l, ρ l (y l)) * (if y i = y j then 1 else 0) ≤
      min κi κj / p * ∑ y : S → F, ∏ l, ρ l (y l) := by
  rw [sum_prod_coincidence ρ hij, ← Fintype.prod_sum (fun l s => ρ l s),
    ← Finset.mul_prod_erase univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase (univ.erase i) _
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
  have hrest : 0 ≤ ∏ l ∈ (univ.erase i).erase j, ∑ s, ρ l s :=
    Finset.prod_nonneg fun l _ => Finset.sum_nonneg fun s _ => hρ l s
  have hsi : ∑ s, ρ i s = ci * Ai.card := by
    simp only [hρi, ← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.univ_inter]
  have hsj : ∑ s, ρ j s = cj * Aj.card := by
    simp only [hρj, ← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.univ_inter]
  have hov := indicator_overlap_le Ai Aj hci hcj hp hκi hκj
  simp only [← hρi, ← hρj] at hov
  rw [hsi, hsj]
  calc (∑ t, ρ i t * ρ j t) * ∏ l ∈ (univ.erase i).erase j, ∑ s, ρ l s
      ≤ (min κi κj / p * ((ci * Ai.card) * (cj * Aj.card))) *
          ∏ l ∈ (univ.erase i).erase j, ∑ s, ρ l s := mul_le_mul_of_nonneg_right hov hrest
    _ = _ := by ring

/-! ### The coincidence term `Coll_k` -/

/-- `y` has a coincidence on the set of vertices `T`. -/
def Coin (y : S → F) (T : Finset S) : Prop := ∃ i ∈ T, ∃ j ∈ T, i ≠ j ∧ y i = y j

instance (y : S → F) (T : Finset S) : Decidable (Coin y T) := by
  unfold Coin
  infer_instance

omit [Fintype S] [Fintype F] [DecidableEq F] in
theorem coin_pair {i j : S} (hij : i ≠ j) (y : S → F) : Coin y {i, j} ↔ y i = y j := by
  constructor
  · rintro ⟨a, ha, b, hb, hab, h⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact h
    · exact h.symm
    · exact absurd rfl hab
  · intro h
    exact ⟨i, by simp, j, by simp, hij, h⟩

omit [Fintype F] in
/-- The two indicator inequalities: injectivity inside the parts (no coincidence on the pairs
`Q`) minus full injectivity (no coincidence on `P ∪ Q`) is at most the number of coincidences on
the cross pairs `P`; one minus injectivity inside the parts is at most the number of
coincidences on `Q`. -/
theorem inj_indicator_le (P Q : Finset (Finset S)) (y : S → F) :
    0 ≤ (if ∀ T ∈ Q, ¬ Coin y T then (1 : ℝ) else 0) -
        (if ∀ T ∈ P ∪ Q, ¬ Coin y T then 1 else 0) ∧
    (if ∀ T ∈ Q, ¬ Coin y T then (1 : ℝ) else 0) -
        (if ∀ T ∈ P ∪ Q, ¬ Coin y T then 1 else 0) ≤
      ∑ T ∈ P, (if Coin y T then 1 else 0) ∧
    0 ≤ 1 - (if ∀ T ∈ Q, ¬ Coin y T then (1 : ℝ) else 0) ∧
    1 - (if ∀ T ∈ Q, ¬ Coin y T then (1 : ℝ) else 0) ≤ ∑ T ∈ Q, (if Coin y T then 1 else 0) := by
  have hP0 : 0 ≤ ∑ T ∈ P, (if Coin y T then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun T _ => by split_ifs <;> norm_num
  have hQ0 : 0 ≤ ∑ T ∈ Q, (if Coin y T then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun T _ => by split_ifs <;> norm_num
  have hone : ∀ (R : Finset (Finset S)) (T : Finset S), T ∈ R → Coin y T →
      1 ≤ ∑ T ∈ R, (if Coin y T then (1 : ℝ) else 0) := fun R T hT hc => by
    have := Finset.single_le_sum (f := fun T => if Coin y T then (1 : ℝ) else 0)
      (fun T _ => by split_ifs <;> norm_num) hT
    simpa [hc] using this
  by_cases hQ : ∀ T ∈ Q, ¬ Coin y T
  · by_cases hPQ : ∀ T ∈ P ∪ Q, ¬ Coin y T
    · rw [ite_eq_left hQ, ite_eq_left hPQ, sub_self]
      exact ⟨le_rfl, hP0, le_rfl, hQ0⟩
    · rw [ite_eq_left hQ, ite_eq_right hPQ, sub_zero, sub_self]
      push Not at hPQ
      obtain ⟨T, hT, hc⟩ := hPQ
      rcases Finset.mem_union.mp hT with hTP | hTQ
      · exact ⟨zero_le_one, hone P T hTP hc, le_rfl, hQ0⟩
      · exact absurd hc (hQ T hTQ)
  · have hPQ : ¬ ∀ T ∈ P ∪ Q, ¬ Coin y T := fun h =>
      hQ fun T hT => h T (Finset.mem_union_right P hT)
    rw [ite_eq_right hQ, ite_eq_right hPQ, sub_zero, sub_zero]
    push Not at hQ
    obtain ⟨T, hT, hc⟩ := hQ
    exact ⟨le_rfl, hP0, zero_le_one, hone Q T hT hc⟩

/-- **The coincidence term** of `lem:push:localvariance` (b): with weights `w(y) = ∏_l ρ_l(y_l)`,
the edge product `0 ≤ Φ ≤ M` (`M = 2^{|E(G⁺[S])|}`), cross pairs `P` and inside pairs `Q`,
`|(𝓗 - 𝓗') + (T_∅ - ∏ q)| ≤ M ∑_{T∈P} C_T + ∑_{T∈Q} C_T`, `C_T = ∑_y w(y) [y has a coincidence
on T]`. Here `𝓗 = ∑ w [inj] Φ`, `𝓗' = ∑ w [inj inside the parts] Φ = ∑_H T_H`,
`T_∅ = ∑ w [inj inside the parts]` and `∏ q = ∑ w` (all unnormalized); so
`|𝓗 - ∏ q - ∑_{H ≠ ∅} T_H|` is at most the right side, and with `coincidence_bound` on each
pair this is at most `Coll_k`. -/
theorem coll_bound (ρ : S → F → ℝ) (hρ : ∀ l s, 0 ≤ ρ l s) (Φ : (S → F) → ℝ) {M : ℝ}
    (hΦ0 : ∀ y, 0 ≤ Φ y) (hΦM : ∀ y, Φ y ≤ M) (P Q : Finset (Finset S)) :
    |(∑ y : S → F, (∏ l, ρ l (y l)) * (if ∀ T ∈ P ∪ Q, ¬ Coin y T then 1 else 0) * Φ y -
        ∑ y : S → F, (∏ l, ρ l (y l)) * (if ∀ T ∈ Q, ¬ Coin y T then 1 else 0) * Φ y) +
      (∑ y : S → F, (∏ l, ρ l (y l)) * (if ∀ T ∈ Q, ¬ Coin y T then 1 else 0) -
        ∑ y : S → F, ∏ l, ρ l (y l))| ≤
      M * ∑ T ∈ P, ∑ y : S → F, (∏ l, ρ l (y l)) * (if Coin y T then 1 else 0) +
        ∑ T ∈ Q, ∑ y : S → F, (∏ l, ρ l (y l)) * (if Coin y T then 1 else 0) := by
  set w : (S → F) → ℝ := fun y => ∏ l, ρ l (y l) with hw
  have hw0 : ∀ y, 0 ≤ w y := fun y => Finset.prod_nonneg fun l _ => hρ l (y l)
  set a : (S → F) → ℝ := fun y => if ∀ T ∈ P ∪ Q, ¬ Coin y T then 1 else 0 with ha
  set b : (S → F) → ℝ := fun y => if ∀ T ∈ Q, ¬ Coin y T then 1 else 0 with hb
  set cP : (S → F) → ℝ := fun y => ∑ T ∈ P, (if Coin y T then 1 else 0) with hcP
  set cQ : (S → F) → ℝ := fun y => ∑ T ∈ Q, (if Coin y T then 1 else 0) with hcQ
  have hind := fun y : S → F => inj_indicator_le P Q y
  -- the two terms as sums of nonpositive quantities
  have e : (∑ y, w y * a y * Φ y - ∑ y, w y * b y * Φ y) + (∑ y, w y * b y - ∑ y, w y) =
      -(∑ y, w y * ((b y - a y) * Φ y + (1 - b y))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hnn : 0 ≤ ∑ y, w y * ((b y - a y) * Φ y + (1 - b y)) :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hw0 y)
      (add_nonneg (mul_nonneg (hind y).1 (hΦ0 y)) (hind y).2.2.1)
  have hle : ∑ y, w y * ((b y - a y) * Φ y + (1 - b y)) ≤ ∑ y, w y * (M * cP y + cQ y) :=
    Finset.sum_le_sum fun y _ => by
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ (hind y).2.2.2) (hw0 y)
      have h1 := (hind y).2.1
      have h2 := (hind y).1
      have hcP0 : 0 ≤ cP y := Finset.sum_nonneg fun T _ => by split_ifs <;> norm_num
      calc (b y - a y) * Φ y ≤ (b y - a y) * M := mul_le_mul_of_nonneg_left (hΦM y) h2
        _ ≤ cP y * M := mul_le_mul_of_nonneg_right h1 ((hΦ0 y).trans (hΦM y))
        _ = M * cP y := by ring
  have hsP : ∑ y, w y * cP y = ∑ T ∈ P, ∑ y, w y * (if Coin y T then 1 else 0) := by
    simp only [hcP, Finset.mul_sum]
    exact Finset.sum_comm
  have hsQ : ∑ y, w y * cQ y = ∑ T ∈ Q, ∑ y, w y * (if Coin y T then 1 else 0) := by
    simp only [hcQ, Finset.mul_sum]
    exact Finset.sum_comm
  have hswap : ∑ y, w y * (M * cP y + cQ y) =
      M * ∑ T ∈ P, ∑ y, w y * (if Coin y T then 1 else 0) +
        ∑ T ∈ Q, ∑ y, w y * (if Coin y T then 1 else 0) := by
    rw [← hsP, ← hsQ, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  change |(∑ y, w y * a y * Φ y - ∑ y, w y * b y * Φ y) + (∑ y, w y * b y - ∑ y, w y)| ≤ _
  rw [e, abs_neg, abs_of_nonneg hnn, ← hswap]
  exact hle

end Sarkozy.Spectral
