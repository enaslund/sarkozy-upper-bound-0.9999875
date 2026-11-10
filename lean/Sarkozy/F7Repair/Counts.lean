module

public import Sarkozy.F7Repair.NewGraph

@[expose] public section

/-!
# Crude explicit count bounds at the tail primes (from Weil's bound H1)

`lem:graphs:sequential` (`Labellings.extCount_bounds`): the number of extensions of a feasible
labelling of a set `A` lies between the products `lowerProd` and `upperProd` of the one-step
bounds along any ordering of the other vertices. At a tail prime `q ≥ 2⁵¹²` and for graphs on at
most `72` vertices, every one-step ratio is at most `257/256`, uniformly in the degrees
(`stepUpper_le`). This gives, with no per-graph computation:

* `prod_ratio`: `upperProd ≤ (257/256)^{|l|} lowerProd` and `lowerProd > 0`;
* `nonempty_of_large`: `Inj_q(G) ≠ ∅` for every oriented graph on at most `72` vertices;
* `graphLaw_layer_weight`: the layer-`k` marginal of `λ_q(Γ)` is `extCount/|Inj|`;
* **`layer_density_le`**: for two graphs with the same edges inside layer `k` (e.g. `G^new` and
  `G = G_{φ₀φ₁,2}`), the layer-`k` marginal of `λ_q(Γ₁)` is at most `2` times that of `λ_q(Γ₂)`
  (`(257/256)^{144} ≤ 2`).

The constants are crude (the paper's (F1) evaluates the products exactly); at the tail they are
enough, since any explicit repair constant is free there.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.UpperComparison

/-! ### One step at a prime `q ≥ 2⁵¹²` -/

theorem gradedA_le {t : ℕ} (ht : t ≤ 72) : gradedA t ≤ 2 ^ 80 := by
  unfold gradedA
  split_ifs with h0
  · positivity
  · have h1 : ((t : ℝ) - 3) ≤ 72 := by
      have : (t : ℝ) ≤ 72 := by exact_mod_cast ht
      linarith
    have h2 : (2 : ℝ) ^ (t - 1) ≤ 2 ^ 71 := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (0 : ℝ) ≤ 2 ^ (t - 1) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) h3]

theorem gradedB_le {t : ℕ} (ht : t ≤ 72) : gradedB t ≤ 2 ^ 72 := by
  unfold gradedB
  split_ifs with h0
  · positivity
  · have h2 : (2 : ℝ) ^ (t - 1) ≤ 2 ^ 72 := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith

theorem sqrt_ge_of_large {q : ℝ} (hq : 2 ^ 512 ≤ q) : (2 : ℝ) ^ 256 ≤ Real.sqrt q := by
  have h : Real.sqrt ((2 : ℝ) ^ 512) = 2 ^ 256 := by
    rw [show (2 : ℝ) ^ 512 = (2 ^ 256) ^ 2 by rw [← pow_mul], Real.sqrt_sq (by positivity)]
  rw [← h]
  exact Real.sqrt_le_sqrt hq

/-- **One step at a large prime**: for `t, n ≤ 72` and `q ≥ 2⁵¹²`, `q − 𝔈_t − 2^t n > 0` and
`(q + 𝔈_t) · 256 ≤ 257 (q − 𝔈_t − 2^t n)`. -/
theorem step_main {q : ℝ} (hq : 2 ^ 512 ≤ q) {n : ℕ} (hn : n ≤ 72) {t : ℕ} (ht : t ≤ 72) :
    0 < q - softError q t - 2 ^ t * n ∧
      (q + softError q t) * 256 ≤ 257 * (q - softError q t - 2 ^ t * n) := by
  have hs := sqrt_ge_of_large hq
  have hq0 : 0 ≤ q := le_trans (by positivity) hq
  set s := Real.sqrt q with hsdef
  have hqs : q = s * s := (Real.mul_self_sqrt hq0).symm
  have hE : softError q t ≤ 2 ^ 80 * s + 2 ^ 72 := by
    unfold softError
    have h1 := gradedA_le ht
    have h2 := gradedB_le ht
    have h3 : 0 ≤ s := Real.sqrt_nonneg _
    nlinarith
  clear_value s
  have hT : (2 : ℝ) ^ t * n ≤ 2 ^ 79 := by
    have h1 : (2 : ℝ) ^ t ≤ 2 ^ 72 := pow_le_pow_right₀ (by norm_num) ht
    have h2 : (n : ℝ) ≤ 72 := by exact_mod_cast hn
    have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ 2 ^ t := by positivity
    calc (2 : ℝ) ^ t * n ≤ 2 ^ 72 * 72 := mul_le_mul h1 h2 h3 (by positivity)
      _ ≤ 2 ^ 79 := by norm_num
  have hT0 : (0 : ℝ) ≤ 2 ^ t * n := by positivity
  have hE0 := softError_nonneg q t
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  have h1 : (2 : ℝ) ^ 256 * s ≤ s * s := mul_le_mul_of_nonneg_right hs hs0
  have h2 : (2 ^ 256 - 513 * 2 ^ 80 : ℝ) * 2 ^ 256 ≤ (2 ^ 256 - 513 * 2 ^ 80) * s :=
    mul_le_mul_of_nonneg_left hs (by norm_num)
  have h3 : (513 * 2 ^ 72 + 257 * 2 ^ 79 : ℝ) < (2 ^ 256 - 513 * 2 ^ 80) * 2 ^ 256 := by norm_num
  have key : 513 * (2 ^ 80 * s + 2 ^ 72) + 257 * 2 ^ 79 < q := by
    rw [hqs]
    linarith only [h1, h2, h3]
  constructor
  · linarith only [hE, hT, key, hs0, hE0, hT0]
  · linarith only [hE, hT, key, hs0, hE0, hT0]

theorem stepLower_eq {q : ℝ} (hq : 2 ^ 512 ≤ q) {n : ℕ} (hn : n ≤ 72) {t : ℕ} (ht : t ≤ 72) :
    stepLower q n t = (q - softError q t - 2 ^ t * n) / 2 ^ t := by
  unfold stepLower
  exact max_eq_right (div_nonneg (step_main hq hn ht).1.le (by positivity))

theorem stepLower_pos {q : ℝ} (hq : 2 ^ 512 ≤ q) {n : ℕ} (hn : n ≤ 72) {t : ℕ} (ht : t ≤ 72) :
    0 < stepLower q n t := by
  rw [stepLower_eq hq hn ht]
  exact div_pos (step_main hq hn ht).1 (by positivity)

/-- **The one-step ratio is at most `257/256`** at `q ≥ 2⁵¹²`, `t, n ≤ 72`. -/
theorem stepUpper_le {q : ℝ} (hq : 2 ^ 512 ≤ q) {n : ℕ} (hn : n ≤ 72) {t : ℕ} (ht : t ≤ 72) :
    stepUpper q t ≤ 257 / 256 * stepLower q n t := by
  rw [stepLower_eq hq hn ht]
  unfold stepUpper
  have h := (step_main hq hn ht).2
  have h2 : (0 : ℝ) < 2 ^ t := by positivity
  rw [div_le_iff₀ h2]
  field_simp
  linarith

/-! ### Products along an ordering -/

variable {W : Type*} [Fintype W] [DecidableEq W]

theorem nbrCount_le_card (G : OrientedGraph W) (A : Finset W) (v : W) :
    nbrCount G A v ≤ Fintype.card W := by
  unfold nbrCount
  exact (card_filter_le _ _).trans (card_le_univ A)

/-- **`upperProd ≤ (257/256)^{|l|} lowerProd`, and `lowerProd > 0`**, at `q ≥ 2⁵¹²` on at most
`72` vertices. -/
theorem prod_ratio (G : OrientedGraph W) {q : ℝ} (hq : 2 ^ 512 ≤ q) {n : ℕ}
    (hW : Fintype.card W ≤ n) (hn : n ≤ 72) :
    ∀ (l : List W) (A : Finset W), upperProd G q A l ≤ (257 / 256 : ℝ) ^ l.length *
      lowerProd G q n A l ∧ 0 < lowerProd G q n A l
  | [], A => by simp [upperProd, lowerProd]
  | v :: l, A => by
      obtain ⟨h1, h2⟩ := prod_ratio G hq hW hn l (insert v A)
      have ht : nbrCount G A v ≤ 72 := ((nbrCount_le_card G A v).trans hW).trans hn
      have hq0 : 0 ≤ q := le_trans (by positivity) hq
      simp only [upperProd, lowerProd, List.length_cons]
      constructor
      · calc stepUpper q (nbrCount G A v) * upperProd G q (insert v A) l
            ≤ (257 / 256 * stepLower q n (nbrCount G A v)) *
                ((257 / 256 : ℝ) ^ l.length * lowerProd G q n (insert v A) l) :=
              mul_le_mul (stepUpper_le hq hn ht) h1 (upperProd_nonneg G hq0 l _)
                (by have := stepLower_pos hq hn ht; positivity)
          _ = (257 / 256 : ℝ) ^ (l.length + 1) *
                (stepLower q n (nbrCount G A v) * lowerProd G q n (insert v A) l) := by ring
      · exact mul_pos (stepLower_pos hq hn ht) h2

/-- `(257/256)^{144} ≤ 2`. -/
theorem ratio_pow_le : (257 / 256 : ℝ) ^ 144 ≤ 2 := by norm_num

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Every oriented graph on at most `72` vertices has a labelling** at `q ≥ 2⁵¹²` (H1). -/
theorem nonempty_of_large (hWeil : WeilBound F) (G : OrientedGraph W)
    (hq : (2 : ℝ) ^ 512 ≤ Fintype.card F) (hW : Fintype.card W ≤ 72) :
    (injLabellings F G).Nonempty := by
  have h := lowerProd_le_card_inj hWeil G le_rfl (univ : Finset W).toList (nodup_toList _)
    (fun w => mem_toList.mpr (mem_univ w))
  have hpos := (prod_ratio G hq le_rfl hW (univ : Finset W).toList ∅).2
  have hc : (0 : ℝ) < (injLabellings F G).card := lt_of_lt_of_le hpos h
  exact card_pos.mp (by exact_mod_cast hc)

/-- A labelling feasible on `univ` is feasible on every `A`, and feasibility on `A` depends only on
the values on `A`. -/
theorem extCount_eq_zero_of_not_feasible (G : OrientedGraph W) (A : Finset W) (x : W → F)
    (h : ¬ Feasible F G A x) : extCount G A x = 0 := by
  classical
  unfold extCount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro y hy hagree
  apply h
  have hf := (mem_injLabellings_iff_feasible G y).mp hy
  refine ⟨fun a ha b hb hab => hf.1 a (mem_univ _) b (mem_univ _) ?_, fun e he h1 h2 => ?_⟩
  · rw [hagree a ha, hagree b hb]
    exact hab
  · rw [← hagree _ h1, ← hagree _ h2]
    exact hf.2 e he (mem_univ _) (mem_univ _)

/-! ### Layer marginals of graph laws -/

variable {O₀ O₁ : Type*} [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁]

/-- The vertices of layer `k`. -/
noncomputable def layerSet (k : Fin 2) : Finset (O₀ × O₁ × Fin 2) := univ.filter fun w => w.2.2 = k

/-- A half labelling lifted to both layers. -/
def liftL (x : O₀ × O₁ → F) : O₀ × O₁ × Fin 2 → F := fun w => x (w.1, w.2.1)

omit [Field F] [Fintype F] [DecidableEq F] [DecidableEq O₀] [DecidableEq O₁] in
theorem agree_iff (k : Fin 2) (x : O₀ × O₁ → F) (y : O₀ × O₁ × Fin 2 → F) :
    (∀ a ∈ (layerSet k : Finset (O₀ × O₁ × Fin 2)), y a = liftL x a) ↔ layerOf y k = x := by
  constructor
  · intro h
    funext o
    have := h (o.1, o.2, k) (by simp [layerSet])
    exact this
  · intro h a ha
    have hk : a.2.2 = k := (mem_filter.mp ha).2
    have e : a = (a.1, a.2.1, k) := by rw [← hk]
    rw [e, ← h]
    rfl

/-- **The layer-`k` marginal of a graph law** is `extCount/|Inj|`. -/
theorem graphLaw_layer_weight (Γ : OrientedGraph (O₀ × O₁ × Fin 2))
    (hN : (injLabellings F Γ).Nonempty) (k : Fin 2) (x : O₀ × O₁ → F) :
    ((graphLaw Γ hN).map (fun y => layerOf y k)).weight x =
      (extCount Γ (layerSet k) (liftL x) : ℝ) / (injLabellings F Γ).card := by
  classical
  change (∑ y, if layerOf y k = x then (if y ∈ injLabellings F Γ then
    1 / ((injLabellings F Γ).card : ℝ) else 0) else 0) = _
  have e : ∀ y, (if layerOf y k = x then (if y ∈ injLabellings F Γ then
      1 / ((injLabellings F Γ).card : ℝ) else 0) else 0) =
      if y ∈ (injLabellings F Γ).filter (fun y => ∀ a ∈ (layerSet k : Finset (O₀ × O₁ × Fin 2)),
        y a = liftL x a) then 1 / ((injLabellings F Γ).card : ℝ) else 0 := by
    intro y
    have key := agree_iff k x y
    by_cases h1 : layerOf y k = x <;> by_cases h2 : y ∈ injLabellings F Γ <;>
      simp only [h1, h2, mem_filter, key, ↓reduceIte, and_self, and_true, and_false]
  rw [sum_congr rfl fun y _ => e y, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  unfold extCount
  rw [mul_one_div]

theorem sum_extCount (Γ : OrientedGraph (O₀ × O₁ × Fin 2)) (hN : (injLabellings F Γ).Nonempty)
    (k : Fin 2) : ∑ x : O₀ × O₁ → F, (extCount Γ (layerSet k) (liftL x) : ℝ) =
      (injLabellings F Γ).card := by
  have h := ((graphLaw Γ hN).map (fun y => layerOf y k)).total
  simp only [graphLaw_layer_weight] at h
  have hc : (0 : ℝ) < (injLabellings F Γ).card := by exact_mod_cast card_pos.mpr hN
  rw [← sum_div, div_eq_one_iff_eq hc.ne'] at h
  exact h

/-- **Layer marginals of two graph laws within a factor `2`** (`q ≥ 2⁵¹²`, at most `72` vertices):
if `Γ₁`, `Γ₂` have the same feasible labellings of layer `k`, the layer-`k` marginal of `λ_q(Γ₁)`
is at most twice that of `λ_q(Γ₂)`. -/
theorem layer_density_le (hWeil : WeilBound F) (Γ₁ Γ₂ : OrientedGraph (O₀ × O₁ × Fin 2))
    (hN₁ : (injLabellings F Γ₁).Nonempty) (hN₂ : (injLabellings F Γ₂).Nonempty) (k : Fin 2)
    (hfe : ∀ x : O₀ × O₁ × Fin 2 → F,
      Feasible F Γ₁ (layerSet k) x ↔ Feasible F Γ₂ (layerSet k) x)
    (hq : (2 : ℝ) ^ 512 ≤ Fintype.card F) (hW : Fintype.card (O₀ × O₁ × Fin 2) ≤ 72)
    (x : O₀ × O₁ → F) :
    ((graphLaw Γ₁ hN₁).map (fun y => layerOf y k)).weight x ≤
      2 * ((graphLaw Γ₂ hN₂).map (fun y => layerOf y k)).weight x := by
  classical
  set A : Finset (O₀ × O₁ × Fin 2) := layerSet k with hA
  set l := (univ \ A).toList with hl
  set q : ℝ := ((Fintype.card F : ℕ) : ℝ)
  set n := Fintype.card (O₀ × O₁ × Fin 2)
  have hnd : l.Nodup := nodup_toList _
  have hcov : ∀ w, w ∈ A ∨ w ∈ l := by
    intro w
    by_cases h : w ∈ A
    · exact Or.inl h
    · exact Or.inr (mem_toList.mpr (mem_sdiff.mpr ⟨mem_univ _, h⟩))
  have hdisj : ∀ w ∈ l, w ∉ A := fun w hw => (mem_sdiff.mp (mem_toList.mp hw)).2
  have hm : l.length ≤ 72 := by
    rw [hl, length_toList]
    exact (card_le_univ _).trans hW
  obtain ⟨hU₁, hL₁⟩ := prod_ratio Γ₁ hq le_rfl hW l A
  obtain ⟨hU₂, hL₂⟩ := prod_ratio Γ₂ hq le_rfl hW l A
  set L₁ := lowerProd Γ₁ q n A l
  set L₂ := lowerProd Γ₂ q n A l
  set R := (257 / 256 : ℝ) ^ l.length with hR
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR2 : R * R ≤ 2 := by
    rw [hR, ← pow_add]
    exact (pow_le_pow_right₀ (by norm_num) (by omega)).trans ratio_pow_le
  -- the feasible half labellings
  set S := univ.filter fun x : O₀ × O₁ → F => Feasible F Γ₂ A (liftL x) with hS
  have cnt : ∀ (Γ : OrientedGraph (O₀ × O₁ × Fin 2)) (hfΓ : ∀ x : O₀ × O₁ → F,
      Feasible F Γ A (liftL x) ↔ x ∈ S),
      (∀ x ∈ S, lowerProd Γ q n A l ≤ extCount Γ A (liftL x) ∧
        (extCount Γ A (liftL x) : ℝ) ≤ upperProd Γ q A l) ∧
      ∀ x ∉ S, extCount Γ A (liftL x) = 0 := by
    intro Γ hfΓ
    refine ⟨fun x hx => extCount_bounds hWeil Γ le_rfl l A _ hnd hcov hdisj ((hfΓ x).mpr hx),
      fun x hx => extCount_eq_zero_of_not_feasible Γ A _ (fun h => hx ((hfΓ x).mp h))⟩
  have hf₂ : ∀ x : O₀ × O₁ → F, Feasible F Γ₂ A (liftL x) ↔ x ∈ S := fun x => by
    rw [hS, mem_filter]
    exact ⟨fun h => ⟨mem_univ _, h⟩, fun h => h.2⟩
  have hf₁ : ∀ x : O₀ × O₁ → F, Feasible F Γ₁ A (liftL x) ↔ x ∈ S := fun x =>
    (hfe _).trans (hf₂ x)
  obtain ⟨b₁, z₁⟩ := cnt Γ₁ hf₁
  obtain ⟨b₂, z₂⟩ := cnt Γ₂ hf₂
  rw [graphLaw_layer_weight, graphLaw_layer_weight]
  by_cases hx : x ∈ S
  swap
  · rw [z₁ x hx]
    simp only [Nat.cast_zero, zero_div]
    exact mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have ha : (0 : ℝ) < S.card := by exact_mod_cast card_pos.mpr ⟨x, hx⟩
  -- the totals
  have hI₁ : (S.card : ℝ) * L₁ ≤ (injLabellings F Γ₁).card := by
    rw [← sum_extCount Γ₁ hN₁ k, ← hA]
    calc (S.card : ℝ) * L₁ = ∑ x ∈ S, L₁ := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ S, (extCount Γ₁ A (liftL x) : ℝ) := sum_le_sum fun x hx => (b₁ x hx).1
      _ ≤ ∑ x, (extCount Γ₁ A (liftL x) : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.cast_nonneg _
  have hI₂ : ((injLabellings F Γ₂).card : ℝ) ≤ S.card * (R * L₂) := by
    rw [← sum_extCount Γ₂ hN₂ k, ← hA]
    calc ∑ x, (extCount Γ₂ A (liftL x) : ℝ) = ∑ x ∈ S, (extCount Γ₂ A (liftL x) : ℝ) := by
          refine (sum_subset (subset_univ _) fun x _ hx => ?_).symm
          rw [z₂ x hx, Nat.cast_zero]
      _ ≤ ∑ x ∈ S, R * L₂ := sum_le_sum fun x hx => (b₂ x hx).2.trans hU₂
      _ = S.card * (R * L₂) := by rw [sum_const, nsmul_eq_mul]
  have hc₁ : (extCount Γ₁ A (liftL x) : ℝ) ≤ R * L₁ := (b₁ x hx).2.trans hU₁
  have hc₂ : L₂ ≤ (extCount Γ₂ A (liftL x) : ℝ) := (b₂ x hx).1
  have hI₁pos : (0 : ℝ) < (injLabellings F Γ₁).card := by exact_mod_cast card_pos.mpr hN₁
  have hI₂pos : (0 : ℝ) < (injLabellings F Γ₂).card := by exact_mod_cast card_pos.mpr hN₂
  clear_value R L₁ L₂
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have haR : (0 : ℝ) < S.card * R := mul_pos ha hR0
  have w₁le : (extCount Γ₁ A (liftL x) : ℝ) / (injLabellings F Γ₁).card ≤ R / S.card := by
    rw [div_le_div_iff₀ hI₁pos ha]
    have e1 := mul_le_mul_of_nonneg_right hc₁ ha.le
    have e2 := mul_le_mul_of_nonneg_left hI₁ hR0.le
    linarith
  have w₂ge : 1 / (S.card * R) ≤ (extCount Γ₂ A (liftL x) : ℝ) / (injLabellings F Γ₂).card := by
    rw [div_le_div_iff₀ haR hI₂pos]
    have e1 := mul_le_mul_of_nonneg_left hc₂ haR.le
    linarith
  have hfin : R / S.card ≤ 2 / (S.card * R) := by
    rw [div_le_div_iff₀ ha haR]
    have e1 := mul_le_mul_of_nonneg_left hR2 ha.le
    linarith
  calc (extCount Γ₁ A (liftL x) : ℝ) / (injLabellings F Γ₁).card ≤ R / S.card := w₁le
    _ ≤ 2 / (S.card * R) := hfin
    _ = 2 * (1 / (S.card * R)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left w₂ge (by norm_num)

end Sarkozy.F7Repair
