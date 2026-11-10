module

public import Sarkozy.F7Repair.Counts

@[expose] public section

/-!
# Count bounds of order `r` at the tail primes (from Weil's bound H1)

The refinement of `Counts.lean` that (F7) needs: at `q ≥ 2⁵¹²` every one-step ratio is at most
`R_q = 1 + 2⁹⁰/√q` (`step_fine`), and a pinned set larger by vertices of degree at most `D` into
the new vertices costs at most `2^D` per step (`prod_fine`). Consequences:

* `pow_le_one_add`: `(1 + δ)^m ≤ 1 + 2mδ` for `mδ ≤ 1/2`;
* **`layer_density_fine`**: two graphs with the same feasible labellings of a layer have layer
  marginals within the factor `R_q^{144} ≤ 1 + 2⁹⁹/√q` of each other.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.UpperComparison

/-- The one-step ratio `R_q = 1 + 2⁹⁰/√q`. -/
noncomputable def fineR (q : ℝ) : ℝ := 1 + 2 ^ 90 / Real.sqrt q

theorem fineR_ge_one (q : ℝ) : 1 ≤ fineR q := by
  unfold fineR
  have := div_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ 90) (Real.sqrt_nonneg q)
  linarith

theorem fineR_le_two {q : ℝ} (hq : 2 ^ 512 ≤ q) : fineR q ≤ 2 := by
  unfold fineR
  have hs := sqrt_ge_of_large hq
  have hs0 : (0 : ℝ) < Real.sqrt q := lt_of_lt_of_le (by positivity) hs
  have : (2 : ℝ) ^ 90 / Real.sqrt q ≤ 1 := by
    rw [div_le_one hs0]
    exact le_trans (by norm_num) hs
  linarith

/-- **One step with a larger pinned set**: for `t ≤ t' ≤ 72`, `n ≤ 72`, `q ≥ 2⁵¹²`,
`stepUpper q t ≤ R_q 2^{t'−t} stepLower q n t'`. -/
theorem step_fine {q : ℝ} (hq : 2 ^ 512 ≤ q) {n : ℕ} (hn : n ≤ 72) {t t' : ℕ} (htt : t ≤ t')
    (ht' : t' ≤ 72) :
    stepUpper q t ≤ fineR q * 2 ^ (t' - t) * stepLower q n t' := by
  have ht : t ≤ 72 := htt.trans ht'
  rw [stepLower_eq hq hn ht']
  unfold stepUpper fineR
  have hs := sqrt_ge_of_large hq
  have hq0 : 0 ≤ q := le_trans (by positivity) hq
  have hs0 : (0 : ℝ) < Real.sqrt q := lt_of_lt_of_le (by positivity) hs
  set s := Real.sqrt q with hsdef
  have hqs : q = s * s := (Real.mul_self_sqrt hq0).symm
  have hE : softError q t ≤ 2 ^ 80 * s + 2 ^ 72 := by
    unfold softError
    have h1 := gradedA_le ht
    have h2 := gradedB_le ht
    have h3 : 0 ≤ s := hs0.le
    nlinarith
  have hE' : softError q t' ≤ 2 ^ 80 * s + 2 ^ 72 := by
    unfold softError
    have h1 := gradedA_le ht'
    have h2 := gradedB_le ht'
    have h3 : 0 ≤ s := hs0.le
    nlinarith
  have hT : (2 : ℝ) ^ t' * n ≤ 2 ^ 79 := by
    have h1 : (2 : ℝ) ^ t' ≤ 2 ^ 72 := pow_le_pow_right₀ (by norm_num) ht'
    have h2 : (n : ℝ) ≤ 72 := by exact_mod_cast hn
    calc (2 : ℝ) ^ t' * n ≤ 2 ^ 72 * 72 := mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
      _ ≤ 2 ^ 79 := by norm_num
  have hT0 : (0 : ℝ) ≤ 2 ^ t' * n := by positivity
  have hE0 := softError_nonneg q t
  have hE0' := softError_nonneg q t'
  set δ := (2 : ℝ) ^ 90 / s with hδ
  have hδ0 : 0 ≤ δ := div_nonneg (by positivity) hs0.le
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one hs0]
    exact le_trans (by norm_num) hs
  have hδq : δ * q = 2 ^ 90 * s := by
    rw [hδ, hqs]
    field_simp
  clear_value s δ
  have hm : δ * (softError q t' + 2 ^ t' * n) ≤ softError q t' + 2 ^ t' * n :=
    mul_le_of_le_one_left (by positivity) hδ1
  have hbig : 3 * (2 ^ 80 * s + 2 ^ 72) + 2 * 2 ^ 79 ≤ 2 ^ 90 * s := by
    have : (2 : ℝ) ^ 90 * 2 ^ 256 ≤ 2 ^ 90 * s := mul_le_mul_of_nonneg_left hs (by positivity)
    have h2 : (0 : ℝ) ≤ s := hs0.le
    nlinarith
  have key : q + softError q t ≤ (1 + δ) * (q - softError q t' - 2 ^ t' * n) := by
    have e : (1 + δ) * (q - softError q t' - 2 ^ t' * n) =
        q - softError q t' - 2 ^ t' * n + δ * q - δ * (softError q t' + 2 ^ t' * n) := by ring
    rw [e]
    linarith only [hm, hδq, hE, hE', hT, hT0, hE0, hE0', hbig]
  have h2 : (2 : ℝ) ^ t' = 2 ^ (t' - t) * 2 ^ t := by
    rw [← pow_add, Nat.sub_add_cancel htt]
  rw [h2]
  have hp : (0 : ℝ) < 2 ^ t := by positivity
  have hp' : (0 : ℝ) < 2 ^ (t' - t) := by positivity
  rw [show (1 + δ) * 2 ^ (t' - t) * ((q - softError q t' - 2 ^ (t' - t) * 2 ^ t * n) /
      (2 ^ (t' - t) * 2 ^ t)) = (1 + δ) * (q - softError q t' - 2 ^ t' * n) / 2 ^ t by
    rw [h2]; field_simp]
  exact div_le_div_of_nonneg_right key hp.le

variable {W : Type*} [Fintype W] [DecidableEq W]

omit [Fintype W] in
theorem nbrCount_mono (G : OrientedGraph W) {A A' : Finset W} (h : A ⊆ A') (v : W) :
    nbrCount G A v ≤ nbrCount G A' v := by
  classical
  unfold nbrCount
  exact card_le_card (filter_subset_filter _ h)

/-- **Products with a larger pinned set**: if `A ⊆ A'` and, for every set `S` and every vertex of
`l`, pinning `A' ∪ S` instead of `A ∪ S` adds at most `D` neighbours, then
`upperProd(A, l) ≤ (R_q 2^D)^{|l|} lowerProd(A', l)` and `lowerProd(A', l) > 0`. -/
theorem prod_fine (G : OrientedGraph W) {q : ℝ} (hq : 2 ^ 512 ≤ q) {n : ℕ}
    (hW : Fintype.card W ≤ n) (hn : n ≤ 72) (D : ℕ) :
    ∀ (l : List W) (A A' : Finset W), A ⊆ A' →
      (∀ S : Finset W, ∀ v ∈ l, nbrCount G (A' ∪ S) v ≤ nbrCount G (A ∪ S) v + D) →
      upperProd G q A l ≤ (fineR q * 2 ^ D) ^ l.length * lowerProd G q n A' l ∧
        0 < lowerProd G q n A' l
  | [], A, A', _, _ => by simp [upperProd, lowerProd]
  | v :: l, A, A', hAA, hD => by
      have hrec := prod_fine G hq hW hn D l (insert v A) (insert v A')
        (insert_subset_insert v hAA) (fun S w hw => by
          rw [insert_union, insert_union, ← union_insert, ← union_insert]
          exact hD (insert v S) w (List.mem_cons_of_mem v hw))
      obtain ⟨h1, h2⟩ := hrec
      have htt : nbrCount G A v ≤ nbrCount G A' v := nbrCount_mono G hAA v
      have ht'D : nbrCount G A' v ≤ nbrCount G A v + D := by
        have := hD ∅ v List.mem_cons_self
        rwa [union_empty, union_empty] at this
      have ht' : nbrCount G A' v ≤ 72 := ((nbrCount_le_card G A' v).trans hW).trans hn
      have hq0 : 0 ≤ q := le_trans (by positivity) hq
      have hR := fineR_ge_one q
      have hstep : stepUpper q (nbrCount G A v) ≤
          fineR q * 2 ^ D * stepLower q n (nbrCount G A' v) := by
        refine (step_fine hq hn htt ht').trans ?_
        have hpow : (2 : ℝ) ^ (nbrCount G A' v - nbrCount G A v) ≤ 2 ^ D :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have := stepLower_pos hq hn ht'
        have : 0 ≤ fineR q := by linarith
        gcongr
      simp only [upperProd, lowerProd, List.length_cons]
      constructor
      · calc stepUpper q (nbrCount G A v) * upperProd G q (insert v A) l
            ≤ (fineR q * 2 ^ D * stepLower q n (nbrCount G A' v)) *
                ((fineR q * 2 ^ D) ^ l.length * lowerProd G q n (insert v A') l) :=
              mul_le_mul hstep h1 (upperProd_nonneg G hq0 l _)
                (by have := stepLower_pos hq hn ht'; have : 0 ≤ fineR q := by linarith
                    positivity)
          _ = (fineR q * 2 ^ D) ^ (l.length + 1) *
                (stepLower q n (nbrCount G A' v) * lowerProd G q n (insert v A') l) := by ring
      · exact mul_pos (stepLower_pos hq hn ht') h2

/-- `(1 + δ)^m ≤ 1 + 2mδ` for `0 ≤ δ`, `mδ ≤ 1/2`. -/
theorem pow_le_one_add {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ m : ℕ, (m : ℝ) * δ ≤ 1 / 2 → (1 + δ) ^ m ≤ 1 + 2 * m * δ
  | 0, _ => by simp
  | m + 1, h => by
      have h' : (m : ℝ) * δ ≤ 1 / 2 := by
        push_cast at h
        nlinarith
      have ih := pow_le_one_add hδ m h'
      rw [pow_succ]
      push_cast at h ⊢
      have : 0 ≤ (1 : ℝ) + δ := by linarith
      calc (1 + δ) ^ m * (1 + δ) ≤ (1 + 2 * m * δ) * (1 + δ) := mul_le_mul_of_nonneg_right ih this
        _ ≤ 1 + 2 * (m + 1) * δ := by nlinarith

/-- `R_q^{144} ≤ 1 + 2⁹⁹/√q`. -/
theorem fineR_pow_le {q : ℝ} (hq : 2 ^ 512 ≤ q) :
    fineR q ^ 144 ≤ 1 + 2 ^ 99 / Real.sqrt q := by
  have hs := sqrt_ge_of_large hq
  have hs0 : (0 : ℝ) < Real.sqrt q := lt_of_lt_of_le (by positivity) hs
  have hδ0 : (0 : ℝ) ≤ 2 ^ 90 / Real.sqrt q := div_nonneg (by positivity) hs0.le
  have hm : ((144 : ℕ) : ℝ) * (2 ^ 90 / Real.sqrt q) ≤ 1 / 2 := by
    push_cast
    rw [mul_div_assoc', div_le_div_iff₀ hs0 (by norm_num)]
    have h1 : (144 * 2 ^ 90 * 2 : ℝ) ≤ 2 ^ 256 := by norm_num
    linarith only [h1, hs]
  have h := pow_le_one_add hδ0 144 hm
  unfold fineR
  refine h.trans ?_
  push_cast
  have h2 : 2 * 144 * (2 ^ 90 / Real.sqrt q) ≤ 2 ^ 99 / Real.sqrt q := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by norm_num) hs0.le
  linarith

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {O₀ O₁ : Type*} [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁]

/-- **Layer marginals of two graph laws within `R_q^{144}`** (`q ≥ 2⁵¹²`, at most `72` vertices):
if `Γ₁`, `Γ₂` have the same feasible labellings of layer `k`, the layer-`k` marginal of `λ_q(Γ₁)`
is at most `R_q^{144}` times that of `λ_q(Γ₂)`. -/
theorem layer_density_fine (hWeil : WeilBound F) (Γ₁ Γ₂ : OrientedGraph (O₀ × O₁ × Fin 2))
    (hN₁ : (injLabellings F Γ₁).Nonempty) (hN₂ : (injLabellings F Γ₂).Nonempty) (k : Fin 2)
    (hfe : ∀ x : O₀ × O₁ × Fin 2 → F,
      Feasible F Γ₁ (layerSet k) x ↔ Feasible F Γ₂ (layerSet k) x)
    (hq : (2 : ℝ) ^ 512 ≤ Fintype.card F) (hW : Fintype.card (O₀ × O₁ × Fin 2) ≤ 72)
    (x : O₀ × O₁ → F) :
    ((graphLaw Γ₁ hN₁).map (fun y => layerOf y k)).weight x ≤
      fineR (Fintype.card F) ^ 144 * ((graphLaw Γ₂ hN₂).map (fun y => layerOf y k)).weight x := by
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
  have hD0 : ∀ (Γ : OrientedGraph (O₀ × O₁ × Fin 2)) (S : Finset (O₀ × O₁ × Fin 2)), ∀ v ∈ l,
      nbrCount Γ (A ∪ S) v ≤ nbrCount Γ (A ∪ S) v + 0 := fun _ _ _ _ => le_rfl
  obtain ⟨hU₁, hL₁⟩ := prod_fine Γ₁ hq le_rfl hW 0 l A A subset_rfl (hD0 Γ₁)
  obtain ⟨hU₂, hL₂⟩ := prod_fine Γ₂ hq le_rfl hW 0 l A A subset_rfl (hD0 Γ₂)
  simp only [pow_zero, mul_one] at hU₁ hU₂
  set L₁ := lowerProd Γ₁ q n A l
  set L₂ := lowerProd Γ₂ q n A l
  set R := fineR q ^ l.length with hR
  have hR1 : 1 ≤ R := one_le_pow₀ (fineR_ge_one q)
  have hR2 : R * R ≤ fineR q ^ 144 := by
    rw [hR, ← pow_add]
    exact pow_le_pow_right₀ (fineR_ge_one q) (by omega)
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
    exact mul_nonneg (pow_nonneg (by linarith [fineR_ge_one q]) _)
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have ha : (0 : ℝ) < S.card := by exact_mod_cast card_pos.mpr ⟨x, hx⟩
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
  have hfin : R / S.card ≤ fineR q ^ 144 / (S.card * R) := by
    rw [div_le_div_iff₀ ha haR]
    have e1 := mul_le_mul_of_nonneg_left hR2 ha.le
    linarith
  calc (extCount Γ₁ A (liftL x) : ℝ) / (injLabellings F Γ₁).card ≤ R / S.card := w₁le
    _ ≤ fineR q ^ 144 / (S.card * R) := hfin
    _ = fineR q ^ 144 * (1 / (S.card * R)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left w₂ge (pow_nonneg (by linarith [fineR_ge_one q]) _)

end Sarkozy.F7Repair
