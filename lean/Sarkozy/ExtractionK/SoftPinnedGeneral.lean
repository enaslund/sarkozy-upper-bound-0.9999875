module

public import Sarkozy.ExtractionK.SoftPinned
public import Sarkozy.ExtractionK.SoftGeneral

@[expose] public section

/-!
# Soft pinned coincidences, all coefficients (`cor:soft-kernels`(c), `prop:pinned-collision`)

`paper/sections/16_extraction.tex`, `cor:soft-kernels`(c) for `prop:pinned-collision`, without
the restriction of `SoftPinned.lean` (`χ(-1) = -1` at the pairs with `D_{ij} < 0`): a factor with
`D_{ij} < 0` is flipped by an integer non-square `ν` (`skPinSgnN`), so the row sums of
`prop:pinned-collision` are re-proved for cross signs that are only nonzero in `F` on their support
(`sk_pin_free_sum_le_g`, `sk_pin_rowSum_le_g`: the proofs of `PinnedCollision.lean`, where the sign
hypothesis gives `χ(ς_{ij}) = ±1`).

* `sk_soft_pinned_collision_opBound_g`: `‖T^D‖ ≤ (D_X D_Y)^{1/2}` for all `|D_{ij}| ≤ 1`, given
  `ν` with `χ(ν) = -1`;
* **`sk_soft_pinned_collision_opBound_zmod`**: the same over `𝔽_p`, `p` odd, with no condition.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section SkPinG

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The free values of a coordinate** (`lem:extraction-merged-count` with the pins as the
conditions and no merged roots, since the cross roots `x_i` avoid `𝓜`):
`∑_{t allowed, t ∉ x([n])} ω_j(t) ≤ q 2^{-ϖ_j} (1 + e_{ϖ_j + |N_Y(j)|}(q, 2n + z))`. -/
theorem sk_pin_free_sum_le_g (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) (x : Fin n → F)
    (hxinj : Function.Injective x) (hxM : ∀ i, x i ∉ M) (j : Fin n) :
    ∑ t ∈ (pinAllowed M pin j).filter (fun t => t ∉ univ.image x), pinOmega ς x j t ≤
      (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ pinCount pin j *
        (1 + coarseError (pinCount pin j + (pinNY ς j).card) (Fintype.card F)
          (2 * n + M.card)) := by
  set ι := ↥(pinRoots pin j)
  set κ := ↥(pinNY ς j)
  let β : ι → F := fun b => b.1
  have hβ : Function.Injective β := fun a b h => Subtype.ext h
  let γ : κ → F := fun i => x i.1
  have hγ : Function.Injective γ := fun a b h => Subtype.ext (hxinj h)
  have hpm : ∀ b : ι, pin j b.1 = 1 ∨ pin j b.1 = -1 := by
    intro b
    have hb : pin j b.1 ≠ 0 := (mem_filter.mp b.2).2
    rcases hpin j b.1 with h | h | h
    · exact absurd h hb
    · exact Or.inl h
    · exact Or.inr h
  let s : ι → ℤ := fun b => quadraticChar F (pin j b.1 : F)
  have hs : ∀ b, s b = 1 ∨ s b = -1 := fun b => pin_char_pm (hpm b)
  let s' : κ → ℤ := fun i => quadraticChar F (ς i.1 j : F)
  have hs' : ∀ i, s' i = 1 ∨ s' i = -1 := fun i =>
    quadraticChar_dichotomy (hς i.1 j (mem_filter.mp i.2).2)
  set 𝒳 : Finset F := M ∪ univ.image x with h𝒳
  have hβX : ∀ b, β b ∈ 𝒳 := fun b =>
    mem_union_left _ (hpinM j b.1 (mem_filter.mp b.2).2)
  have hγX : ∀ i, γ i ∈ 𝒳 := fun i => mem_union_right _ (mem_image_of_mem x (mem_univ _))
  have hmc := merged_count_le_fintype hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX
    (n' := 2 * (n : ℝ) + M.card) (by positivity)
  have hm0 : mergedCount β γ = 0 := by
    unfold mergedCount
    rw [card_eq_zero, filter_eq_empty_iff]
    intro il _ h
    have h1 : β il.1 ∈ M := hpinM j il.1.1 (mem_filter.mp il.1.2).2
    have h2 : γ il.2 ∈ M := h ▸ h1
    exact hxM il.2.1 h2
  have hcι : Fintype.card ι = pinCount pin j := Fintype.card_coe _
  have hcκ : Fintype.card κ = (pinNY ς j).card := Fintype.card_coe _
  rw [hm0, hcι, hcκ, Nat.sub_zero, pow_zero, mul_one] at hmc
  have hset : (pinAllowed M pin j).filter (fun t => t ∉ univ.image x) =
      univ.filter (fun y => y ∉ 𝒳 ∧ ∀ b, quadraticChar F (y - β b) = s b) := by
    ext t
    simp only [pinAllowed, mem_filter, mem_univ, true_and, h𝒳, mem_union, not_or]
    constructor
    · rintro ⟨⟨htM, hpins⟩, htx⟩
      refine ⟨⟨htM, htx⟩, fun b => ?_⟩
      exact (pin_cond_iff (hpm b) _).mp (hpins b.1 (mem_filter.mp b.2).2)
    · rintro ⟨⟨htM, htx⟩, hall⟩
      refine ⟨⟨htM, fun b hb => ?_⟩, htx⟩
      have hbm : b ∈ pinRoots pin j := mem_filter.mpr ⟨mem_univ _, hb⟩
      exact (pin_cond_iff (hpm ⟨b, hbm⟩) _).mpr (hall ⟨b, hbm⟩)
  have hsum : ∀ t, pinOmega ς x j t = ∏ l, ((1 : ℝ) + s' l * quadraticChar F (t - γ l)) := by
    intro t
    unfold pinOmega
    rw [← prod_coe_sort (pinNY ς j)]
    refine prod_congr rfl fun i _ => ?_
    simp only [s', γ, map_mul, Int.cast_mul]
  rw [hset, sum_congr rfl fun t _ => hsum t]
  exact hmc

/-- **Row sums of `T^pin_coll`** (the proof of `prop:pinned-collision`): for `x ∈ 𝓘_pin`,
`∑_{y ∈ 𝓘_pin} K(x, y) ≤ D_Y |𝓘_pin|`, i.e. `E_{y ∼ μ} K(x, y) ≤ D_Y`. -/
theorem sk_pin_rowSum_le_g (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) (x : Fin n → F) (hx : x ∈ pinLab M pin) :
    ∑ y ∈ pinLab M pin, pinKer ς x y ≤
      pinD (Fintype.card F) M.card ϖ (pinNY ς) * (pinLab M pin).card := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast Fintype.card_pos
  obtain ⟨hxinj, hxM, -⟩ := mem_pinLab_iff.mp hx
  set c : Fin n → ℝ := fun j => q * (2 : ℝ)⁻¹ ^ pinCount pin j with hcdef
  set E : Fin n → ℝ := fun j => ePin q n M.card (ϖ + (pinNY ς j).card) with hEdef
  set u : Fin n → ℝ := fun j => (Real.sqrt q)⁻¹ ^ 2 * ∑ i,
    (2 : ℝ) ^ (ϖ + ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0)) with hudef
  set B : Fin n → ℝ := fun j => ∑ i,
    (2 : ℝ) ^ ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0) with hBdef
  have hc0 : ∀ j, 0 < c j := fun j => by simp only [hcdef]; positivity
  have hE0 : ∀ j, 0 ≤ E j := fun j => ePin_nonneg _ _ _ _
  have hu0 : ∀ j, 0 ≤ u j := fun j => by simp only [hudef]; positivity
  have hB0 : ∀ j, 0 ≤ B j := fun j => by simp only [hBdef]; positivity
  have hBu : ∀ j, B j ≤ c j * u j := by
    intro j
    simp only [hBdef, hcdef, hudef, mul_sum]
    refine sum_le_sum fun i _ => ?_
    have hr : q * (Real.sqrt q)⁻¹ ^ 2 = 1 := by
      rw [inv_pow, Real.sq_sqrt hq0.le, mul_inv_cancel₀ hq0.ne']
    have h2 : (1 : ℝ) ≤ (2 : ℝ)⁻¹ ^ pinCount pin j * 2 ^ ϖ := by
      have e2 : (2 : ℝ)⁻¹ ^ pinCount pin j * 2 ^ ϖ = 2 ^ (ϖ - pinCount pin j) := by
        calc (2 : ℝ)⁻¹ ^ pinCount pin j * 2 ^ ϖ
            = (2 : ℝ)⁻¹ ^ pinCount pin j * (2 ^ (ϖ - pinCount pin j) * 2 ^ pinCount pin j) := by
              rw [← pow_add, Nat.sub_add_cancel (hϖ j)]
          _ = 2 ^ (ϖ - pinCount pin j) * ((2 : ℝ)⁻¹ ^ pinCount pin j * 2 ^ pinCount pin j) := by
              ring
          _ = 2 ^ (ϖ - pinCount pin j) := by
              rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, mul_one]
      rw [e2]
      exact one_le_pow₀ (by norm_num)
    have h0 : (0 : ℝ) ≤ 2 ^ ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0) := by
      positivity
    calc (2 : ℝ) ^ ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0)
        ≤ ((2 : ℝ)⁻¹ ^ pinCount pin j * 2 ^ ϖ) *
            2 ^ ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0) :=
          le_mul_of_one_le_left h0 h2
      _ = q * (2 : ℝ)⁻¹ ^ pinCount pin j * ((Real.sqrt q)⁻¹ ^ 2 *
            (2 : ℝ) ^ (ϖ + ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0))) := by
          rw [pow_add]
          calc (2 : ℝ)⁻¹ ^ pinCount pin j * 2 ^ ϖ *
                2 ^ ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0)
              = (q * (Real.sqrt q)⁻¹ ^ 2) * ((2 : ℝ)⁻¹ ^ pinCount pin j * 2 ^ ϖ *
                  2 ^ ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0)) := by
                rw [hr, one_mul]
            _ = _ := by ring
  -- the one-coordinate bounds
  have hA : ∀ j, ∑ t ∈ pinAllowed M pin j, pinA ς x j t ≤ c j * (1 + E j) := by
    intro j
    have h1 : ∑ t ∈ pinAllowed M pin j, pinA ς x j t =
        ∑ t ∈ (pinAllowed M pin j).filter (fun t => t ∉ univ.image x), pinOmega ς x j t := by
      rw [sum_filter]
      refine sum_congr rfl fun t _ => ?_
      unfold pinA
      split_ifs <;> simp_all
    rw [h1]
    refine (sk_pin_free_sum_le_g hW M pin hpin hpinM ς hς x hxinj hxM j).trans ?_
    simp only [hcdef, hEdef]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := (coarseError_le_ePin q n M.card (pinCount pin j + (pinNY ς j).card)).trans
      (ePin_mono q n M.card (Nat.add_le_add_right (hϖ j) _))
    linarith
  have hBb : ∀ j, ∑ t ∈ pinAllowed M pin j, pinB ς x j t ≤ B j := by
    intro j
    have h1 : ∑ t ∈ pinAllowed M pin j, pinB ς x j t =
        ∑ t ∈ (pinAllowed M pin j).filter (fun t => t ∈ univ.image x), pinOmega ς x j t := by
      rw [sum_filter]
      refine sum_congr rfl fun t _ => ?_
      unfold pinB
      split_ifs <;> simp_all
    rw [h1]
    exact pin_coinc_sum_le ς x hxinj j _
  -- each stratum
  have hstrat : ∀ I ∈ (univ : Finset (Fin n)).powerset.erase ∅,
      ∑ y ∈ pinLab M pin, (∏ j ∈ I, pinB ς x j (y j)) * ∏ j ∈ univ \ I, pinA ς x j (y j) ≤
        (∏ j ∈ I, B j) * ∏ j ∈ univ \ I, (c j * (1 + E j)) := by
    intro I _
    have hite : ∀ y : Fin n → F, (∏ j ∈ I, pinB ς x j (y j)) * ∏ j ∈ univ \ I, pinA ς x j (y j) =
        ∏ j, (if j ∈ I then pinB ς x j (y j) else pinA ς x j (y j)) := by
      intro y
      rw [prod_ite, filter_mem_eq_inter, univ_inter, filter_notMem_eq_sdiff]
    have hite' : (∏ j ∈ I, B j) * ∏ j ∈ univ \ I, (c j * (1 + E j)) =
        ∏ j, (if j ∈ I then B j else c j * (1 + E j)) := by
      rw [prod_ite, filter_mem_eq_inter, univ_inter, filter_notMem_eq_sdiff]
    rw [hite']
    calc ∑ y ∈ pinLab M pin, (∏ j ∈ I, pinB ς x j (y j)) * ∏ j ∈ univ \ I, pinA ς x j (y j)
        = ∑ y ∈ pinLab M pin, ∏ j, (if j ∈ I then pinB ς x j (y j) else pinA ς x j (y j)) :=
          sum_congr rfl fun y _ => hite y
      _ ≤ ∑ y ∈ Fintype.piFinset (fun j => pinAllowed M pin j),
            ∏ j, (if j ∈ I then pinB ς x j (y j) else pinA ς x j (y j)) := by
          refine sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) fun y _ _ =>
            prod_nonneg fun j _ => ?_
          · rw [Fintype.mem_piFinset]
            exact (mem_pinLab.mp hy).2
          · split_ifs
            · exact pinB_nonneg ς x j _
            · exact pinA_nonneg ς x j _
      _ = ∏ j, ∑ t ∈ pinAllowed M pin j, (if j ∈ I then pinB ς x j t else pinA ς x j t) :=
          (prod_univ_sum (fun j => pinAllowed M pin j)
            (fun j t => if j ∈ I then pinB ς x j t else pinA ς x j t)).symm
      _ ≤ ∏ j, (if j ∈ I then B j else c j * (1 + E j)) := by
          refine prod_le_prod₀ (fun j _ => sum_nonneg fun t _ => ?_) fun j _ => ?_
          · split_ifs
            · exact pinB_nonneg ς x j t
            · exact pinA_nonneg ς x j t
          · split_ifs
            · exact hBb j
            · exact hA j
  -- the sum over the strata
  have hsumI : ∑ I ∈ (univ : Finset (Fin n)).powerset.erase ∅,
      (∏ j ∈ I, B j) * ∏ j ∈ univ \ I, (c j * (1 + E j)) =
        ∏ j, (B j + c j * (1 + E j)) - ∏ j, (c j * (1 + E j)) := by
    have h := prod_add B (fun j => c j * (1 + E j)) univ
    rw [← add_sum_erase _ _ (empty_mem_powerset univ), prod_empty, one_mul, sdiff_empty] at h
    rw [h]
    ring
  have hrow : ∑ y ∈ pinLab M pin, pinKer ς x y ≤
      ∏ j, (B j + c j * (1 + E j)) - ∏ j, (c j * (1 + E j)) := by
    rw [← hsumI]
    calc ∑ y ∈ pinLab M pin, pinKer ς x y
        = ∑ I ∈ (univ : Finset (Fin n)).powerset.erase ∅, ∑ y ∈ pinLab M pin,
            (∏ j ∈ I, pinB ς x j (y j)) * ∏ j ∈ univ \ I, pinA ς x j (y j) := by
          rw [sum_comm]
          exact sum_congr rfl fun y _ => pinKer_expand ς x y
      _ ≤ _ := sum_le_sum hstrat
  have halg := pin_algebra c E u B (ePin q n M.card ϖ) hc0 hE0 hu0 hB0 hBu he
  have hcount := card_pinLab_ge hW M pin hpin hpinM ϖ hϖ he
  have hD0 := pinD_nonneg q M.card ϖ (pinNY ς) he
  have hDeq : (∏ j, (1 + E j)) / (1 - ePin q n M.card ϖ) ^ n * (Real.exp (∑ j, u j) - 1) =
      pinD q M.card ϖ (pinNY ς) := by
    unfold pinD pinUps pinU
    congr 2
    simp only [hudef, ← mul_sum]
  rw [hDeq] at halg
  calc ∑ y ∈ pinLab M pin, pinKer ς x y
      ≤ ∏ j, (B j + c j * (1 + E j)) - ∏ j, (c j * (1 + E j)) := hrow
    _ ≤ pinD q M.card ϖ (pinNY ς) * ∏ j, (c j * (1 - ePin q n M.card ϖ)) := halg
    _ ≤ pinD q M.card ϖ (pinNY ς) * (pinLab M pin).card :=
        mul_le_mul_of_nonneg_left hcount hD0


/-- The signs restricted to `T` and multiplied by `ν` (`χ(ν) = -1`) at the pairs with a negative
coefficient. -/
noncomputable def skPinSgnN {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    (T : Finset (Fin n × Fin n)) (ν : ℤ) : Fin n → Fin n → ℤ :=
  fun i j => if (i, j) ∈ T then (if D (i, j) < 0 then ν * ς i j else ς i j) else 0

theorem sk_skPinE_sgnN {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    {T : Finset (Fin n × Fin n)} (hT : T ⊆ skPinE ς) {ν : ℤ} (hν0 : ν ≠ 0) :
    skPinE (skPinSgnN ς D T ν) = T := by
  ext e
  unfold skPinE skPinSgnN
  simp only [mem_filter, mem_univ, true_and, Prod.mk.eta]
  constructor
  · intro h
    by_contra he
    simp [he] at h
  · intro he
    have hς : ς e.1 e.2 ≠ 0 := by
      have := hT he
      unfold skPinE at this
      simpa using this
    simp only [he, ↓reduceIte]
    split_ifs
    · exact mul_ne_zero hν0 hς
    · exact hς

omit [Fintype F] [DecidableEq F] in
theorem sk_skPinSgnN_castF {n : ℕ} {ς : Fin n → Fin n → ℤ}
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) (D : Fin n × Fin n → ℝ)
    (T : Finset (Fin n × Fin n)) {ν : ℤ} (hνF : ((ν : ℤ) : F) ≠ 0) (i j : Fin n) :
    skPinSgnN ς D T ν i j ≠ 0 → ((skPinSgnN ς D T ν i j : ℤ) : F) ≠ 0 := by
  unfold skPinSgnN
  split_ifs with h1 h2
  · intro h
    have : ς i j ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
    push_cast
    exact mul_ne_zero hνF (hς i j this)
  · exact hς i j
  · intro h
    exact absurd rfl h

theorem sk_pinNY_sgnN_subset {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    (T : Finset (Fin n × Fin n)) (ν : ℤ) (j : Fin n) :
    pinNY (skPinSgnN ς D T ν) j ⊆ pinNY ς j := by
  intro i hi
  unfold pinNY skPinSgnN at *
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  intro h0
  apply hi
  split_ifs <;> simp [h0]

theorem sk_pin_flipN_identity {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    {T : Finset (Fin n × Fin n)} {e : Fin n × Fin n} (he : e ∈ T) {ν : ℤ}
    (hν : quadraticChar F ((ν : ℤ) : F) = -1) (x y : Fin n → F) :
    1 + D e * (quadraticChar F ((ς e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ) =
      |D e| * (1 + (quadraticChar F ((skPinSgnN ς D T ν e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ)) +
        (1 - |D e|) := by
  by_cases hD : D e < 0
  · have hflip : (quadraticChar F ((skPinSgnN ς D T ν e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ) =
        -(quadraticChar F ((ς e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ) := by
      unfold skPinSgnN
      simp only [Prod.mk.eta, he, hD, ↓reduceIte]
      push_cast
      rw [mul_assoc, map_mul, hν]
      push_cast
      ring
    rw [hflip, abs_of_neg hD]
    ring
  · push Not at hD
    have hflip : (quadraticChar F ((skPinSgnN ς D T ν e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ) =
        (quadraticChar F ((ς e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ) := by
      unfold skPinSgnN
      have : ¬ (D e < 0) := not_lt.mpr hD
      simp only [Prod.mk.eta, he, this, ↓reduceIte]
    rw [hflip, abs_of_nonneg hD]
    ring

/-- **The convex decomposition** of the soft pinned kernel into Boolean pinned kernels of the
signs restricted to `T ⊆ E_×` (and flipped where `D < 0`). -/
theorem sk_pinKer_expandN {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    {ν : ℤ} (hν : quadraticChar F ((ν : ℤ) : F) = -1) (x y : Fin n → F) :
    skPinKer ς D x y = ∑ T ∈ (skPinE ς).powerset,
      skW D (skPinE ς) T * pinKer (skPinSgnN ς D T ν) x y := by
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp at hν
  unfold skPinKer
  rw [sk_prod_pinNY ς (fun e => 1 + D e * (quadraticChar F ((ς e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ))]
  have hF : ∏ e ∈ skPinE ς, (1 + D e * (quadraticChar F ((ς e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ)) =
      ∏ e ∈ skPinE ς, (|D e| * (1 + (quadraticChar F
        ((skPinSgnN ς D (skPinE ς) ν e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ)) + (1 - |D e|)) :=
    prod_congr rfl fun e he => sk_pin_flipN_identity ς D he hν x y
  rw [hF, prod_add, mul_sum]
  refine sum_congr rfl fun T hT => ?_
  rw [mem_powerset] at hT
  unfold pinKer pinOmega skW
  rw [sk_prod_pinNY (skPinSgnN ς D T ν) (fun e => 1 + (quadraticChar F
    ((skPinSgnN ς D T ν e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ)), sk_skPinE_sgnN ς D hT hν0, prod_mul_distrib]
  have hTe : ∏ e ∈ T, (1 + (quadraticChar F
      ((skPinSgnN ς D (skPinE ς) ν e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ)) =
      ∏ e ∈ T, (1 + (quadraticChar F ((skPinSgnN ς D T ν e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ)) := by
    refine prod_congr rfl fun e he => ?_
    unfold skPinSgnN
    simp only [Prod.mk.eta, he, hT he, ↓reduceIte]
  rw [hTe]
  ring

/-- **Row sums of the soft pinned collision kernel**: `∑_y K^D(x, y) ≤ D_Y |𝓘_pin|`. -/
theorem sk_pin_rowSum_le_gN (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) (D : Fin n × Fin n → ℝ)
    (hD : ∀ e, |D e| ≤ 1) {ν : ℤ} (hν : quadraticChar F ((ν : ℤ) : F) = -1)
    (x : Fin n → F) (hx : x ∈ pinLab M pin) :
    ∑ y ∈ pinLab M pin, skPinKer ς D x y ≤
      pinD (Fintype.card F) M.card ϖ (pinNY ς) * (pinLab M pin).card := by
  have hνF : ((ν : ℤ) : F) ≠ 0 := by
    intro h
    rw [h, quadraticChar_zero] at hν
    norm_num at hν
  simp only [sk_pinKer_expandN ς D hν x]
  rw [sum_comm]
  have hw0 : ∀ T ∈ (skPinE ς).powerset, 0 ≤ skW D (skPinE ς) T :=
    fun T _ => skW_nonneg (fun e _ => hD e) T
  calc ∑ T ∈ (skPinE ς).powerset, ∑ y ∈ pinLab M pin,
        skW D (skPinE ς) T * pinKer (skPinSgnN ς D T ν) x y
      = ∑ T ∈ (skPinE ς).powerset, skW D (skPinE ς) T *
          ∑ y ∈ pinLab M pin, pinKer (skPinSgnN ς D T ν) x y :=
        sum_congr rfl fun T _ => (mul_sum _ _ _).symm
    _ ≤ ∑ T ∈ (skPinE ς).powerset, skW D (skPinE ς) T *
          (pinD (Fintype.card F) M.card ϖ (pinNY ς) * (pinLab M pin).card) := by
        refine sum_le_sum fun T hT => mul_le_mul_of_nonneg_left ?_ (hw0 T hT)
        refine (sk_pin_rowSum_le_g hW M pin hpin hpinM ϖ hϖ he (skPinSgnN ς D T ν)
          (sk_skPinSgnN_castF hς D T hνF) x hx).trans ?_
        exact mul_le_mul_of_nonneg_right
          (sk_pinD_mono _ _ _ (fun j => sk_pinNY_sgnN_subset ς D T ν j) he) (Nat.cast_nonneg _)
    _ = _ := by rw [← sum_mul, skW_sum, one_mul]

/-- **`cor:soft-kernels`(c) for `prop:pinned-collision`, all coefficients `|D_{ij}| ≤ 1`**, given an
integer `ν` with `χ(ν) = -1` (for `𝔽_p`, `sk_exists_nonsquare_int`). -/
theorem sk_soft_pinned_collision_opBound_g (hW : WeilBound F) {n : ℕ} (M : Finset F)
    (pin : Fin n → F → ℤ) (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (D : Fin n × Fin n → ℝ)
    (hD : ∀ e, |D e| ≤ 1) (ν : ℤ) (hν : quadraticChar F ((ν : ℤ) : F) = -1) :
    Sarkozy.Influence.OpBound (pinLab M pin) (pinLab M pin)
      (fun x y => skPinKer ς D x y / (pinLab M pin).card)
      (Real.sqrt (pinD (Fintype.card F) M.card ϖ (pinNX ς) *
        pinD (Fintype.card F) M.card ϖ (pinNY ς))) := by
  set N : ℝ := ((pinLab M pin).card : ℝ)
  have hςF : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0 := fun i j h0 => by
    rcases hς i j with h | h | h
    · exact absurd h h0
    · rw [h]; simp
    · rw [h]; simp
  have hD0 := pinD_nonneg (Fintype.card F) M.card ϖ (pinNY ς) he
  have hD0' := pinD_nonneg (Fintype.card F) M.card ϖ (pinNX ς) he
  have hrow : ∀ x ∈ pinLab M pin, ∑ y ∈ pinLab M pin, skPinKer ς D x y / N ≤
      pinD (Fintype.card F) M.card ϖ (pinNY ς) := by
    intro x hx
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (card_pos.mpr ⟨x, hx⟩)
    rw [← sum_div, div_le_iff₀ hN]
    exact sk_pin_rowSum_le_gN hW M pin hpin hpinM ϖ hϖ he ς hςF D hD hν x hx
  have hcol : ∀ y ∈ pinLab M pin, ∑ x ∈ pinLab M pin, skPinKer ς D x y / N ≤
      pinD (Fintype.card F) M.card ϖ (pinNX ς) := by
    intro y hy
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (card_pos.mpr ⟨y, hy⟩)
    rw [← sum_div, div_le_iff₀ hN]
    have h := sk_pin_rowSum_le_gN hW M pin hpin hpinM ϖ hϖ he (pinSwap ς)
      (fun i j h0 => by
        unfold pinSwap at h0 ⊢
        push_cast
        exact neg_ne_zero.mpr (hςF j i (neg_ne_zero.mp h0)))
      (fun e => D e.swap) (fun e => hD e.swap) hν y hy
    rw [pinNY_swap] at h
    calc ∑ x ∈ pinLab M pin, skPinKer ς D x y =
          ∑ x ∈ pinLab M pin, skPinKer (pinSwap ς) (fun e => D e.swap) y x :=
          sum_congr rfl fun x _ => sk_pinKer_soft_swap ς D x y
      _ ≤ _ := h
  have h := Sarkozy.Influence.opBound_schur (R := pinLab M pin) (C := pinLab M pin)
    (A := fun x y => skPinKer ς D x y / N)
    (fun x y => div_nonneg (sk_pinKer_soft_nonneg ς D hD x y) (Nat.cast_nonneg _)) hD0 hD0' hrow
    hcol
  rwa [mul_comm] at h

end SkPinG

section SkPinZMod

variable {p : ℕ} [Fact p.Prime]

/-- **`cor:soft-kernels`(c) for `prop:pinned-collision` over `𝔽_p`, `p` odd, all coefficients
`|D_{ij}| ≤ 1`** (no further condition). -/
theorem sk_soft_pinned_collision_opBound_zmod (hp2 : p ≠ 2) (hW : WeilBound (ZMod p)) {n : ℕ}
    (M : Finset (ZMod p)) (pin : Fin n → ZMod p → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card (ZMod p)) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (D : Fin n × Fin n → ℝ)
    (hD : ∀ e, |D e| ≤ 1) :
    Sarkozy.Influence.OpBound (pinLab M pin) (pinLab M pin)
      (fun x y => skPinKer ς D x y / (pinLab M pin).card)
      (Real.sqrt (pinD (Fintype.card (ZMod p)) M.card ϖ (pinNX ς) *
        pinD (Fintype.card (ZMod p)) M.card ϖ (pinNY ς))) := by
  obtain ⟨ν, hν⟩ := sk_exists_nonsquare_int (p := p) hp2
  exact sk_soft_pinned_collision_opBound_g hW M pin hpin hpinM ϖ hϖ he ς hς D hD ν hν

end SkPinZMod

end Sarkozy.ExtractionK
