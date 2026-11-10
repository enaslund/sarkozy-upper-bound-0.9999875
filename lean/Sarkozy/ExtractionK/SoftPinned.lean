module

public import Sarkozy.ExtractionK.PinnedCollision
public import Sarkozy.ExtractionK.SoftCore

@[expose] public section

/-!
# Soft cross factors for the pinned coincidences (`cor:soft-kernels`(c), `prop:pinned-collision`)

`paper/sections/16_extraction.tex`, `cor:soft-kernels`(c): the bound of `prop:pinned-collision`
holds for the soft pinned collision kernel `1{x([n]) ∩ y([n]) ≠ ∅} ∏_{(i,j) ∈ E_×}(1 + D_{ij} χ_{ij})`,
`|D_{ij}| ≤ 1` (`skPinKer`).

* `sk_pinKer_expand`: the soft kernel is a convex combination (weights `skW`) of the Boolean pinned
  kernels of the signs restricted to `T ⊆ E_×` (flipped to `-ς` where `D < 0`; this uses
  `χ(-1) = -1` at such pairs).
* `sk_pinD_mono`: `D_Y` is nondecreasing in the neighbourhoods; `sk_pin_rowSum_le`: the row sums
  are at most `D_Y` (via `pin_rowSum_le` for each `T`); `sk_pinKer_soft_swap`: the column sums are
  row sums of the transposed soft kernel.
* **`sk_soft_pinned_collision_opBound`**: `‖T^D‖ ≤ (D_X D_Y)^{1/2}` by Schur's test, for
  `|D_{ij}| ≤ 1`, provided `χ(-1) = -1` if some `D_{ij} < 0` (no condition when `D ≥ 0`).

Not covered: negative coefficients when `χ(-1) = 1` (as in `SoftCore.lean`), and
`prop:pinned-extraction` (not formalized).
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section SkPin

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The soft pinned collision kernel
`1{x([n]) ∩ y([n]) ≠ ∅} ∏_{(i,j) ∈ E_×} (1 + D_{ij} χ_{ij}(x, y))`. -/
noncomputable def skPinKer {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    (x y : Fin n → F) : ℝ :=
  (if ∃ i j, x i = y j then (1 : ℝ) else 0) *
    ∏ j, ∏ i ∈ pinNY ς j, (1 + D (i, j) * (quadraticChar F ((ς i j : F) * (y j - x i)) : ℝ))

/-- The cross pairs `E_× = {(i, j) : ς_{ij} ≠ 0}`. -/
def skPinE {n : ℕ} (ς : Fin n → Fin n → ℤ) : Finset (Fin n × Fin n) :=
  univ.filter fun e => ς e.1 e.2 ≠ 0

/-- The signs restricted to `T` and flipped (`-ς`) at the pairs with a negative coefficient. -/
noncomputable def skPinSgn {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    (T : Finset (Fin n × Fin n)) : Fin n → Fin n → ℤ :=
  fun i j => if (i, j) ∈ T then (if D (i, j) < 0 then -ς i j else ς i j) else 0

theorem sk_prod_pinNY {n : ℕ} (ς : Fin n → Fin n → ℤ) (g : Fin n × Fin n → ℝ) :
    ∏ j, ∏ i ∈ pinNY ς j, g (i, j) = ∏ e ∈ skPinE ς, g e := by
  unfold pinNY skPinE
  simp only [prod_filter]
  rw [Fintype.prod_prod_type, prod_comm]

theorem sk_skPinE_sgn {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    {T : Finset (Fin n × Fin n)} (hT : T ⊆ skPinE ς) : skPinE (skPinSgn ς D T) = T := by
  ext e
  unfold skPinE skPinSgn
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
    split_ifs <;> simpa using hς

theorem sk_skPinSgn_values {n : ℕ} {ς : Fin n → Fin n → ℤ}
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (D : Fin n × Fin n → ℝ)
    (T : Finset (Fin n × Fin n)) (i j : Fin n) :
    skPinSgn ς D T i j = 0 ∨ skPinSgn ς D T i j = 1 ∨ skPinSgn ς D T i j = -1 := by
  unfold skPinSgn
  split_ifs
  · rcases hς i j with h | h | h <;> simp [h]
  · exact hς i j
  · exact Or.inl rfl

theorem sk_pinNY_sgn_subset {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    (T : Finset (Fin n × Fin n)) (j : Fin n) : pinNY (skPinSgn ς D T) j ⊆ pinNY ς j := by
  intro i hi
  unfold pinNY skPinSgn at *
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  intro h0
  apply hi
  split_ifs <;> simp [h0]

/-- The pointwise identity of a soft factor (flipped sign when `D < 0`, using `χ(-1) = -1`). -/
theorem sk_pin_flip_identity {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    {T : Finset (Fin n × Fin n)} {e : Fin n × Fin n} (he : e ∈ T)
    (hneg : D e < 0 → quadraticChar F (-1) = -1) (x y : Fin n → F) :
    1 + D e * (quadraticChar F ((ς e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ) =
      |D e| * (1 + (quadraticChar F ((skPinSgn ς D T e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ)) +
        (1 - |D e|) := by
  by_cases hD : D e < 0
  · have hm := hneg hD
    have hflip : (quadraticChar F ((skPinSgn ς D T e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ) =
        -(quadraticChar F ((ς e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ) := by
      unfold skPinSgn
      simp only [Prod.mk.eta, he, hD, ↓reduceIte, Int.cast_neg]
      have : (-(ς e.1 e.2 : F)) * (y e.2 - x e.1) =
          (-1) * ((ς e.1 e.2 : F) * (y e.2 - x e.1)) := by ring
      rw [this, map_mul, hm]
      push_cast
      ring
    rw [hflip, abs_of_neg hD]
    ring
  · push Not at hD
    have hflip : (quadraticChar F ((skPinSgn ς D T e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ) =
        (quadraticChar F ((ς e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ) := by
      unfold skPinSgn
      have : ¬ (D e < 0) := not_lt.mpr hD
      simp only [Prod.mk.eta, he, this, ↓reduceIte]
    rw [hflip, abs_of_nonneg hD]
    ring

/-- **The convex decomposition** of the soft pinned kernel into Boolean pinned kernels of the
signs restricted to `T ⊆ E_×` (and flipped where `D < 0`). -/
theorem sk_pinKer_expand {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    (hneg : ∀ e, D e < 0 → quadraticChar F (-1) = -1) (x y : Fin n → F) :
    skPinKer ς D x y = ∑ T ∈ (skPinE ς).powerset,
      skW D (skPinE ς) T * pinKer (skPinSgn ς D T) x y := by
  unfold skPinKer
  rw [sk_prod_pinNY ς (fun e => 1 + D e * (quadraticChar F ((ς e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ))]
  have hF : ∏ e ∈ skPinE ς, (1 + D e * (quadraticChar F ((ς e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ)) =
      ∏ e ∈ skPinE ς, (|D e| * (1 + (quadraticChar F
        ((skPinSgn ς D (skPinE ς) e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ)) + (1 - |D e|)) :=
    prod_congr rfl fun e he => sk_pin_flip_identity ς D he (hneg e) x y
  rw [hF, prod_add, mul_sum]
  refine sum_congr rfl fun T hT => ?_
  rw [mem_powerset] at hT
  unfold pinKer pinOmega skW
  rw [sk_prod_pinNY (skPinSgn ς D T) (fun e => 1 + (quadraticChar F
    ((skPinSgn ς D T e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ)), sk_skPinE_sgn ς D hT, prod_mul_distrib]
  have hTe : ∏ e ∈ T, (1 + (quadraticChar F
      ((skPinSgn ς D (skPinE ς) e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ)) =
      ∏ e ∈ T, (1 + (quadraticChar F ((skPinSgn ς D T e.1 e.2 : F) * (y e.2 - x e.1)) : ℝ)) := by
    refine prod_congr rfl fun e he => ?_
    unfold skPinSgn
    simp only [Prod.mk.eta, he, hT he, ↓reduceIte]
  rw [hTe]
  ring

theorem sk_pin_exp_mono {n : ℕ} {N N' : Finset (Fin n)} (h : N ⊆ N') (ϖ : ℕ) (i : Fin n) :
    ϖ + (N.card - if i ∈ N then 1 else 0) ≤ ϖ + (N'.card - if i ∈ N' then 1 else 0) := by
  by_cases hi : i ∈ N
  · have hi' : i ∈ N' := h hi
    simp only [hi, hi', ↓reduceIte]
    have := card_le_card h
    omega
  · by_cases hi' : i ∈ N'
    · simp only [hi, hi', ↓reduceIte]
      have := card_lt_card ⟨h, fun h' => hi (h' hi')⟩
      omega
    · simp only [hi, hi', ↓reduceIte]
      have := card_le_card h
      omega

/-- `D_Y` is nondecreasing in the neighbourhoods. -/
theorem sk_pinD_mono {n : ℕ} (q : ℝ) (z ϖ : ℕ) {N N' : Fin n → Finset (Fin n)}
    (hN : ∀ j, N j ⊆ N' j) (he : ePin q n z ϖ < 1) : pinD q z ϖ N ≤ pinD q z ϖ N' := by
  unfold pinD pinUps pinU
  have h1 : 0 < 1 - ePin q n z ϖ := by linarith
  have hUps : ∏ j, (1 + ePin q n z (ϖ + (N j).card)) ≤ ∏ j, (1 + ePin q n z (ϖ + (N' j).card)) :=
    prod_le_prod₀ (fun j _ => by linarith [ePin_nonneg q n z (ϖ + (N j).card)])
      (fun j _ => by linarith [ePin_mono q n z (Nat.add_le_add_left (card_le_card (hN j)) ϖ)])
  have hU : (Real.sqrt q)⁻¹ ^ 2 * ∑ j, ∑ i, (2 : ℝ) ^ (ϖ + ((N j).card - if i ∈ N j then 1 else 0)) ≤
      (Real.sqrt q)⁻¹ ^ 2 * ∑ j, ∑ i,
        (2 : ℝ) ^ (ϖ + ((N' j).card - if i ∈ N' j then 1 else 0)) := by
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => sum_le_sum fun i _ => ?_) (sq_nonneg _)
    exact pow_le_pow_right₀ (by norm_num) (sk_pin_exp_mono (hN j) ϖ i)
  have hexp := Real.exp_le_exp.mpr hU
  have hU0 : 0 ≤ (Real.sqrt q)⁻¹ ^ 2 * ∑ j, ∑ i,
      (2 : ℝ) ^ (ϖ + ((N j).card - if i ∈ N j then 1 else 0)) := by positivity
  have hE0 : 0 ≤ Real.exp ((Real.sqrt q)⁻¹ ^ 2 * ∑ j, ∑ i,
      (2 : ℝ) ^ (ϖ + ((N j).card - if i ∈ N j then 1 else 0))) - 1 := by
    have := Real.add_one_le_exp ((Real.sqrt q)⁻¹ ^ 2 * ∑ j, ∑ i,
      (2 : ℝ) ^ (ϖ + ((N j).card - if i ∈ N j then 1 else 0)))
    linarith
  have hP0 : 0 ≤ ∏ j, (1 + ePin q n z (ϖ + (N j).card)) :=
    prod_nonneg fun j _ => by linarith [ePin_nonneg q n z (ϖ + (N j).card)]
  refine mul_le_mul (div_le_div_of_nonneg_right hUps (pow_nonneg h1.le _)) (by linarith) hE0
    (div_nonneg (le_trans hP0 hUps) (pow_nonneg h1.le _))

theorem sk_pin_omega_factor_nonneg (D : ℝ) (hD : |D| ≤ 1) (a : F) :
    0 ≤ 1 + D * (quadraticChar F a : ℝ) := by
  have h1 : |(quadraticChar F a : ℝ)| ≤ 1 := by
    rcases eq_or_ne a 0 with h | h
    · rw [h]; simp
    · rcases quadraticChar_dichotomy h with h' | h' <;> rw [h'] <;> norm_num
  have : |D * (quadraticChar F a : ℝ)| ≤ 1 := by
    rw [abs_mul]
    calc |D| * |(quadraticChar F a : ℝ)| ≤ 1 * 1 :=
          mul_le_mul hD h1 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  linarith [neg_abs_le (D * (quadraticChar F a : ℝ))]

theorem sk_pinKer_soft_nonneg {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    (hD : ∀ e, |D e| ≤ 1) (x y : Fin n → F) : 0 ≤ skPinKer ς D x y := by
  unfold skPinKer
  refine mul_nonneg (by split_ifs <;> norm_num) (prod_nonneg fun j _ => prod_nonneg fun i _ => ?_)
  exact sk_pin_omega_factor_nonneg _ (hD (i, j)) _

/-- **Row sums of the soft pinned collision kernel**: `∑_y K^D(x, y) ≤ D_Y |𝓘_pin|`. -/
theorem sk_pin_rowSum_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (D : Fin n × Fin n → ℝ)
    (hD : ∀ e, |D e| ≤ 1) (hneg : ∀ e, D e < 0 → quadraticChar F (-1) = -1)
    (x : Fin n → F) (hx : x ∈ pinLab M pin) :
    ∑ y ∈ pinLab M pin, skPinKer ς D x y ≤
      pinD (Fintype.card F) M.card ϖ (pinNY ς) * (pinLab M pin).card := by
  simp only [sk_pinKer_expand ς D hneg x]
  rw [sum_comm]
  have hw0 : ∀ T ∈ (skPinE ς).powerset, 0 ≤ skW D (skPinE ς) T :=
    fun T _ => skW_nonneg (fun e _ => hD e) T
  calc ∑ T ∈ (skPinE ς).powerset, ∑ y ∈ pinLab M pin,
        skW D (skPinE ς) T * pinKer (skPinSgn ς D T) x y
      = ∑ T ∈ (skPinE ς).powerset, skW D (skPinE ς) T *
          ∑ y ∈ pinLab M pin, pinKer (skPinSgn ς D T) x y :=
        sum_congr rfl fun T _ => (mul_sum _ _ _).symm
    _ ≤ ∑ T ∈ (skPinE ς).powerset, skW D (skPinE ς) T *
          (pinD (Fintype.card F) M.card ϖ (pinNY ς) * (pinLab M pin).card) := by
        refine sum_le_sum fun T hT => mul_le_mul_of_nonneg_left ?_ (hw0 T hT)
        refine (pin_rowSum_le hW M pin hpin hpinM ϖ hϖ he (skPinSgn ς D T)
          (sk_skPinSgn_values hς D T) x hx).trans ?_
        exact mul_le_mul_of_nonneg_right
          (sk_pinD_mono _ _ _ (fun j => sk_pinNY_sgn_subset ς D T j) he) (Nat.cast_nonneg _)
    _ = _ := by rw [← sum_mul, skW_sum, one_mul]

/-- Exchanging the two rows of the soft kernel: `K^D(x, y) = K^{Dᵀ}_{ςᵀ}(y, x)`. -/
theorem sk_pinKer_soft_swap {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    (x y : Fin n → F) :
    skPinKer ς D x y = skPinKer (pinSwap ς) (fun e => D e.swap) y x := by
  unfold skPinKer
  congr 1
  · have : (∃ i j, x i = y j) ↔ (∃ i j, y i = x j) :=
      ⟨fun ⟨i, j, h⟩ => ⟨j, i, h.symm⟩, fun ⟨i, j, h⟩ => ⟨j, i, h.symm⟩⟩
    simp only [this]
  · rw [pinNY_swap]
    unfold pinNY pinNX
    rw [pin_prod_pairs ς (fun i j => 1 + D (i, j) * (quadraticChar F ((ς i j : F) * (y j - x i)) : ℝ))]
    refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
    simp only [pinSwap, Int.cast_neg, Prod.swap_prod_mk]
    congr 3
    ring_nf

/-- **`cor:soft-kernels`(c) for `prop:pinned-collision`**: for coefficients `|D_{ij}| ≤ 1` the soft
pinned collision operator with kernel `1{x([n]) ∩ y([n]) ≠ ∅} ∏_{(i,j) ∈ E_×}(1 + D_{ij} χ_{ij})`
satisfies the bound of `pinned_collision_opBound`, `‖T‖ ≤ (D_X D_Y)^{1/2}`, provided
`χ(-1) = -1` if some `D_{ij} < 0` (no condition when `D ≥ 0`). -/
theorem sk_soft_pinned_collision_opBound (hW : WeilBound F) {n : ℕ} (M : Finset F)
    (pin : Fin n → F → ℤ) (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (D : Fin n × Fin n → ℝ)
    (hD : ∀ e, |D e| ≤ 1) (hneg : ∀ e, D e < 0 → quadraticChar F (-1) = -1) :
    Sarkozy.Influence.OpBound (pinLab M pin) (pinLab M pin)
      (fun x y => skPinKer ς D x y / (pinLab M pin).card)
      (Real.sqrt (pinD (Fintype.card F) M.card ϖ (pinNX ς) *
        pinD (Fintype.card F) M.card ϖ (pinNY ς))) := by
  set N : ℝ := ((pinLab M pin).card : ℝ)
  have hD0 := pinD_nonneg (Fintype.card F) M.card ϖ (pinNY ς) he
  have hD0' := pinD_nonneg (Fintype.card F) M.card ϖ (pinNX ς) he
  have hrow : ∀ x ∈ pinLab M pin, ∑ y ∈ pinLab M pin, skPinKer ς D x y / N ≤
      pinD (Fintype.card F) M.card ϖ (pinNY ς) := by
    intro x hx
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (card_pos.mpr ⟨x, hx⟩)
    rw [← sum_div, div_le_iff₀ hN]
    exact sk_pin_rowSum_le hW M pin hpin hpinM ϖ hϖ he ς hς D hD hneg x hx
  have hcol : ∀ y ∈ pinLab M pin, ∑ x ∈ pinLab M pin, skPinKer ς D x y / N ≤
      pinD (Fintype.card F) M.card ϖ (pinNX ς) := by
    intro y hy
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (card_pos.mpr ⟨y, hy⟩)
    rw [← sum_div, div_le_iff₀ hN]
    have h := sk_pin_rowSum_le hW M pin hpin hpinM ϖ hϖ he (pinSwap ς) (pinSwap_signs hς)
      (fun e => D e.swap) (fun e => hD e.swap) (fun e he' => hneg e.swap he') y hy
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

end SkPin

end Sarkozy.ExtractionK
