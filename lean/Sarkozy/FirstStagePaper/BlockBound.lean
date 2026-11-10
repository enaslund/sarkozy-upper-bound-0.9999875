module

public import Sarkozy.FirstStagePaper.TensorDiff
public import Sarkozy.PartVRecords.OneStageDelta
public import Sarkozy.PartVRecords.OneStageBlock

@[expose] public section

/-!
# `lem:record:one-stage-folded-e`(d): the block bound `‖Δ_c‖ ≤ k_new(X) b^{-1/2}`

`paper/sections/20c_middle_frame.tex`, `lem:record:one-stage-folded-e`(d), first bound. V3 proved
(a)–(c) at one prime (`Sarkozy.PartVRecords.OneStage*`), on functions `F → ℝ` vanishing at the
shared label `c`. Here:

* **One prime, on `V_c`.** `Vc c = {a // a ≠ c}`; the matrices `KpMat c` (`𝒦₊^{(c)}`) and `K0Mat c`
  (`𝒦₀^{(c)} = (J - I)/(p - 2)`) on `V_c` are doubly stochastic (`KpMat_mul_mean`, …), and on the
  mean-zero functions of `V_c`: `‖𝒦₊ f‖ ≤ (√p + 3)/(p - 3) ‖f‖` (V3's `Kop_norm_sq_le`),
  `‖𝒦₀ f‖ = ‖f‖/(p - 2)`, `‖(𝒦₊ - 𝒦₀) f‖ ≤ κ_Δ(p) ‖f‖ = k_new(p) p^{-1/2} ‖f‖`
  (V3's `Dop_norm_sq_le`,
  `kappaDelta_eq_knew`).
* **The constants.** `knew` is nondecreasing in `q, r` (`knew_mono`) and at least one
  (`one_le_knew`), so `k_new(p) p^{-1/2} ≤ k_new(X) b^{-1/2}` for `p ≥ b ≥ X`; and
  `α_p ≤ 2 b^{-1/2}`, `β_p ≤ 2/b`, so
  `α_p α_{p'} + β_p β_{p'} ≤ 4/b + 4/b² ≤ b^{-1/2} ≤ k_new(X) b^{-1/2}`
  for `b ≥ 2^{24}` (the paper's two-support gate `α_X² r_X + β_X² q_X r_X < k_new(X)` in a cruder,
  sufficient form; `pair_le_knew`).
* **The block** (`block_delta_norm_le`, **`block_delta_form_le`**): for a block of class-three
  primes `p ≥ b ≥ X ≥ 2^{24}` and every shared label `c = (c_p)_p`, the difference
  `Δ_c = ⊗_p 𝒦₊^{(c_p)} - ⊗_p 𝒦₀^{(c_p)}` on `∏_p V_{c_p}` satisfies `‖Δ_c‖ ≤ k_new(X) b^{-1/2}`,
  in operator form and as a bound of the bilinear form. This is the first bound of (d); the bound
  `‖Sym Δ_c‖ ≤ s_fold(X)/b` of the symmetric part is not formalized (it is not used by (CP2)).

The norms are Euclidean on `∏_p V_{c_p}`; they are those of `L²` of the uniform law of `∏_p V_{c_p}`
up to the common factor `∏_p (p - 1)`, which cancels in an operator norm.
-/

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.FirstStagePaper

open Sarkozy.IndexSupport Sarkozy.PartVRecords Sarkozy.PartV

/-! ## One prime, on `V_c` -/

section Generic

variable {F : Type*} [Fintype F] [DecidableEq F]

/-- `V_c = F ∖ {c}`. -/
abbrev Vc (c : F) : Type _ := {a : F // a ≠ c}

/-- Extension by zero from `V_c` to `F`. -/
noncomputable def extV (c : F) (f : Vc c → ℝ) (a : F) : ℝ := if h : a = c then 0 else f ⟨a, h⟩

theorem sum_Vc (c : F) (ψ : F → ℝ) (hψ : ψ c = 0) : ∑ a, ψ a = ∑ y : Vc c, ψ y.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a => a ≠ c) ψ]
  have h0 : ∑ i : {x // ¬ x ≠ c}, ψ i = 0 := by
    refine sum_eq_zero fun i _ => ?_
    have hi : i.1 = c := not_not.mp i.2
    rw [hi, hψ]
  rw [h0, add_zero]

omit [Fintype F] in
theorem extV_val (c : F) (f : Vc c → ℝ) (y : Vc c) : extV c f y.1 = f y := by
  have hy : ¬ (y.1 = c) := y.2
  simp only [extV, hy, ↓reduceDIte]

omit [Fintype F] in
theorem extV_c (c : F) (f : Vc c → ℝ) : extV c f c = 0 := by
  simp only [extV, ↓reduceDIte]

theorem sum_extV (c : F) (f : Vc c → ℝ) : ∑ a, extV c f a = ∑ y, f y := by
  rw [sum_Vc c _ (extV_c c f)]
  exact sum_congr rfl fun y _ => extV_val c f y

theorem sum_extV_sq (c : F) (f : Vc c → ℝ) : ∑ a, extV c f a ^ 2 = ∑ y, f y ^ 2 := by
  rw [sum_Vc c (fun a => extV c f a ^ 2) (by simp only [extV_c]; norm_num)]
  exact sum_congr rfl fun y _ => by rw [extV_val]

theorem card_Vc (c : F) : (Fintype.card (Vc c) : ℝ) = (Fintype.card F : ℝ) - 1 := by
  rw [Fintype.card_subtype, filter_ne' univ c, card_erase_of_mem (mem_univ _), card_univ]
  have h1 : 1 ≤ Fintype.card F := Fintype.card_pos_iff.mpr ⟨c⟩
  push_cast [Nat.cast_sub h1]
  ring

theorem dotProduct_self_eq {c : F} (f : Vc c → ℝ) : f ⬝ᵥ f = ∑ y, f y ^ 2 := by
  simp only [dotProduct, sq]

/-- `𝒦₀^{(c)} = (J - I)/(q - 2)` on `V_c`: the conditional coupling of the replaced record. -/
noncomputable def K0Mat (c : F) : Matrix (Vc c) (Vc c) ℝ :=
  fun a a' => if a = a' then 0 else ((Fintype.card F : ℝ) - 2)⁻¹

theorem K0Mat_symm (c : F) (x y : Vc c) : K0Mat c x y = K0Mat c y x := by
  simp only [K0Mat, eq_comm]

theorem K0Mat_row_sum (c : F) (hq : (3 : ℝ) ≤ Fintype.card F) (x : Vc c) :
    ∑ y, K0Mat c x y = 1 := by
  simp only [K0Mat]
  rw [Finset.sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
  have hcard : ((univ.filter fun y : Vc c => ¬ x = y).card : ℝ) = (Fintype.card F : ℝ) - 2 := by
    rw [show (univ.filter fun y : Vc c => ¬ x = y) = univ.filter (fun y => x ≠ y) from rfl,
      filter_ne univ x, card_erase_of_mem (mem_univ x), card_univ]
    have h2 : 1 ≤ Fintype.card (Vc c) := Fintype.card_pos_iff.mpr ⟨x⟩
    push_cast [Nat.cast_sub h2]
    rw [card_Vc]
    ring
  rw [hcard]
  have : (Fintype.card F : ℝ) - 2 ≠ 0 := by linarith
  field_simp

theorem K0Mat_mul_mean (c : F) (hq : (3 : ℝ) ≤ Fintype.card F) :
    K0Mat c * meanMatrix (Vc c) = meanMatrix (Vc c) := by
  ext x z
  simp only [Matrix.mul_apply, meanMatrix_apply, ← sum_mul, K0Mat_row_sum c hq, one_mul]

theorem mean_mul_K0Mat (c : F) (hq : (3 : ℝ) ≤ Fintype.card F) :
    meanMatrix (Vc c) * K0Mat c = meanMatrix (Vc c) := by
  ext x z
  simp only [Matrix.mul_apply, meanMatrix_apply, ← mul_sum]
  rw [show ∑ y, K0Mat c y z = ∑ y, K0Mat c z y from sum_congr rfl fun y _ => K0Mat_symm c y z,
    K0Mat_row_sum c hq, mul_one]

/-- `𝒦₀ f = -f/(q - 2)` on the mean-zero functions of `V_c`, so `‖𝒦₀ f‖ = ‖f‖/(q - 2)`. -/
theorem K0Mat_norm_sq_le (c : F) (f : Vc c → ℝ) (hf : ∑ y, f y = 0) :
    (K0Mat c *ᵥ f) ⬝ᵥ (K0Mat c *ᵥ f) ≤ (1 / ((Fintype.card F : ℝ) - 2)) ^ 2 * (f ⬝ᵥ f) := by
  have hval : ∀ x, (K0Mat c *ᵥ f) x = -f x / ((Fintype.card F : ℝ) - 2) := by
    intro x
    simp only [Matrix.mulVec, dotProduct, K0Mat, ite_mul, zero_mul]
    rw [Finset.sum_ite, sum_const_zero, zero_add, ← mul_sum]
    have hs : ∑ y ∈ univ.filter (fun y => ¬ x = y), f y = -f x := by
      have := Finset.sum_filter_add_sum_filter_not univ (fun y => x = y) f
      rw [hf, Finset.filter_eq univ x] at this
      simp only [mem_univ, ↓reduceIte, sum_singleton] at this
      linarith
    rw [hs]
    ring
  rw [dotProduct_self_eq, dotProduct_self_eq]
  simp only [hval, div_pow, neg_sq, ← sum_div, one_div, inv_pow]
  rw [div_eq_inv_mul]

end Generic

section OnePrime

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

instance (c : F) : Nonempty (Vc c) := ⟨⟨c + 1, fun h => one_ne_zero (add_eq_left.mp h)⟩⟩

/-- `𝒦₊^{(c)}` on `V_c` (`lem:record:one-stage-folded-e`(b)). -/
noncomputable def KpMat (c : F) : Matrix (Vc c) (Vc c) ℝ := fun a a' => Kplus c a.1 a'.1

theorem KpMat_mulVec (c : F) (f : Vc c → ℝ) (x : Vc c) :
    (KpMat c *ᵥ f) x = Kop c (extV c f) x.1 := by
  simp only [Matrix.mulVec, dotProduct, KpMat, Kop]
  rw [sum_Vc c (fun a => Kplus c x.1 a * extV c f a) (by simp only [extV_c, mul_zero])]
  exact sum_congr rfl fun y _ => by rw [extV_val]

omit [Field F] in
theorem K0Mat_mulVec (c : F) (f : Vc c → ℝ) (x : Vc c) :
    (K0Mat c *ᵥ f) x = K0op c (extV c f) x.1 := by
  have hx : ¬ (x.1 = c) := x.2
  simp only [Matrix.mulVec, dotProduct, K0Mat, K0op, hx, ↓reduceIte, sum_div]
  rw [sum_Vc c (fun a => (if a = c ∨ a = x.1 then 0 else extV c f a) / ((Fintype.card F : ℝ) - 2))
    (by simp)]
  refine sum_congr rfl fun y _ => ?_
  by_cases hxy : x = y
  · subst hxy
    simp
  · have h1 : ¬ (y.1 = c ∨ y.1 = x.1) := by
      rintro (h | h)
      · exact y.2 h
      · exact hxy (Subtype.ext h.symm)
    simp only [hxy, h1, ↓reduceIte, extV_val]
    ring

variable (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
include hF h3 hk

theorem KpMat_mul_mean (c : F) : KpMat c * meanMatrix (Vc c) = meanMatrix (Vc c) := by
  ext x z
  simp only [Matrix.mul_apply, meanMatrix_apply, KpMat, ← sum_mul]
  rw [← sum_Vc c (fun a => Kplus c x.1 a) Kplus_right_eq, Kplus_row_sum hF h3 hk x.2, one_mul]

theorem mean_mul_KpMat (c : F) : meanMatrix (Vc c) * KpMat c = meanMatrix (Vc c) := by
  ext x z
  simp only [Matrix.mul_apply, meanMatrix_apply, KpMat, ← mul_sum]
  rw [← sum_Vc c (fun a => Kplus c a z.1) Kplus_left_eq, Kplus_col_sum hF h3 hk z.2, mul_one]

/-- `‖𝒦₊ f‖ ≤ κ^{fold}_p ‖f‖` on the mean-zero functions of `V_c` (V3's `Kop_norm_sq_le`). -/
theorem KpMat_norm_sq_le (c : F) (f : Vc c → ℝ) (hf : ∑ y, f y = 0) :
    (KpMat c *ᵥ f) ⬝ᵥ (KpMat c *ᵥ f) ≤
      ((Real.sqrt (Fintype.card F : ℝ) + 3) / ((Fintype.card F : ℝ) - 3)) ^ 2 * (f ⬝ᵥ f) := by
  rw [dotProduct_self_eq, dotProduct_self_eq]
  have h := Kop_norm_sq_le hF h3 hk c (f := extV c f) (extV_c c f) (by rw [sum_extV, hf])
  rw [sum_Vc c (fun a => Kop c (extV c f) a ^ 2) (by simp only [Kop_c]; norm_num),
    sum_extV_sq] at h
  simpa only [KpMat_mulVec] using h

/-- `‖(𝒦₊ - 𝒦₀) f‖ ≤ κ_Δ(p) ‖f‖` on the mean-zero functions of `V_c` (V3's `Dop_norm_sq_le`). -/
theorem DMat_norm_sq_le (c : F) (f : Vc c → ℝ) (hf : ∑ y, f y = 0) :
    ((KpMat c - K0Mat c) *ᵥ f) ⬝ᵥ ((KpMat c - K0Mat c) *ᵥ f) ≤
      kappaDelta (Fintype.card F : ℝ) ^ 2 * (f ⬝ᵥ f) := by
  rw [dotProduct_self_eq, dotProduct_self_eq]
  have h := Dop_norm_sq_le hF h3 hk c (f := extV c f) (extV_c c f) (by rw [sum_extV, hf])
  rw [sum_Vc c (fun a => Dop c (extV c f) a ^ 2) (by simp only [Dop_c]; norm_num),
    sum_extV_sq] at h
  have e : ∀ y : Vc c, ((KpMat c - K0Mat c) *ᵥ f) y = Dop c (extV c f) y.1 := by
    intro y
    rw [Matrix.sub_mulVec, Pi.sub_apply, KpMat_mulVec, K0Mat_mulVec]
    rfl
  simpa only [e] using h

end OnePrime

/-! ## The constants -/

section Constants

/-- **`k_new` is nondecreasing in `q` and `r`** (proof of `lem:record:one-stage-folded-e`(d):
its first term is `(1 + 4q/(1 + q))/(1 - 3q)`). -/
theorem knew_mono {q₁ q₂ r₁ r₂ : ℝ} (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (hq₂ : q₂ ≤ 1 / 10)
    (hr₁ : 0 ≤ r₁) (hr : r₁ ≤ r₂) : knew q₁ r₁ ≤ knew q₂ r₂ := by
  unfold knew
  have hq₂0 : 0 ≤ q₂ := le_trans hq₁ hq
  apply add_le_add
  · exact div_le_div₀ (by linarith) (by linarith) (by nlinarith) (by nlinarith)
  · exact div_le_div₀ (mul_nonneg hq₂0 (le_trans hr₁ hr)) (mul_le_mul hq hr hr₁ hq₂0)
      (by nlinarith) (by nlinarith)

/-- `k_new ≥ 1`. -/
theorem one_le_knew {q r : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 10) (hr : 0 ≤ r) : 1 ≤ knew q r := by
  unfold knew
  have h1 : 1 ≤ (1 + 5 * q) / ((1 - 3 * q) * (1 + q)) := by
    rw [le_div_iff₀ (by nlinarith)]
    nlinarith
  have h2 : 0 ≤ q * r / ((1 - 3 * q) * (1 - 2 * q)) :=
    div_nonneg (mul_nonneg hq hr) (by nlinarith)
  linarith

/-- **The block constant** `k_new(X) b^{-1/2}` of `lem:record:one-stage-folded-e`(d). -/
noncomputable def blockConst (X b : ℝ) : ℝ := knew (1 / X) (1 / Real.sqrt X) * (1 / Real.sqrt b)

section Prime

variable {X b p : ℝ} (hX : 2 ^ 24 ≤ X) (hXb : X ≤ b) (hbp : b ≤ p)
include hX hXb hbp

theorem sqrt_ge_of_block : (2 : ℝ) ^ 12 ≤ Real.sqrt b ∧ Real.sqrt b ≤ Real.sqrt p := by
  refine ⟨?_, Real.sqrt_le_sqrt hbp⟩
  rw [show (2 : ℝ) ^ 12 = Real.sqrt ((2 ^ 12) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- `κ_Δ(p) = k_new(p) p^{-1/2} ≤ k_new(X) b^{-1/2}` for `p ≥ b ≥ X`. -/
theorem kappaDelta_le_blockConst : kappaDelta p ≤ blockConst X b := by
  have hX0 : 0 < X := by linarith
  have hp3 : 3 < p := by linarith
  rw [kappaDelta_eq_knew hp3, blockConst]
  obtain ⟨hsb, hsbp⟩ := sqrt_ge_of_block hX hXb hbp
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hsXp : Real.sqrt X ≤ Real.sqrt p := Real.sqrt_le_sqrt (le_trans hXb hbp)
  have hk1 : knew (1 / p) (1 / Real.sqrt p) ≤ knew (1 / X) (1 / Real.sqrt X) :=
    knew_mono (by positivity) (one_div_le_one_div_of_le hX0 (le_trans hXb hbp))
      (by rw [div_le_div_iff₀ hX0 (by norm_num)]; linarith) (by positivity)
      (one_div_le_one_div_of_le hsX hsXp)
  have hk0 : 0 ≤ knew (1 / X) (1 / Real.sqrt X) :=
    le_trans zero_le_one (one_le_knew (by positivity)
      (by rw [div_le_div_iff₀ hX0 (by norm_num)]; linarith) (by positivity))
  have hr : 1 / Real.sqrt p ≤ 1 / Real.sqrt b :=
    one_div_le_one_div_of_le (by linarith) hsbp
  calc knew (1 / p) (1 / Real.sqrt p) * (1 / Real.sqrt p)
      ≤ knew (1 / X) (1 / Real.sqrt X) * (1 / Real.sqrt p) :=
        mul_le_mul_of_nonneg_right hk1 (by positivity)
    _ ≤ knew (1 / X) (1 / Real.sqrt X) * (1 / Real.sqrt b) := mul_le_mul_of_nonneg_left hr hk0

theorem kappaDelta_nonneg : 0 ≤ kappaDelta p := by
  have hp3 : 3 < p := by linarith
  rw [kappaDelta_eq_knew hp3]
  have hp0 : 0 < p := by linarith
  have hq : 1 / p ≤ 1 / 10 := by rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
  exact mul_nonneg (le_trans zero_le_one (one_le_knew (by positivity) hq (by positivity)))
    (by positivity)

/-- `κ^{fold}_p = (√p + 3)/(p - 3) ≤ 2 b^{-1/2}`, and it lies in `[0, 1]`. -/
theorem kfold_bounds : 0 ≤ (Real.sqrt p + 3) / (p - 3) ∧ (Real.sqrt p + 3) / (p - 3) ≤ 1 ∧
    (Real.sqrt p + 3) / (p - 3) ≤ 2 / Real.sqrt b := by
  obtain ⟨hsb, hsbp⟩ := sqrt_ge_of_block hX hXb hbp
  have hp0 : 0 ≤ p := by linarith
  have hs2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0
  have hs : (2 : ℝ) ^ 12 ≤ Real.sqrt p := le_trans hsb hsbp
  have hp3 : 0 < p - 3 := by nlinarith
  have h2 : (Real.sqrt p + 3) / (p - 3) ≤ 2 / Real.sqrt p := by
    rw [div_le_div_iff₀ hp3 (by linarith)]
    nlinarith
  have h3 : 2 / Real.sqrt p ≤ 2 / Real.sqrt b :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) hsbp
  refine ⟨div_nonneg (by positivity) hp3.le, ?_, le_trans h2 h3⟩
  refine le_trans h2 ?_
  rw [div_le_one (by linarith)]
  linarith

/-- `1/(p - 2) ≤ 2/b`, and it lies in `[0, 1]`. -/
theorem k0_bounds : 0 ≤ 1 / (p - 2) ∧ 1 / (p - 2) ≤ 1 ∧ 1 / (p - 2) ≤ 2 / b := by
  have hp : 4 ≤ p := by linarith
  have hb0 : 0 < b := by linarith
  refine ⟨div_nonneg zero_le_one (by linarith), ?_, ?_⟩
  · rw [div_le_one (by linarith)]
    linarith
  · rw [div_le_div_iff₀ (by linarith) hb0]
    linarith

end Prime

/-- **The two-support gate** in the form used: `4/b + 4/b² ≤ k_new(X) b^{-1/2}` for `b ≥ X ≥ 2^{24}`
(the paper's gate `α_X² r_X + β_X² q_X r_X < k_new(X)` holds a fortiori;
`cert:record:one-stage`). -/
theorem pair_le_blockConst {X b : ℝ} (hX : 2 ^ 24 ≤ X) (hXb : X ≤ b) :
    (2 / Real.sqrt b) ^ 2 + (2 / b) ^ 2 ≤ blockConst X b := by
  have hX0 : 0 < X := by linarith
  obtain ⟨hsb, -⟩ := sqrt_ge_of_block hX hXb (le_refl b)
  have hb0 : 0 ≤ b := by linarith
  have ht2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0
  set t := Real.sqrt b with ht
  have ht0 : 0 < t := by linarith
  have hk : 1 ≤ knew (1 / X) (1 / Real.sqrt X) :=
    one_le_knew (by positivity) (by rw [div_le_div_iff₀ hX0 (by norm_num)]; linarith)
      (by positivity)
  have hmain : (2 / t) ^ 2 + (2 / b) ^ 2 ≤ 1 / t := by
    have e1 : (2 / t) ^ 2 = 4 / t ^ 2 := by rw [div_pow]; norm_num
    have e2 : (2 / b) ^ 2 = 4 / t ^ 4 := by rw [← ht2, div_pow, ← pow_mul]; norm_num
    have h1 : 4 / t ^ 2 ≤ 1 / (2 * t) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : 4 / t ^ 4 ≤ 1 / (2 * t) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos ht0 3, pow_pos ht0 2]
    have e3 : 1 / (2 * t) + 1 / (2 * t) = 1 / t := by field_simp; ring
    rw [e1, e2, ← e3]
    exact add_le_add h1 h2
  unfold blockConst
  calc (2 / t) ^ 2 + (2 / b) ^ 2 ≤ 1 / t := hmain
    _ = 1 * (1 / t) := (one_mul _).symm
    _ ≤ knew (1 / X) (1 / Real.sqrt X) * (1 / t) :=
        mul_le_mul_of_nonneg_right hk (by positivity)

end Constants

/-! ## The block -/

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- `⊗_p 𝒦₊^{(c_p)}` on `∏_p V_{c_p}`, for the shared label `c = (c_p)_p` of a block. -/
noncomputable def blockKp (c : BlockLabel pr) : Matrix (∀ i, Vc (c i)) (∀ i, Vc (c i)) ℝ :=
  piKron (fun i => KpMat (c i))

/-- `⊗_p 𝒦₀^{(c_p)}` on `∏_p V_{c_p}`. -/
noncomputable def blockK0 (c : BlockLabel pr) : Matrix (∀ i, Vc (c i)) (∀ i, Vc (c i)) ℝ :=
  piKron (fun i => K0Mat (c i))

/-- **`lem:record:one-stage-folded-e`(d), first bound: `‖Δ_c‖ ≤ k_new(X) b^{-1/2}`.** For a block of
class-three primes `p ≥ b ≥ X ≥ 2^{24}` and every shared label `c = (c_p)_p`, the difference
`Δ_c = ⊗_p 𝒦₊^{(c_p)} - ⊗_p 𝒦₀^{(c_p)}` satisfies `‖Δ_c f‖ ≤ k_new(X) b^{-1/2} ‖f‖` on all of
`ℝ^{∏_p V_{c_p}}`. -/
theorem block_delta_norm_le (h : ClassThreeBlock pr) {X b : ℝ} (hX : 2 ^ 24 ≤ X) (hXb : X ≤ b)
    (hbp : ∀ i, b ≤ (pr i : ℝ)) (c : BlockLabel pr) (f : (∀ i, Vc (c i)) → ℝ) :
    ((blockKp pr c - blockK0 pr c) *ᵥ f) ⬝ᵥ ((blockKp pr c - blockK0 pr c) *ᵥ f) ≤
      blockConst X b ^ 2 * (f ⬝ᵥ f) := by
  have hcard : ∀ i, (Fintype.card (ZMod (pr i)) : ℝ) = pr i := fun i => by rw [ZMod.card]
  have hq3 : ∀ i, (3 : ℝ) ≤ Fintype.card (ZMod (pr i)) := fun i => card_three_le (h.card_mod i)
  have hbp' : ∀ i, b ≤ (Fintype.card (ZMod (pr i)) : ℝ) := fun i => by rw [hcard]; exact hbp i
  exact tensor_diff_norm_le (fun i => KpMat (c i)) (fun i => K0Mat (c i))
    (fun i => KpMat_mul_mean (h.ringChar_ne i) (h.card_mod i) (h.kP_pos' i) (c i))
    (fun i => mean_mul_KpMat (h.ringChar_ne i) (h.card_mod i) (h.kP_pos' i) (c i))
    (fun i => K0Mat_mul_mean (c i) (hq3 i)) (fun i => mean_mul_K0Mat (c i) (hq3 i))
    (α := fun i => (Real.sqrt (Fintype.card (ZMod (pr i)) : ℝ) + 3) /
      ((Fintype.card (ZMod (pr i)) : ℝ) - 3))
    (β := fun i => 1 / ((Fintype.card (ZMod (pr i)) : ℝ) - 2))
    (δ := fun i => kappaDelta (Fintype.card (ZMod (pr i)) : ℝ))
    (fun i => (kfold_bounds hX hXb (hbp' i)).1) (fun i => (kfold_bounds hX hXb (hbp' i)).2.1)
    (fun i => (k0_bounds hX hXb (hbp' i)).1) (fun i => (k0_bounds hX hXb (hbp' i)).2.1)
    (fun i => kappaDelta_nonneg hX hXb (hbp' i))
    (fun i f hf => KpMat_norm_sq_le (h.ringChar_ne i) (h.card_mod i) (h.kP_pos' i) (c i) f hf)
    (fun i f hf => K0Mat_norm_sq_le (c i) f hf)
    (fun i f hf => DMat_norm_sq_le (h.ringChar_ne i) (h.card_mod i) (h.kP_pos' i) (c i) f hf)
    (fun i => kappaDelta_le_blockConst hX hXb (hbp' i))
    (fun i j _ => by
      obtain ⟨ha0, -, ha⟩ := kfold_bounds hX hXb (hbp' i)
      obtain ⟨ha0', -, ha'⟩ := kfold_bounds hX hXb (hbp' j)
      obtain ⟨hb0, -, hb⟩ := k0_bounds hX hXb (hbp' i)
      obtain ⟨hb0', -, hb'⟩ := k0_bounds hX hXb (hbp' j)
      have h2 : (0 : ℝ) ≤ 2 / Real.sqrt b := by positivity
      have h2' : (0 : ℝ) ≤ 2 / b := by
        have : (0 : ℝ) < b := by linarith
        positivity
      refine le_trans ?_ (pair_le_blockConst hX hXb)
      rw [sq, sq]
      exact add_le_add (mul_le_mul ha ha' ha0' h2) (mul_le_mul hb hb' hb0' h2'))
    f

/-- **`lem:record:one-stage-folded-e`(d), as a bound of the bilinear form**:
`|⟨g, Δ_c f⟩| ≤ k_new(X) b^{-1/2} ‖g‖ ‖f‖` on `ℝ^{∏_p V_{c_p}}`. -/
theorem block_delta_form_le (h : ClassThreeBlock pr) {X b : ℝ} (hX : 2 ^ 24 ≤ X) (hXb : X ≤ b)
    (hbp : ∀ i, b ≤ (pr i : ℝ)) (c : BlockLabel pr) (g f : (∀ i, Vc (c i)) → ℝ) :
    |g ⬝ᵥ ((blockKp pr c - blockK0 pr c) *ᵥ f)| ≤
      blockConst X b * Real.sqrt (g ⬝ᵥ g) * Real.sqrt (f ⬝ᵥ f) := by
  have hD : 0 ≤ blockConst X b := by
    have hX0 : 0 < X := by linarith
    unfold blockConst
    exact mul_nonneg (le_trans zero_le_one (one_le_knew (by positivity)
      (by rw [div_le_div_iff₀ hX0 (by norm_num)]; linarith) (by positivity))) (by positivity)
  exact tensor_diff_form_le _ _ hD (block_delta_norm_le pr h hX hXb hbp c) g f

end Block

end Sarkozy.FirstStagePaper
