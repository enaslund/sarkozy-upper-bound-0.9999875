module

public import Sarkozy.SecondOrder.OrderedStar
public import Sarkozy.SecondOrder.StarTrace

/-!
# Weighted star marginals: the second-moment bounds (`lem:wt:stars`(a), Weil and conditional)

`paper/sections/15_second_order.tex`, `lem:wt:stars`. For a support `T` and a vertex `i ∈ T`, on
injective labellings `w_T(x) = 𝒢(x_i)` with `𝒢(ξ) = p⁻¹ ∑_y χ(f(y)(y - ξ))`, where
`f = ∏_{l ∈ T∖{i}} (X - x_l)` (`kernelG`, `starW_eq_kernelG`).

* `sum_kernelG_sq_le`: `∑_ξ 𝒢(ξ)² ≤ 1`, by `eq:two-root` (`sum_chi_mul_chi`);
  `abs_kernelG_le`: `|𝒢(ξ)| ≤ s r` for `s = |T| - 1 ≥ 2`, from Weil.
* `abs_starW_le`: the *Weil* bound of (a), `|w_T| ≤ (|T| - 1) r` on injective labellings, so
  `E_μ w_T² ≤ (|T| - 1)² q` (`wt_second_weil`).
* `wt_cond_second`, `wt_second_cond`: the *conditional* bound of (a). For a pinned half law
  (`def:pinned-law`), `E_μ[w_T² | x_{-i}] ≤ |Φ_i|⁻¹ ∑_ξ 𝒢(ξ)² ≤ q 2^{d_i}/(1 - e_i)`, hence
  `E_μ w_T² ≤ q 2^{d_i}/(1 - e_i)` for every `i ∈ T`.

The conditional mean (b), the cross terms (c) and the norm consequence are in
`WeightedStarsMean.lean`. The *density* bound `2^{e(T)} R_U q` of (a) is not formalized: it needs
`lem:graphs:vertex`(c).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SecondOrder

open Sarkozy.Target Sarkozy.Labellings

variable {p : ℕ} [hp : Fact p.Prime]

/-- `𝒢_R(ξ) = p⁻¹ ∑_y χ(f_R(y)(y - ξ))`, with `f_R = ∏_{a∈R}(X - a)`. -/
noncomputable def kernelG (p : ℕ) [Fact p.Prime] (R : Finset (ZMod p)) (ξ : ZMod p) : ℝ :=
  (1 / (p : ℝ)) * ((∑ y, quadraticChar (ZMod p) ((∏ a ∈ R, (y - a)) * (y - ξ)) : ℤ) : ℝ)

theorem kernelSum_eq_of_not_mem (S : Finset (ZMod p)) {ξ : ZMod p} (hξ : ξ ∉ S) :
    (∑ y, quadraticChar (ZMod p) ((∏ a ∈ S, (y - a)) * (y - ξ)) : ℤ) =
      rootSum (insert ξ S) := by
  unfold rootSum
  refine sum_congr rfl fun y _ => ?_
  rw [prod_insert hξ, mul_comm]

/-- `|𝒢_R(ξ)| ≤ |R| r` for `|R| ≥ 2`, from Weil (`lem:wt:stars`, proof of (b)). -/
theorem abs_kernelG_le (hW : Target.Weil) (hp2 : p ≠ 2) (R : Finset (ZMod p)) (hR : 2 ≤ R.card)
    (ξ : ZMod p) : |kernelG p R ξ| ≤ R.card * (1 / Real.sqrt p) := by
  have hWB := weilBound_of_target hW p hp2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hsq1 : 1 ≤ Real.sqrt p := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hp1
  have hmain : |((∑ y, quadraticChar (ZMod p) ((∏ a ∈ R, (y - a)) * (y - ξ)) : ℤ) : ℝ)| ≤
      R.card * Real.sqrt p := by
    by_cases hξ : ξ ∈ R
    · rw [kernelSum_eq_of_mem R hξ]
      have hcard : (R.erase ξ).card = R.card - 1 := card_erase_of_mem hξ
      have hne : (R.erase ξ).Nonempty := card_pos.mp (by omega)
      have hb := hWB (R.erase ξ) hne
      rw [hcard, ZMod.card, Nat.cast_sub (by omega : 1 ≤ R.card), Nat.cast_one] at hb
      have hchi : |((quadraticChar (ZMod p) (∏ a ∈ R.erase ξ, (ξ - a)) : ℤ) : ℝ)| ≤ 1 := by
        rcases quadraticChar_isQuadratic (ZMod p) (∏ a ∈ R.erase ξ, (ξ - a)) with h | h | h <;>
          rw [h] <;> norm_num
      push_cast
      have h1 := abs_le.mp hb
      have h2 := abs_le.mp hchi
      rw [abs_le]
      constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, hsq1]
    · rw [kernelSum_eq_of_not_mem R hξ]
      have hb := hWB (insert ξ R) (insert_nonempty ξ R)
      rw [card_insert_of_notMem hξ, ZMod.card] at hb
      push_cast at hb
      linarith
  unfold kernelG
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / p)]
  calc 1 / (p : ℝ) * |((∑ y, quadraticChar (ZMod p) ((∏ a ∈ R, (y - a)) * (y - ξ)) : ℤ) : ℝ)|
      ≤ 1 / (p : ℝ) * (R.card * Real.sqrt p) := mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = R.card * (1 / Real.sqrt p) := by
        rw [show 1 / (p : ℝ) * (R.card * Real.sqrt p) = R.card * (Real.sqrt p / p) by ring,
          Real.sqrt_div_self']

/-- `∑_ξ χ(y - ξ) χ(y' - ξ) = p [y = y'] - 1` (`eq:two-root`). -/
theorem sum_chi_mul_chi (hp2 : p ≠ 2) (y y' : ZMod p) :
    ∑ ξ, ((quadraticChar (ZMod p) (y - ξ) : ℤ) : ℝ) * ((quadraticChar (ZMod p) (y' - ξ) : ℤ) : ℝ) =
      (p : ℝ) * (if y = y' then 1 else 0) - 1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  by_cases h : y = y'
  · subst h
    simp only [↓reduceIte, mul_one]
    have e : ∀ ξ, ((quadraticChar (ZMod p) (y - ξ) : ℤ) : ℝ) *
        ((quadraticChar (ZMod p) (y - ξ) : ℤ) : ℝ) = 1 - (if ξ = y then 1 else 0) := by
      intro ξ
      by_cases hξ : ξ = y
      · subst hξ; simp
      · have hne : y - ξ ≠ 0 := sub_ne_zero.mpr (Ne.symm hξ)
        simp only [hξ, ↓reduceIte, sub_zero]
        rw [← Int.cast_mul, ← map_mul, ← sq, quadraticChar_sq_one' hne, Int.cast_one]
    rw [sum_congr rfl fun ξ _ => e ξ, sum_sub_distrib, sum_ite_eq']
    simp [ZMod.card]
  · simp only [h, ↓reduceIte, mul_zero, zero_sub]
    have h2 := two_root hF h
    unfold rootSum at h2
    have e : ∀ ξ, ((quadraticChar (ZMod p) (y - ξ) : ℤ) : ℝ) *
        ((quadraticChar (ZMod p) (y' - ξ) : ℤ) : ℝ) =
        ((quadraticChar (ZMod p) (∏ a ∈ ({y, y'} : Finset (ZMod p)), (ξ - a)) : ℤ) : ℝ) := by
      intro ξ
      rw [prod_pair h, ← Int.cast_mul, ← map_mul]
      congr 2
      ring
    rw [sum_congr rfl fun ξ _ => e ξ, ← Int.cast_sum, h2]
    simp

/-- `∑_ξ 𝒢_R(ξ)² ≤ 1` (`lem:wt:stars`, the conditional bound of (a)). -/
theorem sum_kernelG_sq_le (hp2 : p ≠ 2) (R : Finset (ZMod p)) : ∑ ξ, kernelG p R ξ ^ 2 ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  set a : ZMod p → ℝ := fun y => ((quadraticChar (ZMod p) (∏ b ∈ R, (y - b)) : ℤ) : ℝ) with ha
  set c : ZMod p → ZMod p → ℝ := fun y ξ => ((quadraticChar (ZMod p) (y - ξ) : ℤ) : ℝ) with hc
  have hG : ∀ ξ, kernelG p R ξ = (1 / (p : ℝ)) * ∑ y, a y * c y ξ := by
    intro ξ
    unfold kernelG
    congr 1
    push_cast
    refine sum_congr rfl fun y _ => ?_
    simp only [a, c]
    rw [← Int.cast_mul, ← map_mul]
  have hsq : ∀ ξ, kernelG p R ξ ^ 2 =
      (1 / (p : ℝ)) ^ 2 * ∑ y, ∑ y', a y * a y' * (c y ξ * c y' ξ) := by
    intro ξ
    rw [hG, mul_pow, sq (∑ y, a y * c y ξ), sum_mul_sum]
    congr 1
    exact sum_congr rfl fun y _ => sum_congr rfl fun y' _ => by ring
  have hswap : ∑ ξ, ∑ y, ∑ y', a y * a y' * (c y ξ * c y' ξ) =
      ∑ y, ∑ y', a y * a y' * ((p : ℝ) * (if y = y' then 1 else 0) - 1) := by
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun y' _ => ?_
    rw [← mul_sum]
    simp only [c]
    rw [sum_chi_mul_chi hp2]
  have hclosed : ∑ y, ∑ y', a y * a y' * ((p : ℝ) * (if y = y' then 1 else 0) - 1) =
      (p : ℝ) * ∑ y, a y ^ 2 - (∑ y, a y) ^ 2 := by
    have e : ∀ y y', a y * a y' * ((p : ℝ) * (if y = y' then 1 else 0) - 1) =
        (p : ℝ) * (if y = y' then a y * a y' else 0) - a y * a y' := by
      intro y y'; split_ifs <;> ring
    simp_rw [e, sum_sub_distrib, ← mul_sum]
    simp only [sum_ite_eq, mem_univ, ↓reduceIte]
    rw [← sum_mul, ← sq]
    congr 2
    exact sum_congr rfl fun y _ => (sq (a y)).symm
  have ha2 : ∀ y, a y ^ 2 ≤ 1 := by
    intro y
    simp only [a]
    rcases quadraticChar_isQuadratic (ZMod p) (∏ b ∈ R, (y - b)) with h | h | h <;>
      rw [h] <;> norm_num
  have hsum2 : ∑ y, a y ^ 2 ≤ p := by
    calc ∑ y, a y ^ 2 ≤ ∑ _y : ZMod p, (1 : ℝ) := sum_le_sum fun y _ => ha2 y
      _ = p := by simp [ZMod.card]
  rw [sum_congr rfl fun ξ _ => hsq ξ, ← mul_sum, hswap, hclosed]
  have hsq0 := sq_nonneg (∑ y, a y)
  calc (1 / (p : ℝ)) ^ 2 * ((p : ℝ) * ∑ y, a y ^ 2 - (∑ y, a y) ^ 2)
      ≤ (1 / (p : ℝ)) ^ 2 * ((p : ℝ) * p) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
    _ = 1 := by field_simp

variable {U : Type*} [DecidableEq U]

/-- On injective labellings, `w_T(x) = 𝒢_{x(T∖{i})}(x_i)` for `i ∈ T`. -/
theorem starW_eq_kernelG {x : U → ZMod p} (hx : Function.Injective x) {T : Finset U} {i : U}
    (hi : i ∈ T) : starW x T = kernelG p ((T.erase i).image x) (x i) := by
  have hfac : ∀ z, ∏ j ∈ T, (z - x j) = (∏ a ∈ (T.erase i).image x, (z - a)) * (z - x i) := by
    intro z
    rw [prod_image (fun a _ b _ h => hx h)]
    exact (prod_erase_mul T (fun j => z - x j) hi).symm
  unfold starW kernelG
  congr 1
  push_cast
  refine sum_congr rfl fun z _ => ?_
  rw [prod_chi_eq, hfac z]

omit [DecidableEq U] in
/-- **The Weil bound of `lem:wt:stars`(a)**: `|w_T| ≤ (|T| - 1) r` on injective labellings. -/
theorem abs_starW_le (hW : Target.Weil) (hp2 : p ≠ 2) {x : U → ZMod p}
    (hx : Function.Injective x) {T : Finset U} (hT : T.Nonempty) :
    |starW x T| ≤ ((T.card : ℝ) - 1) * (1 / Real.sqrt p) := by
  have hWB := weilBound_of_target hW p hp2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have heq : starW x T = (1 / (p : ℝ)) * (rootSum (T.image x) : ℝ) := by
    unfold starW rootSum
    congr 1
    push_cast
    refine sum_congr rfl fun z _ => ?_
    rw [prod_chi_eq, prod_image (fun a _ b _ h => hx h)]
  have hb := hWB (T.image x) (hT.image x)
  rw [card_image_of_injective _ hx, ZMod.card] at hb
  rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / p)]
  calc 1 / (p : ℝ) * |(rootSum (T.image x) : ℝ)|
      ≤ 1 / (p : ℝ) * (((T.card : ℝ) - 1) * Real.sqrt p) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ((T.card : ℝ) - 1) * (1 / Real.sqrt p) := by
        rw [show 1 / (p : ℝ) * (((T.card : ℝ) - 1) * Real.sqrt p) =
          ((T.card : ℝ) - 1) * (Real.sqrt p / p) by ring, Real.sqrt_div_self']

variable [Fintype U]

namespace PinnedHalfLaw

variable (L : PinnedHalfLaw p U)

/-- On a fibre of positive mass, every admissible label has positive mass. -/
theorem pos_of_mem_phi (i : U) (x : U → ZMod p) (z₀ : ZMod p)
    (hz₀ : 0 < L.μ (Function.update x i z₀)) {z : ZMod p}
    (hz : z ∈ pinnedPhi L.N L.sign i x) : 0 < L.μ (Function.update x i z) := by
  have hupd : ∀ w, Function.update (Function.update x i z₀) i w = Function.update x i w :=
    fun w => Function.update_idem _ _ _
  have hΦ : pinnedPhi L.N L.sign i (Function.update x i z₀) = pinnedPhi L.N L.sign i x :=
    pinnedPhi_update L.N L.sign L.not_mem_N i x z₀
  have hpos := L.phi_card_pos i _ hz₀
  rw [hΦ] at hpos
  have hc := L.cond i _ hz₀ z
  simp only [hupd, hΦ, hz, ↓reduceIte] at hc
  have hM : 0 < ∑ w, L.μ (Function.update x i w) :=
    lt_of_lt_of_le hz₀ (single_le_sum (fun w _ => L.μ_nonneg _) (mem_univ z₀))
  have : L.μ (Function.update x i z) = (∑ w, L.μ (Function.update x i w)) /
      (pinnedPhi L.N L.sign i x).card := by
    rw [← hc, mul_div_assoc, div_self hpos.ne', mul_one]
  rw [this]
  exact div_pos hM hpos

/-- `|Φ_i|⁻¹ ≤ q 2^{d_i}/(1 - e_i)`. -/
theorem inv_phi_card_le (i : U) (x : U → ZMod p) (hx : 0 < L.μ x) :
    1 / ((pinnedPhi L.N L.sign i x).card : ℝ) ≤
      (1 / (p : ℝ)) * (2 ^ (L.N i).card / (1 - L.e i)) := by
  have hγ := L.gamma_le i x hx
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hpos := L.phi_card_pos i x hx
  have he : 0 < 1 - L.e i := by linarith [L.e_lt i]
  have h2 : (0 : ℝ) < 2 ^ (L.N i).card := by positivity
  have hk : (0 : ℝ) ≤ 2 ^ (L.N i).card / p := by positivity
  have h := mul_le_mul_of_nonneg_right hγ hk
  have e1 : (p : ℝ) / 2 ^ (L.N i).card / (pinnedPhi L.N L.sign i x).card *
      (2 ^ (L.N i).card / p) = 1 / (pinnedPhi L.N L.sign i x).card := by
    field_simp
  have e2 : 1 / (1 - L.e i) * (2 ^ (L.N i).card / p) =
      (1 / (p : ℝ)) * (2 ^ (L.N i).card / (1 - L.e i)) := by
    field_simp
  rw [e1, e2] at h
  exact h

end PinnedHalfLaw

/-- **The conditional bound of `lem:wt:stars`(a)**, fibrewise:
`E_μ[w_T² | x_{-i}] ≤ q 2^{d_i}/(1 - e_i)` for `i ∈ T`. -/
theorem wt_cond_second (hp2 : p ≠ 2) (L : PinnedHalfLaw p U) {T : Finset U} {i : U}
    (hi : i ∈ T) (x : U → ZMod p) :
    ∑ z, L.μ (Function.update x i z) * starW (Function.update x i z) T ^ 2 ≤
      (1 / (p : ℝ)) * (2 ^ (L.N i).card / (1 - L.e i)) * ∑ z, L.μ (Function.update x i z) := by
  by_cases h0 : ∃ z₀, 0 < L.μ (Function.update x i z₀)
  · obtain ⟨z₀, hz₀⟩ := h0
    rw [L.fibre_sum i x z₀ hz₀]
    have hval : ∀ z ∈ pinnedPhi L.N L.sign i x, starW (Function.update x i z) T ^ 2 =
        kernelG p ((T.erase i).image x) z ^ 2 := by
      intro z hz
      have hinj := L.μ_inj _ (L.pos_of_mem_phi i x z₀ hz₀ hz)
      rw [starW_eq_kernelG hinj hi, image_erase_update, Function.update_self]
    rw [sum_congr rfl hval]
    have hsub : ∑ z ∈ pinnedPhi L.N L.sign i x, kernelG p ((T.erase i).image x) z ^ 2 ≤ 1 :=
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun z _ _ => sq_nonneg _).trans
        (sum_kernelG_sq_le hp2 _)
    have hinv := L.inv_phi_card_le i _ hz₀
    rw [pinnedPhi_update L.N L.sign L.not_mem_N] at hinv
    have hM0 : 0 ≤ ∑ z, L.μ (Function.update x i z) := sum_nonneg fun z _ => L.μ_nonneg _
    have hpos : (0 : ℝ) ≤ 1 / ((pinnedPhi L.N L.sign i x).card : ℝ) := by positivity
    calc (∑ z, L.μ (Function.update x i z)) * (1 / ((pinnedPhi L.N L.sign i x).card : ℝ) *
          ∑ z ∈ pinnedPhi L.N L.sign i x, kernelG p ((T.erase i).image x) z ^ 2)
        ≤ (∑ z, L.μ (Function.update x i z)) * (1 / ((pinnedPhi L.N L.sign i x).card : ℝ) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsub hpos) hM0
      _ ≤ (∑ z, L.μ (Function.update x i z)) *
            ((1 / (p : ℝ)) * (2 ^ (L.N i).card / (1 - L.e i))) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left hinv hM0
      _ = (1 / (p : ℝ)) * (2 ^ (L.N i).card / (1 - L.e i)) * ∑ z, L.μ (Function.update x i z) := by
          ring
  · have hz := L.fibre_zero i x h0
    simp [hz]

/-- **`lem:wt:stars`(a), conditional form**: `E_μ w_T² ≤ q 2^{d_i}/(1 - e_i)` for `i ∈ T`. -/
theorem wt_second_cond (hp2 : p ≠ 2) (L : PinnedHalfLaw p U) {T : Finset U} {i : U}
    (hi : i ∈ T) :
    ∑ x, L.μ x * starW x T ^ 2 ≤ (1 / (p : ℝ)) * (2 ^ (L.N i).card / (1 - L.e i)) := by
  have hX : (0 : ℝ) < Fintype.card (ZMod p) := by exact_mod_cast Fintype.card_pos
  have havg : ∀ g : (U → ZMod p) → ℝ, ∑ x, g x =
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, ∑ z, g (Function.update x i z) := by
    intro g
    rw [sum_sum_update, ← mul_assoc, inv_mul_cancel₀ hX.ne', one_mul]
  rw [havg (fun x => L.μ x * starW x T ^ 2)]
  calc (Fintype.card (ZMod p) : ℝ)⁻¹ *
        ∑ x, ∑ z, L.μ (Function.update x i z) * starW (Function.update x i z) T ^ 2
      ≤ (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, (1 / (p : ℝ)) * (2 ^ (L.N i).card / (1 - L.e i)) *
          ∑ z, L.μ (Function.update x i z) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => wt_cond_second hp2 L hi x)
          (by positivity)
    _ = (1 / (p : ℝ)) * (2 ^ (L.N i).card / (1 - L.e i)) *
          ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, ∑ z, L.μ (Function.update x i z)) := by
        rw [← mul_sum]; ring
    _ = (1 / (p : ℝ)) * (2 ^ (L.N i).card / (1 - L.e i)) := by
        rw [← havg L.μ, L.μ_sum, mul_one]

/-- **`lem:wt:stars`(a), Weil form**: `E_μ w_T² ≤ (|T| - 1)² q`. -/
theorem wt_second_weil (hW : Target.Weil) (hp2 : p ≠ 2) (L : PinnedHalfLaw p U)
    {T : Finset U} (hT : T.Nonempty) :
    ∑ x, L.μ x * starW x T ^ 2 ≤ ((T.card : ℝ) - 1) ^ 2 * (1 / (p : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hpt : ∀ x, L.μ x * starW x T ^ 2 ≤ L.μ x * (((T.card : ℝ) - 1) ^ 2 * (1 / (p : ℝ))) := by
    intro x
    rcases (L.μ_nonneg x).lt_or_eq with hpos | hzero
    · apply mul_le_mul_of_nonneg_left _ (L.μ_nonneg x)
      have h := abs_starW_le hW hp2 (L.μ_inj x hpos) hT
      have h1 : (1 : ℝ) ≤ T.card := by exact_mod_cast card_pos.mpr hT
      have hsq : starW x T ^ 2 ≤ (((T.card : ℝ) - 1) * (1 / Real.sqrt p)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
      rw [mul_pow, div_pow, one_pow, Real.sq_sqrt hp0.le] at hsq
      exact hsq
    · rw [← hzero, zero_mul, zero_mul]
  calc ∑ x, L.μ x * starW x T ^ 2 ≤ ∑ x, L.μ x * (((T.card : ℝ) - 1) ^ 2 * (1 / (p : ℝ))) :=
        sum_le_sum fun x _ => hpt x
    _ = ((T.card : ℝ) - 1) ^ 2 * (1 / (p : ℝ)) := by rw [← sum_mul, L.μ_sum, one_mul]

end Sarkozy.SecondOrder
