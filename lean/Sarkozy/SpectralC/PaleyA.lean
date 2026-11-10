module

public import Sarkozy.SpectralC.CouplingData
public import Sarkozy.SpectralC.PaleyOne

@[expose] public section

/-!
# The deviation of the coupling densities from the stars (`lem:spec2:paley`(a))

`paper/sections/14_spectral.tex`, the Paley part of `subsec:spec:coupling`. For a labelling `x`
(injective, as in `𝓘⁺`), `φ_k(a; x) = ∏_{j∈N(k)} (1 + χ(ς_jk(a − x_j)))` (`starProd`) and, for a
probability vector `P_k` supported on `Φ_k(x)` with `|Φ_k(x)| P_k ∈ [1/R'_k, R'_k]` there
(condition (iii) of `def:coupling-data`), `E_k = p P_k − φ_k`. With the count
`|Φ_k(x)| ∈ p 2^{-r_k} [1 − ê_k, 1 + ê_k]` of `lem:extension`(coarse) (a hypothesis),
`Δ_k = max(R'_k/(1 − ê_k) − 1, 1 − 1/((1 + ê_k)R'_k))` and
`Ê² = ∑_k (2^{r_k}(1 + ê_k)Δ_k² + n 4^{r_k}/p)`:

`lem:spec2:paley`(a): `‖∑_k w_k E_k(·; x)‖² ≤ Ê² |w|²` (`paley_deviation`).

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- `φ_k(a; x) = ∏_{j ∈ N(k)} (1 + χ(ς_jk(a − x_j)))`. -/
noncomputable def starProd (N : U → Finset U) (ς : U → U → ZMod p) (k : U) (x : U → ZMod p)
    (a : ZMod p) : ℂ :=
  ∏ j ∈ N k, (1 + chiC p (ς j k * (a - x j)))

/-- `Δ_k = max(R'/(1 − ê) − 1, 1 − 1/((1 + ê)R'))`. -/
noncomputable def devConst (Rp e : ℝ) : ℝ := max (Rp / (1 - e) - 1) (1 - 1 / ((1 + e) * Rp))

lemma norm_one_add_chiC_le (t : ZMod p) : ‖1 + chiC p t‖ ≤ 2 := by
  by_cases h : t = 0
  · rw [h, chiC_zero, add_zero, norm_one]; norm_num
  · rw [chiC_apply]
    rcases quadraticChar_dichotomy h with h1 | h1 <;> rw [h1] <;> norm_num

omit [Fintype U] [DecidableEq U] in
lemma norm_starProd_le (N : U → Finset U) (ς : U → U → ZMod p) (k : U) (x : U → ZMod p)
    (a : ZMod p) : ‖starProd N ς k x a‖ ≤ 2 ^ (N k).card := by
  unfold starProd
  rw [norm_prod]
  calc ∏ j ∈ N k, ‖1 + chiC p (ς j k * (a - x j))‖ ≤ ∏ _j ∈ N k, (2 : ℝ) :=
        prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => norm_one_add_chiC_le _)
    _ = 2 ^ (N k).card := by rw [prod_const]

/-- Off the labels, `φ_k = 2^{r_k} 1_{Φ_k}` (signs `ς_jk ≠ 0` for `j ∈ N(k)`). -/
lemma starProd_off_labels (N : U → Finset U) (ς : U → U → ZMod p)
    (hς : ∀ k, ∀ j ∈ N k, ς j k ≠ 0)
    (k : U) (x : U → ZMod p) {a : ZMod p} (ha : a ∉ univ.image x) :
    starProd N ς k x a = if a ∈ allowedSet N ς k x then (2 : ℂ) ^ (N k).card else 0 := by
  have hfac : ∀ j ∈ N k, 1 + chiC p (ς j k * (a - x j)) =
      if IsSquare (ς j k * (a - x j)) then 2 else 0 := by
    intro j hj
    have hne : ς j k * (a - x j) ≠ 0 := by
      apply mul_ne_zero (hς k j hj)
      intro h
      apply ha
      rw [mem_image]
      exact ⟨j, mem_univ _, (sub_eq_zero.mp h).symm⟩
    split_ifs with hs
    · rw [chiC_of_isSquare hne hs]; norm_num
    · rw [chiC_of_not_isSquare hs]; ring
  unfold starProd
  rw [prod_congr rfl hfac, prod_ite]
  by_cases hmem : a ∈ allowedSet N ς k x
  · rw [ite_eq_left hmem]
    have hall : (N k).filter (fun j => ¬ IsSquare (ς j k * (a - x j))) = ∅ := by
      rw [filter_eq_empty_iff]
      intro j hj
      unfold allowedSet at hmem
      rw [mem_filter] at hmem
      exact not_not.mpr (hmem.2.2 j hj).2
    have hall2 : (N k).filter (fun j => IsSquare (ς j k * (a - x j))) = N k := by
      rw [filter_eq_self]
      intro j hj
      unfold allowedSet at hmem
      rw [mem_filter] at hmem
      exact (hmem.2.2 j hj).2
    rw [hall, hall2, prod_empty, mul_one, prod_const]
  · rw [ite_eq_right hmem]
    have hex : ∃ j ∈ N k, ¬ IsSquare (ς j k * (a - x j)) := by
      by_contra hcon
      push Not at hcon
      apply hmem
      unfold allowedSet
      rw [mem_filter]
      refine ⟨mem_univ _, ha, fun j hj => ⟨?_, hcon j hj⟩⟩
      apply mul_ne_zero (hς k j hj)
      intro h
      apply ha
      rw [mem_image]
      exact ⟨j, mem_univ _, (sub_eq_zero.mp h).symm⟩
    obtain ⟨j, hj, hjs⟩ := hex
    have hmem2 : j ∈ (N k).filter (fun j => ¬ IsSquare (ς j k * (a - x j))) := by
      rw [mem_filter]; exact ⟨hj, hjs⟩
    rw [prod_eq_zero hmem2 rfl, mul_zero]

/-- The pointwise deviation on `Φ_k`: `|p P_k(a) − 2^{r_k}| ≤ 2^{r_k} Δ_k`. -/
lemma dev_on_allowed {r : ℕ} {Pa card pR Rp e : ℝ} (hRp : 1 ≤ Rp) (he0 : 0 ≤ e) (he1 : e < 1)
    (hpR : 0 < pR) (hcard1 : pR / 2 ^ r * (1 - e) ≤ card) (hcard2 : card ≤ pR / 2 ^ r * (1 + e))
    (hq1 : Rp⁻¹ ≤ Pa * card) (hq2 : Pa * card ≤ Rp) :
    |pR * Pa - 2 ^ r| ≤ 2 ^ r * devConst Rp e := by
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  have hcard0 : 0 < card := by
    have : 0 < pR / 2 ^ r * (1 - e) := by
      apply mul_pos (div_pos hpR h2r); linarith
    linarith
  set lam := pR / (2 ^ r * card) with hlam
  have hlam0 : 0 < lam := by positivity
  have hpP : pR * Pa = 2 ^ r * (lam * (Pa * card)) := by
    rw [hlam]; field_simp
  have hlam1 : lam ≤ 1 / (1 - e) := by
    rw [hlam, div_le_div_iff₀ (by positivity) (by linarith)]
    have := mul_le_mul_of_nonneg_left hcard1 h2r.le
    rw [show (2 : ℝ) ^ r * (pR / 2 ^ r * (1 - e)) = pR * (1 - e) by field_simp] at this
    linarith
  have hlam2 : 1 / (1 + e) ≤ lam := by
    rw [hlam, div_le_div_iff₀ (by linarith) (by positivity)]
    have := mul_le_mul_of_nonneg_left hcard2 h2r.le
    rw [show (2 : ℝ) ^ r * (pR / 2 ^ r * (1 + e)) = pR * (1 + e) by field_simp] at this
    linarith
  set q := Pa * card with hq
  have hq0 : 0 < q := lt_of_lt_of_le (inv_pos.mpr (by linarith)) hq1
  have hup : lam * q ≤ Rp / (1 - e) := by
    calc lam * q ≤ 1 / (1 - e) * Rp :=
          mul_le_mul hlam1 hq2 hq0.le (by apply div_nonneg <;> linarith)
      _ = Rp / (1 - e) := by ring
  have hlow : 1 / ((1 + e) * Rp) ≤ lam * q := by
    calc 1 / ((1 + e) * Rp) = 1 / (1 + e) * Rp⁻¹ := by field_simp
      _ ≤ lam * q := mul_le_mul hlam2 hq1 (by positivity) hlam0.le
  rw [hpP, ← mul_sub_one, abs_mul, abs_of_pos h2r]
  apply mul_le_mul_of_nonneg_left _ h2r.le
  unfold devConst
  rw [abs_le]
  constructor
  · have := le_max_right (Rp / (1 - e) - 1) (1 - 1 / ((1 + e) * Rp))
    linarith
  · have := le_max_left (Rp / (1 - e) - 1) (1 - 1 / ((1 + e) * Rp))
    linarith

/-- **`lem:spec2:paley`(a)**: `‖∑_k w_k E_k(·; x)‖² ≤ Ê² |w|²`, with
`E_k = p P_k(· | x) − φ_k` and `Ê² = ∑_k (2^{r_k}(1 + ê_k)Δ_k² + n 4^{r_k}/p)`; the count of
`lem:extension`(coarse) for `|Φ_k(x)|` is the hypothesis `hcount`. -/
theorem paley_deviation (N : U → Finset U) (ς : U → U → ZMod p)
    (hς : ∀ k, ∀ j ∈ N k, ς j k ≠ 0)
    (x : U → ZMod p) (P : U → ZMod p → ℝ)
    (hPsupp : ∀ k a, a ∉ allowedSet N ς k x → P k a = 0) (Rp : U → ℝ) (hRp : ∀ k, 1 ≤ Rp k)
    (hPdens : ∀ k, ∀ a ∈ allowedSet N ς k x,
      (Rp k)⁻¹ ≤ P k a * (allowedSet N ς k x).card ∧ P k a * (allowedSet N ς k x).card ≤ Rp k)
    (ehat : U → ℝ) (he0 : ∀ k, 0 ≤ ehat k) (he1 : ∀ k, ehat k < 1)
    (hcount : ∀ k, (p : ℝ) / 2 ^ (N k).card * (1 - ehat k) ≤ (allowedSet N ς k x).card ∧
      ((allowedSet N ς k x).card : ℝ) ≤ (p : ℝ) / 2 ^ (N k).card * (1 + ehat k))
    (w : U → ℂ) :
    l2sq (fun a => ∑ k, w k * ((p : ℂ) * (P k a : ℂ) - starProd N ς k x a)) ≤
      (∑ k, ((2 : ℝ) ^ (N k).card * (1 + ehat k) * devConst (Rp k) (ehat k) ^ 2 +
        (Fintype.card U : ℝ) * 4 ^ (N k).card / p)) * ∑ k, ‖w k‖ ^ 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set E : U → ZMod p → ℂ := fun k a => (p : ℂ) * (P k a : ℂ) - starProd N ς k x a with hE
  -- pointwise Cauchy--Schwarz in `k`
  have hpt : ∀ a, ‖∑ k, w k * E k a‖ ^ 2 ≤ (∑ k, ‖w k‖ ^ 2) * ∑ k, ‖E k a‖ ^ 2 := by
    intro a
    have h1 : ‖∑ k, w k * E k a‖ ≤ ∑ k, ‖w k‖ * ‖E k a‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      apply sum_congr rfl; intro k _; rw [norm_mul]
    have h2 := sum_mul_sq_le_sq_mul_sq univ (fun k => ‖w k‖) (fun k => ‖E k a‖)
    calc ‖∑ k, w k * E k a‖ ^ 2 ≤ (∑ k, ‖w k‖ * ‖E k a‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  -- the deviation of one `E_k`
  have hEk : ∀ k, (p : ℝ)⁻¹ * ∑ a, ‖E k a‖ ^ 2 ≤
      (2 : ℝ) ^ (N k).card * (1 + ehat k) * devConst (Rp k) (ehat k) ^ 2 +
        (Fintype.card U : ℝ) * 4 ^ (N k).card / p := by
    intro k
    set Φ := allowedSet N ς k x with hΦ
    set r := (N k).card with hr
    have hsplit : ∑ a, ‖E k a‖ ^ 2 = ∑ a ∈ Φ, ‖E k a‖ ^ 2 + ∑ a ∈ univ \ Φ, ‖E k a‖ ^ 2 := by
      rw [← sum_union disjoint_sdiff, union_sdiff_of_subset (subset_univ _)]
    -- on `Φ_k`
    have hon : ∑ a ∈ Φ, ‖E k a‖ ^ 2 ≤ Φ.card * (2 ^ r * devConst (Rp k) (ehat k)) ^ 2 := by
      calc ∑ a ∈ Φ, ‖E k a‖ ^ 2 ≤ ∑ _a ∈ Φ, (2 ^ r * devConst (Rp k) (ehat k)) ^ 2 := by
            apply sum_le_sum
            intro a ha
            have hax : a ∉ univ.image x := by
              rw [hΦ] at ha; unfold allowedSet at ha; rw [mem_filter] at ha; exact ha.2.1
            have hφ : starProd N ς k x a = (2 : ℂ) ^ r := by
              rw [starProd_off_labels N ς hς k x hax, ite_eq_left ha]
            have hEa : E k a = (((p : ℝ) * P k a - 2 ^ r : ℝ) : ℂ) := by
              simp only [hE, hφ]; push_cast; ring
            rw [hEa, Complex.norm_real, Real.norm_eq_abs, sq_abs]
            have hd := dev_on_allowed (r := r) (hRp k) (he0 k) (he1 k) hp (hcount k).1
              (hcount k).2 (hPdens k a ha).1 (hPdens k a ha).2
            have h0 : 0 ≤ (2 : ℝ) ^ r * devConst (Rp k) (ehat k) :=
              (abs_nonneg _).trans hd
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) hd 2
        _ = Φ.card * (2 ^ r * devConst (Rp k) (ehat k)) ^ 2 := by
            rw [sum_const, nsmul_eq_mul]
    -- off `Φ_k`: only the labels contribute
    have hoff : ∑ a ∈ univ \ Φ, ‖E k a‖ ^ 2 ≤ (Fintype.card U : ℝ) * 4 ^ r := by
      have hsub : ∀ a ∈ univ \ Φ, ‖E k a‖ ^ 2 ≤ if a ∈ univ.image x then (4 : ℝ) ^ r else 0 := by
        intro a ha
        rw [mem_sdiff] at ha
        have hP : P k a = 0 := hPsupp k a ha.2
        have hEa : E k a = -starProd N ς k x a := by simp only [hE, hP]; push_cast; ring
        rw [hEa, norm_neg]
        by_cases hax : a ∈ univ.image x
        · rw [ite_eq_left hax]
          have := norm_starProd_le N ς k x a
          rw [show (4 : ℝ) ^ r = ((2 : ℝ) ^ r) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
          exact pow_le_pow_left₀ (norm_nonneg _) this 2
        · rw [ite_eq_right hax, starProd_off_labels N ς hς k x hax, ite_eq_right ha.2]
          simp
      calc ∑ a ∈ univ \ Φ, ‖E k a‖ ^ 2
          ≤ ∑ a ∈ univ \ Φ, (if a ∈ univ.image x then (4 : ℝ) ^ r else 0) := sum_le_sum hsub
        _ ≤ ∑ a, (if a ∈ univ.image x then (4 : ℝ) ^ r else 0) :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun a _ _ => by split_ifs <;> positivity)
        _ = (univ.image x).card * 4 ^ r := by
            rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
        _ ≤ (Fintype.card U : ℝ) * 4 ^ r := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have := card_image_le (s := (univ : Finset U)) (f := x)
            rw [card_univ] at this
            exact_mod_cast this
    have hΦcard : (Φ.card : ℝ) ≤ (p : ℝ) / 2 ^ r * (1 + ehat k) := (hcount k).2
    rw [hsplit]
    calc (p : ℝ)⁻¹ * (∑ a ∈ Φ, ‖E k a‖ ^ 2 + ∑ a ∈ univ \ Φ, ‖E k a‖ ^ 2)
        ≤ (p : ℝ)⁻¹ * ((p : ℝ) / 2 ^ r * (1 + ehat k) * (2 ^ r * devConst (Rp k) (ehat k)) ^ 2 +
            (Fintype.card U : ℝ) * 4 ^ r) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply add_le_add _ hoff
          exact hon.trans (mul_le_mul_of_nonneg_right hΦcard (sq_nonneg _))
      _ = (2 : ℝ) ^ r * (1 + ehat k) * devConst (Rp k) (ehat k) ^ 2 +
            (Fintype.card U : ℝ) * 4 ^ r / p := by
          field_simp
  -- assemble
  unfold l2sq
  calc (p : ℝ)⁻¹ * ∑ a, ‖∑ k, w k * E k a‖ ^ 2
      ≤ (p : ℝ)⁻¹ * ∑ a, (∑ k, ‖w k‖ ^ 2) * ∑ k, ‖E k a‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun a _ => hpt a) (by positivity)
    _ = (∑ k, ‖w k‖ ^ 2) * ∑ k, (p : ℝ)⁻¹ * ∑ a, ‖E k a‖ ^ 2 := by
        rw [← mul_sum, mul_left_comm, sum_comm, mul_sum]
    _ ≤ (∑ k, ‖w k‖ ^ 2) * ∑ k, ((2 : ℝ) ^ (N k).card * (1 + ehat k) *
          devConst (Rp k) (ehat k) ^ 2 + (Fintype.card U : ℝ) * 4 ^ (N k).card / p) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => hEk k) (by positivity)
    _ = _ := mul_comm _ _

end Sarkozy.SpectralC
