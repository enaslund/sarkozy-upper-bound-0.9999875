module

public import Sarkozy.MiddleComparison.Atom
public import Sarkozy.MiddleRecords.ComparisonPrices
public import Sarkozy.MiddleRecords.AcceptingC2

@[expose] public section

/-!
# The prices of the constructed middle atom (`lem:middle-comparison-prices`)

`paper/sections/21_middle_records.tex`, `lem:middle-comparison-prices`.

The prices of `Replacements.toAtom` are, by construction (`rem:cp:charging`),
`s_𝔅 = ∑_t π̃^s_t sel` and `a_𝔅 = ∑_t π̃^a_t sel` with `π̃_t = P(r)⁻¹ w_t r^{deg} N_{t,ε}` for the
changed records and `P(r)⁻¹ c_d` (symmetric only) for the deleted ones.

* `sprice_eq`, `aprice_eq`: these sums written in the form of W6's
  `middle_comparison_prices` (folds, matchings, merges, constants, deletions).
* **`prices_le`** (`lem:middle-comparison-prices`, the prices): if the norms `N_{t,ε}` satisfy the
  per-record bounds of the paper (`prop:signed-bounds`(a),(b),(e) for the folds,
  `lem:record:exact-marginal-e`(ii) for the matchings, the table of `lem:merge-repair` for the six
  merges, `lem:record:accepting-c2` for the two constants), then
  `s_𝔅 ≤ (S₂ r² + S₃ r³ + S₄ r⁴ + S₅ r⁵) sel` and `a_𝔅 ≤ (A₂ r² + A₃ r³ + A₄ r⁴) sel`, with W6's
  coefficients `coefS2`, …, `coefA4` and `r = b^{-1/2}`. This is the per-block hypothesis `M_𝔅` of
  B2's `SAExplicit_of_bands` (with `M_𝔅` the sum of the two right-hand sides).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleComparison

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.ComparisonLawPaper Sarkozy.MiddleRecords

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
  {D : FrameData X} {acc : X → X → Prop} {E : Type} {Q : Queries E}

namespace Replacements

variable (R : Replacements D acc Q) (h : FrameFacts D acc Q)

/-- **The symmetric price, record by record** (in the form of W6's `middle_comparison_prices`). -/
theorem sprice_eq (hfh : 0 ≤ D.I.f₁ + D.I.h₁) (sel : ℝ) :
    (R.toAtom h).sprice sel =
      ∑ i, D.W.w .D * D.r / D.P * R.N (.inl i) .sym * sel +
        ∑ i, D.W.w .S * D.r / D.P * R.N (.inr (.inl i)) .sym * sel +
        ∑ j, D.W.w .R * D.r ^ 2 / D.P * R.N (.inr (.inr (.inl j))) .sym * sel +
        ∑ k, D.P⁻¹ * (D.W.w .C * D.r ^ 3) * R.N (.inr (.inr (.inr k))) .sym * sel +
        (6 * D.W.v .R * D.r ^ 3 + 2 * D.W.v .D * (D.I.f₁ + D.I.h₁) * D.r ^ 3 +
          2 * D.W.v .C * D.r ^ 4) / D.P * sel := by
  have hP := (P_inv_nonneg (D := D))
  have hr := D.r_nonneg
  have hcR : (Fintype.card (PType.Pat .R) : ℝ) = 6 := by
    rw [PType.card_pat]
    norm_num [PType.mult]
  rw [toAtom_sprice]
  simp only [Fintype.sum_sum_type, piT]
  have hR : ∀ φ : PType.Pat .R, |D.P⁻¹ * delCoef D (.inl φ)| * sel =
      D.P⁻¹ * (D.W.v .R * D.r ^ 3) * sel := by
    intro φ
    simp only [delCoef, midCoeff, PType.deg]
    rw [abs_of_nonneg (mul_nonneg hP (mul_nonneg (D.W.v_nonneg _) (pow_nonneg hr _)))]
  have hC : ∀ k : PType.Pat .C, |D.P⁻¹ * delCoef D (.inr (.inl k))| * sel =
      D.P⁻¹ * (D.W.v .C * D.r ^ 4) * sel := by
    intro k
    simp only [delCoef, midCoeff, PType.deg]
    rw [abs_of_nonneg (mul_nonneg hP (mul_nonneg (D.W.v_nonneg _) (pow_nonneg hr _)))]
  have hG : ∀ g : Fin 2, |D.P⁻¹ * delCoef D (.inr (.inr g))| * sel =
      D.P⁻¹ * ((D.I.f₁ + D.I.h₁) * D.r * (D.W.v .D * D.r ^ 2)) * sel := by
    intro g
    simp only [delCoef]
    rw [abs_of_nonneg (mul_nonneg hP (mul_nonneg (mul_nonneg hfh hr)
      (mul_nonneg (D.W.v_nonneg _) (pow_nonneg hr _))))]
  simp only [hR, hC, hG, sum_const, card_univ, nsmul_eq_mul, hcR]
  simp only [Fin.sum_univ_two, chgCoef, chgPat, foldPat, midCoeff, PType.deg, Fintype.card_fin]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  ring_nf

/-- **The skew price, record by record** (only the changed records are charged). -/
theorem aprice_eq (sel : ℝ) :
    (R.toAtom h).aprice sel =
      ∑ i, D.W.w .D * D.r / D.P * R.N (.inl i) .skew * sel +
        ∑ i, D.W.w .S * D.r / D.P * R.N (.inr (.inl i)) .skew * sel +
        ∑ j, D.W.w .R * D.r ^ 2 / D.P * R.N (.inr (.inr (.inl j))) .skew * sel +
        ∑ k, D.P⁻¹ * (D.W.w .C * D.r ^ 3) * R.N (.inr (.inr (.inr k))) .skew * sel := by
  rw [toAtom_aprice]
  simp only [Fintype.sum_sum_type, piT, zero_mul, sum_const_zero, add_zero]
  simp only [Fin.sum_univ_two, chgCoef, chgPat, foldPat, midCoeff, PType.deg]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  ring_nf

/-- The total price of the two constants: `≤ 2 w_C/(1 - 1/X)² r⁵ sel` and `≤ 2 w_C/(1 - 1/X) r⁴ sel`
(`lem:record:accepting-c2`, W6's `accepting_c2_prices`, record by record). -/
theorem const_prices_le {Xn b sel : ℝ} (hX : 1 < Xn) (hXb : Xn ≤ b) (hsel : 0 ≤ sel)
    (hCs : ∀ k, R.N (.inr (.inr (.inr k))) .sym ≤ D.r ^ 2 / (1 - 1 / b) ^ 2)
    (hCa : ∀ k, R.N (.inr (.inr (.inr k))) .skew ≤ D.r / (1 - 1 / b)) :
    ∑ k, D.P⁻¹ * (D.W.w .C * D.r ^ 3) * R.N (.inr (.inr (.inr k))) .sym * sel ≤
        2 * D.W.w .C / (1 - 1 / Xn) ^ 2 * D.r ^ 5 * sel ∧
      ∑ k, D.P⁻¹ * (D.W.w .C * D.r ^ 3) * R.N (.inr (.inr (.inr k))) .skew * sel ≤
        2 * D.W.w .C / (1 - 1 / Xn) * D.r ^ 4 * sel := by
  have hP1 : 1 ≤ D.P := one_le_midPoly D.W D.r_nonneg
  have hPi : D.P⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hP1
  have hP0 := (P_inv_nonneg (D := D))
  have hw : 0 ≤ D.W.w .C * D.r ^ 3 := mul_nonneg (D.W.w_nonneg _) (pow_nonneg D.r_nonneg _)
  have key : ∀ (k : PType.Pat .C) (e : ChangeType),
      D.P⁻¹ * (D.W.w .C * D.r ^ 3) * R.N (.inr (.inr (.inr k))) e * sel ≤
        D.W.w .C * D.r ^ 3 * R.N (.inr (.inr (.inr k))) e * sel := by
    intro k e
    have hN := R.N_nonneg (.inr (.inr (.inr k))) e
    have : D.P⁻¹ * (D.W.w .C * D.r ^ 3) ≤ D.W.w .C * D.r ^ 3 := by nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hN) hsel
  constructor
  · have hk : ∀ k : PType.Pat .C, D.W.w .C * D.r ^ 3 * R.N (.inr (.inr (.inr k))) .sym * sel ≤
        D.W.w .C / (1 - 1 / Xn) ^ 2 * D.r ^ 5 * sel := by
      intro k
      have := (accepting_c2_prices (D.W.w_nonneg .C) D.r_nonneg hsel hX hXb (hCs k)
        (hCa k)).1
      have e : 2 * D.W.w .C / (1 - 1 / Xn) ^ 2 * D.r ^ 5 * sel =
          2 * (D.W.w .C / (1 - 1 / Xn) ^ 2 * D.r ^ 5 * sel) := by ring
      linarith
    calc _ ≤ ∑ k : PType.Pat .C, D.W.w .C / (1 - 1 / Xn) ^ 2 * D.r ^ 5 * sel :=
          sum_le_sum fun k _ => (key k .sym).trans (hk k)
      _ = _ := by
          rw [sum_const, card_univ, PType.card_pat, nsmul_eq_mul]
          simp only [PType.mult]
          push_cast
          ring
  · have hk : ∀ k : PType.Pat .C, D.W.w .C * D.r ^ 3 * R.N (.inr (.inr (.inr k))) .skew * sel ≤
        D.W.w .C / (1 - 1 / Xn) * D.r ^ 4 * sel := by
      intro k
      have := (accepting_c2_prices (D.W.w_nonneg .C) D.r_nonneg hsel hX hXb (hCs k)
        (hCa k)).2
      have e : 2 * D.W.w .C / (1 - 1 / Xn) * D.r ^ 4 * sel =
          2 * (D.W.w .C / (1 - 1 / Xn) * D.r ^ 4 * sel) := by ring
      linarith
    calc _ ≤ ∑ k : PType.Pat .C, D.W.w .C / (1 - 1 / Xn) * D.r ^ 4 * sel :=
          sum_le_sum fun k _ => (key k .skew).trans (hk k)
      _ = _ := by
          rw [sum_const, card_univ, PType.card_pat, nsmul_eq_mul]
          simp only [PType.mult]
          push_cast
          ring

/-- **`lem:middle-comparison-prices`, the prices of the constructed atom.** Let `X ≥ 4` be the
piece start, `b ≥ X` the least prime of the block, `r = b^{-1/2}`, `sel ≥ 0`, `f₁ + h₁ ≥ 0`. If
the norms of the replacements satisfy the paper's per-record bounds (folds:
`prop:signed-bounds`(a),(b),(e); matchings: `lem:record:exact-marginal-e`(ii); merges: the table
of `lem:merge-repair`; constants: `lem:record:accepting-c2`), then
`s_𝔅 ≤ (S₂ r² + S₃ r³ + S₄ r⁴ + S₅ r⁵) sel` and `a_𝔅 ≤ (A₂ r² + A₃ r³ + A₄ r⁴) sel`. -/
theorem prices_le {Xn : ℕ} {b sel : ℝ} (hX : 4 ≤ Xn) (hb : (Xn : ℝ) ≤ b)
    (hr : D.r = 1 / Real.sqrt b) (hsel : 0 ≤ sel) (hfh : 0 ≤ D.I.f₁ + D.I.h₁) {sF aF ℓ sE aE : ℝ}
    (hFs : ∀ i, R.N (.inl i) .sym ≤ sF * (1 / Real.sqrt b) ^ 2)
    (hFa : ∀ i, R.N (.inl i) .skew ≤ ℓ * (1 / Real.sqrt b) + aF * (1 / Real.sqrt b) ^ 2)
    (hEs : ∀ i, R.N (.inr (.inl i)) .sym ≤ sE * (1 / Real.sqrt b))
    (hEa : ∀ i, R.N (.inr (.inl i)) .skew ≤ aE * (1 / Real.sqrt b))
    (hM : MergeRepairBounds b (fun j => R.N (.inr (.inr (.inl j))) .sym)
      (fun j => R.N (.inr (.inr (.inl j))) .skew))
    (hCs : ∀ k, R.N (.inr (.inr (.inr k))) .sym ≤ D.r ^ 2 / (1 - 1 / b) ^ 2)
    (hCa : ∀ k, R.N (.inr (.inr (.inr k))) .skew ≤ D.r / (1 - 1 / b)) :
    (R.toAtom h).sprice sel ≤
        (coefS2 D.W sE * (1 / Real.sqrt b) ^ 2 + coefS3 D.W D.I sF * (1 / Real.sqrt b) ^ 3 +
          coefS4 D.W (gS (1 / (Xn : ℝ))) * (1 / Real.sqrt b) ^ 4 +
          coefS5 D.W (1 / (Xn : ℝ)) * (1 / Real.sqrt b) ^ 5) * sel ∧
      (R.toAtom h).aprice sel ≤
        (coefA2 D.W ℓ aE * (1 / Real.sqrt b) ^ 2 +
          coefA3 D.W aF (gA (1 / (Xn : ℝ)) (rXof Xn)) * (1 / Real.sqrt b) ^ 3 +
          coefA4 D.W (1 / (Xn : ℝ)) * (1 / Real.sqrt b) ^ 4) * sel := by
  have hX1 : (1 : ℝ) < Xn := by
    have : (4 : ℝ) ≤ Xn := by exact_mod_cast hX
    linarith
  obtain ⟨hcs, hca⟩ := R.const_prices_le hX1 hb hsel hCs hCa
  rw [hr] at hcs hca
  have hP1 : 1 ≤ D.P := one_le_midPoly D.W D.r_nonneg
  have W6 := middle_comparison_prices D.W D.I hX hb hP1 hsel hfh
    (fun i => R.N (.inl i) .sym) (fun i => R.N (.inl i) .skew) (fun i => R.N_nonneg _ _)
    (fun i => R.N_nonneg _ _) hFs hFa
    (fun i => R.N (.inr (.inl i)) .sym) (fun i => R.N (.inr (.inl i)) .skew)
    (fun i => R.N_nonneg _ _) (fun i => R.N_nonneg _ _) hEs hEa
    (fun j => R.N (.inr (.inr (.inl j))) .sym) (fun j => R.N (.inr (.inr (.inl j))) .skew) hM
    hcs hca
  rw [R.sprice_eq h hfh, R.aprice_eq h]
  rw [hr]
  exact W6


/-- **The block price `s_𝔅 + a_𝔅`** (the per-block bound `M_𝔅` of B2's `SAExplicit_of_bands`). -/
theorem price_sum_le {Xn : ℕ} {b sel : ℝ} (hX : 4 ≤ Xn) (hb : (Xn : ℝ) ≤ b)
    (hr : D.r = 1 / Real.sqrt b) (hsel : 0 ≤ sel) (hfh : 0 ≤ D.I.f₁ + D.I.h₁) {sF aF ℓ sE aE : ℝ}
    (hFs : ∀ i, R.N (.inl i) .sym ≤ sF * (1 / Real.sqrt b) ^ 2)
    (hFa : ∀ i, R.N (.inl i) .skew ≤ ℓ * (1 / Real.sqrt b) + aF * (1 / Real.sqrt b) ^ 2)
    (hEs : ∀ i, R.N (.inr (.inl i)) .sym ≤ sE * (1 / Real.sqrt b))
    (hEa : ∀ i, R.N (.inr (.inl i)) .skew ≤ aE * (1 / Real.sqrt b))
    (hM : MergeRepairBounds b (fun j => R.N (.inr (.inr (.inl j))) .sym)
      (fun j => R.N (.inr (.inr (.inl j))) .skew))
    (hCs : ∀ k, R.N (.inr (.inr (.inr k))) .sym ≤ D.r ^ 2 / (1 - 1 / b) ^ 2)
    (hCa : ∀ k, R.N (.inr (.inr (.inr k))) .skew ≤ D.r / (1 - 1 / b)) :
    (R.toAtom h).sprice sel + (R.toAtom h).aprice sel ≤
      ((coefS2 D.W sE * (1 / Real.sqrt b) ^ 2 + coefS3 D.W D.I sF * (1 / Real.sqrt b) ^ 3 +
          coefS4 D.W (gS (1 / (Xn : ℝ))) * (1 / Real.sqrt b) ^ 4 +
          coefS5 D.W (1 / (Xn : ℝ)) * (1 / Real.sqrt b) ^ 5) +
        (coefA2 D.W ℓ aE * (1 / Real.sqrt b) ^ 2 +
          coefA3 D.W aF (gA (1 / (Xn : ℝ)) (rXof Xn)) * (1 / Real.sqrt b) ^ 3 +
          coefA4 D.W (1 / (Xn : ℝ)) * (1 / Real.sqrt b) ^ 4)) * sel := by
  obtain ⟨h1, h2⟩ := R.prices_le h hX hb hr hsel hfh hFs hFa hEs hEa hM hCs hCa
  linarith

end Replacements

end Sarkozy.MiddleComparison
