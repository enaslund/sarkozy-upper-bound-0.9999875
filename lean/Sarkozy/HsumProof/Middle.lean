module

public import Sarkozy.HsumProof.Upper
public import Sarkozy.NumericalFields.Signs

@[expose] public section

/-!
# The middle part of `SAParts3.hsum`, reduced to per-piece bounds on `κ` (HS)

`paper/sections/21_middle_records.tex`, `lem:middle-comparison-prices` (the coefficients
`S₂ = 2w_S s_E`, `A₂ = 2w_D ℓ_t + 2w_S a_E`, `S₃ = 2w_D s_F + 6v_R + 2v_D(f₁ + h₁)`,
`A₃ = 2w_D a_F + w_R g_A`, `S₄`, `A₄`, `S₅`), at the ALLp weights (`w_S = w_D`) and N2's F1 numbers
`f1c2`, `f1c3`.

E3's `middlePart κ` is affine in `κ = (s_F, a_F, ℓ_t, s_E, a_E)`:
* `middlePart_le_linear`: `middlePart κ ≤ ∑_i [2w_D c₂ (s_E + a_E + ℓ_t) + 2w_D c₃ (s_F + a_F)
  + fix_i]`, where `fix_i` (`midFix`) is the `κ`-free part with `r_X, b^{-1/2} ≤ 2^{-12}`;
* **`middlePart_le_of_kappa`**: if on every piece `s_E + a_E + ℓ_t ≤ 23/10` and
  `s_F + a_F ≤ 3700`, then `middlePart κ ≤ 0.8509` (kernel check `middle_uniform_check`). RG
  (7 November 2026): at `a_G = 71/10⁵` (the F1 numbers `f1C2`, `f1C3` regenerated there), with
  `3700` for HS's `1000` (room for the fold constants at `c₊ = 38`) and `0.8509` for `0.962`.

The paper's constants (`cert:signed-local`) are `s_E + a_E + ℓ_t ≤ 2.27374` and
`s_F + a_F ≤ 15.97` on every piece; RB's loosened table (`PaperKappa.lean`) has
`s_E + a_E + ℓ_t ≤ 2.2965` and `s_F + a_F ≤ 3622.6` (`paperKappa_bounds`).
-/

open Finset

namespace Sarkozy.HsumProof

open Sarkozy.PartV Sarkozy.MainFinal Sarkozy.NumericalFields
open Sarkozy.MiddleRecords (coefS2 coefS3 coefS4 coefS5 coefA2 coefA3 coefA4 gS gA rXof)
open Sarkozy.BlockSpecPaper (allpWeights allpInputs)
open Sarkozy.BlockSpecPaper.AllpData (allpRecord)
open Sarkozy.AnalyticCells (f1c2 f1c3 f1C2 f1C3)

/-- `2 w_D c₂` of piece `i`. -/
def midW2 (i : Fin 33) : ℚ := 2 * (allpRecord i).wD * f1C2 i.val

/-- `2 w_D c₃` of piece `i`. -/
def midW3 (i : Fin 33) : ℚ := 2 * (allpRecord i).wD * f1C3 i.val

/-- `q_X = 1/X`. -/
def midQ (i : Fin 33) : ℚ := 1 / (pieceStart i : ℚ)

/-- The bound `2^{-12}` of `r_X` and `b^{-1/2}`. -/
def rB : ℚ := 1 / 4096

/-- The `κ`-free part of the middle term of piece `i`, with `r_X, b^{-1/2} ≤ 2^{-12}`. -/
def midFix (i : Fin 33) : ℚ :=
  (6 * (allpRecord i).vR + 2 * (allpRecord i).vD * ((allpRecord i).f₁ + (allpRecord i).h₁) +
      (allpRecord i).wR * (4 * (1 + 8 * rB) / ((1 - 2 * midQ i) * (1 - 3 * midQ i)) +
        2 / (1 - midQ i))) * f1C3 i.val +
    (2 * (allpRecord i).vC + (allpRecord i).wR * (20 / ((1 - 2 * midQ i) * (1 - 3 * midQ i)) +
        4 / (1 - 2 * midQ i) + 2 / (1 - midQ i)) + 2 * (allpRecord i).wC / (1 - midQ i)) *
      rB * f1C3 i.val +
    2 * (allpRecord i).wC / (1 - midQ i) ^ 2 * rB ^ 2 * f1C3 i.val

theorem f1C2_nonneg (i : ℕ) : 0 ≤ f1C2 i := by
  unfold f1C2
  positivity

theorem f1C3_nonneg (i : ℕ) : 0 ≤ f1C3 i := by
  unfold f1C3
  positivity

theorem pieceScale_le (i : Fin 33) : pieceScale i ≤ (rB : ℝ) := by
  have h := MiddlePrimeInputs.pieceStart_ge i
  have h' : ((2 : ℝ) ^ 24) ≤ (pieceStart i : ℝ) := by exact_mod_cast h
  unfold pieceScale rB
  have hs : (4096 : ℝ) ≤ Real.sqrt (pieceStart i : ℝ) :=
    Real.le_sqrt_of_sq_le (by norm_num at h' ⊢; linarith)
  push_cast
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

theorem rXof_le (i : Fin 33) : rXof (pieceStart i) ≤ (rB : ℝ) := by
  have h := MiddlePrimeInputs.pieceStart_ge i
  have hs : 4096 ≤ Nat.sqrt (pieceStart i) := Nat.le_sqrt.mpr (by norm_num at h ⊢; omega)
  have hs' : (4096 : ℝ) ≤ (Nat.sqrt (pieceStart i) : ℝ) := by exact_mod_cast hs
  unfold rXof rB
  push_cast
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

theorem midQ_cast (i : Fin 33) : ((midQ i : ℚ) : ℝ) = 1 / (pieceStart i : ℝ) := by
  unfold midQ
  push_cast
  rfl

/-- **The middle term of piece `i` is at most the linear form.** -/
theorem middle_term_le (κ : Fin 33 → MiddleConsts) (i : Fin 33) :
    midK2 κ i * f1c2 i +
        (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) * f1c3 i ≤
      (midW2 i : ℝ) * ((κ i).sE + (κ i).aE + (κ i).ℓ) + (midW3 i : ℝ) * ((κ i).sF + (κ i).aF) +
        (midFix i : ℝ) := by
  have hq := qX_mem i
  have hq2 : (0 : ℝ) < 1 - 2 * (1 / (pieceStart i : ℝ)) := by linarith [hq.2]
  have hq3 : (0 : ℝ) < 1 - 3 * (1 / (pieceStart i : ℝ)) := by linarith [hq.2]
  have hq1 : (0 : ℝ) < 1 - 1 / (pieceStart i : ℝ) := by linarith [hq.2]
  have hc3 : (0 : ℝ) ≤ f1c3 i := by unfold f1c3; exact_mod_cast f1C3_nonneg _
  have hK4 := midK4_nonneg i
  have hK5 := midK5_nonneg i
  have hr := pieceScale_le i
  have hr0 : 0 ≤ pieceScale i := by unfold pieceScale; positivity
  have hrX := rXof_le i
  have hrX0 : 0 ≤ rXof (pieceStart i) := by unfold rXof; positivity
  have hwR : (0 : ℝ) ≤ (allpWeights i).w .R := (allpWeights i).w_nonneg _
  -- `g_A` increases in `r_X`
  have hgA : gA (1 / (pieceStart i : ℝ)) (rXof (pieceStart i)) ≤
      4 * (1 + 8 * (rB : ℝ)) / ((1 - 2 * (1 / (pieceStart i : ℝ))) *
        (1 - 3 * (1 / (pieceStart i : ℝ)))) + 2 / (1 - 1 / (pieceStart i : ℝ)) := by
    unfold gA
    have := div_le_div_of_nonneg_right (by linarith : 4 * (1 + 8 * rXof (pieceStart i)) ≤
      4 * (1 + 8 * (rB : ℝ))) (mul_pos hq2 hq3).le
    linarith
  have h4 : midK4 i * pieceScale i ≤ midK4 i * (rB : ℝ) := mul_le_mul_of_nonneg_left hr hK4
  have h5 : midK5 i * pieceScale i ^ 2 ≤ midK5 i * (rB : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr 2) hK5
  have hK3 : midK3 κ i ≤ 2 * (allpWeights i).w .D * (κ i).sF + 6 * (allpWeights i).v .R +
      2 * (allpWeights i).v .D * ((allpInputs i).f₁ + (allpInputs i).h₁) +
      2 * (allpWeights i).w .D * (κ i).aF +
      (allpWeights i).w .R * (4 * (1 + 8 * (rB : ℝ)) / ((1 - 2 * (1 / (pieceStart i : ℝ))) *
        (1 - 3 * (1 / (pieceStart i : ℝ)))) + 2 / (1 - 1 / (pieceStart i : ℝ))) := by
    unfold midK3 coefS3 coefA3
    have := mul_le_mul_of_nonneg_left hgA hwR
    linarith
  have hsum : midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2 ≤
      2 * (allpWeights i).w .D * (κ i).sF + 6 * (allpWeights i).v .R +
      2 * (allpWeights i).v .D * ((allpInputs i).f₁ + (allpInputs i).h₁) +
      2 * (allpWeights i).w .D * (κ i).aF +
      (allpWeights i).w .R * (4 * (1 + 8 * (rB : ℝ)) / ((1 - 2 * (1 / (pieceStart i : ℝ))) *
        (1 - 3 * (1 / (pieceStart i : ℝ)))) + 2 / (1 - 1 / (pieceStart i : ℝ))) +
      midK4 i * (rB : ℝ) + midK5 i * (rB : ℝ) ^ 2 := by linarith
  have h3 := mul_le_mul_of_nonneg_right hsum hc3
  refine (add_le_add (le_refl _) h3).trans (le_of_eq ?_)
  unfold midK2 midK4 midK5 coefS2 coefA2 coefS4 coefA4 coefS5 midW2 midW3 midFix f1c2 f1c3 gS
    midQ
  simp only [allpWeights, allpInputs, MiddleRecords.CompletionRecord.weights,
    MiddleRecords.CompletionRecord.inputs, MiddleRecords.CompletionRecord.w,
    MiddleRecords.CompletionRecord.v]
  push_cast
  ring

/-- **The middle part is at most the linear form in `κ`.** -/
theorem middlePart_le_linear (κ : Fin 33 → MiddleConsts) :
    middlePart κ ≤ ∑ i : Fin 33, ((midW2 i : ℝ) * ((κ i).sE + (κ i).aE + (κ i).ℓ) +
      (midW3 i : ℝ) * ((κ i).sF + (κ i).aF) + (midFix i : ℝ)) :=
  sum_le_sum fun i _ => middle_term_le κ i

/-- The rational check of the uniform bounds `23/10`, `3700` (RG: `3700` in place of HS's `1000`,
room for the fold constants at `c₊ = 38`; `0.8509` in place of `0.962`, at `a_G`). -/
theorem middle_uniform_check :
    ∑ i : Fin 33, (midW2 i * (23 / 10) + midW3 i * 3700 + midFix i) ≤ 8509 / 10000 := by
  decide +kernel

/-- **The middle part of `hsum` from per-piece bounds on the paper's constants**:
`s_E + a_E + ℓ_t ≤ 23/10` and `s_F + a_F ≤ 3700` on every piece give `middlePart κ ≤ 0.8509`
(RG's values at `a_G`; HS had `1000` and `0.962` at `a_T`). -/
theorem middlePart_le_of_kappa (κ : Fin 33 → MiddleConsts)
    (h : ∀ i, (κ i).sE + (κ i).aE + (κ i).ℓ ≤ 23 / 10 ∧ (κ i).sF + (κ i).aF ≤ 3700) :
    middlePart κ ≤ middleBudgetHS := by
  refine (middlePart_le_linear κ).trans ?_
  have hw2 : ∀ i, (0 : ℝ) ≤ (midW2 i : ℝ) := fun i => by
    have : (0 : ℚ) ≤ (allpRecord i).wD :=
      (Sarkozy.BlockSpecPaper.AllpData.allpRecord_nonneg i).1 .D
    have hc := f1C2_nonneg i.val
    unfold midW2
    push_cast
    have h' : (0 : ℝ) ≤ ((allpRecord i).wD : ℝ) := by exact_mod_cast this
    have hc' : (0 : ℝ) ≤ (f1C2 i.val : ℝ) := by exact_mod_cast hc
    positivity
  have hw3 : ∀ i, (0 : ℝ) ≤ (midW3 i : ℝ) := fun i => by
    have : (0 : ℚ) ≤ (allpRecord i).wD :=
      (Sarkozy.BlockSpecPaper.AllpData.allpRecord_nonneg i).1 .D
    have hc := f1C3_nonneg i.val
    unfold midW3
    push_cast
    have h' : (0 : ℝ) ≤ ((allpRecord i).wD : ℝ) := by exact_mod_cast this
    have hc' : (0 : ℝ) ≤ (f1C3 i.val : ℝ) := by exact_mod_cast hc
    positivity
  calc ∑ i : Fin 33, ((midW2 i : ℝ) * ((κ i).sE + (κ i).aE + (κ i).ℓ) +
        (midW3 i : ℝ) * ((κ i).sF + (κ i).aF) + (midFix i : ℝ)) ≤
      ∑ i : Fin 33, ((midW2 i : ℝ) * (23 / 10) + (midW3 i : ℝ) * 3700 + (midFix i : ℝ)) :=
        sum_le_sum fun i _ => by
          have := mul_le_mul_of_nonneg_left (h i).1 (hw2 i)
          have := mul_le_mul_of_nonneg_left (h i).2 (hw3 i)
          linarith
    _ = ((∑ i : Fin 33, (midW2 i * (23 / 10) + midW3 i * 3700 + midFix i) : ℚ) : ℝ) := by
        push_cast
        rfl
    _ ≤ ((8509 / 10000 : ℚ) : ℝ) := by exact_mod_cast middle_uniform_check
    _ = middleBudgetHS := by unfold middleBudgetHS; push_cast; rfl

end Sarkozy.HsumProof
