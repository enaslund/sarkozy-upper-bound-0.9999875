module

public import Sarkozy.SharpBase.Parts

@[expose] public section

/-!
# Sanity checks for SH2: the shared `r₂`, and what the remainder consists of

SH2 (7 November 2026). DC2's finding 1: the fields `hdiff` (with a free `r₂`) are satisfiable on
their own, so the content of `lem:sharp-first` reaches the main statement only through the
summation fields (`hr2`, and B9's `hm` built from them), which must use **the same** `r₂`. Here:

* `envMeansBase_r2L`, …: the constructors put the paper's `r₂` (`r2EnvL/R`, `r2FixL/R`) in the
  `r₂` slot read by `hdiff` **and** by `hr2` (by `rfl`; `hr2` is stated for that slot), and B9's
  bundles (`toEnvMeansInputs`, `toFixMeansInputs`, read by the endgame through `hmL/R`) keep it;
* `rchOpt_le_rchVal`: when both whole bounds are positive, the re-optimized remainder is at
  most DC3's `rchVal` (nothing is lost by the switch);
* `rchOpt_le_cross`: the re-optimized remainder of one choice and tag is at most the paper's
  error terms `√(W M₊ R₋) + √(W M₋ R₊) + √(R₊ R₋)` when both whole bounds `A_± = W M_± + R_±`
  are positive, and `(R₊ + R₋)/2` with one of `R_±` zero otherwise. Here `R_±` are DC3's
  weighted remainders (chain remainders `G C_dc L^{-σ} α` at the small pieces, `|𝔈_±|` at the
  large pieces, and in DC3's bad case the main term of the fold whose partner vanishes) and
  `W M_±` the main terms. So `RchSum*` asks for the summation of these terms only.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.SharpBase

open Sarkozy.DensityChain2

section Algebra

variable {Φ : Type} [Fintype Φ]

/-- **The re-optimized remainder is made of the paper's error terms**:
`rchOpt ≤ √(W M₊ R₋) + √(W M₋ R₊) + √(R₊ R₋)` when both whole bounds `A_± = W M_± + R_±` are
positive, and `rchOpt ≤ (R₊ + R₋)/2` (one of `R_±` is then `0`) otherwise. -/
theorem rchOpt_le_cross (small : Φ → Prop) {K₀ Pp Pm Cr : ℝ} (hK₀ : 0 ≤ K₀) (hPp : 0 ≤ Pp)
    (hPm : 0 ≤ Pm) (hCr : 0 ≤ Cr) (w BG Gp Gm Fp Fm : Φ → ℝ) (hw : ∀ φ, 0 ≤ w φ)
    (hBG : ∀ φ, 0 ≤ BG φ) (hGp : ∀ φ, 0 ≤ Gp φ) (hGm : ∀ φ, 0 ≤ Gm φ) :
    rchOpt small K₀ Pp Pm Cr w BG Gp Gm Fp Fm ≤
      Real.sqrt ((∑ φ, w φ * BG φ) * hfoldM K₀ Pp Pm Pp *
          (∑ φ, w φ * hfoldR small K₀ Pp Pm Pm Cr BG Gm Fm φ)) +
        Real.sqrt ((∑ φ, w φ * BG φ) * hfoldM K₀ Pp Pm Pm *
          (∑ φ, w φ * hfoldR small K₀ Pp Pm Pp Cr BG Gp Fp φ)) +
        Real.sqrt ((∑ φ, w φ * hfoldR small K₀ Pp Pm Pp Cr BG Gp Fp φ) *
          (∑ φ, w φ * hfoldR small K₀ Pp Pm Pm Cr BG Gm Fm φ)) +
        (if 0 < (∑ φ, w φ * BG φ) * hfoldM K₀ Pp Pm Pp +
              ∑ φ, w φ * hfoldR small K₀ Pp Pm Pp Cr BG Gp Fp φ ∧
            0 < (∑ φ, w φ * BG φ) * hfoldM K₀ Pp Pm Pm +
              ∑ φ, w φ * hfoldR small K₀ Pp Pm Pm Cr BG Gm Fm φ then 0
          else ((∑ φ, w φ * hfoldR small K₀ Pp Pm Pp Cr BG Gp Fp φ) +
            (∑ φ, w φ * hfoldR small K₀ Pp Pm Pm Cr BG Gm Fm φ)) / 2) := by
  unfold rchOpt
  set W := ∑ φ, w φ * BG φ with hWdef
  set Mp := hfoldM K₀ Pp Pm Pp with hMp
  set Mm := hfoldM K₀ Pp Pm Pm with hMm
  set Rp := ∑ φ, w φ * hfoldR small K₀ Pp Pm Pp Cr BG Gp Fp φ with hRp
  set Rm := ∑ φ, w φ * hfoldR small K₀ Pp Pm Pm Cr BG Gm Fm φ with hRm
  have hW : 0 ≤ W := sum_nonneg fun φ _ => mul_nonneg (hw φ) (hBG φ)
  have hMp0 : 0 ≤ Mp := hfoldM_nonneg hK₀ hPp
  have hMm0 : 0 ≤ Mm := hfoldM_nonneg hK₀ hPm
  have hRp0 : 0 ≤ Rp := sum_nonneg fun φ _ =>
    mul_nonneg (hw φ) (hfoldR_nonneg small hK₀ hPp hCr BG Gp Fp hBG hGp φ)
  have hRm0 : 0 ≤ Rm := sum_nonneg fun φ _ =>
    mul_nonneg (hw φ) (hfoldR_nonneg small hK₀ hPm hCr BG Gm Fm hBG hGm φ)
  -- DC3's main prices vanish together
  have hMpm : Mp = 0 → Mm = 0 := by
    intro h0
    rw [hMp] at h0
    rw [hMm]
    unfold hfoldM at h0 ⊢
    split_ifs at h0 ⊢ with hg
    · exact absurd h0 (ne_of_gt hg.1)
    · rfl
  have hMmp : Mm = 0 → Mp = 0 := by
    intro h0
    rw [hMm] at h0
    rw [hMp]
    unfold hfoldM at h0 ⊢
    split_ifs at h0 ⊢ with hg
    · exact absurd h0 (ne_of_gt hg.2)
    · rfl
  have hs1 := Real.sqrt_nonneg (W * Mp * Rm)
  have hs2 := Real.sqrt_nonneg (W * Mm * Rp)
  have hs : 0 ≤ W * Real.sqrt (Mp * Mm) := mul_nonneg hW (Real.sqrt_nonneg _)
  have hAp : 0 ≤ W * Mp + Rp := add_nonneg (mul_nonneg hW hMp0) hRp0
  have hAm : 0 ≤ W * Mm + Rm := add_nonneg (mul_nonneg hW hMm0) hRm0
  have hs3 := Real.sqrt_nonneg (Rp * Rm)
  by_cases hnd : 0 < W * Mp + Rp ∧ 0 < W * Mm + Rm
  · have h1 := rchOptVal_le_cross hW hMp0 hMm0 hRp0 hRm0 hnd.1 hnd.2
    simp only [hnd, and_self, ↓reduceIte, add_zero]
    exact h1
  · simp only [hnd, ↓reduceIte]
    have hval : rchOptVal W Mp Mm Rp Rm =
        ((W * Mp + Rp) + (W * Mm + Rm)) / 2 - W * Real.sqrt (Mp * Mm) := by
      unfold rchOptVal optT
      simp only [hnd, ↓reduceIte, one_mul, div_one]
    rw [hval]
    rcases not_and_or.mp hnd with h | h
    · have hA : W * Mp + Rp = 0 := le_antisymm (not_lt.mp h) hAp
      have h1 : W * Mp = 0 := by linarith [mul_nonneg hW hMp0]
      have h3 : W * Mm = 0 := by
        rcases mul_eq_zero.mp h1 with h4 | h4
        · rw [h4, zero_mul]
        · rw [hMpm h4, mul_zero]
      linarith
    · have hA : W * Mm + Rm = 0 := le_antisymm (not_lt.mp h) hAm
      have h1 : W * Mm = 0 := by linarith [mul_nonneg hW hMm0]
      have h3 : W * Mp = 0 := by
        rcases mul_eq_zero.mp h1 with h4 | h4
        · rw [h4, zero_mul]
        · rw [hMmp h4, mul_zero]
      linarith

/-- **The re-optimized remainder is never larger than DC3's** when both whole bounds are positive:
`rchOpt ≤ rchVal` (DC3's `HfoldAlgebra.rchVal`, ratio `t = √(M₋/M₊)` or `√(R₋/R₊)`). So the
switch to `rchOpt` loses nothing; it removes the ratio `√(M₋/M₊)` from the remainder. -/
theorem rchOpt_le_rchVal (small : Φ → Prop) {K₀ Pp Pm Cr : ℝ} (w BG Gp Gm Fp Fm : Φ → ℝ)
    (hw : ∀ φ, 0 ≤ w φ) (hBG : ∀ φ, 0 ≤ BG φ)
    (hnd : 0 < (∑ φ, w φ * BG φ) * hfoldM K₀ Pp Pm Pp +
        ∑ φ, w φ * hfoldR small K₀ Pp Pm Pp Cr BG Gp Fp φ ∧
      0 < (∑ φ, w φ * BG φ) * hfoldM K₀ Pp Pm Pm +
        ∑ φ, w φ * hfoldR small K₀ Pp Pm Pm Cr BG Gm Fm φ) :
    rchOpt small K₀ Pp Pm Cr w BG Gp Gm Fp Fm ≤ rchVal small K₀ Pp Pm Cr w BG Gp Gm Fp Fm := by
  have hTpos := hfoldT_pos small K₀ Pp Pm Cr w BG Gp Gm Fp Fm
  unfold rchOpt rchVal
  set T := hfoldT small K₀ Pp Pm Cr w BG Gp Gm Fp Fm with hTdef
  set W := ∑ φ, w φ * BG φ with hWdef
  set Mp := hfoldM K₀ Pp Pm Pp with hMp
  set Mm := hfoldM K₀ Pp Pm Pm with hMm
  set Rp := ∑ φ, w φ * hfoldR small K₀ Pp Pm Pp Cr BG Gp Fp φ with hRp
  set Rm := ∑ φ, w φ * hfoldR small K₀ Pp Pm Pm Cr BG Gm Fm φ with hRm
  have hW : 0 ≤ W := sum_nonneg fun φ _ => mul_nonneg (hw φ) (hBG φ)
  have hkey : T * Mp + Mm / T ≤ 2 * Real.sqrt (Mp * Mm) := by
    by_cases hg : HfoldGood K₀ Pp Pm
    · have hMpv : Mp = K₀ * Pp := by
        rw [hMp]
        unfold hfoldM
        simp only [hg, ↓reduceIte]
      have hMmv : Mm = K₀ * Pm := by
        rw [hMm]
        unfold hfoldM
        simp only [hg, ↓reduceIte]
      have hT : T = Real.sqrt (Mm / Mp) := by
        rw [hTdef, hMp, hMm]
        unfold hfoldT
        simp only [hg, ↓reduceIte]
      have hp0 : 0 < Mp := hMpv ▸ hg.1
      have hm0 : 0 < Mm := hMmv ▸ hg.2
      have h := DensityFibre.fold_ratio_eq hp0 hm0 (Real.sqrt_nonneg (Mp * Mm))
        (Real.sq_sqrt (mul_nonneg hp0.le hm0.le)).symm
      rw [hT]
      exact le_of_eq h.2
    · have hMp0 : Mp = 0 := by
        rw [hMp]
        unfold hfoldM
        simp only [hg, ↓reduceIte]
      have hMm0 : Mm = 0 := by
        rw [hMm]
        unfold hfoldM
        simp only [hg, ↓reduceIte]
      rw [hMp0, hMm0, mul_zero, zero_div, add_zero, zero_mul, Real.sqrt_zero, mul_zero]
  rw [rchOptVal_eq hnd.1 hnd.2]
  have h1 := two_sqrt_le (le_of_lt hnd.1) (le_of_lt hnd.2) hTpos
  have e : T * (W * Mp + Rp) + (W * Mm + Rm) / T = W * (T * Mp + Mm / T) + (T * Rp + Rm / T) := by
    ring
  have h3 : W * (T * Mp + Mm / T) ≤ W * (2 * Real.sqrt (Mp * Mm)) :=
    mul_le_mul_of_nonneg_left hkey hW
  linarith

end Algebra

section Shared

open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.BlockAnchor Sarkozy.CancellationSteps

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
  (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
    (joinModuli m₀ (paperTail L) j))
  (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
  (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
  (hne : ∀ β, ∃ i, blk i = β) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)

/-- `envMeansBase` puts the paper's `r₂` in the slot read by `hdiffL` and by `hr2L`. -/
theorem envMeansBase_r2L (hL : RchSumEnvL hcop D hpair dec c₂)
    (hR : RchSumEnvR hcop D hpair dec c₂) :
    (envMeansBase hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).r2L = r2EnvL hcop D hpair dec ∧
      (envMeansBase hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).r2R =
        r2EnvR hcop D hpair dec ∧
      (envMeansBase hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).z = zBase D :=
  ⟨rfl, rfl, rfl⟩

/-- `fixMeansBase` puts the paper's `r₂` in the slot read by `hdiffL/R` and by `hr2L/R`. -/
theorem fixMeansBase_r2 (hL : RchSumFixL hcop D hpair dec c₂)
    (hR : RchSumFixR hcop D hpair dec c₂) :
    (fixMeansBase hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).r2L = r2FixL hcop D hpair dec ∧
      (fixMeansBase hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).r2R =
        r2FixR hcop D hpair dec ∧
      (fixMeansBase hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).z = zBase D :=
  ⟨rfl, rfl, rfl⟩

/-- **The same `r₂` reaches B9's bundle** (`hdiffL/R` and the mean bounds `hmL/R`, K2's fields
30–31, read by the endgame): TH's `toEnvMeansInputs` keeps `r2L`, `r2R`, `z`. -/
theorem envMeansBase_toB9 (hL : RchSumEnvL hcop D hpair dec c₂)
    (hR : RchSumEnvR hcop D hpair dec c₂) :
    ((envMeansBase hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).toEnvMeansInputs ha hpar hne
        hsel).r2L = r2EnvL hcop D hpair dec ∧
      ((envMeansBase hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).toEnvMeansInputs ha hpar hne
        hsel).r2R = r2EnvR hcop D hpair dec ∧
      ((envMeansBase hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).toEnvMeansInputs ha hpar hne
        hsel).z = zBase D :=
  ⟨rfl, rfl, rfl⟩

/-- **The same `r₂` reaches B9's bundle for `fixC`** (`toFixMeansInputs`). -/
theorem fixMeansBase_toB9 (hL : RchSumFixL hcop D hpair dec c₂)
    (hR : RchSumFixR hcop D hpair dec c₂) :
    ((fixMeansBase hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).toFixMeansInputs ha hpar hne
        hsel).r2L = r2FixL hcop D hpair dec ∧
      ((fixMeansBase hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).toFixMeansInputs ha hpar hne
        hsel).r2R = r2FixR hcop D hpair dec ∧
      ((fixMeansBase hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).toFixMeansInputs ha hpar hne
        hsel).z = zBase D :=
  ⟨rfl, rfl, rfl⟩

end Shared

end Sarkozy.SharpBase
