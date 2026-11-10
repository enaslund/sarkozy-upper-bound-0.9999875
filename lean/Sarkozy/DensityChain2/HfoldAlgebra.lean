module

public import Sarkozy.DensityChain2.FoldedPieces

@[expose] public section

/-!
# The algebra of one choice of DC2's `hfold`: `t`, `M_±`, `r_±`

DC2's `hfold` asks, for one choice `σ` and tag `j`: `t > 0`, `M_±`, `r_±` with
`t M₊ + M₋/t ≤ 2(1 + ε)ΛK`, `𝔈_±(φ) ≤ (∏ bpieceG(φ)) M_± + r_±(φ)` at every admissible piece, and
`(t ∑ w r₊ + (∑ w r₋)/t)/2 ≤ rch`. Here the witnesses are explicit functions of the per-piece data:

* the main prices `M_± = K₀ P_±` when both are positive (`good`), else `0`;
* `r_±(φ) = G_±(φ) C_r + bpieceG(φ)(K₀ P_± − M_±)` at the pieces where the chain applies
  (`small φ`), and `|𝔈_±(φ)|` at the others (`lem:record:density-lp` sums these);
* `t = √(M₋/M₊)` when `good` (DC2's `fold_ratio_eq`), else the optimal ratio of the remainder
  sums.

`hfold_choice` proves the four conditions from the per-piece chain bounds and
`P₊ P₋ = Π_∅²`, `2 K₀ Π_∅ ≤ R`. The value `rchVal` is then an explicit `rch`.
When `good` fails (a query of one half has zero local density), the whole main term of the other
fold is a remainder, and only `√(∑ w r₊ ∑ w r₋)` reaches `rch`.
-/

namespace Sarkozy.DensityChain2

open Finset
open scoped BigOperators

variable {Φ : Type} [Fintype Φ]

/-- The good case: both folded main prices positive. -/
def HfoldGood (K₀ Pp Pm : ℝ) : Prop := 0 < K₀ * Pp ∧ 0 < K₀ * Pm

open Classical in
/-- The main prices `M_±`. -/
noncomputable def hfoldM (K₀ Pp Pm P : ℝ) : ℝ := if HfoldGood K₀ Pp Pm then K₀ * P else 0

open Classical in
/-- The remainders `r_±(φ)`. -/
noncomputable def hfoldR (small : Φ → Prop) (K₀ Pp Pm P Cr : ℝ) (BG G F : Φ → ℝ) (φ : Φ) : ℝ :=
  if small φ then G φ * Cr + BG φ * (K₀ * P - hfoldM K₀ Pp Pm P) else |F φ|

open Classical in
/-- The ratio `t`. -/
noncomputable def hfoldT (small : Φ → Prop) (K₀ Pp Pm Cr : ℝ) (w BG Gp Gm Fp Fm : Φ → ℝ) : ℝ :=
  if HfoldGood K₀ Pp Pm then Real.sqrt (hfoldM K₀ Pp Pm Pm / hfoldM K₀ Pp Pm Pp)
  else
    let Rp := ∑ φ, w φ * hfoldR small K₀ Pp Pm Pp Cr BG Gp Fp φ
    let Rm := ∑ φ, w φ * hfoldR small K₀ Pp Pm Pm Cr BG Gm Fm φ
    if 0 < Rp ∧ 0 < Rm then Real.sqrt (Rm / Rp) else 1

/-- The explicit `rch` of one choice and tag. -/
noncomputable def rchVal (small : Φ → Prop) (K₀ Pp Pm Cr : ℝ) (w BG Gp Gm Fp Fm : Φ → ℝ) : ℝ :=
  (hfoldT small K₀ Pp Pm Cr w BG Gp Gm Fp Fm *
      ∑ φ, w φ * hfoldR small K₀ Pp Pm Pp Cr BG Gp Fp φ +
    (∑ φ, w φ * hfoldR small K₀ Pp Pm Pm Cr BG Gm Fm φ) /
      hfoldT small K₀ Pp Pm Cr w BG Gp Gm Fp Fm) / 2

theorem hfoldT_pos (small : Φ → Prop) (K₀ Pp Pm Cr : ℝ) (w BG Gp Gm Fp Fm : Φ → ℝ) :
    0 < hfoldT small K₀ Pp Pm Cr w BG Gp Gm Fp Fm := by
  unfold hfoldT
  by_cases hg : HfoldGood K₀ Pp Pm
  · simp only [hg, ↓reduceIte]
    obtain ⟨hp, hm⟩ := hg
    unfold hfoldM
    simp only [HfoldGood, hp, hm, and_self, ↓reduceIte]
    exact Real.sqrt_pos.mpr (div_pos hm hp)
  · simp only [hg, ↓reduceIte]
    split_ifs with h2
    · exact Real.sqrt_pos.mpr (div_pos h2.2 h2.1)
    · exact zero_lt_one

/-- **One choice of `hfold`.** -/
theorem hfold_choice (small adm : Φ → Prop) {K₀ Pp Pm P0 Cr R : ℝ} (hK₀ : 0 ≤ K₀)
    (hPp : 0 ≤ Pp) (hPm : 0 ≤ Pm) (hP0 : 0 ≤ P0) (hprod : Pp * Pm = P0 ^ 2)
    (hR : 2 * (K₀ * P0) ≤ R) (hR0 : 0 ≤ R)
    (w BG Gp Gm Fp Fm : Φ → ℝ) (hBG : ∀ φ, 0 ≤ BG φ)
    (hp : ∀ φ, adm φ → small φ → Fp φ ≤ BG φ * (K₀ * Pp) + Gp φ * Cr)
    (hm : ∀ φ, adm φ → small φ → Fm φ ≤ BG φ * (K₀ * Pm) + Gm φ * Cr) :
    0 < hfoldT small K₀ Pp Pm Cr w BG Gp Gm Fp Fm ∧
      hfoldT small K₀ Pp Pm Cr w BG Gp Gm Fp Fm * hfoldM K₀ Pp Pm Pp +
          hfoldM K₀ Pp Pm Pm / hfoldT small K₀ Pp Pm Cr w BG Gp Gm Fp Fm ≤ R ∧
      (∀ φ, adm φ → Fp φ ≤ BG φ * hfoldM K₀ Pp Pm Pp + hfoldR small K₀ Pp Pm Pp Cr BG Gp Fp φ) ∧
      (∀ φ, adm φ → Fm φ ≤ BG φ * hfoldM K₀ Pp Pm Pm + hfoldR small K₀ Pp Pm Pm Cr BG Gm Fm φ) ∧
      (hfoldT small K₀ Pp Pm Cr w BG Gp Gm Fp Fm *
          ∑ φ, w φ * hfoldR small K₀ Pp Pm Pp Cr BG Gp Fp φ +
        (∑ φ, w φ * hfoldR small K₀ Pp Pm Pm Cr BG Gm Fm φ) /
          hfoldT small K₀ Pp Pm Cr w BG Gp Gm Fp Fm) / 2 ≤
        rchVal small K₀ Pp Pm Cr w BG Gp Gm Fp Fm := by
  classical
  have hMnn : ∀ P, 0 ≤ P → 0 ≤ hfoldM K₀ Pp Pm P := fun P hP => by
    unfold hfoldM
    split_ifs
    · exact mul_nonneg hK₀ hP
    · exact le_refl 0
  refine ⟨hfoldT_pos _ _ _ _ _ _ _ _ _ _ _, ?_, ?_, ?_, le_refl _⟩
  · by_cases hg : HfoldGood K₀ Pp Pm
    · have hMp : hfoldM K₀ Pp Pm Pp = K₀ * Pp := by unfold hfoldM; simp only [hg, ↓reduceIte]
      have hMm : hfoldM K₀ Pp Pm Pm = K₀ * Pm := by unfold hfoldM; simp only [hg, ↓reduceIte]
      have hT : hfoldT small K₀ Pp Pm Cr w BG Gp Gm Fp Fm = Real.sqrt (K₀ * Pm / (K₀ * Pp)) := by
        unfold hfoldT
        simp only [hg, ↓reduceIte, hMp, hMm]
      rw [hT, hMp, hMm]
      have h := DensityFibre.fold_ratio_eq hg.1 hg.2 (mul_nonneg hK₀ hP0)
        (by rw [mul_pow, ← hprod]; ring)
      rw [h.2]
      exact hR
    · have hMp : hfoldM K₀ Pp Pm Pp = 0 := by unfold hfoldM; simp only [hg, ↓reduceIte]
      have hMm : hfoldM K₀ Pp Pm Pm = 0 := by unfold hfoldM; simp only [hg, ↓reduceIte]
      rw [hMp, hMm, mul_zero, zero_div, add_zero]
      exact hR0
  · intro φ hφ
    unfold hfoldR
    split_ifs with hs
    · have := hp φ hφ hs
      linarith
    · have h1 : 0 ≤ BG φ * hfoldM K₀ Pp Pm Pp := mul_nonneg (hBG φ) (hMnn Pp hPp)
      linarith [le_abs_self (Fp φ)]
  · intro φ hφ
    unfold hfoldR
    split_ifs with hs
    · have := hm φ hφ hs
      linarith
    · have h1 : 0 ≤ BG φ * hfoldM K₀ Pp Pm Pm := mul_nonneg (hBG φ) (hMnn Pm hPm)
      linarith [le_abs_self (Fm φ)]


omit [Fintype Φ] in
/-- The explicit remainders are nonnegative. -/
theorem hfoldR_nonneg (small : Φ → Prop) {K₀ Pp Pm P Cr : ℝ} (hK₀ : 0 ≤ K₀) (hP : 0 ≤ P)
    (hCr : 0 ≤ Cr) (BG G F : Φ → ℝ) (hBG : ∀ φ, 0 ≤ BG φ) (hG : ∀ φ, 0 ≤ G φ) (φ : Φ) :
    0 ≤ hfoldR small K₀ Pp Pm P Cr BG G F φ := by
  classical
  unfold hfoldR
  split_ifs
  · refine add_nonneg (mul_nonneg (hG φ) hCr) (mul_nonneg (hBG φ) ?_)
    unfold hfoldM
    split_ifs with hg
    · rw [sub_self]
    · rw [sub_zero]
      exact mul_nonneg hK₀ hP
  · exact abs_nonneg _

/-- **`rchVal ≥ 0`**, so a sum of `rchVal` over the tags dominates each of them. -/
theorem rchVal_nonneg (small : Φ → Prop) {K₀ Pp Pm Cr : ℝ} (hK₀ : 0 ≤ K₀) (hPp : 0 ≤ Pp)
    (hPm : 0 ≤ Pm) (hCr : 0 ≤ Cr) (w BG Gp Gm Fp Fm : Φ → ℝ) (hw : ∀ φ, 0 ≤ w φ)
    (hBG : ∀ φ, 0 ≤ BG φ) (hGp : ∀ φ, 0 ≤ Gp φ) (hGm : ∀ φ, 0 ≤ Gm φ) :
    0 ≤ rchVal small K₀ Pp Pm Cr w BG Gp Gm Fp Fm := by
  unfold rchVal
  have ht := hfoldT_pos small K₀ Pp Pm Cr w BG Gp Gm Fp Fm
  have h1 : 0 ≤ ∑ φ, w φ * hfoldR small K₀ Pp Pm Pp Cr BG Gp Fp φ := sum_nonneg fun φ _ =>
    mul_nonneg (hw φ) (hfoldR_nonneg small hK₀ hPp hCr BG Gp Fp hBG hGp φ)
  have h2 : 0 ≤ ∑ φ, w φ * hfoldR small K₀ Pp Pm Pm Cr BG Gm Fm φ := sum_nonneg fun φ _ =>
    mul_nonneg (hw φ) (hfoldR_nonneg small hK₀ hPm hCr BG Gm Fm hBG hGm φ)
  positivity

end Sarkozy.DensityChain2
