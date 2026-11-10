module

public import Sarkozy.SpectralD.TailCounts
public import Sarkozy.SpectralD.CxSmallCut

/-!
# The small-pair matrices in the root tail range

The count-error bounds give uniform row bounds for the explicit matrices
mXcut and mVcut used by the degree-one part of the spectral criterion.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.Labellings

theorem smallConst_tail {p d n : ℕ} (hp : 2 ^ 512 ≤ p) (hd : d ≤ 20) (hn : n ≤ 72) :
    Cx.smallConst p d n ≤ (2 : ℝ)⁻¹ ^ 48 := by
  have h0 := coarseErr_tail hp (by omega : d ≤ 24) hn
  have h1 := coarseErr_tail hp (by omega : d + 1 ≤ 24) hn
  unfold Cx.smallConst
  rw [div_le_iff₀ (by norm_num at h0 ⊢; linarith)]
  norm_num at h0 h1 ⊢
  linarith

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W]

theorem mXcut_tail (D : Cuts.SpecData W) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card W ≤ 72) (hd : ∀ v, nbrCount D.G (univ.erase v) v ≤ 20)
    (k l : D.cut.Half) : Cx.mXcut p D k l ≤ (2 : ℝ)⁻¹ ^ 48 := by
  unfold Cx.mXcut
  split_ifs
  · exact (min_le_left _ _).trans (smallConst_tail hp (hd _) hn)
  · positivity

omit [Fact p.Prime] in
theorem mVcut_tail (D : Cuts.SpecData W) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card D.cut.Half ≤ 72)
    (hd : ∀ k, nbrCount D.halfGraph (univ.erase k) k ≤ 20)
    (k l : D.cut.Half) : Cx.mVcut p D k l ≤ 1 := by
  unfold Cx.mVcut
  split_ifs
  · norm_num
  · rfl
  · exact ((min_le_left _ _).trans (smallConst_tail hp (hd _) hn)).trans (by norm_num)

theorem small_rowX_tail (D : Cuts.SpecData W) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card W ≤ 72) (hhalf : Fintype.card D.cut.Half = 36)
    (hd : ∀ v, nbrCount D.G (univ.erase v) v ≤ 20) (k : D.cut.Half) :
    ∑ l, (if Cx.sgnZ (p := p) D k l = 0 then Cx.mXcut p D k l else 0) ≤ (2 : ℝ)⁻¹ ^ 40 := by
  calc _ ≤ ∑ _l : D.cut.Half, (2 : ℝ)⁻¹ ^ 48 := sum_le_sum fun l _ => by
        split_ifs
        · exact mXcut_tail D hp hn hd k l
        · positivity
    _ = 36 * (2 : ℝ)⁻¹ ^ 48 := by
        simp only [sum_const, card_univ, hhalf, nsmul_eq_mul, Nat.cast_ofNat]
    _ ≤ (2 : ℝ)⁻¹ ^ 40 := by norm_num

omit [Fact p.Prime] in
theorem small_rowV_tail (D : Cuts.SpecData W) (hp : 2 ^ 512 ≤ p)
    (hhalf : Fintype.card D.cut.Half = 36)
    (hd : ∀ k, nbrCount D.halfGraph (univ.erase k) k ≤ 20) (k : D.cut.Half) :
    ∑ l, (if k = l then 0 else Cx.mVcut p D k l) ≤ 36 := by
  calc _ ≤ ∑ _l : D.cut.Half, (1 : ℝ) := sum_le_sum fun l _ => by
        split_ifs
        · norm_num
        · exact mVcut_tail D hp (by omega) hd k l
    _ = 36 := by simp only [sum_const, card_univ, hhalf, nsmul_eq_mul, Nat.cast_ofNat, mul_one]

end Sarkozy.SpectralD
