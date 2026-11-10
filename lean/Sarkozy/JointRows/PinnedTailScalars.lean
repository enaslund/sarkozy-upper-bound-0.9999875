module

public import Sarkozy.ExtractionK.PinnedExtraction
public import Sarkozy.SpectralD.TailErrorBounds

/-! Coarse scalar estimates for singleton extraction in pinned tail rows. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.PinTail

open Finset Sarkozy.Extraction Sarkozy.ExtractionK

variable {p n z : ℕ}

theorem count_error (hp : 2 ^ 512 ≤ p) (hn : n ≤ 12) (hz : z ≤ 12) :
    ePin p n z 4 ≤ 1 / 4 := by
  have hr := SpectralD.tail_rp_le hp
  have hnR : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  have hzR : (z : ℝ) ≤ 12 := by exact_mod_cast hz
  unfold ePin
  norm_num only [Nat.cast_ofNat]
  calc
    _ ≤ 16 * ((2 * 12 + 12) * (((2 : ℝ)⁻¹ ^ 256) ^ 2) + 4 / 2 * (2 : ℝ)⁻¹ ^ 256) := by
      gcongr
      norm_num
    _ ≤ _ := by norm_num

theorem density_error (hp : 2 ^ 512 ≤ p) (hn : n ≤ 12) {d : ℕ} (hd : d ≤ 4) :
    (Real.sqrt p)⁻¹ ^ 2 * n * 2 ^ d ≤ 1 / 4 := by
  have hr := SpectralD.tail_rp_le hp
  have hnR : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  calc
    _ ≤ (((2 : ℝ)⁻¹ ^ 256) ^ 2) * 12 * 2 ^ 4 := by gcongr; norm_num
    _ ≤ _ := by norm_num

theorem vertex_factor (hp : 2 ^ 512 ≤ p) (hn : n ≤ 12) (hz : z ≤ 12)
    {d : ℕ} (hd : d ≤ 4) : peF p n z 4 d 0 ≤ 4 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have he := count_error hp hn hz
  have hed := (ePin_mono (p : ℝ) n z hd).trans he
  have h := peF_le hp0 (he.trans_lt (by norm_num)) d 0
  simp only [add_zero] at h
  apply h.trans
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - ePin p n z 4)]
  linarith [density_error hp hn hd]

variable [Fact p.Prime]

theorem empty_factor (hp : 2 ^ 512 ≤ p) (hn : n ≤ 12) (hz : z ≤ 12)
    (pin : Fin n → ZMod p → ℤ) (hpin : ∀ i, pinCount pin i ≤ 4)
    (V W : Finset (Fin n)) :
    peFactor p n z 4 pin ∅ V W (univ \ V) (univ \ W) ≤ 2 ^ 48 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have he : ePin p n z 4 < 1 := (count_error hp hn hz).trans_lt (by norm_num)
  have hprod (C : Finset (Fin n)) : ∏ i ∈ C, peF p n z 4 (pinCount pin i) 0 ≤ 4 ^ 12 := by
    calc
      _ ≤ ∏ _i ∈ C, (4 : ℝ) :=
        prod_le_prod₀ (fun i _ => peF_nonneg hp0 he _ 0)
          (fun i _ => vertex_factor hp hn hz (hpin i))
      _ = (4 : ℝ) ^ C.card := by rw [prod_const]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num)
        ((card_le_univ C).trans (by simpa only [Fintype.card_fin] using hn))
  have hcomp (C : Finset (Fin n)) : C ∪ (univ \ C) = univ := by
    ext i
    simp
  simp only [peFactor, hcomp, sdiff_self]
  simp only [intH, peColH, notMem_empty, Finset.filter_false, card_empty]
  simp only [bot_eq_empty, prod_empty, one_mul, mul_one]
  change (∏ i ∈ univ \ W, peF p n z 4 (pinCount pin i) 0) *
    (∏ i ∈ univ \ V, peF p n z 4 (pinCount pin i) 0) ≤ 2 ^ 48
  have h := mul_le_mul (hprod (univ \ W)) (hprod (univ \ V))
    (prod_nonneg fun i _ => peF_nonneg hp0 he _ 0) (by positivity : (0 : ℝ) ≤ 4 ^ 12)
  exact h.trans (by norm_num)

end Sarkozy.JointRows.PinTail
