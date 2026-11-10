module

public import Sarkozy.SpectralD.TailErrorBounds
public import Sarkozy.SpectralOne.Rfull

/-!
# Uniform count ratios in the root tail range

All count errors with degree at most 24 and at most 72 vertices are below
2^(-50) at p ≥ 2^512. Products of at most 72 corresponding density ratios
are within 2^(-40) of one.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.SpectralOne

theorem coarseError_eq_coarseErr {q : ℝ} (hq : 0 ≤ q) (t n : ℕ) :
    coarseError t q n = TraceMixing.coarseErr q t n := by
  simp only [coarseError, coarseH, TraceMixing.coarseErr, inv_pow,
    Real.sq_sqrt hq, div_eq_mul_inv, one_mul]

theorem coarseError_tail {p t n : ℕ} (hp : 2 ^ 512 ≤ p) (ht : t ≤ 24) (hn : n ≤ 72) :
    coarseError t p n ≤ (2 : ℝ)⁻¹ ^ 50 := by
  have hq : (2 : ℝ) ^ 256 ≤ p := by exact_mod_cast (show 2 ^ 256 ≤ p by omega)
  calc coarseError t p n ≤ coarseError 24 p n := coarseError_mono (by positivity) ht
    _ ≤ coarseError 24 p 72 := coverRow_coarseError_mono_n _ (by exact_mod_cast hn)
    _ ≤ coarseError 24 ((2 : ℝ) ^ 256) 72 :=
        collision_coarseError_anti 24 (by norm_num) (by positivity) hq
    _ ≤ (2 : ℝ)⁻¹ ^ 50 := by
        unfold coarseError
        rw [show 256 = 128 * 2 by rfl, pow_mul, Real.sqrt_sq (by positivity)]
        norm_num [coarseH]

theorem coarseErr_tail {p t n : ℕ} (hp : 2 ^ 512 ≤ p) (ht : t ≤ 24) (hn : n ≤ 72) :
    TraceMixing.coarseErr p t n ≤ (2 : ℝ)⁻¹ ^ 50 := by
  rw [← coarseError_eq_coarseErr (Nat.cast_nonneg p)]
  exact coarseError_tail hp ht hn

theorem tail_ratio_le {e : ℝ} (he : e ≤ 2⁻¹ ^ 50) :
    (1 + e) / (1 - e) ≤ 1 + 2⁻¹ ^ 48 := by
  rw [div_le_iff₀ (by norm_num at he ⊢; linarith)]
  norm_num at he ⊢
  linarith

theorem tail_ratio_power : ((1 : ℝ) + 2⁻¹ ^ 48) ^ 72 ≤ 1 + 2⁻¹ ^ 40 := by
  norm_num

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W]

theorem Rcut_tail (D : Cuts.SpecData W) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card D.cut.Half ≤ 72) (ht : ∀ i, D.tdeg i ≤ 24) :
    D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) ≤ 1 + 2⁻¹ ^ 40 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have he : ∀ i, TraceMixing.coarseErr p (D.tdeg i) 72 ≤ (2 : ℝ)⁻¹ ^ 50 :=
    fun i => coarseErr_tail hp (ht i) le_rfl
  have hcard : D.cut.half.card ≤ 72 := by simpa only [Fintype.card_coe] using hn
  unfold Cuts.SpecData.Rcut
  simp only [ZMod.card]
  calc _ ≤ ∏ _i : Fin D.cut.half.card, ((1 : ℝ) + 2⁻¹ ^ 48) :=
        prod_le_prod₀ (fun i _ => div_nonneg
          (by linarith [TraceMixing.coarseErr_nonneg hp0 (D.tdeg i) 72])
          (by have := he i; norm_num at this ⊢; linarith)) (fun i _ => tail_ratio_le (he i))
    _ = ((1 : ℝ) + 2⁻¹ ^ 48) ^ D.cut.half.card := by simp only [prod_const, card_univ,
        Fintype.card_fin]
    _ ≤ ((1 : ℝ) + 2⁻¹ ^ 48) ^ 72 := pow_le_pow_right₀ (by norm_num) hcard
    _ ≤ 1 + 2⁻¹ ^ 40 := tail_ratio_power

theorem Rprime_tail (D : Cuts.SpecData W) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card W ≤ 72)
    (hd : ∀ v, nbrCount D.G (univ.erase v) v ≤ 20) (i : D.cut.Half) :
    Cx.Rprime p D 72 (Cx.restList D) i ≤ 1 + 2⁻¹ ^ 40 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have he : TraceMixing.coarseErr p 20 72 < 1 :=
    lt_of_le_of_lt (coarseErr_tail hp (by norm_num) le_rfl) (by norm_num)
  have hd' : ∀ (A : Finset W) v, nbrCount D.G A v ≤ 20 :=
    fun A v => (nbrCount_le_deg D.G A v).trans (hd v)
  have hL := lowerProd_pos_of D.G hp1 72 (fun _ => 20) hd' (fun _ => he)
    (Cx.restList D i) (Cx.fixSet D i)
  have hU := upperProd_le_mul_lowerProd D.G hp1 72 (fun _ => 20) hd' (fun _ => he)
    (Cx.restList D i) (Cx.fixSet D i)
  simp only [List.map_const', List.prod_replicate] at hU
  have hlen : (Cx.restList D i).length ≤ 72 := by
    unfold Cx.restList
    simpa only [length_toList, card_univ] using
      (card_filter_le (s := univ) (p := fun w => w ∉ Cx.fixSet D i)).trans hn
  have hR0 : 0 ≤ ratioE p 72 20 := zero_le_one.trans (one_le_ratioE hp0 he)
  have hR : ratioE p 72 20 ≤ 1 + (2 : ℝ)⁻¹ ^ 48 :=
    tail_ratio_le (coarseErr_tail hp (by norm_num) le_rfl)
  unfold Cx.Rprime
  rw [ZMod.card]
  apply max_le (by norm_num)
  calc _ ≤ ratioE p 72 20 ^ (Cx.restList D i).length := (div_le_iff₀ hL).mpr hU
    _ ≤ ((1 : ℝ) + 2⁻¹ ^ 48) ^ (Cx.restList D i).length := pow_le_pow_left₀ hR0 hR _
    _ ≤ ((1 : ℝ) + 2⁻¹ ^ 48) ^ 72 := pow_le_pow_right₀ (by norm_num) hlen
    _ ≤ 1 + 2⁻¹ ^ 40 := tail_ratio_power

end Sarkozy.SpectralD
