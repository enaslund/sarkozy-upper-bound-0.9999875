module

public import Sarkozy.SpectralD.TailCounts
public import Sarkozy.SpectralOne.Transfer

/-!
# Stronger density estimates for the class-one Paley term

The non-coverable-set allowance includes up to 2^36 supports. The stronger
count error 2^(-100) and density error 2^(-90) retain ample room for that sum.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.Extraction Sarkozy.SpectralOne

theorem coarseErr_tail_strong {p t n : ℕ} (hp : 2 ^ 512 ≤ p) (ht : t ≤ 24) (hn : n ≤ 72) :
    TraceMixing.coarseErr p t n ≤ (2 : ℝ)⁻¹ ^ 100 := by
  have hq : (2 : ℝ) ^ 256 ≤ p := by exact_mod_cast (show 2 ^ 256 ≤ p by omega)
  rw [← coarseError_eq_coarseErr (Nat.cast_nonneg p)]
  calc coarseError t p n ≤ coarseError 24 p n := coarseError_mono (by positivity) ht
    _ ≤ coarseError 24 p 72 := coverRow_coarseError_mono_n _ (by exact_mod_cast hn)
    _ ≤ coarseError 24 ((2 : ℝ) ^ 256) 72 :=
        collision_coarseError_anti 24 (by norm_num) (by positivity) hq
    _ ≤ (2 : ℝ)⁻¹ ^ 100 := by
        unfold coarseError
        rw [show 256 = 128 * 2 by rfl, pow_mul, Real.sqrt_sq (by positivity)]
        norm_num [coarseH]

theorem tail_ratio_strong {e : ℝ} (he : e ≤ 2⁻¹ ^ 100) :
    (1 + e) / (1 - e) ≤ 1 + 2⁻¹ ^ 98 := by
  rw [div_le_iff₀ (by norm_num at he ⊢; linarith)]
  norm_num at he ⊢
  linarith

theorem tail_count_product {U : Type*} [Fintype U] (e : U → ℝ)
    (hn : Fintype.card U ≤ 72) (he0 : ∀ i, 0 ≤ e i) (he : ∀ i, e i ≤ 2⁻¹ ^ 100) :
    ∏ i, (1 + e i) / (1 - e i) ≤ 1 + 2⁻¹ ^ 90 := by
  calc _ ≤ ∏ _i : U, ((1 : ℝ) + 2⁻¹ ^ 98) :=
        prod_le_prod₀ (fun i _ => div_nonneg (by linarith [he0 i])
          (by have := he i; norm_num at this ⊢; linarith)) (fun i _ => tail_ratio_strong (he i))
    _ = ((1 : ℝ) + 2⁻¹ ^ 98) ^ Fintype.card U := by simp only [prod_const, card_univ]
    _ ≤ ((1 : ℝ) + 2⁻¹ ^ 98) ^ 72 := pow_le_pow_right₀ (by norm_num) hn
    _ ≤ 1 + 2⁻¹ ^ 90 := by norm_num

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W]

theorem Rcut_tail_strong (D : Cuts.SpecData W) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card D.cut.Half ≤ 72) (ht : ∀ i, D.tdeg i ≤ 24) :
    D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) ≤ 1 + 2⁻¹ ^ 90 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold Cuts.SpecData.Rcut
  simp only [ZMod.card]
  exact tail_count_product _ (by simpa only [Fintype.card_fin, Fintype.card_coe] using hn)
    (fun _ => TraceMixing.coarseErr_nonneg hp0 _ _)
    (fun i => coarseErr_tail_strong hp (ht i) le_rfl)

theorem Rfull_tail_strong (D : Cuts.SpecData W) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card D.cut.Half ≤ 72)
    (hd : ∀ j, Labellings.nbrCount D.halfGraph (univ.erase j) j ≤ 24) :
    RfullPaper (p := p) D (Fintype.card D.cut.Half) ≤ 1 + 2⁻¹ ^ 90 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold RfullPaper ratioE
  exact tail_count_product _ hn (fun _ => TraceMixing.coarseErr_nonneg hp0 _ _)
    (fun i => coarseErr_tail_strong hp (hd i) hn)

end Sarkozy.SpectralD
