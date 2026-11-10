module

public import Sarkozy.SpectralD.TailStrongCounts

/-!
# The class-one non-coverable-set allowance at tail primes

The count-based Paley allowance is at most 2^(-80). Even the crude count
of all subsets of a 36-vertex half leaves its contribution below 2^(-38).
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.SpectralC Sarkozy.SpectralOne

theorem tail_shift_quotient {p n : ℕ} (hp : 2 ^ 512 ≤ p) (hn : n ≤ 72) :
    1 / (((p : ℝ) - n) * (Real.sqrt p)⁻¹) ≤ 2 * (Real.sqrt p)⁻¹ := by
  have hp144 : (144 : ℝ) ≤ p := by exact_mod_cast (show 144 ≤ p by omega)
  have hn72 : (n : ℝ) ≤ 72 := by exact_mod_cast hn
  have hp0 : (0 : ℝ) < p := by linarith
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hs : (p : ℝ) * (Real.sqrt p)⁻¹ = Real.sqrt p := by
    rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hs0.ne', Real.mul_self_sqrt hp0.le]
  have hratio : (p : ℝ) / (p - n) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  calc _ = ((p : ℝ) - n)⁻¹ * Real.sqrt p := by rw [one_div, mul_inv, inv_inv]
    _ = ((p : ℝ) - n)⁻¹ * ((p : ℝ) * (Real.sqrt p)⁻¹) :=
        congrArg (fun t => ((p : ℝ) - n)⁻¹ * t) hs.symm
    _ = (p : ℝ) / (p - n) * (Real.sqrt p)⁻¹ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio (by positivity)

theorem tail_zeta_scalar {p : ℕ} (hp : 2 ^ 512 ≤ p) {R F : ℝ}
    (hF0 : 0 ≤ F) (hR : R ≤ 1 + 2⁻¹ ^ 90) (hF : F ≤ 1 + 2⁻¹ ^ 90) :
    (R * F - 1) + 36 / (((p : ℝ) - 36) * (Real.sqrt p)⁻¹) ≤ 2⁻¹ ^ 80 := by
  have hprod := mul_le_mul hR hF hF0 (by positivity)
  have hq : 36 / (((p : ℝ) - 36) * (Real.sqrt p)⁻¹) ≤ 72 * (2 : ℝ)⁻¹ ^ 256 := by
    calc _ = 36 * (1 / (((p : ℝ) - 36) * (Real.sqrt p)⁻¹)) := by ring
      _ ≤ 36 * (2 * (Real.sqrt p)⁻¹) :=
          mul_le_mul_of_nonneg_left (tail_shift_quotient hp (n := 36) (by norm_num)) (by norm_num)
      _ = 72 * (Real.sqrt p)⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (tail_rp_le hp) (by norm_num)
  exact (add_le_add (sub_le_sub_right hprod 1) hq).trans (by norm_num)

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W]

theorem zeta_tail (D : Cuts.SpecData W) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card D.cut.Half = 36) (ht : ∀ i, D.tdeg i ≤ 24)
    (hd : ∀ j, Labellings.nbrCount D.halfGraph (univ.erase j) j ≤ 24) :
    (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) *
      RfullPaper (p := p) D (Fintype.card D.cut.Half) - 1) +
      (Fintype.card D.cut.Half : ℝ) /
        (((p : ℝ) - Fintype.card D.cut.Half) * rp p) ≤ 2⁻¹ ^ 80 := by
  have hF1 : 1 ≤ RfullPaper (p := p) D (Fintype.card D.cut.Half) := by
    apply one_le_RfullPaper D
    intro j
    exact lt_of_le_of_lt (coarseErr_tail hp (hd j) (by omega)) (by norm_num)
  have h := tail_zeta_scalar hp (zero_le_one.trans hF1)
    (Rcut_tail_strong D hp (by omega) ht) (Rfull_tail_strong D hp (by omega) hd)
  simpa only [hn, Nat.cast_ofNat, rp] using h

section Sets

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem noncoverable_count (Adj : U → U → Prop) [DecidableRel Adj]
    (hn : Fintype.card U = 36) : (PaleyB.ncSets Adj).card * Fintype.card U ≤ 2 ^ 42 := by
  have h : (PaleyB.ncSets Adj).card ≤ 2 ^ 36 := by
    unfold PaleyB.ncSets
    calc _ ≤ (univ : Finset (Finset U)).card := (card_filter_le _ _).trans (card_filter_le _ _)
      _ = 2 ^ 36 := by simp only [card_univ, Fintype.card_finset, hn]
  rw [hn]
  exact (Nat.mul_le_mul_right 36 h).trans (by norm_num)

theorem parity_term_tail (Adj : U → U → Prop) [DecidableRel Adj]
    (hn : Fintype.card U = 36) {ζ : ℝ} (hζ : ζ ≤ 2⁻¹ ^ 80) :
    ζ * ((PaleyB.ncSets Adj).card * Fintype.card U : ℝ) ≤ 2⁻¹ ^ 38 := by
  have hc : ((PaleyB.ncSets Adj).card * Fintype.card U : ℝ) ≤ (2 : ℝ) ^ 42 := by
    exact_mod_cast noncoverable_count Adj hn
  exact (mul_le_mul hζ hc (by positivity) (by positivity)).trans (by norm_num)

end Sets

end Sarkozy.SpectralD
