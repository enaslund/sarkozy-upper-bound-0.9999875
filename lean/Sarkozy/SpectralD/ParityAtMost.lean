module

public import Sarkozy.SpectralD.TailParityInputs

/-!
# Parity allowances for halves of size at most thirty-six

The actual non-coverable averages obey the same tail allowance as the
root cuts; the count of subsets is bounded monotonically in the half size.
-/

@[expose] public section

namespace Sarkozy.SpectralD.AtMost

open Finset Sarkozy.SpectralC Sarkozy.SpectralOne Sarkozy.Labellings

theorem tail_zeta_scalar {p n : ℕ} (hp : 2 ^ 512 ≤ p) (hn : n ≤ 36) {R F : ℝ}
    (hF0 : 0 ≤ F) (hR : R ≤ 1 + 2⁻¹ ^ 90) (hF : F ≤ 1 + 2⁻¹ ^ 90) :
    (R * F - 1) + n / (((p : ℝ) - n) * (Real.sqrt p)⁻¹) ≤ 2⁻¹ ^ 80 := by
  have hprod := mul_le_mul hR hF hF0 (by positivity)
  have hnR : (n : ℝ) ≤ 36 := by exact_mod_cast hn
  have hq : n / (((p : ℝ) - n) * (Real.sqrt p)⁻¹) ≤ 72 * (2 : ℝ)⁻¹ ^ 256 := by
    calc _ = n * (1 / (((p : ℝ) - n) * (Real.sqrt p)⁻¹)) := by ring
      _ ≤ n * (2 * (Real.sqrt p)⁻¹) :=
          mul_le_mul_of_nonneg_left (tail_shift_quotient hp (by omega)) (Nat.cast_nonneg n)
      _ ≤ 36 * (2 * (Real.sqrt p)⁻¹) := by gcongr
      _ = 72 * (Real.sqrt p)⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (tail_rp_le hp) (by norm_num)
  exact (add_le_add (sub_le_sub_right hprod 1) hq).trans (by norm_num)

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W]

theorem zeta_tail (D : Cuts.SpecData W) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card D.cut.Half ≤ 36) (ht : ∀ i, D.tdeg i ≤ 24)
    (hd : ∀ j, Labellings.nbrCount D.halfGraph (univ.erase j) j ≤ 24) :
    (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) *
      RfullPaper (p := p) D (Fintype.card D.cut.Half) - 1) +
      (Fintype.card D.cut.Half : ℝ) /
        (((p : ℝ) - Fintype.card D.cut.Half) * rp p) ≤ 2⁻¹ ^ 80 := by
  have hF1 : 1 ≤ RfullPaper (p := p) D (Fintype.card D.cut.Half) := by
    apply one_le_RfullPaper D
    intro j
    exact lt_of_le_of_lt (coarseErr_tail hp (hd j) (by omega)) (by norm_num)
  have h := tail_zeta_scalar hp hn (zero_le_one.trans hF1)
    (Rcut_tail_strong D hp (by omega) ht) (Rfull_tail_strong D hp (by omega) hd)
  simpa only [rp] using h

section Sets

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem noncoverable_count (Adj : U → U → Prop) [DecidableRel Adj]
    (hn : Fintype.card U ≤ 36) : (PaleyB.ncSets Adj).card * Fintype.card U ≤ 2 ^ 42 := by
  have h : (PaleyB.ncSets Adj).card ≤ 2 ^ 36 := by
    unfold PaleyB.ncSets
    calc _ ≤ (univ : Finset (Finset U)).card := (card_filter_le _ _).trans (card_filter_le _ _)
      _ ≤ 2 ^ 36 := by
        simp only [card_univ, Fintype.card_finset]
        exact Nat.pow_le_pow_right (by norm_num) hn
  exact (Nat.mul_le_mul h hn).trans (by norm_num)

theorem parity_term_tail (Adj : U → U → Prop) [DecidableRel Adj]
    (hn : Fintype.card U ≤ 36) {ζ : ℝ} (hζ : ζ ≤ 2⁻¹ ^ 80) :
    ζ * ((PaleyB.ncSets Adj).card * Fintype.card U : ℝ) ≤ 2⁻¹ ^ 38 := by
  have hc : ((PaleyB.ncSets Adj).card * Fintype.card U : ℝ) ≤ (2 : ℝ) ^ 42 := by
    exact_mod_cast noncoverable_count Adj hn
  exact (mul_le_mul hζ hc (by positivity) (by positivity)).trans (by norm_num)

end Sets


theorem noncoverable_tail (D : Cuts.SpecData W) (hW : WeilBound (ZMod p))
    (hp : 2 ^ 512 ≤ p) (hnW : Fintype.card W ≤ 72)
    (hn : Fintype.card D.cut.Half ≤ 36) (ht : ∀ i, D.tdeg i ≤ 24)
    (hd : ∀ j, nbrCount D.halfGraph (univ.erase j) j ≤ 24)
    (hne : (injLabellings (ZMod p) D.G).Nonempty)
    (Adj : D.cut.Half → D.cut.Half → Prop)
    (hAdj : ∀ i j, (i, j) ∈ D.halfGraph.E ∨ (j, i) ∈ D.halfGraph.E → Adj i j)
    (J : Finset D.cut.Half) (hJ : 2 ≤ J.card) (hnc : ¬ PaleyB.Coverable Adj J) :
    ‖PaleyB.tJ (Cx.nuA D hne) J‖ ≤ 2⁻¹ ^ 80 * rp p := by
  have he1 : ∀ i, TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) 72 < 1 := by
    intro i
    rw [ZMod.card]
    exact (coarseErr_tail hp (ht i) le_rfl).trans_lt (by norm_num)
  have he : ∀ i, TraceMixing.coarseErr p (deg0 D i) (Fintype.card D.cut.Half) < 1 := by
    intro i
    exact (coarseErr_tail hp (hd i) (by omega)).trans_lt (by norm_num)
  have h := hzeta_cut_paper D hW (by omega) hnW hne he1 le_rfl (by omega)
    he Adj hAdj J hJ hnc
  exact h.trans (mul_le_mul_of_nonneg_right (zeta_tail D hp hn ht hd) (by unfold rp; positivity))


end Sarkozy.SpectralD.AtMost
