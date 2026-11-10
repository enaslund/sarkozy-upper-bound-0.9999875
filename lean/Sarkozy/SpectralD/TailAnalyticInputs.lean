module

public import Sarkozy.SpectralD.TailCoupling
public import Sarkozy.SpectralD.TailEtaB
public import Sarkozy.SpectralD.TailSmall

/-!
# All analytic row and density inputs for the root tail criterion

This package supplies concrete allowances from the sizes and degrees of
the graphs. Its construction has no unproved analytic input.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.Labellings Sarkozy.SpectralC

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W]

structure TailAnalyticInputs (p : ℕ) [Fact p.Prime] (D : Cuts.SpecData W) : Prop where
  coupling : ∑ k, ((2 : ℝ) ^ (D.Nset k).card *
      (1 + TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) *
      devConst (Cx.Rprime p D 72 (Cx.restList D) k)
        (TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) ^ 2 +
      (Fintype.card D.cut.Half : ℝ) * 4 ^ (D.Nset k).card / p) ≤ 1 / 100000000
  beta : ∀ k, ∑ l, betaG D.Nset (Cx.sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) k l ≤ 1 / 2000
  cross : ∀ k, ∑ l, bX D.Nset (Cx.sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half))
      (Cx.Rprime p D 72 (Cx.restList D)) k l ≤ 1 / 2000
  theta : ∀ j : D.cut.Half,
      D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) ^ 2 *
        (2 ^ nbrCount D.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (nbrCount D.halfGraph (univ.erase j) j)
            (Fintype.card D.cut.Half))) - 1 ≤ 64 ^ 2
  smallX : ∀ k, ∑ l, (if Cx.sgnZ (p := p) D k l = 0 then Cx.mXcut p D k l else 0) ≤
      (2 : ℝ)⁻¹ ^ 40
  smallV : ∀ k, ∑ l, (if k = l then 0 else Cx.mVcut p D k l) ≤ 36
  density : D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) ^ 2 *
      (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72))⁻¹ ≤ 1 + 2⁻¹ ^ 40

theorem tail_analytic_inputs (D : Cuts.SpecData W) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card W ≤ 72) (hhalf : Fintype.card D.cut.Half = 36)
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ 20)
    (hd : ∀ j, nbrCount D.halfGraph (univ.erase j) j ≤ 10)
    (hr : ∀ k, (D.Nset k).card ≤ 12) : TailAnalyticInputs p D := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hfull : ∀ v, nbrCount D.G (univ.erase v) v ≤ 20 := Cx.nbrCount_G_le D hdeg
  have hR := Rprime_tail D hp hn hfull
  have hR1 : ∀ k, 1 ≤ Cx.Rprime p D 72 (Cx.restList D) k := fun _ => le_max_left _ _
  have he : ∀ t ≤ 24, TraceMixing.coarseErr p t (Fintype.card D.cut.Half) ≤ (2 : ℝ)⁻¹ ^ 50 :=
    fun t ht => coarseErr_tail hp ht (by omega)
  have he0 : ∀ t, 0 ≤ TraceMixing.coarseErr p t (Fintype.card D.cut.Half) :=
    fun t => TraceMixing.coarseErr_nonneg hp0 t _
  have ht : ∀ i, D.tdeg i ≤ 24 := fun i => (Cx.tdeg_le D hdeg i).trans (by norm_num)
  have hcut := Rcut_tail D hp (by omega) ht
  have hcut1 : 1 ≤ D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) := by
    apply Cx.one_le_Rcut D
    intro i
    rw [ZMod.card]
    exact lt_of_le_of_lt (coarseErr_tail hp (ht i) le_rfl) (by norm_num)
  refine ⟨coupling_error_tail D.Nset _ hp hhalf hr hR1 hR,
    betaG_tail_row D.Nset _ _ hhalf hr he0 he,
    bX_tail_row D.Nset _ _ _ hhalf hr he hR1 hR, ?_,
    small_rowX_tail D hp hn hhalf hfull,
    small_rowV_tail D hp hhalf (fun j => (hd j).trans (by norm_num)), ?_⟩
  · intro j
    exact tail_theta_scalar (zero_le_one.trans hcut1) hcut
      (he _ ((hd j).trans (by norm_num))) (hd j)
  · have hpos : 0 < D.Rcut
        (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) := by linarith
    rw [pow_two, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one]
    exact hcut

end Sarkozy.SpectralD
