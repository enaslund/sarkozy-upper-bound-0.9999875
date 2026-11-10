module

public import Sarkozy.SpectralD.TailAnalyticInputs
public import Sarkozy.SecondOrder.StarAtMost

/-!
# Analytic spectral inputs for every smaller half

The row sums and coupling sums decrease with the number of vertices.
The root allowances therefore apply to every half of size at most 36.
-/

@[expose] public section

namespace Sarkozy.SpectralD.AtMost

open Finset Sarkozy.Labellings Sarkozy.SpectralC

variable {p : ℕ} [Fact p.Prime] {U W : Type*}
  [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

theorem betaG_tail_row (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ)
    (hn : Fintype.card U ≤ 36) (hr : ∀ k, (N k).card ≤ 12) (he0 : ∀ t, 0 ≤ e t)
    (he : ∀ t ≤ 24, e t ≤ 2⁻¹ ^ 50) (k : U) : ∑ l, betaG N ς e k l ≤ 1 / 2000 := by
  calc _ ≤ ∑ _l : U, (2 : ℝ)⁻¹ ^ 20 :=
        sum_le_sum fun l _ => betaG_tail_entry N ς e hr he0 he k l
    _ ≤ 36 * (2 : ℝ)⁻¹ ^ 20 := SecondOrder.AtMost.sum_const_bound hn (by positivity)
    _ ≤ 1 / 2000 := by norm_num

theorem bX_tail_row (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ)
    (R : U → ℝ) (hn : Fintype.card U ≤ 36) (hr : ∀ k, (N k).card ≤ 12)
    (he : ∀ t ≤ 24, e t ≤ 2⁻¹ ^ 50)
    (hR1 : ∀ k, 1 ≤ R k) (hR : ∀ k, R k ≤ 1 + 2⁻¹ ^ 40) (k : U) :
    ∑ l, bX N ς e R k l ≤ 1 / 2000 := by
  calc _ ≤ ∑ _l : U, (2 : ℝ)⁻¹ ^ 20 :=
        sum_le_sum fun l _ => bX_tail_entry N ς e R hr he hR1 hR k l
    _ ≤ 36 * (2 : ℝ)⁻¹ ^ 20 := SecondOrder.AtMost.sum_const_bound hn (by positivity)
    _ ≤ 1 / 2000 := by norm_num


theorem small_rowX_tail (D : Cuts.SpecData W) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card W ≤ 72) (hhalf : Fintype.card D.cut.Half ≤ 36)
    (hd : ∀ v, nbrCount D.G (univ.erase v) v ≤ 20) (k : D.cut.Half) :
    ∑ l, (if Cx.sgnZ (p := p) D k l = 0 then Cx.mXcut p D k l else 0) ≤ (2 : ℝ)⁻¹ ^ 40 := by
  calc _ ≤ ∑ _l : D.cut.Half, (2 : ℝ)⁻¹ ^ 48 := sum_le_sum fun l _ => by
        split_ifs
        · exact mXcut_tail D hp hn hd k l
        · positivity
    _ ≤ 36 * (2 : ℝ)⁻¹ ^ 48 :=
        SecondOrder.AtMost.sum_const_bound hhalf (by positivity)
    _ ≤ (2 : ℝ)⁻¹ ^ 40 := by norm_num

omit [Fact p.Prime] in
theorem small_rowV_tail (D : Cuts.SpecData W) (hp : 2 ^ 512 ≤ p)
    (hhalf : Fintype.card D.cut.Half ≤ 36)
    (hd : ∀ k, nbrCount D.halfGraph (univ.erase k) k ≤ 20) (k : D.cut.Half) :
    ∑ l, (if k = l then 0 else Cx.mVcut p D k l) ≤ 36 := by
  calc _ ≤ ∑ _l : D.cut.Half, (1 : ℝ) := sum_le_sum fun l _ => by
        split_ifs
        · norm_num
        · exact mVcut_tail D hp (by omega) hd k l
    _ ≤ 36 := by simpa only [mul_one] using
        SecondOrder.AtMost.sum_const_bound hhalf (by norm_num : (0 : ℝ) ≤ 1)


omit [DecidableEq U] in
theorem coupling_error_tail (N : U → Finset U) (R : U → ℝ) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card U ≤ 36) (hr : ∀ k, (N k).card ≤ 12)
    (hR1 : ∀ k, 1 ≤ R k) (hR : ∀ k, R k ≤ 1 + 2⁻¹ ^ 40) :
    ∑ k, ((2 : ℝ) ^ (N k).card *
        (1 + TraceMixing.coarseErr p (N k).card (Fintype.card U)) *
        devConst (R k) (TraceMixing.coarseErr p (N k).card (Fintype.card U)) ^ 2 +
      (Fintype.card U : ℝ) * 4 ^ (N k).card / p) ≤ 1 / 100000000 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc _ ≤ ∑ _k : U, (2 : ℝ)⁻¹ ^ 40 := sum_le_sum fun k _ => by
        have hnR : (Fintype.card U : ℝ) ≤ 36 := by exact_mod_cast hn
        have hterm : (Fintype.card U : ℝ) * 4 ^ (N k).card / p ≤
            36 * 4 ^ (N k).card / p := by gcongr
        apply (add_le_add le_rfl hterm).trans
        exact tail_coupling_entry hp (hr k) (TraceMixing.coarseErr_nonneg hp0 _ _)
          (coarseErr_tail hp ((hr k).trans (by norm_num)) (by omega)) (hR1 k) (hR k)
    _ ≤ 36 * (2 : ℝ)⁻¹ ^ 40 := SecondOrder.AtMost.sum_const_bound hn (by positivity)
    _ ≤ 1 / 100000000 := by norm_num


theorem tail_analytic_inputs (D : Cuts.SpecData W) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card W ≤ 72) (hhalf : Fintype.card D.cut.Half ≤ 36)
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


end Sarkozy.SpectralD.AtMost
