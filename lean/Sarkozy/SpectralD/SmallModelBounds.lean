module

public import Sarkozy.SpectralD.SmallMatrixChecks
public import Sarkozy.SpectralD.SmallTailErrors
public import Sarkozy.SpectralD.MatrixCertificate

/-! Uniform model bounds for the nine smaller cuts, from their exact row checks. -/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Finset Sarkozy.PartVLaws.FieldGraphs Sarkozy.SpectralC

theorem rho_bound (c : SmallCut) (j : c.data.cut.Half) :
    ((2 : ℝ) ^ (c.data.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (c.data.Nset j').card - 1) ≤ 301768740 := by
  have hb (i : c.data.cut.Half) : (2 : ℝ) ^ (c.data.Nset i).card - 1 ≤ 255 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (SmallCut.cross_degree c i)
    norm_num at h
    linarith
  have hsum : ∑ i : c.data.cut.Half, ((2 : ℝ) ^ (c.data.Nset i).card - 1) ≤ 18 * 255 := by
    calc _ ≤ ∑ _i : c.data.cut.Half, (255 : ℝ) := sum_le_sum (fun i _ => hb i)
      _ = (Fintype.card c.data.cut.Half : ℝ) * 255 := by simp
      _ ≤ 18 * 255 := by
        have hn : (Fintype.card c.data.cut.Half : ℝ) ≤ 18 := by
          exact_mod_cast SmallCut.card_half c
        gcongr
  have hs0 : 0 ≤ ∑ i : c.data.cut.Half, ((2 : ℝ) ^ (c.data.Nset i).card - 1) := by
    apply sum_nonneg
    intro i _
    exact sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  calc _ ≤ 255 * (18 * 255 : ℝ) := mul_le_mul (hb j) hsum hs0 (by norm_num)
    _ ≤ _ := by norm_num

variable {p : ℕ} [Fact p.Prime]

theorem model_upper (c : SmallCut) (hp : p ≠ 2) (x : c.data.cut.Half → ℂ) :
    (qform (PaleyB.modelHC c.data.Nset (Cx.sgnZ (p := p) c.data)) x).re ≤
      8928 * ∑ j, ‖x j‖ ^ 2 := by
  rcases PaleyB.mod_four_cases (Fact.out : p.Prime) hp with hp1 | hp3
  · have hM : PaleyB.modelHC c.data.Nset (Cx.sgnZ (p := p) c.data) =
        (fun i j => (atTable c (gramOneTable c) i j : ℂ)) := by
      funext i j
      rw [FiniteModel.modelHC_one c.data c.edge (SmallCut.mem_edge c) hp1]
      exact congrArg (fun z : ℤ => (z : ℂ)) (models c i j).2.2.1
    rw [hM]
    exact qform_le_of_integer_rows _ (rows c).1 8928 (fun i => ((rows c).2.2.2 i).1) x
  · have hM : PaleyB.modelHC c.data.Nset (Cx.sgnZ (p := p) c.data) =
        (fun i j => (atTable c (gramThreeTable c) i j : ℂ)) := by
      funext i j
      rw [FiniteModel.modelHC_three c.data c.edge (SmallCut.mem_edge c) hp3]
      exact congrArg (fun z : ℤ => (z : ℂ)) (models c i j).2.2.2.2
    rw [hM]
    exact qform_le_of_integer_rows _ (rows c).2.1 8928
      (fun i => ((rows c).2.2.2 i).2.1) x

theorem plus_upper (c : SmallCut) (hp : p ≠ 2) (x : c.data.cut.Half → ℂ) :
    (qform (PaleyB.hplusM (FiniteModel.Adj c.edge c.data.cut) c.data.Nset
      (Cx.sgnZ (p := p) c.data)) x).re ≤ 12384 * ∑ j, ‖x j‖ ^ 2 := by
  rcases PaleyB.mod_four_cases (Fact.out : p.Prime) hp with hp1 | hp3
  · have hM : PaleyB.hplusM (FiniteModel.Adj c.edge c.data.cut) c.data.Nset
        (Cx.sgnZ (p := p) c.data) =
        (fun i j => (atTable c (plusOneTable c) i j : ℂ)) := by
      funext i j
      rw [FiniteModel.hplusM_one c.data c.edge (SmallCut.mem_edge c) hp1]
      exact congrArg (fun z : ℤ => (z : ℂ)) (models c i j).2.2.2.1
    rw [hM]
    exact qform_le_of_integer_rows _ (rows c).2.2.1 12384
      (fun i => ((rows c).2.2.2 i).2.2) x
  · have hM : PaleyB.hplusM (FiniteModel.Adj c.edge c.data.cut) c.data.Nset
        (Cx.sgnZ (p := p) c.data) =
        (fun i j => (atTable c (gramThreeTable c) i j : ℂ)) := by
      funext i j
      rw [FiniteModel.hplusM_three c.data c.edge (SmallCut.mem_edge c) hp3]
      exact congrArg (fun z : ℤ => (z : ℂ)) (models c i j).2.2.2.2
    rw [hM]
    exact qform_le_of_integer_rows _ (rows c).2.1 12384
      (fun i => (((rows c).2.2.2 i).2.1).trans (by norm_num)) x

theorem deltaE_bound (c : SmallCut) : NormLe (deltaE (Cx.sgnZ (p := p) c.data)) 12 := by
  apply Cx.deltaE_normLe
  intro k
  exact_mod_cast (SmallCut.cross_degree c k).trans (by norm_num : 8 ≤ 12)

theorem graph_error (c : SmallCut) (hp : 2 ^ 512 ≤ p) (i : c.data.cut.Half) :
    SecondOrder.graphCountError (p := p) c.data.halfGraph i < 1 := by
  apply lt_of_le_of_lt (AtMost.graphCountError_bound c.data.halfGraph
    ((SmallCut.card_half c).trans (by norm_num)) ?_ (by omega) i) (by norm_num)
  intro j
  have h := SmallCut.half_degree c j
  rw [SecondOrder.nbrCount_erase_self] at h
  exact h.trans (by norm_num)

end Sarkozy.SpectralD.SmallMatrices
