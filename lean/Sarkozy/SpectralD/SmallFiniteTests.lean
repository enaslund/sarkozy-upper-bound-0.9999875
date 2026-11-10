module

public import Sarkozy.SpectralD.SmallMatrixChecks
public import Sarkozy.SpectralD.ComplexFiniteTest
public import Sarkozy.SpectralD.ClassThreeCharacters

/-!
# Finite spectral tests for the nine smaller cuts

The exact Gaussian integer certificates cover both odd prime classes and
all three possible Fourier coefficients, including the zero character.
-/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Finset Sarkozy.PartVLaws.FieldGraphs Sarkozy.SpectralC
open scoped Matrix

set_option maxHeartbeats 0

noncomputable def step (c : SmallCut) : ℝ := cap c - 1 / 500

theorem step_pos (c : SmallCut) : 0 < step c := by
  cases c <;> norm_num [step, cap]

theorem linear_eq (c : SmallCut) : (linear c : ℝ) = 100000000 * step c := by
  cases c <;> norm_num [step, cap, linear]

theorem base_eq (c : SmallCut) :
    (base c : ℝ) = 100000000 * (step c * (1 / 1000 + step c - 1 / 100000) - 1 / 100) := by
  cases c <;> norm_num [step, cap, base]

theorem step_cap (c : SmallCut) :
    ((1 / 1000 : ℝ) + step c) / (1 - 1 / 100000) ≤ cap c := by
  cases c <;> norm_num [step, cap]

theorem test_matrix_eq (c : SmallCut) (a : Fin 2) (e : Fin 3) :
    (fun i j => gaussian (testReal c a e i j) (testImag c a e i j)) =
      complexTest (modelD c a) (modelH c a) 100000000 (base c) (linear c) (char e) a := by
  funext i j
  rw [(tests c a e i j).1, (tests c a e i j).2]
  apply Complex.ext
  all_goals
    fin_cases a <;> simp [gaussian, complexTest, phase, Complex.re_sum,
      Complex.im_sum, Int.cast_sum, Int.cast_mul, pow_two] <;> split_ifs <;> simp

theorem finiteTest_model (c : SmallCut) (a : Fin 2) (e : Fin 3) :
    Spectral.FiniteTest
      (fun x => (qform (fun i j => phaseMode (modelD c a) (char e) a i j) x).re)
      (fun x => Spectral.qform (integerMatrix (modelH c a)) x x -
        Spectral.sqn (phaseMode (modelD c a) (char e) a *ᵥ x))
      (1 / 1000) (step c) (1 / 100000) (1 / 100) := by
  apply finiteTest_of_scaled_matrix _ _
    (fun i j => gaussian (testReal c a e i j) (testImag c a e i j))
    (scale := 100000000) (step_pos c) (by norm_num)
  · rw [test_matrix_eq]
    exact complexTest_cast _ _ _ _ _ _ _ (linear_eq c) (base_eq c)
  · exact test_nonneg c (residuals c) a e

variable {p : ℕ} [Fact p.Prime]

theorem finiteTest_one (c : SmallCut) (hp1 : p % 4 = 1) (ξ : ZMod p) :
    Spectral.FiniteTest (fun x => (qform (azero (Cx.sgnZ c.data) ξ) x).re)
      (Cx.qXcx (FiniteModel.Adj c.edge c.data.cut) c.data.Nset (Cx.sgnZ c.data) ξ)
      (1 / 1000) (step c) (1 / 100000) (1 / 100) := by
  obtain ⟨e, he⟩ := chi_eps_one hp1 ξ
  have hA : azero (Cx.sgnZ c.data) ξ =
      (fun i j => phaseMode (modelD c 0) (char e) 0 i j) := by
    funext i j
    unfold azero phaseMode
    rw [FiniteModel.deltaE_one c.data c.edge (SmallCut.mem_edge c) hp1, he,
      (models c i j).2.1]
    simp [phase, char, modelD]
  have hH : PaleyB.hplusM (FiniteModel.Adj c.edge c.data.cut) c.data.Nset
      (Cx.sgnZ (p := p) c.data) =
      (fun i j => integerMatrix (modelH c 0) i j) := by
    funext i j
    rw [FiniteModel.hplusM_one c.data c.edge (SmallCut.mem_edge c) hp1,
      (models c i j).2.2.2.1]
    rfl
  intro x
  simpa only [Cx.qXcx, hA, hH] using finiteTest_model c 0 e x

theorem finiteTest_three (c : SmallCut) (hp3 : p % 4 = 3) (ξ : ZMod p) :
    Spectral.FiniteTest (fun x => (qform (azero (Cx.sgnZ c.data) ξ) x).re)
      (Cx.qXcx (FiniteModel.Adj c.edge c.data.cut) c.data.Nset (Cx.sgnZ c.data) ξ)
      (1 / 1000) (step c) (1 / 100000) (1 / 100) := by
  obtain ⟨e, he⟩ := chi_eps_three hp3 ξ
  have hA : azero (Cx.sgnZ c.data) ξ =
      (fun i j => phaseMode (modelD c 1) (char e) 1 i j) := by
    funext i j
    unfold azero phaseMode
    rw [FiniteModel.deltaE_three c.data c.edge (SmallCut.mem_edge c) hp3, he,
      (models c i j).1]
    simp [phase, char, modelD]
  have hH : PaleyB.hplusM (FiniteModel.Adj c.edge c.data.cut) c.data.Nset
      (Cx.sgnZ (p := p) c.data) =
      (fun i j => integerMatrix (modelH c 1) i j) := by
    funext i j
    rw [FiniteModel.hplusM_three c.data c.edge (SmallCut.mem_edge c) hp3,
      (models c i j).2.2.2.2]
    rfl
  intro x
  simpa only [Cx.qXcx, hA, hH] using finiteTest_model c 1 e x

theorem finiteTest (c : SmallCut) (hp : p ≠ 2) (ξ : ZMod p) :
    Spectral.FiniteTest (fun x => (qform (azero (Cx.sgnZ c.data) ξ) x).re)
      (Cx.qXcx (FiniteModel.Adj c.edge c.data.cut) c.data.Nset (Cx.sgnZ c.data) ξ)
      (1 / 1000) (step c) (1 / 100000) (1 / 100) := by
  rcases PaleyB.mod_four_cases (Fact.out : p.Prime) hp with h | h
  · exact finiteTest_one c h ξ
  · exact finiteTest_three c h ξ

end Sarkozy.SpectralD.SmallMatrices
