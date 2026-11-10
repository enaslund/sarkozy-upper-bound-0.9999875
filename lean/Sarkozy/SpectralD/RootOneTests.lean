module

public import Sarkozy.SpectralD.RootOneFinite
public import Sarkozy.SpectralD.IntegerFiniteTest
public import Sarkozy.SpectralD.ClassOneCharacters

/-!
# The class-one root finite tests

The three graph-verified integer matrices cover every Fourier character.
The LL20 test uses s = 223/2; the LL22 test uses s = 44.
-/

@[expose] public section

namespace Sarkozy.SpectralD.Root

open Sarkozy.SpectralC

variable {p : ℕ} [Fact p.Prime]

theorem LL20_tail_finiteTest_one (hp1 : p % 4 = 1) (ξ : ZMod p) :
    Spectral.FiniteTest (fun x => (qform (azero (Cx.sgnZ LL20) ξ) x).re)
      (Cx.qXcx halfAdjB LL20.Nset (Cx.sgnZ LL20) ξ)
      (1 / 4) (223 / 2) (1 / 1000) (3 / 20) := by
  obtain ⟨e, he⟩ := chi_eps_one hp1 ξ
  have hA : azero (Cx.sgnZ LL20) ξ =
      (fun i j => integerMode (crossOne LL20.cut) (oneChar e) i j) := by
    funext i j
    unfold azero integerMode
    rw [deltaE_one_eq LL20 rfl hp1, he]
    rfl
  have hH : PaleyB.hplusM halfAdjB LL20.Nset (Cx.sgnZ (p := p) LL20) =
      (fun i j => integerMatrix
        (fun i j => oneEntry LL20_HplusOneTable (slotCode i.1) (slotCode j.1)) i j) := by
    funext i j
    rw [hplusM_one_eq LL20 rfl hp1, LL20_plusOne_table]
    rfl
  have h := finiteTest_of_integer (crossOne LL20.cut)
    (fun i j => oneEntry LL20_HplusOneTable (slotCode i.1) (slotCode j.1))
    24919727 223000 (oneChar e) (s := 223 / 2) (c := 1 / 4) (ηQ := 1 / 1000) (ηB := 3 / 20)
    (by norm_num) (by norm_num) (by norm_num) (LL20_oneTest_nonneg e)
  intro x
  simpa only [Cx.qXcx, hA, hH] using h x

theorem LL22_tail_finiteTest_one (hp1 : p % 4 = 1) (ξ : ZMod p) :
    Spectral.FiniteTest (fun x => (qform (azero (Cx.sgnZ LL22) ξ) x).re)
      (Cx.qXcx halfAdjB LL22.Nset (Cx.sgnZ LL22) ξ)
      (1 / 4) (44) (1 / 1000) (3 / 20) := by
  obtain ⟨e, he⟩ := chi_eps_one hp1 ξ
  have hA : azero (Cx.sgnZ LL22) ξ =
      (fun i j => integerMode (crossOne LL22.cut) (oneChar e) i j) := by
    funext i j
    unfold azero integerMode
    rw [deltaE_one_eq LL22 rfl hp1, he]
    rfl
  have hH : PaleyB.hplusM halfAdjB LL22.Nset (Cx.sgnZ (p := p) LL22) =
      (fun i j => integerMatrix
        (fun i j => oneEntry LL22_HplusOneTable (slotCode i.1 / 2) (slotCode j.1 / 2)) i j) := by
    funext i j
    rw [hplusM_one_eq LL22 rfl hp1, LL22_plusOne_table]
    rfl
  have h := finiteTest_of_integer (crossOne LL22.cut)
    (fun i j => oneEntry LL22_HplusOneTable (slotCode i.1 / 2) (slotCode j.1 / 2))
    3893612 88000 (oneChar e) (s := 44) (c := 1 / 4) (ηQ := 1 / 1000) (ηB := 3 / 20)
    (by norm_num) (by norm_num) (by norm_num) (LL22_oneTest_nonneg e)
  intro x
  simpa only [Cx.qXcx, hA, hH] using h x

theorem LL20_tail_finite_cap_one :
    ((1 / 4 : ℝ) + 223 / 2) / (1 - 1 / 100) ≤ 113 := by norm_num

end Sarkozy.SpectralD.Root
