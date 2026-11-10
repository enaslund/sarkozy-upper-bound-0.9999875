module

public import Sarkozy.SpectralD.FiniteGeometry
public import Sarkozy.SpectralD.ClassOneModels

/-!
# Integer model matrices for a Boolean graph

Both odd prime classes reduce to finite integer matrices. In class one
the coverable correction is included explicitly.
-/

@[expose] public section

namespace Sarkozy.SpectralD.FiniteModel

open Finset Sarkozy.SpectralC Sarkozy.Characters

variable {W : Type*} [Fintype W] [DecidableEq W]

def Adj (E : W → W → Bool) (c : ReflectionCut W) (i j : c.Half) : Prop :=
  E i.1 j.1 = true ∨ E j.1 i.1 = true

instance (E : W → W → Bool) (c : ReflectionCut W) : DecidableRel (Adj E c) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def gramOne (E : W → W → Bool) (c : ReflectionCut W) (i j : c.Half) : ℤ :=
  2 ^ (edgeNeighbours E c i ∩ edgeNeighbours E c j).card - 1

def plusOne (E : W → W → Bool) (c : ReflectionCut W) (i j : c.Half) : ℤ :=
  gramOne E c i j + coverCount (edgeNeighbours E c) (Adj E c) i j

def crossOne (E : W → W → Bool) (c : ReflectionCut W) (i j : c.Half) : ℤ :=
  if edgeSign E c.flip i.1 j.1 = 0 then 0 else 1

def gramThree (E : W → W → Bool) (c : ReflectionCut W) (i j : c.Half) : ℤ :=
  ∏ k : c.Half, (1 + edgeSign E c.flip k.1 i.1 * edgeSign E c.flip k.1 j.1) - 1

variable (D : Cuts.SpecData W) (E : W → W → Bool)
  (hE : ∀ i j, (i, j) ∈ D.G.E ↔ E i j = true)

include hE

theorem Adj_contains (i j : D.cut.Half)
    (h : (i, j) ∈ D.halfGraph.E ∨ (j, i) ∈ D.halfGraph.E) : Adj E D.cut i j := by
  simpa only [Adj, Cuts.SpecData.mem_halfGraph, hE] using h

variable {p : ℕ} [Fact p.Prime]

theorem modelHC_one (hp1 : p % 4 = 1) (i j : D.cut.Half) :
    PaleyB.modelHC D.Nset (Cx.sgnZ (p := p) D) i j = (gramOne E D.cut i j : ℂ) := by
  unfold PaleyB.modelHC
  rw [modelH_one D hp1, Nset_eq_edgeNeighbours D E hE]
  unfold gramOne
  push_cast
  rfl

theorem hplusM_one (hp1 : p % 4 = 1) (i j : D.cut.Half) :
    PaleyB.hplusM (Adj E D.cut) D.Nset (Cx.sgnZ (p := p) D) i j =
      (plusOne E D.cut i j : ℂ) := by
  unfold PaleyB.hplusM
  rw [hp1, modelHC_one D E hE hp1, hcovM_one D hp1]
  simp only [ite_true, Complex.ofReal_one, one_mul, Nset_eq_edgeNeighbours D E hE]
  unfold plusOne
  push_cast
  rfl

theorem deltaE_one (hp1 : p % 4 = 1) (i j : D.cut.Half) :
    deltaE (Cx.sgnZ (p := p) D) i j = (crossOne E D.cut i j : ℂ) := by
  unfold crossOne
  rw [← sgn_eq_edgeSign D E hE]
  by_cases h : D.sgn i j = 0
  · simp only [deltaE, Cx.sgnZ, h, Int.cast_zero, ne_eq, not_true_eq_false, ite_false,
      ite_true]
  · have hk : i ∈ D.Nset j := by
      simpa only [Cuts.SpecData.Nset, mem_filter, mem_univ, true_and] using h
    rw [deltaE, ite_eq_left (Cx.sgnZ_ne_zero D hk), chi_sign_one D hp1 i j h,
      ite_eq_right h]
    norm_num

theorem modelHC_three (hp3 : p % 4 = 3) (i j : D.cut.Half) :
    PaleyB.modelHC D.Nset (Cx.sgnZ (p := p) D) i j = (gramThree E D.cut i j : ℂ) := by
  unfold PaleyB.modelHC
  rw [Root.modelH_eq D hp3]
  simp only [Root.hMat, gramThree, sgn_eq_edgeSign D E hE, Complex.ofReal_intCast]

theorem hplusM_three (hp3 : p % 4 = 3) (i j : D.cut.Half) :
    PaleyB.hplusM (Adj E D.cut) D.Nset (Cx.sgnZ (p := p) D) i j =
      (gramThree E D.cut i j : ℂ) := by
  unfold PaleyB.hplusM
  rw [hp3, modelHC_three D E hE hp3]
  norm_num

theorem deltaE_three (hp3 : p % 4 = 3) (i j : D.cut.Half) :
    deltaE (Cx.sgnZ (p := p) D) i j = (edgeSign E D.cut.flip i.1 j.1 : ℂ) := by
  rw [← sgn_eq_edgeSign D E hE]
  by_cases h : D.sgn i j = 0
  · simp only [deltaE, Cx.sgnZ, h, Int.cast_zero, ne_eq, not_true_eq_false, ite_false]
  · have hk : i ∈ D.Nset j := by
      simpa only [Cuts.SpecData.Nset, mem_filter, mem_univ, true_and] using h
    rw [deltaE, ite_eq_left (Cx.sgnZ_ne_zero D hk), chiC_apply]
    exact_mod_cast Root.chi_int hp3 (D.sgn i j) (Root.sgn_cases D i j)

end Sarkozy.SpectralD.FiniteModel
