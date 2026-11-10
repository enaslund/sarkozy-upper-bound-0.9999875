module

public import Sarkozy.SpectralD.ClassOneModels
public import Sarkozy.SpectralD.RootCriterion

/-!
# Computable class-one model matrices for the root cuts

The coverable correction enumerates subsets of a common cross neighbourhood,
whose size is at most twelve. It does not enumerate all subsets of the half.
-/

@[expose] public section

namespace Sarkozy.SpectralD.Root

open Finset Sarkozy.Labellings Sarkozy.SpectralC

def neighboursB (c : ReflectionCut Slot) (k : c.Half) : Finset c.Half :=
  univ.filter (fun j => sgnB c.flip j.1 k.1 ≠ 0)

def halfAdjB {c : ReflectionCut Slot} (i j : c.Half) : Prop :=
  edgeB i.1 j.1 = true ∨ edgeB j.1 i.1 = true

instance {c : ReflectionCut Slot} : DecidableRel (halfAdjB (c := c)) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

def gramOne (c : ReflectionCut Slot) (k l : c.Half) : ℤ :=
  2 ^ (neighboursB c k ∩ neighboursB c l).card - 1

def coverOne (c : ReflectionCut Slot) (k l : c.Half) : ℤ :=
  coverCount (neighboursB c) halfAdjB k l

def plusOne (c : ReflectionCut Slot) (k l : c.Half) : ℤ := gramOne c k l + coverOne c k l

def crossOne (c : ReflectionCut Slot) (k l : c.Half) : ℤ :=
  if sgnB c.flip k.1 l.1 = 0 then 0 else 1

theorem Nset_eq_neighboursB (D : Cuts.SpecData Slot) (hG : D.G = rootGraph) :
    D.Nset = neighboursB D.cut := by
  funext k
  unfold Cuts.SpecData.Nset neighboursB
  congr 1
  funext j
  rw [sgn_eq D hG]

theorem halfAdjB_contains (D : Cuts.SpecData Slot) (hG : D.G = rootGraph)
    (i j : D.cut.Half) (h : (i, j) ∈ D.halfGraph.E ∨ (j, i) ∈ D.halfGraph.E) :
    halfAdjB i j := by
  simpa only [halfAdjB, Cuts.SpecData.mem_halfGraph, mem_E D hG] using h

theorem gramOne_symm (c : ReflectionCut Slot) (k l : c.Half) :
    gramOne c k l = gramOne c l k := by unfold gramOne; rw [inter_comm]

theorem plusOne_symm (c : ReflectionCut Slot) (k l : c.Half) :
    plusOne c k l = plusOne c l k := by
  unfold plusOne coverOne
  rw [gramOne_symm, coverCount_symm]

variable {p : ℕ} [Fact p.Prime]

theorem modelHC_one_eq (D : Cuts.SpecData Slot) (hG : D.G = rootGraph)
    (hp1 : p % 4 = 1) (k l : D.cut.Half) :
    PaleyB.modelHC D.Nset (Cx.sgnZ (p := p) D) k l = (gramOne D.cut k l : ℂ) := by
  unfold PaleyB.modelHC
  rw [modelH_one D hp1, Nset_eq_neighboursB D hG]
  unfold gramOne
  push_cast
  rfl

theorem hplusM_one_eq (D : Cuts.SpecData Slot) (hG : D.G = rootGraph)
    (hp1 : p % 4 = 1) (k l : D.cut.Half) :
    PaleyB.hplusM halfAdjB D.Nset (Cx.sgnZ (p := p) D) k l = (plusOne D.cut k l : ℂ) := by
  unfold PaleyB.hplusM
  rw [hp1, modelHC_one_eq D hG hp1, hcovM_one D hp1]
  simp only [ite_true, Complex.ofReal_one, one_mul, Nset_eq_neighboursB D hG]
  unfold plusOne coverOne
  push_cast
  rfl

theorem deltaE_one_eq (D : Cuts.SpecData Slot) (hG : D.G = rootGraph)
    (hp1 : p % 4 = 1) (k l : D.cut.Half) :
    deltaE (Cx.sgnZ (p := p) D) k l = (crossOne D.cut k l : ℂ) := by
  unfold crossOne
  rw [← sgn_eq D hG]
  by_cases h : D.sgn k l = 0
  · simp only [deltaE, Cx.sgnZ, h, Int.cast_zero, ne_eq, not_true_eq_false, ite_false,
      ite_true]
  · have hk : k ∈ D.Nset l := by
      simpa only [Cuts.SpecData.Nset, mem_filter, mem_univ, true_and] using h
    rw [deltaE, ite_eq_left (Cx.sgnZ_ne_zero D hk), chi_sign_one D hp1 k l h, ite_eq_right h]
    norm_num

end Sarkozy.SpectralD.Root
