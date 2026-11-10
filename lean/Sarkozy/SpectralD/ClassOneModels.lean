module

public import Sarkozy.SpectralD.RootModelH
public import Sarkozy.SpectralD.CxCounts

/-!
# Finite models at primes equal to one modulo four

Every nonzero cross sign has quadratic character one. Thus the model
Gram entries count common-neighbour subsets, and the coverable correction
counts only coverable subsets of the common neighbourhood.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Complex Sarkozy.SpectralC Sarkozy.Characters
open scoped ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W]

theorem chi_sign_one (D : Cuts.SpecData W) (hp1 : p % 4 = 1) (j k : D.cut.Half)
    (h : D.sgn j k ≠ 0) : chiC p (Cx.sgnZ D j k) = 1 := by
  have hp2 : p ≠ 2 := by omega
  rcases Root.sgn_cases D j k with hs | hs | hs
  · simp only [Cx.sgnZ, hs, Int.cast_one, MulChar.map_one]
  · simp only [Cx.sgnZ, hs, Int.cast_neg, Int.cast_one]
    rw [chiC_neg_one hp2, ZMod.χ₄_nat_one_mod_four hp1]
    norm_num
  · exact (h hs).elim

theorem modelH_one (D : Cuts.SpecData W) (hp1 : p % 4 = 1) (k l : D.cut.Half) :
    modelH D.Nset (Cx.sgnZ (p := p) D) k l = (2 : ℝ) ^ (D.Nset k ∩ D.Nset l).card - 1 := by
  have hc : ∀ j ∈ D.Nset k ∩ D.Nset l,
      (quadraticChar (ZMod p) (Cx.sgnZ D j k * Cx.sgnZ D j l) : ℝ) = 1 := by
    intro j hj
    have hk : D.sgn j k ≠ 0 := by
      simpa only [Cuts.SpecData.Nset, mem_filter, mem_univ, true_and] using (mem_inter.mp hj).1
    have hl : D.sgn j l ≠ 0 := by
      simpa only [Cuts.SpecData.Nset, mem_filter, mem_univ, true_and] using (mem_inter.mp hj).2
    have h : chiC p (Cx.sgnZ D j k * Cx.sgnZ D j l) = 1 := by
      rw [map_mul, chi_sign_one D hp1 j k hk, chi_sign_one D hp1 j l hl, one_mul]
    rw [chiC_apply] at h
    exact_mod_cast h
  unfold modelH
  rw [prod_congr rfl (fun j hj => congrArg (1 + ·) (hc j hj))]
  norm_num only [show (1 : ℝ) + 1 = 2 by norm_num, prod_const]

theorem epsJ_one (D : Cuts.SpecData W) (hp1 : p % 4 = 1) (J : Finset D.cut.Half)
    (k : D.cut.Half) :
    PaleyB.epsJ D.Nset (Cx.sgnZ (p := p) D) J k = if J ⊆ D.Nset k then 1 else 0 := by
  unfold PaleyB.epsJ
  split_ifs with h
  · apply prod_eq_one
    intro j hj
    apply chi_sign_one D hp1
    simpa only [Cuts.SpecData.Nset, mem_filter, mem_univ, true_and] using h hj
  · rfl

section Count

variable {U : Type*} [Fintype U] [DecidableEq U]

def coverCount (N : U → Finset U) (Adj : U → U → Prop) [DecidableRel Adj] (k l : U) : ℕ :=
  ((N k ∩ N l).powerset.filter (fun J => 2 ≤ J.card ∧ PaleyB.Coverable Adj J)).card

theorem coverCount_symm (N : U → Finset U) (Adj : U → U → Prop) [DecidableRel Adj]
    (k l : U) : coverCount N Adj k l = coverCount N Adj l k := by
  unfold coverCount
  rw [inter_comm]

theorem coverCount_eq_filter (N : U → Finset U) (Adj : U → U → Prop) [DecidableRel Adj]
    (k l : U) :
    (PaleyB.covSets Adj).filter (fun J => J ⊆ N k ∩ N l) =
      (N k ∩ N l).powerset.filter (fun J => 2 ≤ J.card ∧ PaleyB.Coverable Adj J) := by
  ext J
  simp only [PaleyB.covSets, mem_filter, mem_univ, true_and, mem_powerset]
  tauto

end Count

theorem hcovM_one (D : Cuts.SpecData W) (hp1 : p % 4 = 1)
    (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj] (k l : D.cut.Half) :
    PaleyB.hcovM Adj D.Nset (Cx.sgnZ (p := p) D) k l = (coverCount D.Nset Adj k l : ℂ) := by
  unfold PaleyB.hcovM
  simp_rw [epsJ_one D hp1]
  have ht : ∀ J : Finset D.cut.Half,
      conj (if J ⊆ D.Nset k then (1 : ℂ) else 0) * (if J ⊆ D.Nset l then 1 else 0) =
        if J ⊆ D.Nset k ∩ D.Nset l then 1 else 0 := by
    intro J
    by_cases hk : J ⊆ D.Nset k <;> by_cases hl : J ⊆ D.Nset l <;> simp [hk, hl, subset_inter_iff]
  simp_rw [ht]
  rw [sum_boole, coverCount_eq_filter]
  rfl

end Sarkozy.SpectralD
