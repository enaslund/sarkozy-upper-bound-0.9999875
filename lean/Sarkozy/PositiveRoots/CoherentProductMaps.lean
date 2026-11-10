module

public import Sarkozy.L20Cap.CoreCount
public import Sarkozy.SpectralC.StarProductLaw
public import Sarkozy.PositiveRoots.CoherentPrivateCompression
public import Sarkozy.PositiveRoots.SquareL20

/-! Core and private raw-star product maps for the actual coherent rectangle. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.L20Cap
open Sarkozy.Cuts Sarkozy.Recentering
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def productFactor {ι : Type*} [DecidableEq ι] (S T : Finset ι) : ℝ :=
  if S = T then 2 else 1

theorem productFactor_nonneg {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    0 ≤ productFactor S T := by unfold productFactor; split_ifs <;> norm_num

theorem productFactor_sq {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    productFactor S T ^ 2 = if S = T then 4 else 1 := by
  unfold productFactor
  split_ifs <;> norm_num

noncomputable def coreProductPrice (p : ℕ) (S T : Finset (Fin 4)) : ℝ :=
  productFactor S T * Real.sqrt (coreCubeDensity p) * (p : ℝ)⁻¹

noncomputable def privateProductPrice (p : ℕ) (S T : Finset (Fin 2)) : ℝ :=
  productFactor S T * Real.sqrt ((p : ℝ) / (p - 1)) * (p : ℝ)⁻¹

theorem core_product_map_sq (hDLK : Target.FourCycle) (hp3 : p % 4 = 3) (hp7 : 7 < p)
    [Nonempty (CoreT (ZMod p))] (S T : Finset (Fin 4))
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : 2 ≤ (S ∪ T).card)
    (F : ZMod p × ZMod p → ℝ) :
    (coreLaw (F := ZMod p)).expect (fun c => recOp ((fieldLaw p).product (fieldLaw p))
      (fun c z => offdiagFeature S T c.val z) F c ^ 2) ≤
      coreProductPrice p S T ^ 2 * nrm ((fieldLaw p).product (fieldLaw p)) F ^ 2 := by
  have h := offdiagFeature_law_sq hDLK (by omega : p ≠ 2) coreLaw
    (fun c : CoreT (ZMod p) => c.val) (fun c => c.property.1)
    (coreCubeDensity_pos hp7).le (coreLaw_cube_comparison hp3 hp7) S T hS hT hST F
  simpa only [coreProductPrice, mul_pow, Real.sq_sqrt (coreCubeDensity_pos hp7).le,
    productFactor_sq, nrm_sq_expect] using h

theorem core_product_gram (hDLK : Target.FourCycle) (hp3 : p % 4 = 3) (hp7 : 7 < p)
    [Nonempty (CoreT (ZMod p))] (S T : Finset (Fin 4))
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : 2 ≤ (S ∪ T).card)
    (f : CoreT (ZMod p) → ℝ) :
    kernelForm coreLaw coreLaw (fun c d => ip ((fieldLaw p).product (fieldLaw p))
      (offdiagFeature S T c.val) (offdiagFeature S T d.val)) f f ≤
      coreProductPrice p S T ^ 2 * nrm coreLaw f ^ 2 := by
  exact gram_le_of_map coreLaw ((fieldLaw p).product (fieldLaw p))
    (fun c : CoreT (ZMod p) => offdiagFeature S T c.val) (sq_nonneg _)
    (core_product_map_sq hDLK hp3 hp7 S T hS hT hST) f

theorem private_pair_injective (b : PairT (ZMod p)) :
    Function.Injective (![b.val.1, b.val.2] : Fin 2 → ZMod p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [b.property, Ne.symm b.property]

theorem private_product_map_sq (hDLK : Target.FourCycle) (hp2 : p ≠ 2)
    [Nonempty (PairT (ZMod p))] (S T : Finset (Fin 2))
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : 2 ≤ (S ∪ T).card)
    (F : ZMod p × ZMod p → ℝ) :
    (pairLaw (F := ZMod p)).expect (fun b => recOp ((fieldLaw p).product (fieldLaw p))
      (fun b z => offdiagFeature S T ![b.val.1, b.val.2] z) F b ^ 2) ≤
      privateProductPrice p S T ^ 2 * nrm ((fieldLaw p).product (fieldLaw p)) F ^ 2 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hD : 0 ≤ (p : ℝ) / (p - 1) := by positivity
  have h := offdiagFeature_law_sq hDLK hp2 pairLaw
    (fun b : PairT (ZMod p) => ![b.val.1, b.val.2]) private_pair_injective hD
    (fun f hf => pairLaw_le_privateCube f hf) S T hS hT hST F
  simpa only [privateProductPrice, mul_pow, Real.sq_sqrt hD,
    productFactor_sq, nrm_sq_expect] using h

theorem private_product_gram (hDLK : Target.FourCycle) (hp2 : p ≠ 2)
    [Nonempty (PairT (ZMod p))] (S T : Finset (Fin 2))
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : 2 ≤ (S ∪ T).card)
    (f : PairT (ZMod p) → ℝ) :
    kernelForm pairLaw pairLaw (fun b d => ip ((fieldLaw p).product (fieldLaw p))
      (offdiagFeature S T ![b.val.1, b.val.2]) (offdiagFeature S T ![d.val.1, d.val.2])) f f ≤
      privateProductPrice p S T ^ 2 * nrm pairLaw f ^ 2 := by
  exact gram_le_of_map pairLaw ((fieldLaw p).product (fieldLaw p))
    (fun b : PairT (ZMod p) => offdiagFeature S T ![b.val.1, b.val.2]) (sq_nonneg _)
    (private_product_map_sq hDLK hp2 S T hS hT hST) f

end Sarkozy.PositiveRoots.CoherentFrame
