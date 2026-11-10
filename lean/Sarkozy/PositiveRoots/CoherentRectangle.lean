module

public import Sarkozy.PositiveRoots.CoherentProductMaps
public import Sarkozy.Cuts.SwappedDecorated

/-! The two whole-rectangle estimates used for off-diagonal coherent covariance. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.Cuts Sarkozy.Recentering Sarkozy.L20Cap Sarkozy.SpectralC.TwoLabel
open scoped BigOperators

section General

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]

theorem decorated_rectangle_norm (α : FiniteLaw X) (hα : ∀ x, 0 < α.weight x)
    (β : FiniteLaw Y) (π : FiniteLaw Z) (A : X → Y → ℝ)
    (φ φ' : X → Z → ℝ) (ψ ψ' : Y → Z → ℝ)
    (hψ : ∀ y z, |ψ y z| ≤ 1) (hψ' : ∀ y z, |ψ' y z| ≤ 1)
    {R c c' : ℝ} (hR : 0 ≤ R) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hrow : ∀ x, β.expect (fun y => A x y ^ 2) ≤ R)
    (hφ : ∀ f, kernelForm α α (fun x x' => ip π (φ x) (φ x')) f f ≤ c ^ 2 * nrm α f ^ 2)
    (hφ' : ∀ f, kernelForm α α (fun x x' => ip π (φ' x) (φ' x')) f f ≤ c' ^ 2 * nrm α f ^ 2)
    (F G : X × Y → ℝ) :
    |kernelForm (α.product β) (α.product β)
      (fun x y => A x.1 y.2 * A y.1 x.2 *
        ip π (fun z => φ x.1 z * ψ x.2 z) (fun z => φ' y.1 z * ψ' y.2 z)) F G| ≤
      R * c * c' * nrm (α.product β) F * nrm (α.product β) G := by
  have he (d : ℝ) (hd : 0 ≤ d) : Real.sqrt (R * d ^ 2) = Real.sqrt R * d := by
    rw [Real.sqrt_mul hR, Real.sqrt_sq hd]
  have h := swap_decorated_multiplier_norm α β π A φ φ' ψ ψ' hψ hψ'
    (Real.sqrt_nonneg (R * c ^ 2)) (Real.sqrt_nonneg (R * c' ^ 2))
    (prodMap_norm α hα β π A φ hrow (sq_nonneg c) hφ)
    (prodMap_norm α hα β π A φ' hrow (sq_nonneg c') hφ') F G
  rw [he c hc, he c' hc'] at h
  have hs := Real.sq_sqrt hR
  convert h using 1
  ring_nf at hs ⊢
  rw [hs]

end General

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem coreProductPrice_nonneg (S T : Finset (Fin 4)) : 0 ≤ coreProductPrice p S T :=
  mul_nonneg (mul_nonneg (productFactor_nonneg S T) (Real.sqrt_nonneg _)) (by positivity)

omit [Fact p.Prime] in
theorem privateProductPrice_nonneg (S T : Finset (Fin 2)) : 0 ≤ privateProductPrice p S T :=
  mul_nonneg (mul_nonneg (productFactor_nonneg S T) (Real.sqrt_nonneg _)) (by positivity)

theorem core_rectangle_bound (hDLK : Target.FourCycle) (hp3 : p % 4 = 3) (hp7 : 7 < p)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (A : CoreT (ZMod p) → PairT (ZMod p) → ℝ)
    (S T U V : Finset (Fin 4)) (hS : S.Nonempty) (hT : T.Nonempty)
    (hU : U.Nonempty) (hV : V.Nonempty) (hST : 2 ≤ (S ∪ T).card) (hUV : 2 ≤ (U ∪ V).card)
    (ψ ψ' : PairT (ZMod p) → ZMod p × ZMod p → ℝ)
    (hψ : ∀ b z, |ψ b z| ≤ 1) (hψ' : ∀ b z, |ψ' b z| ≤ 1)
    {R : ℝ} (hR : 0 ≤ R) (hrow : ∀ c, pairLaw.expect (fun b => A c b ^ 2) ≤ R)
    (F G : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
      (fun x y => A x.1 y.2 * A y.1 x.2 *
        ip ((fieldLaw p).product (fieldLaw p))
          (fun z => offdiagFeature S T x.1.val z * ψ x.2 z)
          (fun z => offdiagFeature U V y.1.val z * ψ' y.2 z)) F G| ≤
      (R * coreCubeDensity p * (p : ℝ)⁻¹ ^ 2 * productFactor S T * productFactor U V) *
        nrm (coreLaw.product pairLaw) F * nrm (coreLaw.product pairLaw) G := by
  have h := decorated_rectangle_norm coreLaw coreLaw_pos pairLaw
    ((fieldLaw p).product (fieldLaw p)) A
    (fun c : CoreT (ZMod p) => offdiagFeature S T c.val)
    (fun c : CoreT (ZMod p) => offdiagFeature U V c.val) ψ ψ' hψ hψ'
    hR (coreProductPrice_nonneg S T) (coreProductPrice_nonneg U V) hrow
    (core_product_gram hDLK hp3 hp7 S T hS hT hST)
    (core_product_gram hDLK hp3 hp7 U V hU hV hUV) F G
  have hs := Real.sq_sqrt (coreCubeDensity_pos hp7).le
  unfold coreProductPrice at h
  convert h using 1
  ring_nf at hs ⊢
  rw [hs]
  ring

theorem private_rectangle_bound (hDLK : Target.FourCycle) (hp2 : p ≠ 2)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (A : PairT (ZMod p) → CoreT (ZMod p) → ℝ)
    (S T U V : Finset (Fin 2)) (hS : S.Nonempty) (hT : T.Nonempty)
    (hU : U.Nonempty) (hV : V.Nonempty) (hST : 2 ≤ (S ∪ T).card) (hUV : 2 ≤ (U ∪ V).card)
    (ψ ψ' : CoreT (ZMod p) → ZMod p × ZMod p → ℝ)
    (hψ : ∀ c z, |ψ c z| ≤ 1) (hψ' : ∀ c z, |ψ' c z| ≤ 1)
    {R : ℝ} (hR : 0 ≤ R) (hrow : ∀ b, coreLaw.expect (fun c => A b c ^ 2) ≤ R)
    (F G : PairT (ZMod p) × CoreT (ZMod p) → ℝ) :
    |kernelForm (pairLaw.product coreLaw) (pairLaw.product coreLaw)
      (fun x y => A x.1 y.2 * A y.1 x.2 *
        ip ((fieldLaw p).product (fieldLaw p))
          (fun z => offdiagFeature S T ![x.1.val.1, x.1.val.2] z * ψ x.2 z)
          (fun z => offdiagFeature U V ![y.1.val.1, y.1.val.2] z * ψ' y.2 z)) F G| ≤
      (R * ((p : ℝ) / (p - 1)) * (p : ℝ)⁻¹ ^ 2 * productFactor S T * productFactor U V) *
        nrm (pairLaw.product coreLaw) F * nrm (pairLaw.product coreLaw) G := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpos (b : PairT (ZMod p)) : 0 < (pairLaw (F := ZMod p)).weight b := by
    change 0 < (Fintype.card (PairT (ZMod p)) : ℝ)⁻¹
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have h := decorated_rectangle_norm pairLaw hpos coreLaw
    ((fieldLaw p).product (fieldLaw p)) A
    (fun b : PairT (ZMod p) => offdiagFeature S T ![b.val.1, b.val.2])
    (fun b : PairT (ZMod p) => offdiagFeature U V ![b.val.1, b.val.2]) ψ ψ' hψ hψ'
    hR (privateProductPrice_nonneg S T) (privateProductPrice_nonneg U V) hrow
    (private_product_gram hDLK hp2 S T hS hT hST)
    (private_product_gram hDLK hp2 U V hU hV hUV) F G
  have hs := Real.sq_sqrt (by positivity : 0 ≤ (p : ℝ) / (p - 1))
  unfold privateProductPrice at h
  convert h using 1
  ring_nf at hs ⊢
  rw [hs]

end Sarkozy.PositiveRoots.CoherentFrame
