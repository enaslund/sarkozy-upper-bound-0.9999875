module

public import Sarkozy.L20Cap.PrimeCaps
public import Sarkozy.L20Cap.GapComplement

/-!
# The caps of L20 at a prime, with the nonstar remainder `N_A` (`prop:l20-collisions`(b))

`l20_prime_caps_NA` is `l20_prime_caps` with the complement bound of `prop:l20-pair-gap` derived
(`hB_of_nonstar`): `l_g = 2r + N_A`, where `N_A` bounds the nonstar part
`C ↦ E_b[N(C; b)g(b)]` of `𝖱` on the complement of the range of `𝐯'` (`prop:l20-rectangular`(b);
the raw cap of `cor:soft-kernels`(a) or `thm:rectangle-gram`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (CoreT F)]
  [Nonempty (PairT F)]

/-- **The caps of L20 at a prime, with `l_g = 2r + N_A`** (`prop:l20-collisions`(b),
`prop:l20-pair-gap`): `-C₂₀ ⪯ T ⪯ 1 + χ⁺_p/(1 - H₂₀)`. -/
theorem l20_prime_caps_NA (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2)
    (hW : WeilBound F) (h6 : 6 ≤ Fintype.card F) {m τg NA xg D mstar Nns χp : ℝ}
    (hm : (coreLaw (F := F)).expect (fun C => Kbar C.1 - 1) ≤ m)
    (hτq : 30 * (Fintype.card F : ℝ)⁻¹ ≤ τg ^ 2)
    (hΔ : 0 < 30 * (Fintype.card F : ℝ)⁻¹ - (2 * (Real.sqrt (Fintype.card F))⁻¹ + NA) ^ 2)
    (hNA : 0 ≤ NA) (hx : 0 ≤ xg)
    (hA : ∀ h : F → ℝ, ∑ z, h z = 0 →
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc (vOp h)) ≤
        τg * nrm (pairLaw (F := F)) (vOp h))
    (hN : ∀ g : PairT F → ℝ, (pairLaw (F := F)).expect g = 0 →
      (∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) →
      nrm (coreLaw (F := F)) (fun C => (pairLaw (F := F)).expect (fun b => Nrect C b * g b)) ≤
        NA * nrm (pairLaw (F := F)) g)
    (hC : ∀ (h : F → ℝ) (g : PairT F → ℝ), ∑ z, h z = 0 → (pairLaw (F := F)).expect g = 0 →
      (∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) →
      |ip (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc (vOp h))
          (recOp (pairLaw (F := F)) Rc g)| ≤
        xg * nrm (pairLaw (F := F)) (vOp h) * nrm (pairLaw (F := F)) g)
    (hgate : cGap (Fintype.card F : ℝ)⁻¹ τg (2 * (Real.sqrt (Fintype.card F))⁻¹ + NA) xg ≤ sP F m)
    (hD0 : 0 ≤ D)
    (hD : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) collK f f| ≤ D * nrm (halfLaw h6) f ^ 2)
    (hNns0 : 0 ≤ Nns)
    (hns : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) nonstar f f| ≤ Nns * nrm (halfLaw h6) f ^ 2)
    (hstar : |kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => starPart6 (labels x) (labels x')) (fun _ => 1) (fun _ => 1)| ≤ mstar)
    (hεZ : Nns + D + mstar < 1)
    (hχ0 : 0 ≤ χp)
    (hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp)
    (hC1 : (sP F m * cGap (Fintype.card F : ℝ)⁻¹ τg (2 * (Real.sqrt (Fintype.card F))⁻¹ + NA) xg /
      prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid + D) /
        (1 - (Nns + D + mstar)) < 1)
    (hH1 : (Nns + D) / (1 - (Nns + D + mstar)) < 1) (f : CoreT F × PairT F → ℝ) :
    -((sP F m * cGap (Fintype.card F : ℝ)⁻¹ τg (2 * (Real.sqrt (Fintype.card F))⁻¹ + NA) xg /
        prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid + D) /
          (1 - (Nns + D + mstar))) *
        nrm (halfLaw h6) f ^ 2 ≤ kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ∧
      kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ≤
        (1 + χp / (1 - (Nns + D) / (1 - (Nns + D + mstar)))) * nrm (halfLaw h6) f ^ 2 := by
  have hl : 0 ≤ 2 * (Real.sqrt (Fintype.card F))⁻¹ + NA :=
    add_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr (Real.sqrt_nonneg _))) hNA
  exact l20_prime_caps hm1 hF hW h6 hm hτq hΔ hl hx hA
    (fun g hg0 horth => hB_of_nonstar hm1 hF (by omega) hN g hg0 horth) hC hgate hD0 hD hNns0 hns
    hstar hεZ hχ0 hchi hC1 hH1 f

end Sarkozy.L20Cap
