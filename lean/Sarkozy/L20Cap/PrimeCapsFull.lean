module

public import Sarkozy.L20Cap.PrimeCapsNA
public import Sarkozy.L20Cap.GapRange

/-!
# The caps of L20 at a prime, with `τ_g` proved (`prop:l20-collisions`(b))

`l20_prime_caps_full` is `l20_prime_caps_NA` with the range bound of `prop:l20-pair-gap` proved
(`hA_proved`): `τ_g² = 2qM_g/((1 - q)²(1 - 2q))`, `M_g = 15 + 44𝔪₊ + (42 + 12η)η²`,
`η = 2q + 11r` (`Kbar_dev`, Weil). Of the three block bounds of `prop:l20-pair-gap` only the
cross bound `x_g` (`hC`) remains a hypothesis; the complement bound comes from the nonstar
remainder `N_A` (`hN`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (CoreT F)]
  [Nonempty (PairT F)]

/-- `τ_g = (2qM_g/((1 - q)²(1 - 2q)))^{1/2}` with `M_g = 15 + 44𝔪 + (42 + 12η)η²`,
`η = 2q + 11r`. -/
noncomputable def tauG (F : Type*) [Fintype F] (m : ℝ) : ℝ :=
  Real.sqrt (2 * (Fintype.card F : ℝ)⁻¹ * (15 + 44 * m + (42 + 12 * etaL F) * etaL F ^ 2) /
    ((1 - (Fintype.card F : ℝ)⁻¹) ^ 2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹)))

/-- **The caps of L20 at a prime** (`prop:l20-collisions`(b), "The caps"), with `‖𝔯‖ ≤ s_p`,
the range bound `τ_g` and the complement bound `l_g = 2r + N_A` of `prop:l20-pair-gap` proved:
`-C₂₀ ⪯ T ⪯ 1 + χ⁺_p/(1 - H₂₀)`. -/
theorem l20_prime_caps_full (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2)
    (hW : WeilBound F) (h6 : 6 ≤ Fintype.card F) {m NA xg D mstar Nns χp : ℝ}
    (hm : (coreLaw (F := F)).expect (fun C => Kbar C.1 - 1) ≤ m) (hm0 : 0 ≤ m)
    (hΔ : 0 < 30 * (Fintype.card F : ℝ)⁻¹ - (2 * (Real.sqrt (Fintype.card F))⁻¹ + NA) ^ 2)
    (hNA : 0 ≤ NA) (hx : 0 ≤ xg)
    (hN : ∀ g : PairT F → ℝ, (pairLaw (F := F)).expect g = 0 →
      (∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) →
      nrm (coreLaw (F := F)) (fun C => (pairLaw (F := F)).expect (fun b => Nrect C b * g b)) ≤
        NA * nrm (pairLaw (F := F)) g)
    (hC : ∀ (h : F → ℝ) (g : PairT F → ℝ), ∑ z, h z = 0 → (pairLaw (F := F)).expect g = 0 →
      (∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) →
      |ip (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc (vOp h))
          (recOp (pairLaw (F := F)) Rc g)| ≤
        xg * nrm (pairLaw (F := F)) (vOp h) * nrm (pairLaw (F := F)) g)
    (hgate : cGap (Fintype.card F : ℝ)⁻¹ (tauG F m) (2 * (Real.sqrt (Fintype.card F))⁻¹ + NA) xg ≤
      sP F m)
    (hD0 : 0 ≤ D)
    (hD : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) collK f f| ≤ D * nrm (halfLaw h6) f ^ 2)
    (hNns0 : 0 ≤ Nns)
    (hns : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) nonstar f f| ≤ Nns * nrm (halfLaw h6) f ^ 2)
    (hstar : |kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => starPart6 (labels x) (labels x')) (fun _ => 1) (fun _ => 1)| ≤ mstar)
    (hεZ : Nns + D + mstar < 1)
    (hχ0 : 0 ≤ χp)
    (hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp)
    (hC1 : (sP F m * cGap (Fintype.card F : ℝ)⁻¹ (tauG F m)
        (2 * (Real.sqrt (Fintype.card F))⁻¹ + NA) xg /
      prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid + D) /
        (1 - (Nns + D + mstar)) < 1)
    (hH1 : (Nns + D) / (1 - (Nns + D + mstar)) < 1) (f : CoreT F × PairT F → ℝ) :
    -((sP F m * cGap (Fintype.card F : ℝ)⁻¹ (tauG F m)
        (2 * (Real.sqrt (Fintype.card F))⁻¹ + NA) xg /
        prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid + D) /
          (1 - (Nns + D + mstar))) *
        nrm (halfLaw h6) f ^ 2 ≤ kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ∧
      kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ≤
        (1 + χp / (1 - (Nns + D) / (1 - (Nns + D + mstar)))) * nrm (halfLaw h6) f ^ 2 := by
  have hp6 : (6 : ℝ) ≤ Fintype.card F := by exact_mod_cast h6
  have hp0 : (0 : ℝ) < Fintype.card F := by linarith
  have hq0 : 0 < (Fintype.card F : ℝ)⁻¹ := inv_pos.mpr hp0
  have hq6 : (Fintype.card F : ℝ)⁻¹ ≤ 1 / 6 := by rw [one_div]; exact inv_anti₀ (by norm_num) hp6
  have hη0 : 0 ≤ etaL F := by unfold etaL; positivity
  have hMg : 15 ≤ 15 + 44 * m + (42 + 12 * etaL F) * etaL F ^ 2 := by
    have : 0 ≤ (42 + 12 * etaL F) * etaL F ^ 2 := by positivity
    linarith
  have hτ : tauG F m ^ 2 = 2 * (Fintype.card F : ℝ)⁻¹ *
      (15 + 44 * m + (42 + 12 * etaL F) * etaL F ^ 2) /
        ((1 - (Fintype.card F : ℝ)⁻¹) ^ 2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹)) := by
    unfold tauG
    rw [Real.sq_sqrt]
    have h1 : 0 < 1 - (Fintype.card F : ℝ)⁻¹ := by linarith
    have h2 : 0 < 1 - 2 * (Fintype.card F : ℝ)⁻¹ := by linarith
    positivity
  have hτq : 30 * (Fintype.card F : ℝ)⁻¹ ≤ tauG F m ^ 2 := by
    rw [hτ]
    exact tau_sq_ge hq0 (by linarith) hMg
  have hA : ∀ h : F → ℝ, ∑ z, h z = 0 →
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc (vOp h)) ≤
        tauG F m * nrm (pairLaw (F := F)) (vOp h) :=
    fun h h0 => hA_proved hm1 (by omega) (fun C => Kbar_dev hF hW C.2.1) hm h h0
  exact l20_prime_caps_NA hm1 hF hW h6 hm hτq hΔ hNA hx hA hN hC hgate hD0 hD hNns0 hns hstar hεZ
    hχ0 hchi hC1 hH1 f

end Sarkozy.L20Cap
