module

public import Sarkozy.L20Cap.Stars
public import Sarkozy.L20Cap.GapSplit
public import Sarkozy.L20Cap.Mass

/-!
# The caps of L20 at a prime, with the paper's constants (`prop:l20-collisions`(b))

`paper/sections/20_middle_reference.tex`, `prop:l20-collisions`(b), "The caps", at one prime
`p ≡ 3 (mod 4)` (here: a finite field `F` with `χ(-1) = -1`, `p = |F| ≥ 6`). Notation of
`Sarkozy.L20Cap.Completion`; `q = 1/p`, `r = p^{-1/2}`.

**`l20_prime_caps`** assembles the chain
`prop:l20-pair-gap` (`pair_gap_ranges`) → `‖𝔯‖ ≤ s_p` (`rmass_norm_le` with `Kbar_dev`, Weil) →
`prop:l20-rectangular`(d) (`cutT_lower`, `cutT_perp`) → `prop:l20-completion` (`cutT_upper`,
`soft_eq_nonstar`):
`-C₂₀ ⪯ T ⪯ 1 + χ⁺_p/(1 - H₂₀)`, with
* `η = 2q + 11r`, `s_p = [1 + 4𝔪₊ + (6 + 4η + η²)η² + 256q²(1 + 2𝔪₊ + η²)]^{1/2}/(1 - q)`;
* `c_gap = (τ_g² + x_g²/Δ_g)^{1/2}`, `Δ_g = 30q - l_g²`;
* `h_p = P(Avoid) = (1 - 4q)(1 - 5q)/(1 - q)` (`hP_eq`);
* `ε_Z = N_ns + D_bal + m_⋆`, `C₂₀ = (s_p c_gap/h_p + D_bal)/(1 - ε_Z)`,
  `H₂₀ = (N_ns + D_bal)/(1 - ε_Z)`.

Inputs (hypotheses; the paper's sources in parentheses): `thm:weil` (`WeilBound`, H1);
`m_𝖪 ≤ 𝔪₊` (`prop:l20-rank4`, from `lem:l20-star-mean`); the three bounds of the proof of
`prop:l20-pair-gap` (`τ_g` on the range of `𝐯'`, `l_g` on its complement, `x_g` across; the
splitting itself is `pair_split`); `‖T_coll‖ ≤ D_bal` (`prop:l20-collisions`(a) via
`cor:incident-weights`); the star-mean bound `|⟨𝟙, (stars)𝟙⟩| ≤ m_⋆` (`lem:l20-star-mean`),
which gives `Z₀ ≥ 1 - ε_Z`, `ε_Z = N_ns + D_bal + m_⋆` (`Z0_lower`); the raw nonstar cap
`‖T_ns‖ ≤ N_ns` (`cor:extraction-compressed`; the
star terms vanish on `𝓘 ∩ 𝟙^⊥` by `soft_eq_nonstar`); `‖T𝟙 - 𝟙‖² ≤ χ⁺_p`
(`lem:record:root-marginal`(ii)); the gates `c_gap ≤ s_p` (the paper has `c_gap < 1 ≤ s_p`),
`C₂₀ < 1`, `H₂₀ < 1`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (CoreT F)]
  [Nonempty (PairT F)]

/-- `η = 2q + 11r`. -/
noncomputable def etaL (F : Type*) [Fintype F] : ℝ :=
  2 / (Fintype.card F : ℝ) + 11 / Real.sqrt (Fintype.card F)

/-- `s_p` of `prop:l20-rectangular`(d), with `𝔪₊ = m`. -/
noncomputable def sP (F : Type*) [Fintype F] (m : ℝ) : ℝ :=
  Real.sqrt (1 + 4 * m + (6 + 4 * etaL F + etaL F ^ 2) * etaL F ^ 2 +
    256 * (Fintype.card F : ℝ)⁻¹ ^ 2 * (1 + 2 * m + etaL F ^ 2)) / (1 - (Fintype.card F : ℝ)⁻¹)

/-- `c_gap = (τ_g² + x_g²/Δ_g)^{1/2}`, `Δ_g = 30q - l_g²`. -/
noncomputable def cGap (q τg lg xg : ℝ) : ℝ := Real.sqrt (τg ^ 2 + xg ^ 2 / (30 * q - lg ^ 2))

/-- **The caps of L20 at a prime** (`prop:l20-collisions`(b), "The caps"):
`-C₂₀ ⪯ T ⪯ 1 + χ⁺_p/(1 - H₂₀)` on `L²(μ_p)`, with the constants of the paper (see the module
docstring), `ε_Z = N_ns + D_bal + m_⋆`. -/
theorem l20_prime_caps (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2)
    (hW : WeilBound F) (h6 : 6 ≤ Fintype.card F) {m τg lg xg D mstar Nns χp : ℝ}
    (hm : (coreLaw (F := F)).expect (fun C => Kbar C.1 - 1) ≤ m)
    (hτq : 30 * (Fintype.card F : ℝ)⁻¹ ≤ τg ^ 2) (hΔ : 0 < 30 * (Fintype.card F : ℝ)⁻¹ - lg ^ 2)
    (hl : 0 ≤ lg) (hx : 0 ≤ xg)
    (hA : ∀ h : F → ℝ, ∑ z, h z = 0 →
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc (vOp h)) ≤
        τg * nrm (pairLaw (F := F)) (vOp h))
    (hB : ∀ g : PairT F → ℝ, (pairLaw (F := F)).expect g = 0 →
      (∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) →
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc g) ≤ lg * nrm (pairLaw (F := F)) g)
    (hC : ∀ (h : F → ℝ) (g : PairT F → ℝ), ∑ z, h z = 0 → (pairLaw (F := F)).expect g = 0 →
      (∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) →
      |ip (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc (vOp h))
          (recOp (pairLaw (F := F)) Rc g)| ≤
        xg * nrm (pairLaw (F := F)) (vOp h) * nrm (pairLaw (F := F)) g)
    (hgate : cGap (Fintype.card F : ℝ)⁻¹ τg lg xg ≤ sP F m)
    (hD0 : 0 ≤ D)
    (hD : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) collK f f| ≤ D * nrm (halfLaw h6) f ^ 2)
    (hNns0 : 0 ≤ Nns)
    (hns : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) nonstar f f| ≤ Nns * nrm (halfLaw h6) f ^ 2)
    (hstar : |kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => starPart6 (labels x) (labels x')) (fun _ => 1) (fun _ => 1)| ≤ mstar)
    (hεZ : Nns + D + mstar < 1)
    (hχ0 : 0 ≤ χp)
    (hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp)
    (hC1 : (sP F m * cGap (Fintype.card F : ℝ)⁻¹ τg lg xg /
      prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid + D) /
        (1 - (Nns + D + mstar)) < 1)
    (hH1 : (Nns + D) / (1 - (Nns + D + mstar)) < 1) (f : CoreT F × PairT F → ℝ) :
    -((sP F m * cGap (Fintype.card F : ℝ)⁻¹ τg lg xg /
        prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid + D) /
          (1 - (Nns + D + mstar))) *
        nrm (halfLaw h6) f ^ 2 ≤ kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ∧
      kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ≤
        (1 + χp / (1 - (Nns + D) / (1 - (Nns + D + mstar)))) * nrm (halfLaw h6) f ^ 2 := by
  have hRc : ∀ h : PairT F → ℝ, nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc h) ≤
      cGap (Fintype.card F : ℝ)⁻¹ τg lg xg * nrm (pairLaw (F := F)) h :=
    fun h => pair_gap_ranges (by omega) hl hx hτq hΔ hA hB hC h
  have hs : nrm (coreLaw (F := F)) rmass ≤ sP F m :=
    rmass_norm_le hm1 (fun C => Kbar_dev hF hW C.2.1) hm
  have hZ := Z0_lower h6 hns hD hstar
  exact cutT_caps_ns hm1 h6 (Real.sqrt_nonneg _) hRc hs hgate hD0 hD hεZ hZ hNns0 hns hχ0 hchi
    hC1 hH1 f

end Sarkozy.L20Cap
