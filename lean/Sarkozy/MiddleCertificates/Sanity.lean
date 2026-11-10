module

public import Sarkozy.MiddleCertificates.Main

/-!
# Sanity checks for the middle certificates (C8)

* the sizes: `|U⁺| = 3` (L10) and `6` (L21), `|E_×| = 4` and `12`, and `16` nonzero entries of
  `D₂₀` (the power `2¹⁶` of `K0_eq_cutK`);
* `routeALower_iff`, `routeAUpper_iff`: since the finite tests are proved for every `ξ`, the open
  fields of `MidPrimeInputs` are exactly the per-prime statements (a) and (d) of
  `thm:spectral-criterion` at the recorded constants; they are not satisfied through a false
  antecedent;
* `lam_attained`: `λ̄(𝐇)` is the largest eigenvalue of `𝐇` (an eigenvector with that eigenvalue).
-/

@[expose] public section

namespace Sarkozy.MiddleCertificates

open Finset Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.SpectralD.Cx MidCut
open scoped InnerProductSpace

theorem card_half_l10 : Fintype.card MidCut.l10.data.cut.Half = 3 := by decide

theorem card_half_l21 : Fintype.card MidCut.l21.data.cut.Half = 6 := by decide

theorem card_cross (c : MidCut) :
    c.data.crossPairs.card = if c = .l10 then 4 else 12 := by
  rw [crossPairs_eq_edgeCrossPairs c.data c.edge (mem_edge c)]
  cases c <;> decide

theorem card_crossDZ :
    (univ.filter (fun ij : Fin 6 × Fin 6 => crossDZ ij.1 ij.2 ≠ 0)).card = 16 := by decide

/-- The eigenvectors of `𝐇` at `λ̄`: `(0, 1, 0)` for L10, `(1, 0, -1, 0, 0, 0)` for L21. -/
theorem lam_attained :
    (∀ a : MidCut.l10.data.cut.Half,
      ∑ b, modelH .l10 a b * (if MidCut.l10.code b.1 = 1 then 1 else 0) =
        3 * (if MidCut.l10.code a.1 = 1 then 1 else 0)) ∧
    (∀ a : MidCut.l21.data.cut.Half,
      ∑ b, modelH .l21 a b * (if MidCut.l21.code b.1 = 0 then 1 else
        if MidCut.l21.code b.1 = 2 then -1 else 0) =
        4 * (if MidCut.l21.code a.1 = 0 then 1 else if MidCut.l21.code a.1 = 2 then -1 else 0)) := by
  constructor <;> decide +kernel

variable {p : ℕ} [Fact p.Prime]

/-- The open field `lower` of `MidPrimeInputs` is exactly `thm:spectral-criterion`(a) at `p`. -/
theorem routeALower_iff (c : MidCut) (i : Fin 33) (hp3 : p % 4 = 3) :
    RouteALower (p := p) c.data (FiniteModel.Adj c.edge c.data.cut) (cbar c i) (tau c i)
        (etaQ c i) (etaB c i) (epsV c i) ↔
      ∀ (hne : (Labellings.injLabellings (ZMod p) c.data.G).Nonempty) (g : ℝ),
        ((cbar c i : ℝ) + tau c i) / (1 - epsV c i) ≤ g →
        ∀ f : EuclideanSpace ℝ (c.data.cut.Half → ZMod p),
          -(g * rp p) * ‖f‖ ^ 2 ≤ ⟪f, Spectral.cutOp c.data hne f⟫_ℝ := by
  constructor
  · intro h hne g hg f
    exact h hne g (fun ξ => finiteTest_three c i hp3 ξ) hg f
  · intro h hne g _ hg f
    exact h hne g hg f

/-- The open field `upper` of `MidPrimeInputs` is exactly `thm:spectral-criterion`(d) at `p`. -/
theorem routeAUpper_iff (c : MidCut) (i : Fin 33) (hp3 : p % 4 = 3) (hX : PartV.pieceStart i ≤ p) :
    RouteAUpper (p := p) c.data (FiniteModel.Adj c.edge c.data.cut) (cbar c i) (tau c i)
        (etaQ c i) (etaB c i) (epsV c i) (BlockSpecPaper.AllpData.allpG i c.allpIdx)
        (BlockSpecPaper.AllpData.allpB i c.allpIdx) ↔
      ∀ (hne : (Labellings.injLabellings (ZMod p) c.data.G).Nonempty)
        (f : EuclideanSpace ℝ (c.data.cut.Half → ZMod p)),
          ⟪f, Spectral.cutOp c.data hne f⟫_ℝ ≤
            (1 + (BlockSpecPaper.AllpData.allpB i c.allpIdx : ℝ) / p) * ‖f‖ ^ 2 := by
  constructor
  · intro h hne f
    exact h hne (fun ξ => finiteTest_three c i hp3 ξ) (fun ξ => finiteTest_three_neg c i hp3 ξ)
      (g_le_allpG c i).1 (BlockAdapter.allpG_mul_lt_one i c.allpIdx hX) f
  · intro h hne _ _ _ _ f
    exact h hne f

end Sarkozy.MiddleCertificates
