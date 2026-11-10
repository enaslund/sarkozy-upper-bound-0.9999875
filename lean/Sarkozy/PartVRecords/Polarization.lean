module

public import Sarkozy.PartVRecords.OneStageBlock
public import Sarkozy.FiveType.PolarizationOrders

@[expose] public section

/-!
# The polarized first stage (`lem:middle-polarization`, (CP2)(a) at `ϑ₀`)

`paper/sections/20c_middle_frame.tex`, `lem:middle-polarization`. For every middle block,
`E_add + G - F_fold ⪰_{ϑ₀} 0`; hence `ρ_𝔅 ⪰_{ϑ₀} μ_𝔅` (and `⪰_{ϑ₀} 0` when `μ_𝔅` is), which is
(CP2)(a) at the cut `ϑ₀ = firstChamberCut 0`, with the variation price of the positive records
`F_fold`, `E_add`, `G` (`Prices.rho_sub_mu_eq`, `Prices.price_first_stage`).

The proof is the paper's: the one-layer data form a five-type datum (V1's `DatumHyp` and
`fieldDatum`; for the block laws `middleBlock_datumHyp₁`) whose rows satisfy
`‖T_F^ξ - J‖ ≤ f₁ r`, `‖T_E^ξ - J‖ ≤ h₁ r` (`lem:front12:reference`(i) with `j = 1`, V1's
`RowBounds`, **a hypothesis**); C1's `lem:tr:polarization`(a) (`Datum.polarization_a`) with
`ε = (f₁ + h₁) r` gives
`Π⁽¹⁾_{E₀} + Π⁽¹⁾_{E₁} + ε (Π⁽¹⁾_{G₀₀} + Π⁽¹⁾_{G₁₁}) ⪰_{ϑ₀} Π⁽¹⁾_{F₁} + Π⁽¹⁾_{F₂}`;
the diagonal copy preserves the order (V1's `pushL_firstCut_positive`), and multiplying by the
record weight `v_D r²` gives `E_add + G ⪰_{ϑ₀} F_fold` (`Eadd_Gpol_sub_Ffold_positive`).

The identification of each one-layer frame record with the push-forward of the datum's
component (`diag_S_eq`, `diag_D_eq`, `diag_R_eq`) is V1's `emit_midDiag_eq` with `lawL_merge`.
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.Labellings Sarkozy.PartV Sarkozy.TheoremC Sarkozy.FiveType

variable {X : Type} [Fintype X] [DecidableEq X]

namespace FrameData

variable (D : FrameData X)

/-- The one-layer matching record is the push-forward of the datum's `Π_{E_s}`. -/
theorem diag_S_eq (h₁ : DatumHyp (D.F.one .E) (D.F.one .F) (D.F.one .L)) (s : Fin 2) :
    D.diag .S s = pushL ((fieldDatum h₁).compE s) toSlot₁ := by
  change signedIntegral (emit (D.F.one .E) (midDiagEmission (matching s))).weight = _
  rw [emit_midDiag_eq]
  rfl

/-- The one-layer fold record is the push-forward of the datum's `Π_{F_j}`. -/
theorem diag_D_eq (h₁ : DatumHyp (D.F.one .E) (D.F.one .F) (D.F.one .L)) (j : Fin 3) :
    D.diag .D j = pushL ((fieldDatum h₁).compF j) toSlot₁ := by
  change signedIntegral (emit (D.F.one .F) (midDiagEmission (fold j))).weight = _
  rw [emit_midDiag_eq]
  rfl

/-- The one-layer merge record is the push-forward of the datum's `Π_{G_{sk}}`. -/
theorem diag_R_eq (h₁ : DatumHyp (D.F.one .E) (D.F.one .F) (D.F.one .L)) (s : Fin 2)
    (k : Fin 3) : D.diag .R (s, k) = pushL ((fieldDatum h₁).compG s k) toSlot₁ := by
  change signedIntegral (emit (D.F.one .E)
    (midDiagEmission (fun u => (merge s k u).castSucc))).weight = _
  rw [emit_midDiag_eq]
  change _ = pushL (lawL (patternLaw (merge s k) (gamOf (objLaw (D.F.one .E))))) toSlot₁
  rw [lawL_merge]

/-- `E_add + G - F_fold = v_D r² · e₁(𝒬^E_ε - 𝒬^F)` with `ε = (f₁ + h₁) r`, `e₁` the diagonal
copy. -/
theorem Eadd_Gpol_sub_Ffold_eq (h₁ : DatumHyp (D.F.one .E) (D.F.one .F) (D.F.one .L)) :
    D.Eadd + D.Gpol - D.Ffold = (D.W.v .D * D.r ^ 2) •
      pushL ((fieldDatum h₁).QE ((D.I.f₁ + D.I.h₁) * D.r) - (fieldDatum h₁).QF) toSlot₁ := by
  have hS0 := D.diag_S_eq h₁ 0
  have hS1 := D.diag_S_eq h₁ 1
  have hD1 := D.diag_D_eq h₁ 1
  have hD2 := D.diag_D_eq h₁ 2
  have hR0 := D.diag_R_eq h₁ 0 0
  have hR1 := D.diag_R_eq h₁ 1 1
  apply LinearMap.ext
  intro f
  simp only [Eadd, Gpol, Ge, Go, Ffold, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hS0, hS1, hD1, hD2, hR0, hR1, pushL_apply, Datum.QE,
    Datum.QF]
  ring

/-- **`lem:middle-polarization`: `E_add + G - F_fold ⪰_{ϑ₀} 0`**, given the one-layer datum
hypotheses and the rows of `lem:front12:reference`(i) with `j = 1`. -/
theorem Eadd_Gpol_sub_Ffold_positive (h₁ : DatumHyp (D.F.one .E) (D.F.one .F) (D.F.one .L))
    (hrows : RowBounds (fieldDatum h₁) D.I.f₁ D.I.h₁ D.r) :
    (firstChamberCut 0).Positive (D.Eadd + D.Gpol - D.Ffold) := by
  have hpol : (chamberCut 0).Below (fieldDatum h₁).QF
      ((fieldDatum h₁).QE ((D.I.f₁ + D.I.h₁) * D.r)) :=
    (fieldDatum h₁).polarization_a (eF := D.I.f₁ * D.r) (eE := D.I.h₁ * D.r)
      (fun b hb => (hrows b hb).1) (fun b hb => (hrows b hb).2) (le_of_eq (by ring))
  have hpush : (firstChamberCut 0).Positive
      (pushL ((fieldDatum h₁).QE ((D.I.f₁ + D.I.h₁) * D.r) - (fieldDatum h₁).QF) toSlot₁) :=
    pushL_firstCut_positive (fun y _ => y 0) _ 0 hpol
  rw [D.Eadd_Gpol_sub_Ffold_eq h₁]
  exact hpush.smul (D.coef2_nonneg _)

/-- **(CP2)(a) at `ϑ₀`: `ρ_𝔅 ⪰_{ϑ₀} μ_𝔅`** (`lem:middle-polarization`), with
`ρ_𝔅 - μ_𝔅 = (E_add + G - F_fold)/P(r)` a real combination of the positive records `F_fold`,
`E_add`, `G` (`rho_sub_mu_eq`). -/
theorem rho_ge_mu (h₁ : DatumHyp (D.F.one .E) (D.F.one .F) (D.F.one .L))
    (hrows : RowBounds (fieldDatum h₁) D.I.f₁ D.I.h₁ D.r) :
    (firstChamberCut 0).Below D.mu D.rho := by
  change (firstChamberCut 0).Positive (D.rho - D.mu)
  rw [D.rho_sub_mu]
  exact (D.Eadd_Gpol_sub_Ffold_positive h₁ hrows).smul (inv_nonneg.mpr D.P_pos.le)

/-- `ρ_𝔅 ⪰_{ϑ₀} 0` when the reference is positive at `ϑ₀` (`lem:front12:reference`). -/
theorem rho_positive (h₁ : DatumHyp (D.F.one .E) (D.F.one .F) (D.F.one .L))
    (hrows : RowBounds (fieldDatum h₁) D.I.f₁ D.I.h₁ D.r)
    (hμ : (firstChamberCut 0).Positive D.mu) : (firstChamberCut 0).Positive D.rho := by
  have h := hμ.add (D.rho_ge_mu h₁ hrows)
  have e : D.mu + (D.rho - D.mu) = D.rho := by abel
  rwa [e] at h

end FrameData

/-! ## The middle block -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **`lem:middle-polarization` on a middle block**: with V1's block field laws the one-layer datum
hypotheses hold (`middleBlock_datumHyp₁`), so `ρ_𝔅 ⪰_{ϑ₀} μ_𝔅` as soon as the rows of
`lem:front12:reference`(i) with `j = 1` hold. -/
theorem middleFrame_rho_ge_mu (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (b : ℝ) (h : ClassThreeBlock pr)
    (hrows : RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) I.f₁ I.h₁ r) :
    (firstChamberCut 0).Below (middleFrame pr hne root W I hr b h).mu
      (middleFrame pr hne root W I hr b h).rho :=
  (middleFrame pr hne root W I hr b h).rho_ge_mu (middleBlock_datumHyp₁ pr hne) hrows

end Sarkozy.PartVRecords
