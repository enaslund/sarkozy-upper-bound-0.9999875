module

public import Sarkozy.TailCorr.LayerEE

@[expose] public section

/-!
# `TailInputsCorr P₄` from the remaining spectral inputs of the tail datum

`paper/sections/27_tail_index.tex`, `lem:tail-law`(i);
`paper/sections/25_upper_reference.tex`, `subsec:upper-reference-rp` ((V1), (V3)),
`it:record:upper-F4` (`subsec:row-anova-correlation`), `it:record:upper-F6`,
`lem:upper-completed-root`.

`TailSpectral` (in `Reduction`) is the spectral part of `lem:tail-law`(i). This file splits its
correlation fields (F4) into the fold half (`FoldCorr`, the maximal correlation `ρ_F` of the fold
kernel) and the matching half (`MatchNorm`, `‖T_E^b - J‖ ≤ ρ_E`), and its layer caps (V3) into the
nine field pairs. It discharges the matching half at the field type `E` (`MatchingE`) and the layer
cap of the field pair `EE` (`LayerEE`). What is left is **`TailSpectralCore`**:

* (V1) the root envelopes of the four row families (`lem:upper-completed-root` for the root cuts,
  `it:record:upper-F6` for the nonroot chamber cuts);
* (F4), fold half: `ρ_F ≤ (f - 2⁻⁹⁰) r` for the four families at the three field types;
* (F4), matching half: `‖T_E^b - J‖ ≤ h r` for the four families at the field types `L`, `F`;
* (V3) the layer caps of the eight field pairs other than `EE` (`it:record:upper-F6` at the
  layer cuts).

**`tailInputsCorr_of_core`**: `TailSpectralCore` at every prime `q ≥ P ≥ P₄` gives V2's
`TailInputsCorr P`, hence (`tailInputsValid_of_corr`) `TailInputsValid P`.
-/

namespace Sarkozy.TailCorr

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws

section Halves

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

/-- **(F4), fold half** (`it:record:upper-F4`): at every middle value, the maximal correlation of
the fold kernel, measured in its own marginals, is at most `ρ_F`. -/
def FoldCorr (D : Datum 𝔛) (ρF : ℝ) : Prop :=
  ∀ b, D.nu.weight b ≠ 0 →
    ∀ g g' : 𝔛 → ℝ, |kf (D.nub b) (covKernel (D.nub b) (D.TF b)) g g'| ≤
      ρF * Real.sqrt (wvar (D.nub b) (margL (D.nub b) (D.TF b)) g) *
        Real.sqrt (wvar (D.nub b) (margR (D.nub b) (D.TF b)) g')

/-- **(F4), matching half** (`it:record:upper-F4`): at every middle value,
`‖T_E^b - J‖ ≤ ρ_E` on `L²(ν^b)`. -/
def MatchNorm (D : Datum 𝔛) (ρE : ℝ) : Prop :=
  ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TE b) ρE

/-- `CorrInputs` is the conjunction of its two halves. -/
theorem corrInputs_iff (D : Datum 𝔛) (ρF ρE : ℝ) :
    CorrInputs D ρF ρE ↔ FoldCorr D ρF ∧ MatchNorm D ρE :=
  ⟨fun h => ⟨fun b hb => (h b hb).1, fun b hb => (h b hb).2⟩,
    fun h b hb => ⟨h.1 b hb, h.2 b hb⟩⟩

end Halves

/-- **The remaining spectral inputs of the tail datum at one prime** (`lem:tail-law`(i), its
spectral part, without the matching rows of the field type `E` and the layer cap of `EE`, which
are proved in `MatchingE` and `LayerEE`). Hypothesis bundle, not proved here; every field is the
paper's statement at the single prime `q` with the recorded inputs of the tail datum:
* `root20`, `root21`, `root10`, `root11`: (V1), `it:upper-valid-root` (`lem:upper-completed-root`
  for the root cuts, `it:record:upper-F6` for the nonroot chamber cuts);
* `fold20`, `fold21`, `fold10`, `fold11`: (F4), fold half (`it:record:upper-F4`,
  `eq:row-anova-actual` with `eq:row-anova-stars`), `ρ_F ≤ (f - 2⁻⁹⁰) r`;
* `match20`, `match21`, `match10`, `match11`: (F4), matching half, `‖T_E^b - J‖ ≤ h r`, at the
  field types `L` and `F`;
* `caps`: (V3), `it:upper-valid-layer` (`it:record:upper-F6` at the layer cuts), for the eight
  field pairs other than `EE`. -/
structure TailSpectralCore (q : ℕ) [Fact q.Prime] (hne : TailNonempty q)
    (hW : WeilBound (ZMod q)) (hp : (2 : ℝ) ^ 20 ≤ q) : Prop where
  root20 : ∀ f', RootEnv (rowD0 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two0 f')) (tailOrd f').d (tailR q)
  root21 : ∀ f', RootEnv (rowD1 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two1 f')) (tailOrd f').d (tailR q)
  root10 : ∀ f', RootEnv (rowD0 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one0 f')) (tailRes f').d (tailR q)
  root11 : ∀ f', RootEnv (rowD1 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one1 f')) (tailRes f').d (tailR q)
  fold20 : ∀ f', FoldCorr (rowD0 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two0 f')) (tailCF (tailOrd f') * tailR q)
  fold21 : ∀ f', FoldCorr (rowD1 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two1 f')) (tailCF (tailOrd f') * tailR q)
  fold10 : ∀ f', FoldCorr (rowD0 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one0 f')) (tailCF (tailRes f') * tailR q)
  fold11 : ∀ f', FoldCorr (rowD1 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one1 f')) (tailCF (tailRes f') * tailR q)
  match20 : ∀ f', f' ≠ .E → MatchNorm (rowD0 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two0 f')) ((tailOrd f').h * tailR q)
  match21 : ∀ f', f' ≠ .E → MatchNorm (rowD1 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two1 f')) ((tailOrd f').h * tailR q)
  match10 : ∀ f', f' ≠ .E → MatchNorm (rowD0 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one0 f')) ((tailRes f').h * tailR q)
  match11 : ∀ f', f' ≠ .E → MatchNorm (rowD1 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one1 f')) ((tailRes f').h * tailR q)
  caps : ∀ f0 f1 : FieldTy, ¬ (f0 = .E ∧ f1 = .E) →
    (Reserved.fieldCut f0.Obj f1.Obj).Below
      (-(tailKappa f0 f1 * tailR q) •
        pushFunctional (lawL (lam1 (tailFieldLaws q hne) f0 f1)) Reserved.diagF)
      (lawL (lam2 (tailFieldLaws q hne) f0 f1))

/-- **`TailSpectral` from the remaining inputs**: the matching half of (F4) at the field type `E`
(`matchE_two0`, …, `matchE_one1`) and the layer cap of `EE` (`layerCap_EE`) are proved. -/
theorem tailSpectral_of_core (q : ℕ) [Fact q.Prime] (hne : TailNonempty q)
    (hW : WeilBound (ZMod q)) (hp : (2 : ℝ) ^ 20 ≤ q) (h : TailSpectralCore q hne hW hp) :
    TailSpectral q hne hW hp := by
  obtain ⟨r20, r21, r10, r11, f20, f21, f10, f11, m20, m21, m10, m11, caps⟩ := h
  refine ⟨r20, r21, r10, r11, fun f' => ?_, fun f' => ?_, fun f' => ?_, fun f' => ?_,
    fun f0 f1 => ?_⟩
  rotate_left 4
  · by_cases hEE : f0 = .E ∧ f1 = .E
    · obtain ⟨rfl, rfl⟩ := hEE
      exact layerCap_EE q hne hp
    · exact caps f0 f1 hEE
  · refine (corrInputs_iff _ _ _).mpr ⟨f20 f', ?_⟩
    cases f'
    · exact m20 .L (by decide)
    · exact m20 .F (by decide)
    · exact matchE_two0 q hne hW hp
  · refine (corrInputs_iff _ _ _).mpr ⟨f21 f', ?_⟩
    cases f'
    · exact m21 .L (by decide)
    · exact m21 .F (by decide)
    · exact matchE_two1 q hne hW hp
  · refine (corrInputs_iff _ _ _).mpr ⟨f10 f', ?_⟩
    cases f'
    · exact m10 .L (by decide)
    · exact m10 .F (by decide)
    · exact matchE_one0 q hne hW hp
  · refine (corrInputs_iff _ _ _).mpr ⟨f11 f', ?_⟩
    cases f'
    · exact m11 .L (by decide)
    · exact m11 .F (by decide)
    · exact matchE_one1 q hne hW hp

/-- **`TailInputsCorr P` from the remaining spectral inputs** (`lem:tail-law`(i) reduced to
`TailSpectralCore`): for `P ≥ P₄`, `TailSpectralCore` at every prime `q ≥ P` gives V2's
`TailInputsCorr P`. With `P = P₄` this is the obligation `hC` of the main statement. -/
theorem tailInputsCorr_of_core {P : ℕ} (hP : P4 ≤ P)
    (hS : ∀ (q : ℕ) [Fact q.Prime], P ≤ q → ∀ (hne : TailNonempty q) (hW : WeilBound (ZMod q))
      (hp : (2 : ℝ) ^ 20 ≤ q), TailSpectralCore q hne hW hp) :
    TailInputsCorr P :=
  tailInputsCorr_of_spectral hP fun q _ hq hne hW hp => tailSpectral_of_core q hne hW hp
    (hS q hq hne hW hp)

/-- **`TailInputsValid P₄` from the remaining spectral inputs** (V2's `tailInputsValid_of_corr`
composed with `tailInputsCorr_of_core`). -/
theorem tailInputsValid_of_core
    (hS : ∀ (q : ℕ) [Fact q.Prime], P4 ≤ q → ∀ (hne : TailNonempty q) (hW : WeilBound (ZMod q))
      (hp : (2 : ℝ) ^ 20 ≤ q), TailSpectralCore q hne hW hp) :
    TailInputsValid P4 :=
  tailInputsValid_of_corr le_rfl (tailInputsCorr_of_core le_rfl hS)

end Sarkozy.TailCorr
