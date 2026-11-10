module

public import Sarkozy.SpectralD.CxFull
public import Sarkozy.Cuts.CutMass

@[expose] public section

/-!
# `prop:spec2:mucentre`(c2): the supremum of `ϱ`

`paper/sections/14_spectral.tex`, `prop:spec2:mucentre`(c2):
`sup_{𝓘⁺} ϱ ≤ R₊ = ∏_i(1 + e_{t_i}(p, 2n)) / ((1 − ε_Z) ∏_{i ∈ U⁺}(1 − e_{d⁰_i}(p, n)))`.
`rho_sup_le` proves the graded form
`ϱ(x) ≤ R₊ = 2^{m_×} ∏_i 𝔲(t_i) / ((1 − ε_Z) ∏_i 𝔩(t⁰_i))` (WP-P's one-step bounds
`stepUpper`, `stepLower` along the deletion order, which are at least as sharp as the coarse
factors), from:
* `ϱ(x) = N(x)/(Z |𝓘⁺|)` (WP-P's `rho_eq`, `cutZ_eq`);
* `N(x) ≤ ∏_i 𝔲(t_i)` (`Ncount_bounds`), `|𝓘⁺| ≥ ∏_i 𝔩(t⁰_i)` (`card_half_graded`);
* `Z₀ = 2^{m_×} Z ≥ 1 − ε_Z` (`Z0_lower`, with the explicit `T_ns`, `T_coll` of `CxExpansion`).

This is the paper's `R₊`, the sharper alternative to `R_cut` in the coupling inputs of the root
cuts (`lem:upper-completed-root`(ii)).

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- **`prop:spec2:mucentre`(c2)**, graded form: `ϱ ≤ R₊` on `𝓘⁺`. -/
theorem rho_sup_le [LinearOrder D.cut.Half] (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hp2 : p ≠ 2) (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) {nn : ℕ}
    (hn : Fintype.card W ≤ nn) (he : ∀ i, SecondOrder.graphCountError (p := p) D.halfGraph i < 1)
    {εZ Nns Dcol : ℝ} (hεZ : εZ < 1)
    (hns : ∀ x, ‖nsOp D hne x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖collOp D hne x‖ ≤ Dcol * ‖x‖)
    (hεZc : 2 * Spectral.starZstar (SecondOrder.graphPinned
        (Labellings.weilBound_of_target hW p hp2) D.halfGraph (D.half_nonempty hne) he) D.Nset
        (Spectral.starCoef (p := p) D) + Nns + Dcol ≤ εZ)
    (hL : 0 < ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn (D.t0deg j))
    {x : D.cut.Half → ZMod p} (hx : x ∈ Labellings.injLabellings (ZMod p) D.halfGraph) :
    rhoK (D.halfLaw hne).weight (cutKn D hne) x ≤
      2 ^ D.mcross * (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) (D.tdeg j)) /
        ((1 - εZ) * ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn (D.t0deg j)) := by
  have hWB := Labellings.weilBound_of_target hW p hp2
  have hI0 : (0 : ℝ) < ((Labellings.injLabellings (ZMod p) D.halfGraph).card : ℝ) := by
    exact_mod_cast card_pos.mpr (D.half_nonempty hne)
  have hJ0 : (0 : ℝ) < ((Labellings.injLabellings (ZMod p) D.G).card : ℝ) := by
    exact_mod_cast card_pos.mpr hne
  have hZ := D.cutZ_pos hne
  have hZeq := D.cutZ_eq hne
  have hrho : rhoK (D.halfLaw hne).weight (cutKn D hne) x =
      (D.Ncount x : ℝ) / (D.cutZ hne * ((Labellings.injLabellings (ZMod p) D.halfGraph).card : ℝ)) := by
    rw [rhoK_eq_rowFun, D.rho_eq hne x, hZeq]
    field_simp
  have hNU := (D.Ncount_bounds hWB hn hx).2
  have hIL := (D.card_half_graded hWB hn).1
  have hN0 : (0 : ℝ) ≤ (D.Ncount x : ℝ) := Nat.cast_nonneg _
  have hZ0 := Z0_lower D hne hW hMR hp2 he hns hcoll
  have h2 : (0 : ℝ) < 2 ^ D.mcross := by positivity
  have hZl : (1 - εZ) / 2 ^ D.mcross ≤ D.cutZ hne := by
    rw [div_le_iff₀ h2]
    unfold Z0 at hZ0
    have e : (2 : ℝ) ^ D.crossPairs.card = 2 ^ D.mcross := rfl
    rw [e] at hZ0
    nlinarith
  have h1e : 0 < 1 - εZ := by linarith
  have hU0 : (0 : ℝ) ≤ ∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) (D.tdeg j) :=
    hN0.trans hNU
  rw [hrho]
  calc (D.Ncount x : ℝ) / (D.cutZ hne * ((Labellings.injLabellings (ZMod p) D.halfGraph).card : ℝ))
      ≤ (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) (D.tdeg j)) /
          (D.cutZ hne * ((Labellings.injLabellings (ZMod p) D.halfGraph).card : ℝ)) :=
        div_le_div_of_nonneg_right hNU (mul_pos hZ hI0).le
    _ ≤ (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) (D.tdeg j)) /
          ((1 - εZ) / 2 ^ D.mcross *
            ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn (D.t0deg j)) :=
        div_le_div_of_nonneg_left hU0 (mul_pos (div_pos h1e h2) hL)
          (mul_le_mul hZl hIL hL.le hZ.le)
    _ = 2 ^ D.mcross * (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) (D.tdeg j)) /
          ((1 - εZ) * ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn (D.t0deg j)) := by
        field_simp

end Sarkozy.SpectralD.Cx
