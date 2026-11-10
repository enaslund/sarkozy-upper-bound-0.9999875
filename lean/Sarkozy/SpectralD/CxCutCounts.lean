module

public import Sarkozy.SpectralD.CxInstanceA
public import Sarkozy.Cuts.CutCount

@[expose] public section

/-!
# The density range of instance (A) for the cut (`lem:spec:cutkernel`(c))

`paper/sections/14_spectral.tex`, `def:coupling-data`, instance (A): "Here `R_ν = R_cut`: by
`lem:spec:cutkernel`(b), (c) and its proof, `ϱ = N/E_μN` with `N₋ ≤ N ≤ N₊` and
`N₊/N₋ = R_cut`". WP-P's `Cuts.SpecData.rho_Rcut` gives `R_cut⁻¹ ≤ ϱ ≤ R_cut` on `𝓘⁺` when
`e_{t_i}(p, n') < 1` for every deletion degree `t_i` (and `thm:weil`). Since `rhoK` is WP-P's
`rowFun` (`rhoK_eq_rowFun`), this discharges two of the three counting hypotheses of
`couplingDataA` / `couplingBound_cut`: `ϱ > 0` on `𝓘⁺` and the density ratio, with
`c = R_cut⁻¹`, `R = R_cut²` (so `R c = R_cut`) (`rho_counts`, `one_le_Rcut`).

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- `ϱ = Op 1` is WP-P's `rowFun`. -/
theorem rhoK_eq_rowFun (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (x : D.cut.Half → ZMod p) :
    rhoK (D.halfLaw hne).weight (cutKn D hne) x =
      Cuts.rowFun (D.halfLaw hne) (fun x x' => D.cutK x x' / D.cutZ hne) x := rfl

/-- `R_cut ≥ 1` when every `e_{t_i} < 1` (the errors are nonnegative). -/
theorem one_le_Rcut {nn : ℕ}
    (he1 : ∀ i, TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) nn < 1) :
    1 ≤ D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) := by
  have hq : (0 : ℝ) < (Fintype.card (ZMod p) : ℕ) := by exact_mod_cast Fintype.card_pos
  unfold Cuts.SpecData.Rcut
  have hf : ∀ i, (1 : ℝ) ≤ (1 + TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) nn) /
      (1 - TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) nn) := by
    intro i
    have h0 := TraceMixing.coarseErr_nonneg hq (D.tdeg i) nn
    have h1 := he1 i
    rw [le_div_iff₀ (by linarith)]
    linarith
  calc (1 : ℝ) = ∏ _i : Fin D.cut.half.card, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => zero_le_one) (fun i _ => hf i)

/-- **The density range of instance (A)** (`lem:spec:cutkernel`(c), WP-P's `rho_Rcut`): with
`thm:weil` and `e_{t_i}(p, n') < 1` for every `i` (`n' ≥ |U|`), `ϱ > 0` on `𝓘⁺` and
`R_cut⁻¹ ≤ ϱ ≤ R_cut² · R_cut⁻¹ (= R_cut)`: the hypotheses `hρpos` and `hdens` of
`couplingDataA` and `couplingBound_cut` with `c = R_cut⁻¹`, `R = R_cut²`. -/
theorem rho_counts (hW : Labellings.WeilBound (ZMod p)) {nn : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (he1 : ∀ i, TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) nn < 1) :
    (∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      0 < rhoK (D.halfLaw hne).weight (cutKn D hne) x) ∧
    (∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn))⁻¹ ≤
          rhoK (D.halfLaw hne).weight (cutKn D hne) x ∧
        rhoK (D.halfLaw hne).weight (cutKn D hne) x ≤
          D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) ^ 2 *
            (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn))⁻¹) := by
  have hR1 := one_le_Rcut D he1
  set R := D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) with hRdef
  have hR0 : 0 < R := by linarith
  have e : R ^ 2 * R⁻¹ = R := by field_simp
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have h := (D.rho_Rcut hW hn hne he1 hx).1
    rw [← rhoK_eq_rowFun] at h
    exact lt_of_lt_of_le (inv_pos.mpr hR0) h
  · have h := D.rho_Rcut hW hn hne he1 hx
    rw [← rhoK_eq_rowFun] at h
    rw [e]
    exact h

end Sarkozy.SpectralD.Cx
