module

public import Sarkozy.Variance.Classes
public import Sarkozy.Variance.BackgroundVariance

/-!
# The variance classes of the final construction (`cor:variance:final`(i)–(iii))

`paper/sections/22_variance.tex`, `cor:variance:final`. Parts (i)–(iii) are instances of the
results of this directory, with the piece data of a pattern `m` (`C = C_m`, `κ_F = k_{F,m}`,
`κ_E = k_{E,m}`, `ε_X ≤ η_m`) and the certified upper bound `R_* ≥ R_err`:

* **(i), fold selections** (`variance_final_fold_class`): the selection of `F_j` on `X` has class
  cost `B - g_F(m)`, `g_F(m) = [b_F(m) - R_*]_+`, `b_F(m) = (ℓ_m/C_m - k_{F,m})/(1 - k_{F,m})`:
  `lem:var-gain`(b) with (Res) the restoration bound `ℓ_m` (`restoration`), and the monotonicity
  of the gain in `R` (`gainOf_anti`).
* **(i), aligned matching classes**: `background_variance_class_cost` with the displayed bound
  of `background_variance_a` (`BackgroundVariance.lean`).
* **(ii)** and **(iii)**: `lem:var-gain`(a) with `C = C_m` and the numbers `b_F(m)`, `b_E(m)`, that
  is `var_classes_fold` and `var_classes_aligned_matching` (`Classes.lean`). The envelope credits
  of `lem:class-credit` are not formalized here.

**Not formalized:** (iv), the assembly of the credits into the complete polynomial of
`lem:record:record-expansion` (the total `D_var` of `eq:variance:dvar`), and the gates of
`cert:variance:fresh`, which are hypotheses here (`k_{F,i}, k_{E,i} < 1` as `κ < 1`; the gains
in `[0, 1)` via `var_gain_c`).
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

/-- The gain is antitone in the subtracted error: `R ≤ R'` gives
`[l̄ - R']_+ ≤ [l̄ - R]_+`. -/
theorem gainOf_anti {l₀ C κ R R' : ℝ} (h : R ≤ R') : gainOf l₀ C κ R' ≤ gainOf l₀ C κ R :=
  max_le_max le_rfl (by linarith)

section Final

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)] {ι : Type*}

/-- **`cor:variance:final`(i), the fold selections**: under the hypotheses of `var_gain_b`
(with `C = C_m`, `κ = k_{F,m}`, (Res) the restoration bound `ℓ_m`) and `R_err ≤ R_*`, the
selections form a class of cost `B - g_F(m)`, `g_F(m) = [b_F(m) - R_*]_+`:
`∑ |I_ω| ≤ (B - g_F(m) + z) ∑ π_ω Y`. -/
theorem variance_final_fold_class (c : ReflectionCut V) (O N lam : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (j₀ : J) (hO : ∀ j, j ≠ j₀ → c.Positive (O j))
    (hN : ∀ j, j ≠ j₀ → c.Bracket (N j) (lam j) (N j))
    (F : (∀ b, X b) → ℝ) (R : Finset ι) (hR : R.Nonempty)
    (P : ι → ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) (m : ι → (c.Half → X j₀) → ℝ)
    (hm : ∀ φ ∈ R, ∀ x, 0 ≤ m φ x) (hmpos : ∀ φ ∈ R, 0 < ∑ x, m φ x)
    (hsymm : ∀ φ ∈ R, ∀ G H : (c.Half → X j₀) → ℝ, c.form (P φ) G H = c.form (P φ) H G)
    (hplus : ∀ φ ∈ R, ∀ G : (c.Half → X j₀) → ℝ, c.form (P φ) G 1 = ∑ x, m φ x * G x)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hcen : ∀ φ ∈ R, CentredNormLe c (P φ) (m φ) κ)
    {Yμ CX Cm ℓ z₁ z₂ z₃ z₄ Bf Rerr Rstar γ : ℝ} (hY : 0 ≤ Yμ) (hCX : 1 ≤ CX) (hC : CX ≤ Cm)
    (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂) (hz₄ : 0 ≤ z₄) (hγ : 0 ≤ γ) (hRs : Rerr ≤ Rstar)
    (hRes : (ℓ - z₁) * Yμ ≤ (∑ φ ∈ R, energyAt O j₀ (P φ) F) / R.card)
    (hE1 : ∀ φ ∈ R, energyAt O j₀ (c.diagonalLaw (m φ)) F ≤ (1 + z₂) * CX * Yμ)
    (ζ : ι → ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ)
    (hζ : ∀ φ ∈ R, ∀ G H : (c.Half → X j₀) → ℝ, |c.form (ζ φ) G H| ≤
      γ * Real.sqrt (c.form (c.diagonalLaw (m φ) - indepLaw c (m φ)) G G) *
        Real.sqrt (c.form (c.diagonalLaw (m φ) - indepLaw c (m φ)) H H))
    (hDiagN : ∀ φ ∈ R, energyAt N j₀ (c.diagonalLaw (m φ)) F ≤ (Bf + z₃) * CX * Yμ)
    (hJN : ∀ φ ∈ R, energyAt O j₀ (indepLaw c (m φ)) F - (Rerr + z₄) * CX * Yμ ≤
      energyAt N j₀ (indepLaw c (m φ)) F) :
    ∑ φ ∈ R, |energyAt lam j₀ (ζ φ) F| ≤
      (Bf - gainOf ℓ Cm κ Rstar + (z₃ + z₄ + (z₁ + κ * z₂) / (1 - κ))) *
        (∑ _φ ∈ R, γ * CX) * Yμ := by
  have h := var_gain_b c O N lam j₀ hO hN F R hR P m hm hmpos hsymm hplus hκ0 hκ1 hcen hY hCX hC
    hz₁ hz₂ hz₄ hγ hRes hE1 ζ hζ hDiagN hJN
  refine h.trans ?_
  have hsum : 0 ≤ (∑ _φ ∈ R, γ * CX) * Yμ := by
    apply mul_nonneg _ hY
    exact sum_nonneg fun _ _ => mul_nonneg hγ (by linarith)
  have hmono := gainOf_anti (l₀ := ℓ) (C := Cm) (κ := κ) hRs
  have := mul_le_mul_of_nonneg_right (show Bf - gainOf ℓ Cm κ Rerr +
      (z₃ + z₄ + (z₁ + κ * z₂) / (1 - κ)) ≤
      Bf - gainOf ℓ Cm κ Rstar + (z₃ + z₄ + (z₁ + κ * z₂) / (1 - κ)) by linarith) hsum
  calc (Bf - gainOf ℓ Cm κ Rerr + (z₃ + z₄ + (z₁ + κ * z₂) / (1 - κ))) *
        (∑ _φ ∈ R, γ * CX) * Yμ
      = (Bf - gainOf ℓ Cm κ Rerr + (z₃ + z₄ + (z₁ + κ * z₂) / (1 - κ))) *
          ((∑ _φ ∈ R, γ * CX) * Yμ) := by ring
    _ ≤ (Bf - gainOf ℓ Cm κ Rstar + (z₃ + z₄ + (z₁ + κ * z₂) / (1 - κ))) *
          ((∑ _φ ∈ R, γ * CX) * Yμ) := this
    _ = _ := by ring

end Final

end Sarkozy.Variance
