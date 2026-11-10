module

public import Sarkozy.SpectralC.CouplingModes

@[expose] public section

/-!
# Coupling data (`def:coupling-data`) and their modes (`lem:coupling-modes`)

`paper/sections/14_spectral.tex`, `subsec:spec:coupling`. For labellings `x : U⁺ → 𝔽_p`, the
allowed set is
`Φ_k(x) = {a ∉ x(U⁺) : ς_jk(a − x_j) ∈ Q_p for all j ∈ N(k)}` (`allowedSet`), and `Aff_p` acts
diagonally on labellings (`affLab`). `CouplingData` is `def:coupling-data` at `p` for the
labelling set `𝓘⁺` (`Iplus`, `Aff_p`-invariant) and the half law `μ`: a law `ν` on `𝓘⁺` and
probability vectors `P_k(· | x)` supported on `Φ_k(x)` with (i) `ν` invariant and
`dν/dμ ∈ [c, R_ν c]`, (ii) `P_k(γa | γx) = P_k(a | x)`, (iii)
`|Φ_k(x)| P_k(a | x) = 1 + δ_k(a; x) ∈ [1/R'_k, R'_k]` on `Φ_k(x)`. The vectors are extended by
`0` off `𝓘⁺`.

`CouplingData.modes` is `lem:coupling-modes` for coupling data:
`‖𝒫F_V‖²_ν = ∑_{ξ ≠ 0} ĝ(ξ)^* 𝐌(ξ) ĝ(ξ)` (from `coupling_modes`).

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- The diagonal action of `z ↦ sz + c` on labellings. -/
def affLab (s c : ZMod p) (x : U → ZMod p) : U → ZMod p := fun j => s * x j + c

/-- The allowed set `Φ_k(x) = {a ∉ x(U⁺) : ς_jk(a − x_j) ∈ Q_p for all j ∈ N(k)}`. -/
def allowedSet (N : U → Finset U) (ς : U → U → ZMod p) (k : U) (x : U → ZMod p) :
    Finset (ZMod p) :=
  univ.filter (fun a => a ∉ univ.image x ∧
    ∀ j ∈ N k, ς j k * (a - x j) ≠ 0 ∧ IsSquare (ς j k * (a - x j)))

omit [Fintype U] [DecidableEq U] in
lemma affLab_bijective {s : ZMod p} (hs : s ≠ 0) (c : ZMod p) :
    Function.Bijective (affLab (U := U) s c) := by
  constructor
  · intro x x' h
    funext j
    have := congrFun h j
    unfold affLab at this
    have h2 : s * x j = s * x' j := by linear_combination this
    exact mul_left_cancel₀ hs h2
  · intro x'
    refine ⟨fun j => s⁻¹ * (x' j - c), ?_⟩
    funext j
    unfold affLab
    rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul, sub_add_cancel]

/-- **`def:coupling-data`** at `p`, for the labelling set `𝓘⁺` and the half law `μ`. -/
structure CouplingData (p : ℕ) [Fact p.Prime] (U : Type*) [Fintype U] [DecidableEq U]
    (N : U → Finset U) (ς : U → U → ZMod p) (Iplus : Finset (U → ZMod p))
    (μ : (U → ZMod p) → ℝ) where
  /-- The law `ν` on `𝓘⁺`. -/
  ν : (U → ZMod p) → ℝ
  /-- The probability vectors `P_k(· | x)`. -/
  P : U → (U → ZMod p) → ZMod p → ℝ
  ν_nonneg : ∀ x, 0 ≤ ν x
  ν_total : ∑ x ∈ Iplus, ν x = 1
  ν_supp : ∀ x, x ∉ Iplus → ν x = 0
  P_nonneg : ∀ k x a, 0 ≤ P k x a
  P_total : ∀ k, ∀ x ∈ Iplus, ∑ a, P k x a = 1
  P_supp : ∀ k, ∀ x ∈ Iplus, ∀ a, a ∉ allowedSet N ς k x → P k x a = 0
  P_off : ∀ k x a, x ∉ Iplus → P k x a = 0
  /-- `𝓘⁺` is `Aff_p`-invariant. -/
  I_inv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s →
    (affLab s c x ∈ Iplus ↔ x ∈ Iplus)
  /-- (i) `ν` is `Aff_p`-invariant. -/
  ν_inv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → ν (affLab s c x) = ν x
  /-- (i) the density of `ν` with respect to `μ` takes values in `[c, R_ν c]`. -/
  dens_c : ℝ
  dens_R : ℝ
  dens_c_pos : 0 < dens_c
  dens_R_ge : 1 ≤ dens_R
  dens : ∀ x ∈ Iplus, dens_c * μ x ≤ ν x ∧ ν x ≤ dens_R * dens_c * μ x
  /-- (ii) covariance. -/
  P_cov : ∀ (k : U) (s c : ZMod p), ∀ x ∈ Iplus, ∀ a, s ≠ 0 → IsSquare s →
    P k (affLab s c x) (s * a + c) = P k x a
  /-- (iii) `1 + δ_k = |Φ_k(x)| P_k(a | x) ∈ [1/R'_k, R'_k]` on `Φ_k(x)`. -/
  Rp : U → ℝ
  Rp_ge : ∀ k, 1 ≤ Rp k
  P_dens : ∀ k, ∀ x ∈ Iplus, ∀ a ∈ allowedSet N ς k x,
    (Rp k)⁻¹ ≤ P k x a * (allowedSet N ς k x).card ∧
      P k x a * (allowedSet N ς k x).card ≤ Rp k

namespace CouplingData

variable {N : U → Finset U} {ς : U → U → ZMod p} {Iplus : Finset (U → ZMod p)}
  {μ : (U → ZMod p) → ℝ}

/-- The action of `Aff_p` on all labellings, preserving `ν`. -/
def affAction (D : CouplingData p U N ς Iplus μ) : AffAction p (U → ZMod p) D.ν where
  act := affLab
  bij := fun _ c hs _ => affLab_bijective hs c
  pres := fun s c x hs hsq => D.ν_inv s c x hs hsq

lemma P_cov_all (D : CouplingData p U N ς Iplus μ) (k : U) (s c : ZMod p) (x : U → ZMod p)
    (a : ZMod p) (hs : s ≠ 0) (hsq : IsSquare s) :
    D.P k (affLab s c x) (s * a + c) = D.P k x a := by
  by_cases hx : x ∈ Iplus
  · exact D.P_cov k s c x hx a hs hsq
  · rw [D.P_off k x a hx, D.P_off k _ _ (fun h => hx ((D.I_inv s c x hs hsq).mp h))]

/-- **`lem:coupling-modes`** for coupling data: for `F_V = ∑_k g_k(x_k)` with mean-zero `g_k`,
`‖𝒫F_V‖²_ν = ∑_{ξ ≠ 0} ĝ(ξ)^* 𝐌(ξ) ĝ(ξ)`, `𝐌(ξ) = H̃/(p − 1) + (p/(p − 1)) c_ξ 𝐃`. -/
theorem modes (D : CouplingData p U N ς Iplus μ) (hp2 : p ≠ 2) (g : U → ZMod p → ℂ)
    (hg : ∀ k, ∑ a, g k a = 0) :
    ∑ x, (D.ν x : ℂ) * ((‖condField D.P g x‖ ^ 2 : ℝ) : ℂ) =
      ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
        qform (couplingM D.ν D.P ξ) (fun k => fcoef (g k) ξ) := by
  apply coupling_modes hp2 D.ν D.affAction D.P _ _ g hg
  · intro k x hx
    by_cases hxI : x ∈ Iplus
    · exact D.P_total k x hxI
    · exact absurd (D.ν_supp x hxI) hx
  · intro k s c x a hs hsq
    exact D.P_cov_all k s c x a hs hsq

end CouplingData

end Sarkozy.SpectralC
