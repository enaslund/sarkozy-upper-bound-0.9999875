module

public import Sarkozy.SpectralD.StarMatrixNorm
public import Sarkozy.SpectralD.Features

@[expose] public section

/-!
# The star matrix with the `λ_max` synthesis (`cor:star-matrix` with `lem:general-star`(f))

`paper/sections/14_spectral.tex`, `cor:star-matrix`: `‖r F M(Φ̂) F^*‖ ≤ r ‖F‖² ‖M(i)‖`, with
`‖F‖² ≤ 1 + λ_max(N)` from `lem:general-star`(f) in its `λ_max` form
(`Sarkozy.SpectralD.features_synthesis_eigenvalue`, S1's `Features`). The features of
`Sarkozy.SpectralD.Features` are those used here (`featKer_eq_features`).

* `starPart_norm_le_eigen`: if `N ≥ 0` (symmetric) bounds the off-diagonal Grams
  `‖F_α^*F_β‖ ≤ N_αβ` and `‖M(i)‖ ≤ λ`, then
  `|⟨P₀g, K_st P₀f⟩_μ| ≤ r λ (1 + λ_max(N)) ‖g‖_μ ‖f‖_μ`.

New material for this paper.
-/

namespace Sarkozy.SpectralD.StarMatrix

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] [DecidableEq U] in
/-- The actual features here and in `Sarkozy.SpectralD.Features` are the same. -/
lemma featKer_eq_features (𝒮 : Finset (Finset U)) (a : Feat U 𝒮) :
    StarMatrix.featKer (p := p) 𝒮 a = Sarkozy.SpectralD.featKer 𝒮 a := by
  cases a <;> rfl

/-- **`cor:star-matrix` with `‖F‖² ≤ 1 + λ_max(N)`** (`lem:general-star`(f)): for
`p ≡ 3 (mod 4)`, an `Aff_p`-invariant law `μ` on injective labellings, nonempty supports, a
symmetric `N ≥ 0` bounding the off-diagonal Grams of the features (`hoff`, bilinear form) and
`‖M(i)‖ ≤ λ`: `|⟨P₀g, K_st P₀f⟩_μ| ≤ r λ (1 + λ_max(N)) ‖g‖_μ ‖f‖_μ`. -/
theorem starPart_norm_le_eigen (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (d : U → U → ℝ) (L : U → Finset U → ℝ) (R : Finset U → U → ℝ) (𝒮 : Finset (Finset U))
    (h𝒮 : ∀ S ∈ 𝒮, S.Nonempty) {lam : ℝ} (hlam : 0 ≤ lam)
    (hM : NormLe (matI (starM0 L R 𝒮) (starM1 d 𝒮)) lam)
    (N : Matrix (U ⊕ 𝒮) (U ⊕ 𝒮) ℝ) (hN : N.IsHermitian) (hN0 : ∀ a b, 0 ≤ N a b)
    (hoff : ∀ a b : U ⊕ 𝒮, a ≠ b → ∀ (h h' : ZMod p → ℂ), meanC h = 0 → meanC h' = 0 →
      ‖∑ x, (μ x : ℂ) * (conj (kerMap (Sarkozy.SpectralD.featKer 𝒮 a) h x) *
        kerMap (Sarkozy.SpectralD.featKer 𝒮 b) h' x)‖ ≤
        N a b * Real.sqrt (l2sq h) * Real.sqrt (l2sq h'))
    (g f : (U → ZMod p) → ℂ) :
    ‖bil μ (cent μ g) (starPart d L R 𝒮) (cent μ f)‖ ≤
      rp p * lam * (1 + ⨆ i, hN.eigenvalues i) * √(∑ x, μ x * ‖g x‖ ^ 2) *
        √(∑ x, μ x * ‖f x‖ ^ 2) := by
  have hev : 0 ≤ 1 + ⨆ i, hN.eigenvalues i := by
    by_cases hι : IsEmpty (U ⊕ 𝒮)
    · have := hι
      rw [Real.iSup_of_isEmpty]
      norm_num
    · rw [not_isEmpty_iff] at hι
      obtain ⟨a0⟩ := hι
      have h := quad_le_eigenvalue_sup N hN (fun a => if a = a0 then (1 : ℝ) else 0)
      simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
        ite_true, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow] at h
      linarith [hN0 a0 a0]
  refine starPart_norm_le hp2 hp3 μ hμ0 hμ1 hinv d L R 𝒮 hlam hev hM ?_ g f
  intro h hh
  simp only [featKer_eq_features]
  exact features_synthesis_eigenvalue hp2 hp3 μ hμ0 hμ1 hinv hinj 𝒮 h𝒮 N hN hN0 hoff h hh

end Sarkozy.SpectralD.StarMatrix
