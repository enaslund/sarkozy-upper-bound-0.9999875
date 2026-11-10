module

public import Sarkozy.SpectralC.All
public import Sarkozy.Spectral.Coupling
public import Sarkozy.Spectral.RouteB

/-!
# Glue, VI: the degree-one inputs of `cor:spec2:coupling` from WP-K (`lem:spec:degone` (b))

`Sarkozy.Spectral.coupling_block` takes, on every mode `ξ`, two hypotheses:
* `hQ`, `|𝐐ĝ|² ≥ r²(|Aĝ|² - 2Λ_D η_Q |ĝ|²)`;
* `hA`, `|Aĝ| ≤ Λ_D |ĝ|`.

WP-K's `SpectralC.degone_Q_lower` states the first, and `SpectralC.normLe_mulV` with
`normLe_azero_iff` gives the second, for:
* `A(ξ) = azero ς ξ`, that is, `χ(ξ) ε_G Δ^E`;
* `𝐐(ξ) = degoneQ Λ ξ`;
* `r = rp p`;
* `‖Δ^E‖ ≤ Λ_D` and `‖E_Q(ξ)‖ ≤ η_Q` as hypotheses. The second is supplied by
  `SpectralC.degone_block`, with the paper's `η_Q`.

`glue_h1a`: the first bound of (H1) of Route B (`‖𝐄^*𝐄 - I‖ ≤ ε_V`) from WP-K's
`degoneN_sub_one`, with the Gram identity of `𝐄_ξ` (the polarized `degone_norm`) as hypothesis.

WP-K's matrices are functions `U → U → ℂ` with `mulV`, and its norm is `vnorm`. Here they are
read as `Matrix.of` and `*ᵥ`, with `sqn = vnorm²`. The two lemmas below are this translation,
for `𝕜 = ℂ` and `n = U`.
-/

@[expose] public section

open scoped BigOperators Matrix
open Finset

namespace Sarkozy.Spectral

variable {U : Type*} [Fintype U] [DecidableEq U] {p : ℕ} [Fact p.Prime]

omit [DecidableEq U] in
theorem sqn_eq_vnorm_sq (w : U → ℂ) : sqn w = SpectralC.vnorm w ^ 2 := by
  rw [SpectralC.vnorm, Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
  rfl

omit [DecidableEq U] in
theorem mulVec_of_eq_mulV (M : U → U → ℂ) (w : U → ℂ) :
    Matrix.of M *ᵥ w = SpectralC.mulV M w := by
  funext k
  simp [Matrix.mulVec, dotProduct, SpectralC.mulV]

/-- **`hQ` of `coupling_block`** from `SpectralC.degone_Q_lower`. -/
theorem glue_hQ (hp2 : p ≠ 2) (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) (ς : U → U → ZMod p)
    {ξ : ZMod p} (hξ : ξ ≠ 0) {ΛD η : ℝ} (hΛD : 0 ≤ ΛD) (hη : 0 ≤ η)
    (hD : SpectralC.NormLe (SpectralC.deltaE ς) ΛD)
    (hE : SpectralC.NormLe (SpectralC.errQ Λ ς ξ) η) (w : U → ℂ) :
    SpectralC.rp p ^ 2 * (sqn (Matrix.of (SpectralC.azero ς ξ) *ᵥ w) - 2 * ΛD * η * sqn w) ≤
      sqn (Matrix.of (SpectralC.degoneQ Λ ξ) *ᵥ w) := by
  rw [mulVec_of_eq_mulV, mulVec_of_eq_mulV, sqn_eq_vnorm_sq, sqn_eq_vnorm_sq, sqn_eq_vnorm_sq]
  exact SpectralC.degone_Q_lower hp2 Λ ς hξ hΛD hη hD hE w

omit [DecidableEq U] in
/-- **`hA` of `coupling_block`**: `|A(ξ) w| ≤ Λ_D |w|` for `A(ξ) = χ(ξ) ε_G Δ^E`, `ξ ≠ 0`. -/
theorem glue_hA (hp2 : p ≠ 2) (ς : U → U → ZMod p) {ξ : ZMod p} (hξ : ξ ≠ 0) {ΛD : ℝ}
    (hΛD : 0 ≤ ΛD) (hD : SpectralC.NormLe (SpectralC.deltaE ς) ΛD) (w : U → ℂ) :
    sqn (Matrix.of (SpectralC.azero ς ξ) *ᵥ w) ≤ ΛD ^ 2 * sqn w := by
  rw [mulVec_of_eq_mulV, sqn_eq_vnorm_sq, sqn_eq_vnorm_sq]
  have h := SpectralC.normLe_mulV ((SpectralC.normLe_azero_iff hp2 ς hξ ΛD).mpr hD) hΛD w
  have h0 := SpectralC.vnorm_nonneg (SpectralC.mulV (SpectralC.azero ς ξ) w)
  calc SpectralC.vnorm (SpectralC.mulV (SpectralC.azero ς ξ) w) ^ 2
      ≤ (ΛD * SpectralC.vnorm w) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = ΛD ^ 2 * SpectralC.vnorm w ^ 2 := by ring

omit [DecidableEq U] in
/-- WP-K's bilinear form is `w^* M z`. -/
theorem bform_eq_dotProduct (M : U → U → ℂ) (w z : U → ℂ) :
    SpectralC.bform M w z = star w ⬝ᵥ (Matrix.of M *ᵥ z) := by
  simp only [SpectralC.bform, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
    RCLike.star_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

section Frame

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **(H1), the first bound, from `SpectralC.degoneN_sub_one`** (`lem:record:frame-inputs` (i),
`ε_V`). If the Gram matrix of `𝐄_ξ` on the mode is WP-K's `degoneN μ ξ` (`hgram`, the
polarized `degone_norm`, in a realization of `L²(μ)`) and `‖N(ξ) - I‖ ≤ ε_V`, then
`|⟪𝐄u, 𝐄w⟫ - u^* w| ≤ ε_V |u| |w|`, the hypothesis `h1a` of `routeB_a` on that mode. -/
theorem glue_h1a (E : (U → ℂ) →ₗ[ℂ] H) (μ : (U → ZMod p) → ℝ) (ξ : ZMod p) {εV : ℝ}
    (hgram : ∀ u w, inner ℂ (E u) (E w) = star u ⬝ᵥ (Matrix.of (SpectralC.degoneN μ ξ) *ᵥ w))
    (hN : SpectralC.NormLe (fun k l => SpectralC.degoneN μ ξ k l - if k = l then 1 else 0) εV)
    (u w : U → ℂ) :
    ‖inner ℂ (E u) (E w) - star u ⬝ᵥ w‖ ≤ εV * √(sqn u) * √(sqn w) := by
  have e : inner ℂ (E u) (E w) - star u ⬝ᵥ w =
      SpectralC.bform (fun k l => SpectralC.degoneN μ ξ k l - if k = l then 1 else 0) u w := by
    rw [hgram, bform_eq_dotProduct]
    have h1 : Matrix.of (fun k l => SpectralC.degoneN μ ξ k l - if k = l then (1 : ℂ) else 0) =
        Matrix.of (SpectralC.degoneN μ ξ) - 1 := by
      ext k l
      simp [Matrix.one_apply]
    rw [h1, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
  rw [e]
  have h := hN u w
  have hu : SpectralC.vnorm u = √(sqn u) := by rw [sqn_eq_vnorm_sq, Real.sqrt_sq
    (SpectralC.vnorm_nonneg u)]
  have hw : SpectralC.vnorm w = √(sqn w) := by rw [sqn_eq_vnorm_sq, Real.sqrt_sq
    (SpectralC.vnorm_nonneg w)]
  rw [hu, hw] at h
  exact h

end Frame

end Sarkozy.Spectral
