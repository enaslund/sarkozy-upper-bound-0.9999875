module

public import Sarkozy.SpectralC.All
public import Sarkozy.Spectral.Coupling

@[expose] public section

/-!
# Adapters to WP-A's `coupling_block` (`cor:spec2:coupling`)

WP-A's `Sarkozy.Spectral.coupling_block` and `coupling_M_bound` (`Spectral/Coupling.lean`) use
Mathlib matrices, `Sarkozy.Spectral.qform M x y = re(x^* M y)` and
`Sarkozy.Spectral.sqn x = ∑_k |x_k|²`. This package uses functions `U → U → ℂ`, `mulV`,
`qform` and `vnorm`.

The dictionary (`sqn_eq_vnorm_sq`, `mulVec_eq_mulV`, `spectral_qform_eq`): `Matrix U U ℂ` is
`U → U → ℂ`, `mulVec` is `mulV`, `sqn = vnorm²`, and `Spectral.qform M w w = re(qform M w)`.

With it, the inputs of `coupling_block` and `coupling_M_bound` become:
* `hQ`, `hA` (`lem:spec:degone`(b)): `coupling_hQ_hA`, from `degone_Q_lower` and `normLe_mulV`;
* `hvnorm` (`lem:spec:degone`(c), in function form): `coupling_hvnorm`, from
  `degone_equiv_coeffs`;
* `hht` (`lem:spec2:gram`): `spectral_qform_le_of_normLe`, applied to `gram_comparison`;
* Step 1 (`lem:coupling-modes`): `coupling_step1_modes`, from `CouplingData.modes`.

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex
open scoped BigOperators ComplexConjugate Matrix

variable {U : Type*} [Fintype U]

/-- `sqn = vnorm²`. -/
lemma sqn_eq_vnorm_sq (w : U → ℂ) : Sarkozy.Spectral.sqn w = vnorm w ^ 2 := by
  rw [vnorm_sq]; rfl

/-- `mulVec` is `mulV`. -/
lemma mulVec_eq_mulV (M : U → U → ℂ) (w : U → ℂ) : (M : Matrix U U ℂ) *ᵥ w = mulV M w := by
  funext k
  simp [Matrix.mulVec, dotProduct, mulV]

/-- `Spectral.qform M w w = re(w^* M w)`. -/
lemma spectral_qform_eq (M : U → U → ℂ) (w : U → ℂ) :
    Sarkozy.Spectral.qform (M : Matrix U U ℂ) w w = (qform M w).re := by
  unfold Sarkozy.Spectral.qform qform
  rw [RCLike.re_to_complex]
  congr 1
  rw [dotProduct]
  refine sum_congr rfl fun k _ => ?_
  show (star w) k * (∑ l, M k l * w l) = ∑ l, conj (w k) * M k l * w l
  rw [Pi.star_apply, RCLike.star_def, Finset.mul_sum]
  exact sum_congr rfl fun l _ => by ring

/-- **`hht` of `coupling_M_bound`** from a two-sided bound `‖A − B‖ ≤ ρ` (for instance
`gram_comparison`): `w^*Aw ≤ w^*Bw + ρ|w|²`. -/
theorem spectral_qform_le_of_normLe {A B : U → U → ℂ} {ρ : ℝ}
    (h : NormLe (fun k l => A k l - B k l) ρ) (w : U → ℂ) :
    Sarkozy.Spectral.qform (A : Matrix U U ℂ) w w ≤
      Sarkozy.Spectral.qform (B : Matrix U U ℂ) w w + ρ * Sarkozy.Spectral.sqn w := by
  rw [spectral_qform_eq, spectral_qform_eq]
  exact re_qform_le_of_normLe h w

variable [DecidableEq U] {p : ℕ} [Fact p.Prime]

/-- **`hQ` and `hA` of `coupling_block`** (`lem:spec:degone`(b)): with `A(ξ) = 𝐀₀(ξ)`,
`Qm(ξ) = 𝐐(ξ)`, `r = p^{-1/2}`, `Λ = Λ_D` and `η_Q = η`. -/
theorem coupling_hQ_hA (hp2 : p ≠ 2) (Λ : (U → ZMod p) × (U → ZMod p) → ℝ)
    (ς : U → U → ZMod p) {ΛD η : ℝ} (hΛD : 0 ≤ ΛD) (hη : 0 ≤ η) (hD : NormLe (deltaE ς) ΛD)
    (s : Finset (ZMod p)) (hs : ∀ ξ ∈ s, ξ ≠ 0) (hE : ∀ ξ ∈ s, NormLe (errQ Λ ς ξ) η)
    (g : ZMod p → U → ℂ) :
    (∀ ξ ∈ s, rp p ^ 2 * (Sarkozy.Spectral.sqn ((azero ς ξ : Matrix U U ℂ) *ᵥ g ξ) -
        2 * ΛD * η * Sarkozy.Spectral.sqn (g ξ)) ≤
        Sarkozy.Spectral.sqn ((degoneQ Λ ξ : Matrix U U ℂ) *ᵥ g ξ)) ∧
    (∀ ξ ∈ s, Sarkozy.Spectral.sqn ((azero ς ξ : Matrix U U ℂ) *ᵥ g ξ) ≤
        ΛD ^ 2 * Sarkozy.Spectral.sqn (g ξ)) := by
  constructor
  · intro ξ hξ
    rw [mulVec_eq_mulV, mulVec_eq_mulV, sqn_eq_vnorm_sq, sqn_eq_vnorm_sq, sqn_eq_vnorm_sq]
    exact degone_Q_lower hp2 Λ ς (hs ξ hξ) hΛD hη hD (hE ξ hξ) (g ξ)
  · intro ξ hξ
    rw [mulVec_eq_mulV, sqn_eq_vnorm_sq, sqn_eq_vnorm_sq]
    have h := normLe_mulV ((normLe_azero_iff hp2 ς (hs ξ hξ) ΛD).mpr hD) hΛD (g ξ)
    have h0 := vnorm_nonneg (mulV (azero ς ξ) (g ξ))
    calc vnorm (mulV (azero ς ξ) (g ξ)) ^ 2 ≤ (ΛD * vnorm (g ξ)) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = ΛD ^ 2 * vnorm (g ξ) ^ 2 := mul_pow _ _ _

/-- **`hvnorm` of `coupling_block`** (`lem:spec:degone`(c)), in function form: for
`v = ∑_ξ ∑_k c_k(ξ) e_ξ(x_k)` with `c(0) = 0` (for instance `c(ξ) = 𝐐(ξ)ĝ(ξ)`),
`‖v‖²_μ ≤ (1 + ε_V) ∑_ξ |c(ξ)|²`. -/
theorem coupling_hvnorm (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {εV : ℝ} (hN : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (fun k l => degoneN μ ξ k l - if k = l then 1 else 0) εV)
    (c : ZMod p → U → ℂ) (hc0 : ∀ k, c 0 k = 0) :
    ∑ x, μ x * ‖∑ ξ, ∑ k, c ξ k * ech ξ (x k)‖ ^ 2 ≤
      (1 + εV) * ∑ ξ, Sarkozy.Spectral.sqn (c ξ) := by
  have h := abs_le.mp (degone_equiv_coeffs hp2 μ hμ1 hinv hinj hN c hc0)
  have e : ∑ ξ, Sarkozy.Spectral.sqn (c ξ) = ∑ ξ, ∑ k, ‖c ξ k‖ ^ 2 := rfl
  rw [e]
  linarith [h.2]

/-- **Step 1 of `coupling_block`** (`lem:coupling-modes`): `‖𝒫F_V‖²_ν = ∑_{ξ ≠ 0} ĝ^*𝐌(ξ)ĝ` in
WP-A's `qform`. -/
theorem coupling_step1_modes {N : U → Finset U} {ς : U → U → ZMod p}
    {Iplus : Finset (U → ZMod p)} {μ : (U → ZMod p) → ℝ} (D : CouplingData p U N ς Iplus μ)
    (hp2 : p ≠ 2) (g : U → ZMod p → ℂ) (hg : ∀ k, ∑ a, g k a = 0) :
    ∑ x, D.ν x * ‖condField D.P g x‖ ^ 2 =
      ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
        Sarkozy.Spectral.qform (couplingM D.ν D.P ξ : Matrix U U ℂ)
          (fun k => fcoef (g k) ξ) (fun k => fcoef (g k) ξ) := by
  have h := congrArg Complex.re (D.modes hp2 g hg)
  simp only [Complex.re_sum] at h
  rw [sum_congr rfl fun ξ _ => spectral_qform_eq _ _]
  rw [← h]
  refine sum_congr rfl fun x _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

end Sarkozy.SpectralC
