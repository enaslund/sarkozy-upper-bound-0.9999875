module

public import Sarkozy.SpectralC.MatrixNorms

@[expose] public section

/-!
# The norm equivalence on `𝒱` (`lem:spec:degone`(c), last claim)

`paper/sections/14_spectral.tex`, `lem:spec:degone`(c): if `‖𝐍(ξ) − I‖ ≤ ε_V` for every `ξ ≠ 0`
(`degoneN_sub_one`), then `(1 − ε_V)‖g‖² ≤ ‖v‖²_μ ≤ (1 + ε_V)‖g‖²` for every
`v = ∑_k g_k(x_k)` with mean-zero `g_k`, where `‖g‖² = ∑_k ‖g_k‖²` (`degone_equiv`,
`degone_equiv_bounds`). The proof expands `v = ∑_{ξ ≠ 0} v_ξ` into the mode components
`v_ξ = ∑_k ĝ_k(ξ) e_ξ(x_k)` (`sum_modeV`, `modeV_zero`), uses their orthogonality in `L²(μ)`
(`degone_modes_orth`), the identity `‖v_ξ‖²_μ = ĝ(ξ)^*𝐍(ξ)ĝ(ξ)` (`degone_norm`) and Parseval
(`l2sq_eq_sum_fcoef`). `degone_equiv_coeffs` is the same bound for `v` given by its Fourier
coefficients `c(ξ) ∈ ℂ^{U⁺}` (the form of Step 2 of `cor:spec2:coupling`).

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- The mode component `v_ξ(x) = ∑_k ĝ_k(ξ) e_ξ(x_k)`. -/
noncomputable def modeV (g : U → ZMod p → ℂ) (ξ : ZMod p) (x : U → ZMod p) : ℂ :=
  ∑ k, fcoef (g k) ξ * ech ξ (x k)

omit [DecidableEq U] in
lemma sum_modeV (g : U → ZMod p → ℂ) (x : U → ZMod p) :
    ∑ k, g k (x k) = ∑ ξ, modeV g ξ x := by
  unfold modeV
  rw [sum_comm]
  exact sum_congr rfl fun k _ => fourier_inv (g k) (x k)

omit [DecidableEq U] in
lemma fcoef_zero_of_sum (h : ZMod p → ℂ) (hh : ∑ a, h a = 0) : fcoef h 0 = 0 := by
  rw [fcoef_zero, hh, mul_zero]

omit [DecidableEq U] in
lemma modeV_zero (g : U → ZMod p → ℂ) (hg : ∀ k, ∑ a, g k a = 0) (x : U → ZMod p) :
    modeV g 0 x = 0 := by
  unfold modeV
  exact sum_eq_zero fun k _ => by rw [fcoef_zero_of_sum _ (hg k), zero_mul]

/-- `w^*𝐍w = |w|² + w^*(𝐍 − I)w`. -/
lemma qform_eq_add_bform (N : U → U → ℂ) (w : U → ℂ) :
    qform N w = ((∑ k, ‖w k‖ ^ 2 : ℝ) : ℂ) +
      bform (fun k l => N k l - if k = l then 1 else 0) w w := by
  have h1 : ∀ k, ∑ l, conj (w k) * N k l * w l =
      conj (w k) * w k + ∑ l, conj (w k) * (N k l - if k = l then 1 else 0) * w l := by
    intro k
    have h2 : ∑ l, conj (w k) * (N k l - if k = l then 1 else 0) * w l =
        ∑ l, conj (w k) * N k l * w l - ∑ l, conj (w k) * (if k = l then 1 else 0) * w l := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun l _ => by ring
    have h3 : ∑ l, conj (w k) * (if k = l then 1 else 0) * w l = conj (w k) * w k := by
      rw [sum_eq_single k (fun b _ hb => by rw [ite_eq_right (Ne.symm hb)]; ring)
        (fun h => absurd (mem_univ k) h), ite_eq_left rfl, mul_one]
    rw [h2, h3]
    ring
  unfold qform bform
  rw [sum_congr rfl fun k _ => h1 k, sum_add_distrib]
  congr 1
  push_cast
  exact sum_congr rfl fun k _ => Complex.conj_mul' (w k)

omit [DecidableEq U] in
lemma vnorm_mul_self (w : U → ℂ) : vnorm w * vnorm w = ∑ k, ‖w k‖ ^ 2 :=
  Real.mul_self_sqrt (sum_nonneg fun _ _ => sq_nonneg _)

/-- **`lem:spec:degone`(c), the norm equivalence**: if `‖𝐍(ξ) − I‖ ≤ ε_V` for `ξ ≠ 0`, then
`|‖v‖²_μ − ‖g‖²| ≤ ε_V ‖g‖²` for `v = ∑_k g_k(x_k)`, `g_k` mean-zero, `‖g‖² = ∑_k ‖g_k‖²`. -/
theorem degone_equiv (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {εV : ℝ} (hN : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (fun k l => degoneN μ ξ k l - if k = l then 1 else 0) εV)
    (g : U → ZMod p → ℂ) (hg : ∀ k, ∑ a, g k a = 0) :
    |∑ x, μ x * ‖∑ k, g k (x k)‖ ^ 2 - ∑ k, l2sq (g k)| ≤ εV * ∑ k, l2sq (g k) := by
  set a : ZMod p → ℝ := fun ξ => ∑ x, μ x * ‖modeV g ξ x‖ ^ 2 with ha
  set G : ZMod p → ℝ := fun ξ => ∑ k, ‖fcoef (g k) ξ‖ ^ 2 with hG
  -- `‖v‖²_μ = ∑_ξ ‖v_ξ‖²_μ`
  have hA : ∑ x, μ x * ‖∑ k, g k (x k)‖ ^ 2 = ∑ ξ, a ξ := by
    have hC : ((∑ x, μ x * ‖∑ k, g k (x k)‖ ^ 2 : ℝ) : ℂ) = ((∑ ξ, a ξ : ℝ) : ℂ) := by
      have hL : ((∑ x, μ x * ‖∑ k, g k (x k)‖ ^ 2 : ℝ) : ℂ) =
          ∑ ξ, ∑ η, ∑ x, (μ x : ℂ) * (conj (modeV g ξ x) * modeV g η x) := by
        push_cast
        have hx : ∀ x, (μ x : ℂ) * (‖∑ k, g k (x k)‖ : ℂ) ^ 2 =
            ∑ ξ, ∑ η, (μ x : ℂ) * (conj (modeV g ξ x) * modeV g η x) := by
          intro x
          rw [← Complex.conj_mul', sum_modeV, map_sum, sum_mul_sum, mul_sum]
          exact sum_congr rfl fun ξ _ => by rw [mul_sum]
        rw [sum_congr rfl fun x _ => hx x, sum_comm]
        exact sum_congr rfl fun ξ _ => sum_comm
      have hdiag : ∀ ξ, ∑ η, ∑ x, (μ x : ℂ) * (conj (modeV g ξ x) * modeV g η x) =
          ∑ x, (μ x : ℂ) * (conj (modeV g ξ x) * modeV g ξ x) := by
        intro ξ
        have horth : ∀ η, η ≠ ξ →
            ∑ x, (μ x : ℂ) * (conj (modeV g ξ x) * modeV g η x) = 0 := by
          intro η hη
          unfold modeV
          exact degone_modes_orth μ hinv (Ne.symm hη) (fun k => fcoef (g k) ξ)
            (fun k => fcoef (g k) η)
        rw [sum_eq_single ξ (fun η _ hη => horth η hη) (fun h => absurd (mem_univ ξ) h)]
      rw [hL, sum_congr rfl fun ξ _ => hdiag ξ]
      simp only [ha]
      push_cast
      exact sum_congr rfl fun ξ _ => sum_congr rfl fun x _ => by rw [Complex.conj_mul']
    exact_mod_cast hC
  -- Parseval: `∑_ξ |ĝ(ξ)|² = ‖g‖²`
  have hP : ∑ ξ, G ξ = ∑ k, l2sq (g k) := by
    simp only [hG]
    rw [sum_comm]
    exact sum_congr rfl fun k _ => (l2sq_eq_sum_fcoef (g k)).symm
  -- each mode
  have hmode : ∀ ξ, |a ξ - G ξ| ≤ εV * G ξ := by
    intro ξ
    by_cases hξ : ξ = 0
    · subst hξ
      have ha0 : a 0 = 0 := by
        simp only [ha]
        exact sum_eq_zero fun x _ => by rw [modeV_zero g hg x, norm_zero]; ring
      have hG0 : G 0 = 0 := by
        simp only [hG]
        exact sum_eq_zero fun k _ => by rw [fcoef_zero_of_sum _ (hg k), norm_zero]; ring
      rw [ha0, hG0]
      simp
    · have hq := degone_norm hp2 μ hμ1 hinv hinj hξ (fun k => fcoef (g k) ξ)
      rw [qform_eq_add_bform] at hq
      have hb : bform (fun k l => degoneN μ ξ k l - if k = l then 1 else 0)
          (fun k => fcoef (g k) ξ) (fun k => fcoef (g k) ξ) = ((a ξ - G ξ : ℝ) : ℂ) := by
        have hq' : ((a ξ : ℝ) : ℂ) = ((G ξ : ℝ) : ℂ) +
            bform (fun k l => degoneN μ ξ k l - if k = l then 1 else 0)
              (fun k => fcoef (g k) ξ) (fun k => fcoef (g k) ξ) := by
          rw [← hq]
          simp only [ha]
          push_cast
          rfl
        rw [Complex.ofReal_sub, hq']
        ring
      have hbd := hN ξ hξ (fun k => fcoef (g k) ξ) (fun k => fcoef (g k) ξ)
      rw [hb, Complex.norm_real, Real.norm_eq_abs, mul_assoc, vnorm_mul_self] at hbd
      exact hbd
  rw [hA, ← hP, ← sum_sub_distrib, mul_sum]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ξ _ => hmode ξ)

/-- **`lem:spec:degone`(c)**: `(1 − ε_V)‖g‖² ≤ ‖v‖²_μ ≤ (1 + ε_V)‖g‖²`. -/
theorem degone_equiv_bounds (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {εV : ℝ} (hN : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (fun k l => degoneN μ ξ k l - if k = l then 1 else 0) εV)
    (g : U → ZMod p → ℂ) (hg : ∀ k, ∑ a, g k a = 0) :
    (1 - εV) * ∑ k, l2sq (g k) ≤ ∑ x, μ x * ‖∑ k, g k (x k)‖ ^ 2 ∧
      ∑ x, μ x * ‖∑ k, g k (x k)‖ ^ 2 ≤ (1 + εV) * ∑ k, l2sq (g k) := by
  have h := abs_le.mp (degone_equiv hp2 μ hμ1 hinv hinj hN g hg)
  constructor <;> linarith [h.1, h.2]

omit [DecidableEq U] in
/-- The Fourier coefficients of a trigonometric polynomial: `\widehat{∑_η c_η e_η}(ξ) = c_ξ`. -/
lemma fcoef_trig (c : ZMod p → ℂ) (ξ : ZMod p) :
    fcoef (fun a => ∑ η, c η * ech η a) ξ = c ξ := by
  have h : ∀ a, conj (ech ξ a) * ∑ η, c η * ech η a =
      ∑ η, c η * (conj (ech ξ a) * ech η a) := by
    intro a; rw [mul_sum]; exact sum_congr rfl fun η _ => by ring
  unfold fcoef ip
  dsimp only
  rw [sum_congr rfl fun a _ => h a, sum_comm, mul_sum]
  have h2 : ∀ η, (p : ℂ)⁻¹ * ∑ a, c η * (conj (ech ξ a) * ech η a) =
      c η * ip (ech ξ) (ech η) := by
    intro η; unfold ip; rw [← mul_sum]; ring
  rw [sum_congr rfl fun η _ => h2 η]
  simp_rw [ip_ech_ech]
  simp

/-- **`lem:spec:degone`(c) in coefficient form**: for `v = ∑_{ξ} ∑_k c_k(ξ) e_ξ(x_k)` with
`c(0) = 0` (any complex coefficients), `|‖v‖²_μ − ∑_ξ |c(ξ)|²| ≤ ε_V ∑_ξ |c(ξ)|²`; this is the
form used in Step 2 of `cor:spec2:coupling` (with `c(ξ) = 𝐐(ξ)ĝ(ξ)`). -/
theorem degone_equiv_coeffs (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {εV : ℝ} (hN : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (fun k l => degoneN μ ξ k l - if k = l then 1 else 0) εV)
    (c : ZMod p → U → ℂ) (hc0 : ∀ k, c 0 k = 0) :
    |∑ x, μ x * ‖∑ ξ, ∑ k, c ξ k * ech ξ (x k)‖ ^ 2 - ∑ ξ, ∑ k, ‖c ξ k‖ ^ 2| ≤
      εV * ∑ ξ, ∑ k, ‖c ξ k‖ ^ 2 := by
  set g : U → ZMod p → ℂ := fun k a => ∑ ξ, c ξ k * ech ξ a with hg
  have hgsum : ∀ k, ∑ a, g k a = 0 := by
    intro k
    simp only [hg]
    rw [sum_comm]
    have h1 : ∀ ξ : ZMod p, ∑ a, c ξ k * ech ξ a = c ξ k * (if ξ = 0 then (p : ℂ) else 0) := by
      intro ξ; rw [← mul_sum, sum_ech]
    rw [sum_congr rfl fun ξ _ => h1 ξ]
    simp [hc0]
  have hfc : ∀ k ξ, fcoef (g k) ξ = c ξ k := fun k ξ => fcoef_trig (fun η => c η k) ξ
  have hG : ∑ k, l2sq (g k) = ∑ ξ, ∑ k, ‖c ξ k‖ ^ 2 := by
    rw [sum_comm]
    exact sum_congr rfl fun k _ => by
      rw [l2sq_eq_sum_fcoef]; exact sum_congr rfl fun ξ _ => by rw [hfc]
  have hv : ∀ x : U → ZMod p, ∑ k, g k (x k) = ∑ ξ, ∑ k, c ξ k * ech ξ (x k) := by
    intro x; simp only [hg]; rw [sum_comm]
  have h := degone_equiv hp2 μ hμ1 hinv hinj hN g hgsum
  rw [hG, sum_congr rfl fun x _ => by rw [hv x]] at h
  exact h

end Sarkozy.SpectralC
