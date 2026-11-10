module

public import Sarkozy.SpectralC.CovariantFields

@[expose] public section

/-!
# Modes of coupling data (`lem:coupling-modes`)

`paper/sections/14_spectral.tex`, `def:coupling-data` and `lem:coupling-modes`, in the generality
the proof uses: a finite set `𝒴` (the labellings `𝓘⁺`) with weights `ν` and an action of `Aff_p`
preserving them (`AffAction`), and covariant probability vectors `P_k(· | y)` on `𝔽_p`
(`P_k(γa | γy) = P_k(a | y)`, condition (ii) of `def:coupling-data`). With
`Ψ_k(y, a) = p P_k(a | y) − 1` (`psiField`), `H̃_kl = E_ν⟨Ψ_k, Ψ_l⟩`, `𝐃_kl = E_ν⟨Ψ_k, CΨ_l⟩`
and `𝐌(ξ) = H̃/(p − 1) + (p/(p − 1)) c_ξ 𝐃` (`couplingM`), for `F_V = ∑_k g_k(x_k)` with
mean-zero `g_k` and `(𝒫F_V)(y) = ∑_k ∑_a P_k(a | y) g_k(a)` (`condField`):

* `coupling_modes`: `‖𝒫F_V‖²_ν = ∑_{ξ ≠ 0} ĝ(ξ)^* 𝐌(ξ) ĝ(ξ)`;
* `couplingM_hermitian`: `𝐌(ξ)` is Hermitian;
* `instanceA_bound`: if `Op H = ϱ · 𝒫H` (`lem:spec:cutkernel`(b), instance (A)), then
  `‖Op F_V‖²_μ ≤ (sup ϱ) ‖𝒫F_V‖²_{m_p}`, `m_p = ϱ μ`.

The support and density conditions (i), (iii) of `def:coupling-data` are not used by this lemma.
New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {𝒴 ι : Type*} [Fintype 𝒴] [Fintype ι]

/-- `Ψ_k(y, a) = p P_k(a | y) − 1`. -/
noncomputable def psiField (P : ι → 𝒴 → ZMod p → ℝ) (k : ι) (y : 𝒴) (a : ZMod p) : ℂ :=
  (p : ℂ) * (P k y a : ℂ) - 1

/-- `𝐌(ξ) = H̃/(p − 1) + (p/(p − 1)) c_ξ 𝐃`, with `H̃ = E_ν⟨Ψ_k, Ψ_l⟩` and
`𝐃 = E_ν⟨Ψ_k, CΨ_l⟩`. -/
noncomputable def couplingM (ν : 𝒴 → ℝ) (P : ι → 𝒴 → ZMod p → ℝ) (ξ : ZMod p) (k l : ι) : ℂ :=
  gramΓ ν (psiField P) k l / ((p : ℂ) - 1) +
    (p : ℂ) / ((p : ℂ) - 1) * gaussEig ξ * gramP ν (psiField P) k l

/-- `(𝒫F_V)(y) = ∑_k ∑_a P_k(a | y) g_k(a)`. -/
noncomputable def condField (P : ι → 𝒴 → ZMod p → ℝ) (g : ι → ZMod p → ℂ) (y : 𝒴) : ℂ :=
  ∑ k, ∑ a, (P k y a : ℂ) * g k a

/-- The mode `Y_ξ(y) = E_a[∑_k ĝ_k(ξ) Ψ_k(y, a) e_ξ(a)]`. -/
noncomputable def modeY (P : ι → 𝒴 → ZMod p → ℝ) (g : ι → ZMod p → ℂ) (ξ : ZMod p) (y : 𝒴) : ℂ :=
  (p : ℂ)⁻¹ * ∑ a, fieldW (psiField P) (fun k => fcoef (g k) ξ) y a * ech ξ a

omit [Fintype 𝒴] in
lemma condField_eq_sum_modeY (P : ι → 𝒴 → ZMod p → ℝ)
    (g : ι → ZMod p → ℂ) (hg : ∀ k, ∑ a, g k a = 0) (y : 𝒴) :
    condField P g y = ∑ ξ, modeY P g ξ y := by
  have hpC := p_ne_zero_C (p := p)
  -- `∑_a P g = E_a[Ψ g]`
  have h1 : ∀ k, ∑ a, (P k y a : ℂ) * g k a = (p : ℂ)⁻¹ * ∑ a, psiField P k y a * g k a := by
    intro k
    unfold psiField
    simp_rw [sub_mul, sum_sub_distrib, one_mul, hg k, sub_zero, mul_assoc, ← mul_sum,
      ← mul_assoc, inv_mul_cancel₀ hpC, one_mul]
  unfold condField modeY fieldW
  simp_rw [h1]
  -- expand `g_k` in characters
  have h2 : ∀ k a, psiField P k y a * g k a =
      ∑ ξ, fcoef (g k) ξ * psiField P k y a * ech ξ a := by
    intro k a
    rw [fourier_inv (g k) a, mul_sum]
    apply sum_congr rfl; intro ξ _; ring
  simp_rw [h2]
  simp only [mul_sum, sum_mul]
  refine (sum_congr rfl fun k _ => sum_comm).trans ?_
  refine sum_comm.trans ?_
  refine sum_congr rfl fun ξ _ => ?_
  refine sum_comm.trans ?_
  refine sum_congr rfl fun a _ => sum_congr rfl fun k _ => ?_
  ring

omit [Fintype 𝒴] in
lemma modeY_zero (P : ι → 𝒴 → ZMod p → ℝ) (g : ι → ZMod p → ℂ) (hg : ∀ k, ∑ a, g k a = 0)
    (y : 𝒴) : modeY P g 0 y = 0 := by
  unfold modeY fieldW
  simp_rw [fcoef_zero, hg, mul_zero, zero_mul, sum_const_zero, zero_mul, sum_const_zero,
    mul_zero]

omit [Fintype 𝒴] in
/-- Translation covariance of the modes: `Y_ξ(y + c𝟙) = e_ξ(c) Y_ξ(y)`. -/
lemma modeY_translate {ν : 𝒴 → ℝ} (G : AffAction p 𝒴 ν) (P : ι → 𝒴 → ZMod p → ℝ)
    (hPcov : ∀ (k : ι) (s c : ZMod p) (y : 𝒴) (a : ZMod p), s ≠ 0 → IsSquare s →
      P k (G.act s c y) (s * a + c) = P k y a)
    (g : ι → ZMod p → ℂ) (ξ c : ZMod p) (y : 𝒴) :
    modeY P g ξ (G.act 1 c y) = ech ξ c * modeY P g ξ y := by
  unfold modeY
  have hre : ∑ a, fieldW (psiField P) (fun k => fcoef (g k) ξ) (G.act 1 c y) a * ech ξ a =
      ∑ a, fieldW (psiField P) (fun k => fcoef (g k) ξ) (G.act 1 c y) (a + c) * ech ξ (a + c) :=
    (Fintype.sum_equiv (Equiv.addRight c) _ _ (fun a => by simp)).symm
  rw [hre]
  have hcov : ∀ a, fieldW (psiField P) (fun k => fcoef (g k) ξ) (G.act 1 c y) (a + c) =
      fieldW (psiField P) (fun k => fcoef (g k) ξ) y a := by
    intro a
    unfold fieldW psiField
    apply sum_congr rfl
    intro k _
    have := hPcov k 1 c y a one_ne_zero ⟨1, by ring⟩
    rw [one_mul] at this
    rw [this]
  simp_rw [hcov, ech_add_right]
  simp only [mul_sum]
  apply sum_congr rfl; intro a _
  ring

/-- Orthogonality of the modes in `L²(ν)`. -/
lemma modeY_orth {ν : 𝒴 → ℝ} (G : AffAction p 𝒴 ν) (P : ι → 𝒴 → ZMod p → ℝ)
    (hPcov : ∀ (k : ι) (s c : ZMod p) (y : 𝒴) (a : ZMod p), s ≠ 0 → IsSquare s →
      P k (G.act s c y) (s * a + c) = P k y a)
    (g : ι → ZMod p → ℂ) {ξ η : ZMod p} (hξη : ξ ≠ η) :
    ∑ y, (ν y : ℂ) * (conj (modeY P g ξ y) * modeY P g η y) = 0 := by
  set S := ∑ y, (ν y : ℂ) * (conj (modeY P g ξ y) * modeY P g η y) with hS
  have hbij := G.bij 1 1 one_ne_zero ⟨1, by ring⟩
  have h1 : S = conj (ech ξ 1) * ech η 1 * S := by
    conv_lhs => rw [hS, ← hbij.sum_comp]
    rw [hS, mul_sum]
    apply sum_congr rfl
    intro y _
    rw [G.pres 1 1 y one_ne_zero ⟨1, by ring⟩, modeY_translate G P hPcov,
      modeY_translate G P hPcov, map_mul]
    ring
  have h2 : conj (ech ξ 1) * ech η 1 = ech (η - ξ) 1 := by
    rw [conj_ech, ← ech_add_left]
    ring_nf
  have h3 : ech (η - ξ) (1 : ZMod p) ≠ 1 := by
    intro h
    unfold ech at h
    rw [mul_one, ← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := p))] at h
    exact hξη (sub_eq_zero.mp (ZMod.injective_stdAddChar h)).symm
  rw [h2] at h1
  have : (1 - ech (η - ξ) (1 : ZMod p)) * S = 0 := by linear_combination h1
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm h3
  · exact h

omit [Fintype ι] in
lemma gramM_psi_zero (ν : 𝒴 → ℝ) (P : ι → 𝒴 → ZMod p → ℝ)
    (hP1 : ∀ k y, ν y ≠ 0 → ∑ a, P k y a = 1) :
    gramM ν (psiField P) = 0 := by
  have hz : ∀ k y, ν y ≠ 0 → ∑ a, psiField P k y a = 0 := by
    intro k y hy
    unfold psiField
    rw [sum_sub_distrib, ← mul_sum]
    have : ∑ a, (P k y a : ℂ) = 1 := by exact_mod_cast hP1 k y hy
    rw [this, mul_one, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one, sub_self]
  funext k l
  unfold gramM
  apply sum_eq_zero
  intro y _
  by_cases hy : ν y = 0
  · rw [hy]; simp
  · rw [hz k y hy, hz l y hy]; simp

/-- **`lem:coupling-modes`**: `‖𝒫F_V‖²_ν = ∑_{ξ ≠ 0} ĝ(ξ)^* 𝐌(ξ) ĝ(ξ)`. -/
theorem coupling_modes [DecidableEq ι] (hp2 : p ≠ 2) (ν : 𝒴 → ℝ) (G : AffAction p 𝒴 ν)
    (P : ι → 𝒴 → ZMod p → ℝ) (hP1 : ∀ k y, ν y ≠ 0 → ∑ a, P k y a = 1)
    (hPcov : ∀ (k : ι) (s c : ZMod p) (y : 𝒴) (a : ZMod p), s ≠ 0 → IsSquare s →
      P k (G.act s c y) (s * a + c) = P k y a)
    (g : ι → ZMod p → ℂ) (hg : ∀ k, ∑ a, g k a = 0) :
    ∑ y, (ν y : ℂ) * ((‖condField P g y‖ ^ 2 : ℝ) : ℂ) =
      ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
        qform (couplingM ν P ξ) (fun k => fcoef (g k) ξ) := by
  have hnorm : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = conj z * z := by
    intro z
    rw [Complex.ofReal_pow, ← Complex.mul_conj', mul_comm]
  simp_rw [hnorm, condField_eq_sum_modeY P g hg, map_sum, sum_mul, mul_sum]
  -- the cross terms vanish
  have hdiag : ∀ ξ, ∑ y, ∑ η, (ν y : ℂ) * (conj (modeY P g ξ y) * modeY P g η y) =
      ∑ y, (ν y : ℂ) * (conj (modeY P g ξ y) * modeY P g ξ y) := by
    intro ξ
    rw [sum_comm, sum_eq_single ξ]
    · intro η _ hη
      exact modeY_orth G P hPcov g (Ne.symm hη)
    · intro h0; exact absurd (mem_univ ξ) h0
  have hswap : ∑ y, ∑ ξ, ∑ η, (ν y : ℂ) * (conj (modeY P g ξ y) * modeY P g η y) =
      ∑ ξ, ∑ y, ∑ η, (ν y : ℂ) * (conj (modeY P g ξ y) * modeY P g η y) := sum_comm
  rw [hswap]
  simp_rw [hdiag]
  rw [← sum_filter_add_sum_filter_not univ (fun ξ : ZMod p => ξ ≠ 0)]
  have hzero : ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ¬ ξ ≠ 0),
      ∑ y, (ν y : ℂ) * (conj (modeY P g ξ y) * modeY P g ξ y) = 0 := by
    apply sum_eq_zero
    intro ξ hξ
    rw [mem_filter, not_not] at hξ
    rw [hξ.2]
    simp_rw [modeY_zero P g hg, map_zero, zero_mul, mul_zero, sum_const_zero]
  rw [hzero, add_zero]
  apply sum_congr rfl
  intro ξ hξ
  have hξ0 : ξ ≠ 0 := (mem_filter.mp hξ).2
  -- the covariant-field formula for `Ψ`
  have hcov : ∀ (k : ι) (s c : ZMod p) (y : 𝒴) (a : ZMod p), s ≠ 0 → IsSquare s →
      psiField P k (G.act s c y) (s * a + c) = psiField P k y a := by
    intro k s c y a hs hsq
    unfold psiField
    rw [hPcov k s c y a hs hsq]
  have hcf := covariant_fields hp2 ν G (psiField P) hcov hξ0 (fun k => fcoef (g k) ξ)
  simp_rw [hnorm] at hcf
  have hY : ∀ y, modeY P g ξ y =
      (p : ℂ)⁻¹ * ∑ a, fieldW (psiField P) (fun k => fcoef (g k) ξ) y a * ech ξ a := fun y => rfl
  simp_rw [hY]
  rw [hcf, gramM_psi_zero ν P hP1]
  have hq0 : qform (0 : ι → ι → ℂ) (fun k => fcoef (g k) ξ) = 0 := by
    unfold qform; simp
  rw [hq0, sub_zero]
  -- `χ(ξ) G_χ = p c_ξ` and linearity of `qform`
  have hlin : qform (couplingM ν P ξ) (fun k => fcoef (g k) ξ) =
      ((p : ℂ) - 1)⁻¹ * qform (gramΓ ν (psiField P)) (fun k => fcoef (g k) ξ) +
        (p : ℂ) / ((p : ℂ) - 1) * gaussEig ξ * qform (gramP ν (psiField P))
          (fun k => fcoef (g k) ξ) := by
    unfold couplingM qform
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro k _
    apply sum_congr rfl; intro l _
    ring
  rw [hlin, gaussEig_eq]
  have hpC := p_ne_zero_C (p := p)
  field_simp

/-- **`lem:coupling-modes`, instance (A)**: if `Op H = ϱ · 𝒫H` (`lem:spec:cutkernel`(b)) with
`0 ≤ ϱ ≤ R` and `m_p = ϱ μ`, then `‖Op F_V‖²_μ ≤ R ‖𝒫F_V‖²_{m_p}`. -/
theorem instanceA_bound (μ ϱ : 𝒴 → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hϱ : ∀ y, 0 ≤ ϱ y) {R : ℝ}
    (hR : ∀ y, ϱ y ≤ R) (OpF PF : 𝒴 → ℂ) (hOp : ∀ y, OpF y = (ϱ y : ℂ) * PF y) :
    ∑ y, μ y * ‖OpF y‖ ^ 2 ≤ R * ∑ y, (μ y * ϱ y) * ‖PF y‖ ^ 2 := by
  rw [mul_sum]
  apply sum_le_sum
  intro y _
  rw [hOp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hϱ y), mul_pow]
  have h1 : 0 ≤ μ y * ϱ y * ‖PF y‖ ^ 2 := by
    have := hμ y; have := hϱ y; positivity
  have h2 : μ y * (ϱ y ^ 2 * ‖PF y‖ ^ 2) = ϱ y * (μ y * ϱ y * ‖PF y‖ ^ 2) := by ring
  rw [h2]
  exact mul_le_mul_of_nonneg_right (hR y) h1

/-! ## `𝐌(ξ)` is Hermitian -/

lemma qform_single [DecidableEq ι] (X : ι → ι → ℂ) (i : ι) :
    qform X (fun k => if k = i then 1 else 0) = X i i := by
  unfold qform
  rw [sum_eq_single i, sum_eq_single i]
  · simp
  · intro l _ hl; simp [hl]
  · intro h0; exact absurd (mem_univ i) h0
  · intro k _ hk; simp [hk]
  · intro h0; exact absurd (mem_univ i) h0

lemma qform_two [DecidableEq ι] (X : ι → ι → ℂ) {i j : ι} (hij : i ≠ j) (c : ℂ) :
    qform X (fun k => if k = i then 1 else if k = j then c else 0) =
      X i i + X i j * c + conj c * X j i + conj c * X j j * c := by
  unfold qform
  rw [Fintype.sum_eq_add i j hij, Fintype.sum_eq_add i j hij, Fintype.sum_eq_add i j hij]
  · simp [Ne.symm hij]
    ring
  · intro l hl; simp [hl.1, hl.2]
  · intro l hl; simp [hl.1, hl.2]
  · intro k hk; simp [hk.1, hk.2]

/-- A matrix whose quadratic form is real is Hermitian (polarization). -/
theorem hermitian_of_qform_real [DecidableEq ι] (X : ι → ι → ℂ)
    (h : ∀ w, (qform X w).im = 0) (k l : ι) : conj (X l k) = X k l := by
  have hdiag : ∀ i, (X i i).im = 0 := by
    intro i
    have := h (fun k => if k = i then 1 else 0)
    rwa [qform_single] at this
  by_cases hkl : k = l
  · subst hkl
    exact Complex.conj_eq_iff_im.mpr (hdiag k)
  · have h1 := h (fun m => if m = k then 1 else if m = l then 1 else 0)
    have h2 := h (fun m => if m = k then 1 else if m = l then I else 0)
    rw [qform_two X hkl] at h1 h2
    have hk := hdiag k
    have hl := hdiag l
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, map_one]
      at h1 h2
    apply Complex.ext
    · simp only [Complex.conj_re]
      nlinarith
    · simp only [Complex.conj_im]
      nlinarith

/-- `w^*𝐌(ξ)w = E_ν |E_a[Ψ_w(y, a) e_ξ(a)]|²` for `ξ ≠ 0`. -/
theorem qform_couplingM (hp2 : p ≠ 2) (ν : 𝒴 → ℝ) (G : AffAction p 𝒴 ν)
    (P : ι → 𝒴 → ZMod p → ℝ) (hP1 : ∀ k y, ν y ≠ 0 → ∑ a, P k y a = 1)
    (hPcov : ∀ (k : ι) (s c : ZMod p) (y : 𝒴) (a : ZMod p), s ≠ 0 → IsSquare s →
      P k (G.act s c y) (s * a + c) = P k y a)
    {ξ : ZMod p} (hξ : ξ ≠ 0) (w : ι → ℂ) :
    qform (couplingM ν P ξ) w =
      ∑ y, (ν y : ℂ) * ((‖(p : ℂ)⁻¹ * ∑ a, fieldW (psiField P) w y a * ech ξ a‖ ^ 2 : ℝ) : ℂ) := by
  have hcov : ∀ (k : ι) (s c : ZMod p) (y : 𝒴) (a : ZMod p), s ≠ 0 → IsSquare s →
      psiField P k (G.act s c y) (s * a + c) = psiField P k y a := by
    intro k s c y a hs hsq
    unfold psiField
    rw [hPcov k s c y a hs hsq]
  rw [covariant_fields hp2 ν G (psiField P) hcov hξ w, gramM_psi_zero ν P hP1]
  have hq0 : qform (0 : ι → ι → ℂ) w = 0 := by unfold qform; simp
  rw [hq0, sub_zero]
  have hlin : qform (couplingM ν P ξ) w =
      ((p : ℂ) - 1)⁻¹ * qform (gramΓ ν (psiField P)) w +
        (p : ℂ) / ((p : ℂ) - 1) * gaussEig ξ * qform (gramP ν (psiField P)) w := by
    unfold couplingM qform
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro k _
    apply sum_congr rfl; intro l _
    ring
  rw [hlin, gaussEig_eq]
  have hpC := p_ne_zero_C (p := p)
  field_simp

/-- **`lem:coupling-modes`: `𝐌(ξ)` is Hermitian** (`ξ ≠ 0`): its quadratic form is the real
number `E_ν |E_a[Ψ_w e_ξ]|²`. -/
theorem couplingM_hermitian [DecidableEq ι] (hp2 : p ≠ 2) (ν : 𝒴 → ℝ) (G : AffAction p 𝒴 ν)
    (P : ι → 𝒴 → ZMod p → ℝ) (hP1 : ∀ k y, ν y ≠ 0 → ∑ a, P k y a = 1)
    (hPcov : ∀ (k : ι) (s c : ZMod p) (y : 𝒴) (a : ZMod p), s ≠ 0 → IsSquare s →
      P k (G.act s c y) (s * a + c) = P k y a)
    {ξ : ZMod p} (hξ : ξ ≠ 0) (k l : ι) :
    conj (couplingM ν P ξ l k) = couplingM ν P ξ k l := by
  apply hermitian_of_qform_real
  intro w
  rw [qform_couplingM hp2 ν G P hP1 hPcov hξ w, Complex.im_sum]
  apply sum_eq_zero
  intro y _
  rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_im, zero_mul, mul_zero, add_zero]

end Sarkozy.SpectralC
