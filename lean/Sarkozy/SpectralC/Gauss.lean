module

public import Sarkozy.SpectralC.Fourier

@[expose] public section

/-!
# The Gauss operator (`lem:spec:gauss`)

`paper/sections/14_spectral.tex`, `lem:spec:gauss`. With `χ` the quadratic character of `𝔽_p`
(`Sarkozy.Characters.chiC`), `G_χ = ∑_t χ(t) e(t/p)` (`Gchi`), `ε_G = G_χ/√p` (`epsG`),
`r = p^{-1/2}` (`rp`), the Gauss operator `(Ch)(a) = E_b χ(b − a) h(b)` (`gaussOp`) and
`(C_ς h)(a) = E_b χ(ς(b − a)) h(b)` (`gaussOpS`):

* `gaussOp_ech`: `C e_ξ = c_ξ e_ξ`, `c_ξ = χ(ξ) ε_G r` (`gaussEig`; `c_0 = 0`, `gaussEig_zero`);
* `epsG_sq`, `epsG_cases`: `ε_G² = χ(−1)`, so `ε_G ∈ {±1}` for `p ≡ 1 (4)` and `ε_G ∈ {±i}` for
  `p ≡ 3 (4)`;
* `norm_gaussEig`: `|c_ξ| = r` for `ξ ≠ 0`;
* `l2sq_gaussOp_le`, `l2sq_gaussOp_ech_one`: `‖C‖ = r` (the bound for every `h`, attained at `e_1`);
* `gaussOp_one`, `gaussOpAdj_one`: `C1 = C*1 = 0`, with `C*` the adjoint (`ip_gaussOp`);
* `conj_gaussEig`, `gaussEig_neg`: `\overline{c_ξ} = c_{−ξ} = χ(−1) c_ξ`;
* `gaussOpS_eq`: `C_ς = χ(ς) C`.

The Gauss sum facts are `thm:gauss` (`Sarkozy.Characters.GaussJacobi`). New material for this
paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

/-- The quadratic Gauss sum `G_χ = ∑_t χ(t) e(t/p)`. -/
noncomputable def Gchi (p : ℕ) [Fact p.Prime] : ℂ :=
  gaussSum (chiC p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ)

/-- `ε_G = G_χ/√p`. -/
noncomputable def epsG (p : ℕ) [Fact p.Prime] : ℂ := Gchi p / (Real.sqrt p : ℂ)

/-- `r = p^{-1/2}`. -/
noncomputable def rp (p : ℕ) : ℝ := (Real.sqrt p)⁻¹

/-- The Gauss operator `(Ch)(a) = E_b χ(b − a) h(b)`. -/
noncomputable def gaussOp (h : ZMod p → ℂ) (a : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ b, chiC p (b - a) * h b

/-- `(C_ς h)(a) = E_b χ(ς(b − a)) h(b)`. -/
noncomputable def gaussOpS (ς : ZMod p) (h : ZMod p → ℂ) (a : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ b, chiC p (ς * (b - a)) * h b

/-- The adjoint `(C^*h)(a) = E_b \overline{χ(a − b)} h(b)`. -/
noncomputable def gaussOpAdj (h : ZMod p → ℂ) (a : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ b, conj (chiC p (a - b)) * h b

/-- The eigenvalue `c_ξ = χ(ξ) ε_G r`. -/
noncomputable def gaussEig (ξ : ZMod p) : ℂ := chiC p ξ * epsG p * (rp p : ℂ)

/-- `‖h‖² = E|h|²`. -/
noncomputable def l2sq (h : ZMod p → ℂ) : ℝ := (p : ℝ)⁻¹ * ∑ a, ‖h a‖ ^ 2

lemma chiC_ne_one (hp2 : p ≠ 2) : chiC p ≠ 1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  unfold chiC
  exact (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int (Int.castRingHom ℂ))).mpr
    (quadraticChar_ne_one hF)

lemma chiC_isQuadratic : (chiC p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp _

lemma chiC_apply (t : ZMod p) : chiC p t = ((quadraticChar (ZMod p) t : ℤ) : ℂ) := rfl

lemma chiC_zero : chiC p 0 = 0 := by
  rw [chiC_apply, quadraticChar_zero, Int.cast_zero]

lemma conj_chiC (t : ZMod p) : conj (chiC p t) = chiC p t := by
  rw [chiC_apply, map_intCast]

lemma norm_chiC {t : ZMod p} (ht : t ≠ 0) : ‖chiC p t‖ = 1 := by
  rw [chiC_apply]
  rcases quadraticChar_dichotomy ht with h | h <;> rw [h] <;> simp

lemma sum_chiC (hp2 : p ≠ 2) : ∑ t, chiC p t = 0 :=
  MulChar.sum_eq_zero_of_ne_one (chiC_ne_one hp2)

/-- `∑_t χ(t) e(ξt/p) = χ(ξ) G_χ` for every `ξ` (`thm:gauss`). -/
theorem sum_chiC_ech (hp2 : p ≠ 2) (ξ : ZMod p) : ∑ t, chiC p t * ech ξ t = chiC p ξ * Gchi p := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp_rw [ech_zero_left, mul_one]
    rw [sum_chiC hp2, chiC_zero, zero_mul]
  · have h := gaussSumAt_twist (chiC p) hξ
    rw [chiC_isQuadratic.inv] at h
    unfold gaussSumAt gaussSum at h
    unfold Gchi gaussSum
    rw [← h]
    apply sum_congr rfl
    intro t _
    rfl

omit [Fact p.Prime] in
lemma sqrt_p_mul_self : ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt p : ℝ) : ℂ) = (p : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg p), Complex.ofReal_natCast]

lemma sqrt_p_ne_zero : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
  exact_mod_cast this.ne'

/-- `c_ξ = χ(ξ) G_χ / p`. -/
lemma gaussEig_eq (ξ : ZMod p) : gaussEig ξ = chiC p ξ * Gchi p / (p : ℂ) := by
  unfold gaussEig epsG rp
  rw [← sqrt_p_mul_self]
  push_cast
  field_simp [sqrt_p_ne_zero]

theorem gaussEig_zero : gaussEig (0 : ZMod p) = 0 := by
  rw [gaussEig, chiC_zero, zero_mul, zero_mul]

/-- **`lem:spec:gauss`, eigenvectors**: `C e_ξ = c_ξ e_ξ`. -/
theorem gaussOp_ech (hp2 : p ≠ 2) (ξ a : ZMod p) : gaussOp (ech ξ) a = gaussEig ξ * ech ξ a := by
  unfold gaussOp
  have hre : ∑ b, chiC p (b - a) * ech ξ b = ∑ t, chiC p t * ech ξ (t + a) :=
    (Fintype.sum_equiv (Equiv.addRight a) _ _ (fun t => by simp)).symm
  rw [hre]
  simp_rw [ech_add_right, ← mul_assoc]
  rw [← sum_mul, sum_chiC_ech hp2, gaussEig_eq]
  field_simp [p_ne_zero_C (p := p)]

/-- **`lem:spec:gauss`**: `ε_G² = χ(−1)`. -/
theorem epsG_sq (hp2 : p ≠ 2) : epsG p ^ 2 = chiC p (-1) := by
  unfold epsG
  rw [div_pow, sq, sq, sqrt_p_mul_self, ← sq]
  unfold Gchi
  rw [quadratic_gaussSum_sq hp2]
  field_simp [p_ne_zero_C (p := p)]

lemma chiC_neg_one (hp2 : p ≠ 2) :
    chiC p (-1) = (((ZMod.χ₄ (p : ZMod 4)) : ℤ) : ℂ) := by
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  rw [chiC_apply, quadraticChar_neg_one hF, ZMod.card]

/-- **`lem:spec:gauss`**: `ε_G ∈ {±1}` if `p ≡ 1 (mod 4)` and `ε_G ∈ {±i}` if `p ≡ 3 (mod 4)`. -/
theorem epsG_cases (hp2 : p ≠ 2) :
    (p % 4 = 1 → epsG p = 1 ∨ epsG p = -1) ∧ (p % 4 = 3 → epsG p = I ∨ epsG p = -I) := by
  have hsq := epsG_sq (p := p) hp2
  rw [chiC_neg_one hp2] at hsq
  constructor
  · intro h1
    rw [ZMod.χ₄_nat_one_mod_four h1] at hsq
    have : (epsG p - 1) * (epsG p + 1) = 0 := by
      rw [show (epsG p - 1) * (epsG p + 1) = epsG p ^ 2 - 1 by ring, hsq]
      simp
    rcases mul_eq_zero.mp this with h | h
    · left; exact sub_eq_zero.mp h
    · right; exact eq_neg_of_add_eq_zero_left h
  · intro h3
    rw [ZMod.χ₄_nat_three_mod_four h3] at hsq
    have : (epsG p - I) * (epsG p + I) = 0 := by
      rw [show (epsG p - I) * (epsG p + I) = epsG p ^ 2 - I ^ 2 by ring, hsq, I_sq]
      simp
    rcases mul_eq_zero.mp this with h | h
    · left; exact sub_eq_zero.mp h
    · right; exact eq_neg_of_add_eq_zero_left h

theorem norm_epsG (hp2 : p ≠ 2) : ‖epsG p‖ = 1 := by
  unfold epsG Gchi
  rw [norm_div, norm_gaussSum (chiC_ne_one hp2), Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact div_self (Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)).ne'

/-- **`lem:spec:gauss`**: `|c_ξ| = r` for `ξ ≠ 0`. -/
theorem norm_gaussEig (hp2 : p ≠ 2) {ξ : ZMod p} (hξ : ξ ≠ 0) : ‖gaussEig ξ‖ = rp p := by
  unfold gaussEig
  rw [norm_mul, norm_mul, norm_chiC hξ, norm_epsG hp2, Complex.norm_real,
    Real.norm_of_nonneg (by unfold rp; positivity)]
  ring

lemma norm_gaussEig_le (hp2 : p ≠ 2) (ξ : ZMod p) : ‖gaussEig ξ‖ ≤ rp p := by
  by_cases hξ : ξ = 0
  · rw [hξ, gaussEig_zero, norm_zero]; unfold rp; positivity
  · exact (norm_gaussEig hp2 hξ).le

/-- **`lem:spec:gauss`**: `C1 = 0`. -/
theorem gaussOp_one (hp2 : p ≠ 2) (a : ZMod p) : gaussOp (fun _ => (1 : ℂ)) a = 0 := by
  unfold gaussOp
  simp_rw [mul_one]
  have hre : ∑ b, chiC p (b - a) = ∑ t, chiC p t :=
    Fintype.sum_equiv (Equiv.subRight a) _ _ (fun b => rfl)
  rw [hre, sum_chiC hp2, mul_zero]

/-- **`lem:spec:gauss`**: `C^*1 = 0`. -/
theorem gaussOpAdj_one (hp2 : p ≠ 2) (a : ZMod p) : gaussOpAdj (fun _ => (1 : ℂ)) a = 0 := by
  unfold gaussOpAdj
  simp_rw [mul_one, conj_chiC]
  have hre : ∑ b, chiC p (a - b) = ∑ t, chiC p t :=
    Fintype.sum_equiv ((Equiv.neg _).trans (Equiv.addLeft a)) _ _
      (fun b => by simp [sub_eq_add_neg])
  rw [hre, sum_chiC hp2, mul_zero]

/-- `C^*` is the adjoint of `C`: `⟨f, Ch⟩ = ⟨C^*f, h⟩`. -/
theorem ip_gaussOp (f h : ZMod p → ℂ) : ip f (gaussOp h) = ip (gaussOpAdj f) h := by
  unfold ip gaussOp gaussOpAdj
  congr 1
  have hc : ∀ b, conj ((p : ℂ)⁻¹ * ∑ a, conj (chiC p (b - a)) * f a) =
      (p : ℂ)⁻¹ * ∑ a, chiC p (b - a) * conj (f a) := by
    intro b
    rw [map_mul, map_inv₀, Complex.conj_natCast, map_sum]
    congr 1
    apply sum_congr rfl
    intro a _
    rw [map_mul, Complex.conj_conj]
  simp_rw [hc]
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  ring

/-- `\overline{G_χ} = χ(−1) G_χ`. -/
lemma conj_Gchi (hp2 : p ≠ 2) : conj (Gchi p) = chiC p (-1) * Gchi p := by
  rw [← sum_chiC_ech hp2]
  unfold Gchi gaussSum
  rw [map_sum]
  apply sum_congr rfl
  intro t _
  rw [map_mul, conj_chiC, ← conj_ech, ech]
  rw [one_mul]

/-- **`lem:spec:gauss`**: `c_{−ξ} = χ(−1) c_ξ`. -/
theorem gaussEig_neg (ξ : ZMod p) : gaussEig (-ξ) = chiC p (-1) * gaussEig ξ := by
  unfold gaussEig
  rw [show -ξ = -1 * ξ by ring, map_mul]
  ring

/-- **`lem:spec:gauss`**: `\overline{c_ξ} = c_{−ξ}`. -/
theorem conj_gaussEig (hp2 : p ≠ 2) (ξ : ZMod p) : conj (gaussEig ξ) = gaussEig (-ξ) := by
  rw [gaussEig_eq, gaussEig_eq, map_div₀, map_mul, conj_chiC, conj_Gchi hp2, Complex.conj_natCast,
    show -ξ = -1 * ξ by ring, map_mul]
  ring

/-- **`lem:spec:gauss`**: `C_ς = χ(ς) C`. -/
theorem gaussOpS_eq (ς : ZMod p) (h : ZMod p → ℂ) (a : ZMod p) :
    gaussOpS ς h a = chiC p ς * gaussOp h a := by
  unfold gaussOpS gaussOp
  simp_rw [map_mul]
  simp only [mul_sum]
  apply sum_congr rfl
  intro b _
  ring

/-- The coefficients of `Ch`: `\widehat{Ch}(ξ) = c_ξ ĥ(ξ)`. -/
theorem fcoef_gaussOp (hp2 : p ≠ 2) (h : ZMod p → ℂ) (ξ : ZMod p) :
    fcoef (gaussOp h) ξ = gaussEig ξ * fcoef h ξ := by
  have hadj : ∀ a, gaussOpAdj (ech ξ) a = conj (gaussEig ξ) * ech ξ a := by
    intro a
    unfold gaussOpAdj
    simp_rw [conj_chiC]
    have hre : ∑ b, chiC p (a - b) * ech ξ b = ∑ t, chiC p t * ech ξ (a - t) :=
      Fintype.sum_equiv ((Equiv.neg _).trans (Equiv.addLeft a)) _ _
        (fun b => by simp [sub_eq_add_neg])
    rw [hre]
    have h2 : ∀ t, chiC p t * ech ξ (a - t) = ech ξ a * (chiC p t * ech (-ξ) t) := by
      intro t
      rw [sub_eq_add_neg, ech_add_right]
      unfold ech
      rw [show ξ * -t = -ξ * t by ring]
      ring
    simp_rw [h2]
    rw [← mul_sum, sum_chiC_ech hp2, conj_gaussEig hp2, gaussEig_eq]
    rw [show -ξ = -1 * ξ by ring, map_mul]
    field_simp [p_ne_zero_C (p := p)]
  unfold fcoef
  rw [ip_gaussOp]
  unfold ip
  simp_rw [hadj, map_mul, Complex.conj_conj]
  simp only [mul_sum]
  apply sum_congr rfl
  intro a _
  ring

lemma l2sq_eq_re_ip (h : ZMod p → ℂ) : (l2sq h : ℂ) = ip h h := by
  rw [ip_self, l2sq]

lemma l2sq_eq_sum_fcoef (h : ZMod p → ℂ) : l2sq h = ∑ ξ, ‖fcoef h ξ‖ ^ 2 := by
  have h1 := ip_eq_sum_fcoef h h
  rw [← l2sq_eq_re_ip] at h1
  have h2 : ∑ ξ, conj (fcoef h ξ) * fcoef h ξ = ((∑ ξ, ‖fcoef h ξ‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    apply sum_congr rfl
    intro ξ _
    rw [mul_comm, Complex.mul_conj', ← Complex.ofReal_pow]
  rw [h2] at h1
  exact_mod_cast h1

/-- **`lem:spec:gauss`, `‖C‖ ≤ r`**: `‖Ch‖² ≤ r² ‖h‖²` for every `h`. -/
theorem l2sq_gaussOp_le (hp2 : p ≠ 2) (h : ZMod p → ℂ) :
    l2sq (gaussOp h) ≤ rp p ^ 2 * l2sq h := by
  rw [l2sq_eq_sum_fcoef, l2sq_eq_sum_fcoef, mul_sum]
  apply sum_le_sum
  intro ξ _
  rw [fcoef_gaussOp hp2, norm_mul, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_gaussEig_le hp2 ξ) 2

lemma l2sq_ech (ξ : ZMod p) : l2sq (ech ξ) = 1 := by
  unfold l2sq
  simp_rw [norm_ech, one_pow, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- **`lem:spec:gauss`, `‖C‖ = r`**: the bound is attained at `e_1`, a unit vector. -/
theorem l2sq_gaussOp_ech_one (hp2 : p ≠ 2) :
    l2sq (gaussOp (ech (1 : ZMod p))) = rp p ^ 2 * l2sq (ech (1 : ZMod p)) := by
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  unfold l2sq
  simp_rw [gaussOp_ech hp2, norm_mul, norm_gaussEig hp2 h1, mul_pow, ← mul_sum]
  ring

end Sarkozy.SpectralC
