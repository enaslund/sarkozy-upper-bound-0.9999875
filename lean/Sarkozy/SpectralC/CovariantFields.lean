module

public import Sarkozy.SpectralC.AffinePairs

@[expose] public section

/-!
# Covariant fields (`lem:spec:affpair`(c))

`paper/sections/14_spectral.tex`, `lem:spec:affpair`(c). Let `ν` be weights on a finite set `𝒴`
(a probability in the paper) on which `Aff_p` acts preserving `ν` (`AffAction`: each map
`act s c`, `s` a nonzero square, is a `ν`-preserving bijection; the group laws are not needed),
and let `𝒱_1, …, 𝒱_s : 𝒴 × 𝔽_p → ℂ` be covariant: `𝒱_k(γy, γa) = 𝒱_k(y, a)`. With
`Γ_kl = E_ν E_a \overline{𝒱_k} 𝒱_l`, `M_kl = E_ν \overline{E_a 𝒱_k} E_a 𝒱_l`,
`𝒫_kl = E_ν ⟨𝒱_k(y,·), C 𝒱_l(y,·)⟩` and `𝒱_w = ∑_k w_k 𝒱_k`, for `ξ ≠ 0`:
`E_ν |E_a[𝒱_w(y, a) e_ξ(a)]|² = w^*(Γ − M + χ(ξ) G_χ 𝒫) w / (p − 1)` (`covariant_fields`).

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

/-- An action of `Aff_p` on `𝒴` preserving the weights `ν`: `act s c` is the action of
`z ↦ sz + c`; for every nonzero square `s` it is a bijection preserving `ν`. -/
structure AffAction (p : ℕ) [Fact p.Prime] (𝒴 : Type*) (ν : 𝒴 → ℝ) where
  act : ZMod p → ZMod p → 𝒴 → 𝒴
  bij : ∀ s c : ZMod p, s ≠ 0 → IsSquare s → Function.Bijective (act s c)
  pres : ∀ (s c : ZMod p) (y : 𝒴), s ≠ 0 → IsSquare s → ν (act s c y) = ν y

/-- The quadratic form `w^* X w = ∑_{k,l} \overline{w_k} X_kl w_l`. -/
noncomputable def qform {ι : Type*} [Fintype ι] (X : ι → ι → ℂ) (w : ι → ℂ) : ℂ :=
  ∑ k, ∑ l, conj (w k) * X k l * w l

variable {𝒴 ι : Type*} [Fintype 𝒴] [Fintype ι]

/-- The field `𝒱_w = ∑_k w_k 𝒱_k`. -/
noncomputable def fieldW (V : ι → 𝒴 → ZMod p → ℂ) (w : ι → ℂ) (y : 𝒴) (a : ZMod p) : ℂ :=
  ∑ k, w k * V k y a

/-- A bilinear functional of two fields with kernel `c`:
`E_ν ∑_{a,b} c(a,b) \overline{𝒱_k(y,a)} 𝒱_l(y,b)`. -/
noncomputable def bilin (ν : 𝒴 → ℝ) (V : ι → 𝒴 → ZMod p → ℂ) (c : ZMod p → ZMod p → ℂ)
    (k l : ι) : ℂ :=
  ∑ y, (ν y : ℂ) * ∑ a, ∑ b, c a b * (conj (V k y a) * V l y b)

omit [Fact p.Prime] [Fintype 𝒴] in
lemma conj_mul_fieldW (V : ι → 𝒴 → ZMod p → ℂ) (w : ι → ℂ) (y : 𝒴) (a b : ZMod p) :
    conj (fieldW V w y a) * fieldW V w y b =
      ∑ k, ∑ l, conj (w k) * (conj (V k y a) * V l y b) * w l := by
  unfold fieldW
  rw [map_sum, sum_mul]
  apply sum_congr rfl
  intro k _
  rw [mul_sum]
  apply sum_congr rfl
  intro l _
  rw [map_mul]
  ring

lemma sum5_comm (F : ι → ι → 𝒴 → ZMod p → ZMod p → ℂ) :
    ∑ k, ∑ l, ∑ y, ∑ a, ∑ b, F k l y a b = ∑ y, ∑ a, ∑ b, ∑ k, ∑ l, F k l y a b := by
  calc ∑ k, ∑ l, ∑ y, ∑ a, ∑ b, F k l y a b
      = ∑ k, ∑ y, ∑ l, ∑ a, ∑ b, F k l y a b := sum_congr rfl fun k _ => sum_comm
    _ = ∑ y, ∑ k, ∑ l, ∑ a, ∑ b, F k l y a b := sum_comm
    _ = ∑ y, ∑ k, ∑ a, ∑ l, ∑ b, F k l y a b :=
        sum_congr rfl fun y _ => sum_congr rfl fun k _ => sum_comm
    _ = ∑ y, ∑ a, ∑ k, ∑ l, ∑ b, F k l y a b := sum_congr rfl fun y _ => sum_comm
    _ = ∑ y, ∑ a, ∑ k, ∑ b, ∑ l, F k l y a b :=
        sum_congr rfl fun y _ => sum_congr rfl fun a _ => sum_congr rfl fun k _ => sum_comm
    _ = ∑ y, ∑ a, ∑ b, ∑ k, ∑ l, F k l y a b :=
        sum_congr rfl fun y _ => sum_congr rfl fun a _ => sum_comm

/-- `w^* B w` for a bilinear functional is the functional of `𝒱_w` with itself. -/
lemma qform_bilin (ν : 𝒴 → ℝ) (V : ι → 𝒴 → ZMod p → ℂ) (c : ZMod p → ZMod p → ℂ)
    (w : ι → ℂ) :
    qform (bilin ν V c) w =
      ∑ y, (ν y : ℂ) * ∑ a, ∑ b, c a b * (conj (fieldW V w y a) * fieldW V w y b) := by
  unfold qform bilin
  simp_rw [conj_mul_fieldW, mul_sum, sum_mul]
  rw [sum5_comm]
  apply sum_congr rfl; intro y _
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro b _
  apply sum_congr rfl; intro k _
  apply sum_congr rfl; intro l _
  ring

/-- `Γ_kl = E_ν E_a \overline{𝒱_k} 𝒱_l`. -/
noncomputable def gramΓ (ν : 𝒴 → ℝ) (V : ι → 𝒴 → ZMod p → ℂ) (k l : ι) : ℂ :=
  ∑ y, (ν y : ℂ) * ((p : ℂ)⁻¹ * ∑ a, conj (V k y a) * V l y a)

/-- `M_kl = E_ν \overline{E_a 𝒱_k} E_a 𝒱_l`. -/
noncomputable def gramM (ν : 𝒴 → ℝ) (V : ι → 𝒴 → ZMod p → ℂ) (k l : ι) : ℂ :=
  ∑ y, (ν y : ℂ) * (conj ((p : ℂ)⁻¹ * ∑ a, V k y a) * ((p : ℂ)⁻¹ * ∑ a, V l y a))

/-- `𝒫_kl = E_ν ⟨𝒱_k(y, ·), C 𝒱_l(y, ·)⟩`. -/
noncomputable def gramP (ν : 𝒴 → ℝ) (V : ι → 𝒴 → ZMod p → ℂ) (k l : ι) : ℂ :=
  ∑ y, (ν y : ℂ) * ip (V k y) (gaussOp (V l y))

omit [Fintype ι] in
lemma gramΓ_eq (ν : 𝒴 → ℝ) (V : ι → 𝒴 → ZMod p → ℂ) :
    gramΓ ν V = bilin ν V (fun a b => if a = b then (p : ℂ)⁻¹ else 0) := by
  funext k l
  unfold gramΓ bilin
  apply sum_congr rfl; intro y _
  congr 1
  rw [mul_sum]
  apply sum_congr rfl; intro a _
  dsimp only
  rw [sum_eq_single a]
  · rw [ite_eq_left rfl]
  · intro b _ hb; rw [ite_eq_right (Ne.symm hb), zero_mul]
  · intro h0; exact absurd (mem_univ a) h0

omit [Fintype ι] in
lemma gramM_eq (ν : 𝒴 → ℝ) (V : ι → 𝒴 → ZMod p → ℂ) :
    gramM ν V = bilin ν V (fun _ _ => (p : ℂ)⁻¹ * (p : ℂ)⁻¹) := by
  funext k l
  unfold gramM bilin
  apply sum_congr rfl; intro y _
  congr 1
  rw [map_mul, map_inv₀, Complex.conj_natCast, map_sum, mul_sum, sum_mul]
  apply sum_congr rfl; intro a _
  rw [mul_sum, mul_sum]
  apply sum_congr rfl; intro b _
  ring

omit [Fintype ι] in
lemma gramP_eq (ν : 𝒴 → ℝ) (V : ι → 𝒴 → ZMod p → ℂ) :
    gramP ν V = bilin ν V (fun a b => (p : ℂ)⁻¹ * (p : ℂ)⁻¹ * chiC p (b - a)) := by
  funext k l
  unfold gramP bilin ip gaussOp
  apply sum_congr rfl; intro y _
  congr 1
  rw [mul_sum]
  apply sum_congr rfl; intro a _
  dsimp only
  simp only [mul_sum]
  apply sum_congr rfl; intro b _
  ring

/-! ## The moments of an orbit-constant kernel -/

section Moments

variable (A B Cc : ℂ) (κ : ZMod p → ZMod p → ℂ)

lemma kernel_moment_diag (hκ : ∀ a b, κ a b = A * (if a = b then 1 else 0) + B + Cc * chiC p (b - a)) :
    ∑ a, κ a a = (p : ℂ) * (A + B) := by
  simp_rw [hκ, sub_self, chiC_zero]
  simp only [ite_true, mul_one, mul_zero, add_zero, sum_const, card_univ, ZMod.card, nsmul_eq_mul]

lemma kernel_moment_total (hp2 : p ≠ 2)
    (hκ : ∀ a b, κ a b = A * (if a = b then 1 else 0) + B + Cc * chiC p (b - a)) :
    ∑ a, ∑ b, κ a b = A * p + B * (p : ℂ) ^ 2 := by
  simp_rw [hκ, sum_add_distrib, ← mul_sum, sum_chiC_sub hp2]
  simp only [sum_ite_eq, mem_univ, ite_true, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  ring

lemma kernel_moment_chi (hp2 : p ≠ 2)
    (hκ : ∀ a b, κ a b = A * (if a = b then 1 else 0) + B + Cc * chiC p (b - a)) :
    ∑ a, ∑ b, chiC p (b - a) * κ a b = Cc * ((p : ℂ) * ((p : ℂ) - 1)) := by
  simp_rw [hκ, mul_add, sum_add_distrib]
  have hz : ∀ a, ∑ b, chiC p (b - a) * (A * (if a = b then (1 : ℂ) else 0)) = 0 := by
    intro a
    rw [sum_eq_single a]
    · rw [sub_self, chiC_zero, zero_mul]
    · intro b _ hb; rw [ite_eq_right (Ne.symm hb), mul_zero, mul_zero]
    · intro h0; exact absurd (mem_univ a) h0
  have h2 : ∀ a, ∑ b, chiC p (b - a) * B = 0 := by
    intro a; rw [← sum_mul, sum_chiC_sub hp2, zero_mul]
  have h3 : ∀ a, ∑ b, chiC p (b - a) * (Cc * chiC p (b - a)) = Cc * ((p : ℂ) - 1) := by
    intro a
    rw [← sum_chiC_sub_sq a, mul_sum]
    apply sum_congr rfl; intro b _; ring
  simp_rw [hz, h2, h3]
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  ring

lemma kernel_moment_ech (hp2 : p ≠ 2) {ξ : ZMod p} (hξ : ξ ≠ 0)
    (hκ : ∀ a b, κ a b = A * (if a = b then 1 else 0) + B + Cc * chiC p (b - a)) :
    ∑ a, ∑ b, conj (ech ξ a) * ech ξ b * κ a b = A * p + Cc * p * (chiC p ξ * Gchi p) := by
  simp_rw [hκ, mul_add, sum_add_distrib]
  have hd : ∀ a, ∑ b, conj (ech ξ a) * ech ξ b * (A * (if a = b then (1 : ℂ) else 0)) = A := by
    intro a
    rw [sum_eq_single a]
    · rw [ite_eq_left rfl, mul_one, mul_comm (conj _), Complex.mul_conj', norm_ech]
      simp
    · intro b _ hb; rw [ite_eq_right (Ne.symm hb), mul_zero, mul_zero]
    · intro h0; exact absurd (mem_univ a) h0
  have hB : ∀ a, ∑ b, conj (ech ξ a) * ech ξ b * B = 0 := by
    intro a
    rw [← sum_mul, ← mul_sum, sum_ech, ite_eq_right hξ, mul_zero, zero_mul]
  have hC : ∀ a, ∑ b, conj (ech ξ a) * ech ξ b * (Cc * chiC p (b - a)) =
      Cc * (chiC p ξ * Gchi p) := by
    intro a
    have hre : ∑ b, conj (ech ξ a) * ech ξ b * (Cc * chiC p (b - a)) =
        ∑ t, conj (ech ξ a) * ech ξ (t + a) * (Cc * chiC p t) :=
      (Fintype.sum_equiv (Equiv.addRight a) _ _ (fun t => by simp)).symm
    rw [hre]
    have h1 : ∀ t, conj (ech ξ a) * ech ξ (t + a) * (Cc * chiC p t) =
        Cc * (chiC p t * ech ξ t) := by
      intro t
      rw [ech_add_right]
      have : conj (ech ξ a) * ech ξ a = 1 := by
        rw [mul_comm, Complex.mul_conj', norm_ech]; simp
      linear_combination (Cc * chiC p t * ech ξ t) * this
    simp_rw [h1]
    rw [← mul_sum, sum_chiC_ech hp2]
  simp_rw [hd, hB, hC]
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  ring

end Moments

/-! ## Part (c) -/

lemma bilinW_eq_kernel (ν : 𝒴 → ℝ) (V : ι → 𝒴 → ZMod p → ℂ) (w : ι → ℂ)
    (c : ZMod p → ZMod p → ℂ) :
    ∑ y, (ν y : ℂ) * ∑ a, ∑ b, c a b * (conj (fieldW V w y a) * fieldW V w y b) =
      ∑ a, ∑ b, c a b * ∑ y, (ν y : ℂ) * (conj (fieldW V w y a) * fieldW V w y b) := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro a _
  rw [sum_comm]
  apply sum_congr rfl; intro b _
  apply sum_congr rfl; intro y _
  ring

/-- **`lem:spec:affpair`(c), covariant fields.** For `ξ ≠ 0` and `w`,
`E_ν |E_a[𝒱_w(y, a) e_ξ(a)]|² = w^*(Γ − M + χ(ξ) G_χ 𝒫) w / (p − 1)`. -/
theorem covariant_fields (hp2 : p ≠ 2) (ν : 𝒴 → ℝ) (G : AffAction p 𝒴 ν)
    (V : ι → 𝒴 → ZMod p → ℂ)
    (hV : ∀ (k : ι) (s c : ZMod p) (y : 𝒴) (a : ZMod p), s ≠ 0 → IsSquare s →
      V k (G.act s c y) (s * a + c) = V k y a)
    {ξ : ZMod p} (hξ : ξ ≠ 0) (w : ι → ℂ) :
    ∑ y, (ν y : ℂ) * ((‖(p : ℂ)⁻¹ * ∑ a, fieldW V w y a * ech ξ a‖ ^ 2 : ℝ) : ℂ) =
      (qform (gramΓ ν V) w - qform (gramM ν V) w +
        chiC p ξ * Gchi p * qform (gramP ν V) w) / ((p : ℂ) - 1) := by
  set κ : ZMod p → ZMod p → ℂ :=
    fun a b => ∑ y, (ν y : ℂ) * (conj (fieldW V w y a) * fieldW V w y b) with hκdef
  -- the kernel is invariant
  have hinv : IsAffInv κ := by
    intro s c a b hs hsq
    simp only [hκdef]
    have hW : ∀ y d, fieldW V w (G.act s c y) (s * d + c) = fieldW V w y d := by
      intro y d
      unfold fieldW
      apply sum_congr rfl
      intro k _
      rw [hV k s c y d hs hsq]
    rw [← (G.bij s c hs hsq).sum_comp]
    apply sum_congr rfl
    intro y _
    rw [G.pres s c y hs hsq, hW, hW]
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare (oddChar (p := p) hp2)
  have horb := affInv_orbit κ hinv hn
  set A := κ 0 0 - (κ 0 1 + κ 0 n) / 2 with hA
  set B := (κ 0 1 + κ 0 n) / 2 with hB
  set Cc := (κ 0 1 - κ 0 n) / 2 with hCc
  have hκχ : ∀ a b, κ a b = A * (if a = b then 1 else 0) + B + Cc * chiC p (b - a) := by
    intro a b
    rw [horb a b, orbit_eq_chi]
  have hpC := p_ne_zero_C (p := p)
  have hk : ∀ a b, ∑ y, (ν y : ℂ) * (conj (fieldW V w y a) * fieldW V w y b) = κ a b :=
    fun a b => rfl
  -- the three quadratic forms
  have hΓ : qform (gramΓ ν V) w = A + B := by
    rw [gramΓ_eq, qform_bilin, bilinW_eq_kernel]
    simp only [hk]
    have : ∀ a, ∑ b, (if a = b then (p : ℂ)⁻¹ else 0) * κ a b = (p : ℂ)⁻¹ * κ a a := by
      intro a
      rw [sum_eq_single a]
      · rw [ite_eq_left rfl]
      · intro b _ hb; rw [ite_eq_right (Ne.symm hb), zero_mul]
      · intro h0; exact absurd (mem_univ a) h0
    simp_rw [this]
    rw [← mul_sum, kernel_moment_diag A B Cc κ hκχ]
    field_simp
  have hM : qform (gramM ν V) w = A / p + B := by
    rw [gramM_eq, qform_bilin, bilinW_eq_kernel]
    simp only [hk]
    simp_rw [← mul_sum]
    rw [kernel_moment_total A B Cc κ hp2 hκχ]
    field_simp
  have hP : qform (gramP ν V) w = Cc * ((p : ℂ) - 1) / p := by
    rw [gramP_eq, qform_bilin, bilinW_eq_kernel]
    simp only [hk]
    simp_rw [mul_assoc, ← mul_sum]
    rw [kernel_moment_chi A B Cc κ hp2 hκχ]
    field_simp
  -- the left side
  have hL : ∑ y, (ν y : ℂ) * ((‖(p : ℂ)⁻¹ * ∑ a, fieldW V w y a * ech ξ a‖ ^ 2 : ℝ) : ℂ) =
      (p : ℂ)⁻¹ * (p : ℂ)⁻¹ * ∑ a, ∑ b, conj (ech ξ a) * ech ξ b * κ a b := by
    have hsq : ∀ y, ((‖(p : ℂ)⁻¹ * ∑ a, fieldW V w y a * ech ξ a‖ ^ 2 : ℝ) : ℂ) =
        ∑ a, ∑ b, (p : ℂ)⁻¹ * (p : ℂ)⁻¹ * (conj (ech ξ a) * ech ξ b) *
          (conj (fieldW V w y a) * fieldW V w y b) := by
      intro y
      rw [Complex.ofReal_pow, ← Complex.mul_conj', mul_comm]
      rw [map_mul, map_inv₀, Complex.conj_natCast, map_sum, mul_mul_mul_comm, sum_mul_sum,
        mul_sum]
      apply sum_congr rfl; intro a _
      rw [mul_sum]
      apply sum_congr rfl; intro b _
      rw [map_mul]
      ring
    simp_rw [hsq]
    rw [bilinW_eq_kernel ν V w (fun a b => (p : ℂ)⁻¹ * (p : ℂ)⁻¹ * (conj (ech ξ a) * ech ξ b))]
    simp only [hk, mul_sum]
    apply sum_congr rfl; intro a _
    apply sum_congr rfl; intro b _
    ring
  rw [hL, kernel_moment_ech A B Cc κ hp2 hξ hκχ, hΓ, hM, hP]
  have hp1 : (p : ℂ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    intro h0
    have h1 : ((p : ℂ) - 1).re = 0 := by rw [h0]; simp
    simp at h1
    linarith
  field_simp
  ring

end Sarkozy.SpectralC
