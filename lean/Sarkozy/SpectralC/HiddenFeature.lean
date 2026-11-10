module

public import Sarkozy.SpectralC.StarGrams
public import Sarkozy.SpectralC.PaleyOne

@[expose] public section

/-!
# Unobserved features: the core bound (`lem:hidden-feature`)

`paper/sections/14_spectral.tex`, `lem:hidden-feature`. Its proof reduces `Π_O` to the conditional
expectation `Π_j` given the coordinates other than `j` (`Π_O = Π_O Π_j`, `‖Π_O‖ ≤ 1`), and bounds
`Π_j V_j`, the map with the kernel of the conditional law `ν_j(· | x)` of `x_j`. This file proves
that bound for an abstract covariant probability kernel (`markov_kernel_bound`): if `Y(x, ·)` is
a probability vector with `Y(x, t) ≤ D/p`, covariant under `Aff_p`, then for `p ≡ 3 (mod 4)`
`‖Yh‖²_ν ≤ q(D − 1)/(1 − q) ‖h‖²` on `L²_0`; its Gram is scalar and the trace is
`E_ν(p ∑_t Y² − 1) ≤ D − 1` (`eq:star-traces`).

The star part (`pivot_kernel_bound`): `Π_j W_S` has the kernel `φ_j ψ_{S∖j}` with
`φ_j(z, x) = ∑_t ν_j(t | x) χ(z − t)` and `|ψ_{S∖j}| ≤ 1`; by the two-root identity
`E_z φ_j² = ∑_t ν_j(t)² − q ≤ q(D − 1)` (`sum_phi_sq`), so `‖Π_j(W_S/r)h‖² ≤ q(D − 1)/(1 − q)‖h‖²`.

The reduction from `Π_O` to `Π_j` and the identification of `Π_j V_j`, `Π_j W_S` with these
kernels are in `Sarkozy.SpectralC.CondExp` (`hidden_feature_vert`, `hidden_feature_star`).

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {𝒴 : Type*} [Fintype 𝒴]

/-- `‖Yf‖²_ν = re⟨f, Y^*Y f⟩`. -/
lemma norm_kerMap_sq (ν : 𝒴 → ℝ) (Y : 𝒴 → ZMod p → ℝ) (f : ZMod p → ℂ) :
    ((∑ y, ν y * ‖kerMap Y f y‖ ^ 2 : ℝ) : ℂ) = ip f (gramOp ν Y Y f) := by
  rw [← ip_kerMap]
  push_cast
  exact sum_congr rfl fun y _ => by rw [Complex.conj_mul']

/-- **`lem:hidden-feature`, the core bound** (`p ≡ 3 (mod 4)`): a covariant probability kernel
`Y` with density at most `D` satisfies `‖Yh‖²_ν ≤ q(D − 1)/(1 − q) ‖h‖²` on `L²_0`. -/
theorem markov_kernel_bound (hp2 : p ≠ 2) (hp3 : p % 4 = 3) {ν : 𝒴 → ℝ} (G : AffAction p 𝒴 ν)
    (hν0 : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1) (Y : 𝒴 → ZMod p → ℝ)
    (hY : ∀ (s c : ZMod p), s ≠ 0 → IsSquare s → ∀ (h : ZMod p → ℂ) (y : 𝒴),
      kerMap Y (fun a => h (s * a + c)) y = kerMap Y h (G.act s c y))
    (hY0 : ∀ y t, 0 ≤ Y y t) (hY1 : ∀ y, ν y ≠ 0 → ∑ t, Y y t = 1) {D : ℝ}
    (hD : ∀ y t, ν y ≠ 0 → Y y t ≤ D / p) (h : ZMod p → ℂ) (hh : meanC h = 0) :
    ∑ y, ν y * ‖kerMap Y h y‖ ^ 2 ≤ (p : ℝ)⁻¹ * (D - 1) / (1 - (p : ℝ)⁻¹) * l2sq h := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1' : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  obtain ⟨α, hα, htr⟩ := intertwiner_gram_self hp2 hp3 G Y hY
  rw [trace_gramOp] at htr
  -- the norm is `α ‖h‖²`
  have hnorm : ∑ y, ν y * ‖kerMap Y h y‖ ^ 2 = α * l2sq h := by
    have h1 := norm_kerMap_sq ν Y h
    have h2 : gramOp ν Y Y h = fun a => (α : ℂ) * h a := funext (hα h hh)
    rw [h2] at h1
    have h3 : ip h (fun a => (α : ℂ) * h a) = (α : ℂ) * ip h h := by
      show (p : ℂ)⁻¹ * ∑ a, conj (h a) * ((α : ℂ) * h a) =
        (α : ℂ) * ((p : ℂ)⁻¹ * ∑ a, conj (h a) * h a)
      have e : ∑ a, conj (h a) * ((α : ℂ) * h a) = (α : ℂ) * ∑ a, conj (h a) * h a := by
        rw [mul_sum]; exact sum_congr rfl fun a _ => by ring
      rw [e]; ring
    rw [h3, ← l2sq_eq_re_ip] at h1
    exact_mod_cast h1
  -- the trace is at most `D − 1`
  have htrR : ((p : ℝ) - 1) * α = ∑ y, ν y * ((p : ℝ) * ∑ t, Y y t * Y y t - (∑ t, Y y t) ^ 2) := by
    have : ((((p : ℝ) - 1) * α : ℝ) : ℂ) =
        ((∑ y, ν y * ((p : ℝ) * ∑ t, Y y t * Y y t - (∑ t, Y y t) ^ 2) : ℝ) : ℂ) := by
      push_cast
      rw [← htr]
      exact sum_congr rfl fun y _ => by ring
    exact_mod_cast this
  have hterm : ∀ y, ν y * ((p : ℝ) * ∑ t, Y y t * Y y t - (∑ t, Y y t) ^ 2) ≤ ν y * (D - 1) := by
    intro y
    by_cases hy : ν y = 0
    · rw [hy, zero_mul, zero_mul]
    · apply mul_le_mul_of_nonneg_left _ (hν0 y)
      rw [hY1 y hy]
      have h1 : ∑ t, Y y t * Y y t ≤ ∑ t, D / p * Y y t :=
        sum_le_sum fun t _ => mul_le_mul_of_nonneg_right (hD y t hy) (hY0 y t)
      rw [← mul_sum, hY1 y hy, mul_one] at h1
      have h2 : (p : ℝ) * ∑ t, Y y t * Y y t ≤ D := by
        calc (p : ℝ) * ∑ t, Y y t * Y y t ≤ (p : ℝ) * (D / p) :=
              mul_le_mul_of_nonneg_left h1 hp0.le
          _ = D := by field_simp
      linarith
  have htrle : ((p : ℝ) - 1) * α ≤ D - 1 := by
    rw [htrR]
    calc ∑ y, ν y * ((p : ℝ) * ∑ t, Y y t * Y y t - (∑ t, Y y t) ^ 2)
        ≤ ∑ y, ν y * (D - 1) := sum_le_sum fun y _ => hterm y
      _ = D - 1 := by rw [← sum_mul, hν1, one_mul]
  have hαle : α ≤ (p : ℝ)⁻¹ * (D - 1) / (1 - (p : ℝ)⁻¹) := by
    have e : (p : ℝ)⁻¹ * (D - 1) / (1 - (p : ℝ)⁻¹) = (D - 1) / ((p : ℝ) - 1) := by
      have : (1 : ℝ) - (p : ℝ)⁻¹ ≠ 0 := by
        have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
        linarith
      field_simp
    rw [e, le_div_iff₀ hp1']
    linarith
  rw [hnorm]
  exact mul_le_mul_of_nonneg_right hαle (by unfold l2sq; positivity)

/-- `∑_z χ(z − t)χ(z − t') = p𝟙[t = t'] − 1` (the two-root identity `eq:two-root`). -/
lemma sum_chiRe_mul (hp2 : p ≠ 2) (t t' : ZMod p) :
    ∑ z, chiRe (z - t) * chiRe (z - t') = (if t = t' then (p : ℝ) else 0) - 1 := by
  by_cases htt : t = t'
  · subst htt
    rw [ite_eq_left rfl]
    have h1 : ∀ z : ZMod p, chiRe (z - t) * chiRe (z - t) = 1 - if z = t then 1 else 0 := by
      intro z
      by_cases hz : z = t
      · rw [hz, sub_self, ite_eq_left rfl]; unfold chiRe; simp
      · rw [ite_eq_right hz, sub_zero]
        have hne : z - t ≠ 0 := sub_ne_zero.mpr hz
        unfold chiRe
        rw [← sq]
        exact_mod_cast quadraticChar_sq_one hne
    rw [sum_congr rfl fun z _ => h1 z, sum_sub_distrib, sum_const, card_univ, ZMod.card,
      nsmul_eq_mul, mul_one, sum_ite_eq', ite_eq_left (mem_univ t)]
  · rw [ite_eq_right htt, zero_sub]
    have h := sum_chiC_two_root hp2 htt
    have h2 : ∀ z : ZMod p, chiC p (t - z) * chiC p (t' - z) =
        ((chiRe (z - t) * chiRe (z - t') : ℝ) : ℂ) := by
      intro z
      have e1 : t - z = -1 * (z - t) := by ring
      have e2 : t' - z = -1 * (z - t') := by ring
      have hm : chiC p (-1) * chiC p (-1) = 1 := by rw [← map_mul]; norm_num
      have hc : ∀ u : ZMod p, ((chiRe u : ℝ) : ℂ) = chiC p u := by
        intro u; unfold chiRe; rw [chiC_apply, Complex.ofReal_intCast]
      rw [e1, e2, map_mul, map_mul, Complex.ofReal_mul, hc, hc]
      linear_combination (chiC p (z - t) * chiC p (z - t')) * hm
    rw [sum_congr rfl fun z _ => h2 z] at h
    exact_mod_cast h

/-- `∑_z (∑_t ν_t χ(z − t))² = p ∑_t ν_t² − (∑_t ν_t)²`. -/
lemma sum_phi_sq (hp2 : p ≠ 2) (νj : ZMod p → ℝ) :
    ∑ z, (∑ t, νj t * chiRe (z - t)) ^ 2 = (p : ℝ) * ∑ t, νj t ^ 2 - (∑ t, νj t) ^ 2 := by
  have h1 : ∀ z, (∑ t, νj t * chiRe (z - t)) ^ 2 =
      ∑ t, ∑ t', νj t * νj t' * (chiRe (z - t) * chiRe (z - t')) := by
    intro z
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun t _ => sum_congr rfl fun t' _ => by ring
  rw [sum_congr rfl fun z _ => h1 z, sum_comm]
  have h2 : ∀ t, ∑ z, ∑ t', νj t * νj t' * (chiRe (z - t) * chiRe (z - t')) =
      (p : ℝ) * νj t ^ 2 - νj t * ∑ t', νj t' := by
    intro t
    rw [sum_comm]
    simp_rw [← mul_sum, sum_chiRe_mul hp2]
    have h3 : ∑ t', νj t * νj t' * ((if t = t' then (p : ℝ) else 0) - 1) =
        νj t * νj t * p - νj t * ∑ t', νj t' := by
      simp only [mul_sub, mul_ite, mul_zero, mul_one, sum_sub_distrib, sum_ite_eq, mem_univ,
        ite_true, ← mul_sum]
    rw [h3]
    ring
  rw [sum_congr rfl fun t _ => h2 t, sum_sub_distrib, ← mul_sum, ← sum_mul, sq]

/-- The kernel of `Π_j W_S`: `p⁻¹ φ(x, z) ψ'(x, z)`, `φ(x, z) = ∑_t ν_j(t | x) χ(z − t)`. -/
noncomputable def pivotKer (νj : 𝒴 → ZMod p → ℝ) (ψ' : 𝒴 → ZMod p → ℝ) (y : 𝒴) (z : ZMod p) : ℝ :=
  (p : ℝ)⁻¹ * (∑ t, νj y t * chiRe (z - t)) * ψ' y z

/-- **`lem:hidden-feature`, the star core** (`p ≡ 3 (mod 4)`): for a covariant kernel
`p⁻¹ φ ψ'` with `φ(x, z) = ∑_t ν_j(t | x) χ(z − t)`, `ν_j(· | x)` a probability vector with
density at most `D`, and `|ψ'| ≤ 1`: `‖Yh‖²_ν ≤ q · q(D − 1)/(1 − q) ‖h‖²` on `L²_0`, that is
`‖Y/r‖² ≤ q(D − 1)/(1 − q)`. -/
theorem pivot_kernel_bound (hp2 : p ≠ 2) (hp3 : p % 4 = 3) {ν : 𝒴 → ℝ} (G : AffAction p 𝒴 ν)
    (hν0 : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1) (νj : 𝒴 → ZMod p → ℝ)
    (hνj0 : ∀ y t, 0 ≤ νj y t) (hνj1 : ∀ y, ν y ≠ 0 → ∑ t, νj y t = 1) {D : ℝ}
    (hD : ∀ y t, ν y ≠ 0 → νj y t ≤ D / p) (ψ' : 𝒴 → ZMod p → ℝ) (hψ : ∀ y z, |ψ' y z| ≤ 1)
    (hY : ∀ (s c : ZMod p), s ≠ 0 → IsSquare s → ∀ (h : ZMod p → ℂ) (y : 𝒴),
      kerMap (pivotKer νj ψ') (fun a => h (s * a + c)) y =
        kerMap (pivotKer νj ψ') h (G.act s c y))
    (h : ZMod p → ℂ) (hh : meanC h = 0) :
    ∑ y, ν y * ‖kerMap (pivotKer νj ψ') h y‖ ^ 2 ≤
      (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ * (D - 1) / (1 - (p : ℝ)⁻¹)) * l2sq h := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1' : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  set Y := pivotKer νj ψ' with hYdef
  obtain ⟨α, hα, htr⟩ := intertwiner_gram_self hp2 hp3 G Y hY
  rw [trace_gramOp] at htr
  have hnorm : ∑ y, ν y * ‖kerMap Y h y‖ ^ 2 = α * l2sq h := by
    have h1 := norm_kerMap_sq ν Y h
    have h2 : gramOp ν Y Y h = fun a => (α : ℂ) * h a := funext (hα h hh)
    rw [h2] at h1
    have h3 : ip h (fun a => (α : ℂ) * h a) = (α : ℂ) * ip h h := by
      show (p : ℂ)⁻¹ * ∑ a, conj (h a) * ((α : ℂ) * h a) =
        (α : ℂ) * ((p : ℂ)⁻¹ * ∑ a, conj (h a) * h a)
      have e : ∑ a, conj (h a) * ((α : ℂ) * h a) = (α : ℂ) * ∑ a, conj (h a) * h a := by
        rw [mul_sum]; exact sum_congr rfl fun a _ => by ring
      rw [e]; ring
    rw [h3, ← l2sq_eq_re_ip] at h1
    exact_mod_cast h1
  have htrR : ((p : ℝ) - 1) * α =
      ∑ y, ν y * ((p : ℝ) * ∑ z, Y y z * Y y z - (∑ z, Y y z) ^ 2) := by
    have : ((((p : ℝ) - 1) * α : ℝ) : ℂ) =
        ((∑ y, ν y * ((p : ℝ) * ∑ z, Y y z * Y y z - (∑ z, Y y z) ^ 2) : ℝ) : ℂ) := by
      push_cast
      rw [← htr]
      exact sum_congr rfl fun y _ => by ring
    exact_mod_cast this
  have hterm : ∀ y, ν y * ((p : ℝ) * ∑ z, Y y z * Y y z - (∑ z, Y y z) ^ 2) ≤
      ν y * ((p : ℝ)⁻¹ * (D - 1)) := by
    intro y
    by_cases hy : ν y = 0
    · rw [hy, zero_mul, zero_mul]
    · apply mul_le_mul_of_nonneg_left _ (hν0 y)
      have hsq : ∀ z, Y y z * Y y z ≤ (p : ℝ)⁻¹ ^ 2 * (∑ t, νj y t * chiRe (z - t)) ^ 2 := by
        intro z
        simp only [hYdef, pivotKer]
        have hψ2 : ψ' y z ^ 2 ≤ 1 := by
          have := hψ y z
          rw [← sq_abs]
          nlinarith [abs_nonneg (ψ' y z)]
        have hφ : 0 ≤ (∑ t, νj y t * chiRe (z - t)) ^ 2 := sq_nonneg _
        have e : (p : ℝ)⁻¹ * (∑ t, νj y t * chiRe (z - t)) * ψ' y z *
            ((p : ℝ)⁻¹ * (∑ t, νj y t * chiRe (z - t)) * ψ' y z) =
            (p : ℝ)⁻¹ ^ 2 * (∑ t, νj y t * chiRe (z - t)) ^ 2 * ψ' y z ^ 2 := by ring
        rw [e]
        have hq : 0 ≤ (p : ℝ)⁻¹ ^ 2 * (∑ t, νj y t * chiRe (z - t)) ^ 2 := by positivity
        nlinarith
      have hν2 : ∑ t, νj y t ^ 2 ≤ D / p := by
        have : ∑ t, νj y t ^ 2 ≤ ∑ t, D / p * νj y t :=
          sum_le_sum fun t _ => by rw [sq]; exact mul_le_mul_of_nonneg_right (hD y t hy) (hνj0 y t)
        rwa [← mul_sum, hνj1 y hy, mul_one] at this
      have hS : (p : ℝ) * ∑ z, Y y z * Y y z ≤ (p : ℝ)⁻¹ * (D - 1) := by
        calc (p : ℝ) * ∑ z, Y y z * Y y z
            ≤ (p : ℝ) * ∑ z, (p : ℝ)⁻¹ ^ 2 * (∑ t, νj y t * chiRe (z - t)) ^ 2 :=
              mul_le_mul_of_nonneg_left (sum_le_sum fun z _ => hsq z) hp0.le
          _ = (p : ℝ)⁻¹ * ((p : ℝ) * ∑ t, νj y t ^ 2 - (∑ t, νj y t) ^ 2) := by
              rw [← mul_sum, sum_phi_sq hp2]
              field_simp
          _ ≤ (p : ℝ)⁻¹ * (D - 1) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [hνj1 y hy]
              have : (p : ℝ) * ∑ t, νj y t ^ 2 ≤ D := by
                calc (p : ℝ) * ∑ t, νj y t ^ 2 ≤ (p : ℝ) * (D / p) :=
                      mul_le_mul_of_nonneg_left hν2 hp0.le
                  _ = D := by field_simp
              linarith
      nlinarith [sq_nonneg (∑ z, Y y z)]
  have htrle : ((p : ℝ) - 1) * α ≤ (p : ℝ)⁻¹ * (D - 1) := by
    rw [htrR]
    calc ∑ y, ν y * ((p : ℝ) * ∑ z, Y y z * Y y z - (∑ z, Y y z) ^ 2)
        ≤ ∑ y, ν y * ((p : ℝ)⁻¹ * (D - 1)) := sum_le_sum fun y _ => hterm y
      _ = (p : ℝ)⁻¹ * (D - 1) := by rw [← sum_mul, hν1, one_mul]
  have hαle : α ≤ (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ * (D - 1) / (1 - (p : ℝ)⁻¹)) := by
    have e : (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ * (D - 1) / (1 - (p : ℝ)⁻¹)) =
        (p : ℝ)⁻¹ * (D - 1) / ((p : ℝ) - 1) := by
      have : (1 : ℝ) - (p : ℝ)⁻¹ ≠ 0 := by
        have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
        linarith
      field_simp
    rw [e, le_div_iff₀ hp1']
    linarith
  rw [hnorm]
  exact mul_le_mul_of_nonneg_right hαle (by unfold l2sq; positivity)

end Sarkozy.SpectralC
