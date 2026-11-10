module

public import Sarkozy.SpectralC.CondExp

@[expose] public section

/-!
# Singleton–star entries (`lem:general-star`(d), `eq:singleton-star`)

`paper/sections/14_spectral.tex`, `lem:general-star`(d). For two covariant real kernels the Gram
`Y^*Y'` is `αI + γC` on `L²_0` with `α = tr/(p − 1)`, `γ = tr(C^*·)/(1 − q)` and the traces of
`eq:star-traces` (`gram_two_traces`, any odd `p`). For `p ≡ 3 (mod 4)`, its squared norm is
`α² + qγ²`, and bounds `|tr| ≤ T`, `|tr(C^*·)| ≤ B` give
`‖Y^*Y'‖² ≤ (T/(p − 1))² + q(B/(1 − q))²` (`gram_two_traces_le`): this is the form of every case
of `eq:singleton-star`, `(1 − q)‖V_i^*W_S‖/r ≤ (q T² + B²)^{1/2}`.

For `V_i^*W_S` the traces are `E_μ(ψ_S(x_i, x) − w_S(x))` and `E_μ E_z χ(z − x_i) ψ_S(z, x)`
(`vert_star_gtrace`, `vert_star_gtraceC`). In the case `i ∈ S`, `|S| = 2` they are `q` and
`−q E_μ χ(x_i − x_j)` (two-root identity), and `(1 − q)‖V_i^*W_S‖/r ≤ q√(1 + q)`
(`vert_star_pair_bound`). The other three cases follow from `gram_two_traces_le` once these
traces are bounded, which needs `thm:weil` (`|w_R| ≤ (|R| − 1)r`); they are not stated.

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

section Generic

variable {𝒴 : Type*} [Fintype 𝒴]

/-- `tr(Y^*Y') = E_ν(p ∑ YY' − ∑Y ∑Y')`. -/
noncomputable def gtrace (ν : 𝒴 → ℝ) (Y Y' : 𝒴 → ZMod p → ℝ) : ℝ :=
  ∑ y, ν y * ((p : ℝ) * ∑ a, Y y a * Y' y a - (∑ a, Y y a) * ∑ a, Y' y a)

/-- `tr(C^*Y^*Y') = E_ν ∑_{a,b} Y(a) χ(b − a) Y'(b)`. -/
noncomputable def gtraceC (ν : 𝒴 → ℝ) (Y Y' : 𝒴 → ZMod p → ℝ) : ℝ :=
  ∑ y, ν y * ∑ a, ∑ b, Y y a * chiRe (b - a) * Y' y b

/-- **The Gram of two covariant kernels from its traces** (`lem:spec:affpair`(d),
`eq:star-traces`): `Y^*Y' = tr/(p − 1) I + tr(C^*·)/(1 − q) C` on `L²_0`. -/
theorem gram_two_traces (hp2 : p ≠ 2) {ν : 𝒴 → ℝ} (G : AffAction p 𝒴 ν) (Y Y' : 𝒴 → ZMod p → ℝ)
    (hY : ∀ (s c : ZMod p), s ≠ 0 → IsSquare s → ∀ (h : ZMod p → ℂ) (y : 𝒴),
      kerMap Y (fun a => h (s * a + c)) y = kerMap Y h (G.act s c y))
    (hY' : ∀ (s c : ZMod p), s ≠ 0 → IsSquare s → ∀ (h : ZMod p → ℂ) (y : 𝒴),
      kerMap Y' (fun a => h (s * a + c)) y = kerMap Y' h (G.act s c y))
    (h : ZMod p → ℂ) (hh : meanC h = 0) (a : ZMod p) :
    gramOp ν Y Y' h a = ((gtrace ν Y Y' / ((p : ℝ) - 1) : ℝ) : ℂ) * h a +
      ((gtraceC ν Y Y' / (1 - (p : ℝ)⁻¹) : ℝ) : ℂ) * gaussOp h a := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq1 : (1 : ℝ) - (p : ℝ)⁻¹ ≠ 0 := by
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    linarith
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  obtain ⟨αT, γT, hT⟩ := intertwiner_gram hp2 G Y Y' hY hY'
  have hagree : ∀ ξ : ZMod p, ξ ≠ 0 → gramOp ν Y Y' (ech ξ) =
      fun a => (αT : ℂ) * ech ξ a + (γT : ℂ) * gaussOp (ech ξ) a := by
    intro ξ hξ
    have hm : meanC (ech ξ) = 0 := by rw [meanC_ech, ite_eq_right hξ]
    exact funext (hT (ech ξ) hm)
  obtain ⟨hc1, hc2⟩ := commutant_traces hp2 αT γT
  have h1 : trace0 (gramOp ν Y Y') = ((p : ℂ) - 1) * αT := by
    rw [← hc1]
    unfold trace0
    exact sum_congr rfl fun ξ hξ => by rw [hagree ξ (mem_filter.mp hξ).2]
  have h2 : trace0 (fun h => gaussOpAdj (gramOp ν Y Y' h)) = (1 - (p : ℂ)⁻¹) * γT := by
    rw [← hc2]
    unfold trace0
    exact sum_congr rfl fun ξ hξ => by dsimp only; rw [hagree ξ (mem_filter.mp hξ).2]
  rw [trace_gramOp] at h1
  rw [trace_gaussAdj_gramOp hp2] at h2
  have hA : gtrace ν Y Y' = ((p : ℝ) - 1) * αT := by
    have : ((gtrace ν Y Y' : ℝ) : ℂ) = (((p : ℝ) - 1) * αT : ℝ) := by
      push_cast
      rw [← h1]
      unfold gtrace
      push_cast
      rfl
    exact_mod_cast this
  have hB : gtraceC ν Y Y' = (1 - (p : ℝ)⁻¹) * γT := by
    have : ((gtraceC ν Y Y' : ℝ) : ℂ) = ((1 - (p : ℝ)⁻¹) * γT : ℝ) := by
      push_cast
      rw [← h2]
      unfold gtraceC chiRe
      push_cast
      simp only [chiC_apply]
    exact_mod_cast this
  have hα : αT = gtrace ν Y Y' / ((p : ℝ) - 1) := by rw [hA]; field_simp
  have hγ : γT = gtraceC ν Y Y' / (1 - (p : ℝ)⁻¹) := by rw [hB]; field_simp
  rw [hT h hh a, hα, hγ]

/-- **The norm from bounds on the traces** (`p ≡ 3 (mod 4)`): if `|tr| ≤ T` and
`|tr(C^*·)| ≤ B`, then `‖Y^*Y'h‖² ≤ ((T/(p − 1))² + q(B/(1 − q))²)‖h‖²` on `L²_0`. -/
theorem gram_two_traces_le (hp2 : p ≠ 2) (hp3 : p % 4 = 3) {ν : 𝒴 → ℝ} (G : AffAction p 𝒴 ν)
    (Y Y' : 𝒴 → ZMod p → ℝ)
    (hY : ∀ (s c : ZMod p), s ≠ 0 → IsSquare s → ∀ (h : ZMod p → ℂ) (y : 𝒴),
      kerMap Y (fun a => h (s * a + c)) y = kerMap Y h (G.act s c y))
    (hY' : ∀ (s c : ZMod p), s ≠ 0 → IsSquare s → ∀ (h : ZMod p → ℂ) (y : 𝒴),
      kerMap Y' (fun a => h (s * a + c)) y = kerMap Y' h (G.act s c y))
    {T B : ℝ} (hT : |gtrace ν Y Y'| ≤ T) (hB : |gtraceC ν Y Y'| ≤ B)
    (h : ZMod p → ℂ) (hh : meanC h = 0) :
    l2sq (gramOp ν Y Y' h) ≤
      ((T / ((p : ℝ) - 1)) ^ 2 + (p : ℝ)⁻¹ * (B / (1 - (p : ℝ)⁻¹)) ^ 2) * l2sq h := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp1' : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hq1 : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    linarith
  have hfun : gramOp ν Y Y' h = fun a => ((gtrace ν Y Y' / ((p : ℝ) - 1) : ℝ) : ℂ) * h a +
      ((gtraceC ν Y Y' / (1 - (p : ℝ)⁻¹) : ℝ) : ℂ) * gaussOp h a :=
    funext (gram_two_traces hp2 G Y Y' hY hY' h hh)
  rw [hfun, commutant_norm hp2 hp3 _ _ h hh]
  apply mul_le_mul_of_nonneg_right _ (by unfold l2sq; positivity)
  have e1 : (gtrace ν Y Y' / ((p : ℝ) - 1)) ^ 2 ≤ (T / ((p : ℝ) - 1)) ^ 2 := by
    rw [div_pow, div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hT 2
  have e2 : (gtraceC ν Y Y' / (1 - (p : ℝ)⁻¹)) ^ 2 ≤ (B / (1 - (p : ℝ)⁻¹)) ^ 2 := by
    rw [div_pow, div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hB 2
  have hq0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left e2 hq0]

end Generic

/-! ## `V_i^*W_S` -/

variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] [DecidableEq U] in
lemma sum_chiRe_shift (hp2 : p ≠ 2) (t : ZMod p) : ∑ b, chiRe (b - t) = 0 := by
  have h := quadraticChar_sum_zero (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  rw [Fintype.sum_equiv (Equiv.subRight t) (fun b => chiRe (b - t)) chiRe (fun b => rfl)]
  unfold chiRe
  exact_mod_cast h

omit [Fintype U] [DecidableEq U] in
lemma chiRe_sq_eq (b t : ZMod p) : chiRe (b - t) * chiRe (b - t) = 1 - if b = t then 1 else 0 := by
  by_cases hb : b = t
  · rw [hb, sub_self, ite_eq_left rfl]; unfold chiRe; simp
  · rw [ite_eq_right hb, sub_zero]
    have hne : b - t ≠ 0 := sub_ne_zero.mpr hb
    unfold chiRe
    rw [← sq]
    exact_mod_cast quadraticChar_sq_one hne

/-- The trace `tr(V_i^*W_S) = E_μ(ψ_S(x_i, x) − w_S(x))`. -/
lemma vert_star_gtrace (μ : (U → ZMod p) → ℝ) (i : U) (S : Finset U) :
    gtrace μ (vertKer i) (starKer S) =
      ∑ x, μ x * (∏ k ∈ S, chiRe (x i - x k) - starMean S x) := by
  unfold gtrace
  refine sum_congr rfl fun x _ => ?_
  congr 1
  have h1 : ∑ a, vertKer i x a * starKer S x a = starKer S x (x i) := by
    unfold vertKer
    rw [sum_eq_single (x i) (fun b _ hb => by rw [ite_eq_right hb, zero_mul])
      (fun h => absurd (mem_univ _) h), ite_eq_left rfl, one_mul]
  rw [h1, sum_vertKer, one_mul]
  unfold starMean starKer
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp

/-- The trace `tr(C^*V_i^*W_S) = E_μ ∑_b χ(b − x_i) (ψ_S(b, x)/p) = E_μ E_z χ(z − x_i)ψ_S(z, x)`. -/
lemma vert_star_gtraceC (μ : (U → ZMod p) → ℝ) (i : U) (S : Finset U) :
    gtraceC μ (vertKer i) (starKer S) =
      ∑ x, μ x * ∑ b, chiRe (b - x i) * starKer S x b := by
  unfold gtraceC
  refine sum_congr rfl fun x _ => ?_
  congr 1
  unfold vertKer
  rw [sum_eq_single (x i) (fun a _ ha => by simp [ha]) (fun h => absurd (mem_univ _) h)]
  simp

/-- **`lem:general-star`(d), the case `i ∈ S`, `|S| = 2`** (`p ≡ 3 (mod 4)`): for `S = {i, j}`
and injective `μ`, `‖V_i^*W_S h‖² ≤ q³(1 + q)/(1 − q)² ‖h‖²` on `L²_0`, that is
`(1 − q)‖V_i^*W_S‖/r ≤ q√(1 + q)`. -/
theorem vert_star_pair_bound (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {i j : U} (hij : i ≠ j) (h : ZMod p → ℂ) (hh : meanC h = 0) :
    l2sq (gramOp μ (vertKer i) (starKer {i, j}) h) ≤
      (p : ℝ)⁻¹ ^ 3 * (1 + (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2 * l2sq h := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  -- the two traces
  have hstar : ∀ (x : U → ZMod p) (a : ZMod p),
      starKer {i, j} x a = (p : ℝ)⁻¹ * (chiRe (a - x i) * chiRe (a - x j)) := by
    intro x a; unfold starKer; rw [prod_pair hij]
  have hT : gtrace μ (vertKer i) (starKer {i, j}) = (p : ℝ)⁻¹ := by
    unfold gtrace
    have hx : ∀ x, μ x * ((p : ℝ) * ∑ a, vertKer i x a * starKer {i, j} x a -
        (∑ a, vertKer i x a) * ∑ a, starKer {i, j} x a) = μ x * (p : ℝ)⁻¹ := by
      intro x
      by_cases hx : μ x = 0
      · rw [hx, zero_mul, zero_mul]
      congr 1
      have h1 : ∑ a, vertKer i x a * starKer {i, j} x a = 0 := by
        unfold vertKer
        rw [sum_eq_single (x i) (fun b _ hb => by rw [ite_eq_right hb, zero_mul])
          (fun h => absurd (mem_univ _) h), ite_eq_left rfl, one_mul, hstar, sub_self]
        unfold chiRe
        simp
      have h2 : ∑ a, starKer {i, j} x a = -(p : ℝ)⁻¹ := by
        rw [sum_congr rfl fun a _ => hstar x a, ← mul_sum, sum_chiRe_mul hp2,
          ite_eq_right (hinj x i j hx hij)]
        ring
      rw [h1, sum_vertKer, h2]
      ring
    rw [sum_congr rfl fun x _ => hx x, ← sum_mul, hμ1, one_mul]
  have hB : |gtraceC μ (vertKer i) (starKer {i, j})| ≤ (p : ℝ)⁻¹ := by
    unfold gtraceC
    have hx : ∀ x, μ x * ∑ a, ∑ b, vertKer i x a * chiRe (b - a) * starKer {i, j} x b =
        μ x * ((p : ℝ)⁻¹ * -chiRe (x i - x j)) := by
      intro x
      congr 1
      unfold vertKer
      rw [sum_eq_single (x i) (fun a _ ha => by simp [ha]) (fun h => absurd (mem_univ _) h)]
      simp only [ite_true, one_mul]
      have e : ∀ b, chiRe (b - x i) * starKer {i, j} x b =
          (p : ℝ)⁻¹ * ((1 - if b = x i then 1 else 0) * chiRe (b - x j)) := by
        intro b; rw [hstar, ← chiRe_sq_eq]; ring
      rw [sum_congr rfl fun b _ => e b, ← mul_sum]
      congr 1
      simp only [sub_mul, one_mul, ite_mul, zero_mul, sum_sub_distrib, sum_ite_eq', mem_univ,
        ite_true, sum_chiRe_shift hp2]
      ring
    rw [sum_congr rfl fun x _ => hx x]
    calc |∑ x, μ x * ((p : ℝ)⁻¹ * -chiRe (x i - x j))|
        ≤ ∑ x, μ x * (p : ℝ)⁻¹ := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
          rw [abs_mul, abs_of_nonneg (hμ0 x), abs_mul, abs_neg, abs_of_pos (by positivity)]
          apply mul_le_mul_of_nonneg_left _ (hμ0 x)
          exact mul_le_of_le_one_right (by positivity) (abs_chiRe_le (x i - x j))
      _ = (p : ℝ)⁻¹ := by rw [← sum_mul, hμ1, one_mul]
  have hb := gram_two_traces_le hp2 hp3 (labAction μ hinv) (vertKer i) (starKer {i, j})
    (fun s c _ _ h' x => vertKer_cov i s c h' x) (fun s c hs hsq h' x => starKer_cov _ s c hs hsq h' x)
    (le_of_eq (by rw [hT, abs_of_pos (by positivity)])) hB h hh
  refine hb.trans (le_of_eq ?_)
  congr 1
  have hq1 : (1 : ℝ) - (p : ℝ)⁻¹ ≠ 0 := by
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    linarith
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

end Sarkozy.SpectralC
