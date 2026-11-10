module

public import Sarkozy.SpectralC.All

@[expose] public section

/-!
# The Paley part of the coupling (`lem:spec2:paley`(b))

`paper/sections/14_spectral.tex`, `subsec:spec:coupling`, the Paley part. Notation as in
`Sarkozy.SpectralC` (WP-K): `p` an odd prime, `q = p⁻¹`, `r = p^{-1/2}` (`rp p`), labellings
`x : U → 𝔽_p`, the cross neighbourhoods `N(k)` and signs `ς_jk`, the Gauss operator `C`
(`gaussOp`), the inner product `ip` and `l2sq` of the uniform probability on `𝔽_p`.

For a law `ν` on labellings and vectors `P_k(· | x)`, `Ψ_k = pP_k − 1` (`psiField`),
`φ_k = ∏_{j∈N(k)} (1 + χ(ς_jk(a − x_j)))` (`starProd`), `E_k = pP_k − φ_k`,
`𝐃 = E_ν⟨Ψ_k, CΨ_l⟩` (`gramP ν (psiField P)`), `H̃ = E_ν⟨Ψ_k, Ψ_l⟩` (`gramΓ ν (psiField P)`),
`g_J(a; x) = ∏_{j∈J} χ(a − x_j)` (`gJ`), `S_J = ⟨g_J, Cg_J⟩` (`SJ`), `t_J = E_ν S_J` (`tJ`), and
`(ε_J)_k = ∏_{j∈J} χ(ς_jk)` if `J ⊆ N(k)`, `0` otherwise (`epsJ`).

**`lem:spec2:paley`(b)** (`paley_b`): if `E_ν‖∑_k w_kE_k‖² ≤ Γ_E|w|²` and
`w^*H̃w ≤ Λ_H|w|²` (the paper's `Λ_H = λ̄(𝐇) + ε_H`), and if under `ν` every conditional
probability of one label is at most `D_j/p` with `D_j − 1 ≤ θ²` (the paper's
`θ_j = (R_ν 2^{d⁰_j}/(1 − e_{d⁰_j}(p, n)) − 1)^{1/2} ≤ θ_max`), and
`(2^{r_k} − 1)∑_l(2^{r_l} − 1) ≤ ρ` (`ρ_row`), then
`|w^*𝐃w − ∑_{|J|≥2} t_J|ε_J·w|²| ≤ r(ε_≠ + ε_rem(Γ_E))|w|²` with `ε_≠ = rθρ` and
`ε_rem = 2(Γ_EΛ_H)^{1/2} + Γ_E`.

The three numbers `Γ_E`, `Λ_H`, `D_j` are hypotheses, as in the paper: `Γ_E` is supplied by
`lem:spec2:paley`(a) (`SpectralC.paley_deviation`) or by `lem:projection-diagonal`; `Λ_H` by
`lem:spec2:gram` (`SpectralC.gram_comparison`) and a certified `λ̄(𝐇)`; `D_j` by
`lem:graphs:vertex`(dens) and the density ratio `R_ν` (`condLaw_le_of_density` turns a density
ratio into the pivot bound). No other property of `ν` or `P` is used: the probability-vector,
support and covariance conditions of `def:coupling-data` enter only through these three numbers.

The proof is the paper's. Write `Ψ_w = φ°_w + E_w`; the `E` terms are bounded by Cauchy–Schwarz
(`cform_diff_bound`, `remainder_bound`). For the main term, `φ°_w = ∑_{J≠∅} (ε_J·w) g_J`
(`phi_eq`, from `χ_{J,k} = (ε_J)_k g_J`), so `E_ν⟨φ°_w, Cφ°_w⟩ = ∑_{J,J'} \overline{c_J} c_{J'}
E_ν⟨g_J, Cg_{J'}⟩` (`main_eq`). For `J ≠ J'` a pivot `j ∈ J △ J'` gives
`|E_ν⟨g_J, Cg_{J'}⟩| ≤ r²θ` (`pivot_core`, `pivot_bound`: the conditional law of `x_j` under
`ν`, `‖φ_j‖² = ∑_t ν_j(t)² − q ≤ q(D_j − 1)` by the two-root identity, `‖C‖ = r`); the
diagonal terms are `t_J|ε_J·w|²`, and the singletons vanish (`SJ_singleton`, part (c)). The
off-diagonal total is at most `r²θ(∑_J|c_J|)² ≤ r²θ(∑_k(2^{r_k} − 1)|w_k|)² ≤ r²θρ|w|²`
(`sum_norm_cJ_le`, `schur_sq`).

New material for this paper.
-/

namespace Sarkozy.SpectralD.PaleyB

open Finset Complex Sarkozy.Characters Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

/-! ## The form `⟨f, Cg⟩` -/

/-- `B(f, g) = ⟨f, Cg⟩`. -/
noncomputable def cform (f g : ZMod p → ℂ) : ℂ := ip f (gaussOp g)

lemma cform_eq (f g : ZMod p → ℂ) :
    cform f g = (p : ℂ)⁻¹ * (p : ℂ)⁻¹ * ∑ a, ∑ b, conj (f a) * chiC p (b - a) * g b := by
  unfold cform ip gaussOp
  simp only [mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

lemma cform_sub_left (f g h : ZMod p → ℂ) :
    cform (fun a => f a - g a) h = cform f h - cform g h := by
  simp only [cform_eq, map_sub, sub_mul, sum_sub_distrib, mul_sub]

lemma cform_sub_right (f g h : ZMod p → ℂ) :
    cform f (fun a => g a - h a) = cform f g - cform f h := by
  simp only [cform_eq, mul_sub, sum_sub_distrib]

/-- `B(Ψ − E, Ψ − E) = B(Ψ, Ψ) − B(Ψ, E) − B(E, Ψ) + B(E, E)`. -/
lemma cform_sub_sub (f g : ZMod p → ℂ) :
    cform (fun a => f a - g a) (fun a => f a - g a) =
      cform f f - cform f g - cform g f + cform g g := by
  rw [cform_sub_left, cform_sub_right, cform_sub_right]
  ring

lemma l2sq_nonneg' (h : ZMod p → ℂ) : 0 ≤ l2sq h := by
  unfold l2sq; positivity

/-- `‖C‖ = r` in the form `‖Cg‖ ≤ r‖g‖`. -/
lemma sqrt_l2sq_gaussOp_le (hp2 : p ≠ 2) (g : ZMod p → ℂ) :
    Real.sqrt (l2sq (gaussOp g)) ≤ rp p * Real.sqrt (l2sq g) := by
  have hr : 0 ≤ rp p := by unfold rp; positivity
  rw [← Real.sqrt_sq hr, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (l2sq_gaussOp_le hp2 g)

/-- `|⟨f, Cg⟩| ≤ r‖f‖‖g‖`. -/
lemma norm_cform_le (hp2 : p ≠ 2) (f g : ZMod p → ℂ) :
    ‖cform f g‖ ≤ rp p * (Real.sqrt (l2sq f) * Real.sqrt (l2sq g)) := by
  unfold cform
  calc ‖ip f (gaussOp g)‖ ≤ Real.sqrt (l2sq f) * Real.sqrt (l2sq (gaussOp g)) := norm_ip_le _ _
    _ ≤ Real.sqrt (l2sq f) * (rp p * Real.sqrt (l2sq g)) :=
        mul_le_mul_of_nonneg_left (sqrt_l2sq_gaussOp_le hp2 g) (Real.sqrt_nonneg _)
    _ = rp p * (Real.sqrt (l2sq f) * Real.sqrt (l2sq g)) := by ring

/-- `⟨u, Cv⟩ = χ(−1)\overline{⟨v, Cu⟩}`. -/
lemma cform_swap (u v : ZMod p → ℂ) : cform u v = chiC p (-1) * conj (cform v u) := by
  rw [cform_eq, cform_eq]
  simp only [map_mul, map_inv₀, Complex.conj_natCast, map_sum, Complex.conj_conj, conj_chiC]
  rw [sum_comm (s := univ) (t := univ) (f := fun a b => v a * chiC p (b - a) * conj (u b))]
  have h : ∀ a b : ZMod p, conj (u a) * chiC p (b - a) * v b =
      chiC p (-1) * (v b * chiC p (a - b) * conj (u a)) := by
    intro a b
    have : chiC p (b - a) = chiC p (-1) * chiC p (a - b) := by
      rw [← map_mul]; congr 1; ring
    rw [this]; ring
  simp_rw [h, ← mul_sum]
  ring

lemma norm_chiC_neg_one : ‖chiC p (-1)‖ = 1 := norm_chiC (neg_ne_zero.mpr one_ne_zero)

/-! ## Quadratic forms of the Gram matrices -/

section Forms

variable {𝒴 ι : Type*} [Fintype 𝒴] [Fintype ι]

/-- `w^*𝐃w = E_ν⟨V_w, CV_w⟩` for `𝐃 = E_ν⟨V_k, CV_l⟩` (`gramP`). -/
lemma qform_gramP_eq (ν : 𝒴 → ℝ) (V : ι → 𝒴 → ZMod p → ℂ) (w : ι → ℂ) :
    qform (gramP ν V) w = ∑ y, (ν y : ℂ) * cform (fieldW V w y) (fieldW V w y) := by
  rw [gramP_eq, qform_bilin]
  refine sum_congr rfl fun y _ => ?_
  rw [cform_eq]
  congr 1
  simp only [mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

/-- `w^*H̃w = E_ν‖V_w‖²` for `H̃ = E_ν⟨V_k, V_l⟩` (`gramΓ`). -/
lemma qform_gramΓ_eq (ν : 𝒴 → ℝ) (V : ι → 𝒴 → ZMod p → ℂ) (w : ι → ℂ) :
    qform (gramΓ ν V) w = ∑ y, ((ν y * l2sq (fieldW V w y) : ℝ) : ℂ) := by
  rw [gramΓ_eq, qform_bilin]
  refine sum_congr rfl fun y _ => ?_
  push_cast
  congr 1
  unfold l2sq
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_eq_single a (fun b _ hb => by rw [ite_eq_right (Ne.symm hb), zero_mul])
    (fun h => absurd (mem_univ a) h), ite_eq_left rfl, Complex.conj_mul']

lemma re_qform_gramΓ_eq (ν : 𝒴 → ℝ) (V : ι → 𝒴 → ZMod p → ℂ) (w : ι → ℂ) :
    (qform (gramΓ ν V) w).re = ∑ y, ν y * l2sq (fieldW V w y) := by
  rw [qform_gramΓ_eq, ← Complex.ofReal_sum, Complex.ofReal_re]

end Forms

/-! ## Star coefficients and the expansion of `φ_k` -/

section Stars

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `(ε_J)_k = ∏_{j∈J} χ(ς_jk)` if `J ⊆ N(k)`, and `0` otherwise (a number in `{0, ±1}`). -/
noncomputable def epsJ (N : U → Finset U) (ς : U → U → ZMod p) (J : Finset U) (k : U) : ℂ :=
  if J ⊆ N k then ∏ j ∈ J, chiC p (ς j k) else 0

/-- The coefficients `c_J = ε_J·w = ∑_k (ε_J)_k w_k` of `φ°_w = ∑_{J≠∅} c_J g_J`, with `c_∅ = 0`. -/
noncomputable def cJ (N : U → Finset U) (ς : U → U → ZMod p) (w : U → ℂ) (J : Finset U) : ℂ :=
  if J = ∅ then 0 else ∑ k, epsJ N ς J k * w k

/-- `t_J = E_ν S_J(x_J)`. -/
noncomputable def tJ (ν : (U → ZMod p) → ℝ) (J : Finset U) : ℂ := ∑ x, (ν x : ℂ) * SJ J x

/-- The functions `g_J(·; x)`, indexed by `J`. -/
noncomputable def gJf (J : Finset U) (x : U → ZMod p) (a : ZMod p) : ℂ := gJ J x a

omit [Fintype U] in
/-- `φ_k = ∑_{J ⊆ N(k)} χ_{J,k} = ∑_J (ε_J)_k g_J`, since `χ(ς(a − x)) = χ(ς)χ(a − x)`. -/
lemma starProd_eq_sum [Fintype U] (N : U → Finset U) (ς : U → U → ZMod p) (k : U)
    (x : U → ZMod p) (a : ZMod p) :
    starProd N ς k x a = ∑ J, epsJ N ς J k * gJ J x a := by
  unfold starProd
  rw [prod_one_add]
  have h1 : ∀ t ∈ (N k).powerset, ∏ j ∈ t, chiC p (ς j k * (a - x j)) =
      (∏ j ∈ t, chiC p (ς j k)) * gJ t x a := by
    intro t _
    unfold gJ
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun j _ => map_mul _ _ _
  rw [sum_congr rfl h1]
  unfold epsJ
  simp only [ite_mul, zero_mul]
  rw [← sum_filter]
  congr 1
  ext J
  simp [mem_powerset]

omit [Fintype U] in
lemma epsJ_empty (N : U → Finset U) (ς : U → U → ZMod p) (k : U) : epsJ N ς ∅ k = 1 := by
  unfold epsJ; simp

omit [Fintype U] [DecidableEq U] in
lemma gJ_empty (x : U → ZMod p) (a : ZMod p) : gJ (∅ : Finset U) x a = 1 := by
  unfold gJ; simp

/-- `φ_k − 1 = ∑_{J ≠ ∅} (ε_J)_k g_J`. -/
lemma starProd_sub_one (N : U → Finset U) (ς : U → U → ZMod p) (k : U) (x : U → ZMod p)
    (a : ZMod p) :
    starProd N ς k x a - 1 = ∑ J, (if J = ∅ then 0 else epsJ N ς J k) * gJ J x a := by
  rw [starProd_eq_sum, ← add_sum_erase univ _ (mem_univ (∅ : Finset U)),
    ← add_sum_erase univ (fun J => (if J = ∅ then 0 else epsJ N ς J k) * gJ J x a)
      (mem_univ ∅)]
  simp only [epsJ_empty, gJ_empty, ↓reduceIte, mul_one, zero_add, add_sub_cancel_left]
  refine sum_congr rfl fun J hJ => ?_
  rw [ite_eq_right (ne_of_mem_erase hJ)]

/-- **`φ°_w = ∑_J c_J g_J`**: `∑_k w_k(φ_k − 1) = ∑_{J≠∅} (ε_J·w) g_J`. -/
lemma phi_eq (N : U → Finset U) (ς : U → U → ZMod p) (w : U → ℂ) (x : U → ZMod p)
    (a : ZMod p) :
    ∑ k, w k * (starProd N ς k x a - 1) = ∑ J, cJ N ς w J * gJ J x a := by
  simp_rw [starProd_sub_one, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun J _ => ?_
  unfold cJ
  by_cases hJ : J = ∅
  · simp [hJ]
  · simp only [hJ, ↓reduceIte, sum_mul]
    exact sum_congr rfl fun k _ => by ring

/-! ## The pivot -/

/-- The law of total expectation, for complex functions (`SpectralC.sum_mu_class` is the real
case). -/
lemma sum_mu_class_C (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (A : Finset U)
    (G : (U → ZMod p) → ℂ) :
    ∑ x, (μ x : ℂ) * ((∑ x', if agree A x x' then (μ x' : ℂ) * G x' else 0) /
      (cmass μ A x : ℂ)) = ∑ x, (μ x : ℂ) * G x := by
  have h1 : ∀ x, (μ x : ℂ) * ((∑ x', if agree A x x' then (μ x' : ℂ) * G x' else 0) /
      (cmass μ A x : ℂ)) =
      ∑ x', if agree A x' x then (μ x' : ℂ) * G x' * ((μ x / cmass μ A x : ℝ) : ℂ) else 0 := by
    intro x
    rw [sum_div, mul_sum]
    refine sum_congr rfl fun x' _ => ?_
    by_cases h : agree A x x'
    · rw [ite_eq_left h, ite_eq_left (agree_comm.mp h)]; push_cast; ring
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (agree_comm.mpr h'))]; simp
  rw [sum_congr rfl fun x _ => h1 x, sum_comm]
  refine sum_congr rfl fun x' _ => ?_
  have h2 : ∑ x, (if agree A x' x then (μ x' : ℂ) * G x' * ((μ x / cmass μ A x : ℝ) : ℂ)
      else 0) = (μ x' : ℂ) * G x' *
        ((∑ x, if agree A x' x then μ x / cmass μ A x else 0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [h2]
  by_cases hm : cmass μ A x' = 0
  · have : μ x' = 0 := le_antisymm (hm ▸ mu_le_cmass μ hμ0 A x') (hμ0 x')
    rw [this]; simp
  · rw [sum_class_div μ A x' hm]; simp

/-- **The tower property for one coordinate**: `E_ν F = E_ν ∑_t ν_j(t | x) F(x[j ↦ t])`, with
`ν_j(· | x)` the conditional law of `x_j` given the other labels (`condLaw`). -/
lemma tower (ν : (U → ZMod p) → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (j : U) (F : (U → ZMod p) → ℂ) :
    ∑ x, (ν x : ℂ) * F x =
      ∑ x, (ν x : ℂ) * ∑ t, (condLaw ν j x t : ℂ) * F (Function.update x j t) := by
  rw [← sum_mu_class_C ν hν0 (univ.erase j) F]
  refine sum_congr rfl fun x _ => ?_
  congr 1
  rw [sum_agree_erase j x (fun x' => (ν x' : ℂ) * F x'), sum_div]
  refine sum_congr rfl fun t _ => ?_
  unfold condLaw
  push_cast
  ring

omit [Fintype U] [DecidableEq U] in
lemma gJ_update_of_notMem [DecidableEq U] {J : Finset U} {j : U} (hj : j ∉ J)
    (x : U → ZMod p) (t : ZMod p) : gJ J (Function.update x j t) = gJ J x := by
  funext a
  unfold gJ
  refine prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (by rintro rfl; exact hj hi)]

omit [Fintype U] in
lemma gJ_update_of_mem {J : Finset U} {j : U} (hj : j ∈ J) (x : U → ZMod p) (t : ZMod p) :
    gJ J (Function.update x j t) = fun a => chiC p (a - t) * gJ (J.erase j) x a := by
  funext a
  unfold gJ
  rw [← mul_prod_erase J _ hj, Function.update_self]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hi)]

omit [Fintype U] [DecidableEq U] in
/-- `∑_t c_t ⟨u_t, Ch⟩ = ⟨∑_t c_t u_t, Ch⟩` for real `c_t`. -/
lemma sum_cform_left (c : ZMod p → ℝ) (u : ZMod p → ZMod p → ℂ) (h : ZMod p → ℂ) :
    ∑ t, (c t : ℂ) * cform (u t) h = cform (fun a => ∑ t, (c t : ℂ) * u t a) h := by
  simp only [cform_eq, map_sum, map_mul, Complex.conj_ofReal, sum_mul, mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact sum_congr rfl fun b _ => sum_congr rfl fun t _ => by ring

omit [Fact p.Prime] in
lemma rp_sq : rp p ^ 2 = (p : ℝ)⁻¹ := by
  unfold rp
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg p)]

omit [Fintype U] [DecidableEq U] in
lemma l2sq_gJ_le (J : Finset U) (x : U → ZMod p) : l2sq (gJ J x) ≤ 1 := by
  unfold l2sq
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc (p : ℝ)⁻¹ * ∑ a, ‖gJ J x a‖ ^ 2 ≤ (p : ℝ)⁻¹ * ∑ _a : ZMod p, (1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum; intro a _
        have := norm_gJ_le J x a
        nlinarith [norm_nonneg (gJ J x a)]
    _ = 1 := by
        rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]
        exact inv_mul_cancel₀ hp.ne'

/-- `‖φ‖² = ∑_t ν_t² − q ≤ (D − 1)/p` for `φ(a) = ∑_t ν_t χ(a − t)`, `ν` a probability vector
with `ν_t ≤ D/p` (`eq:two-root`). -/
lemma l2sq_phi_le (hp2 : p ≠ 2) (νj : ZMod p → ℝ) (h1 : ∑ t, νj t = 1) (h0 : ∀ t, 0 ≤ νj t)
    {D : ℝ} (hD : ∀ t, νj t ≤ D / p) :
    l2sq (fun a => ∑ t, (νj t : ℂ) * chiC p (a - t)) ≤ (D - 1) / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hc : ∀ a : ZMod p, ∑ t, (νj t : ℂ) * chiC p (a - t) =
      ((∑ t, νj t * chiRe (a - t) : ℝ) : ℂ) := by
    intro a
    push_cast
    refine sum_congr rfl fun t _ => ?_
    unfold chiRe
    rw [chiC_apply]
    push_cast
    rfl
  unfold l2sq
  simp_rw [hc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [sum_phi_sq hp2, h1]
  have hν2 : ∑ t, νj t ^ 2 ≤ D / p := by
    have : ∑ t, νj t ^ 2 ≤ ∑ t, D / p * νj t :=
      sum_le_sum fun t _ => by rw [sq]; exact mul_le_mul_of_nonneg_right (hD t) (h0 t)
    rwa [← mul_sum, h1, mul_one] at this
  have e : (D - 1) / p = (p : ℝ)⁻¹ * ((p : ℝ) * (D / p) - 1) := by field_simp
  rw [e, one_pow]
  gcongr

omit [Fintype U] [DecidableEq U] in
/-- `‖φ g‖² ≤ ‖φ‖²` when `|g| ≤ 1`. -/
lemma l2sq_mul_le (φ g : ZMod p → ℂ) (hg : ∀ a, ‖g a‖ ≤ 1) :
    l2sq (fun a => φ a * g a) ≤ l2sq φ := by
  unfold l2sq
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum; intro a _
  rw [norm_mul, mul_pow]
  have h1 : ‖g a‖ ^ 2 ≤ 1 := by
    have := hg a
    nlinarith [norm_nonneg (g a)]
  nlinarith [sq_nonneg ‖φ a‖]

/-- **The pivot** (the terms `J ≠ J'` of `lem:spec2:paley`(b)): for `j ∈ J ∖ J'`, with
conditional probabilities `ν_j(t | x) ≤ D/p` and `D − 1 ≤ θ²`,
`|E_ν⟨g_J, Cg_{J'}⟩| ≤ (∑ν) r²θ`. -/
lemma pivot_core (hp2 : p ≠ 2) (ν : (U → ZMod p) → ℝ) (hν0 : ∀ x, 0 ≤ ν x) {j : U}
    {J J' : Finset U} (hjJ : j ∈ J) (hjJ' : j ∉ J') {D θ : ℝ}
    (hD : ∀ x t, ν x ≠ 0 → condLaw ν j x t ≤ D / p) (hθ0 : 0 ≤ θ) (hθ : D - 1 ≤ θ ^ 2) :
    ‖∑ x, (ν x : ℂ) * cform (gJ J x) (gJ J' x)‖ ≤ (∑ x, ν x) * (rp p * (rp p * θ)) := by
  have hr : 0 ≤ rp p := by unfold rp; positivity
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [tower ν hν0 j]
  have hin : ∀ x, ∑ t, (condLaw ν j x t : ℂ) *
      cform (gJ J (Function.update x j t)) (gJ J' (Function.update x j t)) =
      cform (fun a => (∑ t, (condLaw ν j x t : ℂ) * chiC p (a - t)) * gJ (J.erase j) x a)
        (gJ J' x) := by
    intro x
    simp_rw [gJ_update_of_mem hjJ, gJ_update_of_notMem hjJ']
    rw [sum_cform_left (condLaw ν j x) (fun t a => chiC p (a - t) * gJ (J.erase j) x a)]
    congr 1
    funext a
    rw [sum_mul]
    exact sum_congr rfl fun t _ => by ring
  simp_rw [hin]
  have hbd : ∀ x, ν x * ‖cform (fun a => (∑ t, (condLaw ν j x t : ℂ) * chiC p (a - t)) *
      gJ (J.erase j) x a) (gJ J' x)‖ ≤ ν x * (rp p * (rp p * θ)) := by
    intro x
    by_cases hx : ν x = 0
    · rw [hx, zero_mul, zero_mul]
    apply mul_le_mul_of_nonneg_left _ (hν0 x)
    have hφ := l2sq_phi_le hp2 (condLaw ν j x) (sum_condLaw ν hν0 j x hx)
      (condLaw_nonneg ν hν0 j x) (hD x · hx)
    have h1 := l2sq_mul_le (fun a => ∑ t, (condLaw ν j x t : ℂ) * chiC p (a - t))
      (gJ (J.erase j) x) (norm_gJ_le (J.erase j) x)
    have h2 := l2sq_gJ_le J' x
    have hs1 : Real.sqrt (l2sq (fun a => (∑ t, (condLaw ν j x t : ℂ) * chiC p (a - t)) *
        gJ (J.erase j) x a)) ≤ rp p * θ := by
      have e : rp p * θ = Real.sqrt ((rp p * θ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      rw [e]
      apply Real.sqrt_le_sqrt
      rw [mul_pow, rp_sq]
      calc _ ≤ (D - 1) / p := h1.trans hφ
        _ ≤ θ ^ 2 / p := by gcongr
        _ = (p : ℝ)⁻¹ * θ ^ 2 := by ring
    have hs2 : Real.sqrt (l2sq (gJ J' x)) ≤ 1 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt h2
    calc ‖cform _ (gJ J' x)‖ ≤ rp p * (Real.sqrt (l2sq (fun a =>
          (∑ t, (condLaw ν j x t : ℂ) * chiC p (a - t)) * gJ (J.erase j) x a)) *
            Real.sqrt (l2sq (gJ J' x))) := norm_cform_le hp2 _ _
      _ ≤ rp p * ((rp p * θ) * 1) := by
          apply mul_le_mul_of_nonneg_left _ hr
          exact mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (by positivity)
      _ = rp p * (rp p * θ) := by ring
  calc ‖∑ x, (ν x : ℂ) * cform (fun a => (∑ t, (condLaw ν j x t : ℂ) * chiC p (a - t)) *
        gJ (J.erase j) x a) (gJ J' x)‖
      ≤ ∑ x, ν x * ‖cform (fun a => (∑ t, (condLaw ν j x t : ℂ) * chiC p (a - t)) *
          gJ (J.erase j) x a) (gJ J' x)‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun x _ => ?_))
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hν0 x)]
    _ ≤ ∑ x, ν x * (rp p * (rp p * θ)) := sum_le_sum fun x _ => hbd x
    _ = (∑ x, ν x) * (rp p * (rp p * θ)) := by rw [sum_mul]

omit [Fintype U] [DecidableEq U] in
/-- `|E_ν⟨u, Cv⟩| = |E_ν⟨v, Cu⟩|` (`C^* = χ(−1)C`). -/
lemma norm_sum_cform_swap {𝒴 : Type*} [Fintype 𝒴] (ν : 𝒴 → ℝ) (u v : 𝒴 → ZMod p → ℂ) :
    ‖∑ x, (ν x : ℂ) * cform (u x) (v x)‖ = ‖∑ x, (ν x : ℂ) * cform (v x) (u x)‖ := by
  have h1 : ∀ x, (ν x : ℂ) * cform (u x) (v x) =
      chiC p (-1) * conj ((ν x : ℂ) * cform (v x) (u x)) := fun x => by
    rw [cform_swap (u x) (v x), map_mul, Complex.conj_ofReal]; ring
  rw [sum_congr rfl fun x _ => h1 x, ← mul_sum, ← map_sum, norm_mul, norm_chiC_neg_one, one_mul,
    Complex.norm_conj]

/-- **The terms `J ≠ J'`**: `|E_ν⟨g_J, Cg_{J'}⟩| ≤ r²θ`, by a pivot `j ∈ J △ J'`. -/
theorem pivot_bound (hp2 : p ≠ 2) (ν : (U → ZMod p) → ℝ) (hν0 : ∀ x, 0 ≤ ν x)
    (hν1 : ∑ x, ν x = 1) (Dj : U → ℝ) (hpiv : ∀ j x t, ν x ≠ 0 → condLaw ν j x t ≤ Dj j / p)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ j, Dj j - 1 ≤ θ ^ 2) {J J' : Finset U} (hJJ : J ≠ J') :
    ‖∑ x, (ν x : ℂ) * cform (gJ J x) (gJ J' x)‖ ≤ rp p * (rp p * θ) := by
  by_cases h : J ⊆ J'
  · have h' : ¬ J' ⊆ J := fun h' => hJJ (subset_antisymm h h')
    obtain ⟨j, hj', hj⟩ := not_subset.mp h'
    rw [norm_sum_cform_swap ν (fun x => gJ J x) (fun x => gJ J' x)]
    have := pivot_core hp2 ν hν0 hj' hj (hpiv j) hθ0 (hθ j)
    rwa [hν1, one_mul] at this
  · obtain ⟨j, hj, hj'⟩ := not_subset.mp h
    have := pivot_core hp2 ν hν0 hj hj' (hpiv j) hθ0 (hθ j)
    rwa [hν1, one_mul] at this

/-! ## Counting and the Schur test -/

omit [Fintype U] in
lemma norm_epsJ_le (N : U → Finset U) (ς : U → U → ZMod p) (J : Finset U) (k : U) :
    ‖epsJ N ς J k‖ ≤ if J ⊆ N k then 1 else 0 := by
  unfold epsJ
  split_ifs
  · rw [norm_prod]
    apply prod_le_one₀ (fun j _ => norm_nonneg _)
    intro j _
    by_cases h : ς j k = 0
    · rw [h, chiC_zero, norm_zero]; exact zero_le_one
    · rw [norm_chiC h]
  · simp

/-- `#{J : ∅ ≠ J ⊆ N(k)} = 2^{r_k} − 1`. -/
lemma sum_nonempty_subsets (N : U → Finset U) (k : U) :
    ∑ J : Finset U, (if J = ∅ then (0 : ℝ) else if J ⊆ N k then 1 else 0) =
      (2 : ℝ) ^ (N k).card - 1 := by
  have h1 : ∑ J : Finset U, (if J ⊆ N k then (1 : ℝ) else 0) = (2 : ℝ) ^ (N k).card := by
    rw [sum_boole]
    have : (univ.filter (fun J : Finset U => J ⊆ N k)) = (N k).powerset := by
      ext J; simp [mem_powerset]
    rw [this, card_powerset]
    push_cast
    ring
  rw [← add_sum_erase univ _ (mem_univ (∅ : Finset U))] at h1 ⊢
  simp only [↓reduceIte, empty_subset] at h1 ⊢
  have h2 : ∑ J ∈ univ.erase (∅ : Finset U), (if J = ∅ then (0 : ℝ) else if J ⊆ N k then 1 else 0)
      = ∑ J ∈ univ.erase (∅ : Finset U), (if J ⊆ N k then (1 : ℝ) else 0) :=
    sum_congr rfl fun J hJ => by rw [ite_eq_right (ne_of_mem_erase hJ)]
  rw [h2]
  linarith

/-- `∑_J |ε_J·w| ≤ ∑_k (2^{r_k} − 1)|w_k|`. -/
lemma sum_norm_cJ_le (N : U → Finset U) (ς : U → U → ZMod p) (w : U → ℂ) :
    ∑ J, ‖cJ N ς w J‖ ≤ ∑ k, ((2 : ℝ) ^ (N k).card - 1) * ‖w k‖ := by
  have h1 : ∀ J, ‖cJ N ς w J‖ ≤
      ∑ k, (if J = ∅ then (0 : ℝ) else if J ⊆ N k then 1 else 0) * ‖w k‖ := by
    intro J
    unfold cJ
    by_cases hJ : J = ∅
    · simp [hJ]
    · simp only [hJ, ↓reduceIte]
      refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_epsJ_le N ς J k) (norm_nonneg _)
  calc ∑ J, ‖cJ N ς w J‖
      ≤ ∑ J, ∑ k, (if J = ∅ then (0 : ℝ) else if J ⊆ N k then 1 else 0) * ‖w k‖ :=
        sum_le_sum fun J _ => h1 J
    _ = ∑ k, (∑ J : Finset U, (if J = ∅ then (0 : ℝ) else if J ⊆ N k then 1 else 0)) * ‖w k‖ := by
        rw [sum_comm]
        exact sum_congr rfl fun k _ => by rw [sum_mul]
    _ = ∑ k, ((2 : ℝ) ^ (N k).card - 1) * ‖w k‖ := by
        simp_rw [sum_nonempty_subsets]

omit [DecidableEq U] in
/-- **The Schur test** for the rank-one matrix `(a_k a_l)`:
`(∑_k a_k t_k)² ≤ ρ ∑_k t_k²` if `a_k ∑_l a_l ≤ ρ` for every `k`. -/
lemma schur_sq (a : U → ℝ) (ha : ∀ k, 0 ≤ a k) {ρ : ℝ} (hρ : ∀ k, a k * ∑ l, a l ≤ ρ)
    (t : U → ℝ) : (∑ k, a k * t k) ^ 2 ≤ ρ * ∑ k, t k ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq univ (fun k => Real.sqrt (a k))
    (fun k => Real.sqrt (a k) * t k)
  have e1 : ∀ k, Real.sqrt (a k) * (Real.sqrt (a k) * t k) = a k * t k := fun k => by
    rw [← mul_assoc, Real.mul_self_sqrt (ha k)]
  have e2 : ∀ k, Real.sqrt (a k) ^ 2 = a k := fun k => Real.sq_sqrt (ha k)
  have e3 : ∀ k, (Real.sqrt (a k) * t k) ^ 2 = a k * t k ^ 2 := fun k => by
    rw [mul_pow, e2]
  simp only [e1, e2, e3] at h
  refine h.trans ?_
  calc (∑ l, a l) * ∑ k, a k * t k ^ 2 = ∑ k, (a k * ∑ l, a l) * t k ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
    _ ≤ ∑ k, ρ * t k ^ 2 :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hρ k) (sq_nonneg _)
    _ = ρ * ∑ k, t k ^ 2 := by rw [mul_sum]

/-- The off-diagonal part of a quadratic form: if `|X_{ii'}| ≤ β` for `i ≠ i'`, then
`|c^*Xc − ∑_i X_ii|c_i|²| ≤ β(∑_i|c_i|)²`. -/
lemma qform_offdiag_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (X : ι → ι → ℂ) (c : ι → ℂ)
    {β : ℝ} (hX : ∀ i i', i ≠ i' → ‖X i i'‖ ≤ β) (hβ : 0 ≤ β) :
    ‖qform X c - ∑ i, conj (c i) * X i i * c i‖ ≤ β * (∑ i, ‖c i‖) ^ 2 := by
  have e : qform X c - ∑ i, conj (c i) * X i i * c i =
      ∑ i, ∑ i', if i = i' then 0 else conj (c i) * X i i' * c i' := by
    unfold qform
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    have h : ∀ i', (if i = i' then (0 : ℂ) else conj (c i) * X i i' * c i') =
        conj (c i) * X i i' * c i' - if i = i' then conj (c i) * X i i' * c i' else 0 := by
      intro i'; split_ifs <;> simp
    rw [sum_congr rfl fun i' _ => h i', sum_sub_distrib, sum_ite_eq, ite_eq_left (mem_univ i)]
  rw [e]
  calc ‖∑ i, ∑ i', if i = i' then (0 : ℂ) else conj (c i) * X i i' * c i'‖
      ≤ ∑ i, ∑ i', ‖c i‖ * β * ‖c i'‖ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (sum_le_sum fun i' _ => ?_)
        split_ifs with h
        · rw [norm_zero]; positivity
        · rw [norm_mul, norm_mul, Complex.norm_conj]
          gcongr
          exact hX i i' h
    _ = β * (∑ i, ‖c i‖) ^ 2 := by
        rw [sq, sum_mul_sum, mul_sum]
        exact sum_congr rfl fun i _ => by rw [mul_sum]; exact sum_congr rfl fun i' _ => by ring

/-! ## The remainder (the terms with `E`) -/

omit [Fintype U] [DecidableEq U] in
/-- Cauchy–Schwarz with weights: `∑ ν a b ≤ (∑ ν a²)^{1/2} (∑ ν b²)^{1/2}`. -/
lemma weighted_cs {𝒴 : Type*} [Fintype 𝒴] (ν a b : 𝒴 → ℝ) (hν : ∀ y, 0 ≤ ν y) :
    ∑ y, ν y * (a y * b y) ≤
      Real.sqrt (∑ y, ν y * a y ^ 2) * Real.sqrt (∑ y, ν y * b y ^ 2) := by
  have h := sum_mul_sq_le_sq_mul_sq univ (fun y => Real.sqrt (ν y) * a y)
    (fun y => Real.sqrt (ν y) * b y)
  have e1 : ∀ y, Real.sqrt (ν y) * a y * (Real.sqrt (ν y) * b y) = ν y * (a y * b y) :=
    fun y => by
      have := Real.mul_self_sqrt (hν y)
      calc Real.sqrt (ν y) * a y * (Real.sqrt (ν y) * b y)
          = (Real.sqrt (ν y) * Real.sqrt (ν y)) * (a y * b y) := by ring
        _ = ν y * (a y * b y) := by rw [this]
  have e2 : ∀ y (c : 𝒴 → ℝ), (Real.sqrt (ν y) * c y) ^ 2 = ν y * c y ^ 2 := fun y c => by
    rw [mul_pow, Real.sq_sqrt (hν y)]
  simp only [e1, e2] at h
  rw [← Real.sqrt_mul (sum_nonneg fun y _ => mul_nonneg (hν y) (sq_nonneg _))]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

omit [Fintype U] [DecidableEq U] in
/-- **The terms with `E`**: `|E_ν(⟨Ψ, CE⟩ + ⟨E, CΨ⟩ − ⟨E, CE⟩)| ≤ r(2(ΓΛ)^{1/2} + Γ)s` when
`E_ν‖E‖² ≤ Γs` and `E_ν‖Ψ‖² ≤ Λs`. -/
lemma remainder_bound (hp2 : p ≠ 2) {𝒴 : Type*} [Fintype 𝒴] (ν : 𝒴 → ℝ) (hν0 : ∀ x, 0 ≤ ν x)
    (Ψ E : 𝒴 → ZMod p → ℂ) {Γ Λ s : ℝ} (hΓ0 : 0 ≤ Γ) (hΛ0 : 0 ≤ Λ) (hs : 0 ≤ s)
    (hE : ∑ x, ν x * l2sq (E x) ≤ Γ * s) (hΨ : ∑ x, ν x * l2sq (Ψ x) ≤ Λ * s) :
    ‖∑ x, (ν x : ℂ) * (cform (Ψ x) (E x) + cform (E x) (Ψ x) - cform (E x) (E x))‖ ≤
      rp p * (2 * Real.sqrt (Γ * Λ) + Γ) * s := by
  have hr : 0 ≤ rp p := by unfold rp; positivity
  set a : 𝒴 → ℝ := fun x => Real.sqrt (l2sq (Ψ x)) with ha
  set b : 𝒴 → ℝ := fun x => Real.sqrt (l2sq (E x)) with hb
  have ha2 : ∀ x, a x ^ 2 = l2sq (Ψ x) := fun x => Real.sq_sqrt (PaleyB.l2sq_nonneg' (Ψ x))
  have hb2 : ∀ x, b x ^ 2 = l2sq (E x) := fun x => Real.sq_sqrt (PaleyB.l2sq_nonneg' (E x))
  have hpt : ∀ x, ‖cform (Ψ x) (E x) + cform (E x) (Ψ x) - cform (E x) (E x)‖ ≤
      rp p * (2 * (a x * b x) + b x ^ 2) := by
    intro x
    have h1 := norm_cform_le hp2 (Ψ x) (E x)
    have h2 := norm_cform_le hp2 (E x) (Ψ x)
    have h3 := norm_cform_le hp2 (E x) (E x)
    calc _ ≤ ‖cform (Ψ x) (E x)‖ + ‖cform (E x) (Ψ x)‖ + ‖cform (E x) (E x)‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ rp p * (a x * b x) + rp p * (b x * a x) + rp p * (b x * b x) := by
          gcongr
      _ = rp p * (2 * (a x * b x) + b x ^ 2) := by ring
  have hab : ∑ x, ν x * (a x * b x) ≤ Real.sqrt (Γ * Λ) * s := by
    refine (weighted_cs ν a b hν0).trans ?_
    simp only [ha2, hb2]
    calc Real.sqrt (∑ x, ν x * l2sq (Ψ x)) * Real.sqrt (∑ x, ν x * l2sq (E x))
        ≤ Real.sqrt (Λ * s) * Real.sqrt (Γ * s) :=
          mul_le_mul (Real.sqrt_le_sqrt hΨ) (Real.sqrt_le_sqrt hE) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = Real.sqrt (Γ * Λ) * s := by
          rw [← Real.sqrt_mul (mul_nonneg hΛ0 hs),
            show Λ * s * (Γ * s) = (Γ * Λ) * (s * s) by ring, Real.sqrt_mul (mul_nonneg hΓ0 hΛ0),
            Real.sqrt_mul_self hs]
  have hbb : ∑ x, ν x * b x ^ 2 ≤ Γ * s := by simp only [hb2]; exact hE
  calc ‖∑ x, (ν x : ℂ) * (cform (Ψ x) (E x) + cform (E x) (Ψ x) - cform (E x) (E x))‖
      ≤ ∑ x, ν x * (rp p * (2 * (a x * b x) + b x ^ 2)) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun x _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hν0 x)]
        exact mul_le_mul_of_nonneg_left (hpt x) (hν0 x)
    _ = rp p * (2 * ∑ x, ν x * (a x * b x) + ∑ x, ν x * b x ^ 2) := by
        simp only [mul_add, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun x _ => by ring
    _ ≤ rp p * (2 * (Real.sqrt (Γ * Λ) * s) + Γ * s) := by gcongr
    _ = rp p * (2 * Real.sqrt (Γ * Λ) + Γ) * s := by ring

/-! ## `lem:spec2:paley`(b) -/

/-- The singletons do not contribute: `t_{{j}} = 0` (`lem:spec2:paley`(c), `SJ_singleton`). -/
lemma tJ_singleton (hp2 : p ≠ 2) (ν : (U → ZMod p) → ℝ) (j : U) : tJ ν {j} = 0 := by
  unfold tJ
  simp [SJ_singleton hp2]

lemma gramP_gJf (ν : (U → ZMod p) → ℝ) (J J' : Finset U) :
    gramP ν gJf J J' = ∑ x, (ν x : ℂ) * cform (gJ J x) (gJ J' x) := rfl

lemma gramP_gJf_diag (ν : (U → ZMod p) → ℝ) (J : Finset U) : gramP ν gJf J J = tJ ν J := rfl

/-- **The diagonal terms** `J = J'`: `∑_J \overline{c_J} t_J c_J = ∑_{|J|≥2} t_J |ε_J·w|²`. -/
lemma diag_eq (hp2 : p ≠ 2) (N : U → Finset U) (ς : U → U → ZMod p) (ν : (U → ZMod p) → ℝ)
    (w : U → ℂ) :
    ∑ J, conj (cJ N ς w J) * tJ ν J * cJ N ς w J =
      ∑ J ∈ univ.filter (fun J : Finset U => 2 ≤ J.card),
        tJ ν J * ((‖∑ k, epsJ N ς J k * w k‖ ^ 2 : ℝ) : ℂ) := by
  rw [← sum_filter_add_sum_filter_not univ (fun J : Finset U => 2 ≤ J.card)]
  have h0 : ∑ J ∈ univ.filter (fun J : Finset U => ¬ 2 ≤ J.card),
      conj (cJ N ς w J) * tJ ν J * cJ N ς w J = 0 := by
    refine sum_eq_zero fun J hJ => ?_
    have hc : J.card = 0 ∨ J.card = 1 := by
      have := (mem_filter.mp hJ).2
      omega
    rcases hc with h | h
    · rw [card_eq_zero] at h
      subst h
      simp [cJ]
    · obtain ⟨j, rfl⟩ := card_eq_one.mp h
      rw [tJ_singleton hp2]
      ring
  rw [h0, add_zero]
  refine sum_congr rfl fun J hJ => ?_
  have hJ2 : 2 ≤ J.card := (mem_filter.mp hJ).2
  have hne : J ≠ ∅ := by
    rintro rfl
    simp at hJ2
  unfold cJ
  simp only [hne, ↓reduceIte]
  rw [mul_comm (conj _) _, mul_assoc, Complex.conj_mul']
  push_cast
  ring

/-- **`lem:spec2:paley`(b)**: for `w ∈ ℂ^{U⁺}`,
`|w^*𝐃w − ∑_{|J|≥2} t_J |ε_J·w|²| ≤ r(ε_≠ + ε_rem(Γ_E))|w|²`, with `ε_≠ = rθρ` (`θ = θ_max`,
`ρ = ρ_row`) and `ε_rem(Γ_E) = 2(Γ_E Λ_H)^{1/2} + Γ_E` (`eq:spec:rem`, with
`Λ_H = λ̄(𝐇) + ε_H`).

Hypotheses (all explicit; none is a property of `P` beyond these):
* `hΓ`: `E_ν‖∑_k w_kE_k(·; x)‖² ≤ Γ_E|w|²` (`E_k = pP_k − φ_k`; for instance `Γ_E = Ê²` by
  `lem:spec2:paley`(a), `SpectralC.paley_deviation`);
* `hH`: `w^*H̃w ≤ Λ_H|w|²` (`lem:spec2:gram` and a certified `λ̄(𝐇)`);
* `hpiv`, `hθ`: under `ν`, `ν_j(t | x) ≤ D_j/p` with `D_j − 1 ≤ θ²` (the paper's
  `D_j = R_ν2^{d⁰_j}/(1 − e_{d⁰_j}(p, n))`, from `lem:graphs:vertex`(dens) and the density ratio
  `R_ν`; `condLaw_le_of_density` is the ratio step);
* `hρ`: `(2^{r_k} − 1)∑_l(2^{r_l} − 1) ≤ ρ` for every `k`. -/
theorem paley_b (hp2 : p ≠ 2) (N : U → Finset U) (ς : U → U → ZMod p)
    (ν : (U → ZMod p) → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (P : U → (U → ZMod p) → ZMod p → ℝ) {ΓE ΛH : ℝ} (hΓ0 : 0 ≤ ΓE) (hΛ0 : 0 ≤ ΛH)
    (hΓ : ∀ w : U → ℂ, ∑ x, ν x * l2sq (fun a => ∑ k, w k *
      ((p : ℂ) * (P k x a : ℂ) - starProd N ς k x a)) ≤ ΓE * ∑ k, ‖w k‖ ^ 2)
    (hH : ∀ w : U → ℂ, (qform (gramΓ ν (psiField P)) w).re ≤ ΛH * ∑ k, ‖w k‖ ^ 2)
    (Dj : U → ℝ) (hpiv : ∀ j x t, ν x ≠ 0 → condLaw ν j x t ≤ Dj j / p)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ j, Dj j - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ k, ((2 : ℝ) ^ (N k).card - 1) * ∑ l, ((2 : ℝ) ^ (N l).card - 1) ≤ ρ)
    (w : U → ℂ) :
    ‖qform (gramP ν (psiField P)) w - ∑ J ∈ univ.filter (fun J : Finset U => 2 ≤ J.card),
        tJ ν J * ((‖∑ k, epsJ N ς J k * w k‖ ^ 2 : ℝ) : ℂ)‖ ≤
      rp p * (rp p * θ * ρ + (2 * Real.sqrt (ΓE * ΛH) + ΓE)) * ∑ k, ‖w k‖ ^ 2 := by
  set s := ∑ k, ‖w k‖ ^ 2 with hs
  have hs0 : 0 ≤ s := sum_nonneg fun k _ => sq_nonneg _
  have hr : 0 ≤ rp p := by unfold rp; positivity
  set Ψ : (U → ZMod p) → ZMod p → ℂ := fun x => fieldW (psiField P) w x with hΨ
  set E : (U → ZMod p) → ZMod p → ℂ := fun x a =>
    ∑ k, w k * ((p : ℂ) * (P k x a : ℂ) - starProd N ς k x a) with hE
  set φ : (U → ZMod p) → ZMod p → ℂ := fun x a =>
    ∑ k, w k * (starProd N ς k x a - 1) with hφ
  have hφΨ : ∀ x, φ x = fun a => Ψ x a - E x a := by
    intro x
    funext a
    simp only [hφ, hΨ, hE, fieldW, psiField]
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  have h2 : ∑ x, (ν x : ℂ) * cform (φ x) (φ x) = qform (gramP ν gJf) (cJ N ς w) := by
    rw [qform_gramP_eq]
    refine sum_congr rfl fun x _ => ?_
    have : φ x = fieldW gJf (cJ N ς w) x := by
      funext a
      simp only [hφ, fieldW, gJf]
      exact phi_eq N ς w x a
    rw [this]
  have hsplit : qform (gramP ν (psiField P)) w = ∑ x, (ν x : ℂ) * cform (φ x) (φ x) +
      ∑ x, (ν x : ℂ) * (cform (Ψ x) (E x) + cform (E x) (Ψ x) - cform (E x) (E x)) := by
    rw [qform_gramP_eq ν (psiField P) w, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [hφΨ x, cform_sub_sub]
    ring
  have hrem := remainder_bound hp2 ν hν0 Ψ E hΓ0 hΛ0 hs0 (hΓ w)
    (by rw [← re_qform_gramΓ_eq]; exact hH w)
  have hoff : ‖qform (gramP ν gJf) (cJ N ς w) -
      ∑ J, conj (cJ N ς w J) * gramP ν gJf J J * cJ N ς w J‖ ≤
        rp p * (rp p * θ) * (∑ J, ‖cJ N ς w J‖) ^ 2 :=
    qform_offdiag_bound _ _ (fun J J' hJJ => by
      rw [gramP_gJf]; exact pivot_bound hp2 ν hν0 hν1 Dj hpiv hθ0 hθ hJJ) (by positivity)
  have hdiag : ∑ J, conj (cJ N ς w J) * gramP ν gJf J J * cJ N ς w J =
      ∑ J ∈ univ.filter (fun J : Finset U => 2 ≤ J.card),
        tJ ν J * ((‖∑ k, epsJ N ς J k * w k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [gramP_gJf_diag]
    exact diag_eq hp2 N ς ν w
  have hcount : (∑ J, ‖cJ N ς w J‖) ^ 2 ≤ ρ * s := by
    have h0 : 0 ≤ ∑ J, ‖cJ N ς w J‖ := sum_nonneg fun J _ => norm_nonneg _
    calc (∑ J, ‖cJ N ς w J‖) ^ 2 ≤ (∑ k, ((2 : ℝ) ^ (N k).card - 1) * ‖w k‖) ^ 2 :=
          pow_le_pow_left₀ h0 (sum_norm_cJ_le N ς w) 2
      _ ≤ ρ * s := schur_sq _ (fun k => by
          have : (1 : ℝ) ≤ 2 ^ (N k).card := one_le_pow₀ (by norm_num)
          linarith) hρ _
  rw [hsplit, h2, ← hdiag]
  calc ‖qform (gramP ν gJf) (cJ N ς w) +
        ∑ x, (ν x : ℂ) * (cform (Ψ x) (E x) + cform (E x) (Ψ x) - cform (E x) (E x)) -
        ∑ J, conj (cJ N ς w J) * gramP ν gJf J J * cJ N ς w J‖
      = ‖(qform (gramP ν gJf) (cJ N ς w) -
          ∑ J, conj (cJ N ς w J) * gramP ν gJf J J * cJ N ς w J) +
        ∑ x, (ν x : ℂ) * (cform (Ψ x) (E x) + cform (E x) (Ψ x) - cform (E x) (E x))‖ := by
        congr 1; ring
    _ ≤ rp p * (rp p * θ) * (∑ J, ‖cJ N ς w J‖) ^ 2 +
        rp p * (2 * Real.sqrt (ΓE * ΛH) + ΓE) * s :=
        (norm_add_le _ _).trans (add_le_add hoff hrem)
    _ ≤ rp p * (rp p * θ) * (ρ * s) + rp p * (2 * Real.sqrt (ΓE * ΛH) + ΓE) * s := by
        gcongr
    _ = rp p * (rp p * θ * ρ + (2 * Real.sqrt (ΓE * ΛH) + ΓE)) * s := by ring

/-! ## The pivot densities -/

/-- Sanity check of the pivot hypothesis: conditional probabilities are at most `1`, so `hpiv`
always holds with `D_j = p` (and then `θ² = p − 1` is admissible). -/
lemma condLaw_le_one (ν : (U → ZMod p) → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (j : U) (x : U → ZMod p)
    (t : ZMod p) : condLaw ν j x t ≤ 1 := by
  unfold condLaw
  rw [cmass_erase]
  by_cases h : ∑ s, ν (Function.update x j s) = 0
  · rw [h, div_zero]; exact zero_le_one
  · rw [div_le_one (lt_of_le_of_ne (sum_nonneg fun s _ => hν0 _) (Ne.symm h))]
    exact single_le_sum (f := fun s => ν (Function.update x j s)) (fun s _ => hν0 _) (mem_univ t)

lemma pivot_trivial (ν : (U → ZMod p) → ℝ) (hν0 : ∀ x, 0 ≤ ν x) :
    ∀ j x t, ν x ≠ 0 → condLaw ν j x t ≤ (p : ℝ) / p := by
  intro j x t _
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [div_self hp]
  exact condLaw_le_one ν hν0 j x t

/-- **The density-ratio step** behind `θ_j` (proof of `lem:spec2:paley`(b)): if
`c μ ≤ ν ≤ R c μ` pointwise, then `ν_j(t | x) ≤ R μ_j(t | x)`. With the uniform conditional law
of `lem:graphs:vertex`(dens) under `μ` on at least `p2^{-d⁰_j}(1 − e)` values this gives
`D_j = R_ν2^{d⁰_j}/(1 − e)`. -/
lemma condLaw_le_of_density (μ ν : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) {c R : ℝ}
    (hc : 0 < c) (hR : 0 ≤ R) (hdens : ∀ x, c * μ x ≤ ν x ∧ ν x ≤ R * c * μ x) (j : U)
    (x : U → ZMod p) (t : ZMod p) : condLaw ν j x t ≤ R * condLaw μ j x t := by
  unfold condLaw
  rw [cmass_erase, cmass_erase]
  set mμ := ∑ s, μ (Function.update x j s) with hmμdef
  set mν := ∑ s, ν (Function.update x j s) with hmνdef
  have hmν : c * mμ ≤ mν := by
    rw [hmμdef, hmνdef, mul_sum]
    exact sum_le_sum fun s _ => (hdens _).1
  have hμt : μ (Function.update x j t) ≤ mμ :=
    single_le_sum (f := fun s => μ (Function.update x j s)) (fun s _ => hμ0 _) (mem_univ t)
  by_cases h0 : mμ = 0
  · have hμ' : μ (Function.update x j t) = 0 := le_antisymm (h0 ▸ hμt) (hμ0 _)
    have h1 := (hdens (Function.update x j t)).1
    have h2 := (hdens (Function.update x j t)).2
    rw [hμ', mul_zero] at h1 h2
    rw [le_antisymm h2 h1, zero_div, h0, div_zero, mul_zero]
  · have hmμ : 0 < mμ := lt_of_le_of_ne (sum_nonneg fun s _ => hμ0 _) (Ne.symm h0)
    have hmν' : 0 < mν := lt_of_lt_of_le (mul_pos hc hmμ) hmν
    rw [div_le_iff₀ hmν']
    have hq : 0 ≤ R * (μ (Function.update x j t) / mμ) :=
      mul_nonneg hR (div_nonneg (hμ0 _) hmμ.le)
    calc ν (Function.update x j t) ≤ R * c * μ (Function.update x j t) := (hdens _).2
      _ = R * (μ (Function.update x j t) / mμ) * (c * mμ) := by field_simp
      _ ≤ R * (μ (Function.update x j t) / mμ) * mν := mul_le_mul_of_nonneg_left hmν hq

end Stars

end Sarkozy.SpectralD.PaleyB
