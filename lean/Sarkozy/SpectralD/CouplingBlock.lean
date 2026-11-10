module

public import Sarkozy.SpectralD.PaleyB
public import Sarkozy.Spectral.Coupling
public import Sarkozy.SpectralC.CouplingAdapters

@[expose] public section

/-!
# The coupling block: the matrix `𝐌(ξ)` and Step 1 (`cor:spec2:coupling`)

`paper/sections/14_spectral.tex`, `cor:spec2:coupling`, in WP-K's conventions
(`Sarkozy.SpectralC`) with the Paley part `lem:spec2:paley`(b) of `PaleyB`.

* **Coverable sets** (`def:coupling-model`): `J` with `|J| ≥ 2` is coverable if `G⁺[J]` has no
  isolated vertex (`Coverable`, for an adjacency relation `Adj` of `G⁺`). The Gram sums
  `𝐇^cov = ∑_{J cov} ε_Jε_Jᵀ`, `𝐇^nc = ∑_{J not cov} ε_Jε_Jᵀ` enter through their quadratic forms
  `hcovQ`, `hncQ` (`w^*𝐇^cov w = ∑_{J cov} |ε_J·w|²`), and `hcovM` is `𝐇^cov` as a matrix
  (`qform_hcovM`).
* **The first display** (`coupling_M_first`): for `ξ ≠ 0`,
  `w^*𝐌(ξ)w ≤ (w^*H̃w + [p ≡ 1]w^*𝐇^cov w + (ε_≠ + ε_rem + ε_par)|w|²)/(p − 1)
  ≤ Λ_M|w|²/(p − 1)`, `Λ_M = Λ₊ + ε_H + ε_≠ + ε_rem + ε_par`, `ε_par = [p ≡ 1] ζ̄ Λ_nc`. This is
  WP-A's abstract `Spectral.coupling_M_bound` with its inputs `hM` (`qform_couplingM_re`, the
  definition of `𝐌(ξ)`) and `hδ` (`coupling_delta_bound`, from `lem:spec2:paley`(b), (c):
  `δ = p c_ξ w^*𝐃w`, `|c_ξ| = r`, `pr² = 1`, `|t_J| ≤ r`, `t_J = 0` for `p ≡ 3`, and the
  hypothesis `|t_J| ≤ ζ̄r` on the non-coverable `J` for `p ≡ 1`) now proved.
* **Step 1** (`coupling_step1`): in instance (A) (`Op F_V = ϱ · 𝒫F_V`, `m_p = ϱμ = ν`, `ϱ ≤ R₊`),
  `‖Op F_V‖²_μ ≤ r² (R₊p/(p − 1)) ∑_{ξ≠0} (ĝ^*𝐇⁺ĝ + e|ĝ|²)` from any bound
  `𝐌(ξ) ⪯ (𝐇⁺ + eI)/(p − 1)`; with `coupling_M_first` and `H̃ ⪯ 𝐇 + ε_H I` this is the input
  `hstep1` of WP-A's `Spectral.coupling_block`, `e = ε_H + ε_≠ + ε_rem + ε_par`
  (`coupling_step1_of_first`).

The remaining inputs of `Spectral.coupling_block` were supplied by WP-K
(`SpectralC.CouplingAdapters`: `coupling_hQ_hA`, `coupling_hvnorm`); the identification of the
abstract `‖TF‖²` with `∑_x μ(x)|Op F_V(x)|²` is the realization of the cut operator and is not
done here.

The certified numbers `Λ₊ ≥ λ_max(𝐇⁺)`, `Λ_nc ≥ λ_max(𝐇^nc)`, `λ̄(𝐇)`, `ε_H`, `Γ_E` and the
pivot densities are hypotheses, as in the paper.

New material for this paper.
-/

namespace Sarkozy.SpectralD.PaleyB

open Finset Complex Sarkozy.Characters Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate Matrix

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-! ## Coverable sets and the Gram sums `𝐇^cov`, `𝐇^nc` -/

/-- `J` is **coverable** (`def:coupling-model`): `G⁺[J]` has no isolated vertex. -/
def Coverable (Adj : U → U → Prop) (J : Finset U) : Prop := ∀ j ∈ J, ∃ i ∈ J, i ≠ j ∧ Adj i j

instance (Adj : U → U → Prop) [DecidableRel Adj] : DecidablePred (Coverable Adj) := by
  intro J; unfold Coverable; infer_instance

variable (Adj : U → U → Prop) [DecidableRel Adj]

/-- The coverable sets `|J| ≥ 2`. -/
noncomputable def covSets : Finset (Finset U) :=
  (univ.filter (fun J : Finset U => 2 ≤ J.card)).filter (Coverable Adj)

/-- The non-coverable sets `|J| ≥ 2`. -/
noncomputable def ncSets : Finset (Finset U) :=
  (univ.filter (fun J : Finset U => 2 ≤ J.card)).filter (fun J => ¬ Coverable Adj J)

/-- `w^*𝐇^cov w = ∑_{J cov} |ε_J·w|²`. -/
noncomputable def hcovQ (N : U → Finset U) (ς : U → U → ZMod p) (w : U → ℂ) : ℝ :=
  ∑ J ∈ covSets Adj, ‖∑ k, epsJ N ς J k * w k‖ ^ 2

/-- `w^*𝐇^nc w = ∑_{J not cov} |ε_J·w|²`. -/
noncomputable def hncQ (N : U → Finset U) (ς : U → U → ZMod p) (w : U → ℂ) : ℝ :=
  ∑ J ∈ ncSets Adj, ‖∑ k, epsJ N ς J k * w k‖ ^ 2

/-- `𝐇^cov = ∑_{J cov} ε_Jε_Jᵀ` as a matrix. -/
noncomputable def hcovM (N : U → Finset U) (ς : U → U → ZMod p) (k l : U) : ℂ :=
  ∑ J ∈ covSets Adj, conj (epsJ N ς J k) * epsJ N ς J l

lemma hcovQ_nonneg (N : U → Finset U) (ς : U → U → ZMod p) (w : U → ℂ) :
    0 ≤ hcovQ Adj N ς w := sum_nonneg fun _ _ => sq_nonneg _

lemma hncQ_nonneg (N : U → Finset U) (ς : U → U → ZMod p) (w : U → ℂ) :
    0 ≤ hncQ Adj N ς w := sum_nonneg fun _ _ => sq_nonneg _

/-- `w^*𝐇^cov w = ∑_{J cov} |ε_J·w|²` for the matrix `hcovM`. -/
lemma qform_hcovM (N : U → Finset U) (ς : U → U → ZMod p) (w : U → ℂ) :
    qform (hcovM Adj N ς) w = (hcovQ Adj N ς w : ℂ) := by
  have key : ∀ J, ((‖∑ k, epsJ N ς J k * w k‖ ^ 2 : ℝ) : ℂ) =
      ∑ k, ∑ l, conj (w k) * (conj (epsJ N ς J k) * epsJ N ς J l) * w l := by
    intro J
    rw [Complex.ofReal_pow, ← Complex.conj_mul', map_sum, sum_mul_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    rw [map_mul]
    ring
  calc qform (hcovM Adj N ς) w = ∑ k, ∑ l, ∑ J ∈ covSets Adj,
        conj (w k) * (conj (epsJ N ς J k) * epsJ N ς J l) * w l := by
        unfold qform hcovM; simp only [mul_sum, sum_mul]
    _ = ∑ k, ∑ J ∈ covSets Adj, ∑ l,
        conj (w k) * (conj (epsJ N ς J k) * epsJ N ς J l) * w l :=
        sum_congr rfl fun k _ => sum_comm
    _ = ∑ J ∈ covSets Adj, ∑ k, ∑ l,
        conj (w k) * (conj (epsJ N ς J k) * epsJ N ς J l) * w l := sum_comm
    _ = ∑ J ∈ covSets Adj, ((‖∑ k, epsJ N ς J k * w k‖ ^ 2 : ℝ) : ℂ) :=
        sum_congr rfl fun J _ => (key J).symm
    _ = (hcovQ Adj N ς w : ℂ) := by unfold hcovQ; push_cast; rfl

/-! ## The matrix `𝐌(ξ)` -/

omit Adj [DecidableRel Adj] in
/-- `w^*𝐌(ξ)w = (w^*H̃w + δ)/(p − 1)` with `δ = Re(p c_ξ w^*𝐃w)` (the definition of `𝐌`,
real parts). -/
lemma qform_couplingM_re (ν : (U → ZMod p) → ℝ) (P : U → (U → ZMod p) → ZMod p → ℝ)
    (ξ : ZMod p) (w : U → ℂ) :
    (qform (couplingM ν P ξ) w).re = ((qform (gramΓ ν (psiField P)) w).re +
      ((p : ℂ) * gaussEig ξ * qform (gramP ν (psiField P)) w).re) / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp1' : ((p : ℂ) - 1) ≠ 0 := by
    have : ((p : ℝ) - 1 : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have hlin : qform (couplingM ν P ξ) w = ((((p : ℝ) - 1)⁻¹ : ℝ) : ℂ) *
      (qform (gramΓ ν (psiField P)) w + (p : ℂ) * gaussEig ξ * qform (gramP ν (psiField P)) w) := by
    unfold couplingM qform
    push_cast
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    field_simp
  rw [hlin, Complex.re_ofReal_mul, Complex.add_re, div_eq_inv_mul]

omit Adj [DecidableRel Adj] in
lemma norm_tJ_le (hp2 : p ≠ 2) (ν : (U → ZMod p) → ℝ) (hν0 : ∀ x, 0 ≤ ν x)
    (hν1 : ∑ x, ν x = 1) (J : Finset U) : ‖tJ ν J‖ ≤ rp p := by
  unfold tJ
  calc ‖∑ x, (ν x : ℂ) * SJ J x‖ ≤ ∑ x, ν x * rp p := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun x _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hν0 x)]
        exact mul_le_mul_of_nonneg_left (norm_SJ_le hp2 J x) (hν0 x)
    _ = rp p := by rw [← sum_mul, hν1, one_mul]

omit Adj [DecidableRel Adj] in
lemma tJ_eq_zero_of_three (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (ν : (U → ZMod p) → ℝ)
    (J : Finset U) : tJ ν J = 0 := by
  unfold tJ
  simp [SJ_eq_zero_of_three hp2 hp3]

omit [Fact p.Prime] in
lemma mod_four_cases (hp : p.Prime) (hp2 : p ≠ 2) : p % 4 = 1 ∨ p % 4 = 3 := by
  rcases hp.eq_two_or_odd with h | h
  · exact absurd h hp2
  · omega

/-- **The diagonal Paley terms** (`lem:spec2:paley`(c) and the hypothesis on the non-coverable
sets): `|∑_{|J|≥2} t_J|ε_J·w|²| ≤ [p ≡ 1] r (w^*𝐇^cov w + ζ̄ w^*𝐇^nc w)`. -/
lemma star_sum_bound (hp2 : p ≠ 2) (N : U → Finset U) (ς : U → U → ZMod p)
    (ν : (U → ZMod p) → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) {ζ : ℝ}
    (hζ : p % 4 = 1 → ∀ J : Finset U, 2 ≤ J.card → ¬ Coverable Adj J → ‖tJ ν J‖ ≤ ζ * rp p)
    (w : U → ℂ) :
    ‖∑ J ∈ univ.filter (fun J : Finset U => 2 ≤ J.card),
        tJ ν J * ((‖∑ k, epsJ N ς J k * w k‖ ^ 2 : ℝ) : ℂ)‖ ≤
      (if p % 4 = 1 then (1 : ℝ) else 0) * (rp p * (hcovQ Adj N ς w + ζ * hncQ Adj N ς w)) := by
  rcases mod_four_cases (Fact.out : p.Prime) hp2 with h1 | h3
  · simp only [h1, ↓reduceIte, one_mul]
    rw [← sum_filter_add_sum_filter_not _ (Coverable Adj)]
    have hcov : ‖∑ J ∈ (univ.filter (fun J : Finset U => 2 ≤ J.card)).filter (Coverable Adj),
        tJ ν J * ((‖∑ k, epsJ N ς J k * w k‖ ^ 2 : ℝ) : ℂ)‖ ≤ rp p * hcovQ Adj N ς w := by
      unfold hcovQ covSets
      rw [mul_sum]
      refine (norm_sum_le _ _).trans (sum_le_sum fun J _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right (norm_tJ_le hp2 ν hν0 hν1 J) (sq_nonneg _)
    have hnc : ‖∑ J ∈ (univ.filter (fun J : Finset U => 2 ≤ J.card)).filter
        (fun J => ¬ Coverable Adj J), tJ ν J * ((‖∑ k, epsJ N ς J k * w k‖ ^ 2 : ℝ) : ℂ)‖ ≤
        rp p * (ζ * hncQ Adj N ς w) := by
      unfold hncQ ncSets
      rw [mul_sum, mul_sum]
      refine (norm_sum_le _ _).trans (sum_le_sum fun J hJ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
      have hJ' := mem_filter.mp hJ
      have hJ2 := (mem_filter.mp hJ'.1).2
      have := hζ h1 J hJ2 hJ'.2
      calc ‖tJ ν J‖ * ‖∑ k, epsJ N ς J k * w k‖ ^ 2 ≤
            ζ * rp p * ‖∑ k, epsJ N ς J k * w k‖ ^ 2 :=
            mul_le_mul_of_nonneg_right this (sq_nonneg _)
        _ = rp p * (ζ * ‖∑ k, epsJ N ς J k * w k‖ ^ 2) := by ring
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ rp p * hcovQ Adj N ς w + rp p * (ζ * hncQ Adj N ς w) := add_le_add hcov hnc
      _ = rp p * (hcovQ Adj N ς w + ζ * hncQ Adj N ς w) := by ring
  · have hne : p % 4 ≠ 1 := by omega
    simp only [hne, ↓reduceIte, zero_mul]
    rw [sum_eq_zero fun J _ => by rw [tJ_eq_zero_of_three hp2 h3, zero_mul], norm_zero]

/-- **`hδ` of `Spectral.coupling_M_bound`** (`lem:spec2:paley`(b), (c)): with
`δ = Re(p c_ξ w^*𝐃w)`, `|δ| ≤ [p ≡ 1](w^*𝐇^cov w + ζ̄ w^*𝐇^nc w) + (ε_≠ + ε_rem)|w|²`, where
`ε_≠ = rθρ` and `ε_rem = 2(Γ_EΛ_H)^{1/2} + Γ_E`. -/
theorem coupling_delta_bound (hp2 : p ≠ 2) (N : U → Finset U) (ς : U → U → ZMod p)
    (ν : (U → ZMod p) → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (P : U → (U → ZMod p) → ZMod p → ℝ) {ΓE ΛH : ℝ} (hΓ0 : 0 ≤ ΓE) (hΛ0 : 0 ≤ ΛH)
    (hΓ : ∀ w : U → ℂ, ∑ x, ν x * l2sq (fun a => ∑ k, w k *
      ((p : ℂ) * (P k x a : ℂ) - starProd N ς k x a)) ≤ ΓE * ∑ k, ‖w k‖ ^ 2)
    (hH : ∀ w : U → ℂ, (qform (gramΓ ν (psiField P)) w).re ≤ ΛH * ∑ k, ‖w k‖ ^ 2)
    (Dj : U → ℝ) (hpiv : ∀ j x t, ν x ≠ 0 → condLaw ν j x t ≤ Dj j / p)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ j, Dj j - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ k, ((2 : ℝ) ^ (N k).card - 1) * ∑ l, ((2 : ℝ) ^ (N l).card - 1) ≤ ρ)
    {ζ : ℝ}
    (hζ : p % 4 = 1 → ∀ J : Finset U, 2 ≤ J.card → ¬ Coverable Adj J → ‖tJ ν J‖ ≤ ζ * rp p)
    {ξ : ZMod p} (hξ : ξ ≠ 0) (w : U → ℂ) :
    |((p : ℂ) * gaussEig ξ * qform (gramP ν (psiField P)) w).re| ≤
      (if p % 4 = 1 then (1 : ℝ) else 0) * (hcovQ Adj N ς w + ζ * hncQ Adj N ς w) +
        (rp p * θ * ρ + (2 * Real.sqrt (ΓE * ΛH) + ΓE)) * ∑ k, ‖w k‖ ^ 2 := by
  set qD := qform (gramP ν (psiField P)) w with hqD
  set S := ∑ J ∈ univ.filter (fun J : Finset U => 2 ≤ J.card),
    tJ ν J * ((‖∑ k, epsJ N ς J k * w k‖ ^ 2 : ℝ) : ℂ) with hS
  set ind : ℝ := if p % 4 = 1 then (1 : ℝ) else 0 with hind
  set X := rp p * θ * ρ + (2 * Real.sqrt (ΓE * ΛH) + ΓE) with hX
  set Y := hcovQ Adj N ς w + ζ * hncQ Adj N ς w with hY
  set s := ∑ k, ‖w k‖ ^ 2 with hs
  have hb : ‖qD - S‖ ≤ rp p * X * s :=
    paley_b hp2 N ς ν hν0 hν1 P hΓ0 hΛ0 hΓ hH Dj hpiv hθ0 hθ hρ w
  have hSb : ‖S‖ ≤ ind * (rp p * Y) := star_sum_bound Adj hp2 N ς ν hν0 hν1 hζ w
  have hqDb : ‖qD‖ ≤ rp p * X * s + ind * (rp p * Y) := by
    calc ‖qD‖ = ‖(qD - S) + S‖ := by rw [sub_add_cancel]
      _ ≤ ‖qD - S‖ + ‖S‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hb hSb
  have hr : 0 ≤ rp p := by unfold rp; positivity
  have hnorm : ‖(p : ℂ) * gaussEig ξ * qD‖ = p * rp p * ‖qD‖ := by
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_gaussEig hp2 hξ]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpr : (p : ℝ) * rp p * rp p = 1 := by
    rw [mul_assoc, ← sq, rp_sq, mul_inv_cancel₀ hp0]
  calc |((p : ℂ) * gaussEig ξ * qD).re| ≤ ‖(p : ℂ) * gaussEig ξ * qD‖ := Complex.abs_re_le_norm _
    _ = p * rp p * ‖qD‖ := hnorm
    _ ≤ p * rp p * (rp p * X * s + ind * (rp p * Y)) :=
        mul_le_mul_of_nonneg_left hqDb (by positivity)
    _ = ((p : ℝ) * rp p * rp p) * (ind * Y + X * s) := by ring
    _ = ind * Y + X * s := by rw [hpr, one_mul]

/-- The model matrix `𝐇` (`eq:spec:H`, `SpectralC.modelH`) with complex entries. -/
noncomputable def modelHC (N : U → Finset U) (ς : U → U → ZMod p) (k l : U) : ℂ :=
  (modelH N ς k l : ℂ)

/-- **`cor:spec2:coupling`, the first display**: for `ξ ≠ 0` and every `w`,
`w^*𝐌(ξ)w ≤ (w^*H̃w + [p ≡ 1]w^*𝐇^cov w + (ε_≠ + ε_rem + ε_par)|w|²)/(p − 1)` and
`w^*𝐌(ξ)w ≤ Λ_M|w|²/(p − 1)`, with `ε_≠ = rθρ`, `ε_rem = 2(Γ_E(λ̄ + ε_H))^{1/2} + Γ_E`,
`ε_par = [p ≡ 1]ζ̄Λ_nc` and `Λ_M = Λ₊ + ε_H + ε_≠ + ε_rem + ε_par`.

Hypotheses beyond those of `paley_b` (all certified numbers of the paper): `hHt`
(`H̃ ⪯ 𝐇 + ε_H I`, `lem:spec2:gram`), `hλ` (`λ̄ ≥ λ_max(𝐇)`), `hnc` (`Λ_nc ≥ λ_max(𝐇^nc)`),
`hplus` (`Λ₊ ≥ λ_max(𝐇⁺)`, `𝐇⁺ = 𝐇 + [p ≡ 1]𝐇^cov`), and `hζ` (`|t_J| ≤ ζ̄r` for the
non-coverable `J`, supplied by `subsec:advance:parity`; void for `p ≡ 3`). -/
theorem coupling_M_first (hp2 : p ≠ 2) (N : U → Finset U) (ς : U → U → ZMod p)
    (ν : (U → ZMod p) → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (P : U → (U → ZMod p) → ZMod p → ℝ) {ΓE lamH εH : ℝ} (hΓ0 : 0 ≤ ΓE)
    (hΛ0 : 0 ≤ lamH + εH)
    (hΓ : ∀ w : U → ℂ, ∑ x, ν x * l2sq (fun a => ∑ k, w k *
      ((p : ℂ) * (P k x a : ℂ) - starProd N ς k x a)) ≤ ΓE * ∑ k, ‖w k‖ ^ 2)
    (Dj : U → ℝ) (hpiv : ∀ j x t, ν x ≠ 0 → condLaw ν j x t ≤ Dj j / p)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ j, Dj j - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ k, ((2 : ℝ) ^ (N k).card - 1) * ∑ l, ((2 : ℝ) ^ (N l).card - 1) ≤ ρ)
    {ζ Λnc Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset U, 2 ≤ J.card → ¬ Coverable Adj J → ‖tJ ν J‖ ≤ ζ * rp p)
    (hHt : ∀ w : U → ℂ, (qform (gramΓ ν (psiField P)) w).re ≤
      (qform (modelHC N ς) w).re + εH * ∑ k, ‖w k‖ ^ 2)
    (hlam : ∀ w : U → ℂ, (qform (modelHC N ς) w).re ≤ lamH * ∑ k, ‖w k‖ ^ 2)
    (hnc : ∀ w : U → ℂ, hncQ Adj N ς w ≤ Λnc * ∑ k, ‖w k‖ ^ 2)
    (hplus : ∀ w : U → ℂ, (qform (modelHC N ς) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * hcovQ Adj N ς w ≤ Λp * ∑ k, ‖w k‖ ^ 2)
    {ξ : ZMod p} (hξ : ξ ≠ 0) (w : U → ℂ) :
    (qform (couplingM ν P ξ) w).re ≤ ((qform (gramΓ ν (psiField P)) w).re +
        (if p % 4 = 1 then (1 : ℝ) else 0) * hcovQ Adj N ς w +
        (rp p * θ * ρ + (2 * Real.sqrt (ΓE * (lamH + εH)) + ΓE) +
          (if p % 4 = 1 then (1 : ℝ) else 0) * ζ * Λnc) * ∑ k, ‖w k‖ ^ 2) / ((p : ℝ) - 1) ∧
    (qform (couplingM ν P ξ) w).re ≤ (Λp + εH + rp p * θ * ρ +
        (2 * Real.sqrt (ΓE * (lamH + εH)) + ΓE) +
        (if p % 4 = 1 then (1 : ℝ) else 0) * ζ * Λnc) * (∑ k, ‖w k‖ ^ 2) / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hH : ∀ w : U → ℂ, (qform (gramΓ ν (psiField P)) w).re ≤
      (lamH + εH) * ∑ k, ‖w k‖ ^ 2 := fun w => by
    have := hHt w; have := hlam w; linarith
  have hind : (0 : ℝ) ≤ if p % 4 = 1 then (1 : ℝ) else 0 := by split_ifs <;> norm_num
  exact Sarkozy.Spectral.coupling_M_bound hp1 (qform_couplingM_re ν P ξ w)
    (coupling_delta_bound Adj hp2 N ς ν hν0 hν1 P hΓ0 hΛ0 hΓ hH Dj hpiv hθ0 hθ hρ hζ hξ w)
    hind hζ0 (hnc w) (hHt w) (hplus w)

/-! ## Step 1 -/

omit Adj [DecidableRel Adj] [DecidableEq U] in
/-- WP-A's `Spectral.qform M w w` is `Re(w^*Mw)` (as `SpectralC.spectral_qform_eq`). -/
lemma spectral_qform_eq' (M : U → U → ℂ) (w : U → ℂ) :
    Sarkozy.Spectral.qform (M : Matrix U U ℂ) w w = (qform M w).re := by
  unfold Sarkozy.Spectral.qform qform
  rw [RCLike.re_to_complex]
  congr 1
  rw [dotProduct]
  refine sum_congr rfl fun k _ => ?_
  show (star w) k * (∑ l, M k l * w l) = ∑ l, conj (w k) * M k l * w l
  rw [Pi.star_apply, RCLike.star_def, Finset.mul_sum]
  exact sum_congr rfl fun l _ => by ring

omit Adj [DecidableRel Adj] in
/-- **`cor:spec2:coupling`, Step 1** (instance (A)): if `Op F_V = ϱ · 𝒫F_V` with `0 ≤ ϱ ≤ R₊`,
`m_p = ν = ϱμ` (`lem:coupling-modes`), and `𝐌(ξ) ⪯ (𝐇⁺ + eI)/(p − 1)` for every `ξ ≠ 0`, then
`‖Op F_V‖²_μ ≤ r² (R₊p/(p − 1)) ∑_{ξ≠0} (ĝ^*𝐇⁺ĝ + e|ĝ|²)`: the input `hstep1` of WP-A's
`Spectral.coupling_block`, with `κ = R₊p/(p − 1)`. -/
theorem coupling_step1 {N : U → Finset U} {ς : U → U → ZMod p} {Iplus : Finset (U → ZMod p)}
    {μ : (U → ZMod p) → ℝ} (D : CouplingData p U N ς Iplus μ) (hp2 : p ≠ 2)
    (hμ0 : ∀ x, 0 ≤ μ x) (ϱ : (U → ZMod p) → ℝ) (hϱ0 : ∀ x, 0 ≤ ϱ x) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ x, ϱ x ≤ R) (hνϱ : ∀ x, D.ν x = μ x * ϱ x) (g : U → ZMod p → ℂ)
    (hg : ∀ k, ∑ a, g k a = 0) (OpF : (U → ZMod p) → ℂ)
    (hOp : ∀ x, OpF x = (ϱ x : ℂ) * condField D.P g x) (Hp : Matrix U U ℂ) {e : ℝ}
    (hMb : ∀ ξ : ZMod p, ξ ≠ 0 → ∀ w : U → ℂ, (qform (couplingM D.ν D.P ξ) w).re ≤
      (Sarkozy.Spectral.qform Hp w w + e * Sarkozy.Spectral.sqn w) / ((p : ℝ) - 1)) :
    ∑ x, μ x * ‖OpF x‖ ^ 2 ≤ rp p ^ 2 * (R * p / ((p : ℝ) - 1) *
      ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
        (Sarkozy.Spectral.qform Hp (fun k => fcoef (g k) ξ) (fun k => fcoef (g k) ξ) +
          e * Sarkozy.Spectral.sqn (fun k => fcoef (g k) ξ))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have h1 := instanceA_bound μ ϱ hμ0 hϱ0 hR OpF (condField D.P g) hOp
  have h2 := congrArg Complex.re (D.modes hp2 g hg)
  simp only [Complex.re_sum] at h2
  have h2' : ∑ x, (μ x * ϱ x) * ‖condField D.P g x‖ ^ 2 =
      ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
        (qform (couplingM D.ν D.P ξ) (fun k => fcoef (g k) ξ)).re := by
    rw [← h2]
    refine sum_congr rfl fun x _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re, hνϱ]
  rw [h2'] at h1
  refine h1.trans ?_
  have h3 : ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
      (qform (couplingM D.ν D.P ξ) (fun k => fcoef (g k) ξ)).re ≤
      ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
        (Sarkozy.Spectral.qform Hp (fun k => fcoef (g k) ξ) (fun k => fcoef (g k) ξ) +
          e * Sarkozy.Spectral.sqn (fun k => fcoef (g k) ξ)) / ((p : ℝ) - 1) :=
    sum_le_sum fun ξ hξ => hMb ξ (mem_filter.mp hξ).2 _
  calc R * ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
        (qform (couplingM D.ν D.P ξ) (fun k => fcoef (g k) ξ)).re
      ≤ R * ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
        (Sarkozy.Spectral.qform Hp (fun k => fcoef (g k) ξ) (fun k => fcoef (g k) ξ) +
          e * Sarkozy.Spectral.sqn (fun k => fcoef (g k) ξ)) / ((p : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left h3 hR0
    _ = rp p ^ 2 * (R * p / ((p : ℝ) - 1) *
        ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
          (Sarkozy.Spectral.qform Hp (fun k => fcoef (g k) ξ) (fun k => fcoef (g k) ξ) +
            e * Sarkozy.Spectral.sqn (fun k => fcoef (g k) ξ))) := by
        rw [← sum_div, rp_sq]
        have : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp

/-- `𝐇⁺ = 𝐇 + [p ≡ 1]𝐇^cov` (`def:coupling-model`) as a matrix. -/
noncomputable def hplusM (N : U → Finset U) (ς : U → U → ZMod p) (k l : U) : ℂ :=
  modelHC N ς k l + (((if p % 4 = 1 then (1 : ℝ) else 0) : ℝ) : ℂ) * hcovM Adj N ς k l

lemma qform_hplusM_re (N : U → Finset U) (ς : U → U → ZMod p) (w : U → ℂ) :
    (qform (hplusM Adj N ς) w).re = (qform (modelHC N ς) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * hcovQ Adj N ς w := by
  have h : qform (hplusM Adj N ς) w = qform (modelHC N ς) w +
      (((if p % 4 = 1 then (1 : ℝ) else 0) : ℝ) : ℂ) * qform (hcovM Adj N ς) w := by
    unfold qform hplusM
    simp only [mul_add, add_mul, sum_add_distrib, mul_sum]
    congr 1
    exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
  rw [h, qform_hcovM, Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]

omit Adj [DecidableRel Adj] in
lemma couplingData_sum_ν {N : U → Finset U} {ς : U → U → ZMod p}
    {Iplus : Finset (U → ZMod p)} {μ : (U → ZMod p) → ℝ} (D : CouplingData p U N ς Iplus μ) :
    ∑ x, D.ν x = 1 := by
  rw [← D.ν_total]
  symm
  exact sum_subset (subset_univ _) fun x _ hx => D.ν_supp x hx

/-- **`cor:spec2:coupling`, Step 1 with the first display**: in instance (A),
`‖Op F_V‖²_μ ≤ r²(R₊p/(p − 1))∑_{ξ≠0}(ĝ^*𝐇⁺ĝ + e|ĝ|²)` with
`e = ε_H + ε_≠ + ε_rem + ε_par`. All inputs are those of `coupling_M_first` (for `ν = m_p`,
`P_k` the conditional laws of the cut) and of `coupling_step1`. -/
theorem coupling_step1_of_first {N : U → Finset U} {ς : U → U → ZMod p}
    {Iplus : Finset (U → ZMod p)} {μ : (U → ZMod p) → ℝ} (D : CouplingData p U N ς Iplus μ)
    (hp2 : p ≠ 2) (hμ0 : ∀ x, 0 ≤ μ x) (ϱ : (U → ZMod p) → ℝ) (hϱ0 : ∀ x, 0 ≤ ϱ x) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ x, ϱ x ≤ R) (hνϱ : ∀ x, D.ν x = μ x * ϱ x) (g : U → ZMod p → ℂ)
    (hg : ∀ k, ∑ a, g k a = 0) (OpF : (U → ZMod p) → ℂ)
    (hOp : ∀ x, OpF x = (ϱ x : ℂ) * condField D.P g x)
    {ΓE lamH εH : ℝ} (hΓ0 : 0 ≤ ΓE) (hΛ0 : 0 ≤ lamH + εH)
    (hΓ : ∀ w : U → ℂ, ∑ x, D.ν x * l2sq (fun a => ∑ k, w k *
      ((p : ℂ) * (D.P k x a : ℂ) - starProd N ς k x a)) ≤ ΓE * ∑ k, ‖w k‖ ^ 2)
    (Dj : U → ℝ) (hpiv : ∀ j x t, D.ν x ≠ 0 → condLaw D.ν j x t ≤ Dj j / p)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ j, Dj j - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ k, ((2 : ℝ) ^ (N k).card - 1) * ∑ l, ((2 : ℝ) ^ (N l).card - 1) ≤ ρ)
    {ζ Λnc Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset U, 2 ≤ J.card → ¬ Coverable Adj J → ‖tJ D.ν J‖ ≤ ζ * rp p)
    (hHt : ∀ w : U → ℂ, (qform (gramΓ D.ν (psiField D.P)) w).re ≤
      (qform (modelHC N ς) w).re + εH * ∑ k, ‖w k‖ ^ 2)
    (hlam : ∀ w : U → ℂ, (qform (modelHC N ς) w).re ≤ lamH * ∑ k, ‖w k‖ ^ 2)
    (hnc : ∀ w : U → ℂ, hncQ Adj N ς w ≤ Λnc * ∑ k, ‖w k‖ ^ 2)
    (hplus : ∀ w : U → ℂ, (qform (modelHC N ς) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * hcovQ Adj N ς w ≤ Λp * ∑ k, ‖w k‖ ^ 2) :
    ∑ x, μ x * ‖OpF x‖ ^ 2 ≤ rp p ^ 2 * (R * p / ((p : ℝ) - 1) *
      ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
        (Sarkozy.Spectral.qform (hplusM Adj N ς : Matrix U U ℂ) (fun k => fcoef (g k) ξ)
            (fun k => fcoef (g k) ξ) +
          (εH + rp p * θ * ρ + (2 * Real.sqrt (ΓE * (lamH + εH)) + ΓE) +
            (if p % 4 = 1 then (1 : ℝ) else 0) * ζ * Λnc) *
            Sarkozy.Spectral.sqn (fun k => fcoef (g k) ξ))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine coupling_step1 D hp2 hμ0 ϱ hϱ0 hR0 hR hνϱ g hg OpF hOp _ (fun ξ hξ w => ?_)
  have h1 := (coupling_M_first Adj hp2 N ς D.ν D.ν_nonneg (couplingData_sum_ν D) D.P hΓ0 hΛ0 hΓ Dj hpiv
    hθ0 hθ hρ hζ0 hζ hHt hlam hnc hplus hξ w).1
  refine h1.trans (div_le_div_of_nonneg_right ?_ (by linarith))
  rw [spectral_qform_eq', qform_hplusM_re]
  have h2 := hHt w
  have hs : Sarkozy.Spectral.sqn w = ∑ k, ‖w k‖ ^ 2 := rfl
  rw [hs]
  set ind : ℝ := if p % 4 = 1 then (1 : ℝ) else 0
  set X : ℝ := rp p * θ * ρ + (2 * Real.sqrt (ΓE * (lamH + εH)) + ΓE) + ind * ζ * Λnc
  calc (qform (gramΓ D.ν (psiField D.P)) w).re + ind * hcovQ Adj N ς w + X * ∑ k, ‖w k‖ ^ 2
      ≤ ((qform (modelHC N ς) w).re + εH * ∑ k, ‖w k‖ ^ 2) + ind * hcovQ Adj N ς w +
          X * ∑ k, ‖w k‖ ^ 2 := by linarith
    _ = (qform (modelHC N ς) w).re + ind * hcovQ Adj N ς w +
          (εH + rp p * θ * ρ + (2 * Real.sqrt (ΓE * (lamH + εH)) + ΓE) + ind * ζ * Λnc) *
            ∑ k, ‖w k‖ ^ 2 := by ring

/-- **`cor:spec2:coupling`, `eq:spec:coupling`**, with Step 1 and `Λ₊` discharged: WP-A's
`Spectral.coupling_block` for the cut operator realized as `T` on a space `H`
(`hTF : ‖TF‖² = ∑_x μ(x)|Op F_V(x)|²`), with `𝐇⁺ = hplusM`, `κ = R₊p/(p − 1)`,
`e = ε_H + ε_≠ + ε_rem + ε_par`, `𝐀₀ = azero ς`, `𝐐 = degoneQ` and `hQ`, `hA` from WP-K's
`coupling_hQ_hA` (`lem:spec:degone`(b)). The remaining abstract inputs are the realization
`hTF` and the degree-one test vector `v` of Step 2 (`hv`, `hvT`, `hvnorm`, the latter from
`SpectralC.coupling_hvnorm`). Conclusion:
`‖(I − Π_𝒱) Op F_V‖² ≤ r²∑_{ξ≠0} ĝ^*(𝐇⁺ − 𝐀₀^*𝐀₀ + η_B I)ĝ`,
`η_B = (κ − 1)Λ₊ + κe + ε_VΛ_D² + 2Λ_Dη_Q` (`eq:spec:etaB`). -/
theorem coupling_block_concrete {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (T : H →ₗ[ℂ] H) (V : Submodule ℂ H) (F : H)
    {N : U → Finset U} {ς : U → U → ZMod p}
    {Iplus : Finset (U → ZMod p)} {μ : (U → ZMod p) → ℝ} (D : CouplingData p U N ς Iplus μ)
    (hp2 : p ≠ 2) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (ϱ : (U → ZMod p) → ℝ)
    (hϱ0 : ∀ x, 0 ≤ ϱ x) {R : ℝ} (hR : ∀ x, ϱ x ≤ R) (hνϱ : ∀ x, D.ν x = μ x * ϱ x)
    (g : U → ZMod p → ℂ) (hg : ∀ k, ∑ a, g k a = 0) (OpF : (U → ZMod p) → ℂ)
    (hOp : ∀ x, OpF x = (ϱ x : ℂ) * condField D.P g x)
    (hTF : ‖T F‖ ^ 2 = ∑ x, μ x * ‖OpF x‖ ^ 2)
    {ΓE lamH εH : ℝ} (hΓ0 : 0 ≤ ΓE) (hΛ0 : 0 ≤ lamH + εH)
    (hΓ : ∀ w : U → ℂ, ∑ x, D.ν x * l2sq (fun a => ∑ k, w k *
      ((p : ℂ) * (D.P k x a : ℂ) - starProd N ς k x a)) ≤ ΓE * ∑ k, ‖w k‖ ^ 2)
    (Dj : U → ℝ) (hpiv : ∀ j x t, D.ν x ≠ 0 → condLaw D.ν j x t ≤ Dj j / p)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ j, Dj j - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ k, ((2 : ℝ) ^ (N k).card - 1) * ∑ l, ((2 : ℝ) ^ (N l).card - 1) ≤ ρ)
    {ζ Λnc Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset U, 2 ≤ J.card → ¬ Coverable Adj J → ‖tJ D.ν J‖ ≤ ζ * rp p)
    (hHt : ∀ w : U → ℂ, (qform (gramΓ D.ν (psiField D.P)) w).re ≤
      (qform (modelHC N ς) w).re + εH * ∑ k, ‖w k‖ ^ 2)
    (hlam : ∀ w : U → ℂ, (qform (modelHC N ς) w).re ≤ lamH * ∑ k, ‖w k‖ ^ 2)
    (hnc : ∀ w : U → ℂ, hncQ Adj N ς w ≤ Λnc * ∑ k, ‖w k‖ ^ 2)
    (hplus : ∀ w : U → ℂ, (qform (modelHC N ς) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * hcovQ Adj N ς w ≤ Λp * ∑ k, ‖w k‖ ^ 2)
    (Λj : (U → ZMod p) × (U → ZMod p) → ℝ) {ΛD η εV : ℝ} (hΛD : 0 ≤ ΛD) (hη : 0 ≤ η)
    (hDE : NormLe (deltaE ς) ΛD) (hE : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (errQ Λj ς ξ) η)
    (v : H) (hv : v ∈ V)
    (hvT : @inner ℂ _ _ v (T F) = ((∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
      Sarkozy.Spectral.sqn ((degoneQ Λj ξ : Matrix U U ℂ) *ᵥ (fun k => fcoef (g k) ξ)) : ℝ) : ℂ))
    (hvnorm : ‖v‖ ^ 2 ≤ (1 + εV) * ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
      Sarkozy.Spectral.sqn ((degoneQ Λj ξ : Matrix U U ℂ) *ᵥ (fun k => fcoef (g k) ξ)))
    (hεV : 0 ≤ εV) :
    ‖T F - V.starProjection (T F)‖ ^ 2 ≤
      rp p ^ 2 * ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
        (Sarkozy.Spectral.qform (hplusM Adj N ς : Matrix U U ℂ) (fun k => fcoef (g k) ξ)
            (fun k => fcoef (g k) ξ) -
          Sarkozy.Spectral.sqn ((azero ς ξ : Matrix U U ℂ) *ᵥ (fun k => fcoef (g k) ξ)) +
          ((R * p / ((p : ℝ) - 1) - 1) * Λp +
            R * p / ((p : ℝ) - 1) * (εH + rp p * θ * ρ +
              (2 * Real.sqrt (ΓE * (lamH + εH)) + ΓE) +
              (if p % 4 = 1 then (1 : ℝ) else 0) * ζ * Λnc) +
            εV * ΛD ^ 2 + 2 * ΛD * η) * Sarkozy.Spectral.sqn (fun k => fcoef (g k) ξ)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  -- `R₊ ≥ 1`, since `E_μ ϱ = 1`
  have hR1 : 1 ≤ R := by
    have h1 : ∑ x, D.ν x ≤ ∑ x, μ x * R := sum_le_sum fun x _ => by
      rw [hνϱ]; exact mul_le_mul_of_nonneg_left (hR x) (hμ0 x)
    rw [(couplingData_sum_ν D), ← sum_mul, hμ1, one_mul] at h1
    exact h1
  have hκ : 1 ≤ R * p / ((p : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hΛp : ∀ w : U → ℂ, Sarkozy.Spectral.qform (hplusM Adj N ς : Matrix U U ℂ) w w ≤
      Λp * Sarkozy.Spectral.sqn w := fun w => by
    rw [spectral_qform_eq', qform_hplusM_re]; exact hplus w
  have hstep1 := coupling_step1_of_first Adj D hp2 hμ0 ϱ hϱ0 (by linarith) hR hνϱ g hg OpF hOp
    hΓ0 hΛ0 hΓ Dj hpiv hθ0 hθ hρ hζ0 hζ hHt hlam hnc hplus
  rw [← hTF] at hstep1
  obtain ⟨hQ, hA⟩ := coupling_hQ_hA hp2 Λj ς hΛD hη hDE (univ.filter (fun ξ : ZMod p => ξ ≠ 0))
    (fun ξ hξ => (mem_filter.mp hξ).2) (fun ξ hξ => hE ξ (mem_filter.mp hξ).2)
    (fun ξ k => fcoef (g k) ξ)
  exact Sarkozy.Spectral.coupling_block T V F (univ.filter (fun ξ : ZMod p => ξ ≠ 0))
    (fun ξ k => fcoef (g k) ξ) (hplusM Adj N ς : Matrix U U ℂ) (fun ξ => azero ς ξ)
    (fun ξ => degoneQ Λj ξ) hκ hΛp hstep1 v hv hvT hvnorm hQ hA hεV hΛD hη

end Sarkozy.SpectralD.PaleyB
