module

public import Sarkozy.SpectralC.All

@[expose] public section

/-!
# Disjoint supports (`lem:general-star`(e), first claim)

`paper/sections/14_spectral.tex`, `lem:general-star`(e). In the setting of
`subsec:spec:actual-stars` (`p ≡ 3 (mod 4)`, `μ` an `Aff_p`-invariant law on injective labellings
`x : U → 𝔽_p`, `W_S h = kerMap (starKer S) h`), let `ρ_S` bound the maximal correlation
(`def:prelim:maxcorr`) of `x_S` and `x_{U∖S}`. Then for every support `T` disjoint from `S` and
mean-zero `h, h'`, `|⟨W_S h, W_T h'⟩_μ| ≤ ρ_S q ‖h‖ ‖h'‖` (`disjoint_star_bound`), that is
`‖(W_S/r)^*(W_T/r)‖ ≤ ρ_S`; in operator form `‖W_S^*W_T h'‖² ≤ (ρ_S q)² ‖h'‖²`
(`disjoint_star_gram`).

**The maximal-correlation hypothesis.** `CorrBound μ A B ρ` is the inequality form
`|E_μ \overline{F} G| ≤ ρ ‖F‖_μ ‖G‖_μ` for complex `F` depending only on `x_A`, `G` depending only
on `x_B`, both of `μ`-mean zero. For `ρ ≥ 0` it is implied by `ρ(x_A; x_B) ≤ ρ` in the real sense
of `def:prelim:maxcorr` (`Peyre.maxCorr`): this complexification step is
`corrBound_of_maxCorr_le` in `OverlapBridge`. It always holds with `ρ = 1` (`corrBound_one`,
Cauchy–Schwarz), so the hypothesis is satisfiable.

Ingredients: `W_S h` is a function of `x_S` (`dependsOn_starMap`), has `μ`-mean zero
(`starMap_mean_zero`, from `kerMap_orth_invariant`), and `‖W_S h‖²_μ ≤ q‖h‖²`
(`norm_starMap_sq_le`, from `star_diagonal`, i.e. `lem:general-star`(a)).

New material for this paper.
-/

namespace Sarkozy.SpectralD.Overlap

open Finset Complex Sarkozy.Characters Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- `F` depends only on the coordinates in `A`. -/
def DependsOn (A : Finset U) (F : (U → ZMod p) → ℂ) : Prop :=
  ∀ x x' : U → ZMod p, (∀ i ∈ A, x i = x' i) → F x = F x'

/-- **Maximal correlation, inequality form** (`def:prelim:maxcorr`, complex functions):
`|E_μ \overline{F} G| ≤ ρ ‖F‖_μ ‖G‖_μ` for `F` a function of `x_A` and `G` a function of `x_B`,
both of `μ`-mean zero. -/
def CorrBound (μ : (U → ZMod p) → ℝ) (A B : Finset U) (ρ : ℝ) : Prop :=
  ∀ F G : (U → ZMod p) → ℂ, DependsOn A F → DependsOn B G →
    ∑ x, (μ x : ℂ) * F x = 0 → ∑ x, (μ x : ℂ) * G x = 0 →
    ‖∑ x, (μ x : ℂ) * (conj (F x) * G x)‖ ≤
      ρ * Real.sqrt (∑ x, μ x * ‖F x‖ ^ 2) * Real.sqrt (∑ x, μ x * ‖G x‖ ^ 2)

omit [Fact p.Prime] [Fintype U] [DecidableEq U] in
lemma dependsOn_mono {A B : Finset U} (hAB : A ⊆ B) {F : (U → ZMod p) → ℂ}
    (hF : DependsOn A F) : DependsOn B F :=
  fun x x' h => hF x x' fun i hi => h i (hAB hi)

omit [Fintype U] [DecidableEq U] in
/-- `W_S h` is a function of `x_S`. -/
lemma dependsOn_starMap (S : Finset U) (h : ZMod p → ℂ) :
    DependsOn S (kerMap (starKer S) h) := by
  intro x x' hxx'
  unfold kerMap starKer
  refine sum_congr rfl fun a _ => ?_
  rw [prod_congr rfl fun j hj => by rw [hxx' j hj]]

/-- **Sanity check** (rule 9): the hypothesis `CorrBound` always holds with `ρ = 1`
(Cauchy–Schwarz in `L²(μ)`). -/
theorem corrBound_one (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (A B : Finset U) :
    CorrBound μ A B 1 := by
  intro F G _ _ _ _
  rw [one_mul]
  calc ‖∑ x, (μ x : ℂ) * (conj (F x) * G x)‖
      ≤ ∑ x, (Real.sqrt (μ x) * ‖F x‖) * (Real.sqrt (μ x) * ‖G x‖) := by
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun x _ => ?_))
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
          Real.norm_of_nonneg (hμ0 x)]
        rw [show Real.sqrt (μ x) * ‖F x‖ * (Real.sqrt (μ x) * ‖G x‖) =
          (Real.sqrt (μ x) * Real.sqrt (μ x)) * (‖F x‖ * ‖G x‖) by ring,
          Real.mul_self_sqrt (hμ0 x)]
    _ ≤ Real.sqrt (∑ x, (Real.sqrt (μ x) * ‖F x‖) ^ 2) *
          Real.sqrt (∑ x, (Real.sqrt (μ x) * ‖G x‖) ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (∑ x, μ x * ‖F x‖ ^ 2) * Real.sqrt (∑ x, μ x * ‖G x‖ ^ 2) := by
        congr 2 <;> refine sum_congr rfl fun x _ => ?_ <;>
          rw [mul_pow, Real.sq_sqrt (hμ0 x)]

/-- `W_S h` has `μ`-mean zero for mean-zero `h` (the opening claim of `lem:general-star`). -/
lemma starMap_mean_zero (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (S : Finset U) (h : ZMod p → ℂ) (hh : meanC h = 0) :
    ∑ x, (μ x : ℂ) * kerMap (starKer S) h x = 0 := by
  have h0 := kerMap_orth_invariant (labAction μ hinv) (starKer S)
    (fun s c hs hsq h' x => starKer_cov S s c hs hsq h' x) (fun _ => (1 : ℂ))
    (fun _ _ => rfl) h hh
  simpa using h0

/-- `‖W_S h‖²_μ ≤ q ‖h‖²` on `L²_0` (`lem:general-star`(a); the empty support gives `0`). -/
lemma norm_starMap_sq_le (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l) (S : Finset U)
    (h : ZMod p → ℂ) (hh : meanC h = 0) :
    ∑ x, μ x * ‖kerMap (starKer S) h x‖ ^ 2 ≤ (p : ℝ)⁻¹ * l2sq h := by
  have hl := l2sq_nonneg h
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    have h0 : ∀ x, kerMap (starKer (∅ : Finset U)) h x = 0 := by
      intro x
      unfold kerMap starKer
      simp only [prod_empty, mul_one]
      unfold meanC at hh
      push_cast
      rw [← mul_sum]
      exact hh
    simp only [h0, norm_zero]
    have : ∑ x : U → ZMod p, μ x * (0 : ℝ) ^ 2 = 0 := by simp
    rw [this]
    positivity
  · obtain ⟨hT, hle⟩ := star_diagonal hp2 hp3 μ hμ0 hμ1 hinv hinj S
    set c := (p : ℝ)⁻¹ * (1 - (S.card : ℝ) * (p : ℝ)⁻¹ - ∑ x, μ x * starMean S x ^ 2) /
      (1 - (p : ℝ)⁻¹)
    have h1 := norm_kerMap_sq μ (starKer S) h
    have h2 : gramOp μ (starKer S) (starKer S) h = fun a => (c : ℂ) * h a := funext (hT h hh)
    rw [h2] at h1
    have h3 : ip h (fun a => (c : ℂ) * h a) = (c : ℂ) * ip h h := by
      unfold ip
      have e : ∑ a, conj (h a) * ((c : ℂ) * h a) = (c : ℂ) * ∑ a, conj (h a) * h a := by
        rw [mul_sum]; exact sum_congr rfl fun a _ => by ring
      rw [e]; ring
    rw [h3, ← l2sq_eq_re_ip] at h1
    have h4 : ∑ x, μ x * ‖kerMap (starKer S) h x‖ ^ 2 = c * l2sq h := by exact_mod_cast h1
    rw [h4]
    exact mul_le_mul_of_nonneg_right (hle hS) hl

/-- From a bilinear bound to an operator bound: if `|⟨u, u⟩| ≤ c ‖u‖ ‖g‖` then `‖u‖² ≤ c²‖g‖²`. -/
lemma l2sq_le_of_self_ip {u g : ZMod p → ℂ} {c : ℝ}
    (hb : ‖ip u u‖ ≤ c * Real.sqrt (l2sq u) * Real.sqrt (l2sq g)) :
    l2sq u ≤ c ^ 2 * l2sq g := by
  have hu := l2sq_nonneg u
  have hg := l2sq_nonneg g
  have e : ‖ip u u‖ = l2sq u := by
    rw [← l2sq_eq_re_ip, Complex.norm_real, Real.norm_of_nonneg hu]
  rw [e] at hb
  have hsu := Real.sq_sqrt hu
  have hsg := Real.sq_sqrt hg
  have hsu0 := Real.sqrt_nonneg (l2sq u)
  have hsg0 := Real.sqrt_nonneg (l2sq g)
  rcases hsu0.eq_or_lt with h0 | hpos
  · have hz : l2sq u = 0 := by rw [← hsu, ← h0]; ring
    rw [hz]; positivity
  · have h5 : Real.sqrt (l2sq u) ≤ c * Real.sqrt (l2sq g) := by
      have : Real.sqrt (l2sq u) * Real.sqrt (l2sq u) ≤
          (c * Real.sqrt (l2sq g)) * Real.sqrt (l2sq u) := by
        rw [← sq, hsu]; linarith
      exact le_of_mul_le_mul_right this hpos
    have h6 := pow_le_pow_left₀ hsu0 h5 2
    rw [hsu, mul_pow, hsg] at h6
    exact h6

/-- `E(Ch) = 0`. -/
lemma meanC_gaussOp (hp2 : p ≠ 2) (h : ZMod p → ℂ) : meanC (gaussOp h) = 0 := by
  unfold meanC gaussOp
  have : ∑ a : ZMod p, ∑ b : ZMod p, chiC p (b - a) * h b = 0 := by
    rw [sum_comm]
    refine sum_eq_zero fun b _ => ?_
    rw [← sum_mul]
    have e : ∑ a : ZMod p, chiC p (b - a) = ∑ t : ZMod p, chiC p t :=
      Fintype.sum_equiv (Equiv.subLeft b) _ _ (fun a => rfl)
    rw [e, sum_chiC hp2, zero_mul]
  rw [← mul_sum, this, mul_zero, mul_zero]

/-- The Gram `W_S^*W_T` maps `L²_0` into `L²_0` (any odd `p`). -/
lemma meanC_gramOp_star (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (S T : Finset U) (h : ZMod p → ℂ) (hh : meanC h = 0) :
    meanC (gramOp μ (starKer S) (starKer T) h) = 0 := by
  have hT := (star_cross hp2 μ hinv S T).1 h hh
  rw [show gramOp μ (starKer S) (starKer T) h = fun a => _ from funext hT]
  have hg := meanC_gaussOp hp2 h
  unfold meanC at hh hg ⊢
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, mul_add]
  have e1 : (p : ℂ)⁻¹ * (((((p : ℝ)⁻¹ * (starA μ S T - starC μ S T) / (1 - (p : ℝ)⁻¹) : ℝ)) : ℂ) *
      ∑ a, h a) = ((((p : ℝ)⁻¹ * (starA μ S T - starC μ S T) / (1 - (p : ℝ)⁻¹) : ℝ)) : ℂ) *
      ((p : ℂ)⁻¹ * ∑ a, h a) := by ring
  have e2 : (p : ℂ)⁻¹ * ((((starB μ S T / (1 - (p : ℝ)⁻¹) : ℝ)) : ℂ) * ∑ a, gaussOp h a) =
      ((((starB μ S T / (1 - (p : ℝ)⁻¹) : ℝ)) : ℂ)) * ((p : ℂ)⁻¹ * ∑ a, gaussOp h a) := by ring
  rw [e1, e2, hh, hg, mul_zero, mul_zero, add_zero]

/-- **`lem:general-star`(e), disjoint supports** (`p ≡ 3 (mod 4)`): if `ρ ≥ 0` bounds the maximal
correlation of `x_S` and `x_{U∖S}` (hypothesis `hρ`, `def:prelim:maxcorr` in inequality form) and
`T` is disjoint from `S`, then `|⟨W_S h, W_T h'⟩_μ| ≤ ρ q ‖h‖ ‖h'‖` on `L²_0`, that is
`‖(W_S/r)^*(W_T/r)‖ ≤ ρ`. -/
theorem disjoint_star_bound (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {S T : Finset U} (hST : Disjoint S T) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : CorrBound μ S (univ \ S) ρ)
    (h h' : ZMod p → ℂ) (hh : meanC h = 0) (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (starKer S) h x) * kerMap (starKer T) h' x)‖ ≤
      ρ * (p : ℝ)⁻¹ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  have hTS : T ⊆ univ \ S := fun i hi =>
    mem_sdiff.mpr ⟨mem_univ i, fun hiS => disjoint_left.mp hST hiS hi⟩
  have hb := hρ (kerMap (starKer S) h) (kerMap (starKer T) h') (dependsOn_starMap S h)
    (dependsOn_mono hTS (dependsOn_starMap T h')) (starMap_mean_zero μ hinv S h hh)
    (starMap_mean_zero μ hinv T h' hh')
  refine hb.trans ?_
  have hA := norm_starMap_sq_le hp2 hp3 μ hμ0 hμ1 hinv hinj S h hh
  have hB := norm_starMap_sq_le hp2 hp3 μ hμ0 hμ1 hinv hinj T h' hh'
  have hq : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hsA : Real.sqrt (∑ x, μ x * ‖kerMap (starKer S) h x‖ ^ 2) ≤
      Real.sqrt (p : ℝ)⁻¹ * Real.sqrt (l2sq h) := by
    rw [← Real.sqrt_mul hq]; exact Real.sqrt_le_sqrt hA
  have hsB : Real.sqrt (∑ x, μ x * ‖kerMap (starKer T) h' x‖ ^ 2) ≤
      Real.sqrt (p : ℝ)⁻¹ * Real.sqrt (l2sq h') := by
    rw [← Real.sqrt_mul hq]; exact Real.sqrt_le_sqrt hB
  have hqq : Real.sqrt (p : ℝ)⁻¹ * Real.sqrt (p : ℝ)⁻¹ = (p : ℝ)⁻¹ := Real.mul_self_sqrt hq
  calc ρ * Real.sqrt (∑ x, μ x * ‖kerMap (starKer S) h x‖ ^ 2) *
        Real.sqrt (∑ x, μ x * ‖kerMap (starKer T) h' x‖ ^ 2)
      ≤ ρ * (Real.sqrt (p : ℝ)⁻¹ * Real.sqrt (l2sq h)) *
          (Real.sqrt (p : ℝ)⁻¹ * Real.sqrt (l2sq h')) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hsA hρ0) hsB (Real.sqrt_nonneg _)
        exact mul_nonneg hρ0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = ρ * (Real.sqrt (p : ℝ)⁻¹ * Real.sqrt (p : ℝ)⁻¹) * Real.sqrt (l2sq h) *
          Real.sqrt (l2sq h') := by ring
    _ = ρ * (p : ℝ)⁻¹ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by rw [hqq]

/-- **`lem:general-star`(e), disjoint supports, operator form** (`p ≡ 3 (mod 4)`): under the
hypotheses of `disjoint_star_bound`, `‖W_S^*W_T h'‖² ≤ (ρ q)² ‖h'‖²` on `L²_0`. -/
theorem disjoint_star_gram (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {S T : Finset U} (hST : Disjoint S T) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : CorrBound μ S (univ \ S) ρ)
    (h' : ZMod p → ℂ) (hh' : meanC h' = 0) :
    l2sq (gramOp μ (starKer S) (starKer T) h') ≤ (ρ * (p : ℝ)⁻¹) ^ 2 * l2sq h' := by
  set u := gramOp μ (starKer S) (starKer T) h' with hu
  have hu0 : meanC u = 0 := meanC_gramOp_star hp2 μ hinv S T h' hh'
  apply l2sq_le_of_self_ip
  have e := ip_kerMap μ (starKer S) (starKer T) u h'
  rw [← hu] at e
  rw [← e]
  exact disjoint_star_bound hp2 hp3 μ hμ0 hμ1 hinv hinj hST hρ0 hρ u h' hu0 hh'

end Sarkozy.SpectralD.Overlap
