module

public import Sarkozy.SpectralD.CxStepTwo

@[expose] public section

/-!
# The degree-one inputs of Route A in the complex realization (`lem:spec:degone`)

`paper/sections/14_spectral.tex`, `lem:spec:degone` and the Route A inputs of
`thm:spectral-criterion` (WP-A's `Sarkozy.Spectral.RouteAInputs`). In the complex realization
of `Sarkozy.SpectralD.CxRealization` (`H = EuclideanSpace ℂ (U → 𝔽_p)`, `T = kernelOpC μ K`,
`one = l2MapC μ 1`, `V = degSpace μ`, `coef = degCoef μ`, `Ξ = 𝔽_p`, `n = U`, `r = rp p`), this
file proves the degree-one fields of `RouteAInputs`:

* `cx_norm_one` (`‖1‖_μ = 1`), `cx_rho_mean` (`⟪1, Op 1⟫ = E_λ 1 = 1`);
* `cx_V_perp_one` (`⟪1, v⟫ = 0` on `𝒱`: the one-vertex marginals of `μ` are uniform) and
  `cx_rho_V` (`⟪1, Op v⟫ = E_λ v(x') = 0` on `𝒱`: those of the second half of `λ` are);
* `cx_degone_norm` (`lem:spec:degone`(c): `(1 − ε_V)∑_ξ|ĝ(ξ)|² ≤ ‖v‖²`, from WP-K's
  `degone_equiv_bounds`);
* `inner_degMap_kernelOpC` (`lem:spec:degone`(a) in the realization:
  `⟪v, Op v⟫ = ∑_{ξ≠0} ĝ(ξ)^*𝐐(ξ)ĝ(ξ)`, from WP-K's `degone_bilinear`), and
  `cx_degone_lower`, `cx_degone_upper` (`lem:spec:degone`(b):
  `r∑_ξ(ĝ^*𝐀₀(ξ)ĝ ∓ η_Q|ĝ|²)` bounds `re⟪v, Op v⟫`, since `𝐐 = r(𝐀₀ + E_Q)` and
  `‖E_Q(ξ)‖ ≤ η_Q`);
* `cx_degone_fields`: these together with `symm`, in the form of the fields of `RouteAInputs`.

The quadratic form `qA ξ x = re(x^*𝐀₀(ξ)x)` is written with WP-K's `SpectralC.qform`:
`qA ξ x = (qform (azero ς ξ) x).re`.

**Hypotheses** (explicit): the half law `μ` (`hμ0`, `hμ1`, `hinv`: invariance under
`affLab s c`, `s` a nonzero square; `hinj`); a real symmetric kernel `K` whose cut law
`λ(x, x') = μ(x)μ(x')K(x, x')` (`cutLaw`) has total mass one (`hΛ1`), is invariant under the
diagonal action of `Aff_p` (`hΛinv`) and has `x_k ≠ x'_l` almost surely (`hΛinj`) — exactly the
hypotheses of WP-K's `degone_bilinear` (`lem:spec:cutkernel` for the cut); the bounds `hN`
(`‖𝐍(ξ) − I‖ ≤ ε_V`, `eq:spec:epsV`) and `hE` (`‖E_Q(ξ)‖ ≤ η_Q`, `eq:spec:Azero`), which WP-K's
`degoneN_sub_one` and `degone_block` supply from the certified numbers.

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate InnerProductSpace

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-! ## Uniform marginals -/

omit [Fintype U] [DecidableEq U] in
lemma isSquare_one_cx : IsSquare (1 : ZMod p) := ⟨1, by ring⟩

omit [Fintype U] [DecidableEq U] in
/-- A probability vector invariant under a free family of shifts has uniform marginal: the mean
of a mean-zero function of the shifted coordinate vanishes. -/
lemma sum_marginal_zero {Y : Type*} [Fintype Y] (ν : Y → ℝ) (σ : ZMod p → Y → Y)
    (hσ : ∀ c, Function.Bijective (σ c)) (hνσ : ∀ c y, ν (σ c y) = ν y) (π : Y → ZMod p)
    (hπ : ∀ c y, π (σ c y) = π y + c) (f : ZMod p → ℂ) (hf : ∑ a, f a = 0) :
    ∑ y, (ν y : ℂ) * f (π y) = 0 := by
  have hshift : ∀ c, ∑ y, (ν y : ℂ) * f (π y) = ∑ y, (ν y : ℂ) * f (π y + c) := by
    intro c
    rw [← (hσ c).sum_comp (fun y => (ν y : ℂ) * f (π y))]
    refine sum_congr rfl fun y _ => ?_
    rw [hνσ c y, hπ c y]
  have hsum : (p : ℂ) * ∑ y, (ν y : ℂ) * f (π y) = 0 := by
    have h1 : (p : ℂ) * ∑ y, (ν y : ℂ) * f (π y) =
        ∑ c : ZMod p, ∑ y, (ν y : ℂ) * f (π y + c) := by
      rw [← sum_congr rfl fun c _ => hshift c, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    rw [h1, sum_comm]
    refine sum_eq_zero fun y _ => ?_
    rw [← mul_sum]
    have h2 : ∑ c : ZMod p, f (π y + c) = ∑ a, f a :=
      Fintype.sum_equiv (Equiv.addLeft (π y)) _ _ (fun c => rfl)
    rw [h2, hf, mul_zero]
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact (mul_eq_zero.mp hsum).resolve_left hp

/-- The one-vertex marginals of `μ` are uniform: `E_μ f(x_j) = 0` for mean-zero `f`. -/
lemma sum_mu_comp_zero (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (j : U) (f : ZMod p → ℂ) (hf : ∑ a, f a = 0) : ∑ x, (μ x : ℂ) * f (x j) = 0 :=
  sum_marginal_zero μ (fun c => affLab 1 c) (fun c => affLab_bijective one_ne_zero c)
    (fun c x => hinv 1 c x one_ne_zero isSquare_one_cx) (fun x => x j)
    (fun c x => by simp [affLab]) f hf

/-- The one-vertex marginals of the second half of the cut law are uniform. -/
lemma sum_cutLaw_comp_zero (Λ : (U → ZMod p) × (U → ZMod p) → ℝ)
    (hΛinv : ∀ (s c : ZMod p) (z : (U → ZMod p) × (U → ZMod p)), s ≠ 0 → IsSquare s →
      Λ (affLab s c z.1, affLab s c z.2) = Λ z)
    (l : U) (f : ZMod p → ℂ) (hf : ∑ a, f a = 0) : ∑ z, (Λ z : ℂ) * f (z.2 l) = 0 :=
  sum_marginal_zero Λ (fun c z => (affLab 1 c z.1, affLab 1 c z.2))
    (fun c => (affLab_bijective one_ne_zero c).prodMap (affLab_bijective one_ne_zero c))
    (fun c z => hΛinv 1 c z one_ne_zero isSquare_one_cx) (fun z => z.2 l)
    (fun c z => by simp [affLab]) f hf

/-! ## The constants -/

/-- **`norm_one`**: `‖1‖_μ = 1`. -/
theorem cx_norm_one (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) :
    ‖l2MapC μ (fun _ : U → ZMod p => (1 : ℂ))‖ = 1 := by
  have h := norm_l2MapC_sq μ hμ0 (fun _ : U → ZMod p => (1 : ℂ))
  simp only [norm_one, one_pow, mul_one, hμ1] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

/-- **`rho_mean`**: `⟪1, Op 1⟫ = E_λ 1 = 1`. -/
theorem cx_rho_mean (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (K : (U → ZMod p) → (U → ZMod p) → ℝ) (hΛ1 : ∑ z, cutLaw μ K z = 1) :
    ⟪l2MapC μ (fun _ : U → ZMod p => (1 : ℂ)),
      kernelOpC μ K (l2MapC μ (fun _ : U → ZMod p => (1 : ℂ)))⟫_ℂ = 1 := by
  rw [kernelOpC_l2MapC μ hμ0, inner_l2MapC μ hμ0]
  unfold opFun
  have e : ∑ x, (μ x : ℂ) * (conj (1 : ℂ) * ∑ x', (μ x' : ℂ) * (K x x' : ℂ) * 1) =
      ∑ z, (cutLaw μ K z : ℂ) := by
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun x _ => ?_
    rw [map_one, one_mul, mul_sum]
    refine sum_congr rfl fun x' _ => ?_
    unfold cutLaw
    push_cast
    ring
  rw [e]
  exact_mod_cast hΛ1

/-- `⟪1, F_V⟫_μ = E_μ F_V = 0` for `F_V = ∑_k g_k(x_k)` with mean-zero `g_k`. -/
lemma inner_one_degMap (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (g : U → ZMod p → ℂ) (hg : ∀ k, ∑ a, g k a = 0) :
    ⟪l2MapC μ (fun _ : U → ZMod p => (1 : ℂ)), degMap μ g⟫_ℂ = 0 := by
  rw [degMap_apply, inner_l2MapC μ hμ0]
  unfold degFun
  simp only [map_one, one_mul, mul_sum]
  rw [sum_comm]
  exact sum_eq_zero fun j _ => sum_mu_comp_zero μ hinv j _ (hg j)

/-- **`V_perp_one`**: `⟪1, v⟫ = 0` on the degree-one space. -/
theorem cx_V_perp_one (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x) :
    ∀ v ∈ degSpace μ, ⟪l2MapC μ (fun _ : U → ZMod p => (1 : ℂ)), v⟫_ℂ = 0 := by
  intro v hv
  obtain ⟨hg, hvg⟩ := degRep_spec μ hv
  have h := inner_one_degMap μ hμ0 hinv (degRep μ v) hg
  rwa [hvg] at h

/-- `⟪1, Op F_V⟫ = E_λ F_V(x') = 0` for mean-zero `g_k`. -/
lemma inner_one_kernelOpC_degMap (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (K : (U → ZMod p) → (U → ZMod p) → ℝ)
    (hΛinv : ∀ (s c : ZMod p) (z : (U → ZMod p) × (U → ZMod p)), s ≠ 0 → IsSquare s →
      cutLaw μ K (affLab s c z.1, affLab s c z.2) = cutLaw μ K z)
    (g : U → ZMod p → ℂ) (hg : ∀ k, ∑ a, g k a = 0) :
    ⟪l2MapC μ (fun _ : U → ZMod p => (1 : ℂ)), kernelOpC μ K (degMap μ g)⟫_ℂ = 0 := by
  rw [degMap_apply, kernelOpC_l2MapC μ hμ0, inner_l2MapC μ hμ0]
  unfold opFun degFun
  have e : ∑ x, (μ x : ℂ) * (conj (1 : ℂ) * ∑ x', (μ x' : ℂ) * (K x x' : ℂ) * ∑ l, g l (x' l)) =
      ∑ l, ∑ z, (cutLaw μ K z : ℂ) * g l (z.2 l) := by
    have e1 : ∀ l, ∑ z, (cutLaw μ K z : ℂ) * g l (z.2 l) =
        ∑ x, ∑ x', (μ x : ℂ) * ((μ x' : ℂ) * (K x x' : ℂ) * g l (x' l)) := by
      intro l
      rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun x _ => sum_congr rfl fun x' _ => ?_
      unfold cutLaw
      push_cast
      ring
    rw [sum_congr rfl fun l _ => e1 l, Finset.sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [map_one, one_mul, mul_sum, Finset.sum_comm]
    refine sum_congr rfl fun x' _ => ?_
    rw [mul_sum, mul_sum]
  rw [e]
  exact sum_eq_zero fun l _ => sum_cutLaw_comp_zero (cutLaw μ K) hΛinv l _ (hg l)

/-- **`rho_V`**: `⟪1, Op v⟫ = 0` on the degree-one space. -/
theorem cx_rho_V (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (K : (U → ZMod p) → (U → ZMod p) → ℝ)
    (hΛinv : ∀ (s c : ZMod p) (z : (U → ZMod p) × (U → ZMod p)), s ≠ 0 → IsSquare s →
      cutLaw μ K (affLab s c z.1, affLab s c z.2) = cutLaw μ K z) :
    ∀ v ∈ degSpace μ, ⟪l2MapC μ (fun _ : U → ZMod p => (1 : ℂ)), kernelOpC μ K v⟫_ℂ = 0 := by
  intro v hv
  obtain ⟨hg, hvg⟩ := degRep_spec μ hv
  have h := inner_one_kernelOpC_degMap μ hμ0 K hΛinv (degRep μ v) hg
  rwa [hvg] at h

/-! ## The norm (`lem:spec:degone`(c)) -/

omit [DecidableEq U] in
lemma sum_sqn_fcoef (g : U → ZMod p → ℂ) :
    ∑ ξ, Sarkozy.Spectral.sqn (fun k => fcoef (g k) ξ) = ∑ k, l2sq (g k) := by
  unfold Sarkozy.Spectral.sqn
  rw [sum_comm]
  exact sum_congr rfl fun k _ => (l2sq_eq_sum_fcoef _).symm

/-- **`degone_norm`** (`lem:spec:degone`(c)): `(1 − ε_V) ∑_ξ |ĝ(ξ)|² ≤ ‖v‖²` on `𝒱`. -/
theorem cx_degone_norm (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {εV : ℝ} (hN : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (fun k l => degoneN μ ξ k l - if k = l then 1 else 0) εV) :
    ∀ v ∈ degSpace μ, (1 - εV) * ∑ ξ, Sarkozy.Spectral.sqn (degCoef μ v ξ) ≤ ‖v‖ ^ 2 := by
  intro v hv
  obtain ⟨hg, hvg⟩ := degRep_spec μ hv
  have h := (degone_equiv_bounds hp2 μ hμ1 hinv hinj hN (degRep μ v) hg).1
  have e2 : ‖degMap μ (degRep μ v)‖ ^ 2 = ∑ x, μ x * ‖∑ k, degRep μ v k (x k)‖ ^ 2 := by
    rw [degMap_apply, norm_l2MapC_sq μ hμ0]
    rfl
  rw [← sum_sqn_fcoef, ← e2, hvg] at h
  exact h

/-! ## The form on `𝒱` (`lem:spec:degone`(a), (b)) -/

/-- `⟪F_V, Op F_V'⟫_μ = E_λ[\overline{F_V(x)} F_V'(x')]`. -/
lemma inner_degMap_kernelOpC_eq (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (K : (U → ZMod p) → (U → ZMod p) → ℝ) (g h : U → ZMod p → ℂ) :
    ⟪degMap μ g, kernelOpC μ K (degMap μ h)⟫_ℂ =
      ∑ z, (cutLaw μ K z : ℂ) * (conj (∑ k, g k (z.1 k)) * ∑ l, h l (z.2 l)) := by
  rw [degMap_apply, degMap_apply, kernelOpC_l2MapC μ hμ0, inner_l2MapC μ hμ0,
    Fintype.sum_prod_type]
  unfold opFun degFun
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun x' _ => ?_
  unfold cutLaw
  push_cast
  ring

/-- **`lem:spec:degone`(a) in the realization**: for mean-zero `g`,
`⟪F_V, Op F_V⟫ = ∑_{ξ≠0} ĝ(ξ)^*𝐐(ξ)ĝ(ξ)`. -/
theorem inner_degMap_kernelOpC (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (K : (U → ZMod p) → (U → ZMod p) → ℝ) (hΛ1 : ∑ z, cutLaw μ K z = 1)
    (hΛinv : ∀ (s c : ZMod p) (z : (U → ZMod p) × (U → ZMod p)), s ≠ 0 → IsSquare s →
      cutLaw μ K (affLab s c z.1, affLab s c z.2) = cutLaw μ K z)
    (hΛinj : ∀ (z : (U → ZMod p) × (U → ZMod p)) (k l : U), cutLaw μ K z ≠ 0 → z.1 k ≠ z.2 l)
    (g : U → ZMod p → ℂ) (hg : ∀ k, ∑ a, g k a = 0) :
    ⟪degMap μ g, kernelOpC μ K (degMap μ g)⟫_ℂ =
      ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
        qform (degoneQ (cutLaw μ K) ξ) (fun k => fcoef (g k) ξ) := by
  rw [inner_degMap_kernelOpC_eq μ hμ0 K g g,
    degone_bilinear hp2 (cutLaw μ K) hΛ1 hΛinv hΛinj g g hg hg]
  rfl

/-- `𝐐(ξ) = r(𝐀₀(ξ) + E_Q(ξ))`, so `w^*𝐐w = r(w^*𝐀₀w + w^*E_Qw)`. -/
lemma qform_degoneQ (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) (ς : U → U → ZMod p)
    (ξ : ZMod p) (w : U → ℂ) :
    qform (degoneQ Λ ξ) w = (rp p : ℂ) * (qform (azero ς ξ) w + qform (errQ Λ ς ξ) w) := by
  have hr := rp_ne_zero (p := p)
  have hQ : ∀ k l, degoneQ Λ ξ k l = (rp p : ℂ) * (azero ς ξ k l + errQ Λ ς ξ k l) := by
    intro k l
    unfold errQ
    field_simp
    ring
  unfold qform
  rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun l _ => ?_
  rw [hQ]
  ring

omit [Fintype U] [DecidableEq U] in
lemma qform_zero_vec (X : U → U → ℂ) [Fintype U] : qform X (fun _ => (0 : ℂ)) = 0 := by
  unfold qform
  simp

/-- **The two-sided mode bound** (`lem:spec:degone`(b)): for `ξ ≠ 0` and `‖E_Q(ξ)‖ ≤ η_Q`,
`|re(w^*𝐐w) − r re(w^*𝐀₀w)| ≤ r η_Q |w|²`. -/
lemma mode_bounds (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) (ς : U → U → ZMod p) (ξ : ZMod p)
    {ηQ : ℝ} (hE : NormLe (errQ Λ ς ξ) ηQ) (w : U → ℂ) :
    rp p * ((qform (azero ς ξ) w).re - ηQ * Sarkozy.Spectral.sqn w) ≤
        (qform (degoneQ Λ ξ) w).re ∧
      (qform (degoneQ Λ ξ) w).re ≤
        rp p * ((qform (azero ς ξ) w).re + ηQ * Sarkozy.Spectral.sqn w) := by
  have hr : 0 ≤ rp p := by unfold rp; positivity
  have hE' : |(qform (errQ Λ ς ξ) w).re| ≤ ηQ * Sarkozy.Spectral.sqn w := by
    have h1 : qform (errQ Λ ς ξ) w = bform (errQ Λ ς ξ) w w := rfl
    have h2 := hE w w
    rw [mul_assoc, vnorm_mul_self] at h2
    rw [h1]
    exact (Complex.abs_re_le_norm _).trans h2
  rw [qform_degoneQ Λ ς ξ w, Complex.re_ofReal_mul, Complex.add_re]
  have h3 := abs_le.mp hE'
  constructor
  · exact mul_le_mul_of_nonneg_left (by linarith [h3.1]) hr
  · exact mul_le_mul_of_nonneg_left (by linarith [h3.2]) hr

/-- The sums over all modes and over `ξ ≠ 0` agree when the mode `0` contributes nothing. -/
lemma sum_modes_eq (f : ZMod p → ℝ) (hf : f 0 = 0) :
    ∑ ξ, f ξ = ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0), f ξ := by
  refine (sum_filter_of_ne fun ξ _ hξ => ?_).symm
  intro h0
  exact hξ (h0 ▸ hf)

omit [Fintype U] [DecidableEq U] in
lemma fcoef_zero_vec (g : U → ZMod p → ℂ) (hg : ∀ k, ∑ a, g k a = 0) :
    (fun k => fcoef (g k) 0) = fun _ => (0 : ℂ) := by
  funext k
  rw [fcoef_zero, hg k, mul_zero]

/-- **`degone_lower` and `degone_upper` for `F_V`** (`lem:spec:degone`(a), (b)): for mean-zero
`g`, `r ∑_ξ (re(ĝ^*𝐀₀ĝ) ∓ η_Q|ĝ|²)` bounds `re⟪F_V, Op F_V⟫` from below and above. -/
theorem degMap_degone_bounds (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (K : (U → ZMod p) → (U → ZMod p) → ℝ) (hΛ1 : ∑ z, cutLaw μ K z = 1)
    (hΛinv : ∀ (s c : ZMod p) (z : (U → ZMod p) × (U → ZMod p)), s ≠ 0 → IsSquare s →
      cutLaw μ K (affLab s c z.1, affLab s c z.2) = cutLaw μ K z)
    (hΛinj : ∀ (z : (U → ZMod p) × (U → ZMod p)) (k l : U), cutLaw μ K z ≠ 0 → z.1 k ≠ z.2 l)
    (ς : U → U → ZMod p) {ηQ : ℝ}
    (hE : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (errQ (cutLaw μ K) ς ξ) ηQ)
    (g : U → ZMod p → ℂ) (hg : ∀ k, ∑ a, g k a = 0) :
    rp p * ∑ ξ, ((qform (azero ς ξ) (fun k => fcoef (g k) ξ)).re -
        ηQ * Sarkozy.Spectral.sqn (fun k => fcoef (g k) ξ)) ≤
        RCLike.re ⟪degMap μ g, kernelOpC μ K (degMap μ g)⟫_ℂ ∧
      RCLike.re ⟪degMap μ g, kernelOpC μ K (degMap μ g)⟫_ℂ ≤
        rp p * ∑ ξ, ((qform (azero ς ξ) (fun k => fcoef (g k) ξ)).re +
          ηQ * Sarkozy.Spectral.sqn (fun k => fcoef (g k) ξ)) := by
  have hz := fcoef_zero_vec g hg
  have hsq0 : Sarkozy.Spectral.sqn (fun _ : U => (0 : ℂ)) = 0 := by
    unfold Sarkozy.Spectral.sqn; simp
  rw [inner_degMap_kernelOpC hp2 μ hμ0 K hΛ1 hΛinv hΛinj g hg, RCLike.re_to_complex,
    Complex.re_sum, mul_sum, mul_sum]
  rw [sum_modes_eq _ (by rw [hz, qform_zero_vec, hsq0]; simp),
    sum_modes_eq (fun ξ => rp p * ((qform (azero ς ξ) (fun k => fcoef (g k) ξ)).re +
      ηQ * Sarkozy.Spectral.sqn (fun k => fcoef (g k) ξ))) (by rw [hz, qform_zero_vec, hsq0]; simp)]
  constructor
  · exact sum_le_sum fun ξ hξ =>
      (mode_bounds (cutLaw μ K) ς ξ (hE ξ (mem_filter.mp hξ).2) _).1
  · exact sum_le_sum fun ξ hξ =>
      (mode_bounds (cutLaw μ K) ς ξ (hE ξ (mem_filter.mp hξ).2) _).2

/-- **`degone_lower`** (`lem:spec:degone`(b), Route A input): on `𝒱`,
`r ∑_ξ (qA ξ (coef v ξ) − η_Q |coef v ξ|²) ≤ re⟪v, Op v⟫`, `qA ξ x = re(x^*𝐀₀(ξ)x)`. -/
theorem cx_degone_lower (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (K : (U → ZMod p) → (U → ZMod p) → ℝ) (hΛ1 : ∑ z, cutLaw μ K z = 1)
    (hΛinv : ∀ (s c : ZMod p) (z : (U → ZMod p) × (U → ZMod p)), s ≠ 0 → IsSquare s →
      cutLaw μ K (affLab s c z.1, affLab s c z.2) = cutLaw μ K z)
    (hΛinj : ∀ (z : (U → ZMod p) × (U → ZMod p)) (k l : U), cutLaw μ K z ≠ 0 → z.1 k ≠ z.2 l)
    (ς : U → U → ZMod p) {ηQ : ℝ}
    (hE : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (errQ (cutLaw μ K) ς ξ) ηQ) :
    ∀ v ∈ degSpace μ, rp p * ∑ ξ, ((qform (azero ς ξ) (degCoef μ v ξ)).re -
        ηQ * Sarkozy.Spectral.sqn (degCoef μ v ξ)) ≤ RCLike.re ⟪v, kernelOpC μ K v⟫_ℂ := by
  intro v hv
  obtain ⟨hg, hvg⟩ := degRep_spec μ hv
  have h := (degMap_degone_bounds hp2 μ hμ0 K hΛ1 hΛinv hΛinj ς hE (degRep μ v) hg).1
  rw [hvg] at h
  exact h

/-- **`degone_upper`** (`lem:spec:degone`(b), Route A input): on `𝒱`,
`re⟪v, Op v⟫ ≤ r ∑_ξ (qA ξ (coef v ξ) + η_Q |coef v ξ|²)`. -/
theorem cx_degone_upper (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (K : (U → ZMod p) → (U → ZMod p) → ℝ) (hΛ1 : ∑ z, cutLaw μ K z = 1)
    (hΛinv : ∀ (s c : ZMod p) (z : (U → ZMod p) × (U → ZMod p)), s ≠ 0 → IsSquare s →
      cutLaw μ K (affLab s c z.1, affLab s c z.2) = cutLaw μ K z)
    (hΛinj : ∀ (z : (U → ZMod p) × (U → ZMod p)) (k l : U), cutLaw μ K z ≠ 0 → z.1 k ≠ z.2 l)
    (ς : U → U → ZMod p) {ηQ : ℝ}
    (hE : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (errQ (cutLaw μ K) ς ξ) ηQ) :
    ∀ v ∈ degSpace μ, RCLike.re ⟪v, kernelOpC μ K v⟫_ℂ ≤
      rp p * ∑ ξ, ((qform (azero ς ξ) (degCoef μ v ξ)).re +
        ηQ * Sarkozy.Spectral.sqn (degCoef μ v ξ)) := by
  intro v hv
  obtain ⟨hg, hvg⟩ := degRep_spec μ hv
  have h := (degMap_degone_bounds hp2 μ hμ0 K hΛ1 hΛinv hΛinj ς hE (degRep μ v) hg).2
  rw [hvg] at h
  exact h

/-- **The degree-one fields of `RouteAInputs`** in the complex realization, together:
`symm`, `norm_one`, `V_perp_one`, `rho_mean`, `rho_V`, `degone_lower`, `degone_upper`,
`degone_norm`, with `T = kernelOpC μ K`, `one = l2MapC μ 1`, `V = degSpace μ`,
`coef = degCoef μ`, `qA ξ x = re(x^*𝐀₀(ξ)x)`, `r = rp p`. -/
theorem cx_degone_fields (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (K : (U → ZMod p) → (U → ZMod p) → ℝ) (hK : ∀ x x', K x x' = K x' x)
    (hΛ1 : ∑ z, cutLaw μ K z = 1)
    (hΛinv : ∀ (s c : ZMod p) (z : (U → ZMod p) × (U → ZMod p)), s ≠ 0 → IsSquare s →
      cutLaw μ K (affLab s c z.1, affLab s c z.2) = cutLaw μ K z)
    (hΛinj : ∀ (z : (U → ZMod p) × (U → ZMod p)) (k l : U), cutLaw μ K z ≠ 0 → z.1 k ≠ z.2 l)
    (ς : U → U → ZMod p) {ηQ εV : ℝ}
    (hE : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (errQ (cutLaw μ K) ς ξ) ηQ)
    (hN : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (fun k l => degoneN μ ξ k l - if k = l then 1 else 0) εV) :
    (kernelOpC μ K).IsSymmetric ∧
    ‖l2MapC μ (fun _ : U → ZMod p => (1 : ℂ))‖ = 1 ∧
    (∀ v ∈ degSpace μ, ⟪l2MapC μ (fun _ : U → ZMod p => (1 : ℂ)), v⟫_ℂ = 0) ∧
    ⟪l2MapC μ (fun _ : U → ZMod p => (1 : ℂ)),
      kernelOpC μ K (l2MapC μ (fun _ : U → ZMod p => (1 : ℂ)))⟫_ℂ = 1 ∧
    (∀ v ∈ degSpace μ, ⟪l2MapC μ (fun _ : U → ZMod p => (1 : ℂ)), kernelOpC μ K v⟫_ℂ = 0) ∧
    (∀ v ∈ degSpace μ, rp p * ∑ ξ, ((qform (azero ς ξ) (degCoef μ v ξ)).re -
        ηQ * Sarkozy.Spectral.sqn (degCoef μ v ξ)) ≤ RCLike.re ⟪v, kernelOpC μ K v⟫_ℂ) ∧
    (∀ v ∈ degSpace μ, RCLike.re ⟪v, kernelOpC μ K v⟫_ℂ ≤
      rp p * ∑ ξ, ((qform (azero ς ξ) (degCoef μ v ξ)).re +
        ηQ * Sarkozy.Spectral.sqn (degCoef μ v ξ))) ∧
    (∀ v ∈ degSpace μ, (1 - εV) * ∑ ξ, Sarkozy.Spectral.sqn (degCoef μ v ξ) ≤ ‖v‖ ^ 2) :=
  ⟨kernelOpC_isSymmetric μ K hK, cx_norm_one μ hμ0 hμ1, cx_V_perp_one μ hμ0 hinv,
    cx_rho_mean μ hμ0 K hΛ1, cx_rho_V μ hμ0 K hΛinv,
    cx_degone_lower hp2 μ hμ0 K hΛ1 hΛinv hΛinj ς hE,
    cx_degone_upper hp2 μ hμ0 K hΛ1 hΛinv hΛinj ς hE,
    cx_degone_norm hp2 μ hμ0 hμ1 hinv hinj hN⟩

end Sarkozy.SpectralD.Cx
