module

public import Sarkozy.SpectralD.SingletonStar

@[expose] public section

/-!
# The pivot bound for cross Grams of stars (`lem:general-star`(c), `eq:star-cross-bound`)

`paper/sections/14_spectral.tex`, `lem:general-star`(c). Setting of `subsec:spec:actual-stars`:
`p ≡ 3 (mod 4)`, `μ` an `Aff_p`-invariant law on labellings `x : U → 𝔽_p`, supported on
injective labellings. For supports `S ≠ T` (nonempty), with `k = |S|`, `l = |T|`, `c = |S∩T|`,
`d = |S△T|` and `a_d` of `aConst`, and a pivot `j ∈ S△T` whose conditional law given the other
coordinates is at most `D_j/p` (`condLaw μ j x t ≤ D_j/p` on the support of `μ`):

`‖W_S^*W_T‖/q ≤ ([a_d + (c + (k − 1)(l − 1))q]² + q(D_j − 1))^{1/2}/(1 − q)`
(`star_pivot_bound`, in squared form).

The ingredients, in the order of the paper's proof:
* `abs_starA_le`: `|𝒜_ST| ≤ a_d + cq` (product of two stars, `sum_starKer_mul`; `a_1 = 0`,
  `a_2 = q` by the two-root identity, `a_d = (d − 1)r` by `thm:weil` for `d ≥ 3`);
* `abs_starC_le`: `|𝒞_ST| ≤ (k − 1)(l − 1)q` (`|w_S| ≤ (k − 1)r`, Weil);
* `starB_sq_le`: `ℬ_ST² ≤ q²(D_j − 1)`. For `j ∈ S∖T`, the law of total expectation over `x_j`
  (`sum_mu_condLaw`) replaces `χ(z − x_j)` by `φ_j(z) = ∑_t ν_j(t)χ(z − t)`, with
  `‖φ_j‖² = ∑_t ν_j(t)² − q ≤ q(D_j − 1)` (WP-K's `sum_phi_sq`), `|ψ_{S∖j}| ≤ 1` and `‖C‖ = r`
  (`sum_gauss_sq_le`); for `j ∈ T∖S`, `ℬ_ST = χ(−1)ℬ_TS` (`starB_swap`).
These are inserted into the norm formula of `lem:general-star`(b) (WP-K's `star_cross`).

`thm:weil` enters as the hypothesis `Labellings.WeilBound (ZMod p)` (from `Target.Weil` by
`Labellings.weilBound_of_target`); the pivot density is a hypothesis (in the paper it comes
from `lem:graphs:vertex`(dens) and `lem:extension`(coarse), `D_j = 2^t/(1 − e_t(p, n))`).

New material for this paper.
-/

namespace Sarkozy.SpectralD

open Finset Sarkozy.SpectralC
open scoped BigOperators symmDiff ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- The law of total expectation over one coordinate:
`E_μ G = E_μ ∑_t ν_j(t | x) G(x[j ↦ t])`. -/
lemma sum_mu_condLaw (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (j : U)
    (G : (U → ZMod p) → ℝ) :
    ∑ x, μ x * G x = ∑ x, μ x * ∑ t, condLaw μ j x t * G (Function.update x j t) := by
  rw [← sum_mu_class μ hμ0 (univ.erase j) G]
  refine sum_congr rfl fun x _ => ?_
  congr 1
  rw [sum_agree_erase j x (fun x' => μ x' * G x'), sum_div]
  refine sum_congr rfl fun t _ => ?_
  unfold condLaw
  ring

omit [Fintype U] in
lemma starKer_update_not_mem {T : Finset U} {j : U} (hj : j ∉ T) (x : U → ZMod p)
    (t : ZMod p) : starKer T (Function.update x j t) = starKer T x := by
  funext b
  unfold starKer
  congr 1
  refine prod_congr rfl fun i hi => ?_
  have hij : i ≠ j := fun h => hj (by rw [← h]; exact hi)
  rw [Function.update_of_ne hij]

omit [Fintype U] in
lemma starKer_update_mem {S : Finset U} {j : U} (hj : j ∈ S) (x : U → ZMod p)
    (t a : ZMod p) :
    starKer S (Function.update x j t) a = (p : ℝ)⁻¹ * (chiRe (a - t) * psiRest S j x a) := by
  unfold starKer
  rw [prod_update S hj x t a]

omit [Fintype U] in
lemma psiRest_update {S : Finset U} {j : U} (x : U → ZMod p) (t a : ZMod p) :
    psiRest S j (Function.update x j t) a = psiRest S j x a := by
  unfold psiRest
  refine prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hi)]

/-- `‖C‖ ≤ r` in unnormalized real form: `∑_a (∑_b χ(b − a) f(b))² ≤ p ∑_b f(b)²`. -/
lemma sum_gauss_sq_le (hp2 : p ≠ 2) (f : ZMod p → ℝ) :
    ∑ a, (∑ b, chiRe (b - a) * f b) ^ 2 ≤ (p : ℝ) * ∑ b, f b ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h := l2sq_gaussOp_le hp2 (fun b => ((f b : ℝ) : ℂ))
  have e1 : ∀ a, gaussOp (fun b => ((f b : ℝ) : ℂ)) a =
      (((p : ℝ)⁻¹ * ∑ b, chiRe (b - a) * f b : ℝ) : ℂ) := by
    intro a
    unfold gaussOp chiRe
    push_cast
    simp only [chiC_apply]
  unfold l2sq at h
  simp only [e1, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  rw [rp_sq] at h
  have e2 : ∀ a, ((p : ℝ)⁻¹ * ∑ b, chiRe (b - a) * f b) ^ 2 =
      (p : ℝ)⁻¹ ^ 2 * (∑ b, chiRe (b - a) * f b) ^ 2 := fun a => by ring
  simp only [e2, ← mul_sum] at h
  have h2 : (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ ^ 2 * ∑ a, (∑ b, chiRe (b - a) * f b) ^ 2) ≤
      (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ * ∑ b, f b ^ 2) := h
  have h3 : (p : ℝ)⁻¹ ^ 2 * ∑ a, (∑ b, chiRe (b - a) * f b) ^ 2 ≤
      (p : ℝ)⁻¹ * ∑ b, f b ^ 2 := le_of_mul_le_mul_left h2 (inv_pos.mpr hp0)
  have h4 : ∑ a, (∑ b, chiRe (b - a) * f b) ^ 2 =
      (p : ℝ) ^ 2 * ((p : ℝ)⁻¹ ^ 2 * ∑ a, (∑ b, chiRe (b - a) * f b) ^ 2) := by
    field_simp
  rw [h4]
  calc (p : ℝ) ^ 2 * ((p : ℝ)⁻¹ ^ 2 * ∑ a, (∑ b, chiRe (b - a) * f b) ^ 2)
      ≤ (p : ℝ) ^ 2 * ((p : ℝ)⁻¹ * ∑ b, f b ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (p : ℝ) * ∑ b, f b ^ 2 := by field_simp

/-- **`ℬ_ST` with a pivot `j ∈ S∖T`**: `ℬ_ST² ≤ q²(D_j − 1)`. -/
theorem starB_sq_le_of_mem (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1) {S T : Finset U} {j : U} (hjS : j ∈ S) (hjT : j ∉ T) {D : ℝ}
    (hD : ∀ x t, μ x ≠ 0 → condLaw μ j x t ≤ D / p) :
    starB μ S T ^ 2 ≤ (p : ℝ)⁻¹ ^ 2 * (D - 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set X : (U → ZMod p) → ℝ := fun x => ∑ a, ∑ b, starKer S x a * chiRe (b - a) * starKer T x b
    with hX
  have hB : starB μ S T = ∑ x, μ x * X x := rfl
  rw [hB, sum_mu_condLaw μ hμ0 j X]
  set Y : (U → ZMod p) → ℝ := fun x => ∑ t, condLaw μ j x t * X (Function.update x j t)
    with hY
  -- the pointwise bound
  have hYle : ∀ x, μ x ≠ 0 → Y x ^ 2 ≤ (p : ℝ)⁻¹ ^ 2 * (D - 1) := by
    intro x hx
    set ν : ZMod p → ℝ := condLaw μ j x with hν
    set φ : ZMod p → ℝ := fun a => ∑ t, ν t * chiRe (a - t) with hφ
    set Cψ : ZMod p → ℝ := fun a => ∑ b, chiRe (b - a) * starKer T x b with hCψ
    have hYx : Y x = (p : ℝ)⁻¹ * ∑ a, φ a * (psiRest S j x a * Cψ a) := by
      simp only [hY, hX, starKer_update_not_mem hjT, starKer_update_mem hjS]
      simp only [mul_sum, hφ, hCψ, sum_mul]
      rw [sum_comm]
      refine sum_congr rfl fun a _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun b _ => ?_
      refine sum_congr rfl fun t _ => ?_
      ring
    have hν1 : ∑ t, ν t = 1 := sum_condLaw μ hμ0 j x hx
    have hν0 : ∀ t, 0 ≤ ν t := condLaw_nonneg μ hμ0 j x
    -- `∑ φ² ≤ D − 1`
    have hφ2 : ∑ a, φ a ^ 2 ≤ D - 1 := by
      have e := sum_phi_sq hp2 ν
      simp only [hφ] at e ⊢
      rw [e, hν1]
      have h2 : ∑ t, ν t ^ 2 ≤ D / p := by
        have : ∑ t, ν t ^ 2 ≤ ∑ t, D / p * ν t :=
          sum_le_sum fun t _ => by rw [sq]; exact mul_le_mul_of_nonneg_right (hD x t hx) (hν0 t)
        rwa [← mul_sum, hν1, mul_one] at this
      have h3 : (p : ℝ) * ∑ t, ν t ^ 2 ≤ D := by
        calc (p : ℝ) * ∑ t, ν t ^ 2 ≤ (p : ℝ) * (D / p) := mul_le_mul_of_nonneg_left h2 hp0.le
          _ = D := by field_simp
      linarith
    -- `∑ (ψ' Cψ)² ≤ 1`
    have hC2 : ∑ a, (psiRest S j x a * Cψ a) ^ 2 ≤ 1 := by
      have h1 : ∀ a, (psiRest S j x a * Cψ a) ^ 2 ≤ Cψ a ^ 2 := by
        intro a
        rw [mul_pow]
        have : psiRest S j x a ^ 2 ≤ 1 := by
          have := abs_psiRest_le S j x a
          rw [← sq_abs]; nlinarith [abs_nonneg (psiRest S j x a)]
        nlinarith [sq_nonneg (Cψ a)]
      refine (sum_le_sum fun a _ => h1 a).trans ?_
      have h2 := sum_gauss_sq_le hp2 (starKer T x)
      refine h2.trans ?_
      have h3 : ∀ b, starKer T x b ^ 2 ≤ (p : ℝ)⁻¹ ^ 2 := by
        intro b
        unfold starKer
        rw [mul_pow]
        have : (∏ i ∈ T, chiRe (b - x i)) ^ 2 ≤ 1 := by
          have := abs_prod_chiRe_le T x b
          rw [← sq_abs]; nlinarith [abs_nonneg (∏ i ∈ T, chiRe (b - x i))]
        nlinarith [sq_nonneg (p : ℝ)⁻¹]
      calc (p : ℝ) * ∑ b, starKer T x b ^ 2 ≤ (p : ℝ) * ∑ _b : ZMod p, (p : ℝ)⁻¹ ^ 2 :=
            mul_le_mul_of_nonneg_left (sum_le_sum fun b _ => h3 b) hp0.le
        _ = 1 := by
          rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
          field_simp
    -- Cauchy--Schwarz in `a`
    have hCS := sum_mul_sq_le_sq_mul_sq univ φ (fun a => psiRest S j x a * Cψ a)
    rw [hYx, mul_pow]
    have hφ0 : 0 ≤ ∑ a, φ a ^ 2 := sum_nonneg fun a _ => sq_nonneg _
    calc (p : ℝ)⁻¹ ^ 2 * (∑ a, φ a * (psiRest S j x a * Cψ a)) ^ 2
        ≤ (p : ℝ)⁻¹ ^ 2 * ((∑ a, φ a ^ 2) * ∑ a, (psiRest S j x a * Cψ a) ^ 2) :=
          mul_le_mul_of_nonneg_left hCS (by positivity)
      _ ≤ (p : ℝ)⁻¹ ^ 2 * ((∑ a, φ a ^ 2) * 1) := by
          gcongr
      _ ≤ (p : ℝ)⁻¹ ^ 2 * (D - 1) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left hφ2 (by positivity)
  -- Jensen in `x`
  have hJ : (∑ x, μ x * Y x) ^ 2 ≤ (∑ x, μ x) * ∑ x, μ x * Y x ^ 2 := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro x _; exact hμ0 x
    · intro x _; exact mul_nonneg (hμ0 x) (sq_nonneg _)
    · intro x _; nlinarith [hμ0 x]
  rw [hμ1, one_mul] at hJ
  refine hJ.trans ?_
  calc ∑ x, μ x * Y x ^ 2 ≤ ∑ x, μ x * ((p : ℝ)⁻¹ ^ 2 * (D - 1)) := by
        refine sum_le_sum fun x _ => ?_
        by_cases hx : μ x = 0
        · rw [hx, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (hYle x hx) (hμ0 x)
    _ = (p : ℝ)⁻¹ ^ 2 * (D - 1) := by rw [← sum_mul, hμ1, one_mul]

omit [Fintype U] [DecidableEq U] in
lemma chiRe_neg_mul (s : ZMod p) : chiRe (-s) = chiRe (-1 : ZMod p) * chiRe s := by
  rw [← chiRe_mul]; ring_nf

/-- `ℬ_TS = χ(−1) ℬ_ST`. -/
lemma starB_swap (μ : (U → ZMod p) → ℝ) (S T : Finset U) :
    starB μ T S = chiRe (-1 : ZMod p) * starB μ S T := by
  unfold starB
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  have e : ∑ a, ∑ b, starKer T x a * chiRe (b - a) * starKer S x b =
      ∑ a, ∑ b, starKer T x b * chiRe (a - b) * starKer S x a := Finset.sum_comm
  rw [e]
  simp only [mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [show a - b = -(b - a) by ring, chiRe_neg_mul]
  ring

/-- **The `ℬ` bound of `lem:general-star`(c)**: for a pivot `j ∈ S△T`, `ℬ_ST² ≤ q²(D_j − 1)`. -/
theorem starB_sq_le (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1) {S T : Finset U} {j : U} (hj : j ∈ S ∆ T) {D : ℝ}
    (hD : ∀ x t, μ x ≠ 0 → condLaw μ j x t ≤ D / p) :
    starB μ S T ^ 2 ≤ (p : ℝ)⁻¹ ^ 2 * (D - 1) := by
  rcases mem_symmDiff.mp hj with ⟨hjS, hjT⟩ | ⟨hjT, hjS⟩
  · exact starB_sq_le_of_mem hp2 μ hμ0 hμ1 hjS hjT hD
  · have h := starB_sq_le_of_mem hp2 μ hμ0 hμ1 hjT hjS hD
    rw [starB_swap, mul_pow] at h
    have hm : chiRe (-1 : ZMod p) ^ 2 = 1 := by
      unfold chiRe
      have hne : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
      exact_mod_cast quadraticChar_sq_one hne
    rwa [hm, one_mul] at h

/-- **The `𝒜` bound of `lem:general-star`(c)**: `|𝒜_ST| ≤ a_d + cq` for `S ≠ T`. -/
theorem abs_starA_le (hp2 : p ≠ 2) (hW : Labellings.WeilBound (ZMod p)) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {S T : Finset U} (hST : S ≠ T) :
    |starA μ S T| ≤ aConst p (S ∆ T).card + ((S ∩ T).card : ℝ) * (p : ℝ)⁻¹ := by
  have hinjOn : ∀ x, μ x ≠ 0 → ∀ R : Finset U, Set.InjOn x R := fun x hx R a _ b _ hab => by
    by_contra hne; exact hinj x a b hx hne hab
  have hD : (S ∆ T).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    exact hST (symmDiff_eq_bot.mp h)
  unfold starA
  calc |∑ x, μ x * ((p : ℝ) * ∑ a, starKer S x a * starKer T x a)|
      ≤ ∑ x, μ x * (aConst p (S ∆ T).card + ((S ∩ T).card : ℝ) * (p : ℝ)⁻¹) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
        rw [abs_mul, abs_of_nonneg (hμ0 x)]
        by_cases hx : μ x = 0
        · rw [hx, zero_mul, zero_mul]
        apply mul_le_mul_of_nonneg_left _ (hμ0 x)
        have hxU : Set.InjOn x (↑S ∪ ↑T) := by
          have := hinjOn x hx (S ∪ T); rwa [coe_union] at this
        refine (abs_sum_starKer_mul_le S T x hxU).trans ?_
        exact add_le_add (abs_starMean_le_aConst hp2 hW hD x (hinjOn x hx _)) (le_refl _)
    _ = aConst p (S ∆ T).card + ((S ∩ T).card : ℝ) * (p : ℝ)⁻¹ := by
        rw [← sum_mul, hμ1, one_mul]

/-- **The `𝒞` bound of `lem:general-star`(c)**: `|𝒞_ST| ≤ (k − 1)(l − 1)q` (Weil). -/
theorem abs_starC_le (hW : Labellings.WeilBound (ZMod p)) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {S T : Finset U} (hS : S.Nonempty) (hT : T.Nonempty) :
    |starC μ S T| ≤ ((S.card : ℝ) - 1) * ((T.card : ℝ) - 1) * (p : ℝ)⁻¹ := by
  have hinjOn : ∀ x, μ x ≠ 0 → ∀ R : Finset U, Set.InjOn x R := fun x hx R a _ b _ hab => by
    by_contra hne; exact hinj x a b hx hne hab
  have hk : (0 : ℝ) ≤ (S.card : ℝ) - 1 := by
    have : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
    linarith
  have hl : (0 : ℝ) ≤ (T.card : ℝ) - 1 := by
    have : (1 : ℝ) ≤ T.card := by exact_mod_cast hT.card_pos
    linarith
  unfold starC
  calc |∑ x, μ x * (starMean S x * starMean T x)|
      ≤ ∑ x, μ x * (((S.card : ℝ) - 1) * ((T.card : ℝ) - 1) * (p : ℝ)⁻¹) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
        rw [abs_mul, abs_of_nonneg (hμ0 x)]
        by_cases hx : μ x = 0
        · rw [hx, zero_mul, zero_mul]
        apply mul_le_mul_of_nonneg_left _ (hμ0 x)
        rw [abs_mul]
        have h1 := abs_starMean_le hW hS x (hinjOn x hx S)
        have h2 := abs_starMean_le hW hT x (hinjOn x hx T)
        calc |starMean S x| * |starMean T x|
            ≤ (((S.card : ℝ) - 1) * rp p) * (((T.card : ℝ) - 1) * rp p) :=
              mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hk rp_nonneg)
          _ = ((S.card : ℝ) - 1) * ((T.card : ℝ) - 1) * (p : ℝ)⁻¹ := by
              rw [← rp_sq]; ring
    _ = ((S.card : ℝ) - 1) * ((T.card : ℝ) - 1) * (p : ℝ)⁻¹ := by
        rw [← sum_mul, hμ1, one_mul]

/-- **`lem:general-star`(c), `eq:star-cross-bound`** (`p ≡ 3 (mod 4)`, Weil): for nonempty
supports `S ≠ T` and a pivot `j ∈ S△T` with conditional probabilities `ν_j(t | x) ≤ D_j/p` on
the support of `μ`,
`‖W_S^*W_T h‖² ≤ (q/(1 − q))² ([a_d + (c + (k − 1)(l − 1))q]² + q(D_j − 1)) ‖h‖²` on `L²_0`,
that is `‖W_S^*W_T‖/q ≤ ([a_d + (c + (k − 1)(l − 1))q]² + q(D_j − 1))^{1/2}/(1 − q)`, with
`k = |S|`, `l = |T|`, `c = |S∩T|`, `d = |S△T|`. -/
theorem star_pivot_bound (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (hW : Labellings.WeilBound (ZMod p))
    (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {S T : Finset U} (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ≠ T) {j : U}
    (hj : j ∈ S ∆ T) {D : ℝ} (hD : ∀ x t, μ x ≠ 0 → condLaw μ j x t ≤ D / p)
    (h : ZMod p → ℂ) (hh : meanC h = 0) :
    l2sq (gramOp μ (starKer S) (starKer T) h) ≤
      ((p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹)) ^ 2 * ((aConst p (S ∆ T).card +
        (((S ∩ T).card : ℝ) + ((S.card : ℝ) - 1) * ((T.card : ℝ) - 1)) * (p : ℝ)⁻¹) ^ 2 +
          (p : ℝ)⁻¹ * (D - 1)) * l2sq h := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [(star_cross hp2 μ hinv S T).2 hp3 h hh]
  apply mul_le_mul_of_nonneg_right _ (l2sq_nonneg h)
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hA := abs_starA_le hp2 hW μ hμ0 hμ1 hinj hST
  have hC := abs_starC_le hW μ hμ0 hμ1 hinj hS hT
  have hB := starB_sq_le hp2 μ hμ0 hμ1 hj hD
  have hAC : (starA μ S T - starC μ S T) ^ 2 ≤ (aConst p (S ∆ T).card +
      (((S ∩ T).card : ℝ) + ((S.card : ℝ) - 1) * ((T.card : ℝ) - 1)) * (p : ℝ)⁻¹) ^ 2 := by
    rw [← sq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _)
    refine (abs_sub _ _).trans ?_
    linarith
  have hB' : starB μ S T ^ 2 / (p : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ * (D - 1) := by
    rw [div_le_iff₀ (inv_pos.mpr hp0)]
    nlinarith
  linarith

/-- **Sanity check of the pivot hypothesis**: every conditional probability is at most `1`, so
the hypothesis `condLaw μ j x t ≤ D/p` of `star_pivot_bound` holds with `D = p` for every `μ`
(the paper's value for graph labellings is `D_j = 2^t/(1 − e_t(p, n))`). -/
lemma condLaw_le_one (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (j : U) (x : U → ZMod p)
    (t : ZMod p) : condLaw μ j x t ≤ (p : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [div_self hp0.ne']
  unfold condLaw
  rw [cmass_erase]
  have hle : μ (Function.update x j t) ≤ ∑ t', μ (Function.update x j t') :=
    single_le_sum (fun t' _ => hμ0 _) (mem_univ t)
  by_cases h0 : ∑ t', μ (Function.update x j t') = 0
  · rw [h0, div_zero]; exact zero_le_one
  · have hpos : 0 < ∑ t', μ (Function.update x j t') :=
      lt_of_le_of_ne (sum_nonneg fun t' _ => hμ0 _) (Ne.symm h0)
    rw [div_le_one hpos]
    exact hle

end Sarkozy.SpectralD
