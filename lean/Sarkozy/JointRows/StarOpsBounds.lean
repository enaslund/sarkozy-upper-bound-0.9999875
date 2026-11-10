module

public import Sarkozy.JointRows.StarOps
public import Sarkozy.JointRows.StarFeatures

/-!
# Norm bounds for the feature maps `W_S` (`prop:conditional-star`, Steps 1 and 6)

Source: `paper/sections/16_extraction.tex`, proof of `prop:conditional-star`.

* `gam_self_le_one`, `gamMat_posSemidef`: `Γ_ν` is positive semidefinite with `Γ_ν(t, t) ≤ 1`;
* `sum_paley_sq_le`: `‖Φ̂h‖ ≤ ‖h‖` (from `Φ̂* = -Φ̂`, `Φ̂² = -(I - J)`);
* `gam_quad_le`, `gamMat_le`: for a law `ν` with density at most `κ`, `Γ_ν ⪯ κ I` as a matrix,
  i.e. `Γ_ν ⪯ κ r² I` as an operator relative to the uniform law (Step 1: `Γ_i = V_i^* V_i` with
  `V_i f = P_0 ι_{ν_i} C f`);
* `wOp_norm_le`: **`‖W_S‖ ≤ √κ r`** on all of `L²(𝔽_p)` (Step 1, by the Gram identity and the
  Schur product theorem, `Star.prod_gamma_le`);
* `wOp_decay`: **`‖W_S 𝟙_Ω‖² ≤ r² + ν_χ^{|S|}`** (Step 6), for `ν_χ` bounding `|Γ_i(t, t')|`
  (`= |Cov_{ν_i}(χ(t - x), χ(t' - x))|`) at distinct `t, t' ∈ Ω`, stated for `g` supported in `Ω`.

Here `r² = 1/p`, and the norms are those of `L²(uniform)` and `L²(ν_X)`.
-/

@[expose] public section

open scoped BigOperators
open Matrix

namespace Sarkozy.JointRows.StarOps

open Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.JointRows.PaleyGauss

variable {p : ℕ} [Fact p.Prime]

theorem chiR_mul_self_le_one (x : ZMod p) : chiR p x * chiR p x ≤ 1 := by
  by_cases hx : x = 0
  · rw [hx, chiR_zero]; norm_num
  · rw [chiR_sq hx]

theorem gam_comm (ν : FiniteLaw (ZMod p)) (t t' : ZMod p) : gam ν t t' = gam ν t' t := by
  unfold gam
  exact FiniteLaw.expect_congr _ fun a => mul_comm _ _

theorem gam_self_nonneg (ν : FiniteLaw (ZMod p)) (t : ZMod p) : 0 ≤ gam ν t t :=
  FiniteLaw.expect_nonneg _ fun _ => mul_self_nonneg _

/-- `Γ_ν(t, t) = Var_ν χ(t - x) ≤ 1`. -/
theorem gam_self_le_one (ν : FiniteLaw (ZMod p)) (t : ZMod p) : gam ν t t ≤ 1 := by
  have h := FiniteLaw.expect_sq_sub_mean ν (fun a => chiR p (t - a))
  have h1 : gam ν t t =
      ν.expect (fun a => (chiR p (t - a) - ν.expect (fun a => chiR p (t - a))) ^ 2) := by
    unfold gam phi mchi
    exact FiniteLaw.expect_congr _ fun a => by ring
  have h2 : ν.expect (fun a => chiR p (t - a) ^ 2) ≤ 1 :=
    FiniteLaw.expect_le_const _ fun a => by rw [sq]; exact chiR_mul_self_le_one _
  have h3 := sq_nonneg (ν.expect (fun a => chiR p (t - a)))
  linarith

/-- `E_a (∑_t F_t(a))² = ∑_{t,t'} E_a F_t(a) F_{t'}(a)`. -/
theorem expect_sq_sum {α β : Type*} [Fintype α] [Fintype β] (μ : FiniteLaw α) (F : β → α → ℝ) :
    μ.expect (fun a => (∑ t, F t a) ^ 2) = ∑ t, ∑ t', μ.expect (fun a => F t a * F t' a) := by
  simp only [FiniteLaw.expect, sq]
  simp only [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  calc ∑ a, ∑ t, ∑ t', μ.weight a * (F t a * F t' a)
      = ∑ t, ∑ a, ∑ t', μ.weight a * (F t a * F t' a) := Finset.sum_comm
    _ = ∑ t, ∑ t', ∑ a, μ.weight a * (F t a * F t' a) :=
        Finset.sum_congr rfl fun t _ => Finset.sum_comm

/-- `⟨h, Γ_ν h⟩ = E_{a∼ν} (∑_t h(t) φ_ν(t, a))²`. -/
theorem gam_quad (ν : FiniteLaw (ZMod p)) (h : ZMod p → ℝ) :
    ∑ t, ∑ t', h t * gam ν t t' * h t' = ν.expect (fun a => (∑ t, h t * phi ν t a) ^ 2) := by
  rw [expect_sq_sum]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
  unfold gam
  rw [← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_mul_const]
  exact FiniteLaw.expect_congr _ fun a => by ring

/-- `∑_b χ(b - a) h(b) = √p · Φ̂h(a)`. -/
theorem sum_chi_eq_paley (h : ZMod p → ℝ) (a : ZMod p) :
    ∑ b, chiR p (b - a) * h b = Real.sqrt p * paley p h a := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  unfold paley
  rw [← mul_assoc, mul_div_assoc', hs, div_self hp0.ne', one_mul]

/-- `∑_t h(t) φ_ν(t, a) = √p (Φ̂h(a) - E_ν Φ̂h)`. -/
theorem sum_mul_phi (ν : FiniteLaw (ZMod p)) (h : ZMod p → ℝ) (a : ZMod p) :
    ∑ t, h t * phi ν t a = Real.sqrt p * (paley p h a - ν.expect (paley p h)) := by
  unfold phi mchi
  have h1 : ∑ t, h t * (chiR p (t - a) - ν.expect (fun a' => chiR p (t - a'))) =
      ∑ t, chiR p (t - a) * h t - ν.expect (fun a' => ∑ t, chiR p (t - a') * h t) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun t _ => mul_comm _ _
    · simp only [FiniteLaw.expect, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun t _ => by ring
  rw [h1, sum_chi_eq_paley]
  simp only [sum_chi_eq_paley]
  rw [FiniteLaw.expect_const_mul]
  ring

/-- **`‖Φ̂h‖ ≤ ‖h‖`**: `∑ (Φ̂h)² = ∑ h² - (∑ h)²/p`. -/
theorem sum_paley_sq_le (hp : p % 4 = 3) (h : ZMod p → ℝ) :
    ∑ t, paley p h t * paley p h t ≤ ∑ t, h t * h t := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have ha := paley_anti hp h (paley p h)
  simp only [paley_sq hp] at ha
  have hexp : ∑ t, h t * -(h t - (∑ c, h c) / p) = -(∑ t, h t * h t) + (∑ c, h c) ^ 2 / p := by
    simp only [mul_neg, mul_sub, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul]
    ring
  have hnn : 0 ≤ (∑ c, h c) ^ 2 / p := by positivity
  linarith

/-- **`Γ_ν ⪯ κ I`** for a law `ν` with density at most `κ` (`ν(a) ≤ κ/p`). -/
theorem gam_quad_le (hp : p % 4 = 3) (ν : FiniteLaw (ZMod p)) {κ : ℝ}
    (hκ : ∀ a, ν.weight a ≤ κ / p) (h : ZMod p → ℝ) :
    ∑ t, ∑ t', h t * gam ν t t' * h t' ≤ κ * ∑ t, h t * h t := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hκ0 : 0 ≤ κ := by
    have := (ν.nonneg 0).trans (hκ 0)
    rwa [le_div_iff₀ hp0, zero_mul] at this
  rw [gam_quad]
  simp only [sum_mul_phi]
  have h2 : ν.expect (fun a => (Real.sqrt p * (paley p h a - ν.expect (paley p h))) ^ 2) =
      p * (ν.expect (fun a => paley p h a ^ 2) - ν.expect (paley p h) ^ 2) := by
    rw [show (fun a => (Real.sqrt p * (paley p h a - ν.expect (paley p h))) ^ 2) =
        fun a => (p : ℝ) * (paley p h a - ν.expect (paley p h)) ^ 2 from
        funext fun a => by rw [mul_pow, Real.sq_sqrt hp0.le]]
    rw [FiniteLaw.expect_const_mul, FiniteLaw.expect_sq_sub_mean]
  rw [h2]
  have h3 : ν.expect (fun a => paley p h a ^ 2) ≤ κ / p * ∑ a, paley p h a * paley p h a := by
    unfold FiniteLaw.expect
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => by
      simp only [sq]; exact mul_le_mul_of_nonneg_right (hκ a) (mul_self_nonneg _)
  have h4 := sum_paley_sq_le hp h
  have h5 := sq_nonneg (ν.expect (paley p h))
  calc (p : ℝ) * (ν.expect (fun a => paley p h a ^ 2) - ν.expect (paley p h) ^ 2)
      ≤ p * ν.expect (fun a => paley p h a ^ 2) := by nlinarith
    _ ≤ p * (κ / p * ∑ a, paley p h a * paley p h a) := mul_le_mul_of_nonneg_left h3 hp0.le
    _ = κ * ∑ a, paley p h a * paley p h a := by field_simp
    _ ≤ κ * ∑ t, h t * h t := mul_le_mul_of_nonneg_left h4 hκ0

/-- The matrix of `Γ_ν`. -/
noncomputable def gamMat (ν : FiniteLaw (ZMod p)) : Matrix (ZMod p) (ZMod p) ℝ := Matrix.of (gam ν)

theorem quad_eq (A : Matrix (ZMod p) (ZMod p) ℝ) (x : ZMod p → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ t, ∑ t', x t * A t t' * x t' := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => by ring

theorem gamMat_posSemidef (ν : FiniteLaw (ZMod p)) : (gamMat ν).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (IsHermitian.ext fun i j => ?_) fun x => ?_
  · simp only [gamMat, of_apply, star_trivial]
    exact gam_comm ν j i
  · simp only [star_trivial]
    rw [quad_eq]
    simp only [gamMat, of_apply]
    rw [gam_quad]
    exact FiniteLaw.expect_nonneg _ fun a => sq_nonneg _

theorem gamMat_le (hp : p % 4 = 3) (ν : FiniteLaw (ZMod p)) {κ : ℝ}
    (hκ : ∀ a, ν.weight a ≤ κ / p) :
    (κ • (1 : Matrix (ZMod p) (ZMod p) ℝ) - gamMat ν).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (IsHermitian.ext fun i j => ?_) fun x => ?_
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, gamMat, Matrix.of_apply,
      star_trivial, smul_eq_mul]
    rw [gam_comm ν j i]
    by_cases hij : i = j
    · subst hij; rfl
    · simp only [Ne.symm hij, hij, ↓reduceIte]
  · simp only [star_trivial]
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, quad_eq]
    simp only [gamMat, of_apply]
    have := gam_quad_le hp ν hκ x
    have hd : x ⬝ᵥ x = ∑ t, x t * x t := rfl
    rw [hd]
    linarith

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **`‖W_S‖ ≤ √κ r`** (Step 1): if the coordinate laws `ν_i`, `i ∈ S`, have densities at most
`κ` (`ν_i(a) ≤ κ/p`) and `S ≠ ∅`, then `‖W_S f‖²_{ν_X} ≤ κ r² ‖f‖²`, `r² = 1/p`. -/
theorem wOp_norm_le (hp : p % 4 = 3) (νp : X → FiniteLaw (ZMod p)) (S : Finset X)
    (hS : S.Nonempty) {κ : ℝ} (hκ : ∀ i ∈ S, ∀ a, (νp i).weight a ≤ κ / p) (f : ZMod p → ℝ) :
    ip (blockLaw νp) (wOp νp S f) (wOp νp S f) ≤
      κ * (p : ℝ)⁻¹ * ip (FiniteLaw.uniform (ZMod p)) f f := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  obtain ⟨i₁, hi₁⟩ := hS
  have hκ0 : 0 ≤ κ := by
    have := ((νp i₁).nonneg 0).trans (hκ i₁ hi₁ 0)
    rwa [le_div_iff₀ hp0, zero_mul] at this
  have hP := Star.prod_gamma_le S hi₁ (fun i => gamMat (νp i)) (fun i _ => gamMat_posSemidef _)
    (fun i _ t => gam_self_le_one _ _) hκ0 (gamMat_le hp _ (hκ i₁ hi₁))
  have hq := hP.dotProduct_mulVec_nonneg f
  simp only [star_trivial] at hq
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
    quad_eq] at hq
  simp only [of_apply, gamMat] at hq
  have hd : f ⬝ᵥ f = ∑ t, f t * f t := rfl
  rw [hd] at hq
  rw [wOp_gram]
  simp only [FiniteLaw.expect_uniform, ZMod.card, ip]
  rw [Finset.sum_div]
  have hs : ∑ t, (∑ t', f t * f t' * ∏ i ∈ S, gam (νp i) t t') / p / p =
      (∑ t, ∑ t', f t * (∏ i ∈ S, gam (νp i) t t') * f t') / p / p := by
    rw [← Finset.sum_div, ← Finset.sum_div]
    congr 2
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => by ring
  rw [hs]
  rw [div_div, show κ * (p : ℝ)⁻¹ * ((∑ t, f t * f t) / p) = κ * (∑ t, f t * f t) / (p * p) by
    field_simp]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- **Step 6: `‖W_S 𝟙_Ω‖² ≤ r² + ν_χ^{|S|}`.** If `|Γ_i(t, t')| ≤ ν_χ` for `i ∈ S` and distinct
`t, t' ∈ Ω`, then `‖W_S g‖²_{ν_X} ≤ (r² + ν_χ^{|S|}) ‖g‖²` for every `g` supported in `Ω`
(`r² = 1/p`). -/
theorem wOp_decay (νp : X → FiniteLaw (ZMod p)) (S : Finset X) (Ω : Finset (ZMod p)) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ∀ i ∈ S, ∀ t ∈ Ω, ∀ t' ∈ Ω, t ≠ t' → |gam (νp i) t t'| ≤ ν)
    (g : ZMod p → ℝ) (hg : ∀ t, t ∉ Ω → g t = 0) :
    ip (blockLaw νp) (wOp νp S g) (wOp νp S g) ≤
      ((p : ℝ)⁻¹ + ν ^ S.card) * ip (FiniteLaw.uniform (ZMod p)) g g := by
  have hνs := pow_nonneg hν0 S.card
  have hδ : ∀ t t' : ZMod p, (0 : ℝ) ≤ (if t = t' then 1 else 0) := fun t t' => by
    split_ifs <;> norm_num
  have hpt : ∀ t t', g t * g t' * ∏ i ∈ S, gam (νp i) t t' ≤
      |g t| * |g t'| * ((if t = t' then 1 else 0) + ν ^ S.card) := by
    intro t t'
    have hR : 0 ≤ |g t| * |g t'| * ((if t = t' then 1 else 0) + ν ^ S.card) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (add_nonneg (hδ t t') hνs)
    by_cases ht : t ∈ Ω
    · by_cases ht' : t' ∈ Ω
      · have hprod : |∏ i ∈ S, gam (νp i) t t'| ≤ (if t = t' then 1 else 0) + ν ^ S.card := by
          rw [Finset.abs_prod]
          by_cases htt : t = t'
          · subst htt
            simp only [↓reduceIte]
            have : ∏ i ∈ S, |gam (νp i) t t| ≤ 1 := by
              calc ∏ i ∈ S, |gam (νp i) t t| ≤ ∏ _i ∈ S, (1 : ℝ) :=
                    Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => by
                      rw [abs_of_nonneg (gam_self_nonneg _ _)]
                      exact gam_self_le_one _ _
                _ = 1 := Finset.prod_const_one
            linarith
          · simp only [htt, ↓reduceIte, zero_add]
            calc ∏ i ∈ S, |gam (νp i) t t'| ≤ ∏ _i ∈ S, ν :=
                  Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i hi => hν i hi t ht t' ht' htt
              _ = ν ^ S.card := Finset.prod_const ν
        calc g t * g t' * ∏ i ∈ S, gam (νp i) t t'
            ≤ |g t * g t' * ∏ i ∈ S, gam (νp i) t t'| := le_abs_self _
          _ = |g t| * |g t'| * |∏ i ∈ S, gam (νp i) t t'| := by rw [abs_mul, abs_mul]
          _ ≤ |g t| * |g t'| * ((if t = t' then 1 else 0) + ν ^ S.card) :=
              mul_le_mul_of_nonneg_left hprod (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      · rw [show g t * g t' * ∏ i ∈ S, gam (νp i) t t' = 0 by rw [hg t' ht']; ring]
        exact hR
    · rw [show g t * g t' * ∏ i ∈ S, gam (νp i) t t' = 0 by rw [hg t ht]; ring]
      exact hR
  rw [wOp_gram]
  have hmono := FiniteLaw.expect_mono (FiniteLaw.uniform (ZMod p)) fun t =>
    FiniteLaw.expect_mono (FiniteLaw.uniform (ZMod p)) fun t' => hpt t t'
  have hinner : ∀ t, (FiniteLaw.uniform (ZMod p)).expect
      (fun t' => |g t| * |g t'| * ((if t = t' then 1 else 0) + ν ^ S.card)) =
      (p : ℝ)⁻¹ * (g t * g t) +
        ν ^ S.card * (FiniteLaw.uniform (ZMod p)).expect (fun t' => |g t'|) * |g t| := by
    intro t
    rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform, ZMod.card]
    have hs : ∑ t', |g t| * |g t'| * ((if t = t' then 1 else 0) + ν ^ S.card) =
        |g t| * |g t| + ∑ t', ν ^ S.card * |g t| * |g t'| := by
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
      congr 1
      exact Finset.sum_congr rfl fun t' _ => by ring
    rw [hs, abs_mul_abs_self, ← Finset.mul_sum]
    ring
  have hR : (FiniteLaw.uniform (ZMod p)).expect (fun t => (FiniteLaw.uniform (ZMod p)).expect
      (fun t' => |g t| * |g t'| * ((if t = t' then 1 else 0) + ν ^ S.card))) =
      (p : ℝ)⁻¹ * (FiniteLaw.uniform (ZMod p)).expect (fun t => g t * g t) +
        ν ^ S.card * (FiniteLaw.uniform (ZMod p)).expect (fun t => |g t|) ^ 2 := by
    rw [FiniteLaw.expect_congr _ hinner, FiniteLaw.expect_add, FiniteLaw.expect_const_mul,
      FiniteLaw.expect_const_mul]
    ring
  have hJ : (FiniteLaw.uniform (ZMod p)).expect (fun t => |g t|) ^ 2 ≤
      (FiniteLaw.uniform (ZMod p)).expect (fun t => g t * g t) := by
    have h1 := FiniteLaw.mean_sq_le_second_moment (FiniteLaw.uniform (ZMod p)) (fun t => |g t|)
    have h2 : (FiniteLaw.uniform (ZMod p)).expect (fun t => |g t| ^ 2) =
        (FiniteLaw.uniform (ZMod p)).expect (fun t => g t * g t) :=
      FiniteLaw.expect_congr _ fun t => by rw [sq_abs, sq]
    linarith
  unfold ip
  rw [hR] at hmono
  have := mul_le_mul_of_nonneg_left hJ hνs
  linarith

end Sarkozy.JointRows.StarOps
