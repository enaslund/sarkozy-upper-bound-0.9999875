module

public import Sarkozy.JointRows.PaleyGauss
public import Sarkozy.JointRows.StarHoeffding

/-!
# The feature maps of `prop:conditional-star` on the actual χ-kernels

Source: `paper/sections/16_extraction.tex`, proof of `prop:conditional-star`, "Centred feature
maps" and Step 1.

For a prime `p`, the quadratic character `χ` of `𝔽_p` (`PaleyGauss.chiR`), a finite set `X`,
coordinate laws `ν_i` on `𝔽_p` (`i ∈ X`) and the product law `ν_X = ⊗_i ν_i`
(`FiveType.Blocks.blockLaw`):
* `mchi ν t = E_{a∼ν} χ(t - a)` (the paper's `m_ν`), `phi ν t a = χ(t - a) - m_ν(t)` (`φ_ν`), and
  `gam ν t t' = E_{a∼ν} φ_ν(t, a) φ_ν(t', a)` (`Γ_ν`);
* `wOp νp S f x = E_t f(t) ∏_{i∈S} φ_{ν_i}(t, x_i)` (`W_S`), and
  `wStar νp S g t = E_{x∼ν_X} g(x) ∏_{i∈S} φ_{ν_i}(t, x_i)`, its adjoint (`ip_wOp`);
* `uStar νp i g a = E_{x∼ν_X} p·1{x_i = a} g(x)`, the adjoint of `h ↦ h(x_i)`
  (`expect_eval_mul`); for `g ∈ L²_0(ν_X)` it is `U_i^* ḡ_i = ρ_i ḡ_i`, with `ḡ_i` the component
  of `g` in `H_{{i}}`;
* `wOp_gram`: **the Gram identity** of Step 1,
  `⟨W_S f, W_S f'⟩_{ν_X} = E_{t,t'} f(t) f'(t') ∏_{i∈S} Γ_i(t, t')` ("by independence");
* `wOp_exactSupport`: `W_S f ∈ H_S` (`Star.ExactSupport`), so the `W_S` have pairwise orthogonal
  ranges (`Star.hoeffding_orthogonal`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.JointRows.PaleyGauss

variable {p : ℕ} [Fact p.Prime]

/-- `m_ν(t) = E_{a∼ν} χ(t - a)`. -/
noncomputable def mchi (ν : FiniteLaw (ZMod p)) (t : ZMod p) : ℝ :=
  ν.expect (fun a => chiR p (t - a))

/-- `φ_ν(t, a) = χ(t - a) - m_ν(t)`. -/
noncomputable def phi (ν : FiniteLaw (ZMod p)) (t a : ZMod p) : ℝ := chiR p (t - a) - mchi ν t

/-- `Γ_ν(t, t') = E_{a∼ν} φ_ν(t, a) φ_ν(t', a)`. -/
noncomputable def gam (ν : FiniteLaw (ZMod p)) (t t' : ZMod p) : ℝ :=
  ν.expect (fun a => phi ν t a * phi ν t' a)

/-- `E_{a∼ν} φ_ν(t, a) = 0`. -/
theorem expect_phi (ν : FiniteLaw (ZMod p)) (t : ZMod p) : ν.expect (phi ν t) = 0 := by
  change ν.expect (fun a => chiR p (t - a) - mchi ν t) = 0
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const]
  unfold mchi
  ring

/-- Finite Fubini: `E_a E_b F(a, b) = E_b E_a F(a, b)`. -/
theorem expect_swap {α β : Type*} [Fintype α] [Fintype β] (μ : FiniteLaw α) (ν : FiniteLaw β)
    (F : α → β → ℝ) :
    μ.expect (fun a => ν.expect (fun b => F a b)) =
      ν.expect (fun b => μ.expect (fun a => F a b)) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Independence**: `E_{x∼ν_X} ∏_{i∈S} g_i(x_i) = ∏_{i∈S} E_{ν_i} g_i`. -/
theorem expect_prod_mem (νp : X → FiniteLaw (ZMod p)) (S : Finset X) (g : X → ZMod p → ℝ) :
    (blockLaw νp).expect (fun x => ∏ i ∈ S, g i (x i)) = ∏ i ∈ S, (νp i).expect (g i) := by
  set G : X → ZMod p → ℝ := fun i a => if i ∈ S then g i a else 1 with hG
  have h1 : ∀ x : X → ZMod p, ∏ i ∈ S, g i (x i) = ∏ i, G i (x i) := by
    intro x
    simp only [hG]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  have h2 : ∏ i ∈ S, (νp i).expect (g i) = ∏ i, (νp i).expect (G i) := by
    have : ∀ i, (νp i).expect (G i) = if i ∈ S then (νp i).expect (g i) else 1 := by
      intro i
      by_cases hi : i ∈ S
      · simp only [hG, hi, ↓reduceIte]
      · simp only [hG, hi, ↓reduceIte, FiniteLaw.expect_const]
    simp only [this]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [FiniteLaw.expect_congr _ h1, h2]
  exact expect_blockLaw_prod νp G

/-- `(W_S f)(x) = E_t f(t) ∏_{i∈S} φ_{ν_i}(t, x_i)`. -/
noncomputable def wOp (νp : X → FiniteLaw (ZMod p)) (S : Finset X) (f : ZMod p → ℝ)
    (x : X → ZMod p) : ℝ :=
  (FiniteLaw.uniform (ZMod p)).expect (fun t => f t * ∏ i ∈ S, phi (νp i) t (x i))

/-- `(W_S^* g)(t) = E_{x∼ν_X} g(x) ∏_{i∈S} φ_{ν_i}(t, x_i)`. -/
noncomputable def wStar (νp : X → FiniteLaw (ZMod p)) (S : Finset X) (g : (X → ZMod p) → ℝ)
    (t : ZMod p) : ℝ :=
  (blockLaw νp).expect (fun x => g x * ∏ i ∈ S, phi (νp i) t (x i))

/-- `(U_i^* g)(a) = E_{x∼ν_X} p·1{x_i = a} g(x)`. -/
noncomputable def uStar (νp : X → FiniteLaw (ZMod p)) (i : X) (g : (X → ZMod p) → ℝ)
    (a : ZMod p) : ℝ :=
  (blockLaw νp).expect (fun x => (if x i = a then (p : ℝ) else 0) * g x)

/-- **`W_S^*` is the adjoint of `W_S`**: `⟨W_S f, g⟩_{ν_X} = ⟨f, W_S^* g⟩_{𝔽_p}`. -/
theorem ip_wOp (νp : X → FiniteLaw (ZMod p)) (S : Finset X) (f : ZMod p → ℝ)
    (g : (X → ZMod p) → ℝ) :
    ip (blockLaw νp) (wOp νp S f) g = ip (FiniteLaw.uniform (ZMod p)) f (wStar νp S g) := by
  unfold ip wOp wStar
  rw [show (fun x => (FiniteLaw.uniform (ZMod p)).expect
      (fun t => f t * ∏ i ∈ S, phi (νp i) t (x i)) * g x) =
      fun x => (FiniteLaw.uniform (ZMod p)).expect
        (fun t => f t * (g x * ∏ i ∈ S, phi (νp i) t (x i))) from funext fun x => by
    rw [← FiniteLaw.expect_mul_const]
    exact FiniteLaw.expect_congr _ fun t => by ring]
  rw [expect_swap]
  exact FiniteLaw.expect_congr _ fun t => by rw [FiniteLaw.expect_const_mul]

/-- **`uStar` is the adjoint of the evaluation at `i`**: `E_{ν_X} h(x_i) g(x) = E_a h(a)
(U_i^* g)(a)`. -/
theorem expect_eval_mul (νp : X → FiniteLaw (ZMod p)) (i : X) (h : ZMod p → ℝ)
    (g : (X → ZMod p) → ℝ) :
    (blockLaw νp).expect (fun x => h (x i) * g x) =
      (FiniteLaw.uniform (ZMod p)).expect (fun a => h a * uStar νp i g a) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold uStar
  simp only [← FiniteLaw.expect_const_mul]
  rw [expect_swap]
  refine FiniteLaw.expect_congr _ fun x => ?_
  rw [FiniteLaw.expect_uniform]
  have hs : ∑ a : ZMod p, h a * ((if x i = a then (p : ℝ) else 0) * g x) =
      h (x i) * (p * g x) := by
    simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]
  rw [hs, ZMod.card]
  field_simp

/-- **The Gram identity** (Step 1): `⟨W_S f, W_S f'⟩_{ν_X} = E_{t,t'} f(t) f'(t')
∏_{i∈S} Γ_i(t, t')`. -/
theorem wOp_gram (νp : X → FiniteLaw (ZMod p)) (S : Finset X) (f f' : ZMod p → ℝ) :
    ip (blockLaw νp) (wOp νp S f) (wOp νp S f') =
      (FiniteLaw.uniform (ZMod p)).expect (fun t => (FiniteLaw.uniform (ZMod p)).expect
        (fun t' => f t * f' t' * ∏ i ∈ S, gam (νp i) t t')) := by
  have h : ∀ x : X → ZMod p, wOp νp S f x * wOp νp S f' x =
      (FiniteLaw.uniform (ZMod p)).expect (fun t => (FiniteLaw.uniform (ZMod p)).expect
        (fun t' => f t * f' t' *
          ∏ i ∈ S, (phi (νp i) t (x i) * phi (νp i) t' (x i)))) := by
    intro x
    unfold wOp
    rw [← FiniteLaw.expect_mul_const]
    refine FiniteLaw.expect_congr _ fun t => ?_
    rw [← FiniteLaw.expect_const_mul]
    refine FiniteLaw.expect_congr _ fun t' => ?_
    rw [Finset.prod_mul_distrib]
    ring
  unfold ip
  rw [FiniteLaw.expect_congr _ h, expect_swap]
  refine FiniteLaw.expect_congr _ fun t => ?_
  rw [expect_swap]
  refine FiniteLaw.expect_congr _ fun t' => ?_
  rw [FiniteLaw.expect_const_mul,
    expect_prod_mem νp S (fun i a => phi (νp i) t a * phi (νp i) t' a)]
  rfl

omit [Fintype X] in
/-- **`W_S f ∈ H_S`**: it depends only on `x_S` and has conditional mean zero in each coordinate
of `S`. -/
theorem wOp_exactSupport (νp : X → FiniteLaw (ZMod p)) (S : Finset X) (f : ZMod p → ℝ) :
    Star.ExactSupport νp S (wOp νp S f) where
  depends x x' hxx' := by
    unfold wOp
    refine FiniteLaw.expect_congr _ fun t => ?_
    rw [Finset.prod_congr rfl fun i hi => by rw [hxx' i hi]]
  centred i hi x := by
    unfold Star.condMean wOp
    have hsplit : ∀ (a : ZMod p) (t : ZMod p), ∏ k ∈ S, phi (νp k) t (Function.update x i a k) =
        phi (νp i) t a * ∏ k ∈ S.erase i, phi (νp k) t (x k) := by
      intro a t
      rw [← Finset.mul_prod_erase S _ hi, Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun k hk => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    simp only [hsplit]
    change (νp i).expect (fun a => (FiniteLaw.uniform (ZMod p)).expect
      (fun t => f t * (phi (νp i) t a * ∏ k ∈ S.erase i, phi (νp k) t (x k)))) = 0
    rw [expect_swap]
    have h0 : ∀ t, (νp i).expect (fun a => f t * (phi (νp i) t a *
        ∏ k ∈ S.erase i, phi (νp k) t (x k))) = 0 := by
      intro t
      rw [show (fun a => f t * (phi (νp i) t a * ∏ k ∈ S.erase i, phi (νp k) t (x k))) =
          fun a => (f t * ∏ k ∈ S.erase i, phi (νp k) t (x k)) * phi (νp i) t a from
          funext fun a => by ring, FiniteLaw.expect_const_mul]
      rw [expect_phi, mul_zero]
    simp only [h0, FiniteLaw.expect_const]

end Sarkozy.JointRows.StarOps
