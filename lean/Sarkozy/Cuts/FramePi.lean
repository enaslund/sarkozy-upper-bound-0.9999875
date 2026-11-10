module

public import Sarkozy.Cuts.FrameTensor

/-!
# Cuts, VIII⁗′: Kronecker products of finitely many weighted frames (`lem:weighted-frame` (b))

`lem:weighted-frame` (b) for `n` families of kernel operators (`k : Fin n`), by induction on `n`
from the two-factor statement `Sarkozy.Cuts.frame_tensor`.

* `piOp`: the tensor product `⊗_k V_k`, with the kernel `∏_k V_k(x_k; z_k)` relative to
  `⊗_k μ_k`.
* `expect_pi_succ`: expectations over `⊗_{k ≤ n} μ_k` split off the factor `k = 0`.
* `frame_pi`: if `|⟨V^{(k)}_1 z, V^{(k)}_2 z'⟩| ≤ G_k ‖z‖ ‖z'‖` for every `k`, then
  `|⟨(⊗_k V^{(k)}_1) Z, (⊗_k V^{(k)}_2) Z'⟩| ≤ (∏_k G_k) ‖Z‖ ‖Z'‖`.
* `frame_pi_family`: (b) for `n` families `(V^{(k)}_i)_{i ∈ I_k}` with matrices `G^{(k)}`: the
  tensor family indexed by `∏_k I_k` satisfies the hypothesis with the Kronecker product
  `∏_k G^{(k)}_{i_k j_k}`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering

universe u

section FramePi

/-- The tensor product `⊗_k V_k : L²(⊗_k μ_k) → L²(⊗_k ν_k)` of kernel operators
`V_k : L²(μ_k) → L²(ν_k)`: the kernel `∏_k V_k(x_k; z_k)` relative to `⊗_k μ_k`. -/
noncomputable def piOp {n : ℕ} {X Z : Fin n → Type u} [∀ k, Fintype (Z k)]
    (μ : ∀ k, FiniteLaw (Z k)) (V : ∀ k, X k → Z k → ℝ) (Fn : (∀ k, Z k) → ℝ) :
    (∀ k, X k) → ℝ :=
  recOp (FiniteLaw.pi μ) (fun x z => ∏ k, V k (x k) (z k)) Fn

/-- Expectations over `⊗_{k ≤ n} μ_k` split off the factor `k = 0`. -/
theorem expect_pi_succ {n : ℕ} {Z : Fin (n + 1) → Type u} [∀ k, Fintype (Z k)]
    (μ : ∀ k, FiniteLaw (Z k)) (f : (∀ k, Z k) → ℝ) :
    (FiniteLaw.pi μ).expect f =
      ((μ 0).product (FiniteLaw.pi (fun k : Fin n => μ k.succ))).expect
        (fun p => f (Fin.cons p.1 p.2)) := by
  rw [FiniteLaw.expect_product]
  simp only [FiniteLaw.expect]
  rw [(Fintype.sum_equiv (Fin.consEquiv Z)
    (fun p => (FiniteLaw.pi μ).weight (Fin.cons p.1 p.2) * f (Fin.cons p.1 p.2))
    (fun x => (FiniteLaw.pi μ).weight x * f x) (fun p => rfl)).symm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have hw : (FiniteLaw.pi μ).weight (Fin.cons a y) =
      (μ 0).weight a * (FiniteLaw.pi (fun k : Fin n => μ k.succ)).weight y := by
    show ∏ k, (μ k).weight ((Fin.cons a y : ∀ k, Z k) k) =
      (μ 0).weight a * ∏ k : Fin n, (μ k.succ).weight (y k)
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  rw [hw]
  ring

theorem ip_pi_succ {n : ℕ} {Z : Fin (n + 1) → Type u} [∀ k, Fintype (Z k)]
    (μ : ∀ k, FiniteLaw (Z k)) (f g : (∀ k, Z k) → ℝ) :
    ip (FiniteLaw.pi μ) f g =
      ip ((μ 0).product (FiniteLaw.pi (fun k : Fin n => μ k.succ)))
        (fun p => f (Fin.cons p.1 p.2)) (fun p => g (Fin.cons p.1 p.2)) := by
  unfold ip
  exact expect_pi_succ μ _

theorem nrm_pi_succ {n : ℕ} {Z : Fin (n + 1) → Type u} [∀ k, Fintype (Z k)]
    (μ : ∀ k, FiniteLaw (Z k)) (f : (∀ k, Z k) → ℝ) :
    nrm (FiniteLaw.pi μ) f =
      nrm ((μ 0).product (FiniteLaw.pi (fun k : Fin n => μ k.succ)))
        (fun p => f (Fin.cons p.1 p.2)) := by
  unfold nrm
  rw [ip_pi_succ]

theorem piOp_cons {n : ℕ} {X Z : Fin (n + 1) → Type u} [∀ k, Fintype (Z k)]
    (μ : ∀ k, FiniteLaw (Z k)) (V : ∀ k, X k → Z k → ℝ) (Fn : (∀ k, Z k) → ℝ)
    (p : X 0 × (∀ k : Fin n, X k.succ)) :
    piOp μ V Fn (Fin.cons p.1 p.2) =
      tensOp (μ 0) (FiniteLaw.pi (fun k : Fin n => μ k.succ)) (V 0)
        (fun x' z' => ∏ k : Fin n, V k.succ (x' k) (z' k)) (fun q => Fn (Fin.cons q.1 q.2)) p := by
  unfold piOp recOp tensOp
  rw [expect_pi_succ]
  refine FiniteLaw.expect_congr _ (fun q => ?_)
  beta_reduce
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- **`lem:weighted-frame` (b), `n` factors.** If `|⟨V^{(k)}_1 z, V^{(k)}_2 z'⟩| ≤ G_k ‖z‖ ‖z'‖`
for every `k : Fin n`, then `|⟨(⊗_k V^{(k)}_1) Z, (⊗_k V^{(k)}_2) Z'⟩| ≤ (∏_k G_k) ‖Z‖ ‖Z'‖`. -/
theorem frame_pi : ∀ (n : ℕ) {X Z₁ Z₂ : Fin n → Type u} [∀ k, Fintype (X k)]
    [∀ k, Fintype (Z₁ k)] [∀ k, Fintype (Z₂ k)] (ν : ∀ k, FiniteLaw (X k))
    (μ₁ : ∀ k, FiniteLaw (Z₁ k)) (μ₂ : ∀ k, FiniteLaw (Z₂ k)) (V₁ : ∀ k, X k → Z₁ k → ℝ)
    (V₂ : ∀ k, X k → Z₂ k → ℝ) (G : Fin n → ℝ), (∀ k, 0 ≤ G k) →
    (∀ k z z', |ip (ν k) (recOp (μ₁ k) (V₁ k) z) (recOp (μ₂ k) (V₂ k) z')| ≤
      G k * nrm (μ₁ k) z * nrm (μ₂ k) z') →
    ∀ (Fn : (∀ k, Z₁ k) → ℝ) (Fn' : (∀ k, Z₂ k) → ℝ),
    |ip (FiniteLaw.pi ν) (piOp μ₁ V₁ Fn) (piOp μ₂ V₂ Fn')| ≤
      (∏ k, G k) * nrm (FiniteLaw.pi μ₁) Fn * nrm (FiniteLaw.pi μ₂) Fn'
  | 0, X, Z₁, Z₂, _, _, _, ν, μ₁, μ₂, V₁, V₂, G, _, _, Fn, Fn' => by
    rw [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    have h1 : piOp μ₁ V₁ Fn = fun _ => Fn default := by
      funext x
      unfold piOp recOp
      simp only [FiniteLaw.expect, Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty,
        one_mul]
      show (FiniteLaw.pi μ₁).weight default * Fn default = Fn default
      simp only [FiniteLaw.pi, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    have h2 : piOp μ₂ V₂ Fn' = fun _ => Fn' default := by
      funext x
      unfold piOp recOp
      simp only [FiniteLaw.expect, Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty,
        one_mul]
      show (FiniteLaw.pi μ₂).weight default * Fn' default = Fn' default
      simp only [FiniteLaw.pi, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    have hw : ∀ {Y : Fin 0 → Type u} [∀ k, Fintype (Y k)] (ρ : ∀ k, FiniteLaw (Y k))
        (y : ∀ k, Y k), (FiniteLaw.pi ρ).weight y = 1 := by
      intro Y _ ρ y
      simp only [FiniteLaw.pi, Finset.univ_eq_empty, Finset.prod_empty]
    have hn : ∀ {Y : Fin 0 → Type u} [∀ k, Fintype (Y k)] (ρ : ∀ k, FiniteLaw (Y k))
        (f : (∀ k, Y k) → ℝ), nrm (FiniteLaw.pi ρ) f = |f default| := by
      intro Y _ ρ f
      unfold nrm ip
      simp only [FiniteLaw.expect, Fintype.sum_unique, hw, one_mul]
      exact Real.sqrt_mul_self_eq_abs _
    rw [h1, h2, hn, hn]
    unfold ip
    simp only [FiniteLaw.expect, Fintype.sum_unique, hw, one_mul]
    rw [abs_mul]
  | n + 1, X, Z₁, Z₂, _, _, _, ν, μ₁, μ₂, V₁, V₂, G, hG, hV, Fn, Fn' => by
    have ih := frame_pi n (fun k : Fin n => ν k.succ) (fun k => μ₁ k.succ) (fun k => μ₂ k.succ)
      (fun k => V₁ k.succ) (fun k => V₂ k.succ) (fun k => G k.succ) (fun k => hG k.succ)
      (fun k => hV k.succ)
    have h := frame_tensor (ν 0) (FiniteLaw.pi (fun k : Fin n => ν k.succ)) (μ₁ 0)
      (μ₂ 0) (FiniteLaw.pi (fun k : Fin n => μ₁ k.succ)) (FiniteLaw.pi (fun k : Fin n => μ₂ k.succ))
      (V₁ 0) (V₂ 0) (fun x' z' => ∏ k : Fin n, V₁ k.succ (x' k) (z' k))
      (fun x' z' => ∏ k : Fin n, V₂ k.succ (x' k) (z' k)) (hG 0)
      (Finset.prod_nonneg (fun k _ => hG k.succ)) (hV 0) (fun w w' => ih w w')
      (fun q => Fn (Fin.cons q.1 q.2)) (fun q => Fn' (Fin.cons q.1 q.2))
    rw [ip_pi_succ, nrm_pi_succ μ₁, nrm_pi_succ μ₂, Fin.prod_univ_succ]
    have e1 : (fun p : X 0 × (∀ k : Fin n, X k.succ) => piOp μ₁ V₁ Fn (Fin.cons p.1 p.2)) =
        tensOp (μ₁ 0) (FiniteLaw.pi (fun k : Fin n => μ₁ k.succ)) (V₁ 0)
          (fun x' z' => ∏ k : Fin n, V₁ k.succ (x' k) (z' k))
          (fun q => Fn (Fin.cons q.1 q.2)) := funext (fun p => piOp_cons μ₁ V₁ Fn p)
    have e2 : (fun p : X 0 × (∀ k : Fin n, X k.succ) => piOp μ₂ V₂ Fn' (Fin.cons p.1 p.2)) =
        tensOp (μ₂ 0) (FiniteLaw.pi (fun k : Fin n => μ₂ k.succ)) (V₂ 0)
          (fun x' z' => ∏ k : Fin n, V₂ k.succ (x' k) (z' k))
          (fun q => Fn' (Fin.cons q.1 q.2)) := funext (fun p => piOp_cons μ₂ V₂ Fn' p)
    rw [e1, e2]
    exact h

/-- **`lem:weighted-frame` (b).** Let `(V^{(k)}_i)_{i ∈ I_k}` (`k : Fin n`) be families of kernel
operators `V^{(k)}_i : L²(μ_{k,i}) → L²(ν_k)` with
`|⟨V^{(k)}_i z, V^{(k)}_j z'⟩| ≤ G^{(k)}_{ij} ‖z‖ ‖z'‖` and `G^{(k)} ≥ 0`. Then the tensor products
`⊗_k V^{(k)}_{i_k}`, indexed by `∏_k I_k`, satisfy the hypothesis with the Kronecker product
`(⊗_k G^{(k)})_{(i_k),(j_k)} = ∏_k G^{(k)}_{i_k j_k}`. -/
theorem frame_pi_family {n : ℕ} {I : Fin n → Type u} {X : Fin n → Type u} [∀ k, Fintype (X k)]
    {Z : ∀ k, I k → Type u} [∀ k i, Fintype (Z k i)] (ν : ∀ k, FiniteLaw (X k))
    (μ : ∀ k i, FiniteLaw (Z k i)) (V : ∀ k i, X k → Z k i → ℝ) (G : ∀ k, I k → I k → ℝ)
    (hG : ∀ k i j, 0 ≤ G k i j)
    (hV : ∀ k i j z z', |ip (ν k) (recOp (μ k i) (V k i) z) (recOp (μ k j) (V k j) z')| ≤
      G k i j * nrm (μ k i) z * nrm (μ k j) z')
    (ii jj : ∀ k, I k) (Fn : (∀ k, Z k (ii k)) → ℝ) (Fn' : (∀ k, Z k (jj k)) → ℝ) :
    |ip (FiniteLaw.pi ν) (piOp (fun k => μ k (ii k)) (fun k => V k (ii k)) Fn)
        (piOp (fun k => μ k (jj k)) (fun k => V k (jj k)) Fn')| ≤
      (∏ k, G k (ii k) (jj k)) * nrm (FiniteLaw.pi (fun k => μ k (ii k))) Fn *
        nrm (FiniteLaw.pi (fun k => μ k (jj k))) Fn' :=
  frame_pi n ν (fun k => μ k (ii k)) (fun k => μ k (jj k)) (fun k => V k (ii k))
    (fun k => V k (jj k)) (fun k => G k (ii k) (jj k)) (fun k => hG k _ _) (fun k => hV k _ _)
    Fn Fn'

/-- The Kronecker product `∏_k G^{(k)}_{i_k j_k}` of symmetric matrices is symmetric, and it has
nonnegative entries when the `G^{(k)}` do. -/
theorem kronecker_pi {n : ℕ} {I : Fin n → Type u} (G : ∀ k, I k → I k → ℝ)
    (hGs : ∀ k i j, G k i j = G k j i) (hG : ∀ k i j, 0 ≤ G k i j) (ii jj : ∀ k, I k) :
    ∏ k, G k (ii k) (jj k) = ∏ k, G k (jj k) (ii k) ∧ 0 ≤ ∏ k, G k (ii k) (jj k) :=
  ⟨Finset.prod_congr rfl (fun k _ => hGs k _ _), Finset.prod_nonneg (fun k _ => hG k _ _)⟩

end FramePi

end Sarkozy.Cuts
