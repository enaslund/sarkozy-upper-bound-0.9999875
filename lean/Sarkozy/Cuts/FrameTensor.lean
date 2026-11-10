module

public import Sarkozy.Cuts.Swapped

/-!
# Cuts, VIII⁗: Kronecker products of weighted frames (`lem:weighted-frame` (b))

`13_cuts_correlations.tex`, `lem:weighted-frame` (b), for two families of kernel operators
between `L²` spaces of finite probability spaces. An operator `V : L²(μ) → L²(ν)` with kernel
`V(x; z)` acts by `(V h)(x) = E_{z∼μ} V(x; z) h(z)` (`recOp`). The frame hypothesis of
`lem:weighted-frame` is `‖V_i^* V_j‖ ≤ G_{ij}`, stated as `|⟨V_i z, V_j z'⟩| ≤ G_{ij} ‖z‖ ‖z'‖`
(as in `Sarkozy.Cuts.weighted_frame`). The tensor product `V ⊗ W` of `V : L²(μ) → L²(ν)` and
`W : L²(μ') → L²(ν')` is the operator `L²(μ ⊗ μ') → L²(ν ⊗ ν')` with the kernel
`V(x; z) W(x'; z')` (`tensOp`).

* `frame_tensor`: if `|⟨V₁ z, V₂ z'⟩| ≤ G ‖z‖ ‖z'‖` and `|⟨W₁ w, W₂ w'⟩| ≤ H ‖w‖ ‖w'‖`, then
  `|⟨(V₁ ⊗ W₁) Z, (V₂ ⊗ W₂) Z'⟩| ≤ G H ‖Z‖ ‖Z'‖`.
* `frame_kronecker`: (b) for two families `(V_i)_{i ∈ I}`, `(W_k)_{k ∈ K}` with matrices `G`, `H`:
  the family `(V_i ⊗ W_k)_{(i,k) ∈ I × K}` satisfies the hypothesis with the Kronecker product
  `G_{ij} H_{kl}`.

For more than two families, (b) follows by applying `frame_tensor` repeatedly: a tensor
product of kernel operators is again a kernel operator on the product laws (`tensOp_eq_recOp`).
The iteration over `n` families is `Sarkozy.Cuts.frame_pi_family` (in `Sarkozy.Cuts.FramePi`).

The proof factors `V ⊗ W = (V ⊗ 1)(1 ⊗ W)`. With `M = V₁^* V₂` (the kernel
`E_x V₁(x; z) V₂(x; z')`), `⟨(V₁ ⊗ W₁) Z, (V₂ ⊗ W₂) Z'⟩ = ⟨(1 ⊗ W₁) Z, (1 ⊗ W₂)(M ⊗ 1) Z'⟩`,
which is at most `H ‖Z‖ ‖(M ⊗ 1) Z'‖ ≤ G H ‖Z‖ ‖Z'‖`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering

section FrameTensor

variable {X X' Z₁ Z₂ Z₁' Z₂' : Type*} [Fintype X] [Fintype X'] [Fintype Z₁] [Fintype Z₂]
  [Fintype Z₁'] [Fintype Z₂']

/-- The tensor product `V ⊗ W : L²(μ ⊗ μ') → L²(ν ⊗ ν')` of kernel operators: the kernel
`V(x; z) W(x'; z')`. -/
noncomputable def tensOp {X X' Z Z' : Type*} [Fintype Z] [Fintype Z'] (μ : FiniteLaw Z)
    (μ' : FiniteLaw Z') (V : X → Z → ℝ) (W : X' → Z' → ℝ) (Fn : Z × Z' → ℝ) : X × X' → ℝ :=
  fun p => (μ.product μ').expect (fun q => V p.1 q.1 * W p.2 q.2 * Fn q)

/-- The kernel of `V₁^* V₂`: `M(z; z') = E_{x∼ν} V₁(x; z) V₂(x; z')`. -/
noncomputable def gramKer {X Z Z' : Type*} [Fintype X] (ν : FiniteLaw X) (V₁ : X → Z → ℝ)
    (V₂ : X → Z' → ℝ) (z : Z) (z' : Z') : ℝ :=
  ν.expect (fun x => V₁ x z * V₂ x z')

omit [Fintype X'] [Fintype Z₁'] [Fintype Z₂'] in
/-- `⟨V₁ a, V₂ b⟩_ν = ⟨a, M b⟩_{μ₁}` with `M = V₁^* V₂`. -/
theorem ip_recOp_recOp (ν : FiniteLaw X) (μ₁ : FiniteLaw Z₁) (μ₂ : FiniteLaw Z₂)
    (V₁ : X → Z₁ → ℝ) (V₂ : X → Z₂ → ℝ) (a : Z₁ → ℝ) (b : Z₂ → ℝ) :
    ip ν (recOp μ₁ V₁ a) (recOp μ₂ V₂ b) = ip μ₁ a (recOp μ₂ (gramKer ν V₁ V₂) b) := by
  rw [ip_comm, ← ip_recAdj, ip_comm]
  unfold ip
  refine μ₁.expect_congr (fun z => ?_)
  congr 1
  unfold recAdj recOp gramKer
  simp only [← FiniteLaw.expect_const_mul]
  rw [expect_comm]
  refine μ₂.expect_congr (fun w => ?_)
  rw [← FiniteLaw.expect_mul_const]
  exact ν.expect_congr (fun x => by ring)

omit [Fintype X'] [Fintype Z₁'] [Fintype Z₂'] in
/-- `‖V₁^* V₂‖ ≤ G` from the frame bound `|⟨V₁ z, V₂ z'⟩| ≤ G ‖z‖ ‖z'‖`. -/
theorem nrm_gram_le (ν : FiniteLaw X) (μ₁ : FiniteLaw Z₁) (μ₂ : FiniteLaw Z₂)
    (V₁ : X → Z₁ → ℝ) (V₂ : X → Z₂ → ℝ) {G : ℝ} (hG : 0 ≤ G)
    (hV : ∀ z z', |ip ν (recOp μ₁ V₁ z) (recOp μ₂ V₂ z')| ≤ G * nrm μ₁ z * nrm μ₂ z')
    (b : Z₂ → ℝ) : nrm μ₁ (recOp μ₂ (gramKer ν V₁ V₂) b) ≤ G * nrm μ₂ b := by
  set m := recOp μ₂ (gramKer ν V₁ V₂) b
  have h1 : nrm μ₁ m ^ 2 = ip ν (recOp μ₁ V₁ m) (recOp μ₂ V₂ b) := by
    rw [nrm_sq_eq, ip_recOp_recOp ν μ₁ μ₂ V₁ V₂ m b]
  have h2 := hV m b
  have h0 := nrm_nonneg μ₁ m
  have hb0 := nrm_nonneg μ₂ b
  have h3 : nrm μ₁ m ^ 2 ≤ G * nrm μ₁ m * nrm μ₂ b := by
    rw [h1]
    exact (le_abs_self _).trans h2
  by_contra hlt
  push Not at hlt
  have hpos : 0 < nrm μ₁ m := lt_of_le_of_lt (mul_nonneg hG hb0) hlt
  nlinarith

omit [Fintype X] [Fintype X'] in
/-- `V ⊗ W` is the kernel operator of the kernel `V(x; z) W(x'; z')` relative to `μ ⊗ μ'`; so
`frame_kronecker` applies again to a tensor family, which gives (b) for any finite number of
families. -/
theorem tensOp_eq_recOp (μ : FiniteLaw Z₁) (μ' : FiniteLaw Z₁') (V : X → Z₁ → ℝ)
    (W : X' → Z₁' → ℝ) (Fn : Z₁ × Z₁' → ℝ) :
    tensOp μ μ' V W Fn = recOp (μ.product μ') (fun p q => V p.1 q.1 * W p.2 q.2) Fn := rfl

omit [Fintype X] [Fintype X'] in
/-- `(V ⊗ W) Z = (V ⊗ 1)((1 ⊗ W) Z)`. -/
theorem tensOp_eq (μ : FiniteLaw Z₁) (μ' : FiniteLaw Z₁') (V : X → Z₁ → ℝ) (W : X' → Z₁' → ℝ)
    (Fn : Z₁ × Z₁' → ℝ) (x : X) (x' : X') :
    tensOp μ μ' V W Fn (x, x') =
      recOp μ V (fun z => recOp μ' W (fun z' => Fn (z, z')) x') x := by
  unfold tensOp recOp
  rw [FiniteLaw.expect_product]
  refine μ.expect_congr (fun z => ?_)
  rw [← FiniteLaw.expect_const_mul]
  exact μ'.expect_congr (fun z' => by ring)

/-- **`lem:weighted-frame` (b), two factors.** If `|⟨V₁ z, V₂ z'⟩| ≤ G ‖z‖ ‖z'‖` and
`|⟨W₁ w, W₂ w'⟩| ≤ H ‖w‖ ‖w'‖`, then `|⟨(V₁ ⊗ W₁) Z, (V₂ ⊗ W₂) Z'⟩| ≤ G H ‖Z‖ ‖Z'‖`. -/
theorem frame_tensor (ν : FiniteLaw X) (ν' : FiniteLaw X') (μ₁ : FiniteLaw Z₁)
    (μ₂ : FiniteLaw Z₂) (μ₁' : FiniteLaw Z₁') (μ₂' : FiniteLaw Z₂')
    (V₁ : X → Z₁ → ℝ) (V₂ : X → Z₂ → ℝ) (W₁ : X' → Z₁' → ℝ) (W₂ : X' → Z₂' → ℝ) {G H : ℝ}
    (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hV : ∀ z z', |ip ν (recOp μ₁ V₁ z) (recOp μ₂ V₂ z')| ≤ G * nrm μ₁ z * nrm μ₂ z')
    (hW : ∀ w w', |ip ν' (recOp μ₁' W₁ w) (recOp μ₂' W₂ w')| ≤ H * nrm μ₁' w * nrm μ₂' w')
    (Fn : Z₁ × Z₁' → ℝ) (Fn' : Z₂ × Z₂' → ℝ) :
    |ip (ν.product ν') (tensOp μ₁ μ₁' V₁ W₁ Fn) (tensOp μ₂ μ₂' V₂ W₂ Fn')| ≤
      G * H * nrm (μ₁.product μ₁') Fn * nrm (μ₂.product μ₂') Fn' := by
  -- `(1 ⊗ W) Z` and `(M ⊗ 1) Z'`
  set P : Z₁ → X' → ℝ := fun z x' => recOp μ₁' W₁ (fun z' => Fn (z, z')) x' with hP
  set Q : Z₂ → X' → ℝ := fun z x' => recOp μ₂' W₂ (fun z' => Fn' (z, z')) x' with hQ
  set m := gramKer ν V₁ V₂ with hm
  set R : Z₁ → Z₂' → ℝ := fun z z' => recOp μ₂ m (fun w => Fn' (w, z')) z with hR
  -- step 1: `⟨(V₁ ⊗ W₁) Z, (V₂ ⊗ W₂) Z'⟩ = E_{z ∼ μ₁} ⟨W₁ Z(z, ·), W₂ R(z, ·)⟩`
  have hstep : ip (ν.product ν') (tensOp μ₁ μ₁' V₁ W₁ Fn) (tensOp μ₂ μ₂' V₂ W₂ Fn') =
      μ₁.expect (fun z => ip ν' (recOp μ₁' W₁ (fun z' => Fn (z, z')))
        (recOp μ₂' W₂ (fun z' => R z z'))) := by
    unfold ip
    rw [FiniteLaw.expect_product, expect_comm]
    -- `E_{x'} E_x (V₁ P(·, x'))(x) (V₂ Q(·, x'))(x)`
    have e1 : ∀ x', ν.expect (fun x => tensOp μ₁ μ₁' V₁ W₁ Fn (x, x') *
        tensOp μ₂ μ₂' V₂ W₂ Fn' (x, x')) =
        μ₁.expect (fun z => P z x' * recOp μ₂ m (fun w => Q w x') z) := by
      intro x'
      have h := ip_recOp_recOp ν μ₁ μ₂ V₁ V₂ (fun z => P z x') (fun w => Q w x')
      unfold ip at h
      rw [← h]
      exact ν.expect_congr (fun x => by rw [tensOp_eq, tensOp_eq])
    rw [ν'.expect_congr e1, expect_comm]
    refine μ₁.expect_congr (fun z => ?_)
    refine ν'.expect_congr (fun x' => ?_)
    -- `(M Q(·, x'))(z) = (W₂ R(z, ·))(x')`
    congr 1
    simp only [hQ, hR, recOp]
    simp only [← FiniteLaw.expect_const_mul]
    rw [expect_comm]
    refine μ₂'.expect_congr (fun z' => ?_)
    exact μ₂.expect_congr (fun w => by ring)
  -- step 2: the fibrewise frame bound and Cauchy–Schwarz
  rw [hstep]
  have hfib : ∀ z, |ip ν' (recOp μ₁' W₁ (fun z' => Fn (z, z'))) (recOp μ₂' W₂ (fun z' => R z z'))| ≤
      H * (nrm μ₁' (fun z' => Fn (z, z')) * nrm μ₂' (fun z' => R z z')) := fun z => by
    have := hW (fun z' => Fn (z, z')) (fun z' => R z z')
    linarith
  have hCS := μ₁.abs_expect_mul_le (fun z => nrm μ₁' (fun z' => Fn (z, z')))
    (fun z => nrm μ₂' (fun z' => R z z'))
  have hFn : μ₁.expect (fun z => nrm μ₁' (fun z' => Fn (z, z')) ^ 2) =
      nrm (μ₁.product μ₁') Fn ^ 2 := by
    rw [nrm_sq_expect (μ₁.product μ₁') Fn, FiniteLaw.expect_product]
    exact μ₁.expect_congr (fun z => nrm_sq_expect _ _)
  have hRn : μ₁.expect (fun z => nrm μ₂' (fun z' => R z z') ^ 2) ≤
      G ^ 2 * nrm (μ₂.product μ₂') Fn' ^ 2 := by
    have e : μ₁.expect (fun z => nrm μ₂' (fun z' => R z z') ^ 2) =
        μ₂'.expect (fun z' => nrm μ₁ (fun z => R z z') ^ 2) := by
      simp only [nrm_sq_expect]
      exact expect_comm _ _ _
    rw [e, nrm_sq_expect (μ₂.product μ₂') Fn', FiniteLaw.expect_product, expect_comm,
      ← μ₂'.expect_const_mul]
    refine μ₂'.expect_mono (fun z' => ?_)
    have h := nrm_gram_le ν μ₁ μ₂ V₁ V₂ hG hV (fun w => Fn' (w, z'))
    have hsq := pow_le_pow_left₀ (nrm_nonneg _ _) h 2
    rw [mul_pow, nrm_sq_expect μ₂] at hsq
    exact hsq
  have h1 := μ₁.abs_expect_le (fun z => ip ν' (recOp μ₁' W₁ (fun z' => Fn (z, z')))
    (recOp μ₂' W₂ (fun z' => R z z')))
  have h2 : μ₁.expect (fun z => |ip ν' (recOp μ₁' W₁ (fun z' => Fn (z, z')))
      (recOp μ₂' W₂ (fun z' => R z z'))|) ≤
      H * μ₁.expect (fun z => nrm μ₁' (fun z' => Fn (z, z')) * nrm μ₂' (fun z' => R z z')) := by
    rw [← μ₁.expect_const_mul]
    exact μ₁.expect_mono hfib
  have h3 : μ₁.expect (fun z => nrm μ₁' (fun z' => Fn (z, z')) * nrm μ₂' (fun z' => R z z')) ≤
      nrm (μ₁.product μ₁') Fn * (G * nrm (μ₂.product μ₂') Fn') := by
    refine (le_abs_self _).trans (hCS.trans ?_)
    rw [hFn, Real.sqrt_sq (nrm_nonneg _ _)]
    refine mul_le_mul_of_nonneg_left ?_ (nrm_nonneg _ _)
    calc Real.sqrt (μ₁.expect (fun z => nrm μ₂' (fun z' => R z z') ^ 2))
        ≤ Real.sqrt (G ^ 2 * nrm (μ₂.product μ₂') Fn' ^ 2) := Real.sqrt_le_sqrt hRn
      _ = G * nrm (μ₂.product μ₂') Fn' := by
          rw [← mul_pow, Real.sqrt_sq (mul_nonneg hG (nrm_nonneg _ _))]
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ H * (nrm (μ₁.product μ₁') Fn * (G * nrm (μ₂.product μ₂') Fn')) :=
        mul_le_mul_of_nonneg_left h3 hH
    _ = G * H * nrm (μ₁.product μ₁') Fn * nrm (μ₂.product μ₂') Fn' := by ring

/-- **`lem:weighted-frame` (b).** Let `V_i : L²(μ_i) → L²(ν)` (`i ∈ I`) and
`W_k : L²(μ'_k) → L²(ν')` (`k ∈ K`) be kernel operators with `|⟨V_i z, V_j z'⟩| ≤ G_{ij} ‖z‖ ‖z'‖`
and `|⟨W_k w, W_l w'⟩| ≤ H_{kl} ‖w‖ ‖w'‖`, `G`, `H ≥ 0`. Then the tensor family
`(V_i ⊗ W_k)_{(i, k) ∈ I × K}` satisfies the same hypothesis with the Kronecker product
`(G ⊗ H)_{(i,k),(j,l)} = G_{ij} H_{kl}` (symmetric with nonnegative entries when `G`, `H` are,
`kronecker_symm`, `kronecker_nonneg`). -/
theorem frame_kronecker {I K : Type*} {ZI : I → Type*} {ZK : K → Type*} [∀ i, Fintype (ZI i)]
    [∀ k, Fintype (ZK k)] (ν : FiniteLaw X) (ν' : FiniteLaw X') (μ : ∀ i, FiniteLaw (ZI i))
    (μ' : ∀ k, FiniteLaw (ZK k)) (V : ∀ i, X → ZI i → ℝ) (W : ∀ k, X' → ZK k → ℝ)
    (G : I → I → ℝ) (H : K → K → ℝ) (hG0 : ∀ i j, 0 ≤ G i j) (hH0 : ∀ k l, 0 ≤ H k l)
    (hV : ∀ i j z z', |ip ν (recOp (μ i) (V i) z) (recOp (μ j) (V j) z')| ≤
      G i j * nrm (μ i) z * nrm (μ j) z')
    (hW : ∀ k l w w', |ip ν' (recOp (μ' k) (W k) w) (recOp (μ' l) (W l) w')| ≤
      H k l * nrm (μ' k) w * nrm (μ' l) w')
    (ik jl : I × K) (Fn : ZI ik.1 × ZK ik.2 → ℝ) (Fn' : ZI jl.1 × ZK jl.2 → ℝ) :
    |ip (ν.product ν') (tensOp (μ ik.1) (μ' ik.2) (V ik.1) (W ik.2) Fn)
        (tensOp (μ jl.1) (μ' jl.2) (V jl.1) (W jl.2) Fn')| ≤
      G ik.1 jl.1 * H ik.2 jl.2 * nrm ((μ ik.1).product (μ' ik.2)) Fn *
        nrm ((μ jl.1).product (μ' jl.2)) Fn' :=
  frame_tensor ν ν' (μ ik.1) (μ jl.1) (μ' ik.2) (μ' jl.2) (V ik.1) (V jl.1) (W ik.2) (W jl.2)
    (hG0 _ _) (hH0 _ _) (hV _ _) (hW _ _) Fn Fn'

omit [Fintype X] [Fintype X'] [Fintype Z₁] [Fintype Z₂] [Fintype Z₁'] [Fintype Z₂'] in
/-- The Kronecker product of symmetric matrices is symmetric. -/
theorem kronecker_symm {I K : Type*} (G : I → I → ℝ) (H : K → K → ℝ)
    (hG : ∀ i j, G i j = G j i) (hH : ∀ k l, H k l = H l k) (ik jl : I × K) :
    G ik.1 jl.1 * H ik.2 jl.2 = G jl.1 ik.1 * H jl.2 ik.2 := by
  rw [hG, hH]

omit [Fintype X] [Fintype X'] [Fintype Z₁] [Fintype Z₂] [Fintype Z₁'] [Fintype Z₂'] in
/-- The Kronecker product of matrices with nonnegative entries has nonnegative entries. -/
theorem kronecker_nonneg {I K : Type*} (G : I → I → ℝ) (H : K → K → ℝ)
    (hG : ∀ i j, 0 ≤ G i j) (hH : ∀ k l, 0 ≤ H k l) (ik jl : I × K) :
    0 ≤ G ik.1 jl.1 * H ik.2 jl.2 :=
  mul_nonneg (hG _ _) (hH _ _)

end FrameTensor

end Sarkozy.Cuts
