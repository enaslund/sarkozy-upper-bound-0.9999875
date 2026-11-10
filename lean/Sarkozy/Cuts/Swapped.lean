module

public import Sarkozy.Cuts.Envelope
public import Sarkozy.ProbabilityConstructions

/-!
# Cuts, XI: swapped rectangular kernels (`lem:swapped-rectangle`)

`13_cuts_correlations.tex`, paragraph "Swapped rectangular kernels". Let `(X, α)`, `(Y, β)` be
finite probability spaces and `A(x; y)` a real kernel. Then `(A h)(x) = E_{y∼β} A(x;y) h(y)`
(`recOp`) and `(A^* f)(y) = E_{x∼α} A(x;y) f(x)` (`recAdj`). The operator `T[A,A]` on
`L²(α ⊗ β)` has kernel `A(x;y') A(x';y)` (`swapOp`).

* `swapOp_tensor`: (a), `T[A,A](f ⊗ g) = Ag ⊗ A^*f`.
* `swapKernel_symm`: (a), `T[A,A]` is self-adjoint.
* `nrm_recAdj_le`, `nrm_swapOp_le`, `nrm_recOp_sq_le_of_swapOp`: (a), `‖T[A,A]‖ = ‖A‖²`, as two
  inequalities between bounds. The claims `T[A,A] ⪰ -sc I` and `‖T[A,A] h‖ ≤ sc ‖h‖` for
  `h ⊥ u₀ ⊗ v₀` are in `Sarkozy.Cuts.SwappedLower`. The eigenvalue list, which comes from a
  singular value decomposition, is not formalized.
* `nrm_prodSynth_le`: (b), first statement, `‖P · R‖ ≤ ξ ‖P‖`.
* `entangled_unit`, `entangled_swap`: (c), on a finite label set `Λ` with `|Λ| = p ≥ 2`.
* `multiplier_split`: (d), last statement, no cross terms.
* `swap_multiplier_factor`, `swap_multiplier_norm`: (d), the factorization
  `T[A,A] ∘ M = (𝒴 ⊗ I) Swap (𝒴'^* ⊗ I)` and `‖T[A,A] ∘ M‖ ≤ ‖𝒴‖ ‖𝒴'‖`.

The Schur-product statement of (b) is in `Sarkozy.Cuts.Schur`. Not formalized: the eigenvalue
list of (a), which uses a singular value decomposition.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering

section Fubini

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem expect_comm (α : FiniteLaw X) (β : FiniteLaw Y) (φ : X → Y → ℝ) :
    α.expect (fun x => β.expect (fun y => φ x y)) = β.expect (fun y => α.expect (fun x => φ x y)) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => by ring))

omit [Fintype Y] in
theorem nrm_sq_expect (μ : FiniteLaw X) (f : X → ℝ) : nrm μ f ^ 2 = μ.expect (fun x => f x ^ 2) := by
  rw [nrm_sq_eq]
  unfold ip
  exact μ.expect_congr (fun x => by ring)

omit [Fintype Y] in
theorem nrm_le_of_sq_le {X' : Type*} [Fintype X'] (μ : FiniteLaw X) (ν : FiniteLaw X') {f : X → ℝ}
    {g : X' → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : nrm μ f ^ 2 ≤ c ^ 2 * nrm ν g ^ 2) : nrm μ f ≤ c * nrm ν g := by
  have h0 : 0 ≤ c * nrm ν g := mul_nonneg hc (nrm_nonneg _ _)
  rw [← mul_pow] at h
  exact (abs_le_of_sq_le_sq' h h0).2

end Fubini

section Rectangle

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- `(A h)(x) = E_{y∼β} A(x; y) h(y)`. -/
noncomputable def recOp (β : FiniteLaw Y) (A : X → Y → ℝ) (h : Y → ℝ) : X → ℝ :=
  fun x => β.expect (fun y => A x y * h y)

/-- `(A^* f)(y) = E_{x∼α} A(x; y) f(x)`. -/
noncomputable def recAdj (α : FiniteLaw X) (A : X → Y → ℝ) (f : X → ℝ) : Y → ℝ :=
  fun y => α.expect (fun x => A x y * f x)

/-- `T[A,A]`: the kernel `A(x; y') A(x'; y)` relative to `α ⊗ β`. -/
noncomputable def swapOp (α : FiniteLaw X) (β : FiniteLaw Y) (A : X → Y → ℝ) (Fn : X × Y → ℝ) :
    X × Y → ℝ :=
  fun p => (α.product β).expect (fun q => A p.1 q.2 * A q.1 p.2 * Fn q)

/-- **`lem:swapped-rectangle` (a).** `T[A,A](f ⊗ g) = Ag ⊗ A^* f`. -/
theorem swapOp_tensor (α : FiniteLaw X) (β : FiniteLaw Y) (A : X → Y → ℝ) (f : X → ℝ)
    (g : Y → ℝ) (p : X × Y) :
    swapOp α β A (fun q => f q.1 * g q.2) p = recOp β A g p.1 * recAdj α A f p.2 := by
  unfold swapOp recOp recAdj
  rw [FiniteLaw.expect_product, ← FiniteLaw.expect_const_mul]
  refine α.expect_congr (fun x' => ?_)
  rw [← FiniteLaw.expect_mul_const]
  refine β.expect_congr (fun y' => ?_)
  ring

/-- **`lem:swapped-rectangle` (a).** The kernel of `T[A,A]` is symmetric, so `T[A,A]` is
self-adjoint. -/
theorem swapKernel_symm (α : FiniteLaw X) (β : FiniteLaw Y) (A : X → Y → ℝ)
    (Fn Hn : X × Y → ℝ) :
    kernelForm (α.product β) (α.product β) (fun p q => A p.1 q.2 * A q.1 p.2) Fn Hn =
      kernelForm (α.product β) (α.product β) (fun p q => A p.1 q.2 * A q.1 p.2) Hn Fn :=
  kernelForm_symm _ _ (fun p q => by ring) Fn Hn

/-- The adjoint identity `⟨A^* f, h⟩_β = ⟨f, A h⟩_α`. -/
theorem ip_recAdj (α : FiniteLaw X) (β : FiniteLaw Y) (A : X → Y → ℝ) (f : X → ℝ)
    (h : Y → ℝ) : ip β (recAdj α A f) h = ip α f (recOp β A h) := by
  unfold ip recAdj recOp
  simp only [FiniteLaw.expect, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))

/-- `‖A^*‖ ≤ ‖A‖`. -/
theorem nrm_recAdj_le (α : FiniteLaw X) (β : FiniteLaw Y) (A : X → Y → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hA : ∀ h, nrm α (recOp β A h) ≤ a * nrm β h) (f : X → ℝ) :
    nrm β (recAdj α A f) ≤ a * nrm α f := by
  have h1 : nrm β (recAdj α A f) ^ 2 = ip α f (recOp β A (recAdj α A f)) := by
    rw [nrm_sq_eq, ip_recAdj]
  have h2 := abs_ip_le α f (recOp β A (recAdj α A f))
  have h3 := hA (recAdj α A f)
  have h0 := nrm_nonneg β (recAdj α A f)
  have hf0 := nrm_nonneg α f
  have h4 : nrm β (recAdj α A f) ^ 2 ≤ nrm α f * (a * nrm β (recAdj α A f)) := by
    rw [h1]
    exact (le_abs_self _).trans (h2.trans (mul_le_mul_of_nonneg_left h3 hf0))
  by_contra hlt
  push Not at hlt
  have hnpos : 0 < nrm β (recAdj α A f) := lt_of_le_of_lt (mul_nonneg ha hf0) hlt
  have := mul_lt_mul_of_pos_right hlt hnpos
  nlinarith

/-- `T[A,A] F (x, y) = (A G_y)(x)` with `G_y(y') = (A^* F(·, y'))(y)`. -/
theorem swapOp_eq_recOp (α : FiniteLaw X) (β : FiniteLaw Y) (A : X → Y → ℝ) (Fn : X × Y → ℝ)
    (x : X) (y : Y) :
    swapOp α β A Fn (x, y) = recOp β A (fun y' => recAdj α A (fun x' => Fn (x', y')) y) x := by
  unfold swapOp recOp recAdj
  rw [FiniteLaw.expect_product, expect_comm]
  refine β.expect_congr (fun y' => ?_)
  rw [← FiniteLaw.expect_const_mul]
  refine α.expect_congr (fun x' => ?_)
  ring

/-- **`lem:swapped-rectangle` (a).** `‖T[A,A]‖ ≤ ‖A‖²`. -/
theorem nrm_swapOp_le (α : FiniteLaw X) (β : FiniteLaw Y) (A : X → Y → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hA : ∀ h, nrm α (recOp β A h) ≤ a * nrm β h) (Fn : X × Y → ℝ) :
    nrm (α.product β) (swapOp α β A Fn) ≤ a ^ 2 * nrm (α.product β) Fn := by
  set G : Y → Y → ℝ := fun y y' => recAdj α A (fun x' => Fn (x', y')) y with hG
  apply nrm_le_of_sq_le _ _ (sq_nonneg a)
  rw [nrm_sq_expect, nrm_sq_expect, FiniteLaw.expect_product, FiniteLaw.expect_product]
  -- the inner bound in `x`, for each `y`
  have hrow : ∀ y, α.expect (fun x => swapOp α β A Fn (x, y) ^ 2) ≤
      a ^ 2 * β.expect (fun y' => G y y' ^ 2) := by
    intro y
    have h := hA (G y)
    have hsq := pow_le_pow_left₀ (nrm_nonneg _ _) h 2
    rw [mul_pow, nrm_sq_expect, nrm_sq_expect] at hsq
    calc α.expect (fun x => swapOp α β A Fn (x, y) ^ 2)
        = α.expect (fun x => recOp β A (G y) x ^ 2) :=
          α.expect_congr (fun x => by rw [swapOp_eq_recOp])
      _ ≤ a ^ 2 * β.expect (fun y' => G y y' ^ 2) := hsq
  -- the column bound in `y`, for each `y'`
  have hcol : ∀ y', β.expect (fun y => G y y' ^ 2) ≤
      a ^ 2 * α.expect (fun x' => Fn (x', y') ^ 2) := by
    intro y'
    have h := nrm_recAdj_le α β A ha hA (fun x' => Fn (x', y'))
    have hsq := pow_le_pow_left₀ (nrm_nonneg _ _) h 2
    rw [mul_pow, nrm_sq_expect, nrm_sq_expect] at hsq
    exact hsq
  calc α.expect (fun x => β.expect (fun y => swapOp α β A Fn (x, y) ^ 2))
      = β.expect (fun y => α.expect (fun x => swapOp α β A Fn (x, y) ^ 2)) := expect_comm _ _ _
    _ ≤ β.expect (fun y => a ^ 2 * β.expect (fun y' => G y y' ^ 2)) := β.expect_mono hrow
    _ = a ^ 2 * β.expect (fun y' => β.expect (fun y => G y y' ^ 2)) := by
        rw [FiniteLaw.expect_const_mul, expect_comm]
    _ ≤ a ^ 2 * β.expect (fun y' => a ^ 2 * α.expect (fun x' => Fn (x', y') ^ 2)) :=
        mul_le_mul_of_nonneg_left (β.expect_mono hcol) (sq_nonneg a)
    _ = (a ^ 2) ^ 2 * α.expect (fun x => β.expect (fun y => Fn (x, y) ^ 2)) := by
        rw [FiniteLaw.expect_const_mul, expect_comm α β (fun x y => Fn (x, y) ^ 2)]
        ring

/-- The norm of a tensor product of functions: `‖u ⊗ v‖ = ‖u‖ ‖v‖`. -/
theorem nrm_tensor (α : FiniteLaw X) (β : FiniteLaw Y) (u : X → ℝ) (v : Y → ℝ) :
    nrm (α.product β) (fun p => u p.1 * v p.2) = nrm α u * nrm β v := by
  unfold nrm ip
  rw [← Real.sqrt_mul (α.expect_nonneg (fun x => mul_self_nonneg _))]
  congr 1
  rw [← FiniteLaw.expect_product_mul]
  exact (α.product β).expect_congr (fun p => by ring)

/-- **`lem:swapped-rectangle` (a), `‖T[A,A]‖ ≥ ‖A‖²`.** If `‖T[A,A]‖ ≤ c`, then
`‖A g‖² ≤ c ‖g‖²` for every `g`, that is `‖A‖² ≤ c`. With `nrm_swapOp_le` this gives
`‖T[A,A]‖ = ‖A‖²`. -/
theorem nrm_recOp_sq_le_of_swapOp (α : FiniteLaw X) (β : FiniteLaw Y) (A : X → Y → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hT : ∀ Fn, nrm (α.product β) (swapOp α β A Fn) ≤ c * nrm (α.product β) Fn)
    (g : Y → ℝ) : nrm α (recOp β A g) ^ 2 ≤ c * nrm β g ^ 2 := by
  set f := recOp β A g
  have hTF := hT (fun q => f q.1 * g q.2)
  have e : swapOp α β A (fun q => f q.1 * g q.2) = fun p => recOp β A g p.1 * recAdj α A f p.2 :=
    funext (fun p => swapOp_tensor α β A f g p)
  rw [e, nrm_tensor, nrm_tensor] at hTF
  -- `‖Ag‖² = ⟨A*Ag, g⟩ ≤ ‖A*Ag‖ ‖g‖`
  have h2 : nrm α f ^ 2 ≤ nrm β (recAdj α A f) * nrm β g := by
    rw [nrm_sq_eq]
    have := ip_recAdj α β A f g
    rw [← this]
    exact (le_abs_self _).trans (abs_ip_le β _ _)
  set n := nrm α f
  set m := nrm β (recAdj α A f)
  set k := nrm β g
  have hn : 0 ≤ n := nrm_nonneg _ _
  have hm : 0 ≤ m := nrm_nonneg _ _
  have hk : 0 ≤ k := nrm_nonneg _ _
  rcases hn.lt_or_eq with hpos | hzero
  · -- `n m ≤ c n k` gives `m ≤ c k`
    have hmk : m ≤ c * k := by
      have h := hTF
      have : n * m ≤ n * (c * k) := by nlinarith
      exact le_of_mul_le_mul_left this hpos
    calc n ^ 2 ≤ m * k := h2
      _ ≤ c * k * k := mul_le_mul_of_nonneg_right hmk hk
      _ = c * k ^ 2 := by ring
  · rw [← hzero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

end Rectangle

section Synthesis

variable {Z S S' : Type*} [Fintype Z] [Fintype S] [Fintype S']

/-- The product synthesis `(P · R) F(z) = E_{s∼π, t∼π'} P(z; s) R(z; t) F(s, t)`. -/
noncomputable def prodSynth (π : FiniteLaw S) (π' : FiniteLaw S') (P : Z → S → ℝ) (R : Z → S' → ℝ)
    (Fn : S × S' → ℝ) : Z → ℝ :=
  fun z => (π.product π').expect (fun q => P z q.1 * R z q.2 * Fn q)

/-- **`lem:swapped-rectangle` (b), first statement.** If `‖P‖ ≤ c` and
`sup_z ‖R(z; ·)‖_{L²(π')} ≤ ξ`, then `‖P · R‖ ≤ ξ c` from `L²(π ⊗ π')` to `L²(γ)`. -/
theorem nrm_prodSynth_le (γ : FiniteLaw Z) (π : FiniteLaw S) (π' : FiniteLaw S')
    (P : Z → S → ℝ) (R : Z → S' → ℝ) {c ξ : ℝ} (hc : 0 ≤ c) (hξ : 0 ≤ ξ)
    (hP : ∀ h, nrm γ (recOp π P h) ≤ c * nrm π h)
    (hR : ∀ z, π'.expect (fun t => R z t ^ 2) ≤ ξ ^ 2) (Fn : S × S' → ℝ) :
    nrm γ (prodSynth π π' P R Fn) ≤ ξ * c * nrm (π.product π') Fn := by
  have hrep : ∀ z, prodSynth π π' P R Fn z =
      π'.expect (fun t => R z t * recOp π P (fun s => Fn (s, t)) z) := by
    intro z
    unfold prodSynth recOp
    rw [FiniteLaw.expect_product, expect_comm]
    refine π'.expect_congr (fun t => ?_)
    rw [← FiniteLaw.expect_const_mul]
    refine π.expect_congr (fun s => ?_)
    ring
  -- Cauchy–Schwarz in `t`
  have hcs : ∀ z, prodSynth π π' P R Fn z ^ 2 ≤
      ξ ^ 2 * π'.expect (fun t => recOp π P (fun s => Fn (s, t)) z ^ 2) := by
    intro z
    rw [hrep z]
    have h := abs_ip_le π' (fun t => R z t) (fun t => recOp π P (fun s => Fn (s, t)) z)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs, mul_pow, nrm_sq_expect, nrm_sq_expect] at hsq
    have e : ip π' (fun t => R z t) (fun t => recOp π P (fun s => Fn (s, t)) z) =
        π'.expect (fun t => R z t * recOp π P (fun s => Fn (s, t)) z) := rfl
    rw [e] at hsq
    exact hsq.trans (mul_le_mul_of_nonneg_right (hR z)
      (π'.expect_nonneg (fun t => sq_nonneg _)))
  have hcol : ∀ t, γ.expect (fun z => recOp π P (fun s => Fn (s, t)) z ^ 2) ≤
      c ^ 2 * π.expect (fun s => Fn (s, t) ^ 2) := by
    intro t
    have h := hP (fun s => Fn (s, t))
    have hsq := pow_le_pow_left₀ (nrm_nonneg _ _) h 2
    rw [mul_pow, nrm_sq_expect, nrm_sq_expect] at hsq
    exact hsq
  have hfin : nrm γ (prodSynth π π' P R Fn) ^ 2 ≤ (ξ * c) ^ 2 * nrm (π.product π') Fn ^ 2 := by
    rw [nrm_sq_expect, nrm_sq_expect, FiniteLaw.expect_product]
    calc γ.expect (fun z => prodSynth π π' P R Fn z ^ 2)
        ≤ γ.expect (fun z => ξ ^ 2 * π'.expect (fun t => recOp π P (fun s => Fn (s, t)) z ^ 2)) :=
          γ.expect_mono hcs
      _ = ξ ^ 2 * π'.expect (fun t => γ.expect (fun z => recOp π P (fun s => Fn (s, t)) z ^ 2)) := by
          rw [FiniteLaw.expect_const_mul, expect_comm]
      _ ≤ ξ ^ 2 * π'.expect (fun t => c ^ 2 * π.expect (fun s => Fn (s, t) ^ 2)) :=
          mul_le_mul_of_nonneg_left (π'.expect_mono hcol) (sq_nonneg ξ)
      _ = (ξ * c) ^ 2 * π.expect (fun s => π'.expect (fun t => Fn (s, t) ^ 2)) := by
          rw [FiniteLaw.expect_const_mul, ← expect_comm]
          ring
  exact nrm_le_of_sq_le _ _ (mul_nonneg hξ hc) hfin

end Synthesis

section Entangled

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]

/-- `e₀(a, s) = (p 1_{a=s} - 1)/√(p - 1)`, `p = |Λ|`. -/
noncomputable def entangled (a s : Λ) : ℝ :=
  ((Fintype.card Λ : ℝ) * (if a = s then 1 else 0) - 1) / √((Fintype.card Λ : ℝ) - 1)

omit [Nonempty Λ] in
theorem sum_indicator (a : Λ) : ∑ s : Λ, (if a = s then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]

omit [Nonempty Λ] in
/-- `∑_s (p 1_{a=s} - 1)(p 1_{c=s} - 1) = p² 1_{a=c} - p`. -/
theorem sum_entangled_core (a c : Λ) :
    ∑ s : Λ, ((Fintype.card Λ : ℝ) * (if a = s then 1 else 0) - 1) *
      ((Fintype.card Λ : ℝ) * (if c = s then 1 else 0) - 1) =
      (Fintype.card Λ : ℝ) ^ 2 * (if a = c then 1 else 0) - Fintype.card Λ := by
  set p : ℝ := ((Fintype.card Λ : ℕ) : ℝ)
  have e : ∀ s : Λ, (p * (if a = s then 1 else 0) - 1) * (p * (if c = s then 1 else 0) - 1) =
      p ^ 2 * ((if a = s then 1 else 0) * (if c = s then 1 else 0)) -
        p * (if a = s then 1 else 0) - p * (if c = s then 1 else 0) + 1 := fun s => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_indicator,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hprod : ∑ s : Λ, (if a = s then (1 : ℝ) else 0) * (if c = s then 1 else 0) =
      if a = c then 1 else 0 := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    by_cases hac : a = c
    · rw [ite_eq_left hac, ite_eq_left hac.symm]
    · rw [ite_eq_right hac, ite_eq_right (Ne.symm hac)]
  rw [hprod]
  ring

/-- **`lem:swapped-rectangle` (c).** `e₀` is a unit vector of `L²₀ ⊗ L²₀`: its rows and columns
are centred and `E e₀² = 1` (`p ≥ 2`). -/
theorem entangled_unit (hp : 2 ≤ Fintype.card Λ) :
    (∀ s, (FiniteLaw.uniform Λ).expect (fun a => entangled a s) = 0) ∧
    (∀ a, (FiniteLaw.uniform Λ).expect (fun s => entangled a s) = 0) ∧
    ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ)).expect
      (fun q => entangled q.1 q.2 ^ 2) = 1 := by
  set p : ℝ := ((Fintype.card Λ : ℕ) : ℝ) with hp_def
  have hp1 : (1 : ℝ) < p := by rw [hp_def]; exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hs : 0 < √(p - 1) := Real.sqrt_pos.mpr (by linarith)
  have hss : √(p - 1) ^ 2 = p - 1 := Real.sq_sqrt (by linarith)
  refine ⟨fun s => ?_, fun a => ?_, ?_⟩
  · rw [FiniteLaw.expect_uniform]
    unfold entangled
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have : ∑ a : Λ, (if a = s then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_ite_eq']; simp only [Finset.mem_univ, ite_true]
    rw [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hp_def]
    simp
  · rw [FiniteLaw.expect_uniform]
    unfold entangled
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_indicator,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hp_def]
    simp
  · rw [FiniteLaw.expect_product]
    simp only [FiniteLaw.expect_uniform]
    unfold entangled
    have e : ∀ a : Λ, ∑ s : Λ, ((p * (if a = s then 1 else 0) - 1) / √(p - 1)) ^ 2 =
        (p ^ 2 - p) / (p - 1) := by
      intro a
      have h := sum_entangled_core a a
      simp only [ite_true, mul_one] at h
      rw [← hp_def] at h
      simp only [div_pow, hss]
      rw [← Finset.sum_div]
      congr 1
      rw [← h]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    simp only [e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hp_def]
    have hpm : p - 1 ≠ 0 := (by linarith : (0 : ℝ) < p - 1).ne'
    field_simp

/-- **`lem:swapped-rectangle` (c), the entangled swap.** For `h ∈ L²₀(Λ)`,
`(e₀ ⊗ I)^* Swap₁₃ (e₀ ⊗ I) h = h/(p - 1)`, that is
`E_{a,s}[e₀(a, s) e₀(c, s) h(a)] = h(c)/(p - 1)` for every `c`. -/
theorem entangled_swap (hp : 2 ≤ Fintype.card Λ) (h : Λ → ℝ)
    (hh : (FiniteLaw.uniform Λ).expect h = 0) (c : Λ) :
    ((FiniteLaw.uniform Λ).product (FiniteLaw.uniform Λ)).expect
      (fun q => entangled q.1 q.2 * entangled c q.2 * h q.1) =
      h c / ((Fintype.card Λ : ℝ) - 1) := by
  set p : ℝ := ((Fintype.card Λ : ℕ) : ℝ) with hp_def
  have hp1 : (1 : ℝ) < p := by rw [hp_def]; exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hss : √(p - 1) * √(p - 1) = p - 1 := Real.mul_self_sqrt (by linarith)
  have hs0 : √(p - 1) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  rw [FiniteLaw.expect_uniform] at hh
  have hsum : ∑ a : Λ, h a = 0 := by
    have hc : (Fintype.card Λ : ℝ) ≠ 0 := hp0.ne'
    rwa [div_eq_zero_iff, or_iff_left hc] at hh
  rw [FiniteLaw.expect_product]
  simp only [FiniteLaw.expect_uniform]
  unfold entangled
  rw [← hp_def]
  have inner : ∀ a : Λ, ∑ s : Λ, (p * (if a = s then 1 else 0) - 1) / √(p - 1) *
      ((p * (if c = s then 1 else 0) - 1) / √(p - 1)) * h a =
      h a * (p ^ 2 * (if a = c then 1 else 0) - p) / (p - 1) := by
    intro a
    have hcore := sum_entangled_core a c
    rw [← hp_def] at hcore
    have e1 : (∑ s : Λ, (p * (if a = s then 1 else 0) - 1) / √(p - 1) *
        ((p * (if c = s then 1 else 0) - 1) / √(p - 1)) * h a) =
        h a * (∑ s : Λ, (p * (if a = s then 1 else 0) - 1) *
          (p * (if c = s then 1 else 0) - 1)) / (√(p - 1) * √(p - 1)) := by
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [div_mul_div_comm]
      ring
    rw [e1, hcore, hss]
  simp only [inner]
  have houter : ∑ a : Λ, h a * (p ^ 2 * (if a = c then 1 else 0) - p) / (p - 1) / p =
      (p ^ 2 * h c - p * ∑ a : Λ, h a) / ((p - 1) * p) := by
    rw [← Finset.sum_div, ← Finset.sum_div, div_div]
    congr 1
    have e : ∀ a : Λ, h a * (p ^ 2 * (if a = c then 1 else 0) - p) =
        p ^ 2 * (if a = c then h a else 0) - p * h a := fun a => by split_ifs <;> ring
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  rw [houter, hsum]
  field_simp
  ring

end Entangled

section Multiplier

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]

omit [Fintype X] [Fintype Y] in
/-- **`lem:swapped-rectangle` (d), last statement: no cross terms.** If `φ = φ¹ + φ²` and
`φ' = φ'¹ + φ'²` with `φ¹_x, φ'¹_x ∈ E` and `φ²_x, φ'²_x ∈ E^⊥` (stated as the vanishing of the
cross inner products), then the kernel `A(x;y') A(x';y) M(x, x')` of `T[A,A] ∘ M` is the sum of
the kernels for `M¹¹` and `M²²`. -/
theorem multiplier_split (π : FiniteLaw S) (A : X → Y → ℝ) (φ1 φ2 ψ1 ψ2 : X → S → ℝ)
    (h12 : ∀ x x', ip π (φ1 x) (ψ2 x') = 0) (h21 : ∀ x x', ip π (φ2 x) (ψ1 x') = 0)
    (x x' : X) (y y' : Y) :
    A x y' * A x' y * ip π (fun s => φ1 x s + φ2 x s) (fun s => ψ1 x' s + ψ2 x' s) =
      A x y' * A x' y * ip π (φ1 x) (ψ1 x') + A x y' * A x' y * ip π (φ2 x) (ψ2 x') := by
  have e : ip π (fun s => φ1 x s + φ2 x s) (fun s => ψ1 x' s + ψ2 x' s) =
      ip π (φ1 x) (ψ1 x') + ip π (φ1 x) (ψ2 x') + ip π (φ2 x) (ψ1 x') + ip π (φ2 x) (ψ2 x') := by
    unfold ip FiniteLaw.expect
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  rw [e, h12, h21]
  ring

end Multiplier

section Factorization

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]

/-- **`lem:swapped-rectangle` (d), the bound.** Let `M(x, x') = ⟨φ_x, φ'_{x'}⟩_π`, and let
`𝒴, 𝒴' : L²(β ⊗ π) → L²(α)` have the kernels `A(x;y) φ_x(s)` and `A(x;y) φ'_x(s)`, with
`‖𝒴‖ ≤ c`, `‖𝒴'‖ ≤ c'`. Then `T[A,A] ∘ M` (kernel `A(x;y') A(x';y) M(x,x')` relative to
`(α ⊗ β) ⊗ (α ⊗ β)`) has norm at most `c c'`. The paper factors the operator as
`(𝒴 ⊗ I_β) Swap_{ββ} (𝒴'^* ⊗ I_β)`; the proof below does the same computation on forms.
By `nrm_prodSynth_le`, `‖𝒴‖ ≤ ‖Φ‖ sup_x ‖A(x;·)‖`. -/
theorem swap_multiplier_norm (α : FiniteLaw X) (β : FiniteLaw Y) (π : FiniteLaw S)
    (A : X → Y → ℝ) (φ φ' : X → S → ℝ) {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hY : ∀ G, nrm α (recOp (β.product π) (fun x q => A x q.1 * φ x q.2) G) ≤
      c * nrm (β.product π) G)
    (hY' : ∀ G, nrm α (recOp (β.product π) (fun x q => A x q.1 * φ' x q.2) G) ≤
      c' * nrm (β.product π) G)
    (Fn Hn : X × Y → ℝ) :
    |kernelForm (α.product β) (α.product β)
        (fun p q => A p.1 q.2 * A q.1 p.2 * ip π (φ p.1) (φ' q.1)) Fn Hn| ≤
      c * c' * nrm (α.product β) Fn * nrm (α.product β) Hn := by
  set P : (Y × Y) × S → ℝ := fun r =>
    recAdj α (fun x q => A x q.1 * φ x q.2) (fun x => Fn (x, r.1.1)) (r.1.2, r.2) with hP
  set Q : (Y × Y) × S → ℝ := fun r =>
    recAdj α (fun x q => A x q.1 * φ' x q.2) (fun x => Hn (x, r.1.2)) (r.1.1, r.2) with hQ
  have hA : kernelForm (α.product β) (α.product β)
      (fun p q => A p.1 q.2 * A q.1 p.2 * ip π (φ p.1) (φ' q.1)) Fn Hn =
        ip ((β.product β).product π) P Q := by
    simp only [kernelForm, LinearMap.mk₂_apply, ip, hP, hQ, recAdj, FiniteLaw.expect,
      FiniteLaw.product, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => arg 2; ext x'; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext x'; arg 2; ext y'; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => arg 2; ext y'; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y' _ => Finset.sum_congr rfl (fun s _ =>
      Finset.sum_congr rfl (fun x' _ => Finset.sum_congr rfl (fun x _ => ?_))))
    ring
  have hFub : ∀ (G : (Y × Y) × S → ℝ), ((β.product β).product π).expect G =
      β.expect (fun y => (β.product π).expect (fun q => G ((y, q.1), q.2))) := by
    intro G
    rw [FiniteLaw.expect_product, FiniteLaw.expect_product]
    refine β.expect_congr (fun y => ?_)
    rw [FiniteLaw.expect_product]
  have hFub' : ∀ (G : (Y × Y) × S → ℝ), ((β.product β).product π).expect G =
      β.expect (fun y' => (β.product π).expect (fun q => G ((q.1, y'), q.2))) := by
    intro G
    rw [FiniteLaw.expect_product, FiniteLaw.expect_product, expect_comm]
    refine β.expect_congr (fun y' => ?_)
    rw [FiniteLaw.expect_product]
  have hnF : nrm (α.product β) Fn ^ 2 = β.expect (fun y => α.expect (fun x => Fn (x, y) ^ 2)) := by
    rw [nrm_sq_expect, FiniteLaw.expect_product, expect_comm]
  have hnH : nrm (α.product β) Hn ^ 2 = β.expect (fun y => α.expect (fun x => Hn (x, y) ^ 2)) := by
    rw [nrm_sq_expect, FiniteLaw.expect_product, expect_comm]
  have hPn : nrm ((β.product β).product π) P ≤ c * nrm (α.product β) Fn := by
    apply nrm_le_of_sq_le _ _ hc
    rw [nrm_sq_expect, hFub, hnF, ← FiniteLaw.expect_const_mul]
    refine β.expect_mono (fun y => ?_)
    have h := nrm_recAdj_le α (β.product π) (fun x q => A x q.1 * φ x q.2) hc hY
      (fun x => Fn (x, y))
    have hsq := pow_le_pow_left₀ (nrm_nonneg _ _) h 2
    rw [mul_pow, nrm_sq_expect, nrm_sq_expect] at hsq
    exact hsq
  have hQn : nrm ((β.product β).product π) Q ≤ c' * nrm (α.product β) Hn := by
    apply nrm_le_of_sq_le _ _ hc'
    rw [nrm_sq_expect, hFub', hnH, ← FiniteLaw.expect_const_mul]
    refine β.expect_mono (fun y' => ?_)
    have h := nrm_recAdj_le α (β.product π) (fun x q => A x q.1 * φ' x q.2) hc' hY'
      (fun x => Hn (x, y'))
    have hsq := pow_le_pow_left₀ (nrm_nonneg _ _) h 2
    rw [mul_pow, nrm_sq_expect, nrm_sq_expect] at hsq
    exact hsq
  rw [hA]
  calc |ip ((β.product β).product π) P Q|
      ≤ nrm ((β.product β).product π) P * nrm ((β.product β).product π) Q := abs_ip_le _ _ _
    _ ≤ (c * nrm (α.product β) Fn) * (c' * nrm (α.product β) Hn) :=
        mul_le_mul hPn hQn (nrm_nonneg _ _) (mul_nonneg hc (nrm_nonneg _ _))
    _ = c * c' * nrm (α.product β) Fn * nrm (α.product β) Hn := by ring

/-- **`lem:swapped-rectangle` (d), the factorization.** The action of `T[A,A] ∘ M` (kernel
`A(x;y') A(x';y) M(x,x')`, `M(x,x') = ⟨φ_x, φ'_{x'}⟩_π`) is
`(𝒴 ⊗ I_β) Swap_{ββ} (𝒴'^* ⊗ I_β)`. Here `(𝒴'^* ⊗ I_β) F (y₁, s, y₂) = E_{x'} A(x';y₁) φ'_{x'}(s)
F(x', y₂)`, the swap exchanges `y₁` and `y₂`, and `𝒴 ⊗ I_β` integrates `A(x;y₁) φ_x(s)` against
`(y₁, s)`. -/
theorem swap_multiplier_factor (α : FiniteLaw X) (β : FiniteLaw Y) (π : FiniteLaw S)
    (A : X → Y → ℝ) (φ φ' : X → S → ℝ) (Fn : X × Y → ℝ) (p : X × Y) :
    (α.product β).expect (fun q => A p.1 q.2 * A q.1 p.2 * ip π (φ p.1) (φ' q.1) * Fn q) =
      (β.product π).expect (fun r => A p.1 r.1 * φ p.1 r.2 *
        α.expect (fun x' => A x' p.2 * φ' x' r.2 * Fn (x', r.1))) := by
  simp only [ip, FiniteLaw.expect, FiniteLaw.product, Fintype.sum_prod_type, Finset.mul_sum,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun x _ => ?_))
  ring

end Factorization

end Sarkozy.Cuts
