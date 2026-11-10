module

public import Sarkozy.Cuts.Swapped

/-!
# Cuts, XI′: `T[A,A] ⪰ -sc` and the norm off `u₀ ⊗ v₀` (`lem:swapped-rectangle` (a))

`13_cuts_correlations.tex`, `lem:swapped-rectangle` (a), the last two claims. Let `(X, α)` and
`(Y, β)` be finite probability spaces and `A(x; y)` a real kernel with
`A = σ₀ u₀ ⟨v₀, ·⟩ + A'`, where `u₀ ∈ L²(α)`, `v₀ ∈ L²(β)` are unit vectors, `σ₀ ≥ 0`,
`A' v₀ = 0`, `A'^* u₀ = 0` and `‖A'‖ ≤ c`. If `s ≥ max(σ₀, c)`, then `T[A,A] ⪰ -sc I`
(`swap_lower`), and `‖T[A,A] h‖ ≤ sc ‖h‖` for `h ⊥ u₀ ⊗ v₀` (`swap_norm_perp`).

The paper reads this off the eigenvalue list of `T[A,A]` (a singular value decomposition). The
proof here uses no eigenvalues. Write `N(y', y) = (A^* F(·, y))(y')`, so that
`⟨F, T[A,A] F⟩ = E_{y, y'} N(y', y) N(y, y')` (`swap_form_colN`). Split
`F = u₀ ⊗ a + b' ⊗ v₀ + H` with `a = (u₀ ⊗ I)^* F`, `b' ⊥ u₀` and `H ⊥ u₀ ⊗ L²(β), L²(α) ⊗ v₀`.
Then `⟨F, T[A,A] F⟩ = σ₀² t² + 2σ₀ ⟨A' a⊥, b'⟩ + E_{y,y'} K(y', y) K(y, y')` with
`t = ⟨F, u₀ ⊗ v₀⟩`, `a⊥ = a - t v₀` and `K(y', y) = (A'^* H(·, y))(y')`. The middle term is at
least `-σ₀ c (‖a⊥‖² + ‖b'‖²)`, the last at least `-c² ‖H‖²`, and
`‖F‖² = t² + ‖a⊥‖² + ‖b'‖² + ‖H‖²`.

With the same decomposition, `T[A,A] F = σ₀ u₀ ⊗ A'^* b' + σ₀ A' a⊥ ⊗ v₀ + R` when
`⟨F, u₀ ⊗ v₀⟩ = 0`, with three orthogonal terms of norms at most `sc ‖b'‖`, `sc ‖a⊥‖` and
`c² ‖H‖ ≤ sc ‖H‖`; so `‖T[A,A] F‖ ≤ sc ‖F‖` on the complement of `u₀ ⊗ v₀` (`swap_norm_perp`).

The paper assumes `α`, `β` of full support; the two theorems do not need it.

Given a singular value decomposition (`A v_i = σ_i u_i`, `A^* u_i = σ_i v_i`), `swap_svd_pair`,
`swap_svd_zero` and `swap_svd_eigen` give `T[A,A](u_i ⊗ v_j) = σ_i σ_j u_j ⊗ v_i`, the zero
cases, and the eigenvectors `u_i ⊗ v_i` (`σ_i²`) and `u_i ⊗ v_j ± u_j ⊗ v_i` (`± σ_i σ_j`).

Not formalized: the existence of the singular value decomposition, and the count showing that
these eigenvectors form a basis (so that the list of eigenvalues is complete). The two
consequences used later (`20_middle_reference.tex`, proof of the soft-kernel bounds) are the
lower bound and the norm bound on the complement, which are the two theorems here.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering

section DoubleExpect

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem ee_add (α : FiniteLaw X) (β : FiniteLaw Y) (f g : X → Y → ℝ) :
    α.expect (fun x => β.expect (fun y => f x y + g x y)) =
      α.expect (fun x => β.expect (fun y => f x y)) +
        α.expect (fun x => β.expect (fun y => g x y)) := by
  rw [← α.expect_add]
  exact α.expect_congr (fun x => β.expect_add _ _)

theorem ee_mul (α : FiniteLaw X) (β : FiniteLaw Y) (f : X → ℝ) (g : Y → ℝ) :
    α.expect (fun x => β.expect (fun y => f x * g y)) = α.expect f * β.expect g := by
  rw [← α.expect_mul_const]
  exact α.expect_congr (fun x => β.expect_const_mul _ _)

theorem ee_zero_left (α : FiniteLaw X) (β : FiniteLaw Y) (f : X → ℝ) (φ : X → Y → ℝ)
    (h : ∀ x, β.expect (fun y => φ x y) = 0) :
    α.expect (fun x => β.expect (fun y => f x * φ x y)) = 0 := by
  have e : ∀ x, β.expect (fun y => f x * φ x y) = 0 := fun x => by
    rw [β.expect_const_mul, h x, mul_zero]
  rw [α.expect_congr e]
  exact α.expect_const 0

theorem ee_zero_right (α : FiniteLaw X) (β : FiniteLaw Y) (g : Y → ℝ) (φ : X → Y → ℝ)
    (h : ∀ y, α.expect (fun x => φ x y) = 0) :
    α.expect (fun x => β.expect (fun y => g y * φ x y)) = 0 := by
  rw [expect_comm]
  exact ee_zero_left β α g (fun y x => φ x y) h

end DoubleExpect

section SwapLower

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- `N(y', y) = (A^* F(·, y))(y') = E_{x∼α} A(x; y') F(x, y)`. -/
noncomputable def colN (α : FiniteLaw X) (A : X → Y → ℝ) (Fn : X × Y → ℝ) (y' y : Y) : ℝ :=
  recAdj α A (fun x => Fn (x, y)) y'

/-- `⟨F, T[A,A] F⟩ = E_{y, y'} N(y', y) N(y, y')`. -/
theorem swap_form_colN (α : FiniteLaw X) (β : FiniteLaw Y) (A : X → Y → ℝ) (Fn : X × Y → ℝ) :
    kernelForm (α.product β) (α.product β) (fun p q => A p.1 q.2 * A q.1 p.2) Fn Fn =
      β.expect (fun y => β.expect (fun y' => colN α A Fn y' y * colN α A Fn y y')) := by
  simp only [kernelForm_apply]
  have e1 : ∀ p : X × Y, (α.product β).expect (fun q => A p.1 q.2 * A q.1 p.2 * Fn q) =
      swapOp α β A Fn p := fun p => rfl
  simp only [e1]
  rw [FiniteLaw.expect_product]
  simp only [swapOp_eq_recOp]
  rw [expect_comm]
  refine β.expect_congr (fun y => ?_)
  unfold recOp colN
  simp only [← FiniteLaw.expect_const_mul]
  rw [expect_comm]
  refine β.expect_congr (fun y' => ?_)
  unfold recAdj
  rw [← FiniteLaw.expect_mul_const]
  refine α.expect_congr (fun x => ?_)
  ring

omit [Fintype Y] in
/-- The decomposition `N(y', y) = σ₀ a(y) v₀(y') + v₀(y) (A'^* b')(y') + K(y', y)`. -/
theorem colN_decomp (α : FiniteLaw X) (A A' : X → Y → ℝ) (σ₀ : ℝ) (u₀ : X → ℝ) (v₀ : Y → ℝ)
    (hA : ∀ x y, A x y = σ₀ * u₀ x * v₀ y + A' x y) (hAu : ∀ y, recAdj α A' u₀ y = 0)
    (Fn : X × Y → ℝ) (a : Y → ℝ) (b' : X → ℝ) (H : X × Y → ℝ)
    (hH : ∀ x y, Fn (x, y) = u₀ x * a y + b' x * v₀ y + H (x, y))
    (ha : ∀ y, a y = α.expect (fun x => u₀ x * Fn (x, y))) (y' y : Y) :
    colN α A Fn y' y = σ₀ * a y * v₀ y' + v₀ y * recAdj α A' b' y' + colN α A' H y' y := by
  unfold colN recAdj
  have e : ∀ x, A x y' * Fn (x, y) = σ₀ * v₀ y' * (u₀ x * Fn (x, y)) + a y * (A' x y' * u₀ x) +
      v₀ y * (A' x y' * b' x) + A' x y' * H (x, y) := by
    intro x
    rw [hA, hH x y]
    ring
  rw [α.expect_congr e, α.expect_add, α.expect_add, α.expect_add, α.expect_const_mul,
    α.expect_const_mul, α.expect_const_mul, ← ha y]
  have h0 := hAu y'
  unfold recAdj at h0
  rw [h0]
  ring

/-- **`lem:swapped-rectangle` (a), `T[A,A] ⪰ -sc I`.** Let `A = σ₀ u₀ ⟨v₀, ·⟩ + A'` with unit
vectors `u₀ ∈ L²(α)`, `v₀ ∈ L²(β)`, `σ₀ ≥ 0`, `A' v₀ = 0`, `A'^* u₀ = 0` and `‖A'‖ ≤ c`. If
`σ₀ ≤ s` and `c ≤ s`, then `⟨F, T[A,A] F⟩ ≥ -sc ‖F‖²` for every `F ∈ L²(α ⊗ β)`. -/
theorem swap_lower (α : FiniteLaw X) (β : FiniteLaw Y) (A A' : X → Y → ℝ) {σ₀ c s : ℝ}
    (u₀ : X → ℝ) (v₀ : Y → ℝ) (hu : nrm α u₀ = 1) (hv : nrm β v₀ = 1) (hσ : 0 ≤ σ₀)
    (hA : ∀ x y, A x y = σ₀ * u₀ x * v₀ y + A' x y)
    (hAv : ∀ x, recOp β A' v₀ x = 0) (hAu : ∀ y, recAdj α A' u₀ y = 0)
    (hc0 : 0 ≤ c) (hc : ∀ h, nrm α (recOp β A' h) ≤ c * nrm β h)
    (hsσ : σ₀ ≤ s) (hsc : c ≤ s) (Fn : X × Y → ℝ) :
    -(s * c) * nrm (α.product β) Fn ^ 2 ≤
      kernelForm (α.product β) (α.product β) (fun p q => A p.1 q.2 * A q.1 p.2) Fn Fn := by
  -- unit vectors
  have hu2 : α.expect (fun x => u₀ x * u₀ x) = 1 := by
    have h := nrm_sq_eq α u₀
    rw [hu, one_pow] at h
    unfold ip at h
    exact h.symm
  have hv2 : β.expect (fun y => v₀ y * v₀ y) = 1 := by
    have h := nrm_sq_eq β v₀
    rw [hv, one_pow] at h
    unfold ip at h
    exact h.symm
  -- the decomposition of `F`
  set a : Y → ℝ := fun y => α.expect (fun x => u₀ x * Fn (x, y)) with ha
  set t : ℝ := β.expect (fun y => a y * v₀ y) with ht
  set b : X → ℝ := fun x => β.expect (fun y => Fn (x, y) * v₀ y) with hb
  set b' : X → ℝ := fun x => b x - t * u₀ x with hb'
  set H : X × Y → ℝ := fun p => Fn p - u₀ p.1 * a p.2 - b' p.1 * v₀ p.2 with hH
  set aP : Y → ℝ := fun y => a y - t * v₀ y with haP
  set c' : Y → ℝ := recAdj α A' b' with hc'
  set K : Y → Y → ℝ := fun y' y => colN α A' H y' y with hK
  have hFdec : ∀ x y, Fn (x, y) = u₀ x * a y + b' x * v₀ y + H (x, y) := fun x y => by
    simp only [hH]
    ring
  -- orthogonality relations
  have hub : α.expect (fun x => u₀ x * b x) = t := by
    simp only [hb, ht, ha]
    simp only [← FiniteLaw.expect_const_mul]
    rw [expect_comm]
    refine β.expect_congr (fun y => ?_)
    rw [← FiniteLaw.expect_mul_const]
    exact α.expect_congr (fun x => by ring)
  have hub' : α.expect (fun x => u₀ x * b' x) = 0 := by
    have e : ∀ x, u₀ x * b' x = u₀ x * b x - t * (u₀ x * u₀ x) := fun x => by
      simp only [hb']
      ring
    rw [α.expect_congr e, α.expect_sub, α.expect_const_mul, hub, hu2]
    ring
  have hHu : ∀ y, α.expect (fun x => u₀ x * H (x, y)) = 0 := by
    intro y
    have e : ∀ x, u₀ x * H (x, y) =
        u₀ x * Fn (x, y) - a y * (u₀ x * u₀ x) - v₀ y * (u₀ x * b' x) := fun x => by
      simp only [hH]
      ring
    rw [α.expect_congr e, α.expect_sub, α.expect_sub, α.expect_const_mul, α.expect_const_mul,
      hu2, hub']
    simp only [ha]
    ring
  have hHv : ∀ x, β.expect (fun y => H (x, y) * v₀ y) = 0 := by
    intro x
    have e : ∀ y, H (x, y) * v₀ y =
        Fn (x, y) * v₀ y - u₀ x * (a y * v₀ y) - b' x * (v₀ y * v₀ y) := fun y => by
      simp only [hH]
      ring
    rw [β.expect_congr e, β.expect_sub, β.expect_sub, β.expect_const_mul, β.expect_const_mul,
      hv2, ← ht]
    simp only [hb', hb]
    ring
  have hav : β.expect (fun y => aP y * v₀ y) = 0 := by
    have e : ∀ y, aP y * v₀ y = a y * v₀ y - t * (v₀ y * v₀ y) := fun y => by
      simp only [haP]
      ring
    rw [β.expect_congr e, β.expect_sub, β.expect_const_mul, hv2, ← ht]
    ring
  have hvc : β.expect (fun y => v₀ y * c' y) = 0 := by
    simp only [hc', recAdj]
    simp only [← FiniteLaw.expect_const_mul]
    rw [expect_comm]
    have e : ∀ x, β.expect (fun y => v₀ y * (A' x y * b' x)) = b' x * recOp β A' v₀ x := by
      intro x
      unfold recOp
      rw [← β.expect_const_mul]
      exact β.expect_congr (fun y => by ring)
    rw [α.expect_congr e]
    simp only [hAv, mul_zero]
    exact α.expect_const 0
  -- the two vanishing relations of `K`
  have hK1 : ∀ y, β.expect (fun y' => v₀ y' * K y y') = 0 := by
    intro y
    simp only [hK, colN, recAdj]
    simp only [← FiniteLaw.expect_const_mul]
    rw [expect_comm]
    have e : ∀ x, β.expect (fun y' => v₀ y' * (A' x y * H (x, y'))) =
        A' x y * β.expect (fun y' => H (x, y') * v₀ y') := by
      intro x
      rw [← β.expect_const_mul]
      exact β.expect_congr (fun y' => by ring)
    rw [α.expect_congr e]
    simp only [hHv, mul_zero]
    exact α.expect_const 0
  have hK2 : ∀ y', β.expect (fun y => v₀ y * K y y') = 0 := by
    intro y'
    simp only [hK, colN, recAdj]
    simp only [← FiniteLaw.expect_const_mul]
    rw [expect_comm]
    have e : ∀ x, β.expect (fun y => v₀ y * (A' x y * H (x, y'))) =
        H (x, y') * recOp β A' v₀ x := by
      intro x
      unfold recOp
      rw [← β.expect_const_mul]
      exact β.expect_congr (fun y => by ring)
    rw [α.expect_congr e]
    simp only [hAv, mul_zero]
    exact α.expect_const 0
  -- the form
  have hB : ∀ y' y, colN α A Fn y' y = σ₀ * a y * v₀ y' + v₀ y * c' y' + K y' y := fun y' y =>
    colN_decomp α A A' σ₀ u₀ v₀ hA hAu Fn a b' H hFdec (fun y => rfl) y' y
  have hpt : ∀ y y', colN α A Fn y' y * colN α A Fn y y' =
      ((((σ₀ ^ 2 * (a y * v₀ y)) * (a y' * v₀ y') + (σ₀ * (a y * c' y)) * (v₀ y' * v₀ y')) +
          (σ₀ * (v₀ y * v₀ y)) * (c' y' * a y')) + (v₀ y * c' y) * (v₀ y' * c' y')) +
        ((((σ₀ * a y) * (v₀ y' * K y y') + c' y' * (v₀ y * K y y')) +
          (σ₀ * a y') * (v₀ y * K y' y)) + c' y * (v₀ y' * K y' y)) +
        K y' y * K y y' := by
    intro y y'
    rw [hB y' y, hB y y']
    ring
  rw [swap_form_colN]
  simp only [hpt, ee_add]
  rw [ee_mul, ee_mul, ee_mul, ee_mul,
    ee_zero_left β β (fun y => σ₀ * a y) (fun y y' => v₀ y' * K y y') hK1,
    ee_zero_right β β c' (fun y y' => v₀ y * K y y') hK2,
    ee_zero_right β β (fun y' => σ₀ * a y') (fun y y' => v₀ y * K y' y) hK1,
    ee_zero_left β β c' (fun y y' => v₀ y' * K y' y) hK2]
  rw [β.expect_const_mul, β.expect_const_mul, β.expect_const_mul, hv2, hvc, ← ht]
  -- the cross term: `⟨a, A'^* b'⟩ = ⟨A' a⊥, b'⟩`
  have hca : β.expect (fun y => c' y * a y) = β.expect (fun y => a y * c' y) :=
    β.expect_congr (fun y => mul_comm _ _)
  rw [hca]
  have hrecOp : ∀ x, recOp β A' a x = recOp β A' aP x := by
    intro x
    have h0 := hAv x
    unfold recOp at h0 ⊢
    have e : ∀ y, A' x y * a y = A' x y * aP y + t * (A' x y * v₀ y) := fun y => by
      simp only [haP]
      ring
    rw [β.expect_congr e, β.expect_add, β.expect_const_mul, h0, mul_zero, add_zero]
  have hcross : |β.expect (fun y => a y * c' y)| ≤ c * nrm α b' * nrm β aP := by
    have e : β.expect (fun y => a y * c' y) = ip α b' (recOp β A' aP) := by
      have h1 := ip_recAdj α β A' b' a
      unfold ip at h1 ⊢
      have h2 : α.expect (fun x => b' x * recOp β A' a x) =
          α.expect (fun x => b' x * recOp β A' aP x) :=
        α.expect_congr (fun x => by rw [hrecOp x])
      rw [← h2, ← h1]
      exact β.expect_congr (fun y => mul_comm _ _)
    rw [e]
    refine (abs_ip_le α b' _).trans ?_
    have := mul_le_mul_of_nonneg_left (hc aP) (nrm_nonneg α b')
    linarith
  -- the last term: `E K(y', y) K(y, y') ≥ -c² ‖H‖²`
  have hKK : -(c ^ 2 * nrm (α.product β) H ^ 2) ≤
      β.expect (fun y => β.expect (fun y' => K y' y * K y y')) := by
    have hpt2 : ∀ y y', -((K y' y ^ 2 + K y y' ^ 2) / 2) ≤ K y' y * K y y' := fun y y' => by
      nlinarith [sq_nonneg (K y' y + K y y')]
    have hsym : β.expect (fun y => β.expect (fun y' => K y y' ^ 2)) =
        β.expect (fun y => β.expect (fun y' => K y' y ^ 2)) := expect_comm _ _ _
    have hcol : ∀ y, β.expect (fun y' => K y' y ^ 2) ≤
        c ^ 2 * α.expect (fun x => H (x, y) ^ 2) := by
      intro y
      have h := nrm_recAdj_le α β A' hc0 hc (fun x => H (x, y))
      have hsq := pow_le_pow_left₀ (nrm_nonneg _ _) h 2
      rw [mul_pow, nrm_sq_expect, nrm_sq_expect] at hsq
      exact hsq
    have hH2 : nrm (α.product β) H ^ 2 = β.expect (fun y => α.expect (fun x => H (x, y) ^ 2)) := by
      rw [nrm_sq_expect, FiniteLaw.expect_product, expect_comm]
    have hlow : -(β.expect (fun y => β.expect (fun y' => K y' y ^ 2))) ≤
        β.expect (fun y => β.expect (fun y' => K y' y * K y y')) := by
      have h1 : β.expect (fun y => β.expect (fun y' => -((K y' y ^ 2 + K y y' ^ 2) / 2))) ≤
          β.expect (fun y => β.expect (fun y' => K y' y * K y y')) :=
        β.expect_mono (fun y => β.expect_mono (fun y' => hpt2 y y'))
      have h2 : β.expect (fun y => β.expect (fun y' => -((K y' y ^ 2 + K y y' ^ 2) / 2))) =
          -((β.expect (fun y => β.expect (fun y' => K y' y ^ 2)) +
            β.expect (fun y => β.expect (fun y' => K y y' ^ 2))) / 2) := by
        rw [← ee_add]
        have e : ∀ y, β.expect (fun y' => -((K y' y ^ 2 + K y y' ^ 2) / 2)) =
            (-(1 / 2)) * β.expect (fun y' => K y' y ^ 2 + K y y' ^ 2) := fun y => by
          rw [← β.expect_const_mul]
          exact β.expect_congr (fun y' => by ring)
        rw [β.expect_congr e, β.expect_const_mul]
        ring
      rw [h2, hsym] at h1
      linarith
    have hup : β.expect (fun y => β.expect (fun y' => K y' y ^ 2)) ≤
        c ^ 2 * nrm (α.product β) H ^ 2 := by
      rw [hH2, ← β.expect_const_mul]
      exact β.expect_mono hcol
    linarith
  -- `‖F‖² = t² + ‖a⊥‖² + ‖b'‖² + ‖H‖²`
  have hnorm : nrm (α.product β) Fn ^ 2 =
      t ^ 2 + nrm β aP ^ 2 + nrm α b' ^ 2 + nrm (α.product β) H ^ 2 := by
    have hpt3 : ∀ x y, Fn (x, y) ^ 2 =
        ((((u₀ x * u₀ x) * (a y * a y) + (b' x * b' x) * (v₀ y * v₀ y)) + H (x, y) ^ 2) +
          (2 * (u₀ x * b' x)) * (a y * v₀ y)) + (2 * a y) * (u₀ x * H (x, y)) +
          (2 * b' x) * (H (x, y) * v₀ y) := fun x y => by
      rw [hFdec x y]
      ring
    rw [nrm_sq_expect, FiniteLaw.expect_product]
    simp only [hpt3, ee_add]
    rw [ee_mul, ee_mul, ee_mul, hu2, hv2, α.expect_const_mul, hub',
      ee_zero_right α β (fun y => 2 * a y) (fun x y => u₀ x * H (x, y)) hHu,
      ee_zero_left α β (fun x => 2 * b' x) (fun x y => H (x, y) * v₀ y) hHv]
    have haP2 : nrm β aP ^ 2 = β.expect (fun y => a y * a y) - t ^ 2 := by
      rw [nrm_sq_expect]
      have e : ∀ y, aP y ^ 2 = a y * a y - 2 * t * (a y * v₀ y) + t ^ 2 * (v₀ y * v₀ y) :=
        fun y => by
          simp only [haP]
          ring
      rw [β.expect_congr e, β.expect_add, β.expect_sub, β.expect_const_mul, β.expect_const_mul,
        hv2, ← ht]
      ring
    have hb2 : nrm α b' ^ 2 = α.expect (fun x => b' x * b' x) := by
      rw [nrm_sq_eq]
      rfl
    have hH2 : nrm (α.product β) H ^ 2 = α.expect (fun x => β.expect (fun y => H (x, y) ^ 2)) := by
      rw [nrm_sq_expect, FiniteLaw.expect_product]
    rw [haP2, hb2, hH2]
    ring
  -- conclusion
  have hab : 2 * (nrm α b' * nrm β aP) ≤ nrm α b' ^ 2 + nrm β aP ^ 2 := by
    nlinarith [sq_nonneg (nrm α b' - nrm β aP)]
  have hn1 : 0 ≤ nrm α b' * nrm β aP := mul_nonneg (nrm_nonneg _ _) (nrm_nonneg _ _)
  have hcr := neg_abs_le (β.expect (fun y => a y * c' y))
  have hσc : σ₀ * c ≤ s * c := mul_le_mul_of_nonneg_right hsσ hc0
  have hcc : c ^ 2 ≤ s * c := by nlinarith
  have hsc0 : 0 ≤ s * c := le_trans (mul_nonneg hσ hc0) hσc
  have hH0 : 0 ≤ nrm (α.product β) H ^ 2 := sq_nonneg _
  rw [hnorm]
  nlinarith [mul_le_mul_of_nonneg_left hcross hσ, sq_nonneg (σ₀ * t), sq_nonneg t,
    mul_le_mul_of_nonneg_left hab (mul_nonneg hσ hc0),
    mul_le_mul_of_nonneg_right hcc hH0, mul_nonneg hsc0 (sq_nonneg t)]

/-- **`lem:swapped-rectangle` (a), `‖T[A,A] h‖ ≤ sc ‖h‖` for `h ⊥ u₀ ⊗ v₀`.** Under the hypotheses
of `swap_lower`, `T[A,A]` has norm at most `sc` on the orthogonal complement of `u₀ ⊗ v₀`. -/
theorem swap_norm_perp (α : FiniteLaw X) (β : FiniteLaw Y) (A A' : X → Y → ℝ) {σ₀ c s : ℝ}
    (u₀ : X → ℝ) (v₀ : Y → ℝ) (hu : nrm α u₀ = 1) (hv : nrm β v₀ = 1) (hσ : 0 ≤ σ₀)
    (hA : ∀ x y, A x y = σ₀ * u₀ x * v₀ y + A' x y)
    (hAv : ∀ x, recOp β A' v₀ x = 0) (hAu : ∀ y, recAdj α A' u₀ y = 0)
    (hc0 : 0 ≤ c) (hc : ∀ h, nrm α (recOp β A' h) ≤ c * nrm β h)
    (hsσ : σ₀ ≤ s) (hsc : c ≤ s) (Fn : X × Y → ℝ)
    (hperp : ip (α.product β) Fn (fun p => u₀ p.1 * v₀ p.2) = 0) :
    nrm (α.product β) (swapOp α β A Fn) ≤ s * c * nrm (α.product β) Fn := by
  -- unit vectors
  have hu2 : α.expect (fun x => u₀ x * u₀ x) = 1 := by
    have h := nrm_sq_eq α u₀
    rw [hu, one_pow] at h
    unfold ip at h
    exact h.symm
  have hv2 : β.expect (fun y => v₀ y * v₀ y) = 1 := by
    have h := nrm_sq_eq β v₀
    rw [hv, one_pow] at h
    unfold ip at h
    exact h.symm
  -- the decomposition of `F`
  set a : Y → ℝ := fun y => α.expect (fun x => u₀ x * Fn (x, y)) with ha
  set t : ℝ := β.expect (fun y => a y * v₀ y) with ht
  set b : X → ℝ := fun x => β.expect (fun y => Fn (x, y) * v₀ y) with hb
  set b' : X → ℝ := fun x => b x - t * u₀ x with hb'
  set H : X × Y → ℝ := fun p => Fn p - u₀ p.1 * a p.2 - b' p.1 * v₀ p.2 with hH
  set aP : Y → ℝ := fun y => a y - t * v₀ y with haP
  set c' : Y → ℝ := recAdj α A' b' with hc'
  set K : Y → Y → ℝ := fun y' y => colN α A' H y' y with hK
  have hFdec : ∀ x y, Fn (x, y) = u₀ x * a y + b' x * v₀ y + H (x, y) := fun x y => by
    simp only [hH]
    ring
  -- orthogonality relations
  have hub : α.expect (fun x => u₀ x * b x) = t := by
    simp only [hb, ht, ha]
    simp only [← FiniteLaw.expect_const_mul]
    rw [expect_comm]
    refine β.expect_congr (fun y => ?_)
    rw [← FiniteLaw.expect_mul_const]
    exact α.expect_congr (fun x => by ring)
  have hub' : α.expect (fun x => u₀ x * b' x) = 0 := by
    have e : ∀ x, u₀ x * b' x = u₀ x * b x - t * (u₀ x * u₀ x) := fun x => by
      simp only [hb']
      ring
    rw [α.expect_congr e, α.expect_sub, α.expect_const_mul, hub, hu2]
    ring
  have hHu : ∀ y, α.expect (fun x => u₀ x * H (x, y)) = 0 := by
    intro y
    have e : ∀ x, u₀ x * H (x, y) =
        u₀ x * Fn (x, y) - a y * (u₀ x * u₀ x) - v₀ y * (u₀ x * b' x) := fun x => by
      simp only [hH]
      ring
    rw [α.expect_congr e, α.expect_sub, α.expect_sub, α.expect_const_mul, α.expect_const_mul,
      hu2, hub']
    simp only [ha]
    ring
  have hHv : ∀ x, β.expect (fun y => H (x, y) * v₀ y) = 0 := by
    intro x
    have e : ∀ y, H (x, y) * v₀ y =
        Fn (x, y) * v₀ y - u₀ x * (a y * v₀ y) - b' x * (v₀ y * v₀ y) := fun y => by
      simp only [hH]
      ring
    rw [β.expect_congr e, β.expect_sub, β.expect_sub, β.expect_const_mul, β.expect_const_mul,
      hv2, ← ht]
    simp only [hb', hb]
    ring
  have hav : β.expect (fun y => aP y * v₀ y) = 0 := by
    have e : ∀ y, aP y * v₀ y = a y * v₀ y - t * (v₀ y * v₀ y) := fun y => by
      simp only [haP]
      ring
    rw [β.expect_congr e, β.expect_sub, β.expect_const_mul, hv2, ← ht]
    ring
  have hvc : β.expect (fun y => v₀ y * c' y) = 0 := by
    simp only [hc', recAdj]
    simp only [← FiniteLaw.expect_const_mul]
    rw [expect_comm]
    have e : ∀ x, β.expect (fun y => v₀ y * (A' x y * b' x)) = b' x * recOp β A' v₀ x := by
      intro x
      unfold recOp
      rw [← β.expect_const_mul]
      exact β.expect_congr (fun y => by ring)
    rw [α.expect_congr e]
    simp only [hAv, mul_zero]
    exact α.expect_const 0
  -- the two vanishing relations of `K`
  have hK1 : ∀ y, β.expect (fun y' => v₀ y' * K y y') = 0 := by
    intro y
    simp only [hK, colN, recAdj]
    simp only [← FiniteLaw.expect_const_mul]
    rw [expect_comm]
    have e : ∀ x, β.expect (fun y' => v₀ y' * (A' x y * H (x, y'))) =
        A' x y * β.expect (fun y' => H (x, y') * v₀ y') := by
      intro x
      rw [← β.expect_const_mul]
      exact β.expect_congr (fun y' => by ring)
    rw [α.expect_congr e]
    simp only [hHv, mul_zero]
    exact α.expect_const 0
  have hK2 : ∀ y', β.expect (fun y => v₀ y * K y y') = 0 := by
    intro y'
    simp only [hK, colN, recAdj]
    simp only [← FiniteLaw.expect_const_mul]
    rw [expect_comm]
    have e : ∀ x, β.expect (fun y => v₀ y * (A' x y * H (x, y'))) =
        H (x, y') * recOp β A' v₀ x := by
      intro x
      unfold recOp
      rw [← β.expect_const_mul]
      exact β.expect_congr (fun y => by ring)
    rw [α.expect_congr e]
    simp only [hAv, mul_zero]
    exact α.expect_const 0
  have hB : ∀ y' y, colN α A Fn y' y = σ₀ * a y * v₀ y' + v₀ y * c' y' + K y' y := fun y' y =>
    colN_decomp α A A' σ₀ u₀ v₀ hA hAu Fn a b' H hFdec (fun y => rfl) y' y
  have hrecOp : ∀ x, recOp β A' a x = recOp β A' aP x := by
    intro x
    have h0 := hAv x
    unfold recOp at h0 ⊢
    have e : ∀ y, A' x y * a y = A' x y * aP y + t * (A' x y * v₀ y) := fun y => by
      simp only [haP]
      ring
    rw [β.expect_congr e, β.expect_add, β.expect_const_mul, h0, mul_zero, add_zero]
  -- `t = ⟨F, u₀ ⊗ v₀⟩ = 0`
  have ht0 : t = 0 := by
    rw [← hperp]
    unfold ip
    rw [FiniteLaw.expect_product, expect_comm, ht]
    refine β.expect_congr (fun y => ?_)
    simp only [ha]
    rw [← α.expect_mul_const]
    exact α.expect_congr (fun x => by ring)
  -- `T F = σ₀ u₀ ⊗ A'^* b' + σ₀ A' a⊥ ⊗ v₀ + R`
  set P : X → ℝ := recOp β A' aP with hP
  set R : X → Y → ℝ := fun x y => recOp β A' (fun y' => K y y') x with hR
  have hT : ∀ x y, swapOp α β A Fn (x, y) = σ₀ * u₀ x * c' y + σ₀ * v₀ y * P x + R x y := by
    intro x y
    rw [swapOp_eq_recOp]
    unfold recOp
    have e : ∀ y', A x y' * recAdj α A (fun x' => Fn (x', y')) y =
        σ₀ ^ 2 * u₀ x * v₀ y * (a y' * v₀ y') + σ₀ * u₀ x * c' y * (v₀ y' * v₀ y') +
          σ₀ * u₀ x * (v₀ y' * K y y') + σ₀ * v₀ y * (A' x y' * a y') +
          c' y * (A' x y' * v₀ y') + A' x y' * K y y' := by
      intro y'
      have h1 : recAdj α A (fun x' => Fn (x', y')) y = colN α A Fn y y' := rfl
      rw [h1, hA, hB y y']
      ring
    rw [β.expect_congr e, β.expect_add, β.expect_add, β.expect_add, β.expect_add, β.expect_add,
      β.expect_const_mul, β.expect_const_mul, β.expect_const_mul, β.expect_const_mul,
      β.expect_const_mul, ← ht, hv2, hK1 y, ht0]
    have h2 := hAv x
    unfold recOp at h2
    have h3 := hrecOp x
    unfold recOp at h3
    rw [h2, h3]
    simp only [hP, hR, recOp]
    ring
  have hRu : ∀ y, α.expect (fun x => u₀ x * R x y) = 0 := by
    intro y
    simp only [hR, recOp]
    simp only [← FiniteLaw.expect_const_mul]
    rw [expect_comm]
    have e : ∀ y', α.expect (fun x => u₀ x * (A' x y' * K y y')) = K y y' * recAdj α A' u₀ y' := by
      intro y'
      unfold recAdj
      rw [← α.expect_const_mul]
      exact α.expect_congr (fun x => by ring)
    rw [β.expect_congr e]
    simp only [hAu, mul_zero]
    exact β.expect_const 0
  have hRv : ∀ x, β.expect (fun y => v₀ y * R x y) = 0 := by
    intro x
    simp only [hR, recOp]
    simp only [← FiniteLaw.expect_const_mul]
    rw [expect_comm]
    have e : ∀ y', β.expect (fun y => v₀ y * (A' x y' * K y y')) =
        A' x y' * β.expect (fun y => v₀ y * K y y') := by
      intro y'
      rw [← β.expect_const_mul]
      exact β.expect_congr (fun y => by ring)
    rw [β.expect_congr e]
    simp only [hK2, mul_zero]
    exact β.expect_const 0
  -- `‖T F‖² = σ₀² ‖A'^* b'‖² + σ₀² ‖A' a⊥‖² + ‖R‖²`
  have hTn : nrm (α.product β) (swapOp α β A Fn) ^ 2 =
      σ₀ ^ 2 * nrm β c' ^ 2 + σ₀ ^ 2 * nrm α P ^ 2 +
        α.expect (fun x => β.expect (fun y => R x y ^ 2)) := by
    have hpt3 : ∀ x y, swapOp α β A Fn (x, y) ^ 2 =
        ((((σ₀ ^ 2 * (u₀ x * u₀ x)) * (c' y * c' y) + (σ₀ ^ 2 * (P x * P x)) * (v₀ y * v₀ y)) +
          R x y ^ 2) + (2 * σ₀ ^ 2 * (u₀ x * P x)) * (v₀ y * c' y)) +
          (2 * σ₀ * c' y) * (u₀ x * R x y) + (2 * σ₀ * P x) * (v₀ y * R x y) := fun x y => by
      rw [hT x y]
      ring
    rw [nrm_sq_expect, FiniteLaw.expect_product]
    simp only [hpt3, ee_add]
    rw [ee_mul, ee_mul, ee_mul, α.expect_const_mul, α.expect_const_mul, hu2, hv2, hvc,
      ee_zero_right α β (fun y => 2 * σ₀ * c' y) (fun x y => u₀ x * R x y) hRu,
      ee_zero_left α β (fun x => 2 * σ₀ * P x) (fun x y => v₀ y * R x y) hRv,
      nrm_sq_expect, nrm_sq_expect]
    have e1 : β.expect (fun y => c' y * c' y) = β.expect (fun y => c' y ^ 2) :=
      β.expect_congr (fun y => by ring)
    have e2 : α.expect (fun x => P x * P x) = α.expect (fun x => P x ^ 2) :=
      α.expect_congr (fun x => by ring)
    rw [e1, e2]
    ring
  -- the bounds
  have hc'b : nrm β c' ≤ c * nrm α b' := nrm_recAdj_le α β A' hc0 hc b'
  have hPa : nrm α P ≤ c * nrm β aP := hc aP
  have hRb : α.expect (fun x => β.expect (fun y => R x y ^ 2)) ≤
      c ^ 2 * (c ^ 2 * nrm (α.product β) H ^ 2) := by
    rw [expect_comm]
    have hrow : ∀ y, α.expect (fun x => R x y ^ 2) ≤ c ^ 2 * β.expect (fun y' => K y y' ^ 2) := by
      intro y
      have h := hc (fun y' => K y y')
      have hsq := pow_le_pow_left₀ (nrm_nonneg _ _) h 2
      rw [mul_pow, nrm_sq_expect, nrm_sq_expect] at hsq
      exact hsq
    have hcol : ∀ y', β.expect (fun y => K y y' ^ 2) ≤
        c ^ 2 * α.expect (fun x => H (x, y') ^ 2) := by
      intro y'
      have h := nrm_recAdj_le α β A' hc0 hc (fun x => H (x, y'))
      have hsq := pow_le_pow_left₀ (nrm_nonneg _ _) h 2
      rw [mul_pow, nrm_sq_expect, nrm_sq_expect] at hsq
      exact hsq
    have hH2 : nrm (α.product β) H ^ 2 = β.expect (fun y => α.expect (fun x => H (x, y) ^ 2)) := by
      rw [nrm_sq_expect, FiniteLaw.expect_product, expect_comm]
    calc β.expect (fun y => α.expect (fun x => R x y ^ 2))
        ≤ β.expect (fun y => c ^ 2 * β.expect (fun y' => K y y' ^ 2)) := β.expect_mono hrow
      _ = c ^ 2 * β.expect (fun y' => β.expect (fun y => K y y' ^ 2)) := by
          rw [β.expect_const_mul, expect_comm]
      _ ≤ c ^ 2 * β.expect (fun y' => c ^ 2 * α.expect (fun x => H (x, y') ^ 2)) :=
          mul_le_mul_of_nonneg_left (β.expect_mono hcol) (sq_nonneg c)
      _ = c ^ 2 * (c ^ 2 * nrm (α.product β) H ^ 2) := by
          rw [β.expect_const_mul, hH2]
  -- `‖F‖² = ‖a⊥‖² + ‖b'‖² + ‖H‖²`
  have hnorm : nrm (α.product β) Fn ^ 2 =
      t ^ 2 + nrm β aP ^ 2 + nrm α b' ^ 2 + nrm (α.product β) H ^ 2 := by
    have hpt3 : ∀ x y, Fn (x, y) ^ 2 =
        ((((u₀ x * u₀ x) * (a y * a y) + (b' x * b' x) * (v₀ y * v₀ y)) + H (x, y) ^ 2) +
          (2 * (u₀ x * b' x)) * (a y * v₀ y)) + (2 * a y) * (u₀ x * H (x, y)) +
          (2 * b' x) * (H (x, y) * v₀ y) := fun x y => by
      rw [hFdec x y]
      ring
    rw [nrm_sq_expect, FiniteLaw.expect_product]
    simp only [hpt3, ee_add]
    rw [ee_mul, ee_mul, ee_mul, hu2, hv2, α.expect_const_mul, hub',
      ee_zero_right α β (fun y => 2 * a y) (fun x y => u₀ x * H (x, y)) hHu,
      ee_zero_left α β (fun x => 2 * b' x) (fun x y => H (x, y) * v₀ y) hHv]
    have haP2 : nrm β aP ^ 2 = β.expect (fun y => a y * a y) - t ^ 2 := by
      rw [nrm_sq_expect]
      have e : ∀ y, aP y ^ 2 = a y * a y - 2 * t * (a y * v₀ y) + t ^ 2 * (v₀ y * v₀ y) :=
        fun y => by
          simp only [haP]
          ring
      rw [β.expect_congr e, β.expect_add, β.expect_sub, β.expect_const_mul, β.expect_const_mul,
        hv2, ← ht]
      ring
    have hb2 : nrm α b' ^ 2 = α.expect (fun x => b' x * b' x) := by
      rw [nrm_sq_eq]
      rfl
    have hH2 : nrm (α.product β) H ^ 2 = α.expect (fun x => β.expect (fun y => H (x, y) ^ 2)) := by
      rw [nrm_sq_expect, FiniteLaw.expect_product]
    rw [haP2, hb2, hH2]
    ring
  -- conclusion
  have hsc0 : 0 ≤ s * c := mul_nonneg (le_trans hσ hsσ) hc0
  apply nrm_le_of_sq_le _ _ hsc0
  rw [hTn, hnorm, ht0]
  have h1 : σ₀ ^ 2 * nrm β c' ^ 2 ≤ (s * c) ^ 2 * nrm α b' ^ 2 := by
    have := pow_le_pow_left₀ (nrm_nonneg _ _) hc'b 2
    have hs2 : σ₀ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hσ hsσ 2
    calc σ₀ ^ 2 * nrm β c' ^ 2 ≤ s ^ 2 * (c * nrm α b') ^ 2 :=
          mul_le_mul hs2 this (sq_nonneg _) (sq_nonneg _)
      _ = (s * c) ^ 2 * nrm α b' ^ 2 := by ring
  have h2 : σ₀ ^ 2 * nrm α P ^ 2 ≤ (s * c) ^ 2 * nrm β aP ^ 2 := by
    have := pow_le_pow_left₀ (nrm_nonneg _ _) hPa 2
    have hs2 : σ₀ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hσ hsσ 2
    calc σ₀ ^ 2 * nrm α P ^ 2 ≤ s ^ 2 * (c * nrm β aP) ^ 2 :=
          mul_le_mul hs2 this (sq_nonneg _) (sq_nonneg _)
      _ = (s * c) ^ 2 * nrm β aP ^ 2 := by ring
  have h3 : c ^ 2 * (c ^ 2 * nrm (α.product β) H ^ 2) ≤ (s * c) ^ 2 * nrm (α.product β) H ^ 2 := by
    have hc2 : c ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hc0 hsc 2
    have := mul_le_mul_of_nonneg_right hc2
      (mul_nonneg (sq_nonneg c) (sq_nonneg (nrm (α.product β) H)))
    nlinarith
  nlinarith [hRb]

end SwapLower

section SVD

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- **`lem:swapped-rectangle` (a), the action on a singular value decomposition.** If
`A v_j = σ_j u_j` and `A^* u_i = σ_i v_i`, then `T[A,A](u_i ⊗ v_j) = σ_i σ_j u_j ⊗ v_i`. -/
theorem swap_svd_pair (α : FiniteLaw X) (β : FiniteLaw Y) (A : X → Y → ℝ) {ι : Type*}
    (u : ι → X → ℝ) (v : ι → Y → ℝ) (σ : ι → ℝ)
    (hAv : ∀ j x, recOp β A (v j) x = σ j * u j x) (hAu : ∀ i y, recAdj α A (u i) y = σ i * v i y)
    (i j : ι) (p : X × Y) :
    swapOp α β A (fun q => u i q.1 * v j q.2) p = σ i * σ j * (u j p.1 * v i p.2) := by
  rw [swapOp_tensor, hAv, hAu]
  ring

/-- **`lem:swapped-rectangle` (a).** `T[A,A](f ⊗ g) = 0` when `A g = 0` or `A^* f = 0`; in
particular `T[A,A](u_i ⊗ v_j) = 0` when `i > k` or `j > k`. -/
theorem swap_svd_zero (α : FiniteLaw X) (β : FiniteLaw Y) (A : X → Y → ℝ) (f : X → ℝ)
    (g : Y → ℝ) (h : (∀ x, recOp β A g x = 0) ∨ (∀ y, recAdj α A f y = 0)) (p : X × Y) :
    swapOp α β A (fun q => f q.1 * g q.2) p = 0 := by
  rw [swapOp_tensor]
  rcases h with h | h
  · rw [h, zero_mul]
  · rw [h, mul_zero]

/-- **`lem:swapped-rectangle` (a), the eigenvectors.** Under the hypotheses of `swap_svd_pair`,
`u_i ⊗ v_i` has the eigenvalue `σ_i²`, and `u_i ⊗ v_j ± u_j ⊗ v_i` have the eigenvalues
`± σ_i σ_j`. With orthonormal bases these eigenvectors, and the `u_i ⊗ v_j` with `i > k` or
`j > k` (eigenvalue `0`, `swap_svd_zero`), form an orthogonal basis of `L²(α ⊗ β)`; this last
count is not formalized. -/
theorem swap_svd_eigen (α : FiniteLaw X) (β : FiniteLaw Y) (A : X → Y → ℝ) {ι : Type*}
    (u : ι → X → ℝ) (v : ι → Y → ℝ) (σ : ι → ℝ)
    (hAv : ∀ j x, recOp β A (v j) x = σ j * u j x) (hAu : ∀ i y, recAdj α A (u i) y = σ i * v i y)
    (i j : ι) (p : X × Y) :
    swapOp α β A (fun q => u i q.1 * v i q.2) p = σ i ^ 2 * (u i p.1 * v i p.2) ∧
      swapOp α β A (fun q => u i q.1 * v j q.2 + u j q.1 * v i q.2) p =
        σ i * σ j * (u i p.1 * v j p.2 + u j p.1 * v i p.2) ∧
      swapOp α β A (fun q => u i q.1 * v j q.2 - u j q.1 * v i q.2) p =
        -(σ i * σ j) * (u i p.1 * v j p.2 - u j p.1 * v i p.2) := by
  have hlin : ∀ (F₁ F₂ : X × Y → ℝ) (c : ℝ),
      swapOp α β A (fun q => F₁ q + c * F₂ q) p = swapOp α β A F₁ p + c * swapOp α β A F₂ p := by
    intro F₁ F₂ c
    unfold swapOp
    rw [← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_add]
    exact (α.product β).expect_congr (fun q => by ring)
  refine ⟨?_, ?_, ?_⟩
  · rw [swap_svd_pair α β A u v σ hAv hAu i i p]
    ring
  · have e := hlin (fun q => u i q.1 * v j q.2) (fun q => u j q.1 * v i q.2) 1
    simp only [one_mul] at e
    rw [e, swap_svd_pair α β A u v σ hAv hAu i j p, swap_svd_pair α β A u v σ hAv hAu j i p]
    ring
  · have e := hlin (fun q => u i q.1 * v j q.2) (fun q => u j q.1 * v i q.2) (-1)
    have e2 : (fun q : X × Y => u i q.1 * v j q.2 + -1 * (u j q.1 * v i q.2)) =
        fun q => u i q.1 * v j q.2 - u j q.1 * v i q.2 := funext (fun q => by ring)
    rw [e2] at e
    rw [e, swap_svd_pair α β A u v σ hAv hAu i j p, swap_svd_pair α β A u v σ hAv hAu j i p]
    ring

end SVD

end Sarkozy.Cuts
