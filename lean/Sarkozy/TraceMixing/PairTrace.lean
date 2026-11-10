module

public import Sarkozy.TraceMixing.FourierStep

/-!
# The pair operator, trace form (`lem:trace-mixing`(b), abstract form)

`paper/sections/12_labellings.tex`, `lem:trace-mixing`(b). A joint law `κ` of a pair
`(z_u, z_v) ∈ 𝔽_p²` and the other labels `r ∈ R` such that

* the pair is a strict-square pair (`χ(z_v - z_u) = 1`) almost surely (`hsupp`);
* translating the labels by `β` is a bijection `τ_β` of `R` (`htr`) and dilating them by a
  nonzero square `α` a bijection `σ_α` (`hdil`) — the square-affine invariance of `λ_p(G)`.

`pair_trace_bound`: for every `f` on pairs with `E f = 0` under the pair marginal,
`‖T f‖² ≤ max(E[2/(p-1) ∑_{y∈Q} φ_y²], p · tr) ‖f‖²`, where
`φ_y(r) = (p-1)/2 · ∑_x T(r; x, x + y) - 1` and `tr = ∑_r κ_B(r) ∑_ω T(r; ω)²`
(for a graph law `tr = E[1/|Φ|]`, `trace_pairGram_eq` in `Pair.lean`).

As in the paper: in the coordinates `(x, y)`, `z_v = x + y`, write `f = f₀ + f₁` with
`f₀(x, x + y) = g(y)`, `g` the average of `f` over `x`; `T f₀ ⊥ T f₁` by translation
invariance; `‖T f₀‖² ≤ E[2/(p-1) ∑ φ_y²] ‖f₀‖²` by Cauchy–Schwarz (frequency zero); and
`‖T f₁‖² ≤ p · tr · ‖f₁‖²` by `fourier_step` (nonzero frequencies). The pair marginal is
uniform on the strict-square pairs (`srcWeight_pair`).
-/

@[expose] public section

open Finset Complex
open scoped BigOperators Matrix

namespace Sarkozy.TraceMixing

open Sarkozy.Mixing

variable {p : ℕ} [Fact p.Prime]

/-- The nonzero squares number `(p - 1)/2`. -/
theorem card_squares (hp2 : p ≠ 2) :
    ((univ.filter fun y : ZMod p => quadraticChar (ZMod p) y = 1).card : ℝ) = ((p : ℝ) - 1) / 2 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  set χ := quadraticChar (ZMod p) with hχdef
  have h1 (y : ZMod p) : (if χ y = 1 then (1 : ℝ) else 0) =
      (((χ y : ℤ) : ℝ) ^ 2 + ((χ y : ℤ) : ℝ)) / 2 := by
    by_cases hy : y = 0
    · subst hy
      simp [hχdef]
    · rcases quadraticChar_dichotomy hy with h | h
      · rw [h]
        norm_num
      · rw [h]
        norm_num
  have hsum : ∑ y : ZMod p, (if χ y = 1 then (1 : ℝ) else 0) =
      ((univ.filter fun y : ZMod p => χ y = 1).card : ℝ) := by
    rw [Finset.sum_boole]
  have hχs : ∑ y : ZMod p, ((χ y : ℤ) : ℝ) = 0 := by
    have := quadraticChar_sum_zero hF
    rw [← hχdef] at this
    exact_mod_cast this
  have hχ2 : ∑ y : ZMod p, ((χ y : ℤ) : ℝ) ^ 2 = p - 1 := by
    have h (y : ZMod p) : ((χ y : ℤ) : ℝ) ^ 2 = 1 - (if y = 0 then 1 else 0) := by
      by_cases hy : y = 0
      · subst hy
        simp [hχdef]
      · rw [ite_eq_right hy, sub_zero]
        have := quadraticChar_sq_one hy
        rw [← hχdef] at this
        exact_mod_cast this
    simp only [h, Finset.sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one,
      Finset.sum_ite_eq', mem_univ, ite_true]
  rw [← hsum]
  simp only [h1]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hχs, hχ2]
  ring

/-- `x + y - x = y` in `𝔽_p` (stated here so that it rewrites terms elaborated in this
context). -/
theorem zmod_add_sub_cancel (x y : ZMod p) : x + y - x = y := by ring

/-- The translation `(x, x') ↦ (x + β, x' + β)` of pairs. -/
def pairTr (β : ZMod p) : ZMod p × ZMod p ≃ ZMod p × ZMod p where
  toFun ω := (ω.1 + β, ω.2 + β)
  invFun ω := (ω.1 - β, ω.2 - β)
  left_inv ω := by
    obtain ⟨a, b⟩ := ω
    simp only [Prod.mk.injEq]
    constructor <;> ring
  right_inv ω := by
    obtain ⟨a, b⟩ := ω
    simp only [Prod.mk.injEq]
    constructor <;> ring

/-- The dilation `(x, x') ↦ (αx, αx')` of pairs, `α ≠ 0`. -/
def pairDil {α : ZMod p} (hα : α ≠ 0) : ZMod p × ZMod p ≃ ZMod p × ZMod p where
  toFun ω := (α * ω.1, α * ω.2)
  invFun ω := (α⁻¹ * ω.1, α⁻¹ * ω.2)
  left_inv ω := by
    obtain ⟨a, b⟩ := ω
    simp only [Prod.mk.injEq]
    constructor <;> rw [← mul_assoc, inv_mul_cancel₀ hα, one_mul]
  right_inv ω := by
    obtain ⟨a, b⟩ := ω
    simp only [Prod.mk.injEq]
    constructor <;> rw [← mul_assoc, mul_inv_cancel₀ hα, one_mul]

/-- Pairs in the coordinates `(x, y)`, `x' = x + y`. -/
theorem sum_pair_eq {M : Type*} [AddCommMonoid M] (H : ZMod p × ZMod p → M) :
    ∑ ω, H ω = ∑ x, ∑ y, H (x, x + y) := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  exact (Equiv.sum_comp (Equiv.addLeft x) (fun x' => H (x, x'))).symm

/-- The deviation `φ_y(r) = (p-1)/2 · ∑_x T(r; x, x + y) - 1` of the conditional law of the
difference `z_v - z_u` from the uniform law on the nonzero squares. -/
noncomputable def phiPair {R : Type*} [Fintype R] (κ : FiniteLaw ((ZMod p × ZMod p) × R))
    (r : R) (y : ZMod p) : ℝ :=
  ((p : ℝ) - 1) / 2 * ∑ x, condMatrix κ r (x, x + y) - 1

/-- **The pair marginal is uniform on the strict-square pairs** (`lem:trace-mixing`(b): "the
pair `(z_u, z_v)` has law `Unif(Ω)`"): `κ_A(x, x') = 2/(p(p-1))` if `χ(x' - x) = 1`, else `0`. -/
theorem srcWeight_pair_uniform (hp2 : p ≠ 2) {R : Type*} [Fintype R]
    (κ : FiniteLaw ((ZMod p × ZMod p) × R))
    (hsupp : ∀ x x' r, quadraticChar (ZMod p) (x' - x) ≠ 1 → κ.weight ((x, x'), r) = 0)
    (τ : ZMod p → R ≃ R)
    (htr : ∀ β x x' r, κ.weight ((x + β, x' + β), τ β r) = κ.weight ((x, x'), r))
    (σ : ZMod p → R ≃ R)
    (hdil : ∀ α : ZMod p, quadraticChar (ZMod p) α = 1 → ∀ x x' r,
      κ.weight ((α * x, α * x'), σ α r) = κ.weight ((x, x'), r)) (x x' : ZMod p) :
    srcWeight κ (x, x') =
      if quadraticChar (ZMod p) (x' - x) = 1 then 2 / ((p : ℝ) * ((p : ℝ) - 1)) else 0 := by
  have hpP : p.Prime := Fact.out
  have hp3 : (3 : ℝ) ≤ p := by
    have h2 : 2 ≤ p := hpP.two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  set χ := quadraticChar (ZMod p) with hχdef
  set Q := univ.filter (fun y : ZMod p => χ y = 1) with hQ
  set nQ : ℝ := ((p : ℝ) - 1) / 2 with hnQ
  have hQcard : (Q.card : ℝ) = nQ := card_squares hp2
  have hnQ0 : 0 < nQ := by rw [hnQ]; linarith
  set s := srcWeight κ with hs
  have htrE (β : ZMod p) (a : ZMod p × ZMod p) (r : R) :
      κ.weight (pairTr β a, τ β r) = κ.weight (a, r) := htr β a.1 a.2 r
  have hα0 {α : ZMod p} (hα : χ α = 1) : α ≠ 0 := by
    intro h
    rw [h, hχdef, quadraticChar_zero] at hα
    exact zero_ne_one hα
  have hdilE (α : ZMod p) (hα : χ α = 1) (a : ZMod p × ZMod p) (r : R) :
      κ.weight (pairDil (hα0 hα) a, σ α r) = κ.weight (a, r) := hdil α hα a.1 a.2 r
  have hs_supp (x x' : ZMod p) (h : χ (x' - x) ≠ 1) : s (x, x') = 0 := by
    simp only [hs, srcWeight]
    exact Finset.sum_eq_zero (fun r _ => hsupp x x' r h)
  set s₀ := s (0, 1) with hs₀
  have hs_val (x x' : ZMod p) : s (x, x') = if χ (x' - x) = 1 then s₀ else 0 := by
    split_ifs with h
    · have h1 : s (x, x') = s (0, x' - x) := by
        have := srcWeight_equiv κ (pairTr x) (τ x) (fun a r => htrE x a r) (0, x' - x)
        change s (0 + x, x' - x + x) = s (0, x' - x) at this
        rw [zero_add, sub_add_cancel] at this
        exact this
      have h2 : s (0, x' - x) = s (0, 1) := by
        have := srcWeight_equiv κ (pairDil (hα0 h)) (σ (x' - x))
          (fun a r => hdilE (x' - x) h a r) (0, 1)
        change s ((x' - x) * 0, (x' - x) * 1) = s (0, 1) at this
        rw [mul_zero, mul_one] at this
        exact this
      rw [h1, h2]
    · exact hs_supp x x' h
  have hs₀val : s₀ = 1 / ((p : ℝ) * nQ) := by
    have htot := sum_srcWeight κ
    rw [← hs] at htot
    rw [sum_pair_eq] at htot
    simp only [hs_val, zmod_add_sub_cancel] at htot
    have h1 : ∑ y : ZMod p, (if χ y = 1 then s₀ else 0) = nQ * s₀ := by
      rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, ← hQ, hQcard]
    rw [Finset.sum_congr rfl (fun x _ => h1), sum_const, card_univ, ZMod.card,
      nsmul_eq_mul] at htot
    have hpq : (p : ℝ) * nQ ≠ 0 := by positivity
    field_simp
    linear_combination htot
  rw [hs_val, hs₀val, hnQ]
  split_ifs
  · field_simp
  · rfl

/-- **`lem:trace-mixing`(b), abstract form.** -/
theorem pair_trace_bound (hp2 : p ≠ 2) {R : Type*} [Fintype R]
    (κ : FiniteLaw ((ZMod p × ZMod p) × R))
    (hsupp : ∀ x x' r, quadraticChar (ZMod p) (x' - x) ≠ 1 → κ.weight ((x, x'), r) = 0)
    (τ : ZMod p → R ≃ R)
    (htr : ∀ β x x' r, κ.weight ((x + β, x' + β), τ β r) = κ.weight ((x, x'), r))
    (σ : ZMod p → R ≃ R)
    (hdil : ∀ α : ZMod p, quadraticChar (ZMod p) α = 1 → ∀ x x' r,
      κ.weight ((α * x, α * x'), σ α r) = κ.weight ((x, x'), r))
    (f : ZMod p × ZMod p → ℝ) (hf : ∑ ω, srcWeight κ ω * f ω = 0) :
    ∑ r, tgtWeight κ r * condOp κ f r ^ 2 ≤
      max (∑ r, tgtWeight κ r * (2 / ((p : ℝ) - 1) *
            ∑ y ∈ univ.filter (fun y => quadraticChar (ZMod p) y = 1), phiPair κ r y ^ 2))
          ((p : ℝ) * ∑ r, tgtWeight κ r * ∑ ω, condMatrix κ r ω ^ 2) *
        ∑ ω, srcWeight κ ω * f ω ^ 2 := by
  have hpP : p.Prime := Fact.out
  have hp3 : (3 : ℝ) ≤ p := by
    have h2 : 2 ≤ p := hpP.two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hpR0 : (0 : ℝ) < p := by linarith
  set χ := quadraticChar (ZMod p) with hχdef
  set Q := univ.filter (fun y : ZMod p => χ y = 1) with hQ
  set nQ : ℝ := ((p : ℝ) - 1) / 2 with hnQ
  have hQcard : (Q.card : ℝ) = nQ := card_squares hp2
  have hnQ0 : 0 < nQ := by rw [hnQ]; linarith
  set K := condMatrix κ with hK
  set t := tgtWeight κ with ht
  set s := srcWeight κ with hs
  -- the symmetries
  have hone : χ (1 : ZMod p) = 1 := map_one _
  have htrE (β : ZMod p) (a : ZMod p × ZMod p) (r : R) :
      κ.weight (pairTr β a, τ β r) = κ.weight (a, r) := htr β a.1 a.2 r
  have hα0 {α : ZMod p} (hα : χ α = 1) : α ≠ 0 := by
    intro h
    rw [h, hχdef, quadraticChar_zero] at hα
    exact zero_ne_one hα
  have hdilE (α : ZMod p) (hα : χ α = 1) (a : ZMod p × ZMod p) (r : R) :
      κ.weight (pairDil (hα0 hα) a, σ α r) = κ.weight (a, r) := hdil α hα a.1 a.2 r
  have hKtr (β : ZMod p) (r : R) (x x' : ZMod p) : K (τ β r) (x + β, x' + β) = K r (x, x') :=
    condMatrix_equiv κ (pairTr β) (τ β) (fun a r => htrE β a r) r (x, x')
  have httr (β : ZMod p) (r : R) : t (τ β r) = t r :=
    tgtWeight_equiv κ (pairTr β) (τ β) (fun a r => htrE β a r) r
  have hKdil (α : ZMod p) (hα : χ α = 1) (r : R) (x x' : ZMod p) :
      K (σ α r) (α * x, α * x') = K r (x, x') :=
    condMatrix_equiv κ (pairDil (hα0 hα)) (σ α) (fun a r => hdilE α hα a r) r (x, x')
  have htdil (α : ZMod p) (hα : χ α = 1) (r : R) : t (σ α r) = t r :=
    tgtWeight_equiv κ (pairDil (hα0 hα)) (σ α) (fun a r => hdilE α hα a r) r
  -- the support
  have hs_supp (x x' : ZMod p) (h : χ (x' - x) ≠ 1) : s (x, x') = 0 := by
    simp only [hs, srcWeight]
    exact Finset.sum_eq_zero (fun r _ => hsupp x x' r h)
  have hK_supp (r : R) (x x' : ZMod p) (h : χ (x' - x) ≠ 1) : K r (x, x') = 0 := by
    simp only [hK, condMatrix]
    split_ifs
    · exact hs_supp x x' h
    · rw [hsupp x x' r h, zero_div]
  -- the pair marginal is uniform on the strict-square pairs
  set s₀ := s (0, 1) with hs₀
  have hs_val (x x' : ZMod p) : s (x, x') = if χ (x' - x) = 1 then s₀ else 0 := by
    split_ifs with h
    · have h1 : s (x, x') = s (0, x' - x) := by
        have := srcWeight_equiv κ (pairTr x) (τ x) (fun a r => htrE x a r) (0, x' - x)
        change s (0 + x, x' - x + x) = s (0, x' - x) at this
        rw [zero_add, sub_add_cancel] at this
        exact this
      have h2 : s (0, x' - x) = s (0, 1) := by
        have := srcWeight_equiv κ (pairDil (hα0 h)) (σ (x' - x))
          (fun a r => hdilE (x' - x) h a r) (0, 1)
        change s ((x' - x) * 0, (x' - x) * 1) = s (0, 1) at this
        rw [mul_zero, mul_one] at this
        exact this
      rw [h1, h2]
    · exact hs_supp x x' h
  have hs₀val : s₀ = 1 / ((p : ℝ) * nQ) := by
    have htot := sum_srcWeight κ
    rw [← hs] at htot
    rw [sum_pair_eq] at htot
    simp only [hs_val, zmod_add_sub_cancel] at htot
    have h1 : ∑ y : ZMod p, (if χ y = 1 then s₀ else 0) = nQ * s₀ := by
      rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, ← hQ, hQcard]
    rw [Finset.sum_congr rfl (fun x _ => h1), sum_const, card_univ, ZMod.card,
      nsmul_eq_mul] at htot
    have hpq : (p : ℝ) * nQ ≠ 0 := by positivity
    field_simp
    linear_combination htot
  -- the decomposition
  set g : ZMod p → ℝ := fun y => (1 / (p : ℝ)) * ∑ x, f (x, x + y) with hg
  set f₀ : ZMod p × ZMod p → ℝ := fun ω => g (ω.2 - ω.1) with hf₀
  set f₁ : ZMod p × ZMod p → ℝ := fun ω => if χ (ω.2 - ω.1) = 1 then f ω - f₀ ω else 0
    with hf₁
  have hf₁sum (y : ZMod p) : ∑ x, f₁ (x, x + y) = 0 := by
    simp only [hf₁, hf₀, zmod_add_sub_cancel]
    by_cases hy : χ y = 1
    · simp only [hy, ite_true]
      rw [Finset.sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, hg]
      field_simp
      ring
    · simp only [hy, ite_false, sum_const_zero]
  have hgQ : ∑ y ∈ Q, g y = 0 := by
    have h1 : ∑ ω, s ω * f ω = s₀ * ((p : ℝ) * ∑ y ∈ Q, g y) := by
      rw [sum_pair_eq]
      simp only [hs_val, zmod_add_sub_cancel, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_irrel, sum_const_zero]
      rw [← Finset.sum_filter, ← hQ, Finset.mul_sum, Finset.mul_sum]
      apply sum_congr rfl
      intro y _
      rw [← Finset.mul_sum, hg]
      field_simp
    rw [hf] at h1
    have hs₀0 : s₀ ≠ 0 := by
      rw [hs₀val]
      positivity
    have := mul_eq_zero.mp h1.symm
    rcases this with h | h
    · exact absurd h hs₀0
    · rcases mul_eq_zero.mp h with h' | h'
      · linarith
      · exact h'
  -- the conditional operator splits
  have hTsplit (r : R) : condOp κ f r = condOp κ f₀ r + condOp κ f₁ r := by
    simp only [condOp, Matrix.mulVec, dotProduct, ← hK]
    rw [← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro ω _
    by_cases h : χ (ω.2 - ω.1) = 1
    · simp only [hf₁, h, ite_true]
      ring
    · rw [hK_supp r ω.1 ω.2 h]
      ring
  -- translation invariance of `T f₀` and the average of `T f₁`
  have hTf₀ (β : ZMod p) (r : R) : condOp κ f₀ (τ β r) = condOp κ f₀ r := by
    simp only [condOp, Matrix.mulVec, dotProduct, ← hK]
    rw [← Equiv.sum_comp (pairTr β)]
    apply sum_congr rfl
    intro ω _
    change K (τ β r) (ω.1 + β, ω.2 + β) * f₀ (ω.1 + β, ω.2 + β) = K r ω * f₀ ω
    rw [hKtr]
    simp only [hf₀]
    congr 2
    ring
  have hTf₁avg (r : R) : ∑ β, condOp κ f₁ (τ β r) = 0 := by
    simp only [condOp, Matrix.mulVec, dotProduct, ← hK]
    have h1 (β : ZMod p) : ∑ ω, K (τ β r) ω * f₁ ω = ∑ ω, K r ω * f₁ (ω.1 + β, ω.2 + β) := by
      rw [← Equiv.sum_comp (pairTr β)]
      apply sum_congr rfl
      intro ω _
      change K (τ β r) (ω.1 + β, ω.2 + β) * f₁ (ω.1 + β, ω.2 + β) = _
      rw [hKtr]
    simp only [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro ω _
    rw [← Finset.mul_sum]
    have h2 : ∑ β, f₁ (ω.1 + β, ω.2 + β) = ∑ x, f₁ (x, x + (ω.2 - ω.1)) := by
      rw [← Equiv.sum_comp (Equiv.addLeft ω.1) (fun x => f₁ (x, x + (ω.2 - ω.1)))]
      apply sum_congr rfl
      intro β _
      change f₁ (ω.1 + β, ω.2 + β) = f₁ (ω.1 + β, ω.1 + β + (ω.2 - ω.1))
      rw [show ω.1 + β + (ω.2 - ω.1) = ω.2 + β by ring]
    rw [h2, hf₁sum, mul_zero]
  have hcross : ∑ r, t r * (condOp κ f₀ r * condOp κ f₁ r) = 0 := by
    have h1 (β : ZMod p) : ∑ r, t r * (condOp κ f₀ r * condOp κ f₁ r) =
        ∑ r, t r * (condOp κ f₀ r * condOp κ f₁ (τ β r)) := by
      rw [← Equiv.sum_comp (τ β)]
      apply sum_congr rfl
      intro r _
      rw [httr, hTf₀]
    have h2 : (p : ℝ) * ∑ r, t r * (condOp κ f₀ r * condOp κ f₁ r) =
        ∑ r, t r * (condOp κ f₀ r * ∑ β, condOp κ f₁ (τ β r)) := by
      calc (p : ℝ) * ∑ r, t r * (condOp κ f₀ r * condOp κ f₁ r)
          = ∑ β : ZMod p, ∑ r, t r * (condOp κ f₀ r * condOp κ f₁ (τ β r)) := by
            simp only [← h1, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
        _ = ∑ r, t r * (condOp κ f₀ r * ∑ β, condOp κ f₁ (τ β r)) := by
            rw [Finset.sum_comm]
            apply sum_congr rfl
            intro r _
            rw [Finset.mul_sum, Finset.mul_sum]
    simp only [hTf₁avg, mul_zero, sum_const_zero] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · exact h
  -- frequency zero
  set A : ℝ := ∑ r, t r * (2 / ((p : ℝ) - 1) * ∑ y ∈ Q, phiPair κ r y ^ 2) with hA
  have hnorm₀ : ∑ ω, s ω * f₀ ω ^ 2 = 1 / nQ * ∑ y ∈ Q, g y ^ 2 := by
    rw [sum_pair_eq]
    simp only [hs_val, hf₀, zmod_add_sub_cancel, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_irrel, sum_const_zero, sum_const, card_univ, ZMod.card,
      nsmul_eq_mul]
    rw [← Finset.sum_filter, ← hQ, hs₀val, Finset.mul_sum]
    apply sum_congr rfl
    intro y _
    field_simp
  have hzero : ∑ r, t r * condOp κ f₀ r ^ 2 ≤ A * ∑ ω, s ω * f₀ ω ^ 2 := by
    rw [hnorm₀, hA, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro r _
    have hrow : ∑ y, ∑ x, K r (x, x + y) = 1 := by
      have := condMatrix_row_sum κ r
      rw [← hK, sum_pair_eq, Finset.sum_comm] at this
      exact this
    have hkQ : ∑ y ∈ Q, ∑ x, K r (x, x + y) = 1 := by
      rw [← hrow, hQ, Finset.sum_filter]
      apply sum_congr rfl
      intro y _
      split_ifs with hy
      · rfl
      · symm
        exact Finset.sum_eq_zero (fun x _ => hK_supp r x (x + y) (by rwa [zmod_add_sub_cancel]))
    have hT0 : condOp κ f₀ r = 1 / nQ * ∑ y ∈ Q, phiPair κ r y * g y := by
      have h1 : condOp κ f₀ r = ∑ y ∈ Q, (∑ x, K r (x, x + y)) * g y := by
        simp only [condOp, Matrix.mulVec, dotProduct, ← hK]
        rw [sum_pair_eq, Finset.sum_comm, hQ, Finset.sum_filter]
        apply sum_congr rfl
        intro y _
        simp only [hf₀, zmod_add_sub_cancel]
        rw [← Finset.sum_mul]
        by_cases hy : χ y = 1
        · rw [ite_eq_left hy]
        · rw [ite_eq_right hy, Finset.sum_eq_zero
            (fun x _ => hK_supp r x (x + y) (by rwa [zmod_add_sub_cancel])), zero_mul]
      rw [h1]
      have h2 : ∑ y ∈ Q, phiPair κ r y * g y =
          nQ * ∑ y ∈ Q, (∑ x, K r (x, x + y)) * g y - ∑ y ∈ Q, g y := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply sum_congr rfl
        intro y _
        simp only [phiPair, ← hK, ← hnQ]
        ring
      rw [h2, hgQ, sub_zero]
      field_simp
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq Q (fun y => phiPair κ r y) g
    rw [hT0]
    have ht0 : 0 ≤ t r := tgtWeight_nonneg κ r
    have hsq : (1 / nQ * ∑ y ∈ Q, phiPair κ r y * g y) ^ 2 ≤
        2 / ((p : ℝ) - 1) * (∑ y ∈ Q, phiPair κ r y ^ 2) * (1 / nQ * ∑ y ∈ Q, g y ^ 2) := by
      have h2 : 2 / ((p : ℝ) - 1) = 1 / nQ := by rw [hnQ]; field_simp
      rw [h2, mul_pow]
      have h3 : (1 / nQ) ^ 2 * (∑ y ∈ Q, phiPair κ r y * g y) ^ 2 ≤
          (1 / nQ) ^ 2 * ((∑ y ∈ Q, phiPair κ r y ^ 2) * ∑ y ∈ Q, g y ^ 2) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)
      calc (1 / nQ) ^ 2 * (∑ y ∈ Q, phiPair κ r y * g y) ^ 2
          ≤ (1 / nQ) ^ 2 * ((∑ y ∈ Q, phiPair κ r y ^ 2) * ∑ y ∈ Q, g y ^ 2) := h3
        _ = 1 / nQ * (∑ y ∈ Q, phiPair κ r y ^ 2) * (1 / nQ * ∑ y ∈ Q, g y ^ 2) := by ring
    calc t r * (1 / nQ * ∑ y ∈ Q, phiPair κ r y * g y) ^ 2
        ≤ t r * (2 / ((p : ℝ) - 1) * (∑ y ∈ Q, phiPair κ r y ^ 2) *
            (1 / nQ * ∑ y ∈ Q, g y ^ 2)) := mul_le_mul_of_nonneg_left hsq ht0
      _ = t r * (2 / ((p : ℝ) - 1) * ∑ y ∈ Q, phiPair κ r y ^ 2) *
            (1 / nQ * ∑ y ∈ Q, g y ^ 2) := by ring
  -- nonzero frequencies
  set B : ℝ := (p : ℝ) * ∑ r, t r * ∑ ω, K r ω ^ 2 with hB
  have hnorm₁ : ∑ ω, f₁ ω ^ 2 = (p : ℝ) * nQ * ∑ ω, s ω * f₁ ω ^ 2 := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro ω _
    rw [hs_val ω.1 ω.2]
    simp only [hf₁]
    split_ifs with h
    · rw [hs₀val]
      field_simp
    · ring
  have hone' : ∑ r, t r * condOp κ f₁ r ^ 2 ≤ B * ∑ ω, s ω * f₁ ω ^ 2 := by
    have hF := fourier_step hp2 t (tgtWeight_nonneg κ) (fun r x y => K r (x, x + y)) τ
      (fun β r x y => by
        have := hKtr β r x (x + y)
        rw [show x + β + y = x + y + β by ring]
        exact this)
      httr σ
      (fun α hα r x y => by
        have := hKdil α hα r x (x + y)
        rw [show α * x + α * y = α * (x + y) by ring]
        exact this)
      (fun α hα r => htdil α hα r) (fun x y => f₁ (x, x + y)) (fun y => hf₁sum y)
    have hL : ∑ r, t r * (∑ x, ∑ y, K r (x, x + y) * f₁ (x, x + y)) ^ 2 =
        ∑ r, t r * condOp κ f₁ r ^ 2 := by
      apply sum_congr rfl
      intro r _
      congr 2
      simp only [condOp, Matrix.mulVec, dotProduct, ← hK]
      rw [sum_pair_eq]
    have hR1 : ∑ r, t r * ∑ x, ∑ y, K r (x, x + y) ^ 2 = ∑ r, t r * ∑ ω, K r ω ^ 2 := by
      apply sum_congr rfl
      intro r _
      rw [sum_pair_eq (fun ω => K r ω ^ 2)]
    have hR2 : ∑ x, ∑ y, f₁ (x, x + y) ^ 2 = ∑ ω, f₁ ω ^ 2 :=
      (sum_pair_eq (fun ω => f₁ ω ^ 2)).symm
    rw [hL, hR1, hR2, hnorm₁] at hF
    refine hF.trans (le_of_eq ?_)
    rw [hB, hnQ]
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  -- combine
  have hnorm : ∑ ω, s ω * f ω ^ 2 = ∑ ω, s ω * f₀ ω ^ 2 + ∑ ω, s ω * f₁ ω ^ 2 := by
    rw [← Finset.sum_add_distrib]
    have hcr : ∑ ω, s ω * (f₀ ω * f₁ ω) = 0 := by
      rw [sum_pair_eq]
      simp only [hs_val, hf₀, zmod_add_sub_cancel, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : χ y = 1
      · simp only [hy, ite_true]
        rw [← Finset.mul_sum]
        have : ∑ x, g y * f₁ (x, x + y) = 0 := by rw [← Finset.mul_sum, hf₁sum, mul_zero]
        rw [this, mul_zero]
      · simp only [hy, ite_false, sum_const_zero]
    have hsplit : ∑ ω, s ω * f ω ^ 2 =
        ∑ ω, (s ω * f₀ ω ^ 2 + s ω * f₁ ω ^ 2) + 2 * ∑ ω, s ω * (f₀ ω * f₁ ω) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro ω _
      rw [hs_val ω.1 ω.2]
      split_ifs with h
      · simp only [hf₁, h, ite_true]
        ring
      · ring
    rw [hsplit, hcr, mul_zero, add_zero]
  have hE : ∑ r, t r * condOp κ f r ^ 2 =
      ∑ r, t r * condOp κ f₀ r ^ 2 + ∑ r, t r * condOp κ f₁ r ^ 2 := by
    have h1 : ∑ r, t r * condOp κ f r ^ 2 = ∑ r, t r * condOp κ f₀ r ^ 2 +
        ∑ r, t r * condOp κ f₁ r ^ 2 + 2 * ∑ r, t r * (condOp κ f₀ r * condOp κ f₁ r) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro r _
      rw [hTsplit]
      ring
    rw [h1, hcross, mul_zero, add_zero]
  have hA0 : 0 ≤ ∑ ω, s ω * f₀ ω ^ 2 :=
    Finset.sum_nonneg (fun ω _ => mul_nonneg (srcWeight_nonneg κ ω) (sq_nonneg _))
  have hB0 : 0 ≤ ∑ ω, s ω * f₁ ω ^ 2 :=
    Finset.sum_nonneg (fun ω _ => mul_nonneg (srcWeight_nonneg κ ω) (sq_nonneg _))
  rw [hE, hnorm]
  calc ∑ r, t r * condOp κ f₀ r ^ 2 + ∑ r, t r * condOp κ f₁ r ^ 2
      ≤ A * ∑ ω, s ω * f₀ ω ^ 2 + B * ∑ ω, s ω * f₁ ω ^ 2 := add_le_add hzero hone'
    _ ≤ max A B * ∑ ω, s ω * f₀ ω ^ 2 + max A B * ∑ ω, s ω * f₁ ω ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hA0)
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hB0)
    _ = max A B * (∑ ω, s ω * f₀ ω ^ 2 + ∑ ω, s ω * f₁ ω ^ 2) := by ring

end Sarkozy.TraceMixing
