module

public import Sarkozy.JointRows.Eig
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The normalized Paley operator satisfies `PaleyLike` (`lem:spec:gauss`, real form)

Sources: `paper/sections/14_spectral.tex`, `lem:spec:gauss`; `paper/sections/16_extraction.tex`,
`prop:conditional-star` ("`Φ̂ = C/r` the normalized Paley operator, so that `Φ̂𝟙 = 0`,
`Φ̂* = -Φ̂` and `Φ̂² = -I` on `ℋ`").

For a prime `p ≡ 3 (mod 4)`, with `χ` the quadratic character of `𝔽_p` (`quadraticChar`, real
valued: `chiR`), the normalized Paley operator is `Φ̂ f(a) = √p · E_b χ(b - a) f(b)` (`paley`),
that is `C/r` with `C h(a) = E_b χ(b - a) h(b)` and `r = p^{-1/2}`.

* `paley_anti`, `paley_sq`, `paley_paleyLike`: `Φ̂` satisfies `Eig.PaleyLike` for the uniform
  law on `𝔽_p`, i.e. `Φ̂* = -Φ̂` and `Φ̂² = -(I - J)`;
* `heig_paley`: with `Eig.heig_holds`, the eigenspace bound of `lem:joint-potential` for the
  actual operator.

**Proof.**
* *Antisymmetry*: `χ(a - b) = χ(-1)χ(b - a) = -χ(b - a)` (`chi_neg_one`, `p ≡ 3 (mod 4)`).
* *Square*: `Φ̂² f(a) = (1/p)∑_c f(c) S(a, c)` with `S(a, c) = ∑_b χ(b - a)χ(c - b)`.
  - `S(a, a) = -(p - 1)`;
  - for `a ≠ c`, `S(a, c) = ∑_x χ(x)χ(1 - x) = J(χ, χ) = -χ(-1) = 1`, by the substitution
    `b = a + (c - a)x` and Mathlib's `jacobiSum_nontrivial_inv` (with `χ⁻¹ = χ`).
  - Hence `Φ̂² f(a) = (∑_c f(c) - p f(a))/p = -(f(a) - E f)`.

Mathlib's quadratic-character and Jacobi-sum facts are used; `thm:gauss` itself is not needed.
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace Sarkozy.JointRows

namespace PaleyGauss

variable {p : ℕ} [Fact p.Prime]

/-- The quadratic character of `𝔽_p`, real valued. -/
noncomputable def chiR (p : ℕ) [Fact p.Prime] (x : ZMod p) : ℝ :=
  ((quadraticChar (ZMod p) x : ℤ) : ℝ)

/-- **The normalized Paley operator** `Φ̂ f(a) = √p · E_b χ(b - a) f(b)`. -/
noncomputable def paley (p : ℕ) [Fact p.Prime] (f : ZMod p → ℝ) (a : ZMod p) : ℝ :=
  Real.sqrt p / p * ∑ b, chiR p (b - a) * f b

theorem ringChar_ne_two (hp : p % 4 = 3) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  omega

theorem chi_neg_one (hp : p % 4 = 3) : quadraticChar (ZMod p) (-1) = -1 := by
  rw [quadraticChar_neg_one (ringChar_ne_two hp), ZMod.card, ZMod.χ₄_nat_three_mod_four hp]

theorem chiR_mul (x y : ZMod p) : chiR p (x * y) = chiR p x * chiR p y := by
  unfold chiR
  rw [map_mul]
  push_cast
  ring

theorem chiR_neg (hp : p % 4 = 3) (x : ZMod p) : chiR p (-x) = -chiR p x := by
  rw [show -x = (-1) * x by ring, chiR_mul]
  unfold chiR
  rw [chi_neg_one hp]
  push_cast
  ring

theorem chiR_zero : chiR p 0 = 0 := by
  unfold chiR
  rw [quadraticChar_zero]
  simp

theorem chiR_sq {x : ZMod p} (hx : x ≠ 0) : chiR p x * chiR p x = 1 := by
  unfold chiR
  have h := quadraticChar_sq_one hx (F := ZMod p)
  rw [← sq]
  exact_mod_cast h

/-- **`∑_x χ(x)χ(1 - x) = 1`** for `p ≡ 3 (mod 4)` (`J(χ, χ) = -χ(-1)`). -/
theorem jacobi_one (hp : p % 4 = 3) : ∑ x : ZMod p, chiR p x * chiR p (1 - x) = 1 := by
  have hJ := jacobiSum_nontrivial_inv (quadraticChar_ne_one (ringChar_ne_two hp) (F := ZMod p))
  rw [(quadraticChar_isQuadratic (ZMod p)).inv, chi_neg_one hp, neg_neg] at hJ
  unfold jacobiSum at hJ
  have h := congrArg (fun z : ℤ => (z : ℝ)) hJ
  push_cast at h
  simpa only [chiR] using h

/-- `S(a, c) = 1` for `a ≠ c`. -/
theorem sum_chi_shift (hp : p % 4 = 3) {a c : ZMod p} (hac : a ≠ c) :
    ∑ b, chiR p (b - a) * chiR p (c - b) = 1 := by
  have hd : c - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hac)
  let e : ZMod p ≃ ZMod p :=
    { toFun := fun x => a + (c - a) * x
      invFun := fun b => (b - a) / (c - a)
      left_inv := fun x => by field_simp; ring
      right_inv := fun b => by field_simp; ring }
  rw [← Fintype.sum_equiv e (fun x => chiR p (e x - a) * chiR p (c - e x)) _ (fun _ => rfl)]
  rw [← jacobi_one hp]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : e x - a = (c - a) * x := by simp only [e, Equiv.coe_fn_mk]; ring
  have h2 : c - e x = (c - a) * (1 - x) := by simp only [e, Equiv.coe_fn_mk]; ring
  rw [h1, h2, chiR_mul, chiR_mul]
  have hs := chiR_sq hd
  linear_combination (chiR p x * chiR p (1 - x)) * hs

/-- `S(a, a) = -(p - 1)`. -/
theorem sum_chi_diag (hp : p % 4 = 3) (a : ZMod p) :
    ∑ b, chiR p (b - a) * chiR p (a - b) = 1 - (p : ℝ) := by
  have h : ∀ b, chiR p (b - a) * chiR p (a - b) = (if b = a then 1 else 0) - 1 := by
    intro b
    rw [show a - b = -(b - a) by ring, chiR_neg hp]
    by_cases hb : b = a
    · subst hb; simp [chiR_zero]
    · have := chiR_sq (sub_ne_zero.mpr hb) (p := p)
      simp only [hb, ↓reduceIte]
      linarith
  rw [Finset.sum_congr rfl fun b _ => h b, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp

/-- **`Φ̂* = -Φ̂`**: `∑_t f(t)Φ̂g(t) = -∑_t Φ̂f(t)g(t)`. -/
theorem paley_anti (hp : p % 4 = 3) (f g : ZMod p → ℝ) :
    ∑ t, f t * paley p g t = -∑ t, paley p f t * g t := by
  unfold paley
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [show u - v = -(v - u) by ring, chiR_neg hp]
  ring

/-- **`Φ̂² = -(I - J)`**: `Φ̂(Φ̂f)(a) = -(f(a) - E f)`. -/
theorem paley_sq (hp : p % 4 = 3) (f : ZMod p → ℝ) (a : ZMod p) :
    paley p (paley p f) a = -(f a - (∑ c, f c) / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hsplit : paley p (paley p f) a =
      Real.sqrt p / p * (Real.sqrt p / p * ∑ c, f c * ∑ b, chiR p (b - a) * chiR p (c - b)) := by
    unfold paley
    congr 1
    simp only [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hsum : ∀ c, f c * ∑ b, chiR p (b - a) * chiR p (c - b) =
      f c - (if c = a then (p : ℝ) * f a else 0) := by
    intro c
    by_cases hc : c = a
    · subst hc
      rw [sum_chi_diag hp]
      simp only [↓reduceIte]
      ring
    · rw [sum_chi_shift hp (Ne.symm hc)]
      simp only [hc, ↓reduceIte]
      ring
  have hS : ∑ c, f c * ∑ b, chiR p (b - a) * chiR p (c - b) = (∑ c, f c) - p * f a := by
    rw [Finset.sum_congr rfl fun c _ => hsum c, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp
  rw [hsplit, hS]
  set s := Real.sqrt p with hsdef
  have hs : s * s = p := Real.mul_self_sqrt hp0.le
  have hs0 : s ≠ 0 := by rw [hsdef]; positivity
  rw [← hs]
  field_simp
  ring

/-- **`Φ̂` satisfies `PaleyLike`** (`lem:spec:gauss`, real form) for `p ≡ 3 (mod 4)`. -/
theorem paley_paleyLike (hp : p % 4 = 3) :
    Eig.PaleyLike (FiniteLaw.uniform (ZMod p)) (paley p) := by
  have hcard : (Fintype.card (ZMod p) : ℝ) = p := by rw [ZMod.card]
  constructor
  · intro f g
    rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform, paley_anti hp, neg_div]
  · intro f a
    rw [FiniteLaw.expect_uniform, hcard]
    exact paley_sq hp f a

/-- **`heig` for the actual normalized Paley operator** (`p ≡ 3 (mod 4)`): `Eig.heig_holds` with
`λ` uniform on `𝔽_p` and `Φ = Φ̂`, so the eigenspace bound of `lem:joint-potential` needs only
`T - i𝒵 ⪰ 0`. -/
theorem heig_paley (hp : p % 4 = 3) {n : Type*} [Fintype n] (T Z : Matrix n n ℝ)
    (hN : (RowsA.cplx T - Complex.I • RowsA.cplx Z).PosSemidef) (y : ZMod p → n → ℝ) :
    -(FiniteLaw.uniform (ZMod p)).expect (fun t => y t ⬝ᵥ (T *ᵥ y t)) ≤
      Eig.zqForm (FiniteLaw.uniform (ZMod p)) (paley p) Z y :=
  Eig.heig_holds _ (paley_paleyLike hp) T Z hN y

end PaleyGauss

end Sarkozy.JointRows
