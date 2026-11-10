module

public import Sarkozy.JointRows.Sector
public import Sarkozy.JointRows.Potential

/-!
# The eigenspace bound of `lem:joint-potential` (`heig`)

Source: `paper/sections/16_extraction.tex`, proof of `lem:joint-potential`: "On the eigenspaces of
`Φ̂` for `i`, `-i` and `0` the operator `T ⊗ I + 𝒵 ⊗ Φ̂` is `T + i𝒵`, `T - i𝒵` and `T`, all positive
semidefinite (the last by averaging the first two); so `D(𝒵 ⊗ Φ̂)D ⪰ -D(T ⊗ I)D`"; and
`lem:spec:gauss` (`Φ̂* = -Φ̂`, `Φ̂² = -I` on `ℋ = L²_0(𝔽_p)`, `Φ̂` extended by zero to the
constants).

`Potential.pure_part_potential` took `Zq(y) ≥ -E_t y(t)ᵀTy(t)` as the hypothesis `heig`, with
`Zq(y) = ⟨y, (𝒵 ⊗ Φ̂)y⟩`. Here, for any finite law `λ` (the uniform law on `𝔽_p` in the paper) and
any `Φ` with `E[f Φg] = -E[(Φf) g]` and `Φ(Φf) = -(f - E f)` (`PaleyLike`):

* `zqForm λ Φ 𝒵 y = ∑_{pq} 𝒵_{pq} E[y_p Φ(y_q)]`, the form of `𝒵 ⊗ Φ̂`;
* `heig_holds`: if `T - i𝒵 ⪰ 0` (as a complex matrix), then `zqForm λ Φ 𝒵 y ≥ -E_t y(t)ᵀTy(t)`;
* `pure_part_potential_eig`: `pure_part_potential` with `Zq = zqForm` and `heig` discharged.

**Proof.** The functionals `f ↦ √λ(x) f(x)`, `x ∈ Ω`, are a Parseval frame of `L²(λ)`. With
`α_x(p) = √λ(x) y_p(x)`, `β_x(p) = √λ(x)(Φy_p)(x)`, the sum over `x` of the real parts of
`c_x^*(T - i𝒵)c_x`, `c_x = α_x + iβ_x` (`Sector.re_quad_nonneg`), is
`∑_{pq} T_{pq}(2E[y_p y_q] - E y_p E y_q) + 2𝒵_{pq} E[y_p Φy_q] ≥ 0`, by the two identities of
`Φ`. The
constant part `∑ T_{pq} E y_p E y_q` is `≥ 0` (real vectors). This is the paper's argument: the
constants (eigenvalue `0`) carry `T`, and the rest carries `T - i𝒵`.
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace Sarkozy.JointRows

namespace Eig

variable {Ωt : Type*} [Fintype Ωt] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The properties of `Φ̂` used** (`lem:spec:gauss`, with `Φ̂` extended by zero to the
constants): `Φ* = -Φ` on `L²(λ)` and `Φ² = -(I - J)`. -/
structure PaleyLike (lam : FiniteLaw Ωt) (Φ : (Ωt → ℝ) → (Ωt → ℝ)) : Prop where
  anti : ∀ f g : Ωt → ℝ, lam.expect (fun t => f t * Φ g t) = -lam.expect (fun t => Φ f t * g t)
  sq : ∀ (f : Ωt → ℝ) (t : Ωt), Φ (Φ f) t = -(f t - lam.expect f)

/-- **The form of `𝒵 ⊗ Φ̂`**: `∑_{pq} 𝒵_{pq} E[y_p Φ(y_q)]`, `y_p = y(·)_p`. -/
noncomputable def zqForm (lam : FiniteLaw Ωt) (Φ : (Ωt → ℝ) → (Ωt → ℝ)) (Z : Matrix n n ℝ)
    (y : Ωt → n → ℝ) : ℝ :=
  ∑ p, ∑ q, Z p q * lam.expect (fun t => y t p * Φ (fun t' => y t' q) t)

omit [DecidableEq n] in
theorem expect_quad (lam : FiniteLaw Ωt) (T : Matrix n n ℝ) (y : Ωt → n → ℝ) :
    lam.expect (fun t => y t ⬝ᵥ (T *ᵥ y t)) =
      ∑ p, ∑ q, T p q * lam.expect (fun t => y t p * y t q) := by
  simp only [dotProduct, mulVec, FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun t _ => ?_
  ring

omit [DecidableEq n] in
/-- **`heig` holds**: if `T - i𝒵 ⪰ 0`, then `⟨y, (𝒵 ⊗ Φ̂)y⟩ ≥ -E_t y(t)ᵀTy(t)`. -/
theorem heig_holds (lam : FiniteLaw Ωt) {Φ : (Ωt → ℝ) → (Ωt → ℝ)} (hΦ : PaleyLike lam Φ)
    (T Z : Matrix n n ℝ)
    (hN : (RowsA.cplx T - Complex.I • RowsA.cplx Z).PosSemidef) (y : Ωt → n → ℝ) :
    -lam.expect (fun t => y t ⬝ᵥ (T *ᵥ y t)) ≤ zqForm lam Φ Z y := by
  set N := RowsA.cplx T - Complex.I • RowsA.cplx Z with hNdef
  have hre : ∀ p q, (N p q).re = T p q := fun p q => by
    simp [hNdef, RowsA.cplx]
  have him : ∀ p q, (N p q).im = -Z p q := fun p q => by
    simp [hNdef, RowsA.cplx]
  set yc : n → Ωt → ℝ := fun p t => y t p
  -- the frame sum
  have hx : ∀ x : Ωt, 0 ≤ ∑ p, ∑ q, ((N p q).re *
      (√(lam.weight x) * yc p x * (√(lam.weight x) * yc q x) +
        √(lam.weight x) * Φ (yc p) x * (√(lam.weight x) * Φ (yc q) x)) -
      (N p q).im * (√(lam.weight x) * yc p x * (√(lam.weight x) * Φ (yc q) x) -
        √(lam.weight x) * Φ (yc p) x * (√(lam.weight x) * yc q x))) :=
    fun x => Sector.re_quad_nonneg hN (fun p => √(lam.weight x) * yc p x)
      (fun p => √(lam.weight x) * Φ (yc p) x)
  have hsum := Finset.sum_nonneg fun x (_ : x ∈ Finset.univ) => hx x
  simp only [hre, him] at hsum
  have hsq : ∀ x, √(lam.weight x) * √(lam.weight x) = lam.weight x :=
    fun x => Real.mul_self_sqrt (lam.nonneg x)
  have hframe : ∑ x, ∑ p, ∑ q, (T p q *
      (√(lam.weight x) * yc p x * (√(lam.weight x) * yc q x) +
        √(lam.weight x) * Φ (yc p) x * (√(lam.weight x) * Φ (yc q) x)) -
      -Z p q * (√(lam.weight x) * yc p x * (√(lam.weight x) * Φ (yc q) x) -
        √(lam.weight x) * Φ (yc p) x * (√(lam.weight x) * yc q x))) =
      ∑ p, ∑ q, (T p q * (lam.expect (fun t => yc p t * yc q t) +
        lam.expect (fun t => Φ (yc p) t * Φ (yc q) t)) +
      Z p q * (lam.expect (fun t => yc p t * Φ (yc q) t) -
        lam.expect (fun t => Φ (yc p) t * yc q t))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [FiniteLaw.expect, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have := hsq x
    linear_combination (T p q * (yc p x * yc q x + Φ (yc p) x * Φ (yc q) x) +
      Z p q * (yc p x * Φ (yc q) x - Φ (yc p) x * yc q x)) * this
  rw [hframe] at hsum
  -- the two identities of `Φ`
  have hA : ∀ p q, lam.expect (fun t => Φ (yc p) t * yc q t) =
      -lam.expect (fun t => yc p t * Φ (yc q) t) := by
    intro p q
    rw [hΦ.anti (yc p) (yc q), neg_neg]
  have hB : ∀ p q, lam.expect (fun t => Φ (yc p) t * Φ (yc q) t) =
      lam.expect (fun t => yc p t * yc q t) - lam.expect (yc p) * lam.expect (yc q) := by
    intro p q
    have h1 := hΦ.anti (yc p) (Φ (yc q))
    have h2 : lam.expect (fun t => yc p t * Φ (Φ (yc q)) t) =
        -(lam.expect (fun t => yc p t * yc q t) - lam.expect (yc p) * lam.expect (yc q)) := by
      simp only [hΦ.sq]
      rw [show (fun t => yc p t * -(yc q t - lam.expect (yc q))) =
          fun t => -(yc p t * yc q t) + lam.expect (yc q) * yc p t from funext fun t => by ring,
        FiniteLaw.expect_add, FiniteLaw.expect_const_mul]
      have : lam.expect (fun t => -(yc p t * yc q t)) = -lam.expect (fun t => yc p t * yc q t) := by
        rw [show (fun t => -(yc p t * yc q t)) = fun t => (-1) * (yc p t * yc q t) from
          funext fun t => by ring, FiniteLaw.expect_const_mul]
        ring
      rw [this]
      ring
    linarith
  simp only [hA, hB] at hsum
  -- the constant part: `∑ T_{pq} E y_p E y_q ≥ 0`
  have hT0 : 0 ≤ ∑ p, ∑ q, T p q * (lam.expect (yc p) * lam.expect (yc q)) := by
    have := Sector.re_quad_nonneg hN (fun p => lam.expect (yc p)) (fun _ => 0)
    simp only [hre, him, mul_zero, add_zero, sub_zero, zero_mul] at this
    exact this
  rw [expect_quad]
  unfold zqForm
  have hsplit : ∑ p, ∑ q, (T p q * (lam.expect (fun t => yc p t * yc q t) +
      (lam.expect (fun t => yc p t * yc q t) - lam.expect (yc p) * lam.expect (yc q))) +
      Z p q * (lam.expect (fun t => yc p t * Φ (yc q) t) -
        -lam.expect (fun t => yc p t * Φ (yc q) t))) =
      2 * (∑ p, ∑ q, T p q * lam.expect (fun t => yc p t * yc q t)) -
        ∑ p, ∑ q, T p q * (lam.expect (yc p) * lam.expect (yc q)) +
        2 * ∑ p, ∑ q, Z p q * lam.expect (fun t => yc p t * Φ (yc q) t) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [hsplit] at hsum
  change -(∑ p, ∑ q, T p q * lam.expect (fun t => yc p t * yc q t)) ≤
    ∑ p, ∑ q, Z p q * lam.expect (fun t => yc p t * Φ (yc q) t)
  linarith

/-- **`lem:joint-potential`, the pure part, with `heig` proved**: `Potential.pure_part_potential`
with `Zq = zqForm λ Φ 𝒵` for a `Φ` with the properties of `Φ̂` (`PaleyLike`, `lem:spec:gauss`)
and `T - i𝒵 ⪰ 0` (the paper's `T ± i𝒵 ⪰ 0`, one sign). -/
theorem pure_part_potential_eig {E Hs : Type*} [NormedAddCommGroup E] [NormedAddCommGroup Hs]
    (T G Z : Matrix n n ℝ) {k κ₀ r : ℝ} (hk : 0 < k) (hκ₀ : 0 < κ₀) (hr : 0 ≤ r)
    (𝒮 : Finset (Finset n))
    (hgate : ∀ S ∈ 𝒮, ((k ^ 2 • (1 : Matrix n n ℝ) - (k * κ₀) • T - κ₀ ^ 2 • G).submatrix
      (fun i : S => (i : n)) (fun i : S => (i : n))).PosSemidef)
    (lam : FiniteLaw Ωt) (D : Ωt → n → ℝ) (Sel : Ωt → Finset n) (hSel : ∀ t, Sel t ∈ 𝒮)
    (hdκ : ∀ t i, D t i ^ 2 ≤ κ₀) (hdS : ∀ t i, i ∉ Sel t → D t i = 0)
    (hGpos : ∀ y : n → ℝ, 0 ≤ y ⬝ᵥ (G *ᵥ y))
    (qP : E → ℝ) (qS : (Ωt → n → ℝ) → Hs → ℝ) (uc : E → Ωt → n → ℝ) (vc : E → Hs)
    (hcomp : ∀ x, qP x = qS (uc x) (vc x) ∧
      lam.expect (fun t => uc x t ⬝ᵥ uc x t) + ‖vc x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (Φ : (Ωt → ℝ) → (Ωt → ℝ)) (hΦ : PaleyLike lam Φ)
    (hN : (RowsA.cplx T - Complex.I • RowsA.cplx Z).PosSemidef)
    (Bq : (Ωt → n → ℝ) → Hs → ℝ)
    (hS : ∀ u v, qS u v = r * zqForm lam Φ Z (fun t i => D t i * u t i) +
      2 * Real.sqrt κ₀ * r * Bq (fun t i => D t i * u t i) v)
    (hcouple : ∀ y v, |Bq y v| ≤ Real.sqrt (lam.expect (fun t => y t ⬝ᵥ (G *ᵥ y t))) * ‖v‖)
    (x : E) : -(r * k) * ‖x‖ ^ 2 ≤ qP x :=
  Potential.pure_part_potential T G hk hκ₀ hr 𝒮 hgate lam D Sel hSel hdκ hdS hGpos qP qS uc vc
    hcomp (zqForm lam Φ Z) Bq hS hcouple (heig_holds lam hΦ T Z hN) x

end Eig

end Sarkozy.JointRows
