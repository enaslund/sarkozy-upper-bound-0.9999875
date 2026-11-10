module

public import Sarkozy.F7Repair.Tail
public import Sarkozy.TailPrices.Polynomials

@[expose] public section

/-!
# The (F7) coefficient against its value at the evaluation point (`cert:tail-caps`; K2's field 11)

`paper/sections/26_upper_comparison.tex`, (F7): the repaired record has the symmetric coefficient
`C^s = (ρ_old + ρ')/r` with `ρ' = (ρ_new(1 + 2F) + U²)/(1 − U)`, `F = U(1 + K_∞/(1 − ρ_new))`;
`lem:record:domain`(iii) and `cert:tail-caps`: the caps are these coefficients evaluated at `2⁵⁴`,
and bound the coefficient at every prime `p ≥ 2⁵⁴`. The paper's argument: every input is a
normalized quantity times its power of `r` (`U`, `ρ_new`, `ρ_old` are `O(r)`, `K_∞` is `O(1)`),
the normalized quantities at `p` are at most their values at `p₀`, and the formula is monotone.

This file proves the monotonicity of the composite formula and its scaling:

* `f7C U ρn K ρo`: the (F7) coefficient times `r`, `ρ_old + ρ'`; `F7Record.C_eq`;
* **`f7C_le_scaled`**: if `U ≤ Û r`, `ρ_new ≤ ρ̂ r`, `K_∞ ≤ K̂`, `ρ_old ≤ ρ̂_old r` with
  `r ≤ r₀` and the gates `Û r₀ < 1`, `ρ̂ r₀ < 1`, then
  `f7C(U, ρ_new, K_∞, ρ_old) ≤ r · f7C(Û r₀, ρ̂ r₀, K̂, ρ̂_old r₀)/r₀`: the coefficient at `r` is
  at most the coefficient evaluated at `r₀` (the normalized (F7) coefficient `C_ϱ` of the
  evaluation point `p₀ = r₀⁻²`);
* `F7Norm`, `F7Record.Scaled`, **`F7Record.C_le_of_scaled`**: the same for an `F7Record`;
* **`TailF7s.hcap_of_scaled`**: K2's field 11 for any cap table `K`, from per-prime normalized
  majorants (*hypotheses*: the prime-level conclusions of `lem:record:domain`(iii) for the inputs
  of (F7)) and the numerical comparison of the normalized coefficients at an evaluation radius
  `r₀ ≥ 2⁻²⁵⁶` with `K` (*hypothesis*: a finite table, `cert:tail-caps`). The paper evaluates at
  `r₀ = 2⁻²⁷` (`p₀ = 2⁵⁴`); any `r₀ ≥ 2⁻²⁵⁶` is allowed, since every tail prime has
  `r ≤ 2⁻²⁵⁶`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.UpperComparison Sarkozy.TailPrices
  Sarkozy.RecordExpansion

/-- **The (F7) coefficient times `r`**: `ρ_old + (ρ_new(1 + 2F) + U²)/(1 − U)` with
`F = U(1 + K_∞/(1 − ρ_new))`. -/
noncomputable def f7C (U ρn K ρo : ℝ) : ℝ :=
  ρo + (ρn * (1 + 2 * (U * (1 + K / (1 - ρn)))) + U ^ 2) / (1 - U)

theorem F7Record.C_eq {O₀ O₁ Z : Type*} [Fintype O₀] [DecidableEq O₀] [Fintype O₁]
    [DecidableEq O₁] [Fintype Z] [DecidableEq Z] {lamO : FiniteLaw (O₀ × O₁ × Fin 2 → Z)}
    {lamH : FiniteLaw (O₀ × O₁ → Z)} (R : F7Record lamO lamH) :
    R.C = f7C R.D.U R.D.ρ R.D.K R.ρold := rfl

/-- **The (F7) coefficient is at most its value at the evaluation point** (`lem:record:domain`(iii),
the composite formula): with normalized majorants `Û, ρ̂, K̂, ρ̂_old ≥ 0` of the inputs at `r ≤ r₀`,
`f7C(U, ρ_new, K_∞, ρ_old) ≤ r · f7C(Û r₀, ρ̂ r₀, K̂, ρ̂_old r₀)/r₀`. -/
theorem f7C_le_scaled {U ρn K ρo r r₀ Uh ρh Kh ρoh : ℝ} (hr : 0 ≤ r) (hrr : r ≤ r₀)
    (hr₀ : 0 < r₀) (hU0 : 0 ≤ U) (hUh : 0 ≤ Uh) (hU : U ≤ Uh * r) (hρh : 0 ≤ ρh)
    (hρ : ρn ≤ ρh * r) (hK : K ≤ Kh) (hK0 : 0 ≤ K) (hρo : ρo ≤ ρoh * r) (hgU : Uh * r₀ < 1)
    (hgρ : ρh * r₀ < 1) :
    f7C U ρn K ρo ≤ r * (f7C (Uh * r₀) (ρh * r₀) Kh (ρoh * r₀) / r₀) := by
  have hKh : 0 ≤ Kh := hK0.trans hK
  have hUr : U ≤ Uh * r₀ := hU.trans (mul_le_mul_of_nonneg_left hrr hUh)
  have hρr : ρn ≤ ρh * r₀ := hρ.trans (mul_le_mul_of_nonneg_left hrr hρh)
  have hd0 : 0 < 1 - ρh * r₀ := by linarith
  have hdU : 0 < 1 - Uh * r₀ := by linarith
  set F₀ := Uh * r₀ * (1 + Kh / (1 - ρh * r₀)) with hF₀
  have hKd : K / (1 - ρn) ≤ Kh / (1 - ρh * r₀) :=
    div_le_div₀ hKh hK hd0 (by linarith)
  have hKd0 : 0 ≤ K / (1 - ρn) := div_nonneg hK0 (by linarith)
  have hF : U * (1 + K / (1 - ρn)) ≤ F₀ :=
    mul_le_mul hUr (by linarith) (by linarith) (mul_nonneg hUh hr₀.le)
  have hF0 : 0 ≤ U * (1 + K / (1 - ρn)) := mul_nonneg hU0 (by linarith)
  have hN1 : ρn * (1 + 2 * (U * (1 + K / (1 - ρn)))) ≤ ρh * r * (1 + 2 * F₀) :=
    mul_le_mul hρ (by linarith) (by linarith) (mul_nonneg hρh hr)
  have hN2 : U ^ 2 ≤ Uh ^ 2 * r₀ * r := by
    have h1 : U ^ 2 ≤ (Uh * r) ^ 2 := pow_le_pow_left₀ hU0 hU 2
    have h2 : (Uh * r) ^ 2 ≤ Uh ^ 2 * r₀ * r := by
      have : Uh ^ 2 * r * r ≤ Uh ^ 2 * r₀ * r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrr (sq_nonneg _)) hr
      nlinarith
    exact h1.trans h2
  set N₀ := ρh * (1 + 2 * F₀) + Uh ^ 2 * r₀ with hN₀
  have hN₀0 : 0 ≤ N₀ := by
    have : 0 ≤ F₀ := hF0.trans hF
    have := mul_nonneg hρh (by linarith : (0 : ℝ) ≤ 1 + 2 * F₀)
    nlinarith [sq_nonneg Uh]
  have hN : ρn * (1 + 2 * (U * (1 + K / (1 - ρn)))) + U ^ 2 ≤ r * N₀ := by
    rw [hN₀]
    nlinarith [hN1, hN2]
  have hQ : (ρn * (1 + 2 * (U * (1 + K / (1 - ρn)))) + U ^ 2) / (1 - U) ≤
      r * N₀ / (1 - Uh * r₀) :=
    div_le_div₀ (mul_nonneg hr hN₀0) hN hdU (by linarith)
  have hR : r * (f7C (Uh * r₀) (ρh * r₀) Kh (ρoh * r₀) / r₀) = ρoh * r + r * N₀ / (1 - Uh * r₀) := by
    unfold f7C
    rw [hN₀, hF₀]
    field_simp
  rw [hR]
  unfold f7C
  linarith

/-- **Normalized (F7) inputs** of one record at an evaluation point: `Û`, `ρ̂_new`, `K̂_∞`,
`ρ̂_old` (the values of `U/r`, `ρ_new/r`, `K_∞`, `ρ_old/r` at `p₀`). -/
structure F7Norm where
  U : ℝ
  ρ : ℝ
  K : ℝ
  ρo : ℝ

/-- The normalized (F7) coefficient `C_ϱ` at `r₀`: `f7C(Û r₀, ρ̂ r₀, K̂, ρ̂_old r₀)/r₀`. -/
noncomputable def F7Norm.coeff (n : F7Norm) (r₀ : ℝ) : ℝ := f7C (n.U * r₀) (n.ρ * r₀) n.K (n.ρo * r₀) / r₀

variable {O₀ O₁ Z : Type*} [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁]
  [Fintype Z] [DecidableEq Z] {lamO : FiniteLaw (O₀ × O₁ × Fin 2 → Z)}
  {lamH : FiniteLaw (O₀ × O₁ → Z)}

/-- **The inputs of an `F7Record` at `r` are bounded by normalized majorants**
(`lem:record:domain`(iii), the prime-level conclusions for the inputs of (F7)). -/
def F7Record.Scaled (R : F7Record lamO lamH) (n : F7Norm) (r : ℝ) : Prop :=
  0 ≤ n.U ∧ 0 ≤ n.ρ ∧ R.D.U ≤ n.U * r ∧ R.D.ρ ≤ n.ρ * r ∧ R.D.K ≤ n.K ∧ R.ρold ≤ n.ρo * r

/-- **The coefficient of a scaled record is at most `C_ϱ r`** (`lem:record:domain`(iii)). -/
theorem F7Record.C_le_of_scaled (R : F7Record lamO lamH) (n : F7Norm) {r r₀ : ℝ} (hr : 0 ≤ r)
    (hrr : r ≤ r₀) (hr₀ : 0 < r₀) (hgU : n.U * r₀ < 1) (hgρ : n.ρ * r₀ < 1)
    (hs : R.Scaled n r) : R.C ≤ n.coeff r₀ * r := by
  obtain ⟨hUh, hρh, hU, hρ, hK, hρo⟩ := hs
  rw [R.C_eq, mul_comm]
  exact f7C_le_scaled hr hrr hr₀ R.D.U_nonneg hUh hU hρh hρ hK R.D.K_nonneg hρo hgU hgρ

/-- **K2's field 11 from normalized majorants** (`cert:tail-caps`, `lem:record:domain`(iii)): for a
cap table `K` and an evaluation radius `r₀ ≥ 2⁻²⁵⁶` (every tail prime has `r = q^{-1/2} ≤ 2⁻²⁵⁶`),
if at every tail prime the (F7) inputs of every changed record are bounded by its normalized
majorants `n ρ` (*hypothesis*, analytic: the prime-level conclusions of `lem:record:domain`(iii)),
and the normalized coefficients at `r₀` are at most the caps (*hypothesis*, a finite table), then
every repair constant is at most `K_ρ q^{-1/2}`. -/
theorem TailF7s.hcap_of_scaled (F : ∀ (q : ℕ) [Fact q.Prime] (hne : TailNonempty q), TailF7s hne)
    (K : UpIdx → ℝ) (n : UpIdx → F7Norm) {r₀ : ℝ} (hr₀ : (1 / 2 ^ 256 : ℝ) ≤ r₀)
    (hgU : ∀ ρ, (n ρ).U * r₀ < 1) (hgρ : ∀ ρ, (n ρ).ρ * r₀ < 1)
    (hnum : ∀ ρ, upperFate ρ = .changed → (n ρ).coeff r₀ ≤ K ρ)
    (hs : ∀ (q : ℕ) [Fact q.Prime] (hne : TailNonempty q), P4 ≤ q → ∀ t φ
      (h : upperFate (true, ⟨t, φ⟩) = .changed),
      (F q hne t φ h).data.Scaled (n (true, ⟨t, φ⟩)) (tailR q))
    (q : ℕ) [Fact q.Prime] (hne : TailNonempty q) (h4 : P4 ≤ q) (t : PType × PType)
    (φ : t.1.Pat × t.2.Pat) (h : upperFate (true, ⟨t, φ⟩) = .changed) (e : ChangeType) :
    ((F q hne).toRepairs t φ h).C e ≤ K (true, ⟨t, φ⟩) * tailR q := by
  rw [TailF7s.toRepairs_C]
  have hr0 : (0 : ℝ) < r₀ := lt_of_lt_of_le (by norm_num) hr₀
  have hc := (F q hne t φ h).data.C_le_of_scaled (n (true, ⟨t, φ⟩)) (tailR_nonneg q)
    ((tailR_le h4).trans hr₀) hr0 (hgU _) (hgρ _) (hs q hne h4 t φ h)
  exact hc.trans (mul_le_mul_of_nonneg_right (hnum _ h) (tailR_nonneg q))

end Sarkozy.F7Repair
