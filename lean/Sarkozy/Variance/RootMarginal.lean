module

public import Sarkozy.Variance.ChiSquare
public import Sarkozy.Labellings.Extension

@[expose] public section

/-!
# The root completion count (`lem:record:root-marginal`)

`paper/sections/22_variance.tex`, `lem:record:root-marginal`. At one prime `p ≡ 3 (mod 4)`, with
`q = 1/p` and `r = p^{-1/2}`, the lemma bounds the density and the chi-square divergence of the half
law `ν_{L,p}` of the root against the fold law `λ_{F,p}` at a fold chamber, and then multiplies the
bounds over the primes of a block. Its constants are real functions of `(q, r)`, defined here:
`υ₊ = 11r + 6q`, `υ₋ = 11r + 70q`, `υ_× = 11r + 102q` (`upsPlus`, `upsMinus`, `upsTimes`),
`𝔞_p` (`aP`), `R_p` (`Rp`), `Z₄`, `Δ₂`, `Δ_max`, `D_full`, `L_low` (`Z4`, `Delta2`, `DeltaMax`,
`Dfull`, `Llow`); the *lower factors* are `1 - υ_× - 16q` and `1 - 24𝔞_p` (`LowerFactors`).

**What is proved, and what enters as a hypothesis.** The analytic skeleton of the proof is proved
in full. The combinatorial and character-sum inputs are explicit hypotheses of the theorems:

* the root-count bounds `eq:record:root-count` (from `lem:record:signed-nbhd`; hypothesis
  `hcount` of `rootMarginal_i`);
* in (ii): the number `n = |signed neighbourhood| - n₁` of admissible labels for `y_{4,ℓ}`
  (hypothesis `hn`), the Weil bound `|𝒲| ≤ 4·2√p + 3√p` (`thm:weil`, hypothesis `hWeil`), the
  moment bound `E_{λ_F} (𝒲/p)² ≤ (5q + 34qr + 11q³)/Z₄` (`lem:record:weighted-moment`(b) with the
  transfer to the admissible quadruples, hypothesis `hmom`), and the even-component sandwich
  `(1 - 24𝔞_p) Ξ ≤ ς ≤ Ξ` (hypothesis `hs`). Of these, `hn` and `hWeil` are **discharged** in
  `rootMarginal_ii_second_of_labels`: the soft count identity `𝔖 = q + 2 + 𝒲`
  (`rootMarginal_softCount_eq`, from `eq:two-root`), `𝔖 = 16 · |signed neighbourhood|` for
  admissible labels (`rootMarginal_softCount_card`, `χ(-1) = -1`), and `|𝒲| ≤ 11√q` from H1
  (`rootMarginal_softW_weil`, `Labellings.WeilBound`);
* in (iii): `|𝔅| ≤ ⌊L/log X⌋ ≤ n` (`lem:record:local-domain`) enters as `card ≤ n`. The
  monotonicity in `(q, r)` (`lem:majorant`) is **proved** for these functions
  (`rootMarginal_aP_mono`, `_Rp_mono`, `_Delta2_mono`, `_chiBar_mono`, `_lowerFactors_mono`).

Main results:
* `rootMarginal_Llow_pos`, `rootMarginal_lowerProd_pos`, `rootMarginal_aP_nonneg`,
  `rootMarginal_Rp_ge_one`: the side facts (`L_low > 0` as `Δ_max < υ_×`).
* `rootMarginal_i` (**(i)**): `R_p⁻¹ ≤ dν/dλ ≤ R_p`, and `sup ≤ R_p · inf`.
* `rootMarginal_ii_first`, `rootMarginal_ii_second`, `rootMarginal_ii` (**(ii)**):
  `χ_p ≤ (R_p - 1)²/R_p`, `χ_p ≤ D_full²/L_low²`, and their minimum `χ̄(q, r)` (`chiBar`). The
  second bound is the full chain of the proof: `|β| ≤ Δ_max`, `‖β‖₂ ≤ Δ₂`,
  `Ξ - 1 = β(2+β) - 16q(1+β)`, `‖Ξ - 1‖₂ ≤ (2+Δ_max+16q)Δ₂ + 16q`, the bounds of `Ξ`,
  `‖ς - 1‖₂ ≤ D_full`, `E ς ≥ L_low`.
* `rootMarginal_iii` and `rootMarginal_iii_endpoint` (**(iii)**): at a block of at most `n`
  primes, hypothesis (A) (`hyp:variance:A`) with `M_𝔅 = ∏ R_p ≤ R̄(X)ⁿ`, and
  `χ²(⊗ν ‖ ⊗λ) = ∏(1 + χ_p) - 1 ≤ (1 + χ̄(X))ⁿ - 1`, with `R̄(X)`, `χ̄(X)` the values at
  `(1/X, r_X)` for any `r_X ≥ X^{-1/2}` with positive lower factors.
* `rootMarginal_iv_density_bounds` (**(iv)**, the step "a mean-one density with
  `sup ≤ R · inf` lies in `[R⁻¹, R]`"); the product clause of (iv) is `rootMarginal_iii`
  applied to the positive roots' prime laws. The prime inputs `R_𝔲(X)`, `d_𝔲(X)²` of (iv)
  (`prop:root-chamber`, `cert:positive-root-caps`) are not formalized here.
* The steps of the odd and even components, abstractly: `rootMarginal_prob_le_aP` (a free odd
  label takes a given value with probability `≤ 𝔞_p`, from the two counts) and
  `rootMarginal_union_bound` (the completions avoiding `6` forbidden values in `4` free labels
  form a fraction `≥ 1 - 24𝔞_p`); the counts themselves and the identification of `𝔑` are not
  formalized, so `hcount` and `hs` remain hypotheses.
* Non-vacuity: `rootMarginal_lowerFactors_first_piece` (the lower factors are positive at the
  first piece start `X₁ = 19951586`, `r = 1/4466`) and `rootMarginal_ii_second_satisfiable`.
-/

namespace Sarkozy.Variance

namespace RootMarginal

open Finset
open scoped BigOperators

/-! ### The constants of `lem:record:root-marginal` -/

/-- `υ₊ = 11 r + 6 q` (`lem:record:signed-nbhd`). -/
noncomputable def upsPlus (q r : ℝ) : ℝ := 11 * r + 6 * q

/-- `υ₋ = 11 r + 70 q` (`lem:record:signed-nbhd`). -/
noncomputable def upsMinus (q r : ℝ) : ℝ := 11 * r + 70 * q

/-- `υ_× = υ₋ + 32 q = 11 r + 102 q`. -/
noncomputable def upsTimes (q r : ℝ) : ℝ := 11 * r + 102 * q

/-- `𝔞_p = 4q/(1-3q) · (1+υ₊)² / ((1-υ₋)(1-υ₋-16q))`. -/
noncomputable def aP (q r : ℝ) : ℝ :=
  4 * q / (1 - 3 * q) *
    ((1 + upsPlus q r) ^ 2 / ((1 - upsMinus q r) * (1 - upsMinus q r - 16 * q)))

/-- The lower product `(1-υ_×)(1-υ_×-16q)(1-24𝔞_p)` of `eq:record:root-count`. -/
noncomputable def lowerProd (q r : ℝ) : ℝ :=
  (1 - upsTimes q r) * (1 - upsTimes q r - 16 * q) * (1 - 24 * aP q r)

/-- `R_p = (1+υ₊)² / ((1-υ_×)(1-υ_×-16q)(1-24𝔞_p))`. -/
noncomputable def Rp (q r : ℝ) : ℝ := (1 + upsPlus q r) ^ 2 / lowerProd q r

/-- `Z₄ = (1-q)(1-3q)(1-7q)`. -/
noncomputable def Z4 (q : ℝ) : ℝ := (1 - q) * (1 - 3 * q) * (1 - 7 * q)

/-- `Δ₂ = ((5q + 34qr + 11q³)/Z₄)^{1/2} + 30q`. -/
noncomputable def Delta2 (q r : ℝ) : ℝ :=
  Real.sqrt ((5 * q + 34 * q * r + 11 * q ^ 3) / Z4 q) + 30 * q

/-- `Δ_max = 11 r + 30 q`. -/
noncomputable def DeltaMax (q r : ℝ) : ℝ := 11 * r + 30 * q

/-- `D_full = (2 + Δ_max + 16q) Δ₂ + 16q + 24 𝔞_p (1 + Δ_max)²`. -/
noncomputable def Dfull (q r : ℝ) : ℝ :=
  (2 + DeltaMax q r + 16 * q) * Delta2 q r + 16 * q + 24 * aP q r * (1 + DeltaMax q r) ^ 2

/-- `L_low = (1 - Δ_max)(1 - Δ_max - 16q)(1 - 24𝔞_p)`. -/
noncomputable def Llow (q r : ℝ) : ℝ :=
  (1 - DeltaMax q r) * (1 - DeltaMax q r - 16 * q) * (1 - 24 * aP q r)

/-- The *lower factors* `1 - υ_× - 16q` and `1 - 24𝔞_p` are positive (the assumption of
`lem:record:root-marginal`). -/
def LowerFactors (q r : ℝ) : Prop := 0 < 1 - upsTimes q r - 16 * q ∧ 0 < 1 - 24 * aP q r

/-- `L_low > 0` under the lower factors, since `Δ_max < υ_×` (`lem:record:root-marginal`). -/
theorem rootMarginal_Llow_pos {q r : ℝ} (hq : 0 < q) (h : LowerFactors q r) : 0 < Llow q r := by
  obtain ⟨h1, h2⟩ := h
  unfold Llow
  unfold upsTimes at h1
  unfold DeltaMax
  have ha : 0 < 1 - (11 * r + 30 * q) - 16 * q := by linarith
  have hb : 0 < 1 - (11 * r + 30 * q) := by linarith
  positivity

theorem rootMarginal_lowerProd_pos {q r : ℝ} (hq : 0 < q) (h : LowerFactors q r) :
    0 < lowerProd q r := by
  obtain ⟨h1, h2⟩ := h
  unfold lowerProd
  have hb : 0 < 1 - upsTimes q r := by linarith
  positivity

/-- `𝔞_p ≥ 0` for `q > 0`, `r ≥ 0` and a positive first lower factor. -/
theorem rootMarginal_aP_nonneg {q r : ℝ} (hq : 0 < q) (hr : 0 ≤ r)
    (h1 : 0 < 1 - upsTimes q r - 16 * q) : 0 ≤ aP q r := by
  unfold aP
  unfold upsTimes at h1
  unfold upsMinus
  have e1 : 0 < 1 - 3 * q := by linarith
  have e2 : 0 < 1 - (11 * r + 70 * q) := by linarith
  have e3 : 0 < 1 - (11 * r + 70 * q) - 16 * q := by linarith
  have : 0 < (1 - (11 * r + 70 * q)) * (1 - (11 * r + 70 * q) - 16 * q) := mul_pos e2 e3
  positivity

/-- `R_p ≥ 1` (so that `R̄ ≥ 1` in (iii)). -/
theorem rootMarginal_Rp_ge_one {q r : ℝ} (hq : 0 < q) (hr : 0 ≤ r) (h : LowerFactors q r) :
    1 ≤ Rp q r := by
  have hP := rootMarginal_lowerProd_pos hq h
  have ha := rootMarginal_aP_nonneg hq hr h.1
  obtain ⟨h1, h2⟩ := h
  unfold Rp
  rw [le_div_iff₀ hP, one_mul]
  unfold lowerProd
  unfold upsTimes at h1 ⊢
  unfold upsPlus
  have f1 : 1 - (11 * r + 102 * q) ≤ 1 := by linarith
  have f2 : 1 - (11 * r + 102 * q) - 16 * q ≤ 1 := by linarith
  have f3 : 1 - 24 * aP q r ≤ 1 := by linarith
  have g1 : 0 ≤ 1 - (11 * r + 102 * q) := by linarith
  have g2 : 0 ≤ 1 - (11 * r + 102 * q) - 16 * q := h1.le
  have g3 : 0 ≤ 1 - 24 * aP q r := h2.le
  have hprod : (1 - (11 * r + 102 * q)) * (1 - (11 * r + 102 * q) - 16 * q) *
      (1 - 24 * aP q r) ≤ 1 := by
    have h12 : (1 - (11 * r + 102 * q)) * (1 - (11 * r + 102 * q) - 16 * q) ≤ 1 :=
      calc _ ≤ 1 * 1 := mul_le_mul f1 f2 g2 zero_le_one
        _ = 1 := one_mul 1
    calc _ ≤ 1 * 1 := mul_le_mul h12 f3 g3 zero_le_one
      _ = 1 := one_mul 1
  have hsq : 1 ≤ (1 + (11 * r + 6 * q)) ^ 2 := by nlinarith
  linarith

/-! ### (i): the density of the half law -/

/-- The half law `ν = 𝔑 λ / E_λ 𝔑` with density proportional to the completion count `𝔑`
(the root is uniform on its configurations, so its half marginal is proportional to `𝔑`). -/
noncomputable def halfLaw {S : Type*} [Fintype S] (lam N : S → ℝ) (y : S) : ℝ :=
  lam y * N y / ∑ z, lam z * N z

theorem rootMarginal_halfLaw_density {S : Type*} [Fintype S] {lam : S → ℝ}
    (hlam : ∀ y, 0 < lam y) (N : S → ℝ) (y : S) :
    halfLaw lam N y / lam y = N y / ∑ z, lam z * N z := by
  unfold halfLaw
  have := (hlam y).ne'
  field_simp

theorem rootMarginal_halfLaw_sum {S : Type*} [Fintype S] {lam N : S → ℝ}
    (hm : ∑ z, lam z * N z ≠ 0) : ∑ y, halfLaw lam N y = 1 := by
  unfold halfLaw
  rw [← sum_div, div_self hm]

/-- Scaling the count does not change the half law. -/
theorem rootMarginal_halfLaw_smul {S : Type*} [Fintype S] (lam s : S → ℝ) {K : ℝ} (hK : K ≠ 0) :
    halfLaw lam (fun y => K * s y) = fun y => lam y * s y / ∑ z, lam z * s z := by
  funext y
  unfold halfLaw
  have e : ∑ z, lam z * (K * s z) = K * ∑ z, lam z * s z := by
    rw [mul_sum]
    exact sum_congr rfl fun z _ => by ring
  rw [e]
  by_cases h0 : ∑ z, lam z * s z = 0
  · rw [h0, mul_zero, div_zero, div_zero]
  · field_simp

/-- **`lem:record:root-marginal`(i).** If the completion counts satisfy `eq:record:root-count`,
`(1-υ_×)(1-υ_×-16q)(1-24𝔞_p) ≤ 𝔑(y)/K ≤ (1+υ₊)²` with `K = 𝒵 (p/16)² > 0` (a **hypothesis**,
from `lem:record:signed-nbhd`), then the density of the half law against `λ` lies in
`[R_p⁻¹, R_p]`, and its supremum is at most `R_p` times its infimum. -/
theorem rootMarginal_i {S : Type*} [Fintype S] {lam N : S → ℝ} (hlam : ∀ y, 0 < lam y)
    (hlam1 : ∑ y, lam y = 1) {q r K : ℝ} (hK : 0 < K) (hq : 0 < q) (hlow : LowerFactors q r)
    (hcount : ∀ y, lowerProd q r ≤ N y / K ∧ N y / K ≤ (1 + upsPlus q r) ^ 2) :
    (∀ y, (Rp q r)⁻¹ ≤ halfLaw lam N y / lam y ∧ halfLaw lam N y / lam y ≤ Rp q r) ∧
      ∀ x y, halfLaw lam N x / lam x ≤ Rp q r * (halfLaw lam N y / lam y) := by
  have hP := rootMarginal_lowerProd_pos hq hlow
  have hc : 0 < K * lowerProd q r := mul_pos hK hP
  have hlo : ∀ y, K * lowerProd q r ≤ N y := fun y => by
    have := (hcount y).1
    rw [le_div_iff₀ hK] at this
    linarith
  have hhi : ∀ y, N y ≤ Rp q r * (K * lowerProd q r) := fun y => by
    have := (hcount y).2
    rw [div_le_iff₀ hK] at this
    have e : Rp q r * (K * lowerProd q r) = (1 + upsPlus q r) ^ 2 * K := by
      unfold Rp
      field_simp
    rw [e]
    exact this
  obtain ⟨h1, h2⟩ := chiSq_density_range_of_counts (fun y => (hlam y).le) hlam1 hc hlo hhi
  simp_rw [rootMarginal_halfLaw_density hlam N]
  exact ⟨h1, h2⟩

/-! ### (ii): the chi-square bounds -/

/-- **`lem:record:root-marginal`(ii), first bound**: `χ_p ≤ (R_p - 1)²/R_p`, under the
hypotheses of (i). -/
theorem rootMarginal_ii_first {S : Type*} [Fintype S] {lam N : S → ℝ} (hlam : ∀ y, 0 < lam y)
    (hlam1 : ∑ y, lam y = 1) {q r K : ℝ} (hK : 0 < K) (hq : 0 < q) (hlow : LowerFactors q r)
    (hcount : ∀ y, lowerProd q r ≤ N y / K ∧ N y / K ≤ (1 + upsPlus q r) ^ 2) :
    chiSq (halfLaw lam N) lam ≤ (Rp q r - 1) ^ 2 / Rp q r := by
  obtain ⟨hrange, -⟩ := rootMarginal_i hlam hlam1 hK hq hlow hcount
  have hP := rootMarginal_lowerProd_pos hq hlow
  have hNpos : ∀ y, 0 < N y := fun y => by
    have := (hcount y).1
    rw [le_div_iff₀ hK] at this
    nlinarith
  obtain ⟨y₀⟩ : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hlam1
  have hm : ∑ z, lam z * N z ≠ 0 :=
    (sum_pos (fun z _ => mul_pos (hlam z) (hNpos z)) ⟨y₀, mem_univ y₀⟩).ne'
  have hR : 0 < Rp q r := by
    unfold Rp
    have : 0 < (1 + upsPlus q r) ^ 2 := by
      have h2 := (hcount y₀).2
      have h1 := (hcount y₀).1
      linarith
    positivity
  exact chiSq_le_of_density_range hlam (rootMarginal_halfLaw_sum hm) hlam1 hR
    (fun y => (hrange y).1) (fun y => (hrange y).2)

/-- The L² triangle step used three times in (ii): if `|f| ≤ a |g| + b` pointwise with
`a, b ≥ 0` and `‖g‖₂ ≤ G`, then `‖f‖₂² ≤ (a G + b)²`. -/
theorem rootMarginal_sq_le_of_pointwise {S : Type*} [Fintype S] (μ : FiniteLaw S)
    {f g : S → ℝ} {a b G : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hfg : ∀ y, |f y| ≤ a * |g y| + b)
    (hG : Real.sqrt (μ.expect (fun y => g y ^ 2)) ≤ G) :
    μ.expect (fun y => f y ^ 2) ≤ (a * G + b) ^ 2 := by
  set A := Real.sqrt (μ.expect (fun y => g y ^ 2)) with hA
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = μ.expect (fun y => g y ^ 2) := Real.sq_sqrt (μ.second_moment_nonneg g)
  have habs : μ.expect (fun y => |g y|) ≤ A := by
    have h := μ.mean_sq_le_second_moment (fun y => |g y|)
    simp_rw [sq_abs] at h
    rw [hA]
    exact Real.le_sqrt_of_sq_le h
  have h1 : μ.expect (fun y => f y ^ 2) ≤ μ.expect (fun y => (a * |g y| + b) ^ 2) := by
    apply μ.expect_mono
    intro y
    have h0 : 0 ≤ |f y| := abs_nonneg _
    have := hfg y
    rw [← sq_abs (f y)]
    exact pow_le_pow_left₀ h0 this 2
  have h2 : μ.expect (fun y => (a * |g y| + b) ^ 2) =
      a ^ 2 * μ.expect (fun y => g y ^ 2) + 2 * a * b * μ.expect (fun y => |g y|) + b ^ 2 := by
    have e : ∀ y, (a * |g y| + b) ^ 2 = a ^ 2 * g y ^ 2 + 2 * a * b * |g y| + b ^ 2 := fun y => by
      rw [add_sq, mul_pow, sq_abs]
      ring
    rw [μ.expect_congr e, μ.expect_add, μ.expect_add, μ.expect_const_mul, μ.expect_const_mul,
      μ.expect_const]
  have hGA : A ≤ G := hG
  have h3 : a ^ 2 * μ.expect (fun y => g y ^ 2) + 2 * a * b * μ.expect (fun y => |g y|) + b ^ 2 ≤
      (a * A + b) ^ 2 := by
    rw [← hAsq]
    have : 2 * a * b * μ.expect (fun y => |g y|) ≤ 2 * a * b * A :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    nlinarith
  have h4 : (a * A + b) ^ 2 ≤ (a * G + b) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  linarith

/-- **`lem:record:root-marginal`(ii), second bound**, `χ_p ≤ D_full²/L_low²`. Data at one prime,
on the half configurations `S` with the law `μ = λ_F` (positive weights):
* `𝒲` with `|𝒲| ≤ 11√p` (**hypothesis** `hWeil`, `thm:weil`: four sums with `|A| = 3`, each at
  most `2√p`, and one with `|A| = 4`, at most `3√p`);
* `n₁ ∈ {0,1,2}` and `n = (p + 2 + 𝒲)/16 - n₁`, the number of admissible labels for `y_{4,ℓ}`
  (**hypothesis** `hn`: the soft count is `p + 2 + 𝒲`, by `eq:two-root`, and is `16` times the
  signed neighbourhood; removing `y_{1,0}, y_{1,1}` deletes `n₁` points);
* `E_λ (𝒲/p)² ≤ (5q + 34qr + 11q³)/Z₄` (**hypothesis** `hmom`, `lem:record:weighted-moment`(b)
  on the admissible quadruples);
* `ς = 𝔑/(𝒵 n̄²)` with `(1 - 24𝔞_p) Ξ ≤ ς ≤ Ξ`, `Ξ = n(n-1)/n̄²`, `n̄ = p/16` (**hypothesis**
  `hs`, the even-component step).

Then the law `ν = ς λ / E_λ ς` (the half law of the root) satisfies `χ²(ν ‖ λ) ≤ D_full²/L_low²`.
The proof is the paper's: `β = 𝒲/p + (2 - 16n₁)q` has `|β| ≤ Δ_max`, `‖β‖₂ ≤ Δ₂`;
`Ξ - 1 = β(2 + β) - 16q(1 + β)`; `‖ς - 1‖₂ ≤ D_full`, `E ς ≥ L_low`; `χ² = Var ς/(E ς)²`. -/
theorem rootMarginal_ii_second {S : Type*} [Fintype S] (μ : FiniteLaw S)
    (hpos : ∀ y, 0 < μ.weight y) {p q r : ℝ} (hp : 0 < p) (hqp : q = 1 / p)
    (hr : r * Real.sqrt p = 1) (hlow : LowerFactors q r) (W n₁ n s : S → ℝ)
    (hWeil : ∀ y, |W y| ≤ 11 * Real.sqrt p)
    (hn₁ : ∀ y, n₁ y = 0 ∨ n₁ y = 1 ∨ n₁ y = 2)
    (hn : ∀ y, n y = (p + 2 + W y) / 16 - n₁ y)
    (hmom : μ.expect (fun y => (W y / p) ^ 2) ≤ (5 * q + 34 * q * r + 11 * q ^ 3) / Z4 q)
    (hs : ∀ y, (1 - 24 * aP q r) * (n y * (n y - 1) / (p / 16) ^ 2) ≤ s y ∧
      s y ≤ n y * (n y - 1) / (p / 16) ^ 2) :
    chiSq (fun y => μ.weight y * s y / ∑ z, μ.weight z * s z) μ.weight ≤
      Dfull q r ^ 2 / Llow q r ^ 2 := by
  have hq : 0 < q := by rw [hqp]; positivity
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hr0 : 0 < r := by
    by_contra h
    push Not at h
    have : r * Real.sqrt p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hsp.le
    linarith
  have hrp : r * p = Real.sqrt p := by
    have : p = Real.sqrt p * Real.sqrt p := (Real.mul_self_sqrt hp.le).symm
    calc r * p = r * (Real.sqrt p * Real.sqrt p) := by rw [← this]
      _ = (r * Real.sqrt p) * Real.sqrt p := by ring
      _ = Real.sqrt p := by rw [hr, one_mul]
  have hqp' : q * p = 1 := by rw [hqp]; field_simp
  have ha := rootMarginal_aP_nonneg hq hr0.le hlow.1
  obtain ⟨hl1, hl2⟩ := hlow
  have hl1' : 0 < 1 - DeltaMax q r - 16 * q := by
    unfold upsTimes at hl1
    unfold DeltaMax
    linarith
  -- `β` and its pointwise bound
  set β : S → ℝ := fun y => W y / p + (2 - 16 * n₁ y) * q with hβdef
  have hWp : ∀ y, |W y / p| ≤ 11 * r := fun y => by
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    calc |W y| ≤ 11 * Real.sqrt p := hWeil y
      _ = 11 * r * p := by rw [mul_assoc, hrp]
  have hcorr : ∀ y, |(2 - 16 * n₁ y) * q| ≤ 30 * q := fun y => by
    rcases hn₁ y with h | h | h <;> rw [h] <;>
      rw [abs_le] <;> constructor <;> nlinarith
  have hβ : ∀ y, |β y| ≤ DeltaMax q r := fun y => by
    unfold DeltaMax
    calc |β y| ≤ |W y / p| + |(2 - 16 * n₁ y) * q| := abs_add_le _ _
      _ ≤ 11 * r + 30 * q := add_le_add (hWp y) (hcorr y)
  -- `n = n̄ (1 + β)` and `Ξ = (1 + β)(1 + β - 16 q)`
  have hΞ : ∀ y, n y * (n y - 1) / (p / 16) ^ 2 = (1 + β y) * (1 + β y - 16 * q) := fun y => by
    rw [hn y]
    simp only [hβdef]
    rw [hqp]
    field_simp
    ring
  -- `‖β‖₂ ≤ Δ₂`
  have hD2 : Real.sqrt (μ.expect (fun y => β y ^ 2)) ≤ Delta2 q r := by
    have hb := rootMarginal_sq_le_of_pointwise μ (f := β) (g := fun y => W y / p)
      (a := 1) (b := 30 * q) (G := Real.sqrt ((5 * q + 34 * q * r + 11 * q ^ 3) / Z4 q))
      zero_le_one (by positivity)
      (fun y => by
        rw [one_mul]
        exact (abs_add_le _ _).trans (add_le_add le_rfl (hcorr y)))
      (Real.sqrt_le_sqrt hmom)
    have hD : 0 ≤ Delta2 q r := by unfold Delta2; positivity
    unfold Delta2
    rw [one_mul] at hb
    calc Real.sqrt (μ.expect (fun y => β y ^ 2))
        ≤ Real.sqrt ((Real.sqrt ((5 * q + 34 * q * r + 11 * q ^ 3) / Z4 q) + 30 * q) ^ 2) :=
          Real.sqrt_le_sqrt hb
      _ = _ := Real.sqrt_sq (by positivity)
  -- the bounds of `Ξ`
  have hΞlo : ∀ y, (1 - DeltaMax q r) * (1 - DeltaMax q r - 16 * q) ≤
      (1 + β y) * (1 + β y - 16 * q) := fun y => by
    have hb := abs_le.mp (hβ y)
    apply mul_le_mul (by linarith) (by linarith) hl1'.le (by linarith)
  have hΞhi : ∀ y, (1 + β y) * (1 + β y - 16 * q) ≤ (1 + DeltaMax q r) ^ 2 := fun y => by
    have hb := abs_le.mp (hβ y)
    have h1 : 0 ≤ 1 + β y := by linarith
    calc (1 + β y) * (1 + β y - 16 * q) ≤ (1 + β y) * (1 + β y) :=
          mul_le_mul_of_nonneg_left (by linarith) h1
      _ ≤ (1 + DeltaMax q r) * (1 + DeltaMax q r) := mul_le_mul (by linarith) (by linarith) h1
          (by linarith)
      _ = (1 + DeltaMax q r) ^ 2 := (sq _).symm
  -- `|ς - 1| ≤ (2 + Δ_max + 16q)|β| + 16q + 24𝔞(1 + Δ_max)²`
  have hpt : ∀ y, |s y - 1| ≤ (2 + DeltaMax q r + 16 * q) * |β y| +
      (16 * q + 24 * aP q r * (1 + DeltaMax q r) ^ 2) := fun y => by
    have hb := abs_le.mp (hβ y)
    obtain ⟨hs1, hs2⟩ := hs y
    rw [hΞ y] at hs1 hs2
    have hXi1 : |(1 + β y) * (1 + β y - 16 * q) - 1| ≤
        (2 + DeltaMax q r + 16 * q) * |β y| + 16 * q := by
      have e : (1 + β y) * (1 + β y - 16 * q) - 1 = β y * (2 + β y - 16 * q) - 16 * q := by ring
      rw [e]
      calc |β y * (2 + β y - 16 * q) - 16 * q| ≤ |β y * (2 + β y - 16 * q)| + |16 * q| :=
            abs_sub _ _
        _ = |β y| * |2 + β y - 16 * q| + 16 * q := by
            rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 16 * q)]
        _ ≤ |β y| * (2 + DeltaMax q r + 16 * q) + 16 * q := by
            have : |2 + β y - 16 * q| ≤ 2 + DeltaMax q r + 16 * q := by
              rw [abs_le]
              constructor <;> linarith
            nlinarith [abs_nonneg (β y)]
        _ = (2 + DeltaMax q r + 16 * q) * |β y| + 16 * q := by ring
    have hgap : |s y - (1 + β y) * (1 + β y - 16 * q)| ≤ 24 * aP q r * (1 + DeltaMax q r) ^ 2 := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      have hΞy := hΞhi y
      nlinarith
    calc |s y - 1| ≤ |s y - (1 + β y) * (1 + β y - 16 * q)| +
          |(1 + β y) * (1 + β y - 16 * q) - 1| := abs_sub_le _ _ _
      _ ≤ 24 * aP q r * (1 + DeltaMax q r) ^ 2 +
          ((2 + DeltaMax q r + 16 * q) * |β y| + 16 * q) := add_le_add hgap hXi1
      _ = _ := by ring
  have hDM0 : 0 ≤ DeltaMax q r := by unfold DeltaMax; positivity
  have hdev : μ.expect (fun y => (s y - 1) ^ 2) ≤ Dfull q r ^ 2 := by
    have h := rootMarginal_sq_le_of_pointwise μ (f := fun y => s y - 1) (g := β)
      (by positivity) (by positivity) hpt hD2
    unfold Dfull
    convert h using 2
    ring
  -- `E ς ≥ L_low`
  have hmean : Llow q r ≤ μ.expect s := by
    have h1 : ∀ y, (1 - 24 * aP q r) * ((1 - DeltaMax q r) * (1 - DeltaMax q r - 16 * q)) ≤ s y :=
      fun y => by
        have := (hs y).1
        rw [hΞ y] at this
        exact le_trans (mul_le_mul_of_nonneg_left (hΞlo y) hl2.le) this
    have := μ.const_le_expect h1
    unfold Llow
    linarith
  have hL := rootMarginal_Llow_pos hq ⟨hl1, hl2⟩
  exact chiSq_le_of_sq_dev hpos μ.total hL hmean hdev

/-- **`lem:record:root-marginal`(ii)**: under the hypotheses of (i) and of the second bound, with
the count `𝔑 = K ς` (`K = 𝒵 n̄² > 0`),
`χ_p = χ²(ν_{L,p} ‖ λ_{F,p}) ≤ min((R_p - 1)²/R_p, D_full²/L_low²)`. -/
theorem rootMarginal_ii {S : Type*} [Fintype S] (μ : FiniteLaw S)
    (hpos : ∀ y, 0 < μ.weight y) {p q r K : ℝ} (hp : 0 < p) (hqp : q = 1 / p)
    (hr : r * Real.sqrt p = 1) (hK : 0 < K) (hlow : LowerFactors q r) (W n₁ n s : S → ℝ)
    (hcount : ∀ y, lowerProd q r ≤ K * s y / K ∧ K * s y / K ≤ (1 + upsPlus q r) ^ 2)
    (hWeil : ∀ y, |W y| ≤ 11 * Real.sqrt p)
    (hn₁ : ∀ y, n₁ y = 0 ∨ n₁ y = 1 ∨ n₁ y = 2)
    (hn : ∀ y, n y = (p + 2 + W y) / 16 - n₁ y)
    (hmom : μ.expect (fun y => (W y / p) ^ 2) ≤ (5 * q + 34 * q * r + 11 * q ^ 3) / Z4 q)
    (hs : ∀ y, (1 - 24 * aP q r) * (n y * (n y - 1) / (p / 16) ^ 2) ≤ s y ∧
      s y ≤ n y * (n y - 1) / (p / 16) ^ 2) :
    chiSq (halfLaw μ.weight (fun y => K * s y)) μ.weight ≤
      min ((Rp q r - 1) ^ 2 / Rp q r) (Dfull q r ^ 2 / Llow q r ^ 2) := by
  have hq : 0 < q := by rw [hqp]; positivity
  refine le_min (rootMarginal_ii_first hpos μ.total hK hq hlow hcount) ?_
  rw [rootMarginal_halfLaw_smul μ.weight s hK.ne']
  exact rootMarginal_ii_second μ hpos hp hqp hr hlow W n₁ n s hWeil hn₁ hn hmom hs

/-! ### (iii): blocks -/

/-- **`lem:record:root-marginal`(iii).** At a block `𝔅` with at most `n` primes, the root and
`λ_F` are products over the primes. If at each prime the density lies in `[R_p⁻¹, R_p]` with
`1 ≤ R_p ≤ R̄` and `χ_p ≤ χ̄` (by (i), (ii) and the monotonicity of `lem:majorant`, here
**hypotheses**), then hypothesis (A) (`hyp:variance:A`) holds with `M_𝔅 = ∏ R_p ≤ R̄ⁿ`, and
`χ²(ν_{L,𝔅} ‖ λ_{F,𝔅}) = ∏_p (1 + χ_p) - 1 ≤ (1 + χ̄)ⁿ - 1`. -/
theorem rootMarginal_iii {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*}
    [∀ i, Fintype (S i)] {nu lam : ∀ i, S i → ℝ} (hlam : ∀ i y, 0 < lam i y)
    (hnu1 : ∀ i, ∑ y, nu i y = 1) (hlam1 : ∀ i, ∑ y, lam i y = 1) {R : I → ℝ}
    {Rbar χbar : ℝ} {n : ℕ} (hn : Fintype.card I ≤ n) (hR1 : ∀ i, 1 ≤ R i)
    (hRbar : ∀ i, R i ≤ Rbar) (hRbar1 : 1 ≤ Rbar)
    (hlo : ∀ i y, (R i)⁻¹ ≤ nu i y / lam i y) (hhi : ∀ i y, nu i y / lam i y ≤ R i)
    (hχ : ∀ i, chiSq (nu i) (lam i) ≤ χbar) (hχbar : 0 ≤ χbar) :
    (∀ x, (Rbar ^ n)⁻¹ ≤ prodWeight nu x / prodWeight lam x ∧
        prodWeight nu x / prodWeight lam x ≤ Rbar ^ n) ∧
      chiSq (prodWeight nu) (prodWeight lam) = ∏ i, (1 + chiSq (nu i) (lam i)) - 1 ∧
      chiSq (prodWeight nu) (prodWeight lam) ≤ (1 + χbar) ^ n - 1 := by
  have hRpos : ∀ i, 0 < R i := fun i => lt_of_lt_of_le zero_lt_one (hR1 i)
  have hprodR : ∏ i, R i ≤ Rbar ^ n := prod_le_pow_of_le hR1 hRbar hRbar1 hn
  have hprodR0 : 0 < ∏ i, R i := prod_pos fun i _ => hRpos i
  have hid := chiSq_prod hlam hnu1 hlam1
  refine ⟨fun x => ?_, by linarith, ?_⟩
  · obtain ⟨h1, h2⟩ := chiSq_prod_density_range hRpos hlo hhi x
    exact ⟨le_trans (inv_anti₀ hprodR0 hprodR) h1, le_trans h2 hprodR⟩
  · have := chiSq_prod_le_pow (χ := fun i => chiSq (nu i) (lam i))
      (fun i => chiSq_nonneg (hlam i)) hχ hχbar hn
    linarith

/-! ### (iv): a mean-one density with a range ratio -/

/-- **`lem:record:root-marginal`(iv), the step "`inf T𝟙 ≤ 1 ≤ sup T𝟙`"**: a density `g` of
`λ`-mean one (positive weights) whose values satisfy `g x ≤ R g y` for all `x, y` lies in
`[R⁻¹, R]`; this turns the range ratio `R_𝔲(X)ⁿ` of the positive roots into hypothesis (A). -/
theorem rootMarginal_iv_density_bounds {S : Type*} [Fintype S] {lam g : S → ℝ}
    (hlam : ∀ y, 0 < lam y) (hlam1 : ∑ y, lam y = 1) (hmean : ∑ y, lam y * g y = 1)
    {R : ℝ} (hR : 0 < R) (hratio : ∀ x y, g x ≤ R * g y) (x : S) :
    R⁻¹ ≤ g x ∧ g x ≤ R := by
  -- some point has `g ≤ 1`, some point has `g ≥ 1`
  have hlow : ∃ y, g y ≤ 1 := by
    by_contra h
    push Not at h
    have : ∑ y, lam y * 1 < ∑ y, lam y * g y := by
      apply sum_lt_sum_of_nonempty
      · obtain ⟨y⟩ : Nonempty S := ⟨x⟩
        exact ⟨y, mem_univ y⟩
      · intro y _
        exact mul_lt_mul_of_pos_left (h y) (hlam y)
    simp only [mul_one] at this
    linarith
  have hhigh : ∃ y, 1 ≤ g y := by
    by_contra h
    push Not at h
    have : ∑ y, lam y * g y < ∑ y, lam y * 1 := by
      apply sum_lt_sum_of_nonempty
      · exact ⟨x, mem_univ x⟩
      · intro y _
        exact mul_lt_mul_of_pos_left (h y) (hlam y)
    simp only [mul_one] at this
    linarith
  obtain ⟨y₀, hy₀⟩ := hlow
  obtain ⟨y₁, hy₁⟩ := hhigh
  constructor
  · have h := hratio y₁ x
    rw [inv_eq_one_div, div_le_iff₀ hR]
    linarith [mul_comm (g x) R]
  · have h := hratio x y₀
    nlinarith

/-! ### Monotonicity in `(q, r)` (`lem:majorant`) and the endpoint form of (iii) -/

/-- The chi-square bound of (ii) at one prime: `χ̄(q, r) = min((R_p - 1)²/R_p, D_full²/L_low²)`. -/
noncomputable def chiBar (q r : ℝ) : ℝ :=
  min ((Rp q r - 1) ^ 2 / Rp q r) (Dfull q r ^ 2 / Llow q r ^ 2)

section Mono

variable {q r q' r' : ℝ}

/-- Positivity of the denominators at a point with a positive first lower factor. -/
theorem rootMarginal_denoms_pos (hq : 0 < q) (hr : 0 ≤ r) (h1 : 0 < 1 - upsTimes q r - 16 * q) :
    0 < 1 - 3 * q ∧ 0 < 1 - upsMinus q r ∧ 0 < 1 - upsMinus q r - 16 * q ∧ 0 < 1 - 7 * q ∧
      0 < 1 - upsTimes q r ∧ 0 < 1 - DeltaMax q r - 16 * q ∧ 0 < 1 - DeltaMax q r := by
  unfold upsTimes at h1
  unfold upsMinus DeltaMax upsTimes
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-- `𝔞_p` is nondecreasing in `(q, r)` on the domain of the first lower factor. -/
theorem rootMarginal_aP_mono (hq : 0 < q) (hr : 0 ≤ r) (hqq : q ≤ q') (hrr : r ≤ r')
    (h1 : 0 < 1 - upsTimes q' r' - 16 * q') : aP q r ≤ aP q' r' := by
  obtain ⟨d1, d2, d3, -, -, -, -⟩ := rootMarginal_denoms_pos (hq.trans_le hqq) (hr.trans hrr) h1
  unfold aP
  unfold upsMinus at d2 d3 ⊢
  unfold upsPlus
  have hA : 4 * q / (1 - 3 * q) ≤ 4 * q' / (1 - 3 * q') :=
    div_le_div₀ (by linarith) (by linarith) d1 (by linarith)
  have hB : (1 + (11 * r + 6 * q)) ^ 2 ≤ (1 + (11 * r' + 6 * q')) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hC : (1 - (11 * r' + 70 * q')) * (1 - (11 * r' + 70 * q') - 16 * q') ≤
      (1 - (11 * r + 70 * q)) * (1 - (11 * r + 70 * q) - 16 * q) :=
    mul_le_mul (by linarith) (by linarith) d3.le (by linarith)
  have hBC : (1 + (11 * r + 6 * q)) ^ 2 /
      ((1 - (11 * r + 70 * q)) * (1 - (11 * r + 70 * q) - 16 * q)) ≤
      (1 + (11 * r' + 6 * q')) ^ 2 /
        ((1 - (11 * r' + 70 * q')) * (1 - (11 * r' + 70 * q') - 16 * q')) :=
    div_le_div₀ (by positivity) hB (mul_pos d2 d3) hC
  have hBC0 : 0 ≤ (1 + (11 * r + 6 * q)) ^ 2 /
      ((1 - (11 * r + 70 * q)) * (1 - (11 * r + 70 * q) - 16 * q)) := by
    have e2 : 0 < 1 - (11 * r + 70 * q) := by linarith
    have e3 : 0 < 1 - (11 * r + 70 * q) - 16 * q := by linarith
    positivity
  have hA' : 0 ≤ 4 * q' / (1 - 3 * q') := div_nonneg (by linarith) d1.le
  exact mul_le_mul hA hBC hBC0 hA'

/-- The lower factors at `(q', r')` give the lower factors at every smaller `(q, r)`. -/
theorem rootMarginal_lowerFactors_mono (hq : 0 < q) (hr : 0 ≤ r) (hqq : q ≤ q') (hrr : r ≤ r')
    (h : LowerFactors q' r') : LowerFactors q r := by
  have ha := rootMarginal_aP_mono hq hr hqq hrr h.1
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, by linarith⟩
  unfold upsTimes at h1 ⊢
  linarith

/-- `R_p` is nondecreasing in `(q, r)` on the domain of the lower factors. -/
theorem rootMarginal_Rp_mono (hq : 0 < q) (hr : 0 ≤ r) (hqq : q ≤ q') (hrr : r ≤ r')
    (h : LowerFactors q' r') : Rp q r ≤ Rp q' r' := by
  have ha := rootMarginal_aP_mono hq hr hqq hrr h.1
  have hP' := rootMarginal_lowerProd_pos (hq.trans_le hqq) h
  obtain ⟨-, -, -, -, d5, -, -⟩ := rootMarginal_denoms_pos (hq.trans_le hqq) (hr.trans hrr) h.1
  obtain ⟨h1, h2⟩ := h
  unfold Rp
  apply div_le_div₀ (by positivity) _ hP'
  · unfold lowerProd
    unfold upsTimes at h1 d5 ⊢
    apply mul_le_mul (mul_le_mul (by linarith) (by linarith) h1.le (by linarith)) (by linarith)
      h2.le
    have : 0 ≤ 1 - (11 * r + 102 * q) := by linarith
    have : 0 ≤ 1 - (11 * r + 102 * q) - 16 * q := by linarith
    positivity
  · unfold upsPlus
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- `(R - 1)²/R` is nondecreasing for `R ≥ 1`. -/
theorem rootMarginal_range_chi_mono {R R' : ℝ} (hR : 1 ≤ R) (hRR : R ≤ R') :
    (R - 1) ^ 2 / R ≤ (R' - 1) ^ 2 / R' := by
  have h0 : 0 < R := by linarith
  have h0' : 0 < R' := by linarith
  rw [div_le_div_iff₀ h0 h0']
  have : 0 ≤ (R' - R) * (R * R' - 1) := mul_nonneg (by linarith) (by nlinarith)
  nlinarith

/-- `Δ₂` is nondecreasing in `(q, r)` on the domain of the first lower factor. -/
theorem rootMarginal_Delta2_mono (hq : 0 < q) (hr : 0 ≤ r) (hqq : q ≤ q') (hrr : r ≤ r')
    (h1 : 0 < 1 - upsTimes q' r' - 16 * q') : Delta2 q r ≤ Delta2 q' r' := by
  obtain ⟨d1, -, -, d4, -, -, -⟩ := rootMarginal_denoms_pos (hq.trans_le hqq) (hr.trans hrr) h1
  unfold Delta2
  have hZ' : 0 < Z4 q' := by
    unfold Z4
    have : 0 < 1 - q' := by linarith
    positivity
  have hZ : Z4 q' ≤ Z4 q := by
    unfold Z4
    apply mul_le_mul (mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith))
      (by linarith) (by linarith)
    have : 0 ≤ 1 - q := by linarith
    have : 0 ≤ 1 - 3 * q := by linarith
    positivity
  have hN : 5 * q + 34 * q * r + 11 * q ^ 3 ≤ 5 * q' + 34 * q' * r' + 11 * q' ^ 3 := by
    have : q * r ≤ q' * r' := mul_le_mul hqq hrr hr (by linarith)
    have : q ^ 3 ≤ q' ^ 3 := pow_le_pow_left₀ hq.le hqq 3
    linarith
  have hfrac : (5 * q + 34 * q * r + 11 * q ^ 3) / Z4 q ≤
      (5 * q' + 34 * q' * r' + 11 * q' ^ 3) / Z4 q' := by
    have : 0 ≤ 5 * q' + 34 * q' * r' + 11 * q' ^ 3 := by
      have : 0 ≤ q' := by linarith
      have : 0 ≤ r' := by linarith
      positivity
    exact div_le_div₀ this hN hZ' hZ
  have := Real.sqrt_le_sqrt hfrac
  linarith

/-- `χ̄(q, r)` is nondecreasing in `(q, r)` on the domain of the lower factors. -/
theorem rootMarginal_chiBar_mono (hq : 0 < q) (hr : 0 ≤ r) (hqq : q ≤ q') (hrr : r ≤ r')
    (h : LowerFactors q' r') : chiBar q r ≤ chiBar q' r' := by
  have hl := rootMarginal_lowerFactors_mono hq hr hqq hrr h
  have hR1 := rootMarginal_Rp_ge_one hq hr hl
  have hRR := rootMarginal_Rp_mono hq hr hqq hrr h
  have ha := rootMarginal_aP_mono hq hr hqq hrr h.1
  have ha0 := rootMarginal_aP_nonneg hq hr hl.1
  have hD2 := rootMarginal_Delta2_mono hq hr hqq hrr h.1
  have hL' := rootMarginal_Llow_pos (hq.trans_le hqq) h
  obtain ⟨-, -, -, -, -, d6, d7⟩ := rootMarginal_denoms_pos (hq.trans_le hqq) (hr.trans hrr) h.1
  have hD20 : 0 ≤ Delta2 q r := by unfold Delta2; positivity
  have hDM : DeltaMax q r ≤ DeltaMax q' r' := by unfold DeltaMax; linarith
  have hDM0 : 0 ≤ DeltaMax q r := by unfold DeltaMax; positivity
  have hD : Dfull q r ≤ Dfull q' r' := by
    unfold Dfull
    have t1 : (2 + DeltaMax q r + 16 * q) * Delta2 q r ≤
        (2 + DeltaMax q' r' + 16 * q') * Delta2 q' r' :=
      mul_le_mul (by linarith) hD2 hD20 (by linarith)
    have t2 : (1 + DeltaMax q r) ^ 2 ≤ (1 + DeltaMax q' r') ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have t3 : aP q r * (1 + DeltaMax q r) ^ 2 ≤ aP q' r' * (1 + DeltaMax q' r') ^ 2 :=
      mul_le_mul ha t2 (by positivity) (ha0.trans ha)
    linarith
  have hD0 : 0 ≤ Dfull q r := by unfold Dfull; positivity
  have hL : Llow q' r' ≤ Llow q r := by
    unfold Llow
    obtain ⟨h1, h2⟩ := h
    have e1 : 1 - DeltaMax q' r' ≤ 1 - DeltaMax q r := by linarith
    have e2 : 1 - DeltaMax q' r' - 16 * q' ≤ 1 - DeltaMax q r - 16 * q := by linarith
    have e3 : 1 - 24 * aP q' r' ≤ 1 - 24 * aP q r := by linarith
    apply mul_le_mul (mul_le_mul e1 e2 d6.le (by linarith)) e3 h2.le
    have : 0 ≤ 1 - DeltaMax q r := by linarith
    have : 0 ≤ 1 - DeltaMax q r - 16 * q := by linarith
    positivity
  unfold chiBar
  apply min_le_min (rootMarginal_range_chi_mono hR1 hRR)
  apply div_le_div₀ (by positivity) (pow_le_pow_left₀ hD0 hD 2) (by positivity)
    (pow_le_pow_left₀ hL'.le hL 2)

theorem rootMarginal_chiBar_nonneg (hq : 0 < q) (hr : 0 ≤ r) (h : LowerFactors q r) :
    0 ≤ chiBar q r := by
  have hR1 := rootMarginal_Rp_ge_one hq hr h
  unfold chiBar
  exact le_min (div_nonneg (sq_nonneg _) (by linarith)) (div_nonneg (sq_nonneg _) (sq_nonneg _))

end Mono

/-- **`lem:record:root-marginal`(iii), endpoint form.** Let the primes of a block have
parameters `(q_p, r_p)` with `0 < q_p ≤ q_X`, `0 ≤ r_p ≤ r_X` (`q_X = 1/X`, any `r_X ≥ X^{-1/2}`),
the lower factors positive at `(q_X, r_X)`, and at each prime the conclusions of (i) and (ii):
density in `[R_p⁻¹, R_p]` and `χ_p ≤ χ̄(q_p, r_p)`. Then, for at most `n` primes, hypothesis (A)
holds with `M_𝔅 ≤ R̄(X)ⁿ`, `R̄(X) = R(q_X, r_X)`, and
`χ²(ν_{L,𝔅} ‖ λ_{F,𝔅}) ≤ (1 + χ̄(X))ⁿ - 1`. The monotonicity (`lem:majorant`) is proved here
(`rootMarginal_Rp_mono`, `rootMarginal_chiBar_mono`). -/
theorem rootMarginal_iii_endpoint {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*}
    [∀ i, Fintype (S i)] {nu lam : ∀ i, S i → ℝ} (hlam : ∀ i y, 0 < lam i y)
    (hnu1 : ∀ i, ∑ y, nu i y = 1) (hlam1 : ∀ i, ∑ y, lam i y = 1)
    {qp rp : I → ℝ} {qX rX : ℝ} {n : ℕ} (hn : Fintype.card I ≤ n)
    (hq0 : ∀ i, 0 < qp i) (hr0 : ∀ i, 0 ≤ rp i) (hqX : ∀ i, qp i ≤ qX) (hrX : ∀ i, rp i ≤ rX)
    (hqX0 : 0 < qX) (hrX0 : 0 ≤ rX) (hlowX : LowerFactors qX rX)
    (hlo : ∀ i y, (Rp (qp i) (rp i))⁻¹ ≤ nu i y / lam i y)
    (hhi : ∀ i y, nu i y / lam i y ≤ Rp (qp i) (rp i))
    (hχ : ∀ i, chiSq (nu i) (lam i) ≤ chiBar (qp i) (rp i)) :
    (∀ x, (Rp qX rX ^ n)⁻¹ ≤ prodWeight nu x / prodWeight lam x ∧
        prodWeight nu x / prodWeight lam x ≤ Rp qX rX ^ n) ∧
      chiSq (prodWeight nu) (prodWeight lam) ≤ (1 + chiBar qX rX) ^ n - 1 := by
  have hlow : ∀ i, LowerFactors (qp i) (rp i) := fun i =>
    rootMarginal_lowerFactors_mono (hq0 i) (hr0 i) (hqX i) (hrX i) hlowX
  obtain ⟨h1, -, h3⟩ := rootMarginal_iii hlam hnu1 hlam1 (R := fun i => Rp (qp i) (rp i))
    (Rbar := Rp qX rX) (χbar := chiBar qX rX) hn
    (fun i => rootMarginal_Rp_ge_one (hq0 i) (hr0 i) (hlow i))
    (fun i => rootMarginal_Rp_mono (hq0 i) (hr0 i) (hqX i) (hrX i) hlowX)
    (rootMarginal_Rp_ge_one hqX0 hrX0 hlowX) hlo hhi
    (fun i => (hχ i).trans (rootMarginal_chiBar_mono (hq0 i) (hr0 i) (hqX i) (hrX i) hlowX))
    (rootMarginal_chiBar_nonneg hqX0 hrX0 hlowX)
  exact ⟨h1, h3⟩

/-! ### Non-vacuity -/

/-- **Non-vacuity of the domain**: the lower factors are positive at the start of the first middle
piece, `X₁ = 19951586`, with `q = 1/X₁` and `r = 1/⌊√X₁⌋ = 1/4466` (the evaluation point of
`eq:variance:pieces`). -/
theorem rootMarginal_lowerFactors_first_piece : LowerFactors (1 / 19951586) (1 / 4466) := by
  unfold LowerFactors aP upsTimes upsPlus upsMinus
  norm_num

/-- **Non-vacuity of the hypotheses of the second bound**: they are jointly satisfiable, here by
a one-point law at `p = 4466²` (`√p = 4466`), with `𝒲 = 0`, `n₁ = 0` and `ς = Ξ`. -/
theorem rootMarginal_ii_second_satisfiable :
    ∃ (μ : FiniteLaw Unit) (p q r : ℝ) (W n₁ n s : Unit → ℝ),
      (∀ y, 0 < μ.weight y) ∧ 0 < p ∧ q = 1 / p ∧ r * Real.sqrt p = 1 ∧ LowerFactors q r ∧
      (∀ y, |W y| ≤ 11 * Real.sqrt p) ∧ (∀ y, n₁ y = 0 ∨ n₁ y = 1 ∨ n₁ y = 2) ∧
      (∀ y, n y = (p + 2 + W y) / 16 - n₁ y) ∧
      μ.expect (fun y => (W y / p) ^ 2) ≤ (5 * q + 34 * q * r + 11 * q ^ 3) / Z4 q ∧
      (∀ y, (1 - 24 * aP q r) * (n y * (n y - 1) / (p / 16) ^ 2) ≤ s y ∧
        s y ≤ n y * (n y - 1) / (p / 16) ^ 2) := by
  let μ : FiniteLaw Unit := ⟨fun _ => 1, fun _ => zero_le_one, by simp⟩
  have hsq : Real.sqrt ((4466 : ℝ) ^ 2) = 4466 := Real.sqrt_sq (by norm_num)
  have hlow : LowerFactors (1 / (4466 : ℝ) ^ 2) (1 / 4466) := by
    unfold LowerFactors aP upsTimes upsPlus upsMinus
    norm_num
  have ha : 0 ≤ aP (1 / (4466 : ℝ) ^ 2) (1 / 4466) :=
    rootMarginal_aP_nonneg (by norm_num) (by norm_num) hlow.1
  have hΞ : 0 ≤ ((4466 : ℝ) ^ 2 + 2 + 0) / 16 * (((4466 : ℝ) ^ 2 + 2 + 0) / 16 - 1) /
      ((4466 : ℝ) ^ 2 / 16) ^ 2 := by positivity
  refine ⟨μ, (4466 : ℝ) ^ 2, 1 / (4466 : ℝ) ^ 2, 1 / 4466, fun _ => 0, fun _ => 0,
    fun _ => ((4466 : ℝ) ^ 2 + 2 + 0) / 16 - 0,
    fun _ => ((4466 : ℝ) ^ 2 + 2 + 0) / 16 * (((4466 : ℝ) ^ 2 + 2 + 0) / 16 - 1) /
      ((4466 : ℝ) ^ 2 / 16) ^ 2,
    fun _ => zero_lt_one, by positivity, rfl, by rw [hsq]; norm_num, hlow,
    fun _ => by rw [hsq]; norm_num, fun _ => Or.inl rfl, fun _ => rfl, ?_, fun _ => ?_⟩
  · have : μ.expect (fun _ => ((0 : ℝ) / (4466 : ℝ) ^ 2) ^ 2) = 0 := by
      simp [FiniteLaw.expect, μ]
    rw [this]
    unfold Z4
    norm_num
  · simp only [sub_zero, add_zero]
    simp only [add_zero] at hΞ
    constructor
    · nlinarith [mul_nonneg ha hΞ]
    · exact le_rfl

/-! ### The soft count of (ii) and the Weil bound for `𝒲` -/

section SoftCount

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `𝒲 = ∑_{|A| ∈ {3,4}} s_A ∑_z ∏_{i∈A} χ(z - xᵢ)` for the signs `s = (-1,-1,1,1)`. -/
def softW (x₁ x₂ x₃ x₄ : F) : ℤ :=
  ∑ z : F, (quadraticChar F (z - x₁) * quadraticChar F (z - x₂) * quadraticChar F (z - x₃) +
    quadraticChar F (z - x₁) * quadraticChar F (z - x₂) * quadraticChar F (z - x₄) -
    quadraticChar F (z - x₁) * quadraticChar F (z - x₃) * quadraticChar F (z - x₄) -
    quadraticChar F (z - x₂) * quadraticChar F (z - x₃) * quadraticChar F (z - x₄) +
    quadraticChar F (z - x₁) * quadraticChar F (z - x₂) * quadraticChar F (z - x₃) *
      quadraticChar F (z - x₄))

/-- The soft count `𝔖 = ∑_z ∏ᵢ (1 + sᵢ χ(z - xᵢ))` for the signs `(-1,-1,1,1)`. -/
def softCount (x₁ x₂ x₃ x₄ : F) : ℤ :=
  ∑ z : F, (1 - quadraticChar F (z - x₁)) * (1 - quadraticChar F (z - x₂)) *
    (1 + quadraticChar F (z - x₃)) * (1 + quadraticChar F (z - x₄))

theorem rootMarginal_sum_chi_sub (hF : ringChar F ≠ 2) (a : F) :
    ∑ z : F, quadraticChar F (z - a) = 0 := by
  have h := Labellings.rootSum_singleton hF a
  simpa [Labellings.rootSum] using h

theorem rootMarginal_sum_chi_pair (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ z : F, quadraticChar F (z - a) * quadraticChar F (z - b) = -1 := by
  have h := Labellings.two_root hF hab
  unfold Labellings.rootSum at h
  simp only [prod_pair hab, map_mul] at h
  exact h

/-- **The soft count identity** (proof of `lem:record:root-marginal`(ii), from `eq:two-root`):
for distinct `x₁, …, x₄`, `𝔖 = q + 2 + 𝒲`: the singleton sums vanish, each quadratic sum is `-1`,
and `∑_{i<k} sᵢ s_k = -2`. -/
theorem rootMarginal_softCount_eq (hF : ringChar F ≠ 2) {x₁ x₂ x₃ x₄ : F} (h12 : x₁ ≠ x₂)
    (h13 : x₁ ≠ x₃) (h14 : x₁ ≠ x₄) (h23 : x₂ ≠ x₃) (h24 : x₂ ≠ x₄) (h34 : x₃ ≠ x₄) :
    softCount x₁ x₂ x₃ x₄ = (Fintype.card F : ℤ) + 2 + softW x₁ x₂ x₃ x₄ := by
  unfold softCount softW
  have hpt : ∀ z : F, (1 - quadraticChar F (z - x₁)) * (1 - quadraticChar F (z - x₂)) *
      (1 + quadraticChar F (z - x₃)) * (1 + quadraticChar F (z - x₄)) =
      1 + (quadraticChar F (z - x₃) + quadraticChar F (z - x₄) - quadraticChar F (z - x₁) -
        quadraticChar F (z - x₂)) +
      (quadraticChar F (z - x₃) * quadraticChar F (z - x₄) -
        quadraticChar F (z - x₁) * quadraticChar F (z - x₃) -
        quadraticChar F (z - x₁) * quadraticChar F (z - x₄) -
        quadraticChar F (z - x₂) * quadraticChar F (z - x₃) -
        quadraticChar F (z - x₂) * quadraticChar F (z - x₄) +
        quadraticChar F (z - x₁) * quadraticChar F (z - x₂)) +
      (quadraticChar F (z - x₁) * quadraticChar F (z - x₂) * quadraticChar F (z - x₃) +
        quadraticChar F (z - x₁) * quadraticChar F (z - x₂) * quadraticChar F (z - x₄) -
        quadraticChar F (z - x₁) * quadraticChar F (z - x₃) * quadraticChar F (z - x₄) -
        quadraticChar F (z - x₂) * quadraticChar F (z - x₃) * quadraticChar F (z - x₄) +
        quadraticChar F (z - x₁) * quadraticChar F (z - x₂) * quadraticChar F (z - x₃) *
          quadraticChar F (z - x₄)) := by
    intro z
    ring
  simp only [hpt, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one,
    rootMarginal_sum_chi_sub hF, rootMarginal_sum_chi_pair hF h12, rootMarginal_sum_chi_pair hF h13,
    rootMarginal_sum_chi_pair hF h14, rootMarginal_sum_chi_pair hF h23,
    rootMarginal_sum_chi_pair hF h24, rootMarginal_sum_chi_pair hF h34]
  ring

/-- The signed neighbourhood `{z : χ(z-x₁) = χ(z-x₂) = -1, χ(z-x₃) = χ(z-x₄) = 1}` of
`lem:record:signed-nbhd` for the signs `(-1,-1,1,1)`. -/
def signedNbhd (x₁ x₂ x₃ x₄ : F) : Finset F :=
  univ.filter fun z => quadraticChar F (z - x₁) = -1 ∧ quadraticChar F (z - x₂) = -1 ∧
    quadraticChar F (z - x₃) = 1 ∧ quadraticChar F (z - x₄) = 1

theorem rootMarginal_chi_vals' {a : F} (ha : a ≠ 0) :
    quadraticChar F a = 1 ∨ quadraticChar F a = -1 := quadraticChar_dichotomy ha

/-- **The soft count is `16` times the signed neighbourhood** for admissible labels
(`x₁, x₂ → x₃, x₄`; only `x₁ → x₃`, `x₁ → x₄`, `x₂ → x₃` are used) when `χ(-1) = -1`
(`p ≡ 3 (mod 4)`): at each of the four labels one factor vanishes. -/
theorem rootMarginal_softCount_card (hm : quadraticChar F (-1) = -1) {x₁ x₂ x₃ x₄ : F}
    (h13 : quadraticChar F (x₃ - x₁) = 1) (h14 : quadraticChar F (x₄ - x₁) = 1)
    (h23 : quadraticChar F (x₃ - x₂) = 1) :
    softCount x₁ x₂ x₃ x₄ = 16 * ((signedNbhd x₁ x₂ x₃ x₄).card : ℤ) := by
  have hneg : ∀ a b : F, quadraticChar F (b - a) = 1 → quadraticChar F (a - b) = -1 := by
    intro a b h
    rw [show a - b = (-1) * (b - a) by ring, map_mul, hm, h]
    ring
  have key : ∀ z : F, (1 - quadraticChar F (z - x₁)) * (1 - quadraticChar F (z - x₂)) *
      (1 + quadraticChar F (z - x₃)) * (1 + quadraticChar F (z - x₄)) =
      if (quadraticChar F (z - x₁) = -1 ∧ quadraticChar F (z - x₂) = -1 ∧
        quadraticChar F (z - x₃) = 1 ∧ quadraticChar F (z - x₄) = 1) then 16 else 0 := by
    intro z
    by_cases hz1 : z = x₁
    · rw [hz1, hneg x₁ x₃ h13, sub_self]
      simp
    by_cases hz2 : z = x₂
    · rw [hz2, hneg x₂ x₃ h23, sub_self]
      simp
    by_cases hz3 : z = x₃
    · rw [hz3, h13]
      simp
    by_cases hz4 : z = x₄
    · rw [hz4, h14]
      simp
    rcases rootMarginal_chi_vals' (sub_ne_zero.mpr hz1) with a | a <;>
      rcases rootMarginal_chi_vals' (sub_ne_zero.mpr hz2) with b | b <;>
      rcases rootMarginal_chi_vals' (sub_ne_zero.mpr hz3) with c | c <;>
      rcases rootMarginal_chi_vals' (sub_ne_zero.mpr hz4) with d | d <;>
      simp only [a, b, c, d] <;> norm_num
  unfold softCount signedNbhd
  simp only [key]
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  ring

/-- The signed neighbourhood has `(q + 2 + 𝒲)/16` elements (distinct admissible labels,
`χ(-1) = -1`). This is the identity behind the hypothesis `hn` of `rootMarginal_ii_second`. -/
theorem rootMarginal_signedNbhd_card (hF : ringChar F ≠ 2) (hm : quadraticChar F (-1) = -1)
    {x₁ x₂ x₃ x₄ : F} (h12 : x₁ ≠ x₂) (h13' : x₁ ≠ x₃) (h14' : x₁ ≠ x₄) (h23' : x₂ ≠ x₃)
    (h24' : x₂ ≠ x₄) (h34 : x₃ ≠ x₄)
    (h13 : quadraticChar F (x₃ - x₁) = 1) (h14 : quadraticChar F (x₄ - x₁) = 1)
    (h23 : quadraticChar F (x₃ - x₂) = 1) :
    ((signedNbhd x₁ x₂ x₃ x₄).card : ℝ) =
      ((Fintype.card F : ℝ) + 2 + (softW x₁ x₂ x₃ x₄ : ℝ)) / 16 := by
  have h1 := rootMarginal_softCount_eq hF h12 h13' h14' h23' h24' h34
  have h2 := rootMarginal_softCount_card hm h13 h14 h23
  have h3 : (16 : ℤ) * ((signedNbhd x₁ x₂ x₃ x₄).card : ℤ) =
      (Fintype.card F : ℤ) + 2 + softW x₁ x₂ x₃ x₄ := by rw [← h2, h1]
  have h4 : (16 : ℝ) * ((signedNbhd x₁ x₂ x₃ x₄).card : ℝ) =
      (Fintype.card F : ℝ) + 2 + (softW x₁ x₂ x₃ x₄ : ℝ) := by exact_mod_cast h3
  linarith

theorem rootMarginal_rootSum_three {a b c : F} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Labellings.rootSum ({a, b, c} : Finset F) =
      ∑ z : F, quadraticChar F (z - a) * quadraticChar F (z - b) * quadraticChar F (z - c) := by
  unfold Labellings.rootSum
  apply sum_congr rfl
  intro z _
  rw [prod_insert (by simp [hab, hac]), prod_pair hbc, map_mul, map_mul]
  ring

omit [Field F] [Fintype F] in
theorem rootMarginal_card_three {a b c : F} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset F).card = 3 := by
  rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]

theorem rootMarginal_rootSum_four {a b c d : F} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Labellings.rootSum ({a, b, c, d} : Finset F) =
      ∑ z : F, quadraticChar F (z - a) * quadraticChar F (z - b) * quadraticChar F (z - c) *
        quadraticChar F (z - d) := by
  unfold Labellings.rootSum
  apply sum_congr rfl
  intro z _
  rw [prod_insert (by simp [hab, hac, had]), prod_insert (by simp [hbc, hbd]), prod_pair hcd,
    map_mul, map_mul, map_mul]
  ring

omit [Field F] [Fintype F] in
theorem rootMarginal_card_four {a b c d : F} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Finset F).card = 4 := by
  rw [card_insert_of_notMem (by simp [hab, hac, had]), card_insert_of_notMem (by simp [hbc, hbd]),
    card_pair hcd]

/-- **The Weil bound for `𝒲`** (`thm:weil`, the hypothesis `hWeil` of `rootMarginal_ii_second`):
under `Labellings.WeilBound F` (H1), `|𝒲| ≤ 4·2√q + 3√q = 11√q` for distinct labels. -/
theorem rootMarginal_softW_weil (hW : Labellings.WeilBound F) {x₁ x₂ x₃ x₄ : F}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h14 : x₁ ≠ x₄) (h23 : x₂ ≠ x₃) (h24 : x₂ ≠ x₄)
    (h34 : x₃ ≠ x₄) :
    |(softW x₁ x₂ x₃ x₄ : ℝ)| ≤ 11 * Real.sqrt (Fintype.card F) := by
  have hsplit : softW x₁ x₂ x₃ x₄ = Labellings.rootSum ({x₁, x₂, x₃} : Finset F) +
      Labellings.rootSum ({x₁, x₂, x₄} : Finset F) -
      Labellings.rootSum ({x₁, x₃, x₄} : Finset F) -
      Labellings.rootSum ({x₂, x₃, x₄} : Finset F) +
      Labellings.rootSum ({x₁, x₂, x₃, x₄} : Finset F) := by
    rw [rootMarginal_rootSum_three h12 h13 h23, rootMarginal_rootSum_three h12 h14 h24,
      rootMarginal_rootSum_three h13 h14 h34, rootMarginal_rootSum_three h23 h24 h34,
      rootMarginal_rootSum_four h12 h13 h14 h23 h24 h34]
    unfold softW
    simp only [← sum_add_distrib, ← sum_sub_distrib]
  have w3 : ∀ {a b c : F}, a ≠ b → a ≠ c → b ≠ c →
      |(Labellings.rootSum ({a, b, c} : Finset F) : ℝ)| ≤ 2 * Real.sqrt (Fintype.card F) := by
    intro a b c hab hac hbc
    have := hW {a, b, c} (insert_nonempty _ _)
    rw [rootMarginal_card_three hab hac hbc] at this
    norm_num at this
    exact this
  have w4 : |(Labellings.rootSum ({x₁, x₂, x₃, x₄} : Finset F) : ℝ)| ≤
      3 * Real.sqrt (Fintype.card F) := by
    have := hW {x₁, x₂, x₃, x₄} (insert_nonempty _ _)
    rw [rootMarginal_card_four h12 h13 h14 h23 h24 h34] at this
    norm_num at this
    exact this
  rw [hsplit]
  push_cast
  have a1 := w3 h12 h13 h23
  have a2 := w3 h12 h14 h24
  have a3 := w3 h13 h14 h34
  have a4 := w3 h23 h24 h34
  calc _ ≤ |(Labellings.rootSum ({x₁, x₂, x₃} : Finset F) : ℝ)| +
        |(Labellings.rootSum ({x₁, x₂, x₄} : Finset F) : ℝ)| +
        |(Labellings.rootSum ({x₁, x₃, x₄} : Finset F) : ℝ)| +
        |(Labellings.rootSum ({x₂, x₃, x₄} : Finset F) : ℝ)| +
        |(Labellings.rootSum ({x₁, x₂, x₃, x₄} : Finset F) : ℝ)| := by
        have e1 := abs_add_le ((Labellings.rootSum ({x₁, x₂, x₃} : Finset F) : ℝ) +
          (Labellings.rootSum ({x₁, x₂, x₄} : Finset F) : ℝ) -
          (Labellings.rootSum ({x₁, x₃, x₄} : Finset F) : ℝ) -
          (Labellings.rootSum ({x₂, x₃, x₄} : Finset F) : ℝ))
          (Labellings.rootSum ({x₁, x₂, x₃, x₄} : Finset F) : ℝ)
        have e2 := abs_sub ((Labellings.rootSum ({x₁, x₂, x₃} : Finset F) : ℝ) +
          (Labellings.rootSum ({x₁, x₂, x₄} : Finset F) : ℝ) -
          (Labellings.rootSum ({x₁, x₃, x₄} : Finset F) : ℝ))
          (Labellings.rootSum ({x₂, x₃, x₄} : Finset F) : ℝ)
        have e3 := abs_sub ((Labellings.rootSum ({x₁, x₂, x₃} : Finset F) : ℝ) +
          (Labellings.rootSum ({x₁, x₂, x₄} : Finset F) : ℝ))
          (Labellings.rootSum ({x₁, x₃, x₄} : Finset F) : ℝ)
        have e4 := abs_add_le (Labellings.rootSum ({x₁, x₂, x₃} : Finset F) : ℝ)
          (Labellings.rootSum ({x₁, x₂, x₄} : Finset F) : ℝ)
        linarith
    _ ≤ 11 * Real.sqrt (Fintype.card F) := by linarith


/-- **`lem:record:root-marginal`(ii), second bound, with the soft count and the Weil bound
discharged.** Over a finite field `F` with `q = |F|`, `χ(-1) = -1` and H1
(`Labellings.WeilBound F`, `thm:weil`): if every half configuration `y` carries four distinct
admissible labels `x(y)` and `n(y) = |signed neighbourhood of x(y)| - n₁(y)`, `n₁ ∈ {0,1,2}`,
then the hypotheses `hWeil` and `hn` of `rootMarginal_ii_second` hold with `𝒲 = softW ∘ x`, and
`χ_p ≤ D_full²/L_low²` follows from the remaining **hypotheses** (`hmom`, `hs`). -/
theorem rootMarginal_ii_second_of_labels (hF : ringChar F ≠ 2)
    (hm : quadraticChar F (-1) = -1) (hW : Labellings.WeilBound F)
    {S : Type*} [Fintype S] (μ : FiniteLaw S) (hpos : ∀ y, 0 < μ.weight y) {q r : ℝ}
    (hqp : q = 1 / (Fintype.card F : ℝ)) (hr : r * Real.sqrt (Fintype.card F) = 1)
    (hlow : LowerFactors q r) (x₁ x₂ x₃ x₄ : S → F)
    (hd : ∀ y, x₁ y ≠ x₂ y ∧ x₁ y ≠ x₃ y ∧ x₁ y ≠ x₄ y ∧ x₂ y ≠ x₃ y ∧ x₂ y ≠ x₄ y ∧
      x₃ y ≠ x₄ y)
    (hadm : ∀ y, quadraticChar F (x₃ y - x₁ y) = 1 ∧ quadraticChar F (x₄ y - x₁ y) = 1 ∧
      quadraticChar F (x₃ y - x₂ y) = 1)
    (n₁ n s : S → ℝ) (hn₁ : ∀ y, n₁ y = 0 ∨ n₁ y = 1 ∨ n₁ y = 2)
    (hn : ∀ y, n y = ((signedNbhd (x₁ y) (x₂ y) (x₃ y) (x₄ y)).card : ℝ) - n₁ y)
    (hmom : μ.expect (fun y => ((softW (x₁ y) (x₂ y) (x₃ y) (x₄ y) : ℝ) /
      (Fintype.card F : ℝ)) ^ 2) ≤ (5 * q + 34 * q * r + 11 * q ^ 3) / Z4 q)
    (hs : ∀ y, (1 - 24 * aP q r) * (n y * (n y - 1) / ((Fintype.card F : ℝ) / 16) ^ 2) ≤ s y ∧
      s y ≤ n y * (n y - 1) / ((Fintype.card F : ℝ) / 16) ^ 2) :
    chiSq (fun y => μ.weight y * s y / ∑ z, μ.weight z * s z) μ.weight ≤
      Dfull q r ^ 2 / Llow q r ^ 2 := by
  have hp : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  refine rootMarginal_ii_second μ hpos hp hqp hr hlow
    (fun y => (softW (x₁ y) (x₂ y) (x₃ y) (x₄ y) : ℝ)) n₁ n s ?_ hn₁ ?_ hmom hs
  · intro y
    obtain ⟨h12, h13, h14, h23, h24, h34⟩ := hd y
    exact rootMarginal_softW_weil hW h12 h13 h14 h23 h24 h34
  · intro y
    obtain ⟨h12, h13, h14, h23, h24, h34⟩ := hd y
    obtain ⟨a13, a14, a23⟩ := hadm y
    rw [hn y, rootMarginal_signedNbhd_card hF hm h12 h13 h14 h23 h24 h34 a13 a14 a23]

end SoftCount

/-! ### The odd and even components: the per-label bound and the union bound -/

/-- **The union bound of the even-component step** (proof of `lem:record:root-marginal`(ii)):
if under the uniform law on a finite set `O` each of `k` coordinates takes any given value with
probability at most `𝔞`, then the elements whose `k` coordinates avoid a set `T` of at most `t`
values form a fraction at least `1 - k t 𝔞` of `O` (in the paper `k = 4`, `t = 6`). -/
theorem rootMarginal_union_bound {Ω V : Type*} [DecidableEq Ω] [DecidableEq V] (O : Finset Ω)
    {k : ℕ} (f : Fin k → Ω → V) (T : Finset V) {t : ℕ} (hT : T.card ≤ t) {a : ℝ}
    (hprob : ∀ i v, ((O.filter fun o => f i o = v).card : ℝ) ≤ a * O.card) :
    (1 - k * t * a) * O.card ≤ (O.filter fun o => ∀ i, f i o ∉ T).card := by
  have hsplit : (O.filter fun o => ∀ i, f i o ∉ T).card +
      (O.filter fun o => ¬ ∀ i, f i o ∉ T).card = O.card :=
    card_filter_add_card_filter_not _
  have hbad : (O.filter fun o => ¬ ∀ i, f i o ∉ T) ⊆
      (univ : Finset (Fin k)).biUnion fun i => T.biUnion fun v => O.filter fun o => f i o = v := by
    intro o ho
    rw [mem_filter] at ho
    push Not at ho
    obtain ⟨i, hi⟩ := ho.2
    rw [mem_biUnion]
    refine ⟨i, mem_univ i, ?_⟩
    rw [mem_biUnion]
    exact ⟨f i o, hi, by rw [mem_filter]; exact ⟨ho.1, rfl⟩⟩
  have hcard := card_le_card hbad
  have hU : (((univ : Finset (Fin k)).biUnion fun i =>
      T.biUnion fun v => O.filter fun o => f i o = v).card : ℝ) ≤ k * t * (a * O.card) := by
    have h1 := card_biUnion_le (s := (univ : Finset (Fin k)))
      (t := fun i => T.biUnion fun v => O.filter fun o => f i o = v)
    have h2 : ∀ i, ((T.biUnion fun v => O.filter fun o => f i o = v).card : ℝ) ≤
        t * (a * O.card) := by
      intro i
      have h3 := card_biUnion_le (s := T) (t := fun v => O.filter fun o => f i o = v)
      have h4 : (∑ v ∈ T, ((O.filter fun o => f i o = v).card : ℝ)) ≤ T.card * (a * O.card) := by
        have := sum_le_sum (s := T) fun v _ => hprob i v
        rwa [sum_const, nsmul_eq_mul] at this
      have h5 : (T.card : ℝ) * (a * O.card) ≤ t * (a * O.card) := by
        have ha : 0 ≤ a * O.card := by
          by_cases hO : O.card = 0
          · rw [hO, Nat.cast_zero, mul_zero]
          · obtain ⟨o, -⟩ := card_ne_zero.mp hO
            exact le_trans (Nat.cast_nonneg _) (hprob i (f i o))
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT) ha
      calc ((T.biUnion fun v => O.filter fun o => f i o = v).card : ℝ)
          ≤ ∑ v ∈ T, ((O.filter fun o => f i o = v).card : ℝ) := by exact_mod_cast h3
        _ ≤ _ := h4.trans h5
    calc _ ≤ (∑ i, ((T.biUnion fun v => O.filter fun o => f i o = v).card : ℝ)) := by
          exact_mod_cast h1
      _ ≤ ∑ _i : Fin k, (t : ℝ) * (a * O.card) := sum_le_sum fun i _ => h2 i
      _ = k * t * (a * O.card) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hsplit' : ((O.filter fun o => ∀ i, f i o ∉ T).card : ℝ) +
      ((O.filter fun o => ¬ ∀ i, f i o ∉ T).card : ℝ) = O.card := by exact_mod_cast hsplit
  have hcard' : ((O.filter fun o => ¬ ∀ i, f i o ∉ T).card : ℝ) ≤
      (((univ : Finset (Fin k)).biUnion fun i =>
        T.biUnion fun v => O.filter fun o => f i o = v).card : ℝ) := by exact_mod_cast hcard
  nlinarith

/-- **The per-label probability bound of the odd component** (proof of
`lem:record:root-marginal`(ii)): if `|𝒪| ≥ k_p(k_p-1)(p/16)²(1-υ₋)(1-υ₋-16q)` and a prescribed value
of one free odd label is taken by at most `(k_p-1)(p/16)²(1+υ₊)²` elements of `𝒪` (both
**hypotheses**, from `lem:record:signed-nbhd` and `lem:paley-triple`(a)), with `k_p = (p-3)/4`,
then that probability is at most `𝔞_p`, since `1/k_p = 4q/(1-3q)`. -/
theorem rootMarginal_prob_le_aP {p q r k Z cnt : ℝ} (hp : 0 < p) (hq : q = 1 / p)
    (hk : 4 * k = p - 3) (hr : 0 ≤ r) (h1 : 0 < 1 - upsTimes q r - 16 * q)
    (hZ : k * (k - 1) * (p / 16) ^ 2 * ((1 - upsMinus q r) * (1 - upsMinus q r - 16 * q)) ≤ Z)
    (hcnt : cnt ≤ (k - 1) * (p / 16) ^ 2 * (1 + upsPlus q r) ^ 2) :
    cnt ≤ aP q r * Z := by
  have hq0 : 0 < q := by rw [hq]; positivity
  obtain ⟨d1, d2, d3, -, -, -, -⟩ := rootMarginal_denoms_pos hq0 hr h1
  have ha := rootMarginal_aP_nonneg hq0 hr h1
  have hkq : k = (1 - 3 * q) / (4 * q) := by
    rw [hq]
    field_simp
    linarith
  have hid : aP q r * (k * ((1 - upsMinus q r) * (1 - upsMinus q r - 16 * q))) =
      (1 + upsPlus q r) ^ 2 := by
    unfold aP
    rw [hkq]
    have n1 : 1 - 3 * q ≠ 0 := d1.ne'
    have n2 : 1 - upsMinus q r ≠ 0 := d2.ne'
    have n3 : 1 - upsMinus q r - 16 * q ≠ 0 := d3.ne'
    have n4 : q ≠ 0 := hq0.ne'
    rw [div_mul_div_comm, mul_assoc, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_eq_iff (by positivity)]
    field_simp
  calc cnt ≤ (k - 1) * (p / 16) ^ 2 * (1 + upsPlus q r) ^ 2 := hcnt
    _ = aP q r * (k * (k - 1) * (p / 16) ^ 2 *
          ((1 - upsMinus q r) * (1 - upsMinus q r - 16 * q))) := by
        rw [← hid]
        ring
    _ ≤ aP q r * Z := mul_le_mul_of_nonneg_left hZ ha


end RootMarginal

end Sarkozy.Variance
