module

public import Sarkozy.TraceMixing.PaleySquare

/-!
# Accepting two-layer constants (`lem:record:accepting-c2`)

`paper/sections/21_middle_records.tex`, `subsec:merge-repair`, `lem:record:accepting-c2`.

The single object of a two-layer constant record of a middle block has, at a prime `p` and at
the reserved cut, the labels `(a, b)` (layers `0` and `1`); they are uniform ordered distinct
labels. The comparison law replaces this law by the uniform strict Paley edge `a → b`
(`χ(b - a) = 1`), independently at every prime.

## One prime (exact, over any finite field `F` with `q ≡ 3 (mod 4)` elements)

* `pairOp`, the Markov operator `(D f)(a) = E[f(b) | a] = (∑_{b ≠ a} f b)/(q - 1)` of the source
  law (`pairOp_eq_sum_erase`); `pairOp_const` (`D 1 = 1`), `pairOp_meanZero` (`D = -η I` on the
  mean-zero functions, `η = 1/(q - 1)`), so `D = J - η(I - J)`.
* `edgeOp`, the Markov operator `(P f)(a) = (2/(q - 1)) ∑_{b : a → b} f b` of the replacement;
  `edgeOp_eq`: **`P = D + (q/(q - 1)) K`** with `K = paleyOp`, `(K f)(a) = E_b χ(b - a) f(b)`;
  `edgeOp_const` (`P 1 = 1`); the endpoint marginals are uniform (`edge_out_degree`,
  `edge_in_degree`: every label has `(q - 1)/2` out- and in-neighbours); the law is invariant
  under the square-affine maps (`edge_affine`) and accepts the query `a → b` by definition.
* The difference `P - D = (q/(q - 1)) K` (`edgeOp_sub_pairOp`) is **purely skew**
  (`diff_skew`, `diff_sym_zero`: its symmetric part vanishes on all of `L²`), annihilates the
  constants (`diff_const`) and on the mean-zero functions has
  **`‖(P - D) f‖² = γ_q² ‖f‖²`, `γ_q = √q/(q - 1)`** (`diff_norm_sq`). The centred operators have
  `‖D f‖² = η² ‖f‖²` and `‖P f‖² = ρ_q² ‖f‖²`, `ρ_q = √(q + 1)/(q - 1)` (`pairOp_norm_sq`,
  `edgeOp_norm_sq`). Norms are the counting `ℓ²` sums `∑_a f(a)²`, which are the uniform-law
  `L²` norms up to the common factor `1/q`.

## The real inequalities (`b ≥ 7`)

With `η_b = 1/(b - 1)`, `γ_b = √b/(b - 1)`, `ρ_b = √(b + 1)/(b - 1)` (functions `etaC`, `gamC`,
`rhoC` of a real `b`, `√` = `Real.sqrt`, and `(b + 1)^{3/2}` written `(b + 1) √(b + 1)`):
`three_halves_le` (`(b + 1)^{3/2} + 1 ≤ b(b - 1)`), `rho_cube_add_eta_cube_le`
(`ρ_b³ + η_b³ ≤ γ_b²`), `rho_sq_le_gam` (`ρ_b² ≤ γ_b`), `gam_eq` (`γ_b = r/(1 - 1/b)` for
`r = (√b)⁻¹ = b^{-1/2}`, `rpow_neg_half`), the monotonicity in the prime (`etaC_anti`, `gamC_anti`,
`rhoC_anti`), and `rhoC_le_one`, `etaC_le_one`.

## The block, and the prices

The exact-support (sector) decomposition of the block difference over the primes of the block
(`lem:sector`(a), (b), (h)) is **taken as a hypothesis**, `ConstantSectorBounds`: the block norms
are at most every common bound of the sector norms, and the sector norms are bounded as in the
paper's proof (singletons: symmetric `0`, skew `γ_p`; two primes: symmetric `γ_p γ_{p'}`; size
`≥ 2`: skew `∏ ρ_p`; size `≥ 3`: symmetric `∏ ρ_p + ∏ η_p`). From it, `block_bounds` proves the
whole-block norms `≤ γ_b² = r²/(1 - 1/b)²` (symmetric) and `≤ γ_b = r/(1 - 1/b)` (skew), without a
factor for the number of primes; the singleton sector bounds are the one-prime theorems above.
`accepting_c2_prices`: two records of mass `w_C r³` each give the symmetric and skew prices
`2 w_C/(1 - 1/X)² r⁵ q_𝔅^{2a}` and `2 w_C/(1 - 1/X) r⁴ q_𝔅^{2a}` (charging rule
`rem:cp:charging`(ii); the prices are `mass × norm × sel`).
`constantSectorBounds_toy` is a non-vacuity instance of the bundle.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleRecords

open Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer. -/
local notation "χ" => quadraticChar F

/-- `q = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

omit [Field F] [DecidableEq F] in
theorem card_ge_three (h3 : Fintype.card F % 4 = 3) : (3 : ℝ) ≤ qF := by
  have : 3 ≤ Fintype.card F := by omega
  exact_mod_cast this

/-! ## The source law and its Markov operator -/

/-- **The source operator** (`lem:record:accepting-c2`): the Markov operator
`(D f)(a) = E[f(b) | a]` of the uniform law of ordered distinct labels, written
`(∑_b f b - f a)/(q - 1)`. -/
noncomputable def pairOp (f : F → ℝ) (a : F) : ℝ :=
  (qF - 1)⁻¹ * (∑ b, f b - f a)

omit [Field F] in
theorem pairOp_eq_sum_erase (f : F → ℝ) (a : F) :
    pairOp f a = (qF - 1)⁻¹ * ∑ b ∈ univ.erase a, f b := by
  unfold pairOp
  rw [sum_erase_eq_sub (mem_univ a)]

omit [Field F] [DecidableEq F] in
/-- `D 1 = 1`. -/
theorem pairOp_const (h3 : Fintype.card F % 4 = 3) (c : ℝ) (a : F) :
    pairOp (fun _ => c) a = c := by
  have hq := card_ge_three h3
  have hq1 : qF - 1 ≠ 0 := by linarith
  unfold pairOp
  rw [sum_const, card_univ, nsmul_eq_mul]
  field_simp

omit [Field F] [DecidableEq F] in
/-- **`D = -η I` on the mean-zero functions**, `η = 1/(q - 1)`. -/
theorem pairOp_meanZero (f : F → ℝ) (hf : ∑ b, f b = 0) (a : F) :
    pairOp f a = -((qF - 1)⁻¹ * f a) := by
  unfold pairOp
  rw [hf]
  ring

/-! ## The strict Paley edge law and its Markov operator -/

/-- **The replacement operator**: the Markov operator `(P f)(a) = E[f(b) | a]` of the uniform
strict Paley edge `a → b`, `(P f)(a) = (2/(q - 1)) ∑_{b : χ(b - a) = 1} f b`. -/
noncomputable def edgeOp (f : F → ℝ) (a : F) : ℝ :=
  2 * (qF - 1)⁻¹ * ∑ b ∈ univ.filter (fun b => χ (b - a) = 1), f b

/-- `2 ∑_{a → b} f b = ∑_{b ≠ a} f b + ∑_b χ(b - a) f b`. -/
theorem two_mul_edgeSum (f : F → ℝ) (a : F) :
    2 * ∑ b ∈ univ.filter (fun b => χ (b - a) = 1), f b =
      (∑ b, f b - f a) + ∑ b, (χ (b - a) : ℝ) * f b := by
  rw [Finset.sum_filter, Finset.mul_sum]
  have hpt : ∀ b, 2 * (if χ (b - a) = 1 then f b else 0) =
      (f b - if b = a then f b else 0) + (χ (b - a) : ℝ) * f b := by
    intro b
    by_cases hb : b = a
    · subst hb
      simp only [sub_self, quadraticChar_zero, zero_ne_one, ↓reduceIte, mul_zero,
        Int.cast_zero, zero_mul, add_zero]
    · rcases quadraticChar_dichotomy (sub_ne_zero.mpr hb) with h | h
      · simp only [h, ↓reduceIte, hb, sub_zero, Int.cast_one, one_mul]
        ring
      · have hne : (-1 : ℤ) ≠ 1 := by norm_num
        simp only [h, hne, ↓reduceIte, hb, sub_zero, Int.cast_neg, Int.cast_one, neg_mul,
          one_mul, mul_zero]
        ring
  rw [Finset.sum_congr rfl (fun b _ => hpt b), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' univ a f]
  simp only [mem_univ, ↓reduceIte]

/-- **`P = D + (q/(q - 1)) K`**, `K = paleyOp`, `(K f)(a) = E_b χ(b - a) f(b)`. -/
theorem edgeOp_eq (h3 : Fintype.card F % 4 = 3) (f : F → ℝ) (a : F) :
    edgeOp f a = pairOp f a + qF / (qF - 1) * paleyOp f a := by
  have hq := card_ge_three h3
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  unfold edgeOp pairOp paleyOp
  have e : 2 * (qF - 1)⁻¹ * ∑ b ∈ univ.filter (fun b => χ (b - a) = 1), f b =
      (qF - 1)⁻¹ * (2 * ∑ b ∈ univ.filter (fun b => χ (b - a) = 1), f b) := by ring
  rw [e, two_mul_edgeSum f a]
  field_simp

/-- `P 1 = 1`. -/
theorem edgeOp_const (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (c : ℝ) (a : F) :
    edgeOp (fun _ => c) a = c := by
  rw [edgeOp_eq h3, pairOp_const h3, paleyOp_const hF, mul_zero, add_zero]

/-- **Uniform first endpoint**: every label has `(q - 1)/2` out-neighbours. -/
theorem edge_out_degree (hF : ringChar F ≠ 2) (a : F) :
    2 * ((univ.filter fun b => χ (b - a) = 1).card : ℤ) = Fintype.card F - 1 :=
  card_out hF a

/-- **Uniform second endpoint**: every label has `(q - 1)/2` in-neighbours. -/
theorem edge_in_degree (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (b : F) :
    2 * ((univ.filter fun a => χ (b - a) = 1).card : ℤ) = Fintype.card F - 1 :=
  card_in hF h3 b

/-- **Square-affine invariance** of the strict Paley edge: for a nonzero square `α`,
`(a, b) ↦ (α a + β, α b + β)` preserves the relation `a → b`. -/
theorem edge_affine {α : F} (hα : χ α = 1) (β a b : F) :
    χ ((α * b + β) - (α * a + β)) = χ (b - a) := by
  have : (α * b + β) - (α * a + β) = α * (b - a) := by ring
  rw [this, map_mul, hα, one_mul]

/-! ## The difference -/

/-- `P - D = (q/(q - 1)) K`. -/
theorem edgeOp_sub_pairOp (h3 : Fintype.card F % 4 = 3) (f : F → ℝ) (a : F) :
    edgeOp f a - pairOp f a = qF / (qF - 1) * paleyOp f a := by
  rw [edgeOp_eq h3]
  ring

/-- The difference annihilates the constants. -/
theorem diff_const (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (c : ℝ) (a : F) :
    edgeOp (fun _ => c) a - pairOp (fun _ => c) a = 0 := by
  rw [edgeOp_sub_pairOp h3, paleyOp_const hF, mul_zero]

/-- **The difference is purely skew**: `⟨(P - D) f, g⟩ = -⟨f, (P - D) g⟩` for all `f, g`. -/
theorem diff_skew (h3 : Fintype.card F % 4 = 3) (f g : F → ℝ) :
    ∑ a, (edgeOp f a - pairOp f a) * g a = -∑ a, f a * (edgeOp g a - pairOp g a) := by
  simp only [edgeOp_sub_pairOp h3]
  have h := paleyOp_adjoint h3 f g
  have e1 : ∑ a, qF / (qF - 1) * paleyOp f a * g a = qF / (qF - 1) * ∑ a, paleyOp f a * g a := by
    rw [Finset.mul_sum]
    exact sum_congr rfl fun a _ => by ring
  have e2 : ∑ a, f a * (qF / (qF - 1) * paleyOp g a) = qF / (qF - 1) * ∑ a, f a * paleyOp g a := by
    rw [Finset.mul_sum]
    exact sum_congr rfl fun a _ => by ring
  rw [e1, e2, h]
  ring

/-- **The symmetric part of the difference vanishes**: `⟨(P - D) f, f⟩ = 0`. -/
theorem diff_sym_zero (h3 : Fintype.card F % 4 = 3) (f : F → ℝ) :
    ∑ a, (edgeOp f a - pairOp f a) * f a = 0 := by
  have h := diff_skew h3 f f
  have e : ∑ a, f a * (edgeOp f a - pairOp f a) = ∑ a, (edgeOp f a - pairOp f a) * f a :=
    sum_congr rfl fun a _ => by ring
  rw [e] at h
  linarith

/-- `∑_s (K h)(s)² = q⁻¹ ∑_s h(s)²` on the mean-zero functions. -/
theorem paleyOp_norm_sq_meanZero (hF : ringChar F ≠ 2) (h : F → ℝ) (hh : ∑ s, h s = 0) :
    ∑ s, paleyOp h s ^ 2 = qF⁻¹ * ∑ s, h s ^ 2 := by
  have hq0 : qF ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have := norm_paleyOp hF h
  rw [hh, mul_zero] at this
  have h2 : qF⁻¹ * ∑ s, paleyOp h s ^ 2 = qF⁻¹ * (qF⁻¹ * ∑ s, h s ^ 2) := by
    rw [this]
    ring
  have hinv : qF⁻¹ ≠ 0 := inv_ne_zero hq0
  exact mul_left_cancel₀ hinv h2

/-- `∑_s h(s) (K h)(s) = 0`. -/
theorem paleyOp_form_self_zero (h3 : Fintype.card F % 4 = 3) (h : F → ℝ) :
    ∑ s, h s * paleyOp h s = 0 := by
  have := paleyOp_adjoint h3 h h
  have e : ∑ s, paleyOp h s * h s = ∑ s, h s * paleyOp h s := sum_congr rfl fun s _ => by ring
  rw [e] at this
  linarith

/-- **`‖(P - D) f‖² = γ_q² ‖f‖²` on the mean-zero functions**, `γ_q² = q/(q - 1)²`
(`γ_q = √q/(q - 1)`). -/
theorem diff_norm_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (f : F → ℝ)
    (hf : ∑ a, f a = 0) :
    ∑ a, (edgeOp f a - pairOp f a) ^ 2 = qF / (qF - 1) ^ 2 * ∑ a, f a ^ 2 := by
  have hq := card_ge_three h3
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  simp only [edgeOp_sub_pairOp h3, mul_pow]
  rw [← Finset.mul_sum, paleyOp_norm_sq_meanZero hF f hf]
  field_simp

omit [Field F] [DecidableEq F] in
/-- `‖D f‖² = η² ‖f‖²` on the mean-zero functions. -/
theorem pairOp_norm_sq (f : F → ℝ) (hf : ∑ a, f a = 0) :
    ∑ a, pairOp f a ^ 2 = ((qF - 1)⁻¹) ^ 2 * ∑ a, f a ^ 2 := by
  simp only [pairOp_meanZero f hf, neg_sq, mul_pow]
  rw [← Finset.mul_sum]

/-- **`‖P f‖² = ρ_q² ‖f‖²` on the mean-zero functions**, `ρ_q² = (q + 1)/(q - 1)²`. -/
theorem edgeOp_norm_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (f : F → ℝ)
    (hf : ∑ a, f a = 0) :
    ∑ a, edgeOp f a ^ 2 = (qF + 1) / (qF - 1) ^ 2 * ∑ a, f a ^ 2 := by
  have hq := card_ge_three h3
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hexp : ∀ a, edgeOp f a ^ 2 = ((qF - 1)⁻¹) ^ 2 * f a ^ 2 -
      2 * ((qF - 1)⁻¹ * (qF / (qF - 1))) * (f a * paleyOp f a) +
        (qF / (qF - 1)) ^ 2 * paleyOp f a ^ 2 := by
    intro a
    rw [edgeOp_eq h3, pairOp_meanZero f hf]
    ring
  simp only [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, paleyOp_form_self_zero h3 f, paleyOp_norm_sq_meanZero hF f hf]
  field_simp
  ring

/-- **`(P - D)² = -γ_q² I` on the mean-zero functions**: with `diff_skew` and `diff_norm_sq`, the
real form of "the eigenvalues of `P - D` on a nonconstant Fourier mode are `± i γ_q`". -/
theorem diff_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (f : F → ℝ)
    (hf : ∑ a, f a = 0) (a : F) :
    edgeOp (fun b => edgeOp f b - pairOp f b) a - pairOp (fun b => edgeOp f b - pairOp f b) a =
      -(qF / (qF - 1) ^ 2) * f a := by
  have hq := card_ge_three h3
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  rw [edgeOp_sub_pairOp h3]
  simp only [edgeOp_sub_pairOp h3]
  have hlin : paleyOp (fun b => qF / (qF - 1) * paleyOp f b) a =
      qF / (qF - 1) * paleyOp (paleyOp f) a := by
    unfold paleyOp
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hlin, paleyOp_sq hF h3 f hf a]
  field_simp

/-- **The symmetric part of the replacement on the mean-zero functions is `-η I`**:
`⟨P f, f⟩ = -η ‖f‖²` (and `⟨D f, f⟩ = -η ‖f‖²`), so `P° = -η I + (skew part of norm γ_q)`. -/
theorem edgeOp_form_meanZero (h3 : Fintype.card F % 4 = 3) (f : F → ℝ) (hf : ∑ a, f a = 0) :
    ∑ a, edgeOp f a * f a = -((qF - 1)⁻¹ * ∑ a, f a ^ 2) := by
  have h := diff_sym_zero h3 f
  have e : ∑ a, edgeOp f a * f a = ∑ a, (edgeOp f a - pairOp f a) * f a +
      ∑ a, pairOp f a * f a := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e, h, zero_add]
  simp only [pairOp_meanZero f hf]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-! ## The real inequalities -/

/-- `η_b = 1/(b - 1)`. -/
noncomputable def etaC (b : ℝ) : ℝ := 1 / (b - 1)

/-- `γ_b = √b/(b - 1)`. -/
noncomputable def gamC (b : ℝ) : ℝ := Real.sqrt b / (b - 1)

/-- `ρ_b = √(b + 1)/(b - 1)`. -/
noncomputable def rhoC (b : ℝ) : ℝ := Real.sqrt (b + 1) / (b - 1)

/-- **`(b + 1)^{3/2} + 1 ≤ b(b - 1)` for `b ≥ 7`**, with `(b + 1)^{3/2} = (b + 1)√(b + 1)`. -/
theorem three_halves_le {b : ℝ} (hb : 7 ≤ b) :
    (b + 1) * Real.sqrt (b + 1) + 1 ≤ b * (b - 1) := by
  have hs := Real.sqrt_nonneg (b + 1)
  have hss : Real.sqrt (b + 1) ^ 2 = b + 1 := Real.sq_sqrt (by linarith)
  have hy : 0 ≤ b * (b - 1) - 1 := by nlinarith
  have hcube : ((b + 1) * Real.sqrt (b + 1)) ^ 2 ≤ (b * (b - 1) - 1) ^ 2 := by
    have : ((b + 1) * Real.sqrt (b + 1)) ^ 2 = (b + 1) ^ 3 := by
      rw [mul_pow, hss]
      ring
    rw [this]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ b) (by linarith : (0 : ℝ) ≤ b))
      (by linarith : (0 : ℝ) ≤ b - 7)]
  have hx : 0 ≤ (b + 1) * Real.sqrt (b + 1) := mul_nonneg (by linarith) hs
  have := (pow_le_pow_iff_left₀ hx hy (by norm_num : (2 : ℕ) ≠ 0)).mp hcube
  linarith

/-- **`ρ_b³ + η_b³ ≤ γ_b²` for `b ≥ 7`.** -/
theorem rho_cube_add_eta_cube_le {b : ℝ} (hb : 7 ≤ b) :
    rhoC b ^ 3 + etaC b ^ 3 ≤ gamC b ^ 2 := by
  have h1 : 0 < b - 1 := by linarith
  have hss : Real.sqrt (b + 1) ^ 2 = b + 1 := Real.sq_sqrt (by linarith)
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)
  have key := three_halves_le hb
  have e1 : rhoC b ^ 3 + etaC b ^ 3 = ((b + 1) * Real.sqrt (b + 1) + 1) / (b - 1) ^ 3 := by
    have : Real.sqrt (b + 1) ^ 3 = (b + 1) * Real.sqrt (b + 1) := by
      rw [pow_succ, hss]
    unfold rhoC etaC
    rw [div_pow, div_pow, one_pow, ← add_div, this]
  have e2 : gamC b ^ 2 = b * (b - 1) / (b - 1) ^ 3 := by
    unfold gamC
    rw [div_pow, hsb]
    field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right key (by positivity)

/-- **`ρ_b² ≤ γ_b` for `b ≥ 7`.** -/
theorem rho_sq_le_gam {b : ℝ} (hb : 7 ≤ b) : rhoC b ^ 2 ≤ gamC b := by
  have h1 : 0 < b - 1 := by linarith
  have hss : Real.sqrt (b + 1) ^ 2 = b + 1 := Real.sq_sqrt (by linarith)
  have hs2 : 2 ≤ Real.sqrt b := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  unfold rhoC gamC
  rw [div_pow, hss, div_le_div_iff₀ (by positivity) h1]
  nlinarith

theorem rhoC_nonneg {b : ℝ} (hb : 1 < b) : 0 ≤ rhoC b :=
  div_nonneg (Real.sqrt_nonneg _) (by linarith)

theorem etaC_nonneg {b : ℝ} (hb : 1 < b) : 0 ≤ etaC b :=
  div_nonneg zero_le_one (by linarith)

theorem gamC_nonneg {b : ℝ} (hb : 1 < b) : 0 ≤ gamC b :=
  div_nonneg (Real.sqrt_nonneg _) (by linarith)

/-- `ρ_b ≤ 1` for `b ≥ 3`. -/
theorem rhoC_le_one {b : ℝ} (hb : 3 ≤ b) : rhoC b ≤ 1 := by
  unfold rhoC
  rw [div_le_one (by linarith)]
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

/-- `η_b ≤ 1` for `b ≥ 2`. -/
theorem etaC_le_one {b : ℝ} (hb : 2 ≤ b) : etaC b ≤ 1 := by
  unfold etaC
  rw [div_le_one (by linarith)]
  linarith

/-- `η` decreases in the prime. -/
theorem etaC_anti {b p : ℝ} (hb : 1 < b) (hbp : b ≤ p) : etaC p ≤ etaC b := by
  unfold etaC
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- `γ` decreases in the prime (`b ≥ 1`). -/
theorem gamC_anti {b p : ℝ} (hb : 1 < b) (hbp : b ≤ p) : gamC p ≤ gamC b := by
  have hp : 1 < p := lt_of_lt_of_le hb hbp
  unfold gamC
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  set s := Real.sqrt p
  set t := Real.sqrt b
  have hs : s ^ 2 = p := Real.sq_sqrt (by linarith)
  have ht : t ^ 2 = b := Real.sq_sqrt (by linarith)
  have hts : t ≤ s := Real.sqrt_le_sqrt hbp
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  -- s (t² - 1) ≤ t (s² - 1) ⟺ (t - s)(s t + 1) ≤ 0
  rw [← hs, ← ht]
  nlinarith [mul_nonneg (sub_nonneg.mpr hts) (add_nonneg (mul_nonneg (le_trans ht0 hts) ht0)
    zero_le_one)]

/-- `ρ` decreases in the prime. -/
theorem rhoC_anti {b p : ℝ} (hb : 1 < b) (hbp : b ≤ p) : rhoC p ≤ rhoC b := by
  have hp : 1 < p := lt_of_lt_of_le hb hbp
  have h1 : 0 ≤ rhoC p := rhoC_nonneg hp
  have h2 : 0 ≤ rhoC b := rhoC_nonneg hb
  have hsq : rhoC p ^ 2 ≤ rhoC b ^ 2 := by
    unfold rhoC
    rw [div_pow, div_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith),
      div_le_div_iff₀ (by positivity) (by positivity)]
    -- (b + 1)(p - 1)² - (p + 1)(b - 1)² = (p - b)(b p + p + b - 3)
    nlinarith [mul_nonneg (sub_nonneg.mpr hbp)
      (by nlinarith : (0 : ℝ) ≤ b * p + p + b - 3)]
  exact (pow_le_pow_iff_left₀ h1 h2 (by norm_num : (2 : ℕ) ≠ 0)).mp hsq

/-- `b^{-1/2} = (√b)⁻¹`. -/
theorem rpow_neg_half {b : ℝ} (hb : 0 ≤ b) : b ^ (-(1 / 2 : ℝ)) = (Real.sqrt b)⁻¹ := by
  rw [Real.rpow_neg hb, Real.sqrt_eq_rpow]

/-- **`γ_b = r/(1 - 1/b)`** for `r = (√b)⁻¹ = b^{-1/2}`. -/
theorem gam_eq {b : ℝ} (hb : 1 < b) : gamC b = (Real.sqrt b)⁻¹ / (1 - 1 / b) := by
  have hb0 : 0 < b := by linarith
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
  have hss : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have h1 : b - 1 ≠ 0 := by linarith
  unfold gamC
  rw [one_sub_div hb0.ne']
  field_simp
  rw [hss]

/-- **`γ_b² = r²/(1 - 1/b)²`** for `r = (√b)⁻¹`. -/
theorem gam_sq_eq {b : ℝ} (hb : 1 < b) :
    gamC b ^ 2 = ((Real.sqrt b)⁻¹) ^ 2 / (1 - 1 / b) ^ 2 := by
  rw [gam_eq hb, div_pow]

/-! ## The block (sector decomposition as a hypothesis) -/

/-- **The exact-support decomposition of the block difference** (`lem:record:accepting-c2`, the
paragraph "These exact-support bounds…", with `lem:sector`(a), (b), (h)), **taken as a
hypothesis**. For a block whose primes `S` are all `≥ b`, `symN`, `skewN` are the symmetric and
skew norms of the block difference `⊗_p P_p - ⊗_p D_p`, and `symSec T`, `skewSec T` those of its
restriction to the sector of exact support `T ⊆ S`, `T ≠ ∅` (the constants cancel). The fields
are: the sectors are orthogonal and invariant, so the block norms are at most every common bound
of the sector norms (`sym_le`, `skew_le`); and the sector norms satisfy the bounds of the paper's
proof (on a singleton the difference is purely skew of norm `γ_p` — proved at one prime by
`diff_sym_zero`, `diff_norm_sq`; on two primes the symmetric part is `± γ_p γ_{p'}`; on `≥ 2`
primes the skew part is that of `⊗ P°` (the source is self-adjoint), of norm `∏ ρ_p`; on `≥ 3`
primes the symmetric part has norm at most `∏ ρ_p + ∏ η_p`). -/
structure ConstantSectorBounds (S : Finset ℝ) where
  symN : ℝ
  skewN : ℝ
  symSec : Finset ℝ → ℝ
  skewSec : Finset ℝ → ℝ
  sym_le : ∀ M : ℝ, 0 ≤ M → (∀ T ⊆ S, T.Nonempty → symSec T ≤ M) → symN ≤ M
  skew_le : ∀ M : ℝ, 0 ≤ M → (∀ T ⊆ S, T.Nonempty → skewSec T ≤ M) → skewN ≤ M
  sym_one : ∀ p ∈ S, symSec {p} ≤ 0
  skew_one : ∀ p ∈ S, skewSec {p} ≤ gamC p
  sym_two : ∀ T ⊆ S, T.card = 2 → symSec T ≤ ∏ p ∈ T, gamC p
  skew_two : ∀ T ⊆ S, 2 ≤ T.card → skewSec T ≤ ∏ p ∈ T, rhoC p
  sym_three : ∀ T ⊆ S, 3 ≤ T.card → symSec T ≤ (∏ p ∈ T, rhoC p) + ∏ p ∈ T, etaC p

/-- `∏_{p ∈ T} f p ≤ f b ^ |T|` for `0 ≤ f p ≤ f b` on `T`. -/
theorem prod_le_pow_card {T : Finset ℝ} {f : ℝ → ℝ} {c : ℝ}
    (h0 : ∀ p ∈ T, 0 ≤ f p) (h1 : ∀ p ∈ T, f p ≤ c) : ∏ p ∈ T, f p ≤ c ^ T.card := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod₀ h0 h1

/-- **The whole-block norms** (`lem:record:accepting-c2`, second sentence): if every prime of the
block is at least `b ≥ 7`, the symmetric and skew norms of the replacement minus the source are at
most `γ_b² = r²/(1 - 1/b)²` and `γ_b = r/(1 - 1/b)`, `r = b^{-1/2}` (`gam_sq_eq`, `gam_eq`),
whatever
the number of primes. The sector decomposition is the hypothesis `ConstantSectorBounds`. -/
theorem block_bounds {S : Finset ℝ} {b : ℝ} (hb : 7 ≤ b) (hS : ∀ p ∈ S, b ≤ p)
    (D : ConstantSectorBounds S) : D.symN ≤ gamC b ^ 2 ∧ D.skewN ≤ gamC b := by
  have hb1 : 1 < b := by linarith
  have hge : ∀ p ∈ S, 1 < p := fun p hp => lt_of_lt_of_le hb1 (hS p hp)
  have hgam0 : 0 ≤ gamC b := gamC_nonneg hb1
  have hrho0 : 0 ≤ rhoC b := rhoC_nonneg hb1
  have hrho1 : rhoC b ≤ 1 := rhoC_le_one (by linarith)
  have heta0 : 0 ≤ etaC b := etaC_nonneg hb1
  have heta1 : etaC b ≤ 1 := etaC_le_one (by linarith)
  -- products over a sector
  have hprod_rho : ∀ T ⊆ S, ∏ p ∈ T, rhoC p ≤ rhoC b ^ T.card := fun T hT =>
    prod_le_pow_card (fun p hp => rhoC_nonneg (hge p (hT hp)))
      (fun p hp => rhoC_anti hb1 (hS p (hT hp)))
  have hprod_eta : ∀ T ⊆ S, ∏ p ∈ T, etaC p ≤ etaC b ^ T.card := fun T hT =>
    prod_le_pow_card (fun p hp => etaC_nonneg (hge p (hT hp)))
      (fun p hp => etaC_anti hb1 (hS p (hT hp)))
  have hprod_gam : ∀ T ⊆ S, ∏ p ∈ T, gamC p ≤ gamC b ^ T.card := fun T hT =>
    prod_le_pow_card (fun p hp => gamC_nonneg (hge p (hT hp)))
      (fun p hp => gamC_anti hb1 (hS p (hT hp)))
  constructor
  · apply D.sym_le _ (sq_nonneg _)
    intro T hT hne
    rcases Nat.lt_or_ge T.card 2 with h | h
    · -- a singleton
      have hc : T.card = 1 := by
        have := hne.card_pos
        omega
      obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hc
      exact le_trans (D.sym_one p (hT (Finset.mem_singleton_self p))) (sq_nonneg _)
    · rcases Nat.lt_or_ge T.card 3 with h' | h'
      · have hc : T.card = 2 := by omega
        have := hprod_gam T hT
        rw [hc] at this
        exact le_trans (D.sym_two T hT hc) this
      · have h1 := hprod_rho T hT
        have h2 := hprod_eta T hT
        have h3r : rhoC b ^ T.card ≤ rhoC b ^ 3 := pow_le_pow_of_le_one hrho0 hrho1 h'
        have h3e : etaC b ^ T.card ≤ etaC b ^ 3 := pow_le_pow_of_le_one heta0 heta1 h'
        have := rho_cube_add_eta_cube_le hb
        linarith [D.sym_three T hT h']
  · apply D.skew_le _ hgam0
    intro T hT hne
    rcases Nat.lt_or_ge T.card 2 with h | h
    · have hc : T.card = 1 := by
        have := hne.card_pos
        omega
      obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hc
      have hp := Finset.mem_singleton_self p
      exact le_trans (D.skew_one p (hT hp)) (gamC_anti hb1 (hS p (hT hp)))
    · have h1 := hprod_rho T hT
      have h2r : rhoC b ^ T.card ≤ rhoC b ^ 2 := pow_le_pow_of_le_one hrho0 hrho1 h
      have := rho_sq_le_gam hb
      linarith [D.skew_two T hT h]

/-- **Non-vacuity of `ConstantSectorBounds`**: the bundle is satisfiable (all norms zero). -/
def constantSectorBounds_toy (S : Finset ℝ) (hS : ∀ p ∈ S, 1 < p) : ConstantSectorBounds S where
  symN := 0
  skewN := 0
  symSec := fun _ => 0
  skewSec := fun _ => 0
  sym_le := fun _ hM _ => hM
  skew_le := fun _ hM _ => hM
  sym_one := fun _ _ => le_refl 0
  skew_one := fun p hp => gamC_nonneg (hS p hp)
  sym_two := fun _ hT _ => Finset.prod_nonneg fun p hp => gamC_nonneg (hS p (hT hp))
  skew_two := fun _ hT _ => Finset.prod_nonneg fun p hp => rhoC_nonneg (hS p (hT hp))
  sym_three := fun _ hT _ => add_nonneg (Finset.prod_nonneg fun p hp => rhoC_nonneg (hS p (hT hp)))
    (Finset.prod_nonneg fun p hp => etaC_nonneg (hS p (hT hp)))

/-! ## The prices -/

/-- **The prices of the two two-layer constants** (`lem:record:accepting-c2`, last sentence).
Each of the two records has mass `w_C r³` before normalization; its change has symmetric and
skew norms `symN ≤ r²/(1 - 1/b)²` and `skewN ≤ r/(1 - 1/b)` (`block_bounds`, `gam_eq`); the
charging rule `rem:cp:charging`(ii) charges `mass × norm × sel`, `sel = q_𝔅^{2a} ≥ 0`. For a
piece starting at `X ≤ b`, `X > 1`, the two records together cost at most
`2 w_C/(1 - 1/X)² r⁵ sel` (symmetric) and `2 w_C/(1 - 1/X) r⁴ sel` (skew). -/
theorem accepting_c2_prices {wC r b X sel symN skewN : ℝ} (hwC : 0 ≤ wC) (hr : 0 ≤ r)
    (hsel : 0 ≤ sel) (hX : 1 < X) (hXb : X ≤ b)
    (hsym : symN ≤ r ^ 2 / (1 - 1 / b) ^ 2) (hskew : skewN ≤ r / (1 - 1 / b)) :
    2 * (wC * r ^ 3 * symN * sel) ≤ 2 * wC / (1 - 1 / X) ^ 2 * r ^ 5 * sel ∧
      2 * (wC * r ^ 3 * skewN * sel) ≤ 2 * wC / (1 - 1 / X) * r ^ 4 * sel := by
  have hX0 : 0 < X := by linarith
  have hb0 : 0 < b := by linarith
  have hXpos : 0 < 1 - 1 / X := by
    rw [sub_pos, div_lt_one hX0]
    exact hX
  have hle : 1 - 1 / X ≤ 1 - 1 / b := by
    have : 1 / b ≤ 1 / X := one_div_le_one_div_of_le hX0 hXb
    linarith
  have hinv : 1 / (1 - 1 / b) ≤ 1 / (1 - 1 / X) := one_div_le_one_div_of_le hXpos hle
  have hinv0 : 0 ≤ 1 / (1 - 1 / b) := by
    have : 0 < 1 - 1 / b := lt_of_lt_of_le hXpos hle
    positivity
  have hinv2 : (1 / (1 - 1 / b)) ^ 2 ≤ (1 / (1 - 1 / X)) ^ 2 :=
    pow_le_pow_left₀ hinv0 hinv 2
  have hw : 0 ≤ wC * r ^ 3 := mul_nonneg hwC (pow_nonneg hr 3)
  constructor
  · have h1 : symN ≤ r ^ 2 * (1 / (1 - 1 / X)) ^ 2 := by
      calc symN ≤ r ^ 2 / (1 - 1 / b) ^ 2 := hsym
        _ = r ^ 2 * (1 / (1 - 1 / b)) ^ 2 := by rw [div_pow, one_pow, mul_one_div]
        _ ≤ r ^ 2 * (1 / (1 - 1 / X)) ^ 2 := mul_le_mul_of_nonneg_left hinv2 (sq_nonneg r)
    have h2 : wC * r ^ 3 * symN * sel ≤ wC * r ^ 3 * (r ^ 2 * (1 / (1 - 1 / X)) ^ 2) * sel :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hw) hsel
    have e : 2 * (wC * r ^ 3 * (r ^ 2 * (1 / (1 - 1 / X)) ^ 2) * sel) =
        2 * wC / (1 - 1 / X) ^ 2 * r ^ 5 * sel := by
      field_simp
    linarith
  · have h1 : skewN ≤ r * (1 / (1 - 1 / X)) := by
      calc skewN ≤ r / (1 - 1 / b) := hskew
        _ = r * (1 / (1 - 1 / b)) := by rw [mul_one_div]
        _ ≤ r * (1 / (1 - 1 / X)) := mul_le_mul_of_nonneg_left hinv hr
    have h2 : wC * r ^ 3 * skewN * sel ≤ wC * r ^ 3 * (r * (1 / (1 - 1 / X))) * sel :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hw) hsel
    have e : 2 * (wC * r ^ 3 * (r * (1 / (1 - 1 / X))) * sel) =
        2 * wC / (1 - 1 / X) * r ^ 4 * sel := by
      field_simp
    linarith

end Sarkozy.MiddleRecords
