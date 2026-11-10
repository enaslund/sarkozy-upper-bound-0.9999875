module

public import Sarkozy.Mixing.SectorLemma
public import Sarkozy.MiddleRecords.ActualFeaturesA3

@[expose] public section

/-!
# The singleton correlations of the actual feature frame at a block
(`lem:oct24:feature-block`(a), edges `01`, `02`, `12`)

`paper/sections/23_envelopes.tex`, `lem:oct24:feature-block`(a), proof Steps 1–2: in the actual
product marginal `m_{0,𝔅} = ⊗_p m_{0,p}` the correlations of the singleton fold features
`𝓗₀, 𝓗₁, 𝓗₂` (mean-zero functions of one whole label) are at most `ϱ₀₁` (edges `01`, `12`)
and `ϱ₀₂` (edge `02`), with the constants at the least prime `b` of the block.

The correlation of `𝓗_a` and `𝓗_b` is `sup |⟨f(x_a), g(x_b)⟩_{m_{0,𝔅}}|/(‖f‖ ‖g‖)`; the pair
`(x_a, x_b)` has the law `⊗_p m_{ab,p}` (the product of the prime pair laws), and each coordinate is
uniform. So the correlation is the norm of `⊗_p T_p − 𝒥` on the uniform law, with the prime
conditional expectations `T_p f(u) = p ∑_v m_{ab,p}(u, v) f(v)`.

* **`block_correlation`** (Step 1, generic): for Markov operators `T_j` with uniform marginals
  and `‖T_j f‖ ≤ c ‖f‖` on mean-zero functions, `c ≤ 1`, the block correlation is at most `c`. It
  is Mixing's `general_markov_tensor_max` (`lem:sector`(c)) followed by Cauchy–Schwarz.
* **Prime inputs** (Step 2, `lem:actual-features`(b), MiddleRecords' `norm_V0m_V1`,
  `norm_V1m_V2`, `norm_V0m_V2`): `m₀₁ = m₁₂` (`m01_eq_m12`), the uniform marginals of `m₁₂` and
  `m₀₂` (`sum_m02_right`, `sum_m02_left`), the norms `ϱ₀₁²`, `ϱ₀₂²`.
* **`corr12_block`**, **`corr01_block`**, **`corr02_block`**: for a block of primes
  `p ≡ 3 (mod 4)`, `p ≥ 7`, and any `c ∈ [0, 1]` with `ϱ_{ab}(p)² ≤ c²` at every prime,
  `|∑_{u,v} ∏_p m_{ab,p}(u_p, v_p) f(u) g(v)| ≤ c ‖f‖ ‖g‖` (uniform norms) for mean-zero `g`.
* **`r01sq_anti`**, **`r02sq_anti`**: `ϱ₀₁²` and `ϱ₀₂²` are nonincreasing in `p ≥ 7`, so one may
  take `c = ϱ_{ab}(b)` at the least prime `b` (the paper's "every one-prime bound is at most its
  value at `b`").
* **In the actual block law** `m_{0,𝔅}(x) = ∏_p oldW_p(x_p)/oldZ_p` (`m0B`) on object triples:
  `sum_prod_pair`, `sum_prod_single` (the marginals of a product law are the products of the
  marginals), `fiber_sum_01`, `fiber_sum_12`, `fiber_sum_02` (the pair marginals of `m₀` are
  `m₀₁, m₁₂, m₀₂`), **`norm_actual_x0`**, `norm_actual_x1`, `norm_actual_x2` (the coordinates are
  uniform, so `‖f(x_a)‖_{m_{0,𝔅}}` is the uniform norm of `f`), and **`corr01_actual`**,
  **`corr12_actual`**, **`corr02_actual`**: `|⟨f(x_a), g(x_b)⟩_{m_{0,𝔅}}| ≤ c ‖f(x_a)‖ ‖g(x_b)‖`
  for mean-zero `g`, which is the statement of (a) for these edges.

**Not formalized here:** the edges `03`, `24`, `34` (Steps 3–4 of the proof: the pure-pair
features `𝒦₁₂`, `𝒦₀₁`, with the telescoping bound over several primes), and the vanishing of the
other correlations (`lem:sector`(a), orthogonality of distinct supports).
-/

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.EnvelopeSteps

/-! ## Weighted Cauchy–Schwarz -/

theorem abs_wsum_le {ι : Type*} (s : Finset ι) (w f h : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    |∑ i ∈ s, w i * f i * h i| ≤
      Real.sqrt (∑ i ∈ s, w i * f i ^ 2) * Real.sqrt (∑ i ∈ s, w i * h i ^ 2) := by
  have hcs := sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (w i) * f i)
    (fun i => Real.sqrt (w i) * h i)
  have e1 : ∑ i ∈ s, Real.sqrt (w i) * f i * (Real.sqrt (w i) * h i) =
      ∑ i ∈ s, w i * f i * h i := by
    refine sum_congr rfl fun i hi => ?_
    calc Real.sqrt (w i) * f i * (Real.sqrt (w i) * h i)
        = (Real.sqrt (w i) * Real.sqrt (w i)) * f i * h i := by ring
      _ = w i * f i * h i := by rw [Real.mul_self_sqrt (hw i hi)]
  have e2 : ∀ g : ι → ℝ, ∑ i ∈ s, (Real.sqrt (w i) * g i) ^ 2 = ∑ i ∈ s, w i * g i ^ 2 :=
    fun g => sum_congr rfl fun i hi => by rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rw [e1, e2, e2] at hcs
  rw [← Real.sqrt_mul (sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))]
  exact Real.abs_le_sqrt hcs

/-! ## The block correlation from the prime bounds (`lem:sector`(c)) -/

section Block

variable {K : Type*} [Fintype K] [DecidableEq K] {A : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A j)]

open Sarkozy.Mixing

/-- **Step 1 of `lem:oct24:feature-block`** (generic): for Markov operators `T_j` on `L²(π_j)`
(`T_j 1 = 1`, `T_j^* 1 = 1`) with `‖T_j f‖ ≤ c ‖f‖` on the mean-zero functions and `c ≤ 1`, the
correlation `⟨f, (⊗_j T_j) g⟩` with `g` mean-zero is at most `c ‖f‖ ‖g‖`. -/
theorem block_correlation (π : ∀ j, A j → ℝ) (T : ∀ j, Matrix (A j) (A j) ℝ)
    (hπ : ∀ j a, 0 ≤ π j a) (hπ1 : ∀ j, ∑ a, π j a = 1)
    (hrow : ∀ j b, π j b ≠ 0 → ∑ a, T j b a = 1) (hcol : ∀ j a, ∑ b, π j b * T j b a = π j a)
    {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hδ : ∀ j f, ∑ a, π j a * f a = 0 →
      ∑ b, π j b * (T j *ᵥ f) b ^ 2 ≤ c ^ 2 * ∑ a, π j a * f a ^ 2)
    (f g : (∀ j, A j) → ℝ) (hg : ∑ a, prodW π a * g a = 0) :
    |∑ u, prodW π u * f u * (prodOp T *ᵥ g) u| ≤
      c * (Real.sqrt (∑ u, prodW π u * f u ^ 2) * Real.sqrt (∑ u, prodW π u * g u ^ 2)) := by
  have hcontr : ∀ j f, ∑ a, π j a * f a = 0 →
      ∑ b, π j b * (T j *ᵥ f) b ^ 2 ≤ 1 ^ 2 * ∑ a, π j a * f a ^ 2 := by
    intro j f hf
    have h := hδ j f hf
    have hs : 0 ≤ ∑ a, π j a * f a ^ 2 := sum_nonneg fun a _ => mul_nonneg (hπ j a) (sq_nonneg _)
    have hc2 : c ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hc hc1 2
    nlinarith
  have hglob := (general_markov_tensor_max π π T hπ hπ1 hπ hrow hcol hcontr hc).mpr hδ g
  rw [hg] at hglob
  simp only [sub_zero] at hglob
  have hw : ∀ u ∈ (univ : Finset (∀ j, A j)), 0 ≤ prodW π u :=
    fun u _ => prod_nonneg fun j _ => hπ j (u j)
  have hcs := abs_wsum_le univ (prodW π) f (prodOp T *ᵥ g) hw
  have hsq : Real.sqrt (∑ u, prodW π u * (prodOp T *ᵥ g) u ^ 2) ≤
      c * Real.sqrt (∑ u, prodW π u * g u ^ 2) := by
    rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg c)]
    exact Real.sqrt_le_sqrt hglob
  calc |∑ u, prodW π u * f u * (prodOp T *ᵥ g) u|
      ≤ Real.sqrt (∑ u, prodW π u * f u ^ 2) *
          Real.sqrt (∑ u, prodW π u * (prodOp T *ᵥ g) u ^ 2) := hcs
    _ ≤ Real.sqrt (∑ u, prodW π u * f u ^ 2) * (c * Real.sqrt (∑ u, prodW π u * g u ^ 2)) :=
        mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
    _ = c * (Real.sqrt (∑ u, prodW π u * f u ^ 2) * Real.sqrt (∑ u, prodW π u * g u ^ 2)) := by
        ring

end Block

/-! ## The prime inputs -/

section Prime

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

open Sarkozy.MiddleRecords

/-- `m₀₁ = m₁₂`: the pair laws of `(x₀, x₁)` and `(x₁, x₂)` coincide. -/
theorem m01_eq_m12 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (a b : F) : m01 a b = m12 a b := by
  rw [m01_eq' hF h3 h7, m12_eq' hF h3 h7]

theorem sumR_chi_sub_right (hF : ringChar F ≠ 2) (a : F) : ∑ b, (χ (b - a) : ℝ) = 0 := by
  have h : ∑ y, (χ y : ℝ) = 0 := by exact_mod_cast quadraticChar_sum_zero hF
  rw [← h]
  exact Equiv.sum_comp (Equiv.subRight a) (fun y => (χ y : ℝ))

/-- The coordinate `x₀` is uniform under `m₀`: `∑_b m₀₂(a, b) = 1/p`. -/
theorem sum_m02_right (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (a : F) : ∑ b, m02 a b = 1 / qF := by
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  simp only [m02_eq' hF h3 h7, ← sum_div, sum_sub_distrib, sum_add_distrib, sum_const, card_univ,
    nsmul_eq_mul, mul_one, sumR_chi_sub_right hF a, sum_ite_eq, mem_univ, ↓reduceIte]
  field_simp
  ring

/-- The coordinate `x₂` is uniform under `m₀`: `∑_a m₀₂(a, b) = 1/p`. -/
theorem sum_m02_left (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (b : F) : ∑ a, m02 a b = 1 / qF := by
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  simp only [m02_eq' hF h3 h7, ← sum_div, sum_sub_distrib, sum_add_distrib, sum_const, card_univ,
    nsmul_eq_mul, mul_one, sumR_chi_sub hF b, sum_ite_eq', mem_univ, ↓reduceIte]
  field_simp
  ring

/-- The uniform law `1/p`. -/
noncomputable def unifF (_ : F) : ℝ := 1 / qF

/-- The conditional expectation as a matrix: `T(u, v) = p m(u, v)`. -/
noncomputable def condMat (m : F → F → ℝ) : Matrix F F ℝ := fun u v => qF * m u v

omit [Field F] [DecidableEq F] in
theorem condMat_mulVec (m : F → F → ℝ) (f : F → ℝ) (u : F) :
    (condMat m *ᵥ f) u = condOp m f u := by
  simp only [Matrix.mulVec, dotProduct, condMat, condOp, mul_sum]
  exact sum_congr rfl fun v _ => by ring

omit [DecidableEq F] in
/-- The prime hypotheses of `block_correlation` for a pair law `m` with uniform marginals and the
norm identity `∑ (T f)² = ρ² ∑ f²` on mean-zero `f`, `ρ² ≤ c²`. -/
theorem prime_inputs (m : F → F → ℝ) (hr : ∀ u, ∑ v, m u v = 1 / qF)
    (hl : ∀ v, ∑ u, m u v = 1 / qF) {ρsq c : ℝ} (hρc : ρsq ≤ c ^ 2)
    (hn : ∀ f : F → ℝ, ∑ v, f v = 0 → ∑ u, condOp m f u ^ 2 = ρsq * ∑ u, f u ^ 2)
    (h7 : 7 ≤ qF) :
    (∀ u, unifF u ≠ 0 → ∑ v, condMat m u v = 1) ∧
    (∀ v, ∑ u, unifF u * condMat m u v = unifF v) ∧
    (∀ f : F → ℝ, ∑ v, unifF v * f v = 0 →
      ∑ u, unifF u * (condMat m *ᵥ f) u ^ 2 ≤ c ^ 2 * ∑ v, unifF v * f v ^ 2) := by
  have h0 : qF ≠ 0 := by intro h; linarith
  refine ⟨fun u _ => ?_, fun v => ?_, fun f hf => ?_⟩
  · simp only [condMat, ← mul_sum, hr u]
    field_simp
  · simp only [unifF, condMat]
    have e : ∑ u, 1 / qF * (qF * m u v) = ∑ u, m u v := sum_congr rfl fun u _ => by field_simp
    rw [e, hl v]
  · have hf' : ∑ v, f v = 0 := by
      simp only [unifF, ← mul_sum] at hf
      rcases mul_eq_zero.mp hf with h | h
      · exact absurd h (by positivity)
      · exact h
    simp only [unifF, condMat_mulVec, ← mul_sum, hn f hf']
    have hs : 0 ≤ ∑ u, f u ^ 2 := sum_nonneg fun u _ => sq_nonneg _
    have hq : 0 ≤ 1 / qF := by positivity
    have := mul_le_mul_of_nonneg_right hρc hs
    nlinarith

end Prime

/-! ## The block statements -/

section BlockEdges

open Sarkozy.MiddleRecords Sarkozy.Mixing

variable {P : Type*} [Fintype P] [DecidableEq P] {F : P → Type*} [∀ p, Field (F p)]
  [∀ p, Fintype (F p)] [∀ p, DecidableEq (F p)]

/-- The squared constant `ϱ₀₁²(p) = (1 + μ² p)/(p − 1)²`, `μ = 2/(p − 4)`. -/
noncomputable def r01sq (x : ℝ) : ℝ := (1 + (2 / (x - 4)) ^ 2 * x) / (x - 1) ^ 2

/-- The squared constant `ϱ₀₂²(p) = q(1 + q)/(1 − q)²`, `q = 1/p`. -/
noncomputable def r02sq (x : ℝ) : ℝ := (1 / x) * (1 + 1 / x) / (1 - 1 / x) ^ 2

/-- A uniform block law of the primes. -/
noncomputable def unifB (p : P) (_ : F p) : ℝ := 1 / (Fintype.card (F p) : ℝ)

/-- The prime conditional expectation matrices of a family of pair laws. -/
noncomputable def condMatB (m : ∀ p, F p → F p → ℝ) (p : P) : Matrix (F p) (F p) ℝ :=
  condMat (m p)

omit [∀ p, DecidableEq (F p)] in
/-- The block pair law `⊗_p m_p` against `f ⊗ g` is `⟨f, (⊗_p T_p) g⟩` in the uniform law. -/
theorem pair_sum_eq (m : ∀ p, F p → F p → ℝ)
    (f g : (∀ p, F p) → ℝ) :
    ∑ u, ∑ v, (∏ p, m p (u p) (v p)) * f u * g v =
      ∑ u, prodW unifB u * f u * (prodOp (condMatB m) *ᵥ g) u := by
  refine sum_congr rfl fun u _ => ?_
  simp only [Matrix.mulVec, dotProduct, mul_sum]
  refine sum_congr rfl fun v _ => ?_
  have e : prodW unifB u * prodOp (condMatB m) u v = ∏ p, m p (u p) (v p) := by
    simp only [prodW, prodOp, unifB, condMatB, condMat, ← prod_mul_distrib]
    exact prod_congr rfl fun p _ => by field_simp
  rw [← e]
  ring

/-- The generic block edge from a pair law at every prime. -/
theorem corr_block_of (m : ∀ p, F p → F p → ℝ) (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p))
    (hr : ∀ p u, ∑ v, m p u v = 1 / (Fintype.card (F p) : ℝ))
    (hl : ∀ p v, ∑ u, m p u v = 1 / (Fintype.card (F p) : ℝ))
    (ρsq : P → ℝ)
    (hn : ∀ p, ∀ f : F p → ℝ, ∑ v, f v = 0 →
      ∑ u, condOp (m p) f u ^ 2 = ρsq p * ∑ u, f u ^ 2)
    {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (hρc : ∀ p, ρsq p ≤ c ^ 2)
    (f g : (∀ p, F p) → ℝ) (hg : ∑ v, prodW unifB v * g v = 0) :
    |∑ u, ∑ v, (∏ p, m p (u p) (v p)) * f u * g v| ≤
      c * (Real.sqrt (∑ u, prodW unifB u * f u ^ 2) *
        Real.sqrt (∑ v, prodW unifB v * g v ^ 2)) := by
  have hcard : ∀ p, (Fintype.card (F p) : ℝ) ≠ 0 := fun p h => by linarith [h7 p]
  have hin := fun p => prime_inputs (m p) (hr p) (hl p) (hρc p) (hn p) (h7 p)
  rw [pair_sum_eq m]
  refine block_correlation unifB (condMatB m) (fun p _ => by
      have := h7 p; unfold unifB; positivity) (fun p => ?_) (fun p => (hin p).1)
    (fun p => (hin p).2.1) hc hc1 (fun p => (hin p).2.2) f g hg
  simp only [unifB, sum_const, card_univ, nsmul_eq_mul]
  field_simp [hcard p]

/-- **`lem:oct24:feature-block`(a), edge `12`, at a block**: for a block of primes
`p ≡ 3 (mod 4)`, `p ≥ 7`, and `c ∈ [0, 1]` with `ϱ₀₁(p)² ≤ c²` at every prime, the correlation of
`𝓗₁` and `𝓗₂` in `⊗_p m_{0,p}` is at most `c`. -/
theorem corr12_block (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hρc : ∀ p, r01sq (Fintype.card (F p) : ℝ) ≤ c ^ 2)
    (f g : (∀ p, F p) → ℝ) (hg : ∑ v, prodW unifB v * g v = 0) :
    |∑ u, ∑ v, (∏ p, m12 (u p) (v p)) * f u * g v| ≤
      c * (Real.sqrt (∑ u, prodW unifB u * f u ^ 2) *
        Real.sqrt (∑ v, prodW unifB v * g v ^ 2)) := by
  refine corr_block_of (fun p => m12 (F := F p)) h7
    (fun p u => sum_m12_right (hF p) (h3 p) (h7 p) u)
    (fun p v => sum_m12_left (hF p) (h3 p) (h7 p) v) (fun p => r01sq (Fintype.card (F p) : ℝ))
    (fun p f hf => ?_) hc hc1 hρc f g hg
  rw [norm_V1m_V2 (hF p) (h3 p) (h7 p) f hf]
  rfl

/-- **`lem:oct24:feature-block`(a), edge `01`, at a block** (`m₀₁ = m₁₂`). -/
theorem corr01_block (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hρc : ∀ p, r01sq (Fintype.card (F p) : ℝ) ≤ c ^ 2)
    (f g : (∀ p, F p) → ℝ) (hg : ∑ v, prodW unifB v * g v = 0) :
    |∑ u, ∑ v, (∏ p, m01 (u p) (v p)) * f u * g v| ≤
      c * (Real.sqrt (∑ u, prodW unifB u * f u ^ 2) *
        Real.sqrt (∑ v, prodW unifB v * g v ^ 2)) := by
  have e : ∀ u v : ∀ p, F p, (∏ p, m01 (u p) (v p)) = ∏ p, m12 (u p) (v p) := fun u v =>
    prod_congr rfl fun p _ => m01_eq_m12 (hF p) (h3 p) (h7 p) (u p) (v p)
  simp only [e]
  exact corr12_block hF h3 h7 hc hc1 hρc f g hg

/-- **`lem:oct24:feature-block`(a), edge `02`, at a block**: the correlation of `𝓗₀` and `𝓗₂` in
`⊗_p m_{0,p}` is at most `c` for `c ∈ [0, 1]` with `ϱ₀₂(p)² ≤ c²` at every prime. -/
theorem corr02_block (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hρc : ∀ p, r02sq (Fintype.card (F p) : ℝ) ≤ c ^ 2)
    (f g : (∀ p, F p) → ℝ) (hg : ∑ v, prodW unifB v * g v = 0) :
    |∑ u, ∑ v, (∏ p, m02 (u p) (v p)) * f u * g v| ≤
      c * (Real.sqrt (∑ u, prodW unifB u * f u ^ 2) *
        Real.sqrt (∑ v, prodW unifB v * g v ^ 2)) := by
  refine corr_block_of (fun p => m02 (F := F p)) h7
    (fun p u => sum_m02_right (hF p) (h3 p) (h7 p) u)
    (fun p v => sum_m02_left (hF p) (h3 p) (h7 p) v) (fun p => r02sq (Fintype.card (F p) : ℝ))
    (fun p f hf => ?_) hc hc1 hρc f g hg
  rw [norm_V0m_V2 (hF p) (h3 p) (h7 p) f hf]
  rfl

end BlockEdges

/-! ## The pair marginals of the actual block law -/

section Marginal

variable {P : Type*} [Fintype P] [DecidableEq P] {T F : P → Type*} [∀ p, Fintype (T p)]
  [∀ p, Fintype (F p)] [∀ p, DecidableEq (F p)]

/-- **The pair marginal of a product law is the product of the pair marginals**: for weights
`w_p` on `T_p` and coordinates `πa_p, πb_p : T_p → F_p`,
`∑_x ∏_p w_p(x_p) G(πa x, πb x) = ∑_{u,v} ∏_p m_p(u_p, v_p) G(u, v)` with
`m_p(a, b) = ∑_{πa t = a, πb t = b} w_p(t)`. -/
theorem sum_prod_pair (w : ∀ p, T p → ℝ) (πa πb : ∀ p, T p → F p)
    (G : (∀ p, F p) → (∀ p, F p) → ℝ) :
    ∑ x : ∀ p, T p, (∏ p, w p (x p)) * G (fun p => πa p (x p)) (fun p => πb p (x p)) =
      ∑ u : ∀ p, F p, ∑ v : ∀ p, F p, (∏ p, ∑ t : T p,
        (if πa p t = u p ∧ πb p t = v p then w p t else 0)) * G u v := by
  have hG : ∀ x : ∀ p, T p, G (fun p => πa p (x p)) (fun p => πb p (x p)) =
      ∑ u : ∀ p, F p, ∑ v : ∀ p, F p,
        (if (fun p => πa p (x p)) = u ∧ (fun p => πb p (x p)) = v then G u v else 0) := by
    intro x
    rw [Fintype.sum_eq_single (fun p => πa p (x p))]
    · rw [Fintype.sum_eq_single (fun p => πb p (x p))]
      · simp
      · intro v hv
        simp only [true_and]
        rw [ite_eq_right (fun h => hv h.symm)]
    · intro u hu
      refine sum_eq_zero fun v _ => ?_
      rw [ite_eq_right (fun h => hu h.1.symm)]
  simp only [hG, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [Fintype.prod_sum, sum_mul]
  refine sum_congr rfl fun x _ => ?_
  have e : (∏ p, (if πa p (x p) = u p ∧ πb p (x p) = v p then w p (x p) else 0)) =
      (∏ p, w p (x p)) *
        (if (fun p => πa p (x p)) = u ∧ (fun p => πb p (x p)) = v then 1 else 0) := by
    have e1 : ∀ p, (if πa p (x p) = u p ∧ πb p (x p) = v p then w p (x p) else 0) =
        w p (x p) * (if πa p (x p) = u p ∧ πb p (x p) = v p then 1 else 0) := fun p => by
      split_ifs <;> ring
    rw [prod_congr rfl fun p _ => e1 p, prod_mul_distrib, prod_indicator_forall]
    congr 2
    apply propext
    constructor
    · intro h
      exact ⟨funext fun p => (h p).1, funext fun p => (h p).2⟩
    · rintro ⟨h1, h2⟩ p
      exact ⟨congrFun h1 p, congrFun h2 p⟩
  rw [e]
  split_ifs <;> ring

/-- **The single marginal of a product law is the product of the marginals.** -/
theorem sum_prod_single (w : ∀ p, T p → ℝ) (π : ∀ p, T p → F p) (H : (∀ p, F p) → ℝ) :
    ∑ x : ∀ p, T p, (∏ p, w p (x p)) * H (fun p => π p (x p)) =
      ∑ u : ∀ p, F p, (∏ p, ∑ t : T p, (if π p t = u p then w p t else 0)) * H u := by
  have hH : ∀ x : ∀ p, T p, H (fun p => π p (x p)) =
      ∑ u : ∀ p, F p, (if (fun p => π p (x p)) = u then H u else 0) := by
    intro x
    rw [Fintype.sum_eq_single (fun p => π p (x p))]
    · simp
    · intro u hu
      rw [ite_eq_right (fun h => hu h.symm)]
  simp only [hH, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [Fintype.prod_sum, sum_mul]
  refine sum_congr rfl fun x _ => ?_
  have e : (∏ p, (if π p (x p) = u p then w p (x p) else 0)) =
      (∏ p, w p (x p)) * (if (fun p => π p (x p)) = u then 1 else 0) := by
    have e1 : ∀ p, (if π p (x p) = u p then w p (x p) else 0) =
        w p (x p) * (if π p (x p) = u p then 1 else 0) := fun p => by split_ifs <;> ring
    rw [prod_congr rfl fun p _ => e1 p, prod_mul_distrib, prod_indicator_forall]
    congr 2
    apply propext
    constructor
    · intro h
      exact funext h
    · intro h p
      exact congrFun h p
  rw [e]
  split_ifs <;> ring

end Marginal

section ActualBlock

open Sarkozy.MiddleRecords Sarkozy.Mixing

variable {P : Type*} [Fintype P] [DecidableEq P] {F : P → Type*} [∀ p, Field (F p)]
  [∀ p, Fintype (F p)] [∀ p, DecidableEq (F p)]

/-- The actual block law `m_{0,𝔅}(x) = ∏_p oldW_p(x_p)/oldZ_p` on object triples. -/
noncomputable def m0B (x : ∀ p, F p × F p × F p) : ℝ :=
  ∏ p, oldW (x p).1 (x p).2.1 (x p).2.2 / oldZ (F := F p)

omit [∀ p, Field (F p)] in
theorem fiber_sum_01 {K : Type*} [Field K] [Fintype K] [DecidableEq K] (a b : K) :
    ∑ t : K × K × K, (if t.1 = a ∧ t.2.1 = b then oldW t.1 t.2.1 t.2.2 / oldZ (F := K) else 0) =
      m01 a b := by
  rw [m01, sum_div, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [sum_eq_single a]
  · rw [sum_eq_single b]
    · simp
    · intro y _ hy
      exact sum_eq_zero fun z _ => by simp [hy]
    · simp
  · intro x _ hx
    exact sum_eq_zero fun y _ => sum_eq_zero fun z _ => by simp [hx]
  · simp

/-- **`lem:oct24:feature-block`(a), edge `01`, in the actual block law**: for mean-zero `g`,
`|⟨f(x₀), g(x₁)⟩_{m_{0,𝔅}}| ≤ c ‖f‖ ‖g‖` (uniform norms, which are the `m_{0,𝔅}` norms of
`f(x₀)`, `g(x₁)` since every coordinate is uniform). -/
theorem corr01_actual (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hρc : ∀ p, r01sq (Fintype.card (F p) : ℝ) ≤ c ^ 2)
    (f g : (∀ p, F p) → ℝ) (hg : ∑ v, prodW unifB v * g v = 0) :
    |∑ x, m0B x * f (fun p => (x p).1) * g (fun p => (x p).2.1)| ≤
      c * (Real.sqrt (∑ u, prodW unifB u * f u ^ 2) *
        Real.sqrt (∑ v, prodW unifB v * g v ^ 2)) := by
  have e := sum_prod_pair (fun p (t : F p × F p × F p) => oldW t.1 t.2.1 t.2.2 / oldZ (F := F p))
    (fun p t => t.1) (fun p t => t.2.1) (fun u v => f u * g v)
  simp only [fiber_sum_01] at e
  have e' : ∑ x, m0B x * f (fun p => (x p).1) * g (fun p => (x p).2.1) =
      ∑ u, ∑ v, (∏ p, m01 (u p) (v p)) * f u * g v := by
    rw [show (∑ x, m0B x * f (fun p => (x p).1) * g (fun p => (x p).2.1)) =
      ∑ x : ∀ p, F p × F p × F p, (∏ p, oldW (x p).1 (x p).2.1 (x p).2.2 / oldZ (F := F p)) *
        (f (fun p => (x p).1) * g (fun p => (x p).2.1)) from
      sum_congr rfl fun x _ => by unfold m0B; ring, e]
    exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by ring
  rw [e']
  exact corr01_block hF h3 h7 hc hc1 hρc f g hg

omit [∀ p, Field (F p)] in
theorem fiber_sum_12 {K : Type*} [Field K] [Fintype K] [DecidableEq K] (a b : K) :
    ∑ t : K × K × K, (if t.2.1 = a ∧ t.2.2 = b then oldW t.1 t.2.1 t.2.2 / oldZ (F := K) else 0) =
      m12 a b := by
  rw [m12, sum_div, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, sum_eq_single a]
  · rw [sum_eq_single b]
    · simp
    · intro y _ hy
      simp [hy]
    · simp
  · intro y _ hy
    exact sum_eq_zero fun z _ => by simp [hy]
  · simp

omit [∀ p, Field (F p)] in
theorem fiber_sum_02 {K : Type*} [Field K] [Fintype K] [DecidableEq K] (a b : K) :
    ∑ t : K × K × K, (if t.1 = a ∧ t.2.2 = b then oldW t.1 t.2.1 t.2.2 / oldZ (F := K) else 0) =
      m02 a b := by
  rw [m02, sum_div, Fintype.sum_prod_type, sum_eq_single a]
  · rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun y _ => ?_
    rw [sum_eq_single b]
    · simp
    · intro z _ hz
      simp [hz]
    · simp
  · intro x _ hx
    exact sum_eq_zero fun y _ => by simp [hx]
  · simp

/-- **`lem:oct24:feature-block`(a), edge `12`, in the actual block law.** -/
theorem corr12_actual (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hρc : ∀ p, r01sq (Fintype.card (F p) : ℝ) ≤ c ^ 2)
    (f g : (∀ p, F p) → ℝ) (hg : ∑ v, prodW unifB v * g v = 0) :
    |∑ x, m0B x * f (fun p => (x p).2.1) * g (fun p => (x p).2.2)| ≤
      c * (Real.sqrt (∑ u, prodW unifB u * f u ^ 2) *
        Real.sqrt (∑ v, prodW unifB v * g v ^ 2)) := by
  have e := sum_prod_pair (fun p (t : F p × F p × F p) => oldW t.1 t.2.1 t.2.2 / oldZ (F := F p))
    (fun p t => t.2.1) (fun p t => t.2.2) (fun u v => f u * g v)
  simp only [fiber_sum_12] at e
  have e' : ∑ x, m0B x * f (fun p => (x p).2.1) * g (fun p => (x p).2.2) =
      ∑ u, ∑ v, (∏ p, m12 (u p) (v p)) * f u * g v := by
    rw [show (∑ x, m0B x * f (fun p => (x p).2.1) * g (fun p => (x p).2.2)) =
      ∑ x : ∀ p, F p × F p × F p, (∏ p, oldW (x p).1 (x p).2.1 (x p).2.2 / oldZ (F := F p)) *
        (f (fun p => (x p).2.1) * g (fun p => (x p).2.2)) from
      sum_congr rfl fun x _ => by unfold m0B; ring, e]
    exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by ring
  rw [e']
  exact corr12_block hF h3 h7 hc hc1 hρc f g hg

/-- **`lem:oct24:feature-block`(a), edge `02`, in the actual block law.** -/
theorem corr02_actual (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hρc : ∀ p, r02sq (Fintype.card (F p) : ℝ) ≤ c ^ 2)
    (f g : (∀ p, F p) → ℝ) (hg : ∑ v, prodW unifB v * g v = 0) :
    |∑ x, m0B x * f (fun p => (x p).1) * g (fun p => (x p).2.2)| ≤
      c * (Real.sqrt (∑ u, prodW unifB u * f u ^ 2) *
        Real.sqrt (∑ v, prodW unifB v * g v ^ 2)) := by
  have e := sum_prod_pair (fun p (t : F p × F p × F p) => oldW t.1 t.2.1 t.2.2 / oldZ (F := F p))
    (fun p t => t.1) (fun p t => t.2.2) (fun u v => f u * g v)
  simp only [fiber_sum_02] at e
  have e' : ∑ x, m0B x * f (fun p => (x p).1) * g (fun p => (x p).2.2) =
      ∑ u, ∑ v, (∏ p, m02 (u p) (v p)) * f u * g v := by
    rw [show (∑ x, m0B x * f (fun p => (x p).1) * g (fun p => (x p).2.2)) =
      ∑ x : ∀ p, F p × F p × F p, (∏ p, oldW (x p).1 (x p).2.1 (x p).2.2 / oldZ (F := F p)) *
        (f (fun p => (x p).1) * g (fun p => (x p).2.2)) from
      sum_congr rfl fun x _ => by unfold m0B; ring, e]
    exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by ring
  rw [e']
  exact corr02_block hF h3 h7 hc hc1 hρc f g hg

omit [∀ p, Field (F p)] in
theorem fiber_x0 {K : Type*} [Field K] [Fintype K] [DecidableEq K] (hK : ringChar K ≠ 2)
    (h3 : Fintype.card K % 4 = 3) (h7 : (7 : ℝ) ≤ Fintype.card K) (a : K) :
    ∑ t : K × K × K, (if t.1 = a then oldW t.1 t.2.1 t.2.2 / oldZ (F := K) else 0) =
      1 / (Fintype.card K : ℝ) := by
  rw [← sum_m01 hK h3 h7 a, Fintype.sum_prod_type, sum_eq_single a]
  · simp only [↓reduceIte]
    rw [Fintype.sum_prod_type]
    exact sum_congr rfl fun y _ => by rw [m01, sum_div]
  · intro x _ hx
    exact sum_eq_zero fun y _ => by simp [hx]
  · simp

omit [∀ p, Field (F p)] in
theorem fiber_x1 {K : Type*} [Field K] [Fintype K] [DecidableEq K] (hK : ringChar K ≠ 2)
    (h3 : Fintype.card K % 4 = 3) (h7 : (7 : ℝ) ≤ Fintype.card K) (a : K) :
    ∑ t : K × K × K, (if t.2.1 = a then oldW t.1 t.2.1 t.2.2 / oldZ (F := K) else 0) =
      1 / (Fintype.card K : ℝ) := by
  rw [← sum_m12_right hK h3 h7 a]
  simp only [m12, sum_div]
  rw [sum_comm, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, sum_eq_single a]
  · simp
  · intro y _ hy
    exact sum_eq_zero fun z _ => by simp [hy]
  · simp

omit [∀ p, Field (F p)] in
theorem fiber_x2 {K : Type*} [Field K] [Fintype K] [DecidableEq K] (hK : ringChar K ≠ 2)
    (h3 : Fintype.card K % 4 = 3) (h7 : (7 : ℝ) ≤ Fintype.card K) (b : K) :
    ∑ t : K × K × K, (if t.2.2 = b then oldW t.1 t.2.1 t.2.2 / oldZ (F := K) else 0) =
      1 / (Fintype.card K : ℝ) := by
  rw [← sum_m12_left hK h3 h7 b]
  simp only [m12, sum_div]
  rw [sum_comm, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_eq_single b]
  · simp
  · intro z _ hz
    simp [hz]
  · simp

/-- **The coordinates are uniform under `m_{0,𝔅}`**: for a coordinate map `π` of the object
triples whose prime marginals are uniform, `‖f ∘ π‖²_{m_{0,𝔅}}` is the uniform norm of `f`. -/
theorem norm_actual (π : ∀ p, F p × F p × F p → F p)
    (hπ : ∀ p a, ∑ t : F p × F p × F p,
      (if π p t = a then oldW t.1 t.2.1 t.2.2 / oldZ (F := F p) else 0) =
        1 / (Fintype.card (F p) : ℝ)) (f : (∀ p, F p) → ℝ) :
    ∑ x, m0B x * f (fun p => π p (x p)) ^ 2 = ∑ u, prodW unifB u * f u ^ 2 := by
  have e := sum_prod_single (fun p (t : F p × F p × F p) => oldW t.1 t.2.1 t.2.2 / oldZ (F := F p))
    π (fun u => f u ^ 2)
  simp only [hπ] at e
  exact e

/-- The three coordinates of the object triples are uniform at every middle prime. -/
theorem norm_actual_x0 (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) (f : (∀ p, F p) → ℝ) :
    ∑ x, m0B x * f (fun p => (x p).1) ^ 2 = ∑ u, prodW unifB u * f u ^ 2 :=
  norm_actual (fun _ t => t.1) (fun p a => fiber_x0 (hF p) (h3 p) (h7 p) a) f

theorem norm_actual_x1 (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) (f : (∀ p, F p) → ℝ) :
    ∑ x, m0B x * f (fun p => (x p).2.1) ^ 2 = ∑ u, prodW unifB u * f u ^ 2 :=
  norm_actual (fun _ t => t.2.1) (fun p a => fiber_x1 (hF p) (h3 p) (h7 p) a) f

theorem norm_actual_x2 (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) (f : (∀ p, F p) → ℝ) :
    ∑ x, m0B x * f (fun p => (x p).2.2) ^ 2 = ∑ u, prodW unifB u * f u ^ 2 :=
  norm_actual (fun _ t => t.2.2) (fun p a => fiber_x2 (hF p) (h3 p) (h7 p) a) f

end ActualBlock

/-! ## Monotonicity in the prime -/

/-- `ϱ₀₂²` is nonincreasing on `[7, ∞)`. -/
theorem r02sq_anti {x y : ℝ} (hx : 7 ≤ x) (hxy : x ≤ y) : r02sq y ≤ r02sq x := by
  have hy : 7 ≤ y := le_trans hx hxy
  have ex : ∀ t : ℝ, 7 ≤ t → r02sq t = (t + 1) / (t - 1) ^ 2 := by
    intro t ht
    unfold r02sq
    have h0 : t ≠ 0 := by intro h; linarith
    have h1 : t - 1 ≠ 0 := by intro h; linarith
    field_simp
  rw [ex x hx, ex y hy, div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hx),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hx)) (sub_nonneg.mpr hx)]

/-- `ϱ₀₁²` is nonincreasing on `[7, ∞)`. -/
theorem r01sq_anti {x y : ℝ} (hx : 7 ≤ x) (hxy : x ≤ y) : r01sq y ≤ r01sq x := by
  have hy : 7 ≤ y := le_trans hx hxy
  have ex : ∀ t : ℝ, 7 ≤ t → r01sq t = ((t - 4) ^ 2 + 4 * t) / ((t - 4) ^ 2 * (t - 1) ^ 2) := by
    intro t ht
    unfold r01sq
    have h4 : t - 4 ≠ 0 := by intro h; linarith
    have h1 : t - 1 ≠ 0 := by intro h; linarith
    field_simp
    ring
  rw [ex x hx, ex y hy]
  -- `((t-4)² + 4t)/((t-4)²(t-1)²) = 1/(t-1)² + 4t/((t-4)²(t-1)²)`, both terms nonincreasing
  have hx4 : 0 < x - 4 := by linarith
  have hy4 : 0 < y - 4 := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hy1 : 0 < y - 1 := by linarith
  have s : ∀ t : ℝ, 7 ≤ t → ((t - 4) ^ 2 + 4 * t) / ((t - 4) ^ 2 * (t - 1) ^ 2) =
      1 / (t - 1) ^ 2 + 4 * (t / (t - 4) ^ 2) / (t - 1) ^ 2 := by
    intro t ht
    have h4 : t - 4 ≠ 0 := by intro h; linarith
    have h1 : t - 1 ≠ 0 := by intro h; linarith
    field_simp
  rw [s x hx, s y hy]
  have a1 : 1 / (y - 1) ^ 2 ≤ 1 / (x - 1) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have a2 : y / (y - 4) ^ 2 ≤ x / (x - 4) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hx),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hx)) (sub_nonneg.mpr hx)]
  have a3 : 4 * (y / (y - 4) ^ 2) / (y - 1) ^ 2 ≤ 4 * (x / (x - 4) ^ 2) / (x - 1) ^ 2 := by
    have b1 : 0 ≤ y / (y - 4) ^ 2 := by positivity
    calc 4 * (y / (y - 4) ^ 2) / (y - 1) ^ 2 ≤ 4 * (y / (y - 4) ^ 2) / (x - 1) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
      _ ≤ 4 * (x / (x - 4) ^ 2) / (x - 1) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
  linarith

end Sarkozy.EnvelopeSteps
