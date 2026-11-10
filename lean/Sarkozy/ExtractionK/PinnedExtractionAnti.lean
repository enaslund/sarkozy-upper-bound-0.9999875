module

public import Sarkozy.ExtractionK.PinnedExtraction
public import Sarkozy.ExtractionK.PinnedCollisionAnti

@[expose] public section

/-!
# The pinned nonstar bound at a threshold `Q ≤ p` (`prop:pinned-extraction`, `prop:pinned-collision`)

`paper/sections/16_extraction.tex`, `prop:pinned-collision`, last sentence: "`N^pin/r²` of
`prop:pinned-extraction` [is] admissible (`lem:majorant`) as a function of `r` on the range where
`e^pin_ϖ < 1`". As in `CompressedAnti.lean`, the consequence used — a bound evaluated at a
threshold `Q` holds at every `p ≥ Q` — is proved directly by monotonicity in `q`:

* `peGamma_anti`, `peLambda0_anti`: `γ_pin(q)` and `Λ^pin_0(q)` are nonincreasing in `q ≥ Q`
  when `e^pin_ϖ(Q) < 1` (`ePin_anti`);
* **`pinned_extraction_buckets_at`**: the bucket bound `N^pin` of `pinned_extraction_buckets` at
  `q = |F| ≥ Q` with `Λ^pin_0` and `γ_pin` evaluated at `Q`.

Admissibility in the sense of `lem:majorant` is not stated.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

theorem peGamma_anti {Q q : ℝ} (hQ : 0 < Q) (hQq : Q ≤ q) (n z Δ : ℕ) :
    peGamma q n z Δ ≤ peGamma Q n z Δ := by
  unfold peGamma
  have h1 : (Real.sqrt q)⁻¹ ≤ (Real.sqrt Q)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr hQ) (Real.sqrt_le_sqrt hQq)
  have h0 : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h2 : (Real.sqrt q)⁻¹ ^ 2 ≤ (Real.sqrt Q)⁻¹ ^ 2 := pow_le_pow_left₀ h0 h1 2
  have ha : (0 : ℝ) ≤ (2 * n + z : ℝ) / 2 := by positivity
  have hb : (0 : ℝ) ≤ (Δ : ℝ) / 4 := by positivity
  have := mul_le_mul_of_nonneg_left h2 ha
  have := mul_le_mul_of_nonneg_left h1 hb
  linarith

/-- `Λ^pin_0(q)` is nonincreasing in `q ≥ Q` when `e^pin_ϖ(Q) < 1`. -/
theorem peLambda0_anti (n z ϖ Δ : ℕ) {Q q : ℝ} (hQ : 0 < Q) (hQq : Q ≤ q)
    (he : ePin Q n z ϖ < 1) : peLambda0 q n z ϖ Δ ≤ peLambda0 Q n z ϖ Δ := by
  unfold peLambda0 peRpin
  have heq : ePin q n z ϖ ≤ ePin Q n z ϖ := ePin_anti n z ϖ hQ hQq
  have he0 := ePin_nonneg q n z ϖ
  have he0' := ePin_nonneg Q n z ϖ
  have h1q : 0 < 1 - ePin q n z ϖ := by linarith
  have h1Q : 0 < 1 - ePin Q n z ϖ := by linarith
  have hrat : (1 + ePin q n z ϖ) / (1 - ePin q n z ϖ) ≤
      (1 + ePin Q n z ϖ) / (1 - ePin Q n z ϖ) := by
    rw [div_le_div_iff₀ h1q h1Q]
    nlinarith
  have hrat0 : 0 ≤ (1 + ePin q n z ϖ) / (1 - ePin q n z ϖ) := div_nonneg (by linarith) h1q.le
  have hR : (((1 + ePin q n z ϖ) / (1 - ePin q n z ϖ)) ^ n) ^ 2 ≤
      (((1 + ePin Q n z ϖ) / (1 - ePin Q n z ϖ)) ^ n) ^ 2 :=
    pow_le_pow_left₀ (pow_nonneg hrat0 n) (pow_le_pow_left₀ hrat0 hrat n) 2
  have hr2 : (Real.sqrt q)⁻¹ ^ 2 ≤ (Real.sqrt Q)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (inv_anti₀ (Real.sqrt_pos.mpr hQ) (Real.sqrt_le_sqrt hQq)) 2
  have hexp : Real.exp ((Real.sqrt q)⁻¹ ^ 2 * n ^ 2 * 2 ^ Δ) ≤
      Real.exp ((Real.sqrt Q)⁻¹ ^ 2 * n ^ 2 * 2 ^ Δ) := by
    refine Real.exp_le_exp.mpr ?_
    have h0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * 2 ^ Δ := by positivity
    have := mul_le_mul_of_nonneg_right hr2 h0
    linarith [this]
  have hnum : (((1 + ePin q n z ϖ) / (1 - ePin q n z ϖ)) ^ n) ^ 2 *
      Real.exp ((Real.sqrt q)⁻¹ ^ 2 * n ^ 2 * 2 ^ Δ) ≤
      (((1 + ePin Q n z ϖ) / (1 - ePin Q n z ϖ)) ^ n) ^ 2 *
      Real.exp ((Real.sqrt Q)⁻¹ ^ 2 * n ^ 2 * 2 ^ Δ) :=
    mul_le_mul hR hexp (Real.exp_pos _).le (by positivity)
  have hden : (1 - ePin Q n z ϖ) ^ (n + 2) ≤ (1 - ePin q n z ϖ) ^ (n + 2) :=
    pow_le_pow_left₀ h1Q.le (by linarith) _
  exact div_le_div₀ (by positivity) hnum (pow_pos h1Q _) hden

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **`prop:pinned-extraction`, `N^pin` at a threshold `Q ≤ q = |F|`** (the use of the
admissibility of `N^pin/r²` stated in `prop:pinned-collision`): with `e^pin_ϖ(Q) < 1`, the bucket
bound holds at `q` with `Λ^pin_0` and `γ_pin` evaluated at `Q` and the factor `r² = 1/q` at `q`.
`lem:majorant` is replaced by the direct monotonicity `peLambda0_anti`, `peGamma_anti`. -/
theorem pinned_extraction_buckets_at (hW : WeilBound F) {n : ℕ} (M : Finset F)
    (pin : Fin n → F → ℤ) (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ) {Q : ℝ}
    (hQ : 0 < Q) (hQq : Q ≤ Fintype.card F) (he : ePin Q n M.card ϖ < 1)
    (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) {Δ : ℕ}
    (hΔX : ∀ i, ϖ + (pinNX ς i).card ≤ Δ) (hΔY : ∀ i, ϖ + (pinNY ς i).card ≤ Δ)
    (Ex : Finset (Fin n × Fin n)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0)
    (𝔓 : Finset (Finset (Fin n × Fin n) × Finset (Fin n × Fin n)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex))
    (wit : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → Fin 2 → Fin n × Fin n)
    (cx cz : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → Finset (Fin n))
    (ck : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → ℝ)
    (bucket : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → ℕ) (𝔮 : ℕ)
    (hwit : ∀ c ∈ 𝔓, IsWitness Ex c.1 c.2 (wit c))
    (hcov : ∀ c ∈ 𝔓, IsCover Ex c.1 c.2 (wit c) (cx c) (cz c))
    (hck : ∀ c ∈ 𝔓, 0 ≤ ck c)
    (hker : ∀ c ∈ 𝔓, Sarkozy.Influence.OpBound (injTuples F (witV (wit c)))
      (injTuples F (witW (wit c))) (rectKer ς c.1 (witV (wit c)) (witW (wit c)))
      (ck c * Real.sqrt (Fintype.card F) ^ 2))
    (hbucket : ∀ c ∈ 𝔓, peOc (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c) ≤
      (bucket c : ℝ) * 2 ^ 𝔮)
    (f h : (Fin n → F) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ y ∈ pinLab M pin,
        f x * (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x y) * h y) /
        ((pinLab M pin).card : ℝ) ^ 2| ≤
      (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * peLambda0 Q n M.card ϖ Δ * 2 ^ (2 * ϖ) *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          ck c * Real.sqrt (2 ^ (((Ex \ (c.1 ∪ c.2)).filter (fun e => e.1 ∈ witV (wit c))).card +
            ((Ex \ (c.1 ∪ c.2)).filter (fun e => e.2 ∈ witW (wit c))).card))) *
          Real.exp (peGamma Q n M.card Δ * 2 ^ ϖ * (b * 2 ^ 𝔮))) *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  have heq : ePin (Fintype.card F) n M.card ϖ < 1 :=
    lt_of_le_of_lt (ePin_anti n M.card ϖ hQ hQq) he
  have hb := pinned_extraction_buckets hW M pin hpin hpinM ϖ hϖ heq ς hς hΔX hΔY Ex hEx 𝔓 h𝔓
    wit cx cz ck bucket 𝔮 hwit hcov hck hker hbucket f h
  refine hb.trans ?_
  have hL := peLambda0_anti n M.card ϖ Δ hQ hQq he
  have hL0 : 0 ≤ peLambda0 (Fintype.card F) n M.card ϖ Δ := by
    unfold peLambda0 peRpin
    have he0 := ePin_nonneg (Fintype.card F) n M.card ϖ
    have h1 : 0 < 1 - ePin (Fintype.card F) n M.card ϖ := by linarith
    exact div_nonneg (mul_nonneg (pow_nonneg (pow_nonneg (div_nonneg (by linarith) h1.le) _) _)
      (Real.exp_pos _).le) (pow_pos h1 _).le
  have hS : ∀ b ∈ 𝔓.image bucket, 0 ≤ ∑ c ∈ 𝔓.filter (fun c => bucket c = b),
      ck c * Real.sqrt (2 ^ (((Ex \ (c.1 ∪ c.2)).filter (fun e => e.1 ∈ witV (wit c))).card +
        ((Ex \ (c.1 ∪ c.2)).filter (fun e => e.2 ∈ witW (wit c))).card)) := fun b _ =>
    sum_nonneg fun c hc => mul_nonneg (hck c (mem_filter.mp hc).1) (Real.sqrt_nonneg _)
  have hSig : ∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
      ck c * Real.sqrt (2 ^ (((Ex \ (c.1 ∪ c.2)).filter (fun e => e.1 ∈ witV (wit c))).card +
        ((Ex \ (c.1 ∪ c.2)).filter (fun e => e.2 ∈ witW (wit c))).card))) *
        Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * (b * 2 ^ 𝔮)) ≤
      ∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
      ck c * Real.sqrt (2 ^ (((Ex \ (c.1 ∪ c.2)).filter (fun e => e.1 ∈ witV (wit c))).card +
        ((Ex \ (c.1 ∪ c.2)).filter (fun e => e.2 ∈ witW (wit c))).card))) *
        Real.exp (peGamma Q n M.card Δ * 2 ^ ϖ * (b * 2 ^ 𝔮)) := by
    refine sum_le_sum fun b hb => mul_le_mul_of_nonneg_left ?_ (hS b hb)
    refine Real.exp_le_exp.mpr ?_
    have h0 : (0 : ℝ) ≤ 2 ^ ϖ * (b * 2 ^ 𝔮) := by positivity
    have := mul_le_mul_of_nonneg_right (peGamma_anti hQ hQq n M.card Δ) h0
    linarith [this]
  have hSig0 : 0 ≤ ∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
      ck c * Real.sqrt (2 ^ (((Ex \ (c.1 ∪ c.2)).filter (fun e => e.1 ∈ witV (wit c))).card +
        ((Ex \ (c.1 ∪ c.2)).filter (fun e => e.2 ∈ witW (wit c))).card))) *
        Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * (b * 2 ^ 𝔮)) :=
    sum_nonneg fun b hb => mul_nonneg (hS b hb) (Real.exp_pos _).le
  have hN : 0 ≤ Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
      Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by positivity
  have hr : 0 ≤ (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ (2 * ϖ) := by positivity
  have key := mul_le_mul hL hSig hSig0 (le_trans hL0 hL)
  have key2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key hr) hN
  calc _ = (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ (2 * ϖ) *
          (peLambda0 (Fintype.card F) n M.card ϖ Δ *
          ∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
            ck c * Real.sqrt (2 ^ (((Ex \ (c.1 ∪ c.2)).filter
              (fun e => e.1 ∈ witV (wit c))).card +
              ((Ex \ (c.1 ∪ c.2)).filter (fun e => e.2 ∈ witW (wit c))).card))) *
            Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * (b * 2 ^ 𝔮))) *
          (Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
          Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card)) := by ring
    _ ≤ _ := key2
    _ = _ := by ring

end Sarkozy.ExtractionK
