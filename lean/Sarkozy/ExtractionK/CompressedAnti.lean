module

public import Sarkozy.ExtractionK.Compressed
public import Sarkozy.ExtractionK.Leaf

@[expose] public section

/-!
# Compressed classes at a threshold `Q ≤ p` (`cor:extraction-compressed`, last sentence)

`paper/sections/16_extraction.tex`, `cor:extraction-compressed`: "for fixed classes and a fixed
assignment of each class to an integer `𝔟` (its bucket) as above, this right side divided by `r²`
is admissible (`lem:majorant`) as a function of `r` on the range where (S1) holds". The use of
admissibility is that a bound evaluated at a threshold `Q` holds at every prime `p ≥ Q`; this file
proves that consequence directly, by monotonicity in `q` (`r = q^{-1/2}`), without `lem:majorant`:

* `cmpGamma_anti`, `cmpLambda0_anti` (with `ê = e_{Δ⁺}(q, n)`, `leafEhat`), `cmp_bucketSum_anti`:
  `γ_cmp(q)`, `Λ₀(q)` and `∑_𝔟 S_𝔟 exp(γ_cmp(q) 𝔟 2^𝔮)` are nonincreasing in `q ≥ Q` when
  `ê(Q) < 1`;
* `extraction_compressed_buckets_at`, `extraction_compressed_buckets_two_at`: the bucket bound of
  `extraction_compressed_buckets` (`_two`) at `q = |F| ≥ Q` (`p ≥ Q`) with `Λ₀` and `γ_cmp`
  evaluated at `Q`, the factor `r^k` staying at `q`.

The admissibility in the sense of `lem:majorant` (`Certificates/Majorant.lean`) is not stated.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section Anti

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem cmp_rinv_anti {Q q : ℝ} (hQ : 0 < Q) (hQq : Q ≤ q) :
    (Real.sqrt q)⁻¹ ≤ (Real.sqrt Q)⁻¹ :=
  inv_anti₀ (Real.sqrt_pos.mpr hQ) (Real.sqrt_le_sqrt hQq)

theorem cmpGamma_anti {Q q : ℝ} (hQ : 0 < Q) (hQq : Q ≤ q) (n Δ : ℕ) :
    cmpGamma q n Δ ≤ cmpGamma Q n Δ := by
  unfold cmpGamma
  have h1 := cmp_rinv_anti hQ hQq
  have h0 : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h2 : (Real.sqrt q)⁻¹ ^ 2 ≤ (Real.sqrt Q)⁻¹ ^ 2 := pow_le_pow_left₀ h0 h1 2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hΔ : (0 : ℝ) ≤ (Δ : ℝ) / 4 := by positivity
  have := mul_le_mul_of_nonneg_left h2 hn
  have := mul_le_mul_of_nonneg_left h1 hΔ
  linarith

theorem cmpJsp_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) : 0 ≤ cmpJsp G ς := by
  unfold cmpJsp
  positivity

/-- `Λ₀(q)` with `ê = e_{Δ⁺}(q, n)` is nonincreasing in `q ≥ Q` when `ê(Q) < 1`. -/
theorem cmpLambda0_anti (G : OrientedGraph U) (ς : U → U → ℤ) (n k : ℕ) {Q q : ℝ} (hQ : 0 < Q)
    (hQq : Q ≤ q) (hS1 : leafEhat G Q n < 1) :
    cmpLambda0 G ς q n (leafEhat G q n) k ≤ cmpLambda0 G ς Q n (leafEhat G Q n) k := by
  unfold cmpLambda0
  have hq : 0 < q := lt_of_lt_of_le hQ hQq
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hEq : leafEhat G q n ≤ leafEhat G Q n := leafEhat_anti G hQ hQq
  have heQ : ∀ i, coarseError (rowsDeg0 G i) Q n < 1 := fun i =>
    lt_of_le_of_lt (coarseError_le_leafEhat G Q n i) hS1
  have heq : ∀ i, coarseError (rowsDeg0 G i) q n < 1 := fun i =>
    lt_of_le_of_lt (coarseError_le_leafEhat G q n i) (lt_of_le_of_lt hEq hS1)
  -- the numerators
  have hR1 := rowsR_univ_ge_one G heq
  have hR := rowsR_univ_anti G hQ hQq hS1 (n := n)
  have hr2 : (Real.sqrt q)⁻¹ ^ 2 ≤ (Real.sqrt Q)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) (cmp_rinv_anti hQ hQq) 2
  have hJ := cmpJsp_nonneg G ς
  have hexp : Real.exp ((Real.sqrt q)⁻¹ ^ 2 * cmpJsp G ς) ≤
      Real.exp ((Real.sqrt Q)⁻¹ ^ 2 * cmpJsp G ς) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hr2 hJ)
  have hnum : rowsR G q n univ ^ 2 * Real.exp ((Real.sqrt q)⁻¹ ^ 2 * cmpJsp G ς) ≤
      rowsR G Q n univ ^ 2 * Real.exp ((Real.sqrt Q)⁻¹ ^ 2 * cmpJsp G ς) :=
    mul_le_mul (pow_le_pow_left₀ (by linarith) hR 2) hexp (Real.exp_pos _).le (by positivity)
  -- the denominators
  have hden1 : (1 - leafEhat G Q n) ^ k ≤ (1 - leafEhat G q n) ^ k :=
    pow_le_pow_left₀ (by linarith) (by linarith) k
  have hden2 : ∏ i, (1 - coarseError (rowsDeg0 G i) Q n) ≤
      ∏ i, (1 - coarseError (rowsDeg0 G i) q n) := by
    refine prod_le_prod₀ (fun i _ => by linarith [heQ i]) (fun i _ => ?_)
    linarith [leaf_coarseError_anti (rowsDeg0 G i) hn hQ hQq]
  have hdQ : 0 < (1 - leafEhat G Q n) ^ k * ∏ i, (1 - coarseError (rowsDeg0 G i) Q n) :=
    mul_pos (pow_pos (by linarith) k) (prod_pos fun i _ => by linarith [heQ i])
  have hden : (1 - leafEhat G Q n) ^ k * ∏ i, (1 - coarseError (rowsDeg0 G i) Q n) ≤
      (1 - leafEhat G q n) ^ k * ∏ i, (1 - coarseError (rowsDeg0 G i) q n) :=
    mul_le_mul hden1 hden2 (prod_pos fun i _ => by linarith [heQ i]).le
      (pow_pos (by linarith [lt_of_le_of_lt hEq hS1]) k).le
  exact div_le_div₀ (by positivity) hnum hdQ hden

/-- The bucket sum `∑_𝔟 S_𝔟 exp(γ_cmp(q) 𝔟 2^𝔮)` is nonincreasing in `q` (`S_𝔟 ≥ 0`). -/
theorem cmp_bucketSum_anti {ι : Type*} (s : Finset ι) (S : ι → ℝ) (hS : ∀ b ∈ s, 0 ≤ S b)
    (β : ι → ℕ) (𝔮 n Δ : ℕ) {Q q : ℝ} (hQ : 0 < Q) (hQq : Q ≤ q) :
    ∑ b ∈ s, S b * Real.exp (cmpGamma q n Δ * (β b * 2 ^ 𝔮)) ≤
      ∑ b ∈ s, S b * Real.exp (cmpGamma Q n Δ * (β b * 2 ^ 𝔮)) := by
  refine sum_le_sum fun b hb => mul_le_mul_of_nonneg_left ?_ (hS b hb)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (cmpGamma_anti hQ hQq n Δ)
    (by positivity))

end Anti

section AntiBuckets

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **`cor:extraction-compressed`, the buckets evaluated at `Q ≤ q`** (the use of the
admissibility statement of the corollary): with `ê = e_{Δ⁺}(·, n)` and (S1) at `Q`
(`ê(Q) < 1`), the bucket bound holds at `q = |F| ≥ Q` with `Λ₀` and `γ_cmp` evaluated at `Q`:
`|∑_{S nonstar} ⟨f, T_S h⟩_μ| ≤ r^k Λ₀(Q) ∑_𝔟 S_𝔟 exp(γ_cmp(Q) 𝔟 2^𝔮) ‖f‖_μ ‖h‖_μ`,
`r = q^{-1/2}`. The admissibility (`lem:majorant`) is replaced by this direct monotonicity in `q`
(`cmpLambda0_anti`, `cmpGamma_anti`). -/
theorem extraction_compressed_buckets_at (hW : WeilBound F) (G : OrientedGraph U)
    (ς : U → U → ℤ) (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1)
    (hanti : ∀ j k, ς k j = -ς j k) (hne : (injLabellings F G).Nonempty) {n : ℕ}
    (hn : Fintype.card U ≤ n) {Q : ℝ} (hQ : 0 < Q) (hQq : Q ≤ Fintype.card F)
    (hS1 : leafEhat G Q n < 1)
    {Δ : ℕ} (hΔ : ∀ i, cmpDeg G ς i ≤ Δ) (Ex : Finset (U × U))
    (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex)) {k : ℕ}
    (wit : Finset (U × U) × Finset (U × U) → Fin k → U × U)
    (cx cz : Finset (U × U) × Finset (U × U) → Finset U)
    (ck : Finset (U × U) × Finset (U × U) → ℝ)
    (bucket : Finset (U × U) × Finset (U × U) → ℕ) (𝔮 : ℕ)
    (hwit : ∀ c ∈ 𝔓, IsWitness Ex c.1 c.2 (wit c))
    (hcov : ∀ c ∈ 𝔓, IsCover Ex c.1 c.2 (wit c) (cx c) (cz c))
    (hck : ∀ c ∈ 𝔓, 0 ≤ ck c)
    (hker : ∀ c ∈ 𝔓, Sarkozy.Influence.OpBound (injTuples F (witV (wit c))) (injTuples F (witW (wit c)))
      (rectKer ς c.1 (witV (wit c)) (witW (wit c))) (ck c * Real.sqrt (Fintype.card F) ^ k))
    (hbucket : ∀ c ∈ 𝔓, cmpOc G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c) ≤
      (bucket c : ℝ) * 2 ^ 𝔮)
    (f h : (U → F) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      (Real.sqrt (Fintype.card F))⁻¹ ^ k * cmpLambda0 G ς Q n (leafEhat G Q n) k *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          ck c * Real.sqrt (2 ^ cmpEx G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c))
            (cx c) (cz c))) * Real.exp (cmpGamma Q n Δ * (b * 2 ^ 𝔮))) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  have hEq : leafEhat G (Fintype.card F) n ≤ leafEhat G Q n := leafEhat_anti G hQ hQq
  have hb := extraction_compressed_buckets hW G ς hς hanti hne hn
    (fun i => coarseError_le_leafEhat G _ n i) (lt_of_le_of_lt hEq hS1) hΔ Ex hEx 𝔓 h𝔓 wit cx
    cz ck bucket 𝔮 hwit hcov hck hker hbucket f h
  refine hb.trans ?_
  have hL := cmpLambda0_anti G ς n k hQ hQq hS1
  have hS : ∀ b ∈ 𝔓.image bucket, 0 ≤ ∑ c ∈ 𝔓.filter (fun c => bucket c = b),
      ck c * Real.sqrt (2 ^ cmpEx G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c))
        (cx c) (cz c)) := fun b _ =>
    sum_nonneg fun c hc => mul_nonneg (hck c (mem_filter.mp hc).1) (Real.sqrt_nonneg _)
  have hSig := cmp_bucketSum_anti (𝔓.image bucket) _ hS (fun b => b) 𝔮 n Δ hQ hQq
  have hL0 : 0 ≤ cmpLambda0 G ς (Fintype.card F) n (leafEhat G (Fintype.card F) n) k := by
    unfold cmpLambda0
    have heq : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n < 1 := fun i =>
      lt_of_le_of_lt (coarseError_le_leafEhat G _ n i) (lt_of_le_of_lt hEq hS1)
    have h1 : 0 < 1 - leafEhat G (Fintype.card F) n := by linarith [lt_of_le_of_lt hEq hS1]
    exact div_nonneg (by positivity)
      (mul_nonneg (pow_pos h1 k).le (prod_nonneg fun i _ => by linarith [heq i]))
  have hSig0 : 0 ≤ ∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
      ck c * Real.sqrt (2 ^ cmpEx G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c))
        (cx c) (cz c))) * Real.exp (cmpGamma (Fintype.card F) n Δ * (b * 2 ^ 𝔮)) :=
    sum_nonneg fun b hb => mul_nonneg (hS b hb) (Real.exp_pos _).le
  have hN : 0 ≤ Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
      Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by positivity
  have hr : 0 ≤ (Real.sqrt (Fintype.card F))⁻¹ ^ k := by positivity
  calc (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        cmpLambda0 G ς (Fintype.card F) n (leafEhat G (Fintype.card F) n) k *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          ck c * Real.sqrt (2 ^ cmpEx G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c))
            (cx c) (cz c))) * Real.exp (cmpGamma (Fintype.card F) n Δ * (b * 2 ^ 𝔮))) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2))
      = (Real.sqrt (Fintype.card F))⁻¹ ^ k *
          (cmpLambda0 G ς (Fintype.card F) n (leafEhat G (Fintype.card F) n) k *
          (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
            ck c * Real.sqrt (2 ^ cmpEx G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c))
              (cx c) (cz c))) * Real.exp (cmpGamma (Fintype.card F) n Δ * (b * 2 ^ 𝔮)))) *
          (Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
          Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2))) := by ring
    _ ≤ (Real.sqrt (Fintype.card F))⁻¹ ^ k *
          (cmpLambda0 G ς Q n (leafEhat G Q n) k *
          (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
            ck c * Real.sqrt (2 ^ cmpEx G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c))
              (cx c) (cz c))) * Real.exp (cmpGamma Q n Δ * (b * 2 ^ 𝔮)))) *
          (Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
          Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2))) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hr) hN
        exact mul_le_mul hL hSig hSig0 (le_trans hL0 hL)
    _ = _ := by ring

end AntiBuckets

section AntiTwo

variable {p : ℕ} [Fact p.Prime]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **`cor:extraction-compressed`, the buckets at `Q ≤ p` for witnesses of size two over `𝔽_p`**,
with `c_ker(𝒞) = 2^{β(𝒞)} ∈ {1, 2}` (`lem:matching:kernel`; hypothesis `FourCycleBound p`). -/
theorem extraction_compressed_buckets_two_at (hp2 : p ≠ 2) (h4 : FourCycleBound p)
    (hW : WeilBound (ZMod p)) (G : OrientedGraph U)
    (ς : U → U → ℤ) (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1)
    (hanti : ∀ j k, ς k j = -ς j k) (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ}
    (hn : Fintype.card U ≤ n) {Q : ℝ} (hQ : 0 < Q) (hQp : Q ≤ p) (hS1 : leafEhat G Q n < 1)
    {Δ : ℕ} (hΔ : ∀ i, cmpDeg G ς i ≤ Δ) (Ex : Finset (U × U))
    (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex))
    (wit : Finset (U × U) × Finset (U × U) → Fin 2 → U × U)
    (cx cz : Finset (U × U) × Finset (U × U) → Finset U)
    (bucket : Finset (U × U) × Finset (U × U) → ℕ) (𝔮 : ℕ)
    (hwit : ∀ c ∈ 𝔓, IsWitness Ex c.1 c.2 (wit c))
    (hcov : ∀ c ∈ 𝔓, IsCover Ex c.1 c.2 (wit c) (cx c) (cz c))
    (hbucket : ∀ c ∈ 𝔓, cmpOc G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c) ≤
      (bucket c : ℝ) * 2 ^ 𝔮)
    (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      (Real.sqrt p)⁻¹ ^ 2 * cmpLambda0 G ς Q n (leafEhat G Q n) 2 *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          (2 : ℝ) ^ twoCycleCount (witnessIdx c.1 (wit c)) *
            Real.sqrt (2 ^ cmpEx G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c))
              (cx c) (cz c))) * Real.exp (cmpGamma Q n Δ * (b * 2 ^ 𝔮))) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  have hQq : Q ≤ (Fintype.card (ZMod p) : ℝ) := by rw [ZMod.card]; exact hQp
  have h := extraction_compressed_buckets_at hW G ς hς hanti hne hn hQ hQq hS1 hΔ Ex hEx 𝔓 h𝔓
    wit cx cz (fun c => (2 : ℝ) ^ twoCycleCount (witnessIdx c.1 (wit c))) bucket 𝔮 hwit hcov
    (fun c _ => by positivity) (fun c hc => ?_) hbucket f h
  · rw [ZMod.card] at h
    exact h
  have hςP : ∀ e ∈ c.1, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1 :=
    sign_pm_of_ne_zero hς fun e he => hEx e (h𝔓.1 c hc |>.1 he)
  have hker := Sarkozy.ExtractionK.IsWitness.rectKer_opBound_twoCycles (hwit c hc) hp2 h4 ς hςP
    (cmp_component_card_le_two (witnessIdx c.1 (wit c)))
  rw [ZMod.card]
  exact hker

end AntiTwo

end Sarkozy.ExtractionK
