module

public import Sarkozy.JointRows.CollExpansion

/-!
# The nonstar part of a pinned row as a form bound (`prop:pinned-extraction`)

Source: `paper/sections/16_extraction.tex`, `prop:pinned-extraction` (the bucket sum `N^pin`)
and `lem:joint-rows`(a) (`N_• ≥ ‖T^•_ns‖ + ‖T^•_coll‖` on `L²(μ)`).

* `NsCert F ϖ ς`: the class data of `prop:pinned-extraction` for the nonstar subsets of `E_×`,
  i.e. the hypotheses of X1's `ExtractionK.pinned_extraction_buckets` with `Ex = E_×`: an exact
  partition into classes with witnesses of size two, covers, kernel constants `c_ker(𝒞)` with
  their rectangle bounds, and bucket indices. `NsCert.bound` is the resulting constant
  `r² Λ^pin_0 2^{2ϖ} ∑_𝔟 (…) exp(γ_pin 2^ϖ 𝔟 2^𝔮)`.
* `formBound_of_normalized`: for `μ` uniform on `s`, a bound of `|E_μ⊗μ f K h|` written with
  `E_μ = |s|⁻¹ ∑_s` is `FormBound μ K`.
* `formBound_nsKer`: **`‖T^•_ns‖ ≤ NsCert.bound` on `L²(μ)`**, `μ = λ(· | 𝓘_pin)`.
* `NsCert.ofEmpty`: the certificate for sign data without pairs (non-vacuity of the structure;
  then `T_ns = 0`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows

open Sarkozy.FiveType

namespace Coll

/-- **The class data of `prop:pinned-extraction`** for the nonstar part of a pinned row with sign
data `ς` (the hypotheses of X1's `ExtractionK.pinned_extraction_buckets` for `Ex = E_×`). -/
structure NsCert (F : Type*) [Field F] [Fintype F] [DecidableEq F] {nv : ℕ} (ϖ : ℕ)
    (ς : Fin nv → Fin nv → ℤ) where
  /-- `Δ_pin`. -/
  Δ : ℕ
  hΔX : ∀ i, ϖ + (ExtractionK.pinNX ς i).card ≤ Δ
  hΔY : ∀ i, ϖ + (ExtractionK.pinNY ς i).card ≤ Δ
  /-- The exact partition of the nonstar subsets of `E_×` into classes `𝒞(P, A)`. -/
  𝔓 : Finset (Finset (Fin nv × Fin nv) × Finset (Fin nv × Fin nv))
  h𝔓 : Extraction.IsExactPartition (pairSet ς) 𝔓 (Extraction.nonstars (pairSet ς))
  /-- The witnesses, of size two. -/
  wit : Finset (Fin nv × Fin nv) × Finset (Fin nv × Fin nv) → Fin 2 → Fin nv × Fin nv
  /-- The covers. -/
  cx : Finset (Fin nv × Fin nv) × Finset (Fin nv × Fin nv) → Finset (Fin nv)
  cz : Finset (Fin nv × Fin nv) × Finset (Fin nv × Fin nv) → Finset (Fin nv)
  /-- The kernel constants `c_ker(𝒞)`. -/
  ck : Finset (Fin nv × Fin nv) × Finset (Fin nv × Fin nv) → ℝ
  /-- The bucket indices `𝔟(𝒞)`, with the scale `2^𝔮`. -/
  bucket : Finset (Fin nv × Fin nv) × Finset (Fin nv × Fin nv) → ℕ
  𝔮 : ℕ
  hwit : ∀ c ∈ 𝔓, Extraction.IsWitness (pairSet ς) c.1 c.2 (wit c)
  hcov : ∀ c ∈ 𝔓, Extraction.IsCover (pairSet ς) c.1 c.2 (wit c) (cx c) (cz c)
  hck : ∀ c ∈ 𝔓, 0 ≤ ck c
  hker : ∀ c ∈ 𝔓, Influence.OpBound (ExtractionK.injTuples F (ExtractionK.witV (wit c)))
    (ExtractionK.injTuples F (ExtractionK.witW (wit c)))
    (ExtractionK.rectKer (F := F) ς c.1 (ExtractionK.witV (wit c)) (ExtractionK.witW (wit c)))
    (ck c * Real.sqrt (Fintype.card F) ^ 2)
  hbucket : ∀ c ∈ 𝔓, ExtractionK.peOc (pairSet ς \ (c.1 ∪ c.2)) (ExtractionK.witV (wit c))
    (ExtractionK.witW (wit c)) (cx c) (cz c) ≤ (bucket c : ℝ) * 2 ^ 𝔮

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {nv : ℕ}

/-- **The constant of `prop:pinned-extraction`** for a certificate (`z = |𝓜|`). -/
noncomputable def NsCert.bound {ϖ : ℕ} {ς : Fin nv → Fin nv → ℤ} (c : NsCert F ϖ ς) (z : ℕ) :
    ℝ :=
  (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * ExtractionK.peLambda0 (Fintype.card F) nv z ϖ c.Δ *
    2 ^ (2 * ϖ) *
    (∑ b ∈ c.𝔓.image c.bucket, (∑ d ∈ c.𝔓.filter (fun d => c.bucket d = b),
      c.ck d * Real.sqrt (2 ^ (((pairSet ς \ (d.1 ∪ d.2)).filter
        (fun e => e.1 ∈ ExtractionK.witV (c.wit d))).card +
        ((pairSet ς \ (d.1 ∪ d.2)).filter (fun e => e.2 ∈ ExtractionK.witW (c.wit d))).card))) *
      Real.exp (ExtractionK.peGamma (Fintype.card F) nv z c.Δ * 2 ^ ϖ * (b * 2 ^ c.𝔮)))

section Bridge

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Form bound from a normalized bilinear bound**, for `μ` uniform on `s`. -/
theorem formBound_of_normalized (μ : FiniteLaw Ω) (s : Finset Ω)
    (hμ : ∀ x, μ.weight x = if x ∈ s then ((s.card : ℝ))⁻¹ else 0) (K : Ω → Ω → ℝ) {C : ℝ}
    (h : ∀ f g : Ω → ℝ, |(∑ x ∈ s, ∑ y ∈ s, f x * K x y * g y) / (s.card : ℝ) ^ 2| ≤
      C * Real.sqrt ((∑ x ∈ s, f x ^ 2) / s.card) * Real.sqrt ((∑ x ∈ s, g x ^ 2) / s.card)) :
    FormBound μ K C := by
  intro Φ Ψ
  set N : ℝ := (s.card : ℝ) with hN
  have hμs : ∀ x ∈ s, μ.weight x = N⁻¹ := fun x hx => by
    rw [hμ]
    simp only [hx, ↓reduceIte]
  have hμn : ∀ x, x ∉ s → μ.weight x = 0 := fun x hx => by
    rw [hμ]
    simp only [hx, ↓reduceIte]
  have hkf : kf μ K Φ Ψ = (∑ x ∈ s, ∑ y ∈ s, Φ x * K x y * Ψ y) / N ^ 2 := by
    unfold kf
    rw [← Finset.sum_subset (Finset.subset_univ s), Finset.sum_div]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [← Finset.sum_subset (Finset.subset_univ s), Finset.sum_div]
      · refine Finset.sum_congr rfl fun y hy => ?_
        rw [hμs x hx, hμs y hy, div_eq_mul_inv, ← inv_pow]
        ring
      · intro y _ hy
        rw [hμn y hy, mul_zero, zero_mul]
    · intro x _ hx
      simp only [hμn x hx, zero_mul, Finset.sum_const_zero]
  have hnrm : ∀ U : Ω → ℝ, nrm μ U = Real.sqrt ((∑ x ∈ s, U x ^ 2) / N) := by
    intro U
    unfold nrm ip FiniteLaw.expect
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ s), Finset.sum_div]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [hμs x hx, div_eq_mul_inv]
      ring
    · intro x _ hx
      rw [hμn x hx, zero_mul]
  rw [hkf, hnrm, hnrm]
  exact h Φ Ψ

end Bridge

variable {p : ℕ} [Fact p.Prime]

/-- **`prop:pinned-extraction` as a form bound on `L²(μ)`**, `μ = λ(· | 𝓘_pin)`: the nonstar
kernel `nsKer ς` relative to `μ ⊗ μ` has `‖T_ns‖ ≤ NsCert.bound`, from X1's
`ExtractionK.pinned_extraction_buckets`. -/
theorem formBound_nsKer (hW : Labellings.WeilBound (ZMod p)) (M : Finset (ZMod p))
    (pin : Fin nv → ZMod p → ℤ) (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, ExtractionK.pinCount pin j ≤ ϖ)
    (he : ExtractionK.ePin p nv M.card ϖ < 1) (ς : Fin nv → Fin nv → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (c : NsCert (ZMod p) ϖ ς)
    (lam : FiniteLaw (Lab p nv)) (I : Lab p nv → Prop)
    (hI : ∀ x, I x ↔ x ∈ ExtractionK.pinLab M pin)
    (hlam : ∀ x y, x ∈ ExtractionK.pinLab M pin → y ∈ ExtractionK.pinLab M pin →
      lam.weight x = lam.weight y)
    (hP : 0 < Peyre.prob lam I) :
    FormBound (Peyre.condLaw lam I hP) (nsKer ς) (c.bound M.card) := by
  have hcard : ((Fintype.card (ZMod p) : ℕ) : ℝ) = p := by rw [ZMod.card]
  have he' : ExtractionK.ePin (Fintype.card (ZMod p)) nv M.card ϖ < 1 := by
    rw [hcard]
    exact he
  have hEx : ∀ e ∈ pairSet ς, ς e.1 e.2 ≠ 0 := fun e he => (Finset.mem_filter.mp he).2
  refine formBound_of_normalized _ _ (condLaw_weight_of_const lam I _ hI hlam hP) _ ?_
  intro f g
  exact ExtractionK.pinned_extraction_buckets hW M pin hpin hpinM ϖ hϖ he' ς hς c.hΔX c.hΔY
    (pairSet ς) hEx c.𝔓 c.h𝔓 c.wit c.cx c.cz c.ck c.bucket c.𝔮 c.hwit c.hcov c.hck c.hker
    c.hbucket f g

/-- **A certificate for sign data without pairs** (then `E_× = ∅` and `T_ns = 0`): non-vacuity of
`NsCert` (`i0` is any coordinate, used for the unused witnesses). -/
def NsCert.ofEmpty (ϖ : ℕ) (i0 : Fin nv) : NsCert F ϖ (fun _ _ : Fin nv => (0 : ℤ)) where
  Δ := ϖ
  hΔX i := by simp [ExtractionK.pinNX]
  hΔY i := by simp [ExtractionK.pinNY]
  𝔓 := ∅
  h𝔓 := by
    have h0 : pairSet (fun _ _ : Fin nv => (0 : ℤ)) = ∅ := by
      simp [pairSet]
    have h1 : Extraction.nonstars (pairSet (fun _ _ : Fin nv => (0 : ℤ))) = ∅ := by
      rw [h0]
      unfold Extraction.nonstars
      rw [Finset.powerset_empty, Finset.filter_singleton]
      simp [Extraction.IsNonstar]
    refine ⟨fun c hc => absurd hc (Finset.notMem_empty c), by simp, ?_⟩
    rw [h1, Finset.biUnion_empty]
  wit _ _ := (i0, i0)
  cx _ := ∅
  cz _ := ∅
  ck _ := 0
  bucket _ := 0
  𝔮 := 0
  hwit c hc := absurd hc (Finset.notMem_empty c)
  hcov c hc := absurd hc (Finset.notMem_empty c)
  hck c hc := absurd hc (Finset.notMem_empty c)
  hker c hc := absurd hc (Finset.notMem_empty c)
  hbucket c hc := absurd hc (Finset.notMem_empty c)

end Coll

end Sarkozy.JointRows
