module

public import Sarkozy.PaperFrame.FibreCore
public import Sarkozy.Functional.ScaleConditions

@[expose] public section

/-!
# The paper's tail family `𝒯_N` (`def:record:functional`(a))

`def:record:functional`(a) takes the tail primes `𝒯_N = {p prime : P₄ ≤ p ≤ N^β}`,
`N = KL`, `β = 1/20`. `tailPrimes P₄ L` is this set for an arbitrary lower bound `P₄` (the
paper's `P₄ = 2^512`; nothing is evaluated), written with `p^{20} ≤ N` in place of
`p ≤ N^{1/20}` so that it is a decidable filter of a range. For it, the two-scale
hypotheses of `fibreScale_restoration_paper` and `paper_fibre_energy_le` hold automatically:

* `tailPrimes_prime`: its elements are primes;
* `tailPrimes_mono`: `ℓ ≤ L → 𝒯_{Kℓ} ⊆ 𝒯_{KL}`;
* `tailPrimes_large`: the primes of `𝒯_{KL} \ 𝒯_{Kℓ}` exceed `(Kℓ)^{1/20}`.

`paper_fibre_energy_le_canonical` is the fibre energy bound for this family, for intervals
`|I| ≤ N`, with these hypotheses discharged.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.PaperFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.Comparison

/-- The tail primes `𝒯_N = {p prime : P₄ ≤ p, p^{20} ≤ N}` at the scale `L`, `N = KL`. -/
def tailPrimes (P4 L : ℕ) : Finset ℕ :=
  (range (blockScale * L + 1)).filter fun q => q.Prime ∧ P4 ≤ q ∧ q ^ 20 ≤ blockScale * L

theorem mem_tailPrimes {P4 L q : ℕ} :
    q ∈ tailPrimes P4 L ↔ q.Prime ∧ P4 ≤ q ∧ q ^ 20 ≤ blockScale * L := by
  unfold tailPrimes
  rw [mem_filter, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have h1 : q ≤ q ^ 20 := Nat.le_self_pow (by norm_num) q
    omega

instance tailPrimes_neZero (P4 L : ℕ) (j : ↥(tailPrimes P4 L)) : NeZero (j : ℕ) :=
  ⟨(mem_tailPrimes.mp j.2).1.ne_zero⟩

theorem tailPrimes_prime (P4 L : ℕ) : ∀ q ∈ tailPrimes P4 L, q.Prime :=
  fun _ hq => (mem_tailPrimes.mp hq).1

theorem tailPrimes_mono (P4 : ℕ) {ℓ L : ℕ} (h : ℓ ≤ L) : tailPrimes P4 ℓ ⊆ tailPrimes P4 L := by
  intro q hq
  obtain ⟨h1, h2, h3⟩ := mem_tailPrimes.mp hq
  exact mem_tailPrimes.mpr ⟨h1, h2, h3.trans (Nat.mul_le_mul_left _ h)⟩

/-- The primes of `𝒯_{KL}` missing from `𝒯_{Kℓ}` exceed the cutoff `(Kℓ)^{1/20}`. -/
theorem tailPrimes_large (P4 : ℕ) {ℓ L : ℕ} :
    ∀ q ∈ tailPrimes P4 L, q ∉ tailPrimes P4 ℓ → paperCutoff (blockScale * ℓ) < q := by
  intro q hq hq'
  obtain ⟨h1, h2, _⟩ := mem_tailPrimes.mp hq
  have h4 : blockScale * ℓ < q ^ 20 := by
    by_contra hcon
    exact hq' (mem_tailPrimes.mpr ⟨h1, h2, not_lt.mp hcon⟩)
  have h5 : ((blockScale * ℓ : ℕ) : ℝ) < (q : ℝ) ^ (20 : ℕ) := by exact_mod_cast h4
  unfold paperCutoff liftExponent
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  calc ((blockScale * ℓ : ℕ) : ℝ) ^ ((1 : ℝ) / 20)
      < ((q : ℝ) ^ (20 : ℕ)) ^ ((1 : ℝ) / 20) :=
        Real.rpow_lt_rpow (Nat.cast_nonneg _) h5 (by norm_num)
    _ = q := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq0]
        norm_num

/-- The child scale `ℓ = ⌈M/(KR)⌉` of a square step on an interval of length `M ≤ N = KL`
satisfies `ℓ ≤ L`. -/
theorem stepScale_le_scale {L M R : ℕ} (hR : 1 ≤ R) (hM : M ≤ blockScale * L) :
    stepScale blockScale M R ≤ L := by
  have h := stepScale_mul_le (K := blockScale) (L := L) (M := M) (R := R)
    (by norm_num [blockScale]) hR hM
  exact Nat.le_of_mul_le_mul_left h (by norm_num [blockScale])

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]

/-- **The fibre energy bound for the paper's tail family** (`𝒯_N` with the lower bound `P₄`):
`paper_fibre_energy_le` with the two-scale hypotheses discharged, for intervals `|I| ≤ N`. -/
theorem paper_fibre_energy_le_canonical (P4 : ℕ) {L : ℕ}
    (E : Finset (J₀ ⊕ ↥(tailPrimes P4 L)))
    (hpair : Pairwise fun i j => (joinModuli m₀ (tailModuli (tailPrimes P4) L) i).Coprime
      (joinModuli m₀ (tailModuli (tailPrimes P4) L) j))
    (z : ResidueSpace (joinModuli m₀ (tailModuli (tailPrimes P4) L))) {D0 : ℕ} (hD0 : 1 ≤ D0)
    (s : ZMod D0) (hcop0 : ∀ k, D0.Coprime (joinModuli m₀ (tailModuli (tailPrimes P4) L) k))
    {A : Finset ℤ} (hA : IsSquareDifferenceFree A) (c : ℤ) {M : ℕ} (hM : 1 ≤ M)
    (hMN : M ≤ blockScale * L)
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hμ₀ : ∀ (a : ∀ i, (ZMod (m₀ i))ˣ) (b : ResidueSpace m₀),
      (∀ i, IsSquare ((a i : ZMod (m₀ i)))) → ∀ F : (Slot → ResidueSpace m₀) → ℝ,
        μ₀.expect (fun z => F (fun v => piAffineEquiv m₀ a b (z v))) = μ₀.expect F)
    (hμp : ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (b : ZMod q), IsSquare (a : ZMod q) →
      ∀ F : (Slot → ZMod q) → ℝ,
        (μp q).expect (fun z => F (fun v => affineEquiv a b (z v))) = (μp q).expect F)
    {C : ℝ} (hC : 0 ≤ C)
    (hind : EnergyUpperBoundAt (prefixedFunctional m₀ (J := fun L => ↥(tailPrimes P4 L))
      (fun _ j => (j : ℕ)) (paperLaw m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp))
      C (stepScale blockScale M
        (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) k)))) :
    diagonalIntegral (signedIntegral
        (paperLaw m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp L).weight)
        (fun x => (squareStepModel (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E z s A
          (Icc (c + 1) (c + M)) c M
          (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) k))
          (blockScale * stepScale blockScale M
            (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) k)))
          (paperCutoff (blockScale * stepScale blockScale M
            (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) k))))
          ((splitEquiv m₀ (tailModuli (tailPrimes P4) L)).symm x)).re) ≤
      ((leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) k) *
            (blockScale * stepScale blockScale M
              (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) k))) :
              ℝ) / M) ^ 72 *
        (C * (stepScale blockScale M
            (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) k)) : ℝ) ^
              (-decay)) *
        (((((D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) k : ℕ) : ℝ) / M) *
            ((A ∩ Icc (c + 1) (c + M)).filter
              (InFibre (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E z s)).card) /
          ((leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) k) *
            (blockScale * stepScale blockScale M
              (leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) k))) :
              ℝ) / M)) ^ densityExponent := by
  have hℓ := stepScale_le_scale (L := L) (M := M)
    (R := leastSquare (D0 * ∏ k ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) k))
    (leastSquare_pos _) hMN
  exact paper_fibre_energy_le m₀ (tailPrimes P4) E hpair z hD0 s hcop0 hA c hM
    (tailPrimes_mono P4 hℓ) (tailPrimes_prime P4 L) (tailPrimes_large P4)
    μ₀ μp hp₀ hpp hμ₀ hμp hC hind

end Sarkozy.PaperFrame
