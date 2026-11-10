module

public import Sarkozy.DensityChain2.Restoration

@[expose] public section

/-!
# Restoration for the paper's tail family `𝒯_N` (`lem:record:fibre-scale`(c))

The paper's tail at the scale `L` is `𝒯_N = {p prime : P₄ ≤ p ≤ N^β}`, `N = KL`
(`CancellationSteps.paperTailPrimes`, `def:construction`(a)). It is monotone in `L`, and a prime
of `𝒯_N` missing from `𝒯_n` (`n = Kℓ`, `ℓ ≤ L`) exceeds `n^β`. So `Restoration.envHrest_block`
and `fixHrest_block` apply to it:

* `paperTailPrimes_mono`, `paperTailPrimes_prime`, `paperTailPrimes_large`;
* **`envHrest_paper`**, **`fixHrest_paper`**: the restoration conjunct of DC1's `_hterms`
  (`DensityChain.envMeanBoundL/R_paper_restoration`, `fixMeanBound_of_restoration`), for every
  comparison data on the paper's tail (`p = paperTail`), every term, residue index and slot.
-/

namespace Sarkozy.DensityChain2

open Filter Finset Function
open scoped BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.DensityDC Sarkozy.CancellationSteps

theorem paperTailPrimes_mono {ℓ L : ℕ} (h : ℓ ≤ L) : paperTailPrimes ℓ ⊆ paperTailPrimes L := by
  intro q hq
  rw [mem_paperTailPrimes] at hq ⊢
  refine ⟨hq.1, hq.2.1, hq.2.2.trans ?_⟩
  unfold Functional.paperCutoff
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.mul_le_mul_left _ h)
    (by norm_num [Functional.liftExponent])

theorem paperTailPrimes_prime (L : ℕ) : ∀ q ∈ paperTailPrimes L, q.Prime :=
  fun _ hq => (mem_paperTailPrimes.mp hq).1

theorem paperTailPrimes_large {ℓ L : ℕ} (_h : ℓ ≤ L) :
    ∀ q ∈ paperTailPrimes L, q ∉ paperTailPrimes ℓ →
      Functional.paperCutoff (blockScale * ℓ) < q := by
  intro q hq hn
  rw [mem_paperTailPrimes] at hq hn
  by_contra hle
  exact hn ⟨hq.1, hq.2.1, not_lt.mp hle⟩

instance paperTail_neZero' (L : ℕ) (j : ↥(paperTailPrimes L)) : NeZero (j : ℕ) :=
  ⟨(paperTailPrimes_prime L j.1 j.2).ne_zero⟩

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

omit [DecidableEq P] in
/-- **Restoration for `envC` on the paper's tail** (`lem:record:fibre-scale`(c)): the restoration
conjunct of the per-term hypothesis `_hterms` of `DensityChain.envMeanBoundL/R_paper_restoration`
(with `u = D.index.u` or `D.index.w`), at every scale. -/
theorem envHrest_paper (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (u : E → reservedCut.Half) (L : ℕ)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (f g : BlockAtom Bk PaperJt L → Bool) :
    ∀ ω v, ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk paperTail L) (termSet f g)
        (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk paperTail (prefix_pairwise (hpair L))
          D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk paperTail L) (termSet f g)
            (paperCutoff (blockScale * stepEll (crtModuli m₀ blk paperTail L) (termSet f g)
              (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1)) B
            (blockScale * stepEll (crtModuli m₀ blk paperTail L)
            (termSet f g) (envSlots hcop u L Jq ω v).1
            (envSlots hcop u L Jq ω v).2.2.1)) ≤
        D.Y (stepEll (crtModuli m₀ blk paperTail L) (termSet f g) (envSlots hcop u L Jq ω v).1
          (envSlots hcop u L Jq ω v).2.2.1) B :=
  envHrest_block (T := paperTailPrimes) hcop D (fun _ _ => paperTailPrimes_mono)
    paperTailPrimes_prime (fun _ _ => paperTailPrimes_large) hpair u L Jq f g

omit [DecidableEq P] in
/-- **Restoration for `fixC` on the paper's tail** (`lem:record:fibre-scale`(c)): the restoration
conjunct of the per-term hypothesis `_hterms` of `DensityChain.fixMeanBound_of_restoration`. -/
theorem fixHrest_paper (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (u : E → reservedCut.Half) (L : ℕ) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (f g : BlockAtom Bk PaperJt L → Bool) :
    ∀ ω v, ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk paperTail L) (termSet f g)
        (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk paperTail (prefix_pairwise (hpair L))
          D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk paperTail L) (termSet f g)
            (paperCutoff (blockScale * stepEll (crtModuli m₀ blk paperTail L) (termSet f g)
              (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1)) B
            (blockScale * stepEll (crtModuli m₀ blk paperTail L)
            (termSet f g) (fixSlots hcop u L S t Jq ω v).1
            (fixSlots hcop u L S t Jq ω v).2.2.1)) ≤
        D.Y (stepEll (crtModuli m₀ blk paperTail L) (termSet f g)
          (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1) B :=
  fixHrest_block (T := paperTailPrimes) hcop D (fun _ _ => paperTailPrimes_mono)
    paperTailPrimes_prime (fun _ _ => paperTailPrimes_large) hpair u L S t Jq f g


omit [DecidableEq P] in
/-- **Restoration at the folded slot data of `envC`** (`lem:record:fibre-scale`(c)): the input
`hrest` of DC2's `DensityFibre.env_fold_le_chain` (`prop:record:density-structured` for a folded
energy, `lem:record:folded-energy`), at the slot data `envSlots ∘ fo` for any fold map `fo`, with
the paper's cutoffs `Q' v = Q(K ℓ_v)`, for any set `Es` of selected atoms. -/
theorem envFoldHrest_paper (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (u : E → reservedCut.Half) (L : ℕ)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (fo : Slot → Slot)
    (Es : Finset (BlockAtom Bk PaperJt L)) :
    ∀ v, ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk paperTail L) Es
        (envSlots hcop u L Jq ω (fo v)).1 (envSlots hcop u L Jq ω (fo v)).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk paperTail (prefix_pairwise (hpair L))
          D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk paperTail L) Es
            (paperCutoff (blockScale * stepEll (crtModuli m₀ blk paperTail L) Es
              (envSlots hcop u L Jq ω (fo v)).1 (envSlots hcop u L Jq ω (fo v)).2.2.1)) B
            (blockScale * stepEll (crtModuli m₀ blk paperTail L) Es
              (envSlots hcop u L Jq ω (fo v)).1 (envSlots hcop u L Jq ω (fo v)).2.2.1)) ≤
        D.Y (stepEll (crtModuli m₀ blk paperTail L) Es (envSlots hcop u L Jq ω (fo v)).1
          (envSlots hcop u L Jq ω (fo v)).2.2.1) B := by
  intro v B _
  have hM : (envSlots hcop u L Jq ω (fo v)).2.2.1 ≤ blockScale * L := by
    rw [envSlots_len hcop u L Jq ω (fo v)]
    unfold envM
    split
    · exact Nat.le_mul_of_pos_left L (by norm_num [blockScale])
    · exact le_rfl
  exact hrest_block (T := paperTailPrimes) D (fun ℓ hℓ => paperTailPrimes_mono hℓ)
    (paperTailPrimes_prime L) (fun ℓ hℓ => paperTailPrimes_large hℓ) _ hpair Es _ _ hM B

omit [DecidableEq P] in
/-- **Restoration at the folded slot data of `fixC`**: the input `hrest` of DC2's
`DensityFibre.fix_fold_le_chain`, at `fixSlots ∘ fo`, with the paper's cutoffs. -/
theorem fixFoldHrest_paper (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (u : E → reservedCut.Half) (L : ℕ) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (fo : Slot → Slot)
    (Es : Finset (BlockAtom Bk PaperJt L)) :
    ∀ v, ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk paperTail L) Es
        (fixSlots hcop u L S t Jq ω (fo v)).1 (fixSlots hcop u L S t Jq ω (fo v)).2.2.1 : ℕ) :
          ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk paperTail (prefix_pairwise (hpair L))
          D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk paperTail L) Es
            (paperCutoff (blockScale * stepEll (crtModuli m₀ blk paperTail L) Es
              (fixSlots hcop u L S t Jq ω (fo v)).1 (fixSlots hcop u L S t Jq ω (fo v)).2.2.1)) B
            (blockScale * stepEll (crtModuli m₀ blk paperTail L) Es
              (fixSlots hcop u L S t Jq ω (fo v)).1 (fixSlots hcop u L S t Jq ω (fo v)).2.2.1)) ≤
        D.Y (stepEll (crtModuli m₀ blk paperTail L) Es (fixSlots hcop u L S t Jq ω (fo v)).1
          (fixSlots hcop u L S t Jq ω (fo v)).2.2.1) B := by
  intro v B _
  have hM : (fixSlots hcop u L S t Jq ω (fo v)).2.2.1 ≤ blockScale * L := by
    rw [fixSlots_len hcop u L S t Jq ω (fo v)]
    unfold fixM
    have hL : L ≤ blockScale * L := Nat.le_mul_of_pos_left L (by norm_num [blockScale])
    split
    · split_ifs
      · exact hL
      · exact le_rfl
    · exact le_rfl
  exact hrest_block (T := paperTailPrimes) D (fun ℓ hℓ => paperTailPrimes_mono hℓ)
    (paperTailPrimes_prime L) (fun ℓ hℓ => paperTailPrimes_large hℓ) _ hpair Es _ _ hM B

end Sarkozy.DensityChain2
