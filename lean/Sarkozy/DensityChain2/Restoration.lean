module

public import Sarkozy.DensityChain.All

@[expose] public section

/-!
# Restoration on the paper's block atoms (`lem:record:fibre-scale`(c))

I1's `DensityDC.restoration_atomLaws` proves `lem:record:fibre-scale`(c) for a tensor of atom laws
with a prefix of single prime-power coordinates. On the paper's block atoms the prefix atoms are
the blocks `β`, read on the cyclic coordinates `ℤ/D_β` through the CRT (`crtRef`). This file
proves the restoration there, at the paper's objects:

* `crtRef_eq_atomLaws`: with a tail family `J L = ↥(T L)`, `p L j = j`, the cyclic-coordinate
  reference `crtRef` *is* I1's `atomLaws` with the block moduli `D_β` as prefix moduli and the
  CRT-pulled block laws `crtPrefixLaw β` as prefix laws (definitionally, atom by atom);
* `crtPrefixLaw_slotReflectionPositive`, `crtPrefixLaw_translate`: (R2) and (R3) (`r = 1`) of the
  pulled block laws, from the data's `Reference.rp₀`, `Reference.inv₀`;
* **`restoration_block`**: `Z_{μ_N}(h) ≤ Y(ℓ, B)` for the children `h = Re 𝓛^𝒮_{[Kℓ],(Kℓ)^β} 1_B`
  of any set `E` of block atoms, with `Y = D.Y` the data's reference energy, whenever
  `T ℓ ⊆ T L` and the primes of `T L \ T ℓ` exceed `(Kℓ)^β`;
* **`hrest_block`**: the same at every child scale `ℓ = stepEll E D₀ M` of an interval of length
  `M ≤ KL` (so `ℓ ≤ L`), for a monotone tail family whose new primes lie above the cutoff;
* `envHrest_block`, `fixHrest_block`: the restoration conjunct of DC1's `_hterms` for `envC`
  and `fixC`, for every term, residue index and slot.
-/

namespace Sarkozy.DensityChain2

open Filter Finset Function
open scoped BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.DensityDC

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {T : ℕ → Finset ℕ} [∀ L (j : ↥(T L)), NeZero (j : ℕ)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (blk) in
/-- The law `μ₀ β` of a prefix block read on the cyclic coordinate `ℤ/D_β` (CRT). -/
noncomputable def crtPrefixLaw (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β)) (β : Bk) :
    FiniteLaw (Slot → ZMod (blockModulus m₀ blk β)) :=
  pullFiniteLaw (ZMod.prodEquivPi (blockModuli m₀ blk β) (blockModuli_pairwise blk h0 β)).toEquiv
    (μ₀ β)

omit [Fintype Bk] in
/-- **The cyclic-coordinate reference is a tensor of atom laws**: for the tail family
`J L = ↥(T L)`, `crtRef` is I1's `atomLaws` with prefix moduli `D_β` and prefix laws
`crtPrefixLaw β`. -/
theorem crtRef_eq_atomLaws (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ) :
    crtRef (J := fun L => ↥(T L)) blk (tailModuli T) h0 μ₀ μp L =
      atomLaws (blockModulus m₀ blk) T (crtPrefixLaw blk h0 μ₀) μp L := by
  funext b
  cases b <;> rfl

omit [Fintype Bk] in
/-- (R2) of the pulled block laws. -/
theorem crtPrefixLaw_slotReflectionPositive (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (rp₀ : ∀ β, SlotReflectionPositive (signedIntegral (μ₀ β).weight)) (β : Bk) :
    SlotReflectionPositive (signedIntegral (crtPrefixLaw blk h0 μ₀ β).weight) := by
  unfold crtPrefixLaw
  rw [← pullLaw_signedIntegral]
  exact slotReflectionPositive_pullLaw _ (rp₀ β)

omit [Fintype Bk] in
/-- (R3) with `r = 1` of the pulled block laws: invariance under the simultaneous translations
of the slots, from the coordinatewise square-affine invariance `Reference.inv₀`. -/
theorem crtPrefixLaw_translate (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (inv₀ : ∀ β (a : ∀ i, (ZMod (blockModuli m₀ blk β i))ˣ) (b : BlockRes m₀ blk β),
      (∀ i, IsSquare ((a i : ZMod (blockModuli m₀ blk β i)))) →
        ∀ F : (Slot → BlockRes m₀ blk β) → ℝ,
          (μ₀ β).expect (fun z => F (fun v => piAffineEquiv (blockModuli m₀ blk β) a b (z v))) =
            (μ₀ β).expect F)
    (β : Bk) (r : ZMod (blockModulus m₀ blk β)) (F : (Slot → ZMod (blockModulus m₀ blk β)) → ℝ) :
    (crtPrefixLaw blk h0 μ₀ β).expect (fun z => F (fun v => z v + r)) =
      (crtPrefixLaw blk h0 μ₀ β).expect F := by
  have h := pullFiniteLaw_block_squareAffine blk h0 β (μ₀ β) (inv₀ β) 1 r isUnit_one
    ⟨1, (mul_one 1).symm⟩ F
  simp only [one_mul] at h
  exact h

/-- (R3) with `r = 1` of the tail laws, from `Reference.invp`. -/
theorem tail_translate (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (invp : ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (b : ZMod q), IsSquare (a : ZMod q) →
      ∀ F : (Slot → ZMod q) → ℝ,
        (μp q).expect (fun z => F (fun v => affineEquiv a b (z v))) = (μp q).expect F)
    (q : ℕ) [NeZero q] (r : ZMod q) (F : (Slot → ZMod q) → ℝ) :
    (μp q).expect (fun z => F (fun v => z v + r)) = (μp q).expect F := by
  have h := invp q 1 r ⟨1, by simp⟩ F
  have he : ∀ x : ZMod q, affineEquiv (1 : (ZMod q)ˣ) r x = x + r := by
    intro x
    change ((1 : (ZMod q)ˣ) : ZMod q) * x + r = x + r
    rw [Units.val_one, one_mul]
  simp only [he] at h
  exact h

/-- `F_A` (the unchanged input at `D₀ = 1`, `I = [N]`) is the whole lift of `1_A`. -/
theorem unchangedInput_eq_wholeLift {Jc : Type} [Fintype Jc] [DecidableEq Jc] (m : Jc → ℕ)
    [∀ j, NeZero (m j)] (Q : ℝ) (A : Finset ℤ) (L : ℕ) (y : ResidueSpace m) :
    unchangedInput m Q A L y = (wholeLift m Q (blockScale * L) A y).re := by
  unfold unchangedInput input wholeLift
  rw [inputFun_of_eq_one rfl]


omit [DecidableEq P] in
/-- **`lem:record:fibre-scale`(c) on the paper's block atoms**: for a tail family
`J L = ↥(T L)` of primes with `T ℓ ⊆ T L` whose primes missing from `T ℓ` exceed `(Kℓ)^β`, the
children `h = Re 𝓛^𝒮_{[Kℓ],(Kℓ)^β} 1_B` of any set `E` of block atoms satisfy
`Z_{μ_N}(h) ≤ Y(ℓ, B)`, with `μ_N = ⊗_𝔟 crtRef_𝔟` the reference on the cyclic coordinates and
`Y = D.Y` the data's reference energy. -/
theorem restoration_block (D : TheoremCBlock.ComparisonData a m₀ blk (tailModuli T) pr h E)
    {ℓ L : ℕ} (hT : T ℓ ⊆ T L) (hprime : ∀ q ∈ T L, q.Prime)
    (hlarge : ∀ q ∈ T L, q ∉ T ℓ → paperCutoff (blockScale * ℓ) < q)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (hpairℓ : Pairwise fun i j => (joinModuli m₀ (tailModuli T ℓ) i).Coprime
      (joinModuli m₀ (tailModuli T ℓ) j))
    (Es : Finset (BlockAtom Bk (fun L => ↥(T L)) L)) (B : Finset ℤ) :
    referenceEnergy (FiniteLaw.tensor (crtRef blk (tailModuli T) h0 D.R.μ₀ D.R.μp L))
        (child (crtModuli m₀ blk (tailModuli T) L) Es (paperCutoff (blockScale * ℓ)) B
          (blockScale * ℓ)) ≤
      D.Y ℓ B := by
  rw [crtRef_eq_atomLaws]
  have h1 := restoration_atomLaws (blockModulus m₀ blk) T hT hprime hlarge
    (crtPrefixLaw blk h0 D.R.μ₀) D.R.μp
    (crtPrefixLaw_slotReflectionPositive h0 D.R.μ₀ (fun β => (D.R.rp₀ β).slot))
    (fun q _ hq => (D.R.rpp q hq).slot) (crtPrefixLaw_translate h0 D.R.μ₀ D.R.inv₀)
    (tail_translate D.R.μp D.R.invp) Es B
  refine h1.trans (le_of_eq ?_)
  rw [dataY_eq_referenceEnergy D ℓ hpairℓ B, crtRef_eq_atomLaws]
  unfold referenceEnergy
  simp only [unchangedInput_eq_wholeLift]
  exact (tensor_atomLaws_expect (blockModulus m₀ blk) T (crtPrefixLaw blk h0 D.R.μ₀) D.R.μp ℓ
    (fun z => ∏ v, (wholeLift (joinModuli (blockModulus m₀ blk) (tailModuli T ℓ))
      (paperCutoff (blockScale * ℓ)) (blockScale * ℓ) B (z v)).re)).symm


/-- The child scale of an interval of length `M ≤ KL` is at most `L` (for every `D₀`, `E`). -/
theorem stepEll_le {Jc : Type} [Fintype Jc] (m : Jc → ℕ) (Es : Finset Jc) (D0 M : ℕ) {L : ℕ}
    (hM : M ≤ blockScale * L) : stepEll m Es D0 M ≤ L := by
  unfold stepEll
  by_cases hR : stepR m Es D0 = 0
  · rw [hR]
    unfold stepScale
    simp
  · exact stepScale_le_scale (Nat.one_le_iff_ne_zero.mpr hR) hM

omit [DecidableEq P] in
/-- **Restoration at every child scale** (`lem:record:fibre-scale`(c), the hypothesis `hrest` of
the density chain, on the block atoms): for a tail family of primes, monotone up to `L`, whose
primes added between `ℓ ≤ L` and `L` exceed `(Kℓ)^β`, every child of an interval of length
`M ≤ KL` satisfies `Z_{μ_N}(h) ≤ Y(ℓ, B)` at its scale `ℓ = stepEll E D₀ M`. -/
theorem hrest_block (D : TheoremCBlock.ComparisonData a m₀ blk (tailModuli T) pr h E) {L : ℕ}
    (hmono : ∀ ℓ, ℓ ≤ L → T ℓ ⊆ T L) (hprime : ∀ q ∈ T L, q.Prime)
    (hlarge : ∀ ℓ, ℓ ≤ L → ∀ q ∈ T L, q ∉ T ℓ → paperCutoff (blockScale * ℓ) < q)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (hpair : ∀ ℓ, Pairwise fun i j => (joinModuli m₀ (tailModuli T ℓ) i).Coprime
      (joinModuli m₀ (tailModuli T ℓ) j))
    (Es : Finset (BlockAtom Bk (fun L => ↥(T L)) L)) (D0 M : ℕ) (hM : M ≤ blockScale * L)
    (B : Finset ℤ) :
    referenceEnergy (FiniteLaw.tensor (crtRef blk (tailModuli T) h0 D.R.μ₀ D.R.μp L))
        (child (crtModuli m₀ blk (tailModuli T) L) Es
          (paperCutoff (blockScale * stepEll (crtModuli m₀ blk (tailModuli T) L) Es D0 M)) B
          (blockScale * stepEll (crtModuli m₀ blk (tailModuli T) L) Es D0 M)) ≤
      D.Y (stepEll (crtModuli m₀ blk (tailModuli T) L) Es D0 M) B := by
  have hℓ := stepEll_le (crtModuli m₀ blk (tailModuli T) L) Es D0 M hM
  exact restoration_block D (hmono _ hℓ) hprime (hlarge _ hℓ) h0 (hpair _) Es B

section Slots

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

omit [DecidableEq P] in
/-- **The restoration conjunct of DC1's `_hterms` for `envC`**
(`DensityChain.envMeanBound_of_restoration`, `envMeanBoundL/R_paper_restoration`): at every scale
`L`, depth vector, term `(f, g)`, residue index `ω` and slot `v`. -/
theorem envHrest_block (D : TheoremCBlock.ComparisonData a m₀ blk (tailModuli T) pr h E)
    (hmono : ∀ ℓ L, ℓ ≤ L → T ℓ ⊆ T L) (hprime : ∀ L, ∀ q ∈ T L, q.Prime)
    (hlarge : ∀ ℓ L, ℓ ≤ L → ∀ q ∈ T L, q ∉ T ℓ → paperCutoff (blockScale * ℓ) < q)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (tailModuli T L) i).Coprime
      (joinModuli m₀ (tailModuli T L) j))
    (u : E → reservedCut.Half) (L : ℕ)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (f g : BlockAtom Bk (fun L => ↥(T L)) L → Bool) :
    ∀ ω v, ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk (tailModuli T) L) (termSet f g)
        (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk (tailModuli T)
          (prefix_pairwise (J := fun L => ↥(T L)) (p := tailModuli T) (hpair L))
          D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk (tailModuli T) L) (termSet f g)
            (paperCutoff (blockScale * stepEll (crtModuli m₀ blk (tailModuli T) L) (termSet f g)
              (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1)) B
            (blockScale * stepEll (crtModuli m₀ blk (tailModuli T) L)
            (termSet f g) (envSlots hcop u L Jq ω v).1
            (envSlots hcop u L Jq ω v).2.2.1)) ≤
        D.Y (stepEll (crtModuli m₀ blk (tailModuli T) L) (termSet f g) (envSlots hcop u L Jq ω v).1
          (envSlots hcop u L Jq ω v).2.2.1) B := by
  intro ω v B _
  have hM : (envSlots hcop u L Jq ω v).2.2.1 ≤ blockScale * L := by
    rw [envSlots_len hcop u L Jq ω v]
    unfold envM
    rcases slotQuery u v with _ | e
    · exact le_rfl
    · exact Nat.le_mul_of_pos_left L (by norm_num [blockScale])
  exact hrest_block D (hmono · L) (hprime L) (hlarge · L) _ hpair _ _ _ hM B

omit [DecidableEq P] in
/-- **The restoration conjunct of DC1's `_hterms` for `fixC`**
(`DensityChain.fixMeanBound_of_restoration`). -/
theorem fixHrest_block (D : TheoremCBlock.ComparisonData a m₀ blk (tailModuli T) pr h E)
    (hmono : ∀ ℓ L, ℓ ≤ L → T ℓ ⊆ T L) (hprime : ∀ L, ∀ q ∈ T L, q.Prime)
    (hlarge : ∀ ℓ L, ℓ ≤ L → ∀ q ∈ T L, q ∉ T ℓ → paperCutoff (blockScale * ℓ) < q)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (tailModuli T L) i).Coprime
      (joinModuli m₀ (tailModuli T L) j))
    (u : E → reservedCut.Half) (L : ℕ) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (f g : BlockAtom Bk (fun L => ↥(T L)) L → Bool) :
    ∀ ω v, ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk (tailModuli T) L) (termSet f g)
        (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk (tailModuli T)
          (prefix_pairwise (J := fun L => ↥(T L)) (p := tailModuli T) (hpair L))
          D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk (tailModuli T) L) (termSet f g)
            (paperCutoff (blockScale * stepEll (crtModuli m₀ blk (tailModuli T) L) (termSet f g)
              (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1)) B
            (blockScale * stepEll (crtModuli m₀ blk (tailModuli T) L)
            (termSet f g) (fixSlots hcop u L S t Jq ω v).1
            (fixSlots hcop u L S t Jq ω v).2.2.1)) ≤
        D.Y (stepEll (crtModuli m₀ blk (tailModuli T) L) (termSet f g)
          (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1) B := by
  intro ω v B _
  have hM : (fixSlots hcop u L S t Jq ω v).2.2.1 ≤ blockScale * L := by
    rw [fixSlots_len hcop u L S t Jq ω v]
    unfold fixM
    have hL : L ≤ blockScale * L := Nat.le_mul_of_pos_left L (by norm_num [blockScale])
    split
    · split_ifs
      · exact hL
      · exact le_rfl
    · exact le_rfl
  exact hrest_block D (hmono · L) (hprime L) (hlarge · L) _ hpair _ _ _ hM B

end Slots

end Sarkozy.DensityChain2
