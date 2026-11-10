module

public import Sarkozy.EnvelopeInputs.CoupledTerm
public import Sarkozy.EnvelopeInputs.SharpTensorBound

/-!
# `lem:density:coupled` for one term with several sharp atoms, from per-atom data

`CoupledTerm.abs_diagonalIntegral_coupled_le_laws` takes a sharp decomposition on the product
alphabet of the sharp atoms. Here it is built from the sharp decompositions of the atoms
(`hasSharpBound_tensor`'s construction), so the inputs are per atom, as in the paper ("products of
sharp atoms ... obey the same proof"):

* `foldedLawPlus_tensor`, `foldedLawMinus_tensor`: the normalized full folded laws of the product
  decomposition are the products of the per-atom ones;
* **`abs_diagonalIntegral_coupled_le_atoms`**: the coupled per-term bound with
  - per sharp atom: its sharp decomposition, and unit mixed `L^{72/θ}` of its two normalized
    folded laws `λ̂±_b`;
  - per spectator atom: unit mixed `L^{72/θ}` of its normalized law `κ̂_b`;
  - the outside reference: positive at the cut, with the outside Hölder property;
  - the fibre bound `hZ`.

  The conclusion is
  `|Y| ≤ (∏_T m_b) · (∏_{S'} κ_b(1)) (∏_{S'} d_b) ∏_v b_v ∏_v (E a_v)^{θ/72}`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.Structured Sarkozy.DensityMoments Sarkozy.DensityUpgrade Sarkozy.TheoremC
  Sarkozy.Comparison Sarkozy.RecordExpansion

section Folded

variable {J' : Type} [Fintype J'] [DecidableEq J'] {Y : J' → Type} [∀ j, Fintype (Y j)]
  [∀ j, DecidableEq (Y j)]

/-- The plus normalized full folded law of a product of sharp decompositions is the product of
the per-atom ones. -/
theorem foldedLawPlus_tensor (c : ReflectionCut Slot) {S : J' → Type} [∀ j, Fintype (S j)]
    (π : ∀ j, FiniteLaw (S j)) (κs : ∀ j, S j → SlotMeasure (Y j)) (x : Slot → ∀ j, Y j) :
    foldedLawPlus c (FiniteLaw.pi π)
        (fun s => (tensorLaw fun j => κs j (s j) : SlotMeasure (∀ j, Y j))) x =
      ∏ j, foldedLawPlus c (π j) (κs j) (fun v => x v j) := by
  unfold foldedLawPlus
  have hd : ∀ s : (∀ j, S j), c.diagonalLaw
      (halfMarginalPlus c (tensorLaw fun j => κs j (s j) : SlotMeasure (∀ j, Y j))) =
      tensorLaw (fun j => c.diagonalLaw (halfMarginalPlus c (κs j (s j)))) := by
    intro s
    rw [tensorLaw_diagonalLaw]
    congr 1
    funext y
    exact halfMarginalPlus_tensorLaw c _ y
  simp only [hd, Sarkozy.DensityDC.lawDensity_tensorLaw]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  change (∏ j, (π j).weight (s j)) * _ = _
  rw [← Finset.prod_mul_distrib]

/-- The minus normalized full folded law of a product of sharp decompositions is the product of
the per-atom ones. -/
theorem foldedLawMinus_tensor (c : ReflectionCut Slot) {S : J' → Type} [∀ j, Fintype (S j)]
    (π : ∀ j, FiniteLaw (S j)) (κs : ∀ j, S j → SlotMeasure (Y j)) (x : Slot → ∀ j, Y j) :
    foldedLawMinus c (FiniteLaw.pi π)
        (fun s => (tensorLaw fun j => κs j (s j) : SlotMeasure (∀ j, Y j))) x =
      ∏ j, foldedLawMinus c (π j) (κs j) (fun v => x v j) := by
  unfold foldedLawMinus
  have hd : ∀ s : (∀ j, S j), c.diagonalLaw
      (halfMarginalMinus c (tensorLaw fun j => κs j (s j) : SlotMeasure (∀ j, Y j))) =
      tensorLaw (fun j => c.diagonalLaw (halfMarginalMinus c (κs j (s j)))) := by
    intro s
    rw [tensorLaw_diagonalLaw]
    congr 1
    funext y
    exact halfMarginalMinus_tensorLaw c _ y
  simp only [hd, Sarkozy.DensityDC.lawDensity_tensorLaw]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  change (∏ j, (π j).weight (s j)) * _ = _
  rw [← Finset.prod_mul_distrib]

end Folded

section Term

variable {J : Type} [Fintype J] [DecidableEq J] {Xa : J → Type} [∀ b, Fintype (Xa b)]
  [∀ b, DecidableEq (Xa b)]

/-- **`lem:density:coupled` for one term with several sharp atoms, from per-atom data.** The
sharp atoms `S' ⊆ E` carry sharp decompositions `ν_b = κ_b(1) ∑_s π_b(s) K_{b,s}` (sharp at `c`
with constants `d_b`, relative to the half marginals of the probability measures `κ_{b,s}`). The
spectators `E \ S'` carry positive laws `ν_b = m_b κ̂_b`. The rest carries the outside law `μ_𝒮`.
The moment inputs are per atom:
* unit mixed `L^{72/θ}` of the normalized folded laws `λ̂±_b` of every sharp atom;
* unit mixed `L^{72/θ}` of every spectator `κ̂_b`.

Then `|Y_{⊗_b ν_b}(F)| ≤ (∏_T m_b) (∏_{S'} κ_b(1)) (∏_{S'} d_b) ∏_v b_v ∏_v (E a_v)^{θ/72}`. -/
theorem abs_diagonalIntegral_coupled_le_atoms [∀ b, Nonempty (Xa b)] (E : Finset J)
    (S' : Finset {b // b ∈ E}) (ν : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    (μS : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b))
    (hμS : ∀ w, μS.weight w = ∏ b : {b // b ∉ E}, lawDensity (ν b) (fun v => w v b))
    (F : (∀ b, Xa b) → ℝ) (c : ReflectionCut Slot)
    (κ : ∀ b : {b' // b' ∈ S'}, SlotMeasure (Xa b.1.1)) (d : {b' // b' ∈ S'} → ℝ)
    {Sd : {b' // b' ∈ S'} → Type} [∀ b, Fintype (Sd b)] (π : ∀ b, FiniteLaw (Sd b))
    (κs Ks : ∀ b, Sd b → SlotMeasure (Xa b.1.1)) (hprob : ∀ b s, IsProbability (κs b s))
    (hζ : ∀ b, ν b.1.1 = mass (κ b) • ∑ s, (π b).weight s • Ks b s)
    (hsharp : ∀ b s, Sharp c (Ks b s) (halfMarginalPlus c (κs b s))
      (halfMarginalMinus c (κs b s)) (d b))
    (hmass : ∀ b, 0 ≤ mass (κ b)) (hd : ∀ b, 0 ≤ d b) {θ : ℝ} (hθ : 0 < θ)
    (hO : c.Positive (signedIntegral μS.weight))
    (hhol : coupledOutsideHolderV (multilinearIntegral (signedIntegral μS.weight)))
    (lp lm : ∀ b : {b' // b' ∈ S'}, FiniteLaw (Slot → Xa b.1.1))
    (hlp : ∀ b x, foldedLawPlus c (π b) (κs b) x = (lp b).weight x)
    (hlm : ∀ b x, foldedLawMinus c (π b) (κs b) x = (lm b).weight x)
    (hmp : ∀ b, MixedLpBound (lp b) (72 / θ) 1) (hmm : ∀ b, MixedLpBound (lm b) (72 / θ) 1)
    (m : {b' // b' ∉ S'} → ℝ) (hm : ∀ b, 0 < m b)
    (κhat : ∀ b : {b' // b' ∉ S'}, FiniteLaw (Slot → Xa b.1.1))
    (hκhat : ∀ b z, (κhat b).weight z = lawDensity (ν b.1.1) z / m b)
    (hmκ : ∀ b, MixedLpBound (κhat b) (72 / θ) 1)
    {a : Slot → (∀ b : {b' // b' ∈ S'}, Xa b.1.1) → (∀ b : {b' // b' ∉ S'}, Xa b.1.1) → ℝ}
    {bv : Slot → ℝ} (ha : ∀ v x y, 0 ≤ a v x y) (hb : ∀ v, 0 ≤ bv v)
    (hZ : ∀ v x y, coupledEnergyV (multilinearIntegral (signedIntegral μS.weight))
        (fun w => F (joinLabels E (joinLabels S' x y) w)) ^ (1 / (72 : ℝ)) ≤
      bv v * a v x y ^ (θ / 72)) :
    |diagonalIntegral (tensorLaw ν) F| ≤
      (∏ b, m b) * ((∏ b, mass (κ b)) * (∏ b, d b) * (∏ v, bv v) *
        ∏ v, coupledMean (fun q : (∀ b : {b' // b' ∈ S'}, Xa b.1.1) ×
          (∀ b : {b' // b' ∉ S'}, Xa b.1.1) => a v q.1 q.2) ^ (θ / 72)) := by
  have hmassT : mass (tensorLaw κ : SlotMeasure (∀ b : {b' // b' ∈ S'}, Xa b.1.1)) =
      ∏ b, mass (κ b) := tensorLaw_one κ
  have hζT : (tensorLaw fun b : {b' // b' ∈ S'} => ν b.1.1) =
      mass (tensorLaw κ : SlotMeasure (∀ b : {b' // b' ∈ S'}, Xa b.1.1)) •
        ∑ s, (FiniteLaw.pi π).weight s • (tensorLaw fun b => Ks b (s b)) := by
    have e : (tensorLaw fun b : {b' // b' ∈ S'} => ν b.1.1) =
        tensorLaw (fun b => mass (κ b) • ∑ t, (π b).weight t • Ks b t) := by
      congr 1
      exact funext hζ
    rw [hmassT, e, tensorLaw_smul (fun b => mass (κ b)), tensorLaw_sum
      (fun b t => (π b).weight t • Ks b t)]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [tensorLaw_smul (fun b => (π b).weight (s b)) (fun b => Ks b (s b))]
    rfl
  have hsharpT : ∀ s : (∀ b, Sd b), Sharp c (tensorLaw fun b => Ks b (s b))
      (halfMarginalPlus c (tensorLaw fun b => κs b (s b) :
        SlotMeasure (∀ b : {b' // b' ∈ S'}, Xa b.1.1)))
      (halfMarginalMinus c (tensorLaw fun b => κs b (s b) :
        SlotMeasure (∀ b : {b' // b' ∈ S'}, Xa b.1.1))) (∏ b, d b) := by
    intro s
    have hs := sharp_tensor c (fun b => Ks b (s b)) (fun b => halfMarginalPlus c (κs b (s b)))
      (fun b => halfMarginalMinus c (κs b (s b))) d
      (fun b x => (hprob b (s b)).1 _ (fun _ => by split_ifs <;> norm_num))
      (fun b x => (hprob b (s b)).1 _ (fun _ => by split_ifs <;> norm_num)) hd
      (fun b => hsharp b (s b))
    have hp : halfMarginalPlus c (tensorLaw fun b => κs b (s b) :
        SlotMeasure (∀ b : {b' // b' ∈ S'}, Xa b.1.1)) =
        fun x => ∏ b, halfMarginalPlus c (κs b (s b)) (fun u => x u b) :=
      funext fun x => halfMarginalPlus_tensorLaw c _ x
    have hm' : halfMarginalMinus c (tensorLaw fun b => κs b (s b) :
        SlotMeasure (∀ b : {b' // b' ∈ S'}, Xa b.1.1)) =
        fun x => ∏ b, halfMarginalMinus c (κs b (s b)) (fun u => x u b) :=
      funext fun x => halfMarginalMinus_tensorLaw c _ x
    rw [hp, hm']
    exact hs
  have hlpT : ∀ x, foldedLawPlus c (FiniteLaw.pi π)
      (fun s => (tensorLaw fun b => κs b (s b) :
        SlotMeasure (∀ b : {b' // b' ∈ S'}, Xa b.1.1))) x =
      (FiniteLaw.tensor lp).weight x := by
    intro x
    rw [foldedLawPlus_tensor, tensor_weight]
    exact Finset.prod_congr rfl fun b _ => hlp b _
  have hlmT : ∀ x, foldedLawMinus c (FiniteLaw.pi π)
      (fun s => (tensorLaw fun b => κs b (s b) :
        SlotMeasure (∀ b : {b' // b' ∈ S'}, Xa b.1.1))) x =
      (FiniteLaw.tensor lm).weight x := by
    intro x
    rw [foldedLawMinus_tensor, tensor_weight]
    exact Finset.prod_congr rfl fun b _ => hlm b _
  have hp72 : (0 : ℝ) < 72 / θ := by positivity
  have hmpT : MixedLpBound (FiniteLaw.tensor lp) (72 / θ) 1 := by
    have h := MixedLpBound.tensor lp hp72 (fun _ => 1) (fun _ => zero_le_one) hmp
    rwa [Finset.prod_const_one] at h
  have hmmT : MixedLpBound (FiniteLaw.tensor lm) (72 / θ) 1 := by
    have h := MixedLpBound.tensor lm hp72 (fun _ => 1) (fun _ => zero_le_one) hmm
    rwa [Finset.prod_const_one] at h
  have h := abs_diagonalIntegral_coupled_le_laws E S' ν μS hμS F c
    (κ := (tensorLaw κ : SlotMeasure (∀ b : {b' // b' ∈ S'}, Xa b.1.1))) (d := ∏ b, d b)
    (FiniteLaw.pi π) (fun s => tensorLaw fun b => κs b (s b))
    (fun s => tensorLaw fun b => Ks b (s b))
    (fun s => isProbability_tensorLaw _ (fun b => hprob b (s b))) hζT hsharpT
    (by rw [hmassT]; exact Finset.prod_nonneg fun b _ => hmass b)
    (Finset.prod_nonneg fun b _ => hd b) hθ hO hhol (FiniteLaw.tensor lp) (FiniteLaw.tensor lm)
    hlpT hlmT hmpT hmmT m hm κhat hκhat hmκ ha hb hZ
  rw [hmassT] at h
  exact h

end Term

end Sarkozy.EnvelopeInputs
