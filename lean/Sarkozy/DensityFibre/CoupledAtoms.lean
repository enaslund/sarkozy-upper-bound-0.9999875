module

public import Sarkozy.BracketEnergy.CoupledMulti
public import Sarkozy.EnvelopeInputs.CoupledProduct

@[expose] public section

/-!
# `lem:density:coupled` for one term with several sharp atoms and slot-dependent inputs

B9's `abs_multilinearIntegral_coupled_le_laws` (`BracketEnergy/CoupledMulti.lean`) takes one
sharp decomposition on the product alphabet of the sharp atoms. I1's
`abs_diagonalIntegral_coupled_le_atoms` builds such a decomposition from per-atom data, but only
for one input `F` at every slot.

This file combines the two: **`abs_multilinearIntegral_coupled_le_atoms`** has per-atom sharp
decompositions, per-atom folded and spectator moments, and slot-dependent inputs `G_v`, such as
the revealed inputs of `envC` and `fixC`. The proof is I1's, with B9's multilinear lemma in place
of the diagonal one.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.DensityFibre

open Sarkozy.EnvelopeInputs Sarkozy.BracketEnergy Sarkozy.Structured Sarkozy.DensityMoments
  Sarkozy.DensityUpgrade Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.RecordExpansion

variable {J : Type} [Fintype J] [DecidableEq J] {Xa : J → Type} [∀ b, Fintype (Xa b)]
  [∀ b, DecidableEq (Xa b)]

/-- **`lem:density:coupled` for one term, per-atom sharp data, slot-dependent inputs.** As I1's
`abs_diagonalIntegral_coupled_le_atoms`, with inputs `G_v` in place of one `F`: the fibre bound is
`Z_{μ_𝒮}(G_v(x ⊔ z ⊔ ·))^{1/72} ≤ b_v a_v(x, z)^{θ/72}` at every slot `v`, and
`|∫ ∏_v G_v d(⊗_b ν_b)| ≤ (∏_T m_b)(∏_{S'} κ_b(1))(∏_{S'} d_b) ∏_v b_v ∏_v (E a_v)^{θ/72}`. -/
theorem abs_multilinearIntegral_coupled_le_atoms [∀ b, Nonempty (Xa b)] (E : Finset J)
    (S' : Finset {b // b ∈ E}) (ν : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    (μS : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b))
    (hμS : ∀ w, μS.weight w = ∏ b : {b // b ∉ E}, lawDensity (ν b) (fun v => w v b))
    (G : Slot → (∀ b, Xa b) → ℝ) (c : ReflectionCut Slot)
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
        (fun w => G v (joinLabels E (joinLabels S' x y) w)) ^ (1 / (72 : ℝ)) ≤
      bv v * a v x y ^ (θ / 72)) :
    |multilinearIntegral (tensorLaw ν) G| ≤
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
  have h := abs_multilinearIntegral_coupled_le_laws E S' ν μS hμS G c
    (κ := (tensorLaw κ : SlotMeasure (∀ b : {b' // b' ∈ S'}, Xa b.1.1))) (d := ∏ b, d b)
    (FiniteLaw.pi π) (fun s => tensorLaw fun b => κs b (s b))
    (fun s => tensorLaw fun b => Ks b (s b))
    (fun s => isProbability_tensorLaw _ (fun b => hprob b (s b))) hζT hsharpT
    (by rw [hmassT]; exact Finset.prod_nonneg fun b _ => hmass b)
    (Finset.prod_nonneg fun b _ => hd b) hθ hO hhol (FiniteLaw.tensor lp) (FiniteLaw.tensor lm)
    hlpT hlmT hmpT hmmT m hm κhat hκhat hmκ ha hb hZ
  rw [hmassT] at h
  exact h

end Sarkozy.DensityFibre
