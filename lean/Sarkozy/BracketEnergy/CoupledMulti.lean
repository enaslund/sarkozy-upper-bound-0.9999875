module

public import Sarkozy.EnvelopeInputs.CoupledTerm
public import Sarkozy.BracketEnergy.RevealedChain

@[expose] public section

/-!
# `lem:density:coupled` for one term with slot-dependent inputs

I1's `abs_diagonalIntegral_coupled_le` (`EnvelopeInputs/CoupledTerm.lean`) is stated for a single
input `F` at every slot, but M1's estimate behind it (`coupled_spectator_estimate_sharpDecomp`)
takes a slot-dependent fibre function. This file states the coupled lemma for a multilinear energy
`∫ ∏_v G_v d(⊗_b ν_b)` with arbitrary slot inputs `G_v`, so that it applies to the revealed inputs
of the envelope energies (the per-choice terms of `diff_bound_of_coupled`). The proofs are I1's,
with the multilinear bridge `multilinearIntegral_tensorLaw_eq_structuredEnergy` in place of WP-R's
diagonal one.

* `multilinearIntegral_tensorLaw_eq_coupled`: the coupled form;
* **`abs_multilinearIntegral_coupled_le`**, **`abs_multilinearIntegral_coupled_le_laws`**
  (`lem:density:coupled`, one term): the sharp atoms are folded, the spectators integrated last
  with their own moment, and the fibre bound is `Z_{μ_𝒮}(G_v(x ⊔ z ⊔ ·))^{1/72} ≤ b_v a_v^{θ/72}`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.BracketEnergy

open Sarkozy.EnvelopeInputs Sarkozy.Structured Sarkozy.DensityMoments Sarkozy.DensityUpgrade
  Sarkozy.TheoremC Sarkozy.Comparison

variable {J : Type} [Fintype J] [DecidableEq J] {Xa : J → Type} [∀ b, Fintype (Xa b)]
  [∀ b, DecidableEq (Xa b)]

/-- **A tensor-law energy in the coupled form**: with `E` selected, `μ_𝒮` the outside law and
`S' ⊆ E` the sharp atoms,
`∫ ∏_v G_v d(⊗_b ν_b) = ∑_x ∑_z ζ(x) κ_T(z) Λ_{μ_𝒮}((F(x_v ⊔ z_v ⊔ ·))_v)`,
`ζ = ⊗_{S'} ν_b`, `κ_T(z) = ∏_{E \ S'} ν_b(z_b)`. -/
theorem multilinearIntegral_tensorLaw_eq_coupled (E : Finset J) (S' : Finset {b // b ∈ E})
    (ν : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    (μS : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b))
    (hμS : ∀ w, μS.weight w = ∏ b : {b // b ∉ E}, lawDensity (ν b) (fun v => w v b))
    (G : Slot → (∀ b, Xa b) → ℝ) :
    multilinearIntegral (tensorLaw ν) G =
      ∑ x : Slot → ∀ b : {b' // b' ∈ S'}, Xa b.1.1,
        ∑ z : Slot → ∀ b : {b' // b' ∉ S'}, Xa b.1.1,
          lawDensity (tensorLaw fun b : {b' // b' ∈ S'} => ν b.1.1) x *
            (∏ b : {b' // b' ∉ S'}, lawDensity (ν b.1.1) (fun v => z v b)) *
            multilinearIntegral (signedIntegral μS.weight)
              (fun v w => G v (joinLabels E (joinLabels S' (x v) (z v)) w)) := by
  rw [multilinearIntegral_tensorLaw_eq_structuredEnergy E ν μS hμS (FiniteLaw.uniform Unit) G]
  simp only [structuredEnergy, FiniteLaw.expect_const]
  rw [sum_splitSlots S']
  refine sum_congr rfl fun x _ => sum_congr rfl fun z _ => ?_
  rw [DensityDC.lawDensity_tensorLaw]
  congr 1
  unfold selectedWeight
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun b' : {b // b ∈ E} => b' ∈ S')]
  congr 1
  · refine prod_congr (by congr 1; exact Subsingleton.elim _ _) fun b _ => ?_
    congr 1
    funext v
    exact joinLabels_mem (Xa := fun b' : {b // b ∈ E} => Xa b'.1) S' (x v) (z v) b
  · refine prod_congr rfl fun b _ => ?_
    congr 1
    funext v
    exact joinLabels_not_mem (Xa := fun b' : {b // b ∈ E} => Xa b'.1) S' (x v) (z v) b

/-- **`lem:density:coupled` for one tensor-law term.** Let `S' ⊆ E` be the sharp atoms, with a
sharp decomposition `ζ = ⊗_{S'} ν_b = w ∑_s π_s K_s` (each `K_s` sharp at `c` relative to the half
marginals of the probability `κ_s`), and let the spectator weight `κ_T = ∏_{E \ S'} ν_b` be
nonnegative with mass normalizer `m_T > 0`. Suppose:
* `μ_𝒮` is positive at `c` and has the outside signed Hölder inequality;
* the normalized folded laws `λ̂_±` and `κ_T/m_T` have unit mixed `L^{72/θ}`;
* `Z_{μ_𝒮}(G_v(x ⊔ z ⊔ ·))^{1/72} ≤ b_v a_v(x,z)^{θ/72}` for every slot.

Then `|∫ ∏_v G_v d(⊗_b ν_b)| ≤ m_T · w d ∏_v b_v ∏_v (E_{x,z} a_v(x,z))^{θ/72}`. No moment of a
folded spectator is used. -/
theorem abs_multilinearIntegral_coupled_le (E : Finset J) (S' : Finset {b // b ∈ E})
    (ν : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    (μS : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b))
    (hμS : ∀ w, μS.weight w = ∏ b : {b // b ∉ E}, lawDensity (ν b) (fun v => w v b))
    (G : Slot → (∀ b, Xa b) → ℝ) (c : ReflectionCut Slot)
    {κ : SlotMeasure (∀ b : {b' // b' ∈ S'}, Xa b.1.1)} {d θ mT : ℝ} {Sd : Type} [Fintype Sd]
    (π : FiniteLaw Sd) (κs Ks : Sd → SlotMeasure (∀ b : {b' // b' ∈ S'}, Xa b.1.1))
    (hprob : ∀ s, IsProbability (κs s))
    (hζ : tensorLaw (fun b : {b' // b' ∈ S'} => ν b.1.1) = mass κ • ∑ s, π.weight s • Ks s)
    (hsharp : ∀ s, Sharp c (Ks s) (halfMarginalPlus c (κs s)) (halfMarginalMinus c (κs s)) d)
    (hmass : 0 ≤ mass κ) (hd : 0 ≤ d) (hθ : θ ≠ 0)
    (hO : c.Positive (signedIntegral μS.weight))
    (hhol : coupledOutsideHolderV (multilinearIntegral (signedIntegral μS.weight)))
    (hmT : 0 < mT)
    (hκT : ∀ z : Slot → ∀ b : {b' // b' ∉ S'}, Xa b.1.1,
      0 ≤ ∏ b : {b' // b' ∉ S'}, lawDensity (ν b.1.1) (fun v => z v b))
    (hmp : coupledUnitMixedV (72 / θ) (foldedLawPlus c π κs))
    (hmm : coupledUnitMixedV (72 / θ) (foldedLawMinus c π κs))
    (hmκ : coupledUnitMixedV (72 / θ) (fun z : Slot → ∀ b : {b' // b' ∉ S'}, Xa b.1.1 =>
      mT⁻¹ * ∏ b : {b' // b' ∉ S'}, lawDensity (ν b.1.1) (fun v => z v b)))
    {a : Slot → (∀ b : {b' // b' ∈ S'}, Xa b.1.1) → (∀ b : {b' // b' ∉ S'}, Xa b.1.1) → ℝ}
    {bv : Slot → ℝ} (ha : ∀ v x y, 0 ≤ a v x y) (hb : ∀ v, 0 ≤ bv v)
    (hZ : ∀ v x y, coupledEnergyV (multilinearIntegral (signedIntegral μS.weight))
        (fun w => G v (joinLabels E (joinLabels S' x y) w)) ^ (1 / (72 : ℝ)) ≤
      bv v * a v x y ^ (θ / 72)) :
    |multilinearIntegral (tensorLaw ν) G| ≤
      mT * (mass κ * d * (∏ v, bv v) *
        ∏ v, coupledMean (fun q : (∀ b : {b' // b' ∈ S'}, Xa b.1.1) ×
          (∀ b : {b' // b' ∉ S'}, Xa b.1.1) => a v q.1 q.2) ^ (θ / 72)) := by
  rw [multilinearIntegral_tensorLaw_eq_coupled E S' ν μS hμS G]
  have h := coupled_spectator_estimate_sharpDecomp (Y := ∀ b : {b' // b' ∉ S'}, Xa b.1.1) c
    (signedIntegral μS.weight) π κs Ks hprob hζ hsharp hmass hd hθ hO hhol
    (κ' := fun z => mT⁻¹ * ∏ b : {b' // b' ∉ S'}, lawDensity (ν b.1.1) (fun v => z v b))
    (fun z => mul_nonneg (inv_nonneg.mpr hmT.le) (hκT z)) hmp hmm hmκ
    (h := fun v x y w => G v (joinLabels E (joinLabels S' x y) w)) ha hb hZ
  have hm0 : mT ≠ 0 := hmT.ne'
  have key : ∀ A B C : ℝ, A * B * C = mT * (A * (mT⁻¹ * B) * C) := fun A B C => by
    field_simp
  have hrw : (∑ x : Slot → ∀ b : {b' // b' ∈ S'}, Xa b.1.1,
      ∑ z : Slot → ∀ b : {b' // b' ∉ S'}, Xa b.1.1,
        lawDensity (tensorLaw fun b : {b' // b' ∈ S'} => ν b.1.1) x *
          (∏ b : {b' // b' ∉ S'}, lawDensity (ν b.1.1) (fun v => z v b)) *
          multilinearIntegral (signedIntegral μS.weight)
            (fun v w => G v (joinLabels E (joinLabels S' (x v) (z v)) w))) =
      mT * ∑ x : Slot → ∀ b : {b' // b' ∈ S'}, Xa b.1.1,
        ∑ z : Slot → ∀ b : {b' // b' ∉ S'}, Xa b.1.1,
          lawDensity (tensorLaw fun b : {b' // b' ∈ S'} => ν b.1.1) x *
            (mT⁻¹ * ∏ b : {b' // b' ∉ S'}, lawDensity (ν b.1.1) (fun v => z v b)) *
            multilinearIntegral (signedIntegral μS.weight)
              (fun v w => G v (joinLabels E (joinLabels S' (x v) (z v)) w)) := by
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun z _ => key _ _ _
  rw [hrw, abs_mul, abs_of_pos hmT]
  exact mul_le_mul_of_nonneg_left h hmT.le

/-- **`lem:density:coupled` for one term, with the moments as unit mixed bounds of finite laws**
(the form of M1's moment theorems, `CoupledMoments`):
* the normalized folded laws `λ̂_±` are the weights of finite laws `λ_+`, `λ_-` with unit mixed
  `L^{72/θ}`;
* every spectator atom `b` has a normalized finite law `κ̂_b` with weight `ν_b(·)/m_b`,
  `m_b > 0`, with unit mixed `L^{72/θ}`.

The spectator moment tensors over the spectator atoms (`MixedLpBound.tensor`), and the bound is
`abs_multilinearIntegral_coupled_le` with `m_T = ∏_b m_b`. -/
theorem abs_multilinearIntegral_coupled_le_laws [∀ b, Nonempty (Xa b)] (E : Finset J)
    (S' : Finset {b // b ∈ E}) (ν : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    (μS : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b))
    (hμS : ∀ w, μS.weight w = ∏ b : {b // b ∉ E}, lawDensity (ν b) (fun v => w v b))
    (G : Slot → (∀ b, Xa b) → ℝ) (c : ReflectionCut Slot)
    {κ : SlotMeasure (∀ b : {b' // b' ∈ S'}, Xa b.1.1)} {d θ : ℝ} {Sd : Type} [Fintype Sd]
    (π : FiniteLaw Sd) (κs Ks : Sd → SlotMeasure (∀ b : {b' // b' ∈ S'}, Xa b.1.1))
    (hprob : ∀ s, IsProbability (κs s))
    (hζ : tensorLaw (fun b : {b' // b' ∈ S'} => ν b.1.1) = mass κ • ∑ s, π.weight s • Ks s)
    (hsharp : ∀ s, Sharp c (Ks s) (halfMarginalPlus c (κs s)) (halfMarginalMinus c (κs s)) d)
    (hmass : 0 ≤ mass κ) (hd : 0 ≤ d) (hθ : 0 < θ)
    (hO : c.Positive (signedIntegral μS.weight))
    (hhol : coupledOutsideHolderV (multilinearIntegral (signedIntegral μS.weight)))
    (lp lm : FiniteLaw (Slot → ∀ b : {b' // b' ∈ S'}, Xa b.1.1))
    (hlp : ∀ x, foldedLawPlus c π κs x = lp.weight x)
    (hlm : ∀ x, foldedLawMinus c π κs x = lm.weight x)
    (hmp : MixedLpBound lp (72 / θ) 1) (hmm : MixedLpBound lm (72 / θ) 1)
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
      (∏ b, m b) * (mass κ * d * (∏ v, bv v) *
        ∏ v, coupledMean (fun q : (∀ b : {b' // b' ∈ S'}, Xa b.1.1) ×
          (∀ b : {b' // b' ∉ S'}, Xa b.1.1) => a v q.1 q.2) ^ (θ / 72)) := by
  have hmT : 0 < ∏ b, m b := Finset.prod_pos fun b _ => hm b
  have hld : ∀ b y, lawDensity (ν b.1.1) y = m b * (κhat b).weight y := fun b y => by
    rw [hκhat, mul_div_cancel₀ _ (hm b).ne']
  have hκT : ∀ z : Slot → ∀ b : {b' // b' ∉ S'}, Xa b.1.1,
      ∏ b : {b' // b' ∉ S'}, lawDensity (ν b.1.1) (fun v => z v b) =
        (∏ b, m b) * (FiniteLaw.tensor κhat).weight z := fun z => by
    rw [tensor_weight, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ => hld b _
  have hw : ∀ z : Slot → ∀ b : {b' // b' ∉ S'}, Xa b.1.1,
      (∏ b, m b)⁻¹ * ∏ b : {b' // b' ∉ S'}, lawDensity (ν b.1.1) (fun v => z v b) =
        (FiniteLaw.tensor κhat).weight z := fun z => by
    rw [hκT, ← mul_assoc, inv_mul_cancel₀ hmT.ne', one_mul]
  have htens : MixedLpBound (FiniteLaw.tensor κhat) (72 / θ) 1 := by
    have h := MixedLpBound.tensor κhat (by positivity) (fun _ => 1) (fun _ => zero_le_one) hmκ
    rwa [Finset.prod_const_one] at h
  exact abs_multilinearIntegral_coupled_le E S' ν μS hμS G c π κs Ks hprob hζ hsharp hmass hd
    hθ.ne' hO hhol hmT
    (fun z => by rw [hκT]; exact mul_nonneg hmT.le ((FiniteLaw.tensor κhat).nonneg z))
    (coupledUnitMixedV_of_mixedLpBound lp hlp hmp) (coupledUnitMixedV_of_mixedLpBound lm hlm hmm)
    (coupledUnitMixedV_of_mixedLpBound (FiniteLaw.tensor κhat) hw htens) ha hb hZ

end Sarkozy.BracketEnergy
