module

public import Sarkozy.EnvelopeInputs.CoupledMoments
public import Sarkozy.Structured.Representation
public import Sarkozy.DensityDC.AtomTransport

/-!
# `lem:density:coupled` for one term: a tensor-law energy with sharp atoms and spectators

`paper/sections/31_density_induction_upgrade.tex`, `lem:density:coupled`, for the energy
`Y_{⊗_b ν_b}(F)` of a tensor law over the coordinates, at a selected set `E`:

* the atoms outside `E` carry the outside reference `μ_𝒮` (a finite law, the product of the
  `ν_b` there);
* inside `E`, the atoms of `S' ⊆ E` are the **sharp atoms**, whose product `ζ = ⊗_{S'} ν_b` is a
  sharp law (with a sharp decomposition on the product alphabet, taken as data), and the others
  are the **spectators**, with product weight `κ_T = ∏_{E \ S'} ν_b(·)`.

Nothing is folded except the sharp product: the spectators are integrated last with their own
moment, as in the paper ("No moment hypothesis is required for a fold of `κ`").

* `diagonalIntegral_tensorLaw_eq_coupled`: the energy in M1's form
  `∑_x ∑_z ζ(x) κ_T(z) Λ_{μ_𝒮}((F(x_v ⊔ z_v ⊔ ·))_v)` (two applications of the label splitting of
  `Structured.Bridge`);
* `abs_diagonalIntegral_coupled_le`: M1's `coupled_spectator_estimate_sharpDecomp` for that form:
  `|Y_{⊗_b ν_b}(F)| ≤ m_T · w d ∏_v b_v ∏_v (E_{x,z} a_v(x,z))^{θ/72}`;
* `abs_diagonalIntegral_coupled_le_laws`: the same with the moments stated as `MixedLpBound`s of
  finite laws, the spectator moment **per spectator atom** (it tensors, `MixedLpBound.tensor`),
  so that M1's moment theorems (`CoupledMoments`) apply directly.

Its moment hypotheses are exactly the paper's: unit mixed `L^{72/θ}` of the normalized folded
laws `λ̂_±` of the sharp decomposition and of the normalized spectator weight `κ_T/m_T`. The
other hypotheses are M1's: `μ_𝒮` positive at the cut with the outside signed Hölder inequality,
and the fibre bound `Z_{μ_𝒮}(F(x ⊔ z ⊔ ·))^{1/72} ≤ b_v a_v(x,z)^{θ/72}`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.Structured Sarkozy.DensityMoments Sarkozy.DensityUpgrade Sarkozy.TheoremC
  Sarkozy.Comparison

variable {J : Type} [Fintype J] [DecidableEq J] {Xa : J → Type} [∀ b, Fintype (Xa b)]
  [∀ b, DecidableEq (Xa b)]

/-- **A tensor-law energy in the coupled form**: with `E` selected, `μ_𝒮` the outside law and
`S' ⊆ E` the sharp atoms,
`Y_{⊗_b ν_b}(F) = ∑_x ∑_z ζ(x) κ_T(z) Λ_{μ_𝒮}((F(x_v ⊔ z_v ⊔ ·))_v)`,
`ζ = ⊗_{S'} ν_b`, `κ_T(z) = ∏_{E \ S'} ν_b(z_b)`. -/
theorem diagonalIntegral_tensorLaw_eq_coupled (E : Finset J) (S' : Finset {b // b ∈ E})
    (ν : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    (μS : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b))
    (hμS : ∀ w, μS.weight w = ∏ b : {b // b ∉ E}, lawDensity (ν b) (fun v => w v b))
    (F : (∀ b, Xa b) → ℝ) :
    diagonalIntegral (tensorLaw ν) F =
      ∑ x : Slot → ∀ b : {b' // b' ∈ S'}, Xa b.1.1,
        ∑ z : Slot → ∀ b : {b' // b' ∉ S'}, Xa b.1.1,
          lawDensity (tensorLaw fun b : {b' // b' ∈ S'} => ν b.1.1) x *
            (∏ b : {b' // b' ∉ S'}, lawDensity (ν b.1.1) (fun v => z v b)) *
            multilinearIntegral (signedIntegral μS.weight)
              (fun v w => F (joinLabels E (joinLabels S' (x v) (z v)) w)) := by
  rw [diagonalIntegral_tensorLaw_eq_structuredEnergy E ν μS hμS (FiniteLaw.uniform Unit) F]
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
* `Z_{μ_𝒮}(F(x ⊔ z ⊔ ·))^{1/72} ≤ b_v a_v(x,z)^{θ/72}` for every slot.

Then `|Y_{⊗_b ν_b}(F)| ≤ m_T · w d ∏_v b_v ∏_v (E_{x,z} a_v(x,z))^{θ/72}`. No moment of a folded
spectator is used. -/
theorem abs_diagonalIntegral_coupled_le (E : Finset J) (S' : Finset {b // b ∈ E})
    (ν : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    (μS : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b))
    (hμS : ∀ w, μS.weight w = ∏ b : {b // b ∉ E}, lawDensity (ν b) (fun v => w v b))
    (F : (∀ b, Xa b) → ℝ) (c : ReflectionCut Slot)
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
        (fun w => F (joinLabels E (joinLabels S' x y) w)) ^ (1 / (72 : ℝ)) ≤
      bv v * a v x y ^ (θ / 72)) :
    |diagonalIntegral (tensorLaw ν) F| ≤
      mT * (mass κ * d * (∏ v, bv v) *
        ∏ v, coupledMean (fun q : (∀ b : {b' // b' ∈ S'}, Xa b.1.1) ×
          (∀ b : {b' // b' ∉ S'}, Xa b.1.1) => a v q.1 q.2) ^ (θ / 72)) := by
  rw [diagonalIntegral_tensorLaw_eq_coupled E S' ν μS hμS F]
  have h := coupled_spectator_estimate_sharpDecomp (Y := ∀ b : {b' // b' ∉ S'}, Xa b.1.1) c
    (signedIntegral μS.weight) π κs Ks hprob hζ hsharp hmass hd hθ hO hhol
    (κ' := fun z => mT⁻¹ * ∏ b : {b' // b' ∉ S'}, lawDensity (ν b.1.1) (fun v => z v b))
    (fun z => mul_nonneg (inv_nonneg.mpr hmT.le) (hκT z)) hmp hmm hmκ
    (h := fun _ x y w => F (joinLabels E (joinLabels S' x y) w)) ha hb hZ
  have hm0 : mT ≠ 0 := hmT.ne'
  have key : ∀ A B C : ℝ, A * B * C = mT * (A * (mT⁻¹ * B) * C) := fun A B C => by
    field_simp
  have hrw : (∑ x : Slot → ∀ b : {b' // b' ∈ S'}, Xa b.1.1,
      ∑ z : Slot → ∀ b : {b' // b' ∉ S'}, Xa b.1.1,
        lawDensity (tensorLaw fun b : {b' // b' ∈ S'} => ν b.1.1) x *
          (∏ b : {b' // b' ∉ S'}, lawDensity (ν b.1.1) (fun v => z v b)) *
          multilinearIntegral (signedIntegral μS.weight)
            (fun v w => F (joinLabels E (joinLabels S' (x v) (z v)) w))) =
      mT * ∑ x : Slot → ∀ b : {b' // b' ∈ S'}, Xa b.1.1,
        ∑ z : Slot → ∀ b : {b' // b' ∉ S'}, Xa b.1.1,
          lawDensity (tensorLaw fun b : {b' // b' ∈ S'} => ν b.1.1) x *
            (mT⁻¹ * ∏ b : {b' // b' ∉ S'}, lawDensity (ν b.1.1) (fun v => z v b)) *
            multilinearIntegral (signedIntegral μS.weight)
              (fun v w => F (joinLabels E (joinLabels S' (x v) (z v)) w)) := by
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
`abs_diagonalIntegral_coupled_le` with `m_T = ∏_b m_b`. -/
theorem abs_diagonalIntegral_coupled_le_laws [∀ b, Nonempty (Xa b)] (E : Finset J)
    (S' : Finset {b // b ∈ E}) (ν : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    (μS : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b))
    (hμS : ∀ w, μS.weight w = ∏ b : {b // b ∉ E}, lawDensity (ν b) (fun v => w v b))
    (F : (∀ b, Xa b) → ℝ) (c : ReflectionCut Slot)
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
        (fun w => F (joinLabels E (joinLabels S' x y) w)) ^ (1 / (72 : ℝ)) ≤
      bv v * a v x y ^ (θ / 72)) :
    |diagonalIntegral (tensorLaw ν) F| ≤
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
  exact abs_diagonalIntegral_coupled_le E S' ν μS hμS F c π κs Ks hprob hζ hsharp hmass hd
    hθ.ne' hO hhol hmT
    (fun z => by rw [hκT]; exact mul_nonneg hmT.le ((FiniteLaw.tensor κhat).nonneg z))
    (coupledUnitMixedV_of_mixedLpBound lp hlp hmp) (coupledUnitMixedV_of_mixedLpBound lm hlm hmm)
    (coupledUnitMixedV_of_mixedLpBound (FiniteLaw.tensor κhat) hw htens) ha hb hZ

end Sarkozy.EnvelopeInputs
