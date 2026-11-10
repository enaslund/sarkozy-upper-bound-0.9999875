module

public import Sarkozy.EnvelopeInputs.FoldedEnvelope
public import Sarkozy.DensityDC.AtomTransport
public import Sarkozy.TheoremC.Defs

/-!
# WP-FI's folded energies in coordinates

Input (F) of the reduced hypotheses is stated for WP-FI's atoms `PaperAtom J L = Option (J L)`
(the prefix `none` and the tail primes `some j`) with the input `atomLift m₀ p L A`. The bounds
of `FoldedEnvelope` are stated in the coordinates `J₀ ⊕ J L` of the group with the input
`unchangedInput`. When the prefix factor is a product `⊗_i λ0_i` (the prefix unselected, with a
product prefix law), the two agree:

* `wholeLift_eq_input_one`: `F_A = g^{[N], 1, 0}` (the same statement as
  `CancellationSteps.wholeLift_eq_input`, reproved here to keep this package's imports compiled);
* `diagonalIntegral_atomLift_eq`: an energy `Y_{⊗_b Λ_b}(atomLift)` on the atoms, with a product
  prefix factor, is the coordinate energy with the input `unchangedInput` (the subset terms of
  (S));
* `foldedPlus_atomLift_eq`, `foldedMinus_atomLift_eq`: `𝔈_±(f)` with the input `atomLift` is the
  diagonal integral of `⊗_k joinLaws(R_{·,f})_k` with the input `unchangedInput` at the cutoff
  `Q = paperCutoff N` (`tensorLaw_atoms_transport`).

* `abs_atom_energy_le_unchanged_atoms`: (S) and (F) per term on the atoms, at `θ = ϑ`:
  `abs_tensor_energy_le_unchanged_atoms` for `joinLaws(Λ, λ0)` at the cutoff `paperCutoff N`;
* `sum_abs_lawDensity_eq_mass`: the factors `‖Λ_b‖` of that bound are the masses of the selected
  records.

Not done here: the matching with WP-FI's pieces (which pieces are `μ` off the selected set, the
prefix product), the price inequality against `∏_b pieceG(f_b)`, and the per-term inputs.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.DensityDC

/-- `F_A = g^{[N], 1, 0}`: the whole-interval lift is the input with `D₀ = 1`. -/
theorem wholeLift_eq_input_one {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ)
    [∀ j, NeZero (m j)] (Q : ℝ) (N : ℕ) (A : Finset ℤ) (z : ResidueSpace m) :
    wholeLift m Q N A z = input m Q (Icc 1 (N : ℤ)) 1 0 A z := by
  unfold wholeLift input
  congr 1
  funext n
  unfold indicator inputFun
  have : ((n : ZMod 1) = 0) := Subsingleton.elim _ _
  simp [this]

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- The diagonal integrand of `atomLift` in coordinates. -/
theorem atomLift_symm_eq (L : ℕ) (A : Finset ℤ) (y : ResidueSpace (joinModuli m₀ (p L))) :
    atomLift m₀ p L A ((atomGroupEquiv m₀ p L).symm y) =
      unchangedInput (joinModuli m₀ (p L)) (paperCutoff (blockScale * L)) A L y := by
  unfold atomLift unchangedInput
  rw [Equiv.apply_symm_apply, wholeLift_eq_input_one]

/-- **An energy on WP-FI's atoms in coordinates** (the subset terms of (S) and the folded energies
of (F)): for a product prefix factor `Λ_none = ⊗_i λ0_i`, `Y_{⊗_b Λ_b}(atomLift)` is
`Y_{⊗_k joinLaws(Λ, λ0)_k}(unchangedInput … (paperCutoff N) A L)`. -/
theorem diagonalIntegral_atomLift_eq (L : ℕ) (A : Finset ℤ)
    (Λ : ∀ b : PaperAtom J L, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ)
    (lam0 : ∀ i, ((Slot → ZMod (m₀ i)) → ℝ) →ₗ[ℝ] ℝ) (h0 : Λ none = tensorLaw lam0) :
    diagonalIntegral (tensorLaw Λ) (atomLift m₀ p L A) =
      diagonalIntegral (tensorLaw (joinLaws m₀ p L Λ lam0))
        (unchangedInput (joinModuli m₀ (p L)) (paperCutoff (blockScale * L)) A L) := by
  unfold diagonalIntegral multilinearIntegral
  rw [tensorLaw_atoms_transport m₀ p L Λ lam0 h0]
  congr 1
  funext x
  exact prod_congr rfl fun v _ => atomLift_symm_eq m₀ p L A (x v)

/-- **WP-FI's folded energy `𝔈₊(f)` in coordinates**, for a product prefix factor. -/
theorem foldedPlus_atomLift_eq (L : ℕ) (A : Finset ℤ) (c : ReflectionCut Slot)
    {I : PaperAtom J L → Type*} (Lp : ∀ b, I b → ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ)
    (f : ∀ b, I b) (lam0 : ∀ i, ((Slot → ZMod (m₀ i)) → ℝ) →ₗ[ℝ] ℝ)
    (h0 : Lp none (f none) = tensorLaw lam0) :
    foldedPlus c Lp (fun _ => atomLift m₀ p L A) f =
      diagonalIntegral (tensorLaw (joinLaws m₀ p L (fun b => Lp b (f b)) lam0))
        (unchangedInput (joinModuli m₀ (p L)) (paperCutoff (blockScale * L)) A L) := by
  rw [foldedPlus_const]
  unfold diagonalIntegral multilinearIntegral
  rw [tensorLaw_atoms_transport m₀ p L (fun b => Lp b (f b)) lam0 h0]
  congr 1
  funext x
  exact prod_congr rfl fun v _ => atomLift_symm_eq m₀ p L A (x v)

/-- The same for `𝔈₋(f)`. -/
theorem foldedMinus_atomLift_eq (L : ℕ) (A : Finset ℤ) (c : ReflectionCut Slot)
    {I : PaperAtom J L → Type*} (Lm : ∀ b, I b → ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ)
    (f : ∀ b, I b) (lam0 : ∀ i, ((Slot → ZMod (m₀ i)) → ℝ) →ₗ[ℝ] ℝ)
    (h0 : Lm none (f none) = tensorLaw lam0) :
    foldedMinus c Lm (fun _ => atomLift m₀ p L A) f =
      diagonalIntegral (tensorLaw (joinLaws m₀ p L (fun b => Lm b (f b)) lam0))
        (unchangedInput (joinModuli m₀ (p L)) (paperCutoff (blockScale * L)) A L) := by
  rw [foldedMinus_const]
  unfold diagonalIntegral multilinearIntegral
  rw [tensorLaw_atoms_transport m₀ p L (fun b => Lm b (f b)) lam0 h0]
  congr 1
  funext x
  exact prod_congr rfl fun v _ => atomLift_symm_eq m₀ p L A (x v)

/-- **The total variation of a record is its mass**: for a nonnegative `κ`,
`∑_z |κ({z})| = κ(1)`. So the factors `∏_{b ∈ E} ‖Λ_b‖` of the per-term bounds are the masses of
the selected records. -/
theorem sum_abs_lawDensity_eq_mass {X : Type} [Fintype X] [DecidableEq X]
    (κ : TheoremC.SlotMeasure X) (hκ : TheoremC.IsNonneg κ) :
    ∑ z : Slot → X, |lawDensity κ z| = TheoremC.mass κ := by
  have h0 : ∀ z, 0 ≤ lawDensity κ z := fun z =>
    hκ _ fun y => by split_ifs <;> norm_num
  simp only [abs_of_nonneg (h0 _)]
  unfold lawDensity TheoremC.mass
  rw [← map_sum]
  congr 1
  funext y
  rw [Finset.sum_apply]
  simp

/-- **(S) and (F) per term on WP-FI's atoms, at `θ = ϑ`**: `abs_tensor_energy_le_unchanged_atoms`
for the coordinate law `joinLaws(Λ, λ0)` of an atom law `⊗_b Λ_b` with a product prefix factor
(`diagonalIntegral_atomLift_eq`), at the paper's cutoff `Q = paperCutoff N`. -/
theorem abs_atom_energy_le_unchanged_atoms {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ}
    {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μb : ∀ b, FiniteLaw (Slot → ZMod ((joinModuli m₀ (p L)) b)))
    (hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
    (Λa : ∀ b : PaperAtom J L, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ)
    (lam0 : ∀ i, ((Slot → ZMod (m₀ i)) → ℝ) →ₗ[ℝ] ℝ) (h0 : Λa none = tensorLaw lam0)
    (E : Finset (J₀ ⊕ J L))
    (hE : ∀ b ∉ E, joinLaws m₀ p L Λa lam0 b = signedIntegral (μb b).weight)
    {qE cE : ℕ} (hDE : ∏ j ∈ E, joinModuli m₀ (p L) j = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE)
    (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (hne : ∏ j ∈ E, joinModuli m₀ (p L) j ≠ 1)
    {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (Q' : Slot → ℝ) {Cdc σ : ℝ}
    (hrest : ∀ (v : Slot) (B : Finset ℤ),
      B ⊆ Icc 1 ((blockScale * stepEll (joinModuli m₀ (p L)) E 1 (blockScale * L) : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor μb)
          (child (joinModuli m₀ (p L)) E (Q' v) B
            (blockScale * stepEll (joinModuli m₀ (p L)) E 1 (blockScale * L))) ≤
        Yf (stepEll (joinModuli m₀ (p L)) E 1 (blockScale * L)) B)
    (hinvT : ∀ (j : ℤ) (F : (Slot → ResidueSpace (joinModuli m₀ (p L))) → ℝ),
      (FiniteLaw.tensor μb).expect
          (fun w => F (fun v' => stepMapOff (joinModuli m₀ (p L)) E
            (stepR (joinModuli m₀ (p L)) E 1) 0 j (w v'))) =
        (FiniteLaw.tensor μb).expect F)
    (hdc : |structuredEnergy (FiniteLaw.tensor μb) P
          (liftWeight E (selectedWeight E (joinLaws m₀ p L Λa lam0))
            (uniformRest (Xa := fun b => ZMod ((joinModuli m₀ (p L)) b)) E))
          (paperInputs (joinModuli m₀ (p L)) E (paperCutoff (blockScale * L)) A (fun _ => 1)
            (fun _ => blockScale * L) (fun _ _ => 0)
            (fun _ _ => 0)) -
        structuredEnergy (FiniteLaw.tensor μb) P
          (liftWeight E (selectedWeight E (joinLaws m₀ p L Λa lam0))
            (uniformRest (Xa := fun b => ZMod ((joinModuli m₀ (p L)) b)) E))
          (unchangedModel (joinModuli m₀ (p L)) E A L Q')| ≤
      Cdc * totalVariation (selectedWeight E (joinLaws m₀ p L Λa lam0)) * (L : ℝ) ^ (-σ) *
        density (blockScale * L) A)
    (hatom : ∀ (b : {b // b ∈ E})
      (hb : 0 < totalVariation (lawDensity (joinLaws m₀ p L Λa lam0 b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |diagonalIntegral (tensorLaw Λa) (atomLift m₀ p L A)| ≤
      (∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod ((joinModuli m₀ (p L)) b),
          |lawDensity (joinLaws m₀ p L Λa lam0 b) y|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
            ((stepR (joinModuli m₀ (p L)) E 1 : ℕ) : ℝ) ^ a * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  rw [diagonalIntegral_atomLift_eq m₀ p L A Λa lam0 h0]
  exact abs_tensor_energy_le_unchanged_atoms (joinModuli m₀ (p L)) hpair hcex hθ hθ2 ha hC0 hL hY0
    hsc hM0 μb hμb (joinLaws m₀ p L Λa lam0) E hE hDE hqE hcE hcE0 hcQ hcopE hqN hne P
    (paperCutoff (blockScale * L)) Q' hrest hinvT hdc hatom

end Sarkozy.EnvelopeInputs
