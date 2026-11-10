module

public import Sarkozy.PaperFrame.Restoration
public import Sarkozy.PaperFrame.TailMarginal

@[expose] public section

/-!
# `lem:record:fibre-scale`(c) at the paper's scales

For the comparison worker's reference law `paperLaw = μ₀ ⊗ ⊗_{q ∈ T L} μ_q` with the tail
`J L = ↥(T L)`, `p L j = j` (the primes of `T L`), and a smaller scale `ℓ` with
`T ℓ ⊆ T L` whose missing primes all exceed `n^β`, `n = Kℓ`:

`Z_{μ_N}(h_j) ≤ Y(ℓ, A'_j)`,

where `h_j` is the square-step piece (labels vanishing on the selected coordinates `E`,
cutoff `n^β`, interval `[n]`) and `Y(ℓ, ·) = prefixedFunctional … ℓ` is the paper's
functional at the scale `ℓ`. The proof combines

* the averaging step (`referenceEnergy_stepLift_le_equiv`; `lem:record:holder`(d)), with the
  reflection positivity of `μ_N` from that of the atom laws and the translation invariance
  of `μ_N` from that of the atom laws (`paperLaw_translate`, (R3) with `r_p = 1`);
* the lift at the smaller scale (`lift_restrictScale`: characters of conductor `≤ n^β`
  involve only primes `≤ n^β`);
* the marginal of the reference law on the coordinates of `G_n` (`paperLaw_marginal`; the
  atom laws do not depend on the scale, (R1)).

`Z_{μ_N}(h_j)` is the paper's `Z_𝒮(h_j)` when `μ_N` factors along the selected atoms and
their complement (Fubini, `referenceEnergy_comp_fst`), because `h_j` does not depend on the
coordinates of `E` (`stepLift_congr`); with the prefix as one atom this factorization is
not assumed here.
-/

open Finset Function
open scoped BigOperators ComplexConjugate

namespace Sarkozy.PaperFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.Comparison

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  (T : ℕ → Finset ℕ) [∀ L (j : ↥(T L)), NeZero (j : ℕ)]

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L (j : ↥(T L)), NeZero (j : ℕ)] in
theorem restrictScale_splitEquiv_symm {ℓ L : ℕ} (hT : T ℓ ⊆ T L)
    (x : ResidueSpace m₀ × ResidueSpace (tailModuli T L)) :
    restrictScale m₀ T hT ((splitEquiv m₀ (tailModuli T L)).symm x) =
      (splitEquiv m₀ (tailModuli T ℓ)).symm (x.1, tailRestrict T hT x.2) := by
  funext k
  match k with
  | Sum.inl i => rfl
  | Sum.inr j => rfl

/-- **`lem:record:fibre-scale`(c) at the paper's scales**: `Z_{μ_N}(h_j) ≤ Y(ℓ, A'_j)`. -/
theorem fibreScale_restoration_paper {ℓ L : ℕ} (hT : T ℓ ⊆ T L)
    (hprime : ∀ q ∈ T L, q.Prime)
    (hlarge : ∀ q ∈ T L, q ∉ T ℓ → paperCutoff (blockScale * ℓ) < q)
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hinv₀ : ∀ (s₀ : ResidueSpace m₀) (F : (Slot → ResidueSpace m₀) → ℝ),
      μ₀.expect (fun z => F (fun v => z v + s₀)) = μ₀.expect F)
    (hinvp : ∀ (q : ℕ) [NeZero q] (r : ZMod q) (F : (Slot → ZMod q) → ℝ),
      (μp q).expect (fun z => F (fun v => z v + r)) = (μp q).expect F)
    (E : Finset (J₀ ⊕ ↥(T L))) (B : Finset ℤ) :
    referenceEnergy (paperLaw m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) μ₀ μp L)
        (fun w => (stepLift (joinModuli m₀ (tailModuli T L)) E (paperCutoff (blockScale * ℓ)) B
          (blockScale * ℓ) ((splitEquiv m₀ (tailModuli T L)).symm w)).re) ≤
      prefixedFunctional m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ))
        (paperLaw m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) μ₀ μp) ℓ B := by
  have hrp : SlotReflectionPositive (signedIntegral
      (paperLaw m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) μ₀ μp L).weight) :=
    slotReflectionPositive_slotProduct hp₀
      (tensor_slot_reflection_positive _ fun j => hpp _ (hprime j.1 j.2))
  have h1 := referenceEnergy_stepLift_le_equiv (joinModuli m₀ (tailModuli T L))
    (splitEquiv m₀ (tailModuli T L)).symm
    (paperLaw m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) μ₀ μp L) hrp E
    (fun s _ F => paperLaw_translate m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) μ₀ μp
      hinv₀ hinvp L s F) (paperCutoff (blockScale * ℓ)) B (blockScale * ℓ)
  refine h1.trans (le_of_eq ?_)
  have h2 : ∀ x : ResidueSpace m₀ × ResidueSpace (tailModuli T L),
      (Functional.lift (joinModuli m₀ (tailModuli T L)) (paperCutoff (blockScale * ℓ))
          (Icc 1 ((blockScale * ℓ : ℕ) : ℤ)) (indicator B)
          ((splitEquiv m₀ (tailModuli T L)).symm x)).re =
        (wholeLift (joinModuli m₀ (tailModuli T ℓ)) (paperCutoff (blockScale * ℓ))
          (blockScale * ℓ) B ((splitEquiv m₀ (tailModuli T ℓ)).symm (x.1, tailRestrict T hT x.2))).re := by
    intro x
    rw [lift_restrictScale m₀ T hT hprime hlarge, restrictScale_splitEquiv_symm]
    rfl
  unfold referenceEnergy
  simp_rw [h2]
  unfold prefixedFunctional referenceEnergy
  exact paperLaw_marginal m₀ T μ₀ μp hT (fun y => ∏ v,
    (wholeLift (joinModuli m₀ (tailModuli T ℓ)) (paperCutoff (blockScale * ℓ)) (blockScale * ℓ) B
      ((splitEquiv m₀ (tailModuli T ℓ)).symm (y v))).re)

/-- **The induction input of the comparison** (`lem:record:fibre-scale`(c) with the
induction hypothesis at the smaller scale; "the only use of the induction hypothesis"):
the children `A'_j ⊆ [n]` of a square step are admissible at the scale `ℓ` (`n = Kℓ`), so
the energy of the square-step piece `h_j` is bounded by the induction bound
`Y(ℓ, A'_j) ≤ C ℓ^{-a} α_j^θ` (`EnergyUpperBoundAt` at the scale `ℓ`). This is the input
`Z(h_j) ≤ B α_j^θ` of `Sarkozy.SignedHolder.fibre_energy_le` (`Comparison/FibreEnergy.lean`). -/
theorem fibreScale_child_energy_le {ℓ L : ℕ} (hT : T ℓ ⊆ T L)
    (hprime : ∀ q ∈ T L, q.Prime)
    (hlarge : ∀ q ∈ T L, q ∉ T ℓ → paperCutoff (blockScale * ℓ) < q)
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hinv₀ : ∀ (s₀ : ResidueSpace m₀) (F : (Slot → ResidueSpace m₀) → ℝ),
      μ₀.expect (fun z => F (fun v => z v + s₀)) = μ₀.expect F)
    (hinvp : ∀ (q : ℕ) [NeZero q] (r : ZMod q) (F : (Slot → ZMod q) → ℝ),
      (μp q).expect (fun z => F (fun v => z v + r)) = (μp q).expect F)
    {C : ℝ}
    (hind : EnergyUpperBoundAt (prefixedFunctional m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ))
      (paperLaw m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) μ₀ μp)) C ℓ)
    (E : Finset (J₀ ⊕ ↥(T L))) {A : Finset ℤ} (hA : IsSquareDifferenceFree A) (I : Finset ℤ)
    {R r : ℕ} (hR : R = r ^ 2) (hr : 1 ≤ r) (c j : ℤ) :
    referenceEnergy (paperLaw m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) μ₀ μp L)
        (fun w => (stepLift (joinModuli m₀ (tailModuli T L)) E (paperCutoff (blockScale * ℓ))
          (stepChild A I R (blockScale * ℓ) c j) (blockScale * ℓ)
          ((splitEquiv m₀ (tailModuli T L)).symm w)).re) ≤
      C * (ℓ : ℝ) ^ (-decay) *
        density (blockScale * ℓ) (stepChild A I R (blockScale * ℓ) c j) ^ densityExponent :=
  (fibreScale_restoration_paper m₀ T hT hprime hlarge μ₀ μp hp₀ hpp hinv₀ hinvp E _).trans
    (hind _ (stepChild_admissible hA I hR hr (blockScale * ℓ) c j))

end Sarkozy.PaperFrame
