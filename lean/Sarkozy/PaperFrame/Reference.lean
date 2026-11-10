module

public import Sarkozy.PaperFrame.Atoms
public import Sarkozy.Comparison.PaperMain
public import Sarkozy.Comparison.ConcreteFrame

@[expose] public section

/-!
# The paper's functional as a frame energy of the reference laws

`def:record:functional`(d),(e): the reference law is the product `μ_N = ⊗_𝔟 μ_𝔟` of the
atom laws, and `Y(L, A) = Z_N(F_A) = Λ_{μ_N}(F_A)`. The concrete energies of
`Sarkozy.Comparison.ConcreteFrame` are cut forms `Q_κ(X̄, X̄)` of tensor products of
per-atom functionals at the reserved cut. This module proves that the two descriptions
agree for the atoms of `Sarkozy.PaperFrame.Atoms` (the prefix and the tail primes):

* `form_barHalf` (`eq:cc:bilinear` on the diagonal):
  `Q_κ(X̄, X̄) = κ(∏_v F(z_v))`, the diagonal multilinear average;
* `tensorLaw_refLaws`: the tensor product over the atoms of the reference functionals
  (`μ₀` at the prefix, `μ_p` at the tail primes) is the comparison worker's reference law
  `paperLaw = μ₀ ⊗ ⊗_p μ_p`, transported along `atomEquiv`;
* `energyFirst_refLaws`: the `energyFirst` of the reference laws and the paper's lift
  `atomLift` is the paper's functional `prefixedFunctional … (paperLaw …)`, so the
  firstStage inequality of `ClosingEstimates.ofConcrete` compares energies of the same
  lift over the same atoms; likewise `energyComparison_refLaws` and `energyMean_refLaws`.
-/

open Finset

namespace Sarkozy.PaperFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.Comparison

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- The per-atom reference functionals: `μ₀` at the prefix atom, `μ_p` at the tail prime
`p` (`def:record:functional`(d)). -/
noncomputable def refLaws (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ) :
    ∀ b : PaperAtom J L, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ
  | none => signedIntegral μ₀.weight
  | some j => signedIntegral (μp (p L j)).weight

/-- `eq:cc:bilinear` on the diagonal: the cut form of `X̄` with itself is the diagonal
multilinear average of `F`. -/
theorem form_barHalf {Y : Type} (κ : ((Slot → Y) → ℝ) →ₗ[ℝ] ℝ) (G : Y → ℝ) :
    reservedCut.form κ (barHalf G) (barHalf G) = κ (fun z => ∏ v, G (z v)) := by
  unfold ReflectionCut.form barHalf
  congr 1
  funext z
  exact (reservedCut.prod_split (fun v => G (z v))).symm

theorem form_barHalf_eq_diagonal {Y : Type} (κ : ((Slot → Y) → ℝ) →ₗ[ℝ] ℝ) (G : Y → ℝ) :
    reservedCut.form κ (barHalf G) (barHalf G) = diagonalIntegral κ G :=
  form_barHalf κ G

/-- The density of a finite law's functional at a point is its weight. -/
theorem lawDensity_signedIntegral {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (w : Ω → ℝ)
    (x : Ω) : lawDensity (signedIntegral w) x = w x := by
  unfold lawDensity
  change (∑ y, w y * if y = x then (1 : ℝ) else 0) = w x
  simp

/-- The tensor product over the atoms of the reference functionals is the reference law
`paperLaw = μ₀ ⊗ ⊗_p μ_p` (`Sarkozy.Comparison.paperLaw`), transported along
`atomEquiv`. -/
theorem tensorLaw_refLaws (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ)
    (H : (Slot → ∀ b : PaperAtom J L, AtomLabel m₀ p L b) → ℝ) :
    tensorLaw (refLaws m₀ p μ₀ μp L) H =
      (paperLaw m₀ p μ₀ μp L).expect (fun w => H (fun v => (atomEquiv m₀ p L).symm (w v))) := by
  -- the right side as an iterated sum
  rw [paperLaw, FiniteLaw.expect_slotProduct]
  unfold primeTailLaw
  simp_rw [FiniteLaw.expect_eq_signedIntegral (FiniteLaw.tensor _), FiniteLaw.signedIntegral_tensor]
  -- the left side, split along `Option`
  change (∑ z : ∀ b : PaperAtom J L, Slot → AtomLabel m₀ p L b,
      (∏ b, lawDensity (refLaws m₀ p μ₀ μp L b) (z b)) * H (fun v b => z b v)) = _
  rw [← (Equiv.piOptionEquivProd (β := fun b : PaperAtom J L => Slot → AtomLabel m₀ p L b)).symm.sum_comp,
    Fintype.sum_prod_type]
  unfold FiniteLaw.expect
  apply sum_congr rfl
  intro z0 _
  change _ = μ₀.weight z0 * ∑ zt : ∀ j : J L, Slot → ZMod (p L j),
    (∏ j, lawDensity (signedIntegral (μp (p L j)).weight) (zt j)) *
      H (fun v => (atomEquiv m₀ p L).symm (z0 v, fun j => zt j v))
  rw [mul_sum]
  apply sum_congr rfl
  intro zt _
  rw [Fintype.prod_option]
  have h0 : lawDensity (refLaws m₀ p μ₀ μp L none)
      ((Equiv.piOptionEquivProd (β := fun b : PaperAtom J L => Slot → AtomLabel m₀ p L b)).symm
        (z0, zt) none) = μ₀.weight z0 := lawDensity_signedIntegral _ _
  have hj : ∀ j, lawDensity (refLaws m₀ p μ₀ μp L (some j))
      ((Equiv.piOptionEquivProd (β := fun b : PaperAtom J L => Slot → AtomLabel m₀ p L b)).symm
        (z0, zt) (some j)) = lawDensity (signedIntegral (μp (p L j)).weight) (zt j) := by
    intro j
    rw [lawDensity_signedIntegral]
    exact lawDensity_signedIntegral (μp (p L j)).weight (zt j)
  rw [h0, prod_congr rfl (fun j _ => hj j)]
  have hH : (fun v (b : PaperAtom J L) =>
      (Equiv.piOptionEquivProd (β := fun b : PaperAtom J L => Slot → AtomLabel m₀ p L b)).symm
        (z0, zt) b v) = fun v => (atomEquiv m₀ p L).symm (z0 v, fun j => zt j v) := by
    funext v b
    cases b <;> rfl
  rw [hH]
  ring

/-- The concrete energy of any per-atom family on the diagonal is the diagonal average of
its tensor product; with the reference laws it is an expectation under `paperLaw`. -/
theorem form_tensor_refLaws (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ)
    (G : (∀ b : PaperAtom J L, AtomLabel m₀ p L b) → ℝ) :
    reservedCut.form (tensorLaw (refLaws m₀ p μ₀ μp L)) (barHalf G) (barHalf G) =
      referenceEnergy (paperLaw m₀ p μ₀ μp L) (fun w => G ((atomEquiv m₀ p L).symm w)) := by
  rw [form_barHalf, tensorLaw_refLaws]
  rfl

/-- **`def:record:functional`(e) as a frame energy.** The `energyFirst` of the reference
laws over the paper's atoms, with the paper's lift `atomLift`, is the paper's functional
`Y(L, A) = prefixedFunctional … (paperLaw …) L A`. -/
theorem energyFirst_refLaws (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ) (A : Finset ℤ) :
    energyFirst (Atom := PaperAtom J) (Xb := AtomLabel m₀ p) (refLaws m₀ p μ₀ μp)
        (atomLift m₀ p) L A =
      prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp) L A := by
  unfold energyFirst
  rw [form_tensor_refLaws]
  unfold prefixedFunctional
  congr 1

/-- The same identity for `energyComparison` with the reference laws in place of `ν`. -/
theorem energyComparison_refLaws (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ) (A : Finset ℤ) :
    energyComparison (Atom := PaperAtom J) (Xb := AtomLabel m₀ p) (refLaws m₀ p μ₀ μp)
        (atomLift m₀ p) L A =
      prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp) L A :=
  energyFirst_refLaws m₀ p μ₀ μp L A

/-- The same identity for `energyMean` with the reference laws in place of an envelope. -/
theorem energyMean_refLaws (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ) (A : Finset ℤ) :
    energyMean (Atom := PaperAtom J) (Xb := AtomLabel m₀ p) (atomLift m₀ p)
        (refLaws m₀ p μ₀ μp) L A =
      prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp) L A :=
  energyFirst_refLaws m₀ p μ₀ μp L A

end Sarkozy.PaperFrame
