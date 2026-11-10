module

public import Sarkozy.Functional.Lift
public import Sarkozy.Moments.Energy

@[expose] public section

/-!
# The paper's functional `Y(L, A)` as a `FourierModel` (`def:record:functional`(e))

`def:record:functional`(e) defines `Y(L, A) = Z_N(F_A)`, the multilinear
average `Λ_{μ_N}` of the whole-interval lift `F_A = 𝓛_{[N],N} 1_A` under the
reference law `μ_N` on `G_N^V`, `N = K L`, `Q = N^β`, `β = 1/20`.

This module packages the data that are *not* constructed here — the prime-power
family of `G_N` at every scale and the reference laws `μ_N` (Part V of the
paper) — as `FunctionalData`, defines `Y` from it, and identifies the
project's `FourierModel.energy` of the associated model with `Y` on every
admissible set (`energy_eq_functional`). With `K = blockScale = 863660` (the
paper's selected `K`, `\FourRoutesK`), the existing endgame
`FourierModel.powerSavingBound` can therefore be applied with its analytic
hypotheses stated for the paper's functional itself
(`FunctionalData.powerSavingBound`).

The reference laws enter only through the endgame's hypotheses (uniform
marginals and reflection positivity at the sorting cuts, (R2)–(R3) of
`hyp:record:reference`); this module does not assume that `μ_N` is a product
of atom laws, which the endgame does not use.
-/

open Finset
open scoped BigOperators Topology

namespace Sarkozy.Functional

open Sarkozy.FourierArithmetic

/-- The lift exponent `β = 1/20` of `def:record:functional`. -/
noncomputable def liftExponent : ℝ := 1 / 20

/-- The cutoff `Q = N^β` of `def:record:functional`(a). -/
noncomputable def paperCutoff (N : ℕ) : ℝ := (N : ℝ) ^ liftExponent

theorem one_le_paperCutoff {N : ℕ} (hN : 1 ≤ N) : 1 ≤ paperCutoff N :=
  Real.one_le_rpow (by exact_mod_cast hN) (by norm_num [liftExponent])

/-- The data of `def:record:functional` not constructed in this development:
for every interval scale `L`, the prime-power family of `G_N` (`N = K L`,
`K = blockScale`), e.g. `𝒫_N = 𝒫₁ ∪ 𝒫₃ ∪ 𝒯_N` with `e_p = 2 m_p` on `𝒫₁`, and
the reference law `μ_N` on `G_N^V`. -/
structure FunctionalData where
  family : ℕ → PrimePowerFamily
  law : ∀ L, FiniteLaw (Slot → (family L).Group)

namespace FunctionalData

variable (d : FunctionalData)

/-- The lift `F_A` at the interval scale `L` (with `N = K L`, `Q = N^β`). -/
noncomputable def liftAt (L : ℕ) (A : Finset ℤ) (z : (d.family L).Group) : ℝ :=
  (wholeLift (d.family L).modulus (paperCutoff (blockScale * L)) (blockScale * L) A z).re

/-- The functional `Y(L, A) = Z_N(F_A)` of `def:record:functional`(e). -/
noncomputable def functional (L : ℕ) (A : Finset ℤ) : ℝ :=
  referenceEnergy (d.law L) (d.liftAt L A)

open Classical in
/-- `Y_max(L)`, the maximum of `Y(L, A)` over the square-difference-free
`A ⊆ [N]` (`def:record:functional`(e)); the maximum exists because there are
finitely many such sets and `∅` is one of them. -/
noncomputable def functionalMax (L : ℕ) : ℝ :=
  ((Icc 1 ((blockScale * L : ℕ) : ℤ)).powerset.filter IsSquareDifferenceFree).sup'
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset _, (admissible_empty (blockScale * L)).2⟩⟩
    (d.functional L)

theorem functional_le_functionalMax (L : ℕ) {A : Finset ℤ}
    (hA : Admissible (blockScale * L) A) : d.functional L A ≤ d.functionalMax L := by
  classical
  unfold functionalMax
  apply le_sup'
  exact mem_filter.mpr ⟨mem_powerset.mpr hA.1, hA.2⟩

theorem exists_functional_eq_functionalMax (L : ℕ) :
    ∃ A : Finset ℤ, Admissible (blockScale * L) A ∧ d.functional L A = d.functionalMax L := by
  classical
  unfold functionalMax
  obtain ⟨A, hA, he⟩ := exists_mem_eq_sup'
    (⟨∅, mem_filter.mpr ⟨empty_mem_powerset _, (admissible_empty (blockScale * L)).2⟩⟩ :
      ((Icc 1 ((blockScale * L : ℕ) : ℤ)).powerset.filter IsSquareDifferenceFree).Nonempty)
    (d.functional L)
  obtain ⟨hA1, hA2⟩ := mem_filter.mp hA
  exact ⟨A, ⟨mem_powerset.mp hA1, hA2⟩, he.symm⟩

/-- The `FourierModel` of the paper's lift: residue map `n ↦ (n mod p^{e_p})_p`,
retained characters `{ξ : q(ξ) ≤ N^β}`, reference laws `μ_N`. -/
noncomputable def toFourierModel : FourierModel (fun L => (d.family L).Group) where
  residue L := integerResidue (d.family L).modulus
  characters L := retainedCharacters (d.family L).modulus (paperCutoff (blockScale * L))
  law L := d.law L

/-- The project's `fourierLift` of the model is the paper's lift `F_A`. -/
theorem fourierLift_eq_liftAt (L : ℕ) {A : Finset ℤ}
    (hA : A ⊆ Icc 1 ((blockScale * L : ℕ) : ℤ)) :
    fourierLift (d.toFourierModel.residue L) (blockScale * L) A (d.toFourierModel.characters L) =
      d.liftAt L A := by
  funext z
  exact fourierLift_eq_re_wholeLift (d.family L).modulus _ _ hA z

/-- The model's energy is the paper's functional `Y(L, A)` for every `A ⊆ [N]`. -/
theorem energy_eq_functional (L : ℕ) {A : Finset ℤ}
    (hA : A ⊆ Icc 1 ((blockScale * L : ℕ) : ℤ)) :
    d.toFourierModel.energy L A = d.functional L A := by
  unfold FourierModel.energy functional
  rw [d.fourierLift_eq_liftAt L hA]
  rfl

/-- The model is regular as soon as the reference laws have uniform one-slot
marginals and are reflection positive at the sorting cuts ((R2), (R3)); the
trivial character is retained because `q(0) = 1 ≤ N^β`. -/
theorem regular (hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (d.law L))
    (hp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (d.law L).weight)) :
    d.toFourierModel.Regular := by
  intro L hL
  refine ⟨retainedCharacters_one _ (one_le_paperCutoff ?_), hm L hL, hp L hL⟩
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by norm_num [blockScale]) (by omega))

theorem globalMomentBound_iff (M : ℝ) :
    GlobalMomentBound d.toFourierModel.energy M ↔ GlobalMomentBound d.functional M := by
  unfold GlobalMomentBound
  constructor
  · intro h L hL A hA
    rw [← d.energy_eq_functional L hA.1]
    exact h L hL A hA
  · intro h L hL A hA
    rw [d.energy_eq_functional L hA.1]
    exact h L hL A hA

theorem energyUpperBoundAt_iff (C : ℝ) (k : ℕ) :
    EnergyUpperBoundAt d.toFourierModel.energy C k ↔ EnergyUpperBoundAt d.functional C k := by
  unfold EnergyUpperBoundAt
  constructor
  · intro h A hA
    rw [← d.energy_eq_functional k hA.1]
    exact h A hA
  · intro h A hA
    rw [d.energy_eq_functional k hA.1]
    exact h A hA

theorem rawComparison_iff (q : ℕ → ℝ) (E : ℝ) :
    RawComparison d.toFourierModel.energy q E ↔ RawComparison d.functional q E := by
  unfold RawComparison
  constructor
  · intro h
    filter_upwards [h] with L hL C hC hind A hA
    have hind' : ∀ k : ℕ, 1 ≤ k → k < L → EnergyUpperBoundAt d.toFourierModel.energy C k :=
      fun k hk hkL => (d.energyUpperBoundAt_iff C k).mpr (hind k hk hkL)
    rw [← d.energy_eq_functional L hA.1]
    exact hL C hC hind' A hA
  · intro h
    filter_upwards [h] with L hL C hC hind A hA
    have hind' : ∀ k : ℕ, 1 ≤ k → k < L → EnergyUpperBoundAt d.functional C k :=
      fun k hk hkL => (d.energyUpperBoundAt_iff C k).mp (hind k hk hkL)
    rw [d.energy_eq_functional L hA.1]
    exact hL C hC hind' A hA

/-- The existing endgame (`FourierModel.powerSavingBound`) with its analytic
hypotheses stated for the paper's functional `Y`: reflection positivity and
uniform marginals of the reference laws, the closing ledger, the global moment
bound for `Y`, and the raw comparison for `Y`. -/
theorem powerSavingBound (hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (d.law L))
    (hp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (d.law L).weight))
    {l : ClosingLedger} (hledger : l.Bounds) {M E : ℝ} {q : ℕ → ℝ} (hM : 0 < M) (hE : 0 ≤ E)
    (hglobal : GlobalMomentBound d.functional M) (hrec : RawComparison d.functional q E)
    (hq : Filter.Tendsto q Filter.atTop (𝓝 l.theta)) : PowerSavingBound :=
  d.toFourierModel.powerSavingBound (d.regular hm hp) hledger hM hE
    ((d.globalMomentBound_iff M).mpr hglobal) ((d.rawComparison_iff q E).mpr hrec) hq

end FunctionalData

end Sarkozy.Functional
