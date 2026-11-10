module

public import Sarkozy.Variance.Interpolation

/-!
# Eligible records, repairs and the zero-marginal identity (`def:record:eligible`)

`paper/sections/22_variance.tex`, Section 22.1: `def:record:eligible`, the identity
`eq:record:zero-marginal`, and `hyp:variance:A`.

**Status.** The record laws `Π_{φ,𝔅}` of the four eligible records and the comparison-law
repairs are constructions of Sections 20–21 that are not yet defined in Lean (V1's
`PartV/` defines the reference and its components, not the records' actual half marginals).
So the definition is stated for **abstract data with the paper's hypotheses**: a cut `c` (the
reserved cut `ι`), a record law `Π` and its actual half marginal `m` (a probability on the plus
half labels), and an invariance predicate `Inv` standing for "invariant under independent
square-affine maps at the primes of `𝔅`".

* `EligibleRecord`: the four eligible records `F₁, F₂, E₀, E₁` of a middle block.
* `HasHalfMarginals c κ m`: `κ` has half marginal `m` on both sides of `c`, in form language
  (`Q_κ(F, 1) = ∑ m F`, `Q_κ(1, G) = ∑ m G`).
* `IsRepair c Inv m Π'`: **a repair** in the sense of `def:record:eligible`: a signed measure of
  mass one that is a finite real combination of nonnegative measures, each satisfying `Inv`
  and with the actual half marginal `m` on both sides of `c`.
* `IsRepair.hasHalfMarginals`: a repair has the half marginal `m` itself (when `∑ m = 1`).
* `zero_marginal`: **`eq:record:zero-marginal`**: if `Π` and its repair `Π'` both have the half
  marginal `m`, the record difference `Δ` (the cut form of `Π' - Π` relative to `m`) satisfies
  `Δ 1 = Δ* 1 = 0`, and `Δ = (I - 𝒥) Δ (I - 𝒥)` (`zero_marginal_centred`); the same holds for
  its symmetric and skew parts (`zero_marginal_symPart`, `zero_marginal_skewPart`).
* `RootDensityA`: **`hyp:variance:A`**, `M⁻¹ ≤ dν/dλ ≤ M` for half laws on a finite set.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

/-- The four **eligible records** of a middle block (`def:record:eligible`): the two
nonaligned folds `F₁, F₂` and the two matchings `E₀, E₁`. -/
inductive EligibleRecord
  | F1
  | F2
  | E0
  | E1
  deriving DecidableEq

instance : Fintype EligibleRecord where
  elems := {EligibleRecord.F1, EligibleRecord.F2, EligibleRecord.E0, EligibleRecord.E1}
  complete x := by cases x <;> simp

/-- An eligible record is a fold (`F₁, F₂`) or a matching (`E₀, E₁`). -/
def EligibleRecord.IsFold : EligibleRecord → Prop
  | F1 => True
  | F2 => True
  | E0 => False
  | E1 => False

theorem card_eligibleRecord : Fintype.card EligibleRecord = 4 := rfl

section Defs

variable {W Y : Type*} [Fintype W] [DecidableEq W] [Fintype Y] [DecidableEq Y]

/-- `κ` has the half marginal `m` on both sides of the cut `c` (form language:
`Q_κ(F, 1) = ∑ m F` and `Q_κ(1, G) = ∑ m G`). -/
def HasHalfMarginals (c : ReflectionCut W) (κ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (m : (c.Half → Y) → ℝ) : Prop :=
  (∀ F : (c.Half → Y) → ℝ, c.form κ F 1 = ∑ x, m x * F x) ∧
    ∀ G : (c.Half → Y) → ℝ, c.form κ 1 G = ∑ x, m x * G x

/-- A nonnegative weight whose two half marginals are `m` has the half marginal `m` in form
language. -/
theorem hasHalfMarginals_of_weight (c : ReflectionCut W) {w : (W → Y) → ℝ}
    {m : (c.Half → Y) → ℝ} (hp : plusMarginal c w = m) (hm : minusMarginal c w = m) :
    HasHalfMarginals c (signedIntegral w) m :=
  ⟨fun F => by rw [form_signedIntegral_one_right, hp],
    fun G => by rw [form_signedIntegral_one_left, hm]⟩

/-- **A repair** (`def:record:eligible`) of a record with actual half marginal `m` at `c`: a
signed measure of mass one that is a finite real combination of nonnegative measures, each
satisfying the invariance `Inv` (independent square-affine maps at the primes of the block) and
with the half marginal `m` on both sides of `c`. -/
def IsRepair (c : ReflectionCut W) (Inv : (((W → Y) → ℝ) →ₗ[ℝ] ℝ) → Prop)
    (m : (c.Half → Y) → ℝ) (Pr' : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  (∃ (n : ℕ) (a : Fin n → ℝ) (w : Fin n → (W → Y) → ℝ),
    (∀ i z, 0 ≤ w i z) ∧ (∀ i, Inv (signedIntegral (w i))) ∧
      (∀ i, plusMarginal c (w i) = m ∧ minusMarginal c (w i) = m) ∧
        Pr' = ∑ i, a i • signedIntegral (w i)) ∧
    Pr' (fun _ => 1) = 1

omit [Fintype Y] [DecidableEq Y] in
/-- The form of a finite combination. -/
theorem form_sum_smul (c : ReflectionCut W) {n : ℕ} (a : Fin n → ℝ)
    (K : Fin n → ((W → Y) → ℝ) →ₗ[ℝ] ℝ) (F G : (c.Half → Y) → ℝ) :
    c.form (∑ i, a i • K i) F G = ∑ i, a i * c.form (K i) F G := by
  unfold ReflectionCut.form
  rw [LinearMap.sum_apply]
  rfl

/-- A repair has the half marginal `m` itself, when `m` is a probability (`∑ m = 1`): the
coefficients of its combination sum to one by the mass condition. -/
theorem IsRepair.hasHalfMarginals {c : ReflectionCut W}
    {Inv : (((W → Y) → ℝ) →ₗ[ℝ] ℝ) → Prop} {m : (c.Half → Y) → ℝ}
    {Pr' : ((W → Y) → ℝ) →ₗ[ℝ] ℝ} (h : IsRepair c Inv m Pr') (hm1 : ∑ x, m x = 1) :
    HasHalfMarginals c Pr' m := by
  obtain ⟨⟨n, a, w, -, -, hmarg, rfl⟩, hmass⟩ := h
  -- the mass of each component is `∑ m = 1`
  have hmass_i : ∀ i, signedIntegral (w i) (fun _ => 1) = 1 := by
    intro i
    have h1 := form_signedIntegral_one_right c (w i) 1
    rw [(hmarg i).1] at h1
    simp only [Pi.one_apply, mul_one] at h1
    rw [hm1] at h1
    have h2 : c.form (signedIntegral (w i)) 1 1 = signedIntegral (w i) (fun _ => 1) := by
      unfold ReflectionCut.form
      congr 1
      funext z
      simp
    rw [← h2]
    exact h1
  have hsum_a : ∑ i, a i = 1 := by
    rw [LinearMap.sum_apply] at hmass
    simp only [LinearMap.smul_apply, smul_eq_mul, hmass_i, mul_one] at hmass
    exact hmass
  constructor
  · intro F
    rw [form_sum_smul]
    simp_rw [form_signedIntegral_one_right, fun i => (hmarg i).1]
    rw [← sum_mul, hsum_a, one_mul]
  · intro G
    rw [form_sum_smul]
    simp_rw [form_signedIntegral_one_left, fun i => (hmarg i).2]
    rw [← sum_mul, hsum_a, one_mul]

omit [DecidableEq Y] in
/-- **`eq:record:zero-marginal`**: if the record `Π` and its repair `Π'` both have the half
marginal `m` on both sides of `ι`, the record difference `Δ`, the cut form of `Π' - Π`,
annihilates the constants on both sides: `Δ 1 = 0` and `Δ* 1 = 0`. -/
theorem zero_marginal (c : ReflectionCut W) {Pr Pr' : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    {m : (c.Half → Y) → ℝ} (hPr : HasHalfMarginals c Pr m) (hPr' : HasHalfMarginals c Pr' m) :
    (∀ F : (c.Half → Y) → ℝ, c.form (Pr' - Pr) F 1 = 0) ∧
      ∀ G : (c.Half → Y) → ℝ, c.form (Pr' - Pr) 1 G = 0 := by
  constructor
  · intro F
    change c.form Pr' F 1 - c.form Pr F 1 = 0
    rw [hPr.1, hPr'.1, sub_self]
  · intro G
    change c.form Pr' 1 G - c.form Pr 1 G = 0
    rw [hPr.2, hPr'.2, sub_self]

omit [Fintype Y] [DecidableEq Y] in
/-- A form that annihilates the constants on both sides sees only the centred parts:
`Q(F, G) = Q(F - a, G - b)` for all constants `a, b`. -/
theorem form_centred_of_zero_marginal (c : ReflectionCut W) {Δ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (h1 : ∀ F : (c.Half → Y) → ℝ, c.form Δ F 1 = 0)
    (h2 : ∀ G : (c.Half → Y) → ℝ, c.form Δ 1 G = 0) (F G : (c.Half → Y) → ℝ) (a b : ℝ) :
    c.form Δ F G = c.form Δ (fun x => F x - a) (fun x => G x - b) := by
  have hF : (fun x => F x - a) = F - a • (1 : (c.Half → Y) → ℝ) := by
    funext x
    simp
  have hG : (fun x => G x - b) = G - b • (1 : (c.Half → Y) → ℝ) := by
    funext x
    simp
  rw [hF, hG]
  have bil : ∀ (P Q R : (c.Half → Y) → ℝ) (s t : ℝ),
      c.form Δ (P - s • Q) R = c.form Δ P R - s * c.form Δ Q R := by
    intro P Q R s t
    change Δ _ = Δ _ - s • Δ _
    rw [← map_smul, ← map_sub]
    congr 1
    funext z
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have bil' : ∀ (P Q R : (c.Half → Y) → ℝ) (s : ℝ),
      c.form Δ R (P - s • Q) = c.form Δ R P - s * c.form Δ R Q := by
    intro P Q R s
    change Δ _ = Δ _ - s • Δ _
    rw [← map_smul, ← map_sub]
    congr 1
    funext z
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [bil F 1 _ a 0, bil' G 1 F b, bil' G 1 1 b, h1, h2, h2]
  ring

omit [DecidableEq Y] in
/-- **`eq:record:zero-marginal`, the centred form**: `Δ = (I - 𝒥) Δ (I - 𝒥)`, i.e.
`Q_{Π'-Π}(F, G) = Q_{Π'-Π}(F - E_m F, G - E_m G)`. -/
theorem zero_marginal_centred (c : ReflectionCut W) {Pr Pr' : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    {m : (c.Half → Y) → ℝ} (hPr : HasHalfMarginals c Pr m) (hPr' : HasHalfMarginals c Pr' m)
    (F G : (c.Half → Y) → ℝ) :
    c.form (Pr' - Pr) F G =
      c.form (Pr' - Pr) (fun x => F x - (∑ y, m y * F y) / ∑ y, m y)
        (fun x => G x - (∑ y, m y * G y) / ∑ y, m y) :=
  form_centred_of_zero_marginal c (zero_marginal c hPr hPr').1 (zero_marginal c hPr hPr').2 F G _ _

omit [DecidableEq Y] in
/-- The symmetric part of the record difference also annihilates the constants. -/
theorem zero_marginal_symPart (c : ReflectionCut W) {Pr Pr' : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    {m : (c.Half → Y) → ℝ} (hPr : HasHalfMarginals c Pr m) (hPr' : HasHalfMarginals c Pr' m) :
    (∀ F : (c.Half → Y) → ℝ, c.form (symPart c (Pr' - Pr)) F 1 = 0) ∧
      ∀ G : (c.Half → Y) → ℝ, c.form (symPart c (Pr' - Pr)) 1 G = 0 := by
  obtain ⟨h1, h2⟩ := zero_marginal c hPr hPr'
  constructor
  · intro F
    change (1 / 2 : ℝ) * (c.form (Pr' - Pr) F 1 + c.form (reflect c (Pr' - Pr)) F 1) = 0
    rw [form_reflect, h1, h2]
    ring
  · intro G
    change (1 / 2 : ℝ) * (c.form (Pr' - Pr) 1 G + c.form (reflect c (Pr' - Pr)) 1 G) = 0
    rw [form_reflect, h1, h2]
    ring

omit [DecidableEq Y] in
/-- The skew part of the record difference also annihilates the constants. -/
theorem zero_marginal_skewPart (c : ReflectionCut W) {Pr Pr' : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    {m : (c.Half → Y) → ℝ} (hPr : HasHalfMarginals c Pr m) (hPr' : HasHalfMarginals c Pr' m) :
    (∀ F : (c.Half → Y) → ℝ, c.form (skewPart c (Pr' - Pr)) F 1 = 0) ∧
      ∀ G : (c.Half → Y) → ℝ, c.form (skewPart c (Pr' - Pr)) 1 G = 0 := by
  obtain ⟨h1, h2⟩ := zero_marginal c hPr hPr'
  constructor
  · intro F
    change (1 / 2 : ℝ) * (c.form (Pr' - Pr) F 1 - c.form (reflect c (Pr' - Pr)) F 1) = 0
    rw [form_reflect, h1, h2]
    ring
  · intro G
    change (1 / 2 : ℝ) * (c.form (Pr' - Pr) 1 G - c.form (reflect c (Pr' - Pr)) 1 G) = 0
    rw [form_reflect, h1, h2]
    ring

end Defs

/-- **`hyp:variance:A`** (root density): at the fold chamber, the actual half law `ν` of the
root and the law `λ` whose diagonal copy is the record satisfy `M⁻¹ ≤ dν/dλ ≤ M`, i.e.
`M⁻¹ λ ≤ ν ≤ M λ` pointwise on the (finite) half labels. -/
def RootDensityA {S : Type*} (ν lam : S → ℝ) (M : ℝ) : Prop :=
  ∀ x, M⁻¹ * lam x ≤ ν x ∧ ν x ≤ M * lam x

/-- Hypothesis (A) gives the upper density bound used in the pointwise branch of
`lem:record:restoration`. -/
theorem RootDensityA.le {S : Type*} {ν lam : S → ℝ} {M : ℝ} (h : RootDensityA ν lam M) (x : S) :
    ν x ≤ M * lam x :=
  (h x).2

/-- Hypothesis (A) gives absolute continuity `ν ≪ λ` when `λ ≥ 0` and `M > 0`... in the form
used by the chi-square steps: `λ x = 0 → ν x = 0` once `ν ≥ 0`. -/
theorem RootDensityA.ac {S : Type*} {ν lam : S → ℝ} {M : ℝ} (h : RootDensityA ν lam M)
    (hν : ∀ x, 0 ≤ ν x) (x : S) (hx : lam x = 0) : ν x = 0 := by
  have := (h x).2
  rw [hx, mul_zero] at this
  exact le_antisymm this (hν x)

/-- Non-vacuity of `hyp:variance:A`: `ν = λ` satisfies it with `M = 1`. -/
theorem rootDensityA_refl {S : Type*} (lam : S → ℝ) : RootDensityA lam lam 1 := fun x => by
  simp

end Sarkozy.Variance
