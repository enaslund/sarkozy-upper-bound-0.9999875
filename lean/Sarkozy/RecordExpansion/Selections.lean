module

public import Sarkozy.RecordExpansion.Multilinear

/-!
# Selections and the record expansion

This file formalizes the algebraic part of `lem:record:record-expansion` (i)
of the paper (Section 10, "Expanding `ν - λ` over changed blocks"), together
with the parity cancellation explained after (CP4) in Section 9
(`def:record:comparison-law`).

## Setting

* `J` is the finite set of atoms (the paper's `𝒜_N` at a fixed scale), `X b`
  the finite label set of the atom `b`, `V` the finite slot set, and `c` a cut
  of `V` (the reserved cut `ι` in the paper; any cut here).
* `lam b`, `ζ b t ε` and `ν b` are finite signed measures on `X_b^V`, given as
  linear functionals: the first-stage law `λ_b`, the symmetric (`ε = sym`) and
  skew (`ε = skew`) parts of the change of the record `t ∈ T b`, and the
  comparison law `ν_b`, with the decomposition of (CP4)(b)
  `ν_b = λ_b + ∑_{t ∈ T_b} (ζ^s_{b,t} + ζ^a_{b,t})`.
* Product measures over all atoms are `Sarkozy.tensorLaw`, on the labels
  `V → ∀ b, X b`; the energy of a measure `κ` is its diagonal evaluation
  `Y_κ = diagonalIntegral κ F = ∫ ∏_{v ∈ V} F(z_v) dκ`, for one common slot
  function `F` on `∏_b X_b` (the paper's `Y_κ = Q_κ(X̄, X̄)` with `F = F_A`).

## Selections

A `Choice` assigns to every atom either nothing or one changed record and one
type. Its support `X` is the set of atoms where something was chosen. A
selection of (CP4)(c) is a choice with nonempty support and an even number of
skew types (`Choice.IsSelection`); the paper's data `(X, (t_b, ε_b)_{b ∈ X})`
correspond bijectively to choices with support `X`. For a choice `ω`,
`choiceLaw lam ζ ω` is the paper's `ζ_ω ⊗ λ_{-X}`: the product over all atoms
of `ζ^{ε_b}_{b,t_b}` on `X` and of `λ_b` off `X` (the product of a measure on
`X_X^V` and one on `X_{-X}^V`, written directly over all atoms), and
`term lam ζ F ω` is `I_ω = Y_{ζ_ω ⊗ λ_{-X}}`.

## Main results

* `tensorLaw_sub_eq_sum`: `⊗_b ν_b - ⊗_b λ_b = ∑_{ω ≠ ∅} ζ_ω ⊗ λ_{-X}`, the sum
  over all nonempty choices (no parity restriction).
* `energy_sub_eq_sum_choices`: `Y_ν - Y_λ = ∑_{ω ≠ ∅} I_ω`.
* `term_eq_zero_of_odd`: if every `λ_b` and every `ζ^s_{b,t}` is symmetric at
  `c` and every `ζ^a_{b,t}` is skew, then `I_ω = 0` for every choice with an
  odd number of skew types.
* `energy_sub_eq_sum_selections`: hence `Y_ν - Y_λ = ∑_ω I_ω` over the
  selections of (CP4)(c), the first identity of `lem:record:record-expansion` (i).
* `energy_sub_eq_sum_selections_of_changes`: the same when `ζ^s_{b,t}`,
  `ζ^a_{b,t}` are defined as the symmetric and skew parts of given record
  changes `Δ_{b,t}` with `ν_b - λ_b = ∑_t Δ_{b,t}`, as in (CP4)(b); then only the
  symmetry of `λ_b` (required in (CP3)) is assumed.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.RecordExpansion

/-- The type `ε ∈ {s, a}` of a record change in (CP4)(b),(c): its symmetric
part (`sym`) or its skew part (`skew`) at the reserved cut. -/
inductive ChangeType
  | sym
  | skew
  deriving DecidableEq

instance : Fintype ChangeType where
  elems := {ChangeType.sym, ChangeType.skew}
  complete x := by cases x <;> simp

theorem sum_changeType {M : Type*} [AddCommMonoid M] (f : ChangeType → M) :
    ∑ e, f e = f .sym + f .skew := by
  change ∑ e ∈ {ChangeType.sym, ChangeType.skew}, f e = _
  rw [Finset.sum_pair (by decide)]

/-! ### Choices and selections -/

/-- A choice of at most one changed record and one type at every atom: `none`
off the selected set `X`, `some (t_b, ε_b)` at the atoms `b ∈ X`. A term of the
expansion of `⊗_b (λ_b + ∑_t (ζ^s_{b,t} + ζ^a_{b,t}))` chooses exactly such
data (Section 9, after (CP4)). -/
abbrev Choice {J : Type*} (T : J → Type*) := ∀ b, Option (T b × ChangeType)

/-- Whether one entry of a choice is a skew type. -/
def isSkewEntry {α : Type*} : Option (α × ChangeType) → Bool
  | some (_, .skew) => true
  | _ => false

namespace Choice

variable {J : Type*} [Fintype J] {T : J → Type*}

/-- The empty choice: nothing is selected. -/
def empty : Choice T := fun _ => none

/-- The set `X ⊆ J` of selected atoms. -/
def support (ω : Choice T) : Finset J := univ.filter fun b => (ω b).isSome

/-- The number of skew types of a choice. -/
def skewCount (ω : Choice T) : ℕ := (univ.filter fun b => isSkewEntry (ω b) = true).card

/-- A selection of (CP4)(c): a nonempty set of atoms with one record and one
type at each, the number of skew types being even. -/
def IsSelection (ω : Choice T) : Prop := ω ≠ empty ∧ Even (skewCount ω)

instance [DecidableEq J] [∀ b, DecidableEq (T b)] : DecidablePred (IsSelection (T := T)) :=
  fun ω => inferInstanceAs (Decidable (ω ≠ empty ∧ Even (skewCount ω)))

theorem support_nonempty_iff (ω : Choice T) : (support ω).Nonempty ↔ ω ≠ empty := by
  constructor
  · rintro ⟨b, hb⟩ h
    rw [h] at hb
    simp [support, empty] at hb
  · intro h
    by_contra hne
    apply h
    funext b
    have hb : b ∉ support ω := fun hb => hne ⟨b, hb⟩
    simp only [support, mem_filter, mem_univ, true_and, Option.not_isSome_iff_eq_none] at hb
    exact hb

theorem skewCount_empty : skewCount (empty : Choice T) = 0 := by
  simp [skewCount, empty, isSkewEntry]

end Choice

open Choice

/-! ### The factors of a choice -/

section Factors

variable {α Ω : Type*}

/-- The factor contributed by one atom: `λ_b` if nothing is selected there,
`ζ^ε_{b,t}` if the record `t` with type `ε` is selected. -/
def entryFactor (lamb : (Ω → ℝ) →ₗ[ℝ] ℝ) (ζb : α → ChangeType → (Ω → ℝ) →ₗ[ℝ] ℝ) :
    Option (α × ChangeType) → (Ω → ℝ) →ₗ[ℝ] ℝ
  | none => lamb
  | some (t, e) => ζb t e

theorem sum_entryFactor [Fintype α] (lamb : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (ζb : α → ChangeType → (Ω → ℝ) →ₗ[ℝ] ℝ) :
    ∑ o : Option (α × ChangeType), entryFactor lamb ζb o =
      lamb + ∑ t, (ζb t .sym + ζb t .skew) := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [entryFactor, sum_changeType]

/-- The sign of one entry under the reflection: `-1` for a skew type, `1` otherwise. -/
def entrySign (o : Option (α × ChangeType)) : ℝ := if isSkewEntry o then -1 else 1

theorem neg_one_smul_functional (L : (Ω → ℝ) →ₗ[ℝ] ℝ) : (-1 : ℝ) • L = -L :=
  LinearMap.ext fun f => by
    simp only [LinearMap.smul_apply, LinearMap.neg_apply, smul_eq_mul, neg_one_mul]

theorem one_smul_functional (L : (Ω → ℝ) →ₗ[ℝ] ℝ) : (1 : ℝ) • L = L :=
  LinearMap.ext fun f => by simp only [LinearMap.smul_apply, smul_eq_mul, one_mul]

/-- Every factor of a choice is an eigenmeasure of the reflection, with the sign
of its entry, when `λ_b`, `ζ^s_{b,t}` are symmetric and `ζ^a_{b,t}` skew. -/
theorem reflect_entryFactor {W Y : Type*} [Fintype W] [DecidableEq W] {c : ReflectionCut W}
    {lamb : ((W → Y) → ℝ) →ₗ[ℝ] ℝ} {ζb : α → ChangeType → ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (hlam : IsSymmetricAt c lamb) (hs : ∀ t, IsSymmetricAt c (ζb t .sym))
    (ha : ∀ t, IsSkewAt c (ζb t .skew)) (o : Option (α × ChangeType)) :
    reflect c (entryFactor lamb ζb o) = entrySign o • entryFactor lamb ζb o := by
  rcases o with _ | ⟨t, _ | _⟩
  · change reflect c lamb = (1 : ℝ) • lamb
    rw [one_smul_functional]
    exact hlam
  · change reflect c (ζb t .sym) = (1 : ℝ) • ζb t .sym
    rw [one_smul_functional]
    exact hs t
  · change reflect c (ζb t .skew) = (-1 : ℝ) • ζb t .skew
    rw [neg_one_smul_functional]
    exact ha t

end Factors

theorem prod_entrySign {J : Type*} [Fintype J] {T : J → Type*} (ω : Choice T) :
    ∏ b, entrySign (ω b) = (-1 : ℝ) ^ skewCount ω := by
  unfold entrySign skewCount
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-! ### The expansion -/

section Expansion

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]
  {T : J → Type*} [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)]

/-- The measure `ζ_ω ⊗ λ_{-X}` of a choice `ω` with support `X`. -/
noncomputable def choiceLaw (lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (ζ : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (ω : Choice T) :
    ((V → ∀ b, X b) → ℝ) →ₗ[ℝ] ℝ :=
  tensorLaw fun b => entryFactor (lam b) (ζ b) (ω b)

/-- The term `I_ω = Y_{ζ_ω ⊗ λ_{-X}}` of a choice. -/
noncomputable def term (lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (ζ : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, X b) → ℝ)
    (ω : Choice T) : ℝ :=
  diagonalIntegral (choiceLaw lam ζ ω) F

omit [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)] in
theorem choiceLaw_empty (lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (ζ : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ) :
    choiceLaw lam ζ (Choice.empty : Choice T) = tensorLaw lam := rfl

theorem diagonalIntegral_sub {Ω Y : Type*} [Fintype Ω] (L M : ((Ω → Y) → ℝ) →ₗ[ℝ] ℝ)
    (f : Y → ℝ) : diagonalIntegral (L - M) f = diagonalIntegral L f - diagonalIntegral M f :=
  rfl

theorem diagonalIntegral_sum {Ω Y ι : Type*} [Fintype Ω] (s : Finset ι)
    (L : ι → ((Ω → Y) → ℝ) →ₗ[ℝ] ℝ) (f : Y → ℝ) :
    diagonalIntegral (∑ i ∈ s, L i) f = ∑ i ∈ s, diagonalIntegral (L i) f := by
  unfold diagonalIntegral multilinearIntegral
  exact LinearMap.sum_apply s L _

omit [∀ b, DecidableEq (T b)] in
/-- The product of the decomposed laws is the sum over all choices. -/
theorem tensorLaw_eq_sum_choices {ν lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    {ζ : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hν : ∀ b, ν b = lam b + ∑ t, (ζ b t .sym + ζ b t .skew)) :
    tensorLaw ν = ∑ ω : Choice T, choiceLaw lam ζ ω := by
  have he : ν = fun b => ∑ o, entryFactor (lam b) (ζ b) o :=
    funext fun b => by rw [hν b, sum_entryFactor]
  rw [he, tensorLaw_sum]
  rfl

/-- **Record expansion, measure form** (`lem:record:record-expansion` (i),
without the parity restriction): with
`ν_b = λ_b + ∑_{t ∈ T_b} (ζ^s_{b,t} + ζ^a_{b,t})` at every atom,
`⊗_b ν_b - ⊗_b λ_b = ∑_{ω ≠ ∅} ζ_ω ⊗ λ_{-X}`. -/
theorem tensorLaw_sub_eq_sum {ν lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    {ζ : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hν : ∀ b, ν b = lam b + ∑ t, (ζ b t .sym + ζ b t .skew)) :
    tensorLaw ν - tensorLaw lam =
      ∑ ω ∈ univ.filter (fun ω : Choice T => ω ≠ Choice.empty), choiceLaw lam ζ ω := by
  rw [tensorLaw_eq_sum_choices hν, ← Finset.add_sum_erase univ _ (mem_univ Choice.empty),
    choiceLaw_empty, add_sub_cancel_left, Finset.filter_ne']

/-- **Record expansion, energy form**: `Y_ν - Y_λ = ∑_{ω ≠ ∅} I_ω`, the sum over
all nonempty choices (no parity restriction). -/
theorem energy_sub_eq_sum_choices {ν lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    {ζ : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hν : ∀ b, ν b = lam b + ∑ t, (ζ b t .sym + ζ b t .skew)) (F : (∀ b, X b) → ℝ) :
    diagonalIntegral (tensorLaw ν) F - diagonalIntegral (tensorLaw lam) F =
      ∑ ω ∈ univ.filter (fun ω : Choice T => ω ≠ Choice.empty), term lam ζ F ω := by
  rw [← diagonalIntegral_sub, tensorLaw_sub_eq_sum hν, diagonalIntegral_sum]
  rfl

omit [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)] in
/-- **Parity** (Section 9 after (CP4); proof of `lem:record:record-expansion` (i)):
if every `λ_b` and every `ζ^s_{b,t}` is symmetric at the cut `c` and every
`ζ^a_{b,t}` is skew at `c`, a choice with an odd number of skew types has
`I_ω = 0`: its measure is skew at `c` and the diagonal evaluation is
reflection invariant. -/
theorem term_eq_zero_of_odd (c : ReflectionCut V) {lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    {ζ : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hlam : ∀ b, IsSymmetricAt c (lam b)) (hs : ∀ b t, IsSymmetricAt c (ζ b t .sym))
    (ha : ∀ b t, IsSkewAt c (ζ b t .skew)) (F : (∀ b, X b) → ℝ) (ω : Choice T)
    (hodd : Odd (skewCount ω)) : term lam ζ F ω = 0 := by
  apply diagonalIntegral_tensorLaw_eq_zero c _ (fun b => entrySign (ω b))
  · intro b
    exact reflect_entryFactor (hlam b) (hs b) (ha b) (ω b)
  · rw [prod_entrySign, hodd.neg_one_pow]

/-- **Record expansion over selections** (`lem:record:record-expansion` (i),
first identity): under the symmetry hypotheses of `term_eq_zero_of_odd`,
`Y_ν - Y_λ = ∑_ω I_ω`, the sum over the selections of (CP4)(c) (nonempty, with
an even number of skew types). -/
theorem energy_sub_eq_sum_selections (c : ReflectionCut V)
    {ν lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    {ζ : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hν : ∀ b, ν b = lam b + ∑ t, (ζ b t .sym + ζ b t .skew))
    (hlam : ∀ b, IsSymmetricAt c (lam b)) (hs : ∀ b t, IsSymmetricAt c (ζ b t .sym))
    (ha : ∀ b t, IsSkewAt c (ζ b t .skew)) (F : (∀ b, X b) → ℝ) :
    diagonalIntegral (tensorLaw ν) F - diagonalIntegral (tensorLaw lam) F =
      ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), term lam ζ F ω := by
  rw [energy_sub_eq_sum_choices hν F,
    ← Finset.sum_filter_add_sum_filter_not _ (fun ω : Choice T => Even (skewCount ω))]
  have hodd : ∑ ω ∈ (univ.filter fun ω : Choice T => ω ≠ Choice.empty).filter
      (fun ω => ¬Even (skewCount ω)), term lam ζ F ω = 0 := by
    apply Finset.sum_eq_zero
    intro ω hω
    rw [mem_filter] at hω
    exact term_eq_zero_of_odd c hlam hs ha F ω (Nat.not_even_iff_odd.mp hω.2)
  rw [hodd, add_zero, Finset.filter_filter]
  rfl

/-- **Record expansion from record changes** ((CP4)(b)): if
`ν_b - λ_b = ∑_{t ∈ T_b} Δ_{b,t}` and `ζ^s_{b,t}`, `ζ^a_{b,t}` are the symmetric and
skew parts of `Δ_{b,t}` at `c`, and every `λ_b` is symmetric at `c` ((CP3)),
then `Y_ν - Y_λ = ∑_ω I_ω` over the selections. -/
theorem energy_sub_eq_sum_selections_of_changes (c : ReflectionCut V)
    {ν lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    {Δ : ∀ b, T b → ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hν : ∀ b, ν b = lam b + ∑ t, Δ b t) (hlam : ∀ b, IsSymmetricAt c (lam b))
    (F : (∀ b, X b) → ℝ) :
    diagonalIntegral (tensorLaw ν) F - diagonalIntegral (tensorLaw lam) F =
      ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω),
        term lam (fun b t e => match e with
          | .sym => symPart c (Δ b t)
          | .skew => skewPart c (Δ b t)) F ω := by
  apply energy_sub_eq_sum_selections c _ hlam
  · intro b t
    exact isSymmetricAt_symPart c (Δ b t)
  · intro b t
    exact isSkewAt_skewPart c (Δ b t)
  · intro b
    rw [hν b]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    exact (symPart_add_skewPart c (Δ b t)).symm

end Expansion

end Sarkozy.RecordExpansion
