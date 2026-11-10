module

public import Sarkozy.Reflection.Transport
public import Sarkozy.Reflection.BracketMatrix
public import Sarkozy.RecordExpansion.Multilinear
public import Mathlib.Analysis.Real.Sqrt

/-!
# Folded energies (`lem:record:folded-energy`)

`lem:record:folded-energy` (`paper/sections/08_scale_comparison.tex`) reduces a signed
difference of records at one cut to the geometric mean of two nonnegative *folded*
energies. A signed law `K` on `V → X` is *sharp* at a cut, with constant `d`, relative to
half marginals `m₊, m₋` (`eq:record:sharp`) if
`|∫ φ(z₊) ψ(z₋) dK| ≤ d ‖φ‖_{L²(m₊)} ‖ψ‖_{L²(m₋)}` for all half-functions; in the
project's notation the pairing is the cut form `c.form K φ ψ`, and the half marginals are
weights on the half assignments `c.Half → X` (the minus half identified with the plus half
through the reflection, as everywhere in `Sarkozy.Reflection`).

* `sharp_iff_bracket` is the first step of the proof of (a): a sharp bound is the block-Gram
  bracket `(d D₊, K; Kᵀ, d D₋) ⪰ 0`, with `D±` the diagonal laws (`ReflectionCut.diagonalLaw`)
  of the half marginals. Zero masses and `d = 0` are allowed.
* `folded_energy_tensor` and `folded_energy` are (a) at fixed shared labels, for a product
  over atoms: on the atoms of `E` the laws are sharp, on the others reflection positive
  (`μ_𝒮` of the paper, `K j = Q j` positive). The energy of `K` is at most `∏_{j∈E} d_j`
  times the geometric mean of the two folded energies, which are nonnegative. With one
  block `E` this is (a); with several sharp blocks the constant is the product of their
  constants, which is (d′) (common cut); a probability coupling is sharp with constant one
  (`sharp_one_of_nonneg`), which is (d).
* `abs_sum_le_folded` adds the shared labels `s ∼ π` (and equally an external index
  `ω ∼ 𝐏`, part (c)): Cauchy–Schwarz in `L²(π)`.
* `sum_folds` and `prod_folds` (the latter in `Sarkozy.Reflection.Bracket`) are the copying
  identities of (e).

The folded energy `∫ (a ∘ φ₊) d(⊗ L)` with `L j = D₊,j` on `E` and `L j = Q j` off `E` is the
paper's `𝔈₊ = ∫ Λ_{μ_𝒮}((g_{φ₊(u)}(z_{φ₊(u)}, ·))_u) dm₊(z₊)`: under the diagonal law the
labels at `u` and at `φ₊(u)` agree, and the inputs at slot `u` are those of slot `φ₊(u)`.
Part (b) (the one-slot marginals of the folded laws) is not formalized here.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Comparison

open ReflectionCut

variable {V : Type*} [Fintype V] [DecidableEq V]

section Sharp

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The sharp bound `eq:record:sharp` of `lem:record:folded-energy` at the cut `c`. -/
def Sharp (c : ReflectionCut V) (K : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (mp mm : (c.Half → X) → ℝ) (d : ℝ) : Prop :=
  ∀ F G : (c.Half → X) → ℝ,
    |c.form K F G| ≤ d * Real.sqrt (∑ x, mp x * F x ^ 2) * Real.sqrt (∑ x, mm x * G x ^ 2)

omit [Fintype X] [DecidableEq X] in
theorem form_smul_law (c : ReflectionCut V) (a : ℝ) (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (F G : (c.Half → X) → ℝ) : c.form (a • L) F G = a * c.form L F G := rfl

omit [DecidableEq X] in
theorem form_diagonalLaw_self (c : ReflectionCut V) (m F : (c.Half → X) → ℝ) :
    c.form (c.diagonalLaw m) F F = ∑ x, m x * F x ^ 2 := by
  rw [c.form_diagonalLaw]
  exact Finset.sum_congr rfl fun x _ => by ring

omit [DecidableEq X] in
/-- **A sharp bound is a block-Gram bracket** (first step of the proof of (a)). -/
theorem sharp_iff_bracket (c : ReflectionCut V) (K : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    {mp mm : (c.Half → X) → ℝ} (hmp : ∀ x, 0 ≤ mp x) (hmm : ∀ x, 0 ≤ mm x)
    {d : ℝ} (hd : 0 ≤ d) :
    Sharp c K mp mm d ↔ c.Bracket (d • c.diagonalLaw mp) K (d • c.diagonalLaw mm) := by
  constructor
  · intro h
    refine ⟨(c.diagonalLaw_positive hmp).smul hd, (c.diagonalLaw_positive hmm).smul hd, ?_⟩
    intro F G
    rw [form_smul_law, form_smul_law, form_diagonalLaw_self, form_diagonalLaw_self]
    set A := ∑ x, mp x * F x ^ 2
    set B := ∑ x, mm x * G x ^ 2
    have hA : 0 ≤ A := Finset.sum_nonneg fun x _ => mul_nonneg (hmp x) (sq_nonneg _)
    have hB : 0 ≤ B := Finset.sum_nonneg fun x _ => mul_nonneg (hmm x) (sq_nonneg _)
    have hk := h F G
    have hk' : -(d * Real.sqrt A * Real.sqrt B) ≤ c.form K F G := (abs_le.mp hk).1
    have hsA := Real.sq_sqrt hA
    have hsB := Real.sq_sqrt hB
    have hsq : 0 ≤ d * (Real.sqrt A - Real.sqrt B) ^ 2 := mul_nonneg hd (sq_nonneg _)
    nlinarith [hsq, hsA, hsB, hk']
  · intro h F G
    have hb := h.abs_form_le F G
    rw [form_smul_law, form_smul_law, form_diagonalLaw_self, form_diagonalLaw_self,
      Real.sqrt_mul hd, Real.sqrt_mul hd] at hb
    have hdd : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd
    calc |c.form K F G| ≤ Real.sqrt d * Real.sqrt (∑ x, mp x * F x ^ 2) *
          (Real.sqrt d * Real.sqrt (∑ x, mm x * G x ^ 2)) := hb
      _ = (Real.sqrt d * Real.sqrt d) * Real.sqrt (∑ x, mp x * F x ^ 2) *
          Real.sqrt (∑ x, mm x * G x ^ 2) := by ring
      _ = d * Real.sqrt (∑ x, mp x * F x ^ 2) * Real.sqrt (∑ x, mm x * G x ^ 2) := by
          rw [hdd]

end Sharp

section Tensor

variable {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)]
  [∀ j, DecidableEq (X j)]

/-- **Folded energies for products of brackets.** If every atom carries a bracket
`(d_j L_j, K_j; K_jᵀ, d_j R_j) ⪰ 0` with positive `L_j, R_j`, then the energy of every input
assignment under `⊗ K` is at most `∏ d_j` times the geometric mean of its two folded
energies under `⊗ L` and `⊗ R`, and these are nonnegative. -/
theorem folded_energy_tensor (c : ReflectionCut V) (K L R : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (d : J → ℝ) (hd : ∀ j, 0 ≤ d j) (hL : ∀ j, c.Positive (L j)) (hR : ∀ j, c.Positive (R j))
    (hbr : ∀ j, c.Bracket (d j • L j) (K j) (d j • R j)) (a : V → (∀ j, X j) → ℝ) :
    0 ≤ multilinearIntegral (tensorLaw L) (a ∘ c.foldPlus) ∧
      0 ≤ multilinearIntegral (tensorLaw R) (a ∘ c.foldMinus) ∧
      |multilinearIntegral (tensorLaw K) a| ≤ (∏ j, d j) *
        Real.sqrt (multilinearIntegral (tensorLaw L) (a ∘ c.foldPlus)) *
        Real.sqrt (multilinearIntegral (tensorLaw R) (a ∘ c.foldMinus)) := by
  have hEp := (Positive.tensor hL).foldPlus_nonneg a
  have hEm := (Positive.tensor hR).foldMinus_nonneg a
  refine ⟨hEp, hEm, ?_⟩
  have hb := Bracket.tensor hbr
  rw [RecordExpansion.tensorLaw_smul d L, RecordExpansion.tensorLaw_smul d R] at hb
  have hf := hb.folding a
  set P := ∏ j, d j
  have hP : 0 ≤ P := Finset.prod_nonneg fun j _ => hd j
  have hsmul (M : ((V → ∀ j, X j) → ℝ) →ₗ[ℝ] ℝ) (b : V → (∀ j, X j) → ℝ) :
      multilinearIntegral (P • M) b = P * multilinearIntegral M b := rfl
  rw [hsmul, hsmul] at hf
  set Ep := multilinearIntegral (tensorLaw L) (a ∘ c.foldPlus)
  set Em := multilinearIntegral (tensorLaw R) (a ∘ c.foldMinus)
  have h2 : |multilinearIntegral (tensorLaw K) a| ^ 2 ≤ (P * Real.sqrt Ep * Real.sqrt Em) ^ 2 := by
    calc |multilinearIntegral (tensorLaw K) a| ^ 2 ≤ P * Ep * (P * Em) := hf
      _ = P ^ 2 * (Real.sqrt Ep) ^ 2 * (Real.sqrt Em) ^ 2 := by
          rw [Real.sq_sqrt hEp, Real.sq_sqrt hEm]; ring
      _ = (P * Real.sqrt Ep * Real.sqrt Em) ^ 2 := by ring
  have hr : 0 ≤ P * Real.sqrt Ep * Real.sqrt Em := by positivity
  exact (abs_le_of_sq_le_sq' h2 hr).2

/-- **`lem:record:folded-energy` (a), at fixed shared labels.** The atoms of `E` carry sharp
signed laws `K j` (constants `d j`, half marginals `mp j`, `mm j`); the remaining atoms carry
reflection positive laws (the law `μ_𝒮`). The folded laws replace each sharp factor by the
diagonal law of its half marginal. -/
theorem folded_energy (c : ReflectionCut V) (E : Finset J) (K : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (mp mm : ∀ j, (c.Half → X j) → ℝ) (d : J → ℝ) (hd : ∀ j ∈ E, 0 ≤ d j)
    (hmp : ∀ j ∈ E, ∀ x, 0 ≤ mp j x) (hmm : ∀ j ∈ E, ∀ x, 0 ≤ mm j x)
    (hsharp : ∀ j ∈ E, Sharp c (K j) (mp j) (mm j) (d j))
    (hpos : ∀ j ∉ E, c.Positive (K j)) (a : V → (∀ j, X j) → ℝ) :
    let Lp : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ := fun j => if j ∈ E then c.diagonalLaw (mp j) else K j
    let Lm : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ := fun j => if j ∈ E then c.diagonalLaw (mm j) else K j
    0 ≤ multilinearIntegral (tensorLaw Lp) (a ∘ c.foldPlus) ∧
      0 ≤ multilinearIntegral (tensorLaw Lm) (a ∘ c.foldMinus) ∧
      |multilinearIntegral (tensorLaw K) a| ≤ (∏ j ∈ E, d j) *
        Real.sqrt (multilinearIntegral (tensorLaw Lp) (a ∘ c.foldPlus)) *
        Real.sqrt (multilinearIntegral (tensorLaw Lm) (a ∘ c.foldMinus)) := by
  intro Lp Lm
  let d' : J → ℝ := fun j => if j ∈ E then d j else 1
  have hd' : ∀ j, 0 ≤ d' j := fun j => by
    by_cases hj : j ∈ E
    · simp only [d', hj, ↓reduceIte]; exact hd j hj
    · simp only [d', hj, ↓reduceIte]; norm_num
  have hLp : ∀ j, c.Positive (Lp j) := fun j => by
    by_cases hj : j ∈ E
    · simp only [Lp, hj, ↓reduceIte]; exact c.diagonalLaw_positive (hmp j hj)
    · simp only [Lp, hj, ↓reduceIte]; exact hpos j hj
  have hLm : ∀ j, c.Positive (Lm j) := fun j => by
    by_cases hj : j ∈ E
    · simp only [Lm, hj, ↓reduceIte]; exact c.diagonalLaw_positive (hmm j hj)
    · simp only [Lm, hj, ↓reduceIte]; exact hpos j hj
  have hbr : ∀ j, c.Bracket (d' j • Lp j) (K j) (d' j • Lm j) := fun j => by
    by_cases hj : j ∈ E
    · simp only [d', Lp, Lm, hj, ↓reduceIte]
      exact (sharp_iff_bracket c (K j) (hmp j hj) (hmm j hj) (hd j hj)).mp (hsharp j hj)
    · simp only [d', Lp, Lm, hj, ↓reduceIte, one_smul]
      exact (hpos j hj).bracket_self
  have hprod : ∏ j, d' j = ∏ j ∈ E, d j := by
    simp only [d']
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  have h := folded_energy_tensor c K Lp Lm d' hd' hLp hLm hbr a
  rwa [hprod] at h

/-- **The terms of `lem:sharp-first` by folding.** For a choice `σ` of differences (`σ b = some i`
selects `δ b i`, `none` keeps `ρ b`), with every `δ b i` sharp (constant `d b i`, half marginals
`mp b i`, `mm b i`) and every `ρ b` reflection positive, the term of `σ` is at most the product
of the selected sharp constants times the geometric mean of the two folded energies. This
reduces the per-term hypothesis `hterm` of `RecordExpansion.first_stage_lower_bound` to bounds
on the two folded energies (the structured-energy estimate). -/
theorem abs_term_le_folded (c : ReflectionCut V) {I : J → Type*}
    (ρ : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (δ : ∀ b, I b → ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (mp mm : ∀ b, I b → (c.Half → X b) → ℝ) (d : ∀ b, I b → ℝ)
    (hd : ∀ b i, 0 ≤ d b i) (hmp : ∀ b i x, 0 ≤ mp b i x) (hmm : ∀ b i x, 0 ≤ mm b i x)
    (hsharp : ∀ b i, Sharp c (δ b i) (mp b i) (mm b i) (d b i))
    (hρ : ∀ b, c.Positive (ρ b)) (σ : ∀ b, Option (I b)) (a : V → (∀ b, X b) → ℝ) :
    let Lp : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ := fun b => (σ b).elim (ρ b) fun i => c.diagonalLaw (mp b i)
    let Lm : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ := fun b => (σ b).elim (ρ b) fun i => c.diagonalLaw (mm b i)
    0 ≤ multilinearIntegral (tensorLaw Lp) (a ∘ c.foldPlus) ∧
      0 ≤ multilinearIntegral (tensorLaw Lm) (a ∘ c.foldMinus) ∧
      |multilinearIntegral (tensorLaw fun b => (σ b).elim (ρ b) (δ b)) a| ≤
        (∏ b, (σ b).elim 1 (d b)) *
          Real.sqrt (multilinearIntegral (tensorLaw Lp) (a ∘ c.foldPlus)) *
          Real.sqrt (multilinearIntegral (tensorLaw Lm) (a ∘ c.foldMinus)) := by
  intro Lp Lm
  apply folded_energy_tensor c _ Lp Lm (fun b => (σ b).elim 1 (d b))
  · intro b
    cases σ b with
    | none => norm_num
    | some i => exact hd b i
  · intro b
    simp only [Lp]
    cases σ b with
    | none => exact hρ b
    | some i => exact c.diagonalLaw_positive (hmp b i)
  · intro b
    simp only [Lm]
    cases σ b with
    | none => exact hρ b
    | some i => exact c.diagonalLaw_positive (hmm b i)
  · intro b
    simp only [Lp, Lm]
    cases σ b with
    | none => simpa only [Option.elim, one_smul] using (hρ b).bracket_self
    | some i => exact (sharp_iff_bracket c (δ b i) (hmp b i) (hmm b i) (hd b i)).mp (hsharp b i)

end Tensor

section Shared

/-- **Shared labels and external indices** (`lem:record:folded-energy` (a), last step, and
(c)): pointwise bounds `|T s| ≤ D √(E₊ s) √(E₋ s)` with nonnegative energies average, under
nonnegative weights `π`, to `|∑ π T| ≤ D √(∑ π E₊) √(∑ π E₋)`. -/
theorem abs_sum_le_folded {Ω : Type*} [Fintype Ω] (π T Ep Em : Ω → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hπ : ∀ s, 0 ≤ π s) (hEp : ∀ s, 0 ≤ Ep s) (hEm : ∀ s, 0 ≤ Em s)
    (hT : ∀ s, |T s| ≤ D * Real.sqrt (Ep s) * Real.sqrt (Em s)) :
    |∑ s, π s * T s| ≤ D * Real.sqrt (∑ s, π s * Ep s) * Real.sqrt (∑ s, π s * Em s) := by
  calc |∑ s, π s * T s| ≤ ∑ s, |π s * T s| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, π s * |T s| := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [abs_mul, abs_of_nonneg (hπ s)]
    _ ≤ ∑ s, π s * (D * Real.sqrt (Ep s) * Real.sqrt (Em s)) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hT s) (hπ s)
    _ = D * ∑ s, Real.sqrt (π s * Ep s) * Real.sqrt (π s * Em s) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Real.sqrt_mul (hπ s), Real.sqrt_mul (hπ s)]
        have : Real.sqrt (π s) * Real.sqrt (π s) = π s := Real.mul_self_sqrt (hπ s)
        calc π s * (D * Real.sqrt (Ep s) * Real.sqrt (Em s))
            = D * ((Real.sqrt (π s) * Real.sqrt (π s)) * Real.sqrt (Ep s) * Real.sqrt (Em s)) := by
              rw [this]; ring
          _ = D * (Real.sqrt (π s) * Real.sqrt (Ep s) * (Real.sqrt (π s) * Real.sqrt (Em s))) := by
              ring
    _ ≤ D * (Real.sqrt (∑ s, π s * Ep s) * Real.sqrt (∑ s, π s * Em s)) :=
        mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le _
          (fun s => mul_nonneg (hπ s) (hEp s)) (fun s => mul_nonneg (hπ s) (hEm s))) hD
    _ = D * Real.sqrt (∑ s, π s * Ep s) * Real.sqrt (∑ s, π s * Em s) := by ring

end Shared

section Copying

/-- The copying identity of `lem:record:folded-energy` (e), additive form:
`∑_u b(φ₊ u) + ∑_u b(φ₋ u) = 2 ∑_v b v`. -/
theorem sum_folds (c : ReflectionCut V) (b : V → ℝ) :
    ∑ v, b (c.foldPlus v) + ∑ v, b (c.foldMinus v) = 2 * ∑ v, b v := by
  have hsplit (f : V → ℝ) : ∑ v, f v = ∑ v : c.Half, f v.1 + ∑ v : c.Half, f (c.flip v.1) := by
    rw [← Fintype.sum_equiv c.halfSumEquiv (fun x => f (c.halfSumEquiv x)) f (fun _ => rfl),
      Fintype.sum_sum_type]
    rfl
  rw [hsplit (fun v => b (c.foldPlus v)), hsplit (fun v => b (c.foldMinus v)), hsplit b]
  simp only [foldPlus_half, foldPlus_flip_half, foldMinus_half, foldMinus_flip_half]
  ring

end Copying

section Coupling

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The plus-half marginal of a law: the mass of each plus-half assignment. -/
noncomputable def halfMarginalPlus (c : ReflectionCut V) (K : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (x : c.Half → X) : ℝ :=
  K (fun z => if (fun v : c.Half => z v.1) = x then 1 else 0)

/-- The minus-half marginal, read on the plus half through the reflection. -/
noncomputable def halfMarginalMinus (c : ReflectionCut V) (K : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (y : c.Half → X) : ℝ :=
  K (fun z => if (fun v : c.Half => z (c.flip v.1)) = y then 1 else 0)

/-- Cauchy–Schwarz for a positive linear functional on functions. -/
theorem positive_functional_cauchy_schwarz {Ω : Type*} (K : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hK : ∀ f : Ω → ℝ, (∀ z, 0 ≤ f z) → 0 ≤ K f) (f g : Ω → ℝ) :
    K (fun z => f z * g z) ^ 2 ≤ K (fun z => f z ^ 2) * K (fun z => g z ^ 2) := by
  have hq (t : ℝ) : 0 ≤ K (fun z => f z ^ 2) * (t * t) + (2 * K (fun z => f z * g z)) * t +
      K (fun z => g z ^ 2) := by
    have h := hK (fun z => (t * f z + g z) ^ 2) (fun z => sq_nonneg _)
    have he : (fun z => (t * f z + g z) ^ 2) = (t * t) • (fun z => f z ^ 2) +
        (2 * t) • (fun z => f z * g z) + (fun z => g z ^ 2) := by
      funext z; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [he, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    linarith
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith [hd]

theorem positive_functional_half_sq (c : ReflectionCut V) (K : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (F : (c.Half → X) → ℝ) (side : (V → X) → (c.Half → X)) :
    K (fun z => F (side z) ^ 2) = ∑ x, K (fun z => if side z = x then 1 else 0) * F x ^ 2 := by
  classical
  have he : (fun z => F (side z) ^ 2) =
      ∑ x, (F x ^ 2) • (fun z => if side z = x then (1 : ℝ) else 0) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  rw [he, map_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [map_smul, smul_eq_mul, mul_comm]

/-- **`lem:record:folded-energy` (d): a probability coupling is sharp with constant one**
relative to its own half marginals (Cauchy–Schwarz under the coupling). -/
theorem sharp_one_of_nonneg (c : ReflectionCut V) (K : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hK : ∀ f : (V → X) → ℝ, (∀ z, 0 ≤ f z) → 0 ≤ K f) :
    Sharp c K (halfMarginalPlus c K) (halfMarginalMinus c K) 1 := by
  intro F G
  have hcs := positive_functional_cauchy_schwarz K hK (fun z => F (fun v : c.Half => z v.1))
    (fun z => G (fun v : c.Half => z (c.flip v.1)))
  have h1 := positive_functional_half_sq c K F (fun z v => z v.1)
  have h2 := positive_functional_half_sq c K G (fun z v => z (c.flip v.1))
  rw [h1, h2] at hcs
  have hA : 0 ≤ ∑ x, halfMarginalPlus c K x * F x ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hK _ fun z => by split_ifs <;> norm_num)
      (sq_nonneg _)
  rw [one_mul, ← Real.sqrt_mul hA]
  exact Real.abs_le_sqrt hcs

end Coupling

end Sarkozy.Comparison
