module

public import Sarkozy.RecordExpansion.Bound

/-!
# The first comparison (Step 1) and the trivial mean credit

Two order arguments of Section 10 of the paper that use only positivity at one
cut and tensorization:

* `lem:record:first-stage`, Step 1: if `μ_b ⪰_ϑ 0` at every atom and
  `ρ_b ⪰_ϑ μ_b` (on the first-stage atoms; `ρ_b = μ_b` elsewhere), then
  `ρ = ⊗_b ρ_b ⪰_ϑ μ = ⊗_b μ_b`, and evaluation at the diagonal half-function
  gives `Y_ρ ≥ Y_μ` (`below_tensorLaw`, `energy_le_of_below`,
  `first_stage_step_one`). This is the last assertion of
  `lem:record:block-gram` (d) for cut matrices of measures.
* `lem:record:domination` (the remark "The trivial mean credit"): if
  `Ñ_b ± λ_b ⪰_ι 0` ((CP3)) and `M_b - Ñ_b ⪰_ι 0` (from (CP6) and (E3)), then
  `M_b ± λ_b ⪰_ι 0`, hence `⊗_b M_b ± ⊗_b λ_b ⪰_ι 0`
  (`lem:record:block-gram` (d)), and at the diagonal `e = Y_{⊗M} ≥ |Y_λ|`
  (`domination`, `mean_energy_ge_abs`). With the first comparison
  `Y_λ ≥ (1 - L_0 - z) Y` (whose Step 2 is `lem:sharp-first`, not formalized
  here) this is the trivial mean credit `m = 1 - L_0`
  (`mean_credit_of_first_stage`), and `theta_trivial_credit` is the
  bookkeeping identity of that remark.

`positive_of_diagonal_records` is (E3) of `lem:energy-toolkit` in the form
used by (CP3) and (CP6): a finite nonnegative combination of nonnegative
measures fixed samplewise by the reflection is positive at the cut. It
reuses `ReflectionCut.positive_of_samplewiseFixed`
(`Sarkozy/Reflection/CommonCut.lean`). Tensorization of brackets is
`ReflectionCut.Bracket.tensor` (`Sarkozy/Reflection/BracketMatrix.lean`), and
`ReflectionCut.bracket_of_add_sub_positive` (`Sarkozy/Reflection/Bracket.lean`)
is the first half of `lem:record:block-gram` (d).
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.RecordExpansion

/-! ### Positivity facts at one cut -/

section Cut

variable {W Y : Type*} [Fintype W] [DecidableEq W]

theorem positive_zero (c : ReflectionCut W) : c.Positive (0 : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :=
  ⟨fun _ _ => rfl, fun _ => le_rfl⟩

theorem below_refl (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) : c.Below L L := by
  unfold ReflectionCut.Below
  rw [sub_self]
  exact positive_zero c

/-- **The second half of `lem:record:block-gram` (d) for measures**: a bracket
`(L K; K L) ⪰_c 0` whose off-diagonal measure has a symmetric cut form gives
`L ± K ⪰_c 0`. -/
theorem add_sub_positive_of_bracket {c : ReflectionCut W} {L K : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (h : c.Bracket L K L) (hK : ∀ F G : (c.Half → Y) → ℝ, c.form K F G = c.form K G F) :
    c.Positive (L + K) ∧ c.Positive (L - K) := by
  have hL := h.left_positive
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro F G
    change c.form L F G + c.form K F G = c.form L G F + c.form K G F
    rw [hL.symmetric F G, hK F G]
  · intro F
    change 0 ≤ c.form L F F + c.form K F F
    have h1 := h.nonneg F F
    linarith
  · intro F G
    change c.form L F G - c.form K F G = c.form L G F - c.form K G F
    rw [hL.symmetric F G, hK F G]
  · intro F
    change 0 ≤ c.form L F F - c.form K F F
    have h1 := h.nonneg F ((-1 : ℝ) • F)
    rw [c.form_smul_right, c.form_smul_left, c.form_smul_right] at h1
    linarith

/-- A measure `K` with `L ± K ⪰_c 0` is symmetric at `c`. -/
theorem isSymmetricAt_of_add_sub_positive [Fintype Y] [DecidableEq Y] {c : ReflectionCut W}
    {L K : ((W → Y) → ℝ) →ₗ[ℝ] ℝ} (hp : c.Positive (L + K)) (hm : c.Positive (L - K)) :
    IsSymmetricAt c K := by
  have h1 : reflect c (L + K) = L + K := hp.reflection_invariant
  have h2 : reflect c (L - K) = L - K := hm.reflection_invariant
  rw [reflect_add] at h1
  rw [reflect_sub] at h2
  unfold IsSymmetricAt
  apply LinearMap.ext
  intro f
  have e1 := congrArg (fun M => M f) h1
  have e2 := congrArg (fun M => M f) h2
  simp only [LinearMap.add_apply, LinearMap.sub_apply] at e1 e2
  linarith

/-- A weight is *diagonal at* `c` if it is fixed samplewise by the reflection:
every configuration of positive weight satisfies `z ∘ c.flip = z`
(`def:cp:records`; "reserved diagonal" at the reserved cut). -/
def IsDiagonalAt (c : ReflectionCut W) (w : (W → Y) → ℝ) : Prop :=
  ∀ z, w z ≠ 0 → z ∘ c.flip = z

/-- **(E3) for combinations of diagonal records**: a finite nonnegative
combination `∑_i a_i κ_i` of nonnegative measures `κ_i` that are diagonal at `c`
is positive at `c`. -/
theorem positive_of_diagonal_records [Fintype Y] {I : Type*} (c : ReflectionCut W)
    (s : Finset I) (a : I → ℝ) (w : I → (W → Y) → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hw : ∀ i ∈ s, ∀ z, 0 ≤ w i z) (hdiag : ∀ i ∈ s, IsDiagonalAt c (w i)) :
    c.Positive (∑ i ∈ s, a i • signedIntegral (w i)) := by
  apply ReflectionCut.Positive.sum
  intro i hi
  apply ReflectionCut.Positive.smul _ (ha i hi)
  have hfix : c.SamplewiseFixed (w i) (fun z : W → Y => z) := by
    intro z hz v
    exact congrFun (hdiag i hi z hz) v
  exact c.positive_of_samplewiseFixed (hw i hi) hfix

end Cut

/-! ### Tensorization of the cut order -/

section Tensor

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- **Tensorization of the cut order** (`lem:record:block-gram` (d), last
assertion): `0 ⪯_c μ_b ⪯_c ρ_b` at every atom gives `⊗_b μ_b ⪯_c ⊗_b ρ_b`. -/
theorem below_tensorLaw (c : ReflectionCut V) (μ ρ : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (hμ : ∀ b, c.Positive (μ b)) (hρ : ∀ b, c.Below (μ b) (ρ b)) :
    c.Below (tensorLaw μ) (tensorLaw ρ) := by
  let L : ∀ b, Bool → ((V → X b) → ℝ) →ₗ[ℝ] ℝ := fun b i => if i then ρ b - μ b else μ b
  have hsum : (fun b => ∑ i, L b i) = ρ := by
    funext b
    simp only [L, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, sub_add_cancel]
  have hρ' : tensorLaw ρ = ∑ f : J → Bool, tensorLaw (fun b => L b (f b)) := by
    rw [← tensorLaw_sum, hsum]
  have hμ' : tensorLaw μ = tensorLaw (fun b => L b ((fun _ => false) b)) := by
    congr 1
  unfold ReflectionCut.Below
  rw [hρ', ← Finset.add_sum_erase _ _ (mem_univ (fun _ => false)), hμ', add_sub_cancel_left]
  apply ReflectionCut.Positive.sum
  intro f _
  apply ReflectionCut.Positive.tensor
  intro b
  cases f b
  · exact hμ b
  · exact hρ b

/-- Evaluation of the tensorized order at the diagonal: `Y_μ ≤ Y_ρ`. -/
theorem energy_le_of_below (c : ReflectionCut V) (μ ρ : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (hμ : ∀ b, c.Positive (μ b)) (hρ : ∀ b, c.Below (μ b) (ρ b)) (F : (∀ b, X b) → ℝ) :
    diagonalIntegral (tensorLaw μ) F ≤ diagonalIntegral (tensorLaw ρ) F :=
  (below_tensorLaw c μ ρ hμ hρ).diagonal_le F

/-- **`lem:record:first-stage`, Step 1: `Y_ρ ≥ Y`.** Let `ϑ` be a cut, `μ_b ⪰_ϑ 0`
at every atom ((R2)), `fs` the first-stage atoms, `ρ_b ⪰_ϑ μ_b` for `b ∈ fs`
((CP2)(a)) and `ρ_b = μ_b` otherwise. Then `Y_ρ ≥ Y_μ` at every common input
`F`. -/
theorem first_stage_step_one (ϑ : ReflectionCut V) (fs : Finset J)
    (μ ρ : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (hμ : ∀ b, ϑ.Positive (μ b))
    (hρ : ∀ b ∈ fs, ϑ.Below (μ b) (ρ b)) (hoff : ∀ b ∉ fs, ρ b = μ b)
    (F : (∀ b, X b) → ℝ) :
    diagonalIntegral (tensorLaw μ) F ≤ diagonalIntegral (tensorLaw ρ) F := by
  apply energy_le_of_below ϑ μ ρ hμ
  intro b
  by_cases hb : b ∈ fs
  · exact hρ b hb
  · rw [hoff b hb]
    exact below_refl ϑ (μ b)

/-- **`±` tensorization** (`lem:record:block-gram` (d)): `A_b ± B_b ⪰_c 0` at every
atom gives the bracket `(⊗A  ⊗B; ⊗B  ⊗A) ⪰_c 0`. -/
theorem bracket_tensorLaw_of_add_sub {c : ReflectionCut V}
    {A Bm : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hp : ∀ b, c.Positive (A b + Bm b)) (hm : ∀ b, c.Positive (A b - Bm b)) :
    c.Bracket (tensorLaw A) (tensorLaw Bm) (tensorLaw A) :=
  ReflectionCut.Bracket.tensor fun b => ReflectionCut.bracket_of_add_sub_positive (hp b) (hm b)

/-- **`±` tensorization, order form** (`lem:record:block-gram` (d)): `A_b ± B_b ⪰_c 0`
at every atom gives `⊗_b A_b ± ⊗_b B_b ⪰_c 0`. -/
theorem add_sub_positive_tensorLaw {c : ReflectionCut V}
    {A Bm : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hp : ∀ b, c.Positive (A b + Bm b)) (hm : ∀ b, c.Positive (A b - Bm b)) :
    c.Positive (tensorLaw A + tensorLaw Bm) ∧ c.Positive (tensorLaw A - tensorLaw Bm) := by
  apply add_sub_positive_of_bracket (bracket_tensorLaw_of_add_sub hp hm)
  have hsym : IsSymmetricAt c (tensorLaw Bm) :=
    isSymmetricAt_tensorLaw c Bm fun b => isSymmetricAt_of_add_sub_positive (hp b) (hm b)
  exact hsym.form_comm

/-- **`lem:record:domination`, order part.** If `Ñ_b ± λ_b ⪰_c 0` ((CP3)) and
`Ñ_b ⪯_c M_b` (from (CP6) and (E3)) at every atom, then
`M_b ± λ_b = (Ñ_b ± λ_b) + (M_b - Ñ_b) ⪰_c 0` and `⊗_b M_b ± ⊗_b λ_b ⪰_c 0`. -/
theorem domination {c : ReflectionCut V} {N M lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hNp : ∀ b, c.Positive (N b + lam b)) (hNm : ∀ b, c.Positive (N b - lam b))
    (hMN : ∀ b, c.Below (N b) (M b)) :
    c.Positive (tensorLaw M + tensorLaw lam) ∧ c.Positive (tensorLaw M - tensorLaw lam) := by
  apply add_sub_positive_tensorLaw
  · intro b
    have h := (hNp b).add (hMN b)
    have he : N b + lam b + (M b - N b) = M b + lam b := by abel
    rwa [he] at h
  · intro b
    have h := (hNm b).add (hMN b)
    have he : N b - lam b + (M b - N b) = M b - lam b := by abel
    rwa [he] at h

/-- **`lem:record:domination`, energy part:** the mean energy
`e = Q_{⊗M}(X̄, X̄) = Y_{⊗M}` dominates `|Y_λ|`. -/
theorem mean_energy_ge_abs {c : ReflectionCut V} {N M lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hNp : ∀ b, c.Positive (N b + lam b)) (hNm : ∀ b, c.Positive (N b - lam b))
    (hMN : ∀ b, c.Below (N b) (M b)) (F : (∀ b, X b) → ℝ) :
    |diagonalIntegral (tensorLaw lam) F| ≤ diagonalIntegral (tensorLaw M) F := by
  obtain ⟨hp, hm⟩ := domination hNp hNm hMN
  have h1 := hp.diagonal_nonneg F
  have h2 := hm.diagonal_nonneg F
  change 0 ≤ diagonalIntegral (tensorLaw M) F + diagonalIntegral (tensorLaw lam) F at h1
  change 0 ≤ diagonalIntegral (tensorLaw M) F - diagonalIntegral (tensorLaw lam) F at h2
  rw [abs_le]
  constructor <;> linarith

/-- **The trivial mean credit** (`lem:record:domination`): with the envelopes
`M_L`, `M_R` of the two sides, both satisfying the hypotheses of `domination`,
and a first comparison `Y_λ ≥ (1 - L_0 - z) Y`, the mean energies satisfy
`½(e_L + e_R) ≥ (1 - L_0 - z) Y`; that is, (CP7) holds with `m = 1 - L_0`. -/
theorem mean_credit_of_first_stage {c : ReflectionCut V}
    {N ML MR lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hNp : ∀ b, c.Positive (N b + lam b)) (hNm : ∀ b, c.Positive (N b - lam b))
    (hL : ∀ b, c.Below (N b) (ML b)) (hR : ∀ b, c.Below (N b) (MR b))
    (F : (∀ b, X b) → ℝ) {L0 z Y : ℝ}
    (hfirst : (1 - L0 - z) * Y ≤ diagonalIntegral (tensorLaw lam) F) :
    (1 - L0 - z) * Y ≤
      (diagonalIntegral (tensorLaw ML) F + diagonalIntegral (tensorLaw MR) F) / 2 := by
  have h1 := mean_energy_ge_abs hNp hNm hL F
  have h2 := mean_energy_ge_abs hNp hNm hR F
  have h3 := le_abs_self (diagonalIntegral (tensorLaw lam) F)
  linarith

end Tensor

/-- **The bookkeeping identity of `lem:record:domination`**: with the trivial
credit `m = 1 - L_0`,
`(1 - 2^{-k})(L_0 + ℰ) + J + W + (1 - m)/2^k = L_0 + (1 - 2^{-k}) ℰ + J + W`. -/
theorem theta_trivial_credit (k : ℕ) (L0 E Jm W : ℝ) :
    (1 - 1 / 2 ^ k) * (L0 + E) + Jm + W + (1 - (1 - L0)) / 2 ^ k =
      L0 + (1 - 1 / 2 ^ k) * E + Jm + W := by
  ring

end Sarkozy.RecordExpansion
