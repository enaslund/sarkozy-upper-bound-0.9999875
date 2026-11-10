module

public import Sarkozy.MeanCredit.Classes
public import Sarkozy.EnvelopesPaper.Mean

@[expose] public section

/-!
# The selection-level mean from a positive expansion with each term spent at most once

`paper/sections/24_matching_mean.tex`, `prop:record:mean-credit` (Step 2: the positive expansion,
the one-block credits); `paper/sections/24a_joint_mean.tex`, `prop:joint-middle-mean`
("Partition the retained terms ... The four families are disjoint ... Each has support on at
least two blocks, so none consumes a one-block mean credit"; "Average the pair selection over
the `C(n,2)` pairs"; "The multiaffine inequalities allocate a term among its eligible positions;
they never spend it separately in full on every position").

The mean credit of the joint allocation is paid by the positive terms of the mean expansion. The
accounting rule of the paper is that every positive term is spent at most once in total: by the
one-block credit, or in fractions `a(ω, τ)` among the labelled selections `ω` that it serves.

* **`sum_le_of_allocation`**: terms `M_τ ≥ 0`, a one-block set `T₁`, fractions `a(ω, τ) ≥ 0` with
  `∑_ω a(ω, τ) + [τ ∈ T₁] ≤ 1`, and `v_ω ≤ ∑_τ a(ω, τ) M_τ` give `∑_{T₁} M + ∑_ω v_ω ≤ ∑_τ M_τ`.
* **`energyMean_eq_sum_tags`**, **`energyMean_ML_eq_sum`**, **`meanTermL_nonneg`**: at the formal
  objects, the mean energy `e_L = Q_{⊗ M_L}(X̄, X̄)` is the sum over tags
  `τ_b ∈ {Ñ_b} ∪ {c_i κ_i}` of the energies of the tensor products, each `≥ 0` (positive records and
  `Ñ ⪰ 0`).
* **`selMean_of_allocation`**: `SelMean` (the input of `MD.mean`, #22) from a positive expansion of
  the averaged mean energy, the one-block credit on `T₁`, and an allocation as above with
  `μ_ω Z_ω ≤ ∑_τ a(ω, τ) M_τ`. Family (i) is the allocation `a = 1/C(n,2)` on the pairs of an
  `n`-tag term.

The positive expansion that the paper uses is finer than the formal tags (it splits `Ñ` into the
reference and its positive records after paying `R_err e^{T_K + T_QE}`), so it stays an input here.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MeanCredit

open Sarkozy.ClassInputsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame
open Sarkozy.Comparison (remainder energyMean barHalf)
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Param (Params)
open Sarkozy.PartVLaws (paperAtomMap)
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.GramBracketPaper

/-! ## Each positive term spent at most once -/

/-- **The allocation of positive terms** (`prop:joint-middle-mean`): terms `M_τ ≥ 0`, a one-block
set `T₁ ⊆ 𝒯`, fractions `a(ω, τ)` whose total on every term, together with its one-block use,
is at most `1`, and values `v_ω ≤ ∑_τ a(ω, τ) M_τ`. Then `∑_{T₁} M + ∑_ω v_ω ≤ ∑_{𝒯} M`. -/
theorem sum_le_of_allocation {T Ω : Type*} [DecidableEq T] (𝒯 T₁ : Finset T) (hT₁ : T₁ ⊆ 𝒯)
    (S : Finset Ω) (M : T → ℝ) (hM : ∀ τ ∈ 𝒯, 0 ≤ M τ) (a : Ω → T → ℝ)
    (hcol : ∀ τ ∈ 𝒯, ∑ ω ∈ S, a ω τ + (if τ ∈ T₁ then 1 else 0) ≤ 1)
    (v : Ω → ℝ) (hv : ∀ ω ∈ S, v ω ≤ ∑ τ ∈ 𝒯, a ω τ * M τ) :
    ∑ τ ∈ T₁, M τ + ∑ ω ∈ S, v ω ≤ ∑ τ ∈ 𝒯, M τ := by
  have h1 : ∑ ω ∈ S, v ω ≤ ∑ τ ∈ 𝒯, (∑ ω ∈ S, a ω τ) * M τ := by
    calc ∑ ω ∈ S, v ω ≤ ∑ ω ∈ S, ∑ τ ∈ 𝒯, a ω τ * M τ := sum_le_sum hv
      _ = ∑ τ ∈ 𝒯, ∑ ω ∈ S, a ω τ * M τ := sum_comm
      _ = ∑ τ ∈ 𝒯, (∑ ω ∈ S, a ω τ) * M τ := sum_congr rfl fun τ _ => (sum_mul _ _ _).symm
  have h2 : ∑ τ ∈ T₁, M τ = ∑ τ ∈ 𝒯, (if τ ∈ T₁ then 1 else 0) * M τ := by
    rw [← sum_subset hT₁ (f := fun τ => (if τ ∈ T₁ then (1 : ℝ) else 0) * M τ)
      fun τ _ hτ => by simp [hτ]]
    exact sum_congr rfl fun τ hτ => by simp [hτ]
  have h3 : ∑ τ ∈ 𝒯, (∑ ω ∈ S, a ω τ) * M τ + ∑ τ ∈ 𝒯, (if τ ∈ T₁ then 1 else 0) * M τ ≤
      ∑ τ ∈ 𝒯, M τ := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun τ hτ => ?_
    have := mul_le_mul_of_nonneg_right (hcol τ hτ) (hM τ hτ)
    linarith
  linarith

/-! ## The tag expansion of the mean energy at the formal objects -/

section Tags

variable {Atom : ℕ → Type} [∀ L, Fintype (Atom L)] [∀ L, DecidableEq (Atom L)]
  {Xb : ∀ L, Atom L → Type} [∀ L b, Fintype (Xb L b)] [∀ L b, DecidableEq (Xb L b)]

/-- **The positive expansion of a mean energy** (`prop:record:mean-credit`, Step 2): if
`M_b = ∑_i t_{b,i}` at every atom, then `Q_{⊗M}(X̄, X̄) = ∑_τ Q_{⊗_b t_{b,τ_b}}(X̄, X̄)`. -/
theorem energyMean_eq_sum_tags (F : ∀ L, Finset ℤ → (∀ b, Xb L b) → ℝ)
    (M : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ) {I : ∀ L, Atom L → Type}
    [∀ L b, Fintype (I L b)] (t : ∀ L b, I L b → ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
    (hM : ∀ L b, M L b = ∑ i, t L b i) (L : ℕ) (A : Finset ℤ) :
    energyMean F M L A = ∑ τ : (∀ b, I L b),
      reservedCut.form (tensorLaw fun b => t L b (τ b)) (barHalf (F L A)) (barHalf (F L A)) := by
  unfold energyMean
  have e : M L = fun b => ∑ i, t L b i := funext (hM L)
  rw [e, tensorLaw_sum]
  unfold ReflectionCut.form
  exact LinearMap.sum_apply _ _ _

/-- A tensor product of laws positive at the reserved cut has nonnegative energy. -/
theorem form_tensor_nonneg {L : ℕ} (F : (reservedCut.Half → (∀ b, Xb L b)) → ℝ)
    (t : ∀ b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ) (ht : ∀ b, reservedCut.Positive (t b)) :
    0 ≤ reservedCut.form (tensorLaw t) F F :=
  (ReflectionCut.Positive.tensor ht).nonneg F

end Tags

section Formal

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- The tag laws of the left envelope `M_L = Ñ + ∑_i c_i κ_i`: `Ñ_b` (no tag) or `c_i κ_i`. -/
noncomputable def tagL (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) : Option (D.ME.IL L b) → AtomMeasure m₀ blk p L b :=
  fun o => o.elim (D.GB.N L b) fun i => D.ME.cL L b i • D.ME.κL L b i

/-- The energy of one tag of the left envelope. -/
noncomputable def meanTermL (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (A : Finset ℤ) (τ : ∀ b, Option (D.ME.IL L b)) : ℝ :=
  reservedCut.form (tensorLaw fun b => tagL D L b (τ b)) (barHalf (blockLift m₀ blk p L A))
    (barHalf (blockLift m₀ blk p L A))

/-- **The tag expansion of the left mean energy** (`prop:record:mean-credit`, Step 2, at the formal
envelopes): `e_L = ∑_τ Q_{⊗_b τ_b}(X̄, X̄)` over the tags `τ_b ∈ {Ñ_b} ∪ {c_i κ_i}`. -/
theorem energyMean_ML_eq_sum (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (A : Finset ℤ) :
    energyMean (blockLift m₀ blk p) D.ME.ML L A =
      ∑ τ : (∀ b, Option (D.ME.IL L b)), meanTermL D L A τ := by
  refine energyMean_eq_sum_tags (blockLift m₀ blk p) D.ME.ML (tagL D) (fun L b => ?_) L A
  rw [Fintype.sum_option]
  rfl

/-- **Every tag term of the left mean energy is nonnegative** (`Ñ ⪰ 0` from the bracket of (CP3),
the added records positive reserved diagonals with `c_i ≥ 0`). -/
theorem meanTermL_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (A : Finset ℤ) (τ : ∀ b, Option (D.ME.IL L b)) : 0 ≤ meanTermL D L A τ := by
  refine form_tensor_nonneg _ _ fun b => ?_
  rcases τ b with _ | i
  · exact (D.GB.bracket L b).left_positive
  · exact (EnvelopesPaper.positive_of_nonneg_diagonal (D.ME.κL_pos L b i).1
      (D.ME.κL_diag L b i)).smul (D.ME.cL_nonneg L b i)

/-- The tag laws of the right envelope `M_R = Ñ + ∑_i c_i κ_i`. -/
noncomputable def tagR (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) : Option (D.ME.IR L b) → AtomMeasure m₀ blk p L b :=
  fun o => o.elim (D.GB.N L b) fun i => D.ME.cR L b i • D.ME.κR L b i

/-- The energy of one tag of the right envelope. -/
noncomputable def meanTermR (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (A : Finset ℤ) (τ : ∀ b, Option (D.ME.IR L b)) : ℝ :=
  reservedCut.form (tensorLaw fun b => tagR D L b (τ b)) (barHalf (blockLift m₀ blk p L A))
    (barHalf (blockLift m₀ blk p L A))

theorem energyMean_MR_eq_sum (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (A : Finset ℤ) :
    energyMean (blockLift m₀ blk p) D.ME.MR L A =
      ∑ τ : (∀ b, Option (D.ME.IR L b)), meanTermR D L A τ := by
  refine energyMean_eq_sum_tags (blockLift m₀ blk p) D.ME.MR (tagR D) (fun L b => ?_) L A
  rw [Fintype.sum_option]
  rfl

theorem meanTermR_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (A : Finset ℤ) (τ : ∀ b, Option (D.ME.IR L b)) : 0 ≤ meanTermR D L A τ := by
  refine form_tensor_nonneg _ _ fun b => ?_
  rcases τ b with _ | i
  · exact (D.GB.bracket L b).left_positive
  · exact (EnvelopesPaper.positive_of_nonneg_diagonal (D.ME.κR_pos L b i).1
      (D.ME.κR_diag L b i)).smul (D.ME.cR_nonneg L b i)

/-- **The formal tags give an exact positive expansion of the averaged mean**:
`½(e_L + e_R) = ∑_{τ ∈ tags_L ⊕ tags_R} M_τ` with `M_τ = ½ Q_{⊗τ}(X̄, X̄) ≥ 0`. So the positive
expansion input of `selMean_of_allocation` is satisfiable with `c₁ = 0` (the paper's expansion is a
refinement of it, after paying `R_err e^{T_K+T_QE}`). -/
theorem avgMean_eq_sum_tags (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (A : Finset ℤ) :
    (energyMean (blockLift m₀ blk p) D.ME.ML L A + energyMean (blockLift m₀ blk p) D.ME.MR L A) /
        2 =
      ∑ τ : (∀ b, Option (D.ME.IL L b)) ⊕ (∀ b, Option (D.ME.IR L b)),
        Sum.elim (fun τ => meanTermL D L A τ / 2) (fun τ => meanTermR D L A τ / 2) τ := by
  rw [Fintype.sum_sum_type, energyMean_ML_eq_sum, energyMean_MR_eq_sum, add_div, sum_div,
    sum_div]
  rfl

end Formal

/-! ## The selection-level mean from an allocation -/

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-- **`SelMean` (the input of `MD.mean`, #22) from a positive expansion with each term spent at most
once** (`prop:record:mean-credit` Step 2, `prop:joint-middle-mean`). At every counterexample:
terms `𝒯_L` with energies `M ≥ 0` whose total is at most the averaged mean energy plus a remainder
(the positive expansion, after paying the bracket error); the one-block credit
`(m₁ − ε₂) Y − rem ≤ ∑_{T₁} M`; fractions `a(ω, τ)` with `∑_ω a(ω, τ) + [τ ∈ T₁] ≤ 1`; and the
labelled selections' credits `μ_ω Z_ω ≤ ∑_τ a(ω, τ) M_τ`. *Inputs* (analytic): these four. -/
theorem selMean_of_allocation (D : CD blockOf) (cd : ClassData D.CL)
    (μ : ∀ L, Choice (D.CL.T L) → ℝ) (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    (T : ℕ → Type) [∀ L, DecidableEq (T L)] (𝒯 T₁ : ∀ L, Finset (T L))
    (M : ∀ L, Finset ℤ → T L → ℝ) (al : ∀ L, Choice (D.CL.T L) → T L → ℝ)
    (ε₂ : ℕ → ℝ) (hε : Tendsto ε₂ atTop (𝓝 0)) (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (H : Param.AtCounterexamples (Params.ofDecay targetDecay) D.Y fun L A =>
      T₁ L ⊆ 𝒯 L ∧ (∀ τ ∈ 𝒯 L, 0 ≤ M L A τ) ∧
      ∑ τ ∈ 𝒯 L, M L A τ - remainder c₁ L A ≤
        (energyMean (blockLift paperM0 (paperAtomMap blockOf) paperTail) D.ME.ML L A +
          energyMean (blockLift paperM0 (paperAtomMap blockOf) paperTail) D.ME.MR L A) / 2 ∧
      (targetLedger.m₁ - ε₂ L) * D.Y L A - remainder c₂ L A ≤ ∑ τ ∈ T₁ L, M L A τ ∧
      (∀ τ ∈ 𝒯 L, ∑ ω ∈ cd.sel L, al L ω τ + (if τ ∈ T₁ L then 1 else 0) ≤ 1) ∧
      (∀ ω ∈ cd.sel L, μ L ω * Zs L A ω ≤ ∑ τ ∈ 𝒯 L, al L ω τ * M L A τ)) :
    SelMean D cd μ Zs := by
  refine ⟨ε₂, hε, c₁ + c₂, add_nonneg hc₁ hc₂, ?_⟩
  filter_upwards [H] with L hL
  intro C hC hind A hA hcount
  obtain ⟨hT, hM0, hexp, hone, hcol, hv⟩ := hL C hC hind A hA hcount
  have h := sum_le_of_allocation (𝒯 L) (T₁ L) hT (cd.sel L) (M L A) hM0 (al L) hcol
    (fun ω => μ L ω * Zs L A ω) hv
  rw [JointClosing.remainder_add]
  linarith

end Sarkozy.MeanCredit
