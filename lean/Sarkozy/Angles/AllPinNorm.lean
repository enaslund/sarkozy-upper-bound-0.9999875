module

public import Sarkozy.Angles.AllPin
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# `lem:mid:allpin` with the paper's hypotheses

`lem:mid:allpin` (`paper/sections/13_cuts_correlations.tex`), first statement, for an abstract
family of subspaces: let `Ē` be a symmetric matrix with nonnegative entries, zero diagonal
and operator norm `‖Ē‖ < 1` (the `ℓ²` operator norm, `Matrix.Norms.L2Operator`, as in the
paper's notation section), and let `V[𝒴] ⊓ V[𝒴'] = V[𝒴 ∪ 𝒴']` with
`cos∠(V[{β}], V[{β'}]) ≤ Ē_{ββ'}`. Then
`cos∠(V[𝒫 ∖ {β'}], V[𝒫 ∖ {β}]) ≤ [(I - Ē)⁻¹]_{ββ'}` (`allpin`).

The three matrix facts used by the paper are proved here.
* `posDef_one_sub_of_norm_lt_one`: `I - Ē` is positive definite.
* `PosDefSpace`: a positive definite `M` is a Gram matrix, of the standard basis vectors of
  `P → ℝ` with the inner product `⟪x, y⟫ = (M y) ⬝ x` (Mathlib's `Matrix.toInnerProductSpace`).
* `neumann_mul`, `neumann_apply_nonneg`, `one_le_neumann_apply_self`: the Neumann series
  `Q = ∑ Ēᵏ` is a left inverse of `I - Ē`, with nonnegative entries and `Q_{ββ} ≥ 1`.
-/

@[expose] public section

open scoped InnerProductSpace Matrix.Norms.L2Operator
open Matrix

namespace Sarkozy.Angles

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- `P → ℝ` with the inner product `⟪x, y⟫ = (M *ᵥ y) ⬝ᵥ x` of a positive definite `M`. -/
def PosDefSpace (_M : Matrix P P ℝ) : Type _ := P → ℝ

section PosDefSpace

variable (M : Matrix P P ℝ) [hM : Fact M.PosDef]

noncomputable instance : NormedAddCommGroup (PosDefSpace M) := M.toNormedAddCommGroup hM.out

noncomputable instance : InnerProductSpace ℝ (PosDefSpace M) :=
  M.toInnerProductSpace hM.out.posSemidef

instance : FiniteDimensional ℝ (PosDefSpace M) := (inferInstance : FiniteDimensional ℝ (P → ℝ))

/-- The standard basis vector `e x` of `PosDefSpace M`. -/
def PosDefSpace.basisVec (x : P) : PosDefSpace M := (Pi.single x 1 : P → ℝ)

/-- `M` is the Gram matrix of the standard basis vectors. -/
theorem PosDefSpace.inner_basisVec (x y : P) :
    ⟪PosDefSpace.basisVec M x, PosDefSpace.basisVec M y⟫_ℝ = M x y := by
  change (M *ᵥ Pi.single y 1) ⬝ᵥ star (Pi.single x 1) = M x y
  simp [dotProduct_single]

theorem PosDefSpace.linearIndependent_basisVec :
    LinearIndependent ℝ (PosDefSpace.basisVec M) := by
  have h := (Pi.basisFun ℝ P).linearIndependent
  have e : ⇑(Pi.basisFun ℝ P) = fun x => (Pi.single x 1 : P → ℝ) := by
    ext x
    simp
  rw [e] at h
  exact h

end PosDefSpace

/-- Powers of a matrix with nonnegative entries have nonnegative entries. -/
theorem pow_apply_nonneg (E : Matrix P P ℝ) (h : ∀ x y, 0 ≤ E x y) (k : ℕ) (x y : P) :
    0 ≤ (E ^ k) x y := by
  induction k generalizing x y with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (h z y)

/-- The Neumann series is a left inverse of `I - Ē`. -/
theorem neumann_mul (E : Matrix P P ℝ) (hnorm : ‖E‖ < 1) : (∑' k, E ^ k) * (1 - E) = 1 :=
  geom_series_mul_neg E hnorm

theorem neumann_apply (E : Matrix P P ℝ) (hnorm : ‖E‖ < 1) (x y : P) :
    (∑' k, E ^ k) x y = ∑' k, (E ^ k) x y := by
  have hs : Summable (fun k => E ^ k) := summable_geometric_of_norm_lt_one hnorm
  exact (Pi.hasSum.mp (Pi.hasSum.mp hs.hasSum x) y).tsum_eq.symm

theorem summable_pow_apply (E : Matrix P P ℝ) (hnorm : ‖E‖ < 1) (x y : P) :
    Summable (fun k => (E ^ k) x y) := by
  have hs : Summable (fun k => E ^ k) := summable_geometric_of_norm_lt_one hnorm
  exact (Pi.hasSum.mp (Pi.hasSum.mp hs.hasSum x) y).summable

theorem neumann_apply_nonneg (E : Matrix P P ℝ) (h : ∀ x y, 0 ≤ E x y) (hnorm : ‖E‖ < 1)
    (x y : P) : 0 ≤ (∑' k, E ^ k) x y := by
  rw [neumann_apply E hnorm]
  exact tsum_nonneg fun k => pow_apply_nonneg E h k x y

theorem one_le_neumann_apply_self (E : Matrix P P ℝ) (h : ∀ x y, 0 ≤ E x y) (hnorm : ‖E‖ < 1)
    (x : P) : 1 ≤ (∑' k, E ^ k) x x := by
  rw [neumann_apply E hnorm]
  have h0 : (E ^ 0) x x = 1 := by simp
  calc (1 : ℝ) = (E ^ 0) x x := h0.symm
    _ ≤ ∑' k, (E ^ k) x x :=
      (summable_pow_apply E hnorm x x).le_tsum 0 fun k _ => pow_apply_nonneg E h k x x

/-- `x ⬝ᵥ (E *ᵥ x) ≤ ‖E‖ (x ⬝ᵥ x)` for the `ℓ²` operator norm. -/
theorem dotProduct_mulVec_le (E : Matrix P P ℝ) (x : P → ℝ) :
    x ⬝ᵥ (E *ᵥ x) ≤ ‖E‖ * (x ⬝ᵥ x) := by
  set X : EuclideanSpace ℝ P := WithLp.toLp 2 x with hX
  have hY := E.l2_opNorm_mulVec X
  have hXX : ‖X‖ ^ 2 = x ⬝ᵥ x := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
    simp [hX]
  have hinner : ⟪X, (EuclideanSpace.equiv P ℝ).symm (E *ᵥ X)⟫_ℝ = x ⬝ᵥ (E *ᵥ x) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [hX, dotProduct_comm]
  calc x ⬝ᵥ (E *ᵥ x) = ⟪X, (EuclideanSpace.equiv P ℝ).symm (E *ᵥ X)⟫_ℝ := hinner.symm
    _ ≤ ‖X‖ * ‖(EuclideanSpace.equiv P ℝ).symm (E *ᵥ X)‖ := real_inner_le_norm _ _
    _ ≤ ‖X‖ * (‖E‖ * ‖X‖) := by gcongr
    _ = ‖E‖ * (x ⬝ᵥ x) := by rw [← hXX]; ring

/-- `I - Ē` is positive definite when `Ē` is symmetric with `‖Ē‖ < 1`. -/
theorem posDef_one_sub_of_norm_lt_one (E : Matrix P P ℝ) (hE : E.IsSymm) (hnorm : ‖E‖ < 1) :
    (1 - E).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact (isSymm_one.sub hE).eq
  · have hpos : 0 < x ⬝ᵥ x := by
      set X : EuclideanSpace ℝ P := WithLp.toLp 2 x with hX
      have hXX : ‖X‖ ^ 2 = x ⬝ᵥ x := by
        rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
        simp [hX]
      have hX0 : X ≠ 0 := by
        intro h0
        apply hx
        have := congrArg WithLp.ofLp h0
        simpa [hX] using this
      rw [← hXX]
      exact pow_pos (norm_pos_iff.mpr hX0) 2
    have hle := dotProduct_mulVec_le E x
    rw [star_trivial, sub_mulVec, one_mulVec, dotProduct_sub]
    have : ‖E‖ * (x ⬝ᵥ x) < x ⬝ᵥ x := by nlinarith
    linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **`lem:mid:allpin`** (first statement), for an abstract family of subspaces with
`V[𝒴] ⊓ V[𝒴'] = V[𝒴 ∪ 𝒴']`: if `Ē` is symmetric with nonnegative entries, zero diagonal and
`‖Ē‖ < 1`, and `cos∠(V[{β}], V[{β'}]) ≤ Ē_{ββ'}` for distinct `β, β'`, then
`cos∠(V[𝒫 ∖ {β'}], V[𝒫 ∖ {β}]) ≤ [(I - Ē)⁻¹]_{ββ'}`. -/
theorem allpin (V : Finset P → Submodule ℝ E)
    (hV : ∀ 𝒴 𝒴' : Finset P, V 𝒴 ⊓ V 𝒴' = V (𝒴 ∪ 𝒴'))
    (Ebar : Matrix P P ℝ) (hsymm : Ebar.IsSymm) (hdiag : ∀ x, Ebar x x = 0)
    (hnn : ∀ x y, 0 ≤ Ebar x y) (hnorm : ‖Ebar‖ < 1)
    (hcos : ∀ β β', β ≠ β' → friedrichsCos (V {β}) (V {β'}) ≤ Ebar β β')
    {β β' : P} (hne : β ≠ β') :
    friedrichsCos (V (Finset.univ \ {β'})) (V (Finset.univ \ {β})) ≤ (1 - Ebar)⁻¹ β β' := by
  have hPD := posDef_one_sub_of_norm_lt_one Ebar hsymm hnorm
  have : Fact (1 - Ebar).PosDef := ⟨hPD⟩
  have hQ := neumann_mul Ebar hnorm
  have hinv : (1 - Ebar)⁻¹ = ∑' k, Ebar ^ k := Matrix.inv_eq_left_inv hQ
  have hQs : (1 - Ebar)⁻¹.IsSymm := (isSymm_one.sub hsymm).inv
  rw [hinv] at hQs ⊢
  exact allpin_matrix_le (F := PosDefSpace (1 - Ebar)) V hV
    (PosDefSpace.linearIndependent_basisVec (1 - Ebar)) Ebar
    (PosDefSpace.inner_basisVec (1 - Ebar)) hdiag hcos hQ hQs hne
    (neumann_apply_nonneg Ebar hnn hnorm β β') (one_le_neumann_apply_self Ebar hnn hnorm β)
    (one_le_neumann_apply_self Ebar hnn hnorm β')

end Sarkozy.Angles
