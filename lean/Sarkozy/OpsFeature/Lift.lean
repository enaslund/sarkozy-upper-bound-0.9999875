module

public import Sarkozy.EnvelopeSteps.Constructor
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section

/-!
# The positive enlargement of the lifted envelopes (`lem:oct24:mask-schur`(a), move 4)

`paper/sections/23_envelopes.tex`, `lem:oct24:mask-schur`(a) and its proof, last paragraph
("Summing over all choices of one sector `S_𝔅` at every block … Replacing a factor of a tensor
product of positive operators by a larger positive operator increases it, so these replacements,
made one coordinate at a time, give `0 ⪯ ∑ Ξ (D ⊗ I) Ξ^* ⪯ Lift(D)`").

**The lift map.** For each block `b` let `L b` be its label alphabet and `O b` its objects, and let
`C b` be a *unit table*: a real matrix on `L b × O b`, whose `(a, b)` block `C b ((a, ·), (a', ·))`
is the kernel of the unit lift `e_{aa'} ↦ U_b(a, a')`. The lift of a matrix `D` on the label words
`v ∈ ∀ b, L b` is `liftMap C D (x, y) = ∑_{v,w} D_{vw} ∏_b C b ((v_b, x_b), (w_b, y_b))` (the kernel
of `Lift(D)` in OPS-S's `kern_lift_expand` form). A unit table is the Choi matrix of the unit lift.

* **`liftMap_posSemidef`**: if every `C b` and `D` are positive semidefinite, so is the lift (the
  tensor product of completely positive maps is completely positive). The proof factors
  `C b = R_b R_bᵀ` (`exists_mul_transpose_of_posSemidef`, the spectral theorem) and writes the
  quadratic form of the lift as the trace of `Gᵀ D G`.
* **`liftMap_mono`** (move 4 for **every** degree class): if `0 ⪯ C b ⪯ C' b` at every block and
  `D ⪰ 0`, then `liftMap C D ⪯ liftMap C' D`. The proof expands `∏_b (C b + E b)` over the subsets
  of blocks (`Finset.prod_add`), every term being a lift of positive tables.
* **`liftMap_mask`**, **`posSemidef_mask`**: for `D` in the block algebra `𝒜` (block diagonal at
  every factor for a partition of the labels, e.g. `{0,1,2}, {3}, {4}` of `𝒜_F`), only the
  diagonal blocks of the tables enter, and masking a positive table to its diagonal blocks keeps
  it positive. So the per-block hypothesis is needed only on the diagonal blocks.
* **`sum_sectors_eq_liftMap`**: for sector maps that are tensor products over the blocks,
  `Ξ_s(x, (v, z)) = ∏_b Ξ_b(s_b)(x_b, (v_b, z_b))` (one singleton sector `s_b` at every block),
  `∑_s Ξ_s (D ⊗ I) Ξ_sᵀ = liftMap (gram Ξ) D` with the per-block Gram tables
  `gram Ξ b ((a, x), (a', y)) = ∑_p ∑_z Ξ_b(p)(x, (a, z)) Ξ_b(p)(y, (a', z))`.
* **`hLift_of_blocks`**: B11's hypothesis `hLift` of `hdom_of_mask`
  (`(Lift - ∑ s, Ξ s * (D ⊗ₖ 1) * (Ξ s)ᴴ).PosSemidef`) for `Lift = liftMap CU D`, from the per-block
  inequalities `gram Ξ b ⪯ CU b` (on the diagonal blocks of `𝒜`) and `D ⪰ 0`.

The per-block inequalities are the paper's: on `{0,1,2}`,
`[V_a V_{a'}^*] ⪰ ∑_p [Ξ_{p,a} Ξ_{p,a'}^*]`
(the singleton sectors are among all sectors); at `3`, `Q₁₂ ⪰ Π_{𝒦₁₂} ⪰ Z Z^*`
(`lem:oct24:pure-pair-substitute`, `contraction_le_proj`); at `4`, `Q₀₁ ⪰ 0`.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace Sarkozy.OpsFeature

/-! ## Factorization of a positive semidefinite matrix -/

section Factor

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive semidefinite real matrix is a Gram matrix: `A = R Rᵀ` (spectral theorem). -/
theorem exists_mul_transpose_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    ∃ R : Matrix n n ℝ, ∀ i j, A i j = ∑ k, R i k * R j k := by
  have hs := hA.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set U : Matrix n n ℝ := (hA.1.eigenvectorUnitary : Matrix n n ℝ) with hU
  set e := hA.1.eigenvalues with he
  refine ⟨fun i k => U i k * Real.sqrt (e k), fun i j => ?_⟩
  have h1 : A i j = ∑ k, U i k * e k * U j k := by
    conv_lhs => rw [hs]
    rw [Matrix.mul_apply]
    refine sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.star_apply]
    simp
  rw [h1]
  refine sum_congr rfl fun k _ => ?_
  have := Real.mul_self_sqrt (hA.eigenvalues_nonneg k)
  calc U i k * e k * U j k = U i k * (Real.sqrt (e k) * Real.sqrt (e k)) * U j k := by
        rw [this]
    _ = _ := by ring

end Factor

/-! ## The lift map and its positivity -/

section LiftMap

variable {X : Type*} [Fintype X] [DecidableEq X] {L O : X → Type*} [∀ b, Fintype (L b)]
  [∀ b, Fintype (O b)]

/-- **The lift of a matrix on label words by per-block unit tables**:
`liftMap C D (x, y) = ∑_{v,w} D_{vw} ∏_b C b ((v_b, x_b), (w_b, y_b))`. -/
def liftMap (C : ∀ b, Matrix (L b × O b) (L b × O b) ℝ) (D : Matrix (∀ b, L b) (∀ b, L b) ℝ) :
    Matrix (∀ b, O b) (∀ b, O b) ℝ :=
  fun x y => ∑ v, ∑ w, D v w * ∏ b, C b (v b, x b) (w b, y b)

/-- The quadratic form of a lift through Gram factorizations `C b = R_b R_bᵀ`. -/
theorem liftMap_form (C R : ∀ b, Matrix (L b × O b) (L b × O b) ℝ)
    (hR : ∀ b p q, C b p q = ∑ k, R b p k * R b q k) (D : Matrix (∀ b, L b) (∀ b, L b) ℝ)
    (ξ : (∀ b, O b) → ℝ) :
    ∑ x, ξ x * ∑ y, liftMap C D x y * ξ y =
      ∑ κ : (∀ b, L b × O b), ∑ v, (∑ x, ξ x * ∏ b, R b (v b, x b) (κ b)) *
        ∑ w, D v w * (∑ y, ξ y * ∏ b, R b (w b, y b) (κ b)) := by
  have hprod : ∀ (v w : ∀ b, L b) (x y : ∀ b, O b), ∏ b, C b (v b, x b) (w b, y b) =
      ∑ κ : (∀ b, L b × O b), (∏ b, R b (v b, x b) (κ b)) * ∏ b, R b (w b, y b) (κ b) := by
    intro v w x y
    simp only [hR, Fintype.prod_sum, ← prod_mul_distrib]
  simp only [liftMap, hprod, mul_sum, sum_mul]
  -- flatten both sides to one sum over the tuples and permute the tuple
  simp only [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv
    { toFun := fun t : (∀ b, O b) × (∀ b, O b) × (∀ b, L b) × (∀ b, L b) × (∀ b, L b × O b) =>
        (t.2.2.2.2, t.2.2.1, t.2.2.2.1, t.2.1, t.1)
      invFun := fun t : (∀ b, L b × O b) × (∀ b, L b) × (∀ b, L b) × (∀ b, O b) × (∀ b, O b) =>
        (t.2.2.2.2, t.2.2.2.1, t.2.1, t.2.2.1, t.1)
      left_inv := fun t => rfl
      right_inv := fun t => rfl }
  intro t
  simp only [Equiv.coe_fn_mk]
  ring

omit [∀ b, Fintype (O b)] in
theorem liftMap_isHermitian {C : ∀ b, Matrix (L b × O b) (L b × O b) ℝ}
    (hC : ∀ b, (C b).IsHermitian) {D : Matrix (∀ b, L b) (∀ b, L b) ℝ} (hD : D.IsHermitian) :
    (liftMap C D).IsHermitian := by
  ext x y
  simp only [conjTranspose_apply, star_trivial, liftMap]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => sum_congr rfl fun w _ => ?_
  have h1 : D w v = D v w := by
    have := congrFun (congrFun hD v) w
    simpa only [conjTranspose_apply, star_trivial] using this
  have h2 : ∀ b, C b (w b, y b) (v b, x b) = C b (v b, x b) (w b, y b) := by
    intro b
    have := congrFun (congrFun (hC b) (v b, x b)) (w b, y b)
    simpa only [conjTranspose_apply, star_trivial] using this
  rw [h1]
  simp only [h2]

/-- **The lift of positive tables is positive**: if every unit table `C b` and `D` are positive
semidefinite, so is `liftMap C D` (a tensor product of completely positive maps is completely
positive). -/
theorem liftMap_posSemidef [∀ b, DecidableEq (L b)] [∀ b, DecidableEq (O b)]
    {C : ∀ b, Matrix (L b × O b) (L b × O b) ℝ}
    (hC : ∀ b, (C b).PosSemidef) {D : Matrix (∀ b, L b) (∀ b, L b) ℝ} (hD : D.PosSemidef) :
    (liftMap C D).PosSemidef := by
  choose R hR using fun b => exists_mul_transpose_of_posSemidef (hC b)
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (liftMap_isHermitian (fun b => (hC b).1) hD.1) fun ξ => ?_
  set G : Matrix (∀ b, L b) (∀ b, L b × O b) ℝ :=
    fun v κ => ∑ x, ξ x * ∏ b, R b (v b, x b) (κ b) with hG
  have htr : (Gᴴ * D * G).trace = ∑ κ, ∑ v, G v κ * ∑ w, D v w * G w κ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, star_trivial]
    refine sum_congr rfl fun κ _ => ?_
    simp only [sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun v _ => sum_congr rfl fun w _ => by ring
  have hform : star ξ ⬝ᵥ (liftMap C D *ᵥ ξ) = (Gᴴ * D * G).trace := by
    simp only [dotProduct, mulVec, star_trivial]
    rw [htr, hG]
    exact liftMap_form C R hR D ξ
  rw [hform]
  exact (hD.conjTranspose_mul_mul_same G).trace_nonneg

/-- Replacing the tables of the blocks in `S` by `E`. -/
def mixT (S : Finset X) (C E : ∀ b, Matrix (L b × O b) (L b × O b) ℝ) (b : X) :
    Matrix (L b × O b) (L b × O b) ℝ :=
  if b ∈ S then E b else C b

omit [∀ b, Fintype (O b)] in
/-- The multilinear expansion of a lift over the subsets of blocks. -/
theorem liftMap_add (C E : ∀ b, Matrix (L b × O b) (L b × O b) ℝ)
    (D : Matrix (∀ b, L b) (∀ b, L b) ℝ) :
    liftMap (fun b => E b + C b) D = ∑ S ∈ (univ : Finset X).powerset, liftMap (mixT S C E) D := by
  ext x y
  simp only [liftMap, Matrix.sum_apply, Matrix.add_apply]
  have e : ∀ v w : ∀ b, L b, ∏ b, (E b (v b, x b) (w b, y b) + C b (v b, x b) (w b, y b)) =
      ∑ S ∈ (univ : Finset X).powerset, ∏ b, mixT S C E b (v b, x b) (w b, y b) := by
    intro v w
    rw [prod_add]
    refine sum_congr rfl fun S _ => ?_
    rw [← prod_mul_prod_compl S (fun b => mixT S C E b (v b, x b) (w b, y b)),
      compl_eq_univ_sdiff]
    congr 1
    · exact prod_congr rfl fun b hb => by simp [mixT, hb]
    · exact prod_congr rfl fun b hb => by simp [mixT, (mem_sdiff.1 hb).2]
  simp only [e, mul_sum]
  rw [sum_congr rfl fun v _ => sum_comm, sum_comm]

/-- **Move 4 of `lem:oct24:mask-schur`(a), for every degree class**: if `0 ⪯ C b ⪯ C' b` at every
block and `D ⪰ 0`, then `liftMap C D ⪯ liftMap C' D`. -/
theorem liftMap_mono [∀ b, DecidableEq (L b)] [∀ b, DecidableEq (O b)]
    {C C' : ∀ b, Matrix (L b × O b) (L b × O b) ℝ}
    (hC : ∀ b, (C b).PosSemidef) (hCC : ∀ b, (C' b - C b).PosSemidef)
    {D : Matrix (∀ b, L b) (∀ b, L b) ℝ} (hD : D.PosSemidef) :
    (liftMap C' D - liftMap C D).PosSemidef := by
  have e : liftMap C' D = liftMap (fun b => (C' b - C b) + C b) D := by
    simp only [sub_add_cancel]
  rw [e, liftMap_add]
  have hmix : ∀ S : Finset X, (liftMap (mixT S C (fun b => C' b - C b)) D).PosSemidef := by
    intro S
    refine liftMap_posSemidef (fun b => ?_) hD
    unfold mixT
    split_ifs
    · exact hCC b
    · exact hC b
  rw [← Finset.add_sum_erase _ (fun S => liftMap (mixT S C (fun b => C' b - C b)) D)
    (empty_mem_powerset (univ : Finset X))]
  have h0 : liftMap (mixT ∅ C (fun b => C' b - C b)) D = liftMap C D := by
    have : mixT ∅ C (fun b => C' b - C b) = C := by funext b; simp [mixT]
    rw [this]
  rw [h0, add_sub_cancel_left]
  exact posSemidef_sum _ fun S _ => hmix S

end LiftMap

/-! ## The block algebra: only the diagonal blocks of the tables enter -/

section Mask

variable {X : Type*} [Fintype X] [DecidableEq X] {L O : X → Type*} [∀ b, Fintype (L b)]
  [∀ b, Fintype (O b)] {K : X → Type*}

/-- `D` lies in the block algebra `𝒜 = ⊗_b 𝒜_b`: at every factor it is block diagonal for the
partition `blk b` of the labels (for a fold factor, `{0,1,2}, {3}, {4}`). -/
def InAlg (blk : ∀ b, L b → K b) (D : Matrix (∀ b, L b) (∀ b, L b) ℝ) : Prop :=
  ∀ v w, (∃ b, blk b (v b) ≠ blk b (w b)) → D v w = 0

/-- The table restricted to its diagonal blocks. -/
def maskT [∀ b, DecidableEq (K b)] (blk : ∀ b, L b → K b)
    (C : ∀ b, Matrix (L b × O b) (L b × O b) ℝ) (b : X) : Matrix (L b × O b) (L b × O b) ℝ :=
  fun p q => if blk b p.1 = blk b q.1 then C b p q else 0

omit [∀ b, Fintype (O b)] in
/-- For `D ∈ 𝒜` only the diagonal blocks of the tables enter the lift. -/
theorem liftMap_mask [∀ b, DecidableEq (K b)] {blk : ∀ b, L b → K b}
    {D : Matrix (∀ b, L b) (∀ b, L b) ℝ} (hD : InAlg blk D)
    (C : ∀ b, Matrix (L b × O b) (L b × O b) ℝ) : liftMap (maskT blk C) D = liftMap C D := by
  ext x y
  simp only [liftMap]
  refine sum_congr rfl fun v _ => sum_congr rfl fun w _ => ?_
  by_cases h : ∃ b, blk b (v b) ≠ blk b (w b)
  · rw [hD v w h, zero_mul, zero_mul]
  · simp only [not_exists, not_not] at h
    congr 1
    exact prod_congr rfl fun b _ => by simp [maskT, h b]

/-- Masking a positive semidefinite table to its diagonal blocks keeps it positive (a pinching). -/
theorem posSemidef_maskT {n : Type*} [Fintype n] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (blk : n → κ) {M : Matrix n n ℝ} (hM : M.PosSemidef) :
    (Matrix.of fun p q => if blk p = blk q then M p q else 0 : Matrix n n ℝ).PosSemidef := by
  classical
  set P : κ → Matrix n n ℝ := fun k => diagonal fun p => if blk p = k then (1 : ℝ) else 0 with hP
  have e : (Matrix.of fun p q => if blk p = blk q then M p q else 0 : Matrix n n ℝ) =
      ∑ k : κ, (P k)ᴴ * M * P k := by
    ext p q
    have hk : ∀ k, ((P k)ᴴ * M * P k) p q =
        (if blk p = k then 1 else 0) * M p q * (if blk q = k then 1 else 0) := by
      intro k
      simp only [hP, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp
    simp only [Matrix.of_apply, Matrix.sum_apply, hk]
    by_cases h : blk p = blk q
    · rw [ite_eq_left h, Finset.sum_eq_single (blk p)]
      · simp [h]
      · intro k _ hk'; simp [Ne.symm hk']
      · simp
    · rw [ite_eq_right h]
      refine (sum_eq_zero fun k _ => ?_).symm
      by_cases hp : blk p = k
      · have : ¬ blk q = k := fun hq => h (hp.trans hq.symm)
        simp [this]
      · simp [hp]
  rw [e]
  exact posSemidef_sum _ fun k _ => hM.conjTranspose_mul_mul_same _

end Mask

/-! ## The sum over the singleton sectors -/

section Sectors

variable {X : Type*} [Fintype X] [DecidableEq X] {L O : X → Type*} [∀ b, Fintype (L b)]
  [∀ b, DecidableEq (L b)] [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)]
  {Sb : X → Type*} [∀ b, Fintype (Sb b)] {Zb : ∀ b, Sb b → Type*}
  [∀ b p, Fintype (Zb b p)] [∀ b p, DecidableEq (Zb b p)]

/-- The sector map of a choice `s` of one singleton sector at every block, as a tensor product:
`Ξ_s(x, (v, z)) = ∏_b Ξ_b(s_b)(x_b, (v_b, z_b))`. -/
def xiS (Ξb : ∀ b (p : Sb b), Matrix (O b) (L b × Zb b p) ℝ) (s : ∀ b, Sb b) :
    Matrix (∀ b, O b) ((∀ b, L b) × (∀ b, Zb b (s b))) ℝ :=
  fun x vz => ∏ b, Ξb b (s b) (x b) (vz.1 b, vz.2 b)

/-- The per-block Gram table of the sector maps,
`gramT Ξ b ((a, x), (a', y)) = ∑_p ∑_z Ξ_b(p)(x, (a, z)) Ξ_b(p)(y, (a', z))`. -/
def gramT (Ξb : ∀ b (p : Sb b), Matrix (O b) (L b × Zb b p) ℝ) (b : X) :
    Matrix (L b × O b) (L b × O b) ℝ :=
  fun P Q => ∑ p : Sb b, ∑ z : Zb b p, Ξb b p P.2 (P.1, z) * Ξb b p Q.2 (Q.1, z)

omit [Fintype X] [DecidableEq X] [∀ b, DecidableEq (L b)] [∀ b, DecidableEq (O b)]
  [∀ b p, DecidableEq (Zb b p)] in
theorem gramT_posSemidef (Ξb : ∀ b (p : Sb b), Matrix (O b) (L b × Zb b p) ℝ) (b : X) :
    (gramT Ξb b).PosSemidef := by
  set R : ∀ p : Sb b, Matrix (L b × O b) (Zb b p) ℝ :=
    fun p => Matrix.of fun P z => Ξb b p P.2 (P.1, z) with hR
  have e : gramT Ξb b = ∑ p : Sb b, R p * (R p)ᴴ := by
    ext P Q
    simp only [gramT, Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, star_trivial, hR,
      Matrix.of_apply]
  rw [e]
  exact posSemidef_sum _ fun p _ => posSemidef_self_mul_conjTranspose _

omit [∀ b, Fintype (L b)] [∀ b, DecidableEq (L b)] [∀ b, Fintype (O b)]
  [∀ b, DecidableEq (O b)] [∀ b p, DecidableEq (Zb b p)] in
/-- `∑_s ∑_z ∏_b F_b(s_b, z_b) = ∏_b ∑_p ∑_z F_b(p, z)` (a sum over the sector choices). -/
theorem sum_sector_prod (F : ∀ b (p : Sb b), Zb b p → ℝ) :
    ∑ s : (∀ b, Sb b), ∑ z : (∀ b, Zb b (s b)), ∏ b, F b (s b) (z b) =
      ∏ b, ∑ p : Sb b, ∑ z : Zb b p, F b p z := by
  have e1 : ∀ b, ∑ p : Sb b, ∑ z : Zb b p, F b p z = ∑ σ : (Σ p : Sb b, Zb b p), F b σ.1 σ.2 :=
    fun b => (Fintype.sum_sigma' (F b)).symm
  simp only [e1, Fintype.prod_sum]
  rw [← Fintype.sum_sigma' (fun (s : ∀ b, Sb b) (z : ∀ b, Zb b (s b)) => ∏ b, F b (s b) (z b))]
  exact Fintype.sum_equiv
    { toFun := fun σ b => ⟨σ.1 b, σ.2 b⟩
      invFun := fun τ => ⟨fun b => (τ b).1, fun b => (τ b).2⟩
      left_inv := fun σ => rfl
      right_inv := fun τ => rfl } _ _ (fun σ => rfl)

omit [∀ b, DecidableEq (L b)] [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)] in
/-- **The sum over the singleton sectors is a lift**:
`∑_s Ξ_s (D ⊗ I) Ξ_sᵀ = liftMap (gram Ξ) D`. -/
theorem sum_sectors_eq_liftMap (Ξb : ∀ b (p : Sb b), Matrix (O b) (L b × Zb b p) ℝ)
    (D : Matrix (∀ b, L b) (∀ b, L b) ℝ) :
    ∑ s : (∀ b, Sb b), xiS Ξb s * (D ⊗ₖ (1 : Matrix (∀ b, Zb b (s b)) (∀ b, Zb b (s b)) ℝ)) *
      (xiS Ξb s)ᴴ = liftMap (gramT Ξb) D := by
  ext x y
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, star_trivial,
    kroneckerMap_apply, one_apply, liftMap, gramT, xiS]
  -- the left side, reorganized
  have hL : ∀ s : (∀ b, Sb b),
      ∑ k : (∀ b, L b) × (∀ b, Zb b (s b)), (∑ j : (∀ b, L b) × (∀ b, Zb b (s b)),
        (∏ b, Ξb b (s b) (x b) (j.1 b, j.2 b)) * (D j.1 k.1 * if j.2 = k.2 then 1 else 0)) *
          ∏ b, Ξb b (s b) (y b) (k.1 b, k.2 b) =
      ∑ v, ∑ w, D v w * ∑ z : (∀ b, Zb b (s b)),
        ∏ b, (Ξb b (s b) (x b) (v b, z b) * Ξb b (s b) (y b) (w b, z b)) := by
    intro s
    simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, sum_mul, ite_mul, zero_mul]
    simp only [sum_ite_eq', mem_univ, ↓reduceIte]
    simp only [mul_sum, prod_mul_distrib]
    simp only [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv
      { toFun := fun t : (∀ b, L b) × (∀ b, Zb b (s b)) × (∀ b, L b) => (t.2.2, t.1, t.2.1)
        invFun := fun u : (∀ b, L b) × (∀ b, L b) × (∀ b, Zb b (s b)) => (u.2.1, u.2.2, u.1)
        left_inv := fun t => rfl
        right_inv := fun u => rfl } _ _ (fun t => by simp only [Equiv.coe_fn_mk]; ring)
  simp only [hL]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  rw [← mul_sum]
  congr 1
  exact sum_sector_prod (fun b p z => Ξb b p (x b) (v b, z) * Ξb b p (y b) (w b, z))

/-- **B11's `hLift` from per-block inequalities** (`lem:oct24:mask-schur`(a), move 4, for every
degree class). With the sector maps `Ξ_s` tensor products of per-block maps, `Lift = liftMap CU D`
for the unit tables `CU` of `Lift(D)`, `D ⪰ 0` in the block algebra `𝒜` (`InAlg blk D`), and at
every block the diagonal blocks of `CU` dominating those of the Gram table of the sector maps,
`(Lift - ∑ s, Ξ s * (D ⊗ₖ 1) * (Ξ s)ᴴ).PosSemidef` (the hypothesis `hLift` of
`EnvelopeSteps.hdom_of_mask` and `EnvelopeSteps.mask_lift`). -/
theorem hLift_of_blocks {K : X → Type*} [∀ b, Fintype (K b)] [∀ b, DecidableEq (K b)]
    (blk : ∀ b, L b → K b) (Ξb : ∀ b (p : Sb b), Matrix (O b) (L b × Zb b p) ℝ)
    (CU : ∀ b, Matrix (L b × O b) (L b × O b) ℝ) {D : Matrix (∀ b, L b) (∀ b, L b) ℝ}
    (hD : D.PosSemidef) (hA : InAlg blk D)
    (hUY : ∀ b, (maskT blk CU b - maskT blk (gramT Ξb) b).PosSemidef) :
    (liftMap CU D - ∑ s : (∀ b, Sb b), xiS Ξb s *
      (D ⊗ₖ (1 : Matrix (∀ b, Zb b (s b)) (∀ b, Zb b (s b)) ℝ)) * (xiS Ξb s)ᴴ).PosSemidef := by
  rw [sum_sectors_eq_liftMap, ← liftMap_mask hA CU, ← liftMap_mask hA (gramT Ξb)]
  refine liftMap_mono (fun b => ?_) hUY hD
  exact posSemidef_maskT (blk b ∘ Prod.fst) (gramT_posSemidef Ξb b)

end Sectors

end Sarkozy.OpsFeature
