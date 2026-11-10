module

public import Sarkozy.PartVRecords.OneStage

@[expose] public section

/-!
# The one-stage replacement on a block, and the frame of a middle block
(`lem:record:one-stage-folded-e`(e), `def:record:frame`(c))

`paper/sections/20c_middle_frame.tex`, `lem:record:one-stage-folded-e`(e) and
`def:record:frame`(c). On a block of primes `p ≡ 3 (mod 4)`, `p ≥ 7` (in the paper `p ≥ X ≥ 2²⁴`),
the replacement of each folded matching record is the product over the primes of the one-prime
replacement law of `Sarkozy.PartVRecords.OneStage` (`blockPlusLaw`): the shared label uniform
and, given it, the private pair distributed by `⊗_p 𝒦₊^{(c_p)}`.

Proved here:
* `blockPlusLaw` has uniform one-slot marginals on `X_𝔅` (`blockPlusLaw_vertex_uniform`) and is
  invariant under the maps `z_p ↦ α_p z_p + β_p` acting independently at the primes of the block,
  `χ_p(α_p) = 1` (`blockPlusLaw_affine`);
* on its support, at every prime of the block, `y₀ → y₁` and `y₀, y₁ ≠ y₂`
  (`blockPlusLaw_support`);
* **the replacement records accept the six queries** (`newRec_accepts`): through the diagonal
  emission of `E_s`, every query `(0, j, 0) → (2, rot j, 1)` of `𝓔₆` reads the pair `y₀ → y₁`
  (`cert:record:middle-geometry`: the one-layer `E₀, E₁` need exactly the edge `0 → 1`);
* `middleFrame`: the frame data of a middle block, with V1's block field laws
  (`middleBlockFieldLaws`), `r = b^{-1/2}`, `b` the least prime, and `κnew = blockPlusLaw`;
  its `E_new` records are positive records (`middleFrame_newRec_positiveRecord`).

**Not proved:** the sharp bound of the block difference (`lem:record:one-stage-folded-e`(d)) and
the comparison of the half marginals on the block (they are products of the one-prime half
marginals `plusLaw_pair02`, `plusLaw_pair12`, which equal those of the replaced record; the
product statement is not written out).
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.Labellings Sarkozy.PartV Sarkozy.TheoremC

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The primes of a block are of class three and at least `7`** (true for the middle blocks,
whose primes are class-three primes `≥ Q₃ > 11`). -/
structure ClassThreeBlock : Prop where
  mod4 : ∀ i, pr i % 4 = 3
  ge7 : ∀ i, 7 ≤ pr i

namespace ClassThreeBlock

variable {pr}

omit [Fintype ι] [DecidableEq ι] in
theorem ringChar_ne (h : ClassThreeBlock pr) (i : ι) : ringChar (ZMod (pr i)) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  have := h.ge7 i
  omega

omit [Fintype ι] [DecidableEq ι] in
theorem card_mod (h : ClassThreeBlock pr) (i : ι) : Fintype.card (ZMod (pr i)) % 4 = 3 := by
  rw [ZMod.card]
  exact h.mod4 i

omit [Fintype ι] [DecidableEq ι] in
theorem kP_pos' (h : ClassThreeBlock pr) (i : ι) : 0 < kP (ZMod (pr i)) := by
  apply kP_pos
  rw [ZMod.card]
  exact h.ge7 i

end ClassThreeBlock

/-- **The block replacement law** `⊗_p` (shared label uniform, private pair by `𝒦₊^{(c_p)}`). -/
noncomputable def blockPlusLaw (h : ClassThreeBlock pr) :
    FiniteLaw (Fin 3 × Fin 1 → BlockLabel pr) :=
  FiniteLaw.tensor fun i => plusLaw (ZMod (pr i)) (h.ringChar_ne i) (h.card_mod i) (h.kP_pos' i)

/-- **Uniform one-slot marginals** of the block replacement. -/
theorem blockPlusLaw_vertex_uniform (h : ClassThreeBlock pr) (o : Fin 3 × Fin 1)
    (g : BlockLabel pr → ℝ) :
    (blockPlusLaw pr h).expect (fun y => g (y o)) = (FiniteLaw.uniform (BlockLabel pr)).expect g :=
  tensor_uniform_marginals _ (fun _ => plusLaw_vertex_uniform _ _ _) o g

/-- **Support of the block replacement**: at every prime of the block, `y₀ → y₁` and
`y₀, y₁ ≠ y₂`. -/
theorem blockPlusLaw_support (h : ClassThreeBlock pr) {y : Fin 3 × Fin 1 → BlockLabel pr}
    (hy : (blockPlusLaw pr h).weight y ≠ 0) (i : ι) :
    quadraticChar (ZMod (pr i)) (y (1, 0) i - y (0, 0) i) = 1 ∧ y (0, 0) i ≠ y (2, 0) i ∧
      y (1, 0) i ≠ y (2, 0) i := by
  unfold blockPlusLaw at hy
  rw [tensor_weight] at hy
  have hi := (Finset.prod_ne_zero_iff.mp hy) i (mem_univ _)
  exact plusLaw_support _ _ _ hi

/-- **Invariance under `𝒢_p`, independently at the primes of the block**
(`lem:record:one-stage-folded-e`(e)). -/
theorem blockPlusLaw_affine (h : ClassThreeBlock pr) (α β : BlockLabel pr)
    (hα : ∀ i, quadraticChar (ZMod (pr i)) (α i) = 1) (H : (Fin 3 × Fin 1 → BlockLabel pr) → ℝ) :
    (blockPlusLaw pr h).expect (fun z => H (fun w i => α i * z w i + β i)) =
      (blockPlusLaw pr h).expect H := by
  have hα0 : ∀ i, α i ≠ 0 := fun i => ne_zero_of_quadraticChar_eq_one (hα i)
  let T : ∀ i, (Fin 3 × Fin 1 → ZMod (pr i)) ≃ (Fin 3 × Fin 1 → ZMod (pr i)) := fun i =>
    Equiv.piCongrRight fun _ => affineMap (α i) (hα0 i) (β i)
  have hT : ∀ i y, (plusLaw (ZMod (pr i)) (h.ringChar_ne i) (h.card_mod i) (h.kP_pos' i)).weight
      (T i y) =
        (plusLaw (ZMod (pr i)) (h.ringChar_ne i) (h.card_mod i) (h.kP_pos' i)).weight y := by
    intro i y
    rw [weight_eq_expect, weight_eq_expect]
    have := plusLaw_affine (h.ringChar_ne i) (h.card_mod i) (h.kP_pos' i) (hα i) (β i)
      (fun z => if z = T i y then 1 else 0)
    rw [← this]
    apply FiniteLaw.expect_congr
    intro z
    have hinj : (fun o => α i * z o + β i) = T i y ↔ z = y := by
      constructor
      · intro e
        funext o
        have := congrFun e o
        change α i * z o + β i = α i * y o + β i at this
        exact mul_left_cancel₀ (hα0 i) (add_right_cancel this)
      · rintro rfl
        rfl
    simp only [hinj]
  exact expect_tensor_comp _ T hT H

/-- Through the diagonal emission of `E_s`, the query target `(2, rot j, 1)` reads object `1`. -/
theorem midDiag_queryTarget (s : Fin 2) (j : Chamber) :
    midDiagEmission (matching s) (queryTarget j) = (1, 0) := by
  revert s j
  decide

/-- Through the diagonal emission of `E_s`, the query source `(0, j, 0)` reads object `0`. -/
theorem midDiag_querySource (s : Fin 2) (j : Chamber) :
    midDiagEmission (matching s) (querySource j) = (0, 0) := by
  revert s j
  decide

/-- **The replacement records accept the six queries** (`lem:record:one-stage-folded-e`(e)):
on the support of `emit κnew (Diag_ι ∘ E_s)`, every query difference `z_{v_e} - z_{u_e}` of `𝓔₆`
is a nonzero square at every prime of the block. -/
theorem newRec_accepts (h : ClassThreeBlock pr) (s : Fin 2) {z : Slot → BlockLabel pr}
    (hz : (emit (blockPlusLaw pr h) (midDiagEmission (matching s))).weight z ≠ 0) (j : Chamber)
    (i : ι) : quadraticChar (ZMod (pr i)) (z (queryTarget j) i - z (querySource j) i) = 1 := by
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  simp only [Function.comp_apply, midDiag_queryTarget, midDiag_querySource]
  exact (blockPlusLaw_support pr h hy i).1

/-! ## The frame of a middle block -/

/-- **The frame data of a middle block** (`def:record:frame`): V1's block field laws with the
root `root`, the weights `W` and inputs `I` of the piece, `r = b^{-1/2}` with `b` the least prime
(given here as `r` and `b` with `r ≥ 0`), and the replacement law `blockPlusLaw`. -/
noncomputable def middleFrame (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (b : ℝ) (h : ClassThreeBlock pr) : FrameData (BlockLabel pr) where
  F := middleBlockFieldLaws pr hne root
  W := W
  I := I
  r := r
  r_nonneg := hr
  b := b
  κnew := blockPlusLaw pr h

/-- The frame's reference is V1's `middleBlockReference`. -/
theorem middleFrame_mu (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (b : ℝ) (h : ClassThreeBlock pr) :
    (middleFrame pr hne root W I hr b h).mu =
      signedIntegral (middleBlockReference pr hne root W hr).weight :=
  (middleFrame pr hne root W I hr b h).mu_eq

/-- The `E_new` records of a middle block are positive records (nonnegative with uniform one-slot
marginals; the remark after `lem:record:one-stage-folded-e`). -/
theorem middleFrame_newRec_positiveRecord (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (b : ℝ) (h : ClassThreeBlock pr) (s : Fin 2) {a : ℝ} (ha : 0 ≤ a) :
    IsPositiveRecord (a • (middleFrame pr hne root W I hr b h).newRec s) :=
  (middleFrame pr hne root W I hr b h).isPositiveRecord_newRec
    (fun o g => blockPlusLaw_vertex_uniform pr h o g) s ha

/-- The one-layer field laws of a middle block have uniform vertex marginals, so the frame
records are positive records (`isPositiveRecord_diag`). -/
theorem middleFrame_one_uniform (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (b : ℝ) (h : ClassThreeBlock pr) (f : FType) (o : f.Obj × Fin 1)
    (g : BlockLabel pr → ℝ) :
    ((middleFrame pr hne root W I hr b h).F.one f).expect (fun y => g (y o)) =
      (FiniteLaw.uniform (BlockLabel pr)).expect g := by
  cases f
  · exact blockGraphLaw_vertex_uniform pr _ hne.L1 o g
  · exact blockGraphLaw_vertex_uniform pr _ hne.F1 o g
  · exact blockGraphLaw_vertex_uniform pr _ hne.E1 o g

end Sarkozy.PartVRecords
