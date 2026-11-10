module

public import Sarkozy.MiddleRefinement.Frame
public import Sarkozy.PartVRecords.MatchingReserved

@[expose] public section

/-!
# The block Gram of a fold record in measure form and in `L²(m₀)` form (SGA)

`paper/sections/24_matching_mean.tex`, `lem:record:asymmetric-gram`(a),(b): the paragraph "In
measure form" of the proof of (b), and the enlargement (a).

The fold record `Π_{F_j}` of a middle block is the image of a law `K₀` on two-layer labellings
`y = (x, y')` of the three fold objects under the middle emission of the fold pattern; its
one-layer companion `D^j` is the image of a law `ν` on one-layer labellings under the diagonal
emission. At the reserved cut `ι`, the cut form of such an image at half functions `F, G` is the
kernel form of the law at the triples read by the half (`form_two`, `form_diag`):

* `kform K φ ψ = ∑_y K(y) φ(y₀) ψ(y₁)` (the form `⟨φ, T_K ψ⟩_{L²(m₀)}` of the Markov operator of
  `K` when both half marginals of `K` are `m₀`);
* `mform K φ = ∑_y K(y) φ(y₀)²` (the norm `‖φ‖²_{L²(m₀)}`, `m₀` the layer-`0` marginal of `K`);
* `dform ν φ ψ = ∑_x ν(x) φ(x) ψ(x)` (the form of the diagonal law `Diag_ι(ν)`).

**`OpGram K₀ K' σ_L σ_R`** is the block Gram of `lem:record:asymmetric-gram`(b) on `L²(m₀)²`
with the shifts `σ_s` times the identity:
`(T_old + σ_L I   T' ; T'*   T_old + σ_R I) ⪰ 0` ("This gives the block Gram on `L²(m_{0,𝔅})²`
with the shifts `σ_s` times `I`"). **`DensityLe K₀ ν H`** is the density bound
`‖φ‖²_{L²(m₀)} ≤ H ‖φ‖²_{L²(ν)}`, i.e. `dm₀/dν ≤ H` (`H_𝔅` of (b)).

**`bracket_of_opGram`** (the measure form of (b)): if the cut form of the replacement `Π'` is the
kernel form of `K'`, then `OpGram K₀ K' σ_L σ_R`, `DensityLe K₀ ν H` and `H σ_s ≤ r d_s` give the
cut bracket `(Π + r d_L D   Π' ; ·   Π + r d_R D) ⪰_ι 0`. It uses the layer-swap symmetry of
`K₀` for the symmetry of the diagonal blocks. The enlargement (a) is the inequality
`H σ_s ≤ r d_s` itself: any larger side works.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedGram

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.MiddleComparison Sarkozy.SignedComponents Sarkozy.MiddleRefinement
open Sarkozy.Labellings

section Generic

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The layer `ℓ` of a two-layer labelling of the three fold objects. -/
def lay2 (y : Fin 3 × Fin 2 → X) (ℓ : Fin 2) : Fin 3 → X := fun o => y (o, ℓ)

/-- The triple of a one-layer labelling of the three fold objects. -/
def lay1 (x : Fin 3 × Fin 1 → X) : Fin 3 → X := fun o => x (o, 0)

/-- The kernel form `∑_y K(y) φ(y₀) ψ(y₁)` of a weight on pairs of triples. -/
noncomputable def kform (K : (Fin 3 × Fin 2 → X) → ℝ) (φ ψ : (Fin 3 → X) → ℝ) : ℝ :=
  ∑ y, K y * (φ (lay2 y 0) * ψ (lay2 y 1))

/-- The norm form `∑_y K(y) φ(y₀)²` of the layer-`0` marginal of `K` (`‖φ‖²_{L²(m₀)}`). -/
noncomputable def mform (K : (Fin 3 × Fin 2 → X) → ℝ) (φ : (Fin 3 → X) → ℝ) : ℝ :=
  ∑ y, K y * (φ (lay2 y 0) * φ (lay2 y 0))

/-- The diagonal form `∑_x ν(x) φ(x) ψ(x)` of a weight on triples. -/
noncomputable def dform (ν : (Fin 3 × Fin 1 → X) → ℝ) (φ ψ : (Fin 3 → X) → ℝ) : ℝ :=
  ∑ x, ν x * (φ (lay1 x) * ψ (lay1 x))

/-- **The block Gram on `L²(m₀)²` with the shifts `σ_s I`** (`lem:record:asymmetric-gram`(b), the
conclusion of the sector argument): for all `φ, ψ`,
`⟨φ, T_old φ⟩ + σ_L ‖φ‖² + 2 ⟨φ, T' ψ⟩ + ⟨ψ, T_old ψ⟩ + σ_R ‖ψ‖² ≥ 0`, with `T_old` the operator
of `K₀`, `T'` that of `K'`, and the norms of `L²(m₀)`, `m₀` the half marginal of `K₀`. -/
def OpGram (K₀ K' : (Fin 3 × Fin 2 → X) → ℝ) (σL σR : ℝ) : Prop :=
  ∀ φ ψ : (Fin 3 → X) → ℝ,
    0 ≤ kform K₀ φ φ + σL * mform K₀ φ + 2 * kform K' φ ψ + kform K₀ ψ ψ + σR * mform K₀ ψ

/-- **The density bound** `dm₀/dν ≤ H` (`H_𝔅` of `lem:record:asymmetric-gram`(b)), in quadratic
form: `‖φ‖²_{L²(m₀)} ≤ H ‖φ‖²_{L²(ν)}`. -/
def DensityLe (K₀ : (Fin 3 × Fin 2 → X) → ℝ) (ν : (Fin 3 × Fin 1 → X) → ℝ) (H : ℝ) : Prop :=
  ∀ φ : (Fin 3 → X) → ℝ, mform K₀ φ ≤ H * dform ν φ φ

omit [DecidableEq X] in
theorem kform_zero_right (K : (Fin 3 × Fin 2 → X) → ℝ) (φ : (Fin 3 → X) → ℝ) :
    kform K φ 0 = 0 := by
  simp [kform]

omit [DecidableEq X] in
theorem kform_zero (K : (Fin 3 × Fin 2 → X) → ℝ) : kform K (0 : (Fin 3 → X) → ℝ) 0 = 0 := by
  simp [kform]

omit [DecidableEq X] in
theorem mform_zero (K : (Fin 3 × Fin 2 → X) → ℝ) : mform K (0 : (Fin 3 → X) → ℝ) = 0 := by
  simp [mform]

omit [DecidableEq X] in
theorem dform_nonneg {ν : (Fin 3 × Fin 1 → X) → ℝ} (hν : ∀ x, 0 ≤ ν x) (φ : (Fin 3 → X) → ℝ) :
    0 ≤ dform ν φ φ :=
  sum_nonneg fun x _ => mul_nonneg (hν x) (mul_self_nonneg _)

omit [DecidableEq X] in
theorem dform_comm (ν : (Fin 3 × Fin 1 → X) → ℝ) (φ ψ : (Fin 3 → X) → ℝ) :
    dform ν φ ψ = dform ν ψ φ := by
  unfold dform
  refine sum_congr rfl fun x _ => ?_
  ring

/-- The layer swap of two-layer labellings, as an equivalence. -/
def swapE : (Fin 3 × Fin 2 → X) ≃ (Fin 3 × Fin 2 → X) where
  toFun y := y ∘ layerSwapMap (Fin 3)
  invFun y := y ∘ layerSwapMap (Fin 3)
  left_inv y := by
    funext ⟨o, l⟩
    fin_cases l <;> rfl
  right_inv y := by
    funext ⟨o, l⟩
    fin_cases l <;> rfl

omit [Fintype X] [DecidableEq X] in
theorem lay2_swapE (y : Fin 3 × Fin 2 → X) : lay2 (swapE y) 0 = lay2 y 1 ∧
    lay2 (swapE y) 1 = lay2 y 0 := ⟨rfl, rfl⟩

omit [DecidableEq X] in
/-- **A layer-swap invariant law has a symmetric kernel form.** -/
theorem kform_comm {K : (Fin 3 × Fin 2 → X) → ℝ}
    (hK : ∀ y, K (y ∘ layerSwapMap (Fin 3)) = K y) (φ ψ : (Fin 3 → X) → ℝ) :
    kform K φ ψ = kform K ψ φ := by
  unfold kform
  refine Fintype.sum_equiv swapE _ _ fun y => ?_
  change K y * (φ (lay2 y 0) * ψ (lay2 y 1)) =
    K (y ∘ layerSwapMap (Fin 3)) * (ψ (lay2 (swapE y) 0) * φ (lay2 (swapE y) 1))
  rw [hK, (lay2_swapE y).1, (lay2_swapE y).2]
  ring

/-- The reading of a half configuration of `ι` from the labels of the three objects of one layer,
under a pattern `φ : ℤ/6ℤ → O`. -/
def hread (pat : ZMod 6 → Fin 3) (x : Fin 3 → X) : reservedCut.Half → X := fun v => x (pat v.1.1)

/-- **The cut form at `ι` of a two-layer image** is the kernel form of the law at the read
triples. -/
theorem form_two (lam : FiniteLaw (Fin 3 × Fin 2 → X)) (pat : ZMod 6 → Fin 3)
    (F G : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (signedIntegral (emit lam (midEmission pat)).weight) F G =
      kform lam.weight (fun x => F (hread pat x)) (fun x => G (hread pat x)) := by
  rw [signedIntegral_emit]
  change ∑ y, lam.weight y * (F (fun v => y (midEmission pat v.1)) *
    G (fun v => y (midEmission pat (reservedCut.flip v.1)))) = _
  refine sum_congr rfl fun y _ => ?_
  have h0 : (fun v : reservedCut.Half => y (midEmission pat v.1)) = hread pat (lay2 y 0) := by
    funext v
    simp only [midEmission, hread, lay2, reservedCut_half_layer v]
    rfl
  have h1 : (fun v : reservedCut.Half => y (midEmission pat (reservedCut.flip v.1))) =
      hread pat (lay2 y 1) := by
    funext v
    simp only [midEmission, hread, lay2, reservedCut_flip_apply, reservedCut_half_layer v]
    rfl
  rw [h0, h1]

/-- **The cut form at `ι` of a diagonal image** is the diagonal form of the law at the read
triple. -/
theorem form_diag (ν : FiniteLaw (Fin 3 × Fin 1 → X)) (pat : ZMod 6 → Fin 3)
    (F G : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (signedIntegral (emit ν (midDiagEmission pat)).weight) F G =
      dform ν.weight (fun x => F (hread pat x)) (fun x => G (hread pat x)) := by
  rw [signedIntegral_emit]
  change ∑ x, ν.weight x * (F (fun v => x (midDiagEmission pat v.1)) *
    G (fun v => x (midDiagEmission pat (reservedCut.flip v.1)))) = _
  rfl

end Generic

/-! ## At V3's frame -/

section Frame

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] (D : FrameData X)
  {acc : X → X → Prop} {E : Type} {Q : Queries E} (R : Replacements D acc Q)

/-- The two-layer fold law `K₀` of the frame (`λ(G_{F,2})`, V1's `F.two .F`). -/
noncomputable abbrev K0w : (Fin 3 × Fin 2 → X) → ℝ := (D.F.two .F).weight

/-- The one-layer fold law `ν_F` of the frame (`λ(G_{F,1})`, V1's `F.one .F`). -/
noncomputable abbrev nuw : (Fin 3 × Fin 1 → X) → ℝ := (D.F.one .F).weight

/-- The half reading of the fold `F_{j+1}`. -/
abbrev foldRead (j : Fin 2) : ZMod 6 → Fin 3 := PType.pat .D (foldPat j)

omit [Nonempty X] in
theorem form_foldRec (j : Fin 2) (F G : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (foldRec D j) F G =
      kform (K0w D) (fun x => F (hread (foldRead j) x)) (fun x => G (hread (foldRead j) x)) :=
  form_two _ _ F G

omit [Nonempty X] in
theorem form_foldDiag (j : Fin 2) (F G : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (foldDiag D j) F G =
      dform (nuw D) (fun x => F (hread (foldRead j) x)) (fun x => G (hread (foldRead j) x)) :=
  form_diag _ _ F G

omit [Nonempty X] in
theorem form_side (j : Fin 2) (c : ℝ) (F G : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (foldRec D j + c • foldDiag D j) F G =
      kform (K0w D) (fun x => F (hread (foldRead j) x)) (fun x => G (hread (foldRead j) x)) +
        c * dform (nuw D) (fun x => F (hread (foldRead j) x))
          (fun x => G (hread (foldRead j) x)) := by
  rw [← form_foldRec, ← form_foldDiag]
  rfl

variable {D} in
/-- **The measure form of `lem:record:asymmetric-gram`(b)** (with the enlargement (a)): if the
cut form of the replacement `Π'_{F_{j+1}}` is the kernel form of `K'`, the block Gram
`OpGram K₀ K' σ_a σ_b` on `L²(m₀)²`, the density bound `DensityLe K₀ ν H` and `H σ_s ≤ r d_s`
give the cut bracket `(Π + r d_a D   Π' ; ·   Π + r d_b D) ⪰_ι 0`. The layer-swap invariance of
`K₀` gives the symmetry of the diagonal blocks. -/
theorem bracket_of_opGram (j : Fin 2) {K' : (Fin 3 × Fin 2 → X) → ℝ}
    (hK' : ∀ F G, reservedCut.form (R.newMeas (.inl j)) F G =
      kform K' (fun x => F (hread (foldRead j) x)) (fun x => G (hread (foldRead j) x)))
    (hswap : ∀ y, K0w D (y ∘ layerSwapMap (Fin 3)) = K0w D y)
    {σa σb H da db : ℝ} (ha : 0 ≤ σa) (hb : 0 ≤ σb) (hdens : DensityLe (K0w D) (nuw D) H)
    (hHa : H * σa ≤ D.r * da) (hHb : H * σb ≤ D.r * db) (hG : OpGram (K0w D) K' σa σb) :
    reservedCut.Bracket (foldRec D j + (D.r * da) • foldDiag D j) (R.newMeas (.inl j))
      (foldRec D j + (D.r * db) • foldDiag D j) := by
  have hν : ∀ x, 0 ≤ nuw D x := (D.F.one .F).nonneg
  -- the shift bound: `σ ‖φ‖²_{m₀} ≤ r d ‖φ‖²_ν`
  have hshift : ∀ {σ d : ℝ}, 0 ≤ σ → H * σ ≤ D.r * d → ∀ φ : (Fin 3 → X) → ℝ,
      σ * mform (K0w D) φ ≤ D.r * d * dform (nuw D) φ φ := by
    intro σ d hσ hHd φ
    have h1 := mul_le_mul_of_nonneg_left (hdens φ) hσ
    have h2 := mul_le_mul_of_nonneg_right hHd (dform_nonneg hν φ)
    nlinarith
  have hpos : ∀ {σ d : ℝ}, 0 ≤ σ → H * σ ≤ D.r * d → (∀ φ, 0 ≤ kform (K0w D) φ φ + σ *
      mform (K0w D) φ) → reservedCut.Positive (foldRec D j + (D.r * d) • foldDiag D j) := by
    intro σ d hσ hHd hφ
    refine ⟨fun F G => ?_, fun F => ?_⟩
    · rw [form_side, form_side, kform_comm hswap, dform_comm]
    · rw [form_side]
      have := hshift hσ hHd (fun x => F (hread (foldRead j) x))
      linarith [hφ (fun x => F (hread (foldRead j) x))]
  have hL : ∀ φ, 0 ≤ kform (K0w D) φ φ + σa * mform (K0w D) φ := by
    intro φ
    have := hG φ 0
    rw [kform_zero_right, kform_zero, mform_zero] at this
    linarith
  have hR : ∀ ψ, 0 ≤ kform (K0w D) ψ ψ + σb * mform (K0w D) ψ := by
    intro ψ
    have := hG 0 ψ
    have e : kform K' 0 ψ = 0 := by simp [kform]
    rw [e, kform_zero, mform_zero] at this
    linarith
  refine ⟨hpos ha hHa hL, hpos hb hHb hR, fun F G => ?_⟩
  rw [form_side, form_side, hK']
  have h1 := hshift ha hHa (fun x => F (hread (foldRead j) x))
  have h2 := hshift hb hHb (fun x => G (hread (foldRead j) x))
  have h3 := hG (fun x => F (hread (foldRead j) x)) (fun x => G (hread (foldRead j) x))
  linarith

end Frame

end Sarkozy.SignedGram
