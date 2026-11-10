module

public import Sarkozy.PartVRecords.MatchingReserved
public import Sarkozy.PartV.ChamberCut
public import Sarkozy.PartV.BlockLaw
public import Sarkozy.Misc.TripleBlock

@[expose] public section

/-!
# The matching components at `ι` on a block of primes (`it:triple:block` in `lem:record:gram`)

`paper/sections/20c_middle_frame.tex`, proof of `lem:record:gram`(ii): "the component `Π_{E_s}`
is uniform on two disjoint injective triples, and its cut operator at `ι` relative to its actual
half law […] is the disjoint-triple operator at each prime; by
`sec:frontier:empty-triple-negative`(c) its spectrum on the block lies in `[-3/(b-3), 1]`. Hence
`Π_{E_s} + 3/(b-3) Diag_ι(Π⁽¹⁾_{E_s}) ⪰_ι 0`."

`Sarkozy.PartVRecords.matchingReservedBound_one_prime` discharges the hypothesis
`FrameData.MatchingReservedBound` of `lem:record:gram` (`PartVRecords/Gram.lean`) for a frame over
one prime field. This file does the same for a **block** of primes `pr i` (`i ∈ ι`): the label
alphabet is `X_𝔅 = BlockLabel pr = ∏_i 𝔽_{pr i}`, and the matching laws are the tree's block laws
`blockGraphLaw pr G = ⊗_i λ_{pr i}(G)` (`Sarkozy/PartV/BlockLaw.lean`) of the edgeless graphs
`G_{E,2}` and `G_{E,1}`.

* `blockGraphLaw_two_weight`, `blockGraphLaw_one_weight`: the block law weights are
  `[injective at every prime] · ∏_i |Inj_{pr i}|⁻¹`.
* `form_two_block`, `form_diag_block`: the cut forms at `ι` of `Π_{E_s}` and of
  `Diag_ι(Π⁽¹⁾_{E_s})`, as sums over triples `x : Fin 3 → X_𝔅` injective at every prime (the
  analogues of WP's `MatchingReserved.form_two_eq`, `form_diag_eq`).
* `quad_two_block`: on the diagonal, the two-layer sum is `D₃(𝔅) ⟨g, T_𝔅 g⟩` with
  `T_𝔅 = blockTripleMatrix` the tensor product of the disjoint-triple matrices on `∏_i 𝒯_i`
  and `D₃(𝔅) = ∏_i (p_i - 3)(p_i - 4)(p_i - 5)`.
* **`matching_reserved_block`**: `Π_{E_s} + 3/(b-3) Diag_ι(Π⁽¹⁾_{E_s}) ⪰_ι 0` whenever
  `7 ≤ b ≤ pr i` for all `i`, from `Misc.triple_block` (`-3/(b-3) I ⪯ T_𝔅`, `it:triple:block`).
* **`matchingReservedBound_block`**: hence `D.MatchingReservedBound` for every frame `D` over
  `X_𝔅` whose `E` laws are these block laws and with `D.b = b`. With `b` the least prime of the
  block this is the hypothesis of `lem:record:gram`(ii), now proved; any `7 ≤ b ≤ min p` works.
-/

namespace Sarkozy.Misc

open Finset Matrix Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing Sarkozy.PartVRecords
  Sarkozy.IndexSupport

/-! ## Labellings that are injective at every coordinate -/

section Coord

variable {K : Type} [Fintype K] [DecidableEq K] {F : K → Type} [∀ j, Fintype (F j)]
  [∀ j, DecidableEq (F j)]

/-- A labelling with values in `∏_j F_j` that is injective at every coordinate. -/
def BlockInj {O : Type} (y : O → ∀ j, F j) : Prop := ∀ j, Function.Injective fun o => y o j

instance {O : Type} [Fintype O] [DecidableEq O] (y : O → ∀ j, F j) : Decidable (BlockInj y) := by
  unfold BlockInj
  infer_instance

/-- The triple of `Fin 3 → ∏_j F_j` read off a family of triples. -/
def glue (t : ∀ j, Trip (F j)) : Fin 3 → ∀ j, F j := fun o j => (t j).1 o

omit [Fintype K] [DecidableEq K] [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)] in
theorem blockInj_glue (t : ∀ j, Trip (F j)) : BlockInj (glue t) := fun j => (t j).2

/-- The triples injective at every coordinate are the families of triples `∏_j 𝒯_j`. -/
def blockTripEquiv : (∀ j, Trip (F j)) ≃ {x : Fin 3 → ∀ j, F j // BlockInj x} where
  toFun t := ⟨glue t, blockInj_glue t⟩
  invFun x := fun j => ⟨fun o => x.1 o j, x.2 j⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_blockInj (φ : (Fin 3 → ∀ j, F j) → ℝ) :
    ∑ x, (if BlockInj x then φ x else 0) = ∑ t : ∀ j, Trip (F j), φ (glue t) := by
  rw [← sum_filter, sum_subtype (p := fun x => BlockInj x) _ (fun x => by simp) φ]
  exact (Fintype.sum_equiv blockTripEquiv _ _ fun _ => rfl).symm

omit [Fintype K] [DecidableEq K] [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)] in
theorem blockInj_split_iff (y : Fin 3 × Fin 2 → ∀ j, F j) :
    BlockInj y ↔ BlockInj (fun o => y (o, 0)) ∧
      ∀ j, DisjTriple (fun o => y (o, 0) j) (fun o => y (o, 1) j) := by
  constructor
  · intro h
    exact ⟨fun j => ((injective_split_iff fun ol => y ol j).mp (h j)).1,
      fun j => ((injective_split_iff fun ol => y ol j).mp (h j)).2⟩
  · rintro ⟨h0, h1⟩ j
    exact (injective_split_iff fun ol => y ol j).mpr ⟨h0 j, h1 j⟩

omit [Fintype K] [DecidableEq K] [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)] in
theorem blockInj_one_iff (y : Fin 3 × Fin 1 → ∀ j, F j) :
    BlockInj y ↔ BlockInj (layerOne y) :=
  forall_congr' fun j => injective_one_iff fun ol => y ol j

omit [Fintype K] [DecidableEq K] [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)] in
/-- The condition of the two-layer form, unfolded. -/
theorem blockDisj_iff (x x' : Fin 3 → ∀ j, F j) :
    (BlockInj x ∧ ∀ j, DisjTriple (fun o => x o j) (fun o => x' o j)) ↔
      BlockInj x ∧ BlockInj x' ∧ ∀ j, ∀ a b, x a j ≠ x' b j := by
  unfold DisjTriple BlockInj
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨h0, fun j => (h1 j).1, fun j => (h1 j).2⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, fun j => ⟨h1 j, h2 j⟩⟩

end Coord

/-! ## The cut forms of the block matching laws -/

theorem form_add_smul {X : Type*} (L₁ L₂ : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ) (a : ℝ)
    (G H : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (L₁ + a • L₂) G H = reservedCut.form L₁ G H + a * reservedCut.form L₂ G H :=
  rfl

section BlockLaws

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- `N₁(𝔅) = ∏_i N₁(𝔽_{pr i})`, the number of triples of `X_𝔅` injective at every prime. -/
noncomputable def N1B : ℝ := ∏ i, N1 (ZMod (pr i))

/-- `D₃(𝔅) = ∏_i (p_i - 3)(p_i - 4)(p_i - 5)`. -/
noncomputable def D3B : ℝ := ∏ i, D3 (ZMod (pr i))

/-- The weight of the two-layer block matching law. -/
theorem blockGraphLaw_two_weight
    (hne : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 2))).Nonempty)
    (y : Fin 3 × Fin 2 → BlockLabel pr) :
    (blockGraphLaw pr (matchGraph (Fin 2)) hne).weight y =
      if BlockInj y then (N1B pr * D3B pr)⁻¹ else 0 := by
  unfold blockGraphLaw
  rw [tensor_weight]
  have h : ∀ i, (graphLaw (matchGraph (Fin 2)) (hne i)).weight (fun v => y v i) =
      if Function.Injective (fun v => y v i) then
        (N1 (ZMod (pr i)) * D3 (ZMod (pr i)))⁻¹ else 0 := by
    intro i
    change (if (fun v => y v i) ∈ injLabellings (ZMod (pr i)) (matchGraph (Fin 2)) then
      1 / ((injLabellings (ZMod (pr i)) (matchGraph (Fin 2))).card : ℝ) else 0) = _
    rw [card_inj2 (hne i)]
    by_cases hy : Function.Injective (fun v => y v i)
    · rw [ite_eq_left ((mem_inj_match2_iff _).mpr hy), ite_eq_left hy, one_div]
    · rw [ite_eq_right (fun h' => hy ((mem_inj_match2_iff _).mp h')), ite_eq_right hy]
  simp only [h]
  rw [Fintype.prod_ite_zero, prod_inv_distrib, N1B, D3B, ← prod_mul_distrib]
  rfl

/-- The weight of the one-layer block matching law. -/
theorem blockGraphLaw_one_weight
    (hne : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 1))).Nonempty)
    (y : Fin 3 × Fin 1 → BlockLabel pr) :
    (blockGraphLaw pr (matchGraph (Fin 1)) hne).weight y =
      if BlockInj y then (N1B pr)⁻¹ else 0 := by
  unfold blockGraphLaw
  rw [tensor_weight]
  have h : ∀ i, (graphLaw (matchGraph (Fin 1)) (hne i)).weight (fun v => y v i) =
      if Function.Injective (fun v => y v i) then (N1 (ZMod (pr i)))⁻¹ else 0 := by
    intro i
    change (if (fun v => y v i) ∈ injLabellings (ZMod (pr i)) (matchGraph (Fin 1)) then
      1 / ((injLabellings (ZMod (pr i)) (matchGraph (Fin 1))).card : ℝ) else 0) = _
    rw [card_inj1 (hne i)]
    by_cases hy : Function.Injective (fun v => y v i)
    · rw [ite_eq_left ((mem_inj_match1_iff _).mpr hy), ite_eq_left hy, one_div]
    · rw [ite_eq_right (fun h' => hy ((mem_inj_match1_iff _).mp h')), ite_eq_right hy]
  simp only [h]
  rw [Fintype.prod_ite_zero, prod_inv_distrib, N1B]
  rfl

/-- **The cut form at `ι` of the one-layer diagonal copy on a block**:
`N₁(𝔅)⁻¹ ∑_x [x injective at every prime] G(x) H(x)`. -/
theorem form_diag_block (hne : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 1))).Nonempty)
    (φ : ZMod 6 → Fin 3) (G H : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (signedIntegral (emit (blockGraphLaw pr (matchGraph (Fin 1)) hne)
      (midDiagEmission φ)).weight) G H =
      (N1B pr)⁻¹ * ∑ x : Fin 3 → BlockLabel pr, if BlockInj x then
        G (halfRead φ x) * H (halfRead φ x) else 0 := by
  unfold ReflectionCut.form
  rw [← FiniteLaw.expect_eq_signedIntegral, expect_emit]
  unfold FiniteLaw.expect
  rw [mul_sum]
  refine Fintype.sum_equiv layerOne _ _ fun y => ?_
  change (blockGraphLaw pr (matchGraph (Fin 1)) hne).weight y *
      (G (halfRead φ (layerOne y)) * H (halfRead φ (layerOne y))) = _
  rw [blockGraphLaw_one_weight]
  by_cases hy : BlockInj y
  · rw [ite_eq_left hy, ite_eq_left ((blockInj_one_iff y).mp hy)]
  · rw [ite_eq_right hy, ite_eq_right (fun h => hy ((blockInj_one_iff y).mpr h)), zero_mul,
      mul_zero]

/-- **The cut form at `ι` of the two-layer matching component on a block**:
`(N₁(𝔅) D₃(𝔅))⁻¹ ∑_{x, x'} [x injective, x' a disjoint injective triple, at every prime]
G(x) H(x')`. -/
theorem form_two_block (hne : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 2))).Nonempty)
    (φ : ZMod 6 → Fin 3) (G H : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (signedIntegral (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne)
      (midEmission φ)).weight) G H =
      (N1B pr * D3B pr)⁻¹ * ∑ x : Fin 3 → BlockLabel pr, ∑ x' : Fin 3 → BlockLabel pr,
        if BlockInj x ∧ ∀ i, DisjTriple (fun o => x o i) (fun o => x' o i) then
          G (halfRead φ x) * H (halfRead φ x') else 0 := by
  unfold ReflectionCut.form
  rw [← FiniteLaw.expect_eq_signedIntegral, expect_emit]
  unfold FiniteLaw.expect
  rw [← Fintype.sum_prod_type', mul_sum]
  refine Fintype.sum_equiv layerSplit _ _ fun y => ?_
  have hplus : (fun v : reservedCut.Half => (y ∘ midEmission φ) v.1) =
      halfRead φ (fun o => y (o, 0)) := by
    funext v
    change y (φ v.1.1, layerFin v.1.2.2) = y (φ v.1.1, 0)
    rw [reservedCut_half_layer v]
    rfl
  have hminus : (fun v : reservedCut.Half => (y ∘ midEmission φ) (reservedCut.flip v.1)) =
      halfRead φ (fun o => y (o, 1)) := by
    funext v
    change y (φ v.1.1, layerFin (1 - v.1.2.2)) = y (φ v.1.1, 1)
    rw [reservedCut_half_layer v]
    rfl
  change (blockGraphLaw pr (matchGraph (Fin 2)) hne).weight y *
      (G (fun v : reservedCut.Half => (y ∘ midEmission φ) v.1) *
        H (fun v : reservedCut.Half => (y ∘ midEmission φ) (reservedCut.flip v.1))) =
      (N1B pr * D3B pr)⁻¹ * (if BlockInj (fun o => y (o, 0)) ∧
        ∀ i, DisjTriple (fun o => y (o, 0) i) (fun o => y (o, 1) i) then
        G (halfRead φ (fun o => y (o, 0))) * H (halfRead φ (fun o => y (o, 1))) else 0)
  rw [hplus, hminus, blockGraphLaw_two_weight]
  by_cases hy : BlockInj y
  · rw [ite_eq_left hy, ite_eq_left ((blockInj_split_iff y).mp hy)]
  · rw [ite_eq_right hy, ite_eq_right (fun h => hy ((blockInj_split_iff y).mpr h)), zero_mul,
      mul_zero]

/-- The two-layer sum is symmetric in `G, H`. -/
theorem two_block_symm (φ : ZMod 6 → Fin 3) (G H : (reservedCut.Half → BlockLabel pr) → ℝ) :
    ∑ x : Fin 3 → BlockLabel pr, ∑ x' : Fin 3 → BlockLabel pr,
      (if BlockInj x ∧ ∀ i, DisjTriple (fun o => x o i) (fun o => x' o i) then
        G (halfRead φ x) * H (halfRead φ x') else 0) =
    ∑ x : Fin 3 → BlockLabel pr, ∑ x' : Fin 3 → BlockLabel pr,
      (if BlockInj x ∧ ∀ i, DisjTriple (fun o => x o i) (fun o => x' o i) then
        H (halfRead φ x) * G (halfRead φ x') else 0) := by
  conv_lhs => rw [Finset.sum_comm]
  refine sum_congr rfl fun x' _ => sum_congr rfl fun x _ => ?_
  have hsymm : (BlockInj x ∧ ∀ i, DisjTriple (fun o => x o i) (fun o => x' o i)) ↔
      (BlockInj x' ∧ ∀ i, DisjTriple (fun o => x' o i) (fun o => x o i)) := by
    rw [blockDisj_iff, blockDisj_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, h1, fun i a b e => h3 i b a e.symm⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, h1, fun i a b e => h3 i b a e.symm⟩
  by_cases h : BlockInj x ∧ ∀ i, DisjTriple (fun o => x o i) (fun o => x' o i)
  · rw [ite_eq_left h, ite_eq_left (hsymm.mp h)]
    ring
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hsymm.mpr h'))]

omit [Fintype ι] [DecidableEq ι] in
theorem D3_pos (i : ι) (h6 : 6 ≤ pr i) : 0 < D3 (ZMod (pr i)) := by
  unfold D3
  rw [ZMod.card]
  have : (pr i - 3).descFactorial 3 ≠ 0 := by
    rw [Ne, Nat.descFactorial_eq_zero_iff_lt]
    omega
  exact_mod_cast Nat.pos_of_ne_zero this

omit [DecidableEq ι] in
theorem D3B_pos (h6 : ∀ i, 6 ≤ pr i) : 0 < D3B pr :=
  prod_pos fun i _ => D3_pos pr i (h6 i)

omit [DecidableEq ι] in
theorem N1B_pos (hne : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 1))).Nonempty) :
    0 < N1B pr :=
  prod_pos fun i _ => by
    rw [← card_inj1 (hne i)]
    exact_mod_cast (hne i).card_pos

/-- The block tensor `T_𝔅` applied to `g`: `(T_𝔅 g)(t) = D₃(𝔅)⁻¹ ∑_{t' disjoint from t} g(t')`. -/
theorem blockTripleMatrix_mulVec (g : (∀ i, Trip (ZMod (pr i))) → ℝ) (t : ∀ i, Trip (ZMod (pr i))) :
    (blockTripleMatrix (fun i => ZMod (pr i)) *ᵥ g) t =
      (D3B pr)⁻¹ * ∑ t' : ∀ i, Trip (ZMod (pr i)),
        if ∀ i, ∀ a b, (t i).1 a ≠ (t' i).1 b then g t' else 0 := by
  simp only [mulVec, dotProduct, blockTripleMatrix, piKron_apply, tripleMatrix]
  rw [mul_sum]
  refine sum_congr rfl fun t' _ => ?_
  rw [Fintype.prod_ite_zero]
  by_cases h : ∀ i, ∀ a b, (t i).1 a ≠ (t' i).1 b
  · rw [ite_eq_left h, ite_eq_left h, prod_inv_distrib]
    rfl
  · rw [ite_eq_right h, ite_eq_right h, zero_mul, mul_zero]

/-- **The two-layer sum on the diagonal is `D₃(𝔅) ⟨g, T_𝔅 g⟩`**, with `g(t) = G(x_t)` for the
triple `x_t` of the family `t ∈ ∏_i 𝒯_i`. -/
theorem quad_two_block (h6 : ∀ i, 6 ≤ pr i) (φ : ZMod 6 → Fin 3)
    (G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    ∑ x : Fin 3 → BlockLabel pr, ∑ x' : Fin 3 → BlockLabel pr,
      (if BlockInj x ∧ ∀ i, DisjTriple (fun o => x o i) (fun o => x' o i) then
        G (halfRead φ x) * G (halfRead φ x') else 0) =
      D3B pr * ((fun t => G (halfRead φ (glue t))) ⬝ᵥ
        (blockTripleMatrix (fun i => ZMod (pr i)) *ᵥ fun t => G (halfRead φ (glue t)))) := by
  have h1 : ∀ x : Fin 3 → BlockLabel pr, ∑ x' : Fin 3 → BlockLabel pr,
      (if BlockInj x ∧ ∀ i, DisjTriple (fun o => x o i) (fun o => x' o i) then
        G (halfRead φ x) * G (halfRead φ x') else 0) =
      if BlockInj x then G (halfRead φ x) * ∑ x' : Fin 3 → BlockLabel pr,
        (if BlockInj x' then
          (if ∀ i, ∀ a b, x a i ≠ x' b i then G (halfRead φ x') else 0) else 0)
      else 0 := by
    intro x
    by_cases hx : BlockInj x
    · rw [ite_eq_left hx, mul_sum]
      refine sum_congr rfl fun x' _ => ?_
      by_cases hx' : BlockInj x'
      · rw [ite_eq_left hx']
        by_cases hd : ∀ i, ∀ a b, x a i ≠ x' b i
        · rw [ite_eq_left ((blockDisj_iff x x').mpr ⟨hx, hx', hd⟩), ite_eq_left hd]
        · rw [ite_eq_right (fun h => hd ((blockDisj_iff x x').mp h).2.2), ite_eq_right hd,
            mul_zero]
      · rw [ite_eq_right (fun h => hx' ((blockDisj_iff x x').mp h).2.1), ite_eq_right hx',
          mul_zero]
    · rw [ite_eq_right hx]
      exact sum_eq_zero fun x' _ => ite_eq_right fun h => hx h.1
  rw [sum_congr rfl fun x _ => h1 x, sum_blockInj]
  simp only [sum_blockInj]
  simp only [dotProduct, blockTripleMatrix_mulVec]
  rw [mul_sum]
  refine sum_congr rfl fun t _ => ?_
  have hD := (D3B_pos pr h6).ne'
  field_simp
  rfl

/-- The one-layer sum on the diagonal is `⟨g, g⟩`. -/
theorem diag_block_eq (φ : ZMod 6 → Fin 3) (G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    ∑ x : Fin 3 → BlockLabel pr, (if BlockInj x then G (halfRead φ x) * G (halfRead φ x) else 0) =
      (fun t => G (halfRead φ (glue t))) ⬝ᵥ (fun t => G (halfRead φ (glue t))) := by
  rw [sum_blockInj]
  rfl

/-- **`it:triple:block` in the form used by `lem:record:gram`(ii)**: on a block of primes
`pr i ≥ b ≥ 7`, `Π_{E_s} + 3/(b-3) Diag_ι(Π⁽¹⁾_{E_s}) ⪰_ι 0` for the block laws of `G_{E,2}` and
`G_{E,1}`, for every pattern `φ` (in particular `φ = matching s`). -/
theorem matching_reserved_block (b : ℕ) (hb : 7 ≤ b) (hpr : ∀ i, b ≤ pr i)
    (hne2 : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 2))).Nonempty)
    (hne1 : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 1))).Nonempty)
    (φ : ZMod 6 → Fin 3) :
    reservedCut.Positive
      (signedIntegral (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne2) (midEmission φ)).weight +
        (3 / ((b : ℝ) - 3)) •
          signedIntegral (emit (blockGraphLaw pr (matchGraph (Fin 1)) hne1)
            (midDiagEmission φ)).weight) := by
  have h6 : ∀ i, 6 ≤ pr i := fun i => by have := hpr i; omega
  have hN := N1B_pos pr hne1
  have hD := D3B_pos pr h6
  constructor
  · intro G H
    rw [form_add_smul, form_add_smul, form_two_block, form_two_block, form_diag_block,
      form_diag_block, two_block_symm]
    congr 3
    refine sum_congr rfl fun x _ => ?_
    by_cases hx : BlockInj x
    · rw [ite_eq_left hx, ite_eq_left hx]
      ring
    · rw [ite_eq_right hx, ite_eq_right hx]
  · intro G
    rw [form_add_smul, form_two_block, form_diag_block, quad_two_block pr h6, diag_block_eq]
    set g : (∀ i, Trip (ZMod (pr i))) → ℝ := fun t => G (halfRead φ (glue t))
    have hpsd := (triple_block (fun i => ZMod (pr i)) b hb
      (fun i => by rw [ZMod.card]; exact hpr i)).1
    have h0 := hpsd.dotProduct_mulVec_nonneg g
    simp only [star_trivial, add_mulVec, dotProduct_add, smul_mulVec, one_mulVec,
      dotProduct_smul, smul_eq_mul] at h0
    have e : (N1B pr * D3B pr)⁻¹ *
          (D3B pr * (g ⬝ᵥ (blockTripleMatrix (fun i => ZMod (pr i)) *ᵥ g))) +
        3 / ((b : ℝ) - 3) * ((N1B pr)⁻¹ * (g ⬝ᵥ g)) =
        (N1B pr)⁻¹ * (g ⬝ᵥ (blockTripleMatrix (fun i => ZMod (pr i)) *ᵥ g) +
          3 / ((b : ℝ) - 3) * (g ⬝ᵥ g)) := by
      field_simp
    rw [e]
    exact mul_nonneg (inv_nonneg.mpr hN.le) h0

/-- **`MatchingReservedBound` for a frame on a block of primes** (the hypothesis of
`lem:record:gram`(ii), `PartVRecords/Gram.lean`): if the frame's `E` laws are the block laws
`⊗_i λ_{pr i}(G_{E,2})`, `⊗_i λ_{pr i}(G_{E,1})` and `D.b = b` with `7 ≤ b ≤ pr i` for all `i`
(e.g. `b` the least prime of the block), the hypothesis holds. -/
theorem matchingReservedBound_block (D : FrameData (BlockLabel pr)) (b : ℕ) (hb : 7 ≤ b)
    (hpr : ∀ i, b ≤ pr i)
    (hne2 : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 2))).Nonempty)
    (hne1 : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 1))).Nonempty)
    (h2 : D.F.two .E = blockGraphLaw pr (matchGraph (Fin 2)) hne2)
    (h1 : D.F.one .E = blockGraphLaw pr (matchGraph (Fin 1)) hne1) (hbD : D.b = b) :
    D.MatchingReservedBound := by
  intro s
  change reservedCut.Positive (signedIntegral (emit (D.F.two .E)
    (midEmission (matching s))).weight + (3 / (D.b - 3)) •
      signedIntegral (emit (D.F.one .E) (midDiagEmission (matching s))).weight)
  rw [h2, h1, hbD]
  exact matching_reserved_block pr b hb hpr hne2 hne1 (matching s)

end BlockLaws

/-! ## Non-vacuity -/

/-- The matching graphs have injective labellings over every field with at least six elements, so
the nonemptiness hypotheses of `matching_reserved_block` hold at every prime `p ≥ 6`. -/
theorem injLabellings_match_nonempty (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (h6 : 6 ≤ Fintype.card F) :
    (injLabellings F (matchGraph (Fin 2))).Nonempty ∧
      (injLabellings F (matchGraph (Fin 1))).Nonempty := by
  obtain ⟨e⟩ : Nonempty (Fin 3 × Fin 2 ↪ F) := Function.Embedding.nonempty_of_card_le
    (by simpa using h6)
  refine ⟨⟨e, (mem_inj_match2_iff _).mpr e.injective⟩, ?_⟩
  obtain ⟨e1⟩ : Nonempty (Fin 3 × Fin 1 ↪ F) := Function.Embedding.nonempty_of_card_le
    (by simp only [Fintype.card_prod, Fintype.card_fin]; omega)
  exact ⟨e1, (mem_inj_match1_iff _).mpr e1.injective⟩

/-- The block `{7, 11}`. -/
def toyPrimes : Fin 2 → ℕ := ![7, 11]

instance toyPrimes_prime (i : Fin 2) : Fact (toyPrimes i).Prime :=
  ⟨by fin_cases i <;> norm_num [toyPrimes]⟩

/-- Non-vacuity of `matching_reserved_block`: its hypotheses hold on the block `{7, 11}` with
`b = 7`. -/
example (φ : ZMod 6 → Fin 3) :
    reservedCut.Positive
      (signedIntegral (emit (blockGraphLaw toyPrimes (matchGraph (Fin 2))
        (fun i => (injLabellings_match_nonempty (ZMod (toyPrimes i))
          (by rw [ZMod.card]; fin_cases i <;> norm_num [toyPrimes])).1)) (midEmission φ)).weight +
        (3 / ((7 : ℕ) - 3 : ℝ)) •
          signedIntegral (emit (blockGraphLaw toyPrimes (matchGraph (Fin 1))
            (fun i => (injLabellings_match_nonempty (ZMod (toyPrimes i))
              (by rw [ZMod.card]; fin_cases i <;> norm_num [toyPrimes])).2))
            (midDiagEmission φ)).weight) :=
  matching_reserved_block toyPrimes 7 le_rfl (fun i => by fin_cases i <;> norm_num [toyPrimes])
    _ _ φ

end Sarkozy.Misc
