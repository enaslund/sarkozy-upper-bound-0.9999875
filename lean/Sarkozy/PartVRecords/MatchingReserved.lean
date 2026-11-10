module

public import Sarkozy.PartVRecords.Gram
public import Sarkozy.TraceMixing.DisjointTripleOrdered

@[expose] public section

/-!
# The matching components at `ι`, at one prime (`sec:frontier:empty-triple-negative`(c))

`paper/sections/20c_middle_frame.tex`, proof of `lem:record:gram`(ii): "the component `Π_{E_s}` is
uniform on two disjoint injective triples, and its cut operator at `ι` relative to its actual half
law, the uniform law on injective triples, which is the half law of `Π⁽¹⁾_{E_s}`, is the
disjoint-triple operator at each prime; […] Hence `Π_{E_s} + 3/(b-3) Diag_ι(Π⁽¹⁾_{E_s}) ⪰_ι 0`."

**Proved here at one prime** (a block of one prime `p`, `p ≥ 6`): with the graph laws
`λ_p(G_{E,2})` and `λ_p(G_{E,1})` (uniform on the injective labellings of the edgeless graphs),
`Π_{E_s} + 3/(p - 3) Diag_ι(Π⁽¹⁾_{E_s}) ⪰_ι 0` (`matching_reserved_one_prime`). The cut form of
`Π_{E_s}` at `ι` is `N₁⁻¹ ∑_x [x injective] f(x) (T f)(x)` with `T` WP-S's disjoint-triple operator
(`form_two_eq`), that of the diagonal copy is `N₁⁻¹ ∑_x [x injective] f(x)²` (`form_diag_eq`), and
WP-S's `tripleOp_ge` (`T ⪰ -3/(n-3)`) concludes.

**Not proved:** the block statement (the tensor of the one-prime bounds over the primes of a
block, whose spectra lie in `[-3/(b-3), 1]`), which is the hypothesis `MatchingReservedBound` of
`Sarkozy.PartVRecords.Gram` for blocks of several primes.
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The plus half of `ι` carries layer `0`. -/
theorem reservedCut_half_layer (v : reservedCut.Half) : v.1.2.2 = 0 := by
  have h := v.2
  change v.1 ∈ (Finset.univ : Finset Chamber).product
    ((Finset.univ : Finset Chamber).product layerCut.half) at h
  have h2 : v.1.2.2 ∈ layerCut.half := (Finset.mem_product.mp (Finset.mem_product.mp h).2).2
  change v.1.2.2 ∈ ({0} : Finset Layer) at h2
  exact Finset.mem_singleton.mp h2

/-- The reflection of `ι` changes the layer. -/
theorem reservedCut_flip_apply (v : Slot) : reservedCut.flip v = (v.1, v.2.1, 1 - v.2.2) := rfl

/-- The reading of a half configuration from the labels of the three objects in one layer. -/
def halfRead (φ : ZMod 6 → Fin 3) (x : Fin 3 → F) : reservedCut.Half → F := fun v => x (φ v.1.1)

/-- Two layers of three objects, as two triples. -/
def layerSplit : (Fin 3 × Fin 2 → F) ≃ (Fin 3 → F) × (Fin 3 → F) where
  toFun y := (fun o => y (o, 0), fun o => y (o, 1))
  invFun p := fun ol => if ol.2 = 0 then p.1 ol.1 else p.2 ol.1
  left_inv y := by
    funext ⟨o, l⟩
    fin_cases l <;> simp
  right_inv p := by
    obtain ⟨x, x'⟩ := p
    simp

/-- One layer of three objects, as a triple. -/
def layerOne : (Fin 3 × Fin 1 → F) ≃ (Fin 3 → F) where
  toFun y := fun o => y (o, 0)
  invFun x := fun ol => x ol.1
  left_inv y := by
    funext ⟨o, l⟩
    have : l = 0 := Subsingleton.elim _ _
    subst this
    rfl
  right_inv x := rfl

omit [Field F] [Fintype F] [DecidableEq F] in
/-- A two-layer labelling is injective iff its layer-`0` triple is injective and its layer-`1`
triple is a disjoint injective triple. -/
theorem injective_split_iff (y : Fin 3 × Fin 2 → F) :
    Function.Injective y ↔
      Function.Injective (fun o => y (o, 0)) ∧
        DisjTriple (fun o => y (o, 0)) (fun o => y (o, 1)) := by
  constructor
  · intro h
    refine ⟨fun a b hab => ?_, fun a b hab => ?_, fun i j e => ?_⟩
    · have := h hab
      simp only [Prod.mk.injEq] at this
      exact this.1
    · have := h hab
      simp only [Prod.mk.injEq] at this
      exact this.1
    · have := h e
      simp only [Prod.mk.injEq] at this
      exact absurd this.2 (by decide)
  · rintro ⟨h0, h1, hd⟩ ⟨o, l⟩ ⟨o', l'⟩ e
    fin_cases l <;> fin_cases l'
    · have := h0 (show y (o, 0) = y (o', 0) from e)
      rw [this]
    · exact absurd e (hd o o')
    · exact absurd e.symm (hd o' o)
    · have := h1 (show y (o, 1) = y (o', 1) from e)
      rw [this]

theorem mem_inj_match2_iff (y : Fin 3 × Fin 2 → F) :
    y ∈ injLabellings F (matchGraph (Fin 2)) ↔ Function.Injective y := by
  rw [mem_injLabellings_iff_feasible]
  constructor
  · rintro ⟨h, -⟩ a b hab
    exact h a (mem_univ _) b (mem_univ _) hab
  · intro h
    refine ⟨fun a _ b _ hab => h hab, fun e he => ?_⟩
    simp [matchGraph] at he

theorem mem_inj_match1_iff (y : Fin 3 × Fin 1 → F) :
    y ∈ injLabellings F (matchGraph (Fin 1)) ↔ Function.Injective y := by
  rw [mem_injLabellings_iff_feasible]
  constructor
  · rintro ⟨h, -⟩ a b hab
    exact h a (mem_univ _) b (mem_univ _) hab
  · intro h
    refine ⟨fun a _ b _ hab => h hab, fun e he => ?_⟩
    simp [matchGraph] at he

omit [Field F] [Fintype F] [DecidableEq F] in
theorem injective_one_iff (y : Fin 3 × Fin 1 → F) :
    Function.Injective y ↔ Function.Injective (layerOne y) := by
  constructor
  · intro h a b hab
    have := h hab
    simp only [Prod.mk.injEq] at this
    exact this.1
  · intro h ⟨o, l⟩ ⟨o', l'⟩ e
    have hl : l = 0 := Subsingleton.elim _ _
    have hl' : l' = 0 := Subsingleton.elim _ _
    subst hl hl'
    rw [h e]

/-- The number of injective triples. -/
noncomputable def N1 (F : Type) [Fintype F] [DecidableEq F] : ℝ :=
  ∑ x : Fin 3 → F, if Function.Injective x then (1 : ℝ) else 0

theorem card_inj1 (hne : (injLabellings F (matchGraph (Fin 1))).Nonempty) :
    ((injLabellings F (matchGraph (Fin 1))).card : ℝ) = N1 F := by
  have _hne := hne
  have h1 : ((injLabellings F (matchGraph (Fin 1))).card : ℝ) =
      ∑ y : Fin 3 × Fin 1 → F, if y ∈ injLabellings F (matchGraph (Fin 1)) then (1 : ℝ) else 0 := by
    rw [sum_boole]
    congr 2
    ext y
    simp
  rw [h1, N1]
  refine Fintype.sum_equiv layerOne _ _ fun y => ?_
  by_cases hy : Function.Injective y
  · rw [ite_eq_left ((mem_inj_match1_iff y).mpr hy), ite_eq_left ((injective_one_iff y).mp hy)]
  · rw [ite_eq_right (fun h => hy ((mem_inj_match1_iff y).mp h)),
      ite_eq_right (fun h => hy ((injective_one_iff y).mpr h))]

/-- **The cut form at `ι` of the one-layer diagonal copy**: `N₁⁻¹ ∑_x [x inj] G(x) H(x)`. -/
theorem form_diag_eq (hne : (injLabellings F (matchGraph (Fin 1))).Nonempty) (φ : ZMod 6 → Fin 3)
    (G H : (reservedCut.Half → F) → ℝ) :
    reservedCut.form (signedIntegral (emit (graphLaw (matchGraph (Fin 1)) hne)
      (midDiagEmission φ)).weight) G H =
      (N1 F)⁻¹ * ∑ x : Fin 3 → F, if Function.Injective x then
        G (halfRead φ x) * H (halfRead φ x) else 0 := by
  have hcard := card_inj1 hne
  unfold ReflectionCut.form
  rw [← FiniteLaw.expect_eq_signedIntegral, expect_emit]
  unfold FiniteLaw.expect
  rw [mul_sum]
  refine Fintype.sum_equiv layerOne _ _ fun y => ?_
  change (if y ∈ injLabellings F (matchGraph (Fin 1)) then
      1 / ((injLabellings F (matchGraph (Fin 1))).card : ℝ) else 0) *
      (G (halfRead φ (layerOne y)) * H (halfRead φ (layerOne y))) = _
  rw [hcard]
  by_cases hy : Function.Injective y
  · rw [ite_eq_left ((mem_inj_match1_iff y).mpr hy), ite_eq_left ((injective_one_iff y).mp hy)]
    ring
  · rw [ite_eq_right (fun h => hy ((mem_inj_match1_iff y).mp h)),
      ite_eq_right (fun h => hy ((injective_one_iff y).mpr h))]
    ring

/-- `D₃ = (n - 3)(n - 4)(n - 5)`, the number of disjoint triples of an injective triple. -/
noncomputable def D3 (F : Type) [Fintype F] : ℝ := ((Fintype.card F - 3).descFactorial 3 : ℝ)

omit [Field F] in
theorem sum_disj (x : Fin 3 → F) (hx : Function.Injective x) :
    ∑ x' : Fin 3 → F, (if DisjTriple x x' then (1 : ℝ) else 0) = D3 F := by
  rw [sum_boole, card_disjTriple hx, D3]

theorem card_inj2 (hne : (injLabellings F (matchGraph (Fin 2))).Nonempty) :
    ((injLabellings F (matchGraph (Fin 2))).card : ℝ) = N1 F * D3 F := by
  have _hne := hne
  have h1 : ((injLabellings F (matchGraph (Fin 2))).card : ℝ) =
      ∑ y : Fin 3 × Fin 2 → F, if y ∈ injLabellings F (matchGraph (Fin 2)) then (1 : ℝ) else 0 := by
    rw [sum_boole]
    congr 2
    ext y
    simp
  have h2 : ∑ y : Fin 3 × Fin 2 → F,
      (if y ∈ injLabellings F (matchGraph (Fin 2)) then (1 : ℝ) else 0) =
      ∑ p : (Fin 3 → F) × (Fin 3 → F),
        (if Function.Injective p.1 ∧ DisjTriple p.1 p.2 then (1 : ℝ) else 0) := by
    refine Fintype.sum_equiv layerSplit _ _ fun y => ?_
    change _ = (if Function.Injective (fun o => y (o, 0)) ∧
      DisjTriple (fun o => y (o, 0)) (fun o => y (o, 1)) then (1 : ℝ) else 0)
    by_cases hy : Function.Injective y
    · rw [ite_eq_left ((mem_inj_match2_iff y).mpr hy), ite_eq_left ((injective_split_iff y).mp hy)]
    · rw [ite_eq_right (fun h => hy ((mem_inj_match2_iff y).mp h)),
        ite_eq_right (fun h => hy ((injective_split_iff y).mpr h))]
  rw [h1, h2, Fintype.sum_prod_type, N1, sum_mul]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : Function.Injective x
  · rw [ite_eq_left hx, one_mul, ← sum_disj x hx]
    refine sum_congr rfl fun x' _ => ?_
    by_cases hd : DisjTriple x x'
    · rw [ite_eq_left (show Function.Injective x ∧ DisjTriple x x' from ⟨hx, hd⟩), ite_eq_left hd]
    · rw [ite_eq_right (show ¬ (Function.Injective x ∧ DisjTriple x x') from fun h => hd h.2),
        ite_eq_right hd]
  · rw [ite_eq_right hx, zero_mul]
    exact sum_eq_zero fun x' _ => ite_eq_right fun h => hx h.1

/-- **The cut form at `ι` of the two-layer matching component**:
`(N₁ D₃)⁻¹ ∑_{x, x'} [x inj, x' disjoint from x] G(x) H(x')`. -/
theorem form_two_eq (hne : (injLabellings F (matchGraph (Fin 2))).Nonempty) (φ : ZMod 6 → Fin 3)
    (G H : (reservedCut.Half → F) → ℝ) :
    reservedCut.form (signedIntegral (emit (graphLaw (matchGraph (Fin 2)) hne)
      (midEmission φ)).weight) G H =
      (N1 F * D3 F)⁻¹ * ∑ x : Fin 3 → F, ∑ x' : Fin 3 → F,
        if Function.Injective x ∧ DisjTriple x x' then G (halfRead φ x) * H (halfRead φ x')
        else 0 := by
  have hcard := card_inj2 hne
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
  change (graphLaw (matchGraph (Fin 2)) hne).weight y *
      (G (fun v : reservedCut.Half => (y ∘ midEmission φ) v.1) *
        H (fun v : reservedCut.Half => (y ∘ midEmission φ) (reservedCut.flip v.1))) =
      (N1 F * D3 F)⁻¹ * (if Function.Injective (fun o => y (o, 0)) ∧
        DisjTriple (fun o => y (o, 0)) (fun o => y (o, 1)) then
        G (halfRead φ (fun o => y (o, 0))) * H (halfRead φ (fun o => y (o, 1))) else 0)
  rw [hplus, hminus]
  change (if y ∈ injLabellings F (matchGraph (Fin 2)) then
      1 / ((injLabellings F (matchGraph (Fin 2))).card : ℝ) else 0) * _ = _
  rw [hcard]
  by_cases hy : Function.Injective y
  · rw [ite_eq_left ((mem_inj_match2_iff y).mpr hy), ite_eq_left ((injective_split_iff y).mp hy)]
    ring
  · rw [ite_eq_right (fun h => hy ((mem_inj_match2_iff y).mp h)),
      ite_eq_right (fun h => hy ((injective_split_iff y).mpr h))]
    ring

omit [Field F] in
theorem S2_symm (φ : ZMod 6 → Fin 3) (G H : (reservedCut.Half → F) → ℝ) :
    ∑ x : Fin 3 → F, ∑ x' : Fin 3 → F,
      (if Function.Injective x ∧ DisjTriple x x' then G (halfRead φ x) * H (halfRead φ x') else 0) =
    ∑ x : Fin 3 → F, ∑ x' : Fin 3 → F,
      (if Function.Injective x ∧ DisjTriple x x' then H (halfRead φ x) * G (halfRead φ x')
        else 0) := by
  conv_lhs => rw [Finset.sum_comm]
  refine sum_congr rfl fun x' _ => sum_congr rfl fun x _ => ?_
  have hsymm : (Function.Injective x ∧ DisjTriple x x') ↔
      (Function.Injective x' ∧ DisjTriple x' x) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, h1, fun i j e => h3 j i e.symm⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, h1, fun i j e => h3 j i e.symm⟩
  by_cases h : Function.Injective x ∧ DisjTriple x x'
  · rw [ite_eq_left h, ite_eq_left (hsymm.mp h)]
    ring
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hsymm.mpr h'))]

/-- **`sec:frontier:empty-triple-negative`(c) at one prime, in the form used by
`lem:record:gram`(ii)**: `Π_{E_s} + 3/(q - 3) Diag_ι(Π⁽¹⁾_{E_s}) ⪰_ι 0` for the graph laws of
`G_{E,2}` and `G_{E,1}` at one prime with `q ≥ 6`. -/
theorem matching_reserved_one_prime (h6 : 6 ≤ Fintype.card F)
    (hne2 : (injLabellings F (matchGraph (Fin 2))).Nonempty)
    (hne1 : (injLabellings F (matchGraph (Fin 1))).Nonempty) (s : Fin 2) :
    reservedCut.Positive
      (signedIntegral (emit (graphLaw (matchGraph (Fin 2)) hne2)
          (midEmission (matching s))).weight +
        (3 / ((Fintype.card F : ℝ) - 3)) •
          signedIntegral (emit (graphLaw (matchGraph (Fin 1)) hne1)
            (midDiagEmission (matching s))).weight) := by
  have hq : (6 : ℝ) ≤ Fintype.card F := by exact_mod_cast h6
  have hN1 : 0 < N1 F := by
    rw [← card_inj1 hne1]
    exact_mod_cast hne1.card_pos
  have hD3 : 0 < D3 F := by
    have h := card_inj2 hne2
    have hpos : (0 : ℝ) < ((injLabellings F (matchGraph (Fin 2))).card : ℝ) := by
      exact_mod_cast hne2.card_pos
    rw [h] at hpos
    exact pos_of_mul_pos_right hpos hN1.le
  set φ := matching s
  have hform : ∀ G H : (reservedCut.Half → F) → ℝ, reservedCut.form
      (signedIntegral (emit (graphLaw (matchGraph (Fin 2)) hne2) (midEmission φ)).weight +
        (3 / ((Fintype.card F : ℝ) - 3)) • signedIntegral (emit (graphLaw (matchGraph (Fin 1)) hne1)
          (midDiagEmission φ)).weight) G H =
      reservedCut.form (signedIntegral (emit (graphLaw (matchGraph (Fin 2)) hne2)
        (midEmission φ)).weight) G H +
      (3 / ((Fintype.card F : ℝ) - 3)) * reservedCut.form (signedIntegral
        (emit (graphLaw (matchGraph (Fin 1)) hne1) (midDiagEmission φ)).weight) G H :=
    fun G H => rfl
  constructor
  · intro G H
    rw [hform, hform, form_two_eq, form_two_eq, form_diag_eq, form_diag_eq, S2_symm φ G H]
    have e : ∑ x : Fin 3 → F, (if Function.Injective x then G (halfRead φ x) * H (halfRead φ x)
        else 0) = ∑ x : Fin 3 → F, (if Function.Injective x then H (halfRead φ x) *
          G (halfRead φ x) else 0) := sum_congr rfl fun x _ => by split_ifs <;> ring
    rw [e]
  · intro G
    rw [hform, form_two_eq, form_diag_eq]
    set f : (Fin 3 → F) → ℝ := fun x => G (halfRead φ x)
    have hT := tripleOp_ge h6 f
    have e1 : ∑ x : Fin 3 → F, ∑ x' : Fin 3 → F, (if Function.Injective x ∧ DisjTriple x x' then
        G (halfRead φ x) * G (halfRead φ x') else 0) =
        D3 F * ∑ x, (if Function.Injective x then f x * tripleOp f x else 0) := by
      rw [mul_sum]
      refine sum_congr rfl fun x _ => ?_
      by_cases hx : Function.Injective x
      · rw [ite_eq_left hx]
        have ht : tripleOp f x = (D3 F)⁻¹ * ∑ x', if DisjTriple x x' then f x' else 0 := rfl
        have hD3ne : D3 F ≠ 0 := hD3.ne'
        have hR : D3 F * (f x * ((D3 F)⁻¹ * ∑ x', if DisjTriple x x' then f x' else 0)) =
            ∑ x', (if DisjTriple x x' then f x * f x' else 0) := by
          rw [mul_sum, mul_sum, mul_sum]
          refine sum_congr rfl fun x' _ => ?_
          split_ifs
          · field_simp
          · simp
        rw [ht, hR]
        refine sum_congr rfl fun x' _ => ?_
        by_cases hd : DisjTriple x x'
        · rw [ite_eq_left (show Function.Injective x ∧ DisjTriple x x' from ⟨hx, hd⟩),
            ite_eq_left hd]
        · rw [ite_eq_right (show ¬ (Function.Injective x ∧ DisjTriple x x') from fun h => hd h.2),
            ite_eq_right hd]
      · rw [ite_eq_right hx, mul_zero]
        exact sum_eq_zero fun x' _ => ite_eq_right fun h => hx h.1
    have e2 : ∑ x : Fin 3 → F, (if Function.Injective x then
        G (halfRead φ x) * G (halfRead φ x) else 0) =
        ∑ x, (if Function.Injective x then f x ^ 2 else 0) := by
      refine sum_congr rfl fun x _ => ?_
      split_ifs <;> ring
    rw [e1, e2]
    have hq3 : 0 < (Fintype.card F : ℝ) - 3 := by linarith
    have key : 0 ≤ ∑ x, (if Function.Injective x then f x * tripleOp f x else 0) +
        3 / ((Fintype.card F : ℝ) - 3) * ∑ x, (if Function.Injective x then f x ^ 2 else 0) := by
      have : -(3 / ((Fintype.card F : ℝ) - 3)) *
          ∑ x, (if Function.Injective x then f x ^ 2 else 0) =
          -(3 / ((Fintype.card F : ℝ) - 3) * ∑ x, (if Function.Injective x then f x ^ 2 else 0)) :=
        by ring
      linarith
    have e3 : (N1 F * D3 F)⁻¹ * (D3 F * ∑ x, (if Function.Injective x then f x * tripleOp f x
        else 0)) + 3 / ((Fintype.card F : ℝ) - 3) * ((N1 F)⁻¹ *
          ∑ x, (if Function.Injective x then f x ^ 2 else 0)) =
        (N1 F)⁻¹ * (∑ x, (if Function.Injective x then f x * tripleOp f x else 0) +
          3 / ((Fintype.card F : ℝ) - 3) * ∑ x, (if Function.Injective x then f x ^ 2 else 0)) := by
      field_simp
    rw [e3]
    exact mul_nonneg (inv_nonneg.mpr hN1.le) key

/-- **`MatchingReservedBound` for a frame at one prime**: if the frame's `E` laws are the graph laws
of `G_{E,2}` and `G_{E,1}` over a field with `q ≥ 6` elements and `b = q`, the hypothesis of
`lem:record:gram` holds. -/
theorem matchingReservedBound_one_prime (D : FrameData F) (h6 : 6 ≤ Fintype.card F)
    (hne2 : (injLabellings F (matchGraph (Fin 2))).Nonempty)
    (hne1 : (injLabellings F (matchGraph (Fin 1))).Nonempty)
    (h2 : D.F.two .E = graphLaw (matchGraph (Fin 2)) hne2)
    (h1 : D.F.one .E = graphLaw (matchGraph (Fin 1)) hne1) (hb : D.b = Fintype.card F) :
    D.MatchingReservedBound := by
  intro s
  change reservedCut.Positive (signedIntegral (emit (D.F.two .E)
    (midEmission (matching s))).weight + (3 / (D.b - 3)) •
      signedIntegral (emit (D.F.one .E) (midDiagEmission (matching s))).weight)
  rw [h2, h1, hb]
  exact matching_reserved_one_prime h6 hne2 hne1 s

end Sarkozy.PartVRecords
