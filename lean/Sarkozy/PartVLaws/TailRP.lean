module

public import Sarkozy.PartVLaws.UpperGraphs

@[expose] public section

/-!
# The tail law is reflection positive (`lem:tail-law`(ii))

`paper/sections/27_tail_index.tex`, `lem:tail-law`; `paper/sections/25_upper_reference.tex`,
`lem:upper-reference-rp`, `def:record:upper-bands`(d),(e).

**The supports.** For the paper's field laws (uniform laws on `Inj_p(G_{φ₀φ₁,j})` at one prime,
`graphLaws`, and their tensor over a block of primes, `blockLaws`) the hypotheses of
`upperDatumHyp_of` hold:
* `graphLaws_graphInv`, `blockLaws_graphInv`: invariance under graph automorphisms;
* `graphLaws_suppExt`, `blockLaws_suppExt`: the extension property, under Weil's bound at every
  prime `p ≥ 2²⁰` of the block (`exists_extension`: the fold rows restricted to two rows are
  feasible matching labellings, `typeF_typeE_agree'`, and they extend because the matching graphs
  have degree at most `8`).

Hence `tail_upperDatumHyp` and `block_upperDatumHyp`: the row data form five-type data.

**The tail datum.** `tailWeightsOK`: the fifty tail weights satisfy `WeightsOK` with the ordinary
and reserved inputs and the caps of `def:record:upper-bands`(e); this is V1's exact check
`tailDatum_gates` (105 inequalities), cast to the reals, together with the positivity of the
weights.

**Headlines.**
* **`tailLaw_familyPositive`** (`lem:tail-law`(ii), (R2) part): at every prime `p ≥ 2²⁰` (so at
  every `p ≥ P₄`), under H1, if the inputs of the tail datum are valid on `{p}` (`ValidInputs`,
  (V1)–(V3); this is `lem:tail-law`(i), a spectral input, as a hypothesis), the tail law is
  reflection positive at every cut of `𝔉`.
* `tailLaw_R1R3`: with V1's results, the tail law is a probability law, reflection positive at
  every cut of `𝔉`, invariant under the square-affine maps, with uniform one-slot marginals
  (`lem:tail-law`(ii) except admissibility).
* **`upperBlockReference_familyPositive`** (`lem:upper-reference-rp`(i) for the paper's block
  laws): the same for an upper block of primes `≥ 2²⁰` with weights satisfying `WeightsOK` and
  valid inputs.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord

/-! ## Agreement of `F` and `E` on two rows -/

theorem typeF_typeE_agree' : ∀ j x y : Fin 3, j ≠ 1 → x ≠ j → y ≠ j →
    typeF.rel x y = typeE.rel x y ∧ typeF.fwd x y = typeE.fwd x y := by
  unfold typeF typeE
  decide

theorem edge_agree_left {O Λ : Type} (c : FieldType O) {j : Fin 3} (hj : j ≠ 1)
    (a b : Fin 3 × O × Λ) (ha : a.1 ≠ j) (hb : b.1 ≠ j) :
    twoLayerEdge typeE c a b = twoLayerEdge typeF c a b := by
  have h := typeF_typeE_agree' j a.1 b.1 hj ha hb
  simp only [twoLayerEdge, h.1, h.2]

theorem edge_agree_right {O Λ : Type} (c : FieldType O) {j : Fin 3} (hj : j ≠ 1)
    (a b : O × Fin 3 × Λ) (ha : a.2.1 ≠ j) (hb : b.2.1 ≠ j) :
    twoLayerEdge c typeE a b = twoLayerEdge c typeF a b := by
  have h := typeF_typeE_agree' j a.2.1 b.2.1 hj ha hb
  simp only [twoLayerEdge, h.1, h.2]

/-! ## Degrees and sizes -/

theorem card_obj_le (f : FType) : Fintype.card f.Obj ≤ 6 := by
  cases f <;> decide

theorem degE_left_two (f : FType) (v : Fin 3 × f.Obj × Fin 2) :
    nbrCount (fieldGraph .E f (Fin 2)) univ v ≤ 8 := by
  rw [fieldGraph, nbrCount_twoLayer]
  cases f
  · exact degree_EL_two v
  · exact degree_EF_two v
  · exact degree_EE_two v

theorem degE_left_one (f : FType) (v : Fin 3 × f.Obj × Fin 1) :
    nbrCount (fieldGraph .E f (Fin 1)) univ v ≤ 8 := by
  rw [fieldGraph, nbrCount_twoLayer]
  cases f
  · exact degree_EL_one v
  · exact degree_EF_one v
  · exact degree_EE_one v

theorem degE_right_two (f : FType) (v : f.Obj × Fin 3 × Fin 2) :
    nbrCount (fieldGraph f .E (Fin 2)) univ v ≤ 8 := by
  rw [fieldGraph, nbrCount_twoLayer]
  cases f
  · exact degree_LE_two v
  · exact degree_FE_two v
  · exact degree_EE_two v

theorem degE_right_one (f : FType) (v : f.Obj × Fin 3 × Fin 1) :
    nbrCount (fieldGraph f .E (Fin 1)) univ v ≤ 8 := by
  rw [fieldGraph, nbrCount_twoLayer]
  cases f
  · exact degree_LE_one v
  · exact degree_FE_one v
  · exact degree_EE_one v

/-- The layer sets in use, with their degree bounds. -/
structure LayerOK (Λ' : Type) [Fintype Λ'] [DecidableEq Λ'] : Prop where
  card : Fintype.card Λ' ≤ 2
  left : ∀ (f : FType) (v : Fin 3 × f.Obj × Λ'), nbrCount (fieldGraph .E f Λ') univ v ≤ 8
  right : ∀ (f : FType) (v : f.Obj × Fin 3 × Λ'), nbrCount (fieldGraph f .E Λ') univ v ≤ 8

theorem layerOK_two : LayerOK (Fin 2) := ⟨by simp, degE_left_two, degE_right_two⟩

theorem layerOK_one : LayerOK (Fin 1) := ⟨by simp, degE_left_one, degE_right_one⟩

/-! ## One prime -/

section OnePrime

variable (p : ℕ) [Fact p.Prime]

/-- The extension of a fold labelling of `G_{F𝔣}` off the row `j`, at one prime. -/
theorem extend_left (hW : WeilBound (ZMod p)) (hp : (2 : ℝ) ^ 20 ≤ p) {Λ' : Type} [Fintype Λ']
    [DecidableEq Λ'] (hΛ : LayerOK Λ') (f : FType) (y : Fin 3 × f.Obj × Λ' → ZMod p)
    (hy : y ∈ injLabellings (ZMod p) (fieldGraph .F f Λ')) (j : Fin 3) (hj : j ≠ 1) :
    ∃ z ∈ injLabellings (ZMod p) (fieldGraph .E f Λ'), ∀ w, w.1 ≠ j → z w = y w := by
  classical
  rw [mem_injLabellings_iff_feasible] at hy
  have hfeas : Feasible (ZMod p) (fieldGraph .E f Λ') (univ.filter fun w => w.1 ≠ j) y := by
    refine ⟨fun a _ b _ hab => hy.1 a (mem_univ _) b (mem_univ _) hab, fun e he h1 h2 => ?_⟩
    have h1' := (mem_filter.mp h1).2
    have h2' := (mem_filter.mp h2).2
    have heF : e ∈ (fieldGraph .F f Λ').E := by
      rw [fieldGraph, mem_twoLayerGraph]
      rw [fieldGraph, mem_twoLayerGraph] at he
      exact (edge_agree_left f.rel hj e.1 e.2 h1' h2').symm.trans he
    exact hy.2 e heF (mem_univ _) (mem_univ _)
  have hcard : (Fintype.card (Fin 3 × f.Obj × Λ') : ℝ) ≤ 36 := by
    have h6 := card_obj_le f
    have hl : Fintype.card Λ' ≤ 2 := hΛ.card
    have : Fintype.card (Fin 3 × f.Obj × Λ') ≤ 36 := by
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
      nlinarith
    exact_mod_cast this
  have hq := threshold_eight (q := (Fintype.card (ZMod p) : ℝ)) (by rw [ZMod.card]; exact hp)
    (Nat.cast_nonneg _) hcard
  obtain ⟨z, hz, hzy⟩ := exists_extension hW (fieldGraph .E f Λ') (hΛ.left f) hq hfeas
  exact ⟨z, hz, fun w hw => hzy w (mem_filter.mpr ⟨mem_univ _, hw⟩)⟩

/-- The same in the coordinate `1`. -/
theorem extend_right (hW : WeilBound (ZMod p)) (hp : (2 : ℝ) ^ 20 ≤ p) {Λ' : Type} [Fintype Λ']
    [DecidableEq Λ'] (hΛ : LayerOK Λ') (f : FType) (y : f.Obj × Fin 3 × Λ' → ZMod p)
    (hy : y ∈ injLabellings (ZMod p) (fieldGraph f .F Λ')) (j : Fin 3) (hj : j ≠ 1) :
    ∃ z ∈ injLabellings (ZMod p) (fieldGraph f .E Λ'), ∀ w, w.2.1 ≠ j → z w = y w := by
  classical
  rw [mem_injLabellings_iff_feasible] at hy
  have hfeas : Feasible (ZMod p) (fieldGraph f .E Λ') (univ.filter fun w => w.2.1 ≠ j) y := by
    refine ⟨fun a _ b _ hab => hy.1 a (mem_univ _) b (mem_univ _) hab, fun e he h1 h2 => ?_⟩
    have h1' := (mem_filter.mp h1).2
    have h2' := (mem_filter.mp h2).2
    have heF : e ∈ (fieldGraph f .F Λ').E := by
      rw [fieldGraph, mem_twoLayerGraph]
      rw [fieldGraph, mem_twoLayerGraph] at he
      exact (edge_agree_right f.rel hj e.1 e.2 h1' h2').symm.trans he
    exact hy.2 e heF (mem_univ _) (mem_univ _)
  have hcard : (Fintype.card (f.Obj × Fin 3 × Λ') : ℝ) ≤ 36 := by
    have h6 := card_obj_le f
    have hl : Fintype.card Λ' ≤ 2 := hΛ.card
    have : Fintype.card (f.Obj × Fin 3 × Λ') ≤ 36 := by
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
      nlinarith
    exact_mod_cast this
  have hq := threshold_eight (q := (Fintype.card (ZMod p) : ℝ)) (by rw [ZMod.card]; exact hp)
    (Nat.cast_nonneg _) hcard
  obtain ⟨z, hz, hzy⟩ := exists_extension hW (fieldGraph f .E Λ') (hΛ.right f) hq hfeas
  exact ⟨z, hz, fun w hw => hzy w (mem_filter.mpr ⟨mem_univ _, hw⟩)⟩

/-- The uniform laws on `Inj_p(G_{φ₀φ₁})` at one prime. -/
noncomputable def graphLaws {Λ' : Type} [Fintype Λ'] [DecidableEq Λ']
    (hne : ∀ f₀ f₁, (injLabellings (ZMod p) (fieldGraph f₀ f₁ Λ')).Nonempty) (f₀ f₁ : FType) :
    FiniteLaw (f₀.Obj × f₁.Obj × Λ' → ZMod p) :=
  graphLaw (fieldGraph f₀ f₁ Λ') (hne f₀ f₁)

theorem graphLaws_graphInv {Λ' : Type} [Fintype Λ'] [DecidableEq Λ']
    (hne : ∀ f₀ f₁, (injLabellings (ZMod p) (fieldGraph f₀ f₁ Λ')).Nonempty) :
    GraphInv (graphLaws p hne) :=
  fun _ _ π hπ g => graphLaw_expect_comp _ _ π hπ g

/-- **The extension property of the single-prime laws**, under Weil's bound at `p ≥ 2²⁰`. -/
theorem graphLaws_suppExt (hW : WeilBound (ZMod p)) (hp : (2 : ℝ) ^ 20 ≤ p) {Λ' : Type}
    [Fintype Λ'] [DecidableEq Λ'] (hΛ : LayerOK Λ')
    (hne : ∀ f₀ f₁, (injLabellings (ZMod p) (fieldGraph f₀ f₁ Λ')).Nonempty) :
    SuppExt (graphLaws p hne) where
  left f y hy j hj := by
    obtain ⟨z, hz, hzy⟩ := extend_left p hW hp hΛ f y
      ((graphLaw_weight_ne_zero _ _ _).mp hy) j hj
    exact ⟨z, (graphLaw_weight_ne_zero _ _ _).mpr hz, hzy⟩
  right f y hy j hj := by
    obtain ⟨z, hz, hzy⟩ := extend_right p hW hp hΛ f y
      ((graphLaw_weight_ne_zero _ _ _).mp hy) j hj
    exact ⟨z, (graphLaw_weight_ne_zero _ _ _).mpr hz, hzy⟩

/-- **The row data of the tail law form five-type data** at every prime `p ≥ 2²⁰`, under Weil's
bound (`subsec:upper-rows` for the tail datum, with the extension input proved). -/
theorem tail_upperDatumHyp (hW : WeilBound (ZMod p)) (hp : (2 : ℝ) ^ 20 ≤ p)
    (hne : TailNonempty p) : UpperDatumHyp (tailFieldLaws p hne) :=
  upperDatumHyp_of (tailFieldLaws p hne) (graphLaws_graphInv p hne.two)
    (graphLaws_graphInv p hne.one) (graphLaws_suppExt p hW hp layerOK_two hne.two)
    (graphLaws_suppExt p hW hp layerOK_one hne.one)

end OnePrime

/-! ## The tail datum's weights -/

/-- The ordinary inputs of the tail datum, indexed by C1's field types. -/
def tailOrd (f : FieldTy) : CompletionInput := tailOrdinary (toFType f)

/-- The reserved inputs of the tail datum. -/
def tailRes (f : FieldTy) : CompletionInput := tailReserved (toFType f)

/-- The caps `k_𝔱 = k_{𝔣(𝔱)}` of the tail datum, as reals. -/
noncomputable def tailCap (t₀ t₁ : PType) : ℝ := ((tailFieldCap t₀.field t₁.field : ℚ) : ℝ)

theorem sliceGates_of_sliceOK (I : CompletionInput) (a : PType → ℚ) (h : SliceOK I a) :
    SliceGates I.d I.f I.h I.M (fun s => ((a (ofTy s) : ℚ) : ℝ)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [ofTy]
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4

theorem field_ofTy (t : Ty) : (ofTy t).field = toFType (fieldOf t) := by
  cases t <;> rfl

/-- **The tail weights satisfy the gates of the tail datum** (`def:record:upper-bands`(d),(e),
`cert:upper-completion`): V1's exact check `tailDatum_gates`, in the form `WeightsOK`. -/
theorem tailWeightsOK : WeightsOK tailWeights tailOrd tailRes tailCap where
  g20 t1 := by
    have h := sliceGates_of_sliceOK _ _ (tailDatum_gates.1 0 (ofTy t1))
    rw [field_ofTy] at h
    exact h
  g21 t0 := by
    have h := sliceGates_of_sliceOK _ _ (tailDatum_gates.1 1 (ofTy t0))
    rw [field_ofTy] at h
    exact h
  g10 t1 := by
    have h := sliceGates_of_sliceOK _ _ (tailDatum_gates.2.1 0 (ofTy t1))
    rw [field_ofTy] at h
    exact h
  g11 t0 := by
    have h := sliceGates_of_sliceOK _ _ (tailDatum_gates.2.1 1 (ofTy t0))
    rw [field_ofTy] at h
    exact h
  dom := tailWeights_dom
  posW t₀ t₁ := by cases t₀ <;> cases t₁ <;> norm_num [tailWeights, tailW]
  posV t₀ t₁ := by cases t₀ <;> cases t₁ <;> norm_num [tailWeights, tailV]

/-! ## The tail law -/

section Tail

variable (p : ℕ) [Fact p.Prime]

theorem tailR_pos : 0 < tailR p :=
  Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _

/-- **`lem:tail-law`(ii), reflection positivity**: at every prime `p ≥ 2²⁰` (in particular every
tail prime `p ≥ P₄`), under H1, if the inputs of the tail datum are valid on `{p}`
(`lem:tail-law`(i), a hypothesis here: (V1)–(V3) are the spectral inputs), then the tail law is
reflection positive at every cut of the family `𝔉`. -/
theorem tailLaw_familyPositive (hW : WeilBound (ZMod p)) (hp : (2 : ℝ) ^ 20 ≤ p)
    (hne : TailNonempty p)
    (hV : ValidInputs (tailFieldLaws p hne) (tail_upperDatumHyp p hW hp hne) (tailR p) tailOrd
      tailRes tailCap) :
    TheoremC.FamilyReflectionPositive (signedIntegral (tailLaw p hne).weight) :=
  upperReference_familyPositive (tailFieldLaws p hne) tailWeights (tailR_pos p)
    (tail_upperDatumHyp p hW hp hne) hV tailWeightsOK

theorem two_pow_20_le_P4 : (2 : ℝ) ^ 20 ≤ (P4 : ℝ) := by
  rw [show P4 = 2 ^ 512 from rfl, Nat.cast_pow, Nat.cast_ofNat]
  exact pow_le_pow_right₀ (by norm_num) (by norm_num)

/-- **`lem:tail-law`(ii)** (except admissibility): at every prime `p ≥ P₄`, under H1 and the
validity of the tail inputs (`lem:tail-law`(i), a hypothesis), the tail law `μ_p` is a
probability law on `𝔽_p^V`, reflection positive at every cut of `𝔉`, invariant under the
square-affine maps, with uniform one-slot marginals; so the tail atoms satisfy (R1)–(R3). -/
theorem tailLaw_R1R3 (hW : Target.Weil) (hp : P4 ≤ p) (hne : TailNonempty p)
    (hV : ∀ hW' hp', ValidInputs (tailFieldLaws p hne) (tail_upperDatumHyp p hW' hp' hne)
      (tailR p) tailOrd tailRes tailCap) :
    TheoremC.FamilyReflectionPositive (signedIntegral (tailLaw p hne).weight) ∧
      (∀ {s : ZMod p}, quadraticChar (ZMod p) s = 1 → ∀ (u : ZMod p) (H : (Slot → ZMod p) → ℝ),
        (tailLaw p hne).expect (fun z => H (fun v => s * z v + u)) = (tailLaw p hne).expect H) ∧
      HasUniformMarginals (tailLaw p hne) := by
  have hp20 : (2 : ℝ) ^ 20 ≤ p := two_pow_20_le_P4.trans (by exact_mod_cast hp)
  have hp2 : p ≠ 2 := by
    intro h
    have : (2 : ℝ) ^ 20 ≤ 2 := by rw [h] at hp20; exact_mod_cast hp20
    norm_num at this
  have hW' := weilBound_of_target hW p hp2
  exact ⟨tailLaw_familyPositive p hW' hp20 hne (hV hW' hp20),
    fun hs u H => tailLaw_affine p hne hs u H, tailLaw_uniform p hne⟩

end Tail

end Sarkozy.PartVLaws
