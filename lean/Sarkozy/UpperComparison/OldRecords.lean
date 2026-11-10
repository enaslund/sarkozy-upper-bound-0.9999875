module

public import Sarkozy.UpperComparison.Densities
public import Sarkozy.UpperComparison.Acceptance

@[expose] public section

/-!
# The old two-layer records of an upper block and their half law

`paper/sections/26_upper_comparison.tex`, paragraph "The repair": "the layer swap is an
automorphism of `G`, and both layers induce the one-layer graph `H = G_{φ₀φ₁,1}` on `U`", and the
proofs of (F7), `prop:forest-records`, `prop:dense-comparison`, which work relative to the half law
`λ_H` of the record.

For V1's block field laws:
* `halfLaw`: the half law `λ_H` of an upper two-layer record, the one-layer block law of
  `G_{φ₀φ₁,1}` read on its single layer, as a law on `O₀ × O₁ → X_𝔅`;
* `blockGraphLaw_weight_ne_zero_of`: a block labelling feasible at every prime is charged;
* `layer_feasible`: each layer of a feasible two-layer labelling is a feasible labelling of the
  one-layer graph (`twoLayerEdge` does not read the layer);
* **`upper_layersSupported`**: both layers of the two-layer block law are supported where `λ_H`
  is, the support condition of `Densities`;
* `recOld`, `recHalf`, `recU`, `recChangeForm`: the old law, the half law, the half density and
  the centred change form `𝒞_{K'} - 𝒞_O` of a record of state `𝔱`;
* **`oldRecord_sym_bracket`**, **`oldRecord_skew_bracket`**: for a changed two-layer record of the
  paper (the old law is V1's), the analytic bound on the kernels `pairDensity` gives the bracket of
  the symmetric (skew) part at `ι` of the change from V1's component to the emitted new law. The
  only remaining hypotheses are the support condition for the new law and the analytic bound.
-/

open Finset

namespace Sarkozy.UpperComparison

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.RecordExpansion Sarkozy.Recentering
  Sarkozy.Structured

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The half law `λ_H` of an upper two-layer record** with field types `f₀, f₁`: the block law of
the one-layer graph `G_{φ₀φ₁,1}`, read on its single layer. -/
noncomputable def halfLaw (hne : UpperNonempty pr) (f₀ f₁ : FType) :
    FiniteLaw (f₀.Obj × f₁.Obj → BlockLabel pr) :=
  (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁)).map
    (fun y o => y (o.1, o.2, 0))

/-- A block labelling that is feasible at every prime is charged by the block law. -/
theorem blockGraphLaw_weight_ne_zero_of {W : Type} [Fintype W] [DecidableEq W]
    (G : OrientedGraph W) (hne : ∀ i, (injLabellings (ZMod (pr i)) G).Nonempty)
    {y : W → BlockLabel pr} (h : ∀ i, (fun w => y w i) ∈ injLabellings (ZMod (pr i)) G) :
    (blockGraphLaw pr G hne).weight y ≠ 0 := by
  unfold blockGraphLaw
  rw [tensor_weight, Finset.prod_ne_zero_iff]
  exact fun i _ => (graphLaw_weight_ne_zero _ _ _).mpr (h i)

/-- **Each layer of a feasible two-layer labelling is a feasible labelling of the one-layer
graph**: the edge relation of the field graphs does not read the layer. -/
theorem layer_feasible (f₀ f₁ : FType) (k : Fin 2) {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (y : f₀.Obj × f₁.Obj × Fin 2 → F)
    (hy : y ∈ injLabellings F (fieldGraph f₀ f₁ (Fin 2))) :
    (fun o : f₀.Obj × f₁.Obj × Fin 1 => y (o.1, o.2.1, k)) ∈
      injLabellings F (fieldGraph f₀ f₁ (Fin 1)) := by
  rw [mem_injLabellings_iff_feasible] at hy ⊢
  obtain ⟨hinj, hedge⟩ := hy
  refine ⟨fun a _ b _ hab => ?_, fun e he _ _ => ?_⟩
  · have h := hinj _ (mem_univ _) _ (mem_univ _) hab
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 (Subsingleton.elim _ _))
  · have he' : ((e.1.1, e.1.2.1, k), (e.2.1, e.2.2.1, k)) ∈ (fieldGraph f₀ f₁ (Fin 2)).E := by
      simp only [fieldGraph, mem_twoLayerGraph] at he ⊢
      exact he
    exact hedge _ he' (mem_univ _) (mem_univ _)

/-- **Both layers of an upper two-layer block law are supported where its half law is**: the
support condition `LayersSupported` of `Densities`, for V1's two-layer laws. -/
theorem upper_layersSupported (hne : UpperNonempty pr) (f₀ f₁ : FType) :
    LayersSupported ((upperBlockFieldLaws pr hne).two f₀ f₁) (halfLaw pr hne f₀ f₁) := by
  intro y hy
  have hfeas : ∀ i, (fun w => y w i) ∈ injLabellings (ZMod (pr i)) (fieldGraph f₀ f₁ (Fin 2)) :=
    fun i => blockGraphLaw_support pr _ _ hy i
  have key : ∀ k : Fin 2, (halfLaw pr hne f₀ f₁).weight (layerOf y k) ≠ 0 := by
    intro k
    set y' : f₀.Obj × f₁.Obj × Fin 1 → BlockLabel pr := fun o => y (o.1, o.2.1, k) with hy'
    have hw : (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁)).weight y' ≠ 0 :=
      blockGraphLaw_weight_ne_zero_of pr _ _ fun i => layer_feasible f₀ f₁ k _ (hfeas i)
    have hpos : 0 < (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁)).weight y' :=
      lt_of_le_of_ne ((blockGraphLaw pr _ (hne.one f₀ f₁)).nonneg y') (Ne.symm hw)
    have hmap : (fun o : f₀.Obj × f₁.Obj => y' (o.1, o.2, 0)) = layerOf y k := rfl
    change (∑ y'', if (fun o : f₀.Obj × f₁.Obj => y'' (o.1, o.2, 0)) = layerOf y k then
      (blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁)).weight y'' else 0) ≠ 0
    apply ne_of_gt
    refine Finset.sum_pos' (fun y'' _ => ?_) ⟨y', mem_univ _, ?_⟩
    · split_ifs
      · exact (blockGraphLaw pr _ (hne.one f₀ f₁)).nonneg y''
      · exact le_rfl
    · simp only [hmap, ↓reduceIte]
      exact hpos
  exact ⟨key 0, key 1⟩

/-- The old two-layer law `λ_𝔅(G_{φ₀φ₁,2})` of a record of state `𝔱`. -/
noncomputable abbrev recOld (hne : UpperNonempty pr) (t : PType × PType) :
    FiniteLaw (t.1.field.Obj × t.2.field.Obj × Fin 2 → BlockLabel pr) :=
  (upperBlockFieldLaws pr hne).two t.1.field t.2.field

/-- The half law `λ_H` of a record of state `𝔱`. -/
noncomputable abbrev recHalf (hne : UpperNonempty pr) (t : PType × PType) :
    FiniteLaw (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) :=
  halfLaw pr hne t.1.field t.2.field

/-- The half density `u₀` of the old record: its actual half marginal is `(1 + u₀)λ_H`. -/
noncomputable abbrev recU (hne : UpperNonempty pr) (t : PType × PType) :
    (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ :=
  halfDensity (recOld pr hne t) (recHalf pr hne t)

/-- The centred change form `𝒞_{K'} - 𝒞_O` of a changed record, relative to the old half
marginal, with `K' = pairDensity lamN λ_H` and `O = pairDensity (old law) λ_H`. -/
noncomputable def recChangeForm (hne : UpperNonempty pr) (t : PType × PType)
    (lamN : FiniteLaw (t.1.field.Obj × t.2.field.Obj × Fin 2 → BlockLabel pr))
    (φ' ψ' : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ) : ℝ :=
  centredForm (recHalf pr hne t) (recU pr hne t) (pairDensity lamN (recHalf pr hne t)) φ' ψ' -
    centredForm (recHalf pr hne t) (recU pr hne t)
      (pairDensity (recOld pr hne t) (recHalf pr hne t)) φ' ψ'

/-- **The bracket of the symmetric part of a changed record of the paper** (`prop:record:upper`(i),
"Records repaired", "Records replaced"). The old record is V1's two-layer component `Π_{𝔱,φ}`, its
half law is `λ_H` (`halfLaw`) and its kernels are `pairDensity`, `halfDensity`. For a replacing
two-layer law `lamN` with both layers supported where `λ_H` is, a bound `C` on the symmetric part of
`𝒞_{K'} - 𝒞_O` relative to the old half marginal gives the bracket of the symmetric part at `ι` of
`Π_new - Π_{𝔱,φ}`, with envelope `Diag(m_+)` of the old record. -/
theorem oldRecord_sym_bracket (hne : UpperNonempty pr) (t : PType × PType)
    (φ : t.1.Pat × t.2.Pat)
    (lamN : FiniteLaw (t.1.field.Obj × t.2.field.Obj × Fin 2 → BlockLabel pr))
    (hsN : LayersSupported lamN (recHalf pr hne t)) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ φ' ψ', |(recChangeForm pr hne t lamN φ' ψ' + recChangeForm pr hne t lamN ψ' φ') / 2| ≤
      C * mnrm (recHalf pr hne t) (recU pr hne t) φ' * mnrm (recHalf pr hne t) (recU pr hne t) ψ') :
    reservedCut.Bracket
      (C • reservedCut.diagonalLaw (plusMarginal reservedCut
        (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight))
      (symPart reservedCut
        (signedIntegral (emit lamN (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight -
          signedIntegral (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight))
      (C • reservedCut.diagonalLaw (plusMarginal reservedCut
        (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight)) :=
  upRecord_sym_bracket_of_support lamN (recOld pr hne t) (t.1.pat φ.1) (t.2.pat φ.2)
    (recHalf pr hne t) hsN (upper_layersSupported pr hne t.1.field t.2.field) hC hB

/-- **The bracket of the skew part of a changed record of the paper**, as `oldRecord_sym_bracket`
with the skew parts. -/
theorem oldRecord_skew_bracket (hne : UpperNonempty pr) (t : PType × PType)
    (φ : t.1.Pat × t.2.Pat)
    (lamN : FiniteLaw (t.1.field.Obj × t.2.field.Obj × Fin 2 → BlockLabel pr))
    (hsN : LayersSupported lamN (recHalf pr hne t)) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ φ' ψ', |(recChangeForm pr hne t lamN φ' ψ' - recChangeForm pr hne t lamN ψ' φ') / 2| ≤
      C * mnrm (recHalf pr hne t) (recU pr hne t) φ' * mnrm (recHalf pr hne t) (recU pr hne t) ψ') :
    reservedCut.Bracket
      (C • reservedCut.diagonalLaw (plusMarginal reservedCut
        (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight))
      (skewPart reservedCut
        (signedIntegral (emit lamN (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight -
          signedIntegral (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight))
      (C • reservedCut.diagonalLaw (plusMarginal reservedCut
        (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight)) :=
  upRecord_skew_bracket_of_support lamN (recOld pr hne t) (t.1.pat φ.1) (t.2.pat φ.2)
    (recHalf pr hne t) hsN (upper_layersSupported pr hne t.1.field t.2.field) hC hB

end Sarkozy.UpperComparison
