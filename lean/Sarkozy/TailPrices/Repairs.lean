module

public import Sarkozy.TailPrices.Deletions
public import Sarkozy.UpperComparison.OldRecords

@[expose] public section

/-!
# The repaired records of the tail atom (`lem:tail-prices`(ii), `lem:tr:repair`)

`paper/sections/27_tail_index.tex`, proof of `lem:tail-prices`(i),(ii): "a repaired record becomes
a probability law with exactly the actual half marginals at `ι` of the record it replaces …; its
difference from the replaced record has zero marginals and norm at most `C_ϱ r` relative to these
marginals (`lem:tr:repair`(f) with (F7))". W8 (`UpperComparison.OldRecords`, `Densities`) turns
such a norm bound on the pair kernels into the bracket at `ι`, generically in the labels
(`upRecord_sym_bracket_of_support`). This file applies it at the tail:

* `tailHalf`, `tail_layersSupported`: the half law `λ_H` of a two-layer tail record and the support
  condition for the old record (W8's `upper_layersSupported` at the tail field laws);
* `TailRepair p hne t φ`: the repair of the changed record `(t, φ)`: a two-layer law `lam` with both
  layers supported where `λ_H` is, whose emission accepts `𝓔₆` and is square-affine invariant,
  and constants `C^s, C^a ≥ 0` bounding the symmetric and skew parts of the change of centred pair
  forms relative to the old half marginal (`lem:tr:repair`(f), (F7), `cert:tail-caps`).
  *Hypotheses* (analytic);
* **`TailRepair.bracket`**: the bracket of the change at `ι` with the envelope of the old record;
* **`TailRepairs.toRecords`**: `TailRecordInputs` from a repair of every changed record, with
  `π̃^ε_ρ = P_μ(r)⁻¹ c_ρ C^ε_ρ` (`bracket_smul`); every changed record is two-layer.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.TailPrices

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.Mixing Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.Labellings Sarkozy.UpperComparison Sarkozy.Recentering Sarkozy.Structured
open Sarkozy.ComparisonLawPaper (changePart_smul)

variable (p : ℕ) [Fact p.Prime] (hne : TailNonempty p)

/-- **The half law `λ_H` of a two-layer tail record** with field types `f₀, f₁`: the graph law of
the one-layer graph `G_{φ₀φ₁,1}`, read on its single layer. -/
noncomputable def tailHalf (f₀ f₁ : FType) : FiniteLaw (f₀.Obj × f₁.Obj → ZMod p) :=
  (graphLaw (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁)).map (fun y o => y (o.1, o.2, 0))

/-- **Both layers of a two-layer tail law are supported where its half law is**. -/
theorem tail_layersSupported (f₀ f₁ : FType) :
    LayersSupported ((tailFieldLaws p hne).two f₀ f₁) (tailHalf p hne f₀ f₁) := by
  intro y hy
  change (graphLaw (fieldGraph f₀ f₁ (Fin 2)) (hne.two f₀ f₁)).weight y ≠ 0 at hy
  have hfeas : y ∈ injLabellings (ZMod p) (fieldGraph f₀ f₁ (Fin 2)) :=
    (graphLaw_weight_ne_zero _ _ _).mp hy
  have key : ∀ k : Fin 2, (tailHalf p hne f₀ f₁).weight (layerOf y k) ≠ 0 := by
    intro k
    set y' : f₀.Obj × f₁.Obj × Fin 1 → ZMod p := fun o => y (o.1, o.2.1, k) with hy'
    have hw : (graphLaw (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁)).weight y' ≠ 0 :=
      (graphLaw_weight_ne_zero _ _ _).mpr (layer_feasible f₀ f₁ k _ hfeas)
    have hpos : 0 < (graphLaw (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁)).weight y' :=
      lt_of_le_of_ne ((graphLaw _ (hne.one f₀ f₁)).nonneg y') (Ne.symm hw)
    have hmap : (fun o : f₀.Obj × f₁.Obj => y' (o.1, o.2, 0)) = layerOf y k := rfl
    change (∑ y'', if (fun o : f₀.Obj × f₁.Obj => y'' (o.1, o.2, 0)) = layerOf y k then
      (graphLaw (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁)).weight y'' else 0) ≠ 0
    apply ne_of_gt
    refine Finset.sum_pos' (fun y'' _ => ?_) ⟨y', mem_univ _, ?_⟩
    · split_ifs
      · exact (graphLaw _ (hne.one f₀ f₁)).nonneg y''
      · exact le_rfl
    · simp only [hmap, ↓reduceIte]
      exact hpos
  exact ⟨key 0, key 1⟩

/-- The old two-layer law `λ_p(G_{φ₀φ₁,2})` of a tail record of state `𝔱`. -/
noncomputable abbrev tailOld (t : PType × PType) :
    FiniteLaw (t.1.field.Obj × t.2.field.Obj × Fin 2 → ZMod p) :=
  (tailFieldLaws p hne).two t.1.field t.2.field

/-- The half density `u₀` of the old tail record. -/
noncomputable abbrev tailU (t : PType × PType) :
    (t.1.field.Obj × t.2.field.Obj → ZMod p) → ℝ :=
  halfDensity (tailOld p hne t) (tailHalf p hne t.1.field t.2.field)

/-- The change `𝒞_{K'} - 𝒞_O` of centred pair forms of a repaired tail record, relative to the old
half marginal. -/
noncomputable def tailChangeForm (t : PType × PType)
    (lamN : FiniteLaw (t.1.field.Obj × t.2.field.Obj × Fin 2 → ZMod p))
    (φ' ψ' : (t.1.field.Obj × t.2.field.Obj → ZMod p) → ℝ) : ℝ :=
  centredForm (tailHalf p hne t.1.field t.2.field) (tailU p hne t)
      (pairDensity lamN (tailHalf p hne t.1.field t.2.field)) φ' ψ' -
    centredForm (tailHalf p hne t.1.field t.2.field) (tailU p hne t)
      (pairDensity (tailOld p hne t) (tailHalf p hne t.1.field t.2.field)) φ' ψ'

/-- **The repair of a changed two-layer tail record** (`lem:tr:repair`(a)–(c),(f), (F7) with the
all-prime cap, `cert:tail-caps`). *Hypotheses*. -/
structure TailRepair (t : PType × PType) (φ : t.1.Pat × t.2.Pat) where
  /-- The repaired two-layer law. -/
  lam : FiniteLaw (t.1.field.Obj × t.2.field.Obj × Fin 2 → ZMod p)
  /-- Both layers supported where `λ_H` is (`lem:tr:repair`(a)–(c)). -/
  supp : LayersSupported lam (tailHalf p hne t.1.field t.2.field)
  /-- The repaired record accepts `𝓔₆` (projected queries imposed). -/
  accepts : ∀ z, (emit lam (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight z ≠ 0 →
    ∀ j : Chamber, quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1
  /-- The repaired record is square-affine invariant (its data are). -/
  inv : AffineInvariant p (emit lam (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight
  /-- The symmetric constant `C^s_ρ` (`C_ϱ r` in the paper). -/
  Cs : ℝ
  /-- The skew constant `C^a_ρ` (`C_ϱ r` in the paper). -/
  Ca : ℝ
  Cs_nonneg : 0 ≤ Cs
  Ca_nonneg : 0 ≤ Ca
  /-- The norm bound of the symmetric part of the change (`lem:tr:repair`(f)). -/
  sym_bound : ∀ φ' ψ', |(tailChangeForm p hne t lam φ' ψ' + tailChangeForm p hne t lam ψ' φ') / 2| ≤
    Cs * mnrm (tailHalf p hne t.1.field t.2.field) (tailU p hne t) φ' *
      mnrm (tailHalf p hne t.1.field t.2.field) (tailU p hne t) ψ'
  /-- The norm bound of the skew part of the change (`lem:tr:repair`(f)). -/
  skew_bound : ∀ φ' ψ', |(tailChangeForm p hne t lam φ' ψ' - tailChangeForm p hne t lam ψ' φ') / 2| ≤
    Ca * mnrm (tailHalf p hne t.1.field t.2.field) (tailU p hne t) φ' *
      mnrm (tailHalf p hne t.1.field t.2.field) (tailU p hne t) ψ'

namespace TailRepair

variable {p} {hne} {t : PType × PType} {φ : t.1.Pat × t.2.Pat} (R : TailRepair p hne t φ)

/-- The constant of a change type. -/
def C : ChangeType → ℝ
  | .sym => R.Cs
  | .skew => R.Ca

theorem C_nonneg (e : ChangeType) : 0 ≤ R.C e := by
  cases e
  · exact R.Cs_nonneg
  · exact R.Ca_nonneg

/-- **The bracket of the change of a repaired tail record** at `ι`, against the envelope
`Diag_ι(m_+(Π_ρ))` of the old record (W8's `upRecord_sym_bracket_of_support`,
`upRecord_skew_bracket_of_support`). -/
theorem bracket (e : ChangeType) :
    reservedCut.Bracket (R.C e • tailEnv p hne (true, ⟨t, φ⟩))
      (changePart e (signedIntegral (emit R.lam (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight -
        signedIntegral (upComponent (tailFieldLaws p hne) (true, ⟨t, φ⟩)).weight))
      (R.C e • tailEnv p hne (true, ⟨t, φ⟩)) := by
  cases e
  · exact upRecord_sym_bracket_of_support R.lam (tailOld p hne t) (t.1.pat φ.1) (t.2.pat φ.2)
      (tailHalf p hne t.1.field t.2.field) R.supp (tail_layersSupported p hne _ _) R.Cs_nonneg
      R.sym_bound
  · exact upRecord_skew_bracket_of_support R.lam (tailOld p hne t) (t.1.pat φ.1) (t.2.pat φ.2)
      (tailHalf p hne t.1.field t.2.field) R.supp (tail_layersSupported p hne _ _) R.Ca_nonneg
      R.skew_bound

end TailRepair

/-- A repair of every changed record of the tail law. -/
abbrev TailRepairs : Type :=
  ∀ (t : PType × PType) (φ : t.1.Pat × t.2.Pat), upperFate (true, ⟨t, φ⟩) = .changed →
    TailRepair p hne t φ

variable {p} {hne}

/-- A folded record is never changed. -/
theorem folded_not_changed (t : PType × PType) (φ : t.1.Pat × t.2.Pat) :
    upperFate (false, ⟨t, φ⟩) ≠ .changed := by
  simp only [upperFate]
  split_ifs <;> simp

namespace TailRepairs

variable (Rp : TailRepairs p hne)

/-- The replacing laws: the emitted repairs of the changed records. -/
noncomputable def new : UpIdx → FiniteLaw (Slot → ZMod p)
  | (true, ⟨t, φ⟩) => if h : upperFate (true, ⟨t, φ⟩) = .changed then
      emit (Rp t φ h).lam (upEmission (t.1.pat φ.1) (t.2.pat φ.2))
    else upComponent (tailFieldLaws p hne) (true, ⟨t, φ⟩)
  | (false, ⟨t, φ⟩) => upComponent (tailFieldLaws p hne) (false, ⟨t, φ⟩)

/-- The prices `π̃^ε_ρ = P_μ(r)⁻¹ c_ρ C^ε_ρ` of the changed records. -/
noncomputable def π : UpIdx → ChangeType → ℝ
  | (true, ⟨t, φ⟩), e => if h : upperFate (true, ⟨t, φ⟩) = .changed then
      (upPoly tailWeights (tailR p))⁻¹ * upCoeff tailWeights (tailR p) (true, ⟨t, φ⟩) *
        (Rp t φ h).C e
    else 0
  | (false, _), _ => 0

theorem π_nonneg (ρ : UpIdx) (e : ChangeType) : 0 ≤ Rp.π ρ e := by
  have hr := tailR_nonneg p
  have hP := lt_of_lt_of_le one_pos (one_le_upPoly tailWeights hr)
  rcases ρ with ⟨b, t, φ⟩
  cases b
  · exact le_rfl
  · simp only [π]
    split_ifs with h
    · exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hP.le) (upCoeff_nonneg _ hr _))
        ((Rp t φ h).C_nonneg e)
    · exact le_rfl

/-- **`TailRecordInputs` from the repairs** (`lem:tail-prices`(i),(ii)). -/
noncomputable def toRecords : TailRecordInputs p hne where
  new := Rp.new
  new_accepts ρ hρ z hz j := by
    rcases ρ with ⟨b, t, φ⟩
    cases b
    · exact absurd hρ (folded_not_changed t φ)
    · simp only [new, hρ, ↓reduceDIte] at hz
      exact (Rp t φ hρ).accepts z hz j
  new_inv ρ hρ := by
    rcases ρ with ⟨b, t, φ⟩
    cases b
    · exact absurd hρ (folded_not_changed t φ)
    · simp only [new, hρ, ↓reduceDIte]
      exact (Rp t φ hρ).inv
  π := Rp.π
  π_nonneg := Rp.π_nonneg
  bracket ρ hρ e := by
    rcases ρ with ⟨b, t, φ⟩
    cases b
    · exact absurd hρ (folded_not_changed t φ)
    · have hr := tailR_nonneg p
      have hP := lt_of_lt_of_le one_pos (one_le_upPoly tailWeights hr)
      have hd : tailDelta hne Rp.new (true, ⟨t, φ⟩) =
          ((upPoly tailWeights (tailR p))⁻¹ * upCoeff tailWeights (tailR p) (true, ⟨t, φ⟩)) •
            (signedIntegral (emit (Rp t φ hρ).lam (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight -
              signedIntegral (upComponent (tailFieldLaws p hne) (true, ⟨t, φ⟩)).weight) := by
        unfold tailDelta recordChange
        rw [hρ]
        simp only [new, hρ, ↓reduceDIte]
        rw [smul_smul]
      have hpi : Rp.π (true, ⟨t, φ⟩) e =
          ((upPoly tailWeights (tailR p))⁻¹ * upCoeff tailWeights (tailR p) (true, ⟨t, φ⟩)) *
            (Rp t φ hρ).C e := by
        simp only [π, hρ, ↓reduceDIte]
      rw [hd, changePart_smul, hpi, ← smul_smul]
      exact bracket_smul ((Rp t φ hρ).bracket e)
        (mul_nonneg (inv_nonneg.mpr hP.le) (upCoeff_nonneg _ hr _))

end TailRepairs

end Sarkozy.TailPrices
