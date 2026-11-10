module

public import Sarkozy.PartV.ChamberCut
public import Sarkozy.PartV.PositiveRoot

@[expose] public section

/-!
# The individual-square positive root under `𝒢₆`, and (R2) on the tilted pieces

`paper/sections/20b_positive_roots.tex`, `lem:positive-root-properties`(b) (the chamber
reflections `u ↦ k - u` and the translation `u ↦ u + 2` permute the three scores, so they fix the
weight and the root); `paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(iii).

* `basePair_image`: every `g ∈ 𝒢₆` maps the base pair `{j, j+3}` onto `{σ j, σ j + 3}`,
  `σ j = g(j) mod 3` (`g6Pair`, a bijection of `{0, 1, 2}`), checked by `decide`;
* `rootTrace_g6`: `H_j(x ∘ g) = H_{σ j}(x)`; `individualWeight_g6`: `w_u(x ∘ g) = w_u(x)`;
* `individualRoot_weight_g6`: `Γ_{p,u}` is `𝒢₆`-invariant; `objLaw_individualRoot_inv`: so is the
  block root, as a law of objects;
* `middleBlock_datumHyp₂_individual`: the datum hypotheses of `Sarkozy.PartV.ChamberCut` hold for
  the middle block laws with the individual-square root;
* `middleBlockReference_individual_familyPositive`: **(R2) at every cut of the family for the
  middle law on the six pieces from `2³⁰` to `2⁴⁰`**, with the rows, the root envelopes and the
  layer caps as hypotheses.

The layer-swap invariance of (b) and the coherent root of `[2⁴⁵, P₃)` (which needs the
dictionary `𝒟₃₉`) are not treated here.
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings Sarkozy.FiveType

/-- The vertex map of `g ∈ 𝒢₆` on `ℤ/6ℤ × {0,1}`. -/
noncomputable def g6Vert (k : Fin 6) : ZMod 6 × Fin 2 ≃ ZMod 6 × Fin 2 :=
  Equiv.prodCongr (g6Equiv k) (Equiv.refl (Fin 2))

theorem g6Vert_apply (k : Fin 6) (v : ZMod 6 × Fin 2) : g6Vert k v = (g6 k v.1, v.2) := rfl

/-- The base pair hit by `g`: `g({j, j+3}) = {σ j, σ j + 3}` with `σ j = g(j) mod 3`. -/
def g6Pair (k : Fin 6) (j : Fin 3) : Fin 3 :=
  ⟨(g6 k (j.val : ZMod 6)).val % 3, Nat.mod_lt _ (by norm_num)⟩

theorem g6Pair_bijective (k : Fin 6) : Function.Bijective (g6Pair k) := by
  revert k
  decide

/-- **`𝒢₆` permutes the base pairs** (`lem:positive-root-properties`(b)). -/
theorem basePair_image (k : Fin 6) (j : Fin 3) :
    (basePair j).image (fun v => (g6 k v.1, v.2)) = basePair (g6Pair k j) := by
  revert k j
  decide

section Prime

variable (p : ℕ) [Fact p.Prime]

/-- **The scores are permuted by `𝒢₆`**: `H_j(x ∘ g) = H_{σ j}(x)`. -/
theorem rootTrace_g6 (k : Fin 6) (j : Fin 3) (x : ZMod 6 × Fin 2 → ZMod p) :
    rootTrace p j (x ∘ g6Vert k) = rootTrace p (g6Pair k j) x := by
  unfold rootTrace
  refine sum_congr rfl fun z _ => ?_
  congr 1
  rw [← basePair_image k j, prod_image]
  · rfl
  · intro a _ b _ hab
    exact (g6Vert k).injective hab

/-- **The individual-square weight is `𝒢₆`-invariant** (a symmetric function of the scores). -/
theorem individualWeight_g6 (u : ℚ) (k : Fin 6) (x : ZMod 6 × Fin 2 → ZMod p) :
    individualWeight p u (x ∘ g6Vert k) = individualWeight p u x := by
  unfold individualWeight rootScore
  simp only [rootTrace_g6]
  congr 1
  exact Equiv.sum_comp (Equiv.ofBijective _ (g6Pair_bijective k))
    (fun j => (1 + (u : ℝ) * ((rootTrace p j x : ℝ) / Real.sqrt p)) ^ 2)

/-- **The individual-square root is `𝒢₆`-invariant** (`lem:positive-root-properties`(b), the
chamber reflections and the translation). -/
theorem individualRoot_weight_g6 (u : ℚ)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty) (k : Fin 6)
    (x : ZMod 6 × Fin 2 → ZMod p) :
    (individualRoot p u hne).weight (x ∘ g6Vert k) = (individualRoot p u hne).weight x := by
  change (graphLaw _ hne).weight (x ∘ g6Vert k) * individualWeight p u (x ∘ g6Vert k) / _ =
    (graphLaw _ hne).weight x * individualWeight p u x / _
  have hlam : (graphLaw (recordGraph (Fin 2)) hne).weight (x ∘ g6Vert k) =
      (graphLaw (recordGraph (Fin 2)) hne).weight x := by
    have hmem : x ∘ g6Vert k ∈ injLabellings (ZMod p) (recordGraph (Fin 2)) ↔
        x ∈ injLabellings (ZMod p) (recordGraph (Fin 2)) :=
      mem_injLabellings_comp_iff _ (g6Vert k) (recordGraph_g6 (Fin 2) k) x
    simp only [graphLaw, hmem]
  rw [hlam, individualWeight_g6]

end Prime

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The block positive root is `𝒢₆`-invariant**, as a law of objects. -/
theorem objLaw_individualRoot_inv (u : ℚ)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph (Fin 2))).Nonempty)
    (k : Fin 6) (Ψ : ZMod 6 → Fin 2 → BlockLabel pr) :
    (objLaw (individualBlockRoot pr u hne)).weight (Ψ ∘ g6 k) =
      (objLaw (individualBlockRoot pr u hne)).weight Ψ := by
  rw [objLaw_weight, objLaw_weight]
  unfold individualBlockRoot
  rw [tensor_weight, tensor_weight]
  refine prod_congr rfl fun i _ => ?_
  exact individualRoot_weight_g6 (pr i) u (hne i) k (fun v => Ψ v.1 v.2 i)

/-- **The datum hypotheses for the middle block laws with the individual-square root.** -/
theorem middleBlock_datumHyp₂_individual (hne : MiddleNonempty pr) (u : ℚ) :
    DatumHyp (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
      (blockGraphLaw pr (foldGraph (Fin 2)) hne.F2) (individualBlockRoot pr u hne.L2) :=
  ⟨objLaw_match_exch pr hne.E2, objLaw_fold_supp pr hne.F2 hne.E2,
    objLaw_individualRoot_inv pr u hne.L2⟩

/-- **(R2) for the middle block law with the individual-square root** (`lem:front12:reference`(iii)
on the six pieces from `2³⁰` to `2⁴⁰`): reflection positive at every cut of the family, given
the thirteen inequalities and, as hypotheses, the rows, the root envelopes (the caps of the
positive root at L20, `cert:positive-root-caps`, and of the untilted one-layer root at L10) and
the layer caps at `ι`. -/
theorem middleBlockReference_individual_familyPositive (hne : MiddleNonempty pr) (u : ℚ)
    (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (hW : W.Completes I)
    (hf₂ : 0 ≤ I.f₂) (hf₁ : 0 ≤ I.f₁)
    (hrows₂ : RowBounds (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)) I.f₂ I.h₂ r)
    (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) I.f₁ I.h₁ r)
    (hroot₂ : RootEnvelope (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)) I.d r)
    (hroot₁ : RootEnvelope (fieldDatum (middleBlock_datumHyp₁ pr hne)) I.d₁ r)
    (hcap : MiddleLayerCaps (middleBlockFieldLaws pr hne (individualBlockRoot pr u hne.L2)) I.k r) :
    TheoremC.FamilyReflectionPositive
      (signedIntegral
        (middleBlockReference pr hne (individualBlockRoot pr u hne.L2) W hr).weight) := by
  have hdom : ∀ t, I.k t * W.w t ≤ W.v t := hW.2.2.2.2.2.2.2.2
  refine middleReference_familyPositive _ W I.k hr hcap hdom fun a => ?_
  rw [middleReference_eq]
  exact (middleTilde_firstCut_positive
    (middleBlockFieldLaws pr hne (individualBlockRoot pr u hne.L2))
    (middleBlock_datumHyp₂_individual pr hne u) (middleBlock_datumHyp₁ pr hne) W I hr hW hf₂ hf₁
    hrows₂ hrows₁ hroot₂ hroot₁ a).smul
    (inv_nonneg.mpr (le_trans zero_le_one (one_le_midPoly W hr)))

end Block

end Sarkozy.PartV
