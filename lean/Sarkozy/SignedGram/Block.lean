module

public import Sarkozy.SignedGram.Reflect
public import Sarkozy.SignedComponents.PrimeComponents

@[expose] public section

/-!
# The block Grams of the signed fold records at a middle block (SGA)

`paper/sections/24_matching_mean.tex`, `lem:record:asymmetric-gram`(b),(c), `prop:signed-sides`(i);
`paper/sections/21_middle_records.tex`, `def:record:mixture`(c),(d).

At V3's frame of a middle block (any root) with B8's replacements `ofFold … C t`:

* **`newW C t j`**: the kernel `K'_{F_{j+1}} = ⊗P_{++} + (t/2)⊗P_{-+} − (t/2)⊗P_{--}` of the
  signed record (`def:record:mixture`(c)); **`form_newMeas`**: its cut form at `ι` is
  `kform (newW C t j)` at the triples read by the fold `F_{j+1}`.
* **`lawF_rT`**: `K₀ ∘ Φ = K₀` for the block fold law (B8's `reflT_mem` at each prime);
  **`Reflected C`**: the components of `F₂` are the reflected transposes of those of `F₁`, at
  every prime and component (`def:record:mixture`(d)); **`blockComponents_reflected`** (so the
  paper's `paperComponents` are reflected); **`newW_one`**: `K'_{F₂} = K'_{F₁} ∘ Φ`.
* **`signedSideGrams_of_opGram`**: for reflected components, the block Gram of `F₁` on
  `L²(m₀)²` with shifts `σ_L, σ_R` (`OpGram`), the density bound `dm₀/dν ≤ H` and
  `H σ_s ≤ r d_s` give MRG's `SignedSideGrams D R d_L d_R` (both folds; `F₂` by (c)).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedGram

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.MiddleComparison Sarkozy.SignedComponents Sarkozy.MiddleRefinement
open Sarkozy.Labellings

/-! ## At one prime -/

section Prime

variable {p : ℕ} [Fact p.Prime]

theorem rT_eq_reflT (y : Fin 3 × Fin 2 → ZMod p) : rT y = reflT y := by
  funext ⟨o, l⟩
  fin_cases l <;> rfl

/-- **`K₀ ∘ Φ = K₀` at one prime** (`def:record:mixture`(d); B8's `reflT_mem`). -/
theorem graphLawF_rT (hF : (injLabellings (ZMod p) (foldGraph (Fin 2))).Nonempty)
    (y : Fin 3 × Fin 2 → ZMod p) :
    (graphLaw (foldGraph (Fin 2)) hF).weight (rT y) =
      (graphLaw (foldGraph (Fin 2)) hF).weight y := by
  have hmem : rT y ∈ injLabellings (ZMod p) (foldGraph (Fin 2)) ↔
      y ∈ injLabellings (ZMod p) (foldGraph (Fin 2)) := by
    rw [rT_eq_reflT]
    exact ⟨fun h => by rw [← reflT_reflT y]; exact reflT_mem _ h, reflT_mem y⟩
  simp only [graphLaw, hmem]

end Prime

/-! ## At a middle block -/

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (hne : MiddleNonempty pr)

omit [Fintype ι] [DecidableEq ι] in
theorem rT_apply (y : Fin 3 × Fin 2 → BlockLabel pr) (i : ι) :
    (fun w => rT y w i) = rT (fun w => y w i) := rfl

/-- **`K₀ ∘ Φ = K₀` for the block fold law** `λ_𝔅(G_{F,2})`. -/
theorem lawF_rT (y : Fin 3 × Fin 2 → BlockLabel pr) :
    (lawF pr hne).weight (rT y) = (lawF pr hne).weight y := by
  unfold lawF blockGraphLaw
  rw [tensor_weight, tensor_weight]
  refine prod_congr rfl fun i _ => ?_
  rw [rT_apply]
  exact graphLawF_rT _ _

variable {pr} {hne}

/-- **The components of `F₂` are the reflected transposes of those of `F₁`**
(`def:record:mixture`(d): `K'_{2,c,p}(x, y) = K'_{c,p}(ς y, ς x)`), at every prime and
component. -/
def Reflected (C : FoldComponents pr hne) : Prop :=
  ∀ i c (z : Fin 3 × Fin 2 → ZMod (pr i)), ((C i).law 1 c).weight z = ((C i).law 0 c).weight (rT z)

/-- The kernel of the signed record of `F_{j+1}`:
`K'_{F_{j+1}} = ∑_c α_c ⊗_p P_{c,p}` with `α = (1, t/2, -t/2)` (`def:record:mixture`(c)). -/
noncomputable def newW (C : FoldComponents pr hne) (t : ℝ) (j : Fin 2) :
    (Fin 3 × Fin 2 → BlockLabel pr) → ℝ :=
  fun y => ∑ c, signedCoef t c * (foldLaw C j c).weight y

/-- **`K'_{F₂} = K'_{F₁} ∘ Φ`** for reflected components. -/
theorem newW_one {C : FoldComponents pr hne} (hC : Reflected C) (t : ℝ)
    (y : Fin 3 × Fin 2 → BlockLabel pr) : newW C t 1 y = newW C t 0 (rT y) := by
  unfold newW
  refine sum_congr rfl fun c _ => ?_
  congr 1
  unfold foldLaw
  rw [tensor_weight, tensor_weight]
  refine prod_congr rfl fun i _ => ?_
  rw [rT_apply]
  exact hC i c _

omit [DecidableEq ι] in
theorem placeEquiv_rT {q : ℕ} [Fact q.Prime] (z : Fin 3 × Fin 2 → ZMod q) :
    (placeEquiv 1).symm z = (placeEquiv 0).symm (rT z) := by
  rw [placeEquiv_one_symm, placeEquiv_zero_symm]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- **The paper's components are reflected** (B8's `blockComponents`, hence `paperComponents`:
`law j c = P_{c,p} ∘ placeEquiv j⁻¹`, with `placeEquiv 1 = placeEquiv 0 ∘ Φ`). -/
theorem blockComponents_reflected (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (M : ι → Fin 3 → ℝ) (hM0 : ∀ i c, 0 ≤ M i c)
    (hM : ∀ i c, (repairAt (h3 i) (h19 i) (hne.F2 i) ht0 ht1 c).DefectBound (M i c)) :
    Reflected (blockComponents h3 h19 hne ht0 ht1 M hM0 hM) := by
  intro i c z
  change ((compLaw (h3 i) (h19 i) (hne.F2 i) ht0 ht1 (M i) (hM0 i) (hM i) c).map
      (placeEquiv 1)).weight z =
    ((compLaw (h3 i) (h19 i) (hne.F2 i) ht0 ht1 (M i) (hM0 i) (hM i) c).map
      (placeEquiv 0)).weight (rT z)
  rw [map_equiv_weight, map_equiv_weight, placeEquiv_rT]

variable (h : ClassThreeBlock pr) (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr))
  (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

omit [DecidableEq ι] in
theorem form_sum_smul {V : Type} [Fintype V] [DecidableEq V] {Y : Type}
    (L : Fin 3 → ((V → Y) → ℝ) →ₗ[ℝ] ℝ) (a : Fin 3 → ℝ) (c : ReflectionCut V)
    (F G : (c.Half → Y) → ℝ) :
    c.form (∑ k, a k • L k) F G = ∑ k, a k * c.form (L k) F G := by
  unfold ReflectionCut.form
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

/-- **The cut form of the signed record** `Π'_{F_{j+1}}` of `ofFold` at `ι` is the kernel form of
`K'_{F_{j+1}} = newW C t j` at the triples read by the fold. -/
theorem form_newMeas (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (j : Fin 2)
    (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form ((ofFold pr h hne root W I hr b C t ht0 ht1).toReplacements.newMeas (.inl j))
        F G =
      kform (newW C t j) (fun x => F (hread (foldRead j) x))
        (fun x => G (hread (foldRead j) x)) := by
  rw [ofFold_newMeas_fold, form_sum_smul]
  have e : ∀ c, reservedCut.form (signedIntegral (foldRec C j c).weight) F G =
      kform (foldLaw C j c).weight (fun x => F (hread (foldRead j) x))
        (fun x => G (hread (foldRead j) x)) := fun c => form_two _ _ F G
  simp only [e]
  unfold kform newW
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun c _ => ?_
  ring

/-- **`prop:signed-sides`(i),(ii) at a middle block from the block Gram of `F₁` on `L²(m₀)²`**
(`lem:record:asymmetric-gram`(b), the measure form and the enlargement (a); (c) for `F₂`): for
reflected components, `OpGram K₀ K'_{F₁} σ_L σ_R`, `dm₀/dν ≤ H` and `H σ_s ≤ r d_s` give MRG's
`SignedSideGrams` at the sides `d_L, d_R`. -/
theorem signedSideGrams_of_opGram (C : FoldComponents pr hne) (hC : Reflected C) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {σL σR H dL dR : ℝ} (hσL : 0 ≤ σL) (hσR : 0 ≤ σR)
    (hdens : DensityLe (lawF pr hne).weight (blockGraphLaw pr (foldGraph (Fin 1)) hne.F1).weight H)
    (hHL : H * σL ≤ r * dL) (hHR : H * σR ≤ r * dR)
    (hG : OpGram (lawF pr hne).weight (newW C t 0) σL σR) :
    SignedSideGrams (middleFrame pr hne root W I hr b h)
      (ofFold pr h hne root W I hr b C t ht0 ht1).toReplacements dL dR where
  gram₁ := bracket_of_opGram _ 0 (form_newMeas h root W I hr b C ht0 ht1 0) (lawF_swap pr hne)
    hσL hσR hdens hHL hHR hG
  gram₂ := bracket_of_opGram _ 1 (form_newMeas h root W I hr b C ht0 ht1 1) (lawF_swap pr hne)
    hσR hσL hdens hHR hHL
    (opGram_refl (lawF_rT pr hne) (lawF_swap pr hne) (newW_one hC t) hG)

end Block

end Sarkozy.SignedGram
