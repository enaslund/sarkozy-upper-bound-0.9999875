module

public import Sarkozy.EnvelopeEnergiesPaper.StageMoments
public import Sarkozy.DensityMoments.MiddleCatalog72
public import Sarkozy.DensityMoments.LawAlgebra

@[expose] public section

/-!
# The record moments of the middle first stage from M1's catalog (`lem:density:middle-catalog`)

**The vacuity check.** A1's six first-stage records of a middle block (`FirstStagePaper.rhoRecs`)
are the one-layer components `Diag_ι(Π⁽¹⁾_φ)` of V3's frame, `φ = F₁, F₂` (type `D`), `E₀, E₁`
(type `S`), `G₀₀, G₁₁` (type `R`): the emissions `emit λ⁽¹⁾_𝔣 (midDiagEmission (pat φ))` of the
one-layer block graph laws `λ⁽¹⁾_F`, `λ⁽¹⁾_E` (`PartV.middleBlockFieldLaws`). None of them is the
one-layer constant (type `C`, the constant pattern `0`), which is the only one-label law of the
catalog: each reads the two distinct objects `0`, `1` at `12` slots each. They are M1's rows
`catalog72_fold_one`, `catalog72_matching_one`, `catalog72_merge_one` (unit mixed `L^{66}` on the
72 slots). The folded matching record `κ_s = oldRec s` is a multiple of the same `E` row. So the
per-record moment inputs are satisfiable as the paper states them, and are proved here:

* `expect_emit_tensor`, `mixedLpBound_emit_tensor`: an emission of a tensor over the primes of the
  block is the tensor of the emissions, so unit mixed bounds tensor;
* `graphLaw_pair_dist`, `graphLaw_pair_affine`: the pair laws of a graph law at two distinct
  vertices are distinct and square-affine invariant (`hdist`, `hinv` of M1's rows; `hunif` is
  `PartV.graphLaw_vertex_uniform`);
* **`middle_rhoRecs_moment`**, **`middle_oldRec_moment`**: `RecordMoment` at every `θ ≤ 12/11` for
  the six records and for `κ_s`, at every block of primes `≥ 64`;
* `AtomStageMoments.ofMiddle`: the per-block moment input of a middle block from the two remaining
  families, the sharp folds (`fold`) and the replacement records `κ'_s = newRecN s` (`mom'`).
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.EnvelopeEnergiesPaper

open Sarkozy.PartV Sarkozy.DensityMoments Sarkozy.DensityUpgrade Sarkozy.TheoremC
  Sarkozy.Labellings

/-! ## Emissions of tensors -/

section Tensor

variable {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W] {X : ι → Type}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-- **An emission of a tensor is the tensor of the emissions** (as laws on the 72 slots). -/
theorem expect_emit_tensor (lam : ∀ i, FiniteLaw (W → X i)) (σ : Slot → W)
    (F : (Slot → ∀ i, X i) → ℝ) :
    (emit (FiniteLaw.tensor lam) σ).expect F =
      (FiniteLaw.tensor fun i => emit (lam i) σ).expect F := by
  rw [expect_emit]
  unfold emit
  rw [expect_tensor_map lam (fun i (y : W → X i) => y ∘ σ) F, expect_tensor_eq]
  rfl

/-- Unit mixed bounds of the emissions of the factors give the bound of the emission of the
tensor (`MixedLpBound.tensor`). -/
theorem mixedLpBound_emit_tensor [∀ i, Nonempty (X i)] (lam : ∀ i, FiniteLaw (W → X i))
    (σ : Slot → W) {q : ℝ} (hq : 0 < q) (h : ∀ i, MixedLpBound (emit (lam i) σ) q 1) :
    MixedLpBound (emit (FiniteLaw.tensor lam) σ) q 1 := by
  intro f
  rw [expect_emit_tensor]
  have ht := MixedLpBound.tensor (fun i => emit (lam i) σ) hq (fun _ => 1) (fun _ => zero_le_one) h
  rw [Finset.prod_const_one] at ht
  exact ht f

end Tensor

/-! ## The pair laws of a graph law -/

section GraphLaw

variable {W : Type} [Fintype W] [DecidableEq W] {p : ℕ} [Fact p.Prime]

/-- The two labels of a graph law at distinct vertices are distinct (`hdist`). -/
theorem graphLaw_pair_dist (G : OrientedGraph W) (hne : (injLabellings (ZMod p) G).Nonempty)
    {a b : W} (hab : a ≠ b) (w : Fin 2 → ZMod p) (hw : w 0 = w 1) :
    (pairLaw (graphLaw G hne) (fun y => y a) (fun y => y b)).weight w = 0 := by
  unfold pairLaw FiniteLaw.map
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : ![x a, x b] = w
  · simp only [hx, ↓reduceIte]
    have h0 := congrFun hx 0
    have h1 := congrFun hx 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have hxab : x a = x b := by rw [h0, h1, hw]
    unfold graphLaw
    by_cases hmem : x ∈ injLabellings (ZMod p) G
    · exact absurd (((mem_injLabellings_iff_feasible G x).mp hmem).1 a (mem_univ _) b
        (mem_univ _) hxab) hab
    · simp [hmem]
  · simp only [hx, ↓reduceIte]

/-- The pair law of a graph law at two vertices is invariant under the square-affine maps
`w ↦ s w + u`, `s` a nonzero square (`hinv`; `PartV.graphLaw_expect_affine`). -/
theorem graphLaw_pair_affine (G : OrientedGraph W) (hne : (injLabellings (ZMod p) G).Nonempty)
    (a b : W) (s u : ZMod p) (hs : s ≠ 0) (hsq : IsSquare s) (w : Fin 2 → ZMod p) :
    (pairLaw (graphLaw G hne) (fun y => y a) (fun y => y b)).weight (fun k => s * w k + u) =
      (pairLaw (graphLaw G hne) (fun y => y a) (fun y => y b)).weight w := by
  have hα : quadraticChar (ZMod p) s = 1 := by
    obtain ⟨r, rfl⟩ := hsq
    have hr : r ≠ 0 := fun h => hs (by rw [h, mul_zero])
    rw [← pow_two]
    exact quadraticChar_sq_one' hr
  have hwt : ∀ t : Fin 2 → ZMod p,
      (pairLaw (graphLaw G hne) (fun y => y a) (fun y => y b)).weight t =
        (graphLaw G hne).expect (fun x => if ![x a, x b] = t then 1 else 0) := by
    intro t
    unfold pairLaw FiniteLaw.map FiniteLaw.expect
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : ![x a, x b] = t <;> simp [hx]
  rw [hwt, hwt]
  have h := graphLaw_expect_affine G hne hα u
    (fun x => if ![x a, x b] = (fun k => s * w k + u) then (1 : ℝ) else 0)
  rw [← h]
  refine FiniteLaw.expect_congr _ fun x => ?_
  have hiff : (![s * x a + u, s * x b + u] = fun k => s * w k + u) ↔ (![x a, x b] = w) := by
    constructor
    · intro he
      funext k
      have hk := congrFun he k
      fin_cases k
      · exact mul_left_cancel₀ hs (add_right_cancel hk)
      · exact mul_left_cancel₀ hs (add_right_cancel hk)
    · intro he
      funext k
      rw [← he]
      fin_cases k <;> rfl
  by_cases hc : ![x a, x b] = w
  · simp only [hc, hiff.mpr hc, ↓reduceIte]
  · have hc' : ¬(![s * x a + u, s * x b + u] = fun k => s * w k + u) := fun h' => hc (hiff.mp h')
    simp only [hc, hc', ↓reduceIte]

/-- The pair law of a law at two vertices is distinct if its support separates them. -/
theorem pair_dist_of_support (μ : FiniteLaw (W → ZMod p)) {a b : W}
    (hsupp : ∀ y, μ.weight y ≠ 0 → y a ≠ y b) (w : Fin 2 → ZMod p) (hw : w 0 = w 1) :
    (pairLaw μ (fun y => y a) (fun y => y b)).weight w = 0 := by
  unfold pairLaw FiniteLaw.map
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : ![x a, x b] = w
  · simp only [hx, ↓reduceIte]
    have h0 := congrFun hx 0
    have h1 := congrFun hx 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    by_contra hne
    exact hsupp x hne (by rw [h0, h1, hw])
  · simp only [hx, ↓reduceIte]

/-- The pair law of a law at two vertices is square-affine invariant if the law is. -/
theorem pair_affine_of_expect (μ : FiniteLaw (W → ZMod p))
    (haff : ∀ α : ZMod p, quadraticChar (ZMod p) α = 1 → ∀ (β : ZMod p) (H : (W → ZMod p) → ℝ),
      μ.expect (fun y => H (fun o => α * y o + β)) = μ.expect H)
    (a b : W) (s u : ZMod p) (hs : s ≠ 0) (hsq : IsSquare s) (w : Fin 2 → ZMod p) :
    (pairLaw μ (fun y => y a) (fun y => y b)).weight (fun k => s * w k + u) =
      (pairLaw μ (fun y => y a) (fun y => y b)).weight w := by
  have hα : quadraticChar (ZMod p) s = 1 := by
    obtain ⟨r, rfl⟩ := hsq
    have hr : r ≠ 0 := fun h => hs (by rw [h, mul_zero])
    rw [← pow_two]
    exact quadraticChar_sq_one' hr
  have hwt : ∀ t : Fin 2 → ZMod p, (pairLaw μ (fun y => y a) (fun y => y b)).weight t =
      μ.expect (fun x => if ![x a, x b] = t then 1 else 0) := by
    intro t
    unfold pairLaw FiniteLaw.map FiniteLaw.expect
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : ![x a, x b] = t <;> simp [hx]
  rw [hwt, hwt]
  have h := haff s hα u (fun x => if ![x a, x b] = (fun k => s * w k + u) then (1 : ℝ) else 0)
  rw [← h]
  refine FiniteLaw.expect_congr _ fun x => ?_
  have hiff : (![s * x a + u, s * x b + u] = fun k => s * w k + u) ↔ (![x a, x b] = w) := by
    constructor
    · intro he
      funext k
      have hk := congrFun he k
      fin_cases k
      · exact mul_left_cancel₀ hs (add_right_cancel hk)
      · exact mul_left_cancel₀ hs (add_right_cancel hk)
    · intro he
      funext k
      rw [← he]
      fin_cases k <;> rfl
  by_cases hc : ![x a, x b] = w
  · simp only [hc, hiff.mpr hc, ↓reduceIte]
  · have hc' : ¬(![s * x a + u, s * x b + u] = fun k => s * w k + u) := fun h' => hc (hiff.mp h')
    simp only [hc, hc', ↓reduceIte]

end GraphLaw

/-! ## M1's one-layer rows for graph laws and for block graph laws -/

section Rows

variable {p : ℕ} [Fact p.Prime]

/-- **Row "folded `F₁`"** for a graph law (M1's `catalog72_fold_one`). -/
theorem graphLaw_fold_one (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) (G : OrientedGraph (Fin 3 × Fin 1))
    (hne : (injLabellings (ZMod p) G).Nonempty) (jf : Fin 3) :
    MixedLpBound (emit (graphLaw G hne) (midDiagEmission (Labellings.fold jf))) 66 1 :=
  catalog72_fold_one hp2 hp64 jf (graphLaw G hne)
    (fun w hw => graphLaw_pair_dist G hne (by decide) w hw)
    (fun s u hs hsq w => graphLaw_pair_affine G hne _ _ s u hs hsq w)
    (fun l f => PartV.graphLaw_vertex_uniform G hne l f)

/-- **Row "folded `E₁`"** for a graph law (M1's `catalog72_matching_one`). -/
theorem graphLaw_matching_one (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p)
    (G : OrientedGraph (Fin 3 × Fin 1)) (hne : (injLabellings (ZMod p) G).Nonempty) (sm : Fin 2) :
    MixedLpBound (emit (graphLaw G hne) (midDiagEmission (Labellings.matching sm))) 66 1 :=
  catalog72_matching_one hp2 hp64 sm (graphLaw G hne)
    (fun w hw => graphLaw_pair_dist G hne (by decide) w hw)
    (fun s u hs hsq w => graphLaw_pair_affine G hne _ _ s u hs hsq w)
    (fun l f => PartV.graphLaw_vertex_uniform G hne l f)

/-- **Row "folded `G₁`"** for a graph law (M1's `catalog72_merge_one`). -/
theorem graphLaw_merge_one (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p)
    (G : OrientedGraph (Fin 3 × Fin 1)) (hne : (injLabellings (ZMod p) G).Nonempty)
    (sk : Fin 2 × Fin 3) :
    MixedLpBound (emit (graphLaw G hne)
      (midDiagEmission (fun u => (Labellings.merge sk.1 sk.2 u).castSucc))) 66 1 :=
  catalog72_merge_one hp2 hp64 sk (graphLaw G hne)
    (fun w hw => graphLaw_pair_dist G hne (by decide) w hw)
    (fun s u hs hsq w => graphLaw_pair_affine G hne _ _ s u hs hsq w)
    (fun l f => PartV.graphLaw_vertex_uniform G hne l f)

open Sarkozy.PartVRecords in
/-- **The replacement law of the folded matching records** (A1/V3's `plusLaw`, the matching law
`(a, b, c)` of `lem:density:middle-catalog`): row "folded `E₁`" (M1's `catalog72_matching_one`),
since its queried pair `(y₀, y₁)` is a strict-square edge (`plusLaw_support`) and it is
square-affine invariant (`plusLaw_affine`). -/
theorem plusLaw_matching_one (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p)
    (hF : ringChar (ZMod p) ≠ 2) (h3 : Fintype.card (ZMod p) % 4 = 3) (hk : 0 < kP (ZMod p))
    (sm : Fin 2) :
    MixedLpBound (emit (plusLaw (ZMod p) hF h3 hk) (midDiagEmission (Labellings.matching sm)))
      66 1 :=
  catalog72_matching_one hp2 hp64 sm (plusLaw (ZMod p) hF h3 hk)
    (pair_dist_of_support _ fun y hy he => by
      have h1 := (plusLaw_support hF h3 hk hy).1
      rw [he, sub_self, quadraticChar_zero] at h1
      exact zero_ne_one h1)
    (pair_affine_of_expect _ (fun α hα β H => plusLaw_affine hF h3 hk hα β H) _ _)
    (fun l f => plusLaw_vertex_uniform hF h3 hk l f)

end Rows

section BlockRows

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (hp2 : ∀ i, pr i ≠ 2) (h64 : ∀ i, (64 : ℝ) ≤ pr i)

include hp2 h64 in
/-- The block row "folded `F₁`" (tensor over the primes of the block). -/
theorem block_fold_one (G : OrientedGraph (Fin 3 × Fin 1))
    (hne : ∀ i, (injLabellings (ZMod (pr i)) G).Nonempty) (jf : Fin 3) :
    MixedLpBound (emit (blockGraphLaw pr G hne) (midDiagEmission (Labellings.fold jf))) 66 1 :=
  mixedLpBound_emit_tensor (fun i => graphLaw G (hne i)) _ (by norm_num)
    fun i => graphLaw_fold_one (hp2 i) (h64 i) G (hne i) jf

include hp2 h64 in
/-- The block row "folded `E₁`". -/
theorem block_matching_one (G : OrientedGraph (Fin 3 × Fin 1))
    (hne : ∀ i, (injLabellings (ZMod (pr i)) G).Nonempty) (sm : Fin 2) :
    MixedLpBound (emit (blockGraphLaw pr G hne) (midDiagEmission (Labellings.matching sm))) 66 1 :=
  mixedLpBound_emit_tensor (fun i => graphLaw G (hne i)) _ (by norm_num)
    fun i => graphLaw_matching_one (hp2 i) (h64 i) G (hne i) sm

include hp2 h64 in
/-- The block row "folded `G₁`". -/
theorem block_merge_one (G : OrientedGraph (Fin 3 × Fin 1))
    (hne : ∀ i, (injLabellings (ZMod (pr i)) G).Nonempty) (sk : Fin 2 × Fin 3) :
    MixedLpBound (emit (blockGraphLaw pr G hne)
      (midDiagEmission (fun u => (Labellings.merge sk.1 sk.2 u).castSucc))) 66 1 :=
  mixedLpBound_emit_tensor (fun i => graphLaw G (hne i)) _ (by norm_num)
    fun i => graphLaw_merge_one (hp2 i) (h64 i) G (hne i) sk

include hp2 h64 in
open Sarkozy.PartVRecords in
/-- The block row for the block replacement law `blockPlusLaw` (tensor over the primes). -/
theorem block_plus_matching_one (h : ClassThreeBlock pr) (sm : Fin 2) :
    MixedLpBound (emit (blockPlusLaw pr h) (midDiagEmission (Labellings.matching sm))) 66 1 :=
  mixedLpBound_emit_tensor (fun i => plusLaw (ZMod (pr i)) (h.ringChar_ne i) (h.card_mod i)
      (h.kP_pos' i)) _ (by norm_num)
    fun i => plusLaw_matching_one (hp2 i) (h64 i) _ _ _ sm

end BlockRows

/-! ## The record moments of a middle block -/

/-- **A multiple of a probability law with unit mixed `L^{66}` has the record moment** at every
`0 < θ ≤ 12/11` (`66 ≤ 72/θ`; the density endpoint `12/11` of the catalog). -/
theorem recordMoment_smul_law {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (μ : FiniteLaw (Slot → X)) (h : MixedLpBound μ 66 1) {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 12 / 11) (c : ℝ) : RecordMoment (c • signedIntegral μ.weight) θ := by
  intro hm
  have hmass : mass (c • signedIntegral μ.weight) = c := by
    change c * μ.expect (fun _ => 1) = c
    rw [μ.expect_const, mul_one]
  rw [hmass] at hm
  refine ⟨μ, fun z => ?_, ?_⟩
  · rw [hmass]
    change μ.weight z = c * lawDensity (signedIntegral μ.weight) z / c
    rw [Structured.lawDensity_signedIntegral_eq]
    field_simp
  · refine MixedLpBound.mono_exponent h zero_le_one (by norm_num) ?_
    rw [le_div_iff₀ hθ]
    linarith

section Middle

open Sarkozy.FirstStagePaper Sarkozy.PartVRecords

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h64 : ∀ i, (64 : ℝ) ≤ pr i)
  (hne : MiddleNonempty pr) (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr))
  (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (bmin : ℝ) (h : ClassThreeBlock pr)

include h64 in
/-- **The six first-stage records of a middle block have the record moment**
(`lem:density:middle-catalog`, rows "folded `F₁`", "folded `E₁`", "folded `G₁`"; M1's
`catalog72_*_one`), at every `0 < θ ≤ 12/11`. -/
theorem middle_rhoRecs_moment {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 12 / 11) (i : Fin 6) :
    RecordMoment (rhoRecs pr hne root W I hr bmin h i) θ := by
  have hp2 : ∀ i, pr i ≠ 2 := fun i => by have := h.mod4 i; omega
  have hF : ∀ j : Fin 3, RecordMoment (signedIntegral (emit (blockGraphLaw pr (foldGraph (Fin 1))
      hne.F1) (midDiagEmission (Labellings.fold j))).weight) θ := fun j => by
    have := recordMoment_smul_law _ (block_fold_one pr hp2 h64 _ hne.F1 j) hθ hθ' 1
    rwa [one_smul] at this
  have hE : ∀ s : Fin 2, RecordMoment (signedIntegral (emit (blockGraphLaw pr (matchGraph (Fin 1))
      hne.E1) (midDiagEmission (Labellings.matching s))).weight) θ := fun s => by
    have := recordMoment_smul_law _ (block_matching_one pr hp2 h64 _ hne.E1 s) hθ hθ' 1
    rwa [one_smul] at this
  have hG : ∀ sk : Fin 2 × Fin 3, RecordMoment (signedIntegral (emit (blockGraphLaw pr
      (matchGraph (Fin 1)) hne.E1)
      (midDiagEmission (fun u => (Labellings.merge sk.1 sk.2 u).castSucc))).weight) θ :=
      fun sk => by
    have := recordMoment_smul_law _ (block_merge_one pr hp2 h64 _ hne.E1 sk) hθ hθ' 1
    rwa [one_smul] at this
  fin_cases i
  · exact hF 1
  · exact hF 2
  · exact hE 0
  · exact hE 1
  · exact hG (0, 0)
  · exact hG (1, 1)

include h64 in
/-- **The replacement records `κ'_s` have the record moment** (the matching law `(a, b, c)` of
the catalog, through row "folded `E₁`"). -/
theorem middle_newRecN_moment {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 12 / 11) (s : Fin 2) :
    RecordMoment ((middleFrame pr hne root W I hr bmin h).newRecN s) θ := by
  have hp2 : ∀ i, pr i ≠ 2 := fun i => by have := h.mod4 i; omega
  rw [middle_newRecN]
  exact recordMoment_smul_law _ (block_plus_matching_one pr hp2 h64 h s) hθ hθ' _

include h64 in
/-- **The folded matching records `κ_s` have the record moment** (row "folded `E₁`"). -/
theorem middle_oldRec_moment {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 12 / 11) (s : Fin 2) :
    RecordMoment ((middleFrame pr hne root W I hr bmin h).oldRec s) θ := by
  have hp2 : ∀ i, pr i ≠ 2 := fun i => by have := h.mod4 i; omega
  rw [middle_oldRec]
  exact recordMoment_smul_law _ (block_matching_one pr hp2 h64 _ hne.E1 s) hθ hθ' _

/-- **The remaining moment input of a middle block**: the sharp folds of the two differences
`κ'_s − κ_s` (at `tagCut s`, constant `d`): a sharp decomposition whose normalized full folded laws
have unit mixed `L^{72/θ}` (`lem:density:middle-catalog`, "the additional first-stage matching law
… its own private sharp fold"). -/
abbrev MiddleRemaining (d θ : ℝ) : Type 1 :=
  ∀ s : Fin 2, SharpFoldData (tagCut s) ((middleFrame pr hne root W I hr bmin h).oldRec s)
    ((middleFrame pr hne root W I hr bmin h).newRecN s -
      (middleFrame pr hne root W I hr bmin h).oldRec s) d θ

include h64 in
/-- **The moment inputs of a middle block** from the sharp folds: the six records, `κ_s` and `κ'_s`
are proved (`middle_rhoRecs_moment`, `middle_oldRec_moment`, `middle_newRecN_moment`). -/
noncomputable def AtomStageMoments.ofMiddle
    (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) I.f₁ I.h₁ r)
    {d : ℝ} (hd : 0 ≤ d) (hs : BlockSharp pr hne h d) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 12 / 11)
    (R : MiddleRemaining pr hne root W I hr bmin h d θ) :
    AtomStageMoments (middleStage pr hne root W I hr bmin h hrows₁ hd hs) θ where
  fold := R
  momA := middle_rhoRecs_moment pr h64 hne root W I hr bmin h hθ hθ'
  mom := middle_oldRec_moment pr h64 hne root W I hr bmin h hθ hθ'
  mom' := middle_newRecN_moment pr h64 hne root W I hr bmin h hθ hθ'

end Middle

/-! ## The paper's class-three blocks -/

section Paper

open Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.FirstStagePaper

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

omit [Fintype B] [DecidableEq B] in
/-- The primes of a class-three block are at least `64` (at least `Q₃`). -/
theorem paper_blockPrimes_ge64 (b : B) (j : {j : PaperJ0 // paperAtomMap blockOf j = .inr b}) :
    (64 : ℝ) ≤ blockPrimes blockOf b j := by
  have h := (blockPrimes_mod_ge b j).2
  have h' : 64 ≤ blockPrimes blockOf b j := le_trans (by norm_num [PartV.Q3]) h
  exact_mod_cast h'

variable (blockOf) in
/-- **The remaining moment input of a class-three block** (`lem:density:middle-catalog`, the sharp
folds of the two first-stage differences): nothing at an upper block, `MiddleRemaining` at a middle
block, for its root. -/
noncomputable def SpecRemaining (In : FirstStageInputs blockOf) (θ : ℝ) {b : B} :
    PaperBlockSpec blockOf b → Type 1
  | .upper _ => PUnit
  | .middleUniform M => MiddleRemaining (blockPrimes blockOf b) M.hne
      (uniformRoot (blockPrimes blockOf b) M.hne) M.W M.I M.hr (In.bmin b)
      (classThree_blockPrimes b) (blockConst (In.X b) (In.bmin b)) θ
  | .middleIndividual M => MiddleRemaining (blockPrimes blockOf b) M.hne
      (individualBlockRoot (blockPrimes blockOf b) M.u M.hne.L2) M.W M.I M.hr (In.bmin b)
      (classThree_blockPrimes b) (blockConst (In.X b) (In.bmin b)) θ
  | .middleCoherent M => MiddleRemaining (blockPrimes blockOf b) M.hne
      (coherentBlockRoot (blockPrimes blockOf b) M.D M.u M.hη M.hne.L2) M.W M.I M.hr (In.bmin b)
      (classThree_blockPrimes b) (blockConst (In.X b) (In.bmin b)) θ

/-- **The per-block moment inputs of the paper's first stage from the sharp folds** (for
`0 < θ ≤ 12/11`): the records of every class-three block have their moments by M1's catalog. -/
noncomputable def specStageMoments (hW : Target.Weil) (In : FirstStageInputs blockOf) {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 12 / 11) {b : B} :
    (S : PaperBlockSpec blockOf b) → SpecRemaining blockOf In θ S →
      AtomStageMoments (specStage hW In S) θ
  | .upper _, _ => AtomStageMoments.trivial _ _ _ _ θ
  | .middleUniform M, R => AtomStageMoments.ofMiddle (blockPrimes blockOf b)
      (paper_blockPrimes_ge64 b) M.hne _ M.W M.I M.hr (In.bmin b) (classThree_blockPrimes b)
      M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b)) (In.sharp b M.hne) hθ hθ' R
  | .middleIndividual M, R => AtomStageMoments.ofMiddle (blockPrimes blockOf b)
      (paper_blockPrimes_ge64 b) M.hne _ M.W M.I M.hr (In.bmin b) (classThree_blockPrimes b)
      M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b)) (In.sharp b M.hne) hθ hθ' R
  | .middleCoherent M, R => AtomStageMoments.ofMiddle (blockPrimes blockOf b)
      (paper_blockPrimes_ge64 b) M.hne _ M.W M.I M.hr (In.bmin b) (classThree_blockPrimes b)
      M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b)) (In.sharp b M.hne) hθ hθ' R

end Paper

end Sarkozy.EnvelopeEnergiesPaper
