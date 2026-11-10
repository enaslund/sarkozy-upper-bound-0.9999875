module

public import Sarkozy.NormBoundsPaper3.MatchPrime

@[expose] public section

/-!
# The skew norm of the matching replacements (`lem:record:exact-marginal-e`(ii), `Ea`; NB3)

`paper/sections/21_middle_records.tex`, `lem:record:exact-marginal-e`(ii): "the block differences
`⊗_{p∈𝔅} K_{1,p} − ⊗_{p∈𝔅} K^E_{0,p}` of `E₀` and `E₁` have, on `L²(⊗_p ν_{E,p})`, … skew part
of norm at most `a_E(X) b^{-1/2}`"; proof: "The prime operators are Markov operators of couplings
with exact marginals `ν_{E,p}`, so by `lem:sector`(a),(b) the block difference vanishes on the
empty sector, is the prime difference on the singleton sectors, and the norms of its symmetric and
skew parts are the maxima over the sectors. On a singleton `{p}` they are at most …
`a_E(X) b^{-1/2}`.
… On a sector `S` with `|S| ≥ 3` the reference tensor is self-adjoint, so the skew part is that of
the new tensor (`lem:sector`(b)), of norm at most `(κ_E(X) b^{-1/2})³`."

The proof here is the paper's, with one simplification: the old record `⊗ K^E_0` is symmetric at
the reserved cut (V1's `E` law is invariant under the layer swap, `form_oldE_symm`) on the whole
space, so the skew part of the change is the skew part of `⊗ K₁` (`form_match_skew`), and on every
sector of at least two primes it is bounded by the square of the prime centred norm of `K₁`
(NB2's `change_le` with `(α₁, α₂, β) = (½, −½, 0)`), without the finer `lem:sector`(h).

* `hfE`, `oldE_half`, `oldE_flip`, `newE_half`, `newE_flip`: the halves of a matching record at the
  reserved cut are the triples of the two layers;
* `lift3`, **`expect_tensor_cmT`**: the cut form of a tensor law read at two triples is the form of
  the product coupling on `∏_p 𝔽_p³`;
* `oldE`, **`form_oldE_symm`**, **`hsq_oldE`** (the actual half law is `⊗_p ν_E`, `tw_match`),
  `form_newE`, **`form_match_skew`**;
* **`match_skew`**: the field `Ea` for any bound `e` above the prime constants `aEp p` and above
  `ρ²`, `ρ ≥ rhoE p`;
* numbers: `f_mono` (`p(p + 2)/(p² − 3p + 4)` decreases), `aEp_le`, `rhoE_le`;
* **`match_skew_paper`**: `Ea` at `a_E · b^{-1/2}` for a piece start `X ≥ 16`, `X ≤ b`,
  `2^8 ≤ b ≤ p` and `X(X + 2)/(X² − 3X + 4) ≤ a_E`. The paper's `a_E(X) = (1 + 2q)/((1 − q)(1 − 2q))
  = X(X + 2)/((X − 1)(X − 2))` is above this (`aE_ge`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper3

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.SignedComponents
open Sarkozy.IndexSupport Sarkozy.Mixing Sarkozy.SignedGram
open Sarkozy.NormBoundsPaper (form_emit_gen hsq_emit_gen half_layer flip_layer flip_fst)
open Sarkozy.NormBoundsPaper2 (ip chg chg1 change_le prod_ite01 centredNorm_mono)

/-! ## The halves of a matching record -/

section Cut

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The half configuration of a matching record `E_s` with layer labels `a, b, c` (objects
`0, 1, 2`). -/
def hfE (s : Fin 2) (a b c : X) : reservedCut.Half → X :=
  fun v => ![a, b, c] (matching s v.1.1)

omit [Fintype X] [DecidableEq X] in
theorem oldE_half (s : Fin 2) (y : Fin 3 × Fin 2 → X) :
    (fun v : reservedCut.Half => (y ∘ midEmission (matching s)) v.1) =
      hfE s (y (0, 0)) (y (1, 0)) (y (2, 0)) := by
  funext v
  simp only [Function.comp_apply, midEmission, half_layer v.1 v.2, hfE]
  generalize matching s v.1.1 = m
  fin_cases m <;> rfl

omit [Fintype X] [DecidableEq X] in
theorem oldE_flip (s : Fin 2) (y : Fin 3 × Fin 2 → X) :
    (fun v : reservedCut.Half => (y ∘ midEmission (matching s)) (reservedCut.flip v.1)) =
      hfE s (y (0, 1)) (y (1, 1)) (y (2, 1)) := by
  funext v
  simp only [Function.comp_apply, midEmission, flip_layer v.1 v.2, flip_fst, hfE]
  generalize matching s v.1.1 = m
  fin_cases m <;> rfl

end Cut

/-! ## Triple functions on the block -/

section Bridge

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

/-- A function of three block labels as a function on `∏_i 𝔽_{p_i}³`. -/
def lift3 (φ : BlockLabel pr → BlockLabel pr → BlockLabel pr → ℝ) :
    (∀ i, (ZMod (pr i) × ZMod (pr i)) × ZMod (pr i)) → ℝ :=
  fun x => φ (fun i => (x i).1.1) (fun i => (x i).1.2) (fun i => (x i).2)

/-- **The form of a tensor law read at two triples is the form of the product coupling.** -/
theorem expect_tensor_cmT {W : Type} [Fintype W] [DecidableEq W]
    (μ : ∀ i, FiniteLaw (W → ZMod (pr i))) (u v : Fin 3 → W)
    (φ ψ : BlockLabel pr → BlockLabel pr → BlockLabel pr → ℝ) :
    (FiniteLaw.tensor μ).expect (fun y => φ (y (u 0)) (y (u 1)) (y (u 2)) *
        ψ (y (v 0)) (y (v 1)) (y (v 2))) =
      lift3 φ ⬝ᵥ (piKron (fun i => cmT (μ i) u v) *ᵥ lift3 ψ) := by
  rw [expect_tensor_eq_sum]
  set X : (∀ i, W → ZMod (pr i)) → ∀ i, (ZMod (pr i) × ZMod (pr i)) × ZMod (pr i) :=
    fun z i => rd (z i) u
  set Y : (∀ i, W → ZMod (pr i)) → ∀ i, (ZMod (pr i) × ZMod (pr i)) × ZMod (pr i) :=
    fun z i => rd (z i) v
  have key : ∀ x y : ∀ i, (ZMod (pr i) × ZMod (pr i)) × ZMod (pr i),
      ∏ i, cmT (μ i) u v (x i) (y i) =
        ∑ z : ∀ i, W → ZMod (pr i), (∏ i, (μ i).weight (z i)) *
          (if x = X z ∧ y = Y z then 1 else 0) := by
    intro x y
    unfold cmT
    rw [Fintype.prod_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [prod_mul_distrib, prod_ite01]
    congr 1
    refine if_congr ?_ rfl rfl
    constructor
    · intro hc
      exact ⟨funext fun i => (hc i).1.symm, funext fun i => (hc i).2.symm⟩
    · rintro ⟨hx, hy⟩ i
      subst hx hy
      exact ⟨rfl, rfl⟩
  simp only [dotProduct, Matrix.mulVec, piKron_apply, key, sum_mul, mul_sum]
  have inner : ∀ x, ∑ y, ∑ z, lift3 φ x * ((∏ i, (μ i).weight (z i)) *
      (if x = X z ∧ y = Y z then (1 : ℝ) else 0) * lift3 ψ y) =
      ∑ z, ∑ y, lift3 φ x * ((∏ i, (μ i).weight (z i)) *
      (if x = X z ∧ y = Y z then (1 : ℝ) else 0) * lift3 ψ y) := fun x => sum_comm
  rw [sum_congr rfl fun x _ => inner x, sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [sum_eq_single (X z)]
  · rw [sum_eq_single (Y z)]
    · simp only [and_self, ↓reduceIte, mul_one]
      unfold lift3
      simp only [X, Y, rd]
      ring
    · intro y _ hy
      simp [hy]
    · exact fun h => absurd (mem_univ _) h
  · intro x _ hx
    refine sum_eq_zero fun y _ => ?_
    simp [hx]
  · exact fun h => absurd (mem_univ _) h

theorem piKron_mulVec_one {A : ι → Type} [∀ i, Fintype (A i)] (C : ∀ i, Matrix (A i) (A i) ℝ)
    (x : ∀ i, A i) : (piKron C *ᵥ fun _ => (1 : ℝ)) x = ∏ i, ∑ b, C i (x i) b := by
  simp only [Matrix.mulVec, dotProduct, piKron_apply, mul_one]
  exact (Fintype.prod_sum (fun i b => C i (x i) b)).symm

end Bridge

/-! ## The records at the reserved cut -/

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- The old matching record `E_s` (V1's `E` law placed by `E_s`) as a measure. -/
noncomputable abbrev oldE (s : Fin 2) : SlotMeasure (BlockLabel pr) :=
  signedIntegral (emit (lawE pr hne) (midEmission (matching s))).weight

/-- The value of a half function on the matching half `(a, b, c)`. -/
abbrev me (s : Fin 2) (F : (reservedCut.Half → BlockLabel pr) → ℝ) (a b c : BlockLabel pr) : ℝ :=
  F (hfE s a b c)

/-- **The old matching record is symmetric at the reserved cut** (the `E` law is invariant under
the layer swap). -/
theorem form_oldE_symm (s : Fin 2) (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (oldE pr hne s) G F = reservedCut.form (oldE pr hne s) F G := by
  rw [form_emit_gen _ _ _ _ (oldE_half s) (oldE_flip s),
    form_emit_gen _ _ _ _ (oldE_half s) (oldE_flip s)]
  let π : Fin 3 × Fin 2 ≃ Fin 3 × Fin 2 := Equiv.prodCongr (Equiv.refl _) (Equiv.swap 0 1)
  have hπ := blockGraphLaw_expect_auto pr (matchGraph (Fin 2)) hne.E2 π
    (matchGraph_auto (Fin 2) π)
    (fun y => F (hfE s (y (0, 0)) (y (1, 0)) (y (2, 0))) *
      G (hfE s (y (0, 1)) (y (1, 1)) (y (2, 1))))
  rw [← hπ]
  refine FiniteLaw.expect_congr _ fun y => ?_
  simp only [Function.comp_apply, π, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id_eq]
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right, mul_comm]

/-- **The actual half law of the matching record is `⊗_p ν_E`.** -/
theorem hsq_oldE (s : Fin 2) (F : (reservedCut.Half → BlockLabel pr) → ℝ) :
    hsq reservedCut
        (plusMarginal reservedCut (emit (lawE pr hne) (midEmission (matching s))).weight) F =
      ip (fun i => m3 (pr i)) (lift3 (me pr s F)) (lift3 (me pr s F)) := by
  rw [hsq_emit_gen _ _ _ (oldE_half s)]
  have e : (lawE pr hne).expect (fun y => F (hfE s (y (0, 0)) (y (1, 0)) (y (2, 0))) *
      F (hfE s (y (0, 0)) (y (1, 0)) (y (2, 0)))) =
      (lawE pr hne).expect (fun y =>
        (fun a b c => me pr s F a b c * me pr s F a b c) (y (lay 0 0)) (y (lay 0 1)) (y (lay 0 2)) *
        (fun _ _ _ => (1 : ℝ)) (y (lay 1 0)) (y (lay 1 1)) (y (lay 1 2))) :=
    FiniteLaw.expect_congr _ fun y => by simp only [mul_one]; rfl
  rw [e]
  unfold lawE blockGraphLaw
  refine (expect_tensor_cmT (fun i => graphLaw (matchGraph (Fin 2)) (hne.E2 i)) (lay 0) (lay 1)
    (fun a b c => me pr s F a b c * me pr s F a b c) (fun _ _ _ => 1)).trans ?_
  have hp3 : ∀ i, 3 ≤ pr i := fun i => by
    obtain ⟨z, hz⟩ := hne.E2 i
    rw [mem_injLabellings_iff_feasible] at hz
    have hinj : Function.Injective z := fun u v e => hz.1 u (mem_univ _) v (mem_univ _) e
    have := Fintype.card_le_of_injective z hinj
    simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card] at this
    omega
  have hone : (lift3 (pr := pr) fun _ _ _ => (1 : ℝ)) = fun _ => 1 := rfl
  rw [hone]
  unfold ip
  simp only [dotProduct, Matrix.mulVec_diagonal, piKron_mulVec_one, cmT_row]
  refine sum_congr rfl fun x _ => ?_
  have : ∏ i, tw (graphLaw (matchGraph (Fin 2)) (hne.E2 i)) (lay 0) (x i) =
      Mixing.prodW (fun i => m3 (pr i)) x := by
    unfold Mixing.prodW
    exact prod_congr rfl fun i _ => tw_match (hne.E2 i) (hp3 i) 0 (x i)
  rw [this]
  unfold lift3
  ring

/-- The matching replacement's form is the form of `⊗_p K₁`. -/
theorem form_newE (s : Fin 2) (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (signedIntegral (matchRec pr h s).weight) F G =
      lift3 (me pr s F) ⬝ᵥ
        (piKron (fun i => P3 (blockE_nonempty pr h i)) *ᵥ lift3 (me pr s G)) := by
  unfold matchRec
  rw [form_emit_gen _ _ _ _ (oldE_half s) (oldE_flip s)]
  exact expect_tensor_cmT _ (lay 0) (lay 1) (me pr s F) (me pr s G)

/-- **The skew part of the matching change** is the skew part of `⊗_p K₁`. -/
theorem form_match_skew (s : Fin 2) (C : FoldComponents pr hne) (t : ℝ)
    (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (foldChange pr h hne root W I hr b C t (.inr (.inl s)) .skew) F G =
      chg (fun i => P3 (blockE_nonempty pr h i)) (fun i => P3 (blockE_nonempty pr h i))
        (1 / 2) (-1 / 2) 0 (lift3 (me pr s F)) (lift3 (me pr s G)) := by
  have hS : ∀ L₁ L₂ : SlotMeasure (BlockLabel pr), ∀ F G,
      reservedCut.form (L₁ - L₂) F G = reservedCut.form L₁ F G - reservedCut.form L₂ F G :=
    fun _ _ _ _ => rfl
  change reservedCut.form (skewPart reservedCut
    (signedIntegral (matchRec pr h s).weight - oldE pr hne s)) F G = _
  unfold skewPart
  rw [form_smul, hS, form_reflect, hS, hS, form_oldE_symm pr hne s F G, form_newE, form_newE]
  unfold chg
  ring

end Frame

end Sarkozy.NormBoundsPaper3
