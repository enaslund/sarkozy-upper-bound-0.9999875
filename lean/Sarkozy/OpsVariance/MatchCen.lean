module

public import Sarkozy.OpsVariance.RecordLaws
public import Sarkozy.Variance.MatchingNorm

@[expose] public section

/-!
# (Cen) for the matching records of a middle block (`lem:record:paired-e-bridge`(b))

`paper/sections/22_variance.tex`, `lem:record:paired-e-bridge`(b) ("`E^X_s` is symmetric at `ι`
with centred norm at most `k_{E,m}`"), `subsec:variance:eligible`;
`paper/sections/21_middle_records.tex`, `lem:record:e-law`(b) ("on mean-zero functions `K^E_0` has
… exact value there `3/(p − 3)`"), `lem:record:exact-marginal-e` ("the block record is the tensor
product over the primes").

W1 proved the centred norm `3/(n − 3)` of the disjoint-triple coupling on two slots
(`centredNormLe_disjCoupling`) and listed two steps as not formalized: the identification of the
record on the 72 slots with that coupling, and the tensor product over the primes of a block. Both
are done here:

* `injective_iff_layers`: a labelling of `Fin 3 × Fin 2` is injective iff its two layers are
  injective and disjoint (`DisjTriple`);
* **`form_matchRecord`**: at one prime, the cut form at `ι` of V1's matching record
  `emit (graphLaw matchGraph) (midEmission (matching s))` is `c` times that of W1's disjoint-triple
  coupling, read through the pattern (`c > 0`);
* **`centredNormLe_matchRecord`**: its centred norm relative to its half marginal is at most
  `3/(p − 3)`;
* **`centredNormLe_blockMatch`**: at a middle block whose primes are all `≥ b₀ ≥ 7`, the matching
  record `Π_{E_s}` (V1's block `E` law emitted by `E_s`) has centred norm `≤ 3/(b₀ − 3)` relative
  to its half marginal (`centredNormLe_emit_tensor`); with `blockMatch_symm` and
  `blockMatch_minus` (symmetric, equal half marginals) these are the hypotheses `ht`, `hn`,
  `hcen` of `hres_of_restoration` for the aligned matching classes.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.RecordExpansion Sarkozy.Variance Sarkozy.Labellings
open Sarkozy.TraceMixing (DisjTriple)
open Sarkozy.SignedComponents (halfRead)

section Prime

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] [DecidableEq F] in
/-- A labelling of `Fin 3 × Fin 2` is injective iff its layers are injective and disjoint. -/
theorem injective_iff_layers (y : Fin 3 × Fin 2 → F) :
    Function.Injective y ↔
      Function.Injective (fun o => y (o, 0)) ∧
        DisjTriple (fun o => y (o, 0)) (fun o => y (o, 1)) := by
  constructor
  · intro h
    refine ⟨fun a b e => ?_, fun a b e => ?_, fun i j e => ?_⟩
    · exact (Prod.mk.inj (h e)).1
    · exact (Prod.mk.inj (h e)).1
    · exact absurd (Prod.mk.inj (h e)).2 Fin.zero_ne_one
  · rintro ⟨h0, h1, hd⟩ ⟨a, ℓ⟩ ⟨b, ℓ'⟩ e
    rcases Fin.exists_fin_two.mp ⟨ℓ, rfl⟩ with rfl | rfl <;>
      rcases Fin.exists_fin_two.mp ⟨ℓ', rfl⟩ with rfl | rfl
    · rw [h0 e]
    · exact absurd e (hd a b)
    · exact absurd e.symm (hd b a)
    · rw [h1 e]

/-- The pattern reading of a triple on the plus half of `ι`. -/
def readT (φ : ZMod 6 → Fin 3) (t : Fin 3 → F) : reservedCut.Half → F := fun v => t (φ v.1.1)

/-- A function of the halves of `ι`, as a function of the halves of the two-slot cut. -/
def liftT (φ : ZMod 6 → Fin 3) (H : (reservedCut.Half → F) → ℝ) :
    (twoSlotCut.Half → (Fin 3 → F)) → ℝ := fun xh => H (readT φ (xh tPlus))

omit [Field F] in
/-- The cut form at `ι` of an emitted two-layer law: `E[H(z₊) K(z₋)]`. -/
theorem form_emit_eq (lam : FiniteLaw (Fin 3 × Fin 2 → F)) (φ : ZMod 6 → Fin 3)
    (H K : (reservedCut.Half → F) → ℝ) :
    reservedCut.form (signedIntegral (emit lam (midEmission φ)).weight) H K =
      ∑ y, lam.weight y * (H (readT φ (fun o => y (o, 0))) * K (readT φ (fun o => y (o, 1)))) := by
  unfold ReflectionCut.form
  change (emit lam (midEmission φ)).expect _ = _
  rw [expect_emit]
  unfold FiniteLaw.expect
  refine sum_congr rfl fun y _ => ?_
  have h1 : (fun v : reservedCut.Half => (y ∘ midEmission φ) v.1) = halfRead φ y 0 :=
    SignedComponents.plusHalf_mid (X := F) φ y
  have h2 : (fun v : reservedCut.Half => (y ∘ midEmission φ) (reservedCut.flip v.1)) =
      halfRead φ y 1 := SignedComponents.minusHalf_mid (X := F) φ y
  beta_reduce
  rw [h1, h2]
  rfl

variable (F) in
/-- The normalizing ratio `c = D/N` of V1's `E` law against W1's coupling. -/
noncomputable def ratioE : ℝ :=
  ((Fintype.card F - 3).descFactorial 3 : ℝ) / ((injLabellings F (matchGraph (Fin 2))).card : ℝ)

theorem ratioE_pos (hne : (injLabellings F (matchGraph (Fin 2))).Nonempty)
    (hn : 7 ≤ Fintype.card F) : 0 < ratioE F := by
  unfold ratioE
  apply div_pos
  · have : 0 < (Fintype.card F - 3).descFactorial 3 := Nat.descFactorial_pos.mpr (by omega)
    exact_mod_cast this
  · exact_mod_cast card_pos.mpr hne

/-- **V1's matching record at one prime is W1's disjoint-triple coupling, up to the constant
`c > 0`**: `Q_{Π_{E_s}}(H, K) = c Q_{disj}(H ∘ read, K ∘ read)`. -/
theorem form_matchRecord (hne : (injLabellings F (matchGraph (Fin 2))).Nonempty)
    (hn : 7 ≤ Fintype.card F) (φ : ZMod 6 → Fin 3) (H K : (reservedCut.Half → F) → ℝ) :
    reservedCut.form (signedIntegral (emit (graphLaw (matchGraph (Fin 2)) hne)
        (midEmission φ)).weight) H K =
      ratioE F * twoSlotCut.form (disjCoupling (F := F)) (liftT φ H) (liftT φ K) := by
  rw [form_emit_eq]
  change _ = ratioE F * ∑ z, disjWeight z * (liftT φ H (fun v => z v.1) *
    liftT φ K (fun v => z (twoSlotCut.flip v.1)))
  have hz1 : ∀ z : Bool → (Fin 3 → F), (fun v : twoSlotCut.Half => z v.1) = fun _ => z true := by
    intro z
    funext v
    rw [half_eq_tPlus v]
    rfl
  have hz2 : ∀ z : Bool → (Fin 3 → F),
      (fun v : twoSlotCut.Half => z (twoSlotCut.flip v.1)) = fun _ => z false := by
    intro z
    funext v
    rw [half_eq_tPlus v, flip_tPlus]
  simp_rw [hz1, hz2]
  rw [mul_sum]
  -- reindex the labellings by their two layers
  let e : (Fin 3 × Fin 2 → F) ≃ (Bool → (Fin 3 → F)) :=
    { toFun := fun y b => if b then fun o => y (o, 0) else fun o => y (o, 1)
      invFun := fun z w => if w.2 = 0 then z true w.1 else z false w.1
      left_inv := fun y => by
        funext w
        rcases w with ⟨o, ℓ⟩
        rcases Fin.exists_fin_two.mp ⟨ℓ, rfl⟩ with rfl | rfl <;> simp
      right_inv := fun z => by
        funext b
        cases b <;> simp }
  rw [← Equiv.sum_comp e]
  refine sum_congr rfl fun y _ => ?_
  change _ = ratioE F * (disjWeight (e y) *
    (H (readT φ (fun o => y (o, 0))) * K (readT φ (fun o => y (o, 1)))))
  -- the weights
  have hw : (graphLaw (matchGraph (Fin 2)) hne).weight y =
      if Function.Injective y then 1 / ((injLabellings F (matchGraph (Fin 2))).card : ℝ)
      else 0 := by
    change (if y ∈ injLabellings F (matchGraph (Fin 2)) then _ else _) = _
    congr 1
    rw [mem_injLabellings_iff_feasible]
    apply propext
    constructor
    · intro h a b hab
      exact h.1 a (mem_univ a) b (mem_univ b) hab
    · intro h
      refine ⟨fun a _ b _ hab => h hab, fun e he => ?_⟩
      simp [matchGraph] at he
  have hdw : disjWeight (e y) =
      if Function.Injective (fun o => y (o, 0)) ∧
        DisjTriple (fun o => y (o, 0)) (fun o => y (o, 1)) then
        ((Fintype.card F - 3).descFactorial 3 : ℝ)⁻¹ else 0 := rfl
  have hD : ((Fintype.card F - 3).descFactorial 3 : ℝ) ≠ 0 := by
    have : 0 < (Fintype.card F - 3).descFactorial 3 := Nat.descFactorial_pos.mpr (by omega)
    exact_mod_cast this.ne'
  have hwy : (graphLaw (matchGraph (Fin 2)) hne).weight y = ratioE F * disjWeight (e y) := by
    rw [hw, hdw]
    by_cases hy : Function.Injective y
    · have h2 := (injective_iff_layers y).mp hy
      simp only [hy, h2, and_self, ↓reduceIte]
      unfold ratioE
      field_simp
    · have h2 : ¬ (Function.Injective (fun o => y (o, 0)) ∧
          DisjTriple (fun o => y (o, 0)) (fun o => y (o, 1))) :=
        fun h => hy ((injective_iff_layers y).mpr h)
      simp only [hy, h2, ↓reduceIte, mul_zero]
  rw [hwy]
  ring

/-- **(Cen) at one prime** (`lem:record:paired-e-bridge`(b) at one prime, through W1's
`centredNormLe_disjCoupling`): V1's matching record emitted by any pattern `φ` with values in the
three objects has centred norm `≤ 3/(n − 3)` relative to its half marginal. -/
theorem centredNormLe_matchRecord (hne : (injLabellings F (matchGraph (Fin 2))).Nonempty)
    (hn : 7 ≤ Fintype.card F) (φ : ZMod 6 → Fin 3) :
    CentredNormLe reservedCut (signedIntegral (emit (graphLaw (matchGraph (Fin 2)) hne)
        (midEmission φ)).weight)
      (plusMarginal reservedCut (emit (graphLaw (matchGraph (Fin 2)) hne) (midEmission φ)).weight)
      (3 / ((Fintype.card F : ℝ) - 3)) := by
  set R := emit (graphLaw (matchGraph (Fin 2)) hne) (midEmission φ) with hR
  set c := ratioE F with hc
  have hc0 : 0 < c := ratioE_pos hne hn
  have hsum : ∀ H : (reservedCut.Half → F) → ℝ,
      ∑ x, plusMarginal reservedCut R.weight x * H x =
        c * ∑ xh, tripleMarginal xh * liftT φ H xh := by
    intro H
    rw [← form_signedIntegral_one_right, form_matchRecord hne hn φ H 1,
      show liftT φ (1 : (reservedCut.Half → F) → ℝ) = 1 from rfl,
      disjCoupling_marginal (F := F) (by omega)]
  have hcen := centredNormLe_disjCoupling (F := F) hn
  intro H K
  have hHK := hcen (liftT φ H) (liftT φ K)
  rw [form_matchRecord hne hn φ H K, hsum H, hsum K]
  have h1 := hsum (fun _ => 1)
  have hsq : ∀ G : (reservedCut.Half → F) → ℝ,
      ∑ x, plusMarginal reservedCut R.weight x * G x ^ 2 =
        c * ∑ xh, tripleMarginal xh * liftT φ G xh ^ 2 := fun G => hsum (fun x => G x ^ 2)
  have hone : ∑ x, plusMarginal reservedCut R.weight x =
      c * ∑ xh, tripleMarginal (F := F) xh := by
    have := hsum (fun _ => 1)
    simp only [mul_one] at this
    rw [this]
    congr 1
    exact sum_congr rfl fun xh _ => by simp [liftT]
  rw [hsq H, hsq K, hone]
  have hk : 0 ≤ 3 / ((Fintype.card F : ℝ) - 3) := by
    apply div_nonneg (by norm_num)
    have : (7 : ℝ) ≤ Fintype.card F := by exact_mod_cast hn
    linarith
  set A := ∑ xh, tripleMarginal xh * liftT φ H xh
  set B := ∑ xh, tripleMarginal xh * liftT φ K xh
  set S := ∑ xh, tripleMarginal (F := F) xh
  set Q := twoSlotCut.form (disjCoupling (F := F)) (liftT φ H) (liftT φ K)
  have e1 : c * Q - c * A * (c * B) / (c * S) = c * (Q - A * B / S) := by
    by_cases hS : S = 0
    · simp [hS]
    · field_simp
  rw [e1, abs_mul, abs_of_pos hc0, Real.sqrt_mul hc0.le, Real.sqrt_mul hc0.le]
  have hcs := Real.mul_self_sqrt hc0.le
  calc c * |Q - A * B / S| ≤ c * (3 / ((Fintype.card F : ℝ) - 3) *
        Real.sqrt (∑ xh, tripleMarginal xh * liftT φ H xh ^ 2) *
        Real.sqrt (∑ xh, tripleMarginal xh * liftT φ K xh ^ 2)) :=
        mul_le_mul_of_nonneg_left hHK hc0.le
    _ = 3 / ((Fintype.card F : ℝ) - 3) *
        (Real.sqrt c * Real.sqrt (∑ xh, tripleMarginal xh * liftT φ H xh ^ 2)) *
        (Real.sqrt c * Real.sqrt (∑ xh, tripleMarginal xh * liftT φ K xh ^ 2)) := by
        have e2 : 3 / ((Fintype.card F : ℝ) - 3) *
            (Real.sqrt c * Real.sqrt (∑ xh, tripleMarginal xh * liftT φ H xh ^ 2)) *
            (Real.sqrt c * Real.sqrt (∑ xh, tripleMarginal xh * liftT φ K xh ^ 2)) =
            (Real.sqrt c * Real.sqrt c) * (3 / ((Fintype.card F : ℝ) - 3) *
            Real.sqrt (∑ xh, tripleMarginal xh * liftT φ H xh ^ 2) *
            Real.sqrt (∑ xh, tripleMarginal xh * liftT φ K xh ^ 2)) := by ring
        rw [e2, hcs]

/-- The matching record at one prime is symmetric at `ι`. -/
theorem matchRecord_symm (hne : (injLabellings F (matchGraph (Fin 2))).Nonempty)
    (hn : 7 ≤ Fintype.card F) (φ : ZMod 6 → Fin 3) (H K : (reservedCut.Half → F) → ℝ) :
    reservedCut.form (signedIntegral (emit (graphLaw (matchGraph (Fin 2)) hne)
        (midEmission φ)).weight) H K =
      reservedCut.form (signedIntegral (emit (graphLaw (matchGraph (Fin 2)) hne)
        (midEmission φ)).weight) K H := by
  rw [form_matchRecord hne hn, form_matchRecord hne hn, disjCoupling_symm]

end Prime

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- The block matching record `Π_{E_s}` of V1's middle field laws. -/
noncomputable abbrev blockMatch (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (s : Fin 2) :
    FiniteLaw (Slot → BlockLabel pr) :=
  midComponent (middleBlockFieldLaws pr hne root) (true, ⟨PType.S, s⟩)

/-- The half marginal of a record has total mass one. -/
theorem sum_plusMarginal_emit {X O : Type} [Fintype X] [DecidableEq X] [Fintype O] [DecidableEq O]
    (lam : FiniteLaw (O × Fin 2 → X)) (φ : ZMod 6 → O) :
    ∑ x, plusMarginal reservedCut (emit lam (midEmission φ)).weight x = 1 := by
  have h := form_signedIntegral_one_right reservedCut (emit lam (midEmission φ)).weight 1
  simp only [Pi.one_apply, mul_one] at h
  rw [← h]
  unfold ReflectionCut.form
  change (emit lam (midEmission φ)).expect (fun _ => 1 * 1) = 1
  simp only [mul_one]
  exact (emit lam (midEmission φ)).expect_const 1 |>.trans (by simp)

/-- **(Cen) for the matching records of a middle block** (`lem:record:paired-e-bridge`(b),
`lem:record:exact-marginal-e`): if every prime of the block is `≥ b₀ ≥ 7`, the matching record
`Π_{E_s}` has centred norm `≤ 3/(b₀ − 3)` relative to its half marginal. -/
theorem centredNormLe_blockMatch (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (s : Fin 2) (b₀ : ℕ) (hb₀ : 7 ≤ b₀)
    (hle : ∀ i, b₀ ≤ pr i) :
    CentredNormLe reservedCut (signedIntegral (blockMatch pr hne root s).weight)
      (plusMarginal reservedCut (blockMatch pr hne root s).weight) (3 / ((b₀ : ℝ) - 3)) := by
  have hcard : ∀ i, 7 ≤ Fintype.card (ZMod (pr i)) := fun i => by
    rw [ZMod.card]
    exact hb₀.trans (hle i)
  have hb : (7 : ℝ) ≤ b₀ := by exact_mod_cast hb₀
  refine centredNormLe_emit_tensor reservedCut
    (fun i => graphLaw (matchGraph (Fin 2)) (hne.E2 i)) (midEmission (matching s))
    (fun i => matchRecord_symm (hne.E2 i) (hcard i) (matching s))
    (fun i => by rw [sum_plusMarginal_emit]; exact one_pos)
    (fun i => 3 / ((Fintype.card (ZMod (pr i)) : ℝ) - 3))
    (fun i => div_nonneg (by norm_num) (by
      have : (7 : ℝ) ≤ Fintype.card (ZMod (pr i)) := by exact_mod_cast hcard i
      linarith))
    (fun i => centredNormLe_matchRecord (hne.E2 i) (hcard i) (matching s))
    (div_nonneg (by norm_num) (by linarith)) ?_ ?_
  · rw [div_le_one (by linarith)]
    linarith
  · intro i
    rw [ZMod.card]
    have hp : (b₀ : ℝ) ≤ pr i := by exact_mod_cast hle i
    apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- The block matching record is invariant under the layer swap. -/
theorem blockMatch_swap (hne : MiddleNonempty pr) (y : Fin 3 × Fin 2 → BlockLabel pr) :
    (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2).weight (y ∘ layerSwapMap (Fin 3)) =
      (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2).weight y :=
  blockGraphLaw_weight_auto pr (matchGraph (Fin 2)) hne.E2 (layerSwapMap (Fin 3))
    (matchGraph_auto (Λ := Fin 2) (layerSwapMap (Fin 3))) y

/-- **The block matching record is symmetric at `ι`** (`ht` of `hres_of_restoration`). -/
theorem blockMatch_symm (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr))
    (s : Fin 2) (G H : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (signedIntegral (blockMatch pr hne root s).weight) G H =
      reservedCut.form (signedIntegral (blockMatch pr hne root s).weight) H G :=
  form_symm_of_swap _ (matching s) (blockMatch_swap pr hne) G H

/-- **The block matching record has equal half marginals** (`hn` of `hres_of_restoration`). -/
theorem blockMatch_minus (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr))
    (s : Fin 2) :
    minusMarginal reservedCut (blockMatch pr hne root s).weight =
      plusMarginal reservedCut (blockMatch pr hne root s).weight :=
  minusMarginal_eq_plus_of_swap _ (matching s) (blockMatch_swap pr hne)

end Block

end Sarkozy.OpsVariance
