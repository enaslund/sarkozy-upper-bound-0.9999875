module

public import Sarkozy.ComparisonLawPaper.Tail
public import Sarkozy.TraceMixing.Pair

@[expose] public section

/-!
# The normalized accepted part of the tail comparison law (`lem:tail-prices`(i))

`paper/sections/27_tail_index.tex`, `lem:tail-prices`(i) and its proof: "Every record of `ν_p` is
invariant, so the accepted part has uniform one-slot marginals and invariant query-pair marginals
supported on `Ω`, which are therefore `Unif(Ω)`. Every retained or repaired record imposes the
strict-square relation on each query pair." V3's `AcceptedTailData` asks for the uniform marginals
and the `Unif(Ω)` pair marginals of `ν̄_p` as fields; here they are *proved* from the invariance and
the acceptance of the nonroot part `ρ_p`:

* `AffineInvariant p f`: `f(α z + β) = f(z)` for every nonzero square `α` and every `β`;
* **`uniform_of_translation`**: a law invariant under the translations has uniform one-slot
  marginals;
* **`pair_of_invariant`**: a square-affine invariant law whose `(u, v)`-pair is a strict-square pair
  almost surely has the pair marginal `omegaWeight` (`Unif(Ω)`), through the trace-mixing lemma
  `TraceMixing.srcWeight_pair_uniform`;
* `TailRestData p hne`: the nonroot part `ρ_p ≥ 0` of `P_μ(r) ν_p = π_{LL,2} + ρ_p`, of mass
  `0 < h'_p ≤ h_p`, square-affine invariant and accepting the queries of `𝓔₆`; *hypotheses*;
* **`TailRestData.law`, `TailRestData.accepted`**: `ν̄_p = (π_{LL,2} + ρ_p)/(1 + h'_p)` and its
  `AcceptedTailData` (all ten fields; `uniform` and `pair` proved);
* `TailAtomData`: B2's `TailAtomInputs` with `ν`, `acc` replaced by `TailRestData`;
  **`TailAtomData.toInputs`**.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.TailPrices

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.Mixing Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.Labellings
open Sarkozy.TraceMixing (pairJoint pairCombine pairJoint_weight pairCombine_map pairCombine_u
  pairCombine_v pairCombine_rest restTr restDil restDil_apply srcWeight_pair_uniform
  pairJoint_supp)
open Sarkozy.ComparisonLawPaper (TailAtomInputs)

variable {p : ℕ} [Fact p.Prime]

/-- Pointwise invariance of a weight under the square-affine maps `z_v ↦ α z_v + β`
(`α` a nonzero square, `β ∈ 𝔽_p`). -/
def AffineInvariant (p : ℕ) [Fact p.Prime] (f : (Slot → ZMod p) → ℝ) : Prop :=
  ∀ α β : ZMod p, quadraticChar (ZMod p) α = 1 → ∀ z, f (fun w => α * z w + β) = f z

/-- **Uniform one-slot marginals from translation invariance**. -/
theorem uniform_of_translation (ν : FiniteLaw (Slot → ZMod p))
    (htr : ∀ (β : ZMod p) z, ν.weight (fun w => z w + β) = ν.weight z) :
    HasUniformMarginals ν := by
  intro v f
  have hshift : ∀ β : ZMod p, ν.expect (fun z => f (z v + β)) = ν.expect (fun z => f (z v)) := by
    intro β
    unfold FiniteLaw.expect
    let e : (Slot → ZMod p) ≃ (Slot → ZMod p) :=
      Equiv.piCongrRight (fun _ => Equiv.addRight β)
    rw [← e.sum_comp (fun z => ν.weight z * f (z v))]
    refine sum_congr rfl fun z _ => ?_
    have he : (e z) = fun w => z w + β := rfl
    rw [he, htr β z]
  have hsum : ∑ β : ZMod p, ν.expect (fun z => f (z v + β)) = ∑ x : ZMod p, f x := by
    unfold FiniteLaw.expect
    rw [sum_comm]
    have : ∀ z : Slot → ZMod p, ∑ β : ZMod p, ν.weight z * f (z v + β) =
        ν.weight z * ∑ x : ZMod p, f x := by
      intro z
      rw [← mul_sum]
      congr 1
      exact Equiv.sum_comp (Equiv.addLeft (z v)) f
    rw [sum_congr rfl fun z _ => this z, ← sum_mul, ν.total, one_mul]
  have hconst : ∑ β : ZMod p, ν.expect (fun z => f (z v + β)) =
      (Fintype.card (ZMod p) : ℝ) * ν.expect (fun z => f (z v)) := by
    rw [sum_congr rfl fun β _ => hshift β, sum_const, nsmul_eq_mul, card_univ]
  have hc : (Fintype.card (ZMod p) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold FiniteLaw.expect at hsum hconst ⊢
  simp only [FiniteLaw.uniform]
  rw [← mul_sum, ← hsum, hconst, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

omit [Fact p.Prime] in
/-- `z` is recombined from `z_u`, `z_v` and its other labels. -/
theorem pairCombine_self {u v : Slot} (z : Slot → ZMod p) :
    pairCombine (u := u) (v := v) (z u) (z v) (fun w => z w) = z := by
  funext w
  unfold pairCombine
  split_ifs with h1 h2
  · rw [h1]
  · rw [h2]
  · rfl

/-- **The pair marginal of an invariant law** (`lem:tail-prices`(i), proof): if `ν` is
square-affine invariant and its `(u, v)`-pair is a strict-square pair almost surely (`u ≠ v`,
`p ≠ 2`), then its `(u, v)`-marginal is `Unif(Ω)` (`omegaWeight`). -/
theorem pair_of_invariant (hp2 : p ≠ 2) (ν : FiniteLaw (Slot → ZMod p))
    (hinv : AffineInvariant p ν.weight) {u v : Slot} (huv : u ≠ v)
    (hacc : ∀ z, ν.weight z ≠ 0 → quadraticChar (ZMod p) (z v - z u) = 1) (x x' : ZMod p) :
    srcWeight (pairJoint ν u v) (x, x') = omegaWeight p x x' := by
  unfold omegaWeight
  refine srcWeight_pair_uniform hp2 (pairJoint ν u v) ?_ (fun β => restTr β) ?_
    (fun α => restDil α) ?_ x x'
  · intro y y' r hy
    rw [pairJoint_weight _ huv]
    by_contra h0
    have := hacc _ h0
    rw [pairCombine_u, pairCombine_v huv] at this
    exact hy this
  · intro β y y' r
    rw [pairJoint_weight _ huv, pairJoint_weight _ huv]
    change ν.weight (pairCombine (y + β) (y' + β) (fun w => r w + β)) = _
    have h := pairCombine_map (u := u) (v := v) (fun c => c + β) y y' r
    rw [h]
    have := hinv 1 β (map_one _) (pairCombine y y' r)
    simp only [one_mul] at this
    exact this
  · intro α hα y y' r
    rw [pairJoint_weight _ huv, pairJoint_weight _ huv,
      restDil_apply (ne_zero_of_quadraticChar_eq_one hα)]
    have h := pairCombine_map (u := u) (v := v) (fun c => α * c) y y' r
    rw [h]
    have := hinv α 0 hα (pairCombine y y' r)
    simp only [add_zero] at this
    exact this

/-- The root `π_{LL,2}` is square-affine invariant. -/
theorem root_invariant (hne : TailNonempty p) : AffineInvariant p (tailRootComponent p hne).weight :=
  fun α β hα z => by
    rw [tailRootComponent_weight, tailRootComponent_weight]
    exact TraceMixing.graphLaw_weight_affine slotRootGraph (slotRoot_nonempty p hne) hα β z

/-- The root `π_{LL,2}` accepts every query of `𝓔₆` (`lem:tail-law`(iii)). -/
theorem root_accepts (hne : TailNonempty p) (j : Chamber) (z : Slot → ZMod p)
    (hz : (tailRootComponent p hne).weight z ≠ 0) :
    quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1 := by
  by_contra h
  apply hz
  rw [tailRootComponent_weight]
  have huv := query_mem_slotRootGraph j
  have h0 := pairJoint_supp slotRootGraph (slotRoot_nonempty p hne) huv (z (querySource j))
    (z (queryTarget j)) (fun w => z w) h
  have huv' : querySource j ≠ queryTarget j := fun h' => slotRootGraph.loopless _ (h' ▸ huv)
  rw [pairJoint_weight _ huv', pairCombine_self] at h0
  exact h0

/-! ## The nonroot part and the accepted law -/

/-- **The nonroot part `ρ_p` of the tail comparison law** (`lem:tail-prices`(i), and the proof of
`lem:record:tail-mixing`): `P_μ(r) ν_p = π_{LL,2} + ρ_p` with `ρ_p ≥ 0` of mass `0 < h'_p ≤ h_p`
(the records of degree one are kept; repairs keep mass and deletions decrease it), square-affine
invariant (every record of `ν_p` is invariant) and accepting the queries of `𝓔₆` (every retained or
repaired record imposes the strict-square relation on each query pair). *Hypotheses*. -/
structure TailRestData (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) where
  /-- The nonroot mass `h'_p`. -/
  h' : ℝ
  /-- The nonroot part `ρ_p`. -/
  ρt : (Slot → ZMod p) → ℝ
  ρt_nonneg : ∀ z, 0 ≤ ρt z
  ρt_mass : ∑ z, ρt z = h'
  h'_pos : 0 < h'
  h'_le : h' ≤ tailH p
  /-- Square-affine invariance of `ρ_p`. -/
  ρt_inv : AffineInvariant p ρt
  /-- `ρ_p` accepts the queries of `𝓔₆`. -/
  ρt_acc : ∀ z, ρt z ≠ 0 → ∀ j : Chamber,
    quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1

namespace TailRestData

variable {hne : TailNonempty p} (R : TailRestData p hne)

/-- **`ν̄_p = (π_{LL,2} + ρ_p)/(1 + h'_p)`**, the normalized accepted part. -/
noncomputable def law : FiniteLaw (Slot → ZMod p) where
  weight z := ((tailRootComponent p hne).weight z + R.ρt z) / (1 + R.h')
  nonneg z := div_nonneg (add_nonneg ((tailRootComponent p hne).nonneg z) (R.ρt_nonneg z))
    (by linarith [R.h'_pos])
  total := by
    rw [← sum_div, sum_add_distrib, (tailRootComponent p hne).total, R.ρt_mass,
      div_self (by linarith [R.h'_pos])]

theorem law_invariant : AffineInvariant p R.law.weight := fun α β hα z => by
  change ((tailRootComponent p hne).weight _ + R.ρt _) / _ =
    ((tailRootComponent p hne).weight z + R.ρt z) / _
  rw [root_invariant hne α β hα z, R.ρt_inv α β hα z]

theorem law_accepts (j : Chamber) (z : Slot → ZMod p) (hz : R.law.weight z ≠ 0) :
    quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1 := by
  by_cases hr : (tailRootComponent p hne).weight z = 0
  · have hρ : R.ρt z ≠ 0 := by
      intro h0
      apply hz
      change ((tailRootComponent p hne).weight z + R.ρt z) / _ = 0
      rw [hr, h0, add_zero, zero_div]
    exact R.ρt_acc z hρ j
  · exact root_accepts hne j z hr

/-- **`AcceptedTailData` of `ν̄_p`** (`lem:tail-prices`(i)): the uniform one-slot marginals and the
`Unif(Ω)` query pairs are proved from the invariance and the acceptance (`p ≠ 2`). -/
noncomputable def accepted (hp2 : p ≠ 2) : AcceptedTailData p hne R.law where
  h' := R.h'
  ρt := R.ρt
  ρt_nonneg := R.ρt_nonneg
  ρt_mass := R.ρt_mass
  h'_pos := R.h'_pos
  h'_le := R.h'_le
  decomp _ := rfl
  uniform := uniform_of_translation R.law fun β z => by
    have := R.law_invariant 1 β (map_one _) z
    simp only [one_mul] at this
    exact this
  pair j x x' := pair_of_invariant hp2 R.law R.law_invariant
    (fun h' => slotRootGraph.loopless _ (h' ▸ query_mem_slotRootGraph j))
    (fun z hz => R.law_accepts j z hz) x x'

end TailRestData

/-- **The data of the tail atom at `q`** (`lem:tail-prices`(i),(ii)), with the normalized accepted
part given by its nonroot part `ρ_q` (`TailRestData`) instead of B2's `ν`, `acc`. The other fields
are those of `TailAtomInputs`. *Hypotheses*. -/
structure TailAtomData (q : ℕ) [Fact q.Prime] (hne : TailNonempty q) (μ : SlotMeasure (ZMod q))
    where
  rest : TailRestData q hne
  w : ℝ
  w_pos : 0 < w
  T : Type
  [TFintype : Fintype T]
  [TDecEq : DecidableEq T]
  Δ : T → SlotMeasure (ZMod q)
  change : w • signedIntegral rest.law.weight - μ = ∑ t, Δ t
  D : T → ChangeType → SlotMeasure (ZMod q)
  D_prob : ∀ t e, IsProbability (D t e)
  D_diag : ∀ t e, TheoremC.IsDiagonalAt reservedCut (D t e)
  D_unif : ∀ t e, HasUniformSlotMarginals (D t e)
  πt : T → ChangeType → ℝ
  πt_nonneg : ∀ t e, 0 ≤ πt t e
  bracket : ∀ t e, reservedCut.Bracket (πt t e • D t e) (changePart e (Δ t)) (πt t e • D t e)

attribute [instance] TailAtomData.TFintype TailAtomData.TDecEq

/-- **B2's `TailAtomInputs` from `TailAtomData`** (`p ≠ 2`). -/
noncomputable def TailAtomData.toInputs {q : ℕ} [Fact q.Prime] {hne : TailNonempty q}
    {μ : SlotMeasure (ZMod q)} (D : TailAtomData q hne μ) (hq2 : q ≠ 2) :
    TailAtomInputs q hne μ where
  ν := D.rest.law
  acc := D.rest.accepted hq2
  w := D.w
  w_pos := D.w_pos
  T := D.T
  Δ := D.Δ
  change := D.change
  D := D.D
  D_prob := D.D_prob
  D_diag := D.D_diag
  D_unif := D.D_unif
  πt := D.πt
  πt_nonneg := D.πt_nonneg
  bracket := D.bracket

theorem TailAtomData.toInputs_πt {q : ℕ} [Fact q.Prime] {hne : TailNonempty q}
    {μ : SlotMeasure (ZMod q)} (D : TailAtomData q hne μ) (hq2 : q ≠ 2) :
    (D.toInputs hq2).πt = D.πt := rfl

end Sarkozy.TailPrices
