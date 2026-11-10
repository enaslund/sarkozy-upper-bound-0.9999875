module

public import Sarkozy.ComparisonLawPaper.Assembly
public import Sarkozy.PartVRecords.TailMixing
public import Sarkozy.MainAnchor.PaperQueries
public import Sarkozy.PartVLaws.Labellable

@[expose] public section

/-!
# The tail atoms of (CP4) from `lem:tail-prices`(i) and `lem:record:tail-mixing`

`paper/sections/27_tail_index.tex`. At a tail prime `q ≥ P₄` the comparison law `ν_q` of
`lem:tail-prices` is one nonnegative component `ν_q = w ν̄_q`. The clause (a) of `def:cp4` at the
tail atom (acceptance `(R5)`, uniform one-slot marginals, and the part of (R4) that concerns `ν̄_q`)
follows from the facts of `lem:tail-prices`(i) that V3's `lem:record:tail-mixing` uses, the bundle
`PartVRecords.AcceptedTailData` (`P_μ(r) ν_q = π_{LL,2} + ρ_q`, uniform one-slot marginals,
`Unif(Ω)` query pairs), with Weil's bound (H1) for the mixing at `q ≥ P₅`:

* `expect_pair_eq`: `E_ν̄ g(z_u, z_v) = ∑_{(x,x')} ν̄_{(u,v)}(x, x') g(x, x')`, the pair marginal in
  the `srcWeight` form of `Sarkozy.TraceMixing`;
* **`pairUniformOmega_of_omegaWeight`**: a pair marginal equal to V3's `omegaWeight` (mass
  `2/(q(q-1))` on each pair with `χ(x' - x) = 1`) is `TheoremC.PairUniformOmega` (`Unif(Ω_q)`, the
  strict-square pairs). This is the bridge between the two conventions (V3's interpretation
  choice 3);
* **`tailAccepted_of_omegaWeight`**: under such a law every query pair is a nonzero square almost
  surely (`(R5)` at the tail, `lem:tail-prices`(i), "under every accepted part each query pair is a
  strict-square pair");
* `tailNe`: the labelling sets of the tail law are nonempty at every prime `q ≥ P₄`, under H1
  (V2's `tailNonempty_explicit`);
* `TailAtomInputs q hne μ`: the remaining data of the tail atom: `ν̄_q` with `AcceptedTailData`, the
  mass `w > 0`, and the records and brackets of (b) (`lem:tail-prices`(ii));
* **`TailAtomInputs.toAtom`**: the `AtomComparison` of the atom (one component, coefficient one),
  `toAtom_single`, and **`toAtom_mixing`** (`TailMixing` at `q ≥ P₅`, from V3's `tailAccepted_R4`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.ComparisonLawPaper

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.Mixing Sarkozy.PartV Sarkozy.PartVRecords

section Pair

variable {q : ℕ} [Fact q.Prime]

/-- The expectation of a function of the pair `(z_u, z_v)` is read off the pair marginal
`srcWeight (pairJoint ν u v)` (for any finite set of slots `W`). -/
theorem expect_pair_eq {W : Type} [Fintype W] [DecidableEq W] (ν : FiniteLaw (W → ZMod q))
    (u v : W) (g : ZMod q → ZMod q → ℝ) :
    ν.expect (fun z => g (z u) (z v)) =
      ∑ xy : ZMod q × ZMod q, srcWeight (TraceMixing.pairJoint ν u v) xy * g xy.1 xy.2 := by
  have h : (TraceMixing.pairJoint ν u v).expect (fun ω => g ω.1.1 ω.1.2) =
      ν.expect (fun z => g (z u) (z v)) := by
    unfold TraceMixing.pairJoint
    exact FiniteLaw.expect_map _ _ _
  rw [← h]
  unfold FiniteLaw.expect srcWeight
  rw [Fintype.sum_prod_type]
  exact sum_congr rfl fun xy _ => by rw [sum_mul]

/-- `χ(d) = 1` iff `d` is a nonzero square. -/
theorem quadraticChar_eq_one_iff (d : ZMod q) :
    quadraticChar (ZMod q) d = 1 ↔ d ≠ 0 ∧ IsSquare d := by
  by_cases hd : d = 0
  · subst hd
    simp
  · rw [quadraticChar_one_iff_isSquare hd]
    exact ⟨fun h => ⟨hd, h⟩, fun h => h.2⟩

/-- **A pair marginal equal to `omegaWeight` is `Unif(Ω_q)`** (`TheoremC.PairUniformOmega`): the
`srcWeight` form of V3's `AcceptedTailData.pair` gives the expectation form of `def:cp4`(a). The
normalization `|Ω_q| = q(q-1)/2` is not computed: it follows from the total mass one. -/
theorem pairUniformOmega_of_omegaWeight (ν : FiniteLaw (Slot → ZMod q)) (u v : Slot)
    (h : ∀ x x', srcWeight (TraceMixing.pairJoint ν u v) (x, x') = omegaWeight q x x') :
    PairUniformOmega ν u v := by
  set c : ℝ := 2 / ((q : ℝ) * ((q : ℝ) - 1)) with hc
  have hw : ∀ xy : ZMod q × ZMod q, srcWeight (TraceMixing.pairJoint ν u v) xy =
      if xy ∈ strictSquarePairs q then c else 0 := by
    rintro ⟨x, x'⟩
    rw [h x x']
    unfold omegaWeight strictSquarePairs
    simp only [mem_filter, mem_univ, true_and]
    exact if_congr (quadraticChar_eq_one_iff _) hc.symm rfl
  have hexp : ∀ g : ZMod q → ZMod q → ℝ, ν.expect (fun z => g (z u) (z v)) =
      c * ∑ xy ∈ strictSquarePairs q, g xy.1 xy.2 := by
    intro g
    rw [expect_pair_eq, mul_sum]
    simp only [hw, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, univ_inter]
  have hone : c * (strictSquarePairs q).card = 1 := by
    have h1 := hexp (fun _ _ => 1)
    simp only [FiniteLaw.expect_const, sum_const, nsmul_eq_mul, mul_one] at h1
    linarith
  have hcard : ((strictSquarePairs q).card : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hone
    exact zero_ne_one hone
  intro g
  rw [hexp g, eq_div_iff hcard]
  calc (c * ∑ xy ∈ strictSquarePairs q, g xy.1 xy.2) * ((strictSquarePairs q).card : ℝ) =
      (c * (strictSquarePairs q).card) * ∑ xy ∈ strictSquarePairs q, g xy.1 xy.2 := by ring
    _ = ∑ xy ∈ strictSquarePairs q, g xy.1 xy.2 := by rw [hone, one_mul]

/-- **`(R5)` at the tail from `Unif(Ω)` pairs**: if the `(u, v)`-marginal of `ν` is `omegaWeight`,
then `z_v - z_u` is a nonzero square at every labelling of positive mass. -/
theorem tailAccepted_of_omegaWeight (ν : FiniteLaw (Slot → ZMod q)) (u v : Slot)
    (h : ∀ x x', srcWeight (TraceMixing.pairJoint ν u v) (x, x') = omegaWeight q x x')
    (z : Slot → ZMod q) (hz : ν.weight z ≠ 0) : tailAccepted q (z u) (z v) := by
  have hpos : 0 < ν.weight z := lt_of_le_of_ne (ν.nonneg z) (Ne.symm hz)
  have hind := expect_pair_eq ν u v (fun x x' => if x = z u ∧ x' = z v then 1 else 0)
  have hrhs : ∑ xy : ZMod q × ZMod q, srcWeight (TraceMixing.pairJoint ν u v) xy *
      (if xy.1 = z u ∧ xy.2 = z v then 1 else 0) =
        srcWeight (TraceMixing.pairJoint ν u v) (z u, z v) := by
    rw [sum_eq_single (z u, z v)]
    · simp
    · rintro ⟨x, x'⟩ _ hne
      have : ¬ (x = z u ∧ x' = z v) := fun hh => hne (by rw [hh.1, hh.2])
      simp [this]
    · intro hh
      exact absurd (mem_univ _) hh
  have hlhs : ν.weight z ≤ ν.expect (fun z' => if z' u = z u ∧ z' v = z v then 1 else 0) := by
    unfold FiniteLaw.expect
    have := single_le_sum (f := fun z' => ν.weight z' *
      (if z' u = z u ∧ z' v = z v then (1 : ℝ) else 0))
      (fun z' _ => mul_nonneg (ν.nonneg z') (by split_ifs <;> norm_num)) (mem_univ z)
    simpa using this
  rw [hind, hrhs, h] at hlhs
  have hω : omegaWeight q (z u) (z v) ≠ 0 := fun h0 => by rw [h0] at hlhs; linarith
  unfold omegaWeight at hω
  split_ifs at hω with hχ
  · exact (quadraticChar_eq_one_iff _).mp hχ
  · exact absurd rfl hω

end Pair

/-! ## The tail atom -/

/-- The query `j` of `𝓔₆` has source `querySource j` and target `queryTarget j`. -/
theorem paperQueries_source_eq (j : Chamber) : MainAnchor.paperQueries.source j = querySource j :=
  rfl

theorem paperQueries_target_eq (j : Chamber) : MainAnchor.paperQueries.target j = queryTarget j :=
  MainAnchor.paperQueries_target j

/-- **The labelling sets of the tail law are nonempty at every prime `q ≥ P₄`** (`def:tail-law`),
under Weil's bound H1: V2's `tailNonempty_explicit` (`q ≥ 81·10¹²`). -/
theorem tailNe (hW : Target.Weil) {q : ℕ} [Fact q.Prime] (h4 : PartV.P4 ≤ q) : TailNonempty q := by
  have h47 : (81 * 10 ^ 12 : ℝ) ≤ 2 ^ 47 := by norm_num
  have h512 : (2 : ℝ) ^ 47 ≤ 2 ^ 512 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  exact PartVLaws.tailNonempty_explicit q (Labellings.weilBound_of_target hW q (ne_two_of_P4 q h4))
    (h47.trans (h512.trans (two_pow_512_le_of_P4 q h4)))

/-- **The data of the comparison law at a tail prime `q`** (`lem:tail-prices`(i), (ii)), relative to
the reference `μ = μ_q`, for a proof `hne` that the labelling sets are nonempty (`tailNe`): one
nonnegative component `ν_q = w ν̄_q`.
* `ν`, `acc`: the normalized accepted part `ν̄_q` with the facts of `lem:tail-prices`(i) that
  `lem:record:tail-mixing` uses (V3's `AcceptedTailData`: `P_μ(r) ν_q = π_{LL,2} + ρ_q` with
  `0 < h'_q ≤ h_q`, uniform one-slot marginals, `Unif(Ω)` query pairs);
* `w`, `w_pos`: the mass `ν_q(1) > 0`;
* `T`, `Δ`, `change`, `D`, `πt`, `bracket`: (b) of `def:cp4` for `ν_q - μ_q` (`lem:tail-prices`(ii):
  kept records, one-way repairs and deletions, with the brackets of `prop:record:upper`(i) at a
  single prime). -/
structure TailAtomInputs (q : ℕ) [Fact q.Prime] (hne : TailNonempty q) (μ : SlotMeasure (ZMod q))
    where
  ν : FiniteLaw (Slot → ZMod q)
  acc : AcceptedTailData q hne ν
  w : ℝ
  w_pos : 0 < w
  T : Type
  [TFintype : Fintype T]
  [TDecEq : DecidableEq T]
  Δ : T → SlotMeasure (ZMod q)
  change : w • signedIntegral ν.weight - μ = ∑ t, Δ t
  D : T → ChangeType → SlotMeasure (ZMod q)
  D_prob : ∀ t e, IsProbability (D t e)
  D_diag : ∀ t e, TheoremC.IsDiagonalAt reservedCut (D t e)
  D_unif : ∀ t e, HasUniformSlotMarginals (D t e)
  πt : T → ChangeType → ℝ
  πt_nonneg : ∀ t e, 0 ≤ πt t e
  bracket : ∀ t e, reservedCut.Bracket (πt t e • D t e) (changePart e (Δ t)) (πt t e • D t e)

attribute [instance] TailAtomInputs.TFintype TailAtomInputs.TDecEq

namespace TailAtomInputs

variable {q : ℕ} [Fact q.Prime] {hne : TailNonempty q} {μ : SlotMeasure (ZMod q)}
  (D : TailAtomInputs q hne μ)

/-- **The `AtomComparison` of a tail atom**: one component `ν̄_q` with coefficient one and mass
`w`; acceptance from the `Unif(Ω)` query pairs (`tailAccepted_of_omegaWeight`), uniform marginals
from `AcceptedTailData.uniform`. -/
noncomputable def toAtom : AtomComparison μ (tailAccepted q) MainAnchor.paperQueries where
  I := Unit
  c _ := 1
  w _ := D.w
  law _ := D.ν
  w_pos _ := D.w_pos
  mass_pos := by simpa using D.w_pos
  accept _ z hz e := by
    rw [paperQueries_source_eq, paperQueries_target_eq]
    exact tailAccepted_of_omegaWeight D.ν _ _ (D.acc.pair e) z hz
  unif _ := D.acc.uniform
  T := D.T
  Δ := D.Δ
  change := by simpa using D.change
  D := D.D
  D_prob := D.D_prob
  D_diag := D.D_diag
  D_unif := D.D_unif
  πt := D.πt
  πt_nonneg := D.πt_nonneg
  bracket := D.bracket

/-- The tail atom is one nonnegative component. -/
theorem toAtom_single : D.toAtom.IsSingle :=
  ⟨Fintype.card_unit, fun _ => zero_le_one⟩

/-- **The part of (R4) that concerns `ν̄_q`** (`lem:record:tail-mixing`(c) with (a), (b)): under
Weil's bound (H1), at `q ≥ P₅` the component of the tail atom is `(γ, v)`-mixing at every slot, its
query pairs are `Unif(Ω_q)`, and it is `(γ, {u_e, v_e})`-mixing at every query. From V3's
`tailAccepted_R4` and `pairUniformOmega_of_omegaWeight`. -/
theorem toAtom_mixing (hW : Target.Weil) (hq : PartV.P5 ≤ q) (i : D.toAtom.I) :
    TailMixing q MainAnchor.paperQueries (D.toAtom.law i) := by
  obtain ⟨hslot, hpair⟩ := tailAccepted_R4 q hW hq D.acc
  refine ⟨fun v => hslot v, fun e => ⟨?_, ?_⟩⟩
  · rw [paperQueries_source_eq, paperQueries_target_eq]
    exact pairUniformOmega_of_omegaWeight D.ν _ _ (D.acc.pair e)
  · rw [paperQueries_source_eq, paperQueries_target_eq]
    exact hpair e

end TailAtomInputs

end Sarkozy.ComparisonLawPaper
