module

public import Sarkozy.ClassBoundsPaper.Polynomial

@[expose] public section

/-!
# Non-vacuity checks for `ClassInputs` and `PolynomialData`

* `ClassInputs.trivial`: for **every** comparison law with nonnegative prices, the class inputs with
  no degree class and no variance class exist; so the fields of `ClassInputs` are jointly
  satisfiable (no contradiction between the class map, the coefficients, `nmax_bound` and the robust
  bound). This instance is useless for the closing (its `hΨ` would need `D ≤ 0`).
* The paper's specialization is consistent with the fields it constrains:
  - `paperN_valid`: the 49 degree vectors satisfy `ClassInputs.hN` (nonzero, even total degree), so
    `PolynomialData.hN : CI.N = paperN` does not contradict `CI.hN`;
  - `paperC_nonneg` (in `Savings`): the class costs are nonnegative (`ClassInputs.C_nonneg`, with
    credits at most the cost, `lem:class-credit`);
  - `paperAtot_sum_le_A`: the kind totals `A_F + A_E/2 + A_E/2` of the skew kind variables are below
    the ledger's `A`, as `hAtot` and `hA` together require (the kind variables are skew);
  - `paperN_deg_le`: the degree classes have at most six atoms (`n_max`);
  - `paperTotals_nonneg` (in `Savings`): all kind totals are nonnegative, as the nonnegative upper
    prices require;
  - `targetLedger_B_nonneg`: `B' = targetLedger.B ≥ 0` (`ClassInputs.Bp_nonneg`).
-/

open Finset Filter
open scoped Topology BigOperators

namespace Sarkozy.ClassBoundsPaper

open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.TheoremCBlock Sarkozy.TheoremC
  Sarkozy.Comparison Sarkozy.TargetLedger
open Sarkozy.Param (Params)

variable {a : ℝ} {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {S₀ : Bk → ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀ blk}
  {FS : FirstStage a m₀ blk p S₀ R}

/-- **The class inputs without classes**, for any comparison law with nonnegative prices: the
fields of `ClassInputs` are jointly satisfiable. -/
noncomputable def ClassInputs.trivial (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS)
    (hπ : ∀ L b t e, 0 ≤ CL.π L b t e) : ClassInputs CL where
  N := ∅
  hN := by simp
  C _ := 0
  C_nonneg := by simp
  Bp := 0
  Bp_nonneg := le_rfl
  π_nonneg := hπ
  kind _ _ := none
  kind_skew := by simp
  yarm _ _ := 0
  ylead _ _ := 0
  yrem _ _ := 0
  yarm_nonneg _ _ := le_rfl
  ylead_nonneg _ _ := le_rfl
  yrem_nonneg _ _ := le_rfl
  V _ := Empty
  vcls _ _ := none
  vcost _ _ := 0
  vcost_nonneg _ _ := le_rfl
  nmax := 0
  nmax_bound L ω _ h := by simp at h
  robust := by
    refine ⟨fun _ => 0, tendsto_const_nhds, 0, le_rfl, fun _ _ _ => 0, fun _ _ _ => le_rfl,
      Param.AtCounterexamples.of_forall (Params.ofDecay a) fun L A => ⟨?_, ?_⟩⟩
    · rintro (⟨n, hn⟩ | e)
      · simp at hn
      · exact e.elim
    · simp [Sarkozy.Comparison.remainder]

/-- The 49 degree vectors are nonzero, of even total degree (`ClassInputs.hN`). -/
theorem paperN_valid : ∀ n ∈ paperN, n ≠ 0 ∧ Even (∑ l, n l) := by
  intro n hn
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
  have hdeg := triples_deg t (List.mem_toFinset.mp ht)
  obtain ⟨a, b, c⟩ := t
  have hsum : ∑ l, toVec (a, b, c) l = a + b + c := by
    simp [toVec, Fin.sum_univ_three]
  refine ⟨?_, ?_⟩
  · intro h0
    have : ∑ l, toVec (a, b, c) l = 0 := by simp [h0]
    rw [hsum] at this
    simp only [this] at hdeg
    simp at hdeg
  · rw [hsum]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hdeg
    rcases hdeg with h | h | h <;> rw [h] <;> decide

/-- The degree classes have at most six atoms (`n_max = 6` for them, `prop:closing-data`(d):
"every selection of a class has at most six atoms"). -/
theorem paperN_deg_le : ∀ n ∈ paperN, ∑ l, n l ≤ 6 := by
  intro n hn
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
  have hdeg := triples_deg t (List.mem_toFinset.mp ht)
  obtain ⟨a, b, c⟩ := t
  have hsum : ∑ l, toVec (a, b, c) l = a + b + c := by
    simp [toVec, Fin.sum_univ_three]
  rw [hsum]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdeg
  omega

/-- The skew kind totals fit under the ledger's `A` (`PolynomialData.hAtot` with `hA`). -/
theorem paperAtot_sum_le_A : ∑ l, paperAtot l ≤ targetLedger.A := by
  simp only [Fin.sum_univ_three, paperAtot, totQ]
  norm_num [targetLedger, gF, gE]

theorem targetLedger_B_nonneg : 0 ≤ targetLedger.B := by
  norm_num [targetLedger]

end Sarkozy.ClassBoundsPaper
