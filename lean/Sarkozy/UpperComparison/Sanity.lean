module

public import Sarkozy.UpperComparison.Domain
public import Sarkozy.UpperComparison.Ledger
public import Sarkozy.UpperComparison.UpperLaw
public import Sarkozy.UpperComparison.OldRecords
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Non-vacuity of the upper price bookkeeping and of the domain lemma

Toy instances for the bundle `RecordLedger` and the hypotheses of the headline theorems of
`Prices`, `Ledger` and `Domain`:
* `toyLedger`: one changed record of degree two with `C^s = 2`, `C^a = 1`, its coefficients and
  polynomials evaluated; `toyLedger_prices` applies `block_prices_le` with equality;
* `tailLedger`: the paper's record ledger with V1's tail weights (`PartV.tailWeights`) and zero
  coefficients; `tailLedger_prices` applies `paper_block_prices` with the coefficients equal to
  their bounds, and `tailLedger_degrees` is `DegreesInRange` for it;
* `toy_sector`: `sector_bound_two` with two primes and nonzero norms, gates tight;
* `toy_gates`: `domain_gates` for a nonconstant admissible gate (`r + l`);
* `toy_block_gates`: the three block-gate implications with numbers;
* `root_kept`, `exists_changed`, `rootNew_accepts`, `rootNew_uniform`: the hypotheses of
  `Construction` and `UpperLaw` on the replacing laws are satisfiable on V1's block field laws
  (replacing every changed record by the kept root record `G_{LL,2}`), and changed records exist;
* `toy_layer`, `toy_pair`, `toy_norm` and an `example`: the hypotheses of `upRecord_sym_bracket`
  (pair-law densities and the layer-`0` law) hold jointly, on one-point labels with `K' = O = 1`;
* `toy_layersSupported`: the support hypothesis of `Densities` holds for the uniform two-layer law
  on two labels, a law that is not a point mass;
* `oldRecord_trivial`: the hypotheses of `oldRecord_sym_bracket` hold jointly on V1's block laws
  (replacing a record by itself, `C = 0`).
-/

namespace Sarkozy.UpperComparison

open Finset Sarkozy.Majorant

/-- A ledger with one changed record of degree two, `w = 1`, `C^s = 2`, `C^a = 1`. -/
def toyLedger : RecordLedger Unit where
  w _ := 1
  deg _ := 2
  fate _ := .changed
  Cs _ := 2
  Ca _ := 1
  w_nonneg _ := zero_le_one
  Cs_nonneg _ := zero_le_two
  Ca_nonneg _ := zero_le_one

theorem toyLedger_symCoef (r : ℝ) : toyLedger.symCoef r () = 2 * r ^ 3 := by
  simp [RecordLedger.symCoef, toyLedger]

theorem toyLedger_piRepS (r : ℝ) : toyLedger.piRepS r = 2 * r ^ 3 := by
  simp [RecordLedger.piRepS, RecordLedger.changed, toyLedger]

/-- `block_prices_le` applies to the toy ledger, with the record coefficients equal to their
bounds. -/
theorem toyLedger_prices :
    (∑ ρ, toyLedger.symCoef (1 / 2) ρ / 1) * 1 ≤
        (toyLedger.piRepS (1 / 2) + toyLedger.piDel (1 / 2)) * 1 ∧
      (∑ ρ, toyLedger.skewCoef (1 / 2) ρ / 1) * 1 ≤ toyLedger.piRepA (1 / 2) * 1 :=
  block_prices_le toyLedger (by norm_num) le_rfl zero_le_one _ _ (fun _ => le_rfl)
    (fun _ => le_rfl)

/-- The paper's record ledger with V1's tail weights and zero coefficients. -/
noncomputable def tailLedger : RecordLedger Sarkozy.PartV.UpIdx :=
  upperLedger Sarkozy.PartV.tailWeights (fun _ => 0) (fun _ => 0) (fun _ => le_rfl)
    (fun _ => le_rfl)

theorem tailLedger_degrees : tailLedger.DegreesInRange :=
  upperLedger_degreesInRange _ _ _ _ _

/-- `paper_block_prices` applies to the tail weights at `r = 1/2`, with the record coefficients
equal to their bounds. -/
theorem tailLedger_prices :
    (∑ ρ, tailLedger.symCoef (1 / 2) ρ / Sarkozy.PartV.upPoly Sarkozy.PartV.tailWeights (1 / 2)) *
        1 ≤ ((1 / 2) ^ 3 * tailLedger.ledgerS 2 + (1 / 2) ^ 4 * tailLedger.ledgerS 3 +
          tailLedger.piDel (1 / 2)) * 1 ∧
      (∑ ρ, tailLedger.skewCoef (1 / 2) ρ /
          Sarkozy.PartV.upPoly Sarkozy.PartV.tailWeights (1 / 2)) * 1 ≤
        ((1 / 2) ^ 3 * tailLedger.ledgerA 2 + (1 / 2) ^ 4 * tailLedger.ledgerA 3) * 1 :=
  paper_block_prices Sarkozy.PartV.tailWeights (fun _ => 0) (fun _ => 0) (fun _ => le_rfl)
    (fun _ => le_rfl) (r := 1 / 2) (sel := 1) (by norm_num) zero_le_one _ _ (fun _ => le_rfl)
    (fun _ => le_rfl)

/-- `sector_bound_two` with two primes, `r_p = r_b = 1/2`, `r₀ = 1`, `c_old = c_new = 1/2`,
`δ = δ' = 1/4`, `C^s = 1/2`, `C^a = 1/4`: the block gates hold with equality. -/
theorem toy_sector :
    ∏ p ∈ ({0, 1} : Finset ℕ), (fun _ => (1 / 4 : ℝ)) p +
        ∏ p ∈ ({0, 1} : Finset ℕ), (fun _ => (1 / 4 : ℝ)) p ≤ 1 / 2 * (1 / 2) ∧
      ∏ p ∈ ({0, 1} : Finset ℕ), (fun _ => (1 / 4 : ℝ)) p ≤ 1 / 4 * (1 / 2) :=
  sector_bound_two (r₀ := 1) (rb := 1 / 2) (cold := 1 / 2) (cnew := 1 / 2) {0, 1}
    (fun _ => 1 / 2) (fun _ => 1 / 4) (fun _ => 1 / 4) one_pos (by norm_num) (by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => le_rfl) (fun _ _ => by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (by norm_num) (by norm_num) (by decide)

/-- The gate `r + l < 3` on the box `[0, 1] × [0, 1]`, checked at the endpoint (`1 + 1 < 3`),
holds on the box: `domain_gates` with a nonconstant admissible gate. -/
theorem toy_gates (x : UpperBox 1 1) : x.1.1 + x.1.2 < 3 := by
  have hadm : Sarkozy.Majorant.Admissible (fun y : UpperBox 1 1 => y.1.1 + y.1.2) := by
    refine ⟨fun y z hyz => ?_, fun y => add_nonneg y.2.1 y.2.2.2.1⟩
    exact add_le_add hyz.1 hyz.2
  have h := domain_gates ({()} : Finset Unit) zero_le_one zero_le_one
    (fun _ y => y.1.1 + y.1.2) (fun _ => 3) (fun _ _ => hadm)
    (fun _ _ => by simp only [UpperBox.top]; norm_num) x
  exact h () (Finset.mem_singleton_self _)

/-- The block-gate implications with numbers: a one-way repair with `ρ_old = ρ' = 1/4`,
`C^s r₀ = 1/2`, `C^a r₀ = 1/4`; an FF record; a dense law. -/
theorem toy_block_gates :
    ((1 / 4 : ℝ) ^ 2 + (1 / 4) ^ 2 ≤ 2 * (1 / 4) ∧ (1 / 4 : ℝ) ^ 2 ≤ 1 * (1 / 4)) ∧
    ((1 / 4 : ℝ) ^ 2 + (1 / 4) ^ 2 ≤ 2 * (1 / 4) ∧ (1 / 4 : ℝ) ^ 2 ≤ 1 * (1 / 4)) ∧
    ((1 / 10 : ℝ) ^ 2 + (1 / 10) ^ 2 ≤ 2 * (1 / 4) ∧ (1 / 10 : ℝ) ^ 2 ≤ 2 * (1 / 4)) :=
  ⟨block_gate_oneway (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num),
    block_gate_forest (snew := 1 / 4) (anew := 1 / 4) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num),
    block_gate_dense (ks := 1) (ka := 1) (ds := 1 / 4) (da := 1 / 4) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

/-- The root record `(LL, 2)`. -/
def rootIdx : Sarkozy.PartV.UpIdx := (true, ⟨(.L, .L), ((), ())⟩)

/-- The root record is kept. -/
theorem root_kept : upperFate rootIdx = .kept := by decide +kernel

/-- Changed records exist, so the hypotheses on changed records are not vacuous. -/
theorem exists_changed : ∃ ρ : Sarkozy.PartV.UpIdx, upperFate ρ = .changed := by
  by_contra h
  push Not at h
  have : (univ.filter fun i : Sarkozy.PartV.UpIdx => upperFate i = .changed) = ∅ :=
    Finset.filter_false_of_mem fun i _ => h i
  have hc := card_changed
  rw [this] at hc
  exact absurd hc (by decide)

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- Replacing every changed record by the root component satisfies the acceptance hypothesis of
`upperNu_component_accepts`. -/
theorem rootNew_accepts (hne : Sarkozy.PartV.UpperNonempty pr) :
    ∀ ρ, upperFate ρ = .changed → ∀ z,
      (Sarkozy.PartV.upComponent (Sarkozy.PartV.upperBlockFieldLaws pr hne) rootIdx).weight z ≠ 0 →
      ∀ (j : Sarkozy.Chamber) (i : ι), quadraticChar (ZMod (pr i))
        (z (Sarkozy.queryTarget j) i - z (Sarkozy.querySource j) i) = 1 :=
  fun _ _ _ hz j i => kept_record_accepts pr hne rootIdx root_kept hz j i

/-- … and the uniformity hypothesis of `upperNu_component_uniform`. -/
theorem rootNew_uniform (hne : Sarkozy.PartV.UpperNonempty pr) :
    ∀ ρ, upperFate ρ = .changed → Sarkozy.HasUniformMarginals
      (Sarkozy.PartV.upComponent (Sarkozy.PartV.upperBlockFieldLaws pr hne) rootIdx) :=
  fun _ _ => Sarkozy.PartV.emit_uniform _ _
    (Sarkozy.PartV.blockGraphLaw_vertex_uniform pr _ (hne.two _ _))

end Block

section EmissionToy

open Sarkozy.Recentering Sarkozy.Structured

theorem toy_layer (y : Unit × Unit × Fin 2 → Unit) (k : Fin 2) :
    layerOf y k = fun _ => () := Subsingleton.elim _ _

/-- The pair-law hypothesis of `upRecord_sym_bracket` for the one-point two-layer law, with
`K' = O = 1`. -/
theorem toy_pair (φ ψ : (Unit × Unit → Unit) → ℝ) :
    (FiniteLaw.uniform (Unit × Unit × Fin 2 → Unit)).expect
        (fun y => φ (layerOf y 0) * ψ (layerOf y 1)) =
      kform (FiniteLaw.uniform (Unit × Unit → Unit)) (FiniteLaw.uniform (Unit × Unit → Unit))
        (fun _ => 1) φ ψ := by
  simp only [toy_layer, FiniteLaw.expect_uniform, kform, Fintype.sum_unique, Fintype.card_unique,
    Nat.cast_one, div_one, mul_one]

/-- The layer-`0` hypothesis of `upRecord_sym_bracket` for the one-point law, with `u₀ = 0`. -/
theorem toy_norm (φ : (Unit × Unit → Unit) → ℝ) :
    (FiniteLaw.uniform (Unit × Unit × Fin 2 → Unit)).expect
        (fun y => φ (layerOf y 0) * φ (layerOf y 0)) =
      mnrm (FiniteLaw.uniform (Unit × Unit → Unit)) (fun _ => 0) φ ^ 2 := by
  unfold mnrm
  rw [Real.sq_sqrt]
  · simp only [toy_layer, FiniteLaw.expect_uniform, Fintype.sum_unique, Fintype.card_unique,
      Nat.cast_one, div_one, add_zero, one_mul]
    rw [sq]
  · exact FiniteLaw.expect_nonneg _ (fun x => by positivity)

/-- `upRecord_sym_bracket` applies to the one-point instance. -/
example := upRecord_sym_bracket (FiniteLaw.uniform (Unit × Unit × Fin 2 → Unit))
  (FiniteLaw.uniform (Unit × Unit × Fin 2 → Unit)) (fun _ => ()) (fun _ => ())
  (FiniteLaw.uniform (Unit × Unit → Unit)) (fun _ => 0) (fun _ => 1) (fun _ => 1) toy_pair
  toy_pair toy_norm (C := 0) le_rfl (fun φ ψ => by simp)

/-- The support hypothesis of `Densities.upRecord_sym_bracket_of_support` holds for the uniform
law of a two-layer labelling with two labels, relative to the uniform half law. -/
theorem toy_layersSupported :
    LayersSupported (FiniteLaw.uniform (Unit × Unit × Fin 2 → Fin 2))
      (FiniteLaw.uniform (Unit × Unit → Fin 2)) := by
  intro y _
  have hc : (Fintype.card (Unit × Unit → Fin 2) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact ⟨inv_ne_zero hc, inv_ne_zero hc⟩

end EmissionToy

section OldRecordToy

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- The hypotheses of `oldRecord_sym_bracket` hold jointly on V1's block laws: the support
condition by `upper_layersSupported`, and the analytic bound with `C = 0` for the trivial
replacement `lamN = λ_𝔅(G)`. -/
theorem oldRecord_trivial (hne : Sarkozy.PartV.UpperNonempty pr)
    (t : Sarkozy.PartV.PType × Sarkozy.PartV.PType) (φ : t.1.Pat × t.2.Pat) :
    Sarkozy.reservedCut.Bracket
      ((0 : ℝ) • Sarkozy.reservedCut.diagonalLaw (Sarkozy.RecordExpansion.plusMarginal
        Sarkozy.reservedCut (Sarkozy.PartV.upComponent
          (Sarkozy.PartV.upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight))
      (Sarkozy.RecordExpansion.symPart Sarkozy.reservedCut
        (Sarkozy.signedIntegral (Sarkozy.PartV.emit (recOld pr hne t)
          (Sarkozy.PartV.upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight -
          Sarkozy.signedIntegral (Sarkozy.PartV.upComponent
            (Sarkozy.PartV.upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight))
      ((0 : ℝ) • Sarkozy.reservedCut.diagonalLaw (Sarkozy.RecordExpansion.plusMarginal
        Sarkozy.reservedCut (Sarkozy.PartV.upComponent
          (Sarkozy.PartV.upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight)) :=
  oldRecord_sym_bracket pr hne t φ (recOld pr hne t)
    (upper_layersSupported pr hne t.1.field t.2.field) le_rfl
    (fun φ' ψ' => by simp [recChangeForm])

end OldRecordToy

end Sarkozy.UpperComparison
