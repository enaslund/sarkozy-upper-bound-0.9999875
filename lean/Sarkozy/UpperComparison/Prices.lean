module

public import Sarkozy.Comparison.Repricing
public import Sarkozy.RecordExpansion.Charging
public import Sarkozy.RecordExpansion.Monomials

@[expose] public section

/-!
# (CP4) in the upper range: the totals `S_u` and `A_u` (`prop:record:upper`)

`paper/sections/26_upper_comparison.tex`, `def:upper-comparison` and `prop:record:upper`.

The comparison law `ν_𝔅` of an upper block is obtained from the reference `μ_𝔅` record by
record (`def:upper-comparison`): a record is kept (a), changed (b), (b′) (one-way repair, dense
law, LE mixture), or deleted (c). This file formalizes the price bookkeeping of
`prop:record:upper`, which is the part of the proposition that the closing reads, and the two
charging steps of its part (i).

**The record ledger** (`RecordLedger`). For each record `ρ` of a block: its weight `w ρ ≥ 0`
(`w_𝔱` for a two-layer record, `v_𝔱` for a folded one), its overall degree `deg ρ`
(`deg 𝔱`, respectively `deg 𝔱 + 1`), its fate, and for a changed record its symmetric and skew
coefficients `C^s ρ, C^a ρ ≥ 0` ((F7), (F9)). The unpriced coefficients of the proof of (i) are
* kept: `0` and `0`;
* changed: `w C^s r^{deg+1}` and `w C^a r^{deg+1}` (charging rule (ii) with the bound
  `C^ε r` of `lem:record:domain`(ii));
* deleted: `w r^{deg}` and `0` (charging rule (i): the mass).

**What is proved.**
* (i), the brackets: `changed_record_bracket` (rule (ii) for a record of weight `ω` whose change
  has cut-form norm at most `C r`) and `deleted_record_bracket` (rule (i)), from
  `Sarkozy.RecordExpansion.Charging`.
* (i), the totals: `RecordLedger.sum_symCoef`, `RecordLedger.sum_skewCoef` (the sums of the
  unpriced coefficients are `Π^rep_s + Π^del` and `Π^rep_a`, exactly), `RecordLedger.piRepS_eq`
  (`Π^rep_s(r) = r³ ∑ w Λ^s_2 + r⁴ ∑ w Λ^s_3`, the regrouping by degree when the changed records
  have degree two or three), `poly_eval_regroup` (any sum `∑_ρ c_ρ r^{e_ρ}` with
  `e_ρ ∈ [3, 7]` is the polynomial of its coefficient sums), and `block_prices_le` (dividing by
  `P_μ ≥ 1` and multiplying by `q_𝔅^{2a}`: `s_𝔅 ≤ (Π^rep_s + Π^del)(r) q_𝔅^{2a}`,
  `a_𝔅 ≤ Π^rep_a(r) q_𝔅^{2a}`).
* (ii): `band_sum_le` (the sum over the blocks of a band of `∑_d c_d b^{-d/2} q^{2a}` is at most
  `∑_d c_d 𝒰_d` when `c_d ≥ 0` and `𝒰_d` bounds `∑_𝔅 q^{2a} b^{-d/2}`), `charge_reprice`
  (`𝒰_d(a) = e^{2(a-a_c)l} 𝒰_d(a_c)` is valid, `lem:record:repricing`), and `upper_totals_le`
  (the upper parts of `S` and `A` are at most `S_u(a)` and `A_u(a)`, with the tail sums of
  `lem:tail-prices`(iv) as hypotheses).
* (iii): `block_price_const` (`s_𝔅 + a_𝔅 ≤ C_band b^{-3/2} q_𝔅^{2a}`).
* The interface with the target: `upper_symTotal_le` and `upper_skewTotal_le` state (ii) for the
  totals `symTotal`/`skewTotal` of `Sarkozy.RecordExpansion`, the shape of the fields
  `S_total`/`A_total` of `TheoremCParam.ComparisonLaw` (and of its block-atom version).

**Hypotheses, by label.** The norm bounds of the changed records are inputs: they are (F7) and
(F9) (`prop:forest-records`, `prop:dense-comparison`, `prop:le-mixture`, see `ForestRecords`,
`DenseLaws`, `LEMixture`) extended to blocks by `lem:record:domain`(ii) (`Domain`). The block
charges `𝒰_d(a_c)` are `lem:record:block-charge`(i) (`Sarkozy.Misc`), and the tail sums are
`lem:tail-prices`(iv). The positivity, invariance and acceptance claims of (i) concern the laws
themselves and are not part of this file. Here `r = b^{-1/2}`; the polynomials are written in
`r` with natural powers, `r^d = b^{-d/2}`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.UpperComparison

open Sarkozy.RecordExpansion

/-! ## The brackets of part (i) -/

section Brackets

variable {W Y : Type*} [Fintype W] [DecidableEq W] [Fintype Y] [DecidableEq Y]

omit [DecidableEq Y] in
/-- **`prop:record:upper`(i), a changed record** (charging rule (ii), `rem:cp:charging`): a record
of weight `ω ≥ 0` whose change `Δ` has cut-form norm at most `C r` relative to its actual half
marginal `m` (`|Q_Δ(F, G)| ≤ C r ‖F‖_m ‖G‖_m`, the bound of (F7)/(F9) on the block given by
`lem:record:domain`(ii)) has the bracket `(ωCr Diag(m)  ωΔ; ωΔ*  ωCr Diag(m)) ⪰_c 0`: it
contributes `ω C r` to the unpriced total. The norm bound is a hypothesis. -/
theorem changed_record_bracket (c : ReflectionCut W) {m : (c.Half → Y) → ℝ}
    (hm : ∀ x, 0 ≤ m x) {ω C r : ℝ} (hω : 0 ≤ ω) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (Δ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (hΔ : ∀ F G : (c.Half → Y) → ℝ, |c.form Δ F G| ≤
      C * r * Real.sqrt (∑ x, m x * (F x * F x)) * Real.sqrt (∑ x, m x * (G x * G x))) :
    c.Bracket ((ω * (C * r)) • c.diagonalLaw m) (ω • Δ) ((ω * (C * r)) • c.diagonalLaw m) := by
  have h := bracket_of_norm_bound c hm (mul_nonneg hC hr) Δ hΔ
  have h' := bracket_smul h hω
  simpa only [smul_smul] using h'

/-- **`prop:record:upper`(i), a deleted record** (charging rule (i), `rem:cp:charging`): a deleted
record `ωκ` with `κ ≥ 0` symmetric at the cut (a two-layer record is a coupling of its actual
half marginal with itself, symmetric under the layer interchange) has the bracket
`(ω Diag(m)  -ωκ; -ωκ  ω Diag(m)) ⪰_c 0`: it is charged its mass, in the symmetric total only. -/
theorem deleted_record_bracket (c : ReflectionCut W) {κ : (W → Y) → ℝ} (hκ : ∀ z, 0 ≤ κ z)
    (hsym : IsSymmetricAt c (signedIntegral κ)) {ω : ℝ} (hω : 0 ≤ ω) :
    c.Bracket (ω • c.diagonalLaw (plusMarginal c κ)) (-(ω • signedIntegral κ))
      (ω • c.diagonalLaw (plusMarginal c κ)) :=
  bracket_delete c hκ hsym hω

end Brackets

/-! ## Polynomials in `r` -/

/-- The degrees `3, …, 7` of the upper polynomials `Π^rep_s`, `Π^rep_a`, `Π^del`
(`def:upper-comparison`: no terms below degree three). -/
def upperDegrees : Finset ℕ := Finset.Icc 3 7

/-- The polynomial `∑_{d=3}^{7} c_d r^d`. -/
noncomputable def polyEval (c : ℕ → ℝ) (r : ℝ) : ℝ := ∑ d ∈ upperDegrees, c d * r ^ d

theorem polyEval_add (c c' : ℕ → ℝ) (r : ℝ) :
    polyEval (fun d => c d + c' d) r = polyEval c r + polyEval c' r := by
  unfold polyEval
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- **Regrouping by degree.** A finite sum `∑_ρ c_ρ r^{e_ρ}` with every exponent in `[3, 7]` is
the polynomial whose coefficient of `r^d` is the sum of the `c_ρ` with `e_ρ = d`. -/
theorem poly_eval_regroup {R : Type*} (s : Finset R) (c : R → ℝ) (e : R → ℕ)
    (he : ∀ ρ ∈ s, e ρ ∈ upperDegrees) (r : ℝ) :
    ∑ ρ ∈ s, c ρ * r ^ e ρ = polyEval (fun d => ∑ ρ ∈ s.filter (fun ρ => e ρ = d), c ρ) r := by
  unfold polyEval
  rw [← Finset.sum_fiberwise_of_maps_to he]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [(Finset.mem_filter.mp hρ).2]

/-! ## The record ledger of a block -/

/-- The fate of a record in `def:upper-comparison`: kept (a), changed ((b): one-way repair; (b′):
LE mixture or dense EL law), deleted (c). -/
inductive Fate
  | kept
  | changed
  | deleted
  deriving DecidableEq

/-- **The records of an upper block and their coefficients** (`def:upper-comparison`), as far as
the prices need them: the weight `w ρ ≥ 0` (`w_𝔱` or `v_𝔱`), the overall degree `deg ρ`, the fate,
and the symmetric and skew coefficients `C^s ρ, C^a ρ ≥ 0` of a changed record ((F7), (F9); for a
record that is not changed they are not used). -/
structure RecordLedger (R : Type*) [Fintype R] where
  w : R → ℝ
  deg : R → ℕ
  fate : R → Fate
  Cs : R → ℝ
  Ca : R → ℝ
  w_nonneg : ∀ ρ, 0 ≤ w ρ
  Cs_nonneg : ∀ ρ, 0 ≤ Cs ρ
  Ca_nonneg : ∀ ρ, 0 ≤ Ca ρ

namespace RecordLedger

variable {R : Type*} [Fintype R] (Lg : RecordLedger R)

/-- The unpriced symmetric coefficient of a record (proof of `prop:record:upper`(i)). -/
noncomputable def symCoef (r : ℝ) (ρ : R) : ℝ :=
  match Lg.fate ρ with
  | .kept => 0
  | .changed => Lg.w ρ * Lg.Cs ρ * r ^ (Lg.deg ρ + 1)
  | .deleted => Lg.w ρ * r ^ Lg.deg ρ

/-- The unpriced skew coefficient of a record: deleted records are symmetric and are charged in
the symmetric total only. -/
noncomputable def skewCoef (r : ℝ) (ρ : R) : ℝ :=
  match Lg.fate ρ with
  | .kept => 0
  | .changed => Lg.w ρ * Lg.Ca ρ * r ^ (Lg.deg ρ + 1)
  | .deleted => 0

/-- The changed records. -/
def changed : Finset R := univ.filter (fun ρ => Lg.fate ρ = .changed)

/-- The deleted records. -/
def deleted : Finset R := univ.filter (fun ρ => Lg.fate ρ = .deleted)

/-- `Π^rep_s(r) = ∑_{changed} w C^s r^{deg+1}`. -/
noncomputable def piRepS (r : ℝ) : ℝ := ∑ ρ ∈ Lg.changed, Lg.w ρ * Lg.Cs ρ * r ^ (Lg.deg ρ + 1)

/-- `Π^rep_a(r) = ∑_{changed} w C^a r^{deg+1}`. -/
noncomputable def piRepA (r : ℝ) : ℝ := ∑ ρ ∈ Lg.changed, Lg.w ρ * Lg.Ca ρ * r ^ (Lg.deg ρ + 1)

/-- `Π^del(r) = ∑_{deleted} w r^{deg}`. -/
noncomputable def piDel (r : ℝ) : ℝ := ∑ ρ ∈ Lg.deleted, Lg.w ρ * r ^ Lg.deg ρ

/-- The ledger `Λ^s_k = ∑ C^s` over the changed records of degree `k`, weighted. -/
noncomputable def ledgerS (k : ℕ) : ℝ :=
  ∑ ρ ∈ Lg.changed.filter (fun ρ => Lg.deg ρ = k), Lg.w ρ * Lg.Cs ρ

/-- The weighted skew ledger of degree `k`. -/
noncomputable def ledgerA (k : ℕ) : ℝ :=
  ∑ ρ ∈ Lg.changed.filter (fun ρ => Lg.deg ρ = k), Lg.w ρ * Lg.Ca ρ

theorem symCoef_eq (r : ℝ) (ρ : R) :
    Lg.symCoef r ρ = (if Lg.fate ρ = .changed then Lg.w ρ * Lg.Cs ρ * r ^ (Lg.deg ρ + 1) else 0) +
      (if Lg.fate ρ = .deleted then Lg.w ρ * r ^ Lg.deg ρ else 0) := by
  unfold symCoef
  cases Lg.fate ρ <;> simp

theorem skewCoef_eq (r : ℝ) (ρ : R) :
    Lg.skewCoef r ρ =
      if Lg.fate ρ = .changed then Lg.w ρ * Lg.Ca ρ * r ^ (Lg.deg ρ + 1) else 0 := by
  unfold skewCoef
  cases Lg.fate ρ <;> simp

/-- **`prop:record:upper`(i), the symmetric total**: the unpriced symmetric coefficients of the
records sum to `Π^rep_s(r) + Π^del(r)`. -/
theorem sum_symCoef (r : ℝ) : ∑ ρ, Lg.symCoef r ρ = Lg.piRepS r + Lg.piDel r := by
  simp only [Lg.symCoef_eq, Finset.sum_add_distrib, piRepS, piDel, changed, deleted,
    Finset.sum_filter]

/-- **`prop:record:upper`(i), the skew total**: `Π^rep_a(r)`. -/
theorem sum_skewCoef (r : ℝ) : ∑ ρ, Lg.skewCoef r ρ = Lg.piRepA r := by
  simp only [Lg.skewCoef_eq, piRepA, changed, Finset.sum_filter]

theorem symCoef_nonneg {r : ℝ} (hr : 0 ≤ r) (ρ : R) : 0 ≤ Lg.symCoef r ρ := by
  unfold symCoef
  cases Lg.fate ρ
  · exact le_rfl
  · exact mul_nonneg (mul_nonneg (Lg.w_nonneg ρ) (Lg.Cs_nonneg ρ)) (pow_nonneg hr _)
  · exact mul_nonneg (Lg.w_nonneg ρ) (pow_nonneg hr _)

theorem skewCoef_nonneg {r : ℝ} (hr : 0 ≤ r) (ρ : R) : 0 ≤ Lg.skewCoef r ρ := by
  unfold skewCoef
  cases Lg.fate ρ
  · exact le_rfl
  · exact mul_nonneg (mul_nonneg (Lg.w_nonneg ρ) (Lg.Ca_nonneg ρ)) (pow_nonneg hr _)
  · exact le_rfl

/-- **The regrouping by state and degree** (`def:upper-comparison`): when every changed record
has degree two or three, `Π^rep_s(r) = r³ Λ^s_2 + r⁴ Λ^s_3` with the weighted ledgers. -/
theorem piRepS_eq (h23 : ∀ ρ ∈ Lg.changed, Lg.deg ρ = 2 ∨ Lg.deg ρ = 3) (r : ℝ) :
    Lg.piRepS r = r ^ 3 * Lg.ledgerS 2 + r ^ 4 * Lg.ledgerS 3 := by
  unfold piRepS ledgerS
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not Lg.changed (fun ρ => Lg.deg ρ = 2)]
  congr 1
  · exact Finset.sum_congr rfl fun ρ hρ => by
      rw [(Finset.mem_filter.mp hρ).2]; ring
  · have hset : Lg.changed.filter (fun ρ => ¬ Lg.deg ρ = 2) =
        Lg.changed.filter (fun ρ => Lg.deg ρ = 3) := by
      ext ρ
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h, h2⟩
        exact ⟨h, (h23 ρ h).resolve_left h2⟩
      · rintro ⟨h, h3⟩
        exact ⟨h, by omega⟩
    rw [hset]
    exact Finset.sum_congr rfl fun ρ hρ => by
      rw [(Finset.mem_filter.mp hρ).2]; ring

/-- The same regrouping for the skew polynomial. -/
theorem piRepA_eq (h23 : ∀ ρ ∈ Lg.changed, Lg.deg ρ = 2 ∨ Lg.deg ρ = 3) (r : ℝ) :
    Lg.piRepA r = r ^ 3 * Lg.ledgerA 2 + r ^ 4 * Lg.ledgerA 3 := by
  unfold piRepA ledgerA
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not Lg.changed (fun ρ => Lg.deg ρ = 2)]
  congr 1
  · exact Finset.sum_congr rfl fun ρ hρ => by
      rw [(Finset.mem_filter.mp hρ).2]; ring
  · have hset : Lg.changed.filter (fun ρ => ¬ Lg.deg ρ = 2) =
        Lg.changed.filter (fun ρ => Lg.deg ρ = 3) := by
      ext ρ
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h, h2⟩
        exact ⟨h, (h23 ρ h).resolve_left h2⟩
      · rintro ⟨h, h3⟩
        exact ⟨h, by omega⟩
    rw [hset]
    exact Finset.sum_congr rfl fun ρ hρ => by
      rw [(Finset.mem_filter.mp hρ).2]; ring

/-- The coefficient sequence of `Π^rep_s + Π^del`. -/
noncomputable def coefS (d : ℕ) : ℝ :=
  (∑ ρ ∈ Lg.changed.filter (fun ρ => Lg.deg ρ + 1 = d), Lg.w ρ * Lg.Cs ρ) +
    ∑ ρ ∈ Lg.deleted.filter (fun ρ => Lg.deg ρ = d), Lg.w ρ

/-- The coefficient sequence of `Π^rep_a`. -/
noncomputable def coefA (d : ℕ) : ℝ :=
  ∑ ρ ∈ Lg.changed.filter (fun ρ => Lg.deg ρ + 1 = d), Lg.w ρ * Lg.Ca ρ

/-- The degrees of a ledger lie in `[3, 7]`: changed records have degree two to six, deleted
records three to seven (`def:upper-comparison`: `Π^del` has no terms below degree three). -/
def DegreesInRange : Prop :=
  (∀ ρ ∈ Lg.changed, Lg.deg ρ + 1 ∈ upperDegrees) ∧ ∀ ρ ∈ Lg.deleted, Lg.deg ρ ∈ upperDegrees

theorem coefS_nonneg (d : ℕ) : 0 ≤ Lg.coefS d :=
  add_nonneg (Finset.sum_nonneg fun ρ _ => mul_nonneg (Lg.w_nonneg ρ) (Lg.Cs_nonneg ρ))
    (Finset.sum_nonneg fun ρ _ => Lg.w_nonneg ρ)

theorem coefA_nonneg (d : ℕ) : 0 ≤ Lg.coefA d :=
  Finset.sum_nonneg fun ρ _ => mul_nonneg (Lg.w_nonneg ρ) (Lg.Ca_nonneg ρ)

/-- `Π^rep_s + Π^del` is the polynomial of `coefS`. -/
theorem piRepS_add_piDel_eq (hdeg : Lg.DegreesInRange) (r : ℝ) :
    Lg.piRepS r + Lg.piDel r = polyEval Lg.coefS r := by
  have h1 : Lg.piRepS r = polyEval (fun d => ∑ ρ ∈ Lg.changed.filter
      (fun ρ => Lg.deg ρ + 1 = d), Lg.w ρ * Lg.Cs ρ) r :=
    poly_eval_regroup Lg.changed (fun ρ => Lg.w ρ * Lg.Cs ρ) (fun ρ => Lg.deg ρ + 1) hdeg.1 r
  have h2 : Lg.piDel r = polyEval (fun d => ∑ ρ ∈ Lg.deleted.filter
      (fun ρ => Lg.deg ρ = d), Lg.w ρ) r :=
    poly_eval_regroup Lg.deleted Lg.w Lg.deg hdeg.2 r
  rw [h1, h2, ← polyEval_add]
  rfl

/-- `Π^rep_a` is the polynomial of `coefA`. -/
theorem piRepA_eq_poly (hdeg : Lg.DegreesInRange) (r : ℝ) :
    Lg.piRepA r = polyEval Lg.coefA r :=
  poly_eval_regroup Lg.changed (fun ρ => Lg.w ρ * Lg.Ca ρ) (fun ρ => Lg.deg ρ + 1) hdeg.1 r

end RecordLedger

/-- **`prop:record:upper`(i), the block prices.** Let the record coefficients of the comparison
law of a block be at most the unpriced coefficients of its ledger divided by the normalizer
`P_μ(r) ≥ 1` (the brackets of `changed_record_bracket`, `deleted_record_bracket` with
`ω = w r^{deg}/P_μ`), and let the prices carry the factor `q_𝔅^{2a} ≥ 0` (`def:price`). Then
`s_𝔅 ≤ (Π^rep_s + Π^del)(r) q_𝔅^{2a}` and `a_𝔅 ≤ Π^rep_a(r) q_𝔅^{2a}`. -/
theorem block_prices_le {R : Type*} [Fintype R] (Lg : RecordLedger R) {r Pμ sel : ℝ}
    (hr : 0 ≤ r) (hP : 1 ≤ Pμ) (hsel : 0 ≤ sel) (πs πa : R → ℝ)
    (hπs : ∀ ρ, πs ρ ≤ Lg.symCoef r ρ / Pμ) (hπa : ∀ ρ, πa ρ ≤ Lg.skewCoef r ρ / Pμ) :
    (∑ ρ, πs ρ) * sel ≤ (Lg.piRepS r + Lg.piDel r) * sel ∧
      (∑ ρ, πa ρ) * sel ≤ Lg.piRepA r * sel := by
  have hP0 : 0 < Pμ := lt_of_lt_of_le one_pos hP
  have hdiv : ∀ x : ℝ, 0 ≤ x → x / Pμ ≤ x := fun x hx => div_le_self hx hP
  constructor
  · apply mul_le_mul_of_nonneg_right _ hsel
    rw [← Lg.sum_symCoef]
    exact Finset.sum_le_sum fun ρ _ => (hπs ρ).trans (hdiv _ (Lg.symCoef_nonneg hr ρ))
  · apply mul_le_mul_of_nonneg_right _ hsel
    rw [← Lg.sum_skewCoef]
    exact Finset.sum_le_sum fun ρ _ => (hπa ρ).trans (hdiv _ (Lg.skewCoef_nonneg hr ρ))

/-! ## Part (ii): the sum over the blocks of a band -/

/-- **`prop:record:upper`(ii), one band.** Let `c_d ≥ 0` and let `𝒰_d` bound
`∑_𝔅 q_𝔅^{2a} b_𝔅^{-d/2}` over the blocks of the band (`r_𝔅 = b_𝔅^{-1/2}`, so
`b_𝔅^{-d/2} = r_𝔅^d`). If every block has `s_𝔅 ≤ (∑_d c_d r_𝔅^d) q_𝔅^{2a}`, then
`∑_𝔅 s_𝔅 ≤ ∑_d c_d 𝒰_d`. -/
theorem band_sum_le {Blk : Type*} (blocks : Finset Blk) (rB sel s : Blk → ℝ) (c U : ℕ → ℝ)
    (hc : ∀ d ∈ upperDegrees, 0 ≤ c d)
    (hU : ∀ d ∈ upperDegrees, ∑ B ∈ blocks, sel B * rB B ^ d ≤ U d)
    (hs : ∀ B ∈ blocks, s B ≤ polyEval c (rB B) * sel B) :
    ∑ B ∈ blocks, s B ≤ ∑ d ∈ upperDegrees, c d * U d := by
  calc ∑ B ∈ blocks, s B ≤ ∑ B ∈ blocks, polyEval c (rB B) * sel B := Finset.sum_le_sum hs
    _ = ∑ d ∈ upperDegrees, c d * ∑ B ∈ blocks, sel B * rB B ^ d := by
        unfold polyEval
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun B _ => by ring
    _ ≤ ∑ d ∈ upperDegrees, c d * U d :=
        Finset.sum_le_sum fun d hd => mul_le_mul_of_nonneg_left (hU d hd) (hc d hd)

/-- **The repriced charges** (`prop:record:upper`(ii), `lem:record:repricing`): if
`∑_𝔅 q_𝔅^{2a_c} b_𝔅^{-d/2} ≤ 𝒰_d(a_c)`, `q_𝔅 ≥ 1`, `log q_𝔅 ≤ l` and `a_c ≤ a`, then
`∑_𝔅 q_𝔅^{2a} b_𝔅^{-d/2} ≤ e^{2(a-a_c)l} 𝒰_d(a_c)`. -/
theorem charge_reprice {Blk : Type*} (blocks : Finset Blk) (q w : Blk → ℝ) {a ac l Uc : ℝ}
    (hw : ∀ B ∈ blocks, 0 ≤ w B) (hq : ∀ B ∈ blocks, 1 ≤ q B)
    (hlog : ∀ B ∈ blocks, Real.log (q B) ≤ l) (ha : ac ≤ a)
    (hU : ∑ B ∈ blocks, q B ^ (2 * ac) * w B ≤ Uc) :
    ∑ B ∈ blocks, q B ^ (2 * a) * w B ≤ Real.exp (2 * (a - ac) * l) * Uc := by
  have h := Sarkozy.Comparison.total_reprice blocks w q hw hq hlog ha
  calc ∑ B ∈ blocks, q B ^ (2 * a) * w B = ∑ B ∈ blocks, w B * q B ^ (2 * a) :=
        Finset.sum_congr rfl fun B _ => mul_comm _ _
    _ ≤ Real.exp (2 * (a - ac) * l) * ∑ B ∈ blocks, w B * q B ^ (2 * ac) := h
    _ = Real.exp (2 * (a - ac) * l) * ∑ B ∈ blocks, q B ^ (2 * ac) * w B := by
        congr 1
        exact Finset.sum_congr rfl fun B _ => mul_comm _ _
    _ ≤ Real.exp (2 * (a - ac) * l) * Uc :=
        mul_le_mul_of_nonneg_left hU (Real.exp_pos _).le

/-- **The upper total** `S_u(a) = ∑_bands ∑_d c_{β,d} 𝒰_{β,d}(a) + S_tail(a)`
(`prop:record:upper`(ii)), for coefficient sequences `c_β` (those of `Π^rep_s + Π^del`, or of
`Π^rep_a` for `A_u`) and charges `𝒰_β`. -/
noncomputable def upperTotal {Bd : Type*} (bands : Finset Bd) (c U : Bd → ℕ → ℝ) (tail : ℝ) :
    ℝ :=
  ∑ β ∈ bands, ∑ d ∈ upperDegrees, c β d * U β d + tail

/-- **`prop:record:upper`(ii).** Sum (i) over the blocks of each band, with the charges
`𝒰_{β,d}`, and add the tail prices: the upper part `∑_{𝔅 upper} s_𝔅 + ∑_{p ≥ P₄} s_p` is at
most `S_u(a)` (and likewise for the skew prices and `A_u(a)`). The per-block bounds are (i)
(`block_prices_le`), the charges are `lem:record:block-charge`(i) repriced by
`charge_reprice`, and the tail bound `∑_{p ≥ P₄} s_p ≤ S_tail(a)` is `lem:tail-prices`(iv); all
three enter as hypotheses. -/
theorem upper_totals_le {Bd Blk P : Type*} (bands : Finset Bd) (blocks : Bd → Finset Blk)
    (tail : Finset P) (rB sel s : Blk → ℝ) (sp : P → ℝ) (c U : Bd → ℕ → ℝ) (Stail : ℝ)
    (hc : ∀ β ∈ bands, ∀ d ∈ upperDegrees, 0 ≤ c β d)
    (hU : ∀ β ∈ bands, ∀ d ∈ upperDegrees, ∑ B ∈ blocks β, sel B * rB B ^ d ≤ U β d)
    (hs : ∀ β ∈ bands, ∀ B ∈ blocks β, s B ≤ polyEval (c β) (rB B) * sel B)
    (htail : ∑ p ∈ tail, sp p ≤ Stail) :
    ∑ β ∈ bands, ∑ B ∈ blocks β, s B + ∑ p ∈ tail, sp p ≤ upperTotal bands c U Stail := by
  unfold upperTotal
  refine add_le_add (Finset.sum_le_sum fun β hβ => ?_) htail
  exact band_sum_le (blocks β) rB sel s (c β) (U β) (hc β hβ) (hU β hβ) (hs β hβ)

/-- **`prop:record:upper`(ii) for the totals of the target** (`TheoremCParam.ComparisonLaw`,
fields `S_total`, `A_total`): for prices `π b t ε` on a finite type of atoms, the symmetric
totals `symTotal π b = ∑_t π^s_{b,t}` of the upper atoms, grouped by bands, plus those of the
tail atoms, are at most `S_u(a)`, given the per-block bounds of (i) and the tail bound. -/
theorem upper_symTotal_le {Atom : Type*} {T : Atom → Type*} [∀ b, Fintype (T b)] {Bd : Type*}
    (π : ∀ b, T b → ChangeType → ℝ) (bands : Finset Bd) (blocks : Bd → Finset Atom)
    (tail : Finset Atom) (rB sel : Atom → ℝ) (c U : Bd → ℕ → ℝ) (Stail : ℝ)
    (hc : ∀ β ∈ bands, ∀ d ∈ upperDegrees, 0 ≤ c β d)
    (hU : ∀ β ∈ bands, ∀ d ∈ upperDegrees, ∑ B ∈ blocks β, sel B * rB B ^ d ≤ U β d)
    (hs : ∀ β ∈ bands, ∀ B ∈ blocks β, symTotal π B ≤ polyEval (c β) (rB B) * sel B)
    (htail : ∑ p ∈ tail, symTotal π p ≤ Stail) :
    ∑ β ∈ bands, ∑ B ∈ blocks β, symTotal π B + ∑ p ∈ tail, symTotal π p ≤
      upperTotal bands c U Stail :=
  upper_totals_le bands blocks tail rB sel (symTotal π) (symTotal π) c U Stail hc hU hs htail

/-- The skew counterpart of `upper_symTotal_le`, with the coefficients of `Π^rep_a` and the tail
bound `A_tail(a)`. -/
theorem upper_skewTotal_le {Atom : Type*} {T : Atom → Type*} [∀ b, Fintype (T b)] {Bd : Type*}
    (π : ∀ b, T b → ChangeType → ℝ) (bands : Finset Bd) (blocks : Bd → Finset Atom)
    (tail : Finset Atom) (rB sel : Atom → ℝ) (c U : Bd → ℕ → ℝ) (Atail : ℝ)
    (hc : ∀ β ∈ bands, ∀ d ∈ upperDegrees, 0 ≤ c β d)
    (hU : ∀ β ∈ bands, ∀ d ∈ upperDegrees, ∑ B ∈ blocks β, sel B * rB B ^ d ≤ U β d)
    (hs : ∀ β ∈ bands, ∀ B ∈ blocks β, skewTotal π B ≤ polyEval (c β) (rB B) * sel B)
    (htail : ∑ p ∈ tail, skewTotal π p ≤ Atail) :
    ∑ β ∈ bands, ∑ B ∈ blocks β, skewTotal π B + ∑ p ∈ tail, skewTotal π p ≤
      upperTotal bands c U Atail :=
  upper_totals_le bands blocks tail rB sel (skewTotal π) (skewTotal π) c U Atail hc hU hs htail

/-! ## Part (iii) -/

/-- **`prop:record:upper`(iii).** With `C_band = ∑_{d=3}^{7} (c^s_d + c^a_d) r_X^{d-3}`
(`r_X = X^{-1/2}`, so `r_X^{d-3} = X^{-(d-3)/2}`), a block of the band with least prime `b ≥ X`
(`r = b^{-1/2} ≤ r_X`) has `s_𝔅 + a_𝔅 ≤ C_band b^{-3/2} q_𝔅^{2a}`, given the bounds of (i). -/
theorem block_price_const (cS cA : ℕ → ℝ) (hcS : ∀ d ∈ upperDegrees, 0 ≤ cS d)
    (hcA : ∀ d ∈ upperDegrees, 0 ≤ cA d) {r rX sel sB aB : ℝ} (hr : 0 ≤ r) (hrX : r ≤ rX)
    (hsel : 0 ≤ sel) (hs : sB ≤ polyEval cS r * sel) (ha : aB ≤ polyEval cA r * sel) :
    sB + aB ≤ (∑ d ∈ upperDegrees, (cS d + cA d) * rX ^ (d - 3)) * r ^ 3 * sel := by
  have hpoly : polyEval cS r + polyEval cA r ≤
      (∑ d ∈ upperDegrees, (cS d + cA d) * rX ^ (d - 3)) * r ^ 3 := by
    rw [← polyEval_add]
    unfold polyEval
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd3 : 3 ≤ d := (Finset.mem_Icc.mp hd).1
    have hpow : r ^ d = r ^ (d - 3) * r ^ 3 := by
      rw [← pow_add, Nat.sub_add_cancel hd3]
    have hle : r ^ (d - 3) ≤ rX ^ (d - 3) := pow_le_pow_left₀ hr hrX _
    rw [hpow]
    have hcd : 0 ≤ cS d + cA d := add_nonneg (hcS d hd) (hcA d hd)
    calc (cS d + cA d) * (r ^ (d - 3) * r ^ 3) = (cS d + cA d) * r ^ (d - 3) * r ^ 3 := by ring
      _ ≤ (cS d + cA d) * rX ^ (d - 3) * r ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hcd) (pow_nonneg hr _)
  calc sB + aB ≤ polyEval cS r * sel + polyEval cA r * sel := add_le_add hs ha
    _ = (polyEval cS r + polyEval cA r) * sel := by ring
    _ ≤ (∑ d ∈ upperDegrees, (cS d + cA d) * rX ^ (d - 3)) * r ^ 3 * sel :=
        mul_le_mul_of_nonneg_right hpoly hsel

/-- `(b^{-1/2})^d = b^{-d/2}`: the polynomials in `r = b^{-1/2}` are the block charges'
powers `b^{-d/2}` (`lem:record:block-charge`). -/
theorem rpow_neg_half_pow {b : ℝ} (hb : 0 ≤ b) (d : ℕ) :
    (b ^ (-(1 : ℝ) / 2)) ^ d = b ^ (-(d : ℝ) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
  congr 1
  ring

end Sarkozy.UpperComparison
