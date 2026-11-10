module

public import Sarkozy.PartV.SixQuery
public import Sarkozy.PartV.UpperReference
public import Sarkozy.UpperComparison.Prices

@[expose] public section

/-!
# The record ledger of the upper comparison law (`def:upper-comparison`)

`paper/sections/26_upper_comparison.tex`, `def:upper-comparison` and the first paragraph of the
proof of `prop:record:upper`(i), on V1's records of the upper reference.

The records of `μ̃_𝔅` are V1's components `UpIdx` (`Sarkozy.PartV.UpperReference`): a
two-layer (`true`) or folded (`false`) copy, a state `𝔱 = (𝔱₀, 𝔱₁)` and a pattern pair `φ`, with
the graded weight `upCoeff W r = w_𝔱 r^{deg 𝔱}` or `v_𝔱 r^{deg 𝔱 + 1}`. Acceptance of `𝓔₆` is V1's
edge acceptance (`TwoLayerEdgeAccepts`, `FoldedEdgeAccepts`, `lem:six-query-retention`).

**The fate of a record** (`upperFate`, `def:upper-comparison` (a)–(c)): an accepting record is
kept; a nonaccepting two-layer record of degree two or three is changed; every other record is
deleted. A changed record is replaced (`changeKind`, (b), (b′)):
* the six LE records of degree two (state `LR`) by the LE mixture (`prop:le-mixture`);
* the two nonaccepting EL records of degree two (state `RL`) by the dense law
  (`prop:dense-comparison`);
* the other `84` by their one-way repairs ((F7)).

**Proved** (exact enumeration over the `392` records, `decide +kernel`):
* `card_changed`: `92` records are changed; `card_oneWay`, `card_leMixture`, `card_denseEL`: of
  them `84` are repaired one way, `6` mixed and `2` replaced densely;
* `card_changed_deg2`, `card_changed_deg3`: `28` changed records of degree two and `64` of degree
  three, as in `lem:six-query-retention`;
* `upperFate_degrees`: changed records have overall degree two or three, deleted records degree
  three to seven, so `Π^rep` and `Π^del` have no terms below degree three and none above seven
  (`upperLedger_degreesInRange`); `deg_ge_four_deleted` and `piDel_coef_eq`: every record of
  degree at least four is deleted, so the coefficients of `Π^del` of degrees four to seven are
  those of `P_μ`. These are the remarks after `def:upper-comparison`.

**The ledger** `upperLedger W C^s C^a` is the `RecordLedger` of `Prices` on these records, with
weight `w_𝔱` or `v_𝔱` and overall degree `deg 𝔱` or `deg 𝔱 + 1`; its graded weights are V1's
(`upperLedger_mass`), and `paper_block_prices` is `block_prices_le` with the normalizer
`P_μ(r) = upPoly W r ≥ 1` of V1. The coefficients `C^s, C^a` of the changed records ((F7), (F9))
are parameters.
-/

open Finset

namespace Sarkozy.UpperComparison

open Sarkozy.PartV

/-- **The fate of a record of the upper reference** (`def:upper-comparison`): kept if it accepts
`𝓔₆` (edge acceptance, `lem:six-query-retention`), changed if it is a nonaccepting two-layer
record of degree two or three, deleted otherwise. -/
def upperFate : UpIdx → Fate
  | (true, ⟨t, φ⟩) =>
      if TwoLayerEdgeAccepts t φ then .kept
      else if stateDeg t = 2 ∨ stateDeg t = 3 then .changed else .deleted
  | (false, ⟨t, φ⟩) => if FoldedEdgeAccepts t φ then .kept else .deleted

/-- The overall degree of a record: `deg 𝔱` for a two-layer record, `deg 𝔱 + 1` for a folded
one. -/
def upperDeg : UpIdx → ℕ
  | (true, ⟨t, _⟩) => stateDeg t
  | (false, ⟨t, _⟩) => stateDeg t + 1

/-- The weight of a record: `w_𝔱` for a two-layer record, `v_𝔱` for a folded one. -/
def upperWeight (W : UpperWeights) : UpIdx → ℝ
  | (true, ⟨t, _⟩) => W.w t.1 t.2
  | (false, ⟨t, _⟩) => W.v t.1 t.2

/-- The three kinds of replacement of `def:upper-comparison` (b), (b′). -/
inductive ChangeKind
  | oneWay
  | leMixture
  | denseEL
  deriving DecidableEq

/-- The kind of replacement of a changed record: the LE records of degree two (state `LR`) are
mixed (`prop:le-mixture`), the nonaccepting EL records of degree two (state `RL`) are replaced
densely (`prop:dense-comparison`), the others are repaired one way ((F7)). -/
def changeKind (i : UpIdx) : Option ChangeKind :=
  if upperFate i = .changed then
    if i.2.1 = (.L, .R) then some .leMixture
    else if i.2.1 = (.R, .L) then some .denseEL
    else some .oneWay
  else none

/-- **`lem:six-query-retention`, the changed records**: `92` records are changed. -/
theorem card_changed : (univ.filter fun i : UpIdx => upperFate i = .changed).card = 92 := by
  decide +kernel

/-- Of the changed records, `28` have degree two and `64` degree three. -/
theorem card_changed_deg2 :
    (univ.filter fun i : UpIdx => upperFate i = .changed ∧ upperDeg i = 2).card = 28 := by
  decide +kernel

theorem card_changed_deg3 :
    (univ.filter fun i : UpIdx => upperFate i = .changed ∧ upperDeg i = 3).card = 64 := by
  decide +kernel

/-- **`def:upper-comparison`(b)**: `84` records are repaired one way. -/
theorem card_oneWay : (univ.filter fun i : UpIdx => changeKind i = some .oneWay).card = 84 := by
  decide +kernel

/-- **`def:upper-comparison`(b′)**: the six LE records of degree two are mixed. -/
theorem card_leMixture :
    (univ.filter fun i : UpIdx => changeKind i = some .leMixture).card = 6 := by
  decide +kernel

/-- **`def:upper-comparison`(b′)**: the two nonaccepting EL records of degree two are replaced
densely. -/
theorem card_denseEL : (univ.filter fun i : UpIdx => changeKind i = some .denseEL).card = 2 := by
  decide +kernel

/-- The mixed and the densely replaced records have degree two. -/
theorem changeKind_deg2 : ∀ i : UpIdx, (changeKind i = some .leMixture ∨
    changeKind i = some .denseEL) → upperDeg i = 2 := by
  decide +kernel

/-- **The degrees of the changed and deleted records**: changed records have overall degree two
or three, deleted records three to seven. -/
theorem upperFate_degrees : ∀ i : UpIdx,
    (upperFate i = .changed → (upperDeg i = 2 ∨ upperDeg i = 3)) ∧
      (upperFate i = .deleted → 3 ≤ upperDeg i ∧ upperDeg i ≤ 7) := by
  decide +kernel

/-- Every record of overall degree at least four is deleted (`lem:six-query-retention`: no
record of degree at least four accepts, and only degrees two and three are changed). -/
theorem deg_ge_four_deleted : ∀ i : UpIdx, 4 ≤ upperDeg i → upperFate i = .deleted := by
  decide +kernel

/-- **The record ledger of an upper block** on V1's records, with the coefficients `C^s, C^a` of
the changed records as parameters. -/
def upperLedger (W : UpperWeights) (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i)
    (hCa : ∀ i, 0 ≤ Ca i) : RecordLedger UpIdx where
  w := upperWeight W
  deg := upperDeg
  fate := upperFate
  Cs := Cs
  Ca := Ca
  w_nonneg := by
    rintro ⟨b, t, φ⟩
    cases b
    · exact W.v_nonneg _ _
    · exact W.w_nonneg _ _
  Cs_nonneg := hCs
  Ca_nonneg := hCa

section Ledger

variable (W : UpperWeights) (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i) (hCa : ∀ i, 0 ≤ Ca i)

/-- The graded weights of the ledger are V1's: `w ρ r^{deg ρ} = upCoeff W r ρ`. -/
theorem upperLedger_mass (r : ℝ) (i : UpIdx) :
    (upperLedger W Cs Ca hCs hCa).w i * r ^ (upperLedger W Cs Ca hCs hCa).deg i =
      upCoeff W r i := by
  rcases i with ⟨b, t, φ⟩
  cases b <;> rfl

/-- The changed records of the ledger have degree two or three. -/
theorem upperLedger_changed_deg (i : UpIdx) (hi : i ∈ (upperLedger W Cs Ca hCs hCa).changed) :
    (upperLedger W Cs Ca hCs hCa).deg i = 2 ∨ (upperLedger W Cs Ca hCs hCa).deg i = 3 :=
  (upperFate_degrees i).1 (Finset.mem_filter.mp hi).2

/-- **The degrees lie in `[3, 7]`** (the remark after `def:upper-comparison`). -/
theorem upperLedger_degreesInRange : (upperLedger W Cs Ca hCs hCa).DegreesInRange := by
  constructor
  · intro i hi
    rcases upperLedger_changed_deg W Cs Ca hCs hCa i hi with h | h <;>
      · rw [h]; decide
  · intro i hi
    have h := (upperFate_degrees i).2 (Finset.mem_filter.mp hi).2
    exact Finset.mem_Icc.mpr h

/-- **`prop:record:upper`(i) for the paper's records.** If the record coefficients of the
comparison law are at most the unpriced coefficients divided by `P_μ(r)` (V1's `upPoly W r`), the
block prices are `s_𝔅 ≤ (Π^rep_s + Π^del)(r) q_𝔅^{2a}` and `a_𝔅 ≤ Π^rep_a(r) q_𝔅^{2a}`, with
`Π^rep_s(r) = r³Λ^s_2 + r⁴Λ^s_3` (the ledgers weighted by `w_𝔱`). The bounds on the record
coefficients are the brackets of `changed_record_bracket` and `deleted_record_bracket`. -/
theorem paper_block_prices {r sel : ℝ} (hr : 0 ≤ r) (hsel : 0 ≤ sel) (πs πa : UpIdx → ℝ)
    (hπs : ∀ ρ, πs ρ ≤ (upperLedger W Cs Ca hCs hCa).symCoef r ρ / upPoly W r)
    (hπa : ∀ ρ, πa ρ ≤ (upperLedger W Cs Ca hCs hCa).skewCoef r ρ / upPoly W r) :
    (∑ ρ, πs ρ) * sel ≤
        (r ^ 3 * (upperLedger W Cs Ca hCs hCa).ledgerS 2 +
          r ^ 4 * (upperLedger W Cs Ca hCs hCa).ledgerS 3 +
          (upperLedger W Cs Ca hCs hCa).piDel r) * sel ∧
      (∑ ρ, πa ρ) * sel ≤
        (r ^ 3 * (upperLedger W Cs Ca hCs hCa).ledgerA 2 +
          r ^ 4 * (upperLedger W Cs Ca hCs hCa).ledgerA 3) * sel := by
  have h := block_prices_le (upperLedger W Cs Ca hCs hCa) hr (one_le_upPoly W hr) hsel πs πa
    hπs hπa
  rw [(upperLedger W Cs Ca hCs hCa).piRepS_eq (upperLedger_changed_deg W Cs Ca hCs hCa) r] at h
  rw [(upperLedger W Cs Ca hCs hCa).piRepA_eq (upperLedger_changed_deg W Cs Ca hCs hCa) r] at h
  exact h

/-- **The deletion polynomial is a sum of V1's graded weights**: `Π^del(r) = ∑_{deleted}
upCoeff W r ρ`, the total weight of the deleted records (`def:upper-comparison`). -/
theorem upperLedger_piDel (r : ℝ) :
    (upperLedger W Cs Ca hCs hCa).piDel r =
      ∑ ρ ∈ (upperLedger W Cs Ca hCs hCa).deleted, upCoeff W r ρ :=
  Finset.sum_congr rfl fun ρ _ => upperLedger_mass W Cs Ca hCs hCa r ρ

/-- **The deletion polynomial in degrees four to seven** (the remark after
`def:upper-comparison`): every record of overall degree `d ≥ 4` is deleted, so the coefficient of
`r^d` in `Π^del` is the total weight of all records of degree `d`, the coefficient of `r^d` in
`P_μ`. -/
theorem piDel_coef_eq (d : ℕ) (hd : 4 ≤ d) :
    ∑ ρ ∈ (upperLedger W Cs Ca hCs hCa).deleted.filter (fun ρ => upperDeg ρ = d),
        upperWeight W ρ =
      ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperDeg ρ = d), upperWeight W ρ := by
  congr 1
  ext ρ
  simp only [upperLedger, RecordLedger.deleted, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, deg_ge_four_deleted ρ (h ▸ hd)⟩, h⟩

end Ledger

end Sarkozy.UpperComparison
