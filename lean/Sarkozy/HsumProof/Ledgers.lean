module

public import Sarkozy.HsumProof.UpperData
public import Sarkozy.UpperComparison.LowerBands
public import Sarkozy.UpperRecords.BandCompletion

@[expose] public section




open Finset

namespace Sarkozy.HsumProof

open Sarkozy.PartV Sarkozy.UpperComparison

/-! ## The paper's state ledgers -/

/-- The position of a state in the table (`LR RL DD DS SD SS LC CL DR RD SR RS`). -/
def stateIdx : PType × PType → Option ℕ
  | (.L, .R) => some 0
  | (.R, .L) => some 1
  | (.D, .D) => some 2
  | (.D, .S) => some 3
  | (.S, .D) => some 4
  | (.S, .S) => some 5
  | (.L, .C) => some 6
  | (.C, .L) => some 7
  | (.D, .R) => some 8
  | (.R, .D) => some 9
  | (.S, .R) => some 10
  | (.R, .S) => some 11
  | _ => none

/-- The table entry `(num_s, den_s, num_a, den_a)` of state `t` in band `k`. -/
def ledEntry (k : Fin 310) (t : PType × PType) : ℕ × ℕ × ℕ × ℕ :=
  match stateIdx t with
  | some i => (UpperData.ledgerTab.getD k.val []).getD i (0, 1, 0, 1)
  | none => (0, 1, 0, 1)

/-- `Λ^s(𝔱)` of band `k` (`upper_dense_refined.json`, `symmetric_ledger`). -/
def ledS (k : Fin 310) (t : PType × PType) : ℚ := ((ledEntry k t).1 : ℚ) / (ledEntry k t).2.1

/-- `Λ^a(𝔱)` of band `k` (`upper_dense_refined.json`, `skew_ledger`). -/
def ledA (k : Fin 310) (t : PType × PType) : ℚ :=
  ((ledEntry k t).2.2.1 : ℚ) / (ledEntry k t).2.2.2

theorem ledS_nonneg (k : Fin 310) (t : PType × PType) : 0 ≤ ledS k t := by
  unfold ledS
  positivity

theorem ledA_nonneg (k : Fin 310) (t : PType × PType) : 0 ≤ ledA k t := by
  unfold ledA
  positivity

/-- **The table agrees with `cert:upper-lower-bands`** on the 45 bands below `2⁴⁸`. -/
theorem lower_ledgers_eq : ∀ k : Fin 310, k.val < 45 → ∀ t : PType × PType,
    (ledS k t, ledA k t) = lowerLedger t := by
  decide +kernel

/-- The changed records of state `t`. -/
def changedOf (t : PType × PType) : Finset UpIdx :=
  univ.filter fun ρ => upperFate ρ = .changed ∧ ρ.2.1 = t

/-- **The data `Cs`, `Ca` have the paper's state ledgers** (`def:upper-comparison`): in every band,
the coefficients of the changed records of each state sum to at most `Λ^s(𝔱)`, `Λ^a(𝔱)` of
`upper_dense_refined.json`. -/
def PaperLedgers (Cs Ca : Fin 310 → UpIdx → ℝ) : Prop :=
  ∀ k t, (∑ ρ ∈ changedOf t, Cs k ρ ≤ (ledS k t : ℝ)) ∧ ∑ ρ ∈ changedOf t, Ca k ρ ≤ (ledA k t : ℝ)

/-! ## Regrouping the ledger coefficients by state -/

/-- The layer and the state of a record. -/
def keyOf (ρ : UpIdx) : Bool × (PType × PType) := (ρ.1, ρ.2.1)

/-- The weight of a layer and a state. -/
noncomputable def wOf (W : UpperWeights) : Bool × (PType × PType) → ℝ
  | (true, t) => W.w t.1 t.2
  | (false, t) => W.v t.1 t.2

theorem upperWeight_eq (W : UpperWeights) (ρ : UpIdx) : upperWeight W ρ = wOf W (keyOf ρ) := by
  rcases ρ with ⟨b, t, φ⟩
  cases b <;> rfl

theorem wOf_nonneg (W : UpperWeights) (key : Bool × (PType × PType)) : 0 ≤ wOf W key := by
  rcases key with ⟨b, t⟩
  cases b
  · exact W.v_nonneg _ _
  · exact W.w_nonneg _ _

/-- Changed records are two-layer records (`def:upper-comparison`(b)). -/
theorem changed_layer : ∀ ρ : UpIdx, upperFate ρ = .changed → ρ.1 = true := by
  decide +kernel

theorem changed_facts (W : UpperWeights) (ρ : UpIdx) (h : upperFate ρ = .changed) :
    upperDeg ρ = stateDeg ρ.2.1 ∧ upperWeight W ρ = W.w ρ.2.1.1 ρ.2.1.2 := by
  rcases ρ with ⟨b, t, φ⟩
  have hb := changed_layer _ h
  simp only at hb
  subst hb
  exact ⟨rfl, rfl⟩

/-- The number of deleted records of overall degree `d`, layer and state `key`. -/
def delCnt (d : ℕ) (key : Bool × (PType × PType)) : ℕ :=
  (univ.filter fun ρ : UpIdx => upperFate ρ = .deleted ∧ upperDeg ρ = d ∧ keyOf ρ = key).card

/-- The counts of `delCnt` (`lem:six-query-retention`: the 28 nonaccepting folded records of degree
three and every record of degree at least four). -/
def delTab : ℕ → Bool × (PType × PType) → ℕ
  | 3, (false, (.L, .R)) => 6
  | 3, (false, (.D, .D)) => 6
  | 3, (false, (.D, .S)) => 4
  | 3, (false, (.S, .D)) => 6
  | 3, (false, (.S, .S)) => 4
  | 3, (false, (.R, .L)) => 2
  | 4, (false, (.L, .C)) => 2
  | 4, (false, (.D, .R)) => 18
  | 4, (false, (.S, .R)) => 12
  | 4, (false, (.R, .D)) => 18
  | 4, (false, (.R, .S)) => 12
  | 4, (false, (.C, .L)) => 2
  | 4, (true, (.D, .C)) => 6
  | 4, (true, (.S, .C)) => 4
  | 4, (true, (.R, .R)) => 36
  | 4, (true, (.C, .D)) => 6
  | 4, (true, (.C, .S)) => 4
  | 5, (false, (.D, .C)) => 6
  | 5, (false, (.S, .C)) => 4
  | 5, (false, (.R, .R)) => 36
  | 5, (false, (.C, .D)) => 6
  | 5, (false, (.C, .S)) => 4
  | 5, (true, (.R, .C)) => 12
  | 5, (true, (.C, .R)) => 12
  | 6, (false, (.R, .C)) => 12
  | 6, (false, (.C, .R)) => 12
  | 6, (true, (.C, .C)) => 4
  | 7, (false, (.C, .C)) => 4
  | _, _ => 0

/-- **The deleted counts, by enumeration** of V1's 392 records. -/
theorem delCnt_eq : ∀ d ∈ Finset.Icc 3 7, ∀ key, delCnt d key = delTab d key := by
  decide +kernel

variable (W : UpperWeights) (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i) (hCa : ∀ i, 0 ≤ Ca i)

/-- The changed part of a ledger coefficient, regrouped by state. -/
theorem changed_sum_eq (C : UpIdx → ℝ) (d : ℕ) :
    ∑ ρ ∈ (univ.filter fun ρ : UpIdx => upperFate ρ = .changed).filter
        (fun ρ => upperDeg ρ + 1 = d), upperWeight W ρ * C ρ =
      ∑ t : PType × PType, if stateDeg t + 1 = d then
        W.w t.1 t.2 * ∑ ρ ∈ changedOf t, C ρ else 0 := by
  rw [← sum_fiberwise _ (fun ρ : UpIdx => ρ.2.1)]
  refine sum_congr rfl fun t _ => ?_
  split_ifs with hd
  · rw [mul_sum]
    apply sum_congr
    · ext ρ
      simp only [changedOf, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        refine ⟨⟨h1, ?_⟩, h3⟩
        rw [(changed_facts W ρ h1).1, h3, hd]
    · intro ρ hρ
      simp only [changedOf, mem_filter, mem_univ, true_and] at hρ
      rw [(changed_facts W ρ hρ.1).2, hρ.2]
  · apply sum_eq_zero
    intro ρ hρ
    simp only [mem_filter, mem_univ, true_and] at hρ
    exfalso
    apply hd
    rw [← hρ.2, ← (changed_facts W ρ hρ.1.1).1]
    exact hρ.1.2

/-- The deleted part of `coefS`, regrouped by layer and state. -/
theorem deleted_sum_eq (d : ℕ) :
    ∑ ρ ∈ (univ.filter fun ρ : UpIdx => upperFate ρ = .deleted).filter
        (fun ρ => upperDeg ρ = d), upperWeight W ρ =
      ∑ key : Bool × (PType × PType), (delCnt d key : ℝ) * wOf W key := by
  rw [← sum_fiberwise _ keyOf]
  refine sum_congr rfl fun key _ => ?_
  have hc : ((univ.filter fun ρ : UpIdx => upperFate ρ = .deleted).filter
      (fun ρ => upperDeg ρ = d)).filter (fun ρ => keyOf ρ = key) =
      univ.filter fun ρ : UpIdx => upperFate ρ = .deleted ∧ upperDeg ρ = d ∧ keyOf ρ = key := by
    ext ρ
    simp only [mem_filter, mem_univ, true_and, and_assoc]
  rw [hc, delCnt, ← nsmul_eq_mul, ← sum_const]
  refine sum_congr rfl fun ρ hρ => ?_
  simp only [mem_filter, mem_univ, true_and] at hρ
  rw [upperWeight_eq, hρ.2.2]

/-! ## The rational coefficients of a band -/

/-- The weight of a layer and a state of band `k`, as a rational. -/
def wOfQ (k : Fin 310) : Bool × (PType × PType) → ℚ
  | (true, t) => (UpperRecords.CompletionData.record k).w t.1 t.2
  | (false, t) => (UpperRecords.CompletionData.record k).v t.1 t.2

theorem wOfQ_cast (k : Fin 310) (key : Bool × (PType × PType)) :
    (wOfQ k key : ℝ) = wOf (UpperRecords.bandWeights k) key := by
  rcases key with ⟨b, t⟩
  cases b <;> rfl

/-- **The symmetric coefficient of degree `d` of band `k`** from the paper's ledgers. -/
def cSQ (k : Fin 310) (d : ℕ) : ℚ :=
  (∑ t : PType × PType, if stateDeg t + 1 = d then wOfQ k (true, t) * ledS k t else 0) +
    ∑ key : Bool × (PType × PType), (delTab d key : ℚ) * wOfQ k key

/-- **The skew coefficient of degree `d` of band `k`** from the paper's ledgers. -/
def cAQ (k : Fin 310) (d : ℕ) : ℚ :=
  ∑ t : PType × PType, if stateDeg t + 1 = d then wOfQ k (true, t) * ledA k t else 0

theorem coefS_le (k : Fin 310) (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i) (hCa : ∀ i, 0 ≤ Ca i)
    (hL : ∀ t, ∑ ρ ∈ changedOf t, Cs ρ ≤ (ledS k t : ℝ)) {d : ℕ} (hd : d ∈ Finset.Icc 3 7) :
    (upperLedger (UpperRecords.bandWeights k) Cs Ca hCs hCa).coefS d ≤ (cSQ k d : ℝ) := by
  unfold RecordLedger.coefS RecordLedger.changed RecordLedger.deleted
  change ∑ ρ ∈ (univ.filter fun ρ : UpIdx => upperFate ρ = .changed).filter
      (fun ρ => upperDeg ρ + 1 = d), upperWeight (UpperRecords.bandWeights k) ρ * Cs ρ +
    ∑ ρ ∈ (univ.filter fun ρ : UpIdx => upperFate ρ = .deleted).filter
      (fun ρ => upperDeg ρ = d), upperWeight (UpperRecords.bandWeights k) ρ ≤ _
  rw [changed_sum_eq, deleted_sum_eq]
  unfold cSQ
  push_cast
  apply add_le_add
  · apply sum_le_sum
    intro t _
    split_ifs
    · have hw := wOfQ_cast k (true, t)
      simp only [wOf] at hw
      rw [Rat.cast_mul, hw]
      exact mul_le_mul_of_nonneg_left (hL t) ((UpperRecords.bandWeights k).w_nonneg _ _)
    · rw [Rat.cast_zero]
  · apply le_of_eq
    refine sum_congr rfl fun key _ => ?_
    rw [delCnt_eq d hd key, wOfQ_cast]

theorem coefA_le (k : Fin 310) (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i) (hCa : ∀ i, 0 ≤ Ca i)
    (hL : ∀ t, ∑ ρ ∈ changedOf t, Ca ρ ≤ (ledA k t : ℝ)) (d : ℕ) :
    (upperLedger (UpperRecords.bandWeights k) Cs Ca hCs hCa).coefA d ≤ (cAQ k d : ℝ) := by
  unfold RecordLedger.coefA RecordLedger.changed
  change ∑ ρ ∈ (univ.filter fun ρ : UpIdx => upperFate ρ = .changed).filter
      (fun ρ => upperDeg ρ + 1 = d), upperWeight (UpperRecords.bandWeights k) ρ * Ca ρ ≤ _
  rw [changed_sum_eq]
  unfold cAQ
  push_cast
  apply sum_le_sum
  intro t _
  split_ifs
  · have hw := wOfQ_cast k (true, t)
    simp only [wOf] at hw
    rw [Rat.cast_mul, hw]
    exact mul_le_mul_of_nonneg_left (hL t) ((UpperRecords.bandWeights k).w_nonneg _ _)
  · rw [Rat.cast_zero]

end Sarkozy.HsumProof
