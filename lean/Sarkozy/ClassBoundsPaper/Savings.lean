module

public import Sarkozy.ClassBoundsPaper.Algebra
public import Sarkozy.TargetLedger.Numerics

@[expose] public section






open Finset
open scoped BigOperators

namespace Sarkozy.ClassBoundsPaper

open Sarkozy.RecordExpansion Sarkozy.Comparison Sarkozy.TargetLedger

/-! ### The data (rationals) -/

/-- The ledger's energy factor `B` (`targetLedger.B`). -/
def bLed : ℚ := 252006527019 / 125000000000

/-- `A_F`, the full skew total of the fold records (upper end at `a_T`, rounded up). -/
def gF : ℚ := 446178668434237412523900665361 / 1000000000000000000000000000000

/-- `A_E`, the full skew total of the matching records (upper end at `a_T`, rounded up). -/
def gE : ℚ := 21900161781910134996875531319 / 62500000000000000000000000000

/-- `A^arm_F`, the raw-arm total of the fold records (upper end at `a_T`, rounded up). -/
def bF : ℚ := 350402582539780634749838448779 / 1000000000000000000000000000000

/-- `A^arm_E`, the raw-arm total of the matching records (upper end at `a_T`, rounded up). -/
def bE : ℚ := 350402582539780634749838448779 / 1000000000000000000000000000000

/-- `A^lead_F`, the leading total of the fold records (upper end at `a_T`, rounded up). -/
def lF : ℚ := 446131714957935043579227939743 / 1000000000000000000000000000000

/-- `A^lead_E`, the leading total of the matching records (upper end at `a_T`, rounded up). -/
def lE : ℚ := 10950080741685527798722847513 / 31250000000000000000000000000

/-- `A^rem_F`, the remainder total of the fold records (upper end at `a_T`, rounded up). -/
def rF : ℚ := 23476738151184472336362809 / 500000000000000000000000000000

/-- `A^rem_E`, the remainder total of the matching records (upper end at `a_T`, rounded up). -/
def rE : ℚ := 11948194292139199580747 / 1000000000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(1, 3)` (upper end, rounded up). -/
def c13 : ℚ := 697228360187515918663895270749 / 500000000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(2, 2)` (upper end, rounded up). -/
def c22 : ℚ := 1969575617833382748788380236227 / 1000000000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(3, 1)` (upper end, rounded up). -/
def c31 : ℚ := 1227601742756053409823989878311 / 500000000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(4, 0)` (upper end, rounded up). -/
def c40 : ℚ := 1521879197250811172287337392519 / 500000000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(1, 5)` (upper end, rounded up). -/
def c15 : ℚ := 237999190597972795736853872559 / 125000000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(2, 4)` (upper end, rounded up). -/
def c24 : ℚ := 1317151756095965843612336823379 / 500000000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(3, 3)` (upper end, rounded up). -/
def c33 : ℚ := 1637532111439378312555615091249 / 500000000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(4, 2)` (upper end, rounded up). -/
def c42 : ℚ := 162504858564631367820569797153 / 40000000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(5, 1)` (upper end, rounded up). -/
def c51 : ℚ := 2549611795815622863669082541097 / 500000000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(6, 0)` (upper end, rounded up). -/
def c60 : ℚ := 6432077622584909665154271557673 / 1000000000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(2, 0)` (upper end, rounded up). -/
def c20 : ℚ := 83194843871218258719119734337 / 40000000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(1, 1)` (upper end, rounded up). -/
def c11 : ℚ := 6263612802950267001034601239 / 4000000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(EE, al)` (upper end, rounded up). -/
def cEEal : ℚ := 1345183660753520239899578326401 / 1000000000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(EE, cr)` (upper end, rounded up). -/
def cEEcr : ℚ := 57463594861797534988578691699 / 62500000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(0, 4)` (upper end, rounded up). -/
def c04 : ℚ := 497307409742345201902919245611 / 500000000000000000000000000000

/-- The class cost `C_{n,m}` of the class `(0, 6)` (upper end, rounded up). -/
def c06 : ℚ := 67073095679893104588873826721 / 50000000000000000000000000000

/-- The class cost of the general classes `(n, m)`, `n ≥ 1`. -/
def cGen : ℕ → ℕ → ℚ
  | 1, 1 => c11
  | 2, 0 => c20
  | 1, 3 => c13
  | 2, 2 => c22
  | 3, 1 => c31
  | 4, 0 => c40
  | 1, 5 => c15
  | 2, 4 => c24
  | 3, 3 => c33
  | 4, 2 => c42
  | 5, 1 => c51
  | 6, 0 => c60
  | _, _ => 0

/-- The class cost of the degree vector `(n, m₀, m₁)` (kinds fold, `E₀`, `E₁`). -/
def cQ (n m₀ m₁ : ℕ) : ℚ :=
  if n = 0 then
    (if m₀ + m₁ = 2 then (if m₀ = 1 then cEEcr else cEEal)
      else if m₀ + m₁ = 4 then c04 else c06)
  else cGen n (m₀ + m₁)

/-- The factorial (an exposed copy, for the kernel). -/
def fct : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fct n

/-- The saving of the degree vector `(n, m₀, m₁)`, each matching kind with half of the totals. -/
def savQ (n m₀ m₁ : ℕ) : ℚ :=
  (bLed * (gF ^ n * (gE / 2) ^ m₀ * (gE / 2) ^ m₁) -
      cQ n m₀ m₁ * (bF ^ n * (bE / 2) ^ m₀ * (bE / 2) ^ m₁) -
      bLed * ((lF + rF) ^ n * (lE / 2 + rE / 2) ^ m₀ * (lE / 2 + rE / 2) ^ m₁ -
        lF ^ n * (lE / 2) ^ m₀ * (lE / 2) ^ m₁)) /
    ((fct n * fct m₀ * fct m₁ : ℕ) : ℚ)

/-- The 49 degree vectors `(n, m₀, m₁)` with `n + m₀ + m₁ ∈ {2, 4, 6}`. -/
def triples : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 2), (0, 0, 4), (0, 0, 6), (0, 1, 1), (0, 1, 3), (0, 1, 5), (0, 2, 0), (0, 2, 2),
   (0, 2, 4), (0, 3, 1), (0, 3, 3), (0, 4, 0), (0, 4, 2), (0, 5, 1), (0, 6, 0), (1, 0, 1),
   (1, 0, 3), (1, 0, 5), (1, 1, 0), (1, 1, 2), (1, 1, 4), (1, 2, 1), (1, 2, 3), (1, 3, 0),
   (1, 3, 2), (1, 4, 1), (1, 5, 0), (2, 0, 0), (2, 0, 2), (2, 0, 4), (2, 1, 1), (2, 1, 3),
   (2, 2, 0), (2, 2, 2), (2, 3, 1), (2, 4, 0), (3, 0, 1), (3, 0, 3), (3, 1, 0), (3, 1, 2),
   (3, 2, 1), (3, 3, 0), (4, 0, 0), (4, 0, 2), (4, 1, 1), (4, 2, 0), (5, 0, 1), (5, 1, 0),
   (6, 0, 0)]

/-- A list sum (an exposed copy, for the kernel). -/
def lsum : List ℚ → ℚ
  | [] => 0
  | x :: l => x + lsum l

/-- **The sixteen class savings at `a_T`** (`def:closing-quantities`(8), `cert:closing`),
kernel-checked: their sum is at least `0.264439290659` (the harness: `0.2644392906599531…`). -/
theorem savings_cert :
    (264439290659 / 1000000000000 : ℚ) ≤ lsum (triples.map fun t => savQ t.1 t.2.1 t.2.2) := by
  decide +kernel

theorem triples_nodup : triples.Nodup := by decide

theorem triples_deg : ∀ t ∈ triples, t.1 + t.2.1 + t.2.2 ∈ [2, 4, 6] := by decide

/-! ### The data over the reals -/

/-- The degree vector of a triple. -/
def toVec (t : ℕ × ℕ × ℕ) : Fin 3 → ℕ := ![t.1, t.2.1, t.2.2]

theorem toVec_injective : Function.Injective toVec := by
  intro s t h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [toVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  obtain ⟨a, b, c⟩ := s
  obtain ⟨a', b', c'⟩ := t
  simp_all

/-- **The replaced degree classes** of the closing (49 degree vectors). -/
noncomputable def paperN : Finset (Fin 3 → ℕ) := triples.toFinset.image toVec

/-- The class costs over the reals. -/
noncomputable def paperC (n : Fin 3 → ℕ) : ℝ := (cQ (n 0) (n 1) (n 2) : ℝ)

/-- The kind totals of the upper prices: fold, `E₀`, `E₁` (each matching kind half). -/
def totQ (x y : ℚ) : Fin 3 → ℚ
  | 0 => x
  | 1 => y / 2
  | 2 => y / 2

noncomputable def paperAtot (l : Fin 3) : ℝ := (totQ gF gE l : ℝ)
noncomputable def paperAarm (l : Fin 3) : ℝ := (totQ bF bE l : ℝ)
noncomputable def paperAlead (l : Fin 3) : ℝ := (totQ lF lE l : ℝ)
noncomputable def paperArem (l : Fin 3) : ℝ := (totQ rF rE l : ℝ)

theorem fct_eq (n : ℕ) : fct n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fct, ih, Nat.factorial_succ]

theorem saving_toVec (t : ℕ × ℕ × ℕ) :
    savingOfTotals (toVec t) (paperC (toVec t)) (bLed : ℝ) paperAtot paperAarm paperAlead
      paperArem = (savQ t.1 t.2.1 t.2.2 : ℝ) := by
  obtain ⟨n, m₀, m₁⟩ := t
  simp only [savingOfTotals, degFact, Fin.prod_univ_three, toVec, paperC, paperAtot, paperAarm,
    paperAlead, paperArem, totQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, savQ, fct_eq]
  push_cast
  ring

theorem lsum_cast (l : List ℚ) : ((lsum l : ℚ) : ℝ) = (l.map fun x : ℚ => (x : ℝ)).sum := by
  induction l with
  | nil => simp [lsum]
  | cons x l ih => simp [lsum, ih]

theorem sum_paperN (f : (Fin 3 → ℕ) → ℝ) :
    ∑ n ∈ paperN, f n = (triples.map fun t => f (toVec t)).sum := by
  unfold paperN
  rw [Finset.sum_image (fun s _ t _ h => toVec_injective h), List.sum_toFinset _ triples_nodup]

/-- **The sixteen class savings over the reals**: at the data above, `∑_{n ∈ paperN} savingOfTotals
n (C_n) B (A, A^arm, A^lead, A^rem) ≥ 0.264439290659`. -/
theorem paperSavings_ge :
    (264439290659 / 1000000000000 : ℝ) ≤ ∑ n ∈ paperN, savingOfTotals n (paperC n) (bLed : ℝ)
      paperAtot paperAarm paperAlead paperArem := by
  rw [sum_paperN]
  have h : (triples.map fun t => savingOfTotals (toVec t) (paperC (toVec t)) (bLed : ℝ) paperAtot
      paperAarm paperAlead paperArem) =
      ((triples.map fun t => savQ t.1 t.2.1 t.2.2).map fun x : ℚ => (x : ℝ)) := by
    rw [List.map_map]
    exact List.map_congr_left fun t _ => saving_toVec t
  rw [h, ← lsum_cast,
    show (264439290659 / 1000000000000 : ℝ) = ((264439290659 / 1000000000000 : ℚ) : ℝ) by
      push_cast; ring]
  exact Rat.cast_le.mpr savings_cert

theorem cQ_nonneg (n m₀ m₁ : ℕ) : 0 ≤ cQ n m₀ m₁ := by
  unfold cQ cGen
  split_ifs <;> (try split) <;> norm_num [c11, c20, c13, c22, c31, c40, c15, c24, c33, c42, c51,
    c60, cEEal, cEEcr, c04, c06]

/-- The class costs are nonnegative (`ClassInputs.C_nonneg`). -/
theorem paperC_nonneg (n : Fin 3 → ℕ) : 0 ≤ paperC n := by
  unfold paperC
  exact_mod_cast cQ_nonneg _ _ _

/-- The kind totals of the upper prices are nonnegative. -/
theorem paperTotals_nonneg (l : Fin 3) :
    0 ≤ paperAtot l ∧ 0 ≤ paperAarm l ∧ 0 ≤ paperAlead l ∧ 0 ≤ paperArem l := by
  fin_cases l <;>
    simp [paperAtot, paperAarm, paperAlead, paperArem, totQ, gF, gE, bF, bE, lF, lE, rF, rE] <;>
    norm_num

/-- The ledger's `B` is `bLed`. -/
theorem targetLedger_B_eq : targetLedger.B = (bLed : ℝ) := by
  norm_num [targetLedger, bLed]

/-- **The ledger's discount**: `D = 0.264439290659 + 0.010266762707`, the class savings and the
variance credit `D_var` (`def:closing-quantities`(9)). -/
theorem targetLedger_D_eq :
    targetLedger.D = 264439290659 / 1000000000000 + 10266762707 / 1000000000000 := by
  norm_num [targetLedger]

end Sarkozy.ClassBoundsPaper
