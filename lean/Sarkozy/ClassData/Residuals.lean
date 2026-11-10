module

public import Sarkozy.ClassData.Consistent

@[expose] public section





namespace Sarkozy.ClassData

open Sarkozy.ClassInputsPaper

/-! ### A bounded `all`, for the kernel -/

/-- `allBelow n f`: `f k` for every `k < n`. -/
def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, f => allBelow n f && f n

theorem allBelow_spec {n : ℕ} {f : ℕ → Bool} (h : allBelow n f = true) :
    ∀ k < n, f k = true := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true] at h
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih h.1 k hk
    · exact h.2

/-! ### The constants of `lem:joint-multiaffine` -/

/-- `R = 2.004317`, the bound of `β_B/α_B` (`eq:joint-resources`). -/
def ratioR : ℚ := 2004317 / 1000000
/-- `σ = 0.3842`. -/
def sigmaQ : ℚ := 3842 / 10000
/-- `H_* = 1.000003310`. -/
def hStar : ℚ := 1000003310 / 1000000000
/-- `η₀ = 211/80`. -/
def eta0 : ℚ := 211 / 80
/-- `ζ₀ = 9/4`. -/
def zeta0 : ℚ := 9 / 4
/-- `l = 1/R`. -/
def lQ : ℚ := 1 / ratioR
/-- `u = 1/2`. -/
def uQ : ℚ := 1 / 2
/-- `ρ = 1 + 1/R`. -/
def rhoQ : ℚ := 1 + 1 / ratioR

/-- The minimum of a rational function over `k ≤ n`. -/
def minUpTo (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => f 0
  | n + 1 => if minUpTo f n ≤ f (n + 1) then minUpTo f n else f (n + 1)

/-- `binom k 2` over `ℚ`. -/
def ch2 (k : ℕ) : ℚ := (k : ℚ) * ((k : ℚ) - 1) / 2

/-- `η_n = min_{0 ≤ k ≤ n} (P_{n,k} − 1)/E_{2,n,k}` (`lem:joint-multiaffine`). -/
def etaQ (n : ℕ) : ℚ :=
  minUpTo (fun k => ((1 + lQ) ^ k * (1 + uQ) ^ (n - k) - 1) /
    (ch2 k * lQ ^ 2 + (k : ℚ) * ((n - k : ℕ) : ℚ) * lQ * uQ + ch2 (n - k) * uQ ^ 2)) n

/-- `ζ_n = min_{0 ≤ k ≤ n} P_{n,k}/E_{1,n,k}` (`lem:joint-multiaffine`). -/
def zetaQ (n : ℕ) : ℚ :=
  minUpTo (fun k => (1 + lQ) ^ k * (1 + uQ) ^ (n - k) /
    ((k : ℚ) * lQ + ((n - k : ℕ) : ℚ) * uQ)) n

/-- **The uniform constants are valid in the finite degrees** (`lem:joint-multiaffine`):
`η_n ≥ 211/80` for `2 ≤ n ≤ 10`, `ζ_n ≥ 9/4` for `1 ≤ n ≤ 9`. -/
theorem eta_zeta_ge :
    allBelow 9 (fun n => decide (eta0 ≤ etaQ (n + 2))) = true ∧
      allBelow 9 (fun n => decide (zeta0 ≤ zetaQ (n + 1))) = true := by
  decide +kernel

theorem eta_ge {n : ℕ} (h2 : 2 ≤ n) (h10 : n ≤ 10) : eta0 ≤ etaQ n := by
  have := allBelow_spec eta_zeta_ge.1 (n - 2) (by omega)
  rw [show n - 2 + 2 = n by omega] at this
  exact of_decide_eq_true this

theorem zeta_ge {n : ℕ} (h1 : 1 ≤ n) (h9 : n ≤ 9) : zeta0 ≤ zetaQ n := by
  have := allBelow_spec eta_zeta_ge.2 (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega] at this
  exact of_decide_eq_true this


/-- The invariant caps `κ_b` of the sixteen classes (rounded down to `10⁻⁴⁰`). -/
def capQ : ℕ → ℚ
  | 0 => 6710974940633147997304303379264798072123 /
      10000000000000000000000000000000000000000
  | 1 => 1898315353232001808893998896508032813179 /
      2000000000000000000000000000000000000000
  | 2 => 5915482221621308817492106207421947628967 /
      5000000000000000000000000000000000000000
  | 3 => 912577760014843862143212513440569399763 /
      625000000000000000000000000000000000000
  | 4 => 3239621637969224980113558997901570005517 /
      5000000000000000000000000000000000000000
  | 5 => 9626160456938274636076539421699483756893 /
      10000000000000000000000000000000000000000
  | 6 => 3010205273801313655433407466339023450227 /
      2500000000000000000000000000000000000000
  | 7 => 7524593167291669623699149635679183605739 /
      5000000000000000000000000000000000000000
  | 8 => 4780549783734961952902135304300311368121 /
      2500000000000000000000000000000000000000
  | 9 => 12273771953822861259957956646890546937803 /
      5000000000000000000000000000000000000000
  | 10 => 2058994543441325891594104124042450150923 /
      2000000000000000000000000000000000000000
  | 11 => 484665277686756355059071957765598980299 /
      625000000000000000000000000000000000000
  | 12 => 6666789440067998093657286013091039034293 /
      10000000000000000000000000000000000000000
  | 13 => 4553418469063533218932199066523079153019 /
      10000000000000000000000000000000000000000
  | 14 => 2408795117340617968539598460539240552009 /
      5000000000000000000000000000000000000000
  | 15 => 4619462128850740626127723893954129223563 /
      10000000000000000000000000000000000000000
  | _ => 0

/-- The pure-fold caps `κ_n`, `n = 2, 4, 6` (common to every word; rounded down to `10⁻⁴⁰`). -/
def foldCapQ : ℕ → ℚ
  | 2 => 2058994543441325891594104124042450150923 /
      2000000000000000000000000000000000000000
  | 4 => 912577760014843862143212513440569399763 /
      625000000000000000000000000000000000000
  | 6 => 12273771953822861259957956646890546937803 /
      5000000000000000000000000000000000000000
  | _ => 0

/-- The aligned `E⁴` variance cap (rounded up to `10⁻⁴⁰`). -/
def avkQ : ℚ := 3333394699426654153837695299666233221011 /
  5000000000000000000000000000000000000000

/-! ### The diagonals, their weights and mean coefficients -/

/-- The variance credit subtracted from the cap of class `i` (`prop:joint-middle-mean`). -/
def varQ (i : ℕ) : ℚ :=
  if i = 10 ∨ i = 12 then capQ i / 4 else if i = 3 then capQ i / 32
  else if i = 14 then avkQ / 32 else 0

/-- The comparison weight `κ_b − variance` of class `i`. -/
def wQ (i : ℕ) : ℚ := capQ i - varQ i

/-- The mean coefficient of class `i` at outside degree `j` (`j = 11`: the tail). -/
def meanQ (i j : ℕ) : ℚ :=
  (if i = 10 then 4 / hStar ^ 2 else 0) +
  (if i = 12 ∨ i = 13 then (if j ≤ 8 then etaQ (j + 2) else eta0) else 0) +
  (if i = 11 then sigmaQ * (if j ≤ 8 then zetaQ (j + 1) else zeta0)
    else if i = 2 then sigmaQ ^ 3 * (if j ≤ 8 then zetaQ (j + 1) else zeta0)
    else if i = 8 then sigmaQ ^ 5 * (if j ≤ 8 then zetaQ (j + 1) else zeta0) else 0) +
  (if i = 10 then sigmaQ ^ 2 * (if j ≤ 10 then rhoQ ^ j else 1)
    else if i = 3 then sigmaQ ^ 4 * (if j ≤ 10 then rhoQ ^ j else 1)
    else if i = 9 then sigmaQ ^ 6 * (if j ≤ 10 then rhoQ ^ j else 1) else 0)

/-- **The 192 class residual gates** (`prop:joint-middle-mean`, `cert:four-routes-closing`):
`63 w − b > 23.66`, and `b ≥ 0`, on all sixteen classes and twelve outside degrees. -/
theorem class_gates_check : allBelow 16 (fun i => allBelow 12 (fun j =>
    decide (meanQ i j + 2366 / 100 < 63 * wQ i ∧ 0 ≤ meanQ i j))) = true := by
  decide +kernel

/-- **The 36 pure-fold word gates** (`prop:joint-middle-mean`):
`63(1 − ¼·[n ∈ {2,4}]) κ_n − (4/H_*²)[n = 2] − σⁿ ρ^j > 0`, `j ≤ 10`, and with `ρ^j` replaced by `1`
in the tail. -/
theorem even_word_gates : allBelow 3 (fun k => allBelow 12 (fun j =>
    decide (0 < 63 * (1 - (if k ≤ 1 then 1 / 4 else 0)) * foldCapQ (2 * k + 2) -
      (if k = 0 then 4 / hStar ^ 2 else 0) -
      sigmaQ ^ (2 * k + 2) * (if j ≤ 10 then rhoQ ^ j else 1)))) = true := by
  decide +kernel

/-- **The 27 mixed-word gates** (`prop:joint-middle-mean`): `63/4 − σⁿ ζ_{j+1} > 0`,
`n = 1, 3, 5`, `0 ≤ j ≤ 8`. -/
theorem odd_word_gates : allBelow 3 (fun k => allBelow 9 (fun j =>
    decide (0 < 63 / 4 - sigmaQ ^ (2 * k + 1) * zetaQ (j + 1)))) = true := by
  decide +kernel

/-- **The upper residual gates** (`prop:joint-upper-mean`, worst case `n = 0`):
`63 − ρ^j > 0` (`j ≤ 10`) and `63 − ζ_{j+1} > 0` (`j ≤ 8`). -/
theorem upper_gates : allBelow 11 (fun j => decide (0 < 63 - rhoQ ^ j)) = true ∧
    allBelow 9 (fun j => decide (0 < 63 - zetaQ (j + 1))) = true := by
  decide +kernel

/-- The paper's labelled diagonals of the joint allocation: class × outside degree. -/
abbrev PaperDiag : Type := Fin 16 × Fin 12

/-- The comparison weight of a diagonal. -/
def diagW (d : PaperDiag) : ℚ := wQ d.1

/-- The mean coefficient of a diagonal. -/
def diagB (d : PaperDiag) : ℚ := meanQ d.1 d.2

theorem diag_gate (d : PaperDiag) : diagB d + 2366 / 100 < 63 * diagW d ∧ 0 ≤ diagB d := by
  have h := allBelow_spec (allBelow_spec class_gates_check d.1 d.1.2) d.2 d.2.2
  exact of_decide_eq_true h

/-- **The residual gates on the diagonals**: `b_d + 23.66 < 63 w_d`. -/
theorem diag_resid (d : PaperDiag) : diagB d + 2366 / 100 < 63 * diagW d := (diag_gate d).1

theorem diagB_nonneg (d : PaperDiag) : 0 ≤ diagB d := (diag_gate d).2

/-! ### K2's field 45 along a labelling -/

section Resid

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **K2's field 45** (`MeanData.resid`, `cert:four-routes-closing`): if every diagonal of the
class data carries a paper label (`lab`), with mean coefficient at most the table's and comparison
weight at least the table's, then `b_j ≤ 63 w_j` (indeed with room `23.66`). -/
theorem resid_of_labels {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {cd : ClassInputsPaper.ClassData D.CL} {ED : ClassEnergyData D cd}
    (b : ∀ L, ED.Θ L → ℝ) (lab : ∀ L, ED.Θ L → PaperDiag)
    (hb : ∀ L j, b L j ≤ diagB (lab L j)) (hw : ∀ L j, (diagW (lab L j) : ℝ) ≤ ED.w L j) :
    ∀ L j, b L j ≤ 63 * ED.w L j := by
  intro L j
  have h1 : ((diagB (lab L j) + 2366 / 100 : ℚ) : ℝ) < ((63 * diagW (lab L j) : ℚ) : ℝ) := by
    exact_mod_cast diag_resid (lab L j)
  push_cast at h1
  linarith [hb L j, hw L j]

end Resid

end Sarkozy.ClassData
