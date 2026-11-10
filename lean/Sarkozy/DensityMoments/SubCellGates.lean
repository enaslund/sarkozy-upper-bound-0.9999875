module

public import Sarkozy.DensityMoments.PacketGates
public import Sarkozy.Target





@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DensityMoments

open Sarkozy.Certificates

/-- The prime-counting set `{p ≡ 3 (4) prime, a < p ≤ b}`. -/
def primes3 (a b : ℕ) : Finset ℕ := (Ico (a + 1) (b + 1)).filter (fun p => p.Prime ∧ p % 4 = 3)

/-- `θ(y) - θ(x)` is the sum of `log p` over the primes `p ≡ 3 (4)` in `(⌊x⌋, ⌊y⌋]`. -/
theorem theta4_sub {x y : ℝ} (hxy : x ≤ y) :
    Target.theta4 y 3 - Target.theta4 x 3 = ∑ p ∈ primes3 ⌊x⌋₊ ⌊y⌋₊, Real.log p := by
  unfold Target.theta4 primes3
  have hfl : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  rw [range_eq_Ico, range_eq_Ico, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (⌊x⌋₊ + 1)) (by omega : ⌊x⌋₊ + 1 ≤ ⌊y⌋₊ + 1)]
  ring

/-- **Upper bound of `θ(y) - θ(x)` by the number of primes.** -/
theorem theta4_sub_le {x y : ℝ} (hxy : x ≤ y) (hy : 1 ≤ y) :
    Target.theta4 y 3 - Target.theta4 x 3 ≤ ((primes3 ⌊x⌋₊ ⌊y⌋₊).card : ℝ) * Real.log y := by
  rw [theta4_sub hxy]
  have h : ∀ p ∈ primes3 ⌊x⌋₊ ⌊y⌋₊, Real.log p ≤ Real.log y := by
    intro p hp
    unfold primes3 at hp
    obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
    have hpy : p ≤ ⌊y⌋₊ := by have := (mem_Ico.mp hp1).2; omega
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp2.1.pos
    apply Real.log_le_log hp0
    calc (p : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hpy
      _ ≤ y := Nat.floor_le (by linarith)
  calc ∑ p ∈ primes3 ⌊x⌋₊ ⌊y⌋₊, Real.log p ≤ ∑ _p ∈ primes3 ⌊x⌋₊ ⌊y⌋₊, Real.log y :=
        sum_le_sum h
    _ = _ := by rw [sum_const, nsmul_eq_mul]

/-- **The span of consecutive primes `≡ 3 (mod 4)`** (from `ThetaSmall`): if
`h/2 - 2.072 (√x + √(x+h)) > (n - 1) log(x + h)`, with `1 ≤ x` and `x + h ≤ 10¹⁰`, then `(x, x + h]`
contains at least `n` primes `p ≡ 3 (mod 4)`. -/
theorem span_count (hθ : Target.ThetaSmall) {x h : ℝ} {n : ℕ} (hx : 1 ≤ x) (hh : 0 ≤ h)
    (hxh : x + h ≤ 10 ^ 10)
    (hspan : ((n : ℝ) - 1) * Real.log (x + h) <
      h / 2 - 2072 / 1000 * (Real.sqrt x + Real.sqrt (x + h))) :
    n ≤ (primes3 ⌊x⌋₊ ⌊x + h⌋₊).card := by
  have h1 := hθ x hx (by linarith)
  have h2 := hθ (x + h) (by linarith) hxh
  have hle := theta4_sub_le (by linarith : x ≤ x + h) (by linarith)
  have hlog : 0 < Real.log (x + h) ∨ Real.log (x + h) = 0 := by
    rcases (Real.log_nonneg (by linarith : (1 : ℝ) ≤ x + h)).lt_or_eq with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'.symm
  have hlow : h / 2 - 2072 / 1000 * (Real.sqrt x + Real.sqrt (x + h)) ≤
      Target.theta4 (x + h) 3 - Target.theta4 x 3 := by
    have a1 := (abs_le.mp h1).2
    have a2 := (abs_le.mp h2).1
    nlinarith
  have hcount : ((n : ℝ) - 1) * Real.log (x + h) <
      ((primes3 ⌊x⌋₊ ⌊x + h⌋₊).card : ℝ) * Real.log (x + h) := by linarith
  rcases hlog with hpos | hzero
  · have := lt_of_mul_lt_mul_right hcount hpos.le
    have h3 : (n : ℝ) < (primes3 ⌊x⌋₊ ⌊x + h⌋₊).card + 1 := by linarith
    have h4 : n < (primes3 ⌊x⌋₊ ⌊x + h⌋₊).card + 1 := by exact_mod_cast h3
    omega
  · rw [hzero] at hcount
    simp at hcount

/-- **A block of `n` consecutive primes `≡ 3 (mod 4)`**: `n` primes `≡ 3 (mod 4)` containing every
prime `≡ 3 (mod 4)` between its least and largest element. -/
structure ConsecBlock (B : Finset ℕ) (hB : B.Nonempty) : Prop where
  prime3 : ∀ p ∈ B, p.Prime ∧ p % 4 = 3
  consec : ∀ q : ℕ, q.Prime → q % 4 = 3 → B.min' hB ≤ q → q ≤ B.max' hB → q ∈ B

/-- **The largest prime of a block is at most its least prime plus `h`**, when
`(min B, min B + h]` contains at least `#B - 1` primes `≡ 3 (mod 4)`. -/
theorem block_max_le {B : Finset ℕ} {hB : B.Nonempty} (hc : ConsecBlock B hB) {h : ℕ}
    (hcount : B.card ≤ (primes3 (B.min' hB) (B.min' hB + h)).card + 1) :
    B.max' hB ≤ B.min' hB + h := by
  by_contra hcon
  push Not at hcon
  have hsub : insert (B.min' hB) (primes3 (B.min' hB) (B.min' hB + h)) ⊆ B := by
    intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · exact B.min'_mem hB
    · unfold primes3 at hq
      obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
      have := mem_Ico.mp hq1
      exact hc.consec q hq2.1 hq2.2 (by omega) (by omega)
  have hnot : B.min' hB ∉ primes3 (B.min' hB) (B.min' hB + h) := by
    intro hmem
    unfold primes3 at hmem
    have := (mem_Ico.mp (mem_filter.mp hmem).1).1
    omega
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem hnot] at hcard
  -- the largest element is not in the insert set either
  have hmax : B.max' hB ∉ insert (B.min' hB) (primes3 (B.min' hB) (B.min' hB + h)) := by
    rw [mem_insert]
    push Not
    constructor
    · omega
    · unfold primes3
      simp only [mem_filter, mem_Ico, not_and]
      intro h1
      omega
  have hsub' : insert (B.max' hB) (insert (B.min' hB) (primes3 (B.min' hB) (B.min' hB + h))) ⊆ B :=
    insert_subset (B.max'_mem hB) hsub
  have hcard' := card_le_card hsub'
  rw [card_insert_of_notMem hmax, card_insert_of_notMem hnot] at hcard'
  omega

/-- The H2″ constant. -/
def thetaSmallC : ℚ := 2072 / 1000

/-- One sub-cell of a middle piece: lower end `β = y_k`, upper end `y_{k+1}`, the block size
`n`, the span `h`, rational bounds `s₁ ≥ √y_{k+1}`, `s₂ ≥ √(y_{k+1} + h)`, `λ ≥ log(y_{k+1} + h)`
(witness `wλ`: `e^λ ≥ y_{k+1} + h`), `z = min(y_{k+1} + h, Y)` and `ℓ ≥ log z` (witness `wℓ`), and
the gate data of `GateRow` with `L = n ℓ`. -/
structure SubCellRow where
  piece : ℕ
  beta : ℕ
  yUp : ℕ
  pieceY : ℕ
  n : ℕ
  h : ℕ
  s1 : ℚ
  s2 : ℚ
  lam : ℚ
  wLam : ExpWitness
  ell : ℚ
  wEll : ExpWitness
  rb : ℚ
  w1 : ExpWitness
  w2 : ExpWitness
  deriving DecidableEq

namespace SubCellRow

variable (row : SubCellRow)

/-- The gate row `(β, L = n ℓ)`. -/
def gate : GateRow := ⟨row.piece, row.beta, row.rb, (row.n : ℚ) * row.ell, row.w1, row.w2⟩

/-- **The rational certificate of one sub-cell.** -/
def Check (P : PieceData) : Prop :=
  1 ≤ row.beta ∧ row.beta < row.yUp ∧ row.yUp ≤ row.pieceY ∧ row.yUp + row.h ≤ 10 ^ 10 ∧
    1 ≤ row.n ∧ 0 ≤ row.s1 ∧ (row.yUp : ℚ) ≤ row.s1 ^ 2 ∧ 0 ≤ row.s2 ∧
    ((row.yUp + row.h : ℕ) : ℚ) ≤ row.s2 ^ 2 ∧
    row.wLam.Valid row.lam ⟨row.wLam.lower ^ row.wLam.divisions, row.wLam.upper ^ row.wLam.divisions⟩ ∧
    ((row.yUp + row.h : ℕ) : ℚ) ≤ row.wLam.lower ^ row.wLam.divisions ∧
    row.wEll.Valid row.ell ⟨row.wEll.lower ^ row.wEll.divisions, row.wEll.upper ^ row.wEll.divisions⟩ ∧
    ((min (row.yUp + row.h) row.pieceY : ℕ) : ℚ) ≤ row.wEll.lower ^ row.wEll.divisions ∧
    0 ≤ row.lam ∧
    ((row.n : ℚ) - 1) * row.lam < (row.h : ℚ) / 2 - thetaSmallC * (row.s1 + row.s2) ∧
    row.gate.Check P

instance (P : PieceData) : Decidable (row.Check P) := by unfold Check; infer_instance

/-- From an exponential witness, `log z ≤ q` when `z ≤ lower^k`. -/
theorem log_le_of_witness {w : ExpWitness} {q : ℚ} {z : ℕ}
    (hw : w.Valid q ⟨w.lower ^ w.divisions, w.upper ^ w.divisions⟩)
    (hz : (z : ℚ) ≤ w.lower ^ w.divisions) (hz1 : 1 ≤ z) : Real.log z ≤ q := by
  have he := (ExpWitness.sound hw).1
  simp only at he
  have hz' : (z : ℝ) ≤ ((w.lower : ℝ) ^ w.divisions) := by exact_mod_cast hz
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hz1
  rw [Real.log_le_iff_le_exp hz0]
  push_cast at he
  linarith

/-- **Soundness of a sub-cell** under `ThetaSmall`: every block of `n` consecutive primes
`≡ 3 (mod 4)` whose least prime lies in `[y_k, y_{k+1})` and whose primes are below `Y` has
`log ∏ B ≤ L`, and the joint gate holds at every least prime `b ≥ y_k`. -/
theorem sound (hθ : Target.ThetaSmall) {P : PieceData} (hP : P.Valid) (h : row.Check P)
    {B : Finset ℕ} {hB : B.Nonempty} (hc : ConsecBlock B hB) (hcard : B.card = row.n)
    (hlo : row.beta ≤ B.min' hB) (hhi : B.min' hB < row.yUp) (hY : B.max' hB < row.pieceY) :
    Real.log (∏ p ∈ B, (p : ℝ)) ≤ (row.gate.L : ℝ) ∧
      ∀ b : ℝ, (row.beta : ℝ) ≤ b →
        Real.exp (-((row.gate.L : ℝ) * (1 - (kappaStar : ℝ)))) < kappaStar ∧
        P.sym (1 / Real.sqrt b) * (1 + mixtureBound row.gate.L) < 1 ∧
        P.skew (1 / Real.sqrt b) * (1 + mixtureBound row.gate.L) < 1 := by
  obtain ⟨hb1, hbu, hyY, hyh, hn1, hs10, hs1, hs20, hs2, hwL, hzL, hwE, hzE, hlam0, hspan, hgate⟩ := h
  -- the span at the least prime `p₀`
  set p0 := B.min' hB with hp0
  have hp01 : (1 : ℝ) ≤ p0 := by
    have : 1 ≤ p0 := le_trans hb1 hlo
    exact_mod_cast this
  have hp0u : (p0 : ℝ) ≤ row.yUp := by exact_mod_cast hhi.le
  have hsq1 : Real.sqrt p0 ≤ (row.s1 : ℝ) := by
    rw [Real.sqrt_le_left (by exact_mod_cast hs10)]
    have : ((row.yUp : ℚ) : ℝ) ≤ ((row.s1 ^ 2 : ℚ) : ℝ) := by exact_mod_cast hs1
    push_cast at this
    linarith
  have hsq2 : Real.sqrt ((p0 : ℝ) + row.h) ≤ (row.s2 : ℝ) := by
    rw [Real.sqrt_le_left (by exact_mod_cast hs20)]
    have : ((((row.yUp + row.h : ℕ) : ℚ)) : ℝ) ≤ ((row.s2 ^ 2 : ℚ) : ℝ) := by exact_mod_cast hs2
    push_cast at this
    linarith
  have hlogs : Real.log ((p0 : ℝ) + row.h) ≤ (row.lam : ℝ) := by
    have h1 := log_le_of_witness hwL hzL (by omega)
    have h2 : Real.log ((p0 : ℝ) + row.h) ≤ Real.log (((row.yUp + row.h : ℕ) : ℝ)) := by
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    linarith
  have hspan' : ((row.n : ℝ) - 1) * Real.log ((p0 : ℝ) + row.h) <
      (row.h : ℝ) / 2 - 2072 / 1000 * (Real.sqrt p0 + Real.sqrt ((p0 : ℝ) + row.h)) := by
    have hq : ((((row.n : ℚ) - 1) * row.lam : ℚ) : ℝ) <
        (((row.h : ℚ) / 2 - thetaSmallC * (row.s1 + row.s2) : ℚ) : ℝ) := by exact_mod_cast hspan
    push_cast at hq
    unfold thetaSmallC at hq
    push_cast at hq
    have hn0 : (0 : ℝ) ≤ (row.n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ row.n := by exact_mod_cast hn1
      linarith
    have := mul_le_mul_of_nonneg_left hlogs hn0
    nlinarith
  have hcount := span_count hθ (x := (p0 : ℝ)) (h := (row.h : ℝ)) (n := row.n) hp01
    (by positivity)
    (by
      have : ((p0 + row.h : ℕ) : ℝ) ≤ ((10 ^ 10 : ℕ) : ℝ) := by exact_mod_cast (by omega : p0 + row.h ≤ 10 ^ 10)
      push_cast at this
      linarith)
    hspan'
  have hfl1 : ⌊(p0 : ℝ)⌋₊ = p0 := Nat.floor_natCast p0
  have hfl2 : ⌊(p0 : ℝ) + (row.h : ℝ)⌋₊ = p0 + row.h := by
    rw [show (p0 : ℝ) + (row.h : ℝ) = ((p0 + row.h : ℕ) : ℝ) by push_cast; ring]
    exact Nat.floor_natCast _
  rw [hfl1, hfl2] at hcount
  have hmax := block_max_le hc (h := row.h) (by rw [← hp0]; omega)
  -- the product of the block
  have hlogprod : Real.log (∏ p ∈ B, (p : ℝ)) ≤ (row.n : ℝ) * Real.log (min (row.yUp + row.h) row.pieceY : ℕ) := by
    have hpos : ∀ p ∈ B, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hc.prime3 p hp).1.pos
    rw [Real.log_prod (fun p hp => (hpos p hp).ne')]
    have hzpos : (0 : ℝ) < ((min (row.yUp + row.h) row.pieceY : ℕ) : ℝ) := by
      have : 1 ≤ min (row.yUp + row.h) row.pieceY := by omega
      exact_mod_cast (by omega : 0 < min (row.yUp + row.h) row.pieceY)
    have hle : ∀ p ∈ B, Real.log p ≤ Real.log ((min (row.yUp + row.h) row.pieceY : ℕ) : ℝ) := by
      intro p hp
      apply Real.log_le_log (hpos p hp)
      have h1 : p ≤ B.max' hB := B.le_max' p hp
      have h2 : p ≤ min (row.yUp + row.h) row.pieceY := by omega
      exact_mod_cast h2
    calc ∑ p ∈ B, Real.log p ≤ ∑ _p ∈ B, Real.log ((min (row.yUp + row.h) row.pieceY : ℕ) : ℝ) :=
          sum_le_sum hle
      _ = _ := by rw [sum_const, nsmul_eq_mul, hcard]
  have hell : Real.log ((min (row.yUp + row.h) row.pieceY : ℕ) : ℝ) ≤ (row.ell : ℝ) :=
    log_le_of_witness hwE hzE (by omega)
  refine ⟨?_, ?_⟩
  · have : ((row.gate.L : ℚ) : ℝ) = (row.n : ℝ) * (row.ell : ℝ) := by
      unfold gate
      push_cast
      ring
    rw [this]
    have hn0 : (0 : ℝ) ≤ row.n := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hell hn0]
  · intro b hb
    -- the gate, as in `middle_joint_gates`
    have hc' := hgate
    have hr := GateRow.rsqrt_le hc'.1 hc'.2.2.1 hb
    have hβ : (1 : ℝ) ≤ row.beta := by exact_mod_cast hb1
    have hpos : 0 < 1 / Real.sqrt b := by
      have : 0 < b := by linarith
      positivity
    exact row.gate.sound hP hc' hpos hr

end SubCellRow

end Sarkozy.DensityMoments
