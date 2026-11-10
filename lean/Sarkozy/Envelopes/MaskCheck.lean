module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section






namespace Sarkozy.Envelopes

/-! ### Exact arithmetic on pairs of naturals -/

/-- A nonnegative rational `a/b` as a pair `(a, b)`. -/
abbrev QP := ℕ × ℕ

/-- Sum of pairs. -/
def QP.add (x y : QP) : QP := (x.1 * y.2 + y.1 * x.2, x.2 * y.2)

/-- Product of pairs. -/
def QP.mul (x y : QP) : QP := (x.1 * y.1, x.2 * y.2)

/-- The rational `a/b`. -/
def QP.toQ (x : QP) : ℚ := (x.1 : ℚ) / (x.2 : ℚ)

/-- The order test `a/b ≤ c/d`, i.e. `a d ≤ c b`. -/
def QP.le (x y : QP) : Bool := Nat.ble (x.1 * y.2) (y.1 * x.2)

theorem QP.toQ_add {x y : QP} (hx : 0 < x.2) (hy : 0 < y.2) :
    (QP.add x y).toQ = x.toQ + y.toQ := by
  unfold QP.add QP.toQ
  have h1 : (x.2 : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
  have h2 : (y.2 : ℚ) ≠ 0 := by exact_mod_cast hy.ne'
  push_cast
  field_simp

theorem QP.toQ_mul (x y : QP) : (QP.mul x y).toQ = x.toQ * y.toQ := by
  unfold QP.mul QP.toQ
  push_cast
  rw [div_mul_div_comm]

theorem QP.toQ_le {x y : QP} (hx : 0 < x.2) (hy : 0 < y.2) (h : QP.le x y = true) :
    x.toQ ≤ y.toQ := by
  unfold QP.le at h
  unfold QP.toQ
  have h' : x.1 * y.2 ≤ y.1 * x.2 := Nat.le_of_ble_eq_true h
  have h1 : (0 : ℚ) < x.2 := by exact_mod_cast hx
  have h2 : (0 : ℚ) < y.2 := by exact_mod_cast hy
  rw [div_le_div_iff₀ h1 h2]
  exact_mod_cast h'

/-! ### Words and weights -/

/-- The weights of a diagonal envelope: `((fold word, matching word), numerator, denominator)`,
words sorted. -/
abbrev EnvTable := List ((List ℕ × List ℕ) × ℕ × ℕ)

/-- Insertion into a sorted list of naturals. -/
def insOrd (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if Nat.ble a b then a :: b :: l else b :: insOrd a l

/-- Insertion sort of a list of naturals. -/
def sortNat : List ℕ → List ℕ
  | [] => []
  | a :: l => insOrd a (sortNat l)

/-- `n` copies of `0`. -/
def zeros : ℕ → List ℕ
  | 0 => []
  | n + 1 => 0 :: zeros n

/-- `n` copies of `1`. -/
def ones : ℕ → List ℕ
  | 0 => []
  | n + 1 => 1 :: ones n

/-- The label words `{1, 2, 3}^k` at the fold arm positions. -/
def armWords : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (armWords k).flatMap fun ls => [1 :: ls, 2 :: ls, 3 :: ls]

/-- The sorted fold word with the arm labels `ls` and the centre `0` at the other `n - k`
positions. -/
def foldWord (n k : ℕ) (ls : List ℕ) : List ℕ := sortNat (zeros (n - k) ++ ls)

/-- The sorted matching word with `a` arms (label `1`) among `m` positions. -/
def matchWord (m a : ℕ) : List ℕ := zeros (m - a) ++ ones a

/-- The weight of a word pair as a pair of naturals (`(0, 1)` if absent; `tablePos` excludes it). -/
def weightQP (T : EnvTable) (fw ew : List ℕ) : QP :=
  match T.find? (fun e => e.1 == (fw, ew)) with
  | some (_, a, b) => (a, b)
  | none => (0, 1)

/-- The weight `d_v` as a rational. -/
def weight (T : EnvTable) (fw ew : List ℕ) : ℚ := (weightQP T fw ew).toQ

/-- The squared fold arm magnitudes `1, t², (1 - t)²`, `t = 127/500`, as pairs. -/
def armMagSqQP (l : ℕ) : QP :=
  if l = 1 then (1, 1) else if l = 2 then (127 ^ 2, 500 ^ 2) else if l = 3 then (373 ^ 2, 500 ^ 2)
    else (0, 1)

/-- The fold arm magnitudes `1, t, 1 - t` at the arms `1, 2, 3`, `t = 127/500`. -/
def armMag (l : ℕ) : ℚ :=
  if l = 1 then 1 else if l = 2 then 127 / 500 else if l = 3 then 1 - 127 / 500 else 0

/-- The term `α(v)²/d_v` as a pair (the matching arms have magnitude `1`). -/
def termQP (T : EnvTable) (n m k a : ℕ) (ls : List ℕ) : QP :=
  QP.mul ((ls.map armMagSqQP).foldr QP.mul (1, 1))
    ((weightQP T (foldWord n k ls) (matchWord m a)).2,
      (weightQP T (foldWord n k ls) (matchWord m a)).1)

/-- The mask sum for `k` fold arms and `a` matching arms, as a pair. -/
def maskSumQP (T : EnvTable) (n m k a : ℕ) : QP :=
  ((armWords k).map (termQP T n m k a)).foldr QP.add (0, 1)

/-- **The mask sum** `∑_{A(v) = A} α(v)²/d_v` for a mask with `k` fold arms and `a` matching arms:
the sum over `{1, 2, 3}^k` of the squared arm magnitudes divided by the weight. -/
def maskSum (T : EnvTable) (n m k a : ℕ) : ℚ :=
  ((armWords k).map fun ls =>
    (ls.map fun l => armMag l ^ 2).prod / weight T (foldWord n k ls) (matchWord m a)).sum

/-- The Boolean positivity check: every entry has a positive numerator and denominator, and every
word pair used by the mask sums is in the table. -/
def tablePos (T : EnvTable) (n m : ℕ) : Bool :=
  T.all (fun e => decide (0 < e.2.1 ∧ 0 < e.2.2)) &&
    (List.range (n + 1)).all fun k => (List.range (m + 1)).all fun a =>
      (armWords k).all fun ls => (T.find? (fun e => e.1 == (foldWord n k ls, matchWord m a))).isSome

/-- The Boolean mask check: `maskSum k a · maskSum (n-k) (m-a) ≤ 1` for all `k ≤ n`, `a ≤ m`, on
pairs, with positive denominators. -/
def maskCheck (T : EnvTable) (n m : ℕ) : Bool :=
  (List.range (n + 1)).all fun k => (List.range (m + 1)).all fun a =>
    QP.le (QP.mul (maskSumQP T n m k a) (maskSumQP T n m (n - k) (m - a))) (1, 1) &&
      decide (0 < (maskSumQP T n m k a).2) && decide (0 < (maskSumQP T n m (n - k) (m - a)).2)

/-! ### Soundness -/

theorem armMagSqQP_toQ (l : ℕ) : (armMagSqQP l).toQ = armMag l ^ 2 := by
  unfold armMagSqQP armMag QP.toQ
  split_ifs <;> norm_num

theorem armMagSqQP_pos (l : ℕ) : 0 < (armMagSqQP l).2 := by
  unfold armMagSqQP
  split_ifs <;> norm_num

theorem prod_toQ (ls : List ℕ) :
    ((ls.map armMagSqQP).foldr QP.mul (1, 1)).toQ = (ls.map fun l => armMag l ^ 2).prod ∧
      0 < ((ls.map armMagSqQP).foldr QP.mul (1, 1)).2 := by
  induction ls with
  | nil => simp [QP.toQ]
  | cons l ls ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    refine ⟨?_, ?_⟩
    · rw [QP.toQ_mul, armMagSqQP_toQ, ih.1]
    · unfold QP.mul
      exact Nat.mul_pos (armMagSqQP_pos l) ih.2

theorem sum_toQ (xs : List QP) (hxs : ∀ x ∈ xs, 0 < x.2) :
    (xs.foldr QP.add (0, 1)).toQ = (xs.map QP.toQ).sum ∧ 0 < (xs.foldr QP.add (0, 1)).2 := by
  induction xs with
  | nil => simp [QP.toQ]
  | cons x xs ih =>
    have hx := hxs x (List.mem_cons_self ..)
    have ih' := ih fun y hy => hxs y (List.mem_cons_of_mem _ hy)
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    refine ⟨?_, ?_⟩
    · rw [QP.toQ_add hx ih'.2, ih'.1]
    · unfold QP.add
      exact Nat.mul_pos hx ih'.2

theorem termQP_toQ (T : EnvTable) (n m k a : ℕ) (ls : List ℕ)
    (hw : 0 < (weightQP T (foldWord n k ls) (matchWord m a)).1) :
    (termQP T n m k a ls).toQ =
        (ls.map fun l => armMag l ^ 2).prod / weight T (foldWord n k ls) (matchWord m a) ∧
      0 < (termQP T n m k a ls).2 := by
  unfold termQP
  obtain ⟨hp, hp2⟩ := prod_toQ ls
  refine ⟨?_, Nat.mul_pos hp2 hw⟩
  rw [QP.toQ_mul, hp, weight]
  unfold QP.toQ
  simp only
  rw [div_div_eq_mul_div, mul_div_assoc, div_eq_mul_inv]

theorem weight_pos_of_mem {T : EnvTable} {n m : ℕ} (hT : tablePos T n m = true) {k a : ℕ}
    (hk : k ≤ n) (ha : a ≤ m) {ls : List ℕ} (hls : ls ∈ armWords k) :
    0 < (weightQP T (foldWord n k ls) (matchWord m a)).1 := by
  unfold tablePos at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨hall, hsome⟩ := hT
  have h1 : (T.find? (fun e => e.1 == (foldWord n k ls, matchWord m a))).isSome = true := by
    have h2 := List.all_eq_true.1 hsome k (List.mem_range.2 (by omega))
    have h3 := List.all_eq_true.1 h2 a (List.mem_range.2 (by omega))
    exact List.all_eq_true.1 h3 ls hls
  unfold weightQP
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 h1
  rw [he]
  have hmem := List.mem_of_find?_eq_some he
  have := List.all_eq_true.1 hall e hmem
  simp only [decide_eq_true_eq] at this
  exact this.1

theorem maskSumQP_toQ {T : EnvTable} {n m : ℕ} (hT : tablePos T n m = true) {k a : ℕ}
    (hk : k ≤ n) (ha : a ≤ m) : (maskSumQP T n m k a).toQ = maskSum T n m k a := by
  unfold maskSumQP maskSum
  have hpos : ∀ x ∈ (armWords k).map (termQP T n m k a), 0 < x.2 := by
    intro x hx
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.1 hx
    exact (termQP_toQ T n m k a ls (weight_pos_of_mem hT hk ha hls)).2
  rw [(sum_toQ _ hpos).1, List.map_map]
  congr 1
  refine List.map_congr_left fun ls hls => ?_
  exact (termQP_toQ T n m k a ls (weight_pos_of_mem hT hk ha hls)).1

/-- **Soundness of the kernel check.** If `tablePos` and `maskCheck` hold, then for every mask
count `(k, a)` with `k ≤ n`, `a ≤ m`, the mask condition `eq:oct24:mask-schur`
`maskSum k a · maskSum (n - k) (m - a) ≤ 1` holds in `ℚ`. -/
theorem mask_sound {T : EnvTable} {n m : ℕ} (hT : tablePos T n m = true)
    (hC : maskCheck T n m = true) {k a : ℕ} (hk : k ≤ n) (ha : a ≤ m) :
    maskSum T n m k a * maskSum T n m (n - k) (m - a) ≤ 1 := by
  unfold maskCheck at hC
  have h1 := List.all_eq_true.1 hC k (List.mem_range.2 (by omega))
  have h := List.all_eq_true.1 h1 a (List.mem_range.2 (by omega))
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hle, hp1⟩, hp2⟩ := h
  have hmul := QP.toQ_le (Nat.mul_pos hp1 hp2) (by norm_num) hle
  rw [QP.toQ_mul, maskSumQP_toQ hT hk ha, maskSumQP_toQ hT (by omega) (by omega)] at hmul
  simpa [QP.toQ] using hmul

end Sarkozy.Envelopes
