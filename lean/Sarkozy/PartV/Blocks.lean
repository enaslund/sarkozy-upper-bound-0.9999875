module

public import Sarkozy.PartV.Parameters
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# The block partitions of the middle range (`def:record:exact-blocks`(b)–(d))

`paper/sections/20_middle_reference.tex`, `def:record:exact-blocks`.

* (b) **Threshold points.** `thresholdPoint j` is the least even integer `c` with `c⁴ ≥ 2^j`,
  i.e. the least even integer `≥ 2^{j/4}` (`97 ≤ j ≤ 128`); `Q₃ = c₉₇` is checked exactly
  (`thresholdPoint_97`).
* (c) **Exact blocks below `X_Ch`.** The greedy rule — a prime joins the current block if the
  sum of the integer upper logarithms `𝔲` over the block stays at most `𝔲_*`, otherwise it starts
  a new block — is `greedyBlocks u U ps`. Proved: the blocks partition the list
  (`greedyBlocks_flatten`), and every block has `∑ 𝔲 ≤ 𝔲_*` when every single `𝔲(p) ≤ 𝔲_*`
  (`greedyBlocks_budget`); with `log p < 𝔲(p)/2⁴⁰` this gives `∑_{p ∈ 𝔅} log p ≤ 𝔲_*/2⁴⁰ = L`
  (`greedy_log_budget`). The function `𝔲` (from the 5668 authenticated count bins) is a
  parameter.
* (d) **Fixed-cardinality cells above `X_Ch`.** The cell points `x_j = x^{1-j/𝗇} Y^{j/𝗇}`, the
  cardinalities `n_j = ⌊L / log x_{j+1}⌋`, the number of cells `𝗇 = ⌈128 log₂(Y/x)⌉`, and the
  blocks of `n_j` consecutive primes of a cell (`cellBlock`). Proved: every such block has
  `∑ log p ≤ n_j log x_{j+1} ≤ L` (`cellBlock_log_budget`).
-/

namespace Sarkozy.PartV

open Finset

/-! ## (b) Threshold points -/

/-- `c` is an even integer with `c⁴ ≥ 2^j`. -/
def IsEvenAbove (j c : ℕ) : Prop := Even c ∧ 2 ^ j ≤ c ^ 4

instance (j c : ℕ) : Decidable (IsEvenAbove j c) := by unfold IsEvenAbove; infer_instance

theorem exists_evenAbove (j : ℕ) : ∃ c, IsEvenAbove j c :=
  ⟨2 * 2 ^ j, ⟨⟨2 ^ j, by ring⟩,
    (Nat.le_self_pow (by norm_num) (2 ^ j)).trans (Nat.pow_le_pow_left (by omega) 4)⟩⟩

/-- **The threshold point** `c_j`, the least even integer `≥ 2^{j/4}`
(`def:record:exact-blocks`(b)). -/
noncomputable def thresholdPoint (j : ℕ) : ℕ := Nat.find (exists_evenAbove j)

/-- `Q₃ = c₉₇`: `19 951 586` is the least even integer whose fourth power is at least `2⁹⁷`. -/
theorem thresholdPoint_97 : thresholdPoint 97 = Q3 := by
  unfold thresholdPoint Q3
  rw [Nat.find_eq_iff]
  refine ⟨⟨⟨9975793, by norm_num⟩, by norm_num⟩, fun n hn h => ?_⟩
  obtain ⟨⟨m, hm⟩, h4⟩ := h
  have hle : n ≤ 19951584 := by
    rcases Nat.even_or_odd n with he | ho
    · omega
    · exact absurd ⟨m, hm⟩ (Nat.not_even_iff_odd.mpr ho)
  have : n ^ 4 ≤ 19951584 ^ 4 := Nat.pow_le_pow_left hle 4
  have hlt : (19951584 : ℕ) ^ 4 < 2 ^ 97 := by norm_num
  omega

/-! ## (c) Greedy exact blocks -/

/-- The greedy pass with a current block `cur` (reversed) of weight `s`. -/
def greedyAux (u : ℕ → ℕ) (U : ℕ) : List ℕ → List ℕ → ℕ → List (List ℕ)
  | [], cur, _ => [cur.reverse]
  | p :: ps, cur, s =>
      if s + u p ≤ U then greedyAux u U ps (p :: cur) (s + u p)
      else cur.reverse :: greedyAux u U ps [p] (u p)

/-- **The greedy exact blocks** (`def:record:exact-blocks`(c)) of a list of primes, in order: a
prime joins the current block if the sum of `u` over the block stays at most `U`, otherwise it
starts a new block. (The first block may be empty when the list is empty.) -/
def greedyBlocks (u : ℕ → ℕ) (U : ℕ) (ps : List ℕ) : List (List ℕ) := greedyAux u U ps [] 0

theorem greedyAux_flatten (u : ℕ → ℕ) (U : ℕ) :
    ∀ (ps cur : List ℕ) (s : ℕ), (greedyAux u U ps cur s).flatten = cur.reverse ++ ps
  | [], cur, s => by simp [greedyAux]
  | p :: ps, cur, s => by
      unfold greedyAux
      split_ifs
      · rw [greedyAux_flatten u U ps (p :: cur) (s + u p)]
        simp
      · rw [List.flatten_cons, greedyAux_flatten u U ps [p] (u p)]
        simp

/-- **The greedy blocks partition the list** (in order). -/
theorem greedyBlocks_flatten (u : ℕ → ℕ) (U : ℕ) (ps : List ℕ) :
    (greedyBlocks u U ps).flatten = ps := by
  unfold greedyBlocks
  rw [greedyAux_flatten]
  simp

theorem greedyAux_budget (u : ℕ → ℕ) (U : ℕ) (hu : ∀ p, u p ≤ U) :
    ∀ (ps cur : List ℕ) (s : ℕ), (cur.map u).sum = s → s ≤ U →
      ∀ b ∈ greedyAux u U ps cur s, (b.map u).sum ≤ U
  | [], cur, s, hs, hsU => by
      intro b hb
      simp only [greedyAux, List.mem_singleton] at hb
      subst hb
      rw [List.map_reverse, List.sum_reverse, hs]
      exact hsU
  | p :: ps, cur, s, hs, hsU => by
      intro b hb
      unfold greedyAux at hb
      split_ifs at hb with h
      · exact greedyAux_budget u U hu ps (p :: cur) (s + u p)
          (by simp [hs, add_comm]) h b hb
      · rcases List.mem_cons.mp hb with rfl | hb
        · rw [List.map_reverse, List.sum_reverse, hs]
          exact hsU
        · exact greedyAux_budget u U hu ps [p] (u p) (by simp) (hu p) b hb

/-- **Every greedy block stays within the budget**: `∑_{p ∈ 𝔅} 𝔲(p) ≤ 𝔲_*` when every single
`𝔲(p) ≤ 𝔲_*`. -/
theorem greedyBlocks_budget (u : ℕ → ℕ) (U : ℕ) (hu : ∀ p, u p ≤ U) (ps : List ℕ) :
    ∀ b ∈ greedyBlocks u U ps, (b.map u).sum ≤ U :=
  greedyAux_budget u U hu ps [] 0 (by simp) (Nat.zero_le _)

theorem list_sum_div (u : ℕ → ℕ) (b : List ℕ) :
    (b.map fun p : ℕ => (u p : ℝ) / 2 ^ 40).sum = ((b.map u).sum : ℝ) / 2 ^ 40 := by
  induction b with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.cast_add, add_div]

/-- **The log budget of the exact blocks** (`def:record:exact-blocks`(c)): if
`log p < 𝔲(p)/2⁴⁰` for the primes of the list and `𝔲(p) ≤ 𝔲_*` for all `p`, every greedy block
has `∑_{p ∈ 𝔅} log p ≤ 𝔲_*/2⁴⁰ = L = 570`. -/
theorem greedy_log_budget (u : ℕ → ℕ) (hu : ∀ p, u p ≤ integerBudget) (ps : List ℕ)
    (hlog : ∀ p ∈ ps, Real.log p < (u p : ℝ) / 2 ^ 40) :
    ∀ b ∈ greedyBlocks u integerBudget ps,
      (b.map fun p : ℕ => Real.log (p : ℝ)).sum ≤ middleBudget := by
  intro b hb
  have hsub : ∀ p ∈ b, p ∈ ps := by
    intro p hp
    rw [← greedyBlocks_flatten u integerBudget ps]
    exact List.mem_flatten.mpr ⟨b, hb, hp⟩
  have hsum := greedyBlocks_budget u integerBudget hu ps b hb
  have h1 : (b.map fun p : ℕ => Real.log (p : ℝ)).sum ≤
      (b.map fun p : ℕ => (u p : ℝ) / 2 ^ 40).sum :=
    List.sum_le_sum fun p hp => (hlog p (hsub p hp)).le
  have h2 : (b.map fun p : ℕ => (u p : ℝ) / 2 ^ 40).sum = ((b.map u).sum : ℝ) / 2 ^ 40 :=
    list_sum_div u b
  have h3 : ((b.map u).sum : ℝ) ≤ (integerBudget : ℝ) := by exact_mod_cast hsum
  have h4 : (integerBudget : ℝ) / 2 ^ 40 = middleBudget := by
    unfold integerBudget middleBudget
    push_cast
    ring
  calc (b.map fun p : ℕ => Real.log (p : ℝ)).sum ≤ ((b.map u).sum : ℝ) / 2 ^ 40 :=
        h1.trans h2.le
    _ ≤ (integerBudget : ℝ) / 2 ^ 40 := div_le_div_of_nonneg_right h3 (by positivity)
    _ = middleBudget := h4

/-! ## (d) Fixed-cardinality cells -/

/-- The cell points `x_j = x^{1-j/𝗇} Y^{j/𝗇}` of a piece `[x, Y)` with `𝗇` cells. -/
noncomputable def cellPoint (x Y : ℝ) (n j : ℕ) : ℝ := x ^ (1 - (j : ℝ) / n) * Y ^ ((j : ℝ) / n)

/-- The number of cells `𝗇 = ⌈128 log₂(Y/x)⌉`. -/
noncomputable def cellCount (x Y : ℝ) : ℕ := ⌈128 * Real.logb 2 (Y / x)⌉₊

/-- The cardinality `n_j = ⌊L / log x_{j+1}⌋` of the blocks of the cell `[x_j, x_{j+1})`. -/
noncomputable def cellCard (L x Y : ℝ) (n j : ℕ) : ℕ := ⌊L / Real.log (cellPoint x Y n (j + 1))⌋₊

/-- **The `m`-th block of a cell**: the primes `m k, …, m k + k - 1` (in increasing order) of the
list of the cell's primes `≡ 3 (mod 4)`, `k = n_j`; the last block may have fewer. -/
def cellBlock (ps : List ℕ) (k m : ℕ) : List ℕ := (ps.drop (m * k)).take k

theorem cellBlock_length_le (ps : List ℕ) (k m : ℕ) : (cellBlock ps k m).length ≤ k :=
  List.length_take_le _ _

/-- **Every block of a cell has logarithmic length at most `L`**
(`def:record:exact-blocks`(d)): `∑ log p ≤ n_j log x_{j+1} ≤ L`, for primes `p < x_{j+1}`,
`x_{j+1} > 1` and `k = ⌊L / log x_{j+1}⌋`. -/
theorem cellBlock_log_budget {L xnext : ℝ} (hx : 1 < xnext) (ps : List ℕ)
    (hps : ∀ p ∈ ps, 0 < p ∧ (p : ℝ) < xnext) (m : ℕ) :
    ((cellBlock ps ⌊L / Real.log xnext⌋₊ m).map fun p : ℕ => Real.log (p : ℝ)).sum ≤ L ∨
      L < 0 := by
  rcases lt_or_ge L 0 with hL | hL
  · exact Or.inr hL
  · left
    set k := ⌊L / Real.log xnext⌋₊
    have hlogx : 0 < Real.log xnext := Real.log_pos hx
    have hmem : ∀ p ∈ cellBlock ps k m, p ∈ ps := fun p hp =>
      List.mem_of_mem_drop (List.mem_of_mem_take hp)
    have h1 : ((cellBlock ps k m).map fun p : ℕ => Real.log (p : ℝ)).sum ≤
        ((cellBlock ps k m).map fun _ => Real.log xnext).sum := by
      refine List.sum_le_sum fun p hp => ?_
      obtain ⟨hp0, hpx⟩ := hps p (hmem p hp)
      exact Real.log_le_log (by exact_mod_cast hp0) hpx.le
    have h2 : ((cellBlock ps k m).map fun _ => Real.log xnext).sum =
        (cellBlock ps k m).length * Real.log xnext := by
      rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
    have h3 : ((cellBlock ps k m).length : ℝ) ≤ k := by exact_mod_cast cellBlock_length_le ps k m
    have h4 : (k : ℝ) * Real.log xnext ≤ L := by
      have := Nat.floor_le (div_nonneg hL hlogx.le)
      calc (k : ℝ) * Real.log xnext ≤ L / Real.log xnext * Real.log xnext :=
            mul_le_mul_of_nonneg_right this hlogx.le
        _ = L := div_mul_cancel₀ L hlogx.ne'
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ (k : ℝ) * Real.log xnext := mul_le_mul_of_nonneg_right h3 hlogx.le
      _ ≤ L := h4

end Sarkozy.PartV
