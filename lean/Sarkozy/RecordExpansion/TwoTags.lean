module

public import Sarkozy.RecordExpansion.TagSeries

/-!
# Two tags: the bound of `cor:two-cut-series`

For two tags with equal totals `d_0 = d_1 = d` and `v_0 = v_1 = v` (Part V's case,
`cor:two-cut-series` of the paper, Section 10), the series of (CP2) is bounded by
the explicit quantity

  `𝔗^+_n(d, v) = ∑_{i=1}^n [ (2d^i/i!) ∑_{l=0}^{i-1} v^l/l! + (dv)^i/(i!)² ]
      + 2 e^v d^{n+1} / ((n+1)! (1 - d/(n+2))) + (dv)^{n+1} / (((n+1)!)² (1 - dv/(n+2)²))`

whenever `d < n + 2` and `dv < (n + 2)²` (`tagSeries_two_le`). The sum
`∑_{i=1}^n` is written `∑_{i < n} twoGroup d v (i + 1)`.

Each count vector `(k_0, k_1) ≠ 0` is charged at a tag with the larger count,
which bounds its term by `d^{max(k_0,k_1)} v^{min(k_0,k_1)} / (k_0! k_1!)`
(`tagMin_two_le`). The terms are grouped by `i = max(k_0, k_1)`, and the tails are
bounded by geometric series with ratios `d/(n+2)` and `dv/(n+2)²`, as in the
paper. `tagSeries_two_le_upper` combines this with the monotonicity of `𝔗`
(`tagSeries_mono`): tag totals `d_j ≤ d̂`, `v_j ≤ v̂` give `𝔗(d, v) ≤ 𝔗^+_n(d̂, v̂)`.

The paper assumes `d ≤ v` to write the series exactly as
`∑ d^{max} v^{min}/(k_0! k_1!)`; the upper bound proved here needs only
`d, v ≥ 0` and the two gates. The exact identity, and the monotonicity of
`𝔗^+_n` claimed in the corollary, are not formalized.
-/

@[expose] public section

open Finset
open scoped BigOperators Nat

namespace Sarkozy.RecordExpansion

/-- The term `d^{max(a,b)} v^{min(a,b)} / (a! b!)` of the two-tag series, `0` at `(0, 0)`. -/
noncomputable def twoTerm (d v : ℝ) (a b : ℕ) : ℝ :=
  if a = 0 ∧ b = 0 then 0 else d ^ max a b * v ^ min a b / ((a ! : ℝ) * b !)

/-- The terms with `max(k_0, k_1) = i ≥ 1`:
`(2d^i/i!) ∑_{l < i} v^l/l! + (dv)^i/(i!)²`. -/
noncomputable def twoGroup (d v : ℝ) (i : ℕ) : ℝ :=
  2 * d ^ i / (i ! : ℝ) * ∑ l ∈ range i, v ^ l / (l ! : ℝ) + (d * v) ^ i / ((i ! : ℝ) ^ 2)

/-- The bound `𝔗^+_n(d, v)` of `cor:two-cut-series`. -/
noncomputable def twoTagUpper (n : ℕ) (d v : ℝ) : ℝ :=
  ∑ i ∈ range n, twoGroup d v (i + 1) +
    2 * Real.exp v * d ^ (n + 1) / (((n + 1)! : ℝ) * (1 - d / (n + 2))) +
    (d * v) ^ (n + 1) / ((((n + 1)! : ℝ)) ^ 2 * (1 - d * v / ((n : ℝ) + 2) ^ 2))

theorem tagTerm_two (d v : ℝ) (k : Bool → ℕ) (j : Bool) :
    tagTerm (fun _ => d) (fun _ => v) k j =
      (if j then d ^ k true * v ^ k false else v ^ k true * d ^ k false) /
        (((k true)! : ℝ) * ((k false)! : ℝ)) := by
  unfold tagTerm
  rw [Fintype.prod_bool, Fintype.prod_bool]
  cases j <;> simp

/-- Charging at the tag with the larger count: `tagMin ≤ d^{max} v^{min}/(k_0! k_1!)`. -/
theorem tagMin_two_le (d v : ℝ) (k : Bool → ℕ) :
    tagMin (fun _ => d) (fun _ => v) k ≤ twoTerm d v (k true) (k false) := by
  by_cases hk : k = 0
  · subst hk
    rw [tagMin_zero]
    simp [twoTerm]
  · have hne : ¬(k true = 0 ∧ k false = 0) := by
      rintro ⟨h1, h2⟩
      apply hk
      funext x
      cases x
      · exact h2
      · exact h1
    unfold twoTerm
    rw [ite_eq_right hne]
    by_cases hab : k false ≤ k true
    · have h1 : 1 ≤ k true := by omega
      refine (tagMin_le_tagTerm _ _ h1).trans (le_of_eq ?_)
      rw [tagTerm_two, max_eq_left hab, min_eq_right hab]
      simp
    · push Not at hab
      have h1 : 1 ≤ k false := by omega
      refine (tagMin_le_tagTerm _ _ h1).trans (le_of_eq ?_)
      rw [tagTerm_two, max_eq_right hab.le, min_eq_left hab.le]
      simp only [Bool.false_eq_true, ↓reduceIte]
      ring

/-- The terms with `max = i` sum to `twoGroup`; the zero vector contributes nothing. -/
theorem sum_twoTerm_square (d v : ℝ) (M : ℕ) :
    ∑ a ∈ range M, ∑ b ∈ range M, twoTerm d v a b =
      ∑ i ∈ range M, if i = 0 then 0 else twoGroup d v i := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hsplit : ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), twoTerm d v a b =
        ∑ a ∈ range M, ∑ b ∈ range M, twoTerm d v a b +
          (∑ a ∈ range M, twoTerm d v a M + ∑ b ∈ range M, twoTerm d v M b +
            twoTerm d v M M) := by
      rw [sum_range_succ]
      simp_rw [sum_range_succ (fun b => twoTerm d v _ b)]
      rw [sum_add_distrib]
      ring
    rw [hsplit, ih, sum_range_succ]
    congr 1
    by_cases hM : M = 0
    · subst hM
      simp [twoTerm]
    · rw [ite_eq_right hM]
      have hcol : ∀ a ∈ range M, twoTerm d v a M = d ^ M * v ^ a / ((a ! : ℝ) * M !) := by
        intro a ha
        have ha' : a < M := mem_range.mp ha
        unfold twoTerm
        rw [ite_eq_right (by omega), max_eq_right ha'.le, min_eq_left ha'.le]
      have hrow : ∀ b ∈ range M, twoTerm d v M b = d ^ M * v ^ b / ((M ! : ℝ) * b !) := by
        intro b hb
        have hb' : b < M := mem_range.mp hb
        unfold twoTerm
        rw [ite_eq_right (by omega), max_eq_left hb'.le, min_eq_right hb'.le]
      have hdiag : twoTerm d v M M = (d * v) ^ M / ((M ! : ℝ) ^ 2) := by
        unfold twoTerm
        rw [ite_eq_right (by omega), max_self, min_self, mul_pow, sq]
      rw [sum_congr rfl hcol, sum_congr rfl hrow, hdiag]
      unfold twoGroup
      rw [mul_sum]
      have h2 : ∀ l ∈ range M, 2 * d ^ M / (M ! : ℝ) * (v ^ l / (l ! : ℝ)) =
          d ^ M * v ^ l / ((l ! : ℝ) * M !) + d ^ M * v ^ l / ((M ! : ℝ) * l !) := by
        intro l _
        have hl : (l ! : ℝ) ≠ 0 := by positivity
        have hm : (M ! : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      rw [sum_congr rfl h2, sum_add_distrib]

/-- A geometric tail: if `t_{j+1} ≤ q t_j` with `0 ≤ q < 1` and `t ≥ 0`, then
`∑_{j < N} t_j ≤ t_0 / (1 - q)`. -/
theorem sum_le_geometric {t : ℕ → ℝ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ht : ∀ j, 0 ≤ t j) (hstep : ∀ j, t (j + 1) ≤ q * t j) (N : ℕ) :
    ∑ j ∈ range N, t j ≤ t 0 / (1 - q) := by
  have hpow : ∀ j, t j ≤ t 0 * q ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc t (j + 1) ≤ q * t j := hstep j
        _ ≤ q * (t 0 * q ^ j) := mul_le_mul_of_nonneg_left ih hq0
        _ = t 0 * q ^ (j + 1) := by ring
  have hgeom : ∑ j ∈ range N, q ^ j ≤ 1 / (1 - q) := by
    have hqN : 0 ≤ q ^ N := pow_nonneg hq0 N
    have h1q : 0 < 1 - q := by linarith
    rw [le_div_iff₀ h1q, geom_sum_mul_neg]
    linarith
  calc ∑ j ∈ range N, t j ≤ ∑ j ∈ range N, t 0 * q ^ j := sum_le_sum fun j _ => hpow j
    _ = t 0 * ∑ j ∈ range N, q ^ j := by rw [mul_sum]
    _ ≤ t 0 * (1 / (1 - q)) := mul_le_mul_of_nonneg_left hgeom (ht 0)
    _ = t 0 / (1 - q) := by ring

theorem pow_div_factorial_succ (x : ℝ) (m : ℕ) :
    x ^ (m + 1) / ((m + 1)! : ℝ) = x ^ m / (m ! : ℝ) * (x / ((m : ℝ) + 1)) := by
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have h1 : (m ! : ℝ) ≠ 0 := by positivity
  have h2 : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem pow_div_factorial_sq_succ (x : ℝ) (m : ℕ) :
    x ^ (m + 1) / ((m + 1)! : ℝ) ^ 2 = x ^ m / (m ! : ℝ) ^ 2 * (x / ((m : ℝ) + 1) ^ 2) := by
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have h1 : (m ! : ℝ) ≠ 0 := by positivity
  have h2 : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- The grouped sum up to any `M` is at most `𝔗^+_n(d, v)`. -/
theorem sum_groups_le {d v : ℝ} (hd : 0 ≤ d) (hv : 0 ≤ v) (n : ℕ) (h1 : d < n + 2)
    (h2 : d * v < ((n : ℝ) + 2) ^ 2) (M : ℕ) :
    ∑ i ∈ range M, (if i = 0 then 0 else twoGroup d v i) ≤ twoTagUpper n d v := by
  set G : ℕ → ℝ := fun i => if i = 0 then 0 else twoGroup d v i with hG
  have hG0 : ∀ i, 0 ≤ G i := by
    intro i
    simp only [hG]
    split_ifs
    · exact le_rfl
    · unfold twoGroup
      have : 0 ≤ ∑ l ∈ range i, v ^ l / (l ! : ℝ) :=
        sum_nonneg fun l _ => div_nonneg (pow_nonneg hv _) (by positivity)
      positivity
  set M' := max M (n + 1)
  have hM : ∑ i ∈ range M, G i ≤ ∑ i ∈ range M', G i :=
    sum_le_sum_of_subset_of_nonneg (range_mono (le_max_left _ _)) (fun i _ _ => hG0 i)
  rw [← sum_range_add_sum_Ico G (le_max_right M (n + 1))] at hM
  have hhead : ∑ i ∈ range (n + 1), G i = ∑ i ∈ range n, twoGroup d v (i + 1) := by
    rw [sum_range_succ']
    simp [hG]
  rw [hhead, sum_Ico_eq_sum_range] at hM
  -- the tail
  set q1 := d / ((n : ℝ) + 2)
  set q2 := d * v / ((n : ℝ) + 2) ^ 2
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hq1 : 0 ≤ q1 := div_nonneg hd hn2.le
  have hq1' : q1 < 1 := by rw [div_lt_one hn2]; exact h1
  have hq2 : 0 ≤ q2 := div_nonneg (mul_nonneg hd hv) (by positivity)
  have hq2' : q2 < 1 := by rw [div_lt_one (by positivity)]; exact h2
  set t1 : ℕ → ℝ := fun j => d ^ (n + 1 + j) / (((n + 1 + j)! : ℝ)) with ht1
  set t2 : ℕ → ℝ := fun j => (d * v) ^ (n + 1 + j) / (((n + 1 + j)! : ℝ) ^ 2) with ht2
  have ht1nn : ∀ j, 0 ≤ t1 j := fun j => div_nonneg (pow_nonneg hd _) (by positivity)
  have ht2nn : ∀ j, 0 ≤ t2 j := fun j => div_nonneg (pow_nonneg (mul_nonneg hd hv) _) (by positivity)
  have hstep1 : ∀ j, t1 (j + 1) ≤ q1 * t1 j := by
    intro j
    simp only [ht1]
    rw [show n + 1 + (j + 1) = (n + 1 + j) + 1 by omega, pow_div_factorial_succ]
    have hm : (n : ℝ) + 2 ≤ ((n + 1 + j : ℕ) : ℝ) + 1 := by
      push_cast
      linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
    have hq : d / (((n + 1 + j : ℕ) : ℝ) + 1) ≤ q1 := div_le_div_of_nonneg_left hd hn2 hm
    have h0 := ht1nn j
    simp only [ht1] at h0
    calc d ^ (n + 1 + j) / ((n + 1 + j)! : ℝ) * (d / (((n + 1 + j : ℕ) : ℝ) + 1))
        ≤ d ^ (n + 1 + j) / ((n + 1 + j)! : ℝ) * q1 := mul_le_mul_of_nonneg_left hq h0
      _ = q1 * (d ^ (n + 1 + j) / ((n + 1 + j)! : ℝ)) := by ring
  have hstep2 : ∀ j, t2 (j + 1) ≤ q2 * t2 j := by
    intro j
    simp only [ht2]
    rw [show n + 1 + (j + 1) = (n + 1 + j) + 1 by omega, pow_div_factorial_sq_succ]
    have hm : ((n : ℝ) + 2) ^ 2 ≤ (((n + 1 + j : ℕ) : ℝ) + 1) ^ 2 := by
      apply pow_le_pow_left₀ hn2.le
      push_cast
      linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
    have hq : d * v / (((n + 1 + j : ℕ) : ℝ) + 1) ^ 2 ≤ q2 :=
      div_le_div_of_nonneg_left (mul_nonneg hd hv) (by positivity) hm
    have h0 := ht2nn j
    simp only [ht2] at h0
    calc (d * v) ^ (n + 1 + j) / ((n + 1 + j)! : ℝ) ^ 2 *
          (d * v / (((n + 1 + j : ℕ) : ℝ) + 1) ^ 2)
        ≤ (d * v) ^ (n + 1 + j) / ((n + 1 + j)! : ℝ) ^ 2 * q2 :=
          mul_le_mul_of_nonneg_left hq h0
      _ = q2 * ((d * v) ^ (n + 1 + j) / ((n + 1 + j)! : ℝ) ^ 2) := by ring
  have htail : ∑ j ∈ range (M' - (n + 1)), G (n + 1 + j) ≤
      2 * Real.exp v * t1 0 / (1 - q1) + t2 0 / (1 - q2) := by
    have hle : ∀ j ∈ range (M' - (n + 1)), G (n + 1 + j) ≤ 2 * Real.exp v * t1 j + t2 j := by
      intro j _
      simp only [hG, ht1, ht2]
      rw [ite_eq_right (by omega)]
      unfold twoGroup
      have hs : ∑ l ∈ range (n + 1 + j), v ^ l / (l ! : ℝ) ≤ Real.exp v :=
        Real.sum_le_exp_of_nonneg hv _
      have hpos : 0 ≤ 2 * d ^ (n + 1 + j) / ((n + 1 + j)! : ℝ) :=
        div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hd _)) (by positivity)
      have := mul_le_mul_of_nonneg_left hs hpos
      have e : 2 * d ^ (n + 1 + j) / ((n + 1 + j)! : ℝ) * Real.exp v =
          2 * Real.exp v * (d ^ (n + 1 + j) / ((n + 1 + j)! : ℝ)) := by ring
      linarith
    have hs1 := sum_le_geometric hq1 hq1' ht1nn hstep1 (M' - (n + 1))
    have hs2 := sum_le_geometric hq2 hq2' ht2nn hstep2 (M' - (n + 1))
    calc ∑ j ∈ range (M' - (n + 1)), G (n + 1 + j)
        ≤ ∑ j ∈ range (M' - (n + 1)), (2 * Real.exp v * t1 j + t2 j) := sum_le_sum hle
      _ = 2 * Real.exp v * ∑ j ∈ range (M' - (n + 1)), t1 j +
            ∑ j ∈ range (M' - (n + 1)), t2 j := by rw [sum_add_distrib, mul_sum]
      _ ≤ 2 * Real.exp v * (t1 0 / (1 - q1)) + t2 0 / (1 - q2) := by
          have := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ 2 * Real.exp v)
          linarith
      _ = 2 * Real.exp v * t1 0 / (1 - q1) + t2 0 / (1 - q2) := by ring
  have hfinal : 2 * Real.exp v * t1 0 / (1 - q1) + t2 0 / (1 - q2) =
      2 * Real.exp v * d ^ (n + 1) / (((n + 1)! : ℝ) * (1 - d / (n + 2))) +
        (d * v) ^ (n + 1) / ((((n + 1)! : ℝ)) ^ 2 * (1 - d * v / ((n : ℝ) + 2) ^ 2)) := by
    simp only [ht1, ht2, q1, q2, add_zero]
    rw [mul_div_assoc', div_div, div_div]
  unfold twoTagUpper
  linarith

/-- **`cor:two-cut-series`, the bound**: for two tags with totals `d_0 = d_1 = d ≥ 0` and
`v_0 = v_1 = v ≥ 0`, and `n` with `d < n + 2`, `dv < (n + 2)²`,
`𝔗(d, v) ≤ 𝔗^+_n(d, v)`. -/
theorem tagSeries_two_le {d v : ℝ} (hd : 0 ≤ d) (hv : 0 ≤ v) (n : ℕ) (h1 : d < n + 2)
    (h2 : d * v < ((n : ℝ) + 2) ^ 2) :
    tagSeries (fun _ : Bool => d) (fun _ => v) ≤ twoTagUpper n d v := by
  apply Real.tsum_le_of_sum_le (fun k => tagMin_nonneg (fun _ => hd) (fun _ => hv) k)
  intro s
  obtain ⟨M, hM⟩ : ∃ M, ∀ k ∈ s, ∀ j, k j < M := by
    refine ⟨∑ k ∈ s, ∑ j, k j + 1, ?_⟩
    intro k hk j
    have h1 : k j ≤ ∑ j', k j' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)
    have h2 : ∑ j', k j' ≤ ∑ k' ∈ s, ∑ j', k' j' :=
      Finset.single_le_sum (f := fun k' : Bool → ℕ => ∑ j', k' j') (fun _ _ => Nat.zero_le _) hk
    omega
  set box := Fintype.piFinset (fun _ : Bool => range M) with hbox
  have hsub : s ⊆ box := by
    intro k hk
    simp only [hbox, Fintype.mem_piFinset, mem_range]
    exact hM k hk
  have hprod : ∑ x ∈ range M ×ˢ range M, twoTerm d v x.1 x.2 =
      ∑ a ∈ range M, ∑ b ∈ range M, twoTerm d v a b := sum_product _ _ _
  have hpair : ∑ k ∈ box, tagMin (fun _ => d) (fun _ => v) k ≤
      ∑ a ∈ range M, ∑ b ∈ range M, twoTerm d v a b := by
    rw [← hprod]
    calc ∑ k ∈ box, tagMin (fun _ => d) (fun _ => v) k
        ≤ ∑ k ∈ box, twoTerm d v (k true) (k false) :=
          sum_le_sum fun k _ => tagMin_two_le d v k
      _ = ∑ x ∈ range M ×ˢ range M, twoTerm d v x.1 x.2 := by
          apply Finset.sum_nbij' (fun k => (k true, k false)) (fun x b => if b then x.1 else x.2)
          · intro k hk
            simp only [hbox, Fintype.mem_piFinset, mem_range] at hk
            simp [hk true, hk false]
          · intro x hx
            simp only [mem_product, mem_range] at hx
            simp only [hbox, Fintype.mem_piFinset, mem_range]
            intro b
            cases b <;> simp [hx.1, hx.2]
          · intro k _
            funext b
            cases b <;> rfl
          · intro x _
            rfl
          · intro k _
            rfl
  calc ∑ k ∈ s, tagMin (fun _ => d) (fun _ => v) k
      ≤ ∑ k ∈ box, tagMin (fun _ => d) (fun _ => v) k :=
        sum_le_sum_of_subset_of_nonneg hsub
          (fun k _ _ => tagMin_nonneg (fun _ => hd) (fun _ => hv) k)
    _ ≤ ∑ a ∈ range M, ∑ b ∈ range M, twoTerm d v a b := hpair
    _ = ∑ i ∈ range M, (if i = 0 then 0 else twoGroup d v i) := sum_twoTerm_square d v M
    _ ≤ twoTagUpper n d v := sum_groups_le hd hv n h1 h2 M

/-- **`cor:two-cut-series` at upper totals**: if the two tag totals satisfy
`0 ≤ d_j ≤ d̂` and `0 ≤ v_j ≤ v̂`, and `d̂ < n + 2`, `d̂ v̂ < (n + 2)²`, then
`𝔗(d, v) ≤ 𝔗^+_n(d̂, v̂)`. -/
theorem tagSeries_two_le_upper {d v : Bool → ℝ} {dh vh : ℝ} (hd : ∀ j, 0 ≤ d j)
    (hv : ∀ j, 0 ≤ v j) (hdh : ∀ j, d j ≤ dh) (hvh : ∀ j, v j ≤ vh) (n : ℕ)
    (h1 : dh < n + 2) (h2 : dh * vh < ((n : ℝ) + 2) ^ 2) :
    tagSeries d v ≤ twoTagUpper n dh vh := by
  have hdh0 : 0 ≤ dh := (hd true).trans (hdh true)
  have hvh0 : 0 ≤ vh := (hv true).trans (hvh true)
  exact (tagSeries_mono hd hv hdh hvh).trans (tagSeries_two_le hdh0 hvh0 n h1 h2)

end Sarkozy.RecordExpansion
