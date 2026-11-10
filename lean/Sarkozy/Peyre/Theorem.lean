module

public import Sarkozy.Peyre.One
public import Sarkozy.Peyre.Weights

/-!
# Peyre's tensorization in finite form, V: the theorem (prefix form)

The proof of `thm:peyre-finite` in Appendix B (`B_peyre_finite.tex`), Steps 1–4:

* `lossMatrix`: the matrix `T_l` of Step 3, with its action (`lossMatrix_mulVec`) and its
  column sums (`lossMatrix_colsum`).
* `peyre_core`: Steps 1–4 for fixed weights `α > 0` with `𝓔𝓔ᵀα ≤ λα`:
  `‖E[f | Y]‖² ≤ λ ‖f‖²` for every `f ∈ L²₀(X)`.
* `peyre_prefix_corrLe`, `peyre_prefix`: the second (prefix) statement of
  `thm:peyre-finite`, with the operator norm of `𝓔` given by an upper bound `Λ`
  (`‖𝓔 x‖₂ ≤ Λ ‖x‖₂` for all `x`).

Indices are `0`-based: `X 0, …, X (N-1)` and `Y 0, …, Y (M-1)` are the paper's
`X_1, …, X_N` and `Y_1, …, Y_M`; `pre X k` is the paper's `X_{<k+1}`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Peyre

open Sarkozy

/-! ### Elementary inequalities -/

/-- `2 √s √t ≤ c s + t / c` for `s, t ≥ 0`, `c > 0`. -/
theorem two_sqrt_mul_le {s t c : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hc : 0 < c) :
    2 * √s * √t ≤ c * s + t / c := by
  have hs' : s = √s ^ 2 := (Real.sq_sqrt hs).symm
  have ht' : t = √t ^ 2 := (Real.sq_sqrt ht).symm
  set p := √s
  set q := √t
  rw [hs', ht']
  have key : 0 ≤ (c * p - q) ^ 2 / c := div_nonneg (sq_nonneg _) hc.le
  have e : (c * p - q) ^ 2 / c = c * p ^ 2 + q ^ 2 / c - 2 * p * q := by
    field_simp
    ring
  linarith

/-- Split a sum over `Fin N` at `k`: the term `k`, the terms above `k`, the terms below. -/
theorem sum_split_at {N : ℕ} (g : Fin N → ℝ) (k : Fin N) :
    ∑ i, g i = g k + ∑ i ∈ Finset.univ.filter (fun i => k < i), g i +
      ∑ i ∈ Finset.univ.filter (fun i => i < k), g i := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter]
  have hpt : ∀ i, g i = (if i = k then g i else 0) + (if k < i then g i else 0) +
      (if i < k then g i else 0) := by
    intro i
    rcases lt_trichotomy i k with h | h | h
    · rw [ite_eq_right (ne_of_lt h), ite_eq_right (not_lt.mpr h.le), ite_eq_left h]
      ring
    · rw [ite_eq_left h, ite_eq_right (by rw [h]; exact lt_irrefl k),
        ite_eq_right (by rw [h]; exact lt_irrefl k)]
      ring
    · rw [ite_eq_right (ne_of_gt h), ite_eq_left h, ite_eq_right (not_lt.mpr h.le)]
      ring
  conv_lhs => rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ k,
    ite_eq_left (Finset.mem_univ k)]

/-- The transpose of a matrix has the same operator-norm bound. -/
theorem transpose_bound {N M : ℕ} (ε : Fin N → Fin M → ℝ) {Λ : ℝ}
    (hop : ∀ x : Fin M → ℝ, ∑ k, (∑ l, ε k l * x l) ^ 2 ≤ Λ ^ 2 * ∑ l, x l ^ 2)
    (y : Fin N → ℝ) : ∑ l, (∑ k, ε k l * y k) ^ 2 ≤ Λ ^ 2 * ∑ k, y k ^ 2 := by
  set z : Fin M → ℝ := fun l => ∑ k, ε k l * y k with hz
  set S := ∑ l, z l ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun l _ => sq_nonneg _)
  have e : S = ∑ k, y k * ∑ l, ε k l * z l := by
    rw [hS]
    have : ∀ l, z l ^ 2 = ∑ k, ε k l * y k * z l := by
      intro l
      rw [sq, hz, Finset.sum_mul]
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y (fun k => ∑ l, ε k l * z l)
  rw [← e] at hcs
  have h2 := hop z
  have hy0 : 0 ≤ ∑ k, y k ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have h3 : S ^ 2 ≤ (∑ k, y k ^ 2) * (Λ ^ 2 * S) :=
    hcs.trans (mul_le_mul_of_nonneg_left h2 hy0)
  show S ≤ Λ ^ 2 * ∑ k, y k ^ 2
  rcases hS0.eq_or_lt with h0 | h0
  · rw [← h0]
    exact mul_nonneg (sq_nonneg Λ) hy0
  · nlinarith

/-! ### The matrix `T_l` of Step 3 -/

/-- The matrix `T_l` of Step 3 (for the column `e = (ε_{il})_i` and weights `a`):
`(T_l)_{ii} = e_i² + ∑_{j>i} e_i e_j a_j/a_i`, `(T_l)_{ik} = e_i e_k a_i/a_k` for `k > i`,
and `0` below the diagonal. -/
noncomputable def lossMatrix {N : ℕ} (e a : Fin N → ℝ) (i k : Fin N) : ℝ :=
  (if i = k then e i ^ 2 + ∑ j ∈ Finset.univ.filter (fun j => i < j), e i * e j * (a j / a i)
    else 0) + (if i < k then e i * e k * (a i / a k) else 0)

theorem lossMatrix_nonneg {N : ℕ} {e a : Fin N → ℝ} (he : ∀ i, 0 ≤ e i) (ha : ∀ i, 0 < a i)
    (i k : Fin N) : 0 ≤ lossMatrix e a i k := by
  unfold lossMatrix
  apply add_nonneg
  · split_ifs
    · refine add_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun j _ => ?_))
      exact mul_nonneg (mul_nonneg (he i) (he j)) (div_nonneg (ha j).le (ha i).le)
    · exact le_refl 0
  · split_ifs
    · exact mul_nonneg (mul_nonneg (he i) (he k)) (div_nonneg (ha i).le (ha k).le)
    · exact le_refl 0

theorem lossMatrix_mulVec {N : ℕ} (e a v : Fin N → ℝ) (i : Fin N) :
    ∑ k, lossMatrix e a i k * v k = e i ^ 2 * v i +
      ∑ j ∈ Finset.univ.filter (fun j => i < j),
        e i * e j * (a j / a i * v i + a i / a j * v j) := by
  classical
  unfold lossMatrix
  simp only [add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ i, ite_eq_left (Finset.mem_univ i),
    ← Finset.sum_filter, Finset.sum_mul, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem lossMatrix_colsum {N : ℕ} (e a : Fin N → ℝ) (ha : ∀ i, 0 < a i) (k : Fin N) :
    ∑ i, lossMatrix e a i k = e k / a k * ∑ i, e i * a i := by
  classical
  unfold lossMatrix
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ k, ite_eq_left (Finset.mem_univ k),
    ← Finset.sum_filter, sum_split_at (fun i => e i * a i) k, mul_add, mul_add,
    Finset.mul_sum, Finset.mul_sum]
  have hak : a k ≠ 0 := (ha k).ne'
  have h1 : e k / a k * (e k * a k) = e k ^ 2 := by field_simp
  rw [h1]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    ring

/-! ### Steps 1–4 -/

variable {Ω : Type*} [Fintype Ω] {α β : Type*}

/-- Steps 1–4 of the proof of `thm:peyre-finite`.  Given the conditional correlation bounds
`ρ(X_k; Y_l | X_{<k} = x, Y_{<l} = y) ≤ ε_{kl}` (inequality form) and weights `a > 0` with
`(𝓔𝓔ᵀ a)_k ≤ λ a_k`, `λ < 1`, every `f ∈ L²₀(X)` has `‖E[f | Y]‖² ≤ λ ‖f‖²`. -/
theorem peyre_core (μ : FiniteLaw Ω) {N M : ℕ} (X : Fin N → Ω → α) (Y : Fin M → Ω → β)
    (ε : Fin N → Fin M → ℝ) (hε : ∀ k l, 0 ≤ ε k l)
    (hyp : ∀ (k : Fin N) (l : Fin M) (x : Fin N → Option α) (y : Fin M → Option β)
      (h : 0 < prob μ (fun ω => pre X k ω = x ∧ pre Y l ω = y)),
      CorrLe (condLaw μ (fun ω => pre X k ω = x ∧ pre Y l ω = y) h) (X k) (Y l) (ε k l))
    (a : Fin N → ℝ) (ha : ∀ k, 0 < a k) {lam : ℝ} (hlam : lam < 1)
    (hKa : ∀ k, ∑ l, ε k l * ∑ i, ε i l * a i ≤ lam * a k)
    (f : Ω → ℝ) (hf : IsFunOf (pre X N) f) (hf0 : μ.expect f = 0) :
    μ.expect (fun ω => condExp μ (pre Y M) f ω ^ 2) ≤ lam * μ.expect (fun ω => f ω ^ 2) := by
  classical
  set ZZ : ℕ → ℕ → Ω → (Fin N → Option α) × (Fin M → Option β) :=
    fun l i ω => (pre X i ω, pre Y l ω) with hZZ
  set W : ℕ → Fin N → ℝ := fun l i => mdiff μ (ZZ l) f i with hW
  have hchainZ : ∀ l j, j < N → Coarser (ZZ l j) (ZZ l (j + 1)) := by
    intro l j _ ω ω' h
    simp only [hZZ, Prod.mk.injEq] at h ⊢
    exact ⟨pre_coarser X (Nat.le_succ j) ω ω' h.1, h.2⟩
  have hfZ : ∀ l, IsFunOf (ZZ l N) f := fun l => hf.mono (coarser_fst (pre X N) (pre Y l))
  -- Step 1
  have hsum : ∀ l, ∑ i, W l i = μ.expect (fun ω => (f ω - condExp μ (pre Y l) f ω) ^ 2) := by
    intro l
    have h1 := chain_pythagoras μ (ZZ l) N (hchainZ l) f (hfZ l)
    have h2 : condExp μ (ZZ l 0) f = condExp μ (pre Y l) f := by
      apply condExp_congr_level
      intro ω ω'
      simp only [hZZ, Prod.mk.injEq]
      exact ⟨fun h => h.2, fun h => ⟨pre_zero_eq X ω ω', h⟩⟩
    rw [h2] at h1
    exact h1.symm
  have hsum0 : ∑ i, W 0 i = μ.expect (fun ω => f ω ^ 2) := by
    rw [hsum 0]
    have h0 : ∀ ω, condExp μ (pre Y 0) f ω = 0 := fun ω => by
      rw [condExp_of_const μ (pre_zero_eq Y) f ω, hf0]
    simp only [h0, sub_zero]
  have hsumM : ∑ i, W M i = μ.expect (fun ω => f ω ^ 2) -
      μ.expect (fun ω => condExp μ (pre Y M) f ω ^ 2) := by
    rw [hsum M, expect_sq_eq_condExp_add μ (pre Y M) f]
    ring
  -- Step 2
  set T : Fin M → Fin N → Fin N → ℝ := fun l => lossMatrix (fun i => ε i l) a with hT
  have hrec : ∀ (l : Fin M) i, W l i - ∑ k, T l i k * W l k ≤ W ((l : ℕ) + 1) i := by
    intro l i
    set V : Fin N → Ω → ℝ := fun j => condExp μ (pre Y l)
      (fun ω => (condExp μ (ZZ l ((j : ℕ) + 1)) f ω - condExp μ (ZZ l j) f ω) ^ 2) with hV
    set V' : Fin N → Ω → ℝ := fun j => condExp μ (pre Y l)
      (fun ω => (condExp μ (ZZ ((l : ℕ) + 1) ((j : ℕ) + 1)) f ω -
        condExp μ (ZZ ((l : ℕ) + 1) j) f ω) ^ 2) with hV'
    have hEV : ∀ j, μ.expect (V j) = W l j := fun j => expect_condExp μ _ _
    have hEV' : ∀ j, μ.expect (V' j) = W ((l : ℕ) + 1) j := fun j => expect_condExp μ _ _
    have hpt : ∀ ω₀, μ.weight ω₀ ≠ 0 → V i ω₀ - ∑ k, T l i k * V k ω₀ ≤ V' i ω₀ := by
      intro ω₀ hw₀
      set E₀ : Ω → Prop := fun ω => pre Y l ω = pre Y l ω₀ with hE₀
      have hpos : 0 < prob μ E₀ := prob_pos_of_weight (E := E₀) rfl hw₀
      have hyp' : ∀ (k : Fin N) (x : Fin N → Option α)
          (h : 0 < prob (condLaw μ E₀ hpos) (fun ω => pre X k ω = x)),
          CorrLe (condLaw (condLaw μ E₀ hpos) (fun ω => pre X k ω = x) h) (X k) (Y l) (ε k l) := by
        intro k x h
        have h' := prob_and_pos_of_cond μ E₀ hpos _ h
        rw [cond_cond μ E₀ hpos _ h h']
        exact hyp k l x (pre Y l ω₀) h'
      have hone := peyre_one (condLaw μ E₀ hpos) X (Y l) (fun k => ε k l) (fun k => hε k l)
        hyp' f hf i
      have hcondX : ∀ (m : ℕ) ω, E₀ ω →
          condExp (condLaw μ E₀ hpos) (pre X m) f ω = condExp μ (ZZ l m) f ω := by
        intro m ω hω
        apply condExp_cond
        intro ω'
        simp only [hZZ, Prod.mk.injEq, hE₀]
        rw [hω]
      have hcondXY : ∀ (m : ℕ) ω, E₀ ω →
          condExp (condLaw μ E₀ hpos) (fun ω => (pre X m ω, Y l ω)) f ω =
            condExp μ (ZZ ((l : ℕ) + 1) m) f ω := by
        intro m ω hω
        apply condExp_cond
        intro ω'
        simp only [hZZ, Prod.mk.injEq, hE₀]
        rw [pre_succ_eq_iff Y l ω' ω, hω]
        tauto
      have hw_id : ∀ j : Fin N, mdiff (condLaw μ E₀ hpos) (pre X) f j = V j ω₀ := by
        intro j
        simp only [hV, mdiff]
        rw [← cond_expect_level μ (pre Y l) ω₀ hpos]
        apply cond_expect_congr
        intro ω hω
        rw [hcondX _ ω hω, hcondX _ ω hω]
      have hws_id : mdiff (condLaw μ E₀ hpos) (fun i ω => (pre X i ω, Y l ω)) f i = V' i ω₀ := by
        simp only [hV', mdiff]
        rw [← cond_expect_level μ (pre Y l) ω₀ hpos]
        apply cond_expect_congr
        intro ω hω
        rw [hcondXY _ ω hω, hcondXY _ ω hω]
      rw [hws_id] at hone
      simp only [hw_id] at hone
      have hVnn : ∀ j, 0 ≤ V j ω₀ := fun j => condExp_nonneg μ _ (fun ω => sq_nonneg _) ω₀
      have hTmul : ∑ k, T l i k * V k ω₀ = ε i l ^ 2 * V i ω₀ +
          ∑ j ∈ Finset.univ.filter (fun j => i < j),
            ε i l * ε j l * (a j / a i * V i ω₀ + a i / a j * V j ω₀) :=
        lossMatrix_mulVec (fun i => ε i l) a (fun k => V k ω₀) i
      rw [hTmul]
      have hamgm : 2 * ε i l * √(V i ω₀) *
          ∑ j ∈ Finset.univ.filter (fun j => i < j), ε j l * √(V j ω₀) ≤
          ∑ j ∈ Finset.univ.filter (fun j => i < j),
            ε i l * ε j l * (a j / a i * V i ω₀ + a i / a j * V j ω₀) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j _
        have h2 := two_sqrt_mul_le (hVnn i) (hVnn j) (div_pos (ha j) (ha i))
        have e1 : V j ω₀ / (a j / a i) = a i / a j * V j ω₀ := by
          have := (ha i).ne'
          have := (ha j).ne'
          field_simp
        rw [e1] at h2
        have hee : 0 ≤ ε i l * ε j l := mul_nonneg (hε i l) (hε j l)
        calc 2 * ε i l * √(V i ω₀) * (ε j l * √(V j ω₀)) =
            ε i l * ε j l * (2 * √(V i ω₀) * √(V j ω₀)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h2 hee
      linarith
    have hint := expect_mono_ae μ hpt
    rw [FiniteLaw.expect_sub, expect_sum] at hint
    simp only [FiniteLaw.expect_const_mul, hEV, hEV'] at hint
    exact hint
  -- Step 3
  have hTnn : ∀ l i k, 0 ≤ T l i k := fun l i k => lossMatrix_nonneg (fun i => hε i l) ha i k
  have hcol : ∀ k, ∑ l, ∑ i, T l i k ≤ lam := by
    intro k
    have hc : ∀ l, ∑ i, T l i k = ε k l / a k * ∑ i, ε i l * a i :=
      fun l => lossMatrix_colsum (fun i => ε i l) a ha k
    rw [Finset.sum_congr rfl (fun l _ => hc l)]
    have e : ∑ l, ε k l / a k * ∑ i, ε i l * a i = (∑ l, ε k l * ∑ i, ε i l * a i) / a k := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [e, div_le_iff₀ (ha k)]
    exact hKa k
  -- Step 4
  have hpot := potential W T (fun l _ k => mdiff_nonneg μ _ f _) hTnn hrec hlam hcol
  rw [hsum0, hsumM] at hpot
  nlinarith [expect_sq_nonneg μ f]

end Sarkozy.Peyre
