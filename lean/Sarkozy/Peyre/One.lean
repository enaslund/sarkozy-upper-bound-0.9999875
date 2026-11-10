module

public import Sarkozy.Peyre.Correlation

/-!
# Peyre's tensorization in finite form, III: one variable against a list

* `pre X i` is the prefix `X_{<i} = (X_0, …, X_{i-1})` of a finite family
  `X : Fin N → Ω → α`, encoded as one random variable with values in
  `Fin N → Option α` (`some (X k ω)` for `k < i`, `none` otherwise).  Its level
  sets are those of the tuple `(X_0, …, X_{i-1})` (`pre_eq_iff`).  Indices are
  `0`-based: the paper's `X_{<i}` (1-based) is `pre X (i-1)` and its `X_{≤ i}` is
  `pre X i`.
* `mdiff μ Z f i = ‖E[f | Z (i+1)] - E[f | Z i]‖²` is the squared norm of a
  martingale difference along a chain of random variables.
* `chain_pythagoras`: the martingale differences of a chain are orthogonal and
  sum to `f - E[f | Z 0]` (Step 1 of the proof of `thm:peyre-finite`).
* `peyre_one`: `lem:peyre:one` (Peyre's Lemma 3.3.3).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Peyre

open Sarkozy

variable {Ω : Type*} {α β γ : Type*}

/-! ### Prefix variables -/

/-- The prefix `X_{<i} = (X_k)_{k < i}` of the family `X`, as one random variable. -/
def pre {N : ℕ} (X : Fin N → Ω → α) (i : ℕ) (ω : Ω) : Fin N → Option α :=
  fun k => if (k : ℕ) < i then some (X k ω) else none

theorem pre_eq_iff {N : ℕ} (X : Fin N → Ω → α) (i : ℕ) (ω ω' : Ω) :
    pre X i ω = pre X i ω' ↔ ∀ k : Fin N, (k : ℕ) < i → X k ω = X k ω' := by
  constructor
  · intro h k hk
    have := congrFun h k
    simp only [pre, hk, ite_true, Option.some.injEq] at this
    exact this
  · intro h
    funext k
    by_cases hk : (k : ℕ) < i
    · simp only [pre, hk, ite_true, h k hk]
    · simp only [pre, hk, ite_false]

theorem pre_coarser {N : ℕ} (X : Fin N → Ω → α) {i j : ℕ} (hij : i ≤ j) :
    Coarser (pre X i) (pre X j) := by
  intro ω ω' h
  rw [pre_eq_iff] at h ⊢
  exact fun k hk => h k (lt_of_lt_of_le hk hij)

theorem pre_succ_eq_iff {N : ℕ} (X : Fin N → Ω → α) (k : Fin N) (ω ω' : Ω) :
    pre X ((k : ℕ) + 1) ω = pre X ((k : ℕ) + 1) ω' ↔
      X k ω = X k ω' ∧ pre X k ω = pre X k ω' := by
  rw [pre_eq_iff, pre_eq_iff]
  constructor
  · intro h
    exact ⟨h k (Nat.lt_succ_self _), fun j hj => h j (Nat.lt_succ_of_lt hj)⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · exact h2 j hj
    · rw [show j = k from Fin.ext hj]
      exact h1

theorem pre_zero_eq {N : ℕ} (X : Fin N → Ω → α) (ω ω' : Ω) : pre X 0 ω = pre X 0 ω' :=
  (pre_eq_iff X 0 ω ω').mpr (fun _ hk => absurd hk (Nat.not_lt_zero _))

theorem pre_full_eq_iff {N : ℕ} (X : Fin N → Ω → α) (ω ω' : Ω) :
    pre X N ω = pre X N ω' ↔ (fun k => X k ω) = (fun k => X k ω') := by
  rw [pre_eq_iff]
  constructor
  · intro h
    funext k
    exact h k k.isLt
  · intro h k _
    exact congrFun h k

variable [Fintype Ω]

/-! ### Martingale differences along a chain -/

/-- `‖E[f | Z (i+1)] - E[f | Z i]‖²`. -/
noncomputable def mdiff (μ : FiniteLaw Ω) (Z : ℕ → Ω → γ) (f : Ω → ℝ) (i : ℕ) : ℝ :=
  μ.expect (fun ω => (condExp μ (Z (i + 1)) f ω - condExp μ (Z i) f ω) ^ 2)

theorem mdiff_nonneg (μ : FiniteLaw Ω) (Z : ℕ → Ω → γ) (f : Ω → ℝ) (i : ℕ) :
    0 ≤ mdiff μ Z f i := μ.second_moment_nonneg _

/-- Orthogonal martingale decomposition along an increasing chain `Z 0, …, Z n` with
`f ∈ L²(Z n)`: `‖f - E[f | Z i]‖² = ∑_{i ≤ j < n} ‖E[f|Z (j+1)] - E[f|Z j]‖²`. -/
theorem chain_pythagoras_aux (μ : FiniteLaw Ω) (Z : ℕ → Ω → γ) (n : ℕ)
    (hZ : ∀ j, j < n → Coarser (Z j) (Z (j + 1))) (f : Ω → ℝ) (hf : IsFunOf (Z n) f) :
    ∀ m i, i + m = n → μ.expect (fun ω => (f ω - condExp μ (Z i) f ω) ^ 2) =
      ∑ j ∈ Finset.range m, mdiff μ Z f (i + j) := by
  intro m
  induction m with
  | zero =>
    intro i hi
    rw [add_zero] at hi
    subst hi
    rw [Finset.sum_range_zero]
    exact expect_sq_sub_condExp_eq_zero μ _ hf
  | succ m ih =>
    intro i hi
    rw [expect_sq_sub_condExp_step μ (hZ i (by omega)) f, ih (i + 1) (by omega),
      Finset.sum_range_succ']
    have e : ∀ j ∈ Finset.range m, mdiff μ Z f (i + 1 + j) = mdiff μ Z f (i + (j + 1)) := by
      intro j _
      rw [show i + 1 + j = i + (j + 1) by omega]
    rw [Finset.sum_congr rfl e, add_zero, add_comm]
    rfl

/-- Step 1 of the proof of `thm:peyre-finite`: for an increasing chain `Z 0, …, Z n` and
`f ∈ L²(Z n)`, `‖f - E[f | Z 0]‖² = ∑_{i < n} ‖E[f|Z (i+1)] - E[f|Z i]‖²`. -/
theorem chain_pythagoras (μ : FiniteLaw Ω) (Z : ℕ → Ω → γ) (n : ℕ)
    (hZ : ∀ j, j < n → Coarser (Z j) (Z (j + 1))) (f : Ω → ℝ) (hf : IsFunOf (Z n) f) :
    μ.expect (fun ω => (f ω - condExp μ (Z 0) f ω) ^ 2) =
      ∑ i : Fin n, mdiff μ Z f i := by
  rw [chain_pythagoras_aux μ Z n hZ f hf n 0 (zero_add n),
    Fin.sum_univ_eq_sum_range (fun i => mdiff μ Z f i) n]
  simp only [zero_add]

/-! ### `lem:peyre:one` -/

/-- `lem:peyre:one` (Peyre, Lemma 3.3.3).  Let `X_0, …, X_{N-1}, Y` be random variables and
`ε_k ≥ 0` with `ρ(X_k; Y | X_{<k} = x) ≤ ε_k` (inequality form) for every `k` and every value
`x` of `X_{<k}` of positive probability.  For `f ∈ L²(X_0, …, X_{N-1})` put
`w_k = ‖E[f | X_{≤k}] - E[f | X_{<k}]‖²` and
`w*_k = ‖E[f | X_{≤k}, Y] - E[f | X_{<k}, Y]‖²`.  Then
`w*_k ≥ (1 - ε_k²) w_k - 2 ε_k √w_k ∑_{j > k} ε_j √w_j`. -/
theorem peyre_one (μ : FiniteLaw Ω) {N : ℕ} (X : Fin N → Ω → α) (Y : Ω → β)
    (ε : Fin N → ℝ) (hε : ∀ k, 0 ≤ ε k)
    (hyp : ∀ (k : Fin N) (x : Fin N → Option α) (h : 0 < prob μ (fun ω => pre X k ω = x)),
      CorrLe (condLaw μ (fun ω => pre X k ω = x) h) (X k) Y (ε k))
    (f : Ω → ℝ) (hf : IsFunOf (pre X N) f) (k : Fin N) :
    (1 - ε k ^ 2) * mdiff μ (pre X) f k -
        2 * ε k * √(mdiff μ (pre X) f k) *
          ∑ j ∈ Finset.univ.filter (fun j => k < j), ε j * √(mdiff μ (pre X) f j) ≤
      mdiff μ (fun i ω => (pre X i ω, Y ω)) f k := by
  classical
  set Zs : ℕ → Ω → (Fin N → Option α) × β := fun i ω => (pre X i ω, Y ω) with hZs
  set c : ℕ → Ω → ℝ := fun i => condExp μ (pre X i) f with hc
  set cs : ℕ → Ω → ℝ := fun i => condExp μ (Zs i) f with hcs
  set u : ℕ → Ω → ℝ := fun i ω => cs i ω - c i ω with hu_def
  set D : ℕ → ℝ := fun i => μ.expect (fun ω => u i ω ^ 2) with hD_def
  set w : ℕ → ℝ := fun i => mdiff μ (pre X) f i with hw_def
  set ws : ℕ → ℝ := fun i => mdiff μ Zs f i with hws_def
  have hc_pre : ∀ i, Coarser (pre X i) (Zs i) := fun i => coarser_fst _ _
  have hc_X : ∀ i, Coarser (pre X i) (pre X (i + 1)) := fun i => pre_coarser X (Nat.le_succ i)
  have hc_Zs : ∀ i, Coarser (Zs i) (Zs (i + 1)) := by
    intro i ω ω' h
    simp only [hZs, Prod.mk.injEq] at h ⊢
    exact ⟨pre_coarser X (Nat.le_succ i) ω ω' h.1, h.2⟩
  have hu : ∀ i, IsFunOf (Zs i) (u i) := fun i =>
    (condExp_isFunOf μ _ f).sub ((condExp_isFunOf μ _ f).mono (hc_pre i))
  have hD0 : ∀ i, 0 ≤ D i := fun i => μ.second_moment_nonneg _
  -- (F1) `‖f - E[f|X_{<i}]‖² = D_i + ‖f - E[f|X_{<i},Y]‖²` (Step 1 of the paper)
  have F1 : ∀ i, μ.expect (fun ω => (f ω - c i ω) ^ 2) =
      D i + μ.expect (fun ω => (f ω - cs i ω) ^ 2) := by
    intro i
    have horth : μ.expect (fun ω => u i ω * (f ω - cs i ω)) = 0 := by
      have := expect_sub_condExp_mul μ (Zs i) f (u i) (hu i)
      simpa only [mul_comm] using this
    have := expect_sq_add_of_orth μ (u i) (fun ω => f ω - cs i ω) horth
    rw [← this]
    exact μ.expect_congr (fun ω => by simp only [hu_def]; ring)
  have F2 : ∀ i, μ.expect (fun ω => (f ω - c i ω) ^ 2) =
      w i + μ.expect (fun ω => (f ω - c (i + 1) ω) ^ 2) :=
    fun i => expect_sq_sub_condExp_step μ (hc_X i) f
  have F3 : ∀ i, μ.expect (fun ω => (f ω - cs i ω) ^ 2) =
      ws i + μ.expect (fun ω => (f ω - cs (i + 1) ω) ^ 2) :=
    fun i => expect_sq_sub_condExp_step μ (hc_Zs i) f
  -- (F4) `D_N = 0`
  have F4 : D N = 0 := by
    apply expect_eq_zero_ae
    intro ω hw
    have h1 : cs N ω = f ω := condExp_eq_self μ (Zs N) (hf.mono (hc_pre N)) hw
    have h2 : c N ω = f ω := condExp_eq_self μ (pre X N) hf hw
    simp only [hu_def, h1, h2, sub_self]
    ring
  -- (F5) Step 2 of the paper: `√D_i ≤ ε_i √w_i + √D_{i+1}`
  have F5 : ∀ i (hi : i < N), √(D i) ≤ ε ⟨i, hi⟩ * √(w i) + √(D (i + 1)) := by
    intro i hi
    set j : Fin N := ⟨i, hi⟩ with hj
    have hjv : (j : ℕ) = i := rfl
    set h := u i with hh
    have hDj : D i = μ.expect (fun ω => (f ω - c i ω) * h ω) := by
      have h0 : μ.expect (fun ω => (f ω - cs i ω) * h ω) = 0 :=
        expect_sub_condExp_mul μ (Zs i) f h (hu i)
      have : μ.expect (fun ω => (f ω - c i ω) * h ω) = μ.expect (fun ω => h ω ^ 2) +
          μ.expect (fun ω => (f ω - cs i ω) * h ω) := by
        rw [← FiniteLaw.expect_add]
        exact μ.expect_congr (fun ω => by simp only [hh, hu_def]; ring)
      rw [this, h0, add_zero]
    set fj : Ω → ℝ := fun ω => c (i + 1) ω - c i ω with hfj
    have hsplit : μ.expect (fun ω => (f ω - c i ω) * h ω) =
        μ.expect (fun ω => fj ω * h ω) + μ.expect (fun ω => (f ω - c (i + 1) ω) * h ω) := by
      rw [← FiniteLaw.expect_add]
      exact μ.expect_congr (fun ω => by simp only [hfj]; ring)
    have hb : |μ.expect (fun ω => fj ω * h ω)| ≤ ε j * √(w i) * √(D i) := by
      have hb' := cond_decorrelation' μ (X j) Y (pre X j) (hε j) (hyp j) (f := fj) (g := h)
        (fun ω ω' hx hp => by
          have hpre : pre X ((j : ℕ) + 1) ω = pre X ((j : ℕ) + 1) ω' :=
            (pre_succ_eq_iff X j ω ω').mpr ⟨hx, hp⟩
          rw [hjv] at hpre
          exact ((condExp_isFunOf μ _ f).sub ((condExp_isFunOf μ _ f).mono (hc_X i)))
            ω ω' hpre)
        (fun ω _ => by
          simp only [hfj, hc, hjv]
          rw [condExp_sub, condExp_condExp_of_coarser μ (hc_X i),
            condExp_condExp_of_coarser μ (Coarser.refl _), sub_self])
        (fun ω ω' hy hp => hu i ω ω' (by rw [hjv] at hp; exact Prod.ext hp hy))
      exact hb'
    have hs : |μ.expect (fun ω => (f ω - c (i + 1) ω) * h ω)| ≤ √(D (i + 1)) * √(D i) := by
      have h0 : μ.expect (fun ω => (f ω - cs (i + 1) ω) * h ω) = 0 :=
        expect_sub_condExp_mul μ (Zs (i + 1)) f h ((hu i).mono (hc_Zs i))
      have e : μ.expect (fun ω => (f ω - c (i + 1) ω) * h ω) =
          μ.expect (fun ω => u (i + 1) ω * h ω) := by
        have : μ.expect (fun ω => (f ω - c (i + 1) ω) * h ω) =
            μ.expect (fun ω => u (i + 1) ω * h ω) +
              μ.expect (fun ω => (f ω - cs (i + 1) ω) * h ω) := by
          rw [← FiniteLaw.expect_add]
          exact μ.expect_congr (fun ω => by simp only [hu_def]; ring)
        rw [this, h0, add_zero]
      rw [e]
      exact μ.abs_expect_mul_le _ _
    have htot : D i ≤ (ε j * √(w i) + √(D (i + 1))) * √(D i) := by
      calc D i = μ.expect (fun ω => fj ω * h ω) +
            μ.expect (fun ω => (f ω - c (i + 1) ω) * h ω) := by rw [hDj, hsplit]
        _ ≤ |μ.expect (fun ω => fj ω * h ω) +
            μ.expect (fun ω => (f ω - c (i + 1) ω) * h ω)| := le_abs_self _
        _ ≤ |μ.expect (fun ω => fj ω * h ω)| +
            |μ.expect (fun ω => (f ω - c (i + 1) ω) * h ω)| := abs_add_le _ _
        _ ≤ ε j * √(w i) * √(D i) + √(D (i + 1)) * √(D i) := add_le_add hb hs
        _ = _ := by ring
    have hsq : √(D i) ^ 2 = D i := Real.sq_sqrt (hD0 i)
    have hrhs : 0 ≤ ε j * √(w i) + √(D (i + 1)) :=
      add_nonneg (mul_nonneg (hε j) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    rcases (Real.sqrt_nonneg (D i)).eq_or_lt with h0 | h0
    · rw [← h0]
      exact hrhs
    · nlinarith
  -- (F6) Step 3 of the paper: `√D_i ≤ ∑_{j ≥ i} ε_j √w_j`
  have F6 : ∀ m i, i + m = N →
      √(D i) ≤ ∑ j : Fin N, if i ≤ (j : ℕ) then ε j * √(w j) else 0 := by
    intro m
    induction m with
    | zero =>
      intro i hi
      rw [add_zero] at hi
      subst hi
      rw [F4, Real.sqrt_zero]
      refine Finset.sum_nonneg (fun j _ => ?_)
      split_ifs
      · exact mul_nonneg (hε j) (Real.sqrt_nonneg _)
      · exact le_refl 0
    | succ m ih =>
      intro i hi
      have hiN : i < N := by omega
      have hS : (∑ j : Fin N, if i ≤ (j : ℕ) then ε j * √(w j) else 0) =
          ε ⟨i, hiN⟩ * √(w i) +
            ∑ j : Fin N, if i + 1 ≤ (j : ℕ) then ε j * √(w j) else 0 := by
        have hpt : ∀ j : Fin N, (if i ≤ (j : ℕ) then ε j * √(w j) else 0) =
            (if j = ⟨i, hiN⟩ then ε j * √(w j) else 0) +
              (if i + 1 ≤ (j : ℕ) then ε j * √(w j) else 0) := by
          intro j
          by_cases h1 : (j : ℕ) = i
          · have hj' : j = ⟨i, hiN⟩ := Fin.ext h1
            have h2 : i ≤ (j : ℕ) := le_of_eq h1.symm
            have h3 : ¬ i + 1 ≤ (j : ℕ) := by omega
            rw [ite_eq_left h2, ite_eq_left hj', ite_eq_right h3, add_zero]
          · have h4 : j ≠ ⟨i, hiN⟩ := fun h => h1 (by rw [h])
            rw [ite_eq_right h4, zero_add]
            by_cases h2 : i ≤ (j : ℕ)
            · have h3 : i + 1 ≤ (j : ℕ) := by omega
              rw [ite_eq_left h2, ite_eq_left h3]
            · have h3 : ¬ i + 1 ≤ (j : ℕ) := by omega
              rw [ite_eq_right h2, ite_eq_right h3]
        rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib,
          Finset.sum_ite_eq' Finset.univ (⟨i, hiN⟩ : Fin N), ite_eq_left (Finset.mem_univ _)]
      rw [hS]
      have h5 := F5 i hiN
      have h6 := ih (i + 1) (by omega)
      linarith
  -- Step 4 of the paper
  have hk := k.isLt
  have hdiff : w k - ws k = D k - D (k + 1) := by
    have a1 := F1 k
    have a2 := F1 (k + 1)
    have a3 := F2 k
    have a4 := F3 k
    linarith
  have hS1 : √(D (k + 1)) ≤
      ∑ j ∈ Finset.univ.filter (fun j => k < j), ε j * √(w j) := by
    have h7 := F6 (N - ((k : ℕ) + 1)) ((k : ℕ) + 1) (by omega)
    rw [Finset.sum_filter]
    refine h7.trans (le_of_eq (Finset.sum_congr rfl (fun j _ => ?_)))
    have hiff : ((k : ℕ) + 1 ≤ (j : ℕ)) ↔ k < j := by
      rw [Fin.lt_def]
      omega
    simp only [hiff]
  have hF5 : √(D k) ≤ ε k * √(w k) + √(D (k + 1)) := by
    have := F5 k hk
    simpa only [Fin.eta] using this
  have hrhs : 0 ≤ ε k * √(w k) + √(D (k + 1)) :=
    add_nonneg (mul_nonneg (hε k) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hDk : D k ≤ (ε k * √(w k) + √(D (k + 1))) ^ 2 := by
    calc D k = √(D k) ^ 2 := (Real.sq_sqrt (hD0 k)).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hF5 2
  have hb2 : √(D (k + 1)) ^ 2 = D (k + 1) := Real.sq_sqrt (hD0 _)
  have hw2 : √(w k) ^ 2 = w k := Real.sq_sqrt (mdiff_nonneg μ _ f k)
  have hcoef : 0 ≤ 2 * ε k * √(w k) :=
    mul_nonneg (mul_nonneg zero_le_two (hε k)) (Real.sqrt_nonneg _)
  have hfin : w k - ws k ≤ ε k ^ 2 * w k + 2 * ε k * √(w k) *
      ∑ j ∈ Finset.univ.filter (fun j => k < j), ε j * √(w j) := by
    calc w k - ws k = D k - D (k + 1) := hdiff
      _ ≤ (ε k * √(w k) + √(D (k + 1))) ^ 2 - D (k + 1) := by linarith
      _ = ε k ^ 2 * √(w k) ^ 2 + 2 * ε k * √(w k) * √(D (k + 1)) := by
          linear_combination hb2
      _ = ε k ^ 2 * w k + 2 * ε k * √(w k) * √(D (k + 1)) := by rw [hw2]
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hS1 hcoef
        linarith
  show (1 - ε k ^ 2) * w k - 2 * ε k * √(w k) *
      ∑ j ∈ Finset.univ.filter (fun j => k < j), ε j * √(w j) ≤ ws k
  linarith

/-- `lem:peyre:one` with the hypothesis stated with conditional maximal correlations:
`ρ(X_k; Y | X_{<k} = x) ≤ ε_k` for every `k` and every value `x` of `X_{<k}` of positive
probability (values encoded through `pre`). -/
theorem peyre_one_maxCorr (μ : FiniteLaw Ω) {N : ℕ} (X : Fin N → Ω → α) (Y : Ω → β)
    (ε : Fin N → ℝ) (hε : ∀ k, 0 ≤ ε k)
    (hyp : ∀ (k : Fin N) (x : Fin N → Option α) (h : 0 < prob μ (fun ω => pre X k ω = x)),
      maxCorr (condLaw μ (fun ω => pre X k ω = x) h) (X k) Y ≤ ε k)
    (f : Ω → ℝ) (hf : IsFunOf (pre X N) f) (k : Fin N) :
    (1 - ε k ^ 2) * mdiff μ (pre X) f k -
        2 * ε k * √(mdiff μ (pre X) f k) *
          ∑ j ∈ Finset.univ.filter (fun j => k < j), ε j * √(mdiff μ (pre X) f j) ≤
      mdiff μ (fun i ω => (pre X i ω, Y ω)) f k :=
  peyre_one μ X Y ε hε (fun k x h => corrLe_of_maxCorr_le (hyp k x h)) f hf k

end Sarkozy.Peyre
