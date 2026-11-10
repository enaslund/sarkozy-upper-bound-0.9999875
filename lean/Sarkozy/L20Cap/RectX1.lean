module

public import Sarkozy.L20Cap.GapComplement

/-!
# `prop:l20-rectangular`(b): the nonstar remainder from a bound on the half law

`paper/sections/20_middle_reference.tex`, proof of `prop:l20-rectangular`(b): "The raw extraction
bound of `cor:soft-kernels`(a) also bounds this compression: the core and pair coordinate
embeddings are isometries, and the eight-edge kernel uses the same `221` subsets." Notation of
`Sarkozy.L20Cap.GapComplement`.

`cor:soft-kernels`(a) (X1's `Sarkozy.ExtractionK`, `sk_soft_extraction_leaf_*`) bounds the soft
nonstar class sums of a kernel on the half law `μ_p = λ_p(G_{F,2})`. Here the eight-edge kernel is
`N(x; x') = N(C(x); b(x'))` (`Nrect`, the sum of the `221` nonstar terms of the eight cross pairs
core of `x` × pair of `x'`), a kernel on `L²(μ_p)` (`NrectH`). This file is the bridge:

* `halfLaw_core_marginal`, `halfLaw_pair_marginal`: the core and the pair of a half are
  distributed by `μ^core` and `μ^pair` (the second by the orbit argument: the avoidance
  probability of a pair is square-affine invariant and symmetric, hence constant);
* **`hN_of_half`**: a bound `|⟨φ, N h⟩_{μ_p}| ≤ N_A‖φ‖‖h‖` on the half law (the form in which
  `cor:soft-kernels`(a) is stated) gives the hypothesis `hN` of `l20_prime_caps_full`:
  `‖C ↦ E_b[N(C; b)g(b)]‖ ≤ N_A‖g‖` for every `g` on the pairs.

What remains for `N_A` itself: the exact partition of the `221` nonstar subsets into the `42`
two-leaf classes of the certificate (`middle_factor_probe/rectangular_A.hist.json.gz` stores only
their `13` aggregated signatures, not the classes), the hypotheses of X1's
`sk_soft_extraction_leaf_*` for each class, and the identification of `μ_p` with X1's `graphLaw`
of `G_{F,2}` (`halfLaw_weight`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (CoreT F)]
  [Nonempty (PairT F)]

/-- The eight-edge nonstar kernel on the halves: `N(x; x') = N(C(x); b(x'))`. -/
noncomputable def NrectH (x x' : CoreT F × PairT F) : ℝ := Nrect x.1 x'.2

/-! ## The marginals of the half law -/

/-- **The core marginal**: `E_{μ_p}[v(C)] = E_{μ^core}[v]`. -/
theorem halfLaw_core_marginal (h6 : 6 ≤ Fintype.card F) (v : CoreT F → ℝ) :
    (halfLaw h6).expect (fun x => v x.1) = (coreLaw (F := F)).expect v := by
  have hP0 := hP_pos (F := F) h6
  unfold halfLaw
  rw [condLaw_expect, FiniteLaw.expect_product]
  have e : ∀ C : CoreT F, (pairLaw (F := F)).expect (fun b => (if Avoid (C, b) then 1 else 0) *
      v (C, b).1) = v C * prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid := by
    intro C
    have h1 := prob_avoid_core (F := F) C
    rw [← hP_eq] at h1
    rw [← h1, ← FiniteLaw.expect_const_mul]
    exact (pairLaw (F := F)).expect_congr fun b => by ring
  rw [(coreLaw (F := F)).expect_congr e, FiniteLaw.expect_mul_const, ← mul_assoc, mul_comm _
    ((coreLaw (F := F)).expect v), mul_assoc, inv_mul_cancel₀ hP0.ne', mul_one]

omit [Nonempty (PairT F)] in
/-- The avoidance probability `P_C(b avoids C)` of a pair is square-affine invariant. -/
theorem avoidProb_affine {α : F} (hα : quadraticChar F α = 1) (β : F) (b : PairT F) :
    (coreLaw (F := F)).expect (fun C => if Avoid (C, affPairEquiv (ne_zero_of_chi hα) β b) then
      (1 : ℝ) else 0) =
      (coreLaw (F := F)).expect (fun C => if Avoid (C, b) then (1 : ℝ) else 0) := by
  have hα0 := ne_zero_of_chi hα
  unfold coreLaw
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  congr 1
  rw [← Equiv.sum_comp (affCoreEquiv hα β)]
  refine sum_congr rfl fun C _ => ?_
  have hiff : Avoid ((affCoreEquiv hα β) C, affPairEquiv hα0 β b) ↔ Avoid (C, b) := by
    simp only [Avoid, affCoreEquiv, affPairEquiv, Equiv.coe_fn_mk, affCore, affPair, ne_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun k hk => h1 k (by rw [hk]), fun k hk => h2 k (by rw [hk])⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun k hk => h1 k (mul_left_cancel₀ hα0 (add_right_cancel hk)),
        fun k hk => h2 k (mul_left_cancel₀ hα0 (add_right_cancel hk))⟩
  simp only [hiff]

omit [Nonempty (PairT F)] in
theorem avoidProb_swap (b : PairT F) :
    (coreLaw (F := F)).expect (fun C => if Avoid (C, swapPair b) then (1 : ℝ) else 0) =
      (coreLaw (F := F)).expect (fun C => if Avoid (C, b) then (1 : ℝ) else 0) := by
  refine (coreLaw (F := F)).expect_congr fun C => ?_
  have hiff : Avoid (C, swapPair b) ↔ Avoid (C, b) := by
    simp only [Avoid, swapPair]
    tauto
  simp only [hiff]

omit [Nonempty (PairT F)] in
/-- **The avoidance probability of a pair is constant** (`χ(-1) = -1`). -/
theorem avoidProb_const (hm1 : quadraticChar F (-1) = -1) (b b' : PairT F) :
    (coreLaw (F := F)).expect (fun C => if Avoid (C, b) then (1 : ℝ) else 0) =
      (coreLaw (F := F)).expect (fun C => if Avoid (C, b') then (1 : ℝ) else 0) := by
  set m : F → F → ℝ := fun y y' => if h : y ≠ y' then
    (coreLaw (F := F)).expect (fun C => if Avoid (C, ⟨(y, y'), h⟩) then (1 : ℝ) else 0) else 0
    with hm
  have hm_aff : ∀ (α β : F), quadraticChar F α = 1 → ∀ y y',
      m (α * y + β) (α * y' + β) = m y y' := by
    intro α β hα y y'
    have hα0 := ne_zero_of_chi hα
    by_cases hyy : y = y'
    · subst hyy; simp [hm]
    · have hne : α * y + β ≠ α * y' + β := fun h => hyy (mul_left_cancel₀ hα0 (add_right_cancel h))
      simp only [hm, ne_eq, hyy, hne, not_false_eq_true, ↓reduceDIte]
      have := avoidProb_affine (F := F) hα β ⟨(y, y'), hyy⟩
      exact this
  have hm_symm : ∀ y y', m y' y = m y y' := by
    intro y y'
    by_cases hyy : y = y'
    · subst hyy; rfl
    · have hyy' : y' ≠ y := Ne.symm hyy
      simp only [hm, ne_eq, hyy, hyy', not_false_eq_true, ↓reduceDIte]
      exact avoidProb_swap (F := F) ⟨(y, y'), hyy⟩
  have key := pair_const hm1 (m := m) hm_aff hm_symm b.2 b'.2
  simp only [hm, ne_eq, b.2, b'.2, not_false_eq_true, ↓reduceDIte] at key
  exact key

/-- **The pair marginal**: `E_{μ_p}[u(b)] = E_{μ^pair}[u]`. -/
theorem halfLaw_pair_marginal (hm1 : quadraticChar F (-1) = -1) (h6 : 6 ≤ Fintype.card F)
    (u : PairT F → ℝ) :
    (halfLaw h6).expect (fun x => u x.2) = (pairLaw (F := F)).expect u := by
  have hP0 := hP_pos (F := F) h6
  set P := prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid with hPdef
  -- the avoidance probability of every pair is `P`
  have hconst : ∀ b : PairT F,
      (coreLaw (F := F)).expect (fun C => if Avoid (C, b) then (1 : ℝ) else 0) = P := by
    intro b
    obtain ⟨b₀⟩ := (inferInstance : Nonempty (PairT F))
    have hav : (pairLaw (F := F)).expect (fun b' =>
        (coreLaw (F := F)).expect (fun C => if Avoid (C, b') then (1 : ℝ) else 0)) = P := by
      rw [hPdef]
      unfold prob
      rw [FiniteLaw.expect_product, Cuts.expect_comm]
    have : (fun b' : PairT F =>
        (coreLaw (F := F)).expect (fun C => if Avoid (C, b') then (1 : ℝ) else 0)) =
        fun _ => (coreLaw (F := F)).expect (fun C => if Avoid (C, b) then (1 : ℝ) else 0) :=
      funext fun b' => avoidProb_const hm1 b' b
    rw [this, FiniteLaw.expect_const] at hav
    exact hav
  unfold halfLaw
  rw [condLaw_expect, FiniteLaw.expect_product, Cuts.expect_comm]
  have e : ∀ b : PairT F, (coreLaw (F := F)).expect (fun C => (if Avoid (C, b) then 1 else 0) *
      u (C, b).2) = u b * P := by
    intro b
    rw [← hconst b, ← FiniteLaw.expect_const_mul]
    exact (coreLaw (F := F)).expect_congr fun C => by ring
  rw [(pairLaw (F := F)).expect_congr e, FiniteLaw.expect_mul_const, ← hPdef, ← mul_assoc,
    mul_comm _ ((pairLaw (F := F)).expect u), mul_assoc, inv_mul_cancel₀ hP0.ne', mul_one]

/-! ## The bridge -/

/-- **`prop:l20-rectangular`(b), the isometric embeddings**: a bound
`|⟨φ, N h⟩_{μ_p}| ≤ N_A‖φ‖‖h‖` for the eight-edge nonstar kernel on the half law (the form of
`cor:soft-kernels`(a)) gives `‖C ↦ E_b[N(C; b)g(b)]‖_{μ^core} ≤ N_A‖g‖_{μ^pair}` for every `g`
(the hypothesis `hN` of `l20_prime_caps_full`). -/
theorem hN_of_half (hm1 : quadraticChar F (-1) = -1) (h6 : 6 ≤ Fintype.card F) {NA : ℝ}
    (hNA : 0 ≤ NA)
    (hhalf : ∀ φ h : CoreT F × PairT F → ℝ,
      |kernelForm (halfLaw h6) (halfLaw h6) NrectH φ h| ≤
        NA * nrm (halfLaw h6) φ * nrm (halfLaw h6) h)
    (g : PairT F → ℝ) :
    nrm (coreLaw (F := F)) (fun C => (pairLaw (F := F)).expect (fun b => Nrect C b * g b)) ≤
      NA * nrm (pairLaw (F := F)) g := by
  set G : CoreT F → ℝ := fun C => (pairLaw (F := F)).expect (fun b => Nrect C b * g b) with hG
  have hφ : nrm (halfLaw h6) (fun x => G x.1) = nrm (coreLaw (F := F)) G := by
    unfold nrm ip
    rw [halfLaw_core_marginal h6 (fun C => G C * G C)]
  have hh : nrm (halfLaw h6) (fun x => g x.2) = nrm (pairLaw (F := F)) g := by
    unfold nrm ip
    rw [halfLaw_pair_marginal hm1 h6 (fun b => g b * g b)]
  have hform : kernelForm (halfLaw h6) (halfLaw h6) NrectH (fun x => G x.1) (fun x => g x.2) =
      nrm (coreLaw (F := F)) G ^ 2 := by
    rw [kernelForm_apply]
    have inner : ∀ x : CoreT F × PairT F,
        (halfLaw h6).expect (fun x' => NrectH x x' * g x'.2) = G x.1 := by
      intro x
      unfold NrectH
      rw [halfLaw_pair_marginal hm1 h6 (fun b => Nrect x.1 b * g b)]
    simp only [inner]
    rw [nrm_sq_eq]
    unfold ip
    exact halfLaw_core_marginal h6 (fun C => G C * G C)
  have hb := hhalf (fun x => G x.1) (fun x => g x.2)
  rw [hform, hφ, hh, abs_of_nonneg (sq_nonneg _)] at hb
  have hG0 : 0 ≤ nrm (coreLaw (F := F)) G := nrm_nonneg _ _
  by_cases hz : nrm (coreLaw (F := F)) G = 0
  · rw [hz]; exact mul_nonneg hNA (nrm_nonneg _ _)
  · have hpos : 0 < nrm (coreLaw (F := F)) G := lt_of_le_of_ne hG0 (Ne.symm hz)
    nlinarith

end Sarkozy.L20Cap
