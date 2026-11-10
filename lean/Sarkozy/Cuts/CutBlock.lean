module

public import Sarkozy.Cuts.CutKernel
public import Sarkozy.ProbabilityProducts

/-!
# Cuts, IX″: blocks of primes (`lem:spec:cutkernel` (e))

`13_cuts_correlations.tex`, `lem:spec:cutkernel` (e). For a finite index set `ι` (the primes of a
block `B`) and finite fields `F i`, put `λ_B(G) = ⊗_i λ_i(G)`, `μ_B = ⊗_i μ_i` and
`A_B = ⊗_i A_i`. The kernel of `A_B` relative to `μ_B ⊗ μ_B` is `∏_i K_i/Z_i`. Then
`E_{λ_B(G)}[F(x) H(x')] = ⟨F, A_B H⟩_{μ_B}` for all real `F`, `H` (`block_cut_form`).

The proof is `pi_pair_law`: if each pair `(T_i, S_i)` has the law `μ_i ⊗ μ_i · k_i` under `λ_i`,
the pair of product maps has the law `μ ⊗ μ · ∏_i k_i` under `⊗_i λ_i`.

The block clause of (f) is `block_cut_form_w`, with the reweighted laws `reweight` and
`pi_reweight` (`(⊗_i λ_i)^{∏ w_i} = ⊗_i λ_i^{w_i}`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering Sarkozy.Labellings

section PiPair

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω Ξ : ι → Type*} [∀ i, Fintype (Ω i)]
  [∀ i, Fintype (Ξ i)] [∀ i, DecidableEq (Ξ i)]

omit [DecidableEq ι] [∀ i, Fintype (Ξ i)] in
theorem indicator_pi_eq (ξ : ∀ i, Ξ i) (z : ∀ i, Ξ i) :
    (if z = ξ then (1 : ℝ) else 0) = ∏ i, (if z i = ξ i then (1 : ℝ) else 0) := by
  rw [Finset.prod_boole]
  by_cases h : z = ξ
  · rw [ite_eq_left h, ite_eq_left (fun i _ => by rw [h])]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (funext (fun i => h' i (Finset.mem_univ _))))]

omit [∀ i, DecidableEq (Ξ i)] in
theorem fun_eq_sum_indicator [∀ i, DecidableEq (Ξ i)] (Fn : (∀ i, Ξ i) → ℝ) (z : ∀ i, Ξ i) :
    Fn z = ∑ ξ, Fn ξ * (if z = ξ then (1 : ℝ) else 0) := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]

/-- **Products of pair laws.** If under `λ_i` the pair `(T_i, S_i)` has the law
`μ_i ⊗ μ_i · k_i`, then under `⊗_i λ_i` the pair of product maps has the law `μ ⊗ μ · ∏_i k_i`. -/
theorem pi_pair_law (lam : ∀ i, FiniteLaw (Ω i)) (μ : ∀ i, FiniteLaw (Ξ i))
    (T S : ∀ i, Ω i → Ξ i) (k : ∀ i, Ξ i → Ξ i → ℝ)
    (hpair : ∀ i a b, (lam i).expect (fun y => (if T i y = a then (1 : ℝ) else 0) *
      (if S i y = b then 1 else 0)) = (μ i).weight a * (μ i).weight b * k i a b)
    (Fn Hn : (∀ i, Ξ i) → ℝ) :
    (FiniteLaw.pi lam).expect (fun y => Fn (fun i => T i (y i)) * Hn (fun i => S i (y i))) =
      kernelForm (FiniteLaw.pi μ) (FiniteLaw.pi μ) (fun ξ ξ' => ∏ i, k i (ξ i) (ξ' i)) Fn Hn := by
  have hexp : ∀ y : ∀ i, Ω i, Fn (fun i => T i (y i)) * Hn (fun i => S i (y i)) =
      ∑ ξ, ∑ ξ', Fn ξ * Hn ξ' * ∏ i, ((if T i (y i) = ξ i then (1 : ℝ) else 0) *
        (if S i (y i) = ξ' i then 1 else 0)) := by
    intro y
    rw [fun_eq_sum_indicator Fn, fun_eq_sum_indicator Hn, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ξ' _ => ?_)
    rw [Finset.prod_mul_distrib, ← indicator_pi_eq ξ (fun i => T i (y i)),
      ← indicator_pi_eq ξ' (fun i => S i (y i))]
    ring
  simp only [hexp]
  rw [Sarkozy.Peyre.expect_sum]
  simp only [kernelForm, LinearMap.mk₂_apply]
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  rw [Sarkozy.Peyre.expect_sum]
  refine Finset.sum_congr rfl (fun ξ' _ => ?_)
  rw [FiniteLaw.expect_const_mul]
  have hprod := FiniteLaw.expect_pi_product lam
    (fun i y => (if T i y = ξ i then (1 : ℝ) else 0) * (if S i y = ξ' i then 1 else 0))
  rw [hprod]
  simp only [hpair]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  change Fn ξ * Hn ξ' * ((∏ i, (μ i).weight (ξ i)) * (∏ i, (μ i).weight (ξ' i)) *
    ∏ i, k i (ξ i) (ξ' i)) = (∏ i, (μ i).weight (ξ i)) * (∏ i, (μ i).weight (ξ' i)) * Fn ξ *
      (∏ i, k i (ξ i) (ξ' i)) * Hn ξ'
  ring

end PiPair

namespace SpecData

variable {U : Type*} [Fintype U] [DecidableEq U] (D : SpecData U)

/-- The pair law at one prime, on indicators: `E_λ[1_{x=a} 1_{x'=b}] = μ(a) μ(b) K(a,b)/Z`. -/
theorem expect_halves_indicator {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hne : (injLabellings F D.G).Nonempty) (a b : D.cut.Half → F) :
    (graphLaw D.G hne).expect (fun y => (if D.halfL y = a then (1 : ℝ) else 0) *
      (if D.halfR y = b then 1 else 0)) =
      (D.halfLaw hne).weight a * (D.halfLaw hne).weight b * (D.cutK a b / D.cutZ hne) := by
  rw [D.expect_halves hne (fun x x' => (if x = a then (1 : ℝ) else 0) * (if x' = b then 1 else 0)),
    FiniteLaw.expect_product]
  dsimp only
  have inner : ∀ x : D.cut.Half → F, (D.halfLaw hne).expect (fun x' => D.cutK x x' *
      ((if x = a then (1 : ℝ) else 0) * (if x' = b then 1 else 0))) =
      (if x = a then (1 : ℝ) else 0) * ((D.halfLaw hne).weight b * D.cutK x b) := by
    intro x
    simp only [FiniteLaw.expect]
    have h1 : ∀ x', (D.halfLaw hne).weight x' * (D.cutK x x' *
        ((if x = a then (1 : ℝ) else 0) * (if x' = b then 1 else 0))) =
        (if x = a then (1 : ℝ) else 0) *
          (if x' = b then (D.halfLaw hne).weight x' * D.cutK x x' else 0) := fun x' => by
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun x' _ => h1 x'), ← Finset.mul_sum, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
  have e : (D.halfLaw hne).expect (fun x => (D.halfLaw hne).expect (fun x' =>
      D.cutK x x' * ((if x = a then (1 : ℝ) else 0) * (if x' = b then 1 else 0)))) =
      (D.halfLaw hne).weight a * (D.halfLaw hne).weight b * D.cutK a b := by
    simp only [inner]
    simp only [FiniteLaw.expect]
    have h2 : ∀ x, (D.halfLaw hne).weight x * ((if x = a then (1 : ℝ) else 0) *
        ((D.halfLaw hne).weight b * D.cutK x b)) =
        if x = a then (D.halfLaw hne).weight x * ((D.halfLaw hne).weight b * D.cutK x b)
          else 0 := fun x => by
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    ring
  rw [e]
  ring

/-- **`lem:spec:cutkernel` (e).** For a block of primes, `E_{λ_B(G)}[F(x) H(x')] = ⟨F, A_B H⟩_{μ_B}`,
where `A_B = ⊗_i A_i` has the kernel `∏_i K_i/Z_i` relative to `μ_B ⊗ μ_B`. -/
theorem block_cut_form {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Type*}
    [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (hne : ∀ i, (injLabellings (F i) D.G).Nonempty)
    (Fn Hn : (∀ i, D.cut.Half → F i) → ℝ) :
    (FiniteLaw.pi (fun i => graphLaw D.G (hne i))).expect
        (fun y => Fn (fun i => D.halfL (y i)) * Hn (fun i => D.halfR (y i))) =
      kernelForm (FiniteLaw.pi (fun i => D.halfLaw (hne i)))
        (FiniteLaw.pi (fun i => D.halfLaw (hne i)))
        (fun ξ ξ' => ∏ i, D.cutK (ξ i) (ξ' i) / D.cutZ (hne i)) Fn Hn :=
  pi_pair_law (fun i => graphLaw D.G (hne i)) (fun i => D.halfLaw (hne i))
    (fun _ => D.halfL) (fun _ => D.halfR) (fun i a b => D.cutK a b / D.cutZ (hne i))
    (fun i a b => D.expect_halves_indicator (hne i) a b) Fn Hn

end SpecData

/-! ### Blocks of reweighted laws (`lem:spec:cutkernel` (f), last statement) -/

section Reweight

variable {Ω : Type*} [Fintype Ω]

/-- The reweighted law `λ^w = wλ/E_λ w`. -/
noncomputable def reweight (lam : FiniteLaw Ω) (w : Ω → ℝ) (hw : ∀ y, 0 ≤ w y)
    (hpos : 0 < lam.expect w) : FiniteLaw Ω where
  weight y := w y * lam.weight y / lam.expect w
  nonneg y := div_nonneg (mul_nonneg (hw y) (lam.nonneg y)) hpos.le
  total := by
    rw [← Finset.sum_div]
    have : ∑ y, w y * lam.weight y = lam.expect w := by
      unfold FiniteLaw.expect
      exact Finset.sum_congr rfl (fun y _ => mul_comm _ _)
    rw [this, div_self hpos.ne']

theorem reweight_expect (lam : FiniteLaw Ω) (w : Ω → ℝ) (hw : ∀ y, 0 ≤ w y)
    (hpos : 0 < lam.expect w) (Φ : Ω → ℝ) :
    (reweight lam w hw hpos).expect Φ = lam.expect (fun y => w y * Φ y) / lam.expect w := by
  set c := lam.expect w
  change ∑ y, (w y * lam.weight y / c) * Φ y = lam.expect (fun y => w y * Φ y) / c
  unfold FiniteLaw.expect
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun y _ => by ring)

end Reweight

/-- `E_{⊗λ_i}[∏ w_i] = ∏_i E_{λ_i} w_i`, so `(⊗_i λ_i)^{∏ w_i} = ⊗_i λ_i^{w_i}`. -/
theorem pi_reweight {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] (lam : ∀ i, FiniteLaw (Ω i)) (w : ∀ i, Ω i → ℝ)
    (hw : ∀ i y, 0 ≤ w i y) (hpos : ∀ i, 0 < (lam i).expect (w i)) (y : ∀ i, Ω i) :
    (FiniteLaw.pi (fun i => reweight (lam i) (w i) (hw i) (hpos i))).weight y =
      (∏ i, w i (y i)) * (FiniteLaw.pi lam).weight y /
        (FiniteLaw.pi lam).expect (fun z => ∏ i, w i (z i)) := by
  rw [FiniteLaw.expect_pi_product lam w]
  change ∏ i, (w i (y i) * (lam i).weight (y i) / (lam i).expect (w i)) =
    (∏ i, w i (y i)) * (∏ i, (lam i).weight (y i)) / ∏ i, (lam i).expect (w i)
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]

namespace SpecData

variable {U : Type*} [Fintype U] [DecidableEq U] (D : SpecData U)

/-- The reweighted pair law at one prime, on indicators. -/
theorem expect_halves_indicator_w {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hne : (injLabellings F D.G).Nonempty) (w : (U → F) → ℝ) (hw : ∀ y, 0 ≤ w y)
    (hpos : 0 < (graphLaw D.G hne).expect w) (a b : D.cut.Half → F) :
    (reweight (graphLaw D.G hne) w hw hpos).expect (fun y => (if D.halfL y = a then (1 : ℝ) else 0) *
      (if D.halfR y = b then 1 else 0)) =
      (D.halfLaw hne).weight a * (D.halfLaw hne).weight b *
        (w (D.glue a b) * D.cutK a b / (D.cutZ hne * (graphLaw D.G hne).expect w)) := by
  rw [reweight_expect, D.expect_halves_w hne w
    (fun x x' => (if x = a then (1 : ℝ) else 0) * (if x' = b then 1 else 0)),
    FiniteLaw.expect_product]
  dsimp only
  have inner : ∀ x : D.cut.Half → F, (D.halfLaw hne).expect (fun x' => w (D.glue x x') *
      D.cutK x x' * ((if x = a then (1 : ℝ) else 0) * (if x' = b then 1 else 0))) =
      (if x = a then (1 : ℝ) else 0) * ((D.halfLaw hne).weight b * (w (D.glue x b) * D.cutK x b)) := by
    intro x
    simp only [FiniteLaw.expect]
    have h1 : ∀ x', (D.halfLaw hne).weight x' * (w (D.glue x x') * D.cutK x x' *
        ((if x = a then (1 : ℝ) else 0) * (if x' = b then 1 else 0))) =
        (if x = a then (1 : ℝ) else 0) *
          (if x' = b then (D.halfLaw hne).weight x' * (w (D.glue x x') * D.cutK x x') else 0) :=
      fun x' => by split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun x' _ => h1 x'), ← Finset.mul_sum, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
  simp only [inner]
  simp only [FiniteLaw.expect]
  have h2 : ∀ x, (D.halfLaw hne).weight x * ((if x = a then (1 : ℝ) else 0) *
      ((D.halfLaw hne).weight b * (w (D.glue x b) * D.cutK x b))) =
      if x = a then (D.halfLaw hne).weight x * ((D.halfLaw hne).weight b *
        (w (D.glue x b) * D.cutK x b)) else 0 := fun x => by
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  ring

/-- **`lem:spec:cutkernel` (f), blocks.** For `w_B = ∏_i w_i`,
`E_{⊗_i λ_i^{w_i}}[F(x) H(x')] = ⟨F, (⊗_i A^{w_i}) H⟩_{μ_B}`. -/
theorem block_cut_form_w {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Type*}
    [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (hne : ∀ i, (injLabellings (F i) D.G).Nonempty) (w : ∀ i, (U → F i) → ℝ)
    (hw : ∀ i y, 0 ≤ w i y) (hpos : ∀ i, 0 < (graphLaw D.G (hne i)).expect (w i))
    (Fn Hn : (∀ i, D.cut.Half → F i) → ℝ) :
    (FiniteLaw.pi (fun i => reweight (graphLaw D.G (hne i)) (w i) (hw i) (hpos i))).expect
        (fun y => Fn (fun i => D.halfL (y i)) * Hn (fun i => D.halfR (y i))) =
      kernelForm (FiniteLaw.pi (fun i => D.halfLaw (hne i)))
        (FiniteLaw.pi (fun i => D.halfLaw (hne i)))
        (fun ξ ξ' => ∏ i, w i (D.glue (ξ i) (ξ' i)) * D.cutK (ξ i) (ξ' i) /
          (D.cutZ (hne i) * (graphLaw D.G (hne i)).expect (w i))) Fn Hn :=
  pi_pair_law (fun i => reweight (graphLaw D.G (hne i)) (w i) (hw i) (hpos i))
    (fun i => D.halfLaw (hne i)) (fun _ => D.halfL) (fun _ => D.halfR)
    (fun i a b => w i (D.glue a b) * D.cutK a b /
      (D.cutZ (hne i) * (graphLaw D.G (hne i)).expect (w i)))
    (fun i a b => D.expect_halves_indicator_w (hne i) (w i) (hw i) (hpos i) a b) Fn Hn

end SpecData

end Sarkozy.Cuts
