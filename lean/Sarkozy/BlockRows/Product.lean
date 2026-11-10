module

public import Sarkozy.Cuts.RowCorrelation
public import Sarkozy.PartVLaws.FoldMarginals

@[expose] public section

/-!
# Block rows, I: conditional laws of product laws (the row adapter)

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(i), proof, "The block";
`paper/sections/13_cuts_correlations.tex`, `lem:row-comparison`(a),(c).

A row of a five-type datum at a middle value `ξ` is the kernel `T^ξ` of the conditional law of
the outer objects `(y₀, y₂)` given `y₁ = ξ`, relative to `ν^ξ ⊗ ν^ξ`. On a block the laws of
three objects are products over the primes, so the conditional laws are products too, and
`lem:row-comparison`(a),(c) bound the block row by the largest per-prime correlation and the
products of the per-prime marginal densities. This file proves that step, for any law of three
objects that is a product through a coordinate equivalence `s : 𝔛 ≃ ∀ i, Y i`:

* `condLaw π ξ`: the conditional law of `(y₀, y₂)` given `y₁ = ξ` under `π`;
* `kf_kernelOf_eq`: the form of `T_F^ξ = kernelOf π_E π_F ξ` on `L²(ν^ξ)` is the expectation under
  `condLaw π_F ξ`, when the middle laws of `π_F` and `π_E` agree at `ξ`;
* `condLaw_exact`: under an exchangeable `π_E`, both marginals of `condLaw π_E ξ` are `ν^ξ`;
* `IsProd3` and its consequences `nu_prod`, `nub_prod`, `condLaw_prod`: the middle law, the
  conditional references and the conditional laws of a product law are the products of those of
  the factors;
* `maxCorr_pi_le`: Peyre's theorem (`peyre_independent_le`) for a product law over any finite
  index type;
* **`rows_of_product`**: `lem:row-comparison`(a),(c) on a product: if every factor coupling has
  maximal correlation at most `ρ` and marginal densities in `[R_i⁻¹, R_i]`, the product coupling
  satisfies `|E_C[Φ(x)Ψ(y)] - E_ν Φ E_ν Ψ| ≤ ((∏ R_i) ρ + 2υ + υ²) ‖Φ‖ ‖Ψ‖` with
  `υ² = ∏ (1 + (R_i - 1)²) - 1`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.BlockRows

open Sarkozy Sarkozy.FiveType Sarkozy.PartV Sarkozy.PartVLaws Sarkozy.Cuts Sarkozy.Peyre

/-! ## The conditional law of the outer objects -/

section Cond

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

theorem sum_sum_weight_mid (π : FiniteLaw (Fin 3 → 𝔛)) (ξ : 𝔛) :
    ∑ x, ∑ y, π.weight ![x, ξ, y] = (nuOf π).weight ξ := by
  rw [← sum_gamOf]
  exact sum_congr rfl fun x _ => (gamOf_weight_eq_sum π x ξ).symm

/-- **The conditional law of the outer objects** `(y₀, y₂)` given `y₁ = ξ` under `π`:
`π(x, ξ, y)/π(y₁ = ξ)` (for `π(y₁ = ξ) = 0`, any law; we take the diagonal of `ν`). -/
noncomputable def condLaw (π : FiniteLaw (Fin 3 → 𝔛)) (ξ : 𝔛) : FiniteLaw (𝔛 × 𝔛) :=
  if h : (nuOf π).weight ξ = 0 then (nuOf π).map (fun x => (x, x)) else
  { weight := fun q => π.weight ![q.1, ξ, q.2] / (nuOf π).weight ξ
    nonneg := fun q => div_nonneg (π.nonneg _) ((nuOf π).nonneg ξ)
    total := by
      rw [← sum_div, Fintype.sum_prod_type, sum_sum_weight_mid, div_self h] }

theorem condLaw_weight (π : FiniteLaw (Fin 3 → 𝔛)) {ξ : 𝔛} (h : (nuOf π).weight ξ ≠ 0)
    (x y : 𝔛) : (condLaw π ξ).weight (x, y) = π.weight ![x, ξ, y] / (nuOf π).weight ξ := by
  unfold condLaw
  simp only [h, ↓reduceDIte]

/-- **The row form is the conditional expectation**: if `π_F` is `Γ`-supported in `π_E` and the
two middle laws agree at `ξ ∈ supp ν`, then `⟨Φ, T_F^ξ Ψ⟩_{ν^ξ} = E[Φ(y₀) Ψ(y₂) | y₁ = ξ]`. -/
theorem kf_kernelOf_eq (piE piF : FiniteLaw (Fin 3 → 𝔛)) (hS : GamSupported piE piF) {ξ : 𝔛}
    (hξ : (nuOf piE).weight ξ ≠ 0) (hmid : (nuOf piF).weight ξ = (nuOf piE).weight ξ)
    (Φ Ψ : 𝔛 → ℝ) :
    kf (nubOf piE ξ) (kernelOf piE piF ξ) Φ Ψ =
      (condLaw piF ξ).expect (fun q => Φ q.1 * Ψ q.2) := by
  have hF : (nuOf piF).weight ξ ≠ 0 := hmid ▸ hξ
  unfold kf FiniteLaw.expect
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [condLaw_weight piF hF, hmid, ← fold_term piE piF hS hξ x y]
  ring

omit [DecidableEq 𝔛] in
theorem normBound_le {μ : FiniteLaw 𝔛} {T : 𝔛 → 𝔛 → ℝ} {e e' : ℝ} (h : NormBound μ T e)
    (he : e ≤ e') : NormBound μ T e' := fun Φ Ψ =>
  (h Φ Ψ).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he
    (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

/-- `NormBound` from the bound of the conditional expectation. -/
theorem normBound_of_condLaw (piE piF : FiniteLaw (Fin 3 → 𝔛)) (hS : GamSupported piE piF)
    {ξ : 𝔛} (hξ : (nuOf piE).weight ξ ≠ 0) (hmid : (nuOf piF).weight ξ = (nuOf piE).weight ξ)
    {e : ℝ} (h : ∀ Φ Ψ : 𝔛 → ℝ, |(condLaw piF ξ).expect (fun q => Φ q.1 * Ψ q.2) -
      (nubOf piE ξ).expect Φ * (nubOf piE ξ).expect Ψ| ≤
        e * nrm (nubOf piE ξ) Φ * nrm (nubOf piE ξ) Ψ) :
    NormBound (nubOf piE ξ) (kernelOf piE piF ξ) e := by
  intro Φ Ψ
  rw [kf_kernelOf_eq piE piF hS hξ hmid]
  exact h Φ Ψ

/-- **Under an exchangeable `π_E` the conditional law of the outer objects has both marginals
`ν^ξ`** (densities `1`). -/
theorem condLaw_exact (piE : FiniteLaw (Fin 3 → 𝔛))
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), piE.weight (ω ∘ σ) = piE.weight ω)
    {ξ : 𝔛} (hξ : (nuOf piE).weight ξ ≠ 0) :
    HasMarginalDensities (nubOf piE ξ) (condLaw piE ξ) (fun _ => 1) (fun _ => 1) := by
  constructor
  · intro φ
    unfold FiniteLaw.expect
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun x _ => ?_
    simp only [condLaw_weight piE hξ, nubOf_weight piE hξ, gamOf_weight_eq_sum, one_mul]
    rw [← sum_mul, sum_div]
  · intro φ
    unfold FiniteLaw.expect
    rw [Fintype.sum_prod_type, sum_comm]
    refine sum_congr rfl fun y _ => ?_
    have hs : ∑ x, piE.weight ![x, ξ, y] = ∑ x, piE.weight ![y, ξ, x] :=
      sum_congr rfl fun x _ => piE_swap02 piE hexch x ξ y
    simp only [condLaw_weight piE hξ, nubOf_weight piE hξ, gamOf_weight_eq_sum, one_mul]
    rw [← sum_mul, ← sum_div, hs]

end Cond

/-! ## Products through a coordinate equivalence -/

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ i, Fintype (Y i)]
  [∀ i, DecidableEq (Y i)] {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

/-- **`π` is the product of the laws `πp i`** through the coordinates `s : 𝔛 ≃ ∀ i, Y i`:
`π(ω) = ∏_i πp_i((s ω_o)_i)_o`. -/
def IsProd3 (s : 𝔛 ≃ ∀ i, Y i) (π : FiniteLaw (Fin 3 → 𝔛))
    (πp : ∀ i, FiniteLaw (Fin 3 → Y i)) : Prop :=
  ∀ ω, π.weight ω = ∏ i, (πp i).weight (fun o => s (ω o) i)

omit [DecidableEq ι] [∀ i, DecidableEq (Y i)] [DecidableEq 𝔛] in
theorem IsProd3.weight3 {s : 𝔛 ≃ ∀ i, Y i} {π : FiniteLaw (Fin 3 → 𝔛)}
    {πp : ∀ i, FiniteLaw (Fin 3 → Y i)} (h : IsProd3 s π πp) (x ξ y : 𝔛) :
    π.weight ![x, ξ, y] = ∏ i, (πp i).weight ![s x i, s ξ i, s y i] := by
  rw [h]
  refine prod_congr rfl fun i _ => congrArg _ ?_
  funext o
  fin_cases o <;> rfl

omit [∀ i, DecidableEq (Y i)] [DecidableEq 𝔛] in
theorem sum_split (s : 𝔛 ≃ ∀ i, Y i) (g : ∀ i, Y i → ℝ) :
    ∑ x : 𝔛, ∏ i, g i (s x i) = ∏ i, ∑ y, g i y := by
  rw [Fintype.prod_sum g]
  exact Fintype.sum_equiv s _ _ fun _ => rfl

theorem gam_prod {s : 𝔛 ≃ ∀ i, Y i} {π : FiniteLaw (Fin 3 → 𝔛)}
    {πp : ∀ i, FiniteLaw (Fin 3 → Y i)} (h : IsProd3 s π πp) (x ξ : 𝔛) :
    (gamOf π).weight ![x, ξ] = ∏ i, (gamOf (πp i)).weight ![s x i, s ξ i] := by
  rw [gamOf_weight_eq_sum]
  simp only [h.weight3, gamOf_weight_eq_sum]
  exact sum_split s (fun i y => (πp i).weight ![s x i, s ξ i, y])

theorem nu_prod {s : 𝔛 ≃ ∀ i, Y i} {π : FiniteLaw (Fin 3 → 𝔛)}
    {πp : ∀ i, FiniteLaw (Fin 3 → Y i)} (h : IsProd3 s π πp) (ξ : 𝔛) :
    (nuOf π).weight ξ = ∏ i, (nuOf (πp i)).weight (s ξ i) := by
  rw [← sum_gamOf]
  simp only [gam_prod h, ← sum_gamOf]
  exact sum_split s (fun i y => (gamOf (πp i)).weight ![y, s ξ i])

theorem nu_prod_ne_zero {s : 𝔛 ≃ ∀ i, Y i} {π : FiniteLaw (Fin 3 → 𝔛)}
    {πp : ∀ i, FiniteLaw (Fin 3 → Y i)} (h : IsProd3 s π πp) {ξ : 𝔛}
    (hξ : (nuOf π).weight ξ ≠ 0) (i : ι) : (nuOf (πp i)).weight (s ξ i) ≠ 0 := by
  rw [nu_prod h] at hξ
  exact prod_ne_zero_iff.mp hξ i (mem_univ i)

theorem nub_prod {s : 𝔛 ≃ ∀ i, Y i} {π : FiniteLaw (Fin 3 → 𝔛)}
    {πp : ∀ i, FiniteLaw (Fin 3 → Y i)} (h : IsProd3 s π πp) {ξ : 𝔛}
    (hξ : (nuOf π).weight ξ ≠ 0) (x : 𝔛) :
    (nubOf π ξ).weight x = ∏ i, (nubOf (πp i) (s ξ i)).weight (s x i) := by
  rw [nubOf_weight π hξ, gam_prod h, nu_prod h, ← prod_div_distrib]
  exact prod_congr rfl fun i _ => (nubOf_weight (πp i) (nu_prod_ne_zero h hξ i) _).symm

theorem condLaw_prod {s : 𝔛 ≃ ∀ i, Y i} {π : FiniteLaw (Fin 3 → 𝔛)}
    {πp : ∀ i, FiniteLaw (Fin 3 → Y i)} (h : IsProd3 s π πp) {ξ : 𝔛}
    (hξ : (nuOf π).weight ξ ≠ 0) (x y : 𝔛) :
    (condLaw π ξ).weight (x, y) = ∏ i, (condLaw (πp i) (s ξ i)).weight (s x i, s y i) := by
  rw [condLaw_weight π hξ, h.weight3, nu_prod h, ← prod_div_distrib]
  exact prod_congr rfl fun i _ => (condLaw_weight (πp i) (nu_prod_ne_zero h hξ i) _ _).symm

/-! ## Transport to the product space -/

/-- The coordinates of a pair. -/
def split2 (s : 𝔛 ≃ ∀ i, Y i) : 𝔛 × 𝔛 ≃ ∀ i, Y i × Y i where
  toFun q i := (s q.1 i, s q.2 i)
  invFun z := (s.symm fun i => (z i).1, s.symm fun i => (z i).2)
  left_inv q := by simp
  right_inv z := by funext i; simp

omit [∀ i, DecidableEq (Y i)] [DecidableEq 𝔛] in
theorem expect_split (s : 𝔛 ≃ ∀ i, Y i) (ν : FiniteLaw 𝔛) (νp : ∀ i, FiniteLaw (Y i))
    (hν : ∀ x, ν.weight x = ∏ i, (νp i).weight (s x i)) (Φ : 𝔛 → ℝ) :
    ν.expect Φ = (FiniteLaw.pi νp).expect (fun z => Φ (s.symm z)) := by
  unfold FiniteLaw.expect
  refine Fintype.sum_equiv s _ _ fun x => ?_
  show _ = (FiniteLaw.pi νp).weight (s x) * Φ (s.symm (s x))
  rw [hν, s.symm_apply_apply]
  rfl

omit [∀ i, DecidableEq (Y i)] [DecidableEq 𝔛] in
theorem expect_split2 (s : 𝔛 ≃ ∀ i, Y i) (C : FiniteLaw (𝔛 × 𝔛))
    (Cp : ∀ i, FiniteLaw (Y i × Y i))
    (hC : ∀ x y, C.weight (x, y) = ∏ i, (Cp i).weight (s x i, s y i)) (G : 𝔛 × 𝔛 → ℝ) :
    C.expect G = (FiniteLaw.pi Cp).expect (fun z => G ((split2 s).symm z)) := by
  unfold FiniteLaw.expect
  refine Fintype.sum_equiv (split2 s) _ _ fun q => ?_
  show _ = (FiniteLaw.pi Cp).weight (split2 s q) * G ((split2 s).symm (split2 s q))
  rw [(split2 s).symm_apply_apply]
  obtain ⟨x, y⟩ := q
  rw [hC]
  rfl

/-! ## Peyre's theorem over any finite index type -/

omit [DecidableEq ι] in
theorem indepFamily_pi_equiv {γ : Type*} [DecidableEq ι] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (μ : ∀ i, FiniteLaw (Ω i)) {n : ℕ} (e : Fin n ≃ ι) (h : ∀ i, Ω i → γ) :
    IndepFamily (FiniteLaw.pi μ) (fun k x => h (e k) (x (e k))) := by
  intro E
  have hev : ∀ k, prob (FiniteLaw.pi μ) (fun x => E k (h (e k) (x (e k)))) =
      (μ (e k)).expect (fun y => ind (E k) (h (e k) y)) :=
    fun k => expect_pi_eval μ (e k) (fun y => ind (E k) (h (e k) y))
  simp only [hev]
  unfold prob
  have e1 : ind (fun x : (∀ i, Ω i) => ∀ k, E k (h (e k) (x (e k)))) =
      fun x => ∏ i, ind (E (e.symm i)) (h i (x i)) := by
    funext x
    rw [ind_forall (fun k x => E k (h (e k) (x (e k)))) x]
    exact Fintype.prod_equiv e _ _ fun k => by simp only [Equiv.symm_apply_apply]; rfl
  rw [e1, FiniteLaw.expect_pi_product μ (fun i y => ind (E (e.symm i)) (h i y))]
  exact (Fintype.prod_equiv e _ _ fun k => by simp only [Equiv.symm_apply_apply]).symm

omit [Fintype ι] [DecidableEq ι] in
theorem fun_eq_iff_sigma {Ω : ι → Type*} {n : ℕ} (e : Fin n ≃ ι) {C : ι → Type*}
    (F : ∀ i, Ω i → C i) (x x' : ∀ i, Ω i) :
    (fun i => F i (x i)) = (fun i => F i (x' i)) ↔
      (fun k => (⟨e k, F (e k) (x (e k))⟩ : Σ i, C i)) =
        (fun k => (⟨e k, F (e k) (x' (e k))⟩ : Σ i, C i)) := by
  constructor
  · intro hx
    funext k
    rw [show F (e k) (x (e k)) = F (e k) (x' (e k)) from congrFun hx (e k)]
  · intro hx
    funext j
    obtain ⟨k, rfl⟩ := e.surjective j
    have := congrFun hx k
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
    exact this

omit [DecidableEq ι] in
/-- **Peyre's theorem for a product law over a finite index type**: if every factor has maximal
correlation at most `ρ`, so has the product (`cor:peyre-independent`, `lem:row-comparison`(c)). -/
theorem maxCorr_pi_le [DecidableEq ι] {Ω A B : ι → Type*} [∀ i, Fintype (Ω i)]
    (μ : ∀ i, FiniteLaw (Ω i)) (f : ∀ i, Ω i → A i) (g : ∀ i, Ω i → B i) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ i, maxCorr (μ i) (f i) (g i) ≤ ρ) :
    maxCorr (FiniteLaw.pi μ) (fun x i => f i (x i)) (fun x i => g i (x i)) ≤ ρ := by
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hc0 : maxCorr (FiniteLaw.pi μ) (fun x i => f i (x i)) (fun x i => g i (x i)) =
      maxCorr (FiniteLaw.pi μ) (fun x k => (⟨e k, f (e k) (x (e k))⟩ : Σ i, A i))
        (fun x k => (⟨e k, g (e k) (x (e k))⟩ : Σ i, B i)) :=
    maxCorr_congr _ (fun x x' => fun_eq_iff_sigma e f x x')
      (fun x x' => fun_eq_iff_sigma e g x x')
  rw [hc0]
  refine peyre_independent_le (FiniteLaw.pi μ)
    (fun k x => (⟨e k, f (e k) (x (e k))⟩ : Σ i, A i))
    (fun k x => (⟨e k, g (e k) (x (e k))⟩ : Σ i, B i))
    (indepFamily_pi_equiv μ e (fun i c => ((⟨i, f i c⟩ : Σ i, A i), (⟨i, g i c⟩ : Σ i, B i))))
    hρ0 fun k => ?_
  have hc : maxCorr (FiniteLaw.pi μ) (fun x => (⟨e k, f (e k) (x (e k))⟩ : Σ i, A i))
      (fun x => (⟨e k, g (e k) (x (e k))⟩ : Σ i, B i)) =
      maxCorr (FiniteLaw.pi μ) (fun x => f (e k) (x (e k))) (fun x => g (e k) (x (e k))) := by
    refine maxCorr_congr _ (fun x x' => ?_) (fun x x' => ?_)
    · simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
    · simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
  rw [hc, maxCorr_eq_of_pairLaw _ (μ (e k)) _ _ (f (e k)) (g (e k)) (fun Φ =>
    expect_pi_eval μ (e k) (fun c => Φ (f (e k) c) (g (e k) c)))]
  exact hρ (e k)

omit [∀ i, DecidableEq (Y i)] [DecidableEq 𝔛] in
/-- **The maximal correlation of a product coupling** through the coordinates `s`. -/
theorem maxCorr_split_le (s : 𝔛 ≃ ∀ i, Y i) (C : FiniteLaw (𝔛 × 𝔛))
    (Cp : ∀ i, FiniteLaw (Y i × Y i))
    (hC : ∀ x y, C.weight (x, y) = ∏ i, (Cp i).weight (s x i, s y i)) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ i, maxCorr (Cp i) Prod.fst Prod.snd ≤ ρ) :
    maxCorr C Prod.fst Prod.snd ≤ ρ := by
  have h1 : maxCorr C Prod.fst Prod.snd = maxCorr C (fun q => s q.1) (fun q => s q.2) :=
    maxCorr_congr _ (fun q q' => s.apply_eq_iff_eq.symm) (fun q q' => s.apply_eq_iff_eq.symm)
  have h2 : maxCorr C (fun q => s q.1) (fun q => s q.2) =
      maxCorr (FiniteLaw.pi Cp) (fun z i => (z i).1) (fun z i => (z i).2) := by
    refine maxCorr_eq_of_pairLaw _ _ _ _ _ _ (fun Φ => ?_)
    rw [expect_split2 s C Cp hC]
    refine (FiniteLaw.pi Cp).expect_congr fun z => ?_
    simp [split2]
  rw [h1, h2]
  exact maxCorr_pi_le Cp (fun _ q => q.1) (fun _ q => q.2) hρ0 hρ

/-! ## `lem:row-comparison`(a),(c) on a product -/

/-- The block chi-square allowance `υ = (∏_i (1 + (R_i - 1)²) - 1)^{1/2}`. -/
noncomputable def chiAllow (R : ι → ℝ) : ℝ := √(∏ i, (1 + (R i - 1) ^ 2) - 1)

omit [DecidableEq ι] in
theorem chiAllow_nonneg (R : ι → ℝ) : 0 ≤ chiAllow R := Real.sqrt_nonneg _

omit [∀ i, DecidableEq (Y i)] in
/-- A density of mean one with values in `[R⁻¹, R]` has `‖g - 1‖² ≤ (R - 1)²`. -/
theorem chiSq_le_sq {Z : Type*} [Fintype Z] (ν : FiniteLaw Z) {g : Z → ℝ} {R : ℝ}
    (hR : 1 ≤ R) (hg1 : ν.expect g = 1) (hg : ∀ z, R⁻¹ ≤ g z ∧ g z ≤ R) :
    ν.expect (fun z => (g z - 1) ^ 2) ≤ (R - 1) ^ 2 := by
  refine (chiSq_le_of_range ν hg1 (fun z => (hg z).1) (fun z => (hg z).2)).trans ?_
  have hR0 : 0 < R := by linarith
  have hinv : R * R⁻¹ = 1 := mul_inv_cancel₀ hR0.ne'
  have hsq : 0 ≤ (R - 1) ^ 2 * R⁻¹ := by positivity
  have e : (R - 1) ^ 2 * R⁻¹ = R - 2 + R⁻¹ := by
    rw [show (R - 1) ^ 2 * R⁻¹ = R * (R * R⁻¹) - 2 * (R * R⁻¹) + R⁻¹ by ring, hinv]
    ring
  have h1 : 1 - R⁻¹ ≤ R - 1 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hR)]

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] [DecidableEq 𝔛] in
/-- **Exact marginals** (`lem:row-comparison`(a) with `r_L = r_R = 1`): if both marginals of `C` are
`ν` and `ρ(C) ≤ ρ`, then `|E_C[Φ(x) Ψ(y)] - E_ν Φ E_ν Ψ| ≤ ρ ‖Φ‖ ‖Ψ‖`. -/
theorem exact_rows (ν : FiniteLaw 𝔛) (C : FiniteLaw (𝔛 × 𝔛))
    (hC : HasMarginalDensities ν C (fun _ => 1) (fun _ => 1)) {ρ : ℝ}
    (hρC : maxCorr C Prod.fst Prod.snd ≤ ρ) (hρ0 : 0 ≤ ρ) (Φ Ψ : 𝔛 → ℝ) :
    |C.expect (fun q => Φ q.1 * Ψ q.2) - ν.expect Φ * ν.expect Ψ| ≤
      ρ * nrm ν Φ * nrm ν Ψ := by
  have h0 : Recentering.nrm ν (fun _ => (1 : ℝ) - 1) ≤ 0 := by
    unfold Recentering.nrm Recentering.ip
    simp
  have hb := row_comparison_norm' ν C hC (marginal_density_mean ν C hC).2 hρC hρ0
    (fun _ => zero_le_one) (fun _ => zero_le_one) (fun _ => le_rfl) (fun _ => le_rfl) h0 h0 Φ Ψ
  have e1 : ∀ f, Recentering.nrm ν f = nrm ν f := fun _ => rfl
  rw [e1, e1, mul_one, Real.sqrt_one, one_mul] at hb
  exact hb.trans (le_of_eq (by ring))

omit [DecidableEq 𝔛] in
/-- **`lem:row-comparison`(a),(c) on a product.** Let `ν`, `C` be products through `s` of the
references `νp i` and the couplings `Cp i`, whose marginal densities relative to `νp i` lie in
`[R_i⁻¹, R_i]` and whose maximal correlations are at most `ρ`. Then
`|E_C[Φ(x) Ψ(y)] - E_ν Φ E_ν Ψ| ≤ ((∏ R_i) ρ + 2υ + υ²) ‖Φ‖ ‖Ψ‖`, `υ = chiAllow R`. -/
theorem rows_of_product (s : 𝔛 ≃ ∀ i, Y i) (ν : FiniteLaw 𝔛) (C : FiniteLaw (𝔛 × 𝔛))
    (νp : ∀ i, FiniteLaw (Y i)) (Cp : ∀ i, FiniteLaw (Y i × Y i))
    (hν : ∀ x, ν.weight x = ∏ i, (νp i).weight (s x i))
    (hC : ∀ x y, C.weight (x, y) = ∏ i, (Cp i).weight (s x i, s y i))
    (rL rR : ∀ i, Y i → ℝ) (hr : ∀ i, HasMarginalDensities (νp i) (Cp i) (rL i) (rR i))
    (R : ι → ℝ) (hR1 : ∀ i, 1 ≤ R i) (hRL : ∀ i y, (R i)⁻¹ ≤ rL i y ∧ rL i y ≤ R i)
    (hRR : ∀ i y, (R i)⁻¹ ≤ rR i y ∧ rR i y ≤ R i)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ i, maxCorr (Cp i) Prod.fst Prod.snd ≤ ρ) (Φ Ψ : 𝔛 → ℝ) :
    |C.expect (fun q => Φ q.1 * Ψ q.2) - ν.expect Φ * ν.expect Ψ| ≤
      ((∏ i, R i) * ρ + 2 * chiAllow R + chiAllow R ^ 2) * nrm ν Φ * nrm ν Ψ := by
  set rL' : 𝔛 → ℝ := fun x => ∏ i, rL i (s x i)
  set rR' : 𝔛 → ℝ := fun x => ∏ i, rR i (s x i)
  have hR0 : ∀ i, 0 < R i := fun i => by linarith [hR1 i]
  have hpos : ∀ i y, 0 ≤ rL i y ∧ 0 ≤ rR i y := fun i y =>
    ⟨(inv_pos.mpr (hR0 i)).le.trans (hRL i y).1, (inv_pos.mpr (hR0 i)).le.trans (hRR i y).1⟩
  have hmarg := prodCoupling_marginals νp Cp rL rR hr
  -- the marginal densities of `C` relative to `ν`
  have hr' : HasMarginalDensities ν C rL' rR' := by
    constructor
    · intro φ
      rw [expect_split2 s C Cp hC, expect_split s ν νp hν]
      have h := hmarg.left (fun z => φ (s.symm z))
      unfold prodCoupling at h
      rw [FiniteLaw.expect_map] at h
      refine h.trans ((FiniteLaw.pi νp).expect_congr fun z => ?_)
      simp [rL']
    · intro φ
      rw [expect_split2 s C Cp hC, expect_split s ν νp hν]
      have h := hmarg.right (fun z => φ (s.symm z))
      unfold prodCoupling at h
      rw [FiniteLaw.expect_map] at h
      refine h.trans ((FiniteLaw.pi νp).expect_congr fun z => ?_)
      simp [rR']
  have hmean := marginal_density_mean ν C hr'
  -- the chi-square defects
  have hchi : ∀ r : ∀ i, Y i → ℝ, (∀ i, HasMarginalDensities (νp i) (Cp i) (r i) (rR i) ∨
      HasMarginalDensities (νp i) (Cp i) (rL i) (r i)) → (∀ i y, (R i)⁻¹ ≤ r i y ∧ r i y ≤ R i) →
      nrm ν (fun x => (∏ i, r i (s x i)) - 1) ≤ chiAllow R := by
    intro r hr1 hrR
    have hg1 : ∀ i, (νp i).expect (r i) = 1 := by
      intro i
      rcases hr1 i with h | h
      · exact (marginal_density_mean _ _ h).1
      · exact (marginal_density_mean _ _ h).2
    unfold nrm chiAllow ip
    apply Real.sqrt_le_sqrt
    rw [expect_split s ν νp hν]
    have e : (FiniteLaw.pi νp).expect (fun z => ((∏ i, r i (s (s.symm z) i)) - 1) *
        ((∏ i, r i (s (s.symm z) i)) - 1)) =
        (FiniteLaw.pi νp).expect (fun z => ((∏ i, r i (z i)) - 1) ^ 2) :=
      (FiniteLaw.pi νp).expect_congr fun z => by rw [s.apply_symm_apply]; ring
    rw [e]
    have ht := chiSq_tensor_eq νp r hg1
    have hle : ∏ i, (1 + (νp i).expect (fun y => (r i y - 1) ^ 2)) ≤
        ∏ i, (1 + (R i - 1) ^ 2) := by
      refine prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
      · have := (νp i).expect_nonneg (f := fun y => (r i y - 1) ^ 2) (fun y => sq_nonneg _)
        linarith
      · linarith [chiSq_le_sq (νp i) (hR1 i) (hg1 i) (hrR i)]
    linarith
  have hvL := hchi rL (fun i => Or.inl (hr i)) hRL
  have hvR := hchi rR (fun i => Or.inr (hr i)) hRR
  have hHL : ∀ x, rL' x ≤ ∏ i, R i := fun x =>
    prod_le_prod₀ (fun i _ => (hpos i _).1) (fun i _ => (hRL i _).2)
  have hHR : ∀ x, rR' x ≤ ∏ i, R i := fun x =>
    prod_le_prod₀ (fun i _ => (hpos i _).2) (fun i _ => (hRR i _).2)
  have hρC := maxCorr_split_le s C Cp hC hρ0 hρ
  have hb := row_comparison_norm' ν C hr' hmean.2 hρC hρ0
    (fun x => prod_nonneg fun i _ => (hpos i _).1) (fun x => prod_nonneg fun i _ => (hpos i _).2)
    hHL hHR hvL hvR Φ Ψ
  have hH0 : 0 ≤ ∏ i, R i := prod_nonneg fun i _ => (hR0 i).le
  rw [Real.sqrt_mul_self hH0] at hb
  have e1 : ∀ f, Recentering.nrm ν f = nrm ν f := fun _ => rfl
  rw [e1, e1] at hb
  exact hb.trans (le_of_eq (by ring))

end Product

end Sarkozy.BlockRows
