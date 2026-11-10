module

public import Sarkozy.SignedGram.Sector

@[expose] public section

/-!
# The bound on the sectors of at least two primes, from the prime centred norms (SGA)

`paper/sections/24_matching_mean.tex`, proof of `prop:signed-sides`(i), paragraph "Supports of at
least two primes": "the bound comes from the prime centred norms ... of the reference and ... of
the three components, through `lem:sector`(a) and `rem:signed-mixture-sectors`, the record being
a combination of three products with absolute coefficient sum `1 + t`".

* `condM C μ`: the Markov operator (conditional expectation) of a coupling `C` with marginals `μ`,
  `(T f)(b) = ∑_a C(b, a) f(a) / μ(b)`; `μ(b) T(b, a) = C(b, a)`;
* **`CentredNorm μ C δ`**: `‖T f‖_{L²(μ)} ≤ δ ‖f‖_{L²(μ)}` for `μ`-mean-zero `f` (the prime centred
  norm, the hypothesis of `lem:sector`(e));
* **`sector_dot_sq_le`**: for a product of nonnegative couplings with centred norms `δ_j` and
  `X ∈ H_S`, `⟨G, C X⟩² ≤ ‖G‖² (∏_{j∈S} δ_j)² ‖X‖²` (MX's `general_exact_support_decay`,
  `lem:sector`(e), and Cauchy–Schwarz);
* **`multiBound_of_centred`**: if every prime coupling of the old operator has centred norm
  `≤ ρ₀ ≤ 1` and every component `≤ ρ₁ ≤ 1`, then `MultiBound` holds on every sector of at least
  two coordinates whenever `ρ₀² + (∑_c |α_c|) ρ₁² ≤ σ`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.SignedGram

open Sarkozy.IndexSupport Sarkozy.Mixing

section Coord

variable {B : Type} [Fintype B] [DecidableEq B]

/-- **The Markov operator of a coupling** `C` with row sums `μ`: `T(b, a) = C(b, a) / μ(b)`
(and the row `μ` where `μ(b) = 0`). -/
noncomputable def condM (C : Matrix B B ℝ) (μ : B → ℝ) : Matrix B B ℝ :=
  fun b a => if μ b = 0 then μ a else C b a / μ b

omit [DecidableEq B] in
theorem mul_condM {C : Matrix B B ℝ} {μ : B → ℝ} (hC : ∀ a b, 0 ≤ C a b)
    (hrow : ∀ a, ∑ b, C a b = μ a) (b a : B) : μ b * condM C μ b a = C b a := by
  unfold condM
  by_cases hb : μ b = 0
  · have h := hrow b
    rw [hb] at h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => hC b a).mp h a (mem_univ a)
    simp [hb, hz]
  · simp only [hb, ↓reduceIte]
    field_simp

/-- **The prime centred norm** `‖T f‖_{L²(μ)} ≤ δ ‖f‖_{L²(μ)}` for `μ`-mean-zero `f`, with `T` the
Markov operator of the coupling `C` (the hypothesis of `lem:sector`(e)). -/
def CentredNorm (μ : B → ℝ) (C : Matrix B B ℝ) (δ : ℝ) : Prop :=
  ∀ f : B → ℝ, ∑ a, μ a * f a = 0 →
    ∑ b, μ b * (condM C μ *ᵥ f) b ^ 2 ≤ δ ^ 2 * ∑ a, μ a * f a ^ 2

end Coord

section Matrices

variable {K : Type} [Fintype K] [DecidableEq K] {A : K → Type} [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A j)] {m : ∀ j, A j → ℝ}

theorem SP_mul_SP (hm1 : ∀ j, ∑ a, m j a = 1) {l l' : K → Bool} (h : l' ≠ l) :
    SP m l' * SP m l = 0 := by
  unfold SP
  rw [piKron_mul]
  obtain ⟨j, hj⟩ : ∃ j, l' j ≠ l j := by
    by_contra h'
    exact h (funext fun j => not_not.mp fun hne => h' ⟨j, hne⟩)
  refine piKron_eq_zero j ?_
  rw [wProj_mul (hm1 j)]
  simp [hj]

/-- **`lem:sector`(e) on one sector**: for `X ∈ H_S`, `‖T X‖² ≤ (∏_{j∈S} δ_j)² ‖X‖²`, `T` the
product of the Markov operators of couplings with centred norms `δ_j`. -/
theorem sector_norm_sq_le (hm : ∀ j a, 0 ≤ m j a) (hm1 : ∀ j, ∑ a, m j a = 1)
    {C : ∀ j, Matrix (A j) (A j) ℝ} (hC : IsCoupling m C) (hCn : ∀ j a b, 0 ≤ C j a b)
    (δ : K → ℝ) (hδ : ∀ j, CentredNorm (m j) (C j) (δ j)) (l : K → Bool)
    (X₀ : (∀ j, A j) → ℝ) :
    ∑ b, prodW m b * (prodOp (fun j => condM (C j) (m j)) *ᵥ (SP m l *ᵥ X₀)) b ^ 2 ≤
      (∏ j ∈ univ.filter (fun j => l j = true), δ j) ^ 2 *
        ∑ a, prodW m a * (SP m l *ᵥ X₀) a ^ 2 := by
  have hsp : ∀ j, (fun _ : K => false) j = false →
      (∀ b, m j b ≠ 0 → ∑ a, condM (C j) (m j) b a = 1) ∧
        (∀ a, ∑ b, m j b * condM (C j) (m j) b a = m j a) := by
    intro j _
    refine ⟨fun b hb => ?_, fun a => ?_⟩
    · simp only [condM, hb, ↓reduceIte]
      rw [← Finset.sum_div, hC.row j b, div_self hb]
    · simp only [mul_condM (hCn j) (hC.row j)]
      exact hC.col j a
  have h := (general_exact_support_decay m m (fun j => condM (C j) (m j)) (fun _ => false) hm1 hm
    hsp δ (fun j _ f hf => hδ j f hf) (fun j h => absurd h (by simp)) (SP m l *ᵥ X₀)).2
  refine h.trans (le_of_eq ?_)
  have hcol : ∀ l', wSectorProj m (fun _ => false) l' *ᵥ (SP m l *ᵥ X₀) =
      if l' = l then SP m l *ᵥ X₀ else 0 := by
    intro l'
    change SP m l' *ᵥ (SP m l *ᵥ X₀) = _
    rw [Matrix.mulVec_mulVec]
    by_cases hl : l' = l
    · subst hl
      simp only [↓reduceIte, SP_mul_self m hm1]
    · simp only [hl, ↓reduceIte, SP_mul_SP hm1 hl, Matrix.zero_mulVec]
  simp only [hcol]
  rw [Finset.sum_eq_single l (fun l' _ hl' => by simp [hl']) (by simp)]
  simp only [↓reduceIte, Bool.false_eq_true]
  congr 1
  rw [← Finset.prod_pow, Finset.prod_filter]

/-- **The form of a product coupling on a sector**: for `X ∈ H_S`,
`⟨G, C X⟩² ≤ ‖G‖² (∏_{j∈S} δ_j)² ‖X‖²`. -/
theorem sector_dot_sq_le (hm : ∀ j a, 0 ≤ m j a) (hm1 : ∀ j, ∑ a, m j a = 1)
    {C : ∀ j, Matrix (A j) (A j) ℝ} (hC : IsCoupling m C) (hCn : ∀ j a b, 0 ≤ C j a b)
    (δ : K → ℝ) (hδ : ∀ j, CentredNorm (m j) (C j) (δ j)) (l : K → Bool)
    (G X₀ : (∀ j, A j) → ℝ) :
    (G ⬝ᵥ (piKron C *ᵥ (SP m l *ᵥ X₀))) ^ 2 ≤
      (G ⬝ᵥ (Matrix.diagonal (prodW m) *ᵥ G)) *
        ((∏ j ∈ univ.filter (fun j => l j = true), δ j) ^ 2 *
          ((SP m l *ᵥ X₀) ⬝ᵥ (Matrix.diagonal (prodW m) *ᵥ (SP m l *ᵥ X₀)))) := by
  set X := SP m l *ᵥ X₀
  set T := prodOp (fun j => condM (C j) (m j))
  have hent : ∀ b a, prodW m b * T b a = piKron C b a := by
    intro b a
    simp only [T, prodW, prodOp, piKron_apply, ← prod_mul_distrib]
    exact prod_congr rfl fun j _ => mul_condM (hCn j) (hC.row j) (b j) (a j)
  have hw : ∀ b, 0 ≤ prodW m b := fun b => prod_nonneg fun j _ => hm j (b j)
  have e1 : G ⬝ᵥ (piKron C *ᵥ X) = ∑ b, prodW m b * G b * (T *ᵥ X) b := by
    simp only [dotProduct, Matrix.mulVec]
    refine sum_congr rfl fun b _ => ?_
    have h : ∑ a, piKron C b a * X a = prodW m b * ∑ a, T b a * X a := by
      rw [Finset.mul_sum]
      exact sum_congr rfl fun a _ => by rw [← hent b a]; ring
    rw [h]
    ring
  have hsec := sector_norm_sq_le hm hm1 hC hCn δ hδ l X₀
  have e2 : ∀ Y : (∀ j, A j) → ℝ, Y ⬝ᵥ (Matrix.diagonal (prodW m) *ᵥ Y) =
      ∑ b, prodW m b * Y b ^ 2 := fun Y => by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact sum_congr rfl fun b _ => by ring
  rw [e1, e2, e2]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset (∀ j, A j))
    (r := fun b => prodW m b * G b *
    (T *ᵥ X) b) (f := fun b => prodW m b * G b ^ 2) (g := fun b => prodW m b * (T *ᵥ X) b ^ 2)
    (fun b _ => mul_nonneg (hw b) (sq_nonneg _)) (fun b _ => mul_nonneg (hw b) (sq_nonneg _))
    (fun b _ => le_of_eq (by ring))
  refine hcs.trans (mul_le_mul_of_nonneg_left hsec (sum_nonneg fun b _ =>
    mul_nonneg (hw b) (sq_nonneg _)))

theorem two_abs_le_of_sq_le {u x y δ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hδ : 0 ≤ δ)
    (h : u ^ 2 ≤ x * (δ ^ 2 * y)) : 2 * |u| ≤ δ * (x + y) := by
  have hu : |u| ≤ δ * (Real.sqrt x * Real.sqrt y) := by
    rw [← Real.sqrt_mul hx, ← Real.sqrt_sq hδ, ← Real.sqrt_mul (sq_nonneg _), ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h2 : 2 * (Real.sqrt x * Real.sqrt y) ≤ x + y := by
    have := two_mul_le_add_sq (Real.sqrt x) (Real.sqrt y)
    rw [Real.sq_sqrt hx, Real.sq_sqrt hy] at this
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h2 hδ]

omit [Fintype K] [DecidableEq K] [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)] in
theorem prod_filter_le {δ : K → ℝ} {ρ : ℝ} (hδ0 : ∀ j, 0 ≤ δ j) (hδ : ∀ j, δ j ≤ ρ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (s : Finset K) (hs : 2 ≤ s.card) : ∏ j ∈ s, δ j ≤ ρ ^ 2 := by
  calc ∏ j ∈ s, δ j ≤ ∏ _j ∈ s, ρ := prod_le_prod₀ (fun j _ => hδ0 j) (fun j _ => hδ j)
    _ = ρ ^ s.card := prod_const ρ
    _ ≤ ρ ^ 2 := pow_le_pow_of_le_one hρ0 hρ1 hs

/-- **`MultiBound` from the prime centred norms** (`prop:signed-sides`(i), "Supports of at least
two primes"): if every prime coupling of the old operator has centred norm `≤ ρ₀ ≤ 1` and every
prime component `≤ ρ₁ ≤ 1`, then on every sector of at least two coordinates the restrictions of
the old and new operators have norms `ρ₀²` and `(∑_c |α_c|) ρ₁²`; so `MultiBound` holds when
`ρ₀² + (∑_c |α_c|) ρ₁² ≤ σ`. -/
theorem multiBound_of_centred (hm : ∀ j a, 0 ≤ m j a) (hm1 : ∀ j, ∑ a, m j a = 1)
    {C₀ : ∀ j, Matrix (A j) (A j) ℝ} {P : Fin 3 → ∀ j, Matrix (A j) (A j) ℝ}
    (hC₀ : IsCoupling m C₀) (hP : ∀ c, IsCoupling m (P c)) (hC₀n : ∀ j a b, 0 ≤ C₀ j a b)
    (hPn : ∀ c j a b, 0 ≤ P c j a b) (α : Fin 3 → ℝ) {ρ₀ ρ₁ σ : ℝ} (hρ₀ : 0 ≤ ρ₀)
    (hρ₀1 : ρ₀ ≤ 1) (hρ₁ : 0 ≤ ρ₁) (hρ₁1 : ρ₁ ≤ 1)
    (h₀ : ∀ j, CentredNorm (m j) (C₀ j) ρ₀) (h₁ : ∀ c j, CentredNorm (m j) (P c j) ρ₁)
    (hσ : ρ₀ ^ 2 + (∑ c, |α c|) * ρ₁ ^ 2 ≤ σ) (l : K → Bool)
    (hl : 2 ≤ (univ.filter fun j => l j = true).card) :
    MultiBound m (piKron C₀) (∑ c, α c • piKron (P c)) σ l := by
  set S := univ.filter fun j => l j = true
  have hS₀ : ∏ j ∈ S, ρ₀ ≤ ρ₀ ^ 2 :=
    prod_filter_le (δ := fun _ => ρ₀) (fun _ => hρ₀) (fun _ => le_rfl) hρ₀ hρ₀1 S hl
  have hS₁ : ∏ j ∈ S, ρ₁ ≤ ρ₁ ^ 2 :=
    prod_filter_le (δ := fun _ => ρ₁) (fun _ => hρ₁) (fun _ => le_rfl) hρ₁ hρ₁1 S hl
  have hp₀ : 0 ≤ ∏ j ∈ S, ρ₀ := prod_nonneg fun _ _ => hρ₀
  have hp₁ : 0 ≤ ∏ j ∈ S, ρ₁ := prod_nonneg fun _ _ => hρ₁
  have hA : 0 ≤ ∑ c, |α c| := sum_nonneg fun c _ => abs_nonneg _
  refine ⟨∏ j ∈ S, ρ₀, (∑ c, |α c|) * ∏ j ∈ S, ρ₁, hp₀, mul_nonneg hA hp₁, ?_,
    fun φ ψ => ⟨?_, ?_⟩⟩
  · nlinarith [mul_le_mul_of_nonneg_left hS₁ hA]
  · -- the old operator
    have h := sector_dot_sq_le hm hm1 hC₀ hC₀n (fun _ => ρ₀) h₀ l (SP m l *ᵥ φ) φ
    have dF := diag_nonneg hm (SP m l *ᵥ φ)
    have h2 := two_abs_le_of_sq_le dF dF hp₀ h
    linarith
  · -- the new operator, component by component
    have dF := diag_nonneg hm (SP m l *ᵥ φ)
    have dG := diag_nonneg hm (SP m l *ᵥ ψ)
    have hc : ∀ c, 2 * |(SP m l *ᵥ φ) ⬝ᵥ (piKron (P c) *ᵥ (SP m l *ᵥ ψ))| ≤
        (∏ j ∈ S, ρ₁) * ((SP m l *ᵥ φ) ⬝ᵥ (Matrix.diagonal (prodW m) *ᵥ (SP m l *ᵥ φ)) +
          (SP m l *ᵥ ψ) ⬝ᵥ (Matrix.diagonal (prodW m) *ᵥ (SP m l *ᵥ ψ))) := fun c =>
      two_abs_le_of_sq_le dF dG hp₁
        (sector_dot_sq_le hm hm1 (hP c) (hPn c) (fun _ => ρ₁) (h₁ c) l (SP m l *ᵥ φ) ψ)
    rw [Matrix.sum_mulVec, dotProduct_sum]
    calc 2 * |∑ c, (SP m l *ᵥ φ) ⬝ᵥ ((α c • piKron (P c)) *ᵥ (SP m l *ᵥ ψ))|
        ≤ 2 * ∑ c, |(SP m l *ᵥ φ) ⬝ᵥ ((α c • piKron (P c)) *ᵥ (SP m l *ᵥ ψ))| :=
          mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by norm_num)
      _ = ∑ c, |α c| * (2 * |(SP m l *ᵥ φ) ⬝ᵥ (piKron (P c) *ᵥ (SP m l *ᵥ ψ))|) := by
          rw [Finset.mul_sum]
          refine sum_congr rfl fun c _ => ?_
          rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, abs_mul]
          ring
      _ ≤ ∑ c, |α c| * ((∏ j ∈ S, ρ₁) *
            ((SP m l *ᵥ φ) ⬝ᵥ (Matrix.diagonal (prodW m) *ᵥ (SP m l *ᵥ φ)) +
              (SP m l *ᵥ ψ) ⬝ᵥ (Matrix.diagonal (prodW m) *ᵥ (SP m l *ᵥ ψ)))) :=
          sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hc c) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring

end Matrices

end Sarkozy.SignedGram
