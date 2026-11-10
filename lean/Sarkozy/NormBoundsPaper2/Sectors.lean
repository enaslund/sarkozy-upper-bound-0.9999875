module

public import Sarkozy.SignedGram.SectorNorm

@[expose] public section

/-!
# Norms of changes on a product space, sector by sector (NB2)

`paper/sections/21_middle_records.tex`, proof of `lem:merge-repair`, paragraph "Products over
primes": "Every operator is Markov in the same actual half law, so it preserves the orthogonal
decomposition by exact nonconstant prime support. … On singleton supports use the prime bounds. On
a support of size at least two, the mirror difference has symmetric norm at most `α_b² + d_b²` …
Further support factors are contractions. … Taking the maximum over the orthogonal supports proves
the block claims." This is `lem:sector`(a),(e) for block differences.

On `∏_j A_j` with probability weights `m_j` (SGA's setting, `Sarkozy.SignedGram.Sector`):

* `ip m φ ψ = ⟨φ, ψ⟩_{L²(⊗ m_j)}`; `ip_decomp` (Pythagoras over the sectors);
* `SP_single_eq`, `ip_one_SP`: on a sector `S = {i}`, `P_S φ` is a function `u(x_i)` of `x_i` with
  `E_{m_i} u = 0`;
* **`bilin_le_of_sectors`**: a form that splits over the sectors and has norm `≤ c` on each has
  norm `≤ c`;
* **`change_le`** (the block claim of `lem:merge-repair`): for couplings `P_j`, `C_j` with
  marginals `m_j` and the form `B(φ, ψ) = α₁ ⟨φ, P ψ⟩ + α₂ ⟨ψ, P φ⟩ − β ⟨φ, C ψ⟩`
  (`α₁ + α₂ = β`; `(½, ½, 1)` is the symmetric part of `P − C`, `(½, −½, 0)` the skew part of
  `P` when `C` is symmetric), if every prime form on mean-zero functions is `≤ e` and the prime
  centred norms are `ρ ≤ 1`, `d ≤ 1` with `(|α₁| + |α₂|) ρ² + |β| d² ≤ e`, then `|B| ≤ e`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper2

open Sarkozy.IndexSupport Sarkozy.Mixing Sarkozy.SignedGram

section Matrices

variable {K : Type} [Fintype K] [DecidableEq K] {A : K → Type} [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A j)] {m : ∀ j, A j → ℝ}

/-- The inner product of `L²(⊗_j m_j)`. -/
noncomputable def ip (m : ∀ j, A j → ℝ) (φ ψ : (∀ j, A j) → ℝ) : ℝ :=
  φ ⬝ᵥ (Matrix.diagonal (prodW m) *ᵥ ψ)

omit [DecidableEq K] [∀ j, Fintype (A j)] in
theorem diagonal_prodW_eq :
    Matrix.diagonal (prodW m) = piKron (fun j => Matrix.diagonal (m j)) := by
  ext x y
  simp only [piKron_apply, Matrix.diagonal_apply, prodW]
  by_cases h : x = y
  · subst h
    simp
  · simp only [h, ↓reduceIte]
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := Function.ne_iff.mp h
    exact (prod_eq_zero (mem_univ j) (by simp [hj])).symm

theorem ip_nonneg (hm : ∀ j a, 0 ≤ m j a) (φ : (∀ j, A j) → ℝ) : 0 ≤ ip m φ φ :=
  diag_nonneg hm φ

/-- **Pythagoras over the sectors**: `⟨φ, ψ⟩ = ∑_S ⟨P_S φ, P_S ψ⟩`. -/
theorem ip_decomp (hm1 : ∀ j, ∑ a, m j a = 1) (φ ψ : (∀ j, A j) → ℝ) :
    ip m φ ψ = ∑ l, ip m (SP m l *ᵥ φ) (SP m l *ᵥ ψ) := by
  unfold ip
  rw [diagonal_prodW_eq]
  exact dot_decomp hm1 (fun l => SP_comm diagonal_coupling l) φ ψ

/-- **The form bound from the sectors.** -/
theorem bilin_le_of_sectors (hm : ∀ j a, 0 ≤ m j a) (hm1 : ∀ j, ∑ a, m j a = 1)
    (B : ((∀ j, A j) → ℝ) → ((∀ j, A j) → ℝ) → ℝ)
    (hdec : ∀ φ ψ, B φ ψ = ∑ l, B (SP m l *ᵥ φ) (SP m l *ᵥ ψ)) {c : ℝ} (hc : 0 ≤ c)
    (hsec : ∀ l φ ψ, |B (SP m l *ᵥ φ) (SP m l *ᵥ ψ)| ≤
      c * Real.sqrt (ip m (SP m l *ᵥ φ) (SP m l *ᵥ φ)) *
        Real.sqrt (ip m (SP m l *ᵥ ψ) (SP m l *ᵥ ψ)))
    (φ ψ : (∀ j, A j) → ℝ) :
    |B φ ψ| ≤ c * Real.sqrt (ip m φ φ) * Real.sqrt (ip m ψ ψ) := by
  rw [hdec]
  set a := fun l => Real.sqrt (ip m (SP m l *ᵥ φ) (SP m l *ᵥ φ))
  set b := fun l => Real.sqrt (ip m (SP m l *ᵥ ψ) (SP m l *ᵥ ψ))
  have h1 : |∑ l, B (SP m l *ᵥ φ) (SP m l *ᵥ ψ)| ≤ ∑ l, c * (a l * b l) :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ => (hsec l φ ψ).trans (le_of_eq (by ring)))
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt univ a b
  have ha : ∑ l, a l ^ 2 = ip m φ φ := by
    rw [ip_decomp hm1 φ φ]
    exact sum_congr rfl fun l _ => Real.sq_sqrt (ip_nonneg hm _)
  have hb : ∑ l, b l ^ 2 = ip m ψ ψ := by
    rw [ip_decomp hm1 ψ ψ]
    exact sum_congr rfl fun l _ => Real.sq_sqrt (ip_nonneg hm _)
  rw [ha, hb] at hcs
  rw [← mul_sum] at h1
  calc _ ≤ c * ∑ l, a l * b l := h1
    _ ≤ c * (Real.sqrt (ip m φ φ) * Real.sqrt (ip m ψ ψ)) := mul_le_mul_of_nonneg_left hcs hc
    _ = _ := by ring

/-- On a sector `S = {i}`, `P_S φ` is a function of `x_i`. -/
theorem SP_single_eq (l : K → Bool) {i : K} (hl : univ.filter (fun j => l j = true) = {i})
    (x₀ : ∀ j, A j) (φ : (∀ j, A j) → ℝ) :
    (SP m l *ᵥ φ) = fun x => (fun a => (SP m l *ᵥ φ) (Function.update x₀ i a)) (x i) := by
  funext x
  refine SP_congr l φ fun j hj => ?_
  have hj' : j ∈ univ.filter (fun j => l j = true) := by simp [hj]
  rw [hl, mem_singleton] at hj'
  subst hj'
  simp

/-- On the empty sector, `P_∅ φ` is constant. -/
theorem SP_empty_eq (l : K → Bool) (hl : univ.filter (fun j => l j = true) = ∅)
    (x₀ : ∀ j, A j) (φ : (∀ j, A j) → ℝ) :
    (SP m l *ᵥ φ) = fun _ => (SP m l *ᵥ φ) x₀ := by
  funext x
  refine SP_congr l φ fun j hj => ?_
  have hj' : j ∈ univ.filter (fun j => l j = true) := by simp [hj]
  rw [hl] at hj'
  exact absurd hj' (notMem_empty j)

theorem SP_false_one (hm1 : ∀ j, ∑ a, m j a = 1) :
    SP m (fun _ => false) *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext x
  simp only [SP, wProj, Matrix.mulVec, dotProduct, piKron_apply, mul_one, Bool.false_eq_true,
    ↓reduceIte, avgMatrix]
  rw [← Fintype.prod_sum]
  simp [hm1]

/-- A vector of a nonconstant sector has mean zero. -/
theorem ip_one_SP (hm1 : ∀ j, ∑ a, m j a = 1) {l : K → Bool} (hl : l ≠ fun _ => false)
    (φ : (∀ j, A j) → ℝ) : ip m (fun _ => 1) (SP m l *ᵥ φ) = 0 := by
  unfold ip
  rw [← SP_false_one hm1, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, diagonal_prodW_eq,
    SP_comm diagonal_coupling (fun _ => false), Matrix.mul_assoc, SP_mul_SP hm1 (Ne.symm hl),
    Matrix.mul_zero, Matrix.zero_mulVec, zero_dotProduct]

omit [DecidableEq K] in
theorem filter_nonempty_of_ne {l : K → Bool} (hl : l ≠ fun _ => false) :
    (univ.filter fun j => l j = true).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  refine hl (funext fun j => ?_)
  by_contra hj
  have : j ∈ univ.filter (fun j => l j = true) := by simpa using hj
  rw [h] at this
  exact notMem_empty j this

theorem ip_single (hm1 : ∀ j, ∑ a, m j a = 1) (i : K) (u v : A i → ℝ) :
    ip m (fun x => u (x i)) (fun x => v (x i)) = ∑ a, m i a * u a * v a := by
  unfold ip
  rw [diagonal_prodW_eq, dot_piKron_single diagonal_coupling hm1 i u v]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact sum_congr rfl fun a _ => by ring

theorem abs_le_of_sq_le' {u x y δ : ℝ} (hx : 0 ≤ x) (hδ : 0 ≤ δ)
    (h : u ^ 2 ≤ x * (δ ^ 2 * y)) : |u| ≤ δ * Real.sqrt x * Real.sqrt y := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hδ, ← Real.sqrt_mul (sq_nonneg _),
    ← Real.sqrt_mul (mul_nonneg (sq_nonneg _) hx)]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- The form `α₁ ⟨φ, P ψ⟩ + α₂ ⟨ψ, P φ⟩ − β ⟨φ, C ψ⟩` of two product couplings. -/
noncomputable def chg (P C : ∀ j, Matrix (A j) (A j) ℝ) (α₁ α₂ β : ℝ)
    (φ ψ : (∀ j, A j) → ℝ) : ℝ :=
  α₁ * (φ ⬝ᵥ (piKron P *ᵥ ψ)) + α₂ * (ψ ⬝ᵥ (piKron P *ᵥ φ)) - β * (φ ⬝ᵥ (piKron C *ᵥ ψ))

/-- The one-prime form. -/
noncomputable def chg1 {B : Type} [Fintype B] (P C : Matrix B B ℝ) (α₁ α₂ β : ℝ)
    (u v : B → ℝ) : ℝ :=
  α₁ * (u ⬝ᵥ (P *ᵥ v)) + α₂ * (v ⬝ᵥ (P *ᵥ u)) - β * (u ⬝ᵥ (C *ᵥ v))

/-- **`lem:merge-repair`, products over primes**: the block form `B` of two product couplings
from the prime forms on mean-zero functions (singleton supports) and the prime centred norms
(supports of at least two primes; the empty support contributes `(α₁ + α₂ − β) ab = 0`). -/
theorem change_le (hm : ∀ j a, 0 ≤ m j a) (hm1 : ∀ j, ∑ a, m j a = 1)
    {P C : ∀ j, Matrix (A j) (A j) ℝ} (hP : IsCoupling m P) (hC : IsCoupling m C)
    (hPn : ∀ j a b, 0 ≤ P j a b) (hCn : ∀ j a b, 0 ≤ C j a b) {α₁ α₂ β : ℝ}
    (hαβ : α₁ + α₂ = β) {ρ d e : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hρ : ∀ j, CentredNorm (m j) (P j) ρ) (hd : ∀ j, CentredNorm (m j) (C j) d) (he : 0 ≤ e)
    (hmulti : (|α₁| + |α₂|) * ρ ^ 2 + |β| * d ^ 2 ≤ e)
    (hsingle : ∀ j (u v : A j → ℝ), ∑ a, m j a * u a = 0 → ∑ a, m j a * v a = 0 →
      |chg1 (P j) (C j) α₁ α₂ β u v| ≤
        e * Real.sqrt (∑ a, m j a * u a ^ 2) * Real.sqrt (∑ a, m j a * v a ^ 2))
    (x₀ : ∀ j, A j) (φ ψ : (∀ j, A j) → ℝ) :
    |chg P C α₁ α₂ β φ ψ| ≤ e * Real.sqrt (ip m φ φ) * Real.sqrt (ip m ψ ψ) := by
  refine bilin_le_of_sectors hm hm1 (chg P C α₁ α₂ β) (fun φ ψ => ?_) he (fun l φ ψ => ?_) φ ψ
  · -- the form splits over the sectors
    unfold chg
    rw [dot_decomp hm1 (fun l => SP_comm hP l) φ ψ, dot_decomp hm1 (fun l => SP_comm hP l) ψ φ,
      dot_decomp hm1 (fun l => SP_comm hC l) φ ψ, mul_sum, mul_sum, mul_sum, ← sum_add_distrib,
      ← sum_sub_distrib]
  set S := univ.filter fun j => l j = true
  set f := SP m l *ᵥ φ
  set g := SP m l *ᵥ ψ
  have hf0 := ip_nonneg hm f
  have hg0 := ip_nonneg hm g
  rcases Nat.lt_or_ge S.card 2 with hS | hS
  · rcases Nat.lt_or_ge S.card 1 with hS0 | hS1
    · -- the empty sector
      have hSe : S = ∅ := card_eq_zero.mp (by omega)
      have ef : f = fun _ => f x₀ := SP_empty_eq l hSe x₀ φ
      have eg : g = fun _ => g x₀ := SP_empty_eq l hSe x₀ ψ
      have hz : chg P C α₁ α₂ β f g = 0 := by
        unfold chg
        rw [ef, eg, dot_piKron_const hP hm1, dot_piKron_const hP hm1, dot_piKron_const hC hm1,
          ← hαβ]
        ring
      rw [hz, abs_zero]
      exact mul_nonneg (mul_nonneg he (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    · -- a singleton sector
      obtain ⟨i, hi⟩ := card_eq_one.mp (show S.card = 1 by omega)
      have hl : l ≠ fun _ => false := by
        intro h
        have : i ∈ S := by rw [hi]; exact mem_singleton_self i
        simp [S, h] at this
      set u := fun a => f (Function.update x₀ i a)
      set v := fun a => g (Function.update x₀ i a)
      have ef : f = fun x => u (x i) := SP_single_eq l hi x₀ φ
      have eg : g = fun x => v (x i) := SP_single_eq l hi x₀ ψ
      have hu : ∑ a, m i a * u a = 0 := by
        have h := ip_one_SP hm1 hl φ
        change ip m (fun _ => 1) f = 0 at h
        rw [ef, show (fun _ : ∀ j, A j => (1 : ℝ)) = fun x => (fun _ : A i => (1 : ℝ)) (x i)
          from rfl, ip_single hm1 i (fun _ => (1 : ℝ)) u] at h
        simpa using h
      have hv : ∑ a, m i a * v a = 0 := by
        have h := ip_one_SP hm1 hl ψ
        change ip m (fun _ => 1) g = 0 at h
        rw [eg, show (fun _ : ∀ j, A j => (1 : ℝ)) = fun x => (fun _ : A i => (1 : ℝ)) (x i)
          from rfl, ip_single hm1 i (fun _ => (1 : ℝ)) v] at h
        simpa using h
      have h1 := hsingle i u v hu hv
      have hc : chg P C α₁ α₂ β f g = chg1 (P i) (C i) α₁ α₂ β u v := by
        unfold chg chg1
        rw [ef, eg, dot_piKron_single hP hm1, dot_piKron_single hP hm1, dot_piKron_single hC hm1]
      have hnu : ip m f f = ∑ a, m i a * u a ^ 2 := by
        rw [ef, ip_single hm1]
        exact sum_congr rfl fun a _ => by ring
      have hnv : ip m g g = ∑ a, m i a * v a ^ 2 := by
        rw [eg, ip_single hm1]
        exact sum_congr rfl fun a _ => by ring
      rw [hc, hnu, hnv]
      exact h1
  · -- a sector of at least two coordinates
    have hpρ : ∏ j ∈ S, ρ ≤ ρ ^ 2 :=
      prod_filter_le (δ := fun _ => ρ) (fun _ => hρ0) (fun _ => le_rfl) hρ0 hρ1 S hS
    have hpd : ∏ j ∈ S, d ≤ d ^ 2 :=
      prod_filter_le (δ := fun _ => d) (fun _ => hd0) (fun _ => le_rfl) hd0 hd1 S hS
    have hρS : 0 ≤ ∏ j ∈ S, ρ := prod_nonneg fun _ _ => hρ0
    have hdS : 0 ≤ ∏ j ∈ S, d := prod_nonneg fun _ _ => hd0
    have t1 : |f ⬝ᵥ (piKron P *ᵥ g)| ≤ (∏ j ∈ S, ρ) * Real.sqrt (ip m f f) *
        Real.sqrt (ip m g g) :=
      abs_le_of_sq_le' hf0 hρS (sector_dot_sq_le hm hm1 hP hPn (fun _ => ρ) hρ l f ψ)
    have t2 : |g ⬝ᵥ (piKron P *ᵥ f)| ≤ (∏ j ∈ S, ρ) * Real.sqrt (ip m g g) *
        Real.sqrt (ip m f f) :=
      abs_le_of_sq_le' hg0 hρS (sector_dot_sq_le hm hm1 hP hPn (fun _ => ρ) hρ l g φ)
    have t3 : |f ⬝ᵥ (piKron C *ᵥ g)| ≤ (∏ j ∈ S, d) * Real.sqrt (ip m f f) *
        Real.sqrt (ip m g g) :=
      abs_le_of_sq_le' hf0 hdS (sector_dot_sq_le hm hm1 hC hCn (fun _ => d) hd l f ψ)
    set F := Real.sqrt (ip m f f)
    set G := Real.sqrt (ip m g g)
    have hF : 0 ≤ F := Real.sqrt_nonneg _
    have hG : 0 ≤ G := Real.sqrt_nonneg _
    have hFG : 0 ≤ F * G := mul_nonneg hF hG
    unfold chg
    calc |α₁ * (f ⬝ᵥ (piKron P *ᵥ g)) + α₂ * (g ⬝ᵥ (piKron P *ᵥ f)) -
          β * (f ⬝ᵥ (piKron C *ᵥ g))|
        ≤ |α₁| * |f ⬝ᵥ (piKron P *ᵥ g)| + |α₂| * |g ⬝ᵥ (piKron P *ᵥ f)| +
          |β| * |f ⬝ᵥ (piKron C *ᵥ g)| := by
          rw [← abs_mul, ← abs_mul, ← abs_mul]
          exact (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ |α₁| * (ρ ^ 2 * (F * G)) + |α₂| * (ρ ^ 2 * (F * G)) + |β| * (d ^ 2 * (F * G)) := by
          refine add_le_add (add_le_add ?_ ?_) ?_
          · refine mul_le_mul_of_nonneg_left (t1.trans ?_) (abs_nonneg _)
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right hpρ hFG
          · refine mul_le_mul_of_nonneg_left (t2.trans ?_) (abs_nonneg _)
            rw [mul_assoc, mul_comm G F]
            exact mul_le_mul_of_nonneg_right hpρ hFG
          · refine mul_le_mul_of_nonneg_left (t3.trans ?_) (abs_nonneg _)
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right hpd hFG
      _ = ((|α₁| + |α₂|) * ρ ^ 2 + |β| * d ^ 2) * (F * G) := by ring
      _ ≤ e * (F * G) := mul_le_mul_of_nonneg_right hmulti hFG
      _ = e * F * G := by ring

end Matrices

end Sarkozy.NormBoundsPaper2
