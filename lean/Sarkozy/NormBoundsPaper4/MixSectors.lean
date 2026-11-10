module

public import Sarkozy.NormBoundsPaper2.Sectors

@[expose] public section

/-!
# Norms of a signed mixture of product couplings, sector by sector (FD)

`paper/sections/21_middle_records.tex`, proof of `prop:signed-bounds`, Step 4 ("Every component
and the reference are couplings with both marginals `m_{0,p}`, so their Markov operators are
sector-preserving … By `rem:signed-mixture-sectors`, `D_t` vanishes on the empty sector, is
`D_{t,p}` on the sector `{p}`, and on a sector `S` with `|S| ≥ 2` has norm at most
`(1 + t) ∏_{p∈S} c_+(p) r_p + ∏_{p∈S} (Γ_A + e_o(p) r_p) r_p ≤ c_{≥2}/b` … all these norms are
maxima over the sectors"); `paper/sections/06_lifts_sectors.tex`, `rem:signed-mixture-sectors`.

On `∏_j A_j` with probability weights `m_j`:

* `mixChg P C w α₁ α₂ β φ ψ = ∑_c w_c (α₁ ⟨φ, ⊗P_c ψ⟩ + α₂ ⟨ψ, ⊗P_c φ⟩) − β ⟨φ, ⊗C ψ⟩`, the
  form of a **signed sum of three products** `∑_c w_c ⊗_j P_{c,j}` (the signed sum taken after
  the products, as in `def:record:mixture`(c)) against one product `⊗_j C_j`; with
  `(α₁, α₂, β) = (½, ½, 1)` it is the symmetric part of the difference, with `(½, −½, 0)` the skew
  part of the new record;
* `mixChg1`: the same at one coordinate;
* **`mix_change_le`**: if `(∑ w)(α₁ + α₂) = β`, the one-coordinate forms on mean-zero functions are
  `≤ e`, and the prime centred norms are `ρ ≤ 1` (every `P_{c,j}`) and `d ≤ 1` (every `C_j`) with
  `(∑|w_c|)(|α₁| + |α₂|) ρ² + |β| d² ≤ e`, then `|mixChg| ≤ e ‖φ‖ ‖ψ‖`. This extends NB2's
  `change_le` (one product on each side) to the signed mixture of the fold records.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper4

open Sarkozy.IndexSupport Sarkozy.Mixing Sarkozy.SignedGram
open Sarkozy.NormBoundsPaper2 (ip ip_nonneg bilin_le_of_sectors SP_single_eq SP_empty_eq
  ip_one_SP ip_single abs_le_of_sq_le')

section Matrices

variable {K : Type} [Fintype K] [DecidableEq K] {A : K → Type} [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A j)] {m : ∀ j, A j → ℝ}

/-- The form of the signed mixture `∑_c w_c ⊗P_c` against the product `⊗C`. -/
noncomputable def mixChg (P : Fin 3 → ∀ j, Matrix (A j) (A j) ℝ) (C : ∀ j, Matrix (A j) (A j) ℝ)
    (w : Fin 3 → ℝ) (α₁ α₂ β : ℝ) (φ ψ : (∀ j, A j) → ℝ) : ℝ :=
  ∑ c, w c * (α₁ * (φ ⬝ᵥ (piKron (P c) *ᵥ ψ)) + α₂ * (ψ ⬝ᵥ (piKron (P c) *ᵥ φ))) -
    β * (φ ⬝ᵥ (piKron C *ᵥ ψ))

/-- The one-coordinate form of the signed mixture. -/
noncomputable def mixChg1 {B : Type} [Fintype B] (P : Fin 3 → Matrix B B ℝ) (C : Matrix B B ℝ)
    (w : Fin 3 → ℝ) (α₁ α₂ β : ℝ) (u v : B → ℝ) : ℝ :=
  ∑ c, w c * (α₁ * (u ⬝ᵥ (P c *ᵥ v)) + α₂ * (v ⬝ᵥ (P c *ᵥ u))) - β * (u ⬝ᵥ (C *ᵥ v))

/-- **`prop:signed-bounds`, Step 4** (with `rem:signed-mixture-sectors`, `lem:sector`(a),(e)): the
block form of a signed mixture of product couplings against a product coupling, from the
one-coordinate forms on mean-zero functions (singleton sectors) and the prime centred norms
(sectors of at least two coordinates); the empty sector contributes
`((∑ w)(α₁ + α₂) − β) a b = 0`. -/
theorem mix_change_le (hm : ∀ j a, 0 ≤ m j a) (hm1 : ∀ j, ∑ a, m j a = 1)
    {P : Fin 3 → ∀ j, Matrix (A j) (A j) ℝ} {C : ∀ j, Matrix (A j) (A j) ℝ}
    (hP : ∀ c, IsCoupling m (P c)) (hC : IsCoupling m C)
    (hPn : ∀ c j a b, 0 ≤ P c j a b) (hCn : ∀ j a b, 0 ≤ C j a b) {w : Fin 3 → ℝ}
    {α₁ α₂ β : ℝ} (hαβ : (∑ c, w c) * (α₁ + α₂) = β) {ρ d e : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hρ : ∀ c j, CentredNorm (m j) (P c j) ρ)
    (hd : ∀ j, CentredNorm (m j) (C j) d) (he : 0 ≤ e)
    (hmulti : (∑ c, |w c|) * (|α₁| + |α₂|) * ρ ^ 2 + |β| * d ^ 2 ≤ e)
    (hsingle : ∀ j (u v : A j → ℝ), ∑ a, m j a * u a = 0 → ∑ a, m j a * v a = 0 →
      |mixChg1 (fun c => P c j) (C j) w α₁ α₂ β u v| ≤
        e * Real.sqrt (∑ a, m j a * u a ^ 2) * Real.sqrt (∑ a, m j a * v a ^ 2))
    (x₀ : ∀ j, A j) (φ ψ : (∀ j, A j) → ℝ) :
    |mixChg P C w α₁ α₂ β φ ψ| ≤ e * Real.sqrt (ip m φ φ) * Real.sqrt (ip m ψ ψ) := by
  have hdP : ∀ c (φ ψ : (∀ j, A j) → ℝ), φ ⬝ᵥ (piKron (P c) *ᵥ ψ) =
      ∑ l, (SP m l *ᵥ φ) ⬝ᵥ (piKron (P c) *ᵥ (SP m l *ᵥ ψ)) :=
    fun c φ ψ => dot_decomp hm1 (fun l => SP_comm (hP c) l) φ ψ
  refine bilin_le_of_sectors hm hm1 (mixChg P C w α₁ α₂ β) (fun φ ψ => ?_) he
    (fun l φ ψ => ?_) φ ψ
  · -- the form splits over the sectors
    unfold mixChg
    have e1 : ∑ c, w c * (α₁ * (φ ⬝ᵥ (piKron (P c) *ᵥ ψ)) + α₂ * (ψ ⬝ᵥ (piKron (P c) *ᵥ φ))) =
        ∑ l, ∑ c, w c * (α₁ * ((SP m l *ᵥ φ) ⬝ᵥ (piKron (P c) *ᵥ (SP m l *ᵥ ψ))) +
          α₂ * ((SP m l *ᵥ ψ) ⬝ᵥ (piKron (P c) *ᵥ (SP m l *ᵥ φ)))) := by
      rw [Finset.sum_comm]
      refine sum_congr rfl fun c _ => ?_
      rw [hdP c φ ψ, hdP c ψ φ, mul_sum, mul_sum, ← sum_add_distrib, mul_sum]
    rw [e1, dot_decomp hm1 (fun l => SP_comm hC l) φ ψ, mul_sum, ← sum_sub_distrib]
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
      have hconst : ∀ c (a b' : ℝ), (fun _ : ∀ j, A j => a) ⬝ᵥ (piKron (P c) *ᵥ fun _ => b') =
          a * b' := fun c => dot_piKron_const (hP c) hm1
      have hz : mixChg P C w α₁ α₂ β f g = 0 := by
        unfold mixChg
        rw [ef, eg]
        simp only [hconst, dot_piKron_const hC hm1]
        have hs : ∑ c, w c * (α₁ * (f x₀ * g x₀) + α₂ * (g x₀ * f x₀)) =
            (∑ c, w c) * (α₁ + α₂) * (f x₀ * g x₀) := by
          rw [sum_mul, sum_mul]
          exact sum_congr rfl fun c _ => by ring
        rw [hs, hαβ]
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
      have hsing : ∀ c (u' v' : A i → ℝ),
          (fun x : ∀ j, A j => u' (x i)) ⬝ᵥ (piKron (P c) *ᵥ fun y => v' (y i)) =
            u' ⬝ᵥ (P c i *ᵥ v') := fun c => dot_piKron_single (hP c) hm1 i
      have hc : mixChg P C w α₁ α₂ β f g = mixChg1 (fun c => P c i) (C i) w α₁ α₂ β u v := by
        unfold mixChg mixChg1
        rw [ef, eg]
        simp only [hsing, dot_piKron_single hC hm1]
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
    set F := Real.sqrt (ip m f f)
    set G := Real.sqrt (ip m g g)
    have hF : 0 ≤ F := Real.sqrt_nonneg _
    have hG : 0 ≤ G := Real.sqrt_nonneg _
    have hFG : 0 ≤ F * G := mul_nonneg hF hG
    have t1 : ∀ c, |f ⬝ᵥ (piKron (P c) *ᵥ g)| ≤ ρ ^ 2 * (F * G) := fun c => by
      have h : |f ⬝ᵥ (piKron (P c) *ᵥ g)| ≤ (∏ j ∈ S, ρ) * F * G := abs_le_of_sq_le' hf0 hρS
        (sector_dot_sq_le hm hm1 (hP c) (hPn c) (fun _ => ρ) (hρ c) l f ψ)
      refine h.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hpρ hFG
    have t2 : ∀ c, |g ⬝ᵥ (piKron (P c) *ᵥ f)| ≤ ρ ^ 2 * (F * G) := fun c => by
      have h : |g ⬝ᵥ (piKron (P c) *ᵥ f)| ≤ (∏ j ∈ S, ρ) * G * F := abs_le_of_sq_le' hg0 hρS
        (sector_dot_sq_le hm hm1 (hP c) (hPn c) (fun _ => ρ) (hρ c) l g φ)
      refine h.trans ?_
      rw [mul_assoc, mul_comm G F]
      exact mul_le_mul_of_nonneg_right hpρ hFG
    have t3 : |f ⬝ᵥ (piKron C *ᵥ g)| ≤ d ^ 2 * (F * G) := by
      have h : |f ⬝ᵥ (piKron C *ᵥ g)| ≤ (∏ j ∈ S, d) * F * G := abs_le_of_sq_le' hf0 hdS
        (sector_dot_sq_le hm hm1 hC hCn (fun _ => d) hd l f ψ)
      refine h.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hpd hFG
    have tc : ∀ c, |w c * (α₁ * (f ⬝ᵥ (piKron (P c) *ᵥ g)) + α₂ * (g ⬝ᵥ (piKron (P c) *ᵥ f)))| ≤
        |w c| * ((|α₁| + |α₂|) * ρ ^ 2 * (F * G)) := fun c => by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |α₁ * (f ⬝ᵥ (piKron (P c) *ᵥ g)) + α₂ * (g ⬝ᵥ (piKron (P c) *ᵥ f))|
          ≤ |α₁| * |f ⬝ᵥ (piKron (P c) *ᵥ g)| + |α₂| * |g ⬝ᵥ (piKron (P c) *ᵥ f)| := by
            rw [← abs_mul, ← abs_mul]
            exact abs_add_le _ _
        _ ≤ |α₁| * (ρ ^ 2 * (F * G)) + |α₂| * (ρ ^ 2 * (F * G)) :=
            add_le_add (mul_le_mul_of_nonneg_left (t1 c) (abs_nonneg _))
              (mul_le_mul_of_nonneg_left (t2 c) (abs_nonneg _))
        _ = (|α₁| + |α₂|) * ρ ^ 2 * (F * G) := by ring
    unfold mixChg
    calc |∑ c, w c * (α₁ * (f ⬝ᵥ (piKron (P c) *ᵥ g)) + α₂ * (g ⬝ᵥ (piKron (P c) *ᵥ f))) -
          β * (f ⬝ᵥ (piKron C *ᵥ g))|
        ≤ |∑ c, w c * (α₁ * (f ⬝ᵥ (piKron (P c) *ᵥ g)) + α₂ * (g ⬝ᵥ (piKron (P c) *ᵥ f)))| +
          |β * (f ⬝ᵥ (piKron C *ᵥ g))| := abs_sub _ _
      _ ≤ ∑ c, |w c| * ((|α₁| + |α₂|) * ρ ^ 2 * (F * G)) + |β| * (d ^ 2 * (F * G)) := by
          refine add_le_add ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun c _ => tc c)) ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left t3 (abs_nonneg _)
      _ = ((∑ c, |w c|) * (|α₁| + |α₂|) * ρ ^ 2 + |β| * d ^ 2) * (F * G) := by
          rw [← sum_mul]
          ring
      _ ≤ e * (F * G) := mul_le_mul_of_nonneg_right hmulti hFG
      _ = e * F * G := by ring

end Matrices

end Sarkozy.NormBoundsPaper4
