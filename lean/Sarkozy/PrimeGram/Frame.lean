module

public import Sarkozy.PrimeGram.Features

@[expose] public section

/-!
# The frame bound `Γ_A` in adjoint form at the actual half marginal (PG)

`paper/sections/21_middle_records.tex`, `lem:actual-features`(d); its use as the frame
`‖(V, A₁/r, A₂/r, A₃/r)‖² ≤ Γ` of `lem:record:direct-gram` (`paper/sections/24_matching_mean.tex`).

* `mip_sq_le`: Cauchy–Schwarz in `L²(m)` (`m ≥ 0`).
* **`frame_analysis`**: at the paper's marginal `m₀`, for **every** function `f` of the half,
  `‖V₀^{*m} f‖² + p ∑_i ‖A_i^{*m} f‖² ≤ Γ ‖f‖²_{m₀}`.
  This is W6's synthesis bound (`synthesis_bound`, at `m₀` by `sum_m0`) read through the adjoint
  identity `adj_spec`: with `h = (V₀^{*m} f, √p A₂^{*m} f, √p A₁^{*m} f, √p A₃^{*m} f)` (all in
  `H₀`) the synthesis `S h` satisfies `⟨S h, f⟩_{m₀} = N := ‖h‖²`, and Cauchy–Schwarz gives
  `N² ≤ ‖S h‖² ‖f‖² ≤ Γ N ‖f‖²`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.PrimeGram

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing Sarkozy.SignedComponents
  Sarkozy.SignedEstimates Sarkozy.MiddleRecords

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "qF" => (Fintype.card F : ℝ)

omit [Field F] [DecidableEq F] in
/-- Cauchy–Schwarz in `L²(m)`. -/
theorem mip_sq_le {m : (Fin 3 → F) → ℝ} (hm : ∀ x, 0 ≤ m x) (f g : (Fin 3 → F) → ℝ) :
    mip m f g ^ 2 ≤ mip m f f * mip m g g := by
  unfold mip
  have h := sum_mul_sq_le_sq_mul_sq univ (fun x => Real.sqrt (m x) * f x)
    (fun x => Real.sqrt (m x) * g x)
  have hs : ∀ x, Real.sqrt (m x) ^ 2 = m x := fun x => Real.sq_sqrt (hm x)
  have e1 : ∀ x, Real.sqrt (m x) * f x * (Real.sqrt (m x) * g x) = m x * f x * g x := by
    intro x
    rw [show Real.sqrt (m x) * f x * (Real.sqrt (m x) * g x) =
      Real.sqrt (m x) ^ 2 * f x * g x by ring, hs x]
  have e2 : ∀ x, (Real.sqrt (m x) * f x) ^ 2 = m x * f x * f x := by
    intro x
    rw [mul_pow, hs x]
    ring
  have e3 : ∀ x, (Real.sqrt (m x) * g x) ^ 2 = m x * g x * g x := by
    intro x
    rw [mul_pow, hs x]
    ring
  simp only [e1, e2, e3] at h
  exact h

omit [Field F] [DecidableEq F] in
theorem mip_self_nonneg {m : (Fin 3 → F) → ℝ} (hm : ∀ x, 0 ≤ m x) (f : (Fin 3 → F) → ℝ) :
    0 ≤ mip m f f := by
  unfold mip
  exact sum_nonneg fun x _ => by
    have := hm x
    nlinarith [mul_nonneg this (sq_nonneg (f x))]

omit [Field F] [DecidableEq F] in
theorem uip_self_nonneg (h : F → ℝ) : 0 ≤ uip h h := by
  unfold uip
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (sum_nonneg fun a _ => mul_self_nonneg (h a))

omit [Field F] [DecidableEq F] in
theorem uip_comm (h k : F → ℝ) : uip h k = uip k h := by
  unfold uip
  congr 1
  exact sum_congr rfl fun a _ => mul_comm _ _

omit [Field F] [DecidableEq F] in
theorem uip_smul_left (c : ℝ) (h k : F → ℝ) : uip (fun a => c * h a) k = c * uip h k := by
  unfold uip
  rw [mul_sum, mul_sum, mul_sum]
  exact sum_congr rfl fun a _ => by ring

omit [Field F] [DecidableEq F] in
theorem uip_smul_right (c : ℝ) (h k : F → ℝ) : uip h (fun a => c * k a) = c * uip h k := by
  rw [uip_comm, uip_smul_left, uip_comm]

omit [Field F] [DecidableEq F] in
theorem unifNormSq_eq_uip (h : F → ℝ) : unifNormSq h = uip h h := by
  unfold unifNormSq uip
  congr 1
  exact sum_congr rfl fun a _ => sq _

omit [DecidableEq F] in
theorem sum_smul_cen (c : ℝ) (h : F → ℝ) : ∑ a, c * cen h a = 0 := by
  rw [← mul_sum, sum_cen, mul_zero]

section Frame

variable (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)

/-- **`lem:actual-features`(d) in adjoint form, at the actual half marginal `m₀`**: for every
function `f` of the half,
`‖V₀^{*m} f‖² + p (‖A₁^{*m} f‖² + ‖A₂^{*m} f‖² + ‖A₃^{*m} f‖²) ≤ Γ ‖f‖²_{m₀}`, i.e. the frame
bound `‖(V₀, A₁/r, A₂/r, A₃/r)‖² ≤ Γ ≤ Γ_A` of `lem:record:direct-gram` (`1/r² = p`). -/
theorem frame_analysis (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (h19 : 19 ≤ Fintype.card F) (f : (Fin 3 → F) → ℝ) :
    uip (adj (m0 hF).weight V0 f) (adj (m0 hF).weight V0 f) +
        qF * ∑ i, uip (adj (m0 hF).weight (arm i) f) (adj (m0 hF).weight (arm i) f) ≤
      gammaW (F := F) * mip (m0 hF).weight f f := by
  set m := (m0 hF).weight with hm_def
  have hm : ∀ x, 0 ≤ m x := (m0 hF).nonneg
  have h19' : (19 : ℝ) ≤ qF := by exact_mod_cast h19
  have h7 : (7 : ℝ) ≤ qF := by linarith
  have hq0 : (0 : ℝ) ≤ qF := by linarith
  set s := Real.sqrt qF with hs_def
  have hs2 : s * s = qF := Real.mul_self_sqrt hq0
  set w := adj m V0 f
  set b₁ := adj m A1 f
  set b₂ := adj m A2 f
  set b₃ := adj m A3 f
  set h₁ : F → ℝ := fun a => s * b₂ a
  set h₂ : F → ℝ := fun a => s * b₁ a
  set k : F → ℝ := fun a => s * b₃ a
  have hw0 : ∑ a, w a = 0 := sum_cen _
  have hh₁ : ∑ a, h₁ a = 0 := sum_smul_cen s _
  have hh₂ : ∑ a, h₂ a = 0 := sum_smul_cen s _
  have hk : ∑ a, k a = 0 := sum_smul_cen s _
  -- the synthesis `u = S h`
  set u : (Fin 3 → F) → ℝ := fun x => w (x 0) + s * paleyOp h₁ (x 1) + s * paleyOp h₂ (x 2) +
    s * A3op k (x 1) (x 2) with hu_def
  -- (1) the synthesis bound at `m₀`
  have hsyn := synthesis_bound hR h3 h7 w h₁ h₂ k hh₁ hh₂ hk
  have huu : mip m u u = Iw (fun a b c => (w a + Real.sqrt qF * paleyOp h₁ b +
      Real.sqrt qF * paleyOp h₂ c + Real.sqrt qF * A3op k b c) ^ 2) / oldZ (F := F) := by
    rw [← sum_m0 hF hR h3 h19]
    unfold mip
    refine sum_congr rfl fun x _ => ?_
    simp only [u]
    ring
  rw [← huu] at hsyn
  simp only [unifNormSq_eq_uip] at hsyn
  -- (2) the pairing with `f`
  set N := uip w w + qF * (uip b₁ b₁ + uip b₂ b₂ + uip b₃ b₃) with hN_def
  have hnorms : uip w w + uip h₁ h₁ + uip h₂ h₂ + uip k k = N := by
    simp only [h₁, h₂, k, uip_smul_left, uip_smul_right, hN_def]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, hs2]
    ring
  have hlin : mip m u f = mip m (V0 w) f + s * mip m (A2 h₁) f + s * mip m (A1 h₂) f +
      s * mip m (A3 k) f := by
    unfold mip
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    simp only [u, V0, A1, A2, A3]
    ring
  have hpair : mip m u f = N := by
    rw [hlin, adj_spec m V0_kernel hw0, adj_spec m A2_kernel hh₁, adj_spec m A1_kernel hh₂,
      adj_spec m A3_kernel hk, ← hnorms]
    simp only [h₁, h₂, k, uip_smul_left, uip_smul_right]
    rfl
  rw [hnorms] at hsyn
  -- (3) Cauchy–Schwarz
  have hcs := mip_sq_le hm u f
  rw [hpair] at hcs
  have hΓ := gammaW_nonneg (F := F) h7
  have hN0 : 0 ≤ N := by
    have := uip_self_nonneg w
    have := uip_self_nonneg b₁
    have := uip_self_nonneg b₂
    have := uip_self_nonneg b₃
    positivity
  have hM0 := mip_self_nonneg hm f
  have hsum : ∑ i, uip (adj m (arm i) f) (adj m (arm i) f) = uip b₁ b₁ + uip b₂ b₂ + uip b₃ b₃ := by
    simp only [Fin.sum_univ_three, arm, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rfl
  rw [hsum]
  change N ≤ gammaW * mip m f f
  -- `N² ≤ (Γ N) M`
  have h2 : N ^ 2 ≤ gammaW * N * mip m f f :=
    hcs.trans (mul_le_mul_of_nonneg_right hsyn hM0)
  rcases hN0.lt_or_eq with hpos | hzero
  · nlinarith
  · rw [← hzero]
    exact mul_nonneg hΓ hM0

end Frame

end Sarkozy.PrimeGram
