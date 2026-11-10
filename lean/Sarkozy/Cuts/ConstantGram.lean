module

public import Sarkozy.Cuts.FrameTensor
public import Sarkozy.Cuts.ProjectedDiagonal

/-! Norms of centered kernels whose Gram has constant diagonal and off-diagonal entries. -/

@[expose] public section

namespace Sarkozy.Cuts

open Sarkozy.Recentering

variable {Λ X : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] [Fintype X]

omit [DecidableEq Λ] [Nonempty Λ] [Fintype X] in
theorem recOp_center_of_row_mean_zero (ν : FiniteLaw Λ) (K : X → Λ → ℝ)
    (hK : ∀ x, ν.expect (K x) = 0) (f : Λ → ℝ) :
    recOp ν K (center ν f) = recOp ν K f := by
  funext x
  simp only [recOp, center, mul_sub, FiniteLaw.expect_sub,
    FiniteLaw.expect_mul_const, hK, zero_mul, sub_zero]

theorem constantGram_action (G : Λ → Λ → ℝ) {d e : ℝ}
    (hd : ∀ a, G a a = d) (he : ∀ a b, a ≠ b → G a b = e)
    (f : Λ → ℝ) (hf : (FiniteLaw.uniform Λ).expect f = 0) (a : Λ) :
    recOp (FiniteLaw.uniform Λ) G f a =
      ((d - e) / (Fintype.card Λ : ℝ)) * f a := by
  have hx (b : Λ) : G a b * f b = e * f b + if a = b then (d - e) * f b else 0 := by
    by_cases hab : a = b
    · subst b
      rw [hd, ite_eq_left rfl]
      ring
    · rw [he a b hab, ite_eq_right hab, add_zero]
  unfold recOp
  simp_rw [hx]
  rw [FiniteLaw.expect_add, FiniteLaw.expect_const_mul, hf, mul_zero, zero_add,
    uniform_diagonal_expect]
  ring

theorem constantGram_norm_sq (ν : FiniteLaw X) (K : X → Λ → ℝ) {d e : ℝ}
    (hd : ∀ a, gramKer ν K K a a = d)
    (he : ∀ a b, a ≠ b → gramKer ν K K a b = e)
    (f : Λ → ℝ) (hf : (FiniteLaw.uniform Λ).expect f = 0) :
    nrm ν (recOp (FiniteLaw.uniform Λ) K f) ^ 2 =
      ((d - e) / (Fintype.card Λ : ℝ)) * nrm (FiniteLaw.uniform Λ) f ^ 2 := by
  rw [nrm_sq_eq, ip_recOp_recOp]
  have hact : recOp (FiniteLaw.uniform Λ) (gramKer ν K K) f =
      fun a => ((d - e) / (Fintype.card Λ : ℝ)) * f a :=
    funext (constantGram_action _ hd he f hf)
  rw [hact, ip_comm, ip_smul_left, ← nrm_sq_eq]

theorem constantGram_centered_relation (ν : FiniteLaw X) (K : X → Λ → ℝ)
    (hK : ∀ x, (FiniteLaw.uniform Λ).expect (K x) = 0) {d e : ℝ}
    (hd : ∀ a, gramKer ν K K a a = d)
    (he : ∀ a b, a ≠ b → gramKer ν K K a b = e) :
    d + ((Fintype.card Λ : ℝ) - 1) * e = 0 := by
  obtain ⟨a⟩ := (inferInstance : Nonempty Λ)
  have hrow : (FiniteLaw.uniform Λ).expect (fun b => gramKer ν K K a b) = 0 := by
    unfold gramKer
    rw [expect_comm]
    simp only [FiniteLaw.expect_const_mul, hK, mul_zero, FiniteLaw.expect_const]
  have hx (b : Λ) : gramKer ν K K a b = e + if a = b then d - e else 0 := by
    by_cases hab : a = b
    · subst b
      rw [hd, ite_eq_left rfl]
      ring
    · rw [he a b hab, ite_eq_right hab, add_zero]
  simp_rw [hx] at hrow
  rw [FiniteLaw.expect_add, FiniteLaw.expect_const, uniform_diagonal_const] at hrow
  have hn : (Fintype.card Λ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp at hrow
  linarith

theorem constantGram_centered_norm_sq (ν : FiniteLaw X) (K : X → Λ → ℝ)
    (hK : ∀ x, (FiniteLaw.uniform Λ).expect (K x) = 0) {d e : ℝ}
    (hd : ∀ a, gramKer ν K K a a = d)
    (he : ∀ a b, a ≠ b → gramKer ν K K a b = e) (hn : 2 ≤ Fintype.card Λ)
    (f : Λ → ℝ) (hf : (FiniteLaw.uniform Λ).expect f = 0) :
    nrm ν (recOp (FiniteLaw.uniform Λ) K f) ^ 2 =
      (d / ((Fintype.card Λ : ℝ) - 1)) * nrm (FiniteLaw.uniform Λ) f ^ 2 := by
  rw [constantGram_norm_sq ν K hd he f hf]
  have hc := constantGram_centered_relation ν K hK hd he
  have hn' : (2 : ℝ) ≤ Fintype.card Λ := by exact_mod_cast hn
  have hn0 : (Fintype.card Λ : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card Λ : ℝ) - 1 ≠ 0 := by linarith
  congr 1
  field_simp
  nlinarith

end Sarkozy.Cuts
