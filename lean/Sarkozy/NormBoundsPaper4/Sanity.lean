module

public import Sarkozy.NormBoundsPaper4.Constructor
public import Sarkozy.NormBoundsPaper4.EEps
public import Sarkozy.PrimeGram.Sanity

@[expose] public section

/-!
# Non-vacuity checks for the fold reduction (FD)

* **`foldPrime_crude`**: `FoldPrimeBound` holds at the paper's objects (the components `P_{c,p}` of
  any fold components, the reference `K_{0,p}`, the actual marginal `m_{0,p}`, any `t ≥ 0`) with
  the crude constant `(1 + t)(|α₁| + |α₂|) + |β|` (each coupling is a contraction of `L²(m₀)`): at
  `(½, ½, 1)` this is `2 + t`, at `(½, −½, 0)` it is `1 + t`. So the one-prime statements of
  `FoldInputs` are satisfiable statements about the paper's operators; their content is the
  small constants `s_F/p` and `ℓ_t p^{-1/2} + a_F/p`.
* `sanity_fold_check`: `fold_check` at `Q₃` (piece `0`).
* `sanity_eorth_11`: `lem:record:e-orthogonal`(c) instantiated at `p = 11` (NB3's power iteration
  gives `‖Sym(K₁ − K^E_0)‖ ≈ 0.331` there, the paper's `s^E_11 ≈ 2.93`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper4

open Sarkozy.PartV Sarkozy.SignedComponents Sarkozy.SignedGram Sarkozy.PrimeGram
open Sarkozy.MiddleComparison (signedCoef)

section Toy

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]
  {hne : MiddleNonempty pr}

omit [Fintype ι] [DecidableEq ι] in
/-- **The one-prime fold bounds are satisfiable** at the paper's objects, with the crude constant
`(1 + t)(|α₁| + |α₂|) + |β|`. -/
theorem foldPrime_crude (C : FoldComponents pr hne) {t : ℝ} (ht : 0 ≤ t) (α₁ α₂ β : ℝ) (i : ι) :
    FoldPrimeBound (mP hne i) (fun c => compP hne C c i) (oldP hne i) (signedCoef t) α₁ α₂ β
      ((1 + t) * (|α₁| + |α₂|) + |β|) := by
  intro u v _ _
  set U := √(mip (mP hne i) u u)
  set V := √(mip (mP hne i) v v)
  have hU : √(∑ a, mP hne i a * u a ^ 2) = U := by
    congr 1; exact sum_congr rfl fun a _ => by ring
  have hV : √(∑ a, mP hne i a * v a ^ 2) = V := by
    congr 1; exact sum_congr rfl fun a _ => by ring
  rw [hU, hV]
  have hUV : 0 ≤ U * V := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hc : ∀ c, |u ⬝ᵥ (compP hne C c i *ᵥ v)| ≤ U * V := fun c =>
    coupling_dot_le (compP_nonneg C c i) ((compP_coupling hne C c).row i)
      ((compP_coupling hne C c).col i) u v
  have hc' : ∀ c, |v ⬝ᵥ (compP hne C c i *ᵥ u)| ≤ U * V := fun c => by
    rw [mul_comm U V]
    exact coupling_dot_le (compP_nonneg C c i) ((compP_coupling hne C c).row i)
      ((compP_coupling hne C c).col i) v u
  have ho : |u ⬝ᵥ (oldP hne i *ᵥ v)| ≤ U * V :=
    coupling_dot_le (oldP_nonneg i) ((oldP_coupling hne).row i) ((oldP_coupling hne).col i) u v
  have tc : ∀ c, |signedCoef t c * (α₁ * (u ⬝ᵥ (compP hne C c i *ᵥ v)) +
      α₂ * (v ⬝ᵥ (compP hne C c i *ᵥ u)))| ≤ |signedCoef t c| * ((|α₁| + |α₂|) * (U * V)) :=
    fun c => by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc _ ≤ |α₁ * (u ⬝ᵥ (compP hne C c i *ᵥ v))| + |α₂ * (v ⬝ᵥ (compP hne C c i *ᵥ u))| :=
            abs_add_le _ _
        _ ≤ |α₁| * (U * V) + |α₂| * (U * V) := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul_of_nonneg_left (hc c) (abs_nonneg _))
              (mul_le_mul_of_nonneg_left (hc' c) (abs_nonneg _))
        _ = _ := by ring
  unfold mixChg1
  calc _ ≤ |∑ c, signedCoef t c * (α₁ * (u ⬝ᵥ (compP hne C c i *ᵥ v)) +
        α₂ * (v ⬝ᵥ (compP hne C c i *ᵥ u)))| + |β * (u ⬝ᵥ (oldP hne i *ᵥ v))| := abs_sub _ _
    _ ≤ ∑ c, |signedCoef t c| * ((|α₁| + |α₂|) * (U * V)) + |β| * (U * V) := by
        refine add_le_add ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun c _ => tc c)) ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ho (abs_nonneg _)
    _ = ((∑ c, |signedCoef t c|) * (|α₁| + |α₂|) + |β|) * (U * V) := by
        rw [← sum_mul]; ring
    _ = _ := by rw [sum_abs_signedCoef ht]; ring

end Toy

/-- `fold_check` at the first piece `X = Q₃`. -/
theorem sanity_fold_check :
    (Sarkozy.SignedDecomp.gamX 0 + eo73 0 * Sarkozy.SignedDecomp.rX 0) ^ 2 +
        627 / 500 * Sarkozy.SignedDecomp.cpX 0 ^ 2 ≤ Sarkozy.HsumProof.kSF 0 :=
  (fold_check 0).1

/-- `lem:record:e-orthogonal`(c) at the prime `11`. -/
theorem sanity_eorth_11 :
    haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    Sarkozy.NormBoundsPaper3.EOrthPrime 11
      (Sarkozy.NormBoundsPaper3.sEpaper (1 / ((11 : ℕ) : ℝ)) (1 / Real.sqrt ((11 : ℕ) : ℝ))) :=
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  eorth_prime_paper (p := 11) (by norm_num) (by norm_num)

end Sarkozy.NormBoundsPaper4
