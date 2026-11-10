module

public import Sarkozy.MiddleRecords.MirrorKernel

/-!
# The coincidence remainder (`lem:record:conditional-collision`(a))

`paper/sections/21_middle_records.tex`, `lem:record:conditional-collision`(a):
`‖(1 - I_×) g‖ ≤ 9 M_g q` on `L²(ν_F)`, for a kernel `g` with `|g| ≤ M_g`.

The proof is the paper's: pointwise `|(1 - I_×) g| ≤ M_g ∑_{i,j} δ_{ij}` with
`δ_{ij} = [x_i = y_j]` (`coinc`, `abs_coinc_le`); for fixed `x` each event `y_j = x_i` has
probability `q` because `y_j` is uniform under `ν_F` (WP-S's `hfSum_x0`, `hfSum_x1`, `hfSum_x2`), so
the row and column sums of `∑ δ_{ij}` are `9q` (`coinc_row`, `coinc_col`); the Schur test gives the
bound. Here:

* `collision_schur`: `2 |⟨f, K h⟩| ≤ 9 M q (‖f‖² + ‖h‖²)` for every kernel `K` with
  `|K| ≤ M (1 - I_×)` pointwise (in particular `K = (1 - I_×) g`, `|g| ≤ M`);
* `collision_norm`: `|⟨f, K h⟩| ≤ 9 M q ‖f‖ ‖h‖` for `‖f‖, ‖h‖ > 0`, i.e. the operator norm
  bound.

Norms and inner products are those of `ν_F` (uniform on `H_F`, `|H_F| = p D`). The paper's
remark that a polynomial of degree at most one in each character is bounded everywhere by its
maximum `M_g` on `{±1}⁴` is the hypothesis `|K| ≤ M (1 - I_×)`; it is not formalized.
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Finset Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-- The coincidence count `∑_{i,j} [x_i = y_j]`. -/
noncomputable def coinc (x₀ x₁ x₂ y₀ y₁ y₂ : F) : ℝ :=
  ((if x₀ = y₀ then 1 else 0) + (if x₀ = y₁ then 1 else 0) + (if x₀ = y₂ then 1 else 0)) +
    ((if x₁ = y₀ then 1 else 0) + (if x₁ = y₁ then 1 else 0) + (if x₁ = y₂ then 1 else 0)) +
    ((if x₂ = y₀ then 1 else 0) + (if x₂ = y₁ then 1 else 0) + (if x₂ = y₂ then 1 else 0))

/-- The indicator `1 - I_×` that the halves share a label. -/
noncomputable def shareInd (x₀ x₁ x₂ y₀ y₁ y₂ : F) : ℝ :=
  if x₀ = y₀ ∨ x₀ = y₁ ∨ x₀ = y₂ ∨ x₁ = y₀ ∨ x₁ = y₁ ∨ x₁ = y₂ ∨ x₂ = y₀ ∨ x₂ = y₁ ∨
    x₂ = y₂ then 1 else 0

omit [Field F] [Fintype F] in
theorem shareInd_le_coinc (x₀ x₁ x₂ y₀ y₁ y₂ : F) :
    shareInd x₀ x₁ x₂ y₀ y₁ y₂ ≤ coinc x₀ x₁ x₂ y₀ y₁ y₂ := by
  unfold shareInd coinc
  split_ifs <;> simp_all <;> norm_num

omit [Field F] [Fintype F] in
theorem coinc_nonneg (x₀ x₁ x₂ y₀ y₁ y₂ : F) : 0 ≤ coinc x₀ x₁ x₂ y₀ y₁ y₂ := by
  unfold coinc
  have : ∀ (c : Prop) [Decidable c], (0 : ℝ) ≤ if c then 1 else 0 := by
    intro c _; split_ifs <;> norm_num
  have := this
  positivity

theorem hfSum_add (G G' : F → F → F → ℝ) :
    hfSum (fun a b c => G a b c + G' a b c) = hfSum G + hfSum G' := by
  unfold hfSum
  rw [← sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

theorem hfSum_mono {G G' : F → F → F → ℝ} (h : ∀ a b c, G a b c ≤ G' a b c) :
    hfSum G ≤ hfSum G' := by
  unfold hfSum
  refine sum_le_sum fun s _ => sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
  split_ifs
  · exact h s a b
  · exact le_refl 0

theorem abs_hfSum_le (G : F → F → F → ℝ) : |hfSum G| ≤ hfSum (fun a b c => |G a b c|) := by
  unfold hfSum
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ => ?_)
  split_ifs <;> simp

theorem hfSum_ind (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (v : F) :
    hfSum (fun y₀ _ _ => if v = y₀ then (1 : ℝ) else 0) = fibreSize F ∧
      hfSum (fun _ y₁ _ => if v = y₁ then (1 : ℝ) else 0) = fibreSize F ∧
      hfSum (fun _ _ y₂ => if v = y₂ then (1 : ℝ) else 0) = fibreSize F := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hfSum_x0 hF (fun y => if v = y then (1 : ℝ) else 0), sum_ite_eq]; simp
  · rw [hfSum_x1 hF h3 (fun y => if v = y then (1 : ℝ) else 0), sum_ite_eq]; simp
  · rw [hfSum_x2 hF h3 (fun y => if v = y then (1 : ℝ) else 0), sum_ite_eq]; simp

/-- **Row sums**: `∑_{y ∈ H_F} ∑_{i,j} [x_i = y_j] = 9 D`. -/
theorem coinc_row (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (x₀ x₁ x₂ : F) :
    hfSum (fun y₀ y₁ y₂ => coinc x₀ x₁ x₂ y₀ y₁ y₂) = 9 * fibreSize F := by
  unfold coinc
  simp only [hfSum_add, (hfSum_ind hF h3 _).1, (hfSum_ind hF h3 _).2.1, (hfSum_ind hF h3 _).2.2]
  ring

/-- **Column sums**: `∑_{x ∈ H_F} ∑_{i,j} [x_i = y_j] = 9 D`. -/
theorem coinc_col (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (y₀ y₁ y₂ : F) :
    hfSum (fun x₀ x₁ x₂ => coinc x₀ x₁ x₂ y₀ y₁ y₂) = 9 * fibreSize F := by
  have e : (fun x₀ x₁ x₂ => coinc x₀ x₁ x₂ y₀ y₁ y₂) =
      fun x₀ x₁ x₂ => coinc y₀ y₁ y₂ x₀ x₁ x₂ := by
    funext x₀ x₁ x₂
    unfold coinc
    simp only [eq_comm]
    ring
  rw [e, coinc_row hF h3]

theorem hfSum_mul_left (k : ℝ) (G : F → F → F → ℝ) :
    hfSum (fun a b c => k * G a b c) = k * hfSum G := by
  unfold hfSum
  rw [mul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

/-- **`lem:record:conditional-collision`(a), the Schur bound**: if `|K| ≤ M (1 - I_×)` pointwise,
then `2 |⟨f, K h⟩| ≤ 9 M q (‖f‖² + ‖h‖²)` on `L²(ν_F)`, `q = 1/p`. -/
theorem collision_schur (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {M : ℝ}
    (K : F → F → F → F → F → F → ℝ)
    (hK : ∀ x₀ x₁ x₂ y₀ y₁ y₂, |K x₀ x₁ x₂ y₀ y₁ y₂| ≤ M * shareInd x₀ x₁ x₂ y₀ y₁ y₂)
    (f h : F → F → F → ℝ) :
    2 * |(qF * fibreSize F)⁻¹ ^ 2 *
        hfSum2 (fun x₀ x₁ x₂ y₀ y₁ y₂ => f x₀ x₁ x₂ * K x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂)| ≤
      9 * M * qF⁻¹ * ((qF * fibreSize F)⁻¹ * hfSum (fun a b c => f a b c ^ 2) +
        (qF * fibreSize F)⁻¹ * hfSum (fun a b c => h a b c ^ 2)) := by
  have hD := fibreSize_pos hF
  have hp : (0 : ℝ) < qF := by
    have := Fintype.card_pos (α := F)
    exact_mod_cast this
  have hM : 0 ≤ M := by
    have := hK 0 0 0 0 0 0
    have h1 : shareInd (0 : F) 0 0 0 0 0 = 1 := by unfold shareInd; simp
    rw [h1, mul_one] at this
    exact (abs_nonneg _).trans this
  set c := (qF * fibreSize F)⁻¹ with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  -- pointwise `2|f K h| ≤ M coinc (f² + h²)`
  have hpt : ∀ x₀ x₁ x₂ y₀ y₁ y₂, 2 * |f x₀ x₁ x₂ * K x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂| ≤
      M * coinc x₀ x₁ x₂ y₀ y₁ y₂ * f x₀ x₁ x₂ ^ 2 +
        M * coinc x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂ ^ 2 := by
    intro x₀ x₁ x₂ y₀ y₁ y₂
    have hk := (hK x₀ x₁ x₂ y₀ y₁ y₂).trans
      (mul_le_mul_of_nonneg_left (shareInd_le_coinc x₀ x₁ x₂ y₀ y₁ y₂) hM)
    have hamgm : 2 * |f x₀ x₁ x₂| * |h y₀ y₁ y₂| ≤ f x₀ x₁ x₂ ^ 2 + h y₀ y₁ y₂ ^ 2 := by
      nlinarith [sq_nonneg (|f x₀ x₁ x₂| - |h y₀ y₁ y₂|), sq_abs (f x₀ x₁ x₂),
        sq_abs (h y₀ y₁ y₂)]
    rw [abs_mul, abs_mul]
    have hMc : 0 ≤ M * coinc x₀ x₁ x₂ y₀ y₁ y₂ := mul_nonneg hM (coinc_nonneg _ _ _ _ _ _)
    calc 2 * (|f x₀ x₁ x₂| * |K x₀ x₁ x₂ y₀ y₁ y₂| * |h y₀ y₁ y₂|)
        = |K x₀ x₁ x₂ y₀ y₁ y₂| * (2 * |f x₀ x₁ x₂| * |h y₀ y₁ y₂|) := by ring
      _ ≤ (M * coinc x₀ x₁ x₂ y₀ y₁ y₂) * (f x₀ x₁ x₂ ^ 2 + h y₀ y₁ y₂ ^ 2) :=
          mul_le_mul hk hamgm (by positivity) hMc
      _ = _ := by ring
  -- sum the pointwise bound
  have hsum : 2 * |hfSum2 (fun x₀ x₁ x₂ y₀ y₁ y₂ =>
      f x₀ x₁ x₂ * K x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂)| ≤
      9 * fibreSize F * M * (hfSum (fun a b c => f a b c ^ 2) +
        hfSum (fun a b c => h a b c ^ 2)) := by
    unfold hfSum2
    have step1 : |hfSum (fun x₀ x₁ x₂ => hfSum (fun y₀ y₁ y₂ =>
        f x₀ x₁ x₂ * K x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂))| ≤
        hfSum (fun x₀ x₁ x₂ => hfSum (fun y₀ y₁ y₂ =>
          |f x₀ x₁ x₂ * K x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂|)) :=
      (abs_hfSum_le _).trans (hfSum_mono fun a b c => abs_hfSum_le _)
    have step2 : 2 * hfSum (fun x₀ x₁ x₂ => hfSum (fun y₀ y₁ y₂ =>
        |f x₀ x₁ x₂ * K x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂|)) ≤
        hfSum (fun x₀ x₁ x₂ => hfSum (fun y₀ y₁ y₂ =>
          M * coinc x₀ x₁ x₂ y₀ y₁ y₂ * f x₀ x₁ x₂ ^ 2 +
            M * coinc x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂ ^ 2)) := by
      rw [← hfSum_mul_left]
      refine hfSum_mono fun a b c => ?_
      rw [← hfSum_mul_left]
      exact hfSum_mono fun d e g => hpt a b c d e g
    have step3 : hfSum (fun x₀ x₁ x₂ => hfSum (fun y₀ y₁ y₂ =>
        M * coinc x₀ x₁ x₂ y₀ y₁ y₂ * f x₀ x₁ x₂ ^ 2 +
          M * coinc x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂ ^ 2)) =
        9 * fibreSize F * M * (hfSum (fun a b c => f a b c ^ 2) +
          hfSum (fun a b c => h a b c ^ 2)) := by
      simp only [hfSum_add]
      have e1 : ∀ a b c : F, hfSum (fun y₀ y₁ y₂ => M * coinc a b c y₀ y₁ y₂ * f a b c ^ 2) =
          9 * fibreSize F * M * f a b c ^ 2 := by
        intro a b c
        have : (fun y₀ y₁ y₂ => M * coinc a b c y₀ y₁ y₂ * f a b c ^ 2) =
            fun y₀ y₁ y₂ => (M * f a b c ^ 2) * coinc a b c y₀ y₁ y₂ := by
          funext y₀ y₁ y₂; ring
        rw [this, hfSum_mul_left, coinc_row hF h3]
        ring
      simp only [e1, hfSum_mul_left]
      -- the second part, by Fubini on the pair
      have e2 : hfSum (fun x₀ x₁ x₂ => hfSum (fun y₀ y₁ y₂ =>
          M * coinc x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂ ^ 2)) =
          9 * fibreSize F * M * hfSum (fun a b c => h a b c ^ 2) := by
        have hswap : hfSum (fun x₀ x₁ x₂ => hfSum (fun y₀ y₁ y₂ =>
            M * coinc x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂ ^ 2)) =
            hfSum (fun y₀ y₁ y₂ => hfSum (fun x₀ x₁ x₂ =>
              M * coinc x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂ ^ 2)) := by
          have := hfSum2_comm (fun x₀ x₁ x₂ y₀ y₁ y₂ =>
            M * coinc x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂ ^ 2)
          unfold hfSum2 at this
          exact this
        rw [hswap]
        have e3 : ∀ a b c : F, hfSum (fun x₀ x₁ x₂ => M * coinc x₀ x₁ x₂ a b c * h a b c ^ 2) =
            9 * fibreSize F * M * h a b c ^ 2 := by
          intro a b c
          have : (fun x₀ x₁ x₂ => M * coinc x₀ x₁ x₂ a b c * h a b c ^ 2) =
              fun x₀ x₁ x₂ => (M * h a b c ^ 2) * coinc x₀ x₁ x₂ a b c := by
            funext x₀ x₁ x₂; ring
          rw [this, hfSum_mul_left, coinc_col hF h3]
          ring
        simp only [e3, hfSum_mul_left]
      rw [e2]
      ring
    calc 2 * |hfSum (fun x₀ x₁ x₂ => hfSum (fun y₀ y₁ y₂ =>
          f x₀ x₁ x₂ * K x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂))|
        ≤ 2 * hfSum (fun x₀ x₁ x₂ => hfSum (fun y₀ y₁ y₂ =>
          |f x₀ x₁ x₂ * K x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂|)) := by linarith
      _ ≤ _ := step2
      _ = _ := step3
  rw [abs_mul, abs_of_pos (by positivity : 0 < c ^ 2)]
  have : 2 * (c ^ 2 * |hfSum2 (fun x₀ x₁ x₂ y₀ y₁ y₂ =>
      f x₀ x₁ x₂ * K x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂)|) ≤
      c ^ 2 * (9 * fibreSize F * M * (hfSum (fun a b c => f a b c ^ 2) +
        hfSum (fun a b c => h a b c ^ 2))) := by
    nlinarith [mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ c ^ 2)]
  calc 2 * (c ^ 2 * |hfSum2 (fun x₀ x₁ x₂ y₀ y₁ y₂ =>
        f x₀ x₁ x₂ * K x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂)|)
      ≤ c ^ 2 * (9 * fibreSize F * M * (hfSum (fun a b c => f a b c ^ 2) +
        hfSum (fun a b c => h a b c ^ 2))) := this
    _ = 9 * M * qF⁻¹ * (c * hfSum (fun a b c => f a b c ^ 2) +
        c * hfSum (fun a b c => h a b c ^ 2)) := by
        rw [hc]
        field_simp

/-- **`lem:record:conditional-collision`(a): `‖(1 - I_×) g‖ ≤ 9 M_g q`** as an operator norm on
`L²(ν_F)`: `|⟨f, K h⟩| ≤ 9 M q ‖f‖ ‖h‖` for `‖f‖, ‖h‖ > 0` (the supremum defining the norm),
from `collision_schur` by scaling `f ↦ λ f`, `h ↦ h/λ`. -/
theorem collision_norm (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {M : ℝ}
    (K : F → F → F → F → F → F → ℝ)
    (hK : ∀ x₀ x₁ x₂ y₀ y₁ y₂, |K x₀ x₁ x₂ y₀ y₁ y₂| ≤ M * shareInd x₀ x₁ x₂ y₀ y₁ y₂)
    (f h : F → F → F → ℝ)
    (hf : 0 < (qF * fibreSize F)⁻¹ * hfSum (fun a b c => f a b c ^ 2))
    (hh : 0 < (qF * fibreSize F)⁻¹ * hfSum (fun a b c => h a b c ^ 2)) :
    |(qF * fibreSize F)⁻¹ ^ 2 *
        hfSum2 (fun x₀ x₁ x₂ y₀ y₁ y₂ => f x₀ x₁ x₂ * K x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂)| ≤
      9 * M * qF⁻¹ * (Real.sqrt ((qF * fibreSize F)⁻¹ * hfSum (fun a b c => f a b c ^ 2)) *
        Real.sqrt ((qF * fibreSize F)⁻¹ * hfSum (fun a b c => h a b c ^ 2))) := by
  set Nf := (qF * fibreSize F)⁻¹ * hfSum (fun a b c => f a b c ^ 2) with hNf
  set Nh := (qF * fibreSize F)⁻¹ * hfSum (fun a b c => h a b c ^ 2) with hNh
  have hsf : 0 < Real.sqrt Nf := Real.sqrt_pos.mpr hf
  have hsh : 0 < Real.sqrt Nh := Real.sqrt_pos.mpr hh
  -- the scaling `λ² = √Nh/√Nf`
  set lam := Real.sqrt (Real.sqrt Nh / Real.sqrt Nf) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr (div_pos hsh hsf)
  have hlam2 : lam ^ 2 = Real.sqrt Nh / Real.sqrt Nf := Real.sq_sqrt (div_pos hsh hsf).le
  have hS := collision_schur hF h3 K hK (fun a b c => lam * f a b c) (fun a b c => lam⁻¹ * h a b c)
  have e1 : hfSum2 (fun x₀ x₁ x₂ y₀ y₁ y₂ => lam * f x₀ x₁ x₂ * K x₀ x₁ x₂ y₀ y₁ y₂ *
      (lam⁻¹ * h y₀ y₁ y₂)) =
      hfSum2 (fun x₀ x₁ x₂ y₀ y₁ y₂ => f x₀ x₁ x₂ * K x₀ x₁ x₂ y₀ y₁ y₂ * h y₀ y₁ y₂) := by
    unfold hfSum2
    congr 1
    funext x₀ x₁ x₂
    congr 1
    funext y₀ y₁ y₂
    field_simp
  have e2 : (qF * fibreSize F)⁻¹ * hfSum (fun a b c => (lam * f a b c) ^ 2) = lam ^ 2 * Nf := by
    rw [hNf, show (fun a b c => (lam * f a b c) ^ 2) = fun a b c => lam ^ 2 * f a b c ^ 2 by
      funext a b c; ring, hfSum_mul_left]
    ring
  have e3 : (qF * fibreSize F)⁻¹ * hfSum (fun a b c => (lam⁻¹ * h a b c) ^ 2) =
      (lam ^ 2)⁻¹ * Nh := by
    rw [hNh, show (fun a b c => (lam⁻¹ * h a b c) ^ 2) = fun a b c => (lam ^ 2)⁻¹ * h a b c ^ 2 by
      funext a b c; rw [mul_pow, inv_pow], hfSum_mul_left]
    ring
  simp only [e1, e2, e3] at hS
  have key : lam ^ 2 * Nf + (lam ^ 2)⁻¹ * Nh = 2 * (Real.sqrt Nf * Real.sqrt Nh) := by
    rw [hlam2]
    have hNf' : Nf = Real.sqrt Nf ^ 2 := (Real.sq_sqrt hf.le).symm
    have hNh' : Nh = Real.sqrt Nh ^ 2 := (Real.sq_sqrt hh.le).symm
    rw [hNf', hNh']
    field_simp
    rw [Real.sqrt_sq hsf.le, Real.sqrt_sq hsh.le]
    ring
  rw [key] at hS
  linarith

end Sarkozy.MiddleRecords
