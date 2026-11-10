module

public import Sarkozy.SecondOrder.Conditional

/-!
# The brackets of the moving-root moments and the pivot sums (`eq:pivot-sums`)

`paper/sections/15_second_order.tex`. With `h(s) = 2⌊s/2⌋` (`Target.gam`):

* `bracketTwo r s t u = (s + t + u - 1) h(s) h(t) + 1 + r (s + t + u) s t`, the bracket of
  `eq:advance:rank-second`, and `bracketOne r s u = (s + u - 1) h(s) + r (s + u) s`, that of
  `eq:advance:rank-first` (both as in `Target.MovingRoot`);
* `sum_card_powerset`: over the `2^d` subsets `P` of a `d`-element set, `∑_P |P| = (d/2) 2^d`;
* `sum_bracketTwo`, `sum_bracketOne`: summing over `P` replaces `u = |P|` by `d/2` and multiplies by
  `2^d`;
* the pivot sums `A, L, U, V, W, X, E, K, D²` of `eq:pivot-sums` for a family of coefficients
  `b_l` and root-set sizes `s_l` (`pivA`, …, `pivD2`), and the two identities used in the proof of
  `lem:pivot-moments`: `sum_bracketTwo_family` (the second-moment error is `E`) and
  `sum_bracketOne_family` (the first-moment main part is `2^d [V + (d/2)U + r(X + (d/2)W)]`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SecondOrder

open Sarkozy.Target

/-- The bracket of `eq:advance:rank-second`. -/
noncomputable def bracketTwo (r : ℝ) (s t u : ℕ) : ℝ :=
  ((s : ℝ) + t + u - 1) * gam s * gam t + 1 + r * ((s : ℝ) + t + u) * s * t

/-- The bracket of `eq:advance:rank-first`. -/
noncomputable def bracketOne (r : ℝ) (s u : ℕ) : ℝ :=
  ((s : ℝ) + u - 1) * gam s + r * ((s : ℝ) + u) * s

theorem bracketTwo_nonneg {r : ℝ} (hr : 0 ≤ r) {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) (u : ℕ) :
    0 ≤ bracketTwo r s t u := by
  unfold bracketTwo
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hu : (0 : ℝ) ≤ u := Nat.cast_nonneg _
  have hg : (0 : ℝ) ≤ gam s := Nat.cast_nonneg _
  have hg' : (0 : ℝ) ≤ gam t := Nat.cast_nonneg _
  have h1 : 0 ≤ ((s : ℝ) + t + u - 1) * gam s * gam t :=
    mul_nonneg (mul_nonneg (by linarith) hg) hg'
  have h2 : 0 ≤ r * ((s : ℝ) + t + u) * s * t :=
    mul_nonneg (mul_nonneg (mul_nonneg hr (by linarith)) (by linarith)) (by linarith)
  linarith

theorem bracketOne_nonneg {r : ℝ} (hr : 0 ≤ r) {s : ℕ} (hs : 1 ≤ s) (u : ℕ) :
    0 ≤ bracketOne r s u := by
  unfold bracketOne
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hu : (0 : ℝ) ≤ u := Nat.cast_nonneg _
  have hg : (0 : ℝ) ≤ gam s := Nat.cast_nonneg _
  have h1 : 0 ≤ ((s : ℝ) + u - 1) * gam s := mul_nonneg (by linarith) hg
  have h2 : 0 ≤ r * ((s : ℝ) + u) * s := mul_nonneg (mul_nonneg hr (by linarith)) (by linarith)
  linarith

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem sum_one_powerset : ∑ _J ∈ (univ : Finset κ).powerset, (1 : ℝ) = 2 ^ Fintype.card κ := by
  rw [sum_const, card_powerset, card_univ]
  simp

/-- `∑_{P ⊆ κ} |P| = (d/2) 2^d` with `d = |κ|`, by complementation. -/
theorem sum_card_powerset :
    ∑ J ∈ (univ : Finset κ).powerset, (J.card : ℝ) =
      (Fintype.card κ : ℝ) / 2 * 2 ^ Fintype.card κ := by
  rw [powerset_univ]
  have hinv : ∑ J : Finset κ, (J.card : ℝ) = ∑ J : Finset κ, ((Jᶜ).card : ℝ) :=
    (Equiv.sum_comp (Function.Involutive.toPerm _ compl_involutive)
      (fun J : Finset κ => (J.card : ℝ))).symm
  have hcompl : ∀ J : Finset κ, ((Jᶜ).card : ℝ) = Fintype.card κ - J.card := by
    intro J
    rw [card_compl, Nat.cast_sub (card_le_univ J)]
  have hcard : ∑ _J : Finset κ, (Fintype.card κ : ℝ) =
      (Fintype.card κ : ℝ) * 2 ^ Fintype.card κ := by
    rw [sum_const, card_univ, Fintype.card_finset, nsmul_eq_mul]
    push_cast
    ring
  simp_rw [hcompl] at hinv
  rw [sum_sub_distrib, hcard] at hinv
  linarith

/-- `∑_{P ⊆ κ} B(s, t, |P|) = 2^d [(s + t + d/2 - 1) h(s) h(t) + 1 + r (s + t + d/2) s t]`. -/
theorem sum_bracketTwo (r : ℝ) (s t : ℕ) :
    ∑ J ∈ (univ : Finset κ).powerset, bracketTwo r s t J.card =
      2 ^ Fintype.card κ * (((s : ℝ) + t + (Fintype.card κ : ℝ) / 2 - 1) * gam s * gam t + 1 +
        r * ((s : ℝ) + t + (Fintype.card κ : ℝ) / 2) * s * t) := by
  have h : ∀ J : Finset κ, bracketTwo r s t J.card =
      (((s : ℝ) + t - 1) * gam s * gam t + 1 + r * ((s : ℝ) + t) * s * t) * 1 +
        ((gam s : ℝ) * gam t + r * s * t) * (J.card : ℝ) := by
    intro J; unfold bracketTwo; ring
  simp_rw [h]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_one_powerset, sum_card_powerset]
  ring

/-- `∑_{P ⊆ κ} B₁(s, |P|) = 2^d [(s + d/2 - 1) h(s) + r (s + d/2) s]`. -/
theorem sum_bracketOne (r : ℝ) (s : ℕ) :
    ∑ J ∈ (univ : Finset κ).powerset, bracketOne r s J.card =
      2 ^ Fintype.card κ * (((s : ℝ) + (Fintype.card κ : ℝ) / 2 - 1) * gam s +
        r * ((s : ℝ) + (Fintype.card κ : ℝ) / 2) * s) := by
  have h : ∀ J : Finset κ, bracketOne r s J.card =
      (((s : ℝ) - 1) * gam s + r * s * s) * 1 + ((gam s : ℝ) + r * s) * (J.card : ℝ) := by
    intro J; unfold bracketOne; ring
  simp_rw [h]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_one_powerset, sum_card_powerset]
  ring

/-! ## The pivot sums `eq:pivot-sums` -/

variable {ι : Type*} [Fintype ι]

/-- `A = ∑ a_T²`. -/
noncomputable def pivA (b : ι → ℝ) : ℝ := ∑ l, b l ^ 2
/-- `L = ∑ |a_T|`. -/
noncomputable def pivL (b : ι → ℝ) : ℝ := ∑ l, |b l|
/-- `U = ∑ |a_T| h(s_T)`. -/
noncomputable def pivU (b : ι → ℝ) (s : ι → ℕ) : ℝ := ∑ l, |b l| * gam (s l)
/-- `V = ∑ |a_T| (s_T - 1) h(s_T)`. -/
noncomputable def pivV (b : ι → ℝ) (s : ι → ℕ) : ℝ := ∑ l, |b l| * ((s l : ℝ) - 1) * gam (s l)
/-- `W = ∑ |a_T| s_T`. -/
noncomputable def pivW (b : ι → ℝ) (s : ι → ℕ) : ℝ := ∑ l, |b l| * s l
/-- `X = ∑ |a_T| s_T²`. -/
noncomputable def pivX (b : ι → ℝ) (s : ι → ℕ) : ℝ := ∑ l, |b l| * (s l : ℝ) ^ 2

/-- `E = 2^d [2UV + (d/2 + 1)U² + L² + r{2WX + (d/2)W²}]`. -/
noncomputable def pivE (r : ℝ) (d : ℕ) (b : ι → ℝ) (s : ι → ℕ) : ℝ :=
  2 ^ d * (2 * pivU b s * pivV b s + ((d : ℝ) / 2 + 1) * pivU b s ^ 2 + pivL b ^ 2 +
    r * (2 * pivW b s * pivX b s + (d : ℝ) / 2 * pivW b s ^ 2))

/-- `D² = (A + rE)/(1 - e)`. -/
noncomputable def pivD2 (r : ℝ) (d : ℕ) (e : ℝ) (b : ι → ℝ) (s : ι → ℕ) : ℝ :=
  (pivA b + r * pivE r d b s) / (1 - e)

/-- `K = 2^d/(1 - e) [V + (d/2)U + r{X + (d/2 + n - 1)W}]`. -/
noncomputable def pivK (r : ℝ) (d n : ℕ) (e : ℝ) (b : ι → ℝ) (s : ι → ℕ) : ℝ :=
  2 ^ d / (1 - e) * (pivV b s + (d : ℝ) / 2 * pivU b s +
    r * (pivX b s + ((d : ℝ) / 2 + n - 1) * pivW b s))

theorem pivA_nonneg (b : ι → ℝ) : 0 ≤ pivA b := sum_nonneg fun _ _ => sq_nonneg _
theorem pivL_nonneg (b : ι → ℝ) : 0 ≤ pivL b := sum_nonneg fun _ _ => abs_nonneg _
theorem pivU_nonneg (b : ι → ℝ) (s : ι → ℕ) : 0 ≤ pivU b s :=
  sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
theorem pivW_nonneg (b : ι → ℝ) (s : ι → ℕ) : 0 ≤ pivW b s :=
  sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
theorem pivX_nonneg (b : ι → ℝ) (s : ι → ℕ) : 0 ≤ pivX b s :=
  sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
theorem pivV_nonneg (b : ι → ℝ) {s : ι → ℕ} (hs : ∀ l, 1 ≤ s l) : 0 ≤ pivV b s := by
  refine sum_nonneg fun l _ => mul_nonneg (mul_nonneg (abs_nonneg _) ?_) (Nat.cast_nonneg _)
  have : (1 : ℝ) ≤ s l := by exact_mod_cast hs l
  linarith

theorem pivE_nonneg {r : ℝ} (hr : 0 ≤ r) (d : ℕ) (b : ι → ℝ) {s : ι → ℕ} (hs : ∀ l, 1 ≤ s l) :
    0 ≤ pivE r d b s := by
  unfold pivE
  have hU := pivU_nonneg b s
  have hV := pivV_nonneg b hs
  have hW := pivW_nonneg b s
  have hX := pivX_nonneg b s
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  positivity

theorem pivD2_nonneg {r : ℝ} (hr : 0 ≤ r) (d : ℕ) {e : ℝ} (he : e < 1) (b : ι → ℝ) {s : ι → ℕ}
    (hs : ∀ l, 1 ≤ s l) : 0 ≤ pivD2 r d e b s := by
  unfold pivD2
  have h1 : 0 < 1 - e := by linarith
  have := pivE_nonneg hr d b hs
  have := pivA_nonneg b
  positivity

theorem pivK_nonneg {r : ℝ} (hr : 0 ≤ r) (d : ℕ) {n : ℕ} (hn : 1 ≤ n) {e : ℝ} (he : e < 1)
    (b : ι → ℝ) {s : ι → ℕ} (hs : ∀ l, 1 ≤ s l) : 0 ≤ pivK r d n e b s := by
  unfold pivK
  have h1 : 0 < 1 - e := by linarith
  have hU := pivU_nonneg b s
  have hV := pivV_nonneg b hs
  have hW := pivW_nonneg b s
  have hX := pivX_nonneg b s
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have h2 : 0 ≤ (d : ℝ) / 2 + n - 1 := by linarith [div_nonneg hd (by norm_num : (0 : ℝ) ≤ 2)]
  have h3 : 0 ≤ pivV b s + (d : ℝ) / 2 * pivU b s +
      r * (pivX b s + ((d : ℝ) / 2 + n - 1) * pivW b s) := by positivity
  positivity

theorem sum_sum_const_mul (c : ℝ) (f g : ι → ℝ) :
    ∑ l, ∑ l', c * (f l * g l') = c * ((∑ l, f l) * ∑ l', g l') := by
  rw [sum_mul_sum, mul_sum]
  exact sum_congr rfl fun l _ => by rw [mul_sum]

/-- The second-moment error of `lem:pivot-moments`(a) is `E`:
`∑_P ∑_{T,T'} |a_T||a_{T'}| B(s_T, s_{T'}, |P|) = E`. -/
theorem sum_bracketTwo_family (r : ℝ) (b : ι → ℝ) (s : ι → ℕ) :
    ∑ J ∈ (univ : Finset κ).powerset, ∑ l, ∑ l', |b l| * |b l'| * bracketTwo r (s l) (s l') J.card =
      pivE r (Fintype.card κ) b s := by
  set d : ℝ := (Fintype.card κ : ℝ) with hd
  set c : ℝ := 2 ^ Fintype.card κ with hc
  rw [sum_comm]
  have h1 : ∀ l, ∑ J ∈ (univ : Finset κ).powerset, ∑ l',
      |b l| * |b l'| * bracketTwo r (s l) (s l') J.card =
      ∑ l', (c * ((|b l| * ((s l : ℝ) - 1) * gam (s l)) * (|b l'| * gam (s l'))) +
        c * ((|b l| * gam (s l)) * (|b l'| * ((s l' : ℝ) - 1) * gam (s l'))) +
        (c * (d / 2 + 1)) * ((|b l| * gam (s l)) * (|b l'| * gam (s l'))) +
        c * (|b l| * |b l'|) +
        (c * r) * ((|b l| * (s l : ℝ) ^ 2) * (|b l'| * s l')) +
        (c * r) * ((|b l| * s l) * (|b l'| * (s l' : ℝ) ^ 2)) +
        (c * (r * (d / 2))) * ((|b l| * s l) * (|b l'| * s l'))) := by
    intro l
    rw [sum_comm]
    refine sum_congr rfl fun l' _ => ?_
    rw [← mul_sum, sum_bracketTwo]
    ring
  rw [sum_congr rfl fun l _ => h1 l]
  simp only [sum_add_distrib, sum_sum_const_mul]
  unfold pivE pivU pivV pivL pivW pivX
  rw [← hd, ← hc]
  ring

/-- The first-moment main part of `lem:pivot-moments`(b):
`∑_P ∑_T |a_T| B₁(s_T, |P|) = 2^d [V + (d/2)U + r(X + (d/2)W)]`. -/
theorem sum_bracketOne_family (r : ℝ) (b : ι → ℝ) (s : ι → ℕ) :
    ∑ J ∈ (univ : Finset κ).powerset, ∑ l, |b l| * bracketOne r (s l) J.card =
      2 ^ Fintype.card κ * (pivV b s + (Fintype.card κ : ℝ) / 2 * pivU b s +
        r * (pivX b s + (Fintype.card κ : ℝ) / 2 * pivW b s)) := by
  rw [sum_comm]
  have h1 : ∀ l, ∑ J ∈ (univ : Finset κ).powerset, |b l| * bracketOne r (s l) J.card =
      2 ^ Fintype.card κ * (|b l| * ((s l : ℝ) - 1) * gam (s l) +
        (Fintype.card κ : ℝ) / 2 * (|b l| * gam (s l)) +
        r * (|b l| * (s l : ℝ) ^ 2 + (Fintype.card κ : ℝ) / 2 * (|b l| * s l))) := by
    intro l
    rw [← mul_sum, sum_bracketOne]
    ring
  rw [sum_congr rfl fun l _ => h1 l, ← mul_sum]
  simp only [sum_add_distrib, ← mul_sum]
  unfold pivU pivV pivW pivX
  ring

end Sarkozy.SecondOrder
