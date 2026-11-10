module

public import Sarkozy.TraceMixing.PhiBound

/-!
# The counts of one row in the form used by `phi_row_bound` (`lem:trace-mixing`(c))

Over any finite field `F` with `q` elements, for an edge `(u, v)` and a labelling `z` feasible
on `W' = W ∖ {u, v}` (`n = |W|`, `d'_u`, `d'_v` the numbers of neighbours of `u`, `v` in `W'`):

* `card_pairAdm_ge_main`: `|Φ| ≥ q² 2^{-(d'_u + d'_v + 1)} (1 - e)²` when `e^-_{d'_u}(n - 2) ≤ e`
  and `e^-_{d'_v + 1}(n - 1) ≤ e` (labelling `u` and then `v`);
* `diffCount_le_main`: `c_y ≤ q 2^{-s} (1 + e)`, `s = max(d'_u, d'_v)`, when `e^+_s ≤ e`;
* `diffCount_generic_main`: for `χ(y) = 1` and generic `y`,
  `q 2^{-t}(1 - e) ≤ c_y ≤ q 2^{-t}(1 + e)`, `t = d'_u + d'_v`, when `e^-_t(2n - 4) ≤ e`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

open Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [Fintype W] [DecidableEq W] (G : OrientedGraph W)

/-- The one-step lower count in the form `q (1 - e) ≤ 2^t |Φ_v|`. -/
theorem vertexAdmissible_ge (hW : WeilBound F) {A : Finset W} {x : W → F}
    (hx : Feasible F G A x) (v : W) {e : ℝ} (he : lowerErr (Fintype.card F) (nbrCount G A v) A.card ≤ e) :
    (Fintype.card F : ℝ) / 2 ^ nbrCount G A v * (1 - e) ≤ (vertexAdmissible G A x v).card := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℝ) < 2 ^ nbrCount G A v := pow_pos two_pos _
  have hlo := (card_vertexAdmissible hW G hx v).2
  have hexp : (Fintype.card F : ℝ) * (1 - lowerErr (Fintype.card F) (nbrCount G A v) A.card) =
      (Fintype.card F : ℝ) - softError (Fintype.card F) (nbrCount G A v) -
        2 ^ nbrCount G A v * A.card := by
    unfold lowerErr
    field_simp
    ring
  rw [div_mul_eq_mul_div, div_le_iff₀ hpow]
  have h1 : (Fintype.card F : ℝ) * (1 - e) ≤
      (Fintype.card F : ℝ) * (1 - lowerErr (Fintype.card F) (nbrCount G A v) A.card) :=
    mul_le_mul_of_nonneg_left (by linarith) hq0.le
  rw [hexp] at h1
  linarith

/-- The one-step upper count in the form `|Φ_v| ≤ q 2^{-t} (1 + e)`. -/
theorem vertexAdmissible_le (hW : WeilBound F) {A : Finset W} {x : W → F}
    (hx : Feasible F G A x) (v : W) {e : ℝ}
    (he : softError (Fintype.card F) (nbrCount G A v) / Fintype.card F ≤ e) :
    ((vertexAdmissible G A x v).card : ℝ) ≤ (Fintype.card F : ℝ) / 2 ^ nbrCount G A v * (1 + e) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℝ) < 2 ^ nbrCount G A v := pow_pos two_pos _
  have hup := (card_vertexAdmissible hW G hx v).1
  have h1 : softError (Fintype.card F) (nbrCount G A v) ≤ (Fintype.card F : ℝ) * e := by
    rw [div_le_iff₀ hq0] at he
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hpow]
  nlinarith

/-- **`|Φ| ≥ q² 2^{-(t+1)} (1 - e)²`.** -/
theorem card_pairAdm_ge_main (hW : WeilBound F) {z : W → F} {u v : W} (huv : (u, v) ∈ G.E)
    (hA : Feasible F G (restSet u v) z) {e : ℝ} (he1 : e < 1)
    (hu : lowerErr (Fintype.card F) (nbrCount G (restSet u v) u) (Fintype.card W - 2) ≤ e)
    (hv : lowerErr (Fintype.card F) (nbrCount G (restSet u v) v + 1) (Fintype.card W - 1) ≤ e) :
    (Fintype.card F : ℝ) ^ 2 /
        2 ^ (nbrCount G (restSet u v) u + nbrCount G (restSet u v) v + 1) * (1 - e) ^ 2 ≤
      (pairAdm G z u v).card := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  set A := restSet u v
  set du := nbrCount G A u
  set dv := nbrCount G A v
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have he1' : 0 < 1 - e := by linarith
  have hcardA : A.card = Fintype.card W - 2 := card_restSet huv'
  have hn2 : 2 ≤ Fintype.card W := by
    have : ({u, v} : Finset W).card ≤ Fintype.card W := card_le_univ _
    rwa [card_pair huv'] at this
  have hcardA' : (insert u A).card = Fintype.card W - 1 := by
    rw [card_insert_of_notMem (u_notMem_restSet u v), hcardA]
    omega
  have hLu := vertexAdmissible_ge G hW hA u (e := e) (by rw [hcardA]; exact hu)
  have hLv (x : F) (hx : x ∈ vertexAdmissible G A z u) :
      (Fintype.card F : ℝ) / 2 ^ (dv + 1) * (1 - e) ≤
        (vertexAdmissible G (insert u A) (Function.update z u x) v).card := by
    have hfeas := feasible_insert hA (u_notMem_restSet u v) hx
    have := vertexAdmissible_ge G hW hfeas v (e := e)
      (by rw [nbrCount_insert_u G huv, hcardA']; exact hv)
    rwa [nbrCount_insert_u G huv] at this
  have hsum := card_pairAdm_ge G huv hA
  have hsumR : ∑ x ∈ vertexAdmissible G A z u,
      ((vertexAdmissible G (insert u A) (Function.update z u x) v).card : ℝ) ≤
      (pairAdm G z u v).card := by exact_mod_cast hsum
  have hL0 : 0 ≤ (Fintype.card F : ℝ) / 2 ^ (dv + 1) * (1 - e) :=
    mul_nonneg (div_nonneg hq0.le (pow_pos two_pos _).le) he1'.le
  have h1 : ((vertexAdmissible G A z u).card : ℝ) * ((Fintype.card F : ℝ) / 2 ^ (dv + 1) * (1 - e)) ≤
      (pairAdm G z u v).card := by
    calc ((vertexAdmissible G A z u).card : ℝ) * ((Fintype.card F : ℝ) / 2 ^ (dv + 1) * (1 - e))
        = ∑ _x ∈ vertexAdmissible G A z u, (Fintype.card F : ℝ) / 2 ^ (dv + 1) * (1 - e) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ vertexAdmissible G A z u,
          ((vertexAdmissible G (insert u A) (Function.update z u x) v).card : ℝ) :=
          Finset.sum_le_sum (fun x hx => hLv x hx)
      _ ≤ _ := hsumR
  have h2 : (Fintype.card F : ℝ) / 2 ^ du * (1 - e) * ((Fintype.card F : ℝ) / 2 ^ (dv + 1) * (1 - e)) ≤
      ((vertexAdmissible G A z u).card : ℝ) * ((Fintype.card F : ℝ) / 2 ^ (dv + 1) * (1 - e)) :=
    mul_le_mul_of_nonneg_right hLu hL0
  have h3 : (Fintype.card F : ℝ) ^ 2 / 2 ^ (du + dv + 1) * (1 - e) ^ 2 =
      (Fintype.card F : ℝ) / 2 ^ du * (1 - e) * ((Fintype.card F : ℝ) / 2 ^ (dv + 1) * (1 - e)) := by
    rw [pow_add, pow_add]
    field_simp
    ring
  rw [h3]
  linarith

/-- **`c_y ≤ q 2^{-s}(1 + e)`**, `s = max(d'_u, d'_v)`. -/
theorem diffCount_le_main (hW : WeilBound F) {z : W → F} {u v : W} (huv : (u, v) ∈ G.E)
    (hA : Feasible F G (restSet u v) z) {e : ℝ}
    (hs : softError (Fintype.card F) (max (nbrCount G (restSet u v) u) (nbrCount G (restSet u v) v)) /
      Fintype.card F ≤ e) (y : F) :
    (diffCount G z u v y : ℝ) ≤ (Fintype.card F : ℝ) /
      2 ^ max (nbrCount G (restSet u v) u) (nbrCount G (restSet u v) v) * (1 + e) := by
  rcases le_total (nbrCount G (restSet u v) v) (nbrCount G (restSet u v) u) with h | h
  · rw [max_eq_left h] at hs ⊢
    have h1 : (diffCount G z u v y : ℝ) ≤ (vertexAdmissible G (restSet u v) z u).card := by
      exact_mod_cast diffCount_le_u G huv y
    exact h1.trans (vertexAdmissible_le G hW hA u hs)
  · rw [max_eq_right h] at hs ⊢
    have h1 : (diffCount G z u v y : ℝ) ≤ (vertexAdmissible G (restSet u v) z v).card := by
      exact_mod_cast diffCount_le_v G y
    exact h1.trans (vertexAdmissible_le G hW hA v hs)

/-- **The generic counts**: `q 2^{-t}(1 - e) ≤ c_y ≤ q 2^{-t}(1 + e)`. -/
theorem diffCount_generic_main (hW : WeilBound F) {z : W → F} {u v : W} (huv : (u, v) ∈ G.E)
    (hA : Feasible F G (restSet u v) z) {y : F} (hy : quadraticChar F y = 1)
    (hgen : IsGeneric G z u v y) {e : ℝ}
    (he : lowerErr (Fintype.card F) (nbrCount G (restSet u v) u + nbrCount G (restSet u v) v)
      (2 * (Fintype.card W - 2)) ≤ e) :
    (Fintype.card F : ℝ) / 2 ^ (nbrCount G (restSet u v) u + nbrCount G (restSet u v) v) *
        (1 - e) ≤ diffCount G z u v y ∧
      (diffCount G z u v y : ℝ) ≤ (Fintype.card F : ℝ) /
        2 ^ (nbrCount G (restSet u v) u + nbrCount G (restSet u v) v) * (1 + e) := by
  set t := nbrCount G (restSet u v) u + nbrCount G (restSet u v) v
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℝ) < 2 ^ t := pow_pos two_pos _
  obtain ⟨hup, hlo⟩ := diffCount_bounds G hW huv hA hy hgen
  have hsE : softError (Fintype.card F) t / Fintype.card F ≤ e :=
    (softError_div_le_lowerErr hq0 t _).trans he
  have hexp : (Fintype.card F : ℝ) * (1 - lowerErr (Fintype.card F) t (2 * (Fintype.card W - 2))) =
      (Fintype.card F : ℝ) - softError (Fintype.card F) t -
        2 ^ t * ((2 * (Fintype.card W - 2) : ℕ) : ℝ) := by
    unfold lowerErr
    field_simp
    ring
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ hpow]
    have h1 : (Fintype.card F : ℝ) * (1 - e) ≤
        (Fintype.card F : ℝ) * (1 - lowerErr (Fintype.card F) t (2 * (Fintype.card W - 2))) :=
      mul_le_mul_of_nonneg_left (by linarith) hq0.le
    rw [hexp] at h1
    linarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ hpow]
    have h1 : softError (Fintype.card F) t ≤ (Fintype.card F : ℝ) * e := by
      rw [div_le_iff₀ hq0] at hsE
      linarith
    nlinarith

end Sarkozy.TraceMixing
