module

public import Sarkozy.TraceMixing.PairRow

/-!
# A pair, explicit form (`lem:trace-mixing`(c))

`paper/sections/12_labellings.tex`, `lem:trace-mixing`(c), for the graph law `λ_p(G)` and an
edge `(u, v)`: with `d'_u`, `d'_v` the numbers of neighbours of `u`, `v` in `W' = W ∖ {u, v}`
(`deg - 1`), `t = d'_u + d'_v`, `s = max(d'_u, d'_v)`, `n_× = d'_u d'_v`, and `e < 1` with
`e ≥ e_t(p, 2n - 4)`, `e ≥ e_{s+1}(p, n)`,
`‖T_{uv} f‖² ≤ max(φ_gen² + 2n_×/(p-1) · φ_exc², 2^{t+1}/((p-1)(1-e)²)) ‖f‖²`
for mean-zero `f` (`trace_mixing_explicit`; the bound is `explicitBound`).

The proof is the paper's: `trace_mixing_pair` (b), `phiPair_pairJoint` and
`sum_sq_condMatrix_pairJoint` identify the two terms with `φ_y` and `E[1/|Φ|]`, the counts of
`PairCount.lean`/`PairRow.lean` bound `c_y` and `|Φ|`, and `phi_row_bound` gives the first term.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.TraceMixing

open Sarkozy.Mixing Sarkozy.Labellings

/-- The right-hand side of `lem:trace-mixing`(c). -/
noncomputable def explicitBound (p e : ℝ) (t s nx : ℕ) : ℝ :=
  max ((3 * e / (1 - e) ^ 2 + (1 + e) * (nx * 2 ^ (t - s + 1) / (p - 1))) ^ 2 +
        2 * nx / (p - 1) * (2 ^ (t - s) * (1 + e) / (1 - e) ^ 2) ^ 2)
      (2 ^ (t + 1) / ((p - 1) * (1 - e) ^ 2))

theorem coarseErr_nonneg {q : ℝ} (hq : 0 < q) (t n : ℕ) : 0 ≤ coarseErr q t n := by
  unfold coarseErr
  have h1 := coarseH_nonneg t
  have h2 : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h3 : 0 ≤ (n : ℝ) / q := div_nonneg (Nat.cast_nonneg _) hq.le
  have h4 : (0 : ℝ) ≤ 2 ^ t := (pow_pos two_pos t).le
  exact mul_nonneg h4 (add_nonneg (mul_nonneg h1 h2) h3)

variable {p : ℕ} [Fact p.Prime]
variable {W : Type*} [Fintype W] [DecidableEq W]
variable (G : OrientedGraph W) (hne : (injLabellings (ZMod p) G).Nonempty)

/-- The labels `z'` extended by `0` at `u` and `v`. -/
def zRest {u v : W} (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p) : W → ZMod p :=
  pairCombine 0 0 r

omit [Fintype W] in
theorem pairCombine_eq_pairExt {u v : W} (huv : u ≠ v) (x x' : ZMod p)
    (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p) :
    pairCombine x x' r = pairExt (zRest r) u v x x' := by
  funext w
  unfold pairExt zRest
  by_cases hwv : w = v
  · subst hwv
    rw [Function.update_self, pairCombine_v huv]
  · rw [Function.update_of_ne hwv]
    by_cases hwu : w = u
    · subst hwu
      rw [Function.update_self, pairCombine_u]
    · rw [Function.update_of_ne hwu]
      have hw : w ∉ ({u, v} : Finset W) := by simp [hwu, hwv]
      rw [show w = ((⟨w, hw⟩ : {w // w ∉ ({u, v} : Finset W)}) : W) from rfl,
        pairCombine_rest, pairCombine_rest]

theorem pairAdmissible_eq {u v : W} (huv : u ≠ v)
    (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p) :
    pairAdmissible G r = pairAdm G (zRest r) u v := by
  ext ω
  rw [mem_pairAdm, ← mem_injLabellings_iff, ← pairCombine_eq_pairExt huv]
  unfold pairAdmissible
  simp

theorem feasible_zRest {u v : W} (huv : u ≠ v) (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p)
    (hr : tgtWeight (pairJoint (graphLaw G hne) u v) r ≠ 0) :
    Feasible (ZMod p) G (restSet u v) (zRest r) := by
  have hne' : (pairAdmissible G r).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    apply hr
    unfold tgtWeight
    apply Finset.sum_eq_zero
    intro ω _
    rw [pairJoint_weight_eq G hne huv, h]
    simp
  obtain ⟨ω, hω⟩ := hne'
  rw [pairAdmissible_eq G huv] at hω
  have hf := (mem_pairAdm G).mp hω
  exact feasible_congr' G (fun a ha => pairExt_rest ω.1 ω.2 ha)
    (feasible_mono G (subset_univ _) hf)

/-- **`lem:trace-mixing`(c), explicit form.** -/
theorem trace_mixing_explicit (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2) {u v : W}
    (huv : (u, v) ∈ G.E) {e : ℝ} (he1 : e < 1)
    (het : coarseErr p (nbrCount G (restSet u v) u + nbrCount G (restSet u v) v)
      (2 * Fintype.card W - 4) ≤ e)
    (hes : coarseErr p (max (nbrCount G (restSet u v) u) (nbrCount G (restSet u v) v) + 1)
      (Fintype.card W) ≤ e)
    (f : ZMod p × ZMod p → ℝ)
    (hf : ∑ ω, srcWeight (pairJoint (graphLaw G hne) u v) ω * f ω = 0) :
    ∑ r, tgtWeight (pairJoint (graphLaw G hne) u v) r *
        condOp (pairJoint (graphLaw G hne) u v) f r ^ 2 ≤
      explicitBound p e (nbrCount G (restSet u v) u + nbrCount G (restSet u v) v)
          (max (nbrCount G (restSet u v) u) (nbrCount G (restSet u v) v))
          (nbrCount G (restSet u v) u * nbrCount G (restSet u v) v) *
        ∑ ω, srcWeight (pairJoint (graphLaw G hne) u v) ω * f ω ^ 2 := by
  classical
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  have hpP : p.Prime := Fact.out
  have hp3 : (3 : ℝ) ≤ p := by
    have h2 : 2 ≤ p := hpP.two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hp0 : (0 : ℝ) < p := by linarith
  have hcard : (Fintype.card (ZMod p) : ℝ) = p := by rw [ZMod.card]
  have hn2 : 2 ≤ Fintype.card W := by
    have : ({u, v} : Finset W).card ≤ Fintype.card W := card_le_univ _
    rwa [card_pair huv'] at this
  set κ := pairJoint (graphLaw G hne) u v with hκ
  set du := nbrCount G (restSet u v) u with hdu
  set dv := nbrCount G (restSet u v) v with hdv
  set t := du + dv with ht
  set s := max du dv with hs
  set nx := du * dv with hnx
  have hst : s ≤ t := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have he0 : 0 ≤ e := (coarseErr_nonneg hp0 _ _).trans het
  have he1' : 0 < 1 - e := by linarith
  -- the error terms
  have hu : lowerErr (Fintype.card (ZMod p)) du (Fintype.card W - 2) ≤ e := by
    rw [hcard]
    refine (lowerErr_le_coarseErr (by linarith) _ _).trans ((coarseErr_mono hp0 ?_ ?_).trans hes)
    · exact (le_max_left du dv).trans (Nat.le_succ _)
    · omega
  have hv : lowerErr (Fintype.card (ZMod p)) (dv + 1) (Fintype.card W - 1) ≤ e := by
    rw [hcard]
    refine (lowerErr_le_coarseErr (by linarith) _ _).trans ((coarseErr_mono hp0 ?_ ?_).trans hes)
    · exact Nat.succ_le_succ (le_max_right du dv)
    · omega
  have hsE : softError (Fintype.card (ZMod p)) s / Fintype.card (ZMod p) ≤ e := by
    rw [hcard]
    refine (softError_div_le_lowerErr hp0 s (Fintype.card W)).trans
      ((lowerErr_le_coarseErr (by linarith) _ _).trans ((coarseErr_mono hp0 ?_ le_rfl).trans hes))
    exact Nat.le_succ _
  have hgenE : lowerErr (Fintype.card (ZMod p)) t (2 * (Fintype.card W - 2)) ≤ e := by
    rw [hcard]
    have h2n : 2 * (Fintype.card W - 2) = 2 * Fintype.card W - 4 := by omega
    rw [h2n]
    exact (lowerErr_le_coarseErr (by linarith) _ _).trans het
  -- the row bounds
  set Q := univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = 1) with hQ
  set B₁ : ℝ := (3 * e / (1 - e) ^ 2 + (1 + e) * (nx * 2 ^ (t - s + 1) / (p - 1))) ^ 2 +
      2 * nx / (p - 1) * (2 ^ (t - s) * (1 + e) / (1 - e) ^ 2) ^ 2 with hB₁
  set B₂ : ℝ := 2 ^ (t + 1) / ((p - 1) * (1 - e) ^ 2) with hB₂
  have hrow (r : {w // w ∉ ({u, v} : Finset W)} → ZMod p) (hr : tgtWeight κ r ≠ 0) :
      2 / ((p : ℝ) - 1) * ∑ y ∈ Q, phiPair κ r y ^ 2 ≤ B₁ ∧
        ∑ ω, condMatrix κ r ω ^ 2 ≤ 2 ^ (t + 1) / ((p : ℝ) ^ 2 * (1 - e) ^ 2) := by
    have hA := feasible_zRest G hne huv' r hr
    set z := zRest r with hz
    have hP : ((pairAdmissible G r).card : ℝ) = (pairAdm G z u v).card := by
      rw [pairAdmissible_eq G huv']
    have hPlo := card_pairAdm_ge_main G hW huv hA he1 hu hv
    rw [hcard] at hPlo
    have hP0 : 0 < ((pairAdm G z u v).card : ℝ) := lt_of_lt_of_le
      (mul_pos (div_pos (pow_pos hp0 2) (pow_pos two_pos _)) (pow_pos he1' 2)) hPlo
    constructor
    · have hphi (y : ZMod p) : phiPair κ r y =
          ((p : ℝ) - 1) / 2 * (diffCount G z u v y : ℝ) / (pairAdm G z u v).card - 1 := by
        rw [phiPair_pairJoint G hne huv' r hr y, ← hP, mul_div_assoc]
        congr 3
        rw [pairAdmissible_eq G huv']
        rfl
      simp only [hphi]
      refine phi_row_bound Q (IsGeneric G z u v) hp3 rfl (card_squares hp2) he0 he1 hst
        (fun y => (diffCount G z u v y : ℝ)) (fun y _ => Nat.cast_nonneg _)
        (card_pairAdm_eq_sum G huv) ?_ ?_ ?_ ?_
      · exact hPlo
      · intro y _
        have := diffCount_le_main G hW huv hA hsE y
        rwa [hcard] at this
      · intro y hy hgen
        have hy' : quadraticChar (ZMod p) y = 1 := (mem_filter.mp hy).2
        have := diffCount_generic_main G hW huv hA hy' hgen hgenE
        rwa [hcard] at this
      · have h1 : (Q.filter fun y => ¬ IsGeneric G z u v y).card ≤
            (univ.filter fun y => ¬ IsGeneric G z u v y).card := by
          apply card_le_card
          intro y hy
          simp only [mem_filter] at hy ⊢
          exact ⟨mem_univ _, hy.2⟩
        have h2 := card_nongeneric_le G z u v
        have h3 : (Q.filter fun y => ¬ IsGeneric G z u v y).card ≤ nx := by
          refine h1.trans (le_trans (le_of_eq ?_) h2)
          congr 1
        exact_mod_cast h3
    · rw [sum_sq_condMatrix_pairJoint G hne huv' r hr, hP]
      rw [div_le_div_iff₀ hP0 (mul_pos (pow_pos hp0 2) (pow_pos he1' 2)), one_mul]
      have h1 : (p : ℝ) ^ 2 / 2 ^ (t + 1) * (1 - e) ^ 2 * 2 ^ (t + 1) =
          (p : ℝ) ^ 2 * (1 - e) ^ 2 := by
        field_simp
      have h2 := mul_le_mul_of_nonneg_right hPlo (pow_pos two_pos (t + 1)).le
      rw [h1] at h2
      linarith
  -- the two terms
  have hAterm : ∑ r, tgtWeight κ r * (2 / ((p : ℝ) - 1) * ∑ y ∈ Q, phiPair κ r y ^ 2) ≤ B₁ := by
    calc ∑ r, tgtWeight κ r * (2 / ((p : ℝ) - 1) * ∑ y ∈ Q, phiPair κ r y ^ 2)
        ≤ ∑ r, tgtWeight κ r * B₁ := by
          apply Finset.sum_le_sum
          intro r _
          by_cases hr : tgtWeight κ r = 0
          · rw [hr, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (hrow r hr).1 (tgtWeight_nonneg κ r)
      _ = B₁ := by rw [← Finset.sum_mul, sum_tgtWeight, one_mul]
  have hBterm : (p : ℝ) * ∑ r, tgtWeight κ r * ∑ ω, condMatrix κ r ω ^ 2 ≤ B₂ := by
    have h1 : ∑ r, tgtWeight κ r * ∑ ω, condMatrix κ r ω ^ 2 ≤
        2 ^ (t + 1) / ((p : ℝ) ^ 2 * (1 - e) ^ 2) := by
      calc ∑ r, tgtWeight κ r * ∑ ω, condMatrix κ r ω ^ 2
          ≤ ∑ r, tgtWeight κ r * (2 ^ (t + 1) / ((p : ℝ) ^ 2 * (1 - e) ^ 2)) := by
            apply Finset.sum_le_sum
            intro r _
            by_cases hr : tgtWeight κ r = 0
            · rw [hr, zero_mul, zero_mul]
            · exact mul_le_mul_of_nonneg_left (hrow r hr).2 (tgtWeight_nonneg κ r)
        _ = 2 ^ (t + 1) / ((p : ℝ) ^ 2 * (1 - e) ^ 2) := by
            rw [← Finset.sum_mul, sum_tgtWeight, one_mul]
    calc (p : ℝ) * ∑ r, tgtWeight κ r * ∑ ω, condMatrix κ r ω ^ 2
        ≤ (p : ℝ) * (2 ^ (t + 1) / ((p : ℝ) ^ 2 * (1 - e) ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 hp0.le
      _ ≤ B₂ := by
          rw [hB₂]
          have hq1 : (0 : ℝ) < p - 1 := by linarith
          have hY : (0 : ℝ) < (1 - e) ^ 2 := pow_pos he1' 2
          have hX : (0 : ℝ) < 2 ^ (t + 1) := pow_pos two_pos _
          rw [mul_div_assoc', div_le_div_iff₀ (mul_pos (pow_pos hp0 2) hY) (mul_pos hq1 hY)]
          have h2 : (0 : ℝ) ≤ 2 ^ (t + 1) * (1 - e) ^ 2 * p := by positivity
          nlinarith [h2]
  have hmain := trace_mixing_pair G hne hp2 huv f hf
  have hE : 0 ≤ ∑ ω, srcWeight κ ω * f ω ^ 2 :=
    Finset.sum_nonneg (fun ω _ => mul_nonneg (srcWeight_nonneg κ ω) (sq_nonneg _))
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ hE)
  unfold explicitBound
  exact max_le_max hAterm hBterm

end Sarkozy.TraceMixing
