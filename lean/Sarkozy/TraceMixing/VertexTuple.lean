module

public import Sarkozy.TraceMixing.VertexMarginal

/-!
# The conditional law of a tuple (`lem:graphs:vertex`(e))

`paper/sections/12_labellings.tex`, `lem:graphs:vertex`(e), over any finite field `F` with `q`
elements. Let `W = V ⊔ C ⊔ U`, let `x_C` be a feasible labelling of `C`, order `V` (`lV`), and
let `t_i` be the number of neighbours of the `i`-th vertex of `V` in `C` and among the earlier
vertices of `V`. The conditional probability of `z_V = y_V` given `z_C = x_C` is
`C(x_C, y_V)/C(x_C)`, with `C` the completion counts (`extCount`).

* `tuple_support`: it vanishes unless `(x_C, y_V)` is feasible on `C ∪ V` (in particular `y_V`
  is injective).
* `tuple_density`: `q^{|V|} · C(x_C, y_V)/C(x_C) ≤ R_U / tupleProd`, where
  `tupleProd = ∏_i (1 - e_{t_i}(q, n))/2^{t_i}` (`tupleProd`): the density with respect to the
  uniform law on `𝔽^V` is at most `2^{t_V} R_U/∏_i (1 - e_{t_i}(q, n))`.
* `tuple_density_coarse`: the coarser bound `2^{t_V} R_U/(1 - e_Δ(q, n))^{|V|}`, with
  `t_V = tupleEdges` (`tupleProd_ge`).

The proof counts the completions of `x_C` along the ordering `lV ++ lU` (`lowerProd_append`),
so no separate count of the admissible tuples is needed.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

open Sarkozy.Mixing Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [Fintype W] [DecidableEq W] (G : OrientedGraph W)

omit [Fintype W] in
/-- `lowerProd` along a concatenated ordering. -/
theorem lowerProd_append (q : ℝ) (n : ℕ) :
    ∀ (l₁ l₂ : List W) (A : Finset W),
      lowerProd G q n A (l₁ ++ l₂) = lowerProd G q n A l₁ * lowerProd G q n (A ∪ l₁.toFinset) l₂
  | [], l₂, A => by simp [lowerProd]
  | v :: l₁, l₂, A => by
      have hset : insert v A ∪ l₁.toFinset = A ∪ (v :: l₁).toFinset := by
        ext w
        simp only [mem_union, mem_insert, List.toFinset_cons, List.mem_toFinset]
        tauto
      simp only [List.cons_append, lowerProd]
      rw [lowerProd_append q n l₁ l₂ (insert v A), hset]
      ring

/-- `∏_i (1 - e_{t_i}(q, n))/2^{t_i}` along an ordering. -/
noncomputable def tupleProd (q : ℝ) (n : ℕ) : Finset W → List W → ℝ
  | _, [] => 1
  | A, v :: l => (1 - coarseErr q (nbrCount G A v) n) / 2 ^ nbrCount G A v * tupleProd q n (insert v A) l

omit [Fintype W] in
/-- `q^{|l|} · ∏_i (1 - e_{t_i})/2^{t_i} ≤ lowerProd(A, l)` when every `e_{t_i} ≤ 1`. -/
theorem tupleProd_le_lowerProd {q : ℝ} (hq : 1 ≤ q) (n : ℕ) :
    ∀ (l : List W) (A : Finset W), (∀ v ∈ l, ∀ B : Finset W, coarseErr q (nbrCount G B v) n ≤ 1) →
      q ^ l.length * tupleProd G q n A l ≤ lowerProd G q n A l ∧ 0 ≤ tupleProd G q n A l
  | [], A, _ => by simp [tupleProd, lowerProd]
  | v :: l, A, he => by
      obtain ⟨ih, ih0⟩ := tupleProd_le_lowerProd hq n l (insert v A)
        (fun w hw B => he w (List.mem_cons_of_mem _ hw) B)
      have hq0 : 0 < q := by linarith
      set t := nbrCount G A v
      have hev := he v List.mem_cons_self A
      have hpow : (0 : ℝ) < 2 ^ t := pow_pos two_pos t
      have hstep : q * ((1 - coarseErr q t n) / 2 ^ t) ≤ stepLower q n t := by
        unfold stepLower
        refine le_max_of_le_right ?_
        have hle : Sarkozy.TraceMixing.lowerErr q t n ≤ coarseErr q t n := lowerErr_le_coarseErr hq t n
        have hexp : (q - softError q t - 2 ^ t * n) / 2 ^ t =
            q / 2 ^ t * (1 - Sarkozy.TraceMixing.lowerErr q t n) := by
          unfold Sarkozy.TraceMixing.lowerErr
          field_simp
          ring
        rw [hexp, mul_div_assoc', div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hpow.le
        nlinarith
      have hfac0 : 0 ≤ (1 - coarseErr q t n) / 2 ^ t := div_nonneg (by linarith) hpow.le
      simp only [tupleProd, lowerProd, List.length_cons, pow_succ]
      refine ⟨?_, mul_nonneg hfac0 ih0⟩
      have hL0 : 0 ≤ lowerProd G q n (insert v A) l := lowerProd_nonneg G q n l _
      calc q ^ l.length * q * ((1 - coarseErr q t n) / 2 ^ t * tupleProd G q n (insert v A) l)
          = (q * ((1 - coarseErr q t n) / 2 ^ t)) *
              (q ^ l.length * tupleProd G q n (insert v A) l) := by ring
        _ ≤ stepLower q n t * lowerProd G q n (insert v A) l :=
            mul_le_mul hstep ih (mul_nonneg (pow_nonneg hq0.le _) ih0)
              (le_trans (mul_nonneg hq0.le hfac0) hstep)

/-- **(e) The conditional law is supported on the feasible (in particular injective) tuples.** -/
theorem tuple_support {C V : Finset W} {y : W → F}
    (hy : extCount G (C ∪ V) y ≠ 0) : Feasible F G (C ∪ V) y :=
  feasible_of_extCount_ne_zero G hy

/-- **(e) The density of the conditional law of `z_V` given `z_C = x_C`**: for a feasible
labelling `x` of `C`, orderings `lV` of `V` and `lU` of `U = W ∖ (C ∪ V)`, and any labelling `y`
(for `y` agreeing with `x` on `C`, `C(x_C, y_V)/C(x_C)` is the conditional probability of `y_V`),
`q^{|V|} · C(x_C, y_V) ≤ (R_U / tupleProd(C, lV)) · C(x_C)`, that is the conditional density
with respect to the uniform law on `𝔽^V` is at most `2^{t_V} R_U/∏_i (1 - e_{t_i}(q, n))`. -/
theorem tuple_density (hW : WeilBound F) {n : ℕ} (hn : Fintype.card W ≤ n)
    (hS1 : ∀ i, coarseErr (Fintype.card F) (degree G i) n < 1) (C : Finset W) (lV lU : List W)
    (hnd : (lV ++ lU).Nodup) (hcov : ∀ w, w ∈ C ∨ w ∈ lV ++ lU) (hdisj : ∀ w ∈ lV ++ lU, w ∉ C)
    (x : W → F) (hx : Feasible F G C x) (y : W → F) :
    (Fintype.card F : ℝ) ^ lV.length * tupleProd G (Fintype.card F) n C lV *
        extCount G (C ∪ lV.toFinset) y ≤
      RY G (Fintype.card F) n lU.toFinset * extCount G C x := by
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq0 : (0 : ℝ) < Fintype.card F := by linarith
  set q : ℝ := (Fintype.card F : ℝ) with hq
  -- the lower count of `C(x_C)` along `lV ++ lU`
  have hlow := (extCount_bounds hW G hn (lV ++ lU) C x hnd hcov hdisj hx).1
  rw [lowerProd_append] at hlow
  -- the completions of `(x_C, y_V)` along `lU`
  have hndU : lU.Nodup := (List.nodup_append.mp hnd).2.1
  have hcovU : ∀ w, w ∈ C ∪ lV.toFinset ∨ w ∈ lU := by
    intro w
    rcases hcov w with h | h
    · exact Or.inl (mem_union_left _ h)
    · rcases List.mem_append.mp h with h' | h'
      · exact Or.inl (mem_union_right _ (List.mem_toFinset.mpr h'))
      · exact Or.inr h'
  have hdisjU : ∀ w ∈ lU, w ∉ C ∪ lV.toFinset := by
    intro w hw hmem
    rcases mem_union.mp hmem with h | h
    · exact hdisj w (List.mem_append_right _ hw) h
    · have hdis := (List.nodup_append.mp hnd).2.2
      exact hdis w (List.mem_toFinset.mp h) w hw rfl
  by_cases hfeas : Feasible F G (C ∪ lV.toFinset) y
  · have hup := (extCount_bounds hW G hn lU (C ∪ lV.toFinset) y hndU hcovU hdisjU hfeas).2
    obtain ⟨hratio, hlpos⟩ := upperProd_le_RY G hq1 hS1 lU (C ∪ lV.toFinset)
    have hRl : (lU.map fun i => (1 + coarseErr q (degree G i) n) /
        (1 - coarseErr q (degree G i) n)).prod = RY G q n lU.toFinset := by
      unfold RY
      rw [List.prod_toFinset _ hndU]
    rw [hRl] at hratio
    have he1 : ∀ v ∈ lV, ∀ B : Finset W, coarseErr q (nbrCount G B v) n ≤ 1 := by
      intro v _ B
      exact ((coarseErr_mono hq0 (nbrCount_le_degree G B v) le_rfl).trans (hS1 v).le)
    obtain ⟨htp, htp0⟩ := tupleProd_le_lowerProd G hq1 n lV C he1
    have hlV0 : 0 ≤ lowerProd G q n C lV := lowerProd_nonneg G q n lV C
    have hR0 : 0 ≤ RY G q n lU.toFinset := by
      unfold RY
      apply prod_nonneg
      intro i _
      apply div_nonneg
      · have := coarseErr_nonneg hq0 (degree G i) n
        linarith
      · linarith [hS1 i]
    have hext0 : (0 : ℝ) ≤ extCount G (C ∪ lV.toFinset) y := Nat.cast_nonneg _
    calc q ^ lV.length * tupleProd G q n C lV * extCount G (C ∪ lV.toFinset) y
        ≤ lowerProd G q n C lV * upperProd G q (C ∪ lV.toFinset) lU :=
          mul_le_mul htp hup hext0 hlV0
      _ ≤ lowerProd G q n C lV *
            (RY G q n lU.toFinset * lowerProd G q n (C ∪ lV.toFinset) lU) :=
          mul_le_mul_of_nonneg_left hratio hlV0
      _ = RY G q n lU.toFinset * (lowerProd G q n C lV * lowerProd G q n (C ∪ lV.toFinset) lU) := by
          ring
      _ ≤ RY G q n lU.toFinset * extCount G C x := mul_le_mul_of_nonneg_left hlow hR0
  · have h0 : extCount G (C ∪ lV.toFinset) y = 0 := by
      by_contra h
      exact hfeas (tuple_support G h)
    rw [h0, Nat.cast_zero, mul_zero]
    apply mul_nonneg _ (Nat.cast_nonneg _)
    unfold RY
    apply prod_nonneg
    intro i _
    apply div_nonneg
    · have := coarseErr_nonneg hq0 (degree G i) n
      linarith
    · linarith [hS1 i]

/-- `t_V = ∑_i t_i` along an ordering. -/
noncomputable def tupleEdges : Finset W → List W → ℕ
  | _, [] => 0
  | A, v :: l => nbrCount G A v + tupleEdges (insert v A) l

omit [Fintype W] in
/-- `∏_i (1 - e_{t_i})/2^{t_i} ≥ (1 - e_Δ)^{|V|}/2^{t_V}` when every `t_i ≤ Δ`. -/
theorem tupleProd_ge {q : ℝ} (hq : 1 ≤ q) (n : ℕ) {Δ : ℕ} (hΔ1 : coarseErr q Δ n ≤ 1) :
    ∀ (l : List W) (A : Finset W), (∀ v ∈ l, ∀ B : Finset W, nbrCount G B v ≤ Δ) →
      (1 - coarseErr q Δ n) ^ l.length / 2 ^ tupleEdges G A l ≤ tupleProd G q n A l
  | [], A, _ => by simp [tupleProd, tupleEdges]
  | v :: l, A, hΔ => by
      have ih := tupleProd_ge hq n hΔ1 l (insert v A)
        (fun w hw B => hΔ w (List.mem_cons_of_mem _ hw) B)
      have hq0 : 0 < q := by linarith
      set t := nbrCount G A v
      have ht : t ≤ Δ := hΔ v List.mem_cons_self A
      have hmono : coarseErr q t n ≤ coarseErr q Δ n := coarseErr_mono hq0 ht le_rfl
      have he0 : 0 ≤ 1 - coarseErr q Δ n := by linarith
      have h2t : (0 : ℝ) < 2 ^ t := pow_pos two_pos t
      have h2E : (0 : ℝ) < 2 ^ tupleEdges G (insert v A) l := pow_pos two_pos _
      have hfac : (1 - coarseErr q Δ n) / 2 ^ t ≤ (1 - coarseErr q t n) / 2 ^ t :=
        div_le_div_of_nonneg_right (by linarith) h2t.le
      have hfac0 : 0 ≤ (1 - coarseErr q Δ n) / 2 ^ t := div_nonneg he0 h2t.le
      simp only [tupleProd, tupleEdges, List.length_cons, pow_succ, pow_add]
      calc (1 - coarseErr q Δ n) ^ l.length * (1 - coarseErr q Δ n) /
            (2 ^ t * 2 ^ tupleEdges G (insert v A) l)
          = (1 - coarseErr q Δ n) / 2 ^ t *
              ((1 - coarseErr q Δ n) ^ l.length / 2 ^ tupleEdges G (insert v A) l) := by
            rw [div_mul_div_comm, mul_comm ((1 - coarseErr q Δ n) ^ l.length)]
        _ ≤ (1 - coarseErr q t n) / 2 ^ t * tupleProd G q n (insert v A) l :=
            mul_le_mul hfac ih (div_nonneg (pow_nonneg he0 _) h2E.le) (le_trans hfac0 hfac)

/-- **(e), coarse form**: the conditional density of `z_V` given `z_C = x_C` with respect to the
uniform law on `𝔽^V` is at most `2^{t_V} R_U/(1 - e_Δ(q, n))^{|V|}`, written as
`q^{|V|} (1 - e_Δ)^{|V|}/2^{t_V} · C(x_C, y_V) ≤ R_U · C(x_C)`. -/
theorem tuple_density_coarse (hW : WeilBound F) {n : ℕ} (hn : Fintype.card W ≤ n)
    (hS1 : ∀ i, coarseErr (Fintype.card F) (degree G i) n < 1) {Δ : ℕ}
    (hΔ : ∀ i, degree G i ≤ Δ) (hΔ1 : coarseErr (Fintype.card F) Δ n ≤ 1) (C : Finset W)
    (lV lU : List W) (hnd : (lV ++ lU).Nodup) (hcov : ∀ w, w ∈ C ∨ w ∈ lV ++ lU)
    (hdisj : ∀ w ∈ lV ++ lU, w ∉ C) (x : W → F) (hx : Feasible F G C x) (y : W → F) :
    (Fintype.card F : ℝ) ^ lV.length *
        ((1 - coarseErr (Fintype.card F) Δ n) ^ lV.length / 2 ^ tupleEdges G C lV) *
        extCount G (C ∪ lV.toFinset) y ≤
      RY G (Fintype.card F) n lU.toFinset * extCount G C x := by
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hge := tupleProd_ge G hq1 n hΔ1 lV C
    (fun v _ B => (nbrCount_le_degree G B v).trans (hΔ v))
  have hmain := tuple_density G hW hn hS1 C lV lU hnd hcov hdisj x hx y
  have hpow : (0 : ℝ) ≤ (Fintype.card F : ℝ) ^ lV.length := pow_nonneg (by linarith) _
  have hext : (0 : ℝ) ≤ extCount G (C ∪ lV.toFinset) y := Nat.cast_nonneg _
  calc (Fintype.card F : ℝ) ^ lV.length *
        ((1 - coarseErr (Fintype.card F) Δ n) ^ lV.length / 2 ^ tupleEdges G C lV) *
        extCount G (C ∪ lV.toFinset) y
      ≤ (Fintype.card F : ℝ) ^ lV.length * tupleProd G (Fintype.card F) n C lV *
          extCount G (C ∪ lV.toFinset) y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hge hpow) hext
    _ ≤ RY G (Fintype.card F) n lU.toFinset * extCount G C x := hmain

end Sarkozy.TraceMixing
