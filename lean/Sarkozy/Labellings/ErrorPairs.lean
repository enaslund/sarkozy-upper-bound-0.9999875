module

public import Sarkozy.Labellings.FourCount

/-!
# One-step error pairs and sequential counts for any error pair
(`def:graphs:error-pair`, `lem:graphs:sequential`(a) in the paper's generality)

`paper/sections/12_labellings.tex`. `lem:graphs:sequential` is stated for an arbitrary one-step
error pair `(ε⁺, ε⁻)`. `extCount_bounds` (`Sequential.lean`) proves it for the graded pair of
`lem:extension`; this file proves it for any pair.

* `IsErrorPair G n εp εm`: the one-step bounds `q 2^{-t}(1 - ε⁻_t) ≤ |Φ_v(x)| ≤ q 2^{-t}(1 + ε⁺_t)`
  for every admissible set of `G` (a labelling feasible on `A`, `|A| ≤ n`, a new vertex `v` with
  `t` earlier neighbours). Every admissible set is a set `Φ` of `lem:extension`, with `t` roots
  and the at most `n` labels of `x(A)` excluded. So every one-step error pair of
  `def:graphs:error-pair` satisfies `IsErrorPair` for every graph on at most `n + 1` vertices.
* `graded_isErrorPair`: the graded pair `ε⁺_t = 𝔈_t/q`, `ε⁻_t = (𝔈_t + 2^t n)/q` is an error pair,
  from Weil (`card_vertexAdmissible`).
* `extCount_bounds_pair`: for any error pair and any ordering of `W ∖ A`,
  `main · ∏_i max(0, 1 - ε⁻_{t_i}) ≤ C_A(x) ≤ main · ∏_i (1 + ε⁺_{t_i})`, with
  `main = q^{|W|-|A|} 2^{-(|E| - |E(G[A])|)}` (`mainCount`). This is the exponentiated form of
  `main · e^{-lo} ≤ C_A(x) ≤ main · e^{up}`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [Fintype W] [DecidableEq W]

variable (F) in
/-- **`def:graphs:error-pair`** (graph form): the one-step bounds for every admissible set of `G`
with at most `n` excluded labels. -/
def IsErrorPair (G : OrientedGraph W) (n : ℕ) (εp εm : ℕ → ℝ) : Prop :=
  ∀ (A : Finset W) (x : W → F) (v : W), Feasible F G A x → v ∉ A → A.card ≤ n →
    (Fintype.card F : ℝ) / 2 ^ nbrCount G A v * (1 - εm (nbrCount G A v)) ≤
        (vertexAdmissible G A x v).card ∧
      ((vertexAdmissible G A x v).card : ℝ) ≤
        (Fintype.card F : ℝ) / 2 ^ nbrCount G A v * (1 + εp (nbrCount G A v))

/-- The graded pair of `lem:extension` is a one-step error pair, from Weil. -/
theorem graded_isErrorPair (hW : WeilBound F) (G : OrientedGraph W) (n : ℕ) :
    IsErrorPair F G n (fun t => softError (Fintype.card F) t / Fintype.card F)
      (fun t => (softError (Fintype.card F) t + 2 ^ t * n) / Fintype.card F) := by
  intro A x v hx _ hA
  obtain ⟨hup, hlo⟩ := card_vertexAdmissible hW G hx v
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h2 : (0 : ℝ) < 2 ^ nbrCount G A v := by positivity
  have hAn : (A.card : ℝ) ≤ n := by exact_mod_cast hA
  constructor
  · have e : (Fintype.card F : ℝ) / 2 ^ nbrCount G A v *
        (1 - (softError (Fintype.card F) (nbrCount G A v) + 2 ^ nbrCount G A v * n) /
          Fintype.card F) =
        ((Fintype.card F : ℝ) - softError (Fintype.card F) (nbrCount G A v) -
          2 ^ nbrCount G A v * n) / 2 ^ nbrCount G A v := by
      field_simp
      ring
    rw [e, div_le_iff₀ h2]
    have := mul_le_mul_of_nonneg_left hAn h2.le
    nlinarith
  · have e : (Fintype.card F : ℝ) / 2 ^ nbrCount G A v *
        (1 + softError (Fintype.card F) (nbrCount G A v) / Fintype.card F) =
        ((Fintype.card F : ℝ) + softError (Fintype.card F) (nbrCount G A v)) /
          2 ^ nbrCount G A v := by
      field_simp
    rw [e, le_div_iff₀ h2]
    linarith

/-- The upper product `∏_i (1 + ε⁺_{t_i})` of an error pair along an ordering. -/
noncomputable def upperErrPair (G : OrientedGraph W) (εp : ℕ → ℝ) : Finset W → List W → ℝ
  | _, [] => 1
  | A, v :: l => (1 + εp (nbrCount G A v)) * upperErrPair G εp (insert v A) l

/-- The lower product `∏_i max(0, 1 - ε⁻_{t_i})` of an error pair along an ordering. -/
noncomputable def lowerErrPair (G : OrientedGraph W) (εm : ℕ → ℝ) : Finset W → List W → ℝ
  | _, [] => 1
  | A, v :: l => max 0 (1 - εm (nbrCount G A v)) * lowerErrPair G εm (insert v A) l

omit [Fintype W] in
theorem lowerErrPair_nonneg (G : OrientedGraph W) (εm : ℕ → ℝ) :
    ∀ (l : List W) (A : Finset W), 0 ≤ lowerErrPair G εm A l
  | [], _ => by simp [lowerErrPair]
  | v :: l, A => by
      simp only [lowerErrPair]
      exact mul_nonneg (le_max_left _ _) (lowerErrPair_nonneg G εm l _)

omit [Fintype W] in
theorem upperErrPair_nonneg (G : OrientedGraph W) {εp : ℕ → ℝ} (hεp : ∀ t, 0 ≤ εp t) :
    ∀ (l : List W) (A : Finset W), 0 ≤ upperErrPair G εp A l
  | [], _ => by simp [upperErrPair]
  | v :: l, A => by
      simp only [upperErrPair]
      exact mul_nonneg (by linarith [hεp (nbrCount G A v)]) (upperErrPair_nonneg G hεp l _)

/-- The count bounds along an ordering, before the main term is evaluated:
`(q^{|l|}/2^{∑ t_i}) ∏ max(0, 1 - ε⁻) ≤ C_A(x) ≤ (q^{|l|}/2^{∑ t_i}) ∏ (1 + ε⁺)`. -/
theorem extCount_bounds_pair_aux (G : OrientedGraph W) {n : ℕ} (hn : Fintype.card W ≤ n + 1)
    {εp εm : ℕ → ℝ} (hεp : ∀ t, 0 ≤ εp t) (hpair : IsErrorPair F G n εp εm) :
    ∀ (l : List W) (A : Finset W) (x : W → F), l.Nodup → (∀ w, w ∈ A ∨ w ∈ l) →
      (∀ w ∈ l, w ∉ A) → Feasible F G A x →
      (Fintype.card F : ℝ) ^ l.length / 2 ^ sumNbr G A l * lowerErrPair G εm A l ≤
          extCount G A x ∧
        (extCount G A x : ℝ) ≤
          (Fintype.card F : ℝ) ^ l.length / 2 ^ sumNbr G A l * upperErrPair G εp A l
  | [], A, x, _, hcov, _, hx => by
      have hA : A = univ := eq_univ_of_forall fun w => (hcov w).resolve_right (by simp)
      subst hA
      rw [extCount_univ G hx]
      simp [lowerErrPair, upperErrPair, sumNbr]
  | v :: l, A, x, hnd, hcov, hdisj, hx => by
      have hv : v ∉ A := hdisj v (List.mem_cons_self ..)
      have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
      have hvl : v ∉ l := (List.nodup_cons.mp hnd).1
      have hcov' : ∀ w, w ∈ insert v A ∨ w ∈ l := fun w => by
        rcases hcov w with h | h
        · exact Or.inl (mem_insert_of_mem h)
        · rcases List.mem_cons.mp h with rfl | h'
          · exact Or.inl (mem_insert_self _ _)
          · exact Or.inr h'
      have hdisj' : ∀ w ∈ l, w ∉ insert v A := fun w hw hmem => by
        rcases mem_insert.mp hmem with rfl | h
        · exact hvl hw
        · exact hdisj w (List.mem_cons_of_mem _ hw) h
      have hIH : ∀ c ∈ vertexAdmissible G A x v,
          (Fintype.card F : ℝ) ^ l.length / 2 ^ sumNbr G (insert v A) l *
              lowerErrPair G εm (insert v A) l ≤
              extCount G (insert v A) (Function.update x v c) ∧
            (extCount G (insert v A) (Function.update x v c) : ℝ) ≤
              (Fintype.card F : ℝ) ^ l.length / 2 ^ sumNbr G (insert v A) l *
                upperErrPair G εp (insert v A) l := fun c hc =>
        extCount_bounds_pair_aux G hn hεp hpair l (insert v A) _ hnd' hcov' hdisj'
          (feasible_insert hx hv hc)
      have hrec := extCount_insert G x hv
      have hrecR : (extCount G A x : ℝ) = ∑ c ∈ vertexAdmissible G A x v,
          (extCount G (insert v A) (Function.update x v c) : ℝ) := by exact_mod_cast hrec
      have hAn : A.card ≤ n := by
        have h1 : A.card < Fintype.card W :=
          card_lt_card ⟨subset_univ A, fun h => hv (h (mem_univ v))⟩ |>.trans_eq card_univ
        omega
      obtain ⟨hlo, hup⟩ := hpair A x v hx hv hAn
      set t := nbrCount G A v
      set Φ := vertexAdmissible G A x v
      have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
      have h2 : (0 : ℝ) < 2 ^ t := by positivity
      have hstepL : max 0 ((Fintype.card F : ℝ) / 2 ^ t * (1 - εm t)) ≤ Φ.card :=
        max_le (Nat.cast_nonneg _) hlo
      have hmaxL : (Fintype.card F : ℝ) / 2 ^ t * max 0 (1 - εm t) =
          max 0 ((Fintype.card F : ℝ) / 2 ^ t * (1 - εm t)) := by
        rw [mul_max_of_nonneg _ _ (by positivity), mul_zero]
      simp only [lowerErrPair, upperErrPair, sumNbr, List.length_cons]
      have hpow : (Fintype.card F : ℝ) ^ (l.length + 1) / 2 ^ (t + sumNbr G (insert v A) l) =
          ((Fintype.card F : ℝ) / 2 ^ t) *
            ((Fintype.card F : ℝ) ^ l.length / 2 ^ sumNbr G (insert v A) l) := by
        rw [pow_succ, pow_add]; field_simp
      rw [hpow]
      have hL0 := lowerErrPair_nonneg G εm l (insert v A)
      have hU0 := upperErrPair_nonneg G hεp l (insert v A)
      have hB0 : (0 : ℝ) ≤ (Fintype.card F : ℝ) ^ l.length / 2 ^ sumNbr G (insert v A) l := by
        positivity
      constructor
      · have hsum : (Φ.card : ℝ) * ((Fintype.card F : ℝ) ^ l.length / 2 ^ sumNbr G (insert v A) l *
            lowerErrPair G εm (insert v A) l) ≤ (extCount G A x : ℝ) := by
          rw [hrecR, ← nsmul_eq_mul, ← sum_const]
          exact sum_le_sum fun c hc => (hIH c hc).1
        calc (Fintype.card F : ℝ) / 2 ^ t *
              ((Fintype.card F : ℝ) ^ l.length / 2 ^ sumNbr G (insert v A) l) *
              (max 0 (1 - εm t) * lowerErrPair G εm (insert v A) l)
            = max 0 ((Fintype.card F : ℝ) / 2 ^ t * (1 - εm t)) *
                ((Fintype.card F : ℝ) ^ l.length / 2 ^ sumNbr G (insert v A) l *
                  lowerErrPair G εm (insert v A) l) := by
              rw [← hmaxL]; ring
          _ ≤ (Φ.card : ℝ) * ((Fintype.card F : ℝ) ^ l.length / 2 ^ sumNbr G (insert v A) l *
                lowerErrPair G εm (insert v A) l) :=
              mul_le_mul_of_nonneg_right hstepL (mul_nonneg hB0 hL0)
          _ ≤ (extCount G A x : ℝ) := hsum
      · have hsum : (extCount G A x : ℝ) ≤ (Φ.card : ℝ) *
            ((Fintype.card F : ℝ) ^ l.length / 2 ^ sumNbr G (insert v A) l *
              upperErrPair G εp (insert v A) l) := by
          rw [hrecR, ← nsmul_eq_mul, ← sum_const]
          exact sum_le_sum fun c hc => (hIH c hc).2
        calc (extCount G A x : ℝ) ≤ (Φ.card : ℝ) *
              ((Fintype.card F : ℝ) ^ l.length / 2 ^ sumNbr G (insert v A) l *
                upperErrPair G εp (insert v A) l) := hsum
          _ ≤ ((Fintype.card F : ℝ) / 2 ^ t * (1 + εp t)) *
              ((Fintype.card F : ℝ) ^ l.length / 2 ^ sumNbr G (insert v A) l *
                upperErrPair G εp (insert v A) l) :=
              mul_le_mul_of_nonneg_right hup (mul_nonneg hB0 hU0)
          _ = (Fintype.card F : ℝ) / 2 ^ t *
              ((Fintype.card F : ℝ) ^ l.length / 2 ^ sumNbr G (insert v A) l) *
              ((1 + εp t) * upperErrPair G εp (insert v A) l) := by ring

/-- **`lem:graphs:sequential`(a) for any one-step error pair**: along an ordering `l` of `W ∖ A`,
`main · ∏ max(0, 1 - ε⁻_{t_i}) ≤ C_A(x) ≤ main · ∏ (1 + ε⁺_{t_i})`. -/
theorem extCount_bounds_pair (G : OrientedGraph W) {n : ℕ} (hn : Fintype.card W ≤ n + 1)
    {εp εm : ℕ → ℝ} (hεp : ∀ t, 0 ≤ εp t) (hpair : IsErrorPair F G n εp εm)
    {l : List W} {A : Finset W} {x : W → F} (hnd : l.Nodup) (hcov : ∀ w, w ∈ A ∨ w ∈ l)
    (hdisj : ∀ w ∈ l, w ∉ A) (hx : Feasible F G A x) :
    mainCount G (Fintype.card F) A * lowerErrPair G εm A l ≤ extCount G A x ∧
      (extCount G A x : ℝ) ≤ mainCount G (Fintype.card F) A * upperErrPair G εp A l := by
  have h := extCount_bounds_pair_aux G hn hεp hpair l A x hnd hcov hdisj hx
  have hmain : (Fintype.card F : ℝ) ^ l.length / 2 ^ sumNbr G A l = mainCount G (Fintype.card F) A := by
    rw [mainCount, length_of_ordering hnd hcov hdisj]
    have := sumNbr_add_edgeCount G l A hnd hcov hdisj
    rw [show sumNbr G A l = edgeCount G univ - edgeCount G A by omega]
  rwa [hmain] at h

end Sarkozy.Labellings
