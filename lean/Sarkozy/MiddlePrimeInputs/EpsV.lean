module

public import Sarkozy.MiddlePrimeInputs.Errors
public import Sarkozy.MiddlePrimeInputs.Data
public import Sarkozy.MiddleCertificates.Defs

/-!
# The input `ε_V` of route A for L10 and L21 at every middle prime

`paper/sections/14_spectral.tex`, `lem:spec:degone`(c) and `thm:spectral-criterion`; the bar
`ε̄_V` of `cert:layer12-grid` (`paper/sections/20_middle_reference.tex`), with
`lem:spectral-monotone` for the transfer from the piece start `X` to every `p ≥ X`.

The inputs `hrowV`, `hεVc`, `hεVb` of `spectral_criterion_cut_full` (and of its `R₊` version
`spectral_criterion_cut_fullRplus`) ask for a row bound `ρ_v` of the matrix `mVcut` (`1` on the
internal edges, `min(δ^μ_k, δ^μ_l)` elsewhere) and
`ε_V = (n - 1)/(p - 1) + p/(p - 1)·r·ρ_v ≤ ε̄_V`.

* The half graphs: L10 has one internal edge `{0, 2}` and the isolated vertex `1` (degrees
  `1, 0, 1`); L21 is two triangles (all degrees `2`). So every row is at most
  `ρ_v(p) = A + B·δ_{d⋆}(p)` with `(A, B, d⋆) = (1, 1, 0)` (L10) and `(2, 3, 2)` (L21)
  (`rowV_le`, finite facts by `decide`). These are the evaluator's `nDmu`
  (`checks_spectral2.components2`), formula by formula.
* **`epsV_input`**: at every `p ≥ X_i` (any natural `p`, prime), the row bound and
  `ε_V(p) ≤ ε̄_V(X_i)`, for the 33 pieces and both cuts. The bound at `X_i` uses the rational
  `r_i ≥ X_i^{-1/2}` of `Data` and a kernel check over `ℚ` (`epsV_checks`); the passage to `p ≥ X_i`
  is `smallConst_anti` and `sqrtFactor_anti`.

The smallest relative margin `(ε̄_V - ε_V(X))/ε̄_V` is `5.4·10⁻¹¹` (L21 at `X_1`), the rounding of
the bars; the formal `ε_V` coincides with the evaluator's.
-/

@[expose] public section

namespace Sarkozy.MiddlePrimeInputs

open Finset Sarkozy.PartV Sarkozy.SpectralC Sarkozy.SpectralD.Cx Sarkozy.MiddleCertificates
  MiddleCertificates.MidCut

/-- Internal (half-graph) adjacency, in either direction, as a Boolean. -/
noncomputable def hAdj (c : MidCut) (k l : c.data.cut.Half) : Bool :=
  c.edge k.1 l.1 || c.edge l.1 k.1

theorem hAdj_iff (c : MidCut) (k l : c.data.cut.Half) :
    ((k, l) ∈ c.data.halfGraph.E ∨ (l, k) ∈ c.data.halfGraph.E) ↔ hAdj c k l = true := by
  rw [Cuts.SpecData.mem_halfGraph, Cuts.SpecData.mem_halfGraph, mem_edge, mem_edge]
  simp [hAdj]

/-- The degree of `k` in the half graph. -/
noncomputable def hDeg (c : MidCut) (k : c.data.cut.Half) : ℕ :=
  ((univ.erase k).filter (fun u => hAdj c u k = true)).card

theorem nbrCount_half (c : MidCut) (k : c.data.cut.Half) :
    Labellings.nbrCount c.data.halfGraph (univ.erase k) k = hDeg c k := by
  unfold Labellings.nbrCount hDeg
  congr 1
  exact Finset.filter_congr fun u _ => hAdj_iff c u k

/-- `|U⁺|`: `3` (L10), `6` (L21). -/
def vN : MidCut → ℕ
  | .l10 => 3
  | .l21 => 6

/-- The constants of the row bound `ρ_v = A + B·δ_{d⋆}`. -/
def vA : MidCut → ℕ
  | .l10 => 1
  | .l21 => 2

def vB : MidCut → ℕ
  | .l10 => 1
  | .l21 => 3

def vD : MidCut → ℕ
  | .l10 => 0
  | .l21 => 2

theorem card_half (c : MidCut) : Fintype.card c.data.cut.Half = vN c := by
  cases c <;> decide

/-- The number of internal neighbours of `k`, and of the other non-neighbours. -/
noncomputable def rowA (c : MidCut) (k : c.data.cut.Half) : ℕ :=
  (univ.filter (fun l => k ≠ l ∧ hAdj c k l = true)).card

noncomputable def rowB (c : MidCut) (k : c.data.cut.Half) : ℕ :=
  (univ.filter (fun l => k ≠ l ∧ hAdj c k l = false)).card

/-- The finite facts of the half graphs (`decide`). -/
theorem rowAB_le (c : MidCut) :
    ∀ k : c.data.cut.Half, rowA c k ≤ vA c ∧ rowA c k + rowB c k ≤ vA c + vB c := by
  cases c <;> decide

theorem nonadj_deg (c : MidCut) :
    ∀ k l : c.data.cut.Half, k ≠ l → hAdj c k l = false → hDeg c k = vD c ∨ hDeg c l = vD c := by
  cases c <;> decide

/-- `ρ_v(p) = A + B·δ_{d⋆}(p)`. -/
noncomputable def rhoV (c : MidCut) (p : ℕ) : ℝ := vA c + vB c * smallConst p (vD c) (vN c)

theorem term_le (c : MidCut) {p : ℕ} [Fact p.Prime] (k l : c.data.cut.Half) :
    (if k = l then 0 else mVcut p c.data k l) ≤
      (if k ≠ l ∧ hAdj c k l = true then (1 : ℝ) else 0) +
        (if k ≠ l ∧ hAdj c k l = false then (1 : ℝ) else 0) * smallConst p (vD c) (vN c) := by
  by_cases hkl : k = l
  · simp [hkl]
  · simp only [hkl, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
    unfold mVcut
    simp only [hkl, ↓reduceIte]
    by_cases ha : hAdj c k l = true
    · have he := (hAdj_iff c k l).mpr ha
      simp only [he, ↓reduceIte, ha, Bool.true_eq_false, zero_mul, add_zero, le_refl]
    · have he : ¬ ((k, l) ∈ c.data.halfGraph.E ∨ (l, k) ∈ c.data.halfGraph.E) :=
        fun h => ha ((hAdj_iff c k l).mp h)
      have hf : hAdj c k l = false := by simpa using ha
      simp only [he, ↓reduceIte, hf, Bool.false_eq_true, zero_add, one_mul]
      unfold deltaMuConst
      rw [nbrCount_half, nbrCount_half, card_half]
      rcases nonadj_deg c k l hkl hf with h | h
      · rw [h]; exact min_le_left _ _
      · rw [h]; exact min_le_right _ _

/-- **The rows of `mVcut`** are at most `ρ_v(p)`, when `0 ≤ δ_{d⋆}(p) ≤ 1`. -/
theorem rowV_le (c : MidCut) {p : ℕ} [Fact p.Prime] (h0 : 0 ≤ smallConst p (vD c) (vN c))
    (h1 : smallConst p (vD c) (vN c) ≤ 1) (k : c.data.cut.Half) :
    ∑ l, (if k = l then 0 else mVcut p c.data k l) ≤ rhoV c p := by
  refine (sum_le_sum fun l _ => term_le c k l).trans ?_
  rw [sum_add_distrib, ← sum_mul, sum_boole, sum_boole]
  set s := smallConst p (vD c) (vN c)
  have hAB := rowAB_le c k
  have ha : (rowA c k : ℝ) ≤ vA c := by exact_mod_cast hAB.1
  have hab : (rowA c k : ℝ) + rowB c k ≤ vA c + vB c := by exact_mod_cast hAB.2
  change ((rowA c k : ℕ) : ℝ) + ((rowB c k : ℕ) : ℝ) * s ≤ rhoV c p
  unfold rhoV
  nlinarith

/-- `ε_V` at the piece start over `ℚ`, with `r_i ≥ X_i^{-1/2}`. -/
def epsVQ (c : MidCut) (i : Fin 33) : ℚ :=
  ((vN c : ℚ) - 1) / ((pieceStart i : ℚ) - 1) +
    (pieceStart i : ℚ) / ((pieceStart i : ℚ) - 1) * rUp i *
      (vA c + vB c * scQ (vD c) (vN c) (pieceStart i) (rUp i))

/-- **The kernel checks at the 33 piece starts**: `e_{d⋆} < 1`, `δ_{d⋆} ≤ 1` and
`ε_V(X_i) ≤ ε̄_V(X_i)` over `ℚ`. -/
theorem epsV_checks (c : MidCut) : ∀ i : Fin 33,
    eQ (vD c) (vN c) (pieceStart i) (rUp i) < 1 ∧
      scQ (vD c) (vN c) (pieceStart i) (rUp i) ≤ 1 ∧ epsVQ c i ≤ epsV c i := by
  cases c
  all_goals
    unfold epsVQ scQ eQ rUp rUpList pieceStart pieceEnds epsV epsVList vN vA vB vD
    unfold Sarkozy.MiddleCertificates.l10EpsV Sarkozy.MiddleCertificates.l21EpsV
    decide +kernel

/-- **The input `ε_V` of route A at every `p ≥ X_i`** (`lem:spec:degone`(c),
`lem:spectral-monotone`, the bar `ε̄_V` of `cert:layer12-grid`): the rows of `mVcut` are at most
`ρ_v(p)` and `(n - 1)/(p - 1) + p/(p - 1)·r·ρ_v(p) ≤ ε̄_V(X_i)`. These are the inputs `hrowV`,
`hεVc` (with `ε_V = ε̄_V`) and `hεVb` (`le_rfl`) of `routeALower_mid`/`routeAUpper_mid` and of
the `R₊` chain. -/
theorem epsV_input (c : MidCut) (i : Fin 33) {p : ℕ} [Fact p.Prime] (hX : pieceStart i ≤ p) :
    (∀ k, ∑ l, (if k = l then 0 else mVcut p c.data k l) ≤ rhoV c p) ∧
      ((Fintype.card c.data.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) +
        (p : ℝ) / ((p : ℝ) - 1) * rp p * rhoV c p ≤ (epsV c i : ℝ) := by
  obtain ⟨he, hs1, hQ⟩ := epsV_checks c i
  obtain ⟨hr0, hr⟩ := rUp_ok i
  set X := pieceStart i with hXdef
  have hX24 : 2 ^ 24 ≤ X := pieceStart_ge i
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX24
  have hp0 : 0 < p := lt_of_lt_of_le hX0 hX
  have hX1 : (1 : ℝ) < X := by
    have : (2 : ℝ) ^ 24 ≤ X := by exact_mod_cast hX24
    linarith [show (1 : ℝ) < 2 ^ 24 by norm_num]
  have hXp : (X : ℝ) ≤ p := by exact_mod_cast hX
  have hrr := inv_sqrt_le_of_sq hr0 hr
  -- the count error and `δ_{d⋆}` at `X` and at `p`
  have heX : TraceMixing.coarseErr X (vD c) (vN c) < 1 :=
    lt_of_le_of_lt (coarseErr_le_eQ hrr _ _) (by exact_mod_cast he)
  have hep : TraceMixing.coarseErr p (vD c) (vN c) < 1 :=
    lt_of_le_of_lt (SpectralD.Root.coarseErr_antitone (by exact_mod_cast hX0) hXp _ _) heX
  have hscX := smallConst_le_scQ hX0 hrr (vD c) (vN c) he
  have hscp := smallConst_anti hX0 hX (vD c) (vN c) heX
  have hsc0 := smallConst_nonneg' hp0 (vD c) (vN c) hep
  have hs1' : (scQ (vD c) (vN c) X (rUp i) : ℝ) ≤ 1 := by exact_mod_cast hs1
  refine ⟨rowV_le c hsc0 (by linarith), ?_⟩
  rw [card_half]
  -- monotonicity in `p`
  have hn1 : (0 : ℝ) ≤ (vN c : ℝ) - 1 := by cases c <;> norm_num [vN]
  have ha : ((vN c : ℝ) - 1) / ((p : ℝ) - 1) ≤ ((vN c : ℝ) - 1) / ((X : ℝ) - 1) :=
    div_le_div_of_nonneg_left hn1 (by linarith) (by linarith)
  have hb : (p : ℝ) / ((p : ℝ) - 1) * rp p ≤ (X : ℝ) / ((X : ℝ) - 1) * (rUp i : ℝ) := by
    have h1 := sqrtFactor_anti hX1 hXp
    have h2 : (X : ℝ) / ((X : ℝ) - 1) * (Real.sqrt X)⁻¹ ≤ (X : ℝ) / ((X : ℝ) - 1) * (rUp i : ℝ) :=
      mul_le_mul_of_nonneg_left hrr (div_nonneg (by linarith) (by linarith))
    unfold rp
    linarith
  have hρ : rhoV c p ≤ (vA c : ℝ) + vB c * (scQ (vD c) (vN c) X (rUp i) : ℝ) := by
    unfold rhoV
    have : (vB c : ℝ) * smallConst p (vD c) (vN c) ≤ vB c * (scQ (vD c) (vN c) X (rUp i) : ℝ) :=
      mul_le_mul_of_nonneg_left (hscp.trans hscX) (Nat.cast_nonneg _)
    linarith
  have hρ0 : 0 ≤ rhoV c p := by unfold rhoV; positivity
  have hb0 : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) * rp p := by
    have : (1 : ℝ) < p := lt_of_lt_of_le hX1 hXp
    unfold rp; positivity
  have hprod := mul_le_mul hb hρ hρ0 (by positivity)
  have hQ' : (epsVQ c i : ℝ) ≤ (epsV c i : ℝ) := by exact_mod_cast hQ
  have hcast : (epsVQ c i : ℝ) = ((vN c : ℝ) - 1) / ((X : ℝ) - 1) +
      (X : ℝ) / ((X : ℝ) - 1) * (rUp i : ℝ) *
        ((vA c : ℝ) + vB c * (scQ (vD c) (vN c) X (rUp i) : ℝ)) := by
    unfold epsVQ
    push_cast
    ring
  linarith

end Sarkozy.MiddlePrimeInputs
