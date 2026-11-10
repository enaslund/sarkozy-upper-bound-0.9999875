module

public import Sarkozy.PartVLaws.TailSchur

@[expose] public section

/-!
# The count-type Schur-row data of a row datum read off a pair of graph laws

`paper/sections/25_upper_reference.tex`, `def:record:upper-bands`, items (F1), (F3), (F5)(b);
`paper/sections/12_labellings.tex`, `lem:graphs:sequential`(b).

`TailCounts` and `TailSchur` prove the count-type fields of the Schur-row data for the two-layer
rows of the coordinate `0` of the tail law. The proofs use only the following structure, which
the other three row families of the tail datum (coordinate `1`; the one-layer rows) share:

* the vertices are `W ≃ Fin 3 × V` (the three rows; `e`), and the row coordinates are `Q ≃ V`
  (`c`); the rows of a labelling are `rowRead e c`;
* the fold law and the matching law are the laws of the rows under `Inj_p(G₁)`, `Inj_p(G₂)`;
* `G₁` and `G₂` have the same edges between vertices off the row `2`, and between vertices off
  the row `0` (`FrameEdges`), so the same restrictions to these sets (and to the middle row) are
  feasible.

**`frame_schurRowData`** gives, under these assumptions at a prime `p ≥ P₄` with at most `72`
vertices of degree at most `20` and Weil's bound, the Schur-row data with `H = ρ^{144}`,
`R_m = ρ^{288}`, `υ = ρ^{288} - 1` (`ρ = 1 + 2²⁸/√p`), given the two correlation bounds (F4).
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord

section Frame

variable {p : ℕ} [Fact p.Prime] {W V Q : Type} [Fintype W] [DecidableEq W] [Fintype Q]
  [DecidableEq Q]

/-- The rows of a labelling of `W ≃ Fin 3 × V`, in the row coordinates `Q ≃ V`. -/
def rowRead (e : Fin 3 × V ≃ W) (c : Q ≃ V) (y : W → ZMod p) (i : Fin 3) (q : Q) : ZMod p :=
  y (e (i, c q))

/-- The vertices of the row `i`. -/
def rowSet (e : Fin 3 × V ≃ W) (i : Fin 3) : Finset W := univ.filter fun w => (e.symm w).1 = i

/-- The vertices off the row `j`. -/
def offSet (e : Fin 3 × V ≃ W) (j : Fin 3) : Finset W := univ.filter fun w => (e.symm w).1 ≠ j

/-- A middle-row labelling as a labelling of `W`. -/
def liftMid (e : Fin 3 × V ≃ W) (c : Q ≃ V) (b : Q → ZMod p) (w : W) : ZMod p :=
  b (c.symm (e.symm w).2)

/-- Labellings of the rows `0, 1` as a labelling of `W`. -/
def liftLow (e : Fin 3 × V ≃ W) (c : Q ≃ V) (b : Fin 2 → Q → ZMod p) (w : W) : ZMod p :=
  if h : (e.symm w).1 = Fin.last 2 then 0 else b ((e.symm w).1.castPred h) (c.symm (e.symm w).2)

/-- Labellings of the rows `1, 2` as a labelling of `W`. -/
def liftHigh (e : Fin 3 × V ≃ W) (c : Q ≃ V) (b : Fin 2 → Q → ZMod p) (w : W) : ZMod p :=
  if h : (e.symm w).1 = 0 then 0 else b ((e.symm w).1.pred h) (c.symm (e.symm w).2)

omit [Fact p.Prime] [DecidableEq W] [Fintype Q] [DecidableEq Q] in
theorem readsSet_mid (e : Fin 3 × V ≃ W) (c : Q ≃ V) :
    ReadsSet (rowSet e 1) (fun y : W → ZMod p => rowRead e c y 1) (liftMid e c) := by
  intro y b
  constructor
  · rintro rfl a ha
    have ha1 : (e.symm a).1 = 1 := (mem_filter.mp ha).2
    simp only [liftMid, rowRead, Equiv.apply_symm_apply]
    have : ((1 : Fin 3), (e.symm a).2) = e.symm a := Prod.ext ha1.symm rfl
    rw [this, Equiv.apply_symm_apply]
  · intro h
    funext q
    have := h (e (1, c q)) (mem_filter.mpr ⟨mem_univ _, by simp⟩)
    simp only [liftMid, Equiv.symm_apply_apply] at this
    exact this

omit [DecidableEq W] [Fintype Q] [DecidableEq Q] in
theorem readsSet_low (e : Fin 3 × V ≃ W) (c : Q ≃ V) :
    ReadsSet (offSet e (Fin.last 2)) (fun (y : W → ZMod p) (i : Fin 2) => rowRead e c y i.castSucc)
      (liftLow e c) := by
  intro y b
  constructor
  · rintro rfl a ha
    have ha2 : (e.symm a).1 ≠ Fin.last 2 := (mem_filter.mp ha).2
    simp only [liftLow, ha2, ↓reduceDIte, rowRead, Fin.castSucc_castPred, Equiv.apply_symm_apply,
      Prod.mk.eta]
  · intro h
    funext i q
    have := h (e (i.castSucc, c q))
      (mem_filter.mpr ⟨mem_univ _, by simpa using Fin.castSucc_ne_last i⟩)
    simp only [liftLow, Equiv.symm_apply_apply, Fin.castSucc_ne_last, ↓reduceDIte,
      Fin.castPred_castSucc] at this
    exact this

omit [DecidableEq W] [Fintype Q] [DecidableEq Q] in
theorem readsSet_high (e : Fin 3 × V ≃ W) (c : Q ≃ V) :
    ReadsSet (offSet e 0) (fun (y : W → ZMod p) (i : Fin 2) => rowRead e c y i.succ)
      (liftHigh e c) := by
  intro y b
  constructor
  · rintro rfl a ha
    have ha0 : (e.symm a).1 ≠ 0 := (mem_filter.mp ha).2
    simp only [liftHigh, ha0, ↓reduceDIte, rowRead, Fin.succ_pred, Equiv.apply_symm_apply,
      Prod.mk.eta]
  · intro h
    funext i q
    have := h (e (i.succ, c q)) (mem_filter.mpr ⟨mem_univ _, by simp⟩)
    simp only [liftHigh, Equiv.symm_apply_apply, Fin.succ_ne_zero, ↓reduceDIte,
      Fin.pred_succ] at this
    exact this

/-- **The edge condition of a row frame**: `G₁` and `G₂` have the same edges between vertices
off the row `2`, and between vertices off the row `0`. -/
structure FrameEdges (G1 G2 : OrientedGraph W) (e : Fin 3 × V ≃ W) : Prop where
  low : ∀ a b : W, (e.symm a).1 ≠ Fin.last 2 → (e.symm b).1 ≠ Fin.last 2 →
    ((a, b) ∈ G1.E ↔ (a, b) ∈ G2.E)
  high : ∀ a b : W, (e.symm a).1 ≠ 0 → (e.symm b).1 ≠ 0 → ((a, b) ∈ G1.E ↔ (a, b) ∈ G2.E)

omit [Fintype W] [DecidableEq W] in
/-- Graphs with the same edges inside `A` have the same feasible restrictions to `A`. -/
theorem feasible_iff_of_edges {G1 G2 : OrientedGraph W} {A : Finset W}
    (hE : ∀ a b : W, a ∈ A → b ∈ A → ((a, b) ∈ G1.E ↔ (a, b) ∈ G2.E)) (x : W → ZMod p) :
    Feasible (ZMod p) G1 A x ↔ Feasible (ZMod p) G2 A x := by
  constructor
  · intro h
    exact ⟨h.1, fun e he h1 h2 => h.2 e ((hE e.1 e.2 h1 h2).mpr he) h1 h2⟩
  · intro h
    exact ⟨h.1, fun e he h1 h2 => h.2 e ((hE e.1 e.2 h1 h2).mp he) h1 h2⟩

omit [DecidableEq W] in
theorem FrameEdges.feas_low {G1 G2 : OrientedGraph W} {e : Fin 3 × V ≃ W} (H : FrameEdges G1 G2 e)
    (x : W → ZMod p) :
    Feasible (ZMod p) G1 (offSet e (Fin.last 2)) x ↔
      Feasible (ZMod p) G2 (offSet e (Fin.last 2)) x :=
  feasible_iff_of_edges (fun a b ha hb => H.low a b (mem_filter.mp ha).2 (mem_filter.mp hb).2) x

omit [DecidableEq W] in
theorem FrameEdges.feas_high {G1 G2 : OrientedGraph W} {e : Fin 3 × V ≃ W}
    (H : FrameEdges G1 G2 e) (x : W → ZMod p) :
    Feasible (ZMod p) G1 (offSet e 0) x ↔ Feasible (ZMod p) G2 (offSet e 0) x :=
  feasible_iff_of_edges (fun a b ha hb => H.high a b (mem_filter.mp ha).2 (mem_filter.mp hb).2) x

omit [DecidableEq W] in
theorem FrameEdges.feas_mid {G1 G2 : OrientedGraph W} {e : Fin 3 × V ≃ W}
    (H : FrameEdges G1 G2 e) (x : W → ZMod p) :
    Feasible (ZMod p) G1 (rowSet e 1) x ↔ Feasible (ZMod p) G2 (rowSet e 1) x := by
  refine feasible_iff_of_edges (fun a b ha hb => H.high a b ?_ ?_) x
  · rw [(mem_filter.mp ha).2]
    decide
  · rw [(mem_filter.mp hb).2]
    decide

variable (hW : WeilBound (ZMod p)) (hp : P4 ≤ p) (hW72 : Fintype.card W ≤ 72)
  (G1 G2 : OrientedGraph W) (hne1 : (injLabellings (ZMod p) G1).Nonempty)
  (hne2 : (injLabellings (ZMod p) G2).Nonempty) (hdeg1 : ∀ v, nbrCount G1 univ v ≤ 20)
  (hdeg2 : ∀ v, nbrCount G2 univ v ≤ 20) (e : Fin 3 × V ≃ W) (c : Q ≃ V)
  (HE : FrameEdges G1 G2 e) (πE πF : FiniteLaw (Fin 3 → Q → ZMod p))
  (hπE : πE = (graphLaw G2 hne2).map (rowRead e c))
  (hπF : πF = (graphLaw G1 hne1).map (rowRead e c)) (hS : GamSupported πE πF)

include hW hp hW72 hdeg1 hdeg2 HE hπE hπF hS in
/-- **The fold mass of a row frame**: `ρ^{-144} ≤ m_b ≤ ρ^{144}` on the support of `ν`. -/
theorem frame_mass_bounds {b : Q → ZMod p} (hb : (nuOf πE).weight b ≠ 0) :
    (countRho p ^ 144)⁻¹ ≤ kf (nubOf πE b) (kernelOf πE πF b) (fun _ => 1) (fun _ => 1) ∧
      kf (nubOf πE b) (kernelOf πE πF b) (fun _ => 1) (fun _ => 1) ≤ countRho p ^ 144 := by
  rw [kf_fold_one πE πF hS hb]
  have e1 : πF.map (fun ω => ω 1) = (graphLaw G1 hne1).map (fun y => rowRead e c y 1) := by
    rw [hπF, map_map']
    rfl
  have e2 : nuOf πE = (graphLaw G2 hne2).map (fun y => rowRead e c y 1) := by
    rw [nuOf, hπE, map_map']
    rfl
  rw [e1, e2]
  rw [e2] at hb
  exact restriction_ratio_bounds p hW hp hW72 G1 G2 hne1 hne2 hdeg1 hdeg2 (readsSet_mid e c)
    (HE.feas_mid) b hb

include hW hp hW72 hdeg1 hdeg2 HE hπE hπF hS in
/-- **The row sums of the fold kernel of a row frame** lie in `[ρ^{-144}, ρ^{144}]`. -/
theorem frame_kone_bounds {b : Q → ZMod p} (hb : (nuOf πE).weight b ≠ 0) {x : Q → ZMod p}
    (hx : (nubOf πE b).weight x ≠ 0) :
    (countRho p ^ 144)⁻¹ ≤ kone (nubOf πE b) (kernelOf πE πF b) x ∧
      kone (nubOf πE b) (kernelOf πE πF b) x ≤ countRho p ^ 144 := by
  rw [kone_fold πE πF hS hb hx]
  have eF : gamOf πF =
      (graphLaw G1 hne1).map (fun y (i : Fin 2) => rowRead e c y i.castSucc) := by
    rw [gamOf, hπF, map_map']
    rfl
  have eE : gamOf πE =
      (graphLaw G2 hne2).map (fun y (i : Fin 2) => rowRead e c y i.castSucc) := by
    rw [gamOf, hπE, map_map']
    rfl
  have hg : (gamOf πE).weight ![x, b] ≠ 0 := by
    rw [gamOf_weight πE ![x, b]]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact mul_ne_zero hb hx
  rw [eF, eE]
  rw [eE] at hg
  exact restriction_ratio_bounds p hW hp hW72 G1 G2 hne1 hne2 hdeg1 hdeg2 (readsSet_low e c)
    (HE.feas_low) ![x, b] hg

include hW hp hW72 hdeg1 hdeg2 HE hπE hπF hS in
/-- **The column sums of the fold kernel of a row frame** lie in `[ρ^{-144}, ρ^{144}]`. -/
theorem frame_kone'_bounds
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → Q → ZMod p), πE.weight (ω ∘ σ) = πE.weight ω)
    {b : Q → ZMod p} (hb : (nuOf πE).weight b ≠ 0) {y : Q → ZMod p}
    (hy : (nubOf πE b).weight y ≠ 0) :
    (countRho p ^ 144)⁻¹ ≤ kone' (nubOf πE b) (kernelOf πE πF b) y ∧
      kone' (nubOf πE b) (kernelOf πE πF b) y ≤ countRho p ^ 144 := by
  rw [kone'_fold πE πF hS hb hy]
  have hnum : ∑ x, πF.weight ![x, b, y] =
      ((graphLaw G1 hne1).map (fun z (i : Fin 2) => rowRead e c z i.succ)).weight ![b, y] := by
    rw [← map_succ_weight_eq_sum πF b y, hπF, map_map']
    rfl
  have hden : (gamOf πE).weight ![y, b] =
      ((graphLaw G2 hne2).map (fun z (i : Fin 2) => rowRead e c z i.succ)).weight ![b, y] := by
    rw [gamOf_weight_eq_sum,
      show (∑ x, πE.weight ![y, b, x]) = ∑ x, πE.weight ![x, b, y] from
        sum_congr rfl fun x _ => piE_swap02 πE hexch y b x,
      ← map_succ_weight_eq_sum πE b y, hπE, map_map']
    rfl
  have hg : (gamOf πE).weight ![y, b] ≠ 0 := by
    rw [gamOf_weight πE ![y, b]]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact mul_ne_zero hb hy
  rw [hnum, hden]
  rw [hden] at hg
  exact restriction_ratio_bounds p hW hp hW72 G1 G2 hne1 hne2 hdeg1 hdeg2 (readsSet_high e c)
    (HE.feas_high) ![b, y] hg

include hW hp hW72 hdeg1 hdeg2 HE hπE hπF hS in
/-- **The count-type Schur-row data of a row frame** (`SchurRowData` given the correlations
(F4)): `H = ρ^{144}`, `R_m = ρ^{288}`, `υ = ρ^{288} - 1`. -/
theorem frame_schurRowData
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → Q → ZMod p), πE.weight (ω ∘ σ) = πE.weight ω)
    {b : Q → ZMod p} (hb : (nuOf πE).weight b ≠ 0) {ρF ρE : ℝ}
    (hcorr : ∀ g g' : (Q → ZMod p) → ℝ,
      |kf (nubOf πE b) (covKernel (nubOf πE b) (kernelOf πE πF b)) g g'| ≤
        ρF * Real.sqrt (wvar (nubOf πE b) (margL (nubOf πE b) (kernelOf πE πF b)) g) *
          Real.sqrt (wvar (nubOf πE b) (margR (nubOf πE b) (kernelOf πE πF b)) g'))
    (hnormE : NormBound (nubOf πE b) (kernelOf πE πE b) ρE) :
    SchurRowData (nubOf πE b) (kernelOf πE πF b) (kernelOf πE πE b)
      (countRho p ^ 144) (countRho p ^ 288 - 1) (countRho p ^ 288) ρF ρE := by
  obtain ⟨m1, m2⟩ := frame_mass_bounds hW hp hW72 G1 G2 hne1 hne2 hdeg1 hdeg2 e c HE πE πF hπE hπF
    hS hb
  have hρ : 1 ≤ countRho p ^ 144 := one_le_pow₀ (one_le_countRho p)
  have hρ288 : 1 ≤ countRho p ^ 288 := one_le_pow₀ (one_le_countRho p)
  have hυ : 0 ≤ countRho p ^ 288 - 1 := by linarith
  have hL : ∀ x, (nubOf πE b).weight x ≠ 0 →
      (countRho p ^ 288)⁻¹ ≤ margL (nubOf πE b) (kernelOf πE πF b) x ∧
        margL (nubOf πE b) (kernelOf πE πF b) x ≤ countRho p ^ 288 := by
    intro x hx
    obtain ⟨k1, k2⟩ := frame_kone_bounds hW hp hW72 G1 G2 hne1 hne2 hdeg1 hdeg2 e c HE πE πF hπE
      hπF hS hb hx
    have := div_bounds hρ k1 k2 m1 m2
    rw [← pow_mul] at this
    exact this
  have hR : ∀ y, (nubOf πE b).weight y ≠ 0 →
      (countRho p ^ 288)⁻¹ ≤ margR (nubOf πE b) (kernelOf πE πF b) y ∧
        margR (nubOf πE b) (kernelOf πE πF b) y ≤ countRho p ^ 288 := by
    intro y hy
    obtain ⟨k1, k2⟩ := frame_kone'_bounds hW hp hW72 G1 G2 hne1 hne2 hdeg1 hdeg2 e c HE πE πF hπE
      hπF hS hexch hb hy
    have := div_bounds hρ k1 k2 m1 m2
    rw [← pow_mul] at this
    exact this
  refine ⟨m1, m2, kernelOf_nonneg πE πF b, fun x hx => (hL x hx).2, fun y hy => (hR y hy).2,
    ?_, ?_, hcorr, kernelOf_exactE πE hexch hb, hnormE⟩
  · refine nrm_le_of_abs_le _ _ hυ fun x hx => ?_
    exact abs_sub_one_le hρ288 (hL x hx).1 (hL x hx).2
  · refine nrm_le_of_abs_le _ _ hυ fun y hy => ?_
    exact abs_sub_one_le hρ288 (hR y hy).1 (hR y hy).2

end Frame

/-- **Schur inputs from Schur-row data with `1 ≤ H ≤ 1 + 2⁻²⁰⁰`** and `M = 21/20`. -/
theorem schurInputs_of_rowData {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] (D : Datum 𝔛) {r : ℝ}
    {I : CompletionInput} (hM : (I.M : ℝ) = 21 / 20) {H υ Rm ρF ρE : ℝ} (hH1 : 1 ≤ H)
    (hH2 : H ≤ 1 + 1 / 2 ^ 200) (hRm : 0 ≤ Rm) (hρF : 0 ≤ ρF)
    (hf : (H * Rm * ρF + (H + 50 * H ^ 2) * υ ^ 2) / r ≤ (I.f : ℝ)) (hh : ρE / r ≤ (I.h : ℝ))
    (hb : ∀ b, D.nu.weight b ≠ 0 → SchurRowData (D.nub b) (D.TF b) (D.TE b) H υ Rm ρF ρE) :
    SchurInputs D r I := by
  refine ⟨H, υ, Rm, ρF, ρE, lt_of_lt_of_le zero_lt_one hH1, ?_, ?_, hRm, hρF, hf, hh, hb⟩
  · have : (1 : ℝ) + 1 / 2 ^ 200 ≤ 50 := by norm_num
    linarith
  · rw [hM]
    have : (1 : ℝ) + 1 / 2 ^ 200 + 1 / 50 ≤ 21 / 20 := by norm_num
    linarith

end Sarkozy.PartVLaws
