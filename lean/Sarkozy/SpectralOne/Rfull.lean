module

public import Sarkozy.SpectralOne.PaleyOneCut
public import Sarkozy.Cuts.CutCount
public import Sarkozy.TraceMixing.PhiBound

@[expose] public section

/-!
# The constant `R_full` of `lem:spec2:paley-one` in the paper's form

`paper/sections/14_spectral.tex`, `lem:spec2:paley-one`:
`R_full = ∏_{i ∈ U⁺} (1 + e_{d⁰_i}(p, n))/(1 − e_{d⁰_i}(p, n))`, and in its proof
`max w/min w ≤ R_ν R_{U⁺∖J} ≤ R_ν R_full`.

`hzeta_cut` takes `R_full` as any bound `U_J ≤ R_full L_J` on the ratio of the upper and lower
products of `lem:extension` along `(U⁺ ∖ J).toList`. Here:

* `upperProd_le_mul_lowerProd`: along any ordering of new vertices `v` with at most `d_v`
  neighbours already placed and `e_{d_v}(q, n) < 1`,
  `U ≤ ∏_v (1 + e_{d_v})/(1 − e_{d_v}) · L` (the step comparisons `stepUpper_le_coarse`,
  `coarse_le_stepLower` of `Cuts.CutCount`, and `e_t` nondecreasing in `t`); `lowerProd_pos_of`:
  then `L > 0`;
* `RfullPaper`: the paper's `R_full`, with `d⁰_i` the degree of `i` in `G⁺`;
* `lowJ_pos`, `upJ_le_RfullPaper`: the hypotheses `hLJ`, `hRJ` of `hzeta_cut` for every `J`,
  from `e_{d⁰_i}(p, m) < 1`;
* **`hzeta_cut_paper`**: `|t_J| ≤ ζ r` on the non-coverable `J` with the paper's
  `ζ = (R_cut R_full − 1) + m/((p − m) r)`;
* `lt_of_coarseErr_lt_one`: `e_Δ(p, n') < 1` forces `n' < p` (so `m < p` follows from (S1)).

New material for this paper.
-/

namespace Sarkozy.SpectralOne

attribute [local instance] feasibleDec

open Finset Sarkozy.SpectralC Sarkozy.Labellings

/-- The ratio `(1 + e_t(q, n))/(1 − e_t(q, n))`. -/
noncomputable def ratioE (q : ℝ) (n t : ℕ) : ℝ :=
  (1 + TraceMixing.coarseErr q t n) / (1 - TraceMixing.coarseErr q t n)

lemma one_le_ratioE {q : ℝ} (hq : 0 < q) {n t : ℕ} (he : TraceMixing.coarseErr q t n < 1) :
    1 ≤ ratioE q n t := by
  unfold ratioE
  have h0 := TraceMixing.coarseErr_nonneg hq t n
  rw [le_div_iff₀ (by linarith)]
  linarith

section Products

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- One step: `stepUpper ≤ ((1 + e_d)/(1 − e_d)) stepLower` for `t ≤ d` and `e_d < 1`. -/
lemma stepUpper_le_ratio {q : ℝ} (hq : 1 ≤ q) (n : ℕ) {t d : ℕ} (htd : t ≤ d)
    (he : TraceMixing.coarseErr q d n < 1) :
    stepUpper q t ≤ ratioE q n d * stepLower q n t := by
  have hq0 : 0 < q := by linarith
  have hmono := TraceMixing.coarseErr_mono hq0 htd (le_refl n)
  have h0 := TraceMixing.coarseErr_nonneg hq0 d n
  have hu := Cuts.SpecData.stepUpper_le_coarse hq n t
  have hl := Cuts.SpecData.coarse_le_stepLower hq n t
  have hpos : 0 < 1 - TraceMixing.coarseErr q d n := by linarith
  have hqt : 0 < q / 2 ^ t := by positivity
  calc stepUpper q t ≤ q / 2 ^ t * (1 + TraceMixing.coarseErr q t n) := hu
    _ ≤ q / 2 ^ t * (1 + TraceMixing.coarseErr q d n) :=
        mul_le_mul_of_nonneg_left (by linarith) hqt.le
    _ = ratioE q n d * (q / 2 ^ t * (1 - TraceMixing.coarseErr q d n)) := by
        unfold ratioE; field_simp
    _ ≤ ratioE q n d * (q / 2 ^ t * (1 - TraceMixing.coarseErr q t n)) := by
        apply mul_le_mul_of_nonneg_left _ (by unfold ratioE; positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) hqt.le
    _ ≤ ratioE q n d * stepLower q n t :=
        mul_le_mul_of_nonneg_left hl (by unfold ratioE; positivity)

/-- A vertex has at most `d⁰_v = #(neighbours of v)` neighbours in any set. -/
lemma nbrCount_le_deg (G : OrientedGraph U) (A : Finset U) (v : U) :
    nbrCount G A v ≤ nbrCount G (univ.erase v) v := by
  unfold nbrCount
  refine card_le_card fun u hu => ?_
  obtain ⟨-, hE⟩ := mem_filter.mp hu
  refine mem_filter.mpr ⟨mem_erase.mpr ⟨?_, mem_univ _⟩, hE⟩
  rintro rfl
  rcases hE with h | h <;> exact G.loopless u h

omit [Fintype U] in
/-- **`U ≤ ∏_v (1 + e_{d_v})/(1 − e_{d_v}) · L`** along an ordering `l` of new vertices, when no
vertex has more than `d_v` neighbours in any set. -/
theorem upperProd_le_mul_lowerProd (G : OrientedGraph U) {q : ℝ} (hq : 1 ≤ q) (n : ℕ)
    (d : U → ℕ) (hd : ∀ (A : Finset U) v, nbrCount G A v ≤ d v)
    (he : ∀ v, TraceMixing.coarseErr q (d v) n < 1) :
    ∀ (l : List U) (A : Finset U),
      upperProd G q A l ≤ (l.map fun v => ratioE q n (d v)).prod * lowerProd G q n A l
  | [], _ => by simp [upperProd, lowerProd]
  | v :: l, A => by
      have hq0 : 0 < q := by linarith
      have ih := upperProd_le_mul_lowerProd G hq n d hd he l (insert v A)
      have hstep := stepUpper_le_ratio hq n (hd A v) (he v)
      have hR0 : 0 ≤ (l.map fun v => ratioE q n (d v)).prod := by
        refine List.prod_nonneg fun x hx => ?_
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx
        exact zero_le_one.trans (one_le_ratioE hq0 (he w))
      have hrv : 0 ≤ ratioE q n (d v) := zero_le_one.trans (one_le_ratioE hq0 (he v))
      simp only [upperProd, lowerProd, List.map_cons, List.prod_cons]
      calc stepUpper q (nbrCount G A v) * upperProd G q (insert v A) l
          ≤ (ratioE q n (d v) * stepLower q n (nbrCount G A v)) *
              ((l.map fun v => ratioE q n (d v)).prod * lowerProd G q n (insert v A) l) :=
            mul_le_mul hstep ih (upperProd_nonneg G hq0.le l _)
              (mul_nonneg hrv (le_max_left _ _))
        _ = ratioE q n (d v) * (l.map fun v => ratioE q n (d v)).prod *
              (stepLower q n (nbrCount G A v) * lowerProd G q n (insert v A) l) := by ring

omit [Fintype U] in
/-- **`L > 0`** when every step error is below `1`. -/
theorem lowerProd_pos_of (G : OrientedGraph U) {q : ℝ} (hq : 1 ≤ q) (n : ℕ)
    (d : U → ℕ) (hd : ∀ (A : Finset U) v, nbrCount G A v ≤ d v)
    (he : ∀ v, TraceMixing.coarseErr q (d v) n < 1) :
    ∀ (l : List U) (A : Finset U), 0 < lowerProd G q n A l
  | [], _ => by simp [lowerProd]
  | v :: l, A => by
      have hq0 : 0 < q := by linarith
      have ih := lowerProd_pos_of G hq n d hd he l (insert v A)
      simp only [lowerProd]
      refine mul_pos ?_ ih
      have hmono := TraceMixing.coarseErr_mono hq0 (hd A v) (le_refl n)
      have hl := Cuts.SpecData.coarse_le_stepLower hq n (nbrCount G A v)
      have hqt : 0 < q / 2 ^ (nbrCount G A v) := by positivity
      have : 0 < q / 2 ^ (nbrCount G A v) * (1 - TraceMixing.coarseErr q (nbrCount G A v) n) :=
        mul_pos hqt (by linarith [he v])
      linarith

end Products

/-! ## The cut laws -/

section Cut

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- The degree `d⁰_i` of `i` in `G⁺`. -/
noncomputable def deg0 (i : D.cut.Half) : ℕ := nbrCount D.halfGraph (univ.erase i) i

/-- **The paper's `R_full = ∏_{i ∈ U⁺} (1 + e_{d⁰_i}(p, m))/(1 − e_{d⁰_i}(p, m))`**. -/
noncomputable def RfullPaper (m : ℕ) : ℝ := ∏ i : D.cut.Half, ratioE p m (deg0 D i)

lemma one_le_card_zmod : (1 : ℝ) ≤ (Fintype.card (ZMod p) : ℕ) := by
  rw [ZMod.card]; exact_mod_cast (Fact.out : p.Prime).one_lt.le

lemma one_le_RfullPaper {m : ℕ} (he : ∀ i, TraceMixing.coarseErr p (deg0 D i) m < 1) :
    1 ≤ RfullPaper (p := p) D m := by
  have hq0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold RfullPaper
  exact one_le_prod₀ fun i _ => one_le_ratioE hq0 (he i)

/-- `hLJ` of `hzeta_cut`: `L_J > 0` for every `J`. -/
theorem lowJ_pos {m : ℕ} (he : ∀ i, TraceMixing.coarseErr p (deg0 D i) m < 1)
    (J : Finset D.cut.Half) : 0 < lowJ (p := p) D m J := by
  unfold lowJ
  have hc : ((Fintype.card (ZMod p) : ℕ) : ℝ) = p := by rw [ZMod.card]
  refine lowerProd_pos_of D.halfGraph one_le_card_zmod m (deg0 D)
    (fun A v => nbrCount_le_deg D.halfGraph A v) (fun v => ?_) _ J
  rw [hc]; exact he v

/-- `hRJ` of `hzeta_cut` with the paper's `R_full`: `U_J ≤ R_full L_J` for every `J`. -/
theorem upJ_le_RfullPaper {m : ℕ} (he : ∀ i, TraceMixing.coarseErr p (deg0 D i) m < 1)
    (J : Finset D.cut.Half) : upJ (p := p) D J ≤ RfullPaper (p := p) D m * lowJ (p := p) D m J := by
  have hq0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hc : ((Fintype.card (ZMod p) : ℕ) : ℝ) = p := by rw [ZMod.card]
  have he' : ∀ v, TraceMixing.coarseErr ((Fintype.card (ZMod p) : ℕ) : ℝ) (deg0 D v) m < 1 := by
    intro v; rw [hc]; exact he v
  have h := upperProd_le_mul_lowerProd D.halfGraph one_le_card_zmod m (deg0 D)
    (fun A v => nbrCount_le_deg D.halfGraph A v) he' (univ \ J).toList J
  unfold upJ lowJ
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (lowerProd_nonneg _ _ _ _ _))
  -- the product over `U⁺ ∖ J` is at most the product over `U⁺`
  have hlist : ((univ \ J).toList.map fun v => ratioE ((Fintype.card (ZMod p) : ℕ) : ℝ) m
      (deg0 D v)).prod = ∏ v ∈ univ \ J, ratioE p m (deg0 D v) := by
    rw [prod_map_toList, hc]
  rw [hlist, RfullPaper, ← prod_sdiff (subset_univ J)]
  have h1 : 1 ≤ ∏ v ∈ J, ratioE p m (deg0 D v) :=
    one_le_prod₀ fun v _ => one_le_ratioE hq0 (he v)
  have h0 : 0 ≤ ∏ v ∈ univ \ J, ratioE p m (deg0 D v) :=
    prod_nonneg fun v _ => zero_le_one.trans (one_le_ratioE hq0 (he v))
  nlinarith

/-- **`e_Δ(p, n') < 1` forces `n' < p`** (`e_t(p, n') ≥ n'/p`). -/
lemma lt_of_coarseErr_lt_one {t n : ℕ} (h : TraceMixing.coarseErr p t n < 1) : n < p := by
  have hq0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hH := TraceMixing.coarseH_nonneg t
  have h2 : (1 : ℝ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
  have hsq : 0 < (Real.sqrt p)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hq0)
  have hge : (n : ℝ) / p ≤ TraceMixing.coarseErr p t n := by
    unfold TraceMixing.coarseErr
    have hx : 0 ≤ ((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * (Real.sqrt p)⁻¹ := mul_nonneg hH hsq.le
    have hn0 : 0 ≤ (n : ℝ) / p := by positivity
    nlinarith
  have : (n : ℝ) / p < 1 := hge.trans_lt h
  rw [div_lt_one hq0] at this
  exact_mod_cast this

/-- **`lem:spec2:paley-one` in instance (A), with the paper's `R_full`**: for every relation `Adj`
containing the adjacency of `G⁺`, `e_{d⁰_i}(p, m) < 1` for every `i` and `|U⁺| ≤ m < p`,
`|t_J| ≤ ζ r` on the non-coverable `J`, `ζ = (R_cut R_full − 1) + m/((p − m) r)`. -/
theorem hzeta_cut_paper (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2) {nn : ℕ}
    (hn : Fintype.card W ≤ nn) (hne : (injLabellings (ZMod p) D.G).Nonempty)
    (he1 : ∀ i, TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) nn < 1)
    {m : ℕ} (hm : Fintype.card D.cut.Half ≤ m) (hmp : m < p)
    (he : ∀ i, TraceMixing.coarseErr p (deg0 D i) m < 1)
    (Adj : D.cut.Half → D.cut.Half → Prop)
    (hAdj : ∀ i j : D.cut.Half, (i, j) ∈ D.halfGraph.E ∨ (j, i) ∈ D.halfGraph.E → Adj i j) :
    ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ SpectralD.PaleyB.Coverable Adj J →
      ‖SpectralD.PaleyB.tJ (SpectralD.Cx.nuA D hne) J‖ ≤
        ((D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) *
            RfullPaper (p := p) D m - 1) + (m : ℝ) / (((p : ℝ) - m) * rp p)) * rp p :=
  hzeta_cut D hW hp2 hn hne he1 hm hmp Adj hAdj (fun J _ _ => lowJ_pos D he J)
    (fun J _ _ => upJ_le_RfullPaper D he J)

end Cut

end Sarkozy.SpectralOne
