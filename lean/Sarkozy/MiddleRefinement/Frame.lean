module

public import Sarkozy.SignedComponents.Bracket

@[expose] public section

/-!
# The refined bracket of a middle block with the paper's signed sides (MRG)

`paper/sections/24_matching_mean.tex`, `prop:signed-sides`, `prop:record:matching`(i),
`lem:record:asymmetric-gram`(b),(c); B8's `SignedComponents/Bracket.lean`.

On V3's frame `D` of a middle block with B7's replacements `R`, B8's `refined_bracket` reduces the
refined bracket to one bracket per fold and one per matching. Here the fold brackets are taken
with **the paper's chosen sides** and the matching brackets with their (CP4) envelopes:

* **`SignedSideGrams D R dL dR`** (`prop:signed-sides`(i),(ii), the block Grams of
  `lem:record:asymmetric-gram`(b),(c)): for the signed record `Π'_{F₁}` of `F₁`,
  `(Π_{F₁} + r d_L D¹   Π'_{F₁} ; ·   Π_{F₁} + r d_R D¹) ⪰_ι 0`, and the same for `F₂` with the
  sides interchanged. *Hypothesis* (the analytic content of `prop:signed-sides`).
* the **side coefficients** `k_s = w_D d_s - v_D` (`prop:signed-sides`(ii));
* the **added diagonals** `sideRec` on `Fin 2 ⊕ Fin 2`: the two fold companions `D¹, D²`
  (coefficients `P⁻¹ r² k_L, P⁻¹ r² k_R` on the left, interchanged on the right, the paper's
  `K_{L,𝔅}`, `K_{R,𝔅}` with the normalization `1/μ̃(1)` kept), and the two matching envelopes
  `Diag_ι(m_{E_s})` with their (CP4) prices `π̃^s + π̃^a` on both sides (the paper's `Q_{E,𝔅}`
  dominates them);
* **`refined_bracket_signed`**: `(Ñ + K_L   λ + ∑_{repl} Δ ; ·   Ñ + K_R) ⪰_ι 0`, from
  `SignedSideGrams` and the hypotheses of V3's `gram_bracket` (layer caps, `v ≥ k w`,
  `f₁ + h₁ ≥ 0`, the disjoint-triple bound, `b > 3`); the protection is not used;
* **`sidePriceL_eq`**, **`sidePriceR_eq`**: both sides cost
  `(P⁻¹ r² (k_L + k_R) + ∑_s (π̃^s_{E_s} + π̃^a_{E_s})) sel` (the exchange of
  `lem:record:asymmetric-gram`(c): each side carries `k_L + k_R`);
* **`price_split`**: the atom's price is the fold price plus the price of every other record.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleRefinement

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.MiddleComparison Sarkozy.SignedComponents

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] (D : FrameData X)
  {acc : X → X → Prop} {E : Type} {Q : Queries E} (R : Replacements D acc Q)

/-- The two-layer fold record `Π_{F_{j+1}}` (`def:record:frame`). -/
noncomputable abbrev foldRec (j : Fin 2) : SlotMeasure X := recM D.F (true, chgPat (.inl j))

/-- The normalized one-layer companion `D^{j+1} = Diag_ι(Π⁽¹⁾_{F_{j+1}})` of the fold. -/
noncomputable abbrev foldDiag (j : Fin 2) : SlotMeasure X := D.diag .D (foldPat j)

/-- **The block Grams of the signed fold records with the chosen sides** (`prop:signed-sides`(i),
(ii); `lem:record:asymmetric-gram`(b) for `F₁`, (c) for `F₂` with the sides interchanged):
`(Π_{F₁} + r d_L D¹   Π'_{F₁} ; ·   Π_{F₁} + r d_R D¹) ⪰_ι 0` and
`(Π_{F₂} + r d_R D²   Π'_{F₂} ; ·   Π_{F₂} + r d_L D²) ⪰_ι 0`, with `Π'_{F_j}` the replacement
of the fold in `R` (the signed record of `def:record:mixture`(c),(d)). *Hypothesis.* -/
structure SignedSideGrams (dL dR : ℝ) : Prop where
  gram₁ : reservedCut.Bracket (foldRec D 0 + (D.r * dL) • foldDiag D 0) (R.newMeas (.inl 0))
    (foldRec D 0 + (D.r * dR) • foldDiag D 0)
  gram₂ : reservedCut.Bracket (foldRec D 1 + (D.r * dR) • foldDiag D 1) (R.newMeas (.inl 1))
    (foldRec D 1 + (D.r * dL) • foldDiag D 1)

/-- The side coefficient `k_s = w_D d_s - v_D` of a chosen side `d_s` (`prop:signed-sides`(ii)). -/
noncomputable def kSide (d : ℝ) : ℝ := D.W.w .D * d - D.W.v .D

/-- The index of the added diagonals: the two folds and the two matchings. -/
abbrev SideIdx : Type := Fin 2 ⊕ Fin 2

/-- The added positive diagonals: the fold companions `D¹, D²` and the matching envelopes
`Diag_ι(m_{E_s})`. -/
noncomputable def sideRec : SideIdx → SlotMeasure X
  | .inl j => foldDiag D j
  | .inr s => envT D (.inl (.inr (.inl s)))

/-- The (CP4) price `π̃^s + π̃^a` of the change of the matching `E_s`. -/
noncomputable def matchPrice (s : Fin 2) : ℝ :=
  R.piT (.inl (.inr (.inl s))) .sym + R.piT (.inl (.inr (.inl s))) .skew

/-- The left coefficients: `P⁻¹ r² k_L` on `D¹`, `P⁻¹ r² k_R` on `D²`, the matching prices. -/
noncomputable def sideCoefL (dL dR : ℝ) : SideIdx → ℝ :=
  Sum.elim ![D.P⁻¹ * D.r ^ 2 * kSide D dL, D.P⁻¹ * D.r ^ 2 * kSide D dR] (matchPrice D R)

/-- The right coefficients: the fold sides interchanged. -/
noncomputable def sideCoefR (dL dR : ℝ) : SideIdx → ℝ :=
  Sum.elim ![D.P⁻¹ * D.r ^ 2 * kSide D dR, D.P⁻¹ * D.r ^ 2 * kSide D dL] (matchPrice D R)

theorem matchPrice_nonneg (s : Fin 2) : 0 ≤ matchPrice D R s :=
  add_nonneg (R.piT_nonneg _ _) (R.piT_nonneg _ _)

theorem sideCoefL_nonneg {dL dR : ℝ} (hL : 0 ≤ kSide D dL) (hR : 0 ≤ kSide D dR) (i : SideIdx) :
    0 ≤ sideCoefL D R dL dR i := by
  have hP := Replacements.P_inv_nonneg (D := D)
  rcases i with j | s
  · fin_cases j
    · exact mul_nonneg (mul_nonneg hP (pow_nonneg D.r_nonneg 2)) hL
    · exact mul_nonneg (mul_nonneg hP (pow_nonneg D.r_nonneg 2)) hR
  · exact matchPrice_nonneg D R s

theorem sideCoefR_nonneg {dL dR : ℝ} (hL : 0 ≤ kSide D dL) (hR : 0 ≤ kSide D dR) (i : SideIdx) :
    0 ≤ sideCoefR D R dL dR i := by
  have hP := Replacements.P_inv_nonneg (D := D)
  rcases i with j | s
  · fin_cases j
    · exact mul_nonneg (mul_nonneg hP (pow_nonneg D.r_nonneg 2)) hR
    · exact mul_nonneg (mul_nonneg hP (pow_nonneg D.r_nonneg 2)) hL
  · exact matchPrice_nonneg D R s

variable {D} in
/-- The added diagonals are positive records (the fold companions by the uniform one-layer
marginals, the matching envelopes by B7's `envT_props`). -/
theorem sideRec_pos (hF : FrameFacts D acc Q) (i : SideIdx) : IsPositiveRecord (sideRec D i) := by
  rcases i with j | s
  · have h := D.isPositiveRecord_diag hF.one_unif .D (foldPat j) (a := 1) zero_le_one
    rw [one_smul] at h
    exact h
  · obtain ⟨hp, -, hu⟩ := Replacements.envT_props hF (.inl (.inr (.inl s)))
    exact ⟨hp.1, hu⟩

variable {D} in
/-- The added diagonals are reserved diagonal. -/
theorem sideRec_diag (hF : FrameFacts D acc Q) (i : SideIdx) :
    TheoremC.IsDiagonalAt reservedCut (sideRec D i) := by
  rcases i with j | s
  · exact D.diag_diagonal .D (foldPat j)
  · exact (Replacements.envT_props hF (.inl (.inr (.inl s)))).2.1

variable {D} in
/-- The added diagonals are probability laws. -/
theorem sideRec_mass (hF : FrameFacts D acc Q) (i : SideIdx) : mass (sideRec D i) = 1 := by
  rcases i with j | s
  · exact D.diag_mass .D (foldPat j)
  · exact (Replacements.envT_props hF (.inl (.inr (.inl s)))).1.2

/-- The left fold side: `∑_j KLf j`. -/
noncomputable def foldSideL (dL dR : ℝ) (j : Fin 2) : SlotMeasure X :=
  (D.P⁻¹ * D.r ^ 2 * kSide D (![dL, dR] j)) • foldDiag D j

/-- The right fold side: `∑_j KRf j`. -/
noncomputable def foldSideR (dL dR : ℝ) (j : Fin 2) : SlotMeasure X :=
  (D.P⁻¹ * D.r ^ 2 * kSide D (![dR, dL] j)) • foldDiag D j

theorem sum_sideL (dL dR : ℝ) :
    ∑ i, sideCoefL D R dL dR i • sideRec D i =
      ∑ j, foldSideL D dL dR j + ∑ s, chargedSide D R (.inl (.inr (.inl s))) := by
  rw [Fintype.sum_sum_type]
  congr 1

theorem sum_sideR (dL dR : ℝ) :
    ∑ i, sideCoefR D R dL dR i • sideRec D i =
      ∑ j, foldSideR D dL dR j + ∑ s, chargedSide D R (.inl (.inr (.inl s))) := by
  rw [Fintype.sum_sum_type]
  congr 1

omit [Nonempty X] in
/-- `foldSide j + P⁻¹ r² k_s D^j = P⁻¹ w_D r (Π_{F_j} + r d_s D^j)`. -/
theorem foldSide_add (j : Fin 2) (d : ℝ) :
    foldSide D j + (D.P⁻¹ * D.r ^ 2 * kSide D d) • foldDiag D j =
      (D.P⁻¹ * (D.W.w .D * D.r)) • (foldRec D j + (D.r * d) • foldDiag D j) := by
  unfold foldSide kSide
  rw [chgCoef_fold]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **The refined bracket of a middle block with the paper's signed sides**
(`prop:record:matching`(i), B3's `bracket_pre`):
`(Ñ + K_L   λ + ∑_{repl} Δ ; ·   Ñ + K_R) ⪰_ι 0` with `K_L = ∑_i sideCoefL_i sideRec_i`,
`K_R = ∑_i sideCoefR_i sideRec_i`, `repl` the two folds and the two matchings (B8's `replSet`).
Inputs: the block Grams of `prop:signed-sides` (`SignedSideGrams`), and the hypotheses of V3's
`gram_bracket` for the unchanged part and the matchings. -/
theorem refined_bracket_signed (hcap : MiddleLayerCaps D.F D.I.k D.r)
    (hdom : ∀ t, D.I.k t * D.W.w t ≤ D.W.v t) (hfh : 0 ≤ D.I.f₁ + D.I.h₁)
    (hE : D.MatchingReservedBound) (hb : 3 < D.b) {dL dR : ℝ}
    (G : SignedSideGrams D R dL dR) :
    reservedCut.Bracket (D.Nbr + ∑ i, sideCoefL D R dL dR i • sideRec D i)
      (D.lam + ∑ t ∈ replSet, R.delta t) (D.Nbr + ∑ i, sideCoefR D R dL dR i • sideRec D i) := by
  rw [sum_sideL, sum_sideR]
  have hPw : 0 ≤ D.P⁻¹ * (D.W.w .D * D.r) :=
    mul_nonneg (Replacements.P_inv_nonneg (D := D)) (mul_nonneg (D.W.w_nonneg .D) D.r_nonneg)
  refine refined_bracket D R (lamRest_positive D hcap hdom hfh) (foldSideL D dL dR)
    (foldSideR D dL dR) (fun s => chargedSide D R (.inl (.inr (.inl s))))
    (fun s => chargedSide D R (.inl (.inr (.inl s)))) (fun j => ?_) (fun s => ?_)
  · have e : D.P⁻¹ • (chgCoef D (.inl j) • R.newMeas (.inl j)) =
        (D.P⁻¹ * (D.W.w .D * D.r)) • R.newMeas (.inl j) := by
      rw [chgCoef_fold, smul_smul]
    rw [e]
    unfold foldSideL foldSideR
    rw [foldSide_add, foldSide_add]
    fin_cases j
    · exact bracket_smul G.gram₁ hPw
    · exact bracket_smul G.gram₂ hPw
  · have h := bracket_add (matchSide_bracket D hE hb s)
      (change_bracket D R (.inl (.inr (.inl s))))
    have e : D.P⁻¹ • (chgCoef D (.inr (.inl s)) • recM D.F (true, chgPat (.inr (.inl s)))) +
        R.delta (.inl (.inr (.inl s))) =
        D.P⁻¹ • (chgCoef D (.inr (.inl s)) • R.newMeas (.inr (.inl s))) := by
      unfold Replacements.delta
      apply LinearMap.ext
      intro f
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [e] at h
    exact h

variable {D} in
/-- **The price of the left side**: `(P⁻¹ r² (k_L + k_R) + ∑_s (π̃^s_{E_s} + π̃^a_{E_s})) sel`. -/
theorem sidePriceL_eq (hF : FrameFacts D acc Q) (dL dR sel : ℝ) :
    ∑ i, sideCoefL D R dL dR i * mass (sideRec D i) * sel =
      (D.P⁻¹ * D.r ^ 2 * (kSide D dL + kSide D dR) + ∑ s, matchPrice D R s) * sel := by
  simp only [sideRec_mass hF, mul_one]
  rw [Fintype.sum_sum_type, Fin.sum_univ_two, ← sum_mul]
  simp only [sideCoefL, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

variable {D} in
/-- **The price of the right side** is the same (`k_R + k_L`). -/
theorem sidePriceR_eq (hF : FrameFacts D acc Q) (dL dR sel : ℝ) :
    ∑ i, sideCoefR D R dL dR i * mass (sideRec D i) * sel =
      (D.P⁻¹ * D.r ^ 2 * (kSide D dL + kSide D dR) + ∑ s, matchPrice D R s) * sel := by
  simp only [sideRec_mass hF, mul_one]
  rw [Fintype.sum_sum_type, Fin.sum_univ_two, ← sum_mul]
  simp only [sideCoefR, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The (CP4) price `π̃^s + π̃^a` of the change of the fold `F_{j+1}`. -/
noncomputable def foldPrice (j : Fin 2) : ℝ :=
  R.piT (.inl (.inl j)) .sym + R.piT (.inl (.inl j)) .skew

/-- **The records outside `repl` and the matchings are all records but the folds**:
`∑_{t ∉ repl} (π̃^s_t + π̃^a_t) + ∑_s (π̃^s_{E_s} + π̃^a_{E_s}) + ∑_j (π̃^s_{F_j} + π̃^a_{F_j})`
is the atom's total. -/
theorem price_split :
    ∑ t ∈ univ \ replSet, (R.piT t .sym + R.piT t .skew) + ∑ s, matchPrice D R s +
        ∑ j, foldPrice D R j = ∑ t, (R.piT t .sym + R.piT t .skew) := by
  have h := sum_sdiff (s₁ := replSet) (s₂ := univ) (f := fun t => R.piT t .sym + R.piT t .skew)
    (subset_univ _)
  rw [← h, sum_replSet]
  unfold matchPrice foldPrice
  ring

/-! ## The price of the records other than the folds -/

open Sarkozy.MiddleRecords (coefS2 coefS3 coefS4 coefS5 coefA2 coefA3 coefA4 gS gA rXof
  middle_comparison_prices MergeRepairBounds) in
/-- **The price of every record but the two folds** (`lem:middle-comparison-prices` without the
fold rows, the part of the middle price that `prop:record:matching`(ii) charges besides `T_K`):
from the norm bounds of the matchings (`lem:record:exact-marginal-e`(ii)), the merges (the table of
`lem:merge-repair`) and the constants (`lem:record:accepting-c2`),
`∑_t (π̃^s_t + π̃^a_t) sel - ∑_j (π̃^s_{F_j} + π̃^a_{F_j}) sel` is at most W6's price polynomial
with the fold constants `s_F = a_F = ℓ_t = 0`. -/
theorem noFold_le (hF : FrameFacts D acc Q) {Xn : ℕ} {b sel : ℝ} (hX : 4 ≤ Xn)
    (hb : (Xn : ℝ) ≤ b) (hr : D.r = 1 / Real.sqrt b) (hsel : 0 ≤ sel)
    (hfh : 0 ≤ D.I.f₁ + D.I.h₁) {sE aE : ℝ}
    (hEs : ∀ i, R.N (.inr (.inl i)) .sym ≤ sE * (1 / Real.sqrt b))
    (hEa : ∀ i, R.N (.inr (.inl i)) .skew ≤ aE * (1 / Real.sqrt b))
    (hM : MergeRepairBounds b (fun j => R.N (.inr (.inr (.inl j))) .sym)
      (fun j => R.N (.inr (.inr (.inl j))) .skew))
    (hCs : ∀ k, R.N (.inr (.inr (.inr k))) .sym ≤ D.r ^ 2 / (1 - 1 / b) ^ 2)
    (hCa : ∀ k, R.N (.inr (.inr (.inr k))) .skew ≤ D.r / (1 - 1 / b)) :
    ∑ t, (R.piT t .sym + R.piT t .skew) * sel - ∑ j, foldPrice D R j * sel ≤
      ((coefS2 D.W sE * (1 / Real.sqrt b) ^ 2 + coefS3 D.W D.I 0 * (1 / Real.sqrt b) ^ 3 +
          coefS4 D.W (gS (1 / (Xn : ℝ))) * (1 / Real.sqrt b) ^ 4 +
          coefS5 D.W (1 / (Xn : ℝ)) * (1 / Real.sqrt b) ^ 5) +
        (coefA2 D.W 0 aE * (1 / Real.sqrt b) ^ 2 +
          coefA3 D.W 0 (gA (1 / (Xn : ℝ)) (rXof Xn)) * (1 / Real.sqrt b) ^ 3 +
          coefA4 D.W (1 / (Xn : ℝ)) * (1 / Real.sqrt b) ^ 4)) * sel := by
  have hX1 : (1 : ℝ) < Xn := by
    have : (4 : ℝ) ≤ Xn := by exact_mod_cast hX
    linarith
  obtain ⟨hcs, hca⟩ := R.const_prices_le hX1 hb hsel hCs hCa
  rw [hr] at hcs hca
  have hP1 : 1 ≤ D.P := one_le_midPoly D.W D.r_nonneg
  have W6 := middle_comparison_prices D.W D.I hX hb hP1 hsel hfh (sF := 0) (aF := 0) (ℓ := 0)
    (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => by simp)
    (fun _ => by simp)
    (fun i => R.N (.inr (.inl i)) .sym) (fun i => R.N (.inr (.inl i)) .skew)
    (fun i => R.N_nonneg _ _) (fun i => R.N_nonneg _ _) hEs hEa
    (fun j => R.N (.inr (.inr (.inl j))) .sym) (fun j => R.N (.inr (.inr (.inl j))) .skew) hM
    hcs hca
  have htot : ∑ t, (R.piT t .sym + R.piT t .skew) * sel =
      (R.toAtom hF).sprice sel + (R.toAtom hF).aprice sel := by
    rw [Replacements.toAtom_sprice, Replacements.toAtom_aprice, ← sum_add_distrib]
    exact sum_congr rfl fun t _ => by ring
  rw [htot, R.sprice_eq hF hfh, R.aprice_eq hF]
  have hfold : ∑ j, foldPrice D R j * sel =
      ∑ i, D.W.w .D * D.r / D.P * R.N (.inl i) .sym * sel +
        ∑ i, D.W.w .D * D.r / D.P * R.N (.inl i) .skew * sel := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [foldPrice, Replacements.piT]
    rw [chgCoef_fold, div_eq_mul_inv]
    ring
  rw [hfold]
  simp only [mul_zero, zero_mul, sum_const_zero, zero_add] at W6
  rw [hr]
  obtain ⟨W6s, W6a⟩ := W6
  linarith

variable {D} in
/-- **The middle price that `prop:record:matching`(ii) charges at a block**: the records outside
`repl` plus the left side are all records but the folds, plus the fold sides
`P⁻¹ r² (k_L + k_R) sel`. -/
theorem others_add_sideL (hF : FrameFacts D acc Q) (dL dR sel : ℝ) :
    ∑ t ∈ univ \ replSet, (R.piT t .sym + R.piT t .skew) * sel +
        ∑ i, sideCoefL D R dL dR i * mass (sideRec D i) * sel =
      (∑ t, (R.piT t .sym + R.piT t .skew) * sel - ∑ j, foldPrice D R j * sel) +
        D.P⁻¹ * D.r ^ 2 * (kSide D dL + kSide D dR) * sel := by
  rw [sidePriceL_eq R hF, ← sum_mul, ← sum_mul, ← sum_mul]
  have h := price_split D R
  linear_combination sel * h

variable {D} in
/-- The same with the right side (the side prices are equal, `sidePriceR_eq`). -/
theorem sideL_eq_sideR (hF : FrameFacts D acc Q) (dL dR sel : ℝ) :
    ∑ i, sideCoefL D R dL dR i * mass (sideRec D i) * sel =
      ∑ i, sideCoefR D R dL dR i * mass (sideRec D i) * sel := by
  rw [sidePriceL_eq R hF, sidePriceR_eq R hF]

end Sarkozy.MiddleRefinement
