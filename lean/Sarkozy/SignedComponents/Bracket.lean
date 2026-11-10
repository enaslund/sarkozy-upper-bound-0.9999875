module

public import Sarkozy.SignedComponents.Data

@[expose] public section

/-!
# The refined bracket of a middle block, reduced to the fold and matching brackets

`paper/sections/24_matching_mean.tex`, `prop:record:matching`(i), `prop:signed-sides`;
`paper/sections/20c_middle_frame.tex`, `lem:record:gram`. This is B3's open `bracket_pre`
(`EnvelopesPaper.PrefixRefinement`) at a middle block, at the level of V3's frame.

On a middle block, B3's refined bracket asks
`(Ñ + K_L   λ + ∑_{repl} Δ ; ·   Ñ + K_R) ⪰_ι 0`, where `repl` are the two folds `F₁, F₂` and the
two matchings `E₀, E₁` of B7's atom, `Δ_t = P⁻¹ w_t r (ν'_t - Π_t)` their changes, and `K_L`, `K_R`
the added positive diagonals. This file splits it exactly, record by record:

* `foldSide j = P⁻¹(w_D r Π_{F_j} + v_D r² Diag_ι(Π⁽¹⁾_{F_j}))`: the part of `Ñ` carried by the
  fold `F_{j+1}` (its two-layer record and its folded copy `F_fold`);
* `matchSide s = P⁻¹(w_S r Π_{E_s} + h Diag_ι(Π⁽¹⁾_{E_s}))`, `h = 2 w_S r · 3/(b - 3)`: the part
  carried by the matching `E_s` (its two-layer record and its share of `H`);
* `lamRest = λ - P⁻¹(w_D r (Π_{F₁} + Π_{F₂}) + w_S r (Π_{E₀} + Π_{E₁}))`: everything else;
* **`Nbr_split`**: `Ñ = lamRest + ∑_j foldSide j + ∑_s matchSide s` (exact);
* **`lam_repl_split`**:
  `λ + ∑_{repl} Δ = lamRest + ∑_j P⁻¹ w_D r ν'_{F_j} + ∑_s P⁻¹ w_S r ν'_{E_s}`;
* **`lamRest_positive`**: `lamRest ⪰_ι 0`, from the layer caps of `lem:front12:reference`(ii),
  `v_𝔱 ≥ k_𝔱 w_𝔱` and `f₁ + h₁ ≥ 0` (the root, `F₀`, the merges and the constants pair with their
  folded copies; `E_new` and `G` are positive diagonals);
* **`refined_bracket`**: the refined bracket follows from the two fold brackets
  (`prop:signed-sides`(i),(ii) with the chosen sides) and the two matching brackets
  (`prop:record:matching`(i), the matching records with `Q_E`), which are its hypotheses.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedComponents

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.MiddleComparison

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] (D : FrameData X)

/-- The part of `Ñ` carried by the fold `F_{j+1}`:
`P⁻¹(w_D r Π_{F_j} + v_D r² Diag_ι(Π⁽¹⁾_{F_j}))`. -/
noncomputable def foldSide (j : Fin 2) : SlotMeasure X :=
  D.P⁻¹ • (chgCoef D (.inl j) • recM D.F (true, chgPat (.inl j)) +
    (D.W.v .D * D.r ^ 2) • D.diag .D (foldPat j))

/-- The part of `Ñ` carried by the matching `E_s`: `P⁻¹(w_S r Π_{E_s} + h Diag_ι(Π⁽¹⁾_{E_s}))`. -/
noncomputable def matchSide (s : Fin 2) : SlotMeasure X :=
  D.P⁻¹ • (chgCoef D (.inr (.inl s)) • recM D.F (true, chgPat (.inr (.inl s))) +
    D.hCoef • D.diag .S s)

/-- `λ` without the two-layer folds `F₁, F₂` and matchings `E₀, E₁`. -/
noncomputable def lamRest : SlotMeasure X :=
  D.lam - D.P⁻¹ • (∑ j : Fin 2, chgCoef D (.inl j) • recM D.F (true, chgPat (.inl j)) +
    ∑ s : Fin 2, chgCoef D (.inr (.inl s)) • recM D.F (true, chgPat (.inr (.inl s))))

omit [Nonempty X] in
/-- **`Ñ = lamRest + ∑_j foldSide j + ∑_s matchSide s`.** -/
theorem Nbr_split : D.Nbr = lamRest D + (∑ j, foldSide D j + ∑ s, matchSide D s) := by
  unfold FrameData.Nbr lamRest foldSide matchSide FrameData.Ffold FrameData.Hdiag
  apply LinearMap.ext
  intro f
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Fin.sum_univ_two,
    smul_eq_mul, foldPat, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The fold and matching indices of B7's atom in `T = Chg ⊕ Del`. -/
def replSet : Finset (Chg ⊕ Del) :=
  (univ.image fun j : Fin 2 => (Sum.inl (Sum.inl j) : Chg ⊕ Del)) ∪
    univ.image fun s : Fin 2 => (Sum.inl (Sum.inr (Sum.inl s)) : Chg ⊕ Del)

theorem sum_replSet {M : Type*} [AddCommMonoid M] (g : Chg ⊕ Del → M) :
    ∑ t ∈ replSet, g t =
      ∑ j : Fin 2, g (.inl (.inl j)) + ∑ s : Fin 2, g (.inl (.inr (.inl s))) := by
  unfold replSet
  rw [sum_union]
  · rw [sum_image fun a _ b _ h => by simpa using h, sum_image fun a _ b _ h => by simpa using h]
  · rw [disjoint_left]
    intro t h1 h2
    obtain ⟨j, -, rfl⟩ := mem_image.mp h1
    obtain ⟨s, -, hs⟩ := mem_image.mp h2
    cases hs

variable {acc : X → X → Prop} {E : Type} {Q : Queries E} (R : Replacements D acc Q)

/-- **`λ + ∑_{repl} Δ` is `λ` with the folds and matchings replaced.** -/
theorem lam_repl_split : D.lam + ∑ t ∈ replSet, R.delta t = lamRest D +
    (∑ j : Fin 2, D.P⁻¹ • (chgCoef D (.inl j) • R.newMeas (.inl j)) +
      ∑ s : Fin 2, D.P⁻¹ • (chgCoef D (.inr (.inl s)) • R.newMeas (.inr (.inl s)))) := by
  rw [sum_replSet]
  unfold lamRest Replacements.delta
  apply LinearMap.ext
  intro f
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Fin.sum_univ_two,
    smul_eq_mul]
  ring

omit [Nonempty X] in
/-- **The unchanged part is positive at `ι`** (`lem:record:gram`(ii), summand by summand): the
root, `F₀`, the merges and the constants with their folded copies (layer caps
`lem:front12:reference`(ii) and `v_𝔱 ≥ k_𝔱 w_𝔱`), `E_new` and `G` (positive diagonals,
`f₁ + h₁ ≥ 0`). -/
theorem lamRest_positive (hcap : MiddleLayerCaps D.F D.I.k D.r)
    (hdom : ∀ t, D.I.k t * D.W.w t ≤ D.W.v t) (hfh : 0 ≤ D.I.f₁ + D.I.h₁) :
    reservedCut.Positive (lamRest D) := by
  have hexp := D.muT_eq_sum
  rw [FrameData.sum_sigma_pType] at hexp
  have key : lamRest D = D.P⁻¹ • (D.pairTerm ⟨.L, ()⟩ + D.pairTerm ⟨.D, (0 : Fin 3)⟩ +
      (∑ φ : PType.Pat .R, D.pairTerm ⟨.R, φ⟩ + ∑ φ : PType.Pat .C, D.pairTerm ⟨.C, φ⟩) +
      D.Enew + D.Gpol) := by
    unfold lamRest FrameData.lam
    rw [hexp]
    apply LinearMap.ext
    intro f
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Fin.sum_univ_two,
      smul_eq_mul, FrameData.pairTerm, FrameData.Ffold, FrameData.Efold, FrameData.diag,
      chgCoef, chgPat, foldPat, Matrix.cons_val_zero, Matrix.cons_val_one,
      midCoeff, PType.deg, recM, LinearMap.sum_apply]
    ring
  rw [key]
  have hp := fun s => D.pairTerm_reserved_positive hcap hdom s
  have hE : reservedCut.Positive D.Enew :=
    ((D.newRec_positive 0).add (D.newRec_positive 1)).smul
      (mul_nonneg (add_nonneg (D.W.v_nonneg _) (D.W.v_nonneg _)) (pow_nonneg D.r_nonneg _))
  have hG : reservedCut.Positive D.Gpol :=
    ((((D.diag_positive .R _).smul (mul_nonneg (D.W.v_nonneg _) (pow_nonneg D.r_nonneg _))).add
      ((D.diag_positive .R _).smul (mul_nonneg (D.W.v_nonneg _)
        (pow_nonneg D.r_nonneg _))))).smul (mul_nonneg hfh D.r_nonneg)
  have hR : reservedCut.Positive (∑ φ : PType.Pat .R, D.pairTerm ⟨.R, φ⟩) :=
    sum_induction _ (fun L => reservedCut.Positive L) (fun _ _ h₁ h₂ => h₁.add h₂)
      (positive_zero _) fun φ _ => hp _
  have hC : reservedCut.Positive (∑ φ : PType.Pat .C, D.pairTerm ⟨.C, φ⟩) :=
    sum_induction _ (fun L => reservedCut.Positive L) (fun _ _ h₁ h₂ => h₁.add h₂)
      (positive_zero _) fun φ _ => hp _
  exact (((((hp _).add (hp _)).add (hR.add hC)).add hE).add hG).smul
    (Replacements.P_inv_nonneg (D := D))

/-- **The refined bracket of a middle block** (`prop:record:matching`(i), B3's `bracket_pre`):
`(Ñ + K_L   λ + ∑_{repl} Δ ; ·   Ñ + K_R) ⪰_ι 0` with `K_L = ∑_j KLf j + ∑_s KLm s` and
`K_R = ∑_j KRf j + ∑_s KRm s`, given
* `hrest`: the unchanged part is positive (`lamRest_positive`);
* `hfold`: for each fold, `(foldSide j + KLf j   P⁻¹ w_D r ν'_{F_j} ; ·   foldSide j + KRf j) ⪰_ι 0`
  (`prop:signed-sides`(i),(ii), hypothesis);
* `hmatch`: for each matching,
  `(matchSide s + KLm s   P⁻¹ w_S r ν'_{E_s} ; ·   matchSide s + KRm s) ⪰_ι 0`
  (`prop:record:matching`(i), with `Q_E`; hypothesis). -/
theorem refined_bracket (hrest : reservedCut.Positive (lamRest D))
    (KLf KRf KLm KRm : Fin 2 → SlotMeasure X)
    (hfold : ∀ j, reservedCut.Bracket (foldSide D j + KLf j)
      (D.P⁻¹ • (chgCoef D (.inl j) • R.newMeas (.inl j))) (foldSide D j + KRf j))
    (hmatch : ∀ s, reservedCut.Bracket (matchSide D s + KLm s)
      (D.P⁻¹ • (chgCoef D (.inr (.inl s)) • R.newMeas (.inr (.inl s)))) (matchSide D s + KRm s)) :
    reservedCut.Bracket (D.Nbr + (∑ j, KLf j + ∑ s, KLm s)) (D.lam + ∑ t ∈ replSet, R.delta t)
      (D.Nbr + (∑ j, KRf j + ∑ s, KRm s)) := by
  have h := bracket_add hrest.bracket_self
    (bracket_add (bracket_sum univ fun j _ => hfold j) (bracket_sum univ fun s _ => hmatch s))
  rw [lam_repl_split D R]
  have eL : D.Nbr + (∑ j, KLf j + ∑ s, KLm s) = lamRest D +
      (∑ j, (foldSide D j + KLf j) + ∑ s, (matchSide D s + KLm s)) := by
    rw [Nbr_split, sum_add_distrib, sum_add_distrib]
    abel
  have eR : D.Nbr + (∑ j, KRf j + ∑ s, KRm s) = lamRest D +
      (∑ j, (foldSide D j + KRf j) + ∑ s, (matchSide D s + KRm s)) := by
    rw [Nbr_split, sum_add_distrib, sum_add_distrib]
    abel
  rw [eL, eR]
  exact h

/-! ## The refined bracket with the charged sides (no analytic input)

With the sides `K_t = (π̃^s_t + π̃^a_t) Diag_ι(m_t)` of the replaced records (their (CP4)
envelopes and prices, `rem:cp:charging`(ii)), the fold and matching brackets hold: the replaced
record's own part is the (CP3) bracket of `lem:record:gram` (the fold protection, the
disjoint-triple bound), and the change is B7's atom bracket. This is the refinement that gains
nothing over (CP4); the paper's signed sides (`prop:signed-sides`) lower the side prices. -/

omit [Nonempty X] in
/-- **The fold part of `Ñ` brackets the fold record** (`lem:record:gram`(ii), the protection
`2 w_D r Π_F + v_D r² Diag_ι(Π⁽¹⁾_F) ⪰_ι 0` from the D layer cap and `v_D ≥ 2 k_D w_D`). -/
theorem foldSide_bracket (hcap : MiddleLayerCaps D.F D.I.k D.r) (hP : D.W.Protects D.I)
    (j : Fin 2) :
    reservedCut.Bracket (foldSide D j)
      (D.P⁻¹ • (chgCoef D (.inl j) • recM D.F (true, chgPat (.inl j)))) (foldSide D j) := by
  have hPi := Replacements.P_inv_nonneg (D := D)
  have hr := D.r_nonneg
  have hw := D.W.w_nonneg .D
  have hv := D.W.v_nonneg .D
  apply ReflectionCut.bracket_of_add_sub_positive
  · have e : foldSide D j + D.P⁻¹ • (chgCoef D (.inl j) • recM D.F (true, chgPat (.inl j))) =
        D.P⁻¹ • ((2 * D.W.w .D * D.r) • (signedIntegral (midComponent D.F
          (true, ⟨.D, foldPat j⟩)).weight - (-(D.I.k .D * D.r)) • signedIntegral (midComponent
          D.F (false, ⟨.D, foldPat j⟩)).weight) + ((D.W.v .D - 2 * D.I.k .D * D.W.w .D) *
          D.r ^ 2) • D.diag .D (foldPat j)) := by
      unfold foldSide
      rw [chgCoef_fold]
      apply LinearMap.ext
      intro f
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        FrameData.diag, recM, chgPat]
      ring
    rw [e]
    have hP' : 0 ≤ D.W.v .D - 2 * D.I.k .D * D.W.w .D := sub_nonneg.mpr hP
    exact (((hcap .D (foldPat j)).smul (by positivity)).add
      ((D.diag_positive _ _).smul (mul_nonneg hP' (pow_nonneg hr 2)))).smul hPi
  · have e : foldSide D j - D.P⁻¹ • (chgCoef D (.inl j) • recM D.F (true, chgPat (.inl j))) =
        D.P⁻¹ • ((D.W.v .D * D.r ^ 2) • D.diag .D (foldPat j)) := by
      unfold foldSide
      apply LinearMap.ext
      intro f
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact ((D.diag_positive _ _).smul (mul_nonneg hv (pow_nonneg hr 2))).smul hPi

omit [Nonempty X] in
/-- **The matching part of `Ñ` brackets the matching record** (`lem:record:gram`(ii), the
disjoint-triple bound `Π_{E_s} + 3/(b - 3) Diag_ι(Π⁽¹⁾_{E_s}) ⪰_ι 0`, `b > 3`). -/
theorem matchSide_bracket (hE : D.MatchingReservedBound) (hb : 3 < D.b) (s : Fin 2) :
    reservedCut.Bracket (matchSide D s)
      (D.P⁻¹ • (chgCoef D (.inr (.inl s)) • recM D.F (true, chgPat (.inr (.inl s)))))
      (matchSide D s) := by
  have hPi := Replacements.P_inv_nonneg (D := D)
  have hr := D.r_nonneg
  have hw := D.W.w_nonneg .S
  have hb3 : 0 ≤ 3 / (D.b - 3) := div_nonneg (by norm_num) (by linarith)
  apply ReflectionCut.bracket_of_add_sub_positive
  · have e : matchSide D s + D.P⁻¹ • (chgCoef D (.inr (.inl s)) •
        recM D.F (true, chgPat (.inr (.inl s)))) =
        D.P⁻¹ • ((2 * D.W.w .S * D.r) • (D.two .S s + (3 / (D.b - 3)) • D.diag .S s)) := by
      unfold matchSide FrameData.hCoef
      rw [chgCoef_match]
      apply LinearMap.ext
      intro f
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, FrameData.two, recM,
        chgPat]
      ring
    rw [e]
    exact ((hE s).smul (by positivity)).smul hPi
  · have e : matchSide D s - D.P⁻¹ • (chgCoef D (.inr (.inl s)) •
        recM D.F (true, chgPat (.inr (.inl s)))) = D.P⁻¹ • (D.hCoef • D.diag .S s) := by
      unfold matchSide
      apply LinearMap.ext
      intro f
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [e]
    have hh : 0 ≤ D.hCoef := by unfold FrameData.hCoef; positivity
    exact ((D.diag_positive _ _).smul hh).smul hPi

/-- The charged side of a change: `(π̃^s_t + π̃^a_t) Diag_ι(m_t)`. -/
noncomputable def chargedSide (t : Chg ⊕ Del) : SlotMeasure X :=
  (R.piT t .sym + R.piT t .skew) • envT D t

/-- **The change brackets with its charged side** (B7's (CP4)(b) brackets, symmetric plus
skew). -/
theorem change_bracket (t : Chg ⊕ Del) :
    reservedCut.Bracket (chargedSide D R t) (R.delta t) (chargedSide D R t) := by
  have h := bracket_add (R.bracket_all t .sym) (R.bracket_all t .skew)
  have e1 : R.piT t .sym • envT D t + R.piT t .skew • envT D t = chargedSide D R t := by
    unfold chargedSide
    rw [add_smul]
  have e2 : changePart .sym (R.delta t) + changePart .skew (R.delta t) = R.delta t :=
    symPart_add_skewPart _ _
  rw [e1, e2] at h
  exact h

/-- **The refined bracket of a middle block with the charged sides**, proved: with
`K = ∑_{t ∈ repl} (π̃^s_t + π̃^a_t) Diag_ι(m_t)` on both sides,
`(Ñ + K   λ + ∑_{repl} Δ ; ·   Ñ + K) ⪰_ι 0`, from the layer caps, `v_𝔱 ≥ k_𝔱 w_𝔱`,
`f₁ + h₁ ≥ 0`, the protection, the disjoint-triple bound and `b > 3` (the hypotheses of V3's
`gram_bracket`). -/
theorem refined_bracket_charged (hcap : MiddleLayerCaps D.F D.I.k D.r)
    (hdom : ∀ t, D.I.k t * D.W.w t ≤ D.W.v t) (hfh : 0 ≤ D.I.f₁ + D.I.h₁)
    (hP : D.W.Protects D.I) (hE : D.MatchingReservedBound) (hb : 3 < D.b) :
    reservedCut.Bracket (D.Nbr + ∑ t ∈ replSet, chargedSide D R t)
      (D.lam + ∑ t ∈ replSet, R.delta t) (D.Nbr + ∑ t ∈ replSet, chargedSide D R t) := by
  rw [sum_replSet]
  refine refined_bracket D R (lamRest_positive D hcap hdom hfh)
    (fun j => chargedSide D R (.inl (.inl j))) (fun j => chargedSide D R (.inl (.inl j)))
    (fun s => chargedSide D R (.inl (.inr (.inl s))))
    (fun s => chargedSide D R (.inl (.inr (.inl s)))) (fun j => ?_) (fun s => ?_)
  · have h := bracket_add (foldSide_bracket D hcap hP j) (change_bracket D R (.inl (.inl j)))
    have e : D.P⁻¹ • (chgCoef D (.inl j) • recM D.F (true, chgPat (.inl j))) +
        R.delta (.inl (.inl j)) = D.P⁻¹ • (chgCoef D (.inl j) • R.newMeas (.inl j)) := by
      unfold Replacements.delta
      apply LinearMap.ext
      intro f
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [e] at h
    exact h
  · have h := bracket_add (matchSide_bracket D hE hb s) (change_bracket D R (.inl (.inr (.inl s))))
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

end Sarkozy.SignedComponents
