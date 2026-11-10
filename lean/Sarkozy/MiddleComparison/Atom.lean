module

public import Sarkozy.MiddleComparison.Records
public import Sarkozy.ComparisonLawPaper.Upper

@[expose] public section

/-!
# The comparison law of a middle block as a (CP4) atom (`subsec:middle-comparison`, `def:cp4`)

`paper/sections/21_middle_records.tex`, `subsec:middle-comparison` and
`lem:middle-comparison-prices`; `paper/sections/09_comparison_theorem.tex`, `def:cp4`.

On a middle block (V3's frame `D`, first stage `λ = D.lam`) the comparison law is
`ν_𝔅 = λ_𝔅 + ∑_{t ∈ 𝒯_𝔅} ζ_t`, where `ζ_t` is (the replacement of `t` minus `t`) or (minus `t`),
with the weight of `t` in `λ_𝔅`, divided by `P(r) = μ̃_𝔅(1)`. The records `𝒯_𝔅` are the changed
two-layer records `Chg` and the deleted records `Del` of `Sarkozy.MiddleComparison.Records`.

* `FrameFacts D acc Q`: the facts about the frame's own records that the atom needs: uniform
  vertex marginals of the field laws and of `κnew`, and acceptance of the kept records and of
  `E_new`. They are **proved** for the paper's middle blocks in `Sarkozy.MiddleComparison.Block`.
* **`Replacements D acc Q`**: the inputs, one per changed record `t`: the replacement as a finite
  real combination `∑_j a_{t,j} ν̄_{t,j}` of laws of total mass one (the signed records of
  `def:record:mixture`(c),(d) for `F₁, F₂`; the block laws of `lem:record:exact-marginal-e` for
  `E₀, E₁`; the repairs of `cor:merge-repair`; the accepting constants of
  `lem:record:accepting-c2`), each law accepting the queries with uniform one-slot marginals, and
  the norms `N_{t,ε}` of the symmetric and skew parts of the difference (replacement minus
  record) at `ι`, relative to the actual half marginal of the record (`rem:cp:charging`(ii)).
* **`Replacements.toAtom`**: the `AtomComparison` of the block relative to `λ`. Components: the
  four kept records with their weights over `P(r)`, the two records `E_new`, and the components
  of the replacements, with coefficient `P(r)⁻¹ w_t r^{deg} a_{t,j}` (all masses `1`). Changes:
  `Δ_t = P(r)⁻¹ w_t r^{deg} (ν'_t - Π_t)` for `t ∈ Chg`, `Δ_d = -P(r)⁻¹ c_d Diag_ι(Π⁽¹⁾_d)` for
  `d ∈ Del`. Envelopes: `Diag_ι(m_+)` of the actual half marginal of the record (W8's
  `envelope_of_law`). Prices: `P(r)⁻¹ w_t r^{deg} N_{t,ε}` (changed, from
  `bracket_of_norm_bound`, `rem:cp:charging`(ii)); `P(r)⁻¹ |c_d|` and `0` (deleted, symmetric and
  skew, `bracket_delete`, `rem:cp:charging`(i)).
* `nu`, `toAtom_sum` (the components sum to `ν`), **`nu_sub_lam`** (`ν - λ = ∑_t Δ_t`),
  `toAtom_Δ_fold`, `toAtom_Δ_match` (the changes of the fold and matching records, for (CP6)),
  `toAtom_mass_pos` (`ν(1) ≥ P(r)⁻¹ > 0`), `toAtom_sprice`, `toAtom_aprice`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleComparison

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.ComparisonLawPaper Sarkozy.UpperComparison Sarkozy.Labellings

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]

/-- The norm envelope `Diag_ι(m_+(Π_ρ))` of a record: the reserved-diagonal law of its actual
half marginal. -/
noncomputable abbrev env (F : MiddleFieldLaws X) (ρ : MidIdx) : SlotMeasure X :=
  reservedCut.diagonalLaw (plusMarginal reservedCut (midComponent F ρ).weight)

/-- `‖G‖²` in `L²` of the actual half marginal of the record `ρ`. -/
noncomputable abbrev halfSq (F : MiddleFieldLaws X) (ρ : MidIdx)
    (G : (reservedCut.Half → X) → ℝ) : ℝ :=
  ∑ x, plusMarginal reservedCut (midComponent F ρ).weight x * (G x * G x)

/-- **The facts about the frame's own records used by the atom** (proved for the paper's middle
blocks in `Sarkozy.MiddleComparison.Block`): the field laws and the replacement law `κnew` of
`E_new` have uniform vertex marginals (`lem:front12:reference`(iii),
`lem:record:one-stage-folded-e`(e)); the kept records (the roots and `F₀`, two-layer and folded)
and `E_new` accept every query (`subsec:middle-comparison`: "the root and `F₀` contain the edge
`0 → 2` of the first coordinate in both layers, and so do their diagonal copies"; `E_new` by
`lem:record:one-stage-folded-e`). -/
structure FrameFacts (D : FrameData X) (acc : X → X → Prop) {E : Type} (Q : Queries E) : Prop where
  two_unif : ∀ f (o : f.Obj × Fin 2) (g : X → ℝ),
    (D.F.two f).expect (fun y => g (y o)) = (FiniteLaw.uniform X).expect g
  one_unif : ∀ f (o : f.Obj × Fin 1) (g : X → ℝ),
    (D.F.one f).expect (fun y => g (y o)) = (FiniteLaw.uniform X).expect g
  new_unif : ∀ (o : Fin 3 × Fin 1) (g : X → ℝ),
    D.κnew.expect (fun y => g (y o)) = (FiniteLaw.uniform X).expect g
  kept_accept : ∀ k (z : Slot → X), (midComponent D.F (keptIdx k)).weight z ≠ 0 →
    ∀ e, acc (z (Q.source e)) (z (Q.target e))
  new_accept : ∀ (s : Fin 2) (z : Slot → X),
    (emit D.κnew (midDiagEmission (matching s))).weight z ≠ 0 →
    ∀ e, acc (z (Q.source e)) (z (Q.target e))

namespace FrameFacts

variable {D : FrameData X} {acc : X → X → Prop} {E : Type} {Q : Queries E}

theorem comp_unif (h : FrameFacts D acc Q) (ρ : MidIdx) :
    HasUniformMarginals (midComponent D.F ρ) := by
  rcases ρ with ⟨b, t, φ⟩
  cases b
  · exact emit_uniform _ _ (h.one_unif t.field)
  · exact emit_uniform _ _ (h.two_unif t.field)

theorem env_props (h : FrameFacts D acc Q) (ρ : MidIdx) :
    IsProbability (env D.F ρ) ∧ TheoremC.IsDiagonalAt reservedCut (env D.F ρ) ∧
      HasUniformSlotMarginals (env D.F ρ) :=
  envelope_of_law reservedCut _ (h.comp_unif ρ)

end FrameFacts

/-- The envelope of a change: `Diag_ι(m_+)` of the actual half marginal of its record. -/
noncomputable def envT (D : FrameData X) : Chg ⊕ Del → SlotMeasure X
  | .inl t => env D.F (true, chgPat t)
  | .inr d => env D.F (false, delPat d)

/-- **The inputs of the comparison law of a middle block** (`subsec:middle-comparison`,
`lem:middle-comparison-prices`): for every changed two-layer record `t` (the folds `F₁, F₂`, the
matchings `E₀, E₁`, the six merges, the two constants),
* `J t`, `a t`, `law t`, `mass_one`: the replacement `ν'_t = ∑_j a_{t,j} ν̄_{t,j}`, a finite real
  combination of laws of mass one (`def:record:mixture`(c),(d): `P_{++} + (t/2) P_{-+} -
  (t/2) P_{--}` for a fold; `lem:record:exact-marginal-e`; `cor:merge-repair`;
  `lem:record:accepting-c2`);
* `accept`, `unif`: every `ν̄_{t,j}` accepts every query and has uniform one-slot marginals
  (`lem:signed-components`(a),(d), `lem:record:e-law`(a), `cor:merge-repair`,
  `lem:record:accepting-c2`);
* `N`, `N_nonneg`, `norm`: the norms of the symmetric and skew parts at `ι` of `ν'_t - Π_t`,
  relative to the actual half marginal of `Π_t` (`|Q(F, G)| ≤ N ‖F‖ ‖G‖`; `prop:signed-bounds`
  (a),(b),(e), `lem:record:exact-marginal-e`(ii), `lem:merge-repair`,
  `lem:record:accepting-c2`). -/
structure Replacements (D : FrameData X) (acc : X → X → Prop) {E : Type} (Q : Queries E) where
  J : Chg → Type
  [JFintype : ∀ t, Fintype (J t)]
  a : ∀ t, J t → ℝ
  law : ∀ t, J t → FiniteLaw (Slot → X)
  mass_one : ∀ t, ∑ j, a t j = 1
  accept : ∀ t j (z : Slot → X), (law t j).weight z ≠ 0 → ∀ e, acc (z (Q.source e)) (z (Q.target e))
  unif : ∀ t j, HasUniformMarginals (law t j)
  N : Chg → ChangeType → ℝ
  N_nonneg : ∀ t e, 0 ≤ N t e
  norm : ∀ t e (F G : (reservedCut.Half → X) → ℝ),
    |reservedCut.form (changePart e ((∑ j, a t j • signedIntegral (law t j).weight) -
        recM D.F (true, chgPat t))) F G| ≤
      N t e * Real.sqrt (halfSq D.F (true, chgPat t) F) * Real.sqrt (halfSq D.F (true, chgPat t) G)

attribute [instance] Replacements.JFintype

namespace Replacements

variable {D : FrameData X} {acc : X → X → Prop} {E : Type} {Q : Queries E}
  (R : Replacements D acc Q)

/-- The replacement `ν'_t` of a changed record. -/
noncomputable def newMeas (t : Chg) : SlotMeasure X :=
  ∑ j, R.a t j • signedIntegral (R.law t j).weight

/-- **The comparison law of the block** `ν_𝔅 = P(r)⁻¹ (∑_{kept} c_k Π_k + (v_S + v_D) r² (E_new,0 +
E_new,1) + ∑_{changed} w_t r^{deg} ν'_t)` (`subsec:middle-comparison`). -/
noncomputable def nu : SlotMeasure X :=
  D.P⁻¹ • (∑ k, keptCoef D k • recM D.F (keptIdx k) + enewCoef D • (D.newRec 0 + D.newRec 1) +
    ∑ t, chgCoef D t • R.newMeas t)

/-- The components of `ν_𝔅`: the kept records, the two `E_new`, and the components of the
replacements. -/
abbrev Comp : Type := Kept ⊕ Fin 2 ⊕ (Σ t : Chg, R.J t)

/-- The coefficients of the components. -/
noncomputable def coef : R.Comp → ℝ
  | .inl k => D.P⁻¹ * keptCoef D k
  | .inr (.inl _) => D.P⁻¹ * enewCoef D
  | .inr (.inr x) => D.P⁻¹ * chgCoef D x.1 * R.a x.1 x.2

/-- The (normalized) laws of the components. -/
noncomputable def compLaw : R.Comp → FiniteLaw (Slot → X)
  | .inl k => midComponent D.F (keptIdx k)
  | .inr (.inl s) => emit D.κnew (midDiagEmission (matching s))
  | .inr (.inr x) => R.law x.1 x.2

/-- **The components sum to `ν_𝔅`.** -/
theorem toAtom_sum : ∑ i, (R.coef i * 1) • signedIntegral (R.compLaw i).weight = R.nu := by
  unfold nu newMeas
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, coef, compLaw, mul_one, Fin.sum_univ_two,
    smul_add, smul_sum, mul_smul, FrameData.newRec, recM, add_assoc]

/-- The changes `Δ_t` (`t ∈ Chg ⊕ Del`). -/
noncomputable def delta : Chg ⊕ Del → SlotMeasure X
  | .inl t => (D.P⁻¹ * chgCoef D t) • (R.newMeas t - recM D.F (true, chgPat t))
  | .inr d => -((D.P⁻¹ * delCoef D d) • recM D.F (false, delPat d))

/-- **`ν_𝔅 - λ_𝔅 = ∑_t Δ_t`** (`subsec:middle-comparison`, (CP4)(b)). -/
theorem nu_sub_lam : R.nu - D.lam = ∑ t, R.delta t := by
  have hR : ∑ t, R.delta t = D.P⁻¹ • ((∑ t, chgCoef D t • R.newMeas t) -
      (∑ t, chgCoef D t • recM D.F (true, chgPat t)) -
      ∑ d, delCoef D d • recM D.F (false, delPat d)) := by
    rw [Fintype.sum_sum_type]
    simp only [delta, mul_smul, smul_sub, smul_sum, sum_sub_distrib, sum_neg_distrib]
    abel
  rw [hR, lam_expand]
  unfold nu
  apply LinearMap.ext
  intro f
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
  ring


/-! ### Prices, envelopes and brackets -/

/-- **The unpriced prices** `π̃^ε_t`: `P(r)⁻¹ w_t r^{deg} N_{t,ε}` for a changed record
(`rem:cp:charging`(ii)); `|P(r)⁻¹ c_d|` (symmetric) and `0` (skew) for a deleted record
(`rem:cp:charging`(i)). -/
noncomputable def piT : Chg ⊕ Del → ChangeType → ℝ
  | .inl t, e => D.P⁻¹ * chgCoef D t * R.N t e
  | .inr d, .sym => |D.P⁻¹ * delCoef D d|
  | .inr _, .skew => 0

omit [Nonempty X] in
theorem P_inv_nonneg : 0 ≤ D.P⁻¹ := inv_nonneg.mpr D.P_pos.le

theorem piT_nonneg (t : Chg ⊕ Del) (e : ChangeType) : 0 ≤ R.piT t e := by
  rcases t with t | d
  · exact mul_nonneg (mul_nonneg (P_inv_nonneg (D := D)) (chgCoef_nonneg D t)) (R.N_nonneg t e)
  · cases e
    · exact abs_nonneg _
    · exact le_rfl

omit [Nonempty X] in
/-- The deleted (folded) records are symmetric at `ι`. -/
theorem del_symmetric (d : Del) : IsSymmetricAt reservedCut (recM D.F (false, delPat d)) := by
  rcases d with φ | k | g
  · exact D.diag_symmetric _ _
  · exact D.diag_symmetric _ _
  · exact D.diag_symmetric _ _

omit [DecidableEq X] [Nonempty X] in
/-- The skew part of a symmetric measure vanishes. -/
theorem skewPart_of_symmetric {L : SlotMeasure X} (h : IsSymmetricAt reservedCut L) :
    skewPart reservedCut L = 0 := by
  unfold skewPart
  rw [h]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul, LinearMap.zero_apply]
  ring

/-- **The bracket of a changed record** (`rem:cp:charging`(ii)): from the norm bound of the
difference, `bracket_of_norm_bound`, scaled by the weight `P(r)⁻¹ w_t r^{deg}`. -/
theorem bracket_chg (t : Chg) (e : ChangeType) :
    reservedCut.Bracket (R.piT (.inl t) e • envT D (.inl t)) (changePart e (R.delta (.inl t)))
      (R.piT (.inl t) e • envT D (.inl t)) := by
  have hm : ∀ x, 0 ≤ plusMarginal reservedCut (midComponent D.F (true, chgPat t)).weight x :=
    plusMarginal_nonneg _ (midComponent D.F _).nonneg
  have h1 := bracket_of_norm_bound reservedCut hm (R.N_nonneg t e) _ (R.norm t e)
  have hω : 0 ≤ D.P⁻¹ * chgCoef D t := mul_nonneg (P_inv_nonneg (D := D)) (chgCoef_nonneg D t)
  have h2 := bracket_smul h1 hω
  rw [smul_smul] at h2
  simp only [piT, envT, delta, changePart_smul]
  exact h2

/-- **The bracket of a deleted record** (`rem:cp:charging`(i)): its change is symmetric, charged
`|P(r)⁻¹ c_d|` to the symmetric part (`bracket_delete`) and nothing to the skew part. -/
theorem bracket_del (d : Del) (e : ChangeType) :
    reservedCut.Bracket (R.piT (.inr d) e • envT D (.inr d)) (changePart e (R.delta (.inr d)))
      (R.piT (.inr d) e • envT D (.inr d)) := by
  set ω := D.P⁻¹ * delCoef D d with hωdef
  have hsym : IsSymmetricAt reservedCut (R.delta (.inr d)) := by
    have := (del_symmetric (D := D) d).smul ω
    unfold IsSymmetricAt at this ⊢
    simp only [delta]
    rw [reflect_neg, this]
  cases e
  · simp only [piT, envT]
    change reservedCut.Bracket _ (symPart reservedCut _) _
    rw [symPart_of_symmetric hsym]
    simp only [delta]
    rw [← hωdef]
    have h := bracket_delete reservedCut (midComponent D.F (false, delPat d)).nonneg
      (del_symmetric (D := D) d) (abs_nonneg ω)
    rcases le_or_gt 0 ω with hω | hω
    · rw [abs_of_nonneg hω] at h
      rw [abs_of_nonneg hω]
      exact h
    · rw [abs_of_neg hω] at h
      rw [abs_of_neg hω]
      have h' := bracket_neg h
      rw [neg_neg] at h'
      have e : -(ω • recM D.F (false, delPat d)) =
          (-ω) • signedIntegral (midComponent D.F (false, delPat d)).weight := by
        apply LinearMap.ext
        intro f
        simp only [LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul, neg_mul]
      rw [e]
      exact h'
  · simp only [piT, envT]
    change reservedCut.Bracket _ (skewPart reservedCut _) _
    rw [skewPart_of_symmetric hsym, zero_smul]
    exact DeletionInputs.zero_positive.bracket_self

theorem bracket_all (t : Chg ⊕ Del) (e : ChangeType) :
    reservedCut.Bracket (R.piT t e • envT D t) (changePart e (R.delta t)) (R.piT t e • envT D t) :=
  by
  rcases t with t | d
  · exact R.bracket_chg t e
  · exact R.bracket_del d e

theorem envT_props (h : FrameFacts D acc Q) (t : Chg ⊕ Del) :
    IsProbability (envT D t) ∧ TheoremC.IsDiagonalAt reservedCut (envT D t) ∧
      HasUniformSlotMarginals (envT D t) := by
  rcases t with t | d
  · exact h.env_props _
  · exact h.env_props _

/-! ### The mass -/

/-- `ν_𝔅(1) = P(r)⁻¹ (∑_{kept} c_k + 2 (v_S + v_D) r² + ∑_{changed} w_t r^{deg})`: every
replacement has mass one. -/
theorem coef_sum : ∑ i, R.coef i * 1 =
    D.P⁻¹ * (∑ k, keptCoef D k + 2 * enewCoef D + ∑ t, chgCoef D t) := by
  have ht : ∀ t, ∑ j, D.P⁻¹ * chgCoef D t * R.a t j = D.P⁻¹ * chgCoef D t := fun t => by
    rw [← mul_sum, R.mass_one, mul_one]
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, coef, mul_one, Fin.sum_univ_two]
  simp only [ht, ← mul_sum]
  ring

/-- **`ν_𝔅(1) ≥ P(r)⁻¹ > 0`**: the two-layer root (weight one in `μ̃_𝔅`) is retained
(`lem:middle-comparison-prices`, proof). -/
theorem mass_ge : D.P⁻¹ ≤ ∑ i, R.coef i * 1 := by
  rw [R.coef_sum]
  have h1 : keptCoef D 0 ≤ ∑ k, keptCoef D k :=
    single_le_sum (fun k _ => keptCoef_nonneg D k) (mem_univ 0)
  rw [keptCoef_root] at h1
  have h2 : 0 ≤ ∑ t, chgCoef D t := sum_nonneg fun t _ => chgCoef_nonneg D t
  have h3 := enewCoef_nonneg D
  have hP := P_inv_nonneg (D := D)
  nlinarith

/-! ### The atom -/

/-- **The (CP4) atom of a middle block** (`subsec:middle-comparison`,
`lem:middle-comparison-prices`, `def:cp4`(a),(b)), relative to the first stage `λ = D.lam`. -/
noncomputable def toAtom (h : FrameFacts D acc Q) : AtomComparison D.lam acc Q where
  I := R.Comp
  c := R.coef
  w _ := 1
  law := R.compLaw
  w_pos _ := one_pos
  mass_pos := lt_of_lt_of_le (inv_pos.mpr D.P_pos) R.mass_ge
  accept i z hz e := by
    rcases i with k | s | ⟨t, j⟩
    · exact h.kept_accept k z hz e
    · exact h.new_accept s z hz e
    · exact R.accept t j z hz e
  unif i := by
    rcases i with k | s | ⟨t, j⟩
    · exact h.comp_unif _
    · exact emit_uniform _ _ h.new_unif
    · exact R.unif t j
  T := Chg ⊕ Del
  Δ := R.delta
  change := by rw [R.toAtom_sum]; exact R.nu_sub_lam
  D t _ := envT D t
  D_prob t _ := (envT_props h t).1
  D_diag t _ := (envT_props h t).2.1
  D_unif t _ := (envT_props h t).2.2
  πt := R.piT
  πt_nonneg := R.piT_nonneg
  bracket := R.bracket_all

theorem toAtom_sprice (h : FrameFacts D acc Q) (sel : ℝ) :
    (R.toAtom h).sprice sel = ∑ t, R.piT t .sym * sel := rfl

theorem toAtom_aprice (h : FrameFacts D acc Q) (sel : ℝ) :
    (R.toAtom h).aprice sel = ∑ t, R.piT t .skew * sel := rfl

/-- **The changes of the two fold records** (for (CP6), `prop:record:matching`(i)):
`Δ_{F_j} = P(r)⁻¹ w_D r (ν'_{F_j} - Π_{F_j})`, `j = 1, 2` (`foldPat`). -/
theorem toAtom_Δ_fold (h : FrameFacts D acc Q) (j : Fin 2) :
    (R.toAtom h).Δ (.inl (.inl j)) = (D.P⁻¹ * (D.W.w .D * D.r)) •
      (R.newMeas (.inl j) - recM D.F (true, ⟨.D, foldPat j⟩)) := by
  change (D.P⁻¹ * chgCoef D (.inl j)) • _ = _
  rw [chgCoef_fold]
  rfl

/-- **The changes of the two matching records**: `Δ_{E_s} = P(r)⁻¹ w_S r (ν'_{E_s} - Π_{E_s})`. -/
theorem toAtom_Δ_match (h : FrameFacts D acc Q) (s : Fin 2) :
    (R.toAtom h).Δ (.inl (.inr (.inl s))) = (D.P⁻¹ * (D.W.w .S * D.r)) •
      (R.newMeas (.inr (.inl s)) - recM D.F (true, ⟨.S, s⟩)) := by
  change (D.P⁻¹ * chgCoef D (.inr (.inl s))) • _ = _
  rw [chgCoef_match]
  rfl

/-- The comparison law of the atom is `ν_𝔅`. -/
theorem toAtom_law (h : FrameFacts D acc Q) :
    ∑ i, ((R.toAtom h).c i * (R.toAtom h).w i) • signedIntegral ((R.toAtom h).law i).weight =
      R.nu :=
  R.toAtom_sum

end Replacements

end Sarkozy.MiddleComparison
