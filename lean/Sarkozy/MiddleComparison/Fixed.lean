module

public import Sarkozy.MiddleComparison.Matchings
public import Sarkozy.MiddleComparison.Constants

@[expose] public section

/-!
# The inputs of a middle block with ten of the twelve replacements constructed

`paper/sections/21_middle_records.tex`, `subsec:middle-comparison`.

Of the twelve changed two-layer records of a middle block, the two matchings, the six merges and
the two constants have constructed replacements (`matchRec`, `lem:record:e-law`(a),
`lem:record:exact-marginal-e`; `mergeRec`, `lem:merge-repair`; `constRec`,
`lem:record:accepting-c2`), with their acceptance and uniform marginals proved. What is left:

* **`ReplacementData pr h D`**: the signed fold records of `def:record:mixture`(c),(d), given as
  the parameter `t ∈ [0, 1]` and the three normalized components `⊗P_{++}`, `⊗P_{-+}`, `⊗P_{--}`
  of `F₁` and of `F₂` (`lem:signed-components`), each a law accepting the queries with uniform
  one-slot marginals; and the norms `N_{t,ε}` of the symmetric and skew parts of all twelve
  changes, relative to the actual half marginals of the replaced records (`prop:signed-bounds`
  (a),(b),(e); `lem:record:exact-marginal-e`(ii); the norm table of `lem:merge-repair`;
  `lem:record:accepting-c2`).
* **`ReplacementData.toReplacements`**: the `Replacements` of the block. The fold replacements are
  `K_{t,𝔅} = ⊗P_{++} + (t/2)⊗P_{-+} - (t/2)⊗P_{--}` (`signedCoef`, mass one: `sum_signedCoef`).
* **`toAtom_absmass`** (`lem:middle-comparison-prices`): the total variation of the comparison law
  is `|ν|_𝔅 = ν_𝔅(1) + 2 t w`, `w = w_D r/μ̃_𝔅(1)`: the only negative components are the two
  `-(t/2) w Π^{--}_{F_j}`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleComparison

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.ComparisonLawPaper Sarkozy.Labellings

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr)

/-- **The coefficients of the signed fold record** (`eq:signed-law`): `1`, `t/2`, `-t/2` for the
components `⊗_p P_{++,p}`, `⊗_p P_{-+,p}`, `⊗_p P_{--,p}`. -/
noncomputable def signedCoef (t : ℝ) : Fin 3 → ℝ := ![1, t / 2, -(t / 2)]

/-- The signed fold record has mass one (`def:record:mixture`(c)). -/
theorem sum_signedCoef (t : ℝ) : ∑ c, signedCoef t c = 1 := by
  simp only [signedCoef, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring

/-- The replacement of a changed record: the signed records `K_{t,𝔅} = ⊗P_{++} + (t/2)⊗P_{-+} -
(t/2)⊗P_{--}` for the folds (inputs), `matchRec` for the matchings, `mergeRec` for the merges,
`constRec` for the constants. -/
noncomputable def newOf (t : ℝ) (P : Fin 2 → Fin 3 → FiniteLaw (Slot → BlockLabel pr)) :
    Chg → SlotMeasure (BlockLabel pr)
  | .inl j => ∑ c, signedCoef t c • signedIntegral (P j c).weight
  | .inr (.inl s) => signedIntegral (matchRec pr h s).weight
  | .inr (.inr (.inl φ)) => signedIntegral (mergeRec pr h φ).weight
  | .inr (.inr (.inr _)) => signedIntegral (constRec pr).weight

/-- **The inputs of the comparison law of a middle block, with ten of the twelve replacements
constructed** (`subsec:middle-comparison`):
* `t`, `t_nonneg`, `t_le_one`, `P`, `accept`, `unif`: the signed fold records of
  `def:record:mixture`(c),(d): the parameter `t ∈ [0, 1]` (`t = 127/500` in the paper) and, for
  `F₁` and `F₂` (the latter the reflected transpose), the three normalized components
  `⊗_p P_{++,p}`, `⊗_p P_{-+,p}`, `⊗_p P_{--,p}` placed by the fold (`lem:signed-components`),
  each a law accepting the six queries at every prime, with uniform one-slot marginals
  (`lem:signed-components`(a),(d));
* `N`, `N_nonneg`, `norm`: the norms of the symmetric and skew parts at `ι` of every change
  (replacement minus record), relative to the actual half marginal of the record
  (`prop:signed-bounds`(a),(b),(e); `lem:record:exact-marginal-e`(ii); `lem:merge-repair`;
  `lem:record:accepting-c2`). -/
structure ReplacementData (D : FrameData (BlockLabel pr)) where
  t : ℝ
  t_nonneg : 0 ≤ t
  t_le_one : t ≤ 1
  P : Fin 2 → Fin 3 → FiniteLaw (Slot → BlockLabel pr)
  accept : ∀ j c (z : Slot → BlockLabel pr), (P j c).weight z ≠ 0 → ∀ e : Chamber,
    blockSquareAccepted pr (z (MainAnchor.paperQueries.source e))
      (z (MainAnchor.paperQueries.target e))
  unif : ∀ j c, HasUniformMarginals (P j c)
  N : Chg → ChangeType → ℝ
  N_nonneg : ∀ t e, 0 ≤ N t e
  norm : ∀ t' e (F G : (reservedCut.Half → BlockLabel pr) → ℝ),
    |reservedCut.form (changePart e (newOf pr h t P t' - recM D.F (true, chgPat t'))) F G| ≤
      N t' e * Real.sqrt (halfSq D.F (true, chgPat t') F) *
        Real.sqrt (halfSq D.F (true, chgPat t') G)

namespace ReplacementData

variable {pr} {h} {D : FrameData (BlockLabel pr)} (R : ReplacementData pr h D)

/-- The component index sets of all twelve replacements (`Fin 3` for a fold, `Unit` for a
constructed one). -/
def J' : Chg → Type
  | .inl _ => Fin 3
  | .inr _ => Unit

instance instFintypeJ' : ∀ t, Fintype (J' t)
  | .inl _ => inferInstanceAs (Fintype (Fin 3))
  | .inr _ => inferInstanceAs (Fintype Unit)

/-- The coefficients of all twelve replacements. -/
noncomputable def a' : ∀ t, J' t → ℝ
  | .inl _ => signedCoef R.t
  | .inr _ => fun _ => 1

/-- The laws of all twelve replacements. -/
noncomputable def law' : ∀ t, J' t → FiniteLaw (Slot → BlockLabel pr)
  | .inl j => R.P j
  | .inr (.inl s) => fun _ => matchRec pr h s
  | .inr (.inr (.inl φ)) => fun _ => mergeRec pr h φ
  | .inr (.inr (.inr _)) => fun _ => constRec pr

theorem new_eq (t : Chg) :
    ∑ j, R.a' t j • signedIntegral (R.law' t j).weight = newOf pr h R.t R.P t := by
  rcases t with j | s | φ | k
  · rfl
  · change ∑ _j : Unit, (1 : ℝ) • signedIntegral (matchRec pr h s).weight = _
    rw [Fintype.sum_unique, one_smul]
    rfl
  · change ∑ _j : Unit, (1 : ℝ) • signedIntegral (mergeRec pr h φ).weight = _
    rw [Fintype.sum_unique, one_smul]
    rfl
  · change ∑ _j : Unit, (1 : ℝ) • signedIntegral (constRec pr).weight = _
    rw [Fintype.sum_unique, one_smul]
    rfl

/-- **The `Replacements` of the block**, with the merges replaced by `mergeRec` and the constants
by `constRec`. -/
noncomputable def toReplacements :
    Replacements D (blockSquareAccepted pr) MainAnchor.paperQueries where
  J := J'
  JFintype := instFintypeJ'
  a := R.a'
  law := R.law'
  mass_one t := by
    rcases t with j | t
    · exact sum_signedCoef R.t
    · change ∑ _j : Unit, (1 : ℝ) = 1
      simp
  accept t j z hz e := by
    rcases t with j' | s | φ | k
    · exact R.accept _ j z hz e
    · exact matchRec_accepts pr h s z hz e
    · exact mergeRec_accepts pr h φ z hz e
    · exact constRec_accepts pr z hz e
  unif t j := by
    rcases t with j' | s | φ | k
    · exact R.unif _ j
    · exact matchRec_uniform pr h s
    · exact mergeRec_uniform pr h φ
    · exact constRec_uniform pr
  N := R.N
  N_nonneg := R.N_nonneg
  norm t e F G := by
    rw [R.new_eq t]
    exact R.norm t e F G

/-- The matching components of the constructed replacements are `⊗_p K₁`. -/
theorem toReplacements_match (s : Fin 2) (j : Unit) :
    R.toReplacements.law (.inr (.inl s)) j = matchRec pr h s := rfl

/-- The merge components of the constructed replacements are V3's repairs. -/
theorem toReplacements_merge (φ : PType.Pat .R) (j : Unit) :
    R.toReplacements.law (.inr (.inr (.inl φ))) j = mergeRec pr h φ := rfl

/-- The constant components of the constructed replacements are the strict Paley edges. -/
theorem toReplacements_const (k : PType.Pat .C) (j : Unit) :
    R.toReplacements.law (.inr (.inr (.inr k))) j = constRec pr := rfl

/-- **The replacements, record by record** (for (CP6)): the inputs' signed records for the folds,
`matchRec` for the matchings, `mergeRec` for the merges, `constRec` for the constants. -/
theorem toReplacements_newMeas (t : Chg) :
    R.toReplacements.newMeas t = newOf pr h R.t R.P t :=
  R.new_eq t

/-- The replacement of the matching record `E_s` is `⊗_p K₁` placed by `E_s`. -/
theorem toReplacements_newMeas_match (s : Fin 2) :
    R.toReplacements.newMeas (.inr (.inl s)) = signedIntegral (matchRec pr h s).weight :=
  R.new_eq _

/-- The norms of the constructed replacements are the inputs' norms. -/
theorem toReplacements_N : R.toReplacements.N = R.N := rfl

/-- **The total variation of the comparison law** (`lem:middle-comparison-prices`:
`|ν|_𝔅 ≤ ν_𝔅(1) + 2 t w`, here with equality):
`ν_𝔅 = ν⁺_𝔅 - (t/2) w Π^{--}_{F₁} - (t/2) w Π^{--}_{F₂}` with `w = w_D r/μ̃_𝔅(1)` and every other
component nonnegative. -/
theorem toAtom_absmass (hF : FrameFacts D (blockSquareAccepted pr) MainAnchor.paperQueries) :
    (R.toReplacements.toAtom hF).absmass =
      (R.toReplacements.toAtom hF).numass + 2 * R.t * (D.P⁻¹ * (D.W.w .D * D.r)) := by
  have hP := Replacements.P_inv_nonneg (D := D)
  set w := D.P⁻¹ * (D.W.w .D * D.r) with hw
  have hw0 : 0 ≤ w := mul_nonneg hP (mul_nonneg (D.W.w_nonneg _) D.r_nonneg)
  have hz : ∀ x : ℝ, 0 ≤ x → |x| * 1 - x * 1 = 0 := fun x hx => by rw [abs_of_nonneg hx]; ring
  have key : ∑ i, (|R.toReplacements.coef i| * 1 - R.toReplacements.coef i * 1) = 2 * R.t * w := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sum_type]
    have h1 : ∑ k : Kept, (|R.toReplacements.coef (.inl k)| * 1 -
        R.toReplacements.coef (.inl k) * 1) = 0 :=
      sum_eq_zero fun k _ => hz _ (mul_nonneg hP (keptCoef_nonneg D k))
    have h2 : ∑ s : Fin 2, (|R.toReplacements.coef (.inr (.inl s))| * 1 -
        R.toReplacements.coef (.inr (.inl s)) * 1) = 0 :=
      sum_eq_zero fun s _ => hz _ (mul_nonneg hP (enewCoef_nonneg D))
    have h3 : ∀ t' : Fin 2 ⊕ PType.Pat .R ⊕ PType.Pat .C,
        ∑ x : J' (.inr t'), (|R.toReplacements.coef (.inr (.inr ⟨.inr t', x⟩))| * 1 -
          R.toReplacements.coef (.inr (.inr ⟨.inr t', x⟩)) * 1) = 0 := fun t' =>
      sum_eq_zero fun x _ => hz _ (by
        change 0 ≤ D.P⁻¹ * chgCoef D (.inr t') * 1
        rw [mul_one]
        exact mul_nonneg hP (chgCoef_nonneg D _))
    have h4 : ∀ j : Fin 2,
        ∑ x : J' (.inl j), (|R.toReplacements.coef (.inr (.inr ⟨.inl j, x⟩))| * 1 -
          R.toReplacements.coef (.inr (.inr ⟨.inl j, x⟩)) * 1) = R.t * w := by
      intro j
      change ∑ x : Fin 3, (|D.P⁻¹ * chgCoef D (.inl j) * signedCoef R.t x| * 1 -
        D.P⁻¹ * chgCoef D (.inl j) * signedCoef R.t x * 1) = _
      rw [chgCoef_fold, Fin.sum_univ_three]
      simp only [signedCoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons]
      have ht := R.t_nonneg
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
        abs_of_nonpos (by nlinarith)]
      rw [hw]
      ring
    have H3 : ∑ t' : Fin 2 ⊕ PType.Pat .R ⊕ PType.Pat .C,
        ∑ x : R.toReplacements.J (.inr t'),
          (|R.toReplacements.coef (.inr (.inr ⟨.inr t', x⟩))| * 1 -
            R.toReplacements.coef (.inr (.inr ⟨.inr t', x⟩)) * 1) = 0 :=
      sum_eq_zero fun t' _ => h3 t'
    have H4 : ∑ j : Fin 2, ∑ x : R.toReplacements.J (.inl j),
        (|R.toReplacements.coef (.inr (.inr ⟨.inl j, x⟩))| * 1 -
          R.toReplacements.coef (.inr (.inr ⟨.inl j, x⟩)) * 1) = 2 * R.t * w := by
      rw [Fin.sum_univ_two]
      calc _ = R.t * w + R.t * w := congrArg₂ (· + ·) (h4 0) (h4 1)
        _ = 2 * R.t * w := by ring
    rw [h1, h2, H3, H4]
    ring
  unfold AtomComparison.absmass AtomComparison.numass
  change ∑ i, |R.toReplacements.coef i| * 1 = ∑ i, R.toReplacements.coef i * 1 + _
  have e : ∑ i, |R.toReplacements.coef i| * 1 = ∑ i, R.toReplacements.coef i * 1 +
      ∑ i, (|R.toReplacements.coef i| * 1 - R.toReplacements.coef i * 1) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [e, key]

end ReplacementData

end Block

end Sarkozy.MiddleComparison
