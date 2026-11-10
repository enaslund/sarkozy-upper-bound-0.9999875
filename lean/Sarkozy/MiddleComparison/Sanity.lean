module

public import Sarkozy.MiddleComparison.Paper
public import Sarkozy.MiddleComparison.Prices

@[expose] public section

/-!
# Non-vacuity checks for `Replacements` (`subsec:middle-comparison`)

* `FrameFacts.mono`: the frame facts pass to a weaker acceptance relation.
* `Replacements.trivial`: on any frame whose two-layer field laws have uniform vertex marginals,
  replacing every changed record by itself (`J = Unit`, `a = 1`, `N = 0`) satisfies every field of
  `Replacements` except acceptance, which is taken trivially (`acc = True`). So the mass, the
  uniformity and the norm fields are consistent with each other and with the frame; acceptance of
  the replacements is the genuine content of `lem:signed-components`, `lem:record:e-law`(a),
  `cor:merge-repair` and `lem:record:accepting-c2` (the replaced records themselves do not
  accept).
* `trivial_atom`: on V3's frame of a paper middle block (uniform root), `toAtom` of the trivial
  replacement is an `AtomComparison` of A1's `λ_𝔅`; its prices are the deletions only
  (`trivial_sprice`: `(6 v_R r³ + 2 v_D (f₁ + h₁) r³ + 2 v_C r⁴)/P(r) · sel`; `trivial_aprice`:
  `0`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleComparison

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.ComparisonLawPaper Sarkozy.FirstStagePaper Sarkozy.PartVLaws Sarkozy.CancellationSteps

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]

/-- The frame facts hold for any weaker acceptance relation. -/
theorem FrameFacts.mono {D : FrameData X} {acc acc' : X → X → Prop} {E : Type} {Q : Queries E}
    (h : FrameFacts D acc Q) (hw : ∀ x y, acc x y → acc' x y) : FrameFacts D acc' Q where
  two_unif := h.two_unif
  one_unif := h.one_unif
  new_unif := h.new_unif
  kept_accept k z hz e := hw _ _ (h.kept_accept k z hz e)
  new_accept s z hz e := hw _ _ (h.new_accept s z hz e)

/-- **The trivial replacement**: every changed record replaced by itself, with norms `0`, under the
trivial acceptance relation. -/
noncomputable def Replacements.trivial (D : FrameData X) {E : Type} (Q : Queries E)
    (h2 : ∀ f (o : f.Obj × Fin 2) (g : X → ℝ),
      (D.F.two f).expect (fun y => g (y o)) = (FiniteLaw.uniform X).expect g) :
    Replacements D (fun _ _ => True) Q where
  J _ := Unit
  a _ _ := 1
  law t _ := midComponent D.F (true, chgPat t)
  mass_one _ := by simp
  accept _ _ _ _ _ := True.intro
  unif t _ := emit_uniform _ _ (h2 _)
  N _ _ := 0
  N_nonneg _ _ := le_rfl
  norm t e F G := by
    have h0 : (∑ _j : Unit, (1 : ℝ) • signedIntegral (midComponent D.F (true, chgPat t)).weight) -
        recM D.F (true, chgPat t) = 0 := by
      simp [recM]
    rw [h0, changePart_zero]
    simp [ReflectionCut.form]

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-- **On a paper middle block**, the trivial replacement gives an `AtomComparison` of A1's first
stage (with the trivial acceptance relation). -/
noncomputable def trivial_atom (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleUniformInputs blockOf b) :
    AtomComparison (specLam hW In (.middleUniform M)) (fun _ _ => True) MainAnchor.paperQueries :=
  ((Replacements.trivial (frameU In M) MainAnchor.paperQueries (factsU In M).two_unif).toAtom
    ((factsU In M).mono fun _ _ _ => True.intro)).congrLam (lamU hW In M)

omit [Fintype B] in
/-- The symmetric price of the trivial replacement is the price of the deletions. -/
theorem trivial_sprice (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleUniformInputs blockOf b) (hh : 0 ≤ M.I.h₁) (sel : ℝ) :
    (trivial_atom hW In M).sprice sel =
      (6 * M.W.v .R * M.r ^ 3 + 2 * M.W.v .D * (M.I.f₁ + M.I.h₁) * M.r ^ 3 +
        2 * M.W.v .C * M.r ^ 4) / (frameU In M).P * sel := by
  change ((Replacements.trivial (frameU In M) MainAnchor.paperQueries
    (factsU In M).two_unif).toAtom ((factsU In M).mono fun _ _ _ => True.intro)).sprice sel = _
  rw [Replacements.sprice_eq _ _ (add_nonneg M.hf₁ hh)]
  simp [Replacements.trivial]
  exact Or.inl rfl

omit [Fintype B] in
/-- The skew price of the trivial replacement is `0`. -/
theorem trivial_aprice (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleUniformInputs blockOf b) (sel : ℝ) : (trivial_atom hW In M).aprice sel = 0 := by
  change ((Replacements.trivial (frameU In M) MainAnchor.paperQueries
    (factsU In M).two_unif).toAtom ((factsU In M).mono fun _ _ _ => True.intro)).aprice sel = _
  rw [Replacements.aprice_eq]
  simp [Replacements.trivial]

end Sarkozy.MiddleComparison
