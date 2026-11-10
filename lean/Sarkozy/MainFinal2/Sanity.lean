module

public import Sarkozy.MainFinal2.Main

@[expose] public section

/-!
# Sanity checks for the second-round obligations (K2)

* `MidRefinement.trivialAll`: the shape of `MidRefinement` is satisfiable (nothing replaced at any
  atom, the bracket is (CP3)'s). This is a non-vacuity witness of the structure only: with it,
  `EnvelopeParts2.hothPre` must carry the whole (CP4) price, so the gate `hTK` would fail for the
  paper's numbers (`T ≈ 0.6075 < S + A ≈ 0.98`). The paper's refinement replaces the fold and
  matching records of the middle blocks.
* `midAtom_clique`: no square-clique atom is refined; `midAtom_upper`: no upper block is refined.
* `tPaper_mem`: the paper's `t = 127/500` lies in `[0, 1]`.
-/

namespace Sarkozy.MainFinal2

open Sarkozy.TheoremC Sarkozy.TheoremCBlock
open Sarkozy.PartVLaws (PrefixCoord)

/-- **`MidRefinement` is satisfiable** (all atoms trivial, bounds `0`). -/
noncomputable def MidRefinement.trivialAll {a : ℝ}
    {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
    {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
    {J : ℕ → Type} [∀ L, Fintype (J L)] {p : ∀ L, J L → ℕ} [∀ L j, NeZero (p L j)]
    {S₀ : Bk → ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀ blk}
    {FS : FirstStage a m₀ blk p S₀ R} (GB : GramBracket a m₀ blk p S₀ FS)
    (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS) (mid : Bk → Prop) [DecidablePred mid] :
    MidRefinement GB CL mid where
  R L β _ := AtomRefinement.trivial GB CL L β
  KL _ := 0
  KR _ := 0
  KL_bound _ _ _ := le_of_eq (Finset.sum_eq_zero fun i _ => Empty.elim i)
  KR_bound _ _ _ := le_of_eq (Finset.sum_eq_zero fun i _ => Empty.elim i)

/-- No square-clique atom is refined. -/
theorem midAtom_clique (hW : Target.Weil)
    (A : BlockSpecPaper.PaperAnalyticInputs PaperNumbers.paperCell)
    (q : PrefixCoord) : midAtom hW A (.inl q) = false := rfl

/-- No upper block is refined. -/
theorem midAtom_upper (hW : Target.Weil)
    (A : BlockSpecPaper.PaperAnalyticInputs PaperNumbers.paperCell)
    (b : MainFinal.Blk) (h : ComparisonLawPaper.specUpper (MainFinal.specF hW A b) = true) :
    midAtom hW A (.inr b) = false := by
  simp [midAtom, h]

/-- The paper's `t = 127/500` lies in `[0, 1]`. -/
theorem tPaper_mem : 0 ≤ tPaper ∧ tPaper ≤ 1 := ⟨tPaper_nonneg, tPaper_le_one⟩

end Sarkozy.MainFinal2
