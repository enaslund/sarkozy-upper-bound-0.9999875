module

public import Sarkozy.MiddleRefinement.Frame
public import Sarkozy.MiddleComparison.Sanity
public import Sarkozy.MiddleRefinement.Numbers

@[expose] public section

/-!
# Non-vacuity of `SignedSideGrams` (MRG)

A toy instance of the block-Gram hypothesis of `prop:signed-sides` at any V3 frame: for B7's
trivial replacement (every changed record replaced by itself, `Replacements.trivial`), the block
Grams hold with the equal sides `d_L = d_R = 2 k_D` from the layer cap of the fold alone:
`(Π_F + r·2k_D D   Π_F ; ·   Π_F + r·2k_D D) = (P P; P P) + k_D r (D  -D; -D  D)` with
`P = Π_F + k_D r D ⪰_ι 0` (the cap `lem:front12:reference`(ii)) and `D ⪰_ι 0`.

So the hypothesis is not contradictory in itself; its content at the paper's records (the signed
fold records of `def:record:mixture`(c),(d)) and the paper's sides is `prop:signed-sides`(i),(ii).
(At the trivial replacement the side coefficient `w_D·2k_D - v_D` is `≤ 0` by the protection
`v_D ≥ 2 k_D w_D`: the fold's own companion already carries the bracket; the gate `k_s ≥ 0` is a
separate, numerical, input, checked at the paper's sides in `Numbers.lean`.)
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleRefinement

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.MiddleComparison
open Sarkozy.BlockSpecPaper.AllpData (allpRecord)

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]

theorem trivial_newMeas (D : FrameData X) {E : Type} (Q : Queries E)
    (h2 : ∀ f (o : f.Obj × Fin 2) (g : X → ℝ),
      (D.F.two f).expect (fun y => g (y o)) = (FiniteLaw.uniform X).expect g) (t : Chg) :
    (Replacements.trivial D Q h2).newMeas t = recM D.F (true, chgPat t) := by
  show (∑ _j : Unit, (1 : ℝ) • signedIntegral (midComponent D.F (true, chgPat t)).weight) = _
  simp [recM]

/-- **`SignedSideGrams` is satisfiable**: at B7's trivial replacement, with the sides `2 k_D`,
from the layer cap of the folds (`lem:front12:reference`(ii)) and `k_D ≥ 0`. -/
theorem signedSideGrams_trivial (D : FrameData X) {E : Type} (Q : Queries E)
    (h2 : ∀ f (o : f.Obj × Fin 2) (g : X → ℝ),
      (D.F.two f).expect (fun y => g (y o)) = (FiniteLaw.uniform X).expect g)
    (hcap : MiddleLayerCaps D.F D.I.k D.r) (hk : 0 ≤ D.I.k .D) :
    SignedSideGrams D (Replacements.trivial D Q h2) (2 * D.I.k .D) (2 * D.I.k .D) := by
  have key : ∀ j : Fin 2, reservedCut.Bracket
      (foldRec D j + (D.r * (2 * D.I.k .D)) • foldDiag D j)
      ((Replacements.trivial D Q h2).newMeas (.inl j))
      (foldRec D j + (D.r * (2 * D.I.k .D)) • foldDiag D j) := by
    intro j
    have ha : 0 ≤ D.I.k .D * D.r := mul_nonneg hk D.r_nonneg
    have hP : reservedCut.Positive
        (signedIntegral (midComponent D.F (true, ⟨.D, foldPat j⟩)).weight -
          (-(D.I.k .D * D.r)) •
            signedIntegral (midComponent D.F (false, ⟨.D, foldPat j⟩)).weight) :=
      hcap .D (foldPat j)
    have h1 := bracket_add hP.bracket_self
      (bracket_smul (bracket_neg (D.diag_positive .D (foldPat j)).bracket_self) ha)
    rw [trivial_newMeas]
    have e1 : signedIntegral (midComponent D.F (true, ⟨.D, foldPat j⟩)).weight -
        (-(D.I.k .D * D.r)) • signedIntegral (midComponent D.F (false, ⟨.D, foldPat j⟩)).weight +
          (D.I.k .D * D.r) • D.diag .D (foldPat j) =
        foldRec D j + (D.r * (2 * D.I.k .D)) • foldDiag D j := by
      apply LinearMap.ext
      intro f
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        FrameData.diag, recM, chgPat, foldDiag, foldRec]
      ring
    have e2 : signedIntegral (midComponent D.F (true, ⟨.D, foldPat j⟩)).weight -
        (-(D.I.k .D * D.r)) • signedIntegral (midComponent D.F (false, ⟨.D, foldPat j⟩)).weight +
          (D.I.k .D * D.r) • -D.diag .D (foldPat j) = recM D.F (true, chgPat (.inl j)) := by
      apply LinearMap.ext
      intro f
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.neg_apply, smul_eq_mul, FrameData.diag, recM, chgPat]
      ring
    rw [e1, e2] at h1
    exact h1
  exact ⟨key 0, key 1⟩

omit [DecidableEq X] [Nonempty X] in
/-- A positive measure on both diagonal entries brackets `0`: `(e P   0 ; ·   e P) ⪰_ι 0`. -/
theorem bracket_diag_zero {P : SlotMeasure X} (hP : reservedCut.Positive P) {e : ℝ}
    (he : 0 ≤ e) : reservedCut.Bracket (e • P) 0 (e • P) := by
  have h := bracket_smul (bracket_add hP.bracket_self (bracket_neg hP.bracket_self))
    (show 0 ≤ e / 2 by linarith)
  have e1 : (e / 2) • (P + P) = e • P := by
    rw [← two_smul ℝ P, smul_smul]
    congr 1
    ring
  have e2 : (e / 2) • (P + -P) = 0 := by simp
  rw [e1, e2] at h
  exact h

/-- **`SignedSideGrams` at any equal sides `d ≥ 2 k_D`** for B7's trivial replacement
(`signedSideGrams_trivial` and the enlargement of `lem:record:asymmetric-gram`(a) by the positive
diagonal `r (d - 2k_D) D^j`). -/
theorem signedSideGrams_trivial_ge (D : FrameData X) {E : Type} (Q : Queries E)
    (h2 : ∀ f (o : f.Obj × Fin 2) (g : X → ℝ),
      (D.F.two f).expect (fun y => g (y o)) = (FiniteLaw.uniform X).expect g)
    (hcap : MiddleLayerCaps D.F D.I.k D.r) (hk : 0 ≤ D.I.k .D) {d : ℝ}
    (hd : 2 * D.I.k .D ≤ d) :
    SignedSideGrams D (Replacements.trivial D Q h2) d d := by
  have G := signedSideGrams_trivial D Q h2 hcap hk
  have he : 0 ≤ D.r * (d - 2 * D.I.k .D) := mul_nonneg D.r_nonneg (by linarith)
  have key : ∀ j : Fin 2, reservedCut.Bracket
      (foldRec D j + (D.r * (2 * D.I.k .D)) • foldDiag D j)
      ((Replacements.trivial D Q h2).newMeas (.inl j))
      (foldRec D j + (D.r * (2 * D.I.k .D)) • foldDiag D j) →
      reservedCut.Bracket (foldRec D j + (D.r * d) • foldDiag D j)
        ((Replacements.trivial D Q h2).newMeas (.inl j)) (foldRec D j + (D.r * d) • foldDiag D j) :=
    by
    intro j h
    have h' := bracket_add h (bracket_diag_zero (D.diag_positive .D (foldPat j)) he)
    have e1 : foldRec D j + (D.r * (2 * D.I.k .D)) • foldDiag D j +
        (D.r * (d - 2 * D.I.k .D)) • D.diag .D (foldPat j) =
        foldRec D j + (D.r * d) • foldDiag D j := by
      rw [add_assoc, ← add_smul]
      congr 2
      ring
    rw [e1, add_zero] at h'
    exact h'
  exact ⟨key 0 G.gram₁, key 1 G.gram₂⟩

/-- **The paper's sides exceed `2 k_D`** on every piece (kernel): `2 k_{D,i} ≤ d_s(i)`, so at the
paper's sides the block Grams are satisfiable on every frame of piece `i` (by the trivial
replacement, `signedSideGrams_trivial_ge`). -/
theorem kD_check : ∀ i : Fin 33, 2 * (allpRecord i).kD ≤ sideQ i := by decide +kernel

end Sarkozy.MiddleRefinement
