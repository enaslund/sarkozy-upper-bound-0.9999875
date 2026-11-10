module

public import Sarkozy.PartVLaws.RowConditional
public import Sarkozy.TailCorr.Core

/-! The six fold and four nontrivial matching estimates of the tail datum. -/

@[expose] public section

namespace Sarkozy.PartVLaws

open Sarkozy.Labellings Sarkozy.JointRows Sarkozy.FiveType Sarkozy.FiveType.TwoCoord
  Sarkozy.PartV Sarkozy.TailCorr Sarkozy.PartVLaws.FieldGraphs

variable {p : ℕ} [Fact p.Prime]

theorem tail_fold_two (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (h4 : Extraction.FourCycleBound p) (hne : TailNonempty p) (f' : FieldTy)
    (h : RowHyp0 (lam2 (tailFieldLaws p hne)) f') :
    FoldCorr (rowD0 (lam2 (tailFieldLaws p hne)) f' h) (tailCF (tailOrd f') * tailR p) := by
  intro b hb
  let πE := (lam2 (tailFieldLaws p hne) .E f').map
    (fun y => (rows0 y : Fin 3 → f'.Obj × ZMod 2 → ZMod p))
  let πF := (lam2 (tailFieldLaws p hne) .F f').map
    (fun y => (rows0 y : Fin 3 → f'.Obj × ZMod 2 → ZMod p))
  have hbE : (nuOf πE).weight b ≠ 0 := hb
  have hbi := graph_middle_injective (fieldGraph .E (toFType f') (Fin 2))
    (hne.two .E (toFType f')) (cTwo f') b (by rwa [← two0E_eq p hne f'])
  change KernelCorr (nubOf πE b) (kernelOf πE πF b) (tailCF (tailOrd f') * tailR p)
  cases f' with
  | L =>
    have hc := RowCase.conditional_row_correlation .FL2 hp hW h4 (cTwo .L)
      (hne.two .F .L) πE πF (two0F_eq p hne .L) h.supp b hbi hbE
    simpa [RowCase.cap, tailCF, tailOrd, tailOrdinary, toFType, tailR_eq_inv_sqrt] using hc
  | F =>
    have hc := RowCase.conditional_row_correlation .FF2 hp hW h4 (cTwo .F)
      (hne.two .F .F) πE πF (two0F_eq p hne .F) h.supp b hbi hbE
    simpa [RowCase.cap, tailCF, tailOrd, tailOrdinary, toFType, tailR_eq_inv_sqrt] using hc
  | E =>
    have hc := RowCase.conditional_row_correlation .FE2 hp hW h4 (cTwo .E)
      (hne.two .F .E) πE πF (two0F_eq p hne .E) h.supp b hbi hbE
    simpa [RowCase.cap, tailCF, tailOrd, tailOrdinary, toFType, tailR_eq_inv_sqrt] using hc

theorem tail_fold_one (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (h4 : Extraction.FourCycleBound p) (hne : TailNonempty p) (f' : FieldTy)
    (h : RowHyp0 (lam1 (tailFieldLaws p hne)) f') :
    FoldCorr (rowD0 (lam1 (tailFieldLaws p hne)) f' h) (tailCF (tailRes f') * tailR p) := by
  intro b hb
  let πE := (lam1 (tailFieldLaws p hne) .E f').map
    (fun y => (rows0 y : Fin 3 → f'.Obj × Unit → ZMod p))
  let πF := (lam1 (tailFieldLaws p hne) .F f').map
    (fun y => (rows0 y : Fin 3 → f'.Obj × Unit → ZMod p))
  have hbE : (nuOf πE).weight b ≠ 0 := hb
  have hbi := graph_middle_injective (fieldGraph .E (toFType f') (Fin 1))
    (hne.one .E (toFType f')) (cOne f') b (by rwa [← one0E_eq p hne f'])
  change KernelCorr (nubOf πE b) (kernelOf πE πF b) (tailCF (tailRes f') * tailR p)
  cases f' with
  | L =>
    have hc := RowCase.conditional_row_correlation .FL1 hp hW h4 (cOne .L)
      (hne.one .F .L) πE πF (one0F_eq p hne .L) h.supp b hbi hbE
    simpa [RowCase.cap, tailCF, tailRes, tailReserved, toFType, tailR_eq_inv_sqrt] using hc
  | F =>
    have hc := RowCase.conditional_row_correlation .FF1 hp hW h4 (cOne .F)
      (hne.one .F .F) πE πF (one0F_eq p hne .F) h.supp b hbi hbE
    simpa [RowCase.cap, tailCF, tailRes, tailReserved, toFType, tailR_eq_inv_sqrt] using hc
  | E =>
    have hc := RowCase.conditional_row_correlation .FE1 hp hW h4 (cOne .E)
      (hne.one .F .E) πE πF (one0F_eq p hne .E) h.supp b hbi hbE
    simpa [RowCase.cap, tailCF, tailRes, tailReserved, toFType, tailR_eq_inv_sqrt] using hc

theorem tail_match_two (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (h4 : Extraction.FourCycleBound p) (hne : TailNonempty p) (f' : FieldTy) (hf' : f' ≠ .E)
    (h : RowHyp0 (lam2 (tailFieldLaws p hne)) f') :
    MatchNorm (rowD0 (lam2 (tailFieldLaws p hne)) f' h) ((tailOrd f').h * tailR p) := by
  intro b hb
  let πE := (lam2 (tailFieldLaws p hne) .E f').map
    (fun y => (rows0 y : Fin 3 → f'.Obj × ZMod 2 → ZMod p))
  have hbE : (nuOf πE).weight b ≠ 0 := hb
  have hbi := graph_middle_injective (fieldGraph .E (toFType f') (Fin 2))
    (hne.two .E (toFType f')) (cTwo f') b (by rwa [← two0E_eq p hne f'])
  change NormBound (nubOf πE b) (kernelOf πE πE b) ((tailOrd f').h * tailR p)
  cases f' with
  | L =>
    have hc := RowCase.conditional_row_norm .EL2 hp hW h4 (cTwo .L)
      (hne.two .E .L) πE (two0E_eq p hne .L) h.exch b hbi hbE
    simpa [RowCase.cap, tailOrd, tailOrdinary, toFType, tailR_eq_inv_sqrt] using hc
  | F =>
    have hc := RowCase.conditional_row_norm .EF2 hp hW h4 (cTwo .F)
      (hne.two .E .F) πE (two0E_eq p hne .F) h.exch b hbi hbE
    simpa [RowCase.cap, tailOrd, tailOrdinary, toFType, tailR_eq_inv_sqrt] using hc
  | E => exact False.elim (hf' rfl)

theorem tail_match_one (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (h4 : Extraction.FourCycleBound p) (hne : TailNonempty p) (f' : FieldTy) (hf' : f' ≠ .E)
    (h : RowHyp0 (lam1 (tailFieldLaws p hne)) f') :
    MatchNorm (rowD0 (lam1 (tailFieldLaws p hne)) f' h) ((tailRes f').h * tailR p) := by
  intro b hb
  let πE := (lam1 (tailFieldLaws p hne) .E f').map
    (fun y => (rows0 y : Fin 3 → f'.Obj × Unit → ZMod p))
  have hbE : (nuOf πE).weight b ≠ 0 := hb
  have hbi := graph_middle_injective (fieldGraph .E (toFType f') (Fin 1))
    (hne.one .E (toFType f')) (cOne f') b (by rwa [← one0E_eq p hne f'])
  change NormBound (nubOf πE b) (kernelOf πE πE b) ((tailRes f').h * tailR p)
  cases f' with
  | L =>
    have hc := RowCase.conditional_row_norm .EL1 hp hW h4 (cOne .L)
      (hne.one .E .L) πE (one0E_eq p hne .L) h.exch b hbi hbE
    simpa [RowCase.cap, tailRes, tailReserved, toFType, tailR_eq_inv_sqrt] using hc
  | F =>
    have hc := RowCase.conditional_row_norm .EF1 hp hW h4 (cOne .F)
      (hne.one .E .F) πE (one0E_eq p hne .F) h.exch b hbi hbE
    simpa [RowCase.cap, tailRes, tailReserved, toFType, tailR_eq_inv_sqrt] using hc
  | E => exact False.elim (hf' rfl)

end Sarkozy.PartVLaws
