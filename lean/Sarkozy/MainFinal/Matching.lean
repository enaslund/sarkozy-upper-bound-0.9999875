module

public import Sarkozy.MainFinal.Structure

@[expose] public section

/-!
# `hrepl` from the prices of the records that are not replaced (`prop:record:matching`(ii))

B3's `hrepl` asks that the replaced (fold and matching) records of `CL` carry at least
`∑_𝔟(s_𝔟 + a_𝔟) − (T^{ledger} − T_K)` of the (CP4) price at every scale. Since every atom's price
splits into the replaced and the other records, this is the same as a bound on the others:
`∑_𝔟 ∑_{t ∉ repl} (π^s_t + π^a_t) ≤ T^{ledger} − T_K`. This is the paper's form
`T = T_K + T_QE + S_oth + A_oth + S_u + A_u + 10⁻¹²` of `prop:record:matching`(ii), with the
matching price `T_QE` counted in `T_K` (B3).

* `hrepl_of_others`: the split, for any price table;
* `EnvelopeParts.ofOthers`: B3's inputs with `hrepl` replaced by a bound `T_oth` on the records
  that are not replaced and the scalar gate `T_K + T_oth ≤ T^{ledger}`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MainFinal

open Sarkozy.RecordExpansion
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainTarget Sarkozy.GramBracketPaper Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (paperAtomMap)
open Sarkozy.EnvelopesPaper (PrefixRefinement)

/-- **The split of the (CP4) price into replaced and other records.** If the records outside
`repl` cost at most `T_oth` and `T_K + T_oth ≤ T`, then the replaced records carry at least
`∑_𝔟 (s_𝔟 + a_𝔟) − (T − T_K)`. -/
theorem hrepl_of_others {ι : Type} [Fintype ι] {T : ι → Type} [∀ b, Fintype (T b)]
    [∀ b, DecidableEq (T b)] (π : ∀ b, T b → ChangeType → ℝ) (repl : ∀ b, Finset (T b))
    {Tl TK Toth : ℝ} (hoth : ∑ b, ∑ t ∈ univ \ repl b, (π b t .sym + π b t .skew) ≤ Toth)
    (hT : TK + Toth ≤ Tl) :
    ∑ b, (symTotal π b + skewTotal π b) - (Tl - TK) ≤
      ∑ b, ∑ t ∈ repl b, (π b t .sym + π b t .skew) := by
  have h : ∀ b, symTotal π b + skewTotal π b =
      ∑ t ∈ repl b, (π b t .sym + π b t .skew) +
        ∑ t ∈ univ \ repl b, (π b t .sym + π b t .skew) := by
    intro b
    unfold symTotal skewTotal
    rw [← sum_add_distrib, ← sum_union disjoint_sdiff, union_sdiff_of_subset (subset_univ _)]
  rw [Finset.sum_congr rfl fun b _ => h b, sum_add_distrib]
  linarith

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs PaperNumbers.paperCell} {C : ComparisonParts hW hMR hFour A}

/-- **B3's (CP6)/(CP8)(c) inputs with `hrepl` from the other records**
(`prop:record:matching`(ii)): `hrepl` is proved from `hoth` (the records not replaced cost at
most `T_oth` at every scale; *open*, a property of `CL`) and the scalar gate
`T_K + T_oth ≤ T^{ledger}` (*open*, numerical). -/
noncomputable def EnvelopeParts.ofOthers
    (PR : PrefixRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
      (paperIn PaperNumbers.paperCell) (paperGi hW A)) C.CL)
    (TK : ℝ) (hK : ∑ β, PR.KL β ≤ TK ∧ ∑ β, PR.KR β ≤ TK) (Toth : ℝ)
    (hoth : ∀ L, ∑ b, ∑ t ∈ univ \ PR.repl L b, (C.CL.π L b t .sym + C.CL.π L b t .skew) ≤ Toth)
    (hTK : TK + Toth ≤ targetLedger.T) (σCL : ℝ)
    (hCL : ∀ L, ∑ b, TheoremCBlock.oneWeight (paperAtomMap bOf) paperTail paperPP paperEP L b ^
      ((1 : ℝ) / 4) * (symTotal (C.CL.π L) b + skewTotal (C.CL.π L) b) ≤ σCL) :
    EnvelopeParts hW hMR hFour A C where
  PR := PR
  TK := TK
  hK := hK
  hrepl := fun L => hrepl_of_others (C.CL.π L) (PR.repl L) (hoth L) hTK
  σCL := σCL
  hCL := hCL

end Sarkozy.MainFinal
