module

public import Sarkozy.MainFinalF1.Main

@[expose] public section

/-!
# Sanity checks for the F1 port (F1P)

* **`paperCell_eq_band`**: on a band site above `X_Ch`, the paper's cell value is `⟨1, f1Cell p⟩`;
  so **`paperCell_eq_iff_band`**: two primes of the same band lie in the same block of `paperCell`
  iff they lie in the same block of `f1Cell`. The recorded band cells (`recordedBandRule`,
  `def:record:upper-bands`(b)) are shared, as the brief says; only the encoding of the label
  differs (which is why E2's bridge had to be re-proved, `Bands.lean`).
* `midAtom_clique`, `midAtom_upper` at `f1Cell` (as K2's `Sanity.lean`).

The structures of this directory are K1's, K2's, `MainFinal3`'s, `EnvPrefix`'s and C10's with the
cell changed, field by field (no field added; `NC`, `hHist` removed; the numbers `chargeC2`,
`chargeC3` of the final inequalities replaced by N2's `f1c2`, `f1c3`). Their non-vacuity rests on
the same field-by-field comparison with the paper as at `paperCell` (the reports of K1, K2, C10,
E1, E2, E4).
-/

namespace Sarkozy.MainFinalF1

open Sarkozy.PartV Sarkozy.PaperNumbers Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PrefixCoord)
open Sarkozy.AnalyticCells (f1Cell)

/-- **The paper's cell value on a band is `⟨1, f1Cell p⟩`** (`def:record:upper-bands`(b)). -/
theorem paperCell_eq_band {p : ℕ} {k : Fin 310} (hs : siteOf p = .inr k) (hX : XCh ≤ p) :
    paperCell p = Nat.pair 1 (f1Cell p) := by
  have hX' : ¬ p < XCh := not_lt.mpr hX
  unfold paperCell paperCellWith f1Cell AnalyticCells.f1Pos AnalyticCells.f1CellList
    AnalyticCells.f1Card cellPos cellListOf cellCardOf
  simp only [hX', ↓reduceIte, hs]
  rfl

/-- **The band blocks of `paperCell` and `f1Cell` coincide**: two primes of band `k` above `X_Ch`
have the same `paperCell` value iff they have the same `f1Cell` value. -/
theorem paperCell_eq_iff_band {p p' : ℕ} {k : Fin 310} (hs : siteOf p = .inr k)
    (hs' : siteOf p' = .inr k) (hX : XCh ≤ p) (hX' : XCh ≤ p') :
    paperCell p = paperCell p' ↔ f1Cell p = f1Cell p' := by
  rw [paperCell_eq_band hs hX, paperCell_eq_band hs' hX']
  constructor
  · intro h
    exact (Nat.pair_eq_pair.mp h).2
  · intro h
    rw [h]

/-- No square-clique atom is refined (at `f1Cell`). -/
theorem midAtom_clique (hW : Target.Weil) (A : BlockSpecPaper.PaperAnalyticInputs f1Cell)
    (q : PrefixCoord) : midAtom hW A (.inl q) = false := rfl

/-- No upper block is refined (at `f1Cell`). -/
theorem midAtom_upper (hW : Target.Weil) (A : BlockSpecPaper.PaperAnalyticInputs f1Cell)
    (b : Blk) (h : ComparisonLawPaper.specUpper (specF hW A b) = true) :
    midAtom hW A (.inr b) = false := by
  simp [midAtom, h]

end Sarkozy.MainFinalF1
