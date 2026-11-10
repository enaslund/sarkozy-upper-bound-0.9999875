module

public import Sarkozy.HsumProof.BandUB
public import Sarkozy.HsumProof.Ledgers

@[expose] public section

/-!
# The rational totals of the upper part of `hsum` (HS)

`UBQ a k d` is the rational bound of `bandBound a d k` of `BandUB.lean` (near or far band),
`bandOK a k` its side conditions, and `bandTot k` the rational bound of the `k`-th band's terms
of the upper part of `SAParts3.hsum` at the ledger's exponent `aT` (`a_G = 71/10⁵` since RG's
rebase; `cSQ`, `cAQ` of `Ledgers.lean`):
`∑_{d=3}^{7} (cSQ k d + cAQ k d) UBQ aT k d`. The kernel checks of `Upper.lean` are stated with
these definitions.
-/

open Finset

namespace Sarkozy.HsumProof

open Sarkozy.NumericalFields

/-- The ledger's exponent `TargetLedger.targetDecay` as a rational: `a_G = 71/10⁵` since RG's
rebase (7 November 2026; it was `a_T = 212956239/250000000000`; the name `aT` is kept). -/
def aT : ℚ := 71 / 100000

theorem aT_cast : ((aT : ℚ) : ℝ) = Sarkozy.TargetLedger.targetDecay := by
  unfold aT Sarkozy.TargetLedger.targetDecay
  push_cast
  ring

/-- The rational bound of `bandBound a d k`. -/
def UBQ (a : ℚ) (k : Fin 310) (d : ℕ) : ℚ := if 301 ≤ k.val then farUB a k d else nearUB a k d

/-- The side conditions of band `k`. -/
def bandOK (a : ℚ) (k : Fin 310) : Bool := if 301 ≤ k.val then farOK a k else nearOK a k

/-- **`bandBound a d k ≤ UBQ a k d`** under the side conditions. -/
theorem bandBound_le_UBQ (a : ℚ) (k : Fin 310) (hok : bandOK a k = true) {d : ℕ} (hd : 2 ≤ d) :
    bandBound a d k ≤ (UBQ a k d : ℝ) := by
  unfold UBQ
  unfold bandOK at hok
  split_ifs with hk
  · simp only [hk, ↓reduceIte] at hok
    exact far_le a k hk hok hd
  · simp only [hk, ↓reduceIte] at hok
    exact near_le a k (by omega) hok hd

/-- The rational bound of the terms of band `k` in the upper part of `hsum`, at `aT`. -/
def bandTot (k : Fin 310) : ℚ :=
  ∑ d ∈ Finset.Icc 3 7, (cSQ k d * UBQ aT k d + cAQ k d * UBQ aT k d)

end Sarkozy.HsumProof
