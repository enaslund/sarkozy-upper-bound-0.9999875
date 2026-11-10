module

public import Sarkozy.PositiveRoots.CoherentMeanGeometry
public import Sarkozy.PositiveRoots.CoherentTraceChart
public import Sarkozy.PartV.CoherentCovarianceData
public import Sarkozy.PositiveRoots.CoherentProductMaps

/-! The covariance cases and costs in the actual core/private coordinates. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.PartV.CoherentDictionary

def coreSupport (side : Bool) (S : Support) : Finset (Fin 4) := corePart (chamberSupport side S)
def privateSupport (side : Bool) (S : Support) : Finset (Fin 2) := privatePart (chamberSupport side S)

def corePairCost (S T : Support) : ℕ :=
  16 * (if coreSupport true S = coreSupport true T then 2 else 1) *
    (if coreSupport false S = coreSupport false T then 2 else 1)

def privatePairCost (S T : Support) : ℕ :=
  (if privateSupport true S = privateSupport true T then 2 else 1) *
    (if privateSupport false S = privateSupport false T then 2 else 1)

theorem covariance_chart_cases : ∀ sc ∈ dictionary39, ∀ tc ∈ dictionary39,
    if (covarianceCase sc.1 tc.1).1 then
      GoodPair (privateSupport true sc.1) (privateSupport true tc.1) ∧
        GoodPair (privateSupport false sc.1) (privateSupport false tc.1)
    else GoodPair (coreSupport true sc.1) (coreSupport true tc.1) ∧
      GoodPair (coreSupport false sc.1) (coreSupport false tc.1) := by decide +kernel

theorem covariance_chart_costs : ∀ sc ∈ dictionary39, ∀ tc ∈ dictionary39,
    coreProductCost sc.1 tc.1 = corePairCost sc.1 tc.1 ∧
      privateProductCost sc.1 tc.1 = privatePairCost sc.1 tc.1 := by decide +kernel

theorem corePairCost_real (S T : Support) :
    (corePairCost S T : ℝ) = 16 * productFactor (coreSupport true S) (coreSupport true T) *
      productFactor (coreSupport false S) (coreSupport false T) := by
  unfold corePairCost productFactor
  split_ifs <;> norm_num

theorem privatePairCost_real (S T : Support) :
    (privatePairCost S T : ℝ) = productFactor (privateSupport true S) (privateSupport true T) *
      productFactor (privateSupport false S) (privateSupport false T) := by
  unfold privatePairCost productFactor
  split_ifs <;> norm_num

end Sarkozy.PositiveRoots.CoherentFrame
