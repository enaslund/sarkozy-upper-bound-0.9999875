module

public import Sarkozy.Certificates.Exponential



@[expose] public section

namespace Sarkozy.Certificates

def expOneInterval : Interval := ⟨(2718281828459045235360287 / 1000000000000000000000000), (84946307139345163605009 / 31250000000000000000000)⟩
def expOneWitness : ExpWitness := ⟨1, 28, (2718281828459045235360287 / 1000000000000000000000000), (84946307139345163605009 / 31250000000000000000000)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem expOneValid : expOneWitness.Valid 1 expOneInterval := by
  norm_num [ExpWitness.Valid, expOneWitness, expOneInterval, expSeries, expRemainder,
    Finset.sum_range_succ, Nat.factorial]

theorem expOneBounds : expOneInterval.Contains (Real.exp (1 : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound expOneValid

def expMinusOneInterval : Interval := ⟨(367879441171442321595523 / 1000000000000000000000000), (91969860292860580398881 / 250000000000000000000000)⟩
def expMinusOneWitness : ExpWitness := ⟨1, 28, (367879441171442321595523 / 1000000000000000000000000), (91969860292860580398881 / 250000000000000000000000)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem expMinusOneValid : expMinusOneWitness.Valid (-1) expMinusOneInterval := by
  norm_num [ExpWitness.Valid, expMinusOneWitness, expMinusOneInterval, expSeries, expRemainder,
    Finset.sum_range_succ, Nat.factorial]

theorem expMinusOneBounds : expMinusOneInterval.Contains (Real.exp ((-1) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound expMinusOneValid

def expLogBlockLowerInterval : Interval := ⟨(43182999999999999962004877317 / 50000000000000000000000), (8636599999999999992401021009 / 10000000000000000000000)⟩
def expLogBlockLowerWitness : ExpWitness := ⟨14, 28, (1327377618306040374665909 / 500000000000000000000000), (2654755236612080749331819 / 1000000000000000000000000)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem expLogBlockLowerValid : expLogBlockLowerWitness.Valid (13668934451818942939 / 1000000000000000000) expLogBlockLowerInterval := by
  norm_num [ExpWitness.Valid, expLogBlockLowerWitness, expLogBlockLowerInterval, expSeries, expRemainder,
    Finset.sum_range_succ, Nat.factorial]

theorem expLogBlockLowerBounds : expLogBlockLowerInterval.Contains (Real.exp ((13668934451818942939 / 1000000000000000000) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound expLogBlockLowerValid

def expLogBlockUpperInterval : Interval := ⟨(172732000000000000020751168547 / 200000000000000000000000), (53978750000000000006485024831 / 62500000000000000000000)⟩
def expLogBlockUpperWitness : ExpWitness := ⟨14, 28, (2654755236612080749521443 / 1000000000000000000000000), (663688809153020187380361 / 250000000000000000000000)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem expLogBlockUpperValid : expLogBlockUpperWitness.Valid (683446722590947147 / 50000000000000000) expLogBlockUpperInterval := by
  norm_num [ExpWitness.Valid, expLogBlockUpperWitness, expLogBlockUpperInterval, expSeries, expRemainder,
    Finset.sum_range_succ, Nat.factorial]

theorem expLogBlockUpperBounds : expLogBlockUpperInterval.Contains (Real.exp ((683446722590947147 / 50000000000000000) : ℝ)) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] using
    ExpWitness.sound expLogBlockUpperValid

def logBlockInterval : Interval := ⟨(13668934451818942939 / 1000000000000000000), (683446722590947147 / 50000000000000000)⟩

set_option maxHeartbeats 2000000 in
theorem log_blockScale_bounds : logBlockInterval.Contains (Real.log (blockScale : ℝ)) := by
  apply Interval.log_sound (I := ⟨863660, 863660⟩) (K := logBlockInterval)
    (lower := expLogBlockLowerWitness) (upper := expLogBlockUpperWitness)
    (left := expLogBlockLowerInterval) (right := expLogBlockUpperInterval)
    (by norm_num [Interval.Contains, blockScale]) (by norm_num)
    expLogBlockLowerValid expLogBlockUpperValid
  · norm_num [expLogBlockLowerInterval]
  · norm_num [expLogBlockUpperInterval]

def sqrtCutoffInterval : Interval := ⟨(4466719825554318332994249441 / 1000000000000000000000000), (2233359912777159166497124721 / 500000000000000000000000)⟩

theorem sqrt_cutoff_bounds : sqrtCutoffInterval.Contains (Real.sqrt 19951586) := by
  apply Interval.sqrt_sound (I := ⟨19951586, 19951586⟩)
  · norm_num [Interval.SqrtValid, sqrtCutoffInterval]
  · norm_num [Interval.Contains]

end Sarkozy.Certificates
