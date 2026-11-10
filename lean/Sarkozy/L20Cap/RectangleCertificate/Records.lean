module

public import Sarkozy.L20Cap.RectangleCertificate.Checks
public import Sarkozy.L20Cap.RectangleCertificate.FiniteCounts


@[expose] public section

namespace Sarkozy.L20Cap.RectangleCertificate

open Finset Sarkozy.Extraction Sarkozy.ExtractionK

theorem record0_valid : record0.Valid Ex8 datum0 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record0_small : smallCounts datum0 record0 := by
  unfold smallCounts
  decide +kernel

theorem record0_exponent :
    recordExp G6 (Ex8 \ (datum0.1 ∪ datum0.2)) (witV record0.w)
      (witW record0.w) record0.ordX record0.ordZ +
      2 * twoCycleCount (witnessIdx datum0.1 record0.w) = 6 := by
  change finiteExponent datum0 record0 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum0.1 record0.w) = _
  have hw : witnessIdx (k := 2) datum0.1 record0.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record1_valid : record1.Valid Ex8 datum1 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record1_small : smallCounts datum1 record1 := by
  unfold smallCounts
  decide +kernel

theorem record1_exponent :
    recordExp G6 (Ex8 \ (datum1.1 ∪ datum1.2)) (witV record1.w)
      (witW record1.w) record1.ordX record1.ordZ +
      2 * twoCycleCount (witnessIdx datum1.1 record1.w) = 3 := by
  change finiteExponent datum1 record1 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum1.1 record1.w) = _
  have hw : witnessIdx (k := 2) datum1.1 record1.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record2_valid : record2.Valid Ex8 datum2 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record2_small : smallCounts datum2 record2 := by
  unfold smallCounts
  decide +kernel

theorem record2_exponent :
    recordExp G6 (Ex8 \ (datum2.1 ∪ datum2.2)) (witV record2.w)
      (witW record2.w) record2.ordX record2.ordZ +
      2 * twoCycleCount (witnessIdx datum2.1 record2.w) = 1 := by
  change finiteExponent datum2 record2 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum2.1 record2.w) = _
  have hw : witnessIdx (k := 2) datum2.1 record2.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record3_valid : record3.Valid Ex8 datum3 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record3_small : smallCounts datum3 record3 := by
  unfold smallCounts
  decide +kernel

theorem record3_exponent :
    recordExp G6 (Ex8 \ (datum3.1 ∪ datum3.2)) (witV record3.w)
      (witW record3.w) record3.ordX record3.ordZ +
      2 * twoCycleCount (witnessIdx datum3.1 record3.w) = 8 := by
  change finiteExponent datum3 record3 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum3.1 record3.w) = _
  have hw : witnessIdx (k := 2) datum3.1 record3.w =
      F3Kernel.Components.rectangle 2 0 := by decide +kernel
  rw [hw, two_pattern_count 0 (by decide)]
  decide +kernel

theorem record4_valid : record4.Valid Ex8 datum4 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record4_small : smallCounts datum4 record4 := by
  unfold smallCounts
  decide +kernel

theorem record4_exponent :
    recordExp G6 (Ex8 \ (datum4.1 ∪ datum4.2)) (witV record4.w)
      (witW record4.w) record4.ordX record4.ordZ +
      2 * twoCycleCount (witnessIdx datum4.1 record4.w) = 8 := by
  change finiteExponent datum4 record4 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum4.1 record4.w) = _
  have hw : witnessIdx (k := 2) datum4.1 record4.w =
      F3Kernel.Components.rectangle 2 4 := by decide +kernel
  rw [hw, two_pattern_count 4 (by decide)]
  decide +kernel

theorem record5_valid : record5.Valid Ex8 datum5 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record5_small : smallCounts datum5 record5 := by
  unfold smallCounts
  decide +kernel

theorem record5_exponent :
    recordExp G6 (Ex8 \ (datum5.1 ∪ datum5.2)) (witV record5.w)
      (witW record5.w) record5.ordX record5.ordZ +
      2 * twoCycleCount (witnessIdx datum5.1 record5.w) = 8 := by
  change finiteExponent datum5 record5 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum5.1 record5.w) = _
  have hw : witnessIdx (k := 2) datum5.1 record5.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record6_valid : record6.Valid Ex8 datum6 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record6_small : smallCounts datum6 record6 := by
  unfold smallCounts
  decide +kernel

theorem record6_exponent :
    recordExp G6 (Ex8 \ (datum6.1 ∪ datum6.2)) (witV record6.w)
      (witW record6.w) record6.ordX record6.ordZ +
      2 * twoCycleCount (witnessIdx datum6.1 record6.w) = 10 := by
  change finiteExponent datum6 record6 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum6.1 record6.w) = _
  have hw : witnessIdx (k := 2) datum6.1 record6.w =
      F3Kernel.Components.rectangle 2 6 := by decide +kernel
  rw [hw, two_pattern_count 6 (by decide)]
  decide +kernel

theorem record7_valid : record7.Valid Ex8 datum7 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record7_small : smallCounts datum7 record7 := by
  unfold smallCounts
  decide +kernel

theorem record7_exponent :
    recordExp G6 (Ex8 \ (datum7.1 ∪ datum7.2)) (witV record7.w)
      (witW record7.w) record7.ordX record7.ordZ +
      2 * twoCycleCount (witnessIdx datum7.1 record7.w) = 6 := by
  change finiteExponent datum7 record7 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum7.1 record7.w) = _
  have hw : witnessIdx (k := 2) datum7.1 record7.w =
      F3Kernel.Components.rectangle 2 0 := by decide +kernel
  rw [hw, two_pattern_count 0 (by decide)]
  decide +kernel

theorem record8_valid : record8.Valid Ex8 datum8 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record8_small : smallCounts datum8 record8 := by
  unfold smallCounts
  decide +kernel

theorem record8_exponent :
    recordExp G6 (Ex8 \ (datum8.1 ∪ datum8.2)) (witV record8.w)
      (witW record8.w) record8.ordX record8.ordZ +
      2 * twoCycleCount (witnessIdx datum8.1 record8.w) = 6 := by
  change finiteExponent datum8 record8 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum8.1 record8.w) = _
  have hw : witnessIdx (k := 2) datum8.1 record8.w =
      F3Kernel.Components.rectangle 2 4 := by decide +kernel
  rw [hw, two_pattern_count 4 (by decide)]
  decide +kernel

theorem record9_valid : record9.Valid Ex8 datum9 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record9_small : smallCounts datum9 record9 := by
  unfold smallCounts
  decide +kernel

theorem record9_exponent :
    recordExp G6 (Ex8 \ (datum9.1 ∪ datum9.2)) (witV record9.w)
      (witW record9.w) record9.ordX record9.ordZ +
      2 * twoCycleCount (witnessIdx datum9.1 record9.w) = 6 := by
  change finiteExponent datum9 record9 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum9.1 record9.w) = _
  have hw : witnessIdx (k := 2) datum9.1 record9.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record10_valid : record10.Valid Ex8 datum10 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record10_small : smallCounts datum10 record10 := by
  unfold smallCounts
  decide +kernel

theorem record10_exponent :
    recordExp G6 (Ex8 \ (datum10.1 ∪ datum10.2)) (witV record10.w)
      (witW record10.w) record10.ordX record10.ordZ +
      2 * twoCycleCount (witnessIdx datum10.1 record10.w) = 8 := by
  change finiteExponent datum10 record10 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum10.1 record10.w) = _
  have hw : witnessIdx (k := 2) datum10.1 record10.w =
      F3Kernel.Components.rectangle 2 6 := by decide +kernel
  rw [hw, two_pattern_count 6 (by decide)]
  decide +kernel

theorem record11_valid : record11.Valid Ex8 datum11 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record11_small : smallCounts datum11 record11 := by
  unfold smallCounts
  decide +kernel

theorem record11_exponent :
    recordExp G6 (Ex8 \ (datum11.1 ∪ datum11.2)) (witV record11.w)
      (witW record11.w) record11.ordX record11.ordZ +
      2 * twoCycleCount (witnessIdx datum11.1 record11.w) = 5 := by
  change finiteExponent datum11 record11 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum11.1 record11.w) = _
  have hw : witnessIdx (k := 2) datum11.1 record11.w =
      F3Kernel.Components.rectangle 2 0 := by decide +kernel
  rw [hw, two_pattern_count 0 (by decide)]
  decide +kernel

theorem record12_valid : record12.Valid Ex8 datum12 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record12_small : smallCounts datum12 record12 := by
  unfold smallCounts
  decide +kernel

theorem record12_exponent :
    recordExp G6 (Ex8 \ (datum12.1 ∪ datum12.2)) (witV record12.w)
      (witW record12.w) record12.ordX record12.ordZ +
      2 * twoCycleCount (witnessIdx datum12.1 record12.w) = 5 := by
  change finiteExponent datum12 record12 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum12.1 record12.w) = _
  have hw : witnessIdx (k := 2) datum12.1 record12.w =
      F3Kernel.Components.rectangle 2 4 := by decide +kernel
  rw [hw, two_pattern_count 4 (by decide)]
  decide +kernel

theorem record13_valid : record13.Valid Ex8 datum13 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record13_small : smallCounts datum13 record13 := by
  unfold smallCounts
  decide +kernel

theorem record13_exponent :
    recordExp G6 (Ex8 \ (datum13.1 ∪ datum13.2)) (witV record13.w)
      (witW record13.w) record13.ordX record13.ordZ +
      2 * twoCycleCount (witnessIdx datum13.1 record13.w) = 5 := by
  change finiteExponent datum13 record13 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum13.1 record13.w) = _
  have hw : witnessIdx (k := 2) datum13.1 record13.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record14_valid : record14.Valid Ex8 datum14 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record14_small : smallCounts datum14 record14 := by
  unfold smallCounts
  decide +kernel

theorem record14_exponent :
    recordExp G6 (Ex8 \ (datum14.1 ∪ datum14.2)) (witV record14.w)
      (witW record14.w) record14.ordX record14.ordZ +
      2 * twoCycleCount (witnessIdx datum14.1 record14.w) = 7 := by
  change finiteExponent datum14 record14 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum14.1 record14.w) = _
  have hw : witnessIdx (k := 2) datum14.1 record14.w =
      F3Kernel.Components.rectangle 2 6 := by decide +kernel
  rw [hw, two_pattern_count 6 (by decide)]
  decide +kernel

theorem record15_valid : record15.Valid Ex8 datum15 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record15_small : smallCounts datum15 record15 := by
  unfold smallCounts
  decide +kernel

theorem record15_exponent :
    recordExp G6 (Ex8 \ (datum15.1 ∪ datum15.2)) (witV record15.w)
      (witW record15.w) record15.ordX record15.ordZ +
      2 * twoCycleCount (witnessIdx datum15.1 record15.w) = 3 := by
  change finiteExponent datum15 record15 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum15.1 record15.w) = _
  have hw : witnessIdx (k := 2) datum15.1 record15.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record16_valid : record16.Valid Ex8 datum16 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record16_small : smallCounts datum16 record16 := by
  unfold smallCounts
  decide +kernel

theorem record16_exponent :
    recordExp G6 (Ex8 \ (datum16.1 ∪ datum16.2)) (witV record16.w)
      (witW record16.w) record16.ordX record16.ordZ +
      2 * twoCycleCount (witnessIdx datum16.1 record16.w) = 1 := by
  change finiteExponent datum16 record16 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum16.1 record16.w) = _
  have hw : witnessIdx (k := 2) datum16.1 record16.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record17_valid : record17.Valid Ex8 datum17 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record17_small : smallCounts datum17 record17 := by
  unfold smallCounts
  decide +kernel

theorem record17_exponent :
    recordExp G6 (Ex8 \ (datum17.1 ∪ datum17.2)) (witV record17.w)
      (witW record17.w) record17.ordX record17.ordZ +
      2 * twoCycleCount (witnessIdx datum17.1 record17.w) = 8 := by
  change finiteExponent datum17 record17 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum17.1 record17.w) = _
  have hw : witnessIdx (k := 2) datum17.1 record17.w =
      F3Kernel.Components.rectangle 2 0 := by decide +kernel
  rw [hw, two_pattern_count 0 (by decide)]
  decide +kernel

theorem record18_valid : record18.Valid Ex8 datum18 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record18_small : smallCounts datum18 record18 := by
  unfold smallCounts
  decide +kernel

theorem record18_exponent :
    recordExp G6 (Ex8 \ (datum18.1 ∪ datum18.2)) (witV record18.w)
      (witW record18.w) record18.ordX record18.ordZ +
      2 * twoCycleCount (witnessIdx datum18.1 record18.w) = 8 := by
  change finiteExponent datum18 record18 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum18.1 record18.w) = _
  have hw : witnessIdx (k := 2) datum18.1 record18.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record19_valid : record19.Valid Ex8 datum19 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record19_small : smallCounts datum19 record19 := by
  unfold smallCounts
  decide +kernel

theorem record19_exponent :
    recordExp G6 (Ex8 \ (datum19.1 ∪ datum19.2)) (witV record19.w)
      (witW record19.w) record19.ordX record19.ordZ +
      2 * twoCycleCount (witnessIdx datum19.1 record19.w) = 4 := by
  change finiteExponent datum19 record19 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum19.1 record19.w) = _
  have hw : witnessIdx (k := 2) datum19.1 record19.w =
      F3Kernel.Components.rectangle 2 0 := by decide +kernel
  rw [hw, two_pattern_count 0 (by decide)]
  decide +kernel

theorem record20_valid : record20.Valid Ex8 datum20 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record20_small : smallCounts datum20 record20 := by
  unfold smallCounts
  decide +kernel

theorem record20_exponent :
    recordExp G6 (Ex8 \ (datum20.1 ∪ datum20.2)) (witV record20.w)
      (witW record20.w) record20.ordX record20.ordZ +
      2 * twoCycleCount (witnessIdx datum20.1 record20.w) = 4 := by
  change finiteExponent datum20 record20 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum20.1 record20.w) = _
  have hw : witnessIdx (k := 2) datum20.1 record20.w =
      F3Kernel.Components.rectangle 2 4 := by decide +kernel
  rw [hw, two_pattern_count 4 (by decide)]
  decide +kernel

theorem record21_valid : record21.Valid Ex8 datum21 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record21_small : smallCounts datum21 record21 := by
  unfold smallCounts
  decide +kernel

theorem record21_exponent :
    recordExp G6 (Ex8 \ (datum21.1 ∪ datum21.2)) (witV record21.w)
      (witW record21.w) record21.ordX record21.ordZ +
      2 * twoCycleCount (witnessIdx datum21.1 record21.w) = 4 := by
  change finiteExponent datum21 record21 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum21.1 record21.w) = _
  have hw : witnessIdx (k := 2) datum21.1 record21.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record22_valid : record22.Valid Ex8 datum22 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record22_small : smallCounts datum22 record22 := by
  unfold smallCounts
  decide +kernel

theorem record22_exponent :
    recordExp G6 (Ex8 \ (datum22.1 ∪ datum22.2)) (witV record22.w)
      (witW record22.w) record22.ordX record22.ordZ +
      2 * twoCycleCount (witnessIdx datum22.1 record22.w) = 6 := by
  change finiteExponent datum22 record22 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum22.1 record22.w) = _
  have hw : witnessIdx (k := 2) datum22.1 record22.w =
      F3Kernel.Components.rectangle 2 6 := by decide +kernel
  rw [hw, two_pattern_count 6 (by decide)]
  decide +kernel

theorem record23_valid : record23.Valid Ex8 datum23 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record23_small : smallCounts datum23 record23 := by
  unfold smallCounts
  decide +kernel

theorem record23_exponent :
    recordExp G6 (Ex8 \ (datum23.1 ∪ datum23.2)) (witV record23.w)
      (witW record23.w) record23.ordX record23.ordZ +
      2 * twoCycleCount (witnessIdx datum23.1 record23.w) = 3 := by
  change finiteExponent datum23 record23 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum23.1 record23.w) = _
  have hw : witnessIdx (k := 2) datum23.1 record23.w =
      F3Kernel.Components.rectangle 2 0 := by decide +kernel
  rw [hw, two_pattern_count 0 (by decide)]
  decide +kernel

theorem record24_valid : record24.Valid Ex8 datum24 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record24_small : smallCounts datum24 record24 := by
  unfold smallCounts
  decide +kernel

theorem record24_exponent :
    recordExp G6 (Ex8 \ (datum24.1 ∪ datum24.2)) (witV record24.w)
      (witW record24.w) record24.ordX record24.ordZ +
      2 * twoCycleCount (witnessIdx datum24.1 record24.w) = 3 := by
  change finiteExponent datum24 record24 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum24.1 record24.w) = _
  have hw : witnessIdx (k := 2) datum24.1 record24.w =
      F3Kernel.Components.rectangle 2 4 := by decide +kernel
  rw [hw, two_pattern_count 4 (by decide)]
  decide +kernel

theorem record25_valid : record25.Valid Ex8 datum25 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record25_small : smallCounts datum25 record25 := by
  unfold smallCounts
  decide +kernel

theorem record25_exponent :
    recordExp G6 (Ex8 \ (datum25.1 ∪ datum25.2)) (witV record25.w)
      (witW record25.w) record25.ordX record25.ordZ +
      2 * twoCycleCount (witnessIdx datum25.1 record25.w) = 3 := by
  change finiteExponent datum25 record25 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum25.1 record25.w) = _
  have hw : witnessIdx (k := 2) datum25.1 record25.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record26_valid : record26.Valid Ex8 datum26 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record26_small : smallCounts datum26 record26 := by
  unfold smallCounts
  decide +kernel

theorem record26_exponent :
    recordExp G6 (Ex8 \ (datum26.1 ∪ datum26.2)) (witV record26.w)
      (witW record26.w) record26.ordX record26.ordZ +
      2 * twoCycleCount (witnessIdx datum26.1 record26.w) = 5 := by
  change finiteExponent datum26 record26 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum26.1 record26.w) = _
  have hw : witnessIdx (k := 2) datum26.1 record26.w =
      F3Kernel.Components.rectangle 2 6 := by decide +kernel
  rw [hw, two_pattern_count 6 (by decide)]
  decide +kernel

theorem record27_valid : record27.Valid Ex8 datum27 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record27_small : smallCounts datum27 record27 := by
  unfold smallCounts
  decide +kernel

theorem record27_exponent :
    recordExp G6 (Ex8 \ (datum27.1 ∪ datum27.2)) (witV record27.w)
      (witW record27.w) record27.ordX record27.ordZ +
      2 * twoCycleCount (witnessIdx datum27.1 record27.w) = 0 := by
  change finiteExponent datum27 record27 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum27.1 record27.w) = _
  have hw : witnessIdx (k := 2) datum27.1 record27.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record28_valid : record28.Valid Ex8 datum28 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record28_small : smallCounts datum28 record28 := by
  unfold smallCounts
  decide +kernel

theorem record28_exponent :
    recordExp G6 (Ex8 \ (datum28.1 ∪ datum28.2)) (witV record28.w)
      (witW record28.w) record28.ordX record28.ordZ +
      2 * twoCycleCount (witnessIdx datum28.1 record28.w) = 6 := by
  change finiteExponent datum28 record28 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum28.1 record28.w) = _
  have hw : witnessIdx (k := 2) datum28.1 record28.w =
      F3Kernel.Components.rectangle 2 0 := by decide +kernel
  rw [hw, two_pattern_count 0 (by decide)]
  decide +kernel

theorem record29_valid : record29.Valid Ex8 datum29 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record29_small : smallCounts datum29 record29 := by
  unfold smallCounts
  decide +kernel

theorem record29_exponent :
    recordExp G6 (Ex8 \ (datum29.1 ∪ datum29.2)) (witV record29.w)
      (witW record29.w) record29.ordX record29.ordZ +
      2 * twoCycleCount (witnessIdx datum29.1 record29.w) = 6 := by
  change finiteExponent datum29 record29 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum29.1 record29.w) = _
  have hw : witnessIdx (k := 2) datum29.1 record29.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record30_valid : record30.Valid Ex8 datum30 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record30_small : smallCounts datum30 record30 := by
  unfold smallCounts
  decide +kernel

theorem record30_exponent :
    recordExp G6 (Ex8 \ (datum30.1 ∪ datum30.2)) (witV record30.w)
      (witW record30.w) record30.ordX record30.ordZ +
      2 * twoCycleCount (witnessIdx datum30.1 record30.w) = 4 := by
  change finiteExponent datum30 record30 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum30.1 record30.w) = _
  have hw : witnessIdx (k := 2) datum30.1 record30.w =
      F3Kernel.Components.rectangle 2 0 := by decide +kernel
  rw [hw, two_pattern_count 0 (by decide)]
  decide +kernel

theorem record31_valid : record31.Valid Ex8 datum31 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record31_small : smallCounts datum31 record31 := by
  unfold smallCounts
  decide +kernel

theorem record31_exponent :
    recordExp G6 (Ex8 \ (datum31.1 ∪ datum31.2)) (witV record31.w)
      (witW record31.w) record31.ordX record31.ordZ +
      2 * twoCycleCount (witnessIdx datum31.1 record31.w) = 4 := by
  change finiteExponent datum31 record31 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum31.1 record31.w) = _
  have hw : witnessIdx (k := 2) datum31.1 record31.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record32_valid : record32.Valid Ex8 datum32 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record32_small : smallCounts datum32 record32 := by
  unfold smallCounts
  decide +kernel

theorem record32_exponent :
    recordExp G6 (Ex8 \ (datum32.1 ∪ datum32.2)) (witV record32.w)
      (witW record32.w) record32.ordX record32.ordZ +
      2 * twoCycleCount (witnessIdx datum32.1 record32.w) = 0 := by
  change finiteExponent datum32 record32 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum32.1 record32.w) = _
  have hw : witnessIdx (k := 2) datum32.1 record32.w =
      F3Kernel.Components.rectangle 2 0 := by decide +kernel
  rw [hw, two_pattern_count 0 (by decide)]
  decide +kernel

theorem record33_valid : record33.Valid Ex8 datum33 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record33_small : smallCounts datum33 record33 := by
  unfold smallCounts
  decide +kernel

theorem record33_exponent :
    recordExp G6 (Ex8 \ (datum33.1 ∪ datum33.2)) (witV record33.w)
      (witW record33.w) record33.ordX record33.ordZ +
      2 * twoCycleCount (witnessIdx datum33.1 record33.w) = 0 := by
  change finiteExponent datum33 record33 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum33.1 record33.w) = _
  have hw : witnessIdx (k := 2) datum33.1 record33.w =
      F3Kernel.Components.rectangle 2 4 := by decide +kernel
  rw [hw, two_pattern_count 4 (by decide)]
  decide +kernel

theorem record34_valid : record34.Valid Ex8 datum34 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record34_small : smallCounts datum34 record34 := by
  unfold smallCounts
  decide +kernel

theorem record34_exponent :
    recordExp G6 (Ex8 \ (datum34.1 ∪ datum34.2)) (witV record34.w)
      (witW record34.w) record34.ordX record34.ordZ +
      2 * twoCycleCount (witnessIdx datum34.1 record34.w) = 0 := by
  change finiteExponent datum34 record34 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum34.1 record34.w) = _
  have hw : witnessIdx (k := 2) datum34.1 record34.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record35_valid : record35.Valid Ex8 datum35 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record35_small : smallCounts datum35 record35 := by
  unfold smallCounts
  decide +kernel

theorem record35_exponent :
    recordExp G6 (Ex8 \ (datum35.1 ∪ datum35.2)) (witV record35.w)
      (witW record35.w) record35.ordX record35.ordZ +
      2 * twoCycleCount (witnessIdx datum35.1 record35.w) = 2 := by
  change finiteExponent datum35 record35 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum35.1 record35.w) = _
  have hw : witnessIdx (k := 2) datum35.1 record35.w =
      F3Kernel.Components.rectangle 2 6 := by decide +kernel
  rw [hw, two_pattern_count 6 (by decide)]
  decide +kernel

theorem record36_valid : record36.Valid Ex8 datum36 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record36_small : smallCounts datum36 record36 := by
  unfold smallCounts
  decide +kernel

theorem record36_exponent :
    recordExp G6 (Ex8 \ (datum36.1 ∪ datum36.2)) (witV record36.w)
      (witW record36.w) record36.ordX record36.ordZ +
      2 * twoCycleCount (witnessIdx datum36.1 record36.w) = 5 := by
  change finiteExponent datum36 record36 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum36.1 record36.w) = _
  have hw : witnessIdx (k := 2) datum36.1 record36.w =
      F3Kernel.Components.rectangle 2 0 := by decide +kernel
  rw [hw, two_pattern_count 0 (by decide)]
  decide +kernel

theorem record37_valid : record37.Valid Ex8 datum37 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record37_small : smallCounts datum37 record37 := by
  unfold smallCounts
  decide +kernel

theorem record37_exponent :
    recordExp G6 (Ex8 \ (datum37.1 ∪ datum37.2)) (witV record37.w)
      (witW record37.w) record37.ordX record37.ordZ +
      2 * twoCycleCount (witnessIdx datum37.1 record37.w) = 5 := by
  change finiteExponent datum37 record37 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum37.1 record37.w) = _
  have hw : witnessIdx (k := 2) datum37.1 record37.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record38_valid : record38.Valid Ex8 datum38 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record38_small : smallCounts datum38 record38 := by
  unfold smallCounts
  decide +kernel

theorem record38_exponent :
    recordExp G6 (Ex8 \ (datum38.1 ∪ datum38.2)) (witV record38.w)
      (witW record38.w) record38.ordX record38.ordZ +
      2 * twoCycleCount (witnessIdx datum38.1 record38.w) = 3 := by
  change finiteExponent datum38 record38 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum38.1 record38.w) = _
  have hw : witnessIdx (k := 2) datum38.1 record38.w =
      F3Kernel.Components.rectangle 2 0 := by decide +kernel
  rw [hw, two_pattern_count 0 (by decide)]
  decide +kernel

theorem record39_valid : record39.Valid Ex8 datum39 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record39_small : smallCounts datum39 record39 := by
  unfold smallCounts
  decide +kernel

theorem record39_exponent :
    recordExp G6 (Ex8 \ (datum39.1 ∪ datum39.2)) (witV record39.w)
      (witW record39.w) record39.ordX record39.ordZ +
      2 * twoCycleCount (witnessIdx datum39.1 record39.w) = 3 := by
  change finiteExponent datum39 record39 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum39.1 record39.w) = _
  have hw : witnessIdx (k := 2) datum39.1 record39.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem record40_valid : record40.Valid Ex8 datum40 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record40_small : smallCounts datum40 record40 := by
  unfold smallCounts
  decide +kernel

theorem record40_exponent :
    recordExp G6 (Ex8 \ (datum40.1 ∪ datum40.2)) (witV record40.w)
      (witW record40.w) record40.ordX record40.ordZ +
      2 * twoCycleCount (witnessIdx datum40.1 record40.w) = 0 := by
  change finiteExponent datum40 record40 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum40.1 record40.w) = _
  have hw : witnessIdx (k := 2) datum40.1 record40.w =
      F3Kernel.Components.rectangle 2 0 := by decide +kernel
  rw [hw, two_pattern_count 0 (by decide)]
  decide +kernel

theorem record41_valid : record41.Valid Ex8 datum41 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem record41_small : smallCounts datum41 record41 := by
  unfold smallCounts
  decide +kernel

theorem record41_exponent :
    recordExp G6 (Ex8 \ (datum41.1 ∪ datum41.2)) (witV record41.w)
      (witW record41.w) record41.ordX record41.ordZ +
      2 * twoCycleCount (witnessIdx datum41.1 record41.w) = 0 := by
  change finiteExponent datum41 record41 +
    2 * twoCycleCount (k := 2) (witnessIdx (k := 2) datum41.1 record41.w) = _
  have hw : witnessIdx (k := 2) datum41.1 record41.w =
      F3Kernel.Components.rectangle 2 2 := by decide +kernel
  rw [hw, two_pattern_count 2 (by decide)]
  decide +kernel

theorem records_valid (i : Fin 42) : (record i).Valid Ex8 (datum i) := by
  fin_cases i
  · exact record0_valid
  · exact record1_valid
  · exact record2_valid
  · exact record3_valid
  · exact record4_valid
  · exact record5_valid
  · exact record6_valid
  · exact record7_valid
  · exact record8_valid
  · exact record9_valid
  · exact record10_valid
  · exact record11_valid
  · exact record12_valid
  · exact record13_valid
  · exact record14_valid
  · exact record15_valid
  · exact record16_valid
  · exact record17_valid
  · exact record18_valid
  · exact record19_valid
  · exact record20_valid
  · exact record21_valid
  · exact record22_valid
  · exact record23_valid
  · exact record24_valid
  · exact record25_valid
  · exact record26_valid
  · exact record27_valid
  · exact record28_valid
  · exact record29_valid
  · exact record30_valid
  · exact record31_valid
  · exact record32_valid
  · exact record33_valid
  · exact record34_valid
  · exact record35_valid
  · exact record36_valid
  · exact record37_valid
  · exact record38_valid
  · exact record39_valid
  · exact record40_valid
  · exact record41_valid

theorem records_small (i : Fin 42) : smallCounts (datum i) (record i) := by
  fin_cases i
  · exact record0_small
  · exact record1_small
  · exact record2_small
  · exact record3_small
  · exact record4_small
  · exact record5_small
  · exact record6_small
  · exact record7_small
  · exact record8_small
  · exact record9_small
  · exact record10_small
  · exact record11_small
  · exact record12_small
  · exact record13_small
  · exact record14_small
  · exact record15_small
  · exact record16_small
  · exact record17_small
  · exact record18_small
  · exact record19_small
  · exact record20_small
  · exact record21_small
  · exact record22_small
  · exact record23_small
  · exact record24_small
  · exact record25_small
  · exact record26_small
  · exact record27_small
  · exact record28_small
  · exact record29_small
  · exact record30_small
  · exact record31_small
  · exact record32_small
  · exact record33_small
  · exact record34_small
  · exact record35_small
  · exact record36_small
  · exact record37_small
  · exact record38_small
  · exact record39_small
  · exact record40_small
  · exact record41_small

theorem records_exponent (i : Fin 42) : recordExp G6 (Ex8 \ ((datum i).1 ∪ (datum i).2)) (witV (record i).w)
      (witW (record i).w) (record i).ordX (record i).ordZ +
      2 * twoCycleCount (witnessIdx (datum i).1 (record i).w) = exponent i := by
  fin_cases i
  · exact record0_exponent
  · exact record1_exponent
  · exact record2_exponent
  · exact record3_exponent
  · exact record4_exponent
  · exact record5_exponent
  · exact record6_exponent
  · exact record7_exponent
  · exact record8_exponent
  · exact record9_exponent
  · exact record10_exponent
  · exact record11_exponent
  · exact record12_exponent
  · exact record13_exponent
  · exact record14_exponent
  · exact record15_exponent
  · exact record16_exponent
  · exact record17_exponent
  · exact record18_exponent
  · exact record19_exponent
  · exact record20_exponent
  · exact record21_exponent
  · exact record22_exponent
  · exact record23_exponent
  · exact record24_exponent
  · exact record25_exponent
  · exact record26_exponent
  · exact record27_exponent
  · exact record28_exponent
  · exact record29_exponent
  · exact record30_exponent
  · exact record31_exponent
  · exact record32_exponent
  · exact record33_exponent
  · exact record34_exponent
  · exact record35_exponent
  · exact record36_exponent
  · exact record37_exponent
  · exact record38_exponent
  · exact record39_exponent
  · exact record40_exponent
  · exact record41_exponent

theorem records_size : ∀ i : Fin 42, (record i).k = 2 := by decide +kernel

def rationalPrice (i : Fin 42) : ℚ :=
  if exponent i % 2 = 0 then 2 ^ (exponent i / 2)
  else (283 / 200) * 2 ^ (exponent i / 2)

theorem rationalPrice_nonneg : ∀ i, 0 ≤ rationalPrice i := by decide +kernel

theorem rationalPrice_sq : ∀ i, (2 : ℚ) ^ exponent i ≤ rationalPrice i ^ 2 := by
  decide +kernel

theorem rationalPrice_sum : ∑ i, rationalPrice i = (6998 / 25 : ℚ) := by
  decide +kernel

end Sarkozy.L20Cap.RectangleCertificate
