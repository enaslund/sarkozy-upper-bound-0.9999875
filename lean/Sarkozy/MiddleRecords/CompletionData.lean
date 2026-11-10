module

public import Sarkozy.MiddleRecords.CompletionData.Record00
public import Sarkozy.MiddleRecords.CompletionData.Record01
public import Sarkozy.MiddleRecords.CompletionData.Record02
public import Sarkozy.MiddleRecords.CompletionData.Record03
public import Sarkozy.MiddleRecords.CompletionData.Record04
public import Sarkozy.MiddleRecords.CompletionData.Record05
public import Sarkozy.MiddleRecords.CompletionData.Record06
public import Sarkozy.MiddleRecords.CompletionData.Record07
public import Sarkozy.MiddleRecords.CompletionData.Record08
public import Sarkozy.MiddleRecords.CompletionData.Record09
public import Sarkozy.MiddleRecords.CompletionData.Record10
public import Sarkozy.MiddleRecords.CompletionData.Record11
public import Sarkozy.MiddleRecords.CompletionData.Record12
public import Sarkozy.MiddleRecords.CompletionData.Record13
public import Sarkozy.MiddleRecords.CompletionData.Record14
public import Sarkozy.MiddleRecords.CompletionData.Record15
public import Sarkozy.MiddleRecords.CompletionData.Record16
public import Sarkozy.MiddleRecords.CompletionData.Record17
public import Sarkozy.MiddleRecords.CompletionData.Record18
public import Sarkozy.MiddleRecords.CompletionData.Record19
public import Sarkozy.MiddleRecords.CompletionData.Record20
public import Sarkozy.MiddleRecords.CompletionData.Record21
public import Sarkozy.MiddleRecords.CompletionData.Record22
public import Sarkozy.MiddleRecords.CompletionData.Record23
public import Sarkozy.MiddleRecords.CompletionData.Record24
public import Sarkozy.MiddleRecords.CompletionData.Record25
public import Sarkozy.MiddleRecords.CompletionData.Record26
public import Sarkozy.MiddleRecords.CompletionData.Record27
public import Sarkozy.MiddleRecords.CompletionData.Record28
public import Sarkozy.MiddleRecords.CompletionData.Record29
public import Sarkozy.MiddleRecords.CompletionData.Record30
public import Sarkozy.MiddleRecords.CompletionData.Record31
public import Sarkozy.MiddleRecords.CompletionData.Record32



@[expose] public section

namespace Sarkozy.MiddleRecords.CompletionData

def record : Fin 33 → CompletionRecord :=
  ![record00, record01, record02, record03,
    record04, record05, record06, record07,
    record08, record09, record10, record11,
    record12, record13, record14, record15,
    record16, record17, record18, record19,
    record20, record21, record22, record23,
    record24, record25, record26, record27,
    record28, record29, record30, record31,
    record32]

theorem record_nonneg (i : Fin 33) :
    (record i).Nonneg := by
  fin_cases i
  · exact record00_nonneg
  · exact record01_nonneg
  · exact record02_nonneg
  · exact record03_nonneg
  · exact record04_nonneg
  · exact record05_nonneg
  · exact record06_nonneg
  · exact record07_nonneg
  · exact record08_nonneg
  · exact record09_nonneg
  · exact record10_nonneg
  · exact record11_nonneg
  · exact record12_nonneg
  · exact record13_nonneg
  · exact record14_nonneg
  · exact record15_nonneg
  · exact record16_nonneg
  · exact record17_nonneg
  · exact record18_nonneg
  · exact record19_nonneg
  · exact record20_nonneg
  · exact record21_nonneg
  · exact record22_nonneg
  · exact record23_nonneg
  · exact record24_nonneg
  · exact record25_nonneg
  · exact record26_nonneg
  · exact record27_nonneg
  · exact record28_nonneg
  · exact record29_nonneg
  · exact record30_nonneg
  · exact record31_nonneg
  · exact record32_nonneg

theorem record_completes (i : Fin 33) :
    (record i).Completes := by
  fin_cases i
  · exact record00_completes
  · exact record01_completes
  · exact record02_completes
  · exact record03_completes
  · exact record04_completes
  · exact record05_completes
  · exact record06_completes
  · exact record07_completes
  · exact record08_completes
  · exact record09_completes
  · exact record10_completes
  · exact record11_completes
  · exact record12_completes
  · exact record13_completes
  · exact record14_completes
  · exact record15_completes
  · exact record16_completes
  · exact record17_completes
  · exact record18_completes
  · exact record19_completes
  · exact record20_completes
  · exact record21_completes
  · exact record22_completes
  · exact record23_completes
  · exact record24_completes
  · exact record25_completes
  · exact record26_completes
  · exact record27_completes
  · exact record28_completes
  · exact record29_completes
  · exact record30_completes
  · exact record31_completes
  · exact record32_completes

theorem record_protects (i : Fin 33) :
    (record i).Protects := by
  fin_cases i
  · exact record00_protects
  · exact record01_protects
  · exact record02_protects
  · exact record03_protects
  · exact record04_protects
  · exact record05_protects
  · exact record06_protects
  · exact record07_protects
  · exact record08_protects
  · exact record09_protects
  · exact record10_protects
  · exact record11_protects
  · exact record12_protects
  · exact record13_protects
  · exact record14_protects
  · exact record15_protects
  · exact record16_protects
  · exact record17_protects
  · exact record18_protects
  · exact record19_protects
  · exact record20_protects
  · exact record21_protects
  · exact record22_protects
  · exact record23_protects
  · exact record24_protects
  · exact record25_protects
  · exact record26_protects
  · exact record27_protects
  · exact record28_protects
  · exact record29_protects
  · exact record30_protects
  · exact record31_protects
  · exact record32_protects

theorem record_strong_matching (i : Fin 33) :
    2 * (record i).kE * (record i).wD ≤ (record i).vD := by
  fin_cases i
  · exact record00_strong_matching
  · exact record01_strong_matching
  · exact record02_strong_matching
  · exact record03_strong_matching
  · exact record04_strong_matching
  · exact record05_strong_matching
  · exact record06_strong_matching
  · exact record07_strong_matching
  · exact record08_strong_matching
  · exact record09_strong_matching
  · exact record10_strong_matching
  · exact record11_strong_matching
  · exact record12_strong_matching
  · exact record13_strong_matching
  · exact record14_strong_matching
  · exact record15_strong_matching
  · exact record16_strong_matching
  · exact record17_strong_matching
  · exact record18_strong_matching
  · exact record19_strong_matching
  · exact record20_strong_matching
  · exact record21_strong_matching
  · exact record22_strong_matching
  · exact record23_strong_matching
  · exact record24_strong_matching
  · exact record25_strong_matching
  · exact record26_strong_matching
  · exact record27_strong_matching
  · exact record28_strong_matching
  · exact record29_strong_matching
  · exact record30_strong_matching
  · exact record31_strong_matching
  · exact record32_strong_matching

theorem record_rounding (i : Fin 33) :
    (record i).vD - 2 * (record i).kD * (record i).wD < 1 / 10 ^ 9 := by
  fin_cases i
  · exact record00_rounding
  · exact record01_rounding
  · exact record02_rounding
  · exact record03_rounding
  · exact record04_rounding
  · exact record05_rounding
  · exact record06_rounding
  · exact record07_rounding
  · exact record08_rounding
  · exact record09_rounding
  · exact record10_rounding
  · exact record11_rounding
  · exact record12_rounding
  · exact record13_rounding
  · exact record14_rounding
  · exact record15_rounding
  · exact record16_rounding
  · exact record17_rounding
  · exact record18_rounding
  · exact record19_rounding
  · exact record20_rounding
  · exact record21_rounding
  · exact record22_rounding
  · exact record23_rounding
  · exact record24_rounding
  · exact record25_rounding
  · exact record26_rounding
  · exact record27_rounding
  · exact record28_rounding
  · exact record29_rounding
  · exact record30_rounding
  · exact record31_rounding
  · exact record32_rounding

theorem record_leading_rounding (i : Fin 33) :
    (record i).wD - (record i).d < 1 / 10 ^ 12 ∧
      (record i).vL - (record i).kL < 1 / 10 ^ 12 := by
  fin_cases i
  · exact record00_leading_rounding
  · exact record01_leading_rounding
  · exact record02_leading_rounding
  · exact record03_leading_rounding
  · exact record04_leading_rounding
  · exact record05_leading_rounding
  · exact record06_leading_rounding
  · exact record07_leading_rounding
  · exact record08_leading_rounding
  · exact record09_leading_rounding
  · exact record10_leading_rounding
  · exact record11_leading_rounding
  · exact record12_leading_rounding
  · exact record13_leading_rounding
  · exact record14_leading_rounding
  · exact record15_leading_rounding
  · exact record16_leading_rounding
  · exact record17_leading_rounding
  · exact record18_leading_rounding
  · exact record19_leading_rounding
  · exact record20_leading_rounding
  · exact record21_leading_rounding
  · exact record22_leading_rounding
  · exact record23_leading_rounding
  · exact record24_leading_rounding
  · exact record25_leading_rounding
  · exact record26_leading_rounding
  · exact record27_leading_rounding
  · exact record28_leading_rounding
  · exact record29_leading_rounding
  · exact record30_leading_rounding
  · exact record31_leading_rounding
  · exact record32_leading_rounding

theorem record_root_slack (i : Fin 33) :
    (57 : ℚ) / 10 ^ 6 < (record i).vD - (record i).d₁ * (record i).vL := by
  fin_cases i
  · exact record00_root_slack
  · exact record01_root_slack
  · exact record02_root_slack
  · exact record03_root_slack
  · exact record04_root_slack
  · exact record05_root_slack
  · exact record06_root_slack
  · exact record07_root_slack
  · exact record08_root_slack
  · exact record09_root_slack
  · exact record10_root_slack
  · exact record11_root_slack
  · exact record12_root_slack
  · exact record13_root_slack
  · exact record14_root_slack
  · exact record15_root_slack
  · exact record16_root_slack
  · exact record17_root_slack
  · exact record18_root_slack
  · exact record19_root_slack
  · exact record20_root_slack
  · exact record21_root_slack
  · exact record22_root_slack
  · exact record23_root_slack
  · exact record24_root_slack
  · exact record25_root_slack
  · exact record26_root_slack
  · exact record27_root_slack
  · exact record28_root_slack
  · exact record29_root_slack
  · exact record30_root_slack
  · exact record31_root_slack
  · exact record32_root_slack

theorem record_endpoints : ∀ i : Fin 33,
    (record i).start = PartV.pieceStart i ∧ (record i).stop = PartV.pieceStop i := by
  decide +kernel

end Sarkozy.MiddleRecords.CompletionData
