module

public import Sarkozy.BlockSpecPaper.AllpData.Allp00
public import Sarkozy.BlockSpecPaper.AllpData.Allp01
public import Sarkozy.BlockSpecPaper.AllpData.Allp02
public import Sarkozy.BlockSpecPaper.AllpData.Allp03
public import Sarkozy.BlockSpecPaper.AllpData.Allp04
public import Sarkozy.BlockSpecPaper.AllpData.Allp05
public import Sarkozy.BlockSpecPaper.AllpData.Allp06
public import Sarkozy.BlockSpecPaper.AllpData.Allp07
public import Sarkozy.BlockSpecPaper.AllpData.Allp08
public import Sarkozy.BlockSpecPaper.AllpData.Allp09
public import Sarkozy.BlockSpecPaper.AllpData.Allp10
public import Sarkozy.BlockSpecPaper.AllpData.Allp11
public import Sarkozy.BlockSpecPaper.AllpData.Allp12
public import Sarkozy.BlockSpecPaper.AllpData.Allp13
public import Sarkozy.BlockSpecPaper.AllpData.Allp14
public import Sarkozy.BlockSpecPaper.AllpData.Allp15
public import Sarkozy.BlockSpecPaper.AllpData.Allp16
public import Sarkozy.BlockSpecPaper.AllpData.Allp17
public import Sarkozy.BlockSpecPaper.AllpData.Allp18
public import Sarkozy.BlockSpecPaper.AllpData.Allp19
public import Sarkozy.BlockSpecPaper.AllpData.Allp20
public import Sarkozy.BlockSpecPaper.AllpData.Allp21
public import Sarkozy.BlockSpecPaper.AllpData.Allp22
public import Sarkozy.BlockSpecPaper.AllpData.Allp23
public import Sarkozy.BlockSpecPaper.AllpData.Allp24
public import Sarkozy.BlockSpecPaper.AllpData.Allp25
public import Sarkozy.BlockSpecPaper.AllpData.Allp26
public import Sarkozy.BlockSpecPaper.AllpData.Allp27
public import Sarkozy.BlockSpecPaper.AllpData.Allp28
public import Sarkozy.BlockSpecPaper.AllpData.Allp29
public import Sarkozy.BlockSpecPaper.AllpData.Allp30
public import Sarkozy.BlockSpecPaper.AllpData.Allp31
public import Sarkozy.BlockSpecPaper.AllpData.Allp32



@[expose] public section

namespace Sarkozy.BlockSpecPaper.AllpData

open Sarkozy.MiddleRecords

/-- The ALLp completion records of the 33 middle pieces. -/
def allpRecord : Fin 33 → CompletionRecord :=
  ![allp00, allp01, allp02, allp03,
    allp04, allp05, allp06, allp07,
    allp08, allp09, allp10, allp11,
    allp12, allp13, allp14, allp15,
    allp16, allp17, allp18, allp19,
    allp20, allp21, allp22, allp23,
    allp24, allp25, allp26, allp27,
    allp28, allp29, allp30, allp31,
    allp32]

/-- `nonneg` on every ALLp piece. -/
theorem allpRecord_nonneg (i : Fin 33) :
    (allpRecord i).Nonneg := by
  fin_cases i
  · exact allp00_nonneg
  · exact allp01_nonneg
  · exact allp02_nonneg
  · exact allp03_nonneg
  · exact allp04_nonneg
  · exact allp05_nonneg
  · exact allp06_nonneg
  · exact allp07_nonneg
  · exact allp08_nonneg
  · exact allp09_nonneg
  · exact allp10_nonneg
  · exact allp11_nonneg
  · exact allp12_nonneg
  · exact allp13_nonneg
  · exact allp14_nonneg
  · exact allp15_nonneg
  · exact allp16_nonneg
  · exact allp17_nonneg
  · exact allp18_nonneg
  · exact allp19_nonneg
  · exact allp20_nonneg
  · exact allp21_nonneg
  · exact allp22_nonneg
  · exact allp23_nonneg
  · exact allp24_nonneg
  · exact allp25_nonneg
  · exact allp26_nonneg
  · exact allp27_nonneg
  · exact allp28_nonneg
  · exact allp29_nonneg
  · exact allp30_nonneg
  · exact allp31_nonneg
  · exact allp32_nonneg

/-- `completes` on every ALLp piece. -/
theorem allpRecord_completes (i : Fin 33) :
    (allpRecord i).Completes := by
  fin_cases i
  · exact allp00_completes
  · exact allp01_completes
  · exact allp02_completes
  · exact allp03_completes
  · exact allp04_completes
  · exact allp05_completes
  · exact allp06_completes
  · exact allp07_completes
  · exact allp08_completes
  · exact allp09_completes
  · exact allp10_completes
  · exact allp11_completes
  · exact allp12_completes
  · exact allp13_completes
  · exact allp14_completes
  · exact allp15_completes
  · exact allp16_completes
  · exact allp17_completes
  · exact allp18_completes
  · exact allp19_completes
  · exact allp20_completes
  · exact allp21_completes
  · exact allp22_completes
  · exact allp23_completes
  · exact allp24_completes
  · exact allp25_completes
  · exact allp26_completes
  · exact allp27_completes
  · exact allp28_completes
  · exact allp29_completes
  · exact allp30_completes
  · exact allp31_completes
  · exact allp32_completes

/-- `protects` on every ALLp piece. -/
theorem allpRecord_protects (i : Fin 33) :
    (allpRecord i).Protects := by
  fin_cases i
  · exact allp00_protects
  · exact allp01_protects
  · exact allp02_protects
  · exact allp03_protects
  · exact allp04_protects
  · exact allp05_protects
  · exact allp06_protects
  · exact allp07_protects
  · exact allp08_protects
  · exact allp09_protects
  · exact allp10_protects
  · exact allp11_protects
  · exact allp12_protects
  · exact allp13_protects
  · exact allp14_protects
  · exact allp15_protects
  · exact allp16_protects
  · exact allp17_protects
  · exact allp18_protects
  · exact allp19_protects
  · exact allp20_protects
  · exact allp21_protects
  · exact allp22_protects
  · exact allp23_protects
  · exact allp24_protects
  · exact allp25_protects
  · exact allp26_protects
  · exact allp27_protects
  · exact allp28_protects
  · exact allp29_protects
  · exact allp30_protects
  · exact allp31_protects
  · exact allp32_protects

/-- The ALLp records use the paper's 33 pieces (`def:record:exact-blocks`(a)). -/
theorem allpRecord_endpoints : ∀ i : Fin 33,
    (allpRecord i).start = PartV.pieceStart i ∧ (allpRecord i).stop = PartV.pieceStop i := by
  decide +kernel

end Sarkozy.BlockSpecPaper.AllpData
