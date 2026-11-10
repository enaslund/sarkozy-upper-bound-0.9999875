module

public import Sarkozy.UpperRecords.CompletionData.Chunk00
public import Sarkozy.UpperRecords.CompletionData.Chunk01
public import Sarkozy.UpperRecords.CompletionData.Chunk02
public import Sarkozy.UpperRecords.CompletionData.Chunk03
public import Sarkozy.UpperRecords.CompletionData.Chunk04
public import Sarkozy.UpperRecords.CompletionData.Chunk05
public import Sarkozy.UpperRecords.CompletionData.Chunk06
public import Sarkozy.UpperRecords.CompletionData.Chunk07
public import Sarkozy.UpperRecords.CompletionData.Chunk08
public import Sarkozy.UpperRecords.CompletionData.Chunk09
public import Sarkozy.UpperRecords.CompletionData.Chunk10
public import Sarkozy.UpperRecords.CompletionData.Chunk11
public import Sarkozy.UpperRecords.CompletionData.Chunk12
public import Sarkozy.UpperRecords.CompletionData.Chunk13
public import Sarkozy.UpperRecords.CompletionData.Chunk14
public import Sarkozy.UpperRecords.CompletionData.Chunk15
public import Sarkozy.UpperRecords.CompletionData.Chunk16
public import Sarkozy.UpperRecords.CompletionData.Chunk17
public import Sarkozy.UpperRecords.CompletionData.Chunk18
public import Sarkozy.UpperRecords.CompletionData.Chunk19
public import Sarkozy.UpperRecords.CompletionData.Chunk20
public import Sarkozy.UpperRecords.CompletionData.Chunk21
public import Sarkozy.UpperRecords.CompletionData.Chunk22
public import Sarkozy.UpperRecords.CompletionData.Chunk23
public import Sarkozy.UpperRecords.CompletionData.Chunk24
public import Sarkozy.UpperRecords.CompletionData.Chunk25
public import Sarkozy.UpperRecords.CompletionData.Chunk26
public import Sarkozy.UpperRecords.CompletionData.Chunk27
public import Sarkozy.UpperRecords.CompletionData.Chunk28
public import Sarkozy.UpperRecords.CompletionData.Chunk29
public import Sarkozy.UpperRecords.CompletionData.Chunk30



@[expose] public section

namespace Sarkozy.UpperRecords.CompletionData

def group : Fin 31 → Fin 10 → CompletionRecord :=
  ![Chunk00.record, Chunk01.record, Chunk02.record, Chunk03.record,
    Chunk04.record, Chunk05.record, Chunk06.record, Chunk07.record,
    Chunk08.record, Chunk09.record, Chunk10.record, Chunk11.record,
    Chunk12.record, Chunk13.record, Chunk14.record, Chunk15.record,
    Chunk16.record, Chunk17.record, Chunk18.record, Chunk19.record,
    Chunk20.record, Chunk21.record, Chunk22.record, Chunk23.record,
    Chunk24.record, Chunk25.record, Chunk26.record, Chunk27.record,
    Chunk28.record, Chunk29.record, Chunk30.record]

theorem group_positive (i : Fin 31) (j : Fin 10) :
    (group i j).Positive := by
  fin_cases i
  · exact Chunk00.record_positive j
  · exact Chunk01.record_positive j
  · exact Chunk02.record_positive j
  · exact Chunk03.record_positive j
  · exact Chunk04.record_positive j
  · exact Chunk05.record_positive j
  · exact Chunk06.record_positive j
  · exact Chunk07.record_positive j
  · exact Chunk08.record_positive j
  · exact Chunk09.record_positive j
  · exact Chunk10.record_positive j
  · exact Chunk11.record_positive j
  · exact Chunk12.record_positive j
  · exact Chunk13.record_positive j
  · exact Chunk14.record_positive j
  · exact Chunk15.record_positive j
  · exact Chunk16.record_positive j
  · exact Chunk17.record_positive j
  · exact Chunk18.record_positive j
  · exact Chunk19.record_positive j
  · exact Chunk20.record_positive j
  · exact Chunk21.record_positive j
  · exact Chunk22.record_positive j
  · exact Chunk23.record_positive j
  · exact Chunk24.record_positive j
  · exact Chunk25.record_positive j
  · exact Chunk26.record_positive j
  · exact Chunk27.record_positive j
  · exact Chunk28.record_positive j
  · exact Chunk29.record_positive j
  · exact Chunk30.record_positive j

theorem group_completes (i : Fin 31) (j : Fin 10) :
    (group i j).Completes := by
  fin_cases i
  · exact Chunk00.record_completes j
  · exact Chunk01.record_completes j
  · exact Chunk02.record_completes j
  · exact Chunk03.record_completes j
  · exact Chunk04.record_completes j
  · exact Chunk05.record_completes j
  · exact Chunk06.record_completes j
  · exact Chunk07.record_completes j
  · exact Chunk08.record_completes j
  · exact Chunk09.record_completes j
  · exact Chunk10.record_completes j
  · exact Chunk11.record_completes j
  · exact Chunk12.record_completes j
  · exact Chunk13.record_completes j
  · exact Chunk14.record_completes j
  · exact Chunk15.record_completes j
  · exact Chunk16.record_completes j
  · exact Chunk17.record_completes j
  · exact Chunk18.record_completes j
  · exact Chunk19.record_completes j
  · exact Chunk20.record_completes j
  · exact Chunk21.record_completes j
  · exact Chunk22.record_completes j
  · exact Chunk23.record_completes j
  · exact Chunk24.record_completes j
  · exact Chunk25.record_completes j
  · exact Chunk26.record_completes j
  · exact Chunk27.record_completes j
  · exact Chunk28.record_completes j
  · exact Chunk29.record_completes j
  · exact Chunk30.record_completes j

theorem group_range (i : Fin 31) (j : Fin 10) :
    (group i j).RangeOK := by
  fin_cases i
  · exact Chunk00.record_range j
  · exact Chunk01.record_range j
  · exact Chunk02.record_range j
  · exact Chunk03.record_range j
  · exact Chunk04.record_range j
  · exact Chunk05.record_range j
  · exact Chunk06.record_range j
  · exact Chunk07.record_range j
  · exact Chunk08.record_range j
  · exact Chunk09.record_range j
  · exact Chunk10.record_range j
  · exact Chunk11.record_range j
  · exact Chunk12.record_range j
  · exact Chunk13.record_range j
  · exact Chunk14.record_range j
  · exact Chunk15.record_range j
  · exact Chunk16.record_range j
  · exact Chunk17.record_range j
  · exact Chunk18.record_range j
  · exact Chunk19.record_range j
  · exact Chunk20.record_range j
  · exact Chunk21.record_range j
  · exact Chunk22.record_range j
  · exact Chunk23.record_range j
  · exact Chunk24.record_range j
  · exact Chunk25.record_range j
  · exact Chunk26.record_range j
  · exact Chunk27.record_range j
  · exact Chunk28.record_range j
  · exact Chunk29.record_range j
  · exact Chunk30.record_range j

def record (i : Fin 310) : CompletionRecord :=
  group ⟨i.val / 10, by omega⟩ ⟨i.val % 10, Nat.mod_lt _ (by decide)⟩

theorem record_positive (i : Fin 310) : (record i).Positive :=
  group_positive _ _

theorem record_completes (i : Fin 310) : (record i).Completes :=
  group_completes _ _

theorem record_range (i : Fin 310) : (record i).RangeOK :=
  group_range _ _

/-- The data use exactly the 310 bands defined in the paper. -/
theorem record_endpoints : ∀ i : Fin 310,
    ((record i).start, (record i).stop) = PartV.upperBands.getD i.val (0, 0) := by
  decide +kernel

end Sarkozy.UpperRecords.CompletionData
