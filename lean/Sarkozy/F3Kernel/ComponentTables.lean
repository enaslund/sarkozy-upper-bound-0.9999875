module

public import Sarkozy.F3Kernel.Components
public import Sarkozy.F3Kernel.ComponentTable.Four00
public import Sarkozy.F3Kernel.ComponentTable.Four01
public import Sarkozy.F3Kernel.ComponentTable.Four02
public import Sarkozy.F3Kernel.ComponentTable.Four03
public import Sarkozy.F3Kernel.ComponentTable.Four04
public import Sarkozy.F3Kernel.ComponentTable.Four05
public import Sarkozy.F3Kernel.ComponentTable.Four06
public import Sarkozy.F3Kernel.ComponentTable.Four07
public import Sarkozy.F3Kernel.ComponentTable.Four08
public import Sarkozy.F3Kernel.ComponentTable.Four09
public import Sarkozy.F3Kernel.ComponentTable.Four10
public import Sarkozy.F3Kernel.ComponentTable.Four11
public import Sarkozy.F3Kernel.ComponentTable.Four12
public import Sarkozy.F3Kernel.ComponentTable.Four13
public import Sarkozy.F3Kernel.ComponentTable.Four14
public import Sarkozy.F3Kernel.ComponentTable.Four15

/-!
# Kernel checks of the two-, three-, and four-witness component tables

The two graph certificates use identical component tables. Every nonzero entry is checked
against finite reachability, component cardinalities, and the number of distinct components
of size two. `Components.entry_sound` then supplies the paper's semantic conditions.
-/

@[expose] public section

namespace Sarkozy.F3Kernel.Components

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem LL20_table_two : ∀ p : Fin (2 ^ (2 * 2)), DiagZero 2 p → ValidEntry LL20.SCC2 2 p := by
  decide +kernel

theorem LL20_table_three : ∀ p : Fin (2 ^ (3 * 3)), DiagZero 3 p → ValidEntry LL20.SCC3 3 p := by
  decide +kernel

theorem LL20_table_four : ∀ p : Fin (2 ^ (4 * 4)), DiagZero 4 p → ValidEntry LL20.SCC4 4 p := by
  intro p hp
  have htop : p.val < 32768 := by
    have hd := hp (3 : Fin 4)
    rw [bit_eq_testBit, Nat.testBit_eq_decide_div_mod_eq] at hd
    norm_num at hd
    have := p.isLt
    norm_num at this
    omega
  have hall : ∀ b : Fin 16, ∀ j : Fin 2048,
      DiagZero 4 (2048 * b.val + j.val) →
        ValidEntry LL20.SCC4 4 (2048 * b.val + j.val) := by
    intro b
    fin_cases b
    all_goals first
      | exact Four00.checked
      | exact Four01.checked
      | exact Four02.checked
      | exact Four03.checked
      | exact Four04.checked
      | exact Four05.checked
      | exact Four06.checked
      | exact Four07.checked
      | exact Four08.checked
      | exact Four09.checked
      | exact Four10.checked
      | exact Four11.checked
      | exact Four12.checked
      | exact Four13.checked
      | exact Four14.checked
      | exact Four15.checked
  let b : Fin 16 := ⟨p.val / 2048, by omega⟩
  let j : Fin 2048 := ⟨p.val % 2048, Nat.mod_lt _ (by decide)⟩
  have he : 2048 * b.val + j.val = p.val := by dsimp [b, j]; omega
  simpa only [he] using hall b j (he.symm ▸ hp)

theorem tables_eq :
    LL22.SCC2 = LL20.SCC2 ∧ LL22.SCC3 = LL20.SCC3 ∧ LL22.SCC4 = LL20.SCC4 := by
  decide +kernel

end Sarkozy.F3Kernel.Components
