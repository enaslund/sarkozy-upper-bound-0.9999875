module

public import Sarkozy.UpperComparison.Ledger
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# The bands below `2^48` (`cert:upper-lower-bands`): the explicit checks

`paper/sections/26_upper_comparison.tex`, `cert:upper-lower-bands`, with the coefficients of
`prop:dense-comparison` (dense EL law at `2^47`) and `prop:le-mixture` (vector II at
`167·2^40`).

The certificate rests on JSON records (`lower_p47/*.json`) and their independent reviews; those
are outside Lean. What the paper displays explicitly is checked here, exactly, by the kernel:
* `lowerLedger`: the twelve state ledgers (symmetric, skew) of the table, as exact rationals;
* `ledger_states`: the changed records (`Ledger.upperFate`) have exactly the twelve states of
  the table, and `changed_by_state` gives their numbers (`LR 6, RL 2, DD 6, DS 4, SD 6, SS 4`,
  `LC 2, CL 2, DR 18, RD 18, SR 12, RS 12`), by enumeration of V1's records;
* `ledger_RL_binding`: the `RL` ledger is the number of changed `RL` records (two) times the
  dense EL coefficients `(s_EL, a_EL) = (3.291966120220, 2.401350027793)` at `2^47`
  (`cert:upper-lower-bands`(e), `prop:dense-comparison`);
* `ledger_LR_binding`: the `LR` ledger is the number of changed `LR` records (six) times the
  LE coefficients `(1.872914263008, 1.861100843756)` of vector II at `167·2^40`
  (`prop:le-mixture`, the LE mixture evaluated at `P₃` for these bands);
* `ledger_sym_ge_skew`: in every state the symmetric ledger is at least the skew one, as it must
  be for (F7), where `C^s = (ρ_old + ρ')/r ≥ C^a = ρ'/r`;
* `forest_ledgers_approx`: the forest ledgers `DD`, `DS`, `SD` agree with the approximations
  `43.09/24.01`, `41.67/32.01`, `62.49/48.00` quoted after `prop:forest-records`, to `0.005`.

Not checked: the gates and the coefficients of the `84` repairs, which are only in the records.
-/

namespace Sarkozy.UpperComparison

open Finset Sarkozy.PartV

/-- **The state ledgers of `cert:upper-lower-bands`** (symmetric, skew), the same in all `45`
bands of `[P₃, 2^48)`, as exact rationals. -/
def lowerLedger : PType × PType → ℚ × ℚ
  | (.L, .R) => (11237485578048 / 10 ^ 12, 11166605062536 / 10 ^ 12)
  | (.R, .L) => (658393224044 / 10 ^ 11, 4802700055586 / 10 ^ 12)
  | (.D, .D) => (43091020254 / 10 ^ 9, 24006543228 / 10 ^ 9)
  | (.D, .S) => (41670210072 / 10 ^ 9, 3201254062 / 10 ^ 8)
  | (.S, .D) => (6249133143 / 10 ^ 8, 48004827252 / 10 ^ 9)
  | (.S, .S) => (45271035916 / 10 ^ 9, 45271032884 / 10 ^ 9)
  | (.L, .C) => (51202575332 / 10 ^ 9, 37711621448 / 10 ^ 9)
  | (.C, .L) => (51405075886 / 10 ^ 9, 37914122002 / 10 ^ 9)
  | (.D, .R) => (207354081636 / 10 ^ 9, 163894569102 / 10 ^ 9)
  | (.R, .D) => (163470704406 / 10 ^ 9, 120011191872 / 10 ^ 9)
  | (.S, .R) => (108629454264 / 10 ^ 9, 108629445156 / 10 ^ 9)
  | (.R, .S) => (106542130168 / 10 ^ 9, 106542121068 / 10 ^ 9)
  | _ => (0, 0)

/-- The twelve states of the table. -/
def ledgerStates : Finset (PType × PType) :=
  {(.L, .R), (.R, .L), (.D, .D), (.D, .S), (.S, .D), (.S, .S),
    (.L, .C), (.C, .L), (.D, .R), (.R, .D), (.S, .R), (.R, .S)}

/-- The number of changed records of a state. -/
def changedCount (t : PType × PType) : ℕ :=
  (univ.filter fun i : UpIdx => upperFate i = .changed ∧ i.2.1 = t).card

/-- **The changed records have exactly the states of the table.** -/
theorem ledger_states : (∀ i : UpIdx, upperFate i = .changed → i.2.1 ∈ ledgerStates) ∧
    ∀ t ∈ ledgerStates, 0 < changedCount t := by
  decide +kernel

/-- **The numbers of changed records by state** (`lem:six-query-retention`). -/
theorem changed_by_state :
    changedCount (.L, .R) = 6 ∧ changedCount (.R, .L) = 2 ∧ changedCount (.D, .D) = 6 ∧
    changedCount (.D, .S) = 4 ∧ changedCount (.S, .D) = 6 ∧ changedCount (.S, .S) = 4 ∧
    changedCount (.L, .C) = 2 ∧ changedCount (.C, .L) = 2 ∧ changedCount (.D, .R) = 18 ∧
    changedCount (.R, .D) = 18 ∧ changedCount (.S, .R) = 12 ∧ changedCount (.R, .S) = 12 := by
  decide +kernel

/-- The dense EL coefficients at `2^47` (`prop:dense-comparison`, `cert:upper-lower-bands`(e)). -/
def denseEL47 : ℚ × ℚ := (3291966120220 / 10 ^ 12, 2401350027793 / 10 ^ 12)

/-- The LE coefficients of vector II at `167·2^40` (`prop:le-mixture`). -/
def leMixtureP3 : ℚ × ℚ := (1872914263008 / 10 ^ 12, 1861100843756 / 10 ^ 12)

/-- **The `RL` ledger** is the number of changed `RL` records times the dense EL coefficients. -/
theorem ledger_RL_binding :
    lowerLedger (.R, .L) = ((changedCount (.R, .L) : ℚ) * denseEL47.1,
      (changedCount (.R, .L) : ℚ) * denseEL47.2) := by
  rw [changed_by_state.2.1]
  simp only [lowerLedger, denseEL47, Prod.mk.injEq]
  norm_num

/-- **The `LR` ledger** is the number of changed `LR` records times the LE coefficients of
vector II at `167·2^40`. -/
theorem ledger_LR_binding :
    lowerLedger (.L, .R) = ((changedCount (.L, .R) : ℚ) * leMixtureP3.1,
      (changedCount (.L, .R) : ℚ) * leMixtureP3.2) := by
  rw [changed_by_state.1]
  simp only [lowerLedger, leMixtureP3, Prod.mk.injEq]
  norm_num

/-- **Symmetric ledgers dominate skew ledgers** in every state of the table. -/
theorem ledger_sym_ge_skew : ∀ t ∈ ledgerStates, (lowerLedger t).2 ≤ (lowerLedger t).1 := by
  intro t ht
  simp only [ledgerStates, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    norm_num [lowerLedger]

/-- **The forest ledgers at `2^47`** agree with the approximations quoted after
`prop:forest-records`. -/
theorem forest_ledgers_approx :
    |(lowerLedger (.D, .D)).1 - 4309 / 100| < 5 / 1000 ∧
    |(lowerLedger (.D, .D)).2 - 2401 / 100| < 5 / 1000 ∧
    |(lowerLedger (.D, .S)).1 - 4167 / 100| < 5 / 1000 ∧
    |(lowerLedger (.D, .S)).2 - 3201 / 100| < 5 / 1000 ∧
    |(lowerLedger (.S, .D)).1 - 6249 / 100| < 5 / 1000 ∧
    |(lowerLedger (.S, .D)).2 - 4800 / 100| < 5 / 1000 := by
  simp only [lowerLedger]
  norm_num [abs_lt]

end Sarkozy.UpperComparison
