module

public import Sarkozy.PositiveRoots.CoherentEndpointModel

/-! Exact coverage of all nonzero endpoint matrix entries. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentEndpoint

open Finset Sarkozy.SpectralD

def embedding (c : Cut) : Fin (size c) ↪ Fin 64 := ⟨index c, index_injective c⟩

theorem mem_active_iff (c : Cut) : ∀ i : Fin 64,
    i.val ∈ active c ↔ i ∈ univ.map (embedding c) := by
  cases c <;> decide +kernel

theorem chamber_support_00 : ∀ j : Fin 64,
    ((0 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 0 j = 0 ∧ starImag .chamber 0 j = 0 ∧
        numerator .chamber 0 j = 0) := by decide +kernel

theorem chamber_support_01 : ∀ j : Fin 64,
    ((1 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 1 j = 0 ∧ starImag .chamber 1 j = 0 ∧
        numerator .chamber 1 j = 0) := by decide +kernel

theorem chamber_support_02 : ∀ j : Fin 64,
    ((2 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 2 j = 0 ∧ starImag .chamber 2 j = 0 ∧
        numerator .chamber 2 j = 0) := by decide +kernel

theorem chamber_support_03 : ∀ j : Fin 64,
    ((3 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 3 j = 0 ∧ starImag .chamber 3 j = 0 ∧
        numerator .chamber 3 j = 0) := by decide +kernel

theorem chamber_support_04 : ∀ j : Fin 64,
    ((4 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 4 j = 0 ∧ starImag .chamber 4 j = 0 ∧
        numerator .chamber 4 j = 0) := by decide +kernel

theorem chamber_support_05 : ∀ j : Fin 64,
    ((5 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 5 j = 0 ∧ starImag .chamber 5 j = 0 ∧
        numerator .chamber 5 j = 0) := by decide +kernel

theorem chamber_support_06 : ∀ j : Fin 64,
    ((6 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 6 j = 0 ∧ starImag .chamber 6 j = 0 ∧
        numerator .chamber 6 j = 0) := by decide +kernel

theorem chamber_support_07 : ∀ j : Fin 64,
    ((7 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 7 j = 0 ∧ starImag .chamber 7 j = 0 ∧
        numerator .chamber 7 j = 0) := by decide +kernel

theorem chamber_support_08 : ∀ j : Fin 64,
    ((8 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 8 j = 0 ∧ starImag .chamber 8 j = 0 ∧
        numerator .chamber 8 j = 0) := by decide +kernel

theorem chamber_support_09 : ∀ j : Fin 64,
    ((9 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 9 j = 0 ∧ starImag .chamber 9 j = 0 ∧
        numerator .chamber 9 j = 0) := by decide +kernel

theorem chamber_support_10 : ∀ j : Fin 64,
    ((10 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 10 j = 0 ∧ starImag .chamber 10 j = 0 ∧
        numerator .chamber 10 j = 0) := by decide +kernel

theorem chamber_support_11 : ∀ j : Fin 64,
    ((11 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 11 j = 0 ∧ starImag .chamber 11 j = 0 ∧
        numerator .chamber 11 j = 0) := by decide +kernel

theorem chamber_support_12 : ∀ j : Fin 64,
    ((12 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 12 j = 0 ∧ starImag .chamber 12 j = 0 ∧
        numerator .chamber 12 j = 0) := by decide +kernel

theorem chamber_support_13 : ∀ j : Fin 64,
    ((13 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 13 j = 0 ∧ starImag .chamber 13 j = 0 ∧
        numerator .chamber 13 j = 0) := by decide +kernel

theorem chamber_support_14 : ∀ j : Fin 64,
    ((14 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 14 j = 0 ∧ starImag .chamber 14 j = 0 ∧
        numerator .chamber 14 j = 0) := by decide +kernel

theorem chamber_support_15 : ∀ j : Fin 64,
    ((15 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 15 j = 0 ∧ starImag .chamber 15 j = 0 ∧
        numerator .chamber 15 j = 0) := by decide +kernel

theorem chamber_support_16 : ∀ j : Fin 64,
    ((16 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 16 j = 0 ∧ starImag .chamber 16 j = 0 ∧
        numerator .chamber 16 j = 0) := by decide +kernel

theorem chamber_support_17 : ∀ j : Fin 64,
    ((17 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 17 j = 0 ∧ starImag .chamber 17 j = 0 ∧
        numerator .chamber 17 j = 0) := by decide +kernel

theorem chamber_support_18 : ∀ j : Fin 64,
    ((18 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 18 j = 0 ∧ starImag .chamber 18 j = 0 ∧
        numerator .chamber 18 j = 0) := by decide +kernel

theorem chamber_support_19 : ∀ j : Fin 64,
    ((19 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 19 j = 0 ∧ starImag .chamber 19 j = 0 ∧
        numerator .chamber 19 j = 0) := by decide +kernel

theorem chamber_support_20 : ∀ j : Fin 64,
    ((20 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 20 j = 0 ∧ starImag .chamber 20 j = 0 ∧
        numerator .chamber 20 j = 0) := by decide +kernel

theorem chamber_support_21 : ∀ j : Fin 64,
    ((21 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 21 j = 0 ∧ starImag .chamber 21 j = 0 ∧
        numerator .chamber 21 j = 0) := by decide +kernel

theorem chamber_support_22 : ∀ j : Fin 64,
    ((22 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 22 j = 0 ∧ starImag .chamber 22 j = 0 ∧
        numerator .chamber 22 j = 0) := by decide +kernel

theorem chamber_support_23 : ∀ j : Fin 64,
    ((23 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 23 j = 0 ∧ starImag .chamber 23 j = 0 ∧
        numerator .chamber 23 j = 0) := by decide +kernel

theorem chamber_support_24 : ∀ j : Fin 64,
    ((24 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 24 j = 0 ∧ starImag .chamber 24 j = 0 ∧
        numerator .chamber 24 j = 0) := by decide +kernel

theorem chamber_support_25 : ∀ j : Fin 64,
    ((25 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 25 j = 0 ∧ starImag .chamber 25 j = 0 ∧
        numerator .chamber 25 j = 0) := by decide +kernel

theorem chamber_support_26 : ∀ j : Fin 64,
    ((26 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 26 j = 0 ∧ starImag .chamber 26 j = 0 ∧
        numerator .chamber 26 j = 0) := by decide +kernel

theorem chamber_support_27 : ∀ j : Fin 64,
    ((27 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 27 j = 0 ∧ starImag .chamber 27 j = 0 ∧
        numerator .chamber 27 j = 0) := by decide +kernel

theorem chamber_support_28 : ∀ j : Fin 64,
    ((28 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 28 j = 0 ∧ starImag .chamber 28 j = 0 ∧
        numerator .chamber 28 j = 0) := by decide +kernel

theorem chamber_support_29 : ∀ j : Fin 64,
    ((29 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 29 j = 0 ∧ starImag .chamber 29 j = 0 ∧
        numerator .chamber 29 j = 0) := by decide +kernel

theorem chamber_support_30 : ∀ j : Fin 64,
    ((30 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 30 j = 0 ∧ starImag .chamber 30 j = 0 ∧
        numerator .chamber 30 j = 0) := by decide +kernel

theorem chamber_support_31 : ∀ j : Fin 64,
    ((31 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 31 j = 0 ∧ starImag .chamber 31 j = 0 ∧
        numerator .chamber 31 j = 0) := by decide +kernel

theorem chamber_support_32 : ∀ j : Fin 64,
    ((32 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 32 j = 0 ∧ starImag .chamber 32 j = 0 ∧
        numerator .chamber 32 j = 0) := by decide +kernel

theorem chamber_support_33 : ∀ j : Fin 64,
    ((33 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 33 j = 0 ∧ starImag .chamber 33 j = 0 ∧
        numerator .chamber 33 j = 0) := by decide +kernel

theorem chamber_support_34 : ∀ j : Fin 64,
    ((34 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 34 j = 0 ∧ starImag .chamber 34 j = 0 ∧
        numerator .chamber 34 j = 0) := by decide +kernel

theorem chamber_support_35 : ∀ j : Fin 64,
    ((35 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 35 j = 0 ∧ starImag .chamber 35 j = 0 ∧
        numerator .chamber 35 j = 0) := by decide +kernel

theorem chamber_support_36 : ∀ j : Fin 64,
    ((36 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 36 j = 0 ∧ starImag .chamber 36 j = 0 ∧
        numerator .chamber 36 j = 0) := by decide +kernel

theorem chamber_support_37 : ∀ j : Fin 64,
    ((37 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 37 j = 0 ∧ starImag .chamber 37 j = 0 ∧
        numerator .chamber 37 j = 0) := by decide +kernel

theorem chamber_support_38 : ∀ j : Fin 64,
    ((38 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 38 j = 0 ∧ starImag .chamber 38 j = 0 ∧
        numerator .chamber 38 j = 0) := by decide +kernel

theorem chamber_support_39 : ∀ j : Fin 64,
    ((39 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 39 j = 0 ∧ starImag .chamber 39 j = 0 ∧
        numerator .chamber 39 j = 0) := by decide +kernel

theorem chamber_support_40 : ∀ j : Fin 64,
    ((40 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 40 j = 0 ∧ starImag .chamber 40 j = 0 ∧
        numerator .chamber 40 j = 0) := by decide +kernel

theorem chamber_support_41 : ∀ j : Fin 64,
    ((41 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 41 j = 0 ∧ starImag .chamber 41 j = 0 ∧
        numerator .chamber 41 j = 0) := by decide +kernel

theorem chamber_support_42 : ∀ j : Fin 64,
    ((42 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 42 j = 0 ∧ starImag .chamber 42 j = 0 ∧
        numerator .chamber 42 j = 0) := by decide +kernel

theorem chamber_support_43 : ∀ j : Fin 64,
    ((43 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 43 j = 0 ∧ starImag .chamber 43 j = 0 ∧
        numerator .chamber 43 j = 0) := by decide +kernel

theorem chamber_support_44 : ∀ j : Fin 64,
    ((44 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 44 j = 0 ∧ starImag .chamber 44 j = 0 ∧
        numerator .chamber 44 j = 0) := by decide +kernel

theorem chamber_support_45 : ∀ j : Fin 64,
    ((45 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 45 j = 0 ∧ starImag .chamber 45 j = 0 ∧
        numerator .chamber 45 j = 0) := by decide +kernel

theorem chamber_support_46 : ∀ j : Fin 64,
    ((46 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 46 j = 0 ∧ starImag .chamber 46 j = 0 ∧
        numerator .chamber 46 j = 0) := by decide +kernel

theorem chamber_support_47 : ∀ j : Fin 64,
    ((47 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 47 j = 0 ∧ starImag .chamber 47 j = 0 ∧
        numerator .chamber 47 j = 0) := by decide +kernel

theorem chamber_support_48 : ∀ j : Fin 64,
    ((48 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 48 j = 0 ∧ starImag .chamber 48 j = 0 ∧
        numerator .chamber 48 j = 0) := by decide +kernel

theorem chamber_support_49 : ∀ j : Fin 64,
    ((49 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 49 j = 0 ∧ starImag .chamber 49 j = 0 ∧
        numerator .chamber 49 j = 0) := by decide +kernel

theorem chamber_support_50 : ∀ j : Fin 64,
    ((50 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 50 j = 0 ∧ starImag .chamber 50 j = 0 ∧
        numerator .chamber 50 j = 0) := by decide +kernel

theorem chamber_support_51 : ∀ j : Fin 64,
    ((51 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 51 j = 0 ∧ starImag .chamber 51 j = 0 ∧
        numerator .chamber 51 j = 0) := by decide +kernel

theorem chamber_support_52 : ∀ j : Fin 64,
    ((52 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 52 j = 0 ∧ starImag .chamber 52 j = 0 ∧
        numerator .chamber 52 j = 0) := by decide +kernel

theorem chamber_support_53 : ∀ j : Fin 64,
    ((53 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 53 j = 0 ∧ starImag .chamber 53 j = 0 ∧
        numerator .chamber 53 j = 0) := by decide +kernel

theorem chamber_support_54 : ∀ j : Fin 64,
    ((54 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 54 j = 0 ∧ starImag .chamber 54 j = 0 ∧
        numerator .chamber 54 j = 0) := by decide +kernel

theorem chamber_support_55 : ∀ j : Fin 64,
    ((55 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 55 j = 0 ∧ starImag .chamber 55 j = 0 ∧
        numerator .chamber 55 j = 0) := by decide +kernel

theorem chamber_support_56 : ∀ j : Fin 64,
    ((56 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 56 j = 0 ∧ starImag .chamber 56 j = 0 ∧
        numerator .chamber 56 j = 0) := by decide +kernel

theorem chamber_support_57 : ∀ j : Fin 64,
    ((57 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 57 j = 0 ∧ starImag .chamber 57 j = 0 ∧
        numerator .chamber 57 j = 0) := by decide +kernel

theorem chamber_support_58 : ∀ j : Fin 64,
    ((58 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 58 j = 0 ∧ starImag .chamber 58 j = 0 ∧
        numerator .chamber 58 j = 0) := by decide +kernel

theorem chamber_support_59 : ∀ j : Fin 64,
    ((59 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 59 j = 0 ∧ starImag .chamber 59 j = 0 ∧
        numerator .chamber 59 j = 0) := by decide +kernel

theorem chamber_support_60 : ∀ j : Fin 64,
    ((60 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 60 j = 0 ∧ starImag .chamber 60 j = 0 ∧
        numerator .chamber 60 j = 0) := by decide +kernel

theorem chamber_support_61 : ∀ j : Fin 64,
    ((61 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 61 j = 0 ∧ starImag .chamber 61 j = 0 ∧
        numerator .chamber 61 j = 0) := by decide +kernel

theorem chamber_support_62 : ∀ j : Fin 64,
    ((62 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 62 j = 0 ∧ starImag .chamber 62 j = 0 ∧
        numerator .chamber 62 j = 0) := by decide +kernel

theorem chamber_support_63 : ∀ j : Fin 64,
    ((63 : Fin 64).val ∈ active .chamber ∧ j.val ∈ active .chamber) ∨
      (starReal .chamber 63 j = 0 ∧ starImag .chamber 63 j = 0 ∧
        numerator .chamber 63 j = 0) := by decide +kernel

theorem layer_support_00 : ∀ j : Fin 64,
    ((0 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 0 j = 0 ∧ starImag .layer 0 j = 0 ∧
        numerator .layer 0 j = 0) := by decide +kernel

theorem layer_support_01 : ∀ j : Fin 64,
    ((1 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 1 j = 0 ∧ starImag .layer 1 j = 0 ∧
        numerator .layer 1 j = 0) := by decide +kernel

theorem layer_support_02 : ∀ j : Fin 64,
    ((2 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 2 j = 0 ∧ starImag .layer 2 j = 0 ∧
        numerator .layer 2 j = 0) := by decide +kernel

theorem layer_support_03 : ∀ j : Fin 64,
    ((3 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 3 j = 0 ∧ starImag .layer 3 j = 0 ∧
        numerator .layer 3 j = 0) := by decide +kernel

theorem layer_support_04 : ∀ j : Fin 64,
    ((4 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 4 j = 0 ∧ starImag .layer 4 j = 0 ∧
        numerator .layer 4 j = 0) := by decide +kernel

theorem layer_support_05 : ∀ j : Fin 64,
    ((5 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 5 j = 0 ∧ starImag .layer 5 j = 0 ∧
        numerator .layer 5 j = 0) := by decide +kernel

theorem layer_support_06 : ∀ j : Fin 64,
    ((6 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 6 j = 0 ∧ starImag .layer 6 j = 0 ∧
        numerator .layer 6 j = 0) := by decide +kernel

theorem layer_support_07 : ∀ j : Fin 64,
    ((7 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 7 j = 0 ∧ starImag .layer 7 j = 0 ∧
        numerator .layer 7 j = 0) := by decide +kernel

theorem layer_support_08 : ∀ j : Fin 64,
    ((8 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 8 j = 0 ∧ starImag .layer 8 j = 0 ∧
        numerator .layer 8 j = 0) := by decide +kernel

theorem layer_support_09 : ∀ j : Fin 64,
    ((9 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 9 j = 0 ∧ starImag .layer 9 j = 0 ∧
        numerator .layer 9 j = 0) := by decide +kernel

theorem layer_support_10 : ∀ j : Fin 64,
    ((10 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 10 j = 0 ∧ starImag .layer 10 j = 0 ∧
        numerator .layer 10 j = 0) := by decide +kernel

theorem layer_support_11 : ∀ j : Fin 64,
    ((11 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 11 j = 0 ∧ starImag .layer 11 j = 0 ∧
        numerator .layer 11 j = 0) := by decide +kernel

theorem layer_support_12 : ∀ j : Fin 64,
    ((12 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 12 j = 0 ∧ starImag .layer 12 j = 0 ∧
        numerator .layer 12 j = 0) := by decide +kernel

theorem layer_support_13 : ∀ j : Fin 64,
    ((13 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 13 j = 0 ∧ starImag .layer 13 j = 0 ∧
        numerator .layer 13 j = 0) := by decide +kernel

theorem layer_support_14 : ∀ j : Fin 64,
    ((14 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 14 j = 0 ∧ starImag .layer 14 j = 0 ∧
        numerator .layer 14 j = 0) := by decide +kernel

theorem layer_support_15 : ∀ j : Fin 64,
    ((15 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 15 j = 0 ∧ starImag .layer 15 j = 0 ∧
        numerator .layer 15 j = 0) := by decide +kernel

theorem layer_support_16 : ∀ j : Fin 64,
    ((16 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 16 j = 0 ∧ starImag .layer 16 j = 0 ∧
        numerator .layer 16 j = 0) := by decide +kernel

theorem layer_support_17 : ∀ j : Fin 64,
    ((17 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 17 j = 0 ∧ starImag .layer 17 j = 0 ∧
        numerator .layer 17 j = 0) := by decide +kernel

theorem layer_support_18 : ∀ j : Fin 64,
    ((18 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 18 j = 0 ∧ starImag .layer 18 j = 0 ∧
        numerator .layer 18 j = 0) := by decide +kernel

theorem layer_support_19 : ∀ j : Fin 64,
    ((19 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 19 j = 0 ∧ starImag .layer 19 j = 0 ∧
        numerator .layer 19 j = 0) := by decide +kernel

theorem layer_support_20 : ∀ j : Fin 64,
    ((20 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 20 j = 0 ∧ starImag .layer 20 j = 0 ∧
        numerator .layer 20 j = 0) := by decide +kernel

theorem layer_support_21 : ∀ j : Fin 64,
    ((21 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 21 j = 0 ∧ starImag .layer 21 j = 0 ∧
        numerator .layer 21 j = 0) := by decide +kernel

theorem layer_support_22 : ∀ j : Fin 64,
    ((22 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 22 j = 0 ∧ starImag .layer 22 j = 0 ∧
        numerator .layer 22 j = 0) := by decide +kernel

theorem layer_support_23 : ∀ j : Fin 64,
    ((23 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 23 j = 0 ∧ starImag .layer 23 j = 0 ∧
        numerator .layer 23 j = 0) := by decide +kernel

theorem layer_support_24 : ∀ j : Fin 64,
    ((24 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 24 j = 0 ∧ starImag .layer 24 j = 0 ∧
        numerator .layer 24 j = 0) := by decide +kernel

theorem layer_support_25 : ∀ j : Fin 64,
    ((25 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 25 j = 0 ∧ starImag .layer 25 j = 0 ∧
        numerator .layer 25 j = 0) := by decide +kernel

theorem layer_support_26 : ∀ j : Fin 64,
    ((26 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 26 j = 0 ∧ starImag .layer 26 j = 0 ∧
        numerator .layer 26 j = 0) := by decide +kernel

theorem layer_support_27 : ∀ j : Fin 64,
    ((27 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 27 j = 0 ∧ starImag .layer 27 j = 0 ∧
        numerator .layer 27 j = 0) := by decide +kernel

theorem layer_support_28 : ∀ j : Fin 64,
    ((28 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 28 j = 0 ∧ starImag .layer 28 j = 0 ∧
        numerator .layer 28 j = 0) := by decide +kernel

theorem layer_support_29 : ∀ j : Fin 64,
    ((29 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 29 j = 0 ∧ starImag .layer 29 j = 0 ∧
        numerator .layer 29 j = 0) := by decide +kernel

theorem layer_support_30 : ∀ j : Fin 64,
    ((30 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 30 j = 0 ∧ starImag .layer 30 j = 0 ∧
        numerator .layer 30 j = 0) := by decide +kernel

theorem layer_support_31 : ∀ j : Fin 64,
    ((31 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 31 j = 0 ∧ starImag .layer 31 j = 0 ∧
        numerator .layer 31 j = 0) := by decide +kernel

theorem layer_support_32 : ∀ j : Fin 64,
    ((32 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 32 j = 0 ∧ starImag .layer 32 j = 0 ∧
        numerator .layer 32 j = 0) := by decide +kernel

theorem layer_support_33 : ∀ j : Fin 64,
    ((33 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 33 j = 0 ∧ starImag .layer 33 j = 0 ∧
        numerator .layer 33 j = 0) := by decide +kernel

theorem layer_support_34 : ∀ j : Fin 64,
    ((34 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 34 j = 0 ∧ starImag .layer 34 j = 0 ∧
        numerator .layer 34 j = 0) := by decide +kernel

theorem layer_support_35 : ∀ j : Fin 64,
    ((35 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 35 j = 0 ∧ starImag .layer 35 j = 0 ∧
        numerator .layer 35 j = 0) := by decide +kernel

theorem layer_support_36 : ∀ j : Fin 64,
    ((36 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 36 j = 0 ∧ starImag .layer 36 j = 0 ∧
        numerator .layer 36 j = 0) := by decide +kernel

theorem layer_support_37 : ∀ j : Fin 64,
    ((37 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 37 j = 0 ∧ starImag .layer 37 j = 0 ∧
        numerator .layer 37 j = 0) := by decide +kernel

theorem layer_support_38 : ∀ j : Fin 64,
    ((38 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 38 j = 0 ∧ starImag .layer 38 j = 0 ∧
        numerator .layer 38 j = 0) := by decide +kernel

theorem layer_support_39 : ∀ j : Fin 64,
    ((39 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 39 j = 0 ∧ starImag .layer 39 j = 0 ∧
        numerator .layer 39 j = 0) := by decide +kernel

theorem layer_support_40 : ∀ j : Fin 64,
    ((40 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 40 j = 0 ∧ starImag .layer 40 j = 0 ∧
        numerator .layer 40 j = 0) := by decide +kernel

theorem layer_support_41 : ∀ j : Fin 64,
    ((41 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 41 j = 0 ∧ starImag .layer 41 j = 0 ∧
        numerator .layer 41 j = 0) := by decide +kernel

theorem layer_support_42 : ∀ j : Fin 64,
    ((42 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 42 j = 0 ∧ starImag .layer 42 j = 0 ∧
        numerator .layer 42 j = 0) := by decide +kernel

theorem layer_support_43 : ∀ j : Fin 64,
    ((43 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 43 j = 0 ∧ starImag .layer 43 j = 0 ∧
        numerator .layer 43 j = 0) := by decide +kernel

theorem layer_support_44 : ∀ j : Fin 64,
    ((44 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 44 j = 0 ∧ starImag .layer 44 j = 0 ∧
        numerator .layer 44 j = 0) := by decide +kernel

theorem layer_support_45 : ∀ j : Fin 64,
    ((45 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 45 j = 0 ∧ starImag .layer 45 j = 0 ∧
        numerator .layer 45 j = 0) := by decide +kernel

theorem layer_support_46 : ∀ j : Fin 64,
    ((46 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 46 j = 0 ∧ starImag .layer 46 j = 0 ∧
        numerator .layer 46 j = 0) := by decide +kernel

theorem layer_support_47 : ∀ j : Fin 64,
    ((47 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 47 j = 0 ∧ starImag .layer 47 j = 0 ∧
        numerator .layer 47 j = 0) := by decide +kernel

theorem layer_support_48 : ∀ j : Fin 64,
    ((48 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 48 j = 0 ∧ starImag .layer 48 j = 0 ∧
        numerator .layer 48 j = 0) := by decide +kernel

theorem layer_support_49 : ∀ j : Fin 64,
    ((49 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 49 j = 0 ∧ starImag .layer 49 j = 0 ∧
        numerator .layer 49 j = 0) := by decide +kernel

theorem layer_support_50 : ∀ j : Fin 64,
    ((50 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 50 j = 0 ∧ starImag .layer 50 j = 0 ∧
        numerator .layer 50 j = 0) := by decide +kernel

theorem layer_support_51 : ∀ j : Fin 64,
    ((51 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 51 j = 0 ∧ starImag .layer 51 j = 0 ∧
        numerator .layer 51 j = 0) := by decide +kernel

theorem layer_support_52 : ∀ j : Fin 64,
    ((52 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 52 j = 0 ∧ starImag .layer 52 j = 0 ∧
        numerator .layer 52 j = 0) := by decide +kernel

theorem layer_support_53 : ∀ j : Fin 64,
    ((53 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 53 j = 0 ∧ starImag .layer 53 j = 0 ∧
        numerator .layer 53 j = 0) := by decide +kernel

theorem layer_support_54 : ∀ j : Fin 64,
    ((54 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 54 j = 0 ∧ starImag .layer 54 j = 0 ∧
        numerator .layer 54 j = 0) := by decide +kernel

theorem layer_support_55 : ∀ j : Fin 64,
    ((55 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 55 j = 0 ∧ starImag .layer 55 j = 0 ∧
        numerator .layer 55 j = 0) := by decide +kernel

theorem layer_support_56 : ∀ j : Fin 64,
    ((56 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 56 j = 0 ∧ starImag .layer 56 j = 0 ∧
        numerator .layer 56 j = 0) := by decide +kernel

theorem layer_support_57 : ∀ j : Fin 64,
    ((57 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 57 j = 0 ∧ starImag .layer 57 j = 0 ∧
        numerator .layer 57 j = 0) := by decide +kernel

theorem layer_support_58 : ∀ j : Fin 64,
    ((58 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 58 j = 0 ∧ starImag .layer 58 j = 0 ∧
        numerator .layer 58 j = 0) := by decide +kernel

theorem layer_support_59 : ∀ j : Fin 64,
    ((59 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 59 j = 0 ∧ starImag .layer 59 j = 0 ∧
        numerator .layer 59 j = 0) := by decide +kernel

theorem layer_support_60 : ∀ j : Fin 64,
    ((60 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 60 j = 0 ∧ starImag .layer 60 j = 0 ∧
        numerator .layer 60 j = 0) := by decide +kernel

theorem layer_support_61 : ∀ j : Fin 64,
    ((61 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 61 j = 0 ∧ starImag .layer 61 j = 0 ∧
        numerator .layer 61 j = 0) := by decide +kernel

theorem layer_support_62 : ∀ j : Fin 64,
    ((62 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 62 j = 0 ∧ starImag .layer 62 j = 0 ∧
        numerator .layer 62 j = 0) := by decide +kernel

theorem layer_support_63 : ∀ j : Fin 64,
    ((63 : Fin 64).val ∈ active .layer ∧ j.val ∈ active .layer) ∨
      (starReal .layer 63 j = 0 ∧ starImag .layer 63 j = 0 ∧
        numerator .layer 63 j = 0) := by decide +kernel

theorem support_checks (c : Cut) (i j : Fin 64) :
    (i.val ∈ active c ∧ j.val ∈ active c) ∨
      (starReal c i j = 0 ∧ starImag c i j = 0 ∧ numerator c i j = 0) := by
  cases c with
  | chamber =>
    fin_cases i
    · exact chamber_support_00 j
    · exact chamber_support_01 j
    · exact chamber_support_02 j
    · exact chamber_support_03 j
    · exact chamber_support_04 j
    · exact chamber_support_05 j
    · exact chamber_support_06 j
    · exact chamber_support_07 j
    · exact chamber_support_08 j
    · exact chamber_support_09 j
    · exact chamber_support_10 j
    · exact chamber_support_11 j
    · exact chamber_support_12 j
    · exact chamber_support_13 j
    · exact chamber_support_14 j
    · exact chamber_support_15 j
    · exact chamber_support_16 j
    · exact chamber_support_17 j
    · exact chamber_support_18 j
    · exact chamber_support_19 j
    · exact chamber_support_20 j
    · exact chamber_support_21 j
    · exact chamber_support_22 j
    · exact chamber_support_23 j
    · exact chamber_support_24 j
    · exact chamber_support_25 j
    · exact chamber_support_26 j
    · exact chamber_support_27 j
    · exact chamber_support_28 j
    · exact chamber_support_29 j
    · exact chamber_support_30 j
    · exact chamber_support_31 j
    · exact chamber_support_32 j
    · exact chamber_support_33 j
    · exact chamber_support_34 j
    · exact chamber_support_35 j
    · exact chamber_support_36 j
    · exact chamber_support_37 j
    · exact chamber_support_38 j
    · exact chamber_support_39 j
    · exact chamber_support_40 j
    · exact chamber_support_41 j
    · exact chamber_support_42 j
    · exact chamber_support_43 j
    · exact chamber_support_44 j
    · exact chamber_support_45 j
    · exact chamber_support_46 j
    · exact chamber_support_47 j
    · exact chamber_support_48 j
    · exact chamber_support_49 j
    · exact chamber_support_50 j
    · exact chamber_support_51 j
    · exact chamber_support_52 j
    · exact chamber_support_53 j
    · exact chamber_support_54 j
    · exact chamber_support_55 j
    · exact chamber_support_56 j
    · exact chamber_support_57 j
    · exact chamber_support_58 j
    · exact chamber_support_59 j
    · exact chamber_support_60 j
    · exact chamber_support_61 j
    · exact chamber_support_62 j
    · exact chamber_support_63 j
  | layer =>
    fin_cases i
    · exact layer_support_00 j
    · exact layer_support_01 j
    · exact layer_support_02 j
    · exact layer_support_03 j
    · exact layer_support_04 j
    · exact layer_support_05 j
    · exact layer_support_06 j
    · exact layer_support_07 j
    · exact layer_support_08 j
    · exact layer_support_09 j
    · exact layer_support_10 j
    · exact layer_support_11 j
    · exact layer_support_12 j
    · exact layer_support_13 j
    · exact layer_support_14 j
    · exact layer_support_15 j
    · exact layer_support_16 j
    · exact layer_support_17 j
    · exact layer_support_18 j
    · exact layer_support_19 j
    · exact layer_support_20 j
    · exact layer_support_21 j
    · exact layer_support_22 j
    · exact layer_support_23 j
    · exact layer_support_24 j
    · exact layer_support_25 j
    · exact layer_support_26 j
    · exact layer_support_27 j
    · exact layer_support_28 j
    · exact layer_support_29 j
    · exact layer_support_30 j
    · exact layer_support_31 j
    · exact layer_support_32 j
    · exact layer_support_33 j
    · exact layer_support_34 j
    · exact layer_support_35 j
    · exact layer_support_36 j
    · exact layer_support_37 j
    · exact layer_support_38 j
    · exact layer_support_39 j
    · exact layer_support_40 j
    · exact layer_support_41 j
    · exact layer_support_42 j
    · exact layer_support_43 j
    · exact layer_support_44 j
    · exact layer_support_45 j
    · exact layer_support_46 j
    · exact layer_support_47 j
    · exact layer_support_48 j
    · exact layer_support_49 j
    · exact layer_support_50 j
    · exact layer_support_51 j
    · exact layer_support_52 j
    · exact layer_support_53 j
    · exact layer_support_54 j
    · exact layer_support_55 j
    · exact layer_support_56 j
    · exact layer_support_57 j
    · exact layer_support_58 j
    · exact layer_support_59 j
    · exact layer_support_60 j
    · exact layer_support_61 j
    · exact layer_support_62 j
    · exact layer_support_63 j

theorem fullLeading_zero (c : Cut) (i j : Fin 64)
    (h : i ∉ univ.map (embedding c) ∨ j ∉ univ.map (embedding c)) :
    fullLeading c i j = 0 := by
  rcases support_checks c i j with ha | hz
  · rcases h with hi | hj
    · exact False.elim (hi ((mem_active_iff c i).mp ha.1))
    · exact False.elim (hj ((mem_active_iff c j).mp ha.2))
  · apply Complex.ext <;> simp [fullLeading, hz.1, hz.2.1, hz.2.2, gaussian]

end Sarkozy.PositiveRoots.CoherentEndpoint
