module

public import Mathlib.Data.Fin.VecNotation

@[expose] public section



namespace Sarkozy.PaperNumbers

/-- Runs of far band 0, chunk 0. -/
def farRuns0c0 : List (ℕ × ℕ × ℕ) := [
  (0, 127, 20)]

/-- Runs of far band 0 (`[2^52, 2^53)`). -/
def farRuns0 : List (ℕ × ℕ × ℕ) := farRuns0c0

/-- Runs of far band 1, chunk 0. -/
def farRuns1c0 : List (ℕ × ℕ × ℕ) := [
  (0, 109, 20), (110, 127, 19)]

/-- Runs of far band 1 (`[2^53, 2^54)`). -/
def farRuns1 : List (ℕ × ℕ × ℕ) := farRuns1c0

/-- Runs of far band 2, chunk 0. -/
def farRuns2c0 : List (ℕ × ℕ × ℕ) := [
  (0, 127, 19)]

/-- Runs of far band 2 (`[2^54, 2^55)`). -/
def farRuns2 : List (ℕ × ℕ × ℕ) := farRuns2c0

/-- Runs of far band 3, chunk 0. -/
def farRuns3c0 : List (ℕ × ℕ × ℕ) := [
  (0, 127, 19)]

/-- Runs of far band 3 (`[2^55, 2^56)`). -/
def farRuns3 : List (ℕ × ℕ × ℕ) := farRuns3c0

/-- Runs of far band 4, chunk 0. -/
def farRuns4c0 : List (ℕ × ℕ × ℕ) := [
  (0, 98, 19), (99, 127, 18)]

/-- Runs of far band 4 (`[2^56, 2^57)`). -/
def farRuns4 : List (ℕ × ℕ × ℕ) := farRuns4c0

/-- Runs of far band 5, chunk 0. -/
def farRuns5c0 : List (ℕ × ℕ × ℕ) := [
  (0, 127, 18)]

/-- Runs of far band 5 (`[2^57, 2^58)`). -/
def farRuns5 : List (ℕ × ℕ × ℕ) := farRuns5c0

/-- Runs of far band 6, chunk 0. -/
def farRuns6c0 : List (ℕ × ℕ × ℕ) := [
  (0, 255, 18)]

/-- Runs of far band 6 (`[2^58, 2^60)`). -/
def farRuns6 : List (ℕ × ℕ × ℕ) := farRuns6c0

/-- Runs of far band 7, chunk 0. -/
def farRuns7c0 : List (ℕ × ℕ × ℕ) := [
  (0, 2, 18), (3, 468, 17), (469, 511, 16)]

/-- Runs of far band 7 (`[2^60, 2^64)`). -/
def farRuns7 : List (ℕ × ℕ × ℕ) := farRuns7c0

/-- Runs of far band 8, chunk 0. -/
def farRuns8c0 : List (ℕ × ℕ × ℕ) := [
  (0, 482, 16), (483, 1081, 15), (1082, 1768, 14), (1769, 2566, 13), (2567, 3503, 12), (3504, 4618, 11),
  (4619, 5969, 10), (5970, 7639, 9), (7640, 9756, 8), (9757, 12528, 7), (12529, 16315, 6), (16316, 21802, 5),
  (21803, 30478, 4), (30479, 46310, 3), (46311, 57343, 2)]

/-- Runs of far band 8 (`[2^64, 2^512)`). -/
def farRuns8 : List (ℕ × ℕ × ℕ) := farRuns8c0

/-- **The nine far bands**: `(b, b', runs)`. -/
def farBand : Fin 9 → ℕ × ℕ × List (ℕ × ℕ × ℕ) := ![(52, 53, farRuns0), (53, 54, farRuns1), (54, 55, farRuns2), (55, 56, farRuns3), (56, 57, farRuns4), (57, 58, farRuns5), (58, 60, farRuns6), (60, 64, farRuns7), (64, 512, farRuns8)]

end Sarkozy.PaperNumbers
