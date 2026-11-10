module

public import Sarkozy.DensityChain2.Folded

@[expose] public section

/-!
# The selected part of the main price (`eq:square-step`, `def:record:structured-energy`)

The main price of a structured energy is `Π = ∏_v ξ_v^{a/72} ∏_v (ᾱ_v/α)^{θ/72}` with
`ξ_v = (N/M_v) sq(D_{0,v} D_E)`. When every `D_{0,v}` is coprime to `D_E`,
`sq(D_{0,v} D_E) = sq(D_{0,v}) sq(D_E)` and `Π = sq(D_E)^a Π_∅`, where `Π_∅` is the main price of
the same slot data with no selected atoms (`mainPrice_split`). The slot data are arbitrary, so this
applies to the folded data `envSlots ∘ φ_±` of DC2's `hfold` as well as to the unfolded data (B9's
`envMainPrice_eq` is the unfolded case with the slot factors computed). This is the step that
makes the per-piece main price of `hfold` the product of the term-independent `Π_∅` and the
selected price `sq(D_E)^a`, which the piece prices `∏_𝔟 bpieceG` must then dominate
(`∏_E ‖Λ_𝔟‖ sq(D_𝔟)^a ≤ ∏ bpieceG ∏_f u_𝔟`; `PiecePrice.piecePrice_plus/minus_le`).
-/

namespace Sarkozy.DensityChain2

open Finset
open scoped BigOperators
open Sarkozy.Structured Sarkozy.Functional

/-- **`Π = sq(D_E)^a Π_∅`** for slot moduli coprime to `D_E`. -/
theorem mainPrice_split {J : Type} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]
    (Es : Finset J) (D0 M : Slot → ℕ) (L : ℕ) (αbar : Slot → ℝ) (a θ α : ℝ)
    (hcop : ∀ v, (D0 v).Coprime (∏ j ∈ Es, m j)) :
    mainPrice (paperPrice m Es D0 M L) αbar (fun _ => True) a θ α =
      ((leastSquare (∏ j ∈ Es, m j) : ℕ) : ℝ) ^ a *
        mainPrice (paperPrice m ∅ D0 M L) αbar (fun _ => True) a θ α := by
  unfold mainPrice paperPrice stepR
  set c : ℝ := ((leastSquare (∏ j ∈ Es, m j) : ℕ) : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hx : ∀ v, 0 ≤ ((blockScale * L : ℕ) : ℝ) / (M v : ℝ) * ((leastSquare (D0 v) : ℕ) : ℝ) :=
    fun v => mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hv : ∀ v, (((blockScale * L : ℕ) : ℝ) / (M v : ℝ) *
      ((leastSquare (D0 v * ∏ j ∈ Es, m j) : ℕ) : ℝ)) ^ (a / 72) =
      (((blockScale * L : ℕ) : ℝ) / (M v : ℝ) * ((leastSquare (D0 v * ∏ j ∈ (∅ : Finset J), m j) :
        ℕ) : ℝ)) ^ (a / 72) * c ^ (a / 72) := by
    intro v
    have hcast : ((leastSquare (D0 v) * leastSquare (∏ j ∈ Es, m j) : ℕ) : ℝ) =
        ((leastSquare (D0 v) : ℕ) : ℝ) * c := by
      rw [hc]
      push_cast
      ring
    rw [prod_empty, mul_one, leastSquare_mul (hcop v), hcast, ← mul_assoc,
      Real.mul_rpow (hx v) hc0]
  simp only [hv, prod_mul_distrib]
  have hpow : ∏ _v : Slot, c ^ (a / 72) = c ^ a := by
    rw [prod_const, card_univ, card_slot, ← Real.rpow_natCast, ← Real.rpow_mul hc0]
    norm_num
  rw [hpow]
  ring

end Sarkozy.DensityChain2
