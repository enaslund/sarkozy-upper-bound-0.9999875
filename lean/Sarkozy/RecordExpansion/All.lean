module

public import Sarkozy.RecordExpansion.Completion
public import Sarkozy.RecordExpansion.Replacement
public import Sarkozy.RecordExpansion.FirstStage
public import Sarkozy.RecordExpansion.Charging
public import Sarkozy.RecordExpansion.Toolkit
public import Sarkozy.RecordExpansion.SharpFirst
public import Sarkozy.RecordExpansion.TwoTags
public import Sarkozy.RecordExpansion.Variance
public import Sarkozy.RecordExpansion.SubsetExpansion
public import Sarkozy.Slots





@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.RecordExpansion

open Choice

variable {J : Type*} [Fintype J] [DecidableEq J]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]
  {T : J → Type*} [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)]

/-- `lem:record:record-expansion` (i), first identity, at the reserved cut of the
72 slots. -/
theorem reserved_energy_sub_eq_sum_selections
    {ν lam : ∀ b, ((Slot → X b) → ℝ) →ₗ[ℝ] ℝ}
    {ζ : ∀ b, T b → ChangeType → ((Slot → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hν : ∀ b, ν b = lam b + ∑ t, (ζ b t .sym + ζ b t .skew))
    (hlam : ∀ b, IsSymmetricAt reservedCut (lam b))
    (hs : ∀ b t, IsSymmetricAt reservedCut (ζ b t .sym))
    (ha : ∀ b t, IsSkewAt reservedCut (ζ b t .skew)) (F : (∀ b, X b) → ℝ) :
    diagonalIntegral (tensorLaw ν) F - diagonalIntegral (tensorLaw lam) F =
      ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), term lam ζ F ω :=
  energy_sub_eq_sum_selections reservedCut hν hlam hs ha F

/-- `lem:record:record-expansion` (i) and (ii) without classes, at the reserved cut
of the 72 slots: `|Y_ν - Y_λ| ≤ (B + z)(e^S cosh A - 1) Y` with the prices
`π^ε_{b,t} = π̃^ε_{b,t} q_b`. -/
theorem reserved_cost_le
    {ν lam N : ∀ b, ((Slot → X b) → ℝ) →ₗ[ℝ] ℝ}
    {ζ D : ∀ b, T b → ChangeType → ((Slot → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hν : ∀ b, ν b = lam b + ∑ t, (ζ b t .sym + ζ b t .skew))
    (hlam : ∀ b, IsSymmetricAt reservedCut (lam b))
    (hs : ∀ b t, IsSymmetricAt reservedCut (ζ b t .sym))
    (ha : ∀ b t, IsSkewAt reservedCut (ζ b t .skew))
    {πt : ∀ b, T b → ChangeType → ℝ} (hπt : ∀ b t e, 0 ≤ πt b t e)
    (hN : ∀ b, reservedCut.Bracket (N b) (lam b) (N b))
    (hζ : ∀ b t e,
      reservedCut.Bracket (πt b t e • D b t e) (ζ b t e) (πt b t e • D b t e))
    {q : J → ℝ} (hq : ∀ b, 0 ≤ q b) (F : (∀ b, X b) → ℝ)
    {Bf z Y : ℝ} (hY : 0 ≤ Y) (hBz : 0 ≤ Bf + z)
    (hE1 : ∀ ω : Choice T, IsSelection ω →
      diagonalIntegral (envelopeLaw N D ω) F ≤ (Bf + z) * (∏ b ∈ Choice.support ω, q b) * Y) :
    |diagonalIntegral (tensorLaw ν) F - diagonalIntegral (tensorLaw lam) F| ≤
      (Bf + z) * (Real.exp (∑ b, symTotal (fun b t e => πt b t e * q b) b) *
        Real.cosh (∑ b, skewTotal (fun b t e => πt b t e * q b) b) - 1) * Y :=
  abs_energy_sub_le_of_envelopes reservedCut hν hlam hs ha hπt hN hζ hq F hY hBz hE1

end Sarkozy.RecordExpansion
