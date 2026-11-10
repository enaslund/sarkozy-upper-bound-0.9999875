module

public import Sarkozy.PartV.CoherentHalfChart

/-!
# The coherent exceptional-event mass

Complete cancellation is covered by the actual dictionary's 144 matchings.
Each matching fixes at least three coordinates in the opposite half. This
proves the `144 C D / p³` mass bound from a kernel bound `C` and cube density `D`.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset

variable {p : ℕ} [Fact p.Prime]

def Exceptional (isLayer : Bool)
    (a : Half isLayer true → ZMod p) (b : Half isLayer false → ZMod p) : Prop :=
  Function.Injective b ∧ ∃ sc ∈ dictionary39, Cancellation (joinHalves isLayer a b) sc.1 ∅

theorem halfSupport_matching_budget_real (isLayer : Bool) :
    (dictionary39.map fun sc =>
      (CubePins.matchingCount (halfSupport isLayer true sc.1).card
        (halfSupport isLayer false sc.1).card : ℝ)).sum = 144 := by
  simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def, Nat.cast_ofNat] using
    congrArg (Nat.cast : ℕ → ℝ) (halfSupport_matching_budget isLayer)

theorem matching_event_mass (isLayer : Bool) (S : Support)
    (hS : 3 ≤ (halfSupport isLayer false S).card)
    (a : Half isLayer true → ZMod p) (w : (Half isLayer false → ZMod p) → ℝ)
    (hw0 : ∀ b, 0 ≤ w b) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ b, w b ≤ M / (p : ℝ) ^ 6) :
    CubePins.mass w (MatchingEvent isLayer S a) ≤
      (CubePins.matchingCount (halfSupport isLayer true S).card
        (halfSupport isLayer false S).card : ℝ) * (M / (p : ℝ) ^ 3) := by
  classical
  have h := CubePins.mass_matchings_budget (halfSupport isLayer false S)
    (fun v : halfSupport isLayer true S => a v.val) w hw0 M hM
    (by simpa only [ZMod.card, half_card] using hw)
  simp only [Fintype.card_coe, ZMod.card] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  exact div_le_div_of_nonneg_left hM (by positivity) (pow_le_pow_right₀ hp1 hS)

theorem exceptional_mass (isLayer : Bool)
    (a : Half isLayer true → ZMod p) (ha : Function.Injective a)
    (w : (Half isLayer false → ZMod p) → ℝ) (hw0 : ∀ b, 0 ≤ w b)
    (M : ℝ) (hM : 0 ≤ M) (hw : ∀ b, w b ≤ M / (p : ℝ) ^ 6) :
    CubePins.mass w (Exceptional isLayer a) ≤ 144 * (M / (p : ℝ) ^ 3) := by
  calc
    _ ≤ CubePins.mass w (fun b => ∃ sc ∈ dictionary39, MatchingEvent isLayer sc.1 a b) := by
      apply CubePins.mass_mono w hw0
      rintro b ⟨hb, sc, hsc, hcancel⟩
      exact ⟨sc, hsc, cancellation_matchingEvent isLayer sc.1 a b ha hb hcancel⟩
    _ ≤ (dictionary39.map fun sc => CubePins.mass w (MatchingEvent isLayer sc.1 a)).sum :=
      CubePins.mass_exists_list dictionary39 _ w hw0
    _ ≤ (dictionary39.map fun sc =>
        (CubePins.matchingCount (halfSupport isLayer true sc.1).card
          (halfSupport isLayer false sc.1).card : ℝ) * (M / (p : ℝ) ^ 3)).sum := by
      apply List.sum_le_sum
      intro sc hsc
      exact matching_event_mass isLayer sc.1 (halfSupport_min isLayer sc hsc) a w hw0 M hM hw
    _ = _ := by rw [List.sum_map_mul_right, halfSupport_matching_budget_real]

theorem exceptional_kernel_mass (isLayer : Bool)
    (a : Half isLayer true → ZMod p) (ha : Function.Injective a)
    (ν : FiniteLaw (Half isLayer false → ZMod p))
    (K : (Half isLayer false → ZMod p) → ℝ)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hK0 : ∀ b, 0 ≤ K b) (hK : ∀ b, K b ≤ C)
    (hν : ∀ b, ν.weight b ≤ D / (p : ℝ) ^ 6) :
    CubePins.mass (fun b => ν.weight b * K b) (Exceptional isLayer a) ≤
      144 * C * D / (p : ℝ) ^ 3 := by
  have h := exceptional_mass isLayer a ha (fun b => ν.weight b * K b)
    (fun b => mul_nonneg (ν.nonneg b) (hK0 b)) (C * D) (mul_nonneg hC hD) (by
      intro b
      calc
        _ ≤ ν.weight b * C := mul_le_mul_of_nonneg_left (hK b) (ν.nonneg b)
        _ ≤ D / (p : ℝ) ^ 6 * C := mul_le_mul_of_nonneg_right (hν b) hC
        _ = _ := by ring)
  convert h using 1
  ring

end Sarkozy.PartV.CoherentDictionary
