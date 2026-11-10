module

public import Sarkozy.OpsFeature.ExplicitT

@[expose] public section

/-!
# Non-vacuity of the block hypotheses of OPS-F

`MiddleBlock F b` (every prime `p ≡ 3 (mod 4)`, odd characteristic, least prime `b ≥ Q₃`) holds
for the one-prime block `𝔽_{19951627}` (`19951627` is the least prime `≡ 3 (mod 4)` above
`Q₃ = 19951586`; `prime_19951627` by `norm_num`), so `actual_feature_frame_proved` and
`actual_hcor_proved` apply to actual blocks (`frame_example`). The feature predicates are
satisfied by the zero family (`isFoldFeat_zero`) and, at an actual block, by the actual features.
-/

open Finset

namespace Sarkozy.OpsFeature

open Sarkozy.EnvelopeSteps Sarkozy.Envelopes

/-- `19951627` is prime. -/
theorem prime_19951627 : Nat.Prime 19951627 := by norm_num

instance fact_prime_19951627 : Fact (Nat.Prime 19951627) := ⟨prime_19951627⟩

/-- **`MiddleBlock` is satisfiable**: the one-prime block `𝔽_{19951627}`. -/
theorem middleBlock_example : MiddleBlock (fun _ : Unit => ZMod 19951627) 19951627 where
  hF _ := by rw [ZMod.ringChar_zmod_n]; norm_num
  h3 _ := by rw [ZMod.card]
  hb := by norm_num
  hbp _ := by rw [ZMod.card]; norm_num

/-- The zero family satisfies the feature predicates. -/
theorem isFoldFeat_zero {P : Type*} [Fintype P] [DecidableEq P] {F : P → Type*}
    [∀ p, Field (F p)] [∀ p, Fintype (F p)] [∀ p, DecidableEq (F p)] :
    IsFoldFeat (fun (_ : Fin 5) (_ : Tri F) => (0 : ℝ)) := by
  refine ⟨⟨0, by simp, fun _ => rfl⟩, ⟨0, by simp, fun _ => rfl⟩, ⟨0, by simp, fun _ => rfl⟩,
    ⟨⟨0, fun _ => rfl⟩, fun g => by simp [ipm], fun g => by simp [ipm]⟩,
    ⟨⟨0, fun _ => rfl⟩, fun g => by simp [ipm], fun g => by simp [ipm]⟩⟩

/-- The frame bound applies at the block `𝔽_{19951627}`. -/
theorem frame_example (h : Fin 5 → Tri (fun _ : Unit => ZMod 19951627) → ℝ) (hf : IsFoldFeat h) :
    ipm (fun x => ∑ i, h i x) (fun x => ∑ i, h i x) ≤ (gammaF : ℝ) * ∑ i, ipm (h i) (h i) :=
  actual_feature_frame_proved middleBlock_example h hf

end Sarkozy.OpsFeature
