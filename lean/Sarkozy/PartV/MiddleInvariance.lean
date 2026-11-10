module

public import Sarkozy.PartV.CoherentRP

@[expose] public section

/-!
# The middle reference is invariant under the slot reflections `R_h`

`lem:oct24:invariant-background`(i).

`paper/sections/23_envelopes.tex`, `lem:oct24:invariant-background`(i) and the definition of
`R_h` in `lem:reflection-averaging`: `R_h(u₀, u₁, ℓ) = (h - u₀, u₁, ℓ)`, `h ∈ {1, 3, 5}`; these
are `g6 3, g6 4, g6 5` of `Sarkozy.FiveType`. More generally the middle law is invariant under
every `g ∈ 𝒢₆` acting on the first chamber coordinate (`middleTilde_g6_inv`,
`middleReference_g6_inv`), for every choice of the completion weights, because it is the
push-forward of two `𝒢₆`-invariant five-type measures (`middleTilde_eq`, `Datum.Q_inv6`).

For the paper's block laws this holds on all 33 pieces: uniform root
(`middleBlockReference_uniform_Rinv`), individual-square root
(`middleBlockReference_individual_Rinv`), coherent root of an invariant dictionary
(`middleBlockReference_coherent_Rinv`).
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings Sarkozy.FiveType

/-- The action of `g6 k` on the first chamber coordinate of the slots. -/
def slotG (k : Fin 6) (v : Slot) : Slot := (g6 k v.1, v.2.1, v.2.2)

/-- `R_h = slotG k` for `(h, k) = (1, 3), (3, 4), (5, 5)`. -/
theorem slotG_reflections (v : Slot) :
    slotG 3 v = (1 - v.1, v.2.1, v.2.2) ∧ slotG 4 v = (3 - v.1, v.2.1, v.2.2) ∧
      slotG 5 v = (5 - v.1, v.2.1, v.2.2) := by
  obtain ⟨u, w, l⟩ := v
  refine ⟨?_, ?_, ?_⟩ <;> simp only [slotG, Prod.mk.injEq, and_true] <;> revert u <;> decide

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **The middle law is `𝒢₆`-invariant on the first coordinate**, for every choice of weights. -/
theorem middleTilde_g6_inv (F : MiddleFieldLaws X)
    (h₂ : DatumHyp (F.two .E) (F.two .F) (F.two .L))
    (h₁ : DatumHyp (F.one .E) (F.one .F) (F.one .L))
    (W : MiddleWeights) (r : ℝ) (k : Fin 6) (f : (Slot → X) → ℝ) :
    middleTilde F W r (fun z => f (z ∘ slotG k)) = middleTilde F W r f := by
  rw [middleTilde_eq F h₂ h₁, LinearMap.add_apply, LinearMap.add_apply, pushL_apply, pushL_apply,
    pushL_apply, pushL_apply]
  congr 1
  · exact (fieldDatum h₂).Q_inv6 (twoCoeff W r) k (fun Ψ => f (toSlot₂ Ψ))
  · exact (fieldDatum h₁).Q_inv6 (oneCoeff W r) k (fun Ψ => f (toSlot₁ Ψ))

/-- The normalized middle law is `𝒢₆`-invariant on the first coordinate. -/
theorem middleReference_g6_inv (F : MiddleFieldLaws X)
    (h₂ : DatumHyp (F.two .E) (F.two .F) (F.two .L))
    (h₁ : DatumHyp (F.one .E) (F.one .F) (F.one .L))
    (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) (k : Fin 6) (f : (Slot → X) → ℝ) :
    (middleReference F W hr).expect (fun z => f (z ∘ slotG k)) =
      (middleReference F W hr).expect f := by
  rw [FiniteLaw.expect_eq_signedIntegral, FiniteLaw.expect_eq_signedIntegral, middleReference_eq,
    LinearMap.smul_apply, LinearMap.smul_apply, middleTilde_g6_inv F h₂ h₁]

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **`lem:oct24:invariant-background`(i), uniform root**: the middle block law is invariant under
`R_1, R_3, R_5` (and all of `𝒢₆`), for every choice of weights. -/
theorem middleBlockReference_uniform_Rinv (hne : MiddleNonempty pr) (W : MiddleWeights) {r : ℝ}
    (hr : 0 ≤ r) (k : Fin 6) (f : (Slot → BlockLabel pr) → ℝ) :
    (middleBlockReference pr hne (uniformRoot pr hne) W hr).expect (fun z => f (z ∘ slotG k)) =
      (middleBlockReference pr hne (uniformRoot pr hne) W hr).expect f :=
  middleReference_g6_inv (middleBlockFieldLaws pr hne (uniformRoot pr hne))
    (middleBlock_datumHyp₂ pr hne) (middleBlock_datumHyp₁ pr hne) W hr k f

/-- The same with the individual-square root. -/
theorem middleBlockReference_individual_Rinv (hne : MiddleNonempty pr) (u : ℚ) (W : MiddleWeights)
    {r : ℝ} (hr : 0 ≤ r) (k : Fin 6) (f : (Slot → BlockLabel pr) → ℝ) :
    (middleBlockReference pr hne (individualBlockRoot pr u hne.L2) W hr).expect
        (fun z => f (z ∘ slotG k)) =
      (middleBlockReference pr hne (individualBlockRoot pr u hne.L2) W hr).expect f :=
  middleReference_g6_inv (middleBlockFieldLaws pr hne (individualBlockRoot pr u hne.L2))
    (middleBlock_datumHyp₂_individual pr hne u) (middleBlock_datumHyp₁ pr hne) W hr k f

/-- The same with the coherent root of an invariant dictionary. -/
theorem middleBlockReference_coherent_Rinv (hne : MiddleNonempty pr) (D : Dictionary)
    (hD : D.Invariant) (u : ℚ) {η : ℚ} (hη : 0 < η) (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r)
    (k : Fin 6) (f : (Slot → BlockLabel pr) → ℝ) :
    (middleBlockReference pr hne (coherentBlockRoot pr D u hη hne.L2) W hr).expect
        (fun z => f (z ∘ slotG k)) =
      (middleBlockReference pr hne (coherentBlockRoot pr D u hη hne.L2) W hr).expect f :=
  middleReference_g6_inv (middleBlockFieldLaws pr hne (coherentBlockRoot pr D u hη hne.L2))
    (middleBlock_datumHyp₂_coherent pr hne D hD u hη) (middleBlock_datumHyp₁ pr hne) W hr k f

end Block

end Sarkozy.PartV
