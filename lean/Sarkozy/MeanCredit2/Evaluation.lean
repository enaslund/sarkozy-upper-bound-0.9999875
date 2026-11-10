module

public import Sarkozy.MeanCredit2.MeanValue

@[expose] public section





open Finset

namespace Sarkozy.MeanCredit2

open Sarkozy.ClassData Sarkozy.MeanCredit

variable {C : Type} [Fintype C]

/-- The mean letters of a degree. -/
def toM (d : MLetter ⊕ C → ℕ) : MLetter → ℕ := fun l => d (.inl l)

/-- The `𝖤` share of the outside mass, `r = 1/(1 + ρ_H)`. -/
noncomputable def rH : ℝ := ((1 / (1 + rhoHq) : ℚ) : ℝ)

/-- A degree carried by the mean letters. -/
def ofM (d : MLetter → ℕ) : MLetter ⊕ C → ℕ := Sum.elim d 0

/-- **The paper's middle mean coefficient on `MLetter ⊕ C`**: `mPaper` on the degrees carried by
the mean letters, `0` elsewhere. -/
noncomputable def mLift (d : MLetter ⊕ C → ℕ) : ℝ :=
  if d = ofM (toM d) then mPaper rH (toM d) else 0

omit [Fintype C] in
theorem ofM_injective : Function.Injective (ofM (C := C)) := by
  intro d d' h
  funext l
  exact congrFun h (.inl l)

/-- **The completed mean series on `MLetter ⊕ C`** (`prop:joint-middle-mean`): with the mean
letters at the totals `x` (`F`, `E`), `V` (`I`), `U − V` (`G`), `0` (`O`, `K`). -/
theorem hasSum_mLift (x U V : ℝ) (hV : 0 ≤ V) (hVU : V ≤ U) (hw : rH * U ≠ 0)
    (X : MLetter ⊕ C → ℝ) (hX : ∀ l, X (.inl l) = mTot x 0 0 V (U - V) l) :
    HasSum (fun d => mLift d * ∏ l, X l ^ d l / (d l).factorial)
      (meanValue x (rH * U) ((sigmaQ : ℝ) * x) U V) := by
  have hr : 0 ≤ rH := by unfold rH; norm_num [rhoHq]
  rw [← (ofM_injective (C := C)).hasSum_iff]
  · convert hasSum_mPaper rH hr x U V hV hVU hw using 1
    funext d
    have e1 : toM (ofM (C := C) d) = d := rfl
    simp only [Function.comp, mLift, e1, ↓reduceIte, Fintype.prod_sum_type]
    have e2 : ∏ c : C, X (.inr c) ^ (ofM (C := C) d (.inr c)) /
        ((ofM (C := C) d (.inr c)).factorial : ℝ) = 1 :=
      prod_eq_one fun c _ => by simp [ofM]
    rw [e2, mul_one]
    congr 1
    exact prod_congr rfl fun l _ => by rw [hX]; rfl
  · intro d hd
    have hne : d ≠ ofM (toM d) := fun h' => hd ⟨toM d, h'.symm⟩
    simp [mLift, hne]

/-- **The evaluation at the paper's mean coefficient** (`eq:final-joint-closing` without
`Δ_u − R_u`): the mean side is kernel-checked at E3's v2 totals; the comparison side is the
hypothesis `hC`, `hCv`. -/
theorem seriesBound_paper (c : (MLetter ⊕ C → ℕ) → ℝ) (X : MLetter ⊕ C → ℝ)
    (hX0 : ∀ l, 0 ≤ X l) (hXm : ∀ l, X (.inl l) = mTot xq 0 0 Vq (Uq - Vq) l)
    (hres : ∀ d, 0 ≤ 63 * c d - mLift d) (Cv τ : ℝ)
    (hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv)
    (hCv : Cv ≤ harnessE + τ) :
    SeriesBound (fun d => 63 * c d - mLift d) X
      (63 * (harnessE : ℝ) - 64 * (ledgerMid : ℝ) + (63 * τ - 4 / 10 ^ 11)) := by
  have hw : rH * (Uq : ℝ) ≠ 0 := by unfold rH; norm_num [Uq, rhoHq]
  have hM := hasSum_mLift (xq : ℝ) Uq Vq (by norm_num [Vq]) (by norm_num [Vq, Uq]) hw X hXm
  have e1 : rH * (Uq : ℝ) = (wq : ℝ) := by unfold rH; push_cast [wq]; ring
  have e2 : (sigmaQ : ℝ) * (xq : ℝ) = (yq : ℝ) := by push_cast [yq]; ring
  rw [e1, e2] at hM
  refine (seriesBound_of_hasSum c mLift X hX0 hres Cv _ hC hM).mono ?_
  have := meanValue_ge
  linarith

end Sarkozy.MeanCredit2
