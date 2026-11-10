module

public import Sarkozy.SpectralD.SmallFast.Residuals

/-!
# The test checks of the smaller cuts as computations on codes

`TestChecks c` contains the half sum `∑ k, modelD c a k i * modelD c a k j`. Through the
code `code c` it is a dot product of two columns of the model table (`sum_entry_mul_col`),
and `testChecks_of` assembles `TestChecks c` from a check on codes. No evaluation happens in
this file.
-/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Finset Sarkozy.PartVLaws.FieldGraphs Sarkozy.SpectralC

/-- The table of `modelD c a`. -/
def dTable (c : SmallCut) (a : Fin 2) : List (List ℤ) :=
  if a = 0 then crossTable c else signTable c

/-- The table of `modelH c a`. -/
def hTable (c : SmallCut) (a : Fin 2) : List (List ℤ) :=
  if a = 0 then plusOneTable c else gramThreeTable c

/-- The test checks of `TestChecks` at the codes `x`, `y`. -/
def TestCode (c : SmallCut) (a : Fin 2) (e : Fin 3) (x y : ℕ) : Prop :=
  entry (testRealTable c a e) x y = (if x = y then base c else 0) +
      (if a = 0 then char e * linear c * entry (dTable c a) x y else 0) +
      100000000 * char e ^ 2 * dotZ (colOf (dTable c a) x) (colOf (dTable c a) y) -
      100000000 * entry (hTable c a) x y ∧
    entry (testImagTable c a e) x y =
      (if a = 0 then 0 else char e * linear c * entry (dTable c a) x y)

instance (c : SmallCut) (a : Fin 2) (e : Fin 3) (x y : ℕ) : Decidable (TestCode c a e x y) := by
  unfold TestCode; infer_instance

section Bridge

variable (c : SmallCut) (n : ℕ)
  (hlt : ∀ h : c.data.cut.Half, code c h.1 < n)
  (honto : ∀ x, x < n → ∃ h : c.data.cut.Half, code c h.1 = x)
  (hinj : ∀ h₁ h₂ : c.data.cut.Half, code c h₁.1 = code c h₂.1 → h₁ = h₂)

include hlt honto hinj

theorem sum_entry_mul_col (T : List (List ℤ)) (hT : T.length = n) (x y : ℕ) :
    ∑ k : c.data.cut.Half, entry T (code c k.1) x * entry T (code c k.1) y =
      dotZ (colOf T x) (colOf T y) := by
  have h := sum_half_eq_range c n hlt honto hinj (fun k => entry T k x * entry T k y)
  rw [h, dotZ_eq_sum _ _ n ((length_colOf _ _).trans hT).le]
  simp only [getD_colOf]

theorem testChecks_of (hlen : ∀ a, (dTable c a).length = n)
    (hcode : ∀ a e, ∀ x, x < n → ∀ y, y < n → TestCode c a e x y) : TestChecks c := by
  intro a e i j
  have h := hcode a e _ (hlt i) _ (hlt j)
  unfold TestCode at h
  have hd : modelD c a = atTable c (dTable c a) := rfl
  have hh : modelH c a = atTable c (hTable c a) := rfl
  simp only [testReal, testImag, hd, hh, atTable]
  rw [sum_entry_mul_col c n hlt honto hinj _ (hlen a)]
  have hif : (if i = j then base c else 0) =
      (if code c i.1 = code c j.1 then base c else 0) := by
    by_cases hij : i = j
    · subst hij
      simp
    · have h2 : code c i.1 ≠ code c j.1 := fun h' => hij (hinj i j h')
      simp only [hij, h2, ite_false]
  rw [hif]
  exact h

end Bridge

end Sarkozy.SpectralD.SmallMatrices
