module

public import Sarkozy.MeanCredit.Alloc
public import Sarkozy.MeanCredit.FamilyI

@[expose] public section

/-!
# The evaluation of the completed residual series: comparison and mean separately

`paper/sections/24a_joint_mean.tex`, `prop:joint-middle-mean` ("Its value is precisely the former
comparison bound minus the four displayed corrections"), `prop:joint-upper-mean`;
`paper/sections/32_four_routes_closing.tex`, `eq:final-joint-closing`.

The residual coefficient of a letter degree is `R(d) = 63 c(d) − m(d)`, with the comparison
coefficient `c` and the retained mean coefficient `m`. The paper evaluates the two completed series
separately in closed form (`𝓔 = B(e^S cosh A − 1) − D`, and `64 Δ_mid` from `eq:joint-alpha`,
`eq:joint-middle`), and the residual gates `63c − m ≥ 0` make their difference a bound for every
partial sum:

* **`seriesBound_of_hasSum`**: `R = 63c − m ≥ 0`, `∑_d c(d) X^d/d! = C`, `∑_d m(d) X^d/d! = M`
  give `SeriesBound R X (63 C − M)`;
* `SeriesBound.mono`: monotone in the bound;
* **`seriesBound_ledger`**: with `C ≤ 𝓔_h` and `M ≥ 64 Δ_mid^{ledger} − δ`, the bound of
  `allocJB_of_booking_upperFree`.

Of the mean series, family (i) is evaluated in closed form here (`FamilyI.hasSum_familyI`:
`64 Δ_α`). The comparison series and families (ii)–(iv) are the harness's evaluation.
-/

open Finset

namespace Sarkozy.MeanCredit

open Sarkozy.ClassData

variable {Λ : Type*} [Fintype Λ]

theorem SeriesBound.mono {R : (Λ → ℕ) → ℝ} {X : Λ → ℝ} {M M' : ℝ} (h : SeriesBound R X M)
    (hM : M ≤ M') : SeriesBound R X M' := fun Ds => (h Ds).trans hM

/-- **The completed residual series from the two completed series** (`prop:joint-middle-mean`):
if the residual coefficients `63 c − m` are nonnegative and the completed comparison and mean
series have sums `C` and `M`, every partial sum of the residual series is at most `63 C − M`. -/
theorem seriesBound_of_hasSum (c m : (Λ → ℕ) → ℝ) (X : Λ → ℝ) (hX : ∀ l, 0 ≤ X l)
    (hres : ∀ d, 0 ≤ 63 * c d - m d) (C M : ℝ)
    (hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) C)
    (hM : HasSum (fun d => m d * ∏ l, X l ^ d l / (d l).factorial) M) :
    SeriesBound (fun d => 63 * c d - m d) X (63 * C - M) := by
  intro Ds
  have h := (hC.mul_left 63).sub hM
  have e : (fun d => 63 * (c d * ∏ l, X l ^ d l / (d l).factorial) -
      m d * ∏ l, X l ^ d l / (d l).factorial) =
      fun d => (63 * c d - m d) * ∏ l, X l ^ d l / (d l).factorial := by
    funext d
    ring
  rw [e] at h
  refine sum_le_hasSum Ds (fun d _ => ?_) h
  exact mul_nonneg (hres d) (prod_nonneg fun l _ => div_nonneg (pow_nonneg (hX l) _)
    (Nat.cast_nonneg _))

/-- **The evaluation at the ledger's room** (`eq:final-joint-closing` without `Δ_u − R_u`): a
completed comparison series at most the harness's `𝓔_h` and a completed mean series at least
`64 Δ_mid^{ledger} − δ` give the bound of `allocJB_of_booking_upperFree`. -/
theorem seriesBound_ledger (c m : (Λ → ℕ) → ℝ) (X : Λ → ℝ) (hX : ∀ l, 0 ≤ X l)
    (hres : ∀ d, 0 ≤ 63 * c d - m d) (C M δ : ℝ)
    (hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) C)
    (hM : HasSum (fun d => m d * ∏ l, X l ^ d l / (d l).factorial) M)
    (hCv : C ≤ harnessE) (hMv : 64 * (ledgerMid : ℝ) - δ ≤ M) :
    SeriesBound (fun d => 63 * c d - m d) X (63 * (harnessE : ℝ) - 64 * (ledgerMid : ℝ) + δ) :=
  (seriesBound_of_hasSum c m X hX hres C M hC hM).mono (by linarith)

/-! ## Family (i) at the letter level -/

section FamilyLetters

variable [DecidableEq Λ]

/-- The letter degree `2·F + j·O` of a family-(i) term: a selected fold pair (letter `F`, raw
coordinate `x_B = 2α_B`) and `j` outside `𝖤` factors (letter `O`). -/
def degFI (F O : Λ) (j : ℕ) : Λ → ℕ := fun l => if l = F then 2 else if l = O then j else 0

/-- **Family (i)'s mean coefficient of a letter degree**: `4/(H² C(j+2,2))` on `2·F + j·O`, `0`
elsewhere (`prop:joint-middle-mean`, family (i)). -/
noncomputable def meanFI (H : ℝ) (F O : Λ) (d : Λ → ℕ) : ℝ :=
  if d = degFI F O (d O) then 4 / (H ^ 2 * (Nat.choose (d O + 2) 2 : ℝ)) else 0

omit [Fintype Λ] in
theorem degFI_O {F O : Λ} (hFO : F ≠ O) (j : ℕ) : degFI F O j O = j := by
  simp [degFI, hFO.symm]

omit [Fintype Λ] in
theorem degFI_injective {F O : Λ} (hFO : F ≠ O) : Function.Injective (degFI F O) := by
  intro j j' h
  have := congrFun h O
  rwa [degFI_O hFO, degFI_O hFO] at this

theorem prod_degFI {F O : Λ} (hFO : F ≠ O) (X : Λ → ℝ) (j : ℕ) :
    ∏ l, X l ^ degFI F O j l / (degFI F O j l).factorial =
      (X F ^ 2 / 2) * (X O ^ j / j.factorial) := by
  rw [← prod_subset (subset_univ {F, O}) fun l _ hl => ?_, prod_pair hFO]
  · simp [degFI, hFO.symm]
  · have h1 : l ≠ F := fun h => hl (by simp [h])
    have h2 : l ≠ O := fun h => hl (by simp [h])
    simp [degFI, h1, h2]

/-- **Family (i), completed at the letter level, is `64 Δ_α`** (`eq:joint-alpha`): with letter
totals `x = X_F` (the raw-arm total) and `w = X_O` (the `𝖤` assignment), the series
`∑_d meanFI(d) ∏_l X_l^{d_l}/d_l!` has sum `64 · x²/(16 H²) · (e^w − 1 − w)/w²`. -/
theorem hasSum_meanFI (H : ℝ) (hH : H ≠ 0) {F O : Λ} (hFO : F ≠ O) (X : Λ → ℝ) (hw : X O ≠ 0) :
    HasSum (fun d => meanFI H F O d * ∏ l, X l ^ d l / (d l).factorial)
      (64 * (X F ^ 2 / (16 * H ^ 2) * ((Real.exp (X O) - 1 - X O) / X O ^ 2))) := by
  have h := hasSum_familyI H (X F) (X O) hH hw
  rw [← (degFI_injective hFO).hasSum_iff]
  · convert h using 1
    funext j
    simp only [Function.comp, meanFI, degFI_O hFO, ↓reduceIte, prod_degFI hFO]
    ring
  · intro d hd
    have hne : d ≠ degFI F O (d O) := fun h' => hd ⟨d O, h'.symm⟩
    simp [meanFI, hne]

end FamilyLetters

end Sarkozy.MeanCredit
