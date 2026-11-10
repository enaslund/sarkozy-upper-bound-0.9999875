module

public import Sarkozy.UpperCapsPaper.TableData
public import Sarkozy.F3Kernel.FullCertificateBound





@[expose] public section

open Finset

namespace Sarkozy.UpperCapsPaper

open Sarkozy Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

/-- **The nonstar form bound of LL20 from `Q` on** (`cor:extraction-leaf`(b)):
`|E_x[f(x) E_y[(∑_{S nonstar} ∏_{e ∈ S} χ_e(x, y)) h(y)]]| ≤ (∑_k C_k p^{-k/2}) ‖f‖ ‖h‖` on the
actual half law, at every prime `p ≥ Q` with Weil's bound and the four-cycle bound. -/
def NonstarFormBound (Q C₂ C₃ C₄ : ℝ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], WeilBound (ZMod p) → p ≠ 2 → FourCycleBound p → Q ≤ p →
    ∀ (hne : (injLabellings (ZMod p) SpectralD.Root.LL20.G).Nonempty)
      (f h : (SpectralD.Root.LL20.cut.Half → ZMod p) → ℝ),
      |(SpectralD.Root.LL20.halfLaw hne).expect (fun x => f x *
        (SpectralD.Root.LL20.halfLaw hne).expect (fun y =>
          (∑ S ∈ nonstars SpectralD.Root.LL20.crossPairs,
            ∏ e ∈ S, chiPair SpectralD.Root.LL20.sgn e x y) * h y))| ≤
        (C₂ * (√(p : ℝ))⁻¹ ^ 2 + C₃ * (√(p : ℝ))⁻¹ ^ 3 + C₄ * (√(p : ℝ))⁻¹ ^ 4) *
          √((SpectralD.Root.LL20.halfLaw hne).expect (fun x => f x ^ 2)) *
          √((SpectralD.Root.LL20.halfLaw hne).expect (fun x => h x ^ 2))

/-- The `j`-th row `(Q, C₂, C₃, C₄)` of the LL20 coefficient tables. -/
def ll20Row (j : Fin 19) : ℚ × ℚ × ℚ × ℚ := ll20Anchors.getD j.val (0, 0, 0, 0)

/-- **What the LL20 coefficient tables assert at the 19 anchors** (`cert:upper-root-caps`, first
item; `cor:extraction-leaf`(b)): the nonstar form bound with each row's coefficients from its
anchor on. *Hypothesis* (the paper's certificate; its finite core, the histogram sums, is replayed
by the repository's `special_coefficients.py` and its review). -/
def NonstarAnchorTables : Prop :=
  ∀ j : Fin 19, NonstarFormBound (ll20Row j).1 (ll20Row j).2.1 (ll20Row j).2.2.1 (ll20Row j).2.2.2

/-- The 19 anchors are increasing, from `2⁴⁷` to `2⁵²`, with nonnegative coefficients (kernel). -/
theorem ll20Anchors_sorted : ∀ j : Fin 19,
    (2 : ℚ) ^ 47 ≤ (ll20Row j).1 ∧ (ll20Row j).1 ≤ 2 ^ 52 ∧ 0 ≤ (ll20Row j).2.1 ∧
      0 ≤ (ll20Row j).2.2.1 ∧ 0 ≤ (ll20Row j).2.2.2 ∧
      (∀ i : Fin 19, i < j → (ll20Row i).1 < (ll20Row j).1) := by
  decide +kernel

/-- **An anchor serves every later point with larger coefficients.** -/
theorem NonstarFormBound.mono {Q C₂ C₃ C₄ Q' C₂' C₃' C₄' : ℝ} (h : NonstarFormBound Q C₂ C₃ C₄)
    (hQ : Q ≤ Q') (h₂ : C₂ ≤ C₂') (h₃ : C₃ ≤ C₃') (h₄ : C₄ ≤ C₄') :
    NonstarFormBound Q' C₂' C₃' C₄' := by
  intro p _ hW hp2 h4 hp hne f g
  refine (h p hW hp2 h4 (hQ.trans hp) hne f g).trans ?_
  have hr : 0 ≤ (√(p : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hpoly : C₂ * (√(p : ℝ))⁻¹ ^ 2 + C₃ * (√(p : ℝ))⁻¹ ^ 3 + C₄ * (√(p : ℝ))⁻¹ ^ 4 ≤
      C₂' * (√(p : ℝ))⁻¹ ^ 2 + C₃' * (√(p : ℝ))⁻¹ ^ 3 + C₄' * (√(p : ℝ))⁻¹ ^ 4 := by
    have a := mul_le_mul_of_nonneg_right h₂ (pow_nonneg hr 2)
    have b := mul_le_mul_of_nonneg_right h₃ (pow_nonneg hr 3)
    have c := mul_le_mul_of_nonneg_right h₄ (pow_nonneg hr 4)
    linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpoly (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

theorem nonstarFormBound_F3 :
    NonstarFormBound (2 ^ 60) (F3Kernel.coefficientCap20 2) (F3Kernel.coefficientCap20 3)
      (F3Kernel.coefficientCap20 4) := by
  intro p _ hW hp2 h4 hp hne f h
  have hp' : F3Kernel.productionAnchor ≤ p := by
    have : ((2 : ℕ) ^ 60 : ℝ) ≤ p := by exact_mod_cast hp
    unfold F3Kernel.productionAnchor
    exact_mod_cast this
  have key := F3Kernel.LL20_full_nonstar_bound hW hp2 h4 hp' hne f h
  have hpoly : F3Kernel.productionPolynomial F3Kernel.coefficientCap20 p =
      (F3Kernel.coefficientCap20 2 : ℝ) * (√(p : ℝ))⁻¹ ^ 2 +
        (F3Kernel.coefficientCap20 3 : ℝ) * (√(p : ℝ))⁻¹ ^ 3 +
        (F3Kernel.coefficientCap20 4 : ℝ) * (√(p : ℝ))⁻¹ ^ 4 := by
    unfold F3Kernel.productionPolynomial
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  rw [hpoly] at key
  exact key

end Sarkozy.UpperCapsPaper
