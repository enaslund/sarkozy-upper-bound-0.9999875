module

public import Sarkozy.UpperReference.ObservedSchur

/-!
# `prop:observed-caps`: the Schur test of the full star matrix of EL22

`paper/sections/25_upper_reference.tex`, `prop:observed-caps`, "Schur tests": the full complete
star matrix of the layer cut EL22 (eighteen singletons, `162` supports) satisfies
`k²I - B_⋆B_⋆ᵀ ± i k D ⪰ 0` with `k = 6`, which by `rem:realified-gates` gives `‖M(±i)‖ ≤ 6`.

* `gram`: `(B_⋆B_⋆ᵀ)_{jj'} = ∑_{S ∈ supports} (B_⋆)_{jS} (B_⋆)_{j'S}`, with the paper's
  `(B_⋆)_{j,S} = (-1)^{|S|} ∏_{i∈S} D_{ji}` (`Observed.starB`) over the `162` supports;
  `gram_eq`: it is the explicit integer matrix `gramMat` (diagonal `11`, four off-diagonal ones
  in every row), by `decide`.
* `gram_sos`: `2(15I - B_⋆B_⋆ᵀ) = NᵀN` for the incidence matrix `N` of the off-diagonal ones,
  so `B_⋆B_⋆ᵀ ⪯ 15 I`.
* `Dfull_sq`, `pMat_sq`, `pMat_sos`: `P = -D² = DᵀD` satisfies `3A² + 4B² = 324(12I - P)` with
  `A = P² - 15P + 36I`, `B = P² - 12P` (the eigenvalues of `P` are `0, 3, 12`), so `P ⪯ 12 I`
  and `‖D‖ = 2√3`.
* `full_schur_test`: **the test holds exactly for both signs**:
  `36I - B_⋆B_⋆ᵀ ± 6iD = (15I - B_⋆B_⋆ᵀ) + 6(αI ∓ iD) + (21 - 6α)I` with `α = 17321/5000 ≥ 2√3`,
  `αI - Y = (Y - α)²/(2α) + (α² - 12)/(2α) I + (12I - P)/(2α)` for `Y = ±iD`, and
  `21 - 6α ≈ 0.2148 > 0`.

The step from the test to the norm bound (`rem:realified-gates`) is `ObservedGates.lean`
(`full_gates`) and `ObservedNorm.lean` (`full_normLe`).
-/

@[expose] public section

open scoped Matrix ComplexOrder ComplexConjugate
open Matrix Finset

namespace Sarkozy.UpperReference.Observed

/-- The code `6a + b` of a label `(a, b)`. -/
def code (u : Half) : Fin 18 :=
  ⟨6 * u.1.val + u.2.val, by have := u.1.isLt; have := ZMod.val_lt u.2; omega⟩

def gramTab : Fin 18 → Fin 18 → ℤ :=
  ![![11, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 11, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![1, 0, 11, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 11, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 0, 1, 0, 11, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0],
    ![0, 1, 0, 1, 0, 11, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 0, 11, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 11, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 1, 0, 11, 0, 1, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 1, 0, 11, 0, 1, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 11, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 11, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 11, 0, 1, 0, 1, 0],
    ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 11, 0, 1, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 11, 0, 1, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 11, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 11, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 11]]

def pTab : Fin 18 → Fin 18 → ℤ :=
  ![![4, 0, -2, 0, -2, 0, 2, 0, -1, 0, -1, 0, 2, 0, -1, 0, -1, 0],
    ![0, 4, 0, -2, 0, -2, 0, 2, 0, -1, 0, -1, 0, 2, 0, -1, 0, -1],
    ![-2, 0, 4, 0, -2, 0, -1, 0, 2, 0, -1, 0, -1, 0, 2, 0, -1, 0],
    ![0, -2, 0, 4, 0, -2, 0, -1, 0, 2, 0, -1, 0, -1, 0, 2, 0, -1],
    ![-2, 0, -2, 0, 4, 0, -1, 0, -1, 0, 2, 0, -1, 0, -1, 0, 2, 0],
    ![0, -2, 0, -2, 0, 4, 0, -1, 0, -1, 0, 2, 0, -1, 0, -1, 0, 2],
    ![2, 0, -1, 0, -1, 0, 4, 0, -2, 0, -2, 0, 2, 0, -1, 0, -1, 0],
    ![0, 2, 0, -1, 0, -1, 0, 4, 0, -2, 0, -2, 0, 2, 0, -1, 0, -1],
    ![-1, 0, 2, 0, -1, 0, -2, 0, 4, 0, -2, 0, -1, 0, 2, 0, -1, 0],
    ![0, -1, 0, 2, 0, -1, 0, -2, 0, 4, 0, -2, 0, -1, 0, 2, 0, -1],
    ![-1, 0, -1, 0, 2, 0, -2, 0, -2, 0, 4, 0, -1, 0, -1, 0, 2, 0],
    ![0, -1, 0, -1, 0, 2, 0, -2, 0, -2, 0, 4, 0, -1, 0, -1, 0, 2],
    ![2, 0, -1, 0, -1, 0, 2, 0, -1, 0, -1, 0, 4, 0, -2, 0, -2, 0],
    ![0, 2, 0, -1, 0, -1, 0, 2, 0, -1, 0, -1, 0, 4, 0, -2, 0, -2],
    ![-1, 0, 2, 0, -1, 0, -1, 0, 2, 0, -1, 0, -2, 0, 4, 0, -2, 0],
    ![0, -1, 0, 2, 0, -1, 0, -1, 0, 2, 0, -1, 0, -2, 0, 4, 0, -2],
    ![-1, 0, -1, 0, 2, 0, -1, 0, -1, 0, 2, 0, -2, 0, -2, 0, 4, 0],
    ![0, -1, 0, -1, 0, 2, 0, -1, 0, -1, 0, 2, 0, -2, 0, -2, 0, 4]]

def qTab : Fin 18 → Fin 18 → ℤ :=
  ![![36, 0, -18, 0, -18, 0, 30, 0, -15, 0, -15, 0, 30, 0, -15, 0, -15, 0],
    ![0, 36, 0, -18, 0, -18, 0, 30, 0, -15, 0, -15, 0, 30, 0, -15, 0, -15],
    ![-18, 0, 36, 0, -18, 0, -15, 0, 30, 0, -15, 0, -15, 0, 30, 0, -15, 0],
    ![0, -18, 0, 36, 0, -18, 0, -15, 0, 30, 0, -15, 0, -15, 0, 30, 0, -15],
    ![-18, 0, -18, 0, 36, 0, -15, 0, -15, 0, 30, 0, -15, 0, -15, 0, 30, 0],
    ![0, -18, 0, -18, 0, 36, 0, -15, 0, -15, 0, 30, 0, -15, 0, -15, 0, 30],
    ![30, 0, -15, 0, -15, 0, 36, 0, -18, 0, -18, 0, 30, 0, -15, 0, -15, 0],
    ![0, 30, 0, -15, 0, -15, 0, 36, 0, -18, 0, -18, 0, 30, 0, -15, 0, -15],
    ![-15, 0, 30, 0, -15, 0, -18, 0, 36, 0, -18, 0, -15, 0, 30, 0, -15, 0],
    ![0, -15, 0, 30, 0, -15, 0, -18, 0, 36, 0, -18, 0, -15, 0, 30, 0, -15],
    ![-15, 0, -15, 0, 30, 0, -18, 0, -18, 0, 36, 0, -15, 0, -15, 0, 30, 0],
    ![0, -15, 0, -15, 0, 30, 0, -18, 0, -18, 0, 36, 0, -15, 0, -15, 0, 30],
    ![30, 0, -15, 0, -15, 0, 30, 0, -15, 0, -15, 0, 36, 0, -18, 0, -18, 0],
    ![0, 30, 0, -15, 0, -15, 0, 30, 0, -15, 0, -15, 0, 36, 0, -18, 0, -18],
    ![-15, 0, 30, 0, -15, 0, -15, 0, 30, 0, -15, 0, -18, 0, 36, 0, -18, 0],
    ![0, -15, 0, 30, 0, -15, 0, -15, 0, 30, 0, -15, 0, -18, 0, 36, 0, -18],
    ![-15, 0, -15, 0, 30, 0, -15, 0, -15, 0, 30, 0, -18, 0, -18, 0, 36, 0],
    ![0, -15, 0, -15, 0, 30, 0, -15, 0, -15, 0, 30, 0, -18, 0, -18, 0, 36]]


/-- `B_⋆B_⋆ᵀ`, from the paper's definition over the `162` supports. -/
def gram (j j' : Half) : ℤ := ∑ S ∈ supports, starB j S * starB j' S

/-- The explicit matrix of `B_⋆B_⋆ᵀ`. -/
def gramMat : Matrix Half Half ℤ := fun u v => gramTab (code u) (code v)

/-- `P = -D²`, explicitly. -/
def pMat : Matrix Half Half ℤ := fun u v => pTab (code u) (code v)

/-- `P²`, explicitly. -/
def qMat : Matrix Half Half ℤ := fun u v => qTab (code u) (code v)

/-- **`B_⋆B_⋆ᵀ` is the explicit matrix** (diagonal `11`; four off-diagonal ones per row). -/
theorem gram_eq : ∀ j j' : Half, gram j j' = gramTab (code j) (code j') := by
  decide +kernel

/-- The incidence matrix of the off-diagonal ones of `B_⋆B_⋆ᵀ`, indexed by ordered pairs. -/
def nMat : Matrix (Half × Half) Half ℤ := fun e u =>
  if e.1 ≠ e.2 ∧ gramMat e.1 e.2 = 1 then (if u = e.1 then 1 else 0) - (if u = e.2 then 1 else 0)
  else 0

/-- **`2(15I - B_⋆B_⋆ᵀ) = NᵀN`.** -/
theorem gram_sos : nMat.transpose * nMat = 2 • (15 • (1 : Matrix Half Half ℤ) - gramMat) := by
  decide +kernel

/-- `D` as a matrix. -/
def Dfull : Matrix Half Half ℤ := fun u v => crossD u v

/-- **`D² = -P`.** -/
theorem Dfull_sq : Dfull * Dfull = -pMat := by
  decide +kernel

/-- **`P² = Q`.** -/
theorem pMat_sq : pMat * pMat = qMat := by
  decide +kernel

/-- `A = P² - 15P + 36I` and `B = P² - 12P`. -/
def aMat : Matrix Half Half ℤ := qMat - 15 • pMat + 36 • (1 : Matrix Half Half ℤ)
def bMat : Matrix Half Half ℤ := qMat - 12 • pMat

/-- **`3A² + 4B² = 324(12I - P)`**: the eigenvalues of `P` lie in `{0, 3, 12}`. -/
theorem pMat_sos : 3 • (aMat * aMat) + 4 • (bMat * bMat) =
    324 • (12 • (1 : Matrix Half Half ℤ) - pMat) := by
  decide +kernel

theorem aMat_symm : aMat.transpose = aMat := by
  decide +kernel

theorem bMat_symm : bMat.transpose = bMat := by
  decide +kernel

theorem Dfull_anti : ∀ a b, Dfull b a = -Dfull a b := fun a b => crossD_antisymm a b

end Sarkozy.UpperReference.Observed
