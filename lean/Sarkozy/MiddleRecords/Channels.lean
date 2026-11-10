module

public import Sarkozy.TraceMixing.Paley

/-!
# Halves, kernels and the Paley channels (`subsec:middle-records:notation`)

`paper/sections/21_middle_records.tex`, `subsec:middle-records:notation`, the paragraphs
"Halves and kernels" and "The Paley channels", `eq:middle:channels` and `eq:middle:transpose`.

Over a finite field `F` with `|F| ≡ 3 (mod 4)`, so that `χ(-1) = -1` and `a → b :⇔ χ(b - a) = 1`
is a tournament, a *half* is a triple of labels `x = (x₀, x₁, x₂)` (`Half F = Fin 3 → F`) and a
*kernel* is a real function on pairs of halves (`Ker F`). Kernels form a commutative ring under
pointwise operations (the `Pi` instances), and the reserved reflection acts by the transpose
`K^⊤(x, y) = K(y, x)` (`kerT`), a ring automorphism. The cross characters
(`eq:middle:channels`) are
`𝖠 = χ(y₂ - x₀)`, `𝖡 = χ(x₂ - y₀)`, `𝖢 = χ(y₀ - x₁)`, `𝖣 = χ(y₁ - x₀)` (`chA`, …, `chD`), and
(`eq:middle:transpose`) `(𝖠, 𝖡, 𝖢, 𝖣)^⊤ = (𝖡, 𝖠, -𝖣, -𝖢)` (`chA_swap`, …, `chD_swap`; the last
two use `χ(-1) = -1`). `I_×` (`Icross`) is the indicator that `x` and `y` have no common label,
and it is symmetric (`Icross_swap`).

The kernels are defined at every pair of halves, as in the paper; a channel whose two labels
coincide vanishes there (`χ 0 = 0`). The restriction to `H_F` (halves with `x₀ → x₂`) only enters
through the measure `ν_F`, which is not needed for the identities of this file and of
`Sarkozy.MiddleRecords.Mirror`.
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Sarkozy.TraceMixing

/-- A half: a triple `(x₀, x₁, x₂)` of labels. -/
abbrev Half (F : Type*) := Fin 3 → F

/-- A kernel: a real function on pairs of halves `(x, y)`. -/
abbrev Ker (F : Type*) := Half F → Half F → ℝ

section Generic

variable {F : Type*}

/-- The transpose `K^⊤(x, y) = K(y, x)` (the action of the reserved reflection). -/
def kerT (K : Ker F) : Ker F := fun x y => K y x

/-- `Sym K = (K + K^⊤)/2`. -/
noncomputable def kSym (K : Ker F) : Ker F := fun x y => (K x y + K y x) / 2

/-- `Skew K = (K - K^⊤)/2`. -/
noncomputable def kSkew (K : Ker F) : Ker F := fun x y => (K x y - K y x) / 2

theorem kSym_apply (K : Ker F) (x y : Half F) : kSym K x y = (K x y + K y x) / 2 := rfl

theorem kSkew_apply (K : Ker F) (x y : Half F) : kSkew K x y = (K x y - K y x) / 2 := rfl

theorem kerT_apply (K : Ker F) (x y : Half F) : kerT K x y = K y x := rfl

/-- The transpose is a ring automorphism of the kernels. -/
theorem kerT_mul (K L : Ker F) : kerT (K * L) = kerT K * kerT L := rfl

theorem kerT_add (K L : Ker F) : kerT (K + L) = kerT K + kerT L := rfl

theorem kerT_kerT (K : Ker F) : kerT (kerT K) = K := rfl

/-- `I_×`, the indicator that `x` and `y` have no common label. -/
noncomputable def Icross [DecidableEq F] : Ker F := fun x y => if ∀ i j, x i ≠ y j then 1 else 0

/-- **`I_×^⊤ = I_×`.** -/
theorem Icross_swap [DecidableEq F] (x y : Half F) : Icross (F := F) y x = Icross x y := by
  unfold Icross
  have h : (∀ i j, y i ≠ x j) ↔ (∀ i j, x i ≠ y j) :=
    ⟨fun h i j hij => h j i hij.symm, fun h i j hij => h j i hij.symm⟩
  simp only [h]

end Generic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer-valued character. -/
local notation "χ" => quadraticChar F

/-- The channel `𝖠 = χ(y₂ - x₀)` (`eq:middle:channels`): `𝖠 = 1` means `x₀ → y₂`. -/
def chA : Ker F := fun x y => (χ (y 2 - x 0) : ℝ)

/-- The channel `𝖡 = χ(x₂ - y₀)`: `𝖡 = 1` means `y₀ → x₂`. -/
def chB : Ker F := fun x y => (χ (x 2 - y 0) : ℝ)

/-- The channel `𝖢 = χ(y₀ - x₁)`: `𝖢 = 1` means `x₁ → y₀`. -/
def chC : Ker F := fun x y => (χ (y 0 - x 1) : ℝ)

/-- The channel `𝖣 = χ(y₁ - x₀)`: `𝖣 = 1` means `x₀ → y₁`. -/
def chD : Ker F := fun x y => (χ (y 1 - x 0) : ℝ)


/-- **`eq:middle:transpose`, `𝖠^⊤ = 𝖡`.** -/
theorem chA_swap (x y : Half F) : chA (F := F) y x = chB x y := rfl

/-- **`eq:middle:transpose`, `𝖡^⊤ = 𝖠`.** -/
theorem chB_swap (x y : Half F) : chB (F := F) y x = chA x y := rfl

/-- **`eq:middle:transpose`, `𝖢^⊤ = -𝖣`** (uses `χ(-1) = -1`). -/
theorem chC_swap (h3 : Fintype.card F % 4 = 3) (x y : Half F) : chC y x = -chD x y := by
  simp only [chC, chD, chi_swap h3 (x 0) (y 1), Int.cast_neg]

/-- **`eq:middle:transpose`, `𝖣^⊤ = -𝖢`** (uses `χ(-1) = -1`). -/
theorem chD_swap (h3 : Fintype.card F % 4 = 3) (x y : Half F) : chD y x = -chC x y := by
  simp only [chC, chD, chi_swap h3 (x 1) (y 0), Int.cast_neg]


/-- The transposition rules as kernel identities. -/
theorem kerT_chA : kerT (chA (F := F)) = chB := rfl

theorem kerT_chB : kerT (chB (F := F)) = chA := rfl

theorem kerT_chC (h3 : Fintype.card F % 4 = 3) : kerT (chC (F := F)) = -chD := by
  funext x y
  exact chC_swap h3 x y

theorem kerT_chD (h3 : Fintype.card F % 4 = 3) : kerT (chD (F := F)) = -chC := by
  funext x y
  exact chD_swap h3 x y

end Sarkozy.MiddleRecords
