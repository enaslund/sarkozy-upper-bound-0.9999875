module

public import Sarkozy.Target
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.Analysis.Complex.Basic










@[expose] public section

open Finset

namespace Sarkozy.Target

/-- **H7 (written 2 November 2026; not needed by the closing, see the module docstring): the
symmetric-square Mellin bound**, the ℓ-adic step of `lem:rectangle-mellin`.

For every odd prime `p` and every nontrivial multiplicative character `ρ` of `𝔽_p`,
`|∑_{t ≠ 0, 1} ρ(t) (T_t² − p)| ≤ 3 p^{3/2}`, where `T_t = ∑_y χ(y (y − 1) (y − t))`.

It is Deligne's bound for `H¹_c(𝔸¹ ∖ {0, 1}, Sym² 𝓕 ⊗ 𝓛_ρ)` (rank 3, weights at most 3) for
the Legendre sheaf `𝓕`; see the module docstring. -/
def SymSquareMellin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ ρ : MulChar (ZMod p) ℂ, ρ ≠ 1 →
    ‖∑ t ∈ univ.filter (fun t : ZMod p => t ≠ 0 ∧ t ≠ 1),
        ρ t * ((legendreSum p t ^ 2 - (p : ℤ) : ℤ) : ℂ)‖ ≤ 3 * (p : ℝ) ^ ((3 : ℝ) / 2)

end Sarkozy.Target
