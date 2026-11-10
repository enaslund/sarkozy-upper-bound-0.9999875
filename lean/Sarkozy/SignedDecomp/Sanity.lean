module

public import Sarkozy.SignedDecomp.Numbers

@[expose] public section

/-!
# Cross-checks of the constants against `cert:signed-local` (SD2)

`paper/sections/21_middle_records.tex`, `cert:signed-local`: "A read-only evaluation of the three
functions at `X = Q₃ = 19951586` (`r_X = 1/4466`) gives the following upper bounds:
`Γ_A < 1.0002241`, `c_+ < 1.7371505`, `E_c < 0.04070887`, `e_sg < 17.254638`,
`c_col < 5.6198068`, `e_o < 7.6238442`, … `s_t < 2.3842273` and `d_t < 2.3903321`".

**`cert_Q3`** (kernel): the rational majorants of `Numbers.lean` at the first piece start, which
are the constants of `eq:signed-constants` as formalized in `Poly.lean` and `Paper.lean`, lie in
`[v - 10⁻⁶, v]` for each printed value `v`. So the formulas of the hypotheses `ccolP`, `esgP`,
`cpP` (and PG's `eoP`) reproduce the paper's numbers to six decimals, and the majorants are not
looser than the paper's printed bounds.
-/

namespace Sarkozy.SignedDecomp

/-- `E_c` at `X_i`. -/
def ecX (i : Fin 33) : ℚ := ecPoly (AX i)

/-- `d_t = s_t Γ_A + (e_o + e_sg) r` at `X_i` (with the majorants). -/
def dtX (i : Fin 33) : ℚ := stU * gamX i + (eoX i + esgX i) * rX i

/-- **`cert:signed-local` at `Q₃`**: the printed upper bounds, and lower bounds `10⁻⁶` below. -/
theorem cert_Q3 :
    10002231 / 10 ^ 7 ≤ gamX 0 ∧ gamX 0 ≤ 10002241 / 10 ^ 7 ∧
    17371495 / 10 ^ 7 ≤ cpX 0 ∧ cpX 0 ≤ 17371505 / 10 ^ 7 ∧
    4070877 / 10 ^ 8 ≤ ecX 0 ∧ ecX 0 ≤ 4070887 / 10 ^ 8 ∧
    17254628 / 10 ^ 6 ≤ esgX 0 ∧ esgX 0 ≤ 17254638 / 10 ^ 6 ∧
    56198058 / 10 ^ 7 ≤ ccolX 0 ∧ ccolX 0 ≤ 56198068 / 10 ^ 7 ∧
    76238432 / 10 ^ 7 ≤ eoX 0 ∧ eoX 0 ≤ 76238442 / 10 ^ 7 ∧
    23842263 / 10 ^ 7 ≤ stU ∧ stU ≤ 23842273 / 10 ^ 7 ∧
    23903311 / 10 ^ 7 ≤ dtX 0 ∧ dtX 0 ≤ 23903321 / 10 ^ 7 := by
  decide +kernel

end Sarkozy.SignedDecomp
