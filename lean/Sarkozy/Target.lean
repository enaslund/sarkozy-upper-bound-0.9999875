module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Sarkozy.TargetDLK







@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Target

/-! ## The theorem -/

/-- No two elements of `A` differ by a nonzero perfect square. -/
def SquareDifferenceFree (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ m : ℕ, 1 ≤ m → a - b ≠ (m : ℤ) ^ 2

/-- `s(N) ≤ C N^{1 - ε}`: every square-difference-free `A ⊆ [1, N]` has at most `C N^{1-ε}`
elements, with one constant `C` for all `N ≥ 1`. -/
def SarkozyBound (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℤ, A ⊆ Icc 1 (N : ℤ) →
    SquareDifferenceFree A → (A.card : ℝ) ≤ C * (N : ℝ) ^ (1 - ε)

/-- The paper's exponent. -/
noncomputable def epsPaper : ℝ := 1814179 / 141970826000

/-- The exponent proposed for formalization: `a/(72 - ϑ)` with `a = 9/10⁴`, `ϑ = 1.014587`. -/
noncomputable def epsFormal : ℝ := 900 / 70985413

/-! ## Literature inputs in elementary form -/

/-- **H1, Weil** (`thm:weil`(a)): for an odd prime `p` and a nonempty set `S` of roots,
`|∑_{x∈𝔽_p} χ(∏_{a∈S} (x - a))| ≤ (|S| - 1)√p`. -/
def Weil : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ S : Finset (ZMod p), S.Nonempty →
    |((∑ x, quadraticChar (ZMod p) (∏ a ∈ S, (x - a)) : ℤ) : ℝ)| ≤
      ((S.card : ℝ) - 1) * Real.sqrt p

/-- `θ(x; 4, r) = ∑_{p ≤ x, p ≡ r (4)} log p`. -/
noncomputable def theta4 (x : ℝ) (r : ℕ) : ℝ :=
  ∑ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % 4 = r), Real.log p

/-- **H2, BMOR** (`thm:bmor`): for `r ∈ {1, 3}` and `x ≥ 4 800 162 889`,
`|θ(x; 4, r) - x/2| < 0.0004822 · x / log x`. -/
def BMOR : Prop :=
  ∀ r ∈ ({1, 3} : Finset ℕ), ∀ x : ℝ, 4800162889 ≤ x →
    |theta4 x r - x / 2| < 2411 / 5000000 * (x / Real.log x)



def ThetaSmall : Prop :=
  ∀ x : ℝ, 1 ≤ x → x ≤ 10 ^ 10 → |theta4 x 3 - x / 2| ≤ 2072 / 1000 * Real.sqrt x

/-- **H2″, small-range prime counts** (the owner's choice of 2 November 2026): for `1 ≤ x ≤ 10¹⁰`,
`|θ(x; 4, 3) − x/2| ≤ 1.174 √x`.

Source: Ramaré–Rumely, *Primes in arithmetic progressions*, Math. Comp. 65 (1996), Theorem 5.2.1
(p. 421), second inequality.
- That inequality states `|θ(x; k, l) − (x − N(k, l)√x)/φ(k)| ≤ 1.174 √x` for the moduli of their
  Table 1 and `0 ≤ x ≤ 10¹⁰`, where `N(k, l)` is the number of square roots of `l` mod `k`.
- For `k = 4`, `l = 3`, `N = 0`, since 3 is not a square mod 4.
- The same theorem's first inequality is Theorem 2 (`ThetaSmall`). -/
def ThetaSmallRR : Prop :=
  ∀ x : ℝ, 1 ≤ x → x ≤ 10 ^ 10 → |theta4 x 3 - x / 2| ≤ 1174 / 1000 * Real.sqrt x

/-- **H2′, the sharper table entry** (not used: the owner chose `ThetaSmall`). For `1 ≤ x ≤ 10¹⁰`,
`|θ(x; 4, 3) − x/2| ≤ 1.034832 √x`.

Sources: Ramaré–Rumely (1996), Table 2, row `k = 4`, column θ#; BMOR (2018), (A.3) with Table 4.
For `q = 4` and residue 3, θ# = θ, since 3 is not a square mod 4. This is a table entry, not a
numbered theorem. `ThetaSmall` costs only `+0.0025` in the closing number at `a₀`, so it is the
safer choice. -/
def ThetaSmallTable : Prop :=
  ∀ x : ℝ, 1 ≤ x → x ≤ 10 ^ 10 → |theta4 x 3 - x / 2| ≤ 1034832 / 1000000 * Real.sqrt x

/-- `T_t = ∑_y χ(y (y - 1) (y - t))`. -/
noncomputable def legendreSum (p : ℕ) [Fact p.Prime] (t : ZMod p) : ℤ :=
  ∑ y, quadraticChar (ZMod p) (y * (y - 1) * (y - t))

/-- **H3, Ahlgren–Ono with Deligne** (`thm:ahlgren-ono` (a) and (b) combined): for every odd
prime `p`, `|∑_t χ(t) T_t² + p| ≤ 2 p^{3/2}`. -/
def AhlgrenOno : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    |((∑ t, quadraticChar (ZMod p) t * legendreSum p t ^ 2 : ℤ) : ℝ) + p| ≤
      2 * (p : ℝ) ^ ((3 : ℝ) / 2)

/-- `γ(m) = 2⌊m/2⌋`. -/
def gam (m : ℕ) : ℕ := 2 * (m / 2)

/-- The bound `𝓑(m, n, s)` of `eq:dl:B`, with `r = p^{-1/2}`. -/
noncomputable def twoVarBound (p m n s : ℕ) : ℝ :=
  let r := 1 / Real.sqrt p
  (gam m : ℝ) * ((m : ℝ) + n - s - 1) + (if Odd m then ((n : ℝ) - 1) * r + m * r ^ 2 else 0) +
    m * (((m : ℝ) - 2) * r + r ^ 2)

/-- **H4, the two-variable character sum** (`thm:dl:H2`): for distinct roots `a` (`m ≥ 2` of
them) and `b` (`n ≥ 1`), nonzero `c, c'`, `f = c ∏(X - a_i)`, `g = c' ∏(X - b_k)` and
`s = |a ∩ b|`, the sum `Σ = ∑_{y,z} χ(f(y) g(z) (y - z))` satisfies `|Σ| ≤ p 𝓑(m, n, s)`, and
also `|Σ| ≤ p 𝓑(n, m, s)` if `n ≥ 2`. -/
def TwoVariable : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (a b : Finset (ZMod p)) (c c' : ZMod p), c ≠ 0 → c' ≠ 0 →
    2 ≤ a.card → 1 ≤ b.card →
    let sum2 : ℤ := ∑ y, ∑ z, quadraticChar (ZMod p)
      ((c * ∏ x ∈ a, (y - x)) * (c' * ∏ x ∈ b, (z - x)) * (y - z))
    |(sum2 : ℝ)| ≤ p * twoVarBound p a.card b.card (a ∩ b).card ∧
      (2 ≤ b.card → |(sum2 : ℝ)| ≤ p * twoVarBound p b.card a.card (a ∩ b).card)

/-- `τ_S(x) = p^{-1} (∑_y χ(f_S(y) (y - x)) + [|S| odd])` with `f_S = ∏_{a∈S}(X - a)`. -/
noncomputable def tau (p : ℕ) [Fact p.Prime] (S : Finset (ZMod p)) (x : ZMod p) : ℝ :=
  (1 / (p : ℝ)) * (((∑ y, quadraticChar (ZMod p) ((∏ a ∈ S, (y - a)) * (y - x)) : ℤ) : ℝ) +
    if Odd S.card then 1 else 0)

/-- `χ_A(x) = χ(∏_{a∈A}(x - a))`. -/
noncomputable def chiA (p : ℕ) [Fact p.Prime] (A : Finset (ZMod p)) (x : ZMod p) : ℝ :=
  (quadraticChar (ZMod p) (∏ a ∈ A, (x - a)) : ℝ)

/-- **H5, moving-root moments** (`lem:moving-root-moments`): for `S, T, A ⊆ 𝔽_p` with
`|S| = s ≥ 2`, `|T| = t ≥ 2`, `|A| = u`, `r = p^{-1/2}` and `h(k) = 2⌊k/2⌋`,
`|E_x χ_A τ_S τ_T - p^{-1}[S = T, A = ∅]| ≤ r³[(s+t+u-1) h(s) h(t) + 1 + r(s+t+u) s t]` and
`|E_x χ_A τ_S| ≤ r²[(s+u-1) h(s) + r(s+u) s]`. -/
def MovingRoot : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ S T A : Finset (ZMod p), 2 ≤ S.card → 2 ≤ T.card →
    let r : ℝ := 1 / Real.sqrt p
    let s : ℝ := S.card
    let t : ℝ := T.card
    let u : ℝ := A.card
    let hs : ℝ := gam S.card
    let ht : ℝ := gam T.card
    |(1 / (p : ℝ)) * (∑ x, chiA p A x * tau p S x * tau p T x) -
        (if S = T ∧ A = ∅ then 1 / (p : ℝ) else 0)| ≤
      r ^ 3 * ((s + t + u - 1) * hs * ht + 1 + r * (s + t + u) * s * t) ∧
    |(1 / (p : ℝ)) * (∑ x, chiA p A x * tau p S x)| ≤ r ^ 2 * ((s + u - 1) * hs + r * (s + u) * s)

/-! ## The target -/

/-- The exponent at the middle anchor `a₀ = 8896611739/10¹³`: `ε′ = a₀/(72 − ϑ)` with
`ϑ = 1014587/10⁶`, about `1.25330·10⁻⁵`, i.e. the bound `N^{0.9999875}`. On 1 November 2026 the
project owner chose to formalize at about `0.99ε` ("a bound like 0.9999875 is fine"), because at
this anchor the closing margin is about `5.8%` instead of `2.3·10⁻⁷` (`lean/BLUEPRINT.md` §1.4.2).
The paper's `epsPaper` stays the research record. -/
noncomputable def epsAnchor : ℝ := (8896611739 / 10 ^ 13) / (72 - 1014587 / 10 ^ 6)

noncomputable def epsTarget : ℝ := 3 / 250000

/-- **The agreed formalization target**: from the literature inputs, the bound with exponent
`ε`. The intended instance is `epsTarget` (`N^{0.999988}`, the owner's choice of 2 November
2026). Results so far are proved at `epsAnchor`; `epsPaper` would need the paper's certificates.
The inputs:
* H1, H2, H3, H5 and H2″ (above; H4 `TwoVariable` was removed on 9 November 2026 as unused);
* H6 `FourCycle`, the paper's `thm:dl:K` (`Sarkozy/TargetDLK.lean`), assumed by the owner's
  decision of 1 November 2026, together with the character table of `GL₂(𝔽_p)` behind it. -/
def TargetTheorem (ε : ℝ) : Prop :=
  Weil → BMOR → ThetaSmallRR → AhlgrenOno → MovingRoot → FourCycle → SarkozyBound ε

end Sarkozy.Target
