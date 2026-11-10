module

public import Sarkozy.AnalyticCells.ExpBounds

@[expose] public section

/-!
# The rational cell majorants of the five pieces above `X_Ch`

`paper/sections/20_middle_reference.tex`, `lem:record:block-charge`(i), `eq:record:cell-charge`;
`def:record:exact-blocks`(d).

A piece above `X_Ch` has the geometric cells `x_j = x^{1-j/𝗇} Y^{j/𝗇}` of `[x, Y)` and
`n_j = ⌊570/log x_{j+1}⌋`. With `L_j = log x_j = log x + (j/𝗇)(log Y - log x)`, every quantity of
`eq:record:cell-charge` is an explicit function of the `L_j`:
* `Π_j x_j^{-s} = exp(2a n_j L_{j+1} - s L_j)`,
  `g_j x_j^{1-s} = exp(2a n_j L_{j+1} - (s-1) L_j)/n_j`;
* `I_j(1) = log(L_{j+1}/L_j)`, and `I_j(3/2) ≤ (2/L_j) x_j^{-1/2} (1 - e^{-Δ/2})`,
  `Δ = L_{j+1} - L_j`;
* the jumps `(g_j - g_{j-1})_+ ≤ g_j (1 - ρ_j)_+`, with `ρ_j ≤ g_{j-1}/g_j` from `e^y ≥ 1 + y`.

`GeoQ` holds the rational enclosures `[lxl, lxh] ∋ log x`, `[lYl, lYh] ∋ log Y` and the number of
cells; `Llo j ≤ L_j ≤ Lhi j`, `dhi ≥ Δ`; `m j` is the candidate `n_j` (checked in the kernel to be
`⌊570/L_{j+1}⌋`); `term2 j`, `term3 j` are rational upper bounds of the contribution of cell `j` to
the cell bound at `s = 1`, `s = 3/2` (`a = a_T`), and `bound2`, `bound3` their sums. Everything here
is computable; the soundness is `GeoCells.lean`.
-/

namespace Sarkozy.AnalyticCells

/-- The ledger's exponent `a_G = 71/10⁵` as a rational (RG, 7 November 2026; it was `a_T`). -/
def aQ : ℚ := 71 / 100000

/-- The rational data of a geometric piece. -/
structure GeoQ where
  /-- the number of cells `𝗇` -/
  n : ℕ
  /-- a lower bound of `log x` -/
  lxl : ℚ
  /-- an upper bound of `log x` -/
  lxh : ℚ
  /-- a lower bound of `log Y` -/
  lYl : ℚ
  /-- an upper bound of `log Y` -/
  lYh : ℚ
  /-- the relative error `𝖾` of `θ(t; 4, 3)` on the piece (an upper bound) -/
  err : ℚ

namespace GeoQ

variable (G : GeoQ)

/-- A lower bound of `L_j`. -/
def Llo (j : ℕ) : ℚ := G.lxl + (j : ℚ) / G.n * (G.lYl - G.lxl)

/-- An upper bound of `L_j`. -/
def Lhi (j : ℕ) : ℚ := G.lxh + (j : ℚ) / G.n * (G.lYh - G.lxh)

/-- An upper bound of `Δ = (log Y - log x)/𝗇`. -/
def dhi : ℚ := (G.lYh - G.lxl) / G.n

/-- The candidate `n_j = ⌊570 / Lhi (j+1)⌋`. -/
def m (j : ℕ) : ℕ := (570 * (G.Lhi (j + 1)).den) / (G.Lhi (j + 1)).num.toNat

/-- An upper bound of the exponent `2a n_j L_{j+1} - σ L_j`. -/
def phi (σ : ℚ) (j : ℕ) : ℚ := 2 * aQ * G.m j * G.Lhi (j + 1) - σ * G.Llo j

/-- An upper bound of `exp(2a n_j L_{j+1} - σ L_j)`. -/
def W (σ : ℚ) (j : ℕ) : ℚ := expUpQ (G.phi σ j)

/-- A lower bound of `g_{j-1}/g_j`. -/
def rho (j : ℕ) : ℚ :=
  (1 + 2 * aQ * (((G.m (j - 1) : ℚ) - G.m j) * G.Llo j - G.m j * G.dhi)) * G.m j / G.m (j - 1)

/-- The error constant `𝖾` used (for the pieces above `X_Ch`, `2411/(5·10⁶ lxl)`, an upper bound of
`thm:bmor`'s `2411/(5·10⁶ log x_0)`). -/
def ehi : ℚ := G.err

/-- The edge factor: `1` at `j = 0`, `(1 - ρ_j)_+` at `j ≥ 1`. -/
def edgeF (j : ℕ) : ℚ := if j = 0 then 1 else max 0 (1 - G.rho j)

/-- The exponent step `2a m (lYh - lxh)/𝗇 - σ (lYl - lxl)/𝗇` from cell `j` to `j + 1` inside a
run of constant `n_j = m`. -/
def stepR (σ : ℚ) (m : ℕ) : ℚ := 2 * aQ * m * ((G.lYh - G.lxh) / G.n) - σ * ((G.lYl - G.lxl) / G.n)

/-- An upper bound of `exp (stepR σ m)`. -/
def rUp (σ : ℚ) (m : ℕ) : ℚ := roundUpQ (taylorUp (G.stepR σ m))

/-- The next exponential bound: multiply by the run ratio inside a run, restart at a new run. -/
def nextW (σ : ℚ) (j : ℕ) (w : ℚ) : ℚ :=
  if G.m (j + 1) = G.m j then roundUpQ (w * G.rUp σ (G.m j)) else expUpQ (G.phi σ (j + 1))

/-- The bound of the contribution of cell `j` at `s = 1`, from bounds `wA ≥ exp(φ_j(1))`,
`wB ≥ exp(φ_j(0))`. -/
def term2 (j : ℕ) (wA wB : ℚ) : ℚ :=
  roundUpQ (wA + (1 / 2 + G.ehi) * (wB / G.m j * logUp (G.dhi / G.Llo j)) +
    G.ehi * (2 * wB / G.m j * G.edgeF j / G.Llo j))

/-- The bound of the contribution of cell `j` at `s = 3/2`, from bounds `wA ≥ exp(φ_j(3/2))`,
`wB ≥ exp(φ_j(1/2))`. -/
def term3 (j : ℕ) (wA wB : ℚ) : ℚ :=
  roundUpQ (wA + (1 / 2 + G.ehi) * (wB * (2 * kappa (G.dhi / 2)) / (G.m j * G.Llo j)) +
    G.ehi * (2 * wB / G.m j * G.edgeF j / G.Llo j))

/-- The accumulated cell bound over cells `j, …, j + k - 1`, carrying the exponential bounds. -/
def accum (term : ℕ → ℚ → ℚ → ℚ) (sA sB : ℚ) : ℕ → ℕ → ℚ → ℚ → ℚ
  | 0, _, _, _ => 0
  | k + 1, j, wA, wB =>
      term j wA wB + accum term sA sB k (j + 1) (G.nextW sA j wA) (G.nextW sB j wB)

/-- The rational cell bound at `s = 1`. -/
def bound2 : ℚ := G.accum G.term2 1 0 G.n 0 (G.W 1 0) (G.W 0 0)

/-- The rational cell bound at `s = 3/2`. -/
def bound3 : ℚ := G.accum G.term3 (3 / 2) (1 / 2) G.n 0 (G.W (3 / 2) 0) (G.W (1 / 2) 0)

/-- **The kernel conditions** on the data: `m j` is `⌊570/L_{j+1}⌋` for every enclosed `L_{j+1}`
(`m Lhi ≤ 570 < (m+1) Llo`), `m j ≥ 1`, `m` is nonincreasing, the exponents are small enough for
`expUpQ`, and `Δ`, `L_j` are in the ranges of `logUp`, `kappa`. -/
def Checks : Bool :=
  decide (0 < G.n) && decide (1 < G.lxl) && decide (G.lxl ≤ G.lxh) && decide (G.lYl ≤ G.lYh) &&
    decide (G.lxh ≤ G.lYl) && decide (0 ≤ G.dhi) && decide (G.dhi ≤ 2) &&
    (List.range G.n).all fun j =>
      decide (1 ≤ G.m j) && decide ((G.m j : ℚ) * G.Lhi (j + 1) ≤ 570) &&
      decide (570 < ((G.m j : ℚ) + 1) * G.Llo (j + 1)) &&
      decide (G.m (j + 1) ≤ G.m j ∨ j + 1 = G.n) &&
      decide (|G.phi 0 j| ≤ 64) && decide (|G.phi (1 / 2) j| ≤ 64) && decide (|G.phi 1 j| ≤ 64) &&
      decide (|G.phi (3 / 2) j| ≤ 64) && decide (G.dhi / G.Llo j < 1) &&
      decide (|G.stepR 0 (G.m j)| ≤ 1) && decide (|G.stepR (1 / 2) (G.m j)| ≤ 1) &&
      decide (|G.stepR 1 (G.m j)| ≤ 1) && decide (|G.stepR (3 / 2) (G.m j)| ≤ 1)

end GeoQ

/-! ## The five pieces -/

/-- Enclosures of `log 2`, `log 167` (25 digits) and `log X_Ch` (16 digits); checked in
`Logs.lean`. -/
def l2lo : ℚ := 6931471805599453094172321 / 10 ^ 25
def l2hi : ℚ := 6931471805599453094172322 / 10 ^ 25
def lXChlo : ℚ := 222919156897011298 / 10 ^ 16
def lXChhi : ℚ := 222919156897011299 / 10 ^ 16
def l167lo : ℚ := 51179938124167551072597507 / 10 ^ 25
def l167hi : ℚ := 51179938124167551072597508 / 10 ^ 25

/-- The data of piece 28, `[X_Ch, 2³⁴)`, 236 cells. -/
def geo28 : GeoQ :=
  ⟨236, lXChlo, lXChhi, 34 * l2lo, 34 * l2hi, 2411 / (5000000 * lXChlo)⟩
/-- The data of piece 29, `[2³⁴, 2³⁶)`, 256 cells. -/
def geo29 : GeoQ :=
  ⟨256, 34 * l2lo, 34 * l2hi, 36 * l2lo, 36 * l2hi, 2411 / (5000000 * 34 * l2lo)⟩
/-- The data of piece 30, `[2³⁶, 2⁴⁰)`, 512 cells. -/
def geo30 : GeoQ :=
  ⟨512, 36 * l2lo, 36 * l2hi, 40 * l2lo, 40 * l2hi, 2411 / (5000000 * 36 * l2lo)⟩
/-- The data of piece 31, `[2⁴⁰, 2⁴⁵)`, 640 cells. -/
def geo31 : GeoQ :=
  ⟨640, 40 * l2lo, 40 * l2hi, 45 * l2lo, 45 * l2hi, 2411 / (5000000 * 40 * l2lo)⟩
/-- The data of piece 32, `[2⁴⁵, 167·2⁴⁰)`, 306 cells. -/
def geo32 : GeoQ :=
  ⟨306, 45 * l2lo, 45 * l2hi, l167lo + 40 * l2lo, l167hi + 40 * l2hi,
    2411 / (5000000 * 45 * l2lo)⟩

/-- The data of piece `i` (`28 ≤ i ≤ 32`). -/
def geo : ℕ → GeoQ
  | 28 => geo28
  | 29 => geo29
  | 30 => geo30
  | 31 => geo31
  | _ => geo32

end Sarkozy.AnalyticCells
