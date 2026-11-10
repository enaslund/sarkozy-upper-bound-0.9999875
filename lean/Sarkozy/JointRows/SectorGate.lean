module

public import Sarkozy.JointRows.Sector

/-!
# `lem:joint-rows`(a) from the gate, with the sector reduction proved

Source: `paper/sections/16_extraction.tex`, `lem:joint-rows`(a) and its proof ("Pure stars").

`joint_rows_a_sector` is `RowsA.joint_rows_a_gate` with the operator `𝕄` made concrete:
`𝕄 = (𝒵⊗Φ̂  𝒜⊗I; 𝒜*⊗I  0)` on `ℋ^m ⊕ ℋ^s` (`Sector.qMat`), for a finite-dimensional real inner
product space `ℋ` and `Φ̂` with `Φ̂* = -Φ̂`, `Φ̂² = -I` (`Sector.CxStruct`, the properties of the
normalized Paley operator from `lem:spec:gauss`). Its hypothesis `hsector` (the reduction of `𝕄`
to the `Φ̂`-sectors) is discharged by `Sector.hsector_holds`.

The remaining hypotheses are those of `joint_rows_a_gate` other than `hsector`:
`lem:spec:expansion` with `prop:pinned-collision` (`hexpE`, `hexpF` and the bounds),
`lem:restriction`(a) (`hrestr`), and `prop:conditional-star`(b),(c) (`hdec`, `hV`, `hmean`),
now stated for the concrete `𝕄`; and `lem:spec:gauss` (`hJ`).
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

namespace Sector

variable {m s : Type*} [Fintype m] [DecidableEq m] [Fintype s] [DecidableEq s]
  {Ω : Type*} [Fintype Ω]

/-- **`lem:joint-rows`(a) from the gate `eq:joint-gate`, with the sector reduction proved.** -/
theorem joint_rows_a_sector {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (μ ν : FiniteLaw Ω) (g : Ω → ℝ) (ℓ : ℝ)
    (hν : ∀ x, ν.weight x = g x * μ.weight x) (hg : ∀ x, μ.weight x ≠ 0 → Real.exp (-ℓ) ≤ g x)
    (KE KF KstE KstF TnsE TnsF TcollE TcollF : Ω → Ω → ℝ)
    (hg1 : ∀ x, μ.weight x ≠ 0 → g x = RowsA.dens1 μ KE x)
    (hg2 : ∀ x, μ.weight x ≠ 0 → g x = RowsA.dens2 μ KE x)
    (hexpE : ∀ x y, μ.weight x ≠ 0 → μ.weight y ≠ 0 →
      KE x y = 1 + KstE x y + TnsE x y - TcollE x y)
    (hexpF : ∀ x y, μ.weight x ≠ 0 → μ.weight y ≠ 0 →
      KF x y = 1 + KstF x y + TnsF x y - TcollF x y)
    {εE SE NE nE nE' mE εF SF NF nF nF' mF : ℝ}
    (hεE : |RowsA.mass μ KE - 1| ≤ εE) (hεE1 : εE < 1) (hSE0 : 0 ≤ SE)
    (hSE : PerpBound μ KstE SE)
    (hnsE : FormBound μ TnsE nE) (hcollE : FormBound μ TcollE nE') (hNE : nE + nE' ≤ NE)
    (hmE1 : nrm μ (cen μ (kone μ KE)) ≤ mE) (hmE2 : nrm μ (cen μ (kone' μ KE)) ≤ mE)
    (hεF : |RowsA.mass μ KF - 1| ≤ εF) (hεF1 : εF < 1) (hSF0 : 0 ≤ SF)
    (hSF : PerpBound μ KstF SF)
    (hnsF : FormBound μ TnsF nF) (hcollF : FormBound μ TcollF nF') (hNF : nF + nF' ≤ NF)
    (hmF1 : nrm μ (cen μ (kone μ KF)) ≤ mF) (hmF2 : nrm μ (cen μ (kone' μ KF)) ≤ mF)
    (qT qmean : E → ℝ) (J : H → H) (hJ : CxStruct J)
    (V : E → PiLp 2 (fun _ : m ⊕ s => H)) (ι : (Ω → ℝ) → (Ω → ℝ) → E)
    {P I₀ κ₀ r k eF eE : ℝ}
    (hrestr : ∀ Φ Ψ : Ω → ℝ, μ.expect Φ = 0 → μ.expect Ψ = 0 →
      RowsA.stForm μ KstE KstF Φ Ψ = qT (ι Φ Ψ) / P ∧ ‖ι Φ Ψ‖ ^ 2 = nrm μ Φ ^ 2 + nrm μ Ψ ^ 2)
    (hI₀ : 0 < I₀) (hP : I₀ ≤ P) (hκ₀ : 0 ≤ κ₀) (hr : 0 ≤ r) (hk : 0 < k) (heF : 0 ≤ eF)
    (heE : 0 ≤ eE)
    (Zr : Matrix m m ℝ) (hZ : Zrᵀ = -Zr) (Ar : Matrix m s ℝ)
    (hdec : ∀ x, qT x = κ₀ * r * qMat Zr Ar J (V x) + qmean x) (hV : ∀ x, ‖V x‖ ≤ ‖x‖)
    (hmean : ∀ x, |qmean x| ≤ κ₀ * r * (eF + eE) * ‖x‖ ^ 2)
    (hgate : ((k : ℂ) ^ 2 • (1 : Matrix m m ℂ) + ((k : ℂ) * Complex.I) • RowsA.cplx Zr -
      RowsA.cplx Ar * (RowsA.cplx Ar)ᴴ).PosSemidef) :
    JointBlockLower ν (matchCov (RowsA.relDensity μ KE g)) (foldCov ν (RowsA.relDensity μ KF g))
      (Real.exp ℓ * (κ₀ * r * (k + eF + eE) / I₀ + RowsA.cconst εF SF NF mF +
        RowsA.cconst εE SE NE mE)) :=
  RowsA.joint_rows_a_gate μ ν g ℓ hν hg KE KF KstE KstF TnsE TnsF TcollE TcollF hg1 hg2 hexpE
    hexpF hεE hεE1 hSE0 hSE hnsE hcollE hNE hmE1 hmE2 hεF hεF1 hSF0 hSF hnsF hcollF hNF hmF1 hmF2
    qT qmean (qMat Zr Ar J) V ι hrestr hI₀ hP hκ₀ hr hk heF heE hdec hV hmean Zr hZ Ar hgate
    (hsector_holds hJ Zr Ar)

end Sector

end Sarkozy.JointRows
