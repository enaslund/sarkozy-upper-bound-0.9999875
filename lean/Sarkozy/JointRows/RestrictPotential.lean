module

public import Sarkozy.JointRows.Restrict
public import Sarkozy.JointRows.Potential

/-!
# `lem:joint-potential` for pinned rows, with the restriction step proved

Sources: `paper/sections/16_extraction.tex`, `lem:joint-potential`; `lem:restriction`(a)
(`Sarkozy/Cuts/Restriction.lean`).

`joint_potential_pinned` is `Potential.joint_potential` for rows with the law
`μ = λ(· | 𝓘_pin)`, with `𝕋 = Restrict.qTc` and the embedding `Restrict.iotaC`, so that its
hypothesis `hrestr` is `Restrict.hrestr_holds`. The remaining inputs are those of
`joint_potential` other than `hrestr`: `lem:spec:expansion` with `prop:pinned-collision`, the
decomposition `𝕋 = ℙ + 𝕋_mean` of `prop:conditional-star`(b),(c) with the mean bound, and the
pure-part bound `hPure` (from `Potential.pure_part_potential`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

namespace Restrict

variable {Ω : Type*} [Fintype Ω]

/-- **`lem:joint-potential` for pinned rows**, with `hrestr` discharged. -/
theorem joint_potential_pinned (lam : FiniteLaw Ω) (I : Ω → Prop) (hPpos : 0 < Peyre.prob lam I)
    (ν : FiniteLaw Ω) (g : Ω → ℝ) (ℓ : ℝ)
    (hν : ∀ x, ν.weight x = g x * (Peyre.condLaw lam I hPpos).weight x)
    (hg : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 → Real.exp (-ℓ) ≤ g x)
    (KE KF KstE KstF TnsE TnsF TcollE TcollF : Ω → Ω → ℝ)
    (hg1 : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      g x = RowsA.dens1 (Peyre.condLaw lam I hPpos) KE x)
    (hg2 : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      g x = RowsA.dens2 (Peyre.condLaw lam I hPpos) KE x)
    (hexpE : ∀ x y, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      (Peyre.condLaw lam I hPpos).weight y ≠ 0 → KE x y = 1 + KstE x y + TnsE x y - TcollE x y)
    (hexpF : ∀ x y, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      (Peyre.condLaw lam I hPpos).weight y ≠ 0 → KF x y = 1 + KstF x y + TnsF x y - TcollF x y)
    {εE SE NE nE nE' mE εF SF NF nF nF' mF : ℝ}
    (hεE : |RowsA.mass (Peyre.condLaw lam I hPpos) KE - 1| ≤ εE) (hεE1 : εE < 1)
    (hSE0 : 0 ≤ SE) (hSE : PerpBound (Peyre.condLaw lam I hPpos) KstE SE)
    (hnsE : FormBound (Peyre.condLaw lam I hPpos) TnsE nE)
    (hcollE : FormBound (Peyre.condLaw lam I hPpos) TcollE nE') (hNE : nE + nE' ≤ NE)
    (hmE1 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone (Peyre.condLaw lam I hPpos) KE)) ≤ mE)
    (hmE2 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone' (Peyre.condLaw lam I hPpos) KE)) ≤ mE)
    (hεF : |RowsA.mass (Peyre.condLaw lam I hPpos) KF - 1| ≤ εF) (hεF1 : εF < 1)
    (hSF0 : 0 ≤ SF) (hSF : PerpBound (Peyre.condLaw lam I hPpos) KstF SF)
    (hnsF : FormBound (Peyre.condLaw lam I hPpos) TnsF nF)
    (hcollF : FormBound (Peyre.condLaw lam I hPpos) TcollF nF') (hNF : nF + nF' ≤ NF)
    (hmF1 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone (Peyre.condLaw lam I hPpos) KF)) ≤ mF)
    (hmF2 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone' (Peyre.condLaw lam I hPpos) KF)) ≤ mF)
    (qPure qmean : EuclideanSpace ℝ (Ω ⊕ Ω) → ℝ) {I₀ κ₀ r k eF eE : ℝ}
    (hI₀ : 0 < I₀) (hP : I₀ ≤ Peyre.prob lam I) (hκ₀ : 0 ≤ κ₀) (hr : 0 ≤ r) (hk : 0 ≤ k)
    (heF : 0 ≤ eF) (heE : 0 ≤ eE)
    (hdec : ∀ x, qTc lam KstE KstF x = qPure x + qmean x)
    (hmean : ∀ x, |qmean x| ≤ κ₀ * r * (eF + eE) * ‖x‖ ^ 2)
    (hPure : ∀ x, -(r * k) * ‖x‖ ^ 2 ≤ qPure x) :
    JointBlockLower ν (matchCov (RowsA.relDensity (Peyre.condLaw lam I hPpos) KE g))
      (foldCov ν (RowsA.relDensity (Peyre.condLaw lam I hPpos) KF g))
      (Real.exp ℓ * ((r * k + κ₀ * r * (eF + eE)) / I₀ + RowsA.cconst εF SF NF mF +
        RowsA.cconst εE SE NE mE)) :=
  Potential.joint_potential (Peyre.condLaw lam I hPpos) ν g ℓ hν hg KE KF KstE KstF TnsE TnsF
    TcollE TcollF hg1 hg2 hexpE hexpF hεE hεE1 hSE0 hSE hnsE hcollE hNE hmE1 hmE2 hεF hεF1 hSF0
    hSF hnsF hcollF hNF hmF1 hmF2 (qTc lam KstE KstF) qPure qmean (iotaC lam I)
    (hrestr_holds lam I hPpos KstE KstF) hI₀ hP hκ₀ hr hk heF heE hdec hmean hPure

end Restrict

end Sarkozy.JointRows
