module

public import Sarkozy.JointRows.RestrictPotential
public import Sarkozy.JointRows.PaleyGauss

/-!
# `lem:joint-potential` for pinned rows, with the actual `Φ̂`

Sources: `paper/sections/16_extraction.tex`, `lem:joint-potential` and its proof;
`lem:restriction`(a); `lem:spec:gauss`.

`joint_potential_paley` combines `Restrict.joint_potential_pinned` (`hrestr` discharged) with
`Eig.pure_part_potential_eig` at the normalized Paley operator (`PaleyGauss.paley_paleyLike`,
`p ≡ 3 (mod 4)`). So the pure-part bound `hPure` is no longer an input: it follows from the gate
`eq:joint-potential-gate` on the sets `S ∈ 𝒮` (`hgate`), from `T - i𝒵 ⪰ 0` (`hN`; the paper
assumes `T ± i𝒵 ⪰ 0`, and one sign suffices), and from the structure of the pure part `ℙ`
(`hcomp`, `hS`, `hcouple`): `ℙ = r⟨D u, (𝒵 ⊗ Φ̂) D u⟩ + 2√κ₀ r B(D u, v)` with
`E_t |u_t|² + ‖v‖² ≤ ‖x‖²` and `|B(y, v)| ≤ ‖G^{1/2} y‖ ‖v‖`. The remaining inputs are these
three, `lem:spec:expansion` with `prop:pinned-collision` (the expansion and its bounds), and the
decomposition `𝕋 = ℙ + 𝕋_mean` with the mean bound (`prop:conditional-star`(b),(c)).
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

namespace Restrict

variable {Ω : Type*} [Fintype Ω]

/-- **`lem:joint-potential` for pinned rows, with `hrestr` and the pure-part bound discharged**,
the latter through `heig` for the actual normalized Paley operator. -/
theorem joint_potential_paley {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    {n : Type*} [Fintype n] [DecidableEq n] {Hs : Type*} [NormedAddCommGroup Hs]
    (lam : FiniteLaw Ω) (I : Ω → Prop) (hPpos : 0 < Peyre.prob lam I)
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
    (hI₀ : 0 < I₀) (hP : I₀ ≤ Peyre.prob lam I) (hκ₀ : 0 < κ₀) (hr : 0 ≤ r) (hk : 0 < k)
    (heF : 0 ≤ eF) (heE : 0 ≤ eE)
    (hdec : ∀ x, qTc lam KstE KstF x = qPure x + qmean x)
    (hmean : ∀ x, |qmean x| ≤ κ₀ * r * (eF + eE) * ‖x‖ ^ 2)
    (T G Z : Matrix n n ℝ) (𝒮 : Finset (Finset n))
    (hgate : ∀ S ∈ 𝒮, ((k ^ 2 • (1 : Matrix n n ℝ) - (k * κ₀) • T - κ₀ ^ 2 • G).submatrix
      (fun i : S => (i : n)) (fun i : S => (i : n))).PosSemidef)
    (D : ZMod p → n → ℝ) (Sel : ZMod p → Finset n) (hSel : ∀ t, Sel t ∈ 𝒮)
    (hdκ : ∀ t i, D t i ^ 2 ≤ κ₀) (hdS : ∀ t i, i ∉ Sel t → D t i = 0)
    (hGpos : ∀ y : n → ℝ, 0 ≤ y ⬝ᵥ (G *ᵥ y))
    (qS : (ZMod p → n → ℝ) → Hs → ℝ) (uc : EuclideanSpace ℝ (Ω ⊕ Ω) → ZMod p → n → ℝ)
    (vc : EuclideanSpace ℝ (Ω ⊕ Ω) → Hs)
    (hcomp : ∀ x, qPure x = qS (uc x) (vc x) ∧
      (FiniteLaw.uniform (ZMod p)).expect (fun t => uc x t ⬝ᵥ uc x t) + ‖vc x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (hN : (RowsA.cplx T - Complex.I • RowsA.cplx Z).PosSemidef)
    (Bq : (ZMod p → n → ℝ) → Hs → ℝ)
    (hS : ∀ u v, qS u v = r * Eig.zqForm (FiniteLaw.uniform (ZMod p)) (PaleyGauss.paley p) Z
      (fun t i => D t i * u t i) + 2 * Real.sqrt κ₀ * r * Bq (fun t i => D t i * u t i) v)
    (hcouple : ∀ y v, |Bq y v| ≤
      Real.sqrt ((FiniteLaw.uniform (ZMod p)).expect (fun t => y t ⬝ᵥ (G *ᵥ y t))) * ‖v‖) :
    JointBlockLower ν (matchCov (RowsA.relDensity (Peyre.condLaw lam I hPpos) KE g))
      (foldCov ν (RowsA.relDensity (Peyre.condLaw lam I hPpos) KF g))
      (Real.exp ℓ * ((r * k + κ₀ * r * (eF + eE)) / I₀ + RowsA.cconst εF SF NF mF +
        RowsA.cconst εE SE NE mE)) :=
  joint_potential_pinned lam I hPpos ν g ℓ hν hg KE KF KstE KstF TnsE TnsF TcollE TcollF hg1 hg2
    hexpE hexpF hεE hεE1 hSE0 hSE hnsE hcollE hNE hmE1 hmE2 hεF hεF1 hSF0 hSF hnsF hcollF hNF hmF1
    hmF2 qPure qmean hI₀ hP hκ₀.le hr hk.le heF heE hdec hmean
    (Eig.pure_part_potential_eig T G Z hk hκ₀ hr 𝒮 hgate (FiniteLaw.uniform (ZMod p)) D Sel hSel
      hdκ hdS hGpos qPure qS uc vc hcomp (PaleyGauss.paley p) (PaleyGauss.paley_paleyLike hp) hN
      Bq hS hcouple)

end Restrict

end Sarkozy.JointRows
