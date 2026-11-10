module

public import Sarkozy.JointRows.CollRows
public import Sarkozy.JointRows.CollNonstar

/-!
# `lem:joint-rows`(a) and `lem:joint-potential` for the concrete pinned rows, with
# `lem:spec:expansion`, `prop:pinned-extraction` and `prop:pinned-collision` proved

Sources: `paper/sections/16_extraction.tex`, `lem:joint-rows`(a), `lem:joint-potential`,
`prop:pinned-extraction`, `prop:pinned-collision`; `paper/sections/14_spectral.tex`,
`lem:spec:expansion`.

`joint_rows_a_pinrow` and `joint_potential_pinrow` are `Coll.joint_rows_a_coll` and
`Coll.joint_potential_coll` with all four kernels of each row concrete:
* `K_• = rawKer D_•`, `K^st_• = starKer D_•`, `T^•_ns = nsKer D_•`, `T^•_coll = pinKer D_•`;
* the expansion `hexpE`, `hexpF` (`lem:spec:expansion`) is proved: `prod_pinOmega`, `expansion`;
* the nonstar bounds `hnsE`, `hnsF` (`prop:pinned-extraction`) are proved from the class data
  `cE`, `cF : NsCert` with `‖T^•_ns‖ ≤ c•.bound |𝓜|` (`formBound_nsKer`);
* the collision bounds (`prop:pinned-collision`) are proved as in `joint_rows_a_coll`.

The remaining inputs concern the star part `K^st_• = starKer D_•` (its compressed norm `S^⋆_•`,
`hSE`, `hSF`, and `prop:conditional-star`(b),(c) through `hdec`, `hV`, `hmean`), the masses and
marginals of `K_•` (`hεE`, `hmE1`, ..., `hg1`, `hg2`), the class data `cE`, `cF`, and Weil's
theorem.
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

namespace Coll

open Restrict

variable {m s : Type*} [Fintype m] [DecidableEq m] [Fintype s] [DecidableEq s]

/-- **`lem:joint-rows`(a) for the concrete pinned rows**, with the expansion, the nonstar bounds
and the collision bounds proved. -/
theorem joint_rows_a_pinrow {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) {nv : ℕ}
    (hW : Labellings.WeilBound (ZMod p)) (M : Finset (ZMod p)) (pin : Fin nv → ZMod p → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, ExtractionK.pinCount pin j ≤ ϖ)
    (he : ExtractionK.ePin p nv M.card ϖ < 1)
    (DE DF : Fin nv → Fin nv → ℤ) (hDE : ∀ i j, DE i j = 0 ∨ DE i j = 1 ∨ DE i j = -1)
    (hDF : ∀ i j, DF i j = 0 ∨ DF i j = 1 ∨ DF i j = -1)
    (cE : NsCert (ZMod p) ϖ DE) (cF : NsCert (ZMod p) ϖ DF)
    (lam : FiniteLaw (Lab p nv)) (I : Lab p nv → Prop)
    (hI : ∀ x, I x ↔ x ∈ ExtractionK.pinLab M pin)
    (hlam : ∀ x y, x ∈ ExtractionK.pinLab M pin → y ∈ ExtractionK.pinLab M pin →
      lam.weight x = lam.weight y)
    (hPpos : 0 < Peyre.prob lam I)
    (ν : FiniteLaw (Lab p nv)) (g : Lab p nv → ℝ) (ℓ : ℝ)
    (hν : ∀ x, ν.weight x = g x * (Peyre.condLaw lam I hPpos).weight x)
    (hg : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 → Real.exp (-ℓ) ≤ g x)
    (hg1 : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      g x = RowsA.dens1 (Peyre.condLaw lam I hPpos) (rawKer DE) x)
    (hg2 : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      g x = RowsA.dens2 (Peyre.condLaw lam I hPpos) (rawKer DE) x)
    {εE SE NE mE εF SF NF mF : ℝ}
    (hεE : |RowsA.mass (Peyre.condLaw lam I hPpos) (rawKer DE) - 1| ≤ εE) (hεE1 : εE < 1)
    (hSE0 : 0 ≤ SE) (hSE : PerpBound (Peyre.condLaw lam I hPpos) (starKer DE) SE)
    (hNE : cE.bound M.card + collBound p M.card ϖ DE ≤ NE)
    (hmE1 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone (Peyre.condLaw lam I hPpos) (rawKer DE))) ≤ mE)
    (hmE2 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone' (Peyre.condLaw lam I hPpos) (rawKer DE))) ≤ mE)
    (hεF : |RowsA.mass (Peyre.condLaw lam I hPpos) (rawKer DF) - 1| ≤ εF) (hεF1 : εF < 1)
    (hSF0 : 0 ≤ SF) (hSF : PerpBound (Peyre.condLaw lam I hPpos) (starKer DF) SF)
    (hNF : cF.bound M.card + collBound p M.card ϖ DF ≤ NF)
    (hmF1 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone (Peyre.condLaw lam I hPpos) (rawKer DF))) ≤ mF)
    (hmF2 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone' (Peyre.condLaw lam I hPpos) (rawKer DF))) ≤ mF)
    (qmean : EuclideanSpace ℝ (Lab p nv ⊕ Lab p nv) → ℝ)
    (V : EuclideanSpace ℝ (Lab p nv ⊕ Lab p nv) → PiLp 2 (fun _ : m ⊕ s => PaleyGauss.sumZero p))
    {I₀ κ₀ r k eF eE : ℝ}
    (hI₀ : 0 < I₀) (hP : I₀ ≤ Peyre.prob lam I) (hκ₀ : 0 ≤ κ₀) (hr : 0 ≤ r) (hk : 0 < k)
    (heF : 0 ≤ eF) (heE : 0 ≤ eE)
    (Zr : Matrix m m ℝ) (hZ : Zrᵀ = -Zr) (Ar : Matrix m s ℝ)
    (hdec : ∀ x, qTc lam (starKer DE) (starKer DF) x =
      κ₀ * r * Sector.qMat Zr Ar (PaleyGauss.paleyJ hp) (V x) + qmean x)
    (hV : ∀ x, ‖V x‖ ≤ ‖x‖)
    (hmean : ∀ x, |qmean x| ≤ κ₀ * r * (eF + eE) * ‖x‖ ^ 2)
    (hgate : ((k : ℂ) ^ 2 • (1 : Matrix m m ℂ) + ((k : ℂ) * Complex.I) • RowsA.cplx Zr -
      RowsA.cplx Ar * (RowsA.cplx Ar)ᴴ).PosSemidef) :
    JointBlockLower ν (matchCov (RowsA.relDensity (Peyre.condLaw lam I hPpos) (rawKer DE) g))
      (foldCov ν (RowsA.relDensity (Peyre.condLaw lam I hPpos) (rawKer DF) g))
      (Real.exp ℓ * (κ₀ * r * (k + eF + eE) / I₀ + RowsA.cconst εF SF NF mF +
        RowsA.cconst εE SE NE mE)) :=
  joint_rows_a_coll hp hW M pin hpin hpinM ϖ hϖ he DE DF hDE hDF lam I hI hlam hPpos ν g ℓ hν hg
    (starKer DE) (starKer DF) (nsKer DE) (nsKer DF) hg1 hg2
    (fun x y _ _ => (prod_pinOmega DE x y).trans (expansion DE x y))
    (fun x y _ _ => (prod_pinOmega DF x y).trans (expansion DF x y))
    hεE hεE1 hSE0 hSE (formBound_nsKer hW M pin hpin hpinM ϖ hϖ he DE hDE cE lam I hI hlam hPpos)
    hNE hmE1 hmE2 hεF hεF1 hSF0 hSF
    (formBound_nsKer hW M pin hpin hpinM ϖ hϖ he DF hDF cF lam I hI hlam hPpos) hNF hmF1 hmF2
    qmean V hI₀ hP hκ₀ hr hk heF heE Zr hZ Ar hdec hV hmean hgate

/-- **`lem:joint-potential` for the concrete pinned rows**, with the expansion, the nonstar bounds
and the collision bounds proved. -/
theorem joint_potential_pinrow {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) {nv : ℕ}
    (hW : Labellings.WeilBound (ZMod p)) (M : Finset (ZMod p)) (pin : Fin nv → ZMod p → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, ExtractionK.pinCount pin j ≤ ϖ)
    (he : ExtractionK.ePin p nv M.card ϖ < 1)
    (DE DF : Fin nv → Fin nv → ℤ) (hDE : ∀ i j, DE i j = 0 ∨ DE i j = 1 ∨ DE i j = -1)
    (hDF : ∀ i j, DF i j = 0 ∨ DF i j = 1 ∨ DF i j = -1)
    (cE : NsCert (ZMod p) ϖ DE) (cF : NsCert (ZMod p) ϖ DF)
    {n : Type*} [Fintype n] [DecidableEq n] {Hs : Type*} [NormedAddCommGroup Hs]
    (lam : FiniteLaw (Lab p nv)) (I : Lab p nv → Prop)
    (hI : ∀ x, I x ↔ x ∈ ExtractionK.pinLab M pin)
    (hlam : ∀ x y, x ∈ ExtractionK.pinLab M pin → y ∈ ExtractionK.pinLab M pin →
      lam.weight x = lam.weight y)
    (hPpos : 0 < Peyre.prob lam I)
    (ν : FiniteLaw (Lab p nv)) (g : Lab p nv → ℝ) (ℓ : ℝ)
    (hν : ∀ x, ν.weight x = g x * (Peyre.condLaw lam I hPpos).weight x)
    (hg : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 → Real.exp (-ℓ) ≤ g x)
    (hg1 : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      g x = RowsA.dens1 (Peyre.condLaw lam I hPpos) (rawKer DE) x)
    (hg2 : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      g x = RowsA.dens2 (Peyre.condLaw lam I hPpos) (rawKer DE) x)
    {εE SE NE mE εF SF NF mF : ℝ}
    (hεE : |RowsA.mass (Peyre.condLaw lam I hPpos) (rawKer DE) - 1| ≤ εE) (hεE1 : εE < 1)
    (hSE0 : 0 ≤ SE) (hSE : PerpBound (Peyre.condLaw lam I hPpos) (starKer DE) SE)
    (hNE : cE.bound M.card + collBound p M.card ϖ DE ≤ NE)
    (hmE1 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone (Peyre.condLaw lam I hPpos) (rawKer DE))) ≤ mE)
    (hmE2 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone' (Peyre.condLaw lam I hPpos) (rawKer DE))) ≤ mE)
    (hεF : |RowsA.mass (Peyre.condLaw lam I hPpos) (rawKer DF) - 1| ≤ εF) (hεF1 : εF < 1)
    (hSF0 : 0 ≤ SF) (hSF : PerpBound (Peyre.condLaw lam I hPpos) (starKer DF) SF)
    (hNF : cF.bound M.card + collBound p M.card ϖ DF ≤ NF)
    (hmF1 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone (Peyre.condLaw lam I hPpos) (rawKer DF))) ≤ mF)
    (hmF2 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone' (Peyre.condLaw lam I hPpos) (rawKer DF))) ≤ mF)
    (qPure qmean : EuclideanSpace ℝ (Lab p nv ⊕ Lab p nv) → ℝ) {I₀ κ₀ r k eF eE : ℝ}
    (hI₀ : 0 < I₀) (hP : I₀ ≤ Peyre.prob lam I) (hκ₀ : 0 < κ₀) (hr : 0 ≤ r) (hk : 0 < k)
    (heF : 0 ≤ eF) (heE : 0 ≤ eE)
    (hdec : ∀ x, qTc lam (starKer DE) (starKer DF) x = qPure x + qmean x)
    (hmean : ∀ x, |qmean x| ≤ κ₀ * r * (eF + eE) * ‖x‖ ^ 2)
    (T G Z : Matrix n n ℝ) (𝒮 : Finset (Finset n))
    (hgate : ∀ S ∈ 𝒮, ((k ^ 2 • (1 : Matrix n n ℝ) - (k * κ₀) • T - κ₀ ^ 2 • G).submatrix
      (fun i : S => (i : n)) (fun i : S => (i : n))).PosSemidef)
    (D : ZMod p → n → ℝ) (Sel : ZMod p → Finset n) (hSel : ∀ t, Sel t ∈ 𝒮)
    (hdκ : ∀ t i, D t i ^ 2 ≤ κ₀) (hdS : ∀ t i, i ∉ Sel t → D t i = 0)
    (hGpos : ∀ y : n → ℝ, 0 ≤ y ⬝ᵥ (G *ᵥ y))
    (qS : (ZMod p → n → ℝ) → Hs → ℝ) (uc : EuclideanSpace ℝ (Lab p nv ⊕ Lab p nv) → ZMod p → n → ℝ)
    (vc : EuclideanSpace ℝ (Lab p nv ⊕ Lab p nv) → Hs)
    (hcomp : ∀ x, qPure x = qS (uc x) (vc x) ∧
      (FiniteLaw.uniform (ZMod p)).expect (fun t => uc x t ⬝ᵥ uc x t) + ‖vc x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (hN : (RowsA.cplx T - Complex.I • RowsA.cplx Z).PosSemidef)
    (Bq : (ZMod p → n → ℝ) → Hs → ℝ)
    (hS : ∀ u v, qS u v = r * Eig.zqForm (FiniteLaw.uniform (ZMod p)) (PaleyGauss.paley p) Z
      (fun t i => D t i * u t i) + 2 * Real.sqrt κ₀ * r * Bq (fun t i => D t i * u t i) v)
    (hcouple : ∀ y v, |Bq y v| ≤
      Real.sqrt ((FiniteLaw.uniform (ZMod p)).expect (fun t => y t ⬝ᵥ (G *ᵥ y t))) * ‖v‖) :
    JointBlockLower ν (matchCov (RowsA.relDensity (Peyre.condLaw lam I hPpos) (rawKer DE) g))
      (foldCov ν (RowsA.relDensity (Peyre.condLaw lam I hPpos) (rawKer DF) g))
      (Real.exp ℓ * ((r * k + κ₀ * r * (eF + eE)) / I₀ + RowsA.cconst εF SF NF mF +
        RowsA.cconst εE SE NE mE)) :=
  joint_potential_coll hp hW M pin hpin hpinM ϖ hϖ he DE DF hDE hDF lam I hI hlam hPpos ν g ℓ hν
    hg (starKer DE) (starKer DF) (nsKer DE) (nsKer DF) hg1 hg2
    (fun x y _ _ => (prod_pinOmega DE x y).trans (expansion DE x y))
    (fun x y _ _ => (prod_pinOmega DF x y).trans (expansion DF x y))
    hεE hεE1 hSE0 hSE (formBound_nsKer hW M pin hpin hpinM ϖ hϖ he DE hDE cE lam I hI hlam hPpos)
    hNE hmE1 hmE2 hεF hεF1 hSF0 hSF
    (formBound_nsKer hW M pin hpin hpinM ϖ hϖ he DF hDF cF lam I hI hlam hPpos) hNF hmF1 hmF2
    qPure qmean hI₀ hP hκ₀ hr hk heF heE hdec hmean T G Z 𝒮 hgate D Sel hSel hdκ hdS hGpos qS uc
    vc hcomp hN Bq hS hcouple

end Coll

end Sarkozy.JointRows
