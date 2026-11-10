module

public import Sarkozy.JointRows.CollBridge
public import Sarkozy.JointRows.PotentialPaley

/-!
# `lem:joint-rows`(a) and `lem:joint-potential` for the concrete pinned rows, with
# `prop:pinned-collision` proved

Sources: `paper/sections/16_extraction.tex`, `lem:joint-rows`(a), `lem:joint-potential`,
`prop:pinned-collision`; `paper/sections/14_spectral.tex`, `lem:spec:expansion`.

The rows are the pinned labellings `x ∈ 𝔽_p^{[n]}` (`Coll.Lab p n`), with `μ = λ(· | 𝓘_pin)` for
a law `λ` that is constant on `𝓘_pin = ExtractionK.pinLab M pin` (`hlam`; the paper's
`λ = ⊗_i λ_i`, `λ_i` uniform on the allowed set of `i`, is constant on the product of the allowed
sets, which contains `𝓘_pin`). The fold and matching rows have the sign data `D_F`, `D_E`
(`ς_ij` on the pairs of the row, `0` elsewhere), and
* `K_• = Coll.rawKer D_•`, the raw kernel `1{x([n]) ∩ y([n]) = ∅} ∏_{(i,j)} (1 + χ_ij)`;
* `T^•_coll = ExtractionK.pinKer D_•`, the collision kernel of `prop:pinned-collision`.

In `joint_rows_a_coll` (from `Restrict.joint_rows_a_paley`) and `joint_potential_coll` (from
`Restrict.joint_potential_paley`) the collision bounds `hcollE`, `hcollF` are discharged by
`Coll.formBound_pinKer` with `‖T^•_coll‖ ≤ (D_X D_Y)^{1/2}` (`Coll.collBound`), under X1's
hypotheses: Weil's theorem (`hW`, `thm:weil`(a)), the pin conditions, `e^pin_ϖ < 1` (`he`) and
the sign conditions (`hDE`, `hDF`). The expansion hypotheses `hexpE`, `hexpF` become the identity
part of `lem:spec:expansion` for the full product, `∏_{(i,j)} (1 + χ_ij) = 1 + K^st_• + T^•_ns`
on the support of `μ`; the collision split is `Coll.rawKer_add_pinKer`. The star part `K^st_•` and
the non-star part `T^•_ns` stay abstract, with their bounds (`hSE`, `hnsE`, ...).
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

namespace Coll

open Restrict

variable {m s : Type*} [Fintype m] [DecidableEq m] [Fintype s] [DecidableEq s]

/-- **`lem:joint-rows`(a) for the concrete pinned rows**: `Restrict.joint_rows_a_paley` with
`K_• = rawKer D_•`, `T^•_coll = pinKer D_•`, and the collision bounds proved
(`prop:pinned-collision`, via `formBound_pinKer`). -/
theorem joint_rows_a_coll {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) {nv : ℕ}
    (hW : Labellings.WeilBound (ZMod p)) (M : Finset (ZMod p)) (pin : Fin nv → ZMod p → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, ExtractionK.pinCount pin j ≤ ϖ)
    (he : ExtractionK.ePin p nv M.card ϖ < 1)
    (DE DF : Fin nv → Fin nv → ℤ) (hDE : ∀ i j, DE i j = 0 ∨ DE i j = 1 ∨ DE i j = -1)
    (hDF : ∀ i j, DF i j = 0 ∨ DF i j = 1 ∨ DF i j = -1)
    (lam : FiniteLaw (Lab p nv)) (I : Lab p nv → Prop)
    (hI : ∀ x, I x ↔ x ∈ ExtractionK.pinLab M pin)
    (hlam : ∀ x y, x ∈ ExtractionK.pinLab M pin → y ∈ ExtractionK.pinLab M pin →
      lam.weight x = lam.weight y)
    (hPpos : 0 < Peyre.prob lam I)
    (ν : FiniteLaw (Lab p nv)) (g : Lab p nv → ℝ) (ℓ : ℝ)
    (hν : ∀ x, ν.weight x = g x * (Peyre.condLaw lam I hPpos).weight x)
    (hg : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 → Real.exp (-ℓ) ≤ g x)
    (KstE KstF TnsE TnsF : Lab p nv → Lab p nv → ℝ)
    (hg1 : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      g x = RowsA.dens1 (Peyre.condLaw lam I hPpos) (rawKer DE) x)
    (hg2 : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      g x = RowsA.dens2 (Peyre.condLaw lam I hPpos) (rawKer DE) x)
    (hexpE : ∀ x y, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      (Peyre.condLaw lam I hPpos).weight y ≠ 0 →
        ∏ j, ExtractionK.pinOmega DE x j (y j) = 1 + KstE x y + TnsE x y)
    (hexpF : ∀ x y, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      (Peyre.condLaw lam I hPpos).weight y ≠ 0 →
        ∏ j, ExtractionK.pinOmega DF x j (y j) = 1 + KstF x y + TnsF x y)
    {εE SE NE nE mE εF SF NF nF mF : ℝ}
    (hεE : |RowsA.mass (Peyre.condLaw lam I hPpos) (rawKer DE) - 1| ≤ εE) (hεE1 : εE < 1)
    (hSE0 : 0 ≤ SE) (hSE : PerpBound (Peyre.condLaw lam I hPpos) KstE SE)
    (hnsE : FormBound (Peyre.condLaw lam I hPpos) TnsE nE)
    (hNE : nE + collBound p M.card ϖ DE ≤ NE)
    (hmE1 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone (Peyre.condLaw lam I hPpos) (rawKer DE))) ≤ mE)
    (hmE2 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone' (Peyre.condLaw lam I hPpos) (rawKer DE))) ≤ mE)
    (hεF : |RowsA.mass (Peyre.condLaw lam I hPpos) (rawKer DF) - 1| ≤ εF) (hεF1 : εF < 1)
    (hSF0 : 0 ≤ SF) (hSF : PerpBound (Peyre.condLaw lam I hPpos) KstF SF)
    (hnsF : FormBound (Peyre.condLaw lam I hPpos) TnsF nF)
    (hNF : nF + collBound p M.card ϖ DF ≤ NF)
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
    (hdec : ∀ x, qTc lam KstE KstF x =
      κ₀ * r * Sector.qMat Zr Ar (PaleyGauss.paleyJ hp) (V x) + qmean x)
    (hV : ∀ x, ‖V x‖ ≤ ‖x‖)
    (hmean : ∀ x, |qmean x| ≤ κ₀ * r * (eF + eE) * ‖x‖ ^ 2)
    (hgate : ((k : ℂ) ^ 2 • (1 : Matrix m m ℂ) + ((k : ℂ) * Complex.I) • RowsA.cplx Zr -
      RowsA.cplx Ar * (RowsA.cplx Ar)ᴴ).PosSemidef) :
    JointBlockLower ν (matchCov (RowsA.relDensity (Peyre.condLaw lam I hPpos) (rawKer DE) g))
      (foldCov ν (RowsA.relDensity (Peyre.condLaw lam I hPpos) (rawKer DF) g))
      (Real.exp ℓ * (κ₀ * r * (k + eF + eE) / I₀ + RowsA.cconst εF SF NF mF +
        RowsA.cconst εE SE NE mE)) :=
  joint_rows_a_paley hp lam I hPpos ν g ℓ hν hg (rawKer DE) (rawKer DF) KstE KstF TnsE TnsF
    (ExtractionK.pinKer DE) (ExtractionK.pinKer DF) hg1 hg2
    (fun x y hx hy => by linarith [rawKer_add_pinKer DE x y, hexpE x y hx hy])
    (fun x y hx hy => by linarith [rawKer_add_pinKer DF x y, hexpF x y hx hy])
    hεE hεE1 hSE0 hSE hnsE
    (formBound_pinKer hW M pin hpin hpinM ϖ hϖ he DE hDE lam I hI hlam hPpos) hNE hmE1 hmE2
    hεF hεF1 hSF0 hSF hnsF
    (formBound_pinKer hW M pin hpin hpinM ϖ hϖ he DF hDF lam I hI hlam hPpos) hNF hmF1 hmF2
    qmean V hI₀ hP hκ₀ hr hk heF heE Zr hZ Ar hdec hV hmean hgate

/-- **`lem:joint-potential` for the concrete pinned rows**: `Restrict.joint_potential_paley` with
`K_• = rawKer D_•`, `T^•_coll = pinKer D_•`, and the collision bounds proved
(`prop:pinned-collision`, via `formBound_pinKer`). -/
theorem joint_potential_coll {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) {nv : ℕ}
    (hW : Labellings.WeilBound (ZMod p)) (M : Finset (ZMod p)) (pin : Fin nv → ZMod p → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, ExtractionK.pinCount pin j ≤ ϖ)
    (he : ExtractionK.ePin p nv M.card ϖ < 1)
    (DE DF : Fin nv → Fin nv → ℤ) (hDE : ∀ i j, DE i j = 0 ∨ DE i j = 1 ∨ DE i j = -1)
    (hDF : ∀ i j, DF i j = 0 ∨ DF i j = 1 ∨ DF i j = -1)
    {n : Type*} [Fintype n] [DecidableEq n] {Hs : Type*} [NormedAddCommGroup Hs]
    (lam : FiniteLaw (Lab p nv)) (I : Lab p nv → Prop)
    (hI : ∀ x, I x ↔ x ∈ ExtractionK.pinLab M pin)
    (hlam : ∀ x y, x ∈ ExtractionK.pinLab M pin → y ∈ ExtractionK.pinLab M pin →
      lam.weight x = lam.weight y)
    (hPpos : 0 < Peyre.prob lam I)
    (ν : FiniteLaw (Lab p nv)) (g : Lab p nv → ℝ) (ℓ : ℝ)
    (hν : ∀ x, ν.weight x = g x * (Peyre.condLaw lam I hPpos).weight x)
    (hg : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 → Real.exp (-ℓ) ≤ g x)
    (KstE KstF TnsE TnsF : Lab p nv → Lab p nv → ℝ)
    (hg1 : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      g x = RowsA.dens1 (Peyre.condLaw lam I hPpos) (rawKer DE) x)
    (hg2 : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      g x = RowsA.dens2 (Peyre.condLaw lam I hPpos) (rawKer DE) x)
    (hexpE : ∀ x y, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      (Peyre.condLaw lam I hPpos).weight y ≠ 0 →
        ∏ j, ExtractionK.pinOmega DE x j (y j) = 1 + KstE x y + TnsE x y)
    (hexpF : ∀ x y, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      (Peyre.condLaw lam I hPpos).weight y ≠ 0 →
        ∏ j, ExtractionK.pinOmega DF x j (y j) = 1 + KstF x y + TnsF x y)
    {εE SE NE nE mE εF SF NF nF mF : ℝ}
    (hεE : |RowsA.mass (Peyre.condLaw lam I hPpos) (rawKer DE) - 1| ≤ εE) (hεE1 : εE < 1)
    (hSE0 : 0 ≤ SE) (hSE : PerpBound (Peyre.condLaw lam I hPpos) KstE SE)
    (hnsE : FormBound (Peyre.condLaw lam I hPpos) TnsE nE)
    (hNE : nE + collBound p M.card ϖ DE ≤ NE)
    (hmE1 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone (Peyre.condLaw lam I hPpos) (rawKer DE))) ≤ mE)
    (hmE2 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone' (Peyre.condLaw lam I hPpos) (rawKer DE))) ≤ mE)
    (hεF : |RowsA.mass (Peyre.condLaw lam I hPpos) (rawKer DF) - 1| ≤ εF) (hεF1 : εF < 1)
    (hSF0 : 0 ≤ SF) (hSF : PerpBound (Peyre.condLaw lam I hPpos) KstF SF)
    (hnsF : FormBound (Peyre.condLaw lam I hPpos) TnsF nF)
    (hNF : nF + collBound p M.card ϖ DF ≤ NF)
    (hmF1 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone (Peyre.condLaw lam I hPpos) (rawKer DF))) ≤ mF)
    (hmF2 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone' (Peyre.condLaw lam I hPpos) (rawKer DF))) ≤ mF)
    (qPure qmean : EuclideanSpace ℝ (Lab p nv ⊕ Lab p nv) → ℝ) {I₀ κ₀ r k eF eE : ℝ}
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
  joint_potential_paley hp lam I hPpos ν g ℓ hν hg (rawKer DE) (rawKer DF) KstE KstF TnsE TnsF
    (ExtractionK.pinKer DE) (ExtractionK.pinKer DF) hg1 hg2
    (fun x y hx hy => by linarith [rawKer_add_pinKer DE x y, hexpE x y hx hy])
    (fun x y hx hy => by linarith [rawKer_add_pinKer DF x y, hexpF x y hx hy])
    hεE hεE1 hSE0 hSE hnsE
    (formBound_pinKer hW M pin hpin hpinM ϖ hϖ he DE hDE lam I hI hlam hPpos) hNE hmE1 hmE2
    hεF hεF1 hSF0 hSF hnsF
    (formBound_pinKer hW M pin hpin hpinM ϖ hϖ he DF hDF lam I hI hlam hPpos) hNF hmF1 hmF2
    qPure qmean hI₀ hP hκ₀ hr hk heF heE hdec hmean T G Z 𝒮 hgate D Sel hSel hdκ hdS hGpos qS uc
    vc hcomp hN Bq hS hcouple

end Coll

end Sarkozy.JointRows
