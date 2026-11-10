module

public import Sarkozy.JointRows.StarJointRows

/-!
# `lem:joint-rows`(a) for pinned rows with the actual star kernels: `hdec` and `hV` proved

Sources: `paper/sections/16_extraction.tex`, `lem:joint-rows`(a) and its proof ("Restriction",
"Pure stars"), `prop:conditional-star`(b).

`Restrict.joint_rows_a_star` is `Restrict.joint_rows_a_paley` for the row law `λ = ⊗_i ν_i`
(`blockLaw νp`, coordinate laws with densities at most `κ`), the actual star kernels
`K^st_• = StarOps.starKernel D_• 𝒮` (single pairs, row stars and column stars of
`∏ (1 + D_{ij} χ(y_j - x_i))`), the grouped `𝒵 = StarOps.jointZ D_E D_F`,
`𝒜 = StarOps.jointA D_E D_F 𝒮`, the contraction `V = (𝓕 ⊕ 𝓕)^*` (`StarOps.starFeat`), `κ₀ = κ`
and `r = p^{-1/2}`. The hypotheses `hdec` (`StarOps.qTc_star_decomp`), `hV`
(`StarOps.norm_starFeat_le`) and `hZ` (`StarOps.jointZ_antisymm`) are discharged, besides
`hrestr`, `hsector` and `hJ`.

The remaining star input is `hmean`: the bound `‖𝕋_mean‖ ≤ κ r (e_E + e_F)` on the joint form of
the complementary-mean kernels (`StarOps.qmeanStar`; Step 5 of `prop:conditional-star`). The
antisymmetry `D_E^T = -D_E` (`hDE`) is the paper's (from `ς_{kj} = -ς_{jk}`,
`lem:spec:elementary`); every `S ∈ 𝒮` has at least two elements.
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

namespace Restrict

/-- **`lem:joint-rows`(a) for pinned rows of a product law, with the actual star kernels**:
`hrestr`, `hsector`, `hJ`, `hdec`, `hV` and `hZ` are discharged. The remaining inputs are:
* `lem:spec:expansion` with `prop:pinned-collision`: `hexpE`, `hexpF` and the bounds;
* Step 5 of `prop:conditional-star`: `hmean`, the bound on `StarOps.qmeanStar`. -/
theorem joint_rows_a_star {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    {X : Type*} [Fintype X] [DecidableEq X] (νp : X → FiniteLaw (ZMod p)) {κ : ℝ} (hκ : 0 < κ)
    (hdens : ∀ i a, (νp i).weight a ≤ κ / p) (𝒮 : Finset (Finset X))
    (h𝒮 : ∀ S ∈ 𝒮, 2 ≤ S.card) (DE DF : X → X → ℝ) (hDE : ∀ i j, DE i j = -DE j i)
    (I : (X → ZMod p) → Prop) (hPpos : 0 < Peyre.prob (blockLaw νp) I)
    (ν : FiniteLaw (X → ZMod p)) (g : (X → ZMod p) → ℝ) (ℓ : ℝ)
    (hν : ∀ x, ν.weight x = g x * (Peyre.condLaw (blockLaw νp) I hPpos).weight x)
    (hg : ∀ x, (Peyre.condLaw (blockLaw νp) I hPpos).weight x ≠ 0 → Real.exp (-ℓ) ≤ g x)
    (KE KF TnsE TnsF TcollE TcollF : (X → ZMod p) → (X → ZMod p) → ℝ)
    (hg1 : ∀ x, (Peyre.condLaw (blockLaw νp) I hPpos).weight x ≠ 0 →
      g x = RowsA.dens1 (Peyre.condLaw (blockLaw νp) I hPpos) KE x)
    (hg2 : ∀ x, (Peyre.condLaw (blockLaw νp) I hPpos).weight x ≠ 0 →
      g x = RowsA.dens2 (Peyre.condLaw (blockLaw νp) I hPpos) KE x)
    (hexpE : ∀ x y, (Peyre.condLaw (blockLaw νp) I hPpos).weight x ≠ 0 →
      (Peyre.condLaw (blockLaw νp) I hPpos).weight y ≠ 0 →
        KE x y = 1 + (StarOps.starKernel DE 𝒮) x y + TnsE x y - TcollE x y)
    (hexpF : ∀ x y, (Peyre.condLaw (blockLaw νp) I hPpos).weight x ≠ 0 →
      (Peyre.condLaw (blockLaw νp) I hPpos).weight y ≠ 0 →
        KF x y = 1 + (StarOps.starKernel DF 𝒮) x y + TnsF x y - TcollF x y)
    {εE SE NE nE nE' mE εF SF NF nF nF' mF : ℝ}
    (hεE : |RowsA.mass (Peyre.condLaw (blockLaw νp) I hPpos) KE - 1| ≤ εE) (hεE1 : εE < 1)
    (hSE0 : 0 ≤ SE)
    (hSE : PerpBound (Peyre.condLaw (blockLaw νp) I hPpos) (StarOps.starKernel DE 𝒮) SE)
    (hnsE : FormBound (Peyre.condLaw (blockLaw νp) I hPpos) TnsE nE)
    (hcollE : FormBound (Peyre.condLaw (blockLaw νp) I hPpos) TcollE nE') (hNE : nE + nE' ≤ NE)
    (hmE1 : nrm (Peyre.condLaw (blockLaw νp) I hPpos) (cen (Peyre.condLaw (blockLaw νp) I hPpos)
      (kone (Peyre.condLaw (blockLaw νp) I hPpos) KE)) ≤ mE)
    (hmE2 : nrm (Peyre.condLaw (blockLaw νp) I hPpos) (cen (Peyre.condLaw (blockLaw νp) I hPpos)
      (kone' (Peyre.condLaw (blockLaw νp) I hPpos) KE)) ≤ mE)
    (hεF : |RowsA.mass (Peyre.condLaw (blockLaw νp) I hPpos) KF - 1| ≤ εF) (hεF1 : εF < 1)
    (hSF0 : 0 ≤ SF)
    (hSF : PerpBound (Peyre.condLaw (blockLaw νp) I hPpos) (StarOps.starKernel DF 𝒮) SF)
    (hnsF : FormBound (Peyre.condLaw (blockLaw νp) I hPpos) TnsF nF)
    (hcollF : FormBound (Peyre.condLaw (blockLaw νp) I hPpos) TcollF nF') (hNF : nF + nF' ≤ NF)
    (hmF1 : nrm (Peyre.condLaw (blockLaw νp) I hPpos) (cen (Peyre.condLaw (blockLaw νp) I hPpos)
      (kone (Peyre.condLaw (blockLaw νp) I hPpos) KF)) ≤ mF)
    (hmF2 : nrm (Peyre.condLaw (blockLaw νp) I hPpos) (cen (Peyre.condLaw (blockLaw νp) I hPpos)
      (kone' (Peyre.condLaw (blockLaw νp) I hPpos) KF)) ≤ mF)
    {I₀ k eF eE : ℝ}
    (hI₀ : 0 < I₀) (hP : I₀ ≤ Peyre.prob (blockLaw νp) I) (hk : 0 < k)
    (heF : 0 ≤ eF) (heE : 0 ≤ eE)
    (hmean : ∀ x, |StarOps.qmeanStar νp DE DF 𝒮 x| ≤ κ * (Real.sqrt p)⁻¹ * (eF + eE) * ‖x‖ ^ 2)
    (hgate : ((k : ℂ) ^ 2 • (1 : Matrix (X ⊕ X) (X ⊕ X) ℂ) +
      ((k : ℂ) * Complex.I) • RowsA.cplx (StarOps.jointZ DE DF) -
      RowsA.cplx (StarOps.jointA DE DF 𝒮) *
      (RowsA.cplx (StarOps.jointA DE DF 𝒮))ᴴ).PosSemidef) :
    JointBlockLower ν (matchCov (RowsA.relDensity (Peyre.condLaw (blockLaw νp) I hPpos) KE g))
      (foldCov ν (RowsA.relDensity (Peyre.condLaw (blockLaw νp) I hPpos) KF g))
      (Real.exp ℓ * (κ * (Real.sqrt p)⁻¹ * (k + eF + eE) / I₀ + RowsA.cconst εF SF NF mF +
        RowsA.cconst εE SE NE mE)) :=
  joint_rows_a_paley hp (blockLaw νp) I hPpos ν g ℓ hν hg KE KF (StarOps.starKernel DE 𝒮)
    (StarOps.starKernel DF 𝒮) TnsE TnsF TcollE TcollF hg1 hg2 hexpE hexpF hεE hεE1 hSE0 hSE hnsE
    hcollE hNE hmE1 hmE2 hεF hεF1 hSF0 hSF hnsF hcollF hNF hmF1 hmF2 (StarOps.qmeanStar νp DE DF 𝒮)
    (StarOps.starFeat νp κ 𝒮) hI₀ hP hκ.le (by positivity) hk heF heE (StarOps.jointZ DE DF)
    (StarOps.jointZ_antisymm hDE) (StarOps.jointA DE DF 𝒮) (StarOps.qTc_star_decomp hp νp hDE 𝒮 hκ)
    (StarOps.norm_starFeat_le hp νp hκ hdens 𝒮 h𝒮) hmean hgate

end Restrict

end Sarkozy.JointRows
