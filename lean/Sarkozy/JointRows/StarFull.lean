module

public import Sarkozy.JointRows.StarBridge

/-!
# `lem:joint-rows`(a) for the concrete pinned rows: the star part and the rest together

Sources: `paper/sections/16_extraction.tex`, `lem:joint-rows`(a) and its proof;
`prop:conditional-star`(b); `prop:pinned-collision`; `prop:pinned-extraction`;
`paper/sections/14_spectral.tex`, `lem:spec:expansion`.

`Coll.joint_rows_a_full` combines fork C1-P's `Coll.joint_rows_a_pinrow` (the concrete kernels
`K_• = rawKer D_•`, `K^st_• = starKer D_•`, `T^•_ns = nsKer D_•`, `T^•_coll = pinKer D_•`, with
`hexpE`/`hexpF`, `hnsE`/`hnsF`, `hcollE`/`hcollF` proved) with `StarOps.qTc_star_decomp` and
`StarOps.norm_starFeat_le` (`hdec`, `hV`), through `StarOps.starKer_eq_starKernel`. The row law is
a product law `λ = ⊗_j ν_j` with densities at most `κ`; the paper's `λ` (`Coll.pinLambda`, the
product of the uniform laws on the allowed sets) is of this form, and `Coll.pinLambda_const` gives
`hlam` for it.

The remaining inputs are: Weil's theorem (`hW`); X1's pin and sign conditions and `he`; the nonstar
class data `cE`, `cF : NsCert`; the antisymmetry `D_E^T = -D_E` (`hDEa`, from
`lem:spec:elementary`); the masses, marginals and the perpendicular star bounds of the rows
(`hεE`, `hmE1`, `hmE2`, `hg1`, `hg2`, `hSE`, and the same for `F`); the gate `hgate`; and the
bound on the complementary-mean form `hmean` (Step 5 of `prop:conditional-star`).
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

namespace Coll

open Restrict

/-- **`lem:joint-rows`(a) for the concrete pinned rows**, with the expansion, the nonstar and
collision bounds, the restriction, the sector reduction, `lem:spec:gauss`, and the star
decomposition `hdec` with its contraction `hV` all proved. -/
theorem joint_rows_a_full {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) {nv : ℕ}
    (hW : Labellings.WeilBound (ZMod p)) (M : Finset (ZMod p)) (pin : Fin nv → ZMod p → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, ExtractionK.pinCount pin j ≤ ϖ)
    (he : ExtractionK.ePin p nv M.card ϖ < 1)
    (DE DF : Fin nv → Fin nv → ℤ) (hDE : ∀ i j, DE i j = 0 ∨ DE i j = 1 ∨ DE i j = -1)
    (hDF : ∀ i j, DF i j = 0 ∨ DF i j = 1 ∨ DF i j = -1) (hDEa : ∀ i j, DE i j = -DE j i)
    (cE : NsCert (ZMod p) ϖ DE) (cF : NsCert (ZMod p) ϖ DF)
    (νp : Fin nv → FiniteLaw (ZMod p)) {κ : ℝ} (hκ : 0 < κ)
    (hdens : ∀ i a, (νp i).weight a ≤ κ / p) (I : Lab p nv → Prop)
    (hI : ∀ x, I x ↔ x ∈ ExtractionK.pinLab M pin)
    (hlam : ∀ x y, x ∈ ExtractionK.pinLab M pin → y ∈ ExtractionK.pinLab M pin →
      (blockLaw νp).weight x = (blockLaw νp).weight y)
    (hPpos : 0 < Peyre.prob (blockLaw νp) I)
    (ν : FiniteLaw (Lab p nv)) (g : Lab p nv → ℝ) (ℓ : ℝ)
    (hν : ∀ x, ν.weight x = g x * (Peyre.condLaw (blockLaw νp) I hPpos).weight x)
    (hg : ∀ x, (Peyre.condLaw (blockLaw νp) I hPpos).weight x ≠ 0 → Real.exp (-ℓ) ≤ g x)
    (hg1 : ∀ x, (Peyre.condLaw (blockLaw νp) I hPpos).weight x ≠ 0 →
      g x = RowsA.dens1 (Peyre.condLaw (blockLaw νp) I hPpos) (rawKer DE) x)
    (hg2 : ∀ x, (Peyre.condLaw (blockLaw νp) I hPpos).weight x ≠ 0 →
      g x = RowsA.dens2 (Peyre.condLaw (blockLaw νp) I hPpos) (rawKer DE) x)
    {εE SE NE mE εF SF NF mF : ℝ}
    (hεE : |RowsA.mass (Peyre.condLaw (blockLaw νp) I hPpos) (rawKer DE) - 1| ≤ εE) (hεE1 : εE < 1)
    (hSE0 : 0 ≤ SE) (hSE : PerpBound (Peyre.condLaw (blockLaw νp) I hPpos) (starKer DE) SE)
    (hNE : cE.bound M.card + collBound p M.card ϖ DE ≤ NE)
    (hmE1 : nrm (Peyre.condLaw (blockLaw νp) I hPpos) (cen (Peyre.condLaw (blockLaw νp) I hPpos)
      (kone (Peyre.condLaw (blockLaw νp) I hPpos) (rawKer DE))) ≤ mE)
    (hmE2 : nrm (Peyre.condLaw (blockLaw νp) I hPpos) (cen (Peyre.condLaw (blockLaw νp) I hPpos)
      (kone' (Peyre.condLaw (blockLaw νp) I hPpos) (rawKer DE))) ≤ mE)
    (hεF : |RowsA.mass (Peyre.condLaw (blockLaw νp) I hPpos) (rawKer DF) - 1| ≤ εF) (hεF1 : εF < 1)
    (hSF0 : 0 ≤ SF) (hSF : PerpBound (Peyre.condLaw (blockLaw νp) I hPpos) (starKer DF) SF)
    (hNF : cF.bound M.card + collBound p M.card ϖ DF ≤ NF)
    (hmF1 : nrm (Peyre.condLaw (blockLaw νp) I hPpos) (cen (Peyre.condLaw (blockLaw νp) I hPpos)
      (kone (Peyre.condLaw (blockLaw νp) I hPpos) (rawKer DF))) ≤ mF)
    (hmF2 : nrm (Peyre.condLaw (blockLaw νp) I hPpos) (cen (Peyre.condLaw (blockLaw νp) I hPpos)
      (kone' (Peyre.condLaw (blockLaw νp) I hPpos) (rawKer DF))) ≤ mF)
    {I₀ k eF eE : ℝ}
    (hI₀ : 0 < I₀) (hP : I₀ ≤ Peyre.prob (blockLaw νp) I) (hk : 0 < k)
    (heF : 0 ≤ eF) (heE : 0 ≤ eE)
    (hmean : ∀ x, |StarOps.qmeanStar νp (fun i j => (DE i j : ℝ)) (fun i j => (DF i j : ℝ))
      (StarOps.sets2 (Fin nv)) x| ≤ κ * (Real.sqrt p)⁻¹ * (eF + eE) * ‖x‖ ^ 2)
    (hgate : ((k : ℂ) ^ 2 • (1 : Matrix (Fin nv ⊕ Fin nv) (Fin nv ⊕ Fin nv) ℂ) +
      ((k : ℂ) * Complex.I) •
        RowsA.cplx (StarOps.jointZ (fun i j => (DE i j : ℝ)) (fun i j => (DF i j : ℝ))) -
      RowsA.cplx (StarOps.jointA (fun i j => (DE i j : ℝ)) (fun i j => (DF i j : ℝ))
        (StarOps.sets2 (Fin nv))) *
      (RowsA.cplx (StarOps.jointA (fun i j => (DE i j : ℝ)) (fun i j => (DF i j : ℝ))
        (StarOps.sets2 (Fin nv))))ᴴ).PosSemidef) :
    JointBlockLower ν
      (matchCov (RowsA.relDensity (Peyre.condLaw (blockLaw νp) I hPpos) (rawKer DE) g))
      (foldCov ν (RowsA.relDensity (Peyre.condLaw (blockLaw νp) I hPpos) (rawKer DF) g))
      (Real.exp ℓ * (κ * (Real.sqrt p)⁻¹ * (k + eF + eE) / I₀ + RowsA.cconst εF SF NF mF +
        RowsA.cconst εE SE NE mE)) := by
  have hDEr : ∀ i j, ((DE i j : ℤ) : ℝ) = -((DE j i : ℤ) : ℝ) := fun i j => by
    rw [hDEa i j]; push_cast; ring
  have hE : starKer (F := ZMod p) DE =
      StarOps.starKernel (fun i j => (DE i j : ℝ)) (StarOps.sets2 (Fin nv)) :=
    funext fun x => funext fun y => StarOps.starKer_eq_starKernel hp DE hDE x y
  have hF : starKer (F := ZMod p) DF =
      StarOps.starKernel (fun i j => (DF i j : ℝ)) (StarOps.sets2 (Fin nv)) :=
    funext fun x => funext fun y => StarOps.starKer_eq_starKernel hp DF hDF x y
  have h𝒮 : ∀ S ∈ StarOps.sets2 (Fin nv), 2 ≤ S.card := fun S hS => StarOps.mem_sets2.mp hS
  exact joint_rows_a_pinrow (κ₀ := κ) (r := (Real.sqrt p)⁻¹) hp hW M pin hpin hpinM ϖ hϖ he DE DF
    hDE hDF cE cF (blockLaw νp) I hI hlam hPpos ν g ℓ hν hg hg1 hg2 hεE hεE1 hSE0 hSE hNE hmE1
    hmE2 hεF hεF1 hSF0 hSF hNF hmF1 hmF2
    (StarOps.qmeanStar νp (fun i j => (DE i j : ℝ)) (fun i j => (DF i j : ℝ))
      (StarOps.sets2 (Fin nv)))
    (StarOps.starFeat νp κ (StarOps.sets2 (Fin nv))) hI₀ hP hκ.le (by positivity) hk heF heE
    (StarOps.jointZ (fun i j => (DE i j : ℝ)) (fun i j => (DF i j : ℝ)))
    (StarOps.jointZ_antisymm hDEr)
    (StarOps.jointA (fun i j => (DE i j : ℝ)) (fun i j => (DF i j : ℝ)) (StarOps.sets2 (Fin nv)))
    (fun x => by rw [hE, hF]; exact StarOps.qTc_star_decomp hp νp hDEr _ hκ x)
    (StarOps.norm_starFeat_le hp νp hκ hdens _ h𝒮) hmean hgate

end Coll

end Sarkozy.JointRows
