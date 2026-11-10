module

public import Sarkozy.JointRows.PaleyGauss
public import Sarkozy.JointRows.Restrict

/-!
# `ℋ = L²_0(𝔽_p)` with the normalized Paley operator is a `Sector.CxStruct`

Source: `paper/sections/16_extraction.tex`, `prop:conditional-star` ("let `ℋ = L²_0(𝔽_p)` for the
uniform law, and let `Φ̂ = C/r` be the normalized Paley operator, so that `Φ̂𝟙 = 0`, `Φ̂* = -Φ̂`
and `Φ̂² = -I` on `ℋ` (`lem:spec:gauss`)").

* `sumZero p`: the vectors of `EuclideanSpace ℝ (ZMod p)` with coordinate sum zero, a model of
  `ℋ`. Its inner product is `p` times that of `L²(uniform)`. This does not affect `CxStruct`, nor
  the hypotheses `hdec`, `hV` below: for a feature map `V` into `L²_0(uniform)^{m ⊕ s}`, the
  Euclidean norm of `p^{-1/2} V x` is the `L²(uniform)` norm of `V x`, and `Sector.qMat` of
  `p^{-1/2} V x` for the Euclidean inner product is `Sector.qMat` of `V x` for the `L²(uniform)`
  one;
* `paley_sum_zero`: `Φ̂` maps into `ℋ` (`Φ̂*𝟙 = 0`), so it restricts to `paleyJ hp : ℋ → ℋ`;
* `cxStruct_paley`: `Φ̂* = -Φ̂` and `Φ̂² = -I` on `ℋ`, for `p ≡ 3 (mod 4)`;
* `Restrict.joint_rows_a_paley`: `Restrict.joint_rows_a_pinned` with `ℋ = sumZero p` and
  `Φ̂ = paleyJ hp`, so its hypothesis `hJ` (`lem:spec:gauss`) is discharged.
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

namespace PaleyGauss

variable {p : ℕ} [Fact p.Prime]

/-- `ℋ = L²_0(𝔽_p)`: the vectors of `EuclideanSpace ℝ (ZMod p)` with coordinate sum zero. -/
def sumZero (p : ℕ) [Fact p.Prime] : Submodule ℝ (EuclideanSpace ℝ (ZMod p)) where
  carrier := {v | ∑ a, v.ofLp a = 0}
  add_mem' := by
    intro v w hv hw
    simp only [Set.mem_ofPred_eq, WithLp.ofLp_add, Pi.add_apply, Finset.sum_add_distrib] at *
    rw [hv, hw, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    simp only [Set.mem_ofPred_eq, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      ← Finset.mul_sum] at *
    rw [hv, mul_zero]

/-- `∑_b χ(b - a) = 0`. -/
theorem sum_chiR_sub (hp : p % 4 = 3) (b : ZMod p) : ∑ a, chiR p (b - a) = 0 := by
  rw [Fintype.sum_equiv (Equiv.subLeft b) (fun a => chiR p (b - a)) (fun x => chiR p x)
    (fun _ => rfl)]
  unfold chiR
  have h := quadraticChar_sum_zero (ringChar_ne_two hp) (F := ZMod p)
  exact_mod_cast h

/-- **`Φ̂*𝟙 = 0`**: `∑_a Φ̂f(a) = 0`. -/
theorem paley_sum_zero (hp : p % 4 = 3) (f : ZMod p → ℝ) : ∑ a, paley p f a = 0 := by
  unfold paley
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.sum_mul, sum_chiR_sub hp, zero_mul, Finset.sum_const_zero, mul_zero]

/-- `Φ̂` on `ℋ`. -/
noncomputable def paleyJ (hp : p % 4 = 3) (v : sumZero p) : sumZero p :=
  ⟨WithLp.toLp 2 (paley p (v : EuclideanSpace ℝ (ZMod p)).ofLp), paley_sum_zero hp _⟩

/-- **`lem:spec:gauss`, real form: `Φ̂* = -Φ̂` and `Φ̂² = -I` on `ℋ`** (`p ≡ 3 (mod 4)`). -/
theorem cxStruct_paley (hp : p % 4 = 3) : Sector.CxStruct (paleyJ hp) where
  anti h h' := by
    rw [Submodule.coe_inner, Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct,
      EuclideanSpace.inner_eq_star_dotProduct]
    simp only [paleyJ, WithLp.ofLp_toLp, star_trivial, dotProduct]
    exact paley_anti hp _ _
  sq h := by
    apply Subtype.ext
    apply PiLp.ext
    intro a
    have hh : ∑ c, (h : EuclideanSpace ℝ (ZMod p)).ofLp c = 0 := h.2
    simp only [paleyJ, WithLp.ofLp_toLp, Submodule.coe_neg, WithLp.ofLp_neg, Pi.neg_apply]
    rw [paley_sq hp, hh, zero_div, sub_zero]

end PaleyGauss

namespace Restrict

variable {Ω : Type*} [Fintype Ω]
variable {m s : Type*} [Fintype m] [DecidableEq m] [Fintype s] [DecidableEq s]

/-- **`lem:joint-rows`(a) for pinned rows, with the actual `Φ̂`**: `joint_rows_a_pinned` with
`ℋ = L²_0(𝔽_p)` (`PaleyGauss.sumZero p`) and `Φ̂` the normalized Paley operator
(`PaleyGauss.paleyJ hp`), for `p ≡ 3 (mod 4)`. The hypotheses `hrestr` (`lem:restriction`(a)),
`hsector` (the `Φ̂`-sector reduction) and `hJ` (`lem:spec:gauss`) are discharged. The remaining
inputs are:
* `lem:spec:expansion` with `prop:pinned-collision`: `hexpE`, `hexpF` and the bounds;
* `prop:conditional-star`(b),(c): `hdec`, `hV`, `hmean`, for `qTc`. -/
theorem joint_rows_a_paley {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
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
    (qmean : EuclideanSpace ℝ (Ω ⊕ Ω) → ℝ)
    (V : EuclideanSpace ℝ (Ω ⊕ Ω) → PiLp 2 (fun _ : m ⊕ s => PaleyGauss.sumZero p))
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
    JointBlockLower ν (matchCov (RowsA.relDensity (Peyre.condLaw lam I hPpos) KE g))
      (foldCov ν (RowsA.relDensity (Peyre.condLaw lam I hPpos) KF g))
      (Real.exp ℓ * (κ₀ * r * (k + eF + eE) / I₀ + RowsA.cconst εF SF NF mF +
        RowsA.cconst εE SE NE mE)) :=
  joint_rows_a_pinned lam I hPpos ν g ℓ hν hg KE KF KstE KstF TnsE TnsF TcollE TcollF hg1 hg2
    hexpE hexpF hεE hεE1 hSE0 hSE hnsE hcollE hNE hmE1 hmE2 hεF hεF1 hSF0 hSF hnsF hcollF hNF hmF1
    hmF2 qmean (PaleyGauss.paleyJ hp) (PaleyGauss.cxStruct_paley hp) V hI₀ hP hκ₀ hr hk heF heE Zr
    hZ Ar hdec hV hmean hgate

end Restrict

end Sarkozy.JointRows
