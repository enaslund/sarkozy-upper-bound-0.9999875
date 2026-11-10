module

public import Sarkozy.JointRows.RowsAChain
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.Complex.Basic

/-!
# The joint gate (`eq:joint-gate`) and `lem:joint-rows`(a) from it

Source: `paper/sections/16_extraction.tex`, `lem:joint-rows`(a), proof, "Pure stars": "On `ℋ_±`
it acts as `(±i𝒵 𝒜; 𝒜* 0) ⊗ I`; these are complex conjugate Hermitian matrices, `𝒵` being real
and antisymmetric. By `lem:block-completion`(a), eliminating the block `𝗄I`, the one with `+i` is
`⪰ -𝗄I` if and only if `𝗄I + i𝒵 - 𝗄⁻¹𝒢 ⪰ 0`, which is `eq:joint-gate`."

* `gate_sector_plus`: `eq:joint-gate`, `𝗄²I + i𝗄𝒵 - 𝒢 ⪰ 0` with `𝒢 = 𝒜𝒜*`, gives
  `(i𝒵 𝒜; 𝒜* 0) + 𝗄I ⪰ 0`. The block completion is Mathlib's Schur complement
  (`Matrix.PosDef.fromBlocks₂₂`), so `lem:block-completion`(a) is not needed as a hypothesis.
* `gate_sector_minus`: for real `𝒵` with `𝒵ᵀ = -𝒵` and real `𝒜`, the same gate gives the other
  sector `(-i𝒵 𝒜; 𝒜* 0) + 𝗄I ⪰ 0`. The transposed gate is the gate for `-𝒵`.
* `joint_rows_a_gate`: **`lem:joint-rows`(a) from the gate**. The reduction of `𝕄` to its two
  sectors `ℋ_±` (the eigenspaces of `Φ̂` for `±i`, `lem:spec:gauss`, Step 3 of
  `prop:conditional-star`) is the hypothesis `hsector`.
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

namespace RowsA

variable {m s : Type*} [Fintype m] [DecidableEq m] [Fintype s] [DecidableEq s]

/-- **`eq:joint-gate` gives `(i𝒵 𝒜; 𝒜* 0) ⪰ -𝗄I`** (`lem:block-completion`(a): the Schur
complement of the block `𝗄I`). -/
theorem gate_sector_plus {k : ℝ} (hk : 0 < k) (Z : Matrix m m ℂ) (A : Matrix m s ℂ)
    (hgate : ((k : ℂ) ^ 2 • (1 : Matrix m m ℂ) + ((k : ℂ) * Complex.I) • Z - A * Aᴴ).PosSemidef) :
    (fromBlocks ((k : ℂ) • (1 : Matrix m m ℂ) + Complex.I • Z) A Aᴴ
      ((k : ℂ) • (1 : Matrix s s ℂ))).PosSemidef := by
  have hk' : (0 : ℂ) < (k : ℂ) := by exact_mod_cast hk
  have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hD : ((k : ℂ) • (1 : Matrix s s ℂ)).PosDef := Matrix.PosDef.one.smul hk'
  have hinv : ((k : ℂ)⁻¹ • (1 : Matrix s s ℂ)) * ((k : ℂ) • (1 : Matrix s s ℂ)) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hkne,
      one_smul]
  have : Invertible ((k : ℂ) • (1 : Matrix s s ℂ)) :=
    ⟨(k : ℂ)⁻¹ • 1, hinv, by
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_inv_cancel₀ hkne,
        one_smul]⟩
  rw [Matrix.PosDef.fromBlocks₂₂ _ _ hD, Matrix.inv_eq_left_inv hinv]
  have he : (k : ℂ) • (1 : Matrix m m ℂ) + Complex.I • Z -
      A * ((k : ℂ)⁻¹ • (1 : Matrix s s ℂ)) * Aᴴ =
      (k : ℂ)⁻¹ • ((k : ℂ) ^ 2 • (1 : Matrix m m ℂ) + ((k : ℂ) * Complex.I) • Z - A * Aᴴ) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, smul_sub, smul_add, smul_smul,
      smul_smul]
    congr 2
    · congr 1; field_simp
    · congr 1; field_simp
  rw [he]
  exact hgate.smul (inv_nonneg.mpr hk'.le)

/-- The real matrices `𝒵`, `𝒜` as complex matrices. -/
noncomputable def cplx {a b : Type*} (M : Matrix a b ℝ) : Matrix a b ℂ := M.map (fun t => (t : ℂ))

omit [Fintype m] [DecidableEq s] in
/-- **The transposed gate is the gate for `-𝒵`** (`𝒵` real antisymmetric, `𝒜` real). -/
theorem gate_transpose {k : ℝ} (Zr : Matrix m m ℝ) (hZ : Zrᵀ = -Zr) (Ar : Matrix m s ℝ) :
    ((k : ℂ) ^ 2 • (1 : Matrix m m ℂ) + ((k : ℂ) * Complex.I) • cplx Zr -
      cplx Ar * (cplx Ar)ᴴ)ᵀ =
    (k : ℂ) ^ 2 • (1 : Matrix m m ℂ) + ((k : ℂ) * Complex.I) • (-cplx Zr) -
      cplx Ar * (cplx Ar)ᴴ := by
  have hZc : (cplx Zr)ᵀ = -cplx Zr := by
    unfold cplx
    rw [← Matrix.transpose_map, hZ]
    ext i j
    simp
  have hAA : (cplx Ar * (cplx Ar)ᴴ)ᵀ = cplx Ar * (cplx Ar)ᴴ := by
    ext i j
    simp only [cplx, Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.map_apply, Complex.star_def, Complex.conj_ofReal]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
    Matrix.transpose_one, hZc, hAA]

/-- **The other sector**: for real antisymmetric `𝒵` and real `𝒜`, the gate gives
`(-i𝒵 𝒜; 𝒜* 0) ⪰ -𝗄I`. -/
theorem gate_sector_minus {k : ℝ} (hk : 0 < k) (Zr : Matrix m m ℝ) (hZ : Zrᵀ = -Zr)
    (Ar : Matrix m s ℝ)
    (hgate : ((k : ℂ) ^ 2 • (1 : Matrix m m ℂ) + ((k : ℂ) * Complex.I) • cplx Zr -
      cplx Ar * (cplx Ar)ᴴ).PosSemidef) :
    (fromBlocks ((k : ℂ) • (1 : Matrix m m ℂ) + Complex.I • (-cplx Zr)) (cplx Ar) (cplx Ar)ᴴ
      ((k : ℂ) • (1 : Matrix s s ℂ))).PosSemidef := by
  apply gate_sector_plus hk
  rw [← gate_transpose Zr hZ Ar]
  exact hgate.transpose

variable {Ω : Type*} [Fintype Ω]

/-- **`lem:joint-rows`(a) from the gate `eq:joint-gate`.** The gate `𝗄²I + i𝗄𝒵 - 𝒢 ⪰ 0`
(`𝒵` real antisymmetric, `𝒢 = 𝒜𝒜*`, `𝒜` real) gives both sectors `(±i𝒵 𝒜; 𝒜* 0) + 𝗄I ⪰ 0`; the
reduction of `𝕄 = (𝒵 ⊗ Φ̂  𝒜 ⊗ I; 𝒜* ⊗ I  0)` to these sectors (`lem:spec:gauss`: `Φ̂ = ±i` on
`ℋ_±`) is the hypothesis `hsector`; the rest is `joint_rows_a`. -/
theorem joint_rows_a_gate {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] (μ ν : FiniteLaw Ω) (g : Ω → ℝ) (ℓ : ℝ)
    (hν : ∀ x, ν.weight x = g x * μ.weight x) (hg : ∀ x, μ.weight x ≠ 0 → Real.exp (-ℓ) ≤ g x)
    (KE KF KstE KstF TnsE TnsF TcollE TcollF : Ω → Ω → ℝ)
    (hg1 : ∀ x, μ.weight x ≠ 0 → g x = dens1 μ KE x)
    (hg2 : ∀ x, μ.weight x ≠ 0 → g x = dens2 μ KE x)
    (hexpE : ∀ x y, μ.weight x ≠ 0 → μ.weight y ≠ 0 →
      KE x y = 1 + KstE x y + TnsE x y - TcollE x y)
    (hexpF : ∀ x y, μ.weight x ≠ 0 → μ.weight y ≠ 0 →
      KF x y = 1 + KstF x y + TnsF x y - TcollF x y)
    {εE SE NE nE nE' mE εF SF NF nF nF' mF : ℝ}
    (hεE : |mass μ KE - 1| ≤ εE) (hεE1 : εE < 1) (hSE0 : 0 ≤ SE) (hSE : PerpBound μ KstE SE)
    (hnsE : FormBound μ TnsE nE) (hcollE : FormBound μ TcollE nE') (hNE : nE + nE' ≤ NE)
    (hmE1 : nrm μ (cen μ (kone μ KE)) ≤ mE) (hmE2 : nrm μ (cen μ (kone' μ KE)) ≤ mE)
    (hεF : |mass μ KF - 1| ≤ εF) (hεF1 : εF < 1) (hSF0 : 0 ≤ SF) (hSF : PerpBound μ KstF SF)
    (hnsF : FormBound μ TnsF nF) (hcollF : FormBound μ TcollF nF') (hNF : nF + nF' ≤ NF)
    (hmF1 : nrm μ (cen μ (kone μ KF)) ≤ mF) (hmF2 : nrm μ (cen μ (kone' μ KF)) ≤ mF)
    (qT qmean : E → ℝ) (qM : F → ℝ) (V : E → F) (ι : (Ω → ℝ) → (Ω → ℝ) → E)
    {P I₀ κ₀ r k eF eE : ℝ}
    (hrestr : ∀ Φ Ψ : Ω → ℝ, μ.expect Φ = 0 → μ.expect Ψ = 0 →
      stForm μ KstE KstF Φ Ψ = qT (ι Φ Ψ) / P ∧ ‖ι Φ Ψ‖ ^ 2 = nrm μ Φ ^ 2 + nrm μ Ψ ^ 2)
    (hI₀ : 0 < I₀) (hP : I₀ ≤ P) (hκ₀ : 0 ≤ κ₀) (hr : 0 ≤ r) (hk : 0 < k) (heF : 0 ≤ eF)
    (heE : 0 ≤ eE)
    (hdec : ∀ x, qT x = κ₀ * r * qM (V x) + qmean x) (hV : ∀ x, ‖V x‖ ≤ ‖x‖)
    (hmean : ∀ x, |qmean x| ≤ κ₀ * r * (eF + eE) * ‖x‖ ^ 2)
    (Zr : Matrix m m ℝ) (hZ : Zrᵀ = -Zr) (Ar : Matrix m s ℝ)
    (hgate : ((k : ℂ) ^ 2 • (1 : Matrix m m ℂ) + ((k : ℂ) * Complex.I) • cplx Zr -
      cplx Ar * (cplx Ar)ᴴ).PosSemidef)
    (hsector : (fromBlocks ((k : ℂ) • (1 : Matrix m m ℂ) + Complex.I • cplx Zr) (cplx Ar)
        (cplx Ar)ᴴ ((k : ℂ) • (1 : Matrix s s ℂ))).PosSemidef →
      (fromBlocks ((k : ℂ) • (1 : Matrix m m ℂ) + Complex.I • (-cplx Zr)) (cplx Ar)
        (cplx Ar)ᴴ ((k : ℂ) • (1 : Matrix s s ℂ))).PosSemidef →
      ∀ y, -k * ‖y‖ ^ 2 ≤ qM y) :
    JointBlockLower ν (matchCov (relDensity μ KE g)) (foldCov ν (relDensity μ KF g))
      (Real.exp ℓ * (κ₀ * r * (k + eF + eE) / I₀ + cconst εF SF NF mF + cconst εE SE NE mE)) :=
  joint_rows_a μ ν g ℓ hν hg KE KF KstE KstF TnsE TnsF TcollE TcollF hg1 hg2 hexpE hexpF
    hεE hεE1 hSE0 hSE hnsE hcollE hNE hmE1 hmE2 hεF hεF1 hSF0 hSF hnsF hcollF hNF hmF1 hmF2
    qT qmean qM V ι hrestr hI₀ hP hκ₀ hr hk.le heF heE hdec hV hmean
    (hsector (gate_sector_plus hk _ _ hgate) (gate_sector_minus hk Zr hZ Ar hgate))

end RowsA

end Sarkozy.JointRows
