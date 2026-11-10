module

public import Sarkozy.JointRows.SectorGate
public import Sarkozy.Cuts.Restriction

/-!
# The restriction step of `lem:joint-rows`(a), from `lem:restriction`(a)

Sources: `paper/sections/16_extraction.tex`, proof of `lem:joint-rows`(a) ("Restriction");
`paper/sections/13_cuts_correlations.tex`, `lem:restriction`(a), formalized in
`Sarkozy/Cuts/Restriction.lean` (`nrm_iota`, `expect_iota`, `kernelForm_cond`).

Both rows have the law `μ = λ(· | 𝓘_pin)`, `P = λ(𝓘_pin)`, and `ι f = 𝟙_{𝓘_pin} f/√P`
(`Cuts.iota`). The joint block `𝕋` of the star operators on `L²_0(λ)²` is realized on
`E = EuclideanSpace ℝ (Ω ⊕ Ω)` by `(f, g) ↦ (√λ f, √λ g)` (`realize`): its quadratic form `qTc` is
the joint form of the star kernels `K^{st}_E`, `K^{st}_F` relative to `λ ⊗ λ`, compressed to the
mean-zero functions on both sides (`cen`), as in `prop:conditional-star`. The embedding of
`L²(μ)²` is `ιc(Φ, Ψ) = realize(ιΦ, ιΨ)`.

* `hrestr_holds`: **the hypothesis `hrestr` of `joint_rows_a_gate` holds**: for `μ`-centred
  `Φ, Ψ`, `⟨(Φ, Ψ), 𝕂^{st}(Φ, Ψ)⟩_μ = qTc(ιc(Φ, Ψ))/P` and `‖ιc(Φ, Ψ)‖² = ‖Φ‖²_μ + ‖Ψ‖²_μ`.
  It is `lem:restriction`(a) for each of the three kernel forms (`kernelForm_cond`), the
  isometry `nrm_iota`, and `ι` preserving centring (`expect_iota`).
* `joint_rows_a_pinned`: `lem:joint-rows`(a) for pinned rows, with `hrestr` and `hsector`
  discharged. The remaining hypotheses are `lem:spec:expansion` with `prop:pinned-collision`, and
  `prop:conditional-star`(b),(c) for the concrete `qTc` (`hdec`, `hV`, `hmean`), and
  `lem:spec:gauss` (`hJ`).

Because `qTc` sees only the centred parts, `prop:conditional-star`(b), which is a statement on
`L²_0`, gives `hdec`, `hV`, `hmean` for every `x ∈ E` by precomposing with the centring.
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

namespace Restrict

variable {Ω : Type*} [Fintype Ω]

theorem kf_eq_kernelForm (μ : FiniteLaw Ω) (K : Ω → Ω → ℝ) (f h : Ω → ℝ) :
    kf μ K f h = Cuts.kernelForm μ μ K f h := by
  simp only [kf, Cuts.kernelForm, LinearMap.mk₂_apply]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- A kernel form only sees the values on the support. -/
theorem kf_congr_supp (μ : FiniteLaw Ω) (K : Ω → Ω → ℝ) {f f' g g' : Ω → ℝ}
    (hf : ∀ x, μ.weight x ≠ 0 → f x = f' x) (hg : ∀ x, μ.weight x ≠ 0 → g x = g' x) :
    kf μ K f g = kf μ K f' g' := by
  unfold kf
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases hx : μ.weight x = 0
  · simp only [hx, zero_mul]
  · by_cases hy : μ.weight y = 0
    · simp only [hy, mul_zero, zero_mul]
    · rw [hf x hx, hg y hy]

/-- The realization `(f, g) ↦ (√λ f, √λ g)` of `L²(λ)²` in `EuclideanSpace ℝ (Ω ⊕ Ω)`. -/
noncomputable def realize (lam : FiniteLaw Ω) (f g : Ω → ℝ) : EuclideanSpace ℝ (Ω ⊕ Ω) :=
  WithLp.toLp 2 (Sum.elim (fun x => √(lam.weight x) * f x) (fun x => √(lam.weight x) * g x))

/-- The first component of a vector, as a function (`v/√λ`). -/
noncomputable def dewL (lam : FiniteLaw Ω) (v : EuclideanSpace ℝ (Ω ⊕ Ω)) (x : Ω) : ℝ :=
  v.ofLp (Sum.inl x) / √(lam.weight x)

/-- The second component of a vector, as a function. -/
noncomputable def dewR (lam : FiniteLaw Ω) (v : EuclideanSpace ℝ (Ω ⊕ Ω)) (x : Ω) : ℝ :=
  v.ofLp (Sum.inr x) / √(lam.weight x)

/-- **The joint form of the star kernels on `L²_0(λ)²`**, compressed to the mean-zero functions:
`⟨f°, K^{st}_E f°⟩ + 2⟨f°, K^{st}_F g°⟩ + ⟨g°, K^{st}_E g°⟩`. -/
noncomputable def qTc (lam : FiniteLaw Ω) (KstE KstF : Ω → Ω → ℝ)
    (v : EuclideanSpace ℝ (Ω ⊕ Ω)) : ℝ :=
  RowsA.stForm lam KstE KstF (cen lam (dewL lam v)) (cen lam (dewR lam v))

/-- The embedding `ιc(Φ, Ψ) = realize(ιΦ, ιΨ)` of `L²(μ)²`. -/
noncomputable def iotaC (lam : FiniteLaw Ω) (I : Ω → Prop) (Φ Ψ : Ω → ℝ) :
    EuclideanSpace ℝ (Ω ⊕ Ω) :=
  realize lam (Cuts.iota lam I Φ) (Cuts.iota lam I Ψ)

theorem dewL_realize (lam : FiniteLaw Ω) (f g : Ω → ℝ) (x : Ω) (hx : lam.weight x ≠ 0) :
    dewL lam (realize lam f g) x = f x := by
  have hs : √(lam.weight x) ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne (lam.nonneg x)
    (Ne.symm hx))).ne'
  simp only [dewL, realize, Sum.elim_inl]
  field_simp

theorem dewR_realize (lam : FiniteLaw Ω) (f g : Ω → ℝ) (x : Ω) (hx : lam.weight x ≠ 0) :
    dewR lam (realize lam f g) x = g x := by
  have hs : √(lam.weight x) ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne (lam.nonneg x)
    (Ne.symm hx))).ne'
  simp only [dewR, realize, Sum.elim_inr]
  field_simp

theorem norm_realize (lam : FiniteLaw Ω) (f g : Ω → ℝ) :
    ‖realize lam f g‖ ^ 2 = nrm lam f ^ 2 + nrm lam g ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    ← ip_self_eq, ← ip_self_eq, Fintype.sum_sum_type]
  simp only [realize, Real.norm_eq_abs, sq_abs, Sum.elim_inl, Sum.elim_inr, ip,
    FiniteLaw.expect]
  congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_ <;>
    rw [mul_pow, Real.sq_sqrt (lam.nonneg x)] <;> ring

/-- **`lem:restriction`(a) gives the hypothesis `hrestr` of `joint_rows_a_gate`.** -/
theorem hrestr_holds (lam : FiniteLaw Ω) (I : Ω → Prop) (hP : 0 < Peyre.prob lam I)
    (KstE KstF : Ω → Ω → ℝ) :
    ∀ Φ Ψ : Ω → ℝ, (Peyre.condLaw lam I hP).expect Φ = 0 →
      (Peyre.condLaw lam I hP).expect Ψ = 0 →
      RowsA.stForm (Peyre.condLaw lam I hP) KstE KstF Φ Ψ =
          qTc lam KstE KstF (iotaC lam I Φ Ψ) / Peyre.prob lam I ∧
        ‖iotaC lam I Φ Ψ‖ ^ 2 =
          nrm (Peyre.condLaw lam I hP) Φ ^ 2 + nrm (Peyre.condLaw lam I hP) Ψ ^ 2 := by
  intro Φ Ψ hΦ hΨ
  set μ := Peyre.condLaw lam I hP
  set P := Peyre.prob lam I
  have hPP : √(P * P) = P := Real.sqrt_mul_self hP.le
  -- `ιΦ`, `ιΨ` are `λ`-centred
  have hcΦ : lam.expect (Cuts.iota lam I Φ) = 0 := by
    rw [Cuts.expect_iota lam I hP, hΦ, mul_zero]
  have hcΨ : lam.expect (Cuts.iota lam I Ψ) = 0 := by
    rw [Cuts.expect_iota lam I hP, hΨ, mul_zero]
  -- the de-weighted components agree with `ιΦ`, `ιΨ` on the support, and so do their centrings
  have hL : ∀ x, lam.weight x ≠ 0 →
      cen lam (dewL lam (iotaC lam I Φ Ψ)) x = Cuts.iota lam I Φ x := by
    intro x hx
    have he : lam.expect (dewL lam (iotaC lam I Φ Ψ)) = lam.expect (Cuts.iota lam I Φ) :=
      expect_congr_supp lam fun y hy => dewL_realize lam _ _ y hy
    simp only [cen, he, hcΦ, sub_zero]
    exact dewL_realize lam _ _ x hx
  have hR : ∀ x, lam.weight x ≠ 0 →
      cen lam (dewR lam (iotaC lam I Φ Ψ)) x = Cuts.iota lam I Ψ x := by
    intro x hx
    have he : lam.expect (dewR lam (iotaC lam I Φ Ψ)) = lam.expect (Cuts.iota lam I Ψ) :=
      expect_congr_supp lam fun y hy => dewR_realize lam _ _ y hy
    simp only [cen, he, hcΨ, sub_zero]
    exact dewR_realize lam _ _ x hx
  -- each kernel form restricts (`lem:restriction`(a))
  have hres : ∀ (K : Ω → Ω → ℝ) (f h : Ω → ℝ),
      kf μ K f h = kf lam K (Cuts.iota lam I f) (Cuts.iota lam I h) / P := by
    intro K f h
    rw [kf_eq_kernelForm, kf_eq_kernelForm, Cuts.kernelForm_cond lam lam I I hP hP, hPP]
  refine ⟨?_, ?_⟩
  · unfold qTc RowsA.stForm
    rw [kf_congr_supp lam KstE hL hL, kf_congr_supp lam KstF hL hR, kf_congr_supp lam KstE hR hR,
      hres, hres, hres]
    ring
  · unfold iotaC
    rw [norm_realize]
    have h1 : nrm lam (Cuts.iota lam I Φ) = nrm μ Φ := Cuts.nrm_iota lam I hP Φ
    have h2 : nrm lam (Cuts.iota lam I Ψ) = nrm μ Ψ := Cuts.nrm_iota lam I hP Ψ
    rw [h1, h2]

variable {m s : Type*} [Fintype m] [DecidableEq m] [Fintype s] [DecidableEq s]

/-- **`lem:joint-rows`(a) for pinned rows**: the rows have the law `μ = λ(· | 𝓘_pin)`, and
`𝕋 = qTc`, `𝕄 = Sector.qMat 𝒵 𝒜 Φ̂`. The hypotheses `hrestr` (`lem:restriction`(a), here
`hrestr_holds`) and `hsector` (the `Φ̂`-sector reduction, `Sector.hsector_holds`) are discharged.
The remaining inputs are:
* `lem:spec:expansion` with `prop:pinned-collision`: `hexpE`, `hexpF` and the bounds;
* `prop:conditional-star`(b),(c): `hdec`, `hV`, `hmean`, for `qTc`;
* `lem:spec:gauss`: `hJ`. -/
theorem joint_rows_a_pinned {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
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
    (qmean : EuclideanSpace ℝ (Ω ⊕ Ω) → ℝ) (J : H → H) (hJ : Sector.CxStruct J)
    (V : EuclideanSpace ℝ (Ω ⊕ Ω) → PiLp 2 (fun _ : m ⊕ s => H))
    {I₀ κ₀ r k eF eE : ℝ}
    (hI₀ : 0 < I₀) (hP : I₀ ≤ Peyre.prob lam I) (hκ₀ : 0 ≤ κ₀) (hr : 0 ≤ r) (hk : 0 < k)
    (heF : 0 ≤ eF) (heE : 0 ≤ eE)
    (Zr : Matrix m m ℝ) (hZ : Zrᵀ = -Zr) (Ar : Matrix m s ℝ)
    (hdec : ∀ x, qTc lam KstE KstF x = κ₀ * r * Sector.qMat Zr Ar J (V x) + qmean x)
    (hV : ∀ x, ‖V x‖ ≤ ‖x‖)
    (hmean : ∀ x, |qmean x| ≤ κ₀ * r * (eF + eE) * ‖x‖ ^ 2)
    (hgate : ((k : ℂ) ^ 2 • (1 : Matrix m m ℂ) + ((k : ℂ) * Complex.I) • RowsA.cplx Zr -
      RowsA.cplx Ar * (RowsA.cplx Ar)ᴴ).PosSemidef) :
    JointBlockLower ν (matchCov (RowsA.relDensity (Peyre.condLaw lam I hPpos) KE g))
      (foldCov ν (RowsA.relDensity (Peyre.condLaw lam I hPpos) KF g))
      (Real.exp ℓ * (κ₀ * r * (k + eF + eE) / I₀ + RowsA.cconst εF SF NF mF +
        RowsA.cconst εE SE NE mE)) :=
  Sector.joint_rows_a_sector (Peyre.condLaw lam I hPpos) ν g ℓ hν hg KE KF KstE KstF TnsE TnsF
    TcollE TcollF hg1 hg2 hexpE hexpF hεE hεE1 hSE0 hSE hnsE hcollE hNE hmE1 hmE2 hεF hεF1 hSF0
    hSF hnsF hcollF hNF hmF1 hmF2 (qTc lam KstE KstF) qmean J hJ V (iotaC lam I)
    (hrestr_holds lam I hPpos KstE KstF) hI₀ hP hκ₀ hr hk heF heE Zr hZ Ar hdec hV hmean hgate

end Restrict

end Sarkozy.JointRows
