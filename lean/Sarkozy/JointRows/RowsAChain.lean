module

public import Sarkozy.JointRows.RowsA

/-!
# `lem:joint-rows`(a): restriction, pure stars and the assembled bound

Source: `paper/sections/16_extraction.tex`, `lem:joint-rows`(a), proof: "Restriction",
"Pure stars", and the combination of the three steps into `𝔨_p`.

* `stForm`: the form of the joint block `𝕂^{st}` of the operators `P₀K^{st}_•P₀` at `(Φ, Ψ)`.
* `joint_rows_chain`: if the joint block `𝕋` of the star operators of `prop:conditional-star`
  (a quadratic form `qT` on a real inner product space) satisfies `𝕋 ⪰ -c'I`, then the joint
  block of `(C_E, C_F)` satisfies `⪰ -e^{ℓ_E}(c'/I₀ + 𝔠_F + 𝔠_E) I` on `L²(ν) ⊕ L²(ν)`. This is
  the actual chart, centring and normalization (`RowsA.lean`) and the restriction step
  (`lem:restriction`(a) as the hypothesis `hrestr`).
* `pure_star_bound`: `𝕋 = κ₀r 𝒲𝕄𝒲* + 𝕋_mean` (in form: `qT x = κ₀r qM(𝒲*x) + qmean x`) with
  `𝒲*` a contraction, `‖𝕋_mean‖ ≤ κ₀r(e_F + e_E)` and `𝕄 ⪰ -𝗄I` give
  `𝕋 ⪰ -κ₀r(𝗄 + e_F + e_E)I` (`prop:conditional-star`(b),(c) as the hypotheses).
* **`joint_rows_a`**: `lem:joint-rows`(a),
  `(C_E C_F; C_F* C_E) ⪰ -𝔨_p I`, `𝔨_p = e^{ℓ_E}[κ₀r(𝗄 + e_F + e_E)/I₀ + 𝔠_F + 𝔠_E]`, from
  `𝕄 ⪰ -𝗄I`; `RowsAGate.lean` derives `𝕄 ⪰ -𝗄I` from the gate `eq:joint-gate`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

namespace RowsA

variable {Ω : Type*} [Fintype Ω]

/-- The form of the joint block `𝕂^{st}` of `(P₀K^{st}_EP₀, P₀K^{st}_FP₀)` at `(Φ, Ψ)`. -/
noncomputable def stForm (μ : FiniteLaw Ω) (KstE KstF : Ω → Ω → ℝ) (Φ Ψ : Ω → ℝ) : ℝ :=
  kf μ KstE Φ Φ + 2 * kf μ KstF Φ Ψ + kf μ KstE Ψ Ψ

theorem cconst_nonneg {ε S N m : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hS : 0 ≤ S) (hN : 0 ≤ N) :
    0 ≤ cconst ε S N m := by
  unfold cconst
  have : 0 < 1 - ε := by linarith
  positivity

/-- **The chain of `lem:joint-rows`(a)**: actual chart, centring, normalization and restriction.
If `𝕋 ⪰ -c'I`, the joint block of `(C_E, C_F)` is `⪰ -e^{ℓ_E}(c'/I₀ + 𝔠_F + 𝔠_E) I`. -/
theorem joint_rows_chain {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ ν : FiniteLaw Ω) (g : Ω → ℝ) (ℓ : ℝ)
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
    (qT : E → ℝ) (ι : (Ω → ℝ) → (Ω → ℝ) → E) {P I₀ c' : ℝ}
    (hrestr : ∀ Φ Ψ : Ω → ℝ, μ.expect Φ = 0 → μ.expect Ψ = 0 →
      stForm μ KstE KstF Φ Ψ = qT (ι Φ Ψ) / P ∧ ‖ι Φ Ψ‖ ^ 2 = nrm μ Φ ^ 2 + nrm μ Ψ ^ 2)
    (hI₀ : 0 < I₀) (hP : I₀ ≤ P) (hc' : 0 ≤ c') (hT : ∀ x, -c' * ‖x‖ ^ 2 ≤ qT x) :
    JointBlockLower ν (matchCov (relDensity μ KE g)) (foldCov ν (relDensity μ KF g))
      (Real.exp ℓ * (c' / I₀ + cconst εF SF NF mF + cconst εE SE NE mE)) := by
  intro f h
  have hgpos : ∀ x, μ.weight x ≠ 0 → 0 < g x := fun x hx =>
    lt_of_lt_of_le (Real.exp_pos _) (hg x hx)
  rw [kf_matchCov_chart μ ν g hν hgpos KE hg1 hg2, kf_foldCov_chart μ ν g hν hgpos KF,
    kf_matchCov_chart μ ν g hν hgpos KE hg1 hg2]
  set a := nrm μ f
  set b := nrm μ h
  have ha : 0 ≤ a := FiveType.nrm_nonneg _ _
  have hb : 0 ≤ b := FiveType.nrm_nonneg _ _
  -- the three normalization errors
  have eEf := row_error_bound μ KE KstE TnsE TcollE hexpE hεE hεE1 hSE0 hSE hnsE hcollE hNE
    hmE1 hmE2 f f
  have eEh := row_error_bound μ KE KstE TnsE TcollE hexpE hεE hεE1 hSE0 hSE hnsE hcollE hNE
    hmE1 hmE2 h h
  have eF := row_error_bound μ KF KstF TnsF TcollF hexpF hεF hεF1 hSF0 hSF hnsF hcollF hNF
    hmF1 hmF2 f h
  set cE := cconst εE SE NE mE
  set cF := cconst εF SF NF mF
  have hcE : 0 ≤ cE := cconst_nonneg (le_trans (abs_nonneg _) hεE) hεE1 hSE0
    (le_trans (add_nonneg (FormBound.nonneg' hnsE) (FormBound.nonneg' hcollE)) hNE)
  have hcF : 0 ≤ cF := cconst_nonneg (le_trans (abs_nonneg _) hεF) hεF1 hSF0
    (le_trans (add_nonneg (FormBound.nonneg' hnsF) (FormBound.nonneg' hcollF)) hNF)
  -- restriction: `𝕂^{st} ⪰ -(c'/I₀) I`
  have hst : -(c' / I₀) * (a ^ 2 + b ^ 2) ≤ stForm μ KstE KstF (cen μ f) (cen μ h) := by
    obtain ⟨h1, h2⟩ := hrestr (cen μ f) (cen μ h) (expect_cen μ f) (expect_cen μ h)
    have hP0 : 0 < P := lt_of_lt_of_le hI₀ hP
    have hq := hT (ι (cen μ f) (cen μ h))
    rw [h2] at hq
    have hca := nrm_cen_le μ f
    have hcb := nrm_cen_le μ h
    have hsq : nrm μ (cen μ f) ^ 2 + nrm μ (cen μ h) ^ 2 ≤ a ^ 2 + b ^ 2 := by
      have := FiveType.nrm_nonneg μ (cen μ f)
      have := FiveType.nrm_nonneg μ (cen μ h)
      nlinarith
    rw [h1, le_div_iff₀ hP0]
    have hcP : c' ≤ c' / I₀ * P := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hI₀]
      exact mul_le_mul_of_nonneg_left hP hc'
    have hss : 0 ≤ a ^ 2 + b ^ 2 := by positivity
    have m1 := mul_le_mul_of_nonneg_left hsq hc'
    have m2 := mul_le_mul_of_nonneg_right hcP hss
    have e1 : -(c' / I₀) * (a ^ 2 + b ^ 2) * P = -(c' / I₀ * P * (a ^ 2 + b ^ 2)) := by ring
    rw [e1]
    linarith
  unfold stForm at hst
  -- combine
  have hab : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have l1 := neg_abs_le (kf μ (chartKernel μ KE) f f - kf μ KstE (cen μ f) (cen μ f))
  have l2 := neg_abs_le (kf μ (chartKernel μ KF) f h - kf μ KstF (cen μ f) (cen μ h))
  have l3 := neg_abs_le (kf μ (chartKernel μ KE) h h - kf μ KstE (cen μ h) (cen μ h))
  have hK : -(c' / I₀ + cF + cE) * (a ^ 2 + b ^ 2) ≤
      kf μ (chartKernel μ KE) f f + 2 * kf μ (chartKernel μ KF) f h +
        kf μ (chartKernel μ KE) h h := by
    have m1 : cF * (2 * (a * b)) ≤ cF * (a ^ 2 + b ^ 2) := mul_le_mul_of_nonneg_left hab hcF
    have e2 : -(c' / I₀ + cF + cE) * (a ^ 2 + b ^ 2) =
        -(c' / I₀) * (a ^ 2 + b ^ 2) - cF * (a ^ 2 + b ^ 2) - (cE * a * a + cE * b * b) := by ring
    rw [e2]
    have e3 : cF * (2 * (a * b)) = 2 * (cF * a * b) := by ring
    rw [e3] at m1
    linarith [eEf, eEh, eF, l1, l2, l3, m1, hst]
  -- `‖·‖_μ ≤ e^{ℓ} ‖·‖_ν`
  have n1 := nrm_sq_le_of_density μ ν g ℓ hν hg f
  have n2 := nrm_sq_le_of_density μ ν g ℓ hν hg h
  have hcoef : 0 ≤ c' / I₀ + cF + cE := by
    have : 0 ≤ c' / I₀ := div_nonneg hc' hI₀.le
    linarith
  have hfin : (c' / I₀ + cF + cE) * (a ^ 2 + b ^ 2) ≤
      (c' / I₀ + cF + cE) * (Real.exp ℓ * (nrm ν f ^ 2 + nrm ν h ^ 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) hcoef
  have e4 : -(Real.exp ℓ * (c' / I₀ + cF + cE)) * (nrm ν f ^ 2 + nrm ν h ^ 2) =
      -((c' / I₀ + cF + cE) * (Real.exp ℓ * (nrm ν f ^ 2 + nrm ν h ^ 2))) := by ring
  rw [e4]
  linarith [hK, hfin]

/-- **Pure stars**: `𝕋 = κ₀r 𝒲𝕄𝒲* + 𝕋_mean` with a contraction `𝒲*`,
`‖𝕋_mean‖ ≤ κ₀r(e_F + e_E)` and `𝕄 ⪰ -𝗄I` give `𝕋 ⪰ -κ₀r(𝗄 + e_F + e_E)I`, in form:
`qT x = ⟨x, 𝕋x⟩`,
`qM y = ⟨y, 𝕄y⟩`, `qmean x = ⟨x, 𝕋_mean x⟩`, `V = 𝒲*`. -/
theorem pure_star_bound {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (qT qmean : E → ℝ) (qM : F → ℝ) (V : E → F) {κ₀ r k eF eE : ℝ} (hκr : 0 ≤ κ₀ * r)
    (hk : 0 ≤ k) (hdec : ∀ x, qT x = κ₀ * r * qM (V x) + qmean x) (hV : ∀ x, ‖V x‖ ≤ ‖x‖)
    (hmean : ∀ x, |qmean x| ≤ κ₀ * r * (eF + eE) * ‖x‖ ^ 2) (hM : ∀ y, -k * ‖y‖ ^ 2 ≤ qM y)
    (x : E) : -(κ₀ * r * (k + eF + eE)) * ‖x‖ ^ 2 ≤ qT x := by
  rw [hdec]
  have h1 := hM (V x)
  have h2 : ‖V x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have := norm_nonneg (V x)
    nlinarith [hV x]
  have h3 : -k * ‖x‖ ^ 2 ≤ qM (V x) := by nlinarith
  have h4 := mul_le_mul_of_nonneg_left h3 hκr
  have h5 := neg_abs_le (qmean x)
  nlinarith [hmean x]

/-- **`lem:joint-rows`(a)**: the joint block of `(C_E, C_F)` on `L²(ν) ⊕ L²(ν)` is `⪰ -𝔨_p I`,
`𝔨_p = e^{ℓ_E}[κ₀r(𝗄 + e_F + e_E)/I₀ + 𝔠_F + 𝔠_E]`, `𝔠_• = (ε_•S⋆_• + N_•)/(1 - ε_•) +
m_•²/(1 - ε_•)²`. The inputs `lem:spec:expansion`, `prop:pinned-collision` (`hexpE`, `hexpF` and
the bounds), `lem:restriction`(a) (`hrestr`) and `prop:conditional-star`(b),(c) (`hdec`, `hV`,
`hmean`) are hypotheses; `𝕄 ⪰ -𝗄I` (`hM`) follows from the gate `eq:joint-gate`
(`RowsAGate.lean`). -/
theorem joint_rows_a {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
    (hI₀ : 0 < I₀) (hP : I₀ ≤ P) (hκ₀ : 0 ≤ κ₀) (hr : 0 ≤ r) (hk : 0 ≤ k) (heF : 0 ≤ eF)
    (heE : 0 ≤ eE)
    (hdec : ∀ x, qT x = κ₀ * r * qM (V x) + qmean x) (hV : ∀ x, ‖V x‖ ≤ ‖x‖)
    (hmean : ∀ x, |qmean x| ≤ κ₀ * r * (eF + eE) * ‖x‖ ^ 2) (hM : ∀ y, -k * ‖y‖ ^ 2 ≤ qM y) :
    JointBlockLower ν (matchCov (relDensity μ KE g)) (foldCov ν (relDensity μ KF g))
      (Real.exp ℓ * (κ₀ * r * (k + eF + eE) / I₀ + cconst εF SF NF mF + cconst εE SE NE mE)) :=
  joint_rows_chain μ ν g ℓ hν hg KE KF KstE KstF TnsE TnsF TcollE TcollF hg1 hg2 hexpE hexpF
    hεE hεE1 hSE0 hSE hnsE hcollE hNE hmE1 hmE2 hεF hεF1 hSF0 hSF hnsF hcollF hNF hmF1 hmF2
    qT ι hrestr hI₀ hP (by positivity)
    (pure_star_bound qT qmean qM V (mul_nonneg hκ₀ hr) hk hdec hV hmean hM)

end RowsA

end Sarkozy.JointRows
