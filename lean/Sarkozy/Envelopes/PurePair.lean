module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Positive

@[expose] public section

/-!
# A positive substitute for a pure-pair projection (`lem:oct24:pure-pair-substitute`)

`paper/sections/23_envelopes.tex`, `lem:oct24:pure-pair-substitute`, the operator inequality
`eq:oct24:pure-pair-substitute`.

**Setting (abstract, with the paper's hypotheses).** `E` is a finite-dimensional real inner
product space (in the paper `L²(m)` of an actual half marginal of a prime or a block). Four
subspaces stand for the ranges of the paper's projections:
* `Cst`, the constants (range of `J`);
* `Si`, `Sj`, the functions of `x_i`, of `x_j` (ranges of `P_i`, `P_j`);
* `Sij`, the functions of `(x_i, x_j)` (range of `P_ij`);

with `Cst ≤ Si ≤ Sij` and `Cst ≤ Sj ≤ Sij`, as for functions of coordinates. The paper's
`C_a = P_a - J` is the projection onto `H_a = ran C_a`; here `H_a = S_a ⊓ Cstᗮ`
(`featureSpace`), and `proj_sub_proj_of_le` proves `P_a - J = proj_{H_a}`. The pure-pair space
is `K_ij = ran(P_ij - J) ⊖ (H_i + H_j)` (`pureSpace`). The correlation hypothesis is
`|⟪f, h⟫| ≤ ρ ‖f‖ ‖h‖` for `f ∈ H_i`, `h ∈ H_j`, with `0 ≤ ρ < 1`.

**Main results.**
* `pureSubstitute_form_bounds`: for every `x`,
  `0 ≤ ⟪(Q_ij - Π_ij) x, x⟫ ≤ η ⟪(C_i + C_j) x, x⟫`, `η = 2ρ/(1 - ρ²)`;
* `pureSubstitute_loewner`: the same as Loewner inequalities of operators,
  `Π_ij ≤ Q_ij` and `Q_ij - Π_ij ≤ η (C_i + C_j)`.

The proof is the paper's: the four subspaces `Cst`, `H_i + H_j`, `K_ij`, `Sijᗮ` reduce all the
operators; on `H_i + H_j` the spectrum of `C_i + C_j` lies in `[1 - ρ, 1 + ρ]`
(`gram_upper`, `gram_lower`). The coupling realizations of the second half of the lemma are in
`Sarkozy.Envelopes.Couplings`.
-/

namespace Sarkozy.Envelopes

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The feature space `H_a = ran(P_a - J) = S_a ⊓ Cstᗮ` (`subsec:oct24:pure-features`). -/
noncomputable def featureSpace (Cst S : Submodule ℝ E) : Submodule ℝ E := S ⊓ Cstᗮ

/-- The pure-pair space `K_ij = ran(P_ij - J) ⊖ (H_i + H_j)` (`subsec:oct24:pure-features`). -/
noncomputable def pureSpace (Cst Si Sj Sij : Submodule ℝ E) : Submodule ℝ E :=
  (Sij ⊓ Cstᗮ) ⊓ (featureSpace Cst Si ⊔ featureSpace Cst Sj)ᗮ

/-- The substitute `Q_ij = P_ij - (P_i + P_j)/(1 + ρ) + ((1 - ρ)/(1 + ρ)) J`
(`lem:oct24:pure-pair-substitute`). -/
noncomputable def pureSubstitute (Cst Si Sj Sij : Submodule ℝ E) (ρ : ℝ) : E →L[ℝ] E :=
  Sij.starProjection - (1 + ρ)⁻¹ • (Si.starProjection + Sj.starProjection) +
    ((1 - ρ) / (1 + ρ)) • Cst.starProjection

/-- The constant `η = 2ρ/(1 - ρ²)` of `eq:oct24:pure-pair-substitute`. -/
noncomputable def pairEta (ρ : ℝ) : ℝ := 2 * ρ / (1 - ρ ^ 2)

/-! ### Projection facts -/

theorem inner_proj_self (K : Submodule ℝ E) (x : E) :
    ⟪K.starProjection x, x⟫ = ‖K.starProjection x‖ ^ 2 := by
  have h := K.starProjection_inner_eq_zero x (K.starProjection x) (K.starProjection_apply_mem x)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
  rw [real_inner_comm]
  linarith

theorem inner_proj_of_mem (K : Submodule ℝ E) {c : E} (hc : c ∈ K) (x : E) :
    ⟪c, K.starProjection x⟫ = ⟪c, x⟫ := by
  rw [← K.inner_starProjection_left_eq_right, K.starProjection_eq_self_iff.2 hc]

/-- `P_S - J = proj_{S ⊓ Cstᗮ}` when `Cst ≤ S`: the paper's `C_a = P_a - J` is the projection onto
`H_a`. -/
theorem proj_sub_proj_of_le {Cst S : Submodule ℝ E} (hle : Cst ≤ S) (x : E) :
    S.starProjection x - Cst.starProjection x = (featureSpace Cst S).starProjection x := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · refine Submodule.mem_inf.2 ⟨S.sub_mem (S.starProjection_apply_mem x)
      (hle (Cst.starProjection_apply_mem x)), ?_⟩
    rw [Submodule.mem_orthogonal]
    intro c hc
    rw [inner_sub_right, inner_proj_of_mem S (hle hc), inner_proj_of_mem Cst hc, sub_self]
  · intro w hw
    obtain ⟨hwS, hwC⟩ := Submodule.mem_inf.1 hw
    have e : x - (S.starProjection x - Cst.starProjection x) =
        (x - S.starProjection x) + Cst.starProjection x := by abel
    rw [e, inner_add_left, S.starProjection_inner_eq_zero x w hwS, zero_add]
    exact Submodule.inner_right_of_mem_orthogonal (Cst.starProjection_apply_mem x) hwC

/-- Pythagoras for nested projections: `‖P_S x‖² = ‖J x‖² + ‖(P_S - J) x‖²`. -/
theorem norm_sq_proj_of_le {Cst S : Submodule ℝ E} (hle : Cst ≤ S) (x : E) :
    ‖S.starProjection x‖ ^ 2 =
      ‖Cst.starProjection x‖ ^ 2 + ‖(featureSpace Cst S).starProjection x‖ ^ 2 := by
  rw [← proj_sub_proj_of_le hle x]
  have hmem : S.starProjection x - Cst.starProjection x ∈ Cstᗮ := by
    rw [proj_sub_proj_of_le hle x]
    exact (Submodule.mem_inf.1 ((featureSpace Cst S).starProjection_apply_mem x)).2
  have h0 : ⟪Cst.starProjection x, S.starProjection x - Cst.starProjection x⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (Cst.starProjection_apply_mem x) hmem
  have e : S.starProjection x =
      Cst.starProjection x + (S.starProjection x - Cst.starProjection x) := by abel
  conv_lhs => rw [e]
  rw [norm_add_sq_real, h0, mul_zero, add_zero]

/-! ### The two-subspace Gram bounds -/

/-- **Upper Gram bound.** If `H_i, H_j` have correlation at most `ρ ≥ 0`, then for every `w`,
`‖P_{H_i} w‖² + ‖P_{H_j} w‖² ≤ (1 + ρ) ‖w‖²`, i.e. `C_i + C_j ⪯ (1 + ρ) I`. -/
theorem gram_upper {Hi Hj : Submodule ℝ E} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcor : ∀ f ∈ Hi, ∀ h ∈ Hj, |⟪f, h⟫| ≤ ρ * ‖f‖ * ‖h‖) (w : E) :
    ‖Hi.starProjection w‖ ^ 2 + ‖Hj.starProjection w‖ ^ 2 ≤ (1 + ρ) * ‖w‖ ^ 2 := by
  set a := Hi.starProjection w
  set b := Hj.starProjection w
  set s := ‖a‖ ^ 2 + ‖b‖ ^ 2
  have hs : s = ⟪w, a + b⟫ := by
    rw [inner_add_right, real_inner_comm, inner_proj_self, real_inner_comm, inner_proj_self]
  have hab : |⟪a, b⟫| ≤ ρ * ‖a‖ * ‖b‖ :=
    hcor a (Hi.starProjection_apply_mem w) b (Hj.starProjection_apply_mem w)
  have hnab : ‖a + b‖ ^ 2 ≤ (1 + ρ) * s := by
    rw [norm_add_sq_real]
    have h1 : ⟪a, b⟫ ≤ ρ * ‖a‖ * ‖b‖ := le_trans (le_abs_self _) hab
    have h2 : 2 * (‖a‖ * ‖b‖) ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    nlinarith [mul_le_mul_of_nonneg_left h2 hρ]
  have hcs : s ≤ ‖w‖ * ‖a + b‖ := by
    rw [hs]; exact real_inner_le_norm _ _
  have hs0 : 0 ≤ s := by positivity
  have hsq : s ^ 2 ≤ ‖w‖ ^ 2 * ((1 + ρ) * s) := by
    have := mul_le_mul hcs hcs hs0 (by positivity)
    calc s ^ 2 = s * s := by ring
      _ ≤ ‖w‖ * ‖a + b‖ * (‖w‖ * ‖a + b‖) := this
      _ = ‖w‖ ^ 2 * ‖a + b‖ ^ 2 := by ring
      _ ≤ ‖w‖ ^ 2 * ((1 + ρ) * s) := mul_le_mul_of_nonneg_left hnab (by positivity)
  rcases hs0.lt_or_eq with hpos | hzero
  · have : s * s ≤ ((1 + ρ) * ‖w‖ ^ 2) * s := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]; positivity

/-- **Lower Gram bound.** On `H_i + H_j`, `C_i + C_j ⪰ (1 - ρ) I`: for `w ∈ H_i ⊔ H_j`,
`(1 - ρ) ‖w‖² ≤ ‖P_{H_i} w‖² + ‖P_{H_j} w‖²`. -/
theorem gram_lower {Hi Hj : Submodule ℝ E} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcor : ∀ f ∈ Hi, ∀ h ∈ Hj, |⟪f, h⟫| ≤ ρ * ‖f‖ * ‖h‖) {w : E} (hw : w ∈ Hi ⊔ Hj) :
    (1 - ρ) * ‖w‖ ^ 2 ≤ ‖Hi.starProjection w‖ ^ 2 + ‖Hj.starProjection w‖ ^ 2 := by
  obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 hw
  set w := a' + b'
  set a := Hi.starProjection w
  set b := Hj.starProjection w
  set s := ‖a‖ ^ 2 + ‖b‖ ^ 2
  set t := ‖a'‖ ^ 2 + ‖b'‖ ^ 2
  -- `‖w‖² = ⟪a, a'⟫ + ⟪b, b'⟫`
  have e1 : ⟪w, a'⟫ = ⟪a, a'⟫ := by
    rw [real_inner_comm, ← inner_proj_of_mem Hi ha' w, real_inner_comm]
  have e2 : ⟪w, b'⟫ = ⟪b, b'⟫ := by
    rw [real_inner_comm, ← inner_proj_of_mem Hj hb' w, real_inner_comm]
  have hw2 : ‖w‖ ^ 2 = ⟪a, a'⟫ + ⟪b, b'⟫ := by
    rw [← real_inner_self_eq_norm_sq, ← e1, ← e2, ← inner_add_right]
  have h1 : ⟪a, a'⟫ ≤ ‖a‖ * ‖a'‖ := real_inner_le_norm _ _
  have h2 : ⟪b, b'⟫ ≤ ‖b‖ * ‖b'‖ := real_inner_le_norm _ _
  -- Cauchy–Schwarz in `ℝ²`
  have hcs : (‖a‖ * ‖a'‖ + ‖b‖ * ‖b'‖) ^ 2 ≤ s * t := by
    nlinarith [sq_nonneg (‖a‖ * ‖b'‖ - ‖b‖ * ‖a'‖)]
  have hw0 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have hw4 : (‖w‖ ^ 2) ^ 2 ≤ s * t := by
    have hle : ‖w‖ ^ 2 ≤ ‖a‖ * ‖a'‖ + ‖b‖ * ‖b'‖ := by linarith
    nlinarith
  -- `‖w‖² ≥ (1 - ρ) t`
  have hab : |⟪a', b'⟫| ≤ ρ * ‖a'‖ * ‖b'‖ := hcor a' ha' b' hb'
  have hlow : (1 - ρ) * t ≤ ‖w‖ ^ 2 := by
    have e : ‖w‖ ^ 2 = ‖a'‖ ^ 2 + 2 * ⟪a', b'⟫ + ‖b'‖ ^ 2 := norm_add_sq_real a' b'
    have h3 : -(ρ * ‖a'‖ * ‖b'‖) ≤ ⟪a', b'⟫ := by
      have := neg_abs_le ⟪a', b'⟫
      linarith
    have h4 : 2 * (‖a'‖ * ‖b'‖) ≤ ‖a'‖ ^ 2 + ‖b'‖ ^ 2 := by
      nlinarith [sq_nonneg (‖a'‖ - ‖b'‖)]
    nlinarith [mul_le_mul_of_nonneg_left h4 hρ]
  have hs0 : 0 ≤ s := by positivity
  rcases hw0.lt_or_eq with hpos | hzero
  · -- `(1-ρ) ‖w‖⁴ ≤ (1-ρ) s t ≤ s ‖w‖²`
    have h5 : (1 - ρ) * (‖w‖ ^ 2) ^ 2 ≤ s * ‖w‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hw4 (by linarith : (0 : ℝ) ≤ 1 - ρ)
      have h6 : (1 - ρ) * (s * t) ≤ s * ‖w‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hlow hs0
        linarith
      linarith
    have h7 : ((1 - ρ) * ‖w‖ ^ 2) * ‖w‖ ^ 2 ≤ s * ‖w‖ ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right h7 hpos
  · rw [← hzero]; simp only [mul_zero]; exact hs0

/-! ### The decomposition of `x` -/

section Decomposition

variable {Cst Si Sj Sij : Submodule ℝ E}

omit [FiniteDimensional ℝ E] in
theorem featureSpace_le (hii : Si ≤ Sij) :
    featureSpace Cst Si ≤ Sij ⊓ Cstᗮ :=
  inf_le_inf_right _ hii

/-- `Π_ij x = y - P_N y` with `y = (P_ij - J) x` and `N = H_i + H_j`. -/
theorem pure_proj_eq (hii : Si ≤ Sij) (hjj : Sj ≤ Sij) (x : E) :
    (pureSpace Cst Si Sj Sij).starProjection x =
      (Sij ⊓ Cstᗮ).starProjection x -
        (featureSpace Cst Si ⊔ featureSpace Cst Sj).starProjection
          ((Sij ⊓ Cstᗮ).starProjection x) := by
  set M := Sij ⊓ Cstᗮ
  set N := featureSpace Cst Si ⊔ featureSpace Cst Sj
  have hNM : N ≤ M := sup_le (featureSpace_le hii) (featureSpace_le hjj)
  set y := M.starProjection x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · refine Submodule.mem_inf.2 ⟨M.sub_mem (M.starProjection_apply_mem x)
      (hNM (N.starProjection_apply_mem y)), N.sub_starProjection_mem_orthogonal y⟩
  · intro w hw
    obtain ⟨hwM, hwN⟩ := Submodule.mem_inf.1 hw
    have e : x - (y - N.starProjection y) = (x - y) + N.starProjection y := by abel
    rw [e, inner_add_left, M.starProjection_inner_eq_zero x w hwM, zero_add]
    exact Submodule.inner_right_of_mem_orthogonal (N.starProjection_apply_mem y) hwN

/-- The feature projections of `x` are those of its component `w = P_N y` in `H_i + H_j`. -/
theorem feature_proj_eq (hii : Si ≤ Sij) (hjj : Sj ≤ Sij) {H : Submodule ℝ E}
    (hH : H ≤ featureSpace Cst Si ⊔ featureSpace Cst Sj) (x : E) :
    H.starProjection x =
      H.starProjection ((featureSpace Cst Si ⊔ featureSpace Cst Sj).starProjection
        ((Sij ⊓ Cstᗮ).starProjection x)) := by
  set M := Sij ⊓ Cstᗮ
  set N := featureSpace Cst Si ⊔ featureSpace Cst Sj
  have hNM : N ≤ M := sup_le (featureSpace_le hii) (featureSpace_le hjj)
  set y := M.starProjection x
  have e : x = (x - y) + ((y - N.starProjection y) + N.starProjection y) := by abel
  have h1 : H.starProjection (x - y) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact Submodule.orthogonal_le (hH.trans hNM) (M.sub_starProjection_mem_orthogonal x)
  have h2 : H.starProjection (y - N.starProjection y) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact Submodule.orthogonal_le hH (N.sub_starProjection_mem_orthogonal y)
  conv_lhs => rw [e]
  rw [map_add, map_add, h1, h2, zero_add, zero_add]

end Decomposition

/-! ### The main inequality -/

/-- **`lem:oct24:pure-pair-substitute`, `eq:oct24:pure-pair-substitute` (quadratic forms).**
Let `Cst ≤ S_i ≤ S_ij`, `Cst ≤ S_j ≤ S_ij` (constants, functions of `x_i`, of `x_j`, of
`(x_i, x_j)`), and suppose the correlation of `H_i = S_i ⊖ Cst` and `H_j = S_j ⊖ Cst` is at most
`ρ ∈ [0, 1)`. Then for every `x`, with `Q_ij = pureSubstitute`, `Π_ij` the projection onto
`K_ij`, `C_a = P_a - J` and `η = 2ρ/(1 - ρ²)`,
`0 ≤ ⟪(Q_ij - Π_ij) x, x⟫ ≤ η ⟪(C_i + C_j) x, x⟫`. -/
theorem pureSubstitute_form_bounds {Cst Si Sj Sij : Submodule ℝ E} (hi : Cst ≤ Si)
    (hj : Cst ≤ Sj) (hii : Si ≤ Sij) (hjj : Sj ≤ Sij) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcor : ∀ f ∈ featureSpace Cst Si, ∀ h ∈ featureSpace Cst Sj,
      |⟪f, h⟫| ≤ ρ * ‖f‖ * ‖h‖) (x : E) :
    0 ≤ ⟪(pureSubstitute Cst Si Sj Sij ρ - (pureSpace Cst Si Sj Sij).starProjection) x, x⟫ ∧
      ⟪(pureSubstitute Cst Si Sj Sij ρ - (pureSpace Cst Si Sj Sij).starProjection) x, x⟫ ≤
        pairEta ρ * ⟪((Si.starProjection - Cst.starProjection) +
          (Sj.starProjection - Cst.starProjection)) x, x⟫ := by
  set Hi := featureSpace Cst Si
  set Hj := featureSpace Cst Sj
  set M := Sij ⊓ Cstᗮ
  set N := Hi ⊔ Hj
  set y := M.starProjection x
  set w := N.starProjection y
  set a := Hi.starProjection x
  set b := Hj.starProjection x
  have hHi : Hi ≤ featureSpace Cst Si ⊔ featureSpace Cst Sj := le_sup_left
  have hHj : Hj ≤ featureSpace Cst Si ⊔ featureSpace Cst Sj := le_sup_right
  have ha : a = Hi.starProjection w := feature_proj_eq hii hjj hHi x
  have hb : b = Hj.starProjection w := feature_proj_eq hii hjj hHj x
  -- the forms of the projections
  have fJ : ⟪Cst.starProjection x, x⟫ = ‖Cst.starProjection x‖ ^ 2 := inner_proj_self _ _
  have fij : ⟪Sij.starProjection x, x⟫ = ‖Cst.starProjection x‖ ^ 2 + ‖y‖ ^ 2 := by
    rw [inner_proj_self]
    exact norm_sq_proj_of_le (hi.trans hii) x
  have fi : ⟪Si.starProjection x, x⟫ = ‖Cst.starProjection x‖ ^ 2 + ‖a‖ ^ 2 := by
    rw [inner_proj_self]; exact norm_sq_proj_of_le hi x
  have fj : ⟪Sj.starProjection x, x⟫ = ‖Cst.starProjection x‖ ^ 2 + ‖b‖ ^ 2 := by
    rw [inner_proj_self]; exact norm_sq_proj_of_le hj x
  have hPi : (pureSpace Cst Si Sj Sij).starProjection x = y - w := pure_proj_eq hii hjj x
  have fPi : ⟪(pureSpace Cst Si Sj Sij).starProjection x, x⟫ = ‖y - w‖ ^ 2 := by
    rw [inner_proj_self, hPi]
  -- `‖y‖² = ‖y - w‖² + ‖w‖²`
  have hy : ‖y‖ ^ 2 = ‖y - w‖ ^ 2 + ‖w‖ ^ 2 := by
    have h0 : ⟪y - w, w⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (N.starProjection_apply_mem y)
        (N.sub_starProjection_mem_orthogonal y)
    have e : y = (y - w) + w := by abel
    conv_lhs => rw [e]
    rw [norm_add_sq_real, h0, mul_zero, add_zero]
  -- `C_i x = a`, `C_j x = b`
  have fCi : ⟪(Si.starProjection - Cst.starProjection) x, x⟫ = ‖a‖ ^ 2 := by
    rw [sub_apply, proj_sub_proj_of_le hi x, inner_proj_self]
  have fCj : ⟪(Sj.starProjection - Cst.starProjection) x, x⟫ = ‖b‖ ^ 2 := by
    rw [sub_apply, proj_sub_proj_of_le hj x, inner_proj_self]
  have fC : ⟪((Si.starProjection - Cst.starProjection) +
      (Sj.starProjection - Cst.starProjection)) x, x⟫ = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    rw [add_apply, inner_add_left, fCi, fCj]
  -- the form of `Q - Π`
  have hρ1' : 0 < 1 + ρ := by linarith
  have fQ : ⟪(pureSubstitute Cst Si Sj Sij ρ - (pureSpace Cst Si Sj Sij).starProjection) x, x⟫
      = ‖w‖ ^ 2 - (‖a‖ ^ 2 + ‖b‖ ^ 2) / (1 + ρ) := by
    simp only [pureSubstitute, sub_apply, add_apply,
      smul_apply, inner_sub_left, inner_add_left, real_inner_smul_left]
    rw [fij, fi, fj, fJ, fPi, hy]
    field_simp
    ring
  -- the Gram bounds on `w ∈ H_i + H_j`
  have hwN : w ∈ N := N.starProjection_apply_mem y
  have hU := gram_upper hρ hcor w
  have hL := gram_lower hρ hρ1 hcor hwN
  rw [← ha, ← hb] at hU hL
  rw [fQ, fC]
  refine ⟨?_, ?_⟩
  · rw [sub_nonneg, div_le_iff₀ hρ1']
    linarith
  · have h1ρ : 0 < 1 - ρ := by linarith
    have e : pairEta ρ = 2 * ρ / ((1 - ρ) * (1 + ρ)) := by
      unfold pairEta; congr 1; ring
    rw [e]
    have key : ‖w‖ ^ 2 ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) / (1 - ρ) := by
      rw [le_div_iff₀ h1ρ]; linarith
    have e2 : 2 * ρ / ((1 - ρ) * (1 + ρ)) * (‖a‖ ^ 2 + ‖b‖ ^ 2) =
        (‖a‖ ^ 2 + ‖b‖ ^ 2) / (1 - ρ) - (‖a‖ ^ 2 + ‖b‖ ^ 2) / (1 + ρ) := by
      field_simp
      ring
    rw [e2]
    linarith

omit [FiniteDimensional ℝ E] in
/-- A continuous linear map with a symmetric form is symmetric. -/
theorem isSymmetric_of_form {T : E →L[ℝ] E} (h : ∀ u v, ⟪T u, v⟫ = ⟪u, T v⟫) :
    (T : E →ₗ[ℝ] E).IsSymmetric := fun u v => h u v

/-- The substitute is symmetric. -/
theorem pureSubstitute_form_symm (Cst Si Sj Sij : Submodule ℝ E) (ρ : ℝ) (u v : E) :
    ⟪pureSubstitute Cst Si Sj Sij ρ u, v⟫ = ⟪u, pureSubstitute Cst Si Sj Sij ρ v⟫ := by
  simp only [pureSubstitute, add_apply, sub_apply, smul_apply, inner_add_left,
    inner_sub_left, inner_add_right, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, Submodule.inner_starProjection_left_eq_right]

/-- **`lem:oct24:pure-pair-substitute`, `eq:oct24:pure-pair-substitute` (Loewner order).**
`0 ⪯ Q_ij - Π_ij ⪯ η (C_i + C_j)` in Mathlib's Loewner order on `E →L[ℝ] E`, under the
hypotheses of `pureSubstitute_form_bounds`. -/
theorem pureSubstitute_loewner {Cst Si Sj Sij : Submodule ℝ E} (hi : Cst ≤ Si)
    (hj : Cst ≤ Sj) (hii : Si ≤ Sij) (hjj : Sj ≤ Sij) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcor : ∀ f ∈ featureSpace Cst Si, ∀ h ∈ featureSpace Cst Sj,
      |⟪f, h⟫| ≤ ρ * ‖f‖ * ‖h‖) :
    (pureSpace Cst Si Sj Sij).starProjection ≤ pureSubstitute Cst Si Sj Sij ρ ∧
      pureSubstitute Cst Si Sj Sij ρ - (pureSpace Cst Si Sj Sij).starProjection ≤
        pairEta ρ • ((Si.starProjection - Cst.starProjection) +
          (Sj.starProjection - Cst.starProjection)) := by
  have hb := pureSubstitute_form_bounds hi hj hii hjj hρ hρ1 hcor
  have hsQ := pureSubstitute_form_symm Cst Si Sj Sij ρ
  have hsP := Submodule.inner_starProjection_left_eq_right (pureSpace Cst Si Sj Sij)
  have hsi := Submodule.inner_starProjection_left_eq_right Si
  have hsj := Submodule.inner_starProjection_left_eq_right Sj
  have hsc := Submodule.inner_starProjection_left_eq_right Cst
  refine ⟨?_, ?_⟩
  · rw [ContinuousLinearMap.le_def]
    refine ⟨isSymmetric_of_form fun u v => ?_, fun x => ?_⟩
    · simp only [sub_apply, inner_sub_left, inner_sub_right]
      rw [hsQ u v, hsP u v]
    · simp only [ContinuousLinearMap.reApplyInnerSelf, RCLike.re_to_real]
      exact (hb x).1
  · rw [ContinuousLinearMap.le_def]
    refine ⟨isSymmetric_of_form fun u v => ?_, fun x => ?_⟩
    · simp only [sub_apply, add_apply, smul_apply, inner_sub_left, inner_sub_right,
        inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
      rw [hsQ u v, hsP u v, hsi u v, hsj u v, hsc u v]
    · have := (hb x).2
      simp only [ContinuousLinearMap.reApplyInnerSelf, RCLike.re_to_real, sub_apply,
        smul_apply, inner_sub_left, real_inner_smul_left] at this ⊢
      linarith

end Sarkozy.Envelopes
