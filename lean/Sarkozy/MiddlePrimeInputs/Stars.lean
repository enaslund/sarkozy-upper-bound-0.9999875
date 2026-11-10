module

public import Sarkozy.MiddleCertificates.GraphFacts
public import Sarkozy.Spectral.GlueStars
public import Sarkozy.Spectral.GlueStarOp

/-!
# The star inputs `M_⋆`, `z_⋆` for the middle cuts

`paper/sections/14_spectral.tex`, `lem:star-mean` and `prop:spec2:mucentre`(c3): the inputs
`M_⋆` (in `hcbar`, `hB`) and `z_⋆` (in `hεZc`) of `thm:spectral-criterion`.

For L10 and L21 every column `N(k)` of `ς` has at most two elements (`mid_Nset_card`), so no
support `T` with `|T| ≥ 3` lies in some `N(k)`, and the star coefficients `a_T` vanish there. Then:
* **`starMstar_mid`**: `M_⋆ = 0`;
* **`starZstar_mid`**: `z_⋆ = r²|B_even| ≤ π r²`, with `π = 1` (L10), `6` (L21) the number of
  columns with `|N(k)| = 2`. This is the evaluator's `pairs = ∑_k C(|N(k)|, 2) r²`
  (`layer72_spectral.components`), so `2z_⋆` is at most its share of `ε_Z`.

General lemmas: `starMstar_eq_zero`, `starZstar_eq` (any pinned law, when `a_T = 0` on
`|T| ≥ 3`).
-/

@[expose] public section

namespace Sarkozy.MiddlePrimeInputs

open Finset Sarkozy.MiddleCertificates MiddleCertificates.MidCut Sarkozy.SecondOrder

section General

variable {p : ℕ} [Fact p.Prime] {U K : Type*} [Fintype U] [DecidableEq U] [Fintype K]
  [LinearOrder U]

theorem pivot_zero (L : PinnedHalfLaw p U) (a : Finset U → ℝ)
    (h : ∀ T ∈ supports3 (U := U), a T = 0) (i : U) :
    pivotD2 L supports3 a i = 0 ∧ pivotK L supports3 a i = 0 := by
  have hz : (fun T : pivotGroup (supports3 (U := U)) i => a T.1) = fun _ => 0 := by
    funext T
    exact h T.1 (mem_pivotGroup.mp T.2).1
  unfold pivotD2 pivotK
  rw [hz]
  simp [pivD2, pivK, pivA, pivE, pivU, pivV, pivW, pivX, pivL]

/-- `M_⋆ = 0` when the star coefficients vanish on the supports with `|T| ≥ 3`. -/
theorem starMstar_eq_zero (L : PinnedHalfLaw p U) (N : K → Finset U) (c : K → Finset U → ℝ)
    (h : ∀ T ∈ supports3 (U := U), starCoeff N c T = 0) : Spectral.starMstar L N c = 0 := by
  unfold Spectral.starMstar
  simp [(pivot_zero L _ h _).1, (pivot_zero L _ h _).2]

/-- `z_⋆ = r²|B_even|` when the star coefficients vanish on the supports with `|T| ≥ 3`. -/
theorem starZstar_eq (L : PinnedHalfLaw p U) (N : K → Finset U) (c : K → Finset U → ℝ)
    (h : ∀ T ∈ supports3 (U := U), starCoeff N c T = 0) :
    Spectral.starZstar L N c = (1 / Real.sqrt p) ^ 2 * |starBEven N c| := by
  unfold Spectral.starZstar
  simp [(pivot_zero L _ h _).2]

end General

/-- The number of columns with `|N(k)| = 2`: `1` (L10), `6` (L21). -/
def vPairs : MidCut → ℕ
  | .l10 => 1
  | .l21 => 6

/-- The star coefficients vanish on the supports with `|T| ≥ 3`. -/
theorem starCoeff_three (c : MidCut) {p : ℕ} [Fact p.Prime] :
    ∀ T ∈ supports3 (U := c.data.cut.Half),
      starCoeff c.data.Nset (Spectral.starCoef (p := p) c.data) T = 0 := by
  intro T hT
  unfold starCoeff
  refine sum_eq_zero fun k _ => ?_
  have h3 := supports3_card hT
  have hsub : ¬ T ⊆ c.data.Nset k := fun hs =>
    absurd (le_trans h3 ((card_le_card hs).trans (mid_Nset_card c k))) (by norm_num)
  simp [hsub]

theorem nset_two_count (c : MidCut) :
    (univ.filter (fun k : c.data.cut.Half => (c.data.Nset k).card = 2)).card = vPairs c := by
  rw [SpectralD.Nset_eq_edgeNeighbours c.data c.edge (mem_edge c)]
  cases c <;> decide

/-- `|B_even| ≤ π`. -/
theorem starBEven_le (c : MidCut) {p : ℕ} [Fact p.Prime] :
    |starBEven c.data.Nset (Spectral.starCoef (p := p) c.data)| ≤ vPairs c := by
  unfold starBEven starCoeff
  rw [Finset.sum_comm]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hk : ∀ k : c.data.cut.Half,
      |∑ T ∈ (univ : Finset (Finset c.data.cut.Half)).filter (fun T => 2 ≤ T.card ∧ Even T.card),
        (if T ⊆ c.data.Nset k then Spectral.starCoef (p := p) c.data k T else 0)| ≤
      if (c.data.Nset k).card = 2 then 1 else 0 := by
    intro k
    have hN := mid_Nset_card c k
    -- the only possible support is `T = N(k)`, with `|N(k)| = 2`
    have hsum : ∑ T ∈ (univ : Finset (Finset c.data.cut.Half)).filter
          (fun T => 2 ≤ T.card ∧ Even T.card),
        (if T ⊆ c.data.Nset k then Spectral.starCoef (p := p) c.data k T else 0) =
        if (c.data.Nset k).card = 2 then Spectral.starCoef (p := p) c.data k (c.data.Nset k)
        else 0 := by
      split_ifs with h2
      · rw [sum_eq_single (c.data.Nset k)]
        · simp
        · intro T hT hne
          have hT2 := (mem_filter.mp hT).2.1
          have hsub : ¬ T ⊆ c.data.Nset k := fun hs =>
            hne (eq_of_subset_of_card_le hs (by omega))
          simp [hsub]
        · intro hn
          exact absurd (mem_filter.mpr ⟨mem_univ _, by rw [h2]; decide⟩) hn
      · refine sum_eq_zero fun T hT => ?_
        have hT2 := (mem_filter.mp hT).2.1
        have hsub : ¬ T ⊆ c.data.Nset k := fun hs => by
          have := card_le_card hs
          omega
        simp [hsub]
    rw [hsum]
    split_ifs
    · unfold Spectral.starCoef
      rw [abs_prod]
      refine prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => ?_
      by_cases ha : Spectral.sgnF (p := p) c.data j k = 0
      · simp [ha]
      · rcases quadraticChar_dichotomy ha with h | h <;> simp [h]
    · simp
  calc ∑ k, |∑ T ∈ (univ : Finset (Finset c.data.cut.Half)).filter
          (fun T => 2 ≤ T.card ∧ Even T.card),
        (if T ⊆ c.data.Nset k then Spectral.starCoef (p := p) c.data k T else 0)|
      ≤ ∑ k : c.data.cut.Half, (if (c.data.Nset k).card = 2 then (1 : ℝ) else 0) :=
        sum_le_sum fun k _ => hk k
    _ = vPairs c := by
        rw [sum_boole, nset_two_count]

/-- **`M_⋆ = 0` for L10 and L21** (`lem:star-mean`), for any pinned law. -/
theorem starMstar_mid (c : MidCut) {p : ℕ} [Fact p.Prime] (L : PinnedHalfLaw p c.data.cut.Half) :
    Spectral.starMstar L c.data.Nset (Spectral.starCoef (p := p) c.data) = 0 :=
  starMstar_eq_zero L _ _ (starCoeff_three c)

/-- **`z_⋆ ≤ π r²` for L10 and L21** (`lem:star-mean`), for any pinned law. -/
theorem starZstar_mid (c : MidCut) {p : ℕ} [Fact p.Prime] (L : PinnedHalfLaw p c.data.cut.Half) :
    Spectral.starZstar L c.data.Nset (Spectral.starCoef (p := p) c.data) ≤
      (1 / Real.sqrt p) ^ 2 * vPairs c := by
  rw [starZstar_eq L _ _ (starCoeff_three c)]
  exact mul_le_mul_of_nonneg_left (starBEven_le c) (sq_nonneg _)

end Sarkozy.MiddlePrimeInputs
