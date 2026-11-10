module

public import Sarkozy.OpsCore.LeadBlock

@[expose] public section

/-!
# The split of the skew fold difference at a middle block (`prop:signed-bounds`(b)) (OPS-L)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(b): `Skew D_{t,𝔅} = L_{t,𝔅} + R_{t,𝔅}`
with `L_{t,𝔅}` the leading stars `L°_{t,p}` on the singleton sectors, `‖L_{t,𝔅}‖ ≤ ℓ_t b^{-1/2}` and
`‖R_{t,𝔅}‖ ≤ a_F/b`.

FD's `fold_skew0` bounds the skew form `skwK` of the block difference of the fold `F₁` jointly, in
`L²(m_{0,𝔅})` of the object triples (`mform` of the block law `lawF`). Here, with the prime split
`SkewSplitPrime` (from PG's `NewDecomp`, `skewSplit_block`) and the sector assembly
(`mix_change_sub_le`, `singForm_le`):

* **`foldLead`**: the block leading form `L_{t,𝔅}(φ, ψ) = ∑_p L^m_{t,p}(comp_p φ, comp_p ψ)`;
* **`fold_skew_split`**: `|skwK(φ, ψ) − L_{t,𝔅}(φ, ψ)| ≤ e_R ‖φ‖ ‖ψ‖` and
  `|L_{t,𝔅}(φ, ψ)| ≤ ℓ' ‖φ‖ ‖ψ‖` in `L²(m_{0,𝔅})`, for any `e_R ≥ (1 + t)ρ²` above the prime
  remainders and `ℓ'` above the prime leading stars;
* **`recordLead`**, **`foldChange_skew_split`**: the same for the skew change of the fold record
  `F_{j+1}` itself (B8's `foldChange … .skew`), in its own cut form on the half labellings and
  `L²(mOf)` (FD's `form_fold_skew`, `hsq_fold`); for `F₂` the leading form is the reflected one
  (`prop:signed-bounds`(e), FD's `skwK_refl`). This is (N1)–(N2) for the fold records in form
  language: `|Q_{ζ^a}(F, G) − Lead(F, G)| ≤ e_R ‖F‖ ‖G‖`, `|Lead(F, G)| ≤ ℓ' ‖F‖ ‖G‖`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.FoldSymSkew Sarkozy.PrimeGram Sarkozy.NormBoundsPaper4 Sarkozy.SignedGram
  Sarkozy.PartV Sarkozy.SignedComponents Sarkozy.SignedDecomp Sarkozy.IndexSupport Sarkozy.Mixing
open Sarkozy.MiddleComparison (signedCoef)
open Sarkozy.MainFinal2 (tPaper)
open Sarkozy.NormBoundsPaper2 (ip)
open Sarkozy.PartVRecords Sarkozy.MiddleComparison

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

/-- The leading star form at one prime vanishes at zero. -/
theorem lForm_zero {F : Type} [Field F] [Fintype F] [DecidableEq F] (m : (Fin 3 → F) → ℝ)
    (t : ℝ) : lForm m t 0 0 = 0 := by
  have hadj : ∀ S, adj m S (0 : (Fin 3 → F) → ℝ) = 0 := fun S => by
    funext x
    simp [adj, cen, mip]
  have hB : ∀ i, Ba m i (0 : (Fin 3 → F) → ℝ) = 0 := fun i => by
    funext x
    simp [Ba, hadj]
  have hW : Wa m (0 : (Fin 3 → F) → ℝ) = 0 := by
    funext x
    simp [Wa, hadj]
  unfold lForm
  simp [hB, hW, uip]

/-- **The leading star of the fold record at a block** (`L_{t,𝔅}` of `prop:signed-bounds`(b)):
the prime leading stars `L^m_{t,p}` placed on the singleton sectors. -/
noncomputable def foldLead (hne : MiddleNonempty pr) (t : ℝ) (x₀ : ∀ i, Ai pr i)
    (φ ψ : (∀ i, Ai pr i) → ℝ) : ℝ :=
  singForm (mP hne) x₀ (fun i => lForm (mP hne i) t) φ ψ

omit [Fintype ι] [DecidableEq ι] in
theorem SkewSplitPrime.mono {hne : MiddleNonempty pr} {C : FoldComponents pr hne}
    {t ℓ' ρ ℓ'' ρ' : ℝ}
    {i : ι} (h : SkewSplitPrime hne C t ℓ' ρ i) (hℓ : ℓ' ≤ ℓ'') (hρ : ρ ≤ ρ') :
    SkewSplitPrime hne C t ℓ'' ρ' i := by
  intro u v hu hv
  obtain ⟨h1, h2⟩ := h u v hu hv
  have hsu := Real.sqrt_nonneg (∑ a, mP hne i a * u a ^ 2)
  have hsv := Real.sqrt_nonneg (∑ a, mP hne i a * v a ^ 2)
  exact ⟨h1.trans (by gcongr), h2.trans (by gcongr)⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **The prime split at uniform block constants**: from `skewSplit_block`, if every
`r_p = p^{-1/2}` is at most `τ` (e.g. `τ = b^{-1/2}` at the least prime), then
`SkewSplitPrime … (ℓ τ) (a_F τ²)` at every prime. -/
theorem skewSplit_unif (hne : MiddleNonempty pr) (C : FoldComponents pr hne)
    (h3 : ∀ i, pr i % 4 = 3) (k : Fin 33) (hXp : ∀ i, XQ k ≤ pr i) {E aF ℓ τ : ℝ}
    (hnew : ∀ i, NewDecomp (mP hne i) (∑ c, signedCoef tPaper c • compP hne C c i) tPaper E)
    (haF : E ≤ aF) (hℓ : ((aNU * gamX k : ℚ) : ℝ) ≤ ℓ) (hℓ0 : 0 ≤ ℓ) (haF0 : 0 ≤ aF)
    (hτ : ∀ i, rP pr i ≤ τ) (i : ι) : SkewSplitPrime hne C tPaper (ℓ * τ) (aF * τ ^ 2) i := by
  have hr0 : 0 ≤ rP pr i := inv_nonneg.mpr (Real.sqrt_nonneg _)
  refine (skewSplit_block hne C h3 k hXp hnew haF hℓ i).mono
    (mul_le_mul_of_nonneg_left (hτ i) hℓ0) (mul_le_mul_of_nonneg_left ?_ haF0)
  exact pow_le_pow_left₀ hr0 (hτ i) 2

/-- **`prop:signed-bounds`(b) for `F₁`, with the leading star split off** (Step 4 of its proof
with `rem:signed-mixture-sectors`): in `L²(m_{0,𝔅})`,
`|Skew D_{t,𝔅}(φ, ψ) − L_{t,𝔅}(φ, ψ)| ≤ e_R ‖φ‖ ‖ψ‖` and `|L_{t,𝔅}(φ, ψ)| ≤ ℓ' ‖φ‖ ‖ψ‖`. -/
theorem fold_skew_split (hne : MiddleNonempty pr) (C : FoldComponents pr hne) {t ρ eR ℓ' : ℝ}
    (ht : 0 ≤ t) (heR : 0 ≤ eR) (hℓ' : 0 ≤ ℓ') (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) ρ) (hmulti : (1 + t) * ρ ^ 2 ≤ eR)
    (hsplit : ∀ i, SkewSplitPrime hne C t ℓ' eR i) (x₀ : ∀ i, Ai pr i)
    (φ ψ : (Fin 3 → BlockLabel pr) → ℝ) :
    |skwK pr (newW C t 0) φ ψ - foldLead hne t x₀ (ex φ) (ex ψ)| ≤
        eR * Real.sqrt (mform (lawF pr hne).weight φ) *
          Real.sqrt (mform (lawF pr hne).weight ψ) ∧
      |foldLead hne t x₀ (ex φ) (ex ψ)| ≤
        ℓ' * Real.sqrt (mform (lawF pr hne).weight φ) *
          Real.sqrt (mform (lawF pr hne).weight ψ) := by
  rw [skwK_dot, mform_ip, mform_ip]
  have hd : ∀ i, CentredNorm (mP hne i) (oldP hne i) 1 := fun i =>
    centredNorm_one (oldP_nonneg i) (mP_nonneg hne i) ((oldP_coupling hne).row i)
      ((oldP_coupling hne).col i)
  refine ⟨?_, singForm_le (mP_nonneg hne) (mP_total hne) x₀ _ (fun i => lForm_zero _ t) hℓ'
    (fun i u v hu hv => (hsplit i u v hu hv).2) _ _⟩
  refine mix_change_sub_le (mP_nonneg hne) (mP_total hne) (compP_coupling hne C)
    (oldP_coupling hne) (compP_nonneg C) oldP_nonneg (by norm_num) hρ0 hρ1
    zero_le_one le_rfl hρ hd heR ?_ _ (fun i => lForm_zero _ t)
    (fun i u v hu hv => (hsplit i u v hu hv).1) x₀ _ _
  rw [sum_abs_signedCoef ht]
  norm_num
  linarith

section Record

variable (pr) (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- **The leading form of the skew change of the fold record `F_{j+1}`** on the half labellings:
`F₁`: `L_{t,𝔅}` read through the fold; `F₂`: the reflected form (`prop:signed-bounds`(e)). -/
noncomputable def recordLead (t : ℝ) (x₀ : ∀ i, Ai pr i) :
    Fin 2 → ((reservedCut.Half → BlockLabel pr) → ℝ) → ((reservedCut.Half → BlockLabel pr) → ℝ) → ℝ
  | 0 => fun F G => foldLead hne t x₀ (ex (fr pr 0 F)) (ex (fr pr 0 G))
  | 1 => fun F G => foldLead hne t x₀ (ex fun x => fr pr 1 G (rf x)) (ex fun x => fr pr 1 F (rf x))

/-- **(N1)–(N2) for the fold records, in form language** (`prop:signed-bounds`(b),(e)): the skew
change `ζ^a` of `F_{j+1}` and its leading form satisfy
`|Q_{ζ^a}(F, G) − Lead_j(F, G)| ≤ e_R ‖F‖ ‖G‖` and `|Lead_j(F, G)| ≤ ℓ' ‖F‖ ‖G‖` in `L²(mOf)`,
from the prime split (`SkewSplitPrime`) and the component norms (`F₂` for reflected components). -/
theorem foldChange_skew_split (C : FoldComponents pr hne) (hC : Reflected C) {t ρ eR ℓ' : ℝ}
    (ht : 0 ≤ t) (heR : 0 ≤ eR) (hℓ' : 0 ≤ ℓ') (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) ρ) (hmulti : (1 + t) * ρ ^ 2 ≤ eR)
    (hsplit : ∀ i, SkewSplitPrime hne C t ℓ' eR i) (x₀ : ∀ i, Ai pr i) (j : Fin 2)
    (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    |reservedCut.form (foldChange pr h hne root W I hr b C t (.inl j) .skew) F G -
        recordLead pr hne t x₀ j F G| ≤
        eR * Real.sqrt (hsq reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl j)) F) *
          Real.sqrt (hsq reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl j)) G) ∧
      |recordLead pr hne t x₀ j F G| ≤
        ℓ' * Real.sqrt (hsq reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl j)) F) *
          Real.sqrt (hsq reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl j)) G) := by
  rw [form_fold_skew, hsq_fold, hsq_fold]
  fin_cases j
  · exact fold_skew_split hne C ht heR hℓ' hρ0 hρ1 hρ hmulti hsplit x₀ _ _
  · change |skwK pr (newW C t 1) (fr pr 1 F) (fr pr 1 G) -
        foldLead hne t x₀ (ex fun x => fr pr 1 G (rf x)) (ex fun x => fr pr 1 F (rf x))| ≤
          eR * Real.sqrt (mform (lawF pr hne).weight (fr pr 1 F)) *
            Real.sqrt (mform (lawF pr hne).weight (fr pr 1 G)) ∧
      |foldLead hne t x₀ (ex fun x => fr pr 1 G (rf x)) (ex fun x => fr pr 1 F (rf x))| ≤
          ℓ' * Real.sqrt (mform (lawF pr hne).weight (fr pr 1 F)) *
            Real.sqrt (mform (lawF pr hne).weight (fr pr 1 G))
    rw [skwK_refl hC]
    have k := fold_skew_split hne C ht heR hℓ' hρ0 hρ1 hρ hmulti hsplit x₀
      (fun x => fr pr 1 G (rf x)) (fun x => fr pr 1 F (rf x))
    rw [mform_rf, mform_rf] at k
    obtain ⟨k1, k2⟩ := k
    exact ⟨k1.trans (le_of_eq (by ring)), k2.trans (le_of_eq (by ring))⟩

end Record

end Sarkozy.OpsCore
