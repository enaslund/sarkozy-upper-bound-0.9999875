module

public import Sarkozy.NormBoundsPaper4.FoldCut
public import Sarkozy.NormBoundsPaper3.Final
public import Sarkozy.SignedDecomp.Block
public import Sarkozy.SignedGram.Sanity
public import Sarkozy.NormBoundsPaper4.FoldCol

@[expose] public section

/-!
# The fold norm families `Fs`, `Fa` from the one-prime bounds (FD)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(a),(b),(e) and Step 4 of its proof,
from (c) at one prime.

* **`FoldPrimeBound μ P C w α₁ α₂ β e`**: the one-prime statement `|mixChg1 …| ≤ e ‖u‖‖v‖` on
  `μ`-mean-zero functions. At `(½, ½, 1)` it is `‖D^s_{t,p}‖ ≤ e`, at `(½, −½, 0)` it is
  `‖D^a_{t,p}‖ ≤ e`, for the prime record difference `D_{t,p} = T[K_{t,p}] − T_old` on `L²(m₀)`
  (`prop:signed-bounds`(c): `‖D^s‖ ≤ s_p q`, `‖D^a − L°‖ ≤ a_p q`, `‖L°‖ ≤ ℓ_t r`).
* **`fold_sym0`**, **`fold_skew0`**: the block bound for `F₁` (`mix_change_le`): on singleton
  sectors the prime bound, on sectors of `≥ 2` primes `(1 + t)ρ² + d²` (symmetric) resp.
  `(1 + t)ρ²` (skew; the old record is symmetric, so no reference norm is needed), with `ρ`, `d`
  the prime centred norms of the components and of `K_{0,p}`.
* **`fold_sym`**, **`fold_skew`**: `FormBound` of the changes of both folds (`F₂` by
  `prop:signed-bounds`(e), `symK_refl`, `skwK_refl`, for reflected components).
* **`fold_check`** (`decide +kernel`): `(Γ_X + e_o r_X)² + (1 + t)c_+(X)² ≤ s_F(X_i)` and
  `(1 + t)c_+(X)² ≤ a_F(X_i)` at the 33 piece starts, with SD2's rational majorants `gamX`,
  `cpX`, `e_o` at the crude collision constant `73` (`eo73`), and the table `paperKappa` (the
  paper's `c_{≥2} ≤ s_F`, `a_F`).
* **`fold_paper`**: HN's/NB3's two fold fields (`NormBoundsRest4`) at `s_F r_b²` and
  `ℓ r_b + a_F r_b²` on a middle block of piece `k`, from
  - the one-prime bounds at `s_F p^{-1}` and `ℓ p^{-1/2} + a_F p^{-1}` (`prop:signed-bounds`(c));
  - the component centred norms `c_+ r` (`prop:signed-bounds`(c), Step 1, at the paper's
    constant; SD2's `AnalyticAt.comp`).
  The reference centred norm `(Γ_A + e_o r) r` is proved (PG's `oldDecomp_block`,
  `centredNorm_of_decomp`, with the crude collision bound `collisionBound_73` of `FoldCol`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper4

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.SignedComponents
open Sarkozy.IndexSupport Sarkozy.Mixing Sarkozy.SignedGram Sarkozy.PrimeGram
open Sarkozy.SignedDecomp
open Sarkozy.NormBoundsPaper2 (ip)
open Sarkozy.NormBoundsPaper3 (NormBoundsRest4)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg)
open Sarkozy.HsumProof (kSF kAF)

/-! ## The one-prime statement -/

section Prime

variable {B : Type} [Fintype B]

/-- **The one-prime bound of a signed fold difference** (`prop:signed-bounds`(c) as a
statement): on `μ`-mean-zero functions, `|mixChg1 P C w α₁ α₂ β u v| ≤ e ‖u‖_μ ‖v‖_μ`. -/
def FoldPrimeBound (μ : B → ℝ) (P : Fin 3 → Matrix B B ℝ) (C₀ : Matrix B B ℝ) (w : Fin 3 → ℝ)
    (α₁ α₂ β e : ℝ) : Prop :=
  ∀ u v : B → ℝ, ∑ a, μ a * u a = 0 → ∑ a, μ a * v a = 0 →
    |mixChg1 P C₀ w α₁ α₂ β u v| ≤
      e * Real.sqrt (∑ a, μ a * u a ^ 2) * Real.sqrt (∑ a, μ a * v a ^ 2)

theorem FoldPrimeBound.mono {μ : B → ℝ} {P : Fin 3 → Matrix B B ℝ} {C₀ : Matrix B B ℝ}
    {w : Fin 3 → ℝ} {α₁ α₂ β e e' : ℝ} (h : FoldPrimeBound μ P C₀ w α₁ α₂ β e) (hee : e ≤ e') :
    FoldPrimeBound μ P C₀ w α₁ α₂ β e' := fun u v hu hv =>
  (h u v hu hv).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hee
    (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

end Prime

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- `(1/2, 1/2, 1)`: the symmetric part of a prime fold difference. -/
abbrev SymPrime (C : FoldComponents pr hne) (t e : ℝ) (i : ι) : Prop :=
  FoldPrimeBound (mP hne i) (fun c => compP hne C c i) (oldP hne i) (signedCoef t) (1 / 2) (1 / 2)
    1 e

/-- `(1/2, −1/2, 0)`: the skew part of a prime fold difference. -/
abbrev SkewPrime (C : FoldComponents pr hne) (t e : ℝ) (i : ι) : Prop :=
  FoldPrimeBound (mP hne i) (fun c => compP hne C c i) (oldP hne i) (signedCoef t) (1 / 2)
    (-1 / 2) 0 e

variable {pr} {hne}

omit [Fintype ι] [DecidableEq ι] in
theorem compP_nonneg (C : FoldComponents pr hne) (c : Fin 3) (i : ι) (a b' : Ai pr i) :
    0 ≤ compP hne C c i a b' := ((C i).law 0 c).nonneg _

omit [Fintype ι] [DecidableEq ι] in
theorem oldP_nonneg (i : ι) (a b' : Ai pr i) : 0 ≤ oldP hne i a b' := (K0 (hne.F2 i)).nonneg _

/-- **`prop:signed-bounds`(a) for `F₁`** (Step 4): the symmetric form of the block difference. -/
theorem fold_sym0 (C : FoldComponents pr hne) {t e ρ d : ℝ} (ht : 0 ≤ t) (he : 0 ≤ e)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hρ : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) ρ)
    (hd : ∀ i, CentredNorm (mP hne i) (oldP hne i) d) (hmulti : (1 + t) * ρ ^ 2 + d ^ 2 ≤ e)
    (hin : ∀ i, SymPrime pr hne C t e i) (φ ψ : (Fin 3 → BlockLabel pr) → ℝ) :
    |symK pr hne (newW C t 0) φ ψ| ≤
      e * Real.sqrt (mform (lawF pr hne).weight φ) * Real.sqrt (mform (lawF pr hne).weight ψ) := by
  rw [symK_dot, mform_ip, mform_ip]
  refine mix_change_le (mP_nonneg hne) (mP_total hne) (compP_coupling hne C) (oldP_coupling hne)
    (compP_nonneg C) oldP_nonneg (by rw [sum_signedCoef]; norm_num) hρ0 hρ1 hd0 hd1 hρ hd he ?_
    (fun i u v hu hv => hin i u v hu hv) (fun _ _ => 0) _ _
  rw [sum_abs_signedCoef ht]
  norm_num
  linarith

/-- **`prop:signed-bounds`(b) for `F₁`** (Step 4): the skew form of the block difference. Only the
component norms enter the sectors of `≥ 2` primes. -/
theorem fold_skew0 (C : FoldComponents pr hne) {t e ρ : ℝ} (ht : 0 ≤ t) (he : 0 ≤ e)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρ : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) ρ)
    (hmulti : (1 + t) * ρ ^ 2 ≤ e) (hin : ∀ i, SkewPrime pr hne C t e i)
    (φ ψ : (Fin 3 → BlockLabel pr) → ℝ) :
    |skwK pr (newW C t 0) φ ψ| ≤
      e * Real.sqrt (mform (lawF pr hne).weight φ) * Real.sqrt (mform (lawF pr hne).weight ψ) := by
  rw [skwK_dot, mform_ip, mform_ip]
  have hd : ∀ i, CentredNorm (mP hne i) (oldP hne i) 1 := fun i =>
    centredNorm_one (oldP_nonneg i) (mP_nonneg hne i) ((oldP_coupling hne).row i)
      ((oldP_coupling hne).col i)
  refine mix_change_le (mP_nonneg hne) (mP_total hne) (compP_coupling hne C) (oldP_coupling hne)
    (compP_nonneg C) oldP_nonneg (by rw [sum_signedCoef]; norm_num) hρ0 hρ1 zero_le_one le_rfl
    hρ hd he ?_ (fun i u v hu hv => hin i u v hu hv) (fun _ _ => 0) _ _
  rw [sum_abs_signedCoef ht]
  norm_num
  linarith

variable (pr) (hne)

/-- **`prop:signed-bounds`(a),(e)**: the field `Fs` of `NormBounds` at any `e` above the one-prime
symmetric bounds and above `(1 + t)ρ² + d²`, for reflected components. -/
theorem fold_sym (C : FoldComponents pr hne) (hC : Reflected C) {t e ρ d : ℝ} (ht : 0 ≤ t)
    (he : 0 ≤ e) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hρ : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) ρ)
    (hd : ∀ i, CentredNorm (mP hne i) (oldP hne i) d) (hmulti : (1 + t) * ρ ^ 2 + d ^ 2 ≤ e)
    (hin : ∀ i, SymPrime pr hne C t e i) (j : Fin 2) :
    FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl j))
      (foldChange pr h hne root W I hr b C t (.inl j) .sym) e := by
  refine ⟨he, fun F G => ?_⟩
  rw [form_fold_sym, hsq_fold, hsq_fold]
  have key := fold_sym0 C ht he hρ0 hρ1 hd0 hd1 hρ hd hmulti hin
  fin_cases j
  · exact key _ _
  · change |symK pr hne (newW C t 1) (fr pr 1 F) (fr pr 1 G)| ≤
      e * Real.sqrt (mform (lawF pr hne).weight (fr pr 1 F)) *
        Real.sqrt (mform (lawF pr hne).weight (fr pr 1 G))
    rw [symK_refl hC]
    have k := key (fun x => fr pr 1 G (rf x)) (fun x => fr pr 1 F (rf x))
    rw [mform_rf, mform_rf] at k
    linarith

/-- **`prop:signed-bounds`(b),(e)**: the field `Fa` of `NormBounds` at any `e` above the one-prime
skew bounds and above `(1 + t)ρ²`, for reflected components. -/
theorem fold_skew (C : FoldComponents pr hne) (hC : Reflected C) {t e ρ : ℝ} (ht : 0 ≤ t)
    (he : 0 ≤ e) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) ρ) (hmulti : (1 + t) * ρ ^ 2 ≤ e)
    (hin : ∀ i, SkewPrime pr hne C t e i) (j : Fin 2) :
    FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl j))
      (foldChange pr h hne root W I hr b C t (.inl j) .skew) e := by
  refine ⟨he, fun F G => ?_⟩
  rw [form_fold_skew, hsq_fold, hsq_fold]
  have key := fold_skew0 C ht he hρ0 hρ1 hρ hmulti hin
  fin_cases j
  · exact key _ _
  · change |skwK pr (newW C t 1) (fr pr 1 F) (fr pr 1 G)| ≤
      e * Real.sqrt (mform (lawF pr hne).weight (fr pr 1 F)) *
        Real.sqrt (mform (lawF pr hne).weight (fr pr 1 G))
    rw [skwK_refl hC]
    have k := key (fun x => fr pr 1 G (rf x)) (fun x => fr pr 1 F (rf x))
    rw [mform_rf, mform_rf] at k
    linarith

end Frame

/-! ## The paper's constants -/

/-- `e_o(X)` at the crude collision constant `c_col = 73` (`FoldCol.collisionBound_73`), in
SD2's rational atoms: about `75` at `Q₃` (the paper's sharp `e_o` is `7.62`). -/
def eo73 (k : Fin 33) : ℚ := eoPoly (AX k) 73

/-- **`c_{≥2} ≤ s_F` and `(1 + t)c_+² ≤ a_F` at the 33 piece starts** (exact rationals): with
SD2's majorants `Γ_X = gamX`, `c_+(X) = cpX` at `q = 1/X`, `r = 1/⌊√X⌋`, `e_o` at the crude
collision constant `73` (`eo73`), and the table `s_F = kSF`, `a_F = kAF`; also
`(Γ_X + e_o r_X) r_X ≤ 1`. At `Q₃`: `(Γ + e_o r)² + (1 + t)c_+² = 4.818…` (with the paper's sharp
`e_o` it is `4.788…`), `s_F = 11.166…`, `(1 + t)c_+² = 3.784…`, `a_F = 4.797…`. -/
theorem fold_check : ∀ k : Fin 33,
    (gamX k + eo73 k * rX k) ^ 2 + 627 / 500 * cpX k ^ 2 ≤ kSF k ∧
      627 / 500 * cpX k ^ 2 ≤ kAF k ∧ (gamX k + eo73 k * rX k) * rX k ≤ 1 ∧ 0 ≤ eo73 k := by
  decide +kernel

section Paper

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- **The inputs of the fold families on a middle block** (hypotheses, per prime `p_i`, at the
block's components `C`, the paper's `t = 127/500` and the piece constants `s_F`, `a_F`, `ℓ_t`):
* `sym`, `skew`: `prop:signed-bounds`(c) at one prime, `‖D^s_{t,p}‖ ≤ s_F p^{-1}` and
  `‖D^a_{t,p}‖ ≤ ℓ_t p^{-1/2} + a_F p^{-1}` (the paper's `s_p q`, `ℓ_t r + a_p q` at
  `(1/p, p^{-1/2})`,
  below the piece constants by the monotonicity of `eq:signed-constants`, `lem:majorant`);
* `comp`: `prop:signed-bounds`(c), Step 1: every centred component has norm at most `c_+ r` at the
  paper's `c_+` (SD2's `AnalyticAt.comp`; SD2 proves it with `80` in place of `c_+`, which is not
  enough here).

The collision bound `lem:record:conditional-collision`(d) is **not** an input: the crude
`c_col = 73` (`collisionBound_73`) suffices for the reference centred norm on the sectors of at
least two primes. -/
structure FoldInputs (C : FoldComponents pr hne) (sF aF ℓ : ℝ) : Prop where
  sym : ∀ i, SymPrime pr hne C tPaper (sF * rP pr i ^ 2) i
  skew : ∀ i, SkewPrime pr hne C tPaper (ℓ * rP pr i + aF * rP pr i ^ 2) i
  comp : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) (cpP pr i * rP pr i)

omit [Fintype ι] [DecidableEq ι] in
/-- **The reference centred norm** `(Γ + e_o r) r` at every prime from the collision bound
(`lem:old-f-law`(f); PG's `oldDecomp_block`, `centredNorm_of_decomp`). -/
theorem ref_centred (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i) {ccol : ι → ℝ}
    (col : ∀ i, CollisionBound (hne.F2 i) (ccol i)) (i : ι) :
    CentredNorm (mP hne i) (oldP hne i)
      (gammaP pr i * rP pr i + eoP pr ccol i * (rP pr i * rP pr i)) := by
  have hr : (√(Fintype.card (ZMod (pr i)) : ℝ))⁻¹ = rP pr i := by rw [card_zmod]; rfl
  have hq : ((Fintype.card (ZMod (pr i)) : ℝ))⁻¹ = rP pr i * rP pr i := by
    rw [card_zmod, rP, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have hco := oldP_coupling hne
  have hcn := centredNorm_of_decomp (mP_nonneg hne i) (gammaP_nonneg h19 i)
    (fun a b => (K0 (hne.F2 i)).nonneg _) (hco.row i) (hco.col i) (frame_block hne h3 h19 i)
    (oldDecomp_block hne h3 h19 i (col i))
  rw [hr, hq] at hcn
  exact hcn

/-- **The fold fields `Fs`, `Fa` at the paper's constants** on a middle block of piece `k`
(`prop:signed-bounds`(a),(b),(e)): `s_F r_b²` and `ℓ_t r_b + a_F r_b²`, `r_b = b^{-1/2}`, for
`X_k ≤ b ≤ p` at every prime, from `FoldInputs`, for reflected components, with
`c_{≥2}(X_k) ≤ s_F` and `(1 + t)c_+(X_k)² ≤ a_F`. -/
theorem fold_paper (C : FoldComponents pr hne) (hC : Reflected C) (k : Fin 33) {b' sF aF ℓ : ℝ}
    (hXb : (XQ k : ℝ) ≤ b') (hbp : ∀ i, b' ≤ (pr i : ℝ)) (hℓ : 0 ≤ ℓ)
    (hsF : (((gamX k + eo73 k * rX k) ^ 2 + 627 / 500 * cpX k ^ 2 : ℚ) : ℝ) ≤ sF)
    (haF : ((627 / 500 * cpX k ^ 2 : ℚ) : ℝ) ≤ aF)
    (In : FoldInputs pr hne C sF aF ℓ) :
    NormBoundsRest4 pr h hne root W I hr b C tPaper b' sF aF ℓ := by
  obtain ⟨hX24, hs1, hs2, -⟩ := table_check k
  obtain ⟨-, -, -, g4⟩ := gate_check k
  obtain ⟨-, -, g3, p2⟩ := fold_check k
  obtain ⟨p1, -, -, p4, p5, -⟩ := pos_check k
  have hX' : (2 : ℝ) ^ 24 ≤ (XQ k : ℝ) := by exact_mod_cast hX24
  have hb0 : 0 < b' := lt_of_lt_of_le (by positivity) (hX'.trans hXb)
  have hXp' : ∀ i, (XQ k : ℝ) ≤ (pr i : ℝ) := fun i => hXb.trans (hbp i)
  have hXp : ∀ i, XQ k ≤ pr i := fun i => by exact_mod_cast hXp' i
  have h19 : ∀ i, 19 ≤ pr i := fun i => le_trans (by norm_num) (hX24.trans (hXp i))
  have h3 : ∀ i, pr i % 4 = 3 := h.mod4
  -- the scale
  set τ := 1 / Real.sqrt b' with hτ
  have hτ0 : 0 ≤ τ := by positivity
  have hτ2 : τ ^ 2 * b' = 1 := by
    rw [hτ, div_pow, one_pow, Real.sq_sqrt hb0.le, one_div, inv_mul_cancel₀ hb0.ne']
  obtain ⟨hrp, hrX⟩ := scale_bounds k hτ0 hτ2 hbp hXb
  have hrP0 : ∀ i, 0 ≤ rP pr i := fun i => inv_nonneg.mpr (Real.sqrt_nonneg _)
  -- the majorants at the primes
  have hγ0 : ∀ i, 0 ≤ gammaP pr i := gammaP_nonneg h19
  have hγA : ∀ i, gammaP pr i ≤ GammaAP pr i := gammaP_le_GammaAP h19
  have hΓA : ∀ i, GammaAP pr i ≤ ((gamX k : ℚ) : ℝ) := fun i => GammaA_le hX24 (hXp' i) hs2 hs1
  have hLeA : ∀ i, (atomsAt (pr i) (GammaAP pr i)).Le (AX k).cast := fun i =>
    atomsAt_le hX24 (hXp' i) hs2 hs1 ((hγ0 i).trans (hγA i)) (hΓA i)
  have hLeG : ∀ i, (atomsAt (pr i) (gammaP pr i)).Le (AX k).cast := fun i =>
    atomsAt_le hX24 (hXp' i) hs2 hs1 (hγ0 i) ((hγA i).trans (hΓA i))
  have hp0 : ∀ i, (0 : ℝ) < pr i := fun i => lt_of_lt_of_le (by positivity) (hX'.trans (hXp' i))
  -- the crude collision bound
  have col : ∀ i, CollisionBound (hne.F2 i) ((fun _ => (73 : ℝ)) i) := fun i => by
    obtain ⟨hR, h3', -⟩ := primeHyps h3 h19 i
    have h24 : 2 ^ 24 ≤ Fintype.card (ZMod (pr i)) := by rw [ZMod.card]; exact hX24.trans (hXp i)
    exact collisionBound_73 (hne.F2 i) hR h3' h24
  have heo : ∀ i, eoP pr (fun _ => (73 : ℝ)) i = eoPoly (atomsAt (pr i) (gammaP pr i)) 73 :=
    fun i => eoC_eq _ _ _
  have heoX : ∀ i, eoP pr (fun _ => (73 : ℝ)) i ≤ ((eo73 k : ℚ) : ℝ) := fun i => by
    rw [heo, eo73, eoPoly_cast]
    exact eoPoly_mono (hLeG i) (by norm_num) (by norm_num)
  have heo0 : ∀ i, 0 ≤ eoP pr (fun _ => (73 : ℝ)) i := fun i => by
    rw [heo]; exact eoPoly_nonneg (hLeG i) (by norm_num)
  have hcp : ∀ i, cpP pr i = cpPoly (atomsAt (pr i) (GammaAP pr i)) := fun i => cpL_eq (hp0 i) _
  have hcpX : ∀ i, cpP pr i ≤ ((cpX k : ℚ) : ℝ) := fun i => by
    rw [hcp, cpX, cpPoly_cast]; exact cpPoly_mono (hLeA i)
  have hcp0 : ∀ i, 0 ≤ cpP pr i := fun i => by rw [hcp]; exact cpPoly_nonneg (hLeA i)
  -- the rational facts in `ℝ`
  have pG : (0 : ℝ) ≤ ((gamX k : ℚ) : ℝ) := by exact_mod_cast p1
  have pE : (0 : ℝ) ≤ ((eo73 k : ℚ) : ℝ) := by exact_mod_cast p2
  have pC : (0 : ℝ) ≤ ((cpX k : ℚ) : ℝ) := by exact_mod_cast p4
  have pR : (0 : ℝ) ≤ ((rX k : ℚ) : ℝ) := by exact_mod_cast p5
  have h3' : (((gamX k + eo73 k * rX k) * rX k : ℚ) : ℝ) ≤ 1 := by exact_mod_cast g3
  have h4' : ((cpX k * rX k : ℚ) : ℝ) ≤ 1 := by exact_mod_cast g4
  push_cast at h3' h4' hsF haF
  set Gx := ((gamX k : ℚ) : ℝ)
  set Ex := ((eo73 k : ℚ) : ℝ)
  set Px := ((cpX k : ℚ) : ℝ)
  set Rx := ((rX k : ℚ) : ℝ)
  have hsF0 : 0 ≤ sF := le_trans (by positivity) hsF
  have haF0 : 0 ≤ aF := le_trans (by positivity) haF
  -- the centred norms
  set ρ := Px * τ
  set d := (Gx + Ex * Rx) * τ
  have hρ0 : 0 ≤ ρ := by positivity
  have hd0 : 0 ≤ d := by positivity
  have hρ1 : ρ ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hrX pC) h4'
  have hd1 : d ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hrX (by positivity)) h3'
  have hρc : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) ρ := fun c i =>
    centredNorm_mono (mP_nonneg hne i) (In.comp c i) (mul_nonneg (hcp0 i) (hrP0 i))
      (mul_le_mul (hcpX i) (hrp i) (hrP0 i) pC)
  have hdc : ∀ i, CentredNorm (mP hne i) (oldP hne i) d := fun i => by
    refine centredNorm_mono (mP_nonneg hne i) (ref_centred pr hne h3 h19 col i)
      (add_nonneg (mul_nonneg (hγ0 i) (hrP0 i))
        (mul_nonneg (heo0 i) (mul_nonneg (hrP0 i) (hrP0 i)))) ?_
    have e1 : gammaP pr i * rP pr i ≤ Gx * τ :=
      mul_le_mul ((hγA i).trans (hΓA i)) (hrp i) (hrP0 i) pG
    have e2 : eoP pr (fun _ => (73 : ℝ)) i * (rP pr i * rP pr i) ≤ Ex * (Rx * τ) :=
      mul_le_mul (heoX i) (mul_le_mul ((hrp i).trans hrX) (hrp i) (hrP0 i) pR)
        (mul_nonneg (hrP0 i) (hrP0 i)) pE
    have e3 : d = Gx * τ + Ex * (Rx * τ) := by simp only [d]; ring
    rw [e3]
    linarith
  have hreflect : Reflected C := hC
  have ht : (1 : ℝ) + tPaper = 627 / 500 := by norm_num [tPaper]
  have hτp : ∀ i, rP pr i ^ 2 ≤ τ ^ 2 := fun i => pow_le_pow_left₀ (hrP0 i) (hrp i) 2
  refine ⟨fold_sym pr h hne root W I hr b C hreflect tPaper_nonneg (by positivity) hρ0 hρ1 hd0
    hd1 hρc hdc ?_ (fun i => (In.sym i).mono (mul_le_mul_of_nonneg_left (hτp i) hsF0)),
    fold_skew pr h hne root W I hr b C hreflect tPaper_nonneg (by positivity) hρ0 hρ1 hρc ?_
    (fun i => (In.skew i).mono (add_le_add (mul_le_mul_of_nonneg_left (hrp i) hℓ)
      (mul_le_mul_of_nonneg_left (hτp i) haF0)))⟩
  · rw [ht]
    have : 627 / 500 * ρ ^ 2 + d ^ 2 = ((Gx + Ex * Rx) ^ 2 + 627 / 500 * Px ^ 2) * τ ^ 2 := by
      simp only [ρ, d]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hsF (sq_nonneg _)
  · rw [ht]
    have : 627 / 500 * ρ ^ 2 = 627 / 500 * Px ^ 2 * τ ^ 2 := by simp only [ρ]; ring
    rw [this]
    have := mul_le_mul_of_nonneg_right haF (sq_nonneg τ)
    nlinarith [mul_nonneg hℓ hτ0]

end Paper

end Sarkozy.NormBoundsPaper4
