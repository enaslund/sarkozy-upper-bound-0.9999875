module

public import Sarkozy.NormBoundsPaper4.FoldBlock
public import Sarkozy.CompSharp.Paper

@[expose] public section




open Finset Matrix

namespace Sarkozy.CompSharp

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.SignedComponents
open Sarkozy.IndexSupport Sarkozy.Mixing Sarkozy.SignedGram Sarkozy.PrimeGram
open Sarkozy.SignedDecomp Sarkozy.NormBoundsPaper4
open Sarkozy.NormBoundsPaper3 (NormBoundsRest4)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)

section Paper

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- **FD's fold inputs with the component norms at `c_B r + R q`** (hypotheses, per prime; see
FD's `FoldInputs`): `sym`, `skew` are `prop:signed-bounds`(c) at one prime, as in FD; `comp` is
`prop:signed-bounds`(c), Step 1, with `c_B r + R q` in place of `c_+ r` (proved for the paper's
components with `c_B = 34`, `R = 1000` and with `c_B = 38`, `R = 0`: `ofPaper34`, `ofPaper38`). -/
structure FoldInputsC (C : FoldComponents pr hne) (sF aF ℓ cB R : ℝ) : Prop where
  sym : ∀ i, SymPrime pr hne C tPaper (sF * rP pr i ^ 2) i
  skew : ∀ i, SkewPrime pr hne C tPaper (ℓ * rP pr i + aF * rP pr i ^ 2) i
  comp : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) (cB * rP pr i + R * rP pr i ^ 2)

/-- **The fold fields `Fs`, `Fa` at a crude component constant** on a middle block of piece `k`
(`prop:signed-bounds`(a),(b),(e)): `s_F r_b²` and `ℓ_t r_b + a_F r_b²`, `r_b = b^{-1/2}`, for
`X_k ≤ b ≤ p` at every prime, from `FoldInputsC` (component norms `≤ c_B r + R q`), for reflected
components, with `c_{≥2} = (Γ_X + e_o r_X)² + (1 + t)c'² ≤ s_F` and `(1 + t)c'² ≤ a_F`,
`c' = c_B + R r_X`, and `c' r_X ≤ 1`. FD's `fold_paper` (proof copied) with `c_+(X_k)` replaced by
`c'`. -/
theorem fold_paper_gen (C : FoldComponents pr hne) (hC : Reflected C) (k : Fin 33)
    {b' sF aF ℓ cB R : ℝ} (hcB : 0 ≤ cB) (hR0 : 0 ≤ R)
    (hXb : (XQ k : ℝ) ≤ b') (hbp : ∀ i, b' ≤ (pr i : ℝ)) (hℓ : 0 ≤ ℓ)
    (hsF : (((gamX k + eo73 k * rX k) ^ 2 : ℚ) : ℝ) +
      627 / 500 * (cB + R * ((rX k : ℚ) : ℝ)) ^ 2 ≤ sF)
    (haF : 627 / 500 * (cB + R * ((rX k : ℚ) : ℝ)) ^ 2 ≤ aF)
    (hc1 : (cB + R * ((rX k : ℚ) : ℝ)) * ((rX k : ℚ) : ℝ) ≤ 1)
    (In : FoldInputsC pr hne C sF aF ℓ cB R) :
    NormBoundsRest4 pr h hne root W I hr b C tPaper b' sF aF ℓ := by
  obtain ⟨hX24, hs1, hs2, -⟩ := table_check k
  obtain ⟨-, -, g3, p2⟩ := fold_check k
  obtain ⟨p1, -, -, -, p5, -⟩ := pos_check k
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
  have hLeG : ∀ i, (atomsAt (pr i) (gammaP pr i)).Le (AX k).cast := fun i =>
    atomsAt_le hX24 (hXp' i) hs2 hs1 (hγ0 i) ((hγA i).trans (hΓA i))
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
  -- the rational facts in `ℝ`
  have pG : (0 : ℝ) ≤ ((gamX k : ℚ) : ℝ) := by exact_mod_cast p1
  have pE : (0 : ℝ) ≤ ((eo73 k : ℚ) : ℝ) := by exact_mod_cast p2
  have pR : (0 : ℝ) ≤ ((rX k : ℚ) : ℝ) := by exact_mod_cast p5
  have h3' : (((gamX k + eo73 k * rX k) * rX k : ℚ) : ℝ) ≤ 1 := by exact_mod_cast g3
  push_cast at h3' hsF
  set Gx := ((gamX k : ℚ) : ℝ)
  set Ex := ((eo73 k : ℚ) : ℝ)
  set Rx := ((rX k : ℚ) : ℝ)
  set Px := cB + R * Rx with hPx
  have pC : 0 ≤ Px := add_nonneg hcB (mul_nonneg hR0 pR)
  have hsF0 : 0 ≤ sF := le_trans (by positivity) hsF
  have haF0 : 0 ≤ aF := le_trans (by positivity) haF
  -- the centred norms
  set ρ := Px * τ
  set d := (Gx + Ex * Rx) * τ
  have hρ0 : 0 ≤ ρ := mul_nonneg pC hτ0
  have hd0 : 0 ≤ d := by positivity
  have hρ1 : ρ ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hrX pC) hc1
  have hd1 : d ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hrX (by positivity)) h3'
  have hρc : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) ρ := fun c i => by
    refine centredNorm_mono (mP_nonneg hne i) (In.comp c i)
      (add_nonneg (mul_nonneg hcB (hrP0 i)) (mul_nonneg hR0 (pow_nonneg (hrP0 i) 2))) ?_
    have e1 : cB * rP pr i ≤ cB * τ := mul_le_mul_of_nonneg_left (hrp i) hcB
    have e2 : rP pr i ^ 2 ≤ Rx * τ := by
      rw [sq]; exact mul_le_mul ((hrp i).trans hrX) (hrp i) (hrP0 i) pR
    have e3 : R * rP pr i ^ 2 ≤ R * (Rx * τ) := mul_le_mul_of_nonneg_left e2 hR0
    have e4 : ρ = cB * τ + R * (Rx * τ) := by simp only [ρ, Px]; ring
    rw [e4]
    linarith
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

section Ctor

open Sarkozy.MainFinalF1 (bOf Blk)
open Sarkozy.PartVLaws (blockPrimes)

/-- **The fold inputs at `c_B = 34`, `R = 1000`** for the paper's components, from `sym` and
`skew` alone: the field `comp` is `comp34_paper` (`prop:signed-bounds`(c), Step 1, proved). -/
theorem FoldInputsC.ofPaper34 {b : Blk} {hne : MiddleNonempty (blockPrimes bOf b)}
    (Dc : DefectConstants b hne tPaper_nonneg tPaper_le_one) {sF aF ℓ : ℝ}
    (sym : ∀ i, SymPrime (blockPrimes bOf b) hne (paperComponents Dc) tPaper
      (sF * rP (blockPrimes bOf b) i ^ 2) i)
    (skew : ∀ i, SkewPrime (blockPrimes bOf b) hne (paperComponents Dc) tPaper
      (ℓ * rP (blockPrimes bOf b) i + aF * rP (blockPrimes bOf b) i ^ 2) i) :
    FoldInputsC (blockPrimes bOf b) hne (paperComponents Dc) sF aF ℓ 34 1000 :=
  ⟨sym, skew, comp34_paper hne Dc⟩

/-- **The fold inputs at `c_B = 38`, `R = 0`** for the paper's components, from `sym` and `skew`
alone: the field `comp` is `comp38_paper`. -/
theorem FoldInputsC.ofPaper38 {b : Blk} {hne : MiddleNonempty (blockPrimes bOf b)}
    (Dc : DefectConstants b hne tPaper_nonneg tPaper_le_one) {sF aF ℓ : ℝ}
    (sym : ∀ i, SymPrime (blockPrimes bOf b) hne (paperComponents Dc) tPaper
      (sF * rP (blockPrimes bOf b) i ^ 2) i)
    (skew : ∀ i, SkewPrime (blockPrimes bOf b) hne (paperComponents Dc) tPaper
      (ℓ * rP (blockPrimes bOf b) i + aF * rP (blockPrimes bOf b) i ^ 2) i) :
    FoldInputsC (blockPrimes bOf b) hne (paperComponents Dc) sF aF ℓ 38 0 :=
  ⟨sym, skew, fun c i => by
    have h := comp38_paper hne Dc c i
    rwa [zero_mul, add_zero]⟩

/-- **FD's `FoldInputs` gives `FoldInputsC`** at any `c_B`, `R ≥ 0` dominating `c_+` at every
prime (`c_+ r ≤ c_B r + R q`). -/
theorem FoldInputsC.ofFoldInputs {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ}
    [∀ i, Fact (pr i).Prime] {hne : MiddleNonempty pr} {C : FoldComponents pr hne}
    {sF aF ℓ cB R : ℝ} (In : FoldInputs pr hne C sF aF ℓ) (h0 : ∀ i, 0 ≤ cpP pr i * rP pr i)
    (hle : ∀ i, cpP pr i * rP pr i ≤ cB * rP pr i + R * rP pr i ^ 2) :
    FoldInputsC pr hne C sF aF ℓ cB R :=
  ⟨In.sym, In.skew, fun c i => centredNorm_mono (mP_nonneg hne i) (In.comp c i) (h0 i) (hle i)⟩

end Ctor

end Sarkozy.CompSharp
