module

public import Sarkozy.NormBoundsPaper3.MatchSkew
public import Sarkozy.NormBoundsPaper3.OldLaw

@[expose] public section

/-!
# The symmetric norm of the matching replacements, reduced to one prime (`Es`; NB3)

`paper/sections/21_middle_records.tex`, `lem:record:exact-marginal-e`(ii): "the block differences
… have, on `L²(⊗_p ν_{E,p})`, symmetric part of norm at most `s_E(X) b^{-1/2}`"; proof: "by
`lem:sector`(a),(b) the block difference vanishes on the empty sector, is the prime difference on
the singleton sectors, and the norms of its symmetric and skew parts are the maxima over the
sectors. On a singleton `{p}` they are at most `s_E(X) b^{-1/2}` … On a sector `{p, p'}` …
of norm at most `s^E_{(2)}/b` … the bounds `s^E_{(2)}/b, s^E_{(3)}/b < 2/b` are below
`s_E(X) b^{-1/2}`."

Here the block structure is proved and the singleton (one-prime) bound is the only input:

* `form_oldE`, **`form_match_sym`**: the symmetric part of the change of `E_s` is the form
  `½⟨φ, ⊗K₁ ψ⟩ + ½⟨ψ, ⊗K₁ φ⟩ − ⟨φ, ⊗K^E_0 ψ⟩` on `∏_p 𝔽_p³` (`chg … (½, ½, 1)`);
* **`EOrthPrime p s`**: the one-prime statement `‖Sym(K₁ − K^E_0)‖ ≤ s` on mean-zero functions of
  `L²(ν_E)`; the paper's `lem:record:e-orthogonal`(c) is `EOrthPrime p s^E_p`. *Used as a
  hypothesis* (with `s = s_E(X) p^{-1/2}`, the monotonicity of `lem:record:exact-marginal-e`(i));
  `eOrthPrime_crude`: it holds with the crude `s = rhoE p + 18p/((p − 1)(p − 2))`
  (non-vacuity; too weak for the paper's constant);
* **`match_sym`**: `Es` for any `e` above the prime inputs and `ρ² + d² ≤ e` (`change_le` with
  `(½, ½, 1)`; the larger sectors by `P3_centred`, `C0_centred`);
* **`match_sym_paper`**: `Es` at `s_E · b^{-1/2}` from `EOrthPrime p (s_E p^{-1/2})` at the primes
  of
  the block, for a piece start `10^6 ≤ X ≤ b` and `2 ≤ s_E² X` (true at the paper's `s_E(X) ≈
  (1 + √2) r_X`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper3

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.SignedComponents
open Sarkozy.IndexSupport Sarkozy.Mixing Sarkozy.SignedGram
open Sarkozy.NormBoundsPaper (form_emit_gen)
open Sarkozy.NormBoundsPaper2 (ip chg chg1 change_le centredNorm_mono)

/-! ## The one-prime input -/

/-- **`lem:record:e-orthogonal`(c) at one prime**, in the form used here: the symmetric part of
`K₁ − K^E_0` has form norm at most `s` on mean-zero functions of `L²(ν_E)`. -/
def EOrthPrime (p : ℕ) [Fact p.Prime] (s : ℝ) : Prop :=
  ∀ (hE : (eSet (F := ZMod p)).Nonempty)
    (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty)
    (u v : (ZMod p × ZMod p) × ZMod p → ℝ), ∑ x, m3 p x * u x = 0 → ∑ x, m3 p x * v x = 0 →
    |chg1 (P3 hE) (C0 hne) (1 / 2) (1 / 2) 1 u v| ≤
      s * Real.sqrt (∑ x, m3 p x * u x ^ 2) * Real.sqrt (∑ x, m3 p x * v x ^ 2)

theorem EOrthPrime.mono {p : ℕ} [Fact p.Prime] {s s' : ℝ} (h : EOrthPrime p s) (hs : s ≤ s') :
    EOrthPrime p s' := fun hE hne u v hu hv =>
  (h hE hne u v hu hv).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs
    (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

/-- **Non-vacuity**: the one-prime input holds with a crude constant (the sum of the two
centred bounds). -/
theorem eOrthPrime_crude {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (h3 : p % 4 = 3) :
    EOrthPrime p (rhoE p + 18 * (p : ℝ) / (((p : ℝ) - 1) * ((p : ℝ) - 2))) := by
  intro hE hne u v hu hv
  have h1 := P3_form hE hp h3 u v hu hv
  have h2 := P3_form hE hp h3 v u hv hu
  have h3' := C0_form hne (by omega) u v hu hv
  have hp' : (7 : ℝ) ≤ p := by exact_mod_cast hp
  have hL := F6_lower hne (by omega)
  have hM := M3_pos (p := p) (by omega)
  have h12 : 0 < ((p : ℝ) - 1) * ((p : ℝ) - 2) := by nlinarith
  have hd : 2 * (1 - F6 (p := p) / ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2))) ≤
      18 * (p : ℝ) / (((p : ℝ) - 1) * ((p : ℝ) - 2)) := by
    have e : 18 * (p : ℝ) / (((p : ℝ) - 1) * ((p : ℝ) - 2)) =
        2 * (9 * (p : ℝ) ^ 2 / ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2))) := by
      field_simp; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [sub_le_comm, one_sub_div hM.ne', div_le_div_iff_of_pos_right hM]
    linarith
  set A := Real.sqrt (∑ x, m3 p x * u x ^ 2)
  set B := Real.sqrt (∑ x, m3 p x * v x ^ 2)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have h3'' : |u ⬝ᵥ (C0 hne *ᵥ v)| ≤ 18 * (p : ℝ) / (((p : ℝ) - 1) * ((p : ℝ) - 2)) * A * B := by
    refine h3'.trans ?_
    have := mul_le_mul_of_nonneg_right hd hAB
    calc _ = 2 * (1 - F6 (p := p) / ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2))) * (A * B) := by
          ring
      _ ≤ _ := this
      _ = _ := by ring
  unfold chg1
  rw [abs_le] at h1 h2 h3'' ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3''.1, h3''.2]

/-! ## Numbers -/

/-- `rhoE p ≤ p^{-1/2}(1 + 4p^{-1/2})` for `p ≥ 64`. -/
theorem rhoE_le' {p : ℕ} (hp : (64 : ℝ) ≤ p) :
    rhoE p ≤ (1 / Real.sqrt p) * (1 + 4 * (1 / Real.sqrt p)) := by
  unfold rhoE
  set s := Real.sqrt p
  have hs : s * s = p := Real.mul_self_sqrt (by linarith)
  have hs8 : 8 ≤ s := by
    rw [show (8 : ℝ) = Real.sqrt 64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hp
  have hs0 : 0 < s := by linarith
  have e : (1 / s) * (1 + 4 * (1 / s)) = (s + 4) / (s * s) := by field_simp
  rw [e, ← hs, div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith [mul_pos hs0 hs0, mul_pos (mul_pos hs0 hs0) hs0, mul_nonneg (sub_nonneg.mpr hs8)
    (mul_pos (mul_pos hs0 hs0) hs0).le, mul_nonneg (sub_nonneg.mpr hs8)
    (mul_pos (mul_pos (mul_pos hs0 hs0) hs0) hs0).le]

/-- `18p/((p − 1)(p − 2)) ≤ 36/p` for `p ≥ 6`. -/
theorem d0_le {p : ℝ} (hp : 6 ≤ p) : 18 * p / ((p - 1) * (p - 2)) ≤ 36 * (1 / p) := by
  have h12 : 0 < (p - 1) * (p - 2) := by nlinarith
  rw [mul_one_div, div_le_div_iff₀ h12 (by linarith)]
  nlinarith

/-! ## The block bound -/

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- The old matching record's form is the form of `⊗_p K^E_0`. -/
theorem form_oldE (s : Fin 2) (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (oldE pr hne s) F G =
      lift3 (me pr s F) ⬝ᵥ (piKron (fun i => C0 (hne.E2 i)) *ᵥ lift3 (me pr s G)) := by
  rw [form_emit_gen _ _ _ _ (oldE_half s) (oldE_flip s)]
  unfold lawE blockGraphLaw
  exact expect_tensor_cmT _ (lay 0) (lay 1) (me pr s F) (me pr s G)

/-- **The symmetric part of the matching change** is `Sym(⊗ K₁) − ⊗ K^E_0`. -/
theorem form_match_sym (s : Fin 2) (C : FoldComponents pr hne) (t : ℝ)
    (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (foldChange pr h hne root W I hr b C t (.inr (.inl s)) .sym) F G =
      chg (fun i => P3 (blockE_nonempty pr h i)) (fun i => C0 (hne.E2 i)) (1 / 2) (1 / 2) 1
        (lift3 (me pr s F)) (lift3 (me pr s G)) := by
  have hS : ∀ L₁ L₂ : SlotMeasure (BlockLabel pr), ∀ F G,
      reservedCut.form (L₁ - L₂) F G = reservedCut.form L₁ F G - reservedCut.form L₂ F G :=
    fun _ _ _ _ => rfl
  change reservedCut.form (symPart reservedCut
    (signedIntegral (matchRec pr h s).weight - oldE pr hne s)) F G = _
  unfold symPart
  rw [form_smul, form_add, form_reflect, hS, hS, form_oldE_symm pr hne s F G, form_newE,
    form_newE, form_oldE]
  unfold chg
  ring

/-- **`lem:record:exact-marginal-e`(ii), symmetric part, from the one-prime input**: the
symmetric part of the change of the matching record `E_s` has norm at most `e`, for `e` above the
one-prime inputs and above `ρ² + d²`, `ρ, d ≤ 1` above the prime centred constants of `K₁` and
`K^E_0`. -/
theorem match_sym (s : Fin 2) (C : FoldComponents pr hne) (t : ℝ) {e ρ d : ℝ}
    (he : 0 ≤ e) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hρd : ρ ^ 2 + d ^ 2 ≤ e) (hρp : ∀ i, rhoE (pr i) ≤ ρ)
    (hdp : ∀ i, 18 * (pr i : ℝ) / (((pr i : ℝ) - 1) * ((pr i : ℝ) - 2)) ≤ d)
    (hin : ∀ i, EOrthPrime (pr i) e) :
    FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inl s)))
      (foldChange pr h hne root W I hr b C t (.inr (.inl s)) .sym) e := by
  refine ⟨he, fun F G => ?_⟩
  change |_| ≤ e * Real.sqrt (hsq reservedCut (plusMarginal reservedCut
    (emit (lawE pr hne) (midEmission (matching s))).weight) F) *
    Real.sqrt (hsq reservedCut (plusMarginal reservedCut
    (emit (lawE pr hne) (midEmission (matching s))).weight) G)
  rw [form_match_sym pr h hne root W I hr b s C t F G, hsq_oldE pr hne s F, hsq_oldE pr hne s G]
  have hp7 : ∀ i, 7 ≤ pr i := h.ge7
  have hp3 : ∀ i, 3 ≤ pr i := fun i => by have := hp7 i; omega
  have hcp : IsCoupling (fun i => m3 (pr i)) (fun i => P3 (blockE_nonempty pr h i)) :=
    ⟨fun i a => P3_row _ (hp7 i) (h.mod4 i) a, fun i b => P3_col _ (hp7 i) (h.mod4 i) b⟩
  have hc0 : IsCoupling (fun i => m3 (pr i)) (fun i => C0 (hne.E2 i)) :=
    ⟨fun i a => C0_row _ (hp3 i) a, fun i b => C0_col _ (hp3 i) b⟩
  have hcent : ∀ i, CentredNorm (m3 (pr i)) (P3 (blockE_nonempty pr h i)) ρ := fun i =>
    centredNorm_mono (m3_nonneg (hp3 i)) (P3_centred _ (hp7 i) (h.mod4 i)) (rhoE_nonneg _)
      (hρp i)
  have hcent0 : ∀ i, CentredNorm (m3 (pr i)) (C0 (hne.E2 i)) d := fun i => by
    have hp' : (7 : ℝ) ≤ pr i := by exact_mod_cast hp7 i
    have h12 : 0 < ((pr i : ℝ) - 1) * ((pr i : ℝ) - 2) := by nlinarith
    exact centredNorm_mono (m3_nonneg (hp3 i)) (C0_centred _ (hp3 i)) (by positivity) (hdp i)
  refine change_le (fun i => m3_nonneg (hp3 i)) (fun i => sum_m3 (hp3 i)) hcp hc0
    (fun i => P3_nonneg _) (fun i => C0_nonneg _) (by norm_num) hρ0 hρ1 hd0 hd1 hcent hcent0 he
    ?_ (fun i u v hu hv => hin i _ _ u v hu hv) (fun _ => ((0, 0), 0)) _ _
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_one]
  nlinarith

/-- **The field `Es` at the paper's constant from the one-prime input**
(`lem:record:exact-marginal-e`(ii) from `lem:record:e-orthogonal`(c)): `s_E · b^{-1/2}`, if at every
prime `p` of the block `‖Sym(K₁ − K^E_0)‖ ≤ s_E p^{-1/2}` (*hypothesis* `hin`), for a piece start
`10^6 ≤ X ≤ b` below the primes and `2 ≤ s_E² X`. -/
theorem match_sym_paper (C : FoldComponents pr hne) (t : ℝ) {b' sE X : ℝ} (hX : 10 ^ 6 ≤ X)
    (hXb : X ≤ b') (hbp : ∀ i, b' ≤ (pr i : ℝ)) (hsE0 : 0 ≤ sE) (hsE : 2 ≤ sE ^ 2 * X)
    (hin : ∀ i, EOrthPrime (pr i) (sE * (1 / Real.sqrt (pr i)))) (s : Fin 2) :
    FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inl s)))
      (foldChange pr h hne root W I hr b C t (.inr (.inl s)) .sym) (sE * (1 / Real.sqrt b')) := by
  have hb0 : 0 < b' := by linarith
  have hX0 : 0 < X := by linarith
  have hsb : 0 < Real.sqrt b' := Real.sqrt_pos.mpr hb0
  set τ := 1 / Real.sqrt b'
  have hτ0 : 0 < τ := one_div_pos.mpr hsb
  have hτ2 : τ ^ 2 = 1 / b' := by
    simp only [τ, div_pow, one_pow, Real.sq_sqrt hb0.le]
  have hτX : τ ^ 2 ≤ 1 / X := by rw [hτ2]; exact one_div_le_one_div_of_le hX0 hXb
  have hτs : τ ≤ 1 / 1000 := by
    have : τ ^ 2 ≤ (1 / 1000) ^ 2 := by
      refine hτX.trans ?_
      rw [div_pow, one_pow]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    exact (pow_le_pow_iff_left₀ hτ0.le (by norm_num) (by norm_num)).mp this
  have hρ1 : τ * (1 + 4 * τ) ≤ 1 := by nlinarith
  have hd1 : 36 * τ ^ 2 ≤ 1 := by nlinarith
  -- `ρ² + d² ≤ s_E τ`: `τ (1 + 4τ)² + 1296 τ³ ≤ 1.01 τ ≤ s_E`
  have hkey : τ * 1.01 ≤ sE := by
    have h1 : (τ * 1.01) ^ 2 ≤ sE ^ 2 := by
      have : (τ * 1.01) ^ 2 = τ ^ 2 * 1.0201 := by ring
      rw [this]
      have h2 : τ ^ 2 * X ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hτX hX0.le
        rwa [one_div_mul_cancel hX0.ne'] at this
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hsE0 (by norm_num)).mp h1
  have hρd : (τ * (1 + 4 * τ)) ^ 2 + (36 * τ ^ 2) ^ 2 ≤ sE * τ := by
    have : (τ * (1 + 4 * τ)) ^ 2 + (36 * τ ^ 2) ^ 2 ≤ τ * (τ * 1.01) := by
      have e : (τ * (1 + 4 * τ)) ^ 2 + (36 * τ ^ 2) ^ 2 =
          τ * (τ * ((1 + 4 * τ) ^ 2 + 1296 * τ ^ 2)) := by ring
      rw [e]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hτ0.le) hτ0.le
      nlinarith
    calc _ ≤ τ * (τ * 1.01) := this
      _ ≤ τ * sE := mul_le_mul_of_nonneg_left hkey hτ0.le
      _ = sE * τ := by ring
  refine match_sym pr h hne root W I hr b s C t (ρ := τ * (1 + 4 * τ)) (d := 36 * τ ^ 2)
    (by positivity) (by positivity) hρ1 (by positivity) hd1 hρd (fun i => ?_) (fun i => ?_)
    (fun i => ?_)
  · have hp : (64 : ℝ) ≤ pr i := by linarith [hbp i]
    refine (rhoE_le' hp).trans ?_
    have hτp : 1 / Real.sqrt (pr i) ≤ τ :=
      one_div_le_one_div_of_le hsb (Real.sqrt_le_sqrt (hbp i))
    have : 0 ≤ 1 / Real.sqrt (pr i) := by positivity
    exact mul_le_mul hτp (by linarith) (by positivity) hτ0.le
  · have hp : (6 : ℝ) ≤ pr i := by linarith [hbp i]
    refine (d0_le hp).trans ?_
    rw [hτ2]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hb0 (hbp i)) (by norm_num)
  · refine (hin i).mono (mul_le_mul_of_nonneg_left ?_ hsE0)
    exact one_div_le_one_div_of_le hsb (Real.sqrt_le_sqrt (hbp i))

end Frame

end Sarkozy.NormBoundsPaper3
