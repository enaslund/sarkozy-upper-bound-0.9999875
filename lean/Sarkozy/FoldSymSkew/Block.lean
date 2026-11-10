module

public import Sarkozy.FoldSymSkew.Prime

@[expose] public section

/-!
# `sym`, `skew` at every prime of a middle block, at piece constants (FS)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(c) at one prime (symmetric part, and
skew part with the leading star), at every prime `p ≥ X_k` of a middle block of piece `k`.

* **`newDecomp_mono`**: PG's `NewDecomp` is monotone in `e_sg`.
* **`aNorm_le`**: `|a_t| ≤ aNU = 1.2731976` at `t = 127/500` (`|a_t|² = 1.621032`).
* **`symSkew_block`**: from `NewDecomp` at a constant `E` at every prime of the block (the last
  claim of `prop:signed-bounds`(c)), FD's one-prime statements `SymPrime` at `s_F p^{-1}` and
  `SkewPrime` at `ℓ p^{-1/2} + a_F p^{-1}` (the fields `sym`, `skew` of FD's `FoldInputs`), given
  `e_o(X_k) + E ≤ s_F`, `E ≤ a_F`, `aNU Γ_X ≤ ℓ`. The reference decomposition is PG's
  `oldDecomp_block` with FD's crude collision constant `73` (`e_o(X_k) = eo73 k ≈ 75`); the frame
  constant is W6's `Γ ≤ Γ_A ≤ Γ_X = gamX k` (`≈ 1.000224` at `Q₃`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.FoldSymSkew

open Sarkozy.PartV Sarkozy.SignedComponents Sarkozy.SignedGram Sarkozy.PrimeGram
open Sarkozy.SignedDecomp Sarkozy.NormBoundsPaper4
open Sarkozy.MiddleComparison (signedCoef)
open Sarkozy.MainFinal2 (tPaper)

theorem newDecomp_mono {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {m : (Fin 3 → F) → ℝ} {N : Matrix (Fin 3 → F) (Fin 3 → F) ℝ} {t e e' : ℝ}
    (h : NewDecomp m N t e) (hee : e ≤ e') : NewDecomp m N t e' := fun f g hf hg =>
  (h f g hf hg).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hee
    (inv_nonneg.mpr (Nat.cast_nonneg _))) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

/-- A rational majorant of `|a_t|` at `t = 127/500`: `|a_t|² = 1.621032 ≤ 1.2731976²`. -/
def aNU : ℚ := 12731976 / 10 ^ 7

theorem aNorm_le : aNorm tPaper ≤ ((aNU : ℚ) : ℝ) := by
  unfold aNorm
  rw [aNorm_sq, Real.sqrt_le_left (by norm_num [aNU])]
  norm_num [aNU, tPaper]

theorem aNorm_nonneg (t : ℝ) : 0 ≤ aNorm t := Real.sqrt_nonneg _

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

omit [Fintype ι] [DecidableEq ι] in
/-- **`prop:signed-bounds`(c) at every prime of a middle block of piece `k`, symmetric and skew
parts, from the decomposition of the signed record** (`NewDecomp` at the constant `E`): FD's
`SymPrime` at `s_F p^{-1}` and `SkewPrime` at `ℓ p^{-1/2} + a_F p^{-1}`, for every `s_F`, `a_F`,
`ℓ` with `e_o(X_k) + E ≤ s_F` (`e_o` at the crude collision constant `73`), `E ≤ a_F` and
`aNU Γ_X ≤ ℓ`. The constants are explicit and uniform in the prime: `(e_o(p) + E) q` and
`|a_t| Γ(p) r + E q` at `p`, below the stated ones for `p ≥ X_k`. -/
theorem symSkew_block (hne : MiddleNonempty pr) (C : FoldComponents pr hne)
    (h3 : ∀ i, pr i % 4 = 3) (k : Fin 33) (hXp : ∀ i, XQ k ≤ pr i) {E sF aF ℓ : ℝ}
    (hnew : ∀ i, NewDecomp (mP hne i) (∑ c, signedCoef tPaper c • compP hne C c i) tPaper E)
    (hsF : ((eo73 k : ℚ) : ℝ) + E ≤ sF) (haF : E ≤ aF) (hℓ : ((aNU * gamX k : ℚ) : ℝ) ≤ ℓ) :
    (∀ i, SymPrime pr hne C tPaper (sF * rP pr i ^ 2) i) ∧
      ∀ i, SkewPrime pr hne C tPaper (ℓ * rP pr i + aF * rP pr i ^ 2) i := by
  obtain ⟨hX24, hs1, hs2, -⟩ := table_check k
  obtain ⟨p1, -, -, -, -, -⟩ := pos_check k
  have hX' : (2 : ℝ) ^ 24 ≤ (XQ k : ℝ) := by exact_mod_cast hX24
  have hXp' : ∀ i, (XQ k : ℝ) ≤ (pr i : ℝ) := fun i => by exact_mod_cast hXp i
  have h19 : ∀ i, 19 ≤ pr i := fun i => le_trans (by norm_num) (hX24.trans (hXp i))
  have hp0 : ∀ i, (0 : ℝ) < pr i := fun i => lt_of_lt_of_le (by positivity) (hX'.trans (hXp' i))
  have hγ0 : ∀ i, 0 ≤ gammaP pr i := gammaP_nonneg h19
  have hγA : ∀ i, gammaP pr i ≤ GammaAP pr i := gammaP_le_GammaAP h19
  have hΓA : ∀ i, GammaAP pr i ≤ ((gamX k : ℚ) : ℝ) := fun i => GammaA_le hX24 (hXp' i) hs2 hs1
  have hLeG : ∀ i, (atomsAt (pr i) (gammaP pr i)).Le (AX k).cast := fun i =>
    atomsAt_le hX24 (hXp' i) hs2 hs1 (hγ0 i) ((hγA i).trans (hΓA i))
  have heoX : ∀ i, eoP pr (fun _ => (73 : ℝ)) i ≤ ((eo73 k : ℚ) : ℝ) := fun i => by
    rw [show eoP pr (fun _ => (73 : ℝ)) i = eoPoly (atomsAt (pr i) (gammaP pr i)) 73 from
      eoC_eq _ _ _, eo73, eoPoly_cast]
    exact eoPoly_mono (hLeG i) (by norm_num) (by norm_num)
  have hq : ∀ i, ((Fintype.card (ZMod (pr i)) : ℝ))⁻¹ = rP pr i ^ 2 := fun i => by
    rw [card_zmod, rP, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hr : ∀ i, (√(Fintype.card (ZMod (pr i)) : ℝ))⁻¹ = rP pr i := fun i => by
    rw [card_zmod]; rfl
  have hrP0 : ∀ i, 0 ≤ rP pr i := fun i => inv_nonneg.mpr (Real.sqrt_nonneg _)
  refine ⟨fun i => ?_, fun i => ?_⟩
  · -- the symmetric part: `(e_o + E) q`
    obtain ⟨hR, h3', -⟩ := primeHyps h3 h19 i
    have h24 : 2 ^ 24 ≤ Fintype.card (ZMod (pr i)) := by
      rw [ZMod.card]; exact hX24.trans (hXp i)
    have hold := oldDecomp_block hne h3 h19 i (ccol := fun _ => (73 : ℝ))
      (collisionBound_73 (hne.F2 i) hR h3' h24)
    have h := sym_of_decomp (P := fun c => compP hne C c i) (w := signedCoef tPaper) hold (hnew i)
    rw [hq i] at h
    exact h.mono (mul_le_mul_of_nonneg_right ((add_le_add_left (heoX i) E).trans
      (by linarith)) (sq_nonneg _))
  · -- the skew part: `|a_t| Γ r + E q`
    have h := skew_of_decomp (P := fun c => compP hne C c i) (C₀ := oldP hne i)
      (w := signedCoef tPaper) (mP_nonneg hne i) (hγ0 i) (frame_block hne h3 h19 i) (hnew i)
    rw [hq i, hr i] at h
    refine h.mono (add_le_add (mul_le_mul_of_nonneg_right ?_ (hrP0 i))
      (mul_le_mul_of_nonneg_right haF (sq_nonneg _)))
    have ha := aNorm_le
    have hG : gammaP pr i ≤ ((gamX k : ℚ) : ℝ) := (hγA i).trans (hΓA i)
    have pG : (0 : ℝ) ≤ ((gamX k : ℚ) : ℝ) := by exact_mod_cast p1
    have hℓ' : ((aNU : ℚ) : ℝ) * ((gamX k : ℚ) : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    exact (mul_le_mul ha hG (hγ0 i) (le_trans (aNorm_nonneg _) ha)).trans hℓ'

omit [Fintype ι] [DecidableEq ι] in
/-- The paper's `e_sg` at a prime `p ≥ X_k` is at most its rational majorant `esgX k` at the piece
start (SD2's `esgPoly_mono`, as in `SignedDecomp.Block`). -/
theorem esgP_le_esgX (k : Fin 33) (hXp : ∀ i, XQ k ≤ pr i) (i : ι) :
    esgP pr i ≤ ((esgX k : ℚ) : ℝ) := by
  obtain ⟨hX24, hs1, hs2, -⟩ := table_check k
  have hX' : (2 : ℝ) ^ 24 ≤ (XQ k : ℝ) := by exact_mod_cast hX24
  have hXp' : ∀ i, (XQ k : ℝ) ≤ (pr i : ℝ) := fun i => by exact_mod_cast hXp i
  have h19 : ∀ i, 19 ≤ pr i := fun i => le_trans (by norm_num) (hX24.trans (hXp i))
  have hp0 : (0 : ℝ) < pr i := lt_of_lt_of_le (by positivity) (hX'.trans (hXp' i))
  have hΓA : GammaAP pr i ≤ ((gamX k : ℚ) : ℝ) := GammaA_le hX24 (hXp' i) hs2 hs1
  have hLeA : (atomsAt (pr i) (GammaAP pr i)).Le (AX k).cast :=
    atomsAt_le hX24 (hXp' i) hs2 hs1 ((gammaP_nonneg h19 i).trans (gammaP_le_GammaAP h19 i)) hΓA
  rw [show esgP pr i = esgPoly (atomsAt (pr i) (GammaAP pr i)) from esgL_eq hp0 _, esgX,
    esgPoly_cast]
  exact esgPoly_mono hLeA

end Block

end Sarkozy.FoldSymSkew
