module

public import Sarkozy.FoldSymSkew.Block

@[expose] public section

/-!
# The leading star at one prime: the split of the skew fold difference (OPS-L)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(b),(c); `paper/sections/
23_envelopes.tex`, the star form (N1).

FS's `skew_of_decomp` bounds the skew part of a prime fold difference jointly,
`‖D^a_{t,p}‖ ≤ |a_t| Γ r + e_sg q`, from PG's decomposition of the signed record
`Π_⊥ T[K_t] Π_⊥ = O₀ + L^m_t + R^new` (`NewDecomp`). The star form (N1) needs the two parts
**separately**. This file states and proves them:

* **`skew_split_of_decomp`**: on centred functions, `|D^a(u, v) − L^m_t(u, v)| ≤ e_sg q ‖u‖ ‖v‖`
  and `|L^m_t(u, v)| ≤ |a_t| Γ r ‖u‖ ‖v‖` (`prop:signed-bounds`(c): `‖D^a − L°‖ ≤ a_p q`,
  `‖L°‖ ≤ ℓ_t r`);
* **`skewSplit_block`**: the same at every prime of a middle block of piece `k`, at FS's piece
  constants: `‖D^a_p − L^m_p‖ ≤ a_F p^{-1}` and `‖L^m_p‖ ≤ ℓ p^{-1/2}` for every `a_F ≥ E`,
  `ℓ ≥ aNU Γ_X` (`SkewSplitPrime`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.FoldSymSkew Sarkozy.PrimeGram Sarkozy.NormBoundsPaper4 Sarkozy.SignedGram
  Sarkozy.PartV Sarkozy.SignedComponents Sarkozy.SignedDecomp
open Sarkozy.MiddleComparison (signedCoef)
open Sarkozy.MainFinal2 (tPaper)

section Prime

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "qF" => (Fintype.card F : ℝ)

/-- **The split of the skew part at one prime** (`prop:signed-bounds`(c)): with PG's
decomposition of the signed record, on centred functions the skew form of the prime difference
minus the leading star form is at most `e_sg q`, and the leading star form at most `|a_t| Γ r`. -/
theorem skew_split_of_decomp {m : (Fin 3 → F) → ℝ}
    {P : Fin 3 → Matrix (Fin 3 → F) (Fin 3 → F) ℝ} {C₀ : Matrix (Fin 3 → F) (Fin 3 → F) ℝ}
    {w : Fin 3 → ℝ} {t esg Γ : ℝ} (hm : ∀ x, 0 ≤ m x) (hΓ : 0 ≤ Γ)
    (hframe : ∀ f, FrameAt m Γ f) (hnew : NewDecomp m (∑ c, w c • P c) t esg)
    (u v : (Fin 3 → F) → ℝ) (hu : ∑ a, m a * u a = 0) (hv : ∑ a, m a * v a = 0) :
    |mixChg1 P C₀ w (1 / 2) (-1 / 2) 0 u v - lForm m t u v| ≤
        esg * qF⁻¹ * Real.sqrt (∑ a, m a * u a ^ 2) * Real.sqrt (∑ a, m a * v a ^ 2) ∧
      |lForm m t u v| ≤
        aNorm t * Γ * (√qF)⁻¹ * Real.sqrt (∑ a, m a * u a ^ 2) *
          Real.sqrt (∑ a, m a * v a ^ 2) := by
  have hu' : m ⬝ᵥ u = 0 := hu
  have hv' : m ⬝ᵥ v = 0 := hv
  have h1 := hnew u v hu' hv'
  have h2 := hnew v u hv' hu'
  have hL := lForm_bound m hm hΓ t (hframe u) (hframe v)
  rw [dot_sum_smul] at h1 h2
  have hS : mixChg1 P C₀ w (1 / 2) (-1 / 2) 0 u v - lForm m t u v =
      1 / 2 * ((∑ c, w c * (u ⬝ᵥ (P c *ᵥ v))) - (oForm m u v + lForm m t u v)) -
        1 / 2 * ((∑ c, w c * (v ⬝ᵥ (P c *ᵥ u))) - (oForm m v u + lForm m t v u)) := by
    unfold mixChg1
    rw [oForm_symm m v u, lForm_skew m t v u, split_half]
    ring
  rw [← mip_eq_sq, ← mip_eq_sq]
  refine ⟨?_, by linarith [hL, mul_assoc (aNorm t * Γ * (√qF)⁻¹) (√(mip m u u)) (√(mip m v v))]⟩
  rw [hS]
  have huv : √(mip m v v) * √(mip m u u) = √(mip m u u) * √(mip m v v) := mul_comm _ _
  rw [huv] at h2
  calc _ ≤ 1 / 2 * |(∑ c, w c * (u ⬝ᵥ (P c *ᵥ v))) - (oForm m u v + lForm m t u v)| +
        1 / 2 * |(∑ c, w c * (v ⬝ᵥ (P c *ᵥ u))) - (oForm m v u + lForm m t v u)| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ 1 / 2 * (esg * qF⁻¹ * (√(mip m u u) * √(mip m v v))) +
        1 / 2 * (esg * qF⁻¹ * (√(mip m u u) * √(mip m v v))) := by gcongr
    _ = esg * qF⁻¹ * √(mip m u u) * √(mip m v v) := by ring

end Prime

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

/-- **The split of the skew fold difference at a prime of a middle block** (the content of
(N1) at one prime): on centred functions, `|D^a_p(u, v) − L^m_p(u, v)| ≤ ρ ‖u‖ ‖v‖` and
`|L^m_p(u, v)| ≤ ℓ' ‖u‖ ‖v‖` in `L²(m_p)`. -/
def SkewSplitPrime (hne : MiddleNonempty pr) (C : FoldComponents pr hne) (t ℓ' ρ : ℝ) (i : ι) :
    Prop :=
  ∀ u v : (Fin 3 → ZMod (pr i)) → ℝ, ∑ a, mP hne i a * u a = 0 → ∑ a, mP hne i a * v a = 0 →
    |mixChg1 (fun c => compP hne C c i) (oldP hne i) (signedCoef t) (1 / 2) (-1 / 2) 0 u v -
        lForm (mP hne i) t u v| ≤
      ρ * Real.sqrt (∑ a, mP hne i a * u a ^ 2) * Real.sqrt (∑ a, mP hne i a * v a ^ 2) ∧
    |lForm (mP hne i) t u v| ≤
      ℓ' * Real.sqrt (∑ a, mP hne i a * u a ^ 2) * Real.sqrt (∑ a, mP hne i a * v a ^ 2)

omit [Fintype ι] [DecidableEq ι] in
/-- **`prop:signed-bounds`(c) with the leading star split off, at every prime of a middle block
of piece `k`** (from `NewDecomp` at the constant `E`, as FS's `symSkew_block`):
`‖D^a_p − L^m_p‖ ≤ a_F p^{-1}` and `‖L^m_p‖ ≤ ℓ p^{-1/2}` for `E ≤ a_F`, `aNU Γ_X ≤ ℓ`. -/
theorem skewSplit_block (hne : MiddleNonempty pr) (C : FoldComponents pr hne)
    (h3 : ∀ i, pr i % 4 = 3) (k : Fin 33) (hXp : ∀ i, XQ k ≤ pr i) {E aF ℓ : ℝ}
    (hnew : ∀ i, NewDecomp (mP hne i) (∑ c, signedCoef tPaper c • compP hne C c i) tPaper E)
    (haF : E ≤ aF) (hℓ : ((aNU * gamX k : ℚ) : ℝ) ≤ ℓ) (i : ι) :
    SkewSplitPrime hne C tPaper (ℓ * rP pr i) (aF * rP pr i ^ 2) i := by
  obtain ⟨hX24, hs1, hs2, -⟩ := table_check k
  obtain ⟨p1, -, -, -, -, -⟩ := pos_check k
  have hX' : (2 : ℝ) ^ 24 ≤ (XQ k : ℝ) := by exact_mod_cast hX24
  have hXp' : ∀ i, (XQ k : ℝ) ≤ (pr i : ℝ) := fun i => by exact_mod_cast hXp i
  have h19 : ∀ i, 19 ≤ pr i := fun i => le_trans (by norm_num) (hX24.trans (hXp i))
  have hγ0 : ∀ i, 0 ≤ gammaP pr i := gammaP_nonneg h19
  have hγA : ∀ i, gammaP pr i ≤ GammaAP pr i := gammaP_le_GammaAP h19
  have hΓA : ∀ i, GammaAP pr i ≤ ((gamX k : ℚ) : ℝ) := fun i => GammaA_le hX24 (hXp' i) hs2 hs1
  have hq : ((Fintype.card (ZMod (pr i)) : ℝ))⁻¹ = rP pr i ^ 2 := by
    rw [card_zmod, rP, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hr : (√(Fintype.card (ZMod (pr i)) : ℝ))⁻¹ = rP pr i := by
    rw [card_zmod]; rfl
  have hrP0 : 0 ≤ rP pr i := inv_nonneg.mpr (Real.sqrt_nonneg _)
  intro u v hu hv
  have h := skew_split_of_decomp (P := fun c => compP hne C c i) (C₀ := oldP hne i)
    (w := signedCoef tPaper) (mP_nonneg hne i) (hγ0 i) (frame_block hne h3 h19 i) (hnew i)
    u v hu hv
  rw [hq, hr] at h
  have hsu := Real.sqrt_nonneg (∑ a, mP hne i a * u a ^ 2)
  have hsv := Real.sqrt_nonneg (∑ a, mP hne i a * v a ^ 2)
  have hℓ0 : aNorm tPaper * gammaP pr i ≤ ℓ := by
    have ha := aNorm_le
    have hG : gammaP pr i ≤ ((gamX k : ℚ) : ℝ) := (hγA i).trans (hΓA i)
    have hℓ' : ((aNU : ℚ) : ℝ) * ((gamX k : ℚ) : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    exact (mul_le_mul ha hG (hγ0 i) (le_trans (aNorm_nonneg _) ha)).trans hℓ'
  refine ⟨h.1.trans ?_, h.2.trans ?_⟩
  · gcongr
  · gcongr

end Block

end Sarkozy.OpsCore
