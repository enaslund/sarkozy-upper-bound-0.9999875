module

public import Sarkozy.NormBoundsPaper4.FoldBlock

@[expose] public section

/-!
# The one-prime fold bounds `sym`, `skew` from the prime decompositions (FS)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(c) (Step 3 of its proof: the
symmetric part of the prime difference, and the skew part with the leading star `L°_{t,p}`), from
the two prime decompositions of the same proposition and of `lem:old-f-law`(f):

* reference: `Π_⊥ T_old Π_⊥ = O₀ + R^old`, `‖R^old‖ ≤ e_o q` (PG's `OldDecomp`; proved by PG's
  `oldDecomp_block` from a collision bound, e.g. FD's `collisionBound_73`);
* signed record: `Π_⊥ T[K_t] Π_⊥ = O₀ + L^m_t + R^new`, `‖R^new‖ ≤ e_sg q` (PG's `NewDecomp`,
  the last claim of `prop:signed-bounds`(c)).

On the centred functions the prime difference is `D_{t,p} = L^m_t + R^new − R^old`. Since `O₀` is
self-adjoint (`oForm_symm`), `L^m_t` is skew (`lForm_skew`) and the reference is symmetric:

* **`sym_of_decomp`**: `‖Sym D_{t,p}‖ ≤ (e_o + e_sg) q`;
* **`skew_of_decomp`**: `‖Skew D_{t,p}‖ ≤ ‖L^m_t‖ + e_sg q ≤ |a_t| Γ r + e_sg q`, with
  **`lForm_bound`**: `‖L^m_t‖ ≤ |a_t| Γ r` from the frame bound `FrameAt m Γ`
  (`lem:actual-features`(d)), `|a_t| = (t² + 1 + (1 − t)²)^{1/2}` (`aNorm`).

The statements are FD's `FoldPrimeBound` at `(½, ½, 1)` and `(½, −½, 0)`. This is a different
route from the paper's Step 3, which bounds `Sym Φ_t`, the removed query and `𝖢_rem` directly; it
uses the decompositions instead, which the direct prime Gram (`prop:signed-sides`(i)) needs anyway.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.FoldSymSkew

open Sarkozy.PrimeGram Sarkozy.NormBoundsPaper4 Sarkozy.SignedGram
open Sarkozy.Envelopes (aT)

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "qF" => (Fintype.card F : ℝ)

/-- `|a_t| = (t² + 1 + (1 − t)²)^{1/2}`, the Euclidean norm of `a_t = (t, 1, 1 − t)`. -/
noncomputable def aNorm (t : ℝ) : ℝ := √(∑ i, aT t i ^ 2)

theorem aNorm_sq (t : ℝ) : ∑ i, aT t i ^ 2 = t ^ 2 + 1 + (1 - t) ^ 2 := by
  simp only [Fin.sum_univ_three, aT, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring

omit [Field F] [DecidableEq F] in
theorem uip_cs (h k : F → ℝ) : uip h k ^ 2 ≤ uip h h * uip k k := by
  unfold uip
  have := sum_mul_sq_le_sq_mul_sq univ h k
  have e : ∀ x : F → ℝ, ∑ i, x i ^ 2 = ∑ i, x i * x i := fun x =>
    sum_congr rfl fun i _ => sq (x i)
  rw [e, e] at this
  have hq2 : 0 ≤ qF⁻¹ ^ 2 := sq_nonneg _
  calc (qF⁻¹ * ∑ a, h a * k a) ^ 2 = qF⁻¹ ^ 2 * (∑ a, h a * k a) ^ 2 := by ring
    _ ≤ qF⁻¹ ^ 2 * ((∑ a, h a * h a) * ∑ a, k a * k a) := mul_le_mul_of_nonneg_left this hq2
    _ = _ := by ring

omit [Field F] [DecidableEq F] in
/-- `(∑ a_i x_i)² ≤ |a|² ∑_i ‖B_i f‖² ‖k‖²` for `x_i = ⟨B_i f, k⟩`. -/
theorem sum_arm_sq (t : ℝ) (b : Fin 3 → F → ℝ) (k : F → ℝ) :
    (∑ i, aT t i * uip (b i) k) ^ 2 ≤
      (∑ i, aT t i ^ 2) * ((∑ i, uip (b i) (b i)) * uip k k) := by
  have h1 := sum_mul_sq_le_sq_mul_sq univ (aT t) fun i => uip (b i) k
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (sum_nonneg fun i _ => sq_nonneg _))
  rw [sum_mul]
  exact sum_le_sum fun i _ => uip_cs _ _

/-- **`‖L^m_t‖ ≤ |a_t| Γ r`** (`prop:signed-bounds`(c), leading star, through the frame of
`lem:actual-features`(d) instead of `lem:two-feature-spectrum`): for `f, g` with the frame bound,
`|⟨f, L^m_t g⟩_m| ≤ |a_t| Γ r ‖f‖_m ‖g‖_m`, `r = p^{-1/2}`. -/
theorem lForm_bound {Γ : ℝ} (m : (Fin 3 → F) → ℝ) (hm : ∀ x, 0 ≤ m x) (hΓ : 0 ≤ Γ) (t : ℝ)
    {f g : (Fin 3 → F) → ℝ} (hf : FrameAt m Γ f) (hg : FrameAt m Γ g) :
    |lForm m t f g| ≤ aNorm t * Γ * (√qF)⁻¹ * (√(mip m f f) * √(mip m g g)) := by
  unfold FrameAt at hf hg
  unfold lForm
  have hq : (0 : ℝ) < qF := Nat.cast_pos.mpr Fintype.card_pos
  set s := √qF
  have hs : 0 < s := Real.sqrt_pos.mpr hq
  have hs2 : s * s = qF := Real.mul_self_sqrt hq.le
  set A2 := ∑ i, aT t i ^ 2
  have hA2 : 0 ≤ A2 := sum_nonneg fun i _ => sq_nonneg _
  set wf := uip (Wa m f) (Wa m f)
  set wg := uip (Wa m g) (Wa m g)
  set bf := ∑ i, uip (Ba m i f) (Ba m i f)
  set bg := ∑ i, uip (Ba m i g) (Ba m i g)
  have hwf : 0 ≤ wf := uip_self_nonneg _
  have hwg : 0 ≤ wg := uip_self_nonneg _
  have hbf : 0 ≤ bf := sum_nonneg fun i _ => uip_self_nonneg _
  have hbg : 0 ≤ bg := sum_nonneg fun i _ => uip_self_nonneg _
  set X := ∑ i, aT t i * uip (Ba m i f) (Wa m g)
  set Y := ∑ i, aT t i * uip (Wa m f) (Ba m i g)
  have hX : X ^ 2 ≤ A2 * (bf * wg) := sum_arm_sq t (fun i => Ba m i f) (Wa m g)
  have hY : Y ^ 2 ≤ A2 * (bg * wf) := by
    have e : Y = ∑ i, aT t i * uip (Ba m i g) (Wa m f) :=
      sum_congr rfl fun i _ => by rw [uip_comm]
    rw [e]
    exact sum_arm_sq t (fun i => Ba m i g) (Wa m f)
  have hF1 : wf + qF * bf ≤ Γ * mip m f f := by linarith
  have hF2 : wg + qF * bg ≤ Γ * mip m g g := by linarith
  have hff := mip_self_nonneg hm f
  have hgg := mip_self_nonneg hm g
  -- `(X − Y)² p ≤ A2 (p b_f + w_f)(w_g + p b_g)`
  set U := qF ^ 2 * (bf * bg)
  set V := wf * wg
  have hU : 0 ≤ U := mul_nonneg (sq_nonneg _) (mul_nonneg hbf hbg)
  have hV : 0 ≤ V := mul_nonneg hwf hwg
  have hXY2 : (2 * qF * (X * Y)) ^ 2 ≤ (A2 * (U + V)) ^ 2 := by
    have h1 : (X * Y) ^ 2 ≤ (A2 * (bf * wg)) * (A2 * (bg * wf)) := by
      rw [mul_pow]
      exact mul_le_mul hX hY (sq_nonneg _) (mul_nonneg hA2 (mul_nonneg hbf hwg))
    have h2 : (2 * qF * (X * Y)) ^ 2 ≤ 4 * A2 ^ 2 * (U * V) := by
      have := mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) (sq_nonneg qF) :
        (0 : ℝ) ≤ 4 * qF ^ 2)
      have e1 : (2 * qF * (X * Y)) ^ 2 = 4 * qF ^ 2 * (X * Y) ^ 2 := by ring
      have e2 : 4 * A2 ^ 2 * (U * V) = 4 * qF ^ 2 * ((A2 * (bf * wg)) * (A2 * (bg * wf))) := by
        simp only [U, V]; ring
      rw [e1, e2]
      exact this
    have h3 : 4 * A2 ^ 2 * (U * V) ≤ (A2 * (U + V)) ^ 2 := by
      have : 4 * (U * V) ≤ (U + V) ^ 2 := by nlinarith [sq_nonneg (U - V)]
      have := mul_le_mul_of_nonneg_left this (sq_nonneg A2)
      nlinarith [this]
    exact h2.trans h3
  have hXYabs : -(A2 * (U + V)) ≤ 2 * qF * (X * Y) :=
    (abs_le_of_sq_le_sq' hXY2 (mul_nonneg hA2 (add_nonneg hU hV))).1
  have hmain : (X - Y) ^ 2 * qF ≤ A2 * ((qF * bf + wf) * (wg + qF * bg)) := by
    have e : A2 * ((qF * bf + wf) * (wg + qF * bg)) =
        qF * (A2 * (bf * wg)) + qF * (A2 * (bg * wf)) + A2 * (U + V) := by
      simp only [U, V]; ring
    rw [e]
    have hX' := mul_le_mul_of_nonneg_left hX hq.le
    have hY' := mul_le_mul_of_nonneg_left hY hq.le
    nlinarith
  have hR : (qF * bf + wf) * (wg + qF * bg) ≤ (Γ * mip m f f) * (Γ * mip m g g) :=
    mul_le_mul (by linarith) hF2 (add_nonneg hwg (mul_nonneg hq.le hbg))
      (mul_nonneg hΓ hff)
  have hsq : (X - Y) ^ 2 ≤
      (aNorm t * Γ * s⁻¹ * (√(mip m f f) * √(mip m g g))) ^ 2 := by
    have e2 : (aNorm t * Γ * s⁻¹ * (√(mip m f f) * √(mip m g g))) ^ 2 =
        A2 * ((Γ * mip m f f) * (Γ * mip m g g)) / qF := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hff, Real.sq_sqrt hgg, aNorm,
        Real.sq_sqrt hA2, inv_pow, sq s, hs2]
      field_simp
    rw [e2, le_div_iff₀ hq]
    exact hmain.trans (mul_le_mul_of_nonneg_left hR hA2)
  have hnn : 0 ≤ aNorm t * Γ * s⁻¹ * (√(mip m f f) * √(mip m g g)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hΓ) (inv_nonneg.mpr hs.le))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  exact abs_le.mpr (abs_le_of_sq_le_sq' hsq hnn)

/-! ## The prime difference from the decompositions -/

omit [Field F] [DecidableEq F] in
theorem dot_sum_smul (P : Fin 3 → Matrix (Fin 3 → F) (Fin 3 → F) ℝ) (w : Fin 3 → ℝ)
    (u v : (Fin 3 → F) → ℝ) :
    u ⬝ᵥ ((∑ c, w c • P c) *ᵥ v) = ∑ c, w c * (u ⬝ᵥ (P c *ᵥ v)) := by
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
    smul_eq_mul]

theorem split_half (w x y : Fin 3 → ℝ) (α₁ α₂ : ℝ) :
    ∑ c, w c * (α₁ * x c + α₂ * y c) = α₁ * ∑ c, w c * x c + α₂ * ∑ c, w c * y c := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun c _ => by ring

omit [Field F] [DecidableEq F] in
theorem mip_eq_sq (m u : (Fin 3 → F) → ℝ) : mip m u u = ∑ a, m a * u a ^ 2 := by
  unfold mip
  exact sum_congr rfl fun a _ => by ring

/-- **`prop:signed-bounds`(c), symmetric part, from the decompositions**: with
`T_old = O₀ + R^old` (`OldDecomp`, `e_o`) and `T' = O₀ + L^m_t + R^new` (`NewDecomp`, `e_sg`) on
the centred functions, `‖D^s_{t,p}‖ ≤ (e_o + e_sg) q`. -/
theorem sym_of_decomp {m : (Fin 3 → F) → ℝ} {P : Fin 3 → Matrix (Fin 3 → F) (Fin 3 → F) ℝ}
    {C₀ : Matrix (Fin 3 → F) (Fin 3 → F) ℝ} {w : Fin 3 → ℝ} {t eo esg : ℝ}
    (hold : OldDecomp m C₀ eo) (hnew : NewDecomp m (∑ c, w c • P c) t esg) :
    FoldPrimeBound m P C₀ w (1 / 2) (1 / 2) 1 ((eo + esg) * qF⁻¹) := by
  intro u v hu hv
  have hu' : m ⬝ᵥ u = 0 := hu
  have hv' : m ⬝ᵥ v = 0 := hv
  have h1 := hnew u v hu' hv'
  have h2 := hnew v u hv' hu'
  have h3 := hold u v hu' hv'
  rw [dot_sum_smul] at h1 h2
  have hS : mixChg1 P C₀ w (1 / 2) (1 / 2) 1 u v =
      1 / 2 * ((∑ c, w c * (u ⬝ᵥ (P c *ᵥ v))) - (oForm m u v + lForm m t u v)) +
        1 / 2 * ((∑ c, w c * (v ⬝ᵥ (P c *ᵥ u))) - (oForm m v u + lForm m t v u)) -
        (u ⬝ᵥ (C₀ *ᵥ v) - oForm m u v) := by
    unfold mixChg1
    rw [oForm_symm m v u, lForm_skew m t v u, split_half]
    ring
  rw [hS, ← mip_eq_sq, ← mip_eq_sq]
  have huv : √(mip m v v) * √(mip m u u) = √(mip m u u) * √(mip m v v) := mul_comm _ _
  rw [huv] at h2
  have hn : 0 ≤ qF⁻¹ * (√(mip m u u) * √(mip m v v)) := by positivity
  calc _ ≤ 1 / 2 * |(∑ c, w c * (u ⬝ᵥ (P c *ᵥ v))) - (oForm m u v + lForm m t u v)| +
        1 / 2 * |(∑ c, w c * (v ⬝ᵥ (P c *ᵥ u))) - (oForm m v u + lForm m t v u)| +
        |u ⬝ᵥ (C₀ *ᵥ v) - oForm m u v| := by
        refine (abs_sub _ _).trans (add_le_add_left ?_ _)
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ 1 / 2 * (esg * qF⁻¹ * (√(mip m u u) * √(mip m v v))) +
        1 / 2 * (esg * qF⁻¹ * (√(mip m u u) * √(mip m v v))) +
        eo * qF⁻¹ * (√(mip m u u) * √(mip m v v)) := by gcongr
    _ = (eo + esg) * qF⁻¹ * √(mip m u u) * √(mip m v v) := by ring

/-- **`prop:signed-bounds`(c), skew part, from the decomposition of the signed record**: the
reference is symmetric, so `Skew D_{t,p} = L^m_t + Skew R^new` and
`‖D^a_{t,p}‖ ≤ |a_t| Γ r + e_sg q` (`lForm_bound`). -/
theorem skew_of_decomp {m : (Fin 3 → F) → ℝ} {P : Fin 3 → Matrix (Fin 3 → F) (Fin 3 → F) ℝ}
    {C₀ : Matrix (Fin 3 → F) (Fin 3 → F) ℝ} {w : Fin 3 → ℝ} {t esg Γ : ℝ}
    (hm : ∀ x, 0 ≤ m x) (hΓ : 0 ≤ Γ) (hframe : ∀ f, FrameAt m Γ f)
    (hnew : NewDecomp m (∑ c, w c • P c) t esg) :
    FoldPrimeBound m P C₀ w (1 / 2) (-1 / 2) 0
      (aNorm t * Γ * (√qF)⁻¹ + esg * qF⁻¹) := by
  intro u v hu hv
  have hu' : m ⬝ᵥ u = 0 := hu
  have hv' : m ⬝ᵥ v = 0 := hv
  have h1 := hnew u v hu' hv'
  have h2 := hnew v u hv' hu'
  have hL := lForm_bound m hm hΓ t (hframe u) (hframe v)
  rw [dot_sum_smul] at h1 h2
  have hS : mixChg1 P C₀ w (1 / 2) (-1 / 2) 0 u v =
      1 / 2 * ((∑ c, w c * (u ⬝ᵥ (P c *ᵥ v))) - (oForm m u v + lForm m t u v)) -
        1 / 2 * ((∑ c, w c * (v ⬝ᵥ (P c *ᵥ u))) - (oForm m v u + lForm m t v u)) +
        lForm m t u v := by
    unfold mixChg1
    rw [oForm_symm m v u, lForm_skew m t v u, split_half]
    ring
  rw [hS, ← mip_eq_sq, ← mip_eq_sq]
  have huv : √(mip m v v) * √(mip m u u) = √(mip m u u) * √(mip m v v) := mul_comm _ _
  rw [huv] at h2
  calc _ ≤ 1 / 2 * |(∑ c, w c * (u ⬝ᵥ (P c *ᵥ v))) - (oForm m u v + lForm m t u v)| +
        1 / 2 * |(∑ c, w c * (v ⬝ᵥ (P c *ᵥ u))) - (oForm m v u + lForm m t v u)| +
        |lForm m t u v| := by
        refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ 1 / 2 * (esg * qF⁻¹ * (√(mip m u u) * √(mip m v v))) +
        1 / 2 * (esg * qF⁻¹ * (√(mip m u u) * √(mip m v v))) +
        aNorm t * Γ * (√qF)⁻¹ * (√(mip m u u) * √(mip m v v)) := by gcongr
    _ = (aNorm t * Γ * (√qF)⁻¹ + esg * qF⁻¹) * √(mip m u u) * √(mip m v v) := by ring

end Sarkozy.FoldSymSkew
