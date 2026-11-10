module

public import Sarkozy.SharpBase2.PerTerm

@[expose] public section

/-!
# The three error terms of `lem:sharp-first`, separated

SUM (7 November 2026). SH2's per-term remainder `rchPT` (`SharpBase2.PerTerm`) is, at one choice
and tag, `∑_φ w_φ pieceRem(φ)`. It is the sum of the paper's three error terms of the proof of
`lem:sharp-first`:

* the **chain²** term `C ∑_{small φ} w_φ √(G₊(φ) G₋(φ))` (the product of the two chain
  remainders of `prop:record:density-structured`, `C = C_dc L^{-σ} α`);
* the **cross** term `√C ∑_{small φ} w_φ (√(BG M₊ G₋) + √(G₊ BG M₋))` (main term of one fold times
  the chain remainder of the other);
* the **large-piece** term `∑_{¬small φ} w_φ √𝔈₊(φ) √𝔈₋(φ)` (`lem:record:density-lp`, the terms
  `a_E (I⁺_E I⁻_E)^{1/2}`).

Here:

* `chainPart`, `crossPart`, `largePart` and **`rchPT_eq_split`** (an identity, `C ≥ 0` only);
* `chainPart_le`: `√(G₊G₋) ≤ U` from `G_± ≤ U` on the support of `w`;
* `crossPart_le`: from `G_± ≤ BG V` on the support of `w`, the cross term is at most
  `√K₀ (√P₊ + √P₋) ∑_φ w_φ BG(φ) √V(φ)` (the main prices are `M_± = K₀ P_±`);
* `largePart_le_rankin`: Rankin's trick (`lem:record:density-lp`) for pieces indexed by
  arbitrary finite types, `∑_{T < ∏ q} ∏ g ≤ T^{-1/4} ∏_b ∑_x g_b(x) q_b(x)^{1/4}`;
* `sqrt_mul_sqrt_le_half`: `√x √y ≤ (x + y)/2` (the large pieces are averaged one fold at a time).
-/

open Finset

namespace Sarkozy.SharpSums

open Sarkozy.SharpBase2

section Split

variable {Φ : Type} [Fintype Φ]

/-- **The chain² part** of `rchPT`: `∑_{small φ} w_φ √(G₊(φ) G₋(φ))`. -/
noncomputable def chainPart (small : Φ → Prop) (w Gp Gm : Φ → ℝ) : ℝ :=
  ∑ φ, w φ * (open Classical in if small φ then Real.sqrt (Gp φ * Gm φ) else 0)

/-- **The cross part** of `rchPT`: `∑_{small φ} w_φ (√(BG M₊ G₋) + √(G₊ BG M₋))`. -/
noncomputable def crossPart (small : Φ → Prop) (Mp Mm : ℝ) (w BG Gp Gm : Φ → ℝ) : ℝ :=
  ∑ φ, w φ * (open Classical in if small φ then
    Real.sqrt (BG φ * Mp * Gm φ) + Real.sqrt (Gp φ * BG φ * Mm) else 0)

/-- **The large-piece part** of `rchPT`: `∑_{¬small φ} w_φ √𝔈₊(φ) √𝔈₋(φ)`. -/
noncomputable def largePart (small : Φ → Prop) (w Fp Fm : Φ → ℝ) : ℝ :=
  ∑ φ, w φ * (open Classical in if small φ then 0 else Real.sqrt (Fp φ) * Real.sqrt (Fm φ))

omit [Fintype Φ] in
open Classical in
/-- One piece: `pieceRem = √C (cross) + C (chain²) + (large)`, for `C ≥ 0`. -/
theorem pieceRem_eq_split (small : Φ → Prop) (BG Gp Gm Fp Fm : Φ → ℝ) (Mp Mm : ℝ) {Cr : ℝ}
    (hCr : 0 ≤ Cr) (φ : Φ) :
    pieceRem small BG Gp Gm Fp Fm Mp Mm Cr φ =
      Real.sqrt Cr * (if small φ then
          Real.sqrt (BG φ * Mp * Gm φ) + Real.sqrt (Gp φ * BG φ * Mm) else 0) +
        Cr * (if small φ then Real.sqrt (Gp φ * Gm φ) else 0) +
        (if small φ then 0 else Real.sqrt (Fp φ) * Real.sqrt (Fm φ)) := by
  unfold pieceRem
  split_ifs
  · have e1 : BG φ * Mp * (Gm φ * Cr) = (BG φ * Mp * Gm φ) * Cr := by ring
    have e2 : Gp φ * Cr * (BG φ * Mm) = (Gp φ * BG φ * Mm) * Cr := by ring
    have e3 : Gp φ * Cr * (Gm φ * Cr) = (Gp φ * Gm φ) * Cr ^ 2 := by ring
    rw [e1, e2, e3, Real.sqrt_mul' _ hCr, Real.sqrt_mul' _ hCr, Real.sqrt_mul' _ (sq_nonneg Cr),
      Real.sqrt_sq hCr]
    ring
  · ring

/-- **`rchPT` is the sum of the three error terms** of `lem:sharp-first` (an identity; only
`C ≥ 0` is used): `rchPT = √C · crossPart + C · chainPart + largePart`, with the main prices
`M_± = K₀ P_±`. -/
theorem rchPT_eq_split (small : Φ → Prop) (K₀ Pp Pm : ℝ) {Cr : ℝ} (hCr : 0 ≤ Cr)
    (w BG Gp Gm Fp Fm : Φ → ℝ) :
    rchPT small K₀ Pp Pm Cr w BG Gp Gm Fp Fm =
      Real.sqrt Cr * crossPart small (K₀ * Pp) (K₀ * Pm) w BG Gp Gm +
        Cr * chainPart small w Gp Gm + largePart small w Fp Fm := by
  unfold rchPT crossPart chainPart largePart
  rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun φ _ => ?_
  rw [pieceRem_eq_split small BG Gp Gm Fp Fm _ _ hCr φ]
  ring

theorem chainPart_nonneg (small : Φ → Prop) (w Gp Gm : Φ → ℝ) (hw : ∀ φ, 0 ≤ w φ) :
    0 ≤ chainPart small w Gp Gm := by
  unfold chainPart
  refine sum_nonneg fun φ _ => mul_nonneg (hw φ) ?_
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_rfl

theorem crossPart_nonneg (small : Φ → Prop) (Mp Mm : ℝ) (w BG Gp Gm : Φ → ℝ)
    (hw : ∀ φ, 0 ≤ w φ) : 0 ≤ crossPart small Mp Mm w BG Gp Gm := by
  unfold crossPart
  refine sum_nonneg fun φ _ => mul_nonneg (hw φ) ?_
  split_ifs
  · positivity
  · exact le_rfl

theorem largePart_nonneg (small : Φ → Prop) (w Fp Fm : Φ → ℝ) (hw : ∀ φ, 0 ≤ w φ) :
    0 ≤ largePart small w Fp Fm := by
  unfold largePart
  refine sum_nonneg fun φ _ => mul_nonneg (hw φ) ?_
  split_ifs
  · exact le_rfl
  · positivity

/-- **The chain² part, bounded**: if `0 ≤ G_± ≤ U` wherever `w ≠ 0`, then
`chainPart ≤ ∑_φ w_φ U(φ)` (the restriction to small pieces is dropped). -/
theorem chainPart_le (small : Φ → Prop) (w Gp Gm U : Φ → ℝ) (hw : ∀ φ, 0 ≤ w φ)
    (hU : ∀ φ, 0 ≤ U φ) (hGp0 : ∀ φ, 0 ≤ Gp φ)
    (hGp : ∀ φ, w φ ≠ 0 → Gp φ ≤ U φ) (hGm : ∀ φ, w φ ≠ 0 → Gm φ ≤ U φ) :
    chainPart small w Gp Gm ≤ ∑ φ, w φ * U φ := by
  unfold chainPart
  refine sum_le_sum fun φ _ => ?_
  rcases eq_or_ne (w φ) 0 with h0 | h0
  · simp [h0]
  refine mul_le_mul_of_nonneg_left ?_ (hw φ)
  split_ifs
  · rw [Real.sqrt_le_left (hU φ)]
    have := hGm φ h0
    have hUU : Gp φ * Gm φ ≤ U φ * U φ := by
      rcases le_or_gt 0 (Gm φ) with hg | hg
      · exact mul_le_mul (hGp φ h0) this hg (hU φ)
      · nlinarith [hGp0 φ, hU φ]
    nlinarith
  · exact hU φ

/-- **The cross part, bounded**: if `G_± ≤ BG V` wherever `w ≠ 0` (with `BG, V ≥ 0`), and the
main prices are `M_± = K₀ P_±` with `K₀, P_± ≥ 0`, then
`crossPart ≤ √K₀ (√P₊ + √P₋) ∑_φ w_φ BG(φ) √V(φ)`. -/
theorem crossPart_le (small : Φ → Prop) {K₀ Pp Pm : ℝ} (hK : 0 ≤ K₀) (hPp : 0 ≤ Pp)
    (hPm : 0 ≤ Pm) (w BG Gp Gm V : Φ → ℝ) (hw : ∀ φ, 0 ≤ w φ) (hBG : ∀ φ, 0 ≤ BG φ)
    (hV : ∀ φ, 0 ≤ V φ)
    (hGp : ∀ φ, w φ ≠ 0 → Gp φ ≤ BG φ * V φ) (hGm : ∀ φ, w φ ≠ 0 → Gm φ ≤ BG φ * V φ) :
    crossPart small (K₀ * Pp) (K₀ * Pm) w BG Gp Gm ≤
      Real.sqrt K₀ * (Real.sqrt Pp + Real.sqrt Pm) *
        ∑ φ, w φ * (BG φ * Real.sqrt (V φ)) := by
  unfold crossPart
  rw [mul_sum]
  refine sum_le_sum fun φ _ => ?_
  rcases eq_or_ne (w φ) 0 with h0 | h0
  · simp [h0]
  have key : ∀ (G M : ℝ), 0 ≤ M → G ≤ BG φ * V φ →
      Real.sqrt (BG φ * M * G) ≤ BG φ * Real.sqrt (V φ) * Real.sqrt M := by
    intro G M hM hG
    have h1 : BG φ * M * G ≤ (BG φ * Real.sqrt (V φ) * Real.sqrt M) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (hV φ), Real.sq_sqrt hM]
      have := mul_le_mul_of_nonneg_left hG (mul_nonneg (hBG φ) hM)
      nlinarith
    calc Real.sqrt (BG φ * M * G) ≤ Real.sqrt ((BG φ * Real.sqrt (V φ) * Real.sqrt M) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = _ := Real.sqrt_sq (by have := hBG φ; positivity)
  have hp := key (Gm φ) (K₀ * Pp) (mul_nonneg hK hPp) (hGm φ h0)
  have hm : Real.sqrt (Gp φ * BG φ * (K₀ * Pm)) ≤
      BG φ * Real.sqrt (V φ) * Real.sqrt (K₀ * Pm) := by
    have e : Gp φ * BG φ * (K₀ * Pm) = BG φ * (K₀ * Pm) * Gp φ := by ring
    rw [e]
    exact key (Gp φ) (K₀ * Pm) (mul_nonneg hK hPm) (hGp φ h0)
  rw [Real.sqrt_mul hK] at hp hm
  have hBV : 0 ≤ BG φ * Real.sqrt (V φ) := mul_nonneg (hBG φ) (Real.sqrt_nonneg _)
  split_ifs
  · calc w φ * (Real.sqrt (BG φ * (K₀ * Pp) * Gm φ) + Real.sqrt (Gp φ * BG φ * (K₀ * Pm)))
        ≤ w φ * (BG φ * Real.sqrt (V φ) * (Real.sqrt K₀ * Real.sqrt Pp) +
            BG φ * Real.sqrt (V φ) * (Real.sqrt K₀ * Real.sqrt Pm)) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hp hm) (hw φ)
      _ = _ := by ring
  · rw [mul_zero]
    have := hw φ
    positivity

/-- `√x √y ≤ (x + y)/2` for `x, y ≥ 0`. -/
theorem sqrt_mul_sqrt_le_half {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt x * Real.sqrt y ≤ (x + y) / 2 := by
  have h := sq_nonneg (Real.sqrt x - Real.sqrt y)
  rw [sub_sq, Real.sq_sqrt hx, Real.sq_sqrt hy] at h
  linarith

/-- **The large part, by one fold at a time**: `largePart ≤ ∑_{¬small} w (𝔈₊ + 𝔈₋)/2`. -/
theorem largePart_le_half (small : Φ → Prop) (w Fp Fm : Φ → ℝ) (hw : ∀ φ, 0 ≤ w φ)
    (hFp : ∀ φ, 0 ≤ Fp φ) (hFm : ∀ φ, 0 ≤ Fm φ) :
    largePart small w Fp Fm ≤
      ∑ φ, w φ * (open Classical in if small φ then 0 else (Fp φ + Fm φ) / 2) := by
  unfold largePart
  refine sum_le_sum fun φ _ => mul_le_mul_of_nonneg_left ?_ (hw φ)
  split_ifs
  · exact le_rfl
  · exact sqrt_mul_sqrt_le_half (hFp φ) (hFm φ)

end Split

section Rankin

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} [∀ b, Fintype (X b)]

/-- **Rankin's trick for pieces** (`lem:record:density-lp`, last display): for nonnegative
`g_b(x)`, `q_b(x) ≥ 0` and `T > 0`,
`∑_{φ : T < ∏_b q_b(φ_b)} ∏_b g_b(φ_b) ≤ T^{-1/4} ∏_b ∑_x g_b(x) q_b(x)^{1/4}`. -/
theorem sum_large_pieces_le (g q : ∀ b, X b → ℝ) (hg : ∀ b x, 0 ≤ g b x) (hq : ∀ b x, 0 ≤ q b x)
    {T : ℝ} (hT : 0 < T) :
    ∑ φ ∈ univ.filter (fun φ : (∀ b, X b) => T < ∏ b, q b (φ b)), ∏ b, g b (φ b) ≤
      T ^ (-((1 : ℝ) / 4)) * ∏ b, ∑ x, g b x * q b x ^ ((1 : ℝ) / 4) := by
  rw [Fintype.prod_sum (fun b x => g b x * q b x ^ ((1 : ℝ) / 4)), mul_sum]
  calc ∑ φ ∈ univ.filter (fun φ : (∀ b, X b) => T < ∏ b, q b (φ b)), ∏ b, g b (φ b)
      ≤ ∑ φ ∈ univ.filter (fun φ : (∀ b, X b) => T < ∏ b, q b (φ b)),
          T ^ (-((1 : ℝ) / 4)) * ∏ b, (g b (φ b) * q b (φ b) ^ ((1 : ℝ) / 4)) := by
        refine sum_le_sum fun φ hφ => ?_
        have hlt := (mem_filter.mp hφ).2
        rw [prod_mul_distrib]
        have hq0 : 0 ≤ ∏ b, q b (φ b) := prod_nonneg fun b _ => hq b (φ b)
        have e : ∏ b, q b (φ b) ^ ((1 : ℝ) / 4) = (∏ b, q b (φ b)) ^ ((1 : ℝ) / 4) :=
          Real.finsetProd_rpow _ _ (fun b _ => hq b (φ b)) _
        rw [e]
        have hpow : T ^ ((1 : ℝ) / 4) ≤ (∏ b, q b (φ b)) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow hT.le hlt.le (by norm_num)
        have hTp : 0 < T ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hT _
        have hinv : T ^ (-((1 : ℝ) / 4)) * T ^ ((1 : ℝ) / 4) = 1 := by
          rw [← Real.rpow_add hT]; norm_num
        have hg0 : 0 ≤ ∏ b, g b (φ b) := prod_nonneg fun b _ => hg b (φ b)
        calc ∏ b, g b (φ b) = T ^ (-((1 : ℝ) / 4)) * ((∏ b, g b (φ b)) * T ^ ((1 : ℝ) / 4)) := by
              rw [mul_comm (∏ b, g b (φ b)), ← mul_assoc, hinv, one_mul]
          _ ≤ T ^ (-((1 : ℝ) / 4)) * ((∏ b, g b (φ b)) * (∏ b, q b (φ b)) ^ ((1 : ℝ) / 4)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hg0)
                (Real.rpow_nonneg hT.le _)
          _ = _ := by ring
    _ ≤ ∑ φ : (∀ b, X b), T ^ (-((1 : ℝ) / 4)) * ∏ b, (g b (φ b) * q b (φ b) ^ ((1 : ℝ) / 4)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun φ _ _ =>
          mul_nonneg (Real.rpow_nonneg hT.le _) (prod_nonneg fun b _ =>
            mul_nonneg (hg b (φ b)) (Real.rpow_nonneg (hq b (φ b)) _))

end Rankin

end Sarkozy.SharpSums
