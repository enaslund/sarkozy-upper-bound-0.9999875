module

public import Sarkozy.PrimeGram.Block

@[expose] public section

/-!
# Non-vacuity of the prime decompositions and gates (PG)

The hypotheses `DecompAt` and `GateAt` of `Block.lean` hold, on the paper's very objects (SGA's
`mP`, `oldP`, `compP` at **every** fold components `C` of **every** middle block), with crude
constants and a large shift:

* `coupling_dot_le`: `|⟨f, T g⟩_m| ≤ ‖f‖_m ‖g‖_m` for a coupling with both marginals `m`;
* `uip_sq_le`, `ba_wa_le`, `wa_ba_le`: from the frame bound, every term of the leading forms is at
  most `Γ r ‖f‖ ‖g‖`; so `|⟨f, O₀ g⟩| ≤ 2 Γ r ‖f‖ ‖g‖` and `|⟨f, L^m_t g⟩| ≤ 6 Γ r ‖f‖ ‖g‖`;
* `gammaW_le_two`: W6's frame constant is at most `2` for `p ≥ 19`;
* `oldDecomp_crude`, `newDecomp_crude`: `OldDecomp` with `e_o = p(1 + 2Γ)` and `NewDecomp` with
  `e_sg = p(2 + 8Γ)`;
* **`decompGateAt_large`**: `DecompGateAt` (decompositions and gates) holds at every middle block
  whenever the shift `r d / H_𝔅` is at least `28`.

So the hypotheses are jointly satisfiable at the paper's objects and the chain does not assume
anything contradictory; their content is that they hold with the paper's constants
(`e_o ≈ 7.6`, `e_sg`, `c_+ ≈ √3`) at the small shift `σ ≈ 2.4 r_b` (`prop:signed-sides`(i)).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.PrimeGram

open Sarkozy.TraceMixing Sarkozy.MiddleRecords Sarkozy.Envelopes Sarkozy.SignedGram
open Sarkozy.PartV Sarkozy.SignedComponents Sarkozy.MiddleComparison
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "qF" => (Fintype.card F : ℝ)

/-! ## Elementary bounds -/

omit [Field F] [DecidableEq F] in
/-- Cauchy–Schwarz in `H₀`. -/
theorem uip_sq_le (h k : F → ℝ) : uip h k ^ 2 ≤ uip h h * uip k k := by
  unfold uip
  have := sum_mul_sq_le_sq_mul_sq univ h k
  have e : ∀ x : F → ℝ, ∑ i, x i ^ 2 = ∑ i, x i * x i := fun x =>
    sum_congr rfl fun i _ => sq (x i)
  rw [e, e] at this
  have hq2 : 0 ≤ qF⁻¹ ^ 2 := sq_nonneg _
  calc (qF⁻¹ * ∑ a, h a * k a) ^ 2 = qF⁻¹ ^ 2 * (∑ a, h a * k a) ^ 2 := by ring
    _ ≤ qF⁻¹ ^ 2 * ((∑ a, h a * h a) * ∑ a, k a * k a) :=
        mul_le_mul_of_nonneg_left this hq2
    _ = _ := by ring

/-- `x² ≤ A B`, `0 ≤ A ≤ a`, `0 ≤ B ≤ b` give `|x| ≤ √a √b`. -/
theorem abs_le_of_sq_le {x A B a b : ℝ} (h : x ^ 2 ≤ A * B) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : A ≤ a) (hb : B ≤ b) : |x| ≤ √a * √b := by
  have h1 : x ^ 2 ≤ a * b := h.trans (mul_le_mul ha hb hB (hA.trans ha))
  rw [← Real.sqrt_mul (hA.trans ha)]
  exact Real.abs_le_sqrt h1

omit [Field F] [DecidableEq F] in
/-- **The coupling bound**: for a nonnegative coupling `C` with both marginals `m`,
`|⟨f, C g⟩| ≤ ‖f‖_m ‖g‖_m`. -/
theorem coupling_dot_le {m : (Fin 3 → F) → ℝ} {C : Matrix (Fin 3 → F) (Fin 3 → F) ℝ}
    (hC : ∀ a b, 0 ≤ C a b) (hrow : ∀ a, ∑ b, C a b = m a) (hcol : ∀ b, ∑ a, C a b = m b)
    (f g : (Fin 3 → F) → ℝ) : |f ⬝ᵥ (C *ᵥ g)| ≤ √(mip m f f) * √(mip m g g) := by
  have e1 : f ⬝ᵥ (C *ᵥ g) = ∑ p : (Fin 3 → F) × (Fin 3 → F),
      (√(C p.1 p.2) * f p.1) * (√(C p.1 p.2) * g p.2) := by
    rw [Fintype.sum_prod_type]
    simp only [dotProduct, mulVec, mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    have := Real.mul_self_sqrt (hC a b)
    rw [show √(C a b) * f a * (√(C a b) * g b) = (√(C a b) * √(C a b)) * f a * g b by ring,
      this]
    ring
  have e2 : ∑ p : (Fin 3 → F) × (Fin 3 → F), (√(C p.1 p.2) * f p.1) ^ 2 = mip m f f := by
    rw [Fintype.sum_prod_type]
    unfold mip
    refine sum_congr rfl fun a _ => ?_
    rw [← hrow a, sum_mul, sum_mul]
    refine sum_congr rfl fun b _ => ?_
    rw [mul_pow, Real.sq_sqrt (hC a b)]
    ring
  have e3 : ∑ p : (Fin 3 → F) × (Fin 3 → F), (√(C p.1 p.2) * g p.2) ^ 2 = mip m g g := by
    rw [Fintype.sum_prod_type, sum_comm]
    unfold mip
    refine sum_congr rfl fun b _ => ?_
    rw [← hcol b, sum_mul, sum_mul]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_pow, Real.sq_sqrt (hC a b)]
    ring
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun p : (Fin 3 → F) × (Fin 3 → F) =>
    √(C p.1 p.2) * f p.1) (fun p => √(C p.1 p.2) * g p.2)
  rw [e2, e3, ← e1] at hcs
  rw [← Real.sqrt_mul' _ (by rw [← e3]; exact sum_nonneg fun _ _ => sq_nonneg _)]
  exact Real.abs_le_sqrt hcs

section Terms

variable {m : (Fin 3 → F) → ℝ}

theorem frame_W {Γ : ℝ} {f : (Fin 3 → F) → ℝ} (hf : FrameAt m Γ f) :
    uip (Wa m f) (Wa m f) ≤ Γ * mip m f f := by
  unfold FrameAt at hf
  have : 0 ≤ qF * ∑ i, uip (Ba m i f) (Ba m i f) :=
    mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun i _ => uip_self_nonneg _)
  linarith

theorem frame_B {Γ : ℝ} {f : (Fin 3 → F) → ℝ} (hf : FrameAt m Γ f) (i : Fin 3) :
    uip (Ba m i f) (Ba m i f) ≤ Γ * mip m f f / qF := by
  have hq : (0 : ℝ) < qF := Nat.cast_pos.mpr Fintype.card_pos
  unfold FrameAt at hf
  have h1 : uip (Ba m i f) (Ba m i f) ≤ ∑ j, uip (Ba m j f) (Ba m j f) :=
    single_le_sum (fun j _ => uip_self_nonneg (Ba m j f)) (mem_univ i)
  have h2 := uip_self_nonneg (Wa m f)
  rw [le_div_iff₀ hq]
  nlinarith

/-- `|⟨A_i^* f, V₀^* g⟩| ≤ Γ r ‖f‖ ‖g‖`. -/
theorem ba_wa_le {Γ : ℝ} (hΓ : 0 ≤ Γ) (hm : ∀ x, 0 ≤ m x) {f g : (Fin 3 → F) → ℝ}
    (hf : FrameAt m Γ f) (hg : FrameAt m Γ g) (i : Fin 3) :
    |uip (Ba m i f) (Wa m g)| ≤ Γ * (√qF)⁻¹ * (√(mip m f f) * √(mip m g g)) := by
  have hq : (0 : ℝ) < qF := Nat.cast_pos.mpr Fintype.card_pos
  have h := abs_le_of_sq_le (uip_sq_le (Ba m i f) (Wa m g)) (uip_self_nonneg _)
    (uip_self_nonneg _) (frame_B hf i) (frame_W hg)
  have hff := mip_self_nonneg hm f
  have hgg := mip_self_nonneg hm g
  rw [Real.sqrt_div' _ hq.le, Real.sqrt_mul hΓ, Real.sqrt_mul hΓ] at h
  have e : √Γ * √(mip m f f) / √qF * (√Γ * √(mip m g g)) =
      (√Γ * √Γ) * (√qF)⁻¹ * (√(mip m f f) * √(mip m g g)) := by ring
  rw [e, Real.mul_self_sqrt hΓ] at h
  exact h

/-- `|⟨V₀^* f, A_i^* g⟩| ≤ Γ r ‖f‖ ‖g‖`. -/
theorem wa_ba_le {Γ : ℝ} (hΓ : 0 ≤ Γ) (hm : ∀ x, 0 ≤ m x) {f g : (Fin 3 → F) → ℝ}
    (hf : FrameAt m Γ f) (hg : FrameAt m Γ g) (i : Fin 3) :
    |uip (Wa m f) (Ba m i g)| ≤ Γ * (√qF)⁻¹ * (√(mip m f f) * √(mip m g g)) := by
  rw [uip_comm, mul_comm (√(mip m f f))]
  exact ba_wa_le hΓ hm hg hf i

theorem oForm_crude {Γ : ℝ} (hΓ : 0 ≤ Γ) (hm : ∀ x, 0 ≤ m x) {f g : (Fin 3 → F) → ℝ}
    (hf : FrameAt m Γ f) (hg : FrameAt m Γ g) :
    |oForm m f g| ≤ 2 * (Γ * (√qF)⁻¹ * (√(mip m f f) * √(mip m g g))) := by
  unfold oForm
  rw [abs_neg]
  have h1 := ba_wa_le hΓ hm hf hg 0
  have h2 := wa_ba_le hΓ hm hf hg 0
  calc _ ≤ |uip (Ba m 0 f) (Wa m g)| + |uip (Wa m f) (Ba m 0 g)| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem abs_aT_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin 3) : |aT t i| ≤ 1 := by
  fin_cases i <;> simp [aT, abs_le] <;> constructor <;> linarith

theorem lForm_crude {Γ : ℝ} (hΓ : 0 ≤ Γ) (hm : ∀ x, 0 ≤ m x) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) {f g : (Fin 3 → F) → ℝ} (hf : FrameAt m Γ f) (hg : FrameAt m Γ g) :
    |lForm m t f g| ≤ 6 * (Γ * (√qF)⁻¹ * (√(mip m f f) * √(mip m g g))) := by
  set K := Γ * (√qF)⁻¹ * (√(mip m f f) * √(mip m g g))
  have hterm : ∀ i, |aT t i * uip (Ba m i f) (Wa m g)| ≤ K := fun i => by
    rw [abs_mul]
    have h := ba_wa_le hΓ hm hf hg i
    have := abs_aT_le ht0 ht1 i
    have hK : 0 ≤ K := (abs_nonneg _).trans h
    calc _ ≤ 1 * K := mul_le_mul this h (abs_nonneg _) zero_le_one
      _ = K := one_mul K
  have hterm' : ∀ i, |aT t i * uip (Wa m f) (Ba m i g)| ≤ K := fun i => by
    rw [abs_mul]
    have h := wa_ba_le hΓ hm hf hg i
    have := abs_aT_le ht0 ht1 i
    have hK : 0 ≤ K := (abs_nonneg _).trans h
    calc _ ≤ 1 * K := mul_le_mul this h (abs_nonneg _) zero_le_one
      _ = K := one_mul K
  unfold lForm
  simp only [Fin.sum_univ_three]
  have a0 := abs_le.mp (hterm 0)
  have a1 := abs_le.mp (hterm 1)
  have a2 := abs_le.mp (hterm 2)
  have b0 := abs_le.mp (hterm' 0)
  have b1 := abs_le.mp (hterm' 1)
  have b2 := abs_le.mp (hterm' 2)
  rw [abs_le]
  constructor <;> linarith [a0.1, a0.2, a1.1, a1.2, a2.1, a2.2, b0.1, b0.2, b1.1, b1.2, b2.1, b2.2]

end Terms

/-! ## The frame constant is at most `2` -/

omit [DecidableEq F] in
theorem gammaW_le_two (h19 : (19 : ℝ) ≤ qF) : gammaW (F := F) ≤ 2 := by
  have h0 : (0 : ℝ) < qF := by linarith
  have h1 : (0 : ℝ) < qF - 1 := by linarith
  have h4 : (0 : ℝ) < qF - 4 := by linarith
  -- `√ρ₀₂² ≤ 1/3`
  have e02 : Real.sqrt (rho02sq (F := F)) ≤ 1 / 3 := by
    rw [Real.sqrt_le_left (by norm_num)]
    unfold rho02sq
    have hx : 1 / qF ≤ 1 / 19 := one_div_le_one_div_of_le (by norm_num) h19
    have hx0 : 0 < 1 / qF := by positivity
    have hd : 0 < (1 - 1 / qF) ^ 2 := by
      have : 0 < 1 - 1 / qF := by linarith
      positivity
    rw [div_le_iff₀ hd]
    nlinarith
  -- `√ρ₀₁² ≤ 1/10`
  have e01 : Real.sqrt (rho01sq (F := F)) ≤ 1 / 10 := by
    rw [Real.sqrt_le_left (by norm_num)]
    unfold rho01sq muF
    have hm : (2 / (qF - 4)) ^ 2 * qF ≤ 1 := by
      rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)]
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- `g₀₃ ≤ 1/8`
  have e03 : g03 (F := F) ≤ 1 / 8 := by
    unfold g03
    have hs : Real.sqrt qF ≤ qF := by
      rw [Real.sqrt_le_left h0.le]
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    have hq2 : 0 ≤ qF ^ 2 - 13 * qF - 28 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hs (by linarith : (0 : ℝ) ≤ qF + 4),
      mul_nonneg h0.le hq2]
  -- `g₁₃ ≤ 1/9`
  have e13 : g13 (F := F) ≤ 1 / 9 := by
    unfold g13
    have hm : muF (F := F) ^ 2 * qF ≤ 1 := by
      unfold muF
      rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)]
      nlinarith
    have hs1 : Real.sqrt (1 + muF (F := F) ^ 2 * qF) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      nlinarith [sq_nonneg (muF (F := F)), mul_nonneg (sq_nonneg (muF (F := F))) h0.le]
    have hs : Real.sqrt qF ≤ qF := by
      rw [Real.sqrt_le_left h0.le]
      nlinarith
    have hs0 := Real.sqrt_nonneg qF
    have hs10 := Real.sqrt_nonneg (1 + muF (F := F) ^ 2 * qF)
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hs1 hs hs0 (by norm_num : (0 : ℝ) ≤ 2)]
  unfold gammaW
  linarith

/-! ## The crude decompositions -/

section Crude

variable {m : (Fin 3 → F) → ℝ}

theorem oldDecomp_crude {C₀ : Matrix (Fin 3 → F) (Fin 3 → F) ℝ} {Γ : ℝ} (hΓ : 0 ≤ Γ)
    (hm : ∀ x, 0 ≤ m x) (hC : ∀ a b, 0 ≤ C₀ a b) (hrow : ∀ a, ∑ b, C₀ a b = m a)
    (hcol : ∀ b, ∑ a, C₀ a b = m b) (hframe : ∀ f, FrameAt m Γ f) :
    OldDecomp m C₀ (qF * (1 + 2 * Γ)) := by
  intro f g _ _
  have hq : (0 : ℝ) < qF := Nat.cast_pos.mpr Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ qF := by exact_mod_cast Fintype.card_pos
  have hr : (√qF)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (Real.sqrt_pos.mpr hq)]
    rw [Real.le_sqrt (by norm_num) hq.le]
    linarith
  set N := √(mip m f f) * √(mip m g g)
  have hN : 0 ≤ N := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h1 := coupling_dot_le hC hrow hcol f g
  have h2 := oForm_crude hΓ hm (hframe f) (hframe g)
  have e : qF * (1 + 2 * Γ) * qF⁻¹ * N = (1 + 2 * Γ) * N := by field_simp
  rw [e]
  have h3 : 2 * (Γ * (√qF)⁻¹ * N) ≤ 2 * Γ * N := by
    have := mul_le_mul_of_nonneg_left hr (mul_nonneg hΓ hN)
    nlinarith
  calc |f ⬝ᵥ (C₀ *ᵥ g) - oForm m f g| ≤ |f ⬝ᵥ (C₀ *ᵥ g)| + |oForm m f g| := abs_sub _ _
    _ ≤ (1 + 2 * Γ) * N := by linarith

theorem newDecomp_crude {P : Fin 3 → Matrix (Fin 3 → F) (Fin 3 → F) ℝ} {Γ : ℝ} (hΓ : 0 ≤ Γ)
    (hm : ∀ x, 0 ≤ m x) (hP : ∀ c a b, 0 ≤ P c a b) (hrow : ∀ c a, ∑ b, P c a b = m a)
    (hcol : ∀ c b, ∑ a, P c a b = m b) (hframe : ∀ f, FrameAt m Γ f) :
    NewDecomp m (∑ c, signedCoef tPaper c • P c) tPaper (qF * (2 + 8 * Γ)) := by
  intro f g _ _
  have hq : (0 : ℝ) < qF := Nat.cast_pos.mpr Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ qF := by exact_mod_cast Fintype.card_pos
  have hr : (√qF)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (Real.sqrt_pos.mpr hq)]
    rw [Real.le_sqrt (by norm_num) hq.le]
    linarith
  set N := √(mip m f f) * √(mip m g g)
  have hN : 0 ≤ N := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsplit : f ⬝ᵥ ((∑ c, signedCoef tPaper c • P c) *ᵥ g) =
      ∑ c, signedCoef tPaper c * (f ⬝ᵥ (P c *ᵥ g)) := by
    simp only [Fin.sum_univ_three, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
  have hP1 : |f ⬝ᵥ ((∑ c, signedCoef tPaper c • P c) *ᵥ g)| ≤ (1 + tPaper) * N := by
    rw [hsplit, ← sum_abs_signedCoef tPaper_nonneg, sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun c _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (coupling_dot_le (hP c) (hrow c) (hcol c) f g)
      (abs_nonneg _)
  have h2 := oForm_crude hΓ hm (hframe f) (hframe g)
  have h3 := lForm_crude hΓ hm tPaper_nonneg tPaper_le_one (hframe f) (hframe g)
  have e : qF * (2 + 8 * Γ) * qF⁻¹ * N = (2 + 8 * Γ) * N := by field_simp
  rw [e]
  have h4 : Γ * (√qF)⁻¹ * N ≤ Γ * N := by
    have := mul_le_mul_of_nonneg_left hr (mul_nonneg hΓ hN)
    nlinarith
  have ht := tPaper_le_one
  calc _ ≤ |f ⬝ᵥ ((∑ c, signedCoef tPaper c • P c) *ᵥ g)| + |oForm m f g + lForm m tPaper f g| :=
        abs_sub _ _
    _ ≤ (1 + tPaper) * N + (|oForm m f g| + |lForm m tPaper f g|) := by
        gcongr
        exact abs_add_le _ _
    _ ≤ (2 + 8 * Γ) * N := by nlinarith

end Crude

/-! ## The toy instance at a middle block -/

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

/-- **Non-vacuity**: at every middle block (primes `≡ 3 (mod 4)`, `≥ 19`), for **every** fold
components `C`, the prime decompositions and gates hold whenever the shift `r d / H_𝔅` is at
least `28` (`e_o = p(1 + 2Γ)`, `e_sg = p(2 + 8Γ)`, `c_+ = √p`, `ρ₀ = ρ₁ = 1`). -/
theorem decompGateAt_large (hne : MiddleNonempty pr) (C : FoldComponents pr hne)
    (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i) {r d : ℝ} (hσ : 28 ≤ r * d / Hblock pr) :
    DecompGateAt pr hne C r d := by
  have hcard : ∀ i, (Fintype.card (ZMod (pr i)) : ℝ) = (pr i : ℝ) := fun i => card_zmod i
  have h19' : ∀ i, (19 : ℝ) ≤ (pr i : ℝ) := fun i => by exact_mod_cast h19 i
  have hΓ0 : ∀ i, 0 ≤ gammaP pr i := gammaP_nonneg h19
  have hΓ2 : ∀ i, gammaP pr i ≤ 2 := fun i => by
    apply gammaW_le_two
    rw [hcard]; exact h19' i
  have hrpos : ∀ i, 0 < rP pr i := fun i =>
    inv_pos.mpr (Real.sqrt_pos.mpr (by linarith [h19' i]))
  have hrr : ∀ i, (pr i : ℝ) * (rP pr i * rP pr i) = 1 := fun i => by
    rw [rP, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    exact mul_inv_cancel₀ (by linarith [h19' i])
  have hr1 : ∀ i, rP pr i ≤ 1 := fun i => by
    rw [rP, inv_le_one₀ (Real.sqrt_pos.mpr (by linarith [h19' i])),
      Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]
    linarith [h19' i]
  refine ⟨fun i => (pr i : ℝ) * (1 + 2 * gammaP pr i),
    fun i => (pr i : ℝ) * (2 + 8 * gammaP pr i), fun i => √(pr i : ℝ), ?_, ?_⟩
  · refine ⟨fun i => ?_, fun i => ?_, fun c i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
    · have := oldDecomp_crude (hΓ0 i) (mP_nonneg hne i) (fun a b => (K0 (hne.F2 i)).nonneg _)
        ((oldP_coupling hne).row i) ((oldP_coupling hne).col i) (frame_block hne h3 h19 i)
      rw [hcard] at this
      exact this
    · have := newDecomp_crude (P := fun c => compP hne C c i) (hΓ0 i) (mP_nonneg hne i)
        (fun c a b => ((C i).law 0 c).nonneg _) (fun c => (compP_coupling hne C c).row i)
        (fun c => (compP_coupling hne C c).col i) (frame_block hne h3 h19 i)
      rw [hcard] at this
      exact this
    · have h1 := centredNorm_one (fun a b => ((C i).law 0 c).nonneg _) (mP_nonneg hne i)
        ((compP_coupling hne C c).row i) ((compP_coupling hne C c).col i)
      have e : √(pr i : ℝ) * rP pr i = 1 := by
        rw [rP]
        exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (by linarith [h19' i])).ne'
      rw [e]
      exact h1
    · have := hΓ0 i
      have : (0 : ℝ) ≤ pr i := Nat.cast_nonneg _
      positivity
    · have := hΓ0 i
      have : (0 : ℝ) ≤ pr i := Nat.cast_nonneg _
      positivity
    · exact Real.sqrt_nonneg _
  · have hsT : sT tPaper ≤ 12 / 5 := by
      have := (sT_bounds).2
      unfold tPaper
      linarith
    have hsT0 : 0 ≤ sT tPaper := Real.sqrt_nonneg _
    refine ⟨fun i => ?_, 1, 1, zero_le_one, le_rfl, zero_le_one, le_rfl, fun i => min_le_left _ _,
      fun i => min_le_left _ _, ?_⟩
    · have e : (sT tPaper * gammaP pr i + ((pr i : ℝ) * (1 + 2 * gammaP pr i) +
          (pr i : ℝ) * (2 + 8 * gammaP pr i)) * rP pr i) * rP pr i =
          sT tPaper * gammaP pr i * rP pr i +
            (3 + 10 * gammaP pr i) * ((pr i : ℝ) * (rP pr i * rP pr i)) := by ring
      rw [e, hrr]
      have h1 : sT tPaper * gammaP pr i * rP pr i ≤ 12 / 5 * 2 * 1 := by
        apply mul_le_mul (mul_le_mul hsT (hΓ2 i) (hΓ0 i) (by norm_num)) (hr1 i)
          (hrpos i).le (by norm_num)
      linarith [hΓ2 i]
    · have := tPaper_le_one
      linarith

end Block

end Sarkozy.PrimeGram
