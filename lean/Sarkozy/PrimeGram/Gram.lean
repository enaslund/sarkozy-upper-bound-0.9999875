module

public import Sarkozy.PrimeGram.Frame
public import Sarkozy.Envelopes.DirectGram
public import Sarkozy.SignedGram.SectorNorm

@[expose] public section

/-!
# The prime Gram and the prime centred norm from the prime decompositions (PG)

`paper/sections/24_matching_mean.tex`, proof of `prop:signed-sides`(i) ("The prime Gram",
"Supports of at least two primes"), `lem:record:direct-gram`;
`paper/sections/21_middle_records.tex`, `lem:old-f-law`(f), `prop:signed-bounds`(c).

At one prime, for any weights `m ≥ 0` on the half triples (later: the actual half marginal `m₀`),
with the features of `Features.lean`, `W = V₀^{*m}`, `B_i = A_i^{*m}`:

* **The leading operators** (`lem:old-f-law`(f), `prop:signed-bounds`(c)):
  `O₀ = -(A₁V₀^{*m} + V₀A₁^{*m})` (`O0`) and `L^m_t = A_{a_t}V₀^{*m} - V₀A_{a_t}^{*m}` (`Lm`),
  `a_t = (t, 1, 1 - t)`, `A_ξ = ∑ ξ_i A_i` with the unprojected `A₃`; their forms
  `oForm f g = ⟨f, O₀ g⟩_m` (`mip_O0`) and `lForm t f g = ⟨f, L^m_t g⟩_m` (`mip_Lm`).
* **`gram_lower`** (`lem:record:direct-gram` at `τ = 1`): under the frame bound `FrameAt m Γ` (the
  adjoint form of `‖(V₀, A₁/r, A₂/r, A₃/r)‖² ≤ Γ`, proved at `m₀` in `frame_analysis`),
  `G(u_t, v_t)(f, g) ≥ -r Γ s_t (‖f‖² + ‖g‖²)`, `r = p^{-1/2}`, through Envelopes'
  `pairing_lower`.
* **The decompositions, as hypotheses** (named, with their paper labels):
  - `OldDecomp m C₀ e_o`: `T_old = O₀ + R_o` on the centred functions, `‖R_o‖ ≤ e_o q`
    (`lem:old-f-law`(f));
  - `NewDecomp m N t e_sg`: `Π_⊥ T' Π_⊥ = O₀ + L^m_t + R^new`, `‖R^new‖ ≤ e_sg q`
    (`prop:signed-bounds`(c)).
* **`primeGramC_of_decomp`** (`prop:signed-sides`(i), "On the centred functions"): the prime
  Gram on the centred functions holds at every shift `σ ≥ (s_t Γ + (e_o + e_sg) r) r = d_t r`.
* **`centredNorm_of_decomp`** (`lem:old-f-law`(f), last sentence): the centred norm of `T_old` is
  at most `Γ r + e_o q = (Γ + e_o r) r`, with `‖O₀‖ ≤ Γ r` (`oForm_bound`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.PrimeGram

open Sarkozy.TraceMixing Sarkozy.MiddleRecords Sarkozy.Envelopes Sarkozy.SignedGram

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "qF" => (Fintype.card F : ℝ)

/-! ## The concrete pairing bound -/

omit [Field F] [DecidableEq F] in
theorem uip_add_smul (α β : ℝ) (x x' c : F → ℝ) :
    uip (fun a => α * x a + β * x' a) c = α * uip x c + β * uip x' c := by
  unfold uip
  simp only [add_mul, sum_add_distrib, mul_add, mul_sum]
  congr 1 <;> exact sum_congr rfl fun a _ => by ring

omit [Field F] [DecidableEq F] in
/-- **The pairing bound on `H₀`** (Envelopes' `pairing_lower` on `EuclideanSpace ℝ 𝔽_p`, with the
uniform inner product of `H₀`). -/
theorem pairing_fun {ι : Type*} [Fintype ι] (α β : ι → ℝ) (x x' : F → ℝ) (c : ι → F → ℝ) :
    -(√(lamMax (∑ j, α j ^ 2) (∑ j, β j ^ 2) (∑ j, α j * β j)) *
        (uip x x + uip x' x' + ∑ j, uip (c j) (c j))) ≤
      2 * ∑ j, uip (fun a => α j * x a + β j * x' a) (c j) := by
  have key := pairing_lower (E := EuclideanSpace ℝ F) α β (WithLp.toLp 2 x) (WithLp.toLp 2 x')
    (fun j => WithLp.toLp 2 (c j))
  have hn : ∀ h : F → ℝ, ‖WithLp.toLp 2 h‖ ^ 2 = ∑ a, h a * h a := by
    intro h
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct]
  have hi : ∀ j, inner ℝ (α j • WithLp.toLp 2 x + β j • WithLp.toLp 2 x')
      (WithLp.toLp 2 (c j)) = ∑ a, (α j * x a + β j * x' a) * c j a := by
    intro j
    rw [← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add,
      EuclideanSpace.inner_toLp_toLp]
    simp only [dotProduct, star_trivial, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_congr rfl fun a _ => by ring
  simp only [hn, hi] at key
  unfold uip
  have hq : 0 ≤ qF⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have := mul_le_mul_of_nonneg_left key hq
  rw [← mul_sum, ← mul_sum]
  nlinarith [this]

/-! ## The leading operators -/

section Leading

variable (m : (Fin 3 → F) → ℝ)

/-- `W f = V₀^{*m} f`. -/
noncomputable def Wa (f : (Fin 3 → F) → ℝ) : F → ℝ := adj m V0 f

/-- `B_i f = A_i^{*m} f` (`B 0 = A₁^*`, `B 1 = A₂^*`, `B 2 = A₃^*`). -/
noncomputable def Ba (i : Fin 3) (f : (Fin 3 → F) → ℝ) : F → ℝ := adj m (arm i) f

/-- **`O₀ = -(A₁V₀^{*m} + V₀A₁^{*m})`** (`lem:old-f-law`(f)), as an operator on functions of the
half. -/
noncomputable def O0 (g : (Fin 3 → F) → ℝ) : (Fin 3 → F) → ℝ :=
  fun x => -(A1 (Wa m g) x + V0 (Ba m 0 g) x)

/-- **`L^m_t = A_{a_t}V₀^{*m} - V₀A_{a_t}^{*m}`** (`prop:signed-bounds`(c)), with
`a_t = (t, 1, 1 - t)` and the unprojected `A₃`. -/
noncomputable def Lm (t : ℝ) (g : (Fin 3 → F) → ℝ) : (Fin 3 → F) → ℝ :=
  fun x => ∑ i, aT t i * arm i (Wa m g) x - V0 (fun a => ∑ i, aT t i * Ba m i g a) x

/-- The form `⟨f, O₀ g⟩_m = -(⟨A₁^* f, V₀^* g⟩ + ⟨V₀^* f, A₁^* g⟩)`. -/
noncomputable def oForm (f g : (Fin 3 → F) → ℝ) : ℝ :=
  -(uip (Ba m 0 f) (Wa m g) + uip (Wa m f) (Ba m 0 g))

/-- The form `⟨f, L^m_t g⟩_m = ∑_i a_i ⟨A_i^* f, V₀^* g⟩ - ∑_i a_i ⟨V₀^* f, A_i^* g⟩`. -/
noncomputable def lForm (t : ℝ) (f g : (Fin 3 → F) → ℝ) : ℝ :=
  ∑ i, aT t i * uip (Ba m i f) (Wa m g) - ∑ i, aT t i * uip (Wa m f) (Ba m i g)

/-- **The frame bound at `f`** (adjoint form of `‖(V₀, A₁/r, A₂/r, A₃/r)‖² ≤ Γ`, `1/r² = p`). -/
def FrameAt (Γ : ℝ) (f : (Fin 3 → F) → ℝ) : Prop :=
  uip (Wa m f) (Wa m f) + qF * ∑ i, uip (Ba m i f) (Ba m i f) ≤ Γ * mip m f f

omit [Field F] [DecidableEq F] in
theorem mip_comm (f g : (Fin 3 → F) → ℝ) : mip m f g = mip m g f := by
  unfold mip
  exact sum_congr rfl fun x _ => by ring

omit [Field F] [DecidableEq F] in
theorem mip_add_right (f g g' : (Fin 3 → F) → ℝ) :
    mip m f (fun x => g x + g' x) = mip m f g + mip m f g' := by
  unfold mip
  rw [← sum_add_distrib]
  exact sum_congr rfl fun x _ => by ring

omit [Field F] [DecidableEq F] in
theorem mip_neg_right (f g : (Fin 3 → F) → ℝ) :
    mip m f (fun x => -g x) = -mip m f g := by
  unfold mip
  rw [← sum_neg_distrib]
  exact sum_congr rfl fun x _ => by ring

omit [Field F] [DecidableEq F] in
theorem mip_sum_right (c : Fin 3 → ℝ) (f : (Fin 3 → F) → ℝ) (g : Fin 3 → (Fin 3 → F) → ℝ) :
    mip m f (fun x => ∑ i, c i * g i x) = ∑ i, c i * mip m f (g i) := by
  unfold mip
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun x _ => by ring

theorem sum_Wa (f : (Fin 3 → F) → ℝ) : ∑ a, Wa m f a = 0 := sum_cen _

theorem sum_Ba (i : Fin 3) (f : (Fin 3 → F) → ℝ) : ∑ a, Ba m i f a = 0 := sum_cen _

/-- **`⟨f, O₀ g⟩_m = oForm f g`**: the form of the operator `O₀` is the adjoint expression. -/
theorem mip_O0 (f g : (Fin 3 → F) → ℝ) : mip m f (O0 m g) = oForm m f g := by
  unfold O0 oForm
  rw [mip_neg_right, mip_add_right, mip_comm m f (A1 _), mip_comm m f (V0 _),
    adj_spec m A1_kernel (sum_Wa m g), adj_spec m V0_kernel (sum_Ba m 0 g)]
  rw [uip_comm (Wa m g), uip_comm (Ba m 0 g)]
  rfl

/-- **`⟨f, L^m_t g⟩_m = lForm t f g`**. -/
theorem mip_Lm (t : ℝ) (f g : (Fin 3 → F) → ℝ) : mip m f (Lm m t g) = lForm m t f g := by
  unfold Lm lForm
  have e : (fun x => ∑ i, aT t i * arm i (Wa m g) x - V0 (fun a => ∑ i, aT t i * Ba m i g a) x) =
      fun x => (fun x => ∑ i, aT t i * arm i (Wa m g) x) x +
        (fun x => -V0 (fun a => ∑ i, aT t i * Ba m i g a) x) x := by
    funext x
    ring
  rw [e, mip_add_right, mip_neg_right, mip_sum_right]
  have hs : ∑ a, (∑ i, aT t i * Ba m i g a) = 0 := by
    rw [sum_comm]
    exact sum_eq_zero fun i _ => by rw [← mul_sum, sum_Ba, mul_zero]
  rw [mip_comm m f (V0 _), adj_spec m V0_kernel hs]
  have h1 : ∀ i, mip m f (arm i (Wa m g)) = uip (Ba m i f) (Wa m g) := by
    intro i
    rw [mip_comm, adj_spec m (arm_kernel i) (sum_Wa m g), uip_comm]
    rfl
  simp only [h1]
  have h2 : uip (fun a => ∑ i, aT t i * Ba m i g a) (Wa m f) =
      ∑ i, aT t i * uip (Wa m f) (Ba m i g) := by
    unfold uip
    simp only [sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun a _ => by ring
  rw [show adj m V0 f = Wa m f from rfl, h2]
  ring

end Leading

/-! ## The leading Gram -/

section Gram

variable {m : (Fin 3 → F) → ℝ}

/-- **`lem:record:direct-gram` at the signed point, `τ = 1`, at the actual features**: under the
frame bound at `f` and `g`,
`⟨f, O₀ f⟩ + 2 ⟨f, (O₀ + L^m_t) g⟩ + ⟨g, O₀ g⟩ ≥ -r Γ s_t (‖f‖² + ‖g‖²)`, `r = p^{-1/2}`.
The left side is the form of `G(u_t, v_t)`, since `O₀ + L^m_t = L_{u_t, v_t}`. -/
theorem gram_lower {Γ : ℝ} (t : ℝ) {f g : (Fin 3 → F) → ℝ} (hf : FrameAt m Γ f)
    (hg : FrameAt m Γ g) :
    -((√qF)⁻¹ * Γ * sT t * (mip m f f + mip m g g)) ≤
      oForm m f f + 2 * (oForm m f g + lForm m t f g) + oForm m g g := by
  have hq : (0 : ℝ) < qF := Nat.cast_pos.mpr Fintype.card_pos
  set s := √qF with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr hq
  have hs2 : s * s = qF := Real.mul_self_sqrt hq.le
  set c : Fin 3 ⊕ Fin 3 → F → ℝ := fun j => match j with
    | Sum.inl i => fun a => s * Ba m i f a
    | Sum.inr i => fun a => s * Ba m i g a with hc
  have key := pairing_fun (upsCol1 1 (vT t)) (upsCol2 1 (uT t)) (Wa m f) (Wa m g) c
  rw [gram11, gram22, gram12] at key
  change -(sSide 1 (uT t) (vT t) * _) ≤ _ at key
  rw [sSide_signed] at key
  -- the norms
  have hn : uip (Wa m f) (Wa m f) + uip (Wa m g) (Wa m g) + ∑ j, uip (c j) (c j) =
      (uip (Wa m f) (Wa m f) + qF * ∑ i, uip (Ba m i f) (Ba m i f)) +
        (uip (Wa m g) (Wa m g) + qF * ∑ i, uip (Ba m i g) (Ba m i g)) := by
    simp only [c, Fintype.sum_sum_type, uip_smul_left, uip_smul_right, mul_sum]
    rw [← hs2]
    simp only [mul_assoc]
    ring
  -- the pairing
  have hp : 2 * ∑ j, uip (fun a => upsCol1 1 (vT t) j * Wa m f a + upsCol2 1 (uT t) j * Wa m g a)
      (c j) = s * (oForm m f f + 2 * (oForm m f g + lForm m t f g) + oForm m g g) := by
    simp only [c, Fintype.sum_sum_type, uip_add_smul, uip_smul_right, Fin.sum_univ_three,
      upsCol1, upsCol2, eVec, uT, vT, aT, oForm, lForm]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, div_one, one_mul]
    rw [uip_comm (Wa m f) (Ba m 0 f), uip_comm (Wa m g) (Ba m 0 g),
      uip_comm (Wa m g) (Ba m 0 f), uip_comm (Wa m g) (Ba m 1 f),
      uip_comm (Wa m g) (Ba m 2 f)]
    ring
  rw [hn, hp] at key
  have hframe : (uip (Wa m f) (Wa m f) + qF * ∑ i, uip (Ba m i f) (Ba m i f)) +
      (uip (Wa m g) (Wa m g) + qF * ∑ i, uip (Ba m i g) (Ba m i g)) ≤
      Γ * (mip m f f + mip m g g) := by
    unfold FrameAt at hf hg
    linarith
  have hsT : 0 ≤ sT t := Real.sqrt_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hframe hsT
  -- divide by `s`
  have h2 : -(sT t * (Γ * (mip m f f + mip m g g))) ≤
      s * (oForm m f f + 2 * (oForm m f g + lForm m t f g) + oForm m g g) := by linarith
  have h3 : -((s)⁻¹ * Γ * sT t * (mip m f f + mip m g g)) =
      s⁻¹ * (-(sT t * (Γ * (mip m f f + mip m g g)))) := by ring
  rw [h3]
  have h4 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hs.le)
  rw [inv_mul_cancel_left₀ hs.ne'] at h4
  exact h4

end Gram

/-! ## The decompositions and their consequences -/

section Decomp

variable (m : (Fin 3 → F) → ℝ)

/-- **`lem:old-f-law`(f), on the centred functions** (hypothesis): the centred reference
`O = T_old - J` is `O₀ + R_o` with `‖R_o‖ ≤ e_o q`, i.e. for `m`-mean-zero `f, g`,
`|⟨f, T_old g⟩_m - ⟨f, O₀ g⟩_m| ≤ e_o q ‖f‖_m ‖g‖_m`, `q = 1/p`. The coupling matrix `C₀` gives
`⟨f, T_old g⟩_m = f ⬝ (C₀ g)`. -/
def OldDecomp (C₀ : Matrix (Fin 3 → F) (Fin 3 → F) ℝ) (eo : ℝ) : Prop :=
  ∀ f g : (Fin 3 → F) → ℝ, m ⬝ᵥ f = 0 → m ⬝ᵥ g = 0 →
    |f ⬝ᵥ (C₀ *ᵥ g) - oForm m f g| ≤ eo * qF⁻¹ * (√(mip m f f) * √(mip m g g))

/-- **`prop:signed-bounds`(c), the centred signed record** (hypothesis):
`Π_⊥ T'_p Π_⊥ = O₀ + L^m_t + R^new` with `‖R^new‖ ≤ e_sg q`, i.e. for `m`-mean-zero `f, g`,
`|⟨f, T' g⟩_m - ⟨f, (O₀ + L^m_t) g⟩_m| ≤ e_sg q ‖f‖_m ‖g‖_m`, `T'` given by the coupling matrix
`N = ∑_c α_c P_c`. -/
def NewDecomp (N : Matrix (Fin 3 → F) (Fin 3 → F) ℝ) (t esg : ℝ) : Prop :=
  ∀ f g : (Fin 3 → F) → ℝ, m ⬝ᵥ f = 0 → m ⬝ᵥ g = 0 →
    |f ⬝ᵥ (N *ᵥ g) - (oForm m f g + lForm m t f g)| ≤ esg * qF⁻¹ * (√(mip m f f) * √(mip m g g))

omit [Field F] in
theorem dot_diag (f : (Fin 3 → F) → ℝ) : f ⬝ᵥ (diagonal m *ᵥ f) = mip m f f := by
  unfold mip
  simp only [dotProduct, mulVec_diagonal]
  exact sum_congr rfl fun x _ => by ring

variable {m}

/-- **`prop:signed-sides`(i), the prime Gram on the centred functions**: with the frame bound
(`frame_analysis` at `m₀`), `lem:old-f-law`(f) and `prop:signed-bounds`(c) (hypotheses
`OldDecomp`, `NewDecomp`), the prime Gram
`⟨f, T_old f⟩ + σ‖f‖² + 2⟨f, T' g⟩ + ⟨g, T_old g⟩ + σ‖g‖² ≥ 0` holds at centred `f, g` for every
`σ ≥ (s_t Γ + (e_o + e_sg) r) r` (`= d_t r`, `r = p^{-1/2}`). -/
theorem primeGramC_of_decomp {C₀ N : Matrix (Fin 3 → F) (Fin 3 → F) ℝ} {Γ eo esg t σ : ℝ}
    (hm : ∀ x, 0 ≤ m x) (hes : 0 ≤ esg) (hframe : ∀ f, FrameAt m Γ f)
    (hold : OldDecomp m C₀ eo) (hnew : NewDecomp m N t esg)
    (hσ : (sT t * Γ + (eo + esg) * (√qF)⁻¹) * (√qF)⁻¹ ≤ σ)
    (f g : (Fin 3 → F) → ℝ) (hf : m ⬝ᵥ f = 0) (hg : m ⬝ᵥ g = 0) :
    0 ≤ f ⬝ᵥ (C₀ *ᵥ f) + σ * (f ⬝ᵥ (diagonal m *ᵥ f)) + 2 * (f ⬝ᵥ (N *ᵥ g)) +
      g ⬝ᵥ (C₀ *ᵥ g) + σ * (g ⬝ᵥ (diagonal m *ᵥ g)) := by
  rw [dot_diag, dot_diag]
  have hq : (0 : ℝ) < qF := Nat.cast_pos.mpr Fintype.card_pos
  have hr2 : (√qF)⁻¹ * (√qF)⁻¹ = qF⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hq.le]
  set a := mip m f f
  set b := mip m g g
  have ha : 0 ≤ a := mip_self_nonneg hm f
  have hb : 0 ≤ b := mip_self_nonneg hm g
  have hA : √a * √a = a := Real.mul_self_sqrt ha
  have hB : √b * √b = b := Real.mul_self_sqrt hb
  have h1 := neg_abs_le (f ⬝ᵥ (C₀ *ᵥ f) - oForm m f f)
  have h1' := hold f f hf hf
  have h2 := neg_abs_le (g ⬝ᵥ (C₀ *ᵥ g) - oForm m g g)
  have h2' := hold g g hg hg
  have h3 := neg_abs_le (f ⬝ᵥ (N *ᵥ g) - (oForm m f g + lForm m t f g))
  have h3' := hnew f g hf hg
  rw [hA] at h1'
  rw [hB] at h2'
  have hG := gram_lower t (hframe f) (hframe g)
  have hqi : 0 ≤ qF⁻¹ := inv_nonneg.mpr hq.le
  have hab : 2 * (√a * √b) ≤ a + b := by
    nlinarith [sq_nonneg (√a - √b), hA, hB]
  have h4 : 2 * (esg * qF⁻¹ * (√a * √b)) ≤ esg * qF⁻¹ * (a + b) := by
    have := mul_le_mul_of_nonneg_left hab (mul_nonneg hes hqi)
    linarith
  have hσ' : (√qF)⁻¹ * Γ * sT t + (eo + esg) * qF⁻¹ ≤ σ := by
    rw [← hr2]
    nlinarith [hσ]
  have hab0 : 0 ≤ a + b := add_nonneg ha hb
  have h5 := mul_le_mul_of_nonneg_right hσ' hab0
  nlinarith

/-- **`‖O₀‖ ≤ Γ r`** (`lem:old-f-law`(f): `‖O₀‖ ≤ Γ_A r`), from the frame bound:
`|⟨f, O₀ g⟩_m| ≤ Γ r ‖f‖_m ‖g‖_m`. -/
theorem oForm_bound {Γ : ℝ} (hm : ∀ x, 0 ≤ m x) (hΓ : 0 ≤ Γ) {f g : (Fin 3 → F) → ℝ}
    (hf : FrameAt m Γ f) (hg : FrameAt m Γ g) :
    |oForm m f g| ≤ Γ * (√qF)⁻¹ * (√(mip m f f) * √(mip m g g)) := by
  have hq : (0 : ℝ) < qF := Nat.cast_pos.mpr Fintype.card_pos
  set s := √qF
  have hs : 0 < s := Real.sqrt_pos.mpr hq
  have hs2 : s * s = qF := Real.mul_self_sqrt hq.le
  -- the four norms
  set w₁ := uip (Wa m f) (Wa m f)
  set w₂ := uip (Wa m g) (Wa m g)
  set a₁ := uip (Ba m 0 f) (Ba m 0 f)
  set a₂ := uip (Ba m 0 g) (Ba m 0 g)
  have hw₁ : 0 ≤ w₁ := uip_self_nonneg _
  have hw₂ : 0 ≤ w₂ := uip_self_nonneg _
  have ha₁ : 0 ≤ a₁ := uip_self_nonneg _
  have ha₂ : 0 ≤ a₂ := uip_self_nonneg _
  -- Cauchy–Schwarz in `H₀`
  have cs : ∀ h k : F → ℝ, uip h k ^ 2 ≤ uip h h * uip k k := by
    intro h k
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
  have hF1 : w₁ + qF * a₁ ≤ Γ * mip m f f := by
    have := hf
    unfold FrameAt at this
    simp only [Fin.sum_univ_three] at this
    have := uip_self_nonneg (Ba m 1 f)
    have := uip_self_nonneg (Ba m 2 f)
    nlinarith
  have hF2 : w₂ + qF * a₂ ≤ Γ * mip m g g := by
    have := hg
    unfold FrameAt at this
    simp only [Fin.sum_univ_three] at this
    have := uip_self_nonneg (Ba m 1 g)
    have := uip_self_nonneg (Ba m 2 g)
    nlinarith
  -- squared bound: `oForm² ≤ (a₁ w₂ + ...)`, via `(xy + zw)² ≤ (x² + z²)(y² + w²)`
  set X := uip (Ba m 0 f) (Wa m g)
  set Y := uip (Wa m f) (Ba m 0 g)
  have hX := cs (Ba m 0 f) (Wa m g)
  have hY := cs (Wa m f) (Ba m 0 g)
  -- `(X + Y)² qF ≤ (qF a₁ + w₁)(w₂ + qF a₂)`
  have hXY : (X + Y) ^ 2 * qF ≤ (qF * a₁ + w₁) * (w₂ + qF * a₂) := by
    -- `X² ≤ a₁ w₂`, `Y² ≤ w₁ a₂`, `2XY ≤ 2√(a₁w₂w₁a₂)`; Lagrange
    have hXY2 : (X * Y) ^ 2 ≤ (a₁ * w₂) * (w₁ * a₂) := by
      rw [mul_pow]
      exact mul_le_mul hX hY (sq_nonneg _) (mul_nonneg ha₁ hw₂)
    have hxy : 2 * qF * (X * Y) ≤ qF ^ 2 * (a₁ * a₂) + w₁ * w₂ := by
      have hprod : (qF * (X * Y)) ^ 2 ≤ (qF ^ 2 * (a₁ * a₂)) * (w₁ * w₂) := by
        have := mul_le_mul_of_nonneg_left hXY2 (sq_nonneg qF)
        nlinarith [this]
      nlinarith [sq_nonneg (qF ^ 2 * (a₁ * a₂) - w₁ * w₂), mul_nonneg (mul_nonneg ha₁ ha₂)
        (sq_nonneg qF), mul_nonneg hw₁ hw₂, sq_nonneg (qF * (X * Y))]
    nlinarith [mul_le_mul_of_nonneg_left hX hq.le, mul_le_mul_of_nonneg_left hY hq.le]
  have hR : (qF * a₁ + w₁) * (w₂ + qF * a₂) ≤ (Γ * mip m f f) * (Γ * mip m g g) := by
    have h0 : 0 ≤ qF * a₁ + w₁ := by positivity
    have h0' : 0 ≤ w₂ + qF * a₂ := by positivity
    exact mul_le_mul (by linarith) (by linarith) h0' (le_trans h0 (by linarith))
  -- conclude
  have hff := mip_self_nonneg hm f
  have hgg := mip_self_nonneg hm g
  have hsq : (oForm m f g) ^ 2 ≤ (Γ * s⁻¹ * (√(mip m f f) * √(mip m g g))) ^ 2 := by
    have e1 : (oForm m f g) ^ 2 = (X + Y) ^ 2 := by unfold oForm; ring
    have e2 : (Γ * s⁻¹ * (√(mip m f f) * √(mip m g g))) ^ 2 =
        (Γ * mip m f f) * (Γ * mip m g g) / qF := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hff, Real.sq_sqrt hgg, inv_pow, ← hs2]
      field_simp
    rw [e1, e2, le_div_iff₀ hq]
    linarith
  have hnn : 0 ≤ Γ * s⁻¹ * (√(mip m f f) * √(mip m g g)) := by positivity
  exact abs_le_of_sq_le_sq' hsq hnn |> fun h => abs_le.mpr h

/-- **The centred norm of the reference** (`lem:old-f-law`(f), last sentence): with the frame bound
and `OldDecomp m C₀ e_o`, the Markov operator of the coupling `C₀` (marginals `m`) has centred norm
at most `Γ r + e_o q = (Γ + e_o r) r` (`CentredNorm` of SGA). -/
theorem centredNorm_of_decomp {C₀ : Matrix (Fin 3 → F) (Fin 3 → F) ℝ} {Γ eo : ℝ}
    (hm : ∀ x, 0 ≤ m x) (hΓ : 0 ≤ Γ) (hC : ∀ a b, 0 ≤ C₀ a b) (hrow : ∀ a, ∑ b, C₀ a b = m a)
    (hcol : ∀ b, ∑ a, C₀ a b = m b) (hframe : ∀ f, FrameAt m Γ f) (hold : OldDecomp m C₀ eo) :
    CentredNorm m C₀ (Γ * (√qF)⁻¹ + eo * qF⁻¹) := by
  intro f hf
  set T := condM C₀ m *ᵥ f with hT_def
  have hT : ∀ b, m b * T b = ∑ a, C₀ b a * f a := by
    intro b
    simp only [T, mulVec, dotProduct, mul_sum]
    exact sum_congr rfl fun a _ => by rw [← mul_assoc, mul_condM hC hrow]
  have hTc : m ⬝ᵥ T = 0 := by
    simp only [dotProduct, hT]
    rw [sum_comm]
    simp only [← sum_mul, hcol]
    exact hf
  have hfc : m ⬝ᵥ f = 0 := hf
  have hTT : mip m T T = T ⬝ᵥ (C₀ *ᵥ f) := by
    unfold mip
    simp only [dotProduct, mulVec]
    exact sum_congr rfl fun b _ => by rw [mul_comm (m b), mul_assoc, hT]
  have h1 := hold T f hTc hfc
  have h2 := oForm_bound hm hΓ (hframe T) (hframe f)
  set X := √(mip m T T)
  set Y := √(mip m f f)
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  have hXX : X * X = mip m T T := Real.mul_self_sqrt (mip_self_nonneg hm T)
  have hYY : Y * Y = mip m f f := Real.mul_self_sqrt (mip_self_nonneg hm f)
  set δ := Γ * (√qF)⁻¹ + eo * qF⁻¹
  have hle : X * X ≤ δ * (X * Y) := by
    rw [hXX, hTT]
    have := abs_le.mp h1
    have := abs_le.mp h2
    have e : δ * (X * Y) = Γ * (√qF)⁻¹ * (X * Y) + eo * qF⁻¹ * (X * Y) := by
      simp only [δ]; ring
    rw [e]
    linarith
  have hgoal : X * X ≤ (δ * Y) * (δ * Y) := by
    rcases hX.lt_or_eq with hpos | hzero
    · have hXd : X ≤ δ * Y := by nlinarith
      exact mul_self_le_mul_self hX hXd
    · rw [← hzero, mul_zero]
      exact mul_self_nonneg _
  have e1 : ∑ b, m b * T b ^ 2 = X * X := by
    rw [hXX]; unfold mip; exact sum_congr rfl fun b _ => by ring
  have e2 : δ ^ 2 * ∑ a, m a * f a ^ 2 = (δ * Y) * (δ * Y) := by
    have : ∑ a, m a * f a ^ 2 = Y * Y := by
      rw [hYY]; unfold mip; exact sum_congr rfl fun a _ => by ring
    rw [this]; ring
  change ∑ b, m b * T b ^ 2 ≤ δ ^ 2 * ∑ a, m a * f a ^ 2
  rw [e1, e2]
  exact hgoal

end Decomp

end Sarkozy.PrimeGram
