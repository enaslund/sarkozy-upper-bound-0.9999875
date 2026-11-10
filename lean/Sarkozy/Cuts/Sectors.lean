module

public import Sarkozy.Cuts.Envelope

/-!
# Cuts, VII′: translation sectors (`prop:matching:positive` (a″))

`13_cuts_correlations.tex`, `prop:matching:positive` (a″). Let a finite group `Γ` act on `Ω`,
preserving `ν`, and let the self-adjoint `A` commute with `U_γ f = f ∘ γ⁻¹`. In form language,
`𝔞(U_γ f, U_γ h) = 𝔞(f, h)`. `𝓘` is the space of invariant functions and `P` the averaging
projection onto `𝓘` (`avg`).

* `avg_invariant`, `avg_of_invariant`, `ip_avg`, `form_avg`: `P` is the orthogonal projection
  onto `𝓘`, and `A` commutes with it. So `A` preserves `𝓘` and `𝓘^⊥` (`form_cross_vanish`).
* `envelope_upper_on`, `envelope_lower_on`: parts (a) and (a′) on a subspace containing `1`
  and closed under centring.
* `sectors_bound`: if `|⟨f, Af⟩| ≤ C‖f‖²` on `𝓘^⊥`, `|⟨f, Af⟩| ≤ H‖f‖²` on `𝓘 ∩ 1^⊥` with
  `0 ≤ H < 1`, and `|⟨f, A1⟩| ≤ e‖f‖` on `𝓘 ∩ 1^⊥` (so `‖P₀A1‖² ≤ e² = ϑ_u`), then
  `-max(C, H + e²) ⪯ A ⪯ max(C, 1 + e²/(1 - H))`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering

variable {Ω : Type*} [Fintype Ω]

/-! ### (a), (a′) on a subspace -/

/-- **`prop:matching:positive` (a) on a subspace `S ∋ 1` closed under centring.** -/
theorem envelope_upper_on (ν : FiniteLaw Ω) (𝔞 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hsym : ∀ f g, 𝔞 f g = 𝔞 g f) (h11 : 𝔞 (fun _ => 1) (fun _ => 1) = 1) {e β : ℝ}
    (hβ : β < 1) (S : (Ω → ℝ) → Prop) (hS : ∀ f, S f → S (center ν f))
    (he : ∀ f, S f → ν.expect f = 0 → |𝔞 f (fun _ => 1)| ≤ e * nrm ν f)
    (hP : ∀ f, S f → ν.expect f = 0 → 𝔞 f f ≤ β * nrm ν f ^ 2) (f : Ω → ℝ) (hf : S f) :
    𝔞 f f ≤ (1 + e ^ 2 / (1 - β)) * nrm ν f ^ 2 := by
  rw [form_decomp ν 𝔞 hsym f, h11, nrm_sq_decomp ν f, ← sq_abs (ν.expect f)]
  refine block_upper_scalar (a := 1) (d := β) (b := e) hβ (by rw [one_mul, sq_abs]; linarith)
    (hP _ (hS f hf) (expect_center ν f)) ?_
  rw [abs_mul]
  calc |ν.expect f| * |𝔞 (center ν f) (fun _ => 1)|
      ≤ |ν.expect f| * (e * nrm ν (center ν f)) :=
        mul_le_mul_of_nonneg_left (he _ (hS f hf) (expect_center ν f)) (abs_nonneg _)
    _ = e * |ν.expect f| * nrm ν (center ν f) := by ring

/-- **`prop:matching:positive` (a′) on a subspace `S ∋ 1` closed under centring.** -/
theorem envelope_lower_on (ν : FiniteLaw Ω) (𝔞 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hsym : ∀ f g, 𝔞 f g = 𝔞 g f) (h11 : 𝔞 (fun _ => 1) (fun _ => 1) = 1) {e g : ℝ}
    (hg : 0 ≤ g) (S : (Ω → ℝ) → Prop) (hS : ∀ f, S f → S (center ν f))
    (he : ∀ f, S f → ν.expect f = 0 → |𝔞 f (fun _ => 1)| ≤ e * nrm ν f)
    (hP : ∀ f, S f → ν.expect f = 0 → -g * nrm ν f ^ 2 ≤ 𝔞 f f) (f : Ω → ℝ) (hf : S f) :
    -(g + e ^ 2 / (1 + g)) * nrm ν f ^ 2 ≤ 𝔞 f f := by
  rw [form_decomp ν 𝔞 hsym f, h11, nrm_sq_decomp ν f, ← sq_abs (ν.expect f)]
  have h := block_lower_scalar (a := 1) (d := -g) (b := e) (X := |ν.expect f|)
    (Y := nrm ν (center ν f)) (qA := |ν.expect f| ^ 2 * 1)
    (qD := 𝔞 (center ν f) (center ν f)) (c := ν.expect f * 𝔞 (center ν f) (fun _ => 1))
    (by linarith) (by rw [one_mul, mul_one]) (hP _ (hS f hf) (expect_center ν f)) ?_
  · have e1 : -g - e ^ 2 / (1 - -g) = -(g + e ^ 2 / (1 + g)) := by
      rw [show (1 : ℝ) - -g = 1 + g by ring]
      ring
    rw [e1] at h
    rw [sq_abs] at h ⊢
    linarith
  · rw [abs_mul]
    calc |ν.expect f| * |𝔞 (center ν f) (fun _ => 1)|
        ≤ |ν.expect f| * (e * nrm ν (center ν f)) :=
          mul_le_mul_of_nonneg_left (he _ (hS f hf) (expect_center ν f)) (abs_nonneg _)
      _ = e * |ν.expect f| * nrm ν (center ν f) := by ring

/-! ### The averaging projection -/

variable {Γ : Type*} [Group Γ] [Fintype Γ] [MulAction Γ Ω]

/-- `U_γ f = f ∘ γ⁻¹`. -/
def act (γ : Γ) (f : Ω → ℝ) : Ω → ℝ := fun x => f (γ⁻¹ • x)

/-- The averaging projection `P f = |Γ|⁻¹ ∑_γ U_γ f`. -/
noncomputable def avg (Γ : Type*) [Group Γ] [Fintype Γ] [MulAction Γ Ω] (f : Ω → ℝ) : Ω → ℝ :=
  (Fintype.card Γ : ℝ)⁻¹ • ∑ γ : Γ, act γ f

omit [Fintype Ω] in
theorem avg_apply (f : Ω → ℝ) (x : Ω) :
    avg Γ f x = (Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ, f (γ⁻¹ • x) := by
  simp only [avg, Pi.smul_apply, Finset.sum_apply, act, smul_eq_mul]

/-- `f` is `Γ`-invariant. -/
def Invariant (Γ : Type*) [Group Γ] [MulAction Γ Ω] (f : Ω → ℝ) : Prop :=
  ∀ (γ : Γ) x, f (γ • x) = f x

omit [Fintype Ω] in
theorem avg_invariant (f : Ω → ℝ) : Invariant Γ (avg Γ f) := by
  intro δ x
  rw [avg_apply, avg_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft δ⁻¹) _ _ (fun γ => by
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, mul_smul])

omit [Fintype Ω] in
theorem avg_of_invariant {f : Ω → ℝ} (hf : Invariant Γ f) : avg Γ f = f := by
  funext x
  rw [avg_apply]
  have hfx : ∀ γ : Γ, f (γ⁻¹ • x) = f x := fun γ => hf γ⁻¹ x
  simp only [hfx, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

omit [Fintype Ω] in
theorem avg_avg (f : Ω → ℝ) : avg Γ (avg Γ f) = avg Γ f := avg_of_invariant (avg_invariant f)

omit [Fintype Ω] [Fintype Γ] in
theorem invariant_const (c : ℝ) : Invariant Γ (fun _ : Ω => c) := fun _ _ => rfl

omit [Fintype Γ] in
theorem invariant_center (ν : FiniteLaw Ω) {f : Ω → ℝ} (hf : Invariant Γ f) :
    Invariant Γ (center ν f) := fun γ x => by
  simp only [center, hf γ x]

omit [Fintype Γ] in
/-- `U_γ` preserves the inner product of an invariant law. -/
theorem ip_act (ν : FiniteLaw Ω) (hν : ∀ (γ : Γ) x, ν.weight (γ • x) = ν.weight x) (γ : Γ)
    (f g : Ω → ℝ) : ip ν (act γ f) (act γ g) = ip ν f g := by
  unfold ip act FiniteLaw.expect
  exact Fintype.sum_equiv (MulAction.toPerm γ⁻¹) _ _ (fun x => by
    simp only [MulAction.toPerm_apply]
    rw [← hν γ (γ⁻¹ • x), smul_inv_smul])

/-- `P` is self-adjoint. -/
theorem ip_avg (ν : FiniteLaw Ω) (hν : ∀ (γ : Γ) x, ν.weight (γ • x) = ν.weight x)
    (f g : Ω → ℝ) : ip ν (avg Γ f) g = ip ν f (avg Γ g) := by
  have hsum : ∀ γ : Γ, ip ν (act γ f) g = ip ν f (act γ⁻¹ g) := by
    intro γ
    rw [← ip_act ν hν γ f (act γ⁻¹ g)]
    congr 1
    funext x
    simp only [act, inv_inv, smul_inv_smul]
  have e1 : ip ν (avg Γ f) g = (Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ, ip ν (act γ f) g := by
    unfold ip
    simp only [avg_apply, FiniteLaw.expect, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun γ _ => Finset.sum_congr rfl (fun x _ => ?_))
    simp only [act]
    ring
  have e2 : ip ν f (avg Γ g) = (Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ, ip ν f (act γ g) := by
    unfold ip
    simp only [avg_apply, FiniteLaw.expect, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun γ _ => Finset.sum_congr rfl (fun x _ => ?_))
    simp only [act]
    ring
  rw [e1, e2]
  congr 1
  simp only [hsum]
  exact Fintype.sum_equiv (Equiv.inv Γ) _ _ (fun γ => rfl)

omit [Fintype Ω] in
/-- `A` commutes with `P`: `𝔞(P f, g) = 𝔞(f, P g)`. -/
theorem form_avg (𝔞 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) →ₗ[ℝ] ℝ)
    (h𝔞 : ∀ (γ : Γ) f h, 𝔞 (act γ f) (act γ h) = 𝔞 f h) (f g : Ω → ℝ) :
    𝔞 (avg Γ f) g = 𝔞 f (avg Γ g) := by
  have hsum : ∀ γ : Γ, 𝔞 (act γ f) g = 𝔞 f (act γ⁻¹ g) := by
    intro γ
    rw [← h𝔞 γ f (act γ⁻¹ g)]
    congr 1
    funext x
    simp only [act, inv_inv, smul_inv_smul]
  unfold avg
  rw [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  simp only [smul_eq_mul, hsum]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv Γ) _ _ (fun γ => rfl)

omit [Fintype Ω] in
/-- `A` preserves `𝓘` and `𝓘^⊥`: `𝔞(P f, f - P f) = 0`. -/
theorem form_cross_vanish (𝔞 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) →ₗ[ℝ] ℝ)
    (h𝔞 : ∀ (γ : Γ) f h, 𝔞 (act γ f) (act γ h) = 𝔞 f h) (f : Ω → ℝ) :
    𝔞 (avg Γ f) (f - avg Γ f) = 0 := by
  rw [form_avg 𝔞 h𝔞]
  have : avg Γ (f - avg Γ f) = 0 := by
    funext x
    rw [avg_apply]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, Pi.zero_apply]
    have h2 : ∑ γ : Γ, avg Γ f (γ⁻¹ • x) = ∑ _γ : Γ, avg Γ f x :=
      Finset.sum_congr rfl (fun γ _ => avg_invariant f γ⁻¹ x)
    rw [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_sub, avg_apply]
    have : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
    ring
  rw [this, map_zero]

/-- **`prop:matching:positive` (a″).** With `|⟨f, Af⟩| ≤ C‖f‖²` on `𝓘^⊥`,
`|⟨f, Af⟩| ≤ H‖f‖²` on `𝓘 ∩ 1^⊥` (`0 ≤ H < 1`) and `|⟨f, A1⟩| ≤ e‖f‖` on `𝓘 ∩ 1^⊥`,
`-max(C, H + e²) ‖f‖² ≤ ⟨f, Af⟩ ≤ max(C, 1 + e²/(1 - H)) ‖f‖²`. -/
theorem sectors_bound (ν : FiniteLaw Ω) (hν : ∀ (γ : Γ) x, ν.weight (γ • x) = ν.weight x)
    (𝔞 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) →ₗ[ℝ] ℝ) (hsym : ∀ f g, 𝔞 f g = 𝔞 g f)
    (h𝔞 : ∀ (γ : Γ) f h, 𝔞 (act γ f) (act γ h) = 𝔞 f h)
    (h11 : 𝔞 (fun _ => 1) (fun _ => 1) = 1) {C H e : ℝ} (hH0 : 0 ≤ H) (hH1 : H < 1)
    (hC : ∀ f, avg Γ f = 0 → |𝔞 f f| ≤ C * nrm ν f ^ 2)
    (hHb : ∀ f, Invariant Γ f → ν.expect f = 0 → |𝔞 f f| ≤ H * nrm ν f ^ 2)
    (he : ∀ f, Invariant Γ f → ν.expect f = 0 → |𝔞 f (fun _ => 1)| ≤ e * nrm ν f)
    (f : Ω → ℝ) :
    -max C (H + e ^ 2) * nrm ν f ^ 2 ≤ 𝔞 f f ∧
      𝔞 f f ≤ max C (1 + e ^ 2 / (1 - H)) * nrm ν f ^ 2 := by
  set g := avg Γ f with hg
  set r := f - avg Γ f with hr
  have hfr : f = g + r := by rw [hg, hr]; abel
  have hgI : Invariant Γ g := avg_invariant f
  have hr0 : avg Γ r = 0 := by
    funext x
    rw [hr]
    rw [avg_apply]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, Pi.zero_apply]
    have h2 : ∑ γ : Γ, avg Γ f (γ⁻¹ • x) = ∑ _γ : Γ, avg Γ f x :=
      Finset.sum_congr rfl (fun γ _ => avg_invariant f γ⁻¹ x)
    rw [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_sub, avg_apply]
    have : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
    ring
  -- the form splits
  have hcross : 𝔞 g r = 0 := form_cross_vanish 𝔞 h𝔞 f
  have hsplit : 𝔞 f f = 𝔞 g g + 𝔞 r r := by
    rw [hfr]
    simp only [map_add, LinearMap.add_apply]
    rw [hcross, hsym r g, hcross]
    ring
  -- the norm splits
  have hipc : ip ν g r = 0 := by
    rw [hg, ip_avg ν hν]
    have : avg Γ r = fun _ => 0 := hr0
    rw [this]
    unfold ip
    simp only [mul_zero, FiniteLaw.expect_const]
  have hnsplit : nrm ν f ^ 2 = nrm ν g ^ 2 + nrm ν r ^ 2 := by
    rw [nrm_sq_eq, nrm_sq_eq, nrm_sq_eq]
    have e : ip ν f f = ip ν g g + 2 * ip ν g r + ip ν r r := by
      rw [hfr]
      unfold ip FiniteLaw.expect
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun x _ => by simp only [Pi.add_apply]; ring)
    rw [e, hipc]
    ring
  -- the invariant subspace
  have hS : ∀ f, Invariant Γ f → Invariant Γ (center ν f) := fun f hf => invariant_center ν hf
  have hup := envelope_upper_on ν 𝔞 hsym h11 hH1 (Invariant Γ) hS he
    (fun f hf hf0 => (le_abs_self _).trans (hHb f hf hf0)) g hgI
  have hlo := envelope_lower_on ν 𝔞 hsym h11 hH0 (Invariant Γ) hS he
    (fun f hf hf0 => by
      have := hHb f hf hf0
      linarith [neg_abs_le (𝔞 f f)]) g hgI
  have hCr := hC r hr0
  have hng := sq_nonneg (nrm ν g)
  have hnr := sq_nonneg (nrm ν r)
  have hlo' : -(H + e ^ 2) * nrm ν g ^ 2 ≤ 𝔞 g g := by
    refine le_trans ?_ hlo
    have : e ^ 2 / (1 + H) ≤ e ^ 2 := div_le_self (sq_nonneg e) (by linarith)
    nlinarith
  constructor
  · rw [hsplit, hnsplit]
    have h1 : -max C (H + e ^ 2) * nrm ν g ^ 2 ≤ -(H + e ^ 2) * nrm ν g ^ 2 := by
      have := le_max_right C (H + e ^ 2)
      nlinarith
    have h2 : -max C (H + e ^ 2) * nrm ν r ^ 2 ≤ 𝔞 r r := by
      have := le_max_left C (H + e ^ 2)
      nlinarith [neg_abs_le (𝔞 r r)]
    nlinarith
  · rw [hsplit, hnsplit]
    have h1 : 𝔞 g g ≤ max C (1 + e ^ 2 / (1 - H)) * nrm ν g ^ 2 := by
      have := le_max_right C (1 + e ^ 2 / (1 - H))
      nlinarith
    have h2 : 𝔞 r r ≤ max C (1 + e ^ 2 / (1 - H)) * nrm ν r ^ 2 := by
      have := le_max_left C (1 + e ^ 2 / (1 - H))
      nlinarith [le_abs_self (𝔞 r r)]
    nlinarith

end Sarkozy.Cuts
