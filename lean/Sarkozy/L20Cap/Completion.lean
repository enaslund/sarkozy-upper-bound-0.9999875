module

public import Sarkozy.L20Cap.Caps
public import Sarkozy.Cuts.Sectors

/-!
# Translation sectors and the upper cap of L20 (`prop:l20-completion`)

`paper/sections/20_middle_reference.tex`, `prop:l20-completion` and `prop:l20-rectangular`(d)
(the norm on `𝓘^⊥`). Notation of `Sarkozy.L20Cap.Caps`.

The simultaneous translations `x_k ↦ x_k + y` act on the halves (`Multiplicative F` acting by
`transl`); `𝓘` is the space of invariant functions.

Proved:
* `halfLaw_transl`, `cutT_transl`, `cutT_form_inv`: the translations preserve `μ_p` and the cut
  kernel, so `T` commutes with them (and preserves `𝓘`, `𝓘^⊥`, via `Cuts.sectors_bound`);
* **`cutT_perp`** (`prop:l20-rectangular`(d), the second claim): under the hypotheses of
  `cutT_lower`, `|⟨f, Tf⟩| ≤ C'‖f‖²` for `f ⊥ 𝔯 ⊗ 𝟙`, in particular on `𝓘^⊥`
  (`lem:swapped-rectangle`(a), `Cuts.swap_norm_perp`; the top singular vector `𝔯 ⊗ 𝟙` is
  translation invariant);
* **`cutT_upper`** (`prop:l20-completion`, `eq:l20-caps`, upper half): if moreover the soft
  kernel is bounded by `N_ns` on `𝓘 ∩ 𝟙^⊥` (there the star terms vanish and `K_soft` acts as the
  nonstar part `T_ns`), `‖T𝟙 - 𝟙‖² ≤ χ⁺_p`, `C' < 1` and `H₂₀ = (N_ns + D_col)/(1 - ε_Z) < 1`,
  then `T ⪯ (1 + χ⁺_p/(1 - H₂₀)) I = (1 + c⁺/p) I`, `c⁺ = pχ⁺_p/(1 - H₂₀)`;
* `cutT_caps`: both caps at the prime, `-C' ⪯ T ⪯ 1 + χ⁺_p/(1 - H₂₀)`.

Hypotheses (not proved here): the vanishing of the star terms on `𝓘 ∩ 𝟙^⊥` together with
`‖T_ns‖ ≤ N_ns` (`lem:spec:stars`, `lem:spec:affpair`(d), `cor:extraction-compressed`), and
`‖T𝟙 - 𝟙‖² ≤ χ⁺_p` (`lem:record:root-marginal`(ii)); those of `cutT_lower`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The translations -/

theorem quadraticChar_one' : quadraticChar F 1 = 1 := map_one _

/-- The simultaneous translation by `y` of a half. -/
def transl (y : F) (x : CoreT F × PairT F) : CoreT F × PairT F :=
  (affCoreEquiv quadraticChar_one' y x.1, affPairEquiv one_ne_zero y x.2)

theorem transl_zero (x : CoreT F × PairT F) : transl 0 x = x := by
  obtain ⟨C, b⟩ := x
  simp only [transl, affCoreEquiv, affPairEquiv, Equiv.coe_fn_mk]
  congr 1
  · apply Subtype.ext; funext k; simp [affCore]
  · apply Subtype.ext; simp [affPair]

theorem transl_add (a b : F) (x : CoreT F × PairT F) :
    transl (a + b) x = transl a (transl b x) := by
  obtain ⟨C, c⟩ := x
  simp only [transl, affCoreEquiv, affPairEquiv, Equiv.coe_fn_mk]
  congr 1
  · apply Subtype.ext; funext k; simp only [affCore]; ring
  · apply Subtype.ext; simp only [affPair]; ext <;> simp only <;> ring

instance : MulAction (Multiplicative F) (CoreT F × PairT F) where
  smul y x := transl (Multiplicative.toAdd y) x
  one_smul x := transl_zero x
  mul_smul a b x := transl_add (Multiplicative.toAdd a) (Multiplicative.toAdd b) x

theorem smul_def (y : Multiplicative F) (x : CoreT F × PairT F) :
    y • x = transl (Multiplicative.toAdd y) x := rfl

theorem Avoid_transl (y : F) (x : CoreT F × PairT F) : Avoid (transl y x) ↔ Avoid x := by
  obtain ⟨C, b⟩ := x
  simp only [Avoid, transl, affCoreEquiv, affPairEquiv, Equiv.coe_fn_mk, affCore, affPair,
    one_mul, ne_eq, add_left_inj]

theorem Disj_transl (y : F) (x x' : CoreT F × PairT F) :
    Disj (transl y x) (transl y x') ↔ Disj x x' := by
  obtain ⟨C, b⟩ := x
  obtain ⟨C', b'⟩ := x'
  have e : ∀ (C : CoreT F) (b : PairT F) i, labels (transl y (C, b)) i = labels (C, b) i + y := by
    intro C b i
    fin_cases i <;> simp [labels, emb, transl, affCoreEquiv, affPairEquiv, affCore, affPair]
  simp only [Disj, e, ne_eq, add_left_inj]

theorem Ksoft_transl (y : F) (x x' : CoreT F × PairT F) :
    Ksoft (transl y x) (transl y x') = Ksoft x x' := by
  simp only [Ksoft, transl]
  rw [Rk_affine quadraticChar_one', Rk_affine quadraticChar_one']

theorem K0_transl (y : F) (x x' : CoreT F × PairT F) :
    K0 (transl y x) (transl y x') = K0 x x' := by
  unfold K0
  by_cases h : Disj x x'
  · simp only [(Disj_transl y x x').mpr h, h, ↓reduceIte, Ksoft_transl]
  · have h' : ¬ Disj (transl y x) (transl y x') := fun h'' => h ((Disj_transl y x x').mp h'')
    simp only [h, h', ↓reduceIte]

variable [Nonempty (CoreT F)] [Nonempty (PairT F)]

theorem halfLaw_transl (h6 : 6 ≤ Fintype.card F) (γ : Multiplicative F)
    (x : CoreT F × PairT F) : (halfLaw h6).weight (γ • x) = (halfLaw h6).weight x := by
  simp only [halfLaw, condLaw, smul_def]
  by_cases h : Avoid x
  · simp only [(Avoid_transl _ x).mpr h, h, ↓reduceIte]
    congr 1
  · have h' : ¬ Avoid (transl (Multiplicative.toAdd γ) x) := fun h'' =>
      h ((Avoid_transl _ x).mp h'')
    simp only [h, h', ↓reduceIte]

theorem cutT_transl (h6 : 6 ≤ Fintype.card F) (γ : Multiplicative F) (x x' : CoreT F × PairT F) :
    cutT h6 (γ • x) (γ • x') = cutT h6 x x' := by
  simp only [cutT, smul_def, K0_transl]

/-- The cut form is invariant under the translations. -/
theorem cutT_form_inv (h6 : 6 ≤ Fintype.card F) (γ : Multiplicative F)
    (f h : CoreT F × PairT F → ℝ) :
    kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) (act γ f) (act γ h) =
      kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f h := by
  simp only [kernelForm, LinearMap.mk₂_apply, act]
  refine Fintype.sum_equiv (MulAction.toPerm γ⁻¹) _ _ fun x => ?_
  refine Fintype.sum_equiv (MulAction.toPerm γ⁻¹) _ _ fun x' => ?_
  simp only [MulAction.toPerm_apply]
  rw [← halfLaw_transl h6 γ (γ⁻¹ • x), ← halfLaw_transl h6 γ (γ⁻¹ • x'), smul_inv_smul,
    smul_inv_smul, ← cutT_transl h6 γ (γ⁻¹ • x) (γ⁻¹ • x'), smul_inv_smul, smul_inv_smul]

/-! ## The norm on `𝓘^⊥` -/

theorem kernelForm_eq_ip_swapOp (Fn : CoreT F × PairT F → ℝ) :
    kernelForm ((coreLaw (F := F)).product (pairLaw (F := F)))
        ((coreLaw (F := F)).product (pairLaw (F := F))) (fun x x' => Rk x.1 x'.2 * Rk x'.1 x.2)
        Fn Fn =
      ip ((coreLaw (F := F)).product (pairLaw (F := F))) Fn
        (swapOp (coreLaw (F := F)) (pairLaw (F := F)) Rk Fn) := by
  rw [kernelForm_apply]
  rfl

/-- **`prop:l20-rectangular`(d), the norm off the top singular vector**: under the hypotheses of
`rect_lower`, `|⟨F, T[𝖱, 𝖱]F⟩| ≤ s c_R ‖F‖²` for `F ⊥ 𝔯 ⊗ 𝟙` (`Cuts.swap_norm_perp`). -/
theorem rect_perp (hm1 : quadraticChar F (-1) = -1) {cR s : ℝ} (hcR : 0 ≤ cR)
    (hRc : ∀ h : PairT F → ℝ,
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc h) ≤ cR * nrm (pairLaw (F := F)) h)
    (hs : nrm (coreLaw (F := F)) rmass ≤ s) (hcs : cR ≤ s) (Fn : CoreT F × PairT F → ℝ)
    (hperp : ip ((coreLaw (F := F)).product (pairLaw (F := F))) Fn (fun x => rmass x.1) = 0) :
    |kernelForm ((coreLaw (F := F)).product (pairLaw (F := F)))
        ((coreLaw (F := F)).product (pairLaw (F := F))) (fun x x' => Rk x.1 x'.2 * Rk x'.1 x.2)
        Fn Fn| ≤ s * cR * nrm ((coreLaw (F := F)).product (pairLaw (F := F))) Fn ^ 2 := by
  rw [kernelForm_eq_ip_swapOp]
  set ν := (coreLaw (F := F)).product (pairLaw (F := F))
  have hG : nrm ν (swapOp (coreLaw (F := F)) (pairLaw (F := F)) Rk Fn) ≤ s * cR * nrm ν Fn := by
    set σ := nrm (coreLaw (F := F)) rmass with hσdef
    have hσ0 : 0 ≤ σ := nrm_nonneg _ _
    by_cases hσ : σ = 0
    · have hr0 := rmass_eq_zero_of_nrm hσ
      have hRk : ∀ h : PairT F → ℝ,
          nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rk h) ≤
            cR * nrm (pairLaw (F := F)) h := by
        intro h
        have := hRc h
        unfold Rc at this
        simpa [hr0] using this
      have h1 := nrm_swapOp_le (coreLaw (F := F)) (pairLaw (F := F)) Rk hcR hRk Fn
      have h2 : cR ^ 2 ≤ s * cR := by nlinarith
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (nrm_nonneg _ _))
    · have hσp : 0 < σ := lt_of_le_of_ne hσ0 (Ne.symm hσ)
      refine swap_norm_perp coreLaw pairLaw Rk Rc (σ₀ := σ) (fun C => σ⁻¹ * rmass C) (fun _ => 1)
        ?_ (nrm_one _) hσ0 ?_ ?_ ?_ hcR hRc hs hcs Fn ?_
      · rw [nrm_smul, abs_of_pos (inv_pos.mpr hσp), ← hσdef, inv_mul_cancel₀ hσ]
      · intro C b
        unfold Rc
        field_simp
        ring
      · exact recOp_Rc_one
      · intro b
        unfold recAdj Rc
        have e : ∀ C, (Rk C b - rmass C) * (σ⁻¹ * rmass C) =
            σ⁻¹ * (Rk C b * rmass C - rmass C ^ 2) := fun C => by ring
        rw [(coreLaw (F := F)).expect_congr e, FiniteLaw.expect_const_mul, FiniteLaw.expect_sub]
        have h1 := adj_rmass hm1 b
        unfold recAdj at h1
        rw [h1, ← nrm_sq_expect, ← hσdef]
        ring
      · unfold ip at hperp ⊢
        have e : ∀ x : CoreT F × PairT F, Fn x * (σ⁻¹ * rmass x.1 * 1) = σ⁻¹ * (Fn x * rmass x.1) :=
          fun x => by ring
        rw [ν.expect_congr e, FiniteLaw.expect_const_mul, hperp, mul_zero]
  calc |ip ν Fn (swapOp (coreLaw (F := F)) (pairLaw (F := F)) Rk Fn)|
      ≤ nrm ν Fn * nrm ν (swapOp (coreLaw (F := F)) (pairLaw (F := F)) Rk Fn) := abs_ip_le _ _ _
    _ ≤ nrm ν Fn * (s * cR * nrm ν Fn) := mul_le_mul_of_nonneg_left hG (nrm_nonneg _ _)
    _ = s * cR * nrm ν Fn ^ 2 := by ring

/-- The soft kernel on `L²(μ_p)` off `𝔯 ⊗ 𝟙`: `|⟨f, K_soft f⟩| ≤ (s c_R/h_p)‖f‖²`. -/
theorem soft_perp (hm1 : quadraticChar F (-1) = -1) (h6 : 6 ≤ Fintype.card F) {cR s : ℝ}
    (hcR : 0 ≤ cR)
    (hRc : ∀ h : PairT F → ℝ,
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc h) ≤ cR * nrm (pairLaw (F := F)) h)
    (hs : nrm (coreLaw (F := F)) rmass ≤ s) (hcs : cR ≤ s) (f : CoreT F × PairT F → ℝ)
    (hperp : ip (halfLaw h6) f (fun x => rmass x.1) = 0) :
    |kernelForm (halfLaw h6) (halfLaw h6) Ksoft f f| ≤
      s * cR / prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid *
        nrm (halfLaw h6) f ^ 2 := by
  set ν := (coreLaw (F := F)).product (pairLaw (F := F))
  set P := prob ν Avoid with hPdef
  have hP0 : 0 < P := hP_pos h6
  have e1 : kernelForm (halfLaw h6) (halfLaw h6) Ksoft f f =
      P⁻¹ * P⁻¹ * kernelForm ν ν (fun x x' => Rk x.1 x'.2 * Rk x'.1 x.2)
        (fun ω => (if Avoid ω then 1 else 0) * f ω) (fun ω => (if Avoid ω then 1 else 0) * f ω) :=
    kernelForm_condLaw ν Avoid (hP_pos h6) Ksoft f
  have hperp' : ip ν (fun ω => (if Avoid ω then 1 else 0) * f ω) (fun x => rmass x.1) = 0 := by
    have h := hperp
    unfold ip at h ⊢
    unfold halfLaw at h
    rw [condLaw_expect] at h
    have hPi : P⁻¹ ≠ 0 := inv_ne_zero hP0.ne'
    have h' := (mul_eq_zero.mp h).resolve_left hPi
    calc _ = ν.expect (fun ω => (if Avoid ω then 1 else 0) * (f ω * (fun x => rmass x.1) ω)) :=
          ν.expect_congr fun ω => by ring
      _ = 0 := h'
  have hb := rect_perp hm1 hcR hRc hs hcs _ hperp'
  have hn := nrm_condLaw ν Avoid (hP_pos h6) f
  rw [e1, abs_mul, abs_of_pos (mul_pos (inv_pos.mpr hP0) (inv_pos.mpr hP0))]
  calc P⁻¹ * P⁻¹ * |kernelForm ν ν (fun x x' => Rk x.1 x'.2 * Rk x'.1 x.2)
        (fun ω => (if Avoid ω then 1 else 0) * f ω) (fun ω => (if Avoid ω then 1 else 0) * f ω)|
      ≤ P⁻¹ * P⁻¹ * (s * cR * nrm ν (fun ω => (if Avoid ω then 1 else 0) * f ω) ^ 2) :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg (inv_nonneg.mpr hP0.le) (inv_nonneg.mpr hP0.le))
    _ = s * cR / P * nrm (halfLaw h6) f ^ 2 := by
        have e : nrm (condLaw ν Avoid (hP_pos h6)) f = nrm (halfLaw h6) f := rfl
        rw [hn, e, ← hPdef]
        field_simp

/-- **`prop:l20-rectangular`(d), `‖T|_{𝓘^⊥}‖ ≤ C'`**, in the form: `|⟨f, Tf⟩| ≤ C'‖f‖²` for every
`f ⊥ 𝔯 ⊗ 𝟙` (which contains `𝓘^⊥`), `C' = (s c_R/h_p + D_col)/(1 - ε_Z)`. -/
theorem cutT_perp (hm1 : quadraticChar F (-1) = -1) (h6 : 6 ≤ Fintype.card F)
    {cR s D εZ : ℝ} (hcR : 0 ≤ cR)
    (hRc : ∀ h : PairT F → ℝ,
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc h) ≤ cR * nrm (pairLaw (F := F)) h)
    (hs : nrm (coreLaw (F := F)) rmass ≤ s) (hcs : cR ≤ s) (hD0 : 0 ≤ D)
    (hD : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) collK f f| ≤ D * nrm (halfLaw h6) f ^ 2)
    (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z0 h6) (f : CoreT F × PairT F → ℝ)
    (hperp : ip (halfLaw h6) f (fun x => rmass x.1) = 0) :
    |kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f| ≤
      (s * cR / prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid + D) / (1 - εZ) *
        nrm (halfLaw h6) f ^ 2 := by
  set P := prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid
  have hP0 : 0 < P := hP_pos h6
  have hZ0 : 0 < Z0 h6 := by linarith
  have hεpos : 0 < 1 - εZ := by linarith
  have h1 := soft_perp hm1 h6 hcR hRc hs hcs f hperp
  have h2 := hD f
  rw [cutT_form_eq, abs_div, abs_of_pos hZ0, div_le_iff₀ hZ0]
  set N := nrm (halfLaw h6) f ^ 2
  have hN0 : 0 ≤ N := sq_nonneg _
  have hs0 : 0 ≤ s := le_trans hcR hcs
  set a := s * cR / P + D
  have ha0 : 0 ≤ a := add_nonneg (div_nonneg (mul_nonneg hs0 hcR) hP0.le) hD0
  have h3 : |kernelForm (halfLaw h6) (halfLaw h6) Ksoft f f -
      kernelForm (halfLaw h6) (halfLaw h6) collK f f| ≤ a * N := by
    have := abs_sub (kernelForm (halfLaw h6) (halfLaw h6) Ksoft f f)
      (kernelForm (halfLaw h6) (halfLaw h6) collK f f)
    have e : a * N = s * cR / P * N + D * N := by ring
    linarith
  have h4 : a * N ≤ a / (1 - εZ) * N * Z0 h6 := by
    have e : a / (1 - εZ) * N * Z0 h6 = a * N * (Z0 h6 / (1 - εZ)) := by ring
    rw [e]
    have : 1 ≤ Z0 h6 / (1 - εZ) := by rw [le_div_iff₀ hεpos]; linarith
    nlinarith [mul_nonneg ha0 hN0]
  linarith

/-! ## The upper cap (`prop:l20-completion`) -/

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
theorem kernelForm_symm_of {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω) (K : Ω → Ω → ℝ)
    (hK : ∀ x y, K x y = K y x) (f g : Ω → ℝ) : kernelForm ν ν K f g = kernelForm ν ν K g f := by
  simp only [kernelForm, LinearMap.mk₂_apply]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [hK y x]
  ring

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
/-- `|(A - B)/Z₀| ≤ (a + D)/(1 - ε_Z) · N` from `|A| ≤ aN`, `|B| ≤ DN`, `Z₀ ≥ 1 - ε_Z > 0`. -/
theorem quot_bound {A B a D N Z εZ : ℝ} (ha : 0 ≤ a) (hD : 0 ≤ D) (hN : 0 ≤ N) (hε : εZ < 1)
    (hZ : 1 - εZ ≤ Z) (hA : |A| ≤ a * N) (hB : |B| ≤ D * N) :
    |(A - B) / Z| ≤ (a + D) / (1 - εZ) * N := by
  have hεpos : 0 < 1 - εZ := by linarith
  have hZ0 : 0 < Z := by linarith
  rw [abs_div, abs_of_pos hZ0, div_le_iff₀ hZ0]
  have h3 : |A - B| ≤ (a + D) * N := by
    have := abs_sub A B
    nlinarith
  have h4 : (a + D) * N ≤ (a + D) / (1 - εZ) * N * Z := by
    have e : (a + D) / (1 - εZ) * N * Z = (a + D) * N * (Z / (1 - εZ)) := by ring
    rw [e]
    have : 1 ≤ Z / (1 - εZ) := by rw [le_div_iff₀ hεpos]; linarith
    nlinarith [mul_nonneg (add_nonneg ha hD) hN]
  linarith

theorem cutT_one_one (h6 : 6 ≤ Fintype.card F) (hZ0 : Z0 h6 ≠ 0) :
    kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) (fun _ => 1) (fun _ => 1) = 1 := by
  change kernelForm (halfLaw h6) (halfLaw h6) (fun x y => K0 x y / Z0 h6) (fun _ => 1)
    (fun _ => 1) = 1
  rw [kernelForm_div_kernel]
  exact div_self hZ0

omit [Nonempty (CoreT F)] in
/-- `𝔯 ⊗ 𝟙` is translation invariant. -/
theorem rmass_fst_invariant :
    Invariant (Multiplicative F) (fun x : CoreT F × PairT F => rmass x.1) := by
  intro γ x
  simp only [smul_def, transl]
  exact rmass_affine quadraticChar_one' _ x.1

/-- **`prop:l20-completion`, the upper cap** (`eq:l20-caps`): `T ⪯ (1 + χ⁺_p/(1 - H₂₀)) I`, i.e.
`T ⪯ (1 + c⁺/p) I` with `c⁺ = pχ⁺_p/(1 - H₂₀)`, `H₂₀ = (N_ns + D_col)/(1 - ε_Z)`. From
`prop:matching:positive`(a″) for the translations (`Cuts.sectors_bound`): `T` is bounded by
`C' < 1` on `𝓘^⊥` (`cutT_perp`), by `H₂₀` on `𝓘 ∩ 𝟙^⊥`, and `‖P₀T𝟙‖ ≤ ‖T𝟙 - 𝟙‖ ≤ (χ⁺_p)^{1/2}`. -/
theorem cutT_upper (hm1 : quadraticChar F (-1) = -1) (h6 : 6 ≤ Fintype.card F)
    {cR s D εZ Nns χp : ℝ} (hcR : 0 ≤ cR)
    (hRc : ∀ h : PairT F → ℝ,
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc h) ≤ cR * nrm (pairLaw (F := F)) h)
    (hs : nrm (coreLaw (F := F)) rmass ≤ s) (hcs : cR ≤ s) (hD0 : 0 ≤ D)
    (hD : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) collK f f| ≤ D * nrm (halfLaw h6) f ^ 2)
    (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z0 h6) (hNns0 : 0 ≤ Nns)
    (hns : ∀ f, Invariant (Multiplicative F) f → (halfLaw h6).expect f = 0 →
      |kernelForm (halfLaw h6) (halfLaw h6) Ksoft f f| ≤ Nns * nrm (halfLaw h6) f ^ 2)
    (hχ0 : 0 ≤ χp)
    (hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp)
    (hC1 : (s * cR / prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid + D) /
      (1 - εZ) < 1)
    (hH1 : (Nns + D) / (1 - εZ) < 1) (f : CoreT F × PairT F → ℝ) :
    kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ≤
      (1 + χp / (1 - (Nns + D) / (1 - εZ))) * nrm (halfLaw h6) f ^ 2 := by
  set P := prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid
  set C' := (s * cR / P + D) / (1 - εZ) with hC'
  set H := (Nns + D) / (1 - εZ) with hH
  have hεpos : 0 < 1 - εZ := by linarith
  have hZ0 : 0 < Z0 h6 := by linarith
  have hH0 : 0 ≤ H := div_nonneg (add_nonneg hNns0 hD0) hεpos.le
  have hsym : ∀ f g, kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f g =
      kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) g f :=
    kernelForm_symm_of _ _ (fun x y => cutT_symm' _ x y)
  have hC : ∀ f, avg (Multiplicative F) f = 0 →
      |kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f| ≤ C' * nrm (halfLaw h6) f ^ 2 := by
    intro f hf
    refine cutT_perp hm1 h6 hcR hRc hs hcs hD0 hD hεZ hZ f ?_
    have hg := rmass_fst_invariant (F := F)
    rw [← avg_of_invariant hg, ← ip_avg (halfLaw h6) (halfLaw_transl h6), hf]
    simp [ip]
  have hHb : ∀ f, Invariant (Multiplicative F) f → (halfLaw h6).expect f = 0 →
      |kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f| ≤ H * nrm (halfLaw h6) f ^ 2 := by
    intro f hf hf0
    rw [cutT_form_eq]
    exact quot_bound hNns0 hD0 (sq_nonneg _) hεZ hZ (hns f hf hf0) (hD f)
  have he : ∀ f, Invariant (Multiplicative F) f → (halfLaw h6).expect f = 0 →
      |kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f (fun _ => 1)| ≤
        Real.sqrt χp * nrm (halfLaw h6) f := by
    intro f _ hf0
    have e : kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f (fun _ => 1) =
        ip (halfLaw h6) f (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) := by
      rw [kernelForm_apply]
      unfold ip recOp
      have : ∀ x, f x * (recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) =
          f x * (halfLaw h6).expect (fun y => cutT h6 x y * 1) - f x := fun x => by
        unfold recOp; ring
      unfold recOp at this
      rw [(halfLaw h6).expect_congr this, FiniteLaw.expect_sub, hf0, sub_zero]
    rw [e]
    have h1 := abs_ip_le (halfLaw h6) f (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1)
    have h2 : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ≤
        Real.sqrt χp := Real.le_sqrt_of_sq_le hchi
    calc _ ≤ _ := h1
      _ ≤ nrm (halfLaw h6) f * Real.sqrt χp := mul_le_mul_of_nonneg_left h2 (nrm_nonneg _ _)
      _ = _ := by ring
  have hsec := sectors_bound (Γ := Multiplicative F) (halfLaw h6) (halfLaw_transl h6)
    (kernelForm (halfLaw h6) (halfLaw h6) (cutT h6)) hsym (cutT_form_inv h6)
    (cutT_one_one h6 hZ0.ne') hH0 hH1 hC hHb he f
  rw [Real.sq_sqrt hχ0] at hsec
  have hmax : max C' (1 + χp / (1 - H)) = 1 + χp / (1 - H) := by
    apply max_eq_right
    have : 0 ≤ χp / (1 - H) := div_nonneg hχ0 (by linarith)
    linarith
  rw [hmax] at hsec
  exact hsec.2

/-- **The caps of L20 at a prime** (`prop:l20-completion` with `prop:l20-rectangular`(d)):
`-C' ⪯ T ⪯ 1 + χ⁺_p/(1 - H₂₀)`. With `c_R = c_gap`, `D_col = D_bal` this is `eq:l20-caps` at the
prime, `g = C₂₀/r`, `c⁺ = pχ⁺_p/(1 - H₂₀)` (`prop:l20-collisions`(b)). -/
theorem cutT_caps (hm1 : quadraticChar F (-1) = -1) (h6 : 6 ≤ Fintype.card F)
    {cR s D εZ Nns χp : ℝ} (hcR : 0 ≤ cR)
    (hRc : ∀ h : PairT F → ℝ,
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc h) ≤ cR * nrm (pairLaw (F := F)) h)
    (hs : nrm (coreLaw (F := F)) rmass ≤ s) (hcs : cR ≤ s) (hD0 : 0 ≤ D)
    (hD : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) collK f f| ≤ D * nrm (halfLaw h6) f ^ 2)
    (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z0 h6) (hNns0 : 0 ≤ Nns)
    (hns : ∀ f, Invariant (Multiplicative F) f → (halfLaw h6).expect f = 0 →
      |kernelForm (halfLaw h6) (halfLaw h6) Ksoft f f| ≤ Nns * nrm (halfLaw h6) f ^ 2)
    (hχ0 : 0 ≤ χp)
    (hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp)
    (hC1 : (s * cR / prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid + D) /
      (1 - εZ) < 1)
    (hH1 : (Nns + D) / (1 - εZ) < 1) (f : CoreT F × PairT F → ℝ) :
    -((s * cR / prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid + D) / (1 - εZ)) *
        nrm (halfLaw h6) f ^ 2 ≤ kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ∧
      kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ≤
        (1 + χp / (1 - (Nns + D) / (1 - εZ))) * nrm (halfLaw h6) f ^ 2 :=
  ⟨cutT_lower hm1 h6 hcR hRc hs hcs hD0 hD hεZ hZ f,
    cutT_upper hm1 h6 hcR hRc hs hcs hD0 hD hεZ hZ hNns0 hns hχ0 hchi hC1 hH1 f⟩

end Sarkozy.L20Cap
