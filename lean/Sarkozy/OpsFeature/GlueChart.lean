module

public import Sarkozy.OpsFeature.GlueLead
public import Sarkozy.OpsFeature.Realize
public import Sarkozy.OpsCore.A3Block
public import Sarkozy.OpsCore.LeadOp

@[expose] public section

/-!
# The chart's leading star at a fold block: `hLb` with `A₃°`, the change into the remainder

`paper/sections/23_envelopes.tex`, (N1), `eq:signed-star` (`Ξ_p = (V₀, V₁, V₂, A₃°/r_p, 0)`);
`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(b), `lem:actual-features`(c), (e).

OPS-L's `A3Perp`/`A3Block`: the projected arm `A₃° = A₃ − GA` (`GA` the closed-form projection on
`𝓗₁ + 𝓗₂`, `A3_perp`), the chart's block star `foldLeadC` and `foldLead_chart_le`:
`|L_{t,𝔅} − L°_{t,𝔅}| ≤ 2|1−t| J Γ^{1/2}` in `L²(m_{0,𝔅})`. Here, at a middle block, in
`L²(m_{0,𝔅})` with `m_{0,𝔅} = ∏_p mP_p` (`mB`):

* `foldLeadY` (the block star with a general third arm; `foldLead`, `foldLeadC` are the cases
  `A₃`, `A₃°`, by `rfl`), `foldLeadY_expand`, `foldBil` (as a bilinear map);
* `leadOpY Y w = opOfForm(w⁻¹ L^{(Y)}_{t,𝔅})` (OPS-L's `opOfForm`);
* **`chart_lead`**: with OPS-L's leading-star bound `|L_{t,𝔅}| ≤ ℓ'` (`hℓ`, `fold_skew_split`),
  1. `‖L − L°‖ ≤ w⁻¹ δ`, `δ = 2|1−t|JΓ^{1/2}` (the change goes into the remainder `e_R`;
     `formLE_route`: `‖Δ̂ − L‖ ≤ ρ ⇒ ‖Δ̂ − L°‖ ≤ ρ + w⁻¹δ`);
  2. `‖L°‖ ≤ w⁻¹(ℓ' + δ)`;
  3. **`hLb`**: the kernel of `L°` is the star form `∑_p c_p Ξ_p 𝖥(Φ̂_p) Ξ_pᵀ` with the paper's
     `Ξ_p` (third arm `A₃°`), `c_p = w⁻¹ r_p` (`kern_block_lead_starSum`).
* The columns of these `Ξ_p`: `chartXi_singleton` (`m_{0,𝔅}(x) √p(δ_{x_{p,a},z} − 1/p)`, labels
  `0, 1, 2`), `chartXi_three` (`m_{0,𝔅}(x) y_{3,p,z}(x)`, `yThree`); the singleton arms are centred,
  orthogonal across the sectors and contractions (`ySing_*`; product law `sum_mB_coord`,
  `sum_mB_two`, uniform coordinates `mP_coord`); the label-`3` arms are centred and orthogonal
  across the sectors (`yThree_*`).
* **`hUa_singleton_chart`** (labels `0, 1, 2`, unconditional), `hUa_three_chart` (label `3`) and
  **`hUa_fold_chart`**: the hypothesis `hUa` of `hdom_of_units` at a fold block for these `Ξ_p`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsFeature

open Sarkozy.OpsCore Sarkozy.SignedGram Sarkozy.PrimeGram Sarkozy.MiddleRecords
  Sarkozy.Envelopes Sarkozy.PartV

/-- OPS-L's projected arm `A₃° = A₃ − GA` (`A3Perp`, in `𝒦₁₂` by `A3_perp`). -/
noncomputable def A3c {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    (F → ℝ) → (Fin 3 → F) → ℝ :=
  fun h x => A3 h x - GA h x

section Chart

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

/-- The block star with a general third arm: the prime stars `lFormY` on the singleton sectors. -/
noncomputable def foldLeadY (hne : MiddleNonempty pr) (t : ℝ) (x₀ : ∀ i, Ai pr i)
    (Y : ∀ i, (ZMod (pr i) → ℝ) → (Fin 3 → ZMod (pr i)) → ℝ)
    (φ ψ : (∀ i, Ai pr i) → ℝ) : ℝ :=
  singForm (mP hne) x₀ (fun i => lFormY (mP hne i) t (Y i)) φ ψ

theorem foldLead_eq_Y (hne : MiddleNonempty pr) (t : ℝ) (x₀ : ∀ i, Ai pr i)
    (φ ψ : (∀ i, Ai pr i) → ℝ) : foldLead hne t x₀ φ ψ = foldLeadY hne t x₀ (fun _ => A3) φ ψ :=
  rfl

theorem foldLeadC_eq_Y (hne : MiddleNonempty pr) (t : ℝ) (x₀ : ∀ i, Ai pr i)
    (φ ψ : (∀ i, Ai pr i) → ℝ) :
    foldLeadC hne t x₀ φ ψ = foldLeadY hne t x₀ (fun _ => A3c) φ ψ :=
  rfl

theorem foldLeadY_expand (hne : MiddleNonempty pr) (t : ℝ) (x₀ : ∀ i, Ai pr i)
    (Y : ∀ i, (ZMod (pr i) → ℝ) → (Fin 3 → ZMod (pr i)) → ℝ) (φ ψ : (∀ i, Ai pr i) → ℝ) :
    foldLeadY hne t x₀ Y φ ψ = ∑ x, ∑ y, φ x * ψ y *
      foldLeadY hne t x₀ Y (EnvelopeSteps.delta x) (EnvelopeSteps.delta y) := by
  unfold foldLeadY singForm
  exact blockForm_expand (fun i => mP hne i) t Y
    (fun j => Matrix.of fun z a => SP (mP hne) (sing j) (Function.update x₀ j a) z)
    (fun j => comp1 (mP hne) x₀ j) (fun j φ a => comp1_eq_sum (mP hne) x₀ j φ a) φ ψ

/-- The block star as a bilinear map. -/
noncomputable def foldBil (hne : MiddleNonempty pr) (t : ℝ) (x₀ : ∀ i, Ai pr i)
    (Y : ∀ i, (ZMod (pr i) → ℝ) → (Fin 3 → ZMod (pr i)) → ℝ) :
    ((∀ i, Ai pr i) → ℝ) →ₗ[ℝ] ((∀ i, Ai pr i) → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun φ ψ => ∑ x, ∑ y, φ x * ψ y *
      foldLeadY hne t x₀ Y (EnvelopeSteps.delta x) (EnvelopeSteps.delta y))
    (fun φ φ' ψ => by
      simp only [Pi.add_apply, add_mul, sum_add_distrib])
    (fun c φ ψ => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring)
    (fun φ ψ ψ' => by
      simp only [Pi.add_apply, mul_add, add_mul, sum_add_distrib])
    (fun c φ ψ => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring)

theorem foldBil_apply (hne : MiddleNonempty pr) (t : ℝ) (x₀ : ∀ i, Ai pr i)
    (Y : ∀ i, (ZMod (pr i) → ℝ) → (Fin 3 → ZMod (pr i)) → ℝ) (φ ψ : (∀ i, Ai pr i) → ℝ) :
    foldBil hne t x₀ Y φ ψ = foldLeadY hne t x₀ Y φ ψ :=
  (foldLeadY_expand hne t x₀ Y φ ψ).symm

/-- The block law `m_{0,𝔅} = ∏_p mP_p`. -/
noncomputable def mB (hne : MiddleNonempty pr) : (∀ i, Ai pr i) → ℝ :=
  fun x => ∏ i, mP hne i (x i)

theorem ip_mB (hne : MiddleNonempty pr) (φ ψ : (∀ i, Ai pr i) → ℝ) :
    Sarkozy.NormBoundsPaper2.ip (mP hne) φ ψ = EnvelopeSteps.ip (mB hne) φ ψ := by
  unfold Sarkozy.NormBoundsPaper2.ip EnvelopeSteps.ip mB
  simp only [dotProduct, mulVec_diagonal, Sarkozy.Mixing.prodW]
  exact sum_congr rfl fun x _ => by ring

/-- The operator `w⁻¹ L^{(Y)}_{t,𝔅}` in `L²(m_{0,𝔅})` (OPS-L's `opOfForm`). -/
noncomputable def leadOpY (hne : MiddleNonempty pr) (t : ℝ) (x₀ : ∀ i, Ai pr i)
    (Y : ∀ i, (ZMod (pr i) → ℝ) → (Fin 3 → ZMod (pr i)) → ℝ) (w : ℝ) :
    ((∀ i, Ai pr i) → ℝ) →ₗ[ℝ] ((∀ i, Ai pr i) → ℝ) :=
  opOfForm (mB hne) (fun f g => (w⁻¹ • foldBil hne t x₀ Y) f g)

end Chart

/-- **Routing a change of the leading star into the remainder**: `‖Δ̂ − L‖ ≤ ρ`, `‖L − L°‖ ≤ e`
give `‖Δ̂ − L°‖ ≤ ρ + e` (the forms of `LeadOK`'s `hE`). -/
theorem formLE_route {O : Type*} [Fintype O] {m : O → ℝ} {Δ L Lc : (O → ℝ) →ₗ[ℝ] (O → ℝ)}
    {ρ e : ℝ} (h1 : FormLE m (Δ - L) ρ) (h2 : FormLE m (L - Lc) e) :
    FormLE m (Δ - Lc) (ρ + e) := by
  refine ⟨add_nonneg h1.1 h2.1, fun F G => ?_⟩
  have hsplit : (Δ - Lc) G = (Δ - L) G + (L - Lc) G := by
    simp only [LinearMap.sub_apply]
    abel
  rw [hsplit, EnvelopeSteps.ip_add_right]
  calc |EnvelopeSteps.ip m F ((Δ - L) G) + EnvelopeSteps.ip m F ((L - Lc) G)|
      ≤ |EnvelopeSteps.ip m F ((Δ - L) G)| + |EnvelopeSteps.ip m F ((L - Lc) G)| :=
        abs_add_le _ _
    _ ≤ ρ * Real.sqrt (EnvelopeSteps.ip m F F) * Real.sqrt (EnvelopeSteps.ip m G G) +
        e * Real.sqrt (EnvelopeSteps.ip m F F) * Real.sqrt (EnvelopeSteps.ip m G G) :=
        add_le_add (h1.2 F G) (h2.2 F G)
    _ = (ρ + e) * Real.sqrt (EnvelopeSteps.ip m F F) * Real.sqrt (EnvelopeSteps.ip m G G) := by
        ring

section Main

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

/-- **The chart's leading star at a fold block** (`hLb` with `A₃°`; the change into the
remainder). With OPS-L's bound `|L_{t,𝔅}| ≤ ℓ'` (`hℓ`) and `foldLead_chart_le`
(`δ = 2|1−t|JΓ^{1/2}`), for `L = w⁻¹ L_{t,𝔅}` and `L° = w⁻¹ L°_{t,𝔅}` as operators on
`L²(m_{0,𝔅})`: `‖L − L°‖ ≤ w⁻¹δ`, `‖L°‖ ≤ w⁻¹(ℓ' + δ)`, and the kernel of `L°` is the star form
with the paper's `Ξ_p` (third arm `A₃°`), `c_p = w⁻¹ r_p`. -/
theorem chart_lead (hne : MiddleNonempty pr) (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    {J Γ : ℝ} (hJnn : 0 ≤ J)
    (hJ : ∀ i, jFqr (F := ZMod (pr i)) (Real.sqrt (rho01Sq (F := ZMod (pr i)))) ≤ J)
    (hΓ : ∀ i, gammaP pr i ≤ Γ) (x₀ : ∀ i, Ai pr i) {ℓ' : ℝ} (hℓ0 : 0 ≤ ℓ')
    (hℓ : ∀ φ ψ, |foldLead hne tlaw x₀ φ ψ| ≤
      ℓ' * Real.sqrt (Sarkozy.NormBoundsPaper2.ip (mP hne) φ φ) *
        Real.sqrt (Sarkozy.NormBoundsPaper2.ip (mP hne) ψ ψ))
    {w : ℝ} (hw : 0 < w) :
    FormLE (mB hne) (leadOpY hne tlaw x₀ (fun _ => A3) w - leadOpY hne tlaw x₀ (fun _ => A3c) w)
        (w⁻¹ * (2 * |1 - tlaw| * J * Real.sqrt Γ)) ∧
      FormLE (mB hne) (leadOpY hne tlaw x₀ (fun _ => A3c) w)
        (w⁻¹ * (ℓ' + 2 * |1 - tlaw| * J * Real.sqrt Γ)) ∧
      ∀ x y, EnvelopeSteps.kern (mB hne) (leadOpY hne tlaw x₀ (fun _ => A3c) w) x y =
        (∑ j, (w⁻¹ * (Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹) •
          (((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ •
              ((Matrix.of fun z a => SP (mP hne) (sing j) (Function.update x₀ j a) z) *
                XiM (mP hne j) A3c)) * foldStar (F := ZMod (pr j)) *
            ((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ •
              ((Matrix.of fun z a => SP (mP hne) (sing j) (Function.update x₀ j a) z) *
                XiM (mP hne j) A3c))ᴴ)) x y := by
  set δ := 2 * |1 - tlaw| * J * Real.sqrt Γ with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hwi : 0 ≤ w⁻¹ := inv_nonneg.mpr hw.le
  set sE : ((∀ i, Ai pr i) → ℝ) → ℝ := fun φ => Real.sqrt (EnvelopeSteps.ip (mB hne) φ φ)
    with hsE
  have hsE0 : ∀ φ, 0 ≤ sE φ := fun φ => Real.sqrt_nonneg _
  have hLE : ∀ φ ψ, |foldLead hne tlaw x₀ φ ψ| ≤ ℓ' * sE φ * sE ψ := by
    intro φ ψ
    have := hℓ φ ψ
    rwa [ip_mB, ip_mB] at this
  have hdE : ∀ φ ψ, |foldLead hne tlaw x₀ φ ψ - foldLeadC hne tlaw x₀ φ ψ| ≤ δ * sE φ * sE ψ := by
    intro φ ψ
    have := foldLead_chart_le hne h3 h19 tlaw hJnn hJ hΓ x₀ φ ψ
    rwa [ip_mB, ip_mB] at this
  have hCE : ∀ φ ψ, |foldLeadC hne tlaw x₀ φ ψ| ≤ (ℓ' + δ) * sE φ * sE ψ := by
    intro φ ψ
    have e : foldLeadC hne tlaw x₀ φ ψ = foldLead hne tlaw x₀ φ ψ -
        (foldLead hne tlaw x₀ φ ψ - foldLeadC hne tlaw x₀ φ ψ) := by ring
    rw [e]
    calc _ ≤ |foldLead hne tlaw x₀ φ ψ| +
          |foldLead hne tlaw x₀ φ ψ - foldLeadC hne tlaw x₀ φ ψ| := abs_sub _ _
      _ ≤ ℓ' * sE φ * sE ψ + δ * sE φ * sE ψ := add_le_add (hLE φ ψ) (hdE φ ψ)
      _ = (ℓ' + δ) * sE φ * sE ψ := by ring
  -- the two operators
  have hβL : ∀ f g, (w⁻¹ • foldBil hne tlaw x₀ (fun _ => A3)) f g =
      w⁻¹ * foldLead hne tlaw x₀ f g := fun f g => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, foldBil_apply, ← foldLead_eq_Y]
  have hβC : ∀ f g, (w⁻¹ • foldBil hne tlaw x₀ (fun _ => A3c)) f g =
      w⁻¹ * foldLeadC hne tlaw x₀ f g := fun f g => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, foldBil_apply, ← foldLeadC_eq_Y]
  have hbdL : ∀ f g, |(w⁻¹ • foldBil hne tlaw x₀ (fun _ => A3)) f g| ≤
      (w⁻¹ * ℓ') * Real.sqrt (EnvelopeSteps.ip (mB hne) f f) *
        Real.sqrt (EnvelopeSteps.ip (mB hne) g g) := by
    intro f g
    rw [hβL, abs_mul, abs_of_nonneg hwi]
    have := mul_le_mul_of_nonneg_left (hLE f g) hwi
    simp only [hsE] at this
    linarith
  have hbdC : ∀ f g, |(w⁻¹ • foldBil hne tlaw x₀ (fun _ => A3c)) f g| ≤
      (w⁻¹ * (ℓ' + δ)) * Real.sqrt (EnvelopeSteps.ip (mB hne) f f) *
        Real.sqrt (EnvelopeSteps.ip (mB hne) g g) := by
    intro f g
    rw [hβC, abs_mul, abs_of_nonneg hwi]
    have := mul_le_mul_of_nonneg_left (hCE f g) hwi
    simp only [hsE] at this
    linarith
  have ipL : ∀ f g, EnvelopeSteps.ip (mB hne) f (leadOpY hne tlaw x₀ (fun _ => A3) w g) =
      w⁻¹ * foldLead hne tlaw x₀ f g := fun f g => by
    unfold leadOpY
    rw [ip_opOfForm _ hbdL, hβL]
  have ipC : ∀ f g, EnvelopeSteps.ip (mB hne) f (leadOpY hne tlaw x₀ (fun _ => A3c) w g) =
      w⁻¹ * foldLeadC hne tlaw x₀ f g := fun f g => by
    unfold leadOpY
    rw [ip_opOfForm _ hbdC, hβC]
  refine ⟨⟨by positivity, fun F G => ?_⟩, ⟨by positivity, fun F G => ?_⟩, fun x y => ?_⟩
  · rw [LinearMap.sub_apply, EnvelopeSteps.ip_sub_right, ipL, ipC, ← mul_sub, abs_mul,
      abs_of_nonneg hwi]
    have := mul_le_mul_of_nonneg_left (hdE F G) hwi
    simp only [hsE] at this
    linarith
  · rw [ipC, abs_mul, abs_of_nonneg hwi]
    have := mul_le_mul_of_nonneg_left (hCE F G) hwi
    simp only [hsE] at this
    linarith
  · have hF : ∀ j, ringChar (ZMod (pr j)) ≠ 2 := fun j => (primeHyps h3 h19 j).1
    have h3' : ∀ j, Fintype.card (ZMod (pr j)) % 4 = 3 := fun j => (primeHyps h3 h19 j).2.1
    exact kern_block_lead_starSum hF h3' (fun j => mP hne j) (fun _ => A3c)
      (fun j => Matrix.of fun z a => SP (mP hne) (sing j) (Function.update x₀ j a) z)
      (fun j => comp1 (mP hne) x₀ j) (fun j φ a => comp1_eq_sum (mP hne) x₀ j φ a) w⁻¹ (mB hne)
      _ (fun f g => by rw [ipC, foldLeadC_eq_Y]; rfl) x y

end Main

/-! ## The singleton-label columns of the chart's sector maps -/

section Columns

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

theorem xiF_castSucc {F : Type} [Field F] [Fintype F] [DecidableEq F] (m : (Fin 3 → F) → ℝ)
    (Y : (F → ℝ) → (Fin 3 → F) → ℝ) (a : Fin 3) : xiF m Y (Fin.castSucc a) = adj m (Vc a) := by
  fin_cases a <;> rfl

/-- The singleton-sector placement: `C_j(x, b) = ([b = x_j] − m_j(x_j)) ∏_{i ≠ j} m_i(x_i)`. -/
theorem SP_sing_entry (hne : MiddleNonempty pr) (x₀ : ∀ i, Ai pr i) (j : ι) (b : Ai pr j)
    (x : ∀ i, Ai pr i) :
    SP (mP hne) (sing j) (Function.update x₀ j b) x =
      ((if b = x j then 1 else 0) - mP hne j (x j)) * ∏ i ∈ univ.erase j, mP hne i (x i) := by
  unfold SP
  rw [Sarkozy.IndexSupport.piKron_apply, ← Finset.mul_prod_erase univ _ (mem_univ j)]
  congr 1
  · simp only [sing, decide_true, Mixing.wProj, Bool.false_eq_true, ↓reduceIte,
      Function.update_self,
      Matrix.sub_apply, Matrix.one_apply, Mixing.avgMatrix]
  · refine prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := ne_of_mem_erase hi
    simp only [sing, hij, decide_false, Mixing.wProj, Bool.false_eq_true, ↓reduceIte,
      Mixing.avgMatrix]

/-- The coordinate adjoint at a point mass: `V_a^{*m} δ_b = p m(b) (δ_{b_a} − 1/p)`. -/
theorem adj_Vc_delta {F : Type} [Field F] [Fintype F] [DecidableEq F] (m : (Fin 3 → F) → ℝ)
    (a : Fin 3) (b : Fin 3 → F) (z : F) :
    adj m (Vc a) (EnvelopeSteps.delta b) z =
      (Fintype.card F : ℝ) * m b * ((if b a = z then 1 else 0) - (Fintype.card F : ℝ)⁻¹) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hmip : ∀ s, mip m (Vc a (PrimeGram.delta s)) (EnvelopeSteps.delta b) =
      m b * (if b a = s then 1 else 0) := by
    intro s
    simp only [mip, Vc, PrimeGram.delta, EnvelopeSteps.delta, mul_ite, mul_one, mul_zero,
      sum_ite_eq', mem_univ, ↓reduceIte]
  simp only [adj, cen, hmip]
  have hs : ∑ s, (Fintype.card F : ℝ) * (m b * (if b a = s then 1 else 0)) =
      (Fintype.card F : ℝ) * m b := by
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
  rw [hs]
  by_cases h : b a = z
  · simp only [h, ↓reduceIte]; field_simp
  · simp only [h, ↓reduceIte]; field_simp

/-- Integrals of the product law: `∑_x ∏_i h_i(x_i) = ∏_i ∑_c h_i(c)`. -/
theorem sum_prod_coords (h : ∀ i, Ai pr i → ℝ) :
    ∑ x : (∀ i, Ai pr i), ∏ i, h i (x i) = ∏ i, ∑ c, h i c :=
  (Fintype.prod_sum h).symm

/-- One coordinate of the block law: `∑_x m_{0,𝔅}(x) G(x_j) = ∑_b m_j(b) G(b)`. -/
theorem sum_mB_coord (hne : MiddleNonempty pr) (j : ι) (G : Ai pr j → ℝ) :
    ∑ x, mB hne x * G (x j) = ∑ b, mP hne j b * G b := by
  set h : ∀ i, Ai pr i → ℝ :=
    Function.update (fun i c => mP hne i c) j (fun c => mP hne j c * G c) with hh
  have e1 : ∀ x : (∀ i, Ai pr i), mB hne x * G (x j) = ∏ i, h i (x i) := by
    intro x
    unfold mB
    rw [← Finset.mul_prod_erase univ _ (mem_univ j), ← Finset.mul_prod_erase univ _ (mem_univ j)]
    rw [hh, Function.update_self]
    have : ∏ i ∈ univ.erase j, Function.update (fun i c => mP hne i c) j
        (fun c => mP hne j c * G c) i (x i) = ∏ i ∈ univ.erase j, mP hne i (x i) :=
      prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)]
    rw [this]
    ring
  simp only [e1]
  rw [sum_prod_coords, ← Finset.mul_prod_erase univ _ (mem_univ j), hh, Function.update_self]
  have : ∏ i ∈ univ.erase j, ∑ c, Function.update (fun i c => mP hne i c) j
      (fun c => mP hne j c * G c) i c = 1 :=
    prod_eq_one fun i hi => by
      rw [Function.update_of_ne (ne_of_mem_erase hi)]; exact mP_total hne i
  rw [this, mul_one]

/-- Two coordinates of the block law (`j ≠ k`): the product of the one-coordinate integrals. -/
theorem sum_mB_two (hne : MiddleNonempty pr) {j k : ι} (hjk : j ≠ k) (G : Ai pr j → ℝ)
    (H : Ai pr k → ℝ) :
    ∑ x, mB hne x * (G (x j) * H (x k)) = (∑ b, mP hne j b * G b) * ∑ b, mP hne k b * H b := by
  set h1 : ∀ i, Ai pr i → ℝ :=
    Function.update (fun i c => mP hne i c) j (fun c => mP hne j c * G c) with hh1
  set h : ∀ i, Ai pr i → ℝ := Function.update h1 k (fun c => mP hne k c * H c) with hh
  have hk1 : h1 k = fun c => mP hne k c := by rw [hh1, Function.update_of_ne hjk.symm]
  have e1 : ∀ x : (∀ i, Ai pr i), mB hne x * (G (x j) * H (x k)) = ∏ i, h i (x i) := by
    intro x
    unfold mB
    rw [← Finset.mul_prod_erase univ _ (mem_univ k), ← Finset.mul_prod_erase univ _ (mem_univ k),
      hh, Function.update_self]
    have hj : j ∈ univ.erase k := mem_erase.2 ⟨hjk, mem_univ j⟩
    rw [← Finset.mul_prod_erase _ _ hj, ← Finset.mul_prod_erase (univ.erase k) _ hj,
      Function.update_of_ne hjk, hh1, Function.update_self]
    have : ∏ i ∈ (univ.erase k).erase j, Function.update (Function.update (fun i c => mP hne i c) j
        (fun c => mP hne j c * G c)) k (fun c => mP hne k c * H c) i (x i) =
        ∏ i ∈ (univ.erase k).erase j, mP hne i (x i) :=
      prod_congr rfl fun i hi => by
        have hij : i ≠ j := ne_of_mem_erase hi
        have hik : i ≠ k := ne_of_mem_erase (mem_of_mem_erase hi)
        rw [Function.update_of_ne hik, Function.update_of_ne hij]
    rw [this]
    ring
  simp only [e1]
  rw [sum_prod_coords, ← Finset.mul_prod_erase univ _ (mem_univ k), hh, Function.update_self]
  have hj : j ∈ univ.erase k := mem_erase.2 ⟨hjk, mem_univ j⟩
  rw [← Finset.mul_prod_erase _ _ hj, Function.update_of_ne hjk, hh1, Function.update_self]
  have : ∏ i ∈ (univ.erase k).erase j, ∑ c, Function.update (Function.update
      (fun i c => mP hne i c) j (fun c => mP hne j c * G c)) k (fun c => mP hne k c * H c) i c =
      1 :=
    prod_eq_one fun i hi => by
      have hij : i ≠ j := ne_of_mem_erase hi
      have hik : i ≠ k := ne_of_mem_erase (mem_of_mem_erase hi)
      rw [Function.update_of_ne hik, Function.update_of_ne hij]; exact mP_total hne i
  rw [this, mul_one]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- Each coordinate of a prime law is uniform (`m0_coord`). -/
theorem mP_coord (hne : MiddleNonempty pr) (j : ι) (a : Fin 3) (g : ZMod (pr j) → ℝ) :
    ∑ b, mP hne j b * g (b a) = (∑ c, g c) / (Fintype.card (ZMod (pr j)) : ℝ) :=
  Sarkozy.SignedComponents.m0_coord (hne.F2 j) a g

/-- The singleton-sector placement as a matrix. -/
noncomputable def CXi (hne : MiddleNonempty pr) (x₀ : ∀ i, Ai pr i) (j : ι) :
    Matrix (∀ i, Ai pr i) (Ai pr j) ℝ :=
  Matrix.of fun z a => SP (mP hne) (sing j) (Function.update x₀ j a) z

/-- The singleton-label arm functions: `y_{a,j,z}(x) = √p (δ_{x_{j,a}, z} − 1/p)`, the lift by
`V_a` of the orthonormal basis vector `√p (δ_z − 1/p)` of `H₀` at the prime `j`. -/
noncomputable def ySing (j : ι) (a : Fin 3) (z : ZMod (pr j)) (x : ∀ i, Ai pr i) : ℝ :=
  Real.sqrt (Fintype.card (ZMod (pr j))) *
    ((if x j a = z then 1 else 0) - (Fintype.card (ZMod (pr j)) : ℝ)⁻¹)

/-- **The singleton-label columns of the chart's sector maps** (`chart_lead`'s
`Ξ_j = p^{-1/2} C_j XiM_j`): `Ξ_j(x, (a, z)) = m_{0,𝔅}(x) y_{a,j,z}(x)` for `a = 0, 1, 2`. -/
theorem chartXi_singleton (hne : MiddleNonempty pr) (x₀ : ∀ i, Ai pr i) (j : ι) (a : Fin 3)
    (Y : (ZMod (pr j) → ℝ) → (Fin 3 → ZMod (pr j)) → ℝ) (x : ∀ i, Ai pr i) (z : ZMod (pr j)) :
    ((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ • (CXi hne x₀ j * XiM (mP hne j) Y))
        x (Fin.castSucc a, z) = mB hne x * ySing j a z x := by
  set q : ℝ := (Fintype.card (ZMod (pr j)) : ℝ) with hqdef
  have hq : 0 < q := by rw [hqdef]; exact_mod_cast Fintype.card_pos
  set R := ∏ i ∈ univ.erase j, mP hne i (x i) with hR
  have hmean : ∑ b : Ai pr j, mP hne j b * ((if b a = z then 1 else 0) - q⁻¹) = 0 := by
    rw [mP_coord hne j a (fun c => (if c = z then 1 else 0) - q⁻¹)]
    simp only [sum_sub_distrib, sum_ite_eq', mem_univ, ↓reduceIte, sum_const, card_univ,
      nsmul_eq_mul]
    rw [← hqdef, mul_inv_cancel₀ hq.ne', sub_self, zero_div]
  have hmB : mB hne x = mP hne j (x j) * R := by
    unfold mB; rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
  rw [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  simp only [CXi, Matrix.of_apply, XiM, xiF_castSucc, adj_Vc_delta, SP_sing_entry]
  have e : ∀ b : Ai pr j, ((if b = x j then 1 else 0) - mP hne j (x j)) * R *
      (q * mP hne j b * ((if b a = z then 1 else 0) - q⁻¹)) =
      (if b = x j then R * q * (mP hne j b * ((if b a = z then 1 else 0) - q⁻¹)) else 0) -
        mP hne j (x j) * R * q * (mP hne j b * ((if b a = z then 1 else 0) - q⁻¹)) := by
    intro b
    split_ifs <;> ring
  simp only [← hqdef, ← hR, e, sum_sub_distrib, sum_ite_eq', mem_univ, ↓reduceIte, ← mul_sum,
    hmean, mul_zero, sub_zero, hmB, ySing]
  have hs2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have hs0 : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  field_simp
  rw [hs2]
  ring

/-- The coordinate `x_a = (x_{j,a})_j` of a block point. -/
def piA (a : Fin 3) (x : ∀ i, Ai pr i) : ∀ i, ZMod (pr i) := fun i => x i a

omit [Fintype ι] [DecidableEq ι] in
theorem ySing_mean (hne : MiddleNonempty pr) (j : ι) (a : Fin 3) (z : ZMod (pr j)) :
    ∑ b : Ai pr j, mP hne j b *
      (Real.sqrt (Fintype.card (ZMod (pr j))) *
        ((if b a = z then 1 else 0) - (Fintype.card (ZMod (pr j)) : ℝ)⁻¹)) = 0 := by
  have hq : (0 : ℝ) < Fintype.card (ZMod (pr j)) := by exact_mod_cast Fintype.card_pos
  have e : ∀ b : Ai pr j, mP hne j b * (Real.sqrt (Fintype.card (ZMod (pr j))) *
      ((if b a = z then 1 else 0) - (Fintype.card (ZMod (pr j)) : ℝ)⁻¹)) =
      Real.sqrt (Fintype.card (ZMod (pr j))) * (mP hne j b *
        ((fun c => (if c = z then 1 else 0) - (Fintype.card (ZMod (pr j)) : ℝ)⁻¹) (b a))) :=
    fun b => by ring
  simp only [e, ← mul_sum]
  have hc := mP_coord hne j a
    (fun c => (if c = z then 1 else 0) - (Fintype.card (ZMod (pr j)) : ℝ)⁻¹)
  rw [hc]
  simp only [sum_sub_distrib, sum_ite_eq', mem_univ, ↓reduceIte, sum_const, card_univ,
    nsmul_eq_mul]
  rw [mul_inv_cancel₀ hq.ne', sub_self, zero_div, mul_zero]

/-- **The singleton-label arms are centred** (in `L²(m_{0,𝔅})`). -/
theorem ySing_centred (hne : MiddleNonempty pr) (j : ι) (a : Fin 3) (z : ZMod (pr j)) :
    EnvelopeSteps.ip (mB hne) (ySing j a z) (fun _ => 1) = 0 := by
  unfold EnvelopeSteps.ip ySing
  simp only [mul_one]
  rw [sum_mB_coord hne j (fun b => Real.sqrt (Fintype.card (ZMod (pr j))) *
    ((if b a = z then 1 else 0) - (Fintype.card (ZMod (pr j)) : ℝ)⁻¹))]
  exact ySing_mean hne j a z

/-- **The singleton-label arms of different sectors are orthogonal.** -/
theorem ySing_orth (hne : MiddleNonempty pr) (a : Fin 3) {j k : ι} (hjk : j ≠ k)
    (z : ZMod (pr j)) (z' : ZMod (pr k)) :
    EnvelopeSteps.ip (mB hne) (ySing j a z) (ySing k a z') = 0 := by
  unfold EnvelopeSteps.ip ySing
  rw [sum_mB_two hne hjk (fun b => Real.sqrt (Fintype.card (ZMod (pr j))) *
    ((if b a = z then 1 else 0) - (Fintype.card (ZMod (pr j)) : ℝ)⁻¹))
    (fun b => Real.sqrt (Fintype.card (ZMod (pr k))) *
    ((if b a = z' then 1 else 0) - (Fintype.card (ZMod (pr k)) : ℝ)⁻¹)), ySing_mean, zero_mul]

/-- **The singleton-label arms form a contraction**: `‖∑_z c_z y_{a,j,z}‖² ≤ ∑_z c_z²`. -/
theorem ySing_contraction (hne : MiddleNonempty pr) (j : ι) (a : Fin 3)
    (c : ZMod (pr j) → ℝ) :
    EnvelopeSteps.ip (mB hne) (∑ z, c z • ySing j a z) (∑ z, c z • ySing j a z) ≤
      ∑ z, c z ^ 2 := by
  set q : ℝ := (Fintype.card (ZMod (pr j)) : ℝ) with hqdef
  have hq : 0 < q := by rw [hqdef]; exact_mod_cast Fintype.card_pos
  set cbar := q⁻¹ * ∑ z, c z with hcbar
  have hsum : ∀ x : ∀ i, Ai pr i, (∑ z, c z • ySing j a z) x =
      Real.sqrt q * (c (x j a) - cbar) := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ySing, ← hqdef]
    have : ∑ z, c z * (Real.sqrt q * ((if x j a = z then 1 else 0) - q⁻¹)) =
        Real.sqrt q * (∑ z, (if x j a = z then c z else 0) - q⁻¹ * ∑ z, c z) := by
      rw [mul_sub, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun z _ => ?_
      split_ifs <;> ring
    rw [this, sum_ite_eq]
    simp only [mem_univ, ↓reduceIte, hcbar]
  unfold EnvelopeSteps.ip
  simp only [hsum]
  rw [sum_mB_coord hne j
    (fun b => Real.sqrt q * (c (b a) - cbar) * (Real.sqrt q * (c (b a) - cbar)))]
  have e : ∀ b : Ai pr j, mP hne j b * (Real.sqrt q * (c (b a) - cbar) *
      (Real.sqrt q * (c (b a) - cbar))) =
      q * (mP hne j b * (fun w => (c w - cbar) ^ 2) (b a)) := by
    intro b
    have hs : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
    calc _ = (Real.sqrt q * Real.sqrt q) * (mP hne j b * (c (b a) - cbar) ^ 2) := by ring
      _ = _ := by rw [hs]
  simp only [e, ← mul_sum]
  have hc := mP_coord hne j a (fun w => (c w - cbar) ^ 2)
  rw [hc, ← hqdef, mul_div_cancel₀ _ hq.ne']
  -- `∑ (c − c̄)² = ∑ c² − q c̄² ≤ ∑ c²`
  have e2 : ∑ w, (c w - cbar) ^ 2 = ∑ w, c w ^ 2 - q * cbar ^ 2 := by
    have h1 : ∑ w, (c w - cbar) ^ 2 = ∑ w, c w ^ 2 - 2 * cbar * ∑ w, c w +
        ∑ _w : ZMod (pr j), cbar ^ 2 := by
      rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun w _ => by ring
    rw [h1, sum_const, card_univ, nsmul_eq_mul, ← hqdef]
    have h2 : ∑ w, c w = q * cbar := by rw [hcbar, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
    rw [h2]
    ring
  rw [e2]
  have : 0 ≤ q * cbar ^ 2 := by positivity
  linarith

omit [DecidableEq ι] in
theorem mB_nonneg (hne : MiddleNonempty pr) (x : ∀ i, Ai pr i) : 0 ≤ mB hne x :=
  prod_nonneg fun i _ => mP_nonneg hne i (x i)

/-- **`hUa` for the singleton labels at a fold block, unconditionally** (`hdom_of_units`, labels
`a = 0, 1, 2`): with the unit lift `U(a,a) = P_a − 𝒥` as the conditional expectations of
`m_{0,𝔅}` (`uOp`) and the chart's sector maps `Ξ_j = p_j^{-1/2} C_j XiM_j` of `chart_lead`,
`U(a,a) ⪰ ∑_j Ξ_{j,a} Ξ_{j,a}ᵀ` as kernels. -/
theorem hUa_singleton_chart (hne : MiddleNonempty pr) (x₀ : ∀ i, Ai pr i) (a : Fin 3)
    (Y : ∀ j, (ZMod (pr j) → ℝ) → (Fin 3 → ZMod (pr j)) → ℝ) :
    (Matrix.of fun x x' : (∀ i, Ai pr i) =>
      EnvelopeSteps.kern (mB hne) (uOp (mB hne) (piA a)) x x' -
      ∑ j, ∑ z, ((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ • (CXi hne x₀ j * XiM (mP hne j) (Y j)))
          x (Fin.castSucc a, z) *
        ((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ • (CXi hne x₀ j * XiM (mP hne j) (Y j)))
          x' (Fin.castSucc a, z)).PosSemidef := by
  have := singleton_realized (mB_nonneg hne) (piA a) (fun j z => ySing j a z)
    (fun j z => ⟨fun w => Real.sqrt (Fintype.card (ZMod (pr j))) *
      ((if w j = z then 1 else 0) - (Fintype.card (ZMod (pr j)) : ℝ)⁻¹), rfl⟩)
    (fun j z => ySing_centred hne j a z)
    (fun j k hjk z z' => ySing_orth hne a hjk z z')
    (fun j c => ySing_contraction hne j a c)
    (fun j => Matrix.of fun x z =>
      ((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ • (CXi hne x₀ j * XiM (mP hne j) (Y j)))
        x (Fin.castSucc a, z))
    (fun j x z => by simp only [Matrix.of_apply]; exact chartXi_singleton hne x₀ j a (Y j) x z)
  simpa only [Matrix.of_apply] using this

/-! ## The label-`3` columns of the chart's sector maps -/

/-- A feature adjoint at a point mass: `S^{*m} δ_b = p m(b) (S δ_· (b) − mean)`. -/
theorem adj_delta {F : Type} [Field F] [Fintype F] [DecidableEq F] (m : (Fin 3 → F) → ℝ)
    (S : (F → ℝ) → (Fin 3 → F) → ℝ) (b : Fin 3 → F) (z : F) :
    adj m S (EnvelopeSteps.delta b) z = (Fintype.card F : ℝ) * m b *
      (S (PrimeGram.delta z) b - (Fintype.card F : ℝ)⁻¹ * ∑ s, S (PrimeGram.delta s) b) := by
  have hmip : ∀ s, mip m (S (PrimeGram.delta s)) (EnvelopeSteps.delta b) =
      m b * S (PrimeGram.delta s) b := by
    intro s
    simp only [mip, EnvelopeSteps.delta, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
      ↓reduceIte]
  simp only [adj, cen, hmip, ← mul_sum]
  ring

/-- The centred label-`3` kernel at one prime: `K(c₁, c₂; z) = (A₃° δ_z)(c₁, c₂) − mean_s`. -/
noncomputable def K3 {F : Type} [Field F] [Fintype F] [DecidableEq F] (c1 c2 z : F) : ℝ :=
  (A3op (PrimeGram.delta z) c1 c2 - (uA (PrimeGram.delta z) c1 + vA (PrimeGram.delta z) c2)) -
    (Fintype.card F : ℝ)⁻¹ * ∑ s, (A3op (PrimeGram.delta s) c1 c2 -
      (uA (PrimeGram.delta s) c1 + vA (PrimeGram.delta s) c2))

/-- The label-`3` arm functions: `y_{3,j,z}(x) = p (K(x_{j,1}, x_{j,2}; z) − E_{m_j} K(·; z))`, the
lift of `√p (δ_z − 1/p)` by `A₃°/r` at the prime `j`. -/
noncomputable def yThree (hne : MiddleNonempty pr) (j : ι) (z : ZMod (pr j))
    (x : ∀ i, Ai pr i) : ℝ :=
  (Fintype.card (ZMod (pr j)) : ℝ) *
    (K3 (x j 1) (x j 2) z - ∑ b : Ai pr j, mP hne j b * K3 (b 1) (b 2) z)

/-- **The label-`3` columns of the chart's sector maps**: `Ξ_j(x, (3, z)) = m_{0,𝔅}(x) y_{3,j,z}(x)`
(third arm `A₃°`). -/
theorem chartXi_three (hne : MiddleNonempty pr) (x₀ : ∀ i, Ai pr i) (j : ι)
    (x : ∀ i, Ai pr i) (z : ZMod (pr j)) :
    ((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ • (CXi hne x₀ j * XiM (mP hne j) A3c))
        x (3, z) = mB hne x * yThree hne j z x := by
  set q : ℝ := (Fintype.card (ZMod (pr j)) : ℝ) with hqdef
  have hq : 0 < q := by rw [hqdef]; exact_mod_cast Fintype.card_pos
  set R := ∏ i ∈ univ.erase j, mP hne i (x i) with hR
  have hmB : mB hne x = mP hne j (x j) * R := by
    unfold mB; rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
  have hK : ∀ b : Ai pr j, A3c (PrimeGram.delta z) b -
      q⁻¹ * ∑ s, A3c (PrimeGram.delta s) b = K3 (b 1) (b 2) z := fun b => rfl
  have hx3 : ∀ (f : (Fin 3 → ZMod (pr j)) → ℝ) (w : ZMod (pr j)),
      xiF (mP hne j) A3c 3 f w = Real.sqrt q * adj (mP hne j) A3c f w := fun f w => rfl
  rw [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  simp only [CXi, Matrix.of_apply, XiM, hx3, adj_delta, SP_sing_entry, ← hqdef, hK]
  have hs0 : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have e : ∀ b : Ai pr j, ((if b = x j then 1 else 0) - mP hne j (x j)) * R *
      (Real.sqrt q * (q * mP hne j b * K3 (b 1) (b 2) z)) =
      (if b = x j then R * Real.sqrt q * q * (mP hne j b * K3 (b 1) (b 2) z) else 0) -
        mP hne j (x j) * R * Real.sqrt q * q * (mP hne j b * K3 (b 1) (b 2) z) := by
    intro b
    split_ifs <;> ring
  rw [← hR]
  simp only [e, sum_sub_distrib, sum_ite_eq', mem_univ, ↓reduceIte, ← mul_sum, hmB, yThree]
  field_simp
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem yThree_mean (hne : MiddleNonempty pr) (j : ι) (z : ZMod (pr j)) :
    ∑ b : Ai pr j, mP hne j b * ((Fintype.card (ZMod (pr j)) : ℝ) *
      (K3 (b 1) (b 2) z - ∑ b' : Ai pr j, mP hne j b' * K3 (b' 1) (b' 2) z)) = 0 := by
  have ht := mP_total hne j
  simp only [mul_sub, mul_sum, sum_sub_distrib]
  rw [sub_eq_zero, sum_comm]
  refine sum_congr rfl fun i _ => ?_
  have e : ∑ x : Ai pr j, mP hne j x * ((Fintype.card (ZMod (pr j)) : ℝ) *
      (mP hne j i * K3 (i 1) (i 2) z)) = (∑ x : Ai pr j, mP hne j x) *
        ((Fintype.card (ZMod (pr j)) : ℝ) * (mP hne j i * K3 (i 1) (i 2) z)) := by
    rw [sum_mul]
  rw [e, ht]
  ring

/-- **The label-`3` arms are centred.** -/
theorem yThree_centred (hne : MiddleNonempty pr) (j : ι) (z : ZMod (pr j)) :
    EnvelopeSteps.ip (mB hne) (yThree hne j z) (fun _ => 1) = 0 := by
  unfold EnvelopeSteps.ip yThree
  simp only [mul_one]
  rw [sum_mB_coord hne j (fun b => (Fintype.card (ZMod (pr j)) : ℝ) *
    (K3 (b 1) (b 2) z - ∑ b' : Ai pr j, mP hne j b' * K3 (b' 1) (b' 2) z))]
  exact yThree_mean hne j z

/-- **The label-`3` arms of different sectors are orthogonal.** -/
theorem yThree_orth (hne : MiddleNonempty pr) {j k : ι} (hjk : j ≠ k) (z : ZMod (pr j))
    (z' : ZMod (pr k)) : EnvelopeSteps.ip (mB hne) (yThree hne j z) (yThree hne k z') = 0 := by
  unfold EnvelopeSteps.ip yThree
  rw [sum_mB_two hne hjk (fun b => (Fintype.card (ZMod (pr j)) : ℝ) *
      (K3 (b 1) (b 2) z - ∑ b' : Ai pr j, mP hne j b' * K3 (b' 1) (b' 2) z))
    (fun b => (Fintype.card (ZMod (pr k)) : ℝ) *
      (K3 (b 1) (b 2) z' - ∑ b' : Ai pr k, mP hne k b' * K3 (b' 1) (b' 2) z')),
    yThree_mean, zero_mul]

/-- **`hUa` for the fold label `3` at a fold block** (`hdom_of_units`): with `U(3,3) = Q₁₂` as
conditional expectations of `m_{0,𝔅}` (`qOp`) and the chart's sector maps of `chart_lead`. Proved
here: the columns (`chartXi_three`), the arms are functions of `(x₁, x₂)`, centred and orthogonal
across the sectors. Inputs: `hcor` (edge `12` of the block in `L²(m_{0,𝔅})`), `hy1`, `hy2` (the
arms are orthogonal to the functions of `x₁` and of `x₂`: `A₃° ∈ 𝒦₁₂` at the block,
`lem:actual-features`(c), from OPS-L's `A3_perp` at each prime), `hcon3` (`‖A₃°‖ ≤ r_p`,
`lem:actual-features`(e)). -/
theorem hUa_three_chart (hne : MiddleNonempty pr) (x₀ : ∀ i, Ai pr i) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρ1 : ρ < 1)
    (hcor : ∀ (u v : (∀ i, ZMod (pr i)) → ℝ),
      EnvelopeSteps.ip (mB hne) (fun x => u (piA 1 x)) (fun _ => 1) = 0 →
      EnvelopeSteps.ip (mB hne) (fun x => v (piA 2 x)) (fun _ => 1) = 0 →
      |EnvelopeSteps.ip (mB hne) (fun x => u (piA 1 x)) (fun x => v (piA 2 x))| ≤
        ρ * Real.sqrt (EnvelopeSteps.ip (mB hne) (fun x => u (piA 1 x)) (fun x => u (piA 1 x))) *
          Real.sqrt (EnvelopeSteps.ip (mB hne) (fun x => v (piA 2 x)) (fun x => v (piA 2 x))))
    (hy1 : ∀ j z (u : (∀ i, ZMod (pr i)) → ℝ),
      EnvelopeSteps.ip (mB hne) (yThree hne j z) (fun x => u (piA 1 x)) = 0)
    (hy2 : ∀ j z (v : (∀ i, ZMod (pr i)) → ℝ),
      EnvelopeSteps.ip (mB hne) (yThree hne j z) (fun x => v (piA 2 x)) = 0)
    (hcon3 : ∀ j (c : ZMod (pr j) → ℝ), EnvelopeSteps.ip (mB hne) (∑ z, c z • yThree hne j z)
      (∑ z, c z • yThree hne j z) ≤ ∑ z, c z ^ 2) :
    (Matrix.of fun x x' : (∀ i, Ai pr i) =>
      EnvelopeSteps.kern (mB hne) (qOp (mB hne) (fun x => (piA 1 x, piA 2 x)) ρ) x x' -
      ∑ j, ∑ z, ((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ •
          (CXi hne x₀ j * XiM (mP hne j) A3c)) x (3, z) *
        ((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ • (CXi hne x₀ j * XiM (mP hne j) A3c))
          x' (3, z)).PosSemidef := by
  have := label3_realized (mB_nonneg hne) (fun x => (piA 1 x, piA 2 x)) hρ hρ1 hcor
    (fun j z => yThree hne j z)
    (fun j z => ⟨fun w => (Fintype.card (ZMod (pr j)) : ℝ) *
      (K3 (w.1 j) (w.2 j) z - ∑ b' : Ai pr j, mP hne j b' * K3 (b' 1) (b' 2) z), rfl⟩)
    hy1 hy2 (fun j k hjk z z' => yThree_orth hne hjk z z') hcon3
    (fun j => Matrix.of fun x z =>
      ((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ • (CXi hne x₀ j * XiM (mP hne j) A3c))
        x (3, z))
    (fun j x z => by simp only [Matrix.of_apply]; exact chartXi_three hne x₀ j x z)
  simpa only [Matrix.of_apply] using this

/-- **`hUa` of `hdom_of_units` at a fold block, all four labels**, for the chart's sector maps of
`chart_lead` (third arm `A₃°`), with OPS-S's unit lifts identified as the conditional expectations
of `m_{0,𝔅}` (`hU`, `hU3`; `foldUnit`: `e_aa ↦ M_aa − 𝒥`, `e₃₃ ↦ Q₁₂`) and the label-`3` inputs of
`hUa_three_chart`. -/
theorem hUa_fold_chart (hne : MiddleNonempty pr) (x₀ : ∀ i, Ai pr i) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρ1 : ρ < 1) (U : Fin 5 → Fin 5 → ((∀ i, Ai pr i) → ℝ) →ₗ[ℝ] ((∀ i, Ai pr i) → ℝ))
    (hU : ∀ a : Fin 3, U (Fin.castSucc (Fin.castSucc a)) (Fin.castSucc (Fin.castSucc a)) =
      uOp (mB hne) (piA a))
    (hU3 : U 3 3 = qOp (mB hne) (fun x => (piA 1 x, piA 2 x)) ρ)
    (hcor : ∀ (u v : (∀ i, ZMod (pr i)) → ℝ),
      EnvelopeSteps.ip (mB hne) (fun x => u (piA 1 x)) (fun _ => 1) = 0 →
      EnvelopeSteps.ip (mB hne) (fun x => v (piA 2 x)) (fun _ => 1) = 0 →
      |EnvelopeSteps.ip (mB hne) (fun x => u (piA 1 x)) (fun x => v (piA 2 x))| ≤
        ρ * Real.sqrt (EnvelopeSteps.ip (mB hne) (fun x => u (piA 1 x)) (fun x => u (piA 1 x))) *
          Real.sqrt (EnvelopeSteps.ip (mB hne) (fun x => v (piA 2 x)) (fun x => v (piA 2 x))))
    (hy1 : ∀ j z (u : (∀ i, ZMod (pr i)) → ℝ),
      EnvelopeSteps.ip (mB hne) (yThree hne j z) (fun x => u (piA 1 x)) = 0)
    (hy2 : ∀ j z (v : (∀ i, ZMod (pr i)) → ℝ),
      EnvelopeSteps.ip (mB hne) (yThree hne j z) (fun x => v (piA 2 x)) = 0)
    (hcon3 : ∀ j (c : ZMod (pr j) → ℝ), EnvelopeSteps.ip (mB hne) (∑ z, c z • yThree hne j z)
      (∑ z, c z • yThree hne j z) ≤ ∑ z, c z ^ 2) (a : Fin 4) :
    (Matrix.of fun x x' : (∀ i, Ai pr i) =>
      EnvelopeSteps.kern (mB hne) (U (Fin.castSucc a) (Fin.castSucc a)) x x' -
      ∑ j, ∑ z, ((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ •
          (CXi hne x₀ j * XiM (mP hne j) A3c)) x (a, z) *
        ((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ • (CXi hne x₀ j * XiM (mP hne j) A3c))
          x' (a, z)).PosSemidef := by
  fin_cases a
  · have h := hUa_singleton_chart hne x₀ 0 (fun _ => A3c)
    rw [← hU 0] at h
    exact h
  · have h := hUa_singleton_chart hne x₀ 1 (fun _ => A3c)
    rw [← hU 1] at h
    exact h
  · have h := hUa_singleton_chart hne x₀ 2 (fun _ => A3c)
    rw [← hU 2] at h
    exact h
  · have h := hUa_three_chart hne x₀ hρ hρ1 hcor hy1 hy2 hcon3
    rw [← hU3] at h
    exact h

end Columns

end Sarkozy.OpsFeature
