module

public import Sarkozy.JointRows.StarContract
public import Sarkozy.JointRows.PaleyCx

/-!
# The joint star matrix `𝕄` of `lem:joint-rows`(a), assembled from the two rows

Source: `paper/sections/16_extraction.tex`, proof of `lem:joint-rows`(a), "Pure stars": "with one
contraction `𝓕` for both rows ... `𝕋 = κ₀ r (𝓕 ⊕ 𝓕) 𝕄 (𝓕 ⊕ 𝓕)^* + 𝕋_mean`, where `𝕄` has the
diagonal entries `M_E(Φ̂)` and the off-diagonal entries `M_F(Φ̂)` and `M_F(Φ̂)^*` ... and
`D_E^T = -D_E`, `A_{D_E} = B_{D_E}` give `M_E(Φ̂)^* = M_E(Φ̂)`. Grouping the singletons of the two
copies and the sets of the two copies, `𝕄 = (𝒵 ⊗ Φ̂  𝒜 ⊗ I; 𝒜^* ⊗ I  0)`."

* `embC`: `h ↦ p^{-1/2}(h - E h)` into `ℋ = PaleyGauss.sumZero p`, an isometry on `L²_0(uniform)`
  (`inner_embC`, `inner_embC_paley`);
* `coefA`, `coefB`: `A_{iT} = (-1)^{|T|} ∏_{j∈T} D_{ij}` and `B_{jS} = ∏_{i∈S} D_{ij}`;
* `jointZ DE DF = (D_E  D_F; -D_Fᵀ  D_E)` and `jointA DE DF 𝒮 = (A_E  A_F; B_F  A_E)`: the grouped
  `𝒵` and `𝒜`;
* `jointFeat`: the grouped feature vector `(𝓕 ⊕ 𝓕)^*(f, h)` in `ℋ^{X ⊕ X} ⊕ ℋ^{𝒮 ⊕ 𝒮}`;
* **`qMat_jointFeat`**: for `D_E^T = -D_E` and mean-zero `f`, `h`,
  `⟨y, 𝕄 y⟩ = M_E(𝓕^*f, 𝓕^*f) + 2 M_F(𝓕^*f, 𝓕^*h) + M_E(𝓕^*h, 𝓕^*h)` at `y = jointFeat`;
* **`norm_jointFeat_le`**: `‖jointFeat f h‖² ≤ ‖f‖² + ‖h‖²` (from `featStar_norm_le`).
-/

@[expose] public section

open scoped BigOperators
open Matrix

namespace Sarkozy.JointRows.StarOps

open Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.JointRows.PaleyGauss

variable {p : ℕ} [Fact p.Prime]

theorem sum_cen_uniform (h : ZMod p → ℝ) : ∑ t, cen (FiniteLaw.uniform (ZMod p)) h t = 0 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold cen
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    FiniteLaw.expect_uniform, ZMod.card]
  have : (p : ℝ) * ((∑ t, h t) / p) = ∑ t, h t := by field_simp
  linarith

/-- `h ↦ p^{-1/2} (h - E h) ∈ ℋ`. -/
noncomputable def embC (h : ZMod p → ℝ) : sumZero p :=
  ⟨WithLp.toLp 2 (fun t => (Real.sqrt p)⁻¹ * cen (FiniteLaw.uniform (ZMod p)) h t), by
    show ∑ t, (Real.sqrt p)⁻¹ * cen (FiniteLaw.uniform (ZMod p)) h t = 0
    rw [← Finset.mul_sum, sum_cen_uniform, mul_zero]⟩

theorem cen_of_mean_zero {h : ZMod p → ℝ} (hh : (FiniteLaw.uniform (ZMod p)).expect h = 0) :
    cen (FiniteLaw.uniform (ZMod p)) h = h := by
  funext t; unfold cen; rw [hh, sub_zero]

theorem sqrt_inv_mul_self : (Real.sqrt p)⁻¹ * (Real.sqrt p)⁻¹ = (p : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [← mul_inv, Real.mul_self_sqrt hp0.le]

/-- `⟨embC a, embC b⟩ = ⟨a, b⟩_{L²(uniform)}` for mean-zero `a`, `b`. -/
theorem inner_embC {a b : ZMod p → ℝ} (ha : (FiniteLaw.uniform (ZMod p)).expect a = 0)
    (hb : (FiniteLaw.uniform (ZMod p)).expect b = 0) :
    inner ℝ (embC a) (embC b) = ip (FiniteLaw.uniform (ZMod p)) a b := by
  rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [embC, WithLp.ofLp_toLp, star_trivial, dotProduct, cen_of_mean_zero ha,
    cen_of_mean_zero hb]
  unfold ip
  rw [FiniteLaw.expect_uniform, ZMod.card, Finset.sum_div]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [div_eq_mul_inv, ← sqrt_inv_mul_self]
  ring

/-- `⟨embC a, Φ̂ embC b⟩ = ⟨a, Φ̂ b⟩_{L²(uniform)}` for mean-zero `a`, `b`. -/
theorem inner_embC_paley (hp : p % 4 = 3) {a b : ZMod p → ℝ}
    (ha : (FiniteLaw.uniform (ZMod p)).expect a = 0)
    (hb : (FiniteLaw.uniform (ZMod p)).expect b = 0) :
    inner ℝ (embC a) (paleyJ hp (embC b)) = ip (FiniteLaw.uniform (ZMod p)) a (paley p b) := by
  rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [embC, paleyJ, WithLp.ofLp_toLp, star_trivial, dotProduct, cen_of_mean_zero ha,
    cen_of_mean_zero hb, paley_const_mul]
  unfold ip
  rw [FiniteLaw.expect_uniform, ZMod.card, Finset.sum_div]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [div_eq_mul_inv, ← sqrt_inv_mul_self]
  ring

/-- `⟨a, Φ̂ b⟩ = -⟨b, Φ̂ a⟩`. -/
theorem ip_paley_anti (hp : p % 4 = 3) (a b : ZMod p → ℝ) :
    ip (FiniteLaw.uniform (ZMod p)) a (paley p b) =
      -ip (FiniteLaw.uniform (ZMod p)) b (paley p a) := by
  unfold ip
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform, paley_anti hp, neg_div]
  congr 2
  exact Finset.sum_congr rfl fun t _ => mul_comm _ _

theorem ip_comm' {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω') (a b : Ω' → ℝ) :
    ip μ a b = ip μ b a := by
  unfold ip; exact FiniteLaw.expect_congr _ fun x => mul_comm _ _

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `A_{iT} = (-1)^{|T|} ∏_{j∈T} D_{ij}`. -/
def coefA (D : X → X → ℝ) (i : X) (T : Finset X) : ℝ := (-1) ^ T.card * ∏ j ∈ T, D i j

/-- `B_{jS} = ∏_{i∈S} D_{ij}`. -/
def coefB (D : X → X → ℝ) (j : X) (S : Finset X) : ℝ := ∏ i ∈ S, D i j

omit [Fintype X] [DecidableEq X] in
/-- `D^T = -D` gives `B_D = A_D`. -/
theorem coefB_eq_coefA {D : X → X → ℝ} (hD : ∀ i j, D i j = -D j i) : coefB D = coefA D := by
  funext j S
  unfold coefB coefA
  rw [Finset.prod_congr rfl fun i _ => hD i j, Finset.prod_neg]

/-- `𝒵 = (D_E  D_F; -D_Fᵀ  D_E)`. -/
def jointZ (DE DF : X → X → ℝ) : Matrix (X ⊕ X) (X ⊕ X) ℝ :=
  Matrix.of (Sum.elim (fun i => Sum.elim (DE i) (DF i))
    (fun i => Sum.elim (fun j => -DF j i) (DE i)))

/-- `𝒜 = (A_E  A_F; B_F  A_E)`, from the singletons to the sets of the two copies. -/
def jointA (DE DF : X → X → ℝ) (𝒮 : Finset (Finset X)) : Matrix (X ⊕ X) (𝒮 ⊕ 𝒮) ℝ :=
  Matrix.of (Sum.elim (fun i => Sum.elim (fun S : 𝒮 => coefA DE i S) (fun S : 𝒮 => coefA DF i S))
    (fun j => Sum.elim (fun S : 𝒮 => coefB DF j S) (fun S : 𝒮 => coefA DE j S)))

omit [Fintype X] [DecidableEq X] in
theorem jointZ_antisymm {DE DF : X → X → ℝ} (hDE : ∀ i j, DE i j = -DE j i) :
    (jointZ DE DF)ᵀ = -jointZ DE DF := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [jointZ, transpose_apply, Matrix.neg_apply, of_apply, Sum.elim_inl, Sum.elim_inr,
      neg_neg]
  · rw [hDE i j, neg_neg]
  · rw [hDE i j, neg_neg]

/-- **The grouped feature vector** `(𝓕 ⊕ 𝓕)^*(f, h)`. -/
noncomputable def jointFeat (νp : X → FiniteLaw (ZMod p)) (κ : ℝ) (𝒮 : Finset (Finset X))
    (f h : (X → ZMod p) → ℝ) : PiLp 2 (fun _ : (X ⊕ X) ⊕ (𝒮 ⊕ 𝒮) => sumZero p) :=
  WithLp.toLp 2 (Sum.elim
    (Sum.elim (fun i => embC (featU νp κ f i)) (fun i => embC (featU νp κ h i)))
    (Sum.elim (fun S => embC (featW νp κ f S)) (fun S => embC (featW νp κ h S))))

theorem expect_featU (νp : X → FiniteLaw (ZMod p)) (κ : ℝ) {f : (X → ZMod p) → ℝ}
    (hf : (blockLaw νp).expect f = 0) (i : X) :
    (FiniteLaw.uniform (ZMod p)).expect (featU νp κ f i) = 0 := by
  unfold featU
  rw [FiniteLaw.expect_const_mul]
  have := expect_uStar νp i f
  rw [hf] at this
  rw [this, mul_zero]

theorem expect_featW (νp : X → FiniteLaw (ZMod p)) (κ : ℝ) (f : (X → ZMod p) → ℝ)
    (S : Finset X) : (FiniteLaw.uniform (ZMod p)).expect (featW νp κ f S) = 0 := by
  unfold featW
  rw [FiniteLaw.expect_const_mul]
  unfold cen
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const, sub_self, mul_zero]

/-- **`⟨y, 𝕄 y⟩` at the grouped features** (`lem:joint-rows`(a), "Pure stars"): for
`D_E^T = -D_E` and mean-zero `f`, `h`, `qMat 𝒵 𝒜 Φ̂ y = M_E(𝓕^*f, 𝓕^*f) + 2 M_F(𝓕^*f, 𝓕^*h) +
M_E(𝓕^*h, 𝓕^*h)`. -/
theorem qMat_jointFeat (hp : p % 4 = 3) (νp : X → FiniteLaw (ZMod p)) (κ : ℝ)
    (𝒮 : Finset (Finset X)) {DE DF : X → X → ℝ} (hDE : ∀ i j, DE i j = -DE j i)
    {f h : (X → ZMod p) → ℝ} (hf : (blockLaw νp).expect f = 0)
    (hh : (blockLaw νp).expect h = 0) :
    Sector.qMat (jointZ DE DF) (jointA DE DF 𝒮) (paleyJ hp) (jointFeat νp κ 𝒮 f h) =
      mForm DE 𝒮 (coefA DE) 𝒮 (coefB DE) (featU νp κ f) (featW νp κ f) (featU νp κ f)
          (featW νp κ f) +
        2 * mForm DF 𝒮 (coefA DF) 𝒮 (coefB DF) (featU νp κ f) (featW νp κ f) (featU νp κ h)
          (featW νp κ h) +
        mForm DE 𝒮 (coefA DE) 𝒮 (coefB DE) (featU νp κ h) (featW νp κ h) (featU νp κ h)
          (featW νp κ h) := by
  unfold Sector.qMat jointFeat
  set U := featU νp κ f with hU
  set U' := featU νp κ h with hU'
  set W := featW νp κ f with hW
  set W' := featW νp κ h with hW'
  have mU : ∀ i, (FiniteLaw.uniform (ZMod p)).expect (U i) = 0 := expect_featU νp κ hf
  have mU' : ∀ i, (FiniteLaw.uniform (ZMod p)).expect (U' i) = 0 := expect_featU νp κ hh
  have mW : ∀ S, (FiniteLaw.uniform (ZMod p)).expect (W S) = 0 := expect_featW νp κ f
  have mW' : ∀ S, (FiniteLaw.uniform (ZMod p)).expect (W' S) = 0 := expect_featW νp κ h
  have hBA := coefB_eq_coefA hDE
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, jointZ, jointA, of_apply]
  simp only [inner_embC_paley hp (mU _) (mU _), inner_embC_paley hp (mU _) (mU' _),
    inner_embC_paley hp (mU' _) (mU _), inner_embC_paley hp (mU' _) (mU' _),
    inner_embC (mU _) (mW _), inner_embC (mU _) (mW' _), inner_embC (mU' _) (mW _),
    inner_embC (mU' _) (mW' _)]
  unfold mForm
  simp only [hBA]
  -- the `(inr, inl)` block of `𝒵`, by `Φ̂^* = -Φ̂`
  have h21 : ∑ i, ∑ j, -DF j i * ip (FiniteLaw.uniform (ZMod p)) (U' i) (paley p (U j)) =
      ∑ i, ∑ j, DF i j * ip (FiniteLaw.uniform (ZMod p)) (U i) (paley p (U' j)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [ip_paley_anti hp (U' j) (U i)]; ring
  have hcomm : ∀ (j : X) (S : Finset X), ip (FiniteLaw.uniform (ZMod p)) (W S) (U' j) =
      ip (FiniteLaw.uniform (ZMod p)) (U' j) (W S) := fun j S => ip_comm' _ _ _
  have hcommE : ∀ (j : X) (S : Finset X), ip (FiniteLaw.uniform (ZMod p)) (W S) (U j) =
      ip (FiniteLaw.uniform (ZMod p)) (U j) (W S) := fun j S => ip_comm' _ _ _
  have hcommE' : ∀ (j : X) (S : Finset X), ip (FiniteLaw.uniform (ZMod p)) (W' S) (U' j) =
      ip (FiniteLaw.uniform (ZMod p)) (U' j) (W' S) := fun j S => ip_comm' _ _ _
  simp only [hcomm, hcommE, hcommE']
  simp only [Finset.sum_add_distrib]
  rw [h21]
  have hcs : ∀ F : Finset X → ℝ, ∑ S : 𝒮, F S = ∑ S ∈ 𝒮, F S := fun F => Finset.sum_coe_sort 𝒮 F
  simp only [← hcs]
  ring

end Sarkozy.JointRows.StarOps
