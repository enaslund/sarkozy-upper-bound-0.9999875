module

public import Sarkozy.MiddleRecords.ActualFeaturesSynthesis
public import Sarkozy.SignedEstimates.G0

@[expose] public section

/-!
# The actual features of `lem:actual-features` at the paper's objects (PG)

`paper/sections/21_middle_records.tex`, `lem:actual-features`, `lem:old-f-law`(a).

At one prime, with `F = 𝔽_p` (`p ≡ 3 (mod 4)`, `p ≥ 19`), the half triples `x = (x₀, x₁, x₂)` and
the actual half marginal `m₀` of the reference fold record (B8's `m0`, the layer-`0` marginal of
`K₀ = λ(G_{F,2})`):

* **`m0_eq_oldW`** (`lem:old-f-law`(a)): B8's `m₀(x)` is W6's explicit weight
  `oldW(x₀, x₁, x₂) / Z`. So W6's computations of `lem:actual-features` apply to the paper's
  marginal `m₀`; **`sum_m0`**: `∑_x m₀(x) G(x₀, x₁, x₂) = Iw G / Z`.
* **The features** (`lem:actual-features`, notation of `subsec:middle-records:notation`), maps from
  functions on `𝔽_p` to functions of the half `x`:
  `V₀ h = h(x₀)`, `A₁ h = (P h)(x₂)`, `A₂ h = (P h)(x₁)`, `A₃ h = A3op h (x₁, x₂)`
  (W6's `A3op`, the paper's `-(1/p) ∑_s χ(s - x₁) χ(s - x₂) h(s)` on `H₀`), with the Paley operator
  `(P h)(s) = E_t χ(t - s) h(t)`. The arms are indexed `arm 0 = A₁`, `arm 1 = A₂`, `arm 2 = A₃`.
* **The adjoints** in `L²(m₀)` (`adj`): `S^{*m} f = Π₀ (s ↦ p ⟨S δ_s, f⟩_{m₀})`, with `Π₀` the
  centring of `H₀`. **`adj_spec`**: `⟨S h, f⟩_{m₀} = ⟨h, S^{*m} f⟩_{H₀}` for every mean-zero `h`
  (`H₀` carries the uniform inner product `⟨h, k⟩ = E_a h(a) k(a)`).
* **`frame_analysis`** (`lem:actual-features`(d) in adjoint form): for every function `f` of the
  half,
  `‖V₀^{*m} f‖² + p (‖A₁^{*m} f‖² + ‖A₂^{*m} f‖² + ‖A₃^{*m} f‖²) ≤ Γ ‖f‖²_{m₀}`, with W6's
  `Γ = 1 + ϱ₀₂ + 2ϱ₀₁ + g₀₃ + 2g₁₃ ≤ Γ_A` (`gammaW`, `gammaW_le`). This is the frame bound
  `‖(V₀, A₁/r, A₂/r, A₃/r)‖² ≤ Γ_A` of `lem:record:direct-gram` (`1/r² = p`), obtained from W6's
  synthesis bound by duality.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.PrimeGram

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing Sarkozy.SignedComponents
  Sarkozy.SignedEstimates Sarkozy.MiddleRecords

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-! ## Sums over half triples -/

/-- Half triples as triples. -/
def tripleEquiv : (Fin 3 → F) ≃ F × F × F where
  toFun x := (x 0, x 1, x 2)
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv x := by
    funext o
    fin_cases o <;> rfl
  right_inv _ := rfl

omit [Field F] [DecidableEq F] in
theorem sum_triple (G : (Fin 3 → F) → ℝ) :
    ∑ x, G x = ∑ a, ∑ b, ∑ c, G ![a, b, c] := by
  rw [← Equiv.sum_comp tripleEquiv.symm, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

/-! ## The actual half marginal is W6's weight -/

section Marginal

variable (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)

omit [Field F] [Fintype F] [DecidableEq F] in
theorem injective_of_ne {x : Fin 3 → F} (h01 : x 0 ≠ x 1) (h02 : x 0 ≠ x 2) (h12 : x 1 ≠ x 2) :
    Function.Injective x := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [eq_comm]

/-- **`lem:old-f-law`(a): the actual half marginal.** B8's `m₀` (the layer-`0` marginal of `K₀`)
is W6's explicit weight: `m₀(x) = oldW(x₀, x₁, x₂)/Z`, with
`oldW = (1 + χ(x₂ - x₀))(p - 5 - χ(x₁ - x₀) - χ(x₂ - x₁))/4` on distinct labels and
`Z = p(p - 1)(p - 3)(p - 4)/4`. From E1's `g0_eq` on `H_F` and `m₀ = 0` off `H_F`. -/
theorem m0_eq_oldW (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (h19 : 19 ≤ Fintype.card F) (x : Fin 3 → F) :
    (m0 hF).weight x = oldW (x 0) (x 1) (x 2) / oldZ (F := F) := by
  have h19' : (19 : ℝ) ≤ qF := by exact_mod_cast h19
  rw [oldZ_eq hR h3]
  by_cases hx : HF x
  · have hg := g0_eq hR h3 h19 hF hx
    unfold g0 at hg
    rw [Hcard_eq hR] at hg
    obtain ⟨h01, h02, h12⟩ := HF_ne hx
    have hc : (χ (x 2 - x 0) : ℝ) = 1 := by exact_mod_cast hx.2
    unfold oldW
    simp only [ne_eq, h01, not_false_eq_true, h02, h12, and_self, ↓reduceIte, hc]
    have hp2 : (0 : ℝ) < qF - 2 := by linarith
    have hden : (0 : ℝ) < qF * (qF - 1) * (qF - 2) / 2 := by
      have : (0 : ℝ) < qF * (qF - 1) * (qF - 2) := by
        have h1 : (0 : ℝ) < qF - 1 := by linarith
        positivity
      linarith
    have hw : (m0 hF).weight x = (qF - 2) * (qF - 5 - (χ (x 1 - x 0) : ℝ) -
        (χ (x 2 - x 1) : ℝ)) / ((qF - 3) * (qF - 4)) / (qF * (qF - 1) * (qF - 2) / 2) := by
      rw [eq_div_iff hden.ne', hg]
    rw [hw]
    have h3' : (0 : ℝ) < qF - 3 := by linarith
    have h4' : (0 : ℝ) < qF - 4 := by linarith
    have h1' : (0 : ℝ) < qF - 1 := by linarith
    have h0' : (0 : ℝ) < qF := by linarith
    field_simp
    ring
  · have hm : (m0 hF).weight x = 0 := by
      by_contra h
      exact hx (m0_support hF h)
    rw [hm]
    unfold oldW
    split_ifs with hd
    · obtain ⟨h01, h02, h12⟩ := hd
      have hinj := injective_of_ne h01 h02 h12
      have hc : ¬ χ (x 2 - x 0) = 1 := fun h => hx ⟨hinj, h⟩
      rcases chiR_ne_cases (sub_ne_zero.mpr (Ne.symm h02)) with h | h
      · exact absurd (by exact_mod_cast h) hc
      · rw [h]
        ring
    · simp

/-- **`m₀`-integrals are W6's `Iw`**: `∑_x m₀(x) G(x₀, x₁, x₂) = Iw G / Z`. -/
theorem sum_m0 (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F)
    (G : F → F → F → ℝ) :
    ∑ x, (m0 hF).weight x * G (x 0) (x 1) (x 2) = Iw G / oldZ (F := F) := by
  rw [sum_triple]
  unfold Iw
  rw [sum_div]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun c _ => ?_
  rw [m0_eq_oldW hF hR h3 h19]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  ring

end Marginal

/-! ## Inner products, centring, the features and their adjoints -/

/-- The inner product of `L²(m)` on functions of the half: `⟨f, g⟩_m = ∑_x m(x) f(x) g(x)`. -/
noncomputable def mip (m f g : (Fin 3 → F) → ℝ) : ℝ := ∑ x, m x * f x * g x

/-- The inner product of `H₀ ⊆ L²(𝔽_p)` (uniform law): `⟨h, k⟩ = p⁻¹ ∑_a h(a) k(a)`. -/
noncomputable def uip (h k : F → ℝ) : ℝ := qF⁻¹ * ∑ a, h a * k a

/-- The centring `Π₀ h = h - E h` onto `H₀`. -/
noncomputable def cen (h : F → ℝ) : F → ℝ := fun a => h a - qF⁻¹ * ∑ s, h s

/-- The point mass `δ_s` on `𝔽_p`. -/
def delta (s : F) : F → ℝ := fun t => if t = s then 1 else 0

/-- **`V₀`** (`lem:actual-features`): `(V₀ h)(x) = h(x₀)`. -/
def V0 (h : F → ℝ) : (Fin 3 → F) → ℝ := fun x => h (x 0)

/-- **`A₁ = V₂ P`** (`lem:actual-features`): `(A₁ h)(x) = (P h)(x₂)`. -/
noncomputable def A1 (h : F → ℝ) : (Fin 3 → F) → ℝ := fun x => paleyOp h (x 2)

/-- **`A₂ = V₁ P`** (`lem:actual-features`): `(A₂ h)(x) = (P h)(x₁)`. -/
noncomputable def A2 (h : F → ℝ) : (Fin 3 → F) → ℝ := fun x => paleyOp h (x 1)

/-- **`A₃`**, the pair feature (`lem:actual-features`(c)), unprojected:
`(A₃ h)(x) = A3op h (x₁, x₂)`, which on `H₀` is `-(1/p) ∑_s χ(s - x₁) χ(s - x₂) h(s)`. -/
noncomputable def A3 (h : F → ℝ) : (Fin 3 → F) → ℝ := fun x => A3op h (x 1) (x 2)

/-- The three arms in the order of `lem:record:direct-gram`: `arm 0 = A₁`, `arm 1 = A₂`,
`arm 2 = A₃`. -/
noncomputable def arm : Fin 3 → (F → ℝ) → (Fin 3 → F) → ℝ := ![A1, A2, A3]

/-- **The adjoint in `L²(m)`** of a feature map `S : H₀ → L²(m)`:
`S^{*m} f = Π₀ (s ↦ p ⟨S δ_s, f⟩_m)`. -/
noncomputable def adj (m : (Fin 3 → F) → ℝ) (S : (F → ℝ) → (Fin 3 → F) → ℝ)
    (f : (Fin 3 → F) → ℝ) : F → ℝ :=
  cen (fun s => qF * mip m (S (delta s)) f)

/-- A feature map given by a kernel: `S h = ∑_s h(s) S δ_s`. -/
def IsKernel (S : (F → ℝ) → (Fin 3 → F) → ℝ) : Prop :=
  ∀ h x, S h x = ∑ s, h s * S (delta s) x

omit [DecidableEq F] in
theorem sum_cen (h : F → ℝ) : ∑ a, cen h a = 0 := by
  unfold cen
  rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  have h0 : qF ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  ring

omit [Field F] [DecidableEq F] in
theorem uip_cen {h : F → ℝ} (hh : ∑ a, h a = 0) (k : F → ℝ) : uip h (cen k) = uip h k := by
  unfold uip cen
  congr 1
  simp only [mul_sub, sum_sub_distrib]
  rw [← sum_mul, hh, zero_mul, sub_zero]

/-- **The adjoint identity**: `⟨S h, f⟩_m = ⟨h, S^{*m} f⟩_{H₀}` for mean-zero `h`. -/
theorem adj_spec (m : (Fin 3 → F) → ℝ) {S : (F → ℝ) → (Fin 3 → F) → ℝ} (hS : IsKernel S)
    {h : F → ℝ} (hh : ∑ a, h a = 0) (f : (Fin 3 → F) → ℝ) :
    mip m (S h) f = uip h (adj m S f) := by
  unfold adj
  rw [uip_cen hh]
  unfold uip mip
  have hq : qF ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [hS h]
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  refine sum_congr rfl fun x _ => ?_
  field_simp

omit [Field F] in
theorem V0_kernel : IsKernel (V0 (F := F)) := by
  intro h x
  simp [V0, delta]

theorem paleyOp_kernel (h : F → ℝ) (a : F) :
    paleyOp h a = ∑ s, h s * paleyOp (delta s) a := by
  unfold paleyOp delta
  rw [mul_sum]
  refine sum_congr rfl fun s _ => ?_
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  ring

theorem A1_kernel : IsKernel (A1 (F := F)) := fun h x => paleyOp_kernel h (x 2)

theorem A2_kernel : IsKernel (A2 (F := F)) := fun h x => paleyOp_kernel h (x 1)

theorem A3_kernel : IsKernel (A3 (F := F)) := by
  intro h x
  unfold A3 A3op delta
  have e1 : ∀ s, (∑ t, (χ (t - x 1) : ℝ) * (χ (t - x 2) : ℝ) * (if t = s then 1 else 0)) =
      (χ (s - x 1) : ℝ) * (χ (s - x 2) : ℝ) := by
    intro s
    simp
  have e2 : ∀ s : F, (∑ t, (if t = s then (1 : ℝ) else 0)) = 1 := by
    intro s
    simp
  simp only [e1, e2]
  rw [mul_sum, mul_sum, mul_sum, ← sum_neg_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun s _ => ?_
  ring

theorem arm_kernel (i : Fin 3) : IsKernel (arm (F := F) i) := by
  fin_cases i
  · exact A1_kernel
  · exact A2_kernel
  · exact A3_kernel

/-! ## The frame bound in adjoint form -/

/-- W6's frame constant `Γ = 1 + ϱ₀₂ + 2ϱ₀₁ + g₀₃ + 2g₁₃` (`lem:actual-features`(d)). -/
noncomputable def gammaW : ℝ :=
  1 + Real.sqrt (rho02sq (F := F)) + 2 * Real.sqrt (rho01sq (F := F)) + g03 (F := F) +
    2 * g13 (F := F)

omit [DecidableEq F] in
/-- `Γ ≤ Γ_A(1/p, p^{-1/2})` (W6's `gamma_le_GammaA`). -/
theorem gammaW_le (h7 : 7 ≤ qF) : gammaW (F := F) ≤ GammaA (1 / qF) (Real.sqrt (1 / qF)) :=
  gamma_le_GammaA h7

omit [DecidableEq F] in
theorem gammaW_nonneg (h7 : 7 ≤ qF) : 0 ≤ gammaW (F := F) := by
  unfold gammaW g03 g13
  have h1 : 0 ≤ Real.sqrt (rho02sq (F := F)) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt (rho01sq (F := F)) := Real.sqrt_nonneg _
  have h4 : (0 : ℝ) < qF - 4 := by linarith
  have h5 : (0 : ℝ) < qF - 1 := by linarith
  have h0 : (0 : ℝ) < qF := by linarith
  have : 0 ≤ Real.sqrt qF * (qF + 4) / (qF * (qF - 1) * (qF - 4)) := by positivity
  have : 0 ≤ Real.sqrt (1 + muF (F := F) ^ 2 * qF) * Real.sqrt qF / (qF * (qF - 1)) := by
    positivity
  linarith

end Sarkozy.PrimeGram
