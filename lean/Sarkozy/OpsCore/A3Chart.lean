module

public import Sarkozy.OpsCore.A3Proj
public import Sarkozy.PrimeGram.Gram

@[expose] public section

/-!
# From the unprojected to the projected leading star at a prime (OPS-L)

`paper/sections/21_middle_records.tex`, `lem:actual-features`(c), (e);
`paper/sections/23_envelopes.tex`, (N1) and `eq:signed-star`.

PG's leading form `L^m_t` (`PrimeGram.lForm`) uses the arms `(A₁, A₂, A₃)` with the
**unprojected** `A₃`. The chart of OPS-F (`Ξ_p = (V₀, V₁, V₂, A₃°/r_p, 0)`) and (N1) use the
projected arm `A₃° = A₃ - Π_{𝓗₁+𝓗₂} A₃`. This file bounds the change at one prime, in PG's
objects, by `A3_proj12_paper`:

* `mip_pair`: for functions of `(x₁, x₂)`, PG's `⟨·,·⟩_m` at `m = m0W = oldW/oldZ` (PG's
  `m0_eq_oldW`: B8's actual half marginal) is `ip12`, the inner product of the pair law `m₁₂`;
* **`proj_A3_sq_le`**: if `G = u(x₁) + v(x₂)` (`v` of mean zero) and `A₃ h - G ⊥ G` in `L²(m₀)`
  (e.g. `G = Π_{𝓗₁+𝓗₂} A₃ h`), then `‖G‖² ≤ (J_F q r)² ‖h‖²`;
* `lFormC` (the leading form with the third arm `A₃ - G`), **`lForm_sub_lFormC`** (the change
  is the `(1 - t)` star of `G` alone) and **`lForm_sub_lFormC_le`**: for every kernel map `G`
  with `‖G h‖_m ≤ ε ‖h‖`,
  `|⟨f, L^m_t g⟩ - ⟨f, L°_t g⟩| ≤ |1 - t| ε (‖V₀^{*m} g‖ ‖f‖ + ‖V₀^{*m} f‖ ‖g‖)`;
* **`lead_chart_change`**: at `m = m0W`, for `G` the projection (as in `proj_A3_sq_le`, for every
  mean-zero `h`), the same with `ε = J_F q r` (`jFqr` at `ϱ₀₁`).

So the leading star of `LeadOK` (PG's `L^m_t`) and the chart's `L°_t` differ at a prime by at
most `2|1 - t| J_F q r` times the norm of `V₀^{*m}` (at most `Γ_A^{1/2}`, PG's
`frame_analysis`). What is not done here: constructing `G` (the orthogonal projection; it exists
in finite dimension) as a kernel map, and the block statement (`lem:actual-features`(e)).
-/

open Finset

namespace Sarkozy.OpsCore

open Sarkozy.MiddleRecords Sarkozy.TraceMixing Sarkozy.PrimeGram Sarkozy.Envelopes

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-- The weight of the actual half marginal on half triples, `oldW/oldZ` (PG's `m0_eq_oldW`). -/
noncomputable def m0W (x : Fin 3 → F) : ℝ := oldW (x 0) (x 1) (x 2) / oldZ (F := F)

theorem m0W_nonneg (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (x : Fin 3 → F) : 0 ≤ m0W x :=
  div_nonneg (oldW_nonneg h7 _ _ _) (oldZ_pos hF h3 h7).le

/-- **Pair functions**: `⟨f(x₁, x₂), g(x₁, x₂)⟩_{m₀} = ⟨f, g⟩_{m₁₂}`. -/
theorem mip_pair (f g : F → F → ℝ) :
    mip m0W (fun x => f (x 1) (x 2)) (fun x => g (x 1) (x 2)) = ip12 f g := by
  unfold mip ip12 m0W m12
  rw [sum_triple, sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_div, sum_mul, sum_mul]
  refine sum_congr rfl fun a _ => ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- **The projection of `A₃ h` on `𝓗₁ + 𝓗₂` has norm at most `J_F q r ‖h‖`**: if
`G = u(x₁) + v(x₂)` with `v` of mean zero and `⟨A₃ h - G, G⟩_{m₀} = 0`. -/
theorem proj_A3_sq_le (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h u v : F → ℝ) (hh : ∑ s, h s = 0) (hv : ∑ b, v b = 0)
    (horth : ip12 (fun a b => A3op h a b - (u a + v b)) (fun a b => u a + v b) = 0) :
    ip12 (fun a b => u a + v b) (fun a b => u a + v b) ≤
      jFqr (F := F) (Real.sqrt (rho01Sq (F := F))) ^ 2 * unifNormSq h := by
  set G : F → F → ℝ := fun a b => u a + v b
  have hlin : ip12 (fun a b => A3op h a b - G a b) G = ip12 (A3op h) G - ip12 G G := by
    unfold ip12
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun b _ => by ring
  have heq : ip12 (A3op h) G = ip12 G G := by
    have := hlin.symm.trans horth
    linarith
  have hb := A3_proj12_paper hF h3 h7 h u v hh hv
  rw [heq] at hb
  have hG0 : 0 ≤ ip12 G G := by
    unfold ip12
    refine sum_nonneg fun a _ => sum_nonneg fun b _ => ?_
    have : 0 ≤ m12 a b :=
      div_nonneg (sum_nonneg fun _ _ => oldW_nonneg h7 _ _ _) (oldZ_pos hF h3 h7).le
    nlinarith [sq_nonneg (G a b)]
  rcases hG0.lt_or_eq with hpos | hzero
  · have : ip12 G G * ip12 G G ≤
        (jFqr (F := F) (Real.sqrt (rho01Sq (F := F))) ^ 2 * unifNormSq h) * ip12 G G := by
      nlinarith [hb]
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]
    have : 0 ≤ unifNormSq h := by unfold unifNormSq; positivity
    positivity

section Chart

variable (m : (Fin 3 → F) → ℝ)

/-- The arms with the third replaced by `A₃ - G`. -/
noncomputable def armC (G : (F → ℝ) → (Fin 3 → F) → ℝ) : Fin 3 → (F → ℝ) → (Fin 3 → F) → ℝ :=
  ![A1, A2, fun h x => A3 h x - G h x]

/-- **The leading form with the projected arm**, `⟨f, L°_t g⟩_m`, when `G h` is the projection of
`A₃ h` on `𝓗₁ + 𝓗₂` (`L°_t = A°_{a_t} V₀^{*m} - V₀ A°_{a_t}^{*m}`, `A° = (A₁, A₂, A₃°)`). -/
noncomputable def lFormC (t : ℝ) (G : (F → ℝ) → (Fin 3 → F) → ℝ) (f g : (Fin 3 → F) → ℝ) : ℝ :=
  ∑ i, aT t i * uip (adj m (armC G i) f) (Wa m g) -
    ∑ i, aT t i * uip (Wa m f) (adj m (armC G i) g)

omit [Field F] in
theorem adj_sub (S G : (F → ℝ) → (Fin 3 → F) → ℝ) (f : (Fin 3 → F) → ℝ) :
    adj m (fun h x => S h x - G h x) f = fun s => adj m S f s - adj m G f s := by
  funext s
  unfold adj cen mip
  simp only [mul_sub, sub_mul, sum_sub_distrib]
  ring

omit [Field F] [DecidableEq F] in
theorem uip_sub_left (a b k : F → ℝ) : uip (fun s => a s - b s) k = uip a k - uip b k := by
  unfold uip
  rw [← mul_sub, ← sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun s _ => by ring

omit [Field F] [DecidableEq F] in
theorem uip_sub_right (a b k : F → ℝ) : uip k (fun s => a s - b s) = uip k a - uip k b := by
  unfold uip
  rw [← mul_sub, ← sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun s _ => by ring

/-- **The change of the leading form is the `(1 - t)` star of `G`**:
`⟨f, L^m_t g⟩ - ⟨f, L°_t g⟩ = (1 - t)(⟨G^{*m} f, V₀^{*m} g⟩ - ⟨V₀^{*m} f, G^{*m} g⟩)`. -/
theorem lForm_sub_lFormC (t : ℝ) (G : (F → ℝ) → (Fin 3 → F) → ℝ) (f g : (Fin 3 → F) → ℝ) :
    lForm m t f g - lFormC m t G f g =
      aT t 2 * (uip (adj m G f) (Wa m g) - uip (Wa m f) (adj m G g)) := by
  unfold lForm lFormC Ba
  simp only [Fin.sum_univ_three]
  have e0 : armC G 0 = arm 0 := rfl
  have e1 : armC G 1 = arm 1 := rfl
  have e2 : armC G 2 = fun h x => arm 2 h x - G h x := rfl
  rw [e0, e1, e2, adj_sub, adj_sub, uip_sub_left, uip_sub_right]
  ring

omit [Field F] [DecidableEq F] in
/-- Cauchy–Schwarz in `L²(m)` for a nonnegative weight. -/
theorem mip_sq_le (hm : ∀ x, 0 ≤ m x) (a b : (Fin 3 → F) → ℝ) :
    mip m a b ^ 2 ≤ mip m a a * mip m b b := by
  have e : ∀ (c d : (Fin 3 → F) → ℝ), mip m c d =
      ∑ x, (Real.sqrt (m x) * c x) * (Real.sqrt (m x) * d x) := fun c d => by
    unfold mip
    refine sum_congr rfl fun x _ => ?_
    rw [show Real.sqrt (m x) * c x * (Real.sqrt (m x) * d x) =
      (Real.sqrt (m x) * Real.sqrt (m x)) * c x * d x by ring, Real.mul_self_sqrt (hm x)]
  have e2 : ∀ c : (Fin 3 → F) → ℝ, mip m c c = ∑ x, (Real.sqrt (m x) * c x) ^ 2 := fun c => by
    rw [e]; exact sum_congr rfl fun x _ => by ring
  rw [e a b, e2 a, e2 b]
  exact sum_mul_sq_le_sq_mul_sq _ _ _

/-- One term of the change: `|⟨G^{*m} f, V₀^{*m} g⟩| ≤ ε ‖V₀^{*m} g‖ ‖f‖`. -/
theorem abs_uip_adj_le (hm : ∀ x, 0 ≤ m x) {G : (F → ℝ) → (Fin 3 → F) → ℝ} (hGk : IsKernel G)
    {ε : ℝ} (hε : 0 ≤ ε) (hG : ∀ h : F → ℝ, ∑ s, h s = 0 → mip m (G h) (G h) ≤ ε ^ 2 * uip h h)
    (f : (Fin 3 → F) → ℝ) (k : F → ℝ) (hk : ∑ s, k s = 0) :
    |uip (adj m G f) k| ≤ ε * Real.sqrt (uip k k) * Real.sqrt (mip m f f) := by
  have hsym : uip (adj m G f) k = uip k (adj m G f) := by
    unfold uip; congr 1; exact sum_congr rfl fun s _ => mul_comm _ _
  rw [hsym, ← adj_spec m hGk hk f]
  have hcs := mip_sq_le m hm (G k) f
  have hGG := hG k hk
  have hGG0 : 0 ≤ mip m (G k) (G k) := by
    unfold mip; exact sum_nonneg fun x _ => by nlinarith [hm x, sq_nonneg (G k x)]
  have hff : 0 ≤ mip m f f := by
    unfold mip; exact sum_nonneg fun x _ => by nlinarith [hm x, sq_nonneg (f x)]
  have hkk : 0 ≤ uip k k := by
    unfold uip
    have : (0 : ℝ) ≤ qF⁻¹ := by positivity
    exact mul_nonneg this (sum_nonneg fun s _ => mul_self_nonneg _)
  calc |mip m (G k) f| ≤ Real.sqrt (mip m (G k) (G k) * mip m f f) := Real.abs_le_sqrt hcs
    _ = Real.sqrt (mip m (G k) (G k)) * Real.sqrt (mip m f f) := Real.sqrt_mul hGG0 _
    _ ≤ Real.sqrt (ε ^ 2 * uip k k) * Real.sqrt (mip m f f) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hGG) (Real.sqrt_nonneg _)
    _ = ε * Real.sqrt (uip k k) * Real.sqrt (mip m f f) := by
        rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε]

theorem sum_Wa (f : (Fin 3 → F) → ℝ) : ∑ s, Wa m f s = 0 := sum_cen _

/-- **The change of the leading star** for a kernel map `G` with `‖G h‖_m ≤ ε ‖h‖` on `H₀`:
`|⟨f, L^m_t g⟩ - ⟨f, L°_t g⟩| ≤ |1 - t| ε (‖V₀^{*m} g‖ ‖f‖ + ‖V₀^{*m} f‖ ‖g‖)`. -/
theorem lForm_sub_lFormC_le (hm : ∀ x, 0 ≤ m x) (t : ℝ) {G : (F → ℝ) → (Fin 3 → F) → ℝ}
    (hGk : IsKernel G) {ε : ℝ} (hε : 0 ≤ ε)
    (hG : ∀ h : F → ℝ, ∑ s, h s = 0 → mip m (G h) (G h) ≤ ε ^ 2 * uip h h)
    (f g : (Fin 3 → F) → ℝ) :
    |lForm m t f g - lFormC m t G f g| ≤
      |1 - t| * ε * (Real.sqrt (uip (Wa m g) (Wa m g)) * Real.sqrt (mip m f f) +
        Real.sqrt (uip (Wa m f) (Wa m f)) * Real.sqrt (mip m g g)) := by
  rw [lForm_sub_lFormC]
  have h1 := abs_uip_adj_le m hm hGk hε hG f (Wa m g) (sum_Wa m g)
  have h2 := abs_uip_adj_le m hm hGk hε hG g (Wa m f) (sum_Wa m f)
  have hsym : uip (Wa m f) (adj m G g) = uip (adj m G g) (Wa m f) := by
    unfold uip; congr 1; exact sum_congr rfl fun s _ => mul_comm _ _
  have ha : aT t 2 = 1 - t := rfl
  rw [hsym, ha, abs_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hXY : |uip (adj m G f) (Wa m g) - uip (adj m G g) (Wa m f)| ≤
      |uip (adj m G f) (Wa m g)| + |uip (adj m G g) (Wa m f)| := by
    rw [sub_eq_add_neg]
    exact (abs_add_le _ _).trans (by rw [abs_neg])
  rw [mul_add, ← mul_assoc, ← mul_assoc]
  exact hXY.trans (add_le_add h1 h2)

end Chart

/-- **The leading star of `LeadOK` against the chart's at one prime**: at the actual marginal
`m₀` (`m0W`), if `G h` is the projection of `A₃ h` on `𝓗₁ + 𝓗₂` for every mean-zero `h`
(`G h = u_h(x₁) + v_h(x₂)`, `v_h` of mean zero, `A₃ h - G h ⊥ G h`) and `G` is a kernel map,
then `|⟨f, L^m_t g⟩ - ⟨f, L°_t g⟩| ≤ |1 - t| J_F q r (‖V₀^{*m} g‖ ‖f‖ + ‖V₀^{*m} f‖ ‖g‖)`. -/
theorem lead_chart_change (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (t : ℝ) {G : (F → ℝ) → (Fin 3 → F) → ℝ} (hGk : IsKernel G) (u v : (F → ℝ) → F → ℝ)
    (hGuv : ∀ h x, G h x = u h (x 1) + v h (x 2)) (hv : ∀ h, ∑ s, h s = 0 → ∑ b, v h b = 0)
    (horth : ∀ h, ∑ s, h s = 0 →
      ip12 (fun a b => A3op h a b - (u h a + v h b)) (fun a b => u h a + v h b) = 0)
    (f g : (Fin 3 → F) → ℝ) :
    |lForm m0W t f g - lFormC m0W t G f g| ≤
      |1 - t| * jFqr (F := F) (Real.sqrt (rho01Sq (F := F))) *
        (Real.sqrt (uip (Wa m0W g) (Wa m0W g)) * Real.sqrt (mip m0W f f) +
          Real.sqrt (uip (Wa m0W f) (Wa m0W f)) * Real.sqrt (mip m0W g g)) := by
  have hJ : 0 ≤ jFqr (F := F) (Real.sqrt (rho01Sq (F := F))) := by
    unfold jFqr muF
    have h4 : 0 ≤ qF - 4 := by linarith
    have h1 : 0 ≤ qF - 1 := by linarith
    have h0 : 0 ≤ qF := by linarith
    positivity
  refine lForm_sub_lFormC_le m0W (m0W_nonneg hF h3 h7) t hGk hJ (fun h hh => ?_) f g
  have e : mip m0W (G h) (G h) =
      ip12 (fun a b => u h a + v h b) (fun a b => u h a + v h b) := by
    rw [← mip_pair]
    unfold mip
    exact sum_congr rfl fun x _ => by rw [hGuv]
  rw [e]
  have hb := proj_A3_sq_le hF h3 h7 h (u h) (v h) hh (hv h hh) (horth h hh)
  have hU : unifNormSq h = uip h h := by
    unfold unifNormSq uip; congr 1; exact sum_congr rfl fun s _ => by ring
  rwa [hU] at hb

end Sarkozy.OpsCore
