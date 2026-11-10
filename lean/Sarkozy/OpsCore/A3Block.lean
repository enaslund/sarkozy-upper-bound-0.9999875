module

public import Sarkozy.OpsCore.A3Perp
public import Sarkozy.OpsCore.LeadFold

@[expose] public section

/-!
# The unprojected against the projected leading star at a block (OPS-L)

`paper/sections/21_middle_records.tex`, `lem:actual-features`(e), `prop:signed-bounds`(b);
`paper/sections/23_envelopes.tex`, (N1). The leading star of the fold record at a block,
`foldLead` (`LeadFold`, the singleton sectors of PG's `L^m_{t,p}`, unprojected `A₃`), against the
chart's `L°_{t,𝔅}` (`foldLeadC`, the same with the projected arm `A₃° = A₃ - GA` of `A3Perp`):

* `lead_chart_prime`: at one prime, at B8's actual marginal `m₀` and any frame constant `Γ`
  (`FrameAt`), `|L^m_t(u, v) - L°_t(u, v)| ≤ 2|1 - t| J_F q r Γ^{1/2} ‖u‖ ‖v‖`;
* **`foldLead_chart_le`**: at a middle block of primes `p ≡ 3 (mod 4)`, `p ≥ 19`, with
  `J ≥ J_F(p) q_p r_p` and `Γ ≥ Γ_W(p)` at every prime,
  `|L_{t,𝔅}(φ, ψ) - L°_{t,𝔅}(φ, ψ)| ≤ 2|1 - t| J Γ^{1/2} ‖φ‖ ‖ψ‖` in `L²(m_{0,𝔅})`.

So the leading star of `fold_leadOK_atom` may be replaced by the chart's, the difference going
into the remainder `e_R`, at the cost `2|1 - t| J Γ^{1/2}`: about `2.1 q_b²` at the least prime
`b` (`J_F q r ≈ √2 q²`, `1 - t ≈ 0.746`, `Γ ≈ 1`), against the prime remainder `e_sg q`.
-/

open Finset Matrix

namespace Sarkozy.OpsCore

open Sarkozy.MiddleRecords Sarkozy.TraceMixing Sarkozy.PrimeGram Sarkozy.Envelopes
open Sarkozy.SignedGram Sarkozy.FoldSymSkew Sarkozy.NormBoundsPaper4 Sarkozy.PartVRecords
open Sarkozy.NormBoundsPaper2 (ip)
open Sarkozy.Labellings Sarkozy.PartV Sarkozy.SignedComponents

section Prime

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

theorem lFormC_zero (m : (Fin 3 → F) → ℝ) (t : ℝ) (G : (F → ℝ) → (Fin 3 → F) → ℝ) :
    lFormC m t G 0 0 = 0 := by
  have hadj : ∀ S, adj m S (0 : (Fin 3 → F) → ℝ) = 0 := fun S => by
    funext x
    simp [adj, cen, mip]
  have hW : Wa m (0 : (Fin 3 → F) → ℝ) = 0 := by
    funext x
    simp [Wa, hadj]
  unfold lFormC
  simp [hadj, hW, uip]

omit [Field F] [DecidableEq F] in
theorem uip_self_nonneg (h : F → ℝ) : 0 ≤ uip h h := by
  unfold uip
  have : (0 : ℝ) ≤ qF⁻¹ := by positivity
  exact mul_nonneg this (sum_nonneg fun s _ => mul_self_nonneg _)

omit [Field F] [DecidableEq F] in
theorem mip_self (m f : (Fin 3 → F) → ℝ) : mip m f f = ∑ x, m x * f x ^ 2 := by
  unfold mip
  exact sum_congr rfl fun x _ => by ring

/-- **The change of the leading star at one prime**, in `singForm_le`'s shape: at B8's actual
marginal and a frame constant `Γ`,
`|L^m_t(u, v) - L°_t(u, v)| ≤ 2|1 - t| J_F q r Γ^{1/2} ‖u‖ ‖v‖`. -/
theorem lead_chart_prime (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)
    (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F) (t : ℝ)
    {Γ : ℝ} (hΓ : ∀ f, FrameAt (m0 hF).weight Γ f) (hΓ0 : 0 ≤ Γ) (u v : (Fin 3 → F) → ℝ) :
    |lForm (m0 hF).weight t u v - lFormC (m0 hF).weight t GA u v| ≤
      2 * |1 - t| * jFqr (F := F) (Real.sqrt (rho01Sq (F := F))) * Real.sqrt Γ *
        Real.sqrt (∑ x, (m0 hF).weight x * u x ^ 2) *
          Real.sqrt (∑ x, (m0 hF).weight x * v x ^ 2) := by
  have hmeq : (m0 hF).weight = m0W := funext fun x => m0_eq_oldW hF hR h3 h19 x
  have h7 : (7 : ℝ) ≤ qF := by
    have : (19 : ℝ) ≤ qF := by exact_mod_cast h19
    linarith
  have key := lead_chart_change_proj hR h3 h7 t u v
  rw [← hmeq] at key
  set m := (m0 hF).weight
  set J := jFqr (F := F) (Real.sqrt (rho01Sq (F := F)))
  have hJ : 0 ≤ J := by
    unfold J jFqr muF
    have h4 : 0 ≤ qF - 4 := by linarith
    have h1 : 0 ≤ qF - 1 := by linarith
    have h0 : 0 ≤ qF := by linarith
    positivity
  have hW : ∀ f, Real.sqrt (uip (Wa m f) (Wa m f)) ≤ Real.sqrt Γ * Real.sqrt (mip m f f) := by
    intro f
    have hf := hΓ f
    unfold FrameAt at hf
    have hB : 0 ≤ qF * ∑ i, uip (Ba m i f) (Ba m i f) := by
      have : (0 : ℝ) ≤ qF := by linarith
      exact mul_nonneg this (sum_nonneg fun i _ => uip_self_nonneg _)
    rw [← Real.sqrt_mul hΓ0]
    exact Real.sqrt_le_sqrt (by linarith)
  have hu0 := Real.sqrt_nonneg (mip m u u)
  have hv0 := Real.sqrt_nonneg (mip m v v)
  have hc : 0 ≤ |1 - t| * J := mul_nonneg (abs_nonneg _) hJ
  rw [← mip_self, ← mip_self]
  calc |lForm m t u v - lFormC m t GA u v|
      ≤ |1 - t| * J * (Real.sqrt (uip (Wa m v) (Wa m v)) * Real.sqrt (mip m u u) +
          Real.sqrt (uip (Wa m u) (Wa m u)) * Real.sqrt (mip m v v)) := key
    _ ≤ |1 - t| * J * (Real.sqrt Γ * Real.sqrt (mip m v v) * Real.sqrt (mip m u u) +
          Real.sqrt Γ * Real.sqrt (mip m u u) * Real.sqrt (mip m v v)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hc
        · exact mul_le_mul_of_nonneg_right (hW v) hu0
        · exact mul_le_mul_of_nonneg_right (hW u) hv0
    _ = 2 * |1 - t| * J * Real.sqrt Γ * Real.sqrt (mip m u u) * Real.sqrt (mip m v v) := by ring

end Prime

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

/-- **The chart's leading star of the fold record at a block** (`L°_{t,𝔅}`): the prime stars with
the projected arm `A₃°` placed on the singleton sectors. -/
noncomputable def foldLeadC (hne : MiddleNonempty pr) (t : ℝ) (x₀ : ∀ i, Ai pr i)
    (φ ψ : (∀ i, Ai pr i) → ℝ) : ℝ :=
  singForm (mP hne) x₀ (fun i => lFormC (mP hne i) t GA) φ ψ

theorem foldLead_sub_foldLeadC (hne : MiddleNonempty pr) (t : ℝ) (x₀ : ∀ i, Ai pr i)
    (φ ψ : (∀ i, Ai pr i) → ℝ) :
    foldLead hne t x₀ φ ψ - foldLeadC hne t x₀ φ ψ =
      singForm (mP hne) x₀
        (fun i u v => lForm (mP hne i) t u v - lFormC (mP hne i) t GA u v) φ ψ := by
  unfold foldLead foldLeadC singForm
  rw [← sum_sub_distrib]

/-- **`L_{t,𝔅}` against `L°_{t,𝔅}` at a middle block**: with `J ≥ J_F(p) q_p r_p` and
`Γ ≥ Γ_W(p)` at every prime, `|L_{t,𝔅}(φ, ψ) - L°_{t,𝔅}(φ, ψ)| ≤ 2|1 - t| J Γ^{1/2} ‖φ‖ ‖ψ‖` in
`L²(m_{0,𝔅})`. -/
theorem foldLead_chart_le (hne : MiddleNonempty pr) (h3 : ∀ i, pr i % 4 = 3)
    (h19 : ∀ i, 19 ≤ pr i) (t : ℝ) {J Γ : ℝ} (hJnn : 0 ≤ J)
    (hJ : ∀ i, jFqr (F := ZMod (pr i)) (Real.sqrt (rho01Sq (F := ZMod (pr i)))) ≤ J)
    (hΓ : ∀ i, gammaP pr i ≤ Γ) (x₀ : ∀ i, Ai pr i) (φ ψ : (∀ i, Ai pr i) → ℝ) :
    |foldLead hne t x₀ φ ψ - foldLeadC hne t x₀ φ ψ| ≤
      2 * |1 - t| * J * Real.sqrt Γ * Real.sqrt (ip (mP hne) φ φ) *
        Real.sqrt (ip (mP hne) ψ ψ) := by
  rw [foldLead_sub_foldLeadC]
  have hΓ0 : ∀ i, 0 ≤ gammaP pr i := gammaP_nonneg h19
  have hJ0 : ∀ i, 0 ≤ jFqr (F := ZMod (pr i)) (Real.sqrt (rho01Sq (F := ZMod (pr i)))) := by
    intro i
    obtain ⟨_, _, h19'⟩ := primeHyps h3 h19 i
    have h19r : (19 : ℝ) ≤ (Fintype.card (ZMod (pr i)) : ℝ) := by exact_mod_cast h19'
    unfold jFqr muF
    have h4 : 0 ≤ (Fintype.card (ZMod (pr i)) : ℝ) - 4 := by linarith
    have h1 : 0 ≤ (Fintype.card (ZMod (pr i)) : ℝ) - 1 := by linarith
    positivity
  have hc : 0 ≤ 2 * |1 - t| * J * Real.sqrt Γ := by positivity
  have hzero : ∀ i, (fun u v => lForm (mP hne i) t u v - lFormC (mP hne i) t GA u v) 0 0 = 0 :=
    fun i => by simp only [lForm_zero, lFormC_zero, sub_zero]
  refine singForm_le (mP_nonneg hne) (mP_total hne) x₀ _ hzero hc (fun i u v _ _ => ?_) φ ψ
  obtain ⟨hR, h3', h19'⟩ := primeHyps h3 h19 i
  have hp := lead_chart_prime (hne.F2 i) hR h3' h19' t (fun f => frame_block hne h3 h19 i f)
    (hΓ0 i) u v
  refine hp.trans ?_
  have hsu := Real.sqrt_nonneg (∑ x, (m0 (hne.F2 i)).weight x * u x ^ 2)
  have hsv := Real.sqrt_nonneg (∑ x, (m0 (hne.F2 i)).weight x * v x ^ 2)
  have hJi := hJ i
  have hΓi : Real.sqrt (gammaP pr i) ≤ Real.sqrt Γ := Real.sqrt_le_sqrt (hΓ i)
  have hsΓ := Real.sqrt_nonneg (gammaP pr i)
  have ht := abs_nonneg (1 - t)
  have hk : 2 * |1 - t| * jFqr (F := ZMod (pr i)) (Real.sqrt (rho01Sq (F := ZMod (pr i)))) *
      Real.sqrt (gammaP pr i) ≤ 2 * |1 - t| * J * Real.sqrt Γ := by
    have h1 : 2 * |1 - t| * jFqr (F := ZMod (pr i)) (Real.sqrt (rho01Sq (F := ZMod (pr i)))) ≤
        2 * |1 - t| * J := mul_le_mul_of_nonneg_left hJi (by positivity)
    exact mul_le_mul h1 hΓi hsΓ (by have := (hJ0 i).trans hJi; positivity)
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hsu) hsv
  exact this

end Block

end Sarkozy.OpsCore
