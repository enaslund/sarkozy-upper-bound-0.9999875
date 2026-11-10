module

public import Sarkozy.SignedDecompCrude.Kernel
public import Sarkozy.PrimeGram.OldDecomp
public import Sarkozy.PrimeGram.Sanity

@[expose] public section

/-!
# `prop:signed-bounds`(c) for the signed record, reduced to three kernel bounds (ND)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(c), Step 2 ("the signed record"),
with the transport rules (T1)–(T3) of the proof of `lem:old-f-law`(e),(f).

At one prime, with `m = m₀`, `ν = ν_F`, `E2 K f g = E_{ν⊗ν}[f K g]` (PG's `E2`), `q = 1/p`,
`r = p^{-1/2}`, `e = e₀`, `Γ = gammaW`. The signed record `N` is compared with the kernel
`∑_c α_c V_c = 1 + K_⋆ + K_ns - K_rq` (`signedV_split`). Three inputs, each a single bound:

* **(K) `RecordForm N t κ`** (the normalizations and completions of the three components,
  `prop:signed-bounds`(c), Step 1 weighted by `∑|c_{uv}| = 1 + t`; the paper's `(1 + t)E_c`):
  on `m₀`-centred `f, g`, `|⟨f, N g⟩ - E_{ν⊗ν}[f (∑ α_c V_c) g]| ≤ κ q ‖f‖_{m₀} ‖g‖_{m₀}`;
* **(NS) `NonstarBound t n`** (`lem:record:projected-nonstar`(a) for the nine nonstars; the
  paper's `n = 2(9 - 6t)/Z`): `|E_{ν⊗ν}[f K_ns g]| ≤ n q ‖f‖_ν ‖g‖_ν`;
* **(RQ) `RemovedBound t k`** (the removed query, Schur test; the paper's `k = k_col = 9/4`):
  `|E_{ν⊗ν}[f K_rq g]| ≤ k q ‖f‖_ν ‖g‖_ν`.

**`newDecomp_of_inputs`**: then `NewDecomp m₀ N t e′` with
`e′ = κ + c_g/q + 6 (D_g/q) Γ r + (n + k)/(1 - e₀)` (`esgND`). The constant kernel costs `c_g`
(T3, `Enu_centred`), the star kernel gives `O₀ + L^m_t` exactly on `L²(m₀)` (`star_eq_kernel`)
and up to `6 D_g Γ r` after the transport `f ↦ f/g₀` (T2; the paper has `√(3 + 2t²)` for `6`),
and (T1) transports (NS), (RQ) (`Enu_sq`).
-/

open Finset Matrix

namespace Sarkozy.SignedDecompCrude

open Sarkozy.PrimeGram Sarkozy.TraceMixing Sarkozy.MiddleRecords Sarkozy.SignedEstimates
open Sarkozy.SignedComponents Sarkozy.SignedDecomp Sarkozy.Envelopes Sarkozy.Labellings

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

/-! ## The labelled inputs -/

section Inputs

variable (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)

/-- **(K)** (`prop:signed-bounds`(c), Step 1, the normalizations `z_{uv}` and completions `M_c` of
the three components, weighted by `1 + t`; *hypothesis*): on the `m₀`-centred functions the form of
the signed record `N` differs from `E_{ν⊗ν}[f (∑_c α_c V_c) g]` by at most `κ q ‖f‖ ‖g‖`. -/
def RecordForm (N : Matrix (Fin 3 → F) (Fin 3 → F) ℝ) (t κ : ℝ) : Prop :=
  ∀ f g : (Fin 3 → F) → ℝ, (m0 hF).weight ⬝ᵥ f = 0 → (m0 hF).weight ⬝ᵥ g = 0 →
    |f ⬝ᵥ (N *ᵥ g) - E2 (signedV t) f g| ≤
      κ * qF⁻¹ * (√(mip (m0 hF).weight f f) * √(mip (m0 hF).weight g g))

end Inputs

/-- **(NS)** (`lem:record:projected-nonstar`(a) for the nine nonstar monomials of `Ψ^soft_t`;
*hypothesis*): `‖K_ns‖ ≤ n q` on `L²(ν_F)`. -/
def NonstarBound (t n : ℝ) : Prop :=
  ∀ f g : (Fin 3 → F) → ℝ, |E2 (Knon t) f g| ≤
    n * qF⁻¹ * (√(Enu (fun x => f x ^ 2)) * √(Enu (fun x => g x ^ 2)))

/-- **(RQ)** (the removed query `δ₁₀ G_t` of `prop:signed-bounds`(c), Step 2; *hypothesis*):
`‖K_rq‖ ≤ k q` on `L²(ν_F)`. -/
def RemovedBound (t k : ℝ) : Prop :=
  ∀ f g : (Fin 3 → F) → ℝ, |E2 (Krq t) f g| ≤
    k * qF⁻¹ * (√(Enu (fun x => f x ^ 2)) * √(Enu (fun x => g x ^ 2)))

/-- **The crude constant** `e′ = κ + c_g/q + 6 (D_g/q) Γ r + (n + k)/(1 - e)`. -/
noncomputable def esgND (q r e Γ κ n k : ℝ) : ℝ :=
  κ + cgC e / q + 6 * (DgC e / q) * Γ * r + (n + k) / (1 - e)

/-! ## Linearity of `E2` and the star form -/

theorem E2_signed (t : ℝ) (f g : (Fin 3 → F) → ℝ) :
    E2 (signedV t) f g = Enu f * Enu g + E2 (Kstar t) f g + E2 (Knon t) f g -
      E2 (Krq t) f g := by
  have e1 : E2 (fun _ _ => (1 : ℝ)) f g = Enu f * Enu g := by
    unfold E2 Enu
    rw [sum_mul]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun y _ => ?_
    ring
  rw [← e1]
  unfold E2
  simp only [← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [signedV_split]
  ring

/-- `|⟨A_i^{*m} u, V₀^{*m} v⟩| ≤ Γ r ‖u‖ ‖v‖` from the frame bounds at `u` and `v`. -/
theorem uip_BW_le {m : (Fin 3 → F) → ℝ} (hm : ∀ x, 0 ≤ m x) {Γ : ℝ} (hΓ : 0 ≤ Γ)
    {u v : (Fin 3 → F) → ℝ} (hu : FrameAt m Γ u) (hv : FrameAt m Γ v) (i : Fin 3) :
    |uip (Ba m i u) (Wa m v)| ≤ Γ * (√qF)⁻¹ * (√(mip m u u) * √(mip m v v)) := by
  have hq : (0 : ℝ) < qF := Nat.cast_pos.mpr Fintype.card_pos
  have hBB0 := uip_self_nonneg (Ba m i u)
  have hWW0 := uip_self_nonneg (Wa m v)
  have hmu := mip_self_nonneg hm u
  have hmv := mip_self_nonneg hm v
  have hB : qF * uip (Ba m i u) (Ba m i u) ≤ Γ * mip m u u := by
    have h := hu
    unfold FrameAt at h
    have hs : uip (Ba m i u) (Ba m i u) ≤ ∑ j, uip (Ba m j u) (Ba m j u) :=
      single_le_sum (f := fun j => uip (Ba m j u) (Ba m j u)) (fun j _ => uip_self_nonneg _)
        (mem_univ i)
    have := uip_self_nonneg (Wa m u)
    nlinarith
  have hW : uip (Wa m v) (Wa m v) ≤ Γ * mip m v v := by
    have h := hv
    unfold FrameAt at h
    have : 0 ≤ ∑ j, uip (Ba m j v) (Ba m j v) := sum_nonneg fun j _ => uip_self_nonneg _
    nlinarith
  have hB' : uip (Ba m i u) (Ba m i u) ≤ Γ * mip m u u * qF⁻¹ := by
    rw [le_mul_inv_iff₀ hq]
    linarith
  have hcs := uip_sq_le (Ba m i u) (Wa m v)
  have hΓu : 0 ≤ Γ * mip m u u * qF⁻¹ := le_trans hBB0 hB'
  have h2 : uip (Ba m i u) (Wa m v) ^ 2 ≤
      (Γ * (√qF)⁻¹ * (√(mip m u u) * √(mip m v v))) ^ 2 := by
    have e : (Γ * (√qF)⁻¹ * (√(mip m u u) * √(mip m v v))) ^ 2 =
        (Γ * mip m u u * qF⁻¹) * (Γ * mip m v v) := by
      rw [mul_pow, mul_pow, mul_pow, inv_pow, Real.sq_sqrt hq.le, Real.sq_sqrt hmu,
        Real.sq_sqrt hmv]
      ring
    rw [e]
    calc _ ≤ uip (Ba m i u) (Ba m i u) * uip (Wa m v) (Wa m v) := hcs
      _ ≤ _ := mul_le_mul hB' hW hWW0 hΓu
  have hN : 0 ≤ Γ * (√qF)⁻¹ * (√(mip m u u) * √(mip m v v)) := by positivity
  have := Real.abs_le_sqrt h2
  rwa [Real.sqrt_sq hN] at this

/-- `|⟨V₀^{*m} u, A_i^{*m} v⟩| ≤ Γ r ‖u‖ ‖v‖`. -/
theorem uip_WB_le {m : (Fin 3 → F) → ℝ} (hm : ∀ x, 0 ≤ m x) {Γ : ℝ} (hΓ : 0 ≤ Γ)
    {u v : (Fin 3 → F) → ℝ} (hu : FrameAt m Γ u) (hv : FrameAt m Γ v) (i : Fin 3) :
    |uip (Wa m u) (Ba m i v)| ≤ Γ * (√qF)⁻¹ * (√(mip m u u) * √(mip m v v)) := by
  rw [uip_comm, mul_comm (√(mip m u u))]
  exact uip_BW_le hm hΓ hv hu i

/-- **`‖O₀ + L^m_t‖ ≤ 6 Γ r`** (crude; the paper's frame argument gives `√(3 + 2t²) Γ_A r`), for
`0 ≤ t ≤ 1`, from the frame bounds at `u` and `v`. -/
theorem starForm_le {m : (Fin 3 → F) → ℝ} (hm : ∀ x, 0 ≤ m x) {Γ : ℝ} (hΓ : 0 ≤ Γ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {u v : (Fin 3 → F) → ℝ} (hu : FrameAt m Γ u)
    (hv : FrameAt m Γ v) :
    |oForm m u v + lForm m t u v| ≤ 6 * (Γ * (√qF)⁻¹ * (√(mip m u u) * √(mip m v v))) := by
  have hN : 0 ≤ Γ * (√qF)⁻¹ * (√(mip m u u) * √(mip m v v)) := by positivity
  set N := Γ * (√qF)⁻¹ * (√(mip m u u) * √(mip m v v))
  have b0 := abs_le.mp (uip_BW_le hm hΓ hu hv 0)
  have b1 := abs_le.mp (uip_BW_le hm hΓ hu hv 1)
  have b2 := abs_le.mp (uip_BW_le hm hΓ hu hv 2)
  have c0 := abs_le.mp (uip_WB_le hm hΓ hu hv 0)
  have c1 := abs_le.mp (uip_WB_le hm hΓ hu hv 1)
  have c2 := abs_le.mp (uip_WB_le hm hΓ hu hv 2)
  unfold oForm lForm
  simp only [Fin.sum_univ_three, aT, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  set X0 := uip (Ba m 0 u) (Wa m v)
  set X1 := uip (Ba m 1 u) (Wa m v)
  set X2 := uip (Ba m 2 u) (Wa m v)
  set Y0 := uip (Wa m u) (Ba m 0 v)
  set Y1 := uip (Wa m u) (Ba m 1 v)
  set Y2 := uip (Wa m u) (Ba m 2 v)
  have h1t : 0 ≤ 1 - t := by linarith
  have p1 := mul_nonneg h1t (by linarith : 0 ≤ N + X0)
  have p2 := mul_nonneg h1t (by linarith : 0 ≤ N - X0)
  have p3 := mul_nonneg h1t (by linarith : 0 ≤ N + X2)
  have p4 := mul_nonneg h1t (by linarith : 0 ≤ N - X2)
  have p5 := mul_nonneg ht0 (by linarith : 0 ≤ N + Y0)
  have p6 := mul_nonneg ht0 (by linarith : 0 ≤ N - Y0)
  have p7 := mul_nonneg h1t (by linarith : 0 ≤ N + Y2)
  have p8 := mul_nonneg h1t (by linarith : 0 ≤ N - Y2)
  have p9 := mul_nonneg ht0 hN
  rw [abs_le]
  constructor <;> nlinarith

/-! ## The reduction -/

section Main

variable (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)

/-- `m₀` vanishes on `{x₁ = x₂}` (it is supported on `H_F`, whose triples are injective). -/
theorem m0_off12 (x : Fin 3 → F) (h : x 1 = x 2) : (m0 hF).weight x = 0 := by
  apply m_zero_off hF
  intro hx
  exact absurd (hx.1 h) (by decide)

variable (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F)

include hR h3 h19 in
/-- **`prop:signed-bounds`(c), the centred signed record, from (K), (NS), (RQ)**:
`Π_⊥ T[N] Π_⊥ = O₀ + L^m_t + R^new` with `‖R^new‖ ≤ e′ q`,
`e′ = κ + c_g/q + 6 (D_g/q) Γ r + (n + k)/(1 - e₀)` (`esgND`), for `0 ≤ t ≤ 1`. -/
theorem newDecomp_of_inputs {N : Matrix (Fin 3 → F) (Fin 3 → F) ℝ} {t κ n k : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hn : 0 ≤ n) (hk : 0 ≤ k)
    (hK : RecordForm hF N t κ) (hNS : NonstarBound (F := F) t n)
    (hQ : RemovedBound (F := F) t k) :
    NewDecomp (m0 hF).weight N t (esgND qF⁻¹ (√qF)⁻¹ (e0 qF) (gammaW (F := F)) κ n k) := by
  intro f g hf hg
  set m := (m0 hF).weight with hm_def
  have hm : ∀ x, 0 ≤ m x := (m0 hF).nonneg
  have h19' : (19 : ℝ) ≤ qF := by exact_mod_cast h19
  have hq0 : (0 : ℝ) < qF := by linarith
  set q := qF⁻¹ with hq_def
  set r := (√qF)⁻¹ with hr_def
  set e := e0 qF with he_def
  set Γ := gammaW (F := F) with hΓ_def
  have hqpos : 0 < q := inv_pos.mpr hq0
  have hrpos : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hq0)
  have he1 : e < 1 := e0_lt_one h19
  have he0 : 0 ≤ e := e0_nonneg h19
  have hΓ : 0 ≤ Γ := gammaW_nonneg (by linarith)
  have hframe : ∀ u, FrameAt m Γ u := fun u => frame_analysis hF hR h3 h19 u
  have hm12 : ∀ x : Fin 3 → F, x 1 = x 2 → m x = 0 := m0_off12 hF
  set Nf := √(mip m f f)
  set Ng := √(mip m g g)
  have hNf : 0 ≤ Nf := Real.sqrt_nonneg _
  have hNg : 0 ≤ Ng := Real.sqrt_nonneg _
  set NN := Nf * Ng with hNN_def
  have hNN : 0 ≤ NN := mul_nonneg hNf hNg
  set kk := e / (1 - e) with hkk_def
  have hkk : 0 ≤ kk := div_nonneg he0 (by linarith)
  set df := divG hF f
  set dg := divG hF g
  -- the star part is `O₀ + L^m_t` at `f/g₀, g/g₀`
  have hS : E2 (Kstar t) f g = oForm m df dg + lForm m t df dg := by
    rw [E2_eq_m hF hR h3 h19, star_eq_kernel hR h3 hm12]
  -- (T3) the constant kernel
  have hJ : |Enu f * Enu g| ≤ cgC e * NN := by
    rw [abs_mul]
    have h1 := Enu_centred hF hR h3 h19 f hf
    have h2 := Enu_centred hF hR h3 h19 g hg
    calc |Enu f| * |Enu g| ≤ (kk * Nf) * (kk * Ng) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hkk hNf)
      _ = cgC e * NN := by unfold cgC; rw [hNN_def]; ring
  -- norms of `f/g₀`
  have hdf_sub : √(mip m (fun x => df x - f x) (fun x => df x - f x)) ≤ kk * Nf := by
    calc _ ≤ √(kk ^ 2 * mip m f f) := Real.sqrt_le_sqrt (norm_divG_sub hF hR h3 h19 f)
      _ = kk * Nf := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hkk]
  have hdg_sub : √(mip m (fun x => dg x - g x) (fun x => dg x - g x)) ≤ kk * Ng := by
    calc _ ≤ √(kk ^ 2 * mip m g g) := Real.sqrt_le_sqrt (norm_divG_sub hF hR h3 h19 g)
      _ = kk * Ng := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hkk]
  have hinv : 0 ≤ 1 / (1 - e) := div_nonneg zero_le_one (by linarith)
  have hdg : √(mip m dg dg) ≤ 1 / (1 - e) * Ng := by
    calc _ ≤ √((1 / (1 - e)) ^ 2 * mip m g g) := Real.sqrt_le_sqrt (norm_divG hF hR h3 h19 g)
      _ = 1 / (1 - e) * Ng := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hinv]
  -- (T2) the transport of the star part, through its kernel (bilinear)
  have hbil : oForm m df dg + lForm m t df dg - (oForm m f g + lForm m t f g) =
      (oForm m (fun x => df x - f x) dg + lForm m t (fun x => df x - f x) dg) +
        (oForm m f (fun x => dg x - g x) + lForm m t f (fun x => dg x - g x)) := by
    rw [star_eq_kernel hR h3 hm12, star_eq_kernel hR h3 hm12, star_eq_kernel hR h3 hm12,
      star_eq_kernel hR h3 hm12, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun y _ => ?_
    ring
  have hLd : |oForm m df dg + lForm m t df dg - (oForm m f g + lForm m t f g)| ≤
      6 * (DgC e * Γ * r * NN) := by
    rw [hbil]
    have b1 := starForm_le hm hΓ ht0 ht1 (hframe (fun x => df x - f x)) (hframe dg)
    have b2 := starForm_le hm hΓ ht0 ht1 (hframe f) (hframe (fun x => dg x - g x))
    have hΓr : 0 ≤ Γ * r := mul_nonneg hΓ hrpos.le
    have c1 : 6 * (Γ * r * (√(mip m (fun x => df x - f x) (fun x => df x - f x)) *
        √(mip m dg dg))) ≤ 6 * (Γ * r * ((kk * Nf) * (1 / (1 - e) * Ng))) := by
      have := mul_le_mul hdf_sub hdg (Real.sqrt_nonneg _) (mul_nonneg hkk hNf)
      nlinarith
    have c2 : 6 * (Γ * r * (Nf * √(mip m (fun x => dg x - g x) (fun x => dg x - g x)))) ≤
        6 * (Γ * r * (Nf * (kk * Ng))) := by
      have := mul_le_mul_of_nonneg_left hdg_sub hNf
      nlinarith
    have hD : kk * (1 / (1 - e)) + kk ≤ DgC e := dg_coef he1
    have hD' : Γ * r * NN * (kk * (1 / (1 - e)) + kk) ≤ Γ * r * NN * DgC e :=
      mul_le_mul_of_nonneg_left hD (mul_nonneg hΓr hNN)
    have t := abs_add_le
      (oForm m (fun x => df x - f x) dg + lForm m t (fun x => df x - f x) dg)
      (oForm m f (fun x => dg x - g x) + lForm m t f (fun x => dg x - g x))
    have e6 : 6 * (Γ * r * ((kk * Nf) * (1 / (1 - e) * Ng))) + 6 * (Γ * r * (Nf * (kk * Ng))) =
        6 * (Γ * r * NN * (kk * (1 / (1 - e)) + kk)) := by rw [hNN_def]; ring
    have e7 : 6 * (DgC e * Γ * r * NN) = 6 * (Γ * r * NN * DgC e) := by ring
    linarith
  -- (T1) the nonstars and the removed query
  have hs : ∀ u : (Fin 3 → F) → ℝ, √(Enu (fun x => u x ^ 2)) ≤
      √(1 / (1 - e)) * √(mip m u u) := by
    intro u
    rw [← Real.sqrt_mul hinv]
    apply Real.sqrt_le_sqrt
    rw [one_div_mul_eq_div]
    exact Enu_sq hF hR h3 h19 u
  have hss : √(1 / (1 - e)) * √(1 / (1 - e)) = 1 / (1 - e) := Real.mul_self_sqrt hinv
  have hprod : √(Enu (fun x => f x ^ 2)) * √(Enu (fun x => g x ^ 2)) ≤ 1 / (1 - e) * NN := by
    calc _ ≤ (√(1 / (1 - e)) * Nf) * (√(1 / (1 - e)) * Ng) :=
          mul_le_mul (hs f) (hs g) (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hNf)
      _ = 1 / (1 - e) * NN := by
          rw [hNN_def, show (√(1 / (1 - e)) * Nf) * (√(1 / (1 - e)) * Ng) =
            (√(1 / (1 - e)) * √(1 / (1 - e))) * (Nf * Ng) by ring, hss]
  have hNSb : |E2 (Knon t) f g| ≤ n * q * (1 / (1 - e) * NN) :=
    (hNS f g).trans (mul_le_mul_of_nonneg_left hprod (mul_nonneg hn hqpos.le))
  have hQb : |E2 (Krq t) f g| ≤ k * q * (1 / (1 - e) * NN) :=
    (hQ f g).trans (mul_le_mul_of_nonneg_left hprod (mul_nonneg hk hqpos.le))
  have hKb : |f ⬝ᵥ (N *ᵥ g) - E2 (signedV t) f g| ≤ κ * q * NN := hK f g hf hg
  -- assembly
  have e1 : f ⬝ᵥ (N *ᵥ g) - (oForm m f g + lForm m t f g) =
      (f ⬝ᵥ (N *ᵥ g) - E2 (signedV t) f g) + Enu f * Enu g +
        (oForm m df dg + lForm m t df dg - (oForm m f g + lForm m t f g)) +
        E2 (Knon t) f g + -E2 (Krq t) f g := by
    rw [E2_signed, hS]; ring
  have hesg : esgND q r e Γ κ n k * q * NN = κ * q * NN + cgC e * NN +
      6 * (DgC e * Γ * r * NN) + (n * q * (1 / (1 - e) * NN) + k * q * (1 / (1 - e) * NN)) := by
    unfold esgND
    have h1e : 1 - e ≠ 0 := by linarith
    field_simp
  rw [e1, hesg]
  have t1 := abs_add_le ((f ⬝ᵥ (N *ᵥ g) - E2 (signedV t) f g) + Enu f * Enu g +
    (oForm m df dg + lForm m t df dg - (oForm m f g + lForm m t f g)) + E2 (Knon t) f g)
    (-E2 (Krq t) f g)
  have t2 := abs_add_le ((f ⬝ᵥ (N *ᵥ g) - E2 (signedV t) f g) + Enu f * Enu g +
    (oForm m df dg + lForm m t df dg - (oForm m f g + lForm m t f g))) (E2 (Knon t) f g)
  have t3 := abs_add_le ((f ⬝ᵥ (N *ᵥ g) - E2 (signedV t) f g) + Enu f * Enu g)
    (oForm m df dg + lForm m t df dg - (oForm m f g + lForm m t f g))
  have t4 := abs_add_le (f ⬝ᵥ (N *ᵥ g) - E2 (signedV t) f g) (Enu f * Enu g)
  rw [abs_neg] at t1
  linarith

end Main

end Sarkozy.SignedDecompCrude
