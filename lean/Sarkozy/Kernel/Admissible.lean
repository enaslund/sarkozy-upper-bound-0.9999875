module

public import Sarkozy.Kernel.AdmissibleRates

@[expose] public section

/-!
# The actual-square kernel for every admissible triple

This module proves the paper's `prop:record:kernel20`, parts (i), (ii) and (iii), for every
triple `(β, κ, η)` admissible in the sense of `def:kernel-conditions` (`KernelAdmissible`):
moduli `D ≤ C_D N^κ`, cutoffs `C_H⁻¹ N^(β/2) ≤ H ≤ C_H N^(β/2)`, saving `N^(-β/6)`, with one
pair of constants `C, N₀` depending only on `β, κ, η, C_D, C_H` for all three parts
(`prop_kernel20`). The triple of `cor:kernel20` is admissible (`cor_kernel20_admissible`,
`AdmissibleRates.lean`), and `prop_kernel20_cor` is the resulting instance.

The proof is that of `KernelEstimate.lean` with symbolic exponents: the uniform
approximation `admissible_kernel_rate` (the analogue of `general_kernel_rate`, from upstream
`finite_kernel_uniform` with the internal major-arc exponent `arcExp β κ` and the rates of
`AdmissibleRates.lean`), the pairing bound `admissible_pairing_rootDatum` (the analogue of
`kernel_pairing_rootDatum`) and the root classes of `RootClasses.lean`. Only (E1), (E4) and
the positivity of `β, κ` enter, through `KernelWindow β κ` (`kernelWindow_of_admissible`); the
statements for the window hold more generally (`rem:record:K20-range` discusses the range of
the paper's own conditions; this argument uses different internal arcs).
-/

namespace Sarkozy

section
open Finset
open scoped ComplexConjugate BigOperators
namespace Kernel

/-- The exponent `δ` of the threshold: the least of `β/2`, `θ`, `θ - κ - β/2`,
`1 - θ - κ - β/2`, with `θ = arcExp β κ`. -/
noncomputable def admThresholdExp (β κ : ℝ) : ℝ :=
  min (min (β / 2) (arcExp β κ)) (min (arcExp β κ - κ - β / 2) (1 - arcExp β κ - κ - β / 2))

/-- The threshold `N₀ = ⌈K^(1/δ)⌉`, `K = max 8 (4 C_D C_H)`. -/
noncomputable def admThreshold (β κ CD CH : ℝ) : ℕ :=
  ⌈(max 8 (4 * CD * CH)) ^ (1 / admThresholdExp β κ)⌉₊

lemma admThresholdExp_pos {β κ : ℝ} (hw : KernelWindow β κ) : 0 < admThresholdExp β κ := by
  obtain ⟨_, hθ0, _, h1, h2, _, _, _⟩ := window_facts hw
  have hβ := hw.1
  unfold admThresholdExp
  apply lt_min (lt_min (by linarith) hθ0) (lt_min (by linarith) (by linarith))

/-- **Uniform kernel approximation at an admissible triple** (`lem:record:K20-approx`):
for `N ≥ N₀`, an even `D ≤ C_D N^κ` with a root class, and `C_H⁻¹ N^(β/2) ≤ H ≤ C_H N^(β/2)`,
`‖S(α) - S₀(α)‖ ≤ C H^(-1/3)`; stated for every `(β, κ)` in `KernelWindow`, which contains
every admissible triple. -/
theorem admissible_kernel_rate (β κ : ℝ) (hwin : KernelWindow β κ)
    (CD CH : ℝ) (hCD : 1 ≤ CD) (hCH : 1 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ D : ℕ, 2 ∣ D → 0 < D → (D : ℝ) ≤ CD * (N : ℝ) ^ κ →
      ∀ (r : ℤ) (ρ : RootClassDatum D r),
      ∀ H : ℝ, CH⁻¹ * (N : ℝ) ^ (β / 2) ≤ H → H ≤ CH * (N : ℝ) ^ (β / 2) →
      ∀ α : ℝ, ‖finiteSquareKernel (termSign N D H) (termWeight N D r ρ H) N.sqrt N α -
        ∑ x : CentreIndex H D, centreCoeff H D r x * normalizedLinearSum N (α - centre H D x)‖ ≤
          C * H ^ (-(1 : ℝ) / 3) := by
  refine ⟨admRateConstant β κ CD CH, admRateConstant_pos β κ CD CH hCD hCH,
    admThreshold β κ CD CH, ?_⟩
  intro N hN D h2 hDpos hD r ρ H hHlo hHhi α
  obtain ⟨hε, hθ0, hθ, hθ1, hθ2, _, _, _⟩ := window_facts hwin
  have hβ := hwin.1
  have hκ := hwin.2.1
  set θ := arcExp β κ with hθdef
  set δ := admThresholdExp β κ with hδdef
  have hδ : 0 < δ := admThresholdExp_pos hwin
  have hδ1 : δ ≤ β / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ θ := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ θ - κ - β / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ4 : δ ≤ 1 - θ - κ - β / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hCD0 : 0 ≤ CD := by linarith
  have hCH0 : 0 < CH := by linarith
  set K := max 8 (4 * CD * CH) with hKdef
  have hK8 : (8 : ℝ) ≤ K := le_max_left _ _
  have hK4 : 4 * CD * CH ≤ K := le_max_right _ _
  have hK0 : 0 < K := by linarith
  have hKN : K ^ (1 / δ) ≤ (N : ℝ) := by
    have h : ((admThreshold β κ CD CH : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact (Nat.le_ceil _).trans h
  have hK1 : 1 ≤ K ^ (1 / δ) := Real.one_le_rpow (by linarith) (by positivity)
  have hn1 : (1 : ℝ) ≤ N := hK1.trans hKN
  have hn0 : (0 : ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by exact_mod_cast hn1
  have hroot : K ≤ (N : ℝ) ^ δ := by
    have h := Real.rpow_le_rpow (by positivity) hKN hδ.le
    rw [← Real.rpow_mul hK0.le, show 1 / δ * δ = 1 by field_simp, Real.rpow_one] at h
    exact h
  have hpow : ∀ e : ℝ, δ ≤ e → K ≤ (N : ℝ) ^ e :=
    fun e he => hroot.trans (adm_rpow_mono hn1 he)
  have hH1 : 1 ≤ H := by
    have h1 : CH⁻¹ * (4 * CD * CH) ≤ CH⁻¹ * (N : ℝ) ^ (β / 2) :=
      mul_le_mul_of_nonneg_left (hK4.trans (hpow _ hδ1)) (inv_nonneg.mpr hCH0.le)
    have h2 : CH⁻¹ * (4 * CD * CH) = 4 * CD := by field_simp
    linarith
  have hH0 : 0 < H := by linarith
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDpos
  have hP0 : (0 : ℝ) ≤ (ρ.period : ℝ) := Nat.cast_nonneg _
  have hPD : (ρ.period : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hDpos ρ.period_dvd
  have hDH : 1 ≤ (D : ℝ) * H := by nlinarith
  have hDHn : (D : ℝ) * H ≤ CD * CH * (N : ℝ) ^ (κ + β / 2) := by
    calc (D : ℝ) * H ≤ (CD * (N : ℝ) ^ κ) * (CH * (N : ℝ) ^ (β / 2)) := by
          apply mul_le_mul hD hHhi hH0.le (by positivity)
      _ = CD * CH * ((N : ℝ) ^ κ * (N : ℝ) ^ (β / 2)) := by ring
      _ = CD * CH * (N : ℝ) ^ (κ + β / 2) := by rw [← Real.rpow_add hn0]
  have hLD : (⌈(D : ℝ) * H⌉₊ : ℝ) ≤ 2 * (D : ℝ) * H := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ (D : ℝ) * H by linarith)
    linarith
  have hmodel : (D : ℝ) * H ≤ (⌈(D : ℝ) * H⌉₊ : ℝ) := Nat.le_ceil _
  have hp7 : 0 < (N : ℝ) ^ (1 - θ) := Real.rpow_pos_of_pos hn0 _
  have hT : 0 < ⌈(N : ℝ) ^ (1 - θ)⌉₊ := Nat.ceil_pos.mpr hp7
  have hTlo : (N : ℝ) ^ (1 - θ) ≤ (⌈(N : ℝ) ^ (1 - θ)⌉₊ : ℝ) := Nat.le_ceil _
  have hThi : (⌈(N : ℝ) ^ (1 - θ)⌉₊ : ℝ) ≤ 2 * (N : ℝ) ^ (1 - θ) := by
    have h := Nat.ceil_lt_add_one hp7.le
    have h1 : 1 ≤ (N : ℝ) ^ (1 - θ) := Real.one_le_rpow hn1 (by linarith)
    linarith
  have hT1 : (1 : ℝ) ≤ (⌈(N : ℝ) ^ (1 - θ)⌉₊ : ℝ) := by exact_mod_cast hT
  have hLT : 2 * ⌈(D : ℝ) * H⌉₊ ≤ ⌈(N : ℝ) ^ (1 - θ)⌉₊ + 1 := by
    have h1 : 2 * (⌈(D : ℝ) * H⌉₊ : ℝ) ≤ (N : ℝ) ^ (1 - θ) := by
      calc 2 * (⌈(D : ℝ) * H⌉₊ : ℝ) ≤ 4 * ((D : ℝ) * H) := by linarith
        _ ≤ 4 * (CD * CH * (N : ℝ) ^ (κ + β / 2)) := by gcongr
        _ = (4 * CD * CH) * (N : ℝ) ^ (κ + β / 2) := by ring
        _ ≤ (N : ℝ) ^ (1 - θ - κ - β / 2) * (N : ℝ) ^ (κ + β / 2) := by
          gcongr
          exact hK4.trans (hpow _ hδ4)
        _ = (N : ℝ) ^ (1 - θ) := by rw [← Real.rpow_add hn0]; congr 1; ring
    have h2 : ((2 * ⌈(D : ℝ) * H⌉₊ : ℕ) : ℝ) ≤ (⌈(N : ℝ) ^ (1 - θ)⌉₊ : ℝ) := by
      push_cast
      linarith
    have h3 : 2 * ⌈(D : ℝ) * H⌉₊ ≤ ⌈(N : ℝ) ^ (1 - θ)⌉₊ := by exact_mod_cast h2
    omega
  have hX : (8 : ℝ) ≤ (N : ℝ) ^ θ := hK8.trans (hpow _ hδ2)
  have hLX : (⌈(D : ℝ) * H⌉₊ : ℝ) ≤ (N : ℝ) ^ θ := by
    have h9 := hpow (θ - κ - β / 2) hδ3
    have hK2 : 2 * CD * CH ≤ (N : ℝ) ^ (θ - κ - β / 2) := by nlinarith
    calc (⌈(D : ℝ) * H⌉₊ : ℝ) ≤ 2 * ((D : ℝ) * H) := by linarith
      _ ≤ 2 * (CD * CH * (N : ℝ) ^ (κ + β / 2)) := by gcongr
      _ = (2 * CD * CH) * (N : ℝ) ^ (κ + β / 2) := by ring
      _ ≤ (N : ℝ) ^ (θ - κ - β / 2) * (N : ℝ) ^ (κ + β / 2) := by gcongr
      _ = (N : ℝ) ^ θ := by rw [← Real.rpow_add hn0]; congr 1; ring
  have hXN : (N : ℝ) ^ θ ≤ N := Real.rpow_le_self_of_one_le hn1 (by linarith)
  obtain ⟨hM, hlo, hhi, hMn⟩ := natural_sqrt_bounds N hN1
  obtain ⟨q, hq, w, hw, hwn⟩ := rootWeight_fourier N D ρ.period ρ.base ρ.period_pos H hH0.le
  have hf := finite_kernel_uniform (termSign N D H) (termWeight N D r ρ H) (termPeriod N D r ρ H)
    (fun T => Nat.mul_pos ρ.period_pos (sieveTermPeriod_pos _ ∅ T.val))
    (fun T => rootTermWeight_periodic N D ρ.period ρ.base T.val)
    (fun _ => (ρ.period : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun T m => norm_rootTermWeight N D ρ.period ρ.base T.val m)
    (centre H D) (centreCoeff H D r) ⌈(D : ℝ) * H⌉₊ ⌈(N : ℝ) ^ (1 - θ)⌉₊
    ((N : ℝ) ^ θ) (2^64 * H^(-(1 : ℝ)/3)) hT hLT
    (fun x => centre_den_le D H hH0.le hDpos x) hX hLX (by positivity)
    (fun b hb => termCoefficient_model_bound N D r ρ H h2 hDpos hH0 b
      (by exact_mod_cast hb.trans hXN))
    w (fun a : ZMod q => (a.val : ℝ) / q)
    (fun m => by
      unfold termSign termWeight
      rw [rootTerm_sum, hw m]) N.sqrt N hM hlo hhi α
  refine hf.trans ?_
  have hcost := termCost N D r ρ H hH0.le
  have hwz := centreCoeff_sum D r H hH0.le ⌈(D : ℝ) * H⌉₊ hmodel hDpos
  have hX0 : 0 ≤ (N : ℝ) ^ θ := by positivity
  calc _ ≤ 2^64 * H^(-(1 : ℝ)/3) +
        (H * (2 * (ρ.period : ℝ) * H + 1) * ρ.period) *
          (4 * (N : ℝ) ^ θ + 8 * Real.pi * N / ((⌈(N : ℝ) ^ (1 - θ)⌉₊ : ℝ) + 1)) *
            N.sqrt / N +
        ((ρ.period : ℝ) * H) * (4 * (N.sqrt : ℝ) / N) * Real.sqrt
          (5 * N.sqrt + 32 * (N.sqrt : ℝ)^2 / (N : ℝ) ^ θ +
            (64 * N.sqrt + 8 * ⌈(N : ℝ) ^ (1 - θ)⌉₊) * (1 + Real.log ⌈(N : ℝ) ^ (1 - θ)⌉₊)) +
        (⌈(D : ℝ) * H⌉₊ : ℝ)^2 * ((⌈(N : ℝ) ^ (1 - θ)⌉₊ : ℝ) * ⌈(D : ℝ) * H⌉₊ / N) := by
        gcongr
    _ ≤ _ := adm_all β κ hwin (N : ℝ) (ρ.period : ℝ) (D : ℝ) H
        (⌈(N : ℝ) ^ (1 - θ)⌉₊ : ℝ) (N.sqrt : ℝ) (⌈(D : ℝ) * H⌉₊ : ℝ)
        CD CH hn1 hP0 hPD hD1 hD hH1 hHhi hCD hCH hT1
        (by linarith) hThi (Nat.cast_nonneg _) hLD (Nat.cast_nonneg _) hMn

/-- **The actual-square kernel at an admissible triple, for an even modulus with a root
class** (`prop:record:kernel20`, from `lem:kernel-depth-classes`): the analogue of
`kernel_pairing_rootDatum` with `D ≤ C_D N^κ`, `C_H⁻¹ N^(β/2) ≤ H ≤ C_H N^(β/2)` and saving
`N^(-β/6)`; stated for every `(β, κ)` in `KernelWindow`. -/
theorem admissible_pairing_rootDatum (β κ : ℝ) (hwin : KernelWindow β κ)
    (CD CH : ℝ) (hCD : 1 ≤ CD) (hCH : 1 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ D : ℕ, 2 ∣ D → 0 < D → (D : ℝ) ≤ CD * (N : ℝ) ^ κ →
      ∀ H : ℝ, CH⁻¹ * (N : ℝ) ^ (β / 2) ≤ H → H ≤ CH * (N : ℝ) ^ (β / 2) →
      ∀ a b : ℤ, RootClassDatum D (b - a) →
      ∀ F J : ℤ →₀ ℂ,
        (∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD (D : ℤ)]) →
        (∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD (D : ℤ)]) →
        (∀ x ∈ F.support, ∀ y ∈ J.support, x < y) →
        (∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) →
        ‖(D : ℂ) * ∑ ξ ∈ frequencySet H D,
            unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
              kernelTransform N J (ξ : ℝ)‖ ≤
          C * (N : ℝ) ^ (-(β / 6)) * (l2norm F * l2norm J) / N := by
  obtain ⟨C₁, hC₁, N₁, hrate⟩ := admissible_kernel_rate β κ hwin CD CH hCD hCH
  refine ⟨C₁ * CH ^ ((1 : ℝ) / 3), by positivity, max N₁ 1, ?_⟩
  intro N hN D h2 hDpos hD H hH1 hH2 a b ρ F J hF hJ hord hnosq
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < N := (le_max_right _ _).trans hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hCH0 : 0 < CH := by linarith
  have hk := hrate N hN₁ D h2 hDpos hD (b - a) ρ H hH1 hH2
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH1
  have hδ : 0 ≤ C₁ * H ^ (-(1 : ℝ) / 3) :=
    mul_nonneg hC₁.le (Real.rpow_nonneg hH0.le _)
  have hFs : ∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N := fun x hx => ⟨(hF x hx).1, (hF x hx).2.1⟩
  have hJs : ∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N := fun y hy => ⟨(hJ y hy).1, (hJ y hy).2.1⟩
  have hordc : ∀ x y : ZMod (N+1), liftCyclic N F x * liftCyclic N J y ≠ 0 →
      x.val < y.val ∧ y.val ≤ N := by
    intro x y hxy
    have hx : (x.val : ℤ) ∈ F.support :=
      Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hxy)
    have hy : (y.val : ℤ) ∈ J.support :=
      Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hxy)
    have h1 := hord _ hx _ hy
    have h2' := (hJ _ hy).2.1
    constructor
    · exact_mod_cast h1
    · exact_mod_cast h2'
  have hsquarec : ∀ (x y : ZMod (N+1)) (m : ℕ), m ∈ range N.sqrt →
      (((m+1)^2 : ℕ) : ZMod (N+1)) = y - x → liftCyclic N F x * liftCyclic N J y = 0 := by
    intro x y m hm hxy
    by_contra hne
    obtain ⟨hlt, hyN⟩ := hordc x y hne
    have hx : (x.val : ℤ) ∈ F.support :=
      Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hne)
    have hy : (y.val : ℤ) ∈ J.support :=
      Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)
    have hm' : m + 1 ≤ N.sqrt := mem_range.mp hm
    have hsqN : (m+1)^2 ≤ N := by
      have := Nat.sqrt_le' N
      calc (m+1)^2 ≤ N.sqrt^2 := Nat.pow_le_pow_left hm' 2
        _ ≤ N := this
    have hval := congrArg ZMod.val hxy
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), ZMod.val_sub hlt.le] at hval
    apply hnosq _ hx _ hy (m+1) (by omega)
    have : ((y.val - x.val : ℕ) : ℤ) = (y.val : ℤ) - (x.val : ℤ) := by
      rw [Nat.cast_sub hlt.le]
    rw [← this, ← hval]
    push_cast
    ring
  have hbil := ordered_square_kernel_bilinear_l2 (q := N+1) N.sqrt N hNpos (by omega)
    (fun m => classWeight ρ.period ρ.base m * sieveWeight N D H m)
    (fun x : CentreIndex H D => ((centre H D x : ℚ) : ℝ))
    (centreCoeff H D (b - a)) (C₁ * H ^ (-(1 : ℝ) / 3)) hδ
    (fun α => by
      have := hk α
      rw [finiteSquareKernel_root] at this
      exact this) (liftCyclic N F) (liftCyclic N J) hordc hsquarec
  rw [sum_norm_sq_liftCyclic N F hFs, sum_norm_sq_liftCyclic N J hJs] at hbil
  have hmodel : (∑ x : CentreIndex H D, centreCoeff H D (b - a) x *
      intervalFourier N (liftCyclic N F) (-((centre H D x : ℚ) : ℝ)) *
      intervalFourier N (liftCyclic N J) ((centre H D x : ℚ) : ℝ)) =
      (D : ℂ) * ∑ ξ ∈ frequencySet H D,
        unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) * kernelTransform N J (ξ : ℝ) := by
    simp_rw [intervalFourier_liftCyclic N F hFs, intervalFourier_liftCyclic N J hJs]
    unfold centreCoeff centre
    rw [Finset.sum_coe_sort (range D ×ˢ frequencySet H D)
      (fun y : ℕ × ℚ => expPhase ((y.1 : ℝ) * ((b - a : ℤ) : ℝ) / D) * unitQuadraticAverage y.2 *
        kernelTransform N F (-((((y.1 : ℚ) / D + y.2 : ℚ)) : ℝ)) *
        kernelTransform N J ((((y.1 : ℚ) / D + y.2 : ℚ)) : ℝ))]
    rw [Finset.sum_product]
    have hph := pairing_phase N D hDpos F J a b (fun x hx => (hF x hx).2.2)
      (fun y hy => (hJ y hy).2.2) (frequencySet H D) unitQuadraticAverage
    simp_rw [mul_assoc] at hph ⊢
    exact hph
  rw [hmodel] at hbil
  have hsave := adm_cutoff_saving N H CH β hn1 hCH0 hH1
  calc _ ≤ C₁ * H ^ (-(1 : ℝ) / 3) * Real.sqrt (∑ n ∈ F.support, ‖F n‖^2) *
        Real.sqrt (∑ n ∈ J.support, ‖J n‖^2) / N := hbil
    _ ≤ C₁ * (CH ^ ((1 : ℝ) / 3) * (N : ℝ) ^ (-(β / 6))) *
        Real.sqrt (∑ n ∈ F.support, ‖F n‖^2) * Real.sqrt (∑ n ∈ J.support, ‖J n‖^2) / N := by
        gcongr
    _ = _ := by unfold l2norm; ring

/-- **The actual-square kernel** (`prop:record:kernel20`, parts (i), (ii), (iii)), for every
triple `(β, κ, η)` admissible in the sense of `def:kernel-conditions`.

Fix `C_D, C_H ≥ 1`. There are `C > 0` and `N₀`, depending only on `β, κ, η, C_D, C_H`, such
that for all `N ≥ N₀` and `C_H⁻¹ N^(β/2) ≤ H ≤ C_H N^(β/2)` the following hold, where for a
modulus `D` and integers `a, b` the *pairing bound* means: for all finitely supported
`F, J : ℤ → ℂ` supported in `[1,N]` and in the residue classes `a`, resp. `b`, modulo `D`,
with `x < y` and `y - x` not the square of a positive integer for all `x ∈ supp F`,
`y ∈ supp J`, `|D ∑_{ξ ∈ Ξ_{H,D}} g(ξ) F̂(-ξ) Ĵ(ξ)| ≤ C N^(-β/6) ‖F‖₂ ‖J‖₂ / N`
(`eq:record:K20`).

(i) For `D = 8d ≤ C_D N^κ`, `d` odd, and `b - a` a strict square class modulo `D`.
(ii) For `D = 8d ≤ C_D N^κ`, `d` odd, and `b - a` satisfying the hypotheses of (ii)
  (`IsDividedSquareClass d P₀ m (b - a)`); the rescaling identity of (ii) is not formalized.
(iii) For `D ≤ C_D N^κ` and `b - a` a nonvanishing square class modulo `D`
  (`IsNonvanishingSquareClass D (b - a)`, which includes `v₂(D) ≥ 3`). -/
theorem prop_kernel20 (β κ η : ℝ) (hadm : KernelAdmissible β κ η)
    (CD CH : ℝ) (hCD : 1 ≤ CD) (hCH : 1 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ H : ℝ, CH⁻¹ * (N : ℝ) ^ (β / 2) ≤ H → H ≤ CH * (N : ℝ) ^ (β / 2) →
      -- (i)
      (∀ d : ℕ, Odd d → ((8 * d : ℕ) : ℝ) ≤ CD * (N : ℝ) ^ κ →
        ∀ a b : ℤ, IsStrictSquareClass d (b - a) →
        ∀ F J : ℤ →₀ ℂ,
          (∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD ((8 * d : ℕ) : ℤ)]) →
          (∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD ((8 * d : ℕ) : ℤ)]) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, x < y) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) →
          ‖((8 * d : ℕ) : ℂ) * ∑ ξ ∈ frequencySet H (8 * d),
              unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
                kernelTransform N J (ξ : ℝ)‖ ≤
            C * (N : ℝ) ^ (-(β / 6)) * (l2norm F * l2norm J) / N) ∧
      -- (ii)
      (∀ d : ℕ, Odd d → ((8 * d : ℕ) : ℝ) ≤ CD * (N : ℝ) ^ κ →
        ∀ (P₀ : Finset ℕ) (m : ℕ → ℕ) (a b : ℤ), IsDividedSquareClass d P₀ m (b - a) →
        ∀ F J : ℤ →₀ ℂ,
          (∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD ((8 * d : ℕ) : ℤ)]) →
          (∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD ((8 * d : ℕ) : ℤ)]) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, x < y) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) →
          ‖((8 * d : ℕ) : ℂ) * ∑ ξ ∈ frequencySet H (8 * d),
              unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
                kernelTransform N J (ξ : ℝ)‖ ≤
            C * (N : ℝ) ^ (-(β / 6)) * (l2norm F * l2norm J) / N) ∧
      -- (iii)
      (∀ D : ℕ, (D : ℝ) ≤ CD * (N : ℝ) ^ κ →
        ∀ a b : ℤ, IsNonvanishingSquareClass D (b - a) →
        ∀ F J : ℤ →₀ ℂ,
          (∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD (D : ℤ)]) →
          (∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD (D : ℤ)]) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, x < y) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) →
          ‖(D : ℂ) * ∑ ξ ∈ frequencySet H D,
              unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
                kernelTransform N J (ξ : ℝ)‖ ≤
            C * (N : ℝ) ^ (-(β / 6)) * (l2norm F * l2norm J) / N) := by
  obtain ⟨C, hC, N₀, hmain⟩ :=
    admissible_pairing_rootDatum β κ (kernelWindow_of_admissible hadm) CD CH hCD hCH
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN H hH1 hH2
  have hiii : ∀ D : ℕ, (D : ℝ) ≤ CD * (N : ℝ) ^ κ →
      ∀ a b : ℤ, IsNonvanishingSquareClass D (b - a) →
      ∀ F J : ℤ →₀ ℂ,
        (∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD (D : ℤ)]) →
        (∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD (D : ℤ)]) →
        (∀ x ∈ F.support, ∀ y ∈ J.support, x < y) →
        (∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) →
        ‖(D : ℂ) * ∑ ξ ∈ frequencySet H D,
            unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
              kernelTransform N J (ξ : ℝ)‖ ≤
          C * (N : ℝ) ^ (-(β / 6)) * (l2norm F * l2norm J) / N := by
    intro D hD a b hab F J hF hJ hord hsq
    have hD0 : 0 < D := by
      rcases Nat.eq_zero_or_pos D with h | h
      · exfalso
        have := hab.1
        rw [h] at this
        simp at this
      · exact h
    have h2 : 2 ∣ D := by
      have h3 := hab.1
      exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hD0.ne').mpr (by omega)
    obtain ⟨ρ⟩ := rootClassDatum_of_nonvanishing D hD0 (b - a) hab
    exact hmain N hN D h2 hD0 hD H hH1 hH2 a b ρ F J hF hJ hord hsq
  refine ⟨?_, ?_, hiii⟩
  · intro d hd hD a b hab F J hF hJ hord hsq
    exact hiii (8 * d) hD a b (isNonvanishing_of_strict d hd (b - a) hab) F J hF hJ hord hsq
  · intro d hd hD P₀ m a b hab F J hF hJ hord hsq
    exact hiii (8 * d) hD a b (dividedSquareClass_nonvanishing d hd P₀ m (b - a) hab)
      F J hF hJ hord hsq

/-- `prop_kernel20` at the admissible triple `(1/20, 1/20, 17/100)` of `cor:kernel20`. -/
theorem prop_kernel20_cor (CD CH : ℝ) (hCD : 1 ≤ CD) (hCH : 1 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ H : ℝ, CH⁻¹ * (N : ℝ) ^ ((1 / 20 : ℝ) / 2) ≤ H → H ≤ CH * (N : ℝ) ^ ((1 / 20 : ℝ) / 2) →
      -- (i)
      (∀ d : ℕ, Odd d → ((8 * d : ℕ) : ℝ) ≤ CD * (N : ℝ) ^ (1 / 20 : ℝ) →
        ∀ a b : ℤ, IsStrictSquareClass d (b - a) →
        ∀ F J : ℤ →₀ ℂ,
          (∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD ((8 * d : ℕ) : ℤ)]) →
          (∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD ((8 * d : ℕ) : ℤ)]) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, x < y) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) →
          ‖((8 * d : ℕ) : ℂ) * ∑ ξ ∈ frequencySet H (8 * d),
              unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
                kernelTransform N J (ξ : ℝ)‖ ≤
            C * (N : ℝ) ^ (-((1 / 20 : ℝ) / 6)) * (l2norm F * l2norm J) / N) ∧
      -- (ii)
      (∀ d : ℕ, Odd d → ((8 * d : ℕ) : ℝ) ≤ CD * (N : ℝ) ^ (1 / 20 : ℝ) →
        ∀ (P₀ : Finset ℕ) (m : ℕ → ℕ) (a b : ℤ), IsDividedSquareClass d P₀ m (b - a) →
        ∀ F J : ℤ →₀ ℂ,
          (∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD ((8 * d : ℕ) : ℤ)]) →
          (∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD ((8 * d : ℕ) : ℤ)]) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, x < y) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) →
          ‖((8 * d : ℕ) : ℂ) * ∑ ξ ∈ frequencySet H (8 * d),
              unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
                kernelTransform N J (ξ : ℝ)‖ ≤
            C * (N : ℝ) ^ (-((1 / 20 : ℝ) / 6)) * (l2norm F * l2norm J) / N) ∧
      -- (iii)
      (∀ D : ℕ, (D : ℝ) ≤ CD * (N : ℝ) ^ (1 / 20 : ℝ) →
        ∀ a b : ℤ, IsNonvanishingSquareClass D (b - a) →
        ∀ F J : ℤ →₀ ℂ,
          (∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD (D : ℤ)]) →
          (∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD (D : ℤ)]) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, x < y) →
          (∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) →
          ‖(D : ℂ) * ∑ ξ ∈ frequencySet H D,
              unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
                kernelTransform N J (ξ : ℝ)‖ ≤
            C * (N : ℝ) ^ (-((1 / 20 : ℝ) / 6)) * (l2norm F * l2norm J) / N) :=
  prop_kernel20 (1 / 20) (1 / 20) (17 / 100) cor_kernel20_admissible CD CH hCD hCH

end Kernel
end
end Sarkozy
