module

public import Sarkozy.SpectralC.Commutant
public import Sarkozy.SpectralC.CovariantFields

@[expose] public section

/-!
# Grams of intertwiners (`lem:spec:affpair`(d)(ii))

`paper/sections/14_spectral.tex`, `lem:spec:affpair`(d)(ii). Let `Aff_p` act on `(𝒴, ν)` as in (c)
(`AffAction`) and let `Y, Y' : L²_0(𝔽_p) → L²(ν)` be real kernels `(Yh)(y) = ∑_a Y(y, a) h(a)`
intertwining the two actions: `Y(h ∘ γ) = (Yh) ∘ γ`. Then `⟨Yf, Y'g⟩_ν = ⟨f, T g⟩` with the real
operator `T = Y^*Y'` (`gramOp`, kernel `p E_ν Y(·, a) Y'(·, b)`), which commutes with `Aff_p`; so
on `L²_0` it is `α_T I + γ_T C` (`intertwiner_gram`). For `Y' = Y` and `p ≡ 3 (mod 4)` the
coefficient `γ_T` vanishes: `Y^*Y = α_T I` on `L²_0`, `α_T = tr(Y^*Y)/(p − 1)`
(`intertwiner_gram_self`).

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {𝒴 : Type*} [Fintype 𝒴]

/-- The operator `(Yh)(y) = ∑_a Y(y, a) h(a)` of a real kernel. -/
noncomputable def kerMap (Y : 𝒴 → ZMod p → ℝ) (h : ZMod p → ℂ) (y : 𝒴) : ℂ :=
  ∑ a, (Y y a : ℂ) * h a

/-- The kernel of `T = Y^*Y'`: `T(a, b) = p E_ν Y(·, a) Y'(·, b)`. -/
noncomputable def gramKer (ν : 𝒴 → ℝ) (Y Y' : 𝒴 → ZMod p → ℝ) (a b : ZMod p) : ℝ :=
  (p : ℝ) * ∑ y, ν y * Y y a * Y' y b

/-- `T = Y^*Y'`: `⟨Yf, Y'g⟩_ν = ⟨f, Tg⟩` (`ip_kerMap`). -/
noncomputable def gramOp (ν : 𝒴 → ℝ) (Y Y' : 𝒴 → ZMod p → ℝ) (h : ZMod p → ℂ) (a : ZMod p) : ℂ :=
  matOp (gramKer ν Y Y') h a

/-- `⟨Yf, Y'g⟩_ν = ⟨f, Y^*Y' g⟩`. -/
theorem ip_kerMap (ν : 𝒴 → ℝ) (Y Y' : 𝒴 → ZMod p → ℝ) (f g : ZMod p → ℂ) :
    ∑ y, (ν y : ℂ) * (conj (kerMap Y f y) * kerMap Y' g y) = ip f (gramOp ν Y Y' g) := by
  unfold kerMap gramOp matOp gramKer ip
  have hpC := p_ne_zero_C (p := p)
  simp_rw [map_sum, map_mul, Complex.conj_ofReal, sum_mul_sum, mul_sum]
  push_cast
  simp_rw [sum_mul, mul_sum]
  refine sum_comm.trans ?_
  refine sum_congr rfl fun a _ => ?_
  refine sum_comm.trans ?_
  refine sum_congr rfl fun b _ => sum_congr rfl fun y _ => ?_
  field_simp

omit [Fintype 𝒴] in
/-- The intertwining relation makes the kernel covariant: `Y(γy, γa) = Y(y, a)`. -/
lemma kerMap_cov {ν : 𝒴 → ℝ} (G : AffAction p 𝒴 ν) (Y : 𝒴 → ZMod p → ℝ)
    (hY : ∀ (s c : ZMod p), s ≠ 0 → IsSquare s → ∀ (h : ZMod p → ℂ) (y : 𝒴),
      kerMap Y (fun a => h (s * a + c)) y = kerMap Y h (G.act s c y))
    (s c : ZMod p) (hs : s ≠ 0) (hsq : IsSquare s) (y : 𝒴) (a : ZMod p) :
    Y (G.act s c y) (s * a + c) = Y y a := by
  have h := hY s c hs hsq (fun t => if t = s * a + c then 1 else 0) y
  unfold kerMap at h
  have hinj : ∀ t, (s * t + c = s * a + c) ↔ t = a := by
    intro t
    constructor
    · intro h1; exact mul_left_cancel₀ hs (by linear_combination h1)
    · intro h1; rw [h1]
  simp_rw [hinj] at h
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] at h
  exact_mod_cast h.symm

/-- **`lem:spec:affpair`(d)(ii)**: `T = Y^*Y'` commutes with `Aff_p`, so on `L²_0` it is
`α_T I + γ_T C`. -/
theorem intertwiner_gram (hp2 : p ≠ 2) {ν : 𝒴 → ℝ} (G : AffAction p 𝒴 ν)
    (Y Y' : 𝒴 → ZMod p → ℝ)
    (hY : ∀ (s c : ZMod p), s ≠ 0 → IsSquare s → ∀ (h : ZMod p → ℂ) (y : 𝒴),
      kerMap Y (fun a => h (s * a + c)) y = kerMap Y h (G.act s c y))
    (hY' : ∀ (s c : ZMod p), s ≠ 0 → IsSquare s → ∀ (h : ZMod p → ℂ) (y : 𝒴),
      kerMap Y' (fun a => h (s * a + c)) y = kerMap Y' h (G.act s c y)) :
    ∃ αT γT : ℝ, ∀ (h : ZMod p → ℂ), meanC h = 0 → ∀ a,
      gramOp ν Y Y' h a = αT * h a + γT * gaussOp h a := by
  apply commutant_on_meanZero hp2
  intro s c hs hsq h a
  -- the Gram kernel is invariant
  have hK : ∀ b, gramKer ν Y Y' (s * a + c) (s * b + c) = gramKer ν Y Y' a b := by
    intro b
    unfold gramKer
    congr 1
    rw [← (G.bij s c hs hsq).sum_comp]
    apply sum_congr rfl
    intro y _
    rw [G.pres s c y hs hsq, kerMap_cov G Y hY s c hs hsq, kerMap_cov G Y' hY' s c hs hsq]
  unfold matOp
  have hre : ∑ b, (gramKer ν Y Y' (s * a + c) b : ℂ) * h b =
      ∑ b, (gramKer ν Y Y' (s * a + c) (s * b + c) : ℂ) * h (s * b + c) := by
    have hbij : Function.Bijective (fun b : ZMod p => s * b + c) := by
      constructor
      · intro b b' hb
        exact mul_left_cancel₀ hs (by simpa using hb)
      · intro b
        exact ⟨s⁻¹ * (b - c), by field_simp; ring⟩
    exact (hbij.sum_comp (fun b => (gramKer ν Y Y' (s * a + c) b : ℂ) * h b)).symm
  rw [hre]
  apply sum_congr rfl
  intro b _
  rw [hK b]

/-- **`lem:spec:affpair`(d)(ii), the Gram of one intertwiner** (`p ≡ 3 (mod 4)`):
`Y^*Y = α_T I` on `L²_0`. -/
theorem intertwiner_gram_self (hp2 : p ≠ 2) (hp3 : p % 4 = 3) {ν : 𝒴 → ℝ}
    (G : AffAction p 𝒴 ν) (Y : 𝒴 → ZMod p → ℝ)
    (hY : ∀ (s c : ZMod p), s ≠ 0 → IsSquare s → ∀ (h : ZMod p → ℂ) (y : 𝒴),
      kerMap Y (fun a => h (s * a + c)) y = kerMap Y h (G.act s c y)) :
    ∃ αT : ℝ, (∀ (h : ZMod p → ℂ), meanC h = 0 → ∀ a, gramOp ν Y Y h a = αT * h a) ∧
      trace0 (gramOp ν Y Y) = ((p : ℂ) - 1) * αT := by
  obtain ⟨αT, γT, hT⟩ := intertwiner_gram hp2 G Y Y hY hY
  -- `Y^*Y` is self-adjoint, so `γ_T = 0`
  have hsym : ∀ f g : ZMod p → ℂ, meanC f = 0 → meanC g = 0 →
      ip f (fun a => (αT : ℂ) * g a + (γT : ℂ) * gaussOp g a) =
        ip (fun a => (αT : ℂ) * f a + (γT : ℂ) * gaussOp f a) g := by
    intro f g hf hg
    have h1 : (fun a => (αT : ℂ) * g a + (γT : ℂ) * gaussOp g a) = gramOp ν Y Y g :=
      funext fun a => (hT g hg a).symm
    have h2 : (fun a => (αT : ℂ) * f a + (γT : ℂ) * gaussOp f a) = gramOp ν Y Y f :=
      funext fun a => (hT f hf a).symm
    rw [h1, h2, ← ip_kerMap, ← conj_ip, ← ip_kerMap, map_sum]
    apply sum_congr rfl
    intro y _
    rw [map_mul, Complex.conj_ofReal, map_mul, Complex.conj_conj, mul_comm (conj _)]
  have hγ : γT = 0 := (commutant_selfAdjoint_iff hp2 hp3 αT γT).mp hsym
  have hmain : ∀ (h : ZMod p → ℂ), meanC h = 0 → ∀ a, gramOp ν Y Y h a = αT * h a := by
    intro h hh a
    rw [hT h hh a, hγ]
    simp
  refine ⟨αT, hmain, ?_⟩
  unfold trace0
  have hξ : ∀ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
      ip (ech ξ) (gramOp ν Y Y (ech ξ)) = (αT : ℂ) := by
    intro ξ hξ
    have hm : meanC (ech ξ) = 0 := by rw [meanC_ech, ite_eq_right (mem_filter.mp hξ).2]
    have : gramOp ν Y Y (ech ξ) = fun a => (αT : ℂ) * ech ξ a := funext (hmain _ hm)
    rw [this, ip_ech_smul]
  rw [sum_congr rfl hξ, sum_const, nsmul_eq_mul, card_ne_zero_filter]

end Sarkozy.SpectralC
