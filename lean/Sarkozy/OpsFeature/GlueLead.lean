module

public import Sarkozy.OpsFeature.LeadStar
public import Sarkozy.OpsCore.LeadBlock

@[expose] public section

/-!
# Glue with OPS-L: the kernel of `singForm` of prime leading forms (`hLb` at a fold block)

OPS-L's `OpsCore.LeadBlock.singForm m x₀ Λ φ ψ = ∑_j Λ_j(comp1 j φ, comp1 j ψ)` places
one-coordinate forms on the singleton sectors (`prop:signed-bounds`(b)); `LeadFold.foldLead` is
`singForm` of PG's `lForm` (`= lFormY … A₃`, `lFormY_A3`). Here:

* `comp1_eq_sum`: `comp1` is linear, `comp1 j φ a = ∑_x φ(x) C_j(x, a)` with
  `C_j(x, a) = SP(sing j)(update x₀ j a, x)`;
* **`kern_singForm_lead`**: for an operator `L` with `⟨f, L g⟩ = c · singForm(lFormY_j)(f, g)`
  (OPS-L's `opOfForm` of `w⁻¹ foldLead`, `ip_opOfForm`), its kernel is the star form
  `∑_j c_j (C_j Ξ_j) 𝖥(Φ̂_j) (C_j Ξ_j)ᵀ`: the hypothesis `hLb` of `hdom_of_units` at a fold block.

This file imports `OpsCore` and has its own umbrella `Sarkozy.OpsFeature.GlueAll`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsFeature

open Sarkozy.OpsCore Sarkozy.SignedGram

variable {K : Type} [Fintype K] [DecidableEq K] {Fp : K → Type} [∀ j, Field (Fp j)]
  [∀ j, Fintype (Fp j)] [∀ j, DecidableEq (Fp j)]

omit [∀ j, Field (Fp j)] in
/-- `comp1` is linear: `comp1 j φ a = ∑_x φ(x) SP(sing j)(update x₀ j a, x)`. -/
theorem comp1_eq_sum (mS : ∀ j, (Fin 3 → Fp j) → ℝ) (x₀ : ∀ j, Fin 3 → Fp j) (j : K)
    (φ : (∀ j, Fin 3 → Fp j) → ℝ) (a : Fin 3 → Fp j) :
    comp1 mS x₀ j φ a = ∑ x, φ x * SP mS (sing j) (Function.update x₀ j a) x := by
  unfold comp1
  simp only [mulVec, dotProduct]
  exact sum_congr rfl fun x _ => mul_comm _ _

/-- **The kernel of `singForm` of prime leading forms** (`hLb` at a fold block). -/
theorem kern_singForm_lead (hF : ∀ j, ringChar (Fp j) ≠ 2)
    (h3 : ∀ j, Fintype.card (Fp j) % 4 = 3) (mS : ∀ j, (Fin 3 → Fp j) → ℝ)
    (x₀ : ∀ j, Fin 3 → Fp j) (mP : ∀ j, (Fin 3 → Fp j) → ℝ)
    (Y : ∀ j, (Fp j → ℝ) → (Fin 3 → Fp j) → ℝ) (c : ℝ) (mB : (∀ j, Fin 3 → Fp j) → ℝ)
    (L : ((∀ j, Fin 3 → Fp j) → ℝ) →ₗ[ℝ] ((∀ j, Fin 3 → Fp j) → ℝ))
    (hL : ∀ f g, EnvelopeSteps.ip mB f (L g) =
      c * singForm mS x₀ (fun j => lFormY (mP j) tlaw (Y j)) f g)
    (x y : ∀ j, Fin 3 → Fp j) :
    EnvelopeSteps.kern mB L x y = ∑ j, (c * (Real.sqrt (Fintype.card (Fp j)))⁻¹ *
      (Fintype.card (Fp j) : ℝ)⁻¹) *
        (((Matrix.of fun z a => SP mS (sing j) (Function.update x₀ j a) z) * XiM (mP j) (Y j)) *
          foldStar (F := Fp j) *
          ((Matrix.of fun z a => SP mS (sing j) (Function.update x₀ j a) z) *
            XiM (mP j) (Y j))ᵀ) x y :=
  kern_block_lead hF h3 mP Y
    (fun j => Matrix.of fun z a => SP mS (sing j) (Function.update x₀ j a) z)
    (fun j => comp1 mS x₀ j) (fun j φ a => comp1_eq_sum mS x₀ j φ a) c mB L
    (fun f g => by rw [hL]; rfl) x y

end Sarkozy.OpsFeature
