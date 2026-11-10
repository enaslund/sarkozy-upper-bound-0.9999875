module

public import Sarkozy.OpsFeature.PaleyStars

@[expose] public section

/-!
# The kernel of the tensor of the leading stars, block by block (`lem:oct24:mask-schur`(a), (N1),
(N3))

`paper/sections/23_envelopes.tex`, `lem:oct24:mask-schur`(a), proof, first sentence: "The tensor
`⊗_𝔅 L_𝔅` is the orthogonal sum, over the choices `(p_𝔅)` of one singleton sector at every block, of
`(∏_𝔅 c_{p_𝔅})` times the lift by `Ξ = ⊗_𝔅 Ξ_{p_𝔅}` of `T = ⊗ 𝖥(Φ̂_{p_𝔅}) ⊗ ⊗ 𝖤(Φ̂_{p_𝔅})`".

**`kernel_star_product`**: if at every block the kernel of the leading star is
`K_𝔅 = ∑_p c_{𝔅,p} Ξ_{𝔅,p} 𝖥(Φ̂_p) Ξ_{𝔅,p}ᵀ` (the star form (N1), (N3) as kernels, `starB` the
fold or matching star), then the product kernel `∏_𝔅 K_𝔅(x_𝔅, y_𝔅)` is
`∑_s (∏_𝔅 c_{𝔅,s_𝔅}) (Ξ_s T_s Ξ_sᵀ)(x, y)`, the form of the hypothesis `hL` of
`hdom_of_table_paley`. With OPS-L's `kern_tensorOp` (the kernel of a tensor product of operators
relative to the product marginal is the product of the kernels) this reduces `hL` to the per-block
star form.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsFeature

open Sarkozy.Envelopes Sarkozy.EnvelopeSteps

section StarKernel

variable {n k : ℕ} {Sb : Fin n ⊕ Fin k → Type*} [∀ b, Fintype (Sb b)]
  {Fld : ∀ b, Sb b → Type*} [∀ b p, Field (Fld b p)] [∀ b p, Fintype (Fld b p)]
  [∀ b p, DecidableEq (Fld b p)] {O : Fin n ⊕ Fin k → Type*}

/-- The leading star of a block: `𝖥(Φ̂_p)` at a fold block, `𝖤(Φ̂_p)` at a matching block. -/
noncomputable def starB : ∀ (b : Fin n ⊕ Fin k) (p : Sb b),
    Matrix (featLab n k b × Fld b p) (featLab n k b × Fld b p) ℝ
  | Sum.inl _, _ => foldStar
  | Sum.inr _, _ => matchStar

omit [∀ b, Fintype (Sb b)] in
theorem starTensor_eq_prod (s : ∀ b, Sb b) (v w : Feat n k) (z z' : ∀ b, Fld b (s b)) :
    starTensor (fun i p => foldStar (F := Fld (Sum.inl i) p))
        (fun j p => matchStar (F := Fld (Sum.inr j) p)) s (v, z) (w, z') =
      ∏ b, starB (Fld := Fld) b (s b) (featEquiv n k v b, z b) (featEquiv n k w b, z' b) := by
  rw [Fintype.prod_sum_type]
  rfl

/-- The equivalence `Feat n k × (∀ b, Z b) ≃ ∀ b, featLab n k b × Z b`. -/
def featPairEquiv (Z : Fin n ⊕ Fin k → Type*) :
    Feat n k × (∀ b, Z b) ≃ (∀ b, featLab n k b × Z b) where
  toFun vz b := (featEquiv n k vz.1 b, vz.2 b)
  invFun α := ((featEquiv n k).symm fun b => (α b).1, fun b => (α b).2)
  left_inv vz := by
    obtain ⟨v, z⟩ := vz
    simp only [Equiv.symm_apply_apply]
  right_inv α := by
    funext b
    simp only [Equiv.apply_symm_apply]

/-- The star form of the leading kernel of a block, `∑_p c_p Ξ_p 𝖥(Φ̂_p) Ξ_pᵀ` ((N1), (N3)). -/
noncomputable def starKer (Ξb : ∀ b (p : Sb b), Matrix (O b) (featLab n k b × Fld b p) ℝ)
    (c : ∀ b, Sb b → ℝ) (b : Fin n ⊕ Fin k) : Matrix (O b) (O b) ℝ :=
  ∑ p, c b p • (Ξb b p * starB (Fld := Fld) b p * (Ξb b p)ᴴ)

/-- **The kernel of the tensor of the leading stars, block by block.** -/
theorem kernel_star_product
    (Ξb : ∀ b (p : Sb b), Matrix (O b) (featLab n k b × Fld b p) ℝ) (c : ∀ b, Sb b → ℝ)
    (x y : ∀ b, O b) :
    ∏ b, starKer Ξb c b (x b) (y b) =
      (∑ s : (∀ b, Sb b), (∏ b, c b (s b)) • (xiFeat Ξb s *
        starTensor (fun i p => foldStar (F := Fld (Sum.inl i) p))
          (fun j p => matchStar (F := Fld (Sum.inr j) p)) s * (xiFeat Ξb s)ᴴ)) x y := by
  simp only [starKer, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [prod_mul_distrib]
  congr 1
  -- one sector choice
  simp only [Matrix.mul_apply, conjTranspose_apply, star_trivial]
  -- the left side as a sum over families
  have hL : ∏ b, ∑ β : featLab n k b × Fld b (s b), (∑ α : featLab n k b × Fld b (s b),
      Ξb b (s b) (x b) α * starB (Fld := Fld) b (s b) α β) * Ξb b (s b) (y b) β =
      ∑ β : (∀ b, featLab n k b × Fld b (s b)), ∑ α : (∀ b, featLab n k b × Fld b (s b)),
        ∏ b, (Ξb b (s b) (x b) (α b) * starB (Fld := Fld) b (s b) (α b) (β b) *
          Ξb b (s b) (y b) (β b)) := by
    simp only [sum_mul]
    rw [Fintype.prod_sum]
    refine sum_congr rfl fun β _ => ?_
    rw [Fintype.prod_sum]
  rw [hL]
  -- the right side, relabelled
  refine (Fintype.sum_equiv (featPairEquiv (fun b => Fld b (s b))) _ _ (fun wz => ?_)).symm
  rw [sum_mul]
  refine Fintype.sum_equiv (featPairEquiv (fun b => Fld b (s b))) _ _ (fun vz => ?_)
  obtain ⟨v, z⟩ := vz
  obtain ⟨w, z'⟩ := wz
  simp only [xiFeat, xiS, starTensor_eq_prod, ← prod_mul_distrib]
  rfl

/-- **`hdom` for a checked diagonal envelope, with the leading kernel given block by block**
(B11's `hdom` of `lem:oct24:mask-schur`, diagonal witnesses F2E4, F3E3, F4E2, F5E1, F6E0): the
hypothesis `hL` of `hdom_of_table_paley` with the coefficient `c_s = ∏_𝔅 c_{𝔅,s_𝔅}`, from the
kernel of `L_ω` as the product over the blocks of the star forms `starKer` ((N1), (N3)). For a
tensor operator `L_ω = ⊗_𝔅 L_𝔅` relative to a product marginal, OPS-L's `kern_tensorOp` gives
`hLb` from `kern (m_𝔅) L_𝔅 = starKer Ξb c 𝔅`. -/
theorem hdom_of_table_paley_blocks {O : Fin n ⊕ Fin k → Type*} [∀ b, Fintype (O b)]
    [∀ b, DecidableEq (O b)] (hF : ∀ b p, ringChar (Fld b p) ≠ 2)
    (h3 : ∀ b p, Fintype.card (Fld b p) % 4 = 3) {Tb : EnvTable}
    (hT : tablePos Tb n k = true) (hC : maskCheck Tb n k = true) (hnk : Even (n + k))
    (Ξb : ∀ b (p : Sb b), Matrix (O b) (featLab n k b × Fld b p) ℝ)
    (CU : ∀ b, Matrix (featLab n k b × O b) (featLab n k b × O b) ℝ)
    (hUY : ∀ b, (maskT (fun b => (id : featLab n k b → featLab n k b)) CU b -
      maskT (fun b => (id : featLab n k b → featLab n k b)) (gramT Ξb) b).PosSemidef)
    (c : ∀ b, Sb b → ℝ) (hc0 : ∀ b p, 0 ≤ c b p) (hc1 : ∀ b p, c b p ≤ 1)
    {m : (∀ b, O b) → ℝ} {Lead Lop : ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ)}
    (hLb : ∀ x y, kern m Lead x y = ∏ b, starKer Ξb c b (x b) (y b))
    (hLop : ∀ x y, kern m Lop x y =
      liftMap CU (diagonal ((fun v => (featWeight Tb v : ℝ)) ∘ (featEquiv n k).symm)) x y) :
    OpLE m Lead Lop ∧ OpLE m (-Lead) Lop :=
  hdom_of_table_paley hF h3 hT hC hnk Ξb CU hUY (fun s => ∏ b, c b (s b))
    (fun _ => prod_nonneg fun b _ => hc0 b _)
    (fun _ => prod_le_one₀ (fun b _ => hc0 b _) fun b _ => hc1 b _) (m := m)
    (fun x y => (hLb x y).trans (kernel_star_product Ξb c x y)) hLop

end StarKernel

end Sarkozy.OpsFeature
