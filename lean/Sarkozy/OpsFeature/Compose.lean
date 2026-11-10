module

public import Sarkozy.OpsFeature.Lift
public import Sarkozy.OpsFeature.Witness

@[expose] public section

/-!
# `hdom` for the checked diagonal envelopes from per-block data
(`lem:oct24:mask-schur`(a), (c), `cert:envelopes`(b))

`paper/sections/23_envelopes.tex`, `lem:oct24:mask-schur`. **`hdom_of_table_blocks`** composes
`hdom_of_table` (the mask Schur test on every sector, no move 1) with `hLift_of_blocks` (move 4)
for the five diagonal witnesses: the tensor features `Feat n k` of W2's tables are the label words
`∀ b, featLab n k b` over the fold and matching blocks `Fin n ⊕ Fin k` (`featEquiv`; labels
`Fin 4` = centre and three arms at a fold block, `Fin 2` at a matching block), the sector maps are
tensor products of per-block maps (`xiFeat`), and `D_ω` is the lift `liftMap CU D` of the table's
diagonal by the per-block unit tables `CU`.

The remaining inputs are then per block and per label, plus the sector structure of the stars:
* `hUY`: at every block and label `a`, `U_b(a, a) ⪰ ∑_p Ξ_{b,p,a} Ξ_{b,p,a}^*` (kernels; for a
  diagonal `D` only the diagonal blocks enter, `blk = id`): `C_a ⪰` its singleton-sector part at a
  singleton label, `Q₁₂ ⪰ Π_{𝒦₁₂} ⪰ Z Z^*` at the pure-pair label;
* `hsec`, `hnorm`, `hTs`, `hL`, `hLop`, `0 ≤ c_s ≤ 1`: as in `hdom_of_table`.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace Sarkozy.OpsFeature

open Sarkozy.EnvelopeSteps Sarkozy.Envelopes

/-- The label alphabets of the tensor features: `Fin 4` (centre and three arms) at a fold block,
`Fin 2` (centre and arm) at a matching block. -/
abbrev featLab (n k : ℕ) : Fin n ⊕ Fin k → Type := Sum.elim (fun _ => Fin 4) (fun _ => Fin 2)

instance featLab_fintype (n k : ℕ) : ∀ b, Fintype (featLab n k b)
  | Sum.inl _ => inferInstanceAs (Fintype (Fin 4))
  | Sum.inr _ => inferInstanceAs (Fintype (Fin 2))

instance featLab_decEq (n k : ℕ) : ∀ b, DecidableEq (featLab n k b)
  | Sum.inl _ => inferInstanceAs (DecidableEq (Fin 4))
  | Sum.inr _ => inferInstanceAs (DecidableEq (Fin 2))

/-- `Feat n k ≃ ∀ b, featLab n k b`. -/
def featEquiv (n k : ℕ) : Feat n k ≃ (∀ b, featLab n k b) :=
  (Equiv.sumPiEquivProdPi (featLab n k)).symm

section Compose

variable {n k : ℕ} {O : Fin n ⊕ Fin k → Type*} [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)]
  {Sb : Fin n ⊕ Fin k → Type*} [∀ b, Fintype (Sb b)] {Zb : ∀ b, Sb b → Type*}
  [∀ b p, Fintype (Zb b p)] [∀ b p, DecidableEq (Zb b p)]

/-- The sector maps on the tensor features. -/
def xiFeat (Ξb : ∀ b (p : Sb b), Matrix (O b) (featLab n k b × Zb b p) ℝ) (s : ∀ b, Sb b) :
    Matrix (∀ b, O b) (Feat n k × (∀ b, Zb b (s b))) ℝ :=
  fun x vz => xiS Ξb s x (featEquiv n k vz.1, vz.2)

/-- The sum of the sector congruences `∑_s Ξ_s (diag d ⊗ I) Ξ_sᵀ` on the tensor features. -/
noncomputable def sumXi (Ξb : ∀ b (p : Sb b), Matrix (O b) (featLab n k b × Zb b p) ℝ)
    (d : Feat n k → ℝ) : Matrix (∀ b, O b) (∀ b, O b) ℝ :=
  ∑ s : (∀ b, Sb b), xiFeat Ξb s *
    (diagonal d ⊗ₖ (1 : Matrix (∀ b, Zb b (s b)) (∀ b, Zb b (s b)) ℝ)) * (xiFeat Ξb s)ᴴ

omit [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)] in
/-- The relabelling `Feat n k ≃ ∀ b, featLab n k b` in the sums of the sector congruences. -/
theorem sum_xiFeat_eq (Ξb : ∀ b (p : Sb b), Matrix (O b) (featLab n k b × Zb b p) ℝ)
    (d : Feat n k → ℝ) :
    ∑ s : (∀ b, Sb b), xiFeat Ξb s *
        (diagonal d ⊗ₖ (1 : Matrix (∀ b, Zb b (s b)) (∀ b, Zb b (s b)) ℝ)) * (xiFeat Ξb s)ᴴ =
      ∑ s : (∀ b, Sb b), xiS Ξb s *
        (diagonal (d ∘ (featEquiv n k).symm) ⊗ₖ
          (1 : Matrix (∀ b, Zb b (s b)) (∀ b, Zb b (s b)) ℝ)) * (xiS Ξb s)ᴴ := by
  refine sum_congr rfl fun s _ => ?_
  set σ : Feat n k × (∀ b, Zb b (s b)) ≃ (∀ b, featLab n k b) × (∀ b, Zb b (s b)) :=
    (featEquiv n k).prodCongr (Equiv.refl _) with hσ
  ext x y
  simp only [Matrix.mul_apply, conjTranspose_apply, star_trivial]
  refine Fintype.sum_equiv σ _ _ (fun j => ?_)
  congr 1
  refine Fintype.sum_equiv σ _ _ (fun i => ?_)
  simp only [xiFeat, kroneckerMap_apply, diagonal_apply, Function.comp_apply, hσ,
    Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, (featEquiv n k).apply_eq_iff_eq,
    Equiv.symm_apply_apply]
  rfl

/-- **The positive enlargement for the diagonal witnesses** (move 4): B11's `hLift` for the lift of
the table's diagonal by per-block unit tables. -/
theorem hLift_table (Tb : EnvTable) (hT : tablePos Tb n k = true)
    (Ξb : ∀ b (p : Sb b), Matrix (O b) (featLab n k b × Zb b p) ℝ)
    (CU : ∀ b, Matrix (featLab n k b × O b) (featLab n k b × O b) ℝ)
    (hUY : ∀ b, (maskT (fun b => (id : featLab n k b → featLab n k b)) CU b -
      maskT (fun b => (id : featLab n k b → featLab n k b)) (gramT Ξb) b).PosSemidef) :
    (liftMap CU (diagonal ((fun v => (featWeight Tb v : ℝ)) ∘ (featEquiv n k).symm)) -
      sumXi Ξb (fun v => (featWeight Tb v : ℝ))).PosSemidef := by
  rw [sumXi, sum_xiFeat_eq]
  refine hLift_of_blocks (fun b => (id : featLab n k b → featLab n k b)) Ξb CU ?_ ?_ hUY
  · exact PosSemidef.diagonal fun v => by
      simp only [Pi.zero_apply, Function.comp_apply]; exact_mod_cast (featWeight_pos hT _).le
  · intro v w ⟨b, hb⟩
    have : v ≠ w := fun h => hb (by rw [h])
    exact diagonal_apply_ne _ this

/-- **`hdom` for a checked diagonal envelope from per-block data** (`lem:oct24:mask-schur`(a), (c),
`cert:envelopes`(b)): the input `hdom` of `EnvelopeSteps.DegreeOps`, with `D_ω` the lift of the
table's diagonal by the unit tables `CU` and `L_ω = ∑_s c_s Ξ_s T_s Ξ_sᵀ`. -/
theorem hdom_of_table_blocks {Tb : EnvTable} (hT : tablePos Tb n k = true)
    (hC : maskCheck Tb n k = true)
    (Ξb : ∀ b (p : Sb b), Matrix (O b) (featLab n k b × Zb b p) ℝ)
    (CU : ∀ b, Matrix (featLab n k b × O b) (featLab n k b × O b) ℝ)
    (hUY : ∀ b, (maskT (fun b => (id : featLab n k b → featLab n k b)) CU b -
      maskT (fun b => (id : featLab n k b → featLab n k b)) (gramT Ξb) b).PosSemidef)
    (T : ∀ s : (∀ b, Sb b), Matrix (Feat n k × (∀ b, Zb b (s b))) (Feat n k × (∀ b, Zb b (s b))) ℝ)
    (cs : (∀ b, Sb b) → ℝ) (hc0 : ∀ s, 0 ≤ cs s) (hc1 : ∀ s, cs s ≤ 1)
    (hTs : ∀ s, (T s).IsHermitian)
    (hsec : ∀ s v w z z', featMask w ≠ maskCompl (featMask v) → T s (w, z) (v, z') = 0)
    (hnorm : ∀ s v w (y : (∀ b, Zb b (s b)) → ℝ), ∑ z, (∑ z', T s (w, z) (v, z') * y z') ^ 2 ≤
      ((featAlpha v : ℝ) * featAlpha w) ^ 2 * ∑ z, y z ^ 2)
    {m : (∀ b, O b) → ℝ} {Lead Lop : ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ)}
    (hL : ∀ x y, kern m Lead x y = (∑ s, cs s • (xiFeat Ξb s * T s * (xiFeat Ξb s)ᴴ)) x y)
    (hLop : ∀ x y, kern m Lop x y =
      liftMap CU (diagonal ((fun v => (featWeight Tb v : ℝ)) ∘ (featEquiv n k).symm)) x y) :
    OpLE m Lead Lop ∧ OpLE m (-Lead) Lop :=
  hdom_of_table hT hC T cs hc0 hc1 hTs hsec hnorm (xiFeat Ξb) _ (hLift_table Tb hT Ξb CU hUY)
    hL hLop

end Compose

end Sarkozy.OpsFeature
