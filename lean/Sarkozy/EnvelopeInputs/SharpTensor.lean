module

public import Sarkozy.Reflection.BracketMatrix
public import Sarkozy.Comparison.FoldedEnergy
public import Sarkozy.RecordExpansion.Multilinear

/-!
# Products of sharp atoms are sharp

`paper/sections/31_density_induction_upgrade.tex`, proof of `lem:density:coupled`: "Products of
sharp atoms from one of the two tags of (CP2)(b) ... obey the same proof". The coupled per-term
bound (`CoupledTerm.abs_diagonalIntegral_coupled_le`) takes a sharp decomposition on the product
alphabet of the sharp atoms. This file proves the step that makes products of sharp laws sharp.

* `tensorLaw_sampleIntegral`: a tensor product of push-forwards `∫ · (Z_j) dw_j` is the
  push-forward of the product weight;
* `tensorLaw_diagonalLaw`: `⊗_j Diag(m_j) = Diag(∏_j m_j)`;
* **`sharp_tensor`**: if every `K_j` is sharp at the cut `c` with constant `d_j` relative to
  `(m₊_j, m₋_j)`, then `⊗_j K_j` is sharp with constant `∏_j d_j` relative to the products
  `(∏_j m₊_j, ∏_j m₋_j)`. The proof goes through `sharp_iff_bracket` and the block-Gram
  tensorization `ReflectionCut.Bracket.tensor`.

Not done here: the identification of the products of half marginals with the half marginals of
the product law, and the resulting `HasSharpBound` of the product.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.Comparison Sarkozy.ReflectionCut Sarkozy.RecordExpansion

variable {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [Fintype J] [DecidableEq J]
  {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

omit [Fintype J] [DecidableEq J] [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] in
/-- The coordinates of a joined labelling are the joined coordinates. -/
theorem join_coord (c : ReflectionCut V) (x y : c.Half → ∀ j, X j) (j : J) :
    (fun v => c.join x y v j) = c.join (fun u => x u j) (fun u => y u j) := by
  funext v
  unfold ReflectionCut.join
  split_ifs <;> rfl

/-- **A tensor product of push-forwards is the push-forward of the product weight.** -/
theorem tensorLaw_sampleIntegral {Ω : J → Type*} [∀ j, Fintype (Ω j)] (w : ∀ j, Ω j → ℝ)
    (Z : ∀ j, Ω j → V → X j) :
    tensorLaw (fun j => sampleIntegral (w j) (Z j)) =
      sampleIntegral (fun ω : (∀ j, Ω j) => ∏ j, w j (ω j)) (fun ω v j => Z j (ω j) v) := by
  apply LinearMap.ext
  intro F
  rw [tensorLaw_apply]
  have hld : ∀ j (y : V → X j), lawDensity (sampleIntegral (w j) (Z j)) y =
      ∑ ω, w j ω * (if Z j ω = y then 1 else 0) := fun j y => rfl
  simp only [hld]
  have hprod : ∀ z : ∀ j, V → X j, (∏ j, ∑ ω, w j ω * (if Z j ω = z j then (1 : ℝ) else 0)) =
      ∑ ω : (∀ j, Ω j), ∏ j, (w j (ω j) * (if Z j (ω j) = z j then (1 : ℝ) else 0)) :=
    fun z => Fintype.prod_sum (fun j ω => w j ω * (if Z j ω = z j then (1 : ℝ) else 0))
  simp only [hprod, Finset.sum_mul]
  rw [Finset.sum_comm]
  change _ = ∑ ω : (∀ j, Ω j), (∏ j, w j (ω j)) * F (fun v j => Z j (ω j) v)
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hind : ∀ z : ∀ j, V → X j,
      (∏ j, (w j (ω j) * (if Z j (ω j) = z j then (1 : ℝ) else 0))) * F (fun v j => z j v) =
        if (fun j => Z j (ω j)) = z then (∏ j, w j (ω j)) * F (fun v j => z j v) else 0 := by
    intro z
    rw [Finset.prod_mul_distrib]
    split_ifs with hz
    · have h1 : ∀ j, Z j (ω j) = z j := fun j => congrFun hz j
      have h2 : (∏ j, (if Z j (ω j) = z j then (1 : ℝ) else 0)) = 1 :=
        Finset.prod_eq_one fun j _ => by simp [h1 j]
      rw [h2, mul_one]
    · have h1 : ∃ j, Z j (ω j) ≠ z j := by
        by_contra hc
        push Not at hc
        exact hz (funext hc)
      obtain ⟨j₀, hj₀⟩ := h1
      have h2 : (∏ j, (if Z j (ω j) = z j then (1 : ℝ) else 0)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [hj₀])
      rw [h2, mul_zero, zero_mul]
  rw [Finset.sum_congr rfl fun z _ => hind z, Finset.sum_ite_eq]
  simp

/-- **`⊗_j Diag(m_j) = Diag(∏_j m_j)`**: the tensor product of diagonal laws at a common cut is
the diagonal law of the product weight. -/
theorem tensorLaw_diagonalLaw (c : ReflectionCut V) (m : ∀ j, (c.Half → X j) → ℝ) :
    tensorLaw (fun j => c.diagonalLaw (m j)) =
      c.diagonalLaw (fun x : c.Half → ∀ j, X j => ∏ j, m j (fun u => x u j)) := by
  have h1 : tensorLaw (fun j => c.diagonalLaw (m j)) =
      sampleIntegral (fun ω : (∀ j, c.Half → X j) => ∏ j, m j (ω j))
        (fun ω v j => c.join (ω j) (ω j) v) :=
    tensorLaw_sampleIntegral (fun j => m j) (fun j x => c.join x x)
  rw [h1]
  apply LinearMap.ext
  intro F
  change ∑ ω : (∀ j, c.Half → X j), (∏ j, m j (ω j)) * F (fun v j => c.join (ω j) (ω j) v) =
    ∑ x : (c.Half → ∀ j, X j), (∏ j, m j (fun u => x u j)) * F (c.join x x)
  refine Fintype.sum_equiv (Equiv.piComm fun (j : J) (_ : c.Half) => X j) _ _ fun ω => ?_
  have hj : (fun v j => c.join (ω j) (ω j) v) =
      c.join (fun u j => ω j u) (fun u j => ω j u) := by
    funext v j
    exact (congrFun (join_coord c (fun u j => ω j u) (fun u j => ω j u) j) v).symm
  change (∏ j, m j (ω j)) * F (fun v j => c.join (ω j) (ω j) v) =
    (∏ j, m j (fun u => ω j u)) * F (c.join (fun u j => ω j u) (fun u j => ω j u))
  rw [hj]

/-- **Products of sharp laws are sharp** (`lem:density:coupled`, "products of sharp atoms ...
obey the same proof"): if every `K_j` is sharp at `c` with constant `d_j ≥ 0` relative to the
nonnegative `(m₊_j, m₋_j)`, then `⊗_j K_j` is sharp at `c` with constant `∏_j d_j` relative to
`(∏_j m₊_j, ∏_j m₋_j)`. -/
theorem sharp_tensor (c : ReflectionCut V) (K : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (mp mm : ∀ j, (c.Half → X j) → ℝ) (d : J → ℝ) (hmp : ∀ j x, 0 ≤ mp j x)
    (hmm : ∀ j x, 0 ≤ mm j x) (hd : ∀ j, 0 ≤ d j)
    (h : ∀ j, Sharp c (K j) (mp j) (mm j) (d j)) :
    Sharp c (tensorLaw K) (fun x : c.Half → ∀ j, X j => ∏ j, mp j (fun u => x u j))
      (fun x : c.Half → ∀ j, X j => ∏ j, mm j (fun u => x u j)) (∏ j, d j) := by
  have hb : ∀ j, c.Bracket (d j • c.diagonalLaw (mp j)) (K j) (d j • c.diagonalLaw (mm j)) :=
    fun j => (sharp_iff_bracket c (K j) (hmp j) (hmm j) (hd j)).mp (h j)
  have ht := Bracket.tensor hb
  rw [tensorLaw_smul d (fun j => c.diagonalLaw (mp j)),
    tensorLaw_smul d (fun j => c.diagonalLaw (mm j)), tensorLaw_diagonalLaw,
    tensorLaw_diagonalLaw] at ht
  exact (sharp_iff_bracket c (tensorLaw K)
    (fun x => Finset.prod_nonneg fun j _ => hmp j _)
    (fun x => Finset.prod_nonneg fun j _ => hmm j _)
    (Finset.prod_nonneg fun j _ => hd j)).mpr ht

end Sarkozy.EnvelopeInputs
