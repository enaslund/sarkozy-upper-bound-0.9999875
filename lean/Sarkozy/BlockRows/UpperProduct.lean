module

public import Sarkozy.BlockRows.Joint
public import Sarkozy.BlockRows.Middle
public import Sarkozy.PartVLaws.TailRP

@[expose] public section

/-!
# Block rows, V: the upper row data of a block as products over the primes

`paper/sections/25_upper_reference.tex`, `subsec:upper-rows` (the row data of a coordinate),
`def:record:upper-bands` (F5), `lem:upper-reference-rp`(ii);
`paper/sections/17_completion_repair.tex`,
`cor:joint-completion-blocks` (whose hypothesis is that the conditional kernels are products).

The row data of the coordinate `0` of an upper block at the field type `𝔣'` are the laws of the
three rows of the `E`, `F` field laws (`rowD0`). The field laws of a block are tensors over the
primes, and the rows are read vertex by vertex, so:

* `tensor_map_isProd3`: the image of a block graph law under a vertex reading
  `z ↦ (z_{g(o,q)})_{o,q}` is the product of the one-prime images;
* `rowLaw2_isProd3`, `rowLaw1_isProd3`: the two-layer and the one-layer row laws of the block
  (`lam2`, `lam1` of `upperBlockFieldLaws`) are the products of those of the single-prime field
  laws `tailFieldLaws p` (the laws `λ_p(G_{φ₀φ₁,j})` at one prime; the name comes from the tail
  datum, which uses them);
* `primeNonempty`, `primeDatumHyp`: the single-prime laws of a block's prime form five-type row
  data (`tail_upperDatumHyp`, under Weil's bound and `p ≥ 2²⁰`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.BlockRows

open Sarkozy Sarkozy.Labellings Sarkozy.FiveType Sarkozy.FiveType.TwoCoord Sarkozy.PartV
  Sarkozy.PartVLaws

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The image of a block graph law under a vertex reading is the product of the one-prime
images.** -/
theorem tensor_map_isProd3 {W Q : Type} [Fintype W] [DecidableEq W] [Fintype Q] [DecidableEq Q]
    (G : OrientedGraph W) (hne : ∀ i, (injLabellings (ZMod (pr i)) G).Nonempty)
    (g : Fin 3 → Q → W) :
    IsProd3 (objSplit pr Q) ((blockGraphLaw pr G hne).map fun z o q => z (g o q))
      (fun i => (graphLaw G (hne i)).map fun z o q => z (g o q)) := by
  intro ω
  rw [map_weight_eq, sum_filter]
  have hpt : ∀ z : W → BlockLabel pr,
      (if (fun o q => z (g o q)) = ω then (blockGraphLaw pr G hne).weight z else 0) =
        ∏ i, (if (fun o q => (objSplit pr W) z i (g o q)) = (fun o => (objSplit pr Q) (ω o) i)
          then (graphLaw G (hne i)).weight ((objSplit pr W) z i) else 0) := by
    intro z
    rw [prod_ite_zero]
    have hiff : ((fun o q => z (g o q)) = ω) ↔ ∀ i ∈ (univ : Finset ι),
        (fun o q => (objSplit pr W) z i (g o q)) = (fun o => (objSplit pr Q) (ω o) i) := by
      constructor
      · intro h i _
        funext o q
        rw [← h]
        rfl
      · intro h
        funext o q i
        exact congrFun (congrFun (h i (mem_univ i)) o) q
    split_ifs with h1 h2 h2
    · unfold blockGraphLaw
      rw [tensor_weight]
      rfl
    · exact absurd (hiff.mp h1) h2
    · exact absurd (hiff.mpr h2) h1
    · rfl
  simp only [hpt]
  rw [sum_split (objSplit pr W) (fun i z => if (fun o q => z (g o q)) =
    (fun o => (objSplit pr Q) (ω o) i) then (graphLaw G (hne i)).weight z else 0)]
  refine prod_congr rfl fun i _ => ?_
  rw [map_weight_eq, sum_filter]

/-! ## The single-prime field laws of a block's prime -/

omit [Fintype ι] [DecidableEq ι] in
/-- The labelling sets at the prime `pr i` (from those of the block). -/
theorem primeNonempty (hne : UpperNonempty pr) (i : ι) : TailNonempty (pr i) :=
  ⟨fun f₀ f₁ => hne.two f₀ f₁ i, fun f₀ f₁ => hne.one f₀ f₁ i⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **The single-prime row data form five-type data** (`tail_upperDatumHyp`). -/
theorem primeDatumHyp (hne : UpperNonempty pr) (hW : ∀ i, WeilBound (ZMod (pr i)))
    (hp : ∀ i, (2 : ℝ) ^ 20 ≤ pr i) (i : ι) :
    UpperDatumHyp (tailFieldLaws (pr i) (primeNonempty pr hne i)) :=
  tail_upperDatumHyp (pr i) (hW i) (hp i) (primeNonempty pr hne i)

/-! ## The row laws -/

/-- The two-layer row law of the coordinate `0` (rows of `O_E = {0,1,2}`) of the field pair
`(f₀, 𝔣')`, for `f₀ = E, F`. -/
noncomputable abbrev rowLaw2 {X : Type} [Fintype X] [DecidableEq X] (F : UpperFieldLaws X)
    (f₀ : FieldTy) (hf : f₀.Obj = Fin 3) (f' : FieldTy) :
    FiniteLaw (Fin 3 → f'.Obj × ZMod 2 → X) :=
  (lam2 F f₀ f').map fun y o => rows0 y (cast hf.symm o)

/-- The one-layer row law of the coordinate `0`. -/
noncomputable abbrev rowLaw1 {X : Type} [Fintype X] [DecidableEq X] (F : UpperFieldLaws X)
    (f₀ : FieldTy) (hf : f₀.Obj = Fin 3) (f' : FieldTy) :
    FiniteLaw (Fin 3 → f'.Obj × Unit → X) :=
  (lam1 F f₀ f').map fun y o => rows0 y (cast hf.symm o)

theorem rowLaw2_block_eq (hne : UpperNonempty pr) (f₀ : FieldTy) (hf : f₀.Obj = Fin 3)
    (f' : FieldTy) :
    rowLaw2 (upperBlockFieldLaws pr hne) f₀ hf f' =
      (blockGraphLaw pr (fieldGraph (toFType f₀) (toFType f') (Fin 2))
        (hne.two (toFType f₀) (toFType f'))).map fun z o q =>
          z (objCast f₀ (cast hf.symm o), objCast f' q.1, layerFin q.2) := by
  unfold rowLaw2 lam2
  rw [map_map']
  rfl

theorem rowLaw2_prime_eq (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) (f₀ : FieldTy)
    (hf : f₀.Obj = Fin 3) (f' : FieldTy) :
    rowLaw2 (tailFieldLaws p hne) f₀ hf f' =
      (graphLaw (fieldGraph (toFType f₀) (toFType f') (Fin 2))
        (hne.two (toFType f₀) (toFType f'))).map fun z o q =>
          z (objCast f₀ (cast hf.symm o), objCast f' q.1, layerFin q.2) := by
  unfold rowLaw2 lam2
  rw [map_map']
  rfl

theorem rowLaw1_block_eq (hne : UpperNonempty pr) (f₀ : FieldTy) (hf : f₀.Obj = Fin 3)
    (f' : FieldTy) :
    rowLaw1 (upperBlockFieldLaws pr hne) f₀ hf f' =
      (blockGraphLaw pr (fieldGraph (toFType f₀) (toFType f') (Fin 1))
        (hne.one (toFType f₀) (toFType f'))).map fun z o q =>
          z (objCast f₀ (cast hf.symm o), objCast f' q.1, (0 : Fin 1)) := by
  unfold rowLaw1 lam1
  rw [map_map']
  rfl

theorem rowLaw1_prime_eq (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) (f₀ : FieldTy)
    (hf : f₀.Obj = Fin 3) (f' : FieldTy) :
    rowLaw1 (tailFieldLaws p hne) f₀ hf f' =
      (graphLaw (fieldGraph (toFType f₀) (toFType f') (Fin 1))
        (hne.one (toFType f₀) (toFType f'))).map fun z o q =>
          z (objCast f₀ (cast hf.symm o), objCast f' q.1, (0 : Fin 1)) := by
  unfold rowLaw1 lam1
  rw [map_map']
  rfl

/-- **The two-layer row laws of a block are the products of the single-prime row laws.** -/
theorem rowLaw2_isProd3 (hne : UpperNonempty pr) (f₀ : FieldTy) (hf : f₀.Obj = Fin 3)
    (f' : FieldTy) :
    IsProd3 (objSplit pr (f'.Obj × ZMod 2)) (rowLaw2 (upperBlockFieldLaws pr hne) f₀ hf f')
      (fun i => rowLaw2 (tailFieldLaws (pr i) (primeNonempty pr hne i)) f₀ hf f') := by
  rw [rowLaw2_block_eq]
  simp only [rowLaw2_prime_eq]
  exact tensor_map_isProd3 pr _ _ _

/-- **The one-layer row laws of a block are the products of the single-prime row laws.** -/
theorem rowLaw1_isProd3 (hne : UpperNonempty pr) (f₀ : FieldTy) (hf : f₀.Obj = Fin 3)
    (f' : FieldTy) :
    IsProd3 (objSplit pr (f'.Obj × Unit)) (rowLaw1 (upperBlockFieldLaws pr hne) f₀ hf f')
      (fun i => rowLaw1 (tailFieldLaws (pr i) (primeNonempty pr hne i)) f₀ hf f') := by
  rw [rowLaw1_block_eq]
  simp only [rowLaw1_prime_eq]
  exact tensor_map_isProd3 pr _ _ _

end Sarkozy.BlockRows
