module

public import Sarkozy.SpectralD.SmallFast.Tests
public import Sarkozy.SpectralD.RootOneFast.Count

/-!
# The model checks of the smaller cuts as computations on codes

`ModelChecks c` identifies the five integer model tables with the graph. Once the sign table
is checked against `edgeSign` over the half, the cross neighbourhoods are read from the sign
table on codes (`nbrCode`), and the lemmas of `RootOneFast.Count` turn `gramOne` and
`plusOne` into computations on codes, the coverable count as a bit-mask enumeration. The
product in `gramThree` becomes a product over two columns of the sign table (`prodOnes`).
`modelChecks_of` assembles `ModelChecks c` from checks on codes. No evaluation happens in
this file.
-/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Finset Sarkozy.PartVLaws.FieldGraphs Sarkozy.SpectralC Sarkozy.SpectralD.Root

/-- `∏ k, (1 + l₁[k] * l₂[k])` over two integer lists, truncated to the shorter one. -/
def prodOnes (l₁ l₂ : List ℤ) : ℤ :=
  List.rec (motive := fun _ => List ℤ → ℤ) (fun _ => 1)
    (fun a _ ih l => List.casesOn (motive := fun _ => ℤ) l 1 (fun b l' => (1 + a * b) * ih l'))
    l₁ l₂

theorem prodOnes_eq_prod (l₁ l₂ : List ℤ) (n : ℕ) (h₁ : l₁.length ≤ n) :
    prodOnes l₁ l₂ = ∏ k ∈ range n, (1 + l₁.getD k 0 * l₂.getD k 0) := by
  induction l₁ generalizing l₂ n with
  | nil => simp [prodOnes]
  | cons a l₁ ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at h₁; omega⟩
    rw [Finset.prod_range_succ']
    cases l₂ with
    | nil => simp [prodOnes]
    | cons b l₂ =>
      change (1 + a * b) * prodOnes l₁ l₂ = _
      rw [ih l₂ m (by simp at h₁; omega)]
      simp [mul_comm]

theorem prod_half_eq_range (c : SmallCut) (n : ℕ)
    (hlt : ∀ h : c.data.cut.Half, code c h.1 < n)
    (honto : ∀ x, x < n → ∃ h : c.data.cut.Half, code c h.1 = x)
    (hinj : ∀ h₁ h₂ : c.data.cut.Half, code c h₁.1 = code c h₂.1 → h₁ = h₂)
    (f : ℕ → ℤ) : ∏ j : c.data.cut.Half, f (code c j.1) = ∏ y ∈ range n, f y := by
  rw [← Finset.prod_image (fun a _ b _ h => hinj a b h)]
  congr 1
  ext y
  simp only [mem_image, mem_univ, true_and, mem_range]
  constructor
  · rintro ⟨h, rfl⟩
    exact hlt h
  · exact honto y

/-- The cross neighbour codes of the code `x`, read from the sign table. -/
def nbrCode (c : SmallCut) (n x : ℕ) : List ℕ :=
  (List.range n).filter (fun z => entry (signTable c) z x != 0)

/-- The common cross neighbour codes of the codes `x` and `y`. -/
def commonCode (c : SmallCut) (n x y : ℕ) : List ℕ := commonR (nbrCode c n x) (nbrCode c n y)

/-- The checks of `ModelChecks` after the sign table, at the codes `x`, `y`. -/
def ModelCode (c : SmallCut) (n : ℕ) (A : ℕ → ℕ) (x y : ℕ) : Prop :=
  entry (crossTable c) x y = (if entry (signTable c) x y = 0 then 0 else 1) ∧
    entry (gramOneTable c) x y = 2 ^ (commonCode c n x y).length - 1 ∧
    entry (plusOneTable c) x y = 2 ^ (commonCode c n x y).length - 1 +
      (coverMaskCount A (commonCode c n x y) 0 0 : ℤ) ∧
    entry (gramThreeTable c) x y = prodOnes (colOf (signTable c) x) (colOf (signTable c) y) - 1

instance (c : SmallCut) (n : ℕ) (A : ℕ → ℕ) (x y : ℕ) :
    Decidable (ModelCode c n A x y) := by
  unfold ModelCode; infer_instance

section Bridge

variable (c : SmallCut) (n : ℕ)
  (hlt : ∀ h : c.data.cut.Half, code c h.1 < n)
  (honto : ∀ x, x < n → ∃ h : c.data.cut.Half, code c h.1 = x)
  (hinj : ∀ h₁ h₂ : c.data.cut.Half, code c h₁.1 = code c h₂.1 → h₁ = h₂)
  (hS : (signTable c).length = n)
  (hsign : ∀ i j : c.data.cut.Half,
    edgeSign c.edge c.data.cut.flip i.1 j.1 = entry (signTable c) (code c i.1) (code c j.1))

include hlt honto hinj hsign

omit honto hinj in
theorem mem_edgeNeighbours_code (k j : c.data.cut.Half) :
    j ∈ edgeNeighbours c.edge c.data.cut k ↔ code c j.1 ∈ nbrCode c n (code c k.1) := by
  simp only [edgeNeighbours, mem_filter, mem_univ, true_and, nbrCode, List.mem_filter,
    List.mem_range, hsign, hlt j, bne_iff_ne, ne_eq]

omit hlt hinj hsign in
theorem nbrCode_onto (k : c.data.cut.Half) :
    ∀ x ∈ nbrCode c n (code c k.1), ∃ j : c.data.cut.Half, code c j.1 = x := by
  intro x hx
  simp only [nbrCode, List.mem_filter, List.mem_range] at hx
  exact honto x hx.1

omit hlt honto hinj hsign in
theorem nbrCode_nodup (x : ℕ) : (nbrCode c n x).Nodup := List.nodup_range.filter _

include hS

theorem modelChecks_of (A : ℕ → ℕ)
    (hA : ∀ i j : c.data.cut.Half, (i ≠ j ∧ FiniteModel.Adj c.edge c.data.cut i j) ↔
      (A (code c i.1) >>> code c j.1) % 2 = 1)
    (hcode : ∀ x, x < n → ∀ y, y < n → ModelCode c n A x y) : ModelChecks c := by
  have he : Function.Injective (fun k : c.data.cut.Half => code c k.1) := fun a b h => hinj a b h
  have hN := mem_edgeNeighbours_code c n hlt hsign
  have hcod := nbrCode_onto c n honto
  have hnd : ∀ k : c.data.cut.Half, (nbrCode c n (code c k.1)).Nodup :=
    fun k => nbrCode_nodup c n _
  have hcard : ∀ i j : c.data.cut.Half,
      (edgeNeighbours c.edge c.data.cut i ∩ edgeNeighbours c.edge c.data.cut j).card =
        (commonCode c n (code c i.1) (code c j.1)).length :=
    card_inter_eq_commonR (fun k : c.data.cut.Half => code c k.1) _ (nbrCode c n) he hN hcod hnd
  intro i j
  obtain ⟨h1, h2, h3, h4⟩ := hcode _ (hlt i) _ (hlt j)
  refine ⟨hsign i j, ?_, ?_, ?_, ?_⟩
  · unfold FiniteModel.crossOne atTable
    rw [hsign, h1]
  · unfold FiniteModel.gramOne atTable
    rw [hcard, h2]
  · unfold FiniteModel.plusOne FiniteModel.gramOne atTable
    rw [hcard, coverCount_eq_coverMaskCount (fun k : c.data.cut.Half => code c k.1) _
      (nbrCode c n) he hN hcod hnd _ A hA, h3]
    rfl
  · unfold FiniteModel.gramThree atTable
    have hp := prod_half_eq_range c n hlt honto hinj
      (fun k => 1 + entry (signTable c) k (code c i.1) * entry (signTable c) k (code c j.1))
    simp only [hsign]
    rw [hp, h4, prodOnes_eq_prod _ _ n ((length_colOf _ _).trans hS).le]
    simp only [getD_colOf]

end Bridge

end Sarkozy.SpectralD.SmallMatrices
