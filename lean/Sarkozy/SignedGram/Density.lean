module

public import Sarkozy.SignedGram.Kernel
public import Sarkozy.SignedEstimates.G0
public import Sarkozy.DensityMoments.LawAlgebra
public import Sarkozy.EnvelopeInputs.PrefixCoordinates

@[expose] public section

/-!
# The density of the half marginal `m₀` of a middle block (SGA)

`paper/sections/24_matching_mean.tex`, proof of `lem:record:asymmetric-gram`(b), paragraph "In
measure form": the density of `m_{0,𝔅} = ⊗_p m_{0,p}` relative to `ν_F^{⊗𝔅}` is
`∏_{p∈𝔅} g₀(x_p) ≤ ∏_{p∈𝔅} (1 + e₀(p))`, by `lem:old-f-law`(a) (`|g₀ − 1| ≤ e₀`, E1's
`g0_bound`, proved from the exact Paley counts).

* `mem_injF1_iff`, `card_injF1`: `Inj_p(G_{F,1})` is `H_F` (distinct labels, `x₀ → x₂`);
* **`m0_le`** (one prime): `m₀(x) ≤ (1 + e₀(p)) ν_F(x)` pointwise;
* `tensor_expect_le`: pointwise domination of the factors passes to the tensor;
* **`densityLe_block`**: `DensityLe K₀ ν H_𝔅` with `H_𝔅 = ∏_{p∈𝔅} (1 + e₀(p))`, for every middle
  block whose primes are `≡ 3 (mod 4)` and `≥ 19`. (The paper bounds `H_𝔅` further by
  `(1 + e₀(X))^{n_X} ≤ e^{n_X e₀(X)} ≤ H̄_X`; that step is not needed here, because the shift is
  taken relative to `H_𝔅` itself.)
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedGram

open Sarkozy.PartV Sarkozy.Labellings Sarkozy.SignedComponents Sarkozy.SignedEstimates

/-! ## One prime -/

section Prime

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The layer-`0` restriction of a two-layer labelling, as a one-layer labelling. -/
def res0 (y : Fin 3 × Fin 2 → F) : Fin 3 × Fin 1 → F := fun w => y (w.1, 0)

theorem mem_injF1_iff (x : Fin 3 × Fin 1 → F) :
    x ∈ injLabellings F (foldGraph (Fin 1)) ↔ HF (lay1 x) := by
  rw [mem_injLabellings_iff_feasible]
  constructor
  · rintro ⟨hinj, hedge⟩
    refine ⟨fun a b hab => ?_, ?_⟩
    · have := hinj (a, 0) (mem_univ _) (b, 0) (mem_univ _) hab
      exact (Prod.mk.inj this).1
    · exact hedge ((0, 0), (2, 0)) ((mem_foldGraph (Fin 1) _).mpr ⟨rfl, rfl⟩) (mem_univ _)
        (mem_univ _)
  · rintro ⟨hinj, hedge⟩
    refine ⟨fun a _ b _ hab => ?_, fun e he _ _ => ?_⟩
    · obtain ⟨o, l⟩ := a
      obtain ⟨o', l'⟩ := b
      have hl : l = 0 := Subsingleton.elim _ _
      have hl' : l' = 0 := Subsingleton.elim _ _
      subst hl hl'
      have : o = o' := hinj hab
      rw [this]
    · rw [mem_foldGraph] at he
      obtain ⟨⟨o, l⟩, ⟨o', l'⟩⟩ := e
      simp only at he
      obtain ⟨rfl, rfl⟩ := he
      have hl : l = 0 := Subsingleton.elim _ _
      have hl' : l' = 0 := Subsingleton.elim _ _
      subst hl hl'
      exact hedge

theorem card_injF1 : ((injLabellings F (foldGraph (Fin 1))).card : ℝ) = Hcard (F := F) := by
  unfold Hcard
  congr 1
  refine Finset.card_nbij' (fun x => lay1 x) (fun x' w => x' w.1) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_coe] at hx ⊢
    rw [Hset, Finset.mem_filter]
    exact ⟨mem_univ _, (mem_injF1_iff x).mp hx⟩
  · intro x' hx'
    rw [Finset.mem_coe] at hx' ⊢
    rw [Hset, Finset.mem_filter] at hx'
    exact (mem_injF1_iff _).mpr hx'.2
  · intro x _
    funext ⟨o, l⟩
    have hl : l = 0 := Subsingleton.elim _ _
    subst hl
    rfl
  · intro x' _
    rfl

variable (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)

theorem map_res0_weight (x : Fin 3 × Fin 1 → F) :
    ((K0 hF).map res0).weight x = (m0 hF).weight (lay1 x) := by
  change (∑ y, if res0 y = x then (K0 hF).weight y else 0) =
    ∑ y, if lay y 0 = lay1 x then (K0 hF).weight y else 0
  refine sum_congr rfl fun y _ => ?_
  have hiff : res0 y = x ↔ lay y 0 = lay1 x := by
    constructor
    · rintro rfl
      rfl
    · intro h
      funext ⟨o, l⟩
      have hl : l = 0 := Subsingleton.elim _ _
      subst hl
      exact congrFun h o
  by_cases h : res0 y = x
  · simp only [h, hiff.mp h, ↓reduceIte]
  · simp only [h, mt hiff.mpr h, ↓reduceIte]

/-- **`m₀ ≤ (1 + e₀(p)) ν_F` at one prime** (`lem:old-f-law`(a): `g₀ ≤ 1 + e₀` on `H_F`, and `m₀`
lives on `H_F`). -/
theorem m0_le (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F)
    (hF1 : (injLabellings F (foldGraph (Fin 1))).Nonempty) (x : Fin 3 × Fin 1 → F) :
    ((K0 hF).map res0).weight x ≤
      (1 + e0 (Fintype.card F)) * (graphLaw (foldGraph (Fin 1)) hF1).weight x := by
  rw [map_res0_weight]
  have hH := Hcard_pos hF
  change _ ≤ (1 + e0 (Fintype.card F)) *
    (if x ∈ injLabellings F (foldGraph (Fin 1)) then
      1 / ((injLabellings F (foldGraph (Fin 1))).card : ℝ) else 0)
  rw [card_injF1]
  by_cases hx : HF (lay1 x)
  · have hmem : x ∈ injLabellings F (foldGraph (Fin 1)) := (mem_injF1_iff x).mpr hx
    simp only [hmem, ↓reduceIte]
    have hb := g0_bound hR h3 h19 hF hx
    have hg : g0 hF (lay1 x) = (m0 hF).weight (lay1 x) * Hcard (F := F) := rfl
    rw [hg] at hb
    have h1 : (m0 hF).weight (lay1 x) * Hcard (F := F) ≤ 1 + e0 (Fintype.card F) := by
      have := (abs_le.mp hb).2
      linarith
    rw [mul_one_div, le_div_iff₀ hH]
    exact h1
  · have hmem : x ∉ injLabellings F (foldGraph (Fin 1)) := fun h => hx ((mem_injF1_iff x).mp h)
    simp only [hmem, ↓reduceIte]
    have h0 : (m0 hF).weight (lay1 x) = 0 := by
      by_contra hne
      exact hx (m0_support hF hne)
    rw [h0, mul_zero]

end Prime

/-! ## The tensor -/

section Tensor

variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {Y : J → Type} [∀ j, Fintype (Y j)] [∀ j, DecidableEq (Y j)]

/-- **Pointwise domination of the factors passes to the tensor** (for nonnegative integrands). -/
theorem tensor_expect_le (μ ν : ∀ j, FiniteLaw (V → Y j)) (c : J → ℝ)
    (h : ∀ j z, (μ j).weight z ≤ c j * (ν j).weight z) {g : (V → ∀ j, Y j) → ℝ}
    (hg : ∀ z, 0 ≤ g z) :
    (FiniteLaw.tensor μ).expect g ≤ (∏ j, c j) * (FiniteLaw.tensor ν).expect g := by
  rw [DensityMoments.expect_tensor_eq, DensityMoments.expect_tensor_eq, Finset.mul_sum]
  refine sum_le_sum fun z _ => ?_
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  refine mul_le_mul_of_nonneg_right ?_ (hg _)
  exact Finset.prod_le_prod₀ (fun j _ => (μ j).nonneg _) (fun j _ => h j (z j))

end Tensor

/-! ## A middle block -/

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (hne : MiddleNonempty pr)

/-- The density bound `H_𝔅 = ∏_{p∈𝔅} (1 + e₀(p))` of a middle block. -/
noncomputable def Hblock : ℝ := ∏ i, (1 + e0 (pr i : ℝ))

/-- **`dm_{0,𝔅}/dν_F^{⊗𝔅} ≤ H_𝔅`** (`lem:record:asymmetric-gram`(b), "In measure form", with
`lem:old-f-law`(a) at every prime), for a block of primes `≡ 3 (mod 4)` and `≥ 19`. -/
theorem densityLe_block (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i) :
    DensityLe (lawF pr hne).weight (blockGraphLaw pr (foldGraph (Fin 1)) hne.F1).weight
      (Hblock pr) := by
  intro φ
  have hL : mform (lawF pr hne).weight φ =
      (FiniteLaw.tensor fun i => (K0 (hne.F2 i)).map res0).expect
        (fun x => φ (lay1 x) * φ (lay1 x)) := by
    rw [DensityMoments.expect_tensor_map]
    change (lawF pr hne).expect (fun y => φ (lay2 y 0) * φ (lay2 y 0)) = _
    unfold lawF blockGraphLaw
    rw [EnvelopeInputs.expect_tensor_eq_pi]
    rfl
  have hR : dform (blockGraphLaw pr (foldGraph (Fin 1)) hne.F1).weight φ φ =
      (FiniteLaw.tensor fun i => graphLaw (foldGraph (Fin 1)) (hne.F1 i)).expect
        (fun x => φ (lay1 x) * φ (lay1 x)) := rfl
  rw [hL, hR]
  have hcard : ∀ i, (Fintype.card (ZMod (pr i)) : ℝ) = (pr i : ℝ) := fun i => by
    rw [ZMod.card]
  have key := tensor_expect_le (fun i => (K0 (hne.F2 i)).map res0)
    (fun i => graphLaw (foldGraph (Fin 1)) (hne.F1 i)) (fun i => 1 + e0 (pr i : ℝ))
    (fun i z => by
      have := m0_le (hne.F2 i) (ringChar_zmod_ne_two (h3 i)) (card_zmod_mod (h3 i))
        (card_zmod_ge (h19 i)) (hne.F1 i) z
      rwa [hcard] at this)
    (g := fun x => φ (lay1 x) * φ (lay1 x)) (fun z => mul_self_nonneg _)
  exact key

end Block

end Sarkozy.SignedGram
