module

public import Sarkozy.Labellings.GraphAutomorphism

/-!
# Patterns, folds and chamber reflections

Sources: `def:patterns`, and `lem:record:fold-identification` (b), (e);
`paper/sections/17_completion_repair.tex`.

The patterns are maps `ℤ/6ℤ → O`, listed as `(φ(0), …, φ(5))`:
* the three folds `F_0 = (0,1,2,2,1,0)`, `F_1 = (1,0,0,1,2,2)` and `F_2 = (2,2,1,0,0,1)`;
* the two matchings `E_0 = (0,1,1,2,2,0)` and `E_1 = (0,0,1,1,2,2)`;
* the six merges `G_{sk} = [E_s(·) = k]`.

`Π_φ(λ)` (`patternLaw`) is the law of `ω ∘ φ` for `ω ∼ λ`. The chamber reflections are
`ϑ_{2j}(u) = 4j − 1 − u`, that is `5 − u`, `3 − u` and `1 − u`.

Proved, each by `decide` over `ℤ/6ℤ` and `{0, 1, 2}`:
* (b) `F_j ∘ ϑ_{2j} = F_j`, and `F_j` maps `2j, 2j+1, 2j+2` to `0, 1, 2`. Hence every
  configuration `ω ∘ F_j` is fixed by `ϑ_{2j}` and its plus half carries `ω_o` at `2j + o`
  (`fold_config_fixed`, `fold_config_half`). In particular `Π_{F_j}(λ)` is invariant under
  `ϑ_{2j}` (`patternLaw_fold_invariant`).
* (e), for the generators: the translation `u ↦ u + 2` and the reflections `u ↦ k − u`
  (`k = 1, 3, 5`) permute the folds. They map `E_s` to `ψ ∘ E_s` for a permutation `ψ` of
  `{0, 1, 2}`. The fixed reflections are `F_0`, `G_e`, `G_o` under `ϑ_0`; `F_1` under `ϑ_2`;
  and `F_2` under `ϑ_4 = ϑ_1`.

* (d), the layer swap: on `Λ = {0, 1}`, the swap of the two layers is an automorphism of
  `G_L` and of `G_F`, so their graph laws are swap-invariant (`foldGraphLaw_layerSwap`,
  `recordGraphLaw_layerSwap`). The image `Π_φ` of a swap-invariant law is swap-invariant
  (`patternLaw_layerSwap_invariant`), and its layer-zero half is the `φ`-image of the
  layer-zero part (`patternLaw_layerZero`).

* (e), merges: if a generator maps `E_s` to `ψ ∘ E_s`, it maps `G_{sk}` to `G_{s, ψ⁻¹(k)}`
  (`merge_relabel`).
* (f): at `ϑ_0` the plus half `(φ(0), φ(1), φ(2))` and the reflected half `(φ(5), φ(4), φ(3))`
  of every pattern are those of `tab:corner` (`corner_table`, by `decide`).
  - The corners `𝒰 = {(b, y, y) : y ≠ b}`, `𝒱 = {(y, y, b) : y ≠ b}` and `𝒵 = {(b, b, b)}` are
    pairwise disjoint (`corners_disjoint`).
  - With distinct labels, the halves of the folds and matchings lie in the corners listed
    there (`fold_corners`, `matching_corners`).

Not formalized here: the table of reflections (`tab:reflection`), beyond the generator
statements above.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Labellings

/-- The fold table: `F_0 = (0,1,2,2,1,0)`, `F_1 = (1,0,0,1,2,2)`, `F_2 = (2,2,1,0,0,1)`. -/
def foldTable : Fin 3 → Fin 6 → Fin 3 :=
  ![![0, 1, 2, 2, 1, 0], ![1, 0, 0, 1, 2, 2], ![2, 2, 1, 0, 0, 1]]

/-- The matching table: `E_0 = (0,1,1,2,2,0)`, `E_1 = (0,0,1,1,2,2)`. -/
def matchingTable : Fin 2 → Fin 6 → Fin 3 :=
  ![![0, 1, 1, 2, 2, 0], ![0, 0, 1, 1, 2, 2]]

/-- A residue of `ℤ/6ℤ` as an index of `Fin 6`. -/
def toFin6 (u : ZMod 6) : Fin 6 := ⟨u.val, ZMod.val_lt u⟩

/-- **The fold `F_j`** (`def:patterns`). -/
def fold (j : Fin 3) (u : ZMod 6) : Fin 3 := foldTable j (toFin6 u)

/-- **The matching `E_s`** (`def:patterns`). -/
def matching (s : Fin 2) (u : ZMod 6) : Fin 3 := matchingTable s (toFin6 u)

/-- **The merge `G_{sk} = [E_s(·) = k]`** (`def:patterns`). -/
def merge (s : Fin 2) (k : Fin 3) (u : ZMod 6) : Fin 2 := if matching s u = k then 1 else 0

/-- The chamber reflection `u ↦ k − u`. -/
def chamberRefl (k u : ZMod 6) : ZMod 6 := k - u

/-- The fold chamber of `F_j`: `ϑ_{2j}(u) = 4j − 1 − u`. -/
def foldChamber (j : Fin 3) : ZMod 6 := 4 * (j.val : ZMod 6) - 1

/-- **`lem:record:fold-identification`(b)**: `F_j ∘ ϑ_{2j} = F_j`. -/
theorem fold_chamberRefl (j : Fin 3) (u : ZMod 6) :
    fold j (chamberRefl (foldChamber j) u) = fold j u := by
  revert j u
  decide

/-- **`lem:record:fold-identification`(b)**: `F_j` maps `2j + o` to `o` for `o ∈ {0, 1, 2}`. -/
theorem fold_half (j o : Fin 3) : fold j (2 * (j.val : ZMod 6) + (o.val : ZMod 6)) = o := by
  revert j o
  decide

variable {O 𝔛 : Type*} [Fintype O] [DecidableEq O] [Fintype 𝔛] [DecidableEq 𝔛]

/-- **`Π_φ(λ)`** (`def:patterns`): the law of `ω ∘ φ` for `ω ∼ λ`. -/
noncomputable def patternLaw (φ : ZMod 6 → O) (lam : FiniteLaw (O → 𝔛)) :
    FiniteLaw (ZMod 6 → 𝔛) :=
  lam.map fun ω u => ω (φ u)

omit [Fintype 𝔛] [DecidableEq 𝔛] in
/-- Every configuration `ω ∘ F_j` is fixed by `ϑ_{2j}`. -/
theorem fold_config_fixed (j : Fin 3) (ω : Fin 3 → 𝔛) :
    (fun u => ω (fold j (chamberRefl (foldChamber j) u))) = fun u => ω (fold j u) := by
  funext u
  rw [fold_chamberRefl]

omit [Fintype 𝔛] [DecidableEq 𝔛] in
/-- The plus half of `ω ∘ F_j` carries `ω_o` at `2j + o`. -/
theorem fold_config_half (j o : Fin 3) (ω : Fin 3 → 𝔛) :
    ω (fold j (2 * (j.val : ZMod 6) + (o.val : ZMod 6))) = ω o := by
  rw [fold_half]

/-- **`Π_{F_j}(λ)` is invariant under its fold chamber `ϑ_{2j}`**: the law is carried by
configurations fixed by the reflection, so it is diagonal there. -/
theorem patternLaw_fold_invariant (j : Fin 3) (lam : FiniteLaw (Fin 3 → 𝔛))
    (f : (ZMod 6 → 𝔛) → ℝ) :
    (patternLaw (fold j) lam).expect (fun z => f (fun u => z (chamberRefl (foldChamber j) u))) =
      (patternLaw (fold j) lam).expect f := by
  unfold patternLaw
  rw [FiniteLaw.expect_map, FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro ω
  simp only [Function.comp_apply]
  rw [fold_config_fixed]

/-! ## `lem:record:fold-identification`(e) for the generators -/

/-- The translation `u ↦ u + 2` maps `F_j` to `F_{j-1}`: `F_j(u + 2) = F_{j - 1}(u)`. -/
theorem fold_translation (j : Fin 3) (u : ZMod 6) : fold j (u + 2) = fold (j - 1) u := by
  revert j u
  decide

/-- The reflection `u ↦ 5 − u` fixes `F_0` and exchanges `F_1` and `F_2`. -/
theorem fold_refl5 (u : ZMod 6) :
    fold 0 (chamberRefl 5 u) = fold 0 u ∧ fold 1 (chamberRefl 5 u) = fold 2 u ∧
      fold 2 (chamberRefl 5 u) = fold 1 u := by
  revert u
  decide

/-- The reflection `u ↦ 3 − u` fixes `F_1` and exchanges `F_0` and `F_2`. -/
theorem fold_refl3 (u : ZMod 6) :
    fold 1 (chamberRefl 3 u) = fold 1 u ∧ fold 0 (chamberRefl 3 u) = fold 2 u ∧
      fold 2 (chamberRefl 3 u) = fold 0 u := by
  revert u
  decide

/-- The reflection `u ↦ 1 − u` fixes `F_2` and exchanges `F_0` and `F_1`. -/
theorem fold_refl1 (u : ZMod 6) :
    fold 2 (chamberRefl 1 u) = fold 2 u ∧ fold 0 (chamberRefl 1 u) = fold 1 u ∧
      fold 1 (chamberRefl 1 u) = fold 0 u := by
  revert u
  decide

/-- **The generators map each matching to a relabelled matching**: for `α` the translation
`u ↦ u + 2` or a reflection `u ↦ k − u` (`k = 1, 3, 5`), there is a permutation `ψ` of
`{0, 1, 2}` with `E_s ∘ α = ψ ∘ E_s`. -/
theorem matching_generators (s : Fin 2) :
    (∃ ψ : Equiv.Perm (Fin 3), ∀ u, matching s (u + 2) = ψ (matching s u)) ∧
    ∀ k : ZMod 6, (k = 1 ∨ k = 3 ∨ k = 5) →
      ∃ ψ : Equiv.Perm (Fin 3), ∀ u, matching s (chamberRefl k u) = ψ (matching s u) := by
  revert s
  decide

/-- **The fixed reflections** (`lem:record:fold-identification`(e)): `F_0`, `G_e = G_{00}` and
`G_o = G_{11}` are fixed by `ϑ_0` (`u ↦ 5 − u`); `F_1` by `ϑ_2` (`u ↦ 3 − u`); `F_2` by
`ϑ_4 = ϑ_1` (`u ↦ 1 − u`). -/
theorem fixed_reflections (u : ZMod 6) :
    fold 0 (chamberRefl 5 u) = fold 0 u ∧ merge 0 0 (chamberRefl 5 u) = merge 0 0 u ∧
      merge 1 1 (chamberRefl 5 u) = merge 1 1 u ∧ fold 1 (chamberRefl 3 u) = fold 1 u ∧
      fold 2 (chamberRefl 1 u) = fold 2 u := by
  revert u
  decide

/-! ## `lem:record:fold-identification`(d): the layer swap -/

/-- The swap of the two layers of a two-layer label. -/
def layerSwap {X : Type*} (x : Fin 2 → X) : Fin 2 → X := fun l => x (Equiv.swap 0 1 l)

omit [Fintype O] [DecidableEq O] in
/-- **The image of a swap-invariant law is swap-invariant**: if `λ` is invariant under the swap
of the two layer labels of every object, so is `Π_φ(λ)`, at every slot. -/
theorem patternLaw_layerSwap_invariant [Fintype O] [DecidableEq O] {X : Type*} [Fintype X]
    [DecidableEq X] (φ : ZMod 6 → O) (lam : FiniteLaw (O → (Fin 2 → X)))
    (hlam : ∀ f : (O → (Fin 2 → X)) → ℝ,
      lam.expect (fun ω => f (fun o => layerSwap (ω o))) = lam.expect f)
    (f : (ZMod 6 → (Fin 2 → X)) → ℝ) :
    (patternLaw φ lam).expect (fun z => f (fun u => layerSwap (z u))) =
      (patternLaw φ lam).expect f := by
  unfold patternLaw
  rw [FiniteLaw.expect_map, FiniteLaw.expect_map]
  exact hlam (fun ω => f (fun u => ω (φ u)))

omit [Fintype O] [DecidableEq O] in
/-- **The layer-zero half of `Π_φ(λ)`** is the `φ`-image of the layer-zero part of `λ`. -/
theorem patternLaw_layerZero [Fintype O] [DecidableEq O] {X : Type*} [Fintype X]
    [DecidableEq X] (φ : ZMod 6 → O) (lam : FiniteLaw (O → (Fin 2 → X)))
    (g : (ZMod 6 → X) → ℝ) :
    (patternLaw φ lam).expect (fun z => g (fun u => z u 0)) =
      lam.expect (fun ω => g (fun u => ω (φ u) 0)) := by
  unfold patternLaw
  rw [FiniteLaw.expect_map]
  rfl

/-- The layer swap on `ℤ/6ℤ × {0, 1}` and on `{0, 1, 2} × {0, 1}`. -/
def layerSwapMap (A : Type*) : A × Fin 2 ≃ A × Fin 2 :=
  Equiv.prodCongr (Equiv.refl A) (Equiv.swap 0 1)

/-- **The layer swap is an automorphism of `G_L`**: all layer lifts of the rotation edges are
edges. -/
theorem recordGraph_layerSwap : IsAutomorphism (recordGraph (Fin 2)) (layerSwapMap (ZMod 6)) := by
  intro u v
  simp only [mem_recordGraph, layerSwapMap, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map]
  rfl

/-- **The layer swap is an automorphism of `G_F`**. -/
theorem foldGraph_layerSwap : IsAutomorphism (foldGraph (Fin 2)) (layerSwapMap (Fin 3)) := by
  intro u v
  simp only [mem_foldGraph, layerSwapMap, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map]
  rfl

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The graph law of `G_L` with two layers is invariant under the layer swap.** -/
theorem recordGraphLaw_layerSwap (hne : (injLabellings F (recordGraph (Fin 2))).Nonempty)
    (f : (ZMod 6 × Fin 2 → F) → ℝ) :
    (graphLaw (recordGraph (Fin 2)) hne).expect (fun z => f (z ∘ layerSwapMap (ZMod 6))) =
      (graphLaw (recordGraph (Fin 2)) hne).expect f :=
  graphLaw_expect_comp _ hne _ recordGraph_layerSwap f

/-- **The graph law of `G_F` with two layers is invariant under the layer swap**: `λ_F` is
symmetric at the layer cut `ι`. -/
theorem foldGraphLaw_layerSwap (hne : (injLabellings F (foldGraph (Fin 2))).Nonempty)
    (f : (Fin 3 × Fin 2 → F) → ℝ) :
    (graphLaw (foldGraph (Fin 2)) hne).expect (fun z => f (z ∘ layerSwapMap (Fin 3))) =
      (graphLaw (foldGraph (Fin 2)) hne).expect f :=
  graphLaw_expect_comp _ hne _ foldGraph_layerSwap f

/-- **Merges follow the matchings** (`lem:record:fold-identification`(e)): if `E_s ∘ α = ψ ∘ E_s`,
then `G_{sk} ∘ α = G_{s, ψ⁻¹(k)}`. -/
theorem merge_relabel (s : Fin 2) (α : ZMod 6 → ZMod 6) (ψ : Equiv.Perm (Fin 3))
    (h : ∀ u, matching s (α u) = ψ (matching s u)) (k : Fin 3) (u : ZMod 6) :
    merge s k (α u) = merge s (ψ.symm k) u := by
  unfold merge
  rw [h u]
  congr 1
  exact propext ⟨fun h' => by rw [← h', Equiv.symm_apply_apply],
    fun h' => by rw [h', Equiv.apply_symm_apply]⟩

/-! ## (f): the corner table at `ϑ_0` -/

/-- The plus half `(φ(0), φ(1), φ(2))` of a pattern at `ϑ_0`. -/
def plusHalf {O : Type*} (φ : ZMod 6 → O) (o : Fin 3) : O := φ (o.val : ZMod 6)

/-- The reflected half `(φ(5), φ(4), φ(3))` of a pattern at `ϑ_0`. -/
def reflHalf {O : Type*} (φ : ZMod 6 → O) (o : Fin 3) : O := φ (5 - (o.val : ZMod 6))

/-- **`tab:corner`**: the halves of the folds, matchings and merges at `ϑ_0`. -/
theorem corner_table :
    (plusHalf (fold 0) = ![0, 1, 2] ∧ reflHalf (fold 0) = ![0, 1, 2]) ∧
    (plusHalf (fold 1) = ![1, 0, 0] ∧ reflHalf (fold 1) = ![2, 2, 1]) ∧
    (plusHalf (fold 2) = ![2, 2, 1] ∧ reflHalf (fold 2) = ![1, 0, 0]) ∧
    (plusHalf (matching 0) = ![0, 1, 1] ∧ reflHalf (matching 0) = ![0, 2, 2]) ∧
    (plusHalf (matching 1) = ![0, 0, 1] ∧ reflHalf (matching 1) = ![2, 2, 1]) ∧
    (plusHalf (merge 0 0) = ![1, 0, 0] ∧ reflHalf (merge 0 0) = ![1, 0, 0]) ∧
    (plusHalf (merge 0 1) = ![0, 1, 1] ∧ reflHalf (merge 0 1) = ![0, 0, 0]) ∧
    (plusHalf (merge 0 2) = ![0, 0, 0] ∧ reflHalf (merge 0 2) = ![0, 1, 1]) ∧
    (plusHalf (merge 1 0) = ![1, 1, 0] ∧ reflHalf (merge 1 0) = ![0, 0, 0]) ∧
    (plusHalf (merge 1 1) = ![0, 0, 1] ∧ reflHalf (merge 1 1) = ![0, 0, 1]) ∧
    (plusHalf (merge 1 2) = ![0, 0, 0] ∧ reflHalf (merge 1 2) = ![1, 1, 0]) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> funext o <;> revert o <;> decide

variable {𝔛' : Type*}

/-- The corner `𝒰 = {(b, y, y) : y ≠ b}`. -/
def cornerU : Set (Fin 3 → 𝔛') := {w | w 1 = w 2 ∧ w 0 ≠ w 1}

/-- The corner `𝒱 = {(y, y, b) : y ≠ b}`. -/
def cornerV : Set (Fin 3 → 𝔛') := {w | w 0 = w 1 ∧ w 1 ≠ w 2}

/-- The corner `𝒵 = {(b, b, b)}`. -/
def cornerZ : Set (Fin 3 → 𝔛') := {w | w 0 = w 1 ∧ w 1 = w 2}

/-- **The corners are pairwise disjoint** (`lem:record:fold-identification`(f)). -/
theorem corners_disjoint :
    Disjoint (cornerU (𝔛' := 𝔛')) cornerV ∧ Disjoint (cornerU (𝔛' := 𝔛')) cornerZ ∧
      Disjoint (cornerV (𝔛' := 𝔛')) cornerZ := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [Set.disjoint_left]
  · rintro w ⟨h12, h01⟩ ⟨h01', _⟩
    exact h01 h01'
  · rintro w ⟨_, h01⟩ ⟨h01', _⟩
    exact h01 h01'
  · rintro w ⟨_, h12⟩ ⟨_, h12'⟩
    exact h12 h12'

/-- **The fold halves lie in the listed corners** when the labels `ω_o` are distinct:
`F_1 : 𝒰 → 𝒱` and `F_2 : 𝒱 → 𝒰` (`tab:corner`). -/
theorem fold_corners (ω : Fin 3 → 𝔛') (hω : Function.Injective ω) :
    (fun o => ω (plusHalf (fold 1) o)) ∈ cornerU ∧ (fun o => ω (reflHalf (fold 1) o)) ∈ cornerV ∧
      (fun o => ω (plusHalf (fold 2) o)) ∈ cornerV ∧ (fun o => ω (reflHalf (fold 2) o)) ∈ cornerU := by
  obtain ⟨⟨-, -⟩, ⟨h1p, h1r⟩, ⟨h2p, h2r⟩, -⟩ := corner_table
  have hne : ∀ i j : Fin 3, i ≠ j → ω i ≠ ω j := fun i j h e => h (hω e)
  simp only [cornerU, cornerV, Set.mem_ofPred_eq, h1p, h1r, h2p, h2r]
  refine ⟨⟨rfl, hne 1 0 (by decide)⟩, ⟨rfl, hne 2 1 (by decide)⟩, ⟨rfl, hne 2 1 (by decide)⟩,
    ⟨rfl, hne 1 0 (by decide)⟩⟩

/-- **The matching halves lie in the listed corners** when the labels are distinct:
`E_0 : 𝒰 → 𝒰` and `E_1 : 𝒱 → 𝒱` (`tab:corner`). -/
theorem matching_corners (ω : Fin 3 → 𝔛') (hω : Function.Injective ω) :
    (fun o => ω (plusHalf (matching 0) o)) ∈ cornerU ∧
      (fun o => ω (reflHalf (matching 0) o)) ∈ cornerU ∧
      (fun o => ω (plusHalf (matching 1) o)) ∈ cornerV ∧
      (fun o => ω (reflHalf (matching 1) o)) ∈ cornerV := by
  obtain ⟨-, -, -, ⟨h0p, h0r⟩, ⟨h1p, h1r⟩, -⟩ := corner_table
  have hne : ∀ i j : Fin 3, i ≠ j → ω i ≠ ω j := fun i j h e => h (hω e)
  simp only [cornerU, cornerV, Set.mem_ofPred_eq, h0p, h0r, h1p, h1r]
  refine ⟨⟨rfl, hne 0 1 (by decide)⟩, ⟨rfl, hne 0 2 (by decide)⟩, ⟨rfl, hne 0 1 (by decide)⟩,
    ⟨rfl, hne 2 1 (by decide)⟩⟩

end Sarkozy.Labellings
