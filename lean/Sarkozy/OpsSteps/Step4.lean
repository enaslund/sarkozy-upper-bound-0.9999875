module

public import Sarkozy.EnvelopeSteps.PaperAveraging

@[expose] public section

/-!
# Step 4 of `thm:envelopes`(i) and the background expansion of (iii), at the paper's data (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`, Step 4 and "(iii) and (i)":
"Write `Ñ_{0,𝔅} = Ñ^inv_𝔅 + G_𝔅` at the middle blocks outside `X` and expand: `Ñ₀` outside `X` is
`∑_Z O_Z` … Every `O_Z` is a product of `R₅`-invariant measures `⪰_ι 0` … For `Z ≠ ∅`, or for `ω`
admitting no additional average, `D̄_ω ⪯ ‖D̄_ω‖ I` gives, by the general form of (E2) with the
outside measure `O_Z ⪰_ι 0`, `Y^{O_Z}[[D̄_ω]_ω] ≤ ‖D̄_ω‖ Y^{O_Z}[Diag_ω]`. For `Z = ∅` and `ω` with
all fold records equal, or without fold records, `lem:reflection-averaging`(f), (g) replace `D̄_ω`
by its additional average, whose norm is the cap `b(ω)` used in `κ_b`";
`lem:reflection-averaging`(d), (f), (g); `lem:oct24:invariant-background`(iv); (E2).

B11's `step4_averaging` proves the averaging `∑ π̃ Y^{Ñ₀}[[D_ω]] = ∑ π̃ Y^{Ñ₀}[[D̄_ω]]` (for a fixed
block set `S`). This file proves the rest of the operator part of Step 4 and reduces the field
`step4` of B11's `DegreeOps` to the caps and one inequality between **diagonal** energies:

* `jointEnergy_sum_out`: the energy is linear in the outside law;
* `OZ`, `paperEO`: the outside law `O_Z = ⊗_{𝔅 ∈ Z} G_𝔅 ⊗ ⊗_{𝔅 ∉ Z ∪ S} Ñ^inv_𝔅` and its energy
  `κ ↦ Y^{O_Z}[κ]`; **`paperEN0_expand`**: `Y^{Ñ₀}[κ] = ∑_Z Y^{O_Z}[κ]` when
  `Ñ_{0,𝔅} = Ñ^inv_𝔅 + G_𝔅` outside `S`; `OZ_positive`: `O_Z ⪰_ι 0`;
* **`jointEnergy_place_le_cap`** ((E2) with an outside law `⪰_ι 0`): `K ⪯ b I` in `L²(m)` gives
  `Y^O[[K]_ω] ≤ b Y^O[Diag_ω]`;
* **`extra_average`** (`lem:reflection-averaging`(f), (g) as an identity of energies): if the
  outside law is `α`-invariant and `α_*[K]_ω = [K']_ω`, then `Y^O[[K]] = Y^O[[½(K + K')]]`;
  `extra_average_placed`, for `K' = 𝒫'K𝒫'^*` from a placement identity;
* **`step4_of_caps`**: the field `step4` (`∑ π̃ Y^{Ñ₀}[[D_ω]] ≤ W_Z + z (∑ π̃ C_X) Y + r₄`) from
  - the averaging inputs of `step4_averaging` (the placement identity (a), the `R_h`-invariance of
    `Ñ_{0,𝔅}`, `D_ω̄ = T_ω D_ω`);
  - the split `Ñ_{0,𝔅} = Ñ^inv_𝔅 + G_𝔅` with both parts `⪰_ι 0`
    (`lem:oct24:invariant-background`(iv));
  - per `(ω, Z)` an operator `K^x_{ω,Z}` with the same `O_Z`-energy as `D̄_ω` (the additional
    average where it applies, `D̄_ω` itself elsewhere) and its cap `K^x_{ω,Z} ⪯ b_{ω,Z} I`;
  - the evaluation `∑_ω π̃_ω ∑_Z b_{ω,Z} Y^{O_Z}[Diag_ω] ≤ W_Z + z (∑ π̃ C_X) Y + r₄` (`heval`): the
    last part of (iii), the expansion of `Ñ^inv = μ + E_add + H` inside `Y^{O_Z}[Diag_ω]`, (E1) and
    the class averages `κ_H`, `κ_b`, against the labelled diagonals `W_Z`. No operator is left
    in it.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsSteps

open Sarkozy.EnvelopeSteps Sarkozy.RecordExpansion Sarkozy.Envelopes

section Generic

variable {V : Type*} [Fintype V] [DecidableEq V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **The energy is linear in the outside law.** -/
theorem jointEnergy_sum_out {ι : Type*} (s : Finset ι) (κ : ((V → A) → ℝ) →ₗ[ℝ] ℝ)
    (Ob : ι → ((V → B) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, pairFam A B b) → ℝ) :
    jointEnergy κ (∑ i ∈ s, Ob i) F = ∑ i ∈ s, jointEnergy κ (Ob i) F := by
  simp only [jointEnergy, diagonalIntegral, multilinearIntegral, tensorLaw_pairLaws_apply,
    lawDensity_sum, mul_sum, sum_mul]
  exact Finset.sum_comm

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- **(E2) with a positive outside law, at a cap**: `K ⪯ b I` in `L²(m)` and `O ⪰_c 0` give
`Y_{[K]_ω ⊗ O} ≤ b Y_{Diag_ω ⊗ O}` (`[I]_ω = Diag_ι(φ_* m)`). -/
theorem jointEnergy_place_le_cap (c : ReflectionCut V) {Ob : ((V → B) → ℝ) →ₗ[ℝ] ℝ}
    (hO : c.Positive Ob) (m : O → ℝ) (φ : O → (c.Half → A)) {K : (O → ℝ) →ₗ[ℝ] (O → ℝ)}
    {b : ℝ} (hK : OpLE m K (b • LinearMap.id)) (F : (∀ i, pairFam A B i) → ℝ) :
    jointEnergy (place c m φ K) Ob F ≤ b * jointEnergy (c.diagonalLaw (push m φ)) Ob F := by
  have hpos : c.Positive (place c m φ (b • LinearMap.id) - place c m φ K) := by
    rw [← place_sub]
    exact place_positive c φ hK
  have h := jointEnergyL_nonneg c hO F hpos
  rw [map_sub, place_smul, place_id, map_smul, smul_eq_mul, jointEnergyL_apply,
    jointEnergyL_apply] at h
  linarith

/-- **The additional averages as an identity of energies** (`lem:reflection-averaging`(f), (g)):
if the outside law is invariant under the slot permutation `α` and `α_*[K]_ω = [K']_ω`, then
`Y_{[K]_ω ⊗ O} = Y_{[½(K + K')]_ω ⊗ O}`. -/
theorem extra_average (c : ReflectionCut V) (α : V ≃ V) {Ob : ((V → B) → ℝ) →ₗ[ℝ] ℝ}
    (hO : slotPush α Ob = Ob) (m : O → ℝ) (φ : O → (c.Half → A))
    {K K' : (O → ℝ) →ₗ[ℝ] (O → ℝ)} (hKK : slotPush α (place c m φ K) = place c m φ K')
    (F : (∀ i, pairFam A B i) → ℝ) :
    jointEnergy (place c m φ K) Ob F =
      jointEnergy (place c m φ ((1 / 2 : ℝ) • (K + K'))) Ob F := by
  have h1 : jointEnergy (place c m φ K') Ob F = jointEnergy (place c m φ K) Ob F := by
    rw [← hKK, jointEnergy_slotPush α _ Ob hO F]
  rw [place_smul, place_add]
  change jointEnergy (place c m φ K) Ob F =
    jointEnergyL Ob F ((1 / 2 : ℝ) • (place c m φ K + place c m φ K'))
  rw [map_smul, map_add, jointEnergyL_apply, jointEnergyL_apply, h1, smul_eq_mul]
  ring

/-- **The additional averages at the placements**: if `α` maps the half of `c` onto itself,
commutes with its flip, fixes the outside law, and moves the placement by a relabelling `ψ` of the
objects preserving `m` (`φ ∘ α = φ ∘ ψ` on the half, `lem:reflection-averaging`(f): `R_h` maps the
fold placements of `ω` to themselves and permutes the names at the matching blocks), then
`Y_{[K]_ω ⊗ O} = Y_{[½(K + 𝒫'K𝒫'^*)]_ω ⊗ O}`. -/
theorem extra_average_placed (c : ReflectionCut V) (α : V ≃ V)
    (hhalf : ∀ v, α v ∈ c.half ↔ v ∈ c.half) (hflip : ∀ v, α (c.flip v) = c.flip (α v))
    {Ob : ((V → B) → ℝ) →ₗ[ℝ] ℝ} (hO : slotPush α Ob = Ob) (m : O → ℝ) (φ : O → (c.Half → A))
    (ψ : O ≃ O) (hm : ∀ x, m (ψ x) = m x)
    (ha : ∀ x, (fun v => φ x (halfPerm c α hhalf v)) = φ (ψ x)) (K : (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (F : (∀ i, pairFam A B i) → ℝ) :
    jointEnergy (place c m φ K) Ob F =
      jointEnergy (place c m φ ((1 / 2 : ℝ) • (K + conjObj ψ K))) Ob F := by
  apply extra_average c α hO m φ
  rw [slotPush_place c α hhalf hflip m φ K, ← place_relabel c m ψ hm φ K]
  congr 1
  funext x
  exact ha x

omit [Fintype A] [DecidableEq A] in
/-- **Transport of the placement along an equivalence of object types** (the selections of a
class have object types that depend on the selection in B11's `DegreeOps`; the class averaging of
Step 4 uses common objects): if `e : O ≃ O'` carries the marginal and the placement, and the
kernels correspond (`K'` is `K` conjugated by `e`), then `[K]_{(m, φ)} = [K']_{(m', φ')}`. -/
theorem place_congr_equiv (c : ReflectionCut V) {O O' : Type*} [Fintype O] [DecidableEq O]
    [Fintype O'] [DecidableEq O'] (e : O ≃ O') (m : O → ℝ) (m' : O' → ℝ)
    (φ : O → (c.Half → A)) (φ' : O' → (c.Half → A)) (hφ : ∀ x, φ' (e x) = φ x)
    (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (K' : (O' → ℝ) →ₗ[ℝ] (O' → ℝ))
    (hK : ∀ x y, kern m' K' (e x) (e y) = kern m K x y) :
    place c m φ K = place c m' φ' K' := by
  refine LinearMap.ext fun Φ => ?_
  change (∑ q : O × O, kern m K q.1 q.2 * Φ (c.join (φ q.1) (φ q.2))) =
    ∑ q : O' × O', kern m' K' q.1 q.2 * Φ (c.join (φ' q.1) (φ' q.2))
  let E : O × O ≃ O' × O' := Equiv.prodCongr e e
  rw [← E.sum_comp]
  refine sum_congr rfl fun q _ => ?_
  change kern m K q.1 q.2 * _ = kern m' K' (e q.1) (e q.2) * Φ (c.join (φ' (e q.1)) (φ' (e q.2)))
  rw [hK, hφ, hφ]

/-- **A degree class is a union of classes per block set** (B10's finding 2): `thm:envelopes` and
`step4_averaging` work on one block set `X`, while B4's degree classes `𝒞_n` are unions over all
`X` of one type. If Step 4 holds on every fibre `{ω ∈ 𝒞 : supp ω = X}` with `W_X`, `r_X`, it holds
on `𝒞` with `∑_X W_X`, `∑_X r_X`. -/
theorem step4_of_fibres {Ω β : Type*} [DecidableEq β] (𝒞 : Finset Ω) (supp : Ω → β)
    (wt YN0 CX : Ω → ℝ) (WZ r₄ : β → ℝ) {z Y : ℝ}
    (h : ∀ S ∈ 𝒞.image supp, ∑ ω ∈ 𝒞.filter (fun ω => supp ω = S), wt ω * YN0 ω ≤
      WZ S + z * (∑ ω ∈ 𝒞.filter (fun ω => supp ω = S), wt ω * CX ω) * Y + r₄ S) :
    ∑ ω ∈ 𝒞, wt ω * YN0 ω ≤
      ∑ S ∈ 𝒞.image supp, WZ S + z * (∑ ω ∈ 𝒞, wt ω * CX ω) * Y + ∑ S ∈ 𝒞.image supp, r₄ S := by
  have hmaps : ∀ ω ∈ 𝒞, supp ω ∈ 𝒞.image supp := fun ω hω => mem_image_of_mem supp hω
  rw [← sum_fiberwise_of_maps_to hmaps (fun ω => wt ω * YN0 ω),
    ← sum_fiberwise_of_maps_to hmaps (fun ω => wt ω * CX ω), mul_sum, sum_mul]
  calc ∑ S ∈ 𝒞.image supp, ∑ ω ∈ 𝒞 with supp ω = S, wt ω * YN0 ω
      ≤ ∑ S ∈ 𝒞.image supp, (WZ S + z * (∑ ω ∈ 𝒞.filter (fun ω => supp ω = S), wt ω * CX ω) * Y
          + r₄ S) := sum_le_sum h
    _ = _ := by rw [sum_add_distrib, sum_add_distrib]

end Generic

section Paper

open Sarkozy.TheoremCBlock Sarkozy.BlockFrame

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The outside law `O_Z`**: `G_𝔅` on the blocks of `Z` (`f 𝔅 = true`), `Ñ^inv_𝔅` on the
other blocks outside `S`. -/
noncomputable def OZ (L : ℕ) (S : Finset (BlockAtom Bk J L))
    (Ninv G : ∀ b : BlockAtom Bk J L, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (f : {b // b ∉ S} → Bool) :
    ((Slot → POut (m₀ := m₀) (blk := blk) (p := p) L S) → ℝ) →ₗ[ℝ] ℝ :=
  tensorLaw fun b : {b // b ∉ S} => if f b then G b.1 else Ninv b.1

/-- `κ ↦ Y^{O_Z}[κ] = Y_{κ ⊗ O_Z}` on joint laws on the labels of `S`. -/
noncomputable def paperEO (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L))
    (Ninv G : ∀ b : BlockAtom Bk J L, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (f : {b // b ∉ S} → Bool) :
    (((Slot → PIn (m₀ := m₀) (blk := blk) (p := p) L S) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
  jointEnergyL (OZ L S Ninv G f) (fun z => blockLift m₀ blk p L A (merge S z))

/-- **`O_Z ⪰_ι 0`**: a tensor of laws `⪰_ι 0` (`lem:oct24:invariant-background`(iv): `Ñ^inv_𝔅`
and `G_𝔅` are `⪰_ι 0`). -/
theorem OZ_positive (L : ℕ) (S : Finset (BlockAtom Bk J L))
    (Ninv G : ∀ b : BlockAtom Bk J L, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (hNinv : ∀ b ∉ S, reservedCut.Positive (Ninv b)) (hG : ∀ b ∉ S, reservedCut.Positive (G b))
    (f : {b // b ∉ S} → Bool) : reservedCut.Positive (OZ L S Ninv G f) := by
  unfold OZ
  apply ReflectionCut.Positive.tensor
  intro b
  by_cases hf : f b
  · simp only [hf, ↓reduceIte]
    exact hG b.1 b.2
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact hNinv b.1 b.2

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

omit [DecidableEq P] in
/-- **The background expansion** (proof of `thm:envelopes`, (iii)): if `Ñ_{0,𝔅} = Ñ^inv_𝔅 + G_𝔅`
at every block outside `S`, then `Y^{Ñ₀}[κ] = ∑_Z Y^{O_Z}[κ]` over the sets `Z` of blocks outside
`S`. -/
theorem paperEN0_expand (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L))
    (Ninv G : ∀ b : BlockAtom Bk J L, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (hsplit : ∀ b ∉ S, D.GB.N₀ L b = Ninv b + G b)
    (κ : ((Slot → PIn (m₀ := m₀) (blk := blk) (p := p) L S) → ℝ) →ₗ[ℝ] ℝ) :
    paperEN0 D L A S κ = ∑ f : {b // b ∉ S} → Bool, paperEO L A S Ninv G f κ := by
  unfold paperEN0 paperEO
  rw [jointEnergyL_apply]
  have hN : N0Out D L S = ∑ f : {b // b ∉ S} → Bool, OZ L S Ninv G f := by
    unfold N0Out OZ
    have e : (fun b : {b // b ∉ S} => D.GB.N₀ L b.1) =
        fun b : {b // b ∉ S} => Ninv b.1 + G b.1 := funext fun b => hsplit b.1 b.2
    rw [e]
    exact tensorLaw_add_eq_sum (fun b : {b // b ∉ S} => Ninv b.1) (fun b => G b.1)
  rw [hN, jointEnergy_sum_out]
  rfl

omit [DecidableEq P] in
/-- **The field `step4` of B11's `DegreeOps` from the caps** (`thm:envelopes`(i), Step 4 and the
background expansion of (iii); see the module docstring). On a class `Ω` of record assignments on
the block set `S`, with the raw-arm products `π̃_ω ≥ 0` (`wt`, `π̃_ω̄ = π̃_ω`), common objects with
the half marginal `m`, the placements `φ_ω` and the envelopes `K_ω = D_ω`:

* the averaging inputs of `step4_averaging` (`hinv`, `ha`, `hK`);
* `hsplit`, `hNinv`, `hG`: `Ñ_{0,𝔅} = Ñ^inv_𝔅 + G_𝔅` outside `S`, both parts `⪰_ι 0`;
* `hextra`, `hcap`: per `(ω, Z)` an operator `K^x_{ω,Z}` with the `O_Z`-energy of
  `D̄_ω = ½(K_ω + 𝒫_ω T_ω(K_ω) 𝒫_ω^*)` and `K^x_{ω,Z} ⪯ b_{ω,Z} I`;
* `heval`: `∑_ω π̃_ω ∑_Z b_{ω,Z} Y^{O_Z}[Diag_ω] ≤ W_Z + z (∑ π̃ C_X) Y + r₄`.

Then `∑_ω π̃_ω Y^{Ñ₀}[[D_ω]] ≤ W_Z + z (∑ π̃ C_X) Y + r₄`. -/
theorem step4_of_caps (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L)) (hR : ZMod 6)
    (hinv : ∀ b ∉ S, slotPush (slotREquiv hR) (D.GB.N₀ L b) = D.GB.N₀ L b)
    {Ω : Type*} [Fintype Ω] (bar : Ω → Ω) (hbar : ∀ ω, bar (bar ω) = ω) (wt : Ω → ℝ)
    (hwtb : ∀ ω, wt (bar ω) = wt ω) (hwt : ∀ ω, 0 ≤ wt ω)
    {O : Type} [Fintype O] [DecidableEq O] (m : O → ℝ)
    (φ : Ω → O → (reservedCut.Half → PIn (m₀ := m₀) (blk := blk) (p := p) L S))
    (ψ : Ω → O ≃ O) (hm : ∀ ω x, m (ψ ω x) = m x)
    (ha : ∀ ω x, (fun v => φ (bar ω) x (halfPerm reservedCut (slotREquiv hR) (slotR_half hR) v)) =
      φ ω (ψ ω x))
    (T : Ω → ((O → ℝ) →ₗ[ℝ] (O → ℝ)) →ₗ[ℝ] ((O → ℝ) →ₗ[ℝ] (O → ℝ)))
    (K : Ω → (O → ℝ) →ₗ[ℝ] (O → ℝ)) (hK : ∀ ω, K (bar ω) = T ω (K ω))
    (Ninv G : ∀ b : BlockAtom Bk J L, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (hsplit : ∀ b ∉ S, D.GB.N₀ L b = Ninv b + G b)
    (hNinv : ∀ b ∉ S, reservedCut.Positive (Ninv b)) (hG : ∀ b ∉ S, reservedCut.Positive (G b))
    (Kx : Ω → ({b // b ∉ S} → Bool) → (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (cap : Ω → ({b // b ∉ S} → Bool) → ℝ)
    (hextra : ∀ ω f, paperEO L A S Ninv G f (place reservedCut m (φ ω)
      ((1 / 2 : ℝ) • (K ω + conjObj (ψ ω) (T ω (K ω))))) =
        paperEO L A S Ninv G f (place reservedCut m (φ ω) (Kx ω f)))
    (hcap : ∀ ω f, OpLE m (Kx ω f) (cap ω f • LinearMap.id))
    {WZ z Y r₄ : ℝ} (CX YN0 : Ω → ℝ)
    (hYN0 : ∀ ω, YN0 ω = paperEN0 D L A S (place reservedCut m (φ ω) (K ω)))
    (heval : ∑ ω, wt ω * ∑ f : {b // b ∉ S} → Bool, cap ω f *
        paperEO L A S Ninv G f (reservedCut.diagonalLaw (push m (φ ω))) ≤
      WZ + z * (∑ ω, wt ω * CX ω) * Y + r₄) :
    ∑ ω, wt ω * YN0 ω ≤ WZ + z * (∑ ω, wt ω * CX ω) * Y + r₄ := by
  have hav := step4_averaging D L A S hR hinv bar hbar wt hwtb m φ ψ hm ha T K hK
  simp only [hYN0]
  rw [hav]
  refine le_trans (sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hwt ω)) heval
  rw [paperEN0_expand D L A S Ninv G hsplit]
  refine sum_le_sum fun f _ => ?_
  rw [hextra ω f]
  unfold paperEO
  rw [jointEnergyL_apply, jointEnergyL_apply]
  exact jointEnergy_place_le_cap reservedCut (OZ_positive L S Ninv G hNinv hG f) m (φ ω)
    (hcap ω f) _

omit [DecidableEq P] in
/-- **Transport along an equality of block sets**: B11's `DegreeOps` places the operators of a
selection `ω` on the labels of `Choice.support ω`; a class of `thm:envelopes` lives on one block set
`S` (B10's finding 2). If `support ω = S`, the placement can be read on the labels of `S`. -/
theorem paperEN0_transport (L : ℕ) (A : Finset ℤ) {S S' : Finset (BlockAtom Bk J L)} (hS : S = S')
    {O : Type} [Fintype O] [DecidableEq O] (m : O → ℝ)
    (φ : O → (reservedCut.Half → PIn (m₀ := m₀) (blk := blk) (p := p) L S))
    (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) :
    paperEN0 D L A S (place reservedCut m φ K) =
      paperEN0 D L A S' (place reservedCut m (hS ▸ φ) K) := by
  subst hS
  rfl

omit [DecidableEq P] in
/-- **`step4_of_caps` on a finite set of selections** (the form of the field `step4` of B11's
`DegreeOps`: sums over `ω ∈ 𝒞`), for a class `𝒞` closed under the pairing `ω ↦ ω̄`, all on the
block set `S`. -/
theorem step4_of_caps_finset (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L)) (hR : ZMod 6)
    (hinv : ∀ b ∉ S, slotPush (slotREquiv hR) (D.GB.N₀ L b) = D.GB.N₀ L b)
    {Ω : Type*} (𝒞 : Finset Ω) (bar : Ω → Ω) (hbar𝒞 : ∀ ω ∈ 𝒞, bar ω ∈ 𝒞)
    (hbar : ∀ ω ∈ 𝒞, bar (bar ω) = ω) (wt : Ω → ℝ)
    (hwtb : ∀ ω ∈ 𝒞, wt (bar ω) = wt ω) (hwt : ∀ ω ∈ 𝒞, 0 ≤ wt ω)
    {O : Type} [Fintype O] [DecidableEq O] (m : O → ℝ)
    (φ : Ω → O → (reservedCut.Half → PIn (m₀ := m₀) (blk := blk) (p := p) L S))
    (ψ : Ω → O ≃ O) (hm : ∀ ω ∈ 𝒞, ∀ x, m (ψ ω x) = m x)
    (ha : ∀ ω ∈ 𝒞, ∀ x,
      (fun v => φ (bar ω) x (halfPerm reservedCut (slotREquiv hR) (slotR_half hR) v)) =
        φ ω (ψ ω x))
    (T : Ω → ((O → ℝ) →ₗ[ℝ] (O → ℝ)) →ₗ[ℝ] ((O → ℝ) →ₗ[ℝ] (O → ℝ)))
    (K : Ω → (O → ℝ) →ₗ[ℝ] (O → ℝ)) (hK : ∀ ω ∈ 𝒞, K (bar ω) = T ω (K ω))
    (Ninv G : ∀ b : BlockAtom Bk J L, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (hsplit : ∀ b ∉ S, D.GB.N₀ L b = Ninv b + G b)
    (hNinv : ∀ b ∉ S, reservedCut.Positive (Ninv b)) (hG : ∀ b ∉ S, reservedCut.Positive (G b))
    (Kx : Ω → ({b // b ∉ S} → Bool) → (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (cap : Ω → ({b // b ∉ S} → Bool) → ℝ)
    (hextra : ∀ ω ∈ 𝒞, ∀ f, paperEO L A S Ninv G f (place reservedCut m (φ ω)
      ((1 / 2 : ℝ) • (K ω + conjObj (ψ ω) (T ω (K ω))))) =
        paperEO L A S Ninv G f (place reservedCut m (φ ω) (Kx ω f)))
    (hcap : ∀ ω ∈ 𝒞, ∀ f, OpLE m (Kx ω f) (cap ω f • LinearMap.id))
    {WZ z Y r₄ : ℝ} (CX YN0 : Ω → ℝ)
    (hYN0 : ∀ ω ∈ 𝒞, YN0 ω = paperEN0 D L A S (place reservedCut m (φ ω) (K ω)))
    (heval : ∑ ω ∈ 𝒞, wt ω * ∑ f : {b // b ∉ S} → Bool, cap ω f *
        paperEO L A S Ninv G f (reservedCut.diagonalLaw (push m (φ ω))) ≤
      WZ + z * (∑ ω ∈ 𝒞, wt ω * CX ω) * Y + r₄) :
    ∑ ω ∈ 𝒞, wt ω * YN0 ω ≤ WZ + z * (∑ ω ∈ 𝒞, wt ω * CX ω) * Y + r₄ := by
  let bar' : 𝒞 → 𝒞 := fun ω => ⟨bar ω.1, hbar𝒞 ω.1 ω.2⟩
  have h := step4_of_caps D L A S hR hinv (Ω := 𝒞) bar'
    (fun ω => Subtype.ext (hbar ω.1 ω.2)) (fun ω => wt ω.1) (fun ω => hwtb ω.1 ω.2)
    (fun ω => hwt ω.1 ω.2) m (fun ω => φ ω.1) (fun ω => ψ ω.1) (fun ω => hm ω.1 ω.2)
    (fun ω => ha ω.1 ω.2) (fun ω => T ω.1) (fun ω => K ω.1) (fun ω => hK ω.1 ω.2) Ninv G hsplit
    hNinv hG (fun ω => Kx ω.1) (fun ω => cap ω.1) (fun ω => hextra ω.1 ω.2)
    (fun ω => hcap ω.1 ω.2) (WZ := WZ) (z := z) (Y := Y) (r₄ := r₄) (fun ω => CX ω.1)
    (fun ω => YN0 ω.1) (fun ω => hYN0 ω.1 ω.2) (by
      rw [Finset.sum_coe_sort 𝒞 (fun ω => wt ω * ∑ f : {b // b ∉ S} → Bool, cap ω f *
        paperEO L A S Ninv G f (reservedCut.diagonalLaw (push m (φ ω)))),
        Finset.sum_coe_sort 𝒞 (fun ω => wt ω * CX ω)]
      exact heval)
  rwa [Finset.sum_coe_sort 𝒞 (fun ω => wt ω * YN0 ω),
    Finset.sum_coe_sort 𝒞 (fun ω => wt ω * CX ω)] at h

end Paper

end Sarkozy.OpsSteps
