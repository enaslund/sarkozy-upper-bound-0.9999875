module

public import Sarkozy.EnvelopeSteps.Averaging
public import Sarkozy.EnvelopeSteps.PaperEnergy
public import Sarkozy.PartVLaws.InvariantBackground

@[expose] public section

/-!
# The averaging of Step 4 at the paper's data

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`, Step 4 ("At every atom outside `X`,
`Ñ_{0,𝔅}` is `R_5`-invariant and `⪰_ι 0` (`lem:oct24:invariant-background`(iv)) … applying
`lem:reflection-averaging`(d), the main terms become `∑ π̃ Y^{Ñ₀}[[D̄_ω]_ω]`").

* `slotREquiv h`: the slot reflection `R_h(u₀, u₁, ℓ) = (h − u₀, u₁, ℓ)` as a permutation (it is
  V2's `PartVLaws.slotR`, `slotREquiv_apply`); `slotR_half`, `slotR_flip`: it maps the half of
  the reserved cut `ι` onto itself and commutes with its flip;
* `N0Out`, `paperEN0`: the energy `κ ↦ Y^{Ñ₀}[κ]` against `⊗_{𝔅 ∉ S} Ñ_{0,𝔅}`;
* **`paperEN0_slotPush`** (`lem:reflection-averaging`(c)): if every outside `Ñ_{0,𝔅}` is
  `R_h`-invariant (`lem:oct24:invariant-background`(iv), an input), `Y^{Ñ₀}` is `R_h`-invariant;
* **`step4_averaging`** (`lem:reflection-averaging`(d) at the paper's data): with the placement
  identity of (a) as an input,
  `∑ π_ω Y^{Ñ₀}[[K_ω]_ω] = ∑ π_ω Y^{Ñ₀}[[½(K_ω + 𝒫_ω T_ω(K_ω) 𝒫_ω^*)]_ω]` for operators with
  `K_ω̄ = T_ω(K_ω)` (with `K_ω = D_ω` this is the first half of Step 4);
* **`step3_paper`**: `step3_of_couplings` with the energies `Y^Ñ`, `Y^{Ñ₀}` of the paper's data;
* **`paperEN_diag_eq_varDiag`**: with product objects, `Y^Ñ[Diag_ω]` is B10's `varDiag`, so the
  (E1) input `hE1` of the degree classes is the (E1) input `hDN` of B10's variance classes.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeSteps

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.Envelopes

/-- **The slot reflection `R_h`** as a permutation of the slots. -/
def slotREquiv (h : ZMod 6) : Slot ≃ Slot where
  toFun v := (h - v.1, v.2.1, v.2.2)
  invFun v := (h - v.1, v.2.1, v.2.2)
  left_inv v := by simp
  right_inv v := by simp

theorem slotREquiv_apply (h : ZMod 6) (v : Slot) : slotREquiv h v = PartVLaws.slotR h v := rfl

theorem mem_reservedCut_half (v : Slot) : v ∈ reservedCut.half ↔ v.2.2 = 0 := by
  revert v
  decide

/-- `R_h` maps the half of `ι` onto itself. -/
theorem slotR_half (h : ZMod 6) (v : Slot) :
    slotREquiv h v ∈ reservedCut.half ↔ v ∈ reservedCut.half := by
  rw [mem_reservedCut_half, mem_reservedCut_half]
  rfl

/-- `R_h` commutes with the flip of `ι`. -/
theorem slotR_flip (h : ZMod 6) (v : Slot) :
    slotREquiv h (reservedCut.flip v) = reservedCut.flip (slotREquiv h v) := rfl

section Paper

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

/-- `Ñ₀_{-S}`: the tensor of the laws `Ñ_{0,𝔅}` outside `S`. -/
noncomputable def N0Out (L : ℕ) (S : Finset (BlockAtom Bk J L)) :
    ((Slot → POut (m₀ := m₀) (blk := blk) (p := p) L S) → ℝ) →ₗ[ℝ] ℝ :=
  tensorLaw fun b : {b // b ∉ S} => D.GB.N₀ L b.1

/-- `κ ↦ Y^{Ñ₀}[κ] = Y_{κ ⊗ Ñ₀_{-S}}` on joint laws on the labels of `S`. -/
noncomputable def paperEN0 (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L)) :
    (((Slot → PIn (m₀ := m₀) (blk := blk) (p := p) L S) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
  jointEnergyL (N0Out D L S) (fun z => blockLift m₀ blk p L A (merge S z))

omit [DecidableEq P] in
/-- **`lem:reflection-averaging`(c) at the paper's data**: if every outside `Ñ_{0,𝔅}` is invariant
under the slot permutation `α`, so is `Y^{Ñ₀}`. -/
theorem paperEN0_slotPush (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L)) (α : Slot ≃ Slot)
    (hinv : ∀ b ∉ S, slotPush α (D.GB.N₀ L b) = D.GB.N₀ L b)
    (κ : ((Slot → PIn (m₀ := m₀) (blk := blk) (p := p) L S) → ℝ) →ₗ[ℝ] ℝ) :
    paperEN0 D L A S (slotPush α κ) = paperEN0 D L A S κ := by
  unfold paperEN0
  rw [jointEnergyL_apply, jointEnergyL_apply]
  apply jointEnergy_slotPush
  unfold N0Out
  rw [slotPush_tensorLaw]
  congr 1
  funext b
  exact hinv b.1 b.2

omit [DecidableEq P] in
/-- **`lem:reflection-averaging`(d) at the paper's data** (the averaging of Step 4): for a family
`Ω` of record assignments on the block set `S` with an involution `ω ↦ ω̄` and weights
`π_ω̄ = π_ω`, common objects with the half marginal `m`, placements `φ_ω` satisfying the placement
identity of (a) (`φ_ω̄ ∘ R_h = φ_ω ∘ ψ_ω`, `ψ_ω` preserving `m`), outside laws `Ñ_{0,𝔅}` invariant
under `R_h` (`lem:oct24:invariant-background`(iv)), and operators with `K_ω̄ = T_ω(K_ω)`:
`∑ π_ω Y^{Ñ₀}[[K_ω]_ω] = ∑ π_ω Y^{Ñ₀}[[½(K_ω + 𝒫_ω T_ω(K_ω) 𝒫_ω^*)]_ω]`. -/
theorem step4_averaging (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L)) (hR : ZMod 6)
    (hinv : ∀ b ∉ S, slotPush (slotREquiv hR) (D.GB.N₀ L b) = D.GB.N₀ L b)
    {Ω : Type*} [Fintype Ω] (bar : Ω → Ω) (hbar : ∀ ω, bar (bar ω) = ω) (π : Ω → ℝ)
    (hπ : ∀ ω, π (bar ω) = π ω) {O : Type} [Fintype O] [DecidableEq O] (m : O → ℝ)
    (φ : Ω → O → (reservedCut.Half → PIn (m₀ := m₀) (blk := blk) (p := p) L S))
    (ψ : Ω → O ≃ O) (hm : ∀ ω x, m (ψ ω x) = m x)
    (ha : ∀ ω x, (fun v => φ (bar ω) x (halfPerm reservedCut (slotREquiv hR) (slotR_half hR) v)) =
      φ ω (ψ ω x))
    (T : Ω → ((O → ℝ) →ₗ[ℝ] (O → ℝ)) →ₗ[ℝ] ((O → ℝ) →ₗ[ℝ] (O → ℝ)))
    (K : Ω → (O → ℝ) →ₗ[ℝ] (O → ℝ)) (hK : ∀ ω, K (bar ω) = T ω (K ω)) :
    ∑ ω, π ω * paperEN0 D L A S (place reservedCut m (φ ω) (K ω)) =
      ∑ ω, π ω * paperEN0 D L A S (place reservedCut m (φ ω)
        ((1 / 2 : ℝ) • (K ω + conjObj (ψ ω) (T ω (K ω))))) :=
  reflection_average_placed reservedCut (slotREquiv hR) (slotR_half hR) (slotR_flip hR)
    (paperEN0 D L A S) (paperEN0_slotPush D L A S (slotREquiv hR) hinv) bar hbar π hπ m φ ψ hm
    ha T K hK

omit [DecidableEq P] in
/-- **The identity is placed blockwise**: the kernel of `I` relative to the product marginal is
the product of the kernels of the identities. -/
theorem kern_id_prod {S : Type} [Fintype S] [DecidableEq S] {O : S → Type}
    [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)] (m : ∀ b, O b → ℝ) (x y : ∀ b, O b) :
    kern (prodWeight m) LinearMap.id x y = ∏ b, kern (m b) LinearMap.id (x b) (y b) := by
  simp only [kern_id]
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte, prodWeight]
  · rw [ite_eq_right hxy]
    obtain ⟨b, hb⟩ : ∃ b, x b ≠ y b := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    symm
    exact prod_eq_zero (mem_univ b) (ite_eq_right hb)

omit [DecidableEq P] in
/-- **(E1) of Step 1 is B10's (E1) for the diagonals**: with product objects, the energy
`Y^Ñ[Diag_ω]` of the diagonal copy of the product half marginal is B10's
`varDiag` (`Y[Diag_X ⊗ Ñ]` with the half marginals `φ_{𝔅*} m_𝔅`). So the input `hE1` of
`paperDegreeOps` is the same statement as the input `hDN` of B10's `VarStepsAt.ofRecords`. -/
theorem paperEN_diag_eq_varDiag (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (O : {b // b ∈ Choice.support ω} → Type) [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)]
    (m : ∀ b, O b → ℝ) (φ : ∀ b, O b → (reservedCut.Half → BlockLabel m₀ blk p L b.1)) :
    paperEN D L A (Choice.support ω)
        (reservedCut.diagonalLaw (push (prodWeight m) (prodPlace reservedCut φ))) =
      varDiag D L A ω (fun b => if hb : b ∈ Choice.support ω then push (m ⟨b, hb⟩) (φ ⟨b, hb⟩)
        else fun _ => 0) := by
  set S := Choice.support ω
  rw [← place_id, place_tensor reservedCut m φ (fun _ => LinearMap.id) LinearMap.id
    (kern_id_prod m)]
  simp only [place_id]
  let L' : ∀ b : BlockAtom Bk J L, SlotMeasure (BlockLabel m₀ blk p L b) := fun b =>
    if hb : b ∈ S then reservedCut.diagonalLaw (push (m ⟨b, hb⟩) (φ ⟨b, hb⟩)) else D.GB.N L b
  have h1 : (fun b : {b // b ∈ S} => L' b.1) =
      fun b : {b // b ∈ S} => reservedCut.diagonalLaw (push (m b) (φ b)) := by
    funext b
    simp only [L', b.2, ↓reduceDIte]
    rfl
  have h2 : (fun b : {b // b ∉ S} => L' b.1) = fun b : {b // b ∉ S} => D.GB.N L b.1 := by
    funext b
    simp only [L', b.2, ↓reduceDIte]
  have key := jointEnergy_tensor S L' (blockLift m₀ blk p L A)
  rw [h1, h2] at key
  unfold paperEN
  rw [jointEnergyL_apply]
  change jointEnergy _ (NOut D L S) _ = _
  unfold NOut
  rw [key]
  unfold varDiag
  congr 2
  funext b
  by_cases hb : b ∈ Choice.support ω
  · have hb' : b ∈ S := hb
    simp only [L', hb, hb', ↓reduceDIte, ↓reduceIte]
  · have hb' : b ∉ S := hb
    simp only [L', hb, hb', ↓reduceDIte, ↓reduceIte]

omit [DecidableEq P] in
/-- **Step 3 at the paper's data** (`lem:orbit-coupon`(i), the coupling expansion, without the
orbit improvement): if `D_ω = ∑_C c(C) C` and every placed coupling has
`|Y^Ñ[[C]] − Y^{Ñ₀}[[C]]| ≤ e + r_C`, then
`Y^Ñ[[D_ω]] ≤ Y^{Ñ₀}[[D_ω]] + M(D) e + ∑ |c(C)| r_C`, `M(D) = ∑ |c(C)|`. -/
theorem step3_paper (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L)) {O : Type}
    [Fintype O] [DecidableEq O] (m : O → ℝ)
    (φ : O → (reservedCut.Half → PIn (m₀ := m₀) (blk := blk) (p := p) L S))
    {ι : Type*} (s : Finset ι) (coef : ι → ℝ) (Cop : ι → (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (Dop : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (hD : Dop = ∑ i ∈ s, coef i • Cop i) (e : ℝ) (r : ι → ℝ)
    (herr : ∀ i ∈ s, |paperEN D L A S (place reservedCut m φ (Cop i)) -
      paperEN0 D L A S (place reservedCut m φ (Cop i))| ≤ e + r i) :
    paperEN D L A S (place reservedCut m φ Dop) ≤
      paperEN0 D L A S (place reservedCut m φ Dop) + (∑ i ∈ s, |coef i|) * e +
        ∑ i ∈ s, |coef i| * r i :=
  step3_of_couplings reservedCut _ _ m φ s coef Cop Dop hD e r herr

end Paper

end Sarkozy.EnvelopeSteps
