module

public import Sarkozy.OpsSteps.Step3
public import Sarkozy.OpsSteps.Step4
public import Sarkozy.PartVLaws.InvariantFrame
public import Sarkozy.EnvelopeSteps.MidPlacement

@[expose] public section

/-!
# Bridges from proved invariances to the inputs of Steps 3 and 4 (OPS-S)

`paper/sections/23_envelopes.tex`, `lem:oct24:invariant-background`(iv),
`lem:reflection-averaging`(a), (f), (g), `lem:orbit-coupon` ("then `R_{h*}[C]_ω = [hC]_ω` for a
permutation `C ↦ hC`").

* `slotPush_eq_iff_slotInv`: B11's `slotPush (slotREquiv h) κ = κ` is V2's `SlotInv (slotR h) κ`;
* **`frame_step4_inputs`**: at a middle block whose background `Ñ_{0,𝔅}` is V3's frame `Ñ₀`
  (`FrameData.Nbr0`), V2's `lem:oct24:invariant-background`(iv) (`InvariantFrame.lean`) gives the
  inputs `hinv` (at `h = 5`), `hsplit` (`Ñ^inv = NbrInv`, `G = P⁻¹ G_pol`), `hNinv`, `hG` of
  `Step4.step4_of_caps` at that block, under V2's hypotheses (the exchangeable one-layer `E` law,
  V1's datum hypotheses, the layer caps with `k_𝔱 w_𝔱 ≤ v_𝔱`, `b > 3`, `f₁ + h₁ ≥ 0`);
* `kern_conjObj`, **`hconj_tensor`**: the relabelling of a tensor coupling is blockwise, so the
  input `hconj` of `hpush_of_relabel` reduces to the basic couplings of one block;
* **`extra_ha_blocks`**: the placement identity of the additional averages
  (`lem:reflection-averaging`(f)) at the middle placements, from B11's `midPlace_fold`,
  `midPlace_matching` and the fold table: the input `ha` of `Step4.extra_average_placed`;
* **`hpush_of_relabel`**: the input `hpush` of `Step3.step3_orbit` (`R_{h*}[C]_ω = [hC]_ω`) from a
  placement identity `φ ∘ R_h = φ ∘ ψ` (`lem:reflection-averaging`(a), (f): `R_h` fixes the fold
  placements and permutes the matching names; at the middle placements B11's `midPlace_*`) and the
  relabelling of the couplings `kern(𝒫' C 𝒫'^*) = kern(hC)` (the matching couplings
  `M_{ab} ↦ M_{σa σb}`, `𝒥 ↦ 𝒥`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsSteps

open Sarkozy.EnvelopeSteps Sarkozy.RecordExpansion Sarkozy.Envelopes Sarkozy.TheoremC

/-- **B11's invariance is V2's**: `slotPush (slotREquiv h) κ = κ` iff `SlotInv (slotR h) κ`. -/
theorem slotPush_eq_iff_slotInv {X : Type} [Fintype X] [DecidableEq X] (h : ZMod 6)
    (κ : SlotMeasure X) :
    slotPush (slotREquiv h) κ = κ ↔ PartVLaws.SlotInv (PartVLaws.slotR h) κ := by
  have e : (⇑(slotREquiv h) : Slot → Slot) = PartVLaws.slotR h := funext (slotREquiv_apply h)
  constructor
  · intro hκ f
    have := congrArg (fun L : SlotMeasure X => L f) hκ
    simp only [slotPush_apply, e] at this
    exact this
  · intro hκ
    refine LinearMap.ext fun f => ?_
    rw [slotPush_apply, e]
    exact hκ f

/-- **The background inputs of Step 4 at a middle block, from V2's
`lem:oct24:invariant-background`(iv)**: if `Ñ_{0,𝔅}` is V3's frame `Ñ₀`, then it is
`R₅`-invariant, it splits as `Ñ^inv + G` with `Ñ^inv = NbrInv` and `G = P⁻¹ G_pol`, and both parts
are `⪰_ι 0`. -/
theorem frame_step4_inputs {X : Type} [Fintype X] [DecidableEq X] (N₀ : SlotMeasure X)
    (Fd : PartVRecords.FrameData X) (hN : N₀ = Fd.Nbr0) (hE : PartVLaws.OneLayerExch Fd.F)
    (h₂ : PartV.DatumHyp (Fd.F.two .E) (Fd.F.two .F) (Fd.F.two .L))
    (h₁ : PartV.DatumHyp (Fd.F.one .E) (Fd.F.one .F) (Fd.F.one .L))
    (k : PartV.PType → ℝ) (hcap : PartV.MiddleLayerCaps Fd.F k Fd.r)
    (hdom : ∀ t, k t * Fd.W.w t ≤ Fd.W.v t) (hb : 3 < Fd.b) (hfh : 0 ≤ Fd.I.f₁ + Fd.I.h₁) :
    slotPush (slotREquiv 5) N₀ = N₀ ∧ N₀ = PartVLaws.NbrInv Fd + Fd.P⁻¹ • Fd.Gpol ∧
      reservedCut.Positive (PartVLaws.NbrInv Fd) ∧ reservedCut.Positive (Fd.P⁻¹ • Fd.Gpol) := by
  subst hN
  refine ⟨(slotPush_eq_iff_slotInv 5 _).2 (PartVLaws.Nbr0_slotR5_inv Fd hE h₂ h₁),
    PartVLaws.Nbr0_eq_NbrInv_add Fd, PartVLaws.NbrInv_reserved Fd k hcap hdom hb, ?_⟩
  have hP : 0 ≤ Fd.P⁻¹ :=
    inv_nonneg.mpr (le_trans zero_le_one (PartV.one_le_midPoly Fd.W Fd.r_nonneg))
  exact (PartVLaws.Gpol_reserved Fd hfh).smul hP

section Push

variable {O : Type*} [Fintype O] [DecidableEq O] {V X : Type*} [Fintype V] [DecidableEq V]

/-- **The input `hpush` of `step3_orbit` from a placement identity**: if `R_h` (here any `α`
preserving the half of `c` and commuting with its flip) moves the placement by a relabelling `ψ`
of the objects preserving `m` (`φ ∘ α = φ ∘ ψ` on the half), and the relabelled coupling
`𝒫' C 𝒫'^*` has the kernel of the coupling `hC`, then `α_*[C]_ω = [hC]_ω`. -/
theorem hpush_of_relabel (c : ReflectionCut V) (α : V ≃ V)
    (hhalf : ∀ v, α v ∈ c.half ↔ v ∈ c.half) (hflip : ∀ v, α (c.flip v) = c.flip (α v))
    (m : O → ℝ) (φ : O → (c.Half → X)) (ψ : O ≃ O) (hm : ∀ x, m (ψ x) = m x)
    (ha : ∀ x, (fun v => φ x (halfPerm c α hhalf v)) = φ (ψ x)) {ι : Type*}
    (Cop : ι → (O → ℝ) →ₗ[ℝ] (O → ℝ)) (hC : ι → ι)
    (hconj : ∀ i x y, kern m (conjObj ψ (Cop i)) x y = kern m (Cop (hC i)) x y) (i : ι) :
    slotPush α (place c m φ (Cop i)) = place c m φ (Cop (hC i)) := by
  rw [slotPush_place c α hhalf hflip m φ (Cop i)]
  have e : (fun x v => φ x (halfPerm c α hhalf v)) = fun x => φ (ψ x) := funext ha
  rw [e, place_relabel c m ψ hm φ (Cop i)]
  exact place_eq_of_kern c m φ (hconj i)

omit [Fintype O] in
/-- **The kernel of a relabelled operator**: for a relabelling `ψ` preserving `m`,
`kern(𝒫 K 𝒫^*)(x, y) = kern(K)(ψ⁻¹ x, ψ⁻¹ y)`. -/
theorem kern_conjObj (m : O → ℝ) (ψ : O ≃ O) (hm : ∀ x, m (ψ x) = m x)
    (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (x y : O) :
    kern m (conjObj ψ K) x y = kern m K (ψ.symm x) (ψ.symm y) := by
  have hδ : (fun z => delta y (ψ z)) = delta (ψ.symm y) := by
    funext z
    simp only [delta, ← Equiv.eq_symm_apply]
  have hmx : m x = m (ψ.symm x) := by rw [← hm (ψ.symm x), Equiv.apply_symm_apply]
  simp only [kern, conjObj, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, transportL]
  rw [hδ, hmx]

end Push

section Tensor

/-- **The relabelling of a tensor coupling is blockwise** (the input `hconj` of
`hpush_of_relabel` for the couplings of the expansion): if a product relabelling `ψ = ∏ ψ_𝔟`
(identity at the fold blocks, the name permutation at the matching blocks) preserves the marginals,
and at every block the relabelled basic coupling has the kernel of the coupling `h_𝔟(k)`
(`M_{ab} ↦ M_{σa σb}`, `𝒥 ↦ 𝒥`), then the relabelled tensor coupling `C_κ` has the kernel of
`C_{h(κ)}`, `h(κ)_𝔟 = h_𝔟(κ_𝔟)`. -/
theorem hconj_tensor {S : Type*} [Fintype S] [DecidableEq S] {O : S → Type*}
    [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)] (m : ∀ b, O b → ℝ) (ψ : ∀ b, O b ≃ O b)
    (hm : ∀ b x, m b (ψ b x) = m b x) {Kb : S → Type*}
    (Cpl : ∀ b, Kb b → (O b → ℝ) →ₗ[ℝ] (O b → ℝ)) (hb : ∀ b, Kb b → Kb b)
    (hconjb : ∀ b k x y,
      kern (m b) (conjObj (ψ b) (Cpl b k)) x y = kern (m b) (Cpl b (hb b k)) x y)
    (Cop : (∀ b, Kb b) → ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ))
    (hCop : ∀ κ x y, kern (prodWeight m) (Cop κ) x y = ∏ b, kern (m b) (Cpl b (κ b)) (x b) (y b))
    (κ : ∀ b, Kb b) (x y : ∀ b, O b) :
    kern (prodWeight m) (conjObj (Equiv.piCongrRight ψ) (Cop κ)) x y =
      kern (prodWeight m) (Cop fun b => hb b (κ b)) x y := by
  have hΨ : ∀ z, prodWeight m (Equiv.piCongrRight ψ z) = prodWeight m z := by
    intro z
    unfold prodWeight
    exact prod_congr rfl fun b _ => hm b (z b)
  rw [kern_conjObj (prodWeight m) (Equiv.piCongrRight ψ) hΨ, hCop, hCop]
  refine prod_congr rfl fun b _ => ?_
  rw [← hconjb b (κ b) (x b) (y b), kern_conjObj (m b) (ψ b) (hm b)]
  rfl

end Tensor

section Extra

open Sarkozy.Labellings

variable {S : Type*} {Y : S → Type*}

/-- The relabelling `x ↦ x ∘ ψ_{h,s}` of an object triple (the name permutation of a matching
record under `R_h`). -/
def relabelTriple (σ : Equiv.Perm (Fin 3)) (Z : Type*) : (Fin 3 → Z) ≃ (Fin 3 → Z) :=
  Equiv.arrowCongr σ.symm (Equiv.refl Z)

theorem relabelTriple_apply (σ : Equiv.Perm (Fin 3)) {Z : Type*} (x : Fin 3 → Z) :
    relabelTriple σ Z x = fun o => x (σ o) := by
  funext o
  simp [relabelTriple, Equiv.arrowCongr_apply]

/-- **The placement identity of the additional average** (`lem:reflection-averaging`(f)) at the
middle placements: if every fold block carries the fold `k` fixed by `R_h`
(`F₁ ∘ R₃ = F₁`, `F₂ ∘ R₁ = F₂`, `fold_reflection_table`) and every matching block `j` carries
`E_{s_j}`, then `R_h` moves the product placement by the relabelling that is the identity at the
fold blocks and `ψ_{h,s_j}` at the matching blocks: the input `ha` of `extra_average_placed`
(with `prodPlace_slotR`). -/
theorem extra_ha_blocks (h : ZMod 6) (hh : h = 1 ∨ h = 3 ∨ h = 5) (k : Fin 3)
    (hk : ∀ u, Labellings.fold k (chamberRefl h u) = Labellings.fold k u) (isFold : S → Bool)
    (s : S → Fin 2)
    (x : ∀ j, Fin 3 → Y j) :
    (fun v => prodPlace reservedCut
      (fun j => if isFold j then midPlace (Labellings.fold k) else midPlace (matching (s j))) x
        (halfPerm reservedCut (slotREquiv h) (slotR_half h) v)) =
      prodPlace reservedCut
        (fun j => if isFold j then midPlace (Labellings.fold k) else midPlace (matching (s j)))
        (Equiv.piCongrRight (fun j => if isFold j then Equiv.refl (Fin 3 → Y j)
          else relabelTriple (psiRefl h (s j)) (Y j)) x) := by
  refine prodPlace_slotR h _ _ _ (fun j y => ?_) x
  by_cases hj : isFold j
  · simp only [hj, ↓reduceIte, Equiv.refl_apply]
    exact midPlace_fold h k k hk y
  · simp only [hj, Bool.false_eq_true, ↓reduceIte, relabelTriple_apply]
    exact midPlace_matching h hh (s j) y

end Extra

end Sarkozy.OpsSteps
