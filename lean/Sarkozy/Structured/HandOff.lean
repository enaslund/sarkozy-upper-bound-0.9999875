module

public import Sarkozy.Structured.DensityStructured

/-!
# From the structured-energy bound to (E1)

The hand-off from `prop:record:density-structured` to the energy estimate (E1) of
`lem:energy-toolkit`, which `Sarkozy.RecordExpansion.abs_energy_sub_le_of_envelopes`
(and the first-stage and bracket-energy statements of `Sarkozy/RecordExpansion/`)
take as hypotheses.

* `mainPrice_unchanged_inputs`: for a structured energy whose inputs are all `F_A`
  (`D_{0,v} = 1`, `M_v = N`) and whose selected set `E` is nonempty, every slot
  counts as changed, with `ξ_v = R_E` and `ᾱ_v = α`. Then `Π_main = R_E^a`, which is
  the coarse price `C_E = ∏_{B ∈ E} q_B^{2a}` of (E1) (with `p^{e_p a}` for a prefix
  atom). So `density_structured` with these inputs is (E1) in its first form,
  `|Y[κ]| ≤ (1 + z) ‖κ‖ C_E Y` with outside law `μ`, where
  `z = u_L + (C_dc/C₀) L^{a-σ} α^{1-θ}` (`density_structured_coarse` with `Π = Π_main`).
* `sqrt_mul_sqrt_le_of_folded`: the geometric-mean step of `lem:sharp-first` and
  `lem:record:folded-energy`(e). If the two folded energies satisfy `𝔈_± ≤ k Π_± Y`
  and the prices multiply to `Π_+ Π_- = Π²` (the copying identity), then
  `𝔈_+^{1/2} 𝔈_-^{1/2} ≤ k Π Y`, so `B` is not squared.

What differs between the hypothesis `hE1` of `abs_energy_sub_le_of_envelopes` and the
structured-energy bound:

1. *Outside law.* `hE1` concerns `Y_{(⊗_{b∈X} D) ⊗ Ñ_{-X}}`, with the bracket `Ñ` of
   (CP3) on the atoms outside the selection. A structured energy has the reference law
   `μ_𝒮` there. The passage is `lem:bracket-energy`. Its expansion and summation are
   formalized as `Sarkozy.RecordExpansion.abs_energy_le_bracket`, which gives the
   factor `B = e^{U_0}(1 + 𝔗(d, v))`. Its per-term inputs are of two kinds:
   - the terms of the expansion of `Ñ_0 = μ + (Ñ_0 - μ)`, which are structured
     energies with outside law `μ` and selected measure `κ ⊗ ⊗_{X'} (Ñ_0 - μ)_B`.
     The structured-energy bound applies to them, provided these measures satisfy
     condition (b) of `def:record:structured-energy` (admissibility, (CP8)(a));
   - the sharp-first terms, bounded through two folded energies. When every chosen
     difference is sharp at one cut, this is `Sarkozy.Comparison.abs_term_le_folded`
     (`Sarkozy/Comparison/FoldedEnergy.lean`, another worker's module). The tagged
     bound of `lem:sharp-first` also uses variation bounds for the differences of the
     other tags, which that lemma does not treat. These are energies with the diagonal laws of the
     half marginals on the selected atoms and positive laws elsewhere, after the
     outside laws have been expanded into positive parts as in the paper's proof. The
     structured-energy bound applies to each folded energy, with
     `sqrt_mul_sqrt_le_of_folded` for the geometric mean.
2. *Representation.* `Sarkozy.RecordExpansion` writes energies as `diagonalIntegral` of
   a `tensorLaw` over all atoms. The structured energies here use a law `μ_𝒮` on
   `Slot → X` and weights `ρ` on the selected labels. `Sarkozy/Structured/Bridge.lean`
   identifies the two through the split `(∀ b, X b) ≃ X_E × X_𝒮`
   (`diagonalIntegral_tensorLaw_eq_structuredEnergy`, `abs_envelope_energy_le`). The
   files `PaperSlot`, `PaperEnergy` and `ScaleInputs` use WP-FI's representation
   instead: selected labels in the whole group, inputs through `coordinateFreeze`.
   `Sarkozy/Structured/Representation.lean` identifies that representation with the
   split one (`ρ ↦ ρ ⊗ Unif(X_𝒮)`, `μ_N` with `𝒮`-marginal `μ_𝒮`).
   `Sarkozy/Structured/EnvelopeE1.lean` combines both identifications for the
   unchanged input `F_A`.
3. *Remainders.* `hE1` uses one uniform relative error `z`. The structured-energy bound
   has the explicit error `z = u_L + (C_dc/C₀) L^{a-σ} α^{1-θ}`, with `C_dc` from
   `lem:record:density-dc` (a hypothesis here). The aggregated large-product remainders
   of the paper's sums enter through the remainders `r` of the record-expansion
   statements.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

/-- With unchanged inputs and a nonempty selected set every slot is changed, with
`ξ_v = R_E` and `ᾱ_v = α`; then `Π_main = R_E^a`. -/
theorem mainPrice_unchanged_inputs (R a θ α : ℝ) (hR : 0 ≤ R) (hα : 0 < α) :
    mainPrice (fun _ => R) (fun _ => α) (fun _ => True) a θ α = R ^ a := by
  unfold mainPrice
  have h1 : ∏ _v : Slot, R ^ (a / 72) = R ^ a := by
    rw [prod_const, card_univ, card_slot, ← Real.rpow_natCast, ← Real.rpow_mul hR]
    norm_num
  have h2 : ∏ _v ∈ univ.filter (fun _ : Slot => True), (α / α) ^ (θ / 72) = 1 := by
    apply prod_eq_one
    intro v _
    rw [div_self hα.ne', Real.one_rpow]
  rw [h1, h2, mul_one]

/-- **The geometric-mean step** (`lem:record:folded-energy`(a), (e)): from
`𝔈_± ≤ k Π_± Y` and `Π_+ Π_- = Π²`, `𝔈_+^{1/2} 𝔈_-^{1/2} ≤ k Π Y`. -/
theorem sqrt_mul_sqrt_le_of_folded {Ep Em k Pp Pm P Y : ℝ} (hEp : 0 ≤ Ep) (hEm : 0 ≤ Em)
    (hk : 0 ≤ k) (hPp : 0 ≤ Pp) (hP : 0 ≤ P) (hY : 0 ≤ Y)
    (hp : Ep ≤ k * Pp * Y) (hm : Em ≤ k * Pm * Y) (hcopy : Pp * Pm = P ^ 2) :
    Real.sqrt Ep * Real.sqrt Em ≤ k * P * Y := by
  rw [← Real.sqrt_mul hEp]
  have h1 : Ep * Em ≤ (k * Pp * Y) * (k * Pm * Y) :=
    mul_le_mul hp hm hEm (mul_nonneg (mul_nonneg hk hPp) hY)
  have h2 : (k * Pp * Y) * (k * Pm * Y) = (k * P * Y) ^ 2 := by
    calc (k * Pp * Y) * (k * Pm * Y) = k ^ 2 * (Pp * Pm) * Y ^ 2 := by ring
      _ = (k * P * Y) ^ 2 := by rw [hcopy]; ring
  rw [h2] at h1
  calc Real.sqrt (Ep * Em) ≤ Real.sqrt ((k * P * Y) ^ 2) := Real.sqrt_le_sqrt h1
    _ = k * P * Y := Real.sqrt_sq (mul_nonneg (mul_nonneg hk hP) hY)

end Sarkozy.Structured
