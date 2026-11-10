module

public import Sarkozy.L20Cap.CrossPaper
public import Sarkozy.L20Cap.SanityX1
public import Sarkozy.DLK.Basic
public import Sarkozy.Labellings.TargetBridge

/-!
# The caps of L20 at a prime, with every input in the form of the paper or of X1 / WP-FI

`paper/sections/20_middle_reference.tex`, `prop:l20-collisions`(b), "The caps", for `p ≥ 2²⁰`,
`p ≡ 3 (mod 4)`. **`l20_prime_caps_paper`** composes the bridges of this package:

* `x_g` is the paper's `x_g` (`xPaper`; `xG_le_xPaper`);
* `N_A` is any upper bound of X1's leaf partition sum for the eight cross pairs
  (`l20_prime_caps_X1`), at a threshold `64 ≤ Q ≤ p`;
* `N_ns` is given in X1's form (`hXns`; `hXns_of_compressed` supplies it from compressed class
  data);
* `D` is any uniform bound of WP-FI's incident-weight row sums (`hD_of_incident`).

The remaining hypotheses are the class data (`h𝔓`, `hrec`) and the numbers `N_A`, `N_ns`, `D`,
`𝔪`, `m_⋆`, `χ⁺_p` with their bounds, and the gates of `cert:l20-grid`.
**`l20_prime_caps_target`** takes the literature inputs in the agreed form, H1 (`Target.Weil`) and
H6 (`Target.FourCycle`). **`l20_prime_caps_oct24`** moreover takes the explicit, weaker collision
constant `D = D_1 + D_{≥2}` of `lem:oct24-collision` (`Doct`), so that no collision hypothesis
remains.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts Sarkozy.Labellings Sarkozy.Extraction
  Sarkozy.ExtractionK

variable {p : ℕ} [Fact p.Prime] [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]

/-- **The caps of L20 at a prime `p ≥ 2²⁰`** (`prop:l20-collisions`(b)), with `x_g` the paper's,
`N_A` from X1's leaf partition (`cor:soft-kernels`(a)), `N_ns` in X1's form and `D` from WP-FI's
`cor:incident-weights`: `-C₂₀ ⪯ T ⪯ 1 + χ⁺_p/(1 - H₂₀)`. -/
theorem l20_prime_caps_paper (hm1 : quadraticChar (ZMod p) (-1) = -1) (hW : WeilBound (ZMod p))
    (h4 : FourCycleBound p) (h6 : 6 ≤ Fintype.card (ZMod p))
    (h20 : (2 : ℝ) ^ 20 ≤ Fintype.card (ZMod p)) {m NA D mstar Nns χp : ℝ}
    (𝔓 : Finset (Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6)))
    (h𝔓 : IsExactPartition Ex8 𝔓 (nonstars Ex8))
    (rec : Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6) → LeafRecordData (Fin 6))
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex8 c) {Q : ℝ} (hQ : 64 ≤ Q) (hQp : Q ≤ p)
    (hNAle : ∑ c ∈ 𝔓, (Real.sqrt p)⁻¹ ^ (rec c).k * leafCoef G6 D20Z Q 6 Ex8 c (rec c) ≤ NA)
    (hm : (coreLaw (F := ZMod p)).expect (fun C => Kbar C.1 - 1) ≤ m) (hm0 : 0 ≤ m)
    (hΔ : 0 < 30 * (Fintype.card (ZMod p) : ℝ)⁻¹ -
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) ^ 2)
    (hgate : cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) ≤ sP (ZMod p) m)
    (hD0 : 0 ≤ D)
    (ord : Fin 6 → Fin 6 → Fin 6 → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → Fin 6 → ℕ) (hπ : ∀ k, Function.Injective (π k))
    (hDle : ∀ x : CoreT (ZMod p) × PairT (ZMod p), Avoid x →
      collisionIncident1 G6 D20Z ord (Fintype.card (ZMod p)) 6 (labels x) +
        collisionIncident2 G6 D20Z π (Fintype.card (ZMod p)) 6 (labels x) ≤ D)
    (hNns0 : 0 ≤ Nns)
    (hXns : ∀ φ h : (Fin 6 → ZMod p) → ℝ,
      |(graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z *
          (graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z' => Kns z z' * h z'))| ≤
        Nns * Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z ^ 2)) *
          Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => h z ^ 2)))
    (hstar : |kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => starPart6 (labels x) (labels x')) (fun _ => 1) (fun _ => 1)| ≤ mstar)
    (hεZ : Nns + D + mstar < 1)
    (hχ0 : 0 ≤ χp)
    (hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp)
    (hC1 : (sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) /
      prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid + D) /
        (1 - (Nns + D + mstar)) < 1)
    (hH1 : (Nns + D) / (1 - (Nns + D + mstar)) < 1) (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    -((sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) /
        prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid + D) /
          (1 - (Nns + D + mstar))) *
        nrm (halfLaw h6) f ^ 2 ≤ kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ∧
      kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ≤
        (1 + χp / (1 - (Nns + D) / (1 - (Nns + D + mstar)))) * nrm (halfLaw h6) f ^ 2 := by
  have h64 : (64 : ℝ) ≤ Fintype.card (ZMod p) := le_trans (by norm_num) h20
  exact l20_prime_caps_X1ns hm1 hW h4 h6 𝔓 h𝔓 rec hrec (by linarith) hQp
    (SanityX1.leafEhat_G6_lt hQ) hNAle hm hm0 hΔ (xG_le_xPaper (ZMod p) hm0 NA h20) hgate hD0
    (hD_of_incident hm1 hW h6 (SanityX1.coarseError_G6_lt h64) ord hord π hπ hDle) hNns0 hXns
    hstar hεZ hχ0 hchi hC1 hH1 f

/-- **The caps of L20 at a prime `p ≥ 2²⁰` from the agreed literature inputs**: as
`l20_prime_caps_paper`, with H1 (`Target.Weil`) and H6 (`Target.FourCycle`, `thm:dl:K`) in place
of `WeilBound (ZMod p)` and `FourCycleBound p` (`weilBound_of_target`, `DLK.fourCycleBound`). -/
theorem l20_prime_caps_target (hm1 : quadraticChar (ZMod p) (-1) = -1) (hWeil : Target.Weil)
    (hFour : Target.FourCycle) (h6 : 6 ≤ Fintype.card (ZMod p))
    (h20 : (2 : ℝ) ^ 20 ≤ Fintype.card (ZMod p)) {m NA D mstar Nns χp : ℝ}
    (𝔓 : Finset (Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6)))
    (h𝔓 : IsExactPartition Ex8 𝔓 (nonstars Ex8))
    (rec : Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6) → LeafRecordData (Fin 6))
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex8 c) {Q : ℝ} (hQ : 64 ≤ Q) (hQp : Q ≤ p)
    (hNAle : ∑ c ∈ 𝔓, (Real.sqrt p)⁻¹ ^ (rec c).k * leafCoef G6 D20Z Q 6 Ex8 c (rec c) ≤ NA)
    (hm : (coreLaw (F := ZMod p)).expect (fun C => Kbar C.1 - 1) ≤ m) (hm0 : 0 ≤ m)
    (hΔ : 0 < 30 * (Fintype.card (ZMod p) : ℝ)⁻¹ -
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) ^ 2)
    (hgate : cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) ≤ sP (ZMod p) m)
    (hD0 : 0 ≤ D)
    (ord : Fin 6 → Fin 6 → Fin 6 → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → Fin 6 → ℕ) (hπ : ∀ k, Function.Injective (π k))
    (hDle : ∀ x : CoreT (ZMod p) × PairT (ZMod p), Avoid x →
      collisionIncident1 G6 D20Z ord (Fintype.card (ZMod p)) 6 (labels x) +
        collisionIncident2 G6 D20Z π (Fintype.card (ZMod p)) 6 (labels x) ≤ D)
    (hNns0 : 0 ≤ Nns)
    (hXns : ∀ φ h : (Fin 6 → ZMod p) → ℝ,
      |(graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z *
          (graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z' => Kns z z' * h z'))| ≤
        Nns * Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z ^ 2)) *
          Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => h z ^ 2)))
    (hstar : |kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => starPart6 (labels x) (labels x')) (fun _ => 1) (fun _ => 1)| ≤ mstar)
    (hεZ : Nns + D + mstar < 1)
    (hχ0 : 0 ≤ χp)
    (hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp)
    (hC1 : (sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) /
      prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid + D) /
        (1 - (Nns + D + mstar)) < 1)
    (hH1 : (Nns + D) / (1 - (Nns + D + mstar)) < 1) (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    -((sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) /
        prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid + D) /
          (1 - (Nns + D + mstar))) *
        nrm (halfLaw h6) f ^ 2 ≤ kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ∧
      kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ≤
        (1 + χp / (1 - (Nns + D) / (1 - (Nns + D + mstar)))) * nrm (halfLaw h6) f ^ 2 := by
  have hp2 : p ≠ 2 := by
    have : 6 ≤ p := by rwa [ZMod.card] at h6
    omega
  exact l20_prime_caps_paper hm1 (weilBound_of_target hWeil p hp2) (DLK.fourCycleBound hFour hp2)
    h6 h20 𝔓 h𝔓 rec hrec hQ hQp hNAle hm hm0 hΔ hgate hD0 ord hord π hπ hDle hNns0 hXns hstar hεZ
    hχ0 hchi hC1 hH1 f

/-- **The explicit collision constant** `D_1 + D_{≥2}` of `lem:oct24-collision` for the L20
kernel (WP-FI's `collisionD1`, `collisionD2` for `G6`, `D₂₀`, `n = 6`). -/
noncomputable def Doct (p : ℕ) [Fact p.Prime] (ord : Fin 6 → Fin 6 → Fin 6 → ℕ)
    (π : ℕ → Fin 6 → ℕ) : ℝ :=
  collisionD1 G6 D20Z ord (Fintype.card (ZMod p)) 6 +
    collisionD2 G6 D20Z π (Fintype.card (ZMod p)) 6

/-- **The caps of L20 at a prime `p ≥ 2²⁰` with `D` explicit**: as `l20_prime_caps_target`, with
the uniform collision constant `D = D_1 + D_{≥2}` of `lem:oct24-collision` (`hD_of_oct24`) in
place of the paper's `D_bal`. This `D` is weaker than `D_bal`, but no collision hypothesis
remains. -/
theorem l20_prime_caps_oct24 (hm1 : quadraticChar (ZMod p) (-1) = -1) (hWeil : Target.Weil)
    (hFour : Target.FourCycle) (h6 : 6 ≤ Fintype.card (ZMod p))
    (h20 : (2 : ℝ) ^ 20 ≤ Fintype.card (ZMod p)) {m NA mstar Nns χp : ℝ}
    (ord : Fin 6 → Fin 6 → Fin 6 → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → Fin 6 → ℕ) (hπ : ∀ k, Function.Injective (π k))
    (𝔓 : Finset (Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6)))
    (h𝔓 : IsExactPartition Ex8 𝔓 (nonstars Ex8))
    (rec : Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6) → LeafRecordData (Fin 6))
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex8 c) {Q : ℝ} (hQ : 64 ≤ Q) (hQp : Q ≤ p)
    (hNAle : ∑ c ∈ 𝔓, (Real.sqrt p)⁻¹ ^ (rec c).k * leafCoef G6 D20Z Q 6 Ex8 c (rec c) ≤ NA)
    (hm : (coreLaw (F := ZMod p)).expect (fun C => Kbar C.1 - 1) ≤ m) (hm0 : 0 ≤ m)
    (hΔ : 0 < 30 * (Fintype.card (ZMod p) : ℝ)⁻¹ -
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) ^ 2)
    (hgate : cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) ≤ sP (ZMod p) m)
    (hNns0 : 0 ≤ Nns)
    (hXns : ∀ φ h : (Fin 6 → ZMod p) → ℝ,
      |(graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z *
          (graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z' => Kns z z' * h z'))| ≤
        Nns * Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z ^ 2)) *
          Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => h z ^ 2)))
    (hstar : |kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => starPart6 (labels x) (labels x')) (fun _ => 1) (fun _ => 1)| ≤ mstar)
    (hεZ : Nns + Doct p ord π + mstar < 1)
    (hχ0 : 0 ≤ χp)
    (hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp)
    (hC1 : (sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) /
      prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid + Doct p ord π) /
        (1 - (Nns + Doct p ord π + mstar)) < 1)
    (hH1 : (Nns + Doct p ord π) / (1 - (Nns + Doct p ord π + mstar)) < 1)
    (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    -((sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) /
        prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid + Doct p ord π) /
          (1 - (Nns + Doct p ord π + mstar))) *
        nrm (halfLaw h6) f ^ 2 ≤ kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ∧
      kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ≤
        (1 + χp / (1 - (Nns + Doct p ord π) / (1 - (Nns + Doct p ord π + mstar)))) *
          nrm (halfLaw h6) f ^ 2 := by
  have hp2 : p ≠ 2 := by
    have : 6 ≤ p := by rwa [ZMod.card] at h6
    omega
  have h64 : (64 : ℝ) ≤ Fintype.card (ZMod p) := le_trans (by norm_num) h20
  have hW := weilBound_of_target hWeil p hp2
  have hq : (0 : ℝ) < Fintype.card (ZMod p) := by exact_mod_cast Fintype.card_pos
  have hD0 : 0 ≤ Doct p ord π := add_nonneg
    (collisionD1_nonneg G6 D20Z ord hq (SanityX1.coarseError_G6_lt h64))
    (collisionD2_nonneg G6 D20Z π hq (SanityX1.coarseError_G6_lt h64))
  exact l20_prime_caps_X1ns hm1 hW (DLK.fourCycleBound hFour hp2) h6 𝔓 h𝔓 rec hrec (by linarith)
    hQp (SanityX1.leafEhat_G6_lt hQ) hNAle hm hm0 hΔ (xG_le_xPaper (ZMod p) hm0 NA h20) hgate hD0
    (hD_of_oct24 hm1 hW h6 (SanityX1.coarseError_G6_lt h64) ord hord π hπ) hNns0 hXns hstar hεZ
    hχ0 hchi hC1 hH1 f

end Sarkozy.L20Cap
