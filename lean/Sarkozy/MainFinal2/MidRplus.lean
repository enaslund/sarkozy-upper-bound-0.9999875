module

public import Sarkozy.MiddlePrimeInputs.All
public import Sarkozy.MiddleCertificates.Main

@[expose] public section





open Finset

namespace Sarkozy.MainFinal2

section Rplus

open Sarkozy.MiddlePrimeInputs
open Sarkozy.PartV Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.SpectralD.Cx
  Sarkozy.MiddleCertificates MiddleCertificates.MidCut
open scoped BigOperators InnerProductSpace

/-- **The remaining per-prime inputs of route A along C9's `R₊` chain** at a class-three prime `p`
of piece `i`, for the cut `m` (L10 or L21): the hypotheses of `routeALower_midRplus` and
`routeAUpper_midRplus` other than `2²⁴ ≤ p`, `p ≡ 3 (4)`, `X_i ≤ p`. *Hypotheses* (the
expansion data and their bounds; the scalar comparisons `hcbar`, `hηB`, `hB` with C8's bars and
the ALLp `B`). 55 fields. -/
structure MidRplusData (m : MidCut) (i : Fin 33) (p : ℕ) [Fact p.Prime] where
  hne : (Labellings.injLabellings (ZMod p) m.data.G).Nonempty
  o : Fin m.data.cut.half.card ≃ m.data.cut.Half
  nn : ℕ
  Δ : ℕ
  hn : Fintype.card m.Vertex ≤ nn
  hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ m.data.G.E ∨ (w, v) ∈ m.data.G.E)).card ≤ Δ
  hS1 : TraceMixing.coarseErr p Δ nn < 1
  ehat : ℝ
  hehat : ∀ i, Extraction.coarseError (Extraction.rowsDeg0 m.data.halfGraph i)
    (Fintype.card (ZMod p) : ℕ) (Fintype.card m.data.cut.Half : ℕ) ≤ ehat
  hehat1 : ehat < 1
  hnn : nn ≤ 12
  l : m.data.cut.Half → List m.Vertex
  hnd : ∀ i, (l i).Nodup
  hcov : ∀ i w, w ∈ fixSet m.data i ∨ w ∈ l i
  hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet m.data i
  h4 : Extraction.FourCycleBound p
  Δ' : ℕ
  hΔ' : ∀ i, ExtractionK.cmpDeg m.data.halfGraph m.data.sgn i ≤ Δ'
  𝔓 : Finset (Finset (m.data.cut.Half × m.data.cut.Half) ×
    Finset (m.data.cut.Half × m.data.cut.Half))
  h𝔓 : Extraction.IsExactPartition m.data.crossPairs 𝔓 (Extraction.nonstars m.data.crossPairs)
  wit : Finset (m.data.cut.Half × m.data.cut.Half) × Finset (m.data.cut.Half × m.data.cut.Half) →
    Fin 2 → m.data.cut.Half × m.data.cut.Half
  cx : Finset (m.data.cut.Half × m.data.cut.Half) ×
    Finset (m.data.cut.Half × m.data.cut.Half) → Finset m.data.cut.Half
  cz : Finset (m.data.cut.Half × m.data.cut.Half) ×
    Finset (m.data.cut.Half × m.data.cut.Half) → Finset m.data.cut.Half
  bucket : Finset (m.data.cut.Half × m.data.cut.Half) ×
    Finset (m.data.cut.Half × m.data.cut.Half) → ℕ
  𝔮 : ℕ
  hwit : ∀ c ∈ 𝔓, Extraction.IsWitness m.data.crossPairs c.1 c.2 (wit c)
  hcovX : ∀ c ∈ 𝔓, Extraction.IsCover m.data.crossPairs c.1 c.2 (wit c) (cx c) (cz c)
  hbucket : ∀ c ∈ 𝔓, ExtractionK.cmpOc m.data.halfGraph (m.data.crossPairs \ (c.1 ∪ c.2))
    (ExtractionK.witV (wit c)) (ExtractionK.witW (wit c)) (cx c) (cz c) ≤
    (bucket c : ℝ) * 2 ^ 𝔮
  ord : m.data.cut.Half → m.data.cut.Half → m.data.cut.Half → ℕ
  hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ'
  πc : ℕ → m.data.cut.Half → ℕ
  hπc : ∀ k, Function.Injective (πc k)
  εZ : ℝ
  Nns : ℝ
  Dcol : ℝ
  hεZ : εZ < 1
  hNns0 : 0 ≤ Nns
  hNnsB : (Real.sqrt (Fintype.card (ZMod p)))⁻¹ ^ 2 *
    ExtractionK.cmpLambda0 m.data.halfGraph m.data.sgn (Fintype.card (ZMod p))
    (Fintype.card m.data.cut.Half) ehat 2 *
    (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
    (2 : ℝ) ^ Extraction.twoCycleCount (ExtractionK.witnessIdx c.1 (wit c)) *
    Real.sqrt (2 ^ ExtractionK.cmpEx m.data.halfGraph (m.data.crossPairs \ (c.1 ∪ c.2))
    (ExtractionK.witV (wit c)) (ExtractionK.witW (wit c)) (cx c) (cz c))) *
    Real.exp (ExtractionK.cmpGamma (Fintype.card (ZMod p)) (Fintype.card m.data.cut.Half)
    Δ' * (b * 2 ^ 𝔮))) ≤ Nns
  hDcol : Extraction.collisionD1 m.data.halfGraph m.data.sgn ord (Fintype.card (ZMod p))
    (Fintype.card m.data.cut.Half) +
    Extraction.collisionD2 m.data.halfGraph m.data.sgn πc (Fintype.card (ZMod p))
    (Fintype.card m.data.cut.Half) ≤ Dcol
  hεZc : 2 * ((1 / Real.sqrt p) ^ 2 * vPairs m) + Nns + Dcol ≤ εZ
  ΓE : ℝ
  εH : ℝ
  ρβ : ℝ
  ρX : ℝ
  hΓc : ∑ k, ((2 : ℝ) ^ (m.data.Nset k).card *
    (1 + TraceMixing.coarseErr p (m.data.Nset k).card (Fintype.card m.data.cut.Half)) *
    devConst (Rprime p m.data nn l k)
    (TraceMixing.coarseErr p (m.data.Nset k).card (Fintype.card m.data.cut.Half)) ^ 2 +
    (Fintype.card m.data.cut.Half : ℝ) * 4 ^ (m.data.Nset k).card / p) ≤ ΓE
  hrow : ∀ k, ∑ l, betaG m.data.Nset (sgnZ (p := p) m.data)
    (fun t => TraceMixing.coarseErr p t (Fintype.card m.data.cut.Half)) k l ≤ ρβ
  hrowX : ∀ k, ∑ l', bX m.data.Nset (sgnZ (p := p) m.data)
    (fun t => TraceMixing.coarseErr p t (Fintype.card m.data.cut.Half))
    (Rprime p m.data nn l) k l' ≤ ρX
  hεH : ρβ + ρX ≤ εH
  hΛ0 : 0 ≤ (lamMid m : ℝ) + εH
  θ : ℝ
  hθ0 : 0 ≤ θ
  hθ : ∀ j : m.data.cut.Half,
    ((2 ^ (withOrder m o).mcross *
      (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) ((withOrder m o).tdeg j)) /
    ((1 - εZ) * ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn ((withOrder m o).t0deg j))) *
    (withOrder m o).Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn)) *
    (2 ^ Labellings.nbrCount m.data.halfGraph (univ.erase j) j /
    (1 - TraceMixing.coarseErr p (Labellings.nbrCount m.data.halfGraph (univ.erase j) j)
    (Fintype.card m.data.cut.Half))) - 1 ≤ θ ^ 2
  hcbar : (Nns + Dcol) / (1 - εZ) + ((Nns + Dcol) / (1 - εZ)) ^ 2 ≤ (cbar m i : ℝ) * rp p
  hηB : etaBcx p (2 ^ (withOrder m o).mcross *
    (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) ((withOrder m o).tdeg j)) /
    ((1 - εZ) * ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn ((withOrder m o).t0deg j)))
    (lamMid m) εH θ (rhoRow m) ΓE (lamMid m) 1
    ((PaleyB.ncSets (FiniteModel.Adj m.edge m.data.cut)).card * Fintype.card m.data.cut.Half : ℝ)
    (epsV m i)
    (Real.sqrt (lamD2 m)) (etaQ m i) ≤ (etaB m i : ℝ)
  hB : ((Nns + Dcol) / (1 - εZ)) ^ 2 /
    (1 - (BlockSpecPaper.AllpData.allpG i m.allpIdx : ℝ) * rp p) ≤
    (BlockSpecPaper.AllpData.allpB i m.allpIdx : ℝ) / p

/-- **C8's `MidPrimeInputs` from C9's route** (`routeALower_midRplus`, `routeAUpper_midRplus`,
`midPrimeInputs_of_Rplus`). -/
theorem MidRplusData.toInputs (hW : Target.Weil) (hMR : Target.MovingRoot) {m : MidCut}
    {i : Fin 33} {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3) (hX : pieceStart i ≤ p)
    (D : MidRplusData m i p) : MidPrimeInputs m i p :=
  midPrimeInputs_of_Rplus m i
    (routeALower_midRplus m i hW hMR (FiniteModel.Adj m.edge m.data.cut)
      (le_trans (pieceStart_ge i) hX) hp3 hX D.hne D.o D.hn D.hdeg D.hS1 D.hehat D.hehat1 D.hnn
      D.l D.hnd D.hcov D.hdisj D.h4 D.hΔ' D.𝔓 D.h𝔓 D.wit D.cx D.cz D.bucket D.𝔮 D.hwit D.hcovX
      D.hbucket D.ord D.hord D.πc D.hπc D.hεZ D.hNns0 D.hNnsB D.hDcol D.hεZc D.hΓc D.hrow D.hrowX
      D.hεH D.hΛ0 D.hθ0 D.hθ D.hcbar D.hηB)
    (routeAUpper_midRplus m i hW hMR (FiniteModel.Adj m.edge m.data.cut)
      (le_trans (pieceStart_ge i) hX) hp3 hX D.hne D.o D.hn D.hdeg D.hS1 D.hehat D.hehat1 D.hnn
      D.l D.hnd D.hcov D.hdisj D.h4 D.hΔ' D.𝔓 D.h𝔓 D.wit D.cx D.cz D.bucket D.𝔮 D.hwit D.hcovX
      D.hbucket D.ord D.hord D.πc D.hπc D.hεZ D.hNns0 D.hNnsB D.hDcol D.hεZc D.hΓc D.hrow D.hrowX
      D.hεH D.hΛ0 D.hθ0 D.hθ D.hcbar D.hηB D.hB)

/-- **C8's `MidInputs` from C9's data at every class-three prime of the piece.** -/
theorem midInputs_of_Rplus (hW : Target.Weil) (hMR : Target.MovingRoot) {m : MidCut}
    {i : Fin 33}
    (h : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i →
      Nonempty (MidRplusData m i p)) : MidInputs m i :=
  fun p _ hp3 hX hY => (h p hp3 hX hY).elim fun D => D.toInputs hW hMR hp3 hX

end Rplus

section L20

open Sarkozy.MiddlePrimeInputs
open Sarkozy.Labellings Sarkozy.Cuts Sarkozy.Recentering Sarkozy.BlockAdapter
  Sarkozy.BlockSpecPaper
  Sarkozy.BlockSpecPaper.AllpData Sarkozy.PartV Sarkozy.MiddleCertificates
open scoped BigOperators InnerProductSpace
open L20Cap Sarkozy.Extraction Sarkozy.ExtractionK

structure L20RectData (i : Fin 33) (p : ℕ) [Fact p.Prime] where
  [core : Nonempty (CoreT (ZMod p))]
  [pair : Nonempty (PairT (ZMod p))]
  /-- `6 ≤ p` (needed in the types below; immediate from `p ≥ 2⁴⁰`). -/
  h6 : 6 ≤ Fintype.card (ZMod p)
  m : ℝ
  NA : ℝ
  mstar : ℝ
  Nns : ℝ
  χp : ℝ
  hNA : 282 * (p : ℝ)⁻¹ ≤ NA
  hm : (coreLaw (F := ZMod p)).expect (fun C => Kbar C.1 - 1) ≤ m
  hm0 : 0 ≤ m
  hΔ : 0 < 30 * (Fintype.card (ZMod p) : ℝ)⁻¹ -
    (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) ^ 2
  hgate : cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
    (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) ≤ sP (ZMod p) m
  hNns0 : 0 ≤ Nns
  hXns : ∀ φ h : (Fin 6 → ZMod p) → ℝ,
    |(graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z *
    (graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z' => Kns z z' * h z'))| ≤
    Nns * Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z ^ 2)) *
    Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => h z ^ 2))
  hstar : |kernelForm (halfLaw h6) (halfLaw h6)
    (fun x x' => starPart6 (labels x) (labels x')) (fun _ => 1) (fun _ => 1)| ≤ mstar
  hεZ : Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ +
    mstar < 1
  hχ0 : 0 ≤ χp
  hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp
  hC1 : (sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
    (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) /
    prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid +
    Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹) /
    (1 - (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ +
    mstar)) < 1
  hH1 : (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹) /
    (1 - (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ +
    mstar)) < 1
  hgateC : (sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
    (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) /
    prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid +
    Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹) /
    (1 - (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ +
    mstar)) ≤
    (allpG i 0 : ℝ) * (√(p : ℝ))⁻¹
  hgateB : χp / (1 - (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹
    (Fintype.card (ZMod p) : ℝ)⁻¹) /
    (1 - (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ +
    mstar))) ≤ (allpB i 0 : ℝ) / p

/-- **C8's `L20W3Bounds` from C9's rectangle route** at a class-three prime `p ≥ 2⁴⁰`. -/
theorem L20RectData.toBounds (hW : Target.Weil) (hFour : Target.FourCycle) {i : Fin 33} {p : ℕ}
    [Fact p.Prime] (hp3 : p % 4 = 3) (h40 : 2 ^ 40 ≤ p) (D : L20RectData i p) :
    L20W3Bounds i p := by
  have := D.core
  have := D.pair
  have h40' : (2 : ℝ) ^ 40 ≤ p := by exact_mod_cast h40
  exact l20W3Bounds_of_rectangle i (chi_neg_one_three hp3) hW hFour D.h6 h40'
    D.hNA D.hm D.hm0 D.hΔ D.hgate D.hNns0 D.hXns D.hstar D.hεZ D.hχ0 D.hchi D.hC1 D.hH1 D.hgateC
    D.hgateB

/-- **C8's `L20Inputs` on a piece above `2⁴⁰`** from C9's rectangle route at every class-three
prime of the piece. -/
theorem l20Inputs_of_rect (hW : Target.Weil) (hFour : Target.FourCycle) {i : Fin 33}
    (hi : 2 ^ 40 ≤ pieceStart i)
    (h : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i →
      Nonempty (L20RectData i p)) : L20Inputs i :=
  fun p _ hp3 hX hY => (h p hp3 hX hY).elim fun D => D.toBounds hW hFour hp3 (le_trans hi hX)

end L20

end Sarkozy.MainFinal2
