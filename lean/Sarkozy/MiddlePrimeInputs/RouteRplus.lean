module

public import Sarkozy.MiddlePrimeInputs.EtaQ
public import Sarkozy.MiddlePrimeInputs.StepLower
public import Sarkozy.MiddlePrimeInputs.Stars
public import Sarkozy.MiddleCertificates.Checks
public import Sarkozy.MiddleCertificates.Caps
public import Sarkozy.MiddlePrimeInputs.RchainE






@[expose] public section

namespace Sarkozy.MiddlePrimeInputs

open Finset Sarkozy.PartV Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.SpectralD.Cx
  Sarkozy.MiddleCertificates MiddleCertificates.MidCut
open scoped BigOperators InnerProductSpace

/-- The exact `ρ_row`: `15` (L10), `54` (L21). -/
def rhoRow : MidCut → ℕ
  | .l10 => 15
  | .l21 => 54

/-- The column sizes `r_j = |N(j)|` through the Boolean edges. -/
noncomputable def nsz (c : MidCut) (j : c.data.cut.Half) : ℕ :=
  (edgeNeighbours c.edge c.data.cut j).card

theorem rhoRow_nat (c : MidCut) : ∀ j : c.data.cut.Half,
    (2 ^ nsz c j - 1) * ∑ j', (2 ^ nsz c j' - 1) ≤ rhoRow c := by
  cases c
  all_goals
    unfold nsz edgeNeighbours rhoRow
    decide +kernel

/-- **`ρ_row`** of `cor:spec2:coupling` for the middle cuts, exactly. -/
theorem rhoRow_le (c : MidCut) (j : c.data.cut.Half) :
    ((2 : ℝ) ^ (c.data.Nset j).card - 1) * ∑ j', ((2 : ℝ) ^ (c.data.Nset j').card - 1) ≤
      rhoRow c := by
  have hN : c.data.Nset = edgeNeighbours c.edge c.data.cut :=
    Nset_eq_edgeNeighbours c.data c.edge (mem_edge c)
  have hcast : ∀ k : c.data.cut.Half, (2 : ℝ) ^ (c.data.Nset k).card - 1 =
      ((2 ^ nsz c k - 1 : ℕ) : ℝ) := by
    intro k
    rw [Nat.cast_sub (Nat.one_le_two_pow), hN]
    push_cast
    rfl
  simp_rw [hcast]
  exact_mod_cast rhoRow_nat c j

/-- `0 ≤ η̄_Q`. -/
theorem etaQ_nonneg (c : MidCut) : ∀ i : Fin 33, 0 ≤ etaQ c i := by
  cases c
  all_goals
    unfold etaQ etaQList
    unfold Sarkozy.MiddleCertificates.l10EtaQ Sarkozy.MiddleCertificates.l21EtaQ
    decide +kernel

/-- **Route A part (a) for L10 and L21 at the bars of piece `i`, through the `R₊` chain**
(`thm:spectral-criterion`(a), `prop:spec2:mucentre`(c2), `lem:layer12-caps`(a)), at every prime
`p ≥ X_i`, `p ≡ 3 (mod 4)`, with the `ε_V`, `η_Q`, `Λ_D`, `ρ_row` inputs and the graph facts
proved. The remaining hypotheses are the other inputs of `spectral_criterion_cut_fullRplus` at
`p`, bounded by C8's bars (`hcbar`, `hηB`); see the module docstring. -/
theorem routeALower_midRplus (m : MidCut) (i : Fin 33) {p : ℕ} [Fact p.Prime]
    (hW : Target.Weil) (hMR : Target.MovingRoot)
    (Adj : m.data.cut.Half → m.data.cut.Half → Prop) [DecidableRel Adj]
    (hp : 2 ^ 24 ≤ p) (hp3 : p % 4 = 3) (hX : pieceStart i ≤ p)
    (hne : (Labellings.injLabellings (ZMod p) m.data.G).Nonempty)
    -- the deletion order of the chain (any; for instance a concrete one, see `Orders`)
    (o : Fin m.data.cut.half.card ≃ m.data.cut.Half)
    {nn Δ : ℕ} (hn : Fintype.card m.Vertex ≤ nn)
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ m.data.G.E ∨ (w, v) ∈ m.data.G.E)).card ≤ Δ)
    (hS1 : TraceMixing.coarseErr p Δ nn < 1)
    {ehat : ℝ} (hehat : ∀ i, Extraction.coarseError (Extraction.rowsDeg0 m.data.halfGraph i)
      (Fintype.card (ZMod p) : ℕ) (Fintype.card m.data.cut.Half : ℕ) ≤ ehat) (hehat1 : ehat < 1)
    (hnn : nn ≤ 12)
    -- the orderings `l_i` of `W ∖ fix(i)` (for instance C8's `restList`)
    (l : m.data.cut.Half → List m.Vertex) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet m.data i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet m.data i)
    -- the character expansion: the data of X1's and `Extraction`'s theorems
    (h4 : Extraction.FourCycleBound p)
    {Δ' : ℕ} (hΔ' : ∀ i, ExtractionK.cmpDeg m.data.halfGraph m.data.sgn i ≤ Δ')
    (𝔓 : Finset (Finset (m.data.cut.Half × m.data.cut.Half) ×
      Finset (m.data.cut.Half × m.data.cut.Half)))
    (h𝔓 : Extraction.IsExactPartition m.data.crossPairs 𝔓 (Extraction.nonstars m.data.crossPairs))
    (wit : Finset (m.data.cut.Half × m.data.cut.Half) × Finset (m.data.cut.Half × m.data.cut.Half) →
      Fin 2 → m.data.cut.Half × m.data.cut.Half)
    (cx cz : Finset (m.data.cut.Half × m.data.cut.Half) ×
      Finset (m.data.cut.Half × m.data.cut.Half) → Finset m.data.cut.Half)
    (bucket : Finset (m.data.cut.Half × m.data.cut.Half) ×
      Finset (m.data.cut.Half × m.data.cut.Half) → ℕ) (𝔮 : ℕ)
    (hwit : ∀ c ∈ 𝔓, Extraction.IsWitness m.data.crossPairs c.1 c.2 (wit c))
    (hcovX : ∀ c ∈ 𝔓, Extraction.IsCover m.data.crossPairs c.1 c.2 (wit c) (cx c) (cz c))
    (hbucket : ∀ c ∈ 𝔓, ExtractionK.cmpOc m.data.halfGraph (m.data.crossPairs \ (c.1 ∪ c.2))
      (ExtractionK.witV (wit c)) (ExtractionK.witW (wit c)) (cx c) (cz c) ≤
        (bucket c : ℝ) * 2 ^ 𝔮)
    (ord : m.data.cut.Half → m.data.cut.Half → m.data.cut.Half → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (πc : ℕ → m.data.cut.Half → ℕ) (hπc : ∀ k, Function.Injective (πc k))
    {εZ Nns Dcol : ℝ} (hεZ : εZ < 1) (hNns0 : 0 ≤ Nns)
    (hNnsB : (Real.sqrt (Fintype.card (ZMod p)))⁻¹ ^ 2 *
        ExtractionK.cmpLambda0 m.data.halfGraph m.data.sgn (Fintype.card (ZMod p))
          (Fintype.card m.data.cut.Half) ehat 2 *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          (2 : ℝ) ^ Extraction.twoCycleCount (ExtractionK.witnessIdx c.1 (wit c)) *
            Real.sqrt (2 ^ ExtractionK.cmpEx m.data.halfGraph (m.data.crossPairs \ (c.1 ∪ c.2))
              (ExtractionK.witV (wit c)) (ExtractionK.witW (wit c)) (cx c) (cz c))) *
          Real.exp (ExtractionK.cmpGamma (Fintype.card (ZMod p)) (Fintype.card m.data.cut.Half)
            Δ' * (b * 2 ^ 𝔮))) ≤ Nns)
    (hDcol : Extraction.collisionD1 m.data.halfGraph m.data.sgn ord (Fintype.card (ZMod p))
        (Fintype.card m.data.cut.Half) +
      Extraction.collisionD2 m.data.halfGraph m.data.sgn πc (Fintype.card (ZMod p))
        (Fintype.card m.data.cut.Half) ≤ Dcol)
    (hεZc : 2 * ((1 / Real.sqrt p) ^ 2 * vPairs m) + Nns + Dcol ≤ εZ)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (m.data.Nset k).card *
          (1 + TraceMixing.coarseErr p (m.data.Nset k).card (Fintype.card m.data.cut.Half)) *
          devConst (Rprime p m.data nn l k)
            (TraceMixing.coarseErr p (m.data.Nset k).card (Fintype.card m.data.cut.Half)) ^ 2 +
        (Fintype.card m.data.cut.Half : ℝ) * 4 ^ (m.data.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG m.data.Nset (sgnZ (p := p) m.data)
      (fun t => TraceMixing.coarseErr p t (Fintype.card m.data.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX m.data.Nset (sgnZ (p := p) m.data)
      (fun t => TraceMixing.coarseErr p t (Fintype.card m.data.cut.Half))
        (Rprime p m.data nn l) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ (lamMid m : ℝ) + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : m.data.cut.Half,
      ((2 ^ (withOrder m o).mcross * (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) ((withOrder m o).tdeg j)) /
          ((1 - εZ) * ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn ((withOrder m o).t0deg j))) *
          (withOrder m o).Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn)) *
        (2 ^ Labellings.nbrCount m.data.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount m.data.halfGraph (univ.erase j) j)
            (Fintype.card m.data.cut.Half))) - 1 ≤ θ ^ 2)
    -- the comparisons with C8's bars at the piece start
    (hcbar : (Nns + Dcol) / (1 - εZ) + ((Nns + Dcol) / (1 - εZ)) ^ 2 ≤ (cbar m i : ℝ) * rp p)
    (hηB : etaBcx p (2 ^ (withOrder m o).mcross *
          (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) ((withOrder m o).tdeg j)) /
          ((1 - εZ) * ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn ((withOrder m o).t0deg j)))
        (lamMid m) εH θ (rhoRow m) ΓE (lamMid m) 1
        ((PaleyB.ncSets Adj).card * Fintype.card m.data.cut.Half : ℝ) (epsV m i)
        (Real.sqrt (lamD2 m)) (etaQ m i) ≤ (etaB m i : ℝ)) :
    RouteALower (p := p) m.data Adj (cbar m i) (tau m i) (etaQ m i) (etaB m i) (epsV m i) := by
  intro hne' g htest hg f
  obtain ⟨hΛD, hDE, hrowS, hηQc⟩ := etaQ_input m i hp3 hX
  obtain ⟨hrowV, hεVc⟩ := epsV_input m i hX
  obtain ⟨_, hτ, hc0, hv0, hv1, _⟩ := scalars m i
  have hτ' : (0 : ℝ) < tau m i := by exact_mod_cast hτ
  have hc0' : (0 : ℝ) ≤ cbar m i := by exact_mod_cast hc0
  have hv0' : (0 : ℝ) ≤ epsV m i := by exact_mod_cast hv0
  have hv1' : (epsV m i : ℝ) < 1 := by exact_mod_cast hv1
  have hq0 : (0 : ℝ) ≤ etaQ m i := by exact_mod_cast etaQ_nonneg m i
  have hεZc' : 2 * Spectral.starZstar (SecondOrder.graphPinned
        (Labellings.weilBound_of_target hW p (mid_ne_two hp)) m.data.halfGraph
        (m.data.half_nonempty hne) (errors_of_S1 m.data hn hdeg hS1).2.2.1) m.data.Nset
        (Spectral.starCoef (p := p) m.data) + Nns + Dcol ≤ εZ := by
    have := starZstar_mid m (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p (mid_ne_two hp)) m.data.halfGraph (m.data.half_nonempty hne) (errors_of_S1 m.data hn hdeg hS1).2.2.1)
    linarith
  have hcbar' : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned
          (Labellings.weilBound_of_target hW p (mid_ne_two hp))
          m.data.halfGraph (m.data.half_nonempty hne)
          (errors_of_S1 m.data hn hdeg hS1).2.2.1) m.data.Nset
            (Spectral.starCoef (p := p) m.data) + Nns + Dcol) / (1 - εZ)) ^ 2 ≤
        (cbar m i : ℝ) * rp p := by
    rw [starMstar_mid, zero_add]
    exact hcbar
  exact spectral_criterion_cut_fullRplusE (withOrder m o) hW hMR Adj (mid_ne_two hp) hp3 hn hne
    (hL_mid m o hp hnn)
    hdeg hS1 hehat hehat1 l hnd hcov hdisj h4
    hΔ' 𝔓 h𝔓 wit cx cz bucket 𝔮 hwit hcovX hbucket ord hord πc hπc hεZ hNns0 hNnsB hDcol hεZc'
    hΓc hrow hrowX hεH hΛ0 hθ0 hθ (rhoRow_le m) (mid_lam m hp3) hΛD hq0 hDE hrowS hηQc hrowV
    hεVc hv0' hc0' hcbar' le_rfl hηB le_rfl hv0' hv1' hτ' hτ' (fun ξ _ => htest ξ)
    (fun ξ _ => htest ξ) hg hg f

/-- **C8's `MidPrimeInputs`** from the lower part (for instance `routeALower_midRplus`) and the
upper part (d) (for instance C8's `routeAUpper_mid`). -/
theorem midPrimeInputs_of_Rplus (c : MidCut) (i : Fin 33) {p : ℕ} [Fact p.Prime]
    (hlow : RouteALower (p := p) c.data (FiniteModel.Adj c.edge c.data.cut) (cbar c i) (tau c i)
      (etaQ c i) (etaB c i) (epsV c i))
    (hup : RouteAUpper (p := p) c.data (FiniteModel.Adj c.edge c.data.cut) (cbar c i) (tau c i)
      (etaQ c i) (etaB c i) (epsV c i) (BlockSpecPaper.AllpData.allpG i c.allpIdx)
      (BlockSpecPaper.AllpData.allpB i c.allpIdx)) :
    MidPrimeInputs c i p :=
  ⟨hlow, hup⟩

end Sarkozy.MiddlePrimeInputs
