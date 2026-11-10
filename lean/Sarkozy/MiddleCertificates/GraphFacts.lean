module

public import Sarkozy.MiddleCertificates.RouteUpper
public import Sarkozy.SpectralD.RootChecks
public import Sarkozy.SpectralD.CxInputs
public import Sarkozy.SpectralD.CxCouplingCut

/-!
# The graph facts of route A for the middle cuts L10 and L21

`paper/sections/20_middle_reference.tex`, proof of `lem:layer12-caps`(a): the spectral data
satisfy (S1) at `X ≥ Q₃ > 2²⁴` ("the graphs have at most twelve vertices and maximum degree at
most four"). The `p`-independent inputs of `spectral_criterion_cut_full` for the actual data of
L10 and L21:

* `mid_card`: at most `12` vertices; `mid_hdeg`: degree at most `Δ = 4`;
* `mid_S1`: `e_4(p, 12) < 1` for `p ≥ 2²⁴` (`def:spec:data`, (S1));
* `mid_rho`: `(2^{r_j} - 1) ∑_{j'} (2^{r_{j'}} - 1) ≤ 54` (`ρ_row` of `cor:spec2:coupling`);
* `mid_deltaE`: `‖Δ^E‖ ≤ 2` (`Λ_D`, `lem:spec:degone`);
* `mid_lam`: `𝐇 ⪯ λ̄ I` at class three, with `λ̄ = 3` (L10) and `λ̄ = 4` (L21), the largest
  eigenvalues of `𝐇` (exact certificates);
* `instLinearOrderHalf`: the order of the half by the code `u`;
* **`routeALower_mid`**: `RouteALower` for L10 and L21 at `p ≥ 2²⁴` from the remaining inputs of
  `spectral_criterion_cut_full` (the expansion data, the coupling and degree-one numbers and the
  bounds of the inputs at `p` by the bars); **`routeAUpper_mid`**: the same for part (d), with
  `ε_ϱ²/(1 - g p^{-1/2}) ≤ B/p`.
-/

@[expose] public section

namespace Sarkozy.MiddleCertificates

open Finset Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.SpectralD.Cx MidCut
open scoped BigOperators InnerProductSpace

theorem mid_card (c : MidCut) : Fintype.card c.Vertex ≤ 12 := by
  cases c <;> simp [MidCut.Vertex, Fintype.card_prod, ZMod.card]

theorem mid_hdeg (c : MidCut) :
    ∀ v, (univ.filter (fun w => (v, w) ∈ c.data.G.E ∨ (w, v) ∈ c.data.G.E)).card ≤ 4 := by
  intro v
  have h : (univ.filter (fun w => (v, w) ∈ c.data.G.E ∨ (w, v) ∈ c.data.G.E)) =
      univ.filter (fun w => c.edge v w = true ∨ c.edge w v = true) := by
    apply Finset.filter_congr
    intro w _
    rw [mem_edge, mem_edge]
  rw [h]
  revert v
  cases c <;> decide

/-- **(S1) for the middle cuts from `2²⁴`**: `e_4(p, 12) < 1`. -/
theorem mid_S1 {p : ℕ} (hp : 2 ^ 24 ≤ p) : TraceMixing.coarseErr p 4 12 < 1 := by
  have hp' : (2 : ℝ) ^ 24 ≤ (p : ℝ) := by exact_mod_cast hp
  have h := Root.coarseErr_antitone (q := (2 : ℝ) ^ 24) (by norm_num) hp' 4 12
  refine lt_of_le_of_lt h ?_
  have hs : Real.sqrt ((2 : ℝ) ^ 24) = 2 ^ 12 := by
    rw [show (2 : ℝ) ^ 24 = (2 ^ 12) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold TraceMixing.coarseErr
  rw [hs]
  norm_num

theorem mid_Nset_card (c : MidCut) (j : c.data.cut.Half) : (c.data.Nset j).card ≤ 2 := by
  rw [Nset_eq_edgeNeighbours c.data c.edge (mem_edge c)]
  revert j
  cases c <;> decide

theorem mid_card_half (c : MidCut) : Fintype.card c.data.cut.Half ≤ 6 := by
  cases c <;> decide

/-- `ρ_row ≤ 54`. -/
theorem mid_rho (c : MidCut) (j : c.data.cut.Half) :
    ((2 : ℝ) ^ (c.data.Nset j).card - 1) * ∑ j', ((2 : ℝ) ^ (c.data.Nset j').card - 1) ≤ 54 := by
  have hb : ∀ k : c.data.cut.Half, 0 ≤ (2 : ℝ) ^ (c.data.Nset k).card - 1 ∧
      (2 : ℝ) ^ (c.data.Nset k).card - 1 ≤ 3 := by
    intro k
    have h1 : (1 : ℝ) ≤ 2 ^ (c.data.Nset k).card := one_le_pow₀ (by norm_num)
    have h2 : (2 : ℝ) ^ (c.data.Nset k).card ≤ 2 ^ 2 :=
      pow_le_pow_right₀ (by norm_num) (mid_Nset_card c k)
    constructor <;> linarith
  have hs : ∑ j', ((2 : ℝ) ^ (c.data.Nset j').card - 1) ≤ 18 := by
    calc _ ≤ ∑ _j' : c.data.cut.Half, (3 : ℝ) := sum_le_sum fun k _ => (hb k).2
      _ = 3 * Fintype.card c.data.cut.Half := by
          rw [sum_const, card_univ, nsmul_eq_mul]
          ring
      _ ≤ 3 * 6 := by
          have := mid_card_half c
          have h' : (Fintype.card c.data.cut.Half : ℝ) ≤ 6 := by exact_mod_cast this
          linarith
      _ = 18 := by norm_num
  have hs0 : 0 ≤ ∑ j', ((2 : ℝ) ^ (c.data.Nset j').card - 1) := sum_nonneg fun k _ => (hb k).1
  calc _ ≤ 3 * 18 := mul_le_mul (hb j).2 hs hs0 (by norm_num)
    _ = 54 := by norm_num

/-- `‖Δ^E‖ ≤ 2` at every prime. -/
theorem mid_deltaE (c : MidCut) {p : ℕ} [Fact p.Prime] :
    NormLe (deltaE (sgnZ (p := p) c.data)) 2 :=
  Cx.deltaE_normLe c.data (fun k => by exact_mod_cast mid_Nset_card c k)

/-- `λ̄(𝐇)`: `3` for L10, `4` for L21 (the largest eigenvalues of `𝐇`). -/
def lamMid : MidCut → ℕ
  | .l10 => 3
  | .l21 => 4

/-- The exact factor of `λ̄ I - 𝐇` (zero for L10, the two triangle indicators for L21). -/
def lamFactorTable : MidCut → List (List ℤ)
  | .l10 => []
  | .l21 => [[1, 0, 1, 0, 1, 0], [0, 1, 0, 1, 0, 1]]

/-- The residual shift of `λ̄ I - 𝐇 - B^*B`. -/
def lamShift : MidCut → ℤ
  | .l10 => 2
  | .l21 => 0

noncomputable def lamR (c : MidCut) (a b : c.data.cut.Half) : ℤ :=
  (if a = b then (lamMid c : ℤ) else 0) - modelH c a b

noncomputable def lamFactor (c : MidCut) : c.data.cut.Half → c.data.cut.Half → ℤ :=
  atTable c (lamFactorTable c)

/-- The certificate of `λ̄ I - 𝐇 ⪰ 0`. -/
def LamChecks (c : MidCut) : Prop :=
  (∀ a b, 1 * lamR c a b - gramReal (lamFactor c) (fun _ _ => 0) a b =
      1 * lamR c b a - gramReal (lamFactor c) (fun _ _ => 0) b a) ∧
  (∀ a b : c.data.cut.Half, 1 * (0 : ℤ) - gramImag (lamFactor c) (fun _ _ => 0) a b =
      -(1 * 0 - gramImag (lamFactor c) (fun _ _ => 0) b a)) ∧
  ∀ a, ∑ b, (|(if a = b then lamShift c else 0) -
      (1 * lamR c a b - gramReal (lamFactor c) (fun _ _ => 0) a b)| +
      |1 * (0 : ℤ) - gramImag (lamFactor c) (fun _ _ => 0) a b|) ≤ lamShift c

theorem lamChecks (c : MidCut) : LamChecks c := by
  unfold LamChecks
  cases c <;> decide +kernel

/-- **`λ̄(𝐇)` at class three** (`hlam` of `spectral_criterion_cut_full`): `w^*𝐇w ≤ λ̄|w|²`. -/
theorem mid_lam (c : MidCut) {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3) (w : c.data.cut.Half → ℂ) :
    (qform (PaleyB.modelHC c.data.Nset (sgnZ (p := p) c.data)) w).re ≤
      (lamMid c : ℝ) * ∑ j, ‖w j‖ ^ 2 := by
  have hH : PaleyB.modelHC c.data.Nset (sgnZ (p := p) c.data) =
      fun a b => ((modelH c a b : ℤ) : ℂ) := by
    funext a b
    rw [FiniteModel.modelHC_three c.data c.edge (mem_edge c) hp3, ((models c) a b).2]
  have h0 := qform_nonneg_of_gaussian_factor (lamR c) (fun _ _ => 0) (lamFactor c)
    (fun _ _ => 0) 1 (lamShift c) (by norm_num) (lamChecks c).1 (lamChecks c).2.1
    (lamChecks c).2.2 w
  have hA : (fun a b => gaussian (lamR c a b) ((fun _ _ => (0 : ℤ)) a b)) =
      fun a b => (if a = b then ((lamMid c : ℝ) : ℂ) else 0) - ((modelH c a b : ℤ) : ℂ) := by
    funext a b
    apply Complex.ext <;> by_cases h : a = b <;> simp [gaussian, lamR, h]
  rw [hA, qform_shift] at h0
  rw [hH]
  linarith

theorem mid_code_inj (c : MidCut) :
    ∀ a b : c.data.cut.Half, c.code a.1 = c.code b.1 → a = b := by
  cases c <;> decide

/-- The order of the half by the code `u`. -/
instance instLinearOrderHalf (c : MidCut) : LinearOrder c.data.cut.Half :=
  LinearOrder.lift' (fun k => c.code k.1) (fun a b h => mid_code_inj c a b h)

theorem mid_ne_two {p : ℕ} (hp : 2 ^ 24 ≤ p) : p ≠ 2 := by
  omega

/-- **Route A for the middle cuts L10 and L21 at a prime `p ≥ 2²⁴`, `p ≡ 3 (mod 4)`, with the graph
facts discharged** (`lem:layer12-caps`(a), proof): `RouteALower` from the remaining inputs of
`spectral_criterion_cut_full` (the nonstar partition with its records, the collision orders, the
coupling and degree-one numbers, and the bounds of the inputs at `p` by the bars). Discharged here:
`p ≠ 2`, `|W| ≤ 12`, `Δ = 4`, (S1) `e_4(p, 12) < 1`, the orderings `l_i` (`restList`),
`ρ_row = 54`, `λ̄(𝐇) = lamMid`, `Λ_D = 2`. -/
theorem routeALower_mid (m : MidCut) {p : ℕ} [Fact p.Prime] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : m.data.cut.Half → m.data.cut.Half → Prop) [DecidableRel Adj]
    (hp : 2 ^ 24 ≤ p) (hp3 : p % 4 = 3)
    (hne : (Labellings.injLabellings (ZMod p) m.data.G).Nonempty)
    -- the character expansion: the data of X1's and `Extraction`'s theorems
    (h4 : Extraction.FourCycleBound p)
    {Δ' : ℕ} (hΔ' : ∀ i, ExtractionK.cmpDeg m.data.halfGraph m.data.sgn i ≤ Δ')
    (𝔓 : Finset (Finset (m.data.cut.Half × m.data.cut.Half) × Finset (m.data.cut.Half × m.data.cut.Half)))
    (h𝔓 : Extraction.IsExactPartition m.data.crossPairs 𝔓 (Extraction.nonstars m.data.crossPairs))
    (wit : Finset (m.data.cut.Half × m.data.cut.Half) × Finset (m.data.cut.Half × m.data.cut.Half) →
      Fin 2 → m.data.cut.Half × m.data.cut.Half)
    (cx cz : Finset (m.data.cut.Half × m.data.cut.Half) × Finset (m.data.cut.Half × m.data.cut.Half) →
      Finset m.data.cut.Half)
    (bucket : Finset (m.data.cut.Half × m.data.cut.Half) × Finset (m.data.cut.Half × m.data.cut.Half) → ℕ) (𝔮 : ℕ)
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
        ExtractionK.cmpLambda0 m.data.halfGraph m.data.sgn (Fintype.card (ZMod p)) (Fintype.card m.data.cut.Half)
          (TraceMixing.coarseErr p 4 12) 2 *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          (2 : ℝ) ^ Extraction.twoCycleCount (ExtractionK.witnessIdx c.1 (wit c)) *
            Real.sqrt (2 ^ ExtractionK.cmpEx m.data.halfGraph (m.data.crossPairs \ (c.1 ∪ c.2))
              (ExtractionK.witV (wit c)) (ExtractionK.witW (wit c)) (cx c) (cz c))) *
          Real.exp (ExtractionK.cmpGamma (Fintype.card (ZMod p)) (Fintype.card m.data.cut.Half) Δ' * (b * 2 ^ 𝔮))) ≤ Nns)
    (hDcol : Extraction.collisionD1 m.data.halfGraph m.data.sgn ord (Fintype.card (ZMod p))
        (Fintype.card m.data.cut.Half) +
      Extraction.collisionD2 m.data.halfGraph m.data.sgn πc (Fintype.card (ZMod p))
        (Fintype.card m.data.cut.Half) ≤ Dcol)
    (hεZc : 2 * Spectral.starZstar (SecondOrder.graphPinned
        (Labellings.weilBound_of_target hW p (mid_ne_two hp)) m.data.halfGraph (m.data.half_nonempty hne)
        (errors_of_S1 m.data (mid_card m) (mid_hdeg m) (mid_S1 hp)).2.2.1) m.data.Nset (Spectral.starCoef (p := p) m.data) + Nns + Dcol ≤
        εZ)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (m.data.Nset k).card *
          (1 + TraceMixing.coarseErr p (m.data.Nset k).card (Fintype.card m.data.cut.Half)) *
          devConst (Rprime p m.data 12 (restList m.data) k)
            (TraceMixing.coarseErr p (m.data.Nset k).card (Fintype.card m.data.cut.Half)) ^ 2 +
        (Fintype.card m.data.cut.Half : ℝ) * 4 ^ (m.data.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG m.data.Nset (sgnZ (p := p) m.data)
      (fun t => TraceMixing.coarseErr p t (Fintype.card m.data.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX m.data.Nset (sgnZ (p := p) m.data)
      (fun t => TraceMixing.coarseErr p t (Fintype.card m.data.cut.Half)) (Rprime p m.data 12 (restList m.data)) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ (lamMid m : ℝ) + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : m.data.cut.Half,
      m.data.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 12) ^ 2 *
        (2 ^ Labellings.nbrCount m.data.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount m.data.halfGraph (univ.erase j) j)
            (Fintype.card m.data.cut.Half))) - 1 ≤ θ ^ 2)
    -- the certified numbers of `lem:spec:degone`
    {ηQ εV : ℝ} (hηQ0 : 0 ≤ ηQ)
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) m.data k l = 0 then mXcut p m.data k l else 0) ≤ ρs)
    (hηQc : 2 / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card m.data.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mVcut p m.data k l) ≤ ρv)
    (hεVc : ((Fintype.card m.data.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) +
        (p : ℝ) / ((p : ℝ) - 1) * rp p * ρv ≤ εV) (hεV : 0 ≤ εV)
    {cbar ηQbar ηBbar εVbar s : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p (mid_ne_two hp))
          m.data.halfGraph (m.data.half_nonempty hne)
          (errors_of_S1 m.data (mid_card m) (mid_hdeg m) (mid_S1 hp)).2.2.1) m.data.Nset (Spectral.starCoef (p := p) m.data) +
          Nns + Dcol) / (1 - εZ)) ^ 2 ≤ cbar * rp p)
    (hηQ : ηQ ≤ ηQbar)
    (hηB : etaBcx p (m.data.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 12) ^ 2 *
        (m.data.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 12))⁻¹)
        (lamMid m) εH θ 54 ΓE (lamMid m) 1
        ((PaleyB.ncSets Adj).card * Fintype.card m.data.cut.Half : ℝ) εV 2 ηQ ≤ ηBbar)
    (hεVb : εV ≤ εVbar) (hεV0 : 0 ≤ εVbar) (hεV1 : εVbar < 1) (hs : 0 < s) :
    RouteALower (p := p) m.data Adj cbar s ηQbar ηBbar εVbar :=
  routeALower_of_full m.data hW hMR Adj (mid_ne_two hp) hp3 (mid_card m) hne (mid_hdeg m)
    (mid_S1 hp) (restList m.data) (restList_nodup _) (restList_cover _) (restList_disj _) h4 hΔ'
    𝔓 h𝔓 wit cx cz bucket 𝔮 hwit hcovX hbucket ord hord πc hπc hεZ hNns0 hNnsB hDcol hεZc hΓc hrow
    hrowX hεH hΛ0 hθ0 hθ (mid_rho m) (mid_lam m hp3) (by norm_num) hηQ0 (mid_deltaE m) hrowS hηQc
    hrowV hεVc hεV hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hs

/-- **Route A part (d) for the middle cuts L10 and L21 at `p ≥ 2²⁴`, `p ≡ 3 (mod 4)`, with the
graph facts discharged**: `RouteAUpper` from the inputs of `routeALower_mid` and
`ε_ϱ²/(1 - g p^{-1/2}) ≤ B/p`. -/
theorem routeAUpper_mid (m : MidCut) {p : ℕ} [Fact p.Prime] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : m.data.cut.Half → m.data.cut.Half → Prop) [DecidableRel Adj]
    (hp : 2 ^ 24 ≤ p) (hp3 : p % 4 = 3)
    (hne : (Labellings.injLabellings (ZMod p) m.data.G).Nonempty)
    -- the character expansion: the data of X1's and `Extraction`'s theorems
    (h4 : Extraction.FourCycleBound p)
    {Δ' : ℕ} (hΔ' : ∀ i, ExtractionK.cmpDeg m.data.halfGraph m.data.sgn i ≤ Δ')
    (𝔓 : Finset (Finset (m.data.cut.Half × m.data.cut.Half) × Finset (m.data.cut.Half × m.data.cut.Half)))
    (h𝔓 : Extraction.IsExactPartition m.data.crossPairs 𝔓 (Extraction.nonstars m.data.crossPairs))
    (wit : Finset (m.data.cut.Half × m.data.cut.Half) × Finset (m.data.cut.Half × m.data.cut.Half) →
      Fin 2 → m.data.cut.Half × m.data.cut.Half)
    (cx cz : Finset (m.data.cut.Half × m.data.cut.Half) × Finset (m.data.cut.Half × m.data.cut.Half) →
      Finset m.data.cut.Half)
    (bucket : Finset (m.data.cut.Half × m.data.cut.Half) × Finset (m.data.cut.Half × m.data.cut.Half) → ℕ) (𝔮 : ℕ)
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
        ExtractionK.cmpLambda0 m.data.halfGraph m.data.sgn (Fintype.card (ZMod p)) (Fintype.card m.data.cut.Half)
          (TraceMixing.coarseErr p 4 12) 2 *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          (2 : ℝ) ^ Extraction.twoCycleCount (ExtractionK.witnessIdx c.1 (wit c)) *
            Real.sqrt (2 ^ ExtractionK.cmpEx m.data.halfGraph (m.data.crossPairs \ (c.1 ∪ c.2))
              (ExtractionK.witV (wit c)) (ExtractionK.witW (wit c)) (cx c) (cz c))) *
          Real.exp (ExtractionK.cmpGamma (Fintype.card (ZMod p)) (Fintype.card m.data.cut.Half) Δ' * (b * 2 ^ 𝔮))) ≤ Nns)
    (hDcol : Extraction.collisionD1 m.data.halfGraph m.data.sgn ord (Fintype.card (ZMod p))
        (Fintype.card m.data.cut.Half) +
      Extraction.collisionD2 m.data.halfGraph m.data.sgn πc (Fintype.card (ZMod p))
        (Fintype.card m.data.cut.Half) ≤ Dcol)
    (hεZc : 2 * Spectral.starZstar (SecondOrder.graphPinned
        (Labellings.weilBound_of_target hW p (mid_ne_two hp)) m.data.halfGraph (m.data.half_nonempty hne)
        (errors_of_S1 m.data (mid_card m) (mid_hdeg m) (mid_S1 hp)).2.2.1) m.data.Nset (Spectral.starCoef (p := p) m.data) + Nns + Dcol ≤
        εZ)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (m.data.Nset k).card *
          (1 + TraceMixing.coarseErr p (m.data.Nset k).card (Fintype.card m.data.cut.Half)) *
          devConst (Rprime p m.data 12 (restList m.data) k)
            (TraceMixing.coarseErr p (m.data.Nset k).card (Fintype.card m.data.cut.Half)) ^ 2 +
        (Fintype.card m.data.cut.Half : ℝ) * 4 ^ (m.data.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG m.data.Nset (sgnZ (p := p) m.data)
      (fun t => TraceMixing.coarseErr p t (Fintype.card m.data.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX m.data.Nset (sgnZ (p := p) m.data)
      (fun t => TraceMixing.coarseErr p t (Fintype.card m.data.cut.Half)) (Rprime p m.data 12 (restList m.data)) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ (lamMid m : ℝ) + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : m.data.cut.Half,
      m.data.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 12) ^ 2 *
        (2 ^ Labellings.nbrCount m.data.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount m.data.halfGraph (univ.erase j) j)
            (Fintype.card m.data.cut.Half))) - 1 ≤ θ ^ 2)
    -- the certified numbers of `lem:spec:degone`
    {ηQ εV : ℝ} (hηQ0 : 0 ≤ ηQ)
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) m.data k l = 0 then mXcut p m.data k l else 0) ≤ ρs)
    (hηQc : 2 / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card m.data.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mVcut p m.data k l) ≤ ρv)
    (hεVc : ((Fintype.card m.data.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) +
        (p : ℝ) / ((p : ℝ) - 1) * rp p * ρv ≤ εV) (hεV : 0 ≤ εV)
    -- WP-A's finite tests
    {cbar ηQbar ηBbar εVbar s g B : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p (mid_ne_two hp))
          m.data.halfGraph (m.data.half_nonempty hne)
          (errors_of_S1 m.data (mid_card m) (mid_hdeg m) (mid_S1 hp)).2.2.1) m.data.Nset (Spectral.starCoef (p := p) m.data) +
          Nns + Dcol) / (1 - εZ)) ^ 2 ≤ cbar * rp p)
    (hηQ : ηQ ≤ ηQbar)
    (hηB : etaBcx p (m.data.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 12) ^ 2 *
        (m.data.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 12))⁻¹)
        (lamMid m) εH θ 54 ΓE (lamMid m) 1
        ((PaleyB.ncSets Adj).card * Fintype.card m.data.cut.Half : ℝ) εV 2 ηQ ≤ ηBbar)
    (hεVb : εV ≤ εVbar) (hεV0 : 0 ≤ εVbar) (hεV1 : εVbar < 1) (hs : 0 < s)
    (hB : ((Spectral.starMstar (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p (mid_ne_two hp))
          m.data.halfGraph (m.data.half_nonempty hne)
          (errors_of_S1 m.data (mid_card m) (mid_hdeg m) (mid_S1 hp)).2.2.1) m.data.Nset (Spectral.starCoef (p := p) m.data) +
          Nns + Dcol) / (1 - εZ)) ^ 2 / (1 - g * rp p) ≤ B / p) :
    RouteAUpper (p := p) m.data Adj cbar s ηQbar ηBbar εVbar g B :=
  routeAUpper_of_full m.data hW hMR Adj (mid_ne_two hp) hp3 (mid_card m) hne (mid_hdeg m)
    (mid_S1 hp) (restList m.data) (restList_nodup _) (restList_cover _) (restList_disj _) h4 hΔ'
    𝔓 h𝔓 wit cx cz bucket 𝔮 hwit hcovX hbucket ord hord πc hπc hεZ hNns0 hNnsB hDcol hεZc hΓc hrow
    hrowX hεH hΛ0 hθ0 hθ (mid_rho m) (mid_lam m hp3) (by norm_num) hηQ0 (mid_deltaE m) hrowS hηQc
    hrowV hεVc hεV hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hs hB

end Sarkozy.MiddleCertificates
