module

public import Sarkozy.BlockInputs.FoldCaps
public import Sarkozy.SignedEstimates.G0

@[expose] public section

/-!
# The F21 density bound, proved (`lem:old-f-law`(a))

`paper/sections/21_middle_records.tex`, `lem:old-f-law`(a): the half marginal `m₀` of the fold
record `K₀` has density `g₀ = (p-2)(p-3-2e₀₁-2e₁₂)/((p-3)(p-4))` relative to `ν_F`, so
`‖g₀ - 1‖_∞ ≤ e₀ = 2q/((1-3q)(1-4q))`.

`FoldCaps.lean` asked for this bound as the per-prime input `FoldDensity e p`. It is proved here
from E1's exact formula (`SignedEstimates.g0_bound`), through a chart between the half of the cut
F21 and B8's half coordinates `Fin 3 → 𝔽_p`:

* `foldChart`: `o ↦ (o, 0)`; `foldHalf_mem_iff`: a half labelling is in `Inj(G⁺)` iff its chart
  image is in `H_F`; `card_foldHalf`: `|Inj(G⁺)| = |H_F|`;
* `halfLaw_mul_actDens`: `μ(x) g(x) = m₀(x ∘ chart)` (`lem:spec:cutkernel`(b));
* **`foldDensity_e0`**: `FoldDensity (e₀(p)) p` at every prime `p ≡ 3 (4)`, `p ≥ 19`;
  `e0_anti`: `e₀` decreases, so `FoldDensity (e₀(X)) p` for `p ≥ X ≥ 19`;
* `MiddleFoldCut i` (`MiddleFoldCert` without the density input, at `e = e₀(X_i)`, the paper's
  `e_X`) and **`middleFoldCert_of_cut`**.
-/

open Finset

namespace Sarkozy.BlockInputs

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.Cuts Sarkozy.BlockSpecPaper
  Sarkozy.BlockSpecPaper.AllpData Sarkozy.BlockAdapter Sarkozy.SignedComponents
  Sarkozy.SignedEstimates

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The chart `o ↦ (o, 0)` of the plus half of F21. -/
def foldChart (o : Fin 3) : foldLayer.cut.Half := ⟨(o, 0), (mem_layerHalf (Fin 3) _).mpr rfl⟩

theorem foldChart_surj (h : foldLayer.cut.Half) : foldChart h.1.1 = h := by
  apply Subtype.ext
  exact Prod.ext rfl ((mem_layerHalf (Fin 3) _).mp h.2).symm

theorem foldChart_injective : Function.Injective foldChart := fun _ _ h =>
  (Prod.mk.inj (congrArg Subtype.val h)).1

/-- **A half labelling of F21 is feasible iff its chart image is in `H_F`.** -/
theorem foldHalf_mem_iff (x : foldLayer.cut.Half → F) :
    x ∈ injLabellings F foldLayer.halfGraph ↔ HF (x ∘ foldChart) := by
  rw [mem_injLabellings_iff_feasible]
  have hE : ∀ a b : foldLayer.cut.Half, (a, b) ∈ foldLayer.halfGraph.E ↔
      a.1.1 = 0 ∧ b.1.1 = 2 := fun a b => by
    rw [SpecData.mem_halfGraph]
    exact mem_foldGraph (Fin 2) _
  constructor
  · rintro ⟨hinj, hedge⟩
    refine ⟨fun o o' h => foldChart_injective (hinj _ (mem_univ _) _ (mem_univ _) h), ?_⟩
    exact hedge (foldChart 0, foldChart 2) ((hE _ _).mpr ⟨rfl, rfl⟩) (mem_univ _) (mem_univ _)
  · rintro ⟨hinj, hchi⟩
    refine ⟨fun a _ b _ hab => ?_, fun e he _ _ => ?_⟩
    · rw [← foldChart_surj a, ← foldChart_surj b] at hab ⊢
      exact congrArg foldChart (hinj hab)
    · obtain ⟨a, b⟩ := e
      obtain ⟨ha, hb⟩ := (hE a b).mp he
      rw [← foldChart_surj a, ← foldChart_surj b, ha, hb]
      exact hchi

/-- `|Inj(G⁺)| = |H_F|`. -/
theorem card_foldHalf :
    ((injLabellings F foldLayer.halfGraph).card : ℝ) = Hcard (F := F) := by
  unfold Hcard Hset
  congr 1
  refine Finset.card_bij (fun x _ => x ∘ foldChart) (fun x hx => ?_) (fun x _ y _ hxy => ?_)
    (fun x' hx' => ?_)
  · exact mem_filter.mpr ⟨mem_univ _, (foldHalf_mem_iff x).mp hx⟩
  · funext h
    rw [← foldChart_surj h]
    exact congrFun hxy h.1.1
  · refine ⟨fun h => x' h.1.1, (foldHalf_mem_iff _).mpr ?_, ?_⟩
    · exact (mem_filter.mp hx').2
    · rfl

/-- **`μ(x) g(x) = m₀(x ∘ chart)`**: the half marginal of the cut kernel is B8's `m₀`. -/
theorem halfLaw_mul_actDens (hne : (injLabellings F (foldGraph (Fin 2))).Nonempty)
    (x : foldLayer.cut.Half → F) :
    (foldLayer.halfLaw hne).weight x * actDens foldLayer hne x =
      (m0 hne).weight (x ∘ foldChart) := by
  have h := foldLayer.expect_halfL hne (fun z => if z = x then (1 : ℝ) else 0)
  have hiff : ∀ y : Fin 3 × Fin 2 → F, foldLayer.halfL y = x ↔ lay y 0 = x ∘ foldChart := by
    intro y
    constructor
    · intro hy
      funext o
      rw [← hy]
      rfl
    · intro hy
      funext h
      rw [← foldChart_surj h]
      exact congrFun hy h.1.1
  have hL : (graphLaw foldLayer.G hne).expect
      (fun y => if foldLayer.halfL y = x then (1 : ℝ) else 0) =
        (m0 hne).weight (x ∘ foldChart) := by
    change ∑ y, (graphLaw (foldGraph (Fin 2)) hne).weight y *
        (if foldLayer.halfL y = x then (1 : ℝ) else 0) =
      ∑ y, if lay y 0 = x ∘ foldChart then (graphLaw (foldGraph (Fin 2)) hne).weight y else 0
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : foldLayer.halfL y = x
    · have hy' := (hiff y).mp hy
      simp only [hy, hy', ↓reduceIte, mul_one]
    · have hy' : ¬ lay y 0 = x ∘ foldChart := fun h' => hy ((hiff y).mpr h')
      simp only [hy, hy', ↓reduceIte, mul_zero]
  have hR : (foldLayer.halfLaw hne).expect (fun z => (if z = x then (1 : ℝ) else 0) *
      rowFun (foldLayer.halfLaw hne) (fun z z' => foldLayer.cutK z z' / foldLayer.cutZ hne) z) =
      (foldLayer.halfLaw hne).weight x * actDens foldLayer hne x := by
    unfold FiniteLaw.expect
    rw [Finset.sum_eq_single x]
    · simp only [↓reduceIte, one_mul]
      rfl
    · intro z _ hz
      simp only [hz, ↓reduceIte, zero_mul, mul_zero]
    · intro hx
      exact absurd (mem_univ x) hx
  rw [← hR, ← h, hL]

/-- **`FoldDensity (e₀(p)) p`** at every prime `p ≡ 3 (mod 4)`, `p ≥ 19` (`lem:old-f-law`(a),
via E1's `g0_bound`). -/
theorem foldDensity_e0 (p : ℕ) [Fact p.Prime] (h3 : p % 4 = 3) (h19 : 19 ≤ p) :
    FoldDensity (e0 p) p := by
  intro hne x hx
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hR : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have h3' : Fintype.card (ZMod p) % 4 = 3 := by rw [hcard]; exact h3
  have h19' : 19 ≤ Fintype.card (ZMod p) := by rw [hcard]; exact h19
  have hmem : x ∈ injLabellings (ZMod p) foldLayer.halfGraph := by
    by_contra hn
    apply hx
    change (if x ∈ injLabellings (ZMod p) foldLayer.halfGraph then _ else 0) = 0
    simp only [hn, ↓reduceIte]
  have hHF : HF (x ∘ foldChart) := (foldHalf_mem_iff x).mp hmem
  have hw : (foldLayer.halfLaw hne).weight x = 1 / Hcard (F := ZMod p) := by
    change (if x ∈ injLabellings (ZMod p) foldLayer.halfGraph then
      1 / ((injLabellings (ZMod p) foldLayer.halfGraph).card : ℝ) else 0) = _
    simp only [hmem, ↓reduceIte]
    rw [card_foldHalf]
  have hH : 0 < Hcard (F := ZMod p) := SignedComponents.Hcard_pos hne
  have hg := g0_bound hR h3' h19' hne hHF
  have hg' : g0 hne (x ∘ foldChart) ≤ 1 + e0 (Fintype.card (ZMod p)) := by
    have := (abs_le.mp hg).2
    linarith
  rw [hcard] at hg'
  have hmul := halfLaw_mul_actDens hne x
  rw [hw] at hmul
  have hact : actDens foldLayer hne x = g0 hne (x ∘ foldChart) := by
    unfold g0
    rw [← hmul]
    field_simp
  rw [hact]
  exact_mod_cast hg'

/-- `e₀` decreases: `e₀(p) ≤ e₀(X)` for `19 ≤ X ≤ p`. -/
theorem e0_anti {X p : ℝ} (hX : 19 ≤ X) (hXp : X ≤ p) : e0 p ≤ e0 X := by
  unfold e0
  have h1 : 0 < (X - 3) * (X - 4) := by nlinarith
  have h2 : 0 < (p - 3) * (p - 4) := by nlinarith
  rw [div_le_div_iff₀ h2 h1]
  nlinarith [mul_nonneg (sub_nonneg.mpr hXp) (by nlinarith : (0 : ℝ) ≤ p * X - 12)]

theorem FoldDensity.mono {e e' : ℝ} {p : ℕ} [Fact p.Prime] (h : FoldDensity e p) (he : e ≤ e') :
    FoldDensity e' p := fun hne x hx => (h hne x hx).trans (by linarith)

/-- **The F21 certificate of piece `i` without the density input**: constants `g` (the paper's
`1 + (e_o(X) - 1) r_X`) and `n` (`n_X`) with `n e₀(X_i) < 1`, `570 < (n + 1) log X_i`,
`g X_i^{-1/2} < 1`, `g/(1 - n e₀(X_i)) ≤ k_D(i)`, and the per-prime lower bound `FoldCutCap g p`
at every class-three prime of the piece. *Hypothesis* (per prime). -/
def MiddleFoldCut (i : Fin 33) : Prop :=
  ∃ (g : ℝ) (n : ℕ), 0 ≤ g ∧ (n : ℝ) * e0 (pieceStart i) < 1 ∧
    570 < ((n : ℝ) + 1) * Real.log (pieceStart i) ∧ g * (√(pieceStart i : ℝ))⁻¹ < 1 ∧
    g / (1 - n * e0 (pieceStart i)) ≤ (allpInputs i).k .D ∧
    ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i → FoldCutCap g p

/-- **`MiddleFoldCert i` from `MiddleFoldCut i`**: the density input is `foldDensity_e0`. -/
theorem middleFoldCert_of_cut {i : Fin 33} (h : MiddleFoldCut i) : MiddleFoldCert i := by
  obtain ⟨g, n, hg, hne1, hn, hgX, hkD, hp⟩ := h
  have hX36 := pieceStart_gt_36 i
  have he0 : 0 ≤ e0 (pieceStart i : ℝ) := by
    unfold e0
    have : 0 < ((pieceStart i : ℝ) - 3) * ((pieceStart i : ℝ) - 4) := by nlinarith
    positivity
  refine ⟨g, e0 (pieceStart i), n, hg, he0, hne1, hn, hgX, hkD,
    fun p _ h3 hp1 hp2 => ⟨hp p h3 hp1 hp2, ?_⟩⟩
  have hp1' : (pieceStart i : ℝ) ≤ p := by exact_mod_cast hp1
  have h19 : 19 ≤ p := by
    have : (19 : ℝ) ≤ p := by linarith
    exact_mod_cast this
  exact (foldDensity_e0 p h3 h19).mono (e0_anti (by linarith) hp1')

end Sarkozy.BlockInputs
