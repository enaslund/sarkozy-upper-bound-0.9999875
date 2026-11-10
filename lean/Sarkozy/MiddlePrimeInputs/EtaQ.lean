module

public import Sarkozy.MiddlePrimeInputs.EpsV
public import Sarkozy.MiddlePrimeInputs.NormSharp

/-!
# The input `η_Q` of route A for L10 and L21 at every middle prime

`paper/sections/14_spectral.tex`, `lem:spec:degone`(b) and `thm:spectral-criterion`; the bar
`η̄_Q` of `cert:layer12-grid` (`paper/sections/20_middle_reference.tex`), with
`lem:spectral-monotone` for the transfer from the piece start `X` to every `p ≥ X`.

The inputs `hDE`, `hrowS`, `hηQc`, `hηQ` of `spectral_criterion_cut_fullRplus` (and of
`spectral_criterion_cut_full`) ask for `Λ_D ≥ ‖Δ^E‖`, a row bound `ρ_s` of the small-pair matrix
`mXcut` on the pairs with `ς_{kl} = 0`, and
`η_Q = Λ_D/(p - 1) + p/(p - 1)·ρ_s + n/((p - 1) r) ≤ η̄_Q`.

* `Λ_D = √2` (L10), `√3` (L21): `deltaE_sharp` (class three). With C8's `Λ_D = 2`
  (`routeALower_mid`) the inequality fails at the recorded bars.
* All vertices of `G_L` have degree `d = 2` (L10, `|W| = 6`) or `4` (L21, `|W| = 12`), so every
  `δ^×_k = δ_d(p, |W|)`, and the rows of `ς` have `2, 1, 2` (L10) and `4` (L21) zeros:
  `ρ_s(p) = S·δ_d(p, |W|)` with `S = 2, 4` (`rowS_le`). This is the evaluator's `nDsmall`.
* **`etaQ_input`**: at every prime `p ≥ X_i`, `p ≡ 3 (mod 4)`, the four inputs for the 33 pieces
  and both cuts, with `η_Q = η̄_Q`.

The smallest relative margin is `2.9·10⁻¹¹` (L21), the rounding of the bars.
-/

@[expose] public section

namespace Sarkozy.MiddlePrimeInputs

open Finset Sarkozy.PartV Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.SpectralD.Cx
  Sarkozy.MiddleCertificates MiddleCertificates.MidCut

/-- `|W|`: `6` (L10), `12` (L21). -/
def vW : MidCut → ℕ
  | .l10 => 6
  | .l21 => 12

/-- The degree of every vertex of `G_L`: `2` (L10), `4` (L21). -/
def vDX : MidCut → ℕ
  | .l10 => 2
  | .l21 => 4

/-- The largest number of zeros in a row of `ς`: `2` (L10), `4` (L21). -/
def vS : MidCut → ℕ
  | .l10 => 2
  | .l21 => 4

theorem card_vertex (c : MidCut) : Fintype.card c.Vertex = vW c := by
  cases c <;> simp [MidCut.Vertex, vW, Fintype.card_prod, ZMod.card]

/-- The degree in `G_L`, as a Boolean count. -/
noncomputable def gDeg (c : MidCut) (w : c.Vertex) : ℕ :=
  ((univ.erase w).filter (fun u => (c.edge u w || c.edge w u) = true)).card

theorem nbrCount_G (c : MidCut) (w : c.Vertex) :
    Labellings.nbrCount c.data.G (univ.erase w) w = gDeg c w := by
  unfold Labellings.nbrCount gDeg
  congr 1
  refine Finset.filter_congr fun u _ => ?_
  rw [mem_edge, mem_edge]
  simp

theorem gDeg_eq (c : MidCut) : ∀ w : c.Vertex, gDeg c w = vDX c := by
  cases c <;> decide

/-- **The exact maximal degree of `G_L`**: `Δ = 2` (L10), `4` (L21), the input `hdeg` of the
chain. With `Δ = 2` for L10 (and `n = 6`) the count error `ê = e_Δ(p, n)` in `N_ns` is about
`r` instead of `17r` for C8's `Δ = 4`, `n = 12`. -/
theorem hdeg_exact (c : MidCut) :
    ∀ v, (univ.filter (fun w => (v, w) ∈ c.data.G.E ∨ (w, v) ∈ c.data.G.E)).card ≤ vDX c := by
  intro v
  have h := gDeg_eq c v
  rw [← nbrCount_G] at h
  unfold Labellings.nbrCount at h
  rw [← h]
  apply le_of_eq
  congr 1
  ext w
  simp only [mem_filter, mem_univ, true_and, mem_erase, ne_eq, and_true]
  constructor
  · intro hw
    refine ⟨fun h' => ?_, Or.comm.mp hw⟩
    subst h'
    exact hw.elim (c.data.G.loopless _) (c.data.G.loopless _)
  · intro hw
    exact Or.comm.mp hw.2

/-- The zeros of `sgnZ` are the zeros of `ς`. -/
theorem sgnZ_eq_zero_iff (c : MidCut) {p : ℕ} [Fact p.Prime] (k l : c.data.cut.Half) :
    Cx.sgnZ (p := p) c.data k l = 0 ↔ sgnInt c k l = 0 := by
  unfold Cx.sgnZ
  rw [SpectralD.sgn_eq_edgeSign c.data c.edge (mem_edge c)]
  change ((sgnInt c k l : ℤ) : ZMod p) = 0 ↔ _
  unfold sgnInt edgeSign
  split_ifs <;> simp

/-- The number of zeros of row `k` of `ς`. -/
noncomputable def rowZ (c : MidCut) (k : c.data.cut.Half) : ℕ :=
  (univ.filter (fun l => sgnInt c k l = 0)).card

theorem rowZ_le (c : MidCut) : ∀ k : c.data.cut.Half, rowZ c k ≤ vS c := by
  cases c
  all_goals
    unfold rowZ sgnInt
    decide

/-- `ρ_s(p) = S·δ_d(p, |W|)`. -/
noncomputable def rhoS (c : MidCut) (p : ℕ) : ℝ := vS c * smallConst p (vDX c) (vW c)

/-- **The rows of `mXcut` on the zeros of `ς`** are at most `ρ_s(p)`, when `δ_d(p, |W|) ≥ 0`. -/
theorem rowS_le (c : MidCut) {p : ℕ} [Fact p.Prime] (h0 : 0 ≤ smallConst p (vDX c) (vW c))
    (k : c.data.cut.Half) :
    ∑ l, (if Cx.sgnZ (p := p) c.data k l = 0 then mXcut p c.data k l else 0) ≤ rhoS c p := by
  have hx : ∀ k' : c.data.cut.Half, deltaXConst p c.data k' = smallConst p (vDX c) (vW c) := by
    intro k'
    unfold deltaXConst
    rw [nbrCount_G c (c.data.cut.flip k'.1), gDeg_eq, show Fintype.card c.Vertex = vW c from
      card_vertex c]
  have ht : ∀ l, (if Cx.sgnZ (p := p) c.data k l = 0 then mXcut p c.data k l else 0) =
      (if sgnInt c k l = 0 then (1 : ℝ) else 0) * smallConst p (vDX c) (vW c) := by
    intro l
    by_cases hz : Cx.sgnZ (p := p) c.data k l = 0
    · have hz' := (sgnZ_eq_zero_iff c k l).mp hz
      unfold mXcut
      simp only [hz, hz', ↓reduceIte, hx, min_self, one_mul]
    · have hz' : ¬ sgnInt c k l = 0 := fun h => hz ((sgnZ_eq_zero_iff c k l).mpr h)
      simp only [hz, hz', ↓reduceIte, zero_mul]
  rw [sum_congr rfl fun l _ => ht l, ← sum_mul, sum_boole]
  unfold rhoS
  have : ((rowZ c k : ℕ) : ℝ) ≤ vS c := by exact_mod_cast rowZ_le c k
  change ((rowZ c k : ℕ) : ℝ) * _ ≤ _
  exact mul_le_mul_of_nonneg_right this h0

/-- A rational upper bound of `√λ_D`. -/
def lamDUp : MidCut → ℚ
  | .l10 => 14142135623730950488017 / 10000000000000000000000
  | .l21 => 17320508075688772935275 / 10000000000000000000000

theorem lamDUp_ok (c : MidCut) : 0 ≤ lamDUp c ∧ (lamD2 c : ℚ) ≤ lamDUp c ^ 2 := by
  cases c <;> norm_num [lamDUp, lamD2]

theorem sqrt_lamD_le (c : MidCut) : Real.sqrt (lamD2 c) ≤ (lamDUp c : ℝ) := by
  obtain ⟨h0, h2⟩ := lamDUp_ok c
  have h0' : (0 : ℝ) ≤ lamDUp c := by exact_mod_cast h0
  have h2' : ((lamD2 c : ℕ) : ℝ) ≤ (lamDUp c : ℝ) ^ 2 := by exact_mod_cast h2
  calc Real.sqrt (lamD2 c) ≤ Real.sqrt ((lamDUp c : ℝ) ^ 2) := Real.sqrt_le_sqrt h2'
    _ = lamDUp c := Real.sqrt_sq h0'

/-- `η_Q` at the piece start over `ℚ`, with `r_i ≥ X_i^{-1/2}`. -/
def etaQQ (c : MidCut) (i : Fin 33) : ℚ :=
  lamDUp c / ((pieceStart i : ℚ) - 1) +
    (pieceStart i : ℚ) / ((pieceStart i : ℚ) - 1) *
      (vS c * scQ (vDX c) (vW c) (pieceStart i) (rUp i)) +
      vN c * ((pieceStart i : ℚ) / ((pieceStart i : ℚ) - 1) * rUp i)

/-- **The kernel checks at the 33 piece starts**: `e_d(X_i, |W|) < 1` and
`η_Q(X_i) ≤ η̄_Q(X_i)` over `ℚ`. -/
theorem etaQ_checks (c : MidCut) : ∀ i : Fin 33,
    eQ (vDX c) (vW c) (pieceStart i) (rUp i) < 1 ∧ etaQQ c i ≤ etaQ c i := by
  cases c
  all_goals
    unfold etaQQ scQ eQ rUp rUpList pieceStart pieceEnds etaQ etaQList vN vS vDX vW lamDUp
    unfold Sarkozy.MiddleCertificates.l10EtaQ Sarkozy.MiddleCertificates.l21EtaQ
    decide +kernel

/-- **The input `η_Q` of route A at every prime `p ≥ X_i`, `p ≡ 3 (mod 4)`**
(`lem:spec:degone`(b), `lem:spectral-monotone`, the bar `η̄_Q` of `cert:layer12-grid`):
`‖Δ^E‖ ≤ Λ_D = √λ_D`, the rows of `mXcut` on the zeros of `ς` are at most `ρ_s(p)`, and
`Λ_D/(p - 1) + p/(p - 1)·ρ_s(p) + n/((p - 1) r) ≤ η̄_Q(X_i)`. These are the inputs `hΛD`, `hDE`,
`hrowS`, `hηQc` (with `η_Q = η̄_Q`) and `hηQ` (`le_rfl`) of `spectral_criterion_cut_fullRplus`. -/
theorem etaQ_input (c : MidCut) (i : Fin 33) {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3)
    (hX : pieceStart i ≤ p) :
    0 ≤ Real.sqrt (lamD2 c) ∧ NormLe (deltaE (Cx.sgnZ (p := p) c.data)) (Real.sqrt (lamD2 c)) ∧
      (∀ k, ∑ l, (if Cx.sgnZ (p := p) c.data k l = 0 then mXcut p c.data k l else 0) ≤
        rhoS c p) ∧
      Real.sqrt (lamD2 c) / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * rhoS c p +
        (Fintype.card c.data.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ (etaQ c i : ℝ) := by
  obtain ⟨he, hQ⟩ := etaQ_checks c i
  obtain ⟨hr0, hr⟩ := rUp_ok i
  set X := pieceStart i with hXdef
  have hX24 : 2 ^ 24 ≤ X := pieceStart_ge i
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX24
  have hp0 : 0 < p := lt_of_lt_of_le hX0 hX
  have hX1 : (1 : ℝ) < X := by
    have : (2 : ℝ) ^ 24 ≤ X := by exact_mod_cast hX24
    linarith [show (1 : ℝ) < 2 ^ 24 by norm_num]
  have hXp : (X : ℝ) ≤ p := by exact_mod_cast hX
  have hp1 : (1 : ℝ) < p := lt_of_lt_of_le hX1 hXp
  have hrr := inv_sqrt_le_of_sq hr0 hr
  have heX : TraceMixing.coarseErr X (vDX c) (vW c) < 1 :=
    lt_of_le_of_lt (coarseErr_le_eQ hrr _ _) (by exact_mod_cast he)
  have hep : TraceMixing.coarseErr p (vDX c) (vW c) < 1 :=
    lt_of_le_of_lt (SpectralD.Root.coarseErr_antitone (by exact_mod_cast hX0) hXp _ _) heX
  have hscX := smallConst_le_scQ hX0 hrr (vDX c) (vW c) he
  have hscp := smallConst_anti hX0 hX (vDX c) (vW c) heX
  have hsc0 := smallConst_nonneg' hp0 (vDX c) (vW c) hep
  refine ⟨Real.sqrt_nonneg _, deltaE_sharp c hp3, rowS_le c hsc0, ?_⟩
  rw [card_half]
  -- the three terms
  have hfac := sqrtFactor_anti hX1 hXp
  have hfacX : (X : ℝ) / ((X : ℝ) - 1) * (Real.sqrt X)⁻¹ ≤ (X : ℝ) / ((X : ℝ) - 1) * (rUp i : ℝ) :=
    mul_le_mul_of_nonneg_left hrr (div_nonneg (by linarith) (by linarith))
  have h1 : Real.sqrt (lamD2 c) / ((p : ℝ) - 1) ≤ (lamDUp c : ℝ) / ((X : ℝ) - 1) :=
    div_le_div₀ (by exact_mod_cast (lamDUp_ok c).1) (sqrt_lamD_le c) (by linarith) (by linarith)
  have hpp : (p : ℝ) / ((p : ℝ) - 1) ≤ (X : ℝ) / ((X : ℝ) - 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h2 : (p : ℝ) / ((p : ℝ) - 1) * rhoS c p ≤
      (X : ℝ) / ((X : ℝ) - 1) * (vS c * (scQ (vDX c) (vW c) X (rUp i) : ℝ)) := by
    unfold rhoS
    refine mul_le_mul hpp (mul_le_mul_of_nonneg_left (hscp.trans hscX) (Nat.cast_nonneg _))
      (by positivity) (div_nonneg (by linarith) (by linarith))
  have h3 : (vN c : ℝ) / (((p : ℝ) - 1) * rp p) ≤
      (vN c : ℝ) * ((X : ℝ) / ((X : ℝ) - 1) * (rUp i : ℝ)) := by
    have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
    have hss : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (by linarith)
    have e : (vN c : ℝ) / (((p : ℝ) - 1) * rp p) =
        (vN c : ℝ) * ((p : ℝ) / ((p : ℝ) - 1) * (Real.sqrt p)⁻¹) := by
      unfold rp
      set s := Real.sqrt (p : ℝ) with hs
      have hp' : (p : ℝ) = s * s := hss.symm
      have hp1' : s * s - 1 ≠ 0 := by rw [← hp']; linarith
      rw [hp']
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (hfac.trans hfacX) (Nat.cast_nonneg _)
  have hQ' : (etaQQ c i : ℝ) ≤ (etaQ c i : ℝ) := by exact_mod_cast hQ
  have hcast : (etaQQ c i : ℝ) = (lamDUp c : ℝ) / ((X : ℝ) - 1) +
      (X : ℝ) / ((X : ℝ) - 1) * (vS c * (scQ (vDX c) (vW c) X (rUp i) : ℝ)) +
        (vN c : ℝ) * ((X : ℝ) / ((X : ℝ) - 1) * (rUp i : ℝ)) := by
    unfold etaQQ
    push_cast
    ring
  linarith

end Sarkozy.MiddlePrimeInputs
