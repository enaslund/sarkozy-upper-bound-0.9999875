module

public import Sarkozy.CancellationSteps.L2
public import Sarkozy.DensityDC.LiftMoments





@[expose] public section

namespace Sarkozy.CancellationSteps

open Finset
open scoped BigOperators
open Sarkozy.Cancellation Sarkozy.Mixing Sarkozy.PaperFrame Sarkozy.FourierArithmetic
  Sarkozy.Functional

/-- `Q^{20} = N` for the cutoff `Q = N^{1/20}`. -/
lemma paperCutoff_pow_twenty (N : ℕ) : paperCutoff N ^ 20 = (N : ℝ) := by
  unfold paperCutoff liftExponent
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  norm_num

/-- For `N = K L` with `L ≥ 2^{20} K`: `2⌊Q⌋ ≤ L + 1` and `⌊Q⌋^5 ≤ L + 1`, `Q = N^{1/20}`. -/
lemma floor_cutoff_bounds {K L : ℕ} (hK : 1 ≤ K) (hL : 2 ^ 20 * K ≤ L) :
    2 * ⌊paperCutoff (K * L)⌋₊ ≤ L + 1 ∧ ⌊paperCutoff (K * L)⌋₊ ^ 5 ≤ L + 1 := by
  set Q := paperCutoff (K * L) with hQdef
  have hQ0 : 0 ≤ Q := by rw [hQdef]; unfold paperCutoff; positivity
  have hfl : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le hQ0
  have h20 : (⌊Q⌋₊ : ℝ) ^ 20 ≤ ((K * L : ℕ) : ℝ) :=
    calc (⌊Q⌋₊ : ℝ) ^ 20 ≤ Q ^ 20 := pow_le_pow_left₀ (Nat.cast_nonneg _) hfl 20
      _ = ((K * L : ℕ) : ℝ) := paperCutoff_pow_twenty (K * L)
  have h20n : ⌊Q⌋₊ ^ 20 ≤ K * L := by exact_mod_cast h20
  have hKL : K ≤ L := le_trans (by omega) hL
  have hKLL : K * L ≤ L * L := Nat.mul_le_mul_right L hKL
  have hLL : ∀ n, 2 ≤ n → L * L ≤ (L + 1) ^ n := by
    intro n hn
    calc L * L ≤ (L + 1) ^ 2 := by nlinarith
      _ ≤ (L + 1) ^ n := Nat.pow_le_pow_right (by omega) hn
  constructor
  · have h1 : (2 * ⌊Q⌋₊) ^ 20 ≤ (L + 1) ^ 20 := by
      calc (2 * ⌊Q⌋₊) ^ 20 = 2 ^ 20 * ⌊Q⌋₊ ^ 20 := by ring
        _ ≤ 2 ^ 20 * (K * L) := Nat.mul_le_mul_left _ h20n
        _ = (2 ^ 20 * K) * L := by ring
        _ ≤ L * L := Nat.mul_le_mul_right _ hL
        _ ≤ (L + 1) ^ 20 := hLL 20 (by norm_num)
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
  · have h1 : (⌊Q⌋₊ ^ 5) ^ 4 ≤ (L + 1) ^ 4 := by
      calc (⌊Q⌋₊ ^ 5) ^ 4 = ⌊Q⌋₊ ^ 20 := by ring
        _ ≤ K * L := h20n
        _ ≤ L * L := hKLL
        _ ≤ (L + 1) ^ 4 := hLL 4 (by norm_num)
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1

/-- **The fourth moments of the query inputs** (`lem:record:lift-moments`(c), `r = 2`): given the
moment bound of `DensityDC.moment_input_le` (`r = 2`, `ε = 1440 δ`) with constant `C`, for
`N = K L`, `L ≥ 2^{20} K`, every interval `I_b` and residue `s` modulo `D₀`:
`E_{G_N} |g^{I_b, D₀, s}|⁴ ≤ (D₀⁴ |X₀|⁴ C K) N^{72δ} α`. -/
theorem indexedInput_fourth_moment {J₀ J : Type} [Fintype J₀] [DecidableEq J₀] [Fintype J]
    [DecidableEq J] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (q : J → ℕ) [∀ j, NeZero (q j)] (C : ℝ)
    (hmom : ∀ (Q : ℝ), 1 ≤ Q → ∀ (c : ℤ) (M : ℕ), 0 < M → 2 * ⌊Q⌋₊ ≤ M + 1 →
      ⌊Q⌋₊ ^ 5 ≤ M + 1 → ∀ {D0 : ℕ} (s : ZMod D0) (A : Finset ℤ),
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ q))).moment ((2 * 2 : ℕ) : ℝ)
          (fun x => (input (joinModuli m₀ q) Q (Icc (c + 1) (c + M)) D0 s A x).re) ≤
        (D0 : ℝ) ^ (2 * 2) * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * 2) * C *
          Q ^ (1440 * stageDelta) *
          ((((Icc 1 (M : ℤ)).filter fun x => ((x + c : ℤ) : ZMod D0) = s ∧ x + c ∈ A).card : ℝ) /
            M)))
    (hC : 0 < C) {K L : ℕ} [NeZero K] (hK : 1 ≤ K) (hL : 2 ^ 20 * K ≤ L) {D0 : ℕ}
    (A : Finset ℤ) (b : ZMod K) (s : ZMod D0) :
    (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ q))).expect (fun z =>
        |indexedInput (joinModuli m₀ q) (paperCutoff (K * L)) K L D0 A (b, s) z| ^ 4) ≤
      ((D0 : ℝ) ^ 4 * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ 4 * C) * K) *
        ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) * density (K * L) A := by
  have hL1 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hKL : 1 ≤ K * L := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set c : ℤ := ((leastPosRep b : ℤ) - 1) * L with hc
  have hI : blockInterval K L b = Icc (c + 1) (c + L) := by
    unfold blockInterval
    rw [Ioc_eq_Icc_int]
    congr 1
    rw [hc]
    ring
  obtain ⟨hf1, hf2⟩ := floor_cutoff_bounds hK hL
  have hm := hmom (paperCutoff (K * L)) (one_le_paperCutoff hKL) c L hL1 hf1 hf2 s A
  have hexp : (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ q))).expect (fun z =>
      |indexedInput (joinModuli m₀ q) (paperCutoff (K * L)) K L D0 A (b, s) z| ^ 4) =
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ q))).moment ((2 * 2 : ℕ) : ℝ)
        (fun x => (input (joinModuli m₀ q) (paperCutoff (K * L)) (Icc (c + 1) (c + L)) D0 s A
          x).re) := by
    unfold FiniteLaw.moment indexedInput
    rw [← hI]
    congr 1
    funext z
    rw [show ((2 * 2 : ℕ) : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hexp]
  refine hm.trans ?_
  -- `Q^ε = N^{72δ}`
  have hQε : paperCutoff (K * L) ^ (1440 * stageDelta) = ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) := by
    unfold paperCutoff liftExponent
    rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  rw [hQε]
  -- `|B| / L ≤ K α`
  set B := (Icc 1 (L : ℤ)).filter fun x => ((x + c : ℤ) : ZMod D0) = s ∧ x + c ∈ A with hB
  have hBA : B.card ≤ A.card := by
    refine card_le_card_of_injOn (fun x => x + c) (fun x hx => ?_) (fun x _ y _ h => by
      simpa using h)
    exact ((mem_filter.mp hx).2).2
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL1
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hBL : (B.card : ℝ) / L ≤ K * density (K * L) A := by
    unfold density
    rw [Nat.cast_mul, div_le_iff₀ hLr]
    have : (B.card : ℝ) ≤ A.card := by exact_mod_cast hBA
    calc (B.card : ℝ) ≤ A.card := this
      _ = (K : ℝ) * ((A.card : ℝ) / ((K : ℝ) * L)) * L := by field_simp
  have hN0 : (0 : ℝ) ≤ ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) := by positivity
  have hX0 : (0 : ℝ) ≤ (Fintype.card (ResidueSpace m₀) : ℝ) ^ 4 := by positivity
  have hD0 : (0 : ℝ) ≤ (D0 : ℝ) ^ 4 := by positivity
  calc (D0 : ℝ) ^ (2 * 2) * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * 2) * C *
        ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) * ((B.card : ℝ) / L))
      = (D0 : ℝ) ^ 4 * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ 4 * C) *
          ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) * ((B.card : ℝ) / L) := by ring
    _ ≤ (D0 : ℝ) ^ 4 * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ 4 * C) *
          ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) * (K * density (K * L) A) :=
        mul_le_mul_of_nonneg_left hBL (by positivity)
    _ = ((D0 : ℝ) ^ 4 * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ 4 * C) * K) *
          ((K * L : ℕ) : ℝ) ^ (72 * stageDelta) * density (K * L) A := by ring

/-! ## `DensityCancellation` from Step 2 alone -/

section Final

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)] [∀ L j, Fact (p L j).Prime] {P : Type} [Fintype P] (pr h : P → ℕ)
  [∀ q, NeZero (pr q ^ h q)]

open Sarkozy.TheoremC Sarkozy.IndexSupport Sarkozy.Comparison in
/-- **`lem:record:density-can` (WP-FI's `DensityCancellation`) from Step 2 alone.** Hypotheses:
* elementary facts about the data: distinct tail primes, `P₅ ≥ 64`, `M₀` coprime to every atom
  modulus, the atom moduli pairwise coprime, the prefix moduli prime powers `pp_i^{ep_i}`, and the
  coverage of the primes up to `N^{1/40}` (`hcover`);
* Step 2 of the lemma: `LiftMoments` at the encoded data of every query at every scale
  `L ≥ L₁`, with a constant `C₂` fixed in advance (the moment bounds of the other factors `W`
  and of the pair factor `φ = F₁ F₂`, which the paper derives from `lem:record:lift-moments`(c)
  by Hölder's inequality).

Proved: Step 1 (WP-K) and all of Step 3: the intervals, the fibre formulas, the size of `D`,
`H D_E ≤ Q`, the coprimality and coverage conditions, the square class of `𝔞₂ − 𝔞₁` (from the
acceptance (b)), the uniformity of `𝔞₁` and the `L²` bound, the latter from the fourth moments of
the query inputs (`indexedInput_fourth_moment`, from `DensityDC.moment_input_le`). -/
theorem densityCancellation_of_step2 (P5 : ℕ) (pp ep : J₀ → ℕ)
    (hinj : ∀ L, Function.Injective (p L)) (h64 : 64 ≤ P5) {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (L₁ : ℕ)
    (hcop0 : ∀ L (c : J₀ ⊕ J L), Nat.Coprime (modulus pr h) (joinModuli m₀ (p L) c))
    (hcopE : ∀ L, ∀ i j : J₀ ⊕ J L, i ≠ j →
      Nat.Coprime (joinModuli m₀ (p L) i) (joinModuli m₀ (p L) j))
    (hpre : ∀ i, (pp i).Prime ∧ 1 ≤ ep i ∧ m₀ i = pp i ^ ep i)
    (hcover : ∀ L : ℕ, ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ (1 / 40 : ℝ) →
      ℓ ∣ modulus pr h ∨ (∃ i, ℓ ∣ m₀ i) ∨ ∃ j, p L j = ℓ)
    (hSteps : ∀ L : ℕ, L₁ ≤ L → ∀ A : Finset ℤ, Admissible (blockScale * L) A →
      ∀ ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b),
      (∀ b, HasUniformMarginals (ϱ b)) → ∀ (u v : Slot) (huv : u ≠ v),
      ∀ ha : (∀ j : J L, P5 ≤ p L j → PairUniformOmega (q := p L j) (ϱ (some j)) u v ∧
        Sarkozy.Mixing.IsGammaMixing (p L j) Sarkozy.AnalyticStage.γ (ϱ (some j)) {u, v}),
      (∀ b : PaperAtom J L, (∀ j, b = some j → p L j < P5) → ∀ z, (ϱ b).weight z ≠ 0 →
        AcceptedPair m₀ p pp ep L b (z u) (z v)) →
      ∀ (bI : ZMod blockScale) (s r : ZMod (modulus pr h)), bI ≠ 0 →
      IsNonvanishingSquareClass (modulus pr h) r →
      ∀ G : Slot → (∀ b, AtomLabel m₀ p L b) → ℝ,
      G u = indexInputAt m₀ p pr h L A (bI, s) →
      G v = indexInputAt m₀ p pr h L A (bI + 1, s + r) →
      (∀ w, w ≠ u → w ≠ v → IsQueryInput m₀ p pr h L A (G w)) →
        LiftMoments (tailQ p L P5)
          (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1))
          (encKappa m₀ p L P5 ϱ huv (fun k => (ha k.1 k.2).1)) (encF m₀ p L P5 G u)
          (encF m₀ p L P5 G v) (encW m₀ p L P5 G u v) (blockScale * L) C₂
          (density (blockScale * L) A)) :
    DensityCancellation m₀ p pr h P5 pp ep := by
  obtain ⟨C, hC, hmomC⟩ := DensityDC.moment_input_le 2 (by norm_num) (1440 * stageDelta)
    (by unfold stageDelta; norm_num)
  have hK : 1 ≤ blockScale := by unfold blockScale; norm_num
  have : NeZero blockScale := ⟨by unfold blockScale; norm_num⟩
  apply densityCancellation_of_lift_moments m₀ p pr h P5 pp ep hinj h64 hC₂
    (Cε := ((modulus pr h : ℕ) : ℝ) ^ 4 * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ 4 * C) *
      blockScale) (by positivity) (max L₁ (2 ^ 20 * blockScale)) hcop0 hcopE hpre hcover
  · intro L hL A _ bI s
    exact indexedInput_fourth_moment m₀ (p L) C
      (fun Q hQ c M hM h1 h2 => hmomC m₀ (p L) (fun j => (Fact.out : (p L j).Prime)) (hinj L)
        Q hQ c M hM h1 h2)
      hC hK (le_trans (le_max_right _ _) hL) A bI s
  · intro L hL A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu hGv hGw
    exact hSteps L (le_trans (le_max_left _ _) hL) A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu
      hGv hGw

end Final

end Sarkozy.CancellationSteps
