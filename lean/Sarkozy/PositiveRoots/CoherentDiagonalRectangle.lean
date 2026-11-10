module

public import Sarkozy.PositiveRoots.CoherentDiagonalMaps
public import Sarkozy.PositiveRoots.CoherentOffdiagPhysical

/-! The raw-star diagonal traces satisfy whole-rectangle operator bounds. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.L20Cap Sarkozy.Cuts Sarkozy.Recentering Sarkozy.PartV Sarkozy.PartV.CoherentDictionary
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem coreStarPrice_nonneg (S : Finset (Fin 4)) : 0 ≤ coreStarPrice p S :=
  mul_nonneg (mul_nonneg (coreStarFactor_nonneg S) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

omit [Fact p.Prime] in
theorem privateStarPrice_nonneg : 0 ≤ privateStarPrice p :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem core_rawStar_gram (hp3 : p % 4 = 3) (hp7 : 7 < p) [Nonempty (CoreT (ZMod p))]
    (S : Finset (Fin 4)) (hS : S.Nonempty) (f : CoreT (ZMod p) → ℝ) :
    kernelForm coreLaw coreLaw (fun c d => Recentering.ip (fieldLaw p)
      (fun z => StarMatrix.psi S z c.val) (fun z => StarMatrix.psi S z d.val)) f f ≤
      coreStarPrice p S ^ 2 * nrm coreLaw f ^ 2 :=
  gram_le_of_map coreLaw (fieldLaw p) (fun c : CoreT (ZMod p) => fun z => StarMatrix.psi S z c.val)
    (sq_nonneg _) (core_rawStar_map_sq hp3 hp7 S hS) f

theorem private_rawStar_gram (hp3 : p % 4 = 3) [Nonempty (PairT (ZMod p))]
    (S : Finset (Fin 2)) (hS : S.Nonempty) (f : PairT (ZMod p) → ℝ) :
    kernelForm pairLaw pairLaw (fun b d => Recentering.ip (fieldLaw p)
      (fun z => StarMatrix.psi S z ![b.val.1, b.val.2])
      (fun z => StarMatrix.psi S z ![d.val.1, d.val.2])) f f ≤
      privateStarPrice p ^ 2 * nrm pairLaw f ^ 2 :=
  gram_le_of_map pairLaw (fieldLaw p)
    (fun b : PairT (ZMod p) => fun z => StarMatrix.psi S z ![b.val.1, b.val.2])
    (sq_nonneg _) (private_rawStar_map_sq hp3 S hS) f

noncomputable def chamberTrace (S : Support) (x y : CoreT (ZMod p) × PairT (ZMod p)) : ℝ :=
  trace S (chamberConfiguration (emb x.1.val x.2.val) (emb y.1.val y.2.val)) / p

theorem chamberTrace_core (S : Support) (x y : CoreT (ZMod p) × PairT (ZMod p)) :
    chamberTrace S x y = Recentering.ip (fieldLaw p)
      (fun z => StarMatrix.psi (coreSupport true S) z x.1.val *
        StarMatrix.psi (privateSupport true S) z ![x.2.val.1, x.2.val.2])
      (fun z => StarMatrix.psi (coreSupport false S) z y.1.val *
        StarMatrix.psi (privateSupport false S) z ![y.2.val.1, y.2.val.2]) := by
  unfold chamberTrace
  rw [trace_in_chamber]
  unfold Recentering.ip fieldLaw
  rw [FiniteLaw.expect_uniform, ZMod.card]
  congr 1
  apply sum_congr rfl
  intro z _
  exact congrArg₂ (fun a b : ℝ => a * b)
    (psi_emb _ z x.1.val ![x.2.val.1, x.2.val.2])
    (psi_emb _ z y.1.val ![y.2.val.1, y.2.val.2])

theorem chamberTrace_private (S : Support) (x y : CoreT (ZMod p) × PairT (ZMod p)) :
    chamberTrace S x y = Recentering.ip (fieldLaw p)
      (fun z => StarMatrix.psi (privateSupport true S) z ![x.2.val.1, x.2.val.2] *
        StarMatrix.psi (coreSupport true S) z x.1.val)
      (fun z => StarMatrix.psi (privateSupport false S) z ![y.2.val.1, y.2.val.2] *
        StarMatrix.psi (coreSupport false S) z y.1.val) := by
  rw [chamberTrace_core]
  congr 1 <;> funext z <;> ring

theorem core_diagonal_rectangle (hp3 : p % 4 = 3) (hp7 : 7 < p)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (A : CoreT (ZMod p) → PairT (ZMod p) → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ c, pairLaw.expect (fun b => A c b ^ 2) ≤ R)
    (S : Support) (hS : (coreSupport true S).Nonempty) (hT : (coreSupport false S).Nonempty)
    (F G : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
      (fun x y => A x.1 y.2 * A y.1 x.2 * chamberTrace S x y) F G| ≤
      (R * (coreCubeDensity p / 16) * (p : ℝ)⁻¹ *
        coreStarFactor (coreSupport true S) * coreStarFactor (coreSupport false S)) *
          nrm (coreLaw.product pairLaw) F * nrm (coreLaw.product pairLaw) G := by
  have h := decorated_rectangle_norm coreLaw coreLaw_pos pairLaw (fieldLaw p) A
    (fun c : CoreT (ZMod p) => fun z => StarMatrix.psi (coreSupport true S) z c.val)
    (fun c : CoreT (ZMod p) => fun z => StarMatrix.psi (coreSupport false S) z c.val)
    (fun b : PairT (ZMod p) => fun z => StarMatrix.psi (privateSupport true S) z ![b.val.1, b.val.2])
    (fun b : PairT (ZMod p) => fun z => StarMatrix.psi (privateSupport false S) z ![b.val.1, b.val.2])
    (fun b z => abs_prod_chiRe_le _ ![b.val.1, b.val.2] z)
    (fun b z => abs_prod_chiRe_le _ ![b.val.1, b.val.2] z) hR
    (coreStarPrice_nonneg _) (coreStarPrice_nonneg _) hrow
    (core_rawStar_gram hp3 hp7 _ hS) (core_rawStar_gram hp3 hp7 _ hT) F G
  simp_rw [chamberTrace_core]
  have hq := Real.sq_sqrt (by positivity : 0 ≤ (p : ℝ)⁻¹)
  have hD := Real.sq_sqrt (show 0 ≤ coreCubeDensity p / 16 from
    div_nonneg (coreCubeDensity_pos hp7).le (by norm_num))
  unfold coreStarPrice at h
  convert h using 1
  ring_nf at hq hD ⊢
  rw [hq, hD]
  ring

theorem private_diagonal_rectangle (hp3 : p % 4 = 3)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (A : CoreT (ZMod p) → PairT (ZMod p) → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hcol : ∀ b, coreLaw.expect (fun c => A c b ^ 2) ≤ R)
    (S : Support) (hS : (privateSupport true S).Nonempty) (hT : (privateSupport false S).Nonempty)
    (F G : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
      (fun x y => A x.1 y.2 * A y.1 x.2 * chamberTrace S x y) F G| ≤
      (R * ((p : ℝ) / (p - 1)) * (p : ℝ)⁻¹) *
        nrm (coreLaw.product pairLaw) F * nrm (coreLaw.product pairLaw) G := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpos (b : PairT (ZMod p)) : 0 < (pairLaw (F := ZMod p)).weight b := by
    change 0 < (Fintype.card (PairT (ZMod p)) : ℝ)⁻¹
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have h := decorated_rectangle_norm pairLaw hpos coreLaw (fieldLaw p) (fun b c => A c b)
    (fun b : PairT (ZMod p) => fun z => StarMatrix.psi (privateSupport true S) z ![b.val.1, b.val.2])
    (fun b : PairT (ZMod p) => fun z => StarMatrix.psi (privateSupport false S) z ![b.val.1, b.val.2])
    (fun c : CoreT (ZMod p) => fun z => StarMatrix.psi (coreSupport true S) z c.val)
    (fun c : CoreT (ZMod p) => fun z => StarMatrix.psi (coreSupport false S) z c.val)
    (fun c z => abs_prod_chiRe_le _ c.val z) (fun c z => abs_prod_chiRe_le _ c.val z)
    hR privateStarPrice_nonneg privateStarPrice_nonneg hcol
    (private_rawStar_gram hp3 _ hS) (private_rawStar_gram hp3 _ hT)
    (fun x => F (x.2, x.1)) (fun x => G (x.2, x.1))
  rw [nrm_prodComm, nrm_prodComm] at h
  rw [kernelForm_prodComm]
  simp_rw [chamberTrace_private]
  have hq := Real.sq_sqrt (by positivity : 0 ≤ (p : ℝ)⁻¹)
  have hD := Real.sq_sqrt (by positivity : 0 ≤ (p : ℝ) / (p - 1))
  unfold privateStarPrice at h
  convert h using 1
  · simp only [mul_comm, mul_assoc]
  · ring_nf at hq hD ⊢
    rw [hq, hD]
    ring

end Sarkozy.PositiveRoots.CoherentFrame
