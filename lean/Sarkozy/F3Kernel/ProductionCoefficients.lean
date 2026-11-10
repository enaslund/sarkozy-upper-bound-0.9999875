module

public import Sarkozy.F3Kernel.CompletionBounds

/-!
# Integer upper bounds for the production coefficients

The sums are compared to the accepted certificate in the full-data assembly. These small
kernel checks bound their rational completion factors without trusting decimal arithmetic.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings

def productionTotal20 : ℕ → ℕ
  | 2 => 1501562124900058879249386227394
  | 3 => 8750965918808624230895849334674817024
  | 4 => 22953500344884780253843872668794413383680
  | _ => 0

def productionTotal22 : ℕ → ℕ
  | 2 => 1208270260258534013764407225179
  | 3 => 9727121270429289682937155996613607424
  | 4 => 170767602063266717498086360775929815367680
  | _ => 0

def coefficientCap20 : ℕ → ℕ
  | 2 => 81439546103
  | 3 => 474623767282066575
  | 4 => 1244926936187701663472
  | _ => 0

def coefficientCap22 : ℕ → ℕ
  | 2 => 65532407839
  | 3 => 527567240578306558
  | 4 => 9261907092271439366132
  | _ => 0

theorem coefficientCap20_check : ∀ i : Fin 3,
    rationalCoefficient (productionTotal20 (i + 2)) (i + 2) ≤ coefficientCap20 (i + 2) := by
  decide +kernel

theorem coefficientCap22_check : ∀ i : Fin 3,
    rationalCoefficient (productionTotal22 (i + 2)) (i + 2) ≤ coefficientCap22 (i + 2) := by
  decide +kernel

theorem coefficientCap20_sound {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) :
    rationalCoefficient (productionTotal20 k) k ≤ coefficientCap20 k := by
  have hlt : k - 2 < 3 := by omega
  have he : k - 2 + 2 = k := by omega
  simpa only [he] using coefficientCap20_check ⟨k - 2, hlt⟩

theorem coefficientCap22_sound {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) :
    rationalCoefficient (productionTotal22 k) k ≤ coefficientCap22 k := by
  have hlt : k - 2 < 3 := by omega
  have he : k - 2 + 2 = k := by omega
  simpa only [he] using coefficientCap22_check ⟨k - 2, hlt⟩

noncomputable def productionPolynomial (cap : ℕ → ℕ) (p : ℕ) : ℝ :=
  ∑ k ∈ ({2, 3, 4} : Finset ℕ), (cap k : ℝ) * (Real.sqrt p)⁻¹ ^ k

theorem certificatePolynomial_le_caps (H : OrientedGraph (Fin 36))
    (hd : univ.sup (Sarkozy.Extraction.rowsDeg0 H) ≤ 10) (cs : List CertificateChunk)
    (total cap : ℕ → ℕ)
    (ht : ∀ k, (k = 2 ∨ k = 3 ∨ k = 4) → chunksAccumulator cs k = total k)
    (hc : ∀ k, (k = 2 ∨ k = 3 ∨ k = 4) → rationalCoefficient (total k) k ≤ cap k) (p : ℕ) :
    certificatePolynomial H productionAnchor 36 cs (Real.sqrt p)⁻¹ ≤
      productionPolynomial cap p := by
  refine (certificatePolynomial_le_rational H hd cs _
    (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans ?_
  apply sum_le_sum
  intro k hk
  have hk' : k = 2 ∨ k = 3 ∨ k = 4 := by
    simpa only [mem_insert, mem_singleton] using hk
  rw [ht k hk']
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) k)
  have hrat : (rationalCoefficient (total k) k : ℝ) ≤ (cap k : ℚ) :=
    Rat.cast_le.mpr (hc k hk')
  exact hrat

end Sarkozy.F3Kernel
