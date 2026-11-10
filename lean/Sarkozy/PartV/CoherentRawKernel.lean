module

public import Sarkozy.PartV.CoherentExceptional
public import Sarkozy.Extraction.CoverRows

/-! Concrete positive-kernel bounds on the two coherent cuts of the record graph. -/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.Labellings

def rawCrossEdges (isLayer : Bool) : Finset (Vertex × Vertex) :=
  (recordGraph (Fin 2)).E.filter fun e => cutSide isLayer e.1 ≠ cutSide isLayer e.2

theorem rawCrossEdges_card (isLayer : Bool) :
    (rawCrossEdges isLayer).card = if isLayer then 12 else 16 := by
  cases isLayer <;> decide +kernel

variable {p : ℕ} [Fact p.Prime]

noncomputable def rawCrossKernel (isLayer : Bool) (x : Vertex → ZMod p) : ℝ :=
  ∏ e ∈ rawCrossEdges isLayer, (1 + (quadraticChar (ZMod p) (x e.2 - x e.1) : ℝ))

theorem rawCrossKernel_nonneg (isLayer : Bool) (x : Vertex → ZMod p) :
    0 ≤ rawCrossKernel isLayer x :=
  prod_nonneg fun _ _ => (Extraction.coverRow_one_add_chi _).1

theorem rawCrossKernel_le (isLayer : Bool) (x : Vertex → ZMod p) :
    rawCrossKernel isLayer x ≤ if isLayer then 4096 else 65536 := by
  calc
    _ ≤ ∏ _e ∈ rawCrossEdges isLayer, (2 : ℝ) :=
      prod_le_prod₀ (fun _ _ => (Extraction.coverRow_one_add_chi _).1)
        (fun _ _ => (Extraction.coverRow_one_add_chi _).2)
    _ = _ := by rw [prod_const, rawCrossEdges_card]; cases isLayer <;> norm_num

/-- The paper's `P_* = 144 · 65536 · D₆ / p³`, with the raw root bound supplied. -/
theorem chamber_exceptional_mass
    (a : Half false true → ZMod p) (ha : Function.Injective a)
    (ν : FiniteLaw (Half false false → ZMod p)) (D : ℝ) (hD : 0 ≤ D)
    (hν : ∀ b, ν.weight b ≤ D / (p : ℝ) ^ 6) :
    CubePins.mass (fun b => ν.weight b * rawCrossKernel false (joinHalves false a b))
      (Exceptional false a) ≤ 144 * 65536 * D / (p : ℝ) ^ 3 := by
  exact exceptional_kernel_mass false a ha ν _ 65536 D (by norm_num) hD
    (fun b => rawCrossKernel_nonneg false _) (fun b => rawCrossKernel_le false _) hν

theorem layer_exceptional_mass
    (a : Half true true → ZMod p) (ha : Function.Injective a)
    (ν : FiniteLaw (Half true false → ZMod p)) (D : ℝ) (hD : 0 ≤ D)
    (hν : ∀ b, ν.weight b ≤ D / (p : ℝ) ^ 6) :
    CubePins.mass (fun b => ν.weight b * rawCrossKernel true (joinHalves true a b))
      (Exceptional true a) ≤ 144 * 4096 * D / (p : ℝ) ^ 3 := by
  exact exceptional_kernel_mass true a ha ν _ 4096 D (by norm_num) hD
    (fun b => rawCrossKernel_nonneg true _) (fun b => rawCrossKernel_le true _) hν

end Sarkozy.PartV.CoherentDictionary
