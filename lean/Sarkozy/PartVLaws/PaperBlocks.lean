module

public import Sarkozy.PartVLaws.PaperPrefix
public import Sarkozy.TailMoment.SingleLabel
public import Sarkozy.PartV.PositiveRootRP
public import Sarkozy.PartV.RootAffine
public import Sarkozy.PartV.CoherentRP

@[expose] public section

/-!
# Block atoms of the paper's prefix law (`def:construction`(b))

`paper/sections/18_design.tex`, `def:construction`(b); `paper/sections/20c_middle_frame.tex`,
`lem:front12:reference`(iii); `paper/sections/25_upper_reference.tex`, `lem:upper-reference-rp`.

`BlockAtom blockOf b` is one block of the class-three coordinates with its law and the three
properties of (R1)–(R3); `PaperBlockAtoms.ofAtoms` collects them, so that `paperPrefixLaw`,
`paperPrefix_rp`, `paperPrefix_inv`, `paperPrefix_unif` give D1's `μ₀`, `rp₀`, `inv₀`, `unif₀`.

* **`upperBlockAtom`**: an upper block (primes `≥ 81·10¹²`, so every block of `[P₃, P₄)`) with the
  weights of its band. Its law is the upper block reference `upperBlockReference` on the block's
  own coordinates (the modulus `paperM0 j` is the prime `j`, `paperM0_block_fact`); the three
  properties come from `upperBlock_R1R3`, given the validity of the band inputs (V1)–(V3) on the
  block (a hypothesis, `lem:upper-reference-rp`(ii)).
* **`middleBlockAtom_uniform`**, `middleBlockAtom_individual`, `middleBlockAtom_coherent`: a
  middle block with the uniform root (pieces below `2³⁰`), the individual-square root or the
  coherent root (with its dictionary as an input), from V1's
  `middleBlockReference_*_familyPositive`, `_affine` and `_uniform`, given V1's row, root-envelope
  and layer-cap inputs (`lem:front12:reference`(i),(ii), hypotheses). `middleNonempty_explicit`
  gives the nonemptiness of the six middle labelling sets at every prime `p ≥ 2²⁰` (below `Q₃`),
  under H1.
* `uniformBlockAtom`: the uniform law on the block's labels, a block atom with no hypothesis. It is
  **not** the paper's block law; it shows that `PaperBlockAtoms` can be inhabited for every
  partition (non-vacuity), e.g. `paperPrefix_uniformBlocks_rp`.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.FiveType.TwoCoord

variable {B : Type} [Fintype B] [DecidableEq B] (blockOf : PaperJ0 → B)

/-- **One block atom**: a law on the labels of the coordinates of the block `b`, with (R1)–(R3). -/
structure BlockAtom (b : B) where
  law : FiniteLaw (Slot → AtomLabel paperM0 (paperAtomMap blockOf) (.inr b))
  rp : TheoremC.FamilyReflectionPositive (signedIntegral law.weight)
  inv : ∀ (α : ∀ j : {j : PaperJ0 // paperAtomMap blockOf j = .inr b}, (ZMod (paperM0 j.1))ˣ)
    (β : AtomLabel paperM0 (paperAtomMap blockOf) (.inr b)),
    (∀ j, IsSquare (α j : ZMod (paperM0 j.1))) →
      ∀ H : (Slot → AtomLabel paperM0 (paperAtomMap blockOf) (.inr b)) → ℝ,
        law.expect (fun z => H (fiberAffine paperM0 (paperAtomMap blockOf) α β z)) = law.expect H
  unif : HasUniformMarginals law

variable {blockOf}

/-- The block atoms of a partition, one for each block. -/
def PaperBlockAtoms.ofAtoms (f : ∀ b, BlockAtom blockOf b) : PaperBlockAtoms blockOf where
  law b := (f b).law
  rp b := (f b).rp
  inv b := (f b).inv
  unif b := (f b).unif

variable (blockOf)

/-! ## The uniform block atom (non-vacuity) -/

/-- **The uniform law on a block's labels is a block atom** (not the paper's block law). -/
noncomputable def uniformBlockAtom (b : B) : BlockAtom blockOf b where
  law := FiniteLaw.uniform _
  rp := uniform_familyPositive
  inv α β _ H := uniform_expect_equiv (fiberAffine paperM0 (paperAtomMap blockOf) α β) H
  unif := TailMoment.uniform_hasUniformMarginals

/-- With uniform blocks, all four fields hold with no hypothesis: `PaperBlockAtoms` is inhabited
for every partition. -/
theorem paperPrefix_uniformBlocks_rp :
    TheoremC.FamilyReflectionPositive (signedIntegral
      (paperPrefixLaw (PaperBlockAtoms.ofAtoms (uniformBlockAtom blockOf))).weight) :=
  paperPrefix_rp _

/-! ## Upper blocks -/

section Upper

variable {b : B}

/-- The primes of a block, as the index function of the block laws. -/
abbrev blockPrimes (b : B) (j : {j : PaperJ0 // paperAtomMap blockOf j = .inr b}) : ℕ := paperM0 j.1

omit [Fintype B] [DecidableEq B] in
theorem blockPrimes_ne_two (b : B) (hp : ∀ j, (81 * 10 ^ 12 : ℝ) ≤ blockPrimes blockOf b j)
    (j : {j : PaperJ0 // paperAtomMap blockOf j = .inr b}) : blockPrimes blockOf b j ≠ 2 := by
  intro h
  have := hp j
  rw [h] at this
  norm_num at this

/-- **An upper block as a block atom** (`lem:upper-reference-rp`): the upper block reference with
the weights `W` of its band, on a block of primes `≥ 81·10¹²`, under H1, the gates of the weights
and the validity of the band inputs (V1)–(V3) on the block (hypotheses). -/
noncomputable def upperBlockAtom (hW : Target.Weil)
    (hp : ∀ j, (81 * 10 ^ 12 : ℝ) ≤ blockPrimes blockOf b j) (W : UpperWeights) {r : ℝ}
    (hr : 0 < r) {ord res : FieldTy → CompletionInput} {k : PType → PType → ℝ}
    (hWOK : WeightsOK W ord res k)
    (hV : ∀ hne hW' hp', ValidInputs (upperBlockFieldLaws (blockPrimes blockOf b) hne)
      (block_upperDatumHyp (blockPrimes blockOf b) hW' hp' hne) r ord res k) :
    BlockAtom blockOf b :=
  have hW' : ∀ j, WeilBound (ZMod (blockPrimes blockOf b j)) := fun j =>
    weilBound_of_target hW _ (blockPrimes_ne_two blockOf b hp j)
  have h20 : ∀ j, (2 : ℝ) ^ 20 ≤ blockPrimes blockOf b j := fun j => le_trans (by norm_num) (hp j)
  have hne := upperNonempty_explicit (blockPrimes blockOf b) hW' hp
  have hR := upperBlock_R1R3 (blockPrimes blockOf b) hW h20 hne W hr hWOK fun hW'' =>
    hV hne hW'' h20
  { law := upperBlockReference (blockPrimes blockOf b) hne W hr.le
    rp := hR.1
    inv := blockAtom_inv_of_affine _ hR.2.2
    unif := hR.2.1 }

end Upper

/-! ## Middle blocks -/

section MiddleNonempty

theorem nbrCount_recordGraph (Λ : Type) [Fintype Λ] [DecidableEq Λ] (v : ZMod 6 × Λ) :
    nbrCount (recordGraph Λ) univ v =
      (univ.filter fun u : ZMod 6 × Λ => v.1 = rot u.1 ∨ u.1 = rot v.1).card := by
  unfold nbrCount
  congr 1
  exact Finset.filter_congr fun u _ => by rw [mem_recordGraph, mem_recordGraph]

theorem nbrCount_foldGraph (Λ : Type) [Fintype Λ] [DecidableEq Λ] (v : Fin 3 × Λ) :
    nbrCount (foldGraph Λ) univ v =
      (univ.filter fun u : Fin 3 × Λ => (u.1 = 0 ∧ v.1 = 2) ∨ (v.1 = 0 ∧ u.1 = 2)).card := by
  unfold nbrCount
  congr 1
  exact Finset.filter_congr fun u _ => by rw [mem_foldGraph, mem_foldGraph]

theorem nbrCount_matchGraph (Λ : Type) [Fintype Λ] [DecidableEq Λ] (v : Fin 3 × Λ) :
    nbrCount (matchGraph Λ) univ v = 0 := by
  unfold nbrCount
  simp [matchGraph]

theorem degree_record_two : ∀ v : ZMod 6 × Fin 2,
    (univ.filter fun u : ZMod 6 × Fin 2 => v.1 = rot u.1 ∨ u.1 = rot v.1).card ≤ 8 := by
  unfold rot
  decide +kernel

theorem degree_record_one : ∀ v : ZMod 6 × Fin 1,
    (univ.filter fun u : ZMod 6 × Fin 1 => v.1 = rot u.1 ∨ u.1 = rot v.1).card ≤ 8 := by
  unfold rot
  decide +kernel

theorem degree_fold_two : ∀ v : Fin 3 × Fin 2,
    (univ.filter fun u : Fin 3 × Fin 2 => (u.1 = 0 ∧ v.1 = 2) ∨ (v.1 = 0 ∧ u.1 = 2)).card ≤ 8 := by
  decide +kernel

theorem degree_fold_one : ∀ v : Fin 3 × Fin 1,
    (univ.filter fun u : Fin 3 × Fin 1 => (u.1 = 0 ∧ v.1 = 2) ∨ (v.1 = 0 ∧ u.1 = 2)).card ≤ 8 := by
  decide +kernel

/-- **The middle graphs have labellings at every prime `p ≥ 2²⁰`**, under Weil's bound (explicit
form of V1's `middleNonempty_of_large`; the middle range starts at `Q₃ > 2²⁰`). -/
theorem middleNonempty_explicit {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ)
    [∀ i, Fact (pr i).Prime] (hW : ∀ i, WeilBound (ZMod (pr i)))
    (hp : ∀ i, (2 : ℝ) ^ 20 ≤ pr i) : MiddleNonempty pr := by
  have hq : ∀ i, (2 : ℝ) ^ 20 ≤ (Fintype.card (ZMod (pr i)) : ℝ) := fun i => by
    rw [ZMod.card]
    exact hp i
  have thr : ∀ i (n : ℕ), n ≤ 36 → ∀ t ≤ 8, 0 < (Fintype.card (ZMod (pr i)) : ℝ) -
      softError (Fintype.card (ZMod (pr i))) t - 2 ^ t * (n : ℝ) := fun i n hn =>
    threshold_eight (hq i) (Nat.cast_nonneg _) (by exact_mod_cast hn)
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · exact injLabellings_nonempty_of_degree (hW i) _
      (fun v => (nbrCount_recordGraph (Fin 2) v).trans_le (degree_record_two v))
      (thr i _ (by decide))
  · exact injLabellings_nonempty_of_degree (hW i) _
      (fun v => (nbrCount_foldGraph (Fin 2) v).trans_le (degree_fold_two v)) (thr i _ (by decide))
  · exact injLabellings_nonempty_of_degree (hW i) _
      (fun v => (nbrCount_matchGraph (Fin 2) v).trans_le (Nat.zero_le 8)) (thr i _ (by decide))
  · exact injLabellings_nonempty_of_degree (hW i) _
      (fun v => (nbrCount_recordGraph (Fin 1) v).trans_le (degree_record_one v))
      (thr i _ (by decide))
  · exact injLabellings_nonempty_of_degree (hW i) _
      (fun v => (nbrCount_foldGraph (Fin 1) v).trans_le (degree_fold_one v)) (thr i _ (by decide))
  · exact injLabellings_nonempty_of_degree (hW i) _
      (fun v => (nbrCount_matchGraph (Fin 1) v).trans_le (Nat.zero_le 8)) (thr i _ (by decide))

end MiddleNonempty

section Middle

variable {b : B}

/-- **A middle block with the uniform root as a block atom** (`lem:front12:reference`(iii), pieces
below `2³⁰`): V1's middle block reference with the weights `W` and inputs `I` of its piece, given
V1's inputs: the thirteen inequalities, the rows (i), the root envelopes and the layer caps (ii). -/
noncomputable def middleBlockAtom_uniform (hne : MiddleNonempty (blockPrimes blockOf b))
    (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (hW : W.Completes I)
    (hf₂ : 0 ≤ I.f₂) (hf₁ : 0 ≤ I.f₁)
    (hrows₂ : RowBounds (fieldDatum (middleBlock_datumHyp₂ (blockPrimes blockOf b) hne))
      I.f₂ I.h₂ r)
    (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne))
      I.f₁ I.h₁ r)
    (hroot₂ : RootEnvelope (fieldDatum (middleBlock_datumHyp₂ (blockPrimes blockOf b) hne)) I.d r)
    (hroot₁ : RootEnvelope (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne)) I.d₁ r)
    (hcap : MiddleLayerCaps (middleBlockFieldLaws (blockPrimes blockOf b) hne
      (uniformRoot (blockPrimes blockOf b) hne)) I.k r) :
    BlockAtom blockOf b where
  law := middleBlockReference (blockPrimes blockOf b) hne (uniformRoot (blockPrimes blockOf b) hne)
    W hr
  rp := middleBlockReference_uniform_familyPositive (blockPrimes blockOf b) hne W I hr hW hf₂ hf₁
    hrows₂ hrows₁ hroot₂ hroot₁ hcap
  inv := blockAtom_inv_of_affine _ fun α β hα H =>
    middleBlockReference_uniform_affine (blockPrimes blockOf b) hne α β hα W hr H
  unif := middleBlockReference_uniform (blockPrimes blockOf b) hne _
    (fun o g => blockGraphLaw_vertex_uniform (blockPrimes blockOf b) _ hne.L2 o g) W hr

/-- **A middle block with the individual-square root as a block atom** (`def:positive-root`,
pieces from `2³⁰`), given V1's inputs. -/
noncomputable def middleBlockAtom_individual (hne : MiddleNonempty (blockPrimes blockOf b))
    (u : ℚ) (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (hW : W.Completes I)
    (hf₂ : 0 ≤ I.f₂) (hf₁ : 0 ≤ I.f₁)
    (hrows₂ : RowBounds
      (fieldDatum (middleBlock_datumHyp₂_individual (blockPrimes blockOf b) hne u)) I.f₂ I.h₂ r)
    (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne))
      I.f₁ I.h₁ r)
    (hroot₂ : RootEnvelope
      (fieldDatum (middleBlock_datumHyp₂_individual (blockPrimes blockOf b) hne u)) I.d r)
    (hroot₁ : RootEnvelope (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne)) I.d₁ r)
    (hcap : MiddleLayerCaps (middleBlockFieldLaws (blockPrimes blockOf b) hne
      (individualBlockRoot (blockPrimes blockOf b) u hne.L2)) I.k r) :
    BlockAtom blockOf b where
  law := middleBlockReference (blockPrimes blockOf b) hne
    (individualBlockRoot (blockPrimes blockOf b) u hne.L2) W hr
  rp := middleBlockReference_individual_familyPositive (blockPrimes blockOf b) hne u W I hr hW hf₂
    hf₁ hrows₂ hrows₁ hroot₂ hroot₁ hcap
  inv := blockAtom_inv_of_affine _ fun α β hα H =>
    middleBlockReference_individual_affine (blockPrimes blockOf b) hne u α β hα W hr H
  unif := middleBlockReference_individual_uniform (blockPrimes blockOf b) hne u W hr

/-- **A middle block with the coherent root as a block atom** (`def:positive-root`,
`lem:imp:coherent39-law`; the dictionary and its `𝒢₆`-invariance are inputs), given V1's
inputs. -/
noncomputable def middleBlockAtom_coherent (hne : MiddleNonempty (blockPrimes blockOf b))
    (D : Dictionary) (hD : D.Invariant) (u : ℚ) {η : ℚ} (hη : 0 < η) (W : MiddleWeights)
    (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (hW : W.Completes I) (hf₂ : 0 ≤ I.f₂)
    (hf₁ : 0 ≤ I.f₁)
    (hrows₂ : RowBounds
      (fieldDatum (middleBlock_datumHyp₂_coherent (blockPrimes blockOf b) hne D hD u hη))
      I.f₂ I.h₂ r)
    (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne))
      I.f₁ I.h₁ r)
    (hroot₂ : RootEnvelope
      (fieldDatum (middleBlock_datumHyp₂_coherent (blockPrimes blockOf b) hne D hD u hη)) I.d r)
    (hroot₁ : RootEnvelope (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne)) I.d₁ r)
    (hcap : MiddleLayerCaps (middleBlockFieldLaws (blockPrimes blockOf b) hne
      (coherentBlockRoot (blockPrimes blockOf b) D u hη hne.L2)) I.k r) :
    BlockAtom blockOf b where
  law := middleBlockReference (blockPrimes blockOf b) hne
    (coherentBlockRoot (blockPrimes blockOf b) D u hη hne.L2) W hr
  rp := middleBlockReference_coherent_familyPositive (blockPrimes blockOf b) hne D hD u hη W I hr
    hW hf₂ hf₁ hrows₂ hrows₁ hroot₂ hroot₁ hcap
  inv := blockAtom_inv_of_affine _ fun α β hα H =>
    middleBlockReference_coherent_affine (blockPrimes blockOf b) hne D u hη α β hα W hr H
  unif := middleBlockReference_uniform (blockPrimes blockOf b) hne _
    (coherentBlockRoot_vertex_uniform (blockPrimes blockOf b) D u hη hne.L2) W hr

end Middle

end Sarkozy.PartVLaws
