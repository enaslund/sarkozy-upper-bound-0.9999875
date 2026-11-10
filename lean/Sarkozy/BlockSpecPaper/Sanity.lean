module

public import Sarkozy.BlockSpecPaper.Lemmas
public import Sarkozy.MiddleRecords.PieceCompletion

@[expose] public section



open Finset

namespace Sarkozy.BlockSpecPaper

open Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.BlockSpecPaper.AllpData

/-- The block type is inhabited for every within-site rule. -/
noncomputable instance (cell : ℕ → ℕ) : Inhabited (PaperBlock cell) :=
  ⟨paperBlockOf cell baseCoord⟩

/-- The prime `19 951 627` lies in the first piece and in no other. -/
theorem base_piece_unique : ∀ i : Fin 33,
    pieceStart i ≤ 19951627 → 19951627 < pieceStop i → i = 0 := by
  decide +kernel

/-- **The block of the least class-three prime lies in the first middle piece** `[Q₃, X₂)`. -/
theorem baseBlock_site (cell : ℕ → ℕ) : blockSite (paperBlockOf cell baseCoord) = .inl 0 := by
  have h3 : baseCoord.1 % 4 ≠ 1 := by decide
  have hv := paperBlockOf_val (cell := cell) h3
  unfold blockSite
  rw [hv]
  change siteOf 19951627 = .inl 0
  have h1 : Q3 ≤ 19951627 ∧ 19951627 < P3 := ⟨by norm_num [Q3], by norm_num [P3]⟩
  unfold siteOf
  simp only [h1, and_self, ↓reduceDIte]
  obtain ⟨ha, hb⟩ := (exists_piece h1.1 h1.2).choose_spec
  rw [base_piece_unique _ ha hb]

theorem allp_same_nonroot_caps : ∀ i : Fin 33,
    (MiddleRecords.CompletionData.record i).d₁ ≤ (allpRecord i).d₁ ∧
    (allpRecord i).f₁ = (MiddleRecords.CompletionData.record i).f₁ ∧
    (allpRecord i).f₂ = (MiddleRecords.CompletionData.record i).f₂ ∧
    (allpRecord i).h₁ = (MiddleRecords.CompletionData.record i).h₁ ∧
    (allpRecord i).h₂ = (MiddleRecords.CompletionData.record i).h₂ ∧
    (allpRecord i).kD = (MiddleRecords.CompletionData.record i).kD ∧
    (allpRecord i).kE = (MiddleRecords.CompletionData.record i).kE := by
  decide +kernel

theorem selected_root_cap_lt_allp : ∀ i : Fin 33,
    (MiddleRecords.CompletionData.record i).d < (allpRecord i).d := by
  decide +kernel

end Sarkozy.BlockSpecPaper
