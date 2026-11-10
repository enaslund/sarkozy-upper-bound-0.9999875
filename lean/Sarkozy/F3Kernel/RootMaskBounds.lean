module

public import Sarkozy.F3Kernel.MaskBounds
public import Sarkozy.F3Kernel.ClassRootChecksA

/-!
# Accepted roots have no unused matrix bits

Every initial mask is assembled from submasks of the graph and individual matrix positions.
The two connector decisions preserve this property, so both accepted root kinds satisfy
the raw-word invariant needed for the SWAR free-degree proof.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

theorem classBPM_matrixWord (e f g : Fin 36 × Fin 36) : MatrixWord (classBPM e f g) :=
  (matrixWord_single _ _).lor ((matrixWord_single _ _).lor (matrixWord_single _ _))

theorem classBP_matrixWord (e f g : Fin 36 × Fin 36) : MatrixWord (classBP e f g) :=
  (matrixWord_single _ _).lor ((matrixWord_single _ _).lor (matrixWord_single _ _))

theorem classBAM_matrixWord {G : Consts} (h : MatrixWord G.EM) (e f g : Fin 36 × Fin 36) :
    MatrixWord (classBAM G e f g) :=
  (h.xor ((h.land _).lor (h.land _))).lor
    ((h.land _).lor (((h.land _).land _).lor ((h.land _).land _)))

theorem classBA_matrixWord {G : Consts} (h : MatrixWord G.ET) (e f g : Fin 36 × Fin 36) :
    MatrixWord (classBA G e f g) :=
  (h.xor ((h.land _).lor (h.land _))).lor
    ((h.land _).lor (((h.land _).land _).lor ((h.land _).land _)))

theorem RootBTrace.matrixWords {G : Consts} {c : Cyl} (t : RootBTrace G c)
    (hM : MatrixWord G.EM) (hT : G.WellFormedT) : c.MatrixWords := by
  unfold Cyl.MatrixWords
  rw [t.matrixPresent, t.matrixAbsent, t.present, t.absent]
  have hpm := classBPM_matrixWord t.e t.f t.g
  have hpt := classBP_matrixWord t.e t.f t.g
  have ham := classBAM_matrixWord hM t.e t.f t.g
  have hat := classBA_matrixWord hT t.e t.f t.g
  exact ⟨hpm, ham.xor (ham.land _), hpt, hat.xor (hat.land _)⟩

theorem classAStart_matrixWords {G : Consts} (hM : MatrixWord G.EM)
    (hT : G.WellFormedT) (e f : Fin 36 × Fin 36) : (classAStart G e f).MatrixWords := by
  have hpm : MatrixWord (classAPM e f) := (matrixWord_single _ _).lor (matrixWord_single _ _)
  have hpt : MatrixWord (classAP e f) := (matrixWord_single _ _).lor (matrixWord_single _ _)
  have ham : MatrixWord (classAAM G e f) :=
    (hM.land _).lor ((hM.xor ((hM.land _).lor (hM.land _))).land _)
  have hat : MatrixWord (classAA G e f) :=
    (MatrixWord.land hT _).lor
      ((MatrixWord.xor hT ((MatrixWord.land hT _).lor (MatrixWord.land hT _))).land _)
  exact ⟨hpm, ham.xor (ham.land _), hpt, hat.xor (hat.land _)⟩

theorem ConnectorChange.matrixWords {G : Consts} {c d : Cyl} {e : Fin 36 × Fin 36}
    (h : ConnectorChange G c e d) (hc : c.MatrixWords) : d.MatrixWords := by
  cases h with
  | present => exact hc.present e
  | absent => exact hc.absent e
  | unchanged => exact hc

theorem RootATrace.matrixWords {G : Consts} {c : Cyl} (t : RootATrace G c)
    (hM : MatrixWord G.EM) (hT : G.WellFormedT) : c.MatrixWords :=
  t.second.matrixWords (t.first.matrixWords (classAStart_matrixWords hM hT t.e t.f))

theorem classRoot_matrixWords {G : Consts} (hM : MatrixWord G.EM) (hT : G.WellFormedT)
    {key : ℕ} {c : Cyl} (hr : classRoot G key = some c) : c.MatrixWords := by
  by_cases hk : Nat.land (Nat.shiftRight key 24) 1 = 0
  · obtain ⟨t⟩ := classRoot_B_trace hT hk hr
    exact t.matrixWords hM hT
  · obtain ⟨t⟩ := classRoot_A_trace hT hk hr
    exact t.matrixWords hM hT

end Sarkozy.F3Kernel
