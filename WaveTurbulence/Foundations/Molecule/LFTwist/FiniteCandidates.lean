/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructionChoice

/-! # Finite bounded spaces containing every admissible LF choice

These are finite supersets, not a replacement for the source LF relation:
regular assignments have bounded total replacement order, and actual node
layers lie in {0,...,p}. Both source skeleton choices are retained.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist

@[expose] def BoundedReconstruction {w : ℕ} (S : Garden w) (m : ℕ) :=
  {D : ReconstructionData S // D.size ≤ m}

instance instFiniteBoundedReconstruction {w : ℕ} (S : Garden w) (m : ℕ) :
    Finite (BoundedReconstruction S m) := by
  classical
  let f : BoundedReconstruction S m →
      {E : ReplacementFamily (Fintype.card (GBranch S.tree)) (Fintype.card (SourcePair S)) // E.size ≤ m} :=
    fun D => ⟨D.1.family, by rw [ReconstructionData.family_size]; exact D.2⟩
  apply Finite.of_injective f
  intro D E he
  exact Subtype.ext (ReconstructionData.family_injective S (congrArg Subtype.val he))

@[expose] def BoundedLayering {w : ℕ} (G : Garden w) (p : ℕ) :=
  {f : GNode G.tree → ℕ // IsLayering G f ∧ ∀ n, f n ≤ p}

instance instFiniteBoundedLayering {w : ℕ} (G : Garden w) (p : ℕ) : Finite (BoundedLayering G p) := by
  classical
  let code : BoundedLayering G p → (GNode G.tree → Fin (p+1)) :=
    fun f n => ⟨f.1 n, Nat.lt_succ_of_le (f.2.2 n)⟩
  apply Finite.of_injective code
  intro f g he
  apply Subtype.ext
  funext n
  exact congrArg Fin.val (congrFun he n)

@[expose] def ReconstructionLayerFamily {w : ℕ} (S : Garden w) (hS : S.IsPlain) (m p : ℕ) :=
  Σ D : BoundedReconstruction S m, BoundedLayering (D.1.garden hS) p

instance instFiniteReconstructionLayerFamily {w : ℕ} (S : Garden w) (hS : S.IsPlain) (m p : ℕ) :
    Finite (ReconstructionLayerFamily S hS m p) := by
  unfold ReconstructionLayerFamily
  infer_instance

/-- Decode a finite family datum to its literal actual layered garden. -/
@[expose] noncomputable def reconstructionFamilyGarden {w : ℕ} {S : Garden w} {hS : S.IsPlain} {m p : ℕ}
    (F : ReconstructionLayerFamily S hS m p) : LayeredGarden w :=
  ⟨F.1.1.garden hS, F.2.1, F.2.2.1⟩

theorem finite_reconstructionFamilyGardens {w : ℕ} (S : Garden w) (hS : S.IsPlain) (m p : ℕ) :
    Set.Finite (Set.range (reconstructionFamilyGarden (S := S) (hS := hS) (m := m) (p := p))) :=
  Set.finite_range _

/-- The finite candidate space keeps both original and twisted source skeletons. -/
@[expose] def LFChoiceLayerFamily {w : ℕ} (G : Garden w) (P : CorePlacement G)
    (hG : G.IsPlain) (m p : ℕ) :=
  Σ ε : Bool, ReconstructionLayerFamily (chosenSkeleton G P ε) (chosenSkeleton_plain G P hG ε) m p

instance instFiniteLFChoiceLayerFamily {w : ℕ} (G : Garden w) (P : CorePlacement G)
    (hG : G.IsPlain) (m p : ℕ) : Finite (LFChoiceLayerFamily G P hG m p) := by
  unfold LFChoiceLayerFamily
  infer_instance

@[expose] noncomputable def lfCandidateGarden {w : ℕ} {G : Garden w} {P : CorePlacement G}
    {hG : G.IsPlain} {m p : ℕ} (F : LFChoiceLayerFamily G P hG m p) : LayeredGarden w :=
  reconstructionFamilyGarden F.2

theorem finite_lfCandidateGardens {w : ℕ} (G : Garden w) (P : CorePlacement G) (hG : G.IsPlain) (m p : ℕ) :
    Set.Finite (Set.range (lfCandidateGarden (G := G) (P := P) (hG := hG) (m := m) (p := p))) :=
  Set.finite_range _

end WaveTurbulence.LFTwist
