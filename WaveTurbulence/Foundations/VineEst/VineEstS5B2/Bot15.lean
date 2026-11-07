/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot14
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp19Bottom

/-! # V5 Step 4d-B2: the bottom vine, part 15 (the states reached by a batch over the single member `pstar`)

A batch over `[pstar]` either skips the member (the state is `A` with its chain region) or applies one operation `op` at `pstar` (the state is `op.output`
with the transported chain region).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {p : ℕ}

theorem reach_nil {kind : Bool} {L : List ι} {A B : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family}
    {cB : ChainAt B.skeleton B.family} (h : Reach p kind L A c B cB) (hL : L = []) :
    (⟨B, cB⟩ : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family) = ⟨A, c⟩ := by
  induction h with
  | nil A c => rfl
  | skip i h ih => cases hL
  | apply op h ih => cases hL

theorem reach_single {kind : Bool} {pstar : ι} {A B : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family}
    {cB : ChainAt B.skeleton B.family} (h : Reach p kind [pstar] A c B cB) :
    (⟨B, cB⟩ : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family) = ⟨A, c⟩ ∨
      ∃ op : FamilyOperation (p := p) (kind := kind) A pstar,
        (⟨B, cB⟩ : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family) =
          ⟨op.output, ChainAt.nextA A c pstar op.choice⟩ := by
  generalize hL : [pstar] = L at h
  induction h with
  | nil A c => cases hL
  | skip i h ih =>
    left
    exact reach_nil h (List.cons.inj hL).2.symm
  | apply op h ih =>
    right
    obtain ⟨rfl, hL'⟩ := List.cons.inj hL
    exact ⟨op, reach_nil h hL'.symm⟩

end WaveTurbulence.VineEstS5B2
