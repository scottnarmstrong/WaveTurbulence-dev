/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL23
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunE
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL21
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.GL23`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **G3-LOWDEG (R48), part 23: `Object.unloop` / `Object.lift`.** -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem hyper_added_nonloop {M : Molecule V D} {S : Finset V} {a b : V} (R : Src.HyperLikeRealization Src.γL M S a b) :
    M.atom R.added ≠ M.atom (M.mate R.added) := ends_ne_of R.adjoint.1.2.2.2.1 R.ends_eq

def _root_.WaveTurbulence.GammaLow.FinalCount.Src.HyperLikeRealization.unloop {M : Molecule V D} {S : Finset V} {a b : V} (R : Src.HyperLikeRealization Src.γL M S a b)
    (h : LoopFreeSet M S) : Src.HyperLikeRealization Src.γL M.unloop S a b where
  added := ⟨R.added, hyper_added_nonloop R⟩
  ends_eq := R.ends_eq
  adjoint := ((eraseUnloopEmb M ⟨R.added, hyper_added_nonloop R⟩ h).isVC_iffL rfl).1 R.adjoint

def _root_.WaveTurbulence.GammaLow.FinalCount.Src.HyperLikeRealization.lift {M : Molecule V D} {S : Finset V} {a b : V} (R : Src.HyperLikeRealization Src.γL M.unloop S a b)
    (h : LoopFreeSet M S) : Src.HyperLikeRealization Src.γL M S a b where
  added := R.added.1
  ends_eq := R.ends_eq
  adjoint := ((eraseUnloopEmb M R.added h).isVC_iffL rfl).2 R.adjoint

def _root_.WaveTurbulence.GammaLow.FinalCount.Src.VineLikeObject.unloop {M : Molecule V D} {S : Finset V} {a b : V} (P : Src.VineLikeObject Src.γL M S a b)
    (h : LoopFreeSet M S) : Src.VineLikeObject Src.γL M.unloop S a b :=
  match P with
  | .vc hv => .vc (((unloopEmb M h).isVC_iffL rfl).1 hv)
  | .hyper R => .hyper (R.unloop h)

def _root_.WaveTurbulence.GammaLow.FinalCount.Src.VineLikeObject.lift {M : Molecule V D} {S : Finset V} {a b : V} (P : Src.VineLikeObject Src.γL M.unloop S a b)
    (h : LoopFreeSet M S) : Src.VineLikeObject Src.γL M S a b :=
  match P with
  | .vc hv => .vc (((unloopEmb M h).isVC_iffL rfl).2 hv)
  | .hyper R => .hyper (R.lift h)

def _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.unloop {M : Molecule V D} (P : Src.Object Src.γL M) (h : LoopFreeSet M P.atoms) : Src.Object Src.γL M.unloop :=
  ⟨P.atoms, P.upper, P.lower, P.shape.unloop h⟩

def _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.lift {M : Molecule V D} (P : Src.Object Src.γL M.unloop) (h : LoopFreeSet M P.atoms) : Src.Object Src.γL M :=
  ⟨P.atoms, P.upper, P.lower, P.shape.lift h⟩

theorem _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.unloop_atoms {M : Molecule V D} (P : Src.Object Src.γL M) (h : LoopFreeSet M P.atoms) : (P.unloop h).atoms = P.atoms := rfl
theorem _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.lift_atoms {M : Molecule V D} (P : Src.Object Src.γL M.unloop) (h : LoopFreeSet M P.atoms) : (P.lift h).atoms = P.atoms := rfl

theorem _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.unloop_containsDart {M : Molecule V D} (P : Src.Object Src.γL M) (h : LoopFreeSet M P.atoms) (x : NonLoop M) :
    (P.unloop h).ContainsDart x ↔ P.ContainsDart x.1 := by
  obtain ⟨S, a, b, sh⟩ := P
  cases sh with
  | vc hv => exact Iff.rfl
  | hyper R =>
    unfold Src.Object.ContainsDart
    simp only [Src.Object.unloop, Src.VineLikeObject.unloop, Src.HyperLikeRealization.unloop]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun e => h1 (Subtype.ext e), fun e => h2 (Subtype.ext e), h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun e => h1 (congrArg Subtype.val e), fun e => h2 (congrArg Subtype.val e), h3⟩

theorem _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.lift_containsDart {M : Molecule V D} (P : Src.Object Src.γL M.unloop) (h : LoopFreeSet M P.atoms) (x : NonLoop M) :
    (P.lift h).ContainsDart x.1 ↔ P.ContainsDart x := by
  obtain ⟨S, a, b, sh⟩ := P
  cases sh with
  | vc hv => exact Iff.rfl
  | hyper R =>
    unfold Src.Object.ContainsDart
    simp only [Src.Object.lift, Src.VineLikeObject.lift, Src.HyperLikeRealization.lift]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun e => h1 (congrArg Subtype.val e), fun e => h2 (congrArg Subtype.val e), h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun e => h1 (Subtype.ext e), fun e => h2 (Subtype.ext e), h3⟩

theorem _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.unloop_hasGapKind {M : Molecule V D} (P : Src.Object Src.γL M) (h : LoopFreeSet M P.atoms) (L γ η : ℝ) (w : Mom d)
    (κ : D → Fin d → ℤ) (kind : Molecule.GapKind) :
    (P.unloop h).HasGapKind L γ η w (fun x : NonLoop M => κ x.1) kind ↔ P.HasGapKind L γ η w κ kind := by
  obtain ⟨S, a, b, sh⟩ := P
  cases sh with
  | vc hv =>
    unfold Src.Object.HasGapKind
    simp only [Src.Object.unloop, Src.VineLikeObject.unloop, Src.VineLikeObject.IsGap]
    simp only [(unloopEmb M h).isBlockGap_iff L w κ a]
  | hyper R =>
    unfold Src.Object.HasGapKind
    simp only [Src.Object.unloop, Src.VineLikeObject.unloop, Src.VineLikeObject.IsGap, Src.HyperLikeRealization.IsGap,
      Src.HyperLikeRealization.unloop]
    simp only [(eraseUnloopEmb M ⟨R.added, hyper_added_nonloop R⟩ h).isBlockGap_iff L w (fun x => κ x.1) a]
    rfl

theorem _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.lift_hasGapKind {M : Molecule V D} (P : Src.Object Src.γL M.unloop) (h : LoopFreeSet M P.atoms) (L γ η : ℝ) (w : Mom d)
    (κ : D → Fin d → ℤ) (kind : Molecule.GapKind) :
    (P.lift h).HasGapKind L γ η w κ kind ↔ P.HasGapKind L γ η w (fun x : NonLoop M => κ x.1) kind := by
  obtain ⟨S, a, b, sh⟩ := P
  cases sh with
  | vc hv =>
    unfold Src.Object.HasGapKind
    simp only [Src.Object.lift, Src.VineLikeObject.lift, Src.VineLikeObject.IsGap]
    simp only [(unloopEmb M h).isBlockGap_iff L w κ a]
  | hyper R =>
    unfold Src.Object.HasGapKind
    simp only [Src.Object.lift, Src.VineLikeObject.lift, Src.VineLikeObject.IsGap, Src.HyperLikeRealization.IsGap,
      Src.HyperLikeRealization.lift]
    simp only [(eraseUnloopEmb M R.added h).isBlockGap_iff L w (fun x => κ x.1) a]
    rfl

/-- Every object of `M` is loop-free (vines have no loops). -/
theorem _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.loopFree {M : Molecule V D} (P : Src.Object Src.γL M) : LoopFreeSet M P.atoms := by
  obtain ⟨S, a, b, sh⟩ := P
  cases sh with
  | vc hv => exact isVC_noLoop hv
  | hyper R =>
    intro y hy hloop
    have hN := isVC_noLoop R.adjoint
    have hne : y ≠ R.added ∧ y ≠ M.mate R.added := by
      constructor
      · rintro rfl; exact ends_ne_of R.adjoint.1.2.2.2.1 R.ends_eq hloop
      · intro e
        rw [e, M.mate_mate] at hloop
        exact ends_ne_of R.adjoint.1.2.2.2.1 R.ends_eq hloop.symm
    exact hN ⟨y, hne⟩ hy hloop

end WaveTurbulence.GammaLow.FinalCount.H
