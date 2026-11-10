/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL22
/-! **G3-LOWDEG (R48), part 23: `Object.unloop` / `Object.lift`.** -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem hyper_added_nonloop {M : Molecule V D} {S : Finset V} {a b : V} (R : HyperLikeRealization M S a b) :
    M.atom R.added ≠ M.atom (M.mate R.added) := ends_ne_of R.adjoint.1.2.2.2.1 R.ends_eq

def _root_.WaveTurbulence.LGSpine.SourceVine.HyperLikeRealization.unloop {M : Molecule V D} {S : Finset V} {a b : V} (R : HyperLikeRealization M S a b)
    (h : LoopFreeSet M S) : HyperLikeRealization M.unloop S a b where
  added := ⟨R.added, hyper_added_nonloop R⟩
  ends_eq := R.ends_eq
  adjoint := ((eraseUnloopEmb M ⟨R.added, hyper_added_nonloop R⟩ h).isVC_iff rfl).1 R.adjoint

def _root_.WaveTurbulence.LGSpine.SourceVine.HyperLikeRealization.lift {M : Molecule V D} {S : Finset V} {a b : V} (R : HyperLikeRealization M.unloop S a b)
    (h : LoopFreeSet M S) : HyperLikeRealization M S a b where
  added := R.added.1
  ends_eq := R.ends_eq
  adjoint := ((eraseUnloopEmb M R.added h).isVC_iff rfl).2 R.adjoint

def _root_.WaveTurbulence.LGSpine.SourceVine.VineLikeObject.unloop {M : Molecule V D} {S : Finset V} {a b : V} (P : VineLikeObject M S a b)
    (h : LoopFreeSet M S) : VineLikeObject M.unloop S a b :=
  match P with
  | .vc hv => .vc (((unloopEmb M h).isVC_iff rfl).1 hv)
  | .hyper R => .hyper (R.unloop h)

def _root_.WaveTurbulence.LGSpine.SourceVine.VineLikeObject.lift {M : Molecule V D} {S : Finset V} {a b : V} (P : VineLikeObject M.unloop S a b)
    (h : LoopFreeSet M S) : VineLikeObject M S a b :=
  match P with
  | .vc hv => .vc (((unloopEmb M h).isVC_iff rfl).2 hv)
  | .hyper R => .hyper (R.lift h)

def _root_.WaveTurbulence.LGSpine.SourceVine.Object.unloop {M : Molecule V D} (P : Object M) (h : LoopFreeSet M P.atoms) : Object M.unloop :=
  ⟨P.atoms, P.upper, P.lower, P.shape.unloop h⟩

def _root_.WaveTurbulence.LGSpine.SourceVine.Object.lift {M : Molecule V D} (P : Object M.unloop) (h : LoopFreeSet M P.atoms) : Object M :=
  ⟨P.atoms, P.upper, P.lower, P.shape.lift h⟩

theorem _root_.WaveTurbulence.LGSpine.SourceVine.Object.unloop_containsDart {M : Molecule V D} (P : Object M) (h : LoopFreeSet M P.atoms) (x : NonLoop M) :
    (P.unloop h).ContainsDart x ↔ P.ContainsDart x.1 := by
  obtain ⟨S, a, b, sh⟩ := P
  cases sh with
  | vc hv => exact Iff.rfl
  | hyper R =>
    unfold Object.ContainsDart
    simp only [Object.unloop, VineLikeObject.unloop, HyperLikeRealization.unloop]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun e => h1 (Subtype.ext e), fun e => h2 (Subtype.ext e), h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun e => h1 (congrArg Subtype.val e), fun e => h2 (congrArg Subtype.val e), h3⟩

theorem _root_.WaveTurbulence.LGSpine.SourceVine.Object.lift_containsDart {M : Molecule V D} (P : Object M.unloop) (h : LoopFreeSet M P.atoms) (x : NonLoop M) :
    (P.lift h).ContainsDart x.1 ↔ P.ContainsDart x := by
  obtain ⟨S, a, b, sh⟩ := P
  cases sh with
  | vc hv => exact Iff.rfl
  | hyper R =>
    unfold Object.ContainsDart
    simp only [Object.lift, VineLikeObject.lift, HyperLikeRealization.lift]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun e => h1 (congrArg Subtype.val e), fun e => h2 (congrArg Subtype.val e), h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun e => h1 (Subtype.ext e), fun e => h2 (Subtype.ext e), h3⟩

theorem _root_.WaveTurbulence.LGSpine.SourceVine.Object.unloop_hasGapKind {M : Molecule V D} (P : Object M) (h : LoopFreeSet M P.atoms) (L γ η : ℝ) (w : Mom d)
    (κ : D → Fin d → ℤ) (kind : Molecule.GapKind) :
    (P.unloop h).HasGapKind L γ η w (fun x : NonLoop M => κ x.1) kind ↔ P.HasGapKind L γ η w κ kind := by
  obtain ⟨S, a, b, sh⟩ := P
  cases sh with
  | vc hv =>
    unfold Object.HasGapKind
    simp only [Object.unloop, VineLikeObject.unloop, VineLikeObject.IsGap]
    simp only [(unloopEmb M h).isBlockGap_iff L w κ a]
  | hyper R =>
    unfold Object.HasGapKind
    simp only [Object.unloop, VineLikeObject.unloop, VineLikeObject.IsGap, HyperLikeRealization.IsGap,
      HyperLikeRealization.unloop]
    simp only [(eraseUnloopEmb M ⟨R.added, hyper_added_nonloop R⟩ h).isBlockGap_iff L w (fun x => κ x.1) a]
    rfl

theorem _root_.WaveTurbulence.LGSpine.SourceVine.Object.lift_hasGapKind {M : Molecule V D} (P : Object M.unloop) (h : LoopFreeSet M P.atoms) (L γ η : ℝ) (w : Mom d)
    (κ : D → Fin d → ℤ) (kind : Molecule.GapKind) :
    (P.lift h).HasGapKind L γ η w κ kind ↔ P.HasGapKind L γ η w (fun x : NonLoop M => κ x.1) kind := by
  obtain ⟨S, a, b, sh⟩ := P
  cases sh with
  | vc hv =>
    unfold Object.HasGapKind
    simp only [Object.lift, VineLikeObject.lift, VineLikeObject.IsGap]
    simp only [(unloopEmb M h).isBlockGap_iff L w κ a]
  | hyper R =>
    unfold Object.HasGapKind
    simp only [Object.lift, VineLikeObject.lift, VineLikeObject.IsGap, HyperLikeRealization.IsGap,
      HyperLikeRealization.lift]
    simp only [(eraseUnloopEmb M R.added h).isBlockGap_iff L w (fun x => κ x.1) a]
    rfl

/-- Every object of `M` is loop-free (vines have no loops). -/
theorem _root_.WaveTurbulence.LGSpine.SourceVine.Object.loopFree {M : Molecule V D} (P : Object M) : LoopFreeSet M P.atoms := by
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

end WaveTurbulence.FinalCountG3
