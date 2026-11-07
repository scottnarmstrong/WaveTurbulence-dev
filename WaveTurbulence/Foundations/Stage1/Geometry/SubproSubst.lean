/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.SubproObjMap
public import WaveTurbulence.Foundations.FinalCount.RedSpliceTriple
public import WaveTurbulence.Foundations.FinalCount.RedSpliceResidual
import Mathlib.Tactic

/-!
# SUBPRO (S4): a general substitution isomorphism for a splice

`exists_iso_subst`: the induced subgraph of a molecule `N'` (the molecule of `G` or an adjoint of it, embedded in the
darts of `G` by `ι`) on an atom set `P` is isomorphic, via the dart map `od` of an `SpMap`, to the induced subgraph of the
molecule of `G0` on `P.image j`, provided the atom map `j` is compatible with `od` on the darts inside `P` (R2) and every
dart inside the image comes from one inside `P` (R3).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole SpMap

variable {w : ℕ} {G0 G : Garden w} {cls : GBranch G0.tree → Option (GBranch G0.tree)}

theorem exists_iso_subst (M : SpMap G0 G cls) {D' : Type*} [Fintype D'] [DecidableEq D']
    (N' : Molecule (GBranch G.tree) D') (ι : D' → GardenDart G) (hι : Function.Injective ι)
    (hι_atom : ∀ x, G.molecule.atom (ι x) = N'.atom x)
    (hι_mate : ∀ x, ι (N'.mate x) = G.molecule.mate (ι x))
    (hι_out : ∀ x, G.molecule.out (ι x) = N'.out x)
    (P : Finset (GBranch G.tree)) (j : GBranch G.tree → GBranch G0.tree) (hj : Set.InjOn j P)
    (hR2 : ∀ x, N'.InGroup P x → G0.molecule.atom (M.od (ι x)) = j (N'.atom x))
    (hR3 : ∀ y, G0.molecule.InGroup (P.image j) y → ∃ x, N'.InGroup P x ∧ M.od (ι x) = y) :
    ∃ I : InducedIso N' G0.molecule P (P.image j), I.π = j := by
  classical
  have hfwd : ∀ x : {x : D' // N'.InGroup P x}, G0.molecule.InGroup (P.image j) (M.od (ι x.1)) := by
    intro x
    refine ⟨?_, ?_⟩
    · rw [hR2 _ x.2]; exact Finset.mem_image_of_mem _ x.2.1
    · rw [← M.od_mate, ← hι_mate, hR2 _ ⟨x.2.2, by simpa [N'.mate_mate] using x.2.1⟩]
      exact Finset.mem_image_of_mem _ x.2.2
  refine ⟨
    { π := j
      inj := hj
      img := rfl
      sub := fun _ _ => Finset.mem_univ _
      e :=
        { toFun := fun x => ⟨M.od (ι x.1), hfwd x⟩
          invFun := fun y => ⟨(hR3 y.1 y.2).choose, (hR3 y.1 y.2).choose_spec.1⟩
          left_inv := fun x => by
            apply Subtype.ext
            have h := (hR3 (M.od (ι x.1)) (hfwd x)).choose_spec.2
            exact hι (M.od_inj h)
          right_inv := fun y => Subtype.ext (hR3 y.1 y.2).choose_spec.2 }
      atom_comm := fun x => hR2 x.1 x.2
      mate_comm := fun x => by
        show M.od (ι (N'.mate x.1)) = G0.molecule.mate (M.od (ι x.1))
        rw [hι_mate, M.od_mate]
      out_comm := fun x => by
        show G0.molecule.out (M.od (ι x.1)) = N'.out x.1
        rw [← hι_out, M.od_out] }, rfl⟩

end WaveTurbulence.RedSplice
