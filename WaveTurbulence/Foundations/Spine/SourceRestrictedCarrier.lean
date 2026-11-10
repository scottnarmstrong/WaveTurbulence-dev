/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import WaveTurbulence.Foundations.Spine.SourcePairsCompatible
/-! R6(b): the restricted carrier of the second collection, compared with the conclusion of
TARGET subpro(4) as recorded in `SubproSupport.contained`.

TARGET L2101–L2112: the candidates of `C_2` are the SG vine-like objects of `M_sb` covered by
subpro(4): SG, not contained in an object of `C_1`, disjoint from the hinges, and contained in a DV
or in an LG/ZG vine-like object, where the DV / container is disjoint from the hinges and from
every object of `C_1`. `eligibleSecondObject G L γ η base κ F` with `F = C.forbidden` is exactly
that predicate (the explicit conditions "outside `C_1`" and "disjoint from the hinges" follow from
the container conditions because an object has a joint in its atom set). -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open SourceVine Finset

variable {w d : ℕ}

/-- TARGET L2116, second half (`C_2` side): no hinge atom lies in any object of the (canonical,
restricted) second collection, in particular no hinge is interior to one. This is derived from the
restricted carrier, not assumed. -/
theorem hinge_not_in_second {G : Garden w} (C : CountingChoices G d) (L γ η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (h : C.SecondCollectionOK L γ η base κ) :
    ∀ v ∈ C.subpro.hinges, ∀ P ∈ C.secondCollection, v ∉ P.atoms := by
  obtain ⟨rk, _, K, hK, hC⟩ := h
  intro v hv P hP hvP
  rw [hC] at hP
  have hdis := eligible_atoms_disjoint ((hK.2.2 P).mp hP.1).1
  exact Set.disjoint_left.mp hdis (Finset.mem_coe.mpr hvP) (Or.inl (Finset.mem_coe.mpr hv))

theorem hingeOutsideSecond_of_secondCollectionOK {G : Garden w} (C : CountingChoices G d)
    (L γ η : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (h : C.SecondCollectionOK L γ η base κ) :
    ∀ v ∈ C.subpro.hinges, ∀ P ∈ C.secondCollection, ¬ P.IsInterior v :=
  fun v hv P hP hi => hinge_not_in_second C L γ η base κ h v hv P hP hi.1

end WaveTurbulence.LGSpine
