/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapIncidenceRealization
public import WaveTurbulence.Foundations.Molecule.VineCapAdjointRecognition
public import WaveTurbulence.Foundations.Molecule.VineCapShortAdjoints
import Mathlib.Tactic

/-! # Exact classification of hyper-vine-like objects with primitive cap data

The r=1,2 exclusion uses the current pinned B2 vine family. The incidence,
label and graph reconstruction theorems remain valid in these cases (F69).
-/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace CapPrefixData
variable {M : Molecule V D} {A : Finset V} {n r : ℕ} (C : CapPrefixData M A n r)

include C in
/-- A cap with at least three full rungs has a type-V designated adjoint.
The complete graph realization is reconstructed from the actual dart rows. -/
theorem long_adjoint_isVineV (hM : M.IsMolecule) {x y : V}
    (hH : Mole.IsHyperBlock M A x y) (e : D) (he : M.ends e=s(x,y))
    (hB : (Mole.eraseBond M e).IsBlock A x y) (hr : 3 ≤ r) :
    (Mole.eraseBond M e).IsVine .V A x y := by
  let m := r-3
  have heq : r=(m+2)+1 := by dsimp [m]; omega
  apply cap_adjoint_isVineV_of_realization e he hB 9 m (by decide) C.label C.label_injOn
  · simpa only [← heq] using C.label_image
  · have hj := C.hyper_front_labels_pos hM hH (by omega)
    have hu : 9+(r-1)=9+(m+2) := by omega
    have hv : 9+r+(r-1)=9+((m+2)+1)+(m+2) := by omega
    rw [hu,hv] at hj
    exact hj
  · simpa only [← heq] using C.bonds_eq hM

include C in
/-- TARGET subsetvc's cap classification: an HV/HVC with these actual
primitive incidences has a designated adjoint which is two double bonds or
Vine V. The short-case exclusion is relative to the current B2 family (F69). -/
theorem hyperLike_adjoint_classification (hM : M.IsMolecule) {x y : V}
    (h : IsHV M A x y ∨ IsHVC M A x y) :
    ∃ e : D,M.ends e=s(x,y) ∧
      (DoubleChain (Mole.eraseBond M e) A x y 2 ∨ (Mole.eraseBond M e).IsVine .V A x y) := by
  by_cases hr0 : r=0
  · obtain ⟨e,he,hD⟩ := C.zero_prefix_adjoint_doubleChain h hr0
    exact ⟨e,he,Or.inl hD⟩
  · by_cases hshort : r=1 ∨ r=2
    · exact False.elim (C.short_prefix_not_hyperLike hM hshort h)
    · obtain ⟨e,he,hVC⟩ := hyperLike_iff_adjoint_VC.mp h
      have hH : Mole.IsHyperBlock M A x y := ⟨e,he,hVC.1⟩
      exact ⟨e,he,Or.inr (C.long_adjoint_isVineV hM hH e he hVC.1 (by omega))⟩

end CapPrefixData
end WaveTurbulence.Vine
