/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.SubproC2Second
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproC2Disj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCanonicalDesignation
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.SubproC2Second`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# S4-DISJ goal 2: `C₂` against the counting problem's `secondCollection`; interior atoms of removed objects are not critical

`CriticalSG v` (lg-spine `CountingChoices.CriticalSG`, TARGET L2101 requirement (f): "each SG atom `v` which is not an interior atom of an
SG vine-like object in `C₁` or `C₂`") asks that `v` is interior to no member of `C₁` and to no member of `secondCollection =
canonicalSub rk K`. For an ordinary member `U` of G3's `C₂`: `U ∈ secondCollection`. For a hyper member: `U` is covered by a member of
`K` (hence by one of `secondCollection`) unless `U` is not an eligible object of lg-spine (the designation corner of PORT-LOG item 5).
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCountG3 Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Interior atoms of an object have internal degree four. -/
theorem degIn_interior_object {M : Molecule V D} (U : Src.Object Src.γL M) {v : V} (hv : U.IsInterior v) :
    M.degIn U.atoms v = 4 := by
  obtain ⟨hvS, hva, hvb⟩ := hv
  rcases U with ⟨S, a, b, sh⟩
  cases sh with
  | vc h => exact h.1.2.2.2.2.2.2.2.2.1 v hvS hva hvb
  | hyper R =>
    exact (Mole.hyperBlock_degrees M ⟨R.added, R.ends_eq, R.adjoint.1⟩).2.2 v hvS hva hvb

/-- Joints of an object have internal degree at most three. -/
theorem degIn_joint_object_le {M : Molecule V D} (Q : Src.Object Src.γL M) {v : V} (hv : v = Q.upper ∨ v = Q.lower) :
    M.degIn Q.atoms v ≤ 3 := by
  rcases object_shape_cases Q with h | h
  · rw [object_vc_degIn Q h hv]; omega
  · rw [object_hyper_degIn Q h hv]

/-- An interior atom of an object stays interior in every object whose atom set contains it. -/
theorem interior_of_contained {M : Molecule V D} {U Q : Src.Object Src.γL M} (hsub : U.atoms ⊆ Q.atoms) {v : V}
    (hv : U.IsInterior v) : Q.IsInterior v := by
  have h4 := degIn_interior_object U hv
  have hle := Mole.degIn_mono M hsub v
  refine ⟨hsub hv.1, fun h => ?_, fun h => ?_⟩
  · have := degIn_joint_object_le Q (Or.inl h); omega
  · have := degIn_joint_object_le Q (Or.inr h); omega

variable {w d : ℕ}

/-- **S4-DISJ goal 2, inclusion for ordinary members.** -/
theorem c2Of_vc_mem_secondCollection {G : Garden w} (Cc : Src.CountingChoices Src.γL G d) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} (hSC : Cc.SecondCollectionOK L γ η base κ) {U : Src.Object Src.γL G.molecule}
    (hU : U ∈ (collDataOf Cc.subpro).C2Of L γ η base κ
      (unselOf (collDataOf Cc.subpro) L γ η base κ Cc.omittedDVConstituents))
    (hvc : ∃ h, U.shape = .vc h) : U ∈ Cc.secondCollection := by
  obtain ⟨rk, hrk, K, hK, hsec⟩ := hSC
  have hmem : U ∈ K := c2Of_vc_mem_collection (collDataOf Cc.subpro) hK hU hvc
  rw [hsec]
  refine ⟨hmem, fun Q _ _ hh _ => ?_⟩
  obtain ⟨R, hR⟩ := hh
  obtain ⟨h, hs⟩ := hvc
  rw [hs] at hR
  cases hR

/-- **S4-DISJ goal 2, interior atoms.** An interior atom `v` of a member `U` of `C₂` is interior to a member of
`secondCollection`, hence not critical, except possibly when `U` is of hyper shape and is not an eligible object of lg-spine's
second collection (G3's pool is atom-level, lg-spine's eligibility is designation-level: PORT-LOG item 5). -/
theorem c2Of_interior_covered {G : Garden w} (Cc : Src.CountingChoices Src.γL G d) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} (hSC : Cc.SecondCollectionOK L γ η base κ) {U : Src.Object Src.γL G.molecule}
    (hU : U ∈ (collDataOf Cc.subpro).C2Of L γ η base κ
      (unselOf (collDataOf Cc.subpro) L γ η base κ Cc.omittedDVConstituents)) {v : GBranch G.tree}
    (hv : U.IsInterior v) :
    (∃ P ∈ Cc.secondCollection, P.IsInterior v) ∨
      ((∃ R, U.shape = .hyper R) ∧ ¬ Src.eligibleSecondObject Src.γL G L γ η base κ Cc.subpro.forbidden U) := by
  by_cases hvc : ∃ h, U.shape = .vc h
  · exact Or.inl ⟨U, c2Of_vc_mem_secondCollection Cc hSC hU hvc, hv⟩
  have hhyp : ∃ R, U.shape = .hyper R := (object_shape_cases U).resolve_left hvc
  by_cases hel : Src.eligibleSecondObject Src.γL G L γ η base κ Cc.subpro.forbidden U
  · left
    obtain ⟨rk, hrk, K, hK, hsec⟩ := hSC
    have hno : U.atoms ∉ Cc.omittedDVConstituents := fun h => hU.1.2 ⟨hU.1.1, h⟩
    obtain ⟨Q, hQK, hUQ⟩ := source_secondCollection_covers G L γ η base κ _ _ K hK U hel hno
    obtain ⟨Q', hQ'mem, hQ'at, _⟩ := canonicalSub_covers rk K Q hQK
    refine ⟨Q', hsec ▸ hQ'mem, interior_of_contained ?_ hv⟩
    rw [hQ'at]
    exact Src.Object.contained_atoms_subset U Q hUQ
  · exact Or.inr ⟨hhyp, hel⟩

/-- Interior atoms of the members of `C₁` are not critical. -/
theorem not_critical_of_interior_c1 {G : Garden w} (Cc : Src.CountingChoices Src.γL G d) {v : GBranch G.tree} {i : Fin Cc.subpro.count}
    (hv : (Cc.subpro.collection i).IsInterior v) : ¬ Cc.CriticalSG v :=
  fun h => h.2.1 i hv

/-- Interior atoms of the (non-corner) members of `C₂` are not critical. -/
theorem not_critical_of_interior_c2 {G : Garden w} (Cc : Src.CountingChoices Src.γL G d) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} (hSC : Cc.SecondCollectionOK L γ η base κ) {U : Src.Object Src.γL G.molecule}
    (hU : U ∈ (collDataOf Cc.subpro).C2Of L γ η base κ
      (unselOf (collDataOf Cc.subpro) L γ η base κ Cc.omittedDVConstituents)) {v : GBranch G.tree}
    (hv : U.IsInterior v)
    (hnc : (∃ R, U.shape = .hyper R) → Src.eligibleSecondObject Src.γL G L γ η base κ Cc.subpro.forbidden U) :
    ¬ Cc.CriticalSG v := by
  intro hcrit
  rcases c2Of_interior_covered Cc hSC hU hv with ⟨P, hP, hPi⟩ | ⟨hh, hne⟩
  · exact hcrit.2.2 P hP hPi
  · exact hne (hnc hh)

end WaveTurbulence.GammaLow.FinalCount.H
