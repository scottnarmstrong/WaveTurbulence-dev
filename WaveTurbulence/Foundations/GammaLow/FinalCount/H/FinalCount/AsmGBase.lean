/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGarden3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproC2Second
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmGBase`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (garden level): base independence of the pool notions, the tame shift, and `hnc`.**

* `inP_base_eq`, `c2Of_base_eq`, `c2Can_base_eq`, `unselOK_base_iff`, `collected_base_iff`, `unselOf_base_eq`: G3's pool, `C₂`,
  `UnselOK` and the asm's `Collected` do not depend on the base (they are defined through gap kinds, which are base independent).
* `isTame_shift`: `IsTame` at base `w` with the fixed vectors `kFix` is `IsTame` at base `0` with `kFix.image (· - w)` (the class
  theorem runs at base `0`).
* `eligible_of_pool`: with LG-SPINE AMEND5's atom-level eligibility every pool member is an eligible second object; hence
  `not_critical_of_interior_c2'`: interior atoms of members of `C₂` are not critical, with no hypothesis (`hnc` of S4-DISJ). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Subpro

section generic
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}
variable {M : Molecule V D} (C : CollData M) (L γ η : ℝ) (w w' : Mom d) (κ : D → (Fin d → ℤ))

theorem host_base_indep (P : Src.Object Src.γL M) : C.Host L γ η w κ P ↔ C.Host L γ η w' κ P := by
  unfold CollData.Host
  simp only [object_hasGapKind_base_indep _ L γ η w w' κ]

theorem inP_base_eq : C.InP L γ η w κ = C.InP L γ η w' κ := by
  funext P
  apply propext
  unfold CollData.InP
  rw [object_hasGapKind_base_indep P L γ η w w' κ, host_base_indep C L γ η w w' κ P]

theorem c2Of_base_eq (Unsel : Set (Src.Object Src.γL M)) : C.C2Of L γ η w κ Unsel = C.C2Of L γ η w' κ Unsel := by
  unfold CollData.C2Of
  rw [inP_base_eq C L γ η w w' κ]

theorem c2Can_base_eq (Unsel : Set (Src.Object Src.γL M)) : C.C2Can L γ η w κ Unsel = C.C2Can L γ η w' κ Unsel := by
  unfold CollData.C2Can
  rw [c2Of_base_eq C L γ η w w' κ]

theorem unselOK_base_iff (Unsel : Set (Src.Object Src.γL M)) : C.UnselOK L γ η w κ Unsel ↔ C.UnselOK L γ η w' κ Unsel := by
  constructor
  · rintro ⟨h⟩
    rw [inP_base_eq C L γ η w w' κ, c2Can_base_eq C L γ η w w' κ] at h
    exact ⟨h⟩
  · rintro ⟨h⟩
    rw [inP_base_eq C L γ η w' w κ, c2Can_base_eq C L γ η w' w κ] at h
    exact ⟨h⟩

theorem collected_base_iff (Un : Set (Src.Object Src.γL M)) (U : Src.Object Src.γL M) :
    Collected C Un L γ η w κ U ↔ Collected C Un L γ η w' κ U := by
  unfold Collected
  rw [c2Can_base_eq C L γ η w w' κ]

/-- **The tame shift.** -/
theorem isTame_shift (M : Molecule V D) (L : ℝ) (w : Mom d) (kFix : Finset (Mom d)) (κ : D → (Fin d → ℤ)) (v : V) :
    M.IsTame L w kFix κ v ↔ M.IsTame L 0 (kFix.image (fun k => k - w)) κ v := by
  unfold Molecule.IsTame Molecule.kvec
  refine and_congr ⟨fun h x₁ x₂ h1 h2 => ?_, fun h x₁ x₂ h1 h2 => ?_⟩ ⟨fun h hd x hx => ?_, fun h hd x hx => ?_⟩
  · have := h x₁ x₂ h1 h2
    simpa using this
  · have := h x₁ x₂ h1 h2
    simp only [zero_add] at this
    rw [this]
  · refine Finset.mem_image.mpr ⟨_, h hd x hx, ?_⟩
    simp
  · obtain ⟨k, hk, hk'⟩ := Finset.mem_image.mp (h hd x hx)
    have : k = w + latticePoint L (κ x) := by
      rw [zero_add] at hk'
      rw [← hk']; abel
    rw [← this]; exact hk

end generic

section garden
variable {w d : ℕ} {G : Garden w}

theorem unselOf_base_eq (C : CollData G.molecule) (L γ η : ℝ) (b b' : Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (omitted : Set (Finset (GBranch G.tree))) : unselOf C L γ η b κ omitted = unselOf C L γ η b' κ omitted := by
  unfold unselOf
  rw [inP_base_eq C L γ η b b' κ]

/-- **`hnc` (R42 / AMEND5).** Every pool member (of either shape) is an eligible second object. -/
theorem eligible_of_pool (C : CollData G.molecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {U : Src.Object Src.γL G.molecule} (hU : C.InP L γ η base κ U) :
    Src.eligibleSecondObject Src.γL G L γ η base κ (forbiddenOf C) U := by
  obtain ⟨hsg, _, _, hhost⟩ := hU
  refine ⟨hsg, ?_⟩
  rcases hhost with ⟨S, a, b, hDV, hsub, hSh, hSC⟩ | ⟨Q, hsub, hQk, hQh, hQC⟩
  · obtain ⟨hσ, A, B, hA, hB, hAB, rfl⟩ := hDV
    exact Or.inr ⟨⟨A, B, a, b, hσ, hA, hB, hAB⟩, hsub, (disjoint_forbiddenOf_iff C _).mpr ⟨hSh, hSC⟩⟩
  · exact Or.inl ⟨Q, hsub, hQk, (disjoint_forbiddenOf_iff C _).mpr ⟨hQh, hQC⟩⟩

/-- Interior atoms of members of `C₂` are not critical (no `hnc` hypothesis). -/
theorem not_critical_of_interior_c2' (Cc : Src.CountingChoices Src.γL G d) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} (hSC : Cc.SecondCollectionOK L γ η base κ) {U : Src.Object Src.γL G.molecule}
    (hU : U ∈ (collDataOf Cc.subpro).C2Of L γ η base κ
      (unselOf (collDataOf Cc.subpro) L γ η base κ Cc.omittedDVConstituents)) {v : GBranch G.tree}
    (hv : U.IsInterior v) : ¬ Cc.CriticalSG v :=
  not_critical_of_interior_c2 Cc hSC hU hv (fun _ => eligible_of_pool (collDataOf Cc.subpro) hU.1.1)

end garden

end WaveTurbulence.GammaLow.FinalCount.H
