/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Low
/-! # Recasting the counting choices within the low range (packet L6, item H/I)

For `γ, γ' ≤ 1/2`, `CountingChoices.recast` maps the `𝒱_γ` counting choices of a garden to the `𝒱_{γ'}` ones (objects
recast, all other data unchanged), and transports `CountingGeometry` and `splicedCountingAdmissible`
(`countingGeometry_recast`, `splicedCountingAdmissible_recast`); `ladderScale`, `subpro.hinges` and `numCriticalSG` are
unchanged. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.Src
open Finset
open WaveTurbulence.LGSpine
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale)

variable {w d : ℕ} {γ γ' : ℝ} (hγ : γ ≤ 1 / 2) (hγ' : γ' ≤ 1 / 2)

section recast
variable {G : Garden w}

/-- Recast of the subpro choices. -/
def SubproChoices.recast (C : SubproChoices γ G) : SubproChoices γ' G :=
  ⟨C.count, fun i => (C.collection i).recast hγ hγ', C.hinges, C.first, C.second⟩

/-- Recast of the counting choices. -/
def CountingChoices.recast (C : CountingChoices γ G d) : CountingChoices γ' G d where
  subpro := C.subpro.recast hγ hγ'
  secondCollection := Object.recast hγ hγ' '' C.secondCollection
  omittedDVConstituents := C.omittedDVConstituents
  atomLabel := C.atomLabel
  first := C.first
  second := C.second
  atomScale := C.atomScale
  ladderScale := C.ladderScale
  fixedRoots := C.fixedRoots

/-- Recast of the constituents of a `DV′`. -/
def DoubleVine.recast (D : DoubleVine γ G) : DoubleVine γ' G :=
  ⟨D.first, D.second, D.upper, D.lower, D.sigma_one, isSomeVine_recast hγ hγ' D.first_vine,
    isSomeVine_recast hγ hγ' D.second_vine, D.overlap⟩

theorem mem_recast_image {K : Set (Object γ G.molecule)} {P : Object γ' G.molecule} :
    P ∈ Object.recast hγ hγ' '' K ↔ P.recast hγ' hγ ∈ K := by
  constructor
  · rintro ⟨Q, hQ, rfl⟩; rwa [Object.recast_recast]
  · intro h; exact ⟨P.recast hγ' hγ, h, Object.recast_recast hγ' hγ P⟩

theorem hyperRank_recast {M : Molecule (GBranch G.tree) (GardenDart G)} (rk : GardenDart G → ℕ)
    (U : Object γ M) : (U.recast hγ hγ').hyperRank rk = U.hyperRank rk := by
  obtain ⟨A, a, b, sh⟩ := U
  cases sh <;> rfl

theorem isShapeHyper_recast {M : Molecule (GBranch G.tree) (GardenDart G)} (U : Object γ M) :
    (∃ R, (U.recast hγ hγ').shape = .hyper R) ↔ ∃ R, U.shape = .hyper R := by
  obtain ⟨A, a, b, sh⟩ := U
  cases sh with
  | vc h =>
    constructor
    · rintro ⟨R, hR⟩; simp [Object.recast, VineLikeObject.recast] at hR
    · rintro ⟨R, hR⟩; simp at hR
  | hyper R => exact ⟨fun _ => ⟨R, rfl⟩, fun _ => ⟨R.recast hγ hγ', rfl⟩⟩

theorem canonicalSub_recast (rk : GardenDart G → ℕ) (K : Set (Object γ G.molecule)) :
    canonicalSub rk (Object.recast hγ hγ' '' K) = Object.recast hγ hγ' '' canonicalSub rk K := by
  ext P
  rw [mem_recast_image hγ hγ']
  simp only [canonicalSub, Set.mem_setOf_eq]
  rw [mem_recast_image hγ hγ']
  constructor
  · rintro ⟨hP, hQ⟩
    refine ⟨hP, fun Q hQK hQa hPh hQh => ?_⟩
    have := hQ (Q.recast hγ hγ') ((mem_recast_image hγ hγ').mpr (by rwa [Object.recast_recast]))
      (by simpa using hQa) ((isShapeHyper_recast hγ' hγ P).mp hPh) ((isShapeHyper_recast hγ hγ' Q).mpr hQh)
    rwa [hyperRank_recast, ← hyperRank_recast hγ' hγ rk P] at this
  · rintro ⟨hP, hQ⟩
    refine ⟨hP, fun Q hQK hQa hPh hQh => ?_⟩
    have := hQ (Q.recast hγ' hγ) ((mem_recast_image hγ hγ').mp hQK) (by simpa using hQa)
      ((isShapeHyper_recast hγ' hγ P).mpr hPh) ((isShapeHyper_recast hγ' hγ Q).mpr hQh)
    rwa [hyperRank_recast, hyperRank_recast] at this

theorem eligible_recast {L g η : ℝ} {base : Mom d} {κ : GardenDart G → (Fin d → ℤ)} {F : Set (GBranch G.tree)}
    (P : Object γ G.molecule) :
    eligibleSecondObject γ' G L g η base κ F (P.recast hγ hγ') ↔ eligibleSecondObject γ G L g η base κ F P := by
  unfold eligibleSecondObject
  rw [Object.recast_hasGapKind]
  refine and_congr Iff.rfl (or_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩)
  · rintro ⟨Q, h1, h2, h3⟩
    exact ⟨Q.recast hγ' hγ, h1, by simpa using h2, h3⟩
  · rintro ⟨Q, h1, h2, h3⟩
    exact ⟨Q.recast hγ hγ', h1, by simpa using h2, h3⟩
  · rintro ⟨D, h1, h2⟩
    exact ⟨D.recast hγ' hγ, h1, h2⟩
  · rintro ⟨D, h1, h2⟩
    exact ⟨D.recast hγ hγ', h1, h2⟩

theorem isSourceSecondCollection_recast {L g η : ℝ} {base : Mom d} {κ : GardenDart G → (Fin d → ℤ)}
    {F : Set (GBranch G.tree)} {om : Set (Finset (GBranch G.tree))} {K : Set (Object γ G.molecule)}
    (h : IsSourceSecondCollection γ G L g η base κ F om K) :
    IsSourceSecondCollection γ' G L g η base κ F om (Object.recast hγ hγ' '' K) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun S hS => ?_, fun D hD hf hs => ?_, fun P => ?_⟩
  · obtain ⟨D, hD, hf, hs, hS⟩ := h1 S hS
    exact ⟨D.recast hγ hγ', hD, (Object.recast_hasGapKind hγ hγ' (Object.ofVine D.first_vine) _ _ _ _ _ _).mpr hf,
      (Object.recast_hasGapKind hγ hγ' (Object.ofVine D.second_vine) _ _ _ _ _ _).mpr hs, hS⟩
  · exact h2 (D.recast hγ' hγ) hD (Object.recast_hasGapKind hγ' hγ (Object.ofVine D.first_vine) _ _ _ _ _ _ |>.mpr hf)
      (Object.recast_hasGapKind hγ' hγ (Object.ofVine D.second_vine) _ _ _ _ _ _ |>.mpr hs)
  · rw [mem_recast_image hγ hγ', h3, ← eligible_recast hγ' hγ, Object.recast_atoms]
    refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun hQ Q hQe hQo hc => ?_, fun hQ Q hQe hQo hc => ?_⟩)
    · have := hQ (Q.recast hγ' hγ) ((eligible_recast hγ' hγ Q).mpr hQe) hQo
        (by rw [← Object.recast_isContained hγ hγ', Object.recast_recast, Object.recast_recast]; exact hc)
      rw [← Object.recast_isContained hγ hγ', Object.recast_recast, Object.recast_recast] at this
      exact this
    · have := hQ (Q.recast hγ hγ') ((eligible_recast hγ hγ' Q).mpr hQe) hQo
        (by rw [← Object.recast_isContained hγ' hγ, Object.recast_recast]; exact hc)
      rw [← Object.recast_isContained hγ' hγ, Object.recast_recast] at this
      exact this

end recast

section transfer
variable {R : ℕ} {G : Garden (2 * R)}

@[simp] theorem CountingChoices.recast_ladderScale (C : CountingChoices γ G d) :
    (C.recast hγ hγ').ladderScale = C.ladderScale := rfl
@[simp] theorem CountingChoices.recast_hinges (C : CountingChoices γ G d) :
    (C.recast hγ hγ').subpro.hinges = C.subpro.hinges := rfl

theorem CountingChoices.criticalSG_recast (C : CountingChoices γ G d) (v : GBranch G.tree) :
    (C.recast hγ hγ').CriticalSG v ↔ C.CriticalSG v := by
  unfold CountingChoices.CriticalSG
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h P hP hI => ?_, fun h P hP hI => ?_⟩)
  · exact h (P.recast hγ hγ') ⟨P, hP, rfl⟩ hI
  · obtain ⟨Q, hQ, rfl⟩ := hP
    exact h Q hQ hI

theorem CountingChoices.numCriticalSG_recast (C : CountingChoices γ G d) :
    (C.recast hγ hγ').numCriticalSG = C.numCriticalSG := by
  classical
  unfold CountingChoices.numCriticalSG
  congr 1
  exact Finset.filter_congr fun v _ => C.criticalSG_recast hγ hγ' v

theorem countingGeometry_recast {C : CountingChoices γ G d} (h : CountingGeometry G C) :
    CountingGeometry G (C.recast hγ hγ') where
  molecule := h.molecule
  connected := h.connected
  atom_count := h.atom_count
  bond_count := h.bond_count
  subpro := ⟨fun i => (allowedCollectionObject_recast hγ hγ' _).mpr (h.subpro.1 i), h.subpro.2.1, h.subpro.2.2⟩
  fixedRoots_card := h.fixedRoots_card
  hingeSmall := h.hingeSmall
  hingeOutsideFirst := h.hingeOutsideFirst
  hingeOutsideSecond := fun v hv P hP => by
    obtain ⟨Q, hQ, rfl⟩ := hP
    exact h.hingeOutsideSecond v hv Q hQ
  tripleDesignated := h.tripleDesignated
  hingeNoLoop := h.hingeNoLoop

theorem subproSupport_recast {L g η : ℝ} {base : Mom d} {kFix : Finset (Mom d)} {κ : GardenDart G → (Fin d → ℤ)}
    {C : SubproChoices γ G} (h : SubproSupport γ G C L g η base kFix κ) :
    SubproSupport γ' G (C.recast hγ hγ') L g η base kFix κ where
  selectedSG := fun i => (Object.recast_hasGapKind hγ hγ' _ _ _ _ _ _ _).mpr (h.selectedSG i)
  zeroTame := h.zeroTame
  contained := fun P hP hO hD => by
    have hP' : (P.recast hγ' hγ).HasGapKind L g η base κ .SG := (Object.recast_hasGapKind hγ' hγ _ _ _ _ _ _ _).mpr hP
    rcases h.contained (P.recast hγ' hγ) hP' (fun i hi => hO i hi) hD with ⟨S, a, b, hS, h1, h2, h3⟩ | ⟨Q, h1, h2, h3, h4⟩
    · exact Or.inl ⟨S, a, b, isDV_recast hγ hγ' hS, h1, h2, h3⟩
    · exact Or.inr ⟨Q.recast hγ hγ', h1, by simpa using h2, h3, h4⟩
  hingeSG := h.hingeSG
  hingeJoint := fun v hv i hi => by
    have := h.hingeJoint v hv i hi
    obtain ⟨x, y, h1, h2, h3, h4⟩ := this
    exact ⟨x, y, h1, h2, (Object.recast_containsDart hγ hγ' _ x).mpr h3, (Object.recast_containsDart hγ hγ' _ y).mpr h4⟩
  crossing := fun P hP hO hD => by
    have hP' : (P.recast hγ' hγ).HasGapKind L g η base κ .SG := (Object.recast_hasGapKind hγ' hγ _ _ _ _ _ _ _).mpr hP
    obtain ⟨v, hv, hvP, hc⟩ := h.crossing (P.recast hγ' hγ) hP' (fun i hi => hO i hi) hD
    refine ⟨v, hv, hvP, ?_⟩
    rcases hc with hc | ⟨hj, x, y, h1, h2, h3⟩
    · exact Or.inl hc
    · refine Or.inr ⟨hj, x, y, h1, h2, ?_⟩
      show Xor (P.ContainsDart x) (P.ContainsDart y)
      rwa [Object.recast_containsDart, Object.recast_containsDart] at h3

theorem admissible_recast {L g η : ℝ} {base : Mom d} {κ : GardenDart G → (Fin d → ℤ)} {C : CountingChoices γ G d}
    (h : C.Admissible L g η base κ) : (C.recast hγ hγ').Admissible L g η base κ := by
  obtain ⟨h1, ⟨rk, hrk, K, hK, hsec⟩, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨subproSupport_recast hγ hγ' h1, ⟨rk, hrk, _, isSourceSecondCollection_recast hγ hγ' hK, ?_⟩, h3, h4, h5,
    fun i v hv => ?_, fun P hP v hv => ?_, fun v hv => h8 v ((C.criticalSG_recast hγ hγ' v).mp hv), h9⟩
  · change Object.recast hγ hγ' '' C.secondCollection = _
    rw [hsec, canonicalSub_recast]
  · obtain ⟨x, y, e1, e2, e3, e4⟩ := h6 i v hv
    exact ⟨x, y, e1, e2, (Object.recast_containsDart hγ hγ' _ x).mpr e3, (Object.recast_containsDart hγ hγ' _ y).mpr e4⟩
  · obtain ⟨Q, hQ, rfl⟩ := hP
    obtain ⟨x, y, e1, e2, e3, e4⟩ := h7 Q hQ v hv
    exact ⟨x, y, e1, e2, (Object.recast_containsDart hγ hγ' _ x).mpr e3, (Object.recast_containsDart hγ hγ' _ y).mpr e4⟩

theorem splicedCountingAdmissible_recast {D : SplicedKernelData G d} {C : CountingChoices γ G d} {L g η : ℝ}
    {base : Mom d} {roots : Fin (2 * R) → (Fin d → ℤ)} {κ : GardenDart G → (Fin d → ℤ)}
    (h : splicedCountingAdmissible G D C L g η base roots κ) :
    splicedCountingAdmissible G D (C.recast hγ hγ') L g η base roots κ :=
  ⟨h.1, admissible_recast hγ hγ' h.2⟩

end transfer

end WaveTurbulence.GammaLow.FinalCount.Src
