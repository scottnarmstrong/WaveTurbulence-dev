/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmDesig
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperDiamondObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourcePairsCompatible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmDesig`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (R50 F-DESIG): the same designation.**  `SameDes U U'`: two objects with the same atoms, the same `ContainsDart`
darts and the same joint set (possibly exchanged).  Two members of `C2Can` with equal atoms are `SameDes` (`sameDes_of_c2can`):
ordinary objects are determined by their atoms up to the orientation of the joints (`object_joints_eq`), a hyper object and an ordinary
one cannot share atoms (joint degrees 3 versus 2), and two hyper objects have the same deleted bond (canonical rank). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- Two objects of the same atom set, darts and joint set. -/
def SameDes {M₀ : Molecule V D₀} (U U' : Src.Object Src.γL M₀) : Prop :=
  U.atoms = U'.atoms ∧ (∀ z, U.ContainsDart z ↔ U'.ContainsDart z) ∧
    ({U.upper, U.lower} : Finset V) = {U'.upper, U'.lower}

theorem SameDes.refl {M₀ : Molecule V D₀} (U : Src.Object Src.γL M₀) : SameDes U U := ⟨rfl, fun _ => Iff.rfl, rfl⟩

/-- The joints of an object are determined by its atom set. -/
theorem object_joints_eq {M : Molecule V D₀} (P Q : Src.Object Src.γL M) (h : P.atoms = Q.atoms) :
    ({P.upper, P.lower} : Finset V) = {Q.upper, Q.lower} := by
  have bP := (object_oh P).basic
  have bQ := (object_oh Q).basic
  refine WaveTurbulence.Vine.joints_eq_of_two_low_degrees M (A := P.atoms) (U := P.atoms) (a := Q.upper)
    (b := Q.lower) (x := P.upper) (y := P.lower) subset_rfl (h ▸ bQ.2.1) (h ▸ bQ.2.2.1) bQ.2.2.2.1 bP.2.2.2.1 ?_ ?_ ?_
  · rw [h]; rcases bQ.2.2.2.2.2.1 with h | h <;> omega
  · rw [h, ← bQ.2.2.2.2.1]; rcases bQ.2.2.2.2.2.1 with h | h <;> omega
  · intro v hv h1 h2
    exact bP.2.2.2.2.2.2 v hv h1 h2

theorem sameDes_of_vc_vc {M : Molecule V D₀} {U U' : Src.Object Src.γL M} (hU : ∃ h, U.shape = .vc h) (hU' : ∃ h, U'.shape = .vc h)
    (h : U.atoms = U'.atoms) : SameDes U U' :=
  ⟨h, fun z => by rw [containsDart_vc hU, containsDart_vc hU', h], object_joints_eq U U' h⟩

/-- A hyper object and an ordinary object never have the same atoms. -/
theorem not_vc_hyper_atoms {M : Molecule V D₀} {U U' : Src.Object Src.γL M} (hU : ∃ h, U.shape = .vc h)
    (hU' : ∃ R, U'.shape = .hyper R) (h : U.atoms = U'.atoms) : False := by
  have hj := object_joints_eq U U' h
  have hm : U.upper ∈ ({U'.upper, U'.lower} : Finset V) := hj ▸ mem_insert_self _ _
  have h2 := object_vc_degIn U hU (Or.inl rfl)
  have h3 := object_hyper_degIn U' hU' (by simpa using hm)
  rw [h] at h2
  omega

theorem sameDes_of_hyper_hyper {M : Molecule V D₀} (hrk : Function.Injective (dartRankG D₀)) {U U' : Src.Object Src.γL M}
    (hU : ∃ R, U.shape = .hyper R) (hU' : ∃ R, U'.shape = .hyper R) (h : U.atoms = U'.atoms)
    (h1 : U.hyperRankG ≤ U'.hyperRankG) (h2 : U'.hyperRankG ≤ U.hyperRankG) : SameDes U U' := by
  obtain ⟨R, hR⟩ := hU
  obtain ⟨R', hR'⟩ := hU'
  have hrank : min (dartRankG D₀ R.added) (dartRankG D₀ (M.mate R.added)) =
      min (dartRankG D₀ R'.added) (dartRankG D₀ (M.mate R'.added)) := by
    have e := le_antisymm h1 h2
    unfold Src.Object.hyperRankG at e
    rw [hR, hR'] at e
    exact e
  have hb : R'.added = R.added ∨ R'.added = M.mate R.added := by
    rcases min_choice (dartRankG D₀ R.added) (dartRankG D₀ (M.mate R.added)) with e1 | e1 <;>
      rcases min_choice (dartRankG D₀ R'.added) (dartRankG D₀ (M.mate R'.added)) with e2 | e2 <;>
      rw [e1, e2] at hrank
    · exact Or.inl (hrk hrank).symm
    · right; have := hrk hrank; rw [this, M.mate_mate]
    · right; exact (hrk hrank).symm
    · left; have := hrk hrank; have := congrArg M.mate this; rw [M.mate_mate, M.mate_mate] at this; exact this.symm
  have hconv : ∀ {A B : Src.Object Src.γL M} (RA : Src.HyperLikeRealization Src.γL M A.atoms A.upper A.lower)
      (RB : Src.HyperLikeRealization Src.γL M B.atoms B.upper B.lower), A.shape = .hyper RA → B.shape = .hyper RB →
      A.atoms = B.atoms → (RB.added = RA.added ∨ RB.added = M.mate RA.added) →
      ∀ z, B.ContainsDart z → A.ContainsDart z := by
    intro A B RA RB hA hB hat hb z hz
    unfold Src.Object.ContainsDart at hz ⊢
    rw [hB] at hz
    rw [hA]
    simp only at hz ⊢
    obtain ⟨a1, a2, a3⟩ := hz
    refine ⟨?_, ?_, hat ▸ a3⟩
    · rcases hb with e | e
      · rw [← e]; exact a1
      · intro hz'; apply a2; rw [e, M.mate_mate]; exact hz'
    · rcases hb with e | e
      · rw [← e]; exact a2
      · rw [← e]; exact a1
  have hb' : R.added = R'.added ∨ R.added = M.mate R'.added := by
    rcases hb with e | e
    · exact Or.inl e.symm
    · right; rw [e, M.mate_mate]
  exact ⟨h, fun z => ⟨hconv R' R hR' hR h.symm hb' z, hconv R R' hR hR' h hb z⟩, object_joints_eq U U' h⟩

/-- **Two members of `C2Can` with equal atoms have the same designation.** -/
theorem sameDes_of_c2can {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    {Unsel : Set (Src.Object Src.γL M₀)} {U U' : Src.Object Src.γL M₀} (hU : U ∈ C.C2Can L γ η w κ Unsel) (hU' : U' ∈ C.C2Can L γ η w κ Unsel)
    (h : U.atoms = U'.atoms) : SameDes U U' := by
  rcases object_shape_cases U with hv | hh <;> rcases object_shape_cases U' with hv' | hh'
  · exact sameDes_of_vc_vc hv hv' h
  · exact (not_vc_hyper_atoms hv hh' h).elim
  · exact (not_vc_hyper_atoms hv' hh h.symm).elim
  · exact sameDes_of_hyper_hyper (dartRankG_injective D₀) hh hh' h (hU.2 U' hU'.1 h.symm hh hh')
      (hU'.2 U hU.1 h hh' hh)

theorem SameDes.joints {M : Molecule V D₀} {U U' : Src.Object Src.γL M} (h : SameDes U U') :
    (U.upper = U'.upper ∧ U.lower = U'.lower) ∨ (U.upper = U'.lower ∧ U.lower = U'.upper) := by
  have hne := (object_oh U).basic.2.2.2.1
  have hu : U.upper ∈ ({U'.upper, U'.lower} : Finset V) := h.2.2 ▸ mem_insert_self _ _
  have hl : U.lower ∈ ({U'.upper, U'.lower} : Finset V) := h.2.2 ▸ mem_insert_of_mem (mem_singleton_self _)
  simp only [mem_insert, mem_singleton] at hu hl
  rcases hu with e1 | e1 <;> rcases hl with e2 | e2
  · exact absurd (e1.trans e2.symm) hne
  · exact Or.inl ⟨e1, e2⟩
  · exact Or.inr ⟨e1, e2⟩
  · exact absurd (e1.trans e2.symm) hne

/-- The joint identification of a vine cut transfers along `SameDes`. -/
theorem SameDes.joint_id {M : Molecule V D₀} {U U' : Src.Object Src.γL M} (h : SameDes U U') {X Y : V}
    (hJ : (X = U'.upper ∧ Y = U'.lower) ∨ (X = U'.lower ∧ Y = U'.upper)) :
    (X = U.upper ∧ Y = U.lower) ∨ (X = U.lower ∧ Y = U.upper) := by
  rcases h.joints with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hJ with ⟨c, d⟩ | ⟨c, d⟩
  · exact Or.inl ⟨c.trans a.symm, d.trans b.symm⟩
  · exact Or.inr ⟨c.trans b.symm, d.trans a.symm⟩
  · exact Or.inr ⟨c.trans b.symm, d.trans a.symm⟩
  · exact Or.inl ⟨c.trans a.symm, d.trans b.symm⟩

/-- **Collected objects have the same designation or disjoint atoms** (from S4-DISJ: `C₁` pairwise disjoint, `C₂` disjoint from `C₁`,
`C₂` atoms equal or disjoint; plus F-DESIG). -/
theorem desDisj_of_parts {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    {Un : Set (Src.Object Src.γL M₀)}
    (hC1 : ∀ i j, i ≠ j → Disjoint (C.collection i).atoms (C.collection j).atoms)
    (hC12 : ∀ U ∈ C.C2Of L γ η w κ Un, ∀ i, Disjoint U.atoms (C.collection i).atoms)
    (hC2 : ∀ U ∈ C.C2Of L γ η w κ Un, ∀ U' ∈ C.C2Of L γ η w κ Un, U.atoms = U'.atoms ∨ Disjoint U.atoms U'.atoms)
    (U U' : Src.Object Src.γL M₀) (hU : Collected C Un L γ η w κ U) (hU' : Collected C Un L γ η w κ U') :
    SameDes U U' ∨ Disjoint U.atoms U'.atoms := by
  rcases hU with ⟨i, rfl⟩ | hU <;> rcases hU' with ⟨j, rfl⟩ | hU'
  · by_cases hij : i = j
    · subst hij; exact Or.inl (SameDes.refl _)
    · exact Or.inr (hC1 i j hij)
  · exact Or.inr (hC12 _ hU'.1 i).symm
  · exact Or.inr (hC12 _ hU.1 j)
  · rcases hC2 U hU.1 U' hU'.1 with h | h
    · exact Or.inl (sameDes_of_c2can hU hU' h)
    · exact Or.inr h

end WaveTurbulence.GammaLow.FinalCount.H
