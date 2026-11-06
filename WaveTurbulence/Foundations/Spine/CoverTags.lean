/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceFullPairTable
public import WaveTurbulence.Foundations.Spine.SourceCountingChoiceScales
public import WaveTurbulence.Foundations.Spine.SourcePairTable
public import WaveTurbulence.Foundations.Spine.SourceGapTableSelection
public import WaveTurbulence.Foundations.Spine.SourceDyadicFunctionCount
public import WaveTurbulence.Foundations.Spine.SourceSecondCollectionExists
public import WaveTurbulence.Foundations.Spine.SourceAtomKindAtJoints
/-! The finite counting cover of TARGET L2097-L2116, over arbitrary subpro choice data `Cs`
(RULINGS R7). A choice is a gap table, a pair table and a finite family of dyadic scales. All
definitions below are generic over `Cs : SubproChoices G`; the conditional helpers that consume
`SubproSupport` / `hingeOutsideFirst` have distinct names (`*_of_subpro_choices`). -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.Cover
open SourceVine Set Finset WaveTurbulence.LGSpine
open scoped Classical

variable {w d : ℕ}

/-- Combinatorial tag: local gap table and chosen dart pairs. -/
abbrev Tag (G : Garden w) := (SourceAtomPair G → Molecule.GapKind) × SourcePairTable G

/-- A representative momentum labelling of a gap table (arbitrary if none exists). -/
noncomputable def kappaOf (G : Garden w) (L γ η : ℝ) (base : Mom d)
    (τ : SourceAtomPair G → Molecule.GapKind) : GardenDart G → (Fin d → ℤ) :=
  if h : ∃ κ, sourceGapTable G L γ η base κ = τ then h.choose else fun _ => 0

theorem kappaOf_table (G : Garden w) (L γ η : ℝ) (base : Mom d)
    (τ : SourceAtomPair G → Molecule.GapKind) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : sourceGapTable G L γ η base κ = τ) :
    sourceGapTable G L γ η base (kappaOf G L γ η base τ) = τ := by
  unfold kappaOf
  rw [dif_pos ⟨κ, hκ⟩]
  exact (⟨κ, hκ⟩ : ∃ κ, sourceGapTable G L γ η base κ = τ).choose_spec

/-- The omitted double-vine constituents and second collection attached to a gap table. -/
noncomputable def secondOf (G : Garden w) (hM : G.molecule.IsMolecule) (L γ η : ℝ) (base : Mom d)
    (F : Set (GBranch G.tree)) (τ : SourceAtomPair G → Molecule.GapKind) :
    Set (Finset (GBranch G.tree)) × Set (Object G.molecule) :=
  let h := exists_sourceSecondCollection G hM L γ η base (kappaOf G L γ η base τ) F
  (h.choose, h.choose_spec.choose)

theorem secondOf_spec (G : Garden w) (hM : G.molecule.IsMolecule) (L γ η : ℝ) (base : Mom d)
    (F : Set (GBranch G.tree)) (τ : SourceAtomPair G → Molecule.GapKind)
    (κ : GardenDart G → (Fin d → ℤ)) (hκ : sourceGapTable G L γ η base κ = τ) :
    IsSourceSecondCollection G L γ η base κ F (secondOf G hM L γ η base F τ).1
      (secondOf G hM L γ η base F τ).2 := by
  have h := (exists_sourceSecondCollection G hM L γ η base (kappaOf G L γ η base τ) F).choose_spec.choose_spec
  exact (sourceGapTable_secondCollection_iff G L γ η base κ (kappaOf G L γ η base τ)
    (hκ.trans (kappaOf_table G L γ η base τ κ hκ).symm) F _ _).mpr h

/-- An injective rank on darts (used for the canonical designation). -/
noncomputable def dartRank (G : Garden w) : GardenDart G → ℕ :=
  fun x => (Fintype.equivFin (GardenDart G) x : ℕ)

theorem dartRank_injective (G : Garden w) : Function.Injective (dartRank G) := by
  intro x y h
  exact (Fintype.equivFin (GardenDart G)).injective (Fin.ext h)

/-- The tag-level counting choice, with scales still unset. -/
noncomputable def tagChoice (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : SubproChoices G)
    (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (t : Tag G) :
    CountingChoices G d where
  subpro := Cs
  secondCollection := canonicalSub (dartRank G) (secondOf G hM L γ η base Cs.forbidden t.1).2
  omittedDVConstituents := (secondOf G hM L γ η base Cs.forbidden t.1).1
  atomLabel := fun v => atomGapKind G L γ η base (kappaOf G L γ η base t.1) v
  first := sourcePairFirst G t.2
  second := sourcePairSecond G t.2
  atomScale := fun _ => 0
  ladderScale := fun _ => 0
  fixedRoots := univ.image (fun i => base + latticePoint L (roots i))

theorem tagChoice_atomLabel (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : SubproChoices G)
    (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (t : Tag G) (v : GBranch G.tree) :
    (tagChoice G hM Cs L γ η base roots t).atomLabel v =
      atomGapKind G L γ η base (kappaOf G L γ η base t.1) v := by
  unfold tagChoice
  rfl

abbrev LadderChoices (G : Garden w) (L : ℝ) :=
  {S // S ∈ G.molecule.maximalLadders} → SourceLadderScaleChoice L

abbrev AtomScale (L γ η : ℝ) :=
  {P : ℝ // IsDyadicScale P ∧ L⁻¹ ≤ P ∧ P ≤ L ^ (-γ + η)}

/-- The dyadic scale data of a tag: one choice per maximal ladder and per critical SG atom. -/
abbrev Scales {G : Garden w} (B : CountingChoices G d) (L γ η : ℝ) :=
  LadderChoices G L × ({v // B.CriticalSG v} → AtomScale L γ η)

/-- The full counting choice of a tag with scales. -/
noncomputable def fullChoice {G : Garden w} (B : CountingChoices G d) {L γ η : ℝ}
    (s : Scales B L γ η) : CountingChoices G d :=
  { B with
    atomScale := fun v => if h : B.CriticalSG v then (s.2 ⟨v, h⟩).1 else 0
    ladderScale := fun S => if h : S ∈ G.molecule.maximalLadders then
      (match s.1 ⟨S, h⟩ with | none => 0 | some P => P.1) else 0 }

theorem fullChoice_critical {G : Garden w} (B : CountingChoices G d) {L γ η : ℝ}
    (s : Scales B L γ η) (v : GBranch G.tree) :
    (fullChoice B s).CriticalSG v ↔ B.CriticalSG v := Iff.rfl

theorem fullChoice_numCritical {G : Garden w} (B : CountingChoices G d) {L γ η : ℝ}
    (s : Scales B L γ η) : (fullChoice B s).numCriticalSG = B.numCriticalSG := rfl

/-- Any admissible assignment of scales is represented by a finite scale family. -/
theorem exists_scales_of_admissible {G : Garden w} (B : CountingChoices G d) {L γ η : ℝ}
    (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) (as : GBranch G.tree → ℝ)
    (ls : Finset (GBranch G.tree) → ℝ)
    (h : ({B with atomScale := as, ladderScale := ls} : CountingChoices G d).Admissible
      L γ η base κ) :
    ∃ s : Scales B L γ η, (fullChoice B s).Admissible L γ η base κ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hat : ∀ v, B.CriticalSG v → IsDyadicScale (as v) ∧ L⁻¹ ≤ as v ∧ as v ≤ L ^ (-γ + η) :=
    fun v hv => ⟨(h8 v hv).1, (h8 v hv).2.1, (h8 v hv).2.2.1⟩
  have hla : ∀ S ∈ G.molecule.maximalLadders, ls S ≠ 0 →
      IsDyadicScale (ls S) ∧ L⁻¹ ≤ ls S ∧ ls S ≤ 1 :=
    fun S hS h0 => ((h9 S hS).1).resolve_left h0
  let f : LadderChoices G L := fun S =>
    if h0 : ls S.1 = 0 then none else some ⟨ls S.1, hla S.1 S.2 h0⟩
  let g : {v // B.CriticalSG v} → AtomScale L γ η := fun v => ⟨as v.1, hat v.1 v.2⟩
  refine ⟨(f, g), h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩
  · intro v hv
    have hv' : B.CriticalSG v := hv
    have := h8 v hv'
    simpa only [fullChoice, dif_pos hv', g] using this
  · intro S hS
    have hagree : (fullChoice B (f, g)).ladderScale S = ls S := by
      simp only [fullChoice, dif_pos hS, f]
      by_cases h0 : ls S = 0
      · simp [h0]
      · simp [h0]
    have := h9 S hS
    simpa only [hagree] using this

end WaveTurbulence.LGSpine.Cover
