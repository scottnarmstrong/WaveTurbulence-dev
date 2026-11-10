/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.SubproC2Disj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproCollDisj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.SubproC2Disj`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# S4-DISJ goals 1 and 2: G3's `C2Of` against lg-spine's source second collection

G3's `C₂` (`CollData.C2Of`) is the set of atom-maximal elements of the pool `InP` (SG, outside `C₁`, hinge-free, inside a DV or an LG/ZG
host) minus a set `Unsel` of unselected vines. For the ordinary (VC-shaped) members it coincides with lg-spine's literal second
collection `IsSourceSecondCollection` (the Step-1 collection of TARGET L2101): `c2Of_vc_mem_collection`. Pairwise atom-disjointness
of `C₂` (TARGET L2175) then follows from `collection_atoms_eq_or_disjoint`.
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCountG3 Finset

variable {w d : ℕ}

/-- G3's collection data of lg-spine's `Src.SubproChoices`. -/
def collDataOf {G : Garden w} (C : Src.SubproChoices Src.γL G) : CollData G.molecule :=
  ⟨C.count, C.collection, C.hinges, C.first, C.second⟩

/-- The forbidden set of the second collection (TARGET L2101-L2112): hinges and the atoms of `C₁`. -/
def forbiddenOf {G : Garden w} (C : CollData G.molecule) : Set (GBranch G.tree) :=
  ↑C.hinges ∪ ⋃ i, (↑(C.collection i).atoms : Set (GBranch G.tree))

/-- The unselected vines: pool members whose atom set is omitted. -/
def unselOf {G : Garden w} (C : CollData G.molecule) (L γ η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (omitted : Set (Finset (GBranch G.tree))) : Set (Src.Object Src.γL G.molecule) :=
  {B | C.InP L γ η base κ B ∧ B.atoms ∈ omitted}

theorem disjoint_forbiddenOf_iff {G : Garden w} (C : CollData G.molecule) (S : Finset (GBranch G.tree)) :
    Disjoint (↑S : Set (GBranch G.tree)) (forbiddenOf C) ↔
      Disjoint S C.hinges ∧ ∀ i, Disjoint S (C.collection i).atoms := by
  unfold forbiddenOf
  rw [Set.disjoint_union_right, Set.disjoint_iUnion_right, Finset.disjoint_coe]
  simp only [Finset.disjoint_coe]


/-- A pool member of ordinary shape is an eligible object of lg-spine's second collection. -/
theorem eligible_of_pool_vc {G : Garden w} (C : CollData G.molecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {U : Src.Object Src.γL G.molecule} (hU : C.InP L γ η base κ U)
    (hvc : ∃ h, U.shape = .vc h) : Src.eligibleSecondObject Src.γL G L γ η base κ (forbiddenOf C) U := by
  obtain ⟨hsg, _, _, hhost⟩ := hU
  refine ⟨hsg, ?_⟩
  rcases hhost with ⟨S, a, b, hDV, hsub, hSh, hSC⟩ | ⟨Q, hsub, hQk, hQh, hQC⟩
  · obtain ⟨hσ, A, B, hA, hB, hAB, rfl⟩ := hDV
    exact Or.inr ⟨⟨A, B, a, b, hσ, hA, hB, hAB⟩, hsub, (disjoint_forbiddenOf_iff C _).mpr ⟨hSh, hSC⟩⟩
  · exact Or.inl ⟨Q, hsub, hQk, (disjoint_forbiddenOf_iff C _).mpr ⟨hQh, hQC⟩⟩

/-- Every eligible object of lg-spine's second collection is a pool member of G3. -/
theorem pool_of_eligible {G : Garden w} (C : CollData G.molecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {Q : Src.Object Src.γL G.molecule}
    (hQ : Src.eligibleSecondObject Src.γL G L γ η base κ (forbiddenOf C) Q) : C.InP L γ η base κ Q := by
  have hdisF := eligible_atoms_disjoint hQ
  obtain ⟨hdisH, hdisC⟩ := (disjoint_forbiddenOf_iff C _).mp hdisF
  obtain ⟨hsg, hel⟩ := hQ
  refine ⟨hsg, ?_, hdisH, ?_⟩
  · intro i hsub
    have h1 := Finset.disjoint_of_subset_right hsub (hdisC i)
    have h2 : Q.atoms = ∅ := Finset.disjoint_self_iff_empty _ |>.mp h1
    have h3 := object_mem_of_joint Q (Or.inl rfl)
    rw [h2] at h3
    exact absurd h3 (Finset.notMem_empty _)
  · rcases hel with ⟨Q', hcont, hQ'k, hQ'F⟩ | ⟨D, hsubD, hDF⟩
    · obtain ⟨h1, h2⟩ := (disjoint_forbiddenOf_iff C _).mp hQ'F
      exact Or.inr ⟨Q', hcont, hQ'k, h1, h2⟩
    · obtain ⟨h1, h2⟩ := (disjoint_forbiddenOf_iff C _).mp hDF
      exact Or.inl ⟨D.first ∪ D.second, D.upper, D.lower,
        ⟨D.sigma_one, D.first, D.second, D.first_vine, D.second_vine, D.overlap, rfl⟩, hsubD, h1, h2⟩

/-- **Bridge.** An ordinary member of G3's `C₂` is a member of lg-spine's source second collection (with `omitted` = the atom sets of
the unselected vines). -/
theorem c2Of_vc_mem_collection {G : Garden w} (C : CollData G.molecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {omitted : Set (Finset (GBranch G.tree))}
    {collection : Set (Src.Object Src.γL G.molecule)}
    (hc : Src.IsSourceSecondCollection Src.γL G L γ η base κ (forbiddenOf C) omitted collection)
    {U : Src.Object Src.γL G.molecule} (hU : U ∈ C.C2Of L γ η base κ (unselOf C L γ η base κ omitted))
    (hvc : ∃ h, U.shape = .vc h) : U ∈ collection := by
  obtain ⟨⟨hpool, hnU⟩, hmax⟩ := hU
  refine (hc.2.2 U).mpr ⟨eligible_of_pool_vc C hpool hvc, fun h => hnU ⟨hpool, h⟩, ?_⟩
  intro Q hQel hQo hcont
  have hQpool := pool_of_eligible C hQel
  have := hmax Q ⟨hQpool, fun h => hQo h.2⟩ (Src.Object.contained_atoms_subset U Q hcont)
  exact isContained_of_vc_right Q U hvc this

/-- Two non-nested overlapping objects are both of ordinary shape (their atom sets are blocks). -/
theorem nonnested_overlap_vc {G : Garden w} (hM : G.molecule.IsMolecule) {P Q : Src.Object Src.γL G.molecule}
    (hne : (P.atoms ∩ Q.atoms).Nonempty) (hnP : ¬ P.atoms ⊆ Q.atoms) (hnQ : ¬ Q.atoms ⊆ P.atoms) :
    (∃ h, P.shape = .vc h) ∧ ∃ h, Q.shape = .vc h := by
  obtain ⟨⟨RA⟩, hdA, hiA⟩ := object_overlap_premises P
  obtain ⟨⟨RB⟩, hdB, hiB⟩ := object_overlap_premises Q
  obtain ⟨hAblk, hBblk, _⟩ := Mole.molecule_overlap_classification G.molecule hM RA RB hne hnP hnQ hdA hdB
    hiA hiB
  refine ⟨(object_shape_cases P).resolve_right (by
      rintro ⟨R, hR⟩
      have h1 := object_hyper_degIn P ⟨R, hR⟩ (Or.inl rfl)
      have h2 := (Mole.block_joint_degrees G.molecule hAblk).1
      omega), (object_shape_cases Q).resolve_right (by
      rintro ⟨R, hR⟩
      have h1 := object_hyper_degIn Q ⟨R, hR⟩ (Or.inl rfl)
      have h2 := (Mole.block_joint_degrees G.molecule hBblk).1
      omega)⟩

/-- **S4-DISJ goal 1 (TARGET L2175), `C₂` against `C₂`.** Two members of G3's `C₂` have equal or disjoint atom sets. -/
theorem c2Of_atoms_eq_or_disjoint {G : Garden w} (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    (C : CollData G.molecule) {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Src.Object Src.γL G.molecule)}
    (hc : Src.IsSourceSecondCollection Src.γL G L γ η base κ (forbiddenOf C) omitted collection)
    {U U' : Src.Object Src.γL G.molecule} (hU : U ∈ C.C2Of L γ η base κ (unselOf C L γ η base κ omitted))
    (hU' : U' ∈ C.C2Of L γ η base κ (unselOf C L γ η base κ omitted)) :
    U.atoms = U'.atoms ∨ Disjoint U.atoms U'.atoms := by
  by_cases hdis : Disjoint U.atoms U'.atoms
  · exact Or.inr hdis
  left
  by_cases hnP : U.atoms ⊆ U'.atoms
  · exact hnP.antisymm (hU.2 U' hU'.1 hnP)
  by_cases hnQ : U'.atoms ⊆ U.atoms
  · exact (hnQ.antisymm (hU'.2 U hU.1 hnQ)).symm
  have hne : (U.atoms ∩ U'.atoms).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hdis
  obtain ⟨hvc, hvc'⟩ := nonnested_overlap_vc hM hne hnP hnQ
  exact (collection_atoms_eq_or_disjoint G hM hκ hc0 hc (c2Of_vc_mem_collection C hc hU hvc)
    (c2Of_vc_mem_collection C hc hU' hvc')).resolve_right hdis

end WaveTurbulence.GammaLow.FinalCount.H
