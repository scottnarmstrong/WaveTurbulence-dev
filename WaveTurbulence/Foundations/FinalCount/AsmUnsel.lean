/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.SubproDisjFinal
public import WaveTurbulence.Foundations.Spine.SourceDVContainer
public import WaveTurbulence.Foundations.Spine.SourceDoubleVinePartner
/-! **FINALCOUNT-ASSEMBLY (R49 Q2, R50): `UnselOK` for `unselOf`.**  `IsSourceSecondCollection` is LG-SPINE AMEND7+8's (the DV
witness of an omitted vine is F-disjoint).  `unselOK_of_second8` proves G3's `UnselOK` (session-19 form: the DV rule among the maximal
objects) for `Unsel := unselOf C ... omitted`, with NO named input: the partner of an omitted vine is the other vine of its double vine;
if some non-omitted pool object contains both vines, the omitted vine is covered by a member of `C₂` (`coverCan`); otherwise the
partner is maximal in the pool (`dvPartner_maximal_of_not_first`), hence a VC member of `C₂`.  This replaces the named input
`DVNotInsideObject` of R50 (no AMEND8b needed). -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCountG3 WaveTurbulence.Subpro Finset

variable {w d : ℕ}

/-- A type-V vine has atoms other than its two joints. -/
theorem vine_not_subset_pair {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hS : G.molecule.IsVine .V S a b) : ¬ S ⊆ {a, b} := by
  intro hsub
  have hpair : ({a, b} : Finset (GBranch G.tree)) ⊆ S := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact hS.1.2.1
    · rw [mem_singleton.mp hv]; exact hS.1.2.2.1
  have heq : S = {a, b} := Subset.antisymm hsub hpair
  have h1 := (Mole.block_joint_degrees G.molecule hS.1).1
  have h2 := (Vine.isVine_joint_pair_degrees hS).1
  change G.molecule.degIn {a, b} a = 1 at h2
  rw [heq, h2] at h1
  omega

/-- The swapped double vine. -/
def swapDV {G : Garden w} (D : DoubleVine G) : DoubleVine G where
  first := D.second
  second := D.first
  upper := D.upper
  lower := D.lower
  first_vine := D.second_vine
  second_vine := D.first_vine
  overlap := by rw [inter_comm]; exact D.overlap

/-- **Maximality of the DV partner, the non-nested case.**  A vine-like object `Q'` containing the second vine but not the first
vine is the second vine. -/
theorem dvPartner_maximal_of_not_first {G : Garden w} (hM : G.molecule.IsMolecule) (D : DoubleVine G)
    (Q' : Object G.molecule) (hsub : D.second ⊆ Q'.atoms) (hfirst : ¬ D.first ⊆ Q'.atoms) :
    Q'.atoms ⊆ D.second := by
  by_contra hne
  have hnf : ¬ Q'.atoms ⊆ D.first := by
    intro h
    exact vine_not_subset_pair D.second_vine (by
      intro v hv
      have h1 := h (hsub hv)
      have h2 : v ∈ D.first ∩ D.second := mem_inter.mpr ⟨h1, hv⟩
      rw [D.overlap] at h2; exact h2)
  have ha1 : D.upper ∈ D.first := D.first_vine.1.2.1
  have hb1 : D.lower ∈ D.first := D.first_vine.1.2.2.1
  have ha2 : D.upper ∈ D.second := D.second_vine.1.2.1
  have hb2 : D.lower ∈ D.second := D.second_vine.1.2.2.1
  have hQvc : ∃ h, Q'.shape = .vc h := by
    have hne' : ((Object.ofVine D.first_vine).atoms ∩ Q'.atoms).Nonempty := ⟨D.upper, mem_inter.mpr ⟨ha1, hsub ha2⟩⟩
    have := nonnested_overlap_vc hM (P := Q') (Q := Object.ofVine D.first_vine) (by
      rw [inter_comm]; exact hne') hnf hfirst
    exact this.1
  obtain ⟨D'', hD1, hD2⟩ := dv_branch_double_vine G hM D.first_vine hQvc (hsub ha2) (hsub hb2) hnf hfirst ha1 (hsub ha2)
  have hS' : G.molecule.IsVine .V D.first D''.upper D''.lower := hD1 ▸ D''.first_vine
  have hU : G.molecule.IsVine .V Q'.atoms D''.upper D''.lower := hD2 ▸ D''.second_vine
  have hSU : D.first ∩ Q'.atoms = {D''.upper, D''.lower} := by rw [← hD1, ← hD2]; exact D''.overlap
  have := source_doubleVine_partner_unique_unordered G.molecule hM D.first_vine D.second_vine hS' hU D.overlap hSU
  exact hne (this ▸ subset_rfl)

/-- The partner vine of an omitted vine lies in `C₂` (G3), unless some non-omitted pool object contains both vines. -/
theorem dvPartner_mem_c2Of {G : Garden w} (hM : G.molecule.IsMolecule) (C : CollData G.molecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {omitted : Set (Finset (GBranch G.tree))} (D : DoubleVine G)
    (hNo : ¬ ∃ Q : Object G.molecule, (C.InP L γ η base κ Q ∧ Q ∉ unselOf C L γ η base κ omitted) ∧
      D.first ⊆ Q.atoms ∧ D.second ⊆ Q.atoms)
    (hDF : Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) (forbiddenOf C))
    (hsg2 : (Object.ofVine D.second_vine).HasGapKind L γ η base κ .SG) (hno2 : D.second ∉ omitted) :
    Object.ofVine D.second_vine ∈ C.C2Of L γ η base κ (unselOf C L γ η base κ omitted) := by
  have hel : eligibleSecondObject G L γ η base κ (forbiddenOf C) (Object.ofVine D.second_vine) :=
    ⟨hsg2, Or.inr ⟨D, subset_union_right, hDF⟩⟩
  have hpool := pool_of_eligible C hel
  refine ⟨⟨hpool, fun h => hno2 h.2⟩, ?_⟩
  intro Q' hQ' hsub
  by_cases hfirst : D.first ⊆ Q'.atoms
  · exact (hNo ⟨Q', hQ', hfirst, hsub⟩).elim
  · exact dvPartner_maximal_of_not_first hM D Q' hsub hfirst

/-- **`UnselOK` for `unselOf`** (R49 Q2; no named input). -/
theorem unselOK_of_second8 {G : Garden w} (hM : G.molecule.IsMolecule) (C : CollData G.molecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Object G.molecule)}
    (hc : IsSourceSecondCollection G L γ η base κ (forbiddenOf C) omitted collection) :
    C.UnselOK L γ η base κ (unselOf C L γ η base κ omitted) := by
  refine ⟨fun B hB => ⟨hB.1, ?_⟩⟩
  obtain ⟨hBP, hBω⟩ := hB
  obtain ⟨D, hDF, hsg1, hsg2, hBD⟩ := hc.1 B.atoms hBω
  have hxor := hc.2.1 D hDF hsg1 hsg2
  have key : ∀ D : DoubleVine G, Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) (forbiddenOf C) →
      (Object.ofVine D.second_vine).HasGapKind L γ η base κ .SG → D.second ∉ omitted → B.atoms = D.first →
      (∃ U ∈ C.C2Can L γ η base κ (unselOf C L γ η base κ omitted), B.atoms ⊆ U.atoms) ∨
      ∃ A a b, G.molecule.IsVine .V A a b ∧ G.molecule.IsVine .V B.atoms a b ∧ A ∩ B.atoms = {a, b} ∧
        ∃ U ∈ C.C2Can L γ η base κ (unselOf C L γ η base κ omitted), U.atoms = A ∧ ∃ h, U.shape = .vc h := by
    intro D hDF hsg2 hs hB
    by_cases hcov : ∃ Q : Object G.molecule, (C.InP L γ η base κ Q ∧ Q ∉ unselOf C L γ η base κ omitted) ∧
        D.first ⊆ Q.atoms ∧ D.second ⊆ Q.atoms
    · obtain ⟨Q, ⟨hQP, hQU⟩, h1, -⟩ := hcov
      rcases C.coverCan (unselOf C L γ η base κ omitted) hQP with h | ⟨U, hU, hsub⟩
      · exact absurd h hQU
      · exact Or.inl ⟨U, hU, hB ▸ h1.trans hsub⟩
    · refine Or.inr ⟨D.second, D.upper, D.lower, D.second_vine, hB ▸ D.first_vine, by rw [hB, inter_comm]; exact D.overlap,
        Object.ofVine D.second_vine,
        C.mem_C2Can_of_vc (dvPartner_mem_c2Of hM C D hcov hDF hsg2 hs) ⟨_, rfl⟩, rfl, ?_⟩
      exact ⟨_, rfl⟩
  rcases hBD with h1 | h2
  · have hs : D.second ∉ omitted := fun h => by
      rcases hxor with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · exact a2 h
      · exact a2 (h1 ▸ hBω)
    exact key D hDF hsg2 hs h1
  · have hf : D.first ∉ omitted := fun h => by
      rcases hxor with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · exact a2 (h2 ▸ hBω)
      · exact a2 h
    have hDF' : Disjoint (↑((swapDV D).first ∪ (swapDV D).second) : Set (GBranch G.tree)) (forbiddenOf C) := by
      simpa [swapDV, union_comm] using hDF
    exact key (swapDV D) hDF' hsg1 hf h2

end WaveTurbulence.FinalCountAsm
