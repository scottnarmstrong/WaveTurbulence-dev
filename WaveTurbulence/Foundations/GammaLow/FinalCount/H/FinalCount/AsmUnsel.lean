/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmUnsel
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproDisjFinal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDVContainer
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.DV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmUnsel`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (R49 Q2, R50): `UnselOK` for `unselOf`.**  `IsSourceSecondCollection` is LG-SPINE AMEND7+8's (the DV
witness of an omitted vine is F-disjoint).  `unselOK_of_second8` proves G3's `UnselOK` (session-19 form: the DV rule among the maximal
objects) for `Unsel := unselOf C ... omitted`, with NO named input: the partner of an omitted vine is the other vine of its double vine;
if some non-omitted pool object contains both vines, the omitted vine is covered by a member of `C₂` (`coverCan`); otherwise the
partner is maximal in the pool (`dvPartner_maximal_of_not_first`), hence a VC member of `C₂`.  This replaces the named input
`DVNotInsideObject` of R50 (no AMEND8b needed). 

**Low-range change (L6-HDS).** The double vines are DV′s of the low family (`Src.DoubleVine`: `σ = 1`, T-vine
branches; main: two vines (V)); `UnselOK.dv` has the DV′ form (H/FinalCount/G3VineLG1); partner uniqueness is
`DS.dv_partner_unique_unordered`; a branch is not inside the joint pair (`DS.tvine_not_subset_pair`).
-/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCountG3 WaveTurbulence.Subpro Finset

variable {w d : ℕ}

/-- The swapped double vine. -/
def swapDV {G : Garden w} (D : Src.DoubleVine Src.γL G) : Src.DoubleVine Src.γL G where
  first := D.second
  second := D.first
  upper := D.upper
  lower := D.lower
  sigma_one := D.sigma_one
  first_vine := D.second_vine
  second_vine := D.first_vine
  overlap := by rw [inter_comm]; exact D.overlap

/-- **Maximality of the DV partner, the non-nested case.**  A vine-like object `Q'` containing the second vine but not the first
vine is the second vine. -/
theorem dvPartner_maximal_of_not_first {G : Garden w} (hM : G.molecule.IsMolecule) (D : Src.DoubleVine Src.γL G)
    (Q' : Src.Object Src.γL G.molecule) (hsub : D.second ⊆ Q'.atoms) (hfirst : ¬ D.first ⊆ Q'.atoms) :
    Q'.atoms ⊆ D.second := by
  by_contra hne
  have hnf : ¬ Q'.atoms ⊆ D.first := by
    intro h
    exact DS.tvine_not_subset_pair (DS.isTVine_of_sigma_one D.second_vine D.sigma_one) (by
      intro v hv
      have h1 := h (hsub hv)
      have h2 : v ∈ D.first ∩ D.second := mem_inter.mpr ⟨h1, hv⟩
      rw [D.overlap] at h2; exact h2)
  have ha1 : D.upper ∈ D.first := D.first_vine.block.2.1
  have hb1 : D.lower ∈ D.first := D.first_vine.block.2.2.1
  have ha2 : D.upper ∈ D.second := D.second_vine.block.2.1
  have hb2 : D.lower ∈ D.second := D.second_vine.block.2.2.1
  have hQvc : ∃ h, Q'.shape = .vc h := by
    have hne' : ((Src.Object.ofVine D.first_vine).atoms ∩ Q'.atoms).Nonempty := ⟨D.upper, mem_inter.mpr ⟨ha1, hsub ha2⟩⟩
    have := nonnested_overlap_vc hM (P := Q') (Q := Src.Object.ofVine D.first_vine) (by
      rw [inter_comm]; exact hne') hnf hfirst
    exact this.1
  obtain ⟨D'', hD1, hD2⟩ := dv_branch_double_vine G hM D.sigma_one D.first_vine hQvc (hsub ha2) (hsub hb2) hnf hfirst ha1 (hsub ha2)
  have hS' : Src.IsSomeVine Src.γL G.molecule D.first D''.upper D''.lower := hD1 ▸ D''.first_vine
  have hU : Src.IsSomeVine Src.γL G.molecule Q'.atoms D''.upper D''.lower := hD2 ▸ D''.second_vine
  have hSU : D.first ∩ Q'.atoms = {D''.upper, D''.lower} := by rw [← hD1, ← hD2]; exact D''.overlap
  have := DS.dv_partner_unique_unordered hM D.sigma_one D.first_vine.block
    (DS.isTVine_of_sigma_one D.second_vine D.sigma_one) hS'.block hU.block D.overlap hSU
  exact hne (this ▸ subset_rfl)

/-- The partner vine of an omitted vine lies in `C₂` (G3), unless some non-omitted pool object contains both vines. -/
theorem dvPartner_mem_c2Of {G : Garden w} (hM : G.molecule.IsMolecule) (C : CollData G.molecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {omitted : Set (Finset (GBranch G.tree))} (D : Src.DoubleVine Src.γL G)
    (hNo : ¬ ∃ Q : Src.Object Src.γL G.molecule, (C.InP L γ η base κ Q ∧ Q ∉ unselOf C L γ η base κ omitted) ∧
      D.first ⊆ Q.atoms ∧ D.second ⊆ Q.atoms)
    (hDF : Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) (forbiddenOf C))
    (hsg2 : (Src.Object.ofVine D.second_vine).HasGapKind L γ η base κ .SG) (hno2 : D.second ∉ omitted) :
    Src.Object.ofVine D.second_vine ∈ C.C2Of L γ η base κ (unselOf C L γ η base κ omitted) := by
  have hel : Src.eligibleSecondObject Src.γL G L γ η base κ (forbiddenOf C) (Src.Object.ofVine D.second_vine) :=
    ⟨hsg2, Or.inr ⟨D, subset_union_right, hDF⟩⟩
  have hpool := pool_of_eligible C hel
  refine ⟨⟨hpool, fun h => hno2 h.2⟩, ?_⟩
  intro Q' hQ' hsub
  by_cases hfirst : D.first ⊆ Q'.atoms
  · exact (hNo ⟨Q', hQ', hfirst, hsub⟩).elim
  · exact dvPartner_maximal_of_not_first hM D Q' hsub hfirst

/-- **`UnselOK` for `unselOf`** (R49 Q2; no named input). -/
theorem unselOK_of_second8 {G : Garden w} (hM : G.molecule.IsMolecule) (C : CollData G.molecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Src.Object Src.γL G.molecule)}
    (hc : Src.IsSourceSecondCollection Src.γL G L γ η base κ (forbiddenOf C) omitted collection) :
    C.UnselOK L γ η base κ (unselOf C L γ η base κ omitted) := by
  refine ⟨fun B hB => ⟨hB.1, ?_⟩⟩
  obtain ⟨hBP, hBω⟩ := hB
  obtain ⟨D, hDF, hsg1, hsg2, hBD⟩ := hc.1 B.atoms hBω
  have hxor := hc.2.1 D hDF hsg1 hsg2
  have key : ∀ D : Src.DoubleVine Src.γL G, Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) (forbiddenOf C) →
      (Src.Object.ofVine D.second_vine).HasGapKind L γ η base κ .SG → D.second ∉ omitted → B.atoms = D.first →
      (∃ U ∈ C.C2Can L γ η base κ (unselOf C L γ η base κ omitted), B.atoms ⊆ U.atoms) ∨
      ∃ A a b, G.molecule.sigma a b = 1 ∧ Src.IsSomeVine Src.γL G.molecule A a b ∧
        Src.IsSomeVine Src.γL G.molecule B.atoms a b ∧ A ∩ B.atoms = {a, b} ∧
        ∃ U ∈ C.C2Can L γ η base κ (unselOf C L γ η base κ omitted), U.atoms = A ∧ ∃ h, U.shape = .vc h := by
    intro D hDF hsg2 hs hB
    by_cases hcov : ∃ Q : Src.Object Src.γL G.molecule, (C.InP L γ η base κ Q ∧ Q ∉ unselOf C L γ η base κ omitted) ∧
        D.first ⊆ Q.atoms ∧ D.second ⊆ Q.atoms
    · obtain ⟨Q, ⟨hQP, hQU⟩, h1, -⟩ := hcov
      rcases C.coverCan (unselOf C L γ η base κ omitted) hQP with h | ⟨U, hU, hsub⟩
      · exact absurd h hQU
      · exact Or.inl ⟨U, hU, hB ▸ h1.trans hsub⟩
    · refine Or.inr ⟨D.second, D.upper, D.lower, D.sigma_one, D.second_vine, hB ▸ D.first_vine, by rw [hB, inter_comm]; exact D.overlap,
        Src.Object.ofVine D.second_vine,
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

end WaveTurbulence.GammaLow.FinalCount.H
