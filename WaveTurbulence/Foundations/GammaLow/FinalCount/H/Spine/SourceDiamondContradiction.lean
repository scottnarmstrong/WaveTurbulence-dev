/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceDiamondContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.DV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceDiamondContradiction`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Two selected ordinary objects with the same joints meeting exactly in the joints and not
nested cannot both be selected: they share a joint bond, are both type-V vines, hence form a
double vine one of whose constituents is omitted. 

**Low-range change (L6-HDS).** A vine whose joints are joined by a bond is a double bond or a T-vine with `σ = 1`
(`DS.vineEnl_joint_bond_cases`; main: (I) or (V)); the double vine built from two such vines is a DV′ of the low family
(`Src.DoubleVine`, with `σ = 1`).
-/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine Finset

theorem object_vc_chain {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} (O : Src.Object Src.γL M) (h : ∃ h, O.shape = .vc h) :
    ∃ n, Src.Chain Src.γL M O.atoms O.upper O.lower n := by
  obtain ⟨hh, hs⟩ := h
  rcases O with ⟨S, a, b, sh⟩
  cases sh with
  | vc h' => exact h'.2
  | hyper R => cases hs


theorem ordinary_diamond_false {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Src.Object Src.γL G.molecule)}
    (hc : Src.IsSourceSecondCollection Src.γL G L γ η base κ F omitted collection)
    {P Q : Src.Object Src.γL G.molecule} (hPm : P ∈ collection) (hQm : Q ∈ collection)
    (hPvc : ∃ h, P.shape = .vc h) (hQvc : ∃ h, Q.shape = .vc h)
    (hPQ : P.atoms ∩ Q.atoms = {P.upper, P.lower})
    (hQj : (Q.upper = P.upper ∧ Q.lower = P.lower) ∨ (Q.upper = P.lower ∧ Q.lower = P.upper))
    (hnest : ¬ P.atoms ⊆ Q.atoms) (hnest' : ¬ Q.atoms ⊆ P.atoms)
    (hPsg : P.HasGapKind L γ η base κ .SG) (hQsg : Q.HasGapKind L γ η base κ .SG) : False := by
  have hPB := object_vc_block P hPvc
  have hQB := object_vc_block Q hQvc
  have hQB' : G.molecule.IsBlock Q.atoms P.upper P.lower := by
    rcases hQj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hQB
    · rw [← h1, ← h2]; exact Mole.block_swap_joints _ hQB
  obtain ⟨z, hza, hzb, hzP, hzQ⟩ := diamond_shared_bond hM hPB hQB' hPQ
  have haQ : P.upper ∈ Q.atoms := by
    have : P.upper ∈ P.atoms ∩ Q.atoms := by rw [hPQ]; simp
    exact (mem_inter.mp this).2
  have hbQ : P.lower ∈ Q.atoms := by
    have : P.lower ∈ P.atoms ∩ Q.atoms := by rw [hPQ]; simp
    exact (mem_inter.mp this).2
  have haP : P.upper ∈ P.atoms := hPB.2.1
  have hbP : P.lower ∈ P.atoms := hPB.2.2.1
  obtain ⟨nP, hPch⟩ := object_vc_chain P hPvc
  obtain ⟨nQ, hQch⟩ := object_vc_chain Q hQvc
  have hQch' : Src.Chain Src.γL G.molecule Q.atoms P.upper P.lower nQ := by
    rcases hQj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hQch
    · rw [← h1, ← h2]; exact chain_swap hQch
  have hXP0 := chain_single_of_joint_bond hM hPch.toVine hPB hza hzb hzP
  have hXQ0 := chain_single_of_joint_bond hM hQch'.toVine hQB' hza hzb hzQ
  have hXP : G.molecule.IsTVine P.atoms P.upper P.lower ∧ G.molecule.sigma P.upper P.lower = 1 := by
    rcases DS.vineEnl_joint_bond_cases hXP0 hza hzb with h | h
    · exfalso
      apply hnest
      rw [Vine.typeI_atoms h]
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact haQ
      · rw [mem_singleton.mp hv]; exact hbQ
    · exact h
  have hXQ : G.molecule.IsTVine Q.atoms P.upper P.lower := by
    rcases DS.vineEnl_joint_bond_cases hXQ0 hza hzb with h | h
    · exfalso
      apply hnest'
      rw [Vine.typeI_atoms h]
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact haP
      · rw [mem_singleton.mp hv]; exact hbP
    · exact h.1
  let D : Src.DoubleVine Src.γL G :=
    ⟨P.atoms, Q.atoms, P.upper, P.lower, hXP.2, Src.isSomeVine_of_T hXP.1, Src.isSomeVine_of_T hXQ, hPQ⟩
  have hκ1 : ∀ x, κ (G.molecule.mate x) = κ x := hκ.1
  have hcons : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 →
      ∑ x ∈ G.molecule.dartsAt v, G.molecule.dartSign x • Molecule.kvec L base κ x = 0 :=
    fun v hv hd => (hκ.2 v hv).trans (hc0 v hv hd)
  obtain ⟨rP, hrP, hkP⟩ := (object_vc_hasGapKind_iff P hPvc L γ η base κ .SG).mp hPsg
  obtain ⟨rQ, hrQ, hkQ⟩ := (object_vc_hasGapKind_iff Q hQvc L γ η base κ .SG).mp hQsg
  have h1 : (Src.Object.ofVine D.first_vine).HasGapKind L γ η base κ .SG :=
    (object_vc_hasGapKind_iff _ ⟨_, rfl⟩ L γ η base κ .SG).mpr ⟨rP, hrP, hkP⟩
  have h2 : (Src.Object.ofVine D.second_vine).HasGapKind L γ η base κ .SG := by
    refine (object_vc_hasGapKind_iff _ ⟨_, rfl⟩ L γ η base κ .SG).mpr ?_
    rcases hQj with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨rQ, by show G.molecule.IsBlockGap L base κ Q.atoms P.upper rQ; rw [← e1]; exact hrQ, hkQ⟩
    · obtain ⟨r', hr', hk'⟩ := source_block_lower_SG_gap G.molecule hM hQB L γ η base κ hκ1 hcons
        hrQ hkQ
      exact ⟨r', by show G.molecule.IsBlockGap L base κ Q.atoms P.upper r'; rw [← e2]; exact hr', hk'⟩
  have hPo := ((hc.2.2 P).mp hPm).2.1
  have hQo := ((hc.2.2 Q).mp hQm).2.1
  have hDF : Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) F :=
    disjointF_union (eligible_atoms_disjoint ((hc.2.2 P).mp hPm).1)
      (eligible_atoms_disjoint ((hc.2.2 Q).mp hQm).1)
  rcases hc.2.1 D hDF h1 h2 with ⟨h, h'⟩ | ⟨h, h'⟩
  · exact hPo h
  · exact hQo h

end WaveTurbulence.GammaLow.FinalCount.H
