/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.SubproInterleaved
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproChainSplit
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproOneJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.SubproInterleaved`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# S4-DISJ: two members of the second collection cannot interleave

TARGET `disjointlem` (DH23 Lemma 4.11), case "no common joint": two non-nested blocks `A = C0 ∪ C1`, `B = C1 ∪ C2` with
`A`-joints `p0, p2`, `B`-joints `p1, p3`. For ordinary members `A`, `B` of the second collection: split the chain `B` at the cut atom
`p2` (`chain_split`), so `C2` is a chain object with small gap; the one-joint union of `A` and `C2` is the union `A ∪ B`, which
the lg-spine one-joint lemmas show cannot exist (it would be eligible, non-omitted and strictly above `A`).
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset

theorem interleaved_false {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Src.Object Src.γL G.molecule)}
    (hc : Src.IsSourceSecondCollection Src.γL G L γ η base κ F omitted collection)
    {A B : Src.Object Src.γL G.molecule} (hAm : A ∈ collection) (hBm : B ∈ collection)
    (hAvc : ∃ h, A.shape = .vc h) (hBvc : ∃ h, B.shape = .vc h)
    (T : Mole.ThreeBlockChain G.molecule A.atoms B.atoms {A.upper, A.lower} {B.upper, B.lower}) : False := by
  have hκ1 : ∀ x, κ (G.molecule.mate x) = κ x := hκ.1
  have hcons : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 →
      ∑ x ∈ G.molecule.dartsAt v, G.molecule.dartSign x • Molecule.kvec L base κ x = 0 :=
    fun v hv hd => (hκ.2 v hv).trans (hc0 v hv hd)
  obtain ⟨A', hA'm, hA'vc, hA'at, hA'u, hA'l⟩ :=
    orient_selected G hM hκ hc0 hc hAm hAvc (a := T.p0) (c := T.p2) T.left_joints
  obtain ⟨B', hB'm, hB'vc, hB'at, hB'u, hB'l⟩ :=
    orient_selected G hM hκ hc0 hc hBm hBvc (a := T.p1) (c := T.p3) T.right_joints
  have hBblock : G.molecule.IsBlock B.atoms T.p1 T.p3 := by
    have := object_vc_block B' hB'vc
    rwa [hB'u, hB'l, hB'at] at this
  have hAblock : G.molecule.IsBlock A.atoms T.p0 T.p2 := by
    have := object_vc_block A' hA'vc
    rwa [hA'u, hA'l, hA'at] at this
  obtain ⟨nB, hBch⟩ := object_vc_chain B' hB'vc
  rw [hB'u, hB'l, hB'at] at hBch
  obtain ⟨nA, hAch⟩ := object_vc_chain A' hA'vc
  rw [hA'u, hA'l, hA'at] at hAch
  -- split the chain `B` at `p2`
  have hnc := no_cross_of_blocks G.molecule hM (C := T.C1) (C' := T.C2) (U := B.atoms) (a := T.p1) (b := T.p3)
    (c := T.p2) T.block1 hBblock T.right_union T.right_inter
  have hsplit := chain_split G.molecule hM hBch (C := T.C1) (C' := T.C2) (c := T.p2) hBblock
    T.right_union.symm T.right_inter T.block1.2.1 T.block2.2.2.1 (Ne.symm T.block1.2.2.2.1)
    T.block2.2.2.2.1 hnc
  obtain ⟨_, ⟨m, hC2ch⟩⟩ := hsplit
  let Q : Src.Object Src.γL G.molecule := ⟨T.C2, T.p2, T.p3, .vc ⟨T.block2, m, Src.Chain.ofVine hC2ch⟩⟩
  have hC2B : T.C2 ⊆ B.atoms := by
    intro x hx
    have h : x ∈ T.C1 ∪ T.C2 := mem_union_right _ hx
    rwa [← T.right_union] at h
  -- the small gap of `Q`
  have hQsg : Q.HasGapKind L γ η base κ .SG := by
    obtain ⟨hB'sg, _⟩ := ((hc.2.2 B').mp hB'm).1
    obtain ⟨rB, hrB, hkB⟩ := (object_vc_hasGapKind_iff B' hB'vc L γ η base κ .SG).mp hB'sg
    rw [hB'u, hB'at] at hrB
    obtain ⟨rB', hrB', hkB'⟩ := source_block_lower_SG_gap G.molecule hM hBblock L γ η base κ hκ1 hcons hrB hkB
    have hC2' : G.molecule.IsBlock T.C2 T.p3 T.p2 := Mole.block_swap_joints G.molecule T.block2
    obtain ⟨r2, hr2⟩ := source_block_joint_gap_exists G.molecule hC2' (Or.inl rfl) L base κ
    have hBsw : G.molecule.IsBlock B.atoms T.p3 T.p1 := Mole.block_swap_joints G.molecule hBblock
    have hr2eq : r2 = rB' := Vine.nested_block_gap_eq G.molecule hC2B hC2' hBsw _ hr2 hrB'
    subst hr2eq
    obtain ⟨r3, hr3, hk3⟩ := source_block_lower_SG_gap G.molecule hM hC2' L γ η base κ hκ1 hcons hr2 hkB'
    exact (object_vc_hasGapKind_iff Q ⟨_, rfl⟩ L γ η base κ .SG).mpr ⟨r3, hr3, hk3⟩
  have hQF : Disjoint (↑Q.atoms : Set (GBranch G.tree)) F :=
    disjointF_of_subset (hB'at ▸ hC2B) (eligible_atoms_disjoint ((hc.2.2 B').mp hB'm).1)
  have hPQ : A'.atoms ∩ Q.atoms = {T.p2} := by
    have e : A'.atoms = T.C0 ∪ T.C1 := hA'at.trans T.left_union
    rw [e, Finset.union_inter_distrib_right]
    have h0 : T.C0 ∩ T.C2 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp T.exterior_disjoint
    change T.C0 ∩ T.C2 ∪ T.C1 ∩ T.C2 = {T.p2}
    rw [h0, T.right_inter, Finset.empty_union]
  -- concatenation
  obtain ⟨⟨RA0⟩, -, -⟩ := object_overlap_premises A'
  have key : ∀ (S S' : Finset (GBranch G.tree)) (a a' b b' : GBranch G.tree), S = S' → a = a' → b = b' →
      Mole.BlockRealization G.molecule S a b → Mole.BlockRealization G.molecule S' a' b' := by
    rintro _ _ _ _ _ _ rfl rfl rfl h; exact h
  have hRA : Mole.BlockRealization G.molecule A.atoms T.p0 T.p2 := key _ _ _ _ _ _ hA'at hA'u hA'l RA0
  have hRQ : Mole.BlockRealization G.molecule T.C2 T.p3 T.p2 :=
    .block (Mole.block_swap_joints G.molecule T.block2) T.connected2
  have hi' : A.atoms ∩ T.C2 = {T.p2} := by
    have h := hPQ
    rwa [hA'at] at h
  obtain ⟨_, _, hcat⟩ := Mole.realized_single_joint_concatenation G.molecule hM hRA hRQ hi'
  have hPl : A'.lower = T.p2 := hA'l
  have hQu : Q.upper = T.p2 := rfl
  have hPch : Src.Chain Src.γL G.molecule A'.atoms A'.upper T.p2 nA := by rw [hA'at, hA'u]; exact hAch
  have hQch : Src.Chain Src.γL G.molecule Q.atoms T.p2 Q.lower m := Src.Chain.ofVine hC2ch
  have hUat : A'.atoms ∪ Q.atoms = A.atoms ∪ T.C2 := by rw [hA'at]
  have hUu : A'.upper = T.p0 := hA'u
  have hUl : Q.lower = T.p3 := rfl
  rcases hcat with hU | hH
  · refine one_joint_union_false' G hM hκ hc0 hc hA'm (Q := Q) hA'vc ⟨_, rfl⟩ hPl hQu hPch hQch hPQ ?_ hQsg hQF
    rw [hUat, hUu, hUl]; exact hU
  · refine one_joint_hyperblock_false' G hM hκ hc0 hc hA'm (Q := Q) hA'vc ⟨_, rfl⟩ hPl hQu hPch hQch hPQ ?_
      hQsg hQF
    rw [hUat, hUu, hUl]; exact hH

end WaveTurbulence.GammaLow.FinalCount.H
