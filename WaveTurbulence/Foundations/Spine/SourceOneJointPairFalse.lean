/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSwapObject
/-! Orientation-free form: two selected ordinary objects meeting in a single common joint whose
union is a block or a hyper-block cannot both be selected. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open SourceVine Finset

theorem orient_selected {w d : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule) {L γ η : ℝ}
    {base : Mom d} {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Object G.molecule)}
    (hc : IsSourceSecondCollection G L γ η base κ F omitted collection)
    {P : Object G.molecule} (hPm : P ∈ collection) (hPvc : ∃ h, P.shape = .vc h)
    {a c : GBranch G.tree} (hset : ({P.upper, P.lower} : Finset _) = {a, c}) :
    ∃ P' : Object G.molecule, P' ∈ collection ∧ (∃ h, P'.shape = .vc h) ∧ P'.atoms = P.atoms ∧
      P'.upper = a ∧ P'.lower = c := by
  rcases Mole.finset_pair_eq_pair_iff.mp hset with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨P, hPm, hPvc, rfl, h1, h2⟩
  · exact ⟨swapVC P hPvc, swapVC_mem G hM hκ hc0 hc hPm hPvc, (swapVC_atoms P hPvc).2.2.2,
      rfl, h2, h1⟩

theorem one_joint_pair_false {w d : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule) {L γ η : ℝ}
    {base : Mom d} {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Object G.molecule)}
    (hc : IsSourceSecondCollection G L γ η base κ F omitted collection)
    {P Q : Object G.molecule} (hPm : P ∈ collection) (hQm : Q ∈ collection)
    (hPvc : ∃ h, P.shape = .vc h) (hQvc : ∃ h, Q.shape = .vc h)
    {a b c : GBranch G.tree} (hP : ({P.upper, P.lower} : Finset _) = {a, c})
    (hQ : ({Q.upper, Q.lower} : Finset _) = {b, c}) (hPQ : P.atoms ∩ Q.atoms = {c})
    (hU : G.molecule.IsBlock (P.atoms ∪ Q.atoms) a b ∨
      Mole.IsHyperBlock G.molecule (P.atoms ∪ Q.atoms) a b) : False := by
  obtain ⟨P', hP'm, hP'vc, hP'at, hP'u, hP'l⟩ := orient_selected G hM hκ hc0 hc hPm hPvc hP
  obtain ⟨Q', hQ'm, hQ'vc, hQ'at, hQ'u, hQ'l⟩ := orient_selected G hM hκ hc0 hc hQm hQvc
    (a := c) (c := b) (hQ.trans (Finset.pair_comm b c))
  have hPQ' : P'.atoms ∩ Q'.atoms = {c} := by rw [hP'at, hQ'at]; exact hPQ
  obtain ⟨n, hPch0⟩ := object_vc_chain P' hP'vc
  obtain ⟨m, hQch0⟩ := object_vc_chain Q' hQ'vc
  have hPch : Chain G.molecule P'.atoms P'.upper c n := by rw [← hP'l]; exact hPch0
  have hQch : Chain G.molecule Q'.atoms c Q'.lower m := by rw [← hQ'u]; exact hQch0
  have hU' : G.molecule.IsBlock (P'.atoms ∪ Q'.atoms) P'.upper Q'.lower ∨
      Mole.IsHyperBlock G.molecule (P'.atoms ∪ Q'.atoms) P'.upper Q'.lower := by
    rw [hP'at, hQ'at, hP'u, hQ'l]; exact hU
  rcases hU' with hB | hH
  · exact one_joint_union_contradiction G hM hκ hc0 hc hP'm hQ'm hP'vc hQ'vc hP'l hQ'u hPch hQch
      hPQ' hB
  · exact one_joint_hyperblock_false G hM hκ hc0 hc hP'm hQ'm hP'vc hQ'vc hP'l hQ'u hPch hQch
      hPQ' hH

end WaveTurbulence.LGSpine
