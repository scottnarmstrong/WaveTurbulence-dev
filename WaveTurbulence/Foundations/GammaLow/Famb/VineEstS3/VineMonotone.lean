/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyAtomSlots
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblySourceStates
public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainNoCross
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainSplit
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyAtoms
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainAssembly
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.VineMonotone
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyAtomSlots
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblySourceStates
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.VineMonotone` (sha256 6a0be250f8c4045a…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Row alignment, part 1: descendants lie in vines of smaller or equal index (R22 (2))

For a vine-chain assembly `B` (pieces listed terminal-vine first) each interior atom `z` lies in one vine
`vineOf B z` (the first component of its chart slot).  `vineOf_child_le`: a branch child of an interior atom lies in a
vine of index `≤` that of its parent; `vineOf_desc_le`: so does every interior descendant.  Proved from the bond
locality `block_concat_inGroup_iff`, the CL parent pattern of every piece and the cut vertex structure; no assumption.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 VineParamContract TTree RegRed Finset WaveTurbulence.GammaLow.Famb.VineEstS2
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Bond locality: every internal bond of the chain lies in one piece. -/
theorem assemblyPiece_inGroupΓ (B : CLChainAssemblyΓ γF G R n) (e : GardenDart G) (he : G.molecule.InGroup U e) :
    ∃ i, G.molecule.InGroup (assemblyPieceAtΓ B i).atoms e := by
  induction B with
  | single hV R => exact ⟨0, he⟩
  | append B hT hi hU R ih =>
    have hS := B.isBlock
    rcases (block_concat_inGroup_iff G.molecule (Mole.garden_isMolecule G) hS (memBlock hT) hi hU e).mp he with h | h
    · obtain ⟨i, hi'⟩ := ih h
      exact ⟨i.succ, hi'⟩
    · exact ⟨0, h⟩

/-- Every piece has the CL parent pattern. -/
theorem assemblyPiece_clΓ (B : CLChainAssemblyΓ γF G R n) (i : Fin n) :
    Mole.CLParentPattern G (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).upper (assemblyPieceAtΓ B i).lower := by
  induction B with
  | single hV R => exact R.parentPattern
  | append B hT hi hU R ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (clBlockConcat_parentPatterns B.isBlock (memBlock hT) hi hU R).2
    · exact ih j

theorem assemblyPiece_zero_lowerΓ (B : CLChainAssemblyΓ γF G R n) (h0 : 0 < n) :
    (assemblyPieceAtΓ B ⟨0, h0⟩).lower = b := by
  cases B with
  | single hV R => rfl
  | append B hT hi hU R => rfl

/-- Each piece's upper joint is the overall `a`, or the lower joint of the next piece. -/
theorem assemblyPiece_jointΓ (B : CLChainAssemblyΓ γF G R n) (i : Fin n) :
    (assemblyPieceAtΓ B i).upper = a ∨
      ∃ h : i.1 + 1 < n, (assemblyPieceAtΓ B ⟨i.1 + 1, h⟩).lower = (assemblyPieceAtΓ B i).upper := by
  induction B with
  | single hV R => exact Or.inl rfl
  | @append S T a' b' c' n' RP B hT hi hU R ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · right
      have hn : 0 < n' := B.length_pos
      refine ⟨by simp; omega, ?_⟩
      exact assemblyPiece_zero_lowerΓ B hn
    · rcases ih j with h | ⟨h, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp; omega, h2⟩

section Vine
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)

/-- The vine (piece index) of an interior atom: the first component of its chart slot. -/
noncomputable def vineOfΓ (z : ↥(U.erase a)) : Fin n :=
  ((assemblyInputEquivΓ hM9 B) ((assemblyAtomEquivΓ hM9 B).symm z)).1

theorem vineOf_eqΓ (z : ↥(U.erase a)) (i : Fin n) (j : Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n)
    (hz : z.1 = ((assemblyChartAtΓ hM9 B i).indexing.atom j).1) : vineOfΓ hM9 B z = i := by
  have hs := assemblyAtomEquiv_inputΓ hM9 B i j
  have h1 : z = assemblyAtomEquivΓ hM9 B ((assemblyInputEquivΓ hM9 B).symm ⟨i, j⟩) :=
    Subtype.ext (hz.trans hs.symm)
  have h2 : (assemblyAtomEquivΓ hM9 B).symm z = (assemblyInputEquivΓ hM9 B).symm ⟨i, j⟩ := by
    rw [h1]; simp
  unfold vineOfΓ
  rw [h2]
  simp

/-- An atom of piece `m` is its upper joint or a chart atom of `m`. -/
theorem mem_atoms_casesΓ (m : Fin n) (y : GBranch G.tree) (hy : y ∈ (assemblyPieceAtΓ B m).atoms) :
    y = (assemblyPieceAtΓ B m).upper ∨
      ∃ j, ((assemblyChartAtΓ hM9 B m).indexing.atom j).1 = y := by
  by_cases h : y = (assemblyPieceAtΓ B m).upper
  · exact Or.inl h
  · right
    obtain ⟨j, hj⟩ := (assemblyChartAtΓ hM9 B m).indexing.atom.surjective ⟨y, Finset.mem_erase.mpr ⟨h, hy⟩⟩
    exact ⟨j, congrArg Subtype.val hj⟩

/-- Chart atoms of a piece with membership in its atom set: the vine index is `m`, or `m + 1` for the upper joint. -/
theorem vineOf_of_mem_atomsΓ (m : Fin n) (y : ↥(U.erase a)) (hy : y.1 ∈ (assemblyPieceAtΓ B m).atoms) :
    (y.1 ≠ (assemblyPieceAtΓ B m).upper ∧ vineOfΓ hM9 B y = m) ∨
      (y.1 = (assemblyPieceAtΓ B m).upper ∧ ∃ h : m.1 + 1 < n, vineOfΓ hM9 B y = ⟨m.1 + 1, h⟩) := by
  rcases mem_atoms_casesΓ hM9 B m y.1 hy with hu | ⟨j, hj⟩
  · right
    refine ⟨hu, ?_⟩
    rcases assemblyPiece_jointΓ B m with ha | ⟨h, h2⟩
    · exact absurd (hu.trans ha) (Finset.mem_erase.mp y.2).1
    · refine ⟨h, ?_⟩
      have hb := (assemblyPieceAtΓ B ⟨m.1 + 1, h⟩).isBlock
      have hlow : (assemblyPieceAtΓ B ⟨m.1 + 1, h⟩).lower ∈ (assemblyPieceAtΓ B ⟨m.1 + 1, h⟩).atoms := hb.2.2.1
      have hne : (assemblyPieceAtΓ B ⟨m.1 + 1, h⟩).lower ≠ (assemblyPieceAtΓ B ⟨m.1 + 1, h⟩).upper := fun e =>
        hb.2.2.2.1 e.symm
      have hy' : y.1 ∈ (assemblyPieceAtΓ B ⟨m.1 + 1, h⟩).atoms := by rw [hu, ← h2]; exact hlow
      rcases mem_atoms_casesΓ hM9 B ⟨m.1 + 1, h⟩ y.1 hy' with hu' | ⟨j', hj'⟩
      · exact absurd (h2.trans (hu.symm.trans hu')) hne
      · exact vineOf_eqΓ hM9 B y _ j' hj'.symm
  · left
    refine ⟨?_, vineOf_eqΓ hM9 B y m j hj.symm⟩
    intro hu
    have := ((assemblyChartAtΓ hM9 B m).indexing.atom j).2
    rw [hj, hu] at this
    exact (Finset.mem_erase.mp this).1 rfl

/-- **Child step.** A branch child of an interior atom lies in a vine of index at most that of its parent. -/
theorem vineOf_child_leΓ (z z' : ↥(U.erase a)) (hn : z'.1.1.2 ≠ [])
    (hp : GNode.parent z'.1.toNode hn = z.1) : vineOfΓ hM9 B z' ≤ vineOfΓ hM9 B z := by
  let d : GardenDart G := Sum.inl (⟨z'.1, hn⟩, false)
  have hd : G.molecule.InGroup U d := by
    refine ⟨(Finset.mem_erase.mp z'.2).2, ?_⟩
    show GNode.parent z'.1.toNode hn ∈ U
    rw [hp]
    exact (Finset.mem_erase.mp z.2).2
  obtain ⟨m, hm1, hm2⟩ := assemblyPiece_inGroupΓ B d hd
  have hz'm : z'.1 ∈ (assemblyPieceAtΓ B m).atoms := hm1
  have hzm : z.1 ∈ (assemblyPieceAtΓ B m).atoms := by
    have : GNode.parent z'.1.toNode hn ∈ (assemblyPieceAtΓ B m).atoms := hm2
    rwa [hp] at this
  have hlen : z.1.1.2.length + 1 = z'.1.1.2.length := by
    have e : z.1.1.2 = z'.1.1.2.dropLast := by
      rw [← hp]; rfl
    rw [e, List.length_dropLast]
    have : 0 < z'.1.1.2.length := List.length_pos_of_ne_nil hn
    omega
  rcases vineOf_of_mem_atomsΓ hM9 B m z hzm with ⟨hzu, hzv⟩ | ⟨hzu, hh, hzv⟩ <;>
    rcases vineOf_of_mem_atomsΓ hM9 B m z' hz'm with ⟨hzu', hzv'⟩ | ⟨hzu', hh', hzv'⟩
  · rw [hzv, hzv']
  · exfalso
    have hcl := assemblyPiece_clΓ B m
    have hdesc := Mole.block_one_root_descendants G (assemblyPieceAtΓ B m).isBlock hcl.1 hcl.2 hzm
    have hpre := hdesc.2
    rw [← hzu'] at hpre
    have h3 := hpre.length_le
    change z'.1.1.2.length ≤ z.1.1.2.length at h3
    omega
  · rw [hzv, hzv']; exact Fin.le_def.mpr (by simp)
  · rw [hzv, hzv']

/-- The parent of an interior atom strictly below an interior atom `v` is again interior and below `v`. -/
theorem parent_stepΓ (B : CLChainAssemblyΓ γF G R n) (v u : ↥(U.erase a)) (k : ℕ) (hdesc : v.1.toNode.IsDesc u.1.toNode)
    (hlen : v.1.1.2.length + k + 1 = u.1.1.2.length) :
    ∃ (hn : u.1.1.2 ≠ []) (z : ↥(U.erase a)), GNode.parent u.1.toNode hn = z.1 ∧
      v.1.toNode.IsDesc z.1.toNode ∧ z.1.1.2.length = v.1.1.2.length + k := by
  have hn : u.1.1.2 ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  have hu : u.1 ∈ U := (Finset.mem_erase.mp u.2).2
  have hua : u.1 ≠ a := (Finset.mem_erase.mp u.2).1
  have hv : v.1 ∈ U := (Finset.mem_erase.mp v.2).2
  have hva : v.1 ≠ a := (Finset.mem_erase.mp v.2).1
  have hpar : Mole.InternalParent G U u.1 := by
    by_cases hub : u.1 = b
    · rw [hub]; exact R.parentPattern.2
    · exact Mole.block_interior_has_parent G B.isBlock hu hua hub
  obtain ⟨hn', hzU⟩ := hpar
  have hlenz : (GNode.parent u.1.toNode hn').1.2.length = v.1.1.2.length + k := by
    show (u.1.1.2.dropLast).length = _
    rw [List.length_dropLast]
    omega
  have hdz : v.1.toNode.IsDesc (GNode.parent u.1.toNode hn').toNode := by
    refine ⟨hdesc.1, ?_⟩
    show v.1.1.2 <+: u.1.1.2.dropLast
    exact prefix_dropLast_of_lt hdesc.2 (by omega)
  have hza : GNode.parent u.1.toNode hn' ≠ a := by
    intro hza
    have hadesc := Mole.block_one_root_descendants G B.isBlock R.parentPattern.1 R.parentPattern.2 hv
    have h1 : v.1.1.2 <+: a.1.2 := by
      have e : (GNode.parent u.1.toNode hn').1.2 = a.1.2 := by rw [hza]
      rw [← e]; exact hdz.2
    have h2 : a.1.2 <+: v.1.1.2 := hadesc.2
    have h3 := h1.eq_of_length (le_antisymm h1.length_le h2.length_le)
    apply hva
    apply Subtype.ext
    refine Prod.ext ?_ h3
    exact hadesc.1.symm
  exact ⟨hn', ⟨GNode.parent u.1.toNode hn', Finset.mem_erase.mpr ⟨hza, hzU⟩⟩, rfl, hdz, hlenz⟩

/-- **Descendant monotonicity.** All interior descendants lie in vines of index at most that of the ancestor. -/
theorem vineOf_desc_leΓ (v : ↥(U.erase a)) :
    ∀ (k : ℕ) (u : ↥(U.erase a)), v.1.toNode.IsDesc u.1.toNode → v.1.1.2.length + k + 1 = u.1.1.2.length →
      vineOfΓ hM9 B u ≤ vineOfΓ hM9 B v := by
  intro k
  induction k with
  | zero =>
    intro u hdesc hlen
    obtain ⟨hn, z, hz, hdz, hlz⟩ := parent_stepΓ B v u 0 hdesc hlen
    have hzv : z = v := by
      have h1 : v.1.1.2 <+: z.1.1.2 := hdz.2
      have h3 := h1.eq_of_length (by omega)
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext hdz.1.symm h3.symm
    subst hzv
    exact vineOf_child_leΓ hM9 B z u hn hz
  | succ k ih =>
    intro u hdesc hlen
    obtain ⟨hn, z, hz, hdz, hlz⟩ := parent_stepΓ B v u (k + 1) hdesc hlen
    exact (vineOf_child_leΓ hM9 B z u hn hz).trans (ih z hdz (by omega))

end Vine

end WaveTurbulence.GammaLow.Famb.VineEstS3
