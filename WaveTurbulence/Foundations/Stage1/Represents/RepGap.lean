/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.Stage1.Represents.RepAudit
public import WaveTurbulence.Foundations.FinalCount.RedSpliceGapKind
public import WaveTurbulence.Foundations.Spine.SourceBlockJointGaps
public import WaveTurbulence.Foundations.Spine.GardenDegreeFourSource
public import WaveTurbulence.Foundations.Spine.SplicedMoleculeDecoration
import Mathlib.Tactic

/-!
# S2 REPRESENTS, W1b: the spliced gap indicator is the `σ`-restriction

Restriction direction (no lift): for a conserving decoration `z` of the original garden `G` and ANY
labels `κsb = κ ∘ od` of `G_sb`, `splicedGapIndicator G_sb = [selOf σ z]` (TARGET L1950, L1956).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
  WaveTurbulence.RedSplice

variable {w : ℕ} {G : Garden w}

/-- Every vine-like object has a gap (at its upper joint) for any labels. -/
theorem exists_hasGapKind {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} (O : SourceVine.Object M) {d : ℕ} (L γ η : ℝ) (v : Mom d)
    (κ : D → (Fin d → ℤ)) : ∃ k, O.HasGapKind L γ η v κ k := by
  classical
  cases hs : O.shape with
  | vc hv =>
    obtain ⟨r, hr⟩ := source_block_joint_gap_exists M hv.1 (Or.inl rfl) L v κ
    refine ⟨_, r, ?_, rfl⟩
    unfold SourceVine.VineLikeObject.IsGap
    rw [hs]; exact hr
  | hyper R =>
    obtain ⟨r, hr⟩ := source_block_joint_gap_exists (Mole.eraseBond M R.added) R.adjoint.1 (Or.inl rfl)
      L v (fun x => κ x.1)
    refine ⟨_, r, ?_, rfl⟩
    unfold SourceVine.VineLikeObject.IsGap
    rw [hs]; exact hr


/-- `groupGapKind` is the kind of the designated object for any labels (the object always has a gap). -/
theorem exists_groupGapKind_eq {G : Garden w} {d : ℕ} (L γ η : ℝ) (v : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) {S : Finset (GBranch G.tree)} {O : SourceVine.Object G.molecule}
    (hO : designatedObject G S = some O) :
    ∃ k, O.HasGapKind L γ η v κ k ∧ groupGapKind G L γ η v κ S = k := by
  obtain ⟨k, hk⟩ := exists_hasGapKind O L γ η v κ
  exact ⟨k, hk, groupGapKind_eq L γ η v κ hO hk⟩

open scoped Classical in
/-- **W1b.** For a conserving decoration `κ = bondIndex G z` of the original garden and labels `κsb = κ ∘ od` of
`G_sb`, the spliced gap indicator (any kernel data carrying `gapSpecification G σ`) is the indicator of the
`σ`-restriction `selOf` (TARGET L1950, L1956). -/
theorem splicedGapIndicator_eq_selOf (hM : G.molecule.IsMolecule) (σ : Prescription G) {d : ℕ}
    (L γ η : ℝ) (base : Mom d) (c : GBranch G.tree → Mom d) (z : GNode G.tree → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L base c (bondIndex G z))
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (zsb : GNode (stSt G σ).G.tree → (Fin d → ℤ))
    (hlab : ∀ y, bondIndex (stSt G σ).G zsb y = bondIndex G z ((stSt G σ).M.od y))
    (D : SplicedKernelData (stSt G σ).G d) (hD : D.gapSpecification = gapSpecification G σ) :
    splicedGapIndicator (stSt G σ).G D L γ η base zsb =
      if selOf (GroupPrescription.ofPrescription σ) L γ η base z then 1 else 0 := by
  classical
  set Q : GBranch (stSt G σ).G.tree → Prop := fun v => ∀ q, gapSpecification G σ v = some q →
        Molecule.gapKind L γ η ((base + latticePoint L (bondIndex (stSt G σ).G zsb q.first)) -
          (base + latticePoint L (bondIndex (stSt G σ).G zsb q.second))) = q.kind with hQ
  have hf : splicedGapIndicator (stSt G σ).G D L γ η base zsb = if ∀ v, Q v then 1 else 0 := by
    unfold splicedGapIndicator
    rw [hD]
    have hb := Finset.prod_boole (M₀ := ℝ) (s := (Finset.univ : Finset (GBranch (stSt G σ).G.tree))) (p := fun v => Q v)
    simp only [Finset.mem_univ, true_implies] at hb
    rw [← hb]
    refine Finset.prod_congr rfl fun v _ => ?_
    split
    next heq =>
      have hQv : Q v := fun q hq => by rw [heq] at hq; cases hq
      simp [hQv]
    next q heq =>
      have hiff : Q v ↔ Molecule.gapKind L γ η ((base + latticePoint L (bondIndex (stSt G σ).G zsb q.first)) -
          (base + latticePoint L (bondIndex (stSt G σ).G zsb q.second))) = q.kind := by
        constructor
        · intro h; exact h q heq
        · intro h q' hq'; rw [heq] at hq'; cases hq'; exact h
      simp only [hiff]
  rw [hf]
  have key : (∀ v, Q v) ↔ selOf (GroupPrescription.ofPrescription σ) L γ η base z := by
    constructor
    · intro hall
      unfold selOf
      intro S
      obtain ⟨a, O, ha, hO, e, he, hind⟩ := gapSpecification_indicator_iff hM σ S.2 L γ η base c _ hκ hc0
        (bondIndex (stSt G σ).G zsb) hlab
      obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ η base (bondIndex G z) hO
      have := (hind k hk).mp (hall _ e he)
      exact hgk.trans this
    · intro hsel v q hq
      have hsome : (gapSpecification G σ v).isSome := by rw [hq]; rfl
      obtain ⟨S, hS, hSv⟩ := (gapSpecification_isSome_iff hM σ v).mp hsome
      obtain ⟨a, O, ha, hO, e, he, hind⟩ := gapSpecification_indicator_iff hM σ hS L γ η base c _ hκ hc0
        (bondIndex (stSt G σ).G zsb) hlab
      have hat : groupAtom G σ S = some ((stSt G σ).M.pi (stSt G σ).hcls a) := by
        unfold groupAtom; rw [ha]; rfl
      rw [hat] at hSv
      cases hSv
      rw [he] at hq
      cases hq
      obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ η base (bondIndex G z) hO
      exact (hind k hk).mpr (hgk.symm.trans (hsel ⟨S, hS⟩))
  simp only [key]

open scoped Classical in
/-- `splicedGapIndicator_eq_selOf` for a garden decoration `z` with root values `roots` of a plain garden. -/
theorem splicedGapIndicator_eq_selOf_gen (hM : G.molecule.IsMolecule) (hp : G.IsPlain) (σ : Prescription G)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0) (zsb : GNode (stSt G σ).G.tree → (Fin d → ℤ))
    (hlab : ∀ y, bondIndex (stSt G σ).G zsb y = bondIndex G z.1 ((stSt G σ).M.od y))
    (D : SplicedKernelData (stSt G σ).G d) (hD : D.gapSpecification = gapSpecification G σ) :
    splicedGapIndicator (stSt G σ).G D L γ η base zsb =
      if selOf (GroupPrescription.ofPrescription σ) L γ η base z.1 then 1 else 0 :=
  splicedGapIndicator_eq_selOf hM σ L γ η base _ z.1 (spliced_molecule_decoration G hp hL base roots z)
    (fun v _ hv => gardenSource_eq_zero_of_deg_four G hp _ v hv) zsb hlab D hD

end WaveTurbulence.Represents
