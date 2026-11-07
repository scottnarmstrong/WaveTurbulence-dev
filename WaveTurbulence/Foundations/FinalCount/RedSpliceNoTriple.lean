/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MiniTripleBonds
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceDipoles
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.IncomingPorts
public import WaveTurbulence.Foundations.Molecule.GardenIncidence
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): a prime garden has no triple bond (TARGET L709, DH21 Prop 4.14)

Converse of `Twist.miniA_triple` / `miniB_triple`.  Every dart of the garden molecule is the half-edge of an
incidence slot (`inc`), its port is `(atom, dartPosition)`, and `portMate` of that port is the port of the mate
dart (`dart_portMate`).  Three distinct darts between two atoms give a `BranchDipole`
(`SourceDipoles`), which by `exists_sourceMini` is an embedded source mini piece, impossible in a prime garden.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree WaveTurbulence.Mole WaveTurbulence.Reg.Skeleton

variable {w : ℕ}

/-- The incidence slot of a dart. -/
def dartInc (G : Garden w) : GardenDart G → Incidence G
  | .inl (c, true) => .inl c.1.toNode
  | .inl (c, false) => .inr c.1
  | .inr ℓ => .inl ℓ.1.toNode

theorem encode_inl_nonroot (G : Garden w) (a : GNode G.tree) (ha : a.1.2 ≠ []) :
    encodeIncidence G (.inl a) = .inr (GNode.parent a ha, (a.1.2.getLast ha).succ) := by
  have h := parent_child_eq_node a ha
  conv_lhs => rw [← h]
  exact encodeIncidence_child G _ _

theorem dart_port (G : Garden w) (x : GardenDart G) :
    encodeIncidence G (dartInc G x) = .inr (G.molecule.atom x, dartPosition G x) := by
  rcases x with ⟨c, b⟩ | ℓ
  · cases b
    · rfl
    · exact encode_inl_nonroot G c.1.toNode c.2
  · exact encode_inl_nonroot G ℓ.1.toNode ℓ.2.2.1

theorem dartInc_mate (G : Garden w) (hG : G.IsPlain) (x : GardenDart G) :
    incidenceMate G (dartInc G x) = dartInc G (G.molecule.mate x) := by
  rcases x with ⟨c, b⟩ | ℓ
  · cases b
    · exact incidenceMate_parent G c.1
    · exact incidenceMate_branch G c.1
  · exact incidenceMate_leaf G ℓ.1

/-- The port of a dart is matched with the port of its mate. -/
theorem dart_portMate (G : Garden w) (hG : G.IsPlain) (x : GardenDart G) :
    portMate G (.inr (G.molecule.atom x, dartPosition G x)) =
      .inr (G.molecule.atom (G.molecule.mate x), dartPosition G (G.molecule.mate x)) := by
  rw [← dart_port, ← dart_port, ← dartInc_mate G hG, ← portMate_encode]

/-- Three distinct darts between two distinct atoms of a plain garden give a source dipole. -/
theorem exists_dipole (G : Garden w) (hG : G.IsPlain) {a b : GBranch G.tree} (hne : a ≠ b)
    (f : Fin 3 → GardenDart G) (hf : Function.Injective f) (ha : ∀ i, G.molecule.atom (f i) = a)
    (hb : ∀ i, G.molecule.atom (G.molecule.mate (f i)) = b) :
    ∃ D : BranchDipole G, D.u = a ∧ D.v = b := by
  classical
  let p : Fin 3 → Fin 4 := fun i => dartPosition G (f i)
  let q : Fin 3 → Fin 4 := fun i => dartPosition G (G.molecule.mate (f i))
  have hp : Function.Injective p := by
    intro i j h
    exact hf (atom_position_injective G (Prod.ext ((ha i).trans (ha j).symm) h))
  have hq : Function.Injective q := by
    intro i j h
    have : G.molecule.mate (f i) = G.molecule.mate (f j) :=
      atom_position_injective G (Prod.ext ((hb i).trans (hb j).symm) h)
    exact hf (Mole.mate_injective G.molecule this)
  -- the permutation
  let e : {x : Fin 4 // x ∈ Set.range p} ≃ {x : Fin 4 // x ∈ Set.range q} :=
    (Equiv.ofInjective p hp).symm.trans (Equiv.ofInjective q hq)
  let π : Equiv.Perm (Fin 4) := Equiv.extendSubtype e
  -- the free port
  have hTc : ((Finset.univ : Finset (Fin 4)) \ Finset.univ.image p).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Finset.card_image_of_injective _ hp]
    simp
  obtain ⟨free, hfree⟩ := Finset.card_eq_one.mp hTc
  refine ⟨{ u := a, v := b, ne := hne, perm := π, free := free, internal := ?_ }, rfl, rfl⟩
  intro i hi
  have hiT : i ∈ Finset.univ.image p := by
    by_contra hnot
    have : i ∈ ((Finset.univ : Finset (Fin 4)) \ Finset.univ.image p) := by simp [hnot]
    rw [hfree] at this
    exact hi (Finset.mem_singleton.mp this)
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hiT
  have hπ : π (p j) = q j := by
    have := Equiv.extendSubtype_apply_of_mem e (p j) ⟨j, rfl⟩
    rw [this]
    have hsym : (Equiv.ofInjective p hp).symm ⟨p j, ⟨j, rfl⟩⟩ = j :=
      (Equiv.ofInjective p hp).symm_apply_eq.mpr rfl
    simp only [e, Equiv.trans_apply, hsym, Equiv.ofInjective_apply]
  rw [hπ]
  have := dart_portMate G hG (f j)
  rw [ha j, hb j] at this
  exact this

theorem bondsBetween_self_ne_three (G : Garden w) (a : GBranch G.tree) : G.molecule.bondsBetween a a ≠ 3 := by
  classical
  intro h3
  let B : Finset (GardenDart G) := G.molecule.bonds.filter fun x => G.molecule.ends x = s(a, a)
  have hB : B.card = 3 := h3
  have hBa : ∀ x ∈ B, G.molecule.atom x = a ∧ G.molecule.atom (G.molecule.mate x) = a := by
    intro x hx
    have := (Finset.mem_filter.mp hx).2
    unfold Molecule.ends at this
    simp only [Sym2.eq_iff, and_self, or_self] at this
    exact this
  have hdis : Disjoint B (B.image G.molecule.mate) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx'
    have h1 : G.molecule.out y = true := (Finset.mem_filter.mp hy).1 |> fun h => by
      simpa [Molecule.bonds] using h
    have h2 : G.molecule.out (G.molecule.mate y) = true := by
      have := (Finset.mem_filter.mp hx).1
      simpa [Molecule.bonds] using this
    rw [G.molecule.out_mate, h1] at h2
    simp at h2
  have hsub : B ∪ B.image G.molecule.mate ⊆ G.molecule.dartsAt a := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact (Mole.mem_dartsAt G.molecule a x).mpr (hBa x h).1
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
      exact (Mole.mem_dartsAt G.molecule a _).mpr (hBa y hy).2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ (Mole.mate_injective G.molecule), hB] at hcard
  have h4 := garden_molecule_deg_le_four G a
  unfold Molecule.deg at h4
  omega

/-- **A prime garden has no triple bond** (TARGET L709, DH21 Prop 4.14): the molecule of a prime
garden has no two atoms joined by exactly three bonds. -/
theorem prime_noTriple (G : Garden w) (hP : Reg.Skeleton.IsPrimeGarden G) :
    ∀ a b, G.molecule.bondsBetween a b ≠ 3 := by
  classical
  intro a b h3
  by_cases hab : a = b
  · subst hab
    exact bondsBetween_self_ne_three G a h3
  · rw [Mole.bondsBetween_eq_card_darts G.molecule hab] at h3
    obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := Finset.card_eq_three.mp h3
    have hmem : ∀ d ∈ ({x, y, z} : Finset (GardenDart G)),
        G.molecule.atom d = a ∧ G.molecule.atom (G.molecule.mate d) = b := by
      intro d hd
      rw [← hs] at hd
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hd
      exact ⟨(Mole.mem_dartsAt G.molecule a d).mp h1, h2⟩
    let f : Fin 3 → GardenDart G := ![x, y, z]
    have hf : Function.Injective f := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp [f] at h ⊢ <;> first | exact absurd h hxy | exact absurd h hxz | exact absurd h hyz | exact absurd h.symm hxy | exact absurd h.symm hxz | exact absurd h.symm hyz
    obtain ⟨D, hu, hv⟩ := exists_dipole G hP.1 hab f hf
      (fun i => by fin_cases i <;> simp [f] <;> simp [hmem])
      (fun i => by fin_cases i <;> simp [f] <;> simp [hmem])
    obtain ⟨o, -⟩ := D.exists_sourceMini hP.1
    exact hP.2 ⟨o⟩

end WaveTurbulence.RedSplice
