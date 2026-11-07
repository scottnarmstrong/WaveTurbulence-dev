/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepCnt2
public import WaveTurbulence.Foundations.WaveB.Ladders
public import WaveTurbulence.Foundations.IncohInst.Links.Partition
import Mathlib.Tactic

/-!
# S2 REPRESENTS, `Stage1Counts` item 3, part 3: ladders (`ρ`, `g_sb`) and `g_reg`

* `rho_le_atoms`, `one_le_rho`: `1 ≤ ρ ≤ #atoms` for a nonempty molecule (maximal ladders are disjoint, each has `≥ 4` atoms);
* `totalIncoherency_le_atoms`: `g_sb ≤ #atoms`;
* `two_mul_gregOf_le`: `2 g_reg ≤ |D|` (each link of a regular couple or tree accounts for two branching nodes).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton

section Ladders
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

theorem ladderAtoms_card {m : ℕ} {u v : Fin (m + 1) → V} (h : M.IsLadder u v) :
    (Molecule.ladderAtoms u v).card = 2 * (m + 1) := by
  have hinj := h.2.1
  have hu : Function.Injective u := fun a b hab => Sum.inl_injective (hinj (by simpa using hab))
  have hv : Function.Injective v := fun a b hab => Sum.inr_injective (hinj (by simpa using hab))
  have hd : Disjoint (Finset.univ.image u) (Finset.univ.image v) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hx'
    have := hinj (a₁ := Sum.inl a) (a₂ := Sum.inr b) (by simpa using hb.symm)
    exact Sum.inl_ne_inr this
  unfold Molecule.ladderAtoms
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ hu, Finset.card_image_of_injective _ hv]
  simp only [Finset.card_univ, Fintype.card_fin]
  ring

theorem maxLadder_card {S : Finset V} (hS : S ∈ M.maximalLadders) : ∃ k, 2 ≤ k ∧ S.card = 2 * k := by
  classical
  simp only [Molecule.maximalLadders, Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨m, u, v, hl, rfl⟩ := hS.2.1
  exact ⟨m + 1, by have := hl.1; omega, ladderAtoms_card M hl⟩

theorem maxLadder_subset {S : Finset V} (hS : S ∈ M.maximalLadders) : S ⊆ M.atoms := by
  classical
  simp only [Molecule.maximalLadders, Finset.mem_filter, Finset.mem_powerset] at hS
  exact hS.1

variable {M}

/-- The union of the maximal ladders has `Σ |S|` atoms. -/
theorem card_ladderUnion (hM : M.IsMolecule) :
    (M.maximalLadders.biUnion id).card = ∑ S ∈ M.maximalLadders, S.card := by
  classical
  exact Finset.card_biUnion (fun S hS T hT hST => Molecule.maximalLadders_pairwiseDisjoint M hM hS hT hST)

theorem two_mul_numLadders_le (hM : M.IsMolecule) : 2 * M.numLadders ≤ (M.maximalLadders.biUnion id).card := by
  classical
  rw [card_ladderUnion hM]
  unfold Molecule.numLadders
  have : ∀ S ∈ M.maximalLadders, 2 ≤ S.card := fun S hS => by
    obtain ⟨k, hk, e⟩ := maxLadder_card M hS
    omega
  calc 2 * M.maximalLadders.card = ∑ _S ∈ M.maximalLadders, 2 := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum this

theorem rho_le_atoms (hM : M.IsMolecule) : M.rho ≤ M.atoms.card := by
  classical
  have h1 := two_mul_numLadders_le hM
  have hsub : M.maximalLadders.biUnion id ⊆ M.atoms := by
    intro v hv
    obtain ⟨S, hS, hvS⟩ := Finset.mem_biUnion.mp hv
    exact maxLadder_subset M hS hvS
  have hdisj : Disjoint (M.maximalLadders.biUnion id)
      (M.atoms.filter fun v => ∀ S ∈ M.maximalLadders, v ∉ S) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨S, hS, hvS⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp hv').2 S hS hvS
  have h2 : (M.maximalLadders.biUnion id).card + (M.atoms.filter fun v => ∀ S ∈ M.maximalLadders, v ∉ S).card ≤
      M.atoms.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset hsub (Finset.filter_subset _ _))
  unfold Molecule.rho Molecule.numFree
  omega

theorem one_le_rho (hpos : 1 ≤ M.atoms.card) : 1 ≤ M.rho := by
  classical
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  unfold Molecule.rho Molecule.numFree Molecule.numLadders
  by_cases h : ∀ S ∈ M.maximalLadders, v ∉ S
  · have : 0 < (M.atoms.filter fun v => ∀ S ∈ M.maximalLadders, v ∉ S).card :=
      Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, h⟩⟩
    omega
  · push Not at h
    obtain ⟨S, hS, -⟩ := h
    have : 0 < M.maximalLadders.card := Finset.card_pos.mpr ⟨S, hS⟩
    omega

end Ladders

section TotalInc
variable {w : ℕ} {G : Garden w}

theorem totalIncoherency_le_atoms (hM : G.molecule.IsMolecule) (A : SourceMaximalLadderData G)
    (layer : GBranch G.tree → ℕ) : A.totalIncoherency layer ≤ G.molecule.atoms.card := by
  classical
  have h1 : ∀ S : {S // S ∈ G.molecule.maximalLadders},
      sourceLadderIncoherency G layer (A.upper S) (A.lower S) ≤ A.length S + 1 := by
    intro S
    unfold sourceLadderIncoherency
    calc ∑ j : Fin (A.length S + 1), (if layer (A.upper S j) = layer (A.lower S j) then 0 else 1)
        ≤ ∑ _j : Fin (A.length S + 1), 1 := Finset.sum_le_sum fun j _ => by split_ifs <;> simp
      _ = A.length S + 1 := by simp
  have h2 : ∀ S : {S // S ∈ G.molecule.maximalLadders}, 2 * (A.length S + 1) = S.1.card := by
    intro S
    have := ladderAtoms_card G.molecule (A.ladder S)
    rw [A.atoms S] at this
    omega
  have h3 : A.totalIncoherency layer ≤ ∑ S : {S // S ∈ G.molecule.maximalLadders}, S.1.card := by
    unfold SourceMaximalLadderData.totalIncoherency
    refine (Finset.sum_le_sum fun S _ => h1 S).trans (Finset.sum_le_sum fun S _ => ?_)
    have := h2 S
    omega
  have h4 : ∑ S : {S // S ∈ G.molecule.maximalLadders}, S.1.card = ∑ S ∈ G.molecule.maximalLadders, S.card :=
    Finset.sum_coe_sort G.molecule.maximalLadders (fun S => S.card)
  have h5 := card_ladderUnion hM
  have hsub : G.molecule.maximalLadders.biUnion id ⊆ G.molecule.atoms := by
    intro v hv
    obtain ⟨S, hS, hvS⟩ := Finset.mem_biUnion.mp hv
    exact maxLadder_subset G.molecule hS hvS
  have h6 := Finset.card_le_card hsub
  omega

end TotalInc

section Greg
variable {w : ℕ}

theorem incoherency_le_length (LG : LayeredGarden w) (L : List ((Fin w × Path) × (Fin w × Path))) :
    LG.incoherency L ≤ L.length := by
  classical
  unfold LayeredGarden.incoherency
  refine le_trans (Finset.card_le_card_of_injOn (fun bb => (bb.1.1, bb.2.1)) (t := L.toFinset) ?_ ?_) (List.toFinset_card_le L)
  · intro bb hbb
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hbb
    simpa using hbb.1
  · intro bb₁ _ bb₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

theorem two_mul_gregOf_le {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (LG : LayeredGarden w) :
    2 * gregOf D hS LG ≤ D.size := by
  classical
  have hp : ∀ p : SourcePair S, 2 * LG.incoherency ((D.couple p).linksAt
      (inflatedPosition S D.tree (p.firstLeaf hS).toNode) (inflatedPosition S D.tree (p.secondLeaf hS).toNode)) ≤
      (D.couple p).size := fun p => by
    have h1 := incoherency_le_length LG ((D.couple p).linksAt
      (inflatedPosition S D.tree (p.firstLeaf hS).toNode) (inflatedPosition S D.tree (p.secondLeaf hS).toNode))
    have h2 := Links.couple_linksAt_length (D.couple p) (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode)
    omega
  have hb : ∀ b : GBranch S.tree, 2 * LG.incoherency ((D.tree b).linksAt (nodeSign S.sig b.1)
      (inflatedPosition S D.tree b.toNode)) ≤ (D.tree b).size := fun b => by
    have h1 := incoherency_le_length LG ((D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode))
    have h2 := Links.chain_linksAt_length (D.tree b) (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)
    omega
  unfold gregOf ReconstructionData.size
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, add_comm]
  exact add_le_add (Finset.sum_le_sum fun b _ => hb b) (Finset.sum_le_sum fun p _ => hp p)

end Greg
end WaveTurbulence.Represents
