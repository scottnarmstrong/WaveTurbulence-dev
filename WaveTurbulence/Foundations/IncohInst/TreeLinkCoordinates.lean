/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeCarrier
public import WaveTurbulence.Foundations.IncohInst.Links.Coherence
public import WaveTurbulence.Foundations.Incoh.LayerLink

/-! # Source link endpoints as the exact finite time coordinates -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links

variable {G : Garden 1} {X : RegChain}

/-- Source tree links have two distinct branching endpoints. -/
theorem tree_link_branching (hX : X.DecodesTree G)
    {l : (Fin 1 × TTree.Path) × (Fin 1 × TTree.Path)}
    (hl : l ∈ X.treeLinks (G.sig 0)) :
    l.1.2 ∈ (G.tree l.1.1).branching ∧ l.2.2 ∈ (G.tree l.2.1).branching ∧ l.1 ≠ l.2 :=
  ⟨(tree_mem_pairEndpoints_links_iff hX _).1
      ((Reg.mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inl rfl⟩),
    (tree_mem_pairEndpoints_links_iff hX _).1
      ((Reg.mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inr rfl⟩),
    fst_ne_snd_of_flat_nodup (tree_links_flat_nodup X _) hl⟩

/-- The actual two source branching endpoints of one enumerated link. -/
@[expose] def treeLinkBranch (hX : X.DecodesTree G) (j : Fin (X.treeLinks (G.sig 0)).length) (b : Fin 2) : GBranch G.tree :=
  if b = 0 then treeChosenBranch hX j else
    ⟨((X.treeLinks (G.sig 0)).get j).2, (tree_link_branching hX (List.get_mem (X.treeLinks (G.sig 0)) j)).2.1⟩

/-- Every source branching time occurs among the link endpoints. -/
theorem treeLinkBranch_surjective (hX : X.DecodesTree G) :
    Function.Surjective (fun p : Fin (X.treeLinks (G.sig 0)).length × Fin 2 => treeLinkBranch hX p.1 p.2) := by
  intro b
  obtain ⟨l, ⟨hl, hb⟩, _⟩ := tree_exists_unique_link hX b
  obtain ⟨j, rfl⟩ := List.get_of_mem hl
  rcases hb with hb | hb
  · refine ⟨(j, 0), Subtype.ext ?_⟩
    exact hb.symm
  · refine ⟨(j, 1), Subtype.ext ?_⟩
    exact hb.symm

/-- No branching clock is repeated by the source link parametrization. -/
theorem treeLinkBranch_injective (hX : X.DecodesTree G) :
    Function.Injective (fun p : Fin (X.treeLinks (G.sig 0)).length × Fin 2 => treeLinkBranch hX p.1 p.2) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ he
  dsimp only at he
  have ha : (treeLinkBranch hX i a).1 = ((X.treeLinks (G.sig 0)).get i).1 ∨
      (treeLinkBranch hX i a).1 = ((X.treeLinks (G.sig 0)).get i).2 := by
    fin_cases a <;> simp [treeLinkBranch, treeChosenBranch, treeChosen]
  have hb : (treeLinkBranch hX j b).1 = ((X.treeLinks (G.sig 0)).get j).1 ∨
      (treeLinkBranch hX j b).1 = ((X.treeLinks (G.sig 0)).get j).2 := by
    fin_cases b <;> simp [treeLinkBranch, treeChosenBranch, treeChosen]
  have hij := eq_of_flat_nodup (tree_links_flat_nodup X (G.sig 0)) (List.get_mem (X.treeLinks (G.sig 0)) i)
    (List.get_mem (X.treeLinks (G.sig 0)) j) ha (by rw [he]; exact hb)
  have hij' : i = j := (nodup_of_flat_nodup (tree_links_flat_nodup X (G.sig 0))).get_inj_iff.mp hij
  subst j
  have hne := (tree_link_branching hX (List.get_mem (X.treeLinks (G.sig 0)) i)).2.2
  have hab : a = b := by
    have hv := congrArg Subtype.val he
    fin_cases a <;> fin_cases b
    · rfl
    · exact False.elim (hne hv)
    · exact False.elim (hne hv.symm)
    · rfl
  exact Prod.ext rfl hab

/-- The time-coordinate bijection is derived from C2's actual endpoint partition. -/
@[expose] def treeLinkEquiv (hX : X.DecodesTree G) : (Fin (X.treeLinks (G.sig 0)).length × Fin 2) ≃ GBranch G.tree :=
  Equiv.ofBijective _ ⟨treeLinkBranch_injective hX, treeLinkBranch_surjective hX⟩

/-- Analytic source link data with the exact layers and orientation; localization parameters
are zero here because they are inserted only by the later spectral decomposition. -/
@[expose] def treeLayerLinks {d : ℕ} (LG : LayeredGarden 1) {X : RegChain}
    (hX : X.DecodesTree LG.garden) (j : Fin (X.treeLinks (LG.garden.sig 0)).length) : LayerLink d where
  leftCenter := 0
  rightCenter := 0
  leftShift := 0
  rightShift := 0
  leftLayer := LG.layer (treeLinkBranch hX j 0).toNode
  rightLayer := LG.layer (treeLinkBranch hX j 1).toNode
  orientation := LG.garden.sign (treeChosenBranch hX j).toNode

end WaveTurbulence.IncohInst
