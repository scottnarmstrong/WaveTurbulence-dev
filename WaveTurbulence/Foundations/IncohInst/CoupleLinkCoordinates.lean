/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleCarrier
public import WaveTurbulence.Foundations.IncohInst.Links.Coherence
public import WaveTurbulence.Foundations.Incoh.LayerLink

/-! # Source link endpoints as the exact finite time coordinates -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links

variable {G : Garden 2} {Q : RegCpl}

/-- The actual two source branching endpoints of one enumerated link. -/
@[expose] def coupleLinkBranch (hQ : Q.Decodes G) (j : Fin Q.links.length) (b : Fin 2) : GBranch G.tree :=
  if b = 0 then chosenBranch hQ j else
    ⟨(Q.links.get j).2, (link_branching hQ (List.get_mem Q.links j)).2.1⟩

/-- Every source branching time occurs among the link endpoints. -/
theorem coupleLinkBranch_surjective (hQ : Q.Decodes G) :
    Function.Surjective (fun p : Fin Q.links.length × Fin 2 => coupleLinkBranch hQ p.1 p.2) := by
  intro b
  obtain ⟨l, ⟨hl, hb⟩, _⟩ := exists_unique_link hQ b
  obtain ⟨j, rfl⟩ := List.get_of_mem hl
  rcases hb with hb | hb
  · refine ⟨(j, 0), Subtype.ext ?_⟩
    exact hb.symm
  · refine ⟨(j, 1), Subtype.ext ?_⟩
    exact hb.symm

/-- No branching clock is repeated by the source link parametrization. -/
theorem coupleLinkBranch_injective (hQ : Q.Decodes G) :
    Function.Injective (fun p : Fin Q.links.length × Fin 2 => coupleLinkBranch hQ p.1 p.2) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ he
  dsimp only at he
  have ha : (coupleLinkBranch hQ i a).1 = (Q.links.get i).1 ∨
      (coupleLinkBranch hQ i a).1 = (Q.links.get i).2 := by
    fin_cases a <;> simp [coupleLinkBranch, chosenBranch, chosenNode]
  have hb : (coupleLinkBranch hQ j b).1 = (Q.links.get j).1 ∨
      (coupleLinkBranch hQ j b).1 = (Q.links.get j).2 := by
    fin_cases b <;> simp [coupleLinkBranch, chosenBranch, chosenNode]
  have hij := eq_of_flat_nodup (couple_links_flat_nodup Q) (List.get_mem Q.links i)
    (List.get_mem Q.links j) ha (by rw [he]; exact hb)
  have hij' : i = j := (nodup_of_flat_nodup (couple_links_flat_nodup Q)).get_inj_iff.mp hij
  subst j
  have hne := (link_branching hQ (List.get_mem Q.links i)).2.2
  have hab : a = b := by
    have hv := congrArg Subtype.val he
    fin_cases a <;> fin_cases b
    · rfl
    · exact False.elim (hne hv)
    · exact False.elim (hne hv.symm)
    · rfl
  exact Prod.ext rfl hab

/-- The time-coordinate bijection is derived from C2's actual endpoint partition. -/
@[expose] def coupleLinkEquiv (hQ : Q.Decodes G) : (Fin Q.links.length × Fin 2) ≃ GBranch G.tree :=
  Equiv.ofBijective _ ⟨coupleLinkBranch_injective hQ, coupleLinkBranch_surjective hQ⟩

/-- Analytic source link data with the exact layers and orientation; localization parameters
are zero here because they are inserted only by the later spectral decomposition. -/
@[expose] def coupleLayerLinks {d : ℕ} (LG : LayeredGarden 2) {Q : RegCpl}
    (hQ : Q.Decodes LG.garden) (j : Fin Q.links.length) : LayerLink d where
  leftCenter := 0
  rightCenter := 0
  leftShift := 0
  rightShift := 0
  leftLayer := LG.layer (coupleLinkBranch hQ j 0).toNode
  rightLayer := LG.layer (coupleLinkBranch hQ j 1).toNode
  orientation := LG.garden.sign (chosenBranch hQ j).toNode

end WaveTurbulence.IncohInst
