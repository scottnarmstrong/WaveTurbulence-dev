/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.SubproContained
import Mathlib.Tactic

/-!
# SUBPRO (S4): TARGET `subpro` (4), atom form, for the construction
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1

variable {R : ℕ} {G : Garden (2 * R)}

theorem contained_atoms (hM : G.molecule.IsMolecule) (σ : Prescription G) {d : ℕ}
    (D : SplicedKernelData (stSt G σ).G d) (hD : D.gapSpecification = gapSpecification G σ)
    (L γ η : ℝ) (base : Mom d) (z : GNode (stSt G σ).G.tree → (Fin d → ℤ))
    (hZ : splicedGapIndicator (stSt G σ).G D L γ η base z ≠ 0)
    (P : Object (stSt G σ).G.molecule)
    (hout : ∀ O ∈ objects G σ, ¬ P.atoms ⊆ O.atoms)
    (hdis : Disjoint P.atoms (stSt G σ).hinges) :
    (∃ S a b, IsDV (stSt G σ).G.molecule S a b ∧ P.atoms ⊆ S ∧ Disjoint S (stSt G σ).hinges ∧
        ∀ O ∈ objects G σ, Disjoint S O.atoms) ∨
      ∃ Q : Object (stSt G σ).G.molecule, P.atoms ⊆ Q.atoms ∧
        (Q.HasGapKind L γ η base (bondIndex (stSt G σ).G z) Molecule.GapKind.LG ∨
          Q.HasGapKind L γ η base (bondIndex (stSt G σ).G z) Molecule.GapKind.ZG) ∧
        Disjoint Q.atoms (stSt G σ).hinges ∧ ∀ O ∈ objects G σ, Disjoint Q.atoms O.atoms := by
  classical
  have hB := nohinge_unmerged σ hdis
  obtain ⟨I, hIπ, -⟩ := exists_iso_down (stSt G σ).M (stSt G σ).hcls P.atoms hB
  have hP0 : IsVineLikeSet G.molecule (P.atoms.image (stSt G σ).M.ob) := by
    have := isVineLikeSet_of_object (I.mapObj P (subset_refl _))
    rw [InducedIso.mapObj_atoms, hIπ] at this
    exact this
  obtain ⟨g, hg, hPg⟩ := cover_group hM hP0
  have hPg' : ∀ c ∈ P.atoms, (stSt G σ).M.ob c ∈ g := fun c hc => hPg (Finset.mem_image_of_mem _ hc)
  have hne : P.upper ∈ P.atoms := Object.upper_mem P
  by_cases hmeet : ∃ u ∈ unitBlocks G σ, ∃ z0 ∈ g, z0 ∈ u.atoms
  · exfalso
    obtain ⟨u, hu, z0, hz0g, hz0u⟩ := hmeet
    obtain ⟨S'', hS''m, hσ'', hu''⟩ := mem_unitBlocks.mp hu
    have hgS : S'' = g := by
      by_contra hne'
      exact Finset.disjoint_left.mp (groups_disjoint hM hS''m hg hne')
        ((groupUnitsOf G S'').sub u hu'' hz0u) hz0g
    have hσg : σ g = Molecule.GapKind.SG := hgS ▸ hσ''
    have hu_g : u ∈ (groupUnitsOf G g).units := hgS ▸ hu''
    rcases hskip : (groupUnitsOf G g).skip with _ | sk
    · have hua := (groupUnitsOf G g).noskip_units hskip u hu_g
      have hcl := stSt_cls_mem hM σ hu (hua ▸ hPg' P.upper hne : (stSt G σ).M.ob P.upper ∈ u.atoms)
      rw [hB _ hne] at hcl
      cases hcl
    · obtain ⟨O, hO⟩ := objOf_some hM σ hg hσg (Or.inr ⟨sk, hskip⟩)
      exact hout O (mem_objects_of σ hg hσg hO)
        (atoms_sub_obj hM σ hO (fun c hc => ⟨hPg' c hc, hB c hc⟩))
  · have hall : ∀ z0 ∈ g, (stSt G σ).cls z0 = none := fun z0 hz0 =>
      stSt_cls_none hM σ (fun u hu hzu => hmeet ⟨u, hu, z0, hz0, hzu⟩)
    by_cases hobj : σ g = Molecule.GapKind.SG ∧ HasObj G g
    · exfalso
      obtain ⟨O, hO⟩ := objOf_some hM σ hg hobj.1 hobj.2
      have hsub : P.atoms ⊆ O.atoms := by
        obtain ⟨-, -, -, hSpec⟩ := objOf_spec (Option.mem_def.mpr hO)
        obtain ⟨A, -, hOA, hnm, -⟩ := hSpec.src
        intro c hc
        rw [hOA]
        exact Finset.mem_image.mpr ⟨(stSt G σ).M.ob c, hnm _ (hPg' c hc) (hall _ (hPg' c hc)), pi_ob σ (hB c hc)⟩
      exact hout O (mem_objects_of σ hg hobj.1 hO) hsub
    · have hO : objOf G σ g = none := objOf_none σ (fun h => hobj ⟨h.2.2.1, h.2.2.2⟩)
      have hdisH := image_pi_disjoint_hinges σ hall
      have hdisO := image_pi_disjoint_objects hM σ hg hall hO
      obtain ⟨I2, hI2π, hI2od⟩ := exists_iso_up (stSt G σ).M (stSt G σ).hcls g hall
      have hPsub : P.atoms ⊆ g.image ((stSt G σ).M.pi (stSt G σ).hcls) := by
        intro c hc
        exact Finset.mem_image.mpr ⟨(stSt G σ).M.ob c, hPg' c hc, pi_ob σ (hB c hc)⟩
      by_cases hvl : IsVineLikeSet G.molecule g
      · right
        obtain ⟨a, Q, ha, hQ, e, he, hek, hnh', -⟩ := gapSpecification_pair_of_object hM σ hg
        obtain ⟨a', ha', hdes⟩ := designatedObject_isDesig hQ
        rw [ha] at ha'; cases ha'
        have haQ : a = Q.upper := hdes.1
        have haG : a ∈ g := (groupJoint_kind ha).1
        have hQa : Q.atoms = g := by
          rcases hsk : (groupUnitsOf G g).skip with _ | sk
          · by_cases hu : (groupUnitsOf G g).units = []
            · exact hdes.2.2.2.2.2.2 hsk hu hvl
            · exact (hdes.2.2.2.2.1 hsk hu).1
          · rcases hb : sk.bond with _ | e'
            · exact (hdes.2.2.1 sk hsk hb).1
            · exact (hdes.2.2.2.1 sk e' hsk hb).1
        have hσne : σ g ≠ Molecule.GapKind.SG := by
          intro hσ
          apply hobj
          refine ⟨hσ, ?_⟩
          have hvl' : (∃ a b, IsVC G.molecule g a b ∨ IsHVC G.molecule g a b) → HasObj G g := by
            intro hx
            rcases (groupUnitsOf G g).vl hM hg hx with hu | ⟨sk, hsk⟩
            · exfalso
              obtain ⟨u, hu'⟩ := List.exists_mem_of_ne_nil _ hu
              exact hmeet ⟨u, mem_unitBlocks.mpr ⟨g, hg, hσ, hu'⟩, u.upper,
                (groupUnitsOf G g).sub u hu' u.isBlock.2.1, u.isBlock.2.1⟩
            · exact Or.inr ⟨sk, hsk⟩
          obtain ⟨a0, b0, hab⟩ := hvl
          rcases hab with hhv | hvc | hhvc
          · by_cases hh : ∃ a b, IsHVC G.molecule g a b
            · exact hvl' (by obtain ⟨a', b', h'⟩ := hh; exact ⟨a', b', Or.inr h'⟩)
            · exact Or.inl ⟨⟨a0, b0, hhv⟩, hh⟩
          · exact hvl' ⟨a0, b0, Or.inl hvc⟩
          · exact hvl' ⟨a0, b0, Or.inr hhvc⟩
        have hQup : Q.upper ∈ g := by rw [← haQ]; exact haG
        have hnotH : (stSt G σ).M.pi (stSt G σ).hcls a ∉ (stSt G σ).hinges := by
          intro hh
          have := ((stSt G σ).mem_hinges _).mp hh
          rw [(stSt G σ).M.ob_pi, repC_of_none (hall a haG)] at this
          exact this (hall a haG)
        obtain ⟨-, hc1, hc2⟩ := hnh' hnotH
        have hk := gapKind_of_Z (stSt G σ).G D L γ η base z hZ (q := e) (by rw [hD]; exact he)
        rw [hek] at hk
        have hQsub : Q.atoms ⊆ g := hQa ▸ subset_refl _
        set Q' := I2.mapObj Q hQsub with hQ'
        have hQ'a : Q'.atoms = g.image ((stSt G σ).M.pi (stSt G σ).hcls) := by
          rw [hQ', InducedIso.mapObj_atoms, hQa, hI2π]
        have hcd : ∀ f : GardenDart (stSt G σ).G, Q.ContainsDart ((stSt G σ).M.od f) → Q'.ContainsDart f := by
          intro f hf
          have hx : G.molecule.InGroup g ((stSt G σ).M.od f) := hQa ▸ containsDart_inGroup Q hf
          have h1 := (I2.containsDart_map Q hQsub hx).mpr hf
          have h2 : (I2.e ⟨(stSt G σ).M.od f, hx⟩).1 = f := (stSt G σ).M.od_inj (hI2od ⟨_, hx⟩)
          rw [h2] at h1
          exact h1
        have hQ'up : Q'.upper = (stSt G σ).M.pi (stSt G σ).hcls Q.upper := by
          rw [hQ', InducedIso.mapObj_upper, hI2π]
        have hgap : ∀ k, k = σ g → Q'.HasGapKind L γ η base (bondIndex (stSt G σ).G z) k := by
          intro k hk'
          exact hasGapKind_of_pair Q' L γ η base _ e.first e.second (e.at_first.trans (haQ ▸ hQ'up).symm)
            (e.at_second.trans (haQ ▸ hQ'up).symm) e.opposite (hcd _ hc1) (hcd _ hc2) k (hk.trans hk'.symm)
        refine ⟨Q', hQ'a ▸ hPsub, ?_, hQ'a ▸ hdisH, fun O hO' => hQ'a ▸ hdisO O hO'⟩
        cases hs : σ g
        · exact Or.inr (hgap _ hs.symm)
        · exact absurd hs hσne
        · exact Or.inl (hgap _ hs.symm)
      · left
        have hst := hg.1
        rcases isStage1Group_iff.mp hst with hv | ⟨a, b, hdv⟩
        · exact absurd hv hvl
        · have := I2.isDV_map hdv (subset_refl _)
          rw [hI2π] at this
          exact ⟨g.image ((stSt G σ).M.pi (stSt G σ).hcls), _, _, this, hPsub, hdisH, hdisO⟩

end WaveTurbulence.Subpro
