/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Geometry.SurvConnMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproContained2R83
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK5
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: o75 Theorem 7.5′(4) (`SubproSupportMK.contained`) for the marked splice

`contained_atomsMk` is main's `contained_atoms` (SubproContained2R83) for `stSt G σ Mk`, with survivors
(o75 §4.5, clause (4)).  An SG object `P` of `G_sb` avoiding `H ∪ B` and not inside an object of `𝒞₁ ∪ 𝒞_E` lies,
through the preimage map, in one group `g`:
* (d) `g` marked: `P` lies in one survivor (`obj_in_survivor`), excluded;
* `g` unmarked: main's argument (cases (a)–(c) of o75), with the containers of `g` disjoint from the survivors, which
  live in marked groups.

Ruling R173: every marked vine lies in an SG group (`hMkSG : Mk ⊆ vinesV0 G σ`); then a marked group is SG
(`sg_of_markedGroup`), so the marked case is case (d).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1

variable {R : ℕ} {G : Garden (2 * R)}

/-- **R173**: if every marked vine lies in `𝒱₀` (an SG group), every marked group is SG. -/
theorem sg_of_markedGroup {σ : Prescription G} {Mk : Set (CLVine G)} (hMkSG : Mk ⊆ vinesV0 G σ)
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) (hmk : markedGroup G Mk S) :
    σ S = Molecule.GapKind.SG := by
  obtain ⟨c, hc, -, hI⟩ := hmk
  obtain ⟨-, S', hS', hI', hσ', -⟩ := hMkSG hc
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  obtain ⟨z, hz⟩ : c.atoms.Nonempty := by
    rcases hI with ⟨_, _, _, _, _, _, hCI⟩ | ⟨_, _, _, _, _, _, _, _, _, hCI⟩
    · obtain ⟨X, hX⟩ := (Vine.chainIngredient_spec hCI).2.1
      exact ⟨_, hX.1.2.1⟩
    · obtain ⟨X, hX⟩ := (Vine.chainIngredient_spec hCI).2.1
      exact ⟨_, hX.1.2.1⟩
  by_cases hSS : S = S'
  · rw [hSS]; exact hσ'
  · exact absurd (isIngredient_subset hI' hz)
      (Finset.disjoint_left.mp (groups_disjoint hM hS hS' hSS) (isIngredient_subset hI hz))

/-- The image of an unmerged unmarked group is disjoint from every survivor (survivors lie in marked groups). -/
theorem image_disjoint_survObj (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
    {g : Finset (GBranch G.tree)} (hg : g ∈ maximalGroups G.molecule) (hnm : ¬ markedGroup G Mk g)
    (hall : ∀ z0 ∈ g, (stSt G σ Mk).cls z0 = none)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ survivorsMk G σ Mk) :
    Disjoint (g.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls)) (survObj ht).atoms := by
  obtain ⟨hat, -⟩ := survObj_spec ht
  obtain ⟨S, hS, -, hmk, -, htS⟩ := survivorsMk_group ht
  rw [hat, Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨z1, hz1, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨z2, hz2, he⟩ := Finset.mem_image.mp hv'
  have h21 : z2 = z1 := eq_of_pi_eq_unmerged hM σ (hall z1 hz1) he
  have hz1S : z1 ∈ S := h21 ▸ htS hz2
  have hgS : g = S := by
    by_contra hne
    exact Finset.disjoint_left.mp (groups_disjoint hM hg hS hne) hz1 hz1S
  exact hnm (hgS ▸ hmk)

/-- Main's `gapSpecification_pair_of_object` for an unmarked group of the marked splice. -/
theorem gapSpecification_pair_of_objectMk (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hnm : ¬ markedGroup G Mk S) :
    ∃ a O, groupJoint G S = some a ∧ designatedObject G S = some O ∧
      ∃ e : LocalGapSpecification (stSt G σ Mk).G ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a),
        gapSpecificationMk G σ Mk ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a) = some e ∧ e.kind = σ S ∧
        (((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a ∉ (stSt G σ Mk).hinges →
          (a = O.upper ∨ a = O.lower) ∧ O.ContainsDart ((stSt G σ Mk).M.od e.first) ∧
            O.ContainsDart ((stSt G σ Mk).M.od e.second)) ∧
        ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a ∈ (stSt G σ Mk).hinges →
          HingeSpec G S a ((stSt G σ Mk).M.od e.first, (stSt G σ Mk).M.od e.second))) := by
  obtain ⟨a, ha, e, he, hk, p, h1, h2, hnh⟩ := gapSpecificationMk_group hM σ hS hnm
  obtain ⟨a', O, ha', hO, -⟩ := designatedObject_spec hS
  rw [ha] at ha'
  cases ha'
  refine ⟨a, O, ha, hO, e, he, hk, fun h => ?_, fun h => ?_⟩
  · obtain ⟨-, hsp⟩ := hnh.2 h
    unfold IntSpec at hsp
    obtain ⟨a1, O1, ha1, hO1, hOj, -, hx, hy⟩ := hsp
    rw [ha] at ha1; cases ha1
    rw [hO] at hO1; cases hO1
    rw [h1, h2]
    exact ⟨hOj, hx, hy⟩
  · obtain ⟨-, hsp⟩ := hnh.1 h
    rw [h1, h2]
    exact hsp

/-- **o75 Theorem 7.5′(4) for the marked splice** (main's `contained_atoms` with survivors): an object of `G_sb`
avoiding the hinges and the survivor joints, not inside an object of `𝒞₁` nor inside a survivor, lies in a DV or in
an LG/ZG object, disjoint from the hinges, from `𝒞₁` and from the survivors. -/
theorem contained_atomsMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
    (hMkSG : Mk ⊆ vinesV0 G σ) {d : ℕ}
    (D : SplicedKernelData (stSt G σ Mk).G d) (hD : D.gapSpecification = gapSpecificationMk G σ Mk)
    (L γ η : ℝ) (base : Mom d) (z : GNode (stSt G σ Mk).G.tree → (Fin d → ℤ))
    (hZ : splicedGapIndicator (stSt G σ Mk).G D L γ η base z ≠ 0)
    (P : Object (stSt G σ Mk).G.molecule)
    (hout : ∀ O ∈ objects G σ Mk, ¬ P.atoms ⊆ O.atoms)
    (hsurv : ∀ t (ht : t ∈ survivorsMk G σ Mk), ¬ P.atoms ⊆ (survObj ht).atoms)
    (hdis : Disjoint P.atoms (stSt G σ Mk).hinges)
    (hJ : ∀ t (ht : t ∈ survivorsMk G σ Mk), (survObj ht).upper ∉ P.atoms ∧ (survObj ht).lower ∉ P.atoms) :
    (∃ S a b, IsDV (stSt G σ Mk).G.molecule S a b ∧ P.atoms ⊆ S ∧ Disjoint S (stSt G σ Mk).hinges ∧
        (∀ O ∈ objects G σ Mk, Disjoint S O.atoms) ∧
        ∀ t (ht : t ∈ survivorsMk G σ Mk), Disjoint S (survObj ht).atoms) ∨
      ∃ Q : Object (stSt G σ Mk).G.molecule, P.atoms ⊆ Q.atoms ∧
        (Q.HasGapKind L γ η base (bondIndex (stSt G σ Mk).G z) Molecule.GapKind.LG ∨
          Q.HasGapKind L γ η base (bondIndex (stSt G σ Mk).G z) Molecule.GapKind.ZG) ∧
        Disjoint Q.atoms (stSt G σ Mk).hinges ∧ (∀ O ∈ objects G σ Mk, Disjoint Q.atoms O.atoms) ∧
        ∀ t (ht : t ∈ survivorsMk G σ Mk), Disjoint Q.atoms (survObj ht).atoms := by
  classical
  have hB := nohinge_unmergedMk σ hdis
  obtain ⟨I, hIπ, -⟩ := exists_iso_down (stSt G σ Mk).M (stSt G σ Mk).hcls P.atoms hB
  have hP0 : IsVineLikeSet G.molecule (P.atoms.image (stSt G σ Mk).M.ob) := by
    have := isVineLikeSet_of_object (I.mapObj P (subset_refl _))
    rw [InducedIso.mapObj_atoms, hIπ] at this
    exact this
  obtain ⟨g, hg, hPg⟩ := cover_group hM hP0
  have hPg' : ∀ c ∈ P.atoms, (stSt G σ Mk).M.ob c ∈ g := fun c hc => hPg (Finset.mem_image_of_mem _ hc)
  have hne : P.upper ∈ P.atoms := Object.upper_mem P
  -- (d): a marked group; `P` lies in one survivor
  by_cases hgm : markedGroup G Mk g
  · exfalso
    obtain ⟨t, ht, hsub⟩ := obj_in_survivor hM σ hg (sg_of_markedGroup hMkSG hg hgm) hgm P
      (fun p hp => ⟨_, hPg' p hp, (pi_obMk σ (hB p hp)).symm⟩) hdis hJ
    exact hsurv t ht hsub
  have hgU : groupUnitsMk G Mk g = (groupUnitsOf G g).units := groupUnitsMk_of_not_marked hgm
  by_cases hmeet : ∃ u ∈ unitBlocks G σ Mk, ∃ z0 ∈ g, z0 ∈ u.atoms
  · exfalso
    obtain ⟨u, hu, z0, hz0g, hz0u⟩ := hmeet
    obtain ⟨S'', hS''m, hσ'', hu''⟩ := mem_unitBlocksMk.mp hu
    have hgS : S'' = g := by
      by_contra hne'
      exact Finset.disjoint_left.mp (groups_disjoint hM hS''m hg hne') (groupUnitsMk_sub hu'' hz0u) hz0g
    subst hgS
    have hu_g : u ∈ (groupUnitsOf G S'').units := hgU ▸ hu''
    rcases hskip : (groupUnitsOf G S'').skip with _ | sk
    · have hua := (groupUnitsOf G S'').noskip_units hskip u hu_g
      have hcl := stSt_cls_memMk (Mk := Mk) hM σ hu (hua ▸ hPg' P.upper hne : (stSt G σ Mk).M.ob P.upper ∈ u.atoms)
      rw [hB _ hne] at hcl
      cases hcl
    · obtain ⟨O, hO, hOm⟩ := objOf_isSomeMk hM σ hg hσ'' (Or.inr ⟨sk, hskip⟩) hgm
      exact hout O hOm (atoms_sub_objMk hM σ hO (fun c hc => ⟨hPg' c hc, hB c hc⟩))
  · have hall : ∀ z0 ∈ g, (stSt G σ Mk).cls z0 = none := fun z0 hz0 =>
      stSt_cls_noneMk (Mk := Mk) hM σ (fun u hu hzu => hmeet ⟨u, hu, z0, hz0, hzu⟩)
    by_cases hobj : σ g = Molecule.GapKind.SG ∧ HasObj G g
    · exfalso
      obtain ⟨O, hO, hOm⟩ := objOf_isSomeMk hM σ hg hobj.1 hobj.2 hgm
      exact hout O hOm (atoms_sub_objMk hM σ hO (fun c hc => ⟨hPg' c hc, hB c hc⟩))
    · have hO : objOf G σ g Mk = none := objOf_noneMk σ (fun h => hobj ⟨h.2.2.1, h.2.2.2⟩)
      have hdisH := image_pi_disjoint_hingesMk σ hall
      have hdisO := image_pi_disjoint_objectsMk hM σ hg hall hO
      have hdisS := fun t (ht : t ∈ survivorsMk G σ Mk) => image_disjoint_survObj hM σ hg hgm hall ht
      obtain ⟨I2, hI2π, hI2od⟩ := exists_iso_up (stSt G σ Mk).M (stSt G σ Mk).hcls g hall
      have hPsub : P.atoms ⊆ g.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) := by
        intro c hc
        exact Finset.mem_image.mpr ⟨(stSt G σ Mk).M.ob c, hPg' c hc, pi_obMk σ (hB c hc)⟩
      by_cases hvl : IsVineLikeSet G.molecule g
      · right
        obtain ⟨a, Q, ha, hQ, e, he, hek, hnh', -⟩ := gapSpecification_pair_of_objectMk hM σ hg hgm
        obtain ⟨a', ha', hdes⟩ := designatedObject_isDesig hQ
        rw [ha] at ha'; cases ha'
        have haQ : a = Q.upper := hdes.1
        have haG : a ∈ g := (groupJoint_kind ha).1
        have hQa : Q.atoms = g := by
          rcases hsk : (groupUnitsOf G g).skip with _ | sk
          · by_cases hu : (groupUnitsOf G g).units = []
            · exact hdes.2.2.2.2.2.2.1 hsk hu hvl
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
              exact hmeet ⟨u, mem_unitBlocksMk.mpr ⟨g, hg, hσ, hgU ▸ hu'⟩, u.upper,
                (groupUnitsOf G g).sub u hu' u.isBlock.2.1, u.isBlock.2.1⟩
            · exact Or.inr ⟨sk, hsk⟩
          obtain ⟨a0, b0, hab⟩ := hvl
          rcases hab with hhv | hvc | hhvc
          · by_cases hh : ∃ a b, IsHVC G.molecule g a b
            · exact hvl' (by obtain ⟨a', b', h'⟩ := hh; exact ⟨a', b', Or.inr h'⟩)
            · exact Or.inl ⟨⟨a0, b0, hhv⟩, hh⟩
          · exact hvl' ⟨a0, b0, Or.inl hvc⟩
          · exact hvl' ⟨a0, b0, Or.inr hhvc⟩
        have hnotH : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a ∉ (stSt G σ Mk).hinges := by
          intro hh
          have := ((stSt G σ Mk).mem_hinges _).mp hh
          rw [(stSt G σ Mk).M.ob_pi, repC_of_none (hall a haG)] at this
          exact this (hall a haG)
        obtain ⟨-, hc1, hc2⟩ := hnh' hnotH
        have hk := gapKind_of_Z (stSt G σ Mk).G D L γ η base z hZ (q := e) (by rw [hD]; exact he)
        rw [hek] at hk
        have hQsub : Q.atoms ⊆ g := hQa ▸ subset_refl _
        set Q' := I2.mapObj Q hQsub with hQ'
        have hQ'a : Q'.atoms = g.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) := by
          rw [hQ', InducedIso.mapObj_atoms, hQa, hI2π]
        have hcd : ∀ f : GardenDart (stSt G σ Mk).G, Q.ContainsDart ((stSt G σ Mk).M.od f) →
            Q'.ContainsDart f := by
          intro f hf
          have hx : G.molecule.InGroup g ((stSt G σ Mk).M.od f) := hQa ▸ containsDart_inGroup Q hf
          have h1 := (I2.containsDart_map Q hQsub hx).mpr hf
          have h2 : (I2.e ⟨(stSt G σ Mk).M.od f, hx⟩).1 = f := (stSt G σ Mk).M.od_inj (hI2od ⟨_, hx⟩)
          rw [h2] at h1
          exact h1
        have hQ'up : Q'.upper = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls Q.upper := by
          rw [hQ', InducedIso.mapObj_upper, hI2π]
        have hgap : ∀ k, k = σ g → Q'.HasGapKind L γ η base (bondIndex (stSt G σ Mk).G z) k := by
          intro k hk'
          exact hasGapKind_of_pair Q' L γ η base _ e.first e.second (e.at_first.trans (haQ ▸ hQ'up).symm)
            (e.at_second.trans (haQ ▸ hQ'up).symm) e.opposite (hcd _ hc1) (hcd _ hc2) k (hk.trans hk'.symm)
        refine ⟨Q', hQ'a ▸ hPsub, ?_, hQ'a ▸ hdisH, fun O hO' => hQ'a ▸ hdisO O hO',
          fun t ht => hQ'a ▸ hdisS t ht⟩
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
          exact ⟨g.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls), _, _, this, hPsub, hdisH, hdisO, hdisS⟩

end WaveTurbulence.VineA.NormalizedSplice.Subpro
