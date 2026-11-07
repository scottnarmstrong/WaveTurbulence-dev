/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGardenUnloopMain
public import WaveTurbulence.Foundations.FinalCount.LowGardenClass
/-! **FINALCOUNT-ASSEMBLY (LOW-GARDEN, session 2): `LowLoopData` for a garden (loops allowed).**

`lowLoopData_garden`: for a garden `G` with amended geometry and at least two atoms, an admissible set `Adm` (nonempty), the
`M`-level data `LowLoopData` of the loop transport holds on `M = inlMol G.molecule` (collection `C0 C`, omitted vines `Un0`, first
stage `Fst0`, critical atoms `critMap`, base scale `scaleMap`, `kFix = kFix0 C base`).  All inputs are the garden-level facts of the
REG producers (which hold with loops), the `ε`-support `inl_loop_heq`, `HingeNoLoop`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.AtomTransport WaveTurbulence.MoleProp WaveTurbulence.Mole WaveTurbulence.VineCount

variable {R d : ℕ} {G : Garden (2 * R)}


section helpers
variable (C : CountingChoices G d) {L γ η : ℝ} {base : Mom d} {κ : GardenDart G → (Fin d → ℤ)}

theorem crit_G2 (hadm : C.Admissible L γ η base κ) {U : Object G.molecule}
    (hU : Coll2 (gCol C) (unG C L γ η κ) L γ η 0 κ U) {v : GBranch G.tree} (hv : U.IsInterior v) :
    ¬ C.CriticalSG v := by
  rcases hU with ⟨i, rfl⟩ | hU
  · exact Subpro.not_critical_of_interior_c1 C hv
  · exact not_critical_of_interior_c2' C hadm.2.1 (c2Of_G_base C hU) hv

theorem coll2_map (U : Object (inlMol G.molecule))
    (hU : Coll2 (C0 C) (Un0 C L γ η κ) L γ η 0 κ U) :
    ∃ U0, U = objMap (ι := inlEmb _) U0 ∧ Coll2 (gCol C) (unG C L γ η κ) L γ η 0 κ U0 := by
  rcases hU with ⟨i, rfl⟩ | hU
  · exact ⟨_, rfl, Or.inl ⟨i, rfl⟩⟩
  · obtain ⟨U0, rfl, h⟩ := c2Of0_mem C hU
    exact ⟨U0, rfl, Or.inr h⟩

end helpers

section main
variable (hp : G.IsPlain) (hR : 1 ≤ R) {D : SplicedKernelData G d} {C : CountingChoices G d} (hD : D.hinges = C.subpro.hinges)
  (hg : CountingGeometry G C) (h2a : 2 ≤ G.molecule.atoms.card) {L γ η : ℝ} (hL : 0 < L) {base : Mom d}
  {roots : Fin (2 * R) → (Fin d → ℤ)} {Adm : (GardenDart G → (Fin d → ℤ)) → Prop}
  (hA : ∀ κ, Adm κ → splicedCountingAdmissible G D C L γ η base roots κ) (hne : ∃ κ, Adm κ)

include hp hR hD hg h2a hL hA hne

theorem lowLoopData_garden (m : ℕ) (hcard : ((2 * (inlMol G.molecule).atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m) :
    LowLoopData (d := d) (inlMol G.molecule) R Adm (scaleMap (inlEmb _) C.ladderScale) (C0 C) (Un0 C L γ η) (Fst0 C)
      (critMap (inlEmb _) C) (kFix0 C base) L γ η m := by
  have hL0 : L ≠ 0 := hL.ne'
  have hSG : SubHypLoop R G.molecule := subHypLoop_of_geometry hg hR h2a
  have hS : SubHypLoop R (inlMol G.molecule) := subHypLoop_mapAtoms (inlEmb _) hSG
  have hadm : ∀ κ, Adm κ → C.Admissible L γ η base κ := fun κ hκ => (hA κ hκ).2
  have hgd : ∀ κ, Adm κ → ∃ c, G.molecule.IsDecoration L base c κ ∧ ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0 :=
    fun κ hκ => gdec hp hL0 (hA κ hκ)
  have hz : ∀ κ ∈ {κ | Adm κ}, ∃ z : GenDecoration G d roots 0, ∀ x, bondIndex G z.1 x = κ x := fun κ hκ => by
    obtain ⟨⟨z, hz, -, -⟩, -⟩ := hA κ hκ; exact ⟨z, hz⟩
  obtain ⟨hdec0, hh0, hpin⟩ := class_dec_facts G hp hL0 roots hz
  have hmate : ∀ κ, Adm κ → ∀ x, κ ((inlMol G.molecule).mate x) = κ x := fun κ hκ x => by
    obtain ⟨c, hc, -⟩ := hdec0 κ hκ; exact hc.1 x
  have hC13 : ∀ i, ((C0 C).collection i).atoms.card ≠ 3 := by
    intro i
    show ((C.subpro.collection i).atoms.map (inlEmb _)).card ≠ 3
    rw [Finset.card_map]
    exact Subpro.objVine_card_ne_three (Subpro.objVine_of_allowed (hg.subpro.1 i))
  have hgaps : ∀ κ, Adm κ → SourceLadderGaps (inlMol G.molecule) L 0 (scaleMap (inlEmb _) C.ladderScale) κ := by
    intro κ hκ
    rw [sourceLadderGaps_base_indep (inlMol G.molecule) L 0 base]
    exact (ladderGaps_mapAtoms (inlEmb _) C L γ η base κ).2 (hadm κ hκ).2.2.2.2.2.2.2.2
  have hsgc1 : ∀ κ, Adm κ → ∀ i, ((C0 C).collection i).HasGapKind L γ η 0 κ .SG := by
    intro κ hκ i
    show (objMap (ι := inlEmb _) (C.subpro.collection i)).HasGapKind L γ η 0 κ .SG
    rw [objMap_hasGapKind_iff, object_hasGapKind_base_indep _ L γ η 0 base κ]
    exact (hadm κ hκ).1.selectedSG i
  have hsgh : ∀ κ, Adm κ → ∀ U, Coll2 (C0 C) (Un0 C L γ η κ) L γ η 0 κ U →
      U.HasGapKind L γ η 0 κ .SG ∧ HingeData (C0 C) U := by
    intro κ hκ U hU
    rcases hU with ⟨i, rfl⟩ | hU
    · exact ⟨hsgc1 κ hκ i, hingeData_collection (obl0 C (hadm κ hκ)) i⟩
    · exact ⟨hsg_c2Of hU, hingeData_c2Of hU⟩
  refine
    { hSL := hS
      hmate := hmate
      heq := fun κ hκ => inl_loop_heq hg hD (hA κ hκ)
      hdec := hdec0
      h0 := hh0
      pin := hpin
      hP0 := ?_
      gaps := hgaps
      hH := ?_
      trip := tripleDesig_collMap (inlEmb _) (tripleDesig_LOW hg hR)
      obl := fun κ hκ => obl0 C (hadm κ hκ)
      unsel := fun κ hκ => unselOK0 C (hadm κ hκ)
      degen := ?_
      critSG := ?_
      card := hcard
      sg2 := fun κ hκ U hU => (hsgh κ hκ U hU).1
      des2 := fun κ hκ U hU => (hsgh κ hκ U hU).2
      shape2 := ?_
      crit2 := ?_
      hC1 := ?_
      hC12 := fun κ hκ U hU i => (Subpro.c2Of_disjoint_c1_hinges (C0 C) hU).1 i
      hC22 := fun κ hκ => by
        obtain ⟨c, hc, hc0⟩ := hgd κ hκ
        exact hd22_0 C hc hc0 (hadm κ hκ)
      vc2 := fun κ hκ => by
        obtain ⟨c, hc, hc0⟩ := hgd κ hκ
        exact vcShape0 C hc hc0 (hadm κ hκ)
      hC13 := hC13
      hFst := ?_
      hFstC := ?_
      cn := ?_ }
  · intro S hS'
    obtain ⟨κ, hκ⟩ := hne
    rcases (hgaps κ hκ S hS').1 with h | ⟨-, h, -⟩
    · rw [h]
    · exact le_trans (inv_nonneg.2 hL.le) h
  · intro v hv y hy hl
    obtain ⟨v0, hv0, rfl⟩ := Finset.mem_map.1 hv
    simp only [mapAtoms_atom, mapAtoms_mate, inlEmb_apply, Sum.inl.injEq] at hy hl
    exact hg.hingeNoLoop y (hy ▸ hv0) (hy.trans hl.symm)
  · intro κ hκ
    obtain ⟨c, hc, hc0⟩ := hgd κ hκ
    rw [mapAtoms_degenSGT (inlEmb _), degenSGT_base_indep G.molecule L γ η 0 base]
    refine degenSGT_mono (fun a ha => ?_) (degenSGT_of_support (hadm κ hκ).1)
    exact (mapAtoms_isTame (inlEmb _) L 0 _ a).2 ((isTame_shift G.molecule L base _ κ a).1 ha)
  · intro κ hκ a ha
    obtain ⟨⟨a0, rfl, hlab⟩, -, -⟩ := ha
    rw [mapAtoms_sgat (inlEmb _), sgat_base_indep G.molecule L γ η 0 base]
    exact sgat_of_label (hadm κ hκ) hlab
  · intro κ hκ U hU
    obtain ⟨U0, rfl, hU0⟩ := coll2_map C U hU
    obtain ⟨c, hc, hc0⟩ := hgd κ hκ
    rw [objMap_atoms, Finset.card_map, objVine_objMap_iff]
    rcases hU0 with ⟨i, rfl⟩ | hU0
    · exact Or.inr (Subpro.objVine_of_allowed (hg.subpro.1 i))
    · exact shape_G C hc hc0 (hadm κ hκ) hU0
  · intro κ hκ U hU a ha h1 h2
    obtain ⟨U0, rfl, hU0⟩ := coll2_map C U hU
    rw [objMap_atoms] at ha
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_map.1 ha
    rw [critMap_iff]
    exact crit_G2 C (hadm κ hκ) hU0 ⟨ha0, fun e => h1 (by rw [e]; rfl), fun e => h2 (by rw [e]; rfl)⟩
  · intro i j hij
    show Disjoint ((C.subpro.collection i).atoms.map (inlEmb _)) ((C.subpro.collection j).atoms.map (inlEmb _))
    rw [Finset.disjoint_map]
    exact hg.subpro.2.1 i j hij
  · intro U hU'
    obtain ⟨U0, ⟨⟨i, rfl⟩, -⟩, rfl⟩ := hU'
    exact ⟨i, rfl⟩
  · intro i hvc
    exact ⟨C.subpro.collection i, ⟨⟨i, rfl⟩, (objMap_shape_vc_iff (inlEmb _) _).1 hvc⟩, rfl⟩
  · intro κ hκ ps hps hpw
    refine cnBound_garden hp hR C.subpro hg.subpro ps (fun p hp' => ?_) hpw
    obtain ⟨⟨-, hCD, hJ, hN⟩, hF⟩ := hps p hp'
    exact ⟨hF, hCD, hJ, hN⟩

end main

end WaveTurbulence.FinalCountAsm
