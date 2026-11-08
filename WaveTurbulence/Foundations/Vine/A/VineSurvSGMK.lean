/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK3
public import WaveTurbulence.Foundations.FinalCount.SubproGap
public import WaveTurbulence.Foundations.FinalCount.SubproGap2
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: survivors are small-gap on the support (o75 Theorem 7.5′(2); `SubproSupportMK.survivorSG`)

On any decoration of `G_sb` on which the gap indicator of `gapSpecificationMk` does not vanish, every survivor object
with an ordinary (`vc`) shape has small gap: its entry (ruling R171, one per survivor, at the image of its upper joint)
is a lift of its own pair (`survivor_upper_inj`), of kind `σ S = SG`.

`survObj_SG_vc` covers the `vc` survivors.  `survObj_containsDart`: a bond of the survivor in `G` lifts to a bond of
its image object, also for the HV of a one-survivor HVC (75-W1), whose added bond is not a survivor bond
(`survObj_hyper_added`).  `survObj_SG`: every survivor is small-gap on the support.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1
  WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

section main
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
include hM

/-- **Distinct survivors of one group have distinct upper-joint images.** -/
theorem survivor_upper_inj {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hmk : markedGroup G Mk S)
    {t t' : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ (markedUnitsOfMK hmk).surv) (ht' : t' ∈ (markedUnitsOfMK hmk).surv)
    (he : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t'.2.1 = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1) :
    t' = t := by
  classical
  by_contra hne
  obtain ⟨D', _, _, N, L, a, b, -, hs, -, -, hvineM, hingr, hmemb, hsub, hmem⟩ := (markedUnitsOfMK hmk).surv_spine
  have hsurvL : ∀ x ∈ L, (x ∈ (markedUnitsOfMK hmk).surv ↔ ¬ UnmMemMK G Mk x) := hmem
  have htL := hsub.subset ht
  have ht'L := hsub.subset ht'
  obtain ⟨X, hX⟩ := hvineM t htL
  obtain ⟨X', hX'⟩ := hvineM t' ht'L
  obtain ⟨P, R, Q, hL, -⟩ := left_neighbor hM σ hS hσ hmk hs hvineM hingr hmemb hsurvL ht htL ht' ht'L
    (Ne.symm hne) hX'.1.2.1 he.symm
  obtain ⟨P', R', Q', hL', -⟩ := left_neighbor hM σ hS hσ hmk hs hvineM hingr hmemb hsurvL ht' ht'L ht htL
    hne hX.1.2.1 he
  have hnd := hs.nodupMK
  have e : P ++ t' :: (R ++ t :: Q) = (P' ++ t :: R') ++ t' :: Q' := by rw [← hL, hL']; simp
  have hnd' : (P ++ t' :: (R ++ t :: Q)).Nodup := hL ▸ hnd
  obtain ⟨hP, -⟩ := app_cons_inj_of_nodupMK hnd' e
  have htP : t ∈ P := by rw [hP]; simp
  exact (List.nodup_append.mp hnd').2.2 t htP t (by simp) rfl

/-- The atom of a lifted dart is the image of the atom of the original dart. -/
theorem atom_lift {y : GardenDart (stSt G σ Mk).G} :
    (stSt G σ Mk).G.molecule.atom y =
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (G.molecule.atom ((stSt G σ Mk).M.od y)) := by
  apply (stSt G σ Mk).M.ob_inj
  rw [(stSt G σ Mk).M.ob_atom, (stSt G σ Mk).M.ob_pi]

/-- **A `vc` survivor is small-gap on the support** (`SubproSupportMK.survivorSG`). -/
theorem survObj_SG_vc {d : ℕ} (L γ η : ℝ) (base : Mom d) (zsb : GNode (stSt G σ Mk).G.tree → (Fin d → ℤ))
    (D : SplicedKernelData (stSt G σ Mk).G d) (hD : D.gapSpecification = gapSpecificationMk G σ Mk)
    (hZ : splicedGapIndicator (stSt G σ Mk).G D L γ η base zsb ≠ 0)
    (hdec : ∃ c : GBranch (stSt G σ Mk).G.tree → Mom d,
      (stSt G σ Mk).G.molecule.IsDecoration L base c (bondIndex (stSt G σ Mk).G zsb) ∧
        ∀ v ∈ (stSt G σ Mk).G.molecule.atoms, (stSt G σ Mk).G.molecule.deg v = 4 → c v = 0)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ survivorsMk G σ Mk)
    (hvc : ∃ hv, (survObj ht).shape = VineLikeObject.vc hv) :
    (survObj ht).HasGapKind L γ η base (bondIndex (stSt G σ Mk).G zsb) Molecule.GapKind.SG := by
  obtain ⟨c, hκ, hc0⟩ := hdec
  obtain ⟨S, hS, hσ, hmk, htm, -⟩ := survivorsMk_group ht
  obtain ⟨t', p, ht', hv, ⟨⟨hpx, hpy, -, -⟩, hgx, hgy⟩, e, he, hk, h1, h2⟩ :=
    gapSpecificationMk_marked hM σ hS hmk htm
  have htt := survivor_upper_inj hM σ hS hσ hmk htm ht' hv
  subst htt
  have hgap := Subpro.gapKind_of_Z (stSt G σ Mk).G D L γ η base zsb hZ (q := e) (by rw [hD]; exact he)
  rw [hk, hσ] at hgap
  obtain ⟨hat, hup, -, -, -, -, -⟩ := survObj_spec ht
  obtain ⟨hv0, hsh⟩ := hvc
  -- the two darts of the entry lie in the survivor object
  have hin : ∀ y : GardenDart (stSt G σ Mk).G, (stSt G σ Mk).M.od y = p.1 ∨ (stSt G σ Mk).M.od y = p.2 →
      (survObj ht).ContainsDart y := by
    intro y hy
    unfold Object.ContainsDart
    rw [hsh]
    have hg : G.molecule.InGroup t'.1 ((stSt G σ Mk).M.od y) := by rcases hy with h | h <;> rw [h] <;> assumption
    refine ⟨?_, ?_⟩
    · rw [atom_lift hM σ, hat]
      exact Finset.mem_image_of_mem _ hg.1
    · rw [atom_lift hM σ, hat, (stSt G σ Mk).M.od_mate]
      exact Finset.mem_image_of_mem _ hg.2
  have hj : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t'.2.1 = (survObj ht).upper := hup.symm
  exact Subpro.hasGapKind_of_pair_joint (stSt G σ Mk).G L γ η base c _ hκ hc0 (survObj ht) (Or.inl hj)
    e.at_first e.at_second (hin _ (Or.inl h1)) (hin _ (Or.inr h2)) e.opposite hgap

/-- **A bond of a survivor lifts to a bond of its image object** (both shapes; for the 75-W1 HV, the added bond is not
a survivor bond). -/
theorem survObj_containsDart {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ survivorsMk G σ Mk) {y : GardenDart (stSt G σ Mk).G}
    (hy : G.molecule.InGroup t.1 ((stSt G σ Mk).M.od y)) : (survObj ht).ContainsDart y := by
  obtain ⟨hat, -⟩ := survObj_spec ht
  have hg : (stSt G σ Mk).G.molecule.InGroup (survObj ht).atoms y := by
    refine ⟨?_, ?_⟩
    · rw [atom_lift hM σ, hat]
      exact Finset.mem_image_of_mem _ hy.1
    · rw [atom_lift hM σ, hat, (stSt G σ Mk).M.od_mate]
      exact Finset.mem_image_of_mem _ hy.2
  unfold Object.ContainsDart
  split
  · exact hg
  · rename_i R hR
    refine ⟨fun h => ?_, fun h => ?_, hg⟩
    · exact survObj_hyper_added ht hR (h ▸ hy)
    · apply survObj_hyper_added ht hR
      rw [h, (stSt G σ Mk).M.od_mate] at hy
      exact ⟨by simpa only [G.molecule.mate_mate] using hy.2, hy.1⟩

/-- **Every survivor is small-gap on the support** (o75 Theorem 7.5′(2); `SubproSupportMK.survivorSG`), including
the HV of a one-survivor HVC (75-W1). -/
theorem survObj_SG {d : ℕ} (L γ η : ℝ) (base : Mom d) (zsb : GNode (stSt G σ Mk).G.tree → (Fin d → ℤ))
    (D : SplicedKernelData (stSt G σ Mk).G d) (hD : D.gapSpecification = gapSpecificationMk G σ Mk)
    (hZ : splicedGapIndicator (stSt G σ Mk).G D L γ η base zsb ≠ 0)
    (hdec : ∃ c : GBranch (stSt G σ Mk).G.tree → Mom d,
      (stSt G σ Mk).G.molecule.IsDecoration L base c (bondIndex (stSt G σ Mk).G zsb) ∧
        ∀ v ∈ (stSt G σ Mk).G.molecule.atoms, (stSt G σ Mk).G.molecule.deg v = 4 → c v = 0)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ survivorsMk G σ Mk) :
    (survObj ht).HasGapKind L γ η base (bondIndex (stSt G σ Mk).G zsb) Molecule.GapKind.SG := by
  obtain ⟨c, hκ, hc0⟩ := hdec
  obtain ⟨S, hS, hσ, hmk, htm, -⟩ := survivorsMk_group ht
  obtain ⟨t', p, ht', hv, ⟨⟨hpx, hpy, -, -⟩, hgx, hgy⟩, e, he, hk, h1, h2⟩ :=
    gapSpecificationMk_marked hM σ hS hmk htm
  have htt := survivor_upper_inj hM σ hS hσ hmk htm ht' hv
  subst htt
  have hgap := Subpro.gapKind_of_Z (stSt G σ Mk).G D L γ η base zsb hZ (q := e) (by rw [hD]; exact he)
  rw [hk, hσ] at hgap
  obtain ⟨-, hup, -⟩ := survObj_spec ht
  have hj : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t'.2.1 = (survObj ht).upper := hup.symm
  exact Subpro.hasGapKind_of_pair_joint (stSt G σ Mk).G L γ η base c _ hκ hc0 (survObj ht) (Or.inl hj)
    e.at_first e.at_second (survObj_containsDart hM σ ht (h1 ▸ hgx)) (survObj_containsDart hM σ ht (h2 ▸ hgy))
    e.opposite hgap

end main

end WaveTurbulence.VineA.NormalizedSplice
