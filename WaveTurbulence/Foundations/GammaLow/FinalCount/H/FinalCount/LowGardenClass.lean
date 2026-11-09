/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGardenClass
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenHost
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGReg1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowGardenClass`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (LOW-GARDEN): `LowClassHyps` for every nonempty class of a loop-free LOW garden.**

`lowClassHyps_loopfree`: for a garden `G` with amended geometry, at least two atoms and no loop (degrees `< 3` are allowed), an
admissible set `Adm` and a nonempty class of a label, all fields of `LowClassHyps` hold on `M₀ = inlMol G.molecule` (base `0`,
`C0`, `Un0`, `Fst0`, `critMap`, hereditary ladder scale): the instantiation of `regClassHyps_garden` with
* `subHypL` from `subHypL_of_geometry` (no degree hypothesis),
* `trip` from `tripleDesig_LOW`,
* `hostConn` from `hostConnL_of` (no degree hypothesis),
* `hostConnFL` from `hostConnF_of` (`hnl` only). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.AtomTransport WaveTurbulence.MoleProp WaveTurbulence.Mole WaveTurbulence.VineCount

section subhyp
variable {V W : Type*} [DecidableEq V] [DecidableEq W] {D : Type*} [Fintype D] [DecidableEq D]

end subhyp

variable {R d : ℕ} {G : Garden (2 * R)}

section main
variable (hp : G.IsPlain) (hR : 1 ≤ R) {D : SplicedKernelData G d} {C : Src.CountingChoices Src.γL G d}
  (hg : Src.CountingGeometry G C) (hnlG : ∀ x, G.molecule.atom x ≠ G.molecule.atom (G.molecule.mate x))
  (h2a : 2 ≤ G.molecule.atoms.card) {L γ η : ℝ} (hL : 0 < L) {base : Mom d}
  {roots : Fin (2 * R) → (Fin d → ℤ)} {Adm : (GardenDart G → (Fin d → ℤ)) → Prop}
  (hA : ∀ κ, Adm κ → Src.splicedCountingAdmissible G D C L γ η base roots κ)

include hp hR hg hnlG h2a hL hA

theorem lowClassHyps_loopfree
    (lab : Finset (GBranch G.tree ⊕ ℕ) × (lowAtoms (inlMol G.molecule) → Option (Mom d)))
    (hne : ∃ κ, κ ∈ classOf Adm L C base lab) (m : ℕ)
    (hcard : ((2 * (inlMol G.molecule).atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m) :
    LowClassHyps (d := d) (inlMol G.molecule) R (heredScale' (inlMol G.molecule) (scaleMap (inlEmb _) C.ladderScale))
      (classOf Adm L C base lab) (C0 C) (Un0 C L γ η) (Fst0 C) (critMap (inlEmb _) C) (fun v => v ∈ lab.1) L γ η m := by
  have hL0 : L ≠ 0 := hL.ne'
  have hSG : SubHypL R G.molecule := subHypL_of_geometry hg hR h2a hnlG
  have hS : SubHypL R (inlMol G.molecule) := subHypL_mapAtoms (inlEmb _) hSG
  have hM₀ : (inlMol G.molecule).IsMolecule := isMolecule_inl hg.molecule
  have hnl : ∀ z, (inlMol G.molecule).atom z ≠ (inlMol G.molecule).atom ((inlMol G.molecule).mate z) := hS.noloop
  have hadm : ∀ κ ∈ classOf Adm L C base lab, C.Admissible L γ η base κ := fun κ hκ => (hA κ hκ.1).2
  have hgd : ∀ κ ∈ classOf Adm L C base lab, ∃ c, G.molecule.IsDecoration L base c κ ∧ ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0 :=
    fun κ hκ => gdec hp hL0 (hA κ hκ.1)
  have hz : ∀ κ ∈ classOf Adm L C base lab, ∃ z : GenDecoration G d roots 0, ∀ x, bondIndex G z.1 x = κ x := fun κ hκ => by
    obtain ⟨⟨z, hz, -, -⟩, -⟩ := hA κ hκ.1; exact ⟨z, hz⟩
  obtain ⟨hdec0, hh0, hpin⟩ := class_dec_facts G hp hL0 roots hz
  have hmate : ∀ κ ∈ classOf Adm L C base lab, ∀ x, κ ((inlMol G.molecule).mate x) = κ x := fun κ hκ x => by
    obtain ⟨c, hc, -⟩ := hdec0 κ hκ; exact hc.1 x
  have hdisj : ∀ κ ∈ classOf Adm L C base lab, ∀ U U' : Src.Object Src.γL (inlMol G.molecule), Collected (C0 C) (Un0 C L γ η κ) L γ η 0 κ U →
      Collected (C0 C) (Un0 C L γ η κ) L γ η 0 κ U' → SameDes U U' ∨ Disjoint U.atoms U'.atoms := by
    intro κ hκ U U' hU hU'
    obtain ⟨c, hc, hc0⟩ := hgd κ hκ
    exact hdisj0 C hg hc hc0 (hadm κ hκ) U U' hU hU'
  have hC13 : ∀ i, ((C0 C).collection i).atoms.card ≠ 3 := by
    intro i
    show ((C.subpro.collection i).atoms.map (inlEmb _)).card ≠ 3
    rw [Finset.card_map]
    exact objVine_card_ne_three (objVine_of_allowed (hg.subpro.1 i))
  have hFstC : ∀ i, (∃ h, ((C0 C).collection i).shape = .vc h) → (C0 C).collection i ∈ Fst0 C := by
    intro i hvc
    exact ⟨C.subpro.collection i, ⟨⟨i, rfl⟩, (objMap_shape_vc_iff (inlEmb _) _).1 hvc⟩, rfl⟩
  have hgaps : ∀ κ ∈ classOf Adm L C base lab, SourceLadderGaps (inlMol G.molecule) L 0 (scaleMap (inlEmb _) C.ladderScale) κ := by
    intro κ hκ
    rw [sourceLadderGaps_base_indep (inlMol G.molecule) L 0 base]
    exact (ladderGaps_mapAtoms (inlEmb _) C L γ η base κ).2 (hadm κ hκ).2.2.2.2.2.2.2.2
  have hP0 : ∀ S ∈ (inlMol G.molecule).maximalLadders, 0 ≤ scaleMap (inlEmb _) C.ladderScale S := by
    intro S hS
    obtain ⟨κ, hκ⟩ := hne
    rcases (hgaps κ hκ S hS).1 with h | ⟨-, h, -⟩
    · rw [h]
    · exact le_trans (inv_nonneg.2 hL.le) h
  refine
    { subHypL := hS
      isMol := hM₀
      hP := ladderHered_heredScale' (inlMol G.molecule) _
      hP0 := heredScale'_nonneg (inlMol G.molecule) hP0
      pinned := hpin
      obl := fun κ hκ => obl0 C (hadm κ hκ)
      trip := ?_
      unsel := fun κ hκ => unselOK0 C (hadm κ hκ)
      degen := ?_
      h0 := hh0
      tameEq := ?_
      mate := hmate
      fix := ?_
      critSG := ?_
      card := hcard
      srcGaps := ?_
      dec := hdec0
      disj := hdisj
      fst := fun κ hκ U hU => hFst0 C hU
      sgC := fun κ hκ U hU => (hsg_hinge0 C (hadm κ hκ) hU).1
      desC := fun κ hκ U hU => (hsg_hinge0 C (hadm κ hκ) hU).2
      shape := fun κ hκ U hU => by obtain ⟨c, hc, hc0⟩ := hgd κ hκ; exact hsh0 C hg hc hc0 (hadm κ hκ) hU
      hostConn := ?_
      critInt := fun κ hκ U hU => hcrit0 C (hadm κ hκ) hU
      cnBound := ?_
      hostConnFL := ?_ }
  · exact tripleDesig_collMap (inlEmb _) (tripleDesig_LOW hg hR)
  · intro κ hκ
    obtain ⟨c, hc, hc0⟩ := hgd κ hκ
    rw [mapAtoms_degenSGT (inlEmb _), degenSGT_base_indep G.molecule L γ η 0 base]
    refine degenSGT_mono (fun a ha => ?_) (degenSGT_of_support (hadm κ hκ).1)
    have hcl := hκ.2.1 (inlEmb _ a) (Finset.mem_map_of_mem _ (Finset.mem_univ a))
    exact hcl.1 ((mapAtoms_isTame (inlEmb _) L 0 _ a).2 ((isTame_shift G.molecule L base _ κ a).1 ha))
  · intro k0 hk0 v hv hvZ x y hx hy
    have ht := (hk0.2.1 v hv).2 hvZ
    exact kvec_injective hL0 0 k0 (ht.1 x y hx hy)
  · intro v hv hvZ hdeg
    by_cases hx : ∃ x, (inlMol G.molecule).atom x = v
    · obtain ⟨x0, hx0⟩ := hx
      obtain ⟨κ1, hκ1⟩ := hne
      refine ⟨κ1 x0, fun k0 hk0 x hx => ?_⟩
      have hlow : v ∈ lowAtoms (inlMol G.molecule) := Finset.mem_filter.2 ⟨hv, hdeg⟩
      have e1 := hk0.2.2 ⟨v, hlow⟩ hvZ x hx
      have e2 := hκ1.2.2 ⟨v, hlow⟩ hvZ x0 hx0
      rw [e1] at e2
      have e3 := Option.some.inj e2
      unfold Molecule.kvec at e3
      exact latticePoint_injective' hL0 (add_left_cancel e3)
    · push Not at hx
      exact ⟨0, fun k0 _ x hx' => absurd hx' (hx x)⟩
  · intro κ hκ a ha
    obtain ⟨⟨a0, rfl, hlab⟩, -, -⟩ := ha
    rw [mapAtoms_sgat (inlEmb _), sgat_base_indep G.molecule L γ η 0 base]
    exact sgat_of_label (hadm κ hκ) hlab
  · intro κ hκ
    obtain ⟨c, hc, hc0⟩ := hdec0 κ hκ
    exact sourceLadderGaps_hered hM₀ hc hc0 (hgaps κ hκ)
  · intro κ hκ ps U a x b hps hpw hdis hUc hUat hax hxb hab hclos
    obtain ⟨c, hc, hc0⟩ := hgd κ hκ
    obtain ⟨c', hc', hc0'⟩ := hdec0 κ hκ
    exact hostConnL_of hM₀ hc' hc0' (hd22_0 C hc hc0 (hadm κ hκ)) (vcShape0 C hc hc0 (hadm κ hκ)) (unselOK0 C (hadm κ hκ))
      hnl hC13 ps U a x b hps hpw hdis hUc hUat hax hxb hab hclos
  · intro κ hκ ps hps hpw
    refine cnBound_garden hp hR C.subpro hg.subpro ps (fun p hp' => ?_) hpw
    obtain ⟨⟨-, hCD, hJ, hN⟩, hF⟩ := hps p hp'
    exact ⟨hF, hCD, hJ, hN⟩
  · refine hostConnFL_of ?_
    intro κ hκ ps p hps hp' hpF hpw
    obtain ⟨c, hc, hc0⟩ := hgd κ hκ
    obtain ⟨c', hc', hc0'⟩ := hdec0 κ hκ
    exact hostConnF_of hM₀ hc' hc0' (hd22_0 C hc hc0 (hadm κ hκ)) (vcShape0 C hc hc0 (hadm κ hκ))
      (unselOK0 C (hadm κ hκ)) hnl hFstC ps p hps hp' hpF hpw

end main

end WaveTurbulence.GammaLow.FinalCount.H
