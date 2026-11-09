/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Step5b
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Step5a
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAdm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCoords
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCDict
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCExcess
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCFlow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCGain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCInj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCLadProd
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCScale
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCSource
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCStmt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Gaps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3Step5b`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3 (step 5a, part 2): the joints stay connected when the outer object does** (TARGET L2128 last sentence, L2167).

`VineOutsideConn K G` is the adjacency chain of the universe's `removeBlocks M U₂ [P]` read in `M`: bonds of `M` between atoms that are not
interior atoms of the removed object `K.C`, no dart of which belongs to the group darts `G ⊇ {x₁, x₂, y₁, y₂}` of `K.C`.  It is the
exact output of `subsetvc_simultaneous_removal_connected` (hypotheses `hD : P.darts = univ.filter (M.InGroup P.atoms)`; `KeepDart`).
`vineCut_F_le_of_outside`: `VineOutsideConn K G → K.post.numComponents ≤ M.numComponents` (so `ΔF = 0`, `vine_F_alpha_iff`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- The interior atoms of the removed object (everything but the two joints). -/
def vineInterior (K : Step1.VineCut Src.γL M) : Finset V := K.C.atoms \ {K.C.upper, K.C.lower}

/-- Connectivity of the joints through the bonds that are neither interior atoms nor bonds of the object (`G`). -/
def VineOutsideConn (K : Step1.VineCut Src.γL M) (G : Finset D) : Prop :=
  Relation.EqvGen (fun s t : V => s ∉ vineInterior K ∧ t ∉ vineInterior K ∧
    ∃ z, M.atom z = s ∧ M.atom (M.mate z) = t ∧ z ∉ G ∧ M.mate z ∉ G) K.C.upper K.C.lower

/-- The image of an atom of `M` in the post molecule (joints go to the fresh joints). -/
def hPost (K : Step1.VineCut Src.γL M) (s : V) : V := if s = K.C.upper then K.fa else if s = K.C.lower then K.fb else s

theorem cutMol_atom_outside (K : Step1.VineCut Src.γL M) {G : Finset D} (hG : ∀ z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D), z ∈ G)
    {z : D} (hz : z ∉ G) : K.cutMol.atom z = hPost K (M.atom z) := by
  have hx1 : z ≠ K.x₁ := fun e => hz (hG _ (by simp [e]))
  have hx2 : z ≠ K.x₂ := fun e => hz (hG _ (by simp [e]))
  have hy1 : z ≠ K.y₁ := fun e => hz (hG _ (by simp [e]))
  have hy2 : z ≠ K.y₂ := fun e => hz (hG _ (by simp [e]))
  have e2 : K.cutMol.atom z = (K.m1.cut K.C.lower K.fb K.y₁ K.y₂).atom z := rfl
  rw [e2, cut_atom, show K.m1.atom z = (M.cut K.C.upper K.fa K.x₁ K.x₂).atom z from rfl, cut_atom]
  by_cases c1 : M.atom z = K.C.upper
  · have i0 : (if M.atom z = K.C.upper ∧ z ≠ K.x₁ ∧ z ≠ K.x₂ then K.fa else M.atom z) = K.fa :=
      if_pos ⟨c1, hx1, hx2⟩
    rw [i0]
    have : ¬ (K.fa = K.C.lower ∧ z ≠ K.y₁ ∧ z ≠ K.y₂) := fun h => K.fa_ne_b h.1
    rw [if_neg this]
    simp [hPost, c1]
  · have i1 : (if M.atom z = K.C.upper ∧ z ≠ K.x₁ ∧ z ≠ K.x₂ then K.fa else M.atom z) = M.atom z :=
      if_neg (fun h => c1 h.1)
    rw [i1]
    by_cases c2 : M.atom z = K.C.lower
    · rw [if_pos ⟨c2, hy1, hy2⟩]
      simp [hPost, c2, K.ab_ne.symm]
    · rw [if_neg (fun h => c2 h.1)]
      simp [hPost, c1, c2]

theorem hPost_not_C (K : Step1.VineCut Src.γL M) {s : V} (hs : s ∈ M.atoms) (hsi : s ∉ vineInterior K) : hPost K s ∉ K.C.atoms := by
  unfold hPost
  by_cases e1 : s = K.C.upper
  · rw [if_pos e1]; exact fun h => K.fa_fresh (Step1.objectAtoms_sub K.C h)
  by_cases e2 : s = K.C.lower
  · rw [if_neg e1, if_pos e2]; exact fun h => K.fb_fresh (Step1.objectAtoms_sub K.C h)
  · rw [if_neg e1, if_neg e2]
    intro h
    exact hsi (by unfold vineInterior; simp [h, e1, e2])

theorem vine_fafb_of_outside (K : Step1.VineCut Src.γL M) {G : Finset D}
    (hG : ∀ z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D), z ∈ G) (hr : VineOutsideConn K G) :
    K.post.SameComponent K.fa K.fb := by
  have key : ∀ a b : V, Relation.EqvGen (fun s t : V => s ∉ vineInterior K ∧ t ∉ vineInterior K ∧
      ∃ z, M.atom z = s ∧ M.atom (M.mate z) = t ∧ z ∉ G ∧ M.mate z ∉ G) a b →
      K.post.SameComponent (hPost K a) (hPost K b) := by
    intro a b hab
    induction hab with
    | rel s t hst =>
      obtain ⟨hs, ht, z, hz1, hz2, hzG, hmG⟩ := hst
      have e1 := cutMol_atom_outside K hG hzG
      have e2 : K.cutMol.atom (K.cutMol.mate z) = hPost K (M.atom (M.mate z)) :=
        cutMol_atom_outside K hG hmG
      rw [hz1] at e1; rw [hz2] at e2
      have hn1 : K.cutMol.atom z ∉ K.C.atoms := by
        rw [e1]; exact hPost_not_C K (hz1 ▸ M.atom_mem z) hs
      exact Relation.EqvGen.rel _ _ (show K.post.Adj (hPost K s) (hPost K t) from
        ⟨⟨z, hn1⟩, e1, e2⟩)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have := key _ _ hr
  have h1 : hPost K K.C.upper = K.fa := by simp [hPost]
  have h2 : hPost K K.C.lower = K.fb := by simp [hPost, K.ab_ne.symm]
  rwa [h1, h2] at this

/-- **Step 5a.** A Step-1 VC whose joints are connected outside it (the output of `subsetvc`, TARGET L2128) creates no new component:
`ΔF = 0`.  For a `Step1.DoubleShape K` this is the hypothesis `hconn` that the old statement lacked (it is false for a dumbbell). -/
theorem vineCut_F_le_of_outside (K : Step1.VineCut Src.γL M) {G : Finset D}
    (hG : ∀ z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D), z ∈ G) (hr : VineOutsideConn K G) :
    K.post.numComponents ≤ M.numComponents :=
  vine_F_le_of_sc K (vine_fafb_of_outside K hG hr)

theorem doubleShape_F_le (K : Step1.VineCut Src.γL M) (_S : Step1.DoubleShape K) {G : Finset D}
    (hG : ∀ z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D), z ∈ G) (hr : VineOutsideConn K G) :
    K.post.numComponents ≤ M.numComponents :=
  vineCut_F_le_of_outside K hG hr

end WaveTurbulence.GammaLow.FinalCount.H
