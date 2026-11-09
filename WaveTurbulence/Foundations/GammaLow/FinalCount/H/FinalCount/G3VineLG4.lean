/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineLG4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Dart
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3FinalCopy
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Prop95
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3VineLG4`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: `vineLG`, part 4: no final vine component is SG.**

The case analysis of DH23 L1814 (TARGET `subpro`): an SG object `P` of `M_sub` (the ancestor object of a final vine component) is
(i) contained in a member of `C₁` or `C₂` (impossible: Step 1 removed that member, but the component has a final dart in it),
(ii) the unselected vine of a DV (`residual_unsel`), (iii) crossing a hinge in its interior (the interior atom is an `ε`-atom of the
final molecule, which is LG, but the hinge is SG), (iv) having a hinge at a joint with exactly one designated dart in `P` (impossible:
the joint half of the cut along the designated pair holds both darts or neither). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {Tm : V → Prop}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀} {a₀ j₁ j₂ : V}

theorem Src.Object.atoms_subset_of_contained {P Q : Src.Object Src.γL M₀} (h : P.IsContained Q) : P.atoms ⊆ Q.atoms := by
  unfold Src.Object.IsContained at h
  rcases hP : P.shape with hp | hp <;> rcases hQ : Q.shape with hq | hq <;>
    simp only [hP, hQ, Src.VineLikeObject.IsContained] at h
  · exact h
  · exact h
  · exact h
  · exact h.1

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.atoms_subset_of_contained := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.Object.atoms_subset_of_contained
def DesRec (C : CollData M₀) (hf : HSt V D₀) : Prop :=
  ∀ j ∈ hf.s.M.atoms, ∀ p vis, hf.crec j = some (p, vis) → hf.anc j ∈ C.hinges →
    ∃ f s, C.first (hf.anc j) = some f ∧ C.second (hf.anc j) = some s ∧ ({p.1, p.2} : Set D₀) = {f, s}

/-- (iv) at a joint, the designated pair is held entirely by the joint half or not at all.  The recorded pair `p0` of the joint is the
designated pair or its complement (R29, A1 / `Desig`). -/
theorem hinge_joint_xor {R₀ : ℕ} {P : Src.Object Src.γL M₀} (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s) (hS : SubHyp R₀ M₀)
    (J : FinalJoints hf a₀ j₁ j₂) (hPa : ∀ x : hf.s.D, hf.s.M.SameComponent a₀ (hf.s.M.atom x) → P.ContainsDart (hf.s.down x))
    (hPb : ∀ z, P.ContainsDart z → ∃ x : hf.s.D, hf.s.M.SameComponent a₀ (hf.s.M.atom x) ∧ hf.s.down x = z)
    {j : V} {p0 : D₀ × D₀} (hjc : j = j₁ ∨ j = j₂) (hdp : DPOk (DSet hf.s j) p0) {f s : D₀}
    (hp : ({p0.1, p0.2} : Set D₀) = {f, s} ∨
      ({p0.1, p0.2} : Set D₀) = (↑(M₀.dartsAt (hf.anc j)) : Set D₀) \ {f, s})
    (hfsne : f ≠ s) (hjd : hf.s.M.deg j = 2) (hf1 : M₀.atom f = hf.anc j) (hs1 : M₀.atom s = hf.anc j) :
    ¬ Xor (P.ContainsDart f) (P.ContainsDart s) := by
  have hjm : j ∈ hf.s.M.atoms := by rcases hjc with rfl | rfl; exacts [J.m1, J.m2]
  have hjcomp : hf.s.M.SameComponent a₀ j := by rcases hjc with rfl | rfl; exacts [J.c1, J.c2]
  have key : ∀ z, M₀.atom z = hf.anc j → P.ContainsDart z → z ∈ DSet hf.s j := by
    intro z hz hPz
    obtain ⟨x, hxc, rfl⟩ := hPb z hPz
    refine ⟨x, ?_, rfl⟩
    have hxm := hf.s.M.atom_mem x
    have : hf.anc (hf.s.M.atom x) = hf.anc j := by rw [← hA.atom, hz]
    have hinj := J.injOn hA hD hS
    exact hinj ((mem_compMol _ _).2 ⟨hxm, hxc⟩) ((mem_compMol _ _).2 ⟨hjm, hjcomp⟩) this
  have hin : ∀ z ∈ DSet hf.s j, P.ContainsDart z := by
    rintro z ⟨x, hx, rfl⟩
    exact hPa x (by rw [hx]; exact hjcomp)
  have hboth : (f ∈ DSet hf.s j ∧ s ∈ DSet hf.s j) ∨ (f ∉ DSet hf.s j ∧ s ∉ DSet hf.s j) := by
    rcases hp with hp | hp
    · rcases hdp with he | hdis
      · left; rw [he, hp]; simp
      · right
        constructor <;> intro h <;> refine Set.disjoint_left.1 hdis h ?_ <;> rw [hp] <;> simp
    · rcases hdp with he | hdis
      · right
        rw [he, hp]
        simp
      · -- `DSet j ⊆ {f,s}` and `|DSet j| = 2`
        left
        have hsub : DSet hf.s j ⊆ ↑(M₀.dartsAt (hf.anc j)) := by
          rintro z ⟨x, hx, rfl⟩
          rw [Finset.mem_coe, mem_dartsAt, hA.atom x, hx]
        have hsub2 : DSet hf.s j ⊆ {f, s} := by
          intro z hz
          by_contra hn
          have : z ∈ (↑(M₀.dartsAt (hf.anc j)) : Set D₀) \ {f, s} := ⟨hsub hz, hn⟩
          rw [← hp] at this
          exact Set.disjoint_left.1 hdis hz this
        set S : Finset D₀ := (hf.s.M.dartsAt j).image hf.s.down with hSdef
        have hSeq : (↑S : Set D₀) = DSet hf.s j := by
          ext z; simp [hSdef, DSet, Molecule.dartsAt]
        have hScard : S.card = 2 := by
          rw [hSdef, Finset.card_image_of_injective _ hA.inj]
          exact hjd
        have hSsub : S ⊆ {f, s} := by
          intro z hz
          have : z ∈ DSet hf.s j := by rw [← hSeq]; exact hz
          simpa using hsub2 this
        have hSeq2 : S = {f, s} := Finset.eq_of_subset_of_card_le hSsub (by rw [hScard, Finset.card_pair hfsne])
        have hfS : f ∈ S := by rw [hSeq2]; simp
        have hsS : s ∈ S := by rw [hSeq2]; simp
        constructor
        · rw [← hSeq]; exact hfS
        · rw [← hSeq]; exact hsS
  rcases hboth with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [Xor, hin f h1, hin s h2]
  · have hnf : ¬ P.ContainsDart f := fun h => h1 (key f hf1 h)
    have hns : ¬ P.ContainsDart s := fun h => h2 (key s hs1 h)
    simp [Xor, hnf, hns]

end WaveTurbulence.GammaLow.FinalCount.H
