/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GV08
public import WaveTurbulence.Foundations.FinalCount.G3VineLG4
public import WaveTurbulence.Foundations.FinalCount.GM04
/-! **G3-LOWDEG port of `G3VineLG4`** (only the declarations that change: `SubHypL->SubHypL`, `HRunL->HRunL`, `InvL->InvL`, `FinalStructM->FinalStructM`, `Prop95ConclAtL->Prop95ConclAtL`; names get suffix `L`). -/
@[expose] public section
open WaveTurbulence.VineParamContract

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {Tm : V → Prop}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀} {a₀ j₁ j₂ : V}

/-- Two darts at an `ε`-atom of the final molecule that are distinct bonds of opposite directions have LG gap. -/
theorem eps_pair_LGL (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s) (hC : Prop95ConclAtL L γ η w κ R hf Tm) {c : V}
    (hc : c ∈ hf.s.M.atoms) (hε : hf.s.cls c = .eps) (hT : TameFree hf Tm c) {f s : D₀} (hf1 : M₀.atom f = c) (hs1 : M₀.atom s = c)
    (hfs : s ≠ M₀.mate f) (hout : M₀.out f ≠ M₀.out s) : Molecule.gapKind L γ η (Molecule.gapAt L w κ f s) = .LG := by
  obtain ⟨x, rfl⟩ := hA.surj c hc hε f hf1
  obtain ⟨y, rfl⟩ := hA.surj c hc hε s hs1
  have hax : hf.s.M.atom x = c := hA.uniq _ (hf.s.M.atom_mem x) c hc hε (by rw [← hA.atom x]; exact hf1)
  have hay : hf.s.M.atom y = c := hA.uniq _ (hf.s.M.atom_mem y) c hc hε (by rw [← hA.atom y]; exact hs1)
  have hxo : hf.s.M.out x = M₀.out (hf.s.down x) := (hD.out x).symm
  have hyo : hf.s.M.out y = M₀.out (hf.s.down y) := (hD.out y).symm
  have hne : ∀ {p q : hf.s.D}, M₀.mate (hf.s.down p) ≠ hf.s.down q → q ≠ hf.s.M.mate p := by
    intro p q h e; apply h; rw [hD.mate, e]
  cases hfo : M₀.out (hf.s.down x)
  · have hso : M₀.out (hf.s.down y) = true := by
      cases h : M₀.out (hf.s.down y)
      · exact absurd (hfo.trans h.symm) hout
      · rfl
    exact hC.eps_LG c hc hε hT x y hax hay (by rw [hxo, hfo]) (by rw [hyo, hso])
      (hne (fun e => hfs e.symm))
  · have hso : M₀.out (hf.s.down y) = false := by
      cases h : M₀.out (hf.s.down y)
      · rfl
      · exact absurd (hfo.trans h.symm) hout
    have := hC.eps_LG c hc hε hT y x hay hax (by rw [hyo, hso]) (by rw [hxo, hfo])
      (hne (fun e => hfs (by rw [← e, M₀.mate_mate])))
    change Molecule.gapKind L γ η (Molecule.gapAt L w κ (hf.s.down y) (hf.s.down x)) = _ at this
    have hsw : Molecule.gapAt L w κ (hf.s.down y) (hf.s.down x) = -Molecule.gapAt L w κ (hf.s.down x) (hf.s.down y) := by
      unfold Molecule.gapAt; abel
    rw [hsw] at this
    rwa [gapKind_eq_of_norm_eq (L := L) (γ := γ) (η := η) (norm_neg (Molecule.gapAt L w κ (hf.s.down x) (hf.s.down y)))] at this

/-- (iii) a hinge in the interior of `P` is an `ε`-atom of the final molecule. -/
theorem hinge_interiorL (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s) (hC : Prop95ConclAtL L γ η w κ R hf Tm) (hT : TameFree hf Tm a₀)
    (J : FinalJoints hf a₀ j₁ j₂) {v : V} (hv : v ∈ AncGroup hf a₀) (h1 : v ≠ hf.anc j₁) (h2 : v ≠ hf.anc j₂)
    {f s : D₀} (ht : TripleAtM M₀ v f s)
    (hsg : Molecule.gapKind L γ η (Molecule.gapAt L w κ f s) = .SG) : False := by
  obtain ⟨c, hc, hca⟩ := Finset.mem_image.1 hv
  obtain ⟨hcm, hcc⟩ := (mem_compMol _ _).1 hc
  rcases J.comp c hcm hcc with rfl | rfl | ⟨hε, -⟩
  · exact h1 hca.symm
  · exact h2 hca.symm
  · have hac : hf.anc c = c := hA.eps c hcm hε
    have hvc : v = c := by rw [← hca, hac]
    have := eps_pair_LGL hA hD hC hcm hε (hT.of_sc hcc) (f := f) (s := s) (by rw [ht.1, hvc]) (by rw [ht.2.1, hvc]) ht.2.2.1
      (fun e => ht.2.2.2 e)
    rw [hsg] at this
    exact Molecule.GapKind.noConfusion this

/-- (iv) at a joint, the designated pair is held entirely by the joint half or not at all.  The recorded pair `p0` of the joint is the
designated pair or its complement (R29, A1 / `Desig`). -/
theorem hinge_joint_xorL {R₀ : ℕ} {P : Object M₀} (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s) (hS : SubHypL R₀ M₀)
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
    have hinj := J.injOnL hA hD hS
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

end WaveTurbulence.FinalCountG3

