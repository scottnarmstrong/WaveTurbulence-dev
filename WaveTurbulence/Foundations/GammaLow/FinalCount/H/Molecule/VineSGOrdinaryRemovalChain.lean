/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineSGOrdinaryRemovalChain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineOrdinarySplit
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGOrdinaryRemovalSingle
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGSplitJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineSGOrdinaryRemovalChain`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Simultaneous ordinary SG-vine removals in an LG/ZG vine chain -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc, ordinary removal in a chain: the source gap excludes
every shared junction from the removed pieces. Local surviving paths in
the two sides therefore glue at a retained junction. -/
theorem SG_ordinary_vines_removal_in_chain_connected (M : Molecule V D) (hM : M.IsMolecule)
    (L γ η : ℝ) (w : Mom d) (z : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w z κ) (hz : ∀ v ∈ M.atoms,M.deg v=4 → z v=0)
    {U : Finset V} {a b : V} {n : ℕ} (hchain : Src.Chain Src.γL M U a b n) :
    M.IsBlock U a b → ∀ (ps : List (RemovalPiece V D)),
    (∀ P ∈ ps,Src.IsSomeVine Src.γL M P.atoms P.left P.right) →
    (∀ P ∈ ps,P.atoms ⊆ U) →
    (∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms)) →
    (∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms) →
    ∀ r : Mom d,M.IsBlockGap L w κ U a r →
    (Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG) →
    (∀ P ∈ ps,∃ r' : Mom d,M.IsBlockGap L w κ P.atoms P.left r' ∧
      Molecule.gapKind L γ η r'=.SG) →
    ∀ u ∈ remainingAtoms U ps,∀ v ∈ remainingAtoms U ps,(removeBlocks M U ps).SameComponent u v := by
  induction hchain with
  | single h =>
    intro _hU ps hvine hsub hD hdis r hr houter hSG
    have hX := h
    exact SG_ordinary_vines_removal_in_single_vine_connected M hM hX ps hvine hsub hD hdis
      L γ η w z κ hκ hz hr houter hSG
  | @append S T a b c n hS hT hi _hne ih =>
    intro hU ps hvine hsub hD hdis r hr houter hSG
    have hT := hT
    have hprefix := chain_prefix_isBlock M hM hS hT hi hU
    let k := Molecule.kvec L w κ
    have hk (d : D) : k (M.mate d)=k d := by simp only [k,Molecule.kvec,hκ.1 d]
    have hcons : ∀ v ∈ M.atoms,M.deg v=4 → ∑ d ∈ M.dartsAt v,M.dartSign d • k d=0 :=
      fun v hv hd => (hκ.2 v hv).trans (hz v hv hd)
    have hNoB : ∀ P ∈ ps,b ∉ P.atoms := by
      intro P hP
      have hY := hvine P hP
      obtain ⟨rP,hrP,hsgP⟩ := hSG P hP
      exact SG_VC_split_joint_absent M hM hS hT hi hU ⟨hY.block, 1, Src.Chain.single hY⟩ (hsub P hP)
        L γ η w z κ hκ hz hr hrP houter hsgP
    have hparts : ∀ P ∈ ps,(P.atoms ⊆ S ∧ Disjoint P.atoms T) ∨
        (P.atoms ⊆ T ∧ Disjoint P.atoms S) := by
      intro P hP
      exact ordinary_vine_split_disjoint M hM hS hT hi hU (hvine P hP) (hsub P hP) (hNoB P hP)
    classical
    let qs := ps.filter (fun P => P.atoms ⊆ S)
    let ts := ps.filter (fun P => P.atoms ⊆ T)
    have hqs (P : RemovalPiece V D) (hP : P ∈ qs) : P ∈ ps := (List.mem_filter.mp hP).1
    have hts (P : RemovalPiece V D) (hP : P ∈ ts) : P ∈ ps := (List.mem_filter.mp hP).1
    have hqsSub : ∀ P ∈ qs,P.atoms ⊆ S :=
      fun P hP => of_decide_eq_true (List.mem_filter.mp hP).2
    have htsSub : ∀ P ∈ ts,P.atoms ⊆ T :=
      fun P hP => of_decide_eq_true (List.mem_filter.mp hP).2
    have hqsParts : ∀ P ∈ ps,P ∈ qs ∨ Disjoint P.atoms S := by
      intro P hP
      rcases hparts P hP with ⟨hPS,_hPT⟩ | ⟨_hPT,hPS⟩
      · exact Or.inl (List.mem_filter.mpr ⟨hP,by simpa using hPS⟩)
      · exact Or.inr hPS
    have htsParts : ∀ P ∈ ps,P ∈ ts ∨ Disjoint P.atoms T := by
      intro P hP
      rcases hparts P hP with ⟨_hPS,hPT⟩ | ⟨hPT,_hPS⟩
      · exact Or.inr hPT
      · exact Or.inl (List.mem_filter.mpr ⟨hP,by simpa using hPT⟩)
    have hrFlow : r=groupFlow M (S ∪ T) k a := groupGap_eq_flow M (Mole.block_joint_degrees M hU).1 hr
    have hSFlow : groupFlow M S k a=r :=
      (nested_groupFlow_eq M (show S ⊆ S ∪ T from subset_union_left) a
        ((Mole.block_joint_degrees M hprefix).1.trans (Mole.block_joint_degrees M hU).1.symm) k).trans hrFlow.symm
    have hTFlow : groupFlow M T k b=r :=
      (terminal_block_initialFlow M hM hT.block hU subset_union_right k hk hcons).trans hrFlow.symm
    have hGapS : M.IsBlockGap L w κ S a (groupFlow M S k a) := block_groupGap_exists M hprefix k
    have hGapT : M.IsBlockGap L w κ T b (groupFlow M T k b) := block_groupGap_exists M hT.block k
    have hOutS : Molecule.gapKind L γ η (groupFlow M S k a)=.LG ∨
        Molecule.gapKind L γ η (groupFlow M S k a)=.ZG := by simpa only [hSFlow] using houter
    have hOutT : Molecule.gapKind L γ η (groupFlow M T k b)=.LG ∨
        Molecule.gapKind L γ η (groupFlow M T k b)=.ZG := by simpa only [hTFlow] using houter
    have hconnS := ih hprefix qs (fun P hP => hvine P (hqs P hP)) hqsSub
      (fun P hP => hD P (hqs P hP))
      (fun P hP Q hQ hne => hdis P (hqs P hP) Q (hqs Q hQ) hne)
      _ hGapS hOutS (fun P hP => hSG P (hqs P hP))
    have hconnT := SG_ordinary_vines_removal_in_single_vine_connected M hM hT ts
      (fun P hP => hvine P (hts P hP)) htsSub (fun P hP => hD P (hts P hP))
      (fun P hP Q hQ hne => hdis P (hts P hP) Q (hts Q hQ) hne)
      L γ η w z κ hκ hz hGapT hOutT (fun P hP => hSG P (hts P hP))
    have hinside : ∀ P ∈ ps,∀ d ∈ P.darts,M.InGroup P.atoms d := by
      intro P hP d hd
      rw [hD P hP] at hd
      exact (mem_filter.mp hd).2
    have hbS : b ∈ remainingAtoms S qs := by
      refine mem_filter.mpr ⟨(chain_joints_mem hS).2,?_⟩
      intro P hP hin
      exact hNoB P (hqs P hP) (mem_sdiff.mp hin).1
    have hbT : b ∈ remainingAtoms T ts := by
      refine mem_filter.mpr ⟨hT.block.2.1,?_⟩
      intro P hP hin
      exact hNoB P (hts P hP) (mem_sdiff.mp hin).1
    have reach (u : V) (hu : u ∈ remainingAtoms (S ∪ T) ps) :
        (removeBlocks M (S ∪ T) ps).SameComponent u b := by
      rcases mem_union.mp (mem_filter.mp hu).1 with huS | huT
      · have hul := remainingAtoms_local_of_global (S ∪ T) S ps qs hqs huS hu
        exact removal_local_path_lift M (show S ⊆ S ∪ T from subset_union_left) qs ps
          hqsParts hinside (hconnS u hul b hbS)
      · have hul := remainingAtoms_local_of_global (S ∪ T) T ps ts hts huT hu
        exact removal_local_path_lift M (show T ⊆ S ∪ T from subset_union_right) ts ps
          htsParts hinside (hconnT u hul b hbT)
    intro u hu v hv
    exact Relation.EqvGen.trans _ _ _ (reach u hu) (Relation.EqvGen.symm _ _ (reach v hv))

end WaveTurbulence.GammaLow.FinalCount.H
