/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSGOrdinaryVineShape
public import WaveTurbulence.Foundations.Molecule.VineTypeIRemovalConnected
public import WaveTurbulence.Foundations.Molecule.VineVIISideRemovalConnected
public import WaveTurbulence.Foundations.Molecule.VineRemovalCongruence
public import WaveTurbulence.Foundations.Molecule.VineRemovalConnectivity
import Mathlib.Tactic

/-! # Simultaneous ordinary SG-vine removals inside one LG/ZG vine -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc, ordinary removals in one vine ingredient. Source SG
vines form a disjoint family in an LG/ZG vine; deleting all their bonds
and nonjoint atoms preserves connectivity. All structural shape, rail
paths and side data are derived within the proof. -/
theorem SG_ordinary_vines_removal_in_single_vine_connected (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (hV : M.IsVine X S a b)
    (ps : List (RemovalPiece V D))
    (hvine : ∀ P ∈ ps,IsSomeVine M P.atoms P.left P.right)
    (hsub : ∀ P ∈ ps,P.atoms ⊆ S)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r : Mom d} (hr : M.IsBlockGap L w κ S a r)
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hSG : ∀ P ∈ ps,∃ r' : Mom d,M.IsBlockGap L w κ P.atoms P.left r' ∧
      Molecule.gapKind L γ η r'=.SG) :
    ∀ u ∈ remainingAtoms S ps,∀ v ∈ remainingAtoms S ps,(removeBlocks M S ps).SameComponent u v := by
  classical
  by_cases hXI : X=.I
  · subst X
    have hnone : ∀ P ∈ ps,False := by
      intro P hP
      obtain ⟨Y,hY⟩ := hvine P hP
      obtain ⟨rP,hrP,hsgP⟩ := hSG P hP
      have hne := SG_block_ne_outer M hM hV.1 hY.1 L γ η w c κ hκ hc hr hrP houter hsgP
      have hSCard : S.card=2 := by rw [typeI_atoms hV,card_pair hV.1.2.2.2.1]
      have hACard := isVine_card_ge_two hY
      exact hne (eq_of_subset_of_card_le (hsub P hP) (by omega))
    have hps : ps=[] := by
      cases ps with
      | nil => rfl
      | cons P ps => exact False.elim (hnone P List.mem_cons_self)
    subst ps
    apply removal_connected_of_joint_paths M S [] (isVine_connected hV)
    all_goals simp
  · by_cases hAll : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right
    · intro u hu v hv
      exact nontrivial_vine_typeI_removal_connected M hM hXI hV ps hAll hD hdis
        u (mem_filter.mp hu).1 v (mem_filter.mp hv).1
    · push Not at hAll
      obtain ⟨P0,hP0,hP0not⟩ := hAll
      obtain ⟨r0,hr0,hsg0⟩ := hSG P0 hP0
      have hshape := SG_ordinary_vine_shape M hM hV (hvine P0 hP0) (hsub P0 hP0)
        L γ η w c κ hκ hc hr hr0 houter hsg0
      rcases hshape with hI | ⟨hX,_hP0V⟩
      · exact False.elim (hP0not hI)
      subst X
      obtain ⟨hS,⟨R⟩⟩ := isVine_iff_realization.mp hV
      obtain ⟨kr,kc,kg,hks,hAeq,hpair⟩ := typeVII_SG_nonI_vine_side M hM R hS
        (hvine P0 hP0) hP0not (hsub P0 hP0) L γ η w c κ hκ hc hr hr0 houter hsg0
      let qs := ps.filter (fun P => P ≠ P0)
      have hIqs : ∀ P ∈ qs,M.IsVine .I P.atoms P.left P.right := by
        intro Q hQ
        have hQmem := (List.mem_filter.mp hQ).1
        have hQne : Q ≠ P0 := of_decide_eq_true (List.mem_filter.mp hQ).2
        by_contra hQnot
        obtain ⟨rQ,hrQ,hsgQ⟩ := hSG Q hQmem
        obtain ⟨kr',kc',kg',hks',hAeqQ,_hpairQ⟩ := typeVII_SG_nonI_vine_side M hM R hS
          (hvine Q hQmem) hQnot (hsub Q hQmem) L γ η w c κ hκ hc hr hrQ houter hsgQ
        have hcounts : kr=kr' ∧ kc=kc' ∧ kg=kg' := by simpa using hks.symm.trans hks'
        obtain ⟨rfl,rfl,rfl⟩ := hcounts
        have hdisPQ := hdis P0 hP0 Q hQmem (Ne.symm hQne)
        obtain ⟨_Y,hY⟩ := hvine P0 hP0
        have hleft := hY.1.2.1
        have hleftQ : P0.left ∈ Q.atoms := by rw [hAeqQ,← hAeq]; exact hleft
        exact (disjoint_left.mp hdisPQ) hleft hleftQ
      let B := blockRemoval M (R.selectedAtoms (sideLabels (11+2*kr) kc))
        (R.coreAtom (7 : Fin 11)).1 (R.coreAtom (8 : Fin 11)).1
      have heq0 : P0.Equivalent B := by
        refine ⟨hAeq,hpair,?_⟩
        rw [hD P0 hP0,hAeq]
        rfl
      have hEq : RemovalFamilyEquivalent ps (B::qs) := by
        constructor
        · intro P hP
          by_cases hp : P=P0
          · subst P
            exact ⟨B,List.mem_cons_self,heq0⟩
          · exact ⟨P,List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hP,by simpa using hp⟩),rfl,rfl,rfl⟩
        · intro Q hQ
          rcases List.mem_cons.mp hQ with rfl | hQ
          · exact ⟨P0,hP0,heq0⟩
          · exact ⟨Q,(List.mem_filter.mp hQ).1,rfl,rfl,rfl⟩
      have hDqs : ∀ P ∈ qs,P.darts=univ.filter (M.InGroup P.atoms) :=
        fun P hP => hD P (List.mem_filter.mp hP).1
      have hconn := typeVII_side_typeI_removal_connected M hM R kr kc kg hks qs hIqs hDqs
      have hrAtoms := remainingAtoms_congr_of_equivalent S hEq
      intro u hu v hv
      have hp := hconn u (hrAtoms ▸ hu) v (hrAtoms ▸ hv)
      exact removal_path_congr_of_equivalent M S hEq.symm hp

end WaveTurbulence.Vine
