/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.EnhancedSearch
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaPreprocess
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103DegreeTwoProfile
public import WaveTurbulence.Foundations.FinalCount.MoleProp.InducedBridgeCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.BetaSideCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DegreeTwoNeutral
public import WaveTurbulence.Foundations.FinalCount.MoleProp.QuadrupleDistinctness
import Mathlib.Tactic

/-! # Actual initial-profile preprocessing induction

Every bridge or beta operation produces a proper descendant with the
original two-cubic profile, with one degree-two cleanup when needed.
-/

@[expose] public section
set_option autoImplicit false
open Finset
universe u v
namespace WaveTurbulence.MoleProp

theorem initial_small_graph_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηsmall : η ≤ min γ (1-γ)/200) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ x, M.atom x ≠ M.atom (M.mate x)) →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) →
      (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
      TwoThreeProfile M → (M.atoms.card : ℝ) ≤ Real.log L →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L^(-(min γ (1-γ)+η/2))) := by
  classical
  have hg : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
  have hηmax : η ≤ min γ (1-γ)/2 := by linarith only [hηsmall,hg]
  obtain ⟨Ce,hCe,hE⟩ := enhanced_small_search_bound d hd γ hγ η hη hηsmall
  obtain ⟨Cb,hCb,hB⟩ := countAFree_le_bridgeSide d hd γ hγ η hη hηmax
  obtain ⟨Cq,hCq,hQ⟩ := countAFree_le_beta_side_of_rank_change d hd γ hγ η hη hηmax
  refine ⟨max Ce (max Cb Cq),hCe.trans (le_max_left _ _),?_⟩
  intro C1 hC1 δ hδ
  have hC1e : Ce ≤ C1 := (le_max_left _ _).trans hC1
  have hC1b : Cb ≤ C1 := (le_max_left _ _).trans ((le_max_right _ _).trans hC1)
  have hC1q : Cq ≤ C1 := (le_max_right _ _).trans ((le_max_right _ _).trans hC1)
  have hC1one : 1 ≤ C1 := hCe.trans hC1e
  obtain ⟨Re,hRe⟩ := hE C1 hC1e δ hδ
  obtain ⟨Rb,hRb⟩ := hB C1 hC1b δ hδ
  obtain ⟨Rq,hRq⟩ := hQ C1 hC1q δ hδ
  obtain ⟨Rt,hRt⟩ := countAFree_erase_two_neutral d hd γ hγ η hη hηmax δ hδ
  let R := max Re (max Rb (max Rq Rt))
  refine ⟨R,?_⟩
  intro L hL hlog V D _ _ _ M hM hloop hsimp hconn hprof hsize Adm P hAdm
  have hRall : Re ≤ L ∧ Rb ≤ L ∧ Rq ≤ L ∧ Rt ≤ L := by simpa only [R,max_le_iff] using hL
  rcases hRall with ⟨hLe,hLb,hLq,hLt⟩
  have aux : ∀ n : ℕ, ∀ {E : Type v} [Fintype E] [DecidableEq E]
      (N : Molecule V E), N.atoms.card=n → N.IsMolecule →
      (∀ x, N.atom x ≠ N.atom (N.mate x)) →
      (∀ a b, a ≠ b → N.bondsBetween a b ≤ 1) →
      (∀ a ∈ N.atoms, ∀ b ∈ N.atoms, N.SameComponent a b) →
      TwoThreeProfile N → (N.atoms.card : ℝ) ≤ Real.log L →
      ∀ A : (E → (Fin d → ℤ)) → Prop,
      (∀ κ, A κ → LargeGap N L γ η (0 : Mom d) κ) →
      countAFree N L γ δ C1 (0 : Mom d) A P ≤ ENNReal.ofReal (L^(-(min γ (1-γ)+η/2))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E _ _ N hn hNM hNl hNs hNc hNp hsmall A hALG
      obtain ⟨a,ha,b,hb,hab,ha3,hb3,hrest⟩ := hNp
      by_cases hbridge : ∃ e, Degen.IsBridge N e
      · obtain ⟨e,he⟩ := hbridge
        let S := bridgeSide N e
        let Q := Mole.induced N S
        let AQ := inducedFreeAdmissibility N S A
        have hQcard : Q.atoms.card=S.card := rfl
        obtain ⟨hlt,hQM,hQc,hQp⟩ := initial_bridge_side_profile N hNM hab ha3 hb3 hrest e he
        have hQs := induced_simple N S hNs
        have hQl : ∀ x, Q.atom x ≠ Q.atom (Q.mate x) := fun x => hNl x.val
        have hQlg := inducedFreeAdmissibility_largeGap N S L γ η (0 : Mom d) A hALG
        have hQsmall : (Q.atoms.card : ℝ) ≤ Real.log L := by
          have hh : (Q.atoms.card : ℝ) ≤ N.atoms.card := by rw [hQcard]; exact_mod_cast hlt.le
          exact hh.trans hsmall
        have hstep := hRb L hLb hlog N hNM hNs e he A P hALG
        rcases hQp with htwo3 | hone2
        · have hlt' : Q.atoms.card < n := by simpa only [hQcard,hn] using hlt
          exact hstep.trans (ih _ hlt' Q rfl hQM hQl hQs hQc htwo3 hQsmall AQ hQlg)
        · obtain ⟨w,hw,hw2,hQ'M,hQ'p,hQ'c,hχw,hltw⟩ :=
            erase_one_two_restores_initial_profile Q hQM hQl hQs hQc hone2
          have hstepw := hRt L hLt hlog C1 hC1one Q hQM hQs w hw hw2 hχw AQ P hQlg
          have hlt' : (Degen.eraseAtoms Q {w}).atoms.card < n := by change S.card < N.atoms.card at hlt; omega
          have hsmall' : ((Degen.eraseAtoms Q {w}).atoms.card : ℝ) ≤ Real.log L := by
            have hh : ((Degen.eraseAtoms Q {w}).atoms.card : ℝ) ≤ Q.atoms.card := by exact_mod_cast hltw.le
            exact hh.trans hQsmall
          exact hstep.trans (hstepw.trans (ih _ hlt' (Degen.eraseAtoms Q {w}) rfl hQ'M
            (fun x => hQl x.val) (simple_eraseAtoms Q {w} hQs) hQ'c hQ'p hsmall'
            (erasedFreeAdmissibility Q {w} AQ) (projected_largeGap Q L γ η (0 : Mom d) {w} AQ hQlg)))
      have hnb : ∀ e, ¬ Degen.IsBridge N e := fun e he => hbridge ⟨e,he⟩
      by_cases hbeta : AdmitsBetaSplit N
      · obtain ⟨w,x,y,r,s,U,S,hw,hw4,hx,hy,hr,hs,hxo,hyo,hro,hso,hstar,hU,hcut,hTcut,hSide,hS,hQM,hQp,hQc,hlt⟩ :=
          exists_initial_profile_side_of_beta N hNM hNl hNs hnb hNc hab ha3 hb3 hrest hbeta
        have hcard : ({x,y,r,s} : Finset E).card=4 := by rw [← hstar]; exact hw4
        obtain ⟨hxy,hxr,hxs,hyr,hys,hrs⟩ := quadruple_distinct_of_card hcard
        have hsn : s ∉ ({x,y,r} : Finset E) := by
          simp only [mem_insert,mem_singleton,not_or]
          exact ⟨Ne.symm hxs,Ne.symm hys,Ne.symm hrs⟩
        have hnotMate : y ≠ N.mate x := by
          intro he
          have hm : N.atom (N.mate x) = w := by rw [← he]; exact hy
          exact hNl x (hx.trans hm.symm)
        have hχ := circuitRank_erase_beta_joint N hNM hNl
          (isCutData_withFreshAtom N hw hx hy hnotMate hxo hyo) hw4 (fun e _ => hnb e)
          (beta_split_disconnected_of_old_cut N hx hy U hU hcut)
        have hends : ∀ z ∈ Degen.boundaryDarts N S, N.atom (N.mate z) ∈ ({w} : Finset V) := by
          rcases hSide with rfl | rfl
          · intro z hz
            rw [hcut] at hz
            rcases mem_insert.mp hz with rfl | hz
            · simp only [N.mate_mate,hx,mem_singleton]
            · rw [mem_singleton.mp hz,N.mate_mate,hy]; exact mem_singleton_self w
          · intro z hz
            rw [hTcut] at hz
            rcases mem_insert.mp hz with rfl | hz
            · simp only [N.mate_mate,hr,mem_singleton]
            · rw [mem_singleton.mp hz,N.mate_mate,hs]; exact mem_singleton_self w
        have hstep := hRq L hLq hlog N hNM hNs hsmall w hw x y r s hxy hxr hyr hsn hstar
          hxo hyo hro hso U (fun z hz => (mem_sdiff.mp (hU hz)).1) hcut hχ S hS hends A P hALG
        have hScard : (Mole.induced N S).atoms.card=S.card := rfl
        have hlt' : (Mole.induced N S).atoms.card < n := by simpa only [hScard,hn] using hlt
        have hsmall' : ((Mole.induced N S).atoms.card : ℝ) ≤ Real.log L := by
          have hh : ((Mole.induced N S).atoms.card : ℝ) ≤ N.atoms.card := by rw [hScard]; exact_mod_cast hlt.le
          exact hh.trans hsmall
        exact hstep.trans (ih _ hlt' (Mole.induced N S) rfl hQM (fun x => hNl x.val)
          (induced_simple N S hNs) hQc hQp hsmall' (inducedFreeAdmissibility N S A)
          (inducedFreeAdmissibility_largeGap N S L γ η (0 : Mom d) A hALG))
      · have hI : SearchInput N := {
          molecule := hNM
          loopless := hNl
          simple := hNs
          nonempty := ⟨a,ha⟩
          connected := hNc
          minDegree := by
            intro z hz
            by_cases hza : z=a
            · simpa only [hza,ha3] using (le_refl (3 : ℕ))
            by_cases hzb : z=b
            · simpa only [hzb,hb3] using (le_refl (3 : ℕ))
            rw [hrest z hz hza hzb]; decide
          bridgeless := hnb
          noBeta := hbeta }
        exact hRe L hLe hlog N hI hsmall A P hALG
  exact aux _ M rfl hM hloop hsimp hconn hprof hsize Adm hAdm

end WaveTurbulence.MoleProp
