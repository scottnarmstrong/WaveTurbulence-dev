/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainUniquenessStep

/-! # The couple half of simultaneous uniqueness: the actual induction step -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Equal carriers have equal code orders. -/
theorem code_size_eq_of_carrier_eq {C D : RegCpl} (he : decodedCouple C = decodedCouple D) :
    C.size = D.size := by
  have hh := congrArg Garden.order he
  simpa only [decodedCouple_order] using hh

/-- The current chain uniqueness result and smaller-order couple results close the couple case. -/
theorem couple_unique_induction_step (N : ℕ)
    (ih : ∀ M < N, CoupleUniqueUpTo M ∧ ChainUniqueUpTo M)
    (hchain : ChainUniqueUpTo N) : CoupleUniqueUpTo N := by
  intro C D hN hwC hwD he
  have hsize := code_size_eq_of_carrier_eq he
  by_cases hz : C.size = 0
  · have hc := eq_triv_of_wf_size_zero C hwC hz
    have hd := eq_triv_of_wf_size_zero D hwD (hsize.symm.trans hz)
    exact hc.trans hd.symm
  cases C with
  | triv => exact (hz rfl).elim
  | type1 c r g d =>
    cases D with
    | triv => exact (hz hsize).elim
    | type2 p n q => exact (type1_ne_wf_type2 c r g d q p n hwD he).elim
    | type1 e r' g' d' =>
      have hcomp := type1_components_unique c e r g d r' g' d' he
      obtain ⟨hc,hr,hg,hd⟩ := hcomp
      subst e
      simp only [RegCpl.wf,Bool.and_eq_true] at hwC hwD
      change r.size + g.size + d.size + 2 ≤ N at hN
      have hr' := (ih r.size (by omega)).1 r r' le_rfl hwC.1.1 hwD.1.1 hr
      have hg' := (ih g.size (by omega)).1 g g' le_rfl hwC.1.2 hwD.1.2 hg
      have hd' := (ih d.size (by omega)).1 d d' le_rfl hwC.2 hwD.2 hd
      cases hr'; cases hg'; cases hd'; rfl
  | type2 p n q =>
    cases D with
    | triv => exact (hz hsize).elim
    | type1 c r g d => exact (type1_ne_wf_type2 c r g d q p n hwC he.symm).elim
    | type2 p' n' q' =>
      simp only [RegCpl.wf,Bool.and_eq_true,Bool.not_eq_true'] at hwC hwD
      change p.size + n.size + q.size ≤ N at hN
      have hpos : 2 ≤ p.size + n.size := by
        rcases Bool.and_eq_false_iff.mp hwC.2 with hp | hn
        · have hh := chain_size_pos_of_not_isNil hp; omega
        · have hh := chain_size_pos_of_not_isNil hn; omega
      have hlp := type2_lonePaths_unique p n p' n' q q' hwC.1.2 hwD.1.2 he
      have hterminal := type2_terminal_carrier_unique p n p' n' q q' hwC.1.2 hwD.1.2 he
      have hq := (ih q.size (by omega)).1 q q' le_rfl hwC.1.1.2 hwD.1.1.2 hterminal
      let G := decodedCouple (.type2 p n q)
      have haP : Comb.subtree (G.tree 0) [] = some (p.plug 1 q.trees.1) := by
        change Comb.subtree (p.plug 1 q.trees.1) [] = _
        simp [Comb.subtree]
      have haP' : Comb.subtree (G.tree 0) [] = some (p'.plug 1 q'.trees.1) := by
        change Comb.subtree ((decodedCouple (.type2 p n q)).tree 0) [] = _
        rw [he]
        change Comb.subtree (p'.plug 1 q'.trees.1) [] = _
        simp [Comb.subtree]
      have haN : Comb.subtree (G.tree 1) [] = some (n.plug (-1) q.trees.2) := by
        change Comb.subtree (n.plug (-1) q.trees.2) [] = _
        simp [Comb.subtree]
      have haN' : Comb.subtree (G.tree 1) [] = some (n'.plug (-1) q'.trees.2) := by
        change Comb.subtree ((decodedCouple (.type2 p n q)).tree 1) [] = _
        rw [he]
        change Comb.subtree (n'.plug (-1) q'.trees.2) [] = _
        simp [Comb.subtree]
      have hPP : ∀ z ∈ p.pairsAt 1 (0,[]), z ∈ (RegCpl.type2 p n q).raw.2 := by
        intro z hz
        exact List.mem_append_left _ (List.mem_append_left _ hz)
      have hNN : ∀ z ∈ n.pairsAt (-1) (1,[]), z ∈ (RegCpl.type2 p n q).raw.2 := by
        intro z hz
        exact List.mem_append_left _ (List.mem_append_right _ hz)
      have hPP' : ∀ z ∈ p'.pairsAt 1 (0,[]), z ∈ (RegCpl.type2 p n q).raw.2 := by
        intro z hz
        have hh : z ∈ (RegCpl.type2 p' n' q').raw.2 :=
          List.mem_append_left _ (List.mem_append_left _ hz)
        exact (rawPair_mem_iff_of_carrier_eq he z).mpr hh
      have hNN' : ∀ z ∈ n'.pairsAt (-1) (1,[]), z ∈ (RegCpl.type2 p n q).raw.2 := by
        intro z hz
        have hh : z ∈ (RegCpl.type2 p' n' q').raw.2 :=
          List.mem_append_left _ (List.mem_append_right _ hz)
        exact (rawPair_mem_iff_of_carrier_eq he z).mpr hh
      have hp := hchain p p' (by omega) hwC.1.1.1.1 hwD.1.1.1.1 (.type2 p n q) G
        (decodedCouple_decodes _) (0,[]) 1 _ _ haP haP' hPP hPP' hlp.1
      have hn := hchain n n' (by omega) hwC.1.1.1.2 hwD.1.1.1.2 (.type2 p n q) G
        (decodedCouple_decodes _) (1,[]) (-1) _ _ haN haN' hNN hNN' hlp.2
      cases hp; cases hn; cases hq; rfl

end WaveTurbulence.Reg
