/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamStepData
import Mathlib.Tactic

/-! # One-rung contraction at a cap at the `y`-end of the slot -/

public section
namespace WaveTurbulence.Vine.Param
open Finset

theorem ladderNode_u_out (N k x y j : ℕ) (Cn : Finset ℕ) (hCold : ∀ t ∈ Cn,t < N) (hx : x ∉ Cn)
    (hj : j ≤ k) : ladderNode x y N (k+1) j ∉ Cn := by
  intro h
  have := hCold _ h
  simp only [ladderNode] at h this
  split_ifs at h this <;> first | exact hx h | omega

theorem ladderNode_v_out (N k x' y' j : ℕ) (Cn : Finset ℕ) (hCold : ∀ t ∈ Cn,t < N) (hx : x' ∉ Cn)
    (hj : j ≤ k) : ladderNode x' y' (N+(k+1)) (k+1) j ∉ Cn := by
  intro h
  have := hCold _ h
  simp only [ladderNode] at h this
  split_ifs at h this <;> first | exact hx h | omega

theorem ladderNode_out (N base k x y j : ℕ) (Cn : Finset ℕ) (hCold : ∀ t ∈ Cn,t < N) (hx : x ∉ Cn)
    (hbase : N ≤ base) (hj : j ≤ k) : ladderNode x y base k j ∉ Cn := by
  intro h
  have := hCold _ h
  simp only [ladderNode] at h this
  split_ifs at h this <;> first | exact hx h | omega

theorem restY_uncut (N k x y x' y' : ℕ) (R : Multiset (Sym2 ℕ)) (Cn : Finset ℕ)
    (hCold : ∀ t ∈ Cn,t < N) (hx : x ∉ Cn) (hx' : x' ∉ Cn)
    (hRcross : ∀ z ∈ R,∀ a b : ℕ,z = s(a,b) → (a ∈ Cn ↔ b ∈ Cn)) :
    ∀ z ∈ restY N k x y x' y' R,∀ a b : ℕ,z = s(a,b) → (a ∈ Cn ↔ b ∈ Cn) := by
  intro z hz a b hzab
  unfold restY at hz
  simp only [Multiset.mem_add,Multiset.mem_nsmul,Multiset.mem_coe,List.mem_map,List.mem_range] at hz
  have hout : ∀ u v : ℕ,u ∉ Cn → v ∉ Cn → z = s(u,v) → (a ∈ Cn ↔ b ∈ Cn) := by
    intro u v hu hv hzuv
    rw [hzuv] at hzab
    rcases Sym2.eq_iff.mp hzab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact iff_of_false hu hv
    · exact iff_of_false hv hu
  rcases hz with ((hz | ⟨j,hj,hjz⟩) | ⟨j,hj,hjz⟩) | ⟨_,⟨j,hj,hjz⟩⟩
  · exact hRcross z hz a b hzab
  · exact hout _ _ (ladderNode_u_out N k x y j Cn hCold hx (by omega))
      (ladderNode_u_out N k x y (j+1) Cn hCold hx (by omega)) hjz.symm
  · exact hout _ _ (ladderNode_v_out N k x' y' j Cn hCold hx' (by omega))
      (ladderNode_v_out N k x' y' (j+1) Cn hCold hx' (by omega)) hjz.symm
  · exact hout _ _ (fun h => by have := hCold _ h; omega)
      (fun h => by have := hCold _ h; omega) hjz.symm

/-- Relabeling the rest by the skip map gives the `k`-version rails and rungs. -/
theorem restY_map_skip (N k x y x' y' : ℕ) (hx : x < N) (hy : y < N) (hx' : x' < N)
    (hy' : y' < N) (R : Multiset (Sym2 ℕ)) (hR : ∀ e ∈ R,∀ z ∈ e,z < N) :
    (restY N k x y x' y' R).map (Sym2.map (skip2 (N+k) (N+(2*k+1)))) =
      R + (((List.range k).map (fun j => s(ladderNode x y N k j,ladderNode x y N k (j+1))) :
          List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) +
        (((List.range k).map (fun j => s(ladderNode x' y' (N+k) k j,
          ladderNode x' y' (N+k) k (j+1))) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) +
        2 • (((List.range k).map (fun j => s(N+j,N+k+j)) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) := by
  have hRm : R.map (Sym2.map (skip2 (N+k) (N+(2*k+1)))) = R := by
    conv_rhs => rw [← Multiset.map_id R]
    apply Multiset.map_congr rfl
    intro e he
    revert he
    induction e using Sym2.ind with
    | h a b =>
      intro he
      have ha := hR _ he a (Sym2.mem_mk_left _ _)
      have hb := hR _ he b (Sym2.mem_mk_right _ _)
      simp only [Sym2.map_mk,id,skip2_lt (N+k) (N+(2*k+1)) a (by omega) (by omega),
        skip2_lt (N+k) (N+(2*k+1)) b (by omega) (by omega)]
  unfold restY
  simp only [Multiset.map_add,Multiset.map_coe,Multiset.map_nsmul,hRm,List.map_map]
  have L1 : List.map (Sym2.map (skip2 (N+k) (N+(2*k+1))) ∘ fun j =>
      s(ladderNode x y N (k+1) j,ladderNode x y N (k+1) (j+1))) (List.range k) =
      (List.range k).map (fun j => s(ladderNode x y N k j,ladderNode x y N k (j+1))) := by
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [Function.comp_apply,Sym2.map_mk]
    rw [contractY_nu N k x y j hx hy (by omega),contractY_nu N k x y (j+1) hx hy (by omega)]
  have L2 : List.map (Sym2.map (skip2 (N+k) (N+(2*k+1))) ∘ fun j =>
      s(ladderNode x' y' (N+(k+1)) (k+1) j,ladderNode x' y' (N+(k+1)) (k+1) (j+1))) (List.range k) =
      (List.range k).map (fun j => s(ladderNode x' y' (N+k) k j,ladderNode x' y' (N+k) k (j+1))) := by
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [Function.comp_apply,Sym2.map_mk]
    rw [contractY_nv N k x' y' j hx' hy' (by omega),contractY_nv N k x' y' (j+1) hx' hy' (by omega)]
  have L3 : List.map (Sym2.map (skip2 (N+k) (N+(2*k+1))) ∘ fun j => s(N+j,N+(k+1)+j))
      (List.range k) = (List.range k).map (fun j => s(N+j,N+k+j)) := by
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [Function.comp_apply,Sym2.map_mk,skip2]
    congr 2 <;> split_ifs <;> omega
  rw [L1,L2,L3]

theorem unskip2_ge (f0 f1 u : ℕ) : u ≤ unskip2 f0 f1 u := by
  simp only [unskip2]; split_ifs <;> omega

theorem unskip2_eq_of_lt (f0 f1 u : ℕ) (h : u < f0) (h01 : f0 < f1) : unskip2 f0 f1 u = u := by
  simp only [unskip2]; split_ifs <;> omega

theorem ladderNode_lt (x y base k j bound : ℕ) (hx : x < bound) (hy : y < bound)
    (hb : base + k ≤ bound) (hk : 1 ≤ k ∨ x < bound) :
    ladderNode x y base k j < bound := by
  simp only [ladderNode]
  split_ifs <;> omega

theorem exists_slot_contraction_Y (N k x y x' y' : ℕ) (hx : x < N) (hy : y < N) (hx' : x' < N)
    (hy' : y' < N) (R : Multiset (Sym2 ℕ)) (hR : ∀ e ∈ R,∀ z ∈ e,z < N)
    (Cn : Finset ℕ) (hCold : ∀ t ∈ Cn,t < N)
    (hxC : x ∉ Cn) (hx'C : x' ∉ Cn) (hyC : y ∈ Cn) (hy'C : y' ∈ Cn)
    (hRcross : ∀ z ∈ R,∀ a b : ℕ,z = s(a,b) → (a ∈ Cn ↔ b ∈ Cn))
    (ν : ℕ ≃ ℕ) (hνout : ∀ t ∉ Cn,ν t = t) (hνmem : ∀ t,ν t ∈ Cn ↔ t ∈ Cn)
    (hνy : ν y = y') (hνy' : ν y' = y) (hνR : R.map (Sym2.map ν) = R)
    {β : Type} [Fintype β] [DecidableEq β]
    (ends : β → Fin (N+2*k+2) × Fin (N+2*k+2))
    (hU : (univ : Finset β).val.map (fun e => s((ends e).1.1,(ends e).2.1)) =
      insSym N x y x' y' (k+1) R)
    (hbal : ∀ v,(∑ e,-energySign ends v e) = 0) :
    ∃ G : RungSpliceGeometry (Fin (N+2*k)) (RestEdge (N+k) (N+(2*k+1)) ends ⊕ Fin 2),
      ((univ : Finset (RestEdge (N+k) (N+(2*k+1)) ends ⊕ Fin 2)).val.map
        (fun e => s((G.ends e).1.1,(G.ends e).2.1)) = insSym N x y x' y' k R) ∧
      G.cap = capFin (N+2*k) Cn ∧
      (∀ u : Fin (N+2*k),(G.σ u).1 = u.1 ∨ (G.σ u).1 = ν u.1) ∧
      ((∀ u : Fin (N+2*k),(G.σ u).1 = u.1) ∨ (∀ u : Fin (N+2*k),(G.σ u).1 = ν u.1)) ∧
      ((G.p).1 = x ∨ N ≤ (G.p).1) ∧ ((G.q).1 = x' ∨ N ≤ (G.q).1) ∧ (G.c).1 = y ∧ (G.d).1 = y' ∧
      ∃ J : DirectedGraphIso G.newEnds ends,
        (∀ u : Fin (N+2*k),(u.1 < N → (J.atom (Sum.inl u)).1 = u.1) ∧
          (N ≤ u.1 → N ≤ (J.atom (Sum.inl u)).1)) ∧
        (∀ j,N ≤ (J.atom (Sum.inr j)).1) ∧
        (∀ u : Fin (N+2*k),(J.atom (Sum.inl u)).1 = unskip2 (N+k) (N+(2*k+1)) u.1) ∧
        (J.atom (Sum.inr 0)).1 = (N+k) ∧ (J.atom (Sum.inr 1)).1 = (N+(2*k+1)) := by
  classical
  have h : N+k < N+(2*k+1) := by omega
  have h1 : N+(2*k+1) < (N+2*k)+2 := by omega
  have hpl : ladderNode x y N (k+1) k < (N+2*k)+2 := ladderNode_lt x y N (k+1) k _ (by omega)
    (by omega) (by omega) (Or.inr (by omega))
  have hql : ladderNode x' y' (N+(k+1)) (k+1) k < (N+2*k)+2 :=
    ladderNode_lt x' y' (N+(k+1)) (k+1) k _ (by omega) (by omega) (by omega) (Or.inr (by omega))
  let p : Fin ((N+2*k)+2) := ⟨ladderNode x y N (k+1) k,hpl⟩
  let q : Fin ((N+2*k)+2) := ⟨ladderNode x' y' (N+(k+1)) (k+1) k,hql⟩
  let c : Fin ((N+2*k)+2) := ⟨y,by omega⟩
  let d : Fin ((N+2*k)+2) := ⟨y',by omega⟩
  have hpv : p.1 = x ∨ (N ≤ p.1 ∧ p.1 < N+k) := by
    simp only [p,ladderNode]; split_ifs <;> omega
  have hqv : q.1 = x' ∨ (N+k < q.1 ∧ q.1 < N+(2*k+1)) := by
    simp only [q,ladderNode]; split_ifs <;> omega
  have hp : p.1 ≠ N+k ∧ p.1 ≠ N+(2*k+1) := by omega
  have hq : q.1 ≠ N+k ∧ q.1 ≠ N+(2*k+1) := by omega
  have hc : c.1 ≠ N+k ∧ c.1 ≠ N+(2*k+1) := by simp only [c]; omega
  have hd : d.1 ≠ N+k ∧ d.1 ≠ N+(2*k+1) := by simp only [d]; omega
  have hcell : (((cellRef (N+k) (N+(2*k+1)) p.1 q.1 c.1 d.1).map fun e => s(e.1,e.2) :
      List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) = cellY N k x y x' y' := by
    unfold cellY cellRef
    simp only [List.map_cons,List.map_nil,← Multiset.cons_coe,Multiset.coe_nil,
      ← Multiset.singleton_add,two_nsmul,Multiset.add_zero,p,q,c,d]
    abel
  have hU' : (univ : Finset β).val.map (fun e => s((ends e).1.1,(ends e).2.1)) =
      (((cellRef (N+k) (N+(2*k+1)) p.1 q.1 c.1 d.1).map fun e => s(e.1,e.2) : List (Sym2 ℕ)) :
        Multiset (Sym2 ℕ)) + restY N k x y x' y' R := by
    rw [hU,contractY_split,hcell]
  have hCold' : ∀ t ∈ Cn,t < N+k := fun t ht => by have := hCold t ht; omega
  have hpC : p.1 ∉ Cn := by
    intro hm; have := hCold _ hm
    rcases hpv with h | h
    · exact hxC (h ▸ hm)
    · omega
  have hqC : q.1 ∉ Cn := by
    intro hm; have := hCold _ hm
    rcases hqv with h | h
    · exact hx'C (h ▸ hm)
    · omega
  have hlblout : ∀ (t : ℕ) (ht : t < N+2*k),t ∉ Cn →
      ((reflFinGen ν Cn N (N+2*k) hCold (by omega) hνout hνmem).symm ⟨t,ht⟩).1 = t := by
    intro t ht htC
    rw [reflFinGen_symm_apply]
    rw [ν.symm_apply_eq]
    exact (hνout t htC).symm
  let σ0 := reflFinGen ν Cn N (N+2*k) hCold (by omega) hνout hνmem
  have hlbl1 : ∀ (t : ℕ),t < N+2*k →
      (fun t : ℕ => if ht : t < N+2*k then (σ0.symm ⟨t,ht⟩).1 else t) t = ν.symm t := by
    intro t ht
    simp only [ht,dite_true]
    exact reflFinGen_symm_apply ν Cn N (N+2*k) hCold (by omega) hνout hνmem ⟨t,ht⟩
  have hlbl2 : ∀ (t : ℕ),t < N+2*k → t ∉ Cn →
      (fun t : ℕ => if ht : t < N+2*k then (σ0.symm ⟨t,ht⟩).1 else t) t = t := by
    intro t ht htC
    rw [hlbl1 t ht,ν.symm_apply_eq]
    exact (hνout t htC).symm
  have hRs : R.map (Sym2.map ν.symm) = R := by
    have := congrArg (Multiset.map (Sym2.map ν.symm)) hνR
    rw [Multiset.map_map] at this
    have hid : (Sym2.map ν.symm ∘ Sym2.map ν : Sym2 ℕ → Sym2 ℕ) = id := by
      funext e
      induction e using Sym2.ind with
      | h a b => simp
    rw [hid,Multiset.map_id] at this
    exact this.symm
  have hinv : (((restY N k x y x' y' R).map (Sym2.map (skip2 (N+k) (N+(2*k+1))))).map
      (Sym2.map (fun t : ℕ => if ht : t < N+2*k then (σ0.symm ⟨t,ht⟩).1 else t))) =
      (restY N k x y x' y' R).map (Sym2.map (skip2 (N+k) (N+(2*k+1)))) := by
    rw [restY_map_skip N k x y x' y' hx hy hx' hy' R hR]
    simp only [Multiset.map_add,Multiset.map_nsmul,Multiset.map_coe,List.map_map]
    have hRl : R.map (Sym2.map (fun t : ℕ => if ht : t < N+2*k then (σ0.symm ⟨t,ht⟩).1 else t)) =
        R := by
      conv_rhs => rw [← hRs]
      apply Multiset.map_congr rfl
      intro e he
      revert he
      induction e using Sym2.ind with
      | h a b =>
        intro he
        have ha := hR _ he a (Sym2.mem_mk_left _ _)
        have hb := hR _ he b (Sym2.mem_mk_right _ _)
        simp only [Sym2.map_mk]
        have e1 := hlbl1 a (by omega)
        have e2 := hlbl1 b (by omega)
        beta_reduce at e1 e2
        rw [e1,e2]
    rw [hRl]
    have hl1 : List.map (Sym2.map (fun t : ℕ => if ht : t < N+2*k then (σ0.symm ⟨t,ht⟩).1 else t) ∘
        fun j => s(ladderNode x y N k j,ladderNode x y N k (j+1))) (List.range k) =
        (List.range k).map (fun j => s(ladderNode x y N k j,ladderNode x y N k (j+1))) := by
      apply List.map_congr_left
      intro j hj
      have hj := List.mem_range.mp hj
      have a1 := ladderNode_out N N k x y j Cn hCold hxC le_rfl (by omega)
      have a2 := ladderNode_out N N k x y (j+1) Cn hCold hxC le_rfl (by omega)
      have b1 : ladderNode x y N k j < N+2*k := ladderNode_lt x y N k j _ (by omega) (by omega)
        (by omega) (Or.inr (by omega))
      have b2 : ladderNode x y N k (j+1) < N+2*k := ladderNode_lt x y N k (j+1) _ (by omega)
        (by omega) (by omega) (Or.inr (by omega))
      simp only [Function.comp_apply,Sym2.map_mk]
      have c1 := hlbl2 _ b1 a1
      have c2 := hlbl2 _ b2 a2
      beta_reduce at c1 c2
      rw [c1,c2]
    have hl2 : List.map (Sym2.map (fun t : ℕ => if ht : t < N+2*k then (σ0.symm ⟨t,ht⟩).1 else t) ∘
        fun j => s(ladderNode x' y' (N+k) k j,ladderNode x' y' (N+k) k (j+1))) (List.range k) =
        (List.range k).map (fun j => s(ladderNode x' y' (N+k) k j,ladderNode x' y' (N+k) k (j+1))) := by
      apply List.map_congr_left
      intro j hj
      have hj := List.mem_range.mp hj
      have a1 := ladderNode_out N (N+k) k x' y' j Cn hCold hx'C (by omega) (by omega)
      have a2 := ladderNode_out N (N+k) k x' y' (j+1) Cn hCold hx'C (by omega) (by omega)
      have b1 : ladderNode x' y' (N+k) k j < N+2*k := ladderNode_lt x' y' (N+k) k j _ (by omega)
        (by omega) (by omega) (Or.inr (by omega))
      have b2 : ladderNode x' y' (N+k) k (j+1) < N+2*k := ladderNode_lt x' y' (N+k) k (j+1) _
        (by omega) (by omega) (by omega) (Or.inr (by omega))
      simp only [Function.comp_apply,Sym2.map_mk]
      have c1 := hlbl2 _ b1 a1
      have c2 := hlbl2 _ b2 a2
      beta_reduce at c1 c2
      rw [c1,c2]
    have hl3 : List.map (Sym2.map (fun t : ℕ => if ht : t < N+2*k then (σ0.symm ⟨t,ht⟩).1 else t) ∘
        fun j => s(N+j,N+k+j)) (List.range k) = (List.range k).map (fun j => s(N+j,N+k+j)) := by
      apply List.map_congr_left
      intro j hj
      have hj := List.mem_range.mp hj
      have a1 : N+j ∉ Cn := fun hm => by have := hCold _ hm; omega
      have a2 : N+k+j ∉ Cn := fun hm => by have := hCold _ hm; omega
      simp only [Function.comp_apply,Sym2.map_mk]
      have c1 := hlbl2 (N+j) (by omega) a1
      have c2 := hlbl2 (N+k+j) (by omega) a2
      beta_reduce at c1 c2
      rw [c1,c2]
    rw [hl1,hl2,hl3]
  have hσ0C : ∀ u : Fin (N+2*k),σ0 u ∈ capFin (N+2*k) Cn ↔ u ∈ capFin (N+2*k) Cn := by
    intro u
    simp only [capFin,mem_filter,mem_univ,true_and]
    rw [reflFinGen_apply]
    exact hνmem u.1
  have hskp : skip2 (N+k) (N+(2*k+1)) p.1 ∉ Cn := by
    rcases hpv with h' | h'
    · rw [skip2_lt (N+k) (N+(2*k+1)) p.1 (by omega) (by omega),h']; exact hxC
    · rw [skip2_lt (N+k) (N+(2*k+1)) p.1 (by omega) (by omega)]
      intro hm; have := hCold _ hm; omega
  have hskq : skip2 (N+k) (N+(2*k+1)) q.1 ∉ Cn := by
    rcases hqv with h' | h'
    · rw [skip2_lt (N+k) (N+(2*k+1)) q.1 (by omega) (by omega),h']; exact hx'C
    · intro hm; have := hCold _ hm
      have : N ≤ skip2 (N+k) (N+(2*k+1)) q.1 := by simp only [skip2]; split_ifs <;> omega
      omega
  have hy1 : skip2 (N+k) (N+(2*k+1)) y = y := skip2_lt _ _ _ (by omega) (by omega)
  have hy2 : skip2 (N+k) (N+(2*k+1)) y' = y' := skip2_lt _ _ _ (by omega) (by omega)
  obtain ⟨G,hGends,hGcap,hGp,hGq,hGc,hGd,hGσ,hshadow,J,hJ⟩ :=
    exists_contracted_geometry (N+k) (N+(2*k+1)) h h1 ends p q c d hp hq hc hd
      (restY N k x y x' y' R) (restY_avoid N k x y x' y' hx hx' R hR) hU' Cn hCold'
      hpC hqC hyC hy'C
      (restY_uncut N k x y x' y' R Cn hCold hxC hx'C hRcross) hbal σ0 hσ0C
      (Fin.ext (by
        change ν (skip2 (N+k) (N+(2*k+1)) p.1) = skip2 (N+k) (N+(2*k+1)) p.1
        exact hνout _ hskp))
      (Fin.ext (by
        change ν (skip2 (N+k) (N+(2*k+1)) q.1) = skip2 (N+k) (N+(2*k+1)) q.1
        exact hνout _ hskq))
      (Fin.ext (by
        change ν (skip2 (N+k) (N+(2*k+1)) y) = skip2 (N+k) (N+(2*k+1)) y'
        rw [hy1,hy2]; exact hνy))
      (Fin.ext (by
        change ν (skip2 (N+k) (N+(2*k+1)) y') = skip2 (N+k) (N+(2*k+1)) y
        rw [hy1,hy2]; exact hνy'))
      hinv
  refine ⟨G,?_,hGcap,?_,?_,?_,?_,?_,?_,J,?_,?_,?_,?_,?_⟩
  · rw [hshadow,contractY_back N k x y x' y' hx hy hx' hy' R hR]
    rfl
  · intro u
    rcases hGσ with h' | h'
    · right; rw [h']; exact reflFinGen_apply ν Cn N (N+2*k) hCold (by omega) hνout hνmem u
    · left; rw [h']; rfl
  · rcases hGσ with h' | h'
    · right; intro u; rw [h']; exact reflFinGen_apply ν Cn N (N+2*k) hCold (by omega) hνout hνmem u
    · left; intro u; rw [h']; rfl
  · rw [hGp]
    change skip2 (N+k) (N+(2*k+1)) p.1 = x ∨ N ≤ skip2 (N+k) (N+(2*k+1)) p.1
    rcases hpv with h' | h'
    · left; rw [skip2_lt (N+k) (N+(2*k+1)) p.1 (by omega) (by omega),h']
    · right; rw [skip2_lt (N+k) (N+(2*k+1)) p.1 (by omega) (by omega)]; omega
  · rw [hGq]
    change skip2 (N+k) (N+(2*k+1)) q.1 = x' ∨ N ≤ skip2 (N+k) (N+(2*k+1)) q.1
    rcases hqv with h' | h'
    · left; rw [skip2_lt (N+k) (N+(2*k+1)) q.1 (by omega) (by omega),h']
    · right; simp only [skip2]; split_ifs <;> omega
  · rw [hGc]
    change skip2 (N+k) (N+(2*k+1)) y = y
    exact hy1
  · rw [hGd]
    change skip2 (N+k) (N+(2*k+1)) y' = y'
    exact hy2
  · intro u
    constructor
    · intro hu
      rw [hJ]
      change unskip2 (N+k) (N+(2*k+1)) u.1 = u.1
      exact unskip2_eq_of_lt _ _ _ (by omega) h
    · intro hu
      rw [hJ]
      change N ≤ unskip2 (N+k) (N+(2*k+1)) u.1
      have := unskip2_ge (N+k) (N+(2*k+1)) u.1
      omega
  · intro j
    rw [hJ]
    fin_cases j
    · change N ≤ (if (0 : Fin 2) = 0 then (⟨N+k,by omega⟩ : Fin ((N+2*k)+2)) else ⟨N+(2*k+1),h1⟩).1
      simp
    · change N ≤ (if (1 : Fin 2) = 0 then (⟨N+k,by omega⟩ : Fin ((N+2*k)+2)) else ⟨N+(2*k+1),h1⟩).1
      simp
  · intro u
    rw [hJ]
    rfl
  · rw [hJ]
    change (if (0 : Fin 2) = 0 then (⟨(N+k),by omega⟩ : Fin ((N+2*k)+2)) else ⟨(N+(2*k+1)),h1⟩).1 = _
    simp
  · rw [hJ]
    change (if (1 : Fin 2) = 0 then (⟨(N+k),by omega⟩ : Fin ((N+2*k)+2)) else ⟨(N+(2*k+1)),h1⟩).1 = _
    simp

end WaveTurbulence.Vine.Param
