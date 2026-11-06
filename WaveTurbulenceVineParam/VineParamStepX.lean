/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamStepY
import Mathlib.Tactic

/-! # One-rung contraction at a cap at the `x`-end of the slot -/

public section
namespace WaveTurbulence.Vine.Param
open Finset

theorem ladderNode_out_pos (N base k x y j : ℕ) (Cn : Finset ℕ) (hCold : ∀ t ∈ Cn,t < N)
    (hy : y ∉ Cn) (hbase : N ≤ base) (hj : 1 ≤ j) : ladderNode x y base k j ∉ Cn := by
  intro h
  have := hCold _ h
  simp only [ladderNode] at h this
  split_ifs at h this <;> first | exact hy h | omega

theorem sing_swap (a b : ℕ) : ({s(a,b)} : Multiset (Sym2 ℕ)) = {s(b,a)} := by
  rw [Sym2.eq_swap]

theorem restX_uncut (N k x y x' y' : ℕ) (R : Multiset (Sym2 ℕ)) (Cn : Finset ℕ)
    (hCold : ∀ t ∈ Cn,t < N) (hy : y ∉ Cn) (hy' : y' ∉ Cn)
    (hRcross : ∀ z ∈ R,∀ a b : ℕ,z = s(a,b) → (a ∈ Cn ↔ b ∈ Cn)) :
    ∀ z ∈ restX N k x y x' y' R,∀ a b : ℕ,z = s(a,b) → (a ∈ Cn ↔ b ∈ Cn) := by
  intro z hz a b hzab
  unfold restX at hz
  simp only [Multiset.mem_add,Multiset.mem_nsmul,Multiset.mem_coe,List.mem_map,List.mem_range] at hz
  have hout : ∀ u v : ℕ,u ∉ Cn → v ∉ Cn → z = s(u,v) → (a ∈ Cn ↔ b ∈ Cn) := by
    intro u v hu hv hzuv
    rw [hzuv] at hzab
    rcases Sym2.eq_iff.mp hzab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact iff_of_false hu hv
    · exact iff_of_false hv hu
  rcases hz with ((hz | ⟨j,hj,hjz⟩) | ⟨j,hj,hjz⟩) | ⟨_,⟨j,hj,hjz⟩⟩
  · exact hRcross z hz a b hzab
  · exact hout _ _ (ladderNode_out_pos N N (k+1) x y (j+2) Cn hCold hy le_rfl (by omega))
      (ladderNode_out_pos N N (k+1) x y (j+3) Cn hCold hy le_rfl (by omega)) hjz.symm
  · exact hout _ _ (ladderNode_out_pos N (N+(k+1)) (k+1) x' y' (j+2) Cn hCold hy' (by omega)
      (by omega))
      (ladderNode_out_pos N (N+(k+1)) (k+1) x' y' (j+3) Cn hCold hy' (by omega) (by omega)) hjz.symm
  · exact hout _ _ (fun h => by have := hCold _ h; omega)
      (fun h => by have := hCold _ h; omega) hjz.symm

/-- Relabeling the rest by the skip map gives the `k`-version rails (without the first
bond) and rungs. -/
theorem restX_map_skip (N k x y x' y' : ℕ) (hx : x < N) (hy : y < N) (hx' : x' < N)
    (hy' : y' < N) (R : Multiset (Sym2 ℕ)) (hR : ∀ e ∈ R,∀ z ∈ e,z < N) :
    (restX N k x y x' y' R).map (Sym2.map (skip2 N (N+(k+1)))) =
      R + (((List.range k).map (fun j => s(ladderNode x y N k (j+1),ladderNode x y N k (j+2))) :
          List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) +
        (((List.range k).map (fun j => s(ladderNode x' y' (N+k) k (j+1),
          ladderNode x' y' (N+k) k (j+2))) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) +
        2 • (((List.range k).map (fun j => s(N+j,N+k+j)) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) := by
  have hRm : R.map (Sym2.map (skip2 N (N+(k+1)))) = R := by
    conv_rhs => rw [← Multiset.map_id R]
    apply Multiset.map_congr rfl
    intro e he
    revert he
    induction e using Sym2.ind with
    | h a b =>
      intro he
      have ha := hR _ he a (Sym2.mem_mk_left _ _)
      have hb := hR _ he b (Sym2.mem_mk_right _ _)
      simp only [Sym2.map_mk,id,skip2_lt N (N+(k+1)) a (by omega) (by omega),
        skip2_lt N (N+(k+1)) b (by omega) (by omega)]
  unfold restX
  simp only [Multiset.map_add,Multiset.map_coe,Multiset.map_nsmul,hRm,List.map_map]
  have L1 : List.map (Sym2.map (skip2 N (N+(k+1))) ∘ fun j =>
      s(ladderNode x y N (k+1) (j+2),ladderNode x y N (k+1) (j+3))) (List.range k) =
      (List.range k).map (fun j => s(ladderNode x y N k (j+1),ladderNode x y N k (j+2))) := by
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [Function.comp_apply,Sym2.map_mk]
    rw [contractX_nu N k x y (j+1) hx hy (by omega) (by omega),
      contractX_nu N k x y (j+2) hx hy (by omega) (by omega)]
  have L2 : List.map (Sym2.map (skip2 N (N+(k+1))) ∘ fun j =>
      s(ladderNode x' y' (N+(k+1)) (k+1) (j+2),ladderNode x' y' (N+(k+1)) (k+1) (j+3)))
      (List.range k) =
      (List.range k).map (fun j => s(ladderNode x' y' (N+k) k (j+1),ladderNode x' y' (N+k) k (j+2))) := by
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [Function.comp_apply,Sym2.map_mk]
    rw [contractX_nv N k x' y' (j+1) hx' hy' (by omega) (by omega),
      contractX_nv N k x' y' (j+2) hx' hy' (by omega) (by omega)]
  have L3 : List.map (Sym2.map (skip2 N (N+(k+1))) ∘ fun j => s(N+(j+1),N+(k+1)+(j+1)))
      (List.range k) = (List.range k).map (fun j => s(N+j,N+k+j)) := by
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [Function.comp_apply,Sym2.map_mk,skip2]
    congr 2 <;> split_ifs <;> omega
  rw [L1,L2,L3]

theorem exists_slot_contraction_X (N k x y x' y' : ℕ) (hx : x < N) (hy : y < N) (hx' : x' < N)
    (hy' : y' < N) (R : Multiset (Sym2 ℕ)) (hR : ∀ e ∈ R,∀ z ∈ e,z < N)
    (Cn : Finset ℕ) (hCold : ∀ t ∈ Cn,t < N)
    (hxC : x ∈ Cn) (hx'C : x' ∈ Cn) (hyC : y ∉ Cn) (hy'C : y' ∉ Cn)
    (hRcross : ∀ z ∈ R,∀ a b : ℕ,z = s(a,b) → (a ∈ Cn ↔ b ∈ Cn))
    (ν : ℕ ≃ ℕ) (hνout : ∀ t ∉ Cn,ν t = t) (hνmem : ∀ t,ν t ∈ Cn ↔ t ∈ Cn)
    (hνx : ν x = x') (hνx' : ν x' = x) (hνR : R.map (Sym2.map ν) = R)
    {β : Type} [Fintype β] [DecidableEq β]
    (ends : β → Fin (N+2*k+2) × Fin (N+2*k+2))
    (hU : (univ : Finset β).val.map (fun e => s((ends e).1.1,(ends e).2.1)) =
      insSym N x y x' y' (k+1) R)
    (hbal : ∀ v,(∑ e,-energySign ends v e) = 0) :
    ∃ G : RungSpliceGeometry (Fin (N+2*k)) (RestEdge N (N+(k+1)) ends ⊕ Fin 2),
      ((univ : Finset (RestEdge N (N+(k+1)) ends ⊕ Fin 2)).val.map
        (fun e => s((G.ends e).1.1,(G.ends e).2.1)) = insSym N x y x' y' k R) ∧
      G.cap = capFin (N+2*k) Cn ∧
      (∀ u : Fin (N+2*k),(G.σ u).1 = u.1 ∨ (G.σ u).1 = ν u.1) ∧
      ((∀ u : Fin (N+2*k),(G.σ u).1 = u.1) ∨ (∀ u : Fin (N+2*k),(G.σ u).1 = ν u.1)) ∧
      ((G.p).1 = y ∨ N ≤ (G.p).1) ∧ ((G.q).1 = y' ∨ N ≤ (G.q).1) ∧ (G.c).1 = x ∧ (G.d).1 = x' ∧
      ∃ J : DirectedGraphIso G.newEnds ends,
        (∀ u : Fin (N+2*k),(u.1 < N → (J.atom (Sum.inl u)).1 = u.1) ∧
          (N ≤ u.1 → N ≤ (J.atom (Sum.inl u)).1)) ∧
        (∀ j,N ≤ (J.atom (Sum.inr j)).1) ∧
        (∀ u : Fin (N+2*k),(J.atom (Sum.inl u)).1 = unskip2 N (N+(k+1)) u.1) ∧
        (J.atom (Sum.inr 0)).1 = N ∧ (J.atom (Sum.inr 1)).1 = (N+(k+1)) := by
  classical
  have h : N < N+(k+1) := by omega
  have h1 : N+(k+1) < (N+2*k)+2 := by omega
  have hpl : ladderNode x y N (k+1) 2 < (N+2*k)+2 := ladderNode_lt x y N (k+1) 2 _ (by omega)
    (by omega) (by omega) (Or.inr (by omega))
  have hql : ladderNode x' y' (N+(k+1)) (k+1) 2 < (N+2*k)+2 :=
    ladderNode_lt x' y' (N+(k+1)) (k+1) 2 _ (by omega) (by omega) (by omega) (Or.inr (by omega))
  let p : Fin ((N+2*k)+2) := ⟨ladderNode x y N (k+1) 2,hpl⟩
  let q : Fin ((N+2*k)+2) := ⟨ladderNode x' y' (N+(k+1)) (k+1) 2,hql⟩
  let c : Fin ((N+2*k)+2) := ⟨x,by omega⟩
  let d : Fin ((N+2*k)+2) := ⟨x',by omega⟩
  have hpv : p.1 = y ∨ (p.1 = N+1 ∧ 1 ≤ k) := by
    simp only [p,ladderNode]; split_ifs <;> first | omega | contradiction
  have hqv : q.1 = y' ∨ (q.1 = N+(k+1)+1 ∧ 1 ≤ k) := by
    simp only [q,ladderNode]; split_ifs <;> first | omega | contradiction
  have hp : p.1 ≠ N ∧ p.1 ≠ N+(k+1) := by omega
  have hq : q.1 ≠ N ∧ q.1 ≠ N+(k+1) := by omega
  have hc : c.1 ≠ N ∧ c.1 ≠ N+(k+1) := by simp only [c]; omega
  have hd : d.1 ≠ N ∧ d.1 ≠ N+(k+1) := by simp only [d]; omega
  have hcell : (((cellRef N (N+(k+1)) p.1 q.1 c.1 d.1).map fun e => s(e.1,e.2) :
      List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) = cellX N k x y x' y' := by
    unfold cellX cellRef
    simp only [List.map_cons,List.map_nil,← Multiset.cons_coe,Multiset.coe_nil,
      ← Multiset.singleton_add,two_nsmul,Multiset.add_zero,p,q,c,d]
    rw [sing_swap (ladderNode x y N (k+1) 2) N,sing_swap (ladderNode x' y' (N+(k+1)) (k+1) 2) (N+(k+1)),
      sing_swap N x,sing_swap (N+(k+1)) x']
    abel
  have hU' : (univ : Finset β).val.map (fun e => s((ends e).1.1,(ends e).2.1)) =
      (((cellRef N (N+(k+1)) p.1 q.1 c.1 d.1).map fun e => s(e.1,e.2) : List (Sym2 ℕ)) :
        Multiset (Sym2 ℕ)) + restX N k x y x' y' R := by
    rw [hU,contractX_split,hcell]
  have hpC : p.1 ∉ Cn := by
    intro hm; have := hCold _ hm
    rcases hpv with h' | h'
    · exact hyC (h' ▸ hm)
    · omega
  have hqC : q.1 ∉ Cn := by
    intro hm; have := hCold _ hm
    rcases hqv with h' | h'
    · exact hy'C (h' ▸ hm)
    · omega
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
  have hinv : (((restX N k x y x' y' R).map (Sym2.map (skip2 N (N+(k+1))))).map
      (Sym2.map (fun t : ℕ => if ht : t < N+2*k then (σ0.symm ⟨t,ht⟩).1 else t))) =
      (restX N k x y x' y' R).map (Sym2.map (skip2 N (N+(k+1)))) := by
    rw [restX_map_skip N k x y x' y' hx hy hx' hy' R hR]
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
        fun j => s(ladderNode x y N k (j+1),ladderNode x y N k (j+2))) (List.range k) =
        (List.range k).map (fun j => s(ladderNode x y N k (j+1),ladderNode x y N k (j+2))) := by
      apply List.map_congr_left
      intro j hj
      have hj := List.mem_range.mp hj
      have a1 := ladderNode_out_pos N N k x y (j+1) Cn hCold hyC le_rfl (by omega)
      have a2 := ladderNode_out_pos N N k x y (j+2) Cn hCold hyC le_rfl (by omega)
      have b1 : ladderNode x y N k (j+1) < N+2*k := ladderNode_lt x y N k (j+1) _ (by omega)
        (by omega) (by omega) (Or.inr (by omega))
      have b2 : ladderNode x y N k (j+2) < N+2*k := ladderNode_lt x y N k (j+2) _ (by omega)
        (by omega) (by omega) (Or.inr (by omega))
      have c1 := hlbl2 _ b1 a1
      have c2 := hlbl2 _ b2 a2
      beta_reduce at c1 c2
      simp only [Function.comp_apply,Sym2.map_mk]
      rw [c1,c2]
    have hl2 : List.map (Sym2.map (fun t : ℕ => if ht : t < N+2*k then (σ0.symm ⟨t,ht⟩).1 else t) ∘
        fun j => s(ladderNode x' y' (N+k) k (j+1),ladderNode x' y' (N+k) k (j+2))) (List.range k) =
        (List.range k).map (fun j => s(ladderNode x' y' (N+k) k (j+1),ladderNode x' y' (N+k) k (j+2))) := by
      apply List.map_congr_left
      intro j hj
      have hj := List.mem_range.mp hj
      have a1 := ladderNode_out_pos N (N+k) k x' y' (j+1) Cn hCold hy'C (by omega) (by omega)
      have a2 := ladderNode_out_pos N (N+k) k x' y' (j+2) Cn hCold hy'C (by omega) (by omega)
      have b1 : ladderNode x' y' (N+k) k (j+1) < N+2*k := ladderNode_lt x' y' (N+k) k (j+1) _
        (by omega) (by omega) (by omega) (Or.inr (by omega))
      have b2 : ladderNode x' y' (N+k) k (j+2) < N+2*k := ladderNode_lt x' y' (N+k) k (j+2) _
        (by omega) (by omega) (by omega) (Or.inr (by omega))
      have c1 := hlbl2 _ b1 a1
      have c2 := hlbl2 _ b2 a2
      beta_reduce at c1 c2
      simp only [Function.comp_apply,Sym2.map_mk]
      rw [c1,c2]
    have hl3 : List.map (Sym2.map (fun t : ℕ => if ht : t < N+2*k then (σ0.symm ⟨t,ht⟩).1 else t) ∘
        fun j => s(N+j,N+k+j)) (List.range k) = (List.range k).map (fun j => s(N+j,N+k+j)) := by
      apply List.map_congr_left
      intro j hj
      have hj := List.mem_range.mp hj
      have a1 : N+j ∉ Cn := fun hm => by have := hCold _ hm; omega
      have a2 : N+k+j ∉ Cn := fun hm => by have := hCold _ hm; omega
      have c1 := hlbl2 (N+j) (by omega) a1
      have c2 := hlbl2 (N+k+j) (by omega) a2
      beta_reduce at c1 c2
      simp only [Function.comp_apply,Sym2.map_mk]
      rw [c1,c2]
    rw [hl1,hl2,hl3]
  have hσ0C : ∀ u : Fin (N+2*k),σ0 u ∈ capFin (N+2*k) Cn ↔ u ∈ capFin (N+2*k) Cn := by
    intro u
    simp only [capFin,mem_filter,mem_univ,true_and]
    rw [reflFinGen_apply]
    exact hνmem u.1
  have hskp : skip2 N (N+(k+1)) p.1 ∉ Cn := by
    rcases hpv with h' | h'
    · rw [skip2_lt N (N+(k+1)) p.1 (by omega) (by omega),h']; exact hyC
    · intro hm; have := hCold _ hm
      have : N ≤ skip2 N (N+(k+1)) p.1 := by simp only [skip2]; split_ifs <;> omega
      omega
  have hskq : skip2 N (N+(k+1)) q.1 ∉ Cn := by
    rcases hqv with h' | h'
    · rw [skip2_lt N (N+(k+1)) q.1 (by omega) (by omega),h']; exact hy'C
    · intro hm; have := hCold _ hm
      have : N ≤ skip2 N (N+(k+1)) q.1 := by simp only [skip2]; split_ifs <;> omega
      omega
  have hx1 : skip2 N (N+(k+1)) x = x := skip2_lt _ _ _ (by omega) (by omega)
  have hx2 : skip2 N (N+(k+1)) x' = x' := skip2_lt _ _ _ (by omega) (by omega)
  obtain ⟨G,hGends,hGcap,hGp,hGq,hGc,hGd,hGσ,hshadow,J,hJ⟩ :=
    exists_contracted_geometry N (N+(k+1)) h h1 ends p q c d hp hq hc hd
      (restX N k x y x' y' R) (restX_avoid N k x y x' y' hx hy hx' hy' R hR) hU' Cn hCold
      hpC hqC hxC hx'C
      (restX_uncut N k x y x' y' R Cn hCold hyC hy'C hRcross) hbal σ0 hσ0C
      (Fin.ext (by
        change ν (skip2 N (N+(k+1)) p.1) = skip2 N (N+(k+1)) p.1
        exact hνout _ hskp))
      (Fin.ext (by
        change ν (skip2 N (N+(k+1)) q.1) = skip2 N (N+(k+1)) q.1
        exact hνout _ hskq))
      (Fin.ext (by
        change ν (skip2 N (N+(k+1)) x) = skip2 N (N+(k+1)) x'
        rw [hx1,hx2]; exact hνx))
      (Fin.ext (by
        change ν (skip2 N (N+(k+1)) x') = skip2 N (N+(k+1)) x
        rw [hx1,hx2]; exact hνx'))
      hinv
  refine ⟨G,?_,hGcap,?_,?_,?_,?_,?_,?_,J,?_,?_,?_,?_,?_⟩
  · rw [hshadow,contractX_back N k x y x' y' hx hy hx' hy' R hR]
    have e1 : s((skipFinP N (N+(k+1)) h h1 p hp).1,(skipFinP N (N+(k+1)) h h1 c hc).1) =
        s(skip2 N (N+(k+1)) x,skip2 N (N+(k+1)) (ladderNode x y N (k+1) 2)) := Sym2.eq_swap
    have e2 : s((skipFinP N (N+(k+1)) h h1 q hq).1,(skipFinP N (N+(k+1)) h h1 d hd).1) =
        s(skip2 N (N+(k+1)) x',skip2 N (N+(k+1)) (ladderNode x' y' (N+(k+1)) (k+1) 2)) :=
      Sym2.eq_swap
    rw [e1,e2]
  · intro u
    rcases hGσ with h' | h'
    · right; rw [h']; exact reflFinGen_apply ν Cn N (N+2*k) hCold (by omega) hνout hνmem u
    · left; rw [h']; rfl
  · rcases hGσ with h' | h'
    · right; intro u; rw [h']; exact reflFinGen_apply ν Cn N (N+2*k) hCold (by omega) hνout hνmem u
    · left; intro u; rw [h']; rfl
  · rw [hGp]
    change skip2 N (N+(k+1)) p.1 = y ∨ N ≤ skip2 N (N+(k+1)) p.1
    rcases hpv with h' | h'
    · left; rw [skip2_lt N (N+(k+1)) p.1 (by omega) (by omega),h']
    · right; simp only [skip2]; split_ifs <;> omega
  · rw [hGq]
    change skip2 N (N+(k+1)) q.1 = y' ∨ N ≤ skip2 N (N+(k+1)) q.1
    rcases hqv with h' | h'
    · left; rw [skip2_lt N (N+(k+1)) q.1 (by omega) (by omega),h']
    · right; simp only [skip2]; split_ifs <;> omega
  · rw [hGc]
    change skip2 N (N+(k+1)) x = x
    exact hx1
  · rw [hGd]
    change skip2 N (N+(k+1)) x' = x'
    exact hx2
  · intro u
    constructor
    · intro hu
      rw [hJ]
      change unskip2 N (N+(k+1)) u.1 = u.1
      exact unskip2_eq_of_lt _ _ _ hu h
    · intro hu
      rw [hJ]
      change N ≤ unskip2 N (N+(k+1)) u.1
      have := unskip2_ge N (N+(k+1)) u.1
      omega
  · intro j
    rw [hJ]
    fin_cases j
    · change N ≤ (if (0 : Fin 2) = 0 then (⟨N,by omega⟩ : Fin ((N+2*k)+2)) else ⟨N+(k+1),h1⟩).1
      simp
    · change N ≤ (if (1 : Fin 2) = 0 then (⟨N,by omega⟩ : Fin ((N+2*k)+2)) else ⟨N+(k+1),h1⟩).1
      simp
  · intro u
    rw [hJ]
    rfl
  · rw [hJ]
    change (if (0 : Fin 2) = 0 then (⟨N,by omega⟩ : Fin ((N+2*k)+2)) else ⟨(N+(k+1)),h1⟩).1 = _
    simp
  · rw [hJ]
    change (if (1 : Fin 2) = 0 then (⟨N,by omega⟩ : Fin ((N+2*k)+2)) else ⟨(N+(k+1)),h1⟩).1 = _
    simp

end WaveTurbulence.Vine.Param
