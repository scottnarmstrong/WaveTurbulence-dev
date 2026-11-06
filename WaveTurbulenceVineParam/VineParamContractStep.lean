/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCellIso
public import WaveTurbulenceVineParam.VineParamContractedGeometry
public import WaveTurbulenceVineParam.VineParamSpliceOrientation
public import WaveTurbulenceVineParam.VineParamBalancedCutOrientation
public import WaveTurbulenceVineParam.VineParamLiftedCap
public import WaveTurbulenceVineParam.VineParamDirectedIsoDegrees
public import WaveTurbulenceVineParam.VineParamRawCellDegrees
import Mathlib.Tactic

/-! # One-rung contraction of a balanced directed graph at a marked cap

From the shadow cell data (`exists_cell_iso`), balance, and a cap structure, build
the exact `RungSpliceGeometry` whose spliced graph is the original one.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset

variable {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]

/-- The cap in the contracted label space. -/
@[expose] def capFin (n : ℕ) (C : Finset ℕ) : Finset (Fin n) := univ.filter fun u => u.1 ∈ C

theorem skip2_mem_cap (f0 f1 : ℕ) (Cn : Finset ℕ) (hCold : ∀ t ∈ Cn, t < f0) (h : f0 < f1)
    (t : ℕ) (h0 : t ≠ f0) (h1 : t ≠ f1) : skip2 f0 f1 t ∈ Cn ↔ t ∈ Cn := by
  by_cases ht : t < f0
  · rw [skip2_lt f0 f1 t ht h.le]
  · have h2 : f0 ≤ skip2 f0 f1 t := by simp only [skip2]; split_ifs <;> omega
    constructor
    · intro hm; have := hCold _ hm; omega
    · intro hm; have := hCold _ hm; omega

theorem exists_contracted_geometry (f0 f1 : ℕ) (h : f0 < f1) (h1 : f1 < n+2)
    (ends : β → Fin (n+2) × Fin (n+2)) (p q c d : Fin (n+2))
    (hp : p.1 ≠ f0 ∧ p.1 ≠ f1) (hq : q.1 ≠ f0 ∧ q.1 ≠ f1)
    (hc : c.1 ≠ f0 ∧ c.1 ≠ f1) (hd : d.1 ≠ f0 ∧ d.1 ≠ f1)
    (Rest : Multiset (Sym2 ℕ)) (hRest : ∀ e ∈ Rest, ∀ z ∈ e, z ≠ f0 ∧ z ≠ f1)
    (hU : (univ : Finset β).val.map (fun e => s((ends e).1.1,(ends e).2.1)) =
      (((cellRef f0 f1 p.1 q.1 c.1 d.1).map fun e => s(e.1,e.2) : List (Sym2 ℕ)) :
        Multiset (Sym2 ℕ)) + Rest)
    (Cn : Finset ℕ) (hCold : ∀ t ∈ Cn, t < f0)
    (hpC : p.1 ∉ Cn) (hqC : q.1 ∉ Cn) (hcC : c.1 ∈ Cn) (hdC : d.1 ∈ Cn)
    (huncutRest : ∀ z ∈ Rest, ∀ a b : ℕ, z = s(a,b) → (a ∈ Cn ↔ b ∈ Cn))
    (hbal : ∀ v, (∑ e, -energySign ends v e) = 0)
    (σ0 : Fin n ≃ Fin n) (hσ0C : ∀ u : Fin n, σ0 u ∈ capFin n Cn ↔ u ∈ capFin n Cn)
    (hσ0p : σ0 (skipFinP f0 f1 h h1 p hp) = skipFinP f0 f1 h h1 p hp)
    (hσ0q : σ0 (skipFinP f0 f1 h h1 q hq) = skipFinP f0 f1 h h1 q hq)
    (hσ0c : σ0 (skipFinP f0 f1 h h1 c hc) = skipFinP f0 f1 h h1 d hd)
    (hσ0d : σ0 (skipFinP f0 f1 h h1 d hd) = skipFinP f0 f1 h h1 c hc)
    (hσ0inv : (Rest.map (Sym2.map (skip2 f0 f1))).map
        (Sym2.map (fun t : ℕ => if ht : t < n then (σ0.symm ⟨t,ht⟩).1 else t)) =
      Rest.map (Sym2.map (skip2 f0 f1))) :
    ∃ G : RungSpliceGeometry (Fin n) (RestEdge f0 f1 ends ⊕ Fin 2),
      G.ends = contractedEnds (restEnds f0 f1 h h1 ends) G.σ G.p G.q G.c G.d G.pattern ∧
      G.cap = capFin n Cn ∧ G.p = skipFinP f0 f1 h h1 p hp ∧ G.q = skipFinP f0 f1 h h1 q hq ∧
      G.c = skipFinP f0 f1 h h1 c hc ∧ G.d = skipFinP f0 f1 h h1 d hd ∧
      (G.σ = σ0 ∨ G.σ = Equiv.refl _) ∧
      ((univ : Finset (RestEdge f0 f1 ends ⊕ Fin 2)).val.map
          (fun e => s((G.ends e).1.1,(G.ends e).2.1)) =
        Rest.map (Sym2.map (skip2 f0 f1)) + {s((skipFinP f0 f1 h h1 p hp).1,(skipFinP f0 f1 h h1 c hc).1)} +
          {s((skipFinP f0 f1 h h1 q hq).1,(skipFinP f0 f1 h h1 d hd).1)}) ∧
      ∃ J : DirectedGraphIso G.newEnds ends, ∀ w, J.atom w = (skipEquiv n f0 f1 h h1).symm w := by
  classical
  obtain ⟨p',hp'⟩ : ∃ x, x = skipFinP f0 f1 h h1 p hp := ⟨_,rfl⟩
  obtain ⟨q',hq'⟩ : ∃ x, x = skipFinP f0 f1 h h1 q hq := ⟨_,rfl⟩
  obtain ⟨c',hc'⟩ : ∃ x, x = skipFinP f0 f1 h h1 c hc := ⟨_,rfl⟩
  obtain ⟨d',hd'⟩ : ∃ x, x = skipFinP f0 f1 h h1 d hd := ⟨_,rfl⟩
  have hσp0 : σ0 p' = p' := by rw [hp']; exact hσ0p
  have hσq0 : σ0 q' = q' := by rw [hq']; exact hσ0q
  have hσc0 : σ0 c' = d' := by rw [hc',hd']; exact hσ0c
  have hσd0 : σ0 d' = c' := by rw [hc',hd']; exact hσ0d
  obtain ⟨s,hs,hrestU,hshadow,I,hIa⟩ := exists_cell_iso f0 f1 h h1 ends p q c d hp hq hc hd p' q' c' d'
    hp' hq' hc' hd' Rest hRest hU
  have huncut : ∀ e, touchFree f0 f1 ends e → ((ends e).1.1 ∈ Cn ↔ (ends e).2.1 ∈ Cn) := by
    intro e he
    apply huncutRest s((ends e).1.1,(ends e).2.1) _ _ _ rfl
    rw [← hrestU]
    exact Multiset.mem_map_of_mem _ (by simpa using he)
  have hbalR : ∀ w, (∑ e, -energySign (rawSourceCellEnds (restEnds f0 f1 h h1 ends) p' q' c' d' s) w e) = 0 := by
    intro w
    obtain ⟨v,rfl⟩ := I.atom.surjective w
    rw [I.degree_eq]
    exact hbal v
  have hu : s 2+s 3+s 4-s 0=0 :=
    (rawCell_upper_degree (restEnds f0 f1 h h1 ends) p' q' c' d' s hs).symm.trans (hbalR _)
  have hl : s 5-s 1-s 2-s 3=0 :=
    (rawCell_lower_degree (restEnds f0 f1 h h1 ends) p' q' c' d' s hs).symm.trans (hbalR _)
  have hcapmem : ∀ t : Fin (n+2), t.1 ≠ f0 → t.1 ≠ f1 → (∀ u : Fin n, u.1 = skip2 f0 f1 t.1 →
      (u ∈ capFin n Cn ↔ t.1 ∈ Cn)) := by
    intro t h0 h1' u hu
    simp only [capFin,mem_filter,mem_univ,true_and,hu]
    exact skip2_mem_cap f0 f1 Cn hCold h t.1 h0 h1'
  have hcn : (Sum.inl c' : Fin n ⊕ Fin 2) ∈ liftedCap (capFin n Cn) := by
    simp only [liftedCap,mem_image,Sum.inl.injEq,exists_eq_right]
    exact (hcapmem c hc.1 hc.2 c' (by rw [hc']; rfl)).mpr hcC
  have hdn : (Sum.inl d' : Fin n ⊕ Fin 2) ∈ liftedCap (capFin n Cn) := by
    simp only [liftedCap,mem_image,Sum.inl.injEq,exists_eq_right]
    exact (hcapmem d hd.1 hd.2 d' (by rw [hd']; rfl)).mpr hdC
  have hpn : (Sum.inl p' : Fin n ⊕ Fin 2) ∉ liftedCap (capFin n Cn) := by
    simp only [liftedCap,mem_image,Sum.inl.injEq,exists_eq_right]
    exact fun hm => hpC ((hcapmem p hp.1 hp.2 p' (by rw [hp']; rfl)).mp hm)
  have hqn : (Sum.inl q' : Fin n ⊕ Fin 2) ∉ liftedCap (capFin n Cn) := by
    simp only [liftedCap,mem_image,Sum.inl.injEq,exists_eq_right]
    exact fun hm => hqC ((hcapmem q hq.1 hq.2 q' (by rw [hq']; rfl)).mp hm)
  have hr0 : (Sum.inr 0 : Fin n ⊕ Fin 2) ∉ liftedCap (capFin n Cn) := by simp [liftedCap]
  have hr1 : (Sum.inr 1 : Fin n ⊕ Fin 2) ∉ liftedCap (capFin n Cn) := by simp [liftedCap]
  have hrestC : ∀ e : β ⊕ Fin 6 → Prop, True := fun _ => trivial
  have hcap : s 4+s 5=0 := by
    have key := balanced_two_edge_directions (rawSourceCellEnds (restEnds f0 f1 h h1 ends) p' q' c' d' s)
      (liftedCap (capFin n Cn)) (Sum.inr 4) (Sum.inr 5) (by simp) (Sum.inr 0) (Sum.inr 1)
      (Sum.inl c') (Sum.inl d') hr0 hr1 hcn hdn (s 4) (s 5) (hs 4) (hs 5) rfl rfl ?_ hbalR
    · exact key
    · intro e h4 h5
      rcases e with e | j
      · simp only [rawSourceCellEnds,liftedCap,mem_image,Sum.inl.injEq,exists_eq_right]
        have hy := (mem_filter.mp e.2).2
        have hu := huncut e.1 hy
        change skipFin f0 f1 h h1 (ends e.1).1 hy.1 hy.2.1 ∈ capFin n Cn ↔
          skipFin f0 f1 h h1 (ends e.1).2 hy.2.2.1 hy.2.2.2 ∈ capFin n Cn
        rw [hcapmem (ends e.1).1 hy.1 hy.2.1 _ rfl,hcapmem (ends e.1).2 hy.2.2.1 hy.2.2.2 _ rfl]
        exact hu
      · fin_cases j
        · rcases hs 0 with h' | h' <;>
            simp [rawSourceCellEnds,sourceCellPorts,orientPair,h',hpn,hr0,hr1,hqn]
        · rcases hs 1 with h' | h' <;>
            simp [rawSourceCellEnds,sourceCellPorts,orientPair,h',hpn,hr0,hr1,hqn]
        · rcases hs 2 with h' | h' <;>
            simp [rawSourceCellEnds,sourceCellPorts,orientPair,h',hpn,hr0,hr1,hqn]
        · rcases hs 3 with h' | h' <;>
            simp [rawSourceCellEnds,sourceCellPorts,orientPair,h',hpn,hr0,hr1,hqn]
        · exact (h4 rfl).elim
        · exact (h5 rfl).elim
  obtain ⟨P,hP⟩ := exists_splice_orientation s hs hu hl hcap
  have hnorm : rawSourceCellEnds (restEnds f0 f1 h h1 ends) p' q' c' d' s = sourceCellEnds (restEnds f0 f1 h h1 ends) p' q' c' d' P := by
    rw [hP]; exact rawSourceCell_normalized (restEnds f0 f1 h h1 ends) p' q' c' d' P
  let I2 : DirectedGraphIso ends (sourceCellEnds (restEnds f0 f1 h h1 ends) p' q' c' d' P) :=
    { atom := I.atom, edge := I.edge,
      endpoints := fun e => by rw [← hnorm]; exact I.endpoints e }
  have hsource : ∀ v, (∑ e, -energySign (sourceCellEnds (restEnds f0 f1 h h1 ends) p' q' c' d' P) v e) = 0 := by
    intro v; rw [← hnorm]; exact hbalR v
  let σ : Fin n ≃ Fin n := if P.reversesPorts then σ0 else Equiv.refl _
  have hσp : σ p' = p' := by cases hr : P.reversesPorts <;> simp [σ,hr,hσp0]
  have hσq : σ q' = q' := by cases hr : P.reversesPorts <;> simp [σ,hr,hσq0]
  have hσc : σ c' = if P.reversesPorts then d' else c' := by
    cases hr : P.reversesPorts <;> simp [σ,hr,hσc0]
  have hσd : σ d' = if P.reversesPorts then c' else d' := by
    cases hr : P.reversesPorts <;> simp [σ,hr,hσd0]
  have hσC : ∀ v, σ v ∈ capFin n Cn ↔ v ∈ capFin n Cn := by
    intro v; cases hr : P.reversesPorts <;> simp [σ,hr,hσ0C]
  have hpC' : p' ∉ capFin n Cn := fun hm => hpC ((hcapmem p hp.1 hp.2 p' (by rw [hp']; rfl)).mp hm)
  have hqC' : q' ∉ capFin n Cn := fun hm => hqC ((hcapmem q hq.1 hq.2 q' (by rw [hq']; rfl)).mp hm)
  have hcC' : c' ∈ capFin n Cn := (hcapmem c hc.1 hc.2 c' (by rw [hc']; rfl)).mpr hcC
  have hdC' : d' ∈ capFin n Cn := (hcapmem d hd.1 hd.2 d' (by rw [hd']; rfl)).mpr hdC
  have hrC : ∀ e, (restEnds f0 f1 h h1 ends e).1 ∈ capFin n Cn ↔ (restEnds f0 f1 h h1 ends e).2 ∈ capFin n Cn := by
    intro e
    have hy := (mem_filter.mp e.2).2
    have hu := huncut e.1 hy
    change skipFin f0 f1 h h1 (ends e.1).1 hy.1 hy.2.1 ∈ capFin n Cn ↔
      skipFin f0 f1 h h1 (ends e.1).2 hy.2.2.1 hy.2.2.2 ∈ capFin n Cn
    rw [hcapmem (ends e.1).1 hy.1 hy.2.1 _ rfl,hcapmem (ends e.1).2 hy.2.2.1 hy.2.2.2 _ rfl]
    exact hu
  let G := contractedGeometry (restEnds f0 f1 h h1 ends) σ p' q' c' d' P (capFin n Cn) hpC' hqC' hcC' hdC'
    hσp hσq hσc hσd hσC hrC hsource
  have hIsymm : ∀ w, I2.symm.atom w = (skipEquiv n f0 f1 h h1).symm w := by
    intro w
    have : I.atom = skipEquiv n f0 f1 h h1 := Equiv.ext hIa
    change I.atom.symm w = _
    rw [this]
  have hshadowG : ((univ : Finset (RestEdge f0 f1 ends ⊕ Fin 2)).val.map
          (fun e => s((G.ends e).1.1,(G.ends e).2.1)) =
        Rest.map (Sym2.map (skip2 f0 f1)) + {s(p'.1,c'.1)} + {s(q'.1,d'.1)}) := by
    have hsum : (univ : Finset (RestEdge f0 f1 ends ⊕ Fin 2)).val.map
          (fun e => s((G.ends e).1.1,(G.ends e).2.1)) =
        (univ : Finset (RestEdge f0 f1 ends)).val.map
          (fun e => s((G.ends (Sum.inl e)).1.1,(G.ends (Sum.inl e)).2.1)) +
        (univ : Finset (Fin 2)).val.map
          (fun j => s((G.ends (Sum.inr j)).1.1,(G.ends (Sum.inr j)).2.1)) := by
      change ((univ : Finset (RestEdge f0 f1 ends)).disjSum (univ : Finset (Fin 2))).val.map _ = _
      rw [Finset.val_disjSum,Multiset.map_disjSum]
    rw [hsum]
    have hinr : (univ : Finset (Fin 2)).val.map
          (fun j => s((G.ends (Sum.inr j)).1.1,(G.ends (Sum.inr j)).2.1)) =
        {s(p'.1,c'.1)} + {s(q'.1,d'.1)} := by
      rw [Fin.univ_val_map]
      have hop : ∀ (sg : ℤ) (u w : Fin n),
          s((orientPair sg u w).1.1,(orientPair sg u w).2.1) = s(u.1,w.1) := by
        intro sg u w
        unfold orientPair
        split_ifs
        · rfl
        · exact Sym2.eq_swap
      simp only [List.ofFn_succ,List.ofFn_zero,Fin.isValue,Multiset.coe_singleton]
      change (([s((orientPair (P.signs 2) p' c').1.1,(orientPair (P.signs 2) p' c').2.1),
          s((orientPair (-P.signs 2) q' d').1.1,(orientPair (-P.signs 2) q' d').2.1)] :
          List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) = _
      rw [hop,hop]
      rfl
    have hinl : (univ : Finset (RestEdge f0 f1 ends)).val.map
          (fun e => s((G.ends (Sum.inl e)).1.1,(G.ends (Sum.inl e)).2.1)) =
        Rest.map (Sym2.map (skip2 f0 f1)) := by
      have hlbl : (univ : Finset (RestEdge f0 f1 ends)).val.map
          (fun e => s((G.ends (Sum.inl e)).1.1,(G.ends (Sum.inl e)).2.1)) =
        ((univ : Finset (RestEdge f0 f1 ends)).val.map
          (fun e => s((restEnds f0 f1 h h1 ends e).1.1,(restEnds f0 f1 h h1 ends e).2.1))).map
          (Sym2.map (fun t : ℕ => if ht : t < n then (σ.symm ⟨t,ht⟩).1 else t)) := by
        rw [Multiset.map_map]
        apply Multiset.map_congr rfl
        intro e _
        change s((σ.symm (restEnds f0 f1 h h1 ends e).1).1,(σ.symm (restEnds f0 f1 h h1 ends e).2).1) = _
        simp only [Function.comp_apply,Sym2.map_mk]
        rw [dif_pos (restEnds f0 f1 h h1 ends e).1.2,dif_pos (restEnds f0 f1 h h1 ends e).2.2]
      rw [hlbl,hshadow]
      cases hr : P.reversesPorts
      · have hσr : σ = Equiv.refl _ := by simp [σ,hr]
        rw [hσr]
        simp
      · have hσr : σ = σ0 := by simp [σ,hr]
        rw [hσr]
        exact hσ0inv
    rw [hinl,hinr]
    abel
  have hshadowG' := hshadowG
  rw [hp',hq',hc',hd'] at hshadowG'
  refine ⟨G,rfl,rfl,hp',hq',hc',hd',?_,hshadowG',
    ⟨(contractedSpliceIso (restEnds f0 f1 h h1 ends) σ p' q' c' d' P).trans I2.symm,?_⟩⟩
  · by_cases hr : P.reversesPorts
    · exact Or.inl (by simp [G,σ,hr,contractedGeometry])
    · exact Or.inr (by simp [G,σ,hr,contractedGeometry])
  · intro w
    exact hIsymm w

end WaveTurbulence.Vine.Param
