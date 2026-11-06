/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamExpandBase
public import WaveTurbulenceVineParam.VineParamExpandReflect
public import WaveTurbulenceVineParam.VineParamStepX
public import WaveTurbulenceVineParam.VineParamInsertedPhysicalChart
public import WaveTurbulenceVineParam.VineParamInsertedSelectedSupport
public import WaveTurbulenceVineParam.VineParamOtherCapSupport
public import WaveTurbulenceVineParam.VineParamInsertedPairSupport
public import WaveTurbulenceVineParam.VineParamGroupExpand
import Mathlib.Tactic

/-! # The expanded-template induction: one slot step -/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- Contraction data at a slot, abstract in the prefix template, the slot, the cap and the
cap reflection. -/
theorem contraction_abstract (U : VineTemplate) (sl : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) (Cn : Finset ℕ)
    (ν : ℕ ≃ ℕ)
    (hs1 : sl.1 ∈ U.bonds) (hs2 : sl.2 ∈ U.bonds.erase sl.1)
    (hRn : ∀ e ∈ (U.bonds.erase sl.1).erase sl.2,e.1 < U.n ∧ e.2 < U.n)
    (hRc : ∀ e ∈ (U.bonds.erase sl.1).erase sl.2,(e.1 ∈ Cn ↔ e.2 ∈ Cn))
    (hrefl : (bondSym ((U.bonds.erase sl.1).erase sl.2)).map (Sym2.map ν) =
      bondSym ((U.bonds.erase sl.1).erase sl.2))
    (hslt : sl.1.1 < U.n ∧ sl.1.2 < U.n ∧ sl.2.1 < U.n ∧ sl.2.2 < U.n)
    (hCold : ∀ v ∈ Cn,v < U.n)
    (hports : (sl.1.1 ∈ Cn ∧ sl.1.2 ∉ Cn ∧ sl.2.1 ∈ Cn ∧ sl.2.2 ∉ Cn) ∨
      (sl.1.1 ∉ Cn ∧ sl.1.2 ∈ Cn ∧ sl.2.1 ∉ Cn ∧ sl.2.2 ∈ Cn))
    (hportsw : ν (capEndpoint Cn sl.1) = capEndpoint Cn sl.2 ∧
      ν (capEndpoint Cn sl.2) = capEndpoint Cn sl.1)
    (hνout : ∀ t ∉ Cn,ν t = t) (hνmem : ∀ t,ν t ∈ Cn ↔ t ∈ Cn)
    (hGlt : ∀ g ∈ U.groups,∀ v ∈ g,v < U.n)
    (hGinv : (listGroupSet U.groups).image (Finset.image ν) = listGroupSet U.groups)
    (hνfix : ∀ t,U.n ≤ t → ν t = t)
    {β : Type} [Fintype β] [DecidableEq β]
    (ends : β → Fin (U.n+2*k+2) × Fin (U.n+2*k+2))
    (hU : (univ : Finset β).val.map (fun e => s((ends e).1.1,(ends e).2.1)) =
      bondSym (insertRungs U sl (k+1)).bonds)
    (hbal : ∀ v,(∑ e,-energySign ends v e) = 0) :
    ∃ (γ : Type) (_ : Fintype γ) (_ : DecidableEq γ) (G : RungSpliceGeometry (Fin (U.n+2*k)) γ),
      ((univ : Finset γ).val.map (fun e => s((G.ends e).1.1,(G.ends e).2.1)) =
        bondSym (insertRungs U sl k).bonds) ∧
      G.cap = capFin (U.n+2*k) Cn ∧
      (∀ u : Fin (U.n+2*k),(G.σ u).1 = u.1 ∨ (G.σ u).1 = ν u.1) ∧
      ((∀ u : Fin (U.n+2*k),(G.σ u).1 = u.1) ∨ (∀ u : Fin (U.n+2*k),(G.σ u).1 = ν u.1)) ∧
      (∀ C : Finset ℕ,(∀ t ∈ C,t < U.n) → sl.1.1 ∉ C → sl.1.2 ∉ C → sl.2.1 ∉ C → sl.2.2 ∉ C →
        G.p ∉ capFin (U.n+2*k) C ∧ G.q ∉ capFin (U.n+2*k) C ∧
          G.c ∉ capFin (U.n+2*k) C ∧ G.d ∉ capFin (U.n+2*k) C) ∧
      ∃ J : DirectedGraphIso G.newEnds ends,
        (∀ u : Fin (U.n+2*k),(u.1 < U.n → (J.atom (Sum.inl u)).1 = u.1) ∧
          (U.n ≤ u.1 → U.n ≤ (J.atom (Sum.inl u)).1)) ∧
        (∀ j,U.n ≤ (J.atom (Sum.inr j)).1) ∧
        ∃ (μ : ℕ → ℕ) (f0 f1 : ℕ),(∀ u : Fin (U.n+2*k),(J.atom (Sum.inl u)).1 = μ u.1) ∧
          (J.atom (Sum.inr 0)).1 = f0 ∧ (J.atom (Sum.inr 1)).1 = f1 ∧
          ∀ ψ : ℕ → ℕ,(ψ = id ∨ ψ = ⇑ν) →
            insert ({f0,f1} : Finset ℕ) ((listGroupSet (insertRungs U sl k).groups).image
              (Finset.image (fun t => μ (ψ t)))) = listGroupSet (insertRungs U sl (k+1)).groups := by
  classical
  have hG0 : ∀ s ∈ listGroupSet U.groups,∀ v ∈ s,v < U.n := by
    intro s hs v hv
    obtain ⟨g,hg,rfl⟩ := mem_listGroupSet.mp hs
    exact hGlt g hg v (List.mem_toFinset.mp hv)
  obtain ⟨⟨x,y⟩,⟨x',y'⟩⟩ := sl
  simp only at hs1 hs2 hRn hRc hrefl hslt hports hportsw ⊢
  have hbs := bondSym_insertRungs U x y x' y' (k+1) hs1 hs2
  have hbs' := bondSym_insertRungs U x y x' y' k hs1 hs2
  have hR : ∀ e ∈ bondSym ((U.bonds.erase (x,y)).erase (x',y')),∀ z ∈ e,z < U.n := by
    intro e he z hz
    unfold bondSym at he
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp he)
    have := hRn p hp
    rcases Sym2.mem_iff.mp hz with rfl | rfl <;> omega
  have hRcross : ∀ z ∈ bondSym ((U.bonds.erase (x,y)).erase (x',y')),∀ a b : ℕ,z = s(a,b) →
      (a ∈ Cn ↔ b ∈ Cn) := by
    intro z hz a b hzab
    unfold bondSym at hz
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hz)
    have hc := hRc p hp
    rcases Sym2.eq_iff.mp hzab with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rw [← h1,← h2]; exact hc
    · rw [← h1,← h2]; exact hc.symm
  have hU' : (univ : Finset β).val.map (fun e => s((ends e).1.1,(ends e).2.1)) =
      insSym U.n x y x' y' (k+1) (bondSym ((U.bonds.erase (x,y)).erase (x',y'))) := hU.trans hbs
  rcases hports with ⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4⟩
  · -- cap at the x-end
    have hνx : ν x = x' := by
      have := hportsw.1; simpa [capEndpoint,h1,h3] using this
    have hνx' : ν x' = x := by
      have := hportsw.2; simpa [capEndpoint,h1,h3] using this
    obtain ⟨G,hsh,hcap,hσ,hσd,hp,hq,hc,hd,J,hJ1,hJ2,hJl,hJ0,hJ1'⟩ := exists_slot_contraction_X U.n k x y x' y'
      hslt.1 hslt.2.1 hslt.2.2.1 hslt.2.2.2 _ hR Cn hCold h1 h3 h2 h4 hRcross ν hνout hνmem hνx hνx'
      hrefl ends hU' hbal
    refine ⟨_,inferInstance,inferInstance,G,hsh.trans hbs'.symm,hcap,hσ,hσd,?_,J,hJ1,hJ2,
      unskip2 U.n (U.n+(k+1)),U.n,U.n+(k+1),hJl,hJ0,hJ1',?_⟩
    swap
    · intro ψ hψ
      rw [insertRungs_groupSet,insertRungs_groupSet]
      exact group_step_eq _ _ _ ν _ _ _ (groupSet_step_X _ U.n k hG0) hGinv hνfix ψ hψ
    intro C hC hxC hyC hx'C hy'C
    refine ⟨?_,?_,?_,?_⟩
    · simp only [capFin,mem_filter,mem_univ,true_and]
      rcases hp with h | h
      · rw [h]; exact hyC
      · intro hm; have := hC _ hm; omega
    · simp only [capFin,mem_filter,mem_univ,true_and]
      rcases hq with h | h
      · rw [h]; exact hy'C
      · intro hm; have := hC _ hm; omega
    · simp only [capFin,mem_filter,mem_univ,true_and]; rw [hc]; exact hxC
    · simp only [capFin,mem_filter,mem_univ,true_and]; rw [hd]; exact hx'C
  · -- cap at the y-end
    have hνy : ν y = y' := by
      have := hportsw.1; simpa [capEndpoint,h1,h3] using this
    have hνy' : ν y' = y := by
      have := hportsw.2; simpa [capEndpoint,h1,h3] using this
    obtain ⟨G,hsh,hcap,hσ,hσd,hp,hq,hc,hd,J,hJ1,hJ2,hJl,hJ0,hJ1'⟩ := exists_slot_contraction_Y U.n k x y x' y'
      hslt.1 hslt.2.1 hslt.2.2.1 hslt.2.2.2 _ hR Cn hCold h1 h3 h2 h4 hRcross ν hνout hνmem hνy hνy'
      hrefl ends hU' hbal
    refine ⟨_,inferInstance,inferInstance,G,hsh.trans hbs'.symm,hcap,hσ,hσd,?_,J,hJ1,hJ2,
      unskip2 (U.n+k) (U.n+(2*k+1)),U.n+k,U.n+(2*k+1),hJl,hJ0,hJ1',?_⟩
    swap
    · intro ψ hψ
      rw [insertRungs_groupSet,insertRungs_groupSet]
      exact group_step_eq _ _ _ ν _ _ _ (groupSet_step_Y _ U.n k hG0) hGinv hνfix ψ hψ
    intro C hC hxC hyC hx'C hy'C
    refine ⟨?_,?_,?_,?_⟩
    · simp only [capFin,mem_filter,mem_univ,true_and]
      rcases hp with h | h
      · rw [h]; exact hxC
      · intro hm; have := hC _ hm; omega
    · simp only [capFin,mem_filter,mem_univ,true_and]
      rcases hq with h | h
      · rw [h]; exact hx'C
      · intro hm; have := hC _ hm; omega
    · simp only [capFin,mem_filter,mem_univ,true_and]; rw [hc]; exact hyC
    · simp only [capFin,mem_filter,mem_univ,true_and]; rw [hd]; exact hy'C

theorem bad_cap_eq (X : VineType) (hbd : X.IsBad = true) (hX : X ≠ .I)
    (i : Fin X.template.slots.length) : slotCap X i = {1} := by
  cases X
  · exact absurd rfl hX
  · fin_cases i; rfl
  all_goals simp [VineType.IsBad] at hbd

theorem slots_ne_I (X : VineType) (i : Fin X.template.slots.length) : X ≠ .I := by
  rintro rfl
  exact absurd i.2 (by simp [VineType.template])

/-- One slot step of the expanded-template induction, assuming the chart for the contracted graph. -/
theorem expand_step (X : VineType) (ks1 : List ℕ) (k m : ℕ)
    (hlen : ks1.length+1+m = X.template.slots.length) (joint : Fin 2)
    (IH : ∀ (V' β' : Type) [Fintype V'] [DecidableEq V'] [Fintype β'] [DecidableEq β']
      (ends' : β' → V'×V') (D' : ExpData X (ks1 ++ k :: List.replicate m 0) ends') (a' b' : V'),
      (D'.lab a').1 = 1-joint.1 → (D'.lab b').1 = joint.1 →
      ∃ P : PhysicalGraphChart ends' X a' b',
        (∀ s,P.CapSupported (capV X D'.lab s)) ∧
        (∀ s,∀ j : Fin P.full.indexing.shape.m,
          (P.full.indexing.atom (P.full.indexing.shape.xSlot j)).1 ∈ capV X D'.lab s ↔
            (P.full.indexing.atom (P.full.indexing.shape.ySlot j)).1 ∈ capV X D'.lab s) ∧
        indexingGroupSet P.full.indexing (fun v => (D'.lab v).1) =
          listGroupSet (X.expand (ks1 ++ k :: List.replicate m 0)).groups)
    {V β : Type} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β] (ends : β → V×V)
    (D : ExpData X (ks1 ++ (k+1) :: List.replicate m 0) ends) (a b : V)
    (ha : (D.lab a).1 = 1-joint.1) (hb : (D.lab b).1 = joint.1) :
    ∃ P : PhysicalGraphChart ends X a b,
      (∀ s,P.CapSupported (capV X D.lab s)) ∧
      (∀ s,∀ j : Fin P.full.indexing.shape.m,
        (P.full.indexing.atom (P.full.indexing.shape.xSlot j)).1 ∈ capV X D.lab s ↔
          (P.full.indexing.atom (P.full.indexing.shape.ySlot j)).1 ∈ capV X D.lab s) ∧
      indexingGroupSet P.full.indexing (fun v => (D.lab v).1) =
        listGroupSet (X.expand (ks1 ++ (k+1) :: List.replicate m 0)).groups := by
  classical
  have hi : ks1.length < X.template.slots.length := by omega
  let i : Fin X.template.slots.length := ⟨ks1.length,hi⟩
  have hexp := expand_decomp X ks1 (k+1) m hlen
  have hexp' := expand_decomp X ks1 k m hlen
  have hctx := slot_context X ks1 m hlen
  dsimp only at hctx
  obtain ⟨hNn,hs1,hs2,hRn,hRc⟩ := hctx
  have hrefl := slot_reflect_R X ks1 m hlen
  dsimp only at hrefl
  have hslt := template_slot_endpoints X _ (List.getElem_mem hi)
  have hslt' : (X.template.slots[ks1.length]).1.1 < (prefTemplate X ks1).n ∧
      (X.template.slots[ks1.length]).1.2 < (prefTemplate X ks1).n ∧
      (X.template.slots[ks1.length]).2.1 < (prefTemplate X ks1).n ∧
      (X.template.slots[ks1.length]).2.2 < (prefTemplate X ks1).n := by omega
  have hCold0 := slotCap_old X ⟨ks1.length,hi⟩
  have hjoint := slotReflection_joints X ⟨ks1.length,hi⟩
  have hports := slotCap_marked_ports X ⟨ks1.length,hi⟩
  have hportsw := slotReflection_ports X ⟨ks1.length,hi⟩
  have hνout := fun t (ht : t ∉ slotCap X ⟨ks1.length,hi⟩) => slotReflection_outside_all X ⟨ks1.length,hi⟩ t ht
  have hνmem := slotReflection_mem_cap X ⟨ks1.length,hi⟩
  have hnat : (X.expand (ks1 ++ (k+1) :: List.replicate m 0)).n = (prefTemplate X ks1).n+2*k+2 := by
    rw [hexp,insertRungs_atoms]; omega
  have hnat' : (X.expand (ks1 ++ k :: List.replicate m 0)).n = (prefTemplate X ks1).n+2*k := by
    rw [hexp',insertRungs_atoms]
  let ends2 : β → Fin ((prefTemplate X ks1).n+2*k+2) × Fin ((prefTemplate X ks1).n+2*k+2) :=
    fun e => (finCongr hnat (D.lab (ends e).1),finCongr hnat (D.lab (ends e).2))
  let I0 : DirectedGraphIso ends ends2 :=
    { atom := D.lab.trans (finCongr hnat), edge := Equiv.refl _, endpoints := fun x => rfl }
  have hU2 : (univ : Finset β).val.map (fun e => s((ends2 e).1.1,(ends2 e).2.1)) =
      bondSym (insertRungs (prefTemplate X ks1) (X.template.slots[ks1.length]) (k+1)).bonds :=
    D.shadow.trans (congrArg bondSym (congrArg VineTemplate.bonds hexp))
  have hbal2 : ∀ v,(∑ e,-energySign ends2 v e) = 0 := by
    intro v
    obtain ⟨u,rfl⟩ := I0.atom.surjective v
    exact (I0.degree_eq u).trans (D.balanced u)
  have hpg := prefTemplate_groups X ks1
  have hνfix : ∀ t,(prefTemplate X ks1).n ≤ t → slotReflection X ⟨ks1.length,hi⟩ t = t := by
    intro t ht
    apply hνout
    intro hm
    have := hCold0 t hm
    omega
  have hGinv : (listGroupSet (prefTemplate X ks1).groups).image
      (Finset.image (slotReflection X ⟨ks1.length,hi⟩)) = listGroupSet (prefTemplate X ks1).groups := by
    conv_rhs => rw [← Finset.image_id (s := listGroupSet (prefTemplate X ks1).groups)]
    apply Finset.image_congr
    intro t ht
    obtain ⟨g,hg,rfl⟩ := mem_listGroupSet.mp ht
    simpa using reflection_image_group X ⟨ks1.length,hi⟩ g (hpg.1.1 g hg)
  obtain ⟨γ,_,_,G,hsh,hGcap,hGσ,hGσd,hGpqcd,J,hJ1,hJ2,μ,f0,f1,hJl,hJ0,hJ1',hgrp⟩ :=
    contraction_abstract (prefTemplate X ks1)
    (X.template.slots[ks1.length]) k (slotCap X ⟨ks1.length,hi⟩) (slotReflection X ⟨ks1.length,hi⟩)
    hs1 hs2 hRn hRc hrefl hslt' (fun v hv => by have := hCold0 v hv; omega) hports hportsw hνout hνmem
    hpg.1.2 hGinv hνfix ends2 hU2 hbal2
  have h2n : 2 ≤ X.template.n := by cases X <;> decide
  let D' : ExpData X (ks1 ++ k :: List.replicate m 0) G.ends :=
    { lab := finCongr hnat'.symm
      shadow := hsh.trans (congrArg bondSym (congrArg VineTemplate.bonds hexp')).symm
      balanced := G.balanced }
  have hjb : joint.1 < 2 := joint.2
  have hal : (D.lab a).1 < (prefTemplate X ks1).n+2*k := by omega
  have hbl : (D.lab b).1 < (prefTemplate X ks1).n+2*k := by omega
  let a'' : Fin ((prefTemplate X ks1).n+2*k) := ⟨(D.lab a).1,hal⟩
  let b'' : Fin ((prefTemplate X ks1).n+2*k) := ⟨(D.lab b).1,hbl⟩
  obtain ⟨P',hP',hpu',hgr'⟩ := IH (Fin ((prefTemplate X ks1).n+2*k)) γ G.ends D' a'' b'' ha hb
  have hcapV : ∀ s,capV X D'.lab s = capFin ((prefTemplate X ks1).n+2*k) (slotCap X s) :=
    fun s => rfl
  have hX : X ≠ .I := slots_ne_I X i
  have hjt : ∀ t : ℕ,t < 2 → slotReflection X ⟨ks1.length,hi⟩ t = t := by
    intro t ht
    interval_cases t
    · exact hjoint.1
    · exact hjoint.2
  have hσfix : ∀ u : Fin ((prefTemplate X ks1).n+2*k),u.1 < 2 → G.σ u = u := by
    intro u hu
    apply Fin.ext
    rcases hGσ u with h | h
    · exact h
    · rw [h]; exact hjt _ hu
  have hσa : G.σ a'' = a'' := hσfix a'' (by simp only [a'']; omega)
  have hσb : G.σ b'' = b'' := hσfix b'' (by simp only [b'']; omega)
  have hGcap' : G.cap = capFin ((prefTemplate X ks1).n+2*k) (slotCap X i) := hGcap
  have hcapP : P'.CapSupported G.cap := by
    rw [hGcap']; exact hP' i
  have hpairs : ∀ j : Fin P'.full.indexing.shape.m,
      (P'.full.indexing.atom (P'.full.indexing.shape.xSlot j)).1 ∈ G.cap ↔
        (P'.full.indexing.atom (P'.full.indexing.shape.ySlot j)).1 ∈ G.cap := by
    rw [hGcap']; exact hpu' i
  have hbad : X.IsBad = true → G.gapSign a'' b'' ≠ 0 := by
    intro hbd
    have hc1 := bad_cap_eq X hbd hX i
    simp only [RungSpliceGeometry.gapSign,hGcap',capFin,hc1,mem_filter,mem_univ,true_and,
      Finset.mem_singleton,a'',b'']
    rw [ha,hb]
    rcases joint with ⟨_ | _ | _,hj⟩ <;> simp at hj ⊢
  let Pnew := G.insertedPhysicalChart P' hX hσa hσb hcapP hpairs hbad
  have hσs : ∀ s : Fin X.template.slots.length,∀ v : Fin ((prefTemplate X ks1).n+2*k),
      G.σ v ∈ capFin ((prefTemplate X ks1).n+2*k) (slotCap X s) ↔
        v ∈ capFin ((prefTemplate X ks1).n+2*k) (slotCap X s) := by
    intro s v
    simp only [capFin,mem_filter,mem_univ,true_and]
    rcases hGσ v with h | h
    · rw [h]
    · rw [h]
      by_cases hs : s = i
      · subst hs
        exact hνmem _
      · have hdis := slotCaps_disjoint X s i hs
        constructor
        · intro hm
          have h1 : slotReflection X ⟨ks1.length,hi⟩ v.1 ∉ slotCap X i :=
            fun hh => Finset.disjoint_left.mp hdis hm hh
          have h2 : v.1 ∉ slotCap X i := fun hh => h1 ((hνmem v.1).mpr hh)
          rwa [hνout v.1 h2] at hm
        · intro hv
          have h2 : v.1 ∉ slotCap X i := fun hh => Finset.disjoint_left.mp hdis hv hh
          rwa [hνout v.1 h2]
  have hColdN : ∀ (s : Fin X.template.slots.length),∀ t ∈ slotCap X s,t < (prefTemplate X ks1).n :=
    fun s t ht => by have := slotCap_old X s t ht; omega
  have hsupp : ∀ s : Fin X.template.slots.length,
      Pnew.CapSupported (liftedCap (capFin ((prefTemplate X ks1).n+2*k) (slotCap X s))) := by
    intro s
    by_cases hs : s = i
    · subst hs
      have := G.insertedPhysicalChart_selected_support P' hX hσa hσb hcapP hpairs hbad
      rw [hGcap'] at this
      exact this
    · have hout := other_slot_outside_cap X s i hs
      have hpq := hGpqcd (slotCap X s) (hColdN s) hout.1 hout.2.1 hout.2.2.1 hout.2.2.2
      exact G.insertedPhysicalChart_other_support P' hX hσa hσb hcapP hpairs hbad _ (hP' s)
        hpq.1 hpq.2.1 hpq.2.2.1 hpq.2.2.2 (hσs s)
  have hpair : ∀ (s : Fin X.template.slots.length) (j : Fin Pnew.full.indexing.shape.m),
      (Pnew.full.indexing.atom (Pnew.full.indexing.shape.xSlot j)).1 ∈
        liftedCap (capFin ((prefTemplate X ks1).n+2*k) (slotCap X s)) ↔
      (Pnew.full.indexing.atom (Pnew.full.indexing.shape.ySlot j)).1 ∈
        liftedCap (capFin ((prefTemplate X ks1).n+2*k) (slotCap X s)) := by
    intro s j
    exact G.insertedIndexing_pair_uniform P'.full.indexing hX hσa hσb _ (hσs s) (hpu' s) j
  let Jt : DirectedGraphIso G.newEnds ends := J.trans I0.symm
  have hlabJ : ∀ w,(D.lab (Jt.atom w)).1 = (J.atom w).1 := by
    intro w
    change (D.lab (D.lab.symm ((finCongr hnat).symm (J.atom w)))).1 = _
    simp
  have hJa : Jt.atom (Sum.inl a'') = a := by
    apply D.lab.injective
    apply Fin.ext
    rw [hlabJ]
    exact (hJ1 a'').1 (by simp only [a'']; omega)
  have hJb : Jt.atom (Sum.inl b'') = b := by
    apply D.lab.injective
    apply Fin.ext
    rw [hlabJ]
    exact (hJ1 b'').1 (by simp only [b'']; omega)
  have hC : ∀ (s : Fin X.template.slots.length) (w : Fin ((prefTemplate X ks1).n+2*k) ⊕ Fin 2),
      Jt.atom w ∈ capV X D.lab s ↔
        w ∈ liftedCap (capFin ((prefTemplate X ks1).n+2*k) (slotCap X s)) := by
    intro s w
    simp only [capV,mem_filter,mem_univ,true_and,hlabJ]
    rcases w with u | j
    · simp only [liftedCap,capFin,mem_image,mem_filter,mem_univ,true_and,Sum.inl.injEq,
        exists_eq_right]
      by_cases hu : u.1 < (prefTemplate X ks1).n
      · rw [(hJ1 u).1 hu]
      · have h1 := (hJ1 u).2 (by omega)
        constructor
        · intro hm; have := hColdN s _ hm; omega
        · intro hm; have := hColdN s _ hm; omega
    · constructor
      · intro hm; have := hColdN s _ hm; have := hJ2 j; omega
      · intro hm; simp [liftedCap] at hm
  obtain ⟨P2,hP2,hpu2,hgr2⟩ := chart_transport Jt X (Sum.inl a'') (Sum.inl b'') a b hJa hJb
    (fun s => liftedCap (capFin ((prefTemplate X ks1).n+2*k) (slotCap X s)))
    (fun s => capV X D.lab s) (fun s w => (hC s w).symm.symm) Pnew hsupp hpair
  refine ⟨P2,hP2,hpu2,?_⟩
  rw [hgr2 (fun v => (D.lab v).1)]
  have hℓ : (fun w => (D.lab (Jt.atom w)).1) = fun w => (J.atom w).1 := funext hlabJ
  simp only [hℓ]
  rw [← hexp] at hgrp
  obtain ⟨ψ,hψ,hψσ⟩ : ∃ ψ : ℕ → ℕ,(ψ = id ∨ ψ = ⇑(slotReflection X ⟨ks1.length,hi⟩)) ∧
      ∀ u : Fin ((prefTemplate X ks1).n+2*k),(G.σ u).1 = ψ u.1 := by
    rcases hGσd with h | h
    · exact ⟨id,Or.inl rfl,h⟩
    · exact ⟨_,Or.inr rfl,h⟩
  have hgr'' : shapeGroupSet P'.full.indexing.shape (fun i => (P'.full.indexing.atom i).1.1) =
      listGroupSet (insertRungs (prefTemplate X ks1) (X.template.slots[ks1.length]) k).groups := by
    have h2 : listGroupSet (X.expand (ks1 ++ k :: List.replicate m 0)).groups =
        listGroupSet (insertRungs (prefTemplate X ks1) (X.template.slots[ks1.length]) k).groups := by
      rw [hexp']
    exact hgr'.trans h2
  change indexingGroupSet (G.insertedIndexing P'.full.indexing hX hσa hσb) (fun w => (J.atom w).1) = _
  rw [G.insertedIndexing_groupSet P'.full.indexing hX hσa hσb]
  have hfun : (fun i => (J.atom (Sum.inl (G.σ (P'.full.indexing.atom i).1))).1) =
      fun i => (fun t => μ (ψ t)) ((P'.full.indexing.atom i).1.1) := by
    funext i
    rw [hJl, hψσ]
  have hmap := shapeGroupSet_map P'.full.indexing.shape (fun i => (P'.full.indexing.atom i).1.1)
    (fun t => μ (ψ t))
  rw [hfun]
  erw [hmap]
  rw [hgr'', hJ0, hJ1']
  exact hgrp ψ hψ

theorem exists_last_nonzero : ∀ (ks : List ℕ),ks.sum ≠ 0 →
    ∃ (ks1 : List ℕ) (k m : ℕ),ks = ks1 ++ (k+1) :: List.replicate m 0 := by
  intro ks
  induction ks with
  | nil => intro h; exact absurd rfl h
  | cons a ks ih =>
    intro h
    by_cases hs : ks.sum = 0
    · have hz : ks = List.replicate ks.length 0 := by
        rw [List.eq_replicate_iff]
        refine ⟨rfl,?_⟩
        intro x hx
        exact (List.sum_eq_zero_iff.mp hs) x hx
      obtain ⟨a',rfl⟩ : ∃ a',a = a'+1 := ⟨a-1,by simp at h; omega⟩
      exact ⟨[],a',ks.length,by simp only [List.nil_append]; rw [← hz]⟩
    · obtain ⟨ks1,k,m,e⟩ := ih hs
      exact ⟨a :: ks1,k,m,by rw [e]; rfl⟩

/-- The expanded-template induction, conditional on the base-template statement. -/
theorem exists_physical_expanded (X : VineType) (hB : BaseChartStatement X) :
    ∀ (n : ℕ) (ks : List ℕ),ks.sum = n → ks.length = X.template.slots.length →
    ∀ (V β : Type) [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]
      (ends : β → V×V) (D : ExpData X ks ends) (a b : V) (joint : Fin 2),
      (D.lab a).1 = 1-joint.1 → (D.lab b).1 = joint.1 →
      ∃ P : PhysicalGraphChart ends X a b,
        (∀ s,P.CapSupported (capV X D.lab s)) ∧
        (∀ s,∀ j : Fin P.full.indexing.shape.m,
          (P.full.indexing.atom (P.full.indexing.shape.xSlot j)).1 ∈ capV X D.lab s ↔
            (P.full.indexing.atom (P.full.indexing.shape.ySlot j)).1 ∈ capV X D.lab s) ∧
        indexingGroupSet P.full.indexing (fun v => (D.lab v).1) = listGroupSet (X.expand ks).groups := by
  intro n
  induction n with
  | zero =>
    intro ks hsum hlen V β _ _ _ _ ends D a b joint ha hb
    have hz : ks = List.replicate X.template.slots.length 0 := by
      rw [List.eq_replicate_iff]
      refine ⟨hlen,?_⟩
      intro x hx
      exact (List.sum_eq_zero_iff.mp hsum) x hx
    have hT : X.expand ks = X.template := by rw [hz]; exact expand_zero_rungs X
    exact expData_base X hB ks hT ends D a b joint ha hb
  | succ n ih =>
    intro ks hsum hlen V β _ _ _ _ ends D a b joint ha hb
    obtain ⟨ks1,k,m,hks⟩ := exists_last_nonzero ks (by omega)
    subst hks
    have hlen' : ks1.length+1+m = X.template.slots.length := by
      simp at hlen; omega
    have hsum' : (ks1 ++ k :: List.replicate m 0).sum = n := by
      simp at hsum ⊢; omega
    have hlen'' : (ks1 ++ k :: List.replicate m 0).length = X.template.slots.length := by
      simp; omega
    exact expand_step X ks1 k m hlen' joint
      (fun V' β' [Fintype V'] [DecidableEq V'] [Fintype β'] [DecidableEq β'] ends' D' a' b' ha' hb' =>
        ih _ hsum' hlen'' V' β' ends' D' a' b' joint ha' hb') ends D a b ha hb

end WaveTurbulence.Vine.Param
