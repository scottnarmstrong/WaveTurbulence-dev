/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedBaseSource
public import WaveTurbulenceVineParam.VineParamBaseOutgoing
public import WaveTurbulenceVineParam.VineParamExpandDecomp
public import WaveTurbulenceVineParam.VineParamPhysicalIsoSupport
public import WaveTurbulenceVineParam.VineParamGraphMatch
public import WaveTurbulenceVineParam.VineParamDirectedIsoDegrees
public import WaveTurbulenceVineParam.VineParamRealizedModel
public import WaveTurbulenceVineParam.VineParamGroupInsert
import Mathlib.Tactic

/-! # Expanded-shape graph data, degree equations and the base case -/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- A directed graph labeled by the atoms of the expansion `X.expand ks`, with the exact
unordered bond multiset of the expansion and balanced directed degrees. -/
structure ExpData (X : VineType) (ks : List ℕ) {V β : Type} [Fintype V] [DecidableEq V]
    [Fintype β] (ends : β → V×V) where
  lab : V ≃ Fin (X.expand ks).n
  shadow : (univ : Finset β).val.map (fun e => s((lab (ends e).1).1,(lab (ends e).2).1)) =
    bondSym (X.expand ks).bonds
  balanced : ∀ v,(∑ e,-energySign ends v e) = 0

/-- The cap of a slot, as a set of atoms of the labeled graph. -/
@[expose] def capV {V : Type} [Fintype V] [DecidableEq V] (X : VineType) {n : ℕ} (lab : V ≃ Fin n)
    (s : Fin X.template.slots.length) : Finset V :=
  univ.filter (fun v => (lab v).1 ∈ slotCap X s)

theorem list_sum_ite_eq_count (l : List ℕ) (v : ℕ) :
    (l.map (fun a => if a = v then 1 else 0)).sum = l.count v := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons,List.count_cons,ih]
    by_cases h : a = v <;> simp [h]; omega

theorem two_out_eq_degree {n : ℕ} {β : Type} [Fintype β] [DecidableEq β] (T : VineTemplate)
    (ends : β → Fin n × Fin n)
    (hU : (univ : Finset β).val.map (fun e => s((ends e).1.1,(ends e).2.1)) = bondSym T.bonds)
    (hbal : ∀ v,(∑ e,-energySign ends v e) = 0) (v : Fin n) :
    2 * ((univ : Finset β).filter (fun e => (ends e).1 = v)).card = templateDegree T v.1 := by
  classical
  let degS : Sym2 ℕ → ℕ := Sym2.lift ⟨fun a b => (if a = v.1 then 1 else 0) + (if b = v.1 then 1 else 0),
    fun a b => by ring⟩
  have h1 : (univ : Finset β).val.map (fun e => degS s((ends e).1.1,(ends e).2.1)) =
      (univ : Finset β).val.map (fun e => (if (ends e).1.1 = v.1 then 1 else 0) +
        (if (ends e).2.1 = v.1 then 1 else 0)) := by
    apply Multiset.map_congr rfl; intro e _; rfl
  have h2 : ((univ : Finset β).val.map (fun e => degS s((ends e).1.1,(ends e).2.1))).sum =
      (templateDegree T v.1) := by
    have : (univ : Finset β).val.map (fun e => degS s((ends e).1.1,(ends e).2.1)) =
        ((univ : Finset β).val.map (fun e => s((ends e).1.1,(ends e).2.1))).map degS := by
      rw [Multiset.map_map]; rfl
    rw [this,hU]
    unfold bondSym templateDegree
    rw [Multiset.map_coe,List.map_map,Multiset.sum_coe]
    have : ((fun p : ℕ×ℕ => degS s(p.1,p.2))) = fun p => (if p.1 = v.1 then 1 else 0) +
        (if p.2 = v.1 then 1 else 0) := by funext p; rfl
    rw [Function.comp_def,this]
    rw [List.sum_map_add]
    simp only [← list_sum_ite_eq_count]
    rw [List.map_map,List.map_map]
    rfl
  have h3 : ((univ : Finset β).val.map (fun e => (if (ends e).1.1 = v.1 then 1 else 0) +
        (if (ends e).2.1 = v.1 then 1 else 0))).sum =
      ((univ : Finset β).filter (fun e => (ends e).1 = v)).card +
        ((univ : Finset β).filter (fun e => (ends e).2 = v)).card := by
    have hf : ∀ e : β, ((if (ends e).1.1 = v.1 then 1 else 0) + (if (ends e).2.1 = v.1 then 1 else 0) : ℕ) =
        ((if (ends e).1 = v then 1 else 0) + (if (ends e).2 = v then 1 else 0)) := by
      intro e; simp only [Fin.val_inj]
    calc _ = ∑ e, ((if (ends e).1.1 = v.1 then 1 else 0) + (if (ends e).2.1 = v.1 then 1 else 0) : ℕ) := rfl
      _ = ∑ e, ((if (ends e).1 = v then 1 else 0) + (if (ends e).2 = v then 1 else 0) : ℕ) :=
          Finset.sum_congr rfl (fun e _ => hf e)
      _ = _ := by
        rw [Finset.sum_add_distrib,Finset.sum_boole,Finset.sum_boole]
        simp
  have h4 : (((univ : Finset β).filter (fun e => (ends e).1 = v)).card : ℤ) =
      ((univ : Finset β).filter (fun e => (ends e).2 = v)).card := by
    have := hbal v
    simp only [energySign,neg_sub] at this
    rw [Finset.sum_sub_distrib,Finset.sum_boole,Finset.sum_boole] at this
    linarith
  rw [h1] at h2
  rw [h3] at h2
  have h5 : ((univ : Finset β).filter (fun e => (ends e).1 = v)).card =
      ((univ : Finset β).filter (fun e => (ends e).2 = v)).card := by exact_mod_cast h4
  omega

/-- Transport of a physical chart and its cap supports along a directed graph isomorphism. -/
theorem chart_transport {V W β δ ι : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype β] [Fintype δ] {ends : β → V×V} {other : δ → W×W} (I : DirectedGraphIso ends other)
    (X : VineType) (a b : V) (a' b' : W) (ha : I.atom a = a') (hb : I.atom b = b')
    (Cs : ι → Finset V) (Cs' : ι → Finset W) (hC : ∀ s v,I.atom v ∈ Cs' s ↔ v ∈ Cs s)
    (P : PhysicalGraphChart ends X a b) (hP : ∀ s,P.CapSupported (Cs s))
    (hpu : ∀ s,∀ j : Fin P.full.indexing.shape.m,
      (P.full.indexing.atom (P.full.indexing.shape.xSlot j)).1 ∈ Cs s ↔
        (P.full.indexing.atom (P.full.indexing.shape.ySlot j)).1 ∈ Cs s) :
    ∃ P' : PhysicalGraphChart other X a' b',(∀ s,P'.CapSupported (Cs' s)) ∧
      (∀ s,∀ j : Fin P'.full.indexing.shape.m,
        (P'.full.indexing.atom (P'.full.indexing.shape.xSlot j)).1 ∈ Cs' s ↔
          (P'.full.indexing.atom (P'.full.indexing.shape.ySlot j)).1 ∈ Cs' s) ∧
      (∀ ℓ : W → ℕ,indexingGroupSet P'.full.indexing ℓ =
        indexingGroupSet P.full.indexing (fun v => ℓ (I.atom v))) := by
  subst ha hb
  exact ⟨I.physicalChart P,fun s => I.physicalChart_capSupported P _ _ (hC s) (hP s),
    fun s => I.physicalChart_pair_uniform P _ _ (hC s) (hpu s),
    fun ℓ => I.physicalChart_groupSet P ℓ⟩

/-- The statement proved for the base templates by `exists_physical_base_chart`. -/
@[expose] def BaseChartStatement (X : VineType) : Prop :=
  ∀ {m : ℕ} (A : Fin m → Fin X.template.n × Fin X.template.n),
    ((List.ofFn (fun e => ((A e).1.1,(A e).2.1)) : List (ℕ×ℕ)) : Multiset (ℕ×ℕ)).map
        (fun e => s(e.1,e.2)) =
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)) →
    (∀ v : Fin X.template.n,
      outgoingCount (List.ofFn (fun e => ((A e).1.1,(A e).2.1))) v.1 = if v.1<2 then 1 else 2) →
    ∀ (joint : Fin 2) (a b : Fin X.template.n),a.1 = 1-joint.1 → b.1 = joint.1 →
    ∃ P : PhysicalGraphChart A X a b,
      (∀ s : Fin X.template.slots.length,P.CapSupported (baseSourceCap X s)) ∧
      (∀ s : Fin X.template.slots.length,∀ j : Fin P.full.indexing.shape.m,
        (P.full.indexing.atom (P.full.indexing.shape.xSlot j)).1 ∈ baseSourceCap X s ↔
          (P.full.indexing.atom (P.full.indexing.shape.ySlot j)).1 ∈ baseSourceCap X s) ∧
      indexingGroupSet P.full.indexing (fun v => v.1) = listGroupSet X.template.groups

theorem expData_base (X : VineType) (hB : BaseChartStatement X) (ks : List ℕ)
    (hT : X.expand ks = X.template) {V β : Type} [Fintype V] [DecidableEq V] [Fintype β]
    [DecidableEq β] (ends : β → V×V) (D : ExpData X ks ends) (a b : V) (joint : Fin 2)
    (ha : (D.lab a).1 = 1-joint.1) (hb : (D.lab b).1 = joint.1) :
    ∃ P : PhysicalGraphChart ends X a b,
      (∀ s,P.CapSupported (capV X D.lab s)) ∧
      (∀ s,∀ j : Fin P.full.indexing.shape.m,
        (P.full.indexing.atom (P.full.indexing.shape.xSlot j)).1 ∈ capV X D.lab s ↔
          (P.full.indexing.atom (P.full.indexing.shape.ySlot j)).1 ∈ capV X D.lab s) ∧
      indexingGroupSet P.full.indexing (fun v => (D.lab v).1) = listGroupSet (X.expand ks).groups := by
  classical
  have hn : (X.expand ks).n = X.template.n := congrArg VineTemplate.n hT
  let lab0 : V ≃ Fin X.template.n := D.lab.trans (finCongr hn)
  let e : β ≃ Fin (Fintype.card β) := Fintype.equivFin β
  let ends0 : β → Fin X.template.n × Fin X.template.n := fun x => (lab0 (ends x).1,lab0 (ends x).2)
  let I0 : DirectedGraphIso ends ends0 :=
    { atom := lab0, edge := Equiv.refl _, endpoints := fun x => rfl }
  let A : Fin (Fintype.card β) → Fin X.template.n × Fin X.template.n := fun i => ends0 (e.symm i)
  let I : DirectedGraphIso ends A :=
    { atom := lab0, edge := e, endpoints := fun x => by simp [A,ends0] }
  have hshadow : (univ : Finset β).val.map (fun x => s((ends0 x).1.1,(ends0 x).2.1)) =
      bondSym X.template.bonds := by
    exact D.shadow.trans (congrArg bondSym (congrArg VineTemplate.bonds hT))
  have hbal0 : ∀ v,(∑ x,-energySign ends0 v x) = 0 := by
    intro v
    obtain ⟨u,rfl⟩ := lab0.surjective v
    exact (I0.degree_eq u).trans (D.balanced u)
  have hAeq : (univ : Finset (Fin (Fintype.card β))).val.map
      (fun i => s((A i).1.1,(A i).2.1)) = bondSym X.template.bonds := by
    rw [← hshadow]
    have h := Multiset.map_univ_val_equiv e.symm
    calc _ = ((univ : Finset (Fin (Fintype.card β))).val.map e.symm).map
          (fun x => s((ends0 x).1.1,(ends0 x).2.1)) := by rw [Multiset.map_map]; rfl
      _ = _ := by rw [h]
  have hU : ((List.ofFn (fun i => ((A i).1.1,(A i).2.1)) : List (ℕ×ℕ)) : Multiset (ℕ×ℕ)).map
        (fun e => s(e.1,e.2)) = (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)) := by
    rw [Multiset.map_coe,List.map_ofFn]
    have : ((List.ofFn ((fun e : ℕ×ℕ => s(e.1,e.2)) ∘ fun i => ((A i).1.1,(A i).2.1))) :
        Multiset (Sym2 ℕ)) = (univ : Finset (Fin (Fintype.card β))).val.map
        (fun i => s((A i).1.1,(A i).2.1)) := by
      rw [Fin.univ_val_map]; rfl
    rw [this,hAeq]; rfl
  have hdeg : ∀ v : Fin X.template.n,
      outgoingCount (List.ofFn (fun i => ((A i).1.1,(A i).2.1))) v.1 = if v.1<2 then 1 else 2 := by
    intro v
    rw [outgoingCount_ofFn]
    have h2 := two_out_eq_degree X.template ends0 hshadow hbal0 v
    rw [template_degrees X v.1 v.2] at h2
    have hc : ((univ : Finset (Fin (Fintype.card β))).filter fun j => (A j).1.1 = v.1).card =
        ((univ : Finset β).filter (fun x => (ends0 x).1 = v)).card := by
      rw [Finset.card_filter,Finset.card_filter]
      rw [← Equiv.sum_comp e.symm]
      apply Finset.sum_congr rfl
      intro x _
      simp [A,Fin.val_inj]
    rw [hc]
    split_ifs at h2 ⊢ <;> omega
  have hv : ∀ s v,I.atom v ∈ baseSourceCap X s ↔ v ∈ capV X D.lab s := by
    intro s v
    simp [baseSourceCap,capV,I,lab0]
  have ha0 : (lab0 a).1 = 1-joint.1 := ha
  have hb0 : (lab0 b).1 = joint.1 := hb
  obtain ⟨P,hP,hpu,hgr⟩ := hB A hU hdeg joint (lab0 a) (lab0 b) ha0 hb0
  have hsymm : ∀ s v,I.symm.atom v ∈ capV X D.lab s ↔ v ∈ baseSourceCap X s := by
    intro s v
    simp [baseSourceCap,capV,DirectedGraphIso.symm,I,lab0]
  obtain ⟨P',hP',hpu',hgr'⟩ := chart_transport I.symm X (lab0 a) (lab0 b) a b
    (by simp [DirectedGraphIso.symm,I]) (by simp [DirectedGraphIso.symm,I]) (baseSourceCap X)
    (capV X D.lab) hsymm P hP hpu
  refine ⟨P',hP',hpu',?_⟩
  rw [hgr' (fun v => (D.lab v).1)]
  have hf : (fun v : Fin X.template.n => (D.lab (I.symm.atom v)).1) = fun v => v.1 := by
    funext v
    simp [DirectedGraphIso.symm,I,lab0]
  simp only [hf]
  rw [hgr, hT]

end WaveTurbulence.Vine.Param
