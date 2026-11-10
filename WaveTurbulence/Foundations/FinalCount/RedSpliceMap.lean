/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLCN
public import WaveTurbulence.Foundations.FinalCount.RedSpliceStep
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): old-name maps of iterated splicing, and transport of disjoint CL blocks

`SpMap G G' cls` records that `G'` is obtained from `G` by splicing a family of disjoint (CL) blocks,
where `cls v = some a` says that `v` lies in a spliced block with crown `a` (`cls v = none`: `v` is not
merged).  The maps `ob` (branches) and `od` (darts) send the new names to the old names.  The block
transport lemma `isBlock_pb` shows that a (CL) block of `G` avoiding all spliced blocks pulls back to a
(CL) block of `G'`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole

variable {w : ℕ}

/-- The crown map of a merge labelling. -/
@[expose] def repC {G : Garden w} (cls : GBranch G.tree → Option (GBranch G.tree)) (v : GBranch G.tree) :
    GBranch G.tree := (cls v).getD v

/-- A merge labelling is well formed: the crown of a merged atom is a fixed point. -/
@[expose] def ClsOK {G : Garden w} (cls : GBranch G.tree → Option (GBranch G.tree)) : Prop :=
  ∀ v a, cls v = some a → cls a = some a

/-- `G'` is obtained from `G` by splicing disjoint (CL) blocks labelled by `cls`. -/
structure SpMap (G G' : Garden w) (cls : GBranch G.tree → Option (GBranch G.tree)) where
  ob : GBranch G'.tree → GBranch G.tree
  od : GardenDart G' → GardenDart G
  ob_inj : Function.Injective ob
  od_inj : Function.Injective od
  ob_range : ∀ v, (∃ c, ob c = v) ↔ (cls v = none ∨ cls v = some v)
  od_range : ∀ x, (∃ y, od y = x) ↔
    ¬ ∃ a, cls (G.molecule.atom x) = some a ∧ cls (G.molecule.atom (G.molecule.mate x)) = some a
  od_mate : ∀ y, od (G'.molecule.mate y) = G.molecule.mate (od y)
  od_out : ∀ y, G.molecule.out (od y) = G'.molecule.out y
  ob_atom : ∀ y, ob (G'.molecule.atom y) = repC cls (G.molecule.atom (od y))
  ob_root : ∀ c, (ob c).1.2 = [] ↔ c.1.2 = []
  ob_parent : ∀ c (hn : c.1.2 ≠ []) (ho : (ob c).1.2 ≠ []),
    ob (GNode.parent c.toNode hn) = repC cls (GNode.parent (ob c).toNode ho)

namespace SpMap
variable {G G' : Garden w} {cls : GBranch G.tree → Option (GBranch G.tree)}

/-- The trivial splice (nothing merged). -/
@[expose] def refl (G : Garden w) : SpMap G G (fun _ => none) where
  ob := id
  od := id
  ob_inj := Function.injective_id
  od_inj := Function.injective_id
  ob_range := fun v => by simp
  od_range := fun x => by simp
  od_mate := fun _ => rfl
  od_out := fun _ => rfl
  ob_atom := fun _ => rfl
  ob_root := fun _ => Iff.rfl
  ob_parent := fun _ _ _ => rfl

/-- The preimage of an atom set of `G` in `G'`. -/
@[expose] noncomputable def pb (M : SpMap G G' cls) (U : Finset (GBranch G.tree)) : Finset (GBranch G'.tree) := by
  classical exact Finset.univ.filter (fun c => M.ob c ∈ U)

theorem mem_pb (M : SpMap G G' cls) {U : Finset (GBranch G.tree)} {c : GBranch G'.tree} :
    c ∈ M.pb U ↔ M.ob c ∈ U := by
  classical simp [pb]

variable (M : SpMap G G' cls) (hcls : ClsOK cls) {U : Finset (GBranch G.tree)}
  (hU : ∀ v ∈ U, cls v = none)

include hcls hU in
theorem repC_mem_iff {v : GBranch G.tree} : repC cls v ∈ U ↔ v ∈ U := by
  unfold repC
  cases hv : cls v with
  | none => simp
  | some a =>
    have h1 : v ∉ U := fun h => by have := hU v h; simp_all
    have h2 : a ∉ U := fun h => by have := hU a h; rw [hcls v a hv] at this; simp at this
    simp [h1, h2]

include hcls hU in
theorem repC_eq_of_mem {v w' : GBranch G.tree} (hv : v ∈ U) : repC cls w' = v ↔ w' = v := by
  constructor
  · intro h
    have : repC cls w' ∈ U := h ▸ hv
    rw [repC_mem_iff hcls hU] at this
    have h2 := hU _ this
    unfold repC at h; rw [h2] at h; simpa using h
  · rintro rfl
    unfold repC; rw [hU _ hv]; rfl

include hcls hU in
theorem inGroup_pb (y : GardenDart G') :
    G'.molecule.InGroup (M.pb U) y ↔ G.molecule.InGroup U (M.od y) := by
  unfold Molecule.InGroup
  rw [mem_pb, mem_pb, M.ob_atom, ← M.od_mate, repC_mem_iff hcls hU, M.ob_atom, repC_mem_iff hcls hU]

include hcls hU in
theorem card_filter_pb (P : Bool → Prop) [DecidablePred P] {c : GBranch G'.tree} (hc : M.ob c ∈ U) :
    ((G'.molecule.dartsAt c).filter (fun y => G'.molecule.InGroup (M.pb U) y ∧ P (G'.molecule.out y))).card =
      ((G.molecule.dartsAt (M.ob c)).filter (fun x => G.molecule.InGroup U x ∧ P (G.molecule.out x))).card := by
  apply Finset.card_bij (fun y _ => M.od y)
  · intro y hy
    simp only [Finset.mem_filter, Molecule.dartsAt, Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨h1, h2, h3⟩ := hy
    refine ⟨?_, (inGroup_pb M hcls hU y).mp h2, by rw [M.od_out]; exact h3⟩
    have := M.ob_atom y
    rw [h1] at this
    exact ((repC_eq_of_mem hcls hU hc).mp this.symm)
  · intro x y _ _ h
    exact M.od_inj h
  · intro x hx
    simp only [Finset.mem_filter, Molecule.dartsAt, Finset.mem_univ, true_and] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    have hc0 : cls (G.molecule.atom x) = none := hU _ (h1 ▸ hc)
    obtain ⟨y, hy⟩ := (M.od_range x).mpr (by
      rintro ⟨a, ha, -⟩; rw [hc0] at ha; simp at ha)
    refine ⟨y, ?_, hy⟩
    simp only [Finset.mem_filter, Molecule.dartsAt, Finset.mem_univ, true_and]
    have hatom : G'.molecule.atom y = c := by
      apply M.ob_inj
      rw [M.ob_atom, hy, h1]
      unfold repC; rw [← h1, hc0]; rfl
    refine ⟨hatom, (inGroup_pb M hcls hU y).mpr (hy ▸ h2), ?_⟩
    rw [← M.od_out, hy]; exact h3

include hcls hU in
theorem eqvGen_pb {R : GBranch G.tree → GBranch G.tree → Prop} (hR : R = fun u v =>
      ∃ x, G.molecule.InGroup U x ∧ G.molecule.atom x = u ∧ G.molecule.atom (G.molecule.mate x) = v)
    {u v : GBranch G.tree} (h : Relation.EqvGen R u v) :
    (u ∈ U ↔ v ∈ U) ∧ (u ∈ U → ∀ c d : GBranch G'.tree, M.ob c = u → M.ob d = v →
      Relation.EqvGen (fun a b => ∃ y, G'.molecule.InGroup (M.pb U) y ∧ G'.molecule.atom y = a ∧
        G'.molecule.atom (G'.molecule.mate y) = b) c d) := by
  subst hR
  induction h with
  | rel a b hab =>
    obtain ⟨x, hx, hxa, hxb⟩ := hab
    refine ⟨⟨fun _ => hxb ▸ hx.2, fun _ => hxa ▸ hx.1⟩, fun _ c d hc hd => ?_⟩
    have hcls0 : cls (G.molecule.atom x) = none := hU _ hx.1
    obtain ⟨y, hy⟩ := (M.od_range x).mpr (by
      rintro ⟨a', ha', -⟩; rw [hcls0] at ha'; simp at ha')
    have h1 : G'.molecule.atom y = c := by
      apply M.ob_inj
      rw [M.ob_atom, hy, hc, ← hxa]; unfold repC; rw [hcls0]; rfl
    have hcls1 : cls (G.molecule.atom (G.molecule.mate x)) = none := hU _ hx.2
    have h2 : G'.molecule.atom (G'.molecule.mate y) = d := by
      apply M.ob_inj
      rw [M.ob_atom, M.od_mate, hy, hd, ← hxb]; unfold repC; rw [hcls1]; rfl
    exact Relation.EqvGen.rel _ _ ⟨y, (inGroup_pb M hcls hU y).mpr (hy ▸ hx), h1, h2⟩
  | refl a =>
    refine ⟨Iff.rfl, fun _ c d hc hd => ?_⟩
    have : c = d := M.ob_inj (hc.trans hd.symm)
    exact this ▸ Relation.EqvGen.refl _
  | symm a b _ ih =>
    refine ⟨ih.1.symm, fun hb c d hc hd => ?_⟩
    exact (ih.2 (ih.1.mpr hb) d c hd hc).symm
  | trans a b c _ _ ih1 ih2 =>
    refine ⟨ih1.1.trans ih2.1, fun ha c' d hc hd => ?_⟩
    have hb : b ∈ U := ih1.1.mp ha
    have hb0 := hU b hb
    obtain ⟨e, he⟩ := (M.ob_range b).mpr (Or.inl hb0)
    exact Relation.EqvGen.trans _ _ _ (ih1.2 ha c' e hc he) (ih2.2 hb e d he hd)

include hcls hU in
theorem isBlock_pb {a b : GBranch G.tree} (hB : G.molecule.IsBlock U a b) {a' b' : GBranch G'.tree}
    (ha : M.ob a' = a) (hb : M.ob b' = b) : G'.molecule.IsBlock (M.pb U) a' b' := by
  obtain ⟨hsub, haU, hbU, hab, h1, h2, h3, h4, h5, h6⟩ := hB
  have e1 := fun (P : Bool → Prop) [DecidablePred P] (c : GBranch G'.tree) (hc : M.ob c ∈ U) =>
    card_filter_pb M hcls hU P hc
  refine ⟨fun _ _ => mem_univ _, (mem_pb M).mpr (ha ▸ haU), (mem_pb M).mpr (hb ▸ hbU), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact hab (ha ▸ hb ▸ congrArg M.ob h)
  · have := e1 (fun q => q = true) a' (ha ▸ haU)
    rw [ha] at this
    exact this.trans h1
  · have := e1 (fun q => q = false) a' (ha ▸ haU)
    rw [ha] at this
    exact this.trans h2
  · have := e1 (fun q => q = true) b' (hb ▸ hbU)
    rw [hb] at this
    exact this.trans h3
  · have := e1 (fun q => q = false) b' (hb ▸ hbU)
    rw [hb] at this
    exact this.trans h4
  · intro v hv hva hvb
    have hvU : M.ob v ∈ U := (mem_pb M).mp hv
    have := e1 (fun _ => True) v hvU
    simp only [and_true] at this
    unfold Molecule.degIn
    rw [this]
    exact h5 _ hvU (fun h => hva (M.ob_inj (h.trans ha.symm))) (fun h => hvb (M.ob_inj (h.trans hb.symm)))
  · intro u hu v hv
    obtain ⟨hh, h⟩ := eqvGen_pb M hcls hU rfl (h6 (M.ob u) ((mem_pb M).mp hu) (M.ob v) ((mem_pb M).mp hv))
    exact h ((mem_pb M).mp hu) u v rfl rfl

include hcls hU in
theorem internalParent_pb (v : GBranch G'.tree) :
    InternalParent G' (M.pb U) v ↔ InternalParent G U (M.ob v) := by
  constructor
  · rintro ⟨hn, hp⟩
    have ho : (M.ob v).1.2 ≠ [] := fun h => hn ((M.ob_root v).mp h)
    refine ⟨ho, ?_⟩
    have := (mem_pb M).mp hp
    rw [M.ob_parent v hn ho, repC_mem_iff hcls hU] at this
    exact this
  · rintro ⟨ho, hp⟩
    have hn : v.1.2 ≠ [] := fun h => ho ((M.ob_root v).mpr h)
    refine ⟨hn, (mem_pb M).mpr ?_⟩
    rw [M.ob_parent v hn ho, repC_mem_iff hcls hU]
    exact hp

include hcls hU in
theorem clPattern_pb {a b : GBranch G.tree} (hCL : CLParentPattern G U a b) {a' b' : GBranch G'.tree}
    (ha : M.ob a' = a) (hb : M.ob b' = b) : CLParentPattern G' (M.pb U) a' b' :=
  ⟨fun h => hCL.1 (ha ▸ (internalParent_pb M hcls hU a').mp h),
   (internalParent_pb M hcls hU b').mpr (hb ▸ hCL.2)⟩

/-- Add a block `U` with crown `a` to a merge labelling. -/
@[expose] noncomputable def clsAdd {G : Garden w} (cls : GBranch G.tree → Option (GBranch G.tree))
    (U : Finset (GBranch G.tree)) (a : GBranch G.tree) (v : GBranch G.tree) : Option (GBranch G.tree) := by
  classical exact if v ∈ U then some a else cls v

theorem clsAdd_of_mem {G : Garden w} {cls : GBranch G.tree → Option (GBranch G.tree)}
    {U : Finset (GBranch G.tree)} {a v : GBranch G.tree} (h : v ∈ U) : clsAdd cls U a v = some a := by
  classical simp [clsAdd, h]

theorem clsAdd_of_notMem {G : Garden w} {cls : GBranch G.tree → Option (GBranch G.tree)}
    {U : Finset (GBranch G.tree)} {a v : GBranch G.tree} (h : v ∉ U) : clsAdd cls U a v = cls v := by
  classical simp [clsAdd, h]

theorem repC_clsAdd {G : Garden w} (cls : GBranch G.tree → Option (GBranch G.tree))
    (U : Finset (GBranch G.tree)) (a v : GBranch G.tree) :
    repC (clsAdd cls U a) v = if v ∈ U then a else repC cls v := by
  by_cases h : v ∈ U
  · simp only [h, ↓reduceIte]; unfold repC; rw [clsAdd_of_mem h]; rfl
  · simp only [h, ↓reduceIte]; unfold repC; rw [clsAdd_of_notMem h]

theorem clsOK_clsAdd {G : Garden w} {cls : GBranch G.tree → Option (GBranch G.tree)} (hcls : ClsOK cls)
    {U : Finset (GBranch G.tree)} (hU : ∀ v ∈ U, cls v = none) {a : GBranch G.tree} (ha : a ∈ U) :
    ClsOK (clsAdd cls U a) := by
  intro v a' hv
  by_cases h : v ∈ U
  · rw [clsAdd_of_mem h] at hv
    cases hv
    exact clsAdd_of_mem ha
  · rw [clsAdd_of_notMem h] at hv
    have h1 := hcls v a' hv
    have ha' : a' ∉ U := fun h2 => by have := hU a' h2; rw [h1] at this; simp at this
    rw [clsAdd_of_notMem ha']
    exact h1

section Single
variable {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b)

end Single

section Lift
variable {a b : GBranch G.tree} (hB : G.molecule.IsBlock U a b) (hCL : CLParentPattern G U a b)

theorem exists_ob_of_none {v : GBranch G.tree} (h : cls v = none) : ∃ c, M.ob c = v :=
  (M.ob_range v).mpr (Or.inl h)

include hcls hU hB hCL in
/-- The pulled-back block of the next splice, as a (CL) block of `G'`. -/
theorem pb_block :
    ∃ a' b', M.ob a' = a ∧ M.ob b' = b ∧ G'.molecule.IsBlock (M.pb U) a' b' ∧
      CLParentPattern G' (M.pb U) a' b' := by
  obtain ⟨a', ha'⟩ := exists_ob_of_none M (hU a hB.2.1)
  obtain ⟨b', hb'⟩ := exists_ob_of_none M (hU b hB.2.2.1)
  exact ⟨a', b', ha', hb', SpMap.isBlock_pb M hcls hU hB ha' hb', SpMap.clPattern_pb M hcls hU hCL ha' hb'⟩

end Lift

section LiftMap
variable {a b : GBranch G.tree} {a' b' : GBranch G'.tree}
  (hB' : G'.molecule.IsBlock (M.pb U) a' b') (hCL' : CLParentPattern G' (M.pb U) a' b')
  (D : CLSpliceSlots G' (M.pb U) a' b') (ha : M.ob a' = a) (haU : a ∈ U)

/-- The old-name map of the composite splice. -/
@[expose] noncomputable def liftMap :
    SpMap G (clSplicedGardenOfSlots hB' hCL' D) (clsAdd cls U a) where
  ob := fun c => M.ob (stepB hB' hCL' D c)
  od := fun y => M.od (stepD hB' hCL' D y)
  ob_inj := M.ob_inj.comp (stepB_inj hB' hCL' D)
  od_inj := M.od_inj.comp (stepD_inj hB' hCL' D)
  ob_range := fun v => by
    constructor
    · rintro ⟨c, rfl⟩
      have hc := stepB_mem hB' hCL' D c
      by_cases hv : M.ob (stepB hB' hCL' D c) ∈ U
      · have hc1 : stepB hB' hCL' D c ∈ M.pb U := (mem_pb M).mpr hv
        have : stepB hB' hCL' D c = a' := hc.resolve_left (not_not.mpr hc1)
        rw [this, ha]
        right; rw [clsAdd_of_mem haU]
      · rw [clsAdd_of_notMem hv]
        exact (M.ob_range _).mp ⟨_, rfl⟩
    · intro h
      by_cases hv : v ∈ U
      · have : v = a := by
          rcases h with h | h
          · rw [clsAdd_of_mem hv] at h; simp at h
          · rw [clsAdd_of_mem hv] at h; exact (Option.some.inj h).symm
        obtain ⟨c, hc⟩ := exists_stepB hB' hCL' D (Or.inr (rfl : a' = a'))
        exact ⟨c, by rw [hc, ha, this]⟩
      · rw [clsAdd_of_notMem hv] at h
        obtain ⟨c1, hc1⟩ := (M.ob_range v).mpr h
        have : c1 ∉ M.pb U := fun hh => hv (hc1 ▸ (mem_pb M).mp hh)
        obtain ⟨c, hc⟩ := exists_stepB hB' hCL' D (Or.inl this)
        exact ⟨c, by rw [hc, hc1]⟩
  od_range := fun x => by
    constructor
    · rintro ⟨y, rfl⟩ ⟨a2, h1, h2⟩
      have hz := stepD_notInGroup hB' hCL' D y
      by_cases h0 : G.molecule.atom (M.od (stepD hB' hCL' D y)) ∈ U
      · have h0' : G.molecule.atom (G.molecule.mate (M.od (stepD hB' hCL' D y))) ∈ U := by
          by_contra hn
          rw [clsAdd_of_notMem hn] at h2
          rw [clsAdd_of_mem h0] at h1
          have h3 := hcls _ _ h2
          have : a2 = a := (Option.some.inj h1).symm
          rw [this, hU a haU] at h3; simp at h3
        exact hz ((inGroup_pb M hcls hU _).mpr ⟨h0, h0'⟩)
      · rw [clsAdd_of_notMem h0] at h1
        have h0' : G.molecule.atom (G.molecule.mate (M.od (stepD hB' hCL' D y))) ∉ U := by
          intro hm
          rw [clsAdd_of_mem hm] at h2
          have h3 := hcls _ _ h1
          have : a2 = a := (Option.some.inj h2).symm
          rw [this, hU a haU] at h3; simp at h3
        rw [clsAdd_of_notMem h0'] at h2
        exact ((M.od_range _).mp ⟨_, rfl⟩) ⟨a2, h1, h2⟩
    · intro h
      have hnu : ¬∃ a2, cls (G.molecule.atom x) = some a2 ∧ cls (G.molecule.atom (G.molecule.mate x)) = some a2 := by
        rintro ⟨a2, h1, h2⟩
        apply h
        refine ⟨a2, ?_, ?_⟩
        · have : G.molecule.atom x ∉ U := fun hm => by rw [hU _ hm] at h1; simp at h1
          rw [clsAdd_of_notMem this]; exact h1
        · have : G.molecule.atom (G.molecule.mate x) ∉ U := fun hm => by rw [hU _ hm] at h2; simp at h2
          rw [clsAdd_of_notMem this]; exact h2
      obtain ⟨z, hz⟩ := (M.od_range x).mpr hnu
      have hng : ¬ G'.molecule.InGroup (M.pb U) z := by
        intro hg
        have := (inGroup_pb M hcls hU z).mp hg
        rw [hz] at this
        exact h ⟨a, clsAdd_of_mem this.1, clsAdd_of_mem this.2⟩
      obtain ⟨y, hy⟩ := exists_stepD hB' hCL' D hng
      exact ⟨y, by show M.od (stepD hB' hCL' D y) = x; rw [hy, hz]⟩
  od_mate := fun y => by
    show M.od (stepD hB' hCL' D _) = _
    rw [stepD_mate, M.od_mate]
  od_out := fun y => by
    show G.molecule.out (M.od (stepD hB' hCL' D y)) = _
    rw [M.od_out, stepD_out]
  ob_atom := fun y => by
    show M.ob (stepB hB' hCL' D _) = repC (clsAdd cls U a) (G.molecule.atom (M.od (stepD hB' hCL' D y)))
    rw [stepB_atom, repC_clsAdd]
    by_cases hx : G.molecule.atom (M.od (stepD hB' hCL' D y)) ∈ U
    · have hc : G'.molecule.atom (stepD hB' hCL' D y) ∈ M.pb U :=
        (mem_pb M).mpr (by rw [M.ob_atom, repC_mem_iff hcls hU]; exact hx)
      rw [rep_of_mem hc]; simp only [hx, ↓reduceIte]; rw [ha]
    · have hc : G'.molecule.atom (stepD hB' hCL' D y) ∉ M.pb U := fun h =>
        hx ((repC_mem_iff hcls hU).mp (by rw [← M.ob_atom]; exact (mem_pb M).mp h))
      rw [rep_of_notMem hc]; simp only [hx, ↓reduceIte]; rw [M.ob_atom]
  ob_root := fun c => (M.ob_root _).trans (stepB_root hB' hCL' D c)
  ob_parent := fun c hn ho => by
    have ho1 : (stepB hB' hCL' D c).1.2 ≠ [] := fun h => ho ((M.ob_root _).mpr h)
    show M.ob (stepB hB' hCL' D _) = repC (clsAdd cls U a) (GNode.parent (M.ob (stepB hB' hCL' D c)).toNode ho)
    rw [stepB_parent hB' hCL' D c hn ho1, repC_clsAdd]
    have hp := M.ob_parent (stepB hB' hCL' D c) ho1 ho
    by_cases hx : GNode.parent (M.ob (stepB hB' hCL' D c)).toNode ho ∈ U
    · have hc : GNode.parent (stepB hB' hCL' D c).toNode ho1 ∈ M.pb U :=
        (mem_pb M).mpr (by rw [hp, repC_mem_iff hcls hU]; exact hx)
      rw [rep_of_mem hc]; simp only [hx, ↓reduceIte]; rw [ha]
    · have hc : GNode.parent (stepB hB' hCL' D c).toNode ho1 ∉ M.pb U := fun h =>
        hx ((repC_mem_iff hcls hU).mp (by rw [← hp]; exact (mem_pb M).mp h))
      rw [rep_of_notMem hc]; simp only [hx, ↓reduceIte]; rw [hp]

end LiftMap

end SpMap

end WaveTurbulence.RedSplice
