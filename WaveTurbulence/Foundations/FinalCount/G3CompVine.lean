/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3CompTri
/-! **FINALCOUNT-G3**: `CompBeta` along Step 1 (vines). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {D₀ : Type*}

theorem eqvGen_sc {M : Molecule V D} {r : V → V → Prop} (hr : ∀ x y, r x y → M.SameComponent x y) {a b : V}
    (h : Relation.EqvGen r a b) : M.SameComponent a b := by
  induction h with
  | rel x y h => exact hr x y h
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- The atoms of a vine-like object are in one component. -/
theorem vine_obj_sc {M : Molecule V D} (K : VineCut M) {u w : V} (hu : u ∈ K.C.atoms) (hw : w ∈ K.C.atoms) :
    M.SameComponent u w := by
  rcases K.C.shape with h | R
  · obtain ⟨_, _, _, _, _, _, _, _, _, hconn⟩ := h.1
    exact eqvGen_sc (fun x y ⟨z, _, h1, h2⟩ => Relation.EqvGen.rel _ _ ⟨z, h1, h2⟩) (hconn u hu w hw)
  · obtain ⟨_, _, _, _, _, _, _, _, _, hconn⟩ := R.adjoint.1
    exact eqvGen_sc (fun x y ⟨z, _, h1, h2⟩ => Relation.EqvGen.rel _ _ ⟨z.1, h1, h2⟩) (hconn u hu w hw)

section vinealpha
variable {M : Molecule V D} (K : VineCut M)

/-- Collapse the new joints onto the old ones. -/
def piVine (a : V) : V := if a = K.fa then K.C.upper else if a = K.fb then K.C.lower else a

theorem piVine_atom (z : D) : piVine K (K.cutMol.atom z) = M.atom z := by
  have hfa : K.fa ≠ K.fb := K.fa_ne_fb
  have hA : M.atom z ≠ K.fa := fun e => K.fa_fresh (e ▸ M.atom_mem z)
  have hB : M.atom z ≠ K.fb := fun e => K.fb_fresh (e ▸ M.atom_mem z)
  have e2 : K.cutMol.atom z = (K.m1.cut K.C.lower K.fb K.y₁ K.y₂).atom z := rfl
  rw [e2, cut_atom, show K.m1.atom z = (M.cut K.C.upper K.fa K.x₁ K.x₂).atom z from rfl, cut_atom]
  by_cases c1 : M.atom z = K.C.upper ∧ z ≠ K.x₁ ∧ z ≠ K.x₂
  · rw [if_pos c1]
    have : ¬ (K.fa = K.C.lower ∧ z ≠ K.y₁ ∧ z ≠ K.y₂) := fun h => K.fa_ne_b h.1
    rw [if_neg this]
    simp only [piVine, if_true]; exact c1.1.symm
  · rw [if_neg c1]
    by_cases c2 : M.atom z = K.C.lower ∧ z ≠ K.y₁ ∧ z ≠ K.y₂
    · rw [if_pos c2]
      simp only [piVine, hfa.symm, if_false, if_true]; exact c2.1.symm
    · rw [if_neg c2]
      simp only [piVine, hA, hB, if_false]

theorem post_atoms_eq : K.post.atoms = (insert K.fb (insert K.fa M.atoms)).filter (fun a => a ∉ K.C.atoms) := rfl

theorem piVine_mem {a : V} (ha : a ∈ K.post.atoms) : piVine K a ∈ M.atoms := by
  rw [post_atoms_eq] at ha
  obtain ⟨ha1, _⟩ := Finset.mem_filter.1 ha
  simp only [Finset.mem_insert] at ha1
  unfold piVine
  rcases ha1 with rfl | rfl | h
  · by_cases h' : K.fb = K.fa
    · rw [if_pos h']; exact objectAtoms_sub K.C K.a_mem
    · rw [if_neg h', if_pos rfl]; exact objectAtoms_sub K.C K.b_mem
  · rw [if_pos rfl]; exact objectAtoms_sub K.C K.a_mem
  · have h1 : a ≠ K.fa := fun e => K.fa_fresh (e ▸ h)
    have h2 : a ≠ K.fb := fun e => K.fb_fresh (e ▸ h)
    rw [if_neg h1, if_neg h2]; exact h

/-- **If a vine removal creates no new component, the two fresh joints are in one component.** -/
theorem vine_sc_fafb (hα : K.post.numComponents ≤ M.numComponents) : K.post.SameComponent K.fa K.fb := by
  have hfa : K.fa ∈ K.post.atoms := by
    rw [post_atoms_eq, Finset.mem_filter]
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
      fun h => K.fa_fresh (objectAtoms_sub K.C h)⟩
  have hfb : K.fb ∈ K.post.atoms := by
    rw [post_atoms_eq, Finset.mem_filter]
    exact ⟨Finset.mem_insert_self _ _, fun h => K.fb_fresh (objectAtoms_sub K.C h)⟩
  let f : Quot (fun u w : K.post.atoms => K.post.Adj u.1 w.1) → Quot (fun u w : M.atoms => M.Adj u.1 w.1) :=
    Quot.map (fun a : K.post.atoms => (⟨piVine K a.1, piVine_mem K a.2⟩ : M.atoms)) (by
      intro a b h
      obtain ⟨z, hz1, hz2⟩ := h
      refine ⟨z.1, ?_, ?_⟩
      · show M.atom z.1 = piVine K a.1
        rw [← hz1]; exact (piVine_atom K z.1).symm
      · show M.atom (M.mate z.1) = piVine K b.1
        rw [← hz2]; exact (piVine_atom K (K.cutMol.mate z.1)).symm)
  have hsurj : Function.Surjective f := by
    intro q
    induction q using Quot.ind with
    | mk a =>
      obtain ⟨a, ha⟩ := a
      by_cases hC : a ∈ K.C.atoms
      · refine ⟨Quot.mk _ ⟨K.fa, hfa⟩, ?_⟩
        show Quot.mk _ (⟨piVine K K.fa, _⟩ : M.atoms) = Quot.mk _ ⟨a, ha⟩
        rw [quot_mk_eq_iff M _ _ _ ha]
        have : piVine K K.fa = K.C.upper := by simp [piVine]
        rw [this]
        exact vine_obj_sc K K.a_mem hC
      · have hp : a ∈ K.post.atoms := by
          rw [post_atoms_eq, Finset.mem_filter]
          exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha), hC⟩
        refine ⟨Quot.mk _ ⟨a, hp⟩, ?_⟩
        show Quot.mk _ (⟨piVine K a, _⟩ : M.atoms) = Quot.mk _ ⟨a, ha⟩
        have h1 : a ≠ K.fa := fun e => K.fa_fresh (e ▸ ha)
        have h2 : a ≠ K.fb := fun e => K.fb_fresh (e ▸ ha)
        simp only [piVine, h1, h2, if_false]
  by_contra hn
  have hbij := hsurj.bijective_of_nat_card_le hα
  have hfab : f (Quot.mk _ ⟨K.fa, hfa⟩) = f (Quot.mk _ ⟨K.fb, hfb⟩) := by
    show Quot.mk _ (⟨piVine K K.fa, _⟩ : M.atoms) = Quot.mk _ (⟨piVine K K.fb, _⟩ : M.atoms)
    rw [quot_mk_eq_iff M _ _ (piVine_mem K hfa) (piVine_mem K hfb)]
    have h1 : piVine K K.fa = K.C.upper := by simp [piVine]
    have h2 : piVine K K.fb = K.C.lower := by simp [piVine, K.fa_ne_fb.symm]
    rw [h1, h2]
    exact vine_obj_sc K K.a_mem K.b_mem
  have := hbij.1 hfab
  exact hn ((quot_mk_eq_iff K.post _ _ hfa hfb).1 this)

theorem vine_post_mem {a : V} (haM : a ∈ M.atoms) (haC : a ∉ K.C.atoms) : a ∈ K.post.atoms := by
  rw [post_atoms_eq, Finset.mem_filter]
  exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem haM), haC⟩

theorem vine_cutMol_not_C {a w : V} (haC : a ∉ K.C.atoms) (hw : w ∈ K.C.atoms)
    (h : K.cutMol.SameComponent a w) : False :=
  ((PClosed.sc_iff K.cutMol (fun a => a ∉ K.C.atoms) K.closed h).1 haC) hw

theorem vine_near (hα : K.post.numComponents ≤ M.numComponents) {a : V} (haM : a ∈ M.atoms)
    (haC : a ∉ K.C.atoms) (hU : M.SameComponent a K.C.upper) : K.post.SameComponent a K.fa := by
  have hfafb := vine_sc_fafb K hα
  have hup : K.C.upper ∈ K.C.atoms := K.a_mem
  have hlo : K.C.lower ∈ K.C.atoms := K.b_mem
  have hcd1 : M.IsCutData K.C.upper K.fa K.x₁ K.x₂ := K.cut_a
  have h1 : (M.cut K.C.upper K.fa K.x₁ K.x₂).SameComponent a K.C.upper ∨
      (M.cut K.C.upper K.fa K.x₁ K.x₂).SameComponent a K.fa := by
    rcases cut_sc_split hcd1 hU with h | ⟨hn, _⟩
    · exact Or.inl h
    · exact hn
  have key : K.cutMol.SameComponent a K.fa ∨ K.cutMol.SameComponent a K.fb := by
    have step : ∀ y, (M.cut K.C.upper K.fa K.x₁ K.x₂).SameComponent a y →
        (y = K.C.upper ∨ y = K.fa) → K.cutMol.SameComponent a K.fa ∨ K.cutMol.SameComponent a K.fb := by
      intro y hy hyy
      rcases cut_sc_split K.cut_b hy with h | ⟨hn, hn'⟩
      · rcases hyy with rfl | rfl
        · exact absurd h (vine_cutMol_not_C K haC hup)
        · exact Or.inl h
      · rcases hn with hn | hn
        · exact absurd hn (vine_cutMol_not_C K haC hlo)
        · exact Or.inr hn
    rcases h1 with h | h
    · exact step _ h (Or.inl rfl)
    · exact step _ h (Or.inr rfl)
  have hPa : (fun a => a ∉ K.C.atoms) a := haC
  rcases key with h | h
  · exact restrictP_sc_of K.cutMol _ K.closed h hPa
  · exact Relation.EqvGen.trans _ _ _ (restrictP_sc_of K.cutMol _ K.closed h hPa)
      (Relation.EqvGen.symm _ _ hfafb)

theorem vine_far {a b : V} (haM : a ∈ M.atoms) (haC : a ∉ K.C.atoms)
    (hU : ¬ M.SameComponent a K.C.upper) (hbM : b ∈ M.atoms) (hab : M.SameComponent a b) :
    b ∉ K.C.atoms ∧ K.post.SameComponent a b := by
  have hup : K.C.upper ∈ K.C.atoms := K.a_mem
  have hlo : K.C.lower ∈ K.C.atoms := K.b_mem
  have hUL : M.SameComponent K.C.upper K.C.lower := vine_obj_sc K hup hlo
  have hbC : b ∉ K.C.atoms := fun hb =>
    hU (Relation.EqvGen.trans _ _ _ hab (vine_obj_sc K hb hup))
  refine ⟨hbC, ?_⟩
  have hL : ¬ M.SameComponent a K.C.lower := fun h =>
    hU (Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ hUL))
  have hafa : a ≠ K.fa := fun e => K.fa_fresh (e ▸ haM)
  have hafb : a ≠ K.fb := fun e => K.fb_fresh (e ▸ haM)
  have hbfa : b ≠ K.fa := fun e => K.fa_fresh (e ▸ hbM)
  have hbfb : b ≠ K.fb := fun e => K.fb_fresh (e ▸ hbM)
  have hlfa : K.C.lower ≠ K.fa := K.fa_ne_b.symm
  have hcd1 : M.IsCutData K.C.upper K.fa K.x₁ K.x₂ := K.cut_a
  have hN1 : (M.cut K.C.upper K.fa K.x₁ K.x₂).SameComponent a b := by
    rcases cut_sc_split hcd1 hab with h | ⟨hn, _⟩
    · exact h
    · exfalso
      rcases hn with hn | hn
      · exact hU (by simpa [piV, hafa] using cutSC_pi M hcd1 hn)
      · exact hU (by simpa [piV, hafa] using cutSC_pi M hcd1 hn)
  have hN2 : K.cutMol.SameComponent a b := by
    rcases cut_sc_split K.cut_b hN1 with h | ⟨hn, _⟩
    · exact h
    · exfalso
      have hl : (M.cut K.C.upper K.fa K.x₁ K.x₂).SameComponent a K.C.lower := by
        rcases hn with hn | hn
        · simpa [piV, hafb] using cutSC_pi (M.cut K.C.upper K.fa K.x₁ K.x₂) K.cut_b hn
        · simpa [piV, hafb] using cutSC_pi (M.cut K.C.upper K.fa K.x₁ K.x₂) K.cut_b hn
      exact hL (by simpa [piV, hafa, hlfa] using cutSC_pi M hcd1 hl)
  exact restrictP_sc_of K.cutMol _ K.closed hN2 haC

end vinealpha

section vinestate
variable {s : St.{u} V D₀} (K : VineCut s.M) (c : Cls)

theorem vineSt_M : (vineSt s K c).M = K.post := rfl

theorem vineSt_cls_old {a : V} (haM : a ∈ s.M.atoms) (haC : a ∉ K.C.atoms) :
    (vineSt s K c).cls a = s.cls a := by
  have h1 : a ≠ K.C.upper := fun e => haC (e ▸ K.a_mem)
  have h2 : a ≠ K.C.lower := fun e => haC (e ▸ K.b_mem)
  have h3 : a ≠ K.fa := fun e => K.fa_fresh (e ▸ haM)
  have h4 : a ≠ K.fb := fun e => K.fb_fresh (e ▸ haM)
  show Function.update (Function.update (Function.update (Function.update s.cls K.C.upper c) K.fa c)
    K.C.lower c) K.fb c a = s.cls a
  rw [Function.update_of_ne h4, Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h1]

theorem vineSt_cls_fa : (vineSt s K c).cls K.fa = c := by
  have e1 : K.fa ≠ K.fb := K.fa_ne_fb
  have e2 : K.fa ≠ K.C.lower := K.fa_ne_b
  show Function.update (Function.update (Function.update (Function.update s.cls K.C.upper c) K.fa c)
    K.C.lower c) K.fb c K.fa = c
  rw [Function.update_of_ne e1, Function.update_of_ne e2, Function.update_self]

theorem vineSt_cls_fb : (vineSt s K c).cls K.fb = c := by
  show Function.update (Function.update (Function.update (Function.update s.cls K.C.upper c) K.fa c)
    K.C.lower c) K.fb c K.fb = c
  rw [Function.update_self]

theorem vineSt_deg_old {a : V} (haM : a ∈ s.M.atoms) (haC : a ∉ K.C.atoms) :
    (vineSt s K c).M.deg a = s.M.deg a := by
  have h1 : a ≠ K.C.upper := fun e => haC (e ▸ K.a_mem)
  have h2 : a ≠ K.C.lower := fun e => haC (e ▸ K.b_mem)
  have h3 : a ≠ K.fa := fun e => K.fa_fresh (e ▸ haM)
  have h4 : a ≠ K.fb := fun e => K.fb_fresh (e ▸ haM)
  show (restrictP K.cutMol (fun a => a ∉ K.C.atoms) K.closed).deg a = s.M.deg a
  rw [restrictP_deg K.cutMol _ K.closed haC]
  show ((s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg a = _
  rw [cut_deg_other K.cut_b h2 h4, cut_deg_other K.cut_a h1 h3]

theorem contrib_vineSt_old {a : V} (haM : a ∈ s.M.atoms) (haC : a ∉ K.C.atoms) :
    contrib (vineSt s K c) a = contrib s a := by
  unfold contrib
  rw [vineSt_cls_old K c haM haC, vineSt_deg_old K c haM haC]

theorem vineSt_deg_fa : (vineSt s K c).M.deg K.fa + 2 = s.M.deg K.C.upper := by
  have hfaC : K.fa ∉ K.C.atoms := fun h => K.fa_fresh (objectAtoms_sub K.C h)
  show (restrictP K.cutMol (fun a => a ∉ K.C.atoms) K.closed).deg K.fa + 2 = _
  rw [restrictP_deg K.cutMol _ K.closed hfaC]
  show ((s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg K.fa + 2 = _
  rw [cut_deg_other K.cut_b K.fa_ne_b K.fa_ne_fb]
  exact cut_deg_v₂ K.cut_a

theorem vineSt_deg_fb : (vineSt s K c).M.deg K.fb + 2 = s.M.deg K.C.lower := by
  have hfbC : K.fb ∉ K.C.atoms := fun h => K.fb_fresh (objectAtoms_sub K.C h)
  show (restrictP K.cutMol (fun a => a ∉ K.C.atoms) K.closed).deg K.fb + 2 = _
  rw [restrictP_deg K.cutMol _ K.closed hfbC]
  have h1 := cut_deg_v₂ K.cut_b
  show ((s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg K.fb + 2 = _
  rw [h1]
  show (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = _
  exact cut_deg_other K.cut_a K.ab_ne.symm K.fa_ne_b.symm

theorem vine_fa_mem : K.fa ∈ K.post.atoms := by
  rw [post_atoms_eq, Finset.mem_filter]
  exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun h => K.fa_fresh (objectAtoms_sub K.C h)⟩

theorem vine_fb_mem : K.fb ∈ K.post.atoms := by
  rw [post_atoms_eq, Finset.mem_filter]
  exact ⟨Finset.mem_insert_self _ _, fun h => K.fb_fresh (objectAtoms_sub K.C h)⟩

/-- A witness (`β`-atom or atom of odd degree) in the component of the fresh joint `fa`. -/
theorem vine_wit {R : ℕ} (hg : Good R s) (hC : CompBeta s) (ρ : ℝ) (kp : ℕ)
    (hu : s.cls K.C.upper = .eps) (hl : s.cls K.C.lower = .eps)
    (hα : K.post.numComponents ≤ s.M.numComponents) :
    ∃ b ∈ K.post.atoms, K.post.SameComponent K.fa b ∧
      ((vineSt s K (.alpha ρ kp)).cls b = .beta ∨ contrib (vineSt s K (.alpha ρ kp)) b ≠ 0) := by
  have hfafb := vine_sc_fafb K hα
  have hup : K.C.upper ∈ s.M.atoms := objectAtoms_sub K.C K.a_mem
  obtain ⟨b₀, hb₀, hUb, hprop⟩ := hC K.C.upper hup (by rw [hu]; simp)
  by_cases hbC : b₀ ∈ K.C.atoms
  · by_cases h1 : b₀ = K.C.upper
    · have hodd : contrib s K.C.upper ≠ 0 := by
        rcases hprop with h | h
        · rw [h1, hu] at h; exact absurd h (by simp)
        · rw [h1] at h; exact h
      refine ⟨K.fa, vine_fa_mem K, Relation.EqvGen.refl _, Or.inr ?_⟩
      have := vineSt_deg_fa K (.alpha ρ kp)
      have hcls : (vineSt s K (.alpha ρ kp)).cls K.fa = .alpha ρ kp := vineSt_cls_fa K _
      unfold contrib at hodd ⊢
      rw [hcls]; rw [hu] at hodd
      simp only [Cls.base] at hodd ⊢
      omega
    · by_cases h2 : b₀ = K.C.lower
      · have hodd : contrib s K.C.lower ≠ 0 := by
          rcases hprop with h | h
          · rw [h2, hl] at h; exact absurd h (by simp)
          · rw [h2] at h; exact h
        refine ⟨K.fb, vine_fb_mem K, hfafb, Or.inr ?_⟩
        have := vineSt_deg_fb K (.alpha ρ kp)
        have hcls : (vineSt s K (.alpha ρ kp)).cls K.fb = .alpha ρ kp := vineSt_cls_fb K _
        unfold contrib at hodd ⊢
        rw [hcls]; rw [hl] at hodd
        simp only [Cls.base] at hodd ⊢
        omega
      · exfalso
        have h4 := vine_interior_deg K hg.1.bounds hbC h1 h2
        have hce : s.cls b₀ = .eps := by
          by_contra hne; have := (hg.1.ab b₀ hb₀ hne).1; omega
        rcases hprop with h | h
        · rw [hce] at h; exact absurd h (by simp)
        · exact h (by unfold contrib; rw [hce, h4]; rfl)
  · have hpm := vine_post_mem K hb₀ hbC
    have hnear := vine_near K hα hb₀ hbC (Relation.EqvGen.symm _ _ hUb)
    refine ⟨b₀, hpm, Relation.EqvGen.symm _ _ hnear, ?_⟩
    rw [vineSt_cls_old K _ hb₀ hbC, contrib_vineSt_old K _ hb₀ hbC]; exact hprop

theorem vine_compBeta_alpha {R : ℕ} (hg : Good R s) (hC : CompBeta s) (ρ : ℝ) (kp : ℕ)
    (hu : s.cls K.C.upper = .eps) (hl : s.cls K.C.lower = .eps)
    (hα : K.post.numComponents ≤ s.M.numComponents) :
    CompBeta (vineSt s K (.alpha ρ kp)) := by
  have hfafb := vine_sc_fafb K hα
  obtain ⟨bw, hbw, hfabw, hpw⟩ := vine_wit K hg hC ρ kp hu hl hα
  intro a ha hga
  have ha' : a ∈ K.post.atoms := ha
  rw [post_atoms_eq, Finset.mem_filter] at ha'
  obtain ⟨ham, haC⟩ := ha'
  simp only [Finset.mem_insert] at ham
  rcases ham with rfl | rfl | haM
  · exact ⟨bw, hbw, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hfafb) hfabw, hpw⟩
  · exact ⟨bw, hbw, hfabw, hpw⟩
  · by_cases hU : s.M.SameComponent a K.C.upper
    · have := vine_near K hα haM haC hU
      exact ⟨bw, hbw, Relation.EqvGen.trans _ _ _ this hfabw, hpw⟩
    · rw [vineSt_cls_old K _ haM haC] at hga
      obtain ⟨b, hb, hab, hprop⟩ := hC a haM hga
      obtain ⟨hbC, hpost⟩ := vine_far K haM haC hU hb hab
      refine ⟨b, vine_post_mem K hb hbC, hpost, ?_⟩
      rw [vineSt_cls_old K _ hb hbC, contrib_vineSt_old K _ hb hbC]; exact hprop

end vinestate

end WaveTurbulence.FinalCountG3
