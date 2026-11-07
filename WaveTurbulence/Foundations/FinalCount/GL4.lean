/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL3
/-! **G3-LOWDEG (R48), part 4**: Step 1 at a vine-like object with a degree-`2` joint (TARGET Operation 1: "the two joints then
become two atoms of degree at most `2` (it is possible that they have degree `0`, i.e. isolated atoms)").  The isolated half of
a degree-`2` joint is a ghost and is deleted together with the VC; the half of a joint of degree `≥ 3` is a `β`-atom
(a new component is created: the isolated half itself). State-level definitions and invariants. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} {d : ℕ}

/-- The class of the half of the joint `v` that stays: a ghost if `v` has degree `2` (the half carries no dart), else `β`. -/
noncomputable def jcls {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (v : V) : Cls :=
  if M.deg v = 2 then .ghost else .beta

/-- The atoms kept by Step 1 at a degree-`2` joint: outside the VC, and not an isolated half of a degree-`2` joint. -/
def VineKeep {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : VineCut M) : V → Prop :=
  fun a => a ∉ K.C.atoms ∧ ¬ (a = K.fa ∧ M.deg K.C.upper = 2) ∧ ¬ (a = K.fb ∧ M.deg K.C.lower = 2)

section vk
variable {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem vineCut_fa_dartless (K : VineCut M) (hd : M.deg K.C.upper = 2) : K.cutMol.dartsAt K.fa = ∅ := by
  rw [K.dartsAt_fa]
  have hne : K.x₁ ≠ K.x₂ := by
    intro e; have h1 := K.cut_a.2.2.2.2.2.1; have h2 := K.cut_a.2.2.2.2.2.2; rw [e] at h1; simp_all
  have hx₁ : M.atom K.x₁ = K.C.upper := K.cut_a.2.2.1
  have hx₂ : M.atom K.x₂ = K.C.upper := K.cut_a.2.2.2.1
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  rw [Finset.mem_filter] at hx
  obtain ⟨hx, hx1, hx2⟩ := hx
  have hxa : M.atom x = K.C.upper := by simpa [Molecule.dartsAt] using hx
  rcases dart_of_deg_two M hd hx₁ hx₂ hne x hxa with h | h
  · exact hx1 h
  · exact hx2 h

theorem m1_atom_lower (K : VineCut M) {z : D} (hz : K.m1.atom z = K.C.lower) : M.atom z = K.C.lower := by
  have h := hz
  change (M.cut K.C.upper K.fa K.x₁ K.x₂).atom z = _ at h
  rw [cut_atom] at h
  split_ifs at h with hc
  · exact absurd h K.fa_ne_b
  · exact h

theorem vineCut_fb_dartless (K : VineCut M) (hd : M.deg K.C.lower = 2) : K.cutMol.dartsAt K.fb = ∅ := by
  rw [K.dartsAt_fb]
  have hne : K.y₁ ≠ K.y₂ := by
    intro e; have h1 := K.cut_b.2.2.2.2.2.1; have h2 := K.cut_b.2.2.2.2.2.2; rw [e] at h1; simp_all
  have hy₁ : M.atom K.y₁ = K.C.lower := m1_atom_lower K K.cut_b.2.2.1
  have hy₂ : M.atom K.y₂ = K.C.lower := m1_atom_lower K K.cut_b.2.2.2.1
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  rw [Finset.mem_filter] at hx
  obtain ⟨hx, hx1, hx2⟩ := hx
  have hxa : M.atom x = K.C.lower := by simpa [Molecule.dartsAt] using hx
  rcases dart_of_deg_two M hd hy₁ hy₂ hne x hxa with h | h
  · exact hx1 h
  · exact hx2 h

theorem VineKeep.closed (K : VineCut M) : PClosed K.cutMol (VineKeep K) := by
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨K.closed x h1, ?_, ?_⟩
  · rintro ⟨he, hd⟩
    have : K.cutMol.mate x ∈ K.cutMol.dartsAt K.fa := by
      rw [mem_dartsAt]; exact he
    rw [vineCut_fa_dartless K hd] at this; exact absurd this (by simp)
  · rintro ⟨he, hd⟩
    have : K.cutMol.mate x ∈ K.cutMol.dartsAt K.fb := by
      rw [mem_dartsAt]; exact he
    rw [vineCut_fb_dartless K hd] at this; exact absurd this (by simp)
end vk

/-- **The state after Step 1 at a vine-like object with a degree-`2` joint**: both cuts (the halves of degree-`2` joints are
ghosts, the other halves `β`), then removal of the VC and of the ghosts. -/
noncomputable def vineStG (s : St.{u} V D₀) (K : VineCut s.M) : St.{u} V D₀ :=
  ((s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)).cutSt K.C.lower K.fb K.y₁ K.y₂ .beta
    (jcls s.M K.C.lower)).delSt (VineKeep K) (VineKeep.closed K)


theorem betaSt_cutSt (s : St.{u} V D₀) (v v₂ : V) (x₁ x₂ : s.D) (c₁ c₂ : Cls) :
    (s.betaSt v).cutSt v v₂ x₁ x₂ c₁ c₂ = s.cutSt v v₂ x₁ x₂ c₁ c₂ := by
  unfold St.cutSt St.betaSt St.withCls
  simp [Function.update_idem]

section inv
variable {s : St.{u} V D₀} {R : ℕ}

theorem Inv.contrib_nonneg' (hI : Inv R s) {a : V} (ha : a ∈ s.M.atoms) : 0 ≤ contrib s a := by
  have hle := deg_le_four s.M (hI.bounds a ha)
  unfold contrib
  by_cases he : s.cls a = .eps
  · rw [he]; simp only [Cls.base]; omega
  · have := hI.ab a ha he
    rcases hc : s.cls a with _ | _ | _ | _
    · exact absurd hc he
    · simp only [Cls.base]; omega
    · simp only [Cls.base]; omega
    · have h0 := this.2.1 hc
      simp only [Cls.base]; omega

theorem Inv.sum_contrib' (hI : Inv R s) : ∑ a ∈ s.M.atoms, contrib s a = 2 * R := by
  unfold contrib
  rw [Finset.sum_sub_distrib]
  have h1 := hI.phi
  have h2 := sum_deg_eq s.M
  have h3 : ∑ a ∈ s.M.atoms, ((s.M.deg a : ℕ) : ℤ) = (Fintype.card s.D : ℤ) := by exact_mod_cast h2
  rw [h1, h3]; ring

/-- `Inv`-level index drop under the class change of a degree-`2` `ε`-atom. -/
theorem Inv.betaSt (hI : Inv R s) {v : V} (hv : v ∈ s.M.atoms) (hε : s.cls v = .eps) (hd : s.M.deg v = 2) :
    1 ≤ R ∧ Inv (R - 1) (s.betaSt v) := by
  have hc : contrib s v = 2 := by unfold contrib; rw [hε, hd]; simp [Cls.base]
  have hsum := hI.sum_contrib'
  have hge : contrib s v ≤ ∑ a ∈ s.M.atoms, contrib s a :=
    Finset.single_le_sum (f := contrib s) (fun b hb => hI.contrib_nonneg' hb) hv
  have hR : 1 ≤ R := by omega
  have hcl : ∀ a, (s.betaSt v).cls a = if a = v then Cls.beta else s.cls a := by
    intro a; by_cases h : a = v
    · rw [if_pos h, h]; simp [St.betaSt_cls]
    · rw [if_neg h]; simp [St.betaSt_cls, Function.update_of_ne h]
  refine ⟨hR, hI.bounds, ?_, ?_, ?_, hI.noloop⟩
  · intro a ha hae
    by_cases h : a = v
    · rw [hcl, if_pos h] at hae; exact absurd hae (by simp)
    · rw [hcl, if_neg h] at hae; exact hI.eps a ha hae
  · intro a ha hne
    by_cases h : a = v
    · subst h
      refine ⟨by show s.M.deg a ≤ 2; omega, fun hg' => ?_, fun _ => by show 1 ≤ s.M.deg a; omega⟩
      rw [hcl, if_pos rfl] at hg'; exact absurd hg' (by simp)
    · rw [hcl, if_neg h] at hne ⊢
      exact hI.ab a ha hne
  · show ∑ a ∈ s.M.atoms, ((s.betaSt v).cls a).base = _
    have hrep := sum_replace (s := s.M.atoms) (f := fun a => (s.cls a).base)
      (g := fun a => ((s.betaSt v).cls a).base) hv (fun a _ ha' => by rw [hcl, if_neg ha'])
    have h1 : ((s.betaSt v).cls v).base = 2 := by rw [hcl, if_pos rfl]; rfl
    have h2 : (s.cls v).base = 4 := by rw [hε]; rfl
    rw [h1, h2] at hrep
    have := hI.phi
    show _ = (Fintype.card s.D : ℤ) + 2 * ((R - 1 : ℕ) : ℤ)
    have : ((R - 1 : ℕ) : ℤ) = (R : ℤ) - 1 := by omega
    rw [this]
    linarith

/-- **One joint of Step 1**: the cut of an `ε`-atom of degree `≥ 3` (halves `β`) or of degree `2` (half `β`, other half a ghost;
the index drops by one). -/
theorem Inv.cutJ (hI : Inv R s) {v v₂ : V} {x₁ x₂ : s.D} (hcd : s.M.IsCutData v v₂ x₁ x₂) (hε : s.cls v = .eps)
    (hj : 3 ≤ s.M.deg v ∨ s.M.deg v = 2) :
    ∃ R', R' + (if s.M.deg v = 2 then 1 else 0) = R ∧ Inv R' (s.cutSt v v₂ x₁ x₂ .beta (jcls s.M v)) := by
  by_cases h2 : s.M.deg v = 2
  · obtain ⟨hR, hI'⟩ := hI.betaSt hcd.1 hε h2
    have hcl : (s.betaSt v).cls v = .beta := by simp [St.betaSt_cls]
    have := hI'.cutSt (s := s.betaSt v) (v := v) (v₂ := v₂) (x₁ := x₁) (x₂ := x₂) hcd .beta .ghost
      (by rw [hcl]; rfl) (by simp) (by simp) (by simp) (fun _ => h2) (fun h => absurd rfl h)
    refine ⟨R - 1, by rw [if_pos h2]; omega, ?_⟩
    rw [betaSt_cutSt] at this
    have hj : jcls s.M v = .ghost := by unfold jcls; rw [if_pos h2]
    rw [hj]; exact this
  · have h3 : 3 ≤ s.M.deg v := hj.resolve_right h2
    refine ⟨R, by rw [if_neg h2]; rfl, ?_⟩
    have hj : jcls s.M v = .beta := by unfold jcls; rw [if_neg h2]
    rw [hj]
    exact hI.cutSt hcd .beta .beta (by rw [hε]; rfl) (by simp) (by simp) (by simp) (fun h => absurd h (by simp))
      (fun _ => h3)

theorem jcls_congr {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (M : Molecule V D)
    (M' : Molecule V D') {v : V} (h : M.deg v = M'.deg v) : jcls M v = jcls M' v := by
  unfold jcls; rw [h]

/-- The number of degree-`2` joints of the object. -/
noncomputable def jdeg2 {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : VineCut M) : ℕ :=
  (if M.deg K.C.upper = 2 then 1 else 0) + (if M.deg K.C.lower = 2 then 1 else 0)

theorem Inv.vineStG (hI : Inv R s) (K : VineCut s.M) (hu : s.cls K.C.upper = .eps) (hl : s.cls K.C.lower = .eps)
    (hju : 3 ≤ s.M.deg K.C.upper ∨ s.M.deg K.C.upper = 2) (hjl : 3 ≤ s.M.deg K.C.lower ∨ s.M.deg K.C.lower = 2) :
    ∃ R', R' + jdeg2 K = R ∧ Inv R' (vineStG s K) := by
  obtain ⟨R1, e1, hI1⟩ := hI.cutJ K.cut_a hu hju
  have hdl : (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = s.M.deg K.C.lower :=
    cut_deg_other K.cut_a K.ab_ne.symm K.fa_ne_b.symm
  have hlow : (s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)).cls K.C.lower = .eps := by
    show Function.update (Function.update s.cls K.C.upper .beta) K.fa (jcls s.M K.C.upper) K.C.lower = _
    rw [Function.update_of_ne K.fa_ne_b.symm, Function.update_of_ne K.ab_ne.symm]; exact hl
  obtain ⟨R2, e2, hI2⟩ := hI1.cutJ (s := s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper))
    K.cut_b hlow (by
      show 3 ≤ (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower ∨ (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = 2
      rw [hdl]; exact hjl)
  have hj2 : jcls (s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)).M K.C.lower = jcls s.M K.C.lower :=
    jcls_congr _ _ hdl
  rw [hj2] at hI2
  have e2' : (if (s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)).M.deg K.C.lower = 2 then 1 else 0) =
      (if s.M.deg K.C.lower = 2 then 1 else 0) := by
    show (if (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = 2 then 1 else 0) = _
    rw [hdl]
  rw [e2'] at e2
  refine ⟨R2, by unfold jdeg2; omega, ?_⟩
  refine hI2.delSt _ (VineKeep.closed K) ?_
  intro a ha hna
  have hna' : a ∈ K.C.atoms ∨ (a = K.fa ∧ s.M.deg K.C.upper = 2) ∨ (a = K.fb ∧ s.M.deg K.C.lower = 2) := by
    unfold VineKeep at hna
    by_contra hcon
    push Not at hcon
    exact hna ⟨hcon.1, fun h => hcon.2.1 h.1 h.2, fun h => hcon.2.2 h.1 h.2⟩
  have e_ua : K.C.upper ≠ K.fa := fun e => K.fa_fresh (e ▸ K.a_atom)
  have e_ub : K.C.upper ≠ K.fb := K.fb_ne_a.symm
  have e_ul : K.C.upper ≠ K.C.lower := K.ab_ne
  have e_lb : K.C.lower ≠ K.fb := fun e => K.fb_fresh (e ▸ K.b_atom)
  have e_la : K.C.lower ≠ K.fa := K.fa_ne_b.symm
  have hcl2 : ∀ b, ((s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)).cutSt K.C.lower K.fb K.y₁ K.y₂ .beta
      (jcls s.M K.C.lower)).cls b = Function.update (Function.update (Function.update (Function.update s.cls K.C.upper .beta)
        K.fa (jcls s.M K.C.upper)) K.C.lower .beta) K.fb (jcls s.M K.C.lower) b := fun b => rfl
  have hdeg2 : ∀ b, ((s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)).cutSt K.C.lower K.fb K.y₁ K.y₂ .beta
      (jcls s.M K.C.lower)).M.deg b = ((s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg b :=
    fun b => rfl
  show (((s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)).cutSt K.C.lower K.fb K.y₁ K.y₂ .beta
      (jcls s.M K.C.lower)).cls a).base = _
  rw [hcl2, hdeg2]
  rcases hna' with haC | ⟨hfa, hd2⟩ | ⟨hfb, hd2⟩
  · have haM : a ∈ s.M.atoms := objectAtoms_sub K.C haC
    have hfa : a ≠ K.fa := fun e => K.fa_fresh (e ▸ haM)
    have hfb : a ≠ K.fb := fun e => K.fb_fresh (e ▸ haM)
    by_cases h1 : a = K.C.upper
    · rw [h1, Function.update_of_ne e_ub, Function.update_of_ne e_ul, Function.update_of_ne e_ua, Function.update_self]
      rw [cut_deg_other K.cut_b e_ul e_ub, cut_deg_v s.M K.cut_a]; rfl
    · by_cases h2 : a = K.C.lower
      · rw [h2, Function.update_of_ne e_lb, Function.update_self]
        rw [cut_deg_v _ K.cut_b]; rfl
      · rw [Function.update_of_ne hfb, Function.update_of_ne h2, Function.update_of_ne hfa, Function.update_of_ne h1,
          cut_deg_other K.cut_b h2 hfb, cut_deg_other K.cut_a h1 hfa]
        have h4 := vine_interior_deg K hI.bounds haC h1 h2
        have hce' : s.cls a = .eps := by
          by_contra hne
          have := (hI.ab a haM hne).1; omega
        rw [hce', h4]; rfl
  · -- the ghost half `fa` of a degree-`2` joint
    subst hfa
    have hne1 : K.fa ≠ K.fb := K.fa_ne_fb
    have hjc : jcls s.M K.C.upper = .ghost := by unfold jcls; rw [if_pos hd2]
    rw [Function.update_of_ne hne1, Function.update_of_ne K.fa_ne_b, Function.update_self, hjc]
    rw [cut_deg_other K.cut_b K.fa_ne_b K.fa_ne_fb]
    have := cut_deg_v₂ K.cut_a
    rw [hd2] at this
    rw [show (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.fa = 0 by omega]; rfl
  · subst hfb
    have hjc : jcls s.M K.C.lower = .ghost := by unfold jcls; rw [if_pos hd2]
    rw [Function.update_self, hjc]
    have := cut_deg_v₂ K.cut_b
    have hdl' : ((s.M.cut K.C.upper K.fa K.x₁ K.x₂)).deg K.C.lower = 2 := by rw [hdl]; exact hd2
    rw [hdl'] at this
    rw [show ((s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg K.fb = 0 by omega]; rfl
end inv
end WaveTurbulence.FinalCountG3
