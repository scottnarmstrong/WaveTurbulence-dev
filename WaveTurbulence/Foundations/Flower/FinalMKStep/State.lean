/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKStep.Pot

/-! # C1a SURV-STEP (2): the state after a re-cut (`vineStG` at an `α/β` joint of degree `2`)

Main's `vineStG s K` (GL4) cuts both joints of the object (the half in the object keeps the class `β`, the other half
gets `jcls`: a ghost at a degree-`2` joint) and deletes the object and the ghosts. Main proves its invariants for
`ε` joints (`Inv.vineStG`, `HGap.vinePostG`, `apProd_vineStG`, `vBeta_vineStG`). Here the joints may also be `α/β`
remnants of degree `2` (the re-cut joints of o75 75-F2):

* `Inv.vineStRC`: the index drops by `jeps K` (the `ε` joints of degree `2`); an `α/β` joint of degree `2` has
  `contrib = 0` and its ghost half has `contrib = 0`, so it does not move the index;
* `HGap.vinePostRC` (an `α/β` joint of degree `2` is cut by main's `HGap.cut_two`), `invL_stepRC` (C1a target 3,
  `InvLStepRC`);
* the general product formula `prod_vineStG'` and its consequences: the label refund
  `apProd s ≤ apProd (vineStG s K)` (`apProd_le_vineStRC`), `vBeta_vineStRC`, `numComponents_vineStRC`. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The class condition of a re-cut joint: `ε`, or an `α/β` remnant of degree `2`. -/
def RCJoint (s : St.{u} V D₀) (v : V) : Prop := s.cls v = .eps ∨ ((s.cls v).IsAB ∧ s.M.deg v = 2)

/-- `1` if the joint is an `ε`-atom of degree `2` (its cut drops the index), else `0`. -/
noncomputable def jepsAt (s : St.{u} V D₀) (v : V) : ℕ := if s.cls v = .eps ∧ s.M.deg v = 2 then 1 else 0

/-- The number of `ε` joints of degree `2` of the object: the index drop of the re-cut step. -/
noncomputable def jeps {s : St.{u} V D₀} (K : VineCut s.M) : ℕ := jepsAt s K.C.upper + jepsAt s K.C.lower

section inv
variable {s : St.{u} V D₀} {R : ℕ}

/-- **One joint of a re-cut**: the cut of an `ε`-atom (as main's `Inv.cutJ`) or of an `α/β` atom of degree `2`
(halves `β` and a ghost; the index does not move). -/
theorem Inv.cutJRC (hI : Inv R s) {v v₂ : V} {x₁ x₂ : s.D} (hcd : s.M.IsCutData v v₂ x₁ x₂) (hj : RCJoint s v)
    (hd : 2 ≤ s.M.deg v) :
    ∃ R', R' + jepsAt s v = R ∧ Inv R' (s.cutSt v v₂ x₁ x₂ .beta (jcls s.M v)) := by
  rcases hj with hε | ⟨hab, h2⟩
  · obtain ⟨R', e, hI'⟩ := hI.cutJ hcd hε (by omega)
    refine ⟨R', ?_, hI'⟩
    unfold jepsAt
    by_cases h2 : s.M.deg v = 2
    · rw [ite_eq_left ⟨hε, h2⟩]; rw [ite_eq_left h2] at e; exact e
    · rw [ite_eq_right (fun h => h2 h.2)]; rw [ite_eq_right h2] at e; exact e
  · have hjc : jcls s.M v = .ghost := by unfold jcls; rw [ite_eq_left h2]
    have hne : s.cls v ≠ .eps := Cls.ne_eps_of_isAB hab
    refine ⟨R, by unfold jepsAt; rw [ite_eq_right (fun h => hne h.1)]; rfl, ?_⟩
    rw [hjc]
    exact hI.cutSt hcd .beta .ghost (by rw [Cls.base_eq_two hab]; rfl) (by simp) (by simp) (by simp)
      (fun _ => h2) (fun h => absurd rfl h)

/-- **The index along a re-cut** (`Inv.vineStG` with re-cut joints): it drops by `jeps K`. -/
theorem Inv.vineStRC (hI : Inv R s) (K : VineCut s.M) (hu : RCJoint s K.C.upper) (hl : RCJoint s K.C.lower) :
    ∃ R', R' + jeps K = R ∧ Inv R' (vineStG s K) := by
  obtain ⟨R1, e1, hI1⟩ := Inv.cutJRC hI K.cut_a hu (two_le_deg_upper K)
  have hdl : (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = s.M.deg K.C.lower :=
    cut_deg_other K.cut_a K.ab_ne.symm K.fa_ne_b.symm
  have hlowc : (s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)).cls K.C.lower = s.cls K.C.lower := by
    show Function.update (Function.update s.cls K.C.upper .beta) K.fa (jcls s.M K.C.upper) K.C.lower = _
    rw [Function.update_of_ne K.fa_ne_b.symm, Function.update_of_ne K.ab_ne.symm]
  have hl' : RCJoint (s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)) K.C.lower := by
    unfold RCJoint
    rw [hlowc]
    show s.cls K.C.lower = .eps ∨ ((s.cls K.C.lower).IsAB ∧ (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = 2)
    rw [hdl]; exact hl
  obtain ⟨R2, e2, hI2⟩ := Inv.cutJRC hI1 (s := s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper))
    K.cut_b hl' (by show 2 ≤ (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower; rw [hdl]; exact two_le_deg_lower K)
  have hj2 : jcls (s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)).M K.C.lower = jcls s.M K.C.lower :=
    jcls_congr _ _ hdl
  rw [hj2] at hI2
  have e2' : jepsAt (s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)) K.C.lower = jepsAt s K.C.lower := by
    unfold jepsAt
    rw [hlowc]
    show (if s.cls K.C.lower = .eps ∧ (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = 2 then 1 else 0) = _
    rw [hdl]
  rw [e2'] at e2
  refine ⟨R2, by unfold jeps; omega, ?_⟩
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
  · subst hfa
    have hne1 : K.fa ≠ K.fb := K.fa_ne_fb
    have hjc : jcls s.M K.C.upper = .ghost := by unfold jcls; rw [ite_eq_left hd2]
    rw [Function.update_of_ne hne1, Function.update_of_ne K.fa_ne_b, Function.update_self, hjc]
    rw [cut_deg_other K.cut_b K.fa_ne_b K.fa_ne_fb]
    have := cut_deg_v₂ K.cut_a
    rw [hd2] at this
    rw [show (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.fa = 0 by omega]; rfl
  · subst hfb
    have hjc : jcls s.M K.C.lower = .ghost := by unfold jcls; rw [ite_eq_left hd2]
    rw [Function.update_self, hjc]
    have := cut_deg_v₂ K.cut_b
    have hdl' : ((s.M.cut K.C.upper K.fa K.x₁ K.x₂)).deg K.C.lower = 2 := by rw [hdl]; exact hd2
    rw [hdl'] at this
    rw [show ((s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg K.fb = 0 by omega]; rfl

theorem jepsAt_le (s : St.{u} V D₀) (v : V) : jepsAt s v ≤ 1 := by
  unfold jepsAt; split_ifs <;> omega

theorem jepsAt_eq_zero {s : St.{u} V D₀} {v : V} (h : s.cls v ≠ .eps) : jepsAt s v = 0 := by
  unfold jepsAt; rw [ite_eq_right (fun h' => h h'.1)]

end inv

section gap
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ}

/-- `HGap` under one joint cut of a re-cut (an `ε` joint: main's `HGap.cutJ`; an `α/β` joint of degree `2`: main's
`HGap.cut_two`). -/
theorem HGap.cutJRC {h : HSt V D₀} (hG : HGap L w κ h) {v v₂ : V} {x₁ x₂ : h.s.D}
    (hcd : h.s.M.IsCutData v v₂ x₁ x₂) (hj : RCJoint h.s v) (h4 : h.s.M.deg v ≤ 4) (hd : 2 ≤ h.s.M.deg v)
    (vis nh : List (D₀ × D₀)) {na : V → V} :
    HGap L w κ ⟨h.s.cutSt v v₂ x₁ x₂ .beta (jcls h.s.M v), nh,
      Function.update (Function.update h.crec v (some (h.s.pr x₁ x₂, vis))) v₂
        (some (h.s.pr x₁ x₂, vis)), na⟩ := by
  rcases hj with hε | ⟨-, h2⟩
  · exact hG.cutJ hcd hε h4 (by omega) vis nh
  · have hjc : jcls h.s.M v = .ghost := by unfold jcls; rw [ite_eq_left h2]
    rw [hjc]; exact hG.cut_two hcd h2 .beta (by simp) vis nh

/-- `HGap` after a re-cut (main's `HGap.vinePostG` with re-cut joints). -/
theorem HGap.vinePostRC {h : HSt V D₀} (hG : HGap L w κ h) (hI : Inv R h.s) (K : VineCut h.s.M)
    (hu : RCJoint h.s K.C.upper) (hl : RCJoint h.s K.C.lower) :
    HGap L w κ (h.vinePostG K) := by
  have hdu := two_le_deg_upper K
  have hdl := two_le_deg_lower K
  have hup4 := deg_le_four _ (hI.bounds _ K.cut_a.1)
  have hlo : K.C.lower ∈ h.s.M.atoms := objectAtoms_sub K.C K.b_mem
  have hlo4 := deg_le_four _ (hI.bounds _ hlo)
  have hlne : K.C.lower ≠ K.C.upper := K.ab_ne.symm
  have hlfa : K.C.lower ≠ K.fa := K.fa_ne_b.symm
  have g1 := HGap.cutJRC hG (na := Function.update h.anc K.fa (h.anc K.C.upper)) K.cut_a hu hup4 hdu h.alive
    (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
  have hcl : (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls h.s.M K.C.upper)).cls K.C.lower = h.s.cls K.C.lower := by
    show Function.update (Function.update h.s.cls K.C.upper .beta) K.fa (jcls h.s.M K.C.upper) K.C.lower = _
    rw [Function.update_of_ne hlfa, Function.update_of_ne hlne]
  have hdeg : (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = h.s.M.deg K.C.lower :=
    cut_deg_other K.cut_a hlne hlfa
  have hl' : RCJoint (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls h.s.M K.C.upper)) K.C.lower := by
    unfold RCJoint
    rw [hcl]
    show h.s.cls K.C.lower = .eps ∨ ((h.s.cls K.C.lower).IsAB ∧ (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = 2)
    rw [hdeg]; exact hl
  have g2 := HGap.cutJRC g1 (na := Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower))
    K.cut_b hl' (by show (h.s.M.cut _ _ _ _).deg _ ≤ 4; omega) (by show 2 ≤ (h.s.M.cut _ _ _ _).deg _; omega)
    (h.s.pr K.x₁ K.x₂ :: h.alive) (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
  have hj : jcls (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls h.s.M K.C.upper)).M K.C.lower = jcls h.s.M K.C.lower :=
    jcls_congr _ _ hdeg
  rw [hj] at g2
  exact g2.delSt _ (VineKeep.closed K)

end gap

section invL
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

theorem HStepRC.data {C : CollData M₀} {h h' : HSt V D₀} (hs : HStepRC C L γ η w κ h h') :
    ∃ K : VineCut h.s.M, RCJoint h.s K.C.upper ∧ RCJoint h.s K.C.lower ∧
      (h.s.cls K.C.upper ≠ .eps ∨ h.s.cls K.C.lower ≠ .eps) ∧
      (pgap L w κ (h.s.pr K.y₁ K.y₂) = pgap L w κ (h.s.pr K.x₁ K.x₂) ∨
        pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂)) ∧
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG ∧
      Desig C (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂) ∧ Desig C (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂) ∧
      h' = h.vinePostG K := by
  cases hs with
  | vine K hu hl hrc htwin hsg hdu hdl => exact ⟨K, hu, hl, hrc, htwin, hsg, hdu, hdl, rfl⟩

/-- At least one joint of a re-cut is an `α/β` atom of degree `2`. -/
theorem rc_deg_two {s : St.{u} V D₀} (K : VineCut s.M) (hu : RCJoint s K.C.upper) (hl : RCJoint s K.C.lower)
    (hrc : s.cls K.C.upper ≠ .eps ∨ s.cls K.C.lower ≠ .eps) :
    s.M.deg K.C.upper = 2 ∨ s.M.deg K.C.lower = 2 := by
  rcases hrc with h | h
  · exact Or.inl ((hu.resolve_left h).2)
  · exact Or.inr ((hl.resolve_left h).2)

/-- **The invariants along a re-cut**: the index drops by `jeps K ≤ 1`. -/
theorem InvL.stepRC {C : CollData M₀} {h h' : HSt V D₀} (hs : HStepRC C L γ η w κ h h')
    (hr : InvL M₀ R L γ η w κ h) :
    ∃ K : VineCut h.s.M, ∃ R', R' + jeps K = R ∧ h' = h.vinePostG K ∧ InvL M₀ R' L γ η w κ h' := by
  obtain ⟨K, hu, hl, -, htwin, hsg, -, -, rfl⟩ := HStepRC.data hs
  obtain ⟨R', e, hI⟩ := Inv.vineStRC hr.good.1 K hu hl
  exact ⟨K, R', e, rfl,
    { good := ⟨hI, clean_vineStG hr.good.2 K⟩
      hrec := hr.hrec.vinePostG K htwin hsg
      gap := HGap.vinePostRC hr.gap hr.good.1 K hu hl
      comp := hr.comp.vineStG K
      bal := hr.bal.vineStG K
      rel := hr.rel.vineStG K }⟩

/-- **C1a target 3: `InvLStepRC`** (the run invariant along a re-cut; the index does not increase). -/
theorem invLStepRC (M₀ : Molecule V D₀) (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) :
    InvLStepRC M₀ C L γ η w κ := by
  intro R h h' hs hr
  obtain ⟨K, R', e, -, hI⟩ := InvL.stepRC hs hr
  exact ⟨R', by omega, hI⟩

end invL

section prod
variable (s : St.{u} V D₀) (K : VineCut s.M)

/-- **Products over the atoms after a re-cut** (main's `prod_vineStG` without the assumption that the removed object
contributes `1`): the post product times the object's product is the old product times the surviving halves. -/
theorem prod_vineStG' {α : Type*} [CommMonoid α] (F : Cls → α) :
    (∏ a ∈ (vineStG s K).M.atoms, F ((vineStG s K).cls a)) * ∏ a ∈ K.C.atoms, F (s.cls a) =
      (if s.M.deg K.C.lower = 2 then 1 else F .beta) * (if s.M.deg K.C.upper = 2 then 1 else F .beta) *
        ∏ a ∈ s.M.atoms, F (s.cls a) := by
  have hfa : K.fa ∉ s.M.atoms := K.fa_fresh
  have hfb : K.fb ∉ insert K.fa s.M.atoms := by
    intro h
    rcases Finset.mem_insert.1 h with e | h
    · exact K.fa_ne_fb e.symm
    · exact K.fb_fresh h
  have hsub : K.C.atoms ⊆ s.M.atoms := fun a ha => objectAtoms_sub K.C ha
  rw [vineStG_atoms, Finset.prod_filter, Finset.prod_insert hfb, Finset.prod_insert hfa]
  have e1 : ∏ a ∈ s.M.atoms, (if VineKeep K a then F ((vineStG s K).cls a) else 1) =
      ∏ a ∈ s.M.atoms.filter (fun a => a ∉ K.C.atoms), F (s.cls a) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun a ha => ?_
    by_cases haC : a ∈ K.C.atoms
    · have : ¬ VineKeep K a := fun hk => hk.1 haC
      rw [ite_eq_right this, ite_eq_right (not_not.2 haC)]
    · have hk : VineKeep K a := by
        refine ⟨haC, ?_, ?_⟩
        · rintro ⟨e, -⟩; exact K.fa_fresh (e ▸ ha)
        · rintro ⟨e, -⟩; exact K.fb_fresh (e ▸ ha)
      rw [ite_eq_left hk, ite_eq_left haC, vineStG_cls_old s K haC ha]
  have h1 : s.M.atoms.filter (fun a => a ∈ K.C.atoms) = K.C.atoms := by
    ext a; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have e2 : ∏ a ∈ s.M.atoms, F (s.cls a) =
      (∏ a ∈ s.M.atoms.filter (fun a => a ∉ K.C.atoms), F (s.cls a)) * ∏ a ∈ K.C.atoms, F (s.cls a) := by
    rw [← Finset.prod_filter_mul_prod_filter_not s.M.atoms (fun a => a ∈ K.C.atoms), h1, mul_comm]
  have hfaK : (if VineKeep K K.fa then F ((vineStG s K).cls K.fa) else 1) = if s.M.deg K.C.upper = 2 then 1 else F .beta := by
    by_cases hd : s.M.deg K.C.upper = 2
    · have : ¬ VineKeep K K.fa := fun hk => hk.2.1 ⟨rfl, hd⟩
      rw [ite_eq_right this, ite_eq_left hd]
    · have hk : VineKeep K K.fa := ⟨fun h => K.fa_fresh (objectAtoms_sub K.C h), fun ⟨_, h⟩ => hd h,
        fun ⟨e, _⟩ => K.fa_ne_fb e⟩
      rw [ite_eq_left hk, ite_eq_right hd, vineStG_cls_fa]; unfold jcls; rw [ite_eq_right hd]
  have hfbK : (if VineKeep K K.fb then F ((vineStG s K).cls K.fb) else 1) = if s.M.deg K.C.lower = 2 then 1 else F .beta := by
    by_cases hd : s.M.deg K.C.lower = 2
    · have : ¬ VineKeep K K.fb := fun hk => hk.2.2 ⟨rfl, hd⟩
      rw [ite_eq_right this, ite_eq_left hd]
    · have hk : VineKeep K K.fb := ⟨fun h => K.fb_fresh (objectAtoms_sub K.C h), fun ⟨e, _⟩ => K.fa_ne_fb e.symm,
        fun ⟨_, h⟩ => hd h⟩
      rw [ite_eq_left hk, ite_eq_right hd, vineStG_cls_fb]; unfold jcls; rw [ite_eq_right hd]
  rw [hfaK, hfbK, e1, e2]
  simp only [mul_assoc]

end prod

end WaveTurbulence.Flower.FinalMKStep
