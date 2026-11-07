/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL4
public import WaveTurbulence.Foundations.FinalCount.G3DPInv2
public import WaveTurbulence.Foundations.FinalCount.G3DPInv3
public import WaveTurbulence.Foundations.FinalCount.G3Anc
public import WaveTurbulence.Foundations.FinalCount.G3Ex1New
/-! **G3-LOWDEG (R48), part 5**: the step `HStepD1` (Step 1 at an object with a degree-`2` joint) and its invariants. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- **`HGap` under the cut of a degree-`2` atom** along both its darts: the new half is an isolated ghost. -/
theorem HGap.cut_two {h : HSt V D₀} (hG : HGap L w κ h) {v v₂ : V} {x₁ x₂ : h.s.D}
    (hcd : h.s.M.IsCutData v v₂ x₁ x₂) (hd : h.s.M.deg v = 2) (c₁ : Cls) (hc1 : c₁ ≠ .eps)
    (vis nh : List (D₀ × D₀)) {na : V → V} :
    HGap L w κ ⟨h.s.cutSt v v₂ x₁ x₂ c₁ .ghost, nh,
      Function.update (Function.update h.crec v (some (h.s.pr x₁ x₂, vis))) v₂
        (some (h.s.pr x₁ x₂, vis)), na⟩ where
  chg := by
    intro a ha hae h4'
    have ha' : a ∈ insert v₂ h.s.M.atoms := ha
    have hne : v₂ ≠ v := fun e => hcd.2.1 (e ▸ hcd.1)
    have e2 : a ≠ v₂ := by
      rintro rfl; rw [cutSt_cls_v₂] at hae; exact absurd hae (by simp)
    have e1 : a ≠ v := by
      rintro rfl; rw [cutSt_cls_v _ _ hne] at hae; exact hc1 hae
    rw [cutSt_cls_other _ _ e1 e2] at hae
    have hD : (h.s.cutSt v v₂ x₁ x₂ c₁ .ghost).M.dartsAt a = h.s.M.dartsAt a := cut_dartsAt_other h.s.M hcd e1 e2
    have hdeg : h.s.M.deg a = 4 := by
      have h44 : (h.s.cutSt v v₂ x₁ x₂ c₁ .ghost).M.deg a = 4 := h4'
      have : (h.s.cutSt v v₂ x₁ x₂ c₁ .ghost).M.deg a = h.s.M.deg a := congrArg Finset.card hD
      omega
    have := hG.chg a ((Finset.mem_insert.1 ha').resolve_left e2) hae hdeg
    show ∑ x ∈ (h.s.cutSt v v₂ x₁ x₂ c₁ .ghost).M.dartsAt a, h.s.M.dartSign x • Molecule.kvec L w (κ ∘ h.s.down) x = 0
    rw [hD]; exact this
  dg := by
    intro a ha hac x y hx hy hox0 hoy0
    have hox : h.s.M.out x = false := hox0
    have hoy : h.s.M.out y = true := hoy0
    have ha' : a ∈ insert v₂ h.s.M.atoms := ha
    have hne : v₂ ≠ v := fun e => hcd.2.1 (e ▸ hcd.1)
    by_cases e2 : a = v₂
    · subst e2
      exfalso
      have hx' : x ∈ (h.s.M.cut v a x₁ x₂).dartsAt a := (mem_dartsAt _ _ _).2 hx
      have := cut_deg_v₂ hcd
      have h0 : (h.s.M.cut v a x₁ x₂).deg a = 0 := by omega
      have : (h.s.M.cut v a x₁ x₂).dartsAt a = ∅ := Finset.card_eq_zero.1 h0
      rw [this] at hx'; exact absurd hx' (Finset.notMem_empty _)
    · by_cases e1 : a = v
      · subst e1
        refine ⟨h.s.pr x₁ x₂, vis, by simp [Function.update_of_ne e2], Or.inl ?_⟩
        have hx' : x ∈ (h.s.M.cut a v₂ x₁ x₂).dartsAt a := (mem_dartsAt _ _ _).2 hx
        have hy' : y ∈ (h.s.M.cut a v₂ x₁ x₂).dartsAt a := (mem_dartsAt _ _ _).2 hy
        rw [cut_dartsAt_v_eq h.s.M hcd] at hx' hy'
        have hx'' : x = x₁ ∨ x = x₂ := (Finset.mem_insert.1 hx').imp id Finset.mem_singleton.1
        have hy'' : y = x₁ ∨ y = x₂ := (Finset.mem_insert.1 hy').imp id Finset.mem_singleton.1
        have o1 := hcd.2.2.2.2.2.1
        have o2 := hcd.2.2.2.2.2.2
        have hx1 : x = x₁ := by
          rcases hx'' with h' | h'
          · exact h'
          · have := o2; rw [← h', hox] at this; exact absurd this (by simp)
        have hy2 : y = x₂ := by
          rcases hy'' with h' | h'
          · have := o1; rw [← h', hoy] at this; exact absurd this (by simp)
          · exact h'
        show Molecule.gapAt L w (κ ∘ h.s.down) x y = pgap L w κ (h.s.pr x₁ x₂)
        rw [hx1, hy2]
        rfl
      · rw [cutSt_cls_other _ _ e1 e2] at hac
        obtain ⟨p, vis', hr, hn⟩ := hG.dg a ((Finset.mem_insert.1 ha').resolve_left e2) hac x y
          ((cut_atom_eq_iff h.s.M (v := v) (v₂ := v₂) (x₁ := x₁) (x₂ := x₂) x e1 e2).1 hx)
          ((cut_atom_eq_iff h.s.M (v := v) (v₂ := v₂) (x₁ := x₁) (x₂ := x₂) y e1 e2).1 hy) hox hoy
        exact ⟨p, vis', by simp [Function.update_of_ne e2, Function.update_of_ne e1, hr], hn⟩


/-! ### Small facts about `jcls` and the joints -/
theorem jcls_ne_eps {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (v : V) : jcls M v ≠ .eps := by
  unfold jcls; split_ifs <;> simp

theorem jcls_cases {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (v : V) :
    jcls M v = .beta ∨ (jcls M v = .ghost ∧ M.deg v = 2) := by
  unfold jcls; by_cases h : M.deg v = 2
  · right; exact ⟨if_pos h, h⟩
  · left; exact if_neg h

theorem AtomOK.jcls {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (v : V) {p : D₀ × D₀}
    {vis : List (D₀ × D₀)} (hp : pgap L w κ p ≠ 0) :
    AtomOK L γ η w κ (jcls M v) (some (p, vis)) := by
  rcases jcls_cases M v with h | ⟨h, -⟩
  · rw [h]; exact AtomOK.beta hp
  · rw [h]; exact ⟨fun R' kp h' => absurd h' (by simp), fun h' => absurd h' (by simp)⟩

theorem two_le_deg_upper {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : VineCut M) :
    2 ≤ M.deg K.C.upper := by
  have hne : K.x₁ ≠ K.x₂ := by
    intro e; have h1 := K.cut_a.2.2.2.2.2.1; have h2 := K.cut_a.2.2.2.2.2.2; rw [e] at h1; simp_all
  have hsub : ({K.x₁, K.x₂} : Finset D) ⊆ M.dartsAt K.C.upper := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (mem_dartsAt _ _ _).2 K.cut_a.2.2.1
    · exact (mem_dartsAt _ _ _).2 K.cut_a.2.2.2.1
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at this
  exact this

theorem two_le_deg_lower {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : VineCut M) :
    2 ≤ M.deg K.C.lower := by
  have hne : K.y₁ ≠ K.y₂ := by
    intro e; have h1 := K.cut_b.2.2.2.2.2.1; have h2 := K.cut_b.2.2.2.2.2.2; rw [e] at h1; simp_all
  have hsub : ({K.y₁, K.y₂} : Finset D) ⊆ M.dartsAt K.C.lower := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (mem_dartsAt _ _ _).2 (m1_atom_lower K K.cut_b.2.2.1)
    · exact (mem_dartsAt _ _ _).2 (m1_atom_lower K K.cut_b.2.2.2.1)
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at this
  exact this

/-- `HGap` under one joint cut (degree `≥ 3` `ε`-atom, or degree `2`). -/
theorem HGap.cutJ {h : HSt V D₀} (hG : HGap L w κ h) {v v₂ : V} {x₁ x₂ : h.s.D}
    (hcd : h.s.M.IsCutData v v₂ x₁ x₂) (hε : h.s.cls v = .eps) (h4 : h.s.M.deg v ≤ 4)
    (hj : 3 ≤ h.s.M.deg v ∨ h.s.M.deg v = 2) (vis nh : List (D₀ × D₀)) {na : V → V} :
    HGap L w κ ⟨h.s.cutSt v v₂ x₁ x₂ .beta (jcls h.s.M v), nh,
      Function.update (Function.update h.crec v (some (h.s.pr x₁ x₂, vis))) v₂
        (some (h.s.pr x₁ x₂, vis)), na⟩ := by
  by_cases h2 : h.s.M.deg v = 2
  · have hj : jcls h.s.M v = .ghost := by unfold jcls; rw [if_pos h2]
    rw [hj]; exact hG.cut_two hcd h2 .beta (by simp) vis nh
  · have h3 : 3 ≤ h.s.M.deg v := hj.resolve_right h2
    have hj : jcls h.s.M v = .beta := by unfold jcls; rw [if_neg h2]
    rw [hj]; exact hG.cut_gen hcd hε h3 h4 .beta .beta (by simp) (by simp) vis nh


/-- The state with history after Step 1 at an object with a degree-`2` joint. -/
noncomputable def HSt.vinePostG (h : HSt V D₀) (K : VineCut h.s.M) : HSt V D₀ :=
  ⟨vineStG h.s K, h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist,
   Function.update (Function.update (Function.update (Function.update h.crec K.C.upper
     (some (h.s.pr K.x₁ K.x₂, h.alive))) K.fa (some (h.s.pr K.x₁ K.x₂, h.alive))) K.C.lower
     (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive))) K.fb
     (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive)),
   Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower)⟩

/-- **Step D1** (R48 item 3): Step 1 at an SG vine-like object with a joint of degree `2`.  A new component is created (the
isolated half of the degree-`2` joint), so the surviving halves are `β`-atoms (TARGET Operation 1); the isolated halves are
deleted with the VC. -/
inductive HStepD1 (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : HSt V D₀ → HSt V D₀ → Prop
  | vine (h : HSt V D₀) (K : VineCut h.s.M) (hu : h.s.cls K.C.upper = .eps) (hl : h.s.cls K.C.lower = .eps)
      (hd2 : h.s.M.deg K.C.upper = 2 ∨ h.s.M.deg K.C.lower = 2)
      (htwin : pgap L w κ (h.s.pr K.y₁ K.y₂) = pgap L w κ (h.s.pr K.x₁ K.x₂) ∨
        pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂))
      (hsg : Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG)
      (hnew : h.s.M.numComponents < K.post.numComponents)
      (hdu : Desig C (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂)) (hdl : Desig C (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂)) :
      HStepD1 C L γ η w κ h (h.vinePostG K)

section inv
variable {h h' : HSt V D₀}

theorem clean_vineStG {s : St.{u} V D₀} (hC : Clean s) (K : VineCut s.M) : Clean (vineStG s K) := by
  intro a ha
  have ha' : a ∈ (((s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)).cutSt K.C.lower K.fb K.y₁ K.y₂ .beta
      (jcls s.M K.C.lower)).M.atoms).filter (VineKeep K) := ha
  obtain ⟨haM, haK⟩ := Finset.mem_filter.1 ha'
  obtain ⟨hk1, hk2, hk3⟩ := haK
  have hcl : (vineStG s K).cls a = Function.update (Function.update (Function.update (Function.update s.cls K.C.upper .beta)
        K.fa (jcls s.M K.C.upper)) K.C.lower .beta) K.fb (jcls s.M K.C.lower) a := rfl
  rw [hcl]
  have hat : a ∈ insert K.fb (insert K.fa s.M.atoms) := haM
  by_cases e1 : a = K.fb
  · rw [e1, Function.update_self]
    have : ¬ s.M.deg K.C.lower = 2 := fun hd => hk3 ⟨e1, hd⟩
    unfold jcls; rw [if_neg this]; simp
  · rw [Function.update_of_ne e1]
    by_cases e2 : a = K.C.lower
    · exact absurd (e2 ▸ K.b_mem) hk1
    · rw [Function.update_of_ne e2]
      by_cases e3 : a = K.fa
      · rw [e3, Function.update_self]
        have : ¬ s.M.deg K.C.upper = 2 := fun hd => hk2 ⟨e3, hd⟩
        unfold jcls; rw [if_neg this]; simp
      · rw [Function.update_of_ne e3]
        by_cases e4 : a = K.C.upper
        · exact absurd (e4 ▸ K.a_mem) hk1
        · rw [Function.update_of_ne e4]
          have : a ∈ s.M.atoms := by
            rcases Finset.mem_insert.1 hat with h' | h'
            · exact absurd h' e1
            · rcases Finset.mem_insert.1 h' with h'' | h''
              · exact absurd h'' e3
              · exact h''
          exact hC a this

theorem HInv.vinePostG (hI : HInv L γ η w κ h) (K : VineCut h.s.M)
    (htwin : pgap L w κ (h.s.pr K.y₁ K.y₂) = pgap L w κ (h.s.pr K.x₁ K.x₂) ∨
      pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂))
    (hsg : Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG) :
    HInv L γ η w κ (h.vinePostG K) := by
  have hz1 : pgap L w κ (h.s.pr K.x₁ K.x₂) ≠ 0 := gap_ne_zero_of_SG hsg
  have hz2 : pgap L w κ (h.s.pr K.y₁ K.y₂) ≠ 0 := gap_ne_zero_of_SG (gapKind_of_twin htwin hsg)
  have e1 : AtomOK L γ η w κ .beta (some (h.s.pr K.x₁ K.x₂, h.alive)) := AtomOK.beta hz1
  have e1' : AtomOK L γ η w κ (jcls h.s.M K.C.upper) (some (h.s.pr K.x₁ K.x₂, h.alive)) := AtomOK.jcls _ _ hz1
  have e2 : AtomOK L γ η w κ .beta (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive)) := AtomOK.beta hz2
  have e2' : AtomOK L γ η w κ (jcls h.s.M K.C.lower) (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive)) :=
    AtomOK.jcls _ _ hz2
  have g1 := hI.cut_gen (na := Function.update h.anc K.fa (h.anc K.C.upper)) K.cut_a.1 K.cut_a.2.1 K.x₁ K.x₂ _ _ _ _ _ e1 e1'
    (fun p vis e => mem_of_some List.mem_cons_self e) (fun p vis e => mem_of_some List.mem_cons_self e)
    (fun x hx => List.mem_cons_of_mem _ hx)
    (fun p vis e => sub_of_some (fun q hq => hq) e) (fun p vis e => sub_of_some (fun q hq => hq) e)
    (fun p vis p' vis' e e' => cmp_same e e')
  have g2 := g1.cut_gen (na := Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower))
    K.cut_b.1 K.cut_b.2.1 K.y₁ K.y₂ _ _ _ _ _ e2 e2'
    (fun p vis e => mem_of_some List.mem_cons_self e) (fun p vis e => mem_of_some List.mem_cons_self e)
    (fun x hx => List.mem_cons_of_mem _ hx)
    (fun p vis e => sub_of_some (HSt.alive_cut_sub h _ _ _ _ _ _ _ _ _ _) e)
    (fun p vis e => sub_of_some (HSt.alive_cut_sub h _ _ _ _ _ _ _ _ _ _) e)
    (fun p vis p' vis' e e' => cmp_same e e')
  exact g2.delSt _ (VineKeep.closed K)


theorem HGap.vinePostG (hG : HGap L w κ h) (hI : Inv R h.s) (K : VineCut h.s.M) (hu : h.s.cls K.C.upper = .eps)
    (hl : h.s.cls K.C.lower = .eps) :
    HGap L w κ (h.vinePostG K) := by
  have hdu := two_le_deg_upper K
  have hdl := two_le_deg_lower K
  have hup4 := deg_le_four _ (hI.bounds _ K.cut_a.1)
  have hlo : K.C.lower ∈ h.s.M.atoms := objectAtoms_sub K.C K.b_mem
  have hlo4 := deg_le_four _ (hI.bounds _ hlo)
  have hlne : K.C.lower ≠ K.C.upper := K.ab_ne.symm
  have hlfa : K.C.lower ≠ K.fa := K.fa_ne_b.symm
  have g1 := hG.cutJ (na := Function.update h.anc K.fa (h.anc K.C.upper)) K.cut_a hu hup4
    (by omega) h.alive (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
  have hcl : (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls h.s.M K.C.upper)).cls K.C.lower = .eps := by
    show Function.update (Function.update h.s.cls K.C.upper .beta) K.fa (jcls h.s.M K.C.upper) K.C.lower = _
    rw [Function.update_of_ne hlfa, Function.update_of_ne hlne]; exact hl
  have hdeg : (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = h.s.M.deg K.C.lower :=
    cut_deg_other K.cut_a hlne hlfa
  have g2 := g1.cutJ (na := Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower))
    K.cut_b hcl (by show (h.s.M.cut _ _ _ _).deg _ ≤ 4; omega) (by show 3 ≤ (h.s.M.cut _ _ _ _).deg _ ∨ (h.s.M.cut _ _ _ _).deg _ = 2; omega)
    (h.s.pr K.x₁ K.x₂ :: h.alive) (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
  have hj : jcls (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls h.s.M K.C.upper)).M K.C.lower = jcls h.s.M K.C.lower :=
    jcls_congr _ _ hdeg
  rw [hj] at g2
  exact g2.delSt _ (VineKeep.closed K)

theorem AncRel.vinePostG {s : St.{u} V D₀} {a : V → V} (hr : AncRel M₀ s a) (K : VineCut s.M) :
    AncRel M₀ (vineStG s K) (Function.update (Function.update a K.fa (a K.C.upper)) K.fb (a K.C.lower)) := by
  have h1 := hr.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper) (by simp) (jcls_ne_eps _ _) K.cut_a
    (Function.update a K.fa (a K.C.upper)) (fun b => by
      by_cases e : b = K.fa
      · subst e; simp
      · simp [Function.update_of_ne e, e])
  have h2 := h1.cutSt K.C.lower K.fb K.y₁ K.y₂ .beta (jcls s.M K.C.lower) (by simp) (jcls_ne_eps _ _) K.cut_b
    (Function.update (Function.update a K.fa (a K.C.upper)) K.fb (a K.C.lower)) (fun b => by
      by_cases e : b = K.fb
      · subst e; simp [Function.update_of_ne K.fa_ne_b.symm]
      · simp [Function.update_of_ne e, e])
  exact h2.delSt _ (VineKeep.closed K)

theorem DartRel.vineStG {s : St.{u} V D₀} (hr : DartRel M₀ s) (K : VineCut s.M) : DartRel M₀ (vineStG s K) := by
  have h1 := hr.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper) (by simp) (jcls_ne_eps _ _) K.cut_a.2.1
  have h2 := h1.cutSt K.C.lower K.fb K.y₁ K.y₂ .beta (jcls s.M K.C.lower) (by simp) (jcls_ne_eps _ _) K.cut_b.2.1
  exact h2.delSt _ (VineKeep.closed K)

theorem BalS.vineStG {s : St.{u} V D₀} (hB : BalS s) (K : VineCut s.M) : BalS (vineStG s K) :=
  (((hB.cutSt K.cut_a _ _).cutSt K.cut_b _ _).delSt _ (VineKeep.closed K))

theorem CompBeta.vineStG {s : St.{u} V D₀} (hC : CompBeta s) (K : VineCut s.M) : CompBeta (vineStG s K) := by
  have hdl : (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = s.M.deg K.C.lower :=
    cut_deg_other K.cut_a K.ab_ne.symm K.fa_ne_b.symm
  have c1 := hC.cutβ K.cut_a (jcls s.M K.C.upper) (jcls_cases _ _)
  have c2 := c1.cutβ K.cut_b (jcls s.M K.C.lower) (by
    rcases jcls_cases s.M K.C.lower with h | ⟨h, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, by show (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = 2; rw [hdl]; exact h2⟩)
  exact c2.delSt _ (VineKeep.closed K)


theorem EpsLe.vineStG {s : St.{u} V D₀} (K : VineCut s.M) : EpsLe s (vineStG s K) := by
  have e1 := EpsLe.cutSt s K.x₁ K.x₂ K.cut_a.1 K.cut_a.2.1 .beta (jcls s.M K.C.upper) (by simp) (jcls_ne_eps _ _)
  have e2 := EpsLe.cutSt (s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)) K.y₁ K.y₂ K.cut_b.1 K.cut_b.2.1
    .beta (jcls s.M K.C.lower) (by simp) (jcls_ne_eps _ _)
  exact (e1.trans e2).trans (EpsLe.delSt _ _ (VineKeep.closed K))

theorem HStepD1.data {C : CollData M₀} {h h' : HSt V D₀} (hs : HStepD1 C L γ η w κ h h') :
    ∃ K : VineCut h.s.M, h.s.cls K.C.upper = .eps ∧ h.s.cls K.C.lower = .eps ∧
      (h.s.M.deg K.C.upper = 2 ∨ h.s.M.deg K.C.lower = 2) ∧
      (pgap L w κ (h.s.pr K.y₁ K.y₂) = pgap L w κ (h.s.pr K.x₁ K.x₂) ∨
        pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂)) ∧
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG ∧ h' = h.vinePostG K := by
  cases hs with
  | vine K hu hl hd2 htwin hsg hnew hdu hdl => exact ⟨K, hu, hl, hd2, htwin, hsg, rfl⟩

/-- **The index drops by `1` or `2`** along Step D1 (one per degree-`2` joint). -/
theorem InvL.stepD1 {C : CollData M₀} (hs : HStepD1 C L γ η w κ h h') (hr : InvL M₀ R L γ η w κ h) :
    ∃ j R', 1 ≤ j ∧ R' + j = R ∧ InvL M₀ R' L γ η w κ h' := by
  obtain ⟨K, hu, hl, hd2, htwin, hsg, rfl⟩ := hs.data
  have hdu := two_le_deg_upper K
  have hdl := two_le_deg_lower K
  obtain ⟨R', e, hI⟩ := Inv.vineStG hr.good.1 K hu hl (by omega) (by omega)
  refine ⟨jdeg2 K, R', ?_, e, ?_⟩
  · unfold jdeg2; rcases hd2 with h | h <;> simp [h]
  · exact { good := ⟨hI, clean_vineStG hr.good.2 K⟩
            hrec := hr.hrec.vinePostG K htwin hsg
            gap := hr.gap.vinePostG hr.good.1 K hu hl
            comp := hr.comp.vineStG K
            bal := hr.bal.vineStG K
            rel := hr.rel.vineStG K }

theorem DPInv.vinePostG (hI : DPInv h) (hinj : Function.Injective h.s.down) (K : VineCut h.s.M) :
    DPInv (h.vinePostG K) := by
  have e1 : ∀ p vis, (some (h.s.pr K.x₁ K.x₂, h.alive) : Option ((D₀ × D₀) × List (D₀ × D₀))) = some (p, vis) →
      p = h.s.pr K.x₁ K.x₂ := fun p vis e => by
    simp only [Option.some.injEq, Prod.mk.injEq] at e; exact e.1.symm
  have e2 : ∀ p vis, (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive) : Option ((D₀ × D₀) × List (D₀ × D₀))) =
      some (p, vis) → p = h.s.pr K.y₁ K.y₂ := fun p vis e => by
    simp only [Option.some.injEq, Prod.mk.injEq] at e; exact e.1.symm
  have g1 := hI.cut_gen hinj K.cut_a .beta (jcls h.s.M K.C.upper)
    (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
    (na := Function.update h.anc K.fa (h.anc K.C.upper)) _ _ e1 e1
  have g2 := g1.cut_gen (by exact hinj) K.cut_b .beta (jcls h.s.M K.C.lower)
    (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
    (na := Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower)) _ _ e2 e2
  exact g2.delSt _ (VineKeep.closed K)

end inv
end WaveTurbulence.FinalCountG3
