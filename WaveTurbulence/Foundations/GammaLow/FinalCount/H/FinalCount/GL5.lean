/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3DPInv2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.GL5`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **G3-LOWDEG (R48), part 5**: the step `HStepD1` (Step 1 at an object with a degree-`2` joint) and its invariants. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-! ### Small facts about `jcls` and the joints -/
theorem two_le_deg_upper {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : Step1.VineCut Src.γL M) :
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

theorem two_le_deg_lower {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : Step1.VineCut Src.γL M) :
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

/-- The state with history after Step 1 at an object with a degree-`2` joint. -/
noncomputable def HSt.vinePostGL (h : HSt V D₀) (K : Step1.VineCut Src.γL h.s.M) : HSt V D₀ :=
  ⟨vineStG h.s K, h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist,
   Function.update (Function.update (Function.update (Function.update h.crec K.C.upper
     (some (h.s.pr K.x₁ K.x₂, h.alive))) K.fa (some (h.s.pr K.x₁ K.x₂, h.alive))) K.C.lower
     (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive))) K.fb
     (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive)),
   Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower)⟩

alias _root_.WaveTurbulence.FinalCountG3.HSt.vinePostGL := _root_.WaveTurbulence.GammaLow.FinalCount.H.HSt.vinePostGL
/-- **Step D1** (R48 item 3): Step 1 at an SG vine-like object with a joint of degree `2`.  A new component is created (the
isolated half of the degree-`2` joint), so the surviving halves are `β`-atoms (TARGET Operation 1); the isolated halves are
deleted with the VC. -/
inductive HStepD1 (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : HSt V D₀ → HSt V D₀ → Prop
  | vine (h : HSt V D₀) (K : Step1.VineCut Src.γL h.s.M) (hu : h.s.cls K.C.upper = .eps) (hl : h.s.cls K.C.lower = .eps)
      (hd2 : h.s.M.deg K.C.upper = 2 ∨ h.s.M.deg K.C.lower = 2)
      (htwin : pgap L w κ (h.s.pr K.y₁ K.y₂) = pgap L w κ (h.s.pr K.x₁ K.x₂) ∨
        pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂))
      (hsg : Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG)
      (hnew : h.s.M.numComponents < K.post.numComponents)
      (hdu : Desig C (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂)) (hdl : Desig C (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂)) :
      HStepD1 C L γ η w κ h (h.vinePostGL K)

section inv
variable {h h' : HSt V D₀}

theorem clean_vineStG {s : St.{u} V D₀} (hC : Clean s) (K : Step1.VineCut Src.γL s.M) : Clean (vineStG s K) := by
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

theorem HInv.vinePostGL (hI : HInv L γ η w κ h) (K : Step1.VineCut Src.γL h.s.M)
    (htwin : pgap L w κ (h.s.pr K.y₁ K.y₂) = pgap L w κ (h.s.pr K.x₁ K.x₂) ∨
      pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂))
    (hsg : Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG) :
    HInv L γ η w κ (h.vinePostGL K) := by
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


alias _root_.WaveTurbulence.FinalCountG3.HInv.vinePostGL := _root_.WaveTurbulence.GammaLow.FinalCount.H.HInv.vinePostGL
theorem HGap.vinePostGL (hG : HGap L w κ h) (hI : Inv R h.s) (K : Step1.VineCut Src.γL h.s.M) (hu : h.s.cls K.C.upper = .eps)
    (hl : h.s.cls K.C.lower = .eps) :
    HGap L w κ (h.vinePostGL K) := by
  have hdu := two_le_deg_upper K
  have hdl := two_le_deg_lower K
  have hup4 := deg_le_four _ (hI.bounds _ K.cut_a.1)
  have hlo : K.C.lower ∈ h.s.M.atoms := Step1.objectAtoms_sub K.C K.b_mem
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

alias _root_.WaveTurbulence.FinalCountG3.HGap.vinePostGL := _root_.WaveTurbulence.GammaLow.FinalCount.H.HGap.vinePostGL
theorem AncRel.vinePostGL {s : St.{u} V D₀} {a : V → V} (hr : AncRel M₀ s a) (K : Step1.VineCut Src.γL s.M) :
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

alias _root_.WaveTurbulence.FinalCountG3.AncRel.vinePostGL := _root_.WaveTurbulence.GammaLow.FinalCount.H.AncRel.vinePostGL
theorem DartRel.vineStGL {s : St.{u} V D₀} (hr : DartRel M₀ s) (K : Step1.VineCut Src.γL s.M) : DartRel M₀ (vineStG s K) := by
  have h1 := hr.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper) (by simp) (jcls_ne_eps _ _) K.cut_a.2.1
  have h2 := h1.cutSt K.C.lower K.fb K.y₁ K.y₂ .beta (jcls s.M K.C.lower) (by simp) (jcls_ne_eps _ _) K.cut_b.2.1
  exact h2.delSt _ (VineKeep.closed K)

alias _root_.WaveTurbulence.FinalCountG3.DartRel.vineStGL := _root_.WaveTurbulence.GammaLow.FinalCount.H.DartRel.vineStGL
theorem BalS.vineStGL {s : St.{u} V D₀} (hB : BalS s) (K : Step1.VineCut Src.γL s.M) : BalS (vineStG s K) :=
  (((hB.cutSt K.cut_a _ _).cutSt K.cut_b _ _).delSt _ (VineKeep.closed K))

alias _root_.WaveTurbulence.FinalCountG3.BalS.vineStGL := _root_.WaveTurbulence.GammaLow.FinalCount.H.BalS.vineStGL
theorem CompBeta.vineStGL {s : St.{u} V D₀} (hC : CompBeta s) (K : Step1.VineCut Src.γL s.M) : CompBeta (vineStG s K) := by
  have hdl : (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = s.M.deg K.C.lower :=
    cut_deg_other K.cut_a K.ab_ne.symm K.fa_ne_b.symm
  have c1 := hC.cutβ K.cut_a (jcls s.M K.C.upper) (jcls_cases _ _)
  have c2 := c1.cutβ K.cut_b (jcls s.M K.C.lower) (by
    rcases jcls_cases s.M K.C.lower with h | ⟨h, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, by show (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = 2; rw [hdl]; exact h2⟩)
  exact c2.delSt _ (VineKeep.closed K)


alias _root_.WaveTurbulence.FinalCountG3.CompBeta.vineStGL := _root_.WaveTurbulence.GammaLow.FinalCount.H.CompBeta.vineStGL
theorem EpsLe.vineStGL {s : St.{u} V D₀} (K : Step1.VineCut Src.γL s.M) : EpsLe s (vineStG s K) := by
  have e1 := EpsLe.cutSt s K.x₁ K.x₂ K.cut_a.1 K.cut_a.2.1 .beta (jcls s.M K.C.upper) (by simp) (jcls_ne_eps _ _)
  have e2 := EpsLe.cutSt (s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)) K.y₁ K.y₂ K.cut_b.1 K.cut_b.2.1
    .beta (jcls s.M K.C.lower) (by simp) (jcls_ne_eps _ _)
  exact (e1.trans e2).trans (EpsLe.delSt _ _ (VineKeep.closed K))

theorem HStepD1.data {C : CollData M₀} {h h' : HSt V D₀} (hs : HStepD1 C L γ η w κ h h') :
    ∃ K : Step1.VineCut Src.γL h.s.M, h.s.cls K.C.upper = .eps ∧ h.s.cls K.C.lower = .eps ∧
      (h.s.M.deg K.C.upper = 2 ∨ h.s.M.deg K.C.lower = 2) ∧
      (pgap L w κ (h.s.pr K.y₁ K.y₂) = pgap L w κ (h.s.pr K.x₁ K.x₂) ∨
        pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂)) ∧
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG ∧ h' = h.vinePostGL K := by
  cases hs with
  | vine K hu hl hd2 htwin hsg hnew hdu hdl => exact ⟨K, hu, hl, hd2, htwin, hsg, rfl⟩

/-- **The index drops by `1` or `2`** along Step D1 (one per degree-`2` joint). -/
theorem InvL.stepD1L {C : CollData M₀} (hs : HStepD1 C L γ η w κ h h') (hr : InvL M₀ R L γ η w κ h) :
    ∃ j R', 1 ≤ j ∧ R' + j = R ∧ InvL M₀ R' L γ η w κ h' := by
  obtain ⟨K, hu, hl, hd2, htwin, hsg, rfl⟩ := hs.data
  have hdu := two_le_deg_upper K
  have hdl := two_le_deg_lower K
  obtain ⟨R', e, hI⟩ := Inv.vineStGL hr.good.1 K hu hl (by omega) (by omega)
  refine ⟨jdeg2 K, R', ?_, e, ?_⟩
  · unfold jdeg2; rcases hd2 with h | h <;> simp [h]
  · exact { good := ⟨hI, clean_vineStG hr.good.2 K⟩
            hrec := hr.hrec.vinePostGL K htwin hsg
            gap := hr.gap.vinePostGL hr.good.1 K hu hl
            comp := hr.comp.vineStGL K
            bal := hr.bal.vineStGL K
            rel := hr.rel.vineStGL K }

alias _root_.WaveTurbulence.FinalCountG3.InvL.stepD1L := _root_.WaveTurbulence.GammaLow.FinalCount.H.InvL.stepD1L
theorem DPInv.vinePostGL (hI : DPInv h) (hinj : Function.Injective h.s.down) (K : Step1.VineCut Src.γL h.s.M) :
    DPInv (h.vinePostGL K) := by
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

alias _root_.WaveTurbulence.FinalCountG3.DPInv.vinePostGL := _root_.WaveTurbulence.GammaLow.FinalCount.H.DPInv.vinePostGL
end inv
end WaveTurbulence.GammaLow.FinalCount.H
