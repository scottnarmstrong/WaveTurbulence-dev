/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase2
public import WaveTurbulence.Foundations.FinalCount.AsmRun2
public import WaveTurbulence.Foundations.FinalCount.AsmTriPot2
public import WaveTurbulence.Foundations.FinalCount.AsmPhase3c
public import WaveTurbulence.Foundations.FinalCount.G3Ex2G
/-! **FINALCOUNT-ASSEMBLY, phase 2: per-node facts** (invariant of the post class, dart count decrease, deviation in `stepRHS` form).
Ghost-free triangles use G3 `tri_excess` and `stepRHS_tri`; triangles with a ghost use the named input `GhostTriangleStep`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem apPos_triSt {s : St.{u} V D₀} (hap : ApPos s) (T : TriData s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
    (hQ : ∀ j, 0 < Q j) (hcl : PClosed T.kept (triKeep s T)) : ApPos (triSt s T Q kp hcl) := by
  intro a ha R k hc
  have hcls : (triSt s T Q kp hcl).cls a = triCls s T Q kp a := rfl
  rw [hcls] at hc
  have ham : a ∈ T.m3.atoms := (Finset.mem_filter.1 (Finset.mem_filter.1 ha).1).1
  rw [TriData.m3_atoms] at ham
  simp only [Finset.mem_insert] at ham
  rcases ham with rfl | rfl | rfl | hs
  · rw [triCls_f2] at hc; split_ifs at hc
  · rw [triCls_f1] at hc
    split_ifs at hc with h1 h2
    injection hc with e1 e2; rw [← e1]; exact hQ 1
  · rw [triCls_f0] at hc
    split_ifs at hc with h1 h2
    injection hc with e1 e2; rw [← e1]; exact hQ 0
  · rw [triCls_other T Q kp (fun j e => T.f_fresh j (e ▸ hs))] at hc
    exact hap a hs R k hc

theorem card_dart_post2 [Infinite V] {L γ η : ℝ} {h : HSt V D₀} {n : T2 h} (hn : Node2 L γ η h n) :
    Fintype.card (post2 L γ η h n).s.D < Fintype.card h.s.D := by
  rw [post2_eq hn]; exact card_dart_triSt_lt _ _ _ _


theorem runInv_of_reach {M₀ : Molecule V D₀} {Rn : ℕ} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} (hS : SubHyp Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Relation.ReflTransGen (HAny L γ η w κ) (HSt.init M₀) h) : RunInv Rn L γ η w κ h :=
  rtgH (S := HAny L γ η w κ) (P := RunInv Rn L γ η w κ)
    (fun _ _ hs hI => by rcases hs with hs | hs | hs | hs; exacts [hI.step1 hs, hI.step2 hs, hI.step3 hs, hI.step4 hs]) hr
    (RunInv.init hS h0)

theorem node2_facts [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 A : Set (D₀ → (Fin d → ℤ))} (H : TriReal d L γ η δ C₁) (hS : SubHyp Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hRA : ∀ κ h, Rch κ h → Relation.ReflTransGen (HAny L γ η w κ) (HSt.init M₀) h)
    (h8 : 8 * η ≤ 2 * γ - 1)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    {h : HSt V D₀} (hA : Inv3 M₀ Rn Rch L w A0 A h) {n : T2 h} (hn : Node2 L γ η h n)
    (hext : ∀ k ∈ cls2 L γ η w h A n, Rch k h → Rch k (post2 L γ η h n)) :
    Inv3 M₀ Rn Rch L w A0 (cls2 L γ η w h A n) (post2 L γ η h n) ∧
    Fintype.card (post2 L γ η h n).s.D < Fintype.card h.s.D ∧
    QS L γ δ C₁ w P h (cls2 L γ η w h A n) ≤
      ENNReal.ofReal (ghostConst d c η δ * stepRHS L γ η h (post2 L γ η h n)) *
        QS L γ δ C₁ w P (post2 L γ η h n) (cls2 L γ η w h A n) := by
  have hsub : cls2 L γ η w h A n ⊆ A := fun k hk => hk.1
  have hlt := card_dart_post2 hn
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hQpos : ∀ j, 0 < Q2 n j := fun j => zpow_pos (by norm_num) _
  by_cases hAe : cls2 L γ η w h A n = ∅
  · refine ⟨⟨hsub.trans hA.1, Or.inl hAe⟩, hlt, ?_⟩
    rw [hAe, QS_empty]; exact bot_le
  rcases hA.2 with he | ⟨hc, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hsub)) hAe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAe
  have hcc := uctx_mono hc (fun k (hk : k ∈ cls2 L γ η w h A n) => hk.1)
  have hpp := pinned_mono hp0 (fun k (hk : k ∈ cls2 L γ η w h A n) => hA.1 hk.1)
  have hst := uStep2_node (L := L) (γ := γ) (η := η) (w := w) (A := A) hn
  have hc' : UCtx M₀ Rn (fun k => k ∈ cls2 L γ η w h A n) L w (post2 L γ η h n) := UCtx.step2 hκ hst hpp hcc
  have hap' : ApPos (post2 L γ η h n).s := by
    rw [post2_eq hn]; exact apPos_triSt hap _ _ _ hQpos _
  have hr' : ∀ k ∈ cls2 L γ η w h A n, Rch k (post2 L γ η h n) := fun k hk => hext k hk (hr k hk.1)
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨hc', hap', hr'⟩⟩, hlt, ?_⟩
  have hI : Inv Rn h.s := hc.good.1
  have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
  have hcard : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c := by
    have := UCtx.card_atoms_le hS hcc
    exact le_trans (by exact_mod_cast this) hnc
  have hX : 0 ≤ stepRHS L γ η h (post2 L γ η h n) := by
    unfold stepRHS
    have h1 := apProd_pos (L := L) (γ := γ) (η := η) hL hap
    have h2 := apProd_pos (L := L) (γ := γ) (η := η) hL hap'
    positivity
  have hCB : CompBeta h.s := (invE_of_reach hS (h0 κ (hA.1 hκ.1)) (hRA κ h (hr κ hκ.1))).comp
  have hRI : ∀ k0, k0 ∈ cls2 L γ η w h A n → HInv L γ η w k0 h ∧ HGap L w k0 h := fun k0 hk0 => by
    have := runInv_of_reach hS (h0 k0 (hA.1 hk0.1)) (hRA k0 h (hr k0 hk0.1))
    exact ⟨this.hrec, this.gap⟩
  obtain ⟨T', Q', kp', hcl', hEq, hdev⟩ := UStep2.excess H hst hLC hc.good.2 hCB hcc.atom P hP0 hP hcard ⟨κ, hκ⟩ hRI h8
  rw [hEq] at hX hdev ⊢
  rw [stepRHS_tri' hL hap T' Q' kp' hcl'] at hX ⊢
  exact hdev

end WaveTurbulence.FinalCountAsm
