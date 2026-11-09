/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain9
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain10`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, LC-2 (6): the phase-2 (triangle) cover with the LOW invariant** (`node2_factsL`, `phase2_cover_memL`, `phase2_coverL`;
the degree bound `3 ≤ deg` of the `ε`-atoms of an eligible triangle comes from `NoD3`, `deg_three_of_eligible`). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem node2_factsL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 A : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hRA : ∀ κ h, Rch κ h → Reach2L C Un Fst L γ η w κ h)
    (h8 : 8 * η ≤ 2 * γ - 1)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    {h : HSt V D₀} (hA : Inv3L M₀ Rn Rch L w A0 A h) {n : T2 h} (hn : Node2 L γ η h n)
    (hext : ∀ k ∈ cls2 L γ η w h A n, Rch k h → Rch k (post2 L γ η h n)) :
    Inv3L M₀ Rn Rch L w A0 (cls2 L γ η w h A n) (post2 L γ η h n) ∧
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
  rcases hA.2 with he | ⟨⟨R', hR', hc⟩, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hsub)) hAe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAe
  have hcc := uctx_mono hc (fun k (hk : k ∈ cls2 L γ η w h A n) => hk.1)
  have hpp := pinned_mono hp0 (fun k (hk : k ∈ cls2 L γ η w h A n) => hA.1 hk.1)
  have hst := uStep2_node (L := L) (γ := γ) (η := η) (w := w) (A := A) hn
  have hc' : UCtx M₀ R' (fun k => k ∈ cls2 L γ η w h A n) L w (post2 L γ η h n) := UCtx.step2 hκ hst hpp hcc
  have hap' : ApPos (post2 L γ η h n).s := by
    rw [post2_eq hn]; exact apPos_triSt hap _ _ _ hQpos _
  have hr' : ∀ k ∈ cls2 L γ η w h A n, Rch k (post2 L γ η h n) := fun k hk => hext k hk (hr k hk.1)
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨⟨R', hR', hc'⟩, hap', hr'⟩⟩, hlt, ?_⟩
  have hI : Inv R' h.s := hc.good.1
  have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
  have hcard : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c := by
    have := card_atoms_leL_of_uctx hS hR' hcc
    exact le_trans (by exact_mod_cast this) hnc
  have hX : 0 ≤ stepRHS L γ η h (post2 L γ η h n) := by
    unfold stepRHS
    have h1 := apProd_pos (L := L) (γ := γ) (η := η) hL hap
    have h2 := apProd_pos (L := L) (γ := γ) (η := η) hL hap'
    positivity
  have hCB : CompBeta h.s := by
    obtain ⟨R'', -, hIL⟩ := invL_reach2 hS (h0 κ (hA.1 hκ.1)) (hRA κ h (hr κ hκ.1))
    exact hIL.comp
  have hRI : ∀ k0, k0 ∈ cls2 L γ η w h A n → HInv L γ η w k0 h ∧ HGap L w k0 h := fun k0 hk0 => by
    obtain ⟨R'', -, hIL⟩ := invL_reach2 hS (h0 k0 (hA.1 hk0.1)) (hRA k0 h (hr k0 hk0.1))
    exact ⟨hIL.hrec, hIL.gap⟩
  obtain ⟨T', Q', kp', hcl', hEq, hdev⟩ := UStep2.excess H hst hLC hc.good.2 hCB hcc.atom P hP0 hP hcard ⟨κ, hκ⟩ hRI h8
  rw [hEq] at hX hdev ⊢
  rw [stepRHS_tri' hL hap T' Q' kp' hcl'] at hX ⊢
  exact hdev


/-- **A decoration with an eligible triangle lies in a node class** (phase 2). -/
theorem phase2_cover_memL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η : ℝ} {w : Mom d} {A0 A : Set (D₀ → (Fin d → ℤ))}
    {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} (hS : SubHypL Rn M₀)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hRA : ∀ κ h, Rch κ h → Reach2L C Un Fst L γ η w κ h)
    (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ) (h2 : 2 / L ≤ L ^ (-γ + η))
    {h : HSt V D₀} (hA : Inv3L M₀ Rn Rch L w A0 A h) (hAe : A ≠ ∅) {κ : D₀ → (Fin d → ℤ)} (hκ : κ ∈ A)
    (hnb : ¬ NoEligibleTriangle C L γ η w κ h) :
    ∃ n : T2 h, Node2 L γ η h n ∧ (∀ j : Fin 3, Desig C (h.anc (n.1 j)) (h.s.pr (n.2.1 j) (n.2.2.1 j))) ∧ κ ∈ cls2 L γ η w h A n := by
  obtain ⟨⟨R', hR', hc⟩, hap, hr⟩ := hA.2.resolve_left hAe
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hreach := hRA κ h (hr κ hκ)
  obtain ⟨R'', -, hIL⟩ := invL_reach2 hS (h0 κ (hA.1 hκ)) hreach
  obtain ⟨h₂, hN, hA₂, hD₂, hE⟩ := hreach.d3info hS (h0 κ (hA.1 hκ))
  unfold NoEligibleTriangle at hnb
  push Not at hnb
  obtain ⟨T0, hel⟩ := hnb
  obtain ⟨Q, kp, hQ, hsim, hkp, hi0, hi1⟩ := step2_data (C := C) hL h2 T0 hel
  have hInv := hIL.good.1
  have fs := fresh3_spec h
  let T : TriData h.s.M := triWithF T0 (fresh3 h) fs.1 fs.2
  have hcl : PClosed T.kept (triKeep h.s T) := tri_keep_closed hInv T
  have h3 : ∀ j, h.s.cls (T.t j) = .eps → 3 ≤ h.s.M.deg (T.t j) :=
    deg_three_of_eligible hA₂ hD₂ hc.anc hIL.rel hE hN T0 hel
  have hz : ∀ j : Fin 2, ∃ z : ℤ, Q j = (2 : ℝ) ^ z := fun j => by
    obtain ⟨z, hz, -⟩ := label_zrange hLe hηγ (hQ j); exact ⟨z, hz⟩
  choose z hzQ using hz
  have hQe : Q = fun j => (2 : ℝ) ^ z j := funext hzQ
  have hkpe : kp = fun j => if decide (kp j = 50) then 50 else 0 := by
    funext j; rcases hkp j with e | e <;> simp [e]
  have hd0 : T.t 0 ∈ h.s.M.atoms := T.t_mem 0
  obtain ⟨a0, sg0, ha0, hw0⟩ := alive_data0 (L := L) (γ := γ) (η := η) (w := w) (κ := κ) (h := h) (h.s.pr (T.a 0) (T.b 0)) (Q 0) (T.t 0) hd0
  obtain ⟨a1, sg1, sib, ha1, hw1⟩ := alive_data1 (L := L) (γ := γ) (η := η) (w := w) (κ := κ) (h := h) T (h.s.pr (T.a 0) (T.b 0))
    (h.s.pr (T.a 1) (T.b 1)) rfl (Q 1) (T.t 0) hd0
  let n : T2 h := (T.t, T.a, T.b, z, fun j => decide (kp j = 50), ![a0, a1], ![sg0, sg1], sib)
  have hb0 : (decide (kp 0 = 50)) = true ↔ kp 0 = 50 := decide_eq_true_iff
  have hb1 : (decide (kp 1 = 50)) = true ↔ kp 1 = 50 := decide_eq_true_iff
  have hf0 : (decide (kp 0 = 50)) = false ↔ ¬ kp 0 = 50 := decide_eq_false_iff_not
  have hf1 : (decide (kp 1 = 50)) = false ↔ ¬ kp 1 = 50 := decide_eq_false_iff_not
  refine ⟨n, ⟨T, hcl, rfl, rfl, rfl, rfl, fun j => ?_, h3, fun j => ?_, fun hb => ?_, fun hb hs => ?_, fun hb hs => ?_⟩, hel.2.2, ?_⟩
  · rw [← hzQ j]; exact hQ j
  · fin_cases j <;> simp [n, ha0, ha1]
  · obtain ⟨q, vis, hcr, hq, -⟩ := hw0 (hi0.1 (hb0.1 hb))
    exact ⟨q, vis, hcr, hq⟩
  · obtain ⟨q, vis, hcr, hq, -⟩ := (hw1 (hi1.1 (hb1.1 hb))).1 hs
    exact ⟨q, vis, hcr, hq⟩
  · exact (hw1 (hi1.1 (hb1.1 hb))).2.2 hs
  · subst hQe
    refine ⟨hκ, fun j => hel.1 j, fun j => hsim j, hel.2.1, fun he hb => ?_, fun he hb => ?_, fun he hb => ?_, fun he hb => ?_⟩
    · exact (hw0 (hi0.1 (hb0.1 hb))).choose_spec.choose_spec.2.2
    · exact fun hit => (hf0.1 hb) (hi0.2 hit)
    · refine ⟨fun hs => (hw1 (hi1.1 (hb1.1 hb))).1 hs |>.choose_spec.choose_spec.2.2, fun hs => (hw1 (hi1.1 (hb1.1 hb))).2.1 hs⟩
    · exact fun hit => (hf1.1 hb) (hi1.2 hit)


/-- **Phase 2 cover theorem.** -/
theorem phase2_coverL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c) 
    (h8 : 8 * η ≤ 2 * γ - 1)
    (hRA : ∀ κ h, Rch κ h → Reach2L C Un Fst L γ η w κ h)
    (hext : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (n : T2 h), Node2 L γ η h n →
      (∀ j : Fin 3, Desig C (h.anc (n.1 j)) (h.s.pr (n.2.1 j) (n.2.2.1 j))) → ∀ k ∈ cls2 L γ η w h A n, Rch k h →
        Rch k (post2 L γ η h n))
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h2 : 2 / L ≤ L ^ (-γ + η)) (N : ℕ)
    (hN : nodeBound2 (2 * M₀.atoms.card) (Fintype.card D₀) ⌈2 * Real.log L⌉₊ + 1 ≤ N) (W : HSt V D₀ → ℝ≥0∞)
    (hW : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀) (R' : ℕ), Inv3L M₀ Rn Rch L w A0 A h →
      ApPos h.s → Good R' h.s → (∃ k, k ∈ A) →
      UStep2 L γ η w (fun k => k ∈ A) h h' →
      (N : ℝ≥0∞) * (ENNReal.ofReal (ghostConst d c η δ * stepRHS L γ η h h') * W h') ≤ W h)
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv3L M₀ Rn Rch L w A0 A h →
      (∀ k ∈ A, NoEligibleTriangle C L γ η w k h) → (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn Rch L w A0 A h → QS L γ δ C₁ w P h A ≤ W h := by
  have hηγ : η ≤ γ := by have := H.hη; have := H.hη1; linarith
  refine cover_induction2 (ι := ℕ) (fun a b : HSt V D₀ => Fintype.card a.s.D < Fintype.card b.s.D)
    (InvImage.wf (fun h : HSt V D₀ => Fintype.card h.s.D) wellFounded_lt)
    (fun h A => Inv3L M₀ Rn Rch L w A0 A h) (fun h A => ∀ k ∈ A, NoEligibleTriangle C L γ η w k h)
    (QS L γ δ C₁ w P) W N
    (by omega) (fun h A B hAB => QS_mono L γ δ C₁ w P h hAB) (fun h A B => QS_union L γ δ C₁ w P h A B)
    (fun h => QS_empty L γ δ C₁ w P h) (fun h A => hfin A h) ?_
  intro h A hA _
  let Afin : Set (D₀ → (Fin d → ℤ)) := {k | k ∈ A ∧ NoEligibleTriangle C L γ η w k h}
  have hAfin : Inv3L M₀ Rn Rch L w A0 Afin h := hA.mono fun k hk => hk.1
  by_cases hAe : A = ∅
  · refine ⟨Afin, ∅, fun _ => ∅, fun _ => h, fun _ => 0, hAfin, fun k hk => hk.2, ?_, (by simp; omega), (by simp)⟩
    intro k hk; rw [hAe] at hk; exact absurd hk (by simp)
  obtain ⟨R', hR', hc⟩ := (hA.2.resolve_left hAe).1
  have hapP : ApPos h.s := (hA.2.resolve_left hAe).2.1
  have hcardA : h.s.M.atoms.card ≤ 2 * M₀.atoms.card := card_atoms_leL_of_uctx hS hR' hc
  have hcardD : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
  have hcard : (nodes2D C L γ η h).card ≤ nodeBound2 (2 * M₀.atoms.card) (Fintype.card D₀) ⌈2 * Real.log L⌉₊ := by
    refine (Finset.card_filter_le _ _).trans ((nodes2_card L γ η h).trans ?_)
    unfold nodeBound2
    gcongr
  have hmem : ∀ j t, nodeAt2 C L γ η h j = some t → t ∈ nodes2D C L γ η h := by
    intro j t ht
    unfold nodeAt2 at ht
    split_ifs at ht with hj
    · cases ht; exact ((nodes2D C L γ η h).equivFin.symm ⟨j, hj⟩).2
  have hsurj : ∀ t ∈ nodes2D C L γ η h, ∃ j, nodeAt2 C L γ η h j = some t := by
    intro t ht
    refine ⟨((nodes2D C L γ η h).equivFin ⟨t, ht⟩).1, ?_⟩
    unfold nodeAt2
    rw [dif_pos ((nodes2D C L γ η h).equivFin ⟨t, ht⟩).2]
    simp
  refine ⟨Afin, Finset.range (nodes2D C L γ η h).card, clsAt2 C L γ η w h A, postAt2 C L γ η h,
    (fun j => if clsAt2 C L γ η w h A j = ∅ then 0 else costAt2 C L γ η (ghostConst d c η δ) h j), hAfin, fun k hk => hk.2, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hnb : NoEligibleTriangle C L γ η w k h
    · exact Or.inl ⟨hk, hnb⟩
    · right
      obtain ⟨t, htn, hdt, hkt⟩ := phase2_cover_memL hS h0 hRA H.hL hηγ h2 hA hAe hk hnb
      have ht : t ∈ nodes2D C L γ η h := Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨node2_mem_box H.hL hηγ htn, htn⟩, hdt⟩
      obtain ⟨j, hj⟩ := hsurj t ht
      have hjS : j ∈ Finset.range (nodes2D C L γ η h).card := by
        unfold nodeAt2 at hj
        by_contra hnot
        rw [dif_neg (by simpa using hnot)] at hj
        cases hj
      refine Set.mem_iUnion₂.2 ⟨j, hjS, ?_⟩
      unfold clsAt2
      rw [hj]
      exact hkt
  · simp only [Finset.card_range]; omega
  · intro j hjS
    have hj : j < (nodes2D C L γ η h).card := Finset.mem_range.1 hjS
    obtain ⟨t, ht⟩ : ∃ t, nodeAt2 C L γ η h j = some t := ⟨_, by unfold nodeAt2; rw [dif_pos hj]⟩
    have htm := hmem j t ht
    have hnd : Node2 L γ η h t := (Finset.mem_filter.1 (Finset.mem_filter.1 htm).1).2
    have hdes := (Finset.mem_filter.1 htm).2
    obtain ⟨h1, h2', h3⟩ := node2_factsL H hS hp0 hP hP0 c hnc hRA h8 h0 hA hnd (hext A h t hnd hdes)
    have hcls : clsAt2 C L γ η w h A j = cls2 L γ η w h A t := by unfold clsAt2; rw [ht]
    have hpost : postAt2 C L γ η h j = post2 L γ η h t := by unfold postAt2; rw [ht]
    have hcost : costAt2 C L γ η (ghostConst d c η δ) h j =
        ENNReal.ofReal (ghostConst d c η δ * stepRHS L γ η h (post2 L γ η h t)) := by unfold costAt2; rw [ht]
    rw [hcls, hpost]
    by_cases hce : cls2 L γ η w h A t = ∅
    · rw [hce] at h1
      simp only [hcls, hce, if_true, QS_empty]
      exact ⟨h2', h1, by simp, by simp⟩
    · simp only [hcls, hce, if_false]
      obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hce
      rw [hcost]
      exact ⟨h2', h1, h3, hW _ h _ R' (hA.mono fun k hk => hk.1) hapP hc.good ⟨κ, hκ⟩ (uStep2_node hnd)⟩

end WaveTurbulence.GammaLow.FinalCount.H
