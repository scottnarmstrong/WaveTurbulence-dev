/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain5
/-! **FINALCOUNT LOW-CHAIN, LC-2 (2): the phase-4 cover with the LOW invariant** (`phase4_cover` of `AsmPhase4b` with `Inv3L`, `SubHypL`, an index `R' ≤ Rn`;
nodes with an empty class cost `0`; the step hypothesis `hW` receives `Good R' h.s` and a decoration of the class). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The state data of a node and the facts the cover needs. -/
theorem node4_factsL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 A : Set (D₀ → (Fin d → ℤ))} (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c) {h : HSt V D₀} (hA : Inv3L M₀ Rn Rch L w A0 A h)
    {v : V} {x₁ x₂ : h.s.D} (hn : Node4 h v x₁ x₂)
    (hext : ∀ k ∈ cls4 L w h A x₁ x₂, Rch k h → Rch k (post4 h v x₁ x₂)) :
    Inv3L M₀ Rn Rch L w A0 (cls4 L w h A x₁ x₂) (post4 h v x₁ x₂) ∧
    epsCount (post4 h v x₁ x₂).s < epsCount h.s ∧
    QS L γ δ C₁ w P h (cls4 L w h A x₁ x₂) ≤
      ENNReal.ofReal (cBeta η c * stepRHS L γ η h (post4 h v x₁ x₂)) *
        QS L γ δ C₁ w P (post4 h v x₁ x₂) (cls4 L w h A x₁ x₂) := by
  have hsub : cls4 L w h A x₁ x₂ ⊆ A := fun k hk => hk.1
  have hlt : epsCount (post4 h v x₁ x₂).s < epsCount h.s :=
    epsCount_cutSt_lt h.s hn.1 hn.2.1 .beta .beta (by simp) (by simp)
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  by_cases hAe : cls4 L w h A x₁ x₂ = ∅
  · refine ⟨⟨hsub.trans hA.1, Or.inl hAe⟩, hlt, ?_⟩
    rw [hAe, QS_empty]; exact bot_le
  rcases hA.2 with he | ⟨⟨R', hR', hc⟩, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hsub)) hAe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAe
  have hcc := uctx_mono hc (fun k (hk : k ∈ cls4 L w h A x₁ x₂) => hk.1)
  have hpp := pinned_mono hp0 (fun k (hk : k ∈ cls4 L w h A x₁ x₂) => hA.1 hk.1)
  have hst := uStep4_node (L := L) (w := w) (A := A) hn
  have hc' : UCtx M₀ R' (fun k => k ∈ cls4 L w h A x₁ x₂) L w (post4 h v x₁ x₂) :=
    UCtx.step4 hκ hst hpp hcc
  have hap' : ApPos (post4 h v x₁ x₂).s := apPos_cutSt_beta h.s hap
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨⟨R', hR', hc'⟩, hap', fun k hk => hext k hk (hr k hk.1)⟩⟩, hlt, ?_⟩
  have hI : Inv R' h.s := hc.good.1
  have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
  have hLC' := LCtx.of_inv hc'.good.1 ⟨(post4 h v x₁ x₂).anc, hc'.anc⟩ hc'.rel
  have hcard : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c := by
    have := card_atoms_leL_of_uctx hS hR' hcc
    exact le_trans (by exact_mod_cast this) hnc
  exact UStep4.dev_pot H hst hI (apProd_pos hL hap) P hP0 (LCtx.hPinh hP hLC hLC') c hcard

/-- **Phase 4 cover theorem.** -/
theorem phase4_coverL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 : Set (D₀ → (Fin d → ℤ))} (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hext : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (v : V) (x₁ x₂ : h.s.D), Node4 h v x₁ x₂ →
      ∀ k ∈ cls4 L w h A x₁ x₂, Rch k h → Rch k (post4 h v x₁ x₂)) (N : ℕ)
    (hN : 2 * M₀.atoms.card * Fintype.card D₀ * Fintype.card D₀ + 1 ≤ N) (W : HSt V D₀ → ℝ≥0∞)
    (hW : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀) (R' : ℕ), Inv3L M₀ Rn Rch L w A0 A h →
      ApPos h.s → Good R' h.s → (∃ k, k ∈ A) →
      UStep4 L w (fun k => k ∈ A) h h' →
      (N : ℝ≥0∞) * (ENNReal.ofReal (cBeta η c * stepRHS L γ η h h') * W h') ≤ W h)
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv3L M₀ Rn Rch L w A0 A h →
      (∀ k ∈ A, NoBetaCut L w k h.s) → (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn Rch L w A0 A h → QS L γ δ C₁ w P h A ≤ W h := by
  refine cover_induction2 (ι := ℕ) (fun a b : HSt V D₀ => epsCount a.s < epsCount b.s)
    (InvImage.wf (fun h : HSt V D₀ => epsCount h.s) wellFounded_lt)
    (fun h A => Inv3L M₀ Rn Rch L w A0 A h) (fun h A => ∀ k ∈ A, NoBetaCut L w k h.s) (QS L γ δ C₁ w P) W N
    (by omega) (fun h A B hAB => QS_mono L γ δ C₁ w P h hAB) (fun h A B => QS_union L γ δ C₁ w P h A B)
    (fun h => QS_empty L γ δ C₁ w P h) (fun h A => hfin A h) ?_
  intro h A hA _
  let Afin : Set (D₀ → (Fin d → ℤ)) := {k | k ∈ A ∧ NoBetaCut L w k h.s}
  have hAfin : Inv3L M₀ Rn Rch L w A0 Afin h := hA.mono fun k hk => hk.1
  by_cases hAe : A = ∅
  · refine ⟨Afin, ∅, fun _ => ∅, fun _ => h, fun _ => 0, hAfin, fun k hk => hk.2, ?_, (by simp; omega), (by simp)⟩
    intro k hk; rw [hAe] at hk; exact absurd hk (by simp)
  obtain ⟨R', hR', hc⟩ := (hA.2.resolve_left hAe).1
  have hapP : ApPos h.s := (hA.2.resolve_left hAe).2.1
  have hcard : (nodes4 h).card ≤ 2 * M₀.atoms.card * Fintype.card D₀ * Fintype.card D₀ := by
    refine (nodes4_card h).trans ?_
    have h1 := card_atoms_leL_of_uctx hS hR' hc
    have h2 : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
    exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h2
  have hmem : ∀ j t, nodeAt4 h j = some t → t ∈ nodes4 h := by
    intro j t ht
    unfold nodeAt4 at ht
    split_ifs at ht with hj
    · cases ht; exact ((nodes4 h).equivFin.symm ⟨j, hj⟩).2
  have hsurj : ∀ t ∈ nodes4 h, ∃ j, nodeAt4 h j = some t := by
    intro t ht
    refine ⟨((nodes4 h).equivFin ⟨t, ht⟩).1, ?_⟩
    unfold nodeAt4
    rw [dif_pos ((nodes4 h).equivFin ⟨t, ht⟩).2]
    simp
  refine ⟨Afin, Finset.range (nodes4 h).card, clsAt4 L w h A, postAt4 h, fun j => (match nodeAt4 h j with | some t => if cls4 L w h A t.2.1 t.2.2 = ∅ then 0 else ENNReal.ofReal (cBeta η c * stepRHS L γ η h (post4 h t.1 t.2.1 t.2.2)) | none => 0), hAfin, fun k hk => hk.2, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hnb : NoBetaCut L w k h.s
    · exact Or.inl ⟨hk, hnb⟩
    · right
      have hI := hc.good.1
      unfold NoBetaCut at hnb
      push Not at hnb
      obtain ⟨v, hv, hdeg, v₂, x₁, x₂, hcd, hnz, hnα⟩ := hnb
      have hε : h.s.cls v = .eps := by
        by_contra hne
        have := (hI.ab v hv hne).1
        omega
      have hcd' : h.s.M.IsCutData v (fresh h) x₁ x₂ :=
        ⟨hcd.1, fresh_notMem h, hcd.2.2.1, hcd.2.2.2.1, hcd.2.2.2.2.1, hcd.2.2.2.2.2.1, hcd.2.2.2.2.2.2⟩
      have hnα' : ¬ h.s.M.IsAlphaCut v (fresh h) x₁ x₂ := fun hα =>
        hnα ((isAlphaCut_congr h.s.M x₁ x₂ hcd.2.1 (fresh_notMem h)).2 hα)
      have hnd : Node4 h v x₁ x₂ := ⟨hcd', hε, hnα', hdeg⟩
      have hmt : (v, x₁, x₂) ∈ nodes4 h :=
        Finset.mem_filter.2 ⟨by simp [hv], hnd⟩
      obtain ⟨j, hj⟩ := hsurj _ hmt
      have hjS : j ∈ Finset.range (nodes4 h).card := by
        have := hmem j _ hj
        unfold nodeAt4 at hj
        by_contra hnot
        rw [dif_neg (by simpa using hnot)] at hj
        cases hj
      refine Set.mem_iUnion₂.2 ⟨j, hjS, ?_⟩
      unfold clsAt4
      rw [hj]
      exact ⟨hk, hnz⟩
  · simp only [Finset.card_range]; omega
  · intro j hjS
    have hj : j < (nodes4 h).card := Finset.mem_range.1 hjS
    obtain ⟨t, ht⟩ : ∃ t, nodeAt4 h j = some t := ⟨_, by unfold nodeAt4; rw [dif_pos hj]⟩
    have htm := hmem j t ht
    have hnd : Node4 h t.1 t.2.1 t.2.2 := (Finset.mem_filter.1 htm).2
    obtain ⟨h1, h2, h3⟩ := node4_factsL H hS hp0 hP hP0 c hnc hA hnd (hext A h _ _ _ hnd)
    have hcls : clsAt4 L w h A j = cls4 L w h A t.2.1 t.2.2 := by unfold clsAt4; rw [ht]
    have hpost : postAt4 h j = post4 h t.1 t.2.1 t.2.2 := by unfold postAt4; rw [ht]
    by_cases hce : cls4 L w h A t.2.1 t.2.2 = ∅
    · rw [hce] at h1
      simp only [hcls, hpost, ht, hce, if_true, QS_empty]
      exact ⟨h2, h1, by simp, by simp⟩
    · simp only [hcls, hpost, ht, hce, if_false]
      obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hce
      exact ⟨h2, h1, h3, hW _ h _ R' (hA.mono fun k hk => hk.1) hapP hc.good ⟨κ, hκ⟩ (uStep4_node hnd)⟩

end WaveTurbulence.FinalCountAsm
