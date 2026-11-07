/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase2c
/-! **FINALCOUNT-ASSEMBLY, phase 2: the cover theorem** `phase2_cover` (copy of `phase3_cover` with triangle nodes). -/
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

/-- The box containing all nodes. -/
noncomputable def box2 (L : ℝ) (h : HSt V D₀) : Finset (T2 h) :=
  (Fintype.piFinset (fun _ : Fin 3 => h.s.M.atoms)) ×ˢ ((Finset.univ : Finset (Fin 3 → h.s.D)) ×ˢ
    ((Finset.univ : Finset (Fin 3 → h.s.D)) ×ˢ ((Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(⌈2 * Real.log L⌉₊ : ℤ)) 0)) ×ˢ
    ((Finset.univ : Finset (Fin 2 → Bool)) ×ˢ ((Fintype.piFinset (fun _ : Fin 2 => h.s.M.atoms)) ×ˢ
    ((Finset.univ : Finset (Fin 2 → Bool)) ×ˢ (Finset.univ : Finset Bool)))))))

noncomputable def nodes2 [Infinite V] (L γ η : ℝ) (h : HSt V D₀) : Finset (T2 h) := (box2 L h).filter (fun n => Node2 L γ η h n)

/-- The cardinality bound of the node box. -/
def nodeBound2 (A D Z : ℕ) : ℕ := A ^ 3 * (D ^ 3 * (D ^ 3 * ((Z + 1) ^ 2 * (4 * (A ^ 2 * (4 * 2))))))

theorem nodes2_card [Infinite V] (L γ η : ℝ) (h : HSt V D₀) :
    (nodes2 L γ η h).card ≤ nodeBound2 h.s.M.atoms.card (Fintype.card h.s.D) ⌈2 * Real.log L⌉₊ := by
  refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
  unfold box2 nodeBound2
  simp only [Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Int.card_Icc]
  have : (0 + 1 - -(⌈2 * Real.log L⌉₊ : ℤ)).toNat = ⌈2 * Real.log L⌉₊ + 1 := by omega
  rw [this]; ring

theorem node2_mem_box [Infinite V] {L γ η : ℝ} (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ) {h : HSt V D₀} {n : T2 h}
    (hn : Node2 L γ η h n) : n ∈ box2 L h := by
  obtain ⟨T, hcl, ht, ha, hb, hf, hlab, h3, hal, -⟩ := hn
  unfold box2
  simp only [Finset.mem_product, Finset.mem_univ, true_and, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, trivial⟩
  · rw [← ht]; exact T.t_mem j
  · obtain ⟨z, hz, h1, h2⟩ := label_zrange hLe hηγ (hlab j)
    have : (2 : ℝ) ^ n.2.2.2.1 j = (2 : ℝ) ^ z := hz
    have hzz : n.2.2.2.1 j = z := zpow_right_injective₀ (by norm_num) (by norm_num) this
    rw [hzz]; exact ⟨h1, h2⟩
  · exact hal j

/-- The phase-2 nodes whose triangle pairs are designated (`HStep2C`). -/
noncomputable def nodes2D [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (h : HSt V D₀) : Finset (T2 h) :=
  (nodes2 L γ η h).filter fun n => ∀ j : Fin 3, Desig C (h.anc (n.1 j)) (h.s.pr (n.2.1 j) (n.2.2.1 j))

noncomputable def nodeAt2 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) : Option (T2 h) :=
  if hj : j < (nodes2D C L γ η h).card then some (((nodes2D C L γ η h).equivFin.symm ⟨j, hj⟩ : nodes2D C L γ η h) : T2 h) else none

noncomputable def clsAt2 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (j : ℕ) :
    Set (D₀ → (Fin d → ℤ)) :=
  match nodeAt2 C L γ η h j with
  | some t => cls2 L γ η w h A t
  | none => ∅

noncomputable def postAt2 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) : HSt V D₀ :=
  match nodeAt2 C L γ η h j with
  | some t => post2 L γ η h t
  | none => h

noncomputable def costAt2 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (K : ℝ) (h : HSt V D₀) (j : ℕ) : ℝ≥0∞ :=
  match nodeAt2 C L γ η h j with
  | some t => ENNReal.ofReal (K * stepRHS L γ η h (post2 L γ η h t))
  | none => 0

/-- **Phase 2 cover theorem.** -/
theorem phase2_cover [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} (H : TriReal d L γ η δ C₁) (hS : SubHyp Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c) 
    (h8 : 8 * η ≤ 2 * γ - 1)
    (hRA : ∀ κ h, Rch κ h → Relation.ReflTransGen (HAny L γ η w κ) (HSt.init M₀) h)
    (hext : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (n : T2 h), Node2 L γ η h n →
      (∀ j : Fin 3, Desig C (h.anc (n.1 j)) (h.s.pr (n.2.1 j) (n.2.2.1 j))) → ∀ k ∈ cls2 L γ η w h A n, Rch k h →
        Rch k (post2 L γ η h n))
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h2 : 2 / L ≤ L ^ (-γ + η)) (N : ℕ)
    (hN : nodeBound2 (2 * M₀.atoms.card) (Fintype.card D₀) ⌈2 * Real.log L⌉₊ + 1 ≤ N) (W : HSt V D₀ → ℝ≥0∞)
    (hW : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀), Inv3 M₀ Rn Rch L w A0 A h →
      ApPos h.s → Inv Rn h.s →
      UStep2 L γ η w (fun k => k ∈ A) h h' →
      (N : ℝ≥0∞) * (ENNReal.ofReal (ghostConst d c η δ * stepRHS L γ η h h') * W h') ≤ W h)
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv3 M₀ Rn Rch L w A0 A h →
      (∀ k ∈ A, NoEligibleTriangle C L γ η w k h) → (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3 M₀ Rn Rch L w A0 A h → QS L γ δ C₁ w P h A ≤ W h := by
  have hηγ : η ≤ γ := by have := H.hη; have := H.hη1; linarith
  refine cover_induction2 (ι := ℕ) (fun a b : HSt V D₀ => Fintype.card a.s.D < Fintype.card b.s.D)
    (InvImage.wf (fun h : HSt V D₀ => Fintype.card h.s.D) wellFounded_lt)
    (fun h A => Inv3 M₀ Rn Rch L w A0 A h) (fun h A => ∀ k ∈ A, NoEligibleTriangle C L γ η w k h)
    (QS L γ δ C₁ w P) W N
    (by omega) (fun h A B hAB => QS_mono L γ δ C₁ w P h hAB) (fun h A B => QS_union L γ δ C₁ w P h A B)
    (fun h => QS_empty L γ δ C₁ w P h) (fun h A => hfin A h) ?_
  intro h A hA _
  let Afin : Set (D₀ → (Fin d → ℤ)) := {k | k ∈ A ∧ NoEligibleTriangle C L γ η w k h}
  have hAfin : Inv3 M₀ Rn Rch L w A0 Afin h := hA.mono fun k hk => hk.1
  by_cases hAe : A = ∅
  · refine ⟨Afin, ∅, fun _ => ∅, fun _ => h, fun _ => 0, hAfin, fun k hk => hk.2, ?_, (by simp; omega), (by simp)⟩
    intro k hk; rw [hAe] at hk; exact absurd hk (by simp)
  have hc : UCtx M₀ Rn (fun k => k ∈ A) L w h := (hA.2.resolve_left hAe).1
  have hapP : ApPos h.s := (hA.2.resolve_left hAe).2.1
  have hcardA : h.s.M.atoms.card ≤ 2 * M₀.atoms.card := UCtx.card_atoms_le hS hc
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
    costAt2 C L γ η (ghostConst d c η δ) h, hAfin, fun k hk => hk.2, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hnb : NoEligibleTriangle C L γ η w k h
    · exact Or.inl ⟨hk, hnb⟩
    · right
      obtain ⟨t, htn, hdt, hkt⟩ := phase2_cover_mem hS h0 hRA H.hL hηγ h2 hA hAe hk hnb
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
    obtain ⟨h1, h2', h3⟩ := node2_facts H hS hp0 hP hP0 c hnc hRA h8 h0 hA hnd (hext A h t hnd hdes)
    have hcls : clsAt2 C L γ η w h A j = cls2 L γ η w h A t := by unfold clsAt2; rw [ht]
    have hpost : postAt2 C L γ η h j = post2 L γ η h t := by unfold postAt2; rw [ht]
    have hcost : costAt2 C L γ η (ghostConst d c η δ) h j =
        ENNReal.ofReal (ghostConst d c η δ * stepRHS L γ η h (post2 L γ η h t)) := by unfold costAt2; rw [ht]
    rw [hcls, hpost, hcost]
    exact ⟨h2', h1, h3, hW _ h _ (hA.mono fun k hk => hk.1) hapP hc.good.1 (uStep2_node hnd)⟩

end WaveTurbulence.FinalCountAsm
