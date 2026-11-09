/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase2F
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.BankEngine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.ChainSpec
/-! **Ghost assembly, Phase 2 (G): the Phase-2 cover with the bank** (design: `CHAIN-DESIGN.md`).

`phase2_bank_cover`: main's `phase2_cover` (H port, `H/FinalCount/AsmPhase2d.lean`) without `h8 : 8η ≤ 2γ - 1`:
for every class `A` of the phase invariant and every bank `b ≥ bank h A`,
`QS h A ≤ W h · L^{5η b}`, given the potential step for a charged triangle step
`(splitK·N) · (9·25^d·ghostConstLow·stepRHS h h') · W h' ≤ W h` and the terminal bound. The engine is
`cover_induction_split` on states `(h, b)`; a node is split by the (f′) classes `σ` (`node2_bank`), the child's bank is
its actual bank, and the transfer `L^{5η(ν-k)}` is absorbed by the banks (`bank h' + ν ≤ b + k`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The class of the child `(j, σ)` of a Phase-2 step (empty off the nodes). -/
noncomputable def clsAtS [Infinite V] {M₀ : Molecule V D₀} (C : H.CollData M₀) (L γ η : ℝ) (w : Mom d)
    (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (j : ℕ) (σ : Sig) : Set (D₀ → (Fin d → ℤ)) :=
  match H.nodeAt2 C L γ η h j with
  | some t => if hn : Node2 L γ η h t then nodeSplit L γ η w h A hn σ else ∅
  | none => ∅

theorem rpow_bank_le {L η : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η) {x y : ℝ} (hxy : x ≤ y) :
    L ^ (5 * η * x) ≤ L ^ (5 * η * y) :=
  Real.rpow_le_rpow_of_exponent_le hL (by nlinarith)

/-- **The Phase-2 cover with the bank.** -/
theorem phase2_bank_cover [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop}
    {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : H.CollData M₀}
    (HR : TriReal d L γ η δ C₁) (hS : SubHyp Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hRA : ∀ κ h, Rch κ h → Relation.ReflTransGen (H.HAny L γ η w κ) (HSt.init M₀) h)
    (hext : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (n : T2 h), Node2 L γ η h n →
      (∀ j : Fin 3, H.Desig C (h.anc (n.1 j)) (h.s.pr (n.2.1 j) (n.2.2.1 j))) → ∀ k ∈ cls2 L γ η w h A n, Rch k h →
        Rch k (post2 L γ η h n))
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h2 : 2 / L ≤ L ^ (-γ + η)) (N : ℕ)
    (hN : nodeBound2 (2 * M₀.atoms.card) (Fintype.card D₀) ⌈2 * Real.log L⌉₊ + 1 ≤ N) (W : HSt V D₀ → ℝ≥0∞)
    (hW : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀), Inv3 M₀ Rn Rch L w A0 A h →
      ApPos h.s → Inv Rn h.s → UStep2 L γ η w (fun k => k ∈ A) h h' →
      ((splitK * N : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (9 * 25 ^ d * ghostConstLow d c η δ * stepRHS L γ η h h') * W h') ≤ W h)
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv3 M₀ Rn Rch L w A0 A h →
      (∀ k ∈ A, H.NoEligibleTriangle C L γ η w k h) → (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (b : ℕ), Inv3 M₀ Rn Rch L w A0 A h →
      bank L γ η w h A ≤ b → QS L γ δ C₁ w P h A ≤ W h * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
  have hηγ : η ≤ γ := by have := HR.hη; have := HR.hη1; linarith
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) HR.hL
  have hL : 0 < L := by linarith
  have hη0 : 0 ≤ η := HR.hη.le
  have hN1 : 1 ≤ N := by omega
  have hK1 : 1 ≤ splitK := by unfold splitK; omega
  have hge1 : ∀ b : ℕ, (1 : ℝ≥0∞) ≤ ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := fun b => by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow hL1 (by positivity))
  suffices key : ∀ (hb : HSt V D₀ × ℕ) (A : Set (D₀ → (Fin d → ℤ))),
      (Inv3 M₀ Rn Rch L w A0 A hb.1 ∧ bank L γ η w hb.1 A ≤ hb.2) →
        QS L γ δ C₁ w P hb.1 A ≤ W hb.1 * ENNReal.ofReal (L ^ (5 * η * (hb.2 : ℝ))) by
    intro h A b hA hb
    exact key (h, b) A ⟨hA, hb⟩
  refine cover_induction_split (ι := ℕ × Sig) (fun a b : HSt V D₀ × ℕ => Fintype.card a.1.s.D < Fintype.card b.1.s.D)
    (InvImage.wf (fun hb : HSt V D₀ × ℕ => Fintype.card hb.1.s.D) wellFounded_lt)
    (fun hb A => Inv3 M₀ Rn Rch L w A0 A hb.1 ∧ bank L γ η w hb.1 A ≤ hb.2)
    (fun hb A => ∀ k ∈ A, H.NoEligibleTriangle C L γ η w k hb.1)
    (fun hb A => QS L γ δ C₁ w P hb.1 A) (fun hb => W hb.1 * ENNReal.ofReal (L ^ (5 * η * (hb.2 : ℝ)))) N splitK
    hN1 hK1 (fun hb A B hAB => QS_mono L γ δ C₁ w P hb.1 hAB) (fun hb A B => QS_union L γ δ C₁ w P hb.1 A B)
    (fun hb => QS_empty L γ δ C₁ w P hb.1) ?_ ?_
  · rintro ⟨h, b⟩ A ⟨hA, -⟩ hf
    calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h := hfin A h hA hf
      _ = W h * 1 := (mul_one _).symm
      _ ≤ W h * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by gcongr; exact hge1 b
  rintro ⟨h, b⟩ A ⟨hA, hbank⟩ _
  let Afin : Set (D₀ → (Fin d → ℤ)) := {k | k ∈ A ∧ H.NoEligibleTriangle C L γ η w k h}
  have hAfin : Inv3 M₀ Rn Rch L w A0 Afin h := hA.mono fun k hk => hk.1
  have hbfin : bank L γ η w h Afin ≤ b := (bank_mono fun k hk => hk.1).trans hbank
  by_cases hAe : A = ∅
  · refine ⟨Afin, ∅, fun _ => ∅, fun _ => (h, b), fun _ => 0, ⟨hAfin, hbfin⟩, fun k hk => hk.2, ?_,
      (by simpa using Nat.le_mul_of_pos_right splitK (by omega : 0 < N)), (by simp)⟩
    intro k hk; rw [hAe] at hk; exact absurd hk (by simp)
  have hc := (hA.2.resolve_left hAe).1
  have hapP : ApPos h.s := (hA.2.resolve_left hAe).2.1
  have hcardA : h.s.M.atoms.card ≤ 2 * M₀.atoms.card := UCtx.card_atoms_le hS hc
  have hcardD : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
  have hcard : (H.nodes2D C L γ η h).card ≤ nodeBound2 (2 * M₀.atoms.card) (Fintype.card D₀) ⌈2 * Real.log L⌉₊ := by
    refine (Finset.card_filter_le _ _).trans ((nodes2_card L γ η h).trans ?_)
    unfold nodeBound2
    gcongr
  have hmem : ∀ j t, H.nodeAt2 C L γ η h j = some t → t ∈ H.nodes2D C L γ η h := by
    intro j t ht
    unfold H.nodeAt2 at ht
    split_ifs at ht with hj
    · cases ht; exact ((H.nodes2D C L γ η h).equivFin.symm ⟨j, hj⟩).2
  have hsurj : ∀ t ∈ H.nodes2D C L γ η h, ∃ j, H.nodeAt2 C L γ η h j = some t := by
    intro t ht
    refine ⟨((H.nodes2D C L γ η h).equivFin ⟨t, ht⟩).1, ?_⟩
    unfold H.nodeAt2
    rw [dif_pos ((H.nodes2D C L γ η h).equivFin ⟨t, ht⟩).2]
    simp
  have hnode : ∀ t ∈ H.nodes2D C L γ η h, Node2 L γ η h t ∧
      ∀ j : Fin 3, H.Desig C (h.anc (t.1 j)) (h.s.pr (t.2.1 j) (t.2.2.1 j)) := fun t ht =>
    ⟨(Finset.mem_filter.1 (Finset.mem_filter.1 ht).1).2, (Finset.mem_filter.1 ht).2⟩
  let S : Finset (ℕ × Sig) := (Finset.range (H.nodes2D C L γ η h).card) ×ˢ Finset.univ
  let post : ℕ × Sig → HSt V D₀ × ℕ := fun js =>
    (H.postAt2 C L γ η h js.1, bank L γ η w (H.postAt2 C L γ η h js.1) (clsAtS C L γ η w h A js.1 js.2))
  let cost : ℕ × Sig → ℝ≥0∞ := fun js =>
    ENNReal.ofReal (9 * 25 ^ d * ghostConstLow d c η δ * stepRHS L γ η h (H.postAt2 C L γ η h js.1) *
      L ^ (5 * η * ((b : ℝ) - (post js).2)))
  refine ⟨Afin, S, fun js => clsAtS C L γ η w h A js.1 js.2, post, cost, ⟨hAfin, hbfin⟩, fun k hk => hk.2, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hnb : H.NoEligibleTriangle C L γ η w k h
    · exact Or.inl ⟨hk, hnb⟩
    · right
      obtain ⟨t, htn, hdt, hkt⟩ := H.phase2_cover_mem hS h0 hRA HR.hL hηγ h2 hA hAe hk hnb
      have ht : t ∈ H.nodes2D C L γ η h :=
        Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨node2_mem_box HR.hL hηγ htn, htn⟩, hdt⟩
      obtain ⟨j, hj⟩ := hsurj t ht
      obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 (split_cover h (triOf htn) (Q2 t) (kp2 t) (triOf_cl htn) (w := w) (γ := γ)
        hL (cls2 L γ η w h A t) hkt)
      have hjS : (j, σ) ∈ S := by
        refine Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩
        unfold H.nodeAt2 at hj
        by_contra hnot
        rw [dif_neg (by simpa using hnot)] at hj
        cases hj
      refine Set.mem_iUnion₂.2 ⟨(j, σ), hjS, ?_⟩
      show k ∈ clsAtS C L γ η w h A j σ
      unfold clsAtS
      rw [hj]; dsimp only
      rw [dif_pos htn]
      exact hσ
  · have hS' : S.card = (H.nodes2D C L γ η h).card * splitK := by
      simp only [S, Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      unfold splitK; ring
    rw [hS']
    have : (H.nodes2D C L γ η h).card + 1 ≤ N := by omega
    nlinarith
  · rintro ⟨j, σ⟩ hjS
    have hj : j < (H.nodes2D C L γ η h).card := Finset.mem_range.1 (Finset.mem_product.1 hjS).1
    obtain ⟨t, ht⟩ : ∃ t, H.nodeAt2 C L γ η h j = some t := ⟨_, by unfold H.nodeAt2; rw [dif_pos hj]⟩
    obtain ⟨hnd, hdes⟩ := hnode t (hmem j t ht)
    have hcls : clsAtS C L γ η w h A j σ = nodeSplit L γ η w h A hnd σ := by
      unfold clsAtS; rw [ht]; dsimp only; rw [dif_pos hnd]
    have hpost : H.postAt2 C L γ η h j = post2 L γ η h t := by unfold H.postAt2; rw [ht]
    obtain ⟨hinv, hlt, ν, k, hνb, hbk, hdev⟩ := node2_bank HR hS hp0 hP hP0 c hnc hRA h0 hA hnd
      (hext A h t hnd hdes) hbank σ
    simp only [post, cost, hcls, hpost]
    refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
    · refine hdev.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      have hX : 0 ≤ 9 * 25 ^ d * ghostConstLow d c η δ * stepRHS L γ η h (post2 L γ η h t) := by
        have h1 := ghostConstLow_nonneg (d := d) (c := c) HR.hη HR.hδ0
        have h2 : 0 ≤ stepRHS L γ η h (post2 L γ η h t) := by
          unfold stepRHS
          have := apProd_pos (L := L) (γ := γ) (η := η) hL hapP
          have hap' : ApPos (post2 L γ η h t).s := by
            rw [post2_eq hnd]; exact apPos_triSt hapP _ _ _ (fun j => zpow_pos (by norm_num) _) _
          have := apProd_pos (L := L) (γ := γ) (η := η) hL hap'
          positivity
        positivity
      refine mul_le_mul_of_nonneg_left (rpow_bank_le hL1 hη0 ?_) hX
      have : ((ν : ℕ) : ℝ) + (bank L γ η w (post2 L γ η h t) (nodeSplit L γ η w h A hnd σ) : ℝ) ≤ (b : ℝ) + k := by
        exact_mod_cast (by rw [Nat.add_comm]; exact hbk : ν + bank L γ η w (post2 L γ η h t) (nodeSplit L γ η w h A hnd σ) ≤ b + k)
      linarith
    · have hW' := hW (cls2 L γ η w h A t) h (post2 L γ η h t) (hA.mono fun k hk => hk.1) hapP hc.good.1
        (uStep2_node (A := A) hnd)
      set bb := bank L γ η w (post2 L γ η h t) (nodeSplit L γ η w h A hnd σ)
      have hsplit : ENNReal.ofReal (9 * 25 ^ d * ghostConstLow d c η δ * stepRHS L γ η h (post2 L γ η h t) *
            L ^ (5 * η * ((b : ℝ) - bb))) * (W (post2 L γ η h t) * ENNReal.ofReal (L ^ (5 * η * (bb : ℝ)))) =
          (ENNReal.ofReal (9 * 25 ^ d * ghostConstLow d c η δ * stepRHS L γ η h (post2 L γ η h t)) *
            W (post2 L γ η h t)) * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
        have hX0 : 0 ≤ 9 * 25 ^ d * ghostConstLow d c η δ * stepRHS L γ η h (post2 L γ η h t) := by
          have h1 := ghostConstLow_nonneg (d := d) (c := c) HR.hη HR.hδ0
          have h2 : 0 ≤ stepRHS L γ η h (post2 L γ η h t) := by
            unfold stepRHS
            have := apProd_pos (L := L) (γ := γ) (η := η) hL hapP
            have hap' : ApPos (post2 L γ η h t).s := by
              rw [post2_eq hnd]; exact apPos_triSt hapP _ _ _ (fun j => zpow_pos (by norm_num) _) _
            have := apProd_pos (L := L) (γ := γ) (η := η) hL hap'
            positivity
          positivity
        have e : L ^ (5 * η * ((b : ℝ) - bb)) * L ^ (5 * η * (bb : ℝ)) = L ^ (5 * η * (b : ℝ)) := by
          rw [← Real.rpow_add hL]; congr 1; ring
        rw [ENNReal.ofReal_mul hX0, ← e, ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)]
        ring
      rw [hsplit, ← mul_assoc]
      exact mul_le_mul' hW' le_rfl

end WaveTurbulence.GammaLow.FinalCount.Ghost
