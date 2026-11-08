/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKChain.Reach
public import WaveTurbulence.Foundations.FinalCount.LowChain10

/-! # C1b2 MK-CHAIN (2): phase 3 (SG cuts) after the survivor Step 1

Copy-thread of main's LowChain7 (`pair_of_sg`, `deg_three_of_sg`, `exists_step3C_L`), LowChain8 (`phase3_cover_memL`)
and LowChain9 (`phase3_coverL`). Two changes:
- the obligations enter only through `subpro` (5) at the hinges, C1a's `HingeSG` (`SubproOblG.hingeSG` and
  `SubproOblGMK.hingeSG` both give it); `hinge_orientedH` is main's `hinge_oriented` (AsmRun3) on it;
- the reach relation enters only through `RFacts` (the invariant `InvL` at an index `≤ Rn` and the D3 information
  `NoD3/AncRel/DartRel/EpsLe`), which main's `invL_reach3`/`Reach3L.d3info` supply for `Reach3L` and
  `invL_reach3E`/`Reach3LE.d3info` for the survivor run `Reach3LE`. -/

@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKChain
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.Flower.FinalMKPhase1 WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **The reach facts read by the phase-2/3 covers**: `InvL` at an index `≤ Rn`, and a state `h₂` after Step D3 (no
D3 cut left) with the ancestor/dart relations and `EpsLe h₂ h`. -/
def RFacts (M₀ : Molecule V D₀) (C : CollData M₀) (Rn : ℕ) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ))
    (h : HSt V D₀) : Prop :=
  (∃ R'', R'' ≤ Rn ∧ InvL M₀ R'' L γ η w κ h) ∧
    ∃ h₂, NoD3 C L w κ h₂ ∧ AncRel M₀ h₂.s h₂.anc ∧ DartRel M₀ h₂.s ∧ EpsLe h₂.s h.s

section rf
variable {M₀ : Molecule V D₀} {m : ℕ} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
  {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {Rn : ℕ}

theorem Reach2LE.rfacts (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach2LE C Un Fst E L γ η w κ h) : RFacts M₀ C.toCollData Rn L γ η w κ h :=
  ⟨invL_reach2E hS h0 hr, hr.d3info hS h0⟩

theorem Reach3LE.rfacts (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach3LE C Un Fst E L γ η w κ h) : RFacts M₀ C.toCollData Rn L γ η w κ h :=
  ⟨invL_reach3E hS h0 hr, hr.d3info hS h0⟩

end rf

section step3
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {M₀ : Molecule V D₀} {R : ℕ}

/-- The oriented designated pair of a hinge (main's `hinge_oriented`, AsmRun3, from `subpro` (5) only). -/
theorem hinge_orientedH {C : CollData M₀} (hH : HingeSG C L γ η w κ) {v : V} (hv : v ∈ C.hinges) :
    ∃ f s x y : D₀, C.first v = some f ∧ C.second v = some s ∧ M₀.atom x = v ∧ M₀.atom y = v ∧
      y ≠ M₀.mate x ∧ M₀.out x = false ∧ M₀.out y = true ∧
      Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .SG ∧ ({x, y} : Set D₀) = {f, s} := by
  obtain ⟨f, s, h1, h2, ⟨hf, hs, hfs, hout⟩, hsg⟩ := hH v hv
  cases hof : M₀.out f
  · have hos : M₀.out s = true := by
      cases h : M₀.out s
      · exact absurd (hof.trans h.symm) hout
      · rfl
    exact ⟨f, s, f, s, h1, h2, hf, hs, hfs, hof, hos, hsg, rfl⟩
  · have hos : M₀.out s = false := by
      cases h : M₀.out s
      · rfl
      · exact absurd (hof.trans h.symm) hout
    refine ⟨f, s, s, f, h1, h2, hs, hf, ?_, hos, hof, ?_, Set.pair_comm _ _⟩
    · intro e; apply hfs; rw [e, M₀.mate_mate]
    have hsw : Molecule.gapAt L w κ s f = -Molecule.gapAt L w κ f s := by
      unfold Molecule.gapAt; abel
    rw [hsw, gapKind_eq_of_norm_eq (L := L) (γ := γ) (η := η) (norm_neg (Molecule.gapAt L w κ f s))]
    exact hsg

/-- A pair of darts at an SG `ε`-atom of `M₀` that is designated at a hinge (main's `pair_of_sg`). -/
theorem pair_of_sgH {C : CollData M₀} (hH : HingeSG C L γ η w κ) {v : V} (hSG : SGat M₀ L γ η w κ v) :
    ∃ x y : D₀, M₀.atom x = v ∧ M₀.atom y = v ∧ y ≠ M₀.mate x ∧ M₀.out x = false ∧ M₀.out y = true ∧
      Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .SG ∧ Desig C v (x, y) := by
  by_cases hh : v ∈ C.hinges
  · obtain ⟨f, s, x, y, h1, h2, hx, hy, hne, ho1, ho2, hsg, hset⟩ := hinge_orientedH hH hh
    exact ⟨x, y, hx, hy, hne, ho1, ho2, hsg, fun _ => ⟨f, s, h1, h2, Or.inl hset⟩⟩
  · obtain ⟨x, y, hx, hy, ho1, ho2, hne, hsg⟩ := hSG
    exact ⟨x, y, hx, hy, hne, ho1, ho2, hsg, fun h' => absurd h' hh⟩

/-- **The degree of an SG `ε`-atom after Step D3 is complete** (main's `deg_three_of_sg`). -/
theorem deg_three_of_sgH {C : CollData M₀} (hH : HingeSG C L γ η w κ) {h₂ h : HSt V D₀}
    (hA₂ : AncRel M₀ h₂.s h₂.anc) (hD₂ : DartRel M₀ h₂.s) (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s)
    (hE : EpsLe h₂.s h.s) (hN : NoD3 C L w κ h₂) {v : V} (hv : v ∈ h.s.M.atoms) (hε : h.s.cls v = .eps)
    (hSG : SGat M₀ L γ η w κ v) : 3 ≤ h.s.M.deg v := by
  by_contra hlt
  obtain ⟨x, y, hx, hy, hne, hxo, hyo, hsg, hdes⟩ := pair_of_sgH hH hSG
  obtain ⟨x₁, hx₁d, hx₁a, hx₁o⟩ := eps_lift hA hD hv hε hx
  obtain ⟨x₂, hx₂d, hx₂a, hx₂o⟩ := eps_lift hA hD hv hε hy
  have hne' : x₂ ≠ h.s.M.mate x₁ := by
    intro e
    apply hne
    rw [← hx₂d, e, ← hD.mate, hx₁d]
  have hne12 : x₁ ≠ x₂ := by
    intro e; rw [e] at hx₁o; rw [hxo] at hx₁o; rw [hx₂o, hyo] at hx₁o; exact absurd hx₁o (by simp)
  have h2 := two_le_deg hx₁a hx₂a hne12
  have hD3 : D3Data h v x₁ x₂ :=
    { hv := hv, hε := hε, hd := by omega, hx₁ := hx₁a, hx₂ := hx₂a, hne := hne'
      ho₁ := by rw [hx₁o, hxo], ho₂ := by rw [hx₂o, hyo] }
  have key := noD3_transfer hA₂ hD₂ hA hD hE hN hD3
  have hpr : h.s.pr x₁ x₂ = (x, y) := by simp [St.pr, hx₁d, hx₂d]
  have hnz : pgap L w κ (h.s.pr x₁ x₂) ≠ 0 := by
    rw [hpr]; exact gap_ne_zero_of_SG hsg
  rw [hA.eps v hv hε, hpr] at key
  rcases key with k | k
  · exact hnz (by rw [hpr]; exact k)
  · exact k hdes

/-- **Step-3 existence in the LOW run** (main's `exists_step3C_L`, from `HingeSG`). -/
theorem exists_step3C_LH [Infinite V] {C : CollData M₀} (hH : HingeSG C L γ η w κ) (hL : 0 < L)
    (h2 : 2 / L ≤ L ^ (-γ + η)) {h : HSt V D₀} (hI : InvL M₀ R L γ η w κ h) (hA : AncRel M₀ h.s h.anc)
    {v : V} (hv : v ∈ h.s.M.atoms) (hε : h.s.cls v = .eps) (hSG : SGat M₀ L γ η w κ v)
    (h3 : 3 ≤ h.s.M.deg v) : ∃ h', HStep3C C L γ η w κ h h' := by
  have hD : DartRel M₀ h.s := hI.rel
  have hanc : h.anc v = v := hA.eps v hv hε
  obtain ⟨v₂, hv₂⟩ := Infinite.exists_notMem_finset h.s.M.atoms
  obtain ⟨x, y, hxv, hyv, hne, hxo, hyo, hsgxy, hdes⟩ : ∃ x y : D₀, M₀.atom x = v ∧ M₀.atom y = v ∧ y ≠ M₀.mate x ∧
      M₀.out x = false ∧ M₀.out y = true ∧ Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .SG ∧
      (v ∈ C.hinges → ∃ f s, C.first v = some f ∧ C.second v = some s ∧ ({x, y} : Set D₀) = {f, s}) := by
    by_cases hh : v ∈ C.hinges
    · obtain ⟨f, s, x, y, h1, h2, hx, hy, hne, ho1, ho2, hsg, hset⟩ := hinge_orientedH hH hh
      exact ⟨x, y, hx, hy, hne, ho1, ho2, hsg, fun _ => ⟨f, s, h1, h2, hset⟩⟩
    · obtain ⟨x, y, hx, hy, ho1, ho2, hne, hsg⟩ := hSG
      exact ⟨x, y, hx, hy, hne, ho1, ho2, hsg, fun h' => absurd h' hh⟩
  obtain ⟨x₁, hx₁d, hx₁a, hx₁o⟩ := eps_lift hA hD hv hε hxv
  obtain ⟨x₂, hx₂d, hx₂a, hx₂o⟩ := eps_lift hA hD hv hε hyv
  have hne' : x₂ ≠ h.s.M.mate x₁ := by
    intro e
    apply hne
    rw [← hx₂d, e, ← hD.mate, hx₁d]
  have hc : h.s.M.IsCutData v v₂ x₁ x₂ := ⟨hv, hv₂, hx₁a, hx₂a, hne', by simp [hx₁o, hxo], by simp [hx₂o, hyo]⟩
  have hsg' : Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) x₁ x₂) = .SG := by
    have : Molecule.gapAt L w (κ ∘ h.s.down) x₁ x₂ = Molecule.gapAt L w κ x y := by
      unfold Molecule.gapAt Molecule.kvec; simp [hx₁d, hx₂d]
    rw [this]; exact hsgxy
  obtain ⟨R', hR', hsim⟩ := exists_label_of_SG w (κ ∘ h.s.down) x₁ x₂ hL h2 hsg'
  by_cases hIo : IotaHit L η w κ h.alive (h.s.pr x₁ x₂) R'
  · refine ⟨_, HStep3C.cut h v v₂ x₁ x₂ hc R' 50 hR' (Or.inr rfl) hε hsg' hsim (by simp [hIo]) h3 ?_⟩
    intro hh
    rw [hanc] at hh
    obtain ⟨f, s, h1, h2', hset⟩ := hdes hh
    rw [hanc]
    refine ⟨f, s, h1, h2', Or.inl ?_⟩
    simpa [St.pr, hx₁d, hx₂d] using hset
  · refine ⟨_, HStep3C.cut h v v₂ x₁ x₂ hc R' 0 hR' (Or.inl rfl) hε hsg' hsim (by simp [hIo]) h3 ?_⟩
    intro hh
    rw [hanc] at hh
    obtain ⟨f, s, h1, h2', hset⟩ := hdes hh
    rw [hanc]
    refine ⟨f, s, h1, h2', Or.inl ?_⟩
    simpa [St.pr, hx₁d, hx₂d] using hset

end step3

/-- **A decoration that is not stuck lies in a node class** (phase 3; main's `phase3_cover_memL` with `HingeSG` and
`RFacts`). -/
theorem phase3_cover_memG [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop}
    {L γ η : ℝ} {w : Mom d} {A0 A : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀}
    (hH : ∀ κ ∈ A0, HingeSG C L γ η w κ)
    (hRI : ∀ κ ∈ A0, ∀ h, Rch κ h → RFacts M₀ C Rn L γ η w κ h)
    (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ) (h2 : 2 / L ≤ L ^ (-γ + η))
    {h : HSt V D₀} (hA : Inv3L M₀ Rn Rch L w A0 A h) (hAe : A ≠ ∅) {κ : D₀ → (Fin d → ℤ)} (hκ : κ ∈ A)
    (hnb : ¬ NoSGLeft L γ η w κ (HSt.init M₀).s h.s) :
    ∃ t ∈ nodes3 L γ η h, Desig C (h.anc t.1) (h.s.pr t.2.1 t.2.2.1) ∧
      κ ∈ cls3 L γ η w h A t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 := by
  obtain ⟨⟨R', hR', hc⟩, hap, hr⟩ := hA.2.resolve_left hAe
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  obtain ⟨⟨R'', -, hIL⟩, ⟨h₂, hN, hA₂, hD₂, hE⟩⟩ := hRI κ (hA.1 hκ) h (hr κ hκ)
  unfold NoSGLeft at hnb
  push Not at hnb
  obtain ⟨v, hv, hε, hSG⟩ := hnb
  have h3 : 3 ≤ h.s.M.deg v := deg_three_of_sgH (hH κ (hA.1 hκ)) hA₂ hD₂ hc.anc hIL.rel hE hN hv hε hSG
  obtain ⟨h', hs'⟩ := exists_step3C_LH (hH κ (hA.1 hκ)) hL h2 hIL hc.anc hv hε hSG h3
  cases hs' with
  | cut v' v₂ x₁ x₂ hcd R' kp hR hkp hε' hsg hsim hι h3 hdes =>
    obtain ⟨z, hRz, hz1, hz2⟩ := label_zrange hLe hηγ hR
    subst hRz
    have hcd' : h.s.M.IsCutData v' (fresh h) x₁ x₂ :=
      ⟨hcd.1, fresh_notMem h, hcd.2.2.1, hcd.2.2.2.1, hcd.2.2.2.2.1, hcd.2.2.2.2.2.1, hcd.2.2.2.2.2.2⟩
    by_cases hk50 : kp = 50
    · have hhit := hι.1 hk50
      obtain ⟨q, hq, ⟨a, ha, vis, hcr⟩, sg, hsgn, h1, h2'⟩ := iotaAlive_of_hit hhit
      refine ⟨(v', x₁, x₂, z, true, a, decide (sg = 1)), ?_, hdes, ?_⟩
      · refine Finset.mem_filter.2 ⟨?_, hcd', hε', h3, hR, ha, fun _ => ⟨q, vis, hcr, hq⟩⟩
        simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc]
        exact ⟨hcd.1, ⟨hz1, hz2⟩, ha, trivial⟩
      · have hq' : qOf h a (h.s.pr x₁ x₂) = q := by simp [qOf, hcr]
        have hsg' : (if decide (sg = 1) then (1 : ℝ) else -1) = sg := by
          rcases hsgn with rfl | rfl <;> norm_num
        refine ⟨hκ, hsg, hsim, fun _ => ?_, fun hb => by simp at hb⟩
        rw [hq', hsg']; exact ⟨h1, h2'⟩
    · have hk0 : ¬ IotaHit L η w κ h.alive (h.s.pr x₁ x₂) ((2 : ℝ) ^ z) := fun hh => hk50 (hι.2 hh)
      refine ⟨(v', x₁, x₂, z, false, v', true), ?_, hdes, ?_⟩
      · refine Finset.mem_filter.2 ⟨?_, hcd', hε', h3, hR, hcd.1, fun hb => by simp at hb⟩
        simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc]
        exact ⟨hcd.1, ⟨hz1, hz2⟩, hcd.1, trivial⟩
      · exact ⟨hκ, hsg, hsim, fun hb => by simp at hb, fun _ => hk0⟩

/-- **Phase 3 cover theorem** (main's `phase3_coverL` with `HingeSG` and `RFacts`). -/
theorem phase3_coverG [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop}
    {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hH : ∀ κ ∈ A0, HingeSG C L γ η w κ)
    (hRI : ∀ κ ∈ A0, ∀ h, Rch κ h → RFacts M₀ C Rn L γ η w κ h)
    (hext : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (v : V) (x₁ x₂ : h.s.D) (z : ℤ) (b : Bool) (a : V) (sg : Bool),
      Node3 L γ η h v x₁ x₂ z b a sg → Desig C (h.anc v) (h.s.pr x₁ x₂) → ∀ k ∈ cls3 L γ η w h A x₁ x₂ z b a sg,
        Rch k h → Rch k (post3 h v x₁ x₂ z b))
    (h2 : 2 / L ≤ L ^ (-γ + η)) (N : ℕ)
    (hN : (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
      ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) + 1 ≤ N) (W : HSt V D₀ → ℝ≥0∞)
    (hW : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀) (R' : ℕ), Inv3L M₀ Rn Rch L w A0 A h →
      ApPos h.s → Good R' h.s → (∃ k, k ∈ A) →
      UStep3 L γ η w (fun k => k ∈ A) h h' →
      (N : ℝ≥0∞) * (ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') * W h') ≤ W h)
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv3L M₀ Rn Rch L w A0 A h →
      (∀ k ∈ A, NoSGLeft L γ η w k (HSt.init M₀).s h.s) → (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn Rch L w A0 A h → QS L γ δ C₁ w P h A ≤ W h := by
  have hηγ : η ≤ γ := by have := H.hη; have := H.hη1; linarith
  refine cover_induction2 (ι := ℕ) (fun a b : HSt V D₀ => epsCount a.s < epsCount b.s)
    (InvImage.wf (fun h : HSt V D₀ => epsCount h.s) wellFounded_lt)
    (fun h A => Inv3L M₀ Rn Rch L w A0 A h) (fun h A => ∀ k ∈ A, NoSGLeft L γ η w k (HSt.init M₀).s h.s)
    (QS L γ δ C₁ w P) W N
    (by omega) (fun h A B hAB => QS_mono L γ δ C₁ w P h hAB) (fun h A B => QS_union L γ δ C₁ w P h A B)
    (fun h => QS_empty L γ δ C₁ w P h) (fun h A => hfin A h) ?_
  intro h A hA _
  let Afin : Set (D₀ → (Fin d → ℤ)) := {k | k ∈ A ∧ NoSGLeft L γ η w k (HSt.init M₀).s h.s}
  have hAfin : Inv3L M₀ Rn Rch L w A0 Afin h := hA.mono fun k hk => hk.1
  by_cases hAe : A = ∅
  · refine ⟨Afin, ∅, fun _ => ∅, fun _ => h, fun _ => 0, hAfin, fun k hk => hk.2, ?_, (by simp; omega), (by simp)⟩
    intro k hk; rw [hAe] at hk; exact absurd hk (by simp)
  obtain ⟨R', hR', hc⟩ := (hA.2.resolve_left hAe).1
  have hapP : ApPos h.s := (hA.2.resolve_left hAe).2.1
  have hcardA : h.s.M.atoms.card ≤ 2 * M₀.atoms.card := card_atoms_leL_of_uctx hS hR' hc
  have hcardD : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
  have hcard : (nodes3D C L γ η h).card ≤ (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
      ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) := by
    refine (Finset.card_filter_le _ _).trans ((nodes3_card L γ η h).trans ?_)
    gcongr
  have hmem : ∀ j t, nodeAt3 C L γ η h j = some t → t ∈ nodes3D C L γ η h := by
    intro j t ht
    unfold nodeAt3 at ht
    split_ifs at ht with hj
    · cases ht; exact ((nodes3D C L γ η h).equivFin.symm ⟨j, hj⟩).2
  have hsurj : ∀ t ∈ nodes3D C L γ η h, ∃ j, nodeAt3 C L γ η h j = some t := by
    intro t ht
    refine ⟨((nodes3D C L γ η h).equivFin ⟨t, ht⟩).1, ?_⟩
    unfold nodeAt3
    rw [dite_eq_left ((nodes3D C L γ η h).equivFin ⟨t, ht⟩).2]
    simp
  refine ⟨Afin, Finset.range (nodes3D C L γ η h).card, clsAt3 C L γ η w h A, postAt3 C L γ η h,
    (fun j => if clsAt3 C L γ η w h A j = ∅ then 0 else costAt3 C L γ η c d h j), hAfin,
    fun k hk => hk.2, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hnb : NoSGLeft L γ η w k (HSt.init M₀).s h.s
    · exact Or.inl ⟨hk, hnb⟩
    · right
      obtain ⟨t, ht, hdt, hkt⟩ := phase3_cover_memG hH hRI H.hL hηγ h2 hA hAe hk hnb
      have ht : t ∈ nodes3D C L γ η h := Finset.mem_filter.2 ⟨ht, hdt⟩
      obtain ⟨j, hj⟩ := hsurj t ht
      have hjS : j ∈ Finset.range (nodes3D C L γ η h).card := by
        unfold nodeAt3 at hj
        by_contra hnot
        rw [dite_eq_right (by simpa using hnot)] at hj
        cases hj
      refine Set.mem_iUnion₂.2 ⟨j, hjS, ?_⟩
      unfold clsAt3
      rw [hj]
      exact hkt
  · simp only [Finset.card_range]; omega
  · intro j hjS
    have hj : j < (nodes3D C L γ η h).card := Finset.mem_range.1 hjS
    obtain ⟨t, ht⟩ : ∃ t, nodeAt3 C L γ η h j = some t := ⟨_, by unfold nodeAt3; rw [dite_eq_left hj]⟩
    have htm := hmem j t ht
    have hnd : Node3 L γ η h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 htm).1).2
    have hdes := (Finset.mem_filter.1 htm).2
    obtain ⟨h1, h2', h3⟩ := node3_factsL H hS hp0 hP hP0 c hnc hA hnd (hext A h _ _ _ _ _ _ _ hnd hdes)
    have hcls : clsAt3 C L γ η w h A j =
        cls3 L γ η w h A t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 := by
      unfold clsAt3; rw [ht]
    have hpost : postAt3 C L γ η h j = post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 := by
      unfold postAt3; rw [ht]
    have hcost : costAt3 C L γ η c d h j = ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) *
        stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)) := by unfold costAt3; rw [ht]
    rw [hcls, hpost]
    by_cases hce : cls3 L γ η w h A t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 = ∅
    · rw [hce] at h1
      simp only [hcls, hce, ite_true, QS_empty]
      exact ⟨h2', h1, by simp, by simp⟩
    · simp only [hcls, hce, ite_false]
      obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hce
      rw [hcost]
      exact ⟨h2', h1, h3, hW _ h _ R' (hA.mono fun k hk => hk.1) hapP hc.good ⟨κ, hκ⟩ (uStep3_node hnd)⟩

end WaveTurbulence.Flower.FinalMKChain
