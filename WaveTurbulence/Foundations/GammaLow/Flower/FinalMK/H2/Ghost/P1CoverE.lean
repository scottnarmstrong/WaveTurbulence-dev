/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.Ghost.P1Bank
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKPhase1.Cover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.LowE
/-! **Ghost assembly for L8-H2 (D): the marked Phase-1 cover with the bank** (wt-l6ghost).

`phase1_bank_coverLE`: L8-H2's `phase1_coverLE` (`H2/FinalMKPhase1/Cover`, nodes `nodesAllLE`: vine, triple, Step D1,
re-cut) with the bank, on the weighted engine `cover_induction_wt` (`K = splitK`), as wt-l6ghost's LOW
`phase1_bank_coverL` (`FinalCount/Ghost/LowE`): vine and triple nodes split into the 9 classes `σ` (`node1_bankG`,
`nodeT_bankG`, children of weight `1`); Step D1 and re-cut nodes keep their class (post `h.vinePostGL K`, no critical atom,
`nodeGL_bank`; child `σ = (0,0)` of weight `splitK`, budget `1/N`; the other `σ` empty). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.Flower.H2.Ghost
open WaveTurbulence.GammaLow.FinalCount WaveTurbulence.GammaLow.Flower
open WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.GammaLow.FinalCount.Ghost

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The class of the child `(j, σ)` of a LOW Phase-1 step. -/
noncomputable def clsAt1SLE [Infinite V] {M₀ : Molecule V D₀} {m : ℕ} (C : CollDataMK M₀)
    (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀)) (E : Fin m → Src.Object Src.γL M₀)
    (crit : V → Prop) (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (j : ℕ) (σ : Sig1) :
    Set (D₀ → (Fin d → ℤ)) :=
  match nodeAtPLE C crit E L γ η h j with
  | some (Sum.inl (Sum.inl (Sum.inl t))) => if hn : FinalCount.H.Node1 C.toCollData crit L γ η h t then
      vineSplitG w (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1) hn σ else ∅
  | some (Sum.inl (Sum.inl (Sum.inr t))) => tripSplitG (L := L) (γ := γ) (η := η) w (AtripE C Un E L γ η w h A) t σ
  | some (Sum.inl (Sum.inr t)) => if σ = (0, 0) then
      cls1D L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2 else ∅
  | some (Sum.inr t) => if σ = (0, 0) then
      cls1D L γ η w h (AvineS E Fst h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2 else ∅
  | none => ∅

/-- The base cost of the node `j` of a LOW Phase-1 step. -/
noncomputable def baseAt1LE [Infinite V] {M₀ : Molecule V D₀} {m : ℕ} (C : CollDataMK M₀) (crit : V → Prop)
    (E : Fin m → Src.Object Src.γL M₀) (L γ η CA CN CD CR : ℝ) (c d' : ℕ) (h : HSt V D₀) (j : ℕ) : ℝ :=
  match nodeAtPLE C crit E L γ η h j with
  | some (Sum.inl (Sum.inl (Sum.inl t))) => 3 * 5 ^ d' * vCost L γ η CA CN h (FinalCount.H.post1 C.toCollData crit L γ η h t)
  | some (Sum.inl (Sum.inl (Sum.inr t))) => 3 * 5 ^ d' * max (cAlpha d' γ η) (cBeta η c) *
      stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)
  | some (Sum.inl (Sum.inr _)) => CD * excessRHS2 L γ η [] 1 2
  | some (Sum.inr _) => CR * excessRHS2 L γ η [] 1 2
  | none => 0

/-- The weight of the child `(j, σ)`. -/
noncomputable def wtAt1LE [Infinite V] {M₀ : Molecule V D₀} {m : ℕ} (C : CollDataMK M₀) (crit : V → Prop)
    (E : Fin m → Src.Object Src.γL M₀) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) (σ : Sig1) : ℕ :=
  match nodeAtPLE C crit E L γ η h j with
  | some (Sum.inl (Sum.inr _)) => if σ = (0, 0) then splitK else 0
  | some (Sum.inr _) => if σ = (0, 0) then splitK else 0
  | _ => 1

theorem sum_wtAt1LE_le [Infinite V] {M₀ : Molecule V D₀} {m : ℕ} (C : CollDataMK M₀) (crit : V → Prop)
    (E : Fin m → Src.Object Src.γL M₀) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) :
    ∑ σ : Sig1, wtAt1LE C crit E L γ η h j σ ≤ splitK := by
  unfold wtAt1LE
  cases hj : nodeAtPLE C crit E L γ η h j with
  | none => simp [splitK]
  | some t =>
    rcases t with ((t | t) | t) | t
    · simp [splitK]
    · simp [splitK]
    · simp
    · simp

/-- The deviation of an unsplit child: the bank does not grow, so `L^{5η(b - b')} ≥ 1`. -/
theorem unsplit_dev {L η : ℝ} (hL1 : 1 ≤ L) (hη0 : 0 ≤ η) {b bk : ℕ} (hbk : bk ≤ b) (a : ℝ) {x y : ℝ≥0∞}
    (h : x ≤ ENNReal.ofReal a * y) : x ≤ ENNReal.ofReal (a * L ^ (5 * η * ((b : ℝ) - (bk : ℝ)))) * y := by
  refine h.trans (mul_le_mul' ?_ le_rfl)
  have hge : (1 : ℝ) ≤ L ^ (5 * η * ((b : ℝ) - (bk : ℝ))) := by
    refine Real.one_le_rpow hL1 ?_
    have : (bk : ℝ) ≤ b := by exact_mod_cast hbk
    nlinarith
  have := ofReal_mul_mono_right (a := a) zero_le_one hge
  rwa [mul_one] at this

/-- The weight of an unsplit child (`splitK` units of `1/(splitK·N)`, i.e. the budget `1/N`). -/
theorem unsplit_weight {L η : ℝ} (hL : 0 < L) (N b bk : ℕ) {a : ℝ} {W W' : ℝ≥0∞}
    (hW : (N : ℝ≥0∞) * (ENNReal.ofReal a * W') ≤ W) :
    ((splitK * N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (a * L ^ (5 * η * ((b : ℝ) - (bk : ℝ)))) *
      (W' * ENNReal.ofReal (L ^ (5 * η * (bk : ℝ))))) ≤
      ((splitK : ℕ) : ℝ≥0∞) * (W * ENNReal.ofReal (L ^ (5 * η * (b : ℝ)))) := by
  have hw := child_weight (η := η) hL (N : ℝ≥0∞) b bk hW
  calc ((splitK * N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (a * L ^ (5 * η * ((b : ℝ) - (bk : ℝ)))) *
        (W' * ENNReal.ofReal (L ^ (5 * η * (bk : ℝ))))) =
      ((splitK : ℕ) : ℝ≥0∞) * ((N : ℝ≥0∞) * (ENNReal.ofReal (a * L ^ (5 * η * ((b : ℝ) - (bk : ℝ)))) *
        (W' * ENNReal.ofReal (L ^ (5 * η * (bk : ℝ)))))) := by push_cast; ring
    _ ≤ ((splitK : ℕ) : ℝ≥0∞) * (W * ENNReal.ofReal (L ^ (5 * η * (b : ℝ)))) := by gcongr

/-- **The marked Phase-1 cover with the bank.** -/
theorem phase1_bank_coverLE [Infinite V] {M₀ : Molecule V D₀} {m Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollDataMK M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
    {E : Fin m → Src.Object Src.γL M₀} {crit : V → Prop} {CA CN CD CR ν : ℝ}
    (HR : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hExA : FinalCount.H.Ex1A L γ η δ C₁ w M₀ P CA) (hExN : FinalCount.H.Ex1N L γ η δ C₁ w M₀ P CN ν)
    (hExD : FinalCount.H.Ex1D L γ η δ C₁ w M₀ C.toCollData P CD ν) (hExR : Ex1RC L γ η δ C₁ w M₀ C.toCollData P CR ν)
    (hExC : Ex1Cone L γ η δ C₁ w M₀ P CA)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (N : ℕ)
    (hN : (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) + 1 ≤ N)
    (W : HSt V D₀ → ℝ≥0∞)
    (hmem : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h → ∀ κ ∈ A,
      ¬ Stuck1E C L γ η w Un E κ h →
      (∃ t ∈ FinalCount.H.nodes1 C.toCollData crit L γ η h, κ ∈ cls1 L γ η w h
          (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) ∨
      (∃ t ∈ FinalCount.H.nodesT C.toCollData L γ η h, κ ∈ cls3 L γ η w h (AtripE C Un E L γ η w h A)
          t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2) ∨
      (∃ t ∈ FinalCount.H.nodes1D C.toCollData crit h, κ ∈ cls1D L γ η w h
          (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) ∨
      (∃ t ∈ nodesRC C.toCollData crit E L γ η h, κ ∈ cls1D L γ η w h (AvineS E Fst h A t.1 t.2.1 t.2.2.1 t.2.2.2)
          t.1 t.2.1 t.2.2.1 t.2.2.2))
    (hW1 : ∀ (h : HSt V D₀) (t : T1 h) (R' : ℕ), ApPos h.s → Good R' h.s → FinalCount.H.Node1 C.toCollData crit L γ η h t →
      ((splitK * N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (3 * 5 ^ d * vCost L γ η CA CN h
        (FinalCount.H.post1 C.toCollData crit L γ η h t)) * W (FinalCount.H.post1 C.toCollData crit L γ η h t)) ≤ W h)
    (hW1D : ∀ (h : HSt V D₀) (t : T1D h) (R' : ℕ), ApPos h.s → Good R' h.s → FinalCount.H.Node1D C.toCollData crit h t →
      (N : ℝ≥0∞) * (ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2) * W (FinalCount.H.post1D C.toCollData crit h t)) ≤ W h)
    (hW3 : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀) (R' : ℕ), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h →
      ApPos h.s → Good R' h.s → (∃ k, k ∈ A) → UStep3 L γ η w (fun k => k ∈ A) h h' →
      ((splitK * N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') *
        W h') ≤ W h)
    (hWRC : ∀ (h : HSt V D₀) (t : T1D h) (R' : ℕ), ApPos h.s → Good R' h.s → Node1RC C.toCollData crit E L γ η h t →
      (N : ℝ≥0∞) * (ENNReal.ofReal (CR * excessRHS2 L γ η [] 1 2) * W (post1RC C.toCollData crit E L γ η h t)) ≤ W h)
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (b : ℕ), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h →
      bank L γ η w h A ≤ b → (∀ k ∈ A, Stuck1E C L γ η w Un E k h) →
      (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h * ENNReal.ofReal (L ^ (5 * η * (b : ℝ)))) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (b : ℕ), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h →
      bank L γ η w h A ≤ b → QS L γ δ C₁ w P h A ≤ W h * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) HR.hL
  have hL : 0 < L := by linarith
  have hN1 : 1 ≤ N := by omega
  have hK1 : 1 ≤ splitK := by unfold splitK; omega
  have hIL : ∀ κ ∈ A0, ∀ h', Reach1LE C Un Fst E L γ η w κ h' → ∃ R'', R'' ≤ Rn ∧ InvL M₀ R'' L γ η w κ h' :=
    fun κ hκ h' hr => invL_reach1E hS (h0 κ hκ) hr
  suffices key : ∀ (hb : HSt V D₀ × ℕ) (A : Set (D₀ → (Fin d → ℤ))),
      (Inv1LE M₀ Rn C Un Fst E L γ η w A0 A hb.1 ∧ bank L γ η w hb.1 A ≤ hb.2) →
        QS L γ δ C₁ w P hb.1 A ≤ W hb.1 * ENNReal.ofReal (L ^ (5 * η * (hb.2 : ℝ))) by
    intro h A b hA hb
    exact key (h, b) A ⟨hA, hb⟩
  refine cover_induction_wt (ι := ℕ × Sig1) (fun a b : HSt V D₀ × ℕ => epsCount a.1.s < epsCount b.1.s)
    (InvImage.wf (fun hb : HSt V D₀ × ℕ => epsCount hb.1.s) wellFounded_lt)
    (fun hb A => Inv1LE M₀ Rn C Un Fst E L γ η w A0 A hb.1 ∧ bank L γ η w hb.1 A ≤ hb.2)
    (fun hb A => ∀ k ∈ A, Stuck1E C L γ η w Un E k hb.1)
    (fun hb A => QS L γ δ C₁ w P hb.1 A) (fun hb => W hb.1 * ENNReal.ofReal (L ^ (5 * η * (hb.2 : ℝ)))) N splitK
    hN1 hK1 (fun hb A B hAB => QS_mono L γ δ C₁ w P hb.1 hAB) (fun hb A B => QS_union L γ δ C₁ w P hb.1 A B)
    (fun hb => QS_empty L γ δ C₁ w P hb.1) ?_ ?_
  · rintro ⟨h, b⟩ A ⟨hA, hbA⟩ hf
    exact hfin A h b hA hbA hf
  rintro ⟨h, b⟩ A ⟨hA, hbank⟩ _
  let Afin : Set (D₀ → (Fin d → ℤ)) := {k | k ∈ A ∧ Stuck1E C L γ η w Un E k h}
  have hAfin : Inv1LE M₀ Rn C Un Fst E L γ η w A0 Afin h := hA.mono fun k hk => hk.1
  have hbfin : bank L γ η w h Afin ≤ b := (bank_mono fun k hk => hk.1).trans hbank
  by_cases hAe : A = ∅
  · refine ⟨Afin, ∅, fun _ => ∅, fun _ => (h, b), fun _ => 0, fun _ => 0, ⟨hAfin, hbfin⟩, fun k hk => hk.2, ?_,
      (by simpa using Nat.le_mul_of_pos_right splitK (by omega : 0 < N)), (by simp)⟩
    intro k hk; rw [hAe] at hk; exact absurd hk (by simp)
  obtain ⟨R', hR', hc⟩ := (hA.2.resolve_left hAe).1
  have hapP : ApPos h.s := (hA.2.resolve_left hAe).2.1
  have hRC : ∀ κ ∈ A0, Reach1LE C Un Fst E L γ η w κ h → CompBeta h.s := fun κ hκ hr =>
    (invL_reach1E hS (h0 κ hκ) hr).choose_spec.2.comp
  have hcardA : h.s.M.atoms.card ≤ 2 * M₀.atoms.card := card_atoms_leL_of_uctx hS hR' hc
  have hcardD : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
  have hcard : (nodesAllLE C crit E L γ η h).card ≤ (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        (Fintype.card D₀ * ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) := by
    unfold nodesAllLE
    rw [Finset.card_disjSum, Finset.card_disjSum, Finset.card_disjSum]
    refine add_le_add (add_le_add (add_le_add ((FinalCount.H.nodes1_card C.toCollData crit L γ η h).trans ?_)
      ((FinalCount.H.nodesT_card_le C.toCollData L γ η h).trans ((nodes3_card L γ η h).trans ?_)))
      ((FinalCount.H.nodes1D_card C.toCollData crit h).trans ?_)) ((nodesRC_card C.toCollData crit E L γ η h).trans ?_)
    · gcongr
    · gcongr
    · gcongr
    · gcongr
  have hmemN : ∀ j t, nodeAtPLE C crit E L γ η h j = some t → t ∈ nodesAllLE C crit E L γ η h := by
    intro j t ht
    unfold nodeAtPLE at ht
    split_ifs at ht with hj
    · cases ht; exact ((nodesAllLE C crit E L γ η h).equivFin.symm ⟨j, hj⟩).2
  have hsurj : ∀ t ∈ nodesAllLE C crit E L γ η h, ∃ j, nodeAtPLE C crit E L γ η h j = some t := by
    intro t ht
    refine ⟨((nodesAllLE C crit E L γ η h).equivFin ⟨t, ht⟩).1, ?_⟩
    unfold nodeAtPLE
    rw [dite_eq_left ((nodesAllLE C crit E L γ η h).equivFin ⟨t, ht⟩).2]
    simp
  have hjlt : ∀ j t, nodeAtPLE C crit E L γ η h j = some t → j < (nodesAllLE C crit E L γ η h).card := by
    intro j t hj
    unfold nodeAtPLE at hj
    by_contra hnot
    rw [dite_eq_right hnot] at hj
    cases hj
  let S : Finset (ℕ × Sig1) := (Finset.range (nodesAllLE C crit E L γ η h).card) ×ˢ Finset.univ
  let post : ℕ × Sig1 → HSt V D₀ × ℕ := fun js =>
    (postAtPLE C crit E L γ η h js.1,
      bank L γ η w (postAtPLE C crit E L γ η h js.1) (clsAt1SLE C Un Fst E crit L γ η w h A js.1 js.2))
  let cost : ℕ × Sig1 → ℝ≥0∞ := fun js =>
    if clsAt1SLE C Un Fst E crit L γ η w h A js.1 js.2 = ∅ then 0 else
      ENNReal.ofReal (baseAt1LE C crit E L γ η CA CN CD CR c d h js.1 * L ^ (5 * η * ((b : ℝ) - (post js).2)))
  refine ⟨Afin, S, fun js => clsAt1SLE C Un Fst E crit L γ η w h A js.1 js.2, post, cost,
    fun js => wtAt1LE C crit E L γ η h js.1 js.2, ⟨hAfin, hbfin⟩, fun k hk => hk.2, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hnb : Stuck1E C L γ η w Un E k h
    · exact Or.inl ⟨hk, hnb⟩
    · right
      rcases hmem A h hA k hk hnb with ⟨t, ht, hkt⟩ | ⟨t, ht, hkt⟩ | ⟨t, ht, hkt⟩ | ⟨t, ht, hkt⟩
      · have htm : Sum.inl (Sum.inl (Sum.inl t)) ∈ nodesAllLE C crit E L γ η h := by
          unfold nodesAllLE; simpa using ht
        obtain ⟨j, hj⟩ := hsurj _ htm
        have hn : FinalCount.H.Node1 C.toCollData crit L γ η h t := (Finset.mem_filter.1 ht).2
        obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 (split1_cover (h := h) (h' := h.vinePostL (vcut hn) (vR t) (vkp t))
          (X := vineSurv h (vcut hn) (vR t) (vkp t)) (w := w) (γ := γ) ![(vcut hn).fa, (vcut hn).fb]
          (fun k0 => pgap L w k0 (h.s.pr t.1 t.2.1)) hL _ hkt)
        refine Set.mem_iUnion₂.2 ⟨(j, σ), Finset.mem_product.2 ⟨Finset.mem_range.2 (hjlt j _ hj),
          Finset.mem_univ _⟩, ?_⟩
        show k ∈ clsAt1SLE C Un Fst E crit L γ η w h A j σ
        unfold clsAt1SLE
        rw [hj]; dsimp only
        rw [dite_eq_left hn]
        exact hσ
      · have htm : Sum.inl (Sum.inl (Sum.inr t)) ∈ nodesAllLE C crit E L γ η h := by
          unfold nodesAllLE; simpa using ht
        obtain ⟨j, hj⟩ := hsurj _ htm
        obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 (split1_cover (h := h) (h' := post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)
          (X := cutSurv h t.1 (fresh h) t.2.1 t.2.2.1 ((2 : ℝ) ^ t.2.2.2.1) (if t.2.2.2.2.1 then 50 else 0))
          (w := w) (γ := γ) ![t.1, fresh h] (fun k0 => pgap L w k0 (h.s.pr t.2.1 t.2.2.1)) hL _ hkt)
        refine Set.mem_iUnion₂.2 ⟨(j, σ), Finset.mem_product.2 ⟨Finset.mem_range.2 (hjlt j _ hj),
          Finset.mem_univ _⟩, ?_⟩
        show k ∈ clsAt1SLE C Un Fst E crit L γ η w h A j σ
        unfold clsAt1SLE
        rw [hj]
        exact hσ
      · have htm : Sum.inl (Sum.inr t) ∈ nodesAllLE C crit E L γ η h := by unfold nodesAllLE; simpa using ht
        obtain ⟨j, hj⟩ := hsurj _ htm
        refine Set.mem_iUnion₂.2 ⟨(j, (0, 0)), Finset.mem_product.2 ⟨Finset.mem_range.2 (hjlt j _ hj),
          Finset.mem_univ _⟩, ?_⟩
        show k ∈ clsAt1SLE C Un Fst E crit L γ η w h A j (0, 0)
        unfold clsAt1SLE
        rw [hj]; dsimp only
        rw [ite_eq_left rfl]
        exact hkt
      · have htm : Sum.inr t ∈ nodesAllLE C crit E L γ η h := by unfold nodesAllLE; simpa using ht
        obtain ⟨j, hj⟩ := hsurj _ htm
        refine Set.mem_iUnion₂.2 ⟨(j, (0, 0)), Finset.mem_product.2 ⟨Finset.mem_range.2 (hjlt j _ hj),
          Finset.mem_univ _⟩, ?_⟩
        show k ∈ clsAt1SLE C Un Fst E crit L γ η w h A j (0, 0)
        unfold clsAt1SLE
        rw [hj]; dsimp only
        rw [ite_eq_left rfl]
        exact hkt
  · have hsum : ∑ js ∈ S, wtAt1LE C crit E L γ η h js.1 js.2 ≤ (nodesAllLE C crit E L γ η h).card * splitK := by
      simp only [S]
      rw [Finset.sum_product]
      calc ∑ j ∈ Finset.range (nodesAllLE C crit E L γ η h).card, ∑ σ : Sig1, wtAt1LE C crit E L γ η h j σ
          ≤ ∑ j ∈ Finset.range (nodesAllLE C crit E L γ η h).card, splitK :=
            Finset.sum_le_sum fun j _ => sum_wtAt1LE_le C crit E L γ η h j
        _ = (nodesAllLE C crit E L γ η h).card * splitK := by simp
    have : (nodesAllLE C crit E L γ η h).card + 1 ≤ N := by omega
    have h2 : (nodesAllLE C crit E L γ η h).card * splitK + splitK ≤ splitK * N := by nlinarith
    exact le_trans (Nat.add_le_add_right hsum _) h2
  · rintro ⟨j, σ⟩ hjS
    have hj : j < (nodesAllLE C crit E L γ η h).card := Finset.mem_range.1 (Finset.mem_product.1 hjS).1
    obtain ⟨t, ht⟩ : ∃ t, nodeAtPLE C crit E L γ η h j = some t :=
      ⟨_, by unfold nodeAtPLE; rw [dite_eq_left hj]⟩
    have htm := hmemN j t ht
    unfold nodesAllLE at htm
    rcases t with ((t | t) | t) | t
    · -- a vine node
      have hn : FinalCount.H.Node1 C.toCollData crit L γ η h t := (Finset.mem_filter.1 (Finset.inl_mem_disjSum.1
        (Finset.inl_mem_disjSum.1 (Finset.inl_mem_disjSum.1 htm)))).2
      set A' := AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1 with hA'
      have hfacts : ∀ B, B ⊆ cls1 L γ η w h A' t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1
          t.2.2.2.2.2.2.2 → Inv3L M₀ Rn (Reach1LE C Un Fst E L γ η w) L w A0 B (FinalCount.H.post1 C.toCollData crit L γ η h t) ∧
          epsCount (FinalCount.H.post1 C.toCollData crit L γ η h t).s < epsCount h.s ∧
          QS L γ δ C₁ w P h B ≤ ENNReal.ofReal (vCost L γ η CA CN h (FinalCount.H.post1 C.toCollData crit L γ η h t)) *
            QS L γ δ C₁ w P (FinalCount.H.post1 C.toCollData crit L γ η h t) B := by
        intro B hB
        have hBA : B ⊆ A := fun k hk => AvineE_sub (hB hk).1
        have hself : cls1 L γ η w h B t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1
            t.2.2.2.2.2.2.2 = B := by
          ext k; exact ⟨fun hk => hk.1, fun hk => ⟨hk, (hB hk).2⟩⟩
        have := node1_factsG HR hS hp0 hExA hExN hν hSrc hdec (hA.mono hBA) hRC hn
          (fun k (hk : k ∈ cls1 L γ η w h B t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1
            t.2.2.2.2.2.2.2) hr => Reach1LE.ext hr (hstep1RLE_vine hn (hB hk.1)))
        rw [hself] at this
        exact this
      have hcls : clsAt1SLE C Un Fst E crit L γ η w h A j σ = vineSplitG w A' hn σ := by
        unfold clsAt1SLE; rw [ht]; dsimp only; rw [dite_eq_left hn]
      have hpost : postAtPLE C crit E L γ η h j = FinalCount.H.post1 C.toCollData crit L γ η h t := by
        unfold postAtPLE; rw [ht]
      have hbase : baseAt1LE C crit E L γ η CA CN CD CR c d h j =
          3 * 5 ^ d * vCost L γ η CA CN h (FinalCount.H.post1 C.toCollData crit L γ η h t) := by
        unfold baseAt1LE; rw [ht]
      have hwt : wtAt1LE C crit E L γ η h j σ = 1 := by unfold wtAt1LE; rw [ht]
      obtain ⟨hinv, hlt, hbk, hdev⟩ := node1_bankG HR hExC hSrc hdec hIL hA AvineE_sub hn hfacts hbank σ
      simp only [post, cost, hcls, hpost, hbase, hwt]
      by_cases hce : vineSplitG w A' hn σ = ∅
      · rw [ite_eq_left hce]
        refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
        · rw [hce, QS_empty]; exact bot_le
        · simp
      rw [ite_eq_right hce]
      refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
      · refine hdev.trans (mul_le_mul' (ofReal_mul_mono_right (Real.rpow_nonneg hL.le _) ?_) le_rfl)
        refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
        have : (bank L γ η w (FinalCount.H.post1 C.toCollData crit L γ η h t) (vineSplitG w A' hn σ) : ℝ) ≤
            (b : ℝ) + (k1Of σ : ℝ) := by exact_mod_cast hbk
        have hη0 : 0 ≤ η := HR.hη.le
        nlinarith
      · rw [Nat.cast_one, one_mul]
        exact child_weight hL _ b _ (hW1 h t R' hapP hc.good hn)
    · -- a triple node
      have hn' := Finset.inr_mem_disjSum.1 (Finset.inl_mem_disjSum.1 (Finset.inl_mem_disjSum.1 htm))
      have hn : FinalCount.H.NodeT C.toCollData L γ η h t :=
        ⟨(Finset.mem_filter.1 (Finset.mem_filter.1 hn').1).2, (Finset.mem_filter.1 hn').2⟩
      set A' := AtripE C Un E L γ η w h A with hA'
      have hfacts : ∀ B, B ⊆ cls3 L γ η w h A' t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 →
          Inv3L M₀ Rn (Reach1LE C Un Fst E L γ η w) L w A0 B (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) ∧
          epsCount (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1).s < epsCount h.s ∧
          QS L γ δ C₁ w P h B ≤ ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) *
            stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)) *
            QS L γ δ C₁ w P (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) B := by
        intro B hB
        have hBA : B ⊆ A := fun k hk => AtripE_sub (hB hk).1
        have hself : cls3 L γ η w h B t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 = B := by
          ext k; exact ⟨fun hk => hk.1, fun hk => ⟨hk, (hB hk).2⟩⟩
        have := node3_factsL HR hS hp0 hP hP0 c hnc (hA.mono hBA) hn.1
          (fun k (hk : k ∈ cls3 L γ η w h B t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2) hr =>
            Reach1LE.ext hr (hstep1RLE_trip (Fst := Fst) hn (hB hk.1)))
        rw [hself] at this
        exact this
      have hcls : clsAt1SLE C Un Fst E crit L γ η w h A j σ = tripSplitG (L := L) (γ := γ) (η := η) w A' t σ := by
        unfold clsAt1SLE; rw [ht]
      have hpost : postAtPLE C crit E L γ η h j = post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 := by
        unfold postAtPLE; rw [ht]
      have hbase : baseAt1LE C crit E L γ η CA CN CD CR c d h j = 3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) *
          stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) := by
        unfold baseAt1LE; rw [ht]
      have hwt : wtAt1LE C crit E L γ η h j σ = 1 := by unfold wtAt1LE; rw [ht]
      obtain ⟨hinv, hlt, hbk, hdev⟩ := nodeT_bankG HR hP hP0 c hIL hA AtripE_sub hn hfacts hbank σ
      simp only [post, cost, hcls, hpost, hbase, hwt]
      by_cases hce : tripSplitG (L := L) (γ := γ) (η := η) w A' t σ = ∅
      · rw [ite_eq_left hce]
        refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
        · rw [hce, QS_empty]; exact bot_le
        · simp
      obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hce
      rw [ite_eq_right hce]
      refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
      · refine hdev.trans (mul_le_mul' (ofReal_mul_mono_right (Real.rpow_nonneg hL.le _) ?_) le_rfl)
        refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
        have : (bank L γ η w (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)
            (tripSplitG (L := L) (γ := γ) (η := η) w A' t σ) : ℝ) ≤ (b : ℝ) + (k1Of σ : ℝ) := by
          exact_mod_cast hbk
        have hη0 : 0 ≤ η := HR.hη.le
        nlinarith
      · have hAt : Inv1LE M₀ Rn C Un Fst E L γ η w A0 A' h := hA.mono AtripE_sub
        rw [Nat.cast_one, one_mul]
        exact child_weight hL _ b _ (hW3 _ h _ R' (hAt.mono fun k hk => hk.1) hapP hc.good ⟨κ, hκ.1⟩
          (uStep3_node hn.1))
    · -- a Step D1 node
      have hn : FinalCount.H.Node1D C.toCollData crit h t :=
        (Finset.mem_filter.1 (Finset.inr_mem_disjSum.1 (Finset.inl_mem_disjSum.1 htm))).2
      have hpost : postAtPLE C crit E L γ η h j = FinalCount.H.post1D C.toCollData crit h t := by
        unfold postAtPLE; rw [ht]
      have hbase : baseAt1LE C crit E L γ η CA CN CD CR c d h j = CD * excessRHS2 L γ η [] 1 2 := by
        unfold baseAt1LE; rw [ht]
      obtain ⟨hinv, hlt, hdev⟩ := node1D_factsG hS hp0 hP hP0 hExD hν hSrc hdec (hA.mono AvineE_sub) hRC hn
        (fun k hk hr => Reach1LE.ext hr (hstep1RLE_D1 hn hk))
      obtain ⟨K, -, hK, -⟩ := FinalCount.H.node1D_spec hn
      have hbk : bank L γ η w (FinalCount.H.post1D C.toCollData crit h t) (cls1D L γ η w h
          (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) ≤ b :=
        nodeGL_bank K hK (fun k hk => AvineE_sub hk.1) hbank
      by_cases hσ : σ = (0, 0)
      · have hcls : clsAt1SLE C Un Fst E crit L γ η w h A j σ = cls1D L γ η w h
            (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2 := by
          unfold clsAt1SLE; rw [ht]; dsimp only; rw [ite_eq_left hσ]
        have hwt : wtAt1LE C crit E L γ η h j σ = splitK := by
          unfold wtAt1LE; rw [ht]; dsimp only; rw [ite_eq_left hσ]
        simp only [post, cost, hcls, hpost, hbase, hwt]
        by_cases hce : cls1D L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2 = ∅
        · rw [ite_eq_left hce]
          refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
          · rw [hce, QS_empty]; exact bot_le
          · simp
        rw [ite_eq_right hce]
        exact ⟨hlt, ⟨hinv, le_rfl⟩, unsplit_dev hL1 HR.hη.le hbk _ hdev,
          unsplit_weight hL N b _ (hW1D h t R' hapP hc.good hn)⟩
      · have hcls : clsAt1SLE C Un Fst E crit L γ η w h A j σ = ∅ := by
          unfold clsAt1SLE; rw [ht]; dsimp only; rw [ite_eq_right hσ]
        have hwt : wtAt1LE C crit E L γ η h j σ = 0 := by
          unfold wtAt1LE; rw [ht]; dsimp only; rw [ite_eq_right hσ]
        simp only [post, cost, hcls, hpost, hwt, ite_true]
        refine ⟨hlt, ⟨⟨Set.empty_subset _, Or.inl rfl⟩, le_rfl⟩, ?_, ?_⟩
        · rw [QS_empty]; exact bot_le
        · simp
    · -- a re-cut node
      have hn : Node1RC C.toCollData crit E L γ η h t := (Finset.mem_filter.1 (Finset.inr_mem_disjSum.1 htm)).2
      have hpost : postAtPLE C crit E L γ η h j = post1RC C.toCollData crit E L γ η h t := by
        unfold postAtPLE; rw [ht]
      have hbase : baseAt1LE C crit E L γ η CA CN CD CR c d h j = CR * excessRHS2 L γ η [] 1 2 := by
        unfold baseAt1LE; rw [ht]
      obtain ⟨hinv, hlt, hdev⟩ := nodeRC_factsG hS hp0 hP hP0 hExR hν hSrc hdec (hA.mono AvineS_sub) hRC hn
        (fun k hk hr => Reach1LE.ext hr (hstep1RLE_RC (Un := Un) hn hk))
      obtain ⟨K, -, hK, -⟩ := nodeRC_spec hn
      have hbk : bank L γ η w (post1RC C.toCollData crit E L γ η h t) (cls1D L γ η w h
          (AvineS E Fst h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) ≤ b :=
        nodeGL_bank K hK (fun k hk => AvineS_sub hk.1) hbank
      by_cases hσ : σ = (0, 0)
      · have hcls : clsAt1SLE C Un Fst E crit L γ η w h A j σ = cls1D L γ η w h
            (AvineS E Fst h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2 := by
          unfold clsAt1SLE; rw [ht]; dsimp only; rw [ite_eq_left hσ]
        have hwt : wtAt1LE C crit E L γ η h j σ = splitK := by
          unfold wtAt1LE; rw [ht]; dsimp only; rw [ite_eq_left hσ]
        simp only [post, cost, hcls, hpost, hbase, hwt]
        by_cases hce : cls1D L γ η w h (AvineS E Fst h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2 = ∅
        · rw [ite_eq_left hce]
          refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
          · rw [hce, QS_empty]; exact bot_le
          · simp
        rw [ite_eq_right hce]
        exact ⟨hlt, ⟨hinv, le_rfl⟩, unsplit_dev hL1 HR.hη.le hbk _ hdev,
          unsplit_weight hL N b _ (hWRC h t R' hapP hc.good hn)⟩
      · have hcls : clsAt1SLE C Un Fst E crit L γ η w h A j σ = ∅ := by
          unfold clsAt1SLE; rw [ht]; dsimp only; rw [ite_eq_right hσ]
        have hwt : wtAt1LE C crit E L γ η h j σ = 0 := by
          unfold wtAt1LE; rw [ht]; dsimp only; rw [ite_eq_right hσ]
        simp only [post, cost, hcls, hpost, hwt, ite_true]
        refine ⟨hlt, ⟨⟨Set.empty_subset _, Or.inl rfl⟩, le_rfl⟩, ?_, ?_⟩
        · rw [QS_empty]; exact bot_le
        · simp

end WaveTurbulence.GammaLow.Flower.H2.Ghost
