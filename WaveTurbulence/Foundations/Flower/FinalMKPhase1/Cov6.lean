/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Cov5
public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Pot1

/-! # C1b1 MK-PHASE1 (17): the coverage `HmemAtLE` and the phase-1 cover with survivors

`hmemAtLE_of_inputs : HmemAtLE …` (main's `hmemAtL_of_shape`, LowChain22, with survivors): at a state of the survivor
Step 1 that is not `Stuck1E` for the decoration `κ`,

* some `CollectedF` object is not dartless: a collected vine or D1 node (first the first-stage objects);
* else some survivor is not dartless: the survivor next in the removal order (the least index) gives a survivor vine,
  survivor D1 or **re-cut** node (`survNodeExists`);
* else every collected object and every survivor is gone and a triple cut is left: a triple node of class `AtripE`.

`phase1_coverLE_of_inputs`: `phase1_coverLE_g1E` with `hmem` discharged; the end-of-Step-1 bound `hfin` (phases
D3/2–4 at `Stuck1E` states, where `pendRC = 0`) is the remaining input, C1b2's. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **The coverage of the survivor Step 1** (the `hmem` input of `phase1_coverLE`). -/
def HmemAtLE [Infinite V] {m : ℕ} (M₀ : Molecule V D₀) (Rn : ℕ) (C : CollDataMK M₀)
    (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (Fst : Set (Object M₀)) (E : Fin m → Object M₀) (crit : V → Prop)
    (L γ η : ℝ) (w : Mom d) (A0 : Set (D₀ → (Fin d → ℤ))) : Prop :=
  ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h → ∀ κ ∈ A,
    ¬ Stuck1E C L γ η w Un E κ h →
    (∃ t ∈ nodes1 C.toCollData crit L γ η h, κ ∈ cls1 L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
        t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) ∨
    (∃ t ∈ nodesT C.toCollData L γ η h, κ ∈ cls3 L γ η w h (AtripE C Un E L γ η w h A)
        t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2) ∨
    (∃ t ∈ nodes1D C.toCollData crit h, κ ∈ cls1D L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2)
        t.1 t.2.1 t.2.2.1 t.2.2.2) ∨
    (∃ t ∈ nodesRC C.toCollData crit E L γ η h, κ ∈ cls1D L γ η w h (AvineS E Fst h A t.1 t.2.1 t.2.2.1 t.2.2.2)
        t.1 t.2.1 t.2.2.1 t.2.2.2)

/-- **C1b1 target: the coverage `HmemAtLE`** from the fields of `LowLoopClassHypsMK` (on a general molecule). -/
theorem hmemAtLE_of_inputs [Infinite V] {M₀ : Molecule V D₀} {m Rn : ℕ} {C : CollDataMK M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {crit : V → Prop}
    {L γ η : ℝ} {w : Mom d} {A0 : Set (D₀ → (Fin d → ℤ))}
    (hM₀ : M₀.IsMolecule) (hS : SubHypL Rn M₀) (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ) (hη : 0 < η)
    (h2 : 2 / L ≤ L ^ (-γ + η)) (hmate : ∀ κ ∈ A0, ∀ x, κ (M₀.mate x) = κ x)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Object M₀, CollectedF C (Un κ) L γ η w κ U → CollectedF C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hFst : ∀ κ ∈ A0, ∀ U ∈ Fst, CollectedF C (Un κ) L γ η w κ U)
    (hsgC : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → U.HasGapKind L γ η w κ .SG)
    (hdesC : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → HingeData C.toCollData U)
    (hsh : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → U.atoms.card = 3 ∨ ObjVine M₀ U)
    (hHC : HostConnMK M₀ C Un E L γ η w A0)
    (hcrit : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ a ∈ U.atoms, a ≠ U.upper → a ≠ U.lower → ¬ crit a)
    (hsd : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hobl : ∀ κ ∈ A0, SubproOblGMK C.toCollData E L γ η w κ)
    (hchain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1)
    (hshape : ∀ i, ObjVine M₀ (E i))
    (hcritE : ∀ i, ∀ a ∈ (E i).atoms, a ≠ (E i).upper → a ≠ (E i).lower → ¬ crit a) :
    HmemAtLE M₀ Rn C Un Fst E crit L γ η w A0 := by
  intro A h hA κ hκ hns
  have hAe : A ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨κ, hκ⟩
  have hr : Reach1LE C Un Fst E L γ η w κ h := (hA.2.resolve_left hAe).2.2 κ hκ
  have hκ0 : κ ∈ A0 := hA.1 hκ
  have hinv := (reach1LE_book hS (h0 κ hκ0) (hdisj κ hκ0) (hsd κ hκ0) hr).1
  have hv := collNodeExists (crit := crit) (Fst := Fst) hM₀ hS hLe hηγ hη h2 hmate h0 hsgC hdesC hdisj hsh hsd hHC hcrit
  unfold Stuck1E at hns
  by_cases hex : ∃ U, CollectedF C (Un κ) L γ η w κ U ∧ ¬ Dartless U h
  · obtain ⟨U₀, hU₀, hnd₀⟩ := hex
    have key : (∃ t ∈ nodes1 C.toCollData crit L γ η h, κ ∈ cls1 L γ η w h
          (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) ∨
        (∃ t ∈ nodes1D C.toCollData crit h, κ ∈ cls1D L γ η w h
          (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) := by
      by_cases hF : ∃ U ∈ Fst, ¬ Dartless U h
      · obtain ⟨U, hUF, hnd⟩ := hF
        exact hv A h hA κ hκ U (hFst κ hκ0 U hUF) ((hinv U (hFst κ hκ0 U hUF)).resolve_left hnd) hnd (Or.inl hUF)
      · push Not at hF
        exact hv A h hA κ hκ U₀ hU₀ ((hinv U₀ hU₀).resolve_left hnd₀) hnd₀ (Or.inr hF)
    rcases key with k | k
    · exact Or.inl k
    · exact Or.inr (Or.inr (Or.inl k))
  · push Not at hex
    by_cases hexE : ∃ i, ¬ Dartless (E i) h
    · set S : Finset (Fin m) := Finset.univ.filter fun i => ¬ Dartless (E i) h with hSdef
      have hSne : S.Nonempty := by
        obtain ⟨i, hi⟩ := hexE
        exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
      have hi : ¬ Dartless (E (S.min' hSne)) h := (Finset.mem_filter.1 (S.min'_mem hSne)).2
      have ho : SurvOrder Fst E (S.min' hSne) h := by
        refine ⟨fun U hU => hex U (hFst κ hκ0 U hU), fun j hj => ?_⟩
        by_contra hnd
        exact absurd (S.min'_le j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hnd⟩)) (not_le.2 hj)
      rcases survNodeExists hM₀ hS hLe hηγ hη h2 hmate h0 hdisj hsd hobl hchain hshape hcritE A h hA κ hκ _ hi ho
        with k | k | k
      · exact Or.inl k
      · exact Or.inr (Or.inr (Or.inl k))
      · exact Or.inr (Or.inr (Or.inr k))
    · push Not at hexE
      have hnt : ¬ NoTripleCut C.toCollData L γ η w κ h := fun hn => hns ⟨hn, hex, hexE⟩
      right; left
      exact hmem_tripleG hLe hηγ h2 (B := AtripE C Un E L γ η w h A) ⟨hκ, hex, hexE⟩ hnt

/-- **The phase-1 cover with survivors, coverage discharged**: `phase1_coverLE_g1E` with `hmem := hmemAtLE_of_inputs`.
The remaining input `hfin` is the bound at the end of Step 1 (`Stuck1E`), C1b2's phases D3/2–4 (there `pendRC = 0`,
`WPot_g1E_of_pend_zero`, and `hendAtLE_inv1` gives `F ≤ 2R - 1 + m`). -/
theorem phase1_coverLE_of_inputs [Infinite V] {M₀ : Molecule V D₀} {m Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {crit : V → Prop} {CA CN CD CR ν : ℝ}
    (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hExA : Ex1A L γ η δ C₁ w M₀ P CA) (hExN : Ex1N L γ η δ C₁ w M₀ P CN ν)
    (hExD : Ex1D L γ η δ C₁ w M₀ C.toCollData P CD ν) (hExR : Ex1RC L γ η δ C₁ w M₀ C.toCollData P CR ν)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h8 : 8 * η ≤ 2 * γ - 1) (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ (1 - γ)) (h2 : 2 / L ≤ L ^ (-γ + η))
    (hηγ : η ≤ γ) (hmate : ∀ κ ∈ A0, ∀ x, κ (M₀.mate x) = κ x)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Object M₀, CollectedF C (Un κ) L γ η w κ U → CollectedF C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hFst : ∀ κ ∈ A0, ∀ U ∈ Fst, CollectedF C (Un κ) L γ η w κ U)
    (hsgC : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → U.HasGapKind L γ η w κ .SG)
    (hdesC : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → HingeData C.toCollData U)
    (hsh : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → U.atoms.card = 3 ∨ ObjVine M₀ U)
    (hHC : HostConnMK M₀ C Un E L γ η w A0)
    (hcrit : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ a ∈ U.atoms, a ≠ U.upper → a ≠ U.lower → ¬ crit a)
    (hsd : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hobl : ∀ κ ∈ A0, SubproOblGMK C.toCollData E L γ η w κ)
    (hchain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1)
    (hshape : ∀ i, ObjVine M₀ (E i))
    (hcritE : ∀ i, ∀ a ∈ (E i).atoms, a ≠ (E i).upper → a ≠ (E i).lower → ¬ crit a)
    (N : ℕ)
    (hN : (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) + 1 ≤ N)
    {ε0 Fmax : ℝ} (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2)
    (hCA : 0 ≤ CA) (hCN : 0 ≤ CN) (hCD : 0 ≤ CD) (hCR : 0 ≤ CR)
    (hNC1 : (N : ℝ) * max CA CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    (hNCD : (N : ℝ) * CD ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    (hNCR : (N : ℝ) * CR ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    (hK3 : 0 ≤ max (cAlpha d γ η) (cBeta η c))
    (hNC3 : (N : ℝ) * max (cAlpha d γ η) (cBeta η c) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h →
      (∀ k ∈ A, Stuck1E C L γ η w Un E k h) →
      (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h :=
  phase1_coverLE_g1E H hS hp0 hP hP0 c hnc hExA hExN hExD hExR hν hSrc hdec h0 h8 hη40 hγ0 N hN Yp hYp0 hYpd hε0
    hCA hCN hCD hCR hNC1 hNCD hNCR hK3 hNC3
    (hmemAtLE_of_inputs hS.isMolecule hS (H.hL) hηγ H.hη h2 hmate h0 hdisj hFst hsgC hdesC hsh hHC hcrit hsd hobl
      hchain hshape hcritE) hfin

/-- At the end of Step 1 (`Stuck1E`) no re-cut is pending, so the budget is main's potential there
(`WPot_g1E_of_pend_zero`); this is how C1b2's `hfin` sees `g1`. -/
theorem pendRC_zero_of_stuck {M₀ : Molecule V D₀} {m : ℕ} {C : CollDataMK M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d}
    {κ : D₀ → (Fin d → ℤ)} {h : HSt V D₀} (hst : Stuck1E C L γ η w Un E κ h) : pendRC E h = 0 := by
  unfold pendRC
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ hi
  exact hi.1 (hst.2.2 i)

end WaveTurbulence.Flower.FinalMKPhase1
