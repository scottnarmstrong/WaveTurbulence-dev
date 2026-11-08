/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Cover
public import WaveTurbulence.Foundations.FinalCount.LowChain29

/-! # C1b1 MK-PHASE1 (5): the phase-1 cover with the survivor budget `g1E`

The potential of phase 1 with survivors is `W h = N⁵ · WPot(Yp(R(h)), g1E, h)` with C1a's budget
`g1E = g1(Fmax) - pendRC` (`Fmax = 2R - 1 + m` at the end of Step 1, `HendAtLE`).

* `pendRC_anti`: no step of phase 1 creates a pending re-cut (darts are only removed: `dartless_vinePost(G)`,
  `dartless_ustep3`), so main's per-step inequalities `hW1_of`, `hW_D1'p`, `hW3_1` lift to `g1E` through C1a's
  `g1E_lift` (applied with the constant `Y·L^{pendRC h}`; for `hW_D1'p` with the scaled profile).
* `hWRCE`: the re-cut node, from C1a's `hW_RC'p_h8` and the node facts `hone`, `hpend` of `VFactsRC`.
* `phase1_coverLE_g1E`: `phase1_coverLE` with this potential; the remaining inputs are the coverage `hmem` and the
  final bound `hfin` at `Stuck1E` states (where `pendRC = 0` and `g1E = g1`, `WPot_g1E_of_pend_zero`). -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section dartless
variable {M₀ : Molecule V D₀} {m : ℕ}

/-- `pendRC` does not grow along a step that keeps every dartless survivor dartless. -/
theorem pendRC_anti (E : Fin m → Object M₀) {h h' : HSt V D₀} (hmono : ∀ k, Dartless (E k) h → Dartless (E k) h') :
    pendRC E h' ≤ pendRC E h := by
  unfold pendRC
  refine Finset.card_le_card ?_
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, fun hd => hk.2.1 (hmono k hd), hk.2.2⟩

theorem dartless_vinePost {U : Object M₀} {h : HSt V D₀} (K : VineCut h.s.M) (R : ℝ) (kp : ℕ) (hd : Dartless U h) :
    Dartless U (h.vinePost K R kp) := fun x hx => hd x.1 hx

theorem dartless_vinePostG {U : Object M₀} {h : HSt V D₀} (K : VineCut h.s.M) (hd : Dartless U h) :
    Dartless U (h.vinePostG K) := fun x hx => hd x.1 hx

theorem dartless_ustep3 {L γ η : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {U : Object M₀} {h h' : HSt V D₀}
    (hs : UStep3 L γ η w Adm0 h h') (hd : Dartless U h) : Dartless U h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι hι' h3 => exact fun x hx => hd x hx

end dartless

section pot
variable {M₀ : Molecule V D₀} {m : ℕ} {L γ η : ℝ} {C : CollData M₀} {E : Fin m → Object M₀}

theorem apPos_post1 [Infinite V] {crit : V → Prop} {h : HSt V D₀} {t : T1 h} (hap : ApPos h.s)
    (hn : Node1 C crit L γ η h t) : ApPos (post1 C crit L γ η h t).s := by
  obtain ⟨K, -, hK⟩ := node1_spec hn
  rw [hK, vinePost_s]
  refine apPos_vineSt hap K _ ?_
  intro R' kp' hc
  unfold alphaOrBeta at hc
  split_ifs at hc <;> cases hc <;> exact zpow_pos (by norm_num) _

/-- **Vine nodes with the survivor budget** (main's `hW1_of`, lifted by `g1E_lift`). -/
theorem hW1E [Infinite V] (hL1 : 1 ≤ L) (hη : 0 ≤ η) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R) (crit : V → Prop) (Fmax : ℝ)
    {CA CN : ℝ} (hCA : 0 ≤ CA) (hCN : 0 ≤ CN) (N : ℕ)
    (hNC : (N : ℝ) * max CA CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    {h : HSt V D₀} {t : T1 h} {R' : ℕ} (hap : ApPos h.s) (hg : Good R' h.s) (hn : Node1 C crit L γ η h t) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (vCost L γ η CA CN h (post1 C crit L γ η h t)) *
      WPot L γ η (Yp (RofS (post1 C crit L γ η h t).s)) (g1E γ η crit Fmax E) (post1 C crit L γ η h t)) ≤
      WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h := by
  have hL : 0 < L := by linarith
  have e : RofS (post1 C crit L γ η h t).s = RofS h.s := (rofS_post1 hg.1 hn).trans (rofS_of_inv hg.1).symm
  obtain ⟨K, -, hK⟩ := node1_spec hn
  have hap' : 0 < apProd L γ η (post1 C crit L γ η h t).s := apProd_pos hL (apPos_post1 hap hn)
  have hpend : pendRC E (post1 C crit L γ η h t) ≤ pendRC E h :=
    pendRC_anti E (fun k hd => by rw [hK]; exact dartless_vinePost K _ _ hd)
  rw [e]
  refine g1E_lift hL1 crit Fmax E (hYp0 _) hap' hpend N ?_
  exact hW1_of hL1 hη (by have := hYp0 (RofS h.s); positivity) crit Fmax hCA hCN N hNC hap hg.1 hn

/-- **D1 nodes with the survivor budget** (main's `hW_D1'p` on the scaled profile `Yp·L^{pendRC h}`). -/
theorem hW1DE [Infinite V] (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ (1 - γ)) (ε0 : ℝ)
    (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2)
    (crit : V → Prop) (Fmax : ℝ) {CD : ℝ} (hCD : 0 ≤ CD) (N : ℕ)
    (hNCD : (N : ℝ) * CD ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    {h : HSt V D₀} {t : T1D h} {R' : ℕ} (hap : ApPos h.s) (hg : Good R' h.s) (hn : Node1D C crit h t) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2) *
      WPot L γ η (Yp (RofS (post1D C crit h t).s)) (g1E γ η crit Fmax E) (post1D C crit h t)) ≤
      WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h := by
  have hL : 0 < L := by linarith
  obtain ⟨K, F, hK, -⟩ := node1D_spec hn
  have hap' : 0 < apProd L γ η (h.vinePostG K).s := apProd_pos hL (apPos_vineStG h.s K hap)
  have hpend : pendRC E (h.vinePostG K) ≤ pendRC E h := pendRC_anti E (fun k hd => dartless_vinePostG K hd)
  have hLp : 0 ≤ L ^ (pendRC E h : ℝ) := by positivity
  rw [hK]
  refine g1E_lift hL1 crit Fmax E (hYp0 _) hap' hpend N ?_
  exact hW_D1'p (L := L) (γ := γ) (η := η) hL1 hη hη40 hγ0 ε0 (fun R => Yp R * L ^ (pendRC E h : ℝ))
    (fun R => mul_nonneg (hYp0 R) hLp)
    (fun R R'' j e => by
      have := hYpd R R'' j e
      calc Yp R'' * L ^ (pendRC E h : ℝ) * L ^ (eraseA γ η * (j : ℝ) - ε0)
          = Yp R'' * L ^ (eraseA γ η * (j : ℝ) - ε0) * L ^ (pendRC E h : ℝ) := by ring
        _ ≤ Yp R * L ^ (pendRC E h : ℝ) := mul_le_mul_of_nonneg_right this hLp)
    hε0 crit Fmax K hg.1 hap F.hu F.hl F.hd2 (vineCut_F_lt K F.hd2) (vine_atoms_eps hg.1 K F.hu F.hl) F.hint
    (fun x hx => deg_le_four _ (hg.1.bounds x hx)) F.hloss hCD N hNCD

/-- **Triple cuts with the survivor budget** (main's `hW3_1`, lifted by `g1E_lift`). -/
theorem hW3E (hL1 : 1 ≤ L) (hη : 0 ≤ η) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R) (crit : V → Prop) (Fmax K : ℝ)
    (hγ0 : 0 ≤ min γ (1 - γ)) (hK : 0 ≤ K) (N : ℕ)
    (hNC : (N : ℝ) * K ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
    {w : Mom d} {A : Set (D₀ → (Fin d → ℤ))} {h h' : HSt V D₀} {R' : ℕ} (hap : ApPos h.s) (hg : Good R' h.s)
    (hne : ∃ k, k ∈ A) (hs : UStep3 L γ η w (fun k => k ∈ A) h h') :
    (N : ℝ≥0∞) * (ENNReal.ofReal (K * stepRHS L γ η h h') * WPot L γ η (Yp (RofS h'.s)) (g1E γ η crit Fmax E) h') ≤
      WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h := by
  have hL : 0 < L := by linarith
  have e : RofS h'.s = RofS h.s := (rofS_ustep3 hg hs hne).trans (rofS_of_inv hg.1).symm
  rw [e]
  refine g1E_lift hL1 crit Fmax E (hYp0 _) (apProd_pos hL (apPos_cut3 hs hap))
    (pendRC_anti E fun k hd => dartless_ustep3 hs hd) N ?_
  exact hW3_1 (Rn := R') hL1 hη (by have := hYp0 (RofS h.s); positivity) crit Fmax K hγ0 hK N hNC hap hg.1 hs

/-- **Re-cut nodes with the survivor budget** (C1a's `hW_RC'p_h8` with the node facts `hone`, `hpend`). -/
theorem hWRCE [Infinite V] (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ (1 - γ))
    (h8 : 8 * η ≤ 2 * γ - 1) (ε0 : ℝ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2)
    (crit : V → Prop) (Fmax : ℝ) {CR : ℝ} (hCR : 0 ≤ CR) (N : ℕ)
    (hNCR : (N : ℝ) * CR ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    {h : HSt V D₀} {t : T1D h} {R' : ℕ} (hap : ApPos h.s) (hg : Good R' h.s) (hn : Node1RC C crit E L γ η h t) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (CR * excessRHS2 L γ η [] 1 2) *
      WPot L γ η (Yp (RofS (post1RC C crit E L γ η h t).s)) (g1E γ η crit Fmax E) (post1RC C crit E L γ η h t)) ≤
      WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h := by
  obtain ⟨K, F, hK, -⟩ := nodeRC_spec hn
  rw [hK]
  exact hW_RC'p_h8 hL1 hη hη40 hγ0 h8 ε0 Yp hYp0 hYpd hε0 crit Fmax E K hg.1 hap F.hlab F.hu F.hl F.hrc F.hone
    F.hint (fun x hx => deg_le_four _ (hg.1.bounds x hx)) F.hloss F.hpend hCR N hNCR

end pot

/-- **The phase-1 cover with survivors and the survivor budget** (`phase1_coverLE` with
`W = N⁵ · WPot(Yp(R), g1E)`; main's phase-1 block of `chain_coverLL`). Inputs left open: the coverage `hmem`
(`HmemAtLE`, Cov6) and the end-of-Step-1 bound `hfin` (phases D3/2–4, C1b2). -/
theorem phase1_coverLE_g1E [Infinite V] {M₀ : Molecule V D₀} {m : ℕ} {Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {crit : V → Prop} {CA CN CD CR ν : ℝ}
    (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hExA : Ex1A L γ η δ C₁ w M₀ P CA) (hExN : Ex1N L γ η δ C₁ w M₀ P CN ν) (hExD : Ex1D L γ η δ C₁ w M₀ C.toCollData P CD ν)
    (hExR : Ex1RC L γ η δ C₁ w M₀ C.toCollData P CR ν)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h8 : 8 * η ≤ 2 * γ - 1) (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ (1 - γ))
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
    (hmem : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h → ∀ κ ∈ A,
      ¬ Stuck1E C L γ η w Un E κ h →
      (∃ t ∈ nodes1 C.toCollData crit L γ η h, κ ∈ cls1 L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) ∨
      (∃ t ∈ nodesT C.toCollData L γ η h, κ ∈ cls3 L γ η w h (AtripE C Un E L γ η w h A)
          t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2) ∨
      (∃ t ∈ nodes1D C.toCollData crit h, κ ∈ cls1D L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2)
          t.1 t.2.1 t.2.2.1 t.2.2.2) ∨
      (∃ t ∈ nodesRC C.toCollData crit E L γ η h, κ ∈ cls1D L γ η w h (AvineS E Fst h A t.1 t.2.1 t.2.2.1 t.2.2.2)
          t.1 t.2.1 t.2.2.1 t.2.2.2))
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h →
      (∀ k ∈ A, Stuck1E C L γ η w Un E k h) →
      (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) H.hL
  have hη0 : 0 ≤ η := H.hη.le
  refine phase1_coverLE H hS hp0 hP hP0 c hnc hExA hExN hExD hExR hν hSrc hdec h0 N hN
    (fun h => (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h) hmem ?_ ?_ ?_ ?_ hfin
  · intro h t R' hap hg hn
    exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 5)
      (hW1E hL1 hη0 Yp hYp0 crit Fmax hCA hCN N hNC1 hap hg hn)
  · intro h t R' hap hg hn
    exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 5)
      (hW1DE hL1 hη0 hη40 hγ0 ε0 Yp hYp0 hYpd hε0 crit Fmax hCD N hNCD hap hg hn)
  · intro A h h' R' _ hap hg hne hs
    exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 5)
      (hW3E hL1 hη0 Yp hYp0 crit Fmax _ hγ0 hK3 N hNC3 hap hg hne hs)
  · intro h t R' hap hg hn
    exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 5)
      (hWRCE hL1 hη0 hη40 hγ0 h8 ε0 Yp hYp0 hYpd hε0 crit Fmax hCR N hNCR hap hg hn)

end WaveTurbulence.Flower.FinalMKPhase1
