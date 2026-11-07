/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain16
/-! **FINALCOUNT LOW-CHAIN, session 4 (1): Step D1 nodes without the outside-connectivity field, and the isolated pendant case.**

`VFactsDg` is `VFactsD1` without `hconn`.  `HconnOK h K` is the dropped field (outside connectivity of a three-atom `DoubleShape` object).
A D1 node whose cut has `HconnOK` is covered by `UStepD1.excess_new` (`node1Dg_factsL`).  A node whose cut does not (`PendQ`: the
pendant double-bond chain `a = x = b` with a joint of degree `2`) is the ONE open case; its per-step bound is the explicit named
proposition `PendantD1Bound` (ruling R70a/R71 pending). -/
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

/-- The outside-connectivity field of `VFactsD1` (needed for three-atom `DoubleShape` objects only). -/
def HconnOK (h : HSt V D₀) (K : VineCut h.s.M) : Prop :=
  ∀ K' : VineCut h.s.M, h.vinePostG K = h.vinePostG K' → Nonempty (DoubleShape K') →
    ∃ G : Finset h.s.D, (∀ z ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K' G

/-- `VFactsD1` without the outside-connectivity field. -/
structure VFactsDg {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (h : HSt V D₀) (K : VineCut h.s.M) : Prop where
  hu : h.s.cls K.C.upper = .eps
  hl : h.s.cls K.C.lower = .eps
  hd2 : h.s.M.deg K.C.upper = 2 ∨ h.s.M.deg K.C.lower = 2
  hdu : Desig C (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂)
  hdl : Desig C (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂)
  hcls : ∀ K' : VineCut h.s.M, h.vinePostG K = h.vinePostG K' → SingleVineVC K' ∨ Nonempty (DoubleShape K')
  hnl : ∀ x, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x)
  hloss : ladderLoss h.s.M (h.s.M.atoms.filter (fun a => a ∉ K.C.atoms)) ≤ 86
  hint : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a

theorem VFactsD1.toG {M₀ : Molecule V D₀} {C : CollData M₀} {crit : V → Prop} {h : HSt V D₀} {K : VineCut h.s.M}
    (F : VFactsD1 C crit h K) : VFactsDg C crit h K :=
  ⟨F.hu, F.hl, F.hd2, F.hdu, F.hdl, F.hcls, F.hnl, F.hloss, F.hint⟩

theorem VFactsDg.toD1 {M₀ : Molecule V D₀} {C : CollData M₀} {crit : V → Prop} {h : HSt V D₀} {K : VineCut h.s.M}
    (F : VFactsDg C crit h K) (hc : HconnOK h K) : VFactsD1 C crit h K :=
  ⟨F.hu, F.hl, F.hd2, F.hdu, F.hdl, F.hcls, hc, F.hnl, F.hloss, F.hint⟩

def Node1Dg [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (h : HSt V D₀) (t : T1D h) : Prop :=
  ∃ K : VineCut h.s.M, K.x₁ = t.1 ∧ K.x₂ = t.2.1 ∧ K.y₁ = t.2.2.1 ∧ K.y₂ = t.2.2.2 ∧ K.fa = fresh3 h 0 ∧ K.fb = fresh3 h 1 ∧
    VFactsDg C crit h K

noncomputable def nodes1Dg [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (h : HSt V D₀) : Finset (T1D h) :=
  (Finset.univ : Finset (T1D h)).filter fun t => Node1Dg C crit h t

theorem nodes1Dg_card [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (h : HSt V D₀) :
    (nodes1Dg C crit h).card ≤ Fintype.card h.s.D * (Fintype.card h.s.D * (Fintype.card h.s.D * Fintype.card h.s.D)) := by
  refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
  simp [Fintype.card_prod]

noncomputable def post1Dg [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (h : HSt V D₀) (t : T1D h) : HSt V D₀ :=
  if hn : Node1Dg C crit h t then h.vinePostG (Classical.choose hn) else h

theorem node1Dg_spec [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {crit : V → Prop} {h : HSt V D₀} {t : T1D h}
    (hn : Node1Dg C crit h t) : ∃ K : VineCut h.s.M, VFactsDg C crit h K ∧ post1Dg C crit h t = h.vinePostG K ∧
      K.x₁ = t.1 ∧ K.x₂ = t.2.1 ∧ K.y₁ = t.2.2.1 ∧ K.y₂ = t.2.2.2 ∧ K.fa = fresh3 h 0 ∧ K.fb = fresh3 h 1 := by
  have hspec := Classical.choose_spec hn
  obtain ⟨e1, e2, e3, e4, e5, e6, F⟩ := hspec
  refine ⟨Classical.choose hn, F, ?_, e1, e2, e3, e4, e5, e6⟩
  unfold post1Dg; rw [dif_pos hn]

/-- The pendant case: a D1 node whose cut does not satisfy the outside-connectivity field. -/
def PendQ [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (h : HSt V D₀) (t : T1D h) : Prop :=
  ∃ hn : Node1Dg C crit h t, ¬ HconnOK h (Classical.choose hn)

theorem hconn_of_not_pend [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {crit : V → Prop} {h : HSt V D₀} {t : T1D h}
    (hn : Node1Dg C crit h t) (hp : ¬ PendQ C crit h t) {K : VineCut h.s.M} (hK : post1Dg C crit h t = h.vinePostG K) :
    HconnOK h K := by
  have h1 : HconnOK h (Classical.choose hn) := by
    by_contra hh; exact hp ⟨hn, hh⟩
  have e : post1Dg C crit h t = h.vinePostG (Classical.choose hn) := by unfold post1Dg; rw [dif_pos hn]
  intro K' hK' hd
  exact h1 K' (by rw [← e, hK, hK']) hd

/-- The Step D1 on a class. -/
theorem uStepD1_nodeg [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {crit : V → Prop} {L γ η : ℝ} {w : Mom d} {h : HSt V D₀}
    {A : Set (D₀ → (Fin d → ℤ))} {t : T1D h} (hn : Node1Dg C crit h t) :
    UStepD1 C L γ η w (fun k => k ∈ cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) h (post1Dg C crit h t) := by
  obtain ⟨x₁, x₂, y₁, y₂⟩ := t
  obtain ⟨K, F, hK, e1, e2, e3, e4, -, -⟩ := node1Dg_spec hn
  simp only at e1 e2 e3 e4 hK ⊢
  rw [hK]
  subst e1 e2 e3 e4
  exact UStepD1.vine h K F.hu F.hl F.hd2 (fun k hk => hk.2.2) (fun k hk => hk.2.1) (vineCut_F_lt K F.hd2) F.hdu F.hdl

/-- `HStepD1` on a decoration of a D1 class. -/
theorem hstepD1_nodeg [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {crit : V → Prop} {L γ η : ℝ} {w : Mom d} {h : HSt V D₀}
    {A : Set (D₀ → (Fin d → ℤ))} {t : T1D h} (hn : Node1Dg C crit h t) {κ : D₀ → (Fin d → ℤ)}
    (hk : κ ∈ cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) : HStepD1 C L γ η w κ h (post1Dg C crit h t) :=
  (uStepD1_nodeg (A := A) hn).hstep hk

/-- The restricted Step 1 of the LOW run at a D1 node. -/
theorem hstep1RL_nodeg [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {crit : V → Prop} {L γ η : ℝ} {w : Mom d} {h : HSt V D₀}
    {A : Set (D₀ → (Fin d → ℤ))} {t : T1D h} (hn : Node1Dg C crit h t) {κ : D₀ → (Fin d → ℤ)}
    (hk : κ ∈ cls1D L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) :
    HStep1RL C Un Fst L γ η w κ h (post1Dg C crit h t) := by
  have hC := hstepD1_nodeg hn hk
  obtain ⟨hkA, -⟩ := hk
  obtain ⟨-, U, hU, hUK, hUD, hUJ, hord⟩ := hkA
  obtain ⟨x₁, x₂, y₁, y₂⟩ := t
  obtain ⟨K, F, hK, e1, e2, e3, e4, e5, e6⟩ := node1Dg_spec hn
  simp only at e1 e2 e3 e4 hK hUK hUD hUJ hC ⊢
  rw [hK] at hC ⊢
  have hUK' := hUK K e1 e2 e3 e4 e5 e6
  subst e1 e2 e3 e4
  exact HStep1RL.d1 h K hC U hU hUK' hUD hUJ hord

/-- **Per-node facts of phase 1 (D1 nodes).** -/
theorem node1Dg_factsL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {crit : V → Prop} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 A : Set (D₀ → (Fin d → ℤ))} {CD ν : ℝ} (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S)
    (hExD : Ex1D L γ η δ C₁ w M₀ C P CD ν)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    {h : HSt V D₀} (hA : Inv1L M₀ Rn C Un Fst L γ η w A0 A h) {t : T1D h} (hn : Node1Dg C crit h t)
    (hext : ∀ k ∈ cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2,
      Reach1L C Un Fst L γ η w k h → Reach1L C Un Fst L γ η w k (post1Dg C crit h t)) :
    Inv1L M₀ Rn C Un Fst L γ η w A0 (cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) (post1Dg C crit h t) ∧
    epsCount (post1Dg C crit h t).s < epsCount h.s ∧
    ((∀ K : VineCut h.s.M, post1Dg C crit h t = h.vinePostG K → HconnOK h K) →
    QS L γ δ C₁ w P h (cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) ≤
      ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2) *
        QS L γ δ C₁ w P (post1Dg C crit h t) (cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2)) := by
  set B := cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2 with hB
  have hsub : B ⊆ A := fun k hk => hk.1
  obtain ⟨K, F, hK, -, -, -, -, -, -⟩ := node1Dg_spec hn
  have hlt : epsCount (post1Dg C crit h t).s < epsCount h.s := by
    rw [hK]; exact epsCount_vineStG_lt h.s K F.hu
  by_cases hAe : B = ∅
  · refine ⟨⟨hsub.trans hA.1, Or.inl hAe⟩, hlt, ?_⟩
    intro _; rw [hAe, QS_empty]; exact bot_le
  rcases hA.2 with he | ⟨⟨R', hR', hc⟩, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hsub)) hAe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAe
  have hcc := uctx_mono hc (fun k (hk : k ∈ B) => hsub hk)
  have hpp := pinned_mono hp0 (fun k (hk : k ∈ B) => hA.1 (hsub hk))
  have hst := uStepD1_nodeg (L := L) (γ := γ) (η := η) (w := w) (A := A) hn
  obtain ⟨j, R'', hj1, hjR, hc'⟩ := UCtx.stepD1 hκ hst hpp hcc
  have hap' : ApPos (post1Dg C crit h t).s := by
    rw [hK]; exact apPos_vineStG h.s K hap
  have hr' : ∀ k ∈ B, Reach1L C Un Fst L γ η w k (post1Dg C crit h t) := fun k hk => hext k hk (hr k (hsub hk))
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨⟨R'', by omega, hc'⟩, hap', hr'⟩⟩, hlt, ?_⟩
  intro hcK
  have hI : Inv R' h.s := hc.good.1
  have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
  have hCB : CompBeta h.s := by
    obtain ⟨R₃, -, hIL⟩ := invL_reach1 hS (h0 κ (hA.1 (hsub hκ))) (hr κ (hsub hκ))
    exact hIL.comp
  have hMol : h.s.M.IsMolecule := isMolecule_of_compBeta hc.good hCB
  have hne : ∃ k0, (fun k => k ∈ B) k0 := ⟨κ, hκ⟩
  have hSrc' : ∀ k0, (fun k => k ∈ B) k0 → SourceLadderGaps M₀ L w P k0 := fun k hk => hSrc k (hA.1 (hsub hk))
  have hdec' := fun k (hk : (fun k => k ∈ B) k) => hdec k (hA.1 (hsub hk))
  have hνat : (h.s.M.atoms.card : ℝ) ≤ ν := by
    have := card_atoms_leL_of_uctx hS hR' hcc
    exact le_trans (by exact_mod_cast this) hν
  rw [hK] at hst ⊢
  have hMol0 : M₀.IsMolecule := hS.isMolecule
  obtain ⟨K', he, hdev0⟩ := hExD hP0 hP hMol0 (fun k => k ∈ B) hne hSrc' hdec' hst hLC hcc.atom hMol F.hnl hνat
  have hdev := hdev0 (F.hcls K' he) (fun hd => hcK K hK K' he hd)
  exact hdev


end WaveTurbulence.FinalCountAsm
