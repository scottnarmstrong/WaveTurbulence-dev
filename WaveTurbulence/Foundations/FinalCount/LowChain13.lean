/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain12
public import WaveTurbulence.Foundations.FinalCount.GL29
/-! **FINALCOUNT LOW-CHAIN, LC-2 (9): the Step D1 nodes of phase 1.**  A D1 node of `h` is the dart data `(x₁, x₂, y₁, y₂)` of a vine cut `K` with fresh names
`fresh3 h 0, 1` and the state-level facts `VFactsD1` (a joint of degree `2`); its class is `{κ | SG at the first pair, twin pairs}` (no label: the new halves are
deleted); the step is `UStepD1` (post state `h.vinePostG K`); `Ex1D` is the packaged `UStepD1.excess_new`. -/
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

theorem epsCount_vineStG_lt (s : St.{u} V D₀) (K : VineCut s.M) (hu : s.cls K.C.upper = .eps) :
    epsCount (vineStG s K) < epsCount s := by
  unfold epsCount
  have hsub : (vineStG s K).M.atoms.filter (fun a => (vineStG s K).cls a = .eps) ⊆
      (s.M.atoms.filter fun a => s.cls a = .eps).erase K.C.upper := by
    intro a ha
    obtain ⟨ham, hae⟩ := Finset.mem_filter.1 ha
    rw [vineStG_atoms] at ham
    obtain ⟨ham1, hk⟩ := Finset.mem_filter.1 ham
    by_cases hfa : a = K.fa
    · subst hfa; rw [vineStG_cls_fa] at hae; exact absurd hae (jcls_ne_eps _ _)
    by_cases hfb : a = K.fb
    · subst hfb; rw [vineStG_cls_fb] at hae; exact absurd hae (jcls_ne_eps _ _)
    have has : a ∈ s.M.atoms := by
      rcases Finset.mem_insert.1 ham1 with e | e
      · exact absurd e hfb
      · rcases Finset.mem_insert.1 e with e | e
        · exact absurd e hfa
        · exact e
    rw [vineStG_cls_old s K hk.1 has] at hae
    have hau : a ≠ K.C.upper := fun e => hk.1 (e ▸ K.a_mem)
    exact Finset.mem_erase.2 ⟨hau, Finset.mem_filter.2 ⟨has, hae⟩⟩
  refine lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem ?_)
  exact Finset.mem_filter.2 ⟨objectAtoms_sub K.C K.a_mem, hu⟩

/-- The ladder loss of removing a vine-like or double-shape object is at most `86` (the proof of `hrho_of_cls`). -/
theorem ladderLoss_le_86 {M : Molecule V D₀} (hMol : M.IsMolecule) (K : VineCut M) (hK : SingleVineVC K ∨ Nonempty (DoubleShape K)) :
    ladderLoss M (M.atoms.filter (fun a => a ∉ K.C.atoms)) ≤ 86 := by
  have hdeg : ∀ x ∈ M.atoms, M.deg x ≤ 4 := fun x hx => Mole.deg_le_four M hMol hx
  rcases hK with h | hS
  · unfold SingleVineVC at h
    split at h
    · obtain ⟨X, hX⟩ := h
      have h2 := WaveTurbulence.VineRho.vine_ladderLoss_le M hMol hX
      rw [sdiff_eq_filter_atoms] at h2
      omega
    · rename_i R hsh
      obtain ⟨X, hX⟩ := h
      have hHV : IsHV M K.C.atoms K.C.upper K.C.lower := ⟨R.added, R.ends_eq, X, hX⟩
      have h2 := WaveTurbulence.VineRho.hv_ladderLoss_le M hMol hHV
      rw [sdiff_eq_filter_atoms] at h2
      omega
  · obtain ⟨S⟩ := hS
    have h2 := ladderLoss_le_card M hdeg (M.atoms.filter (fun a => a ∉ K.C.atoms))
    have h3 : (M.atoms \ M.atoms.filter (fun a => a ∉ K.C.atoms)) ⊆ K.C.atoms := by
      intro a ha
      rw [Finset.mem_sdiff, Finset.mem_filter] at ha
      by_contra hc; exact ha.2 ⟨ha.1, hc⟩
    have := Finset.card_le_card h3
    have h4 : K.C.atoms.card ≤ 3 := by rw [S.atoms_eq]; exact Finset.card_le_three
    omega

/-- The state-level facts about a removed object `K` at a Step D1 node. -/
structure VFactsD1 {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (h : HSt V D₀) (K : VineCut h.s.M) : Prop where
  hu : h.s.cls K.C.upper = .eps
  hl : h.s.cls K.C.lower = .eps
  hd2 : h.s.M.deg K.C.upper = 2 ∨ h.s.M.deg K.C.lower = 2
  hdu : Desig C (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂)
  hdl : Desig C (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂)
  hcls : ∀ K' : VineCut h.s.M, h.vinePostG K = h.vinePostG K' → SingleVineVC K' ∨ Nonempty (DoubleShape K')
  hconn : ∀ K' : VineCut h.s.M, h.vinePostG K = h.vinePostG K' → Nonempty (DoubleShape K') →
    ∃ G : Finset h.s.D, (∀ z ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K' G
  hnl : ∀ x, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x)
  hloss : ladderLoss h.s.M (h.s.M.atoms.filter (fun a => a ∉ K.C.atoms)) ≤ 86
  hint : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a

abbrev T1D (h : HSt V D₀) := h.s.D × h.s.D × h.s.D × h.s.D

def Node1D [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (h : HSt V D₀) (t : T1D h) : Prop :=
  ∃ K : VineCut h.s.M, K.x₁ = t.1 ∧ K.x₂ = t.2.1 ∧ K.y₁ = t.2.2.1 ∧ K.y₂ = t.2.2.2 ∧ K.fa = fresh3 h 0 ∧ K.fb = fresh3 h 1 ∧
    VFactsD1 C crit h K

noncomputable def nodes1D [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (h : HSt V D₀) : Finset (T1D h) :=
  (Finset.univ : Finset (T1D h)).filter fun t => Node1D C crit h t

theorem nodes1D_card [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (h : HSt V D₀) :
    (nodes1D C crit h).card ≤ Fintype.card h.s.D * (Fintype.card h.s.D * (Fintype.card h.s.D * Fintype.card h.s.D)) := by
  refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
  simp [Fintype.card_prod]

/-- The class of a D1 node. -/
def cls1D (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (x₁ x₂ y₁ y₂ : h.s.D) : Set (D₀ → (Fin d → ℤ)) :=
  {k | k ∈ A ∧ Molecule.gapKind L γ η (Molecule.gapAt L w (k ∘ h.s.down) x₁ x₂) = .SG ∧
    (pgap L w k (h.s.pr y₁ y₂) = pgap L w k (h.s.pr x₁ x₂) ∨ pgap L w k (h.s.pr y₁ y₂) = -pgap L w k (h.s.pr x₁ x₂))}

noncomputable def post1D [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (h : HSt V D₀) (t : T1D h) : HSt V D₀ :=
  if hn : Node1D C crit h t then h.vinePostG (Classical.choose hn) else h

theorem node1D_spec [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {crit : V → Prop} {h : HSt V D₀} {t : T1D h}
    (hn : Node1D C crit h t) : ∃ K : VineCut h.s.M, VFactsD1 C crit h K ∧ post1D C crit h t = h.vinePostG K ∧
      K.x₁ = t.1 ∧ K.x₂ = t.2.1 ∧ K.y₁ = t.2.2.1 ∧ K.y₂ = t.2.2.2 ∧ K.fa = fresh3 h 0 ∧ K.fb = fresh3 h 1 := by
  have hspec := Classical.choose_spec hn
  obtain ⟨e1, e2, e3, e4, e5, e6, F⟩ := hspec
  refine ⟨Classical.choose hn, F, ?_, e1, e2, e3, e4, e5, e6⟩
  unfold post1D; rw [dif_pos hn]

/-- The Step D1 on a class. -/
theorem uStepD1_node [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {crit : V → Prop} {L γ η : ℝ} {w : Mom d} {h : HSt V D₀}
    {A : Set (D₀ → (Fin d → ℤ))} {t : T1D h} (hn : Node1D C crit h t) :
    UStepD1 C L γ η w (fun k => k ∈ cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) h (post1D C crit h t) := by
  obtain ⟨x₁, x₂, y₁, y₂⟩ := t
  obtain ⟨K, F, hK, e1, e2, e3, e4, -, -⟩ := node1D_spec hn
  simp only at e1 e2 e3 e4 hK ⊢
  rw [hK]
  subst e1 e2 e3 e4
  exact UStepD1.vine h K F.hu F.hl F.hd2 (fun k hk => hk.2.2) (fun k hk => hk.2.1) (vineCut_F_lt K F.hd2) F.hdu F.hdl

/-- `HStepD1` on a decoration of a D1 class. -/
theorem hstepD1_node [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {crit : V → Prop} {L γ η : ℝ} {w : Mom d} {h : HSt V D₀}
    {A : Set (D₀ → (Fin d → ℤ))} {t : T1D h} (hn : Node1D C crit h t) {κ : D₀ → (Fin d → ℤ)}
    (hk : κ ∈ cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) : HStepD1 C L γ η w κ h (post1D C crit h t) :=
  (uStepD1_node (A := A) hn).hstep hk

/-- The restricted Step 1 of the LOW run at a D1 node. -/
theorem hstep1RL_node [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {crit : V → Prop} {L γ η : ℝ} {w : Mom d} {h : HSt V D₀}
    {A : Set (D₀ → (Fin d → ℤ))} {t : T1D h} (hn : Node1D C crit h t) {κ : D₀ → (Fin d → ℤ)}
    (hk : κ ∈ cls1D L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) :
    HStep1RL C Un Fst L γ η w κ h (post1D C crit h t) := by
  have hC := hstepD1_node hn hk
  obtain ⟨hkA, -⟩ := hk
  obtain ⟨-, U, hU, hUK, hUD, hUJ, hord⟩ := hkA
  obtain ⟨x₁, x₂, y₁, y₂⟩ := t
  obtain ⟨K, F, hK, e1, e2, e3, e4, e5, e6⟩ := node1D_spec hn
  simp only at e1 e2 e3 e4 hK hUK hUD hUJ hC ⊢
  rw [hK] at hC ⊢
  have hUK' := hUK K e1 e2 e3 e4 e5 e6
  subst e1 e2 e3 e4
  exact HStep1RL.d1 h K hC U hU hUK' hUD hUJ hord

/-- `excessprop1 (3)` for Step D1, the statement of `UStepD1.excess_new` with the constant fixed. -/
def Ex1D (L γ η δ C₁ : ℝ) (w : Mom d) (M₀ : Molecule V D₀) (C : CollData M₀) (P : Finset V → ℝ) (CD ν : ℝ) : Prop :=
  (∀ S, 0 ≤ P S) → LadderHered M₀ P → M₀.IsMolecule →
  ∀ (Adm0 : (D₀ → (Fin d → ℤ)) → Prop), (∃ k0, Adm0 k0) → (∀ k0, Adm0 k0 → SourceLadderGaps M₀ L w P k0) →
    (∀ k0, Adm0 k0 → ∃ c0, M₀.IsDecoration L w c0 k0 ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0) →
    ∀ {h h' : HSt V D₀}, UStepD1 C L γ η w Adm0 h h' → LCtx M₀ h.s → AtomRelU Adm0 L w h → h.s.M.IsMolecule →
      (∀ x, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x)) → (h.s.M.atoms.card : ℝ) ≤ ν →
      ∃ (K : VineCut h.s.M), h' = h.vinePostG K ∧
        ((SingleVineVC K ∨ Nonempty (DoubleShape K)) →
        (Nonempty (DoubleShape K) →
          ∃ G : Finset h.s.D, (∀ z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K G) →
          IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P) (h'.s.M.countA L γ δ C₁ w (AdmS Adm0 h'.s) P)
            (ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2)))

/-- **Per-node facts of phase 1 (D1 nodes).** -/
theorem node1D_factsL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {crit : V → Prop} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 A : Set (D₀ → (Fin d → ℤ))} {CD ν : ℝ} (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S)
    (hExD : Ex1D L γ η δ C₁ w M₀ C P CD ν)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    {h : HSt V D₀} (hA : Inv1L M₀ Rn C Un Fst L γ η w A0 A h) {t : T1D h} (hn : Node1D C crit h t)
    (hext : ∀ k ∈ cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2,
      Reach1L C Un Fst L γ η w k h → Reach1L C Un Fst L γ η w k (post1D C crit h t)) :
    Inv1L M₀ Rn C Un Fst L γ η w A0 (cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) (post1D C crit h t) ∧
    epsCount (post1D C crit h t).s < epsCount h.s ∧
    QS L γ δ C₁ w P h (cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) ≤
      ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2) *
        QS L γ δ C₁ w P (post1D C crit h t) (cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  set B := cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2 with hB
  have hsub : B ⊆ A := fun k hk => hk.1
  obtain ⟨K, F, hK, -, -, -, -, -, -⟩ := node1D_spec hn
  have hlt : epsCount (post1D C crit h t).s < epsCount h.s := by
    rw [hK]; exact epsCount_vineStG_lt h.s K F.hu
  by_cases hAe : B = ∅
  · refine ⟨⟨hsub.trans hA.1, Or.inl hAe⟩, hlt, ?_⟩
    rw [hAe, QS_empty]; exact bot_le
  rcases hA.2 with he | ⟨⟨R', hR', hc⟩, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hsub)) hAe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAe
  have hcc := uctx_mono hc (fun k (hk : k ∈ B) => hsub hk)
  have hpp := pinned_mono hp0 (fun k (hk : k ∈ B) => hA.1 (hsub hk))
  have hst := uStepD1_node (L := L) (γ := γ) (η := η) (w := w) (A := A) hn
  obtain ⟨j, R'', hj1, hjR, hc'⟩ := UCtx.stepD1 hκ hst hpp hcc
  have hap' : ApPos (post1D C crit h t).s := by
    rw [hK]; exact apPos_vineStG h.s K hap
  have hr' : ∀ k ∈ B, Reach1L C Un Fst L γ η w k (post1D C crit h t) := fun k hk => hext k hk (hr k (hsub hk))
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨⟨R'', by omega, hc'⟩, hap', hr'⟩⟩, hlt, ?_⟩
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
  have hdev := hdev0 (F.hcls K' he) (fun hd => F.hconn K' he hd)
  exact hdev

end WaveTurbulence.FinalCountAsm
