/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain7
/-! **FINALCOUNT LOW-CHAIN, LC-2 (4): phase 3 (SG cuts) in the LOW run: `Reach*L.d3info`, `phase3_cover_memL`, `node3_factsL`.** -/
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

section d3info
variable {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {L γ η : ℝ}
  {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {Rn : ℕ}

theorem d3info_aux (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h₁ h₂ : HSt V D₀}
    (a : Reach1L C Un Fst L γ η w κ h₁) (c : Relation.ReflTransGen (HStepD3 C L γ η w κ) h₁ h₂) :
    AncRel M₀ h₂.s h₂.anc ∧ DartRel M₀ h₂.s := by
  have p1 : RunAux M₀ C h₁ := rtgH (P := fun h => RunAux M₀ C h) (fun _ _ hs hp => hs.aux hp) a.toL (RunAux.init C)
  have p2 : RunAux M₀ C h₂ := rtgH (P := fun h => RunAux M₀ C h) (fun _ _ hs hp => hs.aux hp) c p1
  obtain ⟨R', -, hI⟩ := invL_chain (fun _ _ hs R' hI => hI.stepD3' hs) c (invL_reach1 hS h0 a)
  exact ⟨p2.2.1, hI.rel⟩

theorem Reach2L.d3info (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach2L C Un Fst L γ η w κ h) :
    ∃ h₂, NoD3 C L w κ h₂ ∧ AncRel M₀ h₂.s h₂.anc ∧ DartRel M₀ h₂.s ∧ EpsLe h₂.s h.s := by
  obtain ⟨h₁, h₂, a, -, c, n, e⟩ := hr
  obtain ⟨hA, hD⟩ := d3info_aux hS h0 a c
  refine ⟨h₂, n, hA, hD, ?_⟩
  exact rtgH (P := fun x => EpsLe h₂.s x.s) (fun _ _ hs he => he.trans hs.toHStep2.step.epsLe) e (EpsLe.refl _)

theorem Reach3L.d3info (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach3L C Un Fst L γ η w κ h) :
    ∃ h₂, NoD3 C L w κ h₂ ∧ AncRel M₀ h₂.s h₂.anc ∧ DartRel M₀ h₂.s ∧ EpsLe h₂.s h.s := by
  obtain ⟨h₁, h₂, h₃, a, -, c, n, e, -, g⟩ := hr
  obtain ⟨hA, hD⟩ := d3info_aux hS h0 a c
  refine ⟨h₂, n, hA, hD, ?_⟩
  have e2 : EpsLe h₂.s h₃.s :=
    rtgH (P := fun x => EpsLe h₂.s x.s) (fun _ _ hs he => he.trans hs.toHStep2.step.epsLe) e (EpsLe.refl _)
  exact rtgH (P := fun x => EpsLe h₂.s x.s) (fun _ _ hs he => he.trans hs.toHStep3.step.epsLe) g e2

end d3info

theorem node3_factsL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 A : Set (D₀ → (Fin d → ℤ))} (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c) {h : HSt V D₀} (hA : Inv3L M₀ Rn Rch L w A0 A h)
    {v : V} {x₁ x₂ : h.s.D} {z : ℤ} {b : Bool} {a : V} {sg : Bool} (hn : Node3 L γ η h v x₁ x₂ z b a sg)
    (hext : ∀ k ∈ cls3 L γ η w h A x₁ x₂ z b a sg, Rch k h → Rch k (post3 h v x₁ x₂ z b)) :
    Inv3L M₀ Rn Rch L w A0 (cls3 L γ η w h A x₁ x₂ z b a sg) (post3 h v x₁ x₂ z b) ∧
    epsCount (post3 h v x₁ x₂ z b).s < epsCount h.s ∧
    QS L γ δ C₁ w P h (cls3 L γ η w h A x₁ x₂ z b a sg) ≤
      ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h (post3 h v x₁ x₂ z b)) *
        QS L γ δ C₁ w P (post3 h v x₁ x₂ z b) (cls3 L γ η w h A x₁ x₂ z b a sg) := by
  have hsub : cls3 L γ η w h A x₁ x₂ z b a sg ⊆ A := fun k hk => hk.1
  have hRpos : (0 : ℝ) < (2 : ℝ) ^ z := zpow_pos (by norm_num) z
  have hlt : epsCount (post3 h v x₁ x₂ z b).s < epsCount h.s := by
    have hab : (if h.s.M.IsAlphaCut v (fresh h) x₁ x₂ then Cls.alpha ((2 : ℝ) ^ z) (if b then 50 else 0) else Cls.beta) ≠ Cls.eps := by
      split_ifs <;> simp
    exact epsCount_cutSt_lt h.s hn.1 hn.2.1 _ _ hab hab
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  by_cases hAe : cls3 L γ η w h A x₁ x₂ z b a sg = ∅
  · refine ⟨⟨hsub.trans hA.1, Or.inl hAe⟩, hlt, ?_⟩
    rw [hAe, QS_empty]; exact bot_le
  rcases hA.2 with he | ⟨⟨R', hR', hc⟩, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hsub)) hAe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAe
  have hcc := uctx_mono hc (fun k (hk : k ∈ cls3 L γ η w h A x₁ x₂ z b a sg) => hk.1)
  have hpp := pinned_mono hp0 (fun k (hk : k ∈ cls3 L γ η w h A x₁ x₂ z b a sg) => hA.1 hk.1)
  have hst := uStep3_node (L := L) (γ := γ) (η := η) (w := w) (A := A) hn
  have hc' : UCtx M₀ R' (fun k => k ∈ cls3 L γ η w h A x₁ x₂ z b a sg) L w (post3 h v x₁ x₂ z b) :=
    UCtx.step3 hκ hst hpp hcc
  have hap' : ApPos (post3 h v x₁ x₂ z b).s := by
    by_cases hα : h.s.M.IsAlphaCut v (fresh h) x₁ x₂
    · have : (post3 h v x₁ x₂ z b).s = h.s.cutSt v (fresh h) x₁ x₂ (.alpha ((2 : ℝ) ^ z) (if b then 50 else 0))
          (.alpha ((2 : ℝ) ^ z) (if b then 50 else 0)) := by simp [post3, HSt.cut3Post, if_pos hα]
      rw [this]; exact apPos_cutSt_alpha h.s hap hRpos _
    · have : (post3 h v x₁ x₂ z b).s = h.s.cutSt v (fresh h) x₁ x₂ .beta .beta := by simp [post3, HSt.cut3Post, if_neg hα]
      rw [this]; exact apPos_cutSt_beta h.s hap
  have hr' : ∀ k ∈ cls3 L γ η w h A x₁ x₂ z b a sg, Rch k (post3 h v x₁ x₂ z b) := fun k hk => hext k hk (hr k hk.1)
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨⟨R', hR', hc'⟩, hap', hr'⟩⟩, hlt, ?_⟩
  have hI : Inv R' h.s := hc.good.1
  have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
  have hLC' := LCtx.of_inv hc'.good.1 ⟨(post3 h v x₁ x₂ z b).anc, hc'.anc⟩ hc'.rel
  have hcard : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c := by
    have := card_atoms_leL_of_uctx hS hR' hcc
    exact le_trans (by exact_mod_cast this) hnc
  exact UStep3.dev_pot H hst hI hcc.atom (apProd_pos hL hap) P hP0 (LCtx.hPinh hP hLC hLC') c hcard


/-- **A decoration that is not stuck lies in a node class** (phase 3, LOW run). -/
theorem phase3_cover_memL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η : ℝ} {w : Mom d}
    {A0 A : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)}
    (hS : SubHypL Rn M₀) (hobl : ∀ κ ∈ A0, SubproOblG C L γ η w κ)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hRA : ∀ κ h, Rch κ h → Reach3L C Un Fst L γ η w κ h)
    (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ) (h2 : 2 / L ≤ L ^ (-γ + η))
    {h : HSt V D₀} (hA : Inv3L M₀ Rn Rch L w A0 A h) (hAe : A ≠ ∅) {κ : D₀ → (Fin d → ℤ)} (hκ : κ ∈ A)
    (hnb : ¬ NoSGLeft L γ η w κ (HSt.init M₀).s h.s) :
    ∃ t ∈ nodes3 L γ η h, Desig C (h.anc t.1) (h.s.pr t.2.1 t.2.2.1) ∧
      κ ∈ cls3 L γ η w h A t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 := by
  obtain ⟨⟨R', hR', hc⟩, hap, hr⟩ := hA.2.resolve_left hAe
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hreach := hRA κ h (hr κ hκ)
  obtain ⟨R'', -, hIL⟩ := invL_reach3 hS (h0 κ (hA.1 hκ)) hreach
  obtain ⟨h₂, hN, hA₂, hD₂, hE⟩ := hreach.d3info hS (h0 κ (hA.1 hκ))
  unfold NoSGLeft at hnb
  push Not at hnb
  obtain ⟨v, hv, hε, hSG⟩ := hnb
  have h3 : 3 ≤ h.s.M.deg v := deg_three_of_sg (hobl κ (hA.1 hκ)) hA₂ hD₂ hc.anc hIL.rel hE hN hv hε hSG
  obtain ⟨h', hs'⟩ := exists_step3C_L (hobl κ (hA.1 hκ)) hL h2 hIL hc.anc hv hε hSG h3
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


end WaveTurbulence.FinalCountAsm
