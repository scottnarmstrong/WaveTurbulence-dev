/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase3
/-! **FINALCOUNT-ASSEMBLY, phase 3: node data, classes, the uniform step on a node class.** -/
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

/-- The earlier cut recorded at the atom `a` (default `dflt`). -/
noncomputable def qOf (h : HSt V D₀) (a : V) (dflt : D₀ × D₀) : D₀ × D₀ := ((h.crec a).map Prod.fst).getD dflt

/-- The data of a phase-3 node: `(v, x₁, x₂, z, b, a, sg)`; label `R = 2^z`, `kp = 50` iff `b`. -/
def Node3 [Infinite V] (L γ η : ℝ) (h : HSt V D₀) (v : V) (x₁ x₂ : h.s.D) (z : ℤ) (b : Bool) (a : V) (_sg : Bool) : Prop :=
  h.s.M.IsCutData v (fresh h) x₁ x₂ ∧ h.s.cls v = .eps ∧ 3 ≤ h.s.M.deg v ∧ IsLabel L γ η ((2 : ℝ) ^ z) ∧
    a ∈ h.s.M.atoms ∧ (b = true → ∃ q vis, h.crec a = some (q, vis) ∧ q ∈ h.hist)

abbrev T3 (h : HSt V D₀) := V × h.s.D × h.s.D × ℤ × Bool × V × Bool

noncomputable def nodes3 [Infinite V] (L γ η : ℝ) (h : HSt V D₀) : Finset (T3 h) :=
  (h.s.M.atoms ×ˢ ((Finset.univ : Finset h.s.D) ×ˢ ((Finset.univ : Finset h.s.D) ×ˢ
    ((Finset.Icc (-(⌈2 * Real.log L⌉₊ : ℤ)) 0) ×ˢ ((Finset.univ : Finset Bool) ×ˢ (h.s.M.atoms ×ˢ (Finset.univ : Finset Bool))))))).filter
    fun t => Node3 L γ η h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2

theorem nodes3_card [Infinite V] (L γ η : ℝ) (h : HSt V D₀) :
    (nodes3 L γ η h).card ≤ h.s.M.atoms.card * (Fintype.card h.s.D * (Fintype.card h.s.D *
      ((⌈2 * Real.log L⌉₊ + 1) * (2 * (h.s.M.atoms.card * 2))))) := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool, Int.card_Icc]
  have : (0 + 1 - -(⌈2 * Real.log L⌉₊ : ℤ)).toNat = ⌈2 * Real.log L⌉₊ + 1 := by omega
  rw [this]

/-- The class of a node: the decorations of `A` for which the step data are valid. -/
def cls3 (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (x₁ x₂ : h.s.D) (z : ℤ) (b : Bool) (a : V)
    (sg : Bool) : Set (D₀ → (Fin d → ℤ)) :=
  {k | k ∈ A ∧ Molecule.gapKind L γ η (Molecule.gapAt L w (k ∘ h.s.down) x₁ x₂) = .SG ∧
    GapSim L w (k ∘ h.s.down) x₁ x₂ ((2 : ℝ) ^ z) ∧
    (b = true → 0 < ‖pgap L w k (h.s.pr x₁ x₂) + (if sg then (1 : ℝ) else -1) • pgap L w k (qOf h a (h.s.pr x₁ x₂))‖ ∧
      ‖pgap L w k (h.s.pr x₁ x₂) + (if sg then (1 : ℝ) else -1) • pgap L w k (qOf h a (h.s.pr x₁ x₂))‖ ≤
        L ^ (-50 * η) * (2 : ℝ) ^ z) ∧
    (b = false → ¬ IotaHit L η w k h.alive (h.s.pr x₁ x₂) ((2 : ℝ) ^ z))}

noncomputable def post3 [Infinite V] (h : HSt V D₀) (v : V) (x₁ x₂ : h.s.D) (z : ℤ) (b : Bool) : HSt V D₀ :=
  h.cut3Post v (fresh h) x₁ x₂ ((2 : ℝ) ^ z) (if b then 50 else 0)

theorem uStep3_node [Infinite V] {L γ η : ℝ} {w : Mom d} {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {v : V} {x₁ x₂ : h.s.D}
    {z : ℤ} {b : Bool} {a : V} {sg : Bool} (hn : Node3 L γ η h v x₁ x₂ z b a sg) :
    UStep3 L γ η w (fun k => k ∈ cls3 L γ η w h A x₁ x₂ z b a sg) h (post3 h v x₁ x₂ z b) := by
  obtain ⟨hc, hε, h3, hR, ha, hb⟩ := hn
  refine UStep3.cut h v (fresh h) x₁ x₂ hc ((2 : ℝ) ^ z) (if b then 50 else 0) hR (by cases b <;> simp) hε
    (fun k hk => hk.2.1) (fun k hk => hk.2.2.1) ?_ ?_ h3
  · intro h50
    have hb' : b = true := by cases b <;> simp_all
    obtain ⟨q, vis, hcr, hq⟩ := hb hb'
    refine ⟨q, hq, ⟨a, ha, vis, hcr⟩, if sg then 1 else -1, by cases sg <;> simp, fun k hk => ?_⟩
    have := hk.2.2.2.1 hb'
    have hq' : qOf h a (h.s.pr x₁ x₂) = q := by simp [qOf, hcr]
    rw [hq'] at this
    exact this
  · intro h0 k hk
    have hb' : b = false := by cases b <;> simp_all
    exact hk.2.2.2.2 hb'

theorem node3_facts [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 A : Set (D₀ → (Fin d → ℤ))} (H : TriReal d L γ η δ C₁) (hS : SubHyp Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c) {h : HSt V D₀} (hA : Inv3 M₀ Rn Rch L w A0 A h)
    {v : V} {x₁ x₂ : h.s.D} {z : ℤ} {b : Bool} {a : V} {sg : Bool} (hn : Node3 L γ η h v x₁ x₂ z b a sg)
    (hext : ∀ k ∈ cls3 L γ η w h A x₁ x₂ z b a sg, Rch k h → Rch k (post3 h v x₁ x₂ z b)) :
    Inv3 M₀ Rn Rch L w A0 (cls3 L γ η w h A x₁ x₂ z b a sg) (post3 h v x₁ x₂ z b) ∧
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
  rcases hA.2 with he | ⟨hc, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hsub)) hAe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAe
  have hcc := uctx_mono hc (fun k (hk : k ∈ cls3 L γ η w h A x₁ x₂ z b a sg) => hk.1)
  have hpp := pinned_mono hp0 (fun k (hk : k ∈ cls3 L γ η w h A x₁ x₂ z b a sg) => hA.1 hk.1)
  have hst := uStep3_node (L := L) (γ := γ) (η := η) (w := w) (A := A) hn
  have hc' : UCtx M₀ Rn (fun k => k ∈ cls3 L γ η w h A x₁ x₂ z b a sg) L w (post3 h v x₁ x₂ z b) :=
    UCtx.step3 hκ hst hpp hcc
  have hap' : ApPos (post3 h v x₁ x₂ z b).s := by
    by_cases hα : h.s.M.IsAlphaCut v (fresh h) x₁ x₂
    · have : (post3 h v x₁ x₂ z b).s = h.s.cutSt v (fresh h) x₁ x₂ (.alpha ((2 : ℝ) ^ z) (if b then 50 else 0))
          (.alpha ((2 : ℝ) ^ z) (if b then 50 else 0)) := by simp [post3, HSt.cut3Post, if_pos hα]
      rw [this]; exact apPos_cutSt_alpha h.s hap hRpos _
    · have : (post3 h v x₁ x₂ z b).s = h.s.cutSt v (fresh h) x₁ x₂ .beta .beta := by simp [post3, HSt.cut3Post, if_neg hα]
      rw [this]; exact apPos_cutSt_beta h.s hap
  have hr' : ∀ k ∈ cls3 L γ η w h A x₁ x₂ z b a sg, Rch k (post3 h v x₁ x₂ z b) := fun k hk => hext k hk (hr k hk.1)
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨hc', hap', hr'⟩⟩, hlt, ?_⟩
  have hI : Inv Rn h.s := hc.good.1
  have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
  have hLC' := LCtx.of_inv hc'.good.1 ⟨(post3 h v x₁ x₂ z b).anc, hc'.anc⟩ hc'.rel
  have hcard : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c := by
    have := UCtx.card_atoms_le hS hcc
    exact le_trans (by exact_mod_cast this) hnc
  exact UStep3.dev_pot H hst hI hcc.atom (apProd_pos hL hap) P hP0 (LCtx.hPinh hP hLC hLC') c hcard

end WaveTurbulence.FinalCountAsm
