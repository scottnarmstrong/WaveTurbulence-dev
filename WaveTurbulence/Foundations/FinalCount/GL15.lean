/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL14
public import WaveTurbulence.Foundations.FinalCount.G3Iso
public import WaveTurbulence.Foundations.FinalCount.G3Ex1New
/-! **G3-LOWDEG (R48), part 15**: the uniform step `UStepD1` and its deviation `UStepD1.excess_new` (`excessprop1 (2)` with a
degree-`2` joint: a new component is created, `ΔF = 1`, `ΔV_β = 2`, TARGET-literal bookkeeping with the isolated halves kept; deleting
them is a dartless restriction, deviation `1`; the true increments are smaller and the assembly pays with the index drop).
`UStepD1.excess_new` is a modification of `UStep1.excess_new` (G3Ex1New, sha256 in COPIED-SHA256SUMS) whose proof body is copied. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.VineCount WaveTurbulence.LGSpine.SourceVine

section iso
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem pclosed_restrict_of {M : Molecule V D} {P₁ P₂ P : V → Prop} [DecidablePred P₁] [DecidablePred P₂]
    (hP : ∀ a, P a ↔ P₁ a ∧ P₂ a) (h₁ : PClosed M P₁) (hc : PClosed M P) : PClosed (restrictP M P₁ h₁) P₂ := by
  intro x hx
  exact ((hP _).1 (hc x.1 ((hP _).2 ⟨x.2, hx⟩))).2

/-- Restricting twice is restricting once to the conjunction. -/
noncomputable def restrictRestrictIso (M : Molecule V D) (P₁ P₂ P : V → Prop) [DecidablePred P₁] [DecidablePred P₂]
    [DecidablePred P] (hP : ∀ a, P a ↔ P₁ a ∧ P₂ a) (h₁ : PClosed M P₁) (hc : PClosed M P) :
    DartIso (restrictP (restrictP M P₁ h₁) P₂ (pclosed_restrict_of hP h₁ hc)) (restrictP M P hc) where
  e :=
    { toFun := fun x => ⟨x.1.1, (hP _).2 ⟨x.1.2, x.2⟩⟩
      invFun := fun y => ⟨⟨y.1, ((hP _).1 y.2).1⟩, ((hP _).1 y.2).2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  atoms := by
    ext a
    simp only [restrictP, Finset.mem_filter, hP, and_assoc]
  atom := fun x => rfl
  mate := fun x => rfl
  out := fun x => rfl
end iso

variable {V : Type*} [DecidableEq V] {D₀ : Type*} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {M₀ : Molecule V D₀}

/-- **Step D1 for the class `Adm0`**. -/
inductive UStepD1 (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) :
    HSt V D₀ → HSt V D₀ → Prop
  | vine (h : HSt V D₀) (K : VineCut h.s.M) (hu : h.s.cls K.C.upper = .eps) (hl : h.s.cls K.C.lower = .eps)
      (hd2 : h.s.M.deg K.C.upper = 2 ∨ h.s.M.deg K.C.lower = 2)
      (htwin : ∀ k0, Adm0 k0 → (pgap L w k0 (h.s.pr K.y₁ K.y₂) = pgap L w k0 (h.s.pr K.x₁ K.x₂) ∨
        pgap L w k0 (h.s.pr K.y₁ K.y₂) = -pgap L w k0 (h.s.pr K.x₁ K.x₂)))
      (hsg : ∀ k0, Adm0 k0 → Molecule.gapKind L γ η (Molecule.gapAt L w (k0 ∘ h.s.down) K.x₁ K.x₂) = .SG)
      (hnew : h.s.M.numComponents < K.post.numComponents)
      (hdu : Desig C (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂)) (hdl : Desig C (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂)) :
      UStepD1 C L γ η w Adm0 h (h.vinePostG K)

theorem UStepD1.hstep {C : CollData M₀} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {κ : D₀ → (Fin d → ℤ)} {h h' : HSt V D₀}
    (hs : UStepD1 C L γ η w Adm0 h h') (hk : Adm0 κ) : HStepD1 C L γ η w κ h h' := by
  cases hs with
  | vine K hu hl hd2 htwin hsg hnew hdu hdl => exact HStepD1.vine h K hu hl hd2 (htwin κ hk) (hsg κ hk) hnew hdu hdl

variable {d : ℕ}

/-- **excessprop1 (2), Step 1 at an object with a degree-`2` joint (new component).**  The conclusion bounds the deviation to the
state `h' = h.vinePostG K` (isolated halves deleted); `hF` is automatic (`hnew` and `vine_F_le_succ`). -/
theorem UStepD1.excess_new {V D₀ : Type} [DecidableEq V] [Fintype D₀] [DecidableEq D₀] (hvp : VINEPARAM) (hd : 3 ≤ d)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs C₂ : ℝ, 0 ≤ Cs ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η ν : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → 1 ≤ ν →
      ∀ (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (M₀ : Molecule V D₀) (C : CollData M₀) (P : Finset V → ℝ),
      (∃ k0, Adm0 k0) → (∀ S, 0 ≤ P S) → LadderHered M₀ P → M₀.IsMolecule →
      (∀ k0, Adm0 k0 → SourceLadderGaps M₀ L w P k0) →
      (∀ k0, Adm0 k0 → ∃ c0, M₀.IsDecoration L w c0 k0 ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0) →
      ∀ {h h' : HSt V D₀}, UStepD1 C L γ η w Adm0 h h' → LCtx M₀ h.s → AtomRelU Adm0 L w h → h.s.M.IsMolecule →
      (∀ x, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x)) → (h.s.M.atoms.card : ℝ) ≤ ν →
      ∃ (K : VineCut h.s.M), h' = h.vinePostG K ∧
        ((SingleVineVC K ∨ Nonempty (DoubleShape K)) →
        (Nonempty (DoubleShape K) →
          ∃ G : Finset h.s.D, (∀ z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K G) →
          IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P)
            (h'.s.M.countA L γ δ C₁ w (AdmS Adm0 h'.s) P)
            (ENNReal.ofReal ((Cs * ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) *
              excessRHS2 L γ η [] 1 2))) := by
  obtain ⟨Cs, C₂, hCs, hC₂, key⟩ := prop94_vine_newcomp hvp hd hγ
  refine ⟨Cs, C₂, hCs, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, key2⟩ := key δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η ν hC₁ hη hη1 hν w Adm0 M₀ C P hne hP0 hPh hMol0 hSrc0 hDec0 h h' hs hc hAR hMol hnl
    hνat => ?_⟩
  cases hs with
  | vine K hu hl hd2 htwin hsg hnew hdu hdl =>
    refine ⟨K, rfl, fun hcls hconn => ?_⟩
    have hF : K.post.numComponents = h.s.M.numComponents + 1 := by
      have := vine_F_le_succ K; omega
    have hLe : Real.exp 1 ≤ L := hL₀.trans hL
    have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
    have hnc : ¬ K.post.SameComponent K.fa K.fb := fun hh => by
      have := vine_F_le_of_sc K hh
      omega
    have hsingle : SingleVineVC K := by
      rcases hcls with h1 | hS
      · exact h1
      · exfalso
        obtain ⟨S⟩ := hS
        obtain ⟨G, hG, hr⟩ := hconn ⟨S⟩
        have := doubleShape_F_le K S hG hr
        omega
    set cl := Cls.beta with hcl
    have hctx1 := hc.cutSt K.cut_a .beta (jcls h.s.M K.C.upper) (by simp) (jcls_ne_eps _ _)
    have hctx2 := hctx1.cutSt K.cut_b .beta (jcls h.s.M K.C.lower) (by simp) (jcls_ne_eps _ _)
    have hAdm' : ∀ κ, AdmS Adm0 h.s κ → AdmS Adm0 (vineSt h.s K cl) (fun x => κ x.1) :=
      fun κ hκ => AdmS.delSt (s := (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ cl cl).cutSt K.C.lower K.fb K.y₁ K.y₂ cl cl)
        (fun a => a ∉ K.C.atoms) K.closed hκ
    have hscale : DecScale h.s.M L w (AdmS Adm0 h.s) (SourceLadderGaps h.s.M L w P) := by
      intro c κ' _ _ hAdm
      obtain ⟨k0, hk0, rfl⟩ := hAdm
      obtain ⟨c0, hc0, hc04⟩ := hDec0 k0 hk0
      exact sourceGaps_state hc hPh hMol0 hc0 hc04 (hSrc0 k0 hk0)
    have hgap : ∀ κ, AdmS Adm0 h.s κ → κ K.x₁ ≠ κ K.x₂ := by
      intro κ hκ
      obtain ⟨k0, hk0, rfl⟩ := hκ
      exact gapAt_ne_of_SG (hsg k0 hk0)
    obtain ⟨ν₀, -, hν₀, hfix⟩ := newCompFixed_exists (d := d) (by omega) K hnc hnl hc.d4 (vc_block_of_new K hnc)
      (hL0.ne') (Adm := AdmS Adm0 h.s) (γ := γ) (δ := δ) (w := w) hgap
    have hfix' := newCompFixed_mono hL0 hδ.1 (hν₀.trans hνat) hfix
    have k3 := key2 L hL C₁ η ν hC₁ hη hη1 hν h.s.M K hMol (fun a ha => hc.d4 a ha) hsingle w (AdmS Adm0 h.s)
      (AdmS Adm0 (vineSt h.s K cl)) hAdm' P hP0 hscale
      (fun S' hS' S hS => hc.hPinh hPh hctx1 S' hS' S hS)
      (fun S' hS' S hS => hctx1.hPinh hPh hctx2 S' hS' S hS) hF hfix'
    -- delete the isolated halves of the degree-`2` joints: a dartless restriction, deviation `1`
    have hC0 : 0 < C₁ := lt_of_lt_of_le one_pos (hC₂.trans hC₁)
    set P₂ : V → Prop := fun a => ¬ (a = K.fa ∧ h.s.M.deg K.C.upper = 2) ∧ ¬ (a = K.fb ∧ h.s.M.deg K.C.lower = 2) with hP₂d
    have hPe : ∀ a, VineKeep K a ↔ (a ∉ K.C.atoms) ∧ P₂ a := fun a => Iff.rfl
    have hVK : PClosed K.cutMol (VineKeep K) := VineKeep.closed K
    have hP₂ : PClosed K.post P₂ := pclosed_restrict_of hPe K.closed hVK
    have hno : ∀ x : PDart K.cutMol (fun a => a ∉ K.C.atoms), P₂ (K.post.atom x) := by
      intro x
      refine ⟨fun ⟨he, hd⟩ => ?_, fun ⟨he, hd⟩ => ?_⟩
      · have : x.1 ∈ K.cutMol.dartsAt K.fa := by rw [mem_dartsAt]; exact he
        rw [vineCut_fa_dartless K hd] at this; exact absurd this (Finset.notMem_empty _)
      · have : x.1 ∈ K.cutMol.dartsAt K.fb := by rw [mem_dartsAt]; exact he
        rw [vineCut_fb_dartless K hd] at this; exact absurd this (Finset.notMem_empty _)
    let Adm' : (PDart K.post P₂ → (Fin d → ℤ)) → Prop :=
      fun κ' => ∃ k0, Adm0 k0 ∧ κ' = fun x => k0 (h.s.down x.1.1)
    have hghost := countA_restrict_dartless K.post P₂ hP₂ hno L γ δ C₁ w hL0 hδ.1 hC0
      (AdmS Adm0 (vineSt h.s K cl)) Adm'
      (fun κ hκ => by
        obtain ⟨k0, hk0, rfl⟩ := hκ
        exact ⟨k0, hk0, rfl⟩) P
      (fun S => zero_le_one.trans (ladderWeight_ge_one L γ δ (P S) hLe hδ.1.le (hP0 S)))
    let I : DartIso (restrictP K.post P₂ hP₂) (vineStG h.s K).M :=
      restrictRestrictIso K.cutMol (fun a => a ∉ K.C.atoms) P₂ (VineKeep K) hPe K.closed hVK
    have hiso := I.countA_eq L γ δ C₁ w Adm' (AdmS Adm0 (vineStG h.s K)) (fun κ' => by
      constructor
      · rintro ⟨k0, hk0, e⟩
        refine ⟨k0, hk0, ?_⟩
        funext x
        have := congrFun e (I.e x)
        exact this
      · rintro ⟨k0, hk0, e⟩
        refine ⟨k0, hk0, ?_⟩
        funext y
        have := congrFun e (I.e.symm y)
        simp only [Equiv.apply_symm_apply] at this
        exact this) P
    have htr := isDeviation_trans' k3 hghost
    rw [mul_one] at htr
    show IsDeviation _ ((vineStG h.s K).M.countA L γ δ C₁ w (AdmS Adm0 (vineStG h.s K)) P) _
    rw [← hiso]
    exact htr

end WaveTurbulence.FinalCountG3
