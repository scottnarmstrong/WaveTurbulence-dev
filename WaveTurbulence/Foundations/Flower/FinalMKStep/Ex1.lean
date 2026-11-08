/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKStep.State
public import WaveTurbulence.Foundations.FinalCount.LowChain44

/-! # C1a SURV-STEP (4): the re-cut deviation `Ex1RCUniform` (C1a target 1/2)

`ex1RC_uniform` is main's `ex1D_uniform` (LowChain44 lines 27–121, sha256 in COPIED-SHA256SUMS) with `UStepD1`
replaced by `UStepRC`. The only change in the proof: main's `UStepD1` carries `hnew : F(M) < F(K.post)`; for a re-cut
it is derived from the `α/β` joint of degree `2` (`rc_deg_two`, main's `vineCut_F_lt`). The deviation route is the
class-free count `prop94_vine_newcomp` (no joint class is read), so the re-cut deviation is main's D1 deviation
`CD · excessRHS2 [] 1 2 = CD · L^{γ₀+η²-η³}` (o75 75-F2: `≲ L^{γ₀+2η³}`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountG8
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount WaveTurbulence.FinalCountAsm
open WaveTurbulence.Flower.FinalMKDefs

variable {d : ℕ}

/-- **C1a target 1/2: the uniform re-cut deviation** (`Ex1RCUniform d`, from `prop94_vine_newcomp` as `ex1D_uniform`). -/
theorem ex1RC_uniform (hd : 3 ≤ d) : Ex1RCUniform d := by
  intro γ hγ
  obtain ⟨Cs, C₂, hCs, hC₂, key⟩ := prop94_vine_newcomp WaveTurbulence.Vine.Param.vineparam hd hγ
  refine ⟨Cs, C₂, hCs, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, key2⟩ := key δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η ν hC₁ hη hη1 hν V D₀ _ _ _ w M₀ C P hP0 hPh hMol0 Adm0 hne hSrc0 hDec0 h h' hs hc hAR hMol hnl
    hνat => ?_⟩
  cases hs with
  | vine K hu hl hrc htwin hsg hdu hdl =>
    have hnew : h.s.M.numComponents < K.post.numComponents := vineCut_F_lt K (rc_deg_two K hu hl hrc)
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
    set cl := FinalCountG3.Cls.beta with hcl
    have hctx1 := hc.cutSt K.cut_a FinalCountG3.Cls.beta (jcls h.s.M K.C.upper) (by simp) (jcls_ne_eps _ _)
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

end WaveTurbulence.Flower.FinalMKStep
