/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase1b
public import WaveTurbulence.Foundations.FinalCount.G3VineBall
public import WaveTurbulence.Foundations.FinalCount.G3Ex1New
/-! **FINALCOUNT-ASSEMBLY (top level): V,D₀-UNIFORM `Ex1A`, `Ex1N`.**  G3's `UStep1.excess` / `excess_new` take the atom and dart types BEFORE the
thresholds (`Cs`, `L₀`); `WTPrefix` chooses `L₀` before the garden, hence before `V = GBranch G.tree ⊕ ℕ`, `D₀ = GardenDart G`.  The proofs are copies with
the binder moved after `L₀` (they only use the uniform VINE-COUNT results `prop94_vine_all_ball`, `prop94_vine_newcomp`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.VineCount

variable {d : ℕ}

/-- `excessprop1 (1)`, uniform in the types. -/
theorem ex1A_uniform (hvp : VINEPARAM) (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ →
      ∀ {V D₀ : Type} [DecidableEq V] [Fintype D₀] [DecidableEq D₀] (w : Mom d) (M₀ : Molecule V D₀) (P : Finset V → ℝ),
      (∀ S, 0 ≤ P S) → LadderHered M₀ P → M₀.IsMolecule →
      Ex1A L γ η δ C₁ w M₀ P ((Cs * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13)) * (1 + δ⁻¹)) := by
  obtain ⟨Cs, hCs, C₂, hC₂, key⟩ := prop94_vine_all_ball hvp hd hγ
  refine ⟨Cs, hCs, C₂, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, key2⟩ := key δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η hC₁ hη hη1 hηγ V _ D₀ _ _ w M₀ P hP0 hPh hMol0 Adm0 hne hSrc0 hDec0 h h' hs hc hAR hMol => ?_⟩
  cases hs with
  | vine K R kp hR hkp hu hl ga gb htwin hι hι0 hsg h3a h3b =>
    refine ⟨K, R, kp, rfl, fun hcls hα => ?_⟩
    obtain ⟨-, hRl, hRu⟩ := hR
    obtain ⟨k₀, hk₀⟩ := hne
    have hLe : Real.exp 1 ≤ L := hL₀.trans hL
    have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
    have hF : K.post.numComponents = h.s.M.numComponents := (vine_F_alpha_iff K).1 hα
    set cl := alphaOrBeta K.post.numComponents h.s.M.numComponents R kp with hcl
    have hcl' : cl ≠ .eps := Cls.ne_eps_of_isAB (alphaOrBeta_isAB _ _ _ _)
    have hctx1 := hc.cutSt K.cut_a cl cl hcl' hcl'
    have hctx2 := hctx1.cutSt K.cut_b cl cl hcl' hcl'
    have hAdm' : ∀ κ, AdmS Adm0 h.s κ → AdmS Adm0 (vineSt h.s K cl) (fun x => κ x.1) :=
      fun κ hκ => AdmS.delSt (s := (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ cl cl).cutSt K.C.lower K.fb K.y₁ K.y₂ cl cl)
        (fun a => a ∉ K.C.atoms) K.closed hκ
    have hscale : DecScale h.s.M L w (AdmS Adm0 h.s) (SourceLadderGaps h.s.M L w P) := by
      intro c κ' _ _ hAdm
      obtain ⟨k0, hk0, rfl⟩ := hAdm
      obtain ⟨c0, hc0, hc04⟩ := hDec0 k0 hk0
      exact sourceGaps_state hc hPh hMol0 hc0 hc04 (hSrc0 k0 hk0)
    have hρ : (kp = 0 ∧ (if kp = 0 then 2 * R else L ^ (-50 * η) * R) = 2 * R) ∨
        (kp = 50 ∧ (if kp = 0 then 2 * R else L ^ (-50 * η) * R) = L ^ (-50 * η) * R ∧
          L⁻¹ ≤ (if kp = 0 then 2 * R else L ^ (-50 * η) * R)) := by
      rcases hkp with h0 | h50
      · left; simp [h0]
      · right
        have h' : kp ≠ 0 := by omega
        refine ⟨h50, by simp [h'], ?_⟩
        simp only [h', if_false]
        exact ((hι h50).radius hL0 hk₀)
    exact key2 L hL C₁ η hC₁ hη hη1 hηγ h.s.M K hMol (fun a ha => hc.d4 a ha) hcls w (AdmS Adm0 h.s)
      (AdmS Adm0 (vineSt h.s K cl)) hAdm' P hP0 hscale
      (fun S' hS' S hS => hc.hPinh hPh hctx1 S' hS' S hS)
      (fun S' hS' S hS => hctx1.hPinh hPh hctx2 S' hS' S hS) hF R hRl hRu kp
      (if kp = 0 then 2 * R else L ^ (-50 * η) * R) hρ
      (by rintro _ ⟨k0, hk0, rfl⟩; exact (ga k0 hk0).2)
      (by rintro _ ⟨k0, hk0, rfl⟩; exact (ga k0 hk0).1)
      (fun h50 => (hι h50).ball hAR)


/-- `excessprop1 (2)`, uniform in the types. -/
theorem ex1N_uniform (hvp : VINEPARAM) (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs C₂ : ℝ, 0 ≤ Cs ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η ν : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → 1 ≤ ν →
      ∀ {V D₀ : Type} [DecidableEq V] [Fintype D₀] [DecidableEq D₀] (w : Mom d) (M₀ : Molecule V D₀) (P : Finset V → ℝ),
      (∀ S, 0 ≤ P S) → LadderHered M₀ P → M₀.IsMolecule →
      Ex1N L γ η δ C₁ w M₀ P (Cs * ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) ν := by
  obtain ⟨Cs, C₂, hCs, hC₂, key⟩ := prop94_vine_newcomp hvp hd hγ
  refine ⟨Cs, C₂, hCs, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, key2⟩ := key δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η ν hC₁ hη hη1 hν V _ D₀ _ _ w M₀ P hP0 hPh hMol0 Adm0 hne hSrc0 hDec0 h h' hs hc hAR hMol hnl
    hνat => ?_⟩
  cases hs with
  | vine K R kp hR hkp hu hl ga gb htwin hι hι0 hsg h3a h3b =>
    refine ⟨K, R, kp, rfl, fun hcls hconn hF => ?_⟩
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
    set cl := alphaOrBeta K.post.numComponents h.s.M.numComponents R kp with hcl
    have hcl' : cl ≠ .eps := Cls.ne_eps_of_isAB (alphaOrBeta_isAB _ _ _ _)
    have hctx1 := hc.cutSt K.cut_a cl cl hcl' hcl'
    have hctx2 := hctx1.cutSt K.cut_b cl cl hcl' hcl'
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
    exact key2 L hL C₁ η ν hC₁ hη hη1 hν h.s.M K hMol (fun a ha => hc.d4 a ha) hsingle w (AdmS Adm0 h.s)
      (AdmS Adm0 (vineSt h.s K cl)) hAdm' P hP0 hscale
      (fun S' hS' S hS => hc.hPinh hPh hctx1 S' hS' S hS)
      (fun S' hS' S hS => hctx1.hPinh hPh hctx2 S' hS' S hS) hF hfix'


end WaveTurbulence.FinalCountAsm
