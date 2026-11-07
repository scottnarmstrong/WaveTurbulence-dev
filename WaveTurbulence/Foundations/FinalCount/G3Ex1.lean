/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Ex2
public import WaveTurbulence.Foundations.FinalCount.G3VineBall
public import WaveTurbulence.Foundations.FinalCount.G3SrcGaps
public import WaveTurbulence.Foundations.FinalCount.G3VineF
/-! **FINALCOUNT-G3: excessprop1 (1) for Step 1 (vines)** (DH23 Prop 9.4, Step 1, L1797--L1801), glued to VINE-COUNT
`prop94_vine_all` (`ι` as a fixed ball: `prop94_vine_all_ball`).

The α-case (`F_pos ≤ F_pre`, hence `ΔF = 0` by `vine_F_ge`).  Named inputs (see HANDOFF): `hcls` (the classification of the removed
object, TARGET `subsetvc` + `subpro` (a), (e)), `hMol` (`M_cur` is a molecule: every component has an atom of degree `≠ 4`,
from `CompBeta`), the ladder-scale clause of `Adm0` at `M₀` (`hSrc0`) and `M₀` a molecule. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.VineCount WaveTurbulence.LGSpine.SourceVine

variable {d : ℕ}

/-- **excessprop1 (1), Step 1 (α-case).** -/
theorem UStep1.excess {V D₀ : Type} [DecidableEq V] [Fintype D₀] [DecidableEq D₀] (hvp : VINEPARAM) (hd : 3 ≤ d)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ →
      ∀ (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (M₀ : Molecule V D₀) (P : Finset V → ℝ),
      (∃ k0, Adm0 k0) → (∀ S, 0 ≤ P S) → LadderHered M₀ P → M₀.IsMolecule →
      (∀ k0, Adm0 k0 → SourceLadderGaps M₀ L w P k0) →
      (∀ k0, Adm0 k0 → ∃ c0, M₀.IsDecoration L w c0 k0 ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0) →
      ∀ {h h' : HSt V D₀}, UStep1 L γ η w Adm0 h h' → LCtx M₀ h.s → AtomRelU Adm0 L w h → h.s.M.IsMolecule →
      ∃ (K : VineCut h.s.M) (R : ℝ) (kp : ℕ), h' = h.vinePost K R kp ∧
        ((SingleVineVC K ∨ Nonempty (DoubleShape K)) →
        K.post.numComponents ≤ h.s.M.numComponents →
          IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P)
            (h'.s.M.countA L γ δ C₁ w (AdmS Adm0 h'.s) P)
            (ENNReal.ofReal ((Cs * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13) * (1 + δ⁻¹)) *
              excessRHS L γ η [(R, kp), (R, kp)] 0 0))) := by
  obtain ⟨Cs, hCs, C₂, hC₂, key⟩ := prop94_vine_all_ball hvp hd hγ
  refine ⟨Cs, hCs, C₂, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, key2⟩ := key δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η hC₁ hη hη1 hηγ w Adm0 M₀ P hne hP0 hPh hMol0 hSrc0 hDec0 h h' hs hc hAR hMol => ?_⟩
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

end WaveTurbulence.FinalCountG3
