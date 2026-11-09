/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3UStep
public import WaveTurbulence.Foundations.FinalCount.G3SrcGaps
public import WaveTurbulence.Foundations.FinalCount.GhostMain1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3UStep
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3AdmRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineF
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Op1Cone5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Gamma
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api

/-! # H-ASM (packet L6-HASM): the Op-1 creation cone of the run (`Ex1Cone`, wt-orch RULING R194 (2))

`Ex1Cone`: the Step-1 deviation of a uniform vine step with the creation-cone gain, the Phase-1 input `hExC` of the
ghost step `H.ChainCoverLow'` (`AsmChainLow`). Binders are those of `Ex1A` (`AsmPhase1b`), restricted to `kp = 0` (no
ι-ball) and `ΔF = 0` (no new component), plus the cone data of L6E2: a critical label (`Ghost.Crit`), the joint gap in
the creation cone (`Ghost.JointCone`, from a present degree-2 atom by `Ghost.jointCone_of_present`), and `k ≤ 2` NC
pairs, with right side `CA · (3·5^d · L^{-5ηk}) · excessRHS [(R,0),(R,0)] 0 0` (M1-R2 Thm 6.1 (e) at Op 1).

`ex1C_uniform` produces it from L6E2's `Ghost.prop94_vine_all_family_cone` (L4's Theorem C proved), as
`AsmEx1ULow.ex1A_uniform` produces `Ex1A`; `Ex1Cone.mono` raises the constant (for the common `CA` of `Ex1A` and
`Ex1Cone` in `AsmTopClass3`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.VineCount

variable {d : ℕ} {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀]

/-- **The Op-1 creation step with the cone gain** (RULING R194 (2)): `Ex1A`'s binders at `kp = 0`, `ΔF = 0`, plus a
critical label, `Ghost.JointCone` and `k ≤ 2`; right side `CA · (3·5^d·L^{-5ηk}) · excessRHS [(R,0),(R,0)] 0 0`. -/
def Ex1Cone (L γ η δ C₁ : ℝ) (w : Mom d) (M₀ : Molecule V D₀) (P : Finset V → ℝ) (CA : ℝ) : Prop :=
  ∀ (Adm0 : (D₀ → (Fin d → ℤ)) → Prop), (∃ k0, Adm0 k0) → (∀ k0, Adm0 k0 → SourceLadderGaps M₀ L w P k0) →
    (∀ k0, Adm0 k0 → ∃ c0, M₀.IsDecoration L w c0 k0 ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0) →
    ∀ {h h' : HSt V D₀}, UStep1 L γ η w Adm0 h h' → LCtx M₀ h.s → AtomRelU Adm0 L w h → h.s.M.IsMolecule →
      ∃ (K : Step1.VineCut Src.γL h.s.M) (R : ℝ) (kp : ℕ), h' = h.vinePostL K R kp ∧
        ((Step1.SingleVineVCGamma K ∨ Nonempty (Step1.DoubleShape K)) →
        K.post.numComponents ≤ h.s.M.numComponents → kp = 0 → Ghost.Crit L γ η R →
        Ghost.JointCone K L γ δ η w (AdmS Adm0 h.s) → ∀ k : ℕ, k ≤ 2 →
          IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P) (h'.s.M.countA L γ δ C₁ w (AdmS Adm0 h'.s) P)
            (ENNReal.ofReal (CA * (3 * 5 ^ d * L ^ (-5 * η * (k : ℝ))) * excessRHS L γ η [(R, 0), (R, 0)] 0 0)))

/-- `ENNReal.ofReal (a * X)` is monotone in `a ≥ 0`, whatever the sign of `X`. -/
theorem ofReal_mul_le_of_le {a a' X : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') :
    ENNReal.ofReal (a * X) ≤ ENNReal.ofReal (a' * X) := by
  rcases le_or_gt 0 X with hX | hX
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right haa hX)
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hX.le)]
    exact zero_le

/-- `Ex1Cone` is monotone in the constant. -/
theorem Ex1Cone.mono {L γ η δ C₁ : ℝ} {w : Mom d} {M₀ : Molecule V D₀} {P : Finset V → ℝ} {CA CA' : ℝ}
    (h0 : 0 ≤ CA) (hle : CA ≤ CA') (h : Ex1Cone L γ η δ C₁ w M₀ P CA) : Ex1Cone L γ η δ C₁ w M₀ P CA' := by
  intro Adm0 hne hSrc hDec h₁ h₂ hs hc hAR hMol
  obtain ⟨K, R, kp, he, hK⟩ := h Adm0 hne hSrc hDec hs hc hAR hMol
  refine ⟨K, R, kp, he, fun hcls hF hkp hcrit hcone k hk => ?_⟩
  refine isDeviation_mono (hK hcls hF hkp hcrit hcone k hk) ?_
  rw [mul_assoc CA, mul_assoc CA']
  exact ofReal_mul_le_of_le h0 hle

/-- **`Ex1Cone`, uniform in the types** (from L6E2's `Ghost.prop94_vine_all_family_cone`; the analogue of
`ex1A_uniform`). -/
theorem ex1C_uniform (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ → 200 * η ≤ γ → 200 * η ≤ 1 - γ →
      ∀ {V D₀ : Type} [DecidableEq V] [Fintype D₀] [DecidableEq D₀] (w : Mom d) (M₀ : Molecule V D₀) (P : Finset V → ℝ),
      (∀ S, 0 ≤ P S) → LadderHered M₀ P → M₀.IsMolecule →
      Ex1Cone L γ η δ C₁ w M₀ P ((Cs * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13)) * (1 + δ⁻¹)) := by
  obtain ⟨Cs, hCs, C₂, hC₂, key⟩ := Ghost.prop94_vine_all_family_cone (g := Src.γL) hd hγ
  refine ⟨Cs, hCs, C₂, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, key2⟩ := key δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η hC₁ hη hη1 hηγ h200a h200b V D₀ _ _ _ w M₀ P hP0 hPh hMol0 Adm0 hne hSrc0 hDec0
    h h' hs hc hAR hMol => ?_⟩
  cases hs with
  | vine K R kp hR hkp hu hl ga gb htwin hι hι0 hsg h3a h3b =>
    refine ⟨K, R, kp, rfl, fun hcls hα _ hcrit hcone k hk => ?_⟩
    obtain ⟨-, hRl, hRu⟩ := hR
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
    have key3 := key2 L hL C₁ η hC₁ hη hη1 hηγ h200a h200b h.s.M K hMol (fun a ha => hc.d4 a ha) hcls w
      (AdmS Adm0 h.s) (AdmS Adm0 (vineSt h.s K cl)) hAdm' P hP0 hscale
      (fun S' hS' S hS => hc.hPinh hPh hctx1 S' hS' S hS)
      (fun S' hS' S hS => hctx1.hPinh hPh hctx2 S' hS' S hS) hF R hRl hRu hcrit
      (by rintro _ ⟨k0, hk0, rfl⟩; exact (ga k0 hk0).2)
      (by rintro _ ⟨k0, hk0, rfl⟩; exact (ga k0 hk0).1) hcone k hk
    exact key3

end WaveTurbulence.GammaLow.FinalCount.H
