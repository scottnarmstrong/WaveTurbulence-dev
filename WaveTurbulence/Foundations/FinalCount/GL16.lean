/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL15
public import WaveTurbulence.Foundations.FinalCount.G3AdmRun
/-! **G3-LOWDEG (R48), part 16**: the uniform context `UCtx` (class-inherited charge relations, ancestor and dart relations, `Good`)
along Steps D3 and D1, with the index dropping.  `AtomRelU.vinePostG` is a modification of `AtomRelU.step1` (G3AdmRun, sha256 in
COPIED-SHA256SUMS). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {M₀ : Molecule V D₀} {Rn : ℕ} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop}

theorem AtomRelU.vinePostG {h : HSt V D₀} (hR : AtomRelU Adm0 L w h) (hpin : EpsPin Adm0 L w h) (K : VineCut h.s.M)
    (hu : h.s.cls K.C.upper = .eps) (hl : h.s.cls K.C.lower = .eps) :
    AtomRelU Adm0 L w (h.vinePostG K) := by
  have hup : K.C.upper ∈ h.s.M.atoms := objectAtoms_sub K.C K.a_mem
  have hlo : K.C.lower ∈ h.s.M.atoms := objectAtoms_sub K.C K.b_mem
  have h1 := (hR.toX (ex := fun _ => False)).cut_pin K.cut_a .beta (jcls h.s.M K.C.upper)
    (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
    (Function.update h.anc K.fa (h.anc K.C.upper)) h.alive (hpin _ hup hu)
  obtain ⟨cl, hcl⟩ := hpin _ hlo hl
  have hpin2 : ∃ c : Mom d, ∀ k0, Adm0 k0 →
      chargeAt (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls h.s.M K.C.upper)).M L w
        (k0 ∘ (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls h.s.M K.C.upper)).down) K.C.lower = c := by
    refine ⟨cl, fun k0 hk0 => ?_⟩
    show chargeAt (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂) L w (k0 ∘ h.s.down) K.C.lower = cl
    rw [chargeAt_cut_other h.s.M K.cut_a K.ab_ne.symm K.fa_ne_b.symm]
    exact hcl k0 hk0
  have h2 := h1.cut_pin (h := ⟨h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls h.s.M K.C.upper),
      h.s.pr K.x₁ K.x₂ :: h.hist,
      Function.update (Function.update h.crec K.C.upper (some (h.s.pr K.x₁ K.x₂, h.alive))) K.fa
        (some (h.s.pr K.x₁ K.x₂, h.alive)), Function.update h.anc K.fa (h.anc K.C.upper)⟩) K.cut_b .beta
    (jcls h.s.M K.C.lower)
    (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
    (Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower))
    (h.s.pr K.x₁ K.x₂ :: h.alive) hpin2
  exact (AtomRelX.del h2 (VineKeep K) (VineKeep.closed K) (fun a _ _ hx => hx.1.1) _ _).toU


/-- `UCtx` along Step D3: the index drops by one. -/
theorem UCtx.stepD3 {C : CollData M₀} {h h' : HSt V D₀} {κ : D₀ → (Fin d → ℤ)} (hk : Adm0 κ)
    (hs : UStepD3 C L γ η w Adm0 h h') (hc : UCtx M₀ Rn Adm0 L w h) :
    1 ≤ Rn ∧ UCtx M₀ (Rn - 1) Adm0 L w h' := by
  have hh := hs.hstep hk
  obtain ⟨v, x₁, x₂, hD, rfl⟩ := hh.data
  obtain ⟨hR, hg⟩ := hc.good.1.betaSt hD.hv hD.hε hD.hd
  exact ⟨hR, ⟨⟨hg, by
      intro a ha
      show (h.s.betaSt v).cls a ≠ .ghost
      rw [St.betaSt_cls]
      by_cases e : a = v
      · rw [e, Function.update_self]; simp
      · rw [Function.update_of_ne e]; exact hc.good.2 a ha⟩,
    hc.anc.betaSt v, hc.rel.betaSt v, hc.atom.betaPost hD⟩⟩

/-- `UCtx` along Step D1: the index drops by `1` or `2`. -/
theorem UCtx.stepD1 {C : CollData M₀} {h h' : HSt V D₀} {κ : D₀ → (Fin d → ℤ)} (hk : Adm0 κ)
    (hs : UStepD1 C L γ η w Adm0 h h') (hp : PinnedM0 Adm0 L w M₀) (hc : UCtx M₀ Rn Adm0 L w h) :
    ∃ j R', 1 ≤ j ∧ R' + j = Rn ∧ UCtx M₀ R' Adm0 L w h' := by
  cases hs with
  | vine K hu hl hd2 htwin hsg hnew hdu hdl =>
    have hdu2 := two_le_deg_upper K
    have hdl2 := two_le_deg_lower K
    obtain ⟨R', e, hI⟩ := Inv.vineStG hc.good.1 K hu hl (by omega) (by omega)
    refine ⟨jdeg2 K, R', ?_, e, ⟨hI, clean_vineStG hc.good.2 K⟩, hc.anc.vinePostG K, hc.rel.vineStG K,
      hc.atom.vinePostG (hc.eps hp) K hu hl⟩
    unfold jdeg2; rcases hd2 with h | h <;> simp [h]

end WaveTurbulence.FinalCountG3
