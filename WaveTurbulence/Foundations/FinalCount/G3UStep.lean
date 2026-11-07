/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Iota
/-! **FINALCOUNT-G3: the steps for a whole admissible class** (excessprop1 (1): "each step condition must hold for every
admissible decoration").

`UStepk … Adm0 h h'` is `HStepk` with every κ-dependent condition required for all `k0 ∈ Adm0`; the data of the step
(atoms, darts, label `R`, parameter `kp`) are the same for all decorations of the class.  The `ι` conditions are in the
uniform form: `kp = 50` requires an earlier cut, still carried by a present atom, that hits for all `k0 ∈ Adm0` with one
sign (`IotaUnif`, the fixed ball of DH23 L1801 / TARGET Remark `remiota`); `kp = 0` requires that no earlier cut hits.
`UStepk.hstep` : for every `κ ∈ Adm0` the step is an `HStepk`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-! ### The post states (copied from the targets of `HStep1..4`) -/

noncomputable def HSt.vinePost (h : HSt V D₀) (K : VineCut h.s.M) (R : ℝ) (kp : ℕ) : HSt V D₀ :=
  ⟨vineSt h.s K (alphaOrBeta K.post.numComponents h.s.M.numComponents R kp),
   h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist,
   Function.update (Function.update (Function.update (Function.update h.crec K.C.upper
     (some (h.s.pr K.x₁ K.x₂, h.alive))) K.fa (some (h.s.pr K.x₁ K.x₂, h.alive))) K.C.lower
     (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive))) K.fb
     (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive)),
   Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower)⟩

noncomputable def HSt.triPost (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
    (hcl : PClosed T.kept (triKeep h.s T)) : HSt V D₀ :=
  ⟨triSt h.s T Q kp hcl,
   h.s.pr (T.a 2) (T.b 2) :: h.s.pr (T.a 1) (T.b 1) :: h.s.pr (T.a 0) (T.b 0) :: h.hist,
   Function.update (Function.update (Function.update h.crec (T.f 0) (some (h.s.pr (T.a 0) (T.b 0), h.alive)))
     (T.f 1) (some (h.s.pr (T.a 1) (T.b 1), h.triVis1 T)))
     (T.f 2) (some (h.s.pr (T.a 2) (T.b 2), h.triVis2 T)),
   Function.update (Function.update (Function.update h.anc (T.f 0) (h.anc (T.t 0))) (T.f 1) (h.anc (T.t 1)))
     (T.f 2) (h.anc (T.t 2))⟩

noncomputable def HSt.cut3Post (h : HSt V D₀) (v v₂ : V) (x₁ x₂ : h.s.D) (R : ℝ) (kp : ℕ) : HSt V D₀ :=
  ⟨h.s.cutSt v v₂ x₁ x₂ (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta)
    (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta),
   h.s.pr x₁ x₂ :: h.hist,
   Function.update (Function.update h.crec v (some (h.s.pr x₁ x₂, h.alive))) v₂ (some (h.s.pr x₁ x₂, h.alive)),
   Function.update h.anc v₂ (h.anc v)⟩

noncomputable def HSt.cut4Post (h : HSt V D₀) (v v₂ : V) (x₁ x₂ : h.s.D) : HSt V D₀ :=
  ⟨h.s.cutSt v v₂ x₁ x₂ .beta .beta, h.s.pr x₁ x₂ :: h.hist,
   Function.update (Function.update h.crec v (some (h.s.pr x₁ x₂, h.alive))) v₂ (some (h.s.pr x₁ x₂, h.alive)),
   Function.update h.anc v₂ (h.anc v)⟩

/-! ### The uniform steps -/

/-- **Step 1** for the class `Adm0`. -/
inductive UStep1 (L γ η : ℝ) (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) : HSt V D₀ → HSt V D₀ → Prop
  | vine (h : HSt V D₀) (K : VineCut h.s.M) (R : ℝ) (kp : ℕ) (hR : IsLabel L γ η R) (hkp : kp = 0 ∨ kp = 50)
      (hu : h.s.cls K.C.upper = .eps) (hl : h.s.cls K.C.lower = .eps)
      (ga : ∀ k0, Adm0 k0 → GapSim L w (k0 ∘ h.s.down) K.x₁ K.x₂ R)
      (gb : ∀ k0, Adm0 k0 → GapSim L w (k0 ∘ h.s.down) K.y₁ K.y₂ R)
      (htwin : ∀ k0, Adm0 k0 → (pgap L w k0 (h.s.pr K.y₁ K.y₂) = pgap L w k0 (h.s.pr K.x₁ K.x₂) ∨
        pgap L w k0 (h.s.pr K.y₁ K.y₂) = -pgap L w k0 (h.s.pr K.x₁ K.x₂)))
      (hι : kp = 50 → IotaUnif Adm0 L η w h (h.s.pr K.x₁ K.x₂) R)
      (hι0 : kp = 0 → ∀ k0, Adm0 k0 → ¬ IotaHit L η w k0 h.alive (h.s.pr K.x₁ K.x₂) R ∧
        ¬ IotaHit L η w k0 (h.s.pr K.x₁ K.x₂ :: h.alive) (h.s.pr K.y₁ K.y₂) R)
      (hsg : ∀ k0, Adm0 k0 → Molecule.gapKind L γ η (Molecule.gapAt L w (k0 ∘ h.s.down) K.x₁ K.x₂) = .SG)
      (h3a : 3 ≤ h.s.M.deg K.C.upper) (h3b : 3 ≤ h.s.M.deg K.C.lower) :
      UStep1 L γ η w Adm0 h (h.vinePost K R kp)

/-- **The sibling hit** (DH23 L1782 with the first cut of the same triangle): `0 < |r_p + sg r_q| ≤ L^{-50η} R` uniformly on
`Adm0`, for the cut `p` and the first cut `q` of the same triangle. -/
def SibUnif (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (L η : ℝ) (w : Mom d) (q p : D₀ × D₀) (R : ℝ) : Prop :=
  ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧ ∀ k0, Adm0 k0 → 0 < ‖pgap L w k0 p + sg • pgap L w k0 q‖ ∧
    ‖pgap L w k0 p + sg • pgap L w k0 q‖ ≤ L ^ (-50 * η) * R

/-- **Step 2** for the class `Adm0`: the `κ = 50` of the second cut comes from an earlier cut still carried by a present atom,
or from the first cut of the same triangle (the sibling hit, counted by FINALCOUNT-G2-SIBLING). -/
inductive UStep2 (L γ η : ℝ) (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) : HSt V D₀ → HSt V D₀ → Prop
  | tri (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
      (hQ : ∀ j : Fin 2, IsLabel L γ η (Q j)) (hkp : ∀ j : Fin 2, kp j = 0 ∨ kp j = 50)
      (hsg : ∀ k0, Adm0 k0 → ∀ j : Fin 2, Molecule.gapKind L γ η
        (Molecule.gapAt L w (k0 ∘ h.s.down) (T.a j.castSucc) (T.b j.castSucc)) = .SG)
      (hsim : ∀ k0, Adm0 k0 → ∀ j : Fin 2, GapSim L w (k0 ∘ h.s.down) (T.a j.castSucc) (T.b j.castSucc) (Q j))
      (hcl : PClosed T.kept (triKeep h.s T))
      (hnz : ∀ k0, Adm0 k0 → pgap L w k0 (h.s.pr (T.a 2) (T.b 2)) ≠ 0)
      (hι₀ : h.s.cls (T.t 0) = .eps → kp 0 = 50 → IotaUnif Adm0 L η w h (h.s.pr (T.a 0) (T.b 0)) (Q 0))
      (hι₀' : h.s.cls (T.t 0) = .eps → kp 0 = 0 → ∀ k0, Adm0 k0 →
        ¬ IotaHit L η w k0 h.alive (h.s.pr (T.a 0) (T.b 0)) (Q 0))
      (hι₁ : h.s.cls (T.t 1) = .eps → kp 1 = 50 → IotaUnif Adm0 L η w h (h.s.pr (T.a 1) (T.b 1)) (Q 1) ∨
        (h.s.cls (T.t 0) = .eps ∧
          SibUnif Adm0 L η w (h.s.pr (T.a 0) (T.b 0)) (h.s.pr (T.a 1) (T.b 1)) (Q 1)))
      (hι₁' : h.s.cls (T.t 1) = .eps → kp 1 = 0 → ∀ k0, Adm0 k0 →
        ¬ IotaHit L η w k0 (h.triVis1 T) (h.s.pr (T.a 1) (T.b 1)) (Q 1))
      (h3 : ∀ j, h.s.cls (T.t j) = .eps → 3 ≤ h.s.M.deg (T.t j)) :
      UStep2 L γ η w Adm0 h (h.triPost T Q kp hcl)

/-- **Step 3** for the class `Adm0`. -/
inductive UStep3 (L γ η : ℝ) (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) : HSt V D₀ → HSt V D₀ → Prop
  | cut (h : HSt V D₀) (v v₂ : V) (x₁ x₂ : h.s.D) (hc : h.s.M.IsCutData v v₂ x₁ x₂) (R : ℝ) (kp : ℕ)
      (hR : IsLabel L γ η R) (hkp : kp = 0 ∨ kp = 50) (hε : h.s.cls v = .eps)
      (hsg : ∀ k0, Adm0 k0 → Molecule.gapKind L γ η (Molecule.gapAt L w (k0 ∘ h.s.down) x₁ x₂) = .SG)
      (hsim : ∀ k0, Adm0 k0 → GapSim L w (k0 ∘ h.s.down) x₁ x₂ R)
      (hι : kp = 50 → IotaUnif Adm0 L η w h (h.s.pr x₁ x₂) R)
      (hι' : kp = 0 → ∀ k0, Adm0 k0 → ¬ IotaHit L η w k0 h.alive (h.s.pr x₁ x₂) R)
      (h3 : 3 ≤ h.s.M.deg v) :
      UStep3 L γ η w Adm0 h (h.cut3Post v v₂ x₁ x₂ R kp)

/-- **Step 4** for the class `Adm0`. -/
inductive UStep4 (L : ℝ) (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) : HSt V D₀ → HSt V D₀ → Prop
  | cut (h : HSt V D₀) (v v₂ : V) (x₁ x₂ : h.s.D) (hc : h.s.M.IsCutData v v₂ x₁ x₂)
      (hε : h.s.cls v = .eps) (hβ : ¬ h.s.M.IsAlphaCut v v₂ x₁ x₂)
      (hnz : ∀ k0, Adm0 k0 → pgap L w k0 (h.s.pr x₁ x₂) ≠ 0) (h3 : 3 ≤ h.s.M.deg v) :
      UStep4 L w Adm0 h (h.cut4Post v v₂ x₁ x₂)

variable {L γ η : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {κ : D₀ → (Fin d → ℤ)}

theorem IotaUnif.hit {h : HSt V D₀} {p : D₀ × D₀} {R : ℝ} (hI : IotaUnif Adm0 L η w h p R) (hk : Adm0 κ) :
    IotaHit L η w κ h.alive p R := by
  obtain ⟨q, hq, hcar, sg, hsg, hb⟩ := hI
  exact ⟨q, HSt.mem_alive.2 ⟨hq, hcar⟩, sg, hsg, (hb κ hk).1, (hb κ hk).2⟩

theorem IotaHit.mono {vis vis' : List (D₀ × D₀)} (hv : ∀ q ∈ vis, q ∈ vis') {p : D₀ × D₀} {R : ℝ}
    (hI : IotaHit L η w κ vis p R) : IotaHit L η w κ vis' p R := by
  obtain ⟨q, hq, sg, hsg, h1, h2⟩ := hI
  exact ⟨q, hv q hq, sg, hsg, h1, h2⟩

theorem iotaHit_twin {vis : List (D₀ × D₀)} {p p' : D₀ × D₀} {R : ℝ}
    (hI : IotaHit L η w κ vis p R) (ht : pgap L w κ p' = pgap L w κ p ∨ pgap L w κ p' = -pgap L w κ p) :
    IotaHit L η w κ vis p' R := by
  obtain ⟨q, hq, sg, hsg, h1, h2⟩ := hI
  rcases ht with ht | ht
  · exact ⟨q, hq, sg, hsg, by rwa [ht], by rwa [ht]⟩
  · refine ⟨q, hq, -sg, by rcases hsg with rfl | rfl <;> simp, ?_, ?_⟩
    · have : pgap L w κ p' + (-sg) • pgap L w κ q = -(pgap L w κ p + sg • pgap L w κ q) := by
        rw [ht, neg_smul]; abel
      rw [this, norm_neg]; exact h1
    · have : pgap L w κ p' + (-sg) • pgap L w κ q = -(pgap L w κ p + sg • pgap L w κ q) := by
        rw [ht, neg_smul]; abel
      rw [this, norm_neg]; exact h2

theorem UStep3.hstep {h h' : HSt V D₀} (hs : UStep3 L γ η w Adm0 h h') (hk : Adm0 κ) : HStep3 L γ η w κ h h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι hι' h3 =>
    refine HStep3.cut h v v₂ x₁ x₂ hc R kp hR hkp hε (hsg κ hk) (hsim κ hk) ⟨fun h50 => (hι h50).hit hk, fun hit => ?_⟩ h3
    by_contra hne
    rcases hkp with h0 | h50
    · exact hι' h0 κ hk hit
    · exact hne h50

theorem UStep4.hstep {h h' : HSt V D₀} (hs : UStep4 L w Adm0 h h') (hk : Adm0 κ) : HStep4 L w κ h h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc hε hβ hnz h3 => exact HStep4.cut h v v₂ x₁ x₂ hc hε hβ (hnz κ hk) h3

theorem UStep1.hstep {h h' : HSt V D₀} (hs : UStep1 L γ η w Adm0 h h') (hk : Adm0 κ) : HStep1 L γ η w κ h h' := by
  cases hs with
  | vine K R kp hR hkp hu hl ga gb htwin hι hι0 hsg h3a h3b =>
    refine HStep1.vine h K R kp hR hkp hu hl (ga κ hk) (gb κ hk) (htwin κ hk) ?_ ?_ (hsg κ hk) h3a h3b
    · refine ⟨fun h50 => (hι h50).hit hk, fun hit => ?_⟩
      by_contra hne
      rcases hkp with h0 | h50
      · exact (hι0 h0 κ hk).1 hit
      · exact hne h50
    · refine ⟨fun h50 => ?_, fun hit => ?_⟩
      · have h1 := (hι h50).hit hk
        exact iotaHit_twin (h1.mono fun q hq => List.mem_cons_of_mem _ hq) (htwin κ hk)
      · by_contra hne
        rcases hkp with h0 | h50
        · exact (hι0 h0 κ hk).2 hit
        · exact hne h50

theorem UStep2.hstep {h h' : HSt V D₀} (hs : UStep2 L γ η w Adm0 h h') (hk : Adm0 κ) : HStep2 L γ η w κ h h' := by
  cases hs with
  | tri T Q kp hQ hkp hsg hsim hcl hnz hι₀ hι₀' hι₁ hι₁' h3 =>
    refine HStep2.tri h T Q kp hQ hkp (hsg κ hk) (hsim κ hk) hcl (hnz κ hk) ?_ ?_ h3
    · intro he
      refine ⟨fun h50 => (hι₀ he h50).hit hk, fun hit => ?_⟩
      by_contra hne
      rcases hkp 0 with h0 | h50
      · exact hι₀' he h0 κ hk hit
      · exact hne h50
    · intro he
      refine ⟨fun h50 => ?_, fun hit => ?_⟩
      · rcases hι₁ he h50 with hu | ⟨h0e, sg, hsg, hb⟩
        · exact (hu.hit hk).mono (h.alive_sub_triVis1 T)
        · refine ⟨_, ?_, sg, hsg, (hb κ hk).1, (hb κ hk).2⟩
          unfold HSt.triVis1; rw [if_pos h0e]; exact List.mem_cons_self
      by_contra hne
      rcases hkp 1 with h0 | h50
      · exact hι₁' he h0 κ hk hit
      · exact hne h50

end WaveTurbulence.FinalCountG3
