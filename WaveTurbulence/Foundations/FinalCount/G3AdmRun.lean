/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3AdmRel
public import WaveTurbulence.Foundations.FinalCount.G3UStep
public import WaveTurbulence.Foundations.FinalCount.G3Anc
public import WaveTurbulence.Foundations.FinalCount.G3Rel
public import WaveTurbulence.Foundations.FinalCount.G3AncJoint
/-! **FINALCOUNT-G3: `AtomRelU` along the steps** (excessprop1 (1), `ι`-glue).

`EpsPin`: the charge of an `ε`-atom is constant on the class `Adm0` (derived from `M_sub` by `AncRel`/`DartRel`).
`AtomRelU` is preserved by the uniform Steps 1, 3 and 4 (Step 2 in `G3AdmRun2`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {L : ℝ} {w : Mom d}

/-- The charge of every `ε`-atom of `h` is constant on the admissible class. -/
def EpsPin (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (L : ℝ) (w : Mom d) (h : HSt V D₀) : Prop :=
  ∀ a ∈ h.s.M.atoms, h.s.cls a = .eps → ∃ c : Mom d, ∀ k0, Adm0 k0 →
    chargeAt h.s.M L w (k0 ∘ h.s.down) a = c

/-- The charges of `M_sub` are pinned on the class (the parameters `(c_v)` of `M_sub` are fixed in the piece). -/
def PinnedM0 (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (L : ℝ) (w : Mom d) (M₀ : Molecule V D₀) : Prop :=
  ∀ a ∈ M₀.atoms, ∃ c : Mom d, ∀ k0, Adm0 k0 → chargeAt M₀ L w k0 a = c

theorem epsPin_of_anc {M₀ : Molecule V D₀} {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s)
    (hp : PinnedM0 Adm0 L w M₀) : EpsPin Adm0 L w h := by
  intro a ha hε
  have haM : a ∈ M₀.atoms := by
    have := hA.mem a ha; rwa [hA.eps a ha hε] at this
  obtain ⟨c, hc⟩ := hp a haM
  refine ⟨c, fun k0 hk0 => ?_⟩
  rw [← hc k0 hk0]
  unfold chargeAt
  rw [hA.dartsAt_eps ha hε, Finset.sum_image (fun x _ y _ e => hA.inj e)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have : M₀.dartSign (h.s.down x) = h.s.M.dartSign x := by
    unfold Molecule.dartSign; rw [hD.out]
  rw [this]; rfl

theorem AtomRelX.noex {ex : V → Prop} {h : HSt V D₀} (hR : AtomRelX ex Adm0 L w h) (hn : ∀ a, ¬ ex a) :
    AtomRelX (fun _ => False) Adm0 L w h := fun a ha _ => hR a ha (hn a)

/-- A cut at an atom whose charge is pinned keeps the relation (no exemption). -/
theorem AtomRelX.cut_pin {ex : V → Prop} {h : HSt V D₀} (hR : AtomRelX ex Adm0 L w h) {v v₂ : V}
    {x₁ x₂ : h.s.D} (hcd : h.s.M.IsCutData v v₂ x₁ x₂) (c₁ c₂ : Cls) (nh : List (D₀ × D₀)) (na : V → V)
    (vis : List (D₀ × D₀))
    (hpin : ∃ c : Mom d, ∀ k0, Adm0 k0 → chargeAt h.s.M L w (k0 ∘ h.s.down) v = c) :
    AtomRelX (fun a => ex a ∧ a ≠ v ∧ a ≠ v₂) Adm0 L w
      ⟨h.s.cutSt v v₂ x₁ x₂ c₁ c₂, nh,
        Function.update (Function.update h.crec v (some (h.s.pr x₁ x₂, vis))) v₂ (some (h.s.pr x₁ x₂, vis)), na⟩ :=
  fun a ha hna q vis' hq =>
    (hR.cut hcd c₁ c₂ nh na vis) a ha
      (fun hex => hex.elim (fun h' => hna h') (fun h' => h'.2 hpin)) q vis' hq

/-! ### Step 3 and Step 4 -/

theorem AtomRelU.step3 {h : HSt V D₀} (hR : AtomRelU Adm0 L w h) (hpin : EpsPin Adm0 L w h) {v v₂ : V}
    {x₁ x₂ : h.s.D} (hcd : h.s.M.IsCutData v v₂ x₁ x₂) (hε : h.s.cls v = .eps) (R : ℝ) (kp : ℕ) :
    AtomRelU Adm0 L w (h.cut3Post v v₂ x₁ x₂ R kp) := by
  have := (hR.toX (ex := fun _ => False)).cut_pin hcd
    (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta)
    (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta) (h.s.pr x₁ x₂ :: h.hist)
    (Function.update h.anc v₂ (h.anc v)) h.alive (hpin v hcd.1 hε)
  exact fun a ha => this a ha (fun h' => h'.1) 

theorem AtomRelU.step4 {h : HSt V D₀} (hR : AtomRelU Adm0 L w h) (hpin : EpsPin Adm0 L w h) {v v₂ : V}
    {x₁ x₂ : h.s.D} (hcd : h.s.M.IsCutData v v₂ x₁ x₂) (hε : h.s.cls v = .eps) :
    AtomRelU Adm0 L w (h.cut4Post v v₂ x₁ x₂) := by
  have := (hR.toX (ex := fun _ => False)).cut_pin hcd .beta .beta (h.s.pr x₁ x₂ :: h.hist)
    (Function.update h.anc v₂ (h.anc v)) h.alive (hpin v hcd.1 hε)
  exact fun a ha => this a ha (fun h' => h'.1)

/-! ### Step 1 -/

theorem AtomRelU.step1 {h : HSt V D₀} (hR : AtomRelU Adm0 L w h) (hpin : EpsPin Adm0 L w h) (K : VineCut h.s.M)
    (hu : h.s.cls K.C.upper = .eps) (hl : h.s.cls K.C.lower = .eps) (R : ℝ) (kp : ℕ) :
    AtomRelU Adm0 L w (h.vinePost K R kp) := by
  set hc : Cls := alphaOrBeta K.post.numComponents h.s.M.numComponents R kp with hhc
  have hup : K.C.upper ∈ h.s.M.atoms := objectAtoms_sub K.C K.a_mem
  have hlo : K.C.lower ∈ h.s.M.atoms := objectAtoms_sub K.C K.b_mem
  have h1 := (hR.toX (ex := fun _ => False)).cut_pin K.cut_a hc hc (h.s.pr K.x₁ K.x₂ :: h.hist)
    (Function.update h.anc K.fa (h.anc K.C.upper)) h.alive (hpin _ hup hu)
  -- second cut, in the state after the first cut
  obtain ⟨cl, hcl⟩ := hpin _ hlo hl
  have hpin2 : ∃ c : Mom d, ∀ k0, Adm0 k0 →
      chargeAt (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ hc hc).M L w (k0 ∘ (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ hc hc).down)
        K.C.lower = c := by
    refine ⟨cl, fun k0 hk0 => ?_⟩
    show chargeAt (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂) L w (k0 ∘ h.s.down) K.C.lower = cl
    rw [chargeAt_cut_other h.s.M K.cut_a K.ab_ne.symm K.fa_ne_b.symm]
    exact hcl k0 hk0
  have h2 := h1.cut_pin (h := ⟨h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ hc hc, h.s.pr K.x₁ K.x₂ :: h.hist,
      Function.update (Function.update h.crec K.C.upper (some (h.s.pr K.x₁ K.x₂, h.alive))) K.fa
        (some (h.s.pr K.x₁ K.x₂, h.alive)), Function.update h.anc K.fa (h.anc K.C.upper)⟩) K.cut_b hc hc
    (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist) (Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower))
    (h.s.pr K.x₁ K.x₂ :: h.alive) hpin2
  exact (AtomRelX.del h2 (fun a => a ∉ K.C.atoms) K.closed (fun a _ _ hx => hx.1.1) _ _).toU


/-! ### Step 2 -/

theorem tri_crec_eq {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (T : TriData M)
    {α : Type*} (crec : V → Option α) (r0 r1 r2 : Option α) (a : V) (ha : ∀ j, a ≠ T.t j) :
    Function.update (Function.update (Function.update (Function.update (Function.update (Function.update crec
      (T.t 0) r0) (T.f 0) r0) (T.t 1) r1) (T.f 1) r1) (T.t 2) r2) (T.f 2) r2 a =
    Function.update (Function.update (Function.update crec (T.f 0) r0) (T.f 1) r1) (T.f 2) r2 a := by
  have h0 := ha 0; have h1 := ha 1; have h2 := ha 2
  have f00 := T.f_ne_t 0 0; have f01 := T.f_ne_t 0 1; have f02 := T.f_ne_t 0 2
  have f10 := T.f_ne_t 1 0; have f11 := T.f_ne_t 1 1; have f12 := T.f_ne_t 1 2
  have f20 := T.f_ne_t 2 0; have f21 := T.f_ne_t 2 1; have f22 := T.f_ne_t 2 2
  have t01 := T.t_ne (show (0 : Fin 3) ≠ 1 by decide); have t02 := T.t_ne (show (0 : Fin 3) ≠ 2 by decide)
  have t12 := T.t_ne (show (1 : Fin 3) ≠ 2 by decide)
  have g01 := T.f_ne (show (0 : Fin 3) ≠ 1 by decide); have g02 := T.f_ne (show (0 : Fin 3) ≠ 2 by decide)
  have g12 := T.f_ne (show (1 : Fin 3) ≠ 2 by decide)
  simp only [Function.update_apply]
  split_ifs <;> simp_all [eq_comm]


theorem AtomRelU.step2 {h : HSt V D₀} (hR : AtomRelU Adm0 L w h) (hpin : EpsPin Adm0 L w h)
    (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ) (hcl : PClosed T.kept (triKeep h.s T)) :
    AtomRelU Adm0 L w (h.triPost T Q kp hcl) := by
  have t01 : T.t 1 ≠ T.t 0 := T.t_ne (by decide)
  have t02 : T.t 2 ≠ T.t 0 := T.t_ne (by decide)
  have t12 : T.t 2 ≠ T.t 1 := T.t_ne (by decide)
  set c0 : Cls := if h.s.cls (T.t 0) = .eps then .beta else .ghost with hc0
  set c1 : Cls := if h.s.cls (T.t 1) = .eps then .beta else .ghost with hc1
  set c2 : Cls := if h.s.cls (T.t 2) = .eps then .beta else .ghost with hc2
  have X1 := (hR.toX (ex := fun _ => False)).cut T.cd1 .beta c0 h.hist h.anc h.alive
  have X2 := X1.cut T.cd2 .beta c1 h.hist h.anc (h.triVis1 T)
  have X3 := X2.cut T.cd3 .beta c2 h.hist h.anc (h.triVis2 T)
  have X4 := X3.del' T.TP T.pclosed h.hist h.anc
  have X5 := (X4.withCls (triCls h.s T Q kp)).del (triKeep h.s T) hcl ?_ h.hist h.anc
  · refine (X5.crec_congr (h' := h.triPost T Q kp hcl) rfl ?_).toU
    intro a ha
    have ha1 : a ∈ (T.m3.atoms.filter T.TP).filter (triKeep h.s T) := ha
    have ha2 := (Finset.mem_filter.1 (Finset.mem_filter.1 ha1).1).2
    exact (tri_crec_eq T h.crec _ _ _ a ha2).symm
  · intro a ha hk hex
    have hε : ∀ k : Fin 3, a = T.f k → h.s.cls (T.t k) = .eps := fun k hak => by
      by_contra hne; exact hk k hne hak
    rcases hex with ⟨hex2, -, -⟩ | ⟨ha2, hnp2⟩
    · rcases hex2 with ⟨hex1, -, -⟩ | ⟨ha1, hnp1⟩
      · rcases hex1 with ⟨hF, -⟩ | ⟨ha0, hnp0⟩
        · exact hF
        · exact hnp0 (hpin (T.t 0) (T.t_mem 0) (hε 0 ha0))
      · obtain ⟨c, hc⟩ := hpin (T.t 1) (T.t_mem 1) (hε 1 ha1)
        refine hnp1 ⟨c, fun k0 hk0 => ?_⟩
        show chargeAt (h.s.M.cut (T.t 0) (T.f 0) (T.a 0) (T.b 0)) L w (k0 ∘ h.s.down) (T.t 1) = c
        rw [chargeAt_cut_other h.s.M T.cd1 t01 (T.f_ne_t 0 1).symm]
        exact hc k0 hk0
    · obtain ⟨c, hc⟩ := hpin (T.t 2) (T.t_mem 2) (hε 2 ha2)
      refine hnp2 ⟨c, fun k0 hk0 => ?_⟩
      show chargeAt ((h.s.M.cut (T.t 0) (T.f 0) (T.a 0) (T.b 0)).cut (T.t 1) (T.f 1) (T.a 1) (T.b 1)) L w
        (k0 ∘ h.s.down) (T.t 2) = c
      rw [chargeAt_cut_other (h.s.M.cut (T.t 0) (T.f 0) (T.a 0) (T.b 0)) T.cd2 t12 (T.f_ne_t 1 2).symm, chargeAt_cut_other h.s.M T.cd1 t02 (T.f_ne_t 0 2).symm]
      exact hc k0 hk0

end WaveTurbulence.FinalCountG3
