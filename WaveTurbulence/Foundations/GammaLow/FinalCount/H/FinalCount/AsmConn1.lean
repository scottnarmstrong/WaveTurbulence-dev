/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmConn1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmIntact
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmS4Shape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmConn1`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (hconn0, part 1): the removal bookkeeping along the restricted Step 1.**
`ConnInv` (for a vine-only history): `anc` is injective on the atoms of the state, and the removed pieces `ps` (collected objects with
their node darts) are pairwise atom-disjoint, their atoms are no longer present `ε`-atoms, and every dart of `M₀` absent from the state
lies in the `PieceKill` of a removed piece.  `reach1_connInv`: along `Reach1`, either every collected object is dartless (a triple step
happened) or `ConnInv` holds. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- A dart whose atom after the two cuts is still in the removed set was not moved, and is a node dart at a joint. -/
theorem cutMol_atom_of_mem {M : Molecule V D₀} (K : Step1.VineCut Src.γL M) {y : D₀} (hy : K.cutMol.atom y ∈ K.C.atoms) :
    K.cutMol.atom y = M.atom y ∧ (M.atom y = K.C.upper → y = K.x₁ ∨ y = K.x₂) ∧
      (M.atom y = K.C.lower → y = K.y₁ ∨ y = K.y₂) := by
  have hsub := Step1.objectAtoms_sub K.C
  have hfa : K.fa ∉ K.C.atoms := fun h => K.fa_fresh (hsub h)
  have hfb : K.fb ∉ K.C.atoms := fun h => K.fb_fresh (hsub h)
  have hC : K.cutMol.atom y = if (if M.atom y = K.C.upper ∧ y ≠ K.x₁ ∧ y ≠ K.x₂ then K.fa else M.atom y) = K.C.lower ∧
      y ≠ K.y₁ ∧ y ≠ K.y₂ then K.fb else (if M.atom y = K.C.upper ∧ y ≠ K.x₁ ∧ y ≠ K.x₂ then K.fa else M.atom y) := rfl
  rw [hC] at hy ⊢
  by_cases h1 : M.atom y = K.C.upper ∧ y ≠ K.x₁ ∧ y ≠ K.x₂
  · rw [if_pos h1] at hy
    have hne : K.fa ≠ K.C.lower := K.fa_ne_b
    rw [if_neg (fun h => hne h.1)] at hy
    exact absurd hy hfa
  · rw [if_neg h1] at hy ⊢
    by_cases h2 : M.atom y = K.C.lower ∧ y ≠ K.y₁ ∧ y ≠ K.y₂
    · rw [if_pos h2] at hy
      exact absurd hy hfb
    · rw [if_neg h2]
      refine ⟨rfl, fun e => ?_, fun e => ?_⟩
      · by_contra hc; push Not at hc; exact h1 ⟨e, hc⟩
      · by_contra hc; push Not at hc; exact h2 ⟨e, hc⟩

/-- The bookkeeping invariant of a vine-only history (exact form): `anc` is injective on the state atoms; the removed pieces `ps` are
collected, pairwise atom-disjoint, their atoms are gone, the absent darts of `M₀` are exactly the killed ones, the state atoms are exactly
the non-interior atoms of `M₀` (through `anc`), and a non-first-stage piece forces every first-stage object to be dartless. -/
def ConnData (M₀ : Molecule V D₀) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀))
    (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) (ps : List (Src.Object Src.γL M₀ × Quad D₀)) : Prop :=
  (∀ c ∈ h.s.M.atoms, ∀ b ∈ h.s.M.atoms, h.anc c = h.anc b → c = b) ∧
  (∀ p ∈ ps, PieceData C Un L γ η w κ p) ∧
    ps.Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms) ∧
    (∀ p ∈ ps, ∀ a ∈ p.1.atoms, ¬ (a ∈ h.s.M.atoms ∧ h.s.cls a = .eps)) ∧
    (∀ z : D₀, (∀ x : h.s.D, h.s.down x ≠ z) → ∃ p ∈ ps, z ∈ PieceKill p.1 p.2) ∧
    (∀ x : h.s.D, ∀ p ∈ ps, h.s.down x ∉ PieceKill p.1 p.2) ∧
    (∀ v ∈ M₀.atoms, (∀ p ∈ ps, ¬ PieceInt p.1 v) → ∃ c ∈ h.s.M.atoms, h.anc c = v) ∧
    (∀ c ∈ h.s.M.atoms, ∀ p ∈ ps, ¬ PieceInt p.1 (h.anc c)) ∧
    ((∃ p ∈ ps, p.1 ∉ Fst) → ∀ U ∈ Fst, Dartless U h)

/-- `ConnData` for some list of removed pieces. -/
def ConnInv (M₀ : Molecule V D₀) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀))
    (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∃ ps, ConnData M₀ C Un Fst L γ η w κ h ps

theorem connData_init (M₀ : Molecule V D₀) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀))
    (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : ConnData M₀ C Un Fst L γ η w κ (HSt.init M₀) [] := by
  refine ⟨fun c _ b _ h => h, by simp, by simp, by simp, fun z hz => absurd rfl (hz z), by simp, ?_, by simp, by simp⟩
  intro v hv _
  exact ⟨v, hv, rfl⟩

theorem anc_inj_vinePost {b : HSt V D₀} (K : Step1.VineCut Src.γL b.s.M)
    (hinj : ∀ c ∈ b.s.M.atoms, ∀ e ∈ b.s.M.atoms, b.anc c = b.anc e → c = e) (R : ℝ) (kp : ℕ) :
    ∀ c ∈ (b.vinePostL K R kp).s.M.atoms, ∀ e ∈ (b.vinePostL K R kp).s.M.atoms,
      (b.vinePostL K R kp).anc c = (b.vinePostL K R kp).anc e → c = e := by
  have hsub := Step1.objectAtoms_sub K.C
  have hup : K.C.upper ∈ b.s.M.atoms := hsub K.a_mem
  have hlo : K.C.lower ∈ b.s.M.atoms := hsub K.b_mem
  have hanc : (b.vinePostL K R kp).anc = Function.update (Function.update b.anc K.fa (b.anc K.C.upper)) K.fb (b.anc K.C.lower) := rfl
  have hpost : (b.vinePostL K R kp).s.M.atoms = (insert K.fb (insert K.fa b.s.M.atoms)).filter (fun a => a ∉ K.C.atoms) := rfl
  have hcase : ∀ c ∈ (b.vinePostL K R kp).s.M.atoms, c = K.fb ∨ c = K.fa ∨ (c ∈ b.s.M.atoms ∧ c ∉ K.C.atoms) := by
    intro c hc
    rw [hpost, Finset.mem_filter, Finset.mem_insert, Finset.mem_insert] at hc
    rcases hc with ⟨h1 | h1 | h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
  have hev : ∀ c, c ∈ b.s.M.atoms → (b.vinePostL K R kp).anc c = b.anc c := by
    intro c hc
    rw [hanc, Function.update_of_ne (fun e => K.fb_fresh (by rw [← e]; exact hc)), Function.update_of_ne (fun e => K.fa_fresh (by rw [← e]; exact hc))]
  have hfa : (b.vinePostL K R kp).anc K.fa = b.anc K.C.upper := by
    rw [hanc, Function.update_of_ne K.fa_ne_fb, Function.update_self]
  have hfb : (b.vinePostL K R kp).anc K.fb = b.anc K.C.lower := by
    rw [hanc, Function.update_self]
  have hab : b.anc K.C.upper ≠ b.anc K.C.lower := fun e' => K.ab_ne (hinj _ hup _ hlo e')
  have hold : ∀ c, c ∈ b.s.M.atoms → c ∉ K.C.atoms → b.anc c ≠ b.anc K.C.upper ∧ b.anc c ≠ b.anc K.C.lower := by
    intro c hc hcC
    exact ⟨fun e => hcC (hinj _ hc _ hup e ▸ K.a_mem), fun e => hcC (hinj _ hc _ hlo e ▸ K.b_mem)⟩
  intro c hc e he hce
  rcases hcase c hc with rfl | rfl | ⟨c1, c2⟩ <;> rcases hcase e he with rfl | rfl | ⟨e1, e2⟩
  · rfl
  · rw [hfb, hfa] at hce; exact absurd hce.symm hab
  · rw [hfb, hev _ e1] at hce; exact absurd hce.symm (hold e e1 e2).2
  · rw [hfb, hfa] at hce; exact absurd hce hab
  · rfl
  · rw [hfa, hev _ e1] at hce; exact absurd hce.symm (hold e e1 e2).1
  · rw [hfb, hev _ c1] at hce; exact absurd hce (hold c c1 c2).2
  · rw [hfa, hev _ c1] at hce; exact absurd hce (hold c c1 c2).1
  · rw [hev _ c1, hev _ e1] at hce; exact hinj _ c1 _ e1 hce

theorem connData_vine [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc)
    {ps : List (Src.Object Src.γL M₀ × Quad D₀)} (hI : ConnData M₀ C Un Fst L γ η w κ b ps) (K : Step1.VineCut Src.γL b.s.M) (R : ℝ) (kp : ℕ) (U : Src.Object Src.γL M₀)
    (hU : Collected C (Un κ) L γ η w κ U) (hUK : U.atoms = K.C.atoms)
    (hUD : U.ContainsDart (b.s.down K.x₁) ∧ U.ContainsDart (b.s.down K.x₂) ∧ U.ContainsDart (b.s.down K.y₁) ∧
      U.ContainsDart (b.s.down K.y₂))
    (hUJ : (M₀.atom (b.s.down K.x₁) = U.upper ∧ M₀.atom (b.s.down K.y₁) = U.lower) ∨
      (M₀.atom (b.s.down K.x₁) = U.lower ∧ M₀.atom (b.s.down K.y₁) = U.upper))
    (hord : U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' b)
    (hint : UIntact U b) : ConnData M₀ C Un Fst L γ η w κ (b.vinePostL K R kp)
      ((U, (b.s.down K.x₁, b.s.down K.x₂, b.s.down K.y₁, b.s.down K.y₂)) :: ps) := by
  obtain ⟨hinj, hps, hpw, hrem, hpres, he1, he2, he3, hfo⟩ := hI
  have hUe : ∀ v ∈ K.C.atoms, b.anc v = v := fun v hv => by
    have hv' : v ∈ U.atoms := by rw [hUK]; exact hv
    exact hA.eps v (hint v hv').1 (hint v hv').2
  have hpost : (b.vinePostL K R kp).s.M.atoms = (insert K.fb (insert K.fa b.s.M.atoms)).filter (fun a => a ∉ K.C.atoms) := rfl
  have hup : M₀.atom (b.s.down K.x₁) = K.C.upper := by
    rw [hA.atom, K.cut_a.2.2.1, hUe _ K.a_mem]
  have hlow : M₀.atom (b.s.down K.y₁) = K.C.lower := by
    rw [hA.atom, K.My₁, hUe _ K.b_mem]
  have hJ : (K.C.upper = U.upper ∧ K.C.lower = U.lower) ∨ (K.C.upper = U.lower ∧ K.C.lower = U.upper) := by
    rcases hUJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨hup ▸ e1, hlow ▸ e2⟩
    · exact Or.inr ⟨hup ▸ e1, hlow ▸ e2⟩
  have hJ' : ∀ v, (v = K.C.upper ∨ v = K.C.lower) → (v = U.upper ∨ v = U.lower) := by
    intro v hv
    rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hv with rfl | rfl
    · exact Or.inl e1
    · exact Or.inr e2
    · exact Or.inr e1
    · exact Or.inl e2
  -- an atom of the state whose ancestor lies in `U` is in `K.C`
  have hback : ∀ c ∈ b.s.M.atoms, b.anc c ∈ U.atoms → c = b.anc c := fun c hc hu =>
    hA.uniq c hc (b.anc c) (hint _ hu).1 (hint _ hu).2 rfl
  have hold : ∀ c ∈ b.s.M.atoms, c ∉ K.C.atoms → b.anc c ∉ U.atoms := by
    intro c hc hcC hu
    exact hcC (by rw [← hUK, hback c hc hu]; exact hu)
  have hfa_cls : ∀ c, c = K.fb ∨ c = K.fa → (b.vinePostL K R kp).s.cls c ≠ .eps := by
    intro c hc
    have hcl : (b.vinePostL K R kp).s.cls = (vineSt b.s K (alphaOrBeta K.post.numComponents b.s.M.numComponents R kp)).cls := rfl
    rcases hc with rfl | rfl
    · rw [hcl, vineSt_cls_fb_AsmP1Basic]; exact alphaOrBeta_ne_eps _ _ _ _
    · rw [hcl, vineSt_cls_fa_AsmP1Basic]; exact alphaOrBeta_ne_eps _ _ _ _
  have hanc : (b.vinePostL K R kp).anc = Function.update (Function.update b.anc K.fa (b.anc K.C.upper)) K.fb (b.anc K.C.lower) := rfl
  have hev : ∀ c, c ∈ b.s.M.atoms → (b.vinePostL K R kp).anc c = b.anc c := by
    intro c hc
    rw [hanc, Function.update_of_ne (fun e => K.fb_fresh (by rw [← e]; exact hc)),
      Function.update_of_ne (fun e => K.fa_fresh (by rw [← e]; exact hc))]
  have hfaE : (b.vinePostL K R kp).anc K.fa = K.C.upper := by
    rw [hanc, Function.update_of_ne K.fa_ne_fb, Function.update_self, hUe _ K.a_mem]
  have hfbE : (b.vinePostL K R kp).anc K.fb = K.C.lower := by
    rw [hanc, Function.update_self, hUe _ K.b_mem]
  refine ⟨anc_inj_vinePost K hinj R kp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · refine ⟨hU, hUD, hUJ, ?_, ?_, ?_, ?_⟩
      · rw [hA.atom, hA.atom, K.Mx₂, K.cut_a.2.2.1]
      · rw [hA.atom, hA.atom, K.My₂, K.My₁]
      · intro e
        have h1 := K.cut_a.2.2.2.2.2.1
        have h2 := K.cut_a.2.2.2.2.2.2
        rw [hA.inj e] at h1; rw [h1] at h2; cases h2
      · intro e
        have h1 := K.cut_b.2.2.2.2.2.1
        have h2 := K.cut_b.2.2.2.2.2.2
        rw [hA.inj e] at h1; rw [h1] at h2; cases h2
    · exact hps p hp
  · refine List.pairwise_cons.2 ⟨fun q hq => ?_, hpw⟩
    refine Finset.disjoint_left.2 fun v hv hvq => ?_
    exact hrem q hq v hvq (hint v hv)
  · intro p hp a ha ⟨h1, h2⟩
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [hpost, Finset.mem_filter] at h1
      exact h1.2 (hUK ▸ ha)
    · rw [hpost, Finset.mem_filter, Finset.mem_insert, Finset.mem_insert] at h1
      obtain ⟨h1, h3⟩ := h1
      have hc : (b.vinePostL K R kp).s.cls = (vineSt b.s K (alphaOrBeta K.post.numComponents b.s.M.numComponents R kp)).cls := rfl
      rcases h1 with rfl | rfl | h1
      · rw [hc, vineSt_cls_fb_AsmP1Basic] at h2; exact alphaOrBeta_ne_eps _ _ _ _ h2
      · rw [hc, vineSt_cls_fa_AsmP1Basic] at h2; exact alphaOrBeta_ne_eps _ _ _ _ h2
      · rw [hc, vineSt_cls_old_AsmP1Basic b.s K _ h1 h3] at h2
        exact hrem p hp a ha ⟨h1, h2⟩
  · intro z hz
    by_cases hx : ∃ x : b.s.D, b.s.down x = z
    · obtain ⟨x, rfl⟩ := hx
      have hn : K.cutMol.atom x ∈ K.C.atoms := by
        by_contra hn
        exact hz ⟨x, hn⟩ rfl
      obtain ⟨hca, hj1, hj2⟩ := cutMol_atom_of_mem K hn
      have hMx : b.s.M.atom x ∈ K.C.atoms := hca ▸ hn
      have hz1 : M₀.atom (b.s.down x) = b.s.M.atom x := by rw [hA.atom, hUe _ hMx]
      refine ⟨(U, (b.s.down K.x₁, b.s.down K.x₂, b.s.down K.y₁, b.s.down K.y₂)), List.mem_cons_self, ?_, ?_⟩
      · show M₀.atom (b.s.down x) ∈ U.atoms
        rw [hz1, hUK]; exact hMx
      · intro hj
        rw [hz1] at hj
        have key : (b.s.M.atom x = K.C.upper ∨ b.s.M.atom x = K.C.lower) := by
          rcases hUJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [hup] at e1; rw [hlow] at e2
            rcases hj with h | h
            · exact Or.inl (h.trans e1.symm)
            · exact Or.inr (h.trans e2.symm)
          · rw [hup] at e1; rw [hlow] at e2
            rcases hj with h | h
            · exact Or.inr (h.trans e2.symm)
            · exact Or.inl (h.trans e1.symm)
        rcases key with k | k
        · rcases hj1 k with e | e <;> simp [e]
        · rcases hj2 k with e | e <;> simp [e]
    · push Not at hx
      obtain ⟨p, hp, hk⟩ := hpres z hx
      exact ⟨p, List.mem_cons_of_mem _ hp, hk⟩
  · -- present darts are not killed
    intro x p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · intro hk
      have hat : M₀.atom (b.s.down x.1) ∈ U.atoms := hk.1
      have himp : (M₀.atom (b.s.down x.1) = U.upper ∨ M₀.atom (b.s.down x.1) = U.lower) →
          (b.s.down x.1 = b.s.down K.x₁ ∨ b.s.down x.1 = b.s.down K.x₂ ∨ b.s.down x.1 = b.s.down K.y₁ ∨
            b.s.down x.1 = b.s.down K.y₂) := hk.2
      have hy : K.cutMol.atom x.1 ∉ K.C.atoms := x.2
      have hz1 : M₀.atom (b.s.down x.1) = b.anc (b.s.M.atom x.1) := hA.atom x.1
      have hu : b.anc (b.s.M.atom x.1) ∈ U.atoms := hz1 ▸ hat
      have hMx : b.s.M.atom x.1 = b.anc (b.s.M.atom x.1) := hback _ (b.s.M.atom_mem x.1) hu
      have hMxC : b.s.M.atom x.1 ∈ K.C.atoms := by
        have h1 : b.anc (b.s.M.atom x.1) ∈ K.C.atoms := (Finset.ext_iff.1 hUK _).1 hu
        rw [hMx]; exact h1
      have hmv := cutMol_atom_moved K hMxC hy
      have hzj : M₀.atom (b.s.down x.1) = b.s.M.atom x.1 := by rw [hz1, ← hMx]
      have hmj : M₀.atom (b.s.down x.1) = U.upper ∨ M₀.atom (b.s.down x.1) = U.lower := by
        rcases hmv with ⟨e, -, -⟩ | ⟨e, -, -⟩
        · exact hJ' _ (Or.inl (hzj.trans e))
        · exact hJ' _ (Or.inr (hzj.trans e))
      have hN := himp hmj
      have hinjd := hA.inj
      rcases hmv with ⟨e, n1, n2⟩ | ⟨e, n1, n2⟩
      · rcases hN with e' | e' | e' | e'
        · exact n1 (hinjd e')
        · exact n2 (hinjd e')
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (e.symm.trans K.My₁)
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (e.symm.trans K.My₂)
      · rcases hN with e' | e' | e' | e'
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (K.Mx₁.symm.trans e)
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (K.Mx₂.symm.trans e)
        · exact n1 (hinjd e')
        · exact n2 (hinjd e')
    · exact he1 x.1 p hp
  · -- atoms are exactly the non-interior atoms
    intro v hv hvn
    have hvn' : ∀ p ∈ ps, ¬ PieceInt p.1 v := fun p hp => hvn p (List.mem_cons_of_mem _ hp)
    obtain ⟨c, hc, hcv⟩ := he2 v hv hvn'
    have hnU : ¬ PieceInt U v := hvn _ List.mem_cons_self
    by_cases hcC : c ∈ K.C.atoms
    · have hvU : v ∈ U.atoms := by rw [hUK, ← hcv, hUe _ hcC]; exact hcC
      have hvj : v = U.upper ∨ v = U.lower := by
        by_contra hcon
        push Not at hcon
        exact hnU ⟨hvU, hcon.1, hcon.2⟩
      have hcv' : c = v := by rw [← hcv, hUe _ hcC]
      rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rcases hvj with rfl | rfl
        · refine ⟨K.fa, ?_, ?_⟩
          · rw [hpost, Finset.mem_filter]
            exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun h => K.fa_fresh (Step1.objectAtoms_sub K.C h)⟩
          · rw [hfaE, e1]
        · refine ⟨K.fb, ?_, ?_⟩
          · rw [hpost, Finset.mem_filter]
            exact ⟨Finset.mem_insert_self _ _, fun h => K.fb_fresh (Step1.objectAtoms_sub K.C h)⟩
          · rw [hfbE, e2]
      · rcases hvj with rfl | rfl
        · refine ⟨K.fb, ?_, ?_⟩
          · rw [hpost, Finset.mem_filter]
            exact ⟨Finset.mem_insert_self _ _, fun h => K.fb_fresh (Step1.objectAtoms_sub K.C h)⟩
          · rw [hfbE, e2]
        · refine ⟨K.fa, ?_, ?_⟩
          · rw [hpost, Finset.mem_filter]
            exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun h => K.fa_fresh (Step1.objectAtoms_sub K.C h)⟩
          · rw [hfaE, e1]
    · refine ⟨c, ?_, ?_⟩
      · rw [hpost, Finset.mem_filter]
        exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc), hcC⟩
      · rw [hev c hc, hcv]
  · -- no state atom is the ancestor of an interior atom of a removed piece
    intro c hc p hp
    rw [hpost, Finset.mem_filter, Finset.mem_insert, Finset.mem_insert] at hc
    obtain ⟨hc1, hc2⟩ := hc
    rcases List.mem_cons.1 hp with rfl | hp
    · rintro ⟨hat, hn1, hn2⟩
      rcases hc1 with rfl | rfl | hc1
      · rw [hfbE] at hat hn1 hn2
        rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact hn2 e2
        · exact hn1 e2
      · rw [hfaE] at hat hn1 hn2
        rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact hn1 e1
        · exact hn2 e1
      · rw [hev c hc1] at hat
        exact hold c hc1 hc2 hat
    · rcases hc1 with rfl | rfl | hc1
      · rw [hfbE]
        intro hpi
        have := he3 K.C.lower (Step1.objectAtoms_sub K.C K.b_mem) p hp
        rw [hUe _ K.b_mem] at this
        exact this hpi
      · rw [hfaE]
        intro hpi
        have := he3 K.C.upper (Step1.objectAtoms_sub K.C K.a_mem) p hp
        rw [hUe _ K.a_mem] at this
        exact this hpi
      · rw [hev c hc1]
        exact he3 c hc1 p hp
  · -- first-stage order
    intro ⟨p, hp, hpF⟩ U' hU'
    have hshr : ∀ U'' ∈ Fst, Dartless U'' b := by
      rcases List.mem_cons.1 hp with rfl | hp
      · rcases hord with h1 | h1
        · exact absurd h1 hpF
        · exact h1
      · exact hfo ⟨p, hp, hpF⟩
    intro x hx
    exact hshr U' hU' x.1 hx


/-- **Along the restricted Step 1, either every collected object is dartless (a triple step has happened) or the removal bookkeeping
`ConnInv` holds.** -/
theorem reach1_connInv [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} (hS : SubHyp Rn M₀) {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ U U' : Src.Object Src.γL M₀, Collected C (Un κ) L γ η w κ U → Collected C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    {h : HSt V D₀} (hr : Reach1 C Un Fst L γ η w κ h) :
    (∀ U, Collected C (Un κ) L γ η w κ U → Dartless U h) ∨ ConnInv M₀ C Un Fst L γ η w κ h := by
  induction hr with
  | refl => exact Or.inr ⟨[], connData_init M₀ C Un Fst L γ η w κ⟩
  | @tail b h' hrb hs ih =>
    have hrb' : Reach1 C Un Fst L γ η w κ b := hrb
    have hA := reach1_ancRel hrb'
    cases hs with
    | vine K R kp hs U hU hUK hUD hUJ hord =>
      rcases ih with hd | hI
      · exact absurd (hUD.1) (hd U hU K.x₁)
      · right
        have hint : UIntact U b := by
          rcases collInv_of_reach1 hS h0 hdisj hrb' U hU with hd | hi
          · exact absurd (hUD.1) (hd K.x₁)
          · exact hi
        obtain ⟨ps, hI⟩ := hI
        exact ⟨_, connData_vine hA hI K R kp U hU hUK hUD hUJ hord hint⟩
    | triple _ hs hs3 hall _ =>
      left
      intro U hU x hx
      cases hs3 with
      | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes => exact hall U hU x hx

end WaveTurbulence.GammaLow.FinalCount.H
