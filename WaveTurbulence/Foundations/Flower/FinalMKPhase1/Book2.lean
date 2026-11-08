/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Book

/-! # C1b1 MK-PHASE1 (7): `GeomBook` along an ancestor-matched removal

`GeomBook.vineG` (Step D1 / re-cut, `vinePostG`) and `GeomBook.vine` (`vinePost`): main's `connDataL_vine(G)`
(LowChain20) and `connExtraL_vine(G)` (LowChain23) merged and stated for an ancestor-matched removal (`RemA`); the new
piece is `(U, quadK b K)`. Copied by source, with `anc K.C.upper`/`anc K.C.lower` in place of the joints and the
injectivity of `anc` in place of intactness (sha256 in COPIED-SHA256SUMS). -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

section step
variable {M₀ : Molecule V D₀}

/-- **The bookkeeping along an ancestor-matched removal by `vinePostG`** (Step D1 or a re-cut). -/
theorem GeomBook.vineG {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc) {rs : List (Object M₀ × Quad D₀)}
    (hG : GeomBook M₀ b rs) (K : VineCut b.s.M) (U : Object M₀) (hR : RemA M₀ b K U) :
    GeomBook M₀ (b.vinePostG K) ((U, quadK b K) :: rs) := by
  obtain ⟨hinj, hrem, hpres, he1, he2, he3, hne⟩ := hG
  obtain ⟨⟨hup, -, hlow, -⟩, hJ, hin, hat⟩ := hR.facts hA hinj
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hR.kill hA hinj
  have hUD := hR.2.1
  have hpost : (b.vinePostG K).s.M.atoms = (insert K.fb (insert K.fa b.s.M.atoms)).filter (VineKeep K) := rfl
  have hupm : K.C.upper ∈ b.s.M.atoms := objectAtoms_sub K.C K.a_mem
  have hlom : K.C.lower ∈ b.s.M.atoms := objectAtoms_sub K.C K.b_mem
  have hJ' : ∀ c, (c = K.C.upper ∨ c = K.C.lower) → (b.anc c = U.upper ∨ b.anc c = U.lower) := by
    intro c hc
    rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hc with rfl | rfl
    · exact Or.inl e1
    · exact Or.inr e2
    · exact Or.inr e1
    · exact Or.inl e2
  have hJr : ∀ v, (v = U.upper ∨ v = U.lower) → (v = b.anc K.C.upper ∨ v = b.anc K.C.lower) := by
    intro v hv
    rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hv with rfl | rfl
    · exact Or.inl e1.symm
    · exact Or.inr e2.symm
    · exact Or.inr e2.symm
    · exact Or.inl e1.symm
  have hold : ∀ c ∈ b.s.M.atoms, c ∉ K.C.atoms → b.anc c ∉ U.atoms := fun c hc hcC hu => hcC (hin c hc hu)
  have hcl : (b.vinePostG K).s.cls = (vineStG b.s K).cls := rfl
  have hanc : (b.vinePostG K).anc =
      Function.update (Function.update b.anc K.fa (b.anc K.C.upper)) K.fb (b.anc K.C.lower) := rfl
  have hev : ∀ c, c ∈ b.s.M.atoms → (b.vinePostG K).anc c = b.anc c := by
    intro c hc
    rw [hanc, Function.update_of_ne (fun e => K.fb_fresh (by rw [← e]; exact hc)),
      Function.update_of_ne (fun e => K.fa_fresh (by rw [← e]; exact hc))]
  have hfaE : (b.vinePostG K).anc K.fa = b.anc K.C.upper := by
    rw [hanc, Function.update_of_ne K.fa_ne_fb, Function.update_self]
  have hfbE : (b.vinePostG K).anc K.fb = b.anc K.C.lower := by
    rw [hanc, Function.update_self]
  have hKu : b.s.M.deg K.C.upper = 2 → ∀ z, M₀.atom z = b.anc K.C.upper → z ∈ KillS ((U, quadK b K) :: rs) :=
    fun hd => joint_killed_of_deg2A hA hinj hpres U _ hupm hd K.Mx₁ K.Mx₂ (vineCut_x_ne K) hk1 hk2
  have hKl : b.s.M.deg K.C.lower = 2 → ∀ z, M₀.atom z = b.anc K.C.lower → z ∈ KillS ((U, quadK b K) :: rs) :=
    fun hd => joint_killed_of_deg2A hA hinj hpres U _ hlom hd K.My₁ K.My₂ (vineCut_y_ne K) hk3 hk4
  have hfa_mem : b.s.M.deg K.C.upper ≠ 2 → K.fa ∈ (b.vinePostG K).s.M.atoms := fun hd => by
    rw [hpost, Finset.mem_filter]
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
      fun h => K.fa_fresh (objectAtoms_sub K.C h), fun ⟨_, h⟩ => hd h, fun ⟨e, _⟩ => K.fa_ne_fb e⟩
  have hfb_mem : b.s.M.deg K.C.lower ≠ 2 → K.fb ∈ (b.vinePostG K).s.M.atoms := fun hd => by
    rw [hpost, Finset.mem_filter]
    exact ⟨Finset.mem_insert_self _ _,
      fun h => K.fb_fresh (objectAtoms_sub K.C h), fun ⟨e, _⟩ => K.fa_ne_fb e.symm, fun ⟨_, h⟩ => hd h⟩
  have hcases : ∀ c ∈ (b.vinePostG K).s.M.atoms, c = K.fb ∨ c = K.fa ∨ (c ∈ b.s.M.atoms ∧ c ∉ K.C.atoms) := by
    intro c hc
    rw [hpost, Finset.mem_filter, Finset.mem_insert, Finset.mem_insert] at hc
    obtain ⟨h1, h3⟩ := hc
    rcases h1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨h1, h3.1⟩)
  refine ⟨anc_inj_vinePostG K hinj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- removed atoms are not present `ε`-atoms
    intro p hp a ha ⟨h1, h2⟩
    rcases hcases a h1 with rfl | rfl | ⟨h1, h3⟩
    · rw [hcl, vineStG_cls_fb] at h2; exact jcls_ne_eps _ _ h2
    · rw [hcl, vineStG_cls_fa] at h2; exact jcls_ne_eps _ _ h2
    · rw [hcl, vineStG_cls_old b.s K h3 h1] at h2
      rcases List.mem_cons.1 hp with rfl | hp
      · have he : b.anc a = a := hA.eps a h1 h2
        exact h3 (hin a h1 (by rw [he]; exact ha))
      · exact hrem p hp a ha ⟨h1, h2⟩
  · -- absent darts are killed
    intro z hz
    by_cases hx : ∃ x : b.s.D, b.s.down x = z
    · obtain ⟨x, rfl⟩ := hx
      have hn : K.cutMol.atom x ∈ K.C.atoms := by
        by_contra hn
        exact hz ⟨x, vineG_keep_of_not_mem K hn⟩ rfl
      obtain ⟨hca, hj1, hj2⟩ := cutMol_atom_of_mem K hn
      have hMx : b.s.M.atom x ∈ K.C.atoms := hca ▸ hn
      have hz1 : M₀.atom (b.s.down x) = b.anc (b.s.M.atom x) := hA.atom x
      refine ⟨(U, quadK b K), List.mem_cons_self, ?_, ?_⟩
      · show M₀.atom (b.s.down x) ∈ U.atoms
        rw [hz1]; exact hat _ hMx
      · intro hj
        rw [hz1] at hj
        have key : b.s.M.atom x = K.C.upper ∨ b.s.M.atom x = K.C.lower := by
          rcases hJr _ hj with e | e
          · exact Or.inl (hinj _ (b.s.M.atom_mem x) _ hupm e)
          · exact Or.inr (hinj _ (b.s.M.atom_mem x) _ hlom e)
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
      have hat' : M₀.atom (b.s.down x.1) ∈ U.atoms := hk.1
      have himp : (M₀.atom (b.s.down x.1) = U.upper ∨ M₀.atom (b.s.down x.1) = U.lower) →
          (b.s.down x.1 = b.s.down K.x₁ ∨ b.s.down x.1 = b.s.down K.x₂ ∨ b.s.down x.1 = b.s.down K.y₁ ∨
            b.s.down x.1 = b.s.down K.y₂) := hk.2
      have hy : K.cutMol.atom x.1 ∉ K.C.atoms := x.2.1
      have hz1 : M₀.atom (b.s.down x.1) = b.anc (b.s.M.atom x.1) := hA.atom x.1
      have hMxC : b.s.M.atom x.1 ∈ K.C.atoms := hin _ (b.s.M.atom_mem x.1) (hz1 ▸ hat')
      have hmv := cutMol_atom_moved K hMxC hy
      have hmj : M₀.atom (b.s.down x.1) = U.upper ∨ M₀.atom (b.s.down x.1) = U.lower := by
        rw [hz1]
        rcases hmv with ⟨e, -, -⟩ | ⟨e, -, -⟩
        · rw [e]; exact hJ' _ (Or.inl rfl)
        · rw [e]; exact hJ' _ (Or.inr rfl)
      have hN' := himp hmj
      have hinjd := hA.inj
      rcases hmv with ⟨e, n1, n2⟩ | ⟨e, n1, n2⟩
      · rcases hN' with e' | e' | e' | e'
        · exact n1 (hinjd e')
        · exact n2 (hinjd e')
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (e.symm.trans K.My₁)
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (e.symm.trans K.My₂)
      · rcases hN' with e' | e' | e' | e'
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (K.Mx₁.symm.trans e)
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (K.Mx₂.symm.trans e)
        · exact n1 (hinjd e')
        · exact n2 (hinjd e')
    · exact he1 x.1 p hp
  · -- atoms: ancestor of a state atom, or all darts killed
    intro v hv hvn
    have hvn' : ∀ p ∈ rs, ¬ PieceInt p.1 v := fun p hp => hvn p (List.mem_cons_of_mem _ hp)
    have hnU : ¬ PieceInt U v := hvn _ List.mem_cons_self
    rcases he2 v hv hvn' with ⟨c, hc, hcv⟩ | hk
    · by_cases hcC : c ∈ K.C.atoms
      · have hvU : v ∈ U.atoms := by rw [← hcv]; exact hat c hcC
        have hvj : v = U.upper ∨ v = U.lower := by
          by_contra hcon
          push Not at hcon
          exact hnU ⟨hvU, hcon.1, hcon.2⟩
        rcases hJr v hvj with hvu | hvl
        · by_cases hd : b.s.M.deg K.C.upper = 2
          · right; rw [hvu]; exact hKu hd
          · left; exact ⟨K.fa, hfa_mem hd, by rw [hfaE, hvu]⟩
        · by_cases hd : b.s.M.deg K.C.lower = 2
          · right; rw [hvl]; exact hKl hd
          · left; exact ⟨K.fb, hfb_mem hd, by rw [hfbE, hvl]⟩
      · left
        refine ⟨c, ?_, ?_⟩
        · rw [hpost, Finset.mem_filter]
          exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc), hcC,
            by rintro ⟨e, -⟩; exact K.fa_fresh (e ▸ hc), by rintro ⟨e, -⟩; exact K.fb_fresh (e ▸ hc)⟩
        · rw [hev c hc, hcv]
    · right
      intro z hz
      obtain ⟨p, hp, hkz⟩ := hk z hz
      exact ⟨p, List.mem_cons_of_mem _ hp, hkz⟩
  · -- no state atom is the ancestor of an interior atom of a removed piece
    intro c hc p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · rintro ⟨hat', hn1, hn2⟩
      rcases hcases c hc with rfl | rfl | ⟨hc1, hc2⟩
      · rw [hfbE] at hn1 hn2
        rcases hJ' _ (Or.inr rfl) with e | e
        · exact hn1 e
        · exact hn2 e
      · rw [hfaE] at hn1 hn2
        rcases hJ' _ (Or.inl rfl) with e | e
        · exact hn1 e
        · exact hn2 e
      · rw [hev c hc1] at hat'
        exact hold c hc1 hc2 hat'
    · rcases hcases c hc with rfl | rfl | ⟨hc1, -⟩
      · rw [hfbE]; exact he3 K.C.lower hlom p hp
      · rw [hfaE]; exact he3 K.C.upper hupm p hp
      · rw [hev c hc1]; exact he3 c hc1 p hp
  · -- every non-`ε` atom descends from a removed piece
    intro c hc hce
    rcases hcases c hc with rfl | rfl | ⟨hc1, hc2⟩
    · exact ⟨(U, quadK b K), List.mem_cons_self, by rw [hfbE]; exact hat _ K.b_mem⟩
    · exact ⟨(U, quadK b K), List.mem_cons_self, by rw [hfaE]; exact hat _ K.a_mem⟩
    · rw [hcl, vineStG_cls_old b.s K hc2 hc1] at hce
      obtain ⟨p, hp, hpa⟩ := hne c hc1 hce
      exact ⟨p, List.mem_cons_of_mem _ hp, by rw [hev c hc1]; exact hpa⟩

/-- **The bookkeeping along an ancestor-matched removal by `vinePost`** (an ordinary vine step). -/
theorem GeomBook.vine {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc) {rs : List (Object M₀ × Quad D₀)}
    (hG : GeomBook M₀ b rs) (K : VineCut b.s.M) (R : ℝ) (kp : ℕ) (U : Object M₀) (hR : RemA M₀ b K U) :
    GeomBook M₀ (b.vinePost K R kp) ((U, quadK b K) :: rs) := by
  obtain ⟨hinj, hrem, hpres, he1, he2, he3, hne⟩ := hG
  obtain ⟨⟨hup, -, hlow, -⟩, hJ, hin, hat⟩ := hR.facts hA hinj
  have hpost : (b.vinePost K R kp).s.M.atoms =
      (insert K.fb (insert K.fa b.s.M.atoms)).filter (fun a => a ∉ K.C.atoms) := rfl
  have hupm : K.C.upper ∈ b.s.M.atoms := objectAtoms_sub K.C K.a_mem
  have hlom : K.C.lower ∈ b.s.M.atoms := objectAtoms_sub K.C K.b_mem
  have hJ' : ∀ c, (c = K.C.upper ∨ c = K.C.lower) → (b.anc c = U.upper ∨ b.anc c = U.lower) := by
    intro c hc
    rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hc with rfl | rfl
    · exact Or.inl e1
    · exact Or.inr e2
    · exact Or.inr e1
    · exact Or.inl e2
  have hJr : ∀ v, (v = U.upper ∨ v = U.lower) → (v = b.anc K.C.upper ∨ v = b.anc K.C.lower) := by
    intro v hv
    rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hv with rfl | rfl
    · exact Or.inl e1.symm
    · exact Or.inr e2.symm
    · exact Or.inr e2.symm
    · exact Or.inl e1.symm
  have hold : ∀ c ∈ b.s.M.atoms, c ∉ K.C.atoms → b.anc c ∉ U.atoms := fun c hc hcC hu => hcC (hin c hc hu)
  set cc := alphaOrBeta K.post.numComponents b.s.M.numComponents R kp with hccdef
  have hcl : (b.vinePost K R kp).s.cls = (vineSt b.s K cc).cls := rfl
  have hanc : (b.vinePost K R kp).anc =
      Function.update (Function.update b.anc K.fa (b.anc K.C.upper)) K.fb (b.anc K.C.lower) := rfl
  have hev : ∀ c, c ∈ b.s.M.atoms → (b.vinePost K R kp).anc c = b.anc c := by
    intro c hc
    rw [hanc, Function.update_of_ne (fun e => K.fb_fresh (by rw [← e]; exact hc)),
      Function.update_of_ne (fun e => K.fa_fresh (by rw [← e]; exact hc))]
  have hfaE : (b.vinePost K R kp).anc K.fa = b.anc K.C.upper := by
    rw [hanc, Function.update_of_ne K.fa_ne_fb, Function.update_self]
  have hfbE : (b.vinePost K R kp).anc K.fb = b.anc K.C.lower := by
    rw [hanc, Function.update_self]
  have hfa_mem : K.fa ∈ (b.vinePost K R kp).s.M.atoms := by
    rw [hpost, Finset.mem_filter]
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun h => K.fa_fresh (objectAtoms_sub K.C h)⟩
  have hfb_mem : K.fb ∈ (b.vinePost K R kp).s.M.atoms := by
    rw [hpost, Finset.mem_filter]
    exact ⟨Finset.mem_insert_self _ _, fun h => K.fb_fresh (objectAtoms_sub K.C h)⟩
  have hcases : ∀ c ∈ (b.vinePost K R kp).s.M.atoms, c = K.fb ∨ c = K.fa ∨ (c ∈ b.s.M.atoms ∧ c ∉ K.C.atoms) := by
    intro c hc
    rw [hpost, Finset.mem_filter, Finset.mem_insert, Finset.mem_insert] at hc
    obtain ⟨h1, h3⟩ := hc
    rcases h1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨h1, h3⟩)
  refine ⟨anc_inj_vinePost K hinj R kp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp a ha ⟨h1, h2⟩
    rcases hcases a h1 with rfl | rfl | ⟨h1, h3⟩
    · rw [hcl, FinalCountAsm.vineSt_cls_fb] at h2; exact alphaOrBeta_ne_eps _ _ _ _ h2
    · rw [hcl, FinalCountAsm.vineSt_cls_fa] at h2; exact alphaOrBeta_ne_eps _ _ _ _ h2
    · rw [hcl, FinalCountAsm.vineSt_cls_old b.s K _ h1 h3] at h2
      rcases List.mem_cons.1 hp with rfl | hp
      · have he : b.anc a = a := hA.eps a h1 h2
        exact h3 (hin a h1 (by rw [he]; exact ha))
      · exact hrem p hp a ha ⟨h1, h2⟩
  · intro z hz
    by_cases hx : ∃ x : b.s.D, b.s.down x = z
    · obtain ⟨x, rfl⟩ := hx
      have hn : K.cutMol.atom x ∈ K.C.atoms := by
        by_contra hn
        exact hz ⟨x, hn⟩ rfl
      obtain ⟨hca, hj1, hj2⟩ := cutMol_atom_of_mem K hn
      have hMx : b.s.M.atom x ∈ K.C.atoms := hca ▸ hn
      have hz1 : M₀.atom (b.s.down x) = b.anc (b.s.M.atom x) := hA.atom x
      refine ⟨(U, quadK b K), List.mem_cons_self, ?_, ?_⟩
      · show M₀.atom (b.s.down x) ∈ U.atoms
        rw [hz1]; exact hat _ hMx
      · intro hj
        rw [hz1] at hj
        have key : b.s.M.atom x = K.C.upper ∨ b.s.M.atom x = K.C.lower := by
          rcases hJr _ hj with e | e
          · exact Or.inl (hinj _ (b.s.M.atom_mem x) _ hupm e)
          · exact Or.inr (hinj _ (b.s.M.atom_mem x) _ hlom e)
        rcases key with k | k
        · rcases hj1 k with e | e <;> simp [e]
        · rcases hj2 k with e | e <;> simp [e]
    · push Not at hx
      obtain ⟨p, hp, hk⟩ := hpres z hx
      exact ⟨p, List.mem_cons_of_mem _ hp, hk⟩
  · intro x p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · intro hk
      have hat' : M₀.atom (b.s.down x.1) ∈ U.atoms := hk.1
      have himp : (M₀.atom (b.s.down x.1) = U.upper ∨ M₀.atom (b.s.down x.1) = U.lower) →
          (b.s.down x.1 = b.s.down K.x₁ ∨ b.s.down x.1 = b.s.down K.x₂ ∨ b.s.down x.1 = b.s.down K.y₁ ∨
            b.s.down x.1 = b.s.down K.y₂) := hk.2
      have hy : K.cutMol.atom x.1 ∉ K.C.atoms := x.2
      have hz1 : M₀.atom (b.s.down x.1) = b.anc (b.s.M.atom x.1) := hA.atom x.1
      have hMxC : b.s.M.atom x.1 ∈ K.C.atoms := hin _ (b.s.M.atom_mem x.1) (hz1 ▸ hat')
      have hmv := cutMol_atom_moved K hMxC hy
      have hmj : M₀.atom (b.s.down x.1) = U.upper ∨ M₀.atom (b.s.down x.1) = U.lower := by
        rw [hz1]
        rcases hmv with ⟨e, -, -⟩ | ⟨e, -, -⟩
        · rw [e]; exact hJ' _ (Or.inl rfl)
        · rw [e]; exact hJ' _ (Or.inr rfl)
      have hN' := himp hmj
      have hinjd := hA.inj
      rcases hmv with ⟨e, n1, n2⟩ | ⟨e, n1, n2⟩
      · rcases hN' with e' | e' | e' | e'
        · exact n1 (hinjd e')
        · exact n2 (hinjd e')
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (e.symm.trans K.My₁)
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (e.symm.trans K.My₂)
      · rcases hN' with e' | e' | e' | e'
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (K.Mx₁.symm.trans e)
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (K.Mx₂.symm.trans e)
        · exact n1 (hinjd e')
        · exact n2 (hinjd e')
    · exact he1 x.1 p hp
  · intro v hv hvn
    have hvn' : ∀ p ∈ rs, ¬ PieceInt p.1 v := fun p hp => hvn p (List.mem_cons_of_mem _ hp)
    have hnU : ¬ PieceInt U v := hvn _ List.mem_cons_self
    rcases he2 v hv hvn' with ⟨c, hc, hcv⟩ | hk
    · by_cases hcC : c ∈ K.C.atoms
      · have hvU : v ∈ U.atoms := by rw [← hcv]; exact hat c hcC
        have hvj : v = U.upper ∨ v = U.lower := by
          by_contra hcon
          push Not at hcon
          exact hnU ⟨hvU, hcon.1, hcon.2⟩
        left
        rcases hJr v hvj with hvu | hvl
        · exact ⟨K.fa, hfa_mem, by rw [hfaE, hvu]⟩
        · exact ⟨K.fb, hfb_mem, by rw [hfbE, hvl]⟩
      · left
        refine ⟨c, ?_, ?_⟩
        · rw [hpost, Finset.mem_filter]
          exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc), hcC⟩
        · rw [hev c hc, hcv]
    · right
      intro z hz
      obtain ⟨p, hp, hkz⟩ := hk z hz
      exact ⟨p, List.mem_cons_of_mem _ hp, hkz⟩
  · intro c hc p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · rintro ⟨hat', hn1, hn2⟩
      rcases hcases c hc with rfl | rfl | ⟨hc1, hc2⟩
      · rw [hfbE] at hn1 hn2
        rcases hJ' _ (Or.inr rfl) with e | e
        · exact hn1 e
        · exact hn2 e
      · rw [hfaE] at hn1 hn2
        rcases hJ' _ (Or.inl rfl) with e | e
        · exact hn1 e
        · exact hn2 e
      · rw [hev c hc1] at hat'
        exact hold c hc1 hc2 hat'
    · rcases hcases c hc with rfl | rfl | ⟨hc1, -⟩
      · rw [hfbE]; exact he3 K.C.lower hlom p hp
      · rw [hfaE]; exact he3 K.C.upper hupm p hp
      · rw [hev c hc1]; exact he3 c hc1 p hp
  · intro c hc hce
    rcases hcases c hc with rfl | rfl | ⟨hc1, hc2⟩
    · exact ⟨(U, quadK b K), List.mem_cons_self, by rw [hfbE]; exact hat _ K.b_mem⟩
    · exact ⟨(U, quadK b K), List.mem_cons_self, by rw [hfaE]; exact hat _ K.a_mem⟩
    · rw [hcl, FinalCountAsm.vineSt_cls_old b.s K _ hc1 hc2] at hce
      obtain ⟨p, hp, hpa⟩ := hne c hc1 hce
      exact ⟨p, List.mem_cons_of_mem _ hp, by rw [hev c hc1]; exact hpa⟩

end step

end WaveTurbulence.Flower.FinalMKPhase1
