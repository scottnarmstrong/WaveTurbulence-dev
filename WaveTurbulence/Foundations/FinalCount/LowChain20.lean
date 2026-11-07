/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain19
/-! **FINALCOUNT LOW-CHAIN, session 4 (2): the removal bookkeeping along the LOW Step 1 (`ConnDataL`, `collInv_of_reach1L`, `reach1L_connInv`).**
`ConnDataL` is `ConnData` without the fields that fail after a Step D1 (the halves of degree-2 joints are deleted): the
injectivity of `anc`, the removed pieces `ps`, their pairwise disjointness, removal of their atoms, and that every absent dart of `M₀`
is killed by a piece.  This is all that `hconn0_of_hostConn` uses. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

def ConnDataL (M₀ : Molecule V D₀) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (Fst : Set (Object M₀))
    (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) (ps : List (Object M₀ × Quad D₀)) : Prop :=
  (∀ c ∈ h.s.M.atoms, ∀ b ∈ h.s.M.atoms, h.anc c = h.anc b → c = b) ∧
  (∀ p ∈ ps, PieceData C Un L γ η w κ p) ∧
    ps.Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms) ∧
    (∀ p ∈ ps, ∀ a ∈ p.1.atoms, ¬ (a ∈ h.s.M.atoms ∧ h.s.cls a = .eps)) ∧
    (∀ z : D₀, (∀ x : h.s.D, h.s.down x ≠ z) → ∃ p ∈ ps, z ∈ PieceKill p.1 p.2)

def ConnInvL (M₀ : Molecule V D₀) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (Fst : Set (Object M₀))
    (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∃ ps, ConnDataL M₀ C Un Fst L γ η w κ h ps

theorem connDataL_init (M₀ : Molecule V D₀) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (Fst : Set (Object M₀))
    (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : ConnDataL M₀ C Un Fst L γ η w κ (HSt.init M₀) [] :=
  ⟨fun c _ b _ h => h, by simp, by simp, by simp, fun z hz => absurd rfl (hz z)⟩

theorem anc_inj_vinePostG {b : HSt V D₀} (K : VineCut b.s.M)
    (hinj : ∀ c ∈ b.s.M.atoms, ∀ e ∈ b.s.M.atoms, b.anc c = b.anc e → c = e) :
    ∀ c ∈ (b.vinePostG K).s.M.atoms, ∀ e ∈ (b.vinePostG K).s.M.atoms,
      (b.vinePostG K).anc c = (b.vinePostG K).anc e → c = e := by
  intro c hc e he hce
  have hmem : ∀ x, x ∈ (b.vinePostG K).s.M.atoms → x ∈ (b.vinePost K 0 0).s.M.atoms := by
    intro x hx
    show x ∈ (insert K.fb (insert K.fa b.s.M.atoms)).filter (fun a => a ∉ K.C.atoms)
    have hx' : x ∈ (insert K.fb (insert K.fa b.s.M.atoms)).filter (VineKeep K) := hx
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hx').1, (Finset.mem_filter.1 hx').2.1⟩
  exact anc_inj_vinePost K hinj 0 0 c (hmem c hc) e (hmem e he) hce

theorem vineG_keep_of_not_mem {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : VineCut M) {x : D}
    (hn : K.cutMol.atom x ∉ K.C.atoms) : VineKeep K (K.cutMol.atom x) := by
  refine ⟨hn, ?_, ?_⟩
  · rintro ⟨he, hd⟩
    have : x ∈ K.cutMol.dartsAt K.fa := (Mole.mem_dartsAt _ _ _).2 he
    rw [vineCut_fa_dartless K hd] at this; exact absurd this (by simp)
  · rintro ⟨he, hd⟩
    have : x ∈ K.cutMol.dartsAt K.fb := (Mole.mem_dartsAt _ _ _).2 he
    rw [vineCut_fb_dartless K hd] at this; exact absurd this (by simp)

/-- A collected intact object that is cut along its own `ContainsDart` darts is dartless afterwards (Step D1). -/
theorem dartless_vineStG {M₀ : Molecule V D₀} {s : St.{u} V D₀} {a : V → V} (hA : AncRel M₀ s a) (hD : DartRel M₀ s)
    (K : VineCut s.M) (U : Object M₀) (hUat : U.atoms = K.C.atoms)
    (hint : ∀ b ∈ U.atoms, b ∈ s.M.atoms ∧ s.cls b = .eps)
    (hdx : U.ContainsDart (s.down K.x₁) ∧ U.ContainsDart (s.down K.x₂) ∧ U.ContainsDart (s.down K.y₁) ∧
      U.ContainsDart (s.down K.y₂))
    (hUJ : (M₀.atom (s.down K.x₁) = U.upper ∧ M₀.atom (s.down K.y₁) = U.lower) ∨
      (M₀.atom (s.down K.x₁) = U.lower ∧ M₀.atom (s.down K.y₁) = U.upper)) :
    ∀ x : (vineStG s K).D, ¬ U.ContainsDart ((vineStG s K).down x) :=
  fun x hx => dartless_vineSt_key hA hD K U hUat hint hdx hUJ x.1 x.2.1 hx

theorem uIntact_vinePostG {M₀ : Molecule V D₀} {h : HSt V D₀} (K : VineCut h.s.M) (U : Object M₀)
    (hU : UIntact U h) (hdis : Disjoint U.atoms K.C.atoms) : UIntact U (h.vinePostG K) := by
  intro a ha
  obtain ⟨haM, hε⟩ := hU a ha
  have haC : a ∉ K.C.atoms := fun hc => Finset.disjoint_left.mp hdis ha hc
  refine ⟨?_, ?_⟩
  · show a ∈ (insert K.fb (insert K.fa h.s.M.atoms)).filter (VineKeep K)
    refine Finset.mem_filter.2 ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem haM), haC, ?_, ?_⟩
    · rintro ⟨e, -⟩; exact K.fa_fresh (e ▸ haM)
    · rintro ⟨e, -⟩; exact K.fb_fresh (e ▸ haM)
  · show (vineStG h.s K).cls a = .eps
    rw [vineStG_cls_old h.s K haC haM]; exact hε

theorem connDataL_vine [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc)
    {ps : List (Object M₀ × Quad D₀)} (hI : ConnDataL M₀ C Un Fst L γ η w κ b ps) (K : VineCut b.s.M) (R : ℝ) (kp : ℕ) (U : Object M₀)
    (hU : Collected C (Un κ) L γ η w κ U) (hUK : U.atoms = K.C.atoms)
    (hUD : U.ContainsDart (b.s.down K.x₁) ∧ U.ContainsDart (b.s.down K.x₂) ∧ U.ContainsDart (b.s.down K.y₁) ∧
      U.ContainsDart (b.s.down K.y₂))
    (hUJ : (M₀.atom (b.s.down K.x₁) = U.upper ∧ M₀.atom (b.s.down K.y₁) = U.lower) ∨
      (M₀.atom (b.s.down K.x₁) = U.lower ∧ M₀.atom (b.s.down K.y₁) = U.upper))
    (hord : U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' b)
    (hint : UIntact U b) : ConnDataL M₀ C Un Fst L γ η w κ (b.vinePost K R kp)
      ((U, (b.s.down K.x₁, b.s.down K.x₂, b.s.down K.y₁, b.s.down K.y₂)) :: ps) := by
  obtain ⟨hinj, hps, hpw, hrem, hpres⟩ := hI
  have hUe : ∀ v ∈ K.C.atoms, b.anc v = v := fun v hv => by
    have hv' : v ∈ U.atoms := by rw [hUK]; exact hv
    exact hA.eps v (hint v hv').1 (hint v hv').2
  have hpost : (b.vinePost K R kp).s.M.atoms = (insert K.fb (insert K.fa b.s.M.atoms)).filter (fun a => a ∉ K.C.atoms) := rfl
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
  have hfa_cls : ∀ c, c = K.fb ∨ c = K.fa → (b.vinePost K R kp).s.cls c ≠ .eps := by
    intro c hc
    have hcl : (b.vinePost K R kp).s.cls = (vineSt b.s K (alphaOrBeta K.post.numComponents b.s.M.numComponents R kp)).cls := rfl
    rcases hc with rfl | rfl
    · rw [hcl, vineSt_cls_fb]; exact alphaOrBeta_ne_eps _ _ _ _
    · rw [hcl, vineSt_cls_fa]; exact alphaOrBeta_ne_eps _ _ _ _
  have hanc : (b.vinePost K R kp).anc = Function.update (Function.update b.anc K.fa (b.anc K.C.upper)) K.fb (b.anc K.C.lower) := rfl
  have hev : ∀ c, c ∈ b.s.M.atoms → (b.vinePost K R kp).anc c = b.anc c := by
    intro c hc
    rw [hanc, Function.update_of_ne (fun e => K.fb_fresh (by rw [← e]; exact hc)),
      Function.update_of_ne (fun e => K.fa_fresh (by rw [← e]; exact hc))]
  have hfaE : (b.vinePost K R kp).anc K.fa = K.C.upper := by
    rw [hanc, Function.update_of_ne K.fa_ne_fb, Function.update_self, hUe _ K.a_mem]
  have hfbE : (b.vinePost K R kp).anc K.fb = K.C.lower := by
    rw [hanc, Function.update_self, hUe _ K.b_mem]
  refine ⟨anc_inj_vinePost K hinj R kp, ?_, ?_, ?_, ?_⟩
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
      have hc : (b.vinePost K R kp).s.cls = (vineSt b.s K (alphaOrBeta K.post.numComponents b.s.M.numComponents R kp)).cls := rfl
      rcases h1 with rfl | rfl | h1
      · rw [hc, vineSt_cls_fb] at h2; exact alphaOrBeta_ne_eps _ _ _ _ h2
      · rw [hc, vineSt_cls_fa] at h2; exact alphaOrBeta_ne_eps _ _ _ _ h2
      · rw [hc, vineSt_cls_old b.s K _ h1 h3] at h2
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

theorem connDataL_vineG [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc)
    {ps : List (Object M₀ × Quad D₀)} (hI : ConnDataL M₀ C Un Fst L γ η w κ b ps) (K : VineCut b.s.M) (U : Object M₀)
    (hU : Collected C (Un κ) L γ η w κ U) (hUK : U.atoms = K.C.atoms)
    (hUD : U.ContainsDart (b.s.down K.x₁) ∧ U.ContainsDart (b.s.down K.x₂) ∧ U.ContainsDart (b.s.down K.y₁) ∧
      U.ContainsDart (b.s.down K.y₂))
    (hUJ : (M₀.atom (b.s.down K.x₁) = U.upper ∧ M₀.atom (b.s.down K.y₁) = U.lower) ∨
      (M₀.atom (b.s.down K.x₁) = U.lower ∧ M₀.atom (b.s.down K.y₁) = U.upper))
    (hord : U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' b)
    (hint : UIntact U b) : ConnDataL M₀ C Un Fst L γ η w κ (b.vinePostG K)
      ((U, (b.s.down K.x₁, b.s.down K.x₂, b.s.down K.y₁, b.s.down K.y₂)) :: ps) := by
  obtain ⟨hinj, hps, hpw, hrem, hpres⟩ := hI
  have hUe : ∀ v ∈ K.C.atoms, b.anc v = v := fun v hv => by
    have hv' : v ∈ U.atoms := by rw [hUK]; exact hv
    exact hA.eps v (hint v hv').1 (hint v hv').2
  have hpost : (b.vinePostG K).s.M.atoms = (insert K.fb (insert K.fa b.s.M.atoms)).filter (VineKeep K) := rfl
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
  have hfa_cls : ∀ c, c = K.fb ∨ c = K.fa → (b.vinePostG K).s.cls c ≠ .eps := by
    intro c hc
    have hcl : (b.vinePostG K).s.cls = (vineStG b.s K).cls := rfl
    rcases hc with rfl | rfl
    · rw [hcl, vineStG_cls_fb]; exact jcls_ne_eps _ _
    · rw [hcl, vineStG_cls_fa]; exact jcls_ne_eps _ _
  have hanc : (b.vinePostG K).anc = Function.update (Function.update b.anc K.fa (b.anc K.C.upper)) K.fb (b.anc K.C.lower) := rfl
  have hev : ∀ c, c ∈ b.s.M.atoms → (b.vinePostG K).anc c = b.anc c := by
    intro c hc
    rw [hanc, Function.update_of_ne (fun e => K.fb_fresh (by rw [← e]; exact hc)),
      Function.update_of_ne (fun e => K.fa_fresh (by rw [← e]; exact hc))]
  have hfaE : (b.vinePostG K).anc K.fa = K.C.upper := by
    rw [hanc, Function.update_of_ne K.fa_ne_fb, Function.update_self, hUe _ K.a_mem]
  have hfbE : (b.vinePostG K).anc K.fb = K.C.lower := by
    rw [hanc, Function.update_self, hUe _ K.b_mem]
  refine ⟨anc_inj_vinePostG K hinj, ?_, ?_, ?_, ?_⟩
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
      exact h1.2.1 (hUK ▸ ha)
    · rw [hpost, Finset.mem_filter, Finset.mem_insert, Finset.mem_insert] at h1
      obtain ⟨h1, h3⟩ := h1
      have hc : (b.vinePostG K).s.cls = (vineStG b.s K).cls := rfl
      rcases h1 with rfl | rfl | h1
      · rw [hc, vineStG_cls_fb] at h2; exact jcls_ne_eps _ _ h2
      · rw [hc, vineStG_cls_fa] at h2; exact jcls_ne_eps _ _ h2
      · rw [hc, vineStG_cls_old b.s K h3.1 h1] at h2
        exact hrem p hp a ha ⟨h1, h2⟩
  · intro z hz
    by_cases hx : ∃ x : b.s.D, b.s.down x = z
    · obtain ⟨x, rfl⟩ := hx
      have hn : K.cutMol.atom x ∈ K.C.atoms := by
        by_contra hn
        exact hz ⟨x, vineG_keep_of_not_mem K hn⟩ rfl
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

theorem hconn0_of_hostConnL [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {L γ η : ℝ} {w : Mom d} {A0 : Set (D₀ → (Fin d → ℤ))} {κ : D₀ → (Fin d → ℤ)} (hHC : HostConn M₀ C Un L γ η w A0) (hκ : κ ∈ A0)
    {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s) (hI : ConnInvL M₀ C Un Fst L γ η w κ h)
    {U : Object M₀} (hUc : Collected C (Un κ) L γ η w κ U) (hint : UIntact U h) {K : VineCut h.s.M}
    (hKat : K.C.atoms = U.atoms) :
    ∀ K' : VineCut h.s.M, K'.C.atoms = K.C.atoms → Nonempty (DoubleShape K') →
      ∃ G : Finset h.s.D, (∀ z ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K' G := by
  intro K' hK'at ⟨S⟩
  refine ⟨{K'.x₁, K'.x₂, K'.y₁, K'.y₂}, fun z hz => hz, ?_⟩
  obtain ⟨ps, hinj, hps, hpw, hrem, hpres⟩ := hI
  set a := K'.C.upper with ha
  set b := K'.C.lower with hb
  set x := S.x with hx
  have hUat : U.atoms = {a, x, b} := by rw [← hKat, ← hK'at]; exact S.atoms_eq
  have hax : a ≠ x := S.x_ne_a.symm
  have hxb : x ≠ b := S.x_ne_b
  have hab : a ≠ b := K'.ab_ne
  have hmem : ∀ v ∈ ({a, x, b} : Finset V), v ∈ h.s.M.atoms ∧ h.s.cls v = .eps := fun v hv => hint v (hUat ▸ hv)
  have hancε : ∀ v ∈ ({a, x, b} : Finset V), h.anc v = v := fun v hv => hA.eps v (hmem v hv).1 (hmem v hv).2
  have haM : a ∈ ({a, x, b} : Finset V) := by simp
  have hxM : x ∈ ({a, x, b} : Finset V) := by simp
  have hbM : b ∈ ({a, x, b} : Finset V) := by simp
  -- closure of the darts at x
  have hclos : ∀ z, M₀.atom z = x → M₀.atom (M₀.mate z) = a ∨ M₀.atom (M₀.mate z) = b := by
    intro z hz
    obtain ⟨x', hx'⟩ := hA.surj x (hmem x hxM).1 (hmem x hxM).2 z hz
    have h1 : h.anc (h.s.M.atom x') = x := by rw [← hA.atom x', hx', hz]
    have h2 : h.s.M.atom x' = x := hA.uniq _ (h.s.M.atom_mem x') x (hmem x hxM).1 (hmem x hxM).2 h1
    have h3 : x' ∈ h.s.M.dartsAt x := (Mole.mem_dartsAt _ _ _).2 h2
    rw [S.darts_x] at h3
    have hm : M₀.atom (M₀.mate z) = h.anc (h.s.M.atom (h.s.M.mate x')) := by
      rw [← hx', hD.mate, hA.atom]
    simp only [Finset.mem_insert, Finset.mem_singleton] at h3
    rcases h3 with e | e | e | e <;> rw [e, h.s.M.mate_mate] at hm
    · left; rw [hm, K'.Mx₁, hancε a haM]
    · left; rw [hm, K'.Mx₂, hancε a haM]
    · right; rw [hm, K'.My₁, hancε b hbM]
    · right; rw [hm, K'.My₂, hancε b hbM]
  have hdis : ∀ p ∈ ps, Disjoint p.1.atoms U.atoms := fun p hp =>
    Finset.disjoint_left.2 fun v hv hvU => hrem p hp v hv (hint v hvU)
  have hconn := hHC κ hκ ps U a x b hps hpw hdis hUc hUat hax hxb hab hclos
  -- the lift
  let σ : V → V := fun s => if hs : ∃ c ∈ h.s.M.atoms, h.anc c = s then Classical.choose hs else s
  have hσ : ∀ c ∈ h.s.M.atoms, σ (h.anc c) = c := by
    intro c hc
    have hs : ∃ c' ∈ h.s.M.atoms, h.anc c' = h.anc c := ⟨c, hc, rfl⟩
    simp only [σ, dif_pos hs]
    exact hinj _ (Classical.choose_spec hs).1 _ hc (Classical.choose_spec hs).2
  have hint' : ∀ c ∈ vineInterior K', c = x := by
    intro c hc
    simp only [vineInterior, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    rw [S.atoms_eq] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with ⟨hc | hc | hc, h1, h2⟩
    · exact absurd hc h1
    · exact hc
    · exact absurd hc h2
  have hxint : x ∈ vineInterior K' := by
    unfold vineInterior
    rw [S.atoms_eq]
    refine Finset.mem_sdiff.2 ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hax.symm, hxb⟩
  -- mate darts at x
  have hxd : ∀ y : h.s.D, y ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D) → h.s.M.atom (h.s.M.mate y) = x := by
    intro y hy
    have : h.s.M.mate y ∈ h.s.M.dartsAt x := by
      rw [S.darts_x]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
      rcases hy with e | e | e | e <;> simp [e]
    exact (Mole.mem_dartsAt _ _ _).1 this
  have hxd' : ∀ y : h.s.D, h.s.M.mate y ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D) → h.s.M.atom y = x := by
    intro y hy
    have := hxd _ hy
    rwa [h.s.M.mate_mate] at this
  have hstep : ∀ s t, Relation.EqvGen (fun s t : V => ∃ z, M₀.atom z = s ∧ M₀.atom (M₀.mate z) = t ∧
      z ∉ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ {z | M₀.atom z = x}) ∧
      M₀.mate z ∉ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ {z | M₀.atom z = x})) s t →
      Relation.EqvGen (fun s t : V => s ∉ vineInterior K' ∧ t ∉ vineInterior K' ∧
        ∃ z, h.s.M.atom z = s ∧ h.s.M.atom (h.s.M.mate z) = t ∧ z ∉ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D) ∧
          h.s.M.mate z ∉ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D)) (σ s) (σ t) := by
    intro s t hst
    induction hst with
    | rel s t hr =>
      obtain ⟨z, hs, ht, hz, hmz⟩ := hr
      have hpr : ∀ z' : D₀, z' ∉ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ {z | M₀.atom z = x}) → ∃ x₀ : h.s.D, h.s.down x₀ = z' := by
        intro z' hz'
        by_contra hno
        push Not at hno
        obtain ⟨p, hp, hk⟩ := hpres z' hno
        exact hz' (Or.inl (Set.mem_iUnion₂.2 ⟨p, hp, hk⟩))
      obtain ⟨x₀, hx₀⟩ := hpr z hz
      have hz1 : M₀.atom z ≠ x := fun e => hz (Or.inr e)
      have hz2 : M₀.atom (M₀.mate z) ≠ x := fun e => hmz (Or.inr e)
      have hc1 : h.anc (h.s.M.atom x₀) = s := by rw [← hs, ← hx₀, hA.atom]
      have hc2 : h.anc (h.s.M.atom (h.s.M.mate x₀)) = t := by rw [← ht, ← hx₀, hD.mate, hA.atom]
      have hs1 : σ s = h.s.M.atom x₀ := by rw [← hc1]; exact hσ _ (h.s.M.atom_mem x₀)
      have ht1 : σ t = h.s.M.atom (h.s.M.mate x₀) := by rw [← hc2]; exact hσ _ (h.s.M.atom_mem _)
      rw [hs1, ht1]
      have hne : ∀ c ∈ h.s.M.atoms, h.anc c ≠ x → c ∈ h.s.M.atoms → c ∈ vineInterior K' → False := by
        intro c _ hcx _ hci
        have := hint' c hci
        subst this
        exact hcx (hancε _ hxM)
      refine Relation.EqvGen.rel _ _ ⟨fun hci => hne _ (h.s.M.atom_mem _) (by rw [hc1]; exact fun e => hz1 (hs.trans e)) (h.s.M.atom_mem _) hci,
        fun hci => hne _ (h.s.M.atom_mem _) (by rw [hc2]; exact fun e => hz2 (ht.trans e)) (h.s.M.atom_mem _) hci, x₀, rfl, rfl, ?_, ?_⟩
      · intro hG
        apply hne _ (h.s.M.atom_mem (h.s.M.mate x₀)) (by rw [hc2]; exact fun e => hz2 (ht.trans e)) (h.s.M.atom_mem _)
        rw [hxd x₀ hG]; exact hxint
      · intro hG
        apply hne _ (h.s.M.atom_mem x₀) (by rw [hc1]; exact fun e => hz1 (hs.trans e)) (h.s.M.atom_mem _)
        rw [hxd' x₀ hG]; exact hxint
    | refl s => exact Relation.EqvGen.refl _
    | symm s t _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans s t u _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have := hstep a b hconn
  have e1 : σ a = a := by have := hσ a (hmem a haM).1; rwa [hancε a haM] at this
  have e2 : σ b = b := by have := hσ b (hmem b hbM).1; rwa [hancε b hbM] at this
  rw [e1, e2] at this
  exact this


end WaveTurbulence.FinalCountAsm
