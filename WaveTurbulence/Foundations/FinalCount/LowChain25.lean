/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain24
public import WaveTurbulence.Foundations.FinalCount.AsmEnd3
/-! **FINALCOUNT LOW-CHAIN, session 5 (3): a later (non-first-stage) vine step does not increase the number of components.**
`mate_nonnode_outside`: the mate of a non-node dart at a joint of a vine cut lies outside the interior of the cut object (from `K.closed`).
`vine_F_le_of_hostConnFL`: `vine_F_le_of_hostConnF` for `HostConnFL` (both joints of degree `≥ 3` keep a bond). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount


variable {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem exists_third_dart {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) {j : V} {p q : D} (hd : 3 ≤ M.deg j) :
    ∃ y, M.atom y = j ∧ y ≠ p ∧ y ≠ q := by
  by_contra hno
  push Not at hno
  have hsub : M.dartsAt j ⊆ {p, q} := by
    intro y hy
    have hya := (Mole.mem_dartsAt M j y).1 hy
    by_cases h1 : y = p
    · simp [h1]
    · have := hno y hya h1
      simp [this]
  have h1 := Finset.card_le_card hsub
  have h2 : ({p, q} : Finset D).card ≤ 2 := Finset.card_le_two
  unfold Molecule.deg at hd
  omega

theorem mate_nonnode_outside {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : VineCut M) {y : D}
    (hyj : M.atom y = K.C.upper ∨ M.atom y = K.C.lower) (hyG : y ∉ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D)) :
    M.mate y ∉ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D) ∧ M.atom (M.mate y) ∉ vineInterior K := by
  have e1 : K.cutMol.atom y = hPost K (M.atom y) := cutMol_atom_outside K (G := {K.x₁, K.x₂, K.y₁, K.y₂}) (fun z hz => hz) hyG
  have hn : K.cutMol.atom y ∉ K.C.atoms := by
    rcases hyj with e | e
    · rw [e1, e]
      have : hPost K K.C.upper = K.fa := by simp [hPost]
      rw [this]; exact fun h => K.fa_fresh (objectAtoms_sub K.C h)
    · rw [e1, e]
      have : hPost K K.C.lower = K.fb := by simp [hPost, K.ab_ne.symm]
      rw [this]; exact fun h => K.fb_fresh (objectAtoms_sub K.C h)
  have hcl : K.cutMol.atom (K.cutMol.mate y) ∉ K.C.atoms := K.closed y hn
  have hm : K.cutMol.mate y = M.mate y := rfl
  rw [hm] at hcl
  have hcmem : ∀ z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D), M.atom z ∈ K.C.atoms := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · rw [K.Mx₁]; exact K.a_mem
    · rw [K.Mx₂]; exact K.a_mem
    · rw [K.My₁]; exact K.b_mem
    · rw [K.My₂]; exact K.b_mem
  by_cases hu : M.atom (M.mate y) ∈ K.C.atoms
  · have hmv := cutMol_atom_moved K hu hcl
    have hjt : M.atom (M.mate y) = K.C.upper ∨ M.atom (M.mate y) = K.C.lower := by
      rcases hmv with ⟨e, -, -⟩ | ⟨e, -, -⟩
      · exact Or.inl e
      · exact Or.inr e
    refine ⟨?_, ?_⟩
    · intro hG
      simp only [Finset.mem_insert, Finset.mem_singleton] at hG
      rcases hmv with ⟨e, n1, n2⟩ | ⟨e, n1, n2⟩
      · rcases hG with h | h | h | h
        · exact n1 h
        · exact n2 h
        · rw [h, K.My₁] at e; exact K.ab_ne e.symm
        · rw [h, K.My₂] at e; exact K.ab_ne e.symm
      · rcases hG with h | h | h | h
        · rw [h, K.Mx₁] at e; exact K.ab_ne e
        · rw [h, K.Mx₂] at e; exact K.ab_ne e
        · exact n1 h
        · exact n2 h
    · intro hI
      simp only [vineInterior, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hI
      rcases hjt with e | e
      · exact hI.2.1 e
      · exact hI.2.2 e
  · refine ⟨fun hG => hu (hcmem _ hG), fun hI => hu ?_⟩
    simp only [vineInterior, Finset.mem_sdiff] at hI
    exact hI.1

theorem vine_F_le_of_hostConnFL [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {L γ η : ℝ} {w : Mom d} {A0 : Set (D₀ → (Fin d → ℤ))} {κ : D₀ → (Fin d → ℤ)}
    (hHF : HostConnFL M₀ C Un Fst L γ η w A0) (hκ : κ ∈ A0) {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc) (hD : DartRel M₀ b.s)
    {ps : List (Object M₀ × Quad D₀)} (hI : ConnDataL2 M₀ C Un Fst L γ η w κ b ps) (K : VineCut b.s.M) (U : Object M₀)
    (hU : Collected C (Un κ) L γ η w κ U) (hUK : U.atoms = K.C.atoms)
    (hUD : U.ContainsDart (b.s.down K.x₁) ∧ U.ContainsDart (b.s.down K.x₂) ∧ U.ContainsDart (b.s.down K.y₁) ∧
      U.ContainsDart (b.s.down K.y₂))
    (hUJ : (M₀.atom (b.s.down K.x₁) = U.upper ∧ M₀.atom (b.s.down K.y₁) = U.lower) ∨
      (M₀.atom (b.s.down K.x₁) = U.lower ∧ M₀.atom (b.s.down K.y₁) = U.upper))
    (hint : UIntact U b) (hUF : U ∉ Fst) (h3a : 3 ≤ b.s.M.deg K.C.upper) (h3b : 3 ≤ b.s.M.deg K.C.lower) :
    K.post.numComponents ≤ b.s.M.numComponents := by
  obtain ⟨⟨hinj, hps, hpw, hrem, hpres⟩, he1, he2, he3, hfo⟩ := hI
  have hUe : ∀ v ∈ K.C.atoms, b.anc v = v := fun v hv => by
    have hv' : v ∈ U.atoms := by rw [hUK]; exact hv
    exact hA.eps v (hint v hv').1 (hint v hv').2
  have hup : M₀.atom (b.s.down K.x₁) = K.C.upper := by rw [hA.atom, K.cut_a.2.2.1, hUe _ K.a_mem]
  have hlow : M₀.atom (b.s.down K.y₁) = K.C.lower := by rw [hA.atom, K.My₁, hUe _ K.b_mem]
  have hup2 : M₀.atom (b.s.down K.x₂) = K.C.upper := by rw [hA.atom, K.Mx₂, hUe _ K.a_mem]
  have hlow2 : M₀.atom (b.s.down K.y₂) = K.C.lower := by rw [hA.atom, K.My₂, hUe _ K.b_mem]
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
  have hback : ∀ c ∈ b.s.M.atoms, b.anc c ∈ U.atoms → c = b.anc c := fun c hc hu =>
    hA.uniq c hc (b.anc c) (hint _ hu).1 (hint _ hu).2 rfl
  set N : Quad D₀ := (b.s.down K.x₁, b.s.down K.x₂, b.s.down K.y₁, b.s.down K.y₂) with hN
  have hpd : PieceData C Un L γ η w κ (U, N) := by
    refine ⟨hU, hUD, hUJ, ?_, ?_, ?_, ?_⟩
    · show M₀.atom (b.s.down K.x₂) = M₀.atom (b.s.down K.x₁)
      rw [hA.atom, hA.atom, K.Mx₂, K.cut_a.2.2.1]
    · show M₀.atom (b.s.down K.y₂) = M₀.atom (b.s.down K.y₁)
      rw [hA.atom, hA.atom, K.My₂, K.My₁]
    · intro e
      have h1 := K.cut_a.2.2.2.2.2.1
      have h2 := K.cut_a.2.2.2.2.2.2
      rw [hA.inj e] at h1; rw [h1] at h2; cases h2
    · intro e
      have h1 := K.cut_b.2.2.2.2.2.1
      have h2 := K.cut_b.2.2.2.2.2.2
      rw [hA.inj e] at h1; rw [h1] at h2; cases h2
  have hpw' : ((U, N) :: ps).Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms) := by
    refine List.pairwise_cons.2 ⟨fun q hq => ?_, hpw⟩
    refine Finset.disjoint_left.2 fun v hv hvq => ?_
    exact hrem q hq v hvq (hint v hv)
  -- each joint keeps a bond outside the killed darts
  have hbond : ∀ y : b.s.D, (b.s.M.atom y = K.C.upper ∨ b.s.M.atom y = K.C.lower) →
      y ∉ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset b.s.D) →
      M₀.atom (b.s.down y) = b.s.M.atom y ∧ b.s.down y ∉ KillS ps ∪ PieceKill U N ∧
        M₀.mate (b.s.down y) ∉ KillS ps ∪ PieceKill U N := by
    intro y hyj hyG
    have hyC : b.s.M.atom y ∈ K.C.atoms := by
      rcases hyj with e | e
      · rw [e]; exact K.a_mem
      · rw [e]; exact K.b_mem
    have hz1 : M₀.atom (b.s.down y) = b.s.M.atom y := by rw [hA.atom]; exact hUe _ hyC
    obtain ⟨hmG, hmI⟩ := mate_nonnode_outside K hyj hyG
    refine ⟨hz1, ?_, ?_⟩
    · rintro (⟨p, hp, hk⟩ | hk)
      · exact he1 y p hp hk
      · have hjt := hk.2 (by rw [hz1]; exact hJ' _ hyj)
        apply hyG
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hjt with e | e | e | e
        · exact Or.inl (hA.inj e)
        · exact Or.inr (Or.inl (hA.inj e))
        · exact Or.inr (Or.inr (Or.inl (hA.inj e)))
        · exact Or.inr (Or.inr (Or.inr (hA.inj e)))
    · rw [hD.mate]
      rintro (⟨p, hp, hk⟩ | hk)
      · exact he1 _ p hp hk
      · have hat : M₀.atom (b.s.down (b.s.M.mate y)) ∈ U.atoms := hk.1
        rw [hA.atom] at hat
        have hb := hback _ (b.s.M.atom_mem _) hat
        have hmC : b.s.M.atom (b.s.M.mate y) ∈ K.C.atoms := by
          rw [hb]; exact hUK ▸ hat
        have hmj : b.s.M.atom (b.s.M.mate y) = K.C.upper ∨ b.s.M.atom (b.s.M.mate y) = K.C.lower := by
          by_contra hcon
          push Not at hcon
          exact hmI (by
            simp only [vineInterior, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hmC, hcon.1, hcon.2⟩)
        have hjt := hk.2 (by rw [hA.atom, hUe _ hmC]; exact hJ' _ hmj)
        apply hmG
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hjt with e | e | e | e
        · exact Or.inl (hA.inj e)
        · exact Or.inr (Or.inl (hA.inj e))
        · exact Or.inr (Or.inr (Or.inl (hA.inj e)))
        · exact Or.inr (Or.inr (Or.inr (hA.inj e)))
  have hbU : ∃ z, M₀.atom z = K.C.upper ∧ z ∉ KillS ps ∪ PieceKill U N ∧ M₀.mate z ∉ KillS ps ∪ PieceKill U N := by
    obtain ⟨y, hy, n1, n2⟩ := exists_third_dart b.s.M h3a (p := K.x₁) (q := K.x₂)
    have hyG : y ∉ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset b.s.D) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨n1, n2, fun e => K.ab_ne ?_, fun e => K.ab_ne ?_⟩
      · rw [← hy, e, K.My₁]
      · rw [← hy, e, K.My₂]
    obtain ⟨e1, e2, e3⟩ := hbond y (Or.inl hy) hyG
    exact ⟨_, e1.trans hy, e2, e3⟩
  have hbL : ∃ z, M₀.atom z = K.C.lower ∧ z ∉ KillS ps ∪ PieceKill U N ∧ M₀.mate z ∉ KillS ps ∪ PieceKill U N := by
    obtain ⟨y, hy, n1, n2⟩ := exists_third_dart b.s.M h3b (p := K.y₁) (q := K.y₂)
    have hyG : y ∉ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset b.s.D) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun e => K.ab_ne ?_, fun e => K.ab_ne ?_, n1, n2⟩
      · rw [← K.Mx₁, ← e, hy]
      · rw [← K.Mx₂, ← e, hy]
    obtain ⟨e1, e2, e3⟩ := hbond y (Or.inr hy) hyG
    exact ⟨_, e1.trans hy, e2, e3⟩
  have hj1 : ∃ z, M₀.atom z = U.upper ∧ z ∉ KillS ps ∪ PieceKill U N ∧ M₀.mate z ∉ KillS ps ∪ PieceKill U N := by
    rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1]; exact hbU
    · rw [← e2]; exact hbL
  have hj2 : ∃ z, M₀.atom z = U.lower ∧ z ∉ KillS ps ∪ PieceKill U N ∧ M₀.mate z ∉ KillS ps ∪ PieceKill U N := by
    rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e2]; exact hbL
    · rw [← e1]; exact hbU
  have hconn := hHF κ hκ ps (U, N) hps hpd hUF hpw' hj1 hj2
  set G : Finset b.s.D := {K.x₁, K.x₂, K.y₁, K.y₂} with hG
  have hGk : ∀ y ∈ G, b.s.down y ∈ PieceKill U N := by
    intro y hy
    simp only [hG, Finset.mem_insert, Finset.mem_singleton] at hy
    have hat : ∀ v ∈ K.C.atoms, v ∈ U.atoms := fun v hv => by rw [hUK]; exact hv
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨hup ▸ hat _ K.a_mem, fun _ => Or.inl rfl⟩
    · exact ⟨hup2 ▸ hat _ K.a_mem, fun _ => Or.inr (Or.inl rfl)⟩
    · exact ⟨hlow ▸ hat _ K.b_mem, fun _ => Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨hlow2 ▸ hat _ K.b_mem, fun _ => Or.inr (Or.inr (Or.inr rfl))⟩
  have hint_not : ∀ y : b.s.D, b.s.down y ∉ KillS ps ∪ PieceKill U N → b.s.M.atom y ∉ vineInterior K := by
    intro y hy hyi
    simp only [vineInterior, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hyi
    obtain ⟨hyC, hy1, hy2⟩ := hyi
    apply hy
    right
    have hz1 : M₀.atom (b.s.down y) = b.s.M.atom y := by rw [hA.atom, hUe _ hyC]
    refine ⟨by rw [hz1, hUK]; exact hyC, fun hj => ?_⟩
    rw [hz1] at hj
    exfalso
    rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rcases hj with hj | hj
      · exact hy1 (hj.trans e1.symm)
      · exact hy2 (hj.trans e2.symm)
    · rcases hj with hj | hj
      · exact hy2 (hj.trans e2.symm)
      · exact hy1 (hj.trans e1.symm)
  have hr := lift_connAvoid hA hD hinj hpres (KillS ps ∪ PieceKill U N) Set.subset_union_left
    (fun s t : V => s ∉ vineInterior K ∧ t ∉ vineInterior K ∧ ∃ z, b.s.M.atom z = s ∧ b.s.M.atom (b.s.M.mate z) = t ∧ z ∉ G ∧
      b.s.M.mate z ∉ G)
    (by
      intro x hx hmx
      rw [hD.mate] at hmx
      refine ⟨hint_not x hx, hint_not _ hmx, x, rfl, rfl, fun hxG => hx (Or.inr (hGk x hxG)), fun hxG => hmx (Or.inr (hGk _ hxG))⟩)
    hconn
  have hUu : U.upper ∈ U.atoms := object_mem_of_joint U (Or.inl rfl)
  have hUl : U.lower ∈ U.atoms := object_mem_of_joint U (Or.inr rfl)
  have e1 : ancInv b U.upper = U.upper := by
    have := ancInv_anc hinj (hint _ hUu).1
    rwa [hA.eps _ (hint _ hUu).1 (hint _ hUu).2] at this
  have e2 : ancInv b U.lower = U.lower := by
    have := ancInv_anc hinj (hint _ hUl).1
    rwa [hA.eps _ (hint _ hUl).1 (hint _ hUl).2] at this
  rw [e1, e2] at hr
  refine vineCut_F_le_of_outside K (G := G) (fun z hz => hz) ?_
  unfold VineOutsideConn
  rcases hJ with ⟨j1, j2⟩ | ⟨j1, j2⟩
  · rw [j1, j2]; exact hr
  · rw [j1, j2]; exact Relation.EqvGen.symm _ _ hr

end WaveTurbulence.FinalCountAsm
