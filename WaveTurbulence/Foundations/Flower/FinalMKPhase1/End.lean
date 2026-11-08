/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Inv2

/-! # C1b1 MK-PHASE1 (10): the end of Step 1 with survivors, `HendAtLE` (o75 Prop 4.7(3))

Along `Reach1LE`, `F + 1 ≤ 2R + #{dartless survivors}` (`endE_of_reach1LE`), hence `F ≤ 2R - 1 + m` at every reachable
state (`hendAtLE_of_inputs : HendAtLE`); the stuck condition is not needed.

* First-stage removals (collected objects of `Fst`; no survivor and no non-first-stage piece removed yet, by the order
  `hfo`): `fst_boundE`, main's `fst_boundL` (LowChain26) with `CnBoundF` (R164b) on `BookE`.
* Later collected vine removals do not increase `F`: `vine_F_le_of_hostConnFLE`, main's `vine_F_le_of_hostConnFL`
  (LowChain25) with the survivor pieces in the bookkeeping and the field `hostConnFLE` of `LowLoopClassHypsMK`.
* Step D1 and triple cuts do not increase `F` (main's argument).
* A survivor removal adds at most one component (`vine_F_le_succ`, `numComponents_vineStG`) and makes one more
  survivor dartless (`dartless_vinePostA/GA`).
Copied by source (sha256 in COPIED-SHA256SUMS). -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine.SourceVine

variable {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section endE
variable {M₀ : Molecule V D₀} {m : ℕ} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
  {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
  {A0 : Set (D₀ → (Fin d → ℤ))}

/-- **`HostConnFL` after earlier survivor removals** (the field `hostConnFLE` of `LowLoopClassHypsMK`, on `M₀`). -/
def HostConnFLE (M₀ : Molecule V D₀) (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀))
    (Fst : Set (Object M₀)) (E : Fin m → Object M₀) (L γ η : ℝ) (w : Mom d) (A0 : Set (D₀ → (Fin d → ℤ))) : Prop :=
  ∀ κ ∈ A0, ∀ (qs ps : List (Object M₀ × Quad D₀)) (p : Object M₀ × Quad D₀),
    (∀ q ∈ qs, PieceDataS E q) → (∀ q ∈ ps, PieceDataF C Un L γ η w κ q) →
    PieceDataF C Un L γ η w κ p → p.1 ∉ Fst → (p :: ps).Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms) →
    (∃ z, M₀.atom z = p.1.upper ∧ z ∉ KillS qs ∪ KillS ps ∪ PieceKill p.1 p.2 ∧
      M₀.mate z ∉ KillS qs ∪ KillS ps ∪ PieceKill p.1 p.2) →
    (∃ z, M₀.atom z = p.1.lower ∧ z ∉ KillS qs ∪ KillS ps ∪ PieceKill p.1 p.2 ∧
      M₀.mate z ∉ KillS qs ∪ KillS ps ∪ PieceKill p.1 p.2) →
    ConnAvoid M₀ (KillS qs ∪ KillS ps ∪ PieceKill p.1 p.2) p.1.upper p.1.lower

/-- **First-stage end bound** (main's `fst_boundL` with `CnBoundF` and `BookE`, no survivor piece yet). -/
theorem fst_boundE {Rn : ℕ} (hcn : CnBoundF M₀ C Un Fst L γ η w A0 Rn) (hκ : κ ∈ A0) {h : HSt V D₀}
    (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s) {ps : List (Object M₀ × Quad D₀)}
    (B : BookE M₀ C Un Fst E L γ η w κ h ps []) (hg : ∃ R', Good R' h.s) (hF : ∀ p ∈ ps, p.1 ∈ Fst) :
    h.s.M.numComponents + 1 ≤ 2 * Rn := by
  obtain ⟨⟨hinj, -, hpres, he1, -, he3, -⟩, hps, hpw, -, -, -⟩ := B
  obtain ⟨e, hE, hdeg⟩ := state_rem_isoE hA hD ps hinj hpres he1 he3
  obtain ⟨h1, h2⟩ := hcn κ hκ ps (fun p hp => ⟨hps p hp, hF p hp⟩) hpw
  rw [hE] at h1 h2
  rcases Nat.lt_or_ge (h.s.M.numComponents + e) (2 * Rn) with hlt | hge
  · omega
  · have heq : h.s.M.numComponents + e = 2 * Rn := le_antisymm h1 hge
    obtain ⟨v, hv, hv0⟩ := h2 heq
    rcases hdeg v hv hv0 with hE1 | ⟨c, hc, hc0⟩
    · omega
    · obtain ⟨R', hg⟩ := hg
      have := good_deg_pos hg c hc
      omega

/-- **A later collected vine removal does not increase the number of components** (main's
`vine_F_le_of_hostConnFL`, LowChain25, with the survivor pieces `qs` and `hostConnFLE`). -/
theorem vine_F_le_of_hostConnFLE (hHF : HostConnFLE M₀ C Un Fst E L γ η w A0) (hκ : κ ∈ A0) {b : HSt V D₀}
    (hA : AncRel M₀ b.s b.anc) (hD : DartRel M₀ b.s) {ps qs : List (Object M₀ × Quad D₀)}
    (B : BookE M₀ C Un Fst E L γ η w κ b ps qs) (K : VineCut b.s.M) (U : Object M₀)
    (hU : CollectedF C (Un κ) L γ η w κ U) (hUK : U.atoms = K.C.atoms)
    (hUD : U.ContainsDart (b.s.down K.x₁) ∧ U.ContainsDart (b.s.down K.x₂) ∧ U.ContainsDart (b.s.down K.y₁) ∧
      U.ContainsDart (b.s.down K.y₂))
    (hUJ : (M₀.atom (b.s.down K.x₁) = U.upper ∧ M₀.atom (b.s.down K.y₁) = U.lower) ∨
      (M₀.atom (b.s.down K.x₁) = U.lower ∧ M₀.atom (b.s.down K.y₁) = U.upper))
    (hint : UIntact U b) (hUF : U ∉ Fst) (h3a : 3 ≤ b.s.M.deg K.C.upper) (h3b : 3 ≤ b.s.M.deg K.C.lower) :
    K.post.numComponents ≤ b.s.M.numComponents := by
  obtain ⟨⟨hinj, hrem, hpres, he1, -, -, -⟩, hps, hpw, hqs, -, -⟩ := B
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
  have hpd : PieceDataF C Un L γ η w κ (U, N) := pieceData_of_cut hA K U hU hUD hUJ
  have hpw' : ((U, N) :: ps).Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms) := by
    refine List.pairwise_cons.2 ⟨fun q hq => ?_, hpw⟩
    refine Finset.disjoint_left.2 fun v hv hvq => ?_
    exact hrem q (List.mem_append_right _ hq) v hvq (hint v hv)
  have hlive : ∀ y : b.s.D, b.s.down y ∉ KillS qs ∪ KillS ps := by
    rintro y (⟨p, hp, hk⟩ | ⟨p, hp, hk⟩)
    · exact he1 y p (List.mem_append_left _ hp) hk
    · exact he1 y p (List.mem_append_right _ hp) hk
  -- each joint keeps a bond outside the killed darts
  have hbond : ∀ y : b.s.D, (b.s.M.atom y = K.C.upper ∨ b.s.M.atom y = K.C.lower) →
      y ∉ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset b.s.D) →
      M₀.atom (b.s.down y) = b.s.M.atom y ∧ b.s.down y ∉ KillS qs ∪ KillS ps ∪ PieceKill U N ∧
        M₀.mate (b.s.down y) ∉ KillS qs ∪ KillS ps ∪ PieceKill U N := by
    intro y hyj hyG
    have hyC : b.s.M.atom y ∈ K.C.atoms := by
      rcases hyj with e | e
      · rw [e]; exact K.a_mem
      · rw [e]; exact K.b_mem
    have hz1 : M₀.atom (b.s.down y) = b.s.M.atom y := by rw [hA.atom]; exact hUe _ hyC
    obtain ⟨hmG, hmI⟩ := mate_nonnode_outside K hyj hyG
    refine ⟨hz1, ?_, ?_⟩
    · rintro (hk | hk)
      · exact hlive y hk
      · have hjt := hk.2 (by rw [hz1]; exact hJ' _ hyj)
        apply hyG
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hjt with e | e | e | e
        · exact Or.inl (hA.inj e)
        · exact Or.inr (Or.inl (hA.inj e))
        · exact Or.inr (Or.inr (Or.inl (hA.inj e)))
        · exact Or.inr (Or.inr (Or.inr (hA.inj e)))
    · rw [hD.mate]
      rintro (hk | hk)
      · exact hlive _ hk
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
  have hbU : ∃ z, M₀.atom z = K.C.upper ∧ z ∉ KillS qs ∪ KillS ps ∪ PieceKill U N ∧
      M₀.mate z ∉ KillS qs ∪ KillS ps ∪ PieceKill U N := by
    obtain ⟨y, hy, n1, n2⟩ := exists_third_dart b.s.M h3a (p := K.x₁) (q := K.x₂)
    have hyG : y ∉ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset b.s.D) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨n1, n2, fun e => K.ab_ne ?_, fun e => K.ab_ne ?_⟩
      · rw [← hy, e, K.My₁]
      · rw [← hy, e, K.My₂]
    obtain ⟨e1, e2, e3⟩ := hbond y (Or.inl hy) hyG
    exact ⟨_, e1.trans hy, e2, e3⟩
  have hbL : ∃ z, M₀.atom z = K.C.lower ∧ z ∉ KillS qs ∪ KillS ps ∪ PieceKill U N ∧
      M₀.mate z ∉ KillS qs ∪ KillS ps ∪ PieceKill U N := by
    obtain ⟨y, hy, n1, n2⟩ := exists_third_dart b.s.M h3b (p := K.y₁) (q := K.y₂)
    have hyG : y ∉ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset b.s.D) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun e => K.ab_ne ?_, fun e => K.ab_ne ?_, n1, n2⟩
      · rw [← K.Mx₁, ← e, hy]
      · rw [← K.Mx₂, ← e, hy]
    obtain ⟨e1, e2, e3⟩ := hbond y (Or.inr hy) hyG
    exact ⟨_, e1.trans hy, e2, e3⟩
  have hj1 : ∃ z, M₀.atom z = U.upper ∧ z ∉ KillS qs ∪ KillS ps ∪ PieceKill U N ∧
      M₀.mate z ∉ KillS qs ∪ KillS ps ∪ PieceKill U N := by
    rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1]; exact hbU
    · rw [← e2]; exact hbL
  have hj2 : ∃ z, M₀.atom z = U.lower ∧ z ∉ KillS qs ∪ KillS ps ∪ PieceKill U N ∧
      M₀.mate z ∉ KillS qs ∪ KillS ps ∪ PieceKill U N := by
    rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e2]; exact hbL
    · rw [← e1]; exact hbU
  have hconn := hHF κ hκ qs ps (U, N) hqs hps hpd hUF hpw' hj1 hj2
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
  have hint_not : ∀ y : b.s.D, b.s.down y ∉ KillS qs ∪ KillS ps ∪ PieceKill U N →
      b.s.M.atom y ∉ vineInterior K := by
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
  have hKd : KillS (qs ++ ps) ⊆ KillS qs ∪ KillS ps ∪ PieceKill U N := by
    rintro z ⟨p, hp, hk⟩
    rcases List.mem_append.1 hp with hp | hp
    · exact Or.inl (Or.inl ⟨p, hp, hk⟩)
    · exact Or.inl (Or.inr ⟨p, hp, hk⟩)
  have hr := lift_connAvoid hA hD hinj hpres (KillS qs ∪ KillS ps ∪ PieceKill U N) hKd
    (fun s t : V => s ∉ vineInterior K ∧ t ∉ vineInterior K ∧ ∃ z, b.s.M.atom z = s ∧ b.s.M.atom (b.s.M.mate z) = t ∧
      z ∉ G ∧ b.s.M.mate z ∉ G)
    (by
      intro x hx hmx
      rw [hD.mate] at hmx
      refine ⟨hint_not x hx, hint_not _ hmx, x, rfl, rfl, fun hxG => hx (Or.inr (hGk x hxG)),
        fun hxG => hmx (Or.inr (hGk _ hxG))⟩)
    hconn
  have hUu : U.upper ∈ U.atoms := LGSpine.object_mem_of_joint U (Or.inl rfl)
  have hUl : U.lower ∈ U.atoms := LGSpine.object_mem_of_joint U (Or.inr rfl)
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

end endE

end WaveTurbulence.Flower.FinalMKPhase1
