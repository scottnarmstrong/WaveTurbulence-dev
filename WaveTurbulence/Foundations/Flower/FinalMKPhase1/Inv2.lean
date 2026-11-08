/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Inv

/-! # C1b1 MK-PHASE1 (9): `reach1LE_book`, and the two obligations of the re-cut step

See `Inv.lean` for the statements' roles. -/

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
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section inv
variable {M₀ : Molecule V D₀} {m : ℕ} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
  {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

/-- `BookE` along a removal of a collected object (`vinePost` or `vinePostG`). -/
theorem BookE.coll {b h' : HSt V D₀} (hA : AncRel M₀ b.s b.anc) {ps qs : List (Object M₀ × Quad D₀)}
    (B : BookE M₀ C Un Fst E L γ η w κ b ps qs) (K : VineCut b.s.M) (U : Object M₀)
    (hU : CollectedF C (Un κ) L γ η w κ U)
    (hUD : U.ContainsDart (b.s.down K.x₁) ∧ U.ContainsDart (b.s.down K.x₂) ∧ U.ContainsDart (b.s.down K.y₁) ∧
      U.ContainsDart (b.s.down K.y₂))
    (hUJ : (M₀.atom (b.s.down K.x₁) = U.upper ∧ M₀.atom (b.s.down K.y₁) = U.lower) ∨
      (M₀.atom (b.s.down K.x₁) = U.lower ∧ M₀.atom (b.s.down K.y₁) = U.upper))
    (hord : U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' b) (hint : UIntact U b)
    (hgeom : GeomBook M₀ b (qs ++ ps) → GeomBook M₀ h' ((U, quadK b K) :: (qs ++ ps)))
    (hmono : ∀ U' : Object M₀, Dartless U' b → Dartless U' h') :
    BookE M₀ C Un Fst E L γ η w κ h' ((U, quadK b K) :: ps) qs := by
  obtain ⟨hG, hps, hpw, hqs, hqd, hfo⟩ := B
  have hnd : ¬ Dartless U b := not_dartless_of_cd hUD.1
  refine ⟨(hgeom hG).congr ?_, ?_, ?_, hqs, ?_, ?_⟩
  · intro p
    simp only [List.mem_cons, List.mem_append]
    tauto
  · intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact pieceData_of_cut hA K U hU hUD hUJ
    · exact hps p hp
  · refine List.pairwise_cons.2 ⟨fun q hq => ?_, hpw⟩
    refine Finset.disjoint_left.2 fun v hv hvq => ?_
    exact hG.rem q (List.mem_append_right _ hq) v hvq (hint v hv)
  · intro q hq
    obtain ⟨j, e, hj, hk⟩ := hqd q hq
    exact ⟨j, e, hmono _ hj, fun k hk' => hmono _ (hk k hk')⟩
  · intro hex U' hU'
    refine hmono U' ?_
    rcases hord with hUF | hall
    · exfalso
      rcases hex with ⟨p, hp, hpF⟩ | hq
      · rcases List.mem_cons.1 hp with rfl | hp
        · exact hpF hUF
        · exact hnd (hfo (Or.inl ⟨p, hp, hpF⟩) U hUF)
      · exact hnd (hfo (Or.inr hq) U hUF)
    · exact hall U' hU'

/-- `BookE` along a survivor removal (`vinePost` or `vinePostG`). -/
theorem BookE.surv {b h' : HSt V D₀} {ps qs : List (Object M₀ × Quad D₀)}
    (B : BookE M₀ C Un Fst E L γ η w κ b ps qs) (K : VineCut b.s.M) (i : Fin m) (hPD : PieceDataS E (E i, quadK b K))
    (ho : SurvOrder Fst E i b)
    (hgeom : GeomBook M₀ b (qs ++ ps) → GeomBook M₀ h' ((E i, quadK b K) :: (qs ++ ps)))
    (hmono : ∀ U' : Object M₀, Dartless U' b → Dartless U' h') (hdi : Dartless (E i) h') :
    BookE M₀ C Un Fst E L γ η w κ h' ps ((E i, quadK b K) :: qs) := by
  obtain ⟨hG, hps, hpw, hqs, hqd, hfo⟩ := B
  refine ⟨hgeom hG, hps, hpw, ?_, ?_, fun _ U' hU' => hmono U' (ho.1 U' hU')⟩
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hPD
    · exact hqs q hq
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨i, rfl, hdi, fun k hk => hmono _ (ho.2 k hk)⟩
    · obtain ⟨j, e, hj, hk⟩ := hqd q hq
      exact ⟨j, e, hmono _ hj, fun k hk' => hmono _ (hk k hk')⟩

theorem bookE_init (M₀ : Molecule V D₀) (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀))
    (Fst : Set (Object M₀)) (E : Fin m → Object M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) :
    BookE M₀ C Un Fst E L γ η w κ (HSt.init M₀) [] [] :=
  ⟨geomBook_init M₀, by simp, List.Pairwise.nil, by simp, by simp, by simp⟩

/-- **The bookkeeping along the survivor Step 1** (main's `collInv_of_reach1L` and `reach1L_connInv`): every collected
object is dartless or intact; `ConnInvLE` holds, or every collected object and every survivor is dartless. -/
theorem reach1LE_book [Infinite V] {Rn : ℕ} (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ U U' : Object M₀, CollectedF C (Un κ) L γ η w κ U → CollectedF C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hsd : ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    {h : HSt V D₀} (hr : Reach1LE C Un Fst E L γ η w κ h) :
    (∀ U, CollectedF C (Un κ) L γ η w κ U → Dartless U h ∨ UIntact U h) ∧
      ((∃ ps qs, BookE M₀ C Un Fst E L γ η w κ h ps qs) ∨
        ((∀ U, CollectedF C (Un κ) L γ η w κ U → Dartless U h) ∧ ∀ i, Dartless (E i) h)) := by
  induction hr with
  | refl => exact ⟨fun U _ => Or.inr (uIntact_init U), Or.inl ⟨[], [], bookE_init M₀ C Un Fst E L γ η w κ⟩⟩
  | @tail b h' hrb hs ih =>
    have hrb' : Reach1LE C Un Fst E L γ η w κ b := hrb
    have hA := reach1LE_ancRel hrb'
    have hD : DartRel M₀ b.s := (invL_reach1E hS h0 hrb').choose_spec.2.rel
    obtain ⟨ihc, ihb⟩ := ih
    have hmono : ∀ U' : Object M₀, Dartless U' b → Dartless U' h' := fun U' hd => HStep1RLE.dartless hs hd
    cases hs with
    | vine K R kp hs U hU hUK hUD hUJ hord =>
      have hint : UIntact U b := (ihc U hU).resolve_left (not_dartless_of_cd hUD.1)
      refine ⟨fun U' hU' => ?_, ?_⟩
      · rcases ihc U' hU' with hd | hi
        · exact Or.inl (fun x hx => hd x.1 hx)
        · exact (collInv_vine_step hA hD K U' U hUK hUD hUJ hi (hdisj U' U hU' hU)).1 R kp
      · rcases ihb with ⟨ps, qs, B⟩ | ⟨hd, -⟩
        · exact Or.inl ⟨_, qs, B.coll hA K U hU hUD hUJ hord hint
            (fun hG => hG.vine hA K R kp U (remA_of_intact hA K U hUK hint hUD hUJ)) hmono⟩
        · exact absurd hUD.1 (hd U hU K.x₁)
    | d1 K hs U hU hUK hUD hUJ hord =>
      have hint : UIntact U b := (ihc U hU).resolve_left (not_dartless_of_cd hUD.1)
      refine ⟨fun U' hU' => ?_, ?_⟩
      · rcases ihc U' hU' with hd | hi
        · exact Or.inl (fun x hx => hd x.1 hx)
        · exact (collInv_vine_step hA hD K U' U hUK hUD hUJ hi (hdisj U' U hU' hU)).2
      · rcases ihb with ⟨ps, qs, B⟩ | ⟨hd, -⟩
        · exact Or.inl ⟨_, qs, B.coll hA K U hU hUD hUJ hord hint
            (fun hG => hG.vineG hA K U (remA_of_intact hA K U hUK hint hUD hUJ)) hmono⟩
        · exact absurd hUD.1 (hd U hU K.x₁)
    | triple _ hs hs3 hall hallE hFle =>
      exact ⟨fun U hU => Or.inl (hmono U (hall U hU)),
        Or.inr ⟨fun U hU => hmono U (hall U hU), fun i => hmono _ (hallE i)⟩⟩
    | survVine K R kp i hs hc ho =>
      rcases ihb with ⟨ps, qs, B⟩ | ⟨-, hd⟩
      · have hinj := B.geom.inj
        refine ⟨fun U' hU' => ?_, Or.inl ⟨ps, _, B.surv K i (pieceDataS_of_remA hA K i hc) ho
          (fun hG => hG.vine hA K R kp (E i) (remA_of_survCut hc)) hmono (dartless_vinePostA hA hD hinj K R kp (remA_of_survCut hc))⟩⟩
        rcases ihc U' hU' with hdU | hi
        · exact Or.inl (hmono U' hdU)
        · exact Or.inr ((collInv_surv_step hA hinj K i hc U' hi (hsd U' hU' i)).1 R kp)
      · exact absurd hc.2.1.1 (hd i K.x₁)
    | survD1 K i hs hc ho =>
      rcases ihb with ⟨ps, qs, B⟩ | ⟨-, hd⟩
      · have hinj := B.geom.inj
        refine ⟨fun U' hU' => ?_, Or.inl ⟨ps, _, B.surv K i (pieceDataS_of_remA hA K i hc) ho
          (fun hG => hG.vineG hA K (E i) (remA_of_survCut hc)) hmono (dartless_vinePostGA hA hD hinj K (remA_of_survCut hc))⟩⟩
        rcases ihc U' hU' with hdU | hi
        · exact Or.inl (hmono U' hdU)
        · exact Or.inr (collInv_surv_step hA hinj K i hc U' hi (hsd U' hU' i)).2
      · exact absurd hc.2.1.1 (hd i K.x₁)
    | survRC K i hs hc ho =>
      rcases ihb with ⟨ps, qs, B⟩ | ⟨-, hd⟩
      · have hinj := B.geom.inj
        refine ⟨fun U' hU' => ?_, Or.inl ⟨ps, _, B.surv K i (pieceDataS_of_remA hA K i hc) ho
          (fun hG => hG.vineG hA K (E i) (remA_of_survCut hc)) hmono (dartless_vinePostGA hA hD hinj K (remA_of_survCut hc))⟩⟩
        rcases ihc U' hU' with hdU | hi
        · exact Or.inl (hmono U' hdU)
        · exact Or.inr (collInv_surv_step hA hinj K i hc U' hi (hsd U' hU' i)).2
      · exact absurd hc.2.1.1 (hd i K.x₁)

/-- **The survivors meeting a removed survivor's piece.** If an atom `a` of the survivor `E i` (not dartless) lies in a
removed piece, that piece is the survivor `E j` with `j + 1 = i` (`survChain`; collected pieces miss survivors; a later
survivor is removed only after `E i`). -/
theorem BookE.piece_meet {h : HSt V D₀} {ps qs : List (Object M₀ × Quad D₀)}
    (B : BookE M₀ C Un Fst E L γ η w κ h ps qs)
    (hsd : ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hchain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1)
    {i : Fin m} (hi : ¬ Dartless (E i) h) {a : V} (ha : a ∈ (E i).atoms) {p : Object M₀ × Quad D₀}
    (hp : p ∈ qs ++ ps) (hpa : a ∈ p.1.atoms) :
    ∃ j : Fin m, j.val + 1 = i.val ∧ p.1 = E j ∧ a ∈ (E j).atoms ∩ (E i).atoms ∧
      ((E j).atoms ∩ (E i).atoms).card = 1 := by
  rcases List.mem_append.1 hp with hq | hq
  · obtain ⟨j, e, hj, hk⟩ := B.hqd p hq
    have hji : j ≠ i := fun e' => hi (e' ▸ hj)
    have hnd : ¬ Disjoint (E j).atoms (E i).atoms :=
      fun hdis => Finset.disjoint_left.1 hdis (e ▸ hpa) ha
    obtain ⟨hc, hcard⟩ := hchain j i hji hnd
    rcases hc with hc | hc
    · exact ⟨j, hc, e, Finset.mem_inter.2 ⟨e ▸ hpa, ha⟩, hcard⟩
    · exact absurd (hk i (Fin.lt_def.2 (by omega))) hi
  · exact absurd ha (Finset.disjoint_left.1 (hsd p.1 (B.hps p hq).1 i) hpa)

/-- **Obligation 1 (`hone`)**: at a re-cut of the survivor `E i` from a state with the bookkeeping, at least one joint is
`ε`, i.e. at most one joint is an `α/β` re-cut remnant. -/
theorem recut_hone {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc) {ps qs : List (Object M₀ × Quad D₀)}
    (B : BookE M₀ C Un Fst E L γ η w κ h ps qs)
    (hsd : ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hchain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1)
    (K : VineCut h.s.M) (i : Fin m) (hc : SurvCut E i h K) :
    h.s.cls K.C.upper = .eps ∨ h.s.cls K.C.lower = .eps := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hu, hl⟩ := hcon
  have hinj := B.geom.inj
  obtain ⟨-, hJ, -, hat⟩ := (remA_of_survCut hc).facts hA hinj
  have hi : ¬ Dartless (E i) h := not_dartless_of_cd hc.2.1.1
  obtain ⟨pu, hpu, hpua⟩ := B.geom.neps _ (objectAtoms_sub K.C K.a_mem) hu
  obtain ⟨pl, hpl, hpla⟩ := B.geom.neps _ (objectAtoms_sub K.C K.b_mem) hl
  obtain ⟨ju, hju, -, hmu, hcu⟩ := B.piece_meet hsd hchain hi (hat _ K.a_mem) hpu hpua
  obtain ⟨jl, hjl, -, hml, -⟩ := B.piece_meet hsd hchain hi (hat _ K.b_mem) hpl hpla
  have hj : ju = jl := Fin.ext (by omega)
  subst hj
  have he : h.anc K.C.upper = h.anc K.C.lower := Finset.card_le_one.1 (le_of_eq hcu) _ hmu _ hml
  have hne : (E i).upper ≠ (E i).lower := (LGSpine.object_oh (E i)).basic.2.2.2.1
  rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact hne (e1.symm.trans (he.trans e2))
  · exact hne (e2.symm.trans (he.symm.trans e1))

/-- **Obligation 2**: C1a's non-closing configuration (a re-cut whose two joints are both `α/β` remnants) does not
occur from a state with the bookkeeping. -/
theorem recut_not_both_ab {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc) {ps qs : List (Object M₀ × Quad D₀)}
    (B : BookE M₀ C Un Fst E L γ η w κ h ps qs)
    (hsd : ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hchain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1)
    (K : VineCut h.s.M) (i : Fin m) (hc : SurvCut E i h K) :
    ¬ ((h.s.cls K.C.upper).IsAB ∧ (h.s.cls K.C.lower).IsAB) := by
  rintro ⟨hu, hl⟩
  rcases recut_hone hA B hsd hchain K i hc with e | e
  · rw [e] at hu; exact hu
  · rw [e] at hl; exact hl

/-- **The re-cut pays one pending re-cut** (`hpend` of C1a's `hW_RCp`, via `pendRC_step`). -/
theorem recut_pend {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s)
    {ps qs : List (Object M₀ × Quad D₀)} (B : BookE M₀ C Un Fst E L γ η w κ h ps qs)
    (hsd : ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hchain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1)
    (K : VineCut h.s.M) (i : Fin m) (hc : SurvCut E i h K)
    (hrc : h.s.cls K.C.upper ≠ .eps ∨ h.s.cls K.C.lower ≠ .eps) :
    pendRC E (h.vinePostG K) + 1 ≤ pendRC E h := by
  have hinj := B.geom.inj
  obtain ⟨-, -, -, hat⟩ := (remA_of_survCut hc).facts hA hinj
  have hi : ¬ Dartless (E i) h := not_dartless_of_cd hc.2.1.1
  have hj : ∃ j, j < i ∧ ¬ Disjoint (E j).atoms (E i).atoms := by
    have key : ∀ c, c ∈ K.C.atoms → h.s.cls c ≠ .eps → ∃ j, j < i ∧ ¬ Disjoint (E j).atoms (E i).atoms := by
      intro c hcK hce
      obtain ⟨p, hp, hpa⟩ := B.geom.neps _ (objectAtoms_sub K.C hcK) hce
      obtain ⟨j, hji, -, hm, -⟩ := B.piece_meet hsd hchain hi (hat _ hcK) hp hpa
      exact ⟨j, Fin.lt_def.2 (by omega), fun hdis => Finset.disjoint_left.1 hdis (Finset.mem_inter.1 hm).1
        (Finset.mem_inter.1 hm).2⟩
    rcases hrc with h1 | h1
    · exact key _ K.a_mem h1
    · exact key _ K.b_mem h1
  exact pendRC_step E i (fun k hd => fun x hx => hd x.1 hx) hi (dartless_vinePostGA hA hD hinj K (remA_of_survCut hc)) hj

end inv

end WaveTurbulence.Flower.FinalMKPhase1
