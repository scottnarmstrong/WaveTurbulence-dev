/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowIface3
public import WaveTurbulence.Foundations.FinalCount.LowGardenLift
/-! **LOW-GARDEN (session 3): `CnBound` on `M.unloop` at the ORIGINAL index `R`, equality clause included** (R79 / NOTES section 5 item 3). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

section cn3
variable {V : Type*} [DecidableEq V] {D : Type} [Fintype D] [DecidableEq D] {d : ℕ} {M : Molecule V D}

theorem remMol_cn_transfer {R : ℕ} (ps : List (Object M × Quad D)) (ps' : List (Object M.unloop × Quad (NonLoop M)))
    (hrel : ∀ v, (∀ p ∈ ps, ¬ PieceInt p.1 v) ↔ (∀ p ∈ ps', ¬ PieceInt p.1 v))
    (hkill : ∀ z : NonLoop M, z.1 ∈ KillS ps ↔ z ∈ KillS ps')
    (hc1 : (remMol M ps).numComponents ≤ 2 * R)
    (hc2 : (remMol M ps).numComponents = 2 * R → ∃ v ∈ (remMol M ps).atoms, (remMol M ps).deg v = 0) :
    (remMol M.unloop ps').numComponents ≤ 2 * R ∧
      ((remMol M.unloop ps').numComponents = 2 * R → ∃ v ∈ (remMol M.unloop ps').atoms, (remMol M.unloop ps').deg v = 0) := by
  have hle := remMol_numComponents_le ps ps' hrel hkill
  refine ⟨hle.trans hc1, fun hE => ?_⟩
  obtain ⟨v, hv, hdeg⟩ := hc2 (le_antisymm hc1 (hE ▸ hle))
  refine ⟨v, ?_, ?_⟩
  · simp only [remMol, Finset.mem_filter] at hv ⊢
    exact ⟨hv.1, (hrel v).1 hv.2⟩
  · refine Nat.le_zero.1 (hdeg ▸ ?_)
    unfold Molecule.deg
    refine Finset.card_le_card_of_injOn
      (fun x => (⟨x.1.1, fun h => x.2.1 ((hkill x.1).1 h), fun h => x.2.2 ((hkill (M.unloop.mate x.1)).1 h)⟩ :
        {z : D // z ∉ KillS ps ∧ M.mate z ∉ KillS ps})) (fun x hx => ?_) (fun x _ y _ e => ?_)
    · exact (mem_dartsAt' (remMol M ps) v _).2 ((mem_dartsAt' (remMol M.unloop ps') v x).1 hx)
    · exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val e))

theorem cnBound_unloop_R {Un : (D → Fin d → ℤ) → Set (Object M)} {Fst : Set (Object M)}
    {Un' : (NonLoop M → Fin d → ℤ) → Set (Object M.unloop)} {Adm : (D → Fin d → ℤ) → Prop} {L γ η : ℝ}
    {A0' : Set (NonLoop M → Fin d → ℤ)} {C : CollData M} {R : ℕ}
    (hFst : ∀ U ∈ Fst, ∃ i, U = C.collection i)
    (hA0' : ∀ κ' ∈ A0', unloopAdm M Adm κ')
    (hcn : CnBound M C Un Fst L γ η (0 : Mom d) {κ | Adm κ} R) :
    CnBound M.unloop C.unloop Un' (unloopSet M Fst) L γ η (0 : Mom d) A0' R := by
  intro κ' hκ' ps' hps' hpw'
  obtain ⟨κ, hκ, rfl⟩ := hA0' κ' hκ'
  have hex : ∀ p ∈ ps', ∃ U ∈ Fst, ∃ hU : LoopFreeSet M U.atoms, p.1 = U.unloop hU := fun p hp => by
    obtain ⟨U, hU, he⟩ := (hps' p hp).2
    exact ⟨U, hU, Object.loopFree U, he⟩
  have hlfp : ∀ p ∈ ps', LoopFreeSet M p.1.atoms := fun p hp => by
    obtain ⟨U, -, hU, he⟩ := hex p hp
    rw [he]; exact hU
  have hne : Nonempty (Object M) ∨ ps' = [] := by
    cases ps' with
    | nil => exact Or.inr rfl
    | cons p ps => exact Or.inl ⟨p.1.lift (hlfp p (by simp))⟩
  have hnc : (remMol M.unloop ps').numComponents ≤ 2 * R ∧
      ((remMol M.unloop ps').numComponents = 2 * R → ∃ v ∈ (remMol M.unloop ps').atoms, (remMol M.unloop ps').deg v = 0) := by
    rcases hne with hU0 | rfl
    · let U0 : Object M := Classical.choice hU0
      set ps := ps'.map (liftP U0) with hps
      have hat : ∀ p ∈ ps', (liftP U0 p).1.atoms = p.1.atoms := fun p hp => by rw [liftP_fst U0 p (hlfp p hp)]; rfl
      have hup : ∀ p ∈ ps', (liftP U0 p).1.upper = p.1.upper := fun p hp => by rw [liftP_fst U0 p (hlfp p hp)]; rfl
      have hlo : ∀ p ∈ ps', (liftP U0 p).1.lower = p.1.lower := fun p hp => by rw [liftP_fst U0 p (hlfp p hp)]; rfl
      have hrel : ∀ v, (∀ p ∈ ps, ¬ PieceInt p.1 v) ↔ (∀ p ∈ ps', ¬ PieceInt p.1 v) := by
        intro v
        simp only [hps, List.forall_mem_map]
        refine forall_congr' fun p => forall_congr' fun hp => ?_
        unfold PieceInt
        rw [hat p hp, hup p hp, hlo p hp]
      have hkill : ∀ z : NonLoop M, z.1 ∈ KillS ps ↔ z ∈ KillS ps' := by
        intro z
        unfold KillS
        simp only [hps, List.mem_map, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨_, ⟨p, hp, rfl⟩, hz⟩
          exact ⟨p, hp, (pieceKill_liftP U0 p (hlfp p hp) z).1 hz⟩
        · rintro ⟨p, hp, hz⟩
          exact ⟨_, ⟨p, hp, rfl⟩, (pieceKill_liftP U0 p (hlfp p hp) z).2 hz⟩
      have hpd : ∀ q ∈ ps, PieceData C Un L γ η (0 : Mom d) κ q ∧ q.1 ∈ Fst := by
        intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
        obtain ⟨U, hU, hUl, he⟩ := hex p hp
        have hlf := hlfp p hp
        have h1 : (liftP U0 p).1 = U := by rw [liftP_fst U0 p hlf]; exact lift_eq_of_unloop hlf hUl he
        obtain ⟨-, hc4, hj, hdist⟩ := (hps' p hp).1
        refine ⟨⟨Or.inl (by rw [h1]; exact hFst U hU), ?_, ?_, ?_⟩, by rw [h1]; exact hU⟩
        · rw [liftP_fst U0 p hlf]
          exact ⟨(Object.lift_containsDart p.1 hlf p.2.1).2 hc4.1, (Object.lift_containsDart p.1 hlf p.2.2.1).2 hc4.2.1,
            (Object.lift_containsDart p.1 hlf p.2.2.2.1).2 hc4.2.2.1, (Object.lift_containsDart p.1 hlf p.2.2.2.2).2 hc4.2.2.2⟩
        · rw [liftP_fst U0 p hlf]
          rcases hj with ⟨a, b⟩ | ⟨a, b⟩
          · exact Or.inl ⟨a, b⟩
          · exact Or.inr ⟨a, b⟩
        · exact ⟨hdist.1, hdist.2.1, fun e => hdist.2.2.1 (Subtype.ext e), fun e => hdist.2.2.2 (Subtype.ext e)⟩
      have hpw : ps.Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms) :=
        List.pairwise_map.2 (hpw'.imp_of_mem fun {a b} ha hb h => by rw [hat a ha, hat b hb]; exact h)
      obtain ⟨hc1, hc2⟩ := hcn κ hκ ps hpd hpw
      exact remMol_cn_transfer ps ps' hrel hkill hc1 hc2
    · obtain ⟨hc1, hc2⟩ := hcn κ hκ [] (by simp) List.Pairwise.nil
      exact remMol_cn_transfer (M := M) [] [] (by simp) (by simp [KillS]) hc1 hc2
  exact hnc

end cn3

end WaveTurbulence.FinalCountAsm
