/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKGarden.PoolF
public import WaveTurbulence.Foundations.FinalCount.LowGardenHost

/-! # C1c MK-GARDEN / HostF: host connectivity with survivor removals

Main's `ordinary_host_conn` (AsmGHost), `hostConnL_of` (LowGardenHost) and `hostConnF_of` (AsmGHost2), generic over
the collection data `C` of the pool, with one more family of killed darts `Kx` whose atoms lie in a set `F ⊆ C.hinges`.
The good host of an ordinary member of `C₂` avoids `C.hinges`, hence `F`, so its kept bonds avoid `Kx`. Applied with
`C = poolF C'` and `F = C'.forb` (the survivor atoms), `Kx` = the darts killed by earlier survivor removals; this is
C0's math check item 2 (the `HostF` containers avoid the survivor atoms). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical

namespace WaveTurbulence.Flower.FinalMKGarden
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
  WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Vine WaveTurbulence.Flower.FinalMKDefs

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

section host
variable {M : Molecule V D} (hM : M.IsMolecule) {L γ η : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {c0 : V → Mom d}
  (hκ : M.IsDecoration L w c0 κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c0 v = 0)
  {C : CollData M} {Un : (D → (Fin d → ℤ)) → Set (Object M)}
  (hd22 : ∀ O ∈ C.C2Of L γ η w κ (Un κ), ∀ O' ∈ C.C2Of L γ η w κ (Un κ), O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms)
  (hsh : ∀ O ∈ C.C2Of L γ η w κ (Un κ), (∃ h, O.shape = .vc h) →
    DoubleChain M O.atoms O.upper O.lower 1 ∨ DoubleChain M O.atoms O.upper O.lower 2 ∨ M.IsVine .V O.atoms O.upper O.lower)
  (hUO : C.UnselOK L γ η w κ (Un κ))
include hM hκ hc0 hd22 hsh hUO

/-- **`ordinary_host_conn` with extra killed darts** `Kx` at atoms of `F ⊆ C.hinges`. -/
theorem ordinary_host_connK (hnl : ∀ z, M.atom z ≠ M.atom (M.mate z)) {U : Object M}
    (hU : U ∈ C.C2Can L γ η w κ (Un κ)) (hUvc : ∃ h, U.shape = .vc h) (qs : List (Object M × Quad D))
    (hq : ∀ q ∈ qs, PieceData C Un L γ η w κ q) (hpw : qs.Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms))
    (extra : Bool) (hextra : extra = true → ∀ q ∈ qs, Disjoint q.1.atoms U.atoms)
    (F : Finset V) (hF : F ⊆ C.hinges) (Kx : Set D) (hKx : ∀ z ∈ Kx, M.atom z ∈ F) :
    ConnAvoid M (KillS qs ∪ (Kx ∪ (if extra then {z | M.atom z ∈ U.atoms ∧ M.atom z ≠ U.upper ∧ M.atom z ≠ U.lower}
      else ∅))) U.upper U.lower := by
  have hU2 : U ∈ C.C2Of L γ η w κ (Un κ) := hU.1
  have hDV : Subpro.DVWitnessReduction L γ η w κ C (Un κ) U := by
    rcases hsh U hU2 hUvc with h | h | h
    · exact Subpro.dvWitnessReduction_of_unselOK hM C _ hUO hU2 (by have := doubleChain_card h; omega)
    · exact Subpro.dvWitnessReduction_of_unselOK hM C _ hUO hU2 (by have := doubleChain_card h; omega)
    · exact dvWitnessReduction_typeV hM C _ hU2 h
  obtain ⟨S, hUS, hSo, hSh, hSC, hclean⟩ := Subpro.exists_good_host hM hκ hc0 C (Un κ) hd22 hU2 hDV
  have hinC2 : ∀ q ∈ qs, q.1.atoms ⊆ S → q.1 ∈ C.C2Of L γ η w κ (Un κ) := by
    intro q hqm hin
    rcases (hq q hqm).1 with ⟨i, hi⟩ | hc
    · exfalso
      have hne := object_mem_of_joint q.1 (Or.inl rfl)
      exact Finset.disjoint_left.1 (hSC i) (hin hne) (hi ▸ hne)
    · exact hc.1
  have hH : ∀ q ∈ qs, ¬ q.1.atoms ⊆ S → Subpro.Harmless M S q.1 := by
    intro q hqm hin
    rcases (hq q hqm).1 with ⟨i, hi⟩ | hc
    · rw [hi]; exact Subpro.harmless_of_disjoint (hSC i).symm
    · exact (hclean q.1 hc.1).resolve_left hin
  let qin := qs.filter (fun q => decide (q.1.atoms ⊆ S))
  let psQ : List (RemovalPiece V D) :=
    (qin.filter (fun q => decide (∃ h, q.1.shape = .vc h))).map (fun q => Subpro.ordPiece M q.1)
  let psL : List (RemovalPiece V D) := (if extra then [Subpro.ordPiece M U] else []) ++ psQ
  let qsL : List (AdjointPiece M) := qin.filterMap (fun q => adjOf q.1)
  have hmemqin : ∀ q, q ∈ qin ↔ q ∈ qs ∧ q.1.atoms ⊆ S := fun q => by simp [qin]
  have hqdis : ∀ p ∈ qs, ∀ q ∈ qs, p ≠ q → Disjoint p.1.atoms q.1.atoms := pairwise_ne_disj hpw
  have hpsQ : ∀ P ∈ psQ, ∃ q ∈ qs, q.1.atoms ⊆ S ∧ (∃ h, q.1.shape = .vc h) ∧ P = Subpro.ordPiece M q.1 := by
    intro P hP
    obtain ⟨q, hqf, rfl⟩ := List.mem_map.1 hP
    obtain ⟨hq1, hq2⟩ := List.mem_filter.1 hqf
    obtain ⟨hqs, hin⟩ := (hmemqin q).1 hq1
    exact ⟨q, hqs, hin, of_decide_eq_true hq2, rfl⟩
  have hps : ∀ P ∈ psL, ∃ O ∈ C.C2Of L γ η w κ (Un κ), (∃ h, O.shape = .vc h) ∧ O.atoms ⊆ S ∧
      P = Subpro.ordPiece M O := by
    intro P hP
    rcases List.mem_append.1 hP with hP | hP
    · cases extra
      · simp at hP
      · simp only [ite_true, List.mem_singleton] at hP
        exact ⟨U, hU2, hUvc, hUS, hP⟩
    · obtain ⟨q, hqs, hin, hvc, rfl⟩ := hpsQ P hP
      exact ⟨q.1, hinC2 q hqs hin, hvc, hin, rfl⟩
  have hqsL : ∀ A ∈ qsL, ∃ O ∈ C.C2Of L γ η w κ (Un κ), (∃ R, O.shape = .hyper R) ∧ O.atoms ⊆ S ∧
      A.atoms = O.atoms := by
    intro A hA
    obtain ⟨q, hq1, hqA⟩ := List.mem_filterMap.1 hA
    obtain ⟨hqs, hin⟩ := (hmemqin q).1 hq1
    obtain ⟨-, hat, hh⟩ := adjOf_spec q.1 A hqA
    exact ⟨q.1, hinC2 q hqs hin, hh, hin, hat⟩
  have hdis : ∀ P ∈ psL, ∀ Q ∈ psL, P ≠ Q → Disjoint P.atoms Q.atoms := by
    have hQQ : ∀ P ∈ psQ, ∀ Q ∈ psQ, P ≠ Q → Disjoint P.atoms Q.atoms := by
      intro P hP Q hQ hne
      obtain ⟨p, hp, -, -, rfl⟩ := hpsQ P hP
      obtain ⟨q, hq', -, -, rfl⟩ := hpsQ Q hQ
      exact hqdis p hp q hq' (fun e => hne (by rw [e]))
    have hUQ : extra = true → ∀ Q ∈ psQ, Disjoint (Subpro.ordPiece M U).atoms Q.atoms := by
      intro hex Q hQ
      obtain ⟨q, hq', -, -, rfl⟩ := hpsQ Q hQ
      exact (hextra hex q hq').symm
    intro P hP Q hQ hne
    rcases List.mem_append.1 hP with hP1 | hP2 <;> rcases List.mem_append.1 hQ with hQ1 | hQ2
    · cases extra
      · simp at hP1
      · simp only [ite_true, List.mem_singleton] at hP1 hQ1
        exact absurd (hP1.trans hQ1.symm) hne
    · cases extra
      · simp at hP1
      · simp only [ite_true, List.mem_singleton] at hP1
        rw [hP1]; exact hUQ rfl Q hQ2
    · cases extra
      · simp at hQ1
      · simp only [ite_true, List.mem_singleton] at hQ1
        rw [hQ1]; exact (hUQ rfl P hP2).symm
    · exact hQQ P hP2 Q hQ2 hne
  have hQdis : ∀ P ∈ qsL, ∀ Q ∈ qsL, P ≠ Q → Disjoint P.atoms Q.atoms := by
    intro P hP Q hQ hne
    obtain ⟨p, hp1, hpA⟩ := List.mem_filterMap.1 hP
    obtain ⟨q, hq1, hqA⟩ := List.mem_filterMap.1 hQ
    obtain ⟨hps', -⟩ := (hmemqin p).1 hp1
    obtain ⟨hqs', -⟩ := (hmemqin q).1 hq1
    rw [(adjOf_spec p.1 P hpA).2.1, (adjOf_spec q.1 Q hqA).2.1]
    refine hqdis p hps' q hqs' (fun e => hne ?_)
    rw [e] at hpA; rw [hpA] at hqA; exact Option.some.inj hqA
  obtain ⟨-, -, hconn⟩ := Subpro.host_removal_connected hM hκ hc0 C (Un κ) hd22 hsh hU2 hUvc hUS hSo psL qsL hps hqsL
    hdis hQdis
  rw [Subpro.sameComponent_iff_eqvGen] at hconn
  set Lst := psL ++ qsL.map AdjointPiece.toRemoval with hLst
  refine connAvoid_of_keep hnl hq hH Lst ?_ _ ?_ hconn
  · intro q hqm hin
    rcases object_shape_cases q.1 with hvc | hh
    · rw [pieceOf_vc q.1 hvc]
      refine List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨q, ?_, rfl⟩))
      exact List.mem_filter.2 ⟨(hmemqin q).2 ⟨hqm, hin⟩, decide_eq_true hvc⟩
    · obtain ⟨A, hA⟩ := adjOf_hyper q.1 hh
      rw [← (adjOf_spec q.1 A hA).1]
      exact List.mem_append_right _ (List.mem_map.2 ⟨A, List.mem_filterMap.2 ⟨q, (hmemqin q).2 ⟨hqm, hin⟩, hA⟩, rfl⟩)
  · intro y hy hk
    rcases hk with hk | hk
    · have hyS : M.atom y ∈ S := (Finset.mem_filter.1 hy.1).1
      exact Finset.disjoint_left.1 hSh hyS (hF (hKx y hk))
    cases extra
    · simp at hk
    · simp only [ite_true, Set.mem_ofPred_eq] at hk
      have hP : Subpro.ordPiece M U ∈ Lst := List.mem_append_left _ (List.mem_append_left _ (by simp))
      apply (Finset.mem_filter.1 hy.1).2 _ hP
      simp only [RemovalPiece.interior, Subpro.ordPiece, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
        not_or]
      exact hk

/-- **`hostConnL_of` with extra killed darts** `Kx` at atoms of `F ⊆ C.hinges`. -/
theorem hostConnLK_of (hnl : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hC13 : ∀ i, (C.collection i).atoms.card ≠ 3)
    (F : Finset V) (hF : F ⊆ C.hinges) (Kx : Set D) (hKx : ∀ z ∈ Kx, M.atom z ∈ F)
    (ps : List (Object M × Quad D)) (U : Object M) (a x b : V)
    (hps : ∀ p ∈ ps, PieceData C Un L γ η w κ p) (hpw : ps.Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms))
    (hdisU : ∀ p ∈ ps, Disjoint p.1.atoms U.atoms) (hUc : Collected C (Un κ) L γ η w κ U) (hUat : U.atoms = {a, x, b})
    (hax : a ≠ x) (hxb : x ≠ b) (hab : a ≠ b)
    (hclos : ∀ z, M.atom z = x → M.atom (M.mate z) = a ∨ M.atom (M.mate z) = b) :
    ConnAvoid M ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ Kx ∪ {z | M.atom z = x}) a b := by
  have hcard : U.atoms.card = 3 := by
    rw [hUat, Finset.card_insert_of_notMem (by simp [hax, hab]), Finset.card_pair hxb]
  have hU : U ∈ C.C2Can L γ η w κ (Un κ) := by
    rcases hUc with ⟨i, hi⟩ | h
    · exact absurd (hi ▸ hcard) (hC13 i)
    · exact h
  have hUH : Disjoint U.atoms C.hinges := (Subpro.c2Of_disjoint_c1_hinges C hU.1).2
  have hxU : x ∈ U.atoms := by rw [hUat]; simp
  have haU : a ∈ U.atoms := by rw [hUat]; simp
  have hbU : b ∈ U.atoms := by rw [hUat]; simp
  have hKS : ∀ z, z ∈ (⋃ p ∈ ps, PieceKill p.1 p.2) ↔ z ∈ KillS ps := by
    intro z
    simp only [Set.mem_iUnion, exists_prop]
    rfl
  have hfree : ∀ z, M.atom z ∈ U.atoms → z ∉ (⋃ p ∈ ps, PieceKill p.1 p.2) ∪ Kx := by
    intro z hz hk
    rcases hk with hk | hk
    · rw [hKS] at hk
      exact not_mem_killS_of_atom (fun p hp hzp => Finset.disjoint_left.1 (hdisU p hp) hzp hz) hk
    · exact Finset.disjoint_left.1 hUH hz (hF (hKx z hk))
  have huU := object_mem_of_joint U (Or.inl rfl)
  have hlU := object_mem_of_joint U (Or.inr rfl)
  have hul : U.upper ≠ U.lower := (object_oh U).basic.2.2.2.1
  have hmem3 : ∀ v ∈ U.atoms, v = a ∨ v = x ∨ v = b := by
    intro v hv; rw [hUat] at hv; simpa using hv
  have hjab : x ≠ U.upper → x ≠ U.lower → (U.upper = a ∧ U.lower = b) ∨ (U.upper = b ∧ U.lower = a) := by
    intro h1 h2
    rcases hmem3 _ huU with e1 | e1 | e1 <;> rcases hmem3 _ hlU with e2 | e2 | e2
    · exact absurd (e1.trans e2.symm) hul
    · exact absurd e2.symm h2
    · exact Or.inl ⟨e1, e2⟩
    · exact absurd e1.symm h1
    · exact absurd e1.symm h1
    · exact absurd e1.symm h1
    · exact Or.inr ⟨e1, e2⟩
    · exact absurd e2.symm h2
    · exact absurd (e1.trans e2.symm) hul
  have hgood : ∀ z, M.atom z ∈ U.atoms → M.atom (M.mate z) ∈ U.atoms → M.atom z ≠ x → M.atom (M.mate z) ≠ x →
      z ∉ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ Kx ∪ {z | M.atom z = x}) ∧
        M.mate z ∉ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ Kx ∪ {z | M.atom z = x}) := by
    intro z h1 h2 h3' h4
    exact ⟨fun hk => hk.elim (hfree z h1) h3', fun hk => hk.elim (hfree _ h2) h4⟩
  by_cases hxj : x = U.upper ∨ x = U.lower
  · have hallx : ∀ z, M.atom z = x → M.InGroup U.atoms z := by
      intro z hz
      refine ⟨hz ▸ hxU, ?_⟩
      rcases hclos z hz with e | e <;> rw [e]
      · exact haU
      · exact hbU
    have hdegx : M.degIn U.atoms x = M.deg x := degIn_eq_deg_of_all hallx
    have hdx : M.deg x ≤ 3 := by
      rcases object_shape_cases U with hvc | ⟨R, hR⟩
      · have := object_vc_degIn U hvc hxj
        omega
      · have := object_hyper_degIn U ⟨R, hR⟩ hxj
        omega
    obtain ⟨j', m, hj'ab, hmab, hjm, hm, hatm⟩ : ∃ j' m, (j' = a ∨ j' = b) ∧ (m = a ∨ m = b) ∧ j' ≠ m ∧
        U.IsInterior m ∧ U.atoms = {x, m, j'} := by
      rcases hxj with e | e
      · rcases hmem3 _ hlU with e2 | e2 | e2
        · refine ⟨a, b, Or.inl rfl, Or.inr rfl, hab, ⟨hbU, ?_, ?_⟩, ?_⟩
          · rw [← e]; exact hxb.symm
          · rw [e2]; exact hab.symm
          · rw [hUat]; ext v; simp; tauto
        · exact absurd (e.symm.trans e2.symm) hul
        · refine ⟨b, a, Or.inr rfl, Or.inl rfl, hab.symm, ⟨haU, ?_, ?_⟩, ?_⟩
          · rw [← e]; exact hax
          · rw [e2]; exact hab
          · rw [hUat]; ext v; simp; tauto
      · rcases hmem3 _ huU with e2 | e2 | e2
        · refine ⟨a, b, Or.inl rfl, Or.inr rfl, hab, ⟨hbU, ?_, ?_⟩, ?_⟩
          · rw [e2]; exact hab.symm
          · rw [← e]; exact hxb.symm
          · rw [hUat]; ext v; simp; tauto
        · exact absurd (e2.trans e) hul
        · refine ⟨b, a, Or.inr rfl, Or.inl rfl, hab.symm, ⟨haU, ?_, ?_⟩, ?_⟩
          · rw [e2]; exact hab
          · rw [← e]; exact hax
          · rw [hUat]; ext v; simp; tauto
    obtain ⟨z, hz1, hz2⟩ := hyper_interior_bond_other hnl U hatm hm hdx
    have hmx : m ≠ x := by rcases hmab with rfl | rfl; exacts [hax, hxb.symm]
    have hjx : j' ≠ x := by rcases hj'ab with rfl | rfl; exacts [hax, hxb.symm]
    have hg := hgood z (hz1 ▸ hm.1) (hz2 ▸ (by rw [hatm]; simp)) (hz1 ▸ hmx) (hz2 ▸ hjx)
    have hc := connAvoid_of_bond z hz1 hz2 hg.1 hg.2
    rcases hj'ab with rfl | rfl <;> rcases hmab with rfl | rfl
    · exact absurd rfl hjm
    · exact Relation.EqvGen.symm _ _ hc
    · exact hc
    · exact absurd rfl hjm
  · push Not at hxj
    rcases object_shape_cases U with hvc | ⟨R, hR⟩
    · have hx1 : x ≠ U.upper := hxj.1
      have hx2 : x ≠ U.lower := hxj.2
      have h := ordinary_host_connK hM hκ hc0 hd22 hsh hUO hnl hU hvc ps hps hpw true (fun _ q hq => hdisU q hq)
        F hF Kx hKx
      have h' : ConnAvoid M ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ Kx ∪ {z | M.atom z = x}) U.upper U.lower := by
        refine connAvoid_mono ?_ h
        rintro z ((hk | hk) | hk)
        · exact Or.inl ((hKS z).1 hk)
        · exact Or.inr (Or.inl hk)
        · right; right
          simp only [ite_true, Set.mem_ofPred_eq]
          have hk' : M.atom z = x := hk
          rw [hk']; exact ⟨hxU, hx1, hx2⟩
      rcases hjab hx1 hx2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2] at h'; exact h'
      · rw [e1, e2] at h'; exact Relation.EqvGen.symm _ _ h'
    · have key : ∀ (s t : V), M.atom R.added = s → M.atom (M.mate R.added) = t → s ∈ U.atoms → t ∈ U.atoms →
          s ≠ x → t ≠ x → ConnAvoid M ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ Kx ∪ {z | M.atom z = x}) s t := by
        intro s t e1 e2 hs ht hsx htx
        have hg := hgood R.added (by rw [e1]; exact hs) (by rw [e2]; exact ht) (by rw [e1]; exact hsx)
          (by rw [e2]; exact htx)
        exact connAvoid_of_bond R.added e1 e2 hg.1 hg.2
      rcases hyper_added_ends U (R := R) with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have hc := key _ _ e1 e2 huU hlU (fun e => hxj.1 e.symm) (fun e => hxj.2 e.symm)
        rcases hjab hxj.1 hxj.2 with ⟨f1, f2⟩ | ⟨f1, f2⟩
        · rw [f1, f2] at hc; exact hc
        · rw [f1, f2] at hc; exact Relation.EqvGen.symm _ _ hc
      · have hc := key _ _ e1 e2 hlU huU (fun e => hxj.2 e.symm) (fun e => hxj.1 e.symm)
        rcases hjab hxj.1 hxj.2 with ⟨f1, f2⟩ | ⟨f1, f2⟩
        · rw [f1, f2] at hc; exact Relation.EqvGen.symm _ _ hc
        · rw [f1, f2] at hc; exact hc

/-- **`hostConnF_of` with extra killed darts** `Kx` at atoms of `F ⊆ C.hinges`, `F` disjoint from `C₁`. -/
theorem hostConnFK_of (hnl : ∀ z, M.atom z ≠ M.atom (M.mate z)) {Fst : Set (Object M)}
    (hFst : ∀ i, (∃ h, (C.collection i).shape = .vc h) → C.collection i ∈ Fst)
    (F : Finset V) (hF : F ⊆ C.hinges) (hF1 : ∀ i, Disjoint (C.collection i).atoms F) (Kx : Set D)
    (hKx : ∀ z ∈ Kx, M.atom z ∈ F)
    (ps : List (Object M × Quad D)) (p : Object M × Quad D) (hps : ∀ q ∈ ps, PieceData C Un L γ η w κ q)
    (hp : PieceData C Un L γ η w κ p) (hpF : p.1 ∉ Fst) (hpw : (p :: ps).Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms)) :
    ConnAvoid M (Kx ∪ KillS ps ∪ PieceKill p.1 p.2) p.1.upper p.1.lower := by
  rcases object_shape_cases p.1 with hvc | ⟨R, hR⟩
  · have hU : p.1 ∈ C.C2Can L γ η w κ (Un κ) := by
      rcases hp.1 with ⟨i, hi⟩ | hc
      · exact absurd (hi ▸ hFst i (hi ▸ hvc)) hpF
      · exact hc
    have hq : ∀ q ∈ p :: ps, PieceData C Un L γ η w κ q := by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hp
      · exact hps q hq
    have h := ordinary_host_connK hM hκ hc0 hd22 hsh hUO hnl hU hvc (p :: ps) hq hpw false (by simp) F hF Kx hKx
    refine connAvoid_mono ?_ h
    rintro z ((hk | ⟨q, hq, hk⟩) | hk)
    · exact Or.inr (Or.inl hk)
    · exact Or.inl ⟨q, List.mem_cons_of_mem _ hq, hk⟩
    · exact Or.inl ⟨p, List.mem_cons_self, hk⟩
  · have hdis : ∀ q ∈ ps, Disjoint p.1.atoms q.1.atoms := (List.pairwise_cons.1 hpw).1
    have hpFd : Disjoint p.1.atoms F := by
      rcases hp.1 with ⟨i, hi⟩ | hc
      · rw [hi]; exact hF1 i
      · exact Finset.disjoint_of_subset_right hF (Subpro.c2Of_disjoint_c1_hinges C hc.1).2
    have hjp : ∀ z, (M.atom z = p.1.upper ∨ M.atom z = p.1.lower) → M.atom z ∈ p.1.atoms := by
      intro z hz
      rcases hz with e | e <;> rw [e]
      · exact object_mem_of_joint p.1 (Or.inl rfl)
      · exact object_mem_of_joint p.1 (Or.inr rfl)
    have hnotq : ∀ z, (M.atom z = p.1.upper ∨ M.atom z = p.1.lower) → ∀ q ∈ ps, M.atom z ∉ q.1.atoms :=
      fun z hz q hq hzq => Finset.disjoint_left.1 (hdis q hq) (hjp z hz) hzq
    have hgood : ∀ z, (z = R.added ∨ z = M.mate R.added) → (M.atom z = p.1.upper ∨ M.atom z = p.1.lower) →
        z ∉ Kx ∪ KillS ps ∪ PieceKill p.1 p.2 := by
      rintro z hz hj ((h | h) | h)
      · exact Finset.disjoint_left.1 hpFd (hjp z hj) (hKx z h)
      · exact not_mem_killS_of_atom (hnotq z hj) h
      · exact hyper_added_not_killed hp hR hz hj h
    rcases hyper_added_ends p.1 (R := R) with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact connAvoid_of_bond R.added e1 e2 (hgood _ (Or.inl rfl) (Or.inl e1)) (hgood _ (Or.inr rfl) (Or.inr e2))
    · exact Relation.EqvGen.symm _ _ (connAvoid_of_bond R.added e1 e2 (hgood _ (Or.inl rfl) (Or.inr e1))
        (hgood _ (Or.inr rfl) (Or.inl e2)))

end host

/-! ### Survivor kills sit at the forbidden atoms -/

section surv
universe u
variable {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {M₀ : Molecule V D₀} {m : ℕ}

theorem killS_surv_atom {E : Fin m → Object M₀} {qs : List (Object M₀ × Quad D₀)} (hqs : ∀ q ∈ qs, PieceDataS E q)
    {z : D₀} (hz : z ∈ KillS qs) : M₀.atom z ∈ survAtomsM E := by
  obtain ⟨q, hq, hk⟩ := hz
  obtain ⟨⟨i, hi⟩, -⟩ := hqs q hq
  exact mem_survAtomsM.2 ⟨i, hi ▸ hk.1⟩

end surv

end WaveTurbulence.Flower.FinalMKGarden
