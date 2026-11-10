/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGHost
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEnd3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeC1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeConn
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeDV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmGHost`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY: `HostConn` and `HostConnF` from S4-SHAPE** (census item (b)).

Generic over the molecule (applied to `M₀ = inlMol G.molecule` in the garden instantiation), for one decoration `κ`:
* `pieceOf O`: the removal piece of a collected object (its atoms, joints and `ContainsDart` darts); it is S4-SHAPE's `ordPiece` for an
  ordinary object and the universe's adjoint removal for a hyper object (`adjOf`).
* `lift_keep`: a dart kept by a removal (S4-SHAPE `KeepDart`) is killed by no removed piece, provided every removed piece inside the
  host `S` is removed in `S` and every other one is `Harmless` for `S`.
* `dvWitnessReduction_vc`: the DV′ witness reduction of S4-SHAPE for every ordinary member of `C₂` (low form; main's
  `dvWitnessReduction_typeV` used that a vine (V) of a DV host containing a member is that member, false for T-vines).
* `ordinary_host_conn`: for an ordinary member `U` of `C₂` and removed pieces `qs` (any collected objects, pairwise disjoint), the
  joints of `U` are joined avoiding the killed darts, when `U` itself is among the removed pieces or not.
* `hostConnF_of`: `HostConnF` (hyper pieces: the retained designated bond; ordinary non-first-stage pieces: `ordinary_host_conn`).
* `hostConn_of`: `HostConn` (three-atom collected objects are members of `C₂`; ordinary: `ordinary_host_conn` with `U` removed; hyper:
  the designated bond, or, when the cut atom is a joint, a bond from the interior atom to the other joint). 

**Low-range change (L6-HDS).** The ordinary members of `C₂` are one or two double bonds or T-vines (`hsh`, TARGET
`subsetvc`′); the DV hosts are DV′s; `dvWitnessReduction_vc` replaces `dvWitnessReduction_typeV`.
-/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.Vine

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

/-- The removal piece of an object: its atoms, its joints and its `ContainsDart` darts. -/
noncomputable def pieceOf {M : Molecule V D} (O : Src.Object Src.γL M) : RemovalPiece V D :=
  ⟨O.atoms, O.upper, O.lower, univ.filter (fun z => O.ContainsDart z)⟩

theorem pieceOf_vc {M : Molecule V D} (O : Src.Object Src.γL M) (hvc : ∃ h, O.shape = .vc h) : pieceOf O = ordPiece M O := by
  obtain ⟨h, hs⟩ := hvc
  unfold pieceOf ordPiece
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold Src.Object.ContainsDart
  rw [hs]

/-- The adjoint piece of a hyper object. -/
def adjOf {M : Molecule V D} : Src.Object Src.γL M → Option (AdjointPiece M)
  | ⟨_, _, _, .vc _⟩ => none
  | ⟨S, a, b, .hyper R⟩ => some ⟨S, a, b, R.added, R.ends_eq, R.adjoint.1⟩

theorem adjOf_spec {M : Molecule V D} (O : Src.Object Src.γL M) (A : AdjointPiece M) (h : adjOf O = some A) :
    A.toRemoval = pieceOf O ∧ A.atoms = O.atoms ∧ ∃ R, O.shape = .hyper R := by
  obtain ⟨S, a, b, sh⟩ := O
  cases sh with
  | vc _ => simp [adjOf] at h
  | hyper R =>
    simp only [adjOf, Option.some.injEq] at h
    subst h
    refine ⟨?_, rfl, R, rfl⟩
    unfold AdjointPiece.toRemoval adjointRemoval pieceOf
    congr 1
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    unfold Src.Object.ContainsDart
    simp only
    tauto

theorem adjOf_hyper {M : Molecule V D} (O : Src.Object Src.γL M) (hh : ∃ R, O.shape = .hyper R) : ∃ A, adjOf O = some A := by
  obtain ⟨S, a, b, sh⟩ := O
  obtain ⟨R, hR⟩ := hh
  cases sh with
  | vc _ => cases hR
  | hyper R' => exact ⟨_, rfl⟩

theorem containsDart_inGroup' {M : Molecule V D} (O : Src.Object Src.γL M) {z : D} (h : O.ContainsDart z) : M.InGroup O.atoms z := by
  unfold Src.Object.ContainsDart at h
  split at h
  · exact h
  · exact h.2.2

section lift
variable {M : Molecule V D} {C : CollData M} {Un : (D → (Fin d → ℤ)) → Set (Src.Object Src.γL M)} {L γ η : ℝ} {w : Mom d}
  {κ : D → (Fin d → ℤ)}

/-- **Kept darts are not killed.** -/
theorem lift_keep (hnl : ∀ z, M.atom z ≠ M.atom (M.mate z)) {S : Finset V} {qs : List (Src.Object Src.γL M × Quad D)}
    (hq : ∀ q ∈ qs, PieceData C Un L γ η w κ q) (hH : ∀ q ∈ qs, ¬ q.1.atoms ⊆ S → Harmless M S q.1)
    (Lst : List (RemovalPiece V D)) (hL : ∀ q ∈ qs, q.1.atoms ⊆ S → pieceOf q.1 ∈ Lst) {y : D}
    (hy : KeepDart M S Lst y) : ∀ q ∈ qs, y ∉ PieceKill q.1 q.2 := by
  intro q hqm hk
  obtain ⟨hat, himp⟩ := hk
  obtain ⟨-, hCD, -, -⟩ := hq q hqm
  have hN : ∀ t, t = q.2.1 ∨ t = q.2.2.1 ∨ t = q.2.2.2.1 ∨ t = q.2.2.2.2 → q.1.ContainsDart t := by
    rintro t (rfl | rfl | rfl | rfl)
    exacts [hCD.1, hCD.2.1, hCD.2.2.1, hCD.2.2.2]
  have hyS : M.atom y ∈ S := (Finset.mem_filter.1 hy.1).1
  have hmyS : M.atom (M.mate y) ∈ S := (Finset.mem_filter.1 hy.2.1).1
  by_cases hin : q.1.atoms ⊆ S
  · have hP := hL q hqm hin
    have hnot : M.atom y ∉ (pieceOf q.1).interior := (Finset.mem_filter.1 hy.1).2 _ hP
    have hj : M.atom y = q.1.upper ∨ M.atom y = q.1.lower := by
      by_contra hj
      push Not at hj
      apply hnot
      simp only [RemovalPiece.interior, pieceOf, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hat, hj.1, hj.2⟩
    have hcd := hN y (himp hj)
    exact (hy.2.2 _ hP).1 (by simp only [pieceOf, Finset.mem_filter, Finset.mem_univ, true_and]; exact hcd)
  · obtain ⟨hH1, hH2⟩ := hH q hqm hin
    have hj : M.atom y = q.1.upper ∨ M.atom y = q.1.lower := by
      by_contra hj
      push Not at hj
      have hnj : M.atom y ∉ ({q.1.upper, q.1.lower} : Finset V) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact hj
      exact Finset.disjoint_left.1 hH1 (Finset.mem_sdiff.2 ⟨hat, hnj⟩) hyS
    have hg := containsDart_inGroup' q.1 (hN y (himp hj))
    exact hnl y (hH2 y hyS hmyS hg)

/-- A chain of kept bonds is a chain avoiding the killed darts. -/
theorem connAvoid_of_keep (hnl : ∀ z, M.atom z ≠ M.atom (M.mate z)) {S : Finset V} {qs : List (Src.Object Src.γL M × Quad D)}
    (hq : ∀ q ∈ qs, PieceData C Un L γ η w κ q) (hH : ∀ q ∈ qs, ¬ q.1.atoms ⊆ S → Harmless M S q.1)
    (Lst : List (RemovalPiece V D)) (hL : ∀ q ∈ qs, q.1.atoms ⊆ S → pieceOf q.1 ∈ Lst) (Kx : Set D)
    (hKx : ∀ y, KeepDart M S Lst y → y ∉ Kx) {a b : V}
    (h : Relation.EqvGen (Subpro.KeepAdj M S Lst) a b) : ConnAvoid M (KillS qs ∪ Kx) a b := by
  induction h with
  | rel s t hst =>
    obtain ⟨y, hy, rfl, rfl⟩ := hst
    have hmy := keepDart_mate M S Lst hy
    refine Relation.EqvGen.rel _ _ ⟨y, rfl, rfl, ?_, ?_⟩
    · rintro (⟨q, hqm, hk⟩ | hk)
      · exact lift_keep hnl hq hH Lst hL hy q hqm hk
      · exact hKx y hy hk
    · rintro (⟨q, hqm, hk⟩ | hk)
      · exact lift_keep hnl hq hH Lst hL hmy q hqm hk
      · exact hKx _ hmy hk
  | refl s => exact Relation.EqvGen.refl _
  | symm s t _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans s t u _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end lift

/-- **The DV′ witness reduction for any ordinary member of `C₂`** (low form of main's `dvWitnessReduction_typeV`, whose
step "a vine (V) member inside a DV branch is the branch" fails for T-vines: a T-vine branch has T-vine members). If `U`
contains a branch it contains both joints, so it is a branch (`DS.block_in_DV_both_joints_eq_branchL`); otherwise it lies
in one branch (`ordinary_in_dv_vine`) and `dv_vine_case` (G3's `UnselOK` and the maximality of `U`) reduces the host. -/
theorem dvWitnessReduction_vc {M : Molecule V D} (hM : M.IsMolecule) {L γ η : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)}
    (C : CollData M) (Unsel : Set (Src.Object Src.γL M)) (hUO : C.UnselOK L γ η w κ Unsel) {U : Src.Object Src.γL M}
    (hU : U ∈ C.C2Of L γ η w κ Unsel) (hUvc : ∃ h, U.shape = .vc h) : DVWitnessReduction L γ η w κ C Unsel U := by
  intro A B a b hσ hA hB hAB hUD hh hC
  have hUB := object_vc_block U hUvc
  by_cases hAU : A ⊆ U.atoms
  · have haU : a ∈ U.atoms := hAU hA.block.2.1
    have hbU : b ∈ U.atoms := hAU hA.block.2.2.1
    rcases DS.block_in_DV_both_joints_eq_branchL hM hσ (DS.isTVine_of_sigma_one hA hσ) (DS.isTVine_of_sigma_one hB hσ)
      hAB hUB hUD haU hbU with he | he
    · exact Or.inl ⟨A, B, a, b, hσ, hA, hB, hAB, hUD, hh, hC, U, hU, Or.inl he⟩
    · exact Or.inl ⟨A, B, a, b, hσ, hA, hB, hAB, hUD, hh, hC, U, hU, Or.inr he⟩
  · rcases ordinary_in_dv_vine hM U hσ hA hB hUD hAU with hUA | hUB'
    · exact dv_vine_case C Unsel hUO hU hσ hA hB hAB hUA hh hC
    · exact dv_vine_case C Unsel hUO hU hσ hB hA (by rw [Finset.inter_comm]; exact hAB) hUB'
        (by rwa [Finset.union_comm]) (by simpa [Finset.union_comm] using hC)

section host
variable {M : Molecule V D} (hM : M.IsMolecule) {L γ η : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {c0 : V → Mom d}
  (hκ : M.IsDecoration L w c0 κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c0 v = 0)
  {C : CollData M} {Un : (D → (Fin d → ℤ)) → Set (Src.Object Src.γL M)}
  (hd22 : ∀ O ∈ C.C2Of L γ η w κ (Un κ), ∀ O' ∈ C.C2Of L γ η w κ (Un κ), O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms)
  (hsh : ∀ O ∈ C.C2Of L γ η w κ (Un κ), (∃ h, O.shape = .vc h) →
    DoubleChain M O.atoms O.upper O.lower 1 ∨ DoubleChain M O.atoms O.upper O.lower 2 ∨ M.IsTVine O.atoms O.upper O.lower)
  (hUO : C.UnselOK L γ η w κ (Un κ))
include hM hκ hc0 hd22 hsh hUO

/-- **Host connectivity for an ordinary member of `C₂`** after the removal of pairwise-disjoint collected pieces `qs` and, optionally,
of `U` itself (`extra`): the joints of `U` are joined by bonds of `M` none of which is killed by a piece of `qs`, nor is at an
interior atom of `U` when `extra`. -/
theorem ordinary_host_conn (hnl : ∀ z, M.atom z ≠ M.atom (M.mate z)) {U : Src.Object Src.γL M} (hU : U ∈ C.C2Can L γ η w κ (Un κ))
    (hUvc : ∃ h, U.shape = .vc h) (qs : List (Src.Object Src.γL M × Quad D)) (hq : ∀ q ∈ qs, PieceData C Un L γ η w κ q)
    (hpw : qs.Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms)) (extra : Bool)
    (hextra : extra = true → ∀ q ∈ qs, Disjoint q.1.atoms U.atoms) :
    ConnAvoid M (KillS qs ∪ (if extra then {z | M.atom z ∈ U.atoms ∧ M.atom z ≠ U.upper ∧ M.atom z ≠ U.lower} else ∅))
      U.upper U.lower := by
  have hU2 : U ∈ C.C2Of L γ η w κ (Un κ) := hU.1
  have hDV : DVWitnessReduction L γ η w κ C (Un κ) U := by
    rcases hsh U hU2 hUvc with h | h | h
    · exact dvWitnessReduction_of_unselOK hM C _ hUO hU2 (by have := doubleChain_card h; omega)
    · exact dvWitnessReduction_of_unselOK hM C _ hUO hU2 (by have := doubleChain_card h; omega)
    · exact dvWitnessReduction_vc hM C _ hUO hU2 hUvc
  obtain ⟨S, hUS, hSo, hSh, hSC, hclean⟩ := exists_good_host hM hκ hc0 C (Un κ) hd22 hU2 hDV
  -- collected pieces inside `S` are members of `C₂`
  have hinC2 : ∀ q ∈ qs, q.1.atoms ⊆ S → q.1 ∈ C.C2Of L γ η w κ (Un κ) := by
    intro q hqm hin
    rcases (hq q hqm).1 with ⟨i, hi⟩ | hc
    · exfalso
      have hne := object_mem_of_joint q.1 (Or.inl rfl)
      exact Finset.disjoint_left.1 (hSC i) (hin hne) (hi ▸ hne)
    · exact hc.1
  have hH : ∀ q ∈ qs, ¬ q.1.atoms ⊆ S → Harmless M S q.1 := by
    intro q hqm hin
    rcases (hq q hqm).1 with ⟨i, hi⟩ | hc
    · rw [hi]; exact harmless_of_disjoint (hSC i).symm
    · exact (hclean q.1 hc.1).resolve_left hin
  -- the removal lists
  let qin := qs.filter (fun q => decide (q.1.atoms ⊆ S))
  let psQ : List (RemovalPiece V D) :=
    (qin.filter (fun q => decide (∃ h, q.1.shape = .vc h))).map (fun q => ordPiece M q.1)
  let psL : List (RemovalPiece V D) := (if extra then [ordPiece M U] else []) ++ psQ
  let qsL : List (AdjointPiece M) := qin.filterMap (fun q => adjOf q.1)
  have hmemqin : ∀ q, q ∈ qin ↔ q ∈ qs ∧ q.1.atoms ⊆ S := fun q => by simp [qin]
  have hqdis : ∀ p ∈ qs, ∀ q ∈ qs, p ≠ q → Disjoint p.1.atoms q.1.atoms := pairwise_ne_disj hpw
  have hpsQ : ∀ P ∈ psQ, ∃ q ∈ qs, q.1.atoms ⊆ S ∧ (∃ h, q.1.shape = .vc h) ∧ P = ordPiece M q.1 := by
    intro P hP
    obtain ⟨q, hqf, rfl⟩ := List.mem_map.1 hP
    obtain ⟨hq1, hq2⟩ := List.mem_filter.1 hqf
    obtain ⟨hqs, hin⟩ := (hmemqin q).1 hq1
    exact ⟨q, hqs, hin, of_decide_eq_true hq2, rfl⟩
  have hps : ∀ P ∈ psL, ∃ O ∈ C.C2Of L γ η w κ (Un κ), (∃ h, O.shape = .vc h) ∧ O.atoms ⊆ S ∧ P = ordPiece M O := by
    intro P hP
    rcases List.mem_append.1 hP with hP | hP
    · cases extra
      · simp at hP
      · simp only [ite_true, List.mem_singleton] at hP
        exact ⟨U, hU2, hUvc, hUS, hP⟩
    · obtain ⟨q, hqs, hin, hvc, rfl⟩ := hpsQ P hP
      exact ⟨q.1, hinC2 q hqs hin, hvc, hin, rfl⟩
  have hqsL : ∀ A ∈ qsL, ∃ O ∈ C.C2Of L γ η w κ (Un κ), (∃ R, O.shape = .hyper R) ∧ O.atoms ⊆ S ∧ A.atoms = O.atoms := by
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
    have hUQ : extra = true → ∀ Q ∈ psQ, Disjoint (ordPiece M U).atoms Q.atoms := by
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
  obtain ⟨-, -, hconn⟩ := host_removal_connected hM hκ hc0 C (Un κ) hd22 hsh hU2 hUvc hUS hSo psL qsL hps hqsL hdis hQdis
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
    cases extra
    · simp at hk
    · simp only [ite_true, Set.mem_ofPred_eq] at hk
      have hP : ordPiece M U ∈ Lst := List.mem_append_left _ (List.mem_append_left _ (by simp))
      apply (Finset.mem_filter.1 hy.1).2 _ hP
      simp only [RemovalPiece.interior, ordPiece, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact hk

end host

end WaveTurbulence.GammaLow.FinalCount.H
