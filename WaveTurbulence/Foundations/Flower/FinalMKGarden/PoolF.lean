/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Count
public import WaveTurbulence.Foundations.FinalCount.LowGardenLift

/-! # C1c MK-GARDEN / PoolF: the forbidden pool as main's pool, and its loop transport

* `poolF C`: main's `CollData` with `hinges := C.hinges ∪ C.forb`. It is used ONLY as the carrier of the pool:
  `InPF`/`C2OfF`/`C2CanF`/`CollectedF`/`UnselOKF`/`PieceDataF` are main's `InP`/`C2Of`/`C2Can`/`Collected`/
  `UnselOK`/`PieceData` of `(poolF C)` (definitionally). No obligation (`hingeSG`, `hingeJoint`, `crossing`) is ever asked
  of `(poolF C)`.
* `PoolContained C`: `subpro` (4) alone, the only obligation read by main's loop transports of the pool (GL27). For
  `(poolF C)` it follows from `SubproOblGMK.contained` and `forb = survAtomsM E` (`poolContained_toF`).
* The GL27 transports (`InP_unloop`, `InP_lift`, `C2Of_unloop`, `C2Of_lift`, `UnselOK.unloop`, `collected_lift`) with
  `PoolContained` in place of `SubproOblG`.
* `SubproOblGMK.unloop`: GL26's `SubproOblG.unloop` with the survivor fields. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical

namespace WaveTurbulence.Flower.FinalMKGarden
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
  WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.FinalMKDefs

section toF
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ} {M₀ : Molecule V D₀}
  {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {m : ℕ}

/-- The carrier of the forbidden pool: main's collection data with the forbidden atoms added to the hinge set (used
only for the pool definitions, never for obligations). -/
def poolF (C : CollDataMK M₀) : CollData M₀ :=
  { C.toCollData with hinges := C.hinges ∪ C.forb }

theorem unselOKF_iff (C : CollDataMK M₀) (Un : Set (Object M₀)) :
    C.UnselOKF L γ η w κ Un ↔ (poolF C).UnselOK L γ η w κ Un :=
  ⟨fun h => ⟨h.dv⟩, fun h => ⟨h.dv⟩⟩

/-- `subpro` (4) alone (the only obligation read by main's loop transports of the pool). -/
def PoolContained (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : Prop :=
  ∀ P : Object M₀, P.HasGapKind L γ η w κ .SG → C.Outside P → Disjoint P.atoms C.hinges → C.Host L γ η w κ P

theorem mem_survAtomsM {E : Fin m → Object M₀} {v : V} : v ∈ survAtomsM E ↔ ∃ i, v ∈ (E i).atoms := by
  simp [survAtomsM]

theorem disjoint_survAtomsM {S : Finset V} {E : Fin m → Object M₀} :
    Disjoint S (survAtomsM E) ↔ ∀ i, Disjoint S (E i).atoms := by
  simp [survAtomsM, Finset.disjoint_biUnion_right]

theorem survJointsM_subset (E : Fin m → Object M₀) : survJointsM E ⊆ survAtomsM E := by
  intro v hv
  simp only [survJointsM, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton] at hv
  obtain ⟨i, rfl | rfl⟩ := hv
  · exact mem_survAtomsM.2 ⟨i, object_mem_of_joint (E i) (Or.inl rfl)⟩
  · exact mem_survAtomsM.2 ⟨i, object_mem_of_joint (E i) (Or.inr rfl)⟩

/-- A survivor-aware host (`HostE`) is a host of the forbidden pool. -/
theorem hostF_of_hostE {C : CollDataMK M₀} {E : Fin m → Object M₀} (hforb : C.forb = survAtomsM E) {P : Object M₀}
    (h : HostE C.toCollData E L γ η w κ P) : (poolF C).Host L γ η w κ P := by
  rcases h with ⟨S, a, b, hdv, hsub, hd1, hd2, hd3⟩ | ⟨Q, hsub, hk, hd1, hd2, hd3⟩
  · refine Or.inl ⟨S, a, b, hdv, hsub, ?_, hd2⟩
    show Disjoint S (C.hinges ∪ C.forb)
    rw [hforb, Finset.disjoint_union_right, disjoint_survAtomsM]
    exact ⟨(Finset.disjoint_union_right.1 hd1).1, hd3⟩
  · refine Or.inr ⟨Q, hsub, hk, ?_, hd2⟩
    show Disjoint Q.atoms (C.hinges ∪ C.forb)
    rw [hforb, Finset.disjoint_union_right, disjoint_survAtomsM]
    exact ⟨(Finset.disjoint_union_right.1 hd1).1, hd3⟩

/-- **The pool obligation of `(poolF C)`** from the survivor-aware obligations (R164 (a), C0's math check item 1). -/
theorem poolContained_toF {C : CollDataMK M₀} {E : Fin m → Object M₀} (hforb : C.forb = survAtomsM E)
    (hobl : SubproOblGMK C.toCollData E L γ η w κ) : PoolContained (poolF C) L γ η w κ := by
  intro P hP hout hdis
  have hdis' : Disjoint P.atoms (C.hinges ∪ C.forb) := hdis
  rw [hforb, Finset.disjoint_union_right] at hdis'
  have hE : ∀ i, Disjoint P.atoms (E i).atoms := disjoint_survAtomsM.1 hdis'.2
  refine hostF_of_hostE hforb (hobl.contained P hP hout (fun i hsub => ?_) ?_)
  · have hu := object_mem_of_joint P (Or.inl rfl)
    exact Finset.disjoint_left.1 (hE i) hu (hsub hu)
  · rw [Finset.disjoint_union_right]
    exact ⟨hdis'.1, Finset.disjoint_of_subset_right (survJointsM_subset E) hdis'.2⟩

end toF

section loop
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}
variable {R' : ℕ} {M : Molecule V D} {C : CollData M} {L γ η : ℝ} {w : Mom d} {κ : D → Fin d → ℤ}

theorem PoolContained.unloop (hC : LoopCtx L w κ R' M) (h : PoolContained C L γ η w κ) :
    PoolContained C.unloop L γ η w (fun y : NonLoop M => κ y.1) := by
  intro P hSG hOut hdis
  have hlf := hC.noLoop γ η P hSG
  have hSG' : (P.lift hlf).HasGapKind L γ η w κ .SG := (Object.lift_hasGapKind P hlf L γ η w κ _).2 hSG
  have hOut' : C.Outside (P.lift hlf) := fun i hi => hOut i hi
  rcases h (P.lift hlf) hSG' hOut' hdis with ⟨S, a, b, hdv, hsub, hd1, hd2⟩ | ⟨Q, hPQ, hQk, hQ1, hQ2⟩
  · exact Or.inl ⟨S, a, b, (unloopEmb M (isDV_loopFree hdv)).isDV_of rfl hdv, hsub, hd1, fun i => hd2 i⟩
  · refine Or.inr ⟨Q.unloop (Object.loopFree Q), hPQ, ?_, hQ1, fun i => hQ2 i⟩
    rcases hQk with h | h
    · exact Or.inl ((Object.unloop_hasGapKind Q _ L γ η w κ _).2 h)
    · exact Or.inr ((Object.unloop_hasGapKind Q _ L γ η w κ _).2 h)

theorem inP_unloopP (hC : LoopCtx L w κ R' M) (hP : PoolContained C L γ η w κ) {B : Object M}
    (h : C.InP L γ η w κ B) :
    C.unloop.InP L γ η w (fun y : NonLoop M => κ y.1) (B.unloop (Object.loopFree B)) := by
  obtain ⟨hSG, hOut, hdis, -⟩ := h
  have hSG' := (Object.unloop_hasGapKind B (Object.loopFree B) L γ η w κ _).2 hSG
  have hOut' : C.unloop.Outside (B.unloop (Object.loopFree B)) := hOut
  exact ⟨hSG', hOut', hdis, (hP.unloop hC) _ hSG' hOut' hdis⟩

theorem inP_liftP (hC : LoopCtx L w κ R' M) (hP : PoolContained C L γ η w κ) {P : Object M.unloop}
    (h : C.unloop.InP L γ η w (fun y : NonLoop M => κ y.1) P) :
    C.InP L γ η w κ (P.lift (hC.noLoop γ η P h.1)) := by
  obtain ⟨hSG, hOut, hdis, -⟩ := h
  have hlf := hC.noLoop γ η P hSG
  have hSG' : (P.lift hlf).HasGapKind L γ η w κ .SG := (Object.lift_hasGapKind P hlf L γ η w κ _).2 hSG
  have hOut' : C.Outside (P.lift hlf) := hOut
  exact ⟨hSG', hOut', hdis, hP _ hSG' hOut' hdis⟩

theorem c2Of_unloopP {Unsel : Set (Object M)} (hC : LoopCtx L w κ R' M) (hP : PoolContained C L γ η w κ)
    {U : Object M} (hUC : U ∈ C.C2Of L γ η w κ Unsel) :
    U.unloop (Object.loopFree U) ∈ C.unloop.C2Of L γ η w (fun y : NonLoop M => κ y.1) (unloopSet M Unsel) := by
  obtain ⟨⟨hUP, hUn⟩, hmax⟩ := hUC
  refine ⟨⟨inP_unloopP hC hP hUP, ?_⟩, ?_⟩
  · rintro ⟨U₂, hU₂, he⟩
    exact hUn (by rwa [Object.unloop_inj _ _ he])
  · rintro Q' ⟨hQP, hQn⟩ hsub
    have hlf := hC.noLoop γ η Q' hQP.1
    have hQ := inP_liftP hC hP hQP
    have hQn' : Q'.lift hlf ∉ Unsel := fun hq => hQn ⟨_, hq, (Object.unloop_lift Q' hlf _).symm⟩
    exact hmax _ ⟨hQ, hQn'⟩ hsub

theorem c2Of_liftP {Unsel : Set (Object M)} (hC : LoopCtx L w κ R' M) (hP : PoolContained C L γ η w κ)
    {U' : Object M.unloop}
    (hU : U' ∈ C.unloop.C2Of L γ η w (fun y : NonLoop M => κ y.1) (unloopSet M Unsel)) :
    ∃ hlf : LoopFreeSet M U'.atoms, U'.lift hlf ∈ C.C2Of L γ η w κ Unsel := by
  obtain ⟨⟨hP', hn⟩, hmax⟩ := hU
  have hlf := hC.noLoop γ η U' hP'.1
  refine ⟨hlf, ⟨⟨inP_liftP hC hP hP', ?_⟩, ?_⟩⟩
  · intro h; exact hn ⟨_, h, (Object.unloop_lift U' hlf _).symm⟩
  · rintro Q ⟨hQP, hQn⟩ hsub
    have hQ' := inP_unloopP hC hP hQP
    have hQn' : Q.unloop (Object.loopFree Q) ∉ unloopSet M Unsel := by
      rintro ⟨B, hB, he⟩
      exact hQn (by rw [Object.unloop_inj (Object.loopFree Q) (Object.loopFree B) he]; exact hB)
    exact hmax _ ⟨hQ', hQn'⟩ hsub

theorem collected_liftP {Unsel : Set (Object M)} (hC : LoopCtx L w κ R' M) (hP : PoolContained C L γ η w κ)
    {U' : Object M.unloop}
    (h : Collected C.unloop (unloopSet M Unsel) L γ η w (fun y : NonLoop M => κ y.1) U') :
    ∃ hlf : LoopFreeSet M U'.atoms, Coll2 C Unsel L γ η w κ (U'.lift hlf) := by
  rcases h with ⟨i, rfl⟩ | h
  · have hlf : LoopFreeSet M ((C.unloop.collection i).atoms) := Object.loopFree (C.collection i)
    exact ⟨hlf, Or.inl ⟨i, Object.lift_unloop (C.collection i) (Object.loopFree _) _⟩⟩
  · obtain ⟨hlf, h2⟩ := c2Of_liftP hC hP (CollData.C2Can_subset h)
    exact ⟨hlf, Or.inr h2⟩

theorem unselOK_unloopP {Unsel : Set (Object M)} (hC : LoopCtx L w κ R' M) (hP : PoolContained C L γ η w κ)
    (hU : C.UnselOK L γ η w κ Unsel) :
    C.unloop.UnselOK L γ η w (fun y : NonLoop M => κ y.1) (unloopSet M Unsel) where
  dv := by
    rintro B' ⟨B, hB, rfl⟩
    obtain ⟨hInP, hcase⟩ := hU.dv B hB
    refine ⟨inP_unloopP hC hP hInP, ?_⟩
    rcases hcase with ⟨U, hUC, hsub⟩ | ⟨A, a, b, hA, hBv, hAB, U, hUC, hUA, hUs⟩
    · obtain ⟨Q, hQ, hQat⟩ := CollData.exists_C2Can_of_C2Of C.unloop (c2Of_unloopP hC hP hUC.1)
      exact Or.inl ⟨Q, hQ, by rw [hQat]; exact hsub⟩
    · have hlfA : LoopFreeSet M A := fun y hy => isVine_noLoop hA y hy
      have hlfB : LoopFreeSet M B.atoms := Object.loopFree B
      refine Or.inr ⟨A, a, b, ((unloopEmb M hlfA).isVine_iff rfl).1 hA,
        ((unloopEmb M hlfB).isVine_iff rfl).1 hBv, hAB, U.unloop (Object.loopFree U), ?_, hUA,
        Object.unloop_shape_vc U _ hUs⟩
      exact CollData.mem_C2Can_of_vc (c2Of_unloopP hC hP hUC.1) (Object.unloop_shape_vc U _ hUs)

/-! ### The survivor-aware obligations on `M.unloop` -/

/-- The survivors on `M.unloop`. -/
noncomputable def unloopE {m : ℕ} (E : Fin m → Object M) : Fin m → Object M.unloop :=
  fun i => (E i).unloop (Object.loopFree _)

/-- The designated darts at a hinge are not loops. -/
theorem first_nonloop (hH : HingeNoLoop C) {v : V} (hv : v ∈ C.hinges)
    (hsg : HasChosenPair (C.first v) (C.second v) (fun x y =>
      TripleAtM M v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .SG)) :
    ∃ x y, C.first v = some x ∧ C.second v = some y ∧ M.atom x ≠ M.atom (M.mate x) ∧
      M.atom y ≠ M.atom (M.mate y) := by
  obtain ⟨x, y, hx, hy, hT, -⟩ := hsg
  refine ⟨x, y, hx, hy, ?_, ?_⟩
  · rw [hT.1]; exact (hH v hv x hT.1).symm
  · rw [hT.2.1]; exact (hH v hv y hT.2.1).symm

/-- The hinge alternative of `crossing`/`meetB` on `M.unloop`. -/
theorem hingeCase_unloop (hH : HingeNoLoop C)
    (hsg : ∀ v ∈ C.hinges, HasChosenPair (C.first v) (C.second v) (fun x y =>
      TripleAtM M v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .SG))
    {P : Object M.unloop} (hlf : LoopFreeSet M P.atoms) {v : V} (hvH : v ∈ C.hinges)
    (hcase : (v ≠ (P.lift hlf).upper ∧ v ≠ (P.lift hlf).lower) ∨ ((v = (P.lift hlf).upper ∨ v = (P.lift hlf).lower) ∧
      HasChosenPair (C.first v) (C.second v) (fun x y => Xor ((P.lift hlf).ContainsDart x)
        ((P.lift hlf).ContainsDart y)))) :
    (v ≠ P.upper ∧ v ≠ P.lower) ∨ ((v = P.upper ∨ v = P.lower) ∧
      HasChosenPair (C.unloop.first v) (C.unloop.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))) := by
  rcases hcase with ⟨h1, h2⟩ | ⟨hj, x, y, hx, hy, hxor⟩
  · exact Or.inl ⟨h1, h2⟩
  · right
    refine ⟨hj, ?_⟩
    obtain ⟨x₀, y₀, hx₀, hy₀, hnx, hny⟩ := first_nonloop hH hvH (hsg v hvH)
    have hxx : x₀ = x := Option.some.inj (hx₀.symm.trans hx)
    have hyy : y₀ = y := Option.some.inj (hy₀.symm.trans hy)
    subst hxx hyy
    refine ⟨⟨x₀, hnx⟩, ⟨y₀, hny⟩, by simp [CollData.unloop, hx, toNL_some hnx],
      by simp [CollData.unloop, hy, toNL_some hny], ?_⟩
    have e1 := Object.lift_containsDart P hlf ⟨x₀, hnx⟩
    have e2 := Object.lift_containsDart P hlf ⟨y₀, hny⟩
    rw [e1, e2] at hxor
    exact hxor

/-- **`SubproOblGMK` on `M.unloop`** (GL26's `SubproOblG.unloop` with the survivor fields). -/
theorem SubproOblGMK.unloop {m : ℕ} {E : Fin m → Object M} (hC : LoopCtx L w κ R' M) (hH : HingeNoLoop C)
    (obl : SubproOblGMK C E L γ η w κ) :
    SubproOblGMK C.unloop (unloopE E) L γ η w (fun y : NonLoop M => κ y.1) where
  survSG i := (Object.unloop_hasGapKind (E i) _ L γ η w κ _).2 (obl.survSG i)
  contained := by
    intro P hSG hOut hnot hdis
    have hlf := hC.noLoop γ η P hSG
    have hSG' : (P.lift hlf).HasGapKind L γ η w κ .SG := (Object.lift_hasGapKind P hlf L γ η w κ _).2 hSG
    have hOut' : C.Outside (P.lift hlf) := fun i hi => hOut i hi
    rcases obl.contained (P.lift hlf) hSG' hOut' hnot hdis with ⟨S, a, b, hdv, hsub, hd1, hd2, hd3⟩ |
      ⟨Q, hPQ, hQk, hQ1, hQ2, hQ3⟩
    · exact Or.inl ⟨S, a, b, (unloopEmb M (isDV_loopFree hdv)).isDV_of rfl hdv, hsub, hd1, fun i => hd2 i,
        fun i => hd3 i⟩
    · refine Or.inr ⟨Q.unloop (Object.loopFree Q), hPQ, ?_, hQ1, fun i => hQ2 i, fun i => hQ3 i⟩
      rcases hQk with h | h
      · exact Or.inl ((Object.unloop_hasGapKind Q _ L γ η w κ _).2 h)
      · exact Or.inr ((Object.unloop_hasGapKind Q _ L γ η w κ _).2 h)
  hingeSG := by
    intro v hv
    obtain ⟨x, y, hx, hy, hT, hsg⟩ := obl.hingeSG v hv
    have hnx : M.atom x ≠ M.atom (M.mate x) := by rw [hT.1]; exact (hH v hv x hT.1).symm
    have hny : M.atom y ≠ M.atom (M.mate y) := by rw [hT.2.1]; exact (hH v hv y hT.2.1).symm
    exact ⟨⟨x, hnx⟩, ⟨y, hny⟩, by simp [CollData.unloop, hx, toNL_some hnx],
      by simp [CollData.unloop, hy, toNL_some hny], tripleAtM_unloop hnx hny hT, hsg⟩
  hingeJoint := by
    intro v hv i hvi
    obtain ⟨x, y, hx, hy, hxc, hyc⟩ := obl.hingeJoint v hv i hvi
    obtain ⟨x₀, y₀, hx₀, hy₀, hnx, hny⟩ := first_nonloop hH hv (obl.hingeSG v hv)
    have hxx : x₀ = x := Option.some.inj (hx₀.symm.trans hx)
    have hyy : y₀ = y := Option.some.inj (hy₀.symm.trans hy)
    subst hxx hyy
    refine ⟨⟨x₀, hnx⟩, ⟨y₀, hny⟩, by simp [CollData.unloop, hx, toNL_some hnx],
      by simp [CollData.unloop, hy, toNL_some hny], ?_, ?_⟩
    · exact (Object.unloop_containsDart (C.collection i) _ ⟨x₀, hnx⟩).2 hxc
    · exact (Object.unloop_containsDart (C.collection i) _ ⟨y₀, hny⟩).2 hyc
  jointPair := by
    intro i v hv
    obtain ⟨x, y, hx, hy, hxc, hyc⟩ := obl.jointPair i v hv
    have hnx : M.atom x ≠ M.atom (M.mate x) := Object.loopFree (E i) x (containsDart_inGroup' (E i) hxc).1
    have hny : M.atom y ≠ M.atom (M.mate y) := Object.loopFree (E i) y (containsDart_inGroup' (E i) hyc).1
    exact ⟨⟨x, hnx⟩, ⟨y, hny⟩, by simp [CollData.unloop, hx, toNL_some hnx],
      by simp [CollData.unloop, hy, toNL_some hny], (Object.unloop_containsDart (E i) _ ⟨x, hnx⟩).2 hxc,
      (Object.unloop_containsDart (E i) _ ⟨y, hny⟩).2 hyc⟩
  crossing := by
    intro P hSG hOut hnot hdisJ hnd
    have hlf := hC.noLoop γ η P hSG
    have hSG' : (P.lift hlf).HasGapKind L γ η w κ .SG := (Object.lift_hasGapKind P hlf L γ η w κ _).2 hSG
    have hOut' : C.Outside (P.lift hlf) := fun i hi => hOut i hi
    obtain ⟨v, hvH, hvP, hcase⟩ := obl.crossing (P.lift hlf) hSG' hOut' hnot hdisJ hnd
    exact ⟨v, hvH, hvP, hingeCase_unloop hH obl.hingeSG hlf hvH hcase⟩
  meetB := by
    intro P hSG hmeet
    have hlf := hC.noLoop γ η P hSG
    have hSG' : (P.lift hlf).HasGapKind L γ η w κ .SG := (Object.lift_hasGapKind P hlf L γ η w κ _).2 hSG
    rcases obl.meetB (P.lift hlf) hSG' hmeet with ⟨i, hi⟩ | ⟨i, x, hPx, hEx⟩ | ⟨v, hvH, hvP, hcase⟩
    · exact Or.inl ⟨i, hi⟩
    · have hnx : M.atom x ≠ M.atom (M.mate x) := Object.loopFree (E i) x (containsDart_inGroup' (E i) hEx).1
      exact Or.inr (Or.inl ⟨i, ⟨x, hnx⟩, (Object.lift_containsDart P hlf ⟨x, hnx⟩).1 hPx,
        (Object.unloop_containsDart (E i) _ ⟨x, hnx⟩).2 hEx⟩)
    · exact Or.inr (Or.inr ⟨v, hvH, hvP, hingeCase_unloop hH obl.hingeSG hlf hvH hcase⟩)

/-- The MK collection data on `M.unloop` (the forbidden atoms unchanged). -/
noncomputable def unloopMK (C : CollDataMK M) : CollDataMK M.unloop :=
  { C.toCollData.unloop with forb := C.forb }

end loop

end WaveTurbulence.Flower.FinalMKGarden
