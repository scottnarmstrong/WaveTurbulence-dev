/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGardenLift
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowIface
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowIface2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenHost
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGHost2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmDesig
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowGardenLift`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (LOW-GARDEN, session 2): lifting data from `M.unloop` back to `M`.**

Converse transports of GL26/GL27: a member of `C₂` of `M.unloop` lifts to a member of `C₂` of `M`; the collected objects of
`M.unloop` lift to `C₁ ∪ C₂` of `M`; hinge data, vine shapes and double chains transfer; `remMol` has the same number of components. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

section lift
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}
variable {R' : ℕ} {M : Molecule V D} {C : CollData M} {L γ η : ℝ} {w : Mom d} {κ : D → Fin d → ℤ}

/-- A member of `C₂` of `M.unloop` lifts to a member of `C₂` of `M`. -/
theorem C2Of_lift {Unsel : Set (Src.Object Src.γL M)} (hC : LoopCtx L w κ R' M) (hH : HingeNoLoop C)
    (obl : SubproOblG C L γ η w κ) {U' : Src.Object Src.γL M.unloop}
    (hU : U' ∈ C.unloop.C2Of L γ η w (fun y : NonLoop M => κ y.1) (unloopSet M Unsel)) :
    ∃ hlf : LoopFreeSet M U'.atoms, U'.lift hlf ∈ C.C2Of L γ η w κ Unsel := by
  obtain ⟨⟨hP, hn⟩, hmax⟩ := hU
  have hlf := hC.noLoop γ η U' hP.1
  refine ⟨hlf, ⟨⟨InP_lift hC obl hP, ?_⟩, ?_⟩⟩
  · intro h; exact hn ⟨_, h, (Src.Object.unloop_lift U' hlf _).symm⟩
  · rintro Q ⟨hQP, hQn⟩ hsub
    have hQ' := InP_unloop hC hH obl hQP
    have hQn' : Q.unloop (Src.Object.loopFree Q) ∉ unloopSet M Unsel := by
      rintro ⟨B, hB, he⟩
      exact hQn (by rw [Src.Object.unloop_inj (Src.Object.loopFree Q) (Src.Object.loopFree B) he]; exact hB)
    exact hmax _ ⟨hQ', hQn'⟩ hsub

/-- The collected objects of `M` before the choice of canonical designations: `C₁ ∪ C₂`. -/
def Coll2 (C : CollData M) (Un : Set (Src.Object Src.γL M)) (L γ η : ℝ) (w : Mom d) (κ : D → Fin d → ℤ) (U : Src.Object Src.γL M) : Prop :=
  (∃ i, U = C.collection i) ∨ U ∈ C.C2Of L γ η w κ Un

theorem collected_lift {Unsel : Set (Src.Object Src.γL M)} (hC : LoopCtx L w κ R' M) (hH : HingeNoLoop C)
    (obl : SubproOblG C L γ η w κ) {U' : Src.Object Src.γL M.unloop}
    (h : Collected C.unloop (unloopSet M Unsel) L γ η w (fun y : NonLoop M => κ y.1) U') :
    ∃ hlf : LoopFreeSet M U'.atoms, Coll2 C Unsel L γ η w κ (U'.lift hlf) := by
  rcases h with ⟨i, rfl⟩ | h
  · have hlf : LoopFreeSet M ((C.unloop.collection i).atoms) := Src.Object.loopFree (C.collection i)
    refine ⟨hlf, Or.inl ⟨i, ?_⟩⟩
    exact Src.Object.lift_unloop (C.collection i) (Src.Object.loopFree _) _
  · obtain ⟨hlf, h2⟩ := C2Of_lift hC hH obl (CollData.C2Can_subset h)
    exact ⟨hlf, Or.inr h2⟩

theorem deg_unloop_eq (M : Molecule V D) {a : V} (h : ∀ z, M.atom z = a → M.atom (M.mate z) ≠ a) :
    M.unloop.deg a = M.deg a := by
  refine le_antisymm (unloop_deg_le M a) ?_
  unfold Molecule.deg
  refine Finset.card_le_card_of_surjOn (Subtype.val : NonLoop M → D) ?_
  intro x hx
  have hx' : M.atom x = a := (mem_dartsAt' M a x).1 hx
  have hnl : M.atom x ≠ M.atom (M.mate x) := by rw [hx']; exact (h x hx').symm
  exact ⟨⟨x, hnl⟩, (mem_dartsAt' M.unloop a _).2 hx', rfl⟩

theorem sgat_unloop {a : V} (hC : LoopCtx L w κ R' M) (h : SGat M L γ η w κ a) :
    SGat M.unloop L γ η w (fun y : NonLoop M => κ y.1) a := by
  obtain ⟨x₀, y₀, h1, h2, h3, h4, h5, h6⟩ := h
  have hnx : M.atom x₀ ≠ M.atom (M.mate x₀) := by
    intro hl
    have := hC.heq x₀ hl y₀ (h2.trans h1.symm)
    unfold Molecule.gapAt Molecule.kvec at h6
    rw [this] at h6; simp [gapKind_zero] at h6
  have hny : M.atom y₀ ≠ M.atom (M.mate y₀) := by
    intro hl
    have := hC.heq y₀ hl x₀ (h1.trans h2.symm)
    unfold Molecule.gapAt Molecule.kvec at h6
    rw [this] at h6; simp [gapKind_zero] at h6
  exact ⟨⟨x₀, hnx⟩, ⟨y₀, hny⟩, h1, h2, h3, h4, fun e => h5 (congrArg Subtype.val e), h6⟩

theorem objVine_unloop (U : Src.Object Src.γL M) (hlf : LoopFreeSet M U.atoms) (h : ObjVine M U) :
    ObjVine M.unloop (U.unloop hlf) := by
  obtain ⟨S, a, b, sh⟩ := U
  cases sh with
  | vc hv =>
    have hX : M.IsVineEnl S a b := h
    exact Src.isSomeVine_γL_iff.mp (((unloopEmb M hlf).isVine_iffS rfl).1 (Src.isSomeVine_γL_iff.mpr hX))
  | hyper R =>
    have hX : (M.eraseBond R.added).IsVineEnl S a b := h
    exact Src.isSomeVine_γL_iff.mp
      (((eraseUnloopEmb M ⟨R.added, hyper_added_nonloop R⟩ hlf).isVine_iffS rfl).1 (Src.isSomeVine_γL_iff.mpr hX))

theorem doubleChain_unloop {S : Finset V} {a b : V} {n : ℕ} (h : Vine.DoubleChain M S a b n) :
    LoopFreeSet M S → Vine.DoubleChain M.unloop S a b n := by
  induction h with
  | single hv => exact fun hlf => Vine.DoubleChain.single (((unloopEmb M hlf).isVine_iff rfl).1 hv)
  | append hS hv hint hne ih =>
    rename_i S₁ T₁ a₁ b₁ c₁ n₁
    intro hlf
    exact Vine.DoubleChain.append (ih (hlf.mono Finset.subset_union_left))
      (((unloopEmb M (hlf.mono Finset.subset_union_right)).isVine_iff rfl).1 hv) hint hne

end lift

section hinge
variable {V : Type*} [DecidableEq V] [Infinite V] {D : Type} [Fintype D] [DecidableEq D] {d : ℕ}

theorem hingeData_unloop {M : Molecule V D} {C : CollData M} (hH : HingeNoLoop C) {U' : Src.Object Src.γL M.unloop}
    (hlf : LoopFreeSet M U'.atoms) (h : HingeData C (U'.lift hlf)) : HingeData C.unloop U' := by
  intro v hv hvj
  obtain ⟨f, s, hf, hs, hcf, hcs, haf, has, hout⟩ := h v hv hvj
  have hnf : M.atom f ≠ M.atom (M.mate f) := by rw [haf]; exact (hH v hv f haf).symm
  have hns : M.atom s ≠ M.atom (M.mate s) := by rw [has]; exact (hH v hv s has).symm
  exact ⟨⟨f, hnf⟩, ⟨s, hns⟩, by simp [CollData.unloop, hf, toNL_some hnf], by simp [CollData.unloop, hs, toNL_some hns],
    (Src.Object.lift_containsDart U' hlf ⟨f, hnf⟩).1 hcf, (Src.Object.lift_containsDart U' hlf ⟨s, hns⟩).1 hcs, haf, has, hout⟩

end hinge

section remcomp
variable {V : Type*} [DecidableEq V]

end remcomp

section cn
variable {V : Type*} [DecidableEq V] {D : Type} [Fintype D] [DecidableEq D] {d : ℕ} {M : Molecule V D}

theorem remMol_numComponents_le (ps : List (Src.Object Src.γL M × Quad D)) (ps' : List (Src.Object Src.γL M.unloop × Quad (NonLoop M)))
    (hrel : ∀ v, (∀ p ∈ ps, ¬ PieceInt p.1 v) ↔ (∀ p ∈ ps', ¬ PieceInt p.1 v))
    (hkill : ∀ z : NonLoop M, z.1 ∈ KillS ps ↔ z ∈ KillS ps') :
    (remMol M.unloop ps').numComponents ≤ (remMol M ps).numComponents := by
  refine numComponents_le_of_adj _ _ (fun v => ?_) (fun a b hab => ?_)
  · simp only [remMol, Finset.mem_filter, unloop_atoms]
    exact and_congr_right fun _ => (hrel v).symm
  · obtain ⟨z, hza, hzb⟩ := hab
    by_cases e : a = b
    · exact Or.inl e
    · right
      have hnl : M.atom z.1 ≠ M.atom (M.mate z.1) := by
        show M.atom z.1 ≠ M.atom (M.mate z.1)
        have h1 : M.atom z.1 = a := hza
        have h2 : M.atom (M.mate z.1) = b := hzb
        rw [h1, h2]; exact e
      refine ⟨⟨⟨z.1, hnl⟩, fun h => z.2.1 ((hkill _).2 h), fun h => z.2.2 ((hkill ⟨M.mate z.1, _⟩).2 h)⟩, hza, hzb⟩

/-- Lift a piece of `M.unloop` to `M` (a default object is used off the loop-free pieces). -/
noncomputable def liftP (U0 : Src.Object Src.γL M) (p : Src.Object Src.γL M.unloop × Quad (NonLoop M)) : Src.Object Src.γL M × Quad D :=
  ((if h : LoopFreeSet M p.1.atoms then p.1.lift h else U0), (p.2.1.1, p.2.2.1.1, p.2.2.2.1.1, p.2.2.2.2.1))

theorem liftP_fst (U0 : Src.Object Src.γL M) (p : Src.Object Src.γL M.unloop × Quad (NonLoop M)) (hlf : LoopFreeSet M p.1.atoms) :
    (liftP U0 p).1 = p.1.lift hlf := by
  simp [liftP, hlf]

theorem pieceKill_liftP (U0 : Src.Object Src.γL M) (p : Src.Object Src.γL M.unloop × Quad (NonLoop M)) (hlf : LoopFreeSet M p.1.atoms)
    (z : NonLoop M) :
    z.1 ∈ PieceKill (liftP U0 p).1 (liftP U0 p).2 ↔ z ∈ PieceKill p.1 p.2 := by
  rw [liftP_fst U0 p hlf]
  simp only [PieceKill, Set.mem_ofPred_eq, liftP, Src.Object.lift, Subtype.ext_iff]
  rfl

theorem lift_eq_of_unloop {P' : Src.Object Src.γL M.unloop} (h : LoopFreeSet M P'.atoms) {U : Src.Object Src.γL M} (hU : LoopFreeSet M U.atoms)
    (he : P' = U.unloop hU) : P'.lift h = U := by
  subst he; exact Src.Object.lift_unloop U hU h

/-- **`CnBound` on `M.unloop`** (a molecule with at least one loop: the index `R + k` exceeds `R`, so the equality case is vacuous). -/
theorem cnBound_unloop {Un : (D → Fin d → ℤ) → Set (Src.Object Src.γL M)} {Fst : Set (Src.Object Src.γL M)}
    {Un' : (NonLoop M → Fin d → ℤ) → Set (Src.Object Src.γL M.unloop)} {Adm : (D → Fin d → ℤ) → Prop} {L γ η : ℝ}
    {A0' : Set (NonLoop M → Fin d → ℤ)} {C : CollData M} {R : ℕ}
    (hk : 0 < M.loopBonds.card) (hFst : ∀ U ∈ Fst, ∃ i, U = C.collection i)
    (hA0' : ∀ κ' ∈ A0', unloopAdm M Adm κ')
    (hcn : CnBound M C Un Fst L γ η (0 : Mom d) {κ | Adm κ} R) :
    CnBound M.unloop C.unloop Un' (unloopSet M Fst) L γ η (0 : Mom d) A0' (R + M.loopBonds.card) := by
  intro κ' hκ' ps' hps' hpw'
  obtain ⟨κ, hκ, rfl⟩ := hA0' κ' hκ'
  have hex : ∀ p ∈ ps', ∃ U ∈ Fst, ∃ hU : LoopFreeSet M U.atoms, p.1 = U.unloop hU := fun p hp => by
    obtain ⟨U, hU, he⟩ := (hps' p hp).2
    exact ⟨U, hU, Src.Object.loopFree U, he⟩
  have hlfp : ∀ p ∈ ps', LoopFreeSet M p.1.atoms := fun p hp => by
    obtain ⟨U, -, hU, he⟩ := hex p hp
    rw [he]; exact hU
  have hne : Nonempty (Src.Object Src.γL M) ∨ ps' = [] := by
    cases ps' with
    | nil => exact Or.inr rfl
    | cons p ps => exact Or.inl ⟨p.1.lift (hlfp p (by simp))⟩
  have hnc : (remMol M.unloop ps').numComponents ≤ 2 * R := by
    rcases hne with hU0 | rfl
    · let U0 : Src.Object Src.γL M := Classical.choice hU0
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
      refine (remMol_numComponents_le ps ps' hrel hkill).trans ?_
      refine (hcn κ hκ ps (fun q hq => ?_) ?_).1
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
        obtain ⟨U, hU, hUl, he⟩ := hex p hp
        have hlf := hlfp p hp
        have h1 : (liftP U0 p).1 = U := by rw [liftP_fst U0 p hlf]; exact lift_eq_of_unloop hlf hUl he
        obtain ⟨-, hc4, hj, hdist⟩ := (hps' p hp).1
        refine ⟨⟨Or.inl (by rw [h1]; exact hFst U hU), ?_, ?_, ?_⟩, by rw [h1]; exact hU⟩
        · rw [liftP_fst U0 p hlf]
          exact ⟨(Src.Object.lift_containsDart p.1 hlf p.2.1).2 hc4.1, (Src.Object.lift_containsDart p.1 hlf p.2.2.1).2 hc4.2.1,
            (Src.Object.lift_containsDart p.1 hlf p.2.2.2.1).2 hc4.2.2.1, (Src.Object.lift_containsDart p.1 hlf p.2.2.2.2).2 hc4.2.2.2⟩
        · rw [liftP_fst U0 p hlf]
          rcases hj with ⟨a, b⟩ | ⟨a, b⟩
          · exact Or.inl ⟨a, b⟩
          · exact Or.inr ⟨a, b⟩
        · exact ⟨hdist.1, hdist.2.1, fun e => hdist.2.2.1 (Subtype.ext e), fun e => hdist.2.2.2 (Subtype.ext e)⟩
      · exact List.pairwise_map.2 (hpw'.imp_of_mem fun {a b} ha hb h => by rw [hat a ha, hat b hb]; exact h)
    · refine (remMol_numComponents_le ([] : List (Src.Object Src.γL M × Quad D)) [] (by simp) (by simp [KillS])).trans ?_
      exact (hcn κ hκ [] (by simp) List.Pairwise.nil).1
  refine ⟨by omega, fun h => by omega⟩

end cn

end WaveTurbulence.GammaLow.FinalCount.H
