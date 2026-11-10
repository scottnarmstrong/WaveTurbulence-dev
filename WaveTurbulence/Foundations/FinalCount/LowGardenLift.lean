/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowIface
public import WaveTurbulence.Foundations.FinalCount.LowGardenHost
public import WaveTurbulence.Foundations.FinalCount.AsmGHost2
public import WaveTurbulence.Foundations.FinalCount.AsmDesig
/-! **FINALCOUNT-ASSEMBLY (LOW-GARDEN, session 2): lifting data from `M.unloop` back to `M`.**

Converse transports of GL26/GL27: a member of `C₂` of `M.unloop` lifts to a member of `C₂` of `M`; the collected objects of
`M.unloop` lift to `C₁ ∪ C₂` of `M`; hinge data, vine shapes and double chains transfer; `remMol` has the same number of components. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

section lift
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}
variable {R' : ℕ} {M : Molecule V D} {C : CollData M} {L γ η : ℝ} {w : Mom d} {κ : D → Fin d → ℤ}

/-- A member of `C₂` of `M.unloop` lifts to a member of `C₂` of `M`. -/
theorem C2Of_lift {Unsel : Set (Object M)} (hC : LoopCtx L w κ R' M) (hH : HingeNoLoop C)
    (obl : SubproOblG C L γ η w κ) {U' : Object M.unloop}
    (hU : U' ∈ C.unloop.C2Of L γ η w (fun y : NonLoop M => κ y.1) (unloopSet M Unsel)) :
    ∃ hlf : LoopFreeSet M U'.atoms, U'.lift hlf ∈ C.C2Of L γ η w κ Unsel := by
  obtain ⟨⟨hP, hn⟩, hmax⟩ := hU
  have hlf := hC.noLoop γ η U' hP.1
  refine ⟨hlf, ⟨⟨InP_lift hC obl hP, ?_⟩, ?_⟩⟩
  · intro h; exact hn ⟨_, h, (Object.unloop_lift U' hlf _).symm⟩
  · rintro Q ⟨hQP, hQn⟩ hsub
    have hQ' := InP_unloop hC hH obl hQP
    have hQn' : Q.unloop (Object.loopFree Q) ∉ unloopSet M Unsel := by
      rintro ⟨B, hB, he⟩
      exact hQn (by rw [Object.unloop_inj (Object.loopFree Q) (Object.loopFree B) he]; exact hB)
    exact hmax _ ⟨hQ', hQn'⟩ hsub

/-- The collected objects of `M` before the choice of canonical designations: `C₁ ∪ C₂`. -/
def Coll2 (C : CollData M) (Un : Set (Object M)) (L γ η : ℝ) (w : Mom d) (κ : D → Fin d → ℤ) (U : Object M) : Prop :=
  (∃ i, U = C.collection i) ∨ U ∈ C.C2Of L γ η w κ Un

theorem collected_lift {Unsel : Set (Object M)} (hC : LoopCtx L w κ R' M) (hH : HingeNoLoop C)
    (obl : SubproOblG C L γ η w κ) {U' : Object M.unloop}
    (h : Collected C.unloop (unloopSet M Unsel) L γ η w (fun y : NonLoop M => κ y.1) U') :
    ∃ hlf : LoopFreeSet M U'.atoms, Coll2 C Unsel L γ η w κ (U'.lift hlf) := by
  rcases h with ⟨i, rfl⟩ | h
  · have hlf : LoopFreeSet M ((C.unloop.collection i).atoms) := Object.loopFree (C.collection i)
    refine ⟨hlf, Or.inl ⟨i, ?_⟩⟩
    exact Object.lift_unloop (C.collection i) (Object.loopFree _) _
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

theorem objVine_unloop (U : Object M) (hlf : LoopFreeSet M U.atoms) (h : ObjVine M U) :
    ObjVine M.unloop (U.unloop hlf) := by
  obtain ⟨S, a, b, sh⟩ := U
  cases sh with
  | vc hv =>
    obtain ⟨X, hX⟩ := h
    exact ⟨X, ((unloopEmb M hlf).isVine_iff rfl).1 hX⟩
  | hyper R =>
    obtain ⟨X, hX⟩ := h
    exact ⟨X, ((eraseUnloopEmb M ⟨R.added, hyper_added_nonloop R⟩ hlf).isVine_iff rfl).1 hX⟩

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

theorem hingeData_unloop {M : Molecule V D} {C : CollData M} (hH : HingeNoLoop C) {U' : Object M.unloop}
    (hlf : LoopFreeSet M U'.atoms) (h : HingeData C (U'.lift hlf)) : HingeData C.unloop U' := by
  intro v hv hvj
  obtain ⟨f, s, hf, hs, hcf, hcs, haf, has, hout⟩ := h v hv hvj
  have hnf : M.atom f ≠ M.atom (M.mate f) := by rw [haf]; exact (hH v hv f haf).symm
  have hns : M.atom s ≠ M.atom (M.mate s) := by rw [has]; exact (hH v hv s has).symm
  exact ⟨⟨f, hnf⟩, ⟨s, hns⟩, by simp [CollData.unloop, hf, toNL_some hnf], by simp [CollData.unloop, hs, toNL_some hns],
    (Object.lift_containsDart U' hlf ⟨f, hnf⟩).1 hcf, (Object.lift_containsDart U' hlf ⟨s, hns⟩).1 hcs, haf, has, hout⟩

end hinge

section remcomp
variable {V : Type*} [DecidableEq V]

/-- Components of two molecules on the same atoms whose adjacency relations agree off the diagonal. -/
theorem numComponents_le_of_adj {E F : Type*} [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (N1 : Molecule V E) (N2 : Molecule V F) (hat : ∀ v, v ∈ N1.atoms ↔ v ∈ N2.atoms)
    (hadj : ∀ a b, N2.Adj a b → a = b ∨ N1.Adj a b) : N1.numComponents ≤ N2.numComponents := by
  unfold Molecule.numComponents
  let f : Quot (fun u v : N2.atoms => N2.Adj u.1 v.1) → Quot (fun u v : N1.atoms => N1.Adj u.1 v.1) :=
    Quot.lift (fun u : N2.atoms => Quot.mk _ (⟨u.1, (hat u.1).2 u.2⟩ : N1.atoms))
      (fun a b hab => by
        rcases hadj _ _ hab with h | h
        · have : (⟨a.1, (hat a.1).2 a.2⟩ : N1.atoms) = ⟨b.1, (hat b.1).2 b.2⟩ := Subtype.ext h
          rw [this]
        · exact Quot.sound h)
  have hf : Function.Surjective f := by
    intro q
    induction q using Quot.ind with
    | _ u => exact ⟨Quot.mk _ (⟨u.1, (hat u.1).1 u.2⟩ : N2.atoms), rfl⟩
  exact Nat.card_le_card_of_surjective f hf

end remcomp

section cn
variable {V : Type*} [DecidableEq V] {D : Type} [Fintype D] [DecidableEq D] {d : ℕ} {M : Molecule V D}

theorem remMol_numComponents_le (ps : List (Object M × Quad D)) (ps' : List (Object M.unloop × Quad (NonLoop M)))
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
noncomputable def liftP (U0 : Object M) (p : Object M.unloop × Quad (NonLoop M)) : Object M × Quad D :=
  ((if h : LoopFreeSet M p.1.atoms then p.1.lift h else U0), (p.2.1.1, p.2.2.1.1, p.2.2.2.1.1, p.2.2.2.2.1))

theorem liftP_fst (U0 : Object M) (p : Object M.unloop × Quad (NonLoop M)) (hlf : LoopFreeSet M p.1.atoms) :
    (liftP U0 p).1 = p.1.lift hlf := by
  simp [liftP, hlf]

theorem pieceKill_liftP (U0 : Object M) (p : Object M.unloop × Quad (NonLoop M)) (hlf : LoopFreeSet M p.1.atoms)
    (z : NonLoop M) :
    z.1 ∈ PieceKill (liftP U0 p).1 (liftP U0 p).2 ↔ z ∈ PieceKill p.1 p.2 := by
  rw [liftP_fst U0 p hlf]
  simp only [PieceKill, Set.mem_ofPred_eq, liftP, Object.lift, Subtype.ext_iff]
  rfl

theorem lift_eq_of_unloop {P' : Object M.unloop} (h : LoopFreeSet M P'.atoms) {U : Object M} (hU : LoopFreeSet M U.atoms)
    (he : P' = U.unloop hU) : P'.lift h = U := by
  subst he; exact Object.lift_unloop U hU h

end cn

end WaveTurbulence.FinalCountAsm
