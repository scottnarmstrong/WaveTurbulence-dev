/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecStep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecKind
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadGeom
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClauseA
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcGeoI
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcGeoII
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.BadCount
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecClause
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecStep
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecClause` (sha256 a23c9b4fc28b4d50…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 17, step 2): the geometry of the slots of a record (clause (a) for kind 0)

`kd0_ordPairs`: for a kind-0 summand (`recKind c = 0`) whose slots are `t₀`, and `{s₁, t₁}` in either order, the order pairs contain the two pairs of
clause (a) in one of its two forms.  `rec_slots_typeII`: for a record at a core vine with `qb ≠ qr` (so the vine is of type II, `typeI_qb_qr`), the
slots of `recSlots` are the clock atoms `t₀ = .inl ⟨i,0⟩`, and `s₁ = .inr (.inl ⟨i,⟨0,h⟩⟩)`, `t₁ = .inl ⟨i,1⟩` in either order, with `0 < m i` (`rung0_piece`).
`rec_clause_a`: hence a kind-0 record at such a block gives the clause-(a) pairs inside `ordPairs`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
open WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W13

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

open VineParamContract in
/-- The slot of a branch that is the clock atom `c`. -/
theorem brSlot_of_atomΓ (hM9 : NormalChartSupply γF) (c : (assemblyShapeΓ hM9 B).TVar) (v : GBranch G.tree)
    (hv : (assemblyClockAtomEquivΓ hM9 B c).1 = v) : brSlotΓ hM9 B v = Sum.inl c := by
  classical
  subst hv
  have hmem : (assemblyClockAtomEquivΓ hM9 B c).1 ∈ clInteriorBranches R := (assemblyClockAtomEquivΓ hM9 B c).2
  unfold brSlotΓ
  rw [dif_pos hmem, branchSlot_eqΓ]
  congr 1
  exact (assemblyClockAtomEquivΓ hM9 B).symm_apply_apply c

open VineParamContract in
theorem rec_slots_typeIIΓ (hM9 : NormalChartSupply γF) (lv : LvlΓ B) (pstar : lv.ι) (ν : ℤˣ)
    (hne : qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) ≠
      qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) :
    ∃ h : 0 < (assemblyShapeΓ hM9 B).m (lv.e pstar).1,
      recSlotsΓ hM9 B (assemblyPieceAtΓ B (lv.e pstar).1).lower
          (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) ν 0 =
        Sum.inl (.inl ⟨(lv.e pstar).1, 0⟩) ∧
      ((recSlotsΓ hM9 B (assemblyPieceAtΓ B (lv.e pstar).1).lower
          (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) ν 1 =
          Sum.inl (.inr (.inl ⟨(lv.e pstar).1, ⟨0, h⟩⟩)) ∧
        recSlotsΓ hM9 B (assemblyPieceAtΓ B (lv.e pstar).1).lower
          (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) ν 2 =
          Sum.inl (.inl ⟨(lv.e pstar).1, ⟨1, by omega⟩⟩)) ∨
       (recSlotsΓ hM9 B (assemblyPieceAtΓ B (lv.e pstar).1).lower
          (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) ν 1 =
          Sum.inl (.inl ⟨(lv.e pstar).1, ⟨1, by omega⟩⟩) ∧
        recSlotsΓ hM9 B (assemblyPieceAtΓ B (lv.e pstar).1).lower
          (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) ν 2 =
          Sum.inl (.inr (.inl ⟨(lv.e pstar).1, ⟨0, h⟩⟩)))) := by
  classical
  set i : Fin n := (lv.e pstar).1 with hi
  set F := (lv.state B RD hG layer hLayer).family with hF
  have hbad := core_kind_badΓ B (lv.e pstar)
  have hkind : F.kind pstar = (assemblySourceFamilyΓ B).kind (lv.e pstar).1 := rfl
  have hII : (assemblyPieceAtΓ B i).label = .II := by
    have hnI : F.kind pstar ≠ VineType.I := fun h => hne (by
      have := typeI_qb_qr F pstar h
      exact this.1.trans this.2.symm)
    have hk2 : (assemblySourceFamilyΓ B).kind i = (assemblyPieceAtΓ B i).label := rfl
    rw [← hk2]
    rw [← hkind] at hbad ⊢
    generalize F.kind pstar = κ at hbad hnI
    cases κ <;> simp [VineType.IsBad] at hbad hnI ⊢
  obtain ⟨R0, hn, hp, h0, hrung⟩ := rung0_pieceΓ hM9 (assemblyPieceAtΓ B i) hII (assemblyPiece_clΓ B i)
  have hlow : (F.placement pstar).lower = (assemblyPieceAtΓ B i).lower := start_lowerΓ B RD hG layer hLayer (lv.e pstar)
  have key : ∀ (l1 l2 : GBranch G.tree) (h : l1 = l2)
      (R0 : Molecpl.EndRungData G.molecule (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).upper l2) (hn : l2.1.2 ≠ []),
      l2.toNode.parent hn = R0.left →
      ∃ (R1 : Molecpl.EndRungData G.molecule (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).upper l1) (hn1 : l1.1.2 ≠ []),
        l1.toNode.parent hn1 = R1.left ∧ R1.left = R0.left ∧ R1.right = R0.right := by
    intro l1 l2 h; subst h; intro R0 hn hp; exact ⟨R0, hn, hp, rfl, rfl⟩
  obtain ⟨R1, hn1, hp1, hl1, hr1⟩ := key _ _ hlow R0 hn hp
  have hqq : qbOf (F.placement pstar) = R1.left ∧ qrOf (F.placement pstar) = R1.right :=
    typeII_qb_qr F pstar (by rw [hkind]; exact hII) R1 hn1 hp1
  rw [hl1, hr1] at hqq
  refine ⟨h0, ?_⟩
  have hx := clockAtom_xΓ hM9 B i ⟨0, h0⟩
  have hy := clockAtom_yΓ hM9 B i ⟨0, h0⟩
  have ht0 := clock_t0Γ hM9 B i
  have s0 : brSlotΓ hM9 B (assemblyPieceAtΓ B i).lower = Sum.inl (.inl ⟨i, 0⟩) := brSlot_of_atomΓ B hM9 _ _ ht0
  refine ⟨s0, ?_⟩
  unfold recSlotsΓ
  simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_zero]
  have eq : ∀ (c : (assemblyShapeΓ hM9 B).TVar) (v : GBranch G.tree), (assemblyClockAtomEquivΓ hM9 B c).1 = v → ∀ v' : GBranch G.tree, v' = v →
      brSlotΓ hM9 B v' = Sum.inl c := fun c v h v' hv' => by subst hv'; exact brSlot_of_atomΓ B hM9 c _ h
  rcases hrung with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> by_cases hν : ν = 1 <;> simp only [hν, if_true, if_false]
  · left; exact ⟨eq _ _ (hy.trans h2) _ hqq.2, eq _ _ (hx.trans h1) _ hqq.1⟩
  · right; exact ⟨eq _ _ (hx.trans h1) _ hqq.1, eq _ _ (hy.trans h2) _ hqq.2⟩
  · right; exact ⟨eq _ _ (hx.trans h1) _ hqq.2, eq _ _ (hy.trans h2) _ hqq.1⟩
  · left; exact ⟨eq _ _ (hy.trans h2) _ hqq.1, eq _ _ (hx.trans h1) _ hqq.2⟩

open Classical VineParamContract in
/-- Clause (a) for a kind-0 record at the block `i`: the two pairs of one of its two forms. -/
def RecClause0Γ (hM9 : NormalChartSupply γF) (i : Fin (assemblyShapeΓ hM9 B).I) (kd : ℕ) (zc : Prop)
    (addr : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) : Prop :=
  kd = 0 → ¬ zc → ∃ h : 0 < (assemblyShapeΓ hM9 B).m i,
    (((.inr (.inl ⟨i, ⟨0, h⟩⟩), .inl ⟨i, 0⟩) ∈ addr) ∧ ((.inl ⟨i, 0⟩, .inl ⟨i, ⟨1, by omega⟩⟩) ∈ addr)) ∨
    (((.inl ⟨i, ⟨1, by omega⟩⟩, .inl ⟨i, 0⟩) ∈ addr) ∧ ((.inl ⟨i, 0⟩, .inr (.inl ⟨i, ⟨0, h⟩⟩)) ∈ addr))

open VineParamContract in
theorem rec_clause0Γ (hM9 : NormalChartSupply γF) (lv : LvlΓ B) (pstar : lv.ι) (lo : GBranch G.tree)
    (hlo : lo = (assemblyPieceAtΓ B (lv.e pstar).1).lower) {β : Type*} {d : ℕ} {S : SepTerms β d} {bs₁ bs₂ rA rB : Finset β}
    (c : Ch S bs₁ bs₂ rA rB) (caseA : Prop) :
    RecClause0Γ B hM9 (lv.e pstar).1 (recKind c)
      (ordBad (ordRels caseA c) (recSlotsΓ hM9 B lo (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar)) ∨
        (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
          qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∧ recKind c = 0))
      (ordPairs (ordRels caseA c) (recSlotsΓ hM9 B lo (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar))) := by
  intro hk0 hnz
  have hne : qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) ≠
      qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) := fun h => hnz (Or.inr ⟨h, hk0⟩)
  subst hlo
  obtain ⟨h, h0, h12⟩ := rec_slots_typeIIΓ B RD hG layer hLayer hM9 lv pstar (nuOf (lv.state B RD hG layer hLayer) pstar) hne
  refine ⟨h, ?_⟩
  exact kd0_ordPairs caseA c hk0 _ _ _ _ h0 h12

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
