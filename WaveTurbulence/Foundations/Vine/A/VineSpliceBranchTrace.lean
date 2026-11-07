/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSpliceLeafEquiv
/-! Actual iterated splices retain branching signs and literal branching
root addresses. Combined with full leaf traces this strengthens the quotient iso. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole
variable {w : ℕ} {G : Garden w}

/-- The actual old name of a branching root has the same address. -/
theorem clSplicedBranchName_root_address {H : Garden w} {S : Finset (GBranch H.tree)}
    {a b : GBranch H.tree} (hB : H.molecule.IsBlock S a b) (hCL : CLParentPattern H S a b)
    (D : CLSpliceSlots H S a b) (c : GBranch (clSplicedGardenOfSlots hB hCL D).tree)
    (hc : c.1.2 = []) : (clSplicedBranchNameEquiv hB hCL D c).1.1 = c.1 := by
  classical
  by_cases he : c = spliceCrownBranch (clSpliceBoundary hB hCL D)
  · subst c
    rw [clSplicedBranchName_crown]
    rfl
  · obtain ⟨p, rfl⟩ := spliceBranchPieceNew_surjective_except_crown (clSpliceBoundary hB hCL D) c he
    rw [clSplicedBranchName_piece]
    cases p with
    | inl c => rfl
    | inr p => exact ((List.append_ne_nil_of_right_ne_nil a.1.2 (List.cons_ne_nil p.1 p.2.1)) hc).elim

/-- Structural branching data carried by an actual splice state. -/
structure SpliceBranchTrace (st : SpState G) : Prop where
  sign : ∀ c : GBranch st.G.tree, st.G.sign c.toNode = G.sign (st.M.ob c).toNode
  root_address : ∀ c : GBranch st.G.tree, c.1.2 = [] → (st.M.ob c).1 = c.1

/-- The empty splice retains branching data literally. -/
theorem spliceBranchTrace_init (G : Garden w) : SpliceBranchTrace (SpState.init G) :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- An actual additional CL splice retains branching signs and root addresses. -/
theorem SpliceBranchTrace.add {st : SpState G} (T : SpliceBranchTrace st)
    (u : CLBlock G) (hU : ∀ v ∈ u.atoms, st.cls v = none) : SpliceBranchTrace (st.add u hU) := by
  let h := SpMap.pb_block st.M st.hcls hU u.isBlock u.cl
  let h2 := h.choose_spec
  let h3 := h2.choose_spec
  let hB := h3.2.2.1
  let hCL := h3.2.2.2
  let D := clSpliceSlotsOfBlock hB hCL
  constructor
  · intro c
    exact (clSplicedBranchName_sign hB hCL D c).trans (T.sign _)
  · intro c hc
    have hold : (stepB hB hCL D c).1.2 = [] := (clSplicedBranchName_root_iff hB hCL D c).mpr hc
    exact (T.root_address _ hold).trans (clSplicedBranchName_root_address hB hCL D c hc)

/-- Both branches of an actual fold step retain branching data. -/
theorem SpliceBranchTrace.step {st : SpState G} (T : SpliceBranchTrace st) (u : CLBlock G) :
    SpliceBranchTrace (spliceStep st u) := by
  classical
  unfold spliceStep
  split_ifs with h
  · exact T.add u h
  · exact T

/-- Every actual finite splice sequence retains branching data. -/
theorem SpliceBranchTrace.fold (l : List (CLBlock G)) (st : SpState G) (T : SpliceBranchTrace st) :
    SpliceBranchTrace (l.foldl spliceStep st) := by
  induction l generalizing st with
  | nil => exact T
  | cons u l ih => exact ih (spliceStep st u) (T.step u)

/-- Actual spliceFold branches retain their original signs and branching-root addresses. -/
theorem spliceFoldBranchTrace (l : List (CLBlock G)) : SpliceBranchTrace (spliceFold G l) :=
  SpliceBranchTrace.fold l (SpState.init G) (spliceBranchTrace_init G)

end WaveTurbulence.VineA
