/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSpliceLeaves
public import WaveTurbulence.Foundations.Molecule.CLLPLeaves
/-! Actual iterated splice maps preserve PC/LP dart tags and agree with
the full original-leaf trace on LP darts. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole
variable {w : ℕ} {G : Garden w}

/-- Original LP leaf data obtained from the full leaf trace. -/
def SpliceLeafTrace.lp {st : SpState G} (T : SpliceLeafTrace st) (l : GardenLPLeaf st.G) : GardenLPLeaf G :=
  ⟨T.leaf l.1, (T.mark l.1).symm.trans l.2.1,
    fun h => l.2.2.1 ((T.root _).mp h), by
      intro h
      apply l.2.2.2
      apply (T.root (st.G.pair l.1)).mp
      rw [T.pair]
      exact h⟩

/-- Original nonroot branch data obtained from the actual old branch map. -/
def spliceOldPC (st : SpState G) (c : {c : GBranch st.G.tree // c.1.2 ≠ []}) :
    {c : GBranch G.tree // c.1.2 ≠ []} :=
  ⟨st.M.ob c.1, fun h => c.2 ((st.M.ob_root c.1).mp h)⟩

/-- Compatibility of actual dart names with the branch and full leaf traces. -/
structure SpliceDartTrace {st : SpState G} (T : SpliceLeafTrace st) : Prop where
  pc : ∀ (c : {c : GBranch st.G.tree // c.1.2 ≠ []}) (side : Bool),
    st.M.od (.inl (c, side)) = .inl (spliceOldPC st c, side)
  lp : ∀ l : GardenLPLeaf st.G, st.M.od (.inr l) = .inr (T.lp l)

/-- The empty splice preserves dart tags literally. -/
theorem spliceDartTrace_init (G : Garden w) : SpliceDartTrace (spliceLeafTrace_init G) :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

/-- One actual CL splice preserves both dart tags and their old names. -/
theorem SpliceDartTrace.add {st : SpState G} {T : SpliceLeafTrace st} (H : SpliceDartTrace T)
    (u : CLBlock G) (hU : ∀ v ∈ u.atoms, st.cls v = none) : SpliceDartTrace (T.add u hU) := by
  let h := SpMap.pb_block st.M st.hcls hU u.isBlock u.cl
  let h2 := h.choose_spec
  let h3 := h2.choose_spec
  let hB := h3.2.2.1
  let hCL := h3.2.2.2
  let D := clSpliceSlotsOfBlock hB hCL
  constructor
  · intro c side
    change st.M.od (stepD hB hCL D (.inl (c, side))) = _
    rw [show stepD hB hCL D (.inl (c, side)) = .inl ((clPCChildEquiv hB hCL D c).1, side)
      from clSplicedDartEquiv_pc hB hCL D c side, H.pc]
    rfl
  · intro l
    change st.M.od (stepD hB hCL D (.inr l)) = _
    rw [show stepD hB hCL D (.inr l) = .inr (clLPLeafEquiv hB hCL D l).1
      from clSplicedDartEquiv_lp hB hCL D l, H.lp]
    apply congrArg Sum.inr
    apply Subtype.ext
    exact congrArg T.leaf (clLPLeafEquiv_name hB hCL D l)

/-- Dart compatibility is preserved by literal transport of the splice state. -/
theorem SpliceDartTrace.transport {st st' : SpState G} {T : SpliceLeafTrace st}
    (H : SpliceDartTrace T) (h : st = st') : SpliceDartTrace (h ▸ T) := by
  cases h
  exact H

/-- A skipped fold step preserves the same actual dart trace. -/
theorem SpliceDartTrace.step {st : SpState G} {T : SpliceLeafTrace st} (H : SpliceDartTrace T)
    (u : CLBlock G) : SpliceDartTrace (T.step u) := by
  classical
  unfold SpliceLeafTrace.step
  split_ifs with h
  · exact (H.add u h).transport _
  · exact H.transport _

/-- All actual finite splice sequences preserve PC and LP tags. -/
theorem SpliceDartTrace.fold (l : List (CLBlock G)) (st : SpState G) (T : SpliceLeafTrace st)
    (H : SpliceDartTrace T) : SpliceDartTrace (T.fold l st) := by
  induction l generalizing st with
  | nil => exact H
  | cons u l ih => exact ih (spliceStep st u) (T.step u) (H.step u)

/-- Dart and full-leaf traces agree for the actual spliceFold garden. -/
theorem spliceFoldDartTrace (l : List (CLBlock G)) : SpliceDartTrace (spliceFoldLeafTrace l) :=
  SpliceDartTrace.fold l (SpState.init G) (spliceLeafTrace_init G) (spliceDartTrace_init G)

end WaveTurbulence.VineA
