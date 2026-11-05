/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreStemStart
public import WaveTurbulence.Foundations.Molecule.VineSGJointExclusion
import Mathlib.Tactic

/-! # The stem-start double pairs in all eight pinned vine templates -/

public section
namespace WaveTurbulence.Vine

/-- Two rail predecessors and the doubled pair they meet in the core. -/
structure StemStart where
  predUpper : ℕ
  predLower : ℕ
  upper : ℕ
  lower : ℕ
  deriving DecidableEq

/-- Original doubled pairs immediately adjacent to the outer joints.
Type V uses two different outer predecessors; type VIII starts from joint 1. -/
@[expose] def stemStarts : VineType → List StemStart
  | .I => []
  | .II => [⟨0,0,2,3⟩]
  | .III | .IV => [⟨0,0,2,3⟩,⟨1,1,7,8⟩]
  | .V => [⟨0,1,2,3⟩]
  | .VI => [⟨0,0,2,3⟩,⟨1,1,13,14⟩]
  | .VII => [⟨0,0,2,3⟩,⟨1,1,9,10⟩]
  | .VIII => [⟨1,1,4,5⟩]

/-- Literal index, edge and multiplicity checks for every listed start. -/
theorem stemStarts_valid (X : VineType) : ∀ c ∈ stemStarts X,
    c.predUpper<X.template.n ∧ c.predLower<X.template.n ∧
    c.upper<X.template.n ∧ c.lower<X.template.n ∧
    c.predUpper<2 ∧ c.predLower<2 ∧ c.upper ≠ c.lower ∧
    c.predLower ≠ c.upper ∧ c.predUpper ≠ c.lower ∧
    2 ≤ X.template.bonds.count (c.upper,c.lower) ∧
    (c.predUpper,c.upper) ∈ X.template.bonds ∧
    (c.predLower,c.lower) ∈ X.template.bonds := by
  cases X <;> decide

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every listed stem-start pair is absent from a connected block larger
than a double bond when both outer joints are absent. This holds for every
rung count and every pinned vine type. -/
theorem stemStarts_absent (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hS : M.IsBlock S a b) {A : Finset V} {x y : V} (hA : M.IsBlock A x y)
    (hC : GroupConnected M A) (hcard : 2<A.card) (ha : a ∉ A) (hb : b ∉ A)
    (c : StemStart) (hc : c ∈ stemStarts X) :
    ∀ v ∈ S,R.f v=c.upper ∨ R.f v=c.lower → v ∉ A := by
  obtain ⟨hju,hjl,hu,hl,hj2,hl2,hul,hl_u,hj_l,hd,he1,he2⟩ := stemStarts_valid X c hc
  have hempty := core_stem_start_absent_two_joints M hM R hS hA hC hcard ha hb
    ⟨c.predUpper,hju⟩ ⟨c.predLower,hjl⟩ ⟨c.upper,hu⟩ ⟨c.lower,hl⟩ hj2 hl2
    (fun h => hul (congrArg Fin.val h)) (fun h => hl_u (congrArg Fin.val h))
    (fun h => hj_l (congrArg Fin.val h)) hd he1 he2
  intro v hv hlabel
  rcases hlabel with h | h
  · have he : v=(R.coreAtom ⟨c.upper,hu⟩).1 :=
      R.injOn hv (R.coreAtom ⟨c.upper,hu⟩).2 (h.trans (R.label_coreAtom ⟨c.upper,hu⟩).symm)
    simpa only [he] using hempty.1
  · have he : v=(R.coreAtom ⟨c.lower,hl⟩).1 :=
      R.injOn hv (R.coreAtom ⟨c.lower,hl⟩).2 (h.trans (R.label_coreAtom ⟨c.lower,hl⟩).symm)
    simpa only [he] using hempty.2

/-- TARGET subsetvc, first stem stage: source SG and outer LG/ZG gap
conditions force all listed stem-start pairs to be absent from an inner
VC larger than one double bond. Rung counts are completely arbitrary. -/
theorem SG_stemStarts_absent {d : ℕ} (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hS : M.IsBlock S a b) {A : Finset V} {x y : V} (hVC : IsVC M A x y)
    (hAS : A ⊆ S) (hcard : 2<A.card) (L γ η : ℝ) (w : Mom d)
    (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ)
    (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0) {r r' : Mom d}
    (hr : M.IsBlockGap L w κ S a r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) :
    ∀ c ∈ stemStarts X,∀ v ∈ S,R.f v=c.upper ∨ R.f v=c.lower → v ∉ A := by
  have hj := SG_block_outer_joints_absent M hM hS hVC.1 hAS L γ η w c κ hκ hc hr hr' houter hsmall
  intro st hst
  exact stemStarts_absent M hM R hS hVC.1 (isVC_connected hVC) hcard hj.1 hj.2 st hst

end WaveTurbulence.Vine
