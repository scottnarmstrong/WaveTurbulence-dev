/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmIntact
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVineSwap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.RedSpliceInduced
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Gamma
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineVCJointEdge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.G3GroupIso
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.RedSpliceInduced
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmVN13`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (VineNodeExists, part 13): transport of the single-vine classification to the state.**
`ObjVine M U` is the molecule-level single-vine classification of an object (an ordinary vine, resp. the adjoint of the designated bond is a
vine).  `singleVineVC_of_objVine`: for an intact `U` and ANY vine cut `K'` of the state along an object with the atoms of `U`,
`SingleVineVC K'` (forward transport along `stateIso`; the other designation of a hyper object by `hyper_other_isSomeVine`, the mate of the
designated bond by `eraseMateIso`). 

**Low-range change (L6-HASM).** `singleVineVC_of_objVine`, `hcls_state`: conclusion `Step1.SingleVineVCGamma` (family
member; H-ASM-PROGRESS "Interface decisions"); the drawn-type transports `I.isVine`, `isVine_orient`, … are replaced by
H-TV's `InducedIso.isVineS` and `AsmVineSwap`'s low-family forms.-/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
section vineutil
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D]

/-- Two hyper objects with the same atoms and different designated bonds: the second one's adjoint is some vine. -/
theorem hyper_other_isSomeVine {N : Molecule V D} (O P : Src.Object Src.γL N) (hat : O.atoms = P.atoms) {R : Src.HyperLikeRealization Src.γL N O.atoms O.upper O.lower}
    {R' : Src.HyperLikeRealization Src.γL N P.atoms P.upper P.lower} (hO : O.shape = .hyper R) (hP : P.shape = .hyper R')
    (hdes : ¬ (R'.added = R.added ∨ R'.added = N.mate R.added)) :
    (Molecule.eraseBond N R'.added).IsVineEnl P.atoms P.upper P.lower := by
  classical
  obtain ⟨A, a, b, sh⟩ := O
  obtain ⟨A', x, y, sh'⟩ := P
  simp only at hat R R' hO hP ⊢
  subst hat
  have hHR : Mole.IsHyperBlock N A a b := ⟨R.added, R.ends_eq, R.adjoint.1⟩
  have hHP : Mole.IsHyperBlock N A x y := ⟨R'.added, R'.ends_eq, R'.adjoint.1⟩
  have hdU := Mole.hyperBlock_degrees N hHR
  have hdP := Mole.hyperBlock_degrees N hHP
  have hBR := R.adjoint.1
  have hBP := R'.adjoint.1
  have hab : a ≠ b := hBR.2.2.2.1
  have hxy : x ≠ y := hBP.2.2.2.1
  have hj : ({x, y} : Finset V) = {a, b} :=
    WaveTurbulence.Vine.joints_eq_of_two_low_degrees N (Finset.Subset.refl A) hBR.2.1 hBR.2.2.1 hab hxy
      hdU.1.le hdU.2.1.le hdP.2.2
  have hs : s(x, y) = s(a, b) := by
    have hxa : x ∈ ({a, b} : Finset V) := hj ▸ Finset.mem_insert_self _ _
    have hya : y ∈ ({a, b} : Finset V) := hj ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxa hya
    rcases hxa with rfl | rfl <;> rcases hya with rfl | rfl
    all_goals first | exact absurd rfl hxy | rfl | exact Sym2.eq_swap
  set e := R.added with he
  set f := R'.added with hf
  have hef : e ≠ f := fun h => hdes (Or.inl h.symm)
  have hemf : e ≠ N.mate f := fun h => hdes (Or.inr (by rw [h, N.mate_mate]))
  have hmef : N.mate e ≠ f := fun h => hdes (Or.inr h.symm)
  have hmemf : N.mate e ≠ N.mate f := fun h => hef (Mole.mate_injective N h)
  have hendsE : N.ends e = s(x, y) := R.ends_eq.trans hs.symm
  have hAdj : (Mole.eraseBond N f).Adj x y := by
    have h2 := Sym2.eq_iff.mp hendsE
    change (N.atom e = x ∧ N.atom (N.mate e) = y) ∨ (N.atom e = y ∧ N.atom (N.mate e) = x) at h2
    rcases h2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨e, hef, hemf⟩, h1, h2⟩
    · refine ⟨⟨N.mate e, hmef, hmemf⟩, h2, ?_⟩
      change N.atom (N.mate (N.mate e)) = y
      rw [N.mate_mate]; exact h1
  exact Src.isSomeVine_γL_iff.mp (VC_with_joint_adj_isSomeVine _ R'.adjoint.toVine hAdj)

end vineutil

/-- The molecule-level single-vine classification of an object: an ordinary vine, resp. the adjoint of the designated bond is a vine. -/
def ObjVine {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (U : Src.Object Src.γL M) : Prop :=
  match U.shape with
  | .vc _ => M.IsVineEnl U.atoms U.upper U.lower
  | .hyper R => (Molecule.eraseBond M R.added).IsVineEnl U.atoms U.upper U.lower

variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

theorem singleVineVC_of_objVine {M₀ : Molecule V D₀} {s : St.{u} V D₀} {a : V → V} (hA : AncRel M₀ s a) (hD : DartRel M₀ s)
    (U : Src.Object Src.γL M₀) (hint : ∀ b ∈ U.atoms, b ∈ s.M.atoms ∧ s.cls b = .eps) (hov : ObjVine M₀ U)
    (K' : Step1.VineCut Src.γL s.M) (hat : K'.C.atoms = U.atoms) : Step1.SingleVineVCGamma K' := by
  let I := stateIso hA hD hint
  obtain ⟨A, u, l, sh⟩ := U
  simp only at hat hint hov
  have hat' : K'.C.atoms = (I.mapObjL ⟨A, u, l, sh⟩ subset_rfl).atoms := hat.trans (Finset.image_id (s := A)).symm
  have hjoint : ({K'.C.upper, K'.C.lower} : Finset V) = {u, l} := object_joints_eq K'.C (I.mapObjL ⟨A, u, l, sh⟩ subset_rfl) hat'
  cases sh with
  | vc h =>
    rcases object_shape_cases K'.C with ⟨h', hsh'⟩ | ⟨R', hsh'⟩
    · have hX : Src.IsSomeVine Src.γL M₀ A u l := Src.isSomeVine_γL_iff.mpr hov
      have hv : Src.IsSomeVine Src.γL s.M A u l := I.isVineS hX
      unfold Step1.SingleVineVCGamma
      rw [hsh']
      exact isSomeVine_atoms_congr hat.symm (isSomeVine_orient K'.ab_ne hjoint hv)
    · exact (not_vc_hyper_atoms (U := I.mapObjL ⟨A, u, l, .vc h⟩ subset_rfl) (U' := K'.C) ⟨_, rfl⟩ ⟨R', hsh'⟩ hat'.symm).elim
  | hyper R =>
    rcases object_shape_cases K'.C with ⟨h', hsh'⟩ | ⟨R', hsh'⟩
    · exact (not_vc_hyper_atoms (U := K'.C) (U' := I.mapObjL ⟨A, u, l, .hyper R⟩ subset_rfl) ⟨h', hsh'⟩ ⟨_, rfl⟩ hat').elim
    · have he : M₀.InGroup A R.added := RedSplice.inGroup_of_ends R.ends_eq R.adjoint.1.2.1 R.adjoint.1.2.2.1
      obtain ⟨Rt, hRt, hRta⟩ : ∃ Rt, (I.mapObjL ⟨A, u, l, .hyper R⟩ subset_rfl).shape = .hyper Rt ∧ Rt.added = (I.e ⟨R.added, he⟩).1 :=
        ⟨_, rfl, rfl⟩
      have hX : Src.IsSomeVine Src.γL (M₀.eraseBond R.added) A u l := Src.isSomeVine_γL_iff.mpr hov
      have hv : Src.IsSomeVine Src.γL (s.M.eraseBond (I.e ⟨R.added, he⟩).1) A u l := (I.eraseE R.added he).isVineS hX
      unfold Step1.SingleVineVCGamma
      rw [hsh']
      by_cases h1 : R'.added = (I.e ⟨R.added, he⟩).1
      · exact isSomeVine_atoms_congr hat.symm (isSomeVine_orient K'.ab_ne hjoint (isSomeVine_eraseBond_congr h1.symm hv))
      · by_cases h2 : R'.added = s.M.mate (I.e ⟨R.added, he⟩).1
        · have hB : A ⊆ s.M.atoms := fun b hb => (hint b hb).1
          have hv2 := (eraseMateIso s.M (I.e ⟨R.added, he⟩).1 A hB).isVineS hv
          exact isSomeVine_atoms_congr hat.symm
            (isSomeVine_orient K'.ab_ne hjoint (isSomeVine_eraseBond_congr h2.symm hv2))
        · refine Src.isSomeVine_γL_iff.mpr
            (hyper_other_isSomeVine (I.mapObjL ⟨A, u, l, .hyper R⟩ subset_rfl) K'.C hat'.symm hRt hsh' ?_)
          rw [hRta]
          exact fun h => h.elim h1 h2

/-- **`hcls0` of `vhard_of_atoms`.**  An intact object `U` that has three atoms or is classified as a single vine in `M₀`: every vine cut of the
state along an object with the atoms of `U` is a single vine or a double shape. -/
theorem hcls_state {M₀ : Molecule V D₀} {s : St.{u} V D₀} {a : V → V} (hA : AncRel M₀ s a) (hD : DartRel M₀ s)
    (hnl : ∀ x : s.D, s.M.atom x ≠ s.M.atom (s.M.mate x)) (hdeg : ∀ b ∈ s.M.atoms, s.M.deg b ≤ 4)
    (U : Src.Object Src.γL M₀) (hint : ∀ b ∈ U.atoms, b ∈ s.M.atoms ∧ s.cls b = .eps) (hsh : U.atoms.card = 3 ∨ ObjVine M₀ U)
    (K' : Step1.VineCut Src.γL s.M) (hat : K'.C.atoms = U.atoms) : Step1.SingleVineVCGamma K' ∨ Nonempty (Step1.DoubleShape K') := by
  rcases hsh with h3 | hov
  · exact Or.inr (doubleShape_of_card_three hnl hdeg K' (by rw [hat]; exact h3))
  · exact Or.inl (singleVineVC_of_objVine hA hD U hint hov K' hat)

end WaveTurbulence.GammaLow.FinalCount.H
