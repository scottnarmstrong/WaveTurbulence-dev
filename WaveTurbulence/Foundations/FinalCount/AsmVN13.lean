/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN12
public import WaveTurbulence.Foundations.FinalCount.AsmTransport
/-! **FINALCOUNT-ASSEMBLY (VineNodeExists, part 13): transport of the single-vine classification to the state.**
`ObjVine M U` is the molecule-level single-vine classification of an object (an ordinary vine, resp. the adjoint of the designated bond is a
vine).  `singleVineVC_of_objVine`: for an intact `U` and ANY vine cut `K'` of the state along an object with the atoms of `U`,
`SingleVineVC K'` (forward transport along `stateIso`; the other designation of a hyper object by `hyper_other_isSomeVine`, the mate of the
designated bond by `eraseMateIso`). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
section vineutil
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D]

theorem isVine_swap {N : Molecule V D} {X : VineType} {S : Finset V} {a b : V} (h : N.IsVine X S a b) : N.IsVine X S b a := by
  obtain ⟨hB, k, hk, f, hinj, himg, hj, hb⟩ := h
  exact ⟨Mole.block_swap_joints N hB, k, hk, f, hinj, himg, by rw [Finset.pair_comm]; exact hj, hb⟩

theorem isVine_eraseBond_congr {N : Molecule V D} {e e' : D} (he : e = e') {X : VineType} {S : Finset V} {a b : V}
    (h : (N.eraseBond e).IsVine X S a b) : (N.eraseBond e').IsVine X S a b := by
  subst he; exact h

/-- The adjoints of `e` and of `mate e` are isomorphic on any group of atoms. -/
noncomputable def eraseMateIso (N : Molecule V D) (e : D) (B : Finset V) (hB : B ⊆ N.atoms) :
    RedSplice.InducedIso (N.eraseBond e) (N.eraseBond (N.mate e)) B B where
  π := id
  inj := Set.injOn_id _
  img := Finset.image_id
  sub := hB
  e :=
    { toFun := fun x => ⟨⟨x.1.1, x.1.2.2, by rw [N.mate_mate]; exact x.1.2.1⟩, x.2⟩
      invFun := fun y => ⟨⟨y.1.1, by simpa [N.mate_mate] using y.1.2.2, y.1.2.1⟩, y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  atom_comm := fun x => rfl
  mate_comm := fun x => rfl
  out_comm := fun x => rfl

theorem joints_cases {p q u l : V} (hpq : p ≠ q) (h : ({p, q} : Finset V) = {u, l}) :
    (p = u ∧ q = l) ∨ (p = l ∧ q = u) := by
  have hp : p ∈ ({u, l} : Finset V) := h ▸ Finset.mem_insert_self _ _
  have hq : q ∈ ({u, l} : Finset V) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd rfl hpq
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl hpq

/-- Two hyper objects with the same atoms and different designated bonds: the second one's adjoint is some vine. -/
theorem hyper_other_isSomeVine {N : Molecule V D} (O P : Object N) (hat : O.atoms = P.atoms) {R : HyperLikeRealization N O.atoms O.upper O.lower}
    {R' : HyperLikeRealization N P.atoms P.upper P.lower} (hO : O.shape = .hyper R) (hP : P.shape = .hyper R')
    (hdes : ¬ (R'.added = R.added ∨ R'.added = N.mate R.added)) :
    ∃ X, (Molecule.eraseBond N R'.added).IsVine X P.atoms P.upper P.lower := by
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
  exact WaveTurbulence.Vine.VC_with_joint_adj_isSomeVine _ R'.adjoint.toVine hAdj

theorem isVine_orient {N : Molecule V D} {X : VineType} {S : Finset V} {u l p q : V} (hpq : p ≠ q)
    (h : ({p, q} : Finset V) = {u, l}) (hv : N.IsVine X S u l) : N.IsVine X S p q := by
  rcases joints_cases hpq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hv
  · exact isVine_swap hv

theorem isVine_atoms_congr {N : Molecule V D} {X : VineType} {S S' : Finset V} {a b : V} (h : S = S')
    (hv : N.IsVine X S a b) : N.IsVine X S' a b := h ▸ hv

end vineutil

/-- The molecule-level single-vine classification of an object: an ordinary vine, resp. the adjoint of the designated bond is a vine. -/
def ObjVine {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (U : Object M) : Prop :=
  match U.shape with
  | .vc _ => ∃ X, M.IsVine X U.atoms U.upper U.lower
  | .hyper R => ∃ X, (Molecule.eraseBond M R.added).IsVine X U.atoms U.upper U.lower

variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

theorem singleVineVC_of_objVine {M₀ : Molecule V D₀} {s : St.{u} V D₀} {a : V → V} (hA : AncRel M₀ s a) (hD : DartRel M₀ s)
    (U : Object M₀) (hint : ∀ b ∈ U.atoms, b ∈ s.M.atoms ∧ s.cls b = .eps) (hov : ObjVine M₀ U)
    (K' : VineCut s.M) (hat : K'.C.atoms = U.atoms) : SingleVineVC K' := by
  let I := stateIso hA hD hint
  obtain ⟨A, u, l, sh⟩ := U
  simp only at hat hint hov
  have hat' : K'.C.atoms = (I.mapObj ⟨A, u, l, sh⟩ subset_rfl).atoms := hat.trans (Finset.image_id (s := A)).symm
  have hjoint : ({K'.C.upper, K'.C.lower} : Finset V) = {u, l} := object_joints_eq K'.C (I.mapObj ⟨A, u, l, sh⟩ subset_rfl) hat'
  cases sh with
  | vc h =>
    rcases object_shape_cases K'.C with ⟨h', hsh'⟩ | ⟨R', hsh'⟩
    · obtain ⟨X, hX⟩ := hov
      have hv : s.M.IsVine X A u l := I.isVine hX
      unfold SingleVineVC
      rw [hsh']
      exact ⟨X, isVine_atoms_congr hat.symm (isVine_orient K'.ab_ne hjoint hv)⟩
    · exact (not_vc_hyper_atoms (U := I.mapObj ⟨A, u, l, .vc h⟩ subset_rfl) (U' := K'.C) ⟨_, rfl⟩ ⟨R', hsh'⟩ hat'.symm).elim
  | hyper R =>
    rcases object_shape_cases K'.C with ⟨h', hsh'⟩ | ⟨R', hsh'⟩
    · exact (not_vc_hyper_atoms (U := K'.C) (U' := I.mapObj ⟨A, u, l, .hyper R⟩ subset_rfl) ⟨h', hsh'⟩ ⟨_, rfl⟩ hat').elim
    · have he : M₀.InGroup A R.added := RedSplice.inGroup_of_ends R.ends_eq R.adjoint.1.2.1 R.adjoint.1.2.2.1
      obtain ⟨Rt, hRt, hRta⟩ : ∃ Rt, (I.mapObj ⟨A, u, l, .hyper R⟩ subset_rfl).shape = .hyper Rt ∧ Rt.added = (I.e ⟨R.added, he⟩).1 :=
        ⟨_, rfl, rfl⟩
      obtain ⟨X, hX⟩ := hov
      have hv : (s.M.eraseBond (I.e ⟨R.added, he⟩).1).IsVine X A u l := (I.eraseE R.added he).isVine hX
      unfold SingleVineVC
      rw [hsh']
      by_cases h1 : R'.added = (I.e ⟨R.added, he⟩).1
      · exact ⟨X, isVine_atoms_congr hat.symm (isVine_orient K'.ab_ne hjoint (isVine_eraseBond_congr h1.symm hv))⟩
      · by_cases h2 : R'.added = s.M.mate (I.e ⟨R.added, he⟩).1
        · have hB : A ⊆ s.M.atoms := fun b hb => (hint b hb).1
          have hv2 := (eraseMateIso s.M (I.e ⟨R.added, he⟩).1 A hB).isVine hv
          exact ⟨X, isVine_atoms_congr hat.symm (isVine_orient K'.ab_ne hjoint (isVine_eraseBond_congr h2.symm hv2))⟩
        · refine hyper_other_isSomeVine (I.mapObj ⟨A, u, l, .hyper R⟩ subset_rfl) K'.C hat'.symm hRt hsh' ?_
          rw [hRta]
          exact fun h => h.elim h1 h2

/-- **`hcls0` of `vhard_of_atoms`.**  An intact object `U` that has three atoms or is classified as a single vine in `M₀`: every vine cut of the
state along an object with the atoms of `U` is a single vine or a double shape. -/
theorem hcls_state {M₀ : Molecule V D₀} {s : St.{u} V D₀} {a : V → V} (hA : AncRel M₀ s a) (hD : DartRel M₀ s)
    (hnl : ∀ x : s.D, s.M.atom x ≠ s.M.atom (s.M.mate x)) (hdeg : ∀ b ∈ s.M.atoms, s.M.deg b ≤ 4)
    (U : Object M₀) (hint : ∀ b ∈ U.atoms, b ∈ s.M.atoms ∧ s.cls b = .eps) (hsh : U.atoms.card = 3 ∨ ObjVine M₀ U)
    (K' : VineCut s.M) (hat : K'.C.atoms = U.atoms) : SingleVineVC K' ∨ Nonempty (DoubleShape K') := by
  rcases hsh with h3 | hov
  · exact Or.inr (doubleShape_of_card_three hnl hdeg K' (by rw [hat]; exact h3))
  · exact Or.inl (singleVineVC_of_objVine hA hD U hint hov K' hat)

end WaveTurbulence.FinalCountAsm
