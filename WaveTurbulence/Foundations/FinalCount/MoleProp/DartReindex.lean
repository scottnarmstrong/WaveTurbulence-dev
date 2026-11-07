/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.FreeNormalization
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DeletionFibers
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairCircuit
import Mathlib.Tactic

/-! # Actual counting quantities under a bijection of half-edge carriers -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

def relabelDartLabels (f : D ≃ E) {K : Type*} : (D → K) ≃ (E → K) where
  toFun κ := fun y => κ (f.symm y)
  invFun κ' := fun x => κ' (f x)
  left_inv κ := by funext x; exact congrArg κ (f.symm_apply_apply x)
  right_inv κ' := by funext y; exact congrArg κ' (f.apply_symm_apply y)

theorem sum_dartsAt_reindex (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (ha : ∀ x, N.atom (f x) = M.atom x) (v : V)
    {A : Type*} [AddCommMonoid A] (g : E → A) :
    ∑ x ∈ M.dartsAt v, g (f x) = ∑ y ∈ N.dartsAt v, g y := by
  apply sum_bij (fun x _ => f x)
  · intro x hx
    exact (Mole.mem_dartsAt N v _).mpr ((ha x).trans ((Mole.mem_dartsAt M v x).mp hx))
  · intro x _ y _ h
    exact f.injective h
  · intro y hy
    refine ⟨f.symm y,?_,f.apply_symm_apply y⟩
    apply (Mole.mem_dartsAt M v _).mpr
    have hh := ha (f.symm y)
    rw [f.apply_symm_apply] at hh
    exact hh.symm.trans ((Mole.mem_dartsAt N v y).mp hy)
  · intro x _; rfl

theorem countEFree_le_of_dart_equiv (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x, N.atom (f x) = M.atom x)
    (hm : ∀ x, N.mate (f x) = f (M.mate x)) (ho : ∀ x, N.out (f x) = M.out x)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (E → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → Adm' (relabelDartLabels f κ)) :
    countEFree M L γ δ w Adm ≤ countEFree N L γ δ w Adm' := by
  classical
  conv_lhs => unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let k0' := fun y => k0 (f.symm y)
  have hk0' : ∀ y, k0' (N.mate y) = k0' y := by
    intro y
    obtain ⟨x,rfl⟩ := f.surjective y
    simp only [k0',hm,f.symm_apply_apply,hk0]
  let A := {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}
  let B := {κ' | N.IsDecoration L w c κ' ∧ N.IsRestricted L γ δ w β k0' κ' ∧ Adm' κ'}
  have hsign (x : D) : N.dartSign (f x) = M.dartSign x := by simp only [Molecule.dartSign,ho]
  have hkv (κ : D → (Fin d → ℤ)) (x : D) :
      Molecule.kvec L w (relabelDartLabels f κ) (f x) = Molecule.kvec L w κ x := by
    simp only [Molecule.kvec,relabelDartLabels,Equiv.coe_fn_mk,f.symm_apply_apply]
  have hmap : Set.MapsTo (relabelDartLabels f) A B := by
    intro κ hκ
    have hsum (v : V) : ∑ y ∈ N.dartsAt v, N.dartSign y • Molecule.kvec L w (relabelDartLabels f κ) y =
        ∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L w κ x := by
      rw [← sum_dartsAt_reindex M N f ha v (fun y => N.dartSign y • Molecule.kvec L w (relabelDartLabels f κ) y)]
      simp only [hsign,hkv]
    have henergy (v : V) : N.Gamma L w (relabelDartLabels f κ) v = M.Gamma L w κ v := by
      unfold Molecule.Gamma
      rw [← sum_dartsAt_reindex M N f ha v (fun y => N.dartSign y * ‖Molecule.kvec L w (relabelDartLabels f κ) y‖ ^ 2)]
      simp only [hsign,hkv]
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,hAdm κ hκ.2.2⟩
    · intro y
      obtain ⟨x,rfl⟩ := f.surjective y
      simp only [relabelDartLabels,Equiv.coe_fn_mk,hm,f.symm_apply_apply,hκ.1.1]
    · intro v hv
      rw [hsum]
      exact hκ.1.2 v (hA.symm ▸ hv)
    · intro v hv
      rw [henergy]
      exact hκ.2.1.1 v (hA.symm ▸ hv)
    · intro y
      obtain ⟨x,rfl⟩ := f.surjective y
      simpa only [hkv,k0',f.symm_apply_apply] using hκ.2.1.2 x
  exact (Set.encard_le_encard_of_injOn hmap (relabelDartLabels f).injective.injOn).trans
    (encard_le_countEFree N L γ δ w Adm' c β k0' hk0')

theorem ladderCells_eq_of_dart_equiv (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x, N.atom (f x) = M.atom x)
    (hm : ∀ x, N.mate (f x) = f (M.mate x)) (ho : ∀ x, N.out (f x) = M.out x) :
    ladderCells M = ladderCells N := by
  classical
  have hend (x : D) : N.ends (f x) = M.ends x := by
    unfold Molecule.ends
    rw [ha,hm,ha]
  have hBB (a b : V) : M.bondsBetween a b = N.bondsBetween a b := by
    unfold Molecule.bondsBetween
    apply card_bij (fun x _ => f x)
    · intro x hx
      simp only [mem_filter,Molecule.bonds,mem_univ,true_and] at hx ⊢
      exact ⟨(ho x).trans hx.1,(hend x).trans hx.2⟩
    · intro x _ y _ he
      exact f.injective he
    · intro y hy
      obtain ⟨x,rfl⟩ := f.surjective y
      refine ⟨x,?_,rfl⟩
      simp only [mem_filter,Molecule.bonds,mem_univ,true_and] at hy ⊢
      exact ⟨(ho x).symm.trans hy.1,(hend x).symm.trans hy.2⟩
  have hdir (a b : V) : M.Directed a b ↔ N.Directed a b := by
    constructor
    · rintro ⟨x,hx,hxa,hxb⟩
      refine ⟨f x,(ho x).trans hx,(ha x).trans hxa,?_⟩
      rw [hm,ha]
      exact hxb
    · rintro ⟨y,hy,hya,hyb⟩
      obtain ⟨x,rfl⟩ := f.surjective y
      refine ⟨x,(ho x).symm.trans hy,(ha x).symm.trans hya,?_⟩
      rw [hm,ha] at hyb
      exact hyb
  have hSL {m : ℕ} (u v : Fin (m+1) → V) :
      Degen.SourceLadder M u v ↔ Degen.SourceLadder N u v := by
    simp only [Degen.SourceLadder,hA,hBB,hdir]
  ext S
  simp only [ladderCells,mem_filter,mem_powerset,hA,IsLadderCell,hSL]

/-- Both the actual parameter supremum and every source-normalizing factor
respect the same literal half-edge relabeling. -/
theorem countAFree_le_of_dart_equiv (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x, N.atom (f x) = M.atom x)
    (hm : ∀ x, N.mate (f x) = f (M.mate x)) (ho : ∀ x, N.out (f x) = M.out x)
    {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (E → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → Adm' (relabelDartLabels f κ)) (P : Finset V → ℝ) :
    countAFree M L γ δ C1 w Adm P ≤ countAFree N L γ δ C1 w Adm' P := by
  have hχ := circuitRank_eq_of_dart_equiv M N f hA ha hm ho
  have hcells := ladderCells_eq_of_dart_equiv M N f hA ha hm ho
  unfold countAFree cellProduct
  rw [hχ,hcells]
  exact mul_le_mul_of_nonneg_right (ENat.toENNReal_mono
    (countEFree_le_of_dart_equiv M N f hA ha hm ho L γ δ w Adm Adm' hAdm)) bot_le

/-- Literal iterated projected restrictions flatten to the same actual
old completion under the union-erasure carrier equivalence. -/
theorem erasedFreeAdmissibility_twice_maps_union (M : Molecule V D) (Y Z : Finset V)
    {d : ℕ} (Adm : (D → (Fin d → ℤ)) → Prop)
    {κ : Degen.RetainedDart (Degen.eraseAtoms M Y) Z → (Fin d → ℤ)}
    (hκ : erasedFreeAdmissibility (Degen.eraseAtoms M Y) Z (erasedFreeAdmissibility M Y Adm) κ) :
    erasedFreeAdmissibility M (Y ∪ Z) Adm (relabelDartLabels (eraseDartUnionEquiv M Y Z) κ) := by
  obtain ⟨κY,⟨κ0,hA,hb,rfl⟩,_hbY,rfl⟩ := hκ
  exact ⟨κ0,hA,hb,by funext x; rfl⟩

/-- Two normalized atom-removal bounds end at the actual simultaneous
union-erasure problem, with no conclusion-shaped counting compatibility. -/
theorem countAFree_erase_twice_le_union (M : Molecule V D) (Y Z : Finset V)
    {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ) :
    countAFree (Degen.eraseAtoms (Degen.eraseAtoms M Y) Z) L γ δ C1 w
      (erasedFreeAdmissibility (Degen.eraseAtoms M Y) Z (erasedFreeAdmissibility M Y Adm)) P ≤
    countAFree (Degen.eraseAtoms M (Y ∪ Z)) L γ δ C1 w (erasedFreeAdmissibility M (Y ∪ Z) Adm) P := by
  apply countAFree_le_of_dart_equiv _ _ (eraseDartUnionEquiv M Y Z)
  · ext a
    change (a ∈ (M.atoms \ Y) \ Z) ↔ a ∈ M.atoms \ (Y ∪ Z)
    simp only [mem_sdiff,mem_union,not_or]
    tauto
  · intro x; rfl
  · intro x; exact Subtype.ext rfl
  · intro x; rfl
  · intro κ hκ
    exact erasedFreeAdmissibility_twice_maps_union M Y Z Adm hκ

end WaveTurbulence.MoleProp
