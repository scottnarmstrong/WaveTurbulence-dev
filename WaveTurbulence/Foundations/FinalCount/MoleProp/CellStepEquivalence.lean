/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.LadderCells
public import WaveTurbulence.Foundations.FinalCount.Degen.SourceLadderIntervals
import Mathlib.Tactic

/-! # Actual cells are exactly the distinct steps of maximal selected ladders -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The four actual atoms at one consecutive pair of selected rungs. -/
def ladderStepAtoms {m : ℕ} (u v : Fin (m+1) → V) (i : Fin m) : Finset V :=
  {u i.castSucc,v i.castSucc,u i.succ,v i.succ}

private theorem ladderAtoms_fin_two (u v : Fin 2 → V) :
    Molecule.ladderAtoms u v = {u 0,v 0,u 1,v 1} := by
  change (univ.image u ∪ univ.image v) = {u 0,v 0,u 1,v 1}
  have he : (univ : Finset (Fin 2)) = {0,1} := by decide
  rw [he]
  ext x
  simp only [image_insert,image_singleton,mem_union,mem_insert,mem_singleton]
  tauto

theorem isLadderCell_step (M : Molecule V D) {m : ℕ} {u v : Fin (m+1) → V}
    (hL : SourceLadder M u v) (i : Fin m) : IsLadderCell M (ladderStepAtoms u v i) := by
  let E := ladderIntervalEmbedding m i.val 1 (by have := i.isLt; omega)
  have h0 : E 0 = i.castSucc := Fin.ext (by simp only [E,ladderIntervalEmbedding]; rfl)
  have h1 : E 1 = i.succ := Fin.ext (by simp only [E,ladderIntervalEmbedding]; rfl)
  refine ⟨fun j => u (E j),fun j => v (E j),sourceLadder_interval M hL i.val 1
    (by have := i.isLt; omega) (by omega),?_⟩
  rw [ladderAtoms_fin_two]
  simp only [h0,h1,ladderStepAtoms]

theorem ladderStepAtoms_subset {m : ℕ} (u v : Fin (m+1) → V) (i : Fin m) :
    ladderStepAtoms u v i ⊆ Molecule.ladderAtoms u v := by
  intro x hx
  simp only [ladderStepAtoms,mem_insert,mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact mem_union_left _ (mem_image_of_mem u (mem_univ _))
  · exact mem_union_right _ (mem_image_of_mem v (mem_univ _))
  · exact mem_union_left _ (mem_image_of_mem u (mem_univ _))
  · exact mem_union_right _ (mem_image_of_mem v (mem_univ _))

/-- Distinct steps have distinct four-atom cells, from injectivity of the
actual two-rail atom sequence, including its endpoint cases. -/
theorem ladderStepAtoms_injective {m : ℕ} {u v : Fin (m+1) → V}
    (hinj : Function.Injective (Sum.elim u v)) : Function.Injective (ladderStepAtoms u v) := by
  obtain ⟨hu,_hv,huv⟩ := Sum.elim_injective.mp hinj
  have hindex (j : Fin m) (k : Fin (m+1)) (hk : u k ∈ ladderStepAtoms u v j) :
      k = j.castSucc ∨ k = j.succ := by
    simp only [ladderStepAtoms,mem_insert,mem_singleton] at hk
    rcases hk with hk | hk | hk | hk
    · exact Or.inl (hu hk)
    · exact False.elim (huv _ _ hk)
    · exact Or.inr (hu hk)
    · exact False.elim (huv _ _ hk)
  intro i j hij
  have hstart : u i.castSucc ∈ ladderStepAtoms u v j := by
    rw [← hij]; simp [ladderStepAtoms]
  have hend : u i.succ ∈ ladderStepAtoms u v j := by
    rw [← hij]; simp [ladderStepAtoms]
  have hs := hindex j i.castSucc hstart
  have he := hindex j i.succ hend
  apply Fin.ext
  rcases hs with hs | hs <;> rcases he with he | he
  all_goals
    have hs' := congrArg Fin.val hs
    have he' := congrArg Fin.val he
    simp only [Fin.val_castSucc,Fin.val_succ] at hs' he'
    omega

/-- Physical source alignment identifies any contained length-one cell
with one consecutive step, up to row exchange and traversal reversal. -/
theorem exists_step_eq_of_cell_subset (M : Molecule V D) (hM : M.IsMolecule)
    {m : ℕ} {u v : Fin (m+1) → V} (hL : SourceLadder M u v)
    {S : Finset V} (hS : IsLadderCell M S) (hsub : S ⊆ Molecule.ladderAtoms u v) :
    ∃ i : Fin m, S = ladderStepAtoms u v i := by
  obtain ⟨p,q,hK,rfl⟩ := hS
  obtain ⟨i,hi⟩ := sourceLadder_first_pair_alignment M hM hL hK hsub
  refine ⟨i,?_⟩
  rw [ladderAtoms_fin_two]
  rcases hi with ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩
  all_goals
    have hone : (⟨1,by decide⟩ : Fin 2) = 1 := by decide
    rw [hone] at h2 h3
    rw [h0,h1,h2,h3]
    ext x
    simp only [ladderStepAtoms,mem_insert,mem_singleton] <;> tauto

/-- Literal cell membership is equivalent to being one actual step of an
actual maximal selected ladder, with no repeated or missing ladder positions. -/
theorem mem_ladderCells_iff_maximal_step (M : Molecule V D) (hM : M.IsMolecule) (S : Finset V) :
    S ∈ ladderCells M ↔ ∃ (m : ℕ) (u v : Fin (m+1) → V), SourceLadder M u v ∧
      Molecule.ladderAtoms u v ∈ sourceMaximalLadders M ∧ ∃ i : Fin m, S = ladderStepAtoms u v i := by
  classical
  constructor
  · intro hS
    have hcell : IsLadderCell M S := (mem_filter.mp hS).2
    obtain ⟨p,q,hK,hKS⟩ := hcell
    have hset : SourceLadderSet M S := ⟨1,p,q,hK,hKS⟩
    obtain ⟨T,hT,hST⟩ := exists_sourceMaximalLadder_superset M hset
    obtain ⟨m,u,v,hL,hLT⟩ := (mem_filter.mp hT).2.1
    obtain ⟨i,hi⟩ := exists_step_eq_of_cell_subset M hM hL ⟨p,q,hK,hKS⟩ (hLT.symm ▸ hST)
    exact ⟨m,u,v,hL,hLT.symm ▸ hT,i,hi⟩
  · rintro ⟨m,u,v,hL,_hmax,i,rfl⟩
    have hcell := isLadderCell_step M hL i
    exact mem_filter.mpr ⟨mem_powerset.mpr (isLadderCell_subset_atoms M hcell),hcell⟩

/-- Every actual maximal atomset admits its actual finite ladder enumeration.
Only the actual family is indexed, so the empty molecule causes no default
or nonempty-carrier requirement. -/
theorem exists_maximal_ladder_representatives (M : Molecule V D) :
    ∃ (m : {S // S ∈ sourceMaximalLadders M} → ℕ)
      (u v : ∀ S : {S // S ∈ sourceMaximalLadders M}, Fin (m S+1) → V),
      ∀ S, SourceLadder M (u S) (v S) ∧ Molecule.ladderAtoms (u S) (v S) = S.val := by
  classical
  have hex (S : {S // S ∈ sourceMaximalLadders M}) :
      ∃ (m : ℕ) (u v : Fin (m+1) → V), SourceLadder M u v ∧ Molecule.ladderAtoms u v = S.val :=
    (mem_filter.mp S.property).2.1
  choose m u v h using hex
  exact ⟨m,u,v,h⟩

/-- Every cell factor occurs exactly once in the product over the steps of
maximal ladders. Sequence representatives are arbitrary actual enumerations;
the equality proves that the product is independent of their choice. -/
theorem prod_ladderCells_eq_maximal_steps (M : Molecule V D) (hM : M.IsMolecule)
    (m : {S // S ∈ sourceMaximalLadders M} → ℕ)
    (u v : ∀ S : {S // S ∈ sourceMaximalLadders M}, Fin (m S+1) → V)
    (hrep : ∀ S, SourceLadder M (u S) (v S) ∧ Molecule.ladderAtoms (u S) (v S) = S.val)
    {K : Type*} [CommMonoid K] (f : Finset V → K) :
    (∏ C ∈ ladderCells M, f C) =
      ∏ S : {S // S ∈ sourceMaximalLadders M},
        ∏ i : Fin (m S), f (ladderStepAtoms (u S) (v S) i) := by
  classical
  let I := Σ S : {S // S ∈ sourceMaximalLadders M}, Fin (m S)
  let g : I → {C // C ∈ ladderCells M} := fun t =>
    ⟨ladderStepAtoms (u t.1) (v t.1) t.2,by
      have hc := isLadderCell_step M (hrep t.1).1 t.2
      exact mem_filter.mpr ⟨mem_powerset.mpr (isLadderCell_subset_atoms M hc),hc⟩⟩
  have hginj : Function.Injective g := by
    rintro ⟨S,i⟩ ⟨T,j⟩ h
    have he := congrArg Subtype.val h
    change ladderStepAtoms (u S) (v S) i = ladderStepAtoms (u T) (v T) j at he
    have hST : S = T := by
      apply Subtype.ext
      by_contra hne
      have hd := sourceMaximalLadders_pairwiseDisjoint M hM S.property T.property hne
      have hSi := ladderStepAtoms_subset (u S) (v S) i
      have hTj := ladderStepAtoms_subset (u T) (v T) j
      rw [(hrep S).2] at hSi
      rw [(hrep T).2] at hTj
      have hx : u S i.castSucc ∈ ladderStepAtoms (u S) (v S) i := by
        simp [ladderStepAtoms]
      have hxT : u S i.castSucc ∈ ladderStepAtoms (u T) (v T) j := he ▸ hx
      exact disjoint_left.mp hd (hSi hx) (hTj hxT)
    subst T
    have hij := ladderStepAtoms_injective (hrep S).1.2.1 he
    subst j
    rfl
  have hgsurj : Function.Surjective g := by
    intro C
    have hc : IsLadderCell M C.val := (mem_filter.mp C.property).2
    obtain ⟨p,q,hcL,hcS⟩ := hc
    obtain ⟨S,hS,hCS⟩ := exists_sourceMaximalLadder_superset M
      (show SourceLadderSet M C.val from ⟨1,p,q,hcL,hcS⟩)
    let S' : {S // S ∈ sourceMaximalLadders M} := ⟨S,hS⟩
    have hsub : C.val ⊆ Molecule.ladderAtoms (u S') (v S') := (hrep S').2.symm ▸ hCS
    obtain ⟨i,hi⟩ := exists_step_eq_of_cell_subset M hM (hrep S').1 ⟨p,q,hcL,hcS⟩ hsub
    exact ⟨⟨S',i⟩,Subtype.ext hi.symm⟩
  let e := Equiv.ofBijective g ⟨hginj,hgsurj⟩
  calc
    _ = ∏ C : {C // C ∈ ladderCells M}, f C.val := (prod_coe_sort _ _).symm
    _ = ∏ t : I, f (g t).val :=
      (Fintype.prod_equiv e (fun t => f (g t).val) (fun C => f C.val) (fun _ => rfl)).symm
    _ = _ := Fintype.prod_sigma _

/-- DH23 L1831: the literal cell product is precisely the product of the
separate gap-scale factors over every position of every maximal ladder. -/
theorem cellProduct_eq_maximal_steps (M : Molecule V D) (hM : M.IsMolecule)
    (m : {S // S ∈ sourceMaximalLadders M} → ℕ)
    (u v : ∀ S : {S // S ∈ sourceMaximalLadders M}, Fin (m S+1) → V)
    (hrep : ∀ S, SourceLadder M (u S) (v S) ∧ Molecule.ladderAtoms (u S) (v S) = S.val)
    (L γ δ : ℝ) (P : Finset V → ℝ) :
    cellProduct M L γ δ P =
      ∏ S : {S // S ∈ sourceMaximalLadders M}, ∏ i : Fin (m S),
        Molecule.ladderWeight L γ δ (P (ladderStepAtoms (u S) (v S) i)) :=
  prod_ladderCells_eq_maximal_steps M hM m u v hrep _

end WaveTurbulence.MoleProp
