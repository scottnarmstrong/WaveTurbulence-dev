/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Op5a
/-! **FINALCOUNT-G3 (R29 item 4, ITER-ERASE / UNTOUCHED-ISO): isomorphisms of molecules fixing the atoms.**

`DartIso M M'` is a bijection `e` of the darts compatible with `atom`, `mate`, `out` (the atom types and atom sets agree).
All the combinatorial invariants of a molecule are `DartIso`-invariant: degrees, bonds, adjacency, components, circuit rank,
`bondsBetween`, `Directed`, ladders (`IsLadderSet`, `maximalLadders`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u₁ u₂ u₃
variable {V : Type u₁} [DecidableEq V] {D : Type u₂} [Fintype D] [DecidableEq D] {D' : Type u₃} [Fintype D'] [DecidableEq D']

/-- A bijection of the darts compatible with all the structure (atoms fixed). -/
structure DartIso (M : Molecule V D) (M' : Molecule V D') where
  e : D ≃ D'
  atoms : M'.atoms = M.atoms
  atom : ∀ x, M'.atom (e x) = M.atom x
  mate : ∀ x, M'.mate (e x) = e (M.mate x)
  out : ∀ x, M'.out (e x) = M.out x

namespace DartIso
variable {M : Molecule V D} {M' : Molecule V D'} (I : DartIso M M')
include I

/-- The inverse isomorphism. -/
def symm : DartIso M' M where
  e := I.e.symm
  atoms := I.atoms.symm
  atom := fun y => by
    have := I.atom (I.e.symm y); rw [Equiv.apply_symm_apply] at this; exact this.symm
  mate := fun y => by
    apply I.e.injective
    rw [Equiv.apply_symm_apply, ← I.mate, Equiv.apply_symm_apply]
  out := fun y => by
    have := I.out (I.e.symm y); rw [Equiv.apply_symm_apply] at this; exact this.symm

theorem dartsAt_map (v : V) : (M.dartsAt v).map I.e.toEmbedding = M'.dartsAt v := by
  ext y
  simp only [Finset.mem_map, Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨x, hx, rfl⟩; rw [I.atom]; exact hx
  · intro hy
    refine ⟨I.e.symm y, ?_, Equiv.apply_symm_apply _ _⟩
    have := I.atom (I.e.symm y); rw [Equiv.apply_symm_apply] at this; rw [← this]; exact hy

theorem deg_eq (v : V) : M'.deg v = M.deg v := by
  unfold Molecule.deg
  rw [← I.dartsAt_map v, Finset.card_map]

theorem outdeg_eq (v : V) : M'.outdeg v = M.outdeg v := by
  unfold Molecule.outdeg
  rw [← I.dartsAt_map v, Finset.filter_map, Finset.card_map]
  congr 1
  ext x; simp [I.out]

theorem indeg_eq (v : V) : M'.indeg v = M.indeg v := by
  unfold Molecule.indeg
  rw [← I.dartsAt_map v, Finset.filter_map, Finset.card_map]
  congr 1
  ext x; simp [I.out]

theorem adj_iff (a b : V) : M'.Adj a b ↔ M.Adj a b := by
  constructor
  · rintro ⟨y, h1, h2⟩
    refine ⟨I.e.symm y, ?_, ?_⟩
    · have := I.atom (I.e.symm y); rw [Equiv.apply_symm_apply] at this; rw [← this]; exact h1
    · have := I.atom (M.mate (I.e.symm y)); rw [← I.mate, Equiv.apply_symm_apply] at this; rw [← this]; exact h2
  · rintro ⟨x, h1, h2⟩
    exact ⟨I.e x, by rw [I.atom]; exact h1, by rw [I.mate, I.atom]; exact h2⟩

theorem sc_iff (a b : V) : M'.SameComponent a b ↔ M.SameComponent a b := by
  unfold Molecule.SameComponent
  have : M'.Adj = M.Adj := by funext a b; exact propext (I.adj_iff a b)
  rw [this]

theorem numComponents_eq : M'.numComponents = M.numComponents := by
  unfold Molecule.numComponents
  have h : ∀ (u v : M'.atoms), M'.Adj u.1 v.1 ↔ M.Adj u.1 v.1 := fun u v => I.adj_iff _ _
  let f : M'.atoms ≃ M.atoms := Equiv.subtypeEquivRight (fun a => by rw [I.atoms])
  refine Nat.card_congr (Quot.congr f ?_)
  intro a b
  simp only [f, Equiv.subtypeEquivRight_apply_coe]
  exact (I.adj_iff a.1 b.1)

theorem bonds_card_eq : M'.bonds.card = M.bonds.card := by
  unfold Molecule.bonds
  refine Finset.card_bij (fun y _ => I.e.symm y) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have := I.out (I.e.symm y); rw [Equiv.apply_symm_apply] at this; rw [← this]; exact hy
  · intro y _ y' _ e; exact I.e.symm.injective e
  · intro x hx
    refine ⟨I.e x, ?_, Equiv.symm_apply_apply _ _⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [I.out]; exact hx

theorem circuitRank_eq : M'.circuitRank = M.circuitRank := by
  unfold Molecule.circuitRank
  rw [I.bonds_card_eq, I.numComponents_eq, I.atoms]

theorem ends_eq (x : D) : M'.ends (I.e x) = M.ends x := by
  unfold Molecule.ends; rw [I.atom, I.mate, I.atom]

theorem bondsBetween_eq (a b : V) : M'.bondsBetween a b = M.bondsBetween a b := by
  unfold Molecule.bondsBetween Molecule.bonds
  refine Finset.card_bij (fun y _ => I.e.symm y) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have h1 := I.out (I.e.symm y); rw [Equiv.apply_symm_apply] at h1
    have h2 := I.ends_eq (I.e.symm y); rw [Equiv.apply_symm_apply] at h2
    exact ⟨h1 ▸ hy.1, h2 ▸ hy.2⟩
  · intro y _ y' _ e; exact I.e.symm.injective e
  · intro x hx
    refine ⟨I.e x, ?_, Equiv.symm_apply_apply _ _⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨by rw [I.out]; exact hx.1, by rw [I.ends_eq]; exact hx.2⟩

theorem directed_iff (a b : V) : M'.Directed a b ↔ M.Directed a b := by
  constructor
  · rintro ⟨y, h1, h2, h3⟩
    refine ⟨I.e.symm y, ?_, ?_, ?_⟩
    · have := I.out (I.e.symm y); rw [Equiv.apply_symm_apply] at this; rw [← this]; exact h1
    · have := I.atom (I.e.symm y); rw [Equiv.apply_symm_apply] at this; rw [← this]; exact h2
    · have := I.atom (M.mate (I.e.symm y)); rw [← I.mate, Equiv.apply_symm_apply] at this; rw [← this]; exact h3
  · rintro ⟨x, h1, h2, h3⟩
    exact ⟨I.e x, by rw [I.out]; exact h1, by rw [I.atom]; exact h2, by rw [I.mate, I.atom]; exact h3⟩

theorem isLadder_iff {m : ℕ} (u v : Fin (m + 1) → V) : M'.IsLadder u v ↔ M.IsLadder u v := by
  unfold Molecule.IsLadder
  simp only [I.atoms, I.bondsBetween_eq, I.directed_iff]

theorem isLadderSet_iff (S : Finset V) : M'.IsLadderSet S ↔ M.IsLadderSet S := by
  unfold Molecule.IsLadderSet
  simp only [I.isLadder_iff]

theorem maximalLadders_eq : M'.maximalLadders = M.maximalLadders := by
  unfold Molecule.maximalLadders
  simp only [I.atoms, I.isLadderSet_iff]


theorem dartSign_eq (x : D) : M'.dartSign (I.e x) = M.dartSign x := by
  unfold Molecule.dartSign; rw [I.out]

section dec
variable {d : ℕ}

theorem isDecoration_iff (L : ℝ) (w : Mom d) (c : V → Mom d) (κ' : D' → (Fin d → ℤ)) :
    M'.IsDecoration L w c κ' ↔ M.IsDecoration L w c (fun x => κ' (I.e x)) := by
  unfold Molecule.IsDecoration
  rw [I.atoms]
  have h1 : (∀ y, κ' (M'.mate y) = κ' y) ↔ ∀ x, κ' (I.e (M.mate x)) = κ' (I.e x) := by
    constructor
    · intro h x; rw [← I.mate]; exact h _
    · intro h y
      have := h (I.e.symm y)
      rw [Equiv.apply_symm_apply, ← I.mate, Equiv.apply_symm_apply] at this
      exact this
  have h2 : ∀ v, ∑ y ∈ M'.dartsAt v, M'.dartSign y • Molecule.kvec L w κ' y =
      ∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L w (fun x => κ' (I.e x)) x := by
    intro v
    rw [← I.dartsAt_map v, Finset.sum_map]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.coe_toEmbedding, I.dartSign_eq, Molecule.kvec]
  simp only [h1, h2]

theorem gamma_eq (L : ℝ) (w : Mom d) (κ' : D' → (Fin d → ℤ)) (v : V) :
    M'.Gamma L w κ' v = M.Gamma L w (fun x => κ' (I.e x)) v := by
  unfold Molecule.Gamma
  rw [← I.dartsAt_map v, Finset.sum_map]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Equiv.coe_toEmbedding, I.dartSign_eq, Molecule.kvec]

theorem isRestricted_iff (L γ δ : ℝ) (w : Mom d) (β : V → ℝ) (k0 : D' → Mom d) (κ' : D' → (Fin d → ℤ)) :
    M'.IsRestricted L γ δ w β k0 κ' ↔ M.IsRestricted L γ δ w β (fun x => k0 (I.e x)) (fun x => κ' (I.e x)) := by
  unfold Molecule.IsRestricted
  rw [I.atoms]
  simp only [I.gamma_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun x => h2 (I.e x)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun y => ?_⟩
    have := h2 (I.e.symm y)
    simp only [Molecule.kvec, Equiv.apply_symm_apply] at this ⊢
    exact this

theorem countE_le (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (D' → (Fin d → ℤ)) → Prop) (hA : ∀ κ', Adm' κ' ↔ Adm (fun x => κ' (I.e x))) :
    M.countE L γ δ w Adm ≤ M'.countE L γ δ w Adm' := by
  unfold Molecule.countE
  refine iSup_le fun c => iSup_le fun hc => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk => ?_
  refine le_iSup_of_le c (le_iSup_of_le ?_ (le_iSup_of_le β (le_iSup_of_le (fun y => k0 (I.e.symm y))
    (le_iSup_of_le ?_ ?_))))
  · intro v hv h4
    rw [I.atoms] at hv
    exact hc v hv (by rw [← I.deg_eq]; exact h4)
  · intro y
    have h : M.mate (I.e.symm y) = I.e.symm (M'.mate y) := I.symm.mate y
    show k0 (I.e.symm (M'.mate y)) = k0 (I.e.symm y)
    rw [← h]; exact hk _
  · set f : (D → (Fin d → ℤ)) → (D' → (Fin d → ℤ)) := fun κ y => κ (I.e.symm y) with hf
    have hinj : Function.Injective f := by
      intro κ κ' h
      funext x
      have := congrFun h (I.e x)
      simpa [hf] using this
    rw [← hinj.encard_image]
    refine Set.encard_le_encard ?_
    rintro _ ⟨κ, ⟨h1, h2, h3⟩, rfl⟩
    have e1 : (fun x => f κ (I.e x)) = κ := by funext x; simp [hf]
    refine ⟨?_, ?_, ?_⟩
    · rw [I.isDecoration_iff, e1]; exact h1
    · rw [I.isRestricted_iff, e1]
      simpa using h2
    · rw [hA, e1]; exact h3

theorem countE_eq (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (D' → (Fin d → ℤ)) → Prop) (hA : ∀ κ', Adm' κ' ↔ Adm (fun x => κ' (I.e x))) :
    M.countE L γ δ w Adm = M'.countE L γ δ w Adm' := by
  refine le_antisymm (I.countE_le L γ δ w Adm Adm' hA) ?_
  refine I.symm.countE_le L γ δ w Adm' Adm fun κ => ?_
  have := hA (fun y => κ (I.e.symm y))
  simp only [Equiv.symm_apply_apply] at this
  exact this.symm

theorem countA_eq (L γ δ C₁ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (D' → (Fin d → ℤ)) → Prop) (hA : ∀ κ', Adm' κ' ↔ Adm (fun x => κ' (I.e x))) (P : Finset V → ℝ) :
    M.countA L γ δ C₁ w Adm P = M'.countA L γ δ C₁ w Adm' P := by
  unfold Molecule.countA
  rw [I.countE_eq L γ δ w Adm Adm' hA, I.circuitRank_eq, I.maximalLadders_eq]

end dec
end DartIso

/-- **ITER-ERASE** (core): erasing `K₁` and then `K₂` is the same molecule as erasing `K₁ ∪ K₂`. -/
def iterIso (M : Molecule V D) (K₁ K₂ : Finset V) :
    DartIso (eraseSet (eraseSet M K₁) K₂) (eraseSet M (K₁ ∪ K₂)) where
  e :=
    { toFun := fun x => ⟨x.1.1, by
        have := x.1.2; have h2 := x.2
        simp only [Finset.mem_union, not_or]
        exact ⟨⟨this.1, h2.1⟩, ⟨this.2, h2.2⟩⟩⟩
      invFun := fun y => ⟨⟨y.1, by
          have := y.2; simp only [Finset.mem_union, not_or] at this
          exact ⟨this.1.1, this.2.1⟩⟩, by
          have := y.2; simp only [Finset.mem_union, not_or] at this
          exact ⟨this.1.2, this.2.2⟩⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  atoms := by
    show M.atoms \ (K₁ ∪ K₂) = (M.atoms \ K₁) \ K₂
    ext a; simp [and_assoc]
  atom := fun x => rfl
  mate := fun x => rfl
  out := fun x => rfl

end WaveTurbulence.FinalCountG3
