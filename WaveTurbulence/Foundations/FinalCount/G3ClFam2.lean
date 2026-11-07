/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3ClFam1
/-! **FINALCOUNT-G3 (R29 item 4, chain combinator, part 2): the family data and the one-step transfer.**
`FamData M 𝒦` (structure of a family of clusters), `FamTame M 𝒦 Adm` (tameness / fixed labels), `FamLad` (the ladder ratio `O3`, for
every sub-union of the family); `.step` transfers each of them from `M` to `M - K` for `K ∈ 𝒦` and the family `𝒦 \ {K}`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u v
variable {V : Type u} [DecidableEq V] {D : Type v} [Fintype D] [DecidableEq D] {d : ℕ}

/-- Structure of a family of connected clusters of a molecule of degree `≤ 4`. -/
structure FamData (M : Molecule V D) (𝒦 : Finset (Finset V)) : Prop where
  cl : Clusters M 𝒦
  nl : ∀ x, M.atom x ≠ M.atom (M.mate x)
  m4 : ∀ a ∈ M.atoms, M.deg a ≤ 4
  sub : ∀ K ∈ 𝒦, K ⊆ M.atoms
  ne : ∀ K ∈ 𝒦, K.Nonempty
  dpos : ∀ K ∈ 𝒦, ∀ a ∈ K, 1 ≤ M.deg a
  int : ∀ K ∈ 𝒦, ∀ a ∈ K, ∀ b ∈ K, (eraseSet M (M.atoms \ K)).SameComponent a b

/-- Tameness of the clusters of the family and fixed labels of atoms of degree `< 4` (`hfix`, subpro (3)). -/
def FamTame (M : Molecule V D) (𝒦 : Finset (Finset V)) (Adm : (D → (Fin d → ℤ)) → Prop) : Prop :=
  ∀ K ∈ 𝒦, (∀ κ, Adm κ → TameLabelsS M K κ) ∧
    (∀ a ∈ K, M.deg a < 4 → ∃ k, ∀ κ, Adm κ → ∀ x ∈ M.dartsAt a, κ x = k)

/-- The ladder-weight product over a set of ladders. -/
noncomputable def ladProd (L γ δ : ℝ) (P : Finset V → ℝ) (S : Finset (Finset V)) : ℝ :=
  ∏ S' ∈ S, Molecule.ladderWeight L γ δ (P S') ^ Molecule.ladderLength S'

/-- **O3 for a family**: erasing `K ∈ 𝒦` from `M - ⋃𝒜` (any `𝒜 ⊆ 𝒦 \ {K}`) costs at most `(log L)^{c₀(|K| + e_K)}`. -/
def FamLad (L γ δ : ℝ) (P : Finset V → ℝ) (c₀ : ℕ) (M : Molecule V D) (𝒦 : Finset (Finset V)) : Prop :=
  ∀ 𝒜 ⊆ 𝒦, ∀ K ∈ 𝒦, K ∉ 𝒜 →
    ladProd L γ δ P (eraseSet M (𝒜.biUnion id)).maximalLadders ≤
      Real.log L ^ (c₀ * (K.card + eDart M K)) * ladProd L γ δ P (eraseSet M (𝒜.biUnion id ∪ K)).maximalLadders

/-- Erasing the empty set is an isomorphism. -/
def emptyIso (M : Molecule V D) : DartIso M (eraseSet M ∅) where
  e := { toFun := fun x => ⟨x, by simp, by simp⟩, invFun := fun y => y.1, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  atoms := by show M.atoms \ ∅ = M.atoms; simp
  atom := fun _ => rfl
  mate := fun _ => rfl
  out := fun _ => rfl

theorem resAdm_empty (Adm : (D → (Fin d → ℤ)) → Prop) (M : Molecule V D) (κ' : EDartS M ∅ → (Fin d → ℤ)) :
    resAdm Adm M ∅ κ' ↔ Adm (fun x => κ' ((emptyIso M).e x)) := by
  constructor
  · rintro ⟨κ, hκ, hk⟩
    have : (fun x => κ' ((emptyIso M).e x)) = κ := funext fun x => hk _
    rw [this]; exact hκ
  · intro h
    exact ⟨_, h, fun x => rfl⟩

section step
variable {M : Molecule V D} {K : Finset V} {𝒦 : Finset (Finset V)}

theorem FamData.nb (h : FamData M 𝒦) {K K' : Finset V} (hK : K ∈ 𝒦) (hK' : K' ∈ 𝒦) (hne : K ≠ K') :
    ∀ x, M.atom x ∈ K → M.atom (M.mate x) ∉ K' := h.cl.nobond K hK K' hK' hne

theorem FamData.step (h : FamData M (insert K 𝒦)) (hK : K ∉ 𝒦) : FamData (eraseSet M K) 𝒦 where
  cl := by
    refine ⟨fun A hA B hB hne => h.cl.disj A (Finset.mem_insert_of_mem hA) B (Finset.mem_insert_of_mem hB) hne,
      fun A hA B hB hne x hx => ?_⟩
    exact h.cl.nobond A (Finset.mem_insert_of_mem hA) B (Finset.mem_insert_of_mem hB) hne x.1 hx
  nl := fun x => h.nl x.1
  m4 := fun a ha => le_trans (deg_erase_le (Finset.mem_sdiff.1 ha).2) (h.m4 a (Finset.mem_sdiff.1 ha).1)
  sub := by
    intro A hA a ha
    have hne : K ≠ A := fun e => hK (e ▸ hA)
    exact Finset.mem_sdiff.2 ⟨h.sub A (Finset.mem_insert_of_mem hA) ha,
      Finset.disjoint_left.1 (h.cl.disj K (Finset.mem_insert_self _ _) A (Finset.mem_insert_of_mem hA) hne).symm ha⟩
  ne := fun A hA => h.ne A (Finset.mem_insert_of_mem hA)
  dpos := by
    intro A hA a ha
    have hne : K ≠ A := fun e => hK (e ▸ hA)
    have hnb : ∀ x, M.atom x ∈ A → M.atom (M.mate x) ∉ K :=
      h.cl.nobond A (Finset.mem_insert_of_mem hA) K (Finset.mem_insert_self _ _) hne.symm
    rw [deg_erase_eq hnb (h.cl.disj A (Finset.mem_insert_of_mem hA) K (Finset.mem_insert_self _ _) hne.symm) ha]
    exact h.dpos A (Finset.mem_insert_of_mem hA) a ha
  int := by
    intro A hA a ha b hb
    have hne : K ≠ A := fun e => hK (e ▸ hA)
    exact induced_transfer (h.cl.disj A (Finset.mem_insert_of_mem hA) K (Finset.mem_insert_self _ _) hne.symm)
      (h.int A (Finset.mem_insert_of_mem hA) a ha b hb)

theorem FamTame.step {Adm : (D → (Fin d → ℤ)) → Prop} (hd : FamData M (insert K 𝒦)) (hK : K ∉ 𝒦)
    (h : FamTame M (insert K 𝒦) Adm) : FamTame (eraseSet M K) 𝒦 (resAdm Adm M K) := by
  intro A hA
  have hne : K ≠ A := fun e => hK (e ▸ hA)
  have hnb : ∀ x, M.atom x ∈ A → M.atom (M.mate x) ∉ K :=
    hd.cl.nobond A (Finset.mem_insert_of_mem hA) K (Finset.mem_insert_self _ _) hne.symm
  have hdis := hd.cl.disj A (Finset.mem_insert_of_mem hA) K (Finset.mem_insert_self _ _) hne.symm
  obtain ⟨ht, hf⟩ := h A (Finset.mem_insert_of_mem hA)
  refine ⟨?_, ?_⟩
  · rintro κ₁ ⟨κ, hκ, hk⟩ x y hx hy
    rw [hk, hk]
    exact ht κ hκ x.1 y.1 hx hy
  · intro a ha hlt
    rw [deg_erase_eq hnb hdis ha] at hlt
    obtain ⟨k, hk⟩ := hf a ha hlt
    refine ⟨k, ?_⟩
    rintro κ₁ ⟨κ, hκ, hk1⟩ x hx
    rw [hk1]
    refine hk κ hκ x.1 ?_
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx

theorem maximalLadders_eraseSet_empty (M : Molecule V D) : (eraseSet M ∅).maximalLadders = M.maximalLadders :=
  (emptyIso M).maximalLadders_eq

theorem FamLad.step {L γ δ : ℝ} {P : Finset V → ℝ} {c₀ : ℕ} (hd : FamData M (insert K 𝒦)) (hK : K ∉ 𝒦)
    (h : FamLad L γ δ P c₀ M (insert K 𝒦)) : FamLad L γ δ P c₀ (eraseSet M K) 𝒦 := by
  intro 𝒜 h𝒜 A hA hAn
  have hne : K ≠ A := fun e => hK (e ▸ hA)
  have hnb : ∀ x, M.atom x ∈ A → M.atom (M.mate x) ∉ K :=
    hd.cl.nobond A (Finset.mem_insert_of_mem hA) K (Finset.mem_insert_self _ _) hne.symm
  have hdis := hd.cl.disj A (Finset.mem_insert_of_mem hA) K (Finset.mem_insert_self _ _) hne.symm
  have hKA : K ∉ 𝒜 := fun e => hK (h𝒜 e)
  have h1 := h (insert K 𝒜) (Finset.insert_subset_insert _ h𝒜) A (Finset.mem_insert_of_mem hA)
    (by simp [Finset.mem_insert, hAn, hne.symm])
  rw [eDart_erase_eq hnb hdis]
  have e1 : (eraseSet (eraseSet M K) (𝒜.biUnion id)).maximalLadders =
      (eraseSet M ((insert K 𝒜).biUnion id)).maximalLadders := by
    rw [Finset.biUnion_insert]; exact (iterIso M K (𝒜.biUnion id)).maximalLadders_eq.symm
  have e2 : (eraseSet (eraseSet M K) (𝒜.biUnion id ∪ A)).maximalLadders =
      (eraseSet M ((insert K 𝒜).biUnion id ∪ A)).maximalLadders := by
    rw [Finset.biUnion_insert, Finset.union_assoc]; exact (iterIso M K (𝒜.biUnion id ∪ A)).maximalLadders_eq.symm
  rw [e1, e2]; exact h1

end step
end WaveTurbulence.FinalCountG3
