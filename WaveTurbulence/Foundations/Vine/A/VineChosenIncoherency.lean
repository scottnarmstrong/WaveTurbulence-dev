/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineRealizationMap
/-! The actual chosen vine incoherency index is independent of template,
ordered-joint choices and actual molecular relabeling. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Vine
variable {w : ℕ} {G H : Garden w}

/-- Realizations on the same actual atom set have equal indices, including swapped ordered joints. -/
theorem realized_index_eq_of_atoms {X Y : VineType} {S : Finset (GBranch G.tree)}
    {a b c d : GBranch G.tree} (R : VineRealization G.molecule X S a b)
    (T : VineRealization G.molecule Y S c d) (hB : G.molecule.IsBlock S a b)
    (hC : G.molecule.IsBlock S c d) (layer : GBranch G.tree → ℕ) :
    realizedIncoherencyIndex R layer = realizedIncoherencyIndex T layer := by
  have hj := Vine.block_joints_unique G.molecule hB hC
  have hf : ({T.f a, T.f b} : Finset ℕ) = {0, 1} := by
    have h := congrArg (Finset.image T.f) hj
    simp only [Finset.image_insert, Finset.image_singleton] at h
    exact h.trans T.joints_eq
  let T' : VineRealization G.molecule Y S a b :=
    ⟨T.k, T.length_eq, T.f, T.injOn, T.image_eq, hf, T.bonds_eq⟩
  exact realizedIncoherencyIndex_eq G.molecule (Mole.garden_isMolecule G) R T' hB layer

/-- The actual chosen index in RedSpliceData transports under an actual molecule isomorphism. -/
theorem vineIncoh_image (F : MolIso G.molecule H.molecule) (layer : GBranch H.tree → ℕ)
    (S : Finset (GBranch G.tree)) : vineIncoh H layer (F.img S) = vineIncoh G (layer ∘ F.e) S := by
  classical
  by_cases h : ∃ X a b, G.molecule.IsVine X S a b
  · have ht : ∃ X a b, H.molecule.IsVine X (F.img S) a b := by
      obtain ⟨X, a, b, hv⟩ := h
      exact ⟨X, F.e a, F.e b, F.isVine_img hv⟩
    let hv := h.choose_spec.choose_spec.choose_spec
    let hvt := ht.choose_spec.choose_spec.choose_spec
    let R := Classical.choice (Vine.isVine_iff_realization.mp hv).2
    let T := Classical.choice (Vine.isVine_iff_realization.mp hvt).2
    have he := realized_index_eq_of_atoms (mapVineRealization F R) T (F.isBlock_img hv.1) hvt.1 layer
    unfold vineIncoh
    rw [dite_eq_left ht, dite_eq_left h]
    exact he.symm.trans (mapVineRealization_index F R layer)
  · have ht : ¬ ∃ X a b, H.molecule.IsVine X (F.img S) a b := by
      rintro ⟨X, a, b, hv⟩
      have hg := F.symm.isVine_img hv
      rw [F.img_img_symm] at hg
      exact h ⟨X, F.symm.e a, F.symm.e b, hg⟩
    unfold vineIncoh
    rw [dite_eq_right ht, dite_eq_right h]

end WaveTurbulence.VineA
