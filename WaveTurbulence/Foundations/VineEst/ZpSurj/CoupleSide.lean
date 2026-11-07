/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.GraftT
public import WaveTurbulence.Foundations.Molecule.LFTwist.IdentityConstruction

/-! # ZP-SURJ: the garden-level outside agreement of a couple reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

/-- A garden with the zero layering. -/
@[expose] def zeroLayered (G : Garden w) : LayeredGarden w :=
  ⟨G, fun _ => 0, ⟨fun _ _ => le_refl _, fun _ => rfl⟩⟩

theorem not_below_of_not_under {a z : Fin w × Path} (h : ¬ Under a z) : ¬ Below a z :=
  fun h' => h ⟨h'.1.symm, h'.2⟩

theorem gout_couple {S : Garden w} (hS : S.IsPlain) (D0 : ReconstructionData S) {B : Garden w}
    (hB : D0.Decodes hS B) (π : SourcePair S) (htriv : D0.couple π = .triv) (Q : RegCpl) (hQ : Q.wf = true) :
    GOut B ((D0.withCouple π Q hQ).garden hS)
      (inflatedPosition S D0.tree (π.firstLeaf hS).toNode) (inflatedPosition S D0.tree (π.secondLeaf hS).toNode) := by
  have hBg : B = D0.garden hS := rawOfGarden_injective_plain hB.1 (D0.garden_plain hS)
    (hB.2.symm.trans (D0.garden_raw hS).symm)
  by_cases hQt : Q = .triv
  · subst hQt
    have hM : D0.withCouple π .triv hQ = D0 := D0.eraseCouple_eq_self π htriv
    rw [hM, hBg]
    exact ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun ℓ ℓ' _ he => by rw [Subtype.ext he]⟩
  · set M := D0.withCouple π Q hQ with hMdef
    have hMc : M.couple π = Q := Function.update_self _ _ _
    have hMn : M.couple π ≠ .triv := by rw [hMc]; exact hQt
    let LGz := zeroLayered (M.garden hS)
    have h : Comb.IsSubCouple LGz.garden (M.decodedNode hS (M.garden_decodes hS) (π.firstLeaf hS).toNode)
        (M.decodedNode hS (M.garden_decodes hS) (π.secondLeaf hS).toNode) :=
      M.decoded_couple_isSubCouple hS (M.garden_decodes hS) π
    have hdec := M.eraseCouple_collapse_decodes hS (M.garden_decodes hS) π hMn
    have hE : M.eraseCouple π = D0 := by
      apply ReconstructionData.ext_tree_couple
      · rfl
      · change Function.update (Function.update D0.couple π Q) π .triv = D0.couple
        rw [Function.update_idem, ← htriv]
        exact Function.update_eq_self _ _
    rw [hE] at hdec
    have hBc : B = collapseCoupleGarden h := rawOfGarden_injective_plain hB.1 hdec.1 (hB.2.symm.trans hdec.2)
    subst hBc
    refine ⟨fun z hz => ?_, fun z hz => ?_, fun ℓ ℓ' hz he => ?_⟩
    · exact coupleCollapse_node_outside LGz h z (not_below_of_not_under (fun h' => hz (Or.inl h')))
        (not_below_of_not_under (fun h' => hz (Or.inr h')))
    · exact coupleCollapse_leaf_outside LGz h z (not_below_of_not_under (fun h' => hz (Or.inl h')))
        (not_below_of_not_under (fun h' => hz (Or.inr h')))
    · exact (coupleCollapse_pair_outside LGz h ℓ' ℓ
        (not_below_of_not_under (fun h' => hz (by rw [he]; exact Or.inl h')))
        (not_below_of_not_under (fun h' => hz (by rw [he]; exact Or.inr h'))) he.symm).symm

end WaveTurbulence.ZpSurj
