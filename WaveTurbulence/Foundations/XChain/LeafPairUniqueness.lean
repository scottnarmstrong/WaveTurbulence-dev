/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LeafPairConstruction
public import WaveTurbulence.Foundations.XChain.GardenDataExt
/-! There is exactly one plain zero-order two-root component for any admissible signature. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem leafPair_pair_root_ne (G : Garden 2) (ht : ∀ j, G.tree j = TTree.leaf) (hplain : G.IsPlain)
    (l : GLeaf G.tree) : (G.pair l).1.1 ≠ l.1.1 := by
  intro he
  have hp : G.pair l = l := (leafForestLeafEquiv G.tree ht).injective he
  exact ((G.pair_eq_iff l).mp hp) (hplain l)

theorem leafPair_pair_raw_eq (G H : Garden 2) (htG : ∀ j, G.tree j = TTree.leaf)
    (htH : ∀ j, H.tree j = TTree.leaf) (hG : G.IsPlain) (hH : H.IsPlain)
    (a : GLeaf G.tree) (b : GLeaf H.tree) (hab : a.1 = b.1) : (G.pair a).1 = (H.pair b).1 := by
  have hr := congrArg (fun z : Fin 2 × TTree.Path => z.1.val) hab
  have hnG : (G.pair a).1.1.val ≠ a.1.1.val :=
    fun h => leafPair_pair_root_ne G htG hG a (Fin.ext h)
  have hnH : (H.pair b).1.1.val ≠ b.1.1.val :=
    fun h => leafPair_pair_root_ne H htH hH b (Fin.ext h)
  have hroot : (G.pair a).1.1 = (H.pair b).1.1 := by
    apply Fin.ext
    have h0 := a.1.1.isLt
    have h1 := b.1.1.isLt
    have h2 := (G.pair a).1.1.isLt
    have h3 := (H.pair b).1.1.isLt
    omega
  have hpG := (G.pair a).2
  have hpH := (H.pair b).2
  rw [htG (G.pair a).1.1, TTree.leaves, mem_singleton] at hpG
  rw [htH (H.pair b).1.1, TTree.leaves, mem_singleton] at hpH
  exact Prod.ext hroot (hpG.trans hpH.symm)

theorem LowerGraftData.leafPair {p N : ℕ} {sig : Fin 2 → ℤˣ} (D : LowerGraftData sig p N) :
    (∀ j, D.low.garden.tree j = TTree.leaf) ∧ ∀ a, D.low.layer a = p := by
  rcases D.component with h | h
  · have hw := isCanonG_width h
    omega
  · exact h.2

instance {p N : ℕ} {sig : Fin 2 → ℤˣ} : Subsingleton (LowerGraftData sig p N) := by
  refine ⟨fun D E => LowerGraftData.low_injective ?_⟩
  apply layeredGarden_eq_of_raw_data
  · apply garden_eq_of_raw_data D.low.garden E.low.garden (D.sign.trans E.sign.symm)
      (funext (fun j => (D.leafPair.1 j).trans (E.leafPair.1 j).symm))
    · exact leafPair_pair_raw_eq _ _ D.leafPair.1 E.leafPair.1 D.plain E.plain
    · intro a b _
      exact (D.plain a).trans (E.plain b).symm
  · intro a b _
    exact (D.leafPair.2 a).trans (E.leafPair.2 b).symm

end WaveTurbulence.Induct
