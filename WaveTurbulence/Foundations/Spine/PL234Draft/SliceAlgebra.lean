/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.ChainFacts

/-!
# Slices of single-layer blocks, sizes and well-formedness of the pieces

* `sliceAddress_of_topAll`, `takeLayer_of_topAll`, `chainSlice_of_topAll`: a chain all of whose pairs are in layer
  `r` is its own `r`-slice, with the identity address transport;
* `sliceAddress_append_of_not_prefix`: through a block in layer `r`, every path off the block's lone path keeps
  its address;
* `size_even_cpl`, `size_even_chain`: code sizes are even;
* `closeCouple_size`, `closeCouple_wf`, `wf_split`: the two pieces of the block split.
-/

@[expose] public section
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

variable {w : ℕ}

theorem sliceAddress_of_topAll (LG : LayeredGarden w) (r : ℕ) :
    ∀ (X : RegChain) (a : Fin w × Path) (path : Path), TopAll LG r a X →
      LeafApp.sliceAddress LG a r X path = addrExt a path
  | .nil, _, _, _ => rfl
  | .pair m Qr Qg inner rest, a, path, ⟨ha, hT⟩ => by
    rw [sliceAddress_pair, ite_eq_left ha]
    split_ifs with hp
    · rw [sliceAddress_of_topAll LG r rest _ _ hT]
      obtain ⟨u, hu⟩ := hp
      show addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) _ = addrExt a path
      rw [addrExt_append, ← hu, List.drop_left]
    · rfl

theorem takeLayer_of_topAll (LG : LayeredGarden w) (r : ℕ) :
    ∀ (X : RegChain) (a : Fin w × Path), TopAll LG r a X → takeLayer LG a r X = X
  | .nil, _, _ => rfl
  | .pair m Qr Qg inner rest, a, ⟨ha, hT⟩ => by
    unfold takeLayer
    rw [ite_eq_left ha, takeLayer_of_topAll LG r rest _ hT]

theorem chainSlice_of_topAll (LG : LayeredGarden w) (r : ℕ) :
    ∀ (X : RegChain) (a : Fin w × Path), TopAll LG r a X → SourceApp.chainSlice LG a r X = X
  | .nil, _, _ => rfl
  | .pair m Qr Qg inner rest, a, ⟨ha, hT⟩ => by
    rw [chainSlice_pair, ite_eq_left ha, chainSlice_of_topAll LG r rest _ hT]

theorem sliceAddress_append_of_not_prefix (LG : LayeredGarden w) (r : ℕ) (D : RegChain) :
    ∀ (B : RegChain) (a : Fin w × Path) (path : Path), TopAll LG r a B → ¬ B.lonePath <+: path →
      LeafApp.sliceAddress LG a r (appendChain B D) path = addrExt a path
  | .nil, _, path, _, hp => absurd (List.nil_prefix) hp
  | .pair m Qr Qg inner rest, a, path, ⟨ha, hT⟩, hp => by
    show LeafApp.sliceAddress LG a r (.pair m Qr Qg inner (appendChain rest D)) path = _
    rw [sliceAddress_pair, ite_eq_left ha]
    split_ifs with hs
    · obtain ⟨u, hu⟩ := hs
      have hp' : ¬ rest.lonePath <+: path.drop ([m.c] ++ inner.lonePath ++ [m.lone]).length := by
        rintro ⟨v, hv⟩
        apply hp
        refine ⟨v, ?_⟩
        rw [← hu, List.drop_left] at hv
        rw [RegChain.lonePath, ← hu, ← hv]
        simp only [List.append_assoc]
      rw [sliceAddress_append_of_not_prefix LG r D rest _ _ hT hp']
      show addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) _ = addrExt a path
      rw [addrExt_append, ← hu, List.drop_left]
    · rfl

/-! ### Sizes and well-formedness -/

mutual
theorem size_even_cpl : (Q : RegCpl) → Even Q.size
  | .triv => ⟨0, rfl⟩
  | .type1 _ Q₁ Q₂ Q₃ => by
    simp only [RegCpl.size]
    exact (((size_even_cpl Q₁).add (size_even_cpl Q₂)).add (size_even_cpl Q₃)).add ⟨1, rfl⟩
  | .type2 Xp Xm Qlp => by
    simp only [RegCpl.size]
    exact ((size_even_chain Xp).add (size_even_chain Xm)).add (size_even_cpl Qlp)
termination_by structural Q => Q

theorem size_even_chain : (X : RegChain) → Even X.size
  | .nil => ⟨0, rfl⟩
  | .pair _ Qr Qg inner rest => by
    simp only [RegChain.size]
    exact ((((size_even_cpl Qr).add (size_even_cpl Qg)).add (size_even_chain inner)).add
      (size_even_chain rest)).add ⟨1, rfl⟩
termination_by structural X => X
end

theorem closeCouple_size (X Xm : RegChain) (Qlp : RegCpl) :
    (SourceApp.closeCouple X Xm Qlp).size = X.size + Xm.size + Qlp.size := by
  unfold SourceApp.closeCouple
  split_ifs with h
  · simp only [Bool.and_eq_true] at h
    cases X <;> cases Xm <;> simp_all [RegChain.isNil, RegChain.size]
  · rfl

theorem closeCouple_wf {X Xm : RegChain} {Qlp : RegCpl} (hX : X.wf = true) (hm : Xm.wf = true)
    (hl : Qlp.wf = true) (ht : Qlp.isType2 = false) : (SourceApp.closeCouple X Xm Qlp).wf = true := by
  unfold SourceApp.closeCouple
  split_ifs with h
  · exact hl
  · simp only [RegCpl.wf, hX, hm, hl, ht, Bool.true_and, Bool.not_false, Bool.and_true]
    cases hx : X.isNil <;> cases hy : Xm.isNil <;> simp_all

theorem wf_split {B D Xm : RegChain} {Qlp : RegCpl}
    (hwf : (RegCpl.type2 (appendChain B D) Xm Qlp).wf = true) :
    B.wf = true ∧ (SourceApp.closeCouple D Xm Qlp).wf = true := by
  simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true', appendChain_wf] at hwf
  obtain ⟨⟨⟨⟨⟨hB, hD⟩, hm⟩, hl⟩, ht⟩, -⟩ := hwf
  exact ⟨hB, closeCouple_wf hD hm hl ht⟩

end WaveTurbulence.PL234
