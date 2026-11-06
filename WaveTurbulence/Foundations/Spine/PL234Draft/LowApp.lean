/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.SliceAlgebra

/-!
# The lower leading terms of TARGET (prooflayer1-1)

For a coherent couple `type2 Xp Xm Qlp` whose `-` side lies in layer `q'`, the explicit leading term is a product
of the single-layer leading terms of the same-layer slices of the `+` chain and of the bottom couple. For a
suffix `X` of the `+` chain, rooted at `(0, π)`:

* `lowSlices`: `∏_{q' < r ≤ top} 𝒜_{slice r}(r+1, r)`;
* `lowBot`: `𝒜_{bottom}(q'+1, s)`, the bottom couple `closeCouple (slice q') Xm Qlp`;
* **`lowApp_split`**: removing the top block `B` (layer `u`) leaves `𝒜_B(u+1, u) · lowApp(π ++ B.lp, D)`, the empty
  slices between the layers contributing `1`.
-/

@[expose] public section

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

variable {d : ℕ}

section Low

variable (δ : ℝ) (LG : LayeredGarden 2) (H : LeafProfiles 2 d) (Xm : RegChain) (Qlp : RegCpl) (q' : ℕ)

/-- One slice factor at `(r+1, r)`. -/
noncomputable def sliceFactor (π : Path) (X : RegChain) (r : ℕ) (k : Mom d) : ℂ :=
  LeafApp.tree δ r (LeafApp.sliceProfiles LG H (0, π) r X) (SourceApp.chainSlice LG (0, π) r X) 1
    (r + 1) r k

noncomputable def lowSlices (π : Path) (X : RegChain) (k : Mom d) : ℂ :=
  ∏ r ∈ Ioo q' (layerAt LG (0, π) + 1), sliceFactor δ LG H π X r k

/-- The transported profiles of the bottom couple. -/
noncomputable def botProf (π : Path) (X : RegChain) : LeafProfiles 2 d :=
  fun z => if z.1 = 0 then H (LeafApp.sliceAddress LG (0, π) q' X z.2) else H z

noncomputable def lowBot (π : Path) (X : RegChain) (s : ℝ) (k : Mom d) : ℂ :=
  LeafApp.couple δ q' (botProf LG H q' π X)
    (SourceApp.closeCouple (SourceApp.chainSlice LG (0, π) q' X) Xm Qlp) (q' + 1) s k

noncomputable def lowApp (π : Path) (X : RegChain) (s : ℝ) (k : Mom d) : ℂ :=
  lowSlices δ LG H q' π X k * lowBot δ LG H Xm Qlp q' π X s k

end Low

theorem topNe_of_topAll (LG : LayeredGarden 2) {u r : ℕ} (h : r ≠ u) :
    ∀ (a : Fin 2 × Path) (B : RegChain), TopAll LG u a B → TopNe LG r a B
  | _, .nil, _ => trivial
  | a, .pair m _ _ inner rest, ⟨ha, hT⟩ => ⟨by rw [ha]; exact Ne.symm h, topNe_of_topAll LG h _ rest hT⟩

theorem Ioo_eq_Ico_succ (a b : ℕ) : Ioo a b = Ico (a + 1) b := by
  ext x
  simp only [mem_Ioo, mem_Ico]
  omega

/-- **Removing the top block** from the lower leading term. -/
theorem lowApp_split (δ : ℝ) (LG : LayeredGarden 2) (H : LeafProfiles 2 d) (Xm : RegChain) (Qlp : RegCpl)
    {q' u : ℕ} (π : Path) (X : RegChain) (hu : layerAt LG (0, π) = u) (hq : q' < u)
    (_hX : X ≠ .nil) (_hSM : SpineMono LG (0, π) X)
    (hD : SpineMono LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) (dropLayer LG (0, π) u X))
    (hlow : q' ≤ layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath))
    (hlt : layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) < u) (s : ℝ) (k : Mom d) :
    lowApp δ LG H Xm Qlp q' π X s k =
      sliceFactor δ LG H π X u k *
        lowApp δ LG H Xm Qlp q' (π ++ (takeLayer LG (0, π) u X).lonePath) (dropLayer LG (0, π) u X) s k := by
  set B := takeLayer LG (0, π) u X with hB
  set D := dropLayer LG (0, π) u X with hDd
  set π' := π ++ B.lonePath with hπ'
  set r'' := layerAt LG (0, π') with hr''
  have hXe : appendChain B D = X := appendChain_take_drop LG (0, π) u X
  have haddr : addrExt ((0 : Fin 2), π) B.lonePath = ((0 : Fin 2), π') := rfl
  have hTA : TopAll LG u (0, π) B := topAll_takeLayer LG u _ X
  -- slices in layers `r ≠ u` are slices of `D` at `(0, π')`
  have hslice : ∀ r, r ≠ u → SourceApp.chainSlice LG (0, π) r X = SourceApp.chainSlice LG (0, π') r D :=
    fun r hr => chainSlice_take_drop LG hr (0, π) X
  have haddr' : ∀ r, r ≠ u → ∀ path, LeafApp.sliceAddress LG (0, π) r X path =
      LeafApp.sliceAddress LG (0, π') r D path := fun r hr path => by
    conv_lhs => rw [← hXe]
    exact sliceAddress_append_skip LG r B D (0, π) path (topNe_of_topAll LG hr _ B hTA)
  have hfac : ∀ r, r ≠ u → sliceFactor δ LG H π X r k = sliceFactor δ LG H π' D r k := fun r hr => by
    unfold sliceFactor LeafApp.sliceProfiles
    rw [hslice r hr]
    congr 2
    funext z
    rw [haddr' r hr]
  -- the empty slices above `r''`
  have hnil : ∀ r, r'' < r → sliceFactor δ LG H π' D r k = 1 := fun r hr => by
    unfold sliceFactor
    rw [chainSlice_eq_nil LG (0, π') D hD fun _ => hr]
    exact LeafApp.tree_nil _ _ _ _ _ _ _
  unfold lowApp lowSlices
  rw [hu, Ioo_eq_Ico_succ, prod_Ico_succ_top (by omega)]
  have hprod : ∏ r ∈ Ico (q' + 1) u, sliceFactor δ LG H π X r k =
      ∏ r ∈ Ioo q' (r'' + 1), sliceFactor δ LG H π' D r k := by
    rw [Finset.prod_congr rfl fun r hr => hfac r (by simp only [mem_Ico] at hr; omega),
      Ioo_eq_Ico_succ, ← prod_Ico_consecutive _ (show q' + 1 ≤ r'' + 1 by omega)
      (show r'' + 1 ≤ u by omega),
      Finset.prod_eq_one (s := Ico (r'' + 1) u) fun r hr => hnil r (by simp only [mem_Ico] at hr; omega),
      mul_one]
  have hbot : lowBot δ LG H Xm Qlp q' π X s k = lowBot δ LG H Xm Qlp q' π' D s k := by
    unfold lowBot botProf
    rw [hslice q' (by omega)]
    congr 2
    funext z
    split_ifs
    · rw [haddr' q' (by omega)]
    · rfl
  rw [hprod, hbot]
  ring

end WaveTurbulence.PL234
