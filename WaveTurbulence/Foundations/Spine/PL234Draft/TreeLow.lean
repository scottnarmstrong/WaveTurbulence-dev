/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.TreeCoh

/-!
# Prop 6.1, `q > q'`, trees: the lower leading term

For a suffix `X` of the chain of a coherent tree, rooted at `(0, π)` in layer `u`:

* `lowAppT π X s k = (∏_{q'<r≤u} 𝒜_r(r+1, r)) · 𝒜_{q'}(q'+1, s)`, the slices of `X` with the transported
  profiles (TARGET prooflayer1-2);
* `coherentTree_gt_eq`: the explicit leading term `LeafApp.coherentTree` for `q' < q` in this notation;
* `lowAppT_split`, `lowRestT_eq`: removing the top block;
* `lowAppT_base`: a single block in layer `u ≥ q'` is the single-layer leading term at `(u+1, s)`.
-/

@[expose] public section

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

variable {d : ℕ}

section LowT

variable (δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d) (q' : ℕ)

/-- One tree slice factor at `(r+1, r)`. -/
noncomputable def sliceFactorT (π : Path) (X : RegChain) (r : ℕ) (k : Mom d) : ℂ :=
  LeafApp.tree δ r (LeafApp.sliceProfiles LG H (0, π) r X) (SourceApp.chainSlice LG (0, π) r X)
    (LG.garden.sig 0) (r + 1) r k

/-- The bottom tree slice at `(q'+1, s)`. -/
noncomputable def lowBotT (π : Path) (X : RegChain) (s : ℝ) (k : Mom d) : ℂ :=
  LeafApp.tree δ q' (LeafApp.sliceProfiles LG H (0, π) q' X) (SourceApp.chainSlice LG (0, π) q' X)
    (LG.garden.sig 0) (q' + 1) s k

/-- The lower leading term of a suffix. -/
noncomputable def lowAppT (π : Path) (X : RegChain) (s : ℝ) (k : Mom d) : ℂ :=
  (∏ r ∈ Ioo q' (layerAt LG (0, π) + 1), sliceFactorT δ LG H π X r k) * lowBotT δ LG H q' π X s k

end LowT

theorem TopAll.topNe {w : ℕ} (LG : LayeredGarden w) {u r : ℕ} (h : r ≠ u) :
    ∀ (a : Fin w × Path) (B : RegChain), TopAll LG u a B → TopNe LG r a B
  | _, .nil, _ => trivial
  | a, .pair m _ _ inner rest, ⟨ha, hT⟩ => ⟨by rw [ha]; exact Ne.symm h, TopAll.topNe LG h _ rest hT⟩

/-- **The explicit leading term of a tree for `q' < q`** (TARGET prooflayer1-2). -/
theorem coherentTree_gt_eq (δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d) (X : RegChain) {q q' : ℕ}
    (hq : q' < q) (t s : ℝ) (k : Mom d) :
    LeafApp.coherentTree δ LG H X q q' t s k =
      (∏ r ∈ Ioo q' q, sliceFactorT δ LG H [] X r k) *
        LeafApp.tree δ q (LeafApp.sliceProfiles LG H (0, []) q X) (SourceApp.chainSlice LG (0, []) q X)
          (LG.garden.sig 0) t q k *
        lowBotT δ LG H q' [] X s k := by
  have hne : q ≠ q' := by omega
  simp only [LeafApp.coherentTree, hne, ↓reduceIte]
  rfl

section Split

variable (δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d) {q' u : ℕ} (π : Path) (X : RegChain)
  (hu : layerAt LG (0, π) = u)
  (hD : SpineMono LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) (dropLayer LG (0, π) u X))

theorem sliceFactorT_take_drop {r : ℕ} (hr : r ≠ u) (k : Mom d) :
    sliceFactorT δ LG H π X r k =
      sliceFactorT δ LG H (π ++ (takeLayer LG (0, π) u X).lonePath) (dropLayer LG (0, π) u X) r k := by
  have hXe : appendChain (takeLayer LG (0, π) u X) (dropLayer LG (0, π) u X) = X :=
    appendChain_take_drop LG (0, π) u X
  have hTA : TopAll LG u (0, π) (takeLayer LG (0, π) u X) := topAll_takeLayer LG u _ X
  unfold sliceFactorT LeafApp.sliceProfiles
  rw [chainSlice_take_drop LG hr (0, π) X]
  congr 2
  funext z
  conv_lhs => rw [← hXe]
  exact congrArg H (sliceAddress_append_skip LG r _ _ (0, π) z.2 (TopAll.topNe LG hr _ _ hTA))

theorem lowBotT_take_drop (hq : q' < u) (s : ℝ) (k : Mom d) :
    lowBotT δ LG H q' π X s k =
      lowBotT δ LG H q' (π ++ (takeLayer LG (0, π) u X).lonePath) (dropLayer LG (0, π) u X) s k := by
  have hXe : appendChain (takeLayer LG (0, π) u X) (dropLayer LG (0, π) u X) = X :=
    appendChain_take_drop LG (0, π) u X
  have hTA : TopAll LG u (0, π) (takeLayer LG (0, π) u X) := topAll_takeLayer LG u _ X
  have hr : q' ≠ u := by omega
  unfold lowBotT LeafApp.sliceProfiles
  rw [chainSlice_take_drop LG hr (0, π) X]
  congr 2
  funext z
  conv_lhs => rw [← hXe]
  exact congrArg H (sliceAddress_append_skip LG q' _ _ (0, π) z.2 (TopAll.topNe LG hr _ _ hTA))

include hD in
theorem sliceFactorT_eq_one {r : ℕ} (hr : layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) < r)
    (k : Mom d) :
    sliceFactorT δ LG H (π ++ (takeLayer LG (0, π) u X).lonePath) (dropLayer LG (0, π) u X) r k = 1 := by
  unfold sliceFactorT
  rw [chainSlice_eq_nil LG _ _ hD fun _ => hr]
  exact LeafApp.tree_nil _ _ _ _ _ _ _

include hu hD in
/-- **Removing the top block** from the lower leading term. -/
theorem lowAppT_split {q' : ℕ} (hq : q' < u)
    (hlow : q' ≤ layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath))
    (hlt : layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) < u) (s : ℝ) (k : Mom d) :
    lowAppT δ LG H q' π X s k =
      sliceFactorT δ LG H π X u k *
        lowAppT δ LG H q' (π ++ (takeLayer LG (0, π) u X).lonePath) (dropLayer LG (0, π) u X) s k := by
  set r'' := layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) with hr''
  unfold lowAppT
  rw [hu, Ioo_eq_Ico_succ, prod_Ico_succ_top (by omega)]
  have hprod : ∏ r ∈ Ico (q' + 1) u, sliceFactorT δ LG H π X r k =
      ∏ r ∈ Ioo q' (r'' + 1), sliceFactorT δ LG H (π ++ (takeLayer LG (0, π) u X).lonePath)
        (dropLayer LG (0, π) u X) r k := by
    rw [Finset.prod_congr rfl fun r hr => sliceFactorT_take_drop δ LG H π X (u := u) (r := r)
        (by simp only [Finset.mem_Ico] at hr; omega) k,
      Ioo_eq_Ico_succ, ← prod_Ico_consecutive _ (show q' + 1 ≤ r'' + 1 by omega) (show r'' + 1 ≤ u by omega),
      Finset.prod_eq_one (s := Ico (r'' + 1) u) fun r hr => sliceFactorT_eq_one δ LG H π X hD
        (by simp only [Finset.mem_Ico] at hr; omega) k,
      mul_one]
  rw [hprod, lowBotT_take_drop δ LG H π X (u := u) hq s k]
  ring

include hD in
/-- **The product below a top block** in layer `u` is the lower leading term of the rest. -/
theorem lowRestT_eq {q' : ℕ} (hq : q' < u)
    (hlow : q' ≤ layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath))
    (hlt : layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) < u) (s : ℝ) (k : Mom d) :
    (∏ r ∈ Ioo q' u, sliceFactorT δ LG H π X r k) * lowBotT δ LG H q' π X s k =
      lowAppT δ LG H q' (π ++ (takeLayer LG (0, π) u X).lonePath) (dropLayer LG (0, π) u X) s k := by
  set r'' := layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) with hr''
  have hprod : ∏ r ∈ Ioo q' u, sliceFactorT δ LG H π X r k =
      ∏ r ∈ Ioo q' (r'' + 1), sliceFactorT δ LG H (π ++ (takeLayer LG (0, π) u X).lonePath)
        (dropLayer LG (0, π) u X) r k := by
    rw [Finset.prod_congr rfl fun r hr => sliceFactorT_take_drop δ LG H π X (u := u) (r := r)
        (by simp only [Finset.mem_Ioo] at hr; omega) k,
      Ioo_eq_Ico_succ, Ioo_eq_Ico_succ, ← prod_Ico_consecutive _ (show q' + 1 ≤ r'' + 1 by omega)
        (show r'' + 1 ≤ u by omega),
      Finset.prod_eq_one (s := Ico (r'' + 1) u) fun r hr => sliceFactorT_eq_one δ LG H π X hD
        (by simp only [Finset.mem_Ico] at hr; omega) k,
      mul_one]
  rw [hprod, lowBotT_take_drop δ LG H π X (u := u) hq s k]
  rfl

end Split

/-- **A single block** in layer `u ≥ q'`: the lower leading term is the single-layer leading term at
`(u+1, s)`, `s ≤ q'+1`. -/
theorem lowAppT_base (δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d) {q' u : ℕ} {π : Path}
    {X : RegChain} (hu : layerAt LG (0, π) = u) (hqu : q' ≤ u) (hTA : TopAll LG u (0, π) X) {s : ℝ}
    (hs : s ≤ (q' : ℝ) + 1) (k : Mom d) :
    lowAppT δ LG H q' π X s k =
      LeafApp.tree δ u (fun z => H (botAddr π z)) X (LG.garden.sig 0) (u + 1) s k := by
  have hprof : LeafApp.sliceProfiles LG H (0, π) u X = fun z => H (botAddr π z) := by
    funext z
    unfold LeafApp.sliceProfiles
    rw [sliceAddress_of_topAll LG u X _ _ hTA]
    obtain ⟨j, p⟩ := z
    fin_cases j
    simp [botAddr, addrExt]
  rcases eq_or_lt_of_le hqu with h | h
  · subst h
    unfold lowAppT lowBotT
    have h0 : Ioo q' (q' + 1) = ∅ := by
      ext x
      simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
      omega
    rw [hu, h0, prod_empty, one_mul, chainSlice_of_topAll LG q' X _ hTA, hprof]
  · unfold lowAppT lowBotT
    rw [chainSlice_of_topNe LG q' X _ (TopAll.topNe LG (Nat.ne_of_lt h) _ _ hTA), LeafApp.tree_nil, mul_one, hu,
      Ioo_eq_Ico_succ, prod_Ico_succ_top (by omega)]
    rw [Finset.prod_eq_one fun r hr => by
      unfold sliceFactorT
      rw [chainSlice_of_topNe LG r X _ (TopAll.topNe LG (by simp only [Finset.mem_Ico] at hr; omega) _ _ hTA)]
      exact LeafApp.tree_nil _ _ _ _ _ _ _, one_mul]
    unfold sliceFactorT
    have hsu : s ≤ (u : ℝ) := by
      have : (q' : ℝ) + 1 ≤ u := by exact_mod_cast h
      linarith
    rw [chainSlice_of_topAll LG u X _ hTA, hprof, LeafApp.tree_lower_eq δ u _ X _ _ hsu k]

end WaveTurbulence.PL234
