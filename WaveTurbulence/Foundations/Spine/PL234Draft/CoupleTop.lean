/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.CohTransport

/-!
# Prop 6.1, `q > q'`, couples: the explicit leading term and the top factor

* `coherentCouple_type2_eq`: for `q' < q` the explicit leading term `LeafApp.coherentCouple` of a type-2 code is
  `(∏_{q'<r<q} 𝒜_r(r+1, r)) · 𝒜_q(t, q) · 𝒜_bot(q'+1, s)` in the notation of `LowApp`;
* `lowRest_eq`: the product below a top block in layer `u` is the lower leading term of the rest;
* `one_le_Ktr`.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

variable {d : ℕ}

theorem one_le_Ktr {θ : ℝ} (hθ : 0 ≤ θ) : 1 ≤ Ktr θ := by
  have h := Regref.one_le_traceConst (r := 2) hθ Layered.chiUnit_contDiff
    (Layered.coordinateCutoff_chiUnit_eq_one (t := fun _ => 0) fun _ => ⟨le_rfl, by norm_num⟩)
  have := ENNReal.toReal_mono (Layered.traceConst_chiUnit_ne_top θ) h
  simpa [Ktr] using this

theorem lowerProfiles_eq_botProf (LG : LayeredGarden 2) (H : LeafProfiles 2 d) (q' : ℕ) (Xp Xm : RegChain) :
    LeafApp.lowerProfiles LG H q' Xp Xm 0 = botProf LG H q' [] Xp := by
  funext z
  unfold LeafApp.lowerProfiles botProf
  simp

/-- **The explicit leading term of a type-2 code for `q' < q`** (TARGET prooflayer1-1). -/
theorem coherentCouple_type2_eq (δ : ℝ) (LG : LayeredGarden 2) (H : LeafProfiles 2 d)
    (Xp Xm : RegChain) (Qlp : RegCpl) {q q' : ℕ} (hq : q' < q) (t s : ℝ) (k : Mom d) :
    LeafApp.coherentCouple δ LG H (.type2 Xp Xm Qlp) q q' t s k =
      (∏ r ∈ Ioo q' q, sliceFactor δ LG H [] Xp r k) *
        LeafApp.tree δ q (LeafApp.sliceProfiles LG H (0, []) q Xp)
          (SourceApp.chainSlice LG (0, []) q Xp) 1 t q k *
        lowBot δ LG H Xm Qlp q' [] Xp s k := by
  have hne : q ≠ q' := by omega
  simp only [LeafApp.coherentCouple, hne, hq, ↓reduceIte]
  unfold sliceFactor lowBot
  rw [lowerProfiles_eq_botProf]

/-- **The product below a top block** in layer `u` is the lower leading term of the rest. -/
theorem lowRest_eq (δ : ℝ) (LG : LayeredGarden 2) (H : LeafProfiles 2 d) (Xm : RegChain) (Qlp : RegCpl)
    {q' u : ℕ} (π : Path) (X : RegChain) (hu : layerAt LG (0, π) = u) (hq : q' < u)
    (hD : SpineMono LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) (dropLayer LG (0, π) u X))
    (hlow : q' ≤ layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath))
    (hlt : layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) < u) (s : ℝ) (k : Mom d) :
    (∏ r ∈ Ioo q' u, sliceFactor δ LG H π X r k) * lowBot δ LG H Xm Qlp q' π X s k =
      lowApp δ LG H Xm Qlp q' (π ++ (takeLayer LG (0, π) u X).lonePath) (dropLayer LG (0, π) u X) s k := by
  set B := takeLayer LG (0, π) u X with hB
  set D := dropLayer LG (0, π) u X with hDd
  set π' := π ++ B.lonePath with hπ'
  set r'' := layerAt LG (0, π') with hr''
  have hXe : appendChain B D = X := appendChain_take_drop LG (0, π) u X
  have hTA : TopAll LG u (0, π) B := topAll_takeLayer LG u _ X
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
  have hnil : ∀ r, r'' < r → sliceFactor δ LG H π' D r k = 1 := fun r hr => by
    unfold sliceFactor
    rw [chainSlice_eq_nil LG (0, π') D hD fun _ => hr]
    exact LeafApp.tree_nil _ _ _ _ _ _ _
  have hprod : ∏ r ∈ Ioo q' u, sliceFactor δ LG H π X r k =
      ∏ r ∈ Ioo q' (r'' + 1), sliceFactor δ LG H π' D r k := by
    rw [Finset.prod_congr rfl fun r hr => hfac r (by simp only [Finset.mem_Ioo] at hr; omega),
      Ioo_eq_Ico_succ, Ioo_eq_Ico_succ, ← prod_Ico_consecutive _ (show q' + 1 ≤ r'' + 1 by omega)
      (show r'' + 1 ≤ u by omega),
      Finset.prod_eq_one (s := Ico (r'' + 1) u) fun r hr => hnil r (by simp only [Finset.mem_Ico] at hr; omega),
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
  rfl

end WaveTurbulence.PL234
