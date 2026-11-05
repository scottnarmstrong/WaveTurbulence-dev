/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseCoherentApp
public import WaveTurbulence.Foundations.RegularAsymptotics.RegularAppContinuity
/-! Continuity of the explicit leafwise B2 and coherent approximations; no regularity hypothesis is imposed on H. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
/-- The momentum and special-subset factors are constant in time. -/
theorem continuous_LeafApp_couple {d : ℕ} (δ r : ℝ) (H : LeafProfiles 2 d) (Q : RegCpl) (k : Mom d) :
    Continuous (fun p : ℝ × ℝ => LeafApp.couple δ r H Q p.1 p.2 k) := by
  classical
  unfold LeafApp.couple
  split_ifs
  · apply continuous_const.mul
    apply continuous_finsetSum
    intro Z _
    exact (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_RegCpl_JB r Q))).mul continuous_const
  · exact continuous_const

theorem continuous_LeafApp_tree {d : ℕ} (δ r : ℝ) (H : LeafProfiles 1 d) (X : RegChain) (ζ : ℤˣ) (k : Mom d) :
    Continuous (fun p : ℝ × ℝ => LeafApp.tree δ r H X ζ p.1 p.2 k) := by
  classical
  unfold LeafApp.tree
  split_ifs
  · apply continuous_const.mul
    apply continuous_finsetSum
    intro Z _
    exact (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_RegChain_JBtree r X))).mul continuous_const
  · exact continuous_const

@[fun_prop] theorem continuous_LeafApp_couple_comp {T : Type*} [TopologicalSpace T] {d : ℕ}
    (δ r : ℝ) (H : LeafProfiles 2 d) (Q : RegCpl) (k : Mom d)
    (a b : T → ℝ) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => LeafApp.couple δ r H Q (a x) (b x) k) :=
  (continuous_LeafApp_couple δ r H Q k).comp (ha.prodMk hb)

@[fun_prop] theorem continuous_LeafApp_tree_comp {T : Type*} [TopologicalSpace T] {d : ℕ}
    (δ r : ℝ) (H : LeafProfiles 1 d) (X : RegChain) (ζ : ℤˣ) (k : Mom d)
    (a b : T → ℝ) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => LeafApp.tree δ r H X ζ (a x) (b x) k) :=
  (continuous_LeafApp_tree δ r H X ζ k).comp (ha.prodMk hb)

theorem continuous_LeafApp_coherentCouple {d : ℕ} (δ : ℝ) (H : LeafProfiles 2 d)
    (LG : LayeredGarden 2) (Q : RegCpl) (q q' : ℕ) (k : Mom d) :
    Continuous (fun p : ℝ × ℝ => LeafApp.coherentCouple δ LG H Q q q' p.1 p.2 k) := by
  classical
  cases Q with
  | triv =>
    simp only [LeafApp.coherentCouple]
    split_ifs <;> fun_prop
  | type1 c Q₁ Q₂ Q₃ =>
    simp only [LeafApp.coherentCouple]
    split_ifs <;> fun_prop
  | type2 Xp Xm Qlp =>
    simp only [LeafApp.coherentCouple]
    split_ifs <;> fun_prop

theorem continuous_LeafApp_coherentTree {d : ℕ} (δ : ℝ) (H : LeafProfiles 1 d)
    (LG : LayeredGarden 1) (X : RegChain) (q q' : ℕ) (k : Mom d) :
    Continuous (fun p : ℝ × ℝ => LeafApp.coherentTree δ LG H X q q' p.1 p.2 k) := by
  classical
  unfold LeafApp.coherentTree
  split_ifs <;> fun_prop


end WaveTurbulence.LGSpine
