/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeOriginalRemainderFamily
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeZeroError
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeCellCover

/-! # The literal original tree remainder vanishes at order zero -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ClassJR ApproxNT MainCoef

/-- The empty-order original kernel equals literal app, with every profile and
root-partition cancellation proved rather than an empty-order NT estimate assumed. -/
theorem KTstar_eq_app_of_tree_size_zero {d : ℕ} (hd : 3 ≤ d)
    {X : RegChain} (hwf : X.wf=true) (hsize : X.size=0) (LG : LayeredGarden 1)
    (hX : X.DecodesTree LG.garden) (h0 : ∀ a, LG.layer a=0)
    {L : ℝ} (hL : 1 ≤ L) (δ γ : ℝ) (hδ : δ ≠ 0)
    {F : Mom d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm (40*d) (40*d) (fun k => (F k:ℂ)) ≤ ENNReal.ofReal B)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s<t) (ht : t≤1) (k : Mom d) :
    KTstar L γ δ (fun _ => F) LG t s k=X.app δ 0 F (LG.garden.sig 0) t s k := by
  classical
  have hnil : X=RegChain.nil := by
    cases X with
    | nil => rfl
    | pair m Qr Qg inner rest => simp only [RegChain.size] at hsize; omega
  subst X
  obtain ⟨Ccover,-,hcover⟩ := actual_tree_augmented_uniform_cell_cover d (by omega)
  choose S hS hcov using hcover LG.garden .nil hX
  obtain ⟨C,-,hrem⟩ := exists_tree_original_remainder_family
    (by norm_num : (0:ℝ)<1/40) (by norm_num : (1:ℝ)/40 ≤ 2)
    (le_max_right (1:ℝ) ClassJR.A1) .nil hwf (LG.garden.sig 0)
  have he := hrem d hd L γ δ hL hδ LG rfl h0 hX B hB F hF S
    (fun c k x hx z hz => hcov c k x hx z hz) Ccover hS t s hs hst ht k
  have hz (Z : (ClassJR.chosenSet ((toJRc RegChain.nil).linksAt (LG.garden.sig 0)
      (rootT (LG.garden.sig 0)))).powerset) (lam)
      (u : SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) :
      treeNormalizedScalar hX (treePhysicalErrorScalar L δ γ
        (treeMarkedIndices (treeChosenAddress .nil (LG.garden.sig 0)) Z.val) (C Z)) S lam u=0 := by
    unfold treeNormalizedScalar
    rw [treePhysicalErrorScalar_zero_of_eq (show (RegChain.nil.treeLinks (LG.garden.sig 0)).length=0 from rfl),zero_div]
  simp_rw [hz] at he
  simp only [pairedInverseProfile,zero_mul,integral_zero,mul_zero,Finset.sum_const_zero] at he
  exact sub_eq_zero.mp he

end WaveTurbulence.RegAsymp
