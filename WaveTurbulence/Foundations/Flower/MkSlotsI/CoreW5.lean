/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.CoreW4

/-! # B3s-HELPER7 WP7 (part 5): the member core weight in the form the member chain consumes

* **`selOK_mul_genCoreW_member`**: `selOK(y) · genCoreW(y) (κ) = selOK(a) · selConst(a) · zatomG (resDec κ) · topW`
  for every member `y` (no non-zero hypothesis: if `selOK(a) = 0` then `selOK(y) = 0`, `selOK_member`);
* the stem-free case (`¬ StemDep σ kSel`: no σ filter, no selection), where `CleanPt J a` is not available: every
  general stem node weight is `1` (`genNW_stemFree`), hence `zatomG = 1`, the top weight is `1`, `selOK = 1`, the
  selection constant is `1`;
* **`selOK_mul_genCoreW_member_gen`**: the identity under B4's alternative `¬ StemDep σ kSel ∨ CleanPt J a` (the
  hypothesis of `MkSlotsG.ClassRepGen`), with `CapGeo` of both reconstructions (single-leaf cap trees, one capped
  flower per tree), `G_sb` plain, `hrepU` and `hrepS` (`rep_tops_not_sel`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.Stage1MKGate (CleanPt classMk StemDep)
open WaveTurbulence.Flower.MkSlots (recLG)

namespace WaveTurbulence.Flower.MkSlotsI

/-! ## The stem-free case -/

section StemFree

variable {w : ℕ}

/-- Without stem filters and selections the general stem node weight is `1`. -/
theorem genNW_stemFree (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (Rs : Fin w → ℝ)
    (z : GNode LG.garden.tree) (x : ℝ) : genNW LG J L (fun _ => none) (fun _ => none) Rs z x = 1 := by
  unfold genNW
  split_ifs with h1 h2 h3
  · exfalso
    obtain ⟨j, hj⟩ := (Finset.mem_filter.1 h3).2
    simp [selCap] at hj
  · have e1 : MkSlotsT.radSigma L (fun _ => none) (⟨z.1, h1⟩ : GBranch LG.garden.tree) = [] := rfl
    have e2 : MkSlotsG.shellRad LG J (fun _ => none) Rs (⟨z.1, h1⟩ : GBranch LG.garden.tree) = [] := by
      unfold MkSlotsG.shellRad
      rw [ite_eq_right]
      rintro ⟨v, hv, -⟩
      simp [selCap] at hv
    simp [MkSlotsG.radRaw, e1, e2, MkSlotsT.radProd]
  · rfl
  · rfl

/-- Not stem dependent: no σ filter and no selection. -/
theorem eq_none_of_not_stemDep {σ kSel : Fin w → Option ℕ} (h : ¬ StemDep σ kSel) :
    σ = (fun _ => none) ∧ kSel = (fun _ => none) :=
  ⟨funext fun i => by by_contra hi; exact h (Or.inl ⟨i, hi⟩),
    funext fun i => by by_contra hi; exact h (Or.inr ⟨i, hi⟩)⟩

theorem selOK_stemFree (LG : LayeredGarden w) (J : Finset (Fin w)) : selOK LG J (fun _ => none) = 1 := by
  simp [selOK]

theorem selConst_stemFree (LG : LayeredGarden w) (J : Finset (Fin w)) (Rs : Fin w → ℝ) :
    (∏ j, (selCap LG J (fun _ => none) j).elim 1 (fun _ => (((Rs j)⁻¹ : ℝ) : ℂ))) = 1 := by
  simp [selCap]

theorem zatomG_stemFree {d : ℕ} (J : Finset (Fin w)) (L : ℝ) (Rs : Fin w → ℝ) (a : PrescribedPrimeGarden w)
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma Mk).G d roots 0) :
    zatomG J L (fun _ => none) (fun _ => none) Rs a Mk z = 1 :=
  Finset.prod_eq_one fun _ _ => genNW_stemFree _ J L Rs _ _

theorem radTGen_stemFree (L : ℝ) (Rs : Fin w → ℝ) : radTGen L (fun _ => none) (fun _ => none) Rs = fun _ => [] := by
  funext j
  simp [radTGen]

end StemFree

/-! ## The run class -/

section Class

variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (J : Finset (Fin (2 * R)))

variable (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
  (hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))
  (honeA : MkSlotsS.OneFlower (recLG a) J)
  (honeY : MkSlotsS.OneFlower (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J)

end Class

end WaveTurbulence.Flower.MkSlotsI
