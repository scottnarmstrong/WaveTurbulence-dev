/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreICut
public import WaveTurbulence.Foundations.Molecule.VineCoreIICut
public import WaveTurbulence.Foundations.Molecule.VineCoreIIICut
public import WaveTurbulence.Foundations.Molecule.VineCoreIVCut
public import WaveTurbulence.Foundations.Molecule.VineCoreVCut
public import WaveTurbulence.Foundations.Molecule.VineCoreVICut
public import WaveTurbulence.Foundations.Molecule.VineCoreVIICut
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIICut
public import WaveTurbulence.Foundations.Molecule.VineBinaryCuts
public import WaveTurbulence.Foundations.Molecule.VineCoreMasks
import Mathlib.Tactic

/-! # Complete finite-core cut-mask classification

Auxiliary edge costs are literal absolute membership differences.
Their zero extension outside the enumerated indices is never consumed. -/

public section
namespace WaveTurbulence.Vine

/-- Transfer the type-I flow certificate to literal binary cut weights. -/
theorem coreI_binary_cut_masks (b : ℕ → ℕ) (h0 : b 0=0) (h1 : b 1=0)
    (hb : ∀ i < 2,b i ≤ 1) (hcut : binaryCut b VineType.I.template.bonds ≤ 2) :
    coreMaskVector .I b ∈ List.replicate 2 0 :: coreMaskCandidates .I .hyper := by
  let c : ℕ → ℕ
    | 0 => (b 0-b 1)+(b 1-b 0)
    | _ => 0
  apply coreI_cut_masks b c h0 h1 hb
  · convert hcut using 1;
      simp only [c,binaryCut,VineType.template,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,two_mul,Nat.add_zero]
  all_goals simp only [c]
  all_goals exact binaryCut_edge_bounds b _ _

/-- Transfer the type-II flow certificate to literal binary cut weights. -/
theorem coreII_binary_cut_masks (b : ℕ → ℕ) (h0 : b 0=0) (h1 : b 1=0)
    (hb : ∀ i < 4,b i ≤ 1) (hcut : binaryCut b VineType.II.template.bonds ≤ 2) :
    coreMaskVector .II b ∈ List.replicate 4 0 :: coreMaskCandidates .II .hyper := by
  let c : ℕ → ℕ
    | 0 => (b 0-b 2)+(b 2-b 0)
    | 1 => (b 0-b 3)+(b 3-b 0)
    | 2 => (b 1-b 2)+(b 2-b 1)
    | 3 => (b 1-b 3)+(b 3-b 1)
    | 4 => (b 2-b 3)+(b 3-b 2)
    | _ => 0
  apply coreII_cut_masks b c h0 h1 hb
  · convert hcut using 1;
      simp only [c,binaryCut,VineType.template,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,two_mul,Nat.add_zero]; ac_rfl
  all_goals simp only [c]
  all_goals exact binaryCut_edge_bounds b _ _

/-- Transfer the type-III flow certificate to literal binary cut weights. -/
theorem coreIII_binary_cut_masks (b : ℕ → ℕ) (h0 : b 0=0) (h1 : b 1=0)
    (hb : ∀ i < 9,b i ≤ 1) (hcut : binaryCut b VineType.III.template.bonds ≤ 2) :
    coreMaskVector .III b ∈ List.replicate 9 0 :: coreMaskCandidates .III .hyper := by
  let c : ℕ → ℕ
    | 0 => (b 0-b 2)+(b 2-b 0)
    | 1 => (b 0-b 3)+(b 3-b 0)
    | 2 => (b 1-b 7)+(b 7-b 1)
    | 3 => (b 1-b 8)+(b 8-b 1)
    | 4 => (b 2-b 3)+(b 3-b 2)
    | 5 => (b 2-b 4)+(b 4-b 2)
    | 6 => (b 3-b 5)+(b 5-b 3)
    | 7 => (b 4-b 5)+(b 5-b 4)
    | 8 => (b 4-b 6)+(b 6-b 4)
    | 9 => (b 4-b 7)+(b 7-b 4)
    | 10 => (b 5-b 6)+(b 6-b 5)
    | 11 => (b 6-b 8)+(b 8-b 6)
    | 12 => (b 7-b 8)+(b 8-b 7)
    | _ => 0
  apply coreIII_cut_masks b c h0 h1 hb
  · convert hcut using 1;
      simp only [c,binaryCut,VineType.template,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,two_mul,Nat.add_zero]; ac_rfl
  all_goals simp only [c]
  all_goals exact binaryCut_edge_bounds b _ _

/-- Transfer the type-IV flow certificate to literal binary cut weights. -/
theorem coreIV_binary_cut_masks (b : ℕ → ℕ) (h0 : b 0=0) (h1 : b 1=0)
    (hb : ∀ i < 9,b i ≤ 1) (hcut : binaryCut b VineType.IV.template.bonds ≤ 2) :
    coreMaskVector .IV b ∈ List.replicate 9 0 :: coreMaskCandidates .IV .hyper := by
  let c : ℕ → ℕ
    | 0 => (b 0-b 2)+(b 2-b 0)
    | 1 => (b 0-b 3)+(b 3-b 0)
    | 2 => (b 1-b 7)+(b 7-b 1)
    | 3 => (b 1-b 8)+(b 8-b 1)
    | 4 => (b 2-b 3)+(b 3-b 2)
    | 5 => (b 2-b 4)+(b 4-b 2)
    | 6 => (b 3-b 6)+(b 6-b 3)
    | 7 => (b 4-b 5)+(b 5-b 4)
    | 8 => (b 4-b 7)+(b 7-b 4)
    | 9 => (b 5-b 6)+(b 6-b 5)
    | 10 => (b 6-b 8)+(b 8-b 6)
    | 11 => (b 7-b 8)+(b 8-b 7)
    | _ => 0
  apply coreIV_cut_masks b c h0 h1 hb
  · convert hcut using 1;
      simp only [c,binaryCut,VineType.template,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,two_mul,Nat.add_zero]; ac_rfl
  all_goals simp only [c]
  all_goals exact binaryCut_edge_bounds b _ _

/-- Transfer the type-V flow certificate to literal binary cut weights. -/
theorem coreV_binary_cut_masks (b : ℕ → ℕ) (h0 : b 0=0) (h1 : b 1=0)
    (hb : ∀ i < 9,b i ≤ 1) (hcut : binaryCut b VineType.V.template.bonds ≤ 2) :
    coreMaskVector .V b ∈ List.replicate 9 0 :: coreMaskCandidates .V .hyper := by
  let c : ℕ → ℕ
    | 0 => (b 0-b 1)+(b 1-b 0)
    | 1 => (b 0-b 2)+(b 2-b 0)
    | 2 => (b 1-b 3)+(b 3-b 1)
    | 3 => (b 2-b 3)+(b 3-b 2)
    | 4 => (b 2-b 4)+(b 4-b 2)
    | 5 => (b 3-b 5)+(b 5-b 3)
    | 6 => (b 4-b 5)+(b 5-b 4)
    | 7 => (b 4-b 6)+(b 6-b 4)
    | 8 => (b 5-b 7)+(b 7-b 5)
    | 9 => (b 6-b 7)+(b 7-b 6)
    | 10 => (b 6-b 8)+(b 8-b 6)
    | 11 => (b 7-b 8)+(b 8-b 7)
    | _ => 0
  apply coreV_cut_masks b c h0 h1 hb
  · convert hcut using 1;
      simp only [c,binaryCut,VineType.template,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,two_mul,Nat.add_zero]; ac_rfl
  all_goals simp only [c]
  all_goals exact binaryCut_edge_bounds b _ _

/-- Transfer the type-VI flow certificate to literal binary cut weights. -/
theorem coreVI_binary_cut_masks (b : ℕ → ℕ) (h0 : b 0=0) (h1 : b 1=0)
    (hb : ∀ i < 15,b i ≤ 1) (hcut : binaryCut b VineType.VI.template.bonds ≤ 2) :
    coreMaskVector .VI b ∈ List.replicate 15 0 :: coreMaskCandidates .VI .hyper := by
  let c : ℕ → ℕ
    | 0 => (b 0-b 2)+(b 2-b 0)
    | 1 => (b 0-b 3)+(b 3-b 0)
    | 2 => (b 1-b 13)+(b 13-b 1)
    | 3 => (b 1-b 14)+(b 14-b 1)
    | 4 => (b 2-b 3)+(b 3-b 2)
    | 5 => (b 2-b 4)+(b 4-b 2)
    | 6 => (b 3-b 5)+(b 5-b 3)
    | 7 => (b 4-b 5)+(b 5-b 4)
    | 8 => (b 4-b 6)+(b 6-b 4)
    | 9 => (b 5-b 8)+(b 8-b 5)
    | 10 => (b 6-b 7)+(b 7-b 6)
    | 11 => (b 6-b 13)+(b 13-b 6)
    | 12 => (b 7-b 9)+(b 9-b 7)
    | 13 => (b 7-b 14)+(b 14-b 7)
    | 14 => (b 8-b 9)+(b 9-b 8)
    | 15 => (b 8-b 10)+(b 10-b 8)
    | 16 => (b 9-b 11)+(b 11-b 9)
    | 17 => (b 10-b 11)+(b 11-b 10)
    | 18 => (b 10-b 12)+(b 12-b 10)
    | 19 => (b 11-b 12)+(b 12-b 11)
    | 20 => (b 13-b 14)+(b 14-b 13)
    | _ => 0
  apply coreVI_cut_masks b c h0 h1 hb
  · convert hcut using 1;
      simp only [c,binaryCut,VineType.template,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,two_mul,Nat.add_zero]; ac_rfl
  all_goals simp only [c]
  all_goals exact binaryCut_edge_bounds b _ _

/-- Transfer the type-VII flow certificate to literal binary cut weights. -/
theorem coreVII_binary_cut_masks (b : ℕ → ℕ) (h0 : b 0=0) (h1 : b 1=0)
    (hb : ∀ i < 11,b i ≤ 1) (hcut : binaryCut b VineType.VII.template.bonds ≤ 2) :
    coreMaskVector .VII b ∈ List.replicate 11 0 :: coreMaskCandidates .VII .hyper := by
  let c : ℕ → ℕ
    | 0 => (b 0-b 2)+(b 2-b 0)
    | 1 => (b 0-b 3)+(b 3-b 0)
    | 2 => (b 1-b 9)+(b 9-b 1)
    | 3 => (b 1-b 10)+(b 10-b 1)
    | 4 => (b 2-b 3)+(b 3-b 2)
    | 5 => (b 2-b 7)+(b 7-b 2)
    | 6 => (b 3-b 8)+(b 8-b 3)
    | 7 => (b 4-b 5)+(b 5-b 4)
    | 8 => (b 4-b 6)+(b 6-b 4)
    | 9 => (b 5-b 6)+(b 6-b 5)
    | 10 => (b 5-b 7)+(b 7-b 5)
    | 11 => (b 6-b 8)+(b 8-b 6)
    | 12 => (b 7-b 8)+(b 8-b 7)
    | 13 => (b 7-b 9)+(b 9-b 7)
    | 14 => (b 8-b 10)+(b 10-b 8)
    | 15 => (b 9-b 10)+(b 10-b 9)
    | _ => 0
  apply coreVII_cut_masks b c h0 h1 hb
  · convert hcut using 1;
      simp only [c,binaryCut,VineType.template,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,two_mul,Nat.add_zero]; ac_rfl
  all_goals simp only [c]
  all_goals exact binaryCut_edge_bounds b _ _

/-- Transfer the type-VIII flow certificate to literal binary cut weights. -/
theorem coreVIII_binary_cut_masks (b : ℕ → ℕ) (h0 : b 0=0) (h1 : b 1=0)
    (hb : ∀ i < 11,b i ≤ 1) (hcut : binaryCut b VineType.VIII.template.bonds ≤ 2) :
    coreMaskVector .VIII b ∈ List.replicate 11 0 :: coreMaskCandidates .VIII .hyper := by
  let c : ℕ → ℕ
    | 0 => (b 0-b 2)+(b 2-b 0)
    | 1 => (b 0-b 6)+(b 6-b 0)
    | 2 => (b 1-b 4)+(b 4-b 1)
    | 3 => (b 1-b 5)+(b 5-b 1)
    | 4 => (b 2-b 3)+(b 3-b 2)
    | 5 => (b 2-b 4)+(b 4-b 2)
    | 6 => (b 3-b 5)+(b 5-b 3)
    | 7 => (b 3-b 7)+(b 7-b 3)
    | 8 => (b 4-b 5)+(b 5-b 4)
    | 9 => (b 6-b 7)+(b 7-b 6)
    | 10 => (b 6-b 8)+(b 8-b 6)
    | 11 => (b 7-b 9)+(b 9-b 7)
    | 12 => (b 8-b 9)+(b 9-b 8)
    | 13 => (b 8-b 10)+(b 10-b 8)
    | 14 => (b 9-b 10)+(b 10-b 9)
    | _ => 0
  apply coreVIII_cut_masks b c h0 h1 hb
  · convert hcut using 1;
      simp only [c,binaryCut,VineType.template,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,two_mul,Nat.add_zero]; ac_rfl
  all_goals simp only [c]
  all_goals exact binaryCut_edge_bounds b _ _

/-- A core cut of size at most two, with its two outer joints absent,
has the empty mask or one of the checked hyper-block core masks. -/
theorem core_cut_mask_exhaustive (X : VineType) (W : Finset ℕ)
    (h0 : 0 ∉ W) (h1 : 1 ∉ W) (hcut : rawCut W X.template.bonds ≤ 2) :
    coreMaskVector X (membershipMask W) ∈
      List.replicate X.template.n 0 :: coreMaskCandidates X .hyper := by
  let b := membershipMask W
  have hb0 : b 0=0 := by simp only [b,membershipMask,h0,ite_false]
  have hb1 : b 1=0 := by simp only [b,membershipMask,h1,ite_false]
  have hb : ∀ i,b i ≤ 1 := by
    intro i
    dsimp [b,membershipMask]
    split_ifs <;> omega
  have hcut' : binaryCut b X.template.bonds ≤ 2 := by
    simpa only [rawCut_eq_binaryCut,b] using hcut
  cases X
  case I => exact coreI_binary_cut_masks b hb0 hb1 (fun i _hi => hb i) hcut'
  case II => exact coreII_binary_cut_masks b hb0 hb1 (fun i _hi => hb i) hcut'
  case III => exact coreIII_binary_cut_masks b hb0 hb1 (fun i _hi => hb i) hcut'
  case IV => exact coreIV_binary_cut_masks b hb0 hb1 (fun i _hi => hb i) hcut'
  case V => exact coreV_binary_cut_masks b hb0 hb1 (fun i _hi => hb i) hcut'
  case VI => exact coreVI_binary_cut_masks b hb0 hb1 (fun i _hi => hb i) hcut'
  case VII => exact coreVII_binary_cut_masks b hb0 hb1 (fun i _hi => hb i) hcut'
  case VIII => exact coreVIII_binary_cut_masks b hb0 hb1 (fun i _hi => hb i) hcut'

end WaveTurbulence.Vine
