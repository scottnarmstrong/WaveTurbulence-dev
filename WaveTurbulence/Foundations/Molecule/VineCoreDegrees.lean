/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreMasks
import Mathlib.Tactic

/-! # Explicit adjacency matrices of the eight vine cores -/

public section
namespace WaveTurbulence.Vine

/-- The exact type-I incidence row at atom 0. -/
theorem coreDegree_I_0 (mask : ℕ → ℕ) :
    coreDegree .I mask 0 = 2*mask 1 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-I incidence row at atom 1. -/
theorem coreDegree_I_1 (mask : ℕ → ℕ) :
    coreDegree .I mask 1 = 2*mask 0 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-II incidence row at atom 0. -/
theorem coreDegree_II_0 (mask : ℕ → ℕ) :
    coreDegree .II mask 0 = mask 2+mask 3 := by
  simp [coreDegree,VineType.template]

/-- The exact type-II incidence row at atom 1. -/
theorem coreDegree_II_1 (mask : ℕ → ℕ) :
    coreDegree .II mask 1 = mask 2+mask 3 := by
  simp [coreDegree,VineType.template]

/-- The exact type-II incidence row at atom 2. -/
theorem coreDegree_II_2 (mask : ℕ → ℕ) :
    coreDegree .II mask 2 = mask 0+mask 1+2*mask 3 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-II incidence row at atom 3. -/
theorem coreDegree_II_3 (mask : ℕ → ℕ) :
    coreDegree .II mask 3 = mask 0+mask 1+2*mask 2 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-III incidence row at atom 0. -/
theorem coreDegree_III_0 (mask : ℕ → ℕ) :
    coreDegree .III mask 0 = mask 2+mask 3 := by
  simp [coreDegree,VineType.template]

/-- The exact type-III incidence row at atom 1. -/
theorem coreDegree_III_1 (mask : ℕ → ℕ) :
    coreDegree .III mask 1 = mask 7+mask 8 := by
  simp [coreDegree,VineType.template]

/-- The exact type-III incidence row at atom 2. -/
theorem coreDegree_III_2 (mask : ℕ → ℕ) :
    coreDegree .III mask 2 = mask 0+2*mask 3+mask 4 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-III incidence row at atom 3. -/
theorem coreDegree_III_3 (mask : ℕ → ℕ) :
    coreDegree .III mask 3 = mask 0+2*mask 2+mask 5 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-III incidence row at atom 4. -/
theorem coreDegree_III_4 (mask : ℕ → ℕ) :
    coreDegree .III mask 4 = mask 2+mask 5+mask 6+mask 7 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-III incidence row at atom 5. -/
theorem coreDegree_III_5 (mask : ℕ → ℕ) :
    coreDegree .III mask 5 = mask 3+mask 4+2*mask 6 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-III incidence row at atom 6. -/
theorem coreDegree_III_6 (mask : ℕ → ℕ) :
    coreDegree .III mask 6 = mask 4+2*mask 5+mask 8 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-III incidence row at atom 7. -/
theorem coreDegree_III_7 (mask : ℕ → ℕ) :
    coreDegree .III mask 7 = mask 1+mask 4+2*mask 8 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-III incidence row at atom 8. -/
theorem coreDegree_III_8 (mask : ℕ → ℕ) :
    coreDegree .III mask 8 = mask 1+mask 6+2*mask 7 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-IV incidence row at atom 0. -/
theorem coreDegree_IV_0 (mask : ℕ → ℕ) :
    coreDegree .IV mask 0 = mask 2+mask 3 := by
  simp [coreDegree,VineType.template]

/-- The exact type-IV incidence row at atom 1. -/
theorem coreDegree_IV_1 (mask : ℕ → ℕ) :
    coreDegree .IV mask 1 = mask 7+mask 8 := by
  simp [coreDegree,VineType.template]

/-- The exact type-IV incidence row at atom 2. -/
theorem coreDegree_IV_2 (mask : ℕ → ℕ) :
    coreDegree .IV mask 2 = mask 0+2*mask 3+mask 4 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-IV incidence row at atom 3. -/
theorem coreDegree_IV_3 (mask : ℕ → ℕ) :
    coreDegree .IV mask 3 = mask 0+2*mask 2+mask 6 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-IV incidence row at atom 4. -/
theorem coreDegree_IV_4 (mask : ℕ → ℕ) :
    coreDegree .IV mask 4 = mask 2+2*mask 5+mask 7 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-IV incidence row at atom 5. -/
theorem coreDegree_IV_5 (mask : ℕ → ℕ) :
    coreDegree .IV mask 5 = 2*mask 4+2*mask 6 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-IV incidence row at atom 6. -/
theorem coreDegree_IV_6 (mask : ℕ → ℕ) :
    coreDegree .IV mask 6 = mask 3+2*mask 5+mask 8 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-IV incidence row at atom 7. -/
theorem coreDegree_IV_7 (mask : ℕ → ℕ) :
    coreDegree .IV mask 7 = mask 1+mask 4+2*mask 8 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-IV incidence row at atom 8. -/
theorem coreDegree_IV_8 (mask : ℕ → ℕ) :
    coreDegree .IV mask 8 = mask 1+mask 6+2*mask 7 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-V incidence row at atom 0. -/
theorem coreDegree_V_0 (mask : ℕ → ℕ) :
    coreDegree .V mask 0 = mask 1+mask 2 := by
  simp [coreDegree,VineType.template]

/-- The exact type-V incidence row at atom 1. -/
theorem coreDegree_V_1 (mask : ℕ → ℕ) :
    coreDegree .V mask 1 = mask 0+mask 3 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-V incidence row at atom 2. -/
theorem coreDegree_V_2 (mask : ℕ → ℕ) :
    coreDegree .V mask 2 = mask 0+2*mask 3+mask 4 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-V incidence row at atom 3. -/
theorem coreDegree_V_3 (mask : ℕ → ℕ) :
    coreDegree .V mask 3 = mask 1+2*mask 2+mask 5 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-V incidence row at atom 4. -/
theorem coreDegree_V_4 (mask : ℕ → ℕ) :
    coreDegree .V mask 4 = mask 2+2*mask 5+mask 6 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-V incidence row at atom 5. -/
theorem coreDegree_V_5 (mask : ℕ → ℕ) :
    coreDegree .V mask 5 = mask 3+2*mask 4+mask 7 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-V incidence row at atom 6. -/
theorem coreDegree_V_6 (mask : ℕ → ℕ) :
    coreDegree .V mask 6 = mask 4+mask 7+2*mask 8 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-V incidence row at atom 7. -/
theorem coreDegree_V_7 (mask : ℕ → ℕ) :
    coreDegree .V mask 7 = mask 5+mask 6+2*mask 8 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-V incidence row at atom 8. -/
theorem coreDegree_V_8 (mask : ℕ → ℕ) :
    coreDegree .V mask 8 = 2*mask 6+2*mask 7 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VI incidence row at atom 0. -/
theorem coreDegree_VI_0 (mask : ℕ → ℕ) :
    coreDegree .VI mask 0 = mask 2+mask 3 := by
  simp [coreDegree,VineType.template]

/-- The exact type-VI incidence row at atom 1. -/
theorem coreDegree_VI_1 (mask : ℕ → ℕ) :
    coreDegree .VI mask 1 = mask 13+mask 14 := by
  simp [coreDegree,VineType.template]

/-- The exact type-VI incidence row at atom 2. -/
theorem coreDegree_VI_2 (mask : ℕ → ℕ) :
    coreDegree .VI mask 2 = mask 0+2*mask 3+mask 4 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VI incidence row at atom 3. -/
theorem coreDegree_VI_3 (mask : ℕ → ℕ) :
    coreDegree .VI mask 3 = mask 0+2*mask 2+mask 5 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VI incidence row at atom 4. -/
theorem coreDegree_VI_4 (mask : ℕ → ℕ) :
    coreDegree .VI mask 4 = mask 2+2*mask 5+mask 6 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VI incidence row at atom 5. -/
theorem coreDegree_VI_5 (mask : ℕ → ℕ) :
    coreDegree .VI mask 5 = mask 3+2*mask 4+mask 8 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VI incidence row at atom 6. -/
theorem coreDegree_VI_6 (mask : ℕ → ℕ) :
    coreDegree .VI mask 6 = mask 4+2*mask 7+mask 13 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VI incidence row at atom 7. -/
theorem coreDegree_VI_7 (mask : ℕ → ℕ) :
    coreDegree .VI mask 7 = 2*mask 6+mask 9+mask 14 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VI incidence row at atom 8. -/
theorem coreDegree_VI_8 (mask : ℕ → ℕ) :
    coreDegree .VI mask 8 = mask 5+2*mask 9+mask 10 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VI incidence row at atom 9. -/
theorem coreDegree_VI_9 (mask : ℕ → ℕ) :
    coreDegree .VI mask 9 = mask 7+2*mask 8+mask 11 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VI incidence row at atom 10. -/
theorem coreDegree_VI_10 (mask : ℕ → ℕ) :
    coreDegree .VI mask 10 = mask 8+mask 11+2*mask 12 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VI incidence row at atom 11. -/
theorem coreDegree_VI_11 (mask : ℕ → ℕ) :
    coreDegree .VI mask 11 = mask 9+mask 10+2*mask 12 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VI incidence row at atom 12. -/
theorem coreDegree_VI_12 (mask : ℕ → ℕ) :
    coreDegree .VI mask 12 = 2*mask 10+2*mask 11 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VI incidence row at atom 13. -/
theorem coreDegree_VI_13 (mask : ℕ → ℕ) :
    coreDegree .VI mask 13 = mask 1+mask 6+2*mask 14 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VI incidence row at atom 14. -/
theorem coreDegree_VI_14 (mask : ℕ → ℕ) :
    coreDegree .VI mask 14 = mask 1+mask 7+2*mask 13 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VII incidence row at atom 0. -/
theorem coreDegree_VII_0 (mask : ℕ → ℕ) :
    coreDegree .VII mask 0 = mask 2+mask 3 := by
  simp [coreDegree,VineType.template]

/-- The exact type-VII incidence row at atom 1. -/
theorem coreDegree_VII_1 (mask : ℕ → ℕ) :
    coreDegree .VII mask 1 = mask 9+mask 10 := by
  simp [coreDegree,VineType.template]

/-- The exact type-VII incidence row at atom 2. -/
theorem coreDegree_VII_2 (mask : ℕ → ℕ) :
    coreDegree .VII mask 2 = mask 0+2*mask 3+mask 7 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VII incidence row at atom 3. -/
theorem coreDegree_VII_3 (mask : ℕ → ℕ) :
    coreDegree .VII mask 3 = mask 0+2*mask 2+mask 8 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VII incidence row at atom 4. -/
theorem coreDegree_VII_4 (mask : ℕ → ℕ) :
    coreDegree .VII mask 4 = 2*mask 5+2*mask 6 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VII incidence row at atom 5. -/
theorem coreDegree_VII_5 (mask : ℕ → ℕ) :
    coreDegree .VII mask 5 = 2*mask 4+mask 6+mask 7 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VII incidence row at atom 6. -/
theorem coreDegree_VII_6 (mask : ℕ → ℕ) :
    coreDegree .VII mask 6 = 2*mask 4+mask 5+mask 8 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VII incidence row at atom 7. -/
theorem coreDegree_VII_7 (mask : ℕ → ℕ) :
    coreDegree .VII mask 7 = mask 2+mask 5+mask 8+mask 9 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VII incidence row at atom 8. -/
theorem coreDegree_VII_8 (mask : ℕ → ℕ) :
    coreDegree .VII mask 8 = mask 3+mask 6+mask 7+mask 10 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VII incidence row at atom 9. -/
theorem coreDegree_VII_9 (mask : ℕ → ℕ) :
    coreDegree .VII mask 9 = mask 1+mask 7+2*mask 10 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VII incidence row at atom 10. -/
theorem coreDegree_VII_10 (mask : ℕ → ℕ) :
    coreDegree .VII mask 10 = mask 1+mask 8+2*mask 9 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VIII incidence row at atom 0. -/
theorem coreDegree_VIII_0 (mask : ℕ → ℕ) :
    coreDegree .VIII mask 0 = mask 2+mask 6 := by
  simp [coreDegree,VineType.template]

/-- The exact type-VIII incidence row at atom 1. -/
theorem coreDegree_VIII_1 (mask : ℕ → ℕ) :
    coreDegree .VIII mask 1 = mask 4+mask 5 := by
  simp [coreDegree,VineType.template]

/-- The exact type-VIII incidence row at atom 2. -/
theorem coreDegree_VIII_2 (mask : ℕ → ℕ) :
    coreDegree .VIII mask 2 = mask 0+2*mask 3+mask 4 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VIII incidence row at atom 3. -/
theorem coreDegree_VIII_3 (mask : ℕ → ℕ) :
    coreDegree .VIII mask 3 = 2*mask 2+mask 5+mask 7 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VIII incidence row at atom 4. -/
theorem coreDegree_VIII_4 (mask : ℕ → ℕ) :
    coreDegree .VIII mask 4 = mask 1+mask 2+2*mask 5 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VIII incidence row at atom 5. -/
theorem coreDegree_VIII_5 (mask : ℕ → ℕ) :
    coreDegree .VIII mask 5 = mask 1+mask 3+2*mask 4 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VIII incidence row at atom 6. -/
theorem coreDegree_VIII_6 (mask : ℕ → ℕ) :
    coreDegree .VIII mask 6 = mask 0+2*mask 7+mask 8 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VIII incidence row at atom 7. -/
theorem coreDegree_VIII_7 (mask : ℕ → ℕ) :
    coreDegree .VIII mask 7 = mask 3+2*mask 6+mask 9 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VIII incidence row at atom 8. -/
theorem coreDegree_VIII_8 (mask : ℕ → ℕ) :
    coreDegree .VIII mask 8 = mask 6+mask 9+2*mask 10 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VIII incidence row at atom 9. -/
theorem coreDegree_VIII_9 (mask : ℕ → ℕ) :
    coreDegree .VIII mask 9 = mask 7+mask 8+2*mask 10 := by
  simp [coreDegree,VineType.template]
  all_goals omega

/-- The exact type-VIII incidence row at atom 10. -/
theorem coreDegree_VIII_10 (mask : ℕ → ℕ) :
    coreDegree .VIII mask 10 = 2*mask 8+2*mask 9 := by
  simp [coreDegree,VineType.template]
  all_goals omega

end WaveTurbulence.Vine
