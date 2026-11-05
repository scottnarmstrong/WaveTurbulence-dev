/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TypeIIScenarios

/-! # Exclusivity of the five source scenarios

TARGET molecpl (2): the local actual parent and ancestor relations give
an intrinsic code for each scenario. This proves exactness of the split.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- The scenario is detected from actual tree relations, independent of a vine realization. -/
@[expose] noncomputable def typeIIScenarioCode (b p q : GBranch G.tree) : Fin 5 := by
  classical
  exact if p.toNode.IsDesc q.toNode then
    if IsParent G q b then 2 else if IsParent G p q then 3 else 4
    else if IsParent G q b then 0 else 1

/-- Scenario (II-a) has intrinsic code zero. -/
theorem scenarioCode_A {a b p q : GBranch G.tree} (h : IsTypeIIA G a b p q) :
    typeIIScenarioCode G b p q = 0 := by
  classical
  simp [typeIIScenarioCode,h.2.2.2.1,h.1]

/-- Scenario (II-b) has intrinsic code one. -/
theorem scenarioCode_B {a b p q : GBranch G.tree} (hne : p ≠ q) (h : IsTypeIIB G a b p q) :
    typeIIScenarioCode G b p q = 1 := by
  classical
  have hq : ¬ IsParent G q b := fun hq => hne (isParent_unique G h.1 hq)
  simp [typeIIScenarioCode,h.2.2.2.1,hq]

/-- Scenario (II-c) has intrinsic code two. -/
theorem scenarioCode_C {a b p q : GBranch G.tree} (h : IsTypeIIC G a b p q) :
    typeIIScenarioCode G b p q = 2 := by
  classical
  simp [typeIIScenarioCode,isParent_desc G h.1,h.2.1]

/-- Scenario (II-d) has intrinsic code three. -/
theorem scenarioCode_D {a b p q : GBranch G.tree} (hne : p ≠ q) (h : IsTypeIID G a b p q) :
    typeIIScenarioCode G b p q = 3 := by
  classical
  have hq : ¬ IsParent G q b := fun hq => hne (isParent_unique G h.1 hq)
  simp [typeIIScenarioCode,isParent_desc G h.2.1,hq,h.2.1]

/-- Scenario (II-e) has intrinsic code four. -/
theorem scenarioCode_E {a b p q : GBranch G.tree} (hne : p ≠ q) (hpb : p ≠ b)
    (h : IsTypeIIE G a b p q) : typeIIScenarioCode G b p q = 4 := by
  classical
  have hq : ¬ IsParent G q b := fun hq => hne (isParent_unique G h.1 hq)
  have hpq : ¬ IsParent G p q := fun hpq => hpb (isParent_unique G hpq h.2.1)
  have hpd := isParent_desc G h.1
  have hqd := isParent_desc G h.2.1
  have hd : p.toNode.IsDesc q.toNode := ⟨hpd.1.trans hqd.1,hpd.2.trans hqd.2⟩
  simp [typeIIScenarioCode,hd,hq,hpq]

/-- The five source propositions, indexed in printed order. -/
@[expose] def TypeIIScenario (a b p q : GBranch G.tree) : Fin 5 → Prop :=
  ![IsTypeIIA G a b p q,IsTypeIIB G a b p q,IsTypeIIC G a b p q,
    IsTypeIID G a b p q,IsTypeIIE G a b p q]

/-- A scenario witness determines its intrinsic code. -/
theorem scenarioCode_eq {a b p q : GBranch G.tree} (hne : p ≠ q) (hpb : p ≠ b)
    {i : Fin 5} (hi : TypeIIScenario G a b p q i) : typeIIScenarioCode G b p q = i := by
  fin_cases i
  · exact scenarioCode_A G hi
  · exact scenarioCode_B G hne hi
  · exact scenarioCode_C G hi
  · exact scenarioCode_D G hne hi
  · exact scenarioCode_E G hne hpb hi

/-- Two distinct printed scenarios cannot hold for the same labeled actual branches. -/
theorem typeII_scenarios_exclusive {a b p q : GBranch G.tree} (hne : p ≠ q) (hpb : p ≠ b)
    {i j : Fin 5} (hi : TypeIIScenario G a b p q i) (hj : TypeIIScenario G a b p q j) : i = j :=
  (scenarioCode_eq G hne hpb hi).symm.trans (scenarioCode_eq G hne hpb hj)

end WaveTurbulence.Molecpl
