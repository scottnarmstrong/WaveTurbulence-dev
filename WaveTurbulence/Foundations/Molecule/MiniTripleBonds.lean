/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.JointBondBounds
public import WaveTurbulence.Foundations.Molecule.PrimeGardenDefs

/-! # Every embedded mini piece has three actual bonds between its branches

TARGET prime-garden clause of twist. The predicates here are the exact
accepted SKELETON source mini-couple and mini-tree definitions.
-/

public section
namespace WaveTurbulence.Twist
open TTree Reg.Skeleton
variable {w : ℕ} (G : Garden w)

/-- An actual paired child-leaf bond gives its actual LP dart and ordered position. -/
theorem leafBond_dart (hplain : G.IsPlain) {b c : GBranch G.tree} {i j : Fin 3}
    (h : LeafBond G b c i j) :
    ∃ x : GardenDart G, G.molecule.atom x = b ∧ G.molecule.atom (G.molecule.mate x) = c ∧
      Mole.dartPosition G x = i.succ := by
  obtain ⟨l,q,hl,hq,hpair⟩ := h
  have hn : l.1.2 ≠ [] := by
    change l.toNode.1.2 ≠ []
    rw [hl]
    exact Mole.child_nonroot G b i
  have hp : (G.pair l).1.2 ≠ [] := by
    rw [hpair]
    change q.toNode.1.2 ≠ []
    rw [hq]
    exact Mole.child_nonroot G c j
  let x : GardenDart G := .inr ⟨l,hplain l,hn,hp⟩
  refine ⟨x,parent_eq_of_child hn hl,?_,?_⟩
  · change GNode.parent (G.pair l).toNode hp = c
    exact parent_eq_of_child hp (by rw [hpair]; exact hq)
  · apply Fin.ext
    change (l.1.2.getLast hn).val+1 = i.val+1
    have hh : l.1.2 = b.1.2 ++ [i] := congrArg (fun n : GNode G.tree => n.1.2) hl
    simp [hh]

/-- An actual branch child gives its parent-end PC dart and ordered position. -/
theorem child_PC_dart {b c : GBranch G.tree} {i : Fin 3} (hc : c.toNode = b.child i) :
    ∃ x : GardenDart G, G.molecule.atom x = b ∧ G.molecule.atom (G.molecule.mate x) = c ∧
      Mole.dartPosition G x = i.succ := by
  have hn : c.1.2 ≠ [] := by
    change c.toNode.1.2 ≠ []
    rw [hc]
    exact Mole.child_nonroot G b i
  refine ⟨.inl (⟨c,hn⟩,true),parent_eq_of_child hn hc,rfl,?_⟩
  apply Fin.ext
  change (c.1.2.getLast hn).val+1 = i.val+1
  have hh : c.1.2 = b.1.2 ++ [i] := congrArg (fun n : GNode G.tree => n.1.2) hc
  simp [hh]

/-- Every mini couple has three actual parallel LP bonds. -/
theorem miniA_triple (hplain : G.IsPlain) {b c : GBranch G.tree} {k : MiniCplCode}
    (h : MiniAOccurrence G b c k) : b ≠ c ∧ TripleBond G.molecule b c := by
  have hne : b ≠ c := by
    intro he
    have hs := h.1
    rw [← he] at hs
    rcases Int.units_eq_one_or (G.sign b.toNode) with hh | hh <;> simp [hh] at hs
  have hd (i : Fin 3) := leafBond_dart G hplain (h.2 i)
  choose f ha hb hp using hd
  refine ⟨hne,f,?_,ha,hb⟩
  intro i j he
  have hh := congrArg (Mole.dartPosition G) he
  rw [hp i,hp j] at hh
  exact Fin.succ_inj.mp hh

/-- Every mini tree has one actual PC bond and two distinct LP bonds. -/
theorem miniB_triple (hplain : G.IsPlain) {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) : b ≠ c ∧ TripleBond G.molecule b c := by
  have hne : b ≠ c := by
    intro he
    exact child_ne_parent G b m.c (h.1.trans (congrArg GBranch.toNode he.symm))
  obtain ⟨x₀,ha₀,hb₀,hp₀⟩ := child_PC_dart G h.1.symm
  obtain ⟨x₁,ha₁,hb₁,hp₁⟩ := leafBond_dart G hplain h.2.1
  obtain ⟨x₂,ha₂,hb₂,hp₂⟩ := leafBond_dart G hplain h.2.2
  let f : Fin 3 → GardenDart G := ![x₀,x₁,x₂]
  let p : Fin 3 → Fin 3 := ![m.c,m.red.1,m.green.1]
  have hinj : Function.Injective p := by
    obtain ⟨c,b⟩ := m
    fin_cases c <;> fin_cases b <;> decide
  have hpos : ∀ i, Mole.dartPosition G (f i) = (p i).succ := by
    intro i; fin_cases i
    · exact hp₀
    · exact hp₁
    · exact hp₂
  refine ⟨hne,f,?_,?_,?_⟩
  · intro i j he
    apply hinj
    apply Fin.succ_inj.mp
    exact (hpos i).symm.trans ((congrArg (Mole.dartPosition G) he).trans (hpos j))
  · intro i; fin_cases i
    · exact ha₀
    · exact ha₁
    · exact ha₂
  · intro i; fin_cases i
    · exact hb₀
    · exact hb₁
    · exact hb₂

end WaveTurbulence.Twist
