/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePortSigns
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.MiniPortClassification

/-! # Graph dipoles are exactly source mini patterns: the extraction direction

Every endpoint here is an actual source leaf or branching node. The six B
codes and two A codes are the pinned B2 tables, without shape-only substitutes.
Inverse source surgery and the converse graph correspondence are separate.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- The two ordered child slots are actual partner leaves in the source garden. -/
def LeafBond {w : ℕ} (G : Garden w) (b c : GBranch G.tree) (i j : Fin 3) : Prop :=
  ∃ ℓ q : GLeaf G.tree, ℓ.toNode = b.child i ∧ q.toNode = c.child j ∧ G.pair ℓ = q

/-- A literal embedded `(1,1)` mini couple. Either root orientation is permitted. -/
def MiniAOccurrence {w : ℕ} (G : Garden w) (b c : GBranch G.tree) (k : MiniCplCode) : Prop :=
  G.sign c.toNode = -G.sign b.toNode ∧ ∀ i, LeafBond G b c i (k.partner i)

/-- A literal embedded mini tree, retaining its arbitrary lone-child subtree. -/
def MiniBOccurrence {w : ℕ} (G : Garden w) (b c : GBranch G.tree) (m : MiniTreeCode) : Prop :=
  b.child m.c = c.toNode ∧ LeafBond G b c m.red.1 m.red.2 ∧ LeafBond G b c m.green.1 m.green.2

/-- The source's two kinds of elementary embedded mini pieces, with their actual positions. -/
inductive MiniOccurrence {w : ℕ} (G : Garden w)
  | opA (b c : GBranch G.tree) (k : MiniCplCode) : MiniAOccurrence G b c k → MiniOccurrence G
  | opB (b c : GBranch G.tree) (m : MiniTreeCode) : MiniBOccurrence G b c m → MiniOccurrence G

def MiniOccurrence.first {w : ℕ} {G : Garden w} : MiniOccurrence G → GBranch G.tree
  | .opA b _ _ _ => b
  | .opB b _ _ _ => b

def MiniOccurrence.second {w : ℕ} {G : Garden w} : MiniOccurrence G → GBranch G.tree
  | .opA _ c _ _ => c
  | .opB _ c _ _ => c

theorem miniBPerm_continuing (m : MiniTreeCode) : miniBPerm m m.c.succ = 0 := by
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;> decide

theorem miniBPerm_red (m : MiniTreeCode) : miniBPerm m m.red.1.succ = m.red.2.succ := by
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;> decide

theorem miniBPerm_green (m : MiniTreeCode) : miniBPerm m m.green.1.succ = m.green.2.succ := by
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;> decide

/-- The A table supplies all actual paired leaves of the embedded source mini couple. -/
theorem BranchDipole.miniA_of_perm {w : ℕ} {G : Garden w} (D : BranchDipole G)
    (hf : D.free = 0) (k : MiniCplCode) (hp : D.perm = miniAPerm k)
    (hs : G.sign D.v.toNode = -G.sign D.u.toNode) : MiniAOccurrence G D.u D.v k := by
  refine ⟨hs,?_⟩
  intro i
  have hi : i.succ ≠ D.free := by rw [hf]; exact Fin.succ_ne_zero i
  have he := D.internal i.succ hi
  rw [hp] at he
  change portMate G (.inr (D.u,i.succ)) = .inr (D.v,(k.partner i).succ) at he
  exact paired_leaves_of_child_bond G D.u D.v i (k.partner i) he

/-- The B table supplies the actual continuing edge and both source leaf pairs. -/
theorem BranchDipole.miniB_of_perm {w : ℕ} {G : Garden w} (D : BranchDipole G)
    (hf : D.free = 0) (m : MiniTreeCode) (hp : D.perm = miniBPerm m) : MiniBOccurrence G D.u D.v m := by
  have hc := D.internal m.c.succ (by rw [hf]; exact Fin.succ_ne_zero m.c)
  have hr := D.internal m.red.1.succ (by rw [hf]; exact Fin.succ_ne_zero m.red.1)
  have hg := D.internal m.green.1.succ (by rw [hf]; exact Fin.succ_ne_zero m.green.1)
  rw [hp,miniBPerm_continuing] at hc
  rw [hp,miniBPerm_red] at hr
  rw [hp,miniBPerm_green] at hg
  exact ⟨(portMate_child_parent_iff G D.u D.v m.c).mp hc,
    paired_leaves_of_child_bond G D.u D.v m.red.1 m.red.2 hr,
    paired_leaves_of_child_bond G D.u D.v m.green.1 m.green.2 hg⟩

/-- A parent-free source orientation is one of the exact eight mini pieces. -/
theorem BranchDipole.mini_of_free_zero {w : ℕ} {G : Garden w} (D : BranchDipole G)
    (hG : G.IsPlain) (hf : D.free = 0) :
    (∃ k : MiniCplCode, MiniAOccurrence G D.u D.v k) ∨
      ∃ m : MiniTreeCode, MiniBOccurrence G D.u D.v m := by
  obtain ⟨k,hk,hs⟩ | ⟨m,hm,_⟩ := mini_port_classification (G.sign D.u.toNode) (G.sign D.v.toNode)
    D.perm (D.internal_signs hG hf)
  · exact Or.inl ⟨k,D.miniA_of_perm hf k hk hs⟩
  · exact Or.inr ⟨m,D.miniB_of_perm hf m hm⟩

/-- Every source dipole yields an actual mini occurrence at the same unordered pair of branches. -/
theorem BranchDipole.exists_sourceMini {w : ℕ} {G : Garden w} (D : BranchDipole G) (hG : G.IsPlain) :
    ∃ o : MiniOccurrence G,
      (o.first = D.u ∧ o.second = D.v) ∨ (o.first = D.v ∧ o.second = D.u) := by
  rcases D.free_parent with hf | hf
  · obtain ⟨k,hk⟩ | ⟨m,hm⟩ := D.mini_of_free_zero hG hf
    · exact ⟨.opA D.u D.v k hk,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨.opB D.u D.v m hm,Or.inl ⟨rfl,rfl⟩⟩
  · have hf' : D.flip.free = 0 := hf
    obtain ⟨k,hk⟩ | ⟨m,hm⟩ := D.flip.mini_of_free_zero hG hf'
    · exact ⟨.opA D.v D.u k hk,Or.inr ⟨rfl,rfl⟩⟩
    · exact ⟨.opB D.v D.u m hm,Or.inr ⟨rfl,rfl⟩⟩

/-- Every graph redex of an ordinary source garden is a genuine embedded source mini piece. -/
theorem LabelledGarden.sourceMini_of_graph_dipole {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    (hG : G.garden.IsPlain) (D : Dipole G.graph.mate) : Nonempty (MiniOccurrence G.garden) := by
  obtain ⟨E,_⟩ := G.branchDipole_of_graph hG D
  obtain ⟨o,_⟩ := E.exists_sourceMini hG
  exact ⟨o⟩

end WaveTurbulence.Reg.Skeleton
