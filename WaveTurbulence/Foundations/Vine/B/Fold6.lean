/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Fold5
import Mathlib.Tactic

/-!
# VINE-B Part I (6): one more splice, the core facts

For a fold state `st` with invariant `T : FoldInv P st`, an unspliced block `u` (`hU`, `hdis`), the pulled-back block
`(a', b')` of `st.G` and the actual splice `clSplicedGardenOfSlots hB' hCL' D`, the composite node map
`T.node ∘ spNode` satisfies the facts needed for `FoldInv (P ∨ = u)`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.Mole WaveTurbulence.RegRed WaveTurbulence.RedSplice

variable {w : ℕ} {G0 : Garden w} {P : CLBlock G0 → Prop} {st : SpState G0} (T : FoldInv P st)
  (u : CLBlock G0) {a' b' : GBranch st.G.tree}
  (hB' : st.G.molecule.IsBlock (st.M.pb u.atoms) a' b') (hCL' : CLParentPattern st.G (st.M.pb u.atoms) a' b')
  (D : CLSpliceSlots st.G (st.M.pb u.atoms) a' b')

/-- The pulled-back block of `st.G`. -/
noncomputable def pbBlock : CLBlock st.G := ⟨st.M.pb u.atoms, a', b', hB', hCL'⟩

theorem core_range (hU : ∀ v ∈ u.atoms, st.cls v = none) (ha : st.M.ob a' = u.upper) (x : GNode G0.tree) :
    (∃ y, T.node (spNode (clSpliceBoundary hB' hCL' D) y) = x) ↔ RetP (fun u1 => P u1 ∨ u1 = u) x := by
  have hreal := real_iff_bnode (pbBlock u hB' hCL') D
  have hbr : T.node a'.toNode = u.upper.toNode := by rw [← T.br_node, ha]
  constructor
  · rintro ⟨y, rfl⟩ u1 hu1
    rcases hu1 with hu1 | rfl
    · exact (T.range _).mp ⟨_, rfl⟩ u1 hu1
    · rcases (spNode_range (clSpliceBoundary hB' hCL' D) _).mp ⟨y, rfl⟩ with h | h | h
      · left
        rw [T.bridge u1 hU]
        intro hm
        exact ((hreal _).mp hm).1 |> fun hd => h hd
      · right; rw [h]; exact hbr
      · left
        rw [T.bridge u1 hU]
        intro hm
        exact ((hreal _).mp hm).2 h
  · intro hx
    obtain ⟨z0, hz0⟩ := (T.range x).mpr (fun u1 hu1 => hx u1 (Or.inl hu1))
    have hu := hx u (Or.inr rfl)
    obtain ⟨y, hy⟩ : ∃ y, spNode (clSpliceBoundary hB' hCL' D) y = z0 := by
      rw [spNode_range]
      by_cases hz : z0 = a'.toNode
      · exact Or.inr (Or.inl hz)
      · have hnr : z0 ∉ clRealizationNodes st.G (st.M.pb u.atoms) := by
          intro hm
          have : x ∈ clRealizationNodes G0 u.atoms := by rw [← hz0, T.bridge u hU]; exact hm
          rcases hu with hu | hu
          · exact hu this
          · apply hz
            apply T.inj
            rw [hz0, hu, hbr]
        by_contra hcon
        push Not at hcon
        apply hnr
        exact (hreal z0).mpr ⟨hcon.1, by
          rintro ⟨i, hi⟩
          exact hcon.2.2 i hi⟩
    exact ⟨y, by rw [hy, hz0]⟩


theorem stepB_ne_crown_of_ob (ha : st.M.ob a' = u.upper) (c : GBranch (clSplicedGardenOfSlots hB' hCL' D).tree)
    (u1 : CLBlock G0) (hc : st.M.ob (stepB hB' hCL' D c) ≠ u1.upper) (hu1 : u1 = u) :
    c ≠ spliceCrownBranch (clSpliceBoundary hB' hCL' D) := by
  rintro rfl
  have h1 : stepB hB' hCL' D (spliceCrownBranch (clSpliceBoundary hB' hCL' D)) = a' :=
    clSplicedBranchName_crown hB' hCL' D
  apply hc
  rw [h1, ha, hu1]

theorem core_child (ha : st.M.ob a' = u.upper) (c : GBranch (clSplicedGardenOfSlots hB' hCL' D).tree)
    (i : Fin 3) (hc : ∀ u1 : CLBlock G0, (P u1 ∨ u1 = u) → st.M.ob (stepB hB' hCL' D c) ≠ u1.upper) :
    T.node (spNode (clSpliceBoundary hB' hCL' D) (c.child i)) = (st.M.ob (stepB hB' hCL' D c)).child i := by
  have hcr := stepB_ne_crown_of_ob u hB' hCL' D ha c u (hc u (Or.inr rfl)) rfl
  have h1 := spNode_child (clSpliceBoundary hB' hCL' D) c (stepB hB' hCL' D c)
    (congrArg Subtype.val (stepB_node hB' hCL' D c)) hcr i
  exact (congrArg T.node h1).trans (T.child (stepB hB' hCL' D c) i (fun u1 hu1 => hc u1 (Or.inl hu1)))

theorem ob_not_upper (hdis : ∀ u1, P u1 → Disjoint u1.atoms u.atoms) {v : GBranch G0.tree} (hv : v ∈ u.atoms)
    (u1 : CLBlock G0) (hu1 : P u1) : v ≠ u1.upper := by
  rintro rfl
  exact Finset.disjoint_left.mp (hdis u1 hu1) u1.isBlock.2.1 hv

theorem core_bnode (hdis : ∀ u1, P u1 → Disjoint u1.atoms u.atoms) (hU : ∀ v ∈ u.atoms, st.cls v = none)
    (ha : st.M.ob a' = u.upper) (hb : st.M.ob b' = u.lower) (i : Fin 3) :
    T.node ((clSpliceBoundary hB' hCL' D).node i) ∈ crownSet u := by
  have hcr : (clSpliceBoundary hB' hCL' D).node i ∈ crownSet (pbBlock u hB' hCL') :=
    (crownSet_iff_bnode (pbBlock u hB' hCL') D _).mpr ⟨i, rfl⟩
  have key : ∀ (v : GBranch st.G.tree) (j : Fin 3), st.M.ob v ∈ u.atoms →
      (v.child j) ∈ crownSet (pbBlock u hB' hCL') → T.node (v.child j) ∈ crownSet u := by
    intro v j hv hx
    have hx' := crown_not_real (pbBlock u hB' hCL') hx
    rw [T.child v j (fun u1 hu1 => ob_not_upper u hdis hv u1 hu1)]
    have hnr : (st.M.ob v).child j ∉ clRealizationNodes G0 u.atoms := by
      rw [← T.child v j (fun u1 hu1 => ob_not_upper u hdis hv u1 hu1), T.bridge u hU]
      exact hx'
    rcases ext_child u hv j hnr with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩
    · left; rw [h1, h2]
    · right; left; rw [h1, h2]
    · right; right; rw [h1, h2]
  have hau : st.M.ob a' ∈ u.atoms := ha ▸ upper_mem u
  have hbu : st.M.ob b' ∈ u.atoms := hb ▸ lower_mem u
  rcases hcr with h | h | h
  · rw [h]; exact key a' _ hau (Or.inl rfl)
  · rw [h]; exact key b' _ hbu (Or.inr (Or.inl rfl))
  · rw [h]; exact key b' _ hbu (Or.inr (Or.inr rfl))


theorem core_crown (hdis : ∀ u1, P u1 → Disjoint u1.atoms u.atoms) (hU : ∀ v ∈ u.atoms, st.cls v = none)
    (ha : st.M.ob a' = u.upper) (hb : st.M.ob b' = u.lower)
    (c : GBranch (clSplicedGardenOfSlots hB' hCL' D).tree) (u1 : CLBlock G0) (hu1 : P u1 ∨ u1 = u)
    (hc : st.M.ob (stepB hB' hCL' D c) = u1.upper) (i : Fin 3) :
    T.node (spNode (clSpliceBoundary hB' hCL' D) (c.child i)) ∈ crownSet u1 := by
  have hcrown : stepB hB' hCL' D (spliceCrownBranch (clSpliceBoundary hB' hCL' D)) = a' :=
    clSplicedBranchName_crown hB' hCL' D
  rcases hu1 with hu1 | hu1
  · have hcr : c ≠ spliceCrownBranch (clSpliceBoundary hB' hCL' D) := by
      rintro rfl
      rw [hcrown, ha] at hc
      exact ob_not_upper u hdis (upper_mem u) u1 hu1 hc
    have h1 := spNode_child (clSpliceBoundary hB' hCL' D) c (stepB hB' hCL' D c)
      (congrArg Subtype.val (stepB_node hB' hCL' D c)) hcr i
    exact (congrArg T.node h1) ▸ T.crown (stepB hB' hCL' D c) u1 hu1 hc i
  · rw [hu1] at hc ⊢
    have hcc : c = spliceCrownBranch (clSpliceBoundary hB' hCL' D) := by
      apply stepB_inj hB' hCL' D
      rw [hcrown]
      apply st.M.ob_inj
      rw [hc, ha]
    rw [hcc]
    have h1 := spNode_crown_child (clSpliceBoundary hB' hCL' D) i
    exact (congrArg T.node h1) ▸ core_bnode T u hB' hCL' D hdis hU ha hb i

end WaveTurbulence.VineB
