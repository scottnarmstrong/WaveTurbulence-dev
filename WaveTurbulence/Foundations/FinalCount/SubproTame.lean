/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
public import WaveTurbulence.Foundations.WaveB.Lemmas
import Mathlib.Tactic

/-!
# SUBPRO (S4): TARGET `subpro` (3), the degenerate non-hinge atoms are tame (L2044)

For a plain garden `G` and an integer decoration `z` with `ε̃_z ≠ 0` (`splicedEpsilon`), every non-hinge atom
`v` having a pair of darts of opposite directions with equal bond labels has all its bond labels equal, and (if
`d(v) < 4`) equal to a root value.  Pure garden statement: it uses only the tree structure of `G`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset

variable {w d : ℕ}

/-- The node carrying a dart (the child end of a PC bond, the leaf of an LP dart). -/
def dartNode (G : Garden w) : GardenDart G → GNode G.tree
  | .inl (c, _) => c.1.toNode
  | .inr ℓ => ℓ.1.toNode

theorem bondIndex_eq (G : Garden w) (z : GNode G.tree → (Fin d → ℤ)) (x : GardenDart G) :
    bondIndex G z x = z (dartNode G x) := by
  rcases x with ⟨c, b⟩ | ℓ <;> rfl

theorem exists_child_of_parent {tree : Fin w → TTree} {a : GNode tree} (h : a.1.2 ≠ []) {v : GBranch tree}
    (hv : GNode.parent a h = v) : ∃ i : Fin 3, a = v.child i := by
  refine ⟨a.1.2.getLast h, Subtype.ext ?_⟩
  have := congrArg Subtype.val hv
  simp only [GNode.parent] at this
  show a.1 = (v.1.1, v.1.2 ++ [a.1.2.getLast h])
  rw [← this]
  exact Prod.ext rfl (List.dropLast_append_getLast h).symm

theorem child_ne_self {tree : Fin w → TTree} (v : GBranch tree) (i : Fin 3) : v.toNode ≠ v.child i := by
  intro h
  have := congrArg (fun a : GNode tree => a.1.2.length) h
  simp [GBranch.toNode, GBranch.child] at this

theorem child_inj {tree : Fin w → TTree} (v : GBranch tree) {i j : Fin 3} (h : v.child i = v.child j) : i = j := by
  have := congrArg (fun a : GNode tree => a.1.2) h
  simpa [GBranch.child] using this

theorem child_path_ne_nil {tree : Fin w → TTree} (v : GBranch tree) (i : Fin 3) : (v.child i).1.2 ≠ [] := by
  simp [GBranch.child]

theorem dart_cases (G : Garden w) {v : GBranch G.tree} {x : GardenDart G} (hx : G.molecule.atom x = v) :
    (∃ h : v.1.2 ≠ [], x = Sum.inl (⟨v, h⟩, false)) ∨
      ∃ i : Fin 3, dartNode G x = v.child i ∧ G.molecule.out x = decide (G.sign (v.child i) ≠ 1) := by
  rcases x with ⟨⟨c, hc⟩, b⟩ | ℓ
  · cases b
    · left
      have : c = v := hx
      subst this
      exact ⟨hc, rfl⟩
    · right
      obtain ⟨i, hi⟩ := exists_child_of_parent hc hx
      refine ⟨i, hi, ?_⟩
      show decide (G.sign c.toNode ≠ 1) = _
      have : c.toNode = v.child i := hi
      rw [this]
  · right
    obtain ⟨i, hi⟩ := exists_child_of_parent ℓ.2.2.1 hx
    refine ⟨i, hi, ?_⟩
    show decide (G.sign ℓ.1.toNode ≠ 1) = _
    have : ℓ.1.toNode = v.child i := hi
    rw [this]

theorem sign_child (G : Garden w) (v : GBranch G.tree) :
    G.sign (v.child 0) = G.sign v.toNode ∧ G.sign (v.child 1) = -G.sign v.toNode ∧
      G.sign (v.child 2) = G.sign v.toNode :=
  nodeSign_child G.sig v

theorem epsCoef_ne_zero {n₁ n₂ n₃ : Fin d → ℤ} (h : epsCoef n₁ n₂ n₃ ≠ 0) :
    (n₂ ≠ n₁ ∧ n₂ ≠ n₃) ∨ (n₁ = n₂ ∧ n₂ = n₃) := by
  unfold epsCoef at h
  split_ifs at h with h1 h2
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd rfl h

/-- Degree at least four when every slot carries a dart. -/
theorem four_le_deg (G : Garden w) {v : GBranch G.tree} (hv : v.1.2 ≠ [])
    (hc : ∀ i : Fin 3, ∃ x, G.molecule.atom x = v ∧ dartNode G x = v.child i) : 4 ≤ G.molecule.deg v := by
  classical
  choose f hf1 hf2 using hc
  let g : Option (Fin 3) → GardenDart G := fun s => match s with
    | none => Sum.inl (⟨v, hv⟩, false)
    | some i => f i
  have hg : ∀ s, G.molecule.atom (g s) = v ∧ dartNode G (g s) = (match s with
      | none => v.toNode | some i => v.child i) := by
    intro s
    cases s with
    | none => exact ⟨rfl, rfl⟩
    | some i => exact ⟨hf1 i, hf2 i⟩
  have hinj : Function.Injective g := by
    intro s t hst
    have h2 := congrArg (dartNode G) hst
    rw [(hg s).2, (hg t).2] at h2
    cases s with
    | none =>
      cases t with
      | none => rfl
      | some j => exact absurd h2 (child_ne_self v j)
    | some i =>
      cases t with
      | none => exact absurd h2.symm (child_ne_self v i)
      | some j => exact congrArg some (child_inj v h2)
  have : (Finset.univ : Finset (Option (Fin 3))).card ≤ (G.molecule.dartsAt v).card := by
    apply Finset.card_le_card_of_injOn g
    · intro s _
      simp [Molecule.dartsAt, (hg s).1]
    · intro s _ t _ h
      exact hinj h
  have hc4 : (Finset.univ : Finset (Option (Fin 3))).card = 4 := by simp
  unfold Molecule.deg
  omega


theorem latticePoint_inj {L : ℝ} (hL : L ≠ 0) {n m : Fin d → ℤ} (h : latticePoint L n = latticePoint L m) :
    n = m := by
  funext j
  have := congrArg (fun p : Mom d => p j) h
  simp only [latticePoint] at this
  have h2 : (n j : ℝ) = m j := by
    have := this
    field_simp at this
    exact this
  exact_mod_cast h2

theorem slot_cases (s : Option (Fin 3)) : s = none ∨ s = some 0 ∨ s = some 1 ∨ s = some 2 := by
  rcases s with _ | i
  · simp
  · fin_cases i <;> simp

theorem opposite_eq {p c0 c1 c2 : Fin d → ℤ} (hdec : p = c0 - c1 + c2) (heps : epsCoef c0 c1 c2 ≠ 0)
    (σ : ℤˣ) (s t : Option (Fin 3)) (lab : Option (Fin 3) → (Fin d → ℤ))
    (hlab : lab none = p ∧ lab (some 0) = c0 ∧ lab (some 1) = c1 ∧ lab (some 2) = c2)
    (outS : Option (Fin 3) → Bool)
    (ho : outS none = decide (σ = 1) ∧ outS (some 0) = decide (σ ≠ 1) ∧ outS (some 1) = decide (-σ ≠ 1) ∧
      outS (some 2) = decide (σ ≠ 1))
    (hout : outS s ≠ outS t) (hl : lab s = lab t) : c0 = c1 ∧ c1 = c2 ∧ p = c0 := by
  obtain ⟨l0, l1, l2, l3⟩ := hlab
  obtain ⟨o0, o1, o2, o3⟩ := ho
  rcases epsCoef_ne_zero heps with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exfalso
    have e0 : p = c0 → c1 = c2 := fun h => by linear_combination hdec - h
    have e2 : p = c2 → c0 = c1 := fun h => by linear_combination h - hdec
    have key : outS none = true ∧ outS (some 0) = false ∧ outS (some 1) = true ∧ outS (some 2) = false ∨
        outS none = false ∧ outS (some 0) = true ∧ outS (some 1) = false ∧ outS (some 2) = true := by
      rcases Int.units_eq_one_or σ with rfl | rfl
      · left; rw [o0, o1, o2, o3]; decide
      · right; rw [o0, o1, o2, o3]; decide
    rcases slot_cases s with rfl | rfl | rfl | rfl <;> rcases slot_cases t with rfl | rfl | rfl | rfl <;>
      simp only [l0, l1, l2, l3] at hl <;>
      first
      | exact hout rfl
      | (rcases key with ⟨k0, k1, k2, k3⟩ | ⟨k0, k1, k2, k3⟩ <;> simp [k0, k1, k2, k3] at hout <;> done)
      | exact h2 (e0 hl)
      | exact h2 (e0 hl.symm)
      | exact h1 (e2 hl).symm
      | exact h1 (e2 hl.symm).symm
      | exact h1 hl
      | exact h1 hl.symm
      | exact h2 hl
      | exact h2 hl.symm
  · subst h1; subst h2
    refine ⟨rfl, rfl, ?_⟩
    rw [hdec]; abel


theorem parent_child_eq {tree : Fin w → TTree} (v : GBranch tree) (i : Fin 3) (a : GNode tree)
    (ha : a = v.child i) (h : a.1.2 ≠ []) : GNode.parent a h = v := by
  subst ha
  apply Subtype.ext
  show ((v.child i).1.1, (v.child i).1.2.dropLast) = v.1
  simp [GBranch.child]

theorem dart_of_branching (G : Garden w) (v : GBranch G.tree) (i : Fin 3)
    (hb : (v.child i).1.2 ∈ (G.tree (v.child i).1.1).branching) :
    ∃ x, G.molecule.atom x = v ∧ dartNode G x = v.child i := by
  let c : GBranch G.tree := ⟨(v.child i).1, hb⟩
  have hne : c.1.2 ≠ [] := child_path_ne_nil v i
  refine ⟨Sum.inl (⟨c, hne⟩, true), ?_, rfl⟩
  exact parent_child_eq v i c.toNode rfl hne

theorem dart_of_leaf (G : Garden w) (hG : G.IsPlain) (v : GBranch G.tree) (i : Fin 3)
    (hl : (v.child i).1.2 ∈ (G.tree (v.child i).1.1).leaves)
    (hp : (G.pair ⟨(v.child i).1, hl⟩).1.2 ≠ []) :
    ∃ x, G.molecule.atom x = v ∧ dartNode G x = v.child i := by
  let ℓ : GLeaf G.tree := ⟨(v.child i).1, hl⟩
  have hne : ℓ.1.2 ≠ [] := child_path_ne_nil v i
  refine ⟨Sum.inr ⟨ℓ, hG ℓ, hne, hp⟩, ?_, rfl⟩
  exact parent_child_eq v i ℓ.toNode rfl hne

theorem slot_of_dart (G : Garden w) {v : GBranch G.tree} {x : GardenDart G} (hx : G.molecule.atom x = v)
    (z : GNode G.tree → (Fin d → ℤ)) :
    ∃ s : Option (Fin 3), bondIndex G z x = (match s with | none => z v.toNode | some i => z (v.child i)) ∧
      G.molecule.out x = (match s with
        | none => decide (G.sign v.toNode = 1) | some i => decide (G.sign (v.child i) ≠ 1)) := by
  rcases dart_cases G hx with ⟨h, rfl⟩ | ⟨i, h1, h2⟩
  · exact ⟨none, rfl, rfl⟩
  · exact ⟨some i, by rw [bondIndex_eq, h1], h2⟩

/-- **TARGET `subpro` (3), L2044, for the garden.** A non-hinge atom of a plain garden carrying a pair of darts of
opposite directions with equal bond labels is tame in every decoration with `ε̃ ≠ 0`. -/
theorem tame_of_eps (G : Garden w) (hG : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0)
    {hinges : Finset (GBranch G.tree)} (hε : splicedEpsilon G hinges z.1 ≠ 0)
    {v : GBranch G.tree} (hv : v ∉ hinges)
    (hgap : ∃ x y, TripleAt G v x y ∧ Molecule.gapAt L base (bondIndex G z.1) x y = 0) :
    G.molecule.IsTame L base (Finset.univ.image (fun i => base + latticePoint L (roots i)))
      (bondIndex G z.1) v := by
  classical
  obtain ⟨x, y, ⟨hxa, hya, hyx, hout⟩, hg⟩ := hgap
  have hε' : epsCoef (z.1 (v.child 0)) (z.1 (v.child 1)) (z.1 (v.child 2)) ≠ 0 := by
    unfold splicedEpsilon at hε
    exact (Finset.prod_ne_zero_iff.mp hε) v (by simp [hv])
  have hdec : z.1 v.toNode = z.1 (v.child 0) - z.1 (v.child 1) + z.1 (v.child 2) := z.2.1.1 v
  have hxy : bondIndex G z.1 x = bondIndex G z.1 y := by
    unfold Molecule.gapAt Molecule.kvec at hg
    exact latticePoint_inj hL (add_left_cancel (sub_eq_zero.mp hg))
  obtain ⟨s, hs1, hs2⟩ := slot_of_dart G hxa z.1
  obtain ⟨t, ht1, ht2⟩ := slot_of_dart G hya z.1
  let lab : Option (Fin 3) → (Fin d → ℤ) := fun s => match s with | none => z.1 v.toNode | some i => z.1 (v.child i)
  let outS : Option (Fin 3) → Bool := fun s => match s with
    | none => decide (G.sign v.toNode = 1) | some i => decide (G.sign (v.child i) ≠ 1)
  obtain ⟨sg0, sg1, sg2⟩ := sign_child G v
  have key := opposite_eq (p := z.1 v.toNode) (c0 := z.1 (v.child 0)) (c1 := z.1 (v.child 1))
    (c2 := z.1 (v.child 2)) hdec hε' (G.sign v.toNode) s t lab ⟨rfl, rfl, rfl, rfl⟩ outS
    ⟨rfl, by simp only [outS, sg0], by simp only [outS, sg1], by simp only [outS, sg2]⟩
    (by intro h; apply hout; rw [hs2, ht2]; exact h) (by exact hs1.symm.trans (hxy.trans ht1))
  obtain ⟨e01, e12, ep⟩ := key
  have hall : ∀ s : Option (Fin 3), lab s = z.1 v.toNode := by
    intro s
    rcases slot_cases s with rfl | rfl | rfl | rfl
    · rfl
    · exact ep.symm
    · exact (e01.symm.trans ep.symm)
    · exact (e12.symm.trans (e01.symm.trans ep.symm))
  have hdart : ∀ x', G.molecule.atom x' = v → bondIndex G z.1 x' = z.1 v.toNode := by
    intro x' hx'
    obtain ⟨s', hs', -⟩ := slot_of_dart G hx' z.1
    rw [hs']; exact hall s'
  refine ⟨fun x1 x2 h1 h2 => ?_, fun hdeg x' hx' => ?_⟩
  · unfold Molecule.kvec; rw [hdart x1 h1, hdart x2 h2]
  · have hroot : ∃ j, z.1 v.toNode = roots j := by
      by_cases hr : v.1.2 = []
      · refine ⟨v.1.1, ?_⟩
        have : v.toNode = GNode.root G.tree v.1.1 := Subtype.ext (Prod.ext rfl hr)
        rw [this]; exact z.2.2.1 v.1.1
      · by_contra hno
        by_cases hch : ∀ i : Fin 3, ∃ x'', G.molecule.atom x'' = v ∧ dartNode G x'' = v.child i
        · exact absurd (four_le_deg G hr hch) (not_le.mpr hdeg)
        · obtain ⟨i, hi⟩ := not_forall.mp hch
          have hmem := (v.child i).2
          rcases (TTree.mem_nodes_iff _ _).1 hmem with hl | hb
          · by_cases hp : (G.pair ⟨(v.child i).1, hl⟩).1.2 = []
            · apply hno
              refine ⟨(G.pair ⟨(v.child i).1, hl⟩).1.1, ?_⟩
              have h1 := hall (some i)
              simp only [lab] at h1
              rw [← h1]
              have h2 := z.2.1.2 ⟨(v.child i).1, hl⟩
              have h3 : (G.pair ⟨(v.child i).1, hl⟩).toNode = GNode.root G.tree (G.pair ⟨(v.child i).1, hl⟩).1.1 :=
                Subtype.ext (Prod.ext rfl hp)
              have h4 := z.2.2.1 (G.pair ⟨(v.child i).1, hl⟩).1.1
              rw [← h3] at h4
              rw [← h4, ← h2]
              rfl
            · exact (hi (dart_of_leaf G hG v i hl hp)).elim
          · exact (hi (dart_of_branching G v i hb)).elim
    obtain ⟨j, hj⟩ := hroot
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨j, ?_⟩
    unfold Molecule.kvec
    rw [hdart x' hx', hj]

end WaveTurbulence.Subpro
