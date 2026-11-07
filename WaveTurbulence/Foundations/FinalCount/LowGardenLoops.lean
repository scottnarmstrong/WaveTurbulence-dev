/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGeom
public import WaveTurbulence.Foundations.FinalCount.AsmGReg1
public import WaveTurbulence.Foundations.Molecule.ChildSigns
public import WaveTurbulence.Foundations.Molecule.GardenIncidence
/-! **FINALCOUNT-ASSEMBLY (LOW-GARDEN): the epsilon-support facts at a loop atom of a garden.**

A loop of the garden molecule is a dart `.inr ℓ` whose leaf `ℓ` and its partner are two children `v.child i`, `v.child j` of the
same branching node `v` (`i ≠ j`).  Paired leaves have opposite signs, so `{i, j} ∋ 1` (the children `0`, `2` have the sign of `v`,
the child `1` the opposite one).  If `v` is not a hinge, `splicedEpsilon ≠ 0` gives `epsCoef (z c₀) (z c₁) (z c₂) ≠ 0`, which with
`z cᵢ = z cⱼ` forces `z c₀ = z c₁ = z c₂`, and the decoration identity gives `z v = z c₀`.
* `garden_loop_heq`: every dart at a loop atom carries the loop label (`LoopCtx.heq`).
* `garden_loop_det`: admissible labels are determined by their values off the loop darts (`hdet` of `countA_unloop_le`). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Molecpl
  WaveTurbulence.AtomTransport WaveTurbulence.MoleProp

section nodes
variable {w d : ℕ} {G : Garden w}

theorem eps_ne_eq {a b c : Fin d → ℤ} (h : epsCoef a b c ≠ 0) (h' : a = b ∨ b = c) : a = b ∧ b = c := by
  unfold epsCoef at h
  by_cases h1 : b ≠ a ∧ b ≠ c
  · rcases h' with e | e
    · exact absurd e.symm h1.1
    · exact absurd e h1.2
  · by_cases h2 : a = b ∧ b = c
    · exact h2
    · simp [h1, h2] at h

/-- If two distinct children of `v` carry the same label and the epsilon factor of `v` is nonzero, all three children and `v`
carry that label. -/
theorem three_children_eq {z : GNode G.tree → (Fin d → ℤ)} (hz : IsDecoration G z) (v : GBranch G.tree) (i j : Fin 3)
    (hij : i ≠ j) (hs : G.sign (v.child j) = - G.sign (v.child i)) (he : z (v.child i) = z (v.child j))
    (hε : epsCoef (z (v.child 0)) (z (v.child 1)) (z (v.child 2)) ≠ 0) :
    (∀ k, z (v.child k) = z (v.child i)) ∧ z v.toNode = z (v.child i) := by
  have hs' := (opposite_child_sign_iff G v i j).1 hs
  have hv := hz.1 v
  have key : z (v.child 0) = z (v.child 1) ∧ z (v.child 1) = z (v.child 2) := by
    fin_cases i <;> fin_cases j <;> simp at hij hs' he
    · exact eps_ne_eq hε (Or.inl he)
    · exact eps_ne_eq hε (Or.inl he.symm)
    · exact eps_ne_eq hε (Or.inr he)
    · exact eps_ne_eq hε (Or.inr he.symm)
  obtain ⟨k1, k2⟩ := key
  have hk : ∀ k : Fin 3, z (v.child k) = z (v.child 0) := by
    intro k; fin_cases k
    · rfl
    · exact k1.symm
    · exact (k1.trans k2).symm
  refine ⟨fun k => (hk k).trans (hk i).symm, ?_⟩
  rw [hv, hk i]
  rw [hk 1, hk 2]; abel

theorem parent_ne_self (a : GNode G.tree) (ha : a.1.2 ≠ []) : (GNode.parent a ha).1 ≠ a.1 := by
  intro h
  have := congrArg (fun x : Fin w × TTree.Path => x.2.length) h
  simp [GNode.parent] at this
  have : 0 < (a.1.2).length := List.length_pos_of_ne_nil ha
  omega

theorem exists_third (i j : Fin 3) : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
  revert i j; decide

theorem fin3_other (i j k m : Fin 3) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (h : m ≠ k) : m = i ∨ m = j := by
  revert i j k m; decide

theorem parent_child' (b : GBranch G.tree) (k : Fin 3) (h : (b.child k).1.2 ≠ []) : (b.child k).parent h = b :=
  Subtype.ext (Prod.ext rfl (by simp [GNode.parent, GBranch.child]))

theorem inl_dart_nonloop (c : {c : GBranch G.tree // c.1.2 ≠ []}) (b : Bool) :
    G.molecule.atom (Sum.inl (c, b)) ≠ G.molecule.atom (G.molecule.mate (Sum.inl (c, b))) := by
  have h := parent_ne_self (G := G) c.1.toNode c.2
  cases b
  · intro e
    apply h
    have e' : c.1 = GNode.parent c.1.toNode c.2 := e
    exact (congrArg Subtype.val e').symm
  · intro e
    apply h
    have e' : GNode.parent c.1.toNode c.2 = c.1 := e
    exact congrArg Subtype.val e'

/-- A node whose parent is `v` is a child of `v`. -/
theorem node_eq_child {a : GNode G.tree} (ha : a.1.2 ≠ []) {v : GBranch G.tree} (h : GNode.parent a ha = v) :
    ∃ k : Fin 3, a = v.child k :=
  ⟨_, by rw [← h]; exact (Mole.parent_child_eq_node a ha).symm⟩

end nodes

section loops
variable {R d : ℕ} {G : Garden (2 * R)}

/-- The data of a loop dart `.inr ℓ`: its node `v` and the slots `i ≠ j`. -/
theorem loop_inr_struct (ℓ : {ℓ : GLeaf G.tree // G.mark ℓ = none ∧ ℓ.1.2 ≠ [] ∧ (G.pair ℓ).1.2 ≠ []})
    (hl : G.molecule.atom (Sum.inr ℓ) = G.molecule.atom (G.molecule.mate (Sum.inr ℓ))) :
    ∃ (i j : Fin 3), i ≠ j ∧ ℓ.1.toNode = (G.molecule.atom (Sum.inr ℓ)).child i ∧
      (G.pair ℓ.1).toNode = (G.molecule.atom (Sum.inr ℓ)).child j ∧
      G.sign (G.pair ℓ.1).toNode = - G.sign ℓ.1.toNode := by
  have hp : GNode.parent ℓ.1.toNode ℓ.2.2.1 = GNode.parent (G.pair ℓ.1).toNode ℓ.2.2.2 := hl
  have hne : G.pair ℓ.1 ≠ ℓ.1 := fun h => ((G.pair_eq_iff ℓ.1).1 h) ℓ.2.1
  obtain ⟨i, hi⟩ := node_eq_child (G := G) ℓ.2.2.1 (v := GNode.parent ℓ.1.toNode ℓ.2.2.1) rfl
  obtain ⟨j, hj⟩ := node_eq_child (G := G) ℓ.2.2.2 (v := GNode.parent ℓ.1.toNode ℓ.2.2.1) hp.symm
  refine ⟨i, j, ?_, hi, hj, G.pair_sign ℓ.1 hne⟩
  rintro rfl
  apply hne
  exact (Mole.leaf_toNode_injective (hi.trans hj.symm)).symm

variable {D : SplicedKernelData G d} {C : CountingChoices G d} {L γ η : ℝ} {base : Mom d}
  {roots : Fin (2 * R) → (Fin d → ℤ)} {κ : GardenDart G → (Fin d → ℤ)}

/-- The values of an admissible decoration around a loop: all children and the node itself carry the loop label. -/
theorem loop_values (hg : CountingGeometry G C) (hD : D.hinges = C.subpro.hinges)
    {z : GenDecoration G d roots 0} (hε : splicedEpsilon G D.hinges z.1 ≠ 0)
    (ℓ : {ℓ : GLeaf G.tree // G.mark ℓ = none ∧ ℓ.1.2 ≠ [] ∧ (G.pair ℓ).1.2 ≠ []})
    (hl : G.molecule.atom (Sum.inr ℓ) = G.molecule.atom (G.molecule.mate (Sum.inr ℓ))) :
    (∀ k, z.1 ((G.molecule.atom (Sum.inr ℓ)).child k) = z.1 ℓ.1.toNode) ∧
      z.1 (G.molecule.atom (Sum.inr ℓ)).toNode = z.1 ℓ.1.toNode := by
  obtain ⟨i, j, hij, hi, hj, hs⟩ := loop_inr_struct ℓ hl
  set v := G.molecule.atom (Sum.inr ℓ) with hv
  have hvh : v ∉ D.hinges := by
    intro hh
    rw [hD] at hh
    exact hg.hingeNoLoop (Sum.inr ℓ) hh hl
  have hε' : epsCoef (z.1 (v.child 0)) (z.1 (v.child 1)) (z.1 (v.child 2)) ≠ 0 := by
    unfold splicedEpsilon at hε
    exact (Finset.prod_ne_zero_iff.1 hε) v (Finset.mem_filter.2 ⟨Finset.mem_univ _, hvh⟩)
  have he : z.1 (v.child i) = z.1 (v.child j) := by
    rw [← hi, ← hj]; exact z.2.1.2 ℓ.1
  have hs' : G.sign (v.child j) = - G.sign (v.child i) := by rw [← hi, ← hj]; exact hs
  obtain ⟨h1, h2⟩ := three_children_eq z.2.1 v i j hij hs' he hε'
  rw [hi]
  exact ⟨h1, h2⟩

/-- **`LoopCtx.heq`**: all darts at a loop atom carry the label of the loop. -/
theorem garden_loop_heq (hg : CountingGeometry G C) (hD : D.hinges = C.subpro.hinges)
    (hA : splicedCountingAdmissible G D C L γ η base roots κ) :
    ∀ y : GardenDart G, G.molecule.atom y = G.molecule.atom (G.molecule.mate y) →
      ∀ x : GardenDart G, G.molecule.atom x = G.molecule.atom y → κ x = κ y := by
  obtain ⟨⟨z, hz, hε, -⟩, -⟩ := hA
  intro y hy x hx
  rcases y with ⟨c, b⟩ | ℓ
  · exact absurd hy (inl_dart_nonloop c b)
  obtain ⟨hk, hvz⟩ := loop_values hg hD hε ℓ hy
  set v := G.molecule.atom (Sum.inr ℓ) with hv
  rw [← hz x, ← hz (Sum.inr ℓ)]
  rcases x with ⟨c, b⟩ | ℓ'
  · cases b
    · have : c.1 = v := hx
      show z.1 c.1.toNode = z.1 ℓ.1.toNode
      rw [this]; exact hvz
    · have hx' : GNode.parent c.1.toNode c.2 = v := hx
      obtain ⟨k, hk'⟩ := node_eq_child (G := G) c.2 hx'
      show z.1 c.1.toNode = z.1 ℓ.1.toNode
      rw [hk']; exact hk k
  · have hx' : GNode.parent ℓ'.1.toNode ℓ'.2.2.1 = v := hx
    obtain ⟨k, hk'⟩ := node_eq_child (G := G) ℓ'.2.2.1 hx'
    show z.1 ℓ'.1.toNode = z.1 ℓ.1.toNode
    rw [hk']; exact hk k

/-- **`hdet`**: two admissible decorations that agree off the loop darts are equal. -/
theorem garden_loop_det (hp : G.IsPlain) (hg : CountingGeometry G C) (hD : D.hinges = C.subpro.hinges)
    {κ₁ κ₂ : GardenDart G → (Fin d → ℤ)}
    (hA₁ : splicedCountingAdmissible G D C L γ η base roots κ₁) (hA₂ : splicedCountingAdmissible G D C L γ η base roots κ₂)
    (h : ∀ x : GardenDart G, G.molecule.atom x ≠ G.molecule.atom (G.molecule.mate x) → κ₁ x = κ₂ x) : κ₁ = κ₂ := by
  obtain ⟨⟨z₁, hz₁, hε₁, -⟩, -⟩ := hA₁
  obtain ⟨⟨z₂, hz₂, hε₂, -⟩, -⟩ := hA₂
  funext x
  by_cases hx : G.molecule.atom x ≠ G.molecule.atom (G.molecule.mate x)
  · exact h x hx
  push Not at hx
  rcases x with ⟨c, b⟩ | ℓ
  · exact absurd hx (inl_dart_nonloop c b)
  obtain ⟨hk₁, hvz₁⟩ := loop_values hg hD hε₁ ℓ hx
  obtain ⟨hk₂, hvz₂⟩ := loop_values hg hD hε₂ ℓ hx
  obtain ⟨i, j, hij, hi, hj, hs⟩ := loop_inr_struct ℓ hx
  set v := G.molecule.atom (Sum.inr ℓ) with hv
  -- the third child
  obtain ⟨k, hki, hkj⟩ := exists_third i j
  rw [← hz₁, ← hz₂]
  show z₁.1 ℓ.1.toNode = z₂.1 ℓ.1.toNode
  rw [← hk₁ k, ← hk₂ k]
  -- the node `v.child k` has equal values in both decorations
  have hnr : (v.child k).1.2 ≠ [] := by simp [GBranch.child]
  have hpar : GNode.parent (v.child k) hnr = v := parent_child' v k hnr
  rcases (TTree.mem_nodes_iff _ _).1 (v.child k).2 with hleaf | hbr
  · -- a leaf
    let l : GLeaf G.tree := ⟨(v.child k).1, hleaf⟩
    have hlm : G.mark l = none := hp l
    have hln : l.toNode = v.child k := rfl
    by_cases hpr : (G.pair l).1.2 = []
    · -- the partner is a root leaf: both decorations have the root value
      have e1 : z₁.1 l.toNode = z₁.1 (G.pair l).toNode := z₁.2.1.2 l
      have e2 : z₂.1 l.toNode = z₂.1 (G.pair l).toNode := z₂.2.1.2 l
      have hroot : (G.pair l).toNode = GNode.root G.tree (G.pair l).1.1 := by
        apply Subtype.ext
        change (G.pair l).1 = ((G.pair l).1.1, [])
        exact Prod.ext rfl hpr
      rw [hln] at e1 e2
      rw [e1, e2, hroot, z₁.2.2.1, z₂.2.2.1]
    · -- the dart `.inr l` exists and is not a loop
      let y : GardenDart G := Sum.inr ⟨l, hlm, hnr, hpr⟩
      have hynl : G.molecule.atom y ≠ G.molecule.atom (G.molecule.mate y) := by
        intro hyl
        obtain ⟨i', j', hij', hi', hj', hs'⟩ := loop_inr_struct ⟨l, hlm, hnr, hpr⟩ hyl
        have hav : G.molecule.atom y = v := hpar
        rw [hav] at hi' hj'
        have hik : i' = k := (child_injective G v) hi'.symm
        have hjk : j' ≠ k := fun e => hij' (hik.trans e.symm)
        have hpl : G.pair l ≠ l := fun e => ((G.pair_eq_iff l).1 e) hlm
        rcases fin3_other i j k j' hij hki hkj hjk with e | e
        · rw [e] at hj'
          have h1 : G.pair l = ℓ.1 := Mole.leaf_toNode_injective (hj'.trans hi.symm)
          have h2 : l = G.pair ℓ.1 := by rw [← h1, G.pair_pair]
          have h3 : l.toNode = v.child j := by rw [h2]; exact hj
          exact hkj ((child_injective G v) (hln.symm.trans h3).symm).symm
        · rw [e] at hj'
          have h1 : G.pair l = G.pair ℓ.1 := Mole.leaf_toNode_injective (hj'.trans hj.symm)
          have h2 : l = ℓ.1 := by
            have := congrArg G.pair h1
            rwa [G.pair_pair, G.pair_pair] at this
          have h3 : l.toNode = v.child i := by rw [h2]; exact hi
          exact hki ((child_injective G v) (hln.symm.trans h3).symm).symm
      have := h y hynl
      rw [← hz₁ y, ← hz₂ y] at this
      exact this
  · let c : {c : GBranch G.tree // c.1.2 ≠ []} := ⟨⟨(v.child k).1, hbr⟩, hnr⟩
    have := h (Sum.inl (c, true)) (inl_dart_nonloop c true)
    rw [← hz₁, ← hz₂] at this
    exact this

/-- `heq` for the renamed molecule `inlMol G.molecule`. -/
theorem inl_loop_heq (hg : CountingGeometry G C) (hD : D.hinges = C.subpro.hinges)
    (hA : splicedCountingAdmissible G D C L γ η base roots κ) :
    ∀ y : GardenDart G, (inlMol G.molecule).atom y = (inlMol G.molecule).atom ((inlMol G.molecule).mate y) →
      ∀ x : GardenDart G, (inlMol G.molecule).atom x = (inlMol G.molecule).atom y → κ x = κ y := by
  intro y hy x hx
  simp only [mapAtoms_atom, mapAtoms_mate, inlEmb_apply, Sum.inl.injEq] at hy hx
  exact garden_loop_heq hg hD hA y hy x hx

/-- `hdet` for the renamed molecule `inlMol G.molecule`. -/
theorem inl_loop_det (hp : G.IsPlain) (hg : CountingGeometry G C) (hD : D.hinges = C.subpro.hinges)
    {Adm : (GardenDart G → (Fin d → ℤ)) → Prop}
    (hA : ∀ κ, Adm κ → splicedCountingAdmissible G D C L γ η base roots κ) :
    ∀ κ₁ κ₂, Adm κ₁ → Adm κ₂ →
      (∀ x : GardenDart G, (inlMol G.molecule).atom x ≠ (inlMol G.molecule).atom ((inlMol G.molecule).mate x) → κ₁ x = κ₂ x) →
      κ₁ = κ₂ := by
  intro κ₁ κ₂ h1 h2 h
  refine garden_loop_det hp hg hD (hA κ₁ h1) (hA κ₂ h2) fun x hx => h x ?_
  simpa only [mapAtoms_atom, mapAtoms_mate, inlEmb_apply, ne_eq, Sum.inl.injEq] using hx

end loops

section subhyp
variable {V W : Type*} [DecidableEq V] [DecidableEq W] {D : Type*} [Fintype D] [DecidableEq D]

theorem subHypLoop_mapAtoms {M : Molecule V D} (ι : V ↪ W) {R : ℕ} (h : SubHypLoop R M) :
    SubHypLoop R (mapAtoms M ι) where
  bounds := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := (mem_mapAtoms_atoms M ι).1 ha
    rw [mapAtoms_outdeg, mapAtoms_indeg]; exact h.bounds b hb
  count := by
    rw [mapAtoms_bonds, mapAtoms_atoms, Finset.card_map]; exact h.count
  conn := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := (mem_mapAtoms_atoms M ι).1 ha
    obtain ⟨b', hb', rfl⟩ := (mem_mapAtoms_atoms M ι).1 hb
    exact sameComponent_mapAtoms M ι (h.conn a' ha' b' hb')
  one_le := h.one_le
  nonloop := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := (mem_mapAtoms_atoms M ι).1 ha
    obtain ⟨x, hx, hx'⟩ := h.nonloop b hb
    exact ⟨x, by simp [hx], by simpa [hx] using hx'⟩

end subhyp

end WaveTurbulence.FinalCountAsm
