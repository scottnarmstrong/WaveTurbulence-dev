/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGardenLoops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGeom
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowGardenLoops`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (LOW-GARDEN): the epsilon-support facts at a loop atom of a garden.**

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
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Molecpl
  WaveTurbulence.AtomTransport WaveTurbulence.MoleProp

section nodes
variable {w d : ℕ} {G : Garden w}

end nodes

section loops
variable {R d : ℕ} {G : Garden (2 * R)}

variable {D : SplicedKernelData G d} {C : Src.CountingChoices Src.γL G d} {L γ η : ℝ} {base : Mom d}
  {roots : Fin (2 * R) → (Fin d → ℤ)} {κ : GardenDart G → (Fin d → ℤ)}

/-- The values of an admissible decoration around a loop: all children and the node itself carry the loop label. -/
theorem loop_values (hg : Src.CountingGeometry G C) (hD : D.hinges = C.subpro.hinges)
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
theorem garden_loop_heq (hg : Src.CountingGeometry G C) (hD : D.hinges = C.subpro.hinges)
    (hA : Src.splicedCountingAdmissible G D C L γ η base roots κ) :
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
theorem garden_loop_det (hp : G.IsPlain) (hg : Src.CountingGeometry G C) (hD : D.hinges = C.subpro.hinges)
    {κ₁ κ₂ : GardenDart G → (Fin d → ℤ)}
    (hA₁ : Src.splicedCountingAdmissible G D C L γ η base roots κ₁) (hA₂ : Src.splicedCountingAdmissible G D C L γ η base roots κ₂)
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
theorem inl_loop_heq (hg : Src.CountingGeometry G C) (hD : D.hinges = C.subpro.hinges)
    (hA : Src.splicedCountingAdmissible G D C L γ η base roots κ) :
    ∀ y : GardenDart G, (inlMol G.molecule).atom y = (inlMol G.molecule).atom ((inlMol G.molecule).mate y) →
      ∀ x : GardenDart G, (inlMol G.molecule).atom x = (inlMol G.molecule).atom y → κ x = κ y := by
  intro y hy x hx
  simp only [mapAtoms_atom, mapAtoms_mate, inlEmb_apply, Sum.inl.injEq] at hy hx
  exact garden_loop_heq hg hD hA y hy x hx

/-- `hdet` for the renamed molecule `inlMol G.molecule`. -/
theorem inl_loop_det (hp : G.IsPlain) (hg : Src.CountingGeometry G C) (hD : D.hinges = C.subpro.hinges)
    {Adm : (GardenDart G → (Fin d → ℤ)) → Prop}
    (hA : ∀ κ, Adm κ → Src.splicedCountingAdmissible G D C L γ η base roots κ) :
    ∀ κ₁ κ₂, Adm κ₁ → Adm κ₂ →
      (∀ x : GardenDart G, (inlMol G.molecule).atom x ≠ (inlMol G.molecule).atom ((inlMol G.molecule).mate x) → κ₁ x = κ₂ x) →
      κ₁ = κ₂ := by
  intro κ₁ κ₂ h1 h2 h
  refine garden_loop_det hp hg hD (hA κ₁ h1) (hA κ₂ h2) fun x hx => h x ?_
  simpa only [mapAtoms_atom, mapAtoms_mate, inlEmb_apply, ne_eq, Sum.inl.injEq] using hx

end loops

section subhyp
variable {V W : Type*} [DecidableEq V] [DecidableEq W] {D : Type*} [Fintype D] [DecidableEq D]

end subhyp

end WaveTurbulence.GammaLow.FinalCount.H
