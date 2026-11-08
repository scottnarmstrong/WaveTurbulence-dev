/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.CapKerQ

/-! # B3s MK-SLOTS (cap slots): the dagger weight on a nontrivial cap slot

Inside the native cap couple the only capped flower parent is the terminal chain node `bF` (one capped flower per
tree), so the node-local dagger weight `dagNodeW` is `exp(iθ‖x‖²)` at `bF`, `exp(-iθ ε_i ‖x‖²)` times the sibling
indicator at its children, and `1` elsewhere (`dag_bF`, `dag_child`, `dag_other`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine

namespace WaveTurbulence.Flower.MkSlots

theorem child_ne_toNode {w : ℕ} {T : Fin w → TTree} (b : GBranch T) (i : Fin 3) : b.child i ≠ b.toNode := by
  intro h
  have := congrArg (fun z : GNode T => z.1.2.length) h
  simp [GBranch.child, GBranch.toNode] at this

namespace CapSide

variable {w : ℕ} {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {J : Finset (Fin w)}
  {q : SourcePair S} (K : CapSide D hS J q)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {p : ℕ} (hGeo : CapGeo (layeredReconstruction D hS layer hLayer) J p)

theorem dropLast_mem_branching : K.X.lonePath.dropLast ∈ (K.X.plug K.ζ .leaf).branching :=
  prefix_lone_branching K.X K.ζ (List.dropLast_prefix _) (dropLast_lonePath_ne K.ne)

/-- The capped flower parent (the terminal chain node) in the reconstruction. -/
def bF : GBranch (D.garden hS).tree := embBr K.emb K.X.lonePath.dropLast K.dropLast_mem_branching

/-- The slot of the capped flower under `bF`. -/
def iF : Fin 3 := K.X.lonePath.getLast (lonePath_ne_nil K.ne)

theorem lonePath_eq : K.X.lonePath = K.X.lonePath.dropLast ++ [K.iF] :=
  (List.dropLast_append_getLast (lonePath_ne_nil K.ne)).symm

theorem bF_val : K.bF.1 = addrExt K.u K.X.lonePath.dropLast := rfl

theorem flower_val : K.flower.1 = (K.bF.1.1, K.bF.1.2 ++ [K.iF]) := by
  show addrExt K.u K.X.lonePath = _
  rw [K.lonePath_eq]
  simp [bF_val, addrExt, List.append_assoc]

theorem isCFP_bF : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J K.bF :=
  ⟨K.flower, K.isCapFlower layer hLayer, by rw [K.flower_val], K.iF, by rw [K.flower_val]⟩

include hGeo in
/-- **The only capped flower parent in the chain's tree is `bF`.** -/
theorem eq_bF (b : GBranch (D.garden hS).tree) (hb : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J b)
    (hu : b.1.1 = K.u.1) : b = K.bF := by
  obtain ⟨ℓ, hℓ, h1, i, h2⟩ := hb
  have he : ℓ = K.flower := hGeo.one_flower ℓ K.flower hℓ (K.isCapFlower layer hLayer) (h1.trans hu)
  subst he
  rw [K.flower_val] at h1 h2
  simp only at h1 h2
  have h3 := List.append_inj' h2 rfl
  exact Subtype.ext (Prod.ext h1.symm h3.1.symm)

include hGeo in
theorem eq_flower (ℓ : GLeaf (D.garden hS).tree) (hℓ : IsCapFlower (layeredReconstruction D hS layer hLayer) J ℓ)
    (hu : ℓ.1.1 = K.u.1) : ℓ = K.flower :=
  hGeo.one_flower ℓ K.flower hℓ (K.isCapFlower layer hLayer) hu


/-- The phase scale of `bF`. -/
abbrev θF (L γ δ s : ℝ) : ℝ := capTheta L γ δ s (D.garden hS) K.bF

include hGeo in
theorem dag_bF {d : ℕ} (L γ δ s : ℝ) (cc : Fin w → Fin 3 → Mom d) (x : Mom d) :
    dagNodeW L γ δ s (layeredReconstruction D hS layer hLayer) J (some cc) K.bF.toNode x =
      Complex.exp (((K.θF L γ δ s * ‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I) := by
  unfold dagNodeW
  simp only [Option.elim]
  have h0 : ∃ b : GBranch (layeredReconstruction D hS layer hLayer).garden.tree, b.toNode = K.bF.toNode ∧
      IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J b := ⟨K.bF, rfl, K.isCFP_bF layer hLayer⟩
  rw [dif_pos h0]
  have hch : h0.choose = K.bF := K.eq_bF layer hLayer hGeo _ h0.choose_spec.2
    (by have := congrArg (fun z : GNode (D.garden hS).tree => z.1.1) h0.choose_spec.1; exact this)
  have hn : ¬ ∃ (b : GBranch (layeredReconstruction D hS layer hLayer).garden.tree) (i : Fin 3), b.child i = K.bF.toNode ∧
      IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J b := by
    rintro ⟨b, i, hbi, hb⟩
    have hb' : b = K.bF := K.eq_bF layer hLayer hGeo b hb
      (by have := congrArg (fun z : GNode (D.garden hS).tree => z.1.1) hbi; exact this)
    subst hb'
    exact child_ne_toNode _ i hbi
  rw [dif_neg hn, mul_one, hch]
  rfl

include hGeo in
theorem dag_child {d : ℕ} (L γ δ s : ℝ) (cc : Fin w → Fin 3 → Mom d) (i : Fin 3) (x : Mom d) :
    dagNodeW L γ δ s (layeredReconstruction D hS layer hLayer) J (some cc) (K.bF.child i) x =
      Complex.exp (((-(K.θF L γ δ s * childSign i * ‖x‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
        (if i = K.iF then 1 else if x = cc K.bF.1.1 i then 1 else 0) := by
  unfold dagNodeW
  simp only [Option.elim]
  have hn : ¬ ∃ b : GBranch (layeredReconstruction D hS layer hLayer).garden.tree, b.toNode = K.bF.child i ∧
      IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J b := by
    rintro ⟨b, hbz, hb⟩
    have hb' : b = K.bF := K.eq_bF layer hLayer hGeo b hb
      (by have := congrArg (fun z : GNode (D.garden hS).tree => z.1.1) hbz; exact this)
    subst hb'
    exact child_ne_toNode _ i hbz.symm
  have h0 : ∃ (b : GBranch (layeredReconstruction D hS layer hLayer).garden.tree) (i' : Fin 3), b.child i' = K.bF.child i ∧
      IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J b := ⟨K.bF, i, rfl, K.isCFP_bF layer hLayer⟩
  rw [dif_neg hn, one_mul, dif_pos h0]
  have key : ∀ (b : GBranch (layeredReconstruction D hS layer hLayer).garden.tree) (i' : Fin 3), b.child i' = K.bF.child i ∧
      IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J b → b = K.bF ∧ i' = i := by
    rintro b i' ⟨hbi, hb⟩
    have hb' : b = K.bF := K.eq_bF layer hLayer hGeo b hb
      (by have := congrArg (fun z : GNode (D.garden hS).tree => z.1.1) hbi; exact this)
    subst hb'
    refine ⟨rfl, ?_⟩
    have := congrArg (fun z : GNode (D.garden hS).tree => z.1.2) hbi
    simp only [GBranch.child] at this
    exact List.singleton_injective (List.append_cancel_left this)
  obtain ⟨e1, e2⟩ := key h0.choose h0.choose_spec.choose h0.choose_spec.choose_spec
  rw [e2, e1]
  congr 1
  have hfl : (∃ ℓ : GLeaf (layeredReconstruction D hS layer hLayer).garden.tree, IsCapFlower (layeredReconstruction D hS layer hLayer) J ℓ ∧
      ℓ.toNode = K.bF.child i) ↔ i = K.iF := by
    constructor
    · rintro ⟨ℓ, hℓ, he⟩
      have hu : ℓ.1.1 = K.u.1 := congrArg (fun z : GNode (D.garden hS).tree => z.1.1) he
      have hfl := K.eq_flower layer hLayer hGeo ℓ hℓ hu
      subst hfl
      have h5 : K.flower.1.2 = K.bF.1.2 ++ [i] := congrArg (fun z : GNode (D.garden hS).tree => z.1.2) he
      rw [K.flower_val] at h5
      exact (List.singleton_injective (List.append_cancel_left h5)).symm
    · rintro rfl
      exact ⟨K.flower, K.isCapFlower layer hLayer, Subtype.ext K.flower_val⟩
  by_cases hi : i = K.iF
  · rw [if_pos (hfl.2 hi), if_pos hi]
  · rw [if_neg (fun h => hi (hfl.1 h)), if_neg hi]

include hGeo in
theorem dag_other {d : ℕ} (L γ δ s : ℝ) (cc : Fin w → Fin 3 → Mom d) (z : GNode (D.garden hS).tree)
    (hz : z.1.1 = K.u.1) (h1 : z ≠ K.bF.toNode) (h2 : ∀ i, z ≠ K.bF.child i) (x : Mom d) :
    dagNodeW L γ δ s (layeredReconstruction D hS layer hLayer) J (some cc) z x = 1 := by
  unfold dagNodeW
  simp only [Option.elim]
  have hn1 : ¬ ∃ b : GBranch (layeredReconstruction D hS layer hLayer).garden.tree, b.toNode = z ∧
      IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J b := by
    rintro ⟨b, hbz, hb⟩
    have hb' : b = K.bF := K.eq_bF layer hLayer hGeo b hb
      (by rw [← hz]; exact congrArg (fun z : GNode (D.garden hS).tree => z.1.1) hbz)
    subst hb'
    exact h1 hbz.symm
  have hn2 : ¬ ∃ (b : GBranch (layeredReconstruction D hS layer hLayer).garden.tree) (i : Fin 3), b.child i = z ∧
      IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J b := by
    rintro ⟨b, i, hbz, hb⟩
    have hb' : b = K.bF := K.eq_bF layer hLayer hGeo b hb
      (by rw [← hz]; exact congrArg (fun z : GNode (D.garden hS).tree => z.1.1) hbz)
    subst hb'
    exact h2 i hbz.symm
  rw [dif_neg hn1, dif_neg hn2, mul_one]

end CapSide

end WaveTurbulence.Flower.MkSlots
