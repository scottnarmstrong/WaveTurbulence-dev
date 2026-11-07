/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.Defs
public import WaveTurbulence.Foundations.Spine.RootFormSum
public import WaveTurbulence.Foundations.Spine.KernelCosetDecoration
/-! # FL-POLAR: the flower root form.

In a tree with exactly one flower (flower value `n'`, relative sign `ζ`), the root momentum minus `ζ` times
the flower momentum is the signed sum of the non-flower leaf momenta.  Statement deviation from the plan:
the plan's `flower_rootform` has no hypothesis on `k₀` or on the number of flowers; both are needed
(see `HANDOFF.md`). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Polar
open Finset

theorem nodeSign_root_eq' {w : ℕ} (sig : Fin w → ℤˣ) (tree : Fin w → TTree) (j : Fin w) :
    nodeSign sig (GNode.root tree j).1 = sig j := by
  simp [nodeSign, TTree.pathSign, GNode.root]

theorem leavesBelow_root_eq {w : ℕ} (G : Garden w) (j : Fin w) :
    (GNode.root G.tree j).leavesBelow = (univ : Finset (GLeaf G.tree)).filter fun ℓ => ℓ.1.1 = j := by
  ext ℓ
  constructor
  · intro h
    exact mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp h).2).1.symm⟩
  · intro h
    have h' : ℓ.1.1 = j := (mem_filter.mp h).2
    exact mem_filter.mpr ⟨mem_univ _, h'.symm, List.nil_prefix⟩

/-- **Flower root form.**  Plan statement plus two necessary side conditions: the tree `j` has exactly one
flower, and `(1 - ζ) k₀ = 0` (automatic for `k₀ = 0`). -/
theorem flower_rootform {w d : ℕ} (LG : LayeredGarden w) (L : ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ))
    (n' : Fin d → ℤ) (ζ : ℤˣ) (hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ →
      LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1)
    (κ : GenDecoration LG.garden d n n') (j : Fin w)
    (hone : (univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsFlower ℓ).card = 1)
    (hk₀ : ((1 : ℤ) - (ζ : ℤ)) • k₀ = 0) :
    latticePoint L (n j) - (ζ : ℤ) • latticePoint L n' =
      ∑ ℓ ∈ nonFlowerLeavesOf LG.garden j, (leafSignRel LG.garden ℓ : ℤ) •
        cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode := by
  set δ := cosetDecoration LG.garden L k₀ κ.1 with hδ
  have hdec : IsDecoration LG.garden δ := LGSpine.isDecoration_cosetDecoration LG.garden L k₀ κ.1 κ.2.1
  have hsum := sum_rule LG.garden.sig δ hdec.1 (GNode.root LG.garden.tree j)
  rw [nodeSign_root_eq', leavesBelow_root_eq, sum_filter] at hsum
  -- split the leaves of the tree into the flower and the non-flowers
  set s : Finset (GLeaf LG.garden.tree) := univ.filter fun ℓ => ℓ.1.1 = j with hs
  have hsum' : ((LG.garden.sig j : ℤˣ) : ℤ) • δ (GNode.root LG.garden.tree j) =
      ∑ ℓ ∈ s, ((nodeSign LG.garden.sig ℓ.1 : ℤˣ) : ℤ) • δ ℓ.toNode := by
    rw [hsum, hs, sum_filter]
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun ℓ => LG.garden.IsFlower ℓ)
    (fun ℓ => ((nodeSign LG.garden.sig ℓ.1 : ℤˣ) : ℤ) • δ ℓ.toNode)
  have hnf : s.filter (fun ℓ => ¬ LG.garden.IsFlower ℓ) = nonFlowerLeavesOf LG.garden j := by
    ext ℓ; simp [hs, nonFlowerLeavesOf]
  have hfs : s.filter (fun ℓ => LG.garden.IsFlower ℓ) =
      univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsFlower ℓ := by
    ext ℓ; simp [hs]
  rw [hfs] at hsplit
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hone
  rw [hf, Finset.sum_singleton, hnf] at hsplit
  have hfmem : f ∈ univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsFlower ℓ := by
    rw [hf]; exact Finset.mem_singleton_self f
  have hfj : f.1.1 = j := (mem_filter.mp hfmem).2.1
  have hff : LG.garden.IsFlower f := (mem_filter.mp hfmem).2.2
  have hsf : ((nodeSign LG.garden.sig f.1 : ℤˣ) : ℤ) = (ζ : ℤ) * ((LG.garden.sig j : ℤˣ) : ℤ) := by
    have := hfl f hff
    rw [hfj] at this
    change nodeSign LG.garden.sig f.1 = ζ * LG.garden.sig j at this
    rw [this]; simp
  have hδf : δ f.toNode = k₀ + latticePoint L n' := by
    change k₀ + latticePoint L (κ.1 f.toNode) = _
    rw [κ.2.2.2 f hff]
  have hroot : δ (GNode.root LG.garden.tree j) = k₀ + latticePoint L (n j) := by
    change k₀ + latticePoint L (κ.1 (GNode.root LG.garden.tree j)) = _
    rw [κ.2.2.1 j]
  rw [hroot] at hsum'
  rw [← hsplit, hsf, hδf] at hsum'
  -- relate the right side
  set σ : ℤ := ((LG.garden.sig j : ℤˣ) : ℤ) with hσ
  have hσσ : σ * σ = 1 := by
    have := Int.units_mul_self (LG.garden.sig j)
    simpa [hσ] using congrArg (fun u : ℤˣ => (u : ℤ)) this
  have hrel : ∀ ℓ ∈ nonFlowerLeavesOf LG.garden j, ((leafSignRel LG.garden ℓ : ℤˣ) : ℤ) • δ ℓ.toNode =
      σ • (((nodeSign LG.garden.sig ℓ.1 : ℤˣ) : ℤ) • δ ℓ.toNode) := by
    intro ℓ hℓ
    have hℓj : ℓ.1.1 = j := (mem_filter.mp hℓ).2.1
    rw [← mul_smul]
    congr 1
    simp only [leafSignRel, Units.val_mul, hℓj, hσ]
    change ((nodeSign LG.garden.sig ℓ.1 : ℤˣ) : ℤ) * _ = _
    ring
  rw [sum_congr rfl hrel, ← Finset.smul_sum]
  have hS : ∑ ℓ ∈ nonFlowerLeavesOf LG.garden j, ((nodeSign LG.garden.sig ℓ.1 : ℤˣ) : ℤ) • δ ℓ.toNode =
      σ • (k₀ + latticePoint L (n j)) - (↑ζ * σ) • (k₀ + latticePoint L n') := by
    rw [hsum']; abel
  rw [hS, smul_sub, smul_smul, smul_smul]
  have e1 : σ * σ = 1 := hσσ
  have e2 : σ * (↑ζ * σ) = (ζ : ℤ) := by
    calc σ * (↑ζ * σ) = (σ * σ) * (ζ : ℤ) := by ring
      _ = _ := by rw [e1, one_mul]
  rw [e1, e2]
  have hk := hk₀
  rw [sub_smul, one_smul] at hk
  have : k₀ = (ζ : ℤ) • k₀ := sub_eq_zero.mp hk
  calc latticePoint L (n j) - (ζ : ℤ) • latticePoint L n'
      = (k₀ + latticePoint L (n j)) - (ζ : ℤ) • (k₀ + latticePoint L n') - (k₀ - (ζ : ℤ) • k₀) := by
        rw [smul_add]; abel
    _ = _ := by rw [← this]; simp

end WaveTurbulence.Flower.Polar
