/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitGeom2

/-! # Decorations of a split CL block (V5 Step 4b, P2.3)

Local decorations are handled as functions `x : GNode G.tree → ℤ^d` (extension by `0` of the support function,
`clExtendIndices`).  `ExtCL R L base β` is the set of extended local decorations of `R` with boundary `β`
(`clExtEquiv : CLLocalDecoration R L base β ≃ ExtCL R L base β`).  The decorations of `U = S ∪ T` are the pairs
`(xS, xT)` of an upper-block decoration (`ExtS`, without the two excluded children of `b`) and a decoration of `T` whose boundary
at `b` and at its excluded child is given by `xS`: `splitDecEquiv`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree
variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

/-- Local conservation at the atoms of `V`. -/
@[expose] def consOn (V : Finset (GBranch G.tree)) (x : GNode G.tree → (Fin d → ℤ)) : Prop :=
  ∀ v ∈ V, x v.toNode = x (v.child 0) - x (v.child 1) + x (v.child 2)

/-- Matching of the internal leaves of `V`. -/
@[expose] def leafOn (G : Garden w) (V : Finset (GBranch G.tree)) (x : GNode G.tree → (Fin d → ℤ)) : Prop :=
  ∀ ℓ, Mole.IsInternalLeaf G V ℓ → x ℓ.toNode = x (G.pair ℓ).toNode

/-- The boundary-free constraints of an extended local decoration. -/
@[expose] def FreeDec {U : Finset (GBranch G.tree)} (R : CLRegionData G U a b) (x : GNode G.tree → (Fin d → ℤ)) : Prop :=
  (∀ y, y ∉ clLocalSupport R → x y = 0) ∧ consOn U x ∧ leafOn G U x

/-- The four boundary values of an extended decoration. -/
@[expose] def BdAt {U : Finset (GBranch G.tree)} (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (β : Fin 4 → Mom d) (x : GNode G.tree → (Fin d → ℤ)) : Prop :=
  ∀ j, base + latticePoint L (x (clBoundaryNodes R j)) = β j

/-- Extended local decorations with prescribed boundary. -/
@[expose] def ExtCL {U : Finset (GBranch G.tree)} (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (β : Fin 4 → Mom d) : Type :=
  {x : GNode G.tree → (Fin d → ℤ) // FreeDec R x ∧ BdAt R L base β x}

theorem clExtendIndices_of_notMem {U : Finset (GBranch G.tree)} (R : CLRegionData G U a b)
    (z : ↥(clLocalSupport R) → (Fin d → ℤ)) {y : GNode G.tree} (hy : y ∉ clLocalSupport R) :
    clExtendIndices R z y = 0 := by
  classical
  simp [clExtendIndices, hy]

theorem clExtendIndices_ofExt {U : Finset (GBranch G.tree)} (R : CLRegionData G U a b)
    (e : GNode G.tree → (Fin d → ℤ)) (he : ∀ y, y ∉ clLocalSupport R → e y = 0) :
    clExtendIndices R (fun y => e y.1) = e := by
  funext y
  by_cases hy : y ∈ clLocalSupport R
  · exact clExtendIndices_apply R _ y hy
  · rw [clExtendIndices_of_notMem R _ hy, he y hy]

/-- Local decorations are extended decorations (extension by zero). -/
@[expose] noncomputable def clExtEquiv {U : Finset (GBranch G.tree)} (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (β : Fin 4 → Mom d) : CLLocalDecoration R L base β ≃ ExtCL R L base β where
  toFun z := ⟨clExtendIndices R z.1, ⟨fun y hy => clExtendIndices_of_notMem R _ hy, z.2.1, z.2.2.1⟩, z.2.2.2⟩
  invFun e := ⟨fun y => e.1 y.1, by
      rw [clExtendIndices_ofExt R e.1 e.2.1.1]
      exact ⟨e.2.1.2.1, e.2.1.2.2, e.2.2⟩⟩
  left_inv z := by
    apply Subtype.ext
    funext y
    exact clExtendIndices_apply R z.1 y.1 y.2
  right_inv e := by
    apply Subtype.ext
    exact clExtendIndices_ofExt R e.1 e.2.1.1

theorem clExtEquiv_val {U : Finset (GBranch G.tree)} (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (β : Fin 4 → Mom d) (z : CLLocalDecoration R L base β) :
    (clExtEquiv R L base β z).1 = clExtendIndices R z.1 := rfl

/-! ## Splitting a decoration -/

section Split3
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c)

/-- Constraints of an upper-block decoration (the conservation at the lower joint `b` is a constraint of `T`). -/
@[expose] def FreeS (RS : CLRegionData G S a b) (x : GNode G.tree → (Fin d → ℤ)) : Prop :=
  (∀ y, y ∉ splitA RS → x y = 0) ∧ consOn (S.erase b) x ∧ leafOn G S x

/-- The two upper boundary values of an upper-block decoration. -/
@[expose] def BdS (RS : CLRegionData G S a b) (L : ℝ) (base : Mom d) (β0 β1 : Mom d)
    (x : GNode G.tree → (Fin d → ℤ)) : Prop :=
  base + latticePoint L (x a.toNode) = β0 ∧ base + latticePoint L (x (a.child RS.excluded)) = β1

/-- Extended decorations of the upper block. -/
@[expose] def ExtS (RS : CLRegionData G S a b) (L : ℝ) (base : Mom d) (β0 β1 : Mom d) : Type :=
  {x : GNode G.tree → (Fin d → ℤ) // FreeS RS x ∧ BdS RS L base β0 β1 x}

/-- The boundary of `T` determined by an upper-block decoration `xS` and the lower boundary `(β2, β3)`. -/
@[expose] noncomputable def bdT (RT : CLRegionData G T b c) (L : ℝ) (base : Mom d)
    (xS : GNode G.tree → (Fin d → ℤ)) (β2 β3 : Mom d) : Fin 4 → Mom d :=
  ![base + latticePoint L (xS (clBoundaryNodes RT 0)), base + latticePoint L (xS (clBoundaryNodes RT 1)), β2, β3]

/-- Restriction of a function to the upper-block nodes. -/
@[expose] noncomputable def rA (RS : CLRegionData G S a b) (x : GNode G.tree → (Fin d → ℤ)) : GNode G.tree → (Fin d → ℤ) :=
  fun y => if y ∈ splitA RS then x y else 0

/-- Restriction of a function to the support of `T`. -/
@[expose] noncomputable def rB (RT : CLRegionData G T b c) (x : GNode G.tree → (Fin d → ℤ)) : GNode G.tree → (Fin d → ℤ) :=
  fun y => if y ∈ clLocalSupport RT then x y else 0

/-- Gluing of an upper-block decoration with a decoration of `T`. -/
@[expose] noncomputable def glue (RS : CLRegionData G S a b) (xS xT : GNode G.tree → (Fin d → ℤ)) :
    GNode G.tree → (Fin d → ℤ) :=
  fun y => if y ∈ splitA RS then xS y else xT y

include hS hT hi hU

theorem rA_cons (RS : CLRegionData G S a b) {x : GNode G.tree → (Fin d → ℤ)} (hx : consOn (S ∪ T) x) :
    consOn (S.erase b) (rA RS x) := by
  intro v hv
  obtain ⟨hvb, hvS⟩ := Finset.mem_erase.mp hv
  simp only [rA, splitA_node hS hT hi hU RS hvS, splitA_child hS hT hi hU RS hvS hvb, ite_true]
  exact hx v (Finset.mem_union_left _ hvS)

theorem rA_leaf (RS : CLRegionData G S a b) {x : GNode G.tree → (Fin d → ℤ)} (hx : leafOn G (S ∪ T) x) :
    leafOn G S (rA RS x) := by
  intro ℓ hℓ
  have h1 : ℓ.toNode ∈ splitA RS := Finset.mem_union_left _ ((leaf_mem_clRealizationNodes ℓ).mpr hℓ)
  have h2 : (G.pair ℓ).toNode ∈ splitA RS :=
    Finset.mem_union_left _ ((leaf_mem_clRealizationNodes _).mpr ((Mole.internal_leaf_pair_iff G S ℓ).mpr hℓ))
  simp only [rA, h1, h2, ite_true]
  exact hx ℓ ((split_internalLeaf hS hT hi hU ℓ).mpr (Or.inl hℓ))

theorem rB_cons (RT : CLRegionData G T b c) {x : GNode G.tree → (Fin d → ℤ)} (hx : consOn (S ∪ T) x) :
    consOn T (rB RT x) := by
  intro v hv
  have h0 : v.toNode ∈ clLocalSupport RT := cl_realization_mem_support RT ((branch_mem_clRealizationNodes v).mpr hv)
  simp only [rB, h0, cl_child_mem_support hT RT hv, ite_true]
  exact hx v (Finset.mem_union_right _ hv)

theorem rB_leaf (RT : CLRegionData G T b c) {x : GNode G.tree → (Fin d → ℤ)} (hx : leafOn G (S ∪ T) x) :
    leafOn G T (rB RT x) := by
  intro ℓ hℓ
  have h1 : ℓ.toNode ∈ clLocalSupport RT := cl_realization_mem_support RT ((leaf_mem_clRealizationNodes ℓ).mpr hℓ)
  have h2 : (G.pair ℓ).toNode ∈ clLocalSupport RT := cl_realization_mem_support RT
    ((leaf_mem_clRealizationNodes _).mpr ((Mole.internal_leaf_pair_iff G T ℓ).mpr hℓ))
  simp only [rB, h1, h2, ite_true]
  exact hx ℓ ((split_internalLeaf hS hT hi hU ℓ).mpr (Or.inr hℓ))

theorem split_agree (RS : CLRegionData G S a b) (RT : CLRegionData G T b c) {L : ℝ} (hL : L ≠ 0) {base : Mom d}
    {xS xT : GNode G.tree → (Fin d → ℤ)} {β2 β3 : Mom d} (hc : BdAt RT L base (bdT RT L base xS β2 β3) xT)
    {y : GNode G.tree} (hA : y ∈ splitA RS) (hB : y ∈ clLocalSupport RT) : xS y = xT y := by
  have hkb := split_excluded_b hS hT hi hU RS RT
  have inj := latticePoint_injective_of_ne_zero (d := d) hL
  rcases split_overlap hS hT hi hU RS RT hA hB with rfl | rfl
  · have := hc 0
    simp only [bdT, Matrix.cons_val_zero] at this
    exact (inj (add_left_cancel this)).symm
  · have := hc 1
    simp only [bdT, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at this
    have h1 : clBoundaryNodes RT 1 = b.child RS.kept := by
      show b.child RT.excluded = _
      rw [hkb]
    rw [h1] at this
    exact (inj (add_left_cancel this)).symm

theorem bdU_1 (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b) :
    clBoundaryNodes RU 1 = a.child RS.excluded := by
  show a.child RU.excluded = _
  rw [split_excluded_a hS hT hi hU RU RS]

theorem bdU_2 (RU : CLRegionData G (S ∪ T) a c) (RT : CLRegionData G T b c) :
    clBoundaryNodes RU 2 = clBoundaryNodes RT 2 := by
  show c.child RU.positive = c.child RT.positive
  rw [(split_positive_c hS hT hi hU RU RT).1]

theorem bdU_3 (RU : CLRegionData G (S ∪ T) a c) (RT : CLRegionData G T b c) :
    clBoundaryNodes RU 3 = clBoundaryNodes RT 3 := by
  show c.child RU.negative = c.child RT.negative
  rw [(split_positive_c hS hT hi hU RU RT).2]

theorem bdT_1_mem (RS : CLRegionData G S a b) (RT : CLRegionData G T b c) :
    clBoundaryNodes RT 1 ∈ splitA RS := by
  have hkb := split_excluded_b hS hT hi hU RS RT
  show b.child RT.excluded ∈ splitA RS
  rw [hkb]
  exact Finset.mem_union_left _
    (cl_child_mem_realization_of_internal hS RS hS.2.2.1 RS.kept ((RS.lower RS.kept).mpr rfl))

theorem rA_free_bd (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b) {L : ℝ} {base : Mom d}
    {βU : Fin 4 → Mom d} {x : GNode G.tree → (Fin d → ℤ)} (hx : FreeDec RU x) (hbd : BdAt RU L base βU x) :
    FreeS RS (rA RS x) ∧ BdS RS L base (βU 0) (βU 1) (rA RS x) := by
  refine ⟨⟨fun y hy => by simp [rA, hy], rA_cons hS hT hi hU RS hx.2.1, rA_leaf hS hT hi hU RS hx.2.2⟩, ?_, ?_⟩
  · have h : base + latticePoint L (x a.toNode) = βU 0 := hbd 0
    simpa only [rA, splitA_node hS hT hi hU RS hS.2.1, ite_true] using h
  · have h := hbd 1
    rw [bdU_1 hS hT hi hU RU RS] at h
    have hm : a.child RS.excluded ∈ splitA RS := Finset.mem_union_right _ (by simp)
    simpa only [rA, hm, ite_true] using h

theorem rB_free (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b) (RT : CLRegionData G T b c)
    {x : GNode G.tree → (Fin d → ℤ)} (hx : FreeDec RU x) : FreeDec RT (rB RT x) :=
  ⟨fun y hy => by simp [rB, hy], rB_cons hS hT hi hU RT hx.2.1, rB_leaf hS hT hi hU RT hx.2.2⟩

theorem compat_of (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b) (RT : CLRegionData G T b c)
    {L : ℝ} {base : Mom d} {βU : Fin 4 → Mom d} {x : GNode G.tree → (Fin d → ℤ)} (hx : FreeDec RU x)
    (hbd : BdAt RU L base βU x) :
    BdAt RT L base (bdT RT L base (rA RS x) (βU 2) (βU 3)) (rB RT x) := by
  have hb : ∀ j, clBoundaryNodes RT j ∈ clLocalSupport RT := clBoundaryNodes_mem_support RT
  have h0 : clBoundaryNodes RT 0 ∈ splitA RS := by
    have : clBoundaryNodes RT 0 = b.toNode := rfl
    rw [this]
    exact splitA_node hS hT hi hU RS hS.2.2.1
  have e0 : base + latticePoint L (rB RT x (clBoundaryNodes RT 0)) =
      base + latticePoint L (rA RS x (clBoundaryNodes RT 0)) := by
    simp only [rB, rA, hb 0, h0, ite_true]
  have e1 : base + latticePoint L (rB RT x (clBoundaryNodes RT 1)) =
      base + latticePoint L (rA RS x (clBoundaryNodes RT 1)) := by
    simp only [rB, rA, hb 1, bdT_1_mem hS hT hi hU RS RT, ite_true]
  have e2 : base + latticePoint L (rB RT x (clBoundaryNodes RT 2)) = βU 2 := by
    have h := hbd 2
    rw [bdU_2 hS hT hi hU RU RT] at h
    simp only [rB, hb 2, ite_true]
    exact h
  have e3 : base + latticePoint L (rB RT x (clBoundaryNodes RT 3)) = βU 3 := by
    have h := hbd 3
    rw [bdU_3 hS hT hi hU RU RT] at h
    simp only [rB, hb 3, ite_true]
    exact h
  intro j
  fin_cases j
  · exact e0
  · exact e1
  · exact e2
  · exact e3

theorem glue_B (RS : CLRegionData G S a b) (RT : CLRegionData G T b c) {L : ℝ} (hL : L ≠ 0) {base : Mom d}
    {xS xT : GNode G.tree → (Fin d → ℤ)} {β2 β3 : Mom d} (hc : BdAt RT L base (bdT RT L base xS β2 β3) xT)
    {y : GNode G.tree} (hB : y ∈ clLocalSupport RT) : glue RS xS xT y = xT y := by
  by_cases hA : y ∈ splitA RS
  · simp only [glue, hA, ite_true]
    exact split_agree hS hT hi hU RS RT hL hc hA hB
  · simp only [glue, hA, ite_false]

theorem glue_free_bd (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b) (RT : CLRegionData G T b c)
    {L : ℝ} (hL : L ≠ 0) {base : Mom d} {βU : Fin 4 → Mom d} {xS xT : GNode G.tree → (Fin d → ℤ)}
    (hxS : FreeS RS xS) (hbS : BdS RS L base (βU 0) (βU 1) xS) (hxT : FreeDec RT xT)
    (hc : BdAt RT L base (bdT RT L base xS (βU 2) (βU 3)) xT) :
    FreeDec RU (glue RS xS xT) ∧ BdAt RU L base βU (glue RS xS xT) := by
  have hGB := fun {y} (hB : y ∈ clLocalSupport RT) => glue_B hS hT hi hU RS RT hL hc hB
  have hGA : ∀ {y}, y ∈ splitA RS → glue RS xS xT y = xS y := fun {y} hy => by simp [glue, hy]
  have hsupp := split_support hS hT hi hU RU RS RT
  refine ⟨⟨fun y hy => ?_, ?_, ?_⟩, ?_⟩
  · rw [hsupp] at hy
    have hyA : y ∉ splitA RS := fun h => hy (Finset.mem_union_left _ h)
    have hyB : y ∉ clLocalSupport RT := fun h => hy (Finset.mem_union_right _ h)
    simp only [glue, hyA, ite_false]
    exact hxT.1 y hyB
  · intro v hv
    by_cases hvT : v ∈ T
    · have h0 : v.toNode ∈ clLocalSupport RT :=
        cl_realization_mem_support RT ((branch_mem_clRealizationNodes v).mpr hvT)
      rw [hGB h0, hGB (cl_child_mem_support hT RT hvT 0), hGB (cl_child_mem_support hT RT hvT 1),
        hGB (cl_child_mem_support hT RT hvT 2)]
      exact hxT.2.1 v hvT
    · have hvS : v ∈ S := (Finset.mem_union.mp hv).resolve_right hvT
      have hvb : v ≠ b := fun h => hvT (h ▸ hT.2.1)
      rw [hGA (splitA_node hS hT hi hU RS hvS), hGA (splitA_child hS hT hi hU RS hvS hvb 0),
        hGA (splitA_child hS hT hi hU RS hvS hvb 1), hGA (splitA_child hS hT hi hU RS hvS hvb 2)]
      exact hxS.2.1 v (Finset.mem_erase.mpr ⟨hvb, hvS⟩)
  · intro ℓ hℓ
    rcases (split_internalLeaf hS hT hi hU ℓ).mp hℓ with h | h
    · rw [hGA (Finset.mem_union_left _ ((leaf_mem_clRealizationNodes ℓ).mpr h)),
        hGA (Finset.mem_union_left _ ((leaf_mem_clRealizationNodes _).mpr ((Mole.internal_leaf_pair_iff G S ℓ).mpr h)))]
      exact hxS.2.2 ℓ h
    · rw [hGB (cl_realization_mem_support RT ((leaf_mem_clRealizationNodes ℓ).mpr h)),
        hGB (cl_realization_mem_support RT ((leaf_mem_clRealizationNodes _).mpr
          ((Mole.internal_leaf_pair_iff G T ℓ).mpr h)))]
      exact hxT.2.2 ℓ h
  · have e0 : base + latticePoint L (glue RS xS xT (clBoundaryNodes RU 0)) = βU 0 := by
      have : clBoundaryNodes RU 0 = a.toNode := rfl
      rw [this, hGA (splitA_node hS hT hi hU RS hS.2.1)]
      exact hbS.1
    have e1 : base + latticePoint L (glue RS xS xT (clBoundaryNodes RU 1)) = βU 1 := by
      rw [bdU_1 hS hT hi hU RU RS, hGA (Finset.mem_union_right _ (by simp))]
      exact hbS.2
    have e2 : base + latticePoint L (glue RS xS xT (clBoundaryNodes RU 2)) = βU 2 := by
      rw [bdU_2 hS hT hi hU RU RT, hGB (clBoundaryNodes_mem_support RT 2)]
      exact hc 2
    have e3 : base + latticePoint L (glue RS xS xT (clBoundaryNodes RU 3)) = βU 3 := by
      rw [bdU_3 hS hT hi hU RU RT, hGB (clBoundaryNodes_mem_support RT 3)]
      exact hc 3
    intro j
    fin_cases j
    · exact e0
    · exact e1
    · exact e2
    · exact e3

/-- The decorations of `U = S ∪ T` are the compatible pairs of an upper-block decoration and a decoration of `T`. -/
@[expose] noncomputable def splitPairEquiv (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
    (RT : CLRegionData G T b c) {L : ℝ} (hL : L ≠ 0) (base : Mom d) (βU : Fin 4 → Mom d) :
    ExtCL RU L base βU ≃
      {p : ExtS RS L base (βU 0) (βU 1) × {x : GNode G.tree → (Fin d → ℤ) // FreeDec RT x} //
        BdAt RT L base (bdT RT L base p.1.1 (βU 2) (βU 3)) p.2.1} where
  toFun x := ⟨(⟨rA RS x.1, rA_free_bd hS hT hi hU RU RS x.2.1 x.2.2⟩,
      ⟨rB RT x.1, rB_free hS hT hi hU RU RS RT x.2.1⟩), compat_of hS hT hi hU RU RS RT x.2.1 x.2.2⟩
  invFun p := ⟨glue RS p.1.1.1 p.1.2.1,
      glue_free_bd hS hT hi hU RU RS RT hL p.1.1.2.1 p.1.1.2.2 p.1.2.2 p.2⟩
  left_inv x := by
    apply Subtype.ext
    funext y
    show glue RS (rA RS x.1) (rB RT x.1) y = x.1 y
    by_cases hA : y ∈ splitA RS
    · simp [glue, rA, hA]
    · by_cases hB : y ∈ clLocalSupport RT
      · simp [glue, rB, hA, hB]
      · have hy : y ∉ clLocalSupport RU := by
          rw [split_support hS hT hi hU RU RS RT]
          intro h
          rcases Finset.mem_union.mp h with h | h
          · exact hA h
          · exact hB h
        simp [glue, hA, rB, hB, x.2.1.1 y hy]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      funext y
      show rA RS (glue RS p.1.1.1 p.1.2.1) y = p.1.1.1 y
      by_cases hA : y ∈ splitA RS
      · simp [rA, glue, hA]
      · simp [rA, hA, p.1.1.2.1.1 y hA]
    · apply Subtype.ext
      funext y
      show rB RT (glue RS p.1.1.1 p.1.2.1) y = p.1.2.1 y
      by_cases hB : y ∈ clLocalSupport RT
      · simp only [rB, hB, ite_true]
        exact glue_B hS hT hi hU RS RT hL p.2 hB
      · simp [rB, hB, p.1.2.2.1 y hB]

/-- **Splitting of local decorations.**  `ExtCL RU ≃ Σ xS, ExtCL RT (bdT xS)`. -/
@[expose] noncomputable def splitDecEquiv (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
    (RT : CLRegionData G T b c) {L : ℝ} (hL : L ≠ 0) (base : Mom d) (βU : Fin 4 → Mom d) :
    ExtCL RU L base βU ≃
      Σ xS : ExtS RS L base (βU 0) (βU 1), ExtCL RT L base (bdT RT L base xS.1 (βU 2) (βU 3)) :=
  (splitPairEquiv hS hT hi hU RU RS RT hL base βU).trans
    ((Equiv.subtypeProdEquivSigmaSubtype
      (fun (xS : ExtS RS L base (βU 0) (βU 1)) (xT : {x : GNode G.tree → (Fin d → ℤ) // FreeDec RT x}) =>
        BdAt RT L base (bdT RT L base xS.1 (βU 2) (βU 3)) xT.1)).trans
      (Equiv.sigmaCongrRight fun xS => Equiv.subtypeSubtypeEquivSubtypeInter (fun x => FreeDec RT x)
        (fun x => BdAt RT L base (bdT RT L base xS.1 (βU 2) (βU 3)) x)))

end Split3

end WaveTurbulence.VineEstS4
