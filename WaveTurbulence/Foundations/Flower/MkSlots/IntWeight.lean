/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntCapHyp
public import WaveTurbulence.Foundations.Flower.MkSlots.Bridge
public import WaveTurbulence.Foundations.Flower.MkSlots.Slice

/-! # B3s MK-SLOTS (integration): a capped class summand is the pinned weighted cap kernel

With no selected vertex (`kSel ≡ none`) and no stem filter (`σ ≡ none`), the frozen class summand of B4's hypothesis
(`kernelKgenSel` with the intrinsic plain pins `fixCap … plain`, removed phases `offCap` and the marked weight
`markedWt`) on a plain capped garden is main's pinned weighted leaf kernel `kernelLeavesSelNWF` (coset base `0`,
upper time `t`) with the anchored profiles `anchProfiles` and the node-product weight `∏_z capNodeW` (frontier ×
node-local dagger weight): `classSummand_eq_capKernel`. Pure garden-level algebra:

1. `selOK_none`, `stemFilterCap_none`, `selWeightCap_none`: the selection and stem factors are `1`;
2. `frontierW_eq_prod_fwNode`: the frontier weight is the node product of `fwNode` (no flower nodes on a plain
   garden);
3. `dag_prod`: the dagger sibling indicators times the removed-phase factor `offFactor` is the node product of
   `dagNodeW` (reindexing the capped flower parents and their children);
4. `typeProfilesAnchB_eq_anchProfiles`: on every decoration at coset base `0` the anchored profiles agree;
5. `capWeight_eq` and the assembly `classSummand_eq_capKernel` (via `kernelKgenSel_eq_fixW` and
   `kernelLeavesFixTerm_eq_fixMeasure` at the admissible plain pins). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1MKGate WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine

namespace WaveTurbulence.Flower.MkSlots

namespace IntWeight

variable {w d : ℕ}

/-! ### 1. No selected vertex, no stem filter -/

theorem selOK_none (LG : LayeredGarden w) (J : Finset (Fin w)) : selOK LG J (fun _ => none) = 1 := by
  simp [selOK]

theorem stemFilterCap_none (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ)
    (k : GNode LG.garden.tree → Mom d) : stemFilterCap LG J L (fun _ => none) k = 1 := by
  simp [stemFilterCap]

theorem selWeightCap_none (LG : LayeredGarden w) (J : Finset (Fin w)) (Rs : Fin w → ℝ)
    (k : GNode LG.garden.tree → Mom d) : selWeightCap LG J (selCap LG J (fun _ => none)) Rs k = 1 := by
  simp [selWeightCap, selCap]

/-! ### 2. The frontier weight as a node product -/

/-- A plain garden has no flower node. -/
theorem not_isFlowerNode_of_isPlain (LG : LayeredGarden w) (hplain : LG.garden.IsPlain)
    (a : GNode LG.garden.tree) : ¬ LG.IsFlowerNode a := by
  rintro ⟨ℓ, hℓ, -⟩
  have h0 := hplain ℓ
  unfold Garden.IsFlower at hℓ
  rw [h0] at hℓ
  exact absurd hℓ (by simp)

/-- On a plain garden the frontier weight is the node product of `fwNode` with the frontier cutoffs. -/
theorem frontierW_eq_prod_fwNode (LG : LayeredGarden w) (hplain : LG.garden.IsPlain) (p : ℕ)
    (Rf : Fin w → Option ℝ) (k : GNode LG.garden.tree → Mom d) :
    ((Typed.frontierW LG p Rf k : ℝ) : ℂ) = ∏ z, fwNode LG p (fun j => frontierG (Rf j)) z (k z) := by
  have e : Typed.frontierW LG p Rf k = Stage1W.frontierW LG p Rf k := rfl
  rw [e, frontierW_eq_nodeLabelProduct LG p Rf k (fun a ha _ => not_isFlowerNode_of_isPlain LG hplain a ha)]
  rfl

/-! ### 3. The dagger as a node product -/

theorem toNode_inj {tree : Fin w → TTree} {b b' : GBranch tree} (h : b.toNode = b'.toNode) : b = b' := by
  have h1 := congrArg (fun a : GNode tree => a.1) h
  exact Subtype.ext h1

theorem child_inj {tree : Fin w → TTree} {b b' : GBranch tree} {i i' : Fin 3} (h : b.child i = b'.child i') :
    b = b' ∧ i = i' := by
  have h1 : (b.1.1, b.1.2 ++ [i]) = (b'.1.1, b'.1.2 ++ [i']) := congrArg Subtype.val h
  simp only [Prod.mk.injEq] at h1
  obtain ⟨h1, h2⟩ := h1
  have h3 := List.append_inj' h2 rfl
  refine ⟨Subtype.ext (Prod.ext h1 h3.1), ?_⟩
  simpa using h3.2

/-- The parent factor `exp(+i θ_b ‖x‖²)` of the removed phase of a capped flower parent `b`. -/
def dagParF (L γ δ s : ℝ) (LG : LayeredGarden w) (b : GBranch LG.garden.tree) (x : Mom d) : ℂ :=
  Complex.exp (((capTheta L γ δ s LG.garden b * ‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I)

/-- The child phase factor `exp(-i θ_b ε_i ‖x‖²)` of the removed phase of `b` at its child `i`. -/
def dagChE (L γ δ s : ℝ) (LG : LayeredGarden w) (b : GBranch LG.garden.tree) (i : Fin 3) (x : Mom d) : ℂ :=
  Complex.exp (((-(capTheta L γ δ s LG.garden b * childSign i * ‖x‖ ^ 2) : ℝ) : ℂ) * Complex.I)

/-- The sibling indicator of child `i` of `b` at the node `z` (momentum `x`). -/
def dagChI (LG : LayeredGarden w) (J : Finset (Fin w)) (cc : Fin w → Fin 3 → Mom d)
    (b : GBranch LG.garden.tree) (i : Fin 3) (z : GNode LG.garden.tree) (x : Mom d) : ℂ :=
  if (∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.toNode = z) then 1 else
    if x = cc b.1.1 i then 1 else 0

/-- The node-local dagger weight with a dagger datum, as products over the capped flower parents. -/
theorem dagNodeW_some (L γ δ s : ℝ) (LG : LayeredGarden w) (J : Finset (Fin w)) (cc : Fin w → Fin 3 → Mom d)
    (z : GNode LG.garden.tree) (x : Mom d) :
    dagNodeW L γ δ s LG J (some cc) z x =
      (∏ b ∈ univ.filter (IsCapFlowerParent LG J), if b.toNode = z then dagParF L γ δ s LG b x else 1) *
      ∏ b ∈ univ.filter (IsCapFlowerParent LG J), ∏ i : Fin 3,
        if b.child i = z then dagChE L γ δ s LG b i x * dagChI LG J cc b i z x else 1 := by
  unfold dagNodeW
  simp only [Option.elim]
  congr 1
  · by_cases hb : ∃ b : GBranch LG.garden.tree, b.toNode = z ∧ IsCapFlowerParent LG J b
    · rw [dite_eq_left hb]
      obtain ⟨hz, hc⟩ := hb.choose_spec
      rw [Finset.prod_eq_single hb.choose]
      · rw [ite_eq_left hz]; rfl
      · intro b _ hne
        rw [ite_eq_right]
        intro hbz
        exact hne (toNode_inj (hbz.trans hz.symm))
      · intro hn
        exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩) hn
    · rw [dite_eq_right hb]
      symm
      refine Finset.prod_eq_one fun b hb' => ?_
      rw [ite_eq_right]
      intro hbz
      exact hb ⟨b, hbz, (Finset.mem_filter.1 hb').2⟩
  · by_cases hc : ∃ (b : GBranch LG.garden.tree) (i : Fin 3), b.child i = z ∧ IsCapFlowerParent LG J b
    · rw [dite_eq_left hc]
      obtain ⟨hz, hcp⟩ := hc.choose_spec.choose_spec
      rw [Finset.prod_eq_single hc.choose, Finset.prod_eq_single hc.choose_spec.choose, ite_eq_left hz]
      · rfl
      · intro i _ hne
        rw [ite_eq_right]
        intro hiz
        exact hne (child_inj (hiz.trans hz.symm)).2
      · intro hn
        exact absurd (Finset.mem_univ _) hn
      · intro b _ hne
        refine Finset.prod_eq_one fun i _ => ?_
        rw [ite_eq_right]
        intro hiz
        exact hne (child_inj (hiz.trans hz.symm)).1
      · intro hn
        exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcp⟩) hn
    · rw [dite_eq_right hc]
      symm
      refine Finset.prod_eq_one fun b hb' => Finset.prod_eq_one fun i _ => ?_
      rw [ite_eq_right]
      intro hiz
      exact hc ⟨b, i, hiz, (Finset.mem_filter.1 hb').2⟩

/-- The removed phase of one capped flower parent splits into its parent and child factors. -/
theorem offPhase_split (L γ δ s : ℝ) (LG : LayeredGarden w) (k : GNode LG.garden.tree → Mom d)
    (b : GBranch LG.garden.tree) :
    Complex.exp (-(((Real.pi * ((LG.garden.sign b.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaNode LG.garden k b *
        s : ℝ) : ℂ) * Complex.I)) =
      dagParF L γ δ s LG b (k b.toNode) * ∏ i : Fin 3, dagChE L γ δ s LG b i (k (b.child i)) := by
  unfold dagParF dagChE
  rw [Fin.prod_univ_three, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h0 : childSign 0 = 1 := by simp [childSign]
  have h1 : childSign 1 = -1 := by simp [childSign]
  have h2 : childSign 2 = 1 := by simp [childSign]
  rw [h0, h1, h2]
  unfold omegaNode resFactor capTheta
  push_cast
  ring

theorem prod_par_reindex (LG : LayeredGarden w) (S : Finset (GBranch LG.garden.tree))
    (F : GBranch LG.garden.tree → Mom d → ℂ) (k : GNode LG.garden.tree → Mom d) :
    ∏ z, ∏ b ∈ S, (if b.toNode = z then F b (k z) else 1) = ∏ b ∈ S, F b (k b.toNode) := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Finset.prod_ite_eq]
  simp

theorem prod_child_reindex (LG : LayeredGarden w) (S : Finset (GBranch LG.garden.tree))
    (G : GBranch LG.garden.tree → Fin 3 → GNode LG.garden.tree → Mom d → ℂ) (k : GNode LG.garden.tree → Mom d) :
    ∏ z, ∏ b ∈ S, ∏ i : Fin 3, (if b.child i = z then G b i z (k z) else 1) =
      ∏ b ∈ S, ∏ i : Fin 3, G b i (b.child i) (k (b.child i)) := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_ite_eq]
  simp

/-- **The dagger node product**: the sibling indicators times the removed-phase factor is the node product of the
node-local dagger weights `dagNodeW` (pointwise in the decoration). -/
theorem dag_prod (L γ δ s t : ℝ) (LG : LayeredGarden w) (J : Finset (Fin w))
    (dag : Option (Fin w → Fin 3 → Mom d)) (k : GNode LG.garden.tree → Mom d) :
    ((dag.elim 1 fun c => sibWeightCap LG J c k : ℝ) : ℂ) *
      offFactor L γ δ LG.garden (offCap LG J dag.isSome) (fixCap LG J (fun _ => FixPat.plain) t s) k =
    ∏ z, dagNodeW L γ δ s LG J dag z (k z) := by
  cases dag with
  | none => simp [offCap, offFactor, dagNodeW]
  | some cc =>
    rw [Finset.prod_congr rfl fun z _ => dagNodeW_some L γ δ s LG J cc z (k z), Finset.prod_mul_distrib,
      prod_par_reindex LG _ (dagParF L γ δ s LG) k,
      prod_child_reindex LG _ (fun b i z x => dagChE L γ δ s LG b i x * dagChI LG J cc b i z x) k]
    simp only [Option.elim, Option.isSome_some, offCap, ite_true, offFactor]
    have hsib : ((sibWeightCap LG J cc k : ℝ) : ℂ) =
        ∏ b ∈ univ.filter (IsCapFlowerParent LG J), ∏ i : Fin 3, dagChI LG J cc b i (b.child i) (k (b.child i)) := by
      unfold sibWeightCap dagChI
      rw [Complex.ofReal_prod, Finset.prod_filter]
      refine Finset.prod_congr rfl fun b _ => ?_
      split_ifs with hb
      · rw [Complex.ofReal_prod]
        refine Finset.prod_congr rfl fun i _ => ?_
        split_ifs <;> simp
      · simp
    rw [hsib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b hb => ?_
    have hfix : (fixCap LG J (fun _ => FixPat.plain) t s b).getD 0 = s := by
      simp [fixCap, (Finset.mem_filter.1 hb).2]
    rw [hfix, offPhase_split, Finset.prod_mul_distrib]
    ring

/-! ### 4. The anchored profiles on decorations at coset base `0` -/

/-- The leaf of a cap tree is its root: its label is the prescribed root label. -/
theorem genDec_cap (G : Garden w) (J : Finset (Fin w)) (hcap : ∀ j ∈ J, G.tree j = TTree.leaf)
    {roots : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration G d roots nfl)
    (ℓ : GLeaf G.tree) (hℓ : ℓ.1.1 ∈ J) : κ.1 ℓ.toNode = roots ℓ.1.1 := by
  have hpath : ℓ.1.2 = [] := by
    have h2 := ℓ.2
    rw [hcap _ hℓ] at h2
    simpa [TTree.leaves] using h2
  have hn : ℓ.toNode = GNode.root G.tree ℓ.1.1 := Subtype.ext (Prod.ext rfl hpath)
  rw [hn]
  exact κ.2.2.1 ℓ.1.1

/-- On every decoration at coset base `0`, the anchored profiles `typeProfilesAnchB` and `anchProfiles` agree at
every leaf (the anchored leaves carry exactly the cap momentum). -/
theorem typeProfilesAnchB_eq_anchProfiles (LG : LayeredGarden w) (J : Finset (Fin w))
    (hcap : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (L : ℝ)
    {roots : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d roots nfl)
    (ℓ : GLeaf LG.garden.tree) :
    S2ST.typeProfilesAnchB J LG h ℓ.1 (cosetDecoration LG.garden L 0 κ.1 ℓ.toNode) =
      anchProfiles J LG h L roots ℓ.1 (cosetDecoration LG.garden L 0 κ.1 ℓ.toNode) := by
  rw [S2ST.typeProfilesAnchB_leaf]
  unfold anchProfiles
  rw [pairTrees_leaf]
  by_cases h1 : ℓ.1.1 ∈ J
  · have hk : κ.1 ℓ.toNode = roots ℓ.1.1 := genDec_cap LG.garden J hcap κ ℓ h1
    simp [h1, cosetDecoration, hk]
  · by_cases h2 : (LG.garden.pair ℓ).1.1 ∈ J
    · have hk : κ.1 ℓ.toNode = roots (LG.garden.pair ℓ).1.1 :=
        (κ.2.1.2 ℓ).trans (genDec_cap LG.garden J hcap κ (LG.garden.pair ℓ) h2)
      simp [h1, h2, cosetDecoration, hk]
    · simp [h1, h2, typeProfiles_leaf]

/-! ### 5. The weight and the assembly -/

/-- **The capped weight is the node product of `capNodeW`**: with no selection and no stem filter, the rest of the
marked weight times the removed-phase factor is `∏_z capNodeW`. -/
theorem capWeight_eq (L γ δ : ℝ) (J : Finset (Fin w)) (p : ℕ) (t s : ℝ) (LG : LayeredGarden w)
    (hplain : LG.garden.IsPlain) (Rf : Fin w → Option ℝ) (Rs : Fin w → ℝ)
    (dag : Option (Fin w → Fin 3 → Mom d)) (k : GNode LG.garden.tree → Mom d) :
    ((selOK LG J (fun _ => none) * (Typed.frontierW LG p Rf k * stemFilterCap LG J L (fun _ => none) k *
        selWeightCap LG J (selCap LG J (fun _ => none)) Rs k * dag.elim 1 (fun c => sibWeightCap LG J c k)) : ℝ) :
        ℂ) * offFactor L γ δ LG.garden (offCap LG J dag.isSome) (fixCap LG J (fun _ => FixPat.plain) t s) k =
      ∏ z, capNodeW L γ δ p s LG J Rf dag z (k z) := by
  rw [selOK_none, stemFilterCap_none, selWeightCap_none, one_mul, mul_one, mul_one, Complex.ofReal_mul, mul_assoc,
    dag_prod, frontierW_eq_prod_fwNode LG hplain]
  unfold capNodeW
  rw [Finset.prod_mul_distrib]

end IntWeight

open IntWeight in
/-- **A capped class summand is the pinned weighted cap kernel.** With no selected vertex and no stem filter, the
frozen summand `kernelKgenSel` (intrinsic plain pins `fixCap`, removed phases `offCap`, marked weight `markedWt`) of a
plain capped garden is main's pinned weighted leaf kernel `kernelLeavesSelNWF` with the anchored profiles
`anchProfiles` and the node weight `∏_z capNodeW`. -/
theorem classSummand_eq_capKernel (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (p : ℕ) (t s : ℝ)
    (LG : LayeredGarden (2 * R)) (hG : CapGeo LG J p) (hplain : LG.garden.IsPlain)
    (hs : s ∈ Set.Ioo (p : ℝ) t) (ht : t ≤ p + 1)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (Rf : Fin (2 * R) → Option ℝ) (Rs : Fin (2 * R) → ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (sel : GenDecoration LG.garden P.d roots 0 → Prop) :
    kernelKgenSel P.L P.γ P.δ LG (fixCap LG J (fun _ => FixPat.plain) t s) (offCap LG J dag.isSome)
      (markedWt P J p (fun _ => none) h Rf (fun _ => none) Rs dag LG) (fun _ => t) 0 roots sel =
    kernelLeavesSelNWF P.L P.γ P.δ LG (anchProfiles J LG h P.L roots) (fun _ => t) 0 0 roots 0 sel
      (fun k => ∏ z, capNodeW P.L P.γ P.δ p s LG J Rf dag z (k z)) (fixCap LG J (fun _ => FixPat.plain) t s) := by
  rw [markedWt_eq, kernelKgenSel_eq_fixW P.L P.γ P.δ LG J _ _ (offCap_pinned LG J _ t s dag.isSome) h]
  unfold kernelLeavesFixSelW kernelLeavesSelNWF
  congr 1
  refine tsum_congr fun κ => ?_
  split_ifs with hsel
  · rw [kernelLeavesFixTerm_eq_fixMeasure P.L P.γ P.δ LG _ _ _ (admissiblePins_plain LG J p hG t s hs ht) 0 κ]
    congr 1
    · exact capWeight_eq P.L P.γ P.δ J p t s LG hplain Rf Rs dag _
    · congr 1
      refine Finset.prod_congr rfl fun ℓ _ => ?_
      rw [typeProfilesAnchB_eq_anchProfiles LG J hG.cap_leaf h P.L κ ℓ]
  · rfl

end WaveTurbulence.Flower.MkSlots
