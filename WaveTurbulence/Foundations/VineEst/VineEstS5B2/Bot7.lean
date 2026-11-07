/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot6

/-! # V5 Step 4d-B2: the bottom vine, part 7 (the constraints of an extended decoration of the whole chain under the twist)

`ExtCL R L base β` (the extended local decorations of the whole region, with the boundary values at the two excluded children of `b`)
is mapped to the same set of the twisted region by the label switch: the support, the conservation (at `b` too), the pairing of the
internal leaves and the four boundary values correspond (`ext_iff`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {G : Garden w}

theorem mem_support_iff {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G S a b) (y : GNode G.tree) :
    y ∈ clLocalSupport R ↔ y ∈ splitA R ∨ y = b.child R.positive ∨ y = b.child R.negative := by
  unfold clLocalSupport splitA clBoundaryNodes
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
    Fin.exists_fin_succ, Fin.exists_fin_zero_pi]
  simp
  tauto

/-- The conservation at the single atom `b`. -/
@[expose] def consAt {d : ℕ} (b : GBranch G.tree) (x : GNode G.tree → (Fin d → ℤ)) : Prop :=
  x b.toNode = x (b.child 0) - x (b.child 1) + x (b.child 2)

theorem consOn_iff_erase {d : ℕ} {V : Finset (GBranch G.tree)} {b : GBranch G.tree} (hb : b ∈ V)
    (x : GNode G.tree → (Fin d → ℤ)) : consOn V x ↔ consOn (V.erase b) x ∧ consAt b x := by
  constructor
  · intro H
    exact ⟨fun v hv => H v (Finset.mem_of_mem_erase hv), H b hb⟩
  · rintro ⟨H1, H2⟩ v hv
    by_cases hvb : v = b
    · subst hvb; exact H2
    · exact H1 v (Finset.mem_erase.mpr ⟨hvb, hv⟩)

variable (P : CorePlacement G) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} {RS : CLRegionData G S a b}
  {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (h : STw P RS RS')
include h

theorem stw_support_iff (y : GNode G.tree) :
    y ∈ clLocalSupport RS ↔ naiveNodeEquiv G P y ∈ clLocalSupport RS' := by
  have e1 := stw_child_eb P h RS.positive
  have e2 := stw_child_eb P h RS.negative
  have hl := h.lower
  subst hl
  rw [mem_support_iff, mem_support_iff, h.splitA_iff y, stw_positive_eq P h, stw_negative_eq P h, e1, e2]
  simp only [Equiv.apply_eq_iff_eq]

theorem stw_free_zero_iff {d : ℕ} (x : GNode G.tree → (Fin d → ℤ)) :
    (∀ y, y ∉ clLocalSupport RS → x y = 0) ↔
      (∀ y', y' ∉ clLocalSupport RS' → twistNodeLabels G P x y' = 0) := by
  have hsub : ∀ y, y ∉ clLocalSupport RS → y ∉ splitA RS := fun y hy hh => hy ((mem_support_iff RS y).mpr (Or.inl hh))
  constructor
  · intro H y' hy'
    obtain ⟨y, rfl⟩ := (naiveNodeEquiv G P).surjective y'
    have hy : y ∉ clLocalSupport RS := fun hh => hy' ((stw_support_iff P h y).mp hh)
    rw [twistNodeLabels_naive, h.switched_eq_of_notMem x (hsub y hy)]
    exact H y hy
  · intro H y hy
    have hy' : naiveNodeEquiv G P y ∉ clLocalSupport RS' := fun hh => hy ((stw_support_iff P h y).mpr hh)
    have := H _ hy'
    rwa [twistNodeLabels_naive, h.switched_eq_of_notMem x (hsub y hy)] at this

theorem stw_consAt_iff {d : ℕ} (x : GNode G.tree → (Fin d → ℤ)) :
    consAt b x ↔ consAt (eB P b) (twistNodeLabels G P x) := by
  have hl := h.lower
  subst hl
  unfold consAt
  rcases keep_cases P with hk | hk
  · obtain ⟨e0, e1, e2, e3⟩ := (lower_labels P x).1 hk
    rw [e0, e1, e2, e3]
    constructor <;> intro H <;> rw [H] <;> abel
  · obtain ⟨e0, e1, e2, e3⟩ := (lower_labels P x).2 hk
    rw [e0, e1, e2, e3]
    constructor <;> intro H <;> rw [H] <;> abel

theorem stw_label_bd {d : ℕ} (x : GNode G.tree → (Fin d → ℤ)) (hp : PairedAt P x) (j : Fin 4) :
    twistNodeLabels G P x (clBoundaryNodes RS' j) = x (clBoundaryNodes RS j) := by
  have hal : a ≠ P.lower := h.a_ne_lower
  fin_cases j
  · exact twistNodeLabels_branch G P x a hal
  · change twistNodeLabels G P x ((eB P a).child RS'.excluded) = x (a.child RS.excluded)
    rw [h.excluded_eq]
    exact twistNodeLabels_other_child G P x hp a hal _
  · exact stw_label_pos P h x
  · exact stw_label_neg P h x

theorem stw_bdAt_iff {d : ℕ} (L : ℝ) (base : Mom d) (β : Fin 4 → Mom d) (x : GNode G.tree → (Fin d → ℤ))
    (hp : PairedAt P x) : BdAt RS L base β x ↔ BdAt RS' L base β (twistNodeLabels G P x) := by
  unfold BdAt
  refine forall_congr' fun j => ?_
  rw [stw_label_bd P h x hp j]

theorem stw_freeDec_iff {d : ℕ} (x : GNode G.tree → (Fin d → ℤ)) (hp : PairedAt P x) :
    FreeDec RS x ↔ FreeDec RS' (twistNodeLabels G P x) := by
  have hbS : b ∈ S := h.block.2.2.1
  have hbS' : eB P b ∈ twistedAtoms G P S := (mem_twistedAtoms G P S b).mpr hbS
  unfold FreeDec
  rw [stw_free_zero_iff P h x, consOn_iff_erase hbS, consOn_iff_erase hbS', h.cons_iff x hp,
    stw_consAt_iff P h x, h.leaf_iff x hp]

end WaveTurbulence.VineEstS5B2
