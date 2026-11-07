/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcMom
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.StateInt1

/-! # P4-W2 (b1): `low - ret = ±(gap)` at a split

`region_lower_eq_of_subset`: the slots `kept`, `positive`, `negative` of two nested blocks with the same lower joint agree.  `split_low_ret`: for a split at the lower joint of a
placement, `σ_b (x_b - x_{retained}) = x_{b'.pos} - x_{b'.neg}` for ANY block `V ⊇ T` with the same bottom (local decorations: conservation on `V`, matching of the internal leaves of `V`). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.RegRed TTree WaveTurbulence.VineEstS4 WaveTurbulence.Twist WaveTurbulence.VineEstS5B
variable {w d : ℕ}

section Nested
variable {G : Garden w} {U1 U2 : Finset (GBranch G.tree)} {a1 a2 b : GBranch G.tree}

theorem internalPositions_mono (h : U1 ⊆ U2) (v : GBranch G.tree) :
    Mole.internalPositions G U1 v ⊆ Mole.internalPositions G U2 v := by
  intro i hi
  obtain ⟨x, hx, hg, hp⟩ := (Mole.mem_internalPositions G).mp hi
  exact (Mole.mem_internalPositions G).mpr ⟨x, hx, ⟨h hg.1, h hg.2⟩, hp⟩

/-- **The slots at the common lower joint agree for nested blocks**: `kept`, `positive`, `negative`. -/
theorem region_lower_eq_of_subset (h : U1 ⊆ U2) (R1 : CLRegionData G U1 a1 b) (R2 : CLRegionData G U2 a2 b) :
    R1.kept = R2.kept ∧ R1.positive = R2.positive ∧ R1.negative = R2.negative := by
  have hk : R1.kept = R2.kept := by
    have h1 := (R1.lower R1.kept).mpr rfl
    exact (R2.lower R1.kept).mp (internalPositions_mono h b h1)
  have hpos : R2.positive ≠ R2.kept := fun h' => by
    have := (R2.lower_excluded R2.positive).mpr (Or.inl rfl)
    exact this h'
  have hneg : R2.negative ≠ R2.kept := fun h' => by
    have := (R2.lower_excluded R2.negative).mpr (Or.inr rfl)
    exact this h'
  have hpos' := (R1.lower_excluded R2.positive).mp (hk ▸ hpos)
  have hneg' := (R1.lower_excluded R2.negative).mp (hk ▸ hneg)
  have s1 := R2.positive_sign
  have s2 := R2.negative_sign
  have t1 := R1.positive_sign
  have t2 := R1.negative_sign
  refine ⟨hk, ?_⟩
  rcases hpos' with h5 | h5 <;> rcases hneg' with h6 | h6
  · exact (R2.distinct (h5.trans h6.symm)).elim
  · exact ⟨h5.symm, h6.symm⟩
  · exfalso
    rw [h5, t2] at s1
    exact absurd s1 (by decide)
  · exact (R2.distinct (h5.trans h6.symm)).elim

end Nested

/-- **`low - ret = ±(top gap)`**: for a split at the lower joint of a placement (`retained = lower.child kept`), the signed difference of the lattice values at the
lower joint and at the retained leaf is the difference of the lattice values at the two lower children `b.child positive/negative` of ANY block `V ⊇ T`
with the same bottom `b` (so of the whole region). -/
theorem split_low_ret {S : Garden w} {ι : Type*} {F : CoreFamily S ι} {pstar : ι} {J : Set ι}
    (sp : SplitAt S F pstar J) (L : ℝ) (x : GNode S.tree → (Fin d → ℤ))
    {V : Finset (GBranch S.tree)} {aV : GBranch S.tree} (RV : CLRegionData S V aV sp.tb.b) (hsub : sp.tb.U ⊆ V)
    (hc : ∀ v ∈ V, x v.toNode = x (v.child 0) - x (v.child 1) + x (v.child 2))
    (hl : ∀ ℓ, Mole.IsInternalLeaf S V ℓ → x ℓ.toNode = x (S.pair ℓ).toNode) :
    ((S.sign (F.placement pstar).lower.toNode : ℤ) : ℝ) •
        (latticePoint L (x (F.placement pstar).lower.toNode) - latticePoint L (x (F.placement pstar).retained.toNode)) =
      latticePoint L (x (sp.tb.b.child RV.positive)) - latticePoint L (x (sp.tb.b.child RV.negative)) := by
  have hS := SplitAt.slow sp
  have hn0 : sp.sb.b.toNode = (F.placement pstar).lower.toNode := congrArg GBranch.toNode hS.lower
  have hn1 : sp.sb.b.child sp.RS.kept = (F.placement pstar).retained.toNode := by
    rw [hS.keep, hS.lower]
    exact (F.placement pstar).child.symm
  have h := split_gap_lattice (d := d) sp L x (fun v hv => hc v (hsub hv))
    (fun ℓ hℓ => hl ℓ ⟨hℓ.1, hℓ.2.1, hℓ.2.2.1, ⟨hsub hℓ.2.2.2.1, hsub hℓ.2.2.2.2⟩⟩)
  rw [hn0, hn1] at h
  have hpn := region_lower_eq_of_subset hsub sp.RT RV
  rw [hpn.2.1, hpn.2.2] at h
  exact h

end WaveTurbulence.VineEstS5C.P4.W2
