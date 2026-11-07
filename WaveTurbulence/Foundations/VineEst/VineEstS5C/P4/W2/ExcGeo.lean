/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcMom2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcFam
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.BadCount
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClauseA

/-! # P4-W2 (b1): the geometry of an exceptional record

For a record coming from the operative member `pstar` of a level `lv` (first disjunct of `ExcOf`), with the split `sp = lv.split ..` and the
placement `P`:

* `split_sb_b`: the lower joint of the upper block `sp.sb` is the lower joint `(assemblyPieceAt B i).lower` of the piece `i = (lv.e pstar).1`;
* `clock_lower_piece`: its clock is the sumint clock `t₀ⁱ = τ (.inl ⟨i, 0⟩)`;
* `brSlot`, `brSlot_spec`: the clock of ANY branch of the region is `τ` of a sumint clock, or the exterior clock `t 0` (the top joint);
* `exc_low_ret_eps`: `low = ret + ε r` with `|ε| = 1` and `r = E₀ - E₁` (momentum conservation at the lower joint);
* `rA_lower`, `rA_retained`, `exc_vars`: `bundleVars` at `rA RS (f x)` is `bundleVars`-like data of the OUTER decoration `x`;
* `lower_real_c`, `retained_real_c`: the lower joint and the retained leaf lie in the realization of `lv.c.U`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13

variable {w d : ℕ}

section Gap

theorem exc_gap {S : Garden w} {ι : Type*} {F : CoreFamily S ι} {pstar : ι} {J : Set ι}
    (sp : SplitAt S F pstar J) {U : Finset (GBranch S.tree)} {a b : GBranch S.tree} (R : CLRegionData S U a b)
    (hb : sp.tb.b = b) (hsub : sp.tb.U ⊆ U) (L : ℝ) (base : Mom d) (β' : Fin 4 → Mom d)
    (κ : CLLocalDecoration R L base β') :
    ((S.sign (F.placement pstar).lower.toNode : ℤ) : ℝ) •
        (latticePoint L (clExtendIndices R κ.1 (F.placement pstar).lower.toNode) -
          latticePoint L (clExtendIndices R κ.1 (F.placement pstar).retained.toNode)) =
      β' 2 - β' 3 := by
  subst hb
  have h := split_low_ret sp L (clExtendIndices R κ.1) R hsub κ.2.1 κ.2.2.1
  rw [h]
  have h2 := κ.2.2.2 2
  have h3 := κ.2.2.2 3
  simp only [clBoundaryNodes, Matrix.cons_val_two, Matrix.cons_val_three] at h2 h3
  rw [← h2, ← h3]
  abel

/-- **`low = ret + ε r`**: with `r = E₀ - E₁` the gap of the integer boundary, `|ε| = 1`. -/
theorem exc_low_ret_eps {S : Garden w} {ι : Type*} {F : CoreFamily S ι} {pstar : ι} {J : Set ι}
    (sp : SplitAt S F pstar J) {U : Finset (GBranch S.tree)} {a b : GBranch S.tree} (R : CLRegionData S U a b)
    (hb : sp.tb.b = b) (hsub : sp.tb.U ⊆ U) (L : ℝ) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((S.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
    (κ : CLLocalDecoration R L base (fun j => base + latticePoint L (β j))) :
    ∃ ε : ℝ, |ε| = 1 ∧
      base + latticePoint L (clExtendIndices R κ.1 (F.placement pstar).lower.toNode) =
        (base + latticePoint L (clExtendIndices R κ.1 (F.placement pstar).retained.toNode)) +
          ε • (sumintBoundary (S.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (S.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) := by
  have h := exc_gap sp R hb hsub L base _ κ
  have hg := sumintBoundary_gap_physical (L := L) (S.sign a.toNode) base β hβ
  rw [hg]
  set σ : ℝ := ((S.sign (F.placement pstar).lower.toNode : ℤ) : ℝ) with hσ
  have hσ1 : σ = 1 ∨ σ = -1 := by
    rcases Int.units_eq_one_or (S.sign (F.placement pstar).lower.toNode) with h1 | h1 <;> simp [hσ, h1]
  refine ⟨-σ, by rcases hσ1 with h1 | h1 <;> simp [h1], ?_⟩
  have h' : latticePoint L (clExtendIndices R κ.1 (F.placement pstar).lower.toNode) -
      latticePoint L (clExtendIndices R κ.1 (F.placement pstar).retained.toNode) =
      σ • ((base + latticePoint L (β 2)) - (base + latticePoint L (β 3))) := by
    have := congrArg (fun z => σ • z) h
    simp only [smul_smul] at this
    rcases hσ1 with h1 | h1 <;> rw [h1] at this ⊢ <;> simpa using this
  have hl : latticePoint L (β 2 - β 3) = latticePoint L (β 2) - latticePoint L (β 3) :=
    map_sub (latticePointAddHom (d := d) L) (β 2) (β 3)
  rw [hl, neg_smul, smul_neg, neg_neg]
  have h3 : latticePoint L (clExtendIndices R κ.1 (F.placement pstar).lower.toNode) =
      latticePoint L (clExtendIndices R κ.1 (F.placement pstar).retained.toNode) +
        σ • (latticePoint L (β 2) - latticePoint L (β 3)) := by
    have e : (base + latticePoint L (β 2)) - (base + latticePoint L (β 3)) =
        latticePoint L (β 2) - latticePoint L (β 3) := by abel
    rw [e] at h'
    rw [← h']; abel
  rw [h3]; abel

end Gap

section Clock
variable {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n)

/-- **The clock of the lower joint of the piece `i` is `t₀ⁱ`.** -/
theorem clock_lower_piece (tt : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ) (i : Fin n) :
    clLocalClock R tt (assemblyClockEquiv hM9 B τ) (assemblyPieceAt B i).lower = τ (.inl ⟨i, 0⟩) := by
  rw [← clock_t0 hM9 B i]
  exact clLocalClock_slot hM9 B tt τ _

open Classical in
/-- The slot (sumint clock or exterior clock) of a branch of the region. -/
noncomputable def brSlot (v : GBranch G.tree) : (assemblyShape hM9 B).TVar ⊕ Fin 3 :=
  if h : v ∈ clInteriorBranches R then Sum.inl (branchSlot hM9 B ⟨v, h⟩) else Sum.inr 0

/-- **The clock of any branch of the region** is the sumint clock of its slot, or the exterior clock `t 0` (for the top joint). -/
theorem brSlot_spec {v : GBranch G.tree} (hv : v ∈ U) (tt : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ) :
    clLocalClock R tt (assemblyClockEquiv hM9 B τ) v = Sum.elim τ tt (brSlot hM9 B v) := by
  classical
  by_cases hva : v = a
  · subst hva
    have hn : v ∉ clInteriorBranches R := fun h => (Finset.mem_erase.mp h).1 rfl
    simp only [brSlot, dif_neg hn, Sum.elim_inr]
    exact clLocalClock_upper R tt _
  · have hi : v ∈ clInteriorBranches R := Finset.mem_erase.mpr ⟨hva, hv⟩
    simp only [brSlot, dif_pos hi, Sum.elim_inl]
    exact branchSlot_spec hM9 B ⟨v, hi⟩ tt τ

end Clock

section Split
variable {ι : Type*} {pstar : ι} {J : Set ι}

theorem isInternalLeaf_mono {S : Garden w} {U V : Finset (GBranch S.tree)} (h : U ⊆ V) {ℓ : GLeaf S.tree}
    (hℓ : Mole.IsInternalLeaf S U ℓ) : Mole.IsInternalLeaf S V ℓ :=
  ⟨hℓ.1, hℓ.2.1, hℓ.2.2.1, ⟨h hℓ.2.2.2.1, h hℓ.2.2.2.2⟩⟩

/-- The lower joint lies in the realization of the whole chain region. -/
theorem lower_real_c {S : Garden w} {F : CoreFamily S ι} (sp : SplitAt S F pstar J) :
    (F.placement pstar).lower.toNode ∈ clRealizationNodes S sp.c.U := by
  have h := SplitAt.slow sp
  refine (branch_mem_clRealizationNodes _).mpr ?_
  rw [sp.union]
  exact Finset.mem_union_left _ h.lower_mem

/-- The retained leaf lies in the realization of the whole chain region. -/
theorem retained_real_c {S : Garden w} {F : CoreFamily S ι} (sp : SplitAt S F pstar J) :
    (F.placement pstar).retained.toNode ∈ clRealizationNodes S sp.c.U := by
  have h := SplitAt.slow sp
  refine (leaf_mem_clRealizationNodes _).mpr (isInternalLeaf_mono ?_ h.retained_internal)
  rw [sp.union]
  exact Finset.subset_union_left

theorem rA_lower {S : Garden w} {F : CoreFamily S ι} (sp : SplitAt S F pstar J) (x : GNode S.tree → (Fin d → ℤ)) :
    rA sp.RS x (F.placement pstar).lower.toNode = x (F.placement pstar).lower.toNode := by
  have h := SplitAt.slow sp
  have hm : (F.placement pstar).lower.toNode ∈ splitA sp.RS :=
    Finset.mem_union_left _ ((branch_mem_clRealizationNodes _).mpr h.lower_mem)
  unfold rA
  rw [if_pos hm]

theorem rA_retained {S : Garden w} {F : CoreFamily S ι} (sp : SplitAt S F pstar J) (x : GNode S.tree → (Fin d → ℤ)) :
    rA sp.RS x (F.placement pstar).retained.toNode = x (F.placement pstar).retained.toNode := by
  have h := SplitAt.slow sp
  have hm : (F.placement pstar).retained.toNode ∈ splitA sp.RS :=
    Finset.mem_union_left _ ((leaf_mem_clRealizationNodes _).mpr h.retained_internal)
  unfold rA
  rw [if_pos hm]

end Split

section Vars
variable {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **`bundleVars` at the restricted decoration** `rA RS (f x)` is the data of the outer decoration `x`: the lower joint and the retained leaf carry the
outer labels. -/
theorem exc_vars (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (κ0 : KPar d)
    (f : (GNode G.tree → (Fin d → ℤ)) → (GNode G.tree → (Fin d → ℤ)))
    (hf : ∀ x, ∀ y ∈ clRealizationNodes G lv.c.U, f x y = x y) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) :
    bundleVars κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk)
        (rA (lv.split B RD hG layer hLayer pstar hk).RS (f x)) u =
      (u (lv.split B RD hG layer hLayer pstar hk).sb.b,
        dictS1 (nuOf (lv.state B RD hG layer hLayer) pstar)
          (u (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar)))
          (u (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar))),
        dictT1 (nuOf (lv.state B RD hG layer hLayer) pstar)
          (u (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar)))
          (u (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar))),
        dictX (nuOf (lv.state B RD hG layer hLayer) pstar)
          (κ0.base + latticePoint κ0.L (x ((lv.state B RD hG layer hLayer).family.placement pstar).lower.toNode))
          (κ0.base + latticePoint κ0.L (x ((lv.state B RD hG layer hLayer).family.placement pstar).retained.toNode)),
        dictY (nuOf (lv.state B RD hG layer hLayer) pstar)
          (κ0.base + latticePoint κ0.L (x ((lv.state B RD hG layer hLayer).family.placement pstar).lower.toNode))
          (κ0.base + latticePoint κ0.L (x ((lv.state B RD hG layer hLayer).family.placement pstar).retained.toNode))) := by
  set sp := lv.split B RD hG layer hLayer pstar hk
  have h1 : rA sp.RS (f x) ((lv.state B RD hG layer hLayer).family.placement pstar).lower.toNode =
      x ((lv.state B RD hG layer hLayer).family.placement pstar).lower.toNode :=
    (rA_lower sp (f x)).trans (hf x _ (lower_real_c sp))
  have h2 : rA sp.RS (f x) ((lv.state B RD hG layer hLayer).family.placement pstar).retained.toNode =
      x ((lv.state B RD hG layer hLayer).family.placement pstar).retained.toNode :=
    (rA_retained sp (f x)).trans (hf x _ (retained_real_c sp))
  unfold bundleVars
  rw [h1, h2]
  rfl

theorem split_sb_b (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) :
    (lv.split B RD hG layer hLayer pstar hk).sb.b = (assemblyPieceAt B (lv.e pstar).1).lower := by
  have h1 := (lv.split B RD hG layer hLayer pstar hk).joint
  have h2 := (lv.split B RD hG layer hLayer pstar hk).bk
  have h3 := start_lower B RD hG layer hLayer (lv.e pstar)
  rw [h1, h2]
  exact h3

end Vars

end WaveTurbulence.VineEstS5C.P4.W2
