/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowStep
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AssemblyReach
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Kernel

/-! # Rows of a reached state (V5 Step 4b, step 1)

Along any `Reach`:
* `Reach.localInc_le`: `M₁` (the sum of the incoherency counts of the regional couples and interior trees) of the reached
  state is at least that of the start (ordinary rows are LF-invariant, the two exceptional objects of every operation are
  coherent in the source).  Hence `L^{-η⁸(cohmol + M₁)}` is no larger at the reached garden than at the start.
* `Reach.rowsCoh`: the chart-free row coherence `RowsCoh` of the start is carried to the reached state: either no operation
  was applied (the state is the start) or the state is canonical (the output of an LF operation), where every
  coherent row is coherent by `rowsCoh_of_canonical`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.Links WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton VineParamContract TTree
variable {w : ℕ} {ι : Type*}

theorem localInc_step {p : ℕ} {kind : Bool} (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) (i : ι)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    localInc A.data A.plain A.layered c.U c.a ≤
      localInc op.output.data op.output.plain op.output.layered (ChainAt.nextA A c i op.choice).U
        (ChainAt.nextA A c i op.choice).a := by
  rw [nextA_U, nextA_a]
  exact localInc_step_le op.construction (c.atoms_sub i)

/-- **`M₁` does not decrease along a batch.** -/
theorem Reach.localInc_le {p : ℕ} {kind : Bool} {M : List ι} {A B : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} {c' : ChainAt B.skeleton B.family} (h : Reach p kind M A c B c') :
    localInc A.data A.plain A.layered c.U c.a ≤ localInc B.data B.plain B.layered c'.U c'.a := by
  induction h with
  | nil A c => exact le_rfl
  | skip i h ih => exact ih
  | apply op h ih => exact (localInc_step _ _ _ op).trans ih

/-- Either no operation was applied, or the reached state is canonical. -/
theorem Reach.canonical_or_eq {p : ℕ} {kind : Bool} {M : List ι} {A B : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} {c' : ChainAt B.skeleton B.family} (h : Reach p kind M A c B c') :
    (B = A ∧ HEq c' c) ∨ CanonicalObject p kind B.layered := by
  induction h with
  | nil A c => exact Or.inl ⟨rfl, HEq.rfl⟩
  | skip i h ih => exact ih
  | @apply L A c B c' i op h ih =>
    right
    rcases ih with ⟨hB, _⟩ | hc
    · subst hB
      exact op.output_canonical
    · exact hc

/-- The row coherence is carried from the start to every reached state. -/
theorem Reach.rowsCoh {p : ℕ} {kind : Bool} {M : List ι} {A B : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} {c' : ChainAt B.skeleton B.family} (h : Reach p kind M A c B c')
    (hA : RowsCoh A.data A.plain (stateLayer A) (stateLayer_isLayering A) p c.U c.a) :
    RowsCoh B.data B.plain (stateLayer B) (stateLayer_isLayering B) p c'.U c'.a := by
  rcases h.canonical_or_eq with ⟨hB, hc⟩ | hcan
  · subst hB
    have := eq_of_heq hc
    subst this
    exact hA
  · refine rowsCoh_of_canonical B.data B.plain (stateLayer B) (stateLayer_isLayering B) c'.block
      (clRegionData B.skeleton c'.block c'.cl) p ?_
    rw [stateLayer_spec B]
    exact canonGC_of_canonicalObject hcan

section Assemblies
variable {p : ℕ} {kind : Bool} {M : List ι} {A B : FamilyReconstruction w ι}
  {c : ChainAt A.skeleton A.family} {c' : ChainAt B.skeleton B.family} {n : ℕ}
  (hM9 : VINEPARAM) (h : Reach p kind M A c B c')
  (B0 : CLChainAssembly A.skeleton (clRegionData A.skeleton c.block c.cl) n)
  (B1 : CLChainAssembly B.skeleton (clRegionData B.skeleton c'.block c'.cl) n)
include h

/-- **`M₁` of the reached garden is at least `M₁` of the start** (for any assemblies of the two regions). -/
theorem Reach.m1_ge {d : ℕ} (bk0 : Fin (assemblyShape hM9 B0).I → Fin 4) (q0 : Fin 3 → ℕ)
    (bk1 : Fin (assemblyShape hM9 B1).I → Fin 4) (q1 : Fin 3 → ℕ) (centre : Fin 4 → Mom d) (wBar : Mom d) :
    (step3D hM9 B0 A.data A.plain (stateLayer A) (stateLayer_isLayering A) bk0 q0 centre wBar).M₁ ≤
      (step3D hM9 B1 B.data B.plain (stateLayer B) (stateLayer_isLayering B) bk1 q1 centre wBar).M₁ := by
  rw [step3D_M1, step3D_M1, stateLayer_spec, stateLayer_spec]
  exact h.localInc_le

/-- **`RowCoherent` of the reached garden** (any assembly of the reached region) follows from `RowCoherent` of the
start (any assembly of the start region). -/
theorem Reach.rowCoherent {d : ℕ} (bk0 : Fin (assemblyShape hM9 B0).I → Fin 4) (q0 : Fin 3 → ℕ)
    (bk1 : Fin (assemblyShape hM9 B1).I → Fin 4) (q1 : Fin 3 → ℕ) (centre : Fin 4 → Mom d) (wBar : Mom d)
    (hq0 : q0 0 = stateLayer A (A.data.coreBranch A.plain c.a).toNode)
    (hq1 : q1 0 = stateLayer B (B.data.coreBranch B.plain c'.a).toNode)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (H : RowCoherent hM9 B0 A.data A.plain (stateLayer A) (stateLayer_isLayering A)
      (step3W hM9 B0 A.data A.plain (stateLayer A) (stateLayer_isLayering A) bk0 q0 centre wBar) L γ δ F p) :
    RowCoherent hM9 B1 B.data B.plain (stateLayer B) (stateLayer_isLayering B)
      (step3W hM9 B1 B.data B.plain (stateLayer B) (stateLayer_isLayering B) bk1 q1 centre wBar) L γ δ F p := by
  rw [rowCoherent_iff hM9 B1 B.data B.plain (stateLayer B) (stateLayer_isLayering B) _ rfl hq1]
  rw [rowCoherent_iff hM9 B0 A.data A.plain (stateLayer A) (stateLayer_isLayering A) _ rfl hq0] at H
  exact h.rowsCoh H

end Assemblies

end WaveTurbulence.VineEstS4
