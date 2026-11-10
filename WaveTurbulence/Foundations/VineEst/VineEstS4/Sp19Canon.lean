/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp16Main

/-! # (tildeJ2) over the canonical representatives (V5 Step 4b, step 4)

`sum_canonSp_eq_canon`: the sum over `canonSpFinset` (states with their split) of a function of (state, region) is the sum over
`canonFinset` (forgetting the split).  `tildeJ2_canon`: (tildeJ2) of `tildeJ2_of_split` stated over `canonFinset` of the region `sp0.c`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2 WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]

theorem sum_canonSp_eq_canon (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) {β : Type*} [AddCommMonoid β]
    (f : (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family) → β) :
    ∑ x ∈ canonSpFinset p kind pstar J A sp0 hA, f ⟨x.1, x.2.c⟩ = ∑ y ∈ canonFinsetK p kind A sp0.c, f y := by
  refine Finset.sum_nbij (fun x : ST w ι pstar J => (⟨x.1, x.2.c⟩ : Σ Bs : FamilyReconstruction w ι,
    ChainAt Bs.skeleton Bs.family)) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨M, hM, h⟩ := (mem_canonSpFinset p kind pstar J A sp0 hA).mp hx
    exact (mem_canonFinset hA).mpr ⟨M, hM, h.reach⟩
  · intro x hx x' hx' hxx
    obtain ⟨M, hM, h⟩ := (mem_canonSpFinset p kind pstar J A sp0 hA).mp hx
    obtain ⟨M', hM', h'⟩ := (mem_canonSpFinset p kind pstar J A sp0 hA).mp hx'
    have hs : x.1 = x'.1 := by
      have := hxx
      simp only [Sigma.mk.injEq] at this
      exact this.1
    exact st_ext hs (perm_univ_nodup hM) (perm_univ_nodup hM') h h'
  · intro y hy
    obtain ⟨M, hM, h⟩ := (mem_canonFinset hA).mp hy
    obtain ⟨sp', hsp⟩ := batch_reachSp h.batch sp0
    obtain ⟨y1, y2⟩ := y
    have hreg : y2 = sp'.c := Reach.region_unique (perm_univ_nodup hM) (perm_univ_nodup hM) h hsp.reach
    refine ⟨⟨y1, sp'⟩, (mem_canonSpFinset p kind pstar J A sp0 hA).mpr ⟨M, hM, hsp⟩, ?_⟩
    change (⟨y1, sp'.c⟩ : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family) = ⟨y1, y2⟩
    rw [hreg]
  · intro x hx
    rfl

end WaveTurbulence.VineEstS4
