/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatDict
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.WinX
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.DomEng
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.ExcInd
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RowMatch
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.DomEng` (sha256 fb648733e9538992…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 10, step 4.2): the clock domain with exceptional branches

* `interior_lt_top_exc`: if every interior clock off `Bex` is below its parent clock and every clock in `Bex` is below the clock of some interior
  branch, then every interior clock is below the top clock (the maximum of the interior clocks cannot lie in `Bex`, and off `Bex` its parent
  clock is the top clock).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS4

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)

open Classical in
/-- **The constraints of an engine datum with exceptional branches**: the native parent constraints and layer-order pairs whose smaller clock
is not that of an exceptional branch, plus the extra pairs `add`. -/
noncomputable def consXΓ (layer0 : GBranch G.tree → ℕ) (Bex : Finset (GBranch G.tree))
    (add : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) :
    Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar) :=
  ((assemblyTimeConstraintsΓ hM9 B ∪ layerOrderPairs (assemblyTimeQΓ hM9 B layer0)).filter
    fun c => (assemblyClockAtomEquivΓ hM9 B c.1).1 ∉ Bex) ∪ add

/-- The engine time domain, written out. -/
def EngDomPΓ (q : (assemblyShapeΓ hM9 B).TVar → ℕ) (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar))
    (hI : 0 < (assemblyShapeΓ hM9 B).I) (tt : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) : Prop :=
  (∀ s, (q s : ℝ) ≤ τ s ∧ τ s ≤ q s + 1 ∧ τ s < tt 0) ∧ max (tt 1) (tt 2) < τ (.inl ⟨⟨0, hI⟩, 0⟩) ∧
    ∀ c ∈ cons, τ c.1 < τ c.2

variable (hG : G.IsPlain)

/-- The engine datum's time domain is `EngDomP` (with the datum's `q` and constraints). -/
theorem mem_engTimeDom_iff'Γ (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (wN wDec : ℕ)
    (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)
    (tt : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) :
    τ ∈ (engDatumΓ hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_posΓ hM9 B) (tt 0) (tt 1) (tt 2) ↔
      EngDomPΓ hM9 B W.q cons (assemblyShape_I_posΓ hM9 B) tt τ := by
  cases W with
  | mk wK wL g0 g0' param q constraints badKind qOut centre wBar => exact Iff.rfl

variable {hG}

/-- **Engine domain `⊆` `DomX`** (off the window boundaries). -/
theorem engDom_to_domXΓ (layer0 : GBranch G.tree → ℕ) (Bex : Finset (GBranch G.tree))
    (add : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (hI : 0 < (assemblyShapeΓ hM9 B).I)
    (tt : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ)
    (hbd : ∀ s, τ s ≠ assemblyTimeQΓ hM9 B layer0 s ∧ τ s ≠ assemblyTimeQΓ hM9 B layer0 s + 1)
    (hD : EngDomPΓ hM9 B (assemblyTimeQΓ hM9 B layer0) (consXΓ hM9 B layer0 Bex add) hI tt τ) :
    DomX R layer0 Bex (tt 0) (tt 1) (tt 2) (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ)) := by
  classical
  obtain ⟨hwin, hjoin, hcon⟩ := hD
  have hb : (assemblyClockAtomEquivΓ hM9 B (.inl ⟨⟨0, hI⟩, 0⟩)).1 = b := assemblyClockAtom_firstΓ hM9 B hI
  have hbclock : clLocalClock R tt (assemblyClockEquivΓ hM9 B τ) b = τ (.inl ⟨⟨0, hI⟩, 0⟩) := by
    have := clLocalClock_slotΓ hM9 B tt τ (.inl ⟨⟨0, hI⟩, 0⟩)
    rwa [hb] at this
  refine ⟨fun v hvI => ?_, fun _ => ?_, fun _ => ?_⟩
  · obtain ⟨s, hsv⟩ := (assemblyClockAtomEquivΓ hM9 B).surjective ⟨v, hvI⟩
    have hsv' : (assemblyClockAtomEquivΓ hM9 B s).1 = v := congrArg Subtype.val hsv
    subst hsv'
    have hv : clLocalClock R tt (assemblyClockEquivΓ hM9 B τ) (assemblyClockAtomEquivΓ hM9 B s).1 = τ s :=
      clLocalClock_slotΓ hM9 B tt τ s
    obtain ⟨h1, h2, h3⟩ := hwin s
    have hq0 : (0 : ℝ) ≤ assemblyTimeQΓ hM9 B layer0 s := Nat.cast_nonneg _
    have hlow : (assemblyTimeQΓ hM9 B layer0 s : ℝ) < τ s := lt_of_le_of_ne h1 (hbd s).1.symm
    refine ⟨?_, ?_, ?_, fun hnb => ?_⟩
    · rw [hv]; exact hlow
    · rw [hv]; exact lt_of_le_of_ne h2 (hbd s).2
    · rw [hv]; exact hq0.trans_lt hlow
    · rw [hv]
      rcases slot_parent_clockΓ hM9 B tt τ s with ⟨hp, _⟩ | ⟨s', hs', hp⟩
      · rw [hp]; exact h3
      · rw [hp]
        exact hcon _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hs', hnb⟩))
  · rw [hbclock]; exact (le_max_left _ _).trans_lt hjoin
  · rw [hbclock]; exact (le_max_right _ _).trans_lt hjoin

/-- `domX_to_engDom` with the weaker exceptional hypothesis of `interior_lt_top_exc2`. **`DomX` `⊆` engine domain**, given the extra pairs `add` and that each exceptional clock is below the clock of an interior branch. -/
theorem domX_to_engDom2Γ (layer0 : GBranch G.tree → ℕ) (Bex : Finset (GBranch G.tree))
    (add : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (hI : 0 < (assemblyShapeΓ hM9 B).I)
    (tt : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ)
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      tt 1 ≤ assemblyTimeQΓ hM9 B layer0 (.inl ⟨⟨0, hI⟩, 0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      tt 2 ≤ assemblyTimeQΓ hM9 B layer0 (.inl ⟨⟨0, hI⟩, 0⟩))
    (hD : DomX R layer0 Bex (tt 0) (tt 1) (tt 2) (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ)))
    (hB : ∀ v ∈ Bex, clLocalClock R tt (assemblyClockEquivΓ hM9 B τ) v < tt 0 ∨ ∃ x ∈ U, x ≠ a ∧
      clLocalClock R tt (assemblyClockEquivΓ hM9 B τ) v < clLocalClock R tt (assemblyClockEquivΓ hM9 B τ) x)
    (hadd : ∀ c ∈ add, τ c.1 < τ c.2) :
    EngDomPΓ hM9 B (assemblyTimeQΓ hM9 B layer0) (consXΓ hM9 B layer0 Bex add) hI tt τ := by
  classical
  set u := clLocalClock R tt (assemblyClockEquivΓ hM9 B τ) with hu
  have hslot : ∀ s, u (assemblyClockAtomEquivΓ hM9 B s).1 = τ s := fun s => clLocalClock_slotΓ hM9 B tt τ s
  have hlow : ∀ s, (assemblyTimeQΓ hM9 B layer0 s : ℝ) < τ s := fun s => by
    have := (hD.1 _ (assemblyClockAtomEquivΓ hM9 B s).2).1
    rwa [hslot s] at this
  have hup : ∀ s, τ s < assemblyTimeQΓ hM9 B layer0 s + 1 := fun s => by
    have := (hD.1 _ (assemblyClockAtomEquivΓ hM9 B s).2).2.1
    rwa [hslot s] at this
  have hlt : ∀ s, τ s < tt 0 := by
    intro s
    have hs' := Finset.mem_erase.mp (assemblyClockAtomEquivΓ hM9 B s).2
    have hyp : ∀ v ∈ U, v ≠ a → v ∉ Bex → u v < parentClock (tt 0) u v.toNode := fun v hv hva hvB =>
      (hD.1 v (Finset.mem_erase.mpr ⟨hva, hv⟩)).2.2.2 hvB
    have h0 := interior_lt_top_exc2 B.isBlock R (tt 0) u (clLocalClock_upper R tt _) Bex hyp hB _ hs'.2 hs'.1
    rwa [hslot s] at h0
  have hb : (assemblyClockAtomEquivΓ hM9 B (.inl ⟨⟨0, hI⟩, 0⟩)).1 = b := assemblyClockAtom_firstΓ hM9 B hI
  have hbclock : u b = τ (.inl ⟨⟨0, hI⟩, 0⟩) := by
    have := clLocalClock_slotΓ hM9 B tt τ (.inl ⟨⟨0, hI⟩, 0⟩)
    rwa [hb] at this
  refine ⟨fun s => ⟨(hlow s).le, (hup s).le, hlt s⟩, ?_, fun c hc => ?_⟩
  · rw [max_lt_iff]
    refine ⟨?_, ?_⟩
    · rcases hp with hb1 | hle
      · rw [← hbclock]; exact hD.2.1 hb1
      · exact lt_of_le_of_lt hle (hlow _)
    · rcases hn with hb2 | hle
      · rw [← hbclock]; exact hD.2.2 hb2
      · exact lt_of_le_of_lt hle (hlow _)
  · rcases Finset.mem_union.mp hc with hc | hc
    · obtain ⟨hc1, hnb⟩ := Finset.mem_filter.mp hc
      rcases Finset.mem_union.mp hc1 with hcn | hcl
      · have h1 := (hD.1 _ (assemblyClockAtomEquivΓ hM9 B c.1).2).2.2.2 hnb
        rw [hslot c.1, constraint_parent_clockΓ hM9 B tt τ c hcn] at h1
        exact h1
      · have hq := (mem_layerOrderPairs _ c).mp hcl
        have hq' : (assemblyTimeQΓ hM9 B layer0 c.1 : ℝ) + 1 ≤ assemblyTimeQΓ hM9 B layer0 c.2 := by exact_mod_cast hq
        exact (hup c.1).trans_le (hq'.trans (hlow c.2).le)
    · exact hadd c hc

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
