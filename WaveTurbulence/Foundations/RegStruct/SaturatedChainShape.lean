/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainSpines

/-! # The actual saturated tree shape of a bare chain code -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- A single branching spine, with all off-spine children trivial. -/
def spineContext : Path → TTree → TTree
  | [],h => h
  | i :: p,h => node3 (fun j => if j = i then spineContext p h else .leaf)

/-- Spine contexts concatenate by literal substitution in the terminal slot. -/
theorem spineContext_append (p q : Path) (h : TTree) :
    spineContext (p ++ q) h = spineContext p (spineContext q h) := by
  induction p with
  | nil => rfl
  | cons i p ih => simp only [List.cons_append,spineContext,ih]

/-- Every bare code has exactly the single-spine saturated shape described in DH21 Proposition 4.7. -/
theorem bareChain_plug_spine (X : RegChain) (hX : BareChain X) (ζ : ℤˣ) (h : TTree) :
    X.plug ζ h = spineContext X.lonePath h := by
  cases X with
  | nil => rfl
  | pair k r g i s =>
    obtain ⟨rfl,rfl,hi,hs⟩ := hX
    rw [RegChain.lonePath]
    simp only [spineContext_append,spineContext]
    obtain ⟨c,b⟩ := k
    fin_cases c <;> fin_cases b <;>
      simp [RegChain.plug,node3,RegCpl.trees,treeOfSign,MiniTreeCode.lone,
        bareChain_plug_spine i hi,bareChain_plug_spine s hs]
termination_by structural X

/-- Each spine edge corresponds to exactly one branching node. -/
theorem spineContext_order (p : Path) (h : TTree) :
    (spineContext p h).order = p.length + h.order := by
  induction p with
  | nil => simp [spineContext]
  | cons i p ih =>
    fin_cases i <;> simp [spineContext,node3,TTree.order,ih] <;> omega

/-- The spine has the same even length as the bare chain's branching order. -/
theorem bareChain_lonePath_length (X : RegChain) (hX : BareChain X) :
    X.lonePath.length = 2 * (chainShape X).numNodes := by
  have hp := congrArg TTree.order (bareChain_plug_spine X hX 1 .leaf)
  rw [code_plug_order,spineContext_order,TTree.order,Nat.add_zero,Nat.add_zero,bareChain_size X hX] at hp
  exact hp.symm

/-- The literal branching prefixes of a saturated spine. -/
def spinePrefixes : Path → Finset Path
  | [] => ∅
  | i :: p => insert [] (TTree.pre i (spinePrefixes p))

/-- Its branching addresses are precisely the proper prefixes along the spine. -/
theorem spineContext_branching (p : Path) : (spineContext p .leaf).branching = spinePrefixes p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    fin_cases i <;> simp [spineContext,node3,TTree.branching,spinePrefixes,ih,TTree.pre]

/-- Every branching node lies strictly above the lone leaf. -/
theorem mem_spinePrefixes {p q : Path} (hq : q ∈ spinePrefixes p) : q <+: p ∧ q.length < p.length := by
  induction p generalizing q with
  | nil => simp [spinePrefixes] at hq
  | cons i p ih =>
    simp only [spinePrefixes,Finset.mem_insert,TTree.pre,Finset.mem_image] at hq
    rcases hq with rfl | ⟨r,hr,rfl⟩
    · exact ⟨List.nil_prefix,by simp⟩
    · have h := ih hr
      exact ⟨List.cons_prefix_cons.mpr ⟨rfl,h.1⟩,by simpa only [List.length_cons] using Nat.add_lt_add_right h.2 1⟩

/-- Branching nodes of a bare chain are linearly ordered by ancestry. -/
theorem bareChain_branching_comparable (X : RegChain) (hX : BareChain X) (ζ : ℤˣ)
    {p q : Path} (hp : p ∈ (X.plug ζ .leaf).branching) (hq : q ∈ (X.plug ζ .leaf).branching) :
    p <+: q ∨ q <+: p := by
  rw [bareChain_plug_spine X hX,spineContext_branching] at hp hq
  exact List.prefix_or_prefix_of_prefix (mem_spinePrefixes hp).1 (mem_spinePrefixes hq).1

end WaveTurbulence.Reg
