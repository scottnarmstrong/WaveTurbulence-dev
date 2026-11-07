/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.AssemblyTwist
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Transport
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AtomLayers
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RealizationIso

/-! # The chain assembly of a reached state (V5 Step 4b, P2.2)

`Reach.exists_asm`: along any `Reach`, the chain assembly of the start (for the region `(U,a,b)` of the start) is
transported, by iterating `CLChainAssembly.twist`, to a chain assembly of the reached skeleton and its region.
`AsmCorr B0 B1 e`: the pieces correspond under a branch bijection `e` (same vine types, atoms, joints), so the vine
types (hence the number `b` of bad vines) are preserved.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.RegRed TTree
variable {w : ℕ} {ι : Type*}

/-- The pieces of two assemblies correspond under the branch bijection `e`. -/
@[expose] def AsmCorr {S S' : Garden w} {U : Finset (GBranch S.tree)} {a b : GBranch S.tree} {R : CLRegionData S U a b}
    {U' : Finset (GBranch S'.tree)} {a' b' : GBranch S'.tree} {R' : CLRegionData S' U' a' b'} {n : ℕ}
    (B0 : CLChainAssembly S R n) (B1 : CLChainAssembly S' R' n) (e : GBranch S.tree ≃ GBranch S'.tree) : Prop :=
  ∀ i, (assemblyPieceAt B1 i).vineType = (assemblyPieceAt B0 i).vineType ∧
    (∀ x, x ∈ (assemblyPieceAt B1 i).atoms ↔ e.symm x ∈ (assemblyPieceAt B0 i).atoms) ∧
    (assemblyPieceAt B1 i).upper = e (assemblyPieceAt B0 i).upper ∧
    (assemblyPieceAt B1 i).lower = e (assemblyPieceAt B0 i).lower ∧
    Vine.realizedGroupSets (pieceRealization B1 i) =
      (Vine.realizedGroupSets (pieceRealization B0 i)).image (Finset.image e)

theorem AsmCorr.refl {S : Garden w} {U : Finset (GBranch S.tree)} {a b : GBranch S.tree} {R : CLRegionData S U a b}
    {n : ℕ} (B0 : CLChainAssembly S R n) : AsmCorr B0 B0 (Equiv.refl _) :=
  fun i => ⟨rfl, fun _ => Iff.rfl, rfl, rfl, by
    ext t
    simp only [Finset.mem_image]
    constructor
    · intro ht
      exact ⟨t, ht, by ext x; simp⟩
    · rintro ⟨u, hu, rfl⟩
      convert hu using 1
      ext x; simp⟩

theorem AsmCorr.trans {S S' S'' : Garden w} {U : Finset (GBranch S.tree)} {a b : GBranch S.tree}
    {R : CLRegionData S U a b} {U' : Finset (GBranch S'.tree)} {a' b' : GBranch S'.tree}
    {R' : CLRegionData S' U' a' b'} {U'' : Finset (GBranch S''.tree)} {a'' b'' : GBranch S''.tree}
    {R'' : CLRegionData S'' U'' a'' b''} {n : ℕ} {B0 : CLChainAssembly S R n} {B1 : CLChainAssembly S' R' n}
    {B2 : CLChainAssembly S'' R'' n} {e : GBranch S.tree ≃ GBranch S'.tree} {f : GBranch S'.tree ≃ GBranch S''.tree}
    (h : AsmCorr B0 B1 e) (h' : AsmCorr B1 B2 f) : AsmCorr B0 B2 (e.trans f) := by
  intro i
  obtain ⟨t1, a1, u1, l1, g1⟩ := h i
  obtain ⟨t2, a2, u2, l2, g2⟩ := h' i
  refine ⟨t2.trans t1, fun x => ?_, by rw [u2, u1]; rfl, by rw [l2, l1]; rfl, ?_⟩
  · rw [a2 x, a1 (f.symm x)]
    rfl
  · rw [g2, g1, Finset.image_image]
    apply Finset.image_congr
    intro t _
    exact Finset.image_image

/-- One unit twist of the assembly (the twisted pieces correspond under `coreBranchEquiv`). -/
theorem AsmCorr.twist {G : Garden w} (P : CorePlacement G) {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (B : CLChainAssembly G R n) (U' : Finset (GBranch (unitTwistGarden G P).tree))
    (a' b' : GBranch (unitTwistGarden G P).tree) (hU : U' = twistedAtoms G P U) (ha : a' = coreBranchEquiv G P a)
    (hb : b' = coreBranchEquiv G P b) (R' : CLRegionData (unitTwistGarden G P) U' a' b') :
    AsmCorr B (CLChainAssembly.twist P B U' a' b' hU ha hb R') (coreBranchEquiv G P) := by
  intro i
  obtain ⟨h1, h2, h3, h4⟩ := assemblyPieceAt_twist P B U' a' b' hU ha hb R' i
  refine ⟨h1, fun x => ?_, h3, h4, ?_⟩
  swap
  · exact groups_of_corr G (unitTwistGarden G P) (unitTwistDirectedIso G P) (pieceRealization B i)
      (pieceRealization (CLChainAssembly.twist P B U' a' b' hU ha hb R') i) h2 h3 h4 (assemblyPieceAt B i).vine.1
  obtain ⟨v, rfl⟩ := (coreBranchEquiv G P).surjective x
  rw [h2]
  have e1 : (coreBranchEquiv G P).symm (coreBranchEquiv G P v) = v := (coreBranchEquiv G P).symm_apply_apply v
  exact (mem_twistedAtoms G P _ v).trans (Iff.of_eq (congrArg (· ∈ (assemblyPieceAt B i).atoms) e1.symm))

theorem cast_motive {S : Garden w} {F F' : CoreFamily S ι} (e : F = F') (x : ChainAt S F)
    (Φ : ∀ (U : Finset (GBranch S.tree)) (a b : GBranch S.tree) (_ : S.molecule.IsBlock U a b)
      (_ : Mole.CLParentPattern S U a b), Prop)
    (h : Φ x.U x.a x.b x.block x.cl) : Φ (e ▸ x : ChainAt S F').U (e ▸ x : ChainAt S F').a (e ▸ x : ChainAt S F').b
      (e ▸ x : ChainAt S F').block (e ▸ x : ChainAt S F').cl := by
  subst e
  exact h

/-- One operation (twist or not) transports the assembly (along `chosenBranchEquiv`). -/
theorem step_asm (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) (i : ι) (ε : Bool) {n : ℕ}
    (B0 : CLChainAssembly A.skeleton (clRegionData A.skeleton c.block c.cl) n) :
    ∃ (B1 : CLChainAssembly (chosenSkeleton A.skeleton (A.family.placement i) ε)
        (clRegionData _ (ChainAt.nextA A c i ε).block (ChainAt.nextA A c i ε).cl) n),
      AsmCorr B0 B1 (chosenBranchEquiv A.skeleton (A.family.placement i) ε) ∧
        chosenBranchEquiv A.skeleton (A.family.placement i) ε c.a = (ChainAt.nextA A c i ε).a ∧
        chosenBranchEquiv A.skeleton (A.family.placement i) ε c.b = (ChainAt.nextA A c i ε).b ∧
        ∀ x, x ∈ (ChainAt.nextA A c i ε).U ↔
          (chosenBranchEquiv A.skeleton (A.family.placement i) ε).symm x ∈ c.U := by
  unfold ChainAt.nextA
  refine cast_motive (nextFamily_eq A i ε).symm (c.next i ε)
    (fun U a b block cl => ∃
      (B1 : CLChainAssembly (chosenSkeleton A.skeleton (A.family.placement i) ε) (clRegionData _ block cl) n),
      AsmCorr B0 B1 (chosenBranchEquiv A.skeleton (A.family.placement i) ε) ∧
        chosenBranchEquiv A.skeleton (A.family.placement i) ε c.a = a ∧
        chosenBranchEquiv A.skeleton (A.family.placement i) ε c.b = b ∧
        ∀ x, x ∈ U ↔ (chosenBranchEquiv A.skeleton (A.family.placement i) ε).symm x ∈ c.U) ?_
  cases ε
  · exact ⟨B0, AsmCorr.refl B0, rfl, rfl, fun x => Iff.rfl⟩
  · refine ⟨CLChainAssembly.twist (A.family.placement i) B0
      (c.next i true).U (c.next i true).a (c.next i true).b rfl rfl rfl
      (clRegionData _ (c.next i true).block (c.next i true).cl), AsmCorr.twist _ B0 _ _ _ rfl rfl rfl _, rfl, rfl, ?_⟩
    intro x
    obtain ⟨v, rfl⟩ := (coreBranchEquiv A.skeleton (A.family.placement i)).surjective x
    have e1 : (coreBranchEquiv A.skeleton (A.family.placement i)).symm
        (coreBranchEquiv A.skeleton (A.family.placement i) v) = v := Equiv.symm_apply_apply _ _
    exact (mem_twistedAtoms A.skeleton (A.family.placement i) c.U v).trans
      (Iff.of_eq (congrArg (· ∈ c.U) e1.symm))

/-- **P2.2, assembly along a batch.**  The assembly of the start is carried to the reached state's region; the branch
bijection `e` (composite of the `chosenBranchEquiv`s) carries the pieces, the joints, the region and the atom layers. -/
theorem Reach.exists_asm {p : ℕ} {kind : Bool} {M : List ι} {A B : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} {c' : ChainAt B.skeleton B.family} (h : Reach p kind M A c B c') {n : ℕ}
    (B0 : CLChainAssembly A.skeleton (clRegionData A.skeleton c.block c.cl) n) :
    ∃ (e : GBranch A.skeleton.tree ≃ GBranch B.skeleton.tree)
      (B1 : CLChainAssembly B.skeleton (clRegionData B.skeleton c'.block c'.cl) n),
      AsmCorr B0 B1 e ∧ e c.a = c'.a ∧ e c.b = c'.b ∧ (∀ x, x ∈ c'.U ↔ e.symm x ∈ c.U) ∧
      ∀ x, atomLayer B.data B.plain (stateLayer B) (e x) = atomLayer A.data A.plain (stateLayer A) x := by
  induction h with
  | nil A c => exact ⟨Equiv.refl _, B0, AsmCorr.refl B0, rfl, rfl, fun x => Iff.rfl, fun x => rfl⟩
  | skip i h ih => exact ih B0
  | @apply L A c B c' i op h ih =>
    obtain ⟨B1, hc1, ha1, hb1, hU1⟩ := step_asm A c i op.choice B0
    obtain ⟨e2, B2, hc2, ha2, hb2, hU2, hl2⟩ := ih B1
    refine ⟨(chosenBranchEquiv A.skeleton (A.family.placement i) op.choice).trans e2, B2, hc1.trans hc2, ?_, ?_,
      fun x => ?_, fun x => ?_⟩
    · exact (congrArg e2 ha1).trans ha2
    · exact (congrArg e2 hb1).trans hb2
    · exact (hU2 x).trans (hU1 (e2.symm x))
    · exact (hl2 _).trans (atomLayer_step A i op x)

end WaveTurbulence.VineEstS4
