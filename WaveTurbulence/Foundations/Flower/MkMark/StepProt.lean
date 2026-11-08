/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.PairNat

/-! # B2b MK-MARK: one-step transport of `Π₀` along skeleton coordinate data

`step_prot`: for coordinate data `C` with slot data `E` between decoded gardens, if the replaced skeleton nodes
contain no root and their leaves are paired inside one tree (on both sides), and `Π₀(LG)` avoids the replaced
region, then `Π₀(LG')` avoids the image region and the coordinate map matches `Π₀(LG)` with `Π₀(LG')` off the
regions. (`prot_transport` applied to `C.toOutIso` and `C.symm.toOutIso`.) -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

/-- The region owned by replaced nodes is good when they contain no root and their leaves pair in one tree. -/
theorem regionOK_ownedBy {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {LG : LayeredGarden w}
    (hd : D.Decodes hS LG.garden) (Rsk : Set (GNode S.tree)) (hroot : ∀ o ∈ Rsk, o.1.2 ≠ [])
    (hpairR : ∀ l : GLeaf S.tree, l.toNode ∈ Rsk → (S.pair l).1.1 = l.1.1) :
    RegionOK LG (ownedBy S D.tree Rsk) where
  root z hz _ h0 := by
    apply hroot _ hz
    have hb := (mem_ownRegion_owner S D.tree z).1.2
    rw [h0] at hb
    exact (inflatedPosition_nil_iff S D.tree _).mp (List.prefix_nil.mp hb)
  pair z h hz := by
    have hz' : owner S D.tree z ∈ Rsk := hz
    rcases owner_pair hd (⟨z, h⟩ : GLeaf LG.garden.tree) with he | ⟨l, hl1, hl2⟩
    · rw [← owner_fst S D.tree (LG.garden.pair ⟨z, h⟩).1, ← he, owner_fst]
    · rw [← owner_fst S D.tree (LG.garden.pair ⟨z, h⟩).1, ← hl2]
      show (S.pair l).1.1 = z.1
      rw [hpairR l (by rw [hl1]; exact hz'), ← owner_fst S D.tree z, ← hl1]
      rfl

namespace CoordData
variable {S S' : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {D' : ReconstructionData S'}
  {hS' : S'.IsPlain} (C : CoordData D hS D' hS') (E : PairData C)
  {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden) (hd' : D'.Decodes hS' LG'.garden)

include E hd hd' in
/-- **One-step transport of `Π₀`.** -/
theorem step_prot {J : Finset (Fin w)} {pat : Fin w → FixPat}
    (hroot : ∀ o ∈ C.Rsk, o.1.2 ≠ []) (hpairR : ∀ l : GLeaf S.tree, l.toNode ∈ C.Rsk → (S.pair l).1.1 = l.1.1)
    (hroot' : ∀ o ∈ C.Rsk', o.1.2 ≠ [])
    (hpairR' : ∀ l : GLeaf S'.tree, l.toNode ∈ C.Rsk' → (S'.pair l).1.1 = l.1.1)
    (hp : NoProtIn LG J pat (ownedBy S D.tree C.Rsk)) :
    NoProtIn LG' J pat (ownedBy S' D'.tree C.Rsk') ∧
      ∀ z, NodeAt LG z → z ∉ ownedBy S D.tree C.Rsk → (ProtAt LG' J pat (C.map z) ↔ ProtAt LG J pat z) := by
  let I := C.toOutIso hd hd' (E.pairTree hd hd')
  let I' := C.symm.toOutIso hd' hd (E.symm.pairTree hd' hd)
  have hinv : ∀ z', NodeAt LG' z' → z' ∉ ownedBy S' D'.tree C.Rsk' → I.f (I'.f z') = z' :=
    fun z' hz' hR' => C.symm.symm_map_map hd' hd z' hz' hR'
  have hinv' : ∀ z, NodeAt LG z → z ∉ ownedBy S D.tree C.Rsk → I'.f (I.f z) = z :=
    fun z hz hR => C.symm_map_map hd hd' z hz hR
  exact prot_transport I I' hinv hinv' (regionOK_ownedBy hd C.Rsk hroot hpairR)
    (regionOK_ownedBy hd' C.Rsk' hroot' hpairR') hp

end CoordData

end WaveTurbulence.Flower.MkMark
