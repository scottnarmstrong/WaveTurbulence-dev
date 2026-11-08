/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.StepSel

/-! # B2b-2 MK-MARK: one LF step transports the fine marking `markI`

`markedBranch_transport_gen` is `CoordData.markedBranch_transport` for an abstract protected predicate.
`noProtSel_of_near`: no vertex of `Π` near the lower joint ⇒ `Π` avoids the replaced region.
**`mark_stepI`**: one LF step (either choice) at a member that is unmarked for `Π`, with the capped stems avoiding the
replaced region, transports the fine marked set `markedVinesRaw … Π`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

namespace CoordData
variable {S S' : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {D' : ReconstructionData S'}
  {hS' : S'.IsPlain} (C : CoordData D hS D' hS')
  {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden) (hd' : D'.Decodes hS' LG'.garden)

include hd hd' in
/-- **Marked branches are transported**, for an abstract protected predicate. -/
theorem markedBranch_transport_gen {Pi : Finset (GNode LG.garden.tree)} {Pi' : Finset (GNode LG'.garden.tree)}
    {PA PA' : Address w → Prop} (hPi : ∀ a, a ∈ Pi ↔ PA a.1) (hPi' : ∀ a, a ∈ Pi' ↔ PA' a.1)
    (νB : GBranch S.tree → GBranch S'.tree)
    (hnear : ∀ o, o ∉ C.Rsk → ∀ b, NearRel S o b ↔ NearRel S' (C.ν o) (νB b))
    (hp : ∀ z ∈ ownedBy S D.tree C.Rsk, ¬ PA z) (hp' : ∀ z' ∈ ownedBy S' D'.tree C.Rsk', ¬ PA' z')
    (hiff : ∀ z, NodeAt LG z → z ∉ ownedBy S D.tree C.Rsk → (PA' (C.map z) ↔ PA z)) (b : GBranch S.tree) :
    MarkedBranch S D.tree Pi b ↔ MarkedBranch S' D'.tree Pi' (νB b) := by
  constructor
  · rintro ⟨a, ha, hab⟩
    have hpa := (hPi a).mp ha
    have hR : a.1 ∉ ownedBy S D.tree C.Rsk := fun h => hp _ h hpa
    have hn := C.map_node hd hd' a.1 a.2 hR
    have hpa' := (hiff a.1 a.2 hR).mpr hpa
    refine ⟨⟨C.map a.1, hn.1⟩, (hPi' _).mpr hpa', ?_⟩
    rw [mem_nearRegion_iff'] at hab ⊢
    rw [hn.2]
    exact (hnear _ hR b).mp hab
  · rintro ⟨a', ha', hab'⟩
    have hpa' := (hPi' a').mp ha'
    have hR' : a'.1 ∉ ownedBy S' D'.tree C.Rsk' := fun h => hp' _ h hpa'
    have hn := C.symm.map_node hd' hd a'.1 a'.2 hR'
    have hR : C.symm.map a'.1 ∉ ownedBy S D.tree C.Rsk := C.symm.map_owner_not hd' hd a'.1 a'.2 hR'
    have hinv : C.map (C.symm.map a'.1) = a'.1 := C.symm.symm_map_map hd' hd a'.1 a'.2 hR'
    have hpa : PA (C.symm.map a'.1) := (hiff _ hn.1 hR).mp (by rw [hinv]; exact hpa')
    refine ⟨⟨C.symm.map a'.1, hn.1⟩, (hPi _).mpr hpa, ?_⟩
    rw [mem_nearRegion_iff'] at hab' ⊢
    have ho : owner S D.tree (C.symm.map a'.1) ∉ C.Rsk := hR
    apply (hnear _ ho b).mpr
    have e : C.ν (owner S D.tree (C.symm.map a'.1)) = owner S' D'.tree a'.1 := by
      rw [hn.2]
      exact Equiv.apply_symm_apply _ _
    rw [e]
    exact hab'

end CoordData

/-- No vertex of `Π` in the near region of the lower joint ⇒ `Π` avoids the replaced region. -/
theorem noProtSel_of_near {S : Garden w} (P : CorePlacement S) (D : ReconstructionData S) {LG : LayeredGarden w}
    {J : Finset (Fin w)} {pat : Fin w → FixPat} (t s : ℝ) (kSel : Fin w → Option ℕ)
    (hn : ∀ a ∈ protI LG J pat t s kSel, a.1 ∉ nearRegion S D.tree P.lower) :
    ∀ z ∈ ownedBy S D.tree (replacedNodes P), ¬ ProtG LG (SeedSel LG J pat kSel) z := by
  intro z hz hp
  have hz' : owner S D.tree z ∈ replacedNodes P := hz
  have hmem : (⟨z, hp.1⟩ : GNode LG.garden.tree) ∈ protI LG J pat t s kSel :=
    (mem_protI_iff pat t s kSel _).mpr hp
  apply hn _ hmem
  rw [mem_nearRegion_iff]
  rw [mem_replacedNodes] at hz'
  rcases hz' with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨P.keep, h.trans P.child⟩)
  · refine Or.inr (Or.inr ⟨P.retained, ⟨retained_tree P, P.keep, ?_⟩, h⟩)
    have := congrArg (fun x : GNode S.tree => x.1.2) P.child
    exact this

section Step
variable {S : Garden w} (hS : S.IsPlain) (Z : TwistGroupSite S) (D : ReconstructionData S)
  (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)

/-- Marked branches for `Π` correspond along one LF step, for any branch map compatible with the near relation. -/
theorem markedBranchI (ε : Bool) {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden)
    (hd' : (lfReconstructionChoice S Z.P hS D ε X Q hX hQ).Decodes (chosenSkeleton_plain S Z.P hS ε) LG'.garden)
    {J : Finset (Fin w)} {pat : Fin w → FixPat} (t s : ℝ) (kSel : Fin w → Option ℕ)
    (hn : ∀ a ∈ protI LG J pat t s kSel, a.1 ∉ nearRegion S D.tree Z.P.lower)
    (hs : StemAvoid LG J (ownedBy S D.tree (replacedNodes Z.P)))
    (νB : GBranch S.tree → GBranch (chosenSkeleton S Z.P ε).tree)
    (hnear : ∀ o, o ∉ replacedNodes Z.P → ∀ b, NearRel S o b ↔ NearRel (chosenSkeleton S Z.P ε)
      ((lfCoord hS Z.P D X Q hX hQ (pair_retained_tree' Z.P Z.hB Z.hCL Z.hP) ε).ν o) (νB b))
    (b : GBranch S.tree) :
    MarkedBranch S D.tree (protI LG J pat t s kSel) b ↔
      MarkedBranch (chosenSkeleton S Z.P ε) (lfReconstructionChoice S Z.P hS D ε X Q hX hQ).tree
        (protI LG' J pat t s kSel) (νB b) := by
  have hsame := pair_retained_tree' Z.P Z.hB Z.hCL Z.hP
  set C := lfCoord hS Z.P D X Q hX hQ hsame ε
  have hp1 : ∀ z ∈ ownedBy S D.tree C.Rsk, ¬ ProtG LG (SeedSel LG J pat kSel) z := by
    rw [lfCoord_rsk]
    exact noProtSel_of_near Z.P D t s kSel hn
  have hs1 : StemAvoid LG J (ownedBy S D.tree C.Rsk) := by
    rw [lfCoord_rsk]
    exact hs
  obtain ⟨hp', hiff⟩ := C.step_protSel (lfPair hS Z.P D X Q hX hQ hsame ε) hd hd' kSel
    (lfCoord_root hS Z.P D X Q hX hQ hsame ε) (lfCoord_pairR hS Z.P D X Q hX hQ hsame ε)
    (lfCoord_root' hS Z.P D X Q hX hQ hsame ε) (lfCoord_pairR' hS Z.P D X Q hX hQ hsame ε) hp1 hs1
  exact C.markedBranch_transport_gen hd hd' (mem_protI_iff pat t s kSel) (mem_protI_iff pat t s kSel) νB
    (fun o ho => hnear o (by rw [lfCoord_rsk] at ho; exact ho)) hp1 hp' hiff b

/-- **One LF step transports the fine marking** (either choice), at a member unmarked for `Π` whose replaced region
the capped stems avoid. -/
theorem mark_stepI (ε : Bool) {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden)
    (hd' : (lfReconstructionChoice S Z.P hS D ε X Q hX hQ).Decodes (chosenSkeleton_plain S Z.P hS ε) LG'.garden)
    {J : Finset (Fin w)} {pat : Fin w → FixPat} (t s : ℝ) (kSel : Fin w → Option ℕ)
    (hn : ∀ a ∈ protI LG J pat t s kSel, a.1 ∉ nearRegion S D.tree Z.P.lower)
    (hs : StemAvoid LG J (ownedBy S D.tree (replacedNodes Z.P))) :
    MarkTransported (VineA.chosenMolIso S Z.P ε) (markedVinesRaw S D.tree (protI LG J pat t s kSel))
      (markedVinesRaw (chosenSkeleton S Z.P ε) (lfReconstructionChoice S Z.P hS D ε X Q hX hQ).tree
        (protI LG' J pat t s kSel)) := by
  have hsame := pair_retained_tree' Z.P Z.hB Z.hCL Z.hP
  cases ε with
  | false =>
    have hMB := markedBranchI hS Z D X Q hX hQ false hd hd' t s kSel hn hs id (fun o _ b => Iff.rfl)
    intro c c' hc'
    have hcc : c' = c := by
      apply VineA.clVine_eq_of_atoms
      rw [hc']
      exact Finset.image_id
    subst hcc
    exact ⟨fun ⟨hv, b, hb, hbu, hm⟩ => ⟨hv, b, hb, hbu, (hMB b).mp hm⟩,
      fun ⟨hv, b, hb, hbu, hm⟩ => ⟨hv, b, hb, hbu, (hMB b).mpr hm⟩⟩
  | true =>
    have hMB := markedBranchI hS Z D X Q hX hQ true hd hd' t s kSel hn hs (coreBranchEquiv S Z.P)
      (fun o ho b => twist_nearRel hS Z.P D X Q hX hQ hsame o ho b)
    intro c c' hc'
    rw [mem_markedVinesRaw, mem_markedVinesRaw]
    constructor
    · rintro ⟨hv, b, hb, hbu, hm⟩
      obtain ⟨c'', hc''V, hc''a, hc''u, -⟩ := Z.vinesV_image hv
      have e : c'' = c' := VineA.clVine_eq_of_atoms (hc''a.trans hc'.symm)
      subst e
      refine ⟨hc''V, coreBranchEquiv S Z.P b, ?_, ?_, (hMB b).mp hm⟩
      · rw [hc''a]
        exact (VineA.chosenMolIso S Z.P true).mem_img _ b |>.mpr hb
      · rw [hc''u]
        exact fun h => hbu ((coreBranchEquiv S Z.P).injective h)
    · rintro ⟨hv', b', hb', hbu', hm'⟩
      obtain ⟨c₀, hc₀V, hc₀a, hc₀u, -⟩ := Z.vinesV_preimage hv'
      have hae : c₀.atoms = c.atoms := (VineA.chosenMolIso S Z.P true).img_injective (hc₀a.trans hc')
      have e : c₀ = c := VineA.clVine_eq_of_atoms hae
      subst e
      set b := (coreBranchEquiv S Z.P).symm b'
      have hbb : coreBranchEquiv S Z.P b = b' := Equiv.apply_symm_apply _ _
      refine ⟨hc₀V, b, ?_, ?_, ?_⟩
      · apply ((VineA.chosenMolIso S Z.P true).mem_img c₀.atoms b).mp
        have h1 : (VineA.chosenMolIso S Z.P true).img c₀.atoms = c'.atoms := hc₀a
        have h2 : (VineA.chosenMolIso S Z.P true).e b = b' := hbb
        rw [h1, h2]
        exact hb'
      · intro h
        apply hbu'
        rw [← hbb, h, hc₀u]
      · rw [hMB b, hbb]
        exact hm'

end Step

end WaveTurbulence.Flower.MkMark
