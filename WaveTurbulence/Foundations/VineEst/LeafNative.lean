/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.FamilyBatch
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeLeafEquiv
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeCoupleLayering

/-! # Address, sign and pairing of native replacement leaves (LFTWIST-LEAFMAP, step 1)

Generic facts about `nativeLeafAt` of a reconstruction `D` of a plain skeleton `S`:
the global address, the sign and the partner of the leaf of a native regular couple or paired tree. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LFTwist
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree Links
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

theorem coupleLeaf_addr (p : SourcePair S) (ℓ : NativeLeaf D (.inl p)) :
    (nativeLeafAt D hS (.inl p) ℓ).1 = addrExt (coupleRoot D hS p ℓ.1.1) ℓ.1.2 := by
  obtain ⟨⟨i, r⟩, h⟩ := ℓ
  fin_cases i <;> rfl

theorem chainLeaf_addr (b : GBranch S.tree) (ℓ : NativeLeaf D (.inr b)) :
    (nativeLeafAt D hS (.inr b) ℓ).1 = addrExt (inflatedPosition S D.tree b.toNode) ℓ.1.1.2 := rfl

theorem pair_val_congr {n : ℕ} {G H : Garden n} (h : G = H) (ℓ : GLeaf G.tree) (ℓ' : GLeaf H.tree)
    (e : ℓ.1 = ℓ'.1) : (G.pair ℓ).1 = (H.pair ℓ').1 := by
  subst h
  rw [Subtype.ext e]

/-- The partner of a native couple leaf is the partner in the decoded couple. -/
theorem coupleLeaf_pair (p : SourcePair S) (ℓ : NativeLeaf D (.inl p)) :
    (D.garden hS).pair (nativeLeafAt D hS (.inl p) ℓ) =
      nativeLeafAt D hS (.inl p) ((decodedCouple (D.couple p)).pair ℓ) := by
  have h1 := Comb.RootedSubforest.inducedGarden_pair (G := D.garden hS) (nativeCoupleForest D hS p)
    (nativeCoupleForest_closed D hS p) ℓ
  have h2 := pair_val_congr (nativeCoupleGarden_eq D hS p) ℓ ℓ rfl
  have h3 : ∀ a b : GLeaf (nativeCoupleForest D hS p).shape, a.1 = b.1 →
      (nativeCoupleForest D hS p).leafEmbedding a = (nativeCoupleForest D hS p).leafEmbedding b :=
    fun a b e => by rw [Subtype.ext e]
  have h4 := h3 _ _ h2
  exact h1.symm.trans h4


private theorem pair_eq_of_source_first' {n : ℕ} (G : Garden n) (q : Pair n)
    (hq : q ∈ sourcePairs G) (l : GLeaf G.tree) (hl : l.1 = q.1) : (G.pair l).1 = q.2 := by
  obtain ⟨m, hm, he⟩ := Finset.mem_image.mp hq
  have hml : m = l := Subtype.ext ((congrArg Prod.fst he).trans hl.symm)
  subst m
  exact congrArg Prod.snd he

/-- The partner of a native paired-tree leaf is the partner in the decoded paired tree. -/
theorem chainLeaf_pair (b : GBranch S.tree) (ℓ : NativeLeaf D (.inr b)) :
    ∃ ℓ2 : NativeLeaf D (.inr b), ℓ2.1 = (decodedTree (D.tree b) (nodeSign S.sig b.1)).pair ℓ.1 ∧
      (D.garden hS).pair (nativeLeafAt D hS (.inr b) ℓ) = nativeLeafAt D hS (.inr b) ℓ2 := by
  classical
  have hd := decodedTree_decodes (D.tree b) (nodeSign S.sig b.1)
  have hl : ℓ.1.1.2 ≠ (D.tree b).lonePath := ℓ.2
  have hne2 : ((decodedTree (D.tree b) (nodeSign S.sig b.1)).pair ℓ.1).1.2 ≠ (D.tree b).lonePath := by
    intro h2
    have hm2 : (decodedTree (D.tree b) (nodeSign S.sig b.1)).mark
        ((decodedTree (D.tree b) (nodeSign S.sig b.1)).pair ℓ.1) ≠ none := by
      rw [hd.2.1]; simp [h2]
    have h3 := ((decodedTree (D.tree b) (nodeSign S.sig b.1)).pair_eq_iff _).mpr hm2
    rw [Garden.pair_pair] at h3
    have hm1 := ((decodedTree (D.tree b) (nodeSign S.sig b.1)).pair_eq_iff ℓ.1).mp h3.symm
    rw [hd.2.1] at hm1
    simp [hl] at hm1
  refine ⟨⟨_, hne2⟩, rfl, ?_⟩
  have hp := hd.2.2 ℓ.1 hl
  let a := inflatedPosition S D.tree b.toNode
  let f : (Fin 1 × Path) → (Fin w × Path) := fun z => addrExt a z.2
  have hf : RespectsAt f (0, []) := by
    intro q
    simp only [f, addrExt, List.nil_append, List.append_nil]
  have hm := chain_pairsAt_map_local (D.tree b) f (0, []) hf (nodeSign S.sig b.1)
  have he : f (0, []) = a := by simp only [f, addrExt, List.append_nil]
  rw [he] at hm
  have hmem : ∀ x y : Fin 1 × Path, (x, y) ∈ (D.tree b).pairsAt (nodeSign S.sig b.1) ((0 : Fin 1), []) →
      (addrExt a x.2, addrExt a y.2) ∈ sourcePairs (D.garden hS) := by
    intro x y hxy
    have hq : (f x, f y) ∈ (D.tree b).pairsAt (nodeSign S.sig b.1) a := by
      rw [hm]; exact List.mem_map.mpr ⟨(x, y), hxy, rfl⟩
    exact D.chain_pair_mem hS (D.garden_decodes hS) b _ hq
  apply Subtype.ext
  rcases (mem_symmPairs_iff _ _).mp hp with hp | hp
  · exact pair_eq_of_source_first' (D.garden hS) _ (hmem _ _ hp) _ rfl
  · have h5 := pair_eq_of_source_first' (D.garden hS) _ (hmem _ _ hp)
      (nativeLeafAt D hS (.inr b) ⟨_, hne2⟩) rfl
    have h6 : (D.garden hS).pair (nativeLeafAt D hS (.inr b) ⟨_, hne2⟩) = nativeLeafAt D hS (.inr b) ℓ :=
      Subtype.ext h5
    have h7 := congrArg (D.garden hS).pair h6
    have h8 := (D.garden hS).pair_pair (nativeLeafAt D hS (.inr b) ⟨_, hne2⟩)
    exact congrArg Subtype.val (h7.symm.trans h8)


theorem coupleRoot_sign (p : SourcePair S) (i : Fin 2) :
    nodeSign S.sig (coupleRoot D hS p i) = if i = 0 then 1 else -1 := by
  have hv := ((rawOfGarden_valid S hS).1 p.1 p.2)
  unfold coupleRoot
  split_ifs with h
  · rw [inflatedPosition_sign]; exact hv.2.2.1
  · rw [inflatedPosition_sign]; exact hv.2.2.2

theorem coupleLeaf_sign (p : SourcePair S) (ℓ : NativeLeaf D (.inl p)) :
    nodeSign S.sig (nativeLeafAt D hS (.inl p) ℓ).1 =
      pathSign (if ℓ.1.1 = 0 then 1 else -1) ℓ.1.2 := by
  rw [coupleLeaf_addr, nodeSign_addrExt, coupleRoot_sign]

theorem chainLeaf_sign (b : GBranch S.tree) (ℓ : NativeLeaf D (.inr b)) :
    nodeSign S.sig (nativeLeafAt D hS (.inr b) ℓ).1 = pathSign (nodeSign S.sig b.1) ℓ.1.1.2 := by
  rw [chainLeaf_addr, nodeSign_addrExt, inflatedPosition_sign]
  rfl

end WaveTurbulence.LFTwist
