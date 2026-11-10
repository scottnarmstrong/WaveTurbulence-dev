/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.TreeFam
public import WaveTurbulence.Foundations.IncohInst.InputProductIdentity
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceChainProducts
public import WaveTurbulence.Foundations.RegStruct.DecodedTree
public import WaveTurbulence.Foundations.IncohInst.Links.TreeLinks
public import WaveTurbulence.Foundations.IncohInst.Links.Coherence

/-! # The original tree input product is exactly its structural chain leaf-pair product -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Reg TTree Incoh IncohInst

theorem tree_pair_source_signs {G : Garden 1} (X : RegChain)
    (p : (Fin 1 × Path) × (Fin 1 × Path)) (hp : p ∈ X.pairsAt (G.sig 0) ((0:Fin 1),[])) :
    nodeSign G.sig p.1 = 1 ∧ nodeSign G.sig p.2 = -1 := by
  have hσ : G.sig = fun _ : Fin 1 => G.sig 0 := by
    funext i
    exact congrArg G.sig (Subsingleton.elim _ _)
  rw [hσ]
  exact decodedTree_pair_signs X (G.sig 0) p hp

/-- The first endpoint of the literal original tree pair is its paired positive leaf. -/
def treePositivePairLeaf {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (i : Fin (X.pairsAt (G.sig 0) ((0:Fin 1),[])).length) : TPlus G := by
  let p := (X.pairsAt (G.sig 0) ((0:Fin 1),[])).get i
  have hp := List.get_mem (X.pairsAt (G.sig 0) ((0:Fin 1),[])) i
  have hex := tree_pair_of_decoded hX hp
  let ℓ := hex.choose
  have hℓ := hex.choose_spec.1
  have hpair := hex.choose_spec.2
  have hv : p.1.2 ∈ (G.tree p.1.1).leaves := by rw [← hℓ]; exact ℓ.property
  let a : GLeaf G.tree := ⟨p.1,hv⟩
  have ha : a = ℓ := Subtype.ext hℓ.symm
  have hpairval : (G.pair a).val = p.2 := by rw [ha]; exact hpair
  have hs := tree_pair_source_signs X p hp
  refine ⟨a,hs.1,?_⟩
  intro he
  have hsame : p.2 = p.1 := hpairval.symm.trans (congrArg Subtype.val he)
  have hbad : (1:ℤˣ) = -1 := hs.1.symm.trans ((congrArg (nodeSign G.sig) hsame).symm.trans hs.2)
  exact (by decide : (1:ℤˣ) ≠ -1) hbad

theorem treePositivePairLeaf_fst {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (i : Fin (X.pairsAt (G.sig 0) ((0:Fin 1),[])).length) :
    (treePositivePairLeaf hX i).val.val = ((X.pairsAt (G.sig 0) ((0:Fin 1),[])).get i).1 := rfl

theorem treePositivePairLeaf_injective {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) :
    Function.Injective (treePositivePairLeaf hX) := by
  intro i j hij
  have hf := congrArg (fun a : TPlus G => a.val.val) hij
  simp only [treePositivePairLeaf_fst] at hf
  have hnd := (chain_pairs_flat_nodup X (G.sig 0) ((0:Fin 1),[])).1
  have hp := eq_of_flat_nodup hnd (List.get_mem _ i) (List.get_mem _ j) (Or.inl rfl) (Or.inl hf)
  exact (nodup_of_flat_nodup hnd).get_inj_iff.mp hp

theorem treePositivePairLeaf_surjective {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) :
    Function.Surjective (treePositivePairLeaf hX) := by
  intro ℓ
  have hn : ℓ.val.val.2 ≠ X.lonePath := fun he =>
    ℓ.property.2 ((tree_pair_eq_iff hX ℓ.val).mpr he)
  have hp := (mem_symmPairs_iff (X.pairsAt (G.sig 0) ((0:Fin 1),[]))
    (ℓ.val.val,(G.pair ℓ.val).val)).mp (hX.2.2 ℓ.val hn)
  rcases hp with hp | hp
  · obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
    refine ⟨i,Subtype.ext (Subtype.ext ?_)⟩
    exact (treePositivePairLeaf_fst hX i).trans (congrArg Prod.fst hi)
  · have hs := (tree_pair_source_signs X _ hp).2
    have hbad : (1:ℤˣ) = -1 := ℓ.property.1.symm.trans hs
    exact False.elim ((by decide : (1:ℤˣ) ≠ -1) hbad)

/-- The actual oriented tree pair list is precisely the original input-leaf enumeration. -/
def treePositivePairLeafEquiv {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) :
    Fin (X.pairsAt (G.sig 0) ((0:Fin 1),[])).length ≃ TPlus G :=
  Equiv.ofBijective (treePositivePairLeaf hX)
    ⟨treePositivePairLeaf_injective hX,treePositivePairLeaf_surjective hX⟩

/-- The source paired-positive-leaf product is the literal structural chain pair product. -/
theorem tree_prod_TPlus_eq_pair_list {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    {M : Type*} [CommMonoid M] (f : Fin 1 × Path → M) :
    (∏ ℓ : TPlus G, f ℓ.val.val) = ((X.pairsAt (G.sig 0) ((0:Fin 1),[])).map (fun p => f p.1)).prod := by
  calc
    _ = ∏ i : Fin (X.pairsAt (G.sig 0) ((0:Fin 1),[])).length,
        f ((X.pairsAt (G.sig 0) ((0:Fin 1),[])).get i).1 :=
      ((treePositivePairLeafEquiv hX).prod_comp (fun ℓ : TPlus G => f ℓ.val.val)).symm
    _ = (List.ofFn (fun i : Fin (X.pairsAt (G.sig 0) ((0:Fin 1),[])).length =>
        f ((X.pairsAt (G.sig 0) ((0:Fin 1),[])).get i).1)).prod := (Fin.prod_ofFn _).symm
    _ = _ := by rw [List.ofFn_comp' (X.pairsAt (G.sig 0) ((0:Fin 1),[])).get (fun p => f p.1),List.ofFn_get]

/-- Actual input momentum rows give the original chain leaf product at its source root,
with its original tree parameter extension and the excluded constant continuation. -/
theorem tree_prod_source_input_eq_chainLeafProduct {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (F : Fin 1 × Path → Mom d → ℂ) (k : Mom d)
    (x : Fin (X.treeLinks (G.sig 0)).length → Fin 2 → Mom d) :
    (∏ a, F ((treeInputEquiv G).symm a).val.val ((treeCarrier hX).inputMomentum k x a)) =
      chainLeafProduct F (treeParamFun X (G.sig 0) (fun j => (x j 0,x j 1))) X (G.sig 0) ((0:Fin 1),[]) k (fun _ => k) := by
  simp_rw [tree_inputMomentum_eq]
  change (∏ a, F ((treeInputEquiv G).symm a).val.val (chainVal (treeParamFun X (G.sig 0) (fun j => (x j 0,x j 1)))
    X (G.sig 0) ((0:Fin 1),[]) k (fun _ => k) ((treeInputEquiv G).symm a).val.val)) = _
  have hp := tree_prod_TPlus_eq_pair_list hX (fun z =>
    F z (chainVal (treeParamFun X (G.sig 0) (fun j => (x j 0,x j 1))) X (G.sig 0) ((0:Fin 1),[]) k (fun _ => k) z))
  have he := (treeInputEquiv G).symm.prod_comp (fun ℓ : TPlus G =>
    F ℓ.val.val (chainVal (treeParamFun X (G.sig 0) (fun j => (x j 0,x j 1))) X (G.sig 0) ((0:Fin 1),[]) k (fun _ => k) ℓ.val.val))
  exact he.trans hp

end WaveTurbulence.RA1Leafwise
