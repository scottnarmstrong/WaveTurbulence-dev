/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceType2Products
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceMomentumBridge
public import WaveTurbulence.Foundations.RegStruct.DecodedPairProperties
public import WaveTurbulence.Foundations.RegStruct.PairRelations

/-! # The literal code pair list enumerates all actual positive source leaves -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Reg TTree

/-- The first endpoint of an original code pair is an actual positive source leaf. -/
def positivePairLeaf {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    (i : Fin Q.raw.2.length) : PlusLeaf G := by
  have hp := List.get_mem Q.raw.2 i
  have hv := (decodedCouple_pairs_valid Q _ hp).1
  rw [← tree_eq_coupleForest hQ] at hv
  refine ⟨⟨(Q.raw.2.get i).1,hv⟩,?_⟩
  change nodeSign G.sig (Q.raw.2.get i).1 = 1
  rw [hQ.1.2]
  exact (decodedCouple_pair_signs Q _ hp).1

theorem positivePairLeaf_injective {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) :
    Function.Injective (positivePairLeaf hQ) := by
  intro i j hij
  have hfirst : (Q.raw.2.get i).1 = (Q.raw.2.get j).1 :=
    congrArg (fun ℓ : PlusLeaf G => ℓ.val.val) hij
  have hi : ((Q.raw.2.get i).1,(Q.raw.2.get i).2) ∈ symmPairs Q.raw.2 :=
    List.mem_append_left _ (List.get_mem _ i)
  have hj : ((Q.raw.2.get i).1,(Q.raw.2.get j).2) ∈ symmPairs Q.raw.2 := by
    rw [hfirst]
    exact List.mem_append_left _ (List.get_mem _ j)
  exact (decodedPair_nodup Q).injective_get (Prod.ext hfirst (decodedPair_functional Q hi hj))

theorem positivePairLeaf_surjective {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) :
    Function.Surjective (positivePairLeaf hQ) := by
  intro ℓ
  have hp := (mem_symmPairs_iff Q.raw.2 (ℓ.val.val,(G.pair ℓ.val).val)).mp (hQ.2.2.2 ℓ.val)
  rcases hp with hp | hp
  · obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
    refine ⟨i,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Prod.fst hi
  · have hs := (decodedCouple_pair_signs Q _ hp).2
    have hsign : G.sign ℓ.val.toNode = -1 := by
      change nodeSign G.sig ℓ.val.val = -1
      rw [hQ.1.2]
      exact hs
    have hbad : (1:ℤˣ) = -1 := ℓ.property.symm.trans hsign
    exact False.elim ((by decide : (1:ℤˣ) ≠ -1) hbad)

/-- This enumeration reads the actual oriented pair list, rather than an
arbitrary equivalent list or a changed leaf ordering. -/
def positivePairLeafEquiv {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) :
    Fin Q.raw.2.length ≃ PlusLeaf G :=
  Equiv.ofBijective (positivePairLeaf hQ)
    ⟨positivePairLeaf_injective hQ,positivePairLeaf_surjective hQ⟩

/-- The original positive-leaf product equals the literal code pair product. -/
theorem prod_plusLeaf_eq_pair_list {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    {M : Type*} [CommMonoid M] (f : Fin 2 × Path → M) :
    (∏ ℓ : PlusLeaf G, f ℓ.val.val) = (Q.raw.2.map (fun p => f p.1)).prod := by
  calc
    _ = ∏ i : Fin Q.raw.2.length, f (Q.raw.2.get i).1 :=
      ((positivePairLeafEquiv hQ).prod_comp (fun ℓ : PlusLeaf G => f ℓ.val.val)).symm
    _ = (List.ofFn (fun i : Fin Q.raw.2.length => f (Q.raw.2.get i).1)).prod := (Fin.prod_ofFn _).symm
    _ = _ := by rw [List.ofFn_comp' (Q.raw.2.get) (fun p => f p.1),List.ofFn_get]

/-- Actual source input coordinates give precisely the code leaf kernel,
so its structural factorizations apply to the original source amplitude. -/
theorem prod_source_input_eq_cplLeafProduct {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {V : Type} [AddCommGroup V]
    (F : Fin 2 × Path → V → ℂ) (r : V) (x : Fin Q.links.length → Fin 2 → V) :
    (∏ a, F (plusLeafEquiv hQ hG a).val.1 ((coupleMomentumData hQ hG).inputMomentum r x a)) =
      cplLeafProduct F (paramFun Q (fun j => (x j 0,x j 1))) Q (0,[]) (1,[]) r := by
  simp_rw [coupleMomentumData_inputMomentum]
  change (∏ a, F (plusLeafEquiv hQ hG a).val.1 (cplVal (paramFun Q (fun j => (x j 0,x j 1))) Q (0,[]) (1,[]) r
    (plusLeafEquiv hQ hG a).val.val)) = _
  have hp := prod_plusLeaf_eq_pair_list hQ (fun z =>
    F z (cplVal (paramFun Q (fun j => (x j 0,x j 1))) Q (0,[]) (1,[]) r z))
  have he := (plusLeafEquiv hQ hG).prod_comp (fun ℓ : PlusLeaf G =>
    F ℓ.val.1 (cplVal (paramFun Q (fun j => (x j 0,x j 1))) Q (0,[]) (1,[]) r ℓ.val.val))
  exact he.trans hp

end WaveTurbulence.RA1Leafwise
