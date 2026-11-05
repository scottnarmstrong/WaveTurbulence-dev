/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeCoefficientEnumeration
public import WaveTurbulence.Foundations.RegAsymp.SpecialSign

/-! # Exact transport of original tree special sets to the coefficient sign root -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Reg MainCoef Finset

/-- Place an original one-tree address at its ClassJR root of the same sign. -/
def treeCoefficientAddress (ζ : ℤˣ) (a : Fin 1 × TTree.Path) : ClassJR.Addr :=
  ((rootT ζ).1,a.2)

theorem treeCoefficientAddress_injective (ζ : ℤˣ) : Function.Injective (treeCoefficientAddress ζ) := by
  intro a b h
  exact Prod.ext (Subsingleton.elim _ _) (congrArg (fun z : ClassJR.Addr => z.2) h)

theorem treeCoefficientAddress_addrExt (ζ : ℤˣ) (a : Fin 1 × TTree.Path) (p : TTree.Path) :
    treeCoefficientAddress ζ (addrExt a p)=addrExt (treeCoefficientAddress ζ a) p := rfl

/-- The literal ClassJR coefficient addresses are the images of the original chosen nodes. -/
theorem tree_chosenSet_coefficient_image (X : RegChain) (ζ : ℤˣ) :
    ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)) =
      (WaveTurbulence.chosenSet (X.treeLinks ζ)).image (treeCoefficientAddress ζ) := by
  rw [linksAt_rootT]
  unfold ClassJR.chosenSet WaveTurbulence.chosenSet
  ext v
  constructor
  · intro hv
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hl
    exact mem_image.mpr ⟨p.1,List.mem_toFinset.mpr (List.mem_map.mpr ⟨p,hp,rfl⟩),rfl⟩
  · intro hv
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨p,hp,rfl⟩,rfl⟩)

/-- The original single-child criterion is preserved exactly under sign-root placement. -/
theorem tree_isSpecialSet_coefficient_image (X : RegChain) (ζ : ℤˣ)
    (Z : Finset (Fin 1 × TTree.Path)) :
    IsSpecialSet (X.linksAt ζ (rootT ζ)) (Z.image (treeCoefficientAddress ζ)) ↔
      IsSpecialSet (X.treeLinks ζ) Z := by
  classical
  have hlinks : X.linksAt ζ (rootT ζ) = (X.treeLinks ζ).map
      (fun l => (treeCoefficientAddress ζ l.1,treeCoefficientAddress ζ l.2)) := by
    rw [← linksAt_toJRc,linksAt_rootT]
    rfl
  rw [hlinks]
  constructor
  · intro h z hz
    obtain ⟨i,hi⟩ := h (treeCoefficientAddress ζ z) (mem_image_of_mem _ hz)
    obtain ⟨l,hl,he⟩ := List.mem_map.mp hi
    have hf : l.1=z := treeCoefficientAddress_injective ζ (congrArg Prod.fst he)
    have hs : l.2=addrExt z [i] := treeCoefficientAddress_injective ζ
      ((congrArg Prod.snd he).trans (treeCoefficientAddress_addrExt ζ z [i]).symm)
    have heq : l=(z,addrExt z [i]) := Prod.ext hf hs
    exact ⟨i,heq ▸ hl⟩
  · intro h z hz
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
    obtain ⟨i,hi⟩ := h a ha
    refine ⟨i,List.mem_map.mpr ⟨(a,addrExt a [i]),hi,?_⟩⟩
    rw [treeCoefficientAddress_addrExt]

/-- The marked original indices are unaffected by the address embedding. -/
theorem treeMarkedIndices_coefficient_image (X : RegChain) (ζ : ℤˣ)
    (Z : Finset (Fin 1 × TTree.Path)) :
    treeMarkedIndices (treeChosenAddress X ζ) (Z.image (treeCoefficientAddress ζ)) =
      univ.filter (fun j => treeChosen X ζ j ∈ Z) := by
  classical
  ext j
  simp only [treeMarkedIndices,mem_filter,mem_univ,true_and]
  change treeCoefficientAddress ζ (treeChosen X ζ j) ∈ Z.image (treeCoefficientAddress ζ) ↔ _
  simp only [mem_image,(treeCoefficientAddress_injective ζ).eq_iff,exists_eq_right]

/-- The coefficient sign equals the original garden node sign, at either root sign. -/
theorem treeCoefficientAddress_nodeSgn (ζ : ℤˣ) (a : Fin 1 × TTree.Path) :
    ClassJR.nodeSgn (treeCoefficientAddress ζ a) = ((nodeSign ![ζ] a:ℤˣ):ℤ) := by
  have hh := nodeSgn_rootT_ext ζ a.2
  simpa only [ClassJR.addrExt,rootT,List.nil_append,nodeSign,
    show a.1=0 from Subsingleton.elim _ _,Matrix.cons_val_zero,treeCoefficientAddress] using hh

/-- F61's extracted sign is exactly the corrected original specialWeight. -/
theorem tree_coefficient_signed_weight_eq (ζ : ℤˣ) (Z : Finset (Fin 1 × TTree.Path)) :
    (∏ z ∈ Z.image (treeCoefficientAddress ζ), ((ClassJR.nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹)*
      (-1:ℂ)^(Z.image (treeCoefficientAddress ζ)).card = specialWeight ![ζ] Z := by
  classical
  rw [card_image_of_injective _ (treeCoefficientAddress_injective ζ),
    prod_image (fun _ _ _ _ h => treeCoefficientAddress_injective ζ h),
    specialWeight,prod_neg_inv_eq_sign_mul]
  simp_rw [treeCoefficientAddress_nodeSgn]
  ring

end WaveTurbulence.RegAsymp
