/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.CapMult

/-! # B3s MK-SLOTS (cap slots): the multiplier of the paired tree

On every coset decoration of the paired tree at the cap momentum `x₀`, the multiplier `m1` of a nontrivial cap slot
(the node weights `capNodeW` of the native couple times the cap pair's anchored factors) is a unimodular constant
`capC0` times D3's admissible multiplier: the frontier star weight (`frontS`, INC-TOP `topStar` of the frontier
cutoff) times the dagger sibling indicator `capInd` (a `TermChildIndicator`): on its support the children of the
terminal node carry fixed momenta, so the removed phase is constant (`m1_eq`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine

namespace WaveTurbulence.Flower.MkSlots

namespace CapSide

variable {w : ℕ} {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {J : Finset (Fin w)}
  {q : SourcePair S} (K : CapSide D hS J q)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {p : ℕ} (hGeo : CapGeo (layeredReconstruction D hS layer hLayer) J p)

/-- The terminal chain node on the paired tree. -/
def aF : GBranch (K.Dq layer hLayer).T1.garden.tree :=
  ⟨((0 : Fin 1), K.X.lonePath.dropLast), K.dropLast_mem_branching⟩

/-- The embedding of the paired tree's nodes in the reconstruction. -/
abbrev e1 (a1 : GNode (K.Dq layer hLayer).T1.garden.tree) : GNode (D.forest hS) :=
  (nativeCoupleForest D hS q).nodeEmbedding ((K.Dq layer hLayer).ι a1)

theorem e1_val (a1 : GNode (K.Dq layer hLayer).T1.garden.tree) : (K.e1 layer hLayer a1).1 = addrExt K.u a1.1.2 :=
  K.emb_ι layer hLayer a1

theorem e1_fst (a1 : GNode (K.Dq layer hLayer).T1.garden.tree) : (K.e1 layer hLayer a1).1.1 = K.u.1 := by
  rw [K.e1_val layer hLayer a1]; rfl

theorem node_ext1 {a1 b1 : GNode (K.Dq layer hLayer).T1.garden.tree} (h : a1.1.2 = b1.1.2) : a1 = b1 :=
  Subtype.ext (Prod.ext (Subsingleton.elim _ _) h)

theorem e1_eq_bF_iff (a1 : GNode (K.Dq layer hLayer).T1.garden.tree) :
    K.e1 layer hLayer a1 = K.bF.toNode ↔ a1 = (K.aF layer hLayer).toNode := by
  constructor
  · intro h
    have h2 := congrArg (fun z : GNode (D.forest hS) => z.1.2) h
    simp only [K.e1_val layer hLayer a1] at h2
    exact K.node_ext1 layer hLayer (List.append_cancel_left h2)
  · rintro rfl
    exact Subtype.ext (K.e1_val layer hLayer _)

theorem e1_eq_child_iff (a1 : GNode (K.Dq layer hLayer).T1.garden.tree) (i : Fin 3) :
    K.e1 layer hLayer a1 = K.bF.child i ↔ a1 = (K.aF layer hLayer).child i := by
  constructor
  · intro h
    have h2 := congrArg (fun z : GNode (D.forest hS) => z.1.2) h
    simp only [K.e1_val layer hLayer a1, GBranch.child] at h2
    rw [K.bF_val] at h2
    simp only [addrExt, List.append_assoc] at h2
    exact K.node_ext1 layer hLayer (List.append_cancel_left h2)
  · rintro rfl
    refine Subtype.ext ?_
    rw [K.e1_val layer hLayer]
    show addrExt K.u (K.X.lonePath.dropLast ++ [i]) = (K.bF.1.1, K.bF.1.2 ++ [i])
    rw [K.bF_val]
    simp [addrExt, List.append_assoc]

/-- The four nodes of the terminal star on the paired tree. -/
def starNodeF (o : Option (Fin 3)) : GNode (K.Dq layer hLayer).T1.garden.tree :=
  o.elim (K.aF layer hLayer).toNode (K.aF layer hLayer).child

theorem starNodeF_injective : Function.Injective (K.starNodeF layer hLayer) := by
  intro o o' h
  have h2 := congrArg (fun z : GNode (K.Dq layer hLayer).T1.garden.tree => z.1.2) h
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some i => simp [starNodeF, Option.elim, aF, GBranch.child, GBranch.toNode] at h2
  | some i =>
    cases o' with
    | none => simp [starNodeF, Option.elim, aF, GBranch.child, GBranch.toNode] at h2
    | some j =>
      simp only [starNodeF, Option.elim, aF, GBranch.child] at h2
      rw [List.singleton_injective (List.append_cancel_left h2)]

/-- A product over the paired tree's nodes that is trivial off the terminal star. -/
theorem prod_starF {M : Type*} [CommMonoid M] (f : GNode (K.Dq layer hLayer).T1.garden.tree → M)
    (hf : ∀ a1, a1 ≠ (K.aF layer hLayer).toNode → (∀ i, a1 ≠ (K.aF layer hLayer).child i) → f a1 = 1) :
    ∏ a1, f a1 = f (K.aF layer hLayer).toNode * ∏ i : Fin 3, f ((K.aF layer hLayer).child i) := by
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image (K.starNodeF layer hLayer)))
    (fun a1 _ ha => hf a1 (fun h => ha (Finset.mem_image.2 ⟨none, Finset.mem_univ _, h.symm⟩))
      (fun i h => ha (Finset.mem_image.2 ⟨some i, Finset.mem_univ _, h.symm⟩))),
    Finset.prod_image (fun x _ y _ h => K.starNodeF_injective layer hLayer h), Fintype.prod_option]
  rfl

/-! ### The dagger product -/

include hGeo in
theorem dag_prod {d : ℕ} (L γ δ s : ℝ) (cc : Fin w → Fin 3 → Mom d)
    (K' : GNode (K.Dq layer hLayer).T1.garden.tree → Mom d) :
    ∏ a1, dagNodeW L γ δ s (layeredReconstruction D hS layer hLayer) J (some cc) (K.e1 layer hLayer a1) (K' a1) =
      Complex.exp (((K.θF L γ δ s * ‖K' (K.aF layer hLayer).toNode‖ ^ 2 : ℝ) : ℂ) * Complex.I) *
        ∏ i : Fin 3, (Complex.exp (((-(K.θF L γ δ s * childSign i * ‖K' ((K.aF layer hLayer).child i)‖ ^ 2) : ℝ) : ℂ) *
          Complex.I) * (if i = K.iF then 1 else if K' ((K.aF layer hLayer).child i) = cc K.bF.1.1 i then 1 else 0)) := by
  rw [K.prod_starF layer hLayer]
  · rw [show K.e1 layer hLayer (K.aF layer hLayer).toNode = K.bF.toNode from
      (K.e1_eq_bF_iff layer hLayer _).2 rfl, K.dag_bF layer hLayer hGeo]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show K.e1 layer hLayer ((K.aF layer hLayer).child i) = K.bF.child i from
      (K.e1_eq_child_iff layer hLayer _ i).2 rfl, K.dag_child layer hLayer hGeo]
  · intro a1 h1 h2
    exact K.dag_other layer hLayer hGeo L γ δ s cc _ (K.e1_fst layer hLayer a1)
      (fun h => h1 ((K.e1_eq_bF_iff layer hLayer a1).1 h)) (fun i h => h2 i ((K.e1_eq_child_iff layer hLayer a1 i).1 h)) _

/-- The dagger sibling indicator on the paired tree. -/
def capInd {d : ℕ} (dag : Option (Fin w → Fin 3 → Mom d)) (K' : GNode (K.Dq layer hLayer).T1.garden.tree → Mom d) :
    ℝ :=
  dag.elim 1 fun cc => ∏ i : Fin 3,
    (if i = K.iF then 1 else if K' ((K.aF layer hLayer).child i) = cc K.bF.1.1 i then 1 else 0)

theorem capInd_01 {d : ℕ} (dag : Option (Fin w → Fin 3 → Mom d))
    (K' : GNode (K.Dq layer hLayer).T1.garden.tree → Mom d) :
    0 ≤ K.capInd layer hLayer dag K' ∧ K.capInd layer hLayer dag K' ≤ 1 := by
  cases dag with
  | none => exact ⟨zero_le_one, le_rfl⟩
  | some cc =>
    unfold capInd
    simp only [Option.elim]
    exact prod01 Finset.univ _ fun i _ => ite01 one01 (ite01 one01 zero01)

theorem termChild_capInd {d : ℕ} (dag : Option (Fin w → Fin 3 → Mom d)) :
    TermChildIndicator K.X (K.capInd layer hLayer dag) := by
  refine ⟨fun K' => K.capInd_01 layer hLayer dag K', fun K' K'' hK => ?_⟩
  cases dag with
  | none => rfl
  | some cc =>
    unfold capInd
    simp only [Option.elim]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hk : K' ((K.aF layer hLayer).child i) = K'' ((K.aF layer hLayer).child i) := by
      refine hK _ rfl ?_ ?_
      · simp [aF, GBranch.child]
      · simp [aF, GBranch.child]
    rw [hk]

/-- The fixed momenta of the terminal star on the dagger support. -/
def yF {d : ℕ} (x₀ : Mom d) (cc : Fin w → Fin 3 → Mom d) (i : Fin 3) : Mom d :=
  if i = K.iF then x₀ else cc K.bF.1.1 i

/-- The constant removed phase on the dagger support. -/
def capC0 {d : ℕ} (L γ δ s : ℝ) (x₀ : Mom d) (dag : Option (Fin w → Fin 3 → Mom d)) : ℂ :=
  dag.elim 1 fun cc =>
    Complex.exp (((K.θF L γ δ s * ‖K.yF x₀ cc 0 - K.yF x₀ cc 1 + K.yF x₀ cc 2‖ ^ 2 : ℝ) : ℂ) * Complex.I) *
      ∏ i : Fin 3, Complex.exp (((-(K.θF L γ δ s * childSign i * ‖K.yF x₀ cc i‖ ^ 2) : ℝ) : ℂ) * Complex.I)

theorem norm_capC0 {d : ℕ} (L γ δ s : ℝ) (x₀ : Mom d) (dag : Option (Fin w → Fin 3 → Mom d)) :
    ‖K.capC0 L γ δ s x₀ dag‖ = 1 := by
  cases dag with
  | none => simp [capC0]
  | some cc =>
    simp only [capC0, Option.elim, norm_mul, norm_prod, Complex.norm_exp_ofReal_mul_I, Finset.prod_const_one,
      mul_one]

theorem aF_child_iF : (K.aF layer hLayer).child K.iF = (K.Dq layer hLayer).lone1 :=
  Subtype.ext (by
    show ((0 : Fin 1), K.X.lonePath.dropLast ++ [K.iF]) = ((0 : Fin 1), K.X.lonePath)
    rw [← K.lonePath_eq])

include hGeo in
/-- **The dagger product on a coset decoration** is the constant phase times the sibling indicator. -/
theorem dag_prod_coset {d : ℕ} (L γ δ s : ℝ) (x₀ : Mom d) (dag : Option (Fin w → Fin 3 → Mom d))
    (κ : GenDecoration (K.Dq layer hLayer).T1.garden d (fun _ => 0) 0) :
    ∏ a1, dagNodeW L γ δ s (layeredReconstruction D hS layer hLayer) J dag (K.e1 layer hLayer a1)
        (cosetDecoration (K.Dq layer hLayer).T1.garden L x₀ κ.1 a1) =
      K.capC0 L γ δ s x₀ dag * (K.capInd layer hLayer dag (cosetDecoration (K.Dq layer hLayer).T1.garden L x₀ κ.1) : ℂ) := by
  cases dag with
  | none => simp [dagNodeW, capC0, capInd]
  | some cc =>
    set K' := cosetDecoration (K.Dq layer hLayer).T1.garden L x₀ κ.1 with hK'
    rw [K.dag_prod layer hLayer hGeo L γ δ s cc K']
    simp only [Finset.prod_mul_distrib]
    unfold capC0 capInd
    simp only [Option.elim]
    by_cases hind : ∀ i : Fin 3, i ≠ K.iF → K' ((K.aF layer hLayer).child i) = cc K.bF.1.1 i
    · have hy : ∀ i, K' ((K.aF layer hLayer).child i) = K.yF x₀ cc i := by
        intro i
        unfold yF
        by_cases hi : i = K.iF
        · rw [if_pos hi, hi, K.aF_child_iF layer hLayer]
          exact (K.Dq layer hLayer).lone_coset L x₀ κ
        · rw [if_neg hi]; exact hind i hi
      have hroot : K' (K.aF layer hLayer).toNode = K.yF x₀ cc 0 - K.yF x₀ cc 1 + K.yF x₀ cc 2 := by
        have hdec := (isDecoration_coset _ L x₀ κ.2.1).1 (K.aF layer hLayer)
        rw [← hK'] at hdec
        rw [hdec, hy 0, hy 1, hy 2]
      have hone : ∀ i : Fin 3, (if i = K.iF then (1 : ℂ) else
          if K' ((K.aF layer hLayer).child i) = cc K.bF.1.1 i then 1 else 0) = 1 := by
        intro i
        by_cases hi : i = K.iF
        · rw [if_pos hi]
        · rw [if_neg hi, if_pos (hind i hi)]
      have hone' : ∀ i : Fin 3, (if i = K.iF then (1 : ℝ) else
          if K' ((K.aF layer hLayer).child i) = cc K.bF.1.1 i then 1 else 0) = 1 := by
        intro i
        by_cases hi : i = K.iF
        · rw [if_pos hi]
        · rw [if_neg hi, if_pos (hind i hi)]
      rw [Finset.prod_eq_one (fun i _ => hone i), Finset.prod_eq_one (fun i _ => hone' i), Complex.ofReal_one,
        mul_one, mul_one, hroot]
      congr 1
      exact Finset.prod_congr rfl fun i _ => by rw [hy i]
    · push_neg at hind
      obtain ⟨i0, hi0, hne⟩ := hind
      have hz : ∏ i : Fin 3, (if i = K.iF then (1 : ℂ) else
          if K' ((K.aF layer hLayer).child i) = cc K.bF.1.1 i then 1 else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i0) (by rw [if_neg hi0, if_neg hne])
      have hz' : ∏ i : Fin 3, (if i = K.iF then (1 : ℝ) else
          if K' ((K.aF layer hLayer).child i) = cc K.bF.1.1 i then 1 else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i0) (by rw [if_neg hi0, if_neg hne])
      rw [hz, hz', mul_zero, mul_zero, Complex.ofReal_zero, mul_zero]

end CapSide

end WaveTurbulence.Flower.MkSlots
