/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntCore2
public import WaveTurbulence.Foundations.Flower.MkSlots.IntPiece

/-! # B3s MK-SLOTS (integration, R-core 3): pins, dagger indicator and dagger constant of a member on `G_sb`

For a member `y` of the run class of the representative `a` (shape `Φ = memShape a mk y hy`), with the capped
flower parents at the core common to the class (`member_cfp_iff`, `member_cfp_br`, `member_unit_not_cfp`):
* `member_fixCap`: the pins of `y` at the cores of the `G_sb` atoms are the pins `fixAt` of the α piece;
* `member_fix_unit`: no core of an atom of a unit of `y` is pinned (`hU` of the pinned VINE-B♯);
* `member_sibInd`: on a skeleton decoration `κ` of `y`, the piece's dagger sibling indicator `sibIndAt` at the
  restricted decoration `Φ.resDec κ` is the indicator of the skeleton condition `RestInd` of `y`;
* `member_restConst`: the unimodular dagger constant `restConst` of `y` is the `G_sb` constant `capConstG`.
The `G_sb`-level data: `FlwG` (= the piece's `flwAt`), `momG`, `capThetaG`, `capFactorG`, `capConstG`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine

namespace WaveTurbulence.Flower.MkSlots.IntCore

open WaveTurbulence.Flower.MkSlots.IntRest

/-! ### `G_sb`-level data -/

section GData
variable {w d : ℕ} (G : Garden w) (J : Finset (Fin w))

/-- The flower children of a `G_sb` branch (the body of the piece's `flwAt`). -/
def FlwG (c : GBranch G.tree) (i : Fin 3) : Prop :=
  ∃ ℓ : GLeaf G.tree, ℓ.toNode = c.child i ∧ (G.pair ℓ).1.1 ∈ J

/-- The momentum of child `i` of `c` on the support of the dagger indicator. -/
def momG (L : ℝ) (roots : Fin w → (Fin d → ℤ)) (cc : Fin w → Fin 3 → Mom d) (c : GBranch G.tree) (i : Fin 3) :
    Mom d :=
  if h : FlwG G J c i then latticePoint L (roots (G.pair h.choose).1.1) else cc c.1.1 i

/-- The phase scale of the dagger at `c`. -/
def capThetaG (L γ δ s : ℝ) (c : GBranch G.tree) : ℝ :=
  Real.pi * ((G.sign c.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * s

/-- The factor of the dagger constant at `c`. -/
def capFactorG (L γ δ s : ℝ) (roots : Fin w → (Fin d → ℤ)) (cc : Fin w → Fin 3 → Mom d) (c : GBranch G.tree) : ℂ :=
  Complex.exp (((capThetaG G L γ δ s c * ‖∑ i : Fin 3, childSign i • momG G J L roots cc c i‖ ^ 2 : ℝ) : ℂ) *
      Complex.I) *
    ∏ i : Fin 3, if FlwG G J c i then 1 else
      Complex.exp (((-(capThetaG G L γ δ s c * childSign i * ‖cc c.1.1 i‖ ^ 2) : ℝ) : ℂ) * Complex.I)

/-- The indicator product: a product of `0/1` factors is the indicator of all of them being `1`. -/
theorem prod_ind_eq (P : GBranch G.tree → Prop) (flw : GBranch G.tree → Fin 3 → Prop)
    (k : GNode G.tree → Mom d) (cc : Fin w → Fin 3 → Mom d) :
    (∏ c : GBranch G.tree, if P c then
      ∏ i : Fin 3, (if flw c i then (1 : ℝ) else if k (c.child i) = cc c.1.1 i then 1 else 0) else 1) =
      if ∀ c, P c → ∀ i, ¬ flw c i → k (c.child i) = cc c.1.1 i then 1 else 0 := by
  split_ifs with hall
  · refine Finset.prod_eq_one fun c _ => ?_
    split_ifs with hc
    · refine Finset.prod_eq_one fun i _ => ?_
      split_ifs with hf hk
      · rfl
      · rfl
      · exact absurd (hall c hc i hf) hk
    · rfl
  · push_neg at hall
    obtain ⟨c, hc, i, hf, hk⟩ := hall
    refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
    rw [if_pos hc]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [if_neg hf, if_neg hk]

end GData

/-! ### Through a splice shape -/

section Shape
variable {w d : ℕ} {S : Garden w} {Ju : Type} [Fintype Ju] [DecidableEq Ju] {blk : Ju → CLBlock S}
  {G : Garden w} (Φ : SpliceShape blk G) (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (J : Finset (Fin w)) {p : ℕ} (hGeo : CapGeo (layeredReconstruction D hS layer hLayer) J p)

theorem br_fst (c : GBranch G.tree) : (Φ.br c).1.1 = c.1.1 := by
  have h := Φ.tree_eq c.toNode
  rw [← Φ.br_node] at h
  exact h

include hGeo in
/-- At a non-hinge atom whose core is a capped flower parent, the capped flower children are the `G_sb` flower
children. -/
theorem isCoreFlowerChild_br_iff (c : GBranch G.tree) (hh : ∀ j, Φ.br c ≠ (blk j).upper)
    (hb : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS (Φ.br c))) (i : Fin 3) :
    IsCoreFlowerChild D hS layer hLayer J (Φ.br c) i ↔ FlwG G J c i := by
  rw [isCoreFlowerChild_iff D hS layer hLayer J hGeo _ hb]
  constructor
  · rintro ⟨σ, hσ, hpJ⟩
    have hn : Φ.node (c.child i) = σ.toNode := (Φ.child c i hh).trans hσ.symm
    rcases SpliceShape.node_cases (c.child i) with ⟨c', hc'⟩ | ⟨ℓ, hℓ⟩
    · exfalso
      rw [← hc', ← Φ.br_node] at hn
      exact SpliceShape.leaf_ne_branch hn.symm
    · have hσℓ : Φ.leaf ℓ = σ := Mole.leaf_toNode_injective (by rw [Φ.leaf_node, hℓ, hn])
      refine ⟨ℓ, hℓ, ?_⟩
      rw [← shape_leaf_pair_idx Φ ℓ, hσℓ]
      exact hpJ
  · rintro ⟨ℓ, hℓ, hpJ⟩
    refine ⟨Φ.leaf ℓ, ?_, ?_⟩
    · rw [Φ.leaf_node, hℓ]; exact Φ.child c i hh
    · rw [shape_leaf_pair_idx]; exact hpJ

include hGeo in
theorem restChildMom_br (L : ℝ) (roots : Fin w → (Fin d → ℤ)) (cc : Fin w → Fin 3 → Mom d) (c : GBranch G.tree)
    (hh : ∀ j, Φ.br c ≠ (blk j).upper)
    (hb : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS (Φ.br c))) (i : Fin 3) :
    restChildMom D hS layer hLayer L J roots cc (Φ.br c) i = momG G J L roots cc c i := by
  by_cases hf : FlwG G J c i
  · have hfc := (isCoreFlowerChild_br_iff Φ D hS layer hLayer J hGeo c hh hb i).mpr hf
    have hσ : (Φ.leaf hf.choose).toNode = (Φ.br c).child i := by
      rw [Φ.leaf_node, hf.choose_spec.1]; exact Φ.child c i hh
    rw [restChildMom_flower D hS layer hLayer J hGeo L roots cc (Φ.br c) i (Φ.leaf hf.choose) hσ hfc,
      shape_leaf_pair_idx]
    unfold momG
    rw [dif_pos hf]
  · rw [restChildMom_other D hS layer hLayer J L roots cc (Φ.br c) i
      (fun h => hf ((isCoreFlowerChild_br_iff Φ D hS layer hLayer J hGeo c hh hb i).mp h))]
    unfold momG
    rw [dif_neg hf, br_fst]

theorem capTheta_br (L γ δ s : ℝ) (c : GBranch G.tree) :
    capTheta L γ δ s (layeredReconstruction D hS layer hLayer).garden (D.coreBranch hS (Φ.br c)) =
      capThetaG G L γ δ s c := by
  unfold capTheta capThetaG
  show Real.pi * (((D.garden hS).sign (D.coreBranch hS (Φ.br c)).toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * s = _
  rw [coreBranch_sign D hS (Φ.br c), Φ.br_node, Φ.sign]

include hGeo in
/-- **The dagger constant as a `G_sb` product.** -/
theorem restConst_shape (L γ δ s : ℝ) (roots : Fin w → (Fin d → ℤ)) (cc : Fin w → Fin 3 → Mom d)
    (hrange : ∀ b, IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b) →
      ∃ c, Φ.br c = b)
    (hnh : ∀ c, IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS (Φ.br c)) →
      ∀ j, Φ.br c ≠ (blk j).upper) :
    restConst D hS layer hLayer L γ δ s J roots cc =
      ∏ c ∈ univ.filter (fun c : GBranch G.tree =>
          IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS (Φ.br c))),
        capFactorG G J L γ δ s roots cc c := by
  unfold restConst
  symm
  refine Finset.prod_bij (fun c _ => Φ.br c) (fun c hc => ?_) (fun c _ c' _ h => Φ.br_inj h) (fun b hb => ?_)
    (fun c hc => ?_)
  · exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hc).2⟩
  · obtain ⟨c, rfl⟩ := hrange b (mem_filter.mp hb).2
    exact ⟨c, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hb).2⟩, rfl⟩
  · have hb := (mem_filter.mp hc).2
    have hh := hnh c hb
    have hmom : ∀ i, restChildMom D hS layer hLayer L J roots cc (Φ.br c) i = momG G J L roots cc c i :=
      fun i => restChildMom_br Φ D hS layer hLayer J hGeo L roots cc c hh hb i
    have hfl : ∀ i, IsCoreFlowerChild D hS layer hLayer J (Φ.br c) i ↔ FlwG G J c i :=
      fun i => isCoreFlowerChild_br_iff Φ D hS layer hLayer J hGeo c hh hb i
    unfold capFactorG
    rw [capTheta_br Φ D hS layer hLayer L γ δ s c]
    simp only [hmom, hfl, br_fst]

include hGeo in
/-- **The skeleton dagger condition as a `G_sb` condition.** -/
theorem restInd_shape (L : ℝ) (cc : Fin w → Fin 3 → Mom d) {roots : Fin w → (Fin d → ℤ)} (hd : Disj blk)
    (hrange : ∀ b, IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b) →
      ∃ c, Φ.br c = b)
    (hnh : ∀ c, IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS (Φ.br c)) →
      ∀ j, Φ.br c ≠ (blk j).upper)
    (κ : GenDecoration S d roots 0) :
    RestInd D hS layer hLayer L J cc κ ↔
      ∀ c, IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS (Φ.br c)) →
        ∀ i, ¬ FlwG G J c i → cosetDecoration G L 0 (Φ.resDec hS hd κ).1 (c.child i) = cc c.1.1 i := by
  have hco : ∀ c, (∀ j, Φ.br c ≠ (blk j).upper) → ∀ i,
      cosetDecoration G L 0 (Φ.resDec hS hd κ).1 (c.child i) = cosetDecoration S L 0 κ.1 ((Φ.br c).child i) := by
    intro c hh i
    show 0 + latticePoint L (κ.1 (Φ.node (c.child i))) = 0 + latticePoint L (κ.1 ((Φ.br c).child i))
    rw [Φ.child c i hh]
  constructor
  · intro h c hb i hf
    have hh := hnh c hb
    rw [hco c hh i, ← br_fst Φ c]
    exact h (Φ.br c) hb i (fun h' => hf ((isCoreFlowerChild_br_iff Φ D hS layer hLayer J hGeo c hh hb i).mp h'))
  · intro h b hb i hf
    obtain ⟨c, rfl⟩ := hrange b hb
    have hh := hnh c hb
    rw [← hco c hh i, br_fst]
    exact h c hb i (fun h' => hf ((isCoreFlowerChild_br_iff Φ D hS layer hLayer J hGeo c hh hb i).mpr h'))

end Shape

/-- The capped flower parents of a decoded garden are those of the reconstruction. -/
theorem cfp_decoded_iff {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (LG : LayeredGarden w)
    (hspec : layeredReconstruction D hS layer hLayer = LG) (hd : D.Decodes hS LG.garden) (J : Finset (Fin w))
    (b : GBranch S.tree) :
    IsCapFlowerParent LG J (D.decodedCoreBranch hS hd b) ↔
      IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b) := by
  subst hspec
  exact Iff.rfl

/-- Plain intrinsic pins: a capped flower parent is pinned at `s`, nothing else. -/
theorem fixCap_plain {w : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w)) (t s : ℝ) (b : GBranch LG.garden.tree) :
    fixCap LG J (fun _ => FixPat.plain) t s b = if IsCapFlowerParent LG J b then some s else none := by
  unfold fixCap
  split_ifs <;> rfl

/-! ### The run class -/

section Class
variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (J : Finset (Fin (2 * R)))
  (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
  (hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf)
  (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))

/-- The representative's predicate of the α piece, read on the reconstruction. -/
theorem cfp_coreAt_iff (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    IsCapFlowerParent a.layered J (coreAt a (mk a.prime) c) ↔
      IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)) J
        (a.prime.data.coreBranch a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)) :=
  cfp_decoded_iff a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
    (sourceLayer_reconstructs a) a.prime.decodes J _

include hG hcapA hcapY hrepU in
/-- **The pins of a member at the `G_sb` atoms are the pins of the α piece.** -/
theorem member_fixCap (t s : ℝ) (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
        (fun _ => FixPat.plain) t s (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)) =
      fixAt J (fun _ => FixPat.plain) t s a (mk a.prime) c := by
  unfold fixAt
  refine (fixCap_plain _ J t s _).trans (Eq.trans ?_ (fixCap_plain _ J t s _).symm)
  by_cases h : IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c))
  · rw [if_pos ((member_cfp_iff a mk y hy hG J hcapA hcapY hrepU c).mpr h),
      if_pos ((cfp_coreAt_iff a mk J c).mpr h)]
  · rw [if_neg (fun h' => h ((member_cfp_iff a mk y hy hG J hcapA hcapY hrepU c).mp h')),
      if_neg (fun h' => h ((cfp_coreAt_iff a mk J c).mp h'))]

include hy hG hcapA hcapY hrepU in
/-- **No core of an atom of a unit of a member is pinned.** -/
theorem member_fix_unit (t s : ℝ) (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length)
    (b : GBranch y.1.skeleton.tree) (hb : b ∈ (unitClBlock (y.2 j)).atoms) :
    fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
      (fun _ => FixPat.plain) t s (y.1.data.coreBranch y.1.plain b) = none := by
  refine (fixCap_plain _ J t s _).trans ?_
  rw [if_neg (member_unit_not_cfp a mk y hy hG J hcapA hcapY hrepU j b hb)]

include hG hcapA hcapY hrepU in
theorem member_hrange (b : GBranch y.1.skeleton.tree)
    (hb : IsCapFlowerParent (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
      J (y.1.data.coreBranch y.1.plain b)) :
    ∃ c, (memShape a mk y hy).br c = b :=
  member_cfp_br a mk y hy hG J hcapA hcapY hrepU b hb

include hG hcapA hcapY hrepU in
theorem member_hnh (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree)
    (hb : IsCapFlowerParent (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
      J (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)))
    (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) :
    (memShape a mk y hy).br c ≠ (unitClBlock (y.2 j)).upper := by
  intro h
  rw [h] at hb
  exact member_unit_not_cfp a mk y hy hG J hcapA hcapY hrepU j _ (upper_mem _) hb

/-- **The dagger constant of `G_sb`** (over the atoms whose representative core is a capped flower parent). -/
def capConstG {d : ℕ} (L γ δ s : ℝ) (roots : Fin (2 * R) → (Fin d → ℤ)) (cc : Fin (2 * R) → Fin 3 → Mom d) : ℂ :=
  ∏ c ∈ univ.filter (fun c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree =>
      IsCapFlowerParent a.layered J (coreAt a (mk a.prime) c)),
    capFactorG (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G J L γ δ s roots cc c

theorem norm_capConstG {d : ℕ} (L γ δ s : ℝ) (roots : Fin (2 * R) → (Fin d → ℤ))
    (cc : Fin (2 * R) → Fin 3 → Mom d) : ‖capConstG a mk J L γ δ s roots cc‖ = 1 := by
  unfold capConstG capFactorG
  rw [norm_prod]
  refine Finset.prod_eq_one fun c _ => ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs
  · exact norm_one
  · exact Complex.norm_exp_ofReal_mul_I _

include hy hG hcapA hcapY hrepU in
/-- **The dagger constant of a member is the `G_sb` constant.** -/
theorem member_restConst {d : ℕ}
    (hGeoY : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p)
    (L γ δ s : ℝ) (roots : Fin (2 * R) → (Fin d → ℤ)) (cc : Fin (2 * R) → Fin 3 → Mom d) :
    restConst y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ s J roots cc =
      capConstG a mk J L γ δ s roots cc := by
  rw [restConst_shape (memShape a mk y hy) y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hGeoY
    L γ δ s roots cc (member_hrange a mk y hy hG J hcapA hcapY hrepU)
    (member_hnh a mk y hy hG J hcapA hcapY hrepU)]
  unfold capConstG
  congr 1
  ext c
  simp only [mem_filter, mem_univ, true_and]
  rw [member_cfp_iff a mk y hy hG J hcapA hcapY hrepU c, cfp_coreAt_iff a mk J c]

include hG hcapA hcapY hrepU in
/-- **The dagger sibling indicator of the piece on a member's decoration** is the indicator of `RestInd`. -/
theorem member_sibInd {d : ℕ}
    (hGeoY : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p)
    (L : ℝ) (cc : Fin (2 * R) → Fin 3 → Mom d) {roots : Fin (2 * R) → (Fin d → ℤ)}
    (κ : GenDecoration y.1.skeleton d roots 0) :
    sibIndAt J a (mk a.prime) (some cc) (flwAt J a (mk a.prime))
        (cosetDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G L 0
          ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ).1) =
      if RestInd y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L J cc κ then 1 else 0 := by
  have hP := prod_ind_eq (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G
    (fun c => IsCapFlowerParent a.layered J (coreAt a (mk a.prime) c)) (flwAt J a (mk a.prime))
    (cosetDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G L 0
      ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ).1) cc
  unfold sibIndAt
  refine hP.trans ?_
  congr 1
  rw [restInd_shape (memShape a mk y hy) y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hGeoY
    L cc (source_disjMk a mk y hy) (member_hrange a mk y hy hG J hcapA hcapY hrepU)
    (member_hnh a mk y hy hG J hcapA hcapY hrepU) κ]
  refine propext (forall_congr' fun c => ?_)
  rw [member_cfp_iff a mk y hy hG J hcapA hcapY hrepU c, cfp_coreAt_iff a mk J c]
  rfl

end Class

end WaveTurbulence.Flower.MkSlots.IntCore
