/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtWhole.RegExtract
public import WaveTurbulence.Foundations.Flower.ProtGeo.Sel
public import WaveTurbulence.Foundations.Flower.ProtGeo.Cfg
public import WaveTurbulence.Foundations.Flower.IncTop.TopWeight
public import WaveTurbulence.Foundations.Flower.Stage1W.Frontier
public import WaveTurbulence.Foundations.Flower.MkDefs.Intrinsic

/-! # D6b: the marked weight of a wholly regular component is a protected multiplier

On a cap couple (`CapG`, cap tree `c`, `J = {c}`), read through the projection `ρ` on the paired tree `T1`:
* frontier cutoffs = INC-TOP star weights on `frontS` (`frontierW_eq`);
* capped stem filters = one filter layer `stemF` at scale `2^i L` (`stemFilterCap_eq`);
* the selected-face weight = `selConst · filtWeight (selF ∪ Sel) (· ∈ Sel) Rs` with `Sel = objSelT` (D2b),
  `selConst = R⁻¹` when a vertex is selected (`selWeightCap_eq`);
* anchored profiles = the input-leaf product of `H1` (`leafProdCap_eq`);
* the dagger = `ind1`, a `TermChildIndicator` (`termChild_ind1`);
* the removed phase at the flower parent is constant on the dagger support (`offFactor_const`).

Main result `compValue_capG`: a component value is `[roots c = roots j0] · C · selConst · kernelProt T1 H1 mult …`
with `‖C‖ ≤ 1`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open scoped Classical

namespace WaveTurbulence.Flower.ProtWhole

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtGeo
open WaveTurbulence.Flower.MkDefs

theorem fin2_prod {M : Type*} [CommMonoid M] (f : Fin 2 → M) (j0 c : Fin 2) (h : j0 ≠ c) :
    ∏ j, f j = f j0 * f c := by
  fin_cases j0 <;> fin_cases c <;> simp_all [Fin.prod_univ_two, mul_comm]

theorem prod01 {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    0 ≤ ∏ i ∈ s, f i ∧ ∏ i ∈ s, f i ≤ 1 :=
  ⟨Finset.prod_nonneg fun i hi => (h i hi).1, Finset.prod_le_one₀ (fun i hi => (h i hi).1) fun i hi => (h i hi).2⟩

theorem ite01 {q : Prop} [Decidable q] {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    0 ≤ (if q then a else b) ∧ (if q then a else b) ≤ 1 := by
  split
  · exact ha
  · exact hb

theorem one01 : (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1 := ⟨zero_le_one, le_rfl⟩

theorem zero01 : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩

/-- The stem filter scale `2^i L`. -/
def regStemScale (j0 : Fin 2) (σ : Fin 2 → Option ℕ) (L : ℝ) : ℝ := 2 ^ ((σ j0).getD 0) * L

/-- The explicit factor `R⁻¹` of a selection. -/
def regSelConst (LG : LayeredGarden 2) (c j0 : Fin 2) (Rs : Fin 2 → ℝ) (kSel : Fin 2 → Option ℕ) : ℝ :=
  if (selCap LG {c} kSel j0).isSome then (Rs j0)⁻¹ else 1

/-- The leaf profiles of the paired tree. -/
def regH1 {d : ℕ} (LG : LayeredGarden 2) (j0 : Fin 2) (h : ℕ → Fin 2 → Fin 2 → Mom d → ℝ) : LeafProfiles 1 d :=
  fun z => typeProfiles LG h (j0, z.2)

/-- Coset decorations of integer decorations are decorations. -/
theorem isDecoration_coset {w d : ℕ} (G : Garden w) (L : ℝ) (k₀ : Mom d) {κ : GNode G.tree → (Fin d → ℤ)}
    (h : IsDecoration G κ) : IsDecoration G (cosetDecoration G L k₀ κ) := by
  refine ⟨fun b => ?_, fun ℓ => ?_⟩
  · show k₀ + latticePoint L (κ b.toNode) =
      (k₀ + latticePoint L (κ (b.child 0))) - (k₀ + latticePoint L (κ (b.child 1))) +
        (k₀ + latticePoint L (κ (b.child 2)))
    rw [h.1 b, WaveTurbulence.Links.latticePoint_add, WaveTurbulence.Links.latticePoint_sub]
    abel
  · show k₀ + latticePoint L (κ ℓ.toNode) = k₀ + latticePoint L (κ (G.pair ℓ).toNode)
    rw [h.2 ℓ]

/-- `kernelProt` sees its multiplier only on the coset decorations. -/
theorem kernelProt_congr_m {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m m' : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hm : ∀ κ : GenDecoration LG.garden d nroot nfl,
      m (cosetDecoration LG.garden L k₀ κ.1) = m' (cosetDecoration LG.garden L k₀ κ.1)) :
    kernelProt L γ δ LG H m up s fix k₀ nroot nfl = kernelProt L γ δ LG H m' up s fix k₀ nroot nfl := by
  unfold kernelProt
  congr 1
  exact tsum_congr fun κ => by rw [hm κ]

/-- Profiles carried by the multiplier can be moved to the leaves. -/
theorem kernelProt_moveH {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelProt L γ δ LG (fun _ _ => 1) (fun K => m K * ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (K ℓ.toNode) : ℂ))
        up s fix k₀ nroot nfl = kernelProt L γ δ LG H m up s fix k₀ nroot nfl := by
  unfold kernelProt
  congr 1
  refine tsum_congr fun κ => ?_
  simp only [Complex.ofReal_one, Finset.prod_const_one, mul_one]
  ring

namespace CapG

variable {LG : LayeredGarden 2} {j0 c : Fin 2} {X : RegChain} {ζ : ℤˣ} (D : CapG LG j0 c X ζ)
include D

variable {d : ℕ}

/-! ### Nodes -/

/-- The nodes of the couple: the cap root, and the nodes of the paired tree. -/
def nodeEquiv : Option (GNode D.T1.garden.tree) ≃ GNode LG.garden.tree where
  toFun o := o.elim (GNode.root LG.garden.tree c) D.ι
  invFun a := if a.1.1 = j0 then some (D.ρ a) else none
  left_inv o := by
    cases o with
    | none =>
      show (if (GNode.root LG.garden.tree c).1.1 = j0 then some (D.ρ (GNode.root LG.garden.tree c)) else none) = none
      rw [if_neg (fun h => D.ne h.symm)]
    | some a1 =>
      exact (if_pos (show (D.ι a1).1.1 = j0 from rfl)).trans (congrArg some (D.ρ_ι a1))
  right_inv a := by
    by_cases h : a.1.1 = j0
    · show (if a.1.1 = j0 then some (D.ρ a) else none).elim (GNode.root LG.garden.tree c) D.ι = a
      rw [if_pos h]
      exact D.ι_ρ a h
    · show (if a.1.1 = j0 then some (D.ρ a) else none).elim (GNode.root LG.garden.tree c) D.ι = a
      rw [if_neg h]
      exact Subtype.ext (D.node_c a h).symm

theorem prod_nodes {M : Type*} [CommMonoid M] (g : GNode LG.garden.tree → M) :
    ∏ a, g a = g (GNode.root LG.garden.tree c) * ∏ a1 : GNode D.T1.garden.tree, g (D.ι a1) := by
  rw [← D.nodeEquiv.prod_comp, Fintype.prod_option]
  rfl

/-! ### Frontier cutoffs -/

/-- The frontier nodes, on the paired tree. -/
def frontS (p : ℕ) : Finset (GNode D.T1.garden.tree) :=
  Finset.univ.filter fun a1 => LG.IsTopLeaf p (D.ι a1) ∧ LG.layer (D.ι a1) < p ∧ ¬ LG.IsFlowerNode (D.ι a1)

theorem frontierW_eq (p : ℕ) (Rf : Fin 2 → Option ℝ) (K : GNode D.T1.garden.tree → Mom d) :
    ((Typed.frontierW LG p Rf (fun a => K (D.ρ a)) : ℝ) : ℂ) =
      IncTop.starWeight (D.frontS p) (IncTop.topStar (fun _ => Stage1W.frontierG (Rf j0))) K := by
  unfold Typed.frontierW IncTop.starWeight frontS
  rw [D.prod_nodes]
  have hroot : ¬ LG.IsTopLeaf p (GNode.root LG.garden.tree c) := fun h => h.2.1 rfl
  rw [if_neg (fun h => hroot h.1), one_mul, Complex.ofReal_prod, Finset.prod_filter]
  refine Finset.prod_congr rfl fun a1 _ => ?_
  split_ifs with h
  · unfold IncTop.topStar Stage1W.frontierG
    rw [IncTop.starMomenta_zero]
    show ((((Rf j0).elim 1 fun r => chi0 (‖K (D.ρ (D.ι a1))‖ / r) : ℝ)) : ℂ) =
      (((Rf j0).elim 1 fun r => chi0 (‖K a1‖ / r) : ℝ) : ℂ)
    rw [D.ρ_ι]
  · simp

theorem card_frontS_le (p : ℕ) : (D.frontS p).card ≤ Fintype.card (GNode D.T1.garden.tree) :=
  Finset.card_le_univ _

/-! ### Capped stem filters -/

/-- The capped stem of tree `j0`, on the paired tree. -/
def stem1 : Finset (GBranch D.T1.garden.tree) :=
  Finset.univ.filter fun b1 => D.βc b1 ∈ stemSetCap LG {c} j0

theorem mem_stem1 (b1 : GBranch D.T1.garden.tree) : b1 ∈ D.stem1 ↔ D.βc b1 ∈ stemSetCap LG {c} j0 := by
  simp [stem1]

theorem stemSetCap_c : stemSetCap LG {c} c = ∅ := by
  ext b
  simp only [stemSetCap, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro ⟨hb, -⟩
  exact D.ne ((D.branch_j0 b).symm.trans hb)

theorem omegaNode_βc (K : GNode D.T1.garden.tree → Mom d) (b1 : GBranch D.T1.garden.tree) :
    omegaNode LG.garden (fun a => K (D.ρ a)) (D.βc b1) = omegaNode D.T1.garden K b1 := by
  unfold omegaNode
  simp only [D.βc_child, D.βc_toNode, D.ρ_ι]

theorem prod_stem (g : GBranch LG.garden.tree → ℝ) :
    ∏ b ∈ stemSetCap LG {c} j0, g b = ∏ b1 ∈ D.stem1, g (D.βc b1) := by
  have hs : stemSetCap LG {c} j0 = D.stem1.map D.βc.toEmbedding := by
    ext b
    simp only [Finset.mem_map, Equiv.toEmbedding_apply, D.mem_stem1]
    exact ⟨fun hb => ⟨D.βc.symm b, by simpa using hb, by simp⟩, fun ⟨b1, hb1, he⟩ => he ▸ hb1⟩
  rw [hs, Finset.prod_map]
  rfl

/-- The stem filter set (empty without a stem filter). -/
def stemF (σ : Fin 2 → Option ℕ) : Finset (GBranch D.T1.garden.tree) := if (σ j0).isSome then D.stem1 else ∅

theorem stemFilterCap_eq (L : ℝ) (σ : Fin 2 → Option ℕ) (K : GNode D.T1.garden.tree → Mom d) :
    ((stemFilterCap LG {c} L σ (fun a => K (D.ρ a)) : ℝ) : ℂ) =
      filtWeight (D.stemF σ) (fun _ => false) (fun _ => regStemScale j0 σ L) K := by
  unfold stemFilterCap
  rw [fin2_prod _ j0 c D.ne, D.stemSetCap_c]
  have hc : ((σ c).elim 1 fun i => prodDyadicCut (2 ^ i * L) 0 (∅ : Finset (GBranch LG.garden.tree))
      (fun b => |omegaNode LG.garden (fun a => K (D.ρ a)) b|)) = 1 := by
    cases σ c <;> simp [prodDyadicCut]
  rw [hc, mul_one]
  unfold stemF regStemScale filtWeight
  cases hσ : σ j0 with
  | none => simp
  | some i =>
    simp only [Option.elim, Option.isSome_some, if_true, Option.getD_some, Bool.false_eq_true, if_false]
    unfold prodDyadicCut
    rw [if_pos rfl, D.prod_stem, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun b1 _ => ?_
    simp only [D.omegaNode_βc]

/-! ### The selected-face weight -/

theorem selCap_c (kSel : Fin 2 → Option ℕ) : selCap LG {c} kSel c = none := by
  unfold selCap
  cases kSel c with
  | none => rfl
  | some k =>
    show stemAt LG {c} c k = none
    unfold stemAt
    rw [dif_neg]
    rw [D.stemSetCap_c]
    simp

theorem embBr_eq (b1 : GBranch D.T1.garden.tree) : embBr D.emb b1.1.2 b1.2 = D.βc b1 := rfl

theorem mem_objSelT (kSel : Fin 2 → Option ℕ) (b1 : GBranch D.T1.garden.tree) :
    b1 ∈ objSelT (J := ({c} : Finset (Fin 2))) D.emb kSel ↔ selCap LG {c} kSel j0 = some (D.βc b1) := by
  unfold objSelT selSetCap
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, D.embBr_eq]
  constructor
  · rintro ⟨j, hj⟩
    by_cases h : j = j0
    · subst h; exact hj
    · rw [D.idx j h, D.selCap_c] at hj
      exact absurd hj (by simp)
  · exact fun h => ⟨j0, h⟩

theorem objSelT_none (kSel : Fin 2 → Option ℕ) (h : selCap LG {c} kSel j0 = none) :
    objSelT (J := ({c} : Finset (Fin 2))) D.emb kSel = ∅ := by
  ext b1
  rw [D.mem_objSelT, h]
  simp

theorem objSelT_some (kSel : Fin 2 → Option ℕ) {vj : GBranch LG.garden.tree}
    (h : selCap LG {c} kSel j0 = some vj) :
    objSelT (J := ({c} : Finset (Fin 2))) D.emb kSel = {D.βc.symm vj} := by
  ext b1
  rw [D.mem_objSelT, h, Finset.mem_singleton]
  constructor
  · intro he
    rw [Option.some.inj he]
    simp
  · intro he
    rw [he]
    simp

/-- The other capped stem vertices of the selected tree (the `chi0(|Ω|/R)` factors). -/
def selF (kSel : Fin 2 → Option ℕ) : Finset (GBranch D.T1.garden.tree) :=
  if (selCap LG {c} kSel j0).isSome then
    D.stem1.filter fun b1 => b1 ∉ objSelT (J := ({c} : Finset (Fin 2))) D.emb kSel
  else ∅

theorem chiD_eq : MkDefs.chiD = FlShell.chiD := rfl

theorem selWeightCap_eq (Rs : Fin 2 → ℝ) (kSel : Fin 2 → Option ℕ) (K : GNode D.T1.garden.tree → Mom d) :
    ((selWeightCap LG {c} (selCap LG {c} kSel) Rs (fun a => K (D.ρ a)) : ℝ) : ℂ) =
      (regSelConst LG c j0 Rs kSel : ℂ) *
        filtWeight (D.selF kSel ∪ objSelT (J := ({c} : Finset (Fin 2))) D.emb kSel)
          (fun b => decide (b ∈ objSelT (J := ({c} : Finset (Fin 2))) D.emb kSel))
          (fun b => if b ∈ objSelT (J := ({c} : Finset (Fin 2))) D.emb kSel then Rs j0 else Rs j0) K := by
  unfold selWeightCap
  rw [fin2_prod _ j0 c D.ne, D.selCap_c]
  simp only [Option.elim, mul_one]
  cases hv : selCap LG {c} kSel j0 with
  | none =>
    rw [D.objSelT_none kSel hv]
    simp [selF, regSelConst, hv, filtWeight]
  | some vj =>
    obtain ⟨v1, rfl⟩ : ∃ v1, vj = D.βc v1 := ⟨D.βc.symm vj, by simp⟩
    have hsel : objSelT (J := ({c} : Finset (Fin 2))) D.emb kSel = {v1} := by
      rw [D.objSelT_some kSel hv, Equiv.symm_apply_apply]
    simp only [selF, regSelConst, hv, Option.isSome_some, if_true, hsel]
    have hF : (D.stem1.filter fun b1 => b1 ∉ ({v1} : Finset (GBranch D.T1.garden.tree))) ∪ {v1} =
        insert v1 (D.stem1.filter fun b1 => b1 ∉ ({v1} : Finset (GBranch D.T1.garden.tree))) := by
      rw [Finset.union_comm, Finset.insert_eq]
    have hn : v1 ∉ D.stem1.filter fun b1 => b1 ∉ ({v1} : Finset (GBranch D.T1.garden.tree)) := by simp
    have hE : (stemSetCap LG {c} j0).erase (D.βc v1) =
        (D.stem1.filter fun b1 => b1 ∉ ({v1} : Finset (GBranch D.T1.garden.tree))).map D.βc.toEmbedding := by
      ext b
      simp only [Finset.mem_erase, Finset.mem_map, Finset.mem_filter, Finset.mem_singleton, D.mem_stem1,
        Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨hne, hb⟩
        refine ⟨D.βc.symm b, ⟨by simpa using hb, ?_⟩, by simp⟩
        intro h
        apply hne
        rw [← h, Equiv.apply_symm_apply]
      · rintro ⟨b1, ⟨hb1, hne⟩, rfl⟩
        exact ⟨fun h => hne (D.βc.injective h), hb1⟩
    unfold filtWeight
    rw [hF, Finset.prod_insert hn, hE, Finset.prod_map, Complex.ofReal_mul, Complex.ofReal_mul,
      Complex.ofReal_prod, mul_assoc]
    congr 1
    congr 1
    · simp only [Finset.mem_singleton, decide_true, if_true, D.omegaNode_βc]
      rfl
    · refine Finset.prod_congr rfl fun b1 hb1 => ?_
      have hne : b1 ≠ v1 := by simpa using (Finset.mem_filter.1 hb1).2
      simp only [Equiv.toEmbedding_apply, Finset.mem_singleton, hne, decide_false, Bool.false_eq_true,
        if_false, D.omegaNode_βc]

/-! ### Anchored pair-type profiles -/

theorem mark1_iff (ℓ : GLeaf D.T1.garden.tree) : D.T1.garden.mark ℓ = none ↔ ℓ.1.2 ≠ X.lonePath := by
  have hm := (decodedTree_decodes X ζ).2.1 ℓ
  change D.T1.garden.mark ℓ = _ at hm
  rw [hm]
  split_ifs with h <;> simp [h]

theorem inputLeaves_filter :
    (inputLeaves LG.garden).filter (fun ℓ => ¬ (ℓ.1.1 ∈ ({c} : Finset (Fin 2)) ∨
      (LG.garden.pair ℓ).1.1 ∈ ({c} : Finset (Fin 2)))) =
      (inputLeaves D.T1.garden).map ⟨D.ιL, D.ιL_injective⟩ := by
  ext ℓ
  simp only [inputLeaves, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk, Finset.mem_singleton]
  rcases D.leaf_cases ℓ with h | h | ⟨ℓ1, hne, rfl⟩
  · subst h
    refine iff_of_false (fun hc => hc.2 (Or.inr (congrArg Prod.fst D.pair_ℓ0))) ?_
    rintro ⟨ℓ1, ⟨-, hm⟩, he⟩
    have := congrArg (fun z : GLeaf LG.garden.tree => z.1.2) he
    exact (D.mark1_iff ℓ1).1 hm this
  · refine iff_of_false (fun hc => hc.2 (Or.inl (congrArg Prod.fst h))) ?_
    rintro ⟨ℓ1, -, he⟩
    have := congrArg (fun z : GLeaf LG.garden.tree => z.1.1) he
    simp only [h, ιL] at this
    exact D.ne this
  · have hs : LG.garden.sign (D.ιL ℓ1).toNode = D.T1.garden.sign ℓ1.toNode := D.sign_ι ℓ1.toNode
    have hp : (LG.garden.pair (D.ιL ℓ1)).1.1 = j0 := by rw [D.pair_ιL ℓ1 hne]; rfl
    rw [hs, hp]
    constructor
    · rintro ⟨⟨h1, -⟩, -⟩
      exact ⟨ℓ1, ⟨h1, (D.mark1_iff ℓ1).2 hne⟩, rfl⟩
    · rintro ⟨ℓ1', h1, hc⟩
      rw [D.ιL_injective hc] at h1
      exact ⟨⟨h1.1, D.plain _⟩, fun h => h.elim (fun h => D.ne h) (fun h => D.ne h)⟩

theorem leafProdCap_eq (h : ℕ → Fin 2 → Fin 2 → Mom d → ℝ) (K : GNode D.T1.garden.tree → Mom d) :
    ((leafProdCap LG {c} h (fun a => K (D.ρ a)) : ℝ) : ℂ) =
      ∏ ℓ ∈ inputLeaves D.T1.garden, (regH1 LG j0 h ℓ.1 (K ℓ.toNode) : ℂ) := by
  unfold leafProdCap
  rw [Complex.ofReal_prod]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one]
  rw [← Finset.prod_filter_not_mul_prod_filter (inputLeaves LG.garden)
    (fun ℓ => ℓ.1.1 ∈ ({c} : Finset (Fin 2)) ∨ (LG.garden.pair ℓ).1.1 ∈ ({c} : Finset (Fin 2)))]
  rw [Finset.prod_congr rfl (fun ℓ hℓ => if_neg (Finset.mem_filter.1 hℓ).2),
    Finset.prod_congr rfl (fun ℓ hℓ => if_pos (Finset.mem_filter.1 hℓ).2), Finset.prod_const_one, mul_one,
    D.inputLeaves_filter, Finset.prod_map]
  refine Finset.prod_congr rfl fun ℓ1 _ => ?_
  simp only [Function.Embedding.coeFn_mk, D.ιL_toNode, D.ρ_ι]
  rfl

theorem leafwise_H1 {p : ℕ} (hlay : ∀ a, LG.layer a ≤ p) (h : ℕ → Fin 2 → Fin 2 → Mom d → ℝ) (b : NNReal)
    (hb : ∀ q ≤ p, ∀ j j', SNormR (40 * d) (40 * d) (h q j j') ≤ ENNReal.ofReal (b : ℝ)) :
    LeafwiseControlled D.T1 (regH1 LG j0 h) (fun _ => b) := by
  intro ℓ _
  have hn : (j0, ℓ.1.2).2 ∈ (LG.garden.tree (j0, ℓ.1.2).1).nodes := (D.ι ℓ.toNode).2
  show SNormR (40 * d) (40 * d) (typeProfiles LG h (j0, ℓ.1.2)) ≤ _
  unfold typeProfiles
  rw [dif_pos hn]
  exact hb _ (hlay _) _ _

/-! ### The dagger -/

theorem isCapFlower_iff (ℓ : GLeaf LG.garden.tree) : IsCapFlower LG {c} ℓ ↔ ℓ = D.ℓ0 := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases D.leaf_cases ℓ with h | h | ⟨ℓ1, hne, rfl⟩
    · exact h
    · exact absurd (by rw [Finset.mem_singleton]; exact congrArg Prod.fst h) h1
    · rw [D.pair_ιL ℓ1 hne] at h2
      exact absurd (Finset.mem_singleton.1 h2) D.ne
  · rintro rfl
    refine ⟨fun h => D.ne (Finset.mem_singleton.1 h), ?_⟩
    rw [Finset.mem_singleton]
    exact congrArg Prod.fst D.pair_ℓ0

theorem capFP_iff (b : GBranch LG.garden.tree) : IsCapFlowerParent LG {c} b ↔ b.IsParentOf D.ℓ0 := by
  constructor
  · rintro ⟨ℓ, hℓ, hp⟩
    rwa [(D.isCapFlower_iff ℓ).1 hℓ] at hp
  · exact fun hp => ⟨D.ℓ0, (D.isCapFlower_iff _).2 rfl, hp⟩

/-- The dagger indicator, on the paired tree. -/
def ind1 (dag : Option (Fin 2 → Fin 3 → Mom d)) (K : GNode D.T1.garden.tree → Mom d) : ℝ :=
  dag.elim 1 fun cs => sibWeightCap LG {c} cs (fun a => K (D.ρ a))

theorem parentOf_ℓ0 {b : GBranch LG.garden.tree} (hb : b.IsParentOf D.ℓ0) :
    b.1.1 = j0 ∧ ∃ i0 : Fin 3, X.lonePath = b.1.2 ++ [i0] := ⟨hb.1.symm, hb.2⟩

theorem ρ_child {b : GBranch LG.garden.tree} (i : Fin 3) :
    (D.ρ (b.child i)).1 = ((0 : Fin 1), b.1.2 ++ [i]) :=
  D.ρ_val _ (D.branch_j0 b)

theorem ind1_01 (dag : Option (Fin 2 → Fin 3 → Mom d)) (K : GNode D.T1.garden.tree → Mom d) :
    0 ≤ D.ind1 dag K ∧ D.ind1 dag K ≤ 1 := by
  cases dag with
  | none => exact one01
  | some cs =>
    show 0 ≤ sibWeightCap LG {c} cs (fun a => K (D.ρ a)) ∧ sibWeightCap LG {c} cs (fun a => K (D.ρ a)) ≤ 1
    unfold sibWeightCap
    refine prod01 Finset.univ _ ?_
    intro b _
    refine ite01 ?_ one01
    refine prod01 Finset.univ _ ?_
    intro i _
    exact ite01 one01 (ite01 one01 zero01)

theorem ind1_congr (dag : Option (Fin 2 → Fin 3 → Mom d)) (K K' : GNode D.T1.garden.tree → Mom d)
    (hK : ∀ a : GNode D.T1.garden.tree, a.1.1.val = 0 → a.1.2 ≠ [] → a.1.2.dropLast = X.lonePath.dropLast →
      K a = K' a) : D.ind1 dag K = D.ind1 dag K' := by
  cases dag with
  | none => simp only [ind1, Option.elim_none]
  | some cs =>
    show sibWeightCap LG {c} cs (fun a => K (D.ρ a)) = sibWeightCap LG {c} cs (fun a => K' (D.ρ a))
    unfold sibWeightCap
    refine Finset.prod_congr rfl fun b _ => ?_
    split_ifs with hfp
    · obtain ⟨-, i0, hi0⟩ := D.parentOf_ℓ0 ((D.capFP_iff b).1 hfp)
      refine Finset.prod_congr rfl fun i _ => ?_
      have hk : K (D.ρ (b.child i)) = K' (D.ρ (b.child i)) := by
        refine hK _ rfl ?_ ?_
        · rw [D.ρ_child]; simp
        · rw [D.ρ_child, hi0]; simp
      simp only [hk]
    · rfl

theorem termChild_ind1 (dag : Option (Fin 2 → Fin 3 → Mom d)) : TermChildIndicator X (D.ind1 dag) :=
  ⟨fun K => D.ind1_01 dag K, fun K K' hK => D.ind1_congr dag K K' hK⟩

/-! ### The removed phase -/

omit D in
theorem offFactor_congr (L γ δ : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (dag : Bool)
    (K K' : GNode LG.garden.tree → Mom d)
    (hK : ∀ b, IsCapFlowerParent LG {c} b → K b.toNode = K' b.toNode ∧ ∀ i, K (b.child i) = K' (b.child i)) :
    offFactor L γ δ LG.garden (offCap LG {c} dag) fix K = offFactor L γ δ LG.garden (offCap LG {c} dag) fix K' := by
  unfold offFactor offCap
  split_ifs
  · refine Finset.prod_congr rfl fun b hb => ?_
    obtain ⟨h0, hi⟩ := hK b (Finset.mem_filter.1 hb).2
    unfold omegaNode
    rw [h0, hi 0, hi 1, hi 2]
  · rfl

theorem lone_coset (L : ℝ) (k₀ : Mom d) (κ : GenDecoration D.T1.garden d (fun _ => 0) 0) :
    cosetDecoration D.T1.garden L k₀ κ.1 D.lone1 = k₀ := by
  show k₀ + latticePoint L (κ.1 D.lone1) = k₀
  rw [D.lone1_eq_root κ.2.1, κ.2.2.1 0, WaveTurbulence.Links.latticePoint_zero, add_zero]

/-- On the dagger support, the flower parent and its children carry fixed momenta, so the removed phase is
constant there. -/
theorem offFactor_const (L γ δ : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    (cs : Fin 2 → Fin 3 → Mom d) (κ κ' : GenDecoration D.T1.garden d (fun _ => 0) 0)
    (h1 : D.ind1 (some cs) (cosetDecoration D.T1.garden L k₀ κ.1) ≠ 0)
    (h2 : D.ind1 (some cs) (cosetDecoration D.T1.garden L k₀ κ'.1) ≠ 0) :
    offFactor L γ δ LG.garden (offCap LG {c} true) fix (fun a => cosetDecoration D.T1.garden L k₀ κ.1 (D.ρ a)) =
      offFactor L γ δ LG.garden (offCap LG {c} true) fix
        (fun a => cosetDecoration D.T1.garden L k₀ κ'.1 (D.ρ a)) := by
  -- children of a flower parent on the dagger support
  have hchild : ∀ (κ0 : GenDecoration D.T1.garden d (fun _ => 0) 0),
      D.ind1 (some cs) (cosetDecoration D.T1.garden L k₀ κ0.1) ≠ 0 →
      ∀ b, IsCapFlowerParent LG {c} b → ∀ i : Fin 3,
        cosetDecoration D.T1.garden L k₀ κ0.1 (D.ρ (b.child i)) =
          if D.ρ (b.child i) = D.lone1 then k₀ else cs j0 i := by
    intro κ0 hne b hb i
    obtain ⟨hbj, i0, hi0⟩ := D.parentOf_ℓ0 ((D.capFP_iff b).1 hb)
    split_ifs with hl
    · rw [hl]; exact D.lone_coset L k₀ κ0
    · unfold ind1 sibWeightCap at hne
      simp only [Option.elim] at hne
      have hb' := Finset.prod_ne_zero_iff.1 hne b (Finset.mem_univ _)
      rw [if_pos hb] at hb'
      have hi := Finset.prod_ne_zero_iff.1 hb' i (Finset.mem_univ _)
      have hnf : ¬ ∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG {c} ℓ ∧ ℓ.toNode = b.child i := by
        rintro ⟨ℓ, hℓ, he⟩
        rw [(D.isCapFlower_iff ℓ).1 hℓ] at he
        apply hl
        rw [← he, D.ρ_ℓ0]
      rw [if_neg hnf] at hi
      split_ifs at hi with he
      · rw [he, hbj]
      · exact absurd rfl hi
  refine offFactor_congr L γ δ fix true _ _ fun b hb => ?_
  have hc : ∀ i, cosetDecoration D.T1.garden L k₀ κ.1 (D.ρ (b.child i)) =
      cosetDecoration D.T1.garden L k₀ κ'.1 (D.ρ (b.child i)) := fun i => by
    rw [hchild κ h1 b hb i, hchild κ' h2 b hb i]
  refine ⟨?_, hc⟩
  have d1 := (isDecoration_coset D.T1.garden L k₀ κ.2.1).1 (D.βc.symm b)
  have d2 := (isDecoration_coset D.T1.garden L k₀ κ'.2.1).1 (D.βc.symm b)
  simp only [← D.ρ_βc_toNode, ← D.ρ_βc_child] at d1 d2
  show cosetDecoration D.T1.garden L k₀ κ.1 (D.ρ b.toNode) = cosetDecoration D.T1.garden L k₀ κ'.1 (D.ρ b.toNode)
  rw [d1, d2, hc 0, hc 1, hc 2]

end CapG

end WaveTurbulence.Flower.ProtWhole
