/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Statement
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Canon
public import WaveTurbulence.Foundations.Spine.PL234Draft.SliceApp
public import WaveTurbulence.Foundations.Spine.LeafwiseAt

/-! # The layer-uniform leafwise gates `CoherentGateH`, `IncoherentGateH` (V5 part C, R45)

For an arbitrary layer-indexed family `h : ℕ → Mom d → ℝ` with `SNormR (40d)(40d) (h r) ≤ Bh r` (`r ≤ p`), the
coherent approximation (TARGET Prop 6.1) and the incoherent decay (B2.2), in the form `K*_Q`, `K*_T` of `h`, with the
cost `layerCost Bh LG = ∏_{leaves ℓ} Bh (layer ℓ)` multiplying every bound.  They are derived (not assumed) from
lg-spine-u's `LeafwiseCoherentApproximationAt` and `LeafwiseIncoherentDecayAt` at the layer profiles
`H z = h (layer z)`, using `PL234.KQstar_eq_coupleLeaves` (kernel) and `PL234.sourceCouple_eq` (approximation, ported
from PL234 `SliceApp` into `VineEstS5C/Copied/PL234Draft`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.PL234 TTree WaveTurbulence.Reg WaveTurbulence.Links
open scoped ENNReal

/-- The layer cost of a layered garden: the product of `Bh (layer ℓ)` over its input leaves. -/
noncomputable def layerCost {w : ℕ} (Bh : ℕ → ℝ) (LG : LayeredGarden w) : ℝ :=
  ∏ ℓ ∈ inputLeaves LG.garden, Bh (LG.layer ℓ.toNode)

/-- The size hypothesis on the layer family for layers `≤ p`. -/
def ProfileBound (P : WTParams) (h : ℕ → Mom P.d → ℝ) (Bh : ℕ → ℝ) (p : ℕ) : Prop :=
  ∀ r ≤ p, 0 ≤ Bh r ∧ SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal (Bh r)

theorem layerCost_nonneg {w : ℕ} {Bh : ℕ → ℝ} (LG : LayeredGarden w) (hB : ∀ x, 0 ≤ Bh (LG.layer x)) :
    0 ≤ layerCost Bh LG :=
  Finset.prod_nonneg fun _ _ => hB _

/-- The nodes of a coherent couple carrier are in layers `≤ p`. -/
theorem coherentCouple_layer_le {p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2} (hqq : q' ≤ q) (hqp : q ≤ p)
    (hcoh : IsCoherentCoupleAt p q q' Q LG) (z : GNode LG.garden.tree) : LG.layer z ≤ p := by
  have hQ := hcoh.2.1
  cases Q with
  | triv => rw [layers_type1 hqq hcoh rfl z]; omega
  | type1 c Q₁ Q₂ Q₃ => rw [layers_type1 hqq hcoh rfl z]; omega
  | type2 Xp Xm Qlp =>
    have F := cohFacts_of_coherent hqq hqp hcoh
    rw [← layerAt_node]
    have ha := addrExt_mem_cplNodes hQ ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) z
    have hae : addrExt (if z.1.1 = 0 then ((0 : Fin 2), ([] : Path)) else ((1 : Fin 2), ([] : Path))) z.1.2 =
        z.1 := by
      obtain ⟨⟨j, q⟩, _⟩ := z
      fin_cases j <;> simp [addrExt]
    rw [hae] at ha
    rcases mem_cplNodes_type2.mp ha with h | h | h
    · exact F.high _ h
    · rw [F.minus _ h]; omega
    · rw [F.lp _ h]; omega

/-- The nodes of a coherent tree carrier are in layers `≤ q`. -/
theorem coherentTree_layer_le {p q q' : ℕ} {X : RegChain} {LG : LayeredGarden 1} (hqq : q' ≤ q)
    (hcoh : IsCoherentTreeAt p q q' X LG) (z : GNode LG.garden.tree) : LG.layer z ≤ q := by
  have F := treeCohFacts_of_coherent hcoh
  rw [← layerAt_node]
  rcases addrExt_mem_chainNodes F.dec ((0 : Fin 1), []) z with h | h
  · have e : addrExt ((0 : Fin 1), ([] : Path)) z.1.2 = z.1 := by
      obtain ⟨⟨j, q⟩, _⟩ := z
      fin_cases j
      simp [addrExt]
    rw [e] at h
    exact F.high _ h
  · have e : z.1 = ((0 : Fin 1), X.lonePath) := Prod.ext (Subsingleton.elim _ _) h
    rw [e, F.lone]
    exact hqq

/-- The leafwise control of the layer profiles of `h` on a garden all of whose layers are `≤ p`. -/
theorem controlled_layerProfiles {P : WTParams} {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ}
    (hB : ProfileBound P h Bh p) {w : ℕ} (LG : LayeredGarden w) (hlay : ∀ x, LG.layer x ≤ p) :
    LeafwiseControlled LG (PL234.layerProfiles LG h) (fun z => Real.toNNReal (Bh (layerAt LG z))) := by
  intro ℓ hℓ
  have hle : layerAt LG ℓ.1 ≤ p := (layerAt_node LG ℓ.toNode).le.trans (hlay _)
  obtain ⟨h0, h1⟩ := hB _ hle
  rw [Real.coe_toNNReal _ h0]
  exact h1

theorem leafSizeProduct_eq_layerCost {P : WTParams} {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ}
    (hB : ProfileBound P h Bh p) {w : ℕ} (LG : LayeredGarden w) (hlay : ∀ x, LG.layer x ≤ p) :
    leafSizeProduct LG (fun z => Real.toNNReal (Bh (layerAt LG z))) = layerCost Bh LG := by
  unfold leafSizeProduct layerCost
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  have hle : layerAt LG ℓ.1 ≤ p := (layerAt_node LG ℓ.toNode).le.trans (hlay _)
  rw [Real.coe_toNNReal _ (hB _ hle).1]
  exact congrArg Bh (layerAt_node LG ℓ.toNode)

/-- **The coherent gate for the layer family `h` with cost `layerCost Bh`** (TARGET Prop 6.1, leafwise, layer-uniform).
The approximation is `SourceApp.couple`/`SourceApp.tree` of `h`. -/
def CoherentGateH (P : WTParams) : Prop :=
  ∀ (h : ℕ → Mom P.d → ℝ) (Bh : ℕ → ℝ) (p : ℕ), p < P.D → ProfileBound P h Bh p →
  ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    (∀ (Q : RegCpl) (LG : LayeredGarden 2) (q q' : ℕ),
      q' ≤ q → q ≤ p → Q.size = 2 * n → IsCoherentCoupleAt p q q' Q LG →
      (XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => KQstar P.L P.γ P.δ h LG (ts 0) (ts 1) k -
          SourceApp.couple P.δ h LG Q q q' (ts 0) (ts 1) k) ≤
          regBound P n 1 * ENNReal.ofReal (layerCost Bh LG)) ∧
      (Q.dominant = false → ∀ ts ∈ timeBox q q', ∀ k,
        SourceApp.couple P.δ h LG Q q q' (ts 0) (ts 1) k = 0) ∧
      LeafwiseSeparated P n (30 * P.d) (timeBox q q')
        (fun ts k => SourceApp.couple P.δ h LG Q q q' (ts 0) (ts 1) k) (layerCost Bh LG)) ∧
    (∀ (X : RegChain) (LG : LayeredGarden 1) (q q' : ℕ),
      q' ≤ q → q ≤ p → X.size = 2 * n → IsCoherentTreeAt p q q' X LG →
      (XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => KTstar P.L P.γ P.δ h LG (ts 0) (ts 1) k -
          SourceApp.tree P.δ h LG X q q' (ts 0) (ts 1) k) ≤
          regBound P n 1 * ENNReal.ofReal (layerCost Bh LG)) ∧
      (X.dominant = false → ∀ ts ∈ timeBoxGt q q', ∀ k,
        SourceApp.tree P.δ h LG X q q' (ts 0) (ts 1) k = 0) ∧
      LeafwiseSeparated P n 0 (timeBoxGt q q')
        (fun ts k => SourceApp.tree P.δ h LG X q q' (ts 0) (ts 1) k) (layerCost Bh LG))

/-- **The incoherent gate for the layer family `h` with cost `layerCost Bh`** (B2.2, leafwise, layer-uniform). -/
def IncoherentGateH (P : WTParams) : Prop :=
  ∀ (h : ℕ → Mom P.d → ℝ) (Bh : ℕ → ℝ) (p : ℕ), p < P.D → ProfileBound P h Bh p →
  ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    (∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
      (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q → LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
      1 ≤ LG.incoherency Q.links →
      XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => KQstar P.L P.γ P.δ h LG (ts 0) (ts 1) k) ≤
        regBound P n (LG.incoherency Q.links) * ENNReal.ofReal (layerCost Bh LG)) ∧
    (∀ X : RegChain, X.wf = true → X.size = 2 * n → ∀ LG : LayeredGarden 1,
      X.DecodesTree LG.garden → (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q' ≤ q → q ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q →
      (∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') →
      1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) →
      XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => KTstar P.L P.γ P.δ h LG (ts 0) (ts 1) k) ≤
        regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0))) * ENNReal.ofReal (layerCost Bh LG))

theorem coherentGateH_of {P : WTParams} (hg : LeafwiseCoherentApproximationAt P) : CoherentGateH P := by
  intro h Bh p hp hB n hn
  obtain ⟨hLc, hLt⟩ := hg p hp n hn
  refine ⟨fun Q LG q q' hqq hqp hsize hcoh => ?_, fun X LG q q' hqq hqp hsize hcoh => ?_⟩
  · have hlay := coherentCouple_layer_le hqq hqp hcoh
    have hctl := controlled_layerProfiles hB LG hlay
    have hcost := leafSizeProduct_eq_layerCost hB LG hlay
    obtain ⟨hE, hD, hSp⟩ := hLc Q LG q q' hqq hqp hsize hcoh _ _ hctl
    have hsrc : ∀ ts : Fin 2 → ℝ, ∀ k, SourceApp.couple P.δ h LG Q q q' (ts 0) (ts 1) k =
        LeafApp.coherentCouple P.δ LG (PL234.layerProfiles LG h) Q q q' (ts 0) (ts 1) k :=
      fun ts k => sourceCouple_eq h P.δ hqq hqp hcoh _ _ k
    rw [hcost] at hE hSp
    refine ⟨?_, fun hdom ts hts k => by rw [hsrc]; exact hD hdom ts hts k, ?_⟩
    · have hfun : (fun (ts : Fin 2 → ℝ) (k : Mom P.d) => KQstar P.L P.γ P.δ h LG (ts 0) (ts 1) k -
            SourceApp.couple P.δ h LG Q q q' (ts 0) (ts 1) k) =
          fun (ts : Fin 2 → ℝ) (k : Mom P.d) =>
            (coupleLeaves P.L P.γ P.δ LG (PL234.layerProfiles LG h) (ts 0) (ts 1) k -
              LeafApp.coherentCouple P.δ LG (PL234.layerProfiles LG h) Q q q' (ts 0) (ts 1) k) := by
        funext ts k
        rw [KQstar_eq_coupleLeaves, hsrc]
      rw [hfun]; exact hE
    · obtain ⟨m, J, M, hm, hf, hJ, hM⟩ := hSp
      exact ⟨m, J, M, hm, fun ts hts k => by beta_reduce; rw [hsrc]; exact hf ts hts k, hJ, hM⟩
  · have hlay : ∀ x, LG.layer x ≤ p := fun x => (coherentTree_layer_le hqq hcoh x).trans hqp
    have hctl := controlled_layerProfiles hB LG hlay
    have hcost := leafSizeProduct_eq_layerCost hB LG hlay
    obtain ⟨hE, hD, hSp⟩ := hLt X LG q q' hqq hqp hsize hcoh _ _ hctl
    have hsrc : ∀ ts : Fin 2 → ℝ, ∀ k, SourceApp.tree P.δ h LG X q q' (ts 0) (ts 1) k =
        LeafApp.coherentTree P.δ LG (PL234.layerProfiles LG h) X q q' (ts 0) (ts 1) k :=
      fun ts k => sourceTree_eq h P.δ hqq hcoh _ _ k
    rw [hcost] at hE hSp
    refine ⟨?_, fun hdom ts hts k => by rw [hsrc]; exact hD hdom ts hts k, ?_⟩
    · have hfun : (fun (ts : Fin 2 → ℝ) (k : Mom P.d) => KTstar P.L P.γ P.δ h LG (ts 0) (ts 1) k -
            SourceApp.tree P.δ h LG X q q' (ts 0) (ts 1) k) =
          fun (ts : Fin 2 → ℝ) (k : Mom P.d) => treeLeaves P.L P.γ P.δ LG (PL234.layerProfiles LG h) (ts 0) (ts 1) k -
            LeafApp.coherentTree P.δ LG (PL234.layerProfiles LG h) X q q' (ts 0) (ts 1) k := by
        funext ts k
        rw [KTstar_eq_treeLeaves, hsrc]
      rw [hfun]; exact hE
    · obtain ⟨m, J, M, hm, hf, hJ, hM⟩ := hSp
      exact ⟨m, J, M, hm, fun ts hts k => by beta_reduce; rw [hsrc]; exact hf ts hts k, hJ, hM⟩

theorem incoherentGateH_of {P : WTParams} (hg : LeafwiseIncoherentDecayAt P) : IncoherentGateH P := by
  intro h Bh p hp hB n hn
  obtain ⟨hc, ht⟩ := hg p hp n hn
  refine ⟨fun Q hwf hsize LG hdec hlay q q' hqp hq'p hr0 hr1 hg1 => ?_,
    fun X hwf hsize LG hdec hlay q q' hqq hqp hr0 hlone hg1 => ?_⟩
  · have hctl := controlled_layerProfiles hB LG hlay
    have hcost := leafSizeProduct_eq_layerCost hB LG hlay
    have := hc Q hwf hsize LG hdec hlay q q' hqp hq'p hr0 hr1 hg1 _ _ hctl
    rw [hcost] at this
    have hfun : (fun (ts : Fin 2 → ℝ) (k : Mom P.d) => KQstar P.L P.γ P.δ h LG (ts 0) (ts 1) k) =
        fun (ts : Fin 2 → ℝ) (k : Mom P.d) => coupleLeaves P.L P.γ P.δ LG (PL234.layerProfiles LG h) (ts 0) (ts 1) k := by
      funext ts k; rw [KQstar_eq_coupleLeaves]
    rw [hfun]; exact this
  · have hctl := controlled_layerProfiles hB LG hlay
    have hcost := leafSizeProduct_eq_layerCost hB LG hlay
    have := ht X hwf hsize LG hdec hlay q q' hqq hqp hr0 hlone hg1 _ _ hctl
    rw [hcost] at this
    have hfun : (fun (ts : Fin 2 → ℝ) (k : Mom P.d) => KTstar P.L P.γ P.δ h LG (ts 0) (ts 1) k) =
        fun (ts : Fin 2 → ℝ) (k : Mom P.d) => treeLeaves P.L P.γ P.δ LG (PL234.layerProfiles LG h) (ts 0) (ts 1) k := by
      funext ts k; rw [KTstar_eq_treeLeaves]
    rw [hfun]; exact this

end WaveTurbulence.VineEstS5C
