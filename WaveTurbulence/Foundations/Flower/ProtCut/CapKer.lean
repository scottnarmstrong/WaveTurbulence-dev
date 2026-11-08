/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.Cap

/-! # D2c PROT-CUT: the cap-couple kernel is the paired-tree kernel times one input

* **`CapData.kernelProt_cap`**: `kernelProt LG H m up s fix k = H (0, X.lonePath) k · kernelProt LG1 (capH H)
  (D.capM m) (up ∘ βc) 0 (fix ∘ βc) k`.
* `CapData.exists_of_decodes`; bookkeeping `protSize_cap`, `protIncoh_cap`, `protShape_cap`, `cfg_fix_cap`,
  `cfg_valid_cap`, `hH_cap`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

variable {d : ℕ}

namespace CapData

variable {X : RegChain} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1} (D : CapData X LG LG1)
include D

theorem decBwd_fwd (κ : GenDecoration LG.garden d (fun _ => 0) 0) : D.decBwd (D.decFwd κ) = κ := by
  apply Subtype.ext
  funext a
  show κ.1 (D.ι (D.ρ a)) = κ.1 a
  by_cases h : a.1.1 = 0
  · rw [D.ι_ρ a h]
  · rw [D.ρ_one a h]
    have ha : a.1 = ((1 : Fin 2), []) := D.node_one a h
    have e1 : D.ι D.lone1 = D.ℓ0.toNode := rfl
    have e2 : a = (LG.garden.pair D.ℓ0).toNode := Subtype.ext (ha.trans D.pair_ℓ0.symm)
    rw [e1, e2]
    exact κ.2.1.2 D.ℓ0

theorem decFwd_bwd (κ : GenDecoration LG1.garden d (fun _ => 0) 0) : D.decFwd (D.decBwd κ) = κ := by
  apply Subtype.ext
  funext a
  show κ.1 (D.ρ (D.ι a)) = κ.1 a
  rw [D.ρ_ι]

/-- **Decorations of the cap couple are decorations of the paired tree.** -/
def decEquiv (d : ℕ) : GenDecoration LG.garden d (fun _ => 0) 0 ≃ GenDecoration LG1.garden d (fun _ => 0) 0 :=
  ⟨D.decFwd, D.decBwd, D.decBwd_fwd, D.decFwd_bwd⟩

/-- The multiplier of the paired tree (the cap reads the lone leaf). -/
def capM (m : (GNode LG.garden.tree → Mom d) → ℂ) : (GNode LG1.garden.tree → Mom d) → ℂ :=
  fun K => m (fun a => K (D.ρ a))

theorem coset_cap (L : ℝ) (k : Mom d) (κ : GenDecoration LG.garden d (fun _ => 0) 0) :
    cosetDecoration LG.garden L k κ.1 = fun a => cosetDecoration LG1.garden L k (D.decFwd κ).1 (D.ρ a) := by
  funext a
  unfold cosetDecoration
  congr 2
  exact (congrArg (fun κ' : GenDecoration LG.garden d (fun _ => 0) 0 => κ'.1 a) (D.decBwd_fwd κ)).symm

theorem order_eq : LG.garden.order = LG1.garden.order := by
  simp only [Garden.order, Fin.sum_univ_two, Fin.sum_univ_one, D.tree1, D.tree_eq, TTree.order, add_zero]

theorem zeta_eq : LG.garden.zeta = LG1.garden.zeta := by
  unfold Garden.zeta
  rw [← D.βc.prod_comp]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [D.βc_toNode, D.sign_ι]

theorem epsDec_eq (κ : GenDecoration LG.garden d (fun _ => 0) 0) :
    epsDec LG.garden κ.1 = epsDec LG1.garden (D.decFwd κ).1 :=
  (Equiv.prod_comp D.βc _).symm

theorem phaseProd_eq (L γ δ : ℝ) (K : GNode LG.garden.tree → Mom d) (τ : GBranch LG.garden.tree → ℝ) :
    phaseProd L γ δ LG.garden K τ = phaseProd L γ δ LG1.garden (fun a => K (D.ι a)) (fun b => τ (D.βc b)) := by
  unfold phaseProd
  rw [← D.βc.prod_comp]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [D.βc_toNode, D.sign_ι]
  rfl

theorem isChild_iff (b' b : GBranch LG1.garden.tree) : (D.βc b').IsChildOf (D.βc b) ↔ b'.IsChildOf b :=
  ⟨fun h => ⟨Subsingleton.elim _ _, h.2⟩, fun h => ⟨rfl, h.2⟩⟩

theorem not_loneParent (b : GBranch LG.garden.tree) : ¬ LG.garden.IsLoneParent b := by
  rintro ⟨ℓ, hl, -⟩
  unfold Garden.IsLone at hl
  rw [D.plain ℓ] at hl
  exact absurd hl (by simp)

theorem protTime_cap (L γ δ : ℝ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG up s fix K =
      protTime L γ δ LG1 (fun b => up (D.βc b)) 0 (fun b => fix (D.βc b)) (fun a => K (D.ι a)) := by
  refine protTime_transport L γ δ D.βc (fun _ => rfl) (fun τ => ?_) (fun τ => D.phaseProd_eq L γ δ K τ)
  constructor
  · rintro ⟨hk, -⟩
    refine ⟨fun b => ⟨fun hf => ?_, fun b' hc hor => ?_⟩, fun b _ hf => ?_⟩
    · have := (hk (D.βc b)).1 hf
      simpa only [D.βc_toNode, D.layer_ι] using this
    · exact (hk (D.βc b)).2 (D.βc b') ((D.isChild_iff b' b).2 hc) hor
    · exact ((hk (D.βc b)).1 hf).2.2.1
  · rintro ⟨hk, -⟩
    refine ⟨fun b => ⟨fun hf => ?_, fun b' hc hor => ?_⟩, fun b hl _ => absurd hl (D.not_loneParent b)⟩
    · obtain ⟨b1, rfl⟩ := D.βc.surjective b
      have := (hk b1).1 hf
      simpa only [D.βc_toNode, D.layer_ι] using this
    · obtain ⟨b1, rfl⟩ := D.βc.surjective b
      obtain ⟨b1', rfl⟩ := D.βc.surjective b'
      exact (hk b1).2 b1' ((D.isChild_iff b1' b1).1 hc) hor

/-! ### Input leaves -/

theorem sign_ℓ0 : LG.garden.sign D.ℓ0.toNode = 1 := by
  have hne : LG.garden.pair D.ℓ0 ≠ D.ℓ0 := by
    intro h
    have := congrArg (fun z : GLeaf LG.garden.tree => z.1.1) h
    simp only [D.pair_ℓ0] at this
    exact absurd this (by simp [ℓ0])
  have hs := LG.garden.pair_sign D.ℓ0 hne
  rw [D.pair_ℓ0] at hs
  have h1 : nodeSign LG.garden.sig ((1 : Fin 2), ([] : Path)) = -1 := by
    simp [nodeSign, pathSign, D.sig1']
  rw [h1] at hs
  show nodeSign LG.garden.sig D.ℓ0.1 = 1
  have := congrArg (fun u : ℤˣ => -u) hs
  simpa using this.symm

theorem mark1_iff (ℓ : GLeaf LG1.garden.tree) : LG1.garden.mark ℓ = none ↔ ℓ.1.2 ≠ X.lonePath := by
  rw [D.dec1.2.1 ℓ]
  split_ifs with h <;> simp [h]

theorem inputLeaves_cap : inputLeaves LG.garden =
    insert D.ℓ0 ((inputLeaves LG1.garden).map ⟨D.ιL, D.ιL_injective⟩) := by
  ext ℓ
  simp only [inputLeaves, Finset.mem_insert, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  rcases D.leaf_cases ℓ with h | h | ⟨ℓ1, hne, rfl⟩
  · subst h
    exact iff_of_true ⟨D.sign_ℓ0, D.plain _⟩ (Or.inl rfl)
  · refine iff_of_false (fun hc => ?_) (fun hc => ?_)
    · have hs : LG.garden.sign ℓ.toNode = -1 := by
        show nodeSign LG.garden.sig ℓ.1 = -1
        rw [h]
        simp [nodeSign, pathSign, D.sig1']
      rw [hs] at hc
      exact absurd hc.1 (by decide)
    · rcases hc with hc | ⟨ℓ1, -, hc⟩
      · have := congrArg (fun z : GLeaf LG.garden.tree => z.1.1) hc
        simp only [h, ℓ0] at this
        exact absurd this (by decide)
      · have := congrArg (fun z : GLeaf LG.garden.tree => z.1.1) hc
        simp only [h, ιL] at this
        exact absurd this (by decide)
  · have hs : LG.garden.sign (D.ιL ℓ1).toNode = LG1.garden.sign ℓ1.toNode := D.sign_ι ℓ1.toNode
    rw [hs]
    constructor
    · rintro ⟨h1, -⟩
      exact Or.inr ⟨ℓ1, ⟨h1, (D.mark1_iff ℓ1).2 hne⟩, rfl⟩
    · rintro (hc | ⟨ℓ1', h1, hc⟩)
      · have := congrArg (fun z : GLeaf LG.garden.tree => z.1.2) hc
        exact absurd this hne
      · rw [D.ιL_injective hc] at h1
        exact ⟨h1.1, D.plain _⟩

theorem lone_not_input : D.ℓ0 ∉ (inputLeaves LG1.garden).map ⟨D.ιL, D.ιL_injective⟩ := by
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, inputLeaves, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rintro ⟨ℓ1, ⟨-, hm⟩, h⟩
  have := congrArg (fun z : GLeaf LG.garden.tree => z.1.2) h
  exact (D.mark1_iff ℓ1).1 hm this

theorem prodH_cap (L : ℝ) (H : LeafProfiles 2 d) (k : Mom d) (κ : GenDecoration LG.garden d (fun _ => 0) 0) :
    ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ) =
      (H ((0 : Fin 2), X.lonePath) k : ℂ) *
        ∏ ℓ ∈ inputLeaves LG1.garden, (capH H ℓ.1 (cosetDecoration LG1.garden L k (D.decFwd κ).1 ℓ.toNode) : ℂ) := by
  rw [D.inputLeaves_cap, Finset.prod_insert D.lone_not_input, Finset.prod_map]
  congr 1
  have h0 : κ.1 D.ℓ0.toNode = 0 := by
    rw [κ.2.1.2 D.ℓ0]
    have e : (LG.garden.pair D.ℓ0).toNode = GNode.root LG.garden.tree 1 := Subtype.ext D.pair_ℓ0
    rw [e]
    exact κ.2.2.1 1
  unfold cosetDecoration
  rw [h0, latticePoint_zero, add_zero]
  rfl

/-! ### The kernel -/

theorem summand_cap (L γ δ : ℝ) (H : LeafProfiles 2 d) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k : Mom d)
    (κ : GenDecoration LG.garden d (fun _ => 0) 0) :
    protSummand L γ δ LG H m up s fix k κ = (H ((0 : Fin 2), X.lonePath) k : ℂ) *
      protSummand L γ δ LG1 (capH H) (D.capM m) (fun b => up (D.βc b)) 0 (fun b => fix (D.βc b)) k
        (D.decEquiv d κ) := by
  unfold protSummand
  have hm : m (cosetDecoration LG.garden L k κ.1) = D.capM m (cosetDecoration LG1.garden L k (D.decFwd κ).1) := by
    unfold capM
    rw [D.coset_cap L k κ]
  have ht : protTime L γ δ LG up s fix (cosetDecoration LG.garden L k κ.1) =
      protTime L γ δ LG1 (fun b => up (D.βc b)) 0 (fun b => fix (D.βc b))
        (cosetDecoration LG1.garden L k (D.decFwd κ).1) :=
    D.protTime_cap L γ δ up s fix (cosetDecoration LG.garden L k κ.1)
  have he : D.decEquiv d κ = D.decFwd κ := rfl
  rw [he, hm, D.epsDec_eq κ, ht, D.prodH_cap L H k κ]
  ring

/-- **The cap-couple reduction.** A cap couple's protected kernel is the paired tree's, with the cap read at the
lone leaf, times the input `H (0, X.lonePath) k` of the lone leaf of `X` (sign `+`). -/
theorem kernelProt_cap (L γ δ : ℝ) (H : LeafProfiles 2 d) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k : Mom d) :
    kernelProt L γ δ LG H m up s fix k (fun _ => 0) 0 = (H ((0 : Fin 2), X.lonePath) k : ℂ) *
      kernelProt L γ δ LG1 (capH H) (D.capM m) (fun b => up (D.βc b)) 0 (fun b => fix (D.βc b)) k
        (fun _ => 0) 0 := by
  rw [kernelProt_eq_tsum, kernelProt_eq_tsum, D.order_eq, D.zeta_eq,
    tsum_congr (D.summand_cap L γ δ H m up s fix k), tsum_mul_left,
    (D.decEquiv d).tsum_eq (fun κ1 => protSummand L γ δ LG1 (capH H) (D.capM m) (fun b => up (D.βc b)) 0
      (fun b => fix (D.βc b)) k κ1)]
  ring

/-! ### Bookkeeping -/

omit D in
theorem protSize_cap : protSize X LG = protSize X LG1 := by
  show (RegCpl.type2 X .nil .triv).size = X.size
  simp [RegCpl.size, RegChain.size]

theorem protIncoh_cap : protIncoh X LG = protIncoh X LG1 := by
  show LG.incoherency (capCode X).links = LG1.incoherency (X.treeLinks (LG1.garden.sig 0))
  rw [incoherency_eq_count D.dec, tree_incoherency_eq_count D.dec1, capCode_links, RegChain.treeLinks, D.sig1]
  let φ : Fin 1 × Path → Fin 2 × Path := fun z => ((0 : Fin 2), z.2)
  have hφ : ∀ z q, φ (addrExt z q) = addrExt (φ z) q := by intro z q; simp [φ, addrExt]
  rw [show ((0 : Fin 2), ([] : Path)) = φ ((0 : Fin 1), []) from rfl, chain_linksAt_map X φ hφ 1 ((0 : Fin 1), []),
    List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun l _ => ?_
  simp only [Function.comp_apply, φ, D.layerAt1]

theorem protShape_cap {p : ℕ} (h : ProtShape p X LG) : ProtShape p X LG1 := by
  obtain ⟨hwf, -, -, hlay, hC⟩ := h
  refine ⟨?_, D.dec1, fun a => ?_, fun b hb hpre hne => ?_⟩
  · simp only [RegCpl.wf, Bool.and_eq_true] at hwf
    exact hwf.1.1.1.1
  · rw [← D.layer_ι]
    exact hlay _
  · rw [← D.layer_ι, ← D.βc_toNode]
    exact hC (D.βc b) rfl hpre hne

theorem cfg_fix_cap (cfg : ProtCfg) (s t up : ℝ) :
    (fun b => cfg.fix X s t up (D.βc b)) = cfg.fix X s t up (T := LG1.garden.tree) := by
  funext b
  unfold ProtCfg.fix
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (Fin.val_eq_zero _) h2
  · exact absurd rfl h1
  · rfl

theorem cfg_valid_cap {p : ℕ} (cfg : ProtCfg) (h : cfg.Valid X LG p) : cfg.Valid X LG1 p := by
  cases cfg with
  | termChild i =>
    obtain ⟨h1, h2, b, hb0, hbp, hbl⟩ := h
    refine ⟨h1, h2, D.βc.symm b, by simp, hbp, ?_⟩
    rw [← D.layer_ι, ← D.βc_toNode, D.βc.apply_symm_apply]
    exact hbl
  | _ => exact h

theorem hH_cap (L : ℝ) (H : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|) :
    ∀ ℓ ∈ inputLeaves LG1.garden, ∀ k' : Mom d,
      Summable fun n : Fin d → ℤ => |capH H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ k'
  have hm : D.ιL ℓ ∈ inputLeaves LG.garden := by
    rw [D.inputLeaves_cap]
    exact Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hℓ)
  exact hH _ hm k'

end CapData

/-- **The paired tree of a cap couple exists**: `Reg.decodedTree X 1` with the layers of tree `0`. -/
theorem CapData.exists_of_decodes {X : RegChain} {LG : LayeredGarden 2} (hQ : (capCode X).Decodes LG.garden) :
    ∃ LG1 : LayeredGarden 1, CapData X LG LG1 := by
  have ht0 : LG.garden.tree 0 = X.plug 1 .leaf := by rw [hQ.2.1]; simp [RegCpl.trees]
  let G1 := decodedTree X 1
  have hd1 : X.DecodesTree G1 := decodedTree_decodes X 1
  have hs1 : G1.sig 0 = 1 := decodedTree_sign X 1
  have hT : G1.tree 0 = X.plug 1 .leaf := by have h := hd1.1; rw [hs1] at h; exact h
  have hmem : ∀ (j : Fin 1) (p : Path), p ∈ (G1.tree j).nodes ↔ p ∈ (LG.garden.tree 0).nodes := by
    intro j p; rw [Subsingleton.elim j 0, hT, ht0]
  refine ⟨⟨G1, fun a => layerAt LG ((0 : Fin 2), a.1.2), ⟨fun b i => ?_, fun ℓ => ?_⟩⟩, hQ, hd1, hs1, fun _ => rfl⟩
  · have hb : b.1.2 ∈ (LG.garden.tree 0).branching := by
      have h := b.2; rw [Subsingleton.elim b.1.1 0, hT, ← ht0] at h; exact h
    let B : GBranch LG.garden.tree := ⟨((0 : Fin 2), b.1.2), hb⟩
    have h := LG.isLayering.1 B i
    rw [← layerAt_node LG (B.child i), ← layerAt_node LG B.toNode] at h
    exact h
  · by_cases hl : ℓ.1.2 = X.lonePath
    · have hm : G1.mark ℓ ≠ none := by rw [hd1.2.1 ℓ, if_pos hl]; simp
      rw [(G1.pair_eq_iff ℓ).2 hm]
    · have h1 := hd1.2.2 ℓ hl
      rw [hs1] at h1
      let φ : Fin 1 × Path → Fin 2 × Path := fun z => ((0 : Fin 2), z.2)
      have hφ : ∀ z q, φ (addrExt z q) = addrExt (φ z) q := by intro z q; simp [φ, addrExt]
      have hmap : X.pairsAt 1 ((0 : Fin 2), ([] : Path)) =
          (X.pairsAt 1 ((0 : Fin 1), ([] : Path))).map (fun p => (φ p.1, φ p.2)) :=
        chain_pairsAt_map X φ hφ 1 ((0 : Fin 1), [])
      have key : ∀ u v : Fin 1 × Path, (u, v) ∈ X.pairsAt 1 ((0 : Fin 1), []) →
          layerAt LG (φ u) = layerAt LG (φ v) := by
        intro u v huv
        refine layer_eq_of_decoded_pair hQ (p := (φ u, φ v)) ?_
        rw [capCode_pairs, hmap]
        exact List.mem_append_left _ (List.mem_map.2 ⟨(u, v), huv, rfl⟩)
      rw [mem_symmPairs] at h1
      rcases h1 with h1 | h1
      · exact key _ _ h1
      · exact (key _ _ h1).symm

end WaveTurbulence.Flower.ProtCut
