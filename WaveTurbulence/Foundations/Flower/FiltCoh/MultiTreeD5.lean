/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiPiecesD5
public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiTreeGate

/-! # FILT-COH (D5d-d1): coherent paired trees across layers with the D5 multiplier (bound only)

Milestone (a)'s `MultiTree`/`MultiTreeGate` (bound-only replay of main's `PL2330.tree_lower_bounds30` and the case
split of `tree_err_gt30`) for the multiplied kernel `kernelLeavesW … (d5Mult S ω F ann M Fu Mu)`, from the
single-layer oracle `D5TreeKOracle` (a HYPOTHESIS here). The induction claims quantify over every D5 datum on the
current carrier: a block step (`treeW_block_step`) splits it into the data of the block (`starTop`, `filtTop`) and of
the remainder (`starBot`, `filtBot`), and the star costs split by `prod_mem_glue`. The star cost enters the bound
as the factor `∏_{a ∈ S} max (c a) 0` next to the leaf sizes (`ofReal_mul_prod_ofReal`). -/

public section
open WaveTurbulence.Induct
open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltCoh

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.PL2330 WaveTurbulence.Reg WaveTurbulence.Links

variable {d : ℕ}

/-! ### Star costs and pulled-back data -/

/-- The star product of the target, as one real factor. -/
theorem ofReal_mul_prod_ofReal {ι : Type*} (S : Finset ι) (c : ι → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal x * ∏ a ∈ S, ENNReal.ofReal (c a) = ENNReal.ofReal (x * ∏ a ∈ S, max (c a) 0) := by
  have h1 : ∀ a ∈ S, ENNReal.ofReal (c a) = ENNReal.ofReal (max (c a) 0) := fun a _ => by
    rcases le_total 0 (c a) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  rw [Finset.prod_congr rfl h1, ← ENNReal.ofReal_prod_of_nonneg (fun a _ => le_max_right _ _),
    ← ENNReal.ofReal_mul hx]

theorem starCost_nonneg {ι : Type*} (S : Finset ι) (c : ι → ℝ) : 0 ≤ ∏ a ∈ S, max (c a) 0 :=
  Finset.prod_nonneg fun _ _ => le_max_right _ _

section Mem

variable {w : ℕ} [NeZero w] {G : Garden w} {G₁ : Garden 1} {G₂ : Garden w} {X : RegChain}
  (h : PL234.GlueData G G₁ G₂ X)

theorem mem_filtTop_iff {F : Finset (GBranch G.tree)} {x : GBranch G₁.tree} :
    x ∈ filtTop h F ↔ h.ofSum (.inl x) ∈ F := by
  classical
  simp only [filtTop, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_filtBot_iff {F : Finset (GBranch G.tree)} {y : GBranch G₂.tree} :
    y ∈ filtBot h F ↔ h.ofSum (.inr y) ∈ F := by
  classical
  simp only [filtBot, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The star cost splits over the glue data. -/
theorem starCost_glue (S : Finset (GNode G.tree)) (c : GNode G.tree → ℝ) :
    ∏ a ∈ S, max (c a) 0 =
      (∏ x ∈ starTop h S, max (c (h.ι₁ x)) 0) * ∏ y ∈ starBot h S, max (c (h.ι₂ y)) 0 :=
  prod_mem_glue h S (fun a => max (c a) 0)

end Mem

/-! ### Classes of filter data -/

/-- A class of admissible filter data (the two filter layers `F, M` and `Fu, Mu`) on every garden. -/
abbrev FiltClass : Type := ∀ (w : ℕ) (G : Garden w), Finset (GBranch G.tree) → (GBranch G.tree → ℝ) →
  Finset (GBranch G.tree) → (GBranch G.tree → ℝ) → Prop

/-- Stability of a filter class under the pullbacks to the two pieces of a glue (`filtTop`, `filtBot`). -/
@[expose] def FiltClass.Stable (A : FiltClass) : Prop :=
  ∀ ⦃w : ℕ⦄ [NeZero w] ⦃G : Garden w⦄ ⦃G₁ : Garden 1⦄ ⦃G₂ : Garden w⦄ ⦃X : RegChain⦄
    (hg : PL234.GlueData G G₁ G₂ X) ⦃Fl : Finset (GBranch G.tree)⦄ ⦃M : GBranch G.tree → ℝ⦄
    ⦃Fu : Finset (GBranch G.tree)⦄ ⦃Mu : GBranch G.tree → ℝ⦄, A w G Fl M Fu Mu →
    A 1 G₁ (filtTop hg Fl) (fun x => M (hg.ofSum (.inl x))) (filtTop hg Fu) (fun x => Mu (hg.ofSum (.inl x))) ∧
    A w G₂ (filtBot hg Fl) (fun y => M (hg.ofSum (.inr y))) (filtBot hg Fu) (fun y => Mu (hg.ofSum (.inr y)))

/-- The target's filter class: every filter scale is at least `L`. -/
@[expose] def filtScaled (L : ℝ) : FiltClass :=
  fun _ _ Fl M Fu Mu => (∀ b ∈ Fl, L ≤ M b) ∧ (∀ b ∈ Fu, L ≤ Mu b)

/-- No filters. -/
@[expose] def filtNone : FiltClass := fun _ _ Fl _ Fu _ => Fl = ∅ ∧ Fu = ∅

theorem filtScaled_stable (L : ℝ) : (filtScaled L).Stable := by
  intro w _ G G₁ G₂ X hg Fl M Fu Mu hA
  exact ⟨⟨fun x hx => hA.1 _ ((mem_filtTop_iff hg).1 hx), fun x hx => hA.2 _ ((mem_filtTop_iff hg).1 hx)⟩,
    ⟨fun y hy => hA.1 _ ((mem_filtBot_iff hg).1 hy), fun y hy => hA.2 _ ((mem_filtBot_iff hg).1 hy)⟩⟩

theorem filtTop_empty {w : ℕ} [NeZero w] {G : Garden w} {G₁ : Garden 1} {G₂ : Garden w} {X : RegChain}
    (hg : PL234.GlueData G G₁ G₂ X) : filtTop hg (∅ : Finset (GBranch G.tree)) = ∅ := by
  ext x
  simp only [mem_filtTop_iff, Finset.notMem_empty]

theorem filtBot_empty {w : ℕ} [NeZero w] {G : Garden w} {G₁ : Garden 1} {G₂ : Garden w} {X : RegChain}
    (hg : PL234.GlueData G G₁ G₂ X) : filtBot hg (∅ : Finset (GBranch G.tree)) = ∅ := by
  ext y
  simp only [mem_filtBot_iff, Finset.notMem_empty]

theorem filtNone_stable : filtNone.Stable := by
  intro w _ G G₁ G₂ X hg Fl M Fu Mu hA
  obtain ⟨h1, h2⟩ := hA
  subst h1 h2
  exact ⟨⟨filtTop_empty hg, filtTop_empty hg⟩, ⟨filtBot_empty hg, filtBot_empty hg⟩⟩

/-- `D5TreeKOracle` for the filter data of a class `A` (`D5TreeKOracle` is the class `filtScaled L`). -/
@[expose] def D5TreeKOracleA (A : FiltClass) (d : ℕ) (L γ δ θ : ℝ) (Nmax : ℕ) (C : ℝ) : Prop :=
  ∀ (r q'' n : ℕ), n ≤ Nmax → ∀ X : RegChain, q'' ≤ r → X.wf = true → X.size = 2 * n →
    ∀ LG : LayeredGarden 1, X.DecodesTree LG.garden →
    (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r) →
    ∀ (H : LeafProfiles 1 d) (B : (Fin 1 × Path) → NNReal), LeafwiseControlled LG H B →
    ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
      (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, IncTop.StarPresented (30 * d) (ω a) (cω a)) →
    ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
      (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ),
      A 1 LG.garden F M Fu Mu →
    XNormRestr θ (30 * d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
        (d5Mult S ω F ann M Fu Mu)) ≤
      ENNReal.ofReal (C * (C * δ) ^ n * leafSizeProduct LG B) * ∏ a ∈ S, ENNReal.ofReal (cω a)

theorem D5TreeKOracle.toScaled {L γ δ θ : ℝ} {Nmax : ℕ} {C : ℝ} (O : D5TreeKOracle d L γ δ θ Nmax C) :
    D5TreeKOracleA (filtScaled L) d L γ δ θ Nmax C :=
  fun r q'' n hn X hq hwf hsz LG hX hlay H B hH S ω cω hp F ann M Fu Mu hA =>
    O r q'' n hn X hq hwf hsz LG hX hlay H B hH S ω cω hp F ann M hA.1 Fu Mu hA.2

/-- The tree oracle in the real form used by the induction. -/
theorem treeOracle_real {L γ δ θ : ℝ} {Nmax : ℕ} {C : ℝ} {A : FiltClass} (O : D5TreeKOracleA A d L γ δ θ Nmax C)
    (hC : 1 ≤ C)
    (hδ : 0 ≤ δ) {r q'' n : ℕ} (hn : n ≤ Nmax) (X : RegChain) (hq : q'' ≤ r) (hwf : X.wf = true)
    (hsz : X.size = 2 * n) (LG : LayeredGarden 1) (hX : X.DecodesTree LG.garden)
    (hlay : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r)
    (H : LeafProfiles 1 d) (B : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H B)
    (Sst : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (c : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ Sst, IncTop.StarPresented (30 * d) (ω a) (c a))
    (Fl : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hA : A 1 LG.garden Fl M Fu Mu) :
    XNormRestr θ (30 * d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => treeKW L γ δ LG H (d5Mult Sst ω Fl ann M Fu Mu) (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (C * (C * δ) ^ n * (leafSizeProduct LG B * ∏ a ∈ Sst, max (c a) 0)) := by
  have hβ0 : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hC0 : 0 ≤ C := by linarith
  have h := O r q'' n hn X hq hwf hsz LG hX hlay H B hH Sst ω c hpres Fl ann M Fu Mu hA
  rw [ofReal_mul_prod_ofReal _ _ (by positivity)] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  ring

section Induction

variable {L γ δ θ : ℝ} {Nmax : ℕ} {C : ℝ} {A : FiltClass} (O : D5TreeKOracleA A d L γ δ θ Nmax C) (hAst : A.Stable) (hC : 1 ≤ C)
  (hd : 1 ≤ d) (hL : 1 ≤ L) (hθ0 : 0 ≤ θ) (hδ : 0 ≤ δ)
  {LG : LayeredGarden 1} (H : LeafProfiles 1 d) (Bd : (Fin 1 × Path) → NNReal)
  {X₀ : RegChain} {q' q : ℕ} (F : TreeCohFacts LG X₀ q' q) (hqq : q' ≤ q)
  (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox)

include O hAst hC hd hL hθ0 hδ F hqq hT'

/-- **The lower multiplied kernels of a tree**, by induction over the blocks of its chain, for every D5 datum on
the current carrier, with `G = K_tr(θ) · cLeib · C²`. -/
theorem tree_lower_kernelW : ∀ (m : ℕ) (R Y : RegChain) (LG' : LayeredGarden 1), X₀ = appendChain R Y →
    Y.size = 2 * m → m ≤ Nmax → TreeLowState LG H Bd R.lonePath Y LG' →
    ∀ (Sst : Finset (GNode LG'.garden.tree)) (ω : GNode LG'.garden.tree → IncTop.Star d → ℂ)
      (c : GNode LG'.garden.tree → ℝ), (∀ a ∈ Sst, IncTop.StarPresented (30 * d) (ω a) (c a)) →
    ∀ (Fl : Finset (GBranch LG'.garden.tree)) (ann : GBranch LG'.garden.tree → Bool)
      (M : GBranch LG'.garden.tree → ℝ) (Fu : Finset (GBranch LG'.garden.tree)) (Mu : GBranch LG'.garden.tree → ℝ),
      A 1 LG'.garden Fl M Fu Mu →
    rN θ (30 * d) 0 T' (fun ts k =>
        treeKW L γ δ LG' (fun z => H (botAddr R.lonePath z)) (d5Mult Sst ω Fl ann M Fu Mu)
          ((layerAt LG ((0 : Fin 1), R.lonePath) : ℝ) + 1) (ts 1) k) ≤
        ENNReal.ofReal ((Ktr θ * cLeib d (30 * d) * C ^ 2) * ((Ktr θ * cLeib d (30 * d) * C ^ 2) * δ) ^ m *
          (leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) * ∏ a ∈ Sst, max (c a) 0)) := by
  have _hqq' := hqq
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro R Y LG' hXp hsize hmN S Sst ω c hpres Fl ann M Fu Mu hA
  have hΛ : 30 * d ≠ 0 := by omega
  have hC0 : 0 ≤ C := by linarith
  have hK1 : 1 ≤ Ktr θ := one_le_Ktr hθ0
  have hK0 : 0 ≤ Ktr θ := Ktr_nonneg _
  have hLc : 1 ≤ cLeib d (30 * d) := one_le_cLeib hd _
  set G := Ktr θ * cLeib d (30 * d) * C ^ 2 with hGdef
  have hCG : C ≤ G := by
    have h1 : 1 * 1 * C ^ 1 ≤ Ktr θ * cLeib d (30 * d) * C ^ 2 :=
      mul_le_mul (mul_le_mul hK1 hLc zero_le_one (by linarith)) (pow_le_pow_right₀ hC (by norm_num))
        (by positivity) (by positivity)
    simpa using h1
  have hG0 : 0 ≤ G := hC0.trans hCG
  have hβ0 : 0 ≤ leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) * ∏ a ∈ Sst, max (c a) 0 :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg _ _)
  set π := R.lonePath with hπ
  set ζ := LG.garden.sig 0 with hζ
  set u := layerAt LG ((0 : Fin 1), π) with hu
  have hYwf := F.wf_suffix hXp
  have hEmb := F.emb_suffix hXp
  have hPL := F.pl_suffix hXp
  have hlone := F.lone_suffix hXp
  have hroot : Y ≠ .nil → ((0 : Fin 1), π) ∈ chainNodesSet Y ζ ((0 : Fin 1), π) := fun hYn => by
    cases Y with
    | nil => exact absurd rfl hYn
    | pair m' Qr' Qg' inner' rest' => exact PL234.root_mem_chainNodesSet _ _ _ _ _ _ _
  have hnil : Y = .nil → u = q' := fun hYn => by
    rw [hYn] at hlone
    simpa [RegChain.lonePath, addrExt] using hlone
  have hqu : q' ≤ u := by
    by_cases hYn : Y = .nil
    · rw [hnil hYn]
    · exact F.low _ (TreeCohFacts.sub_suffix hXp (hroot hYn))
  set B := takeLayer LG ((0 : Fin 1), π) u Y with hBdef
  set D := dropLayer LG ((0 : Fin 1), π) u Y with hDdef
  have hXe : appendChain B D = Y := appendChain_take_drop LG _ u Y
  have hTA : TopAll LG u ((0 : Fin 1), π) B := topAll_takeLayer LG u _ Y
  have hEmbBD : ChainEmb LG.garden (appendChain B D) ζ ((0 : Fin 1), π) .leaf := by rw [hXe]; exact hEmb
  have hPLBD : ChainPairLayers LG (appendChain B D) ζ ((0 : Fin 1), π) := by rw [hXe]; exact hPL
  have hBlay : ∀ z ∈ chainNodesSet B ζ ((0 : Fin 1), π), layerAt LG z = u :=
    chainNodes_layer_of_topAll (chainEmb_append_left hEmbBD) (chainPairLayers_append_left LG B D ζ _ hPLBD) hTA
  by_cases hDn : D = .nil
  · -- the base: a single block in layer `u`, with the lone leaf in layer `q'`
    have hYB : Y = B := by rw [← hXe, hDn]; exact appendChain_nil_right B
    have hTAY : TopAll LG u ((0 : Fin 1), π) Y := by rw [hYB]; exact hTA
    have hYlay : ∀ z ∈ chainNodesSet Y ζ ((0 : Fin 1), π), layerAt LG z = u :=
      chainNodes_layer_of_topAll hEmb hPL hTAY
    have hlay' : ∀ a : GNode LG'.garden.tree, LG'.layer a = if a.1.2 = Y.lonePath then q' else u := by
      intro a
      rw [← layerAt_node, S.lay]
      have hba : botAddr π a.1 = addrExt ((0 : Fin 1), π) a.1.2 := by
        obtain ⟨⟨j, p⟩, _⟩ := a
        fin_cases j
        simp [botAddr, addrExt]
      rw [hba]
      split_ifs with hl
      · rw [hl]
        exact hlone
      · rcases addrExt_mem_chainNodes S.dec ((0 : Fin 1), π) a with h | h
        · rw [S.sig] at h
          exact hYlay _ h
        · exact absurd h hl
    have hE := treeOracle_real O hC hδ hmN Y hqu hYwf hsize LG' S.dec hlay' _ _ S.ctrl Sst ω c hpres
      Fl ann M Fu Mu hA
    have hEb := treeKW_bottom_kernel hd hL hθ0 hqu S.dec S.ctrl _ (norm_d5Mult_le Sst ω c hpres Fl ann M Fu Mu)
      hE T' b₀ hT'
    refine hEb.trans (ENNReal.ofReal_le_ofReal ?_)
    calc Ktr θ * (C * (C * δ) ^ m * (leafSizeProduct LG' (fun z => Bd (botAddr π z)) * ∏ a ∈ Sst, max (c a) 0))
        = (Ktr θ * C) * (C * δ) ^ m *
            (leafSizeProduct LG' (fun z => Bd (botAddr π z)) * ∏ a ∈ Sst, max (c a) 0) := by ring
      _ ≤ G * (G * δ) ^ m * (leafSizeProduct LG' (fun z => Bd (botAddr π z)) * ∏ a ∈ Sst, max (c a) 0) := by
          apply mul_le_mul_of_nonneg_right _ hβ0
          apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCG hδ) m)
            (by positivity) hG0
          calc Ktr θ * C = Ktr θ * 1 * C ^ 1 := by ring
            _ ≤ Ktr θ * cLeib d (30 * d) * C ^ 2 :=
                mul_le_mul (mul_le_mul_of_nonneg_left hLc hK0) (pow_le_pow_right₀ hC (by norm_num))
                  (by positivity) (by positivity)
  · -- the step: remove the top block
    have hYn : Y ≠ .nil := by
      intro h
      apply hDn
      rw [hDdef, h]
      rfl
    have hnode : (addrExt ((0 : Fin 1), π) B.lonePath).2 ∈
        (LG.garden.tree (addrExt ((0 : Fin 1), π) B.lonePath).1).nodes := by
      have ht : (LG.garden.tree ((0 : Fin 1), π).1).subtreeAt ((0 : Fin 1), π).2 =
          B.plug ζ (D.plug ζ .leaf) := by
        rw [hEmbBD.tree, appendChain_plug]
      exact (node_iff_of_subtree hEmb.node ht B.lonePath).1.mpr (lonePath_mem_plug B ζ _)
    have hle : layerAt LG ((0 : Fin 1), π ++ B.lonePath) ≤ u :=
      layerAt_le_of_under LG hEmb.node hnode (under_ext _ _)
    have hlt : layerAt LG ((0 : Fin 1), π ++ B.lonePath) < u :=
      lt_of_le_of_ne hle (layer_drop_ne LG u Y _ hDn)
    obtain ⟨G₁, LG'', hdec₁, -, hlay₁, hctrl₁, S'', hβ, hg, hK⟩ :=
      treeW_block_step S L γ δ hd hL hYwf hDn hlt hBlay
    -- sizes
    have hwfBD : (appendChain B D).wf = true := by rw [hXe]; exact hYwf
    rw [appendChain_wf, Bool.and_eq_true] at hwfBD
    have hsz : Y.size = B.size + D.size := by rw [← hXe, appendChain_size]
    obtain ⟨nB, hnB⟩ := size_even_chain B
    obtain ⟨m₂, hm₂⟩ := size_even_chain D
    have hB2 := two_le_size_of_ne_nil B (takeLayer_ne_nil LG Y _ hYn)
    have hBsize : B.size = 2 * nB := by omega
    have hsz₂ : D.size = 2 * m₂ := by omega
    have hmm : m = nB + m₂ := by omega
    have hnB1 : 1 ≤ nB := by omega
    -- the data of the two pieces
    set mT := d5Mult (starTop hg Sst) (fun x => ω (hg.ι₁ x)) (filtTop hg Fl) (fun x => ann (hg.ofSum (.inl x)))
      (fun x => M (hg.ofSum (.inl x))) (filtTop hg Fu) (fun x => Mu (hg.ofSum (.inl x))) with hmT
    set mB := d5Mult (starBot hg Sst) (fun y => ω (hg.ι₂ y)) (filtBot hg Fl) (fun y => ann (hg.ofSum (.inr y)))
      (fun y => M (hg.ofSum (.inr y))) (filtBot hg Fu) (fun y => Mu (hg.ofSum (.inr y))) with hmB
    have hpT : ∀ x ∈ starTop hg Sst, IncTop.StarPresented (30 * d) (ω (hg.ι₁ x)) (c (hg.ι₁ x)) :=
      fun x hx => hpres _ (mem_starTop hg hx)
    have hpB : ∀ y ∈ starBot hg Sst, IncTop.StarPresented (30 * d) (ω (hg.ι₂ y)) (c (hg.ι₂ y)) :=
      fun y hy => hpres _ (mem_starBot hg hy)
    -- the middle factor
    set HT := LeafApp.sliceProfiles LG H ((0 : Fin 1), π) u Y with hHT
    set BT : (Fin 1 × Path) → NNReal := fun z => Bd (LeafApp.sliceAddress LG ((0 : Fin 1), π) u Y z.2) with hBT
    set csT := ∏ x ∈ starTop hg Sst, max (c (hg.ι₁ x)) 0 with hcsT
    set csB := ∏ y ∈ starBot hg Sst, max (c (hg.ι₂ y)) 0 with hcsB
    have hβT0 : 0 ≤ leafSizeProduct G₁ BT * csT :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg _ _)
    have hET := treeOracle_real O hC hδ (by omega) B hlt.le hwfBD.1 hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
      (starTop hg Sst) (fun x => ω (hg.ι₁ x)) (fun x => c (hg.ι₁ x)) hpT (filtTop hg Fl)
      (fun x => ann (hg.ofSum (.inl x))) (fun x => M (hg.ofSum (.inl x)))
      (filtTop hg Fu) (fun x => Mu (hg.ofSum (.inl x)))
      (hAst hg hA).1
    have hmid := treeKW_middle_kernel hd hL hθ0 hlt hdec₁ hlay₁ hctrl₁ mT
      (norm_d5Mult_le _ _ _ hpT _ _ _ _ _) hET
    -- the induction hypothesis on the rest
    have hXp' : X₀ = appendChain (appendChain R B) D := by rw [appendChain_assoc, hXe]; exact hXp
    have hlp : (appendChain R B).lonePath = π ++ B.lonePath := appendChain_lonePath R B
    have S''' : TreeLowState LG H Bd (appendChain R B).lonePath D LG'' := by rw [hlp]; exact S''
    have hE₂ := ih m₂ (by omega) (appendChain R B) D LG'' hXp' hsz₂ (by omega) S'''
      (starBot hg Sst) (fun y => ω (hg.ι₂ y)) (fun y => c (hg.ι₂ y)) hpB (filtBot hg Fl)
      (fun y => ann (hg.ofSum (.inr y))) (fun y => M (hg.ofSum (.inr y)))
      (filtBot hg Fu) (fun y => Mu (hg.ofSum (.inr y)))
      (hAst hg hA).2
    rw [hlp] at hE₂
    have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ B.lonePath) z)) * csB :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg _ _)
    have hstep := restr_mul_w_le hΛ hd (θ := θ) 0 T'
      (c := fun k => treeKW L γ δ G₁ HT mT ((u : ℝ) + 1) u k)
      (fun ts k => treeKW L γ δ LG'' (fun z => H (botAddr (π ++ B.lonePath) z)) mB
        ((layerAt LG ((0 : Fin 1), π ++ B.lonePath) : ℝ) + 1) (ts 1) k)
      (by positivity) hmid hE₂
    have heq : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom d)),
        treeKW L γ δ LG' (fun z => H (botAddr π z)) (d5Mult Sst ω Fl ann M Fu Mu) ((u : ℝ) + 1) (ts 1) k =
        (fun k => treeKW L γ δ G₁ HT mT ((u : ℝ) + 1) u k) k *
          (fun ts k => treeKW L γ δ LG'' (fun z => H (botAddr (π ++ B.lonePath) z)) mB
            ((layerAt LG ((0 : Fin 1), π ++ B.lonePath) : ℝ) + 1) (ts 1) k) ts k := fun ts _ k _ =>
      hK ((u : ℝ) + 1) (ts 1) k (by exact_mod_cast Nat.succ_le_succ hlt.le) (30 * d) Sst ω c hpres
        Fl ann M Fu Mu
    refine (restr_congr (θ := θ) (Λ := 30 * d) (Λ₂ := 0) T' Set.univ heq).trans_le (hstep.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have hab := absorb_kernel_step (c := cLeib d (30 * d)) (C := C) (G := G) (δ := δ)
      (βT := leafSizeProduct G₁ BT * csT)
      (β₂ := leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ B.lonePath) z)) * csB)
      (nB := nB) (m₂ := m₂) hLc hC (by
        calc cLeib d (30 * d) * C ^ 2 = 1 * cLeib d (30 * d) * C ^ 2 := by ring
          _ ≤ G := by
            rw [hGdef]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 (by positivity)) (by positivity))
      hδ hβT0 hβ₂0 hnB1
    have hβe : leafSizeProduct LG' (fun z => Bd (botAddr π z)) * ∏ a ∈ Sst, max (c a) 0 =
        (leafSizeProduct G₁ BT * csT) *
          (leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ B.lonePath) z)) * csB) := by
      rw [hβ, starCost_glue hg Sst c]
      ring
    rw [← hmm, ← hβe] at hab
    exact hab

end Induction

/-! ### The case split at the gate -/

section Gate

variable {L γ δ θ : ℝ} {Nmax : ℕ} {C : ℝ} {A : FiltClass} (O : D5TreeKOracleA A d L γ δ θ Nmax C) (hAst : A.Stable) (hC : 1 ≤ C)
  (hd : 1 ≤ d) (hL : 1 ≤ L) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hδ : 0 ≤ δ)

include O hAst hC hd hL hθ0 hθ1 hδ

/-- **Coherent paired trees with the D5 multiplier, `q' < q`.** -/
theorem treeKW_gt_kernel {q q' n : ℕ} (hqq : q' < q) (hnN : n ≤ Nmax)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (F : TreeCohFacts LG X q' q)
    (H : LeafProfiles 1 d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd)
    (Sst : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (c : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ Sst, IncTop.StarPresented (30 * d) (ω a) (c a))
    (Fl : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hA : A 1 LG.garden Fl M Fu Mu) :
    XNormRestr θ (30 * d) 0 (timeBoxGt q q') Set.univ
      (fun ts k => treeKW L γ δ LG H (d5Mult Sst ω Fl ann M Fu Mu) (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (treeG d θ C * (treeG d θ C * δ) ^ n * (leafSizeProduct LG Bd * ∏ a ∈ Sst, max (c a) 0)) := by
  have hΛ : 30 * d ≠ 0 := by omega
  obtain ⟨hCG', hGG', hG1⟩ := le_treeG hd hθ0 hC
  set G' := treeG d θ C with hG'def
  set G := Ktr θ * cLeib d (30 * d) * C ^ 2 with hGdef
  have hC0 : 0 ≤ C := by linarith
  have hK0 : 0 ≤ Ktr θ := Ktr_nonneg _
  have hLc : 1 ≤ cLeib d (30 * d) := one_le_cLeib hd _
  have hβ0 : 0 ≤ leafSizeProduct LG Bd * ∏ a ∈ Sst, max (c a) 0 :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg _ _)
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b :=
    noFlowerParent_of_noFlower (not_flower_of_decodesTree F.dec)
  have hHe : (fun z => H (botAddr [] z)) = H := funext fun z => by rw [botAddr_nil_tree]
  have hBe : (fun z => Bd (botAddr [] z)) = Bd := funext fun z => by rw [botAddr_nil_tree]
  have S₀ : TreeLowState LG H Bd [] X LG := TreeLowState.root F.dec hH
  have hT := timeBoxGt_shift_unit q q'
  set ζ := LG.garden.sig 0 with hζ
  have hnil : X = .nil → layerAt LG ((0 : Fin 1), []) = q' := fun hXn => by
    have h := F.lone
    rw [hXn] at h
    simpa [RegChain.lonePath] using h
  have hroot : X ≠ .nil → ((0 : Fin 1), ([] : Path)) ∈ chainNodesSet X ζ ((0 : Fin 1), []) := fun hXn => by
    cases X with
    | nil => exact absurd rfl hXn
    | pair m' Qr' Qg' inner' rest' => exact PL234.root_mem_chainNodesSet _ _ _ _ _ _ _
  have hr₁q : layerAt LG ((0 : Fin 1), []) ≤ q := by
    by_cases hXn : X = .nil
    · rw [hnil hXn]; exact hqq.le
    · exact F.high _ (hroot hXn)
  rw [XNormRestr_eq_rN]
  by_cases htop : layerAt LG ((0 : Fin 1), []) = q
  · have hXn : X ≠ .nil := fun h => by have := hnil h; omega
    have hEmb := ChainEmb.of_decodesTree F.dec
    by_cases hDn : dropLayer LG ((0 : Fin 1), []) q X = .nil
    · -- a single block in layer `q`
      have hXe := appendChain_take_drop LG ((0 : Fin 1), []) q X
      rw [hDn, appendChain_nil_right] at hXe
      have hTAX : TopAll LG q ((0 : Fin 1), []) X := by
        have := topAll_takeLayer LG q ((0 : Fin 1), []) X
        rwa [hXe] at this
      have hXlay : ∀ z ∈ chainNodesSet X ζ ((0 : Fin 1), []), layerAt LG z = q :=
        chainNodes_layer_of_topAll hEmb F.pl hTAX
      have hlay := layer_single_block F.dec F.lone hXlay
      have hE := treeOracle_real O hC hδ hnN X hqq.le F.wf hsize LG F.dec hlay H Bd hH Sst ω c hpres
        Fl ann M Fu Mu hA
      rw [XNormRestr_eq_rN] at hE
      exact hE.trans (ENNReal.ofReal_le_ofReal (bound_mono_G n hC0 hCG' hδ hβ0))
    · -- the top block in layer `q`, then the lower blocks
      set B := takeLayer LG ((0 : Fin 1), []) q X with hBdef
      set D := dropLayer LG ((0 : Fin 1), []) q X with hDdef
      have hXe : appendChain B D = X := appendChain_take_drop LG _ q X
      have hTA : TopAll LG q ((0 : Fin 1), []) B := topAll_takeLayer LG q _ X
      have hEmbBD : ChainEmb LG.garden (appendChain B D) ζ ((0 : Fin 1), []) .leaf := by rw [hXe]; exact hEmb
      have hPLBD : ChainPairLayers LG (appendChain B D) ζ ((0 : Fin 1), []) := by rw [hXe]; exact F.pl
      have hBlay : ∀ z ∈ chainNodesSet B ζ ((0 : Fin 1), []), layerAt LG z = q :=
        chainNodes_layer_of_topAll (chainEmb_append_left hEmbBD) (chainPairLayers_append_left LG B D ζ _ hPLBD) hTA
      set r'' := layerAt LG ((0 : Fin 1), B.lonePath) with hr''
      have hnode : (addrExt ((0 : Fin 1), ([] : Path)) B.lonePath).2 ∈
          (LG.garden.tree (addrExt ((0 : Fin 1), ([] : Path)) B.lonePath).1).nodes := by
        have ht : (LG.garden.tree ((0 : Fin 1), ([] : Path)).1).subtreeAt ((0 : Fin 1), ([] : Path)).2 =
            B.plug ζ (D.plug ζ .leaf) := by
          rw [hEmbBD.tree, appendChain_plug]
        exact (node_iff_of_subtree hEmb.node ht B.lonePath).1.mpr (lonePath_mem_plug B ζ _)
      have hle : r'' ≤ q := by
        rw [← htop]
        exact layerAt_le_of_under LG hEmb.node hnode (under_ext _ _)
      have hlt : r'' < q := by
        refine lt_of_le_of_ne hle ?_
        have := layer_drop_ne LG q X ((0 : Fin 1), []) hDn
        simpa [addrExt] using this
      have hBlay' : ∀ z ∈ chainNodesSet (takeLayer LG ((0 : Fin 1), []) q X) (LG.garden.sig 0) (0, []),
          layerAt LG z = q := hBlay
      obtain ⟨G₁, LG'', hdec₁, -, hlay₁, hctrl₁, S'', hβ, hg, hK⟩ :=
        treeW_block_step S₀ L γ δ hd hL F.wf hDn hlt hBlay'
      simp only [List.nil_append] at hlay₁ S'' hβ
      have hβe : leafSizeProduct LG Bd =
          leafSizeProduct G₁ (fun z => Bd (LeafApp.sliceAddress LG (0, []) q X z.2)) *
            leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) := by
        have h' := hβ
        rw [hBe] at h'
        exact h'
      have hwfBD : (appendChain B D).wf = true := by rw [hXe]; exact F.wf
      rw [appendChain_wf, Bool.and_eq_true] at hwfBD
      have hsz : X.size = B.size + D.size := by rw [← hXe, appendChain_size]
      obtain ⟨nB, hnB⟩ := size_even_chain B
      obtain ⟨m₂, hm₂⟩ := size_even_chain D
      have hBne : B ≠ .nil := by
        have := takeLayer_ne_nil LG X ((0 : Fin 1), []) hXn
        rw [htop] at this
        exact this
      have hB2 := two_le_size_of_ne_nil B hBne
      have hBsize : B.size = 2 * nB := by omega
      have hsz₂ : D.size = 2 * m₂ := by omega
      have hnn' : n = nB + m₂ := by omega
      have hnB1 : 1 ≤ nB := by omega
      -- the data of the two pieces
      set mT := d5Mult (starTop hg Sst) (fun x => ω (hg.ι₁ x)) (filtTop hg Fl) (fun x => ann (hg.ofSum (.inl x)))
        (fun x => M (hg.ofSum (.inl x))) (filtTop hg Fu) (fun x => Mu (hg.ofSum (.inl x))) with hmT
      set mB := d5Mult (starBot hg Sst) (fun y => ω (hg.ι₂ y)) (filtBot hg Fl) (fun y => ann (hg.ofSum (.inr y)))
        (fun y => M (hg.ofSum (.inr y))) (filtBot hg Fu) (fun y => Mu (hg.ofSum (.inr y))) with hmB
      have hpT : ∀ x ∈ starTop hg Sst, IncTop.StarPresented (30 * d) (ω (hg.ι₁ x)) (c (hg.ι₁ x)) :=
        fun x hx => hpres _ (mem_starTop hg hx)
      have hpB : ∀ y ∈ starBot hg Sst, IncTop.StarPresented (30 * d) (ω (hg.ι₂ y)) (c (hg.ι₂ y)) :=
        fun y hy => hpres _ (mem_starBot hg hy)
      set HT := LeafApp.sliceProfiles LG H ((0 : Fin 1), []) q X with hHT
      set BT : (Fin 1 × Path) → NNReal := fun z => Bd (LeafApp.sliceAddress LG ((0 : Fin 1), []) q X z.2)
        with hBT
      set csT := ∏ x ∈ starTop hg Sst, max (c (hg.ι₁ x)) 0 with hcsT
      set csB := ∏ y ∈ starBot hg Sst, max (c (hg.ι₂ y)) 0 with hcsB
      have hβT0 : 0 ≤ leafSizeProduct G₁ BT * csT :=
        mul_nonneg (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg _ _)
      have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) * csB :=
        mul_nonneg (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg _ _)
      -- the top factor
      have hET := treeOracle_real O hC hδ (by omega) B hlt.le hwfBD.1 hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
        (starTop hg Sst) (fun x => ω (hg.ι₁ x)) (fun x => c (hg.ι₁ x)) hpT (filtTop hg Fl)
        (fun x => ann (hg.ofSum (.inl x))) (fun x => M (hg.ofSum (.inl x)))
        (filtTop hg Fu) (fun x => Mu (hg.ofSum (.inl x)))
        (hAst hg hA).1
      have hX₁ := treeKW_top_kernel hd hL hθ0 hlt hdec₁ hlay₁ hctrl₁ mT (norm_d5Mult_le _ _ _ hpT _ _ _ _ _) hET
        (timeBoxGt (q : ℝ) q') (-(q' : ℝ)) (fun ts hts => hT ts hts)
      -- the lower factor
      have hX₂ := tree_lower_kernelW O hAst hC hd hL hθ0 hδ H Bd F hqq.le (timeBoxGt (q : ℝ) q') (-(q : ℝ)) hT
        m₂ B D LG'' hXe.symm hsz₂ (by omega) S''
        (starBot hg Sst) (fun y => ω (hg.ι₂ y)) (fun y => c (hg.ι₂ y)) hpB (filtBot hg Fl)
        (fun y => ann (hg.ofSum (.inr y))) (fun y => M (hg.ofSum (.inr y)))
        (filtBot hg Fu) (fun y => Mu (hg.ofSum (.inr y)))
        (hAst hg hA).2
      -- the product
      have hcont : ∀ k, Continuous fun ts : Fin 2 → ℝ =>
          treeKW L γ δ LG'' (fun z => H (botAddr B.lonePath z)) mB
            ((layerAt LG ((0 : Fin 1), B.lonePath) : ℝ) + 1) (ts 1) k := fun k =>
        continuous_treeKW_snd L γ δ LG'' _ S''.dec mB _ (norm_d5Mult_le _ _ _ hpB _ _ _ _ _) _ k
          (S''.ctrl.summable_coset hd hL k)
      have hprod := restr_mul_le hΛ hd hθ0 0 0 (B := timeBoxGt (q : ℝ) q')
        (fun ts hts => mem_closure_interior_timeBoxGt hts)
        (fun ts k => treeKW L γ δ G₁ HT mT (ts 0) q k)
        (fun ts k => treeKW L γ δ LG'' (fun z => H (botAddr B.lonePath z)) mB
          ((layerAt LG ((0 : Fin 1), B.lonePath) : ℝ) + 1) (ts 1) k) hcont
        (hX₁.trans_lt ENNReal.ofReal_lt_top) (hX₂.trans_lt ENNReal.ofReal_lt_top)
      have heq : ∀ ts ∈ timeBoxGt (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom d)),
          treeKW L γ δ LG H (d5Mult Sst ω Fl ann M Fu Mu) (ts 0) (ts 1) k =
            treeKW L γ δ G₁ HT mT (ts 0) q k *
              treeKW L γ δ LG'' (fun z => H (botAddr B.lonePath z)) mB
                ((layerAt LG ((0 : Fin 1), B.lonePath) : ℝ) + 1) (ts 1) k := by
        intro ts hts k _
        have ht0 : (q : ℝ) ≤ ts 0 := hts.1.1.1
        have hr1 : (layerAt LG ((0 : Fin 1), [] ++ B.lonePath) : ℝ) + 1 ≤ ts 0 := by
          have : (r'' : ℝ) + 1 ≤ q := by exact_mod_cast hlt
          simp only [List.nil_append]
          linarith
        have hKe := hK (ts 0) (ts 1) k hr1 (30 * d) Sst ω c hpres Fl ann M Fu Mu
        simp only [List.nil_append] at hKe
        rw [hHe] at hKe
        exact hKe
      rw [zero_add] at hprod
      refine (restr_congr (θ := θ) (Λ := 30 * d) (Λ₂ := 0) (timeBoxGt (q : ℝ) q') Set.univ heq).trans_le
        (hprod.trans ((mul_le_mul' (mul_le_mul' le_rfl hX₁) hX₂).trans ?_))
      rw [ofReal_mul4 (Real.rpow_nonneg (by norm_num) θ) (cLeib_nonneg _ _)
        (mul_nonneg hK0 (by positivity))]
      apply ENNReal.ofReal_le_ofReal
      have h2θ : (2 : ℝ) ^ θ ≤ 2 := by
        calc (2 : ℝ) ^ θ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
          _ = 2 := Real.rpow_one 2
      have hlowG : G * (G * δ) ^ m₂ * (leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) * csB) ≤
          G' * (G' * δ) ^ m₂ * (leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) * csB) :=
        bound_mono_G m₂ (by positivity) hGG' hδ hβ₂0
      have hab := absorb_kernel_step (c := 2 * (cLeib d (30 * d) * Ktr θ)) (C := C) (G := G')
        (δ := δ) (βT := leafSizeProduct G₁ BT * csT)
        (β₂ := leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) * csB) (nB := nB) (m₂ := m₂)
        (by nlinarith [one_le_Ktr hθ0]) hC (by rw [hG'def]; unfold treeG; nlinarith) hδ hβT0 hβ₂0 hnB1
      have hβe' : leafSizeProduct LG Bd * ∏ a ∈ Sst, max (c a) 0 =
          (leafSizeProduct G₁ BT * csT) * (leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) * csB) := by
        rw [hβe, starCost_glue hg Sst c]
        ring
      rw [← hnn', ← hβe'] at hab
      calc 2 ^ θ * cLeib d (30 * d) * (Ktr θ * (C * (C * δ) ^ nB * (leafSizeProduct G₁ BT * csT))) *
            (G * (G * δ) ^ m₂ * (leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) * csB))
          ≤ 2 * cLeib d (30 * d) * (Ktr θ * (C * (C * δ) ^ nB * (leafSizeProduct G₁ BT * csT))) *
            (G' * (G' * δ) ^ m₂ * (leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) * csB)) := by
            gcongr
        _ = 2 * (cLeib d (30 * d) * Ktr θ) * (C * (C * δ) ^ nB * (leafSizeProduct G₁ BT * csT)) *
            (G' * (G' * δ) ^ m₂ * (leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) * csB)) := by ring
        _ ≤ _ := hab
  · -- the root lies below `q`: the kernel does not depend on `t`
    have hr₁lt : layerAt LG ((0 : Fin 1), []) < q := lt_of_le_of_ne hr₁q htop
    set r₁ := layerAt LG ((0 : Fin 1), []) with hr₁
    have hE := tree_lower_kernelW O hAst hC hd hL hθ0 hδ H Bd F hqq.le (timeBoxGt (q : ℝ) q') (-(q : ℝ)) hT
      n .nil X LG rfl hsize hnN S₀ Sst ω c hpres Fl ann M Fu Mu hA
    have heq : ∀ ts ∈ timeBoxGt (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom d)),
        treeKW L γ δ LG H (d5Mult Sst ω Fl ann M Fu Mu) (ts 0) (ts 1) k =
          treeKW L γ δ LG (fun z => H (botAddr RegChain.nil.lonePath z)) (d5Mult Sst ω Fl ann M Fu Mu)
            ((layerAt LG ((0 : Fin 1), RegChain.nil.lonePath) : ℝ) + 1) (ts 1) k := by
      intro ts hts k _
      have ht0 : (q : ℝ) ≤ ts 0 := hts.1.1.1
      have hq1' : (r₁ : ℝ) + 1 ≤ q := by exact_mod_cast hr₁lt
      have hK : treeKW L γ δ LG H (d5Mult Sst ω Fl ann M Fu Mu) (ts 0) (ts 1) k =
          treeKW L γ δ LG H (d5Mult Sst ω Fl ann M Fu Mu) ((r₁ : ℝ) + 1) (ts 1) k :=
        treeKW_upper_eq L γ δ LG H _ hfl (ts 1) k fun b => by
          have hroot0 : ([] : Path) ∈ (LG.garden.tree 0).nodes := TTree.nil_mem_nodes _
          have hu : Under ((0 : Fin 1), ([] : Path)) b.toNode.1 :=
            ⟨Subsingleton.elim _ _, List.nil_prefix⟩
          have hl := layerAt_le_of_under LG hroot0 b.toNode.2 hu
          rw [layerAt_node] at hl
          have : (LG.layer b.toNode : ℝ) ≤ r₁ := by exact_mod_cast hl
          exact ⟨by linarith, by linarith⟩
      simp only [RegChain.lonePath]
      rw [hK, hHe]
    refine (restr_congr (θ := θ) (Λ := 30 * d) (Λ₂ := 0) (timeBoxGt (q : ℝ) q') Set.univ heq).trans_le
      (hE.trans ?_)
    simp only [RegChain.lonePath]
    rw [hBe]
    exact ENNReal.ofReal_le_ofReal (bound_mono_G n (by positivity) hGG' hδ hβ0)

/-- **Coherent paired trees with the D5 multiplier, all `q' ≤ q`.** -/
theorem treeKW_coherent_kernel {p q q' n : ℕ} (hqq : q' ≤ q) (hnN : n ≤ Nmax)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (hcoh : IsCoherentTreeAt p q q' X LG)
    (H : LeafProfiles 1 d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd)
    (Sst : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (c : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ Sst, IncTop.StarPresented (30 * d) (ω a) (c a))
    (Fl : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hA : A 1 LG.garden Fl M Fu Mu) :
    XNormRestr θ (30 * d) 0 (timeBoxGt q q') Set.univ
      (fun ts k => treeKW L γ δ LG H (d5Mult Sst ω Fl ann M Fu Mu) (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (treeG d θ C * (treeG d θ C * δ) ^ n * (leafSizeProduct LG Bd * ∏ a ∈ Sst, max (c a) 0)) := by
  rcases eq_or_lt_of_le hqq with heq | hlt
  · subst heq
    have hlay := coherentTree_layer_eq hcoh
    have hlay' : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else q' := fun a => by
      rw [hlay a]
      split_ifs <;> rfl
    have hβ0 : 0 ≤ leafSizeProduct LG Bd * ∏ a ∈ Sst, max (c a) 0 :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg _ _)
    exact (treeOracle_real O hC hδ hnN X le_rfl hcoh.1 hsize LG hcoh.2.1 hlay' H Bd hH Sst ω c hpres
      Fl ann M Fu Mu hA).trans
      (ENNReal.ofReal_le_ofReal (bound_mono_G n (by linarith) (le_treeG hd hθ0 hC).1 hδ hβ0))
  · exact treeKW_gt_kernel O hAst hC hd hL hθ0 hθ1 hδ hlt hnN X hsize LG (treeCohFacts_of_coherent hcoh) H Bd hH
      Sst ω c hpres Fl ann M Fu Mu hA

end Gate

end WaveTurbulence.Flower.FiltCoh
