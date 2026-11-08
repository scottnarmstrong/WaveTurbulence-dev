/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiTreeD5
public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiCoupleGate

/-! # FILT-COH (D5d-d1): coherent regular couples across layers with the D5 multiplier (bound only)

Milestone (a)'s `MultiCouple`/`MultiCoupleGate` (bound-only replay of main's `PL2330.lower_bounds30`,
`couple_err_type1_30`, `couple_err_type2_30`, `couple_same30`) for the multiplied kernel
`kernelLeavesW … (d5Mult S ω F ann M Fu Mu)`, from the single-layer oracles `D5TreeKOracle`/`D5CoupleKOracle`
(HYPOTHESES here). Each block step (`coupleW_block_step`) splits the D5 data of the current carrier into those of the
block and of the remaining couple; the star costs split by `starCost_glue`. -/

public section
open WaveTurbulence.Induct
open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltCoh

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.PL2330 WaveTurbulence.Reg WaveTurbulence.Links

/-- `D5CoupleKOracle` for the filter data of a class `A` (`D5CoupleKOracle` is the class `filtScaled L`). -/
@[expose] def D5CoupleKOracleA (A : FiltClass) (d : ℕ) (L γ δ θ : ℝ) (Nmax : ℕ) (C : ℝ) : Prop :=
  ∀ (r n : ℕ), n ≤ Nmax → ∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n →
    ∀ LG : LayeredGarden 2, Q.Decodes LG.garden → (∀ a, LG.layer a = r) →
    ∀ (H : LeafProfiles 2 d) (B : (Fin 2 × Path) → NNReal), LeafwiseControlled LG H B →
    ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
      (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, IncTop.StarPresented (30 * d) (ω a) (cω a)) →
    ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
      (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ),
      A 2 LG.garden F M Fu Mu →
    XNormRestr θ (30 * d) (30 * d) (timeBox r r) Set.univ
      (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k
        (fun _ => 0) 0 (d5Mult S ω F ann M Fu Mu)) ≤
      ENNReal.ofReal (C * (C * δ) ^ n * leafSizeProduct LG B) * ∏ a ∈ S, ENNReal.ofReal (cω a)

theorem D5CoupleKOracle.toScaled {d : ℕ} {L γ δ θ : ℝ} {Nmax : ℕ} {C : ℝ} (O : D5CoupleKOracle d L γ δ θ Nmax C) :
    D5CoupleKOracleA (filtScaled L) d L γ δ θ Nmax C :=
  fun r n hn Q hwf hsz LG hQ hlay H B hH S ω cω hp F ann M Fu Mu hA =>
    O r n hn Q hwf hsz LG hQ hlay H B hH S ω cω hp F ann M hA.1 Fu Mu hA.2

/-- The couple oracle in the real form used by the induction. -/
theorem coupleOracle_real {d : ℕ} {L γ δ θ : ℝ} {Nmax : ℕ} {C : ℝ} {A : FiltClass}
    (O : D5CoupleKOracleA A d L γ δ θ Nmax C)
    (hC : 1 ≤ C) (hδ : 0 ≤ δ) {r n : ℕ} (hn : n ≤ Nmax) (Q : RegCpl) (hwf : Q.wf = true)
    (hsz : Q.size = 2 * n) (LG : LayeredGarden 2) (hQ : Q.Decodes LG.garden) (hlay : ∀ a, LG.layer a = r)
    (H : LeafProfiles 2 d) (B : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H B)
    (Sst : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (c : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ Sst, IncTop.StarPresented (30 * d) (ω a) (c a))
    (Fl : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hA : A 2 LG.garden Fl M Fu Mu) :
    XNormRestr θ (30 * d) (30 * d) (timeBox r r) Set.univ
      (fun ts k => coupleKW L γ δ LG H (d5Mult Sst ω Fl ann M Fu Mu) (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (C * (C * δ) ^ n * (leafSizeProduct LG B * ∏ a ∈ Sst, max (c a) 0)) := by
  have hβ0 : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hC0 : 0 ≤ C := by linarith
  have h := O r n hn Q hwf hsz LG hQ hlay H B hH Sst ω c hpres Fl ann M Fu Mu hA
  rw [ofReal_mul_prod_ofReal _ _ (by positivity)] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  ring

section Induction

variable (P : WTParams) {θ : ℝ} {Nmax : ℕ} {C : ℝ} {A : FiltClass}
  (OT : D5TreeKOracleA A P.d P.L P.γ P.δ θ Nmax C) (OC : D5CoupleKOracleA A P.d P.L P.γ P.δ θ Nmax C)
  (hAst : A.Stable) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hθ0 : 0 ≤ θ) (hδ : 0 ≤ P.δ)
  {LG : LayeredGarden 2} (H : LeafProfiles 2 P.d) (Bd : (Fin 2 × Path) → NNReal)
  {Xp Xm : RegChain} {Qlp : RegCpl} {q' p : ℕ} (F : CohFacts LG Xp Xm Qlp q' p)
  (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox)

include OT OC hAst hC hd hL hθ0 hδ F hT'

/-- **The lower multiplied couple kernels**, by induction over the blocks of the `+` chain, for every D5 datum on
the current carrier, with `G = K_tr(θ) · cLeib · C²`. -/
theorem couple_lower_kernelW : ∀ (m : ℕ) (R X : RegChain) (LG' : LayeredGarden 2), Xp = appendChain R X →
    (SourceApp.closeCouple X Xm Qlp).size = 2 * m → m ≤ Nmax →
    LowState LG H Bd Xm Qlp R.lonePath X LG' →
    ∀ (Sst : Finset (GNode LG'.garden.tree)) (ω : GNode LG'.garden.tree → IncTop.Star P.d → ℂ)
      (c : GNode LG'.garden.tree → ℝ), (∀ a ∈ Sst, IncTop.StarPresented (30 * P.d) (ω a) (c a)) →
    ∀ (Fl : Finset (GBranch LG'.garden.tree)) (ann : GBranch LG'.garden.tree → Bool)
      (M : GBranch LG'.garden.tree → ℝ) (Fu : Finset (GBranch LG'.garden.tree)) (Mu : GBranch LG'.garden.tree → ℝ),
      A 2 LG'.garden Fl M Fu Mu →
    rN θ (30 * P.d) (30 * P.d) T' (fun ts k =>
        coupleKW P.L P.γ P.δ LG' (fun z => H (botAddr R.lonePath z)) (d5Mult Sst ω Fl ann M Fu Mu)
          ((layerAt LG ((0 : Fin 2), R.lonePath) : ℝ) + 1) (ts 1) k) ≤
        ENNReal.ofReal ((Ktr θ * cLeib P.d (30 * P.d) * C ^ 2) *
          ((Ktr θ * cLeib P.d (30 * P.d) * C ^ 2) * P.δ) ^ m *
          (leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) * ∏ a ∈ Sst, max (c a) 0)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro R X LG' hXp hsize hmN S Sst ω c hpres Fl ann M Fu Mu hA
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hC0 : 0 ≤ C := by linarith
  have hK1 : 1 ≤ Ktr θ := one_le_Ktr hθ0
  have hK0 : 0 ≤ Ktr θ := Ktr_nonneg _
  have hLc : 1 ≤ cLeib P.d (30 * P.d) := one_le_cLeib hd _
  set G := Ktr θ * cLeib P.d (30 * P.d) * C ^ 2 with hGdef
  have hCG : C ≤ G := by
    have h1 : 1 * 1 * C ^ 1 ≤ Ktr θ * cLeib P.d (30 * P.d) * C ^ 2 :=
      mul_le_mul (mul_le_mul hK1 hLc zero_le_one (by linarith)) (pow_le_pow_right₀ hC (by norm_num))
        (by positivity) (by positivity)
    simpa using h1
  have hG0 : 0 ≤ G := hC0.trans hCG
  have hβ0 : 0 ≤ leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) * ∏ a ∈ Sst, max (c a) 0 :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg _ _)
  obtain ⟨hXwf, hmwf, hlwf, hlt2⟩ := F.wf_suffix hXp
  by_cases hbase : X = .nil ∨ layerAt LG ((0 : Fin 2), R.lonePath) ≤ q'
  · -- the base: a single-layer couple in layer `q'`
    obtain ⟨hu, hTA, hlayq⟩ := base_layers P F hXp S hbase
    have hwfc : (SourceApp.closeCouple X Xm Qlp).wf = true := closeCouple_wf hXwf hmwf hlwf hlt2
    have hE := coupleOracle_real OC hC hδ hmN _ hwfc hsize LG' S.dec hlayq _ _ S.ctrl Sst ω c hpres
      Fl ann M Fu Mu hA
    have hEb := coupleKW_bottom_kernel hd hL hθ0 S.dec S.ctrl _ (norm_d5Mult_le Sst ω c hpres Fl ann M Fu Mu)
      hE T' b₀ hT'
    rw [hu]
    refine hEb.trans (ENNReal.ofReal_le_ofReal ?_)
    calc Ktr θ * (C * (C * P.δ) ^ m *
          (leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) * ∏ a ∈ Sst, max (c a) 0))
        = (Ktr θ * C) * (C * P.δ) ^ m *
          (leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) * ∏ a ∈ Sst, max (c a) 0) := by ring
      _ ≤ G * (G * P.δ) ^ m *
          (leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) * ∏ a ∈ Sst, max (c a) 0) := by
          apply mul_le_mul_of_nonneg_right _ hβ0
          apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCG hδ) m)
            (by positivity) hG0
          calc Ktr θ * C = Ktr θ * 1 * C ^ 1 := by ring
            _ ≤ Ktr θ * cLeib P.d (30 * P.d) * C ^ 2 :=
                mul_le_mul (mul_le_mul_of_nonneg_left hLc hK0) (pow_le_pow_right₀ hC (by norm_num))
                  (by positivity) (by positivity)
  · simp only [not_or, not_le] at hbase
    obtain ⟨hXn, hqu⟩ := hbase
    set π := R.lonePath with hπ
    set u := layerAt LG ((0 : Fin 2), π) with hu
    have hEmb := F.emb_suffix hXp
    have hPL := F.pl_suffix hXp
    set B := takeLayer LG ((0 : Fin 2), π) u X with hBdef
    set D := dropLayer LG ((0 : Fin 2), π) u X with hDdef
    have hXe : appendChain B D = X := appendChain_take_drop LG _ u X
    have hTA : TopAll LG u ((0 : Fin 2), π) B := topAll_takeLayer LG u _ X
    have hEmbBD : ChainEmb LG.garden (appendChain B D) 1 ((0 : Fin 2), π) Qlp.trees.1 := by
      rw [hXe]; exact hEmb
    have hPLBD : ChainPairLayers LG (appendChain B D) 1 ((0 : Fin 2), π) := by rw [hXe]; exact hPL
    have hBlay : ∀ z ∈ chainNodesSet B 1 ((0 : Fin 2), π), layerAt LG z = u :=
      chainNodes_layer_of_topAll (chainEmb_append_left hEmbBD)
        (chainPairLayers_append_left LG B D 1 _ hPLBD) hTA
    have hnode : (addrExt ((0 : Fin 2), π) B.lonePath).2 ∈
        (LG.garden.tree (addrExt ((0 : Fin 2), π) B.lonePath).1).nodes := by
      have ht : (LG.garden.tree ((0 : Fin 2), π).1).subtreeAt ((0 : Fin 2), π).2 =
          B.plug 1 (D.plug 1 Qlp.trees.1) := by
        rw [hEmbBD.tree, appendChain_plug]
      exact (node_iff_of_subtree hEmb.node ht B.lonePath).1.mpr (lonePath_mem_plug B 1 _)
    have hle : layerAt LG ((0 : Fin 2), π ++ B.lonePath) ≤ u :=
      layerAt_le_of_under LG hEmb.node hnode (under_ext _ _)
    have hlone := F.lone_suffix hXp
    have hloneB : D = .nil → layerAt LG ((0 : Fin 2), π ++ B.lonePath) = q' := fun hDn => by
      have e : ((0 : Fin 2), π ++ B.lonePath) = addrExt ((0 : Fin 2), π) X.lonePath := by
        rw [← hXe, appendChain_lonePath, hDn]
        simp [RegChain.lonePath, addrExt]
      rw [e]
      exact hlone
    have hlt : layerAt LG ((0 : Fin 2), π ++ B.lonePath) < u := by
      by_cases hDn : D = .nil
      · rw [hloneB hDn]; exact hqu
      · exact lt_of_le_of_ne hle (layer_drop_ne LG u X _ hDn)
    have hwf2 : (RegCpl.type2 X Xm Qlp).wf = true := by
      have hXnil : X.isNil = false := by cases X <;> simp_all [RegChain.isNil]
      simp [RegCpl.wf, hXwf, hmwf, hlwf, hlt2, hXnil]
    obtain ⟨G₁, LG'', hdec₁, -, hlay₁, hctrl₁, S'', hβ, hg, hK⟩ :=
      coupleW_block_step S P.L P.γ P.δ hd hL hXn hwf2 hu.symm hlt hBlay
    have hsz : (SourceApp.closeCouple X Xm Qlp).size = B.size + (SourceApp.closeCouple D Xm Qlp).size := by
      rw [← hXe, closeCouple_size, closeCouple_size, appendChain_size]
      ring
    obtain ⟨nB, hnB⟩ := size_even_chain B
    obtain ⟨m₂, hm₂⟩ := size_even_cpl (SourceApp.closeCouple D Xm Qlp)
    have hB2 := two_le_size_of_ne_nil B (takeLayer_ne_nil LG X _ hXn)
    have hBsize : B.size = 2 * nB := by omega
    have hsz₂ : (SourceApp.closeCouple D Xm Qlp).size = 2 * m₂ := by omega
    have hmm : m = nB + m₂ := by omega
    have hnB1 : 1 ≤ nB := by omega
    have hBwf : B.wf = true := (wf_split (hXe ▸ hwf2 : (RegCpl.type2 (appendChain B D) Xm Qlp).wf = true)).1
    -- the data of the two pieces
    set mT := d5Mult (starTop hg Sst) (fun x => ω (hg.ι₁ x)) (filtTop hg Fl) (fun x => ann (hg.ofSum (.inl x)))
      (fun x => M (hg.ofSum (.inl x))) (filtTop hg Fu) (fun x => Mu (hg.ofSum (.inl x))) with hmT
    set mB := d5Mult (starBot hg Sst) (fun y => ω (hg.ι₂ y)) (filtBot hg Fl) (fun y => ann (hg.ofSum (.inr y)))
      (fun y => M (hg.ofSum (.inr y))) (filtBot hg Fu) (fun y => Mu (hg.ofSum (.inr y))) with hmB
    have hpT : ∀ x ∈ starTop hg Sst, IncTop.StarPresented (30 * P.d) (ω (hg.ι₁ x)) (c (hg.ι₁ x)) :=
      fun x hx => hpres _ (mem_starTop hg hx)
    have hpB : ∀ y ∈ starBot hg Sst, IncTop.StarPresented (30 * P.d) (ω (hg.ι₂ y)) (c (hg.ι₂ y)) :=
      fun y hy => hpres _ (mem_starBot hg hy)
    set HT := LeafApp.sliceProfiles LG H ((0 : Fin 2), π) u X with hHT
    set BT : (Fin 1 × Path) → NNReal := fun z => Bd (LeafApp.sliceAddress LG ((0 : Fin 2), π) u X z.2) with hBT
    set csT := ∏ x ∈ starTop hg Sst, max (c (hg.ι₁ x)) 0 with hcsT
    set csB := ∏ y ∈ starBot hg Sst, max (c (hg.ι₂ y)) 0 with hcsB
    have hβT0 : 0 ≤ leafSizeProduct G₁ BT * csT :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg _ _)
    have hET := treeOracle_real OT hC hδ (by omega) B hlt.le hBwf hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
      (starTop hg Sst) (fun x => ω (hg.ι₁ x)) (fun x => c (hg.ι₁ x)) hpT (filtTop hg Fl)
      (fun x => ann (hg.ofSum (.inl x))) (fun x => M (hg.ofSum (.inl x)))
      (filtTop hg Fu) (fun x => Mu (hg.ofSum (.inl x)))
      (hAst hg hA).1
    have hmid := treeKW_middle_kernel hd hL hθ0 hlt hdec₁ hlay₁ hctrl₁ mT
      (norm_d5Mult_le _ _ _ hpT _ _ _ _ _) hET
    -- the induction hypothesis on the rest
    have hXp' : Xp = appendChain (appendChain R B) D := by rw [appendChain_assoc, hXe]; exact hXp
    have hlp : (appendChain R B).lonePath = π ++ B.lonePath := appendChain_lonePath R B
    have S''' : LowState LG H Bd Xm Qlp (appendChain R B).lonePath D LG'' := by rw [hlp]; exact S''
    have hE₂ := ih m₂ (by omega) (appendChain R B) D LG'' hXp' hsz₂ (by omega) S'''
      (starBot hg Sst) (fun y => ω (hg.ι₂ y)) (fun y => c (hg.ι₂ y)) hpB (filtBot hg Fl)
      (fun y => ann (hg.ofSum (.inr y))) (fun y => M (hg.ofSum (.inr y)))
      (filtBot hg Fu) (fun y => Mu (hg.ofSum (.inr y)))
      (hAst hg hA).2
    rw [hlp] at hE₂
    have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ B.lonePath) z)) * csB :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg _ _)
    have hstep := restr_mul_s_le hΛ hd (θ := θ) (30 * P.d) T'
      (c := fun k => treeKW P.L P.γ P.δ G₁ HT mT ((u : ℝ) + 1) u k)
      (fun ts k => coupleKW P.L P.γ P.δ LG'' (fun z => H (botAddr (π ++ B.lonePath) z)) mB
        ((layerAt LG ((0 : Fin 2), π ++ B.lonePath) : ℝ) + 1) (ts 1) k)
      (by positivity) hmid hE₂
    have heq : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        coupleKW P.L P.γ P.δ LG' (fun z => H (botAddr π z)) (d5Mult Sst ω Fl ann M Fu Mu)
          ((u : ℝ) + 1) (ts 1) k =
        (fun k => treeKW P.L P.γ P.δ G₁ HT mT ((u : ℝ) + 1) u k) k *
          (fun ts k => coupleKW P.L P.γ P.δ LG'' (fun z => H (botAddr (π ++ B.lonePath) z)) mB
            ((layerAt LG ((0 : Fin 2), π ++ B.lonePath) : ℝ) + 1) (ts 1) k) ts k := fun ts _ k _ =>
      hK ((u : ℝ) + 1) (ts 1) k (by exact_mod_cast Nat.succ_le_succ hlt.le) (30 * P.d) Sst ω c hpres
        Fl ann M Fu Mu
    refine (restr_congr (θ := θ) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) T' Set.univ heq).trans_le (hstep.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have hab := absorb_kernel_step (c := cLeib P.d (30 * P.d)) (C := C) (G := G) (δ := P.δ)
      (βT := leafSizeProduct G₁ BT * csT)
      (β₂ := leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ B.lonePath) z)) * csB)
      (nB := nB) (m₂ := m₂) hLc hC (by
        calc cLeib P.d (30 * P.d) * C ^ 2 = 1 * cLeib P.d (30 * P.d) * C ^ 2 := by ring
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

section Gate

variable (P : WTParams) {θ : ℝ} {Nmax : ℕ} {C : ℝ} {A : FiltClass}
  (OT : D5TreeKOracleA A P.d P.L P.γ P.δ θ Nmax C) (OC : D5CoupleKOracleA A P.d P.L P.γ P.δ θ Nmax C)
  (hAst : A.Stable) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hδ : 0 ≤ P.δ)

include OT OC hAst hC hd hL hθ0 hθ1 hδ

/-- **Coherent couples with the D5 multiplier, type 2, `q' < q`.** -/
theorem coupleKW_type2_kernel {p q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ Nmax)
    (Xp Xm : RegChain) (Qlp : RegCpl) (hsize : (RegCpl.type2 Xp Xm Qlp).size = 2 * n) (LG : LayeredGarden 2)
    (hcoh : IsCoherentCoupleAt p q q' (.type2 Xp Xm Qlp) LG) (H : LeafProfiles 2 P.d)
    (Bd : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd)
    (Sst : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star P.d → ℂ)
    (c : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ Sst, IncTop.StarPresented (30 * P.d) (ω a) (c a))
    (Fl : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hA : A 2 LG.garden Fl M Fu Mu) :
    rN θ (30 * P.d) (30 * P.d) (timeBox q q')
      (fun ts k => coupleKW P.L P.γ P.δ LG H (d5Mult Sst ω Fl ann M Fu Mu) (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (treeG P.d θ C * (treeG P.d θ C * P.δ) ^ n *
        (leafSizeProduct LG Bd * ∏ a ∈ Sst, max (c a) 0)) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  obtain ⟨hCG', hGG', hG1⟩ := le_treeG hd hθ0 hC
  set G' := treeG P.d θ C with hG'def
  set G := Ktr θ * cLeib P.d (30 * P.d) * C ^ 2 with hGdef
  have hC0 : 0 ≤ C := by linarith
  have hK1 : 1 ≤ Ktr θ := one_le_Ktr hθ0
  have hLc : 1 ≤ cLeib P.d (30 * P.d) := one_le_cLeib hd _
  have F := cohFacts_of_coherent hqq.le hqp hcoh
  have hQ := hcoh.2.1
  have hplain : LG.garden.IsPlain := hQ.1.1
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b := noFlowerParent_of_noFlower (not_flower_of_plain hplain)
  have hβ0 : 0 ≤ leafSizeProduct LG Bd * ∏ a ∈ Sst, max (c a) 0 :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg _ _)
  have hwf := F.wf
  have hnn : (Xp.isNil && Xm.isNil) = false := by
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hwf
    exact hwf.2
  have hcl : SourceApp.closeCouple Xp Xm Qlp = RegCpl.type2 Xp Xm Qlp := by
    unfold SourceApp.closeCouple
    rw [hnn]
    rfl
  have hHe : (fun z => H (botAddr [] z)) = H := funext fun z => by rw [botAddr_nil]
  have hBe : (fun z => Bd (botAddr [] z)) = Bd := funext fun z => by rw [botAddr_nil]
  have S₀ : LowState LG H Bd Xm Qlp RegChain.nil.lonePath Xp LG := by
    refine ⟨by rw [hcl]; exact hQ, fun z => by simp [RegChain.lonePath, botAddr_nil], ?_⟩
    show LeafwiseControlled LG (fun z => H (botAddr [] z)) (fun z => Bd (botAddr [] z))
    rw [hHe, hBe]
    exact hH
  have hsizeC : (SourceApp.closeCouple Xp Xm Qlp).size = 2 * n := by rw [hcl]; exact hsize
  have hT := timeBox_shift_unit q q'
  set r₁ := layerAt LG ((0 : Fin 2), []) with hr₁
  have hr₁q : r₁ ≤ q := root_le_type2 hqq.le hcoh
  by_cases htop : r₁ = q
  · have hXpn : Xp ≠ .nil := by
      intro hXpn
      have := F.lone_suffix (R := .nil) (X := Xp) rfl
      rw [hXpn] at this
      simp only [RegChain.lonePath, addrExt, List.append_nil] at this
      rw [← hr₁, htop] at this
      omega
    obtain ⟨hBlay, hlt, hlow'', hwf2, hSMD⟩ := block_facts F (R := .nil) rfl hXpn htop hqq
    simp only [RegChain.lonePath, List.nil_append] at hBlay hlt hlow'' hSMD
    set B := takeLayer LG ((0 : Fin 2), []) q Xp with hBdef
    set D := dropLayer LG ((0 : Fin 2), []) q Xp with hDdef
    set r'' := layerAt LG ((0 : Fin 2), B.lonePath) with hr''
    have hXe : appendChain B D = Xp := appendChain_take_drop LG _ q Xp
    obtain ⟨G₁, LG'', hdec₁, -, hlay₁, hctrl₁, S'', hβ, hg, hK⟩ :=
      coupleW_block_step S₀ P.L P.γ P.δ hd hL hXpn hwf2 htop hlt hBlay
    simp only [RegChain.lonePath, List.nil_append] at hlay₁ S'' hβ
    have hsz : (RegCpl.type2 Xp Xm Qlp).size = B.size + (SourceApp.closeCouple D Xm Qlp).size := by
      rw [← hXe, closeCouple_size]
      simp only [RegCpl.size, appendChain_size]
      ring
    obtain ⟨nB, hnB⟩ := size_even_chain B
    obtain ⟨m₂, hm₂⟩ := size_even_cpl (SourceApp.closeCouple D Xm Qlp)
    have hBne : B ≠ .nil := by
      have := takeLayer_ne_nil LG Xp ((0 : Fin 2), []) hXpn
      rw [← hr₁, htop] at this
      exact this
    have hB2 := two_le_size_of_ne_nil B hBne
    have hBsize : B.size = 2 * nB := by omega
    have hsz₂ : (SourceApp.closeCouple D Xm Qlp).size = 2 * m₂ := by omega
    have hnn' : n = nB + m₂ := by omega
    have hnB1 : 1 ≤ nB := by omega
    have hBwf : B.wf = true :=
      (wf_split (hXe ▸ hwf2 : (RegCpl.type2 (appendChain B D) Xm Qlp).wf = true)).1
    -- the data of the two pieces
    set mT := d5Mult (starTop hg Sst) (fun x => ω (hg.ι₁ x)) (filtTop hg Fl) (fun x => ann (hg.ofSum (.inl x)))
      (fun x => M (hg.ofSum (.inl x))) (filtTop hg Fu) (fun x => Mu (hg.ofSum (.inl x))) with hmT
    set mB := d5Mult (starBot hg Sst) (fun y => ω (hg.ι₂ y)) (filtBot hg Fl) (fun y => ann (hg.ofSum (.inr y)))
      (fun y => M (hg.ofSum (.inr y))) (filtBot hg Fu) (fun y => Mu (hg.ofSum (.inr y))) with hmB
    have hpT : ∀ x ∈ starTop hg Sst, IncTop.StarPresented (30 * P.d) (ω (hg.ι₁ x)) (c (hg.ι₁ x)) :=
      fun x hx => hpres _ (mem_starTop hg hx)
    have hpB : ∀ y ∈ starBot hg Sst, IncTop.StarPresented (30 * P.d) (ω (hg.ι₂ y)) (c (hg.ι₂ y)) :=
      fun y hy => hpres _ (mem_starBot hg hy)
    set HT := LeafApp.sliceProfiles LG H ((0 : Fin 2), []) q Xp with hHT
    set BT : (Fin 1 × Path) → NNReal := fun z => Bd (LeafApp.sliceAddress LG ((0 : Fin 2), []) q Xp z.2)
      with hBT
    set csT := ∏ x ∈ starTop hg Sst, max (c (hg.ι₁ x)) 0 with hcsT
    set csB := ∏ y ∈ starBot hg Sst, max (c (hg.ι₂ y)) 0 with hcsB
    have hβT0 : 0 ≤ leafSizeProduct G₁ BT * csT :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg _ _)
    have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) * csB :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg _ _)
    have hβT1 : 0 ≤ leafSizeProduct G₁ BT := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hβ₂1 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) :=
      Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hcsT0 : 0 ≤ csT := starCost_nonneg _ _
    have hcsB0 : 0 ≤ csB := starCost_nonneg _ _
    -- the top factor
    have hET := treeOracle_real OT hC hδ (by omega) B hlt.le hBwf hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
      (starTop hg Sst) (fun x => ω (hg.ι₁ x)) (fun x => c (hg.ι₁ x)) hpT (filtTop hg Fl)
      (fun x => ann (hg.ofSum (.inl x))) (fun x => M (hg.ofSum (.inl x)))
      (filtTop hg Fu) (fun x => Mu (hg.ofSum (.inl x)))
      (hAst hg hA).1
    have hX₁ := treeKW_top_kernel hd hL hθ0 hlt hdec₁ hlay₁ hctrl₁ mT (norm_d5Mult_le _ _ _ hpT _ _ _ _ _) hET
      (timeBox (q : ℝ) q') (-(q' : ℝ)) (fun ts hts => hT ts hts)
    -- the lower factor
    have hX₂ := couple_lower_kernelW P OT OC hAst hC hd hL hθ0 hδ H Bd F (timeBox (q : ℝ) q') (-(q : ℝ)) hT
      m₂ B D LG'' hXe.symm hsz₂ (by omega) S''
      (starBot hg Sst) (fun y => ω (hg.ι₂ y)) (fun y => c (hg.ι₂ y)) hpB (filtBot hg Fl)
      (fun y => ann (hg.ofSum (.inr y))) (fun y => M (hg.ofSum (.inr y)))
      (filtBot hg Fu) (fun y => Mu (hg.ofSum (.inr y)))
      (hAst hg hA).2
    have hplain'' : LG''.garden.IsPlain := S''.dec.1.1
    have hcont : ∀ k, Continuous fun ts : Fin 2 → ℝ =>
        coupleKW P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) mB
          ((layerAt LG ((0 : Fin 2), B.lonePath) : ℝ) + 1) (ts 1) k := fun k =>
      continuous_coupleKW_snd P.L P.γ P.δ LG'' _ hplain'' mB _ (norm_d5Mult_le _ _ _ hpB _ _ _ _ _) _ k
        (S''.ctrl.summable_coset hd hL k)
    have hprod := restr_mul_le hΛ hd hθ0 0 (30 * P.d) (B := timeBox (q : ℝ) q')
      (fun ts hts => by rw [closure_interior_timeBox]; exact hts)
      (fun ts k => treeKW P.L P.γ P.δ G₁ HT mT (ts 0) q k)
      (fun ts k => coupleKW P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) mB
        ((layerAt LG ((0 : Fin 2), B.lonePath) : ℝ) + 1) (ts 1) k) hcont
      (hX₁.trans_lt ENNReal.ofReal_lt_top) (hX₂.trans_lt ENNReal.ofReal_lt_top)
    rw [zero_add] at hprod
    have heq : ∀ ts ∈ timeBox (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        coupleKW P.L P.γ P.δ LG H (d5Mult Sst ω Fl ann M Fu Mu) (ts 0) (ts 1) k =
          treeKW P.L P.γ P.δ G₁ HT mT (ts 0) q k *
            coupleKW P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) mB
              ((layerAt LG ((0 : Fin 2), B.lonePath) : ℝ) + 1) (ts 1) k := by
      intro ts hts k _
      have ht0 : (q : ℝ) ≤ ts 0 := hts.1.1
      have hr1 : (layerAt LG ((0 : Fin 2), RegChain.nil.lonePath ++ B.lonePath) : ℝ) + 1 ≤ ts 0 := by
        have : (r'' : ℝ) + 1 ≤ q := by exact_mod_cast hlt
        simp only [RegChain.lonePath, List.nil_append]
        linarith
      have hKe := hK (ts 0) (ts 1) k hr1 (30 * P.d) Sst ω c hpres Fl ann M Fu Mu
      simp only [RegChain.lonePath, List.nil_append] at hKe
      rw [hHe] at hKe
      exact hKe
    refine (restr_congr (θ := θ) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) (timeBox (q : ℝ) q') Set.univ heq).trans_le
      (hprod.trans ((mul_le_mul' (mul_le_mul' le_rfl hX₁) hX₂).trans ?_))
    rw [ofReal_mul4 (Real.rpow_nonneg (by norm_num) θ) (cLeib_nonneg _ _)
      (mul_nonneg (Ktr_nonneg _) (by positivity))]
    apply ENNReal.ofReal_le_ofReal
    have h2θ : (2 : ℝ) ^ θ ≤ 2 := by
      calc (2 : ℝ) ^ θ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
        _ = 2 := Real.rpow_one 2
    have hab := absorb_kernel_step (c := 2 * (cLeib P.d (30 * P.d) * Ktr θ)) (C := C) (G := G')
      (δ := P.δ) (βT := leafSizeProduct G₁ BT * csT)
      (β₂ := leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) * csB) (nB := nB) (m₂ := m₂)
      (by nlinarith [one_le_Ktr hθ0]) hC (by rw [hG'def]; unfold treeG; nlinarith) hδ hβT0 hβ₂0 hnB1
    have hβe : leafSizeProduct LG Bd * ∏ a ∈ Sst, max (c a) 0 = (leafSizeProduct G₁ BT * csT) *
        (leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) * csB) := by
      have h' := hβ
      rw [hBe] at h'
      rw [h', starCost_glue hg Sst c]
      ring
    rw [← hnn', ← hβe] at hab
    calc 2 ^ θ * cLeib P.d (30 * P.d) * (Ktr θ * (C * (C * P.δ) ^ nB * (leafSizeProduct G₁ BT * csT))) *
          (G * (G * P.δ) ^ m₂ * (leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) * csB))
        ≤ 2 * cLeib P.d (30 * P.d) * (Ktr θ * (C * (C * P.δ) ^ nB * (leafSizeProduct G₁ BT * csT))) *
          (G' * (G' * P.δ) ^ m₂ * (leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) * csB)) := by
          gcongr
      _ = 2 * (cLeib P.d (30 * P.d) * Ktr θ) * (C * (C * P.δ) ^ nB * (leafSizeProduct G₁ BT * csT)) *
          (G' * (G' * P.δ) ^ m₂ * (leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) * csB)) := by
          ring
      _ ≤ _ := hab
  · -- the top block is below `q`
    have hr₁lt : r₁ < q := lt_of_le_of_ne hr₁q htop
    have hE := couple_lower_kernelW P OT OC hAst hC hd hL hθ0 hδ H Bd F (timeBox (q : ℝ) q') (-(q : ℝ)) hT
      n .nil Xp LG rfl hsizeC hnN S₀ Sst ω c hpres Fl ann M Fu Mu hA
    have heq : ∀ ts ∈ timeBox (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        coupleKW P.L P.γ P.δ LG H (d5Mult Sst ω Fl ann M Fu Mu) (ts 0) (ts 1) k =
        coupleKW P.L P.γ P.δ LG (fun z => H (botAddr RegChain.nil.lonePath z)) (d5Mult Sst ω Fl ann M Fu Mu)
          ((layerAt LG ((0 : Fin 2), RegChain.nil.lonePath) : ℝ) + 1) (ts 1) k := by
      intro ts hts k _
      have ht0 : (q : ℝ) ≤ ts 0 := hts.1.1
      have hq1 : (r₁ : ℝ) + 1 ≤ q := by exact_mod_cast hr₁lt
      have hK : coupleKW P.L P.γ P.δ LG H (d5Mult Sst ω Fl ann M Fu Mu) (ts 0) (ts 1) k =
          coupleKW P.L P.γ P.δ LG H (d5Mult Sst ω Fl ann M Fu Mu) ((r₁ : ℝ) + 1) (ts 1) k :=
        coupleKW_upper_eq P.L P.γ P.δ LG H _ hfl (ts 1) k fun b hb => by
          have hroot : ([] : Path) ∈ (LG.garden.tree 0).nodes := TTree.nil_mem_nodes _
          have hu : Under ((0 : Fin 2), ([] : Path)) b.toNode.1 := ⟨hb.symm, List.nil_prefix⟩
          have hl := layerAt_le_of_under LG hroot b.toNode.2 hu
          rw [layerAt_node] at hl
          have : (LG.layer b.toNode : ℝ) ≤ r₁ := by exact_mod_cast hl
          exact ⟨by linarith, by linarith⟩
      simp only [RegChain.lonePath]
      rw [hK, hHe]
    refine (restr_congr (θ := θ) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) (timeBox (q : ℝ) q') Set.univ heq).trans_le
      (hE.trans ?_)
    simp only [RegChain.lonePath]
    rw [hBe]
    exact ENNReal.ofReal_le_ofReal (bound_mono_G n (by positivity) hGG' hδ hβ0)

/-- **Coherent couples with the D5 multiplier, all `q' ≤ q ≤ p`.** -/
theorem coupleKW_coherent_kernel {p q q' n : ℕ} (hqq : q' ≤ q) (hqp : q ≤ p) (hnN : n ≤ Nmax)
    (Q : RegCpl) (hsize : Q.size = 2 * n) (LG : LayeredGarden 2) (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (H : LeafProfiles 2 P.d) (Bd : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd)
    (Sst : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star P.d → ℂ)
    (c : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ Sst, IncTop.StarPresented (30 * P.d) (ω a) (c a))
    (Fl : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hA : A 2 LG.garden Fl M Fu Mu) :
    XNormRestr θ (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
      (fun ts k => coupleKW P.L P.γ P.δ LG H (d5Mult Sst ω Fl ann M Fu Mu) (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (treeG P.d θ C * (treeG P.d θ C * P.δ) ^ n *
        (leafSizeProduct LG Bd * ∏ a ∈ Sst, max (c a) 0)) := by
  obtain ⟨hCG', hGG', hG1⟩ := le_treeG hd hθ0 hC
  have hβ0 : 0 ≤ leafSizeProduct LG Bd * ∏ a ∈ Sst, max (c a) 0 :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg _ _)
  have hC0 : 0 ≤ C := by linarith
  rcases eq_or_lt_of_le hqq with heq | hlt
  · subst heq
    exact (coupleOracle_real OC hC hδ hnN Q hcoh.1 hsize LG hcoh.2.1 (coherentCouple_layer_eq hcoh) H Bd hH
      Sst ω c hpres Fl ann M Fu Mu hA).trans
      (ENNReal.ofReal_le_ofReal (bound_mono_G n hC0 hCG' hδ hβ0))
  · rw [XNormRestr_eq_rN]
    cases Q with
    | type2 Xp Xm Qlp =>
      exact coupleKW_type2_kernel P OT OC hAst hC hd hL hθ0 hθ1 hδ hlt hqp hnN Xp Xm Qlp hsize LG hcoh H Bd hH
        Sst ω c hpres Fl ann M Fu Mu hA
    | triv | type1 c' Q₁ Q₂ Q₃ =>
      all_goals
        have hwf := hcoh.1
        have hQ := hcoh.2.1
        have hlayq := layers_type1 hlt.le hcoh rfl
        have hplain : LG.garden.IsPlain := hQ.1.1
        have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b :=
          noFlowerParent_of_noFlower (not_flower_of_plain hplain)
        have hE := coupleOracle_real OC hC hδ hnN _ hwf hsize LG hQ hlayq H Bd hH Sst ω c hpres
          Fl ann M Fu Mu hA
        have hEb := coupleKW_bottom_kernel hd hL hθ0 hQ hH _ (norm_d5Mult_le Sst ω c hpres Fl ann M Fu Mu) hE
          (timeBox (q : ℝ) q') (-(q : ℝ)) (timeBox_shift_unit q q')
        have heq : ∀ ts ∈ timeBox (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)),
            coupleKW P.L P.γ P.δ LG H (d5Mult Sst ω Fl ann M Fu Mu) (ts 0) (ts 1) k =
              coupleKW P.L P.γ P.δ LG H (d5Mult Sst ω Fl ann M Fu Mu) (q' + 1) (ts 1) k := by
          intro ts hts k _
          have ht0 : (q : ℝ) ≤ ts 0 := hts.1.1
          have hq1 : (q' : ℝ) + 1 ≤ q := by exact_mod_cast hlt
          exact coupleKW_upper_eq P.L P.γ P.δ LG H _ hfl (ts 1) k fun b _ => by
            rw [hlayq b.toNode]
            exact ⟨by linarith, le_rfl⟩
        refine (restr_congr (θ := θ) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) (timeBox (q : ℝ) q') Set.univ heq).trans_le
          (hEb.trans (ENNReal.ofReal_le_ofReal ?_))
        have hK1 : 1 ≤ Ktr θ := one_le_Ktr hθ0
        calc Ktr θ * (C * (C * P.δ) ^ n * (leafSizeProduct LG Bd * ∏ a ∈ Sst, max (c a) 0))
            = (Ktr θ * C) * (C * P.δ) ^ n * (leafSizeProduct LG Bd * ∏ a ∈ Sst, max (c a) 0) := by ring
          _ ≤ treeG P.d θ C * (treeG P.d θ C * P.δ) ^ n * (leafSizeProduct LG Bd * ∏ a ∈ Sst, max (c a) 0) := by
              apply mul_le_mul_of_nonneg_right _ hβ0
              apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCG' hδ) n)
                (by positivity) (by linarith)
              have hLc : 1 ≤ cLeib P.d (30 * P.d) := one_le_cLeib hd _
              have : Ktr θ * C ≤ Ktr θ * cLeib P.d (30 * P.d) * C ^ 2 := by
                have h1 : Ktr θ * 1 * C ^ 1 ≤ Ktr θ * cLeib P.d (30 * P.d) * C ^ 2 :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hLc (by linarith)) (pow_le_pow_right₀ hC (by norm_num))
                    (by positivity) (by positivity)
                simpa using h1
              exact this.trans hGG'

end Gate

end WaveTurbulence.Flower.FiltCoh
