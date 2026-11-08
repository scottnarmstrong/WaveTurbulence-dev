/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermPerk
public import WaveTurbulence.Foundations.Flower.ProtPin.PieceStar
public import WaveTurbulence.Foundations.Flower.ProtPin.TermStarCut
public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiPiecesD5
public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiBound

/-! # D3 PROT-PIN: `term` with star weights and filters, one output

`StarMult LG X M CS`: at every terminal cut of the paired tree `X`, the multiplier `M` factors into a cut factor of
modulus `≤ Ca` and four pieces carrying D3's gate-form multipliers (presented stars, scales `≥ L`), with
`Ca · ∏ (piece star costs) ≤ CS`. `starMult_tree` proves it for D3's multiplier of a protected paired tree with
`CS = ∏_{a ∈ S} max (cω a) 0`. `term_star_perk` is `term_perk` with star weights and filters: the same cut, kink and
lattice argument, the pieces bounded by `tree_piece_star`/`couple_piece_star`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- D3's gate-form multiplier `starWeight S ω · filtWeight F 0 M · filtWeight Fu 0 Mu`. -/
def gateM {w d : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (F : Finset (GBranch G.tree)) (M : GBranch G.tree → ℝ) (Fu : Finset (GBranch G.tree))
    (Mu : GBranch G.tree → ℝ) (K : GNode G.tree → Mom d) : ℂ :=
  Flower.IncTop.starWeight S ω K * filtWeight F (fun _ => false) M K * filtWeight Fu (fun _ => false) Mu K

/-- Presented stars and scales `≥ L` on a garden. -/
def GateData {w d : ℕ} {G : Garden w} (L : ℝ) (S : Finset (GNode G.tree))
    (ω : GNode G.tree → Flower.IncTop.Star d → ℂ) (cω : GNode G.tree → ℝ) (F : Finset (GBranch G.tree))
    (M : GBranch G.tree → ℝ) (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) : Prop :=
  (∀ a ∈ S, Flower.IncTop.StarPresented (30 * d) (ω a) (cω a)) ∧ (∀ b ∈ F, L ≤ M b) ∧ (∀ b ∈ Fu, L ≤ Mu b)

/-- The star cost `∏_{a ∈ S} max (cω a) 0`. -/
def starCost {w : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) (cω : GNode G.tree → ℝ) : ℝ :=
  ∏ a ∈ S, max (cω a) 0

theorem starCost_nonneg' {w : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) (cω : GNode G.tree → ℝ) :
    0 ≤ starCost S cω :=
  Finset.prod_nonneg fun _ _ => le_max_right _ _

theorem prod_ofReal_starCost {w : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) (cω : GNode G.tree → ℝ) :
    ∏ a ∈ S, ENNReal.ofReal (cω a) = ENNReal.ofReal (starCost S cω) := by
  unfold starCost
  rw [ENNReal.ofReal_prod_of_nonneg fun _ _ => le_max_right _ _]
  exact Finset.prod_congr rfl fun a _ => by
    rcases le_total 0 (cω a) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]

/-- **A multiplier with star weights and filters at every terminal cut.** -/
def StarMult {d : ℕ} (L : ℝ) (LG : LayeredGarden 1) (X : RegChain) (Mt : (GNode LG.garden.tree → Mom d) → ℂ)
    (CS : ℝ) : Prop :=
  ∀ {Xp : RegChain} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain} {LGp LGi : LayeredGarden 1}
    {LGr LGg : LayeredGarden 2} (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg),
    appendChain Xp (cpair m Qr Qg inner) = X →
    ∃ (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ) (Ca : ℝ)
      (Sp : Finset (GNode LGp.garden.tree)) (ωp : GNode LGp.garden.tree → Flower.IncTop.Star d → ℂ)
      (cp : GNode LGp.garden.tree → ℝ) (Fp : Finset (GBranch LGp.garden.tree)) (Mp : GBranch LGp.garden.tree → ℝ)
      (Fup : Finset (GBranch LGp.garden.tree)) (Mup : GBranch LGp.garden.tree → ℝ)
      (Si : Finset (GNode LGi.garden.tree)) (ωi : GNode LGi.garden.tree → Flower.IncTop.Star d → ℂ)
      (ci : GNode LGi.garden.tree → ℝ) (Fi : Finset (GBranch LGi.garden.tree)) (Mi : GBranch LGi.garden.tree → ℝ)
      (Fui : Finset (GBranch LGi.garden.tree)) (Mui : GBranch LGi.garden.tree → ℝ)
      (Sr : Finset (GNode LGr.garden.tree)) (ωr : GNode LGr.garden.tree → Flower.IncTop.Star d → ℂ)
      (cr : GNode LGr.garden.tree → ℝ) (Fr : Finset (GBranch LGr.garden.tree)) (Mr : GBranch LGr.garden.tree → ℝ)
      (Fur : Finset (GBranch LGr.garden.tree)) (Mur : GBranch LGr.garden.tree → ℝ)
      (Sg : Finset (GNode LGg.garden.tree)) (ωg : GNode LGg.garden.tree → Flower.IncTop.Star d → ℂ)
      (cg : GNode LGg.garden.tree → ℝ) (Fg : Finset (GBranch LGg.garden.tree)) (Mg : GBranch LGg.garden.tree → ℝ)
      (Fug : Finset (GBranch LGg.garden.tree)) (Mug : GBranch LGg.garden.tree → ℝ),
      D.MultFactors Mt Mc (gateM Sp ωp Fp Mp Fup Mup) (gateM Si ωi Fi Mi Fui Mui) (gateM Sr ωr Fr Mr Fur Mur)
        (gateM Sg ωg Fg Mg Fug Mug) ∧
      GateData L Sp ωp cp Fp Mp Fup Mup ∧ GateData L Si ωi ci Fi Mi Fui Mui ∧ GateData L Sr ωr cr Fr Mr Fur Mur ∧
      GateData L Sg ωg cg Fg Mg Fug Mug ∧ 0 ≤ Ca ∧ (∀ A B, ‖Mc A B‖ ≤ Ca) ∧
      Ca * (starCost Sp cp * (starCost Si ci * (starCost Sr cr * starCost Sg cg))) ≤ CS

/-- **D3's multiplier of a protected paired tree** satisfies `StarMult` with the star cost of `S`. -/
theorem starMult_tree {d : ℕ} {L : ℝ} {LG : LayeredGarden 1} {X : RegChain} (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ) (cω : GNode LG.garden.tree → ℝ)
    (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, L ≤ Mu b)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ) (hind : TermChildIndicator X ind) :
    StarMult L LG X (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
      filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ)) (starCost S cω) := by
  intro Xp m Qr Qg inner LGp LGi LGr LGg D hX
  subst hX
  refine ⟨_, costB S cω D.aBr * costB S cω D.bBr,
    pullS D.ιP S, fun z => ω (D.ιP z), fun z => cω (D.ιP z), pullF D.βP F, fun y => M (D.βP y),
      pullF D.βP Fu, fun y => Mu (D.βP y),
    pullS D.ιI S, fun z => ω (D.ιI z), fun z => cω (D.ιI z), pullF D.βI F, fun y => M (D.βI y),
      pullF D.βI Fu, fun y => Mu (D.βI y),
    pullS D.ιR S, fun z => ω (D.ιR z), fun z => cω (D.ιR z), pullF D.βR F, fun y => M (D.βR y),
      pullF D.βR Fu, fun y => Mu (D.βR y),
    pullS D.ιG S, fun z => ω (D.ιG z), fun z => cω (D.ιG z), pullF D.βG F, fun y => M (D.βG y),
      pullF D.βG Fu, fun y => Mu (D.βG y),
    star_cut_mult D S ω F M Fu Mu ind hind,
    ⟨pull_pres _ hpres, pull_scale _ hM, pull_scale _ hMu⟩, ⟨pull_pres _ hpres, pull_scale _ hM, pull_scale _ hMu⟩,
    ⟨pull_pres _ hpres, pull_scale _ hM, pull_scale _ hMu⟩, ⟨pull_pres _ hpres, pull_scale _ hM, pull_scale _ hMu⟩,
    mul_nonneg (costB_nonneg _ _ _) (costB_nonneg _ _ _),
    fun A B => star_cut_Mc_le D S ω cω hpres F M Fu Mu ind hind.1 A B, le_of_eq ?_⟩
  unfold starCost
  rw [star_cut_cost D S cω]

/-! ### Pieces with multipliers -/

theorem cut_kernel_tree_m {d : ℕ} (L γ δ : ℝ) (LGt : LayeredGarden 1) {Y : RegChain}
    (hY : Y.DecodesTree LGt.garden) (Ht : LeafProfiles 1 d) (mt : (GNode LGt.garden.tree → Mom d) → ℂ)
    (T u : ℝ) (k : Mom d) :
    kernelProt L γ δ LGt Ht mt (fun _ => T) u (fun _ => none) k (fun _ => 0) 0 =
      Flower.Stage1W.kernelLeavesW L γ δ LGt Ht (fun _ => T) u k (fun _ => 0) 0 mt :=
  kernelProtBridge L γ δ LGt Ht mt (fun _ => T) u k (fun _ => 0) 0 (not_flowerParent_of_decodesTree_piece hY)

theorem cut_kernel_couple_m {d : ℕ} (L γ δ : ℝ) (LGc : LayeredGarden 2) {Q : RegCpl}
    (hQ : Q.Decodes LGc.garden) (Hc : LeafProfiles 2 d) (mc : (GNode LGc.garden.tree → Mom d) → ℂ)
    (c : Fin 2 → ℝ) (k : Mom d) :
    kernelProt L γ δ LGc Hc mc (fun y => c y.1.1) 0 (fun _ => none) k (fun _ => 0) 0 =
      Flower.Stage1W.kernelLeavesW L γ δ LGc Hc (fun b => if b.1.1 = 0 then c 0 else c 1) 0 k (fun _ => 0) 0 mc := by
  rw [kernelProtBridge L γ δ LGc Hc mc (fun y => c y.1.1) 0 k (fun _ => 0) 0
    (no_flowerParent_of_plain LGc.garden hQ.1.1)]
  have hc : ∀ j : Fin 2, c j = if j = 0 then c 0 else c 1 := by
    intro j
    fin_cases j <;> simp
  have hup : (fun y : GBranch LGc.garden.tree => c y.1.1) = fun b => if b.1.1 = 0 then c 0 else c 1 := by
    funext b
    exact hc b.1.1
  rw [hup]

/-- The real bound of a starred piece. -/
theorem piece_conv {P : WTParams} (hL0 : 0 ≤ P.L) (hrb : ∀ j g, 0 ≤ rb P j g) {w : ℕ} {G : Garden w}
    (Sx : Finset (GNode G.tree)) (cx : GNode G.tree → ℝ) (c' : ℝ) (j g : ℕ) (β : ℝ) :
    (∏ a ∈ Sx, ENNReal.ofReal (cx a)) * ENNReal.ofReal (P.L ^ c') * regBound P j g * ENNReal.ofReal β =
      ENNReal.ofReal (P.L ^ c' * rb P j g * β * starCost Sx cx) := by
  have hLc : 0 ≤ P.L ^ c' := Real.rpow_nonneg hL0 _
  rw [prod_ofReal_starCost, regBound_eq_rb, ← ENNReal.ofReal_mul (starCost_nonneg' _ _),
    ← ENNReal.ofReal_mul (mul_nonneg (starCost_nonneg' _ _) hLc),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (starCost_nonneg' _ _) hLc) (hrb j g))]
  congr 1
  ring

/-- **`term` at one output, with star weights and filters.** -/
theorem term_star_perk {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
      {Qr Qg : RegCpl} {inner : RegChain} (_D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
      (_hsh : ProtShape p (appendChain Xp (cpair m Qr Qg inner)) LG)
      (_hsz : (appendChain Xp (cpair m Qr Qg inner)).size = 2 * n)
      (_hamb : TreeAmb p (appendChain Xp (cpair m Qr Qg inner)) LG) {s : ℝ} (_hps : (p : ℝ) < s)
      (_hsp : s < p + 1) (t q' : ℝ) (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal)
      (_hH : LeafwiseControlled LG H B) (Mt : (GNode LG.garden.tree → Mom P.d) → ℂ) (CS : ℝ)
      (_hSM : StarMult P.L LG (appendChain Xp (cpair m Qr Qg inner)) Mt CS) (k : Mom P.d),
      rn θ (timeBoxGt p q') (fun ts => kernelProt P.L P.γ P.δ LG H Mt (fun _ => ts 0) (ts 1)
          (ProtCfg.term.fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
          (P.C₁ ^ 3 * rb P (n - 1) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
            leafSizeProduct LG B * CS) := by
  obtain ⟨Cc, hCc, hcore⟩ := term_core hθ0 (by linarith)
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  refine ⟨Cc * T4, ENNReal.mul_lt_top hCc (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top), ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LGp LGi LGr LGg Xp m Qr Qg inner D hsh hsz hamb s hps hsp t q' H B
    hH Mt CS hSM k
  obtain ⟨Mc, Ca, Sp, ωp, cp, Fp, Mp, Fup, Mup, Si, ωi, ci, Fi, Mi, Fui, Mui, Sr, ωr, cr, Fr, Mr, Fur, Mur,
    Sg, ωg, cg, Fg, Mg, Fug, Mug, hM, hGp, hGi, hGr, hGg, hCa, hMc, hcost⟩ := hSM D rfl
  have hsh' := hsh
  obtain ⟨hwf, hdec, hle, hch⟩ := hsh'
  obtain ⟨hwfp, hwfi, hwfr, hwfg⟩ := cut_wf D hwf
  obtain ⟨np, ni, nr, ng, hnp, hni, hnr, hng, hnsum⟩ := cut_sizes hsz
  obtain ⟨hlp, hlonep, hli, hlonei, hlr, hlg⟩ := cut_layers D hsh
  obtain ⟨hHp, hHi, hHr, hHg⟩ := cut_leafwise D hH
  obtain ⟨fP, fI, fR, fG⟩ := cut_flat D hsh hamb
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hd1 : 1 ≤ P.d := by have := K.hd; omega
  set ζ := LG.garden.sig 0 with hζ
  have hle_n : ∀ j, j ≤ n → j ≤ P.N (p + 1) ^ 4 := fun j hj => hj.trans hn
  -- the piece multipliers and their bounds
  set mp := gateM Sp ωp Fp Mp Fup Mup with hmp
  set mi := gateM Si ωi Fi Mi Fui Mui with hmi
  set mr := gateM Sr ωr Fr Mr Fur Mur with hmr
  set mg := gateM Sg ωg Fg Mg Fug Mug with hmg
  set Bp : ℝ := (∏ a ∈ Sp, max (cp a) 0) * FiltCoh.chiDSup ^ Fp.card * FiltCoh.chiDSup ^ Fup.card with hBp
  set Bi : ℝ := (∏ a ∈ Si, max (ci a) 0) * FiltCoh.chiDSup ^ Fi.card * FiltCoh.chiDSup ^ Fui.card with hBi
  set Br : ℝ := (∏ a ∈ Sr, max (cr a) 0) * FiltCoh.chiDSup ^ Fr.card * FiltCoh.chiDSup ^ Fur.card with hBr
  set Bg : ℝ := (∏ a ∈ Sg, max (cg a) 0) * FiltCoh.chiDSup ^ Fg.card * FiltCoh.chiDSup ^ Fug.card with hBg
  have hmpB : ∀ κ, ‖mp κ‖ ≤ Bp := FiltCoh.norm_d5Mult_le Sp ωp cp hGp.1 Fp (fun _ => false) Mp Fup Mup
  have hmiB : ∀ κ, ‖mi κ‖ ≤ Bi := FiltCoh.norm_d5Mult_le Si ωi ci hGi.1 Fi (fun _ => false) Mi Fui Mui
  have hmrB : ∀ κ, ‖mr κ‖ ≤ Br := FiltCoh.norm_d5Mult_le Sr ωr cr hGr.1 Fr (fun _ => false) Mr Fur Mur
  have hmgB : ∀ κ, ‖mg κ‖ ≤ Bg := FiltCoh.norm_d5Mult_le Sg ωg cg hGg.1 Fg (fun _ => false) Mg Fug Mug
  -- the pieces as time functions
  set Kp : (Fin 2 → ℝ) → ℂ := fun x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGp (cutHp H) (fun _ => x 0) (x 1) k
    (fun _ => 0) 0 mp with hKp
  set Ki : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGi (cutHi Xp m H)
    (fun _ => x 0) (x 1) (k + latticePoint P.L e.1.1) (fun _ => 0) 0 mi with hKi
  set fr : PairE m P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGr
    (cutHr Xp m inner ζ H) (fun y => if y.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 mr
    with hfr
  set fg : PairE m P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGg
    (cutHg Xp m inner ζ H) (fun y => if y.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0 mg
    with hfg
  set Kr : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x =>
    fr e (cupR m inner ζ (x 0) (x 1) 0) (cupR m inner ζ (x 0) (x 1) 1) with hKr
  set Kg : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x =>
    fg e (cupG m inner ζ (x 0) (x 1) 0) (cupG m inner ζ (x 0) (x 1) 1) with hKg
  set W : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x => Ki e x * (Kr e x * Kg e x) with hW
  -- continuity
  have hKpc : Continuous Kp := FiltCoh.continuous_treeKW_time P.L P.γ P.δ LGp (cutHp H) D.decP mp Bp hmpB k
    (summable_coset_piece hHp hL1 k)
  have hKic : ∀ e, Continuous (Ki e) := fun e =>
    FiltCoh.continuous_treeKW_time P.L P.γ P.δ LGi (cutHi Xp m H) D.decI mi Bi hmiB _
      (summable_coset_piece hHi hL1 _)
  have hor : ∀ {f : ℝ → ℝ → ℂ} (c : ℝ → ℝ → Fin 2 → ℝ),
      ((∀ u v, c u v 0 = u ∧ c u v 1 = v) ∨ (∀ u v, c u v 0 = v ∧ c u v 1 = u)) →
      Continuous (fun x : Fin 2 → ℝ => f (x 0) (x 1)) →
      Continuous (fun x : Fin 2 → ℝ => f (c (x 0) (x 1) 0) (c (x 0) (x 1) 1)) := by
    intro f c hc hf
    rcases hc with hc | hc
    · simpa only [(hc _ _).1, (hc _ _).2] using hf
    · simp only [(hc _ _).1, (hc _ _).2]
      exact hf.comp (show Continuous fun x : Fin 2 → ℝ => ![x 1, x 0] by fun_prop)
  have hKrc : ∀ e, Continuous (Kr e) := fun e =>
    hor (f := fr e) (cupR m inner ζ) (cupR_cases m inner ζ)
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGr (cutHr Xp m inner ζ H) D.decR.1.1 mr Br hmrB _
        (summable_coset_piece hHr hL1 _))
  have hKgc : ∀ e, Continuous (Kg e) := fun e =>
    hor (f := fg e) (cupG m inner ζ) (cupG_cases m inner ζ)
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGg (cutHg Xp m inner ζ H) D.decG.1.1 mg Bg hmgB _
        (summable_coset_piece hHg hL1 _))
  have hWc : ∀ e, Continuous (W e) := fun e => (hKic e).mul ((hKrc e).mul (hKgc e))
  -- the gates on the pieces
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hrb : ∀ j g, 0 ≤ rb P j g := fun j g => rb_nonneg hC1 K.hδ hL0 j g
  have hLc : 0 ≤ P.L ^ c' := Real.rpow_nonneg hL0 _
  have hls : ∀ {w : ℕ} (LGx : LayeredGarden w) (Bx : (Fin w × TTree.Path) → NNReal), 0 ≤ leafSizeProduct LGx Bx :=
    fun LGx Bx => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  set gp := LGp.incoherency (Xp.treeLinks (LGp.garden.sig 0)) with hgp
  set gi := LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) with hgi
  set gr := LGr.incoherency Qr.links with hgr
  set gg := LGg.incoherency Qg.links with hgg
  set bp : ℝ := P.L ^ c' * rb P np gp * leafSizeProduct LGp (cutBp B) * starCost Sp cp with hbp
  set bi : ℝ := P.L ^ c' * rb P ni gi * leafSizeProduct LGi (cutBi Xp m B) * starCost Si ci with hbi
  set br : ℝ := P.L ^ c' * rb P nr gr * leafSizeProduct LGr (cutBr Xp m inner ζ B) * starCost Sr cr with hbr
  set bg : ℝ := P.L ^ c' * rb P ng gg * leafSizeProduct LGg (cutBg Xp m inner ζ B) * starCost Sg cg with hbg
  have hKpb : rn θ (timeBoxGt p p) Kp ≤ ENNReal.ofReal bp := by
    rw [hbp, ← piece_conv hL0 hrb Sp cp c' np gp _]
    exact tree_piece_star K hp (hle_n np (by omega)) hθc Xp LGp hwfp hnp D.decP hlp hlonep fP Sp ωp cp hGp.1
      Fp Mp hGp.2.1 Fup Mup hGp.2.2 (cutHp H) (cutBp B) hHp k
  have hKib : ∀ e, rn θ (timeBoxGt p p) (Ki e) ≤ ENNReal.ofReal bi := fun e => by
    rw [hbi, ← piece_conv hL0 hrb Si ci c' ni gi _]
    exact tree_piece_star K hp (hle_n ni (by omega)) hθc inner LGi hwfi hni D.decI hli hlonei fI Si ωi ci hGi.1
      Fi Mi hGi.2.1 Fui Mui hGi.2.2 (cutHi Xp m H) (cutBi Xp m B) hHi _
  set Jr : PairE m P.d → ℝ := fun e => (jbr (k + latticePoint P.L e.1.2.1) ^ (30 * P.d))⁻¹ with hJr
  set Jg : PairE m P.d → ℝ := fun e => (jbr (k + latticePoint P.L e.1.2.2) ^ (30 * P.d))⁻¹ with hJg
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hKrb : ∀ e, rn θ (timeBoxGt p p) (Kr e) ≤ ENNReal.ofReal br * ENNReal.ofReal (Jr e) := fun e => by
    refine (rn_couple_oriented (fr e) (cupR m inner ζ) (cupR_cases m inner ζ)).trans ?_
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbr, ← piece_conv hL0 hrb Sr cr c' nr gr _]
    exact couple_piece_star K hp (hle_n nr (by omega)) hθc Qr LGr hwfr hnr D.decR hlr fR Sr ωr cr hGr.1
      Fr Mr hGr.2.1 Fur Mur hGr.2.2 _ _ hHr _
  have hKgb : ∀ e, rn θ (timeBoxGt p p) (Kg e) ≤ ENNReal.ofReal bg * ENNReal.ofReal (Jg e) := fun e => by
    refine (rn_couple_oriented (fg e) (cupG m inner ζ) (cupG_cases m inner ζ)).trans ?_
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbg, ← piece_conv hL0 hrb Sg cg c' ng gg _]
    exact couple_piece_star K hp (hle_n ng (by omega)) hθc Qg LGg hwfg hng D.decG hlg fG Sg ωg cg hGg.1
      Fg Mg hGg.2.1 Fug Mug hGg.2.2 _ _ hHg _
  have hfinr : ∀ e, rn θ (timeBoxGt p p) (Kr e) < ⊤ := fun e =>
    (hKrb e).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hfing : ∀ e, rn θ (timeBoxGt p p) (Kg e) < ⊤ := fun e =>
    (hKgb e).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hfini : ∀ e, rn θ (timeBoxGt p p) (Ki e) < ⊤ := fun e => (hKib e).trans_lt ENNReal.ofReal_lt_top
  have hRG : ∀ e, rn θ (timeBoxGt p p) (fun x => Kr e x * Kg e x) ≤
      ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) (Kr e) * rn θ (timeBoxGt p p) (Kg e) := fun e =>
    rn_mul_le hθ0 (timeBoxGt_cl p) (Kr e) (Kg e) (hKgc e) (hfinr e) (hfing e)
  have hfinRG : ∀ e, rn θ (timeBoxGt p p) (fun x => Kr e x * Kg e x) < ⊤ := fun e =>
    (hRG e).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfinr e)) (hfing e))
  have hWb : ∀ e, rn θ (timeBoxGt p p) (W e) ≤
      T4 * (ENNReal.ofReal bi * ((ENNReal.ofReal br * ENNReal.ofReal (Jr e)) *
        (ENNReal.ofReal bg * ENNReal.ofReal (Jg e)))) := fun e => by
    refine (rn_mul_le hθ0 (timeBoxGt_cl p) (Ki e) (fun x => Kr e x * Kg e x) ((hKrc e).mul (hKgc e))
      (hfini e) (hfinRG e)).trans ?_
    calc ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) (Ki e) * rn θ (timeBoxGt p p) (fun x => Kr e x * Kg e x)
        ≤ ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal bi *
            (ENNReal.ofReal (2 ^ θ) * (ENNReal.ofReal br * ENNReal.ofReal (Jr e)) *
              (ENNReal.ofReal bg * ENNReal.ofReal (Jg e))) :=
          mul_le_mul' (mul_le_mul' le_rfl (hKib e)) ((hRG e).trans (mul_le_mul' (mul_le_mul' le_rfl (hKrb e))
            (hKgb e)))
      _ = _ := by rw [hT4]; ring
  have hWfin : ∀ e, rn θ (timeBoxGt p p) (W e) < ⊤ := fun e =>
    (hWb e).trans_lt (by
      refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ?_ ?_)) <;>
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hKpfin : rn θ (timeBoxGt p p) Kp < ⊤ := hKpb.trans_lt ENNReal.ofReal_lt_top
  -- the cut identity on the box
  have hHs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom P.d,
      Summable fun j : Fin P.d → ℤ => |H ℓ.1 (k' + latticePoint P.L j)| :=
    fun ℓ hℓ k' => summable_coset_piece hH hL1 k' ℓ hℓ
  set CM : ℝ := max Ca (max Bp (max Bi (max Br Bg))) with hCM
  set c₀ : ℂ := (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
    (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) with hc₀
  set A : PairE m P.d → ℝ := fun e => cutFreq m ζ P.L P.γ P.δ k e with hA
  set c : PairE m P.d → ℂ := fun e => c₀ * (Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ)) with hc
  have hcut : ∀ ts ∈ timeBoxGt (p : ℝ) q',
      kernelProt P.L P.γ P.δ LG H Mt (fun _ => ts 0) (ts 1)
          (ProtCfg.term.fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k (fun _ => 0) 0 =
        ∑' e, c e * ∫ u in Ioo s (ts 0), cutMod (A e) s u * (Kp ![ts 0, u] * W e ![u, s]) := by
    intro ts hts
    rw [kernelProt_term_cut D P.L P.γ P.δ H hHs Mt Mc mp mi mr mg hM CM
      (fun A B => (hMc A B).trans (le_max_left _ _))
      (fun κ => (hmpB κ).trans ((le_max_left _ _).trans (le_max_right _ _)))
      (fun κ => (hmiB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
      (fun κ => (hmrB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _)))))
      (fun κ => (hmgB κ).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _)))))
      s t (ts 0) (ts 1) k, cutU_eq D hch hps hts.1.1.2, ← tsum_mul_left]
    refine tsum_congr fun e => ?_
    rw [show c e = c₀ * (Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ)) from rfl, mul_assoc c₀]
    congr 1
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
    simp only [cut_kernel_tree_m _ _ _ _ D.decP, cut_kernel_tree_m _ _ _ _ D.decI,
      cut_kernel_couple_m _ _ _ _ D.decR, cut_kernel_couple_m _ _ _ _ D.decG]
    rfl
  rw [rn_congr θ hcut]
  refine (hcore (PairE m P.d) p s q' hps hsp A c Kp W hKpc hWc hKpfin hWfin).trans ?_
  -- the exceptional sum
  set cc : ℝ := coupling P.d P.L P.γ P.δ ^ 2 with hcc
  have hcc0 : 0 ≤ cc := sq_nonneg _
  have hc0n : ‖c₀‖ = cc := norm_cutPrefactor hL0 K.hδ _ _
  have hce : ∀ e, ‖c e‖ₑ ≤ ENNReal.ofReal (cc * Ca) := fun e => by
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have hMe : ‖Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ)‖ ≤ Ca := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (hMc _ _) (abs_cutEps_le m e) (abs_nonneg _) hCa).trans (by rw [mul_one])
    calc ‖c e‖ = ‖c₀‖ * ‖Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ)‖ := norm_mul _ _
      _ ≤ cc * Ca := by rw [hc0n]; exact mul_le_mul_of_nonneg_left hMe hcc0
  set f : (Fin P.d → ℤ) → ℝ≥0∞ := fun y => ENNReal.ofReal (jbr (k + latticePoint P.L y) ^ (30 * P.d))⁻¹ with hf
  set Z : ℝ≥0∞ := ENNReal.ofReal (cc * Ca) * ENNReal.ofReal bp * T4 *
    (ENNReal.ofReal bi * ENNReal.ofReal br * ENNReal.ofReal bg) with hZ
  have hterm : ∀ e, ‖c e‖ₑ * (rn θ (timeBoxGt p p) Kp * rn θ (timeBoxGt p p) (W e)) ≤
      Z * (f e.1.2.1 * f e.1.2.2) := fun e => by
    calc ‖c e‖ₑ * (rn θ (timeBoxGt p p) Kp * rn θ (timeBoxGt p p) (W e))
        ≤ ENNReal.ofReal (cc * Ca) * (ENNReal.ofReal bp * (T4 * (ENNReal.ofReal bi * ((ENNReal.ofReal br *
            ENNReal.ofReal (Jr e)) * (ENNReal.ofReal bg * ENNReal.ofReal (Jg e)))))) :=
          mul_le_mul' (hce e) (mul_le_mul' hKpb (hWb e))
      _ = Z * (f e.1.2.1 * f e.1.2.2) := by rw [hZ, hf]; ring
  have hsum : ∑' e, ‖c e‖ₑ * (rn θ (timeBoxGt p p) Kp * rn θ (timeBoxGt p p) (W e)) ≤
      Z * (ENNReal.ofReal (latC P.d * P.L ^ P.d) * ENNReal.ofReal (latC P.d * P.L ^ P.d)) := by
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    rw [ENNReal.tsum_mul_left]
    refine mul_le_mul' le_rfl ((tsum_pairE_le m f).trans (mul_le_mul' ?_ ?_)) <;>
      exact tsum_decay_le hd1 hL1 k
  refine (mul_le_mul' le_rfl hsum).trans ?_
  -- the algebra
  have hlat0 : 0 ≤ latC P.d * P.L ^ P.d := mul_nonneg (latC_nonneg _) (pow_nonneg hL0 _)
  have hn1 : np + ni + nr + ng = n - 1 := by omega
  have hg : gp + gi + gr + gg = protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG :=
    (D.incoherency_cutTerm_of_chainIn hch).symm
  have hprod : bp * bi * br * bg = P.L ^ (4 * c') *
      (P.C₁ ^ 3 * rb P (n - 1) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) * leafSizeProduct LG B *
      (starCost Sp cp * (starCost Si ci * (starCost Sr cr * starCost Sg cg))) := by
    rw [hbp, hbi, hbr, hbg, cut_leafSize D B, ← hn1, ← hg]
    have h4 : P.L ^ (4 * c') = P.L ^ c' * P.L ^ c' * P.L ^ c' * P.L ^ c' := by
      rw [show 4 * c' = c' + c' + c' + c' by ring, Real.rpow_add (by linarith), Real.rpow_add (by linarith),
        Real.rpow_add (by linarith)]
    have h4r := rb_four (P := P) (by linarith : (0 : ℝ) < P.L) (n₁ := np) (n₂ := ni) (n₃ := nr) (n₄ := ng)
      (g₁ := gp) (g₂ := gi) (g₃ := gr) (g₄ := gg)
    rw [h4, show P.C₁ ^ 3 * rb P (np + ni + nr + ng) (gp + gi + gr + gg) =
        rb P np _ * rb P ni _ * rb P nr _ * rb P ng _ from by rw [h4r]; unfold rb; ring]
    ring
  have hsp0 := starCost_nonneg' Sp cp
  have hsi0 := starCost_nonneg' Si ci
  have hsr0 := starCost_nonneg' Sr cr
  have hsg0 := starCost_nonneg' Sg cg
  have hb0 : 0 ≤ bp := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) hsp0
  have hi0 : 0 ≤ bi := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) hsi0
  have hr0 : 0 ≤ br := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) hsr0
  have hg0 : 0 ≤ bg := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) hsg0
  have hccCa : 0 ≤ cc * Ca := mul_nonneg hcc0 hCa
  rw [hZ, ← ENNReal.ofReal_mul hccCa, ← ENNReal.ofReal_mul hi0, ← ENNReal.ofReal_mul (mul_nonneg hi0 hr0),
    ← ENNReal.ofReal_mul hlat0]
  have hrest : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
      (P.C₁ ^ 3 * rb P (n - 1) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
      leafSizeProduct LG B := by
    have := hrb (n - 1) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)
    have := hls LG B
    positivity
  calc Cc * (ENNReal.ofReal (cc * Ca * bp) * T4 * ENNReal.ofReal (bi * br * bg) *
        ENNReal.ofReal ((latC P.d * P.L ^ P.d) * (latC P.d * P.L ^ P.d)))
      = Cc * T4 * (ENNReal.ofReal (cc * Ca * bp) * ENNReal.ofReal (bi * br * bg) *
          ENNReal.ofReal ((latC P.d * P.L ^ P.d) * (latC P.d * P.L ^ P.d))) := by ring
    _ = Cc * T4 * ENNReal.ofReal (cc * Ca * bp * (bi * br * bg) *
          ((latC P.d * P.L ^ P.d) * (latC P.d * P.L ^ P.d))) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hccCa hb0), ← ENNReal.ofReal_mul
          (mul_nonneg (mul_nonneg hccCa hb0) (mul_nonneg (mul_nonneg hi0 hr0) hg0))]
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
        have e : cc * Ca * bp * (bi * br * bg) * ((latC P.d * P.L ^ P.d) * (latC P.d * P.L ^ P.d)) =
            coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
              (P.C₁ ^ 3 * rb P (n - 1) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
              leafSizeProduct LG B *
              (Ca * (starCost Sp cp * (starCost Si ci * (starCost Sr cr * starCost Sg cg)))) := by
          rw [hcc]
          linear_combination (coupling P.d P.L P.γ P.δ ^ 2 * Ca * (latC P.d * P.L ^ P.d) ^ 2) * hprod
        rw [e]
        exact mul_le_mul_of_nonneg_left hcost hrest

end WaveTurbulence.Flower.ProtPin
