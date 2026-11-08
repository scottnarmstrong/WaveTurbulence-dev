/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.RootRest
public import WaveTurbulence.Foundations.Flower.ProtPin.MirrorTri

/-! # D3 PROT-PIN: the root trace `trace` (P8) for protected paired trees, in `X^{θ,30d,0}`

The root is pinned at its own upper clock `T = ts 0` (`cfg_trace_fix`); D2c's root cut at `σ = T` (`pair_pack`,
`root_pack`) writes the kernel as `Σ'_e c_e ∫ e^{πiA_e(T-u)} Ks(u, ts 1) W_e(T, u) du` over `u ∈ (max(p, ts 1), T)`
(`Ks ≡ 1` without a suffix; with a suffix `Ks` vanishes for `u ≤ ts 1` and is port-independent below the layer):
the mirror operator on the triangle (`mirror_tri`, port layer `q' = p`) or with the lower limit at the layer
(`mirror_low`, `q' < p`). Closed by `final_pair` / `final_term`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem tri_sub_cell (p q' : ℝ) : timeBoxGt p q' ⊆ VineEstS3.FS.cell ![p, q'] := by
  intro ts hts i
  fin_cases i
  · simpa using hts.1.1
  · simpa using hts.1.2

theorem rn_one_lt_top (θ p : ℝ) : rn θ (timeBoxGt p p) (fun _ => (1 : ℂ)) < ⊤ :=
  (rn_const_le θ ![p, p] (tri_sub_cell p p) 1).trans_lt
    (ENNReal.mul_lt_top (by simp) (cutNormR_lt_top θ 2))

theorem rn_one_le (θ p : ℝ) : rn θ (timeBoxGt p p) (fun _ => (1 : ℂ)) ≤ cutNormR θ 2 :=
  (rn_const_le θ ![p, p] (tri_sub_cell p p) 1).trans (by simp)

theorem rootU0_eq_tr {LG : LayeredGarden 1} {m : MiniTreeCode} {inner : RegChain} {p : ℕ}
    (hlay : layerAt LG ((0 : Fin 1), bPath m inner) = p) {T σ : ℝ} (hT : T ≤ p + 1) (hσ : (p : ℝ) ≤ σ) :
    rootU0 LG m inner T T σ = Ioo σ T := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  ext u
  simp only [rootU0, hlay, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨-, -, -, h4, -, h6⟩
    exact ⟨h6, h4⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith, by linarith, h2, h2, h1⟩

theorem rootU0_eq_tr_low {LG : LayeredGarden 1} {m : MiniTreeCode} {inner : RegChain} {p : ℕ}
    (hlay : layerAt LG ((0 : Fin 1), bPath m inner) = p) {T σ : ℝ} (hT : T ≤ p + 1) (hσ : σ ≤ p) :
    rootU0 LG m inner T T σ = Ioo (p : ℝ) T := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  ext u
  simp only [rootU0, hlay, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, -, -, h4, -, -⟩
    exact ⟨h1, h4⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith, by linarith, h2, h2, by linarith⟩

theorem rootU_eq_tr {LG : LayeredGarden 1} {m : MiniTreeCode} {inner : RegChain} {p : ℕ}
    (hlay : layerAt LG ((0 : Fin 1), bPath m inner) = p) {T : ℝ} (hT : T ≤ p + 1) :
    rootU LG m inner T T = Ioo (p : ℝ) T := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  ext u
  simp only [rootU, hlay, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, -, -, h4, -⟩
    exact ⟨h1, h4⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith, by linarith, h2, h2⟩

/-- **(P8), one pair, every port layer, one output.** -/
theorem trace_perk_pair {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
      {inner : RegChain} (_C : CutTermData LG .nil m Qr Qg inner LGp LGi LGr LGg)
      (_hsh : ProtShape p (cpair m Qr Qg inner) LG) (_hsz : (cpair m Qr Qg inner).size = 2 * n)
      (_hamb : TreeAmb p (cpair m Qr Qg inner) LG) (s t : ℝ) (q' : ℕ) (_hq' : q' ≤ p)
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind : TermChildIndicator (cpair m Qr Qg inner) ind)
      (k : Mom P.d),
      rn θ (timeBoxGt p q') (fun ts => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.trace.fix (cpair m Qr Qg inner) s t (ts 0)) k (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (pairRb P c' n (protIncoh (cpair m Qr Qg inner) LG) (leafSizeProduct LG B)
          (starCost S cω)) := by
  obtain ⟨Ct, hCt, htri⟩ := mirror_tri hθ0 hθ1
  obtain ⟨Cl, hCl, hlow⟩ := mirror_low hθ0 hθ1
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have hT4f : T4 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨(Ct + Cl) * cutNormR θ 2 * T4, ENNReal.mul_lt_top (ENNReal.mul_lt_top
    (ENNReal.add_lt_top.2 ⟨hCt, hCl⟩) (cutNormR_lt_top θ 2)) hT4f, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LGp LGi LGr LGg m Qr Qg inner C hsh hsz hamb s t q' hq'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind k
  obtain ⟨c, A, W, hWc, hWfin, hsum, hroot, -⟩ := pair_pack hθ0 K hθc hp hn C hsh hsz hamb H B hH S ω cω hpres
    F M hM Fu Mu hMu ind hind k
  have D : PairOnly LG m Qr Qg inner LGi LGr LGg := PairOnly.of_cutTerm C
  have hlay := pair_b_layer D hsh.2.2.2
  set R : ℝ≥0∞ := ENNReal.ofReal (pairRb P c' n (protIncoh (cpair m Qr Qg inner) LG) (leafSizeProduct LG B)
    (starCost S cω)) with hR
  have hcfg : ∀ ts ∈ timeBoxGt (p : ℝ) q',
      kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.trace.fix (cpair m Qr Qg inner) s t (ts 0)) k (fun _ => 0) 0 =
        ∑' e, c e * ∫ u in rootU0 LG m inner (ts 0) (ts 0) (ts 1),
          rootPh (A e) (ts 0) u * ((fun _ => (1 : ℂ)) ![u, ts 1] * W e ![ts 0, u]) := by
    intro ts _
    rw [cfg_trace_fix, hroot (ts 0) (ts 0) (ts 1) le_rfl]
    simp only [one_mul]
  rw [rn_congr θ hcfg]
  have hS : rn θ (timeBoxGt (p : ℝ) p) (fun _ => (1 : ℂ)) * ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (p : ℝ) p) (W e) ≤
      cutNormR θ 2 * (T4 * R) := mul_le_mul' (rn_one_le θ p) hsum
  rcases Nat.lt_or_ge q' p with hlt | hge
  · -- `q' < p`
    have hq1 : (q' : ℝ) + 1 ≤ p := by exact_mod_cast hlt
    have hdom : ∀ ts ∈ timeBoxGt (p : ℝ) q',
        ∑' e, c e * ∫ u in rootU0 LG m inner (ts 0) (ts 0) (ts 1),
          rootPh (A e) (ts 0) u * ((fun _ => (1 : ℂ)) ![u, ts 1] * W e ![ts 0, u]) =
        ∑' e, c e * ∫ u in Ioo (p : ℝ) (ts 0),
          rootPh (A e) (ts 0) u * ((fun _ => (1 : ℂ)) ![u, (p : ℝ)] * W e ![ts 0, u]) := by
      intro ts hts
      rw [rootU0_eq_tr_low hlay hts.1.1.2 (by linarith [hts.1.2.2])]
    rw [rn_congr θ hdom]
    refine (hlow (PairE m P.d) p q' A c (fun _ => 1) W continuous_const hWc (rn_one_lt_top θ p) hWfin).trans ?_
    rw [mul_assoc]
    calc Cl * (rn θ (timeBoxGt (p : ℝ) p) (fun _ => (1 : ℂ)) * ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (p : ℝ) p) (W e))
        ≤ Cl * (cutNormR θ 2 * (T4 * R)) := mul_le_mul' le_rfl hS
      _ ≤ (Ct + Cl) * cutNormR θ 2 * T4 * R := by
          rw [show Cl * (cutNormR θ 2 * (T4 * R)) = Cl * cutNormR θ 2 * T4 * R by ring]
          exact mul_le_mul' (mul_le_mul' (mul_le_mul' le_add_self le_rfl) le_rfl) le_rfl
  · -- `q' = p`
    have hqp : q' = p := le_antisymm hq' hge
    subst hqp
    have hdom : ∀ ts ∈ timeBoxGt (q' : ℝ) q',
        ∑' e, c e * ∫ u in rootU0 LG m inner (ts 0) (ts 0) (ts 1),
          rootPh (A e) (ts 0) u * ((fun _ => (1 : ℂ)) ![u, ts 1] * W e ![ts 0, u]) =
        ∑' e, c e * ∫ u in Ioo (ts 1) (ts 0),
          rootPh (A e) (ts 0) u * ((fun _ => (1 : ℂ)) ![u, ts 1] * W e ![ts 0, u]) := by
      intro ts hts
      rw [rootU0_eq_tr hlay hts.1.1.2 hts.1.2.1]
    rw [rn_congr θ hdom]
    refine (htri (PairE m P.d) q' A c (fun _ => 1) W continuous_const hWc (rn_one_lt_top θ q') hWfin).trans ?_
    rw [mul_assoc]
    calc Ct * (rn θ (timeBoxGt (q' : ℝ) q') (fun _ => (1 : ℂ)) *
          ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (q' : ℝ) q') (W e))
        ≤ Ct * (cutNormR θ 2 * (T4 * R)) := mul_le_mul' le_rfl hS
      _ ≤ (Ct + Cl) * cutNormR θ 2 * T4 * R := by
          rw [show Ct * (cutNormR θ 2 * (T4 * R)) = Ct * cutNormR θ 2 * T4 * R by ring]
          exact mul_le_mul' (mul_le_mul' (mul_le_mul' le_self_add le_rfl) le_rfl) le_rfl

/-- **(P8) with a suffix, every port layer, one output** (`ind ≡ 1`). -/
theorem trace_perk_rest {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
      {inner rest : RegChain} (_D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg)
      (_hsh : ProtShape p (RegChain.pair m Qr Qg inner rest) LG)
      (_hsz : (RegChain.pair m Qr Qg inner rest).size = 2 * n)
      (_hamb : TreeAmb p (RegChain.pair m Qr Qg inner rest) LG) (s t : ℝ) (q' : ℕ) (_hq' : q' ≤ p)
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind1 : ∀ κ, ind κ = 1) (k : Mom P.d),
      rn θ (timeBoxGt p q') (fun ts => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.trace.fix (RegChain.pair m Qr Qg inner rest) s t (ts 0)) k
          (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (termRb P c' n (protIncoh (RegChain.pair m Qr Qg inner rest) LG) (leafSizeProduct LG B)
          (starCost S cω)) := by
  obtain ⟨Ct, hCt, htri⟩ := mirror_tri hθ0 hθ1
  obtain ⟨Cl, hCl, hlowm⟩ := mirror_low hθ0 hθ1
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have hT4f : T4 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨(Ct + Cl) * T4, ENNReal.mul_lt_top (ENNReal.add_lt_top.2 ⟨hCt, hCl⟩) hT4f, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LGZ LGi LGs LGr LGg m Qr Qg inner rest D hsh hsz hamb s t q' hq'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind1 k
  obtain ⟨c, A, W, Ks, hWc, hWfin, hKc, hKfin, hvan, hlow, hsum, hroot⟩ :=
    root_pack hθ0 K hθc hp hn D hsh hsz hamb H B hH S ω cω hpres F M hM Fu Mu hMu ind hind1 k
  have hlay : layerAt LG ((0 : Fin 1), bPath m inner) = p := by
    rw [← D.layer_bR]
    have hbp : D.bR.1.2 = bPath m inner := congrArg Prod.snd D.bR_path
    refine hsh.2.2.2 D.bR (Nat.lt_one_iff.mp D.bR.1.1.isLt) ?_ ?_
    · rw [hbp, root_lonePath]; exact List.prefix_append _ _
    · rw [hbp, root_lonePath]; simp
  set R : ℝ≥0∞ := ENNReal.ofReal (termRb P c' n (protIncoh (RegChain.pair m Qr Qg inner rest) LG)
    (leafSizeProduct LG B) (starCost S cω)) with hR
  have hcfg : ∀ ts ∈ timeBoxGt (p : ℝ) q',
      kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.trace.fix (RegChain.pair m Qr Qg inner rest) s t (ts 0)) k
          (fun _ => 0) 0 =
        ∑' e, c e * ∫ u in Ioo (p : ℝ) (ts 0), rootPh (A e) (ts 0) u * (Ks ![u, ts 1] * W e ![ts 0, u]) := by
    intro ts hts
    rw [cfg_trace_fix, hroot (ts 0) (ts 0) (ts 1) le_rfl, rootU_eq_tr hlay hts.1.1.2]
  rw [rn_congr θ hcfg]
  rcases Nat.lt_or_ge q' p with hlt | hge
  · -- `q' < p`
    have hq1 : (q' : ℝ) + 1 ≤ p := by exact_mod_cast hlt
    have hdom : ∀ ts ∈ timeBoxGt (p : ℝ) q',
        ∑' e, c e * ∫ u in Ioo (p : ℝ) (ts 0), rootPh (A e) (ts 0) u * (Ks ![u, ts 1] * W e ![ts 0, u]) =
        ∑' e, c e * ∫ u in Ioo (p : ℝ) (ts 0), rootPh (A e) (ts 0) u * (Ks ![u, (p : ℝ)] * W e ![ts 0, u]) := by
      intro ts hts
      have hσ : ts 1 ≤ p := by linarith [hts.1.2.2]
      refine tsum_congr fun e => ?_
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
      rw [hlow u (ts 1) hσ]
    rw [rn_congr θ hdom]
    refine (hlowm (PairE m P.d) p q' A c Ks W hKc hWc hKfin hWfin).trans ?_
    rw [mul_assoc]
    calc Cl * (rn θ (timeBoxGt (p : ℝ) p) Ks * ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (p : ℝ) p) (W e))
        ≤ Cl * (T4 * R) := mul_le_mul' le_rfl hsum
      _ ≤ (Ct + Cl) * T4 * R := by
          rw [show Cl * (T4 * R) = Cl * T4 * R by ring]
          exact mul_le_mul' (mul_le_mul' le_add_self le_rfl) le_rfl
  · -- `q' = p`
    have hqp : q' = p := le_antisymm hq' hge
    subst hqp
    have hdom : ∀ ts ∈ timeBoxGt (q' : ℝ) q',
        ∑' e, c e * ∫ u in Ioo (q' : ℝ) (ts 0), rootPh (A e) (ts 0) u * (Ks ![u, ts 1] * W e ![ts 0, u]) =
        ∑' e, c e * ∫ u in Ioo (ts 1) (ts 0), rootPh (A e) (ts 0) u * (Ks ![u, ts 1] * W e ![ts 0, u]) := by
      intro ts hts
      have hσ : (q' : ℝ) ≤ ts 1 := hts.1.2.1
      refine tsum_congr fun e => ?_
      congr 1
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
        (fun u hu => ⟨by linarith [hu.1], hu.2⟩) fun u hu => ?_
      have hu1 : u ≤ ts 1 := by
        by_contra hc
        exact hu.2 ⟨lt_of_not_ge hc, hu.1.2⟩
      rw [hvan ![u, ts 1] (by simpa using hu1), zero_mul, mul_zero]
    rw [rn_congr θ hdom]
    refine (htri (PairE m P.d) q' A c Ks W hKc hWc hKfin hWfin).trans ?_
    rw [mul_assoc]
    calc Ct * (rn θ (timeBoxGt (q' : ℝ) q') Ks * ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (q' : ℝ) q') (W e))
        ≤ Ct * (T4 * R) := mul_le_mul' le_rfl hsum
      _ ≤ (Ct + Cl) * T4 * R := by
          rw [show Ct * (T4 * R) = Ct * T4 * R by ring]
          exact mul_le_mul' (mul_le_mul' le_self_add le_rfl) le_rfl

end WaveTurbulence.Flower.ProtPin
