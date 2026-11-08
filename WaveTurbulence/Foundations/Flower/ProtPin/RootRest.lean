/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.RootPack

/-! # D3 PROT-PIN: (P1) with a suffix (`rest ≠ nil`), every port layer, in `X^{θ,30d,0}`

On the R176 box the (P1) kernel is `σ ↦ Σ'_e c_e ∫_{Ioo p t} e^{πiA_e(t-u)} Ks(u, σ) W_e(t, u) du` (`root_pack`, root
at `t`, port clock `σ = ts 1`):
* `q' = p`: `Ks(u, σ) = 0` for `u ≤ σ`, so the integral is over `Ioo σ t`; `mirror_kink2` (the mirrored kink with the
  two-variable suffix factor: reflection, `kink_restr` at `(-p-1, -t)` with
  `h(T', v) = Ks(-v, -T') · W(t, -v)`, the swap and reflection of `Ks`, the trace of `W`);
* `q' < p`: `Ks(u, σ) = Ks(u, p)`, a constant, bounded pointwise.
`root_final_rest` closes it with `final_term` (four pieces, one cut). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The swapped reflection of a function on the triangle. -/
theorem rn_swapneg_le (θ : ℝ) (p s : ℝ) (Ks : (Fin 2 → ℝ) → ℂ) :
    rn θ (triS (-p - 1) s) (fun x => Ks ![-(x 1), -(x 0)]) ≤ rn θ (timeBoxGt p p) Ks := by
  have e : (fun x : Fin 2 → ℝ => Ks ![-(x 1), -(x 0)]) =
      fun x => (fun y => Ks (-y)) (ConjCoh.permT swap2 x) := by
    funext x
    congr 1
    ext i
    fin_cases i <;> simp [permT_swap2_apply]
  rw [e]
  refine (rn_swap θ (triS (-p - 1) s) (fun y => Ks (-y))).le.trans ?_
  refine rn_comp_neg_le θ (fun y hy => ?_) Ks
  have hy' : ConjCoh.permT swap2 y ∈ triS (-p - 1) s := hy
  rw [permT_swap2_apply] at hy'
  obtain ⟨⟨h0, h1⟩, h2, h3⟩ := hy'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Icc] at h0 h1 h2 h3
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show (-y) 0 ∈ Icc (p : ℝ) (p + 1)
    rw [Pi.neg_apply]; constructor <;> linarith
  · show (-y) 1 ∈ Icc (p : ℝ) (p + 1)
    rw [Pi.neg_apply]; constructor <;> linarith
  · show (-y) 1 < (-y) 0
    simp only [Pi.neg_apply]; linarith

/-- **The mirrored kink with a suffix factor.** -/
theorem mirror_kink2 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p t : ℝ), p < t → t < p + 1 →
      ∀ (A : ι → ℝ) (c : ι → ℂ) (Ks : (Fin 2 → ℝ) → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ), Continuous Ks →
      (∀ i, Continuous (W i)) → rn θ (timeBoxGt p p) Ks < ⊤ →
      (∀ i, rn θ (timeBoxGt p p) (W i) < ⊤) → ∀ {B : Set (Fin 2 → ℝ)}, B ⊆ timeBox p p →
      rn θ B (fun ts => ∑' i, c i * ∫ u in Ioo (ts 1) t, rootPh (A i) t u * (Ks ![u, ts 1] * W i ![t, u])) ≤
        C * (rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) := by
  obtain ⟨Ck, hCk, hK⟩ := kink_restr hθ0 hθ1
  set Ct := Regref.traceConst (r := 2) θ VineEstS3.chiUnit with hCt
  refine ⟨cutNorm θ * (ENNReal.ofReal Ck * (ENNReal.ofReal (2 ^ θ) * Ct)), ENNReal.mul_lt_top (cutNorm_lt_top θ)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (traceConst_lt_top θ))),
    ?_⟩
  intro ι _ p t hpt htp A c Ks W hKc hWc hKfin hWfin B hB
  set Ks' : (Fin 2 → ℝ) → ℂ := fun x => Ks ![-(x 1), -(x 0)] with hKs'
  set W' : ι → (Fin 2 → ℝ) → ℂ := fun i x => W i (-(Function.update x 0 (-t))) with hW'
  set h : ι → (Fin 2 → ℝ) → ℂ := fun i x => Ks' x * W' i x with hh
  have hKc' : Continuous Ks' := hKc.comp (by fun_prop)
  have hWc' : ∀ i, Continuous (W' i) := fun i =>
    (hWc i).comp (continuous_neg.comp (continuous_id.update 0 continuous_const))
  have hhc : ∀ i, Continuous (h i) := fun i => hKc'.mul (hWc' i)
  -- the trace of the reflected `W_i`
  have hWb : ∀ i, rn θ (triS (-p - 1) (-t)) (W' i) ≤ Ct * rn θ (timeBoxGt p p) (W i) := fun i => by
    refine (rn_trace hθ0 (fun _ => -p - 1) (B := Neg.neg ⁻¹' timeBoxGt p p) ?_ (fun y => W i (-y))
      ((hWc i).comp continuous_neg) 0 (-t) ?_).trans ?_
    · intro x hx j
      fin_cases j
      · exact hx.1.1
      · exact hx.1.2
    · intro x hx
      have e0 : (-(Function.update x 0 (-t))) 0 = t := by simp
      have e1 : (-(Function.update x 0 (-t))) 1 = -(x 1) := by simp
      have hx1 := hx.1.2
      have hx2 := hx.2.1
      have hmem : -(Function.update x 0 (-t)) ∈ timeBoxGt p p := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [e0]; exact ⟨hpt.le, htp.le⟩
        · rw [e1]; exact ⟨by linarith [hx1.2], by linarith [hx1.1]⟩
        · rw [e0, e1]; linarith
      have hcl : Function.update x 0 (-t) ∈
          ⇑(Homeomorph.neg (Fin 2 → ℝ)) ⁻¹' closure (interior (timeBoxGt p p)) := timeBoxGt_cl p _ hmem
      rw [Homeomorph.preimage_closure, Homeomorph.preimage_interior] at hcl
      exact hcl
    · exact mul_le_mul' le_rfl (rn_comp_neg_le θ (fun y hy => hy) (W i))
  have hKb : rn θ (triS (-p - 1) (-t)) Ks' ≤ rn θ (timeBoxGt p p) Ks := rn_swapneg_le θ p (-t) Ks
  have hWfin' : ∀ i, rn θ (triS (-p - 1) (-t)) (W' i) < ⊤ := fun i =>
    (hWb i).trans_lt (ENNReal.mul_lt_top (traceConst_lt_top θ) (hWfin i))
  have hhb : ∀ i, rn θ (triS (-p - 1) (-t)) (h i) ≤
      ENNReal.ofReal (2 ^ θ) * Ct * (rn θ (timeBoxGt p p) Ks * rn θ (timeBoxGt p p) (W i)) := fun i => by
    refine (rn_mul_le hθ0 (triS_closure _ _) Ks' (W' i) (hWc' i) (hKb.trans_lt hKfin) (hWfin' i)).trans ?_
    calc ENNReal.ofReal (2 ^ θ) * rn θ (triS (-p - 1) (-t)) Ks' * rn θ (triS (-p - 1) (-t)) (W' i)
        ≤ ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) Ks * (Ct * rn θ (timeBoxGt p p) (W i)) :=
          mul_le_mul' (mul_le_mul' le_rfl hKb) (hWb i)
      _ = _ := by ring
  have hfin : ∀ i, rn θ (triS (-p - 1) (-t)) (h i) < ⊤ := fun i =>
    (hhb i).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (traceConst_lt_top θ))
      (ENNReal.mul_lt_top hKfin (hWfin i)))
  set Gk : (Fin 1 → ℝ) → ℂ := fun T => ∑' i, c i * ∫ v in Ioo (-t) (T 0), cutMod (A i) (-t) v * h i ![T 0, v]
    with hGk
  have hGkb := hK ι (-p - 1) (-t) (by linarith) (by linarith) A c h hhc hfin
  have hf : ∀ y : Fin 1 → ℝ, (∑' i, c i * ∫ u in Ioo (y 0) t, rootPh (A i) t u * (Ks ![u, y 0] * W i ![t, u])) =
      Gk (-y) := by
    intro y
    simp only [hGk, Pi.neg_apply]
    refine tsum_congr fun i => ?_
    congr 1
    rw [integral_Ioo_neg]
    refine setIntegral_congr_fun measurableSet_Ioo fun v _ => ?_
    rw [rootPh_neg]
    congr 1
    simp only [hh, hKs', hW']
    congr 1
    · congr 1
      ext j
      fin_cases j <;> simp
    · congr 1
      ext j
      fin_cases j <;> simp
  calc rn θ B (fun ts => ∑' i, c i * ∫ u in Ioo (ts 1) t, rootPh (A i) t u * (Ks ![u, ts 1] * W i ![t, u]))
      ≤ cutNorm θ * rn θ (win p)
          (fun y => ∑' i, c i * ∫ u in Ioo (y 0) t, rootPh (A i) t u * (Ks ![u, y 0] * W i ![t, u])) :=
        rn_lift2 hθ0 p p hB
          (fun y => ∑' i, c i * ∫ u in Ioo (y 0) t, rootPh (A i) t u * (Ks ![u, y 0] * W i ![t, u]))
    _ = cutNorm θ * rn θ (win p) (fun y => Gk (-y)) := by rw [funext hf]
    _ ≤ cutNorm θ * rn θ (win (-p - 1)) Gk := by
        refine mul_le_mul' le_rfl (rn_comp_neg_le θ (fun y hy => ?_) Gk)
        have h1 := hy.1
        have h2 := hy.2
        show (-y) 0 ∈ Icc (-p - 1) (-p - 1 + 1)
        rw [Pi.neg_apply]
        exact ⟨by linarith, by linarith⟩
    _ ≤ cutNorm θ * (ENNReal.ofReal Ck * ∑' i, ‖c i‖ₑ * rn θ (triS (-p - 1) (-t)) (h i)) :=
        mul_le_mul' le_rfl hGkb
    _ ≤ cutNorm θ * (ENNReal.ofReal Ck * ∑' i, ‖c i‖ₑ *
          (ENNReal.ofReal (2 ^ θ) * Ct * (rn θ (timeBoxGt p p) Ks * rn θ (timeBoxGt p p) (W i)))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun i => mul_le_mul' le_rfl (hhb i)))
    _ = cutNorm θ * (ENNReal.ofReal Ck * (ENNReal.ofReal (2 ^ θ) * Ct)) *
          (rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) := by
        rw [show (fun i => ‖c i‖ₑ * (ENNReal.ofReal (2 ^ θ) * Ct *
            (rn θ (timeBoxGt p p) Ks * rn θ (timeBoxGt p p) (W i)))) =
          fun i => (ENNReal.ofReal (2 ^ θ) * Ct * rn θ (timeBoxGt p p) Ks) *
            (‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) from funext fun i => by ring, ENNReal.tsum_mul_left]
        ring

/-- **Pointwise bound of a root integral with a suffix factor at the layer.** -/
theorem enorm_rootInt2_le {θ : ℝ} (hθ0 : 0 ≤ θ) {ι : Type*} {p t : ℝ} (hpt : p ≤ t) (htp : t ≤ p + 1)
    (A : ι → ℝ) (c : ι → ℂ) (Ks : (Fin 2 → ℝ) → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ) (hKc : Continuous Ks)
    (hWc : ∀ i, Continuous (W i)) :
    ‖∑' i, c i * ∫ u in Ioo p t, rootPh (A i) t u * (Ks ![u, p] * W i ![t, u])‖ₑ ≤
      rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) := by
  rw [← ENNReal.tsum_mul_left]
  refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun i => ?_)
  rw [enorm_mul, mul_left_comm]
  refine mul_le_mul' le_rfl ?_
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hpt' : ∀ u ∈ Ioo p t, ‖rootPh (A i) t u * (Ks ![u, p] * W i ![t, u])‖ₑ ≤
      rn θ (timeBoxGt p p) Ks * rn θ (timeBoxGt p p) (W i) := by
    intro u hu
    rw [enorm_mul, ← ofReal_norm, norm_rootPh, ENNReal.ofReal_one, one_mul, enorm_mul]
    have hm1 : (![u, p] : Fin 2 → ℝ) ∈ timeBoxGt p p := by
      refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> simp <;> linarith [hu.1, hu.2]
    have hm2 : (![t, u] : Fin 2 → ℝ) ∈ timeBoxGt p p := by
      refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> simp <;> linarith [hu.1, hu.2]
    exact mul_le_mul' (enorm_le_rn hθ0 (timeBoxGt_cl p) hKc hm1) (enorm_le_rn hθ0 (timeBoxGt_cl p) (hWc i) hm2)
  calc ∫⁻ u in Ioo p t, ‖rootPh (A i) t u * (Ks ![u, p] * W i ![t, u])‖ₑ
      ≤ ∫⁻ _ in Ioo p t, rn θ (timeBoxGt p p) Ks * rn θ (timeBoxGt p p) (W i) :=
        setLIntegral_mono' measurableSet_Ioo hpt'
    _ = rn θ (timeBoxGt p p) Ks * rn θ (timeBoxGt p p) (W i) * volume (Ioo p t) := setLIntegral_const _ _
    _ ≤ rn θ (timeBoxGt p p) Ks * rn θ (timeBoxGt p p) (W i) * 1 := by
        refine mul_le_mul' le_rfl ?_
        rw [Real.volume_Ioo, ENNReal.ofReal_le_one]
        linarith
    _ = _ := mul_one _

/-- The root range on the R176 box. -/
theorem rootU_eq_box {LG : LayeredGarden 1} {m : MiniTreeCode} {inner : RegChain} {p : ℕ}
    (hlay : layerAt LG ((0 : Fin 1), bPath m inner) = p) {t T : ℝ} (htp : t < p + 1) (hT : t ≤ T) :
    rootU LG m inner T t = Ioo (p : ℝ) t := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  ext u
  simp only [rootU, hlay, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, -, -, -, h5⟩
    exact ⟨h1, h5⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith, by linarith, by linarith, h2⟩

variable {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner rest : RegChain}

/-- **(P1) with a suffix, every port layer, one output.** -/
theorem root_perk_rest {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
      {inner rest : RegChain} (_D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg)
      (_hsh : ProtShape p (RegChain.pair m Qr Qg inner rest) LG)
      (_hsz : (RegChain.pair m Qr Qg inner rest).size = 2 * n)
      (_hamb : TreeAmb p (RegChain.pair m Qr Qg inner rest) LG) {t : ℝ} (_hpt : (p : ℝ) < t) (_htp : t < p + 1)
      (s : ℝ) (q' : ℕ) (_hq' : q' ≤ p)
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind1 : ∀ κ, ind κ = 1) (k : Mom P.d),
      rn θ (ProtCfg.root.box (RegChain.pair m Qr Qg inner rest) t p q') (fun ts => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.root.fix (RegChain.pair m Qr Qg inner rest) s t (ts 0)) k
          (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (termRb P c' n (protIncoh (RegChain.pair m Qr Qg inner rest) LG) (leafSizeProduct LG B)
          (starCost S cω)) := by
  obtain ⟨Cm, hCm, hmk⟩ := mirror_kink2 hθ0 (by linarith)
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have hT4f : T4 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨(Cm + cutNormR θ 2) * T4, ENNReal.mul_lt_top (ENNReal.add_lt_top.2 ⟨hCm, cutNormR_lt_top θ 2⟩) hT4f, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LGZ LGi LGs LGr LGg m Qr Qg inner rest D hsh hsz hamb t hpt htp s
    q' hq' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind1 k
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
  have hcfg : ∀ ts ∈ ProtCfg.root.box (RegChain.pair m Qr Qg inner rest) t p q',
      kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.root.fix (RegChain.pair m Qr Qg inner rest) s t (ts 0)) k (fun _ => 0) 0 =
        ∑' e, c e * ∫ u in Ioo (p : ℝ) t, rootPh (A e) t u * (Ks ![u, ts 1] * W e ![t, u]) := by
    intro ts hts
    rw [box_root] at hts
    rw [cfg_root_fix, hroot (ts 0) t (ts 1) hts.2, rootU_eq_box hlay htp hts.2]
  rw [rn_congr θ hcfg]
  rcases Nat.lt_or_ge q' p with hlt | hge
  · -- `q' < p`: a constant
    have hq1 : (q' : ℝ) + 1 ≤ p := by exact_mod_cast hlt
    have hconst : ∀ ts ∈ ProtCfg.root.box (RegChain.pair m Qr Qg inner rest) t p q',
        ∑' e, c e * ∫ u in Ioo (p : ℝ) t, rootPh (A e) t u * (Ks ![u, ts 1] * W e ![t, u]) =
          ∑' e, c e * ∫ u in Ioo (p : ℝ) t, rootPh (A e) t u * (Ks ![u, p] * W e ![t, u]) := by
      intro ts hts
      rw [box_root] at hts
      have hσ : ts 1 ≤ p := by linarith [hts.1.1.2.2]
      refine tsum_congr fun e => ?_
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
      rw [hlow u (ts 1) hσ]
    rw [rn_congr θ hconst, box_root]
    refine (rn_const_le θ ![(p : ℝ), (q' : ℝ)] (rootBox_sub_cell (p : ℝ) q' t) _).trans ?_
    refine (mul_le_mul' (enorm_rootInt2_le hθ0 hpt.le htp.le A c Ks W hKc hWc) le_rfl).trans ?_
    calc (rn θ (timeBoxGt (p : ℝ) p) Ks * ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (p : ℝ) p) (W e)) * cutNormR θ 2
        ≤ T4 * R * cutNormR θ 2 := mul_le_mul' hsum le_rfl
      _ ≤ (Cm + cutNormR θ 2) * T4 * R := by
          rw [show T4 * R * cutNormR θ 2 = cutNormR θ 2 * T4 * R by ring]
          exact mul_le_mul' (mul_le_mul' le_add_self le_rfl) le_rfl
  · -- `q' = p`: the mirrored kink with the suffix
    have hqp : q' = p := le_antisymm hq' hge
    subst hqp
    have hdom : ∀ ts ∈ ProtCfg.root.box (RegChain.pair m Qr Qg inner rest) t q' q',
        ∑' e, c e * ∫ u in Ioo (q' : ℝ) t, rootPh (A e) t u * (Ks ![u, ts 1] * W e ![t, u]) =
          ∑' e, c e * ∫ u in Ioo (ts 1) t, rootPh (A e) t u * (Ks ![u, ts 1] * W e ![t, u]) := by
      intro ts hts
      rw [box_root] at hts
      have hσ : (q' : ℝ) ≤ ts 1 := hts.1.1.2.1
      refine tsum_congr fun e => ?_
      congr 1
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
        (fun u hu => ⟨by linarith [hu.1], hu.2⟩) fun u hu => ?_
      have hu1 : u ≤ ts 1 := by
        by_contra hc
        exact hu.2 ⟨lt_of_not_ge hc, hu.1.2⟩
      rw [hvan ![u, ts 1] (by simpa using hu1), zero_mul, mul_zero]
    rw [rn_congr θ hdom]
    have hsub : ProtCfg.root.box (RegChain.pair m Qr Qg inner rest) t q' q' ⊆ timeBox (q' : ℝ) q' := by
      rw [box_root]
      exact fun x hx => hx.1.1
    refine (hmk (PairE m P.d) q' t hpt htp A c Ks W hKc hWc hKfin hWfin hsub).trans ?_
    calc Cm * (rn θ (timeBoxGt (q' : ℝ) q') Ks * ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (q' : ℝ) q') (W e))
        ≤ Cm * (T4 * R) := mul_le_mul' le_rfl hsum
      _ ≤ (Cm + cutNormR θ 2) * T4 * R := by
          rw [mul_assoc (Cm + cutNormR θ 2) T4 R]
          exact mul_le_mul' le_self_add le_rfl

/-- **(P1) with a suffix in `X^{θ,30d,0}`** (R176 box, stars, filters; `ind ≡ 1`). -/
theorem root_final_rest {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' c CL : ℝ}
      (_hθc : PieceLoss P θ c') (_hc : 31 * (P.d : ℝ) + 4 * c' + 2 ≤ c) (_hCL : 0 ≤ CL)
      (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d)
        (F : (Fin r → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
        XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
      (_hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
      {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
      {inner rest : RegChain} (_D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg)
      (_hsh : ProtShape p (RegChain.pair m Qr Qg inner rest) LG)
      (_hsz : (RegChain.pair m Qr Qg inner rest).size = 2 * n)
      (_hamb : TreeAmb p (RegChain.pair m Qr Qg inner rest) LG) {t : ℝ} (_hpt : (p : ℝ) < t) (_htp : t < p + 1)
      (s : ℝ) (q' : ℕ) (_hq' : q' ≤ p)
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind1 : ∀ κ, ind κ = 1) (b₀ c₀ : Mom P.d),
      XNormRestr θ (30 * P.d) 0 (ProtCfg.root.box (RegChain.pair m Qr Qg inner rest) t p q')
        (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.root.fix (RegChain.pair m Qr Qg inner rest) s t (ts 0)) k
          (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) *
          regBound P n (protIncoh (RegChain.pair m Qr Qg inner rest) LG) *
            ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨C, hC, hperk⟩ := root_perk_rest hθ0 hθ1
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' c CL hθc hc hCL hLOE hbig p hp n hn LG LGZ LGi LGs LGr LGg m Qr Qg inner rest D hsh hsz
    hamb t hpt htp s q' hq' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind1 b₀ c₀
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hn1 : 1 ≤ n := by
    obtain ⟨_, _, _, _, -, -, -, -, h⟩ := root_sizes hsz
    omega
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  rw [prod_ofReal_starCost]
  refine final_term K.hL K.hδ hC1 ENNReal.toReal_nonneg hCL hc hLOE hbig _ b₀ c₀ _ hn1 hleaf
    (starCost_nonneg' S cω) fun k => ?_
  rw [← mul_ofReal_toReal hC (termRb_nonneg hC1 K.hδ hL0 _ _ hleaf (starCost_nonneg' S cω))]
  exact hperk K hθc hp hn D hsh hsz hamb hpt htp s q' hq' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind1 k

end WaveTurbulence.Flower.ProtPin
