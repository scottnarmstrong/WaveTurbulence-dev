/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.TreePairCase
public import WaveTurbulence.Foundations.Flower.ProtRT.TreePair
public import WaveTurbulence.Foundations.Flower.ProtRT.TreeCoh2

/-! # RT-GATE (i): the off-stem root trace of a paired tree, per output and per lattice ball

Clause (i) of `MkSlotsO.RootTraceBoundAt`: a paired tree `X = pair m Qr Qg inner rest` (layers `≤ p`, root in layer
`p`, lone leaf in layer `q'`, canonical ambient), its root pinned at `s ∈ (p, p+1)`, on the R189 box. D2c's root cut
(`rt_root_pack` / `rt_pair_pack`, eligibility from the ambient by `rtc_*`) and the port cases (`rt_rest_case`,
`rt_pair_case`) give, at each output, `Cr · termRb(g')` with `g'` the pieces' incoherency (`g' ≤ g ≤ g' + 1`, the
closing link possibly lost: D2c's `incoherency_rootCut` / `incoherency_cutTerm`). D3's `final_term` (LOE) gives the ball
at `L^{47d+4} · regBound(n, g')`, and the lost link costs one more `L`: `L^{47d+5} · regBound(n, g)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **Layers decrease along descendants.** -/
theorem rt_layer_anti {w : ℕ} (LG : LayeredGarden w) {p : ℕ} (hle : ∀ a, LG.layer a ≤ p) (j : Fin w)
    (q : TTree.Path) : ∀ r : TTree.Path, q ++ r ∈ (LG.garden.tree j).nodes →
      layerAt LG (j, q ++ r) ≤ layerAt LG (j, q) := by
  intro r
  induction r using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton r i ih =>
    intro hm
    have hm' : q ++ r ∈ (LG.garden.tree j).nodes := by
      have := TTree.dropLast_mem_nodes _ hm
      rwa [← List.append_assoc, List.dropLast_concat] at this
    have h1 := tc2a_child_le LG hle (j, q ++ r) i (by simpa [addrExt, List.append_assoc] using hm)
    have e : addrExt (j, q ++ r) [i] = (j, q ++ (r ++ [i])) := by simp [addrExt]
    rw [e] at h1
    exact h1.trans (ih hm')

theorem rt_ite_le (P : Prop) [Decidable P] : (if P then 0 else 1 : ℕ) ≤ 1 := by
  split <;> omega

/-- Star weights alone are the D3 multiplier with no filters and no dagger. -/
theorem rt_mult_star {w d : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (L : ℝ) :
    (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight (∅ : Finset (GBranch G.tree)) (fun _ => false)
      (fun _ => L) κ * filtWeight (∅ : Finset (GBranch G.tree)) (fun _ => false) (fun _ => L) κ *
        (((fun _ => (1 : ℝ)) κ : ℝ) : ℂ)) = fun κ => Flower.IncTop.starWeight S ω κ := by
  funext κ
  simp [filtWeight]

theorem rt_pairRb_le_termRb {P : WTParams} (hC11 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) (n g : ℕ) {leaf CS : ℝ}
    (hleaf : 0 ≤ leaf) (hCS : 0 ≤ CS) : pairRb P 0 n g leaf CS ≤ termRb P 0 n g leaf CS := by
  unfold pairRb termRb
  have h23 : P.C₁ ^ 2 ≤ P.C₁ ^ 3 := pow_le_pow_right₀ hC11 (by norm_num)
  have hr := rb_nonneg (by linarith) hδ hL (n - 1) g
  have : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 := by
    have := latC_nonneg P.d; have := pow_nonneg hL P.d; positivity
  simp only [mul_zero, Real.rpow_zero, mul_one]
  gcongr

/-- **Clause (i) at one output**: `Cr · termRb(g')`, `g'` within one link of the full incoherency. -/
theorem rt_tree_perk {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) (_hFC : TcFC P)
      (_hθc : PieceLoss P θ 0) (_hC11 : 1 ≤ P.C₁) {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1)
      (X : RegChain) (LG : LayeredGarden 1) (_hwf : X.wf = true) (_hsz : X.size = 2 * n)
      (_hdec : X.DecodesTree LG.garden) (_hne : X.lonePath ≠ []) (_hle : ∀ a, LG.layer a ≤ p)
      (_hroot : LG.layer (GNode.root LG.garden.tree 0) = p) {q' : ℕ}
      (_hlone : ∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') (_hamb : ProtAmbient p X LG)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B),
      1 ≤ n ∧ ∃ g' : ℕ, g' ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) ∧
        LG.incoherency (X.treeLinks (LG.garden.sig 0)) ≤ g' + 1 ∧ ∀ k : Mom P.d,
        rn θ (rtBox p q' s) (fun ts => kernelProt P.L P.γ P.δ LG H (fun κ => Flower.IncTop.starWeight S ω κ)
          (fun _ => ts 0) (ts 1) (MkSlotsO.rootPins (fun _ => True) s) k (fun _ => 0) 0) ≤
          ENNReal.ofReal (Cr * termRb P 0 n g' (leafSizeProduct LG B) (starCost S cω)) := by
  obtain ⟨Crs, hCrs, hrestC⟩ := rt_rest_case hθ0 hθ1
  obtain ⟨Cpr, hCpr, hpair⟩ := rt_pair_case hθ0 hθ1
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  refine ⟨((Crs + Cpr) * T4).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hFC hθc hC11 p hp n hn s hps hsp X LG hwf hsz hdec hne hle hroot q' hlone hamb
    S ω cω hpres H B hH
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCS := starCost_nonneg' S cω
  have hCfin : (Crs + Cpr) * T4 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hCrs.ne, hCpr.ne⟩) (by rw [hT4]; simp [ENNReal.mul_eq_top])
  have hfold : ∀ (x : ℝ), 0 ≤ x → ∀ (C' : ℝ≥0∞), C' ≤ Crs + Cpr →
      C' * (T4 * ENNReal.ofReal x) ≤ ENNReal.ofReal (((Crs + Cpr) * T4).toReal * x) := by
    intro x hx C' hC'
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCfin, ← mul_assoc]
    exact mul_le_mul' (mul_le_mul' hC' le_rfl) le_rfl
  cases X with
  | nil => exact absurd rfl hne
  | pair m Qr Qg inner rest =>
  set ζ := LG.garden.sig 0 with hζ
  set ℓb : ℕ := layerAt LG ((0 : Fin 1), bPath m inner) with hℓbd
  have hℓ₀ : layerAt LG ((0 : Fin 1), []) = p := by
    rw [layerAt_of_mem LG (z := ((0 : Fin 1), [])) (TTree.nil_mem_nodes _)]
    exact hroot
  have hℓbp : ℓb ≤ p := layerAt_le_of_forall_layer_le hle _
  -- the port layer is below the closing node
  have hlp := root_lonePath m Qr Qg inner rest
  have hmem : (RegChain.pair m Qr Qg inner rest).lonePath ∈ (LG.garden.tree 0).nodes :=
    TTree.leaves_subset_nodes _ (Links.lone_mem_leaves hdec)
  have hq : layerAt LG ((0 : Fin 1), (RegChain.pair m Qr Qg inner rest).lonePath) = q' := by
    rw [layerAt_of_mem LG hmem]; exact hlone _ rfl
  have hq'b : q' ≤ ℓb := by
    have h1 := rt_layer_anti LG hle 0 (bPath m inner) ([m.lone] ++ rest.lonePath) (by rw [← hlp]; exact hmem)
    rw [← hlp, hq] at h1
    exact h1
  -- the multiplier
  have hind1 : TermChildIndicator (RegChain.pair m Qr Qg inner rest) (fun _ : GNode LG.garden.tree → Mom P.d => (1 : ℝ)) :=
    ⟨fun _ => ⟨zero_le_one, le_rfl⟩, fun _ _ _ => rfl⟩
  have hmult := rt_mult_star (G := LG.garden) S ω P.L
  -- the kernel on the box
  have hbox : ∀ k : Mom P.d, ∀ ts ∈ rtBox p q' s,
      kernelProt P.L P.γ P.δ LG H (fun κ => Flower.IncTop.starWeight S ω κ) (fun _ => ts 0) (ts 1)
        (MkSlotsO.rootPins (fun _ => True) s) k (fun _ => 0) 0 =
      kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight (∅ : Finset (GBranch LG.garden.tree)) (fun _ => false)
          (fun _ => P.L) κ * filtWeight (∅ : Finset (GBranch LG.garden.tree)) (fun _ => false) (fun _ => P.L) κ *
            (((fun _ => (1 : ℝ)) κ : ℝ) : ℂ))
        (fun _ => s) (ts 1) (rootFix s) k (fun _ => 0) 0 := fun k ts hts => by
    rw [hmult]; exact rt_tree_onBox P.L P.γ P.δ H _ p q' s k ts hts
  have hsz' := hsz
  by_cases hrest : rest = .nil
  · -- one pair
    subst hrest
    obtain ⟨LGp, LGi, LGr, LGg, C⟩ := CutTermData.exists_of_wf LG .nil m Qr Qg inner hdec hwf
    have D := PairOnly.of_cutTerm C
    obtain ⟨hleI, hrI, hloneI, hcI⟩ := rtc_pair_inner D hamb hle hwf
    obtain ⟨hleR, hrR, hcR⟩ := rtc_pair_red D hamb hle hwf
    obtain ⟨hleG, hrG, hcG⟩ := rtc_pair_green D hamb hle hwf
    have E : RtEligP p (layerAt LG ((0 : Fin 1), [])) ℓb ζ m Qr Qg inner LGi LGr LGg :=
      ⟨by rw [hℓ₀]; exact hℓbp, by rw [hℓ₀], hleI, hrI, hloneI, hcI, hleR, hrR, hcR, hleG, hrG, hcG⟩
    rw [hℓ₀] at E
    obtain ⟨np, ni, nr, ng, -, -, -, -, hn1⟩ := cut_sizes (Xp := .nil) hsz
    have hg := C.incoherency_cutTerm
    have h0 : LGp.incoherency (RegChain.nil.treeLinks (LGp.garden.sig 0)) = 0 := by
      simp [RegChain.treeLinks, RegChain.linksAt, LayeredGarden.incoherency]
    rw [h0, zero_add] at hg
    have hg' : LG.incoherency ((RegChain.pair m Qr Qg inner .nil).treeLinks (LG.garden.sig 0)) =
        LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) + LGr.incoherency Qr.links +
          LGg.incoherency Qg.links + (if layerAt LG ((0 : Fin 1), []) = ℓb then 0 else 1) := by
      have e : LG.incoherency ((RegChain.pair m Qr Qg inner .nil).treeLinks (LG.garden.sig 0)) =
          LG.incoherency ((appendChain .nil (cpair m Qr Qg inner)).treeLinks (LG.garden.sig 0)) := rfl
      rw [e, hg]
      by_cases hc : layerAt LG ((0 : Fin 1), []) = ℓb <;> simp [RegChain.lonePath, hℓbd, hc] <;> simp_all
    refine ⟨by omega, LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) + LGr.incoherency Qr.links +
      LGg.incoherency Qg.links, ?_, ?_, fun k => ?_⟩
    · rw [hg']; have := rt_ite_le (layerAt LG ((0 : Fin 1), []) = ℓb); omega
    · rw [hg']; have := rt_ite_le (layerAt LG ((0 : Fin 1), []) = ℓb); omega
    obtain ⟨c, A, W, hWc, hWfin, hsum, hid⟩ := rt_pair_pack hθ0 K hFC hθc hp hn C hwf hsz E H B hH S ω cω hpres
      ∅ (fun _ => P.L) (by simp) ∅ (fun _ => P.L) (by simp) (fun _ => 1) hind1 k
    have hF : ∀ ts ∈ rtBox p q' s,
        kernelProt P.L P.γ P.δ LG H (fun κ => Flower.IncTop.starWeight S ω κ) (fun _ => ts 0) (ts 1)
          (MkSlotsO.rootPins (fun _ => True) s) k (fun _ => 0) 0 =
        ∑' e, c e * ∫ u in rtR0 ℓb s (ts 1), rootPh (A e) s u * W e ![s, u] := fun ts hts => by
      rw [hbox k ts hts, hid s s (ts 1) le_rfl]
      rfl
    rw [rn_congr θ hF]
    refine (hpair _ p ℓb q' hℓbp hq'b s hps hsp A c W hWc hWfin).trans ?_
    refine (mul_le_mul' le_rfl hsum).trans ?_
    refine (hfold _ (pairRb_nonneg (by linarith) K.hδ hL0 _ _ hleaf hCS) Cpr le_add_self).trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (rt_pairRb_le_termRb hC11 K.hδ hL0 _ _ hleaf hCS) ENNReal.toReal_nonneg)
  · -- a suffix
    obtain ⟨LGZ, LGi, LGs, LGr, LGg, D⟩ := RootData.exists_of_wf LG m Qr Qg inner rest hdec hwf hrest
    obtain ⟨hleS, hrS, hloneS, hcS⟩ := rtc_root_rest D hamb hle hwf hlone
    obtain ⟨hleI, hrI, hloneI, hcI⟩ := rtc_root_inner D hamb hle hwf
    obtain ⟨hleR, hrR, hcR⟩ := rtc_root_red D hamb hle hwf
    obtain ⟨hleG, hrG, hcG⟩ := rtc_root_green D hamb hle hwf
    have E : RtEligP p (layerAt LG ((0 : Fin 1), [])) ℓb ζ m Qr Qg inner LGi LGr LGg :=
      ⟨by rw [hℓ₀]; exact hℓbp, by rw [hℓ₀], hleI, hrI, hloneI, hcI, hleR, hrR, hcR, hleG, hrG, hcG⟩
    rw [hℓ₀] at E
    have ES : RtEligS p ℓb q' rest LGs := ⟨hq'b, hleS, hrS, hloneS, hcS⟩
    obtain ⟨ns, ni, nr, ng, -, -, -, -, hn1⟩ := root_sizes hsz
    have hg := D.incoherency_rootCut
    refine ⟨by omega, LGs.incoherency (rest.treeLinks (LGs.garden.sig 0)) +
      LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) + LGr.incoherency Qr.links + LGg.incoherency Qg.links,
      ?_, ?_, fun k => ?_⟩
    · rw [hg]; have := rt_ite_le (layerAt LG ((0 : Fin 1), []) = layerAt LG ((0 : Fin 1), bPath m inner)); omega
    · rw [hg]; have := rt_ite_le (layerAt LG ((0 : Fin 1), []) = layerAt LG ((0 : Fin 1), bPath m inner)); omega
    obtain ⟨c, A, W, Ks, hWc, hWfin, hKc, hKfin, hvan, hSfin, hsum, hid⟩ := rt_root_pack hθ0 K hFC hθc hp hn D hwf
      hsz E ES H B hH S ω cω hpres ∅ (fun _ => P.L) (by simp) ∅ (fun _ => P.L) (by simp) (fun _ => 1) (fun _ => rfl) k
    have hF : ∀ ts ∈ rtBox p q' s,
        kernelProt P.L P.γ P.δ LG H (fun κ => Flower.IncTop.starWeight S ω κ) (fun _ => ts 0) (ts 1)
          (MkSlotsO.rootPins (fun _ => True) s) k (fun _ => 0) 0 =
        ∑' e, c e * ∫ u in rtR ℓb s, rootPh (A e) s u * (Ks ![u, ts 1] * W e ![s, u]) := fun ts hts => by
      rw [hbox k ts hts, hid s s (ts 1) le_rfl]
      rfl
    rw [rn_congr θ hF]
    refine (hrestC _ p ℓb q' hℓbp hq'b s hps hsp A c Ks W hKc hWc hKfin hWfin hSfin hvan).trans ?_
    refine (mul_le_mul' le_rfl hsum).trans ?_
    exact hfold _ (termRb_nonneg (by linarith) K.hδ hL0 _ _ hleaf hCS) Crs le_self_add

end WaveTurbulence.Flower.ProtRT
