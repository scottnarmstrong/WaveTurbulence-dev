/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.TreeMain

/-! # D6a PROT-PTW: the protected paired tree with fixed parameters, the bound -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A
open WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtDefs WaveTurbulence.Links
open WaveTurbulence.Flower.FiltSrc WaveTurbulence.Flower.FiltProd WaveTurbulence.Flower.FiltGate

variable {d : ℕ}

theorem selFreq_eq_zero {LG : LayeredGarden 1} {X : RegChain} {L γ δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (Q : Fin (X.treeLinks (LG.garden.sig 0)).length → LayerLink d) (j : Fin (X.treeLinks (LG.garden.sig 0)).length)
    (ev : Fin 2) (q : LPair d) (h : selFreq (X := X) (LG := LG) L γ δ Q j ev q = 0) : linkBilinear L q = 0 := by
  unfold selFreq at h
  have hs : ((if ev = 0 then 1 else -1 : ℝ)) ≠ 0 := by split_ifs <;> norm_num
  have ho : ((((Q j).orientation : ℤ) : ℝ)) ≠ 0 := by
    rcases Int.units_eq_one_or (Q j).orientation with h' | h' <;> simp [h']
  have hp : δ * L ^ (2 * γ) ≠ 0 := (mul_pos hδ (Real.rpow_pos_of_pos hL _)).ne'
  rcases mul_eq_zero.mp h with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hs
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · rcases mul_eq_zero.mp h3 with h4 | h4
        · exact absurd h4 ho
        · exact absurd h4 hδ.ne'
      · exact absurd h3 (Real.rpow_pos_of_pos hL _).ne'
  · exact h1

/-- **The protected paired tree, pointwise, fixed parameters.** -/
theorem tree_bound_fixedG (hd : 3 ≤ d) {C₀ C₂ Ccov : ℝ} (hC₀ : 0 < C₀) (hC₂ : 1 ≤ C₂) (hCcov : 0 < Ccov)
    (hcov : CellCover d Ccov) {γ η δ L Dr : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hL : 1 ≤ L) (hC₂L : C₂ ≤ L ^ η) (hdec : LinkDecay d C₀ C₂ γ η δ L Dr)
    {LG : LayeredGarden 1} {X : RegChain} (hX : X.DecodesTree LG.garden)
    (hspan : ∀ i, |((treeLayerLinks (d := d) LG hX i).leftLayer : ℝ) -
      (treeLayerLinks (d := d) LG hX i).rightLayer| + 1 ≤ Dr)
    (pin : Bool) (Sel : Finset (GBranch LG.garden.tree)) (hpin : pin = true → X.lonePath ≠ [])
    (hSel : ∀ b ∈ Sel, pin = true → b.1.2 ≠ X.lonePath.dropLast) (hSel1 : Sel.card ≤ 1)
    (M₂ : ℝ) (hM₂ : L ≤ M₂) (s : ℝ) (k : Mom d)
    (sw : (GNode LG.garden.tree → Mom d) → ℂ) {α : Type*} [MeasurableSpace α]
    (Gs : SpatialMeasure (PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length) α)
    (hsw : ∀ p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ,
      sw (cosetDecoration LG.garden L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
        Gs.value (pairedLattice L p))
    {A : ℝ≥0∞} (hA : ENNReal.ofReal Gs.mass ≤ A)
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, L ≤ Mu b)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ) (hind : TermChildIndicator X ind)
    (hind1 : pin = false → ∀ κ, ind κ = 1) (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Fourier.spatialNorm (40 * d) (40 * d) (fun k => (H ℓ.1 k : ℂ)) ≤
      ENNReal.ofReal 1)
    (t₀ t₁ : ℝ) :
    ‖kernelProt L γ δ LG H (protMultG sw F M Sel M₂ Fu Mu ind) (fun _ => t₀) t₁
        ((if pin then ProtCfg.term else ProtCfg.none).fix X s s t₀) k (fun _ => 0) 0‖ₑ ≤
      A * ENNReal.ofReal (2 * (treeConst d C₀ Ccov * δ) ^ (X.treeLinks (LG.garden.sig 0)).length *
        L ^ (-(incoherenceExponent d γ - 2 * η) *
          ((Finset.univ.filter fun i => (treeLayerLinks (d := d) LG hX i).IsIncoherent).card : ℝ)) *
        (L ^ (3 * ((if pin then 1 else 0) + Sel.card)) * M₂ ^ (-(Sel.card : ℝ)))) := by
  have hLp : 0 < L := by linarith
  have hM₂p : 0 < M₂ := by linarith
  obtain ⟨Ep, dag, hEp, hfixE, hfixb, hdag1, hdagE, hdag⟩ := pin_data hX pin hpin s t₀ L k ind hind hind1
  set F' := F ∪ Sel
  set ann' : GBranch LG.garden.tree → Bool := fun b => decide (b ∈ Sel)
  set M' : GBranch LG.garden.tree → ℝ := fun b => if b ∈ Sel then M₂ else M b
  set K := filtMomentConst ^ 4
  set C₀' := max C₀ ((5 : ℝ) ^ (2 * d))
  have hK : 0 ≤ K := filtMomentConst_pow_pos.le
  have hC₀' : C₀ ≤ C₀' := le_max_left _ _
  have h5 : (5 : ℝ) ^ (2 * d) ≤ C₀' := le_max_right _ _
  have hM' : ∀ b ∈ F', L ≤ M' b := by
    intro b hb
    by_cases hbs : b ∈ Sel
    · simp only [M', hbs, ite_true]; exact hM₂
    · simp only [M', hbs, ite_false]
      exact hM b ((Finset.mem_union.mp hb).resolve_right hbs)
  set ψ := treePsi hX L F' Fu ann' M' Mu dag
  have hψK : ∀ i q, ‖ψ i q‖ ≤ K := norm_treePsi_le hX hLp.le F' Fu ann' M' Mu hM' hMu dag hdag1
  have hW := tree_mult_eqG hX L k sw Gs hsw F' Fu ann' M' Mu ind dag hdag
  have hf : ∀ a, Fourier.spatialNorm (40 * d) (40 * d) (treeInputFunctionsL LG H a) ≤ ENNReal.ofReal 1 :=
    fun a => treeInputFunctions_spatialNorm_leL hX H hH a
  have hs := (treeCarrier hX).summable_norm_treeSourceLeafWeight_lattice (by omega) (treeInputFunctionsL LG H) hL
    (by omega) (by omega) hf k
  choose Sc hSc hcovS using hcov _ _ _ (treeCarrier hX) k
  have hFm := hA
  have hCm : cellMass d (X.treeLinks (LG.garden.sig 0)).length (Fintype.card (TPlus LG.garden)) (40 * d) Ccov 1 ≤
      ENNReal.ofReal ((Ccov * max (leafLocalizationConstant d (40 * d)) 0 ^ 2 * halfCellFourierConstant d ^ 2) ^ (X.treeLinks (LG.garden.sig 0)).length) := by
    rw [tree_input_count hX]; exact cellMass_le (X.treeLinks (LG.garden.sig 0)).length hCcov.le
  have hCc : 0 ≤ Ccov * max (leafLocalizationConstant d (40 * d)) 0 ^ 2 * halfCellFourierConstant d ^ 2 := by
    have := le_max_right (leafLocalizationConstant d (40 * d)) 0
    positivity
  have hb : 0 ≤ K * C₀' * δ := mul_nonneg (mul_nonneg hK (hC₀.le.trans hC₀')) hδ.le
  have hTC : treeConst d C₀ Ccov * δ =
      (Ccov * max (leafLocalizationConstant d (40 * d)) 0 ^ 2 * halfCellFourierConstant d ^ 2) * (K * C₀' * δ) := by
    unfold treeConst; ring
  have hy1 : incoherenceExponent d γ - 2 * η ≤ 1 := by
    have := incoherenceExponent_le_one d γ; linarith
  have hMi (i : Fin (X.treeLinks (LG.garden.sig 0)).length) (hi : i ∉ Ep) (A : LayerLink d) (h1 : A.leftLayer = ((treeLayerLinks (d := d) LG hX) i).leftLayer)
      (h2 : A.rightLayer = ((treeLayerLinks (d := d) LG hX) i).rightLayer) :
      ∫⁻ s in linkBox A, ‖genLinkTimeFactor L γ δ A (ψ i) s‖ₑ ≤
        normalMass d K C₀ C₂ γ η δ L ((treeLayerLinks (d := d) LG hX) i).IsIncoherent :=
    normal_link_mass hX hLp.le γ δ hdec F' Fu ann' M' Mu hM' hMu dag i (hdagE i hi) (hspan i) A h1 h2
  have hnormal (i : Fin (X.treeLinks (LG.garden.sig 0)).length) (ρ : ℝ) (hρ : 1 ≤ ρ) :
      ENNReal.ofReal (coupling d L γ δ ^ 2) * normalMass d K C₀ C₂ γ η δ L ((treeLayerLinks (d := d) LG hX) i).IsIncoherent ≤
        ENNReal.ofReal (K * C₀' * δ * (ρ * (if ((treeLayerLinks (d := d) LG hX) i).IsIncoherent then L ^ (-(incoherenceExponent d γ - 2 * η))
          else 1))) := by
    refine (per_normal (y := incoherenceExponent d γ - 2 * η) hL hδ hK hC₀.le hC₀' (by linarith) hC₂L
      (incoherenceExponent d γ - η) (by ring) _).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hb
    apply mul_le_mul_of_nonneg_right hρ
    split_ifs <;> positivity
  rcases Sel.eq_empty_or_nonempty with hSe | ⟨v, hvS0⟩
  · -- no selection
    have hk := enorm_kernelProt_tree_le hX hL γ δ H (protMultG sw F M Sel M₂ Fu Mu ind) (fun _ => t₀) t₁
      ((if pin then ProtCfg.term else ProtCfg.none).fix X s s t₀) k Gs ψ hK hψK hW hs (by omega) (by omega)
      zero_le_one hf Sc hcovS hSc Ep (fun _ => K) (fun i _ => ⟨hK, hψK i⟩)
      (fun i => normalMass d K C₀ C₂ γ η δ L ((treeLayerLinks (d := d) LG hX) i).IsIncoherent) hMi (fun i hi e => hfixE i hi e)
    refine hk.trans ?_
    rw [← one_mul (ENNReal.ofReal Gs.mass * _ * _)]
    have hR : ∏ i : Fin (X.treeLinks (LG.garden.sig 0)).length, (if i ∈ Ep then L ^ 3 else 1) ≤
        L ^ (3 * ((if pin then 1 else 0) + Sel.card)) * M₂ ^ (-(Sel.card : ℝ)) := by
      rw [hSe, Finset.card_empty, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one, add_zero,
        Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, ← pow_mul, mul_comm 3]
      exact pow_le_pow_right₀ hL ((Nat.mul_comm _ _).trans_le (Nat.mul_le_mul_left 3 hEp))
    rw [hTC]
    refine assemble _ (coupling d L γ δ) (K * C₀' * δ) hb (fun i => if i ∈ Ep then L ^ 3 else 1)
      (fun i => by split_ifs <;> positivity) (fun i => ((treeLayerLinks (d := d) LG hX) i).IsIncoherent) hLp (fun i => ?_) (by norm_num) hFm hCc
      hCm hR
    by_cases hi : i ∈ Ep
    · simp only [hi, ite_true]
      exact per_pin hL hγ.2.le hδ hδ1 hK h5 hy1 _
    · simp only [hi, ite_false]
      exact hnormal i 1 le_rfl
  · -- one selected branch
    have hSv : Sel = {v} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hvS0, fun w hw => Finset.card_le_one.mp hSel1 w hw v hvS0⟩
    have hvS : v ∈ Sel := hvS0
    set jv := ((treeLinkEquiv hX).symm v).1
    set ev := ((treeLinkEquiv hX).symm v).2
    have hbv : treeLinkBranch hX jv ev = v := (treeLinkEquiv hX).apply_symm_apply v
    have hfv : (if pin then ProtCfg.term else ProtCfg.none).fix X s s t₀ (treeLinkBranch hX jv ev) = none := by
      rw [hbv]; exact hfixb v (hSel v hvS)
    have hzero : ∀ q, |linkBilinear L q| < M₂ / 4 → ψ jv q = 0 := by
      intro q hq
      apply treePsi_eq_zero_of_small hX L F' Fu ann' M' Mu dag jv ev
        (by rw [hbv]; exact Finset.mem_union_right _ hvS) (by rw [hbv]; simp [ann', hvS]) hM₂p
        (by rw [hbv]; simp [M', hvS]) q hq
    have hann : ∀ q, selFreq (X := X) (LG := LG) L γ δ (treeLayerLinks (d := d) LG hX) jv ev q = 0 → ψ jv q = 0 := by
      intro q hq
      apply hzero q
      rw [selFreq_eq_zero hLp hδ (treeLayerLinks (d := d) LG hX) jv ev q hq, abs_zero]
      positivity
    set cs := 2 * K / (Real.pi * δ * L ^ (2 * γ) * M₂)
    have hcs : 0 ≤ cs := by positivity
    have hsw := norm_selWeight_le (X := X) (LG := LG) hLp γ hδ (treeLayerLinks (d := d) LG hX) jv ev ψ hψK hM₂p hzero
    set E := Ep ∪ {jv}
    have hk := enorm_kernelProt_tree_sel_le hX hL γ δ H (protMultG sw F M Sel M₂ Fu Mu ind) (fun _ => t₀) t₁
      ((if pin then ProtCfg.term else ProtCfg.none).fix X s s t₀) k Gs ψ hK hψK hW hs (by omega) (by omega)
      zero_le_one hf Sc hcovS hSc jv ev hfv hann (Bψ' := max K cs) (le_max_of_le_left hK)
      (fun i q => (hsw i q).trans (by split_ifs; exacts [le_max_right _ _, le_max_left _ _]))
      E (Finset.mem_union_right _ (Finset.mem_singleton_self jv)) (fun i => if i = jv then cs else K)
      (fun i _ => ⟨by split_ifs <;> assumption, fun q => hsw i q⟩)
      (fun i => normalMass d K C₀ C₂ γ η δ L ((treeLayerLinks (d := d) LG hX) i).IsIncoherent)
      (fun i hi A h1 h2 => by
        have hiv : i ≠ jv := fun h => hi (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
        have hiE : i ∉ Ep := fun h => hi (Finset.mem_union_left _ h)
        rw [show selWeight L γ δ (treeLayerLinks (d := d) LG hX) jv ev ψ i = ψ i from Function.update_of_ne hiv _ _]
        exact hMi i hiE A h1 h2)
      (fun i hi e => hfixE i (fun h => hi (Finset.mem_union_left _ h)) e)
    refine hk.trans ?_
    have hcard : E.card ≤ (if pin then 1 else 0) + Sel.card := by
      rw [hSv, Finset.card_singleton]
      exact (Finset.card_union_le _ _).trans (by rw [Finset.card_singleton]; omega)
    have hR : ∏ i : Fin (X.treeLinks (LG.garden.sig 0)).length, ((if i ∈ E then L ^ 3 else 1) * (if i = jv then M₂⁻¹ else 1)) ≤
        L ^ (3 * ((if pin then 1 else 0) + Sel.card)) * M₂ ^ (-(Sel.card : ℝ)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, ← pow_mul,
        Finset.prod_ite_eq' Finset.univ jv, ite_eq_left (Finset.mem_univ _), hSv, Finset.card_singleton,
        Nat.cast_one, Real.rpow_neg_one, mul_comm 3]
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hM₂p.le)
      rw [hSv, Finset.card_singleton] at hcard
      exact pow_le_pow_right₀ hL ((Nat.mul_comm _ _).trans_le (Nat.mul_le_mul_left 3 hcard))
    rw [hTC]
    refine assemble _ (coupling d L γ δ) (K * C₀' * δ) hb
      (fun i => (if i ∈ E then L ^ 3 else 1) * (if i = jv then M₂⁻¹ else 1))
      (fun i => by split_ifs <;> positivity) (fun i => ((treeLayerLinks (d := d) LG hX) i).IsIncoherent) hLp (fun i => ?_) (by norm_num) hFm hCc
      hCm hR
    by_cases hij : i = jv
    · subst hij
      simp only [show jv ∈ E from Finset.mem_union_right _ (Finset.mem_singleton_self jv), ite_true]
      exact per_sel hL hδ hK h5 hM₂p hy1 _
    · by_cases hi : i ∈ E
      · simp only [hi, hij, ite_true, ite_false, mul_one]
        exact per_pin hL hγ.2.le hδ hδ1 hK h5 hy1 _
      · simp only [hi, hij, ite_false, mul_one]
        exact hnormal i 1 le_rfl

/-- The star-weight form. -/
theorem tree_bound_fixed (hd : 3 ≤ d) {C₀ C₂ Ccov : ℝ} (hC₀ : 0 < C₀) (hC₂ : 1 ≤ C₂) (hCcov : 0 < Ccov)
    (hcov : CellCover d Ccov) {γ η δ L Dr : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hL : 1 ≤ L) (hC₂L : C₂ ≤ L ^ η) (hdec : LinkDecay d C₀ C₂ γ η δ L Dr)
    {LG : LayeredGarden 1} {X : RegChain} (hX : X.DecodesTree LG.garden)
    (hspan : ∀ i, |((treeLayerLinks (d := d) LG hX i).leftLayer : ℝ) -
      (treeLayerLinks (d := d) LG hX i).rightLayer| + 1 ≤ Dr)
    (pin : Bool) (Sel : Finset (GBranch LG.garden.tree)) (hpin : pin = true → X.lonePath ≠ [])
    (hSel : ∀ b ∈ Sel, pin = true → b.1.2 ≠ X.lonePath.dropLast) (hSel1 : Sel.card ≤ 1)
    (M₂ : ℝ) (hM₂ : L ≤ M₂) (s : ℝ)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ) (cω : GNode LG.garden.tree → ℝ)
    (hω : ∀ a ∈ S, StarPresented (30 * d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, L ≤ Mu b)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ) (hind : TermChildIndicator X ind)
    (hind1 : pin = false → ∀ κ, ind κ = 1) (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Fourier.spatialNorm (40 * d) (40 * d) (fun k => (H ℓ.1 k : ℂ)) ≤
      ENNReal.ofReal 1)
    (t₀ t₁ : ℝ) (k : Mom d) :
    ‖kernelProt L γ δ LG H (protMult S ω F M Sel M₂ Fu Mu ind) (fun _ => t₀) t₁
        ((if pin then ProtCfg.term else ProtCfg.none).fix X s s t₀) k (fun _ => 0) 0‖ₑ ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (2 * (treeConst d C₀ Ccov * δ) ^ (X.treeLinks (LG.garden.sig 0)).length *
        L ^ (-(incoherenceExponent d γ - 2 * η) *
          ((Finset.univ.filter fun i => (treeLayerLinks (d := d) LG hX i).IsIncoherent).card : ℝ)) *
        (L ^ (3 * ((if pin then 1 else 0) + Sel.card)) * M₂ ^ (-(Sel.card : ℝ)))) := by
  rw [protMult_eq_G]
  exact tree_bound_fixedG hd hC₀ hC₂ hCcov hcov hγ hη hδ hδ1 hL hC₂L hdec hX hspan pin Sel hpin hSel hSel1 M₂ hM₂ s k
    (starWeight S ω) ((starRootMeasure (30 * d) S ω cω hω (treeRow hX)).at k)
    (tree_starWeight_eq_value hX (30 * d) S ω cω hω L k) (star_mass_le S ω cω hω (treeRow hX) k)
    F M hM Fu Mu hMu ind hind hind1 H hH t₀ t₁

end WaveTurbulence.Flower.ProtPtw
