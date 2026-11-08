/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.Gate

/-! # D6a PROT-PTW: `protPtwGate : ProtPtwGate` (o82 Prop 14.2, (18.4)) -/

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

theorem tree_links_eq {X : RegChain} {LG : LayeredGarden 1} {n : ℕ} (h : X.size = 2 * n) :
    (X.treeLinks (LG.garden.sig 0)).length = n := by
  have he : (X.treeLinks (LG.garden.sig 0)).length * 2 = X.size :=
    chain_linksAt_length X (LG.garden.sig 0) ((0 : Fin 1), [])
  omega

theorem tree_incoh_eq {d : ℕ} {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden) :
    (((Finset.univ.filter fun i => (treeLayerLinks (d := d) LG hX i).IsIncoherent).card : ℕ) : ℝ) =
      (protIncoh X LG : ℝ) := by
  have h := treeLayerLinks_incoherenceCount d hX
  unfold incoherenceCount at h
  change _ = ((LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℕ) : ℝ)
  rw [← h]

/-- **D6a: the pointwise bound of protected whole objects** (o82 Prop 14.2 in the form (18.4) of Thm 18.2). -/
theorem protPtwGate : ProtPtwGate := by
  intro d hd γ hγ
  obtain ⟨C₀, hC₀, hdec⟩ := exists_filtOneLink_decay d hd
  obtain ⟨Ccov, hCcov, hcov⟩ := exists_finite_link_cell_localization d (by omega)
  have hinc := incoherenceExponent_pos (d := d) (by omega) hγ
  refine ⟨min (incoherenceExponent d γ / 2) (1 / 4), lt_min (by linarith) (by norm_num), ?_⟩
  intro η hη φin _ τstar _ φ _
  have hη0 : 0 < η := hη.1
  have hηγ : η < incoherenceExponent d γ := (hη.2.trans (min_le_left _ _)).trans_lt (by linarith)
  have hη4 : η ≤ 1 / 4 := hη.2.trans (min_le_right _ _)
  have hT0 : 0 ≤ treeConst d C₀ Ccov := treeConst_nonneg d hCcov.le
  refine ⟨max 2 (treeConst d C₀ Ccov), le_max_of_le_left (by norm_num), 1, one_pos, fun ν _ => ?_⟩
  refine ⟨1, one_pos, fun δ hδ D hD _ => ?_⟩
  obtain ⟨C₂, L₁, hC₂, hL₁, hdecL⟩ := hdec γ hγ η hη0 hηγ δ hδ.1 ((D : ℝ) + 1) (by positivity)
  refine ⟨1, le_rfl, max (max 2 L₁) (C₂ ^ (1 / η)), le_max_of_le_left (le_max_left _ _), fun L hL => ?_⟩
  have hL2 : 2 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hL1 : 1 ≤ L := by linarith
  have hLL₁ : L₁ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hC₂L : C₂ ≤ L ^ η := by
    have h1 : C₂ ^ (1 / η) ≤ L := (le_max_right _ _).trans hL
    calc C₂ = (C₂ ^ (1 / η)) ^ η := by
          rw [← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hη0.ne', Real.rpow_one]
      _ ≤ L ^ η := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) h1 hη0.le
  have hdecP : LinkDecay d C₀ C₂ γ η δ L ((D : ℝ) + 1) := fun Q hQ K φ hφ => hdecL L hLL₁ Q hQ K φ hφ
  intro p hp n _ w LG X hshape hsize pin Sel hpin hSel hSel1 M₂ hM₂ s S ω cω hω F M hM Fu Mu hMu ind hind hind1
    H B hctrl t₀ t₁ k
  dsimp only at hp hM₂ ⊢
  change p < D at hp
  change L ≤ M₂ at hM₂
  have hR0 : 0 ≤ L ^ (3 * ((if pin then 1 else 0) + Sel.card : ℕ)) * M₂ ^ (-(Sel.card : ℝ)) :=
    mul_nonneg (pow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  let P : WTParams := ⟨d, γ, η, φin, τstar, φ, max 2 (treeConst d C₀ Ccov), ν, δ, D, 1, L⟩
  have hreg := fun (n' g : ℕ) (A : ℝ≥0∞) => tree_le_regBound P hT0 (le_max_right _ _) (le_max_left _ _) hδ.1.le hL1
    hη0.le hη4 n' g hR0 A
  refine enorm_le_of_normalized LG _ (fun B' H' hB' => kernelProt_scale _ _ _ LG H' B' hB' _ _ _ _ _ _ _)
    (fun H' ℓ hℓ h0 => kernelProt_zero_of_leaf _ _ _ LG H' hℓ h0 _ _ _ _ _ _ _) _ (fun H' hH' => ?_) H B hctrl
  rcases w with _ | _ | _ | w
  · exact (hshape : False).elim
  · -- protected trees
    obtain ⟨hX, hlay⟩ := protShape_tree_facts hshape
    have hspan (i : Fin (X.treeLinks (LG.garden.sig 0)).length) :
        |((treeLayerLinks (d := d) LG hX i).leftLayer : ℝ) - (treeLayerLinks (d := d) LG hX i).rightLayer| + 1 ≤
          (D : ℝ) + 1 :=
      (treeLayerLinks_span d hX hlay i).trans (by exact_mod_cast Nat.add_le_add_right hp.le 1)
    have hb := tree_bound_fixed hd hC₀ hC₂ hCcov hcov ⟨hγ.1, hγ.2⟩ hη0 hδ.1 hδ.2 hL1 hC₂L hdecP hX hspan pin Sel hpin
      (fun b hb hpt => (hSel b hb).2.2.2 hpt) hSel1 M₂ hM₂ s S ω cω hω F M hM Fu Mu hMu ind hind hind1 H' hH' t₀ t₁ k
    refine hb.trans ?_
    rw [tree_incoh_eq hX, tree_links_eq (LG := LG) hsize]
    exact hreg n (protIncoh X LG) _
  · -- protected cap couples
    obtain ⟨LG1, Dc, hshape1⟩ := protShape_cap_facts hshape
    obtain ⟨hX1, hlay1⟩ := protShape_tree_facts hshape1
    have hspan (i : Fin (X.treeLinks (LG1.garden.sig 0)).length) :
        |((treeLayerLinks (d := d) LG1 hX1 i).leftLayer : ℝ) - (treeLayerLinks (d := d) LG1 hX1 i).rightLayer| + 1 ≤
          (D : ℝ) + 1 :=
      (treeLayerLinks_span d hX1 hlay1 i).trans (by exact_mod_cast Nat.add_le_add_right hp.le 1)
    change ‖kernelProt L γ δ LG H' _ (fun _ => t₀) t₁ _ k (fun _ => 0) 0‖ₑ ≤ _
    rw [Dc.kernelProt_cap, capM_protMult Dc, Dc.cfg_fix_cap, enorm_mul]
    set e := Dc.βc.symm.toEmbedding
    have hℓ0 : Dc.ℓ0 ∈ inputLeaves LG.garden := by rw [Dc.inputLeaves_cap]; exact Finset.mem_insert_self _ _
    have hH0 : ‖((H' ((0 : Fin 2), X.lonePath) k : ℝ) : ℂ)‖ₑ ≤ 1 := enorm_le_of_spatialNorm (hH' Dc.ℓ0 hℓ0) k
    have hH1 : ∀ ℓ ∈ inputLeaves LG1.garden,
        Fourier.spatialNorm (40 * d) (40 * d) (fun k => (capH H' ℓ.1 k : ℂ)) ≤ ENNReal.ofReal 1 := by
      intro ℓ hℓ
      have hm : Dc.ιL ℓ ∈ inputLeaves LG.garden := by
        rw [Dc.inputLeaves_cap]
        exact Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hℓ)
      exact hH' _ hm
    have hSel' : ∀ b ∈ Sel.map e, pin = true → b.1.2 ≠ X.lonePath.dropLast := by
      intro b hb hpt
      obtain ⟨b0, hb0, rfl⟩ := Finset.mem_map.mp hb
      exact (hSel b0 hb0).2.2.2 hpt
    have hM' : ∀ b ∈ F.map e, L ≤ M (Dc.βc b) := by
      intro b hb
      obtain ⟨b0, hb0, rfl⟩ := Finset.mem_map.mp hb
      simpa [e] using hM b0 hb0
    have hMu' : ∀ b ∈ Fu.map e, L ≤ Mu (Dc.βc b) := by
      intro b hb
      obtain ⟨b0, hb0, rfl⟩ := Finset.mem_map.mp hb
      simpa [e] using hMu b0 hb0
    have hb := tree_bound_fixedG hd hC₀ hC₂ hCcov hcov ⟨hγ.1, hγ.2⟩ hη0 hδ.1 hδ.2 hL1 hC₂L hdecP hX1 hspan pin
      (Sel.map e) hpin hSel' (by rw [Finset.card_map]; exact hSel1) M₂ hM₂ s k (capStar Dc S ω)
      ((starRootMeasure (30 * d) S ω cω hω (fun a => treeRow Dc.dec1 (Dc.ρ a))).at k)
      (capStar_eq_value Dc (30 * d) S ω cω hω L k) (capStar_mass_le Dc S ω cω hω k) (F.map e) (fun b => M (Dc.βc b))
      hM' (Fu.map e) (fun b => Mu (Dc.βc b)) hMu' (fun K => ind (fun a => K (Dc.ρ a))) (Dc.termChild_cap ind hind)
      (fun hpf K => hind1 hpf _) (capH H') hH1 t₀ 0
    rw [Finset.card_map, tree_incoh_eq hX1, ← Dc.protIncoh_cap, tree_links_eq (LG := LG1) (show X.size = 2 * n by
      rw [← hsize, CapData.protSize_cap (X := X) (LG := LG) (LG1 := LG1)]; rfl)] at hb
    calc ‖((H' ((0 : Fin 2), X.lonePath) k : ℝ) : ℂ)‖ₑ * ‖kernelProt L γ δ LG1 (capH H') _ (fun _ => t₀) 0 _ k
          (fun _ => 0) 0‖ₑ ≤ 1 * _ := mul_le_mul' hH0 (hb.trans (hreg n (protIncoh X LG) _))
      _ = _ := one_mul _
  · exact (hshape : False).elim

end WaveTurbulence.Flower.ProtPtw
