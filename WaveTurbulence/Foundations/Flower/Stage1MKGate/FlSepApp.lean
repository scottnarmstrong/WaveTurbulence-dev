/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Unclean
public import WaveTurbulence.Foundations.Flower.MkMarkX.TreeSep

/-! # B4 STAGE1MK-GATE: the weight vanishes at stem-unclean points (FL-SEP, per tree)

`markedWt_zero_of_unclean`: at a stem-unclean prescribed point of a gate carrier, for a stem-dependent weight with
high roots, the weight `selOK · markedWeight` vanishes on every decoration selected by the point's prescription
(coset base `0`). It is B2e's per-tree FL-SEP (`weight_zero_of_unclean_collapsed_tree`) applied to the weight
restricted to pairing-consistent momenta with the right root label (its `hW` quantifies over all momenta):
* the frontier bound in the vine's tree `j₀`: top leaves of layer `< p` are cut off by `frontierW` (`chi0`); top
  leaves of layer `p` are paired leaves, of the same layer as their partner (`IsLayering`), one of them an input
  leaf (`pair_sign`), and `leafProdCap`'s pair profile `h p j₀ j'` / `h p j' j₀` vanishes beyond `r = Rf j₀`
  (the high-root clause); a partner in a cap tree would make the leaf a capped flower;
* the root bound `(2N'+2) r ≤ ‖k_root‖/4` and `L^{-γ+η} < ‖k_root‖/2` from `r^10 ≤ ‖latticePoint (roots j₀)‖`,
  `r ≥ L/2`, `8 N_{p+1}^4 + 8 ≤ L`, `L ≥ 4`, `η ≤ γ`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA
open WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents WaveTurbulence.Stage1
open WaveTurbulence.RedSplice (Prescription vinesV0 mem_vinesV0)

namespace WaveTurbulence.Flower.Stage1MKGate

variable {w : ℕ}

theorem chi0_lt_one {x : ℝ} (h : chi0 x ≠ 0) : |x| < 1 := by
  by_contra hx
  push_neg at hx
  apply h
  unfold chi0
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

theorem genDec_cast_apply {G G' : Garden w} (e : G = G') {d : ℕ} {n : Fin w → (Fin d → ℤ)} {n' : Fin d → ℤ}
    (κ : GenDecoration G d n n') (y : Fin w × TTree.Path) (hy : y.2 ∈ (G.tree y.1).nodes)
    (hy' : y.2 ∈ (G'.tree y.1).nodes) : (e ▸ κ : GenDecoration G' d n n').1 ⟨y, hy'⟩ = κ.1 ⟨y, hy⟩ := by
  subst e
  rfl

theorem ofForest_decCast {LG : LayeredGarden w} (A : PrimeData LG) {d : ℕ} {roots : Fin w → (Fin d → ℤ)}
    (κ : GenDecoration LG.garden d roots 0) (x : GNode LG.garden.tree) :
    MkMark.ofForest A (decCast A κ).1 x = κ.1 x :=
  genDec_cast_apply A.gardenEq.symm κ x.1 x.2 _

/-- **The frontier bound in tree `j₀` from a nonzero marked weight.** -/
theorem frontier_le_of_markedWt_ne_zero (P : WTParams) {R : ℕ} {LG : LayeredGarden (2 * R)}
    (J : Finset (Fin (2 * R))) (p : ℕ) (kSel : Fin (2 * R) → Option ℕ)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (k : GNode LG.garden.tree → Mom P.d)
    (hplain : LG.garden.IsPlain) (hlay : ∀ a, LG.layer a ≤ p) {j₀ : Fin (2 * R)} (hj₀ : j₀ ∉ J) {r : ℝ}
    (hr0 : 0 < r) (hRfr : Rf j₀ = some r) (hhp : ∀ j' x, ‖x‖ ≥ r → h p j₀ j' x = 0 ∧ h p j' j₀ x = 0)
    (hpair : ∀ ℓ : GLeaf LG.garden.tree, k ℓ.toNode = k (LG.garden.pair ℓ).toNode)
    (hmw : markedWt P J p kSel h Rf σ Rs dag LG k ≠ 0) (a : GNode LG.garden.tree) (ha : a.1.1 = j₀)
    (htl : LG.IsTopLeaf p a) (hnf : ¬ MkMark.IsFlowerNodeF LG (IsCapFlower LG J) a) : ‖k a‖ ≤ r := by
  unfold markedWt at hmw
  have hmw' := right_ne_zero_of_mul hmw
  unfold markedWeight at hmw'
  have hfw : Typed.frontierW LG p Rf k ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hmw')))
  have hlp : leafProdCap LG J h k ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hmw')
  by_cases hlt : LG.layer a < p
  · have hnfl : ¬ LG.IsFlowerNode a := by
      rintro ⟨ℓ, hfl, -⟩
      have h1 : LG.garden.mark ℓ = none := hplain ℓ
      unfold Garden.IsFlower at hfl
      rw [h1] at hfl
      exact absurd hfl (by simp)
    unfold Typed.frontierW at hfw
    have hf := Finset.prod_ne_zero_iff.mp hfw a (Finset.mem_univ a)
    rw [if_pos ⟨htl, hlt, hnfl⟩, ha, hRfr] at hf
    have hc := chi0_lt_one hf
    rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hr0.le), div_lt_one hr0] at hc
    exact hc.le
  · have hleaf : a.1.2 ∈ (LG.garden.tree a.1.1).leaves := htl.1.resolve_left hlt
    have hlayp : LG.layer a = p := le_antisymm (hlay a) (not_lt.mp hlt)
    let ℓ : GLeaf LG.garden.tree := ⟨a.1, hleaf⟩
    have hℓa : ℓ.toNode = a := Subtype.ext rfl
    have hne : LG.garden.pair ℓ ≠ ℓ := fun he => ((LG.garden.pair_eq_iff ℓ).mp he) (hplain ℓ)
    have hℓj : ℓ.1.1 = j₀ := ha
    have hpJ : (LG.garden.pair ℓ).1.1 ∉ J := fun hj =>
      hnf ⟨ℓ, ⟨by rw [hℓj]; exact hj₀, hj⟩, hℓa⟩
    have hsign : LG.garden.sign (LG.garden.pair ℓ).toNode = - LG.garden.sign ℓ.toNode :=
      LG.garden.pair_sign ℓ hne
    obtain ⟨ℓi, hℓi_in, hℓi_eq⟩ : ∃ ℓi, ℓi ∈ inputLeaves LG.garden ∧ (ℓi = ℓ ∨ ℓi = LG.garden.pair ℓ) := by
      rcases Int.units_eq_one_or (LG.garden.sign ℓ.toNode) with hs | hs
      · exact ⟨ℓ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hs, hplain ℓ⟩, Or.inl rfl⟩
      · refine ⟨LG.garden.pair ℓ, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, hplain _⟩, Or.inr rfl⟩
        rw [hsign, hs, neg_neg]
    have hlp' := Finset.prod_ne_zero_iff.mp hlp ℓi hℓi_in
    have htrees : ¬ (ℓi.1.1 ∈ J ∨ (LG.garden.pair ℓi).1.1 ∈ J) := by
      rcases hℓi_eq with rfl | rfl
      · rintro (h1 | h1)
        · exact hj₀ (hℓj ▸ h1)
        · exact hpJ h1
      · rw [LG.garden.pair_pair]
        rintro (h1 | h1)
        · exact hpJ h1
        · exact hj₀ (hℓj ▸ h1)
    rw [if_neg htrees] at hlp'
    -- the input leaf's momentum and layer are those of `a`
    have hk : k ℓi.toNode = k a := by
      rcases hℓi_eq with rfl | rfl
      · rw [hℓa]
      · rw [← hpair ℓ, hℓa]
    have hlayi : LG.layer ℓi.toNode = p := by
      rcases hℓi_eq with rfl | rfl
      · rw [hℓa]; exact hlayp
      · rw [← LG.isLayering.2 ℓ, hℓa]; exact hlayp
    have hnodes : ℓi.1.2 ∈ (LG.garden.tree ℓi.1.1).nodes := ℓi.toNode.2
    have hpt : pairTrees LG.garden ℓi.1 = (ℓi.1.1, (LG.garden.pair ℓi).1.1) := by
      unfold pairTrees
      have hex : ∃ ℓ' : GLeaf LG.garden.tree, ℓ'.1 = ℓi.1 := ⟨ℓi, rfl⟩
      rw [dif_pos hex]
      have : hex.choose = ℓi := Subtype.ext hex.choose_spec
      rw [this]
    unfold typeProfiles at hlp'
    rw [dif_pos hnodes, hpt] at hlp'
    have hlay' : LG.layer ⟨ℓi.1, hnodes⟩ = p := hlayi
    rw [hlay', hk] at hlp'
    by_contra hr
    push_neg at hr
    have hge : ‖k a‖ ≥ r := hr.le
    have htr : ℓi.1.1 = j₀ ∨ (LG.garden.pair ℓi).1.1 = j₀ := by
      rcases hℓi_eq with rfl | rfl
      · exact Or.inl hℓj
      · rw [LG.garden.pair_pair]; exact Or.inr hℓj
    rcases htr with e | e
    · rw [e] at hlp'
      exact hlp' (hhp _ _ hge).1
    · rw [e] at hlp'
      exact hlp' (hhp _ _ hge).2

/-- **The weight vanishes at a stem-unclean point on its selected decorations** (FL-SEP, per tree). -/
theorem markedWt_zero_of_unclean (P : WTParams) {R p N : ℕ} {J : Finset (Fin (2 * R))}
    {pat : Fin (2 * R) → FixPat} {kSel : Fin (2 * R) → Option ℕ} (b : PrescribedPrimeGarden (2 * R))
    (hcar : MkCarries P p N b.layered ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ b.layered.garden : Garden 2)) ∧
      b.layered.garden.Irreducible ∧ (∀ j ∈ J, b.layered.garden.tree j = TTree.leaf) ∧ CapGeo b.layered J p ∧
      CapPatValid b.layered J pat p)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (hRf : ∀ j r, Rf j = some r → P.L / 2 ≤ r)
    (hhigh : ((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖)
    (hS : StemDep σ kSel) (hun : ¬ CleanPt J b) (hL4 : 4 ≤ P.L) (hηγ : P.η ≤ P.γ)
    (hbig : 8 * ((P.N (p + 1) ^ 4 : ℕ) : ℝ) + 8 ≤ P.L)
    (κ : GenDecoration b.layered.garden P.d roots 0) (hsel : selAt P 0 b.prime b.sigma κ) :
    markedWt P J p kSel h Rf σ Rs dag b.layered (cosetDecoration b.layered.garden P.L 0 κ.1) = 0 := by
  obtain ⟨c, hc, -, hcun⟩ := (not_cleanPt_iff J b).mp hun
  have hcap := hcar.2.2.2.2.1
  have hplain : b.layered.garden.IsPlain := hcar.1.1.1
  set u := MkMark.clBlockOf c with hu
  set j₀ := (MkMark.inflatedBranch b.prime u.lower).1.1 with hj₀def
  have hj₀ : j₀ ∉ J := by
    intro hj
    have hb : (MkMark.inflatedBranch b.prime u.lower).1.2 ∈ (b.layered.garden.tree j₀).branching :=
      (MkMark.inflatedBranch b.prime u.lower).2
    rw [hcar.2.2.2.1 j₀ hj] at hb
    exact absurd hb (by simp [TTree.branching])
  obtain ⟨r, hRfr, hhp, hr10⟩ := hhigh hS j₀ hj₀
  have hrL : P.L / 2 ≤ r := hRf j₀ r hRfr
  have hr2 : 2 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  set N' : ℕ := P.N (p + 1) ^ 4 with hN'
  have hr9 : 8 * (N' : ℝ) + 8 ≤ r ^ 9 := by
    have h8 : (2 : ℝ) ^ 8 ≤ (P.L / 2) ^ 8 := pow_le_pow_left₀ (by norm_num) (by linarith) 8
    have h9 : (P.L / 2) ^ 9 ≤ r ^ 9 := pow_le_pow_left₀ (by linarith) hrL 9
    have hL9 : P.L ≤ (P.L / 2) ^ 9 := by
      rw [pow_succ]
      nlinarith
    linarith
  set k := cosetDecoration b.layered.garden P.L 0 κ.1 with hkdef
  have hdec := isDecoration_cosetDecoration b.layered.garden P.L 0 κ.1 κ.2.1
  have hroot : k (GNode.root b.layered.garden.tree j₀) = latticePoint P.L (roots j₀) := by
    show 0 + latticePoint P.L (κ.1 (GNode.root b.layered.garden.tree j₀)) = _
    rw [zero_add, κ.2.2.1 j₀]
  let W : (GNode b.layered.garden.tree → Mom P.d) → ℝ := fun k' =>
    if k' (GNode.root b.layered.garden.tree j₀) = latticePoint P.L (roots j₀) ∧
        ∀ ℓ : GLeaf b.layered.garden.tree, k' ℓ.toNode = k' (b.layered.garden.pair ℓ).toNode
    then markedWt P J p kSel h Rf σ Rs dag b.layered k' else 0
  have hWk : W k = markedWt P J p kSel h Rf σ Rs dag b.layered k := if_pos ⟨hroot, hdec.2⟩
  rw [← hWk]
  have hN : b.layered.topOrder p j₀ ≤ N' := by
    have := hcar.1.2.1.1 j₀
    simpa using this
  refine MkMarkX.weight_zero_of_unclean_collapsed_tree b.prime J u hcun p N' r hr0.le
    (fun ℓ ℓ' he h1 h2 => hcap.one_flower ℓ ℓ' h1 h2 he) hcap.layer_le ?_ hN W (fun k' => k' = k) ?_
    (L := P.L) (by linarith) P.γ P.η 0 b.totalSigma ⟨c, hc, rfl⟩ (n := roots) (nfl := 0) ?_ ?_ k hdec.1 rfl
  · -- capped flowers are in layer `p`
    rintro a ⟨ℓ, hℓ, rfl⟩
    have := hcap.stem_layer ℓ.toNode ⟨ℓ, hℓ, rfl, List.prefix_refl _⟩
    omega
  · -- `hW`
    intro k' hk'
    have hcond : k' (GNode.root b.layered.garden.tree j₀) = latticePoint P.L (roots j₀) ∧
        ∀ ℓ : GLeaf b.layered.garden.tree, k' ℓ.toNode = k' (b.layered.garden.pair ℓ).toNode := by
      by_contra hc'
      exact hk' (if_neg hc')
    have hmw : markedWt P J p kSel h Rf σ Rs dag b.layered k' ≠ 0 := by
      have e : W k' = markedWt P J p kSel h Rf σ Rs dag b.layered k' := if_pos hcond
      rwa [e] at hk'
    refine ⟨fun a ha htl hnf => frontier_le_of_markedWt_ne_zero P J p kSel h Rf σ Rs dag k' hplain hcap.layer_le hj₀
      hr0 hRfr hhp hcond.2 hmw a ha htl hnf, ?_⟩
    rw [hcond.1]
    have h10 : r ^ 10 = r * r ^ 9 := by ring
    nlinarith
  · -- `hSel`
    rintro k' rfl
    refine ⟨decCast b.prime κ, 0, ?_, fun x => ?_⟩
    · have e : NormalizedSplice.GroupPrescription.ofPrescription b.totalSigma = b.sigma := by
        funext S
        exact dite_eq_left S.2
      have hs' : NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription b.totalSigma) P.L P.γ P.η 0
          (RegRed.collapseGenDecoration b.prime.data b.prime.prime.1 (decCast b.prime κ)).1 := by
        rw [e]
        exact hsel
      exact hs'
    · rw [ofForest_decCast]
      rfl
  · -- `hθ`
    rintro k' rfl
    rw [hroot]
    have h1 : P.L ^ (-P.γ + P.η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have h2 : (2 : ℝ) ^ 10 ≤ r ^ 10 := pow_le_pow_left₀ (by norm_num) hr2 10
    linarith

end WaveTurbulence.Flower.Stage1MKGate
