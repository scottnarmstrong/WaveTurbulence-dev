/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.CapFam

/-! # B3s-HELPER8 / CAP: a nontrivial cap slot (outside the STOP configuration)

For a nontrivial cap slot `K` of the representative `a`, the general slot kernel at the cap momentum is
`c₀ · capCfgKer … capMN … (ts j0)` (`genSlotKer_capN`), with D6's filter multiplier `capMN` (σ's filters, the
selection shells, the selected filter on `capSelT`). The slot carries the capped flower as a protected native node,
so its mass carries `L^{2(47d+5)}` (`hasProtNative_cap`). Cases:

* no selected branch on the paired tree, configuration not pinning the root: D3 with filters (`capF_sup`) at
  `θ = η` (`L^{31d+6}`) and, on `SelAdj` (then the configuration is `term`), at `θ = 1/4` (`L^{47d+2}`):
  `famN_sup`;
* no selected branch, a root-pinning configuration whose chain clock is pinned (`¬ CapPenFree`): the kernel is constant
  on the general box (`ts j0 ≥ rootPinVal`, `genBox_root`), bounded by D3 (`capF_pointwise`): `famN_const`;
* one selected branch `v` (pattern plain, configuration `term`, not `SelAdj`): D6 (`capA_sup`), mass
  `L^{2(47d+5)} · Rs^{-1/18}`, the slot mass's selection gain (`selNative_eq_single`): `famN_D6`;

assembled in **`capN_concl`** (`SlotConcl` for every centre). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Set
open WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.Induct
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsB WaveTurbulence.Flower.MkSlotsI

namespace WaveTurbulence.Flower.MkSlotsO

namespace CapN

section Slot

variable (P : WTParams) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
  {q : SourcePair a.prime.skeleton} (K : CapSide a.prime.data a.prime.prime.1 J q)

/-- The paired tree's profiles. -/
abbrev H1 (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ)) :
    LeafProfiles 1 P.d :=
  CapG.capH1 K.j0 (CapSide.Hq (q := q) (sourceLayer a) (sourceLayer_isLayering a)
    (anchProfiles J (recLG a) h P.L roots))

/-- **The multiplier of the slot on the paired tree** (D6's form). -/
abbrev capMN (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) :
    (GNode (K.Dq (sourceLayer a) (sourceLayer_isLayering a)).T1.garden.tree → Mom P.d) → ℂ :=
  capMA (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p)
    (IncTop.topStar (fun _ => (frontierG (Rf K.u.1) : Mom P.d → ℂ)))
    (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel) (fun _ => CapK.capMσ K P.L σ)
    (CapK.capSelT K (sourceLayer a) (sourceLayer_isLayering a) kSel) (Rs K.u.1)
    (CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
    (CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs)
    (K.capInd (sourceLayer a) (sourceLayer_isLayering a) dag)

/-- The kernel of the slot as a function of the chain clock. -/
abbrev GN (pat : Fin (2 * R) → FixPat) (t s : ℝ) (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (y : ℝ) : ℂ :=
  K.capC0 P.L P.γ P.δ s (latticePoint P.L (roots K.cleaf.1.1)) dag *
    capCfgKer P.L P.γ P.δ (K.Dq (sourceLayer a) (sourceLayer_isLayering a)) (H1 P a J K h roots)
      (capMN P a J K (p := p) σ kSel Rs Rf dag) (CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat) s t
      (latticePoint P.L (roots K.cleaf.1.1)) y

/-- **The general slot kernel of a nontrivial cap slot** is `GN (ts j0)`. -/
theorem genSlotKer_capN (hGeo : CapGeo (recLG a) J p) (hq : IsCapPair a.prime.skeleton a.prime.prime.1 J q)
    (pat : Fin (2 * R) → FixPat) (t s : ℝ) (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (ts : Fin 2 → ℝ) :
    genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inl q) ts
        (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))) =
      GN P a J K (p := p) pat t s σ kSel Rs h roots Rf dag (ts K.j0) := by
  rw [K.capTree]
  refine (CapK.slotFn_cap_T1 K (sourceLayer a) (sourceLayer_isLayering a) hGeo P.L P.γ P.δ pat t s σ kSel Rs h roots
    Rf dag hq ts).trans ?_
  refine congrArg (fun m => K.capC0 P.L P.γ P.δ s (latticePoint P.L (roots K.cleaf.1.1)) dag *
    capCfgKer P.L P.γ P.δ (K.Dq (sourceLayer a) (sourceLayer_isLayering a)) (H1 P a J K h roots) m
      (CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat) s t (latticePoint P.L (roots K.cleaf.1.1))
      (ts K.j0)) (funext fun K' => ?_)
  rw [CapK.capθ1_eq K (sourceLayer a) (sourceLayer_isLayering a) hGeo]
  simp only [capMN, capMA]
  ring

end Slot

/-! ### The common data -/

section Slot

variable {P : WTParams} (hd : 3 ≤ P.d) (hη : 0 < P.η)
  (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hL : 2 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ)
  (C : ℝ) (hC : P.C₁ ≤ C) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
  (hsz : a.prime.data.size ≤ P.N (p + 1) ^ 4) (hGeo : CapGeo (recLG a) J p)
  (b : ℝ) (hb1 : 1 ≤ b) {q : SourcePair a.prime.skeleton} (K : CapSide a.prime.data a.prime.prime.1 J q)

theorem slotSize_N : slotSize a.prime.data (.inl q) = 2 * (K.X.size / 2) := by
  rw [K.slotSize_eq]
  obtain ⟨r, hr⟩ := chain_size_even K.X
  omega

theorem one_le_n : 1 ≤ K.X.size / 2 := by have := K.two_le_size; omega

include hsz in
theorem n_le_N : K.X.size / 2 ≤ P.N (p + 1) ^ 4 := by
  have h1 : K.X.size ≤ a.prime.data.size := K.slotSize_eq ▸ Represents.slotSize_le a.prime.data (.inl q)
  omega

theorem protSize_N : protSize K.X (K.Dq (sourceLayer a) (sourceLayer_isLayering a)).T1 = 2 * (K.X.size / 2) := by
  show K.X.size = 2 * (K.X.size / 2)
  obtain ⟨r, hr⟩ := chain_size_even K.X
  omega

include hηγ hL hC1 hδ hC hb1 in
/-- **The mass of a D3/D6 superposition of the slot**, against the slot mass with loss `Lf` and gain `Π`. -/
theorem massN (Cs : ℝ≥0∞) (hCs : Cs ≠ ⊤) (Kg : ℝ) (hKg : capKcen P.d * (2 * Cs.toReal) ≤ Kg) (Λ Lf Pi : ℝ)
    (hΛ : 0 ≤ Λ) (hΛf : Λ ≤ Lf * Pi) :
    ENNReal.ofReal (capKcen P.d) * (Cs * (2 * ((∏ _a ∈ K.frontS (sourceLayer a) (sourceLayer_isLayering a) p,
        ENNReal.ofReal (frontierConst P.d)) * ENNReal.ofReal Λ *
        regBound P (K.X.size / 2) (protIncoh K.X (K.Dq (sourceLayer a) (sourceLayer_isLayering a)).T1) *
        ENNReal.ofReal (leafSizeProduct (K.Dq (sourceLayer a) (sourceLayer_isLayering a)).T1
          (fun _ => b.toNNReal))))) ≤
      ENNReal.ofReal (Kg * ((C * Real.sqrt P.δ) ^ slotSize a.prime.data (.inl q) *
        P.L ^ (-(P.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (.inl q) : ℝ)) *
        (frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 (.inl q) *
          (b⁻¹ * slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            (fun _ => b.toNNReal) (.inl q))) * Lf * Pi)) := by
  have hL1 : 1 ≤ P.L := by linarith
  have hcF0 : 0 ≤ frontierConst P.d := le_trans zero_le_one (one_le_frontierConst P.d)
  have hLSb : 0 ≤ b⁻¹ * Represents.slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (fun _ => b.toNNReal) (.inl q) := by
    refine mul_nonneg (inv_nonneg.2 (by linarith)) ?_
    unfold Represents.slotLeaf leafSizeProduct
    exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  rw [slotSize_N a J K, ← ENNReal.ofReal_toReal hCs, Finset.prod_const, ← ENNReal.ofReal_pow hcF0,
    K.protIncoh_T1 (sourceLayer a) (sourceLayer_isLayering a)]
  refine le_trans ?_ (capMass_final P C hC hC1 hδ hL1 hηγ Cs.toReal Kg ENNReal.toReal_nonneg hKg _ _
    (K.frontS_card_le (sourceLayer a) (sourceLayer_isLayering a) (p := p)) _ _ (one_le_n a J K) _ Λ Lf Pi hLSb hΛ hΛf)
  gcongr
  exact K.leafSize_T1_le (sourceLayer a) (sourceLayer_isLayering a) b hb1

end Slot

/-! ### The three cases -/

section Slot

variable {P : WTParams} (hD3 : ProtBoundAt P) (hD6 : ProtAnnBoundAt P) (hd : 3 ≤ P.d) (hη : 0 < P.η)
  (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hL : 2 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ)
  (C : ℝ) (hC : P.C₁ ≤ C) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
  (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (hp : p < P.D) (hcan : IsCanonGC (p + 1) (recLG a)) (hsz : a.prime.data.size ≤ P.N (p + 1) ^ 4)
  (hGeo : CapGeo (recLG a) J p) (hpat : CapPatValid (recLG a) J pat p)
  (hps : (p : ℝ) < s) (hst : s < t) (htp : t < p + 1)
  (σ kSel : Fin (2 * R) → Option ℕ) (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain)
  (Rs : Fin (2 * R) → ℝ) (hRs : ∀ j, P.L ≤ Rs j)
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb1 : 1 ≤ b)
  (hb : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
  (Rf : Fin (2 * R) → Option ℝ) (hRf1 : ∀ j r, Rf j = some r → 1 ≤ r)
  (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) {q : SourcePair a.prime.skeleton}
  (hq : IsCapPair a.prime.skeleton a.prime.prime.1 J q) (K : CapSide a.prime.data a.prime.prime.1 J q)
  (x : Fin P.d → ℤ)

include hRf1 in
theorem hpres_N : ∀ z ∈ K.frontS (sourceLayer a) (sourceLayer_isLayering a) p,
    IncTop.StarPresented (30 * P.d) (IncTop.topStar (fun _ => (frontierG (Rf K.u.1) : Mom P.d → ℂ)) z)
      (frontierConst P.d) :=
  fun z _ => IncTop.topStar_presented _ (fun _ => gPresented_frontierG P.d (Rf K.u.1) (hRf1 K.u.1)) z

include hL in
theorem hM_N : ∀ b' ∈ CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel,
    P.L ≤ (fun _ => CapK.capMσ K P.L σ) b' := by
  intro _ _
  have hL0 : 0 ≤ P.L := by linarith
  exact le_mul_of_one_le_left hL0 (one_le_pow₀ (by norm_num))

include hL hRs in
theorem hMu_N : ∀ b' ∈ CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel,
    P.L ≤ CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs b' := by
  intro b' _
  have hL0 : 0 ≤ P.L := by linarith
  unfold CapK.capMuT
  split_ifs
  · exact le_mul_of_one_le_left hL0 (one_le_pow₀ (by norm_num))
  · exact hRs _

theorem norm_capMF_N (K' : GNode (K.Dq (sourceLayer a) (sourceLayer_isLayering a)).T1.garden.tree → Mom P.d) :
    ‖capMF (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p)
      (IncTop.topStar (fun _ => (frontierG (Rf K.u.1) : Mom P.d → ℂ)))
      (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel) (fun _ => CapK.capMσ K P.L σ)
      (CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
      (CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs)
      (K.capInd (sourceLayer a) (sourceLayer_isLayering a) dag) K'‖ ≤ 1 := by
  unfold capMF
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (K.capInd_01 (sourceLayer a) (sourceLayer_isLayering a) dag K').1]
  have h1 := K.norm_starWeight_le (sourceLayer a) (sourceLayer_isLayering a) p Rf K'
  have h2 := norm_filtWeight_false_le (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
    (fun _ => CapK.capMσ K P.L σ) K'
  have h3 := norm_filtWeight_false_le (CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
    (CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs) K'
  have h4 := (K.capInd_01 (sourceLayer a) (sourceLayer_isLayering a) dag K').2
  have hA := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
  have hB := mul_le_mul hA h3 (norm_nonneg _) (by norm_num)
  have hC := mul_le_mul hB h4 (K.capInd_01 (sourceLayer a) (sourceLayer_isLayering a) dag K').1 (by norm_num)
  simpa using hC

theorem norm_capMN_N (K' : GNode (K.Dq (sourceLayer a) (sourceLayer_isLayering a)).T1.garden.tree → Mom P.d) :
    ‖capMN P a J K (p := p) σ kSel Rs Rf dag K'‖ ≤
      MkDefs.chiDNorm ^ (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel ∪
        CapK.capSelT K (sourceLayer a) (sourceLayer_isLayering a) kSel).card := by
  unfold capMN capMA
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (K.capInd_01 (sourceLayer a) (sourceLayer_isLayering a) dag K').1]
  have h1 := K.norm_starWeight_le (sourceLayer a) (sourceLayer_isLayering a) p Rf K'
  have h2 := norm_filtWeight_le (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel ∪
    CapK.capSelT K (sourceLayer a) (sourceLayer_isLayering a) kSel)
    (fun b => decide (b ∈ CapK.capSelT K (sourceLayer a) (sourceLayer_isLayering a) kSel))
    (fun b => if b ∈ CapK.capSelT K (sourceLayer a) (sourceLayer_isLayering a) kSel then Rs K.u.1
      else CapK.capMσ K P.L σ) K'
  have h3 := norm_filtWeight_false_le (CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
    (CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs) K'
  have h4 := (K.capInd_01 (sourceLayer a) (sourceLayer_isLayering a) dag K').2
  have hc : 0 ≤ MkDefs.chiDNorm ^ (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel ∪
      CapK.capSelT K (sourceLayer a) (sourceLayer_isLayering a) kSel).card :=
    pow_nonneg (le_trans zero_le_one MkDefs.one_le_chiDNorm) _
  have hA := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
  have hB := mul_le_mul hA h3 (norm_nonneg _) (by simpa using hc)
  have hC := mul_le_mul hB h4 (K.capInd_01 (sourceLayer a) (sourceLayer_isLayering a) dag K').1 (by simpa using hc)
  simpa using hC

include hD3 hd hηγ hL hC1 hδ hC hp hcan hsz hGeo hpat hps hst htp hRs hb1 hb hRf1 hq in
/-- **No selected branch, configuration not pinning the root**: D3 with filters at `θ = η` or (at `term`)
`θ = 1/4`. -/
theorem famN_sup (hSel : CapK.capSelT K (sourceLayer a) (sourceLayer_isLayering a) kSel = ∅)
    (hroot : (CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat).pinsRoot K.X = false)
    {θ cL : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : (θ = P.η ∧ cL = 31 * P.d + 6) ∨
      (θ = 1 / 4 ∧ cL = 47 * P.d + 2 ∧ CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat = .term))
    (hKg : capKcen P.d * (2 * (capCsup P.d θ).toReal) ≤ capKg P.d P.η)
    (Lf Pi : ℝ) (hΛf : P.L ^ cL ≤ Lf * Pi) (μ : ℝ≥0∞)
    (hμ : ENNReal.ofReal (capKg P.d P.η * ((C * Real.sqrt P.δ) ^ slotSize a.prime.data (.inl q) *
        P.L ^ (-(P.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (.inl q) : ℝ)) *
        (frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 (.inl q) *
          (b⁻¹ * slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            (fun _ => b.toNNReal) (.inl q))) * Lf * Pi)) ≤ μ) :
    SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag (.inl q) x θ μ := by
  have hL1 : 1 ≤ P.L := by linarith
  have hb0 : 0 ≤ b := le_trans zero_le_one hb1
  have hm : capMN P a J K (p := p) σ kSel Rs Rf dag =
      capMF (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p)
        (IncTop.topStar (fun _ => (frontierG (Rf K.u.1) : Mom P.d → ℂ)))
        (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel) (fun _ => CapK.capMσ K P.L σ)
        (CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
        (CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs)
        (K.capInd (sourceLayer a) (sourceLayer_isLayering a) dag) := by
    unfold capMN
    rw [hSel]
    exact capMA_empty _ _ _ _ _ _ _ _
  obtain ⟨wt, u, hw0, hws, hu, hsum, hmass⟩ := capF_sup hD3 (capCsup_spec P.d hθ0) hθ0 (by omega) hL1
    (K.Dq (sourceLayer a) (sourceLayer_isLayering a)) hp (n_le_N a J hsz K)
    (K.protShape_T1 (sourceLayer a) (sourceLayer_isLayering a) hGeo) (protSize_N a J K)
    (CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat)
    (CapP.cfgPat_valid K (sourceLayer a) (sourceLayer_isLayering a) hpat)
    (CapP.objCfg_cases K (sourceLayer a) (sourceLayer_isLayering a) pat) hθ hroot
    (K.protAmbient_T1 (sourceLayer a) (sourceLayer_isLayering a) hcan) hps hst htp
    (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p)
    (IncTop.topStar (fun _ => (frontierG (Rf K.u.1) : Mom P.d → ℂ))) (fun _ => frontierConst P.d)
    (hpres_N a J Rf hRf1 K) (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
    (fun _ => CapK.capMσ K P.L σ) (hM_N hL a J σ kSel K)
    (CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
    (CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs) (hMu_N hL a J σ kSel Rs hRs K)
    (K.capInd (sourceLayer a) (sourceLayer_isLayering a) dag)
    (K.termChild_capInd (sourceLayer a) (sourceLayer_isLayering a) dag) 1 (norm_capMF_N a J σ kSel Rs Rf dag K)
    (H1 P a J K h roots) (fun _ => b.toNNReal)
    (K.capH1_leafwise (sourceLayer a) (sourceLayer_isLayering a) hGeo h P.L roots b hb0 hb)
    (latticePoint P.L (roots K.cleaf.1.1))
  set c₀ := K.capC0 P.L P.γ P.δ s (latticePoint P.L (roots K.cleaf.1.1)) dag
  have hc₀ : ‖c₀‖ = 1 := K.norm_capC0 P.L P.γ P.δ s _ dag
  have hcu : ∀ m, ‖c₀ * u m‖ ≤ 1 := fun m => by rw [norm_mul, hc₀, one_mul]; exact hu m
  refine slotFam1_of_sup P a J pat t s σ kSel Rs h roots Rf dag q x hq θ hθ0 K.j0
    (GN P a J K (p := p) pat t s σ kSel Rs h roots Rf dag) wt (fun m => c₀ * u m) hw0 hws hcu
    (fun y hy => ?_) (fun ts hts => CapK.genBox_j0 K (sourceLayer a) (sourceLayer_isLayering a) hGeo pat t s hps hst htp
      ts hts) (fun ts _ => genSlotKer_capN P a J K hGeo hq pat t s σ kSel Rs h roots Rf dag ts) μ ?_
  · show HasSum _ (c₀ * capCfgKer P.L P.γ P.δ (K.Dq (sourceLayer a) (sourceLayer_isLayering a)) (H1 P a J K h roots)
      (capMN P a J K (p := p) σ kSel Rs Rf dag) (CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat) s t
      (latticePoint P.L (roots K.cleaf.1.1)) y)
    rw [hm]
    refine ((hsum y hy).mul_left c₀).congr_fun fun m => ?_
    ring
  · refine le_trans (mul_le_mul' le_rfl hmass) (le_trans ?_ hμ)
    exact massN hηγ hL hC1 hδ C hC a J b hb1 K (capCsup P.d θ) (capCsup_ne_top P.d θ) (capKg P.d P.η) hKg
      (P.L ^ cL) Lf Pi (Real.rpow_nonneg (by linarith) _) hΛf

include hD3 hd hη hηγ hL hC1 hδ hC hp hcan hsz hGeo hpat hps hst htp hRs hb1 hb hRf1 hq in
/-- **No selected branch, a root-pinning configuration with a pinned chain clock**: the kernel is constant on the
general box, bounded by D3 (any moment weight `θ`). -/
theorem famN_const (hSel : CapK.capSelT K (sourceLayer a) (sourceLayer_isLayering a) kSel = ∅)
    (hroot : (CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat).pinsRoot K.X = true)
    (hpinned : CapK.clkJ0 K (sourceLayer a) (sourceLayer_isLayering a) pat t s ≠ none) (θ : ℝ)
    (Lf Pi : ℝ) (hΛf : P.L ^ (31 * (P.d : ℝ) + 6) ≤ Lf * Pi) (μ : ℝ≥0∞)
    (hμ : ENNReal.ofReal (capKg P.d P.η * ((C * Real.sqrt P.δ) ^ slotSize a.prime.data (.inl q) *
        P.L ^ (-(P.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (.inl q) : ℝ)) *
        (frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 (.inl q) *
          (b⁻¹ * slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            (fun _ => b.toNNReal) (.inl q))) * Lf * Pi)) ≤ μ) :
    SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag (.inl q) x θ μ := by
  have hL1 : 1 ≤ P.L := by linarith
  have hb0 : 0 ≤ b := le_trans zero_le_one hb1
  have hm : capMN P a J K (p := p) σ kSel Rs Rf dag =
      capMF (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p)
        (IncTop.topStar (fun _ => (frontierG (Rf K.u.1) : Mom P.d → ℂ)))
        (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel) (fun _ => CapK.capMσ K P.L σ)
        (CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
        (CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs)
        (K.capInd (sourceLayer a) (sourceLayer_isLayering a) dag) := by
    unfold capMN
    rw [hSel]
    exact capMA_empty _ _ _ _ _ _ _ _
  set cfg := CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat with hcfgdef
  have hcfg := CapP.objCfg_cases K (sourceLayer a) (sourceLayer_isLayering a) pat
  have hne := cfg_ne_trace cfg hcfg
  set mF := capMF (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p)
        (IncTop.topStar (fun _ => (frontierG (Rf K.u.1) : Mom P.d → ℂ)))
        (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel) (fun _ => CapK.capMσ K P.L σ)
        (CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
        (CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs)
        (K.capInd (sourceLayer a) (sourceLayer_isLayering a) dag) with hmF
  set G := capCfgKer P.L P.γ P.δ (K.Dq (sourceLayer a) (sourceLayer_isLayering a)) (H1 P a J K h roots) mF cfg s t
    (latticePoint P.L (roots K.cleaf.1.1)) with hG
  have hconst : ∀ y, rootPinVal cfg s t ≤ y → G y = G t := by
    intro y hy
    rw [hG]
    unfold capCfgKer
    rw [fix_up_indep cfg hne K.X s t y 0, fix_up_indep cfg hne K.X s t t 0]
    obtain ⟨hr1, hr2⟩ := pinsRoot_fix hroot s t 0 hst.le
      (T := (K.Dq (sourceLayer a) (sourceLayer_isLayering a)).T1.garden.tree)
    exact kernelProt_up_const _ _ _ _ _ _ 0 _ _ _ _ (rootPinVal cfg s t)
      (fun b hb => by rw [hr1 b hb]; exact Option.some_ne_none _) hr2 y t hy (rootPinVal_le cfg hst.le)
  have hbound := capF_pointwise hD3 (K.Dq (sourceLayer a) (sourceLayer_isLayering a)) hη.le (by omega) hL1 hp
    (n_le_N a J hsz K) (K.protShape_T1 (sourceLayer a) (sourceLayer_isLayering a) hGeo) (protSize_N a J K) cfg
    (CapP.cfgPat_valid K (sourceLayer a) (sourceLayer_isLayering a) hpat) hcfg hroot
    (K.protAmbient_T1 (sourceLayer a) (sourceLayer_isLayering a) hcan) hps hst htp
    (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p)
    (IncTop.topStar (fun _ => (frontierG (Rf K.u.1) : Mom P.d → ℂ))) (fun _ => frontierConst P.d)
    (hpres_N a J Rf hRf1 K) (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
    (fun _ => CapK.capMσ K P.L σ) (hM_N hL a J σ kSel K)
    (CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
    (CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs) (hMu_N hL a J σ kSel Rs hRs K)
    (K.capInd (sourceLayer a) (sourceLayer_isLayering a) dag)
    (K.termChild_capInd (sourceLayer a) (sourceLayer_isLayering a) dag) 1 (norm_capMF_N a J σ kSel Rs Rf dag K)
    (H1 P a J K h roots) (fun _ => b.toNNReal)
    (K.capH1_leafwise (sourceLayer a) (sourceLayer_isLayering a) hGeo h P.L roots b hb0 hb)
    (latticePoint P.L (roots K.cleaf.1.1)) t ⟨le_rfl, htp.le⟩
  set c₀ := K.capC0 P.L P.γ P.δ s (latticePoint P.L (roots K.cleaf.1.1)) dag
  have hc₀ : ‖c₀‖ = 1 := K.norm_capC0 P.L P.γ P.δ s _ dag
  refine slotFam1_of_const P a J pat t s σ kSel Rs h roots Rf dag q x hq θ (c₀ * G t) (fun ts hts => ?_) μ ?_
  · rw [genSlotKer_capN P a J K hGeo hq pat t s σ kSel Rs h roots Rf dag ts]
    show c₀ * capCfgKer P.L P.γ P.δ (K.Dq (sourceLayer a) (sourceLayer_isLayering a)) (H1 P a J K h roots)
      (capMN P a J K (p := p) σ kSel Rs Rf dag) cfg s t (latticePoint P.L (roots K.cleaf.1.1)) (ts K.j0) = c₀ * G t
    rw [hm]
    exact congrArg (c₀ * ·) (hconst _ (CapK.genBox_root K (sourceLayer a) (sourceLayer_isLayering a) pat t s hst
      hroot hpinned ts hts))
  · have h12 : ENNReal.ofReal (1 / 2) * 2 = 1 := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
      exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    rw [← ofReal_norm, norm_mul, hc₀, one_mul, ofReal_norm]
    refine le_trans ?_ (le_trans (massN hηγ hL hC1 hδ C hC a J b hb1 K (p := p) (ENNReal.ofReal (1 / 2)) ENNReal.ofReal_ne_top
      (capKg P.d P.η) (by rw [ENNReal.toReal_ofReal (by norm_num)]; exact capKg_half P.d P.η)
      (P.L ^ (31 * (P.d : ℝ) + 6)) Lf Pi (Real.rpow_nonneg (by linarith) _) hΛf) hμ)
    refine mul_le_mul' le_rfl (hbound.trans (le_of_eq ?_))
    rw [← mul_assoc, h12, one_mul]

include hD6 hd hη hηγ hL hC1 hδ hC hp hcan hsz hGeo hps hst htp hRs hb1 hb hRf1 hq hplain in
/-- **One selected branch `v1` on the paired tree**: pattern plain, configuration `term`; D6 at `θ = η` with the
selection gain. -/
theorem famN_D6 (v1 : GBranch (K.Dq (sourceLayer a) (sourceLayer_isLayering a)).T1.garden.tree)
    (hv1 : v1 ∈ CapK.capSelT K (sourceLayer a) (sourceLayer_isLayering a) kSel) (μ : ℝ≥0∞)
    (hμ : ENNReal.ofReal (capKg P.d P.η * ((C * Real.sqrt P.δ) ^ slotSize a.prime.data (.inl q) *
        P.L ^ (-(P.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (.inl q) : ℝ)) *
        (frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 (.inl q) *
          (b⁻¹ * slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            (fun _ => b.toNNReal) (.inl q))) * P.L ^ genLossExp P.d * Rs K.u.1 ^ (-(1 / 18 : ℝ)))) ≤ μ) :
    SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag (.inl q) x P.η μ := by
  have hL1 : 1 ≤ P.L := by linarith
  have hb0 : 0 ≤ b := le_trans zero_le_one hb1
  have hpl := CapK.capSel_plain K (sourceLayer a) (sourceLayer_isLayering a) pat kSel hplain v1 hv1
  have hcfg := CapK.cfg_term_of_plain K (sourceLayer a) (sourceLayer_isLayering a) pat hpl
  have hSel1 := CapK.capSelT_single K (sourceLayer a) (sourceLayer_isLayering a) kSel v1 hv1
  obtain ⟨ch1, ch2, ch3⟩ := CapK.capSel_chain K (sourceLayer a) (sourceLayer_isLayering a) hGeo kSel v1 hv1
  have hm : capMN P a J K (p := p) σ kSel Rs Rf dag =
      capMA (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p)
        (IncTop.topStar (fun _ => (frontierG (Rf K.u.1) : Mom P.d → ℂ)))
        (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel) (fun _ => CapK.capMσ K P.L σ) {v1}
        (Rs K.u.1) (CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
        (CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs)
        (K.capInd (sourceLayer a) (sourceLayer_isLayering a) dag) := by
    unfold capMN
    rw [hSel1]
  have hnorm : ∀ K', ‖capMA (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p)
        (IncTop.topStar (fun _ => (frontierG (Rf K.u.1) : Mom P.d → ℂ)))
        (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel) (fun _ => CapK.capMσ K P.L σ) {v1}
        (Rs K.u.1) (CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
        (CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs)
        (K.capInd (sourceLayer a) (sourceLayer_isLayering a) dag) K'‖ ≤
      MkDefs.chiDNorm ^ (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel ∪
        CapK.capSelT K (sourceLayer a) (sourceLayer_isLayering a) kSel).card := fun K' => by
    rw [← hm]; exact norm_capMN_N a J σ kSel Rs Rf dag K K'
  obtain ⟨wt, u, hw0, hws, hu, hsum, hmass⟩ := capA_sup hD6 (capCsup_spec P.d hη.le) hη.le (by omega) hL1
    (K.Dq (sourceLayer a) (sourceLayer_isLayering a)) hp (n_le_N a J hsz K)
    (K.protShape_T1 (sourceLayer a) (sourceLayer_isLayering a) hGeo) (protSize_N a J K) (lonePath_ne_nil K.ne) v1
    ch1 ch2 ch3 (K.protAmbient_T1 (sourceLayer a) (sourceLayer_isLayering a) hcan) (Rs K.u.1) (hRs _) (t := t) hps
    (by linarith) (CapK.capT1_lone_layer K (sourceLayer a) (sourceLayer_isLayering a) hGeo)
    (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p)
    (IncTop.topStar (fun _ => (frontierG (Rf K.u.1) : Mom P.d → ℂ))) (fun _ => frontierConst P.d)
    (hpres_N a J Rf hRf1 K) (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
    (fun _ => CapK.capMσ K P.L σ) (hM_N hL a J σ kSel K)
    (CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
    (CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs) (hMu_N hL a J σ kSel Rs hRs K)
    (K.capInd (sourceLayer a) (sourceLayer_isLayering a) dag)
    (K.termChild_capInd (sourceLayer a) (sourceLayer_isLayering a) dag) _ hnorm
    (H1 P a J K h roots) (fun _ => b.toNNReal)
    (K.capH1_leafwise (sourceLayer a) (sourceLayer_isLayering a) hGeo h P.L roots b hb0 hb)
    (latticePoint P.L (roots K.cleaf.1.1))
  set c₀ := K.capC0 P.L P.γ P.δ s (latticePoint P.L (roots K.cleaf.1.1)) dag
  have hc₀ : ‖c₀‖ = 1 := K.norm_capC0 P.L P.γ P.δ s _ dag
  have hcu : ∀ m, ‖c₀ * u m‖ ≤ 1 := fun m => by rw [norm_mul, hc₀, one_mul]; exact hu m
  refine slotFam1_of_sup P a J pat t s σ kSel Rs h roots Rf dag q x hq P.η hη.le K.j0
    (GN P a J K (p := p) pat t s σ kSel Rs h roots Rf dag) wt (fun m => c₀ * u m) hw0 hws hcu
    (fun y hy => ?_) (fun ts hts => CapK.genBox_j0 K (sourceLayer a) (sourceLayer_isLayering a) hGeo pat t s hps hst htp
      ts hts) (fun ts _ => genSlotKer_capN P a J K hGeo hq pat t s σ kSel Rs h roots Rf dag ts) μ ?_
  · show HasSum _ (c₀ * capCfgKer P.L P.γ P.δ (K.Dq (sourceLayer a) (sourceLayer_isLayering a)) (H1 P a J K h roots)
      (capMN P a J K (p := p) σ kSel Rs Rf dag) (CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat) s t
      (latticePoint P.L (roots K.cleaf.1.1)) y)
    rw [hm, hcfg]
    refine ((hsum y hy).mul_left c₀).congr_fun fun m => ?_
    ring
  · have hpow : P.L ^ ((47 * P.d + 5) * 2) = P.L ^ genLossExp P.d := by
      rw [genLossExp, ← Real.rpow_natCast]
      push_cast
      ring_nf
    have hRs0 : 0 ≤ Rs K.u.1 ^ (-((1 : ℝ) / 18)) := Real.rpow_nonneg (le_trans (by linarith) (hRs _)) _
    refine le_trans (mul_le_mul' le_rfl hmass) (le_trans ?_ hμ)
    refine massN hηγ hL hC1 hδ C hC a J b hb1 K (capCsup P.d P.η) (capCsup_ne_top P.d P.η) (capKg P.d P.η)
      (capKg_eta P.d P.η) _ (P.L ^ genLossExp P.d) (Rs K.u.1 ^ (-(1 / 18 : ℝ)))
      (mul_nonneg (pow_nonneg (by linarith) _) hRs0) (le_of_eq ?_)
    rw [hpow]

include hD3 hD6 hd hη hηγ hL hC1 hδ hC hp hcan hsz hGeo hpat hps hst htp hplain hRs hb1 hb hRf1 hq in
/-- **A nontrivial cap slot outside the STOP configuration** (`¬ CapPenFree`). -/
theorem capN_concl (hfree : ¬ CapK.CapPenFree K (sourceLayer a) (sourceLayer_isLayering a) pat t s) :
    SlotConcl P C capKg (p := p) a J pat t s σ kSel Rs h roots Rf dag b (.inl q) x := by
  have hL1 : 1 ≤ P.L := by linarith
  have hprot := CapK.hasProtNative_cap K (sourceLayer a) (sourceLayer_isLayering a) pat t s kSel
  have hmass := genSlotMass_cap P C b a J pat t s kSel Rs q hq hprot
  have hLg : 1 ≤ P.L ^ genLossExp P.d := Real.one_le_rpow hL1 (by unfold genLossExp; positivity)
  have hLq : 1 ≤ P.L ^ (47 * (P.d : ℝ) + 2) := Real.one_le_rpow hL1 (by positivity)
  have hd0 : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
  have h31 : P.L ^ (31 * (P.d : ℝ) + 6) ≤ P.L ^ genLossExp P.d * 1 := by
    rw [mul_one]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by unfold genLossExp; linarith)
  by_cases hSel : CapK.capSelT K (sourceLayer a) (sourceLayer_isLayering a) kSel = ∅
  · have hselN := CapK.selNative_eq_empty K (sourceLayer a) (sourceLayer_isLayering a) hGeo kSel hSel
    rw [hselN, Finset.prod_empty] at hmass
    have hμη : ENNReal.ofReal (capKg P.d P.η * ((C * Real.sqrt P.δ) ^ slotSize a.prime.data (.inl q) *
        P.L ^ (-(P.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (.inl q) : ℝ)) *
        (frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 (.inl q) *
          (b⁻¹ * slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            (fun _ => b.toNNReal) (.inl q))) * P.L ^ genLossExp P.d * 1)) ≤
        ENNReal.ofReal (capKg P.d P.η * genSlotMass P C b a J pat t s kSel Rs (.inl q)) := by
      rw [hmass]
    have hm0 : 0 ≤ genSlotMass P C b a J pat t s kSel Rs (.inl q) :=
      genSlotMass_nonneg P (by linarith) hb1 (by linarith) a J pat t s kSel Rs
        (fun j => lt_of_lt_of_le (by linarith) (hRs j)) (.inl q)
    have hKg0 : 0 ≤ capKg P.d P.η := le_trans zero_le_one (one_le_capKg P.d P.η)
    have hηq : ENNReal.ofReal (capKg P.d P.η * genSlotMass P C b a J pat t s kSel Rs (.inl q)) ≤
        ENNReal.ofReal (capKg P.d P.η * P.L ^ (47 * (P.d : ℝ) + 2) *
          genSlotMass P C b a J pat t s kSel Rs (.inl q)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      calc capKg P.d P.η * genSlotMass P C b a J pat t s kSel Rs (.inl q)
          = capKg P.d P.η * 1 * genSlotMass P C b a J pat t s kSel Rs (.inl q) := by ring
        _ ≤ _ := by gcongr
    cases hr : (CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat).pinsRoot K.X with
    | false =>
      refine slotConcl_of_fam1 P C capKg a J pat t s σ kSel Rs h roots Rf dag b (.inl q) x (fun _ => ?_)
        (fun hadj => ?_)
      · exact famN_sup (hD3 := hD3) (hd := hd) (hηγ := hηγ) (hL := hL) (hC1 := hC1) (hδ := hδ) (C := C) (hC := hC)
          (a := a) (J := J) (pat := pat) (t := t) (s := s) (hp := hp) (hcan := hcan) (hsz := hsz) (hGeo := hGeo)
          (hpat := hpat) (hps := hps) (hst := hst) (htp := htp) (σ := σ) (kSel := kSel) (Rs := Rs) (hRs := hRs)
          (roots := roots) (h := h) (b := b) (hb1 := hb1) (hb := hb) (Rf := Rf) (hRf1 := hRf1) (dag := dag)
          (hq := hq) (K := K) (x := x) (hSel := hSel) (hroot := hr) (hθ0 := hη.le) (hθ := Or.inl ⟨rfl, rfl⟩)
          (hKg := capKg_eta P.d P.η) (Lf := P.L ^ genLossExp P.d) (Pi := 1) (hΛf := h31) (hμ := hμη)
      · have hcfg := CapK.cfg_term_of_plain K (sourceLayer a) (sourceLayer_isLayering a) pat
          (CapK.selAdj_cap K (sourceLayer a) (sourceLayer_isLayering a) pat kSel hplain hadj).1
        refine famN_sup (hD3 := hD3) (hd := hd) (hηγ := hηγ) (hL := hL) (hC1 := hC1) (hδ := hδ) (C := C) (hC := hC)
          (a := a) (J := J) (pat := pat) (t := t) (s := s) (hp := hp) (hcan := hcan) (hsz := hsz) (hGeo := hGeo)
          (hpat := hpat) (hps := hps) (hst := hst) (htp := htp) (σ := σ) (kSel := kSel) (Rs := Rs) (hRs := hRs)
          (roots := roots) (h := h) (b := b) (hb1 := hb1) (hb := hb) (Rf := Rf) (hRf1 := hRf1) (dag := dag)
          (hq := hq) (K := K) (x := x) (hSel := hSel) (hroot := hr) (hθ0 := by norm_num)
          (hθ := Or.inr ⟨rfl, rfl, hcfg⟩) (hKg := capKg_quarter P.d P.η)
          (Lf := P.L ^ (47 * (P.d : ℝ) + 2) * P.L ^ genLossExp P.d) (Pi := 1) (hΛf := ?_) (hμ := ?_)
        · rw [mul_one]
          exact le_mul_of_one_le_right (Real.rpow_nonneg (by linarith) _) hLg
        · rw [hmass]
          exact le_of_eq (congrArg ENNReal.ofReal (by ring))
    | true =>
      have hpinned : CapK.clkJ0 K (sourceLayer a) (sourceLayer_isLayering a) pat t s ≠ none :=
        fun h0 => hfree ⟨hr, h0⟩
      refine slotConcl_of_fam1 P C capKg a J pat t s σ kSel Rs h roots Rf dag b (.inl q) x (fun _ => ?_)
        (fun _ => ?_)
      · exact famN_const (hD3 := hD3) (hd := hd) (hη := hη) (hηγ := hηγ) (hL := hL) (hC1 := hC1) (hδ := hδ)
          (C := C) (hC := hC) (a := a) (J := J) (pat := pat) (t := t) (s := s) (hp := hp) (hcan := hcan) (hsz := hsz)
          (hGeo := hGeo) (hpat := hpat) (hps := hps) (hst := hst) (htp := htp) (σ := σ) (kSel := kSel) (Rs := Rs)
          (hRs := hRs) (roots := roots) (h := h) (b := b) (hb1 := hb1) (hb := hb) (Rf := Rf) (hRf1 := hRf1)
          (dag := dag) (hq := hq) (K := K) (x := x) (hSel := hSel) (hroot := hr) (hpinned := hpinned) (θ := P.η)
          (Lf := P.L ^ genLossExp P.d) (Pi := 1) (hΛf := h31) (hμ := hμη)
      · exact famN_const (hD3 := hD3) (hd := hd) (hη := hη) (hηγ := hηγ) (hL := hL) (hC1 := hC1) (hδ := hδ)
          (C := C) (hC := hC) (a := a) (J := J) (pat := pat) (t := t) (s := s) (hp := hp) (hcan := hcan) (hsz := hsz)
          (hGeo := hGeo) (hpat := hpat) (hps := hps) (hst := hst) (htp := htp) (σ := σ) (kSel := kSel) (Rs := Rs)
          (hRs := hRs) (roots := roots) (h := h) (b := b) (hb1 := hb1) (hb := hb) (Rf := Rf) (hRf1 := hRf1)
          (dag := dag) (hq := hq) (K := K) (x := x) (hSel := hSel) (hroot := hr) (hpinned := hpinned) (θ := 1 / 4)
          (Lf := P.L ^ genLossExp P.d) (Pi := 1) (hΛf := h31) (hμ := hμη.trans hηq)
  · obtain ⟨v1, hv1⟩ := Finset.nonempty_iff_ne_empty.2 hSel
    have hselN := CapK.selNative_eq_single K (sourceLayer a) (sourceLayer_isLayering a) hGeo kSel v1 hv1
    rw [hselN, Finset.prod_singleton] at hmass
    refine slotConcl_of_fam1 P C capKg a J pat t s σ kSel Rs h roots Rf dag b (.inl q) x (fun _ => ?_)
      (fun hadj => absurd (CapK.selAdj_cap K (sourceLayer a) (sourceLayer_isLayering a) pat kSel hplain hadj).2 hSel)
    exact famN_D6 (hD6 := hD6) (hd := hd) (hη := hη) (hηγ := hηγ) (hL := hL) (hC1 := hC1) (hδ := hδ)
      (C := C) (hC := hC) (a := a) (J := J) (pat := pat) (t := t) (s := s) (hp := hp) (hcan := hcan) (hsz := hsz)
      (hGeo := hGeo) (hps := hps) (hst := hst) (htp := htp) (σ := σ) (kSel := kSel) (hplain := hplain) (Rs := Rs)
      (hRs := hRs) (roots := roots) (h := h) (b := b) (hb1 := hb1) (hb := hb) (Rf := Rf) (hRf1 := hRf1)
      (dag := dag) (hq := hq) (K := K) (x := x) (v1 := v1) (hv1 := hv1) (hμ := by rw [hmass]; exact le_rfl)

end Slot

end CapN

end WaveTurbulence.Flower.MkSlotsO
