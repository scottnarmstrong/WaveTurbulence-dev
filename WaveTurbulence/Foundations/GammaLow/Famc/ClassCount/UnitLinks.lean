/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.TVineFacts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Low
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitLinks
/-! # CLASSCOUNT over `𝒱_γ`: the transfer matrices of the ingredient vines are `Link.Ok` (packet L5c, item I)

L5c port of main `WaveTurbulence.Foundations.Stage1.ClassCount.UnitLinks` (sha256 in COPIED-SHA256SUMS) to the members
of `𝒱_γ`, `γ ≤ 1/2` ((I), (II) and the T-vines):
* (I)/(II) are drawn vines: main's `link_ok_good` / `link_ok_bad` apply, after `vineIncoh_drawn` (L5a's `vineIncoh` is
  main's `vineIncoh` on them);
* T-vines: the good link by **layervine′, improved bound** (`LayervineTVineImproved`, item D) and the bad link by
  **layervine′, first bound** (`LayervineTVineFirst`, item D), with `m` from `|T| = 2m + 5` (`tvine_card_odd`), the
  incoherency index `tvineIncoherency` (`vineIncoh_tvine`) and `g ≤ m + 1` (`tvineIncoherency_le`).
The constants are the maxima of main's and layervine′'s; the bad weight is `Cb^m (Cb^{𝔇+1})^{g+1}`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.LayerCnt WaveTurbulence.LFTwist
open WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.ClassCount (Link linkOf Msum bw restr DistinctOn exists_transversal sum_bw_eq_image msum_nonneg
  msum_eq_transversal sum_msum_le vmOf vmOf_spec vmOf_le)

section vm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The `m` of a member of `𝒱_γ`: main's `vmOf` for a drawn vine, `(|T| − 5)/2` otherwise (T-vines). -/
noncomputable def vmOfG (M : Molecule V D) (T : Finset V) (x y : V) : ℕ := by
  classical
  exact if ∃ X, M.IsVine X T x y then vmOf M T x y else (T.card - 5) / 2

theorem vmOfG_drawn {M : Molecule V D} {T : Finset V} {x y : V} (h : ∃ X, M.IsVine X T x y) :
    vmOfG M T x y = vmOf M T x y := by
  unfold vmOfG; exact if_pos h

/-- A T-vine has `2 vmOfG + 5` atoms. -/
theorem vmOfG_tvine {M : Molecule V D} {T : Finset V} {x y : V} (hT : M.IsTVine T x y) :
    T.card = 2 * vmOfG M T x y + 5 := by
  obtain ⟨m, hm⟩ := tvine_card_odd hT
  by_cases h : ∃ X, M.IsVine X T x y
  · rw [vmOfG_drawn h]
    obtain ⟨X, -, h1, h2⟩ := vmOf_spec h
    cases hb : X.IsBad
    · exact h2 hb
    · have := h1 hb; omega
  · unfold vmOfG; simp only [h, if_false, hm]; omega

theorem vmOfG_le {M : Molecule V D} {T : Finset V} {x y : V} : vmOfG M T x y ≤ T.card := by
  by_cases h : ∃ X, M.IsVine X T x y
  · rw [vmOfG_drawn h]; exact vmOf_le h
  · unfold vmOfG; simp only [h, if_false]; omega

end vm

/-- L5a's `vineIncoh` of a drawn vine of type (I)/(II) is main's. -/
theorem vineIncoh_drawn (γ : ℝ) [Fact (γ ≤ 1 / 2)] {w : ℕ} (G : Garden w) (layer0 : GBranch G.tree → ℕ)
    {X : VineType} {T : Finset (GBranch G.tree)} {x y : GBranch G.tree} (hX : G.molecule.IsVine X T x y)
    (hb : X.IsBad = true) : Fama.vineIncoh γ G layer0 T = RedSplice.vineIncoh G layer0 T := by
  have hM := Mole.garden_isMolecule G
  obtain ⟨-, ⟨R⟩⟩ := isVine_iff_realization.mp hX
  rw [ClassCount.vineIncoh_eq G hM hX R layer0]
  have hex : ∃ X p q, X.IsBad = true ∧ G.molecule.IsVine X T p q := ⟨X, x, y, hb, hX⟩
  unfold Fama.vineIncoh
  rw [dif_pos hex]
  exact ClassCount.realizedIncoherencyIndex_any hM R _ hX.1 hex.choose_spec.choose_spec.choose_spec.2.1 layer0

section mono
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

theorem linkOf_ok_good_mono (M : Molecule V D) (T : Finset V) (x y : V) (𝓗 : Finset (V → ℕ)) {𝔇 m : ℕ}
    {C C' : ℝ} (hC : 1 ≤ C) (hCC : C ≤ C') (h : (linkOf M 2 T x y 𝓗 (true, C ^ m, 0)).Ok 𝔇 C) :
    (linkOf M 2 T x y 𝓗 (true, C' ^ m, 0)).Ok 𝔇 C' := by
  obtain ⟨h0, h1, h2, -⟩ := h
  refine ⟨h0, fun hg => ⟨pow_nonneg (by linarith) _, fun s t hts => ?_⟩, h2, fun h => absurd h (by simp [linkOf])⟩
  obtain ⟨-, hb⟩ := h1 hg
  calc (linkOf M 2 T x y 𝓗 (true, C' ^ m, 0)).M s t = (linkOf M 2 T x y 𝓗 (true, C ^ m, 0)).M s t := rfl
    _ ≤ C ^ m * C ^ (s - t) := hb s t hts
    _ ≤ C' ^ m * C' ^ (s - t) :=
      mul_le_mul (pow_le_pow_left₀ (by linarith) hCC m) (pow_le_pow_left₀ (by linarith) hCC _)
        (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)

theorem linkOf_ok_bad_mono (M : Molecule V D) (T : Finset V) (x y : V) (𝓗 : Finset (V → ℕ)) {𝔇 : ℕ} {K b b' : ℝ}
    (hbb : b ≤ b') (h : (linkOf M 2 T x y 𝓗 (false, 0, b)).Ok 𝔇 K) :
    (linkOf M 2 T x y 𝓗 (false, 0, b')).Ok 𝔇 K := by
  obtain ⟨h0, -, -, h3⟩ := h
  exact ⟨h0, fun h => absurd h (by simp [linkOf]), fun h => absurd h (by simp [linkOf]),
    fun hg => (h3 hg).trans hbb⟩

end mono

/-- **The good link over `𝒱_γ` is `Ok`** (main `link_ok_good`; T-vines by layervine′, improved bound). -/
theorem link_ok_goodG (hImp : LayervineTVineImproved) : ∃ C₀ : ℝ, 1 ≤ C₀ ∧
    ∀ (γ : ℝ) [Fact (γ ≤ 1 / 2)] {w : ℕ} (G : Garden w) (hG : G.IsPlain) (p 𝔇 : ℕ)
      (𝓖 : Finset (GBranch G.tree → ℕ)) (h𝓖 : ∀ f ∈ 𝓖, IsBranchPrelayering G f)
      (T : Finset (GBranch G.tree)) (x y : GBranch G.tree) (hV : Src.IsSomeVine γ G.molecule T x y)
      (hCL : Mole.CLParentPattern G T x y)
      (hgood : ∀ f ∈ 𝓖, SourceRegion G hG p T x f ∧ Fama.vineIncoh γ G f T = 0)
      (𝓗 : Finset (GBranch G.tree → ℕ)) (h𝓗 : 𝓗 ⊆ 𝓖),
      (linkOf G.molecule 2 T x y 𝓗 (true, C₀ ^ vmOfG G.molecule T x y, 0)).Ok 𝔇 C₀ := by
  obtain ⟨C₁, hC₁, hm⟩ := ClassCount.link_ok_good
  obtain ⟨C₂, hC₂, ht⟩ := hImp 2 (by norm_num)
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, ?_⟩
  intro γ _ w G hG p 𝔇 𝓖 h𝓖 T x y hV hCL hgood 𝓗 h𝓗
  have hγ : γ ≤ 1 / 2 := Fact.out
  have hdrawn : ∀ X, G.molecule.IsVine X T x y → X.IsBad = true →
      (linkOf G.molecule 2 T x y 𝓗 (true, max C₁ C₂ ^ vmOfG G.molecule T x y, 0)).Ok 𝔇 (max C₁ C₂) := by
    intro X hX hb
    have hd : ∃ X, G.molecule.IsVine X T x y := ⟨X, hX⟩
    rw [vmOfG_drawn hd]
    refine linkOf_ok_good_mono _ _ _ _ _ hC₁ (le_max_left _ _)
      (hm G hG p 𝔇 𝓖 h𝓖 T x y hd hCL (fun f hf => ⟨(hgood f hf).1, ?_⟩) 𝓗 h𝓗)
    rw [← vineIncoh_drawn γ G f hX hb]; exact (hgood f hf).2
  rcases (Src.isSomeVine_low_iff hγ).mp hV with hX | hX | hT
  · exact hdrawn _ hX rfl
  · exact hdrawn _ hX rfl
  · refine linkOf_ok_good_mono _ _ _ _ _ hC₂ (le_max_right _ _) ?_
    have hcard := vmOfG_tvine hT
    have hyT : y ∈ T := hT.1.2.2.1
    refine ⟨fun s t => msum_nonneg G.molecule (by norm_num) T x y 𝓗 s t,
      fun _ => ⟨pow_nonneg (by linarith) _, ?_⟩, fun _ => ?_, fun h => absurd h (by simp [linkOf])⟩
    · intro s t hts
      obtain ⟨𝓕, h𝓕sub, hdist, hM⟩ := msum_eq_transversal G.molecule 2 T x y 𝓗 s t
      simp only [linkOf]
      rw [hM]
      have hmem : ∀ f ∈ 𝓕, f ∈ 𝓖 ∧ f x = s ∧ f y = t := by
        intro f hf
        have := Finset.mem_filter.mp (h𝓕sub hf)
        exact ⟨h𝓗 this.1, this.2.1, this.2.2⟩
      have := ht G T x y hT hCL (vmOfG G.molecule T x y) hcard p s t 𝓕
        (fun f hf => (hgood f (hmem f hf).1).1.prelayering)
        (fun f hf => by rw [← vineIncoh_tvine γ G f hT]; exact (hgood f (hmem f hf).1).2)
        (fun f hf => ⟨(hmem f hf).2.1, (hmem f hf).2.2⟩)
        (fun f hf => (hgood f (hmem f hf).1).1.canonPairs) hdist
      calc ∑ f ∈ 𝓕, bw G.molecule 2 T f ≤ C₂ ^ (vmOfG G.molecule T x y + (s - t)) := this
        _ = C₂ ^ vmOfG G.molecule T x y * C₂ ^ (s - t) := pow_add _ _ _
    · intro s t hst
      simp only [linkOf, Msum]
      refine Finset.sum_eq_zero fun r hr => ?_
      exfalso
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hr
      have hfm := Finset.mem_filter.mp hf
      obtain ⟨hf1, hf2, hf3⟩ : f ∈ 𝓗 ∧ f x = s ∧ f y = t := ⟨hfm.1, hfm.2.1, hfm.2.2⟩
      have := layer_le_upper G hT.1 hCL (h𝓖 f (h𝓗 hf1)) y hyT
      omega

/-- The constant of main's bad link. -/
noncomputable abbrev Kmain : ℝ := (2 : ℝ) ^ 21 * 3 ^ 48 * 2 ^ 60

/-- **The bad link over `𝒱_γ` is `Ok`** (main `link_ok_bad`; T-vines by layervine′, first bound), with weight
`Cb^m (Cb^{𝔇+1})^{g+1}`. -/
theorem link_ok_badG (hFirst : LayervineTVineFirst) : ∃ Cb : ℝ, 1 ≤ Cb ∧
    ∀ (γ : ℝ) [Fact (γ ≤ 1 / 2)] {w : ℕ} (G : Garden w) (𝔇 : ℕ) (K : ℝ) (𝓖 : Finset (GBranch G.tree → ℕ))
      (h𝓖 : ∀ f ∈ 𝓖, IsBranchPrelayering G f ∧ ∀ x, f x ≤ 𝔇)
      (T : Finset (GBranch G.tree)) (x y : GBranch G.tree) (hV : Src.IsSomeVine γ G.molecule T x y) (g : ℕ)
      (hg : ∀ f ∈ 𝓖, Fama.vineIncoh γ G f T = g) (𝓗 : Finset (GBranch G.tree → ℕ)) (h𝓗 : 𝓗 ⊆ 𝓖),
      (linkOf G.molecule 2 T x y 𝓗
        (false, 0, Cb ^ vmOfG G.molecule T x y * (Cb ^ (𝔇 + 1)) ^ (g + 1))).Ok 𝔇 K := by
  obtain ⟨C₂, hC₂, ht⟩ := hFirst 2 (by norm_num)
  have hK0 : (0 : ℝ) ≤ Kmain := by positivity
  refine ⟨C₂ + 9 + Kmain, by linarith, ?_⟩
  intro γ _ w G 𝔇 K 𝓖 h𝓖 T x y hV g hg 𝓗 h𝓗
  have hγ : γ ≤ 1 / 2 := Fact.out
  set Cb := C₂ + 9 + Kmain with hCb
  have hCb1 : 1 ≤ Cb := by linarith
  have hdrawn : ∀ X, G.molecule.IsVine X T x y → X.IsBad = true →
      (linkOf G.molecule 2 T x y 𝓗
        (false, 0, Cb ^ vmOfG G.molecule T x y * (Cb ^ (𝔇 + 1)) ^ (g + 1))).Ok 𝔇 K := by
    intro X hX hb
    have hd : ∃ X, G.molecule.IsVine X T x y := ⟨X, hX⟩
    rw [vmOfG_drawn hd]
    refine linkOf_ok_bad_mono _ _ _ _ _ ?_ (ClassCount.link_ok_bad G 𝔇 K 𝓖 h𝓖 T x y hd g
      (fun f hf => by rw [← vineIncoh_drawn γ G f hX hb]; exact hg f hf) 𝓗 h𝓗)
    have h9 : (9 : ℝ) ≤ Cb := by linarith
    have hKC : Kmain ≤ Cb := by linarith
    have hKC' : Kmain ^ 𝔇 ≤ Cb ^ (𝔇 + 1) :=
      (pow_le_pow_left₀ hK0 hKC 𝔇).trans (pow_le_pow_right₀ hCb1 (Nat.le_succ 𝔇))
    gcongr
  rcases (Src.isSomeVine_low_iff hγ).mp hV with hX | hX | hT
  · exact hdrawn _ hX rfl
  · exact hdrawn _ hX rfl
  · have hcard := vmOfG_tvine hT
    have hxT : x ∈ T := hT.1.2.1
    have hyT : y ∈ T := hT.1.2.2.1
    refine ⟨fun s t => msum_nonneg G.molecule (by norm_num) T x y 𝓗 s t, fun h => absurd h (by simp [linkOf]),
      fun h => absurd h (by simp [linkOf]), fun _ => ?_⟩
    simp only [linkOf]
    refine (sum_msum_le G.molecule (by norm_num) T hxT hyT 𝔇 𝓗).trans ?_
    obtain ⟨𝓕, h𝓕𝓗, hdist, himg⟩ := exists_transversal T 𝓗
    have hs : ∑ r ∈ 𝓗.image (restr T), bw G.molecule 2 T r = ∑ f ∈ 𝓕, bw G.molecule 2 T f := by
      rw [← himg]; exact (sum_bw_eq_image G.molecule 2 T hdist).symm
    rw [hs]
    have hgT : ∀ f ∈ 𝓕, tvineIncoherency G.molecule T x y f = g := fun f hf => by
      rw [← vineIncoh_tvine γ G f hT]; exact hg f (h𝓗 (h𝓕𝓗 hf))
    have hbound : ∑ f ∈ 𝓕, bw G.molecule 2 T f ≤
        C₂ ^ vmOfG G.molecule T x y * (C₂ ^ (𝔇 + 1)) ^ (g + 1) := by
      rcases 𝓕.eq_empty_or_nonempty with h0 | ⟨f0, hf0⟩
      · rw [h0, Finset.sum_empty]; positivity
      · have hgm : g ≤ vmOfG G.molecule T x y + 1 := by
          rw [← hgT f0 hf0]; exact tvineIncoherency_le hT hcard f0
        have := ht G T x y hT (vmOfG G.molecule T x y) hcard 𝔇 (C₂ ^ (𝔇 + 1)) le_rfl g hgm 𝓕
          (fun f hf => h𝓖 f (h𝓗 (h𝓕𝓗 hf))) hdist
        rwa [Finset.filter_true_of_mem hgT] at this
    refine hbound.trans ?_
    have hC2C : C₂ ≤ Cb := by have : (0 : ℝ) ≤ Kmain := hK0; linarith
    gcongr

end WaveTurbulence.GammaLow.Famc.ClassCount
