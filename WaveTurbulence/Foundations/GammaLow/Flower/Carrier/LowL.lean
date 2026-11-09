/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.FinalCount.GateL

/-! # FLOWER-LOW (packet L8), item E (γL boundary): the marked count over the fixed low family

For every `γ ≤ 1/2` the family `𝒱_γ` is the enlarged family (`Src.isSomeVine_low_iff`, ruling D11), so L6 writes the
ported stage-2 run once, at `Src.γL = 1/2` (PLAN-L6 §3c–§3d, `GateL.lean`). This module gives the marked analogue, so
that PLAN-L8 item H2 can be written over the same fixed carrier:
* `SurvivorDataG.recast`: survivors recast between two parameters of the low range (objects recast, `m` and `prot`
  unchanged), and the transport of `Structural`, `SurvChainOrderG`, `SubproSupportMKG`, `SecondCollectionOKMKG`,
  `AdmissibleMKG`, `splicedCountingAdmissibleMKG` and `numCriticalSGMKG` (with L6's `CountingChoices.recast`);
* **`FinalCountAtMKLAt P`**: `FinalCountAtMKG P` with counting choices `Src.CountingChoices Src.γL` and survivors
  `SurvivorDataG Src.γL`;
* **`finalCountAtMKG_of_L`**, **`finalCountGateLowMK_of_L`**: the `γL` form gives `FinalCountAtMKG P` for
  `P.γ ≤ 1/2`, and `FinalCountGateLowMK` (item H2's target becomes `WTPrefix fun P => P.γ ≤ 1/2 → FinalCountAtMKLAt P`).
The proofs follow L6's `Src/LowCounting.lean` and `GateL.lean`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale)

namespace WaveTurbulence.GammaLow.Flower
open WaveTurbulence.GammaLow.FinalCount

variable {w d : ℕ} {γ γ' : ℝ} (hγ : γ ≤ 1 / 2) (hγ' : γ' ≤ 1 / 2)

section recast
variable {G : Garden w}

/-- Recast of survivor data within the low range (objects recast; `m`, `prot` unchanged). -/
def SurvivorDataG.recast (S : SurvivorDataG γ G) : SurvivorDataG γ' G :=
  ⟨S.m, fun i => (S.surv i).recast hγ hγ', S.prot⟩

@[simp] theorem SurvivorDataG.recast_m (S : SurvivorDataG γ G) : (S.recast hγ hγ').m = S.m := rfl

@[simp] theorem SurvivorDataG.recast_prot (S : SurvivorDataG γ G) : (S.recast hγ hγ').prot = S.prot := rfl

@[simp] theorem SurvivorDataG.recast_surv (S : SurvivorDataG γ G) (i : Fin S.m) :
    (S.recast hγ hγ').surv i = (S.surv i).recast hγ hγ' := rfl

@[simp] theorem SurvivorDataG.joints_recast (S : SurvivorDataG γ G) : (S.recast hγ hγ').joints = S.joints := rfl

theorem objVineG_recast {M : Molecule (GBranch G.tree) (GardenDart G)} (U : Src.Object γ M) :
    ObjVineG M (U.recast hγ hγ') ↔ ObjVineG M U := by
  obtain ⟨A, a, b, sh⟩ := U
  cases sh with
  | vc h =>
    show Src.IsSomeVine γ' _ A a b ↔ Src.IsSomeVine γ _ A a b
    rw [Src.isSomeVine_low_iff hγ', Src.isSomeVine_low_iff hγ]
  | hyper R =>
    show Src.IsSomeVine γ' (Molecule.eraseBond M R.added) A a b ↔
      Src.IsSomeVine γ (Molecule.eraseBond M R.added) A a b
    rw [Src.isSomeVine_low_iff hγ', Src.isSomeVine_low_iff hγ]

theorem structural_recast {C : Src.SubproChoices γ G} {S : SurvivorDataG γ G} (h : S.Structural C) :
    (S.recast hγ hγ').Structural (C.recast hγ hγ') :=
  ⟨fun i => (objVineG_recast hγ hγ' _).mpr (h.1 i), h.2.1, h.2.2.1, h.2.2.2⟩

theorem survChainOrderG_recast {S : SurvivorDataG γ G} (h : SurvChainOrderG S) :
    SurvChainOrderG (S.recast hγ hγ') := h

@[simp] theorem survFirstJointG_recast (S : SurvivorDataG γ G) (i : Fin S.m) (v : GBranch G.tree) :
    SurvFirstJointG (S.recast hγ hγ') i v ↔ SurvFirstJointG S i v := Iff.rfl

theorem forbiddenMKG_recast (C : Src.SubproChoices γ G) (S : SurvivorDataG γ G) :
    forbiddenMKG (C.recast hγ hγ') (S.recast hγ hγ') = forbiddenMKG C S := rfl

theorem subproSupportMKG_recast {L g η : ℝ} {base : Mom d} {kFix : Finset (Mom d)}
    {κ : GardenDart G → (Fin d → ℤ)} {C : Src.SubproChoices γ G} {S : SurvivorDataG γ G}
    (h : SubproSupportMKG G C S L g η base kFix κ) :
    SubproSupportMKG G (C.recast hγ hγ') (S.recast hγ hγ') L g η base kFix κ where
  selectedSG := fun i => (Src.Object.recast_hasGapKind hγ hγ' _ _ _ _ _ _ _).mpr (h.selectedSG i)
  survivorSG := fun i => (Src.Object.recast_hasGapKind hγ hγ' _ _ _ _ _ _ _).mpr (h.survivorSG i)
  zeroTame := h.zeroTame
  contained := fun P hP hO hS hD => by
    have hP' : (P.recast hγ' hγ).HasGapKind L g η base κ .SG :=
      (Src.Object.recast_hasGapKind hγ' hγ _ _ _ _ _ _ _).mpr hP
    rcases h.contained (P.recast hγ' hγ) hP' (fun i hi => hO i hi) (fun i hi => hS i hi) hD with
      ⟨S', a, b, hS', h1, h2, h3, h4⟩ | ⟨Q, h1, h2, h3, h4, h5⟩
    · exact Or.inl ⟨S', a, b, Src.isDV_recast hγ hγ' hS', h1, h2, h3, h4⟩
    · exact Or.inr ⟨Q.recast hγ hγ', h1, by simpa using h2, h3, h4, h5⟩
  hingeSG := h.hingeSG
  hingeJoint := fun v hv i hi => by
    obtain ⟨x, y, h1, h2, h3, h4⟩ := h.hingeJoint v hv i hi
    exact ⟨x, y, h1, h2, (Src.Object.recast_containsDart hγ hγ' _ x).mpr h3,
      (Src.Object.recast_containsDart hγ hγ' _ y).mpr h4⟩
  jointPair := fun i v hv => by
    obtain ⟨x, y, h1, h2, h3, h4⟩ := h.jointPair i v hv
    exact ⟨x, y, h1, h2, (Src.Object.recast_containsDart hγ hγ' _ x).mpr h3,
      (Src.Object.recast_containsDart hγ hγ' _ y).mpr h4⟩
  crossing := fun P hP hO hS hD hH => by
    have hP' : (P.recast hγ' hγ).HasGapKind L g η base κ .SG :=
      (Src.Object.recast_hasGapKind hγ' hγ _ _ _ _ _ _ _).mpr hP
    obtain ⟨v, hv, hvP, hc⟩ := h.crossing (P.recast hγ' hγ) hP' (fun i hi => hO i hi) (fun i hi => hS i hi) hD hH
    refine ⟨v, hv, hvP, ?_⟩
    rcases hc with hc | ⟨hj, x, y, h1, h2, h3⟩
    · exact Or.inl hc
    · refine Or.inr ⟨hj, x, y, h1, h2, ?_⟩
      show Xor (P.ContainsDart x) (P.ContainsDart y)
      rwa [Src.Object.recast_containsDart, Src.Object.recast_containsDart] at h3
  meetB := fun P hP hB => by
    have hP' : (P.recast hγ' hγ).HasGapKind L g η base κ .SG :=
      (Src.Object.recast_hasGapKind hγ' hγ _ _ _ _ _ _ _).mpr hP
    rcases h.meetB (P.recast hγ' hγ) hP' hB with ⟨i, hi⟩ | ⟨i, x, h1, h2⟩ | ⟨v, hv, hvP, hc⟩
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr (Or.inl ⟨i, x, (Src.Object.recast_containsDart hγ' hγ _ x).mp h1,
        (Src.Object.recast_containsDart hγ hγ' _ x).mpr h2⟩)
    · refine Or.inr (Or.inr ⟨v, hv, hvP, ?_⟩)
      rcases hc with hc | ⟨hj, x, y, h1, h2, h3⟩
      · exact Or.inl hc
      · refine Or.inr ⟨hj, x, y, h1, h2, ?_⟩
        show Xor (P.ContainsDart x) (P.ContainsDart y)
        rwa [Src.Object.recast_containsDart, Src.Object.recast_containsDart] at h3

end recast

section transfer
variable {R : ℕ} {G : Garden (2 * R)}

theorem criticalSGMKG_recast (C : Src.CountingChoices γ G d) (S : SurvivorDataG γ G) (v : GBranch G.tree) :
    CriticalSGMKG (C.recast hγ hγ') (S.recast hγ hγ') v ↔ CriticalSGMKG C S v := by
  unfold CriticalSGMKG
  exact and_congr (C.criticalSG_recast hγ hγ' v) Iff.rfl

theorem numCriticalSGMKG_recast (C : Src.CountingChoices γ G d) (S : SurvivorDataG γ G) :
    numCriticalSGMKG (C.recast hγ hγ') (S.recast hγ hγ') = numCriticalSGMKG C S := by
  unfold numCriticalSGMKG
  congr 1
  exact Finset.filter_congr fun v _ => criticalSGMKG_recast hγ hγ' C S v

theorem admissibleMKG_recast {L g η : ℝ} {base : Mom d} {κ : GardenDart G → (Fin d → ℤ)}
    {C : Src.CountingChoices γ G d} {S : SurvivorDataG γ G} (h : AdmissibleMKG C S L g η base κ) :
    AdmissibleMKG (C.recast hγ hγ') (S.recast hγ hγ') L g η base κ := by
  obtain ⟨h1, ⟨rk, hrk, K, hK, hsec⟩, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨subproSupportMKG_recast hγ hγ' h1, ⟨rk, hrk, Src.Object.recast hγ hγ' '' K, ?_, ?_⟩, h3, h4, h5, fun i v hv => ?_, fun i v hv => ?_,
    fun P hP v hv => ?_, fun v hv => h9 v ((criticalSGMKG_recast hγ hγ' C S v).mp hv), h10⟩
  · rw [show forbiddenMKG (C.recast hγ hγ').subpro (S.recast hγ hγ') = forbiddenMKG C.subpro S from rfl]
    exact Src.isSourceSecondCollection_recast hγ hγ' hK
  · change Src.Object.recast hγ hγ' '' C.secondCollection = _
    rw [hsec, Src.canonicalSub_recast]
  · obtain ⟨x, y, e1, e2, e3, e4⟩ := h6 i v hv
    exact ⟨x, y, e1, e2, (Src.Object.recast_containsDart hγ hγ' _ x).mpr e3,
      (Src.Object.recast_containsDart hγ hγ' _ y).mpr e4⟩
  · obtain ⟨x, y, e1, e2, e3, e4⟩ := h7 i v hv
    exact ⟨x, y, e1, e2, (Src.Object.recast_containsDart hγ hγ' _ x).mpr e3,
      (Src.Object.recast_containsDart hγ hγ' _ y).mpr e4⟩
  · obtain ⟨Q, hQ, rfl⟩ := hP
    obtain ⟨x, y, e1, e2, e3, e4⟩ := h8 Q hQ v hv
    exact ⟨x, y, e1, e2, (Src.Object.recast_containsDart hγ hγ' _ x).mpr e3,
      (Src.Object.recast_containsDart hγ hγ' _ y).mpr e4⟩

theorem splicedCountingAdmissibleMKG_recast {D : SplicedKernelData G d} {C : Src.CountingChoices γ G d}
    {S : SurvivorDataG γ G} {L g η : ℝ} {base : Mom d} {roots : Fin (2 * R) → (Fin d → ℤ)}
    {κ : GardenDart G → (Fin d → ℤ)} (h : splicedCountingAdmissibleMKG G D C S L g η base roots κ) :
    splicedCountingAdmissibleMKG G D (C.recast hγ hγ') (S.recast hγ hγ') L g η base roots κ :=
  ⟨h.1, admissibleMKG_recast hγ hγ' h.2⟩

end transfer

/-! ## The marked count over the fixed low family -/

/-- **`FinalCountAtMKLAt`**: `FinalCountAtMKG` over the fixed low carrier (`Src.CountingChoices Src.γL`,
`SurvivorDataG Src.γL`), the carrier of the ported marked run (PLAN-L8 item H2). -/
abbrev FinalCountAtMKLAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelData G P.d) (C : Src.CountingChoices Src.γL G P.d) (S : SurvivorDataG Src.γL G),
    D.hinges = C.subpro.hinges → Src.CountingGeometry G C → S.Structural C.subpro → SurvChainOrderG S →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ Adm : (GardenDart G → (Fin P.d → ℤ)) → Prop,
    (∀ κ, Adm κ → splicedCountingAdmissibleMKG G D C S P.L P.γ P.η base roots κ) →
    G.molecule.countA P.L P.γ P.δ P.C₁ base Adm C.ladderScale ≤
      ENNReal.ofReal
        (P.L ^ (2 * (S.m : ℝ)) * P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + numCriticalSGMKG C S)) *
          P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40)))

/-- The marked count at `γ ≤ 1/2` from its `γL` form (recast the choices and the survivors). -/
theorem finalCountAtMKG_of_L {P : WTParams} (hγP : P.γ ≤ 1 / 2) (h : FinalCountAtMKLAt P) : FinalCountAtMKG P := by
  intro p hp R hR hRm G hpl hirr hbal hn hnm D C S hD hg hS hord base roots Adm hA
  have := h p hp R hR hRm G hpl hirr hbal hn hnm D (C.recast hγP Src.γL_le) (S.recast hγP Src.γL_le) hD
    (Src.countingGeometry_recast hγP Src.γL_le hg) (structural_recast hγP Src.γL_le hS)
    (survChainOrderG_recast hγP Src.γL_le hord) base roots Adm
    (fun κ hκ => splicedCountingAdmissibleMKG_recast hγP Src.γL_le (hA κ hκ))
  rwa [Src.CountingChoices.recast_ladderScale, numCriticalSGMKG_recast, SurvivorDataG.recast_m] at this

/-- **`FinalCountGateLowMK` from the `γL` form** (item H2's target over the fixed carrier). -/
theorem finalCountGateLowMK_of_L (h : WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountAtMKLAt P) : FinalCountGateLowMK := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL hγ' => finalCountAtMKG_of_L hγ' (H L hL hγ')⟩

end WaveTurbulence.GammaLow.Flower
