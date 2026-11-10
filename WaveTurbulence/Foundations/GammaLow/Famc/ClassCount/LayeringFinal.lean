/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.ClassCount.LayeringFinal` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Stage1.Shared.CarriesW
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.KeyedBound
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Assembly
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitListCount
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.LayeringFinal
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.SurvMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceSurvMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.ChainFam2
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.ChainFam3
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.ClassBound
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Classes
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Lab
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.RootDef
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.SkeletonCode
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.SkeletonLeg
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Slots
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Slots2
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Slots3
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.SpliceLayer
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCL
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitChain2
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode4
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode5
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode6
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitFamily
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitLinks
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitSum
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.WeightSum
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit


/-!
# CLASSCOUNT: `LayeringLeg` (TARGET L2248-L2252)

The layered gardens decoded by `D` over `S` and carrying a Stage 1 piece of data `(g, r)` are counted by splitting
into the `≤ 2^n` classes of effective prescriptions (`Fama.unitBlocks γ S σ`), then by key (`keyed_bound`); the constants are
absorbed using `K^(P.D+1) ≤ P.C₂`.
-/

@[expose] public section
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LayerCnt WaveTurbulence.Vine WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine
variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs] [Fact LayervineTVineImproved] [Fact LayervineTVineFirst]

theorem final_numerics {K0 : ℝ} {Kn : ℕ} (hK0 : 2 ≤ K0) (hKn : K0 ≤ Kn) {p g r N : ℕ} (hN : 1 ≤ N) {C2 cardA : ℝ}
    (hC2 : (K0 ^ (p + 1)) ^ 25 ≤ C2)
    (hcard : cardA ≤ 2 ^ N * ((2 : ℝ) ^ (2 * g + 1 + N + N + r) *
      (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g)))) :
    cardA ≤ (((2 ^ 5 * Kn ^ 4 : ℕ)) : ℝ) ^ N * C2 ^ (g + r) := by
  have hK1 : 1 ≤ K0 := by linarith
  have hK00 : 0 ≤ K0 := by linarith
  set X : ℝ := K0 ^ (p + 1) with hX
  have hX2 : 2 ≤ X := by
    calc (2 : ℝ) ≤ K0 := hK0
      _ ≤ K0 ^ (p + 1) := by
        calc K0 = K0 ^ 1 := (pow_one _).symm
          _ ≤ K0 ^ (p + 1) := pow_le_pow_right₀ hK1 (by omega)
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have h2pow : (2 : ℝ) ^ (2 * g + r) ≤ X ^ (2 * g + r) := pow_le_pow_left₀ (by norm_num) hX2 _
  have hK4 : K0 ^ (4 * N) ≤ ((Kn : ℝ) ^ 4) ^ N := by
    rw [← pow_mul]; exact pow_le_pow_left₀ hK00 hKn _ 
  have h2 : (2 : ℝ) ^ (4 * N + 1) ≤ (2 ^ 5) ^ N := by
    rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hXC : X ^ (25 * (g + r)) ≤ C2 ^ (g + r) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hC2 _
  have hC2nn : 0 ≤ C2 := le_trans (by positivity) hC2
  calc cardA ≤ 2 ^ N * ((2 : ℝ) ^ (2 * g + 1 + N + N + r) * (2 ^ N * K0 ^ (4 * N) * X ^ (24 * r + 15 * g))) := hcard
    _ = (2 : ℝ) ^ (4 * N + 1) * (2 : ℝ) ^ (2 * g + r) * K0 ^ (4 * N) * X ^ (24 * r + 15 * g) := by
        rw [show (2 * g + 1 + N + N + r) = (2 * g + r) + (N + N + 1) by ring, pow_add (2 : ℝ) (2 * g + r)]
        rw [show (4 * N + 1) = N + ((N + N + 1) + N) by ring, pow_add, pow_add]
        ring
    _ ≤ (2 ^ 5) ^ N * X ^ (2 * g + r) * ((Kn : ℝ) ^ 4) ^ N * X ^ (24 * r + 15 * g) := by
        gcongr
    _ = ((2 ^ 5 : ℝ) * (Kn : ℝ) ^ 4) ^ N * X ^ (25 * r + 17 * g) := by
        rw [mul_pow, show 25 * r + 17 * g = (2 * g + r) + (24 * r + 15 * g) by ring, pow_add]
        ring
    _ ≤ ((2 ^ 5 : ℝ) * (Kn : ℝ) ^ 4) ^ N * X ^ (25 * (g + r)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (by omega)) (by positivity)
    _ ≤ ((2 ^ 5 : ℝ) * (Kn : ℝ) ^ 4) ^ N * C2 ^ (g + r) :=
        mul_le_mul_of_nonneg_left hXC (by positivity)
    _ = _ := by push_cast; ring

open Classical in
/-- **Leg 2 over `𝒱_γ`** (main `layeringLeg`, TARGET L2248-L2252). -/
theorem layeringLegG : LayeringLegG := by
  obtain ⟨K0, hK0, hKB⟩ := keyed_bound
  set Kn : ℕ := ⌈K0⌉₊ with hKn_def
  have hKn : K0 ≤ (Kn : ℝ) := Nat.le_ceil K0
  have hKn2 : (2 : ℝ) ≤ Kn := le_trans hK0 hKn
  have hKn1 : 1 ≤ Kn := by exact_mod_cast (by linarith : (1 : ℝ) ≤ Kn)
  refine ⟨2 ^ 5 * Kn ^ 4, Kn ^ 25, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (by positivity)
  intro P hγ hK p hp R hR N hN g r S D A' hSpl hord hA'
  have : Fact (P.γ ≤ 1 / 2) := ⟨hγ⟩
  have hK' : ((Kn ^ 25 : ℕ) : ℝ) ^ (P.D + 1) ≤ P.C₂ := by exact_mod_cast hK
  have hC2nn : 0 ≤ P.C₂ := le_trans (by positivity) hK'
  by_cases hAe : A' = ∅
  · subst hAe
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨LG1, hLG1⟩ := Finset.nonempty_iff_ne_empty.2 hAe
  have hex : ∀ LG ∈ A', ∃ σ : Prescription S, ∃ hd : D.Decodes hSpl LG.garden,
      rbarOfG P.γ S σ = r ∧ (Fama.stage1PieceOf P.γ P.d hSpl LG hd σ).gbar = g := by
    intro LG hLG
    obtain ⟨-, hS', hd, σ, hr, hg⟩ := hA' LG hLG
    exact ⟨σ, hd, hr, hg⟩
  haveI : Nonempty (Prescription S) := ⟨(hex LG1 hLG1).choose⟩
  choose! σf hdf hrf hgf using hex
  have hcan : ∀ LG ∈ A', IsCanonGC (p + 1) LG := fun LG h => (hA' LG h).1.1
  have hsize : D.size ≤ N := by
    have h1 := decodeSizeLeg S D hSpl LG1.garden (hdf LG1 hLG1)
    have h2 : LG1.garden.order = N := (hA' LG1 hLG1).1.2.2.1
    omega
  have hn : Fintype.card (GBranch S.tree) ≤ N := by
    rw [Mole.card_gbranch]; exact hord
  set X : ℝ := K0 ^ (p + 1) with hX
  have hXC : X ^ 25 ≤ P.C₂ := by
    have hK1 : 1 ≤ K0 := by linarith
    calc X ^ 25 = (K0 ^ 25) ^ (p + 1) := by rw [hX, ← pow_mul, ← pow_mul, mul_comm]
      _ ≤ ((Kn : ℝ) ^ 25) ^ (p + 1) :=
          pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by linarith) hKn _) _
      _ ≤ ((Kn : ℝ) ^ 25) ^ (P.D + 1) :=
          pow_le_pow_right₀ (one_le_pow₀ (by exact_mod_cast hKn1)) (by omega)
      _ = ((Kn ^ 25 : ℕ) : ℝ) ^ (P.D + 1) := by push_cast; ring
      _ ≤ P.C₂ := hK'
  set cls : LayeredGarden (2 * R) → Finset (Finset (GBranch S.tree)) :=
    fun LG => (Fama.groupsFinset P.γ S).filter (fun T => σf LG T = Molecule.GapKind.SG) with hcls
  have hmaps : ∀ LG ∈ A', cls LG ∈ (Fama.groupsFinset P.γ S).powerset := fun LG _ =>
    Finset.mem_powerset.2 (Finset.filter_subset _ _)
  have hfib : A'.card = ∑ 𝒢 ∈ (Fama.groupsFinset P.γ S).powerset, (A'.filter (fun LG => cls LG = 𝒢)).card :=
    Finset.card_eq_sum_card_fiberwise (fun LG hLG => hmaps LG hLG)
  have hcl : ∀ 𝒢 ∈ (Fama.groupsFinset P.γ S).powerset, ((A'.filter (fun LG => cls LG = 𝒢)).card : ℝ) ≤
      (2 : ℝ) ^ (2 * g + 1 + N + N + r) *
        (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g)) := by
    intro 𝒢 h𝒢
    set Ac := A'.filter (fun LG => cls LG = 𝒢) with hAc
    have hpos0 : 0 ≤ (2 : ℝ) ^ (2 * g + 1 + N + N + r) *
        (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g)) := by positivity
    by_cases hemp : Ac = ∅
    · rw [hemp]; simpa using hpos0
    obtain ⟨LGs, hLGs⟩ := Finset.nonempty_iff_ne_empty.2 hemp
    obtain ⟨hLGsA, hLGsc⟩ := Finset.mem_filter.1 hLGs
    have hAcl : ∀ LG ∈ Ac, IsCanonGC (p + 1) LG ∧ ∃ hd : D.Decodes hSpl LG.garden,
        gbarRHS P.γ D hSpl LG (Fama.stSt P.γ S (σf LGs)) (Set.toFinite (Fama.unitIngredients P.γ S (σf LGs))).toFinset = g := by
      intro LG hLG
      obtain ⟨hLA, hc⟩ := Finset.mem_filter.1 hLG
      have heq : Fama.unitBlocks P.γ S (σf LG) = Fama.unitBlocks P.γ S (σf LGs) :=
        unitBlocks_eq_of_filter_eq S _ _ (hc.trans hLGsc.symm)
      refine ⟨hcan LG hLA, hdf LG hLA, ?_⟩
      rw [← gbar_eq_gbarRHS P.d hSpl LG (hdf LG hLA) (σf LGs)]
      exact (gbar_rbar_eq_of_unitBlocks_eq P.d hSpl LG (hdf LG hLA) (σf LG) (σf LGs) heq).1.symm.trans
        (hgf LG hLA)
    have hr' : (Fama.stSt P.γ S (σf LGs)).G.molecule.rho + (Fama.unitBlocks P.γ S (σf LGs)).length ≤ r :=
      (rho_add_length_le_rbarOf S (σf LGs)).trans (hrf LGs hLGsA).le
    exact hKB P.γ S hSpl D (σf LGs) p g r N Ac hAcl hr' hsize hn
  have hpow : (((Fama.groupsFinset P.γ S).powerset.card : ℕ) : ℝ) ≤ (2 : ℝ) ^ N := by
    rw [Finset.card_powerset]
    have : 2 ^ (Fama.groupsFinset P.γ S).card ≤ 2 ^ N :=
      Nat.pow_le_pow_right (by norm_num) ((card_groupsFinset_le S).trans hn)
    exact_mod_cast this
  have hpos0 : 0 ≤ (2 : ℝ) ^ (2 * g + 1 + N + N + r) *
      (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g)) := by positivity
  have htot : (A'.card : ℝ) ≤ 2 ^ N * ((2 : ℝ) ^ (2 * g + 1 + N + N + r) *
      (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g))) := by
    rw [hfib, Nat.cast_sum]
    calc ∑ 𝒢 ∈ (Fama.groupsFinset P.γ S).powerset, ((A'.filter (fun LG => cls LG = 𝒢)).card : ℝ)
        ≤ ∑ 𝒢 ∈ (Fama.groupsFinset P.γ S).powerset, ((2 : ℝ) ^ (2 * g + 1 + N + N + r) *
          (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g))) := Finset.sum_le_sum hcl
      _ = (((Fama.groupsFinset P.γ S).powerset.card : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * g + 1 + N + N + r) *
          (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow hpos0
  exact final_numerics hK0 hKn hN (hXC) htot

end WaveTurbulence.GammaLow.Famc.ClassCount
