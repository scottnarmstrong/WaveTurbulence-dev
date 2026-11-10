/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain38
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase2d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3ConclN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Dart
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3FinalCopy
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3MapDec5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunE
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3URun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3UStep
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Vine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain30
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain8
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowIface3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAdm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCoords
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCDict
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCFlow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCGain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCInj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCLadProd
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCScale
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCSource
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain38`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, session 6 (12): the `r = 1` LowFree lemma and `hZ_ofL`** (R79 NOTES §4, referee F1).
At `r = 1` with no tame atom, a degree-`2` `ε`-atom would have all other contributions `0`, hence balanced darts, hence an opposite pair
`(x, y)` with LG (nonzero) gap, which is a D3 pair (`D3Data`) that `NoD3` and `Desig` (a degree-2 hinge has its unique pair designated)
exclude; a degree-`1` `ε`-atom has contribution `3 > 2`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem lowFree_r1 {M₀ : Molecule V D₀} {C : CollData M₀} {hf : HSt V D₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    (hL : 0 < L) (hg : Good 1 hf.s) (hbal : BalS hf.s)
    (hND : ∀ (v : V) (x₁ x₂ : hf.s.D), D3Data hf v x₁ x₂ →
      pgap L w κ (hf.s.pr x₁ x₂) = 0 ∨ ¬ Desig C (hf.anc v) (hf.s.pr x₁ x₂))
    (hLG : ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → ∀ x y : hf.s.D, hf.s.M.atom x = a → hf.s.M.atom y = a →
      hf.s.M.out x = false → hf.s.M.out y = true → y ≠ hf.s.M.mate x →
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .LG)
    (hDes : ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → hf.s.M.deg a = 2 → ∀ x y : hf.s.D, hf.s.M.atom x = a →
      hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true → y ≠ hf.s.M.mate x →
      Desig C (hf.anc a) (hf.s.pr x y)) :
    ∀ e ∈ hf.s.M.atoms, hf.s.cls e = .eps → 3 ≤ hf.s.M.deg e := by
  intro e he hε
  by_contra hlt
  push Not at hlt
  have hsum := hg.sum_contrib
  have hnn := fun a (ha : a ∈ hf.s.M.atoms) => Good.contrib_nonneg hg ha
  have hce : contrib hf.s e = 4 - hf.s.M.deg e := by unfold contrib; rw [hε]; simp [Cls.base]
  have hd1 := hg.1.eps e he hε
  have hsplit := Finset.add_sum_erase hf.s.M.atoms (contrib hf.s) he
  have hrest : 0 ≤ ∑ a ∈ hf.s.M.atoms.erase e, contrib hf.s a :=
    Finset.sum_nonneg fun a ha => hnn a (Finset.mem_of_mem_erase ha)
  have hd2 : hf.s.M.deg e = 2 := by
    by_contra hne
    have : hf.s.M.deg e = 1 := by omega
    omega
  have hrest0 : ∑ a ∈ hf.s.M.atoms.erase e, contrib hf.s a = 0 := by omega
  have hz : ∀ a ∈ hf.s.M.atoms.erase e, contrib hf.s a = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun a ha => hnn a (Finset.mem_of_mem_erase ha)).1 hrest0
  have hbd : ∀ a ∈ hf.s.M.atoms.erase e, hf.s.M.outdeg a = hf.s.M.indeg a := by
    intro a ha
    have haM := Finset.mem_of_mem_erase ha
    have h0 := hz a ha
    have hb := hg.1.bounds a haM
    have hdeq := deg_eq hf.s.M a
    unfold contrib at h0
    by_cases hεa : hf.s.cls a = .eps
    · rw [hεa] at h0; simp only [Cls.base] at h0; omega
    · have hab := hg.1.ab a haM hεa
      have hba := hbal.2 a haM hεa
      by_cases hgh : hf.s.cls a = .ghost
      · have := hab.2.1 hgh; omega
      · have hbase : (hf.s.cls a).base = 2 := by
          rcases hc : hf.s.cls a with _ | ⟨ρ, kp⟩ | _ | _
          · exact absurd hc hεa
          · simp [Cls.base]
          · simp [Cls.base]
          · exact absurd hc hgh
        have h2 : hf.s.M.deg a = 2 := by omega
        have := hba h2
        omega
  have hs := sum_outdeg_eq_sum_indeg hf.s.M
  have hsE : ∑ a ∈ hf.s.M.atoms.erase e, hf.s.M.outdeg a = ∑ a ∈ hf.s.M.atoms.erase e, hf.s.M.indeg a :=
    Finset.sum_congr rfl hbd
  have hs1 := Finset.add_sum_erase hf.s.M.atoms (fun a => hf.s.M.outdeg a) he
  have hs2 := Finset.add_sum_erase hf.s.M.atoms (fun a => hf.s.M.indeg a) he
  beta_reduce at hs1 hs2
  have hoi : hf.s.M.outdeg e = hf.s.M.indeg e := by omega
  have hdeq := deg_eq hf.s.M e
  have ho1 : hf.s.M.outdeg e = 1 := by omega
  have hi1 : hf.s.M.indeg e = 1 := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.1 (by unfold Molecule.indeg at hi1; omega : 0 < ((hf.s.M.dartsAt e).filter fun x => hf.s.M.out x = false).card)
  obtain ⟨y, hy⟩ := Finset.card_pos.1 (by unfold Molecule.outdeg at ho1; omega : 0 < ((hf.s.M.dartsAt e).filter fun x => hf.s.M.out x = true).card)
  obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
  obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
  have hxa : hf.s.M.atom x = e := by simpa [Molecule.dartsAt] using hx1
  have hya : hf.s.M.atom y = e := by simpa [Molecule.dartsAt] using hy1
  have hxo : hf.s.M.out x = false := hx2
  have hne : y ≠ hf.s.M.mate x := by
    intro h
    exact hg.1.noloop x (by rw [← h, hxa, hya])
  have hD : D3Data hf e x y := ⟨he, hε, hd2, hxa, hya, hne, hxo, hy2⟩
  have hlg := hLG e he hε x y hxa hya hxo hy2 hne
  have hdes := hDes e he hε hd2 x y hxa hya hxo hy2 hne
  rcases hND e x y hD with h0 | h0
  · have hn := lt_norm_of_LG hlg
    have hp : 0 < L ^ (-γ + η) := Real.rpow_pos_of_pos hL _
    have : Molecule.gapAt L w (κ ∘ hf.s.down) x y = 0 := h0
    rw [this, norm_zero] at hn
    linarith
  · exact h0 hdes

end WaveTurbulence.GammaLow.FinalCount.H
