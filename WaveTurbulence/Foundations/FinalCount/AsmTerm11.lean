/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm10
public import WaveTurbulence.Foundations.FinalCount.AsmClSharp
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 11: the terminal family chain at a state.**
`QS(hf, A) ≤ ∏_K L^{exponent_K} · ∏_{a ∈ R} 𝔄(component a of M₅)` for the cluster family of the tame `ε`-atoms `T`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem terminal_family [Nonempty V] (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ C₁ δ : ℝ, 1 ≤ C₁ → 0 < δ → δ ≤ 1 →
    ∀ {M₀ : Molecule V D₀} {hf : HSt V D₀} {Tm : V → Prop} {A : Set (D₀ → (Fin d → ℤ))} {P : Finset V → ℝ},
      LadderHered M₀ P → (∀ S, 0 ≤ P S) → LCtx M₀ hf.s →
      (∀ k0 ∈ A, ∀ v ∈ M₀.atoms, Tm v → ∀ x y, M₀.atom x = v → M₀.atom y = v → k0 x = k0 y) →
      (∀ k0 ∈ A, ∀ x, k0 (M₀.mate x) = k0 x) →
      (∀ v ∈ M₀.atoms, Tm v → M₀.deg v < 4 → ∃ k, ∀ k0 ∈ A, ∀ x, M₀.atom x = v → k0 x = k) →
      (∀ x, hf.s.M.atom x ≠ hf.s.M.atom (hf.s.M.mate x)) → (∀ a ∈ hf.s.M.atoms, hf.s.M.deg a ≤ 4) →
      (∀ a ∈ hf.s.M.atoms, 1 ≤ hf.s.M.deg a) →
      ∃ (𝒦 : Finset (Finset V)) (j : Finset V → ℤ) (Rs : Finset V),
        𝒦.biUnion id = tameSet hf Tm ∧ Clusters hf.s.M 𝒦 ∧
        hf.s.M.circuitRank = (eraseSet hf.s.M (tameSet hf Tm)).circuitRank + ∑ K ∈ 𝒦, j K ∧
        CompRep (hf.op5 Tm).s.M Rs ∧
        QS L γ δ C₁ (0 : Mom d) P hf A ≤ (∏ K ∈ 𝒦, ENNReal.ofReal (clusterRHSs L γ η C₀ K.card (eDart hf.s.M K) (j K))) *
          ∏ a ∈ Rs, (compMol (hf.op5 Tm).s.M a).countA L γ δ C₁ (0 : Mom d)
            (projAdm (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm))) P := by
  obtain ⟨L₀, hL₀, hfam⟩ := erase_family_deviation_sharp.{_, u} (V := V) hd hγ0 hγ1 hη hη1 hC0 hC0η 4
  refine ⟨max L₀ (Real.exp 1), le_trans hL₀ (le_max_left _ _), fun L hL C₁ δ hC₁ hδ hδ1 M₀ hf Tm A P hP hP0 hc hTame hmate hfix hnl hm4 hdpos => ?_⟩
  have hL' : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hLe : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
  have hTsub : tameSet hf Tm ⊆ hf.s.M.atoms := fun v hv => (tameSet_mem.1 hv).1
  obtain ⟨𝒦, h1, hD⟩ := exists_famData hf.s.M (tameSet hf Tm) hTsub hnl hm4 (fun a ha => hdpos a (hTsub ha))
  obtain ⟨j, hrk, hdev⟩ := hfam 𝒦 hf.s.M hD
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hX : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (P S) := fun S => by
    have := hP0 S
    unfold Molecule.ladderWeight
    exact le_min (by positivity) (by positivity)
  have hKfacts : ∀ K ∈ 𝒦, (∀ a ∈ K, a ∈ hf.s.M.atoms ∧ hf.s.cls a = .eps ∧ Tm a) ∧ (∀ a ∈ K, 1 ≤ hf.s.M.deg a) ∧
      ∀ a ∈ K, ∀ b ∈ K, (eraseSet hf.s.M (hf.s.M.atoms \ K)).SameComponent a b := by
    intro K hK
    refine ⟨fun a ha => ?_, hD.dpos K hK, hD.int K hK⟩
    have : a ∈ tameSet hf Tm := by rw [← h1]; exact Finset.mem_biUnion.2 ⟨K, hK, ha⟩
    exact tameSet_mem.1 this
  have hFT : FamTame hf.s.M 𝒦 (AdmS (fun k => k ∈ A) hf.s) := famTame_state hc Tm A hTame hmate hfix 𝒦 hKfacts
  have hFL : FamLad L γ δ P 4 hf.s.M 𝒦 := famLad_state hP hc hLe hδ hP0 le_rfl hm4 𝒦
  have hdev' := hdev L hL' C₁ δ hC₁ hδ hδ1 (w := (0 : Mom d)) (AdmS (fun k => k ∈ A) hf.s) P hX hFT hFL
  rw [h1] at hdev' hrk
  obtain ⟨Rs, hR, hbd⟩ := terminal_chain hf.s.M (tameSet hf Tm) L γ δ C₁ (0 : Mom d) hL0 hδ (by linarith)
    (AdmS (fun k => k ∈ A) hf.s) P hX hdev'
  exact ⟨𝒦, j, Rs, h1, hD.cl, hrk, hR, hbd⟩

end WaveTurbulence.FinalCountAsm
