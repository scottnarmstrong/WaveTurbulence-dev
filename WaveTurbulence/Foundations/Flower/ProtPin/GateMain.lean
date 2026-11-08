/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.GatePen

/-! # D3 PROT-PIN: the gate `ProtBoundGate` from its slices

`protBoundAt_of`: `ProtBoundAt P` from `none`/`term` (`ProtBoundNTAt`) and one slice `CfgU P.η Cr selRest` covering
every other configuration (all of which carry the weight `θ = η` only); `trace` on an empty chain is `none` (no root
branch). `protBoundGate_of`: the gate, given the slices still proved elsewhere — (P4) with a nonempty prefix, (P7),
and the cap couples — in `CfgU` form; the prefix is that of `protBoundNTGate` with the size conditions of one and two
cuts. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- Every configuration other than `none`/`term`, except `trace` on an empty chain. -/
def selRest : ∀ (w : ℕ), LayeredGarden w → RegChain → ProtCfg → Prop :=
  fun _ _ X cfg => cfg ≠ .none ∧ cfg ≠ .term ∧ ¬ (cfg = .trace ∧ X = .nil)

/-- Weakening of a slice selector along the shape facts. -/
theorem CfgU.weaken {θ Cr : ℝ} {sel sel' : ∀ (w : ℕ), LayeredGarden w → RegChain → ProtCfg → Prop}
    (h : CfgU θ Cr sel)
    (himp : ∀ (p : ℕ) (w : ℕ) (LG : LayeredGarden w) (X : RegChain) (cfg : ProtCfg), ProtShape p X LG →
      cfg.Valid X LG p → sel' w LG X cfg → sel w LG X cfg) : CfgU θ Cr sel' := by
  intro P C₁a C₂a C₁b C₂b K hη CL hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb hsel
  exact h K hη hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb (himp p w LG X cfg hsh hval hsel)

/-- An empty chain has no root branch in tree `0`. -/
theorem no_root_branch_nil {p w : ℕ} {LG : LayeredGarden w} (hsh : ProtShape p .nil LG) :
    ∀ b : GBranch LG.garden.tree, b.1.1.val ≠ 0 ∨ b.1.2 ≠ [] := by
  intro b
  by_cases h0 : b.1.1.val = 0
  · right
    intro h
    have hb := b.2
    match w, LG, hsh, b, h0, hb with
    | 1, LG, hsh, b, h0, hb =>
      have e : b.1.1 = 0 := Fin.ext h0
      rw [e, hsh.2.1.1] at hb
      simp [RegChain.plug, TTree.branching] at hb
    | 2, LG, hsh, b, h0, hb =>
      obtain ⟨LG1, Dc, -, -, -⟩ := cap_pieces hsh
      have e : b.1.1 = 0 := Fin.ext h0
      rw [e, Dc.tree0] at hb
      simp [RegChain.plug, TTree.branching] at hb
  · exact Or.inl h0

theorem trace_fix_nil {p w : ℕ} {LG : LayeredGarden w} (hsh : ProtShape p .nil LG) (s t up : ℝ) :
    (ProtCfg.trace.fix .nil s t up : GBranch LG.garden.tree → Option ℝ) = ProtCfg.none.fix .nil s t up := by
  funext b
  unfold ProtCfg.fix ProtCfg.pins
  rcases no_root_branch_nil hsh b with h | h
  · rw [if_neg h, if_neg h]
  · by_cases h0 : b.1.1.val = 0
    · rw [if_pos h0, if_pos h0]
      obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil h
      simp [List.lookup, hl]
    · rw [if_neg h0, if_neg h0]

/-- **`ProtBoundAt` from `none`/`term` and the rest.** -/
theorem protBoundAt_of {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    (hNT : ProtBoundNTAt P) {Cr CL : ℝ} (hCL : 0 ≤ CL) (hC11 : 1 ≤ P.C₁)
    (hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (F : (Fin r → ℝ) → Mom P.d → ℂ)
      (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr P.η B {k} F ≤ X) →
      XNormRestr P.η (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
    (hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    (hbig2 : twoK CL Cr P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) ≤ P.L ^ (5 : ℝ))
    (hU : CfgU P.η Cr selRest) : ProtBoundAt P := by
  intro p hp n hn w LG X hsh hsz cfg hval hamb θ c hθc s t hps hst htp q' hq' S ω cω hpres F M hM Fu Mu hMu
    ind hind hind1 H B hH b₀ c₀
  by_cases hnt : cfg = .none ∨ cfg = .term
  · exact hNT p hp n hn w LG X hsh hsz cfg hval hamb hnt θ c hθc s t hps hst htp q' hq' S ω cω hpres F M hM Fu Mu
      hMu ind hind hind1 H B hH b₀ c₀
  have hθ : θ = P.η ∧ c = 31 * P.d + 6 := by
    rcases hθc with h | ⟨-, -, h⟩
    · exact h
    · exact absurd h hnt
  obtain ⟨rfl, rfl⟩ := hθ
  by_cases htr : cfg = .trace ∧ X = .nil
  · obtain ⟨rfl, rfl⟩ := htr
    have h1 := hind1 (Or.inr (Or.inr rfl))
    have hfix : ∀ ts : Fin 2 → ℝ, (ProtCfg.trace.fix .nil s t (ts 0) : GBranch LG.garden.tree → Option ℝ) =
        ProtCfg.none.fix .nil s t (ts 0) := fun ts => trace_fix_nil hsh s t (ts 0)
    simp only [hfix]
    exact hNT p hp n hn w LG .nil hsh hsz .none trivial hamb (Or.inl rfl) P.η (31 * P.d + 6) (Or.inl ⟨rfl, rfl⟩)
      s t hps hst htp q' hq' S ω cω hpres F M hM Fu Mu hMu ind hind (fun _ => h1) H B hH b₀ c₀
  · push_neg at hnt
    exact hU K rfl hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb ⟨hnt.1, hnt.2, htr⟩ s t hps hst
      htp q' hq' S ω cω hpres F M hM Fu Mu hMu ind hind hind1 H B hH b₀ c₀

/-- The selectors of the slices proved elsewhere. -/
def selPenPrefix : ∀ (w : ℕ), LayeredGarden w → RegChain → ProtCfg → Prop :=
  fun w _ X cfg => w = 1 ∧ cfg = .penTerm ∧ ¬ selPenNoPrefix X

def selTChild : ∀ (w : ℕ), LayeredGarden w → RegChain → ProtCfg → Prop :=
  fun w _ _ cfg => w = 1 ∧ ∃ i, cfg = .termChild i

def selCap : ∀ (w : ℕ), LayeredGarden w → RegChain → ProtCfg → Prop :=
  fun w _ X cfg => w = 2 ∧ cfg ≠ .none ∧ cfg ≠ .term ∧ ¬ (cfg = .trace ∧ X = .nil)

/-- The slices cover `selRest`. -/
theorem selRest_cover (p w : ℕ) (LG : LayeredGarden w) (X : RegChain) (cfg : ProtCfg) (hsh : ProtShape p X LG)
    (_hval : cfg.Valid X LG p) (hs : selRest w LG X cfg) :
    (((((w = 1 ∧ cfg = .root) ∨ (w = 1 ∧ cfg = .trace ∧ X ≠ .nil)) ∨ (w = 1 ∧ cfg = .rootTerm)) ∨
      (w = 1 ∧ cfg = .penTerm ∧ selPenNoPrefix X)) ∨ selPenPrefix w LG X cfg) ∨ selTChild w LG X cfg ∨
        selCap w LG X cfg := by
  obtain ⟨hn, ht, htr⟩ := hs
  have hw : w = 1 ∨ w = 2 := by
    rcases w with _ | _ | _ | w
    · exact hsh.elim
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact hsh.elim
  rcases hw with rfl | rfl
  · cases cfg with
    | none => exact absurd rfl hn
    | term => exact absurd rfl ht
    | root => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨rfl, rfl⟩))))
    | rootTerm => exact Or.inl (Or.inl (Or.inl (Or.inr ⟨rfl, rfl⟩)))
    | penTerm =>
      by_cases hX : selPenNoPrefix X
      · exact Or.inl (Or.inl (Or.inr ⟨rfl, rfl, hX⟩))
      · exact Or.inl (Or.inr ⟨rfl, rfl, hX⟩)
    | termChild i => exact Or.inr (Or.inl ⟨rfl, i, rfl⟩)
    | trace => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rfl, rfl, fun h => htr ⟨rfl, h⟩⟩))))
  · exact Or.inr (Or.inr ⟨rfl, hn, ht, htr⟩)

end WaveTurbulence.Flower.ProtPin
