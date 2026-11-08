/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildCore
public import WaveTurbulence.Foundations.Flower.ProtPin.TermStar
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildAux

/-! # D3 PROT-PIN (P7): `termChild` at one output, given the root-trace bound of the traced side couple

`TcTraceU θ Ct`: the uniform bound of the root trace of a side couple (the root of tree `j`, in layer `p` and
branching, pinned at its own clock `s`; the other tree at the clock `u`), in the 1D window norm with its output
weight `tcWt` (summed jointly with the side-couple output, loss-free), at the cost of one more cut
(`c² C₁² rb(n−1, g)`) and a factor `L` (a lost incoherency).
`tc_perk_red`: (P7) at one output when the traced tree belongs to the red side couple. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **The root-trace bound of a side couple** (uniform). -/
def TcTraceU (θ Ct : ℝ) : Prop :=
  ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) (_hθc : PieceLoss P θ 0)
    {p : ℕ} (_hp : p < P.D) {nr : ℕ} (_hn : nr ≤ P.N (p + 1) ^ 4) (Q : RegCpl) (LGc : LayeredGarden 2)
    (_hwf : Q.wf = true) (_hsz : Q.size = 2 * nr) (_hdec : Q.Decodes LGc.garden) (_hle : ∀ a, LGc.layer a ≤ p)
    (_hamb : TcCplAmb p Q LGc) (j : Fin 2) (_hj : layerAt LGc (j, []) = p)
    (_hjb : ([] : TTree.Path) ∈ (LGc.garden.tree j).branching) {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1)
    (Hc : LeafProfiles 2 P.d) (Bc : (Fin 2 × TTree.Path) → NNReal) (_hHc : LeafwiseControlled LGc Hc Bc)
    (S : Finset (GNode LGc.garden.tree)) (ω : GNode LGc.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LGc.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LGc.garden.tree)) (M : GBranch LGc.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LGc.garden.tree)) (Mu : GBranch LGc.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (k : Mom P.d),
    rn θ (win p) (fun y => kernelProt P.L P.γ P.δ LGc Hc
        (gateM S ω F M Fu Mu) (fun b => if b.1.1 = j then s else y 0) 0 (trFix j s) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (Ct * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
        (P.C₁ ^ 2 * rb P (nr - 1) (LGc.incoherency Q.links)) * leafSizeProduct LGc Bc * starCost S cω))) *
          tcWt P.L k

/-- A branching root forces a nontrivial couple: `1 ≤ n`. -/
theorem tc_size_pos {Q : RegCpl} {LGc : LayeredGarden 2} (hwf : Q.wf = true) (hdec : Q.Decodes LGc.garden) {j : Fin 2}
    (hjb : ([] : TTree.Path) ∈ (LGc.garden.tree j).branching) {n : ℕ} (hsz : Q.size = 2 * n) : 1 ≤ n := by
  cases Q with
  | triv =>
    exfalso
    have ht := tree_of_decodes hdec j
    split_ifs at ht <;> rw [ht] at hjb <;> simp [RegCpl.trees, TTree.branching] at hjb
  | type1 c Q₁ Q₂ Q₃ => simp only [RegCpl.size] at hsz; omega
  | type2 Xp Xm Qlp =>
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hwf
    obtain ⟨-, hnil⟩ := hwf
    simp only [RegCpl.size] at hsz
    cases Xp with
    | nil =>
      cases Xm with
      | nil => simp [RegChain.isNil] at hnil
      | pair => simp only [RegChain.size] at hsz; omega
    | pair => simp only [RegChain.size] at hsz; omega

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain}

/-- The traced red root is branching (from the branch of the protected tree at that position). -/
theorem tc_red_root_branch (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg) {j : Fin 2} {i : Fin 3}
    (hj : rBase m inner (LG.garden.sig 0) j = bPath m inner ++ [i])
    (hb : Xp.lonePath ++ (bPath m inner ++ [i]) ∈ (LG.garden.tree 0).branching) :
    ([] : TTree.Path) ∈ (LGr.garden.tree j).branching := by
  have hCLz := PL234.chainEmb_append_right (ChainEmb.of_decodesTree D.dec)
  obtain ⟨hrL, -, -, -⟩ := hCLz.parts
  have htree := tree_of_decodes D.decR j
  set σ := slotSign (LG.garden.sig 0) m.red.1 with hσ
  have hpos : rBase m inner (LG.garden.sig 0) j = (if (j = 0) = (σ = 1) then [m.red.1] else bPath m inner ++ [m.red.2]) :=
    rfl
  have hbot : ¬ ((j = 0) = (σ = 1)) := by
    intro hc
    rw [hpos, if_pos hc] at hj
    have := congrArg List.length hj
    simp [bPath] at this
  have hi : i = m.red.2 := by
    rw [hpos, if_neg hbot] at hj
    have h2 := List.append_cancel_left hj
    simp only [List.cons.injEq, and_true] at h2
    exact h2.symm
  subst hi
  by_cases hs : σ = 1
  · rw [if_pos hs] at hrL
    have hj1 : j = 1 := by
      fin_cases j
      · exact absurd (by simp [hs]) hbot
      · rfl
    subst hj1
    have hmem := hrL.nodeB
    have e := hrL.treeB
    rw [htree, if_neg (by decide)]
    rw [← e, (Links.mem_subtreeAt _ _ hmem []).2.2]
    simpa [addrExt, bPath] using hb
  · rw [if_neg hs] at hrL
    have hj0 : j = 0 := by
      fin_cases j
      · rfl
      · exact absurd (by simp [hs]) hbot
    subst hj0
    have hmem := hrL.nodeA
    have e := hrL.treeA
    rw [htree, if_pos rfl]
    rw [← e, (Links.mem_subtreeAt _ _ hmem []).2.2]
    simpa [addrExt, bPath] using hb

/-- The traced green root is branching (from the branch of the protected tree at that position). -/
theorem tc_green_root_branch (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg) {j : Fin 2} {i : Fin 3}
    (hj : gBase m inner (LG.garden.sig 0) j = bPath m inner ++ [i])
    (hb : Xp.lonePath ++ (bPath m inner ++ [i]) ∈ (LG.garden.tree 0).branching) :
    ([] : TTree.Path) ∈ (LGg.garden.tree j).branching := by
  have hCLz := PL234.chainEmb_append_right (ChainEmb.of_decodesTree D.dec)
  obtain ⟨-, hrL, -, -⟩ := hCLz.parts
  have htree := tree_of_decodes D.decG j
  set σ := slotSign (LG.garden.sig 0) m.green.1 with hσ
  have hpos : gBase m inner (LG.garden.sig 0) j = (if (j = 0) = (σ = 1) then [m.green.1] else bPath m inner ++ [m.green.2]) :=
    rfl
  have hbot : ¬ ((j = 0) = (σ = 1)) := by
    intro hc
    rw [hpos, if_pos hc] at hj
    have := congrArg List.length hj
    simp [bPath] at this
  have hi : i = m.green.2 := by
    rw [hpos, if_neg hbot] at hj
    have h2 := List.append_cancel_left hj
    simp only [List.cons.injEq, and_true] at h2
    exact h2.symm
  subst hi
  by_cases hs : σ = 1
  · rw [if_pos hs] at hrL
    have hj1 : j = 1 := by
      fin_cases j
      · exact absurd (by simp [hs]) hbot
      · rfl
    subst hj1
    have hmem := hrL.nodeB
    have e := hrL.treeB
    rw [htree, if_neg (by decide)]
    rw [← e, (Links.mem_subtreeAt _ _ hmem []).2.2]
    simpa [addrExt, bPath] using hb
  · rw [if_neg hs] at hrL
    have hj0 : j = 0 := by
      fin_cases j
      · rfl
      · exact absurd (by simp [hs]) hbot
    subst hj0
    have hmem := hrL.nodeA
    have e := hrL.treeA
    rw [htree, if_pos rfl]
    rw [← e, (Links.mem_subtreeAt _ _ hmem []).2.2]
    simpa [addrExt, bPath] using hb

end WaveTurbulence.Flower.ProtPin
