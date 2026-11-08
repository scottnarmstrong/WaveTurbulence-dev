/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.CplDefs

/-! # RT-GATE (ii): `RtOne` by shape (FROZEN for the workers)

`RtOneOn θ c' Ct Cnd`: `RtOne` restricted to the traced couples with `Cnd Q LGc j`. Shapes of a couple with one
branching pinned root `j` (`triv` is impossible):
* `rtT1`: type 1 (any partner layer);
* `rtT2a`: type 2, `j = 0`, nonempty `+` chain (D3's (a+)); `rtT2am`: `j = 1`, nonempty `−` chain ((a−), conjugate);
* `rtT2m`: type 2, `j = 1`, empty `−` chain, `Qlp` of type 1 (D3's (c−)); `rtT2p`: `j = 0`, empty `+` chain ((c+)).
`rtOne_of_on`: the assembly from the shapes covering the selector `True`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- `RtOne` on the traced couples with `Cnd Q LGc j`. -/
def RtOneOn (θ c' Ct : ℝ) (Cnd : RegCpl → LayeredGarden 2 → Fin 2 → Prop) : Prop :=
  ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) (_hFC : TcFC P)
    (_hC11 : 1 ≤ P.C₁) (_hθc : PieceLoss P θ c')
    {p : ℕ} (_hp : p < P.D) {nr : ℕ} (_hn : nr ≤ P.N (p + 1) ^ 4) (Q : RegCpl) (LGc : LayeredGarden 2)
    (_hwf : Q.wf = true) (_hsz : Q.size = 2 * nr) (_hdec : Q.Decodes LGc.garden) (_hle : ∀ a, LGc.layer a ≤ p)
    (j : Fin 2) (_hC : Cnd Q LGc j) {q' : ℕ} (_hq' : q' ≤ p)
    (_hamb : MkSlotsO.CplAmbient p (rtWin p q' j 0) (rtWin p q' j 1) Q LGc)
    (_hj : layerAt LGc (j, []) = p) (_hjb : ([] : TTree.Path) ∈ (LGc.garden.tree j).branching)
    (_hr : layerAt LGc (t1sw j, []) ≤ q') {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1)
    (Hc : LeafProfiles 2 P.d) (Bc : (Fin 2 × TTree.Path) → NNReal) (_hHc : LeafwiseControlled LGc Hc Bc)
    (S : Finset (GNode LGc.garden.tree)) (ω : GNode LGc.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LGc.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LGc.garden.tree)) (M : GBranch LGc.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LGc.garden.tree)) (Mu : GBranch LGc.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (k : Mom P.d),
    rn θ (win (q' : ℝ)) (fun y => kernelProt P.L P.γ P.δ LGc Hc
        (gateM S ω F M Fu Mu) (fun b => if b.1.1 = j then s else y 0) 0 (trFix j s) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (Ct * (P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
        (P.C₁ ^ 3 * rb P (nr - 1) (LGc.incoherency Q.links)) * leafSizeProduct LGc Bc * starCost S cω)))) *
          tcWt P.L k

def rtT1 (Q : RegCpl) (_LGc : LayeredGarden 2) (_j : Fin 2) : Prop := ∃ c Q₁ Q₂ Q₃, Q = RegCpl.type1 c Q₁ Q₂ Q₃

def rtT2a (Q : RegCpl) (_LGc : LayeredGarden 2) (j : Fin 2) : Prop :=
  j = 0 ∧ ∃ (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest Xm : RegChain) (Qlp : RegCpl),
    Q = RegCpl.type2 (RegChain.pair m Qr Qg inner rest) Xm Qlp

def rtT2am (Q : RegCpl) (_LGc : LayeredGarden 2) (j : Fin 2) : Prop :=
  j = 1 ∧ ∃ (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (Qlp : RegCpl),
    Q = RegCpl.type2 Xp (RegChain.pair m Qr Qg inner rest) Qlp

def rtT2m (Q : RegCpl) (_LGc : LayeredGarden 2) (j : Fin 2) : Prop :=
  j = 1 ∧ ∃ (Xp : RegChain) (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl), Q = RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)

def rtT2p (Q : RegCpl) (_LGc : LayeredGarden 2) (j : Fin 2) : Prop :=
  j = 0 ∧ ∃ (Xm : RegChain) (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl), Q = RegCpl.type2 .nil Xm (.type1 c Q₁ Q₂ Q₃)

theorem rtOneOn_true {θ c' Ct : ℝ} (h : RtOneOn θ c' Ct (fun _ _ _ => True)) : RtOne θ c' Ct := by
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle j q' hq' hamb hj hjb hr s hps hsp
    Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k
  exact h K hFC hC11 hθc hp hn Q LGc hwf hsz hdec hle j trivial hq' hamb hj hjb hr hps hsp Hc Bc hHc S ω cω hpres
    F M hM Fu Mu hMu k

theorem rtOneOn_mono {θ c' Ct Ct' : ℝ} {Cnd : RegCpl → LayeredGarden 2 → Fin 2 → Prop} (hle : Ct ≤ Ct')
    (h : RtOneOn θ c' Ct Cnd) : RtOneOn θ c' Ct' Cnd := by
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle' j hC q' hq' hamb hj hjb hr s hps hsp
    Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k
  refine (h K hFC hC11 hθc hp hn Q LGc hwf hsz hdec hle' j hC hq' hamb hj hjb hr hps hsp Hc Bc hHc S ω cω hpres
    F M hM Fu Mu hMu k).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle ?_)) le_rfl)
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := by linarith
  have := rb_nonneg hC1 K.hδ hL0 (nr - 1) (LGc.incoherency Q.links)
  have := starCost_nonneg' S cω
  have : 0 ≤ leafSizeProduct LGc Bc := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have := Real.rpow_nonneg hL0 (4 * c')
  have : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 := sq_nonneg _
  positivity

end WaveTurbulence.Flower.ProtRT
