/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RTKer
public import WaveTurbulence.Foundations.Flower.MkSlots.CapMain
public import WaveTurbulence.Foundations.Flower.MkSlotsO.Obl

/-! # B3s-HELPER3 (B5(ii)): the root-trace CHAIN slot from `RootTraceGate`

* `rtKc`: the slot constant;
* `sup_of_xnorm_le`: B3s's `superposition_any` from a bound `≤ Bd` (the zero bound included);
* `rtMass_le`: the D-gate mass `C_sup · 2 · c_F^{#front} · L^{47d+5} · regBound · leaf` is at most
  `Kp · genSlotMass` (protected loss `L^{2(47d+5)}`, no selected native vertex);
* `genSlotKer_chain`: on a root-trace chain slot the general slot kernel is the gate's kernel (root pinned at `s`,
  frontier star weights, upper clock `ts 0`, lower clock `ts 1`);
* `genBoxAt_chain_subset`: the general box lies in the gate's box `timeBoxGt p q' ∩ {ts 1 < s ∧ s ≤ ts 0}`;
* **`slotFam1_chain`**: HELPER8's `MkSlotsO.SlotFam1` at `θ = η` for a root-trace chain slot, every centre. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.LGSpine WaveTurbulence.Represents WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
  WaveTurbulence.VineAlign WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.ProtDefs
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.Stage1W WaveTurbulence.VineEstS3.FS
  WaveTurbulence.RepAnalytic

namespace WaveTurbulence.Flower.MkSlotsB

/-! ### The constant -/

/-- **The root-trace chain slot constant.** -/
def rtKc (d : ℕ) (η : ℝ) : ℝ := 1 + 2 * (MkSlots.capCsup d η).toReal

theorem one_le_rtKc (d : ℕ) (η : ℝ) : 1 ≤ rtKc d η := by
  unfold rtKc
  have : 0 ≤ (MkSlots.capCsup d η).toReal := ENNReal.toReal_nonneg
  linarith

theorem two_capCsup_le_rtKc (d : ℕ) (η : ℝ) : 2 * (MkSlots.capCsup d η).toReal ≤ rtKc d η := by
  unfold rtKc; linarith

/-! ### X-norm to superposition -/

/-- **B3s's `superposition_any` from a bound `≤ Bd`** (mass `C · 2 · Bd`; a zero bound gives the empty family). -/
theorem sup_of_xnorm_le {d : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) {Cs : ℝ≥0∞} (hC : MkSlots.CapSupProp d θ Cs)
    (q : Fin 2 → ℝ) (B : Set (Fin 2 → ℝ)) (K : Set (Mom d)) (f : (Fin 2 → ℝ) → Mom d → ℂ) (Bd : ℝ≥0∞)
    (hBd : Bd ≠ ⊤) (hBc : B ⊆ cell q) (hBi : B ⊆ closure (interior B))
    (hfc : ∀ k ∈ K, Continuous fun t => f t k) (hn : XNormRestr θ (30 * d) 0 B K f ≤ Bd) :
    ∃ (Λ : Type) (_ : Countable Λ) (wt : Λ → ℝ) (m : Λ → Fin 2 → ℤ) (amp : Λ → Mom d → ℂ),
      (∀ l, 0 ≤ wt l) ∧ Summable wt ∧ (∀ l, SNorm (30 * d) 0 (amp l) ≤ 1) ∧
      (∀ t ∈ B, ∀ k ∈ K, HasSum (fun l => (wt l : ℂ) * amp l k * fsPhase (m l) t) (f t k)) ∧
      ∑' l, maxBracketPow θ (half (m l)) * ENNReal.ofReal (wt l) ≤ Cs * (2 * Bd) := by
  by_cases hB0 : Bd = 0
  · have hz : ∀ t ∈ B, ∀ k ∈ K, f t k = 0 := by
      intro t ht k hk
      by_contra hne
      have hpos : 0 < ‖f t k‖ₑ := enorm_pos.2 hne
      rw [hB0] at hn
      obtain ⟨-, -, -, -, hlt⟩ := MkSlots.exists_continuous_version hθ hBi
        (fun k hk => (hfc k hk).continuousOn) (lt_of_le_of_lt hn hpos)
      exact lt_irrefl _ (hlt t ht k hk)
    refine ⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim,
      (hasSum_fintype _).summable, fun e => e.elim, fun t ht k hk => by simp [hz t ht k hk], by simp⟩
  · have hlt : XNormRestr θ (30 * d) 0 B K f < 2 * Bd := by
      calc _ ≤ Bd := hn
        _ < Bd + Bd := ENNReal.lt_add_right hBd hB0
        _ = 2 * Bd := (two_mul Bd).symm
    obtain ⟨w, a, hw0, ha, hsum, hws, hmass⟩ :=
      hC q B K f (2 * Bd) (ENNReal.mul_ne_top (by simp) hBd) hBc hBi hfc hlt
    exact ⟨Fin 2 → ℤ, inferInstance, w, id, a, hw0, hws, ha, hsum, hmass⟩

/-! ### The mass -/

/-- **The D-gate mass is at most `Kp · genSlotMass`.** -/
theorem rtMass_le (P : WTParams) (C : ℝ) (hC : P.C₁ ≤ C) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (Cs Kp : ℝ) (hCs : 0 ≤ Cs) (hKp : 2 * Cs ≤ Kp) (ns nr : ℕ)
    (hns : ns ≤ nr) (n g : ℕ) (hn : 1 ≤ n) (LSb : ℝ) (hLSb : 0 ≤ LSb) :
    ENNReal.ofReal Cs * (2 * (ENNReal.ofReal (frontierConst P.d ^ ns) *
        ENNReal.ofReal (P.L ^ (47 * (P.d : ℝ) + 5)) * regBound P n g * ENNReal.ofReal LSb)) ≤
      ENNReal.ofReal (Kp * ((C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) *
        (frontierConst P.d ^ nr * LSb) * P.L ^ MkSlotsI.genLossExp P.d)) := by
  have hcF := one_le_frontierConst P.d
  have hcF0 : 0 ≤ frontierConst P.d := le_trans zero_le_one hcF
  set Lc := P.L ^ (47 * (P.d : ℝ) + 5)
  have hLc : 0 ≤ Lc := Real.rpow_nonneg (by linarith) _
  have hLc1 : 1 ≤ Lc := Real.one_le_rpow hL (by positivity)
  have hLL : Lc ≤ P.L ^ MkSlotsI.genLossExp P.d := by
    refine Real.rpow_le_rpow_of_exponent_le hL ?_
    unfold MkSlotsI.genLossExp
    have : (0 : ℝ) ≤ 47 * (P.d : ℝ) + 5 := by positivity
    linarith
  set R := P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ))
  have hR : 0 ≤ R := by
    have : 0 ≤ P.C₁ := le_trans zero_le_one hC1
    positivity
  have hreg : regBound P n g = ENNReal.ofReal R := rfl
  rw [hreg, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  rw [← ENNReal.ofReal_mul (pow_nonneg hcF0 _), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hCs]
  refine ENNReal.ofReal_le_ofReal ?_
  have hR' := MkSlots.capRegBound_le P C hC hC1 hδ hL hηγ n g hn
  have hpow : frontierConst P.d ^ ns ≤ frontierConst P.d ^ nr := pow_le_pow_right₀ hcF hns
  have hAB : 0 ≤ (C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) := by
    have : 0 ≤ C * Real.sqrt P.δ := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    positivity
  have hK0 : 0 ≤ Kp := le_trans (by positivity) hKp
  calc Cs * (2 * (frontierConst P.d ^ ns * Lc * R * LSb))
      = (2 * Cs) * frontierConst P.d ^ ns * R * LSb * Lc := by ring
    _ ≤ Kp * frontierConst P.d ^ nr * ((C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ))) * LSb *
        P.L ^ MkSlotsI.genLossExp P.d := by
        gcongr
    _ = Kp * ((C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) * (frontierConst P.d ^ nr * LSb) *
        P.L ^ MkSlotsI.genLossExp P.d) := by ring

/-! ### The chain slot -/

section Chain

variable {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
  (t s : ℝ) (γ' : GBranch a.prime.skeleton.tree)

/-- The lone parent of a nontrivial chain tree is not its root. -/
theorem loneParent_ne_root {X : RegChain} {G : Garden 1} (hX : X.DecodesTree G) (h2 : 2 ≤ X.lonePath.length)
    (b : GBranch G.tree) (hb : G.IsLoneParent b) : b.1.2 ≠ [] := by
  obtain ⟨ℓ, hl, hpar⟩ := hb
  have hpl : ℓ.1.2 = X.lonePath := by
    by_contra hne
    unfold Garden.IsLone at hl
    rw [hX.2.1 ℓ, ite_eq_right hne] at hl
    exact absurd hl (by simp)
  obtain ⟨-, i, hi⟩ := hpar
  intro h0
  rw [h0] at hi
  have := congrArg List.length (hpl.symm.trans hi)
  simp at this
  omega

theorem rootPins_loneParent {X : RegChain} {G : Garden 1} (hX : X.DecodesTree G)
    (h2 : 2 ≤ X.lonePath.length) (s : ℝ) (b : GBranch G.tree) (hb : G.IsLoneParent b) :
    MkSlotsO.rootPins (fun _ => True) s b = none := by
  unfold MkSlotsO.rootPins
  split_ifs with h
  · exact absurd h.1 (loneParent_ne_root hX h2 b hb)
  · rfl

variable {a J pat t s γ'}

/-- **The general slot kernel of a root-trace chain slot is the gate's kernel.** -/
theorem genSlotKer_chain (G : RTChain a J pat t s p γ') {d : ℕ} (L γ δ : ℝ) (σ kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (roots : Fin (2 * R) → (Fin d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom d)) (ts : Fin 2 → ℝ) (k : Mom d) :
    MkSlotsI.genSlotKer L γ δ p a J pat t s σ kSel Rs h roots Rf dag (.inr γ') ts k =
      kernelProt L γ δ (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) γ')
        (MkSlots.capProfiles (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) γ')
          (fun z => MkSlots.anchProfiles J (MkSlots.recLG a) h L roots
            (chainContextNode a.prime.data a.prime.prime.1 γ' z).1))
        (fun κ => IncTop.starWeight (frontNat a (chainContextNode a.prime.data a.prime.prime.1 γ') p)
          (fun z y => frontierG (Rf (chainContextNode a.prime.data a.prime.prime.1 γ' z).1.1) (y 0)) κ)
        (fun _ => ts 0) (ts 1) (MkSlotsO.rootPins (fun _ => True) s) k (fun _ => 0) 0 := by
  unfold MkSlotsI.genSlotKer
  dsimp only [slotFnGWFRL]
  have hΘ : MkSlotsI.genΘs a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J L σ kSel Rs
      (.inr γ') k = fun _ => 1 := funext fun κ => G.genΘs_one L σ kSel Rs k κ
  have hfix : MkSlots.fixNative a.prime.data a.prime.prime.1 (fixCap (MkSlots.recLG a) J pat t s) (.inr γ') =
      MkSlotsO.rootPins (fun _ => True) s := funext fun q => G.pins q
  have hm : (fun k' => ∏ z, MkSlots.chainW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      L γ δ p s J Rf dag (chainContextNode a.prime.data a.prime.prime.1 γ' z) (k' z)) =
      fun κ => IncTop.starWeight (frontNat a (chainContextNode a.prime.data a.prime.prime.1 γ') p)
        (fun z y => frontierG (Rf (chainContextNode a.prime.data a.prime.prime.1 γ' z).1.1) (y 0)) κ := by
    funext K'
    rw [Finset.prod_congr rfl fun z _ => G.chainW_eq L γ δ s Rf dag z (K' z)]
    exact prod_fwNode_eq_starWeight (MkSlots.recLG a) p (fun j => frontierG (Rf j))
      (chainContextNode a.prime.data a.prime.prime.1 γ') K'
  rw [hΘ, hfix]
  refine (kernelNodeWR_kDomainR_eq_kernelProt L γ δ _ _ _ _ _ _ k _ _ _
    (fun _ b hb => rootPins_loneParent (Reg.decodedTree_decodes _ _) G.two_le s b hb)).trans ?_
  exact congrArg (fun m' => kernelProt L γ δ _ _ m' (fun _ => ts 0) (ts 1) (MkSlotsO.rootPins (fun _ => True) s) k
    (fun _ => 0) 0) hm

/-- The general box of a root-trace chain slot lies in the gate's box. -/
theorem genBoxAt_chain_subset (G : RTChain a J pat t s p γ') :
    MkSlotsI.genBoxAt p a J pat t s (.inr γ') ⊆
      timeBoxGt (p : ℝ) (sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 γ').toNode : ℝ) ∩
        {ts | ts 1 < s ∧ s ≤ ts 0} := by
  intro ts hts
  obtain ⟨h1, h2⟩ := hts
  have h0 : ts 0 = s := h1 0 s G.clk0
  have harg1 : argSrc a.prime.prime.1 (.inr γ') 1 = .inr γ' := rfl
  have hnone : MkSlotsI.clkPin (fun _ => t) (MkSlots.fixCore a.prime.data a.prime.prime.1
      (fixCap (MkSlots.recLG a) J pat t s)) (argSrc a.prime.prime.1 (.inr γ') 1) = none := by
    rw [harg1]
    exact G.free
  have hsb := h2 ⟨1, hnone⟩
  have hsb' : ts ∈ timeBoxGt ((clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
      (argSrc a.prime.prime.1 (.inr γ') 0) : ℕ) : ℝ)
      ((clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        (argSrc a.prime.prime.1 (.inr γ') 1) : ℕ) : ℝ) := hsb
  rw [G.clkLayer0, harg1] at hsb'
  refine ⟨hsb', ?_, h0.ge⟩
  show ts 1 < s
  rw [← h0]
  exact hsb'.2

end Chain

/-! ### The chain slot family -/

theorem two_le_size_of_lonePath {X : RegChain} (h : X.lonePath ≠ []) : 2 ≤ X.size := by
  cases hX : X with
  | nil => rw [hX] at h; exact absurd rfl h
  | pair m Qr Qg inner rest => simp [RegChain.size]

section ChainFam

variable {R p : ℕ} {a : PrescribedPrimeGarden (2 * R)} {J : Finset (Fin (2 * R))} {pat : Fin (2 * R) → FixPat}
  {t s : ℝ} {γ' : GBranch a.prime.skeleton.tree}

/-- **The root-trace chain slot family** (`θ = η`, HELPER8's `SlotFam1`), at every centre `x`, from RT (i). -/
theorem slotFam1_chain {P : WTParams} (hRT : MkSlotsO.RootTraceBoundAt P) (hd : 1 ≤ P.d) (hη : 0 ≤ P.η)
    (hL : 1 ≤ P.L) (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ)
    (C : ℝ) (hC : P.C₁ ≤ C) (hp : p < P.D) (hsz : a.prime.data.size ≤ P.N (p + 1) ^ 4) (hps : (p : ℝ) < s)
    (hsp : s < p + 1) (hlay : ∀ z, (MkSlots.recLG a).layer z ≤ p) (G : RTChain a J pat t s p γ')
    (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (b : ℝ) (hb1 : 1 ≤ b)
    (hb : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (Rf : Fin (2 * R) → Option ℝ) (hRf1 : ∀ j r, Rf j = some r → 1 ≤ r)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (x : Fin P.d → ℤ) :
    MkSlotsO.SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag (.inr γ') x P.η
      (ENNReal.ofReal (rtKc P.d P.η * MkSlotsI.genSlotMass P C b a J pat t s kSel Rs (.inr γ'))) := by
  set LGc := nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) γ'
    with hLGc
  set X := a.prime.data.tree γ' with hXdef
  set e := chainContextNode a.prime.data a.prime.prime.1 γ' with he
  set S := frontNat a e p with hS
  set ω : GNode LGc.garden.tree → IncTop.Star P.d → ℂ := fun z y => frontierG (Rf (e z).1.1) (y 0) with hω
  set H := MkSlots.capProfiles LGc (fun z => MkSlots.anchProfiles J (MkSlots.recLG a) h P.L roots (e z).1)
    with hH
  set B' := nativeChainB a.prime.data a.prime.prime.1 (fun _ => b.toNNReal) γ' with hB'
  set q' := sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 γ').toNode with hq'def
  have hdec : X.DecodesTree LGc.garden := Reg.decodedTree_decodes _ _
  have hXne : X.lonePath ≠ [] := fun h0 => by have := G.two_le; rw [h0] at this; simp at this
  set n := X.size / 2 with hndef
  have hXs : X.size = 2 * n := by
    obtain ⟨r, hr⟩ := chain_size_even X
    omega
  have hXD : X.size ≤ a.prime.data.size := Represents.slotSize_le a.prime.data (.inr γ')
  have hn : n ≤ P.N (p + 1) ^ 4 := by omega
  have hn1 : 1 ≤ n := by have := two_le_size_of_lonePath hXne; omega
  have hq' : q' ≤ p := hlay _
  have hpres : ∀ z ∈ S, IncTop.StarPresented (30 * P.d) (ω z) (frontierConst P.d) :=
    fun z _ => starPresented_front Rf hRf1 (fun z => (e z).1.1) z
  have hLC : LeafwiseControlled LGc H B' := G.leafwise h P.L roots b (by linarith) hb
  have hgate := (hRT p hp n hn s hps hsp).1 X LGc G.wf hXs hdec hXne G.layer_le G.layer_root q' hq' G.layer_lone
    G.amb S ω (fun _ => frontierConst P.d) hpres H B' hLC 0 (latPt P.d x)
  set Bd : ℝ≥0∞ := (∏ z ∈ S, ENNReal.ofReal ((fun _ => frontierConst P.d) z)) *
    ENNReal.ofReal (P.L ^ (47 * (P.d : ℝ) + 5)) *
    regBound P n (LGc.incoherency (X.treeLinks (LGc.garden.sig 0))) * ENNReal.ofReal (leafSizeProduct LGc B')
    with hBd
  have hBdt : Bd ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top) ?_)
      ENNReal.ofReal_ne_top
    · exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
    · unfold regBound; exact ENNReal.ofReal_ne_top
  have hfc : ∀ k ∈ latticeBall P.L 0 (latPt P.d x), Continuous fun ts : Fin 2 → ℝ =>
      kernelProt P.L P.γ P.δ LGc H (fun κ => IncTop.starWeight S ω κ) (fun _ => ts 0) (ts 1)
        (MkSlotsO.rootPins (fun _ => True) s) k (fun _ => 0) 0 := fun k _ =>
    ProtWhole.continuous_kernelProt_joint P.L P.γ P.δ LGc H _ 1
      (fun κ => norm_starWeight_front_le S Rf (fun z => (e z).1.1) κ) _ k
      (PL234.card_lone_le_of_decodesTree hdec) (hLC.summable_coset hd hL k)
  obtain ⟨Λ, hΛ, wt, m, amp, hw0, hws, hampS, hsum, hmass⟩ := sup_of_xnorm_le hη (MkSlots.capCsup_spec P.d hη)
    (cell2 p q') _ _ _ Bd hBdt (timeBoxGt_cut2_subset_cell p q' s)
    (timeBoxGt_cut2_subset_closure_interior p q' s (by exact_mod_cast hq') hps hsp) hfc hgate
  refine ⟨Λ, hΛ, wt, m, fun _ => 0, amp, hw0, hws,
    fun l k => Represents.snorm_le_one_pointwise _ (amp l) (hampS l) k, hampS,
    fun q hq => absurd hq (by simp), fun ts hts n' _ _ hball => ?_, ?_⟩
  · have hk := hball γ' rfl G.nonroot
    rw [genSlotKer_chain G]
    exact hsum ts (genBoxAt_chain_subset G hts) _ ⟨hk, n', by rw [zero_add]⟩
  · -- the mass
    have hCs := MkSlots.capCsup_ne_top P.d P.η
    have hcF0 : 0 ≤ frontierConst P.d := le_trans zero_le_one (one_le_frontierConst P.d)
    have hLSb : 0 ≤ slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        (fun _ => b.toNNReal) (.inr γ') := by
      unfold slotLeaf leafSizeProduct
      exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hsize : slotSize a.prime.data (.inr γ') = 2 * n := hXs
    unfold MkSlotsI.genSlotMass
    simp only [G.prot kSel, ↓reduceIte, G.selNative_empty kSel, Finset.prod_empty, mul_one]
    rw [hsize]
    refine hmass.trans (le_of_eq_of_le ?_ (rtMass_le P C hC hC1 hδ hL hηγ (MkSlots.capCsup P.d P.η).toReal
      (rtKc P.d P.η) ENNReal.toReal_nonneg (two_capCsup_le_rtKc P.d P.η) S.card
      (slotNr a.prime.data a.prime.prime.1 (.inr γ')) G.front_card n
      (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (.inr γ')) hn1 _ hLSb))
    rw [ENNReal.ofReal_toReal hCs, hBd, Finset.prod_const, ENNReal.ofReal_pow hcF0]
    rfl

end ChainFam

end WaveTurbulence.Flower.MkSlotsB
