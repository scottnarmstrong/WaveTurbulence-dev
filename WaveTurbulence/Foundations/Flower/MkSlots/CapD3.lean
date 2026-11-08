/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.Statement
public import WaveTurbulence.Foundations.Flower.ProtWhole.RegBound
public import WaveTurbulence.Foundations.Flower.MkSlots.CapSup

/-! # B3s MK-SLOTS (cap slots): D3's `term` bound for the paired tree of a cap couple, as a superposition

For a cap couple (D6b's `CapG`) whose paired tree `T1` is a protected object (`ProtShape`, `ProtAmbient`), D3's
`ProtBoundNTAt` at `cfg = term`, `θ = η`, `q' = p` bounds the `X^{η,30d,0}` norm of the `term`-pinned protected kernel
on `timeBoxGt p p` (`capTerm_xnorm`). The kernel sees neither its lone-port time (the lone parent, the capped flower
parent, is pinned) nor its pins through the upper clock, and it is continuous in the upper clock (D6b's
`continuous_kernelProt_up`), so `capSup_of_xnorm` turns the bound into a superposition on the whole window
(`capTerm_sup`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ENNReal
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtWhole

namespace WaveTurbulence.Flower.MkSlots

variable {LG : LayeredGarden 2} {j0 c : Fin 2} {X : RegChain} {ζ : ℤˣ}

theorem xnormRestr_anti_out {r d : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ) (B : Set (Fin r → ℝ)) {K K' : Set (Mom d)}
    (hK : K ⊆ K') (F : (Fin r → ℝ) → Mom d → ℂ) : XNormRestr θ Λ₁ Λ₂ B K F ≤ XNormRestr θ Λ₁ Λ₂ B K' F := by
  unfold XNormRestr
  exact iInf_mono fun G => iInf_mono' fun hG => ⟨fun t ht k hk => hG t ht k (hK hk), le_rfl⟩

/-- The `term`-pinned protected kernel of the paired tree at upper clock `x`. -/
def capTermKer (L γ δ : ℝ) {d : ℕ} (D : CapG LG j0 c X ζ) (H1 : LeafProfiles 1 d)
    (m : (GNode D.T1.garden.tree → Mom d) → ℂ) (s t : ℝ) (k₀ : Mom d) (x : ℝ) : ℂ :=
  kernelProt L γ δ D.T1 H1 m (fun _ => x) 0 (ProtCfg.term.fix X s t x) k₀ (fun _ => 0) 0

theorem capTermKer_port (L γ δ : ℝ) {d : ℕ} (D : CapG LG j0 c X ζ) (H1 : LeafProfiles 1 d)
    (m : (GNode D.T1.garden.tree → Mom d) → ℂ) (s t : ℝ) (k₀ : Mom d) (ts : Fin 2 → ℝ) :
    kernelProt L γ δ D.T1 H1 m (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s t (ts 0)) k₀ (fun _ => 0) 0 =
      capTermKer L γ δ D H1 m s t k₀ (ts 0) :=
  kernelProt_port _ _ _ _ _ _ _ _ _ _ _ _ _ (D.lonePin .term (Or.inl rfl) s t (ts 0))

theorem continuous_capTermKer (L γ δ : ℝ) {d : ℕ} (D : CapG LG j0 c X ζ) (H1 : LeafProfiles 1 d)
    (m : (GNode D.T1.garden.tree → Mom d) → ℂ) (Cm : ℝ) (hm : ∀ K, ‖m K‖ ≤ Cm) (s t : ℝ) (k₀ : Mom d)
    (hH : ∀ ℓ ∈ inputLeaves D.T1.garden, Summable fun n : Fin d → ℤ => |H1 ℓ.1 (k₀ + latticePoint L n)|) :
    Continuous (capTermKer L γ δ D H1 m s t k₀) := by
  have he : capTermKer L γ δ D H1 m s t k₀ =
      fun x => kernelProt L γ δ D.T1 H1 m (fun _ => x) 0 (ProtCfg.term.fix X s t 0) k₀ (fun _ => 0) 0 := by
    funext x
    unfold capTermKer
    rw [fix_up_indep .term (by simp) X s t x 0]
  rw [he]
  exact continuous_kernelProt_up L γ δ D.T1 H1 m Cm hm 0 _ k₀
    (PL234.card_lone_le_of_decodesTree (Reg.decodedTree_decodes X ζ)) hH

/-- **D3 at `term`** on the triangle `timeBoxGt p p`, at one momentum. -/
theorem capTerm_xnorm {P : WTParams} (hD3 : ProtPin.ProtBoundNTAt P) (D : CapG LG j0 c X ζ) {p n : ℕ}
    (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hshape : ProtShape p X D.T1) (hsz : protSize X D.T1 = 2 * n)
    (hne : X.lonePath ≠ []) (hamb : ProtAmbient p X D.T1) {s t : ℝ} (hps : (p : ℝ) < s) (hst : s < t)
    (htp : t < p + 1) (S : Finset (GNode D.T1.garden.tree)) (ω : GNode D.T1.garden.tree → IncTop.Star P.d → ℂ)
    (cω : GNode D.T1.garden.tree → ℝ) (hpres : ∀ a ∈ S, IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (ind : (GNode D.T1.garden.tree → Mom P.d) → ℝ) (hind : TermChildIndicator X ind)
    (H1 : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hLC : LeafwiseControlled D.T1 H1 B)
    (k₀ : Mom P.d) :
    XNormRestr P.η (30 * P.d) 0 (timeBoxGt p p) {k₀}
      (fun ts k => kernelProt P.L P.γ P.δ D.T1 H1 (fun κ => IncTop.starWeight S ω κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (31 * (P.d : ℝ) + 6)) *
        regBound P n (protIncoh X D.T1) * ENNReal.ofReal (leafSizeProduct D.T1 B) := by
  have key := hD3 p hp n hn 1 D.T1 X hshape hsz .term hne hamb (Or.inr rfl) P.η (31 * P.d + 6)
    (Or.inl ⟨rfl, rfl⟩) s t hps hst htp p le_rfl S ω cω hpres ∅ (fun _ => P.L) (by simp) ∅ (fun _ => P.L)
    (by simp) ind hind (fun h => by rcases h with h | h | h <;> exact absurd h (by simp)) H1 B hLC k₀ k₀
  have hk : ({k₀} : Set (Mom P.d)) ⊆ latticeBall P.L k₀ k₀ := by
    intro k hk
    rw [Set.mem_singleton_iff.1 hk]
    exact ⟨by simp, 0, by simp [WaveTurbulence.Links.latticePoint_zero]⟩
  refine (xnormRestr_anti_out _ _ _ _ hk _).trans (le_of_eq_of_le ?_ key)
  congr 1
  funext ts k
  congr 1
  funext κ
  simp [filtWeight_empty]

/-- **The superposition of the `term`-pinned kernel on the window** `[p, p + 1]`, from D3. -/
theorem capTerm_sup {P : WTParams} (hD3 : ProtPin.ProtBoundNTAt P) {C : ℝ≥0∞} (hC : CapSupProp P.d P.η C)
    (hη : 0 ≤ P.η) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (D : CapG LG j0 c X ζ) {p n : ℕ}
    (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hshape : ProtShape p X D.T1) (hsz : protSize X D.T1 = 2 * n)
    (hne : X.lonePath ≠ []) (hamb : ProtAmbient p X D.T1) {s t : ℝ} (hps : (p : ℝ) < s) (hst : s < t)
    (htp : t < p + 1) (S : Finset (GNode D.T1.garden.tree)) (ω : GNode D.T1.garden.tree → IncTop.Star P.d → ℂ)
    (cω : GNode D.T1.garden.tree → ℝ) (hpres : ∀ a ∈ S, IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (ind : (GNode D.T1.garden.tree → Mom P.d) → ℝ) (hind : TermChildIndicator X ind)
    (Cm : ℝ) (hm : ∀ K, ‖IncTop.starWeight S ω K * (ind K : ℂ)‖ ≤ Cm)
    (H1 : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hLC : LeafwiseControlled D.T1 H1 B)
    (k₀ : Mom P.d) :
    ∃ (w : (Fin 2 → ℤ) → ℝ) (u : (Fin 2 → ℤ) → ℂ), (∀ m, 0 ≤ w m) ∧ Summable w ∧ (∀ m, ‖u m‖ ≤ 1) ∧
      (∀ x ∈ Icc (p : ℝ) (p + 1), HasSum (fun m => (w m : ℂ) * u m * fsPhase m ![x, p])
        (capTermKer P.L P.γ P.δ D H1 (fun κ => IncTop.starWeight S ω κ * (ind κ : ℂ)) s t k₀ x)) ∧
      ∑' m, maxBracketPow P.η (half m) * ENNReal.ofReal (w m) ≤
        C * (2 * ((∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (31 * (P.d : ℝ) + 6)) *
          regBound P n (protIncoh X D.T1) * ENNReal.ofReal (leafSizeProduct D.T1 B))) := by
  have hH : ∀ ℓ ∈ inputLeaves D.T1.garden, Summable fun n : Fin P.d → ℤ => |H1 ℓ.1 (k₀ + latticePoint P.L n)| :=
    hLC.summable_coset hd hL k₀
  refine capSup_of_xnorm hη hC p _ (continuous_capTermKer P.L P.γ P.δ D H1 _ Cm hm s t k₀ hH)
    (fun ts k => kernelProt P.L P.γ P.δ D.T1 H1 (fun κ => IncTop.starWeight S ω κ * (ind κ : ℂ))
      (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s t (ts 0)) k (fun _ => 0) 0) k₀
    (fun ts => capTermKer_port P.L P.γ P.δ D H1 _ s t k₀ ts) _ ?_
    (capTerm_xnorm hD3 D hp hn hshape hsz hne hamb hps hst htp S ω cω hpres ind hind H1 B hLC k₀)
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top) ?_)
    ENNReal.ofReal_ne_top
  · exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  · unfold regBound; exact ENNReal.ofReal_ne_top

end WaveTurbulence.Flower.MkSlots
