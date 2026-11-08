/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.PcSup
public import WaveTurbulence.Foundations.Flower.MkSlotsO.PcMass

/-! # PROT-CHAIN (`Pc`): one slot family of a stem chain slot

* `pcC0`: the centre of the consumed lattice ball (the root label on a root chain slot, the node centre `latPt x`
  otherwise); `pc_mem_ball`: every consumed momentum lies in `latticeBall L 0 (pcC0 …)`;
* **`pc_genBox`**: the general slot box of a stem chain slot lies in the closed triangle `pcBoxC p (p + 1) q'`
  (`q'` the layer of the core of `β`); on a skeleton root the upper clock is the top time `t` (the pinned clock values
  are `s` or `t`; a pinned core is pinned at `s` and lies in layer `p`);
* **`pc_fam1`**: a continuous slot function agreeing with the general slot kernel, bounded in `X^{η,30d,0}` on the
  triangle `pcBox lo (p + 1) q'` over the consumed ball, is a `SlotFam1` family. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsI

namespace WaveTurbulence.Flower.MkSlotsO

/-- The centre of the consumed lattice ball of a chain slot. -/
def pcC0 {d R : ℕ} (L : ℝ) (a : PrescribedPrimeGarden (2 * R)) (roots : Fin (2 * R) → (Fin d → ℤ))
    (β : GBranch a.prime.skeleton.tree) (x : Fin d → ℤ) : Mom d :=
  if β.1.2 = [] then latticePoint L (roots β.1.1) else RepAnalytic.latPt d x

theorem pc_mem_ball {d R : ℕ} (L : ℝ) (a : PrescribedPrimeGarden (2 * R)) (roots : Fin (2 * R) → (Fin d → ℤ))
    (β : GBranch a.prime.skeleton.tree) (x : Fin d → ℤ) (n : Fin d → ℤ)
    (h2 : ∀ β' : GBranch a.prime.skeleton.tree, (.inr β : ReplacementSlot a.prime.skeleton) = .inr β' →
      β'.1.2 = [] → n = roots β'.1.1)
    (h3 : ∀ β' : GBranch a.prime.skeleton.tree, (.inr β : ReplacementSlot a.prime.skeleton) = .inr β' →
      β'.1.2 ≠ [] → ‖latticePoint L n - RepAnalytic.latPt d x‖ ≤ 1) :
    latticePoint L n ∈ ProtDefs.latticeBall L 0 (pcC0 L a roots β x) := by
  refine ⟨?_, n, by simp⟩
  unfold pcC0
  by_cases hr : β.1.2 = []
  · simp only [hr, ↓reduceIte]
    rw [h2 β rfl hr, sub_self, norm_zero]
    exact zero_le_one
  · simp only [hr, ↓reduceIte]
    exact h3 β rfl hr

/-- **The general slot box of a stem chain slot.** -/
theorem pc_genBox {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
    (pat : Fin (2 * R) → FixPat) (t s : ℝ) (hG : CapGeo (recLG a) J p) (hpat : CapPatValid (recLG a) J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf (recLG a).garden.tree, IsCapFlower (recLG a) J ℓ ∧ ℓ.1.1 = j)
    (ht : t ∈ Ioo (p : ℝ) (p + 1)) (hs : s ∈ Ioo (p : ℝ) t) (β : GBranch a.prime.skeleton.tree)
    (hne : a.prime.data.tree β ≠ .nil)
    (hcs : OnCapStem (recLG a) J (a.prime.data.coreBranch a.prime.prime.1 β).toNode)
    (ts : Fin 2 → ℝ) (hts : ts ∈ genBoxAt p a J pat t s (.inr β)) :
    ts ∈ pcBoxC p (p + 1) (sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 β).toNode) ∧
      (β.1.2 = [] → ts 0 = t) := by
  set D := a.prime.data
  set hS := a.prime.prime.1
  set fixC := fixCore D hS (fixCap (recLG a) J pat t s) with hfixC
  obtain ⟨hpin, hfree⟩ := hts
  have hc0 := pc_clk0 D hS (sourceLayer a) (sourceLayer_isLayering a) β J hG hcs
  have hv : ∀ (src : ClkSrc a.prime.skeleton) (v : ℝ), clkPin (fun _ => t) fixC src = some v → v = s ∨ v = t := by
    intro src v h
    cases src with
    | inl j =>
      simp only [clkPin, Option.some.injEq] at h
      exact Or.inr h.symm
    | inr b =>
      have h' : fixCap (recLG a) J pat t s (D.coreBranch hS b) = some v := h
      rcases MkSlotsB.fixCap_cases h' with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨i, -, -, -, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
  have hv1 : ∀ v, clkPin (fun _ => t) fixC (argSrc hS (.inr β) 1) = some v →
      v = s ∧ sourceLayer a (D.coreBranch hS β).toNode = p := by
    intro v h
    have h' : fixCap (recLG a) J pat t s (D.coreBranch hS β) = some v := h
    refine ⟨?_, MkSlotsB.fixCap_layer hG hpat hroot h'⟩
    rcases MkSlotsB.fixCap_cases h' with ⟨-, rfl⟩ | ⟨-, -, h0, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨i, -, -, -, rfl⟩
    · rfl
    · exfalso
      have e : (D.coreBranch hS β).1.2 = (pcu D β).2 ++ (D.tree β).lonePath := rfl
      rw [e, List.append_eq_nil_iff] at h0
      exact lonePath_ne_nil hne h0.2
    · rfl
    · rfl
  have hroot0 : β.1.2 = [] → clkPin (fun _ => t) fixC (argSrc hS (.inr β) 0) = some t := by
    intro hr
    have e : argSrc hS (.inr β) 0 = .inl β.1.1 := by
      show clkOfNode a.prime.skeleton β.toNode = _
      unfold clkOfNode nodeToSlot
      have hr' : (β.toNode).1.2 = [] := hr
      simp only [hr', ↓reduceDIte]
      rfl
    rw [e]
    rfl
  have hst : s < t := hs.2
  refine ⟨?_, fun hr => hpin 0 t (hroot0 hr)⟩
  by_cases hfr : ∃ i : Fin 2, clkPin (fun _ => t) fixC (argSrc hS (.inr β) i) = none
  · obtain ⟨⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩⟩, h01⟩ := hfree hfr
    have e0 : (clkLayer p (fun b => sourceLayer a (D.coreBranch hS b).toNode) (argSrc hS (.inr β) 0) : ℝ) = p := by
      rw [hc0]
    rw [e0] at h0a h0b
    exact ⟨h0a, h0b, h1a, h1b, h01.le⟩
  · simp only [not_exists] at hfr
    obtain ⟨v0, hv0⟩ := Option.ne_none_iff_exists'.1 (hfr 0)
    obtain ⟨v1, hv1'⟩ := Option.ne_none_iff_exists'.1 (hfr 1)
    have e0 := hpin 0 v0 hv0
    have e1 := hpin 1 v1 hv1'
    obtain ⟨rfl, hl⟩ := hv1 v1 hv1'
    have hl' : (sourceLayer a (D.coreBranch hS β).toNode : ℝ) = p := by rw [hl]
    rw [pcBoxC, Set.mem_ofPred_eq, e0, e1, hl']
    rcases hv _ v0 hv0 with rfl | rfl
    · exact ⟨hs.1.le, by linarith [ht.2], hs.1.le, by linarith [ht.2], le_rfl⟩
    · exact ⟨ht.1.le, ht.2.le, hs.1.le, by linarith [ht.2], hst.le⟩

/-- **One slot family of a stem chain slot**, from a continuous slot function bounded on a triangle. -/
theorem pc_fam1 (P : WTParams) (hη : 0 ≤ P.η) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ) (σ kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (Rf : Fin (2 * R) → Option ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (β : GBranch a.prime.skeleton.tree) (x : Fin P.d → ℤ)
    (lo q' : ℝ) (hq : q' ≤ lo) (hp : (p : ℝ) ≤ lo) (hlo : lo < p + 1)
    (F : (Fin 2 → ℝ) → Mom P.d → ℂ) (hF : ∀ k, Continuous fun ts => F ts k)
    (hker : ∀ ts k, genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inr β) ts k = F ts k)
    (hbox : ∀ ts ∈ genBoxAt p a J pat t s (.inr β), ts ∈ pcBoxC lo (p + 1) q')
    (M : ℝ) (hM : 0 < M)
    (hX : XNormRestr P.η (30 * P.d) 0 (pcBox lo (p + 1) q') (ProtDefs.latticeBall P.L 0 (pcC0 P.L a roots β x)) F ≤
      ENNReal.ofReal M)
    (μ : ℝ≥0∞) (hμ : ENNReal.ofReal ((capCsup P.d P.η).toReal * (2 * M)) ≤ μ) :
    SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag (.inr β) x P.η μ := by
  have hh : (p : ℝ) + 1 ≤ lo + 1 := by linarith
  obtain ⟨w, am, hw0, hws, hu, hS, hsum, hmass⟩ := pc_sup (capCsup_spec P.d hη) (capCsup_ne_top _ _) ![(p : ℝ), q']
    (pcBox lo (p + 1) q') (pcBox_sub_cell hp le_rfl) (pcBox_sub_closure_interior hq hlo hh)
    (ProtDefs.latticeBall P.L 0 (pcC0 P.L a roots β x)) F hF M hM hX
  refine ⟨Fin 2 → ℤ, inferInstance, w, id, fun _ => 0, am, hw0, hws, hu, hS,
    fun q hq => (Sum.inr_ne_inl hq).elim, fun ts hts n _ h2 h3 => ?_, hmass.trans hμ⟩
  rw [hker]
  exact hsum ts (pcBoxC_sub_closure hq hlo hh (hbox ts hts)) _ (pc_mem_ball P.L a roots β x n h2 h3)

end WaveTurbulence.Flower.MkSlotsO
