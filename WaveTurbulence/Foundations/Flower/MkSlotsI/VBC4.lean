/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.VBC3

/-! # B3s-HELPER7 (WP10): the centre-indexed relaxed pinned VINE-B♯ with the centred expansion at consumed momenta

The variant of VBC1/VBC3 in which the centred expansion is required only at the CONSUMED slot momenta, exactly as the
non-centred one: `ConsC : CentredSlot Gsb → Mom d → Prop`, `hconsC` (every skeleton decoration consumes its centred
slot momenta in `ConsC`) and `hexpC'` (the expansion of `famC c y` at `x ∈ ConsC c` in the node ball of `y`). The swap
only uses the agreement of the superpositions with the slot kernels at the consumed momenta (`CentreAgree`, VBC1), and
the decoration bound of VBC2 only goes through the swap, so the proofs are those of VBC1–VBC3 via their `_agree` forms.
For the slot obligation (rev 4, coset base `0`) take `Cons`, `ConsC := fun _ x => x ∈ Set.range (latticePoint L)`.

* `famVal_famX_eq_cons`, `centreAgree_of_cons`;
* **`hasSum_modes_centred_cons`**, `summable_modes_centred_cons` (per centre assignment);
* **`hasSum_skelValWZRL_centred_cons`** (main theorem), **`hasSum_sigma_centred_cons`** (joint family). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract

namespace WaveTurbulence.Flower.MkSlotsI
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.RepAnalytic
open WaveTurbulence.Flower.MkSlots (fixMeasure outerValMμD)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW RegBoundW unitKernelMGW)
open WaveTurbulence.Flower.MkSlotsB

variable {w d : ℕ}

section Cons
variable {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb) {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

/-- **The superposition of `famX X` reproduces the outer slot kernel** at every consumed momentum of a decoration of
non-zero weight `chiX X`, with the centred expansion only at the consumed momenta (`hconsC`, `hexpC'`). -/
theorem famVal_famX_eq_cons (hd : Disj blk) (hSb : Gsb.IsPlain) {roots : Fin w → (Fin d → ℤ)}
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ)) (Cons : ReplacementSlot Gsb → Mom d → Prop)
    (hcons : ∀ κ : GenDecoration S d roots 0, ∀ s', ¬ IsCentred s' →
      Cons s' (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb s')))))
    (hexp₀ : ∀ s', ¬ IsCentred s' → ∀ ts ∈ Box s', ∀ x, Cons s' x →
      HasSum (fun l => (fam₀.w s' l : ℂ) * fam₀.a s' l x * fsPhase (fam₀.m s' l) ts) (Fs.fs (Φ.iota hS hSb s') ts x))
    (ConsC : CentredSlot Gsb → Mom d → Prop)
    (hconsC : ∀ κ : GenDecoration S d roots 0, ∀ c : CentredSlot Gsb,
      ConsC c (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb (.inr c.1))))))
    (hexpC' : ∀ (c : CentredSlot Gsb) (y : Fin d → ℤ), ∀ ts ∈ Box (.inr c.1), ∀ x, ConsC c x →
      ‖x - latPt d y‖ ≤ 1 →
      HasSum (fun l => ((famC c y).w l : ℂ) * (famC c y).a l x * fsPhase ((famC c y).m l) ts)
        (Fs.fs (Φ.iota hS hSb (.inr c.1)) ts x))
    (X : CentredSlot Gsb → (Fin d → ℤ)) (κ : GenDecoration S d roots 0)
    (hκ : chiX L base X (Φ.resDec hS hd κ) ≠ 0) (s' : ReplacementSlot Gsb) (ts : Fin 2 → ℝ) (hts : ts ∈ Box s') :
    famVal (famX fam₀ famC X) s' ts (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb s')))) =
      Fs.fs (Φ.iota hS hSb s') ts (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb s')))) := by
  refine (hasSum_famVal _ s' ts _).unique ?_
  by_cases hs : IsCentred s'
  · rcases s' with q | c
    · exact hs.elim
    · have e : κ.1 (slotNode hS (Φ.iota hS hSb (.inr c))) =
          (Φ.resDec hS hd κ).1 (⟨c, hs⟩ : CentredSlot Gsb).1.toNode := by
        show κ.1 (Φ.br c).toNode = κ.1 (Φ.node c.toNode)
        rw [Φ.br_node]
      have hball := norm_sub_le_one_of_chiX_ne_zero hκ ⟨c, hs⟩
      rw [← e] at hball
      exact hasSum_famX_centred fam₀ famC X ⟨c, hs⟩ ts _
        (hexpC' ⟨c, hs⟩ (X ⟨c, hs⟩) ts hts _ (hconsC κ ⟨c, hs⟩) hball)
  · exact hasSum_famX_of_not fam₀ famC X hs ts _ (hexp₀ s' hs ts hts _ (hcons κ s' hs))

/-- The consumed-momenta expansions give the agreement at every centre assignment. -/
theorem centreAgree_of_cons (hd : Disj blk) (hSb : Gsb.IsPlain) {roots : Fin w → (Fin d → ℤ)}
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ)) (Cons : ReplacementSlot Gsb → Mom d → Prop)
    (hcons : ∀ κ : GenDecoration S d roots 0, ∀ s', ¬ IsCentred s' →
      Cons s' (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb s')))))
    (hexp₀ : ∀ s', ¬ IsCentred s' → ∀ ts ∈ Box s', ∀ x, Cons s' x →
      HasSum (fun l => (fam₀.w s' l : ℂ) * fam₀.a s' l x * fsPhase (fam₀.m s' l) ts) (Fs.fs (Φ.iota hS hSb s') ts x))
    (ConsC : CentredSlot Gsb → Mom d → Prop)
    (hconsC : ∀ κ : GenDecoration S d roots 0, ∀ c : CentredSlot Gsb,
      ConsC c (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb (.inr c.1))))))
    (hexpC' : ∀ (c : CentredSlot Gsb) (y : Fin d → ℤ), ∀ ts ∈ Box (.inr c.1), ∀ x, ConsC c x →
      ‖x - latPt d y‖ ≤ 1 →
      HasSum (fun l => ((famC c y).w l : ℂ) * (famC c y).a l x * fsPhase ((famC c y).m l) ts)
        (Fs.fs (Φ.iota hS hSb (.inr c.1)) ts x))
    (X : CentredSlot Gsb → (Fin d → ℤ)) : CentreAgree Φ hS hSb hd L base roots Fs fam₀ famC Box X :=
  fun κ hκ s' ts hts =>
    famVal_famX_eq_cons Φ hd hSb fam₀ famC Box Cons hcons hexp₀ ConsC hconsC hexpC' X κ hκ s' ts hts

/-- **The per-centre mode form with the centred expansion at the consumed momenta only** (`hasSum_modes_centred`
with `hexpC` replaced by `hconsC`, `hexpC'`). -/
theorem hasSum_modes_centred_cons (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ)) (Cons : ReplacementSlot Gsb → Mom d → Prop)
    (hcons : ∀ κ : GenDecoration S d roots 0, ∀ s', ¬ IsCentred s' →
      Cons s' (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb s')))))
    (hexp₀ : ∀ s', ¬ IsCentred s' → ∀ ts ∈ Box s', ∀ x, Cons s' x →
      HasSum (fun l => (fam₀.w s' l : ℂ) * fam₀.a s' l x * fsPhase (fam₀.m s' l) ts) (Fs.fs (Φ.iota hS hSb s') ts x))
    (ConsC : CentredSlot Gsb → Mom d → Prop)
    (hconsC : ∀ κ : GenDecoration S d roots 0, ∀ c : CentredSlot Gsb,
      ConsC c (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb (.inr c.1))))))
    (hexpC' : ∀ (c : CentredSlot Gsb) (y : Fin d → ℤ), ∀ ts ∈ Box (.inr c.1), ∀ x, ConsC c x →
      ‖x - latPt d y‖ ≤ 1 →
      HasSum (fun l => ((famC c y).w l : ℂ) * (famC c y).a l x * fsPhase ((famC c y).m l) ts)
        (Fs.fs (Φ.iota hS hSb (.inr c.1)) ts x))
    (fixS lbS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ →
      τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS →
        ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (X : CentredSlot Gsb → (Fin d → ℤ)) :
    HasSum (fun ξ : ∀ s, (famX fam₀ famC X).Λ s => ((modeWt (famX fam₀ famC X) ξ : ℝ) : ℂ) *
      outerValMμD Gsb L γ δ base roots tt
        (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
          lbDomR (fun c => lbS (Φ.br c)))
        (Φ.hinges hd) (fun z => Zw z * chiX L base X z) hSb (fixMeasure (fun c => fixS (Φ.br c)))
        (fun s' => (famX fam₀ famC X).a s' (ξ s')) (fun s' => (famX fam₀ famC X).m s' (ξ s'))
        (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValWZRL blk D hS L γ δ base roots tt layer (fun κ => Zs κ * chiX L base X (Φ.resDec hS hd κ)) Fs
        fixS lbS) :=
  hasSum_modes_centred_agree Φ RB hd hSb hL0 γ δ D layer tt Zs Zw hZw hZ fam₀ famC Box fixS lbS hU hlbU hP hbox X
    (centreAgree_of_cons Φ hd hSb fam₀ famC Box Cons hcons hexp₀ ConsC hconsC hexpC' X)

/-- The per-centre ξ-summability (centred expansion at the consumed momenta only). -/
theorem summable_modes_centred_cons (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ)) (Cons : ReplacementSlot Gsb → Mom d → Prop)
    (hcons : ∀ κ : GenDecoration S d roots 0, ∀ s', ¬ IsCentred s' →
      Cons s' (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb s')))))
    (hexp₀ : ∀ s', ¬ IsCentred s' → ∀ ts ∈ Box s', ∀ x, Cons s' x →
      HasSum (fun l => (fam₀.w s' l : ℂ) * fam₀.a s' l x * fsPhase (fam₀.m s' l) ts) (Fs.fs (Φ.iota hS hSb s') ts x))
    (ConsC : CentredSlot Gsb → Mom d → Prop)
    (hconsC : ∀ κ : GenDecoration S d roots 0, ∀ c : CentredSlot Gsb,
      ConsC c (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb (.inr c.1))))))
    (hexpC' : ∀ (c : CentredSlot Gsb) (y : Fin d → ℤ), ∀ ts ∈ Box (.inr c.1), ∀ x, ConsC c x →
      ‖x - latPt d y‖ ≤ 1 →
      HasSum (fun l => ((famC c y).w l : ℂ) * (famC c y).a l x * fsPhase ((famC c y).m l) ts)
        (Fs.fs (Φ.iota hS hSb (.inr c.1)) ts x))
    (fixS lbS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ →
      τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS →
        ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (X : CentredSlot Gsb → (Fin d → ℤ)) :
    Summable (fun ξ : ∀ s, (famX fam₀ famC X).Λ s => ((modeWt (famX fam₀ famC X) ξ : ℝ) : ℂ) *
      outerValMμD Gsb L γ δ base roots tt
        (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
          lbDomR (fun c => lbS (Φ.br c)))
        (Φ.hinges hd) (fun z => Zw z * chiX L base X z) hSb (fixMeasure (fun c => fixS (Φ.br c)))
        (fun s' => (famX fam₀ famC X).a s' (ξ s')) (fun s' => (famX fam₀ famC X).m s' (ξ s'))
        (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base)) :=
  (hasSum_modes_centred_cons Φ RB hd hSb hL0 γ δ D layer tt Zs Zw hZw hZ fam₀ famC Box Cons hcons hexp₀ ConsC hconsC
    hexpC' fixS lbS hU hlbU hP hbox X).summable

/-- **The centre-indexed relaxed pinned VINE-B♯ with the centred expansion at the consumed momenta only**
(`hasSum_skelValWZRL_centred` with `hexpC` replaced by `hconsC`, `hexpC'`). -/
theorem hasSum_skelValWZRL_centred_cons (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ)) (Cons : ReplacementSlot Gsb → Mom d → Prop)
    (hcons : ∀ κ : GenDecoration S d roots 0, ∀ s', ¬ IsCentred s' →
      Cons s' (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb s')))))
    (hexp₀ : ∀ s', ¬ IsCentred s' → ∀ ts ∈ Box s', ∀ x, Cons s' x →
      HasSum (fun l => (fam₀.w s' l : ℂ) * fam₀.a s' l x * fsPhase (fam₀.m s' l) ts) (Fs.fs (Φ.iota hS hSb s') ts x))
    (ConsC : CentredSlot Gsb → Mom d → Prop)
    (hconsC : ∀ κ : GenDecoration S d roots 0, ∀ c : CentredSlot Gsb,
      ConsC c (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb (.inr c.1))))))
    (hexpC' : ∀ (c : CentredSlot Gsb) (y : Fin d → ℤ), ∀ ts ∈ Box (.inr c.1), ∀ x, ConsC c x →
      ‖x - latPt d y‖ ≤ 1 →
      HasSum (fun l => ((famC c y).w l : ℂ) * (famC c y).a l x * fsPhase ((famC c y).m l) ts)
        (Fs.fs (Φ.iota hS hSb (.inr c.1)) ts x))
    (MC : ℝ) (hMC : ∀ (c : CentredSlot Gsb) (y : Fin d → ℤ), ∑' l, (famC c y).w l ≤ MC)
    (fixS lbS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ →
      τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS →
        ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun X : CentredSlot Gsb → (Fin d → ℤ) => ∑' ξ : ∀ s, (famX fam₀ famC X).Λ s,
      ((modeWt (famX fam₀ famC X) ξ : ℝ) : ℂ) *
        outerValMμD Gsb L γ δ base roots tt
          (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
            lbDomR (fun c => lbS (Φ.br c)))
          (Φ.hinges hd) (fun z => Zw z * chiX L base X z) hSb (fixMeasure (fun c => fixS (Φ.br c)))
          (fun s' => (famX fam₀ famC X).a s' (ξ s')) (fun s' => (famX fam₀ famC X).m s' (ξ s'))
          (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValWZRL blk D hS L γ δ base roots tt layer Zs Fs fixS lbS) :=
  hasSum_skelValWZRL_centred_agree Φ RB hd hSb hL0 γ δ D layer tt Zs Zw hZw hZ fam₀ famC Box MC hMC fixS lbS hU hlbU
    hP hbox (centreAgree_of_cons Φ hd hSb fam₀ famC Box Cons hcons hexp₀ ConsC hconsC hexpC')

/-- **The joint family sums to the relaxed pinned skeleton value** (centred expansion at the consumed momenta
only; `hasSum_sigma_centred` with `hexpC` replaced by `hconsC`, `hexpC'`). -/
theorem hasSum_sigma_centred_cons (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ)) (Cons : ReplacementSlot Gsb → Mom d → Prop)
    (hcons : ∀ κ : GenDecoration S d roots 0, ∀ s', ¬ IsCentred s' →
      Cons s' (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb s')))))
    (hexp₀ : ∀ s', ¬ IsCentred s' → ∀ ts ∈ Box s', ∀ x, Cons s' x →
      HasSum (fun l => (fam₀.w s' l : ℂ) * fam₀.a s' l x * fsPhase (fam₀.m s' l) ts) (Fs.fs (Φ.iota hS hSb s') ts x))
    (ConsC : CentredSlot Gsb → Mom d → Prop)
    (hconsC : ∀ κ : GenDecoration S d roots 0, ∀ c : CentredSlot Gsb,
      ConsC c (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb (.inr c.1))))))
    (hexpC' : ∀ (c : CentredSlot Gsb) (y : Fin d → ℤ), ∀ ts ∈ Box (.inr c.1), ∀ x, ConsC c x →
      ‖x - latPt d y‖ ≤ 1 →
      HasSum (fun l => ((famC c y).w l : ℂ) * (famC c y).a l x * fsPhase ((famC c y).m l) ts)
        (Fs.fs (Φ.iota hS hSb (.inr c.1)) ts x))
    (MC : ℝ) (hMC : ∀ (c : CentredSlot Gsb) (y : Fin d → ℤ), ∑' l, (famC c y).w l ≤ MC)
    (fixS lbS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ →
      τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS →
        ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun p : (Σ X : CentredSlot Gsb → (Fin d → ℤ), ∀ s, (famX fam₀ famC X).Λ s) =>
      ((modeWt (famX fam₀ famC p.1) p.2 : ℝ) : ℂ) *
        outerValMμD Gsb L γ δ base roots tt
          (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
            lbDomR (fun c => lbS (Φ.br c)))
          (Φ.hinges hd) (fun z => Zw z * chiX L base p.1 z) hSb (fixMeasure (fun c => fixS (Φ.br c)))
          (fun s' => (famX fam₀ famC p.1).a s' (p.2 s')) (fun s' => (famX fam₀ famC p.1).m s' (p.2 s'))
          (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValWZRL blk D hS L γ δ base roots tt layer Zs Fs fixS lbS) :=
  hasSum_sigma_centred_agree Φ RB hd hSb hL0 γ δ D layer tt Zs Zw hZw hZ fam₀ famC Box MC hMC fixS lbS hU hlbU hP hbox
    (centreAgree_of_cons Φ hd hSb fam₀ famC Box Cons hcons hexp₀ ConsC hconsC hexpC')

end Cons

end WaveTurbulence.Flower.MkSlotsI
