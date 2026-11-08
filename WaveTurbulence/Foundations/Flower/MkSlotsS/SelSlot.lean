/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelWeight
public import WaveTurbulence.Foundations.Flower.MkSlotsB.RLeaves
public import WaveTurbulence.Foundations.Flower.MkSlots.IntCapHyp

/-! # B3s-HELPER4 (δ) S3: the selected slots (statement)

A selection absorbed in a slot (S2 case (b)) lies on the lone path of the native object of the slot: the regular chain
`X(β)` inflated at a skeleton branch `β` (slot `.inr β`, no pin of a plain-pattern tree inside) or the cap couple of a
cap pair (slot `.inl q`, the capped flower parent pinned at `s`). Its weight inside the slot is the per-slot factor
`selΘs` of the β reduction (`MkSlotsB.slotFnGWFR`, weight `(∏ W) · Θ · ∏_s Θs s`): the product over the non-core
native nodes of the selection node weight `selNW` (the selected filter `chiD(|Ω|/Rs j)` at the selected vertex, the
shells `χ₀(|Ω|/Rs j)` at the other stem nodes), with `Ω` computed in the native garden at the slot momentum (for a
non-core native branch its three children are native nodes). This is the slot part of S4's partition
(`selWeight_split`, `slotFac`).

* `omegaAt`, `selNW` (`selNW_toNode`: on branches it is S4's `selBW`), `HasSelNative`, `selΘs`;
* `selSlotKer`: the pinned weighted slot kernel of the reconstruction of a prescribed point with the selection factor
  (as B3s's `capSlotKer`, on β's relaxed `slotFnGWFR` with `Θs = selΘs`);
* **`SelSlotObligationAt Kc P`**, **`SelSlotObligation`**: for every slot of the reconstruction containing a selected
  native node, on the slot box, a superposition of Fourier modes with `SlotFam`-compatible amplitudes (at every slot
  momentum for a chain slot, at the cap momentum for a cap pair, as `MkSlots.CapSlotObligationAt`), with mass the B3
  slot mass × the protected loss `L^{2(47d+5)}` (D6's `L^{(47d+5)r}`, `r = pin + #Sel ≤ 2`) × the gain
  `∏ Rs_j^{-1/18}` over the selected native vertices of the slot (D6's `M₂^{-a/18}`, `a ≤ 1` per object).

STATUS: statement only (the proof from `ProtWhole.protAnnBoundGate_of_D3` is open; see `HANDOFF.md`, S3). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.MkSlots
open WaveTurbulence.Flower.MkSlotsT (radProd)

namespace WaveTurbulence.Flower.MkSlotsS

variable {w d : ℕ}

/-- The resonance factor at a node (`0` at a leaf). -/
def omegaAt {w' : ℕ} {G : Garden w'} (k : GNode G.tree → Mom d) (a : GNode G.tree) : ℝ :=
  if h : a.1.2 ∈ (G.tree a.1.1).branching then omegaNode G k ⟨a.1, h⟩ else 0

/-- **The selection node weight** at a node `z` of `LG` with resonance value `x`: on a capped-stem branch, the
selected filter `chiD(|x|/Rs)` at a selected vertex times the shells `radProd (selShellRad …) x`; `1` elsewhere. -/
def selNW (LG : LayeredGarden w) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (z : GNode LG.garden.tree) (x : ℝ) : ℂ :=
  if h : z.1.2 ∈ (LG.garden.tree z.1.1).branching then
    if ∃ j, (⟨z.1, h⟩ : GBranch LG.garden.tree) ∈ stemSetCap LG J j then
      (if (⟨z.1, h⟩ : GBranch LG.garden.tree) ∈ selSetCap LG J kSel then
          ((chiD (|x| / Rs z.1.1) : ℝ) : ℂ) else 1) *
        (radProd (selShellRad LG J kSel Rs ⟨z.1, h⟩) x : ℂ)
    else 1
  else 1

theorem selNW_toNode (LG : LayeredGarden w) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (k : GNode LG.garden.tree → Mom d) (b : GBranch LG.garden.tree) :
    selNW LG J kSel Rs b.toNode (omegaNode LG.garden k b) = selBW LG J kSel Rs k b := by
  have hb : (b.toNode).1.2 ∈ (LG.garden.tree (b.toNode).1.1).branching := b.2
  have he : (⟨(b.toNode).1, hb⟩ : GBranch LG.garden.tree) = b := rfl
  unfold selNW
  rw [dif_pos hb, he]
  unfold selBW
  congr 1
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1

section Slots

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)

/-- The slot `sl` of the reconstruction contains a selected vertex as a non-core native node. -/
def HasSelNative (sl : ReplacementSlot S) : Prop :=
  ∃ a : NativeNode D sl, (∀ β : GBranch S.tree, nativeNodeAt D hS sl a ≠ (D.coreBranch hS β).toNode) ∧
    ∃ v ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel, v.1 = (nativeNodeAt D hS sl a).1

/-- The selected vertices of the reconstruction that are non-core native nodes of the slot `sl`. -/
def selNative (sl : ReplacementSlot S) : Finset (GBranch (layeredReconstruction D hS layer hLayer).garden.tree) :=
  (selSetCap (layeredReconstruction D hS layer hLayer) J kSel).filter fun v =>
    ∃ a : NativeNode D sl, (∀ β : GBranch S.tree, nativeNodeAt D hS sl a ≠ (D.coreBranch hS β).toNode) ∧
      v.1 = (nativeNodeAt D hS sl a).1

/-- **The per-slot selection factor** (β's `Θs`): over the non-core native nodes of the slot, the selection node weight
at the resonance factor of the native garden at the slot momentum `k`. -/
def selΘs (L : ℝ) : (sl : ReplacementSlot S) → Mom d → NativeRelativeDecoration D hS d sl → ℂ
  | .inl p => fun k κ => ∏ a : GNode (nativeCoupleGarden D hS p).tree,
      if ∃ β : GBranch S.tree, (nativeCoupleForest D hS p).nodeEmbedding a = (D.coreBranch hS β).toNode then 1
      else selNW (layeredReconstruction D hS layer hLayer) J kSel Rs ((nativeCoupleForest D hS p).nodeEmbedding a)
        (omegaAt (cosetDecoration (nativeCoupleGarden D hS p) L k κ.1) a)
  | .inr b => fun k κ => ∏ a : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree,
      if ∃ β : GBranch S.tree, chainContextNode D hS b a = (D.coreBranch hS β).toNode then 1
      else selNW (layeredReconstruction D hS layer hLayer) J kSel Rs (chainContextNode D hS b a)
        (omegaAt (cosetDecoration (decodedTree (D.tree b) (nodeSign S.sig b.1)) L k κ.1) a)

end Slots

/-- **The selected slot kernel** of a slot of the reconstruction of `a`: the pinned weighted slot kernel (anchored
profiles, frontier × dagger node weight, the intrinsic pins `fixCap … pat`) with the selection factor `selΘs`. -/
def selSlotKer (L γ δ : ℝ) (p : ℕ) (a : PrescribedPrimeGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat)
    (t s : ℝ) (kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (roots : Fin w → (Fin d → ℤ)) (Rf : Fin w → Option ℝ)
    (dag : Option (Fin w → Fin 3 → Mom d)) :
    ReplacementSlot a.prime.skeleton → (Fin 2 → ℝ) → Mom d → ℂ :=
  MkSlotsB.slotFnGWFR a.prime.data a.prime.prime.1 L γ δ (anchProfiles J (recLG a) h L roots)
    (capNodeW L γ δ p s (recLG a) J Rf dag)
    (selΘs a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel Rs L)
    (sourceLayer a) (sourceLayer_isLayering a) (fixCap (recLG a) J pat t s)

/-- **The selected-slot obligation at one parameter record** (constant `Kc d η`; the form of
`MkSlots.CapSlotObligationAt`). For every `C ≥ C₁`, every prescribed point `a` of a capped canonical class, every
pattern `pat` plain on the selected trees, every selection `kSel` at scales `Rs ≥ L`, every anchored profile family
bounded by `b`, frontier scales `≥ L/2` and dagger datum, every slot `sl` of the reconstruction containing a selected
non-core native node: a countable family of modes with `SlotFam`-compatible amplitudes such that on the slot box
`ts ↦ selSlotKer … sl ts k = Σ_l wt l · amp l k · e(m l · ts)` at every momentum `k` (only at the cap momentum `x₀` when
`sl` is a cap pair), with mode mass `Σ_l ⟨m l/2⟩^η wt l ≤ Kc · (B3 slot mass) · L^{2(47d+5)} · ∏_{v} Rs_{j(v)}^{-1/18}`
over the selected native vertices `v` of `sl`. -/
def SelSlotObligationAt (Kc : ℕ → ℝ → ℝ) (P : WTParams) : Prop :=
  ∀ C : ℝ, P.C₁ ≤ C →
  ∀ {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ),
    p < P.D → IsCanonGC (p + 1) a.layered → a.prime.data.size ≤ P.N (p + 1) ^ 4 →
    CapGeo a.layered J p → CapPatValid a.layered J pat p → a.layered.garden.Irreducible →
    t ∈ Ioo (p : ℝ) (p + 1) → s ∈ Ioo (p : ℝ) t →
  ∀ (kSel : Fin (2 * R) → Option ℕ), (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
  ∀ (Rs : Fin (2 * R) → ℝ), (∀ j, P.L ≤ Rs j) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ), 1 ≤ b →
    (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
  ∀ (Rf : Fin (2 * R) → Option ℝ), (∀ j r, Rf j = some r → P.L / 2 ≤ r) →
  ∀ (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
  ∀ sl : ReplacementSlot a.prime.skeleton,
    HasSelNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl →
  ∃ (Λ : Type) (_ : Countable Λ) (wt : Λ → ℝ) (m : Λ → Fin 2 → ℤ) (c : Λ → Fin P.d → ℤ)
    (amp : Λ → Mom P.d → ℂ),
    (∀ l, 0 ≤ wt l) ∧ Summable wt ∧ (∀ l k, ‖amp l k‖ ≤ 1) ∧ (∀ l, SNorm (30 * P.d) 0 (amp l) ≤ 1) ∧
    (∀ l k, amp l k ≠ 0 → ‖k - latPt P.d (c l)‖ ≤ 1) ∧
    (∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1 sl, ∀ k : Mom P.d,
      (∀ q, sl = .inl q → IsCapPair a.prime.skeleton a.prime.prime.1 J q →
        k = latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))) →
      HasSum (fun l => (wt l : ℂ) * amp l k * fsPhase (m l) ts)
        (selSlotKer P.L P.γ P.δ p a J pat t s kSel Rs h roots Rf dag sl ts k)) ∧
    ∑' l, maxBracketPow P.η (half (m l)) * ENNReal.ofReal (wt l) ≤
      ENNReal.ofReal (Kc P.d P.η * (C * Real.sqrt P.δ) ^ slotSize a.prime.data sl *
        P.L ^ (-(P.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          sl : ℝ)) *
        (frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 sl *
          (b⁻¹ * slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            (fun _ => b.toNNReal) sl)) *
        P.L ^ (2 * (47 * (P.d : ℝ) + 5)) *
        ∏ v ∈ selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl,
          Rs v.1.1 ^ (-(1 / 18 : ℝ)))

/-- **`SelSlotObligation`**: a constant `Kc d η ≥ 1` for which the selected-slot superpositions exist on the parameter
prefix (to be proved from `ProtWhole.protAnnBoundGate_of_D3` under D3's `ProtBoundGate`). -/
def SelSlotObligation : Prop :=
  ∃ Kc : ℕ → ℝ → ℝ, (∀ d η, 1 ≤ Kc d η) ∧ WTPrefix (SelSlotObligationAt Kc)

end WaveTurbulence.Flower.MkSlotsS
