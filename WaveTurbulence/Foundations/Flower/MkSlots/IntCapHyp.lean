/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.PRedLeaves
public import WaveTurbulence.Foundations.Flower.MkSlots.Data
public import WaveTurbulence.Foundations.Flower.MkUnits.WSlot
public import WaveTurbulence.Foundations.Flower.Stage1W.Frontier
public import WaveTurbulence.Foundations.FlowerTop.Port.S2ST.AnchorFamilyB

/-! # B3s MK-SLOTS (integration): the isolated analytic input on the cap-couple slots

The skeleton reduction of a capped member (`kernelLeaves_skeleton_reduction_selNWF`) attaches to every skeleton leaf
pair `q` a pinned weighted slot kernel `slotFnNWF … (.inl q)`. When one leaf of `q` is the root of a cap tree
(`IsCapPair`), the native object of `q` is the cap couple (trivial, or D2b's type-2 couple `(X.plug 1 leaf, leaf)`
whose lone leaf is the capped flower), its profile at the cap pair is `1` (anchored, `S2ST.typeProfilesAnchB`), it
may carry the pin of the capped flower parent (`fixCap … plain`) and the dagger weights of that parent (sibling
indicators and the node-local pieces of the removed phase, `dagNodeW`). Such a slot is evaluated at ONE momentum only
(the label of the cap root), so only its value at that momentum matters; in the chain the anchored profile `1` is
replaced by the indicator of that momentum (`anchProfiles`; summable over the lattice, equal on every decoration).

`CapSlotObligation` is the single analytic input of the integration on these slots: for every cap pair slot of the
reconstruction of a prescribed point, the function `ts ↦ capSlotKer … ts x₀` (`x₀` the label of the cap root) has,
on the slot box, a superposition of Fourier modes with `SlotFam`-compatible amplitudes (bounded by `1`,
`SNorm (30 d) 0 ≤ 1`, centred within distance `1` of a lattice point), whose mass is the B3 slot mass
(`K · (C√δ)^{size} · L^{-η⁸·incoh} · c_F^{nr} · leaf`, the leaf factor without the anchored cap pair,
`b⁻¹ · slotLeaf`) times the protected loss `L^{31d+6}`, uniformly in the parameters, on the parameter prefix.

It is to be proved from D3's `ProtPin.protBoundNTGate` (`ProtPin/NTGate.lean`; the `θ = η` bound with the loss
`L^{31d+6}`, configuration `none` for a trivial cap couple and `term` for a type-2 cap couple), D2c's
`ProtCut.CapData.kernelProt_cap` (a cap couple kernel is the paired-tree kernel times one profile), D6b's
`ProtWhole.CapG` (the frozen kernel of a width-2 cap component), D2b's `ProtGeo` (`embeds_stem_cap`,
`protShape_objTree`, `protAmbient_objTree`, `objCfg`: the native object at a cap pair is `objCpl`, its pins are
`fixCap`), main's `LFTwist.reconstruction_coupleEmb` (the native couple of a skeleton pair is embedded in the
reconstruction), and `MkSlots.protSlotSupM` (an X-norm bounded continuous slot function is a superposition).

* `IsCapPair`, `capTreeOf`, `anchProfiles`, `dagNodeW` (node-local dagger weight), `capNodeW` (frontier × dagger
  node weight), `capSlotKer` (the pinned cap slot kernel of the reconstruction of a prescribed point);
* **`CapSlotObligationAt Kc P`**, **`CapSlotObligation`** (`∃ Kc ≥ 1, WTPrefix (CapSlotObligationAt Kc)`);
* `capSlotObligationAt_mono`: large-constant monotonicity (for `prefix_and`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ}

/-- A cap pair: a leaf pair of a skeleton one of whose leaves lies in a cap tree (a cap tree is a single leaf, so that
leaf is the cap root). -/
def IsCapPair (S : Garden w) (hS : S.IsPlain) (J : Finset (Fin w)) (q : SourcePair S) : Prop :=
  (q.firstLeaf hS).1.1 ∈ J ∨ (q.secondLeaf hS).1.1 ∈ J

/-- The phase scale of a capped flower parent `b` in the removed phase `offFactor`
(`exp(-i θ_b ω_b)`, `θ_b = π·sign(b)·δ·L^{2γ}·s`). -/
def capTheta (L γ δ s : ℝ) (G : Garden w) (b : GBranch G.tree) : ℝ :=
  Real.pi * ((G.sign b.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * s

/-- The sign of child `i` in the resonance factor `‖k₀‖² - ‖k₁‖² + ‖k₂‖² - ‖k‖²`. -/
def childSign (i : Fin 3) : ℝ := if i = 1 then -1 else 1

/-- **The node-local dagger weight** at a node `z` (momentum `x`), for the prescribed sibling momenta `cc`:
* if `z` is a capped flower parent `b`: the factor `exp(+i θ_b ‖x‖²)` of its removed phase;
* if `z` is child `i` of a capped flower parent `b`: the factor `exp(-i θ_b ε_i ‖x‖²)` of the removed phase of `b`,
  times the sibling indicator `[x = cc b.1.1 i]` unless `z` is the capped flower.
The product over all nodes is `offCap`'s removed-phase factor times `sibWeightCap` (pointwise). -/
def dagNodeW (L γ δ s : ℝ) (LG : LayeredGarden w) (J : Finset (Fin w))
    (dag : Option (Fin w → Fin 3 → Mom d)) (z : GNode LG.garden.tree) (x : Mom d) : ℂ :=
  dag.elim 1 fun cc =>
    (if hb : ∃ b : GBranch LG.garden.tree, b.toNode = z ∧ IsCapFlowerParent LG J b then
      Complex.exp (((capTheta L γ δ s LG.garden hb.choose * ‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I) else 1) *
    (if hc : ∃ (b : GBranch LG.garden.tree) (i : Fin 3), b.child i = z ∧ IsCapFlowerParent LG J b then
      Complex.exp (((-(capTheta L γ δ s LG.garden hc.choose * childSign hc.choose_spec.choose * ‖x‖ ^ 2) : ℝ) : ℂ) *
          Complex.I) *
        (if (∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.toNode = z) then 1 else
          if x = cc hc.choose.1.1 hc.choose_spec.choose then 1 else 0)
    else 1)

/-- The node weight of the capped integrand on a garden: the frontier weight (`fwNode`, scales `Rf`) times the
node-local dagger weight. -/
def capNodeW (L γ δ : ℝ) (p : ℕ) (s : ℝ) (LG : LayeredGarden w) (J : Finset (Fin w)) (Rf : Fin w → Option ℝ)
    (dag : Option (Fin w → Fin 3 → Mom d)) (z : GNode LG.garden.tree) (x : Mom d) : ℂ :=
  fwNode LG p (fun j => frontierG (Rf j)) z x * dagNodeW L γ δ s LG J dag z x

/-- **The anchored leaf profiles** used in the chain: S2-ST's `typeProfilesAnchB` with the anchored profile `1` replaced
by the indicator of the cap momentum `latticePoint L (roots j)` (`j` the cap tree of the pair). On every decoration
at coset base `0` an anchored input leaf carries exactly that momentum (the cap tree is a single leaf, paired leaves
carry equal labels, the root label is `roots j`), so the class value is unchanged; unlike `1`, the indicator is
summable over the lattice. -/
def anchProfiles (J : Finset (Fin w)) (LG : LayeredGarden w) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (L : ℝ)
    (roots : Fin w → (Fin d → ℤ)) : LeafProfiles w d := fun a =>
  if (pairTrees LG.garden a).1 ∈ J then
    (fun x => if x = latticePoint L (roots (pairTrees LG.garden a).1) then 1 else 0)
  else if (pairTrees LG.garden a).2 ∈ J then
    (fun x => if x = latticePoint L (roots (pairTrees LG.garden a).2) then 1 else 0)
  else typeProfiles LG h a

/-- The cap tree of a cap pair (the tree of its first leaf if that is a cap tree, else of its second leaf). -/
def capTreeOf (S : Garden w) (hS : S.IsPlain) (J : Finset (Fin w)) (q : SourcePair S) : Fin w :=
  if (q.firstLeaf hS).1.1 ∈ J then (q.firstLeaf hS).1.1 else (q.secondLeaf hS).1.1

/-- The reconstruction of a prescribed point at its source layering (it is `a.layered`, `sourceLayer_reconstructs`). -/
abbrev recLG (a : PrescribedPrimeGarden w) : LayeredGarden w :=
  layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)

/-- **The pinned cap slot kernel** of a slot of the reconstruction of `a`: main's slot kernel with the anchored
profiles `anchProfiles`, the node weight `capNodeW` and the intrinsic plain pins `fixCap … plain`. -/
def capSlotKer (L γ δ : ℝ) (p : ℕ) (a : PrescribedPrimeGarden w) (J : Finset (Fin w)) (t s : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (roots : Fin w → (Fin d → ℤ)) (Rf : Fin w → Option ℝ)
    (dag : Option (Fin w → Fin 3 → Mom d)) :
    ReplacementSlot a.prime.skeleton → (Fin 2 → ℝ) → Mom d → ℂ :=
  slotFnNWF a.prime.data a.prime.prime.1 L γ δ (anchProfiles J (recLG a) h L roots)
    (capNodeW L γ δ p s (recLG a) J Rf dag) (sourceLayer a) (sourceLayer_isLayering a)
    (fixCap (recLG a) J (fun _ => FixPat.plain) t s)

/-- **The cap-slot obligation at one parameter record** (constant `Kc d η`). For every `C ≥ C₁`, every prescribed point
`a` of a capped canonical class (cap trees `J`, layers `≤ p`, size `≤ N_{p+1}^4`, times `p < s < t < p + 1`), every
anchored profile family `h` bounded by `b` and frontier scales `≥ L/2`, every dagger datum, every cap pair slot `q`
of the skeleton of `a`, at the cap momentum `x₀ = latticePoint L (roots j)` (`j = capTreeOf … q`): a countable family
of modes `m l ∈ ℤ²` with weights `wt l ≥ 0` (summable) and amplitudes `amp l` (`‖amp l‖ ≤ 1`,
`SNorm (30 d) 0 (amp l) ≤ 1`, supported within distance `1` of the lattice point `latPt d (c l)`) such that on the
slot box
`ts ↦ capSlotKer … (.inl q) ts x₀ = Σ_l wt l · amp l x₀ · e(m l · ts)`,
with mode mass `Σ_l ⟨m l / 2⟩^η · wt l ≤ Kc · (C√δ)^{size(q)} · L^{-η⁸·incoh(q)} · c_F^{nr(q)} · b⁻¹ · leaf_b(q) ·
L^{31d+6}` (`c_F = frontierConst d`, `leaf_b(q) = slotLeaf … (fun _ => b)`). -/
def CapSlotObligationAt (Kc : ℕ → ℝ → ℝ) (P : WTParams) : Prop :=
  ∀ C : ℝ, P.C₁ ≤ C →
  ∀ {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (t s : ℝ),
    p < P.D → IsCanonGC (p + 1) a.layered → a.prime.data.size ≤ P.N (p + 1) ^ 4 →
    CapGeo a.layered J p → a.layered.garden.Irreducible → t ∈ Ioo (p : ℝ) (p + 1) → s ∈ Ioo (p : ℝ) t →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ), 1 ≤ b →
    (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
  ∀ (Rf : Fin (2 * R) → Option ℝ), (∀ j r, Rf j = some r → P.L / 2 ≤ r) →
  ∀ (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
  ∀ q : SourcePair a.prime.skeleton, IsCapPair a.prime.skeleton a.prime.prime.1 J q →
  ∃ (Λ : Type) (_ : Countable Λ) (wt : Λ → ℝ) (m : Λ → Fin 2 → ℤ) (c : Λ → Fin P.d → ℤ)
    (amp : Λ → Mom P.d → ℂ),
    (∀ l, 0 ≤ wt l) ∧ Summable wt ∧ (∀ l k, ‖amp l k‖ ≤ 1) ∧ (∀ l, SNorm (30 * P.d) 0 (amp l) ≤ 1) ∧
    (∀ l k, amp l k ≠ 0 → ‖k - latPt P.d (c l)‖ ≤ 1) ∧
    (∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1 (.inl q),
      HasSum (fun l => (wt l : ℂ) * amp l (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))) *
          fsPhase (m l) ts)
        (capSlotKer P.L P.γ P.δ p a J t s h roots Rf dag (.inl q) ts
          (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))))) ∧
    ∑' l, maxBracketPow P.η (half (m l)) * ENNReal.ofReal (wt l) ≤
      ENNReal.ofReal (Kc P.d P.η * (C * Real.sqrt P.δ) ^ slotSize a.prime.data (.inl q) *
        P.L ^ (-(P.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (.inl q) : ℝ)) *
        (frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 (.inl q) *
          (b⁻¹ * slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            (fun _ => b.toNNReal) (.inl q))) *
        P.L ^ (31 * (P.d : ℝ) + 6))

/-- **`CapSlotObligation`** — the ONE isolated hypothesis of the integration (B3s, milestone α): a constant
`Kc d η ≥ 1` (depending on `d, η` only) for which the cap-slot superpositions `CapSlotObligationAt Kc` exist on the
parameter prefix. To be proved from D3's `ProtPin.protBoundNTGate`, D2c's `ProtCut.CapData.kernelProt_cap`, D6b's
`ProtWhole.CapG`, D2b's `ProtGeo` (`embeds_stem_cap`, `protShape_objTree`, `protAmbient_objTree`, `objCfg`), main's
`LFTwist.reconstruction_coupleEmb` and `MkSlots.protSlotSupM` (see the module docstring). -/
def CapSlotObligation : Prop :=
  ∃ Kc : ℕ → ℝ → ℝ, (∀ d η, 1 ≤ Kc d η) ∧ WTPrefix (CapSlotObligationAt Kc)

/-- The per-record obligation is monotone in the large constants (it reads `C₁` only through `C ≥ C₁`). -/
theorem capSlotObligationAt_mono (Kc : ℕ → ℝ → ℝ) : LargeConstantMonotone (CapSlotObligationAt Kc) := by
  intro P c₁ c₂ _ _ _ _ h₁ _ h C hC R p a J t s hp hcan hsz
  exact h C (h₁.trans hC) (R := R) (p := p) a J t s hp hcan (by rw [← vineEstHalfMK_N P c₁ c₂ (p + 1)]; exact hsz)

end WaveTurbulence.Flower.MkSlots
