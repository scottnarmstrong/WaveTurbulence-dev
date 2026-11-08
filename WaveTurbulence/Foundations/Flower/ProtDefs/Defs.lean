/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Top.StarStatements
public import WaveTurbulence.Foundations.Flower.FlShell.Shell
public import WaveTurbulence.Foundations.Flower.MkDefs.ChiDNorm

/-! Shared statement module of D2a PROT-KER (probe sections 1-6 copied by source, see COPIED-SHA256SUMS; `chiD` is
FL-SHELL's, reused). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal
open WaveTurbulence.Flower.FlShell (chiD)

namespace WaveTurbulence.Flower.ProtDefs

/-! ## §1 Protected kernels (D2a PROT-KER) -/

/-- **Resonance multipliers** on a branch set `F` (S (8.5), o82 §§14, 18): branch `b` carries `chi0 (|Ω_b| / M b)`
(an upper filter) or, if `ann b`, `chiD (|Ω_b| / M b)` (a selected annular factor). Exports take two layers
(`filtWeight F ann M * filtWeight Fu false Mu`): at most four factors per linked frequency (o82 allows any fixed
multiplicity; the stem filter `σ` and the selection shell's `chi0(|Ω|/R_j)` can meet on one branch). -/
noncomputable def filtWeight {w d : ℕ} {G : Garden w} (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool)
    (M : GBranch G.tree → ℝ) (k : GNode G.tree → Mom d) : ℂ :=
  ∏ b ∈ F, (((if ann b then chiD else chi0) (|omegaNode G k b| / M b) : ℝ) : ℂ)

/-- **The protected kernel**: main's leafwise kernel with a decoration multiplier `m`, designated (pinned) branches
`fix` (frozen `kDomainFix`, constraints between two designated branches dropped) and the lone-port lower time `s`
on free lone parents. With `fix ≡ none` and no flowers it is `Stage1W.kernelLeavesW` (`KernelProtBridge`). -/
noncomputable def kernelProt (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) *
          (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
            (kDomainFix LG up fix ∩ {τ | ∀ b, LG.garden.IsLoneParent b → fix b = none → s < τ b}).indicator
              (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) (LG.garden.extendFix fix τ)) *
          ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ))

/-- D2a bridge: no designated branches and no flowers give the weighted leafwise kernel. -/
def KernelProtBridge : Prop :=
  ∀ (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ),
    (∀ b, ¬ LG.garden.IsFlowerParent b) →
    kernelProt L γ δ LG H m up s (fun _ => none) k₀ nroot nfl =
      Flower.Stage1W.kernelLeavesW L γ δ LG H up s k₀ nroot nfl m

/-- The chain of a protected object (o73 Prop 3.1) lies in layer `p`: the strict prefixes of the lone path of
tree `0` (the stem from the root of the object to its lone port, or to the flower in a cap couple). -/
def ChainIn (p : ℕ) (X : RegChain) {w : ℕ} (LG : LayeredGarden w) : Prop :=
  ∀ b : GBranch LG.garden.tree, b.1.1.val = 0 → b.1.2 <+: X.lonePath → b.1.2 ≠ X.lonePath →
    LG.layer b.toNode = p

/-- **The protected geometry** (o73 Prop 3.1): a stem-rooted regular paired tree (`w = 1`, chain code `X`) or a cap
couple (`w = 2`, code `type2 X nil triv`, tree `1` the trivial cap), with its chain in layer `p`. -/
def ProtShape (p : ℕ) (X : RegChain) : {w : ℕ} → LayeredGarden w → Prop
  | 1, LG => X.wf = true ∧ X.DecodesTree LG.garden ∧ (∀ a, LG.layer a ≤ p) ∧ ChainIn p X LG
  | 2, LG => (RegCpl.type2 X .nil .triv).wf = true ∧ (RegCpl.type2 X .nil .triv).Decodes LG.garden ∧
      LG.garden.tree 1 = TTree.leaf ∧ (∀ a, LG.layer a ≤ p) ∧ ChainIn p X LG
  | _, _ => False

/-- **The canonical ambient of a protected object** (ruling R172, finding F-D3-1; D0-PROT `AmbientProbe.lean`). The
object sits in a canonical garden `H` of level `p + 1` (`IsCanonGC (p + 1) H`, supplied by `MkCarries`) with the layers
of `H`: the ambient clause of main's `IsCoherentTreeAt` / `IsCoherentCoupleAt` without `CohOn` (a protected object may
be incoherent). Trees (`w = 1`): the chain `X` is embedded at `a` with the object's root sign (`ChainEmb`). Cap
couples (`w = 2`): the near chain is embedded at `a` with its ambient sign `ζ` and code `X₀`, the object's code being
`X₀` (`ζ = 1`) or `ConjCoh.conjChain X₀` (`ζ = -1`) (= D2b's `normChain ζ X₀`), and its lone leaf (the capped flower)
is paired with the root `b` of a cap tree of `H`. It excludes non-canonical layerings (F-D3-1), and it is transported
to sub-objects by main's `chainEmb_append_left/right`, `ChainEmb.parts`, `Embeds.type2`, so the coherent pieces of a
cut are `IsCoherentTreeAt` / `IsCoherentCoupleAt` objects of the same `H`. -/
def ProtAmbient (p : ℕ) (X : RegChain) : {w : ℕ} → LayeredGarden w → Prop
  | 1, LG => ∃ (w' : ℕ) (H : LayeredGarden w') (a : Fin w' × TTree.Path) (h : TTree),
      IsCanonGC (p + 1) H ∧ Links.ChainEmb H.garden X (LG.garden.sig 0) a h ∧
      nodeSign H.garden.sig a = LG.garden.sig 0 ∧
      ∀ z : GNode LG.garden.tree, LG.layer z = Links.layerAt H (addrExt a z.1.2)
  | 2, LG => ∃ (w' : ℕ) (H : LayeredGarden w') (a b : Fin w' × TTree.Path) (ζ : ℤˣ) (X₀ : RegChain),
      IsCanonGC (p + 1) H ∧ Links.ChainEmb H.garden X₀ ζ a .leaf ∧ nodeSign H.garden.sig a = ζ ∧
      X = (if ζ = 1 then X₀ else ConjCoh.conjChain X₀) ∧
      b.2 = [] ∧ H.garden.tree b.1 = TTree.leaf ∧
      (∀ ℓ : GLeaf H.garden.tree, ℓ.1 = addrExt a X₀.lonePath → (H.garden.pair ℓ).1 = b) ∧
      ∀ z : GNode LG.garden.tree,
        LG.layer z = (if z.1.1 = 0 then Links.layerAt H (addrExt a z.1.2) else Links.layerAt H b)
  | _, _ => False

/-- The size (`2 ×` half-order) of a protected object. -/
def protSize (X : RegChain) : {w : ℕ} → LayeredGarden w → ℕ
  | 1, _ => X.size
  | 2, _ => (RegCpl.type2 X .nil .triv).size
  | _, _ => 0

/-- The full original incoherency index of a protected object (all of it is retained, Thm 7.3′(6), (19.2)). -/
noncomputable def protIncoh (X : RegChain) : {w : ℕ} → LayeredGarden w → ℕ
  | 1, LG => LG.incoherency (X.treeLinks (LG.garden.sig 0))
  | 2, LG => LG.incoherency (RegCpl.type2 X .nil .triv).links
  | _, _ => 0

/-- **Pin configurations** of a protected object, by chain position (o73 (13.1); o104 Prop 7.3 (P1)–(P8); U-clock
(L2)–(L4)). `term` = the terminal chain node (the flower parent, or `π` in (P6)), `pen` = its chain parent. -/
inductive ProtCfg
  /-- protected, unpinned (root children, flower siblings, Π2 neighbours): ordinary kernel. -/
  | none
  /-- (13.1), (P6), (L2)/(L3): terminal node at `s`. -/
  | term
  /-- (P1): `dRoot`, root at `t`, flower parent outside the object. -/
  | root
  /-- (P2)/(P3): root at `t`, terminal node (flower parent) at `s`. -/
  | rootTerm
  /-- (P4)/(P5): `dParent (i)`, penultimate and terminal chain nodes both at `s`. -/
  | penTerm
  /-- (P7): `dChild (i)`, terminal node and its off-chain branching child `i` both at `s`. -/
  | termChild (i : Fin 3)
  /-- (P8)/(L4): root trace, the root at its own upper clock. -/
  | trace
  deriving DecidableEq

/-- The designated paths (in tree `0`) and times of a configuration. -/
def ProtCfg.pins (X : RegChain) (s t up : ℝ) : ProtCfg → List (TTree.Path × ℝ)
  | .none => []
  | .term => [(X.lonePath.dropLast, s)]
  | .root => [([], t)]
  | .rootTerm => [([], t), (X.lonePath.dropLast, s)]
  | .penTerm => [(X.lonePath.dropLast.dropLast, s), (X.lonePath.dropLast, s)]
  | .termChild i => [(X.lonePath.dropLast, s), (X.lonePath.dropLast ++ [i], s)]
  | .trace => [([], up)]

/-- The designated-time function of a configuration. -/
def ProtCfg.fix (cfg : ProtCfg) (X : RegChain) (s t up : ℝ) {w : ℕ} {T : Fin w → TTree} (b : GBranch T) :
    Option ℝ :=
  if b.1.1.val = 0 then (cfg.pins X s t up).lookup b.1.2 else Option.none

/-- (R176) The configuration pins the ROOT of the object at `t`: `root` (P1), `rootTerm` (P2/P3), and `penTerm` when the
penultimate chain node is the root (`Xp = nil`). Not `trace` (the root at its own upper clock). -/
def ProtCfg.pinsRoot (X : RegChain) : ProtCfg → Bool
  | .root => true
  | .rootTerm => true
  | .penTerm => X.lonePath.dropLast.dropLast.isEmpty
  | _ => false

/-- (R176) The time box of a configuration: `timeBoxGt p q'`, restricted to `t ≤ ts 0` when the configuration pins the
root at `t` (the upper clock of an object whose root is pinned is the top time, so `ts 0 < t` is never consumed). -/
def ProtCfg.box (cfg : ProtCfg) (X : RegChain) (t p q' : ℝ) : Set (Fin 2 → ℝ) :=
  if cfg.pinsRoot X then {ts | ts ∈ timeBoxGt p q' ∧ t ≤ ts 0} else timeBoxGt p q'

/-- Validity (o104 `PatValid` transported): the pinned positions are distinct branching chain nodes, and a `dChild`
vertex is an off-chain branching child of layer `p`. -/
def ProtCfg.Valid (X : RegChain) {w : ℕ} (LG : LayeredGarden w) (p : ℕ) : ProtCfg → Prop
  | .none => True
  | .term => X.lonePath ≠ []
  | .root => X.lonePath ≠ []
  | .rootTerm => 2 ≤ X.lonePath.length
  | .penTerm => 2 ≤ X.lonePath.length
  | .termChild i => X.lonePath ≠ [] ∧ X.lonePath.getLast? ≠ some i ∧
      ∃ b : GBranch LG.garden.tree, b.1.1.val = 0 ∧ b.1.2 = X.lonePath.dropLast ++ [i] ∧ LG.layer b.toNode = p
  | .trace => True

/-- Local lattice outputs: the coset `b₀ + ℤ_L^d` inside the unit ball at `c₀` (o73 (13.3)–(13.4)). -/
def latticeBall (L : ℝ) {d : ℕ} (b₀ c₀ : Mom d) : Set (Mom d) :=
  {k | ‖k - c₀‖ ≤ 1 ∧ ∃ n : Fin d → ℤ, k = b₀ + latticePoint L n}

/-- A **dagger indicator** (o104 Lemma 3.3, §8: `1[k_e = c_e]` on the edges from the flower parent to its non-flower
children), allowed in a protected object only when its terminal node (the flower parent) is pinned: values in
`[0,1]`, reading only the momenta of the children of the terminal node. It restricts the exceptional-pair sum, which
the estimates take in absolute value (o104 Prop 8.1; o73 §21). -/
def TermChildIndicator (X : RegChain) {w d : ℕ} {T : Fin w → TTree} (ind : (GNode T → Mom d) → ℝ) : Prop :=
  (∀ κ, 0 ≤ ind κ ∧ ind κ ≤ 1) ∧ ∀ κ κ' : GNode T → Mom d,
    (∀ a : GNode T, a.1.1.val = 0 → a.1.2 ≠ [] → a.1.2.dropLast = X.lonePath.dropLast → κ a = κ' a) →
    ind κ = ind κ'

/-! ## §2 Time operators (D1 done; D1b PROT-OPS) -/

/-- o104 Lemma 7.1(1) with `r` spectator times (spectators first): the consumed-modulation operator `T_A`. -/
def TerminalOperatorBoundY : Prop :=
  ∀ (d r : ℕ) (θ : ℝ), 0 ≤ θ → θ ≤ 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (A : ℝ) (H : (Fin (r + 3) → ℝ) → Mom d → ℂ) (K : Set (Mom d)),
      XNormRestr θ 0 0 {ts : Fin (r + 2) → ℝ | 0 < ts (Fin.natAdd r 1) ∧
          ts (Fin.natAdd r 1) < ts (Fin.natAdd r 0) ∧ ts (Fin.natAdd r 0) < 1} K
        (fun ts k => ∫ u in ts (Fin.natAdd r 1)..ts (Fin.natAdd r 0),
          Complex.exp (((Real.pi * A * (u - ts (Fin.natAdd r 1)) : ℝ) : ℂ) * Complex.I) *
            H (Fin.append (fun i : Fin r => ts (Fin.castAdd 2 i))
              ![ts (Fin.natAdd r 0), u, ts (Fin.natAdd r 1)]) k) ≤
      ENNReal.ofReal C * XNorm θ 0 0 H

/-- o104 Lemma 7.1(2): the mirror operator `T'_A H (t,s) = ∫_s^t e^{πiA(t-u)} H(t,u,s) du`. -/
def MirrorOperatorBoundY : Prop :=
  ∀ (d r : ℕ) (θ : ℝ), 0 ≤ θ → θ ≤ 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (A : ℝ) (H : (Fin (r + 3) → ℝ) → Mom d → ℂ) (K : Set (Mom d)),
      XNormRestr θ 0 0 {ts : Fin (r + 2) → ℝ | 0 < ts (Fin.natAdd r 1) ∧
          ts (Fin.natAdd r 1) < ts (Fin.natAdd r 0) ∧ ts (Fin.natAdd r 0) < 1} K
        (fun ts k => ∫ u in ts (Fin.natAdd r 1)..ts (Fin.natAdd r 0),
          Complex.exp (((Real.pi * A * (ts (Fin.natAdd r 0) - u)) : ℝ) * Complex.I) *
            H (Fin.append (fun i : Fin r => ts (Fin.castAdd 2 i))
              ![ts (Fin.natAdd r 0), u, ts (Fin.natAdd r 1)]) k) ≤
      ENNReal.ofReal C * XNorm θ 0 0 H

/-- o104 Lemma 7.1(3): a fixed last time (on a translated unit cube). `G` is continuous in time: `XNorm` sees only
the a.e. class, and the slice is a null set (D1b's counterexample; wt-orch R160). -/
def FixedSlotBound : Prop :=
  ∀ (d r : ℕ) (θ : ℝ), 0 ≤ θ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q a : ℝ) (G : (Fin (r + 1) → ℝ) → Mom d → ℂ) (K : Set (Mom d)),
      (∀ k, Continuous fun t => G t k) →
      XNormRestr θ 0 0 (Set.pi univ fun _ => Icc q (q + 1)) K (fun y k => G (Fin.snoc y a) k) ≤
        ENNReal.ofReal C * XNorm θ 0 0 G

/-- o104 Lemma 7.1(4): the diagonal trace `g ↦ g(…, s, s)`. `G` is continuous in time (null-set trace; R160). -/
def DiagonalBound : Prop :=
  ∀ (d r : ℕ) (θ : ℝ), 0 ≤ θ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℝ) (G : (Fin (r + 2) → ℝ) → Mom d → ℂ) (K : Set (Mom d)),
      (∀ k, Continuous fun t => G t k) →
      XNormRestr θ 0 0 (Set.pi univ fun _ => Icc q (q + 1)) K
          (fun (y : Fin (r + 1) → ℝ) k => G (Fin.snoc y (y (Fin.last r))) k) ≤
        ENNReal.ofReal C * XNorm θ 0 0 G

/-- o104 Lemma 7.1(5): integration of a modulated slot over a fixed unit interval, uniformly in `A`. -/
def FixedIntervalBound : Prop :=
  ∀ (d r : ℕ) (θ : ℝ), 0 ≤ θ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (A q q' : ℝ) (G : (Fin (r + 1) → ℝ) → Mom d → ℂ) (K : Set (Mom d)),
      XNormRestr θ 0 0 (Set.pi univ fun _ => Icc q (q + 1)) K
          (fun y k => ∫ u in q'..q' + 1,
            Complex.exp (((Real.pi * A * u : ℝ) : ℂ) * Complex.I) * G (Fin.snoc y u) k) ≤
        ENNReal.ofReal C * XNorm θ 0 0 G

/-- o82 Lemmas 17.1–17.2 (folding extension and interpolation) at a fixed output, on the unit triangle:
`‖f‖_{A^η} ≤ C ‖f‖_∞^τ ‖f‖_{A^{1/4}}^{1-τ}`, `τ = (1 - 8η)/9`. -/
def FoldInterpolation : Prop :=
  ∀ η : ℝ, 0 ≤ η → η < 1 / 8 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℝ) (f : (Fin 2 → ℝ) → Unit → ℂ),
      (∀ v, ContinuousOn (fun ts => f ts v) {ts | q ≤ ts 1 ∧ ts 1 ≤ ts 0 ∧ ts 0 ≤ q + 1}) →
      XNorm00Restr η {ts : Fin 2 → ℝ | q ≤ ts 1 ∧ ts 1 ≤ ts 0 ∧ ts 0 ≤ q + 1} Set.univ f ≤
        ENNReal.ofReal C *
          (⨆ (ts : Fin 2 → ℝ) (_ : q ≤ ts 1 ∧ ts 1 ≤ ts 0 ∧ ts 0 ≤ q + 1), ‖f ts ()‖ₑ) ^ ((1 - 8 * η) / 9) *
          XNorm00Restr (1 / 4) {ts : Fin 2 → ℝ | q ≤ ts 1 ∧ ts 1 ≤ ts 0 ∧ ts 0 ≤ q + 1} Set.univ f ^
            (1 - (1 - 8 * η) / 9)

/-- o73 (13.4): per-lattice-output time norms give the local `X^{θ,30d,0}` norm on a unit ball at cost `L^{31d}`. -/
def LocalOutputExtension : Prop :=
  ∀ (d : ℕ) (θ : ℝ), 0 ≤ θ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ))
    (b₀ c₀ : Mom d) (F : (Fin r → ℝ) → Mom d → ℂ) (X : ℝ≥0∞),
    (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
    XNormRestr θ (30 * d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (C * L ^ (31 * d)) * X

/-! ## §3 Filtered ordinary objects (D5) -/

/-- **D5b FILT-INC** (o82 Prop 15.1 `g ≥ 1`, Lemma 16.1, Lemma 18.1): main's leafwise incoherent gate for kernels
carrying INC-TOP star weights and resonance multipliers, in `X^η` (no loss) and `X^{1/4}` (loss `L^{4d}`). -/
def FiltIncoherentDecayAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ θ c : ℝ,
    (θ = P.η ∧ c = 0) ∨ (θ = 1 / 4 ∧ c = 4 * P.d) →
    (∀ (Q : RegCpl), Q.wf = true → Q.size = 2 * n → ∀ (LG : LayeredGarden 2),
      Q.Decodes LG.garden → (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q → LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
      1 ≤ LG.incoherency Q.links →
      ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
      ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
        (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) →
      ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      XNormRestr θ (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1)
          0 k (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ)) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) *
          regBound P n (LG.incoherency Q.links) * ENNReal.ofReal (leafSizeProduct LG B)) ∧
    (∀ (X : RegChain), X.wf = true → X.size = 2 * n → ∀ (LG : LayeredGarden 1),
      X.DecodesTree LG.garden → (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q' ≤ q → q ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q →
      (∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') →
      1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) →
      ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
      ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
        (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) →
      ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      XNormRestr θ (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ)) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) *
          regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0))) *
          ENNReal.ofReal (leafSizeProduct LG B))

def FiltIncoherentDecayGate : Prop := WTPrefix FiltIncoherentDecayAt

/-- **D5d FILT-COH** (o82 Prop 15.1 `g = 0` bound and Lemma 16.1 coherent): coherent objects with star weights and
resonance multipliers, in every weight `θ ≤ 1/4`, with no loss. Only a bound: no principal approximation of a
filtered object is consumed anywhere on the flower route (§4.2 of SCOPE). -/
def FiltCoherentBoundAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 →
    (∀ (Q : RegCpl) (LG : LayeredGarden 2) (q q' : ℕ),
      q' ≤ q → q ≤ p → Q.size = 2 * n → IsCoherentCoupleAt p q q' Q LG →
      ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
      ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
        (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) →
      ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      XNormRestr θ (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1)
          0 k (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ)) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B)) ∧
    (∀ (X : RegChain) (LG : LayeredGarden 1) (q q' : ℕ),
      q' ≤ q → q ≤ p → X.size = 2 * n → IsCoherentTreeAt p q q' X LG →
      ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
      ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
        (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) →
      ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      XNormRestr θ (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ)) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B))

def FiltCoherentBoundGate : Prop := WTPrefix FiltCoherentBoundAt

open scoped FourierTransform in
/-- **D5c, o82 Prop 2.1**: the filtered extracted pole `g_S(u) = χ_∞(u) χ₀(u/S)/u` has `⟨σ⟩^{-2d}` Fourier decay,
uniformly in `S ≥ 1` (main's `ApproxNT.norm_mKerHat_mul_le` is the dyadic case `S = 2^{K+1}`). -/
def FiltPoleFourier : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ K : ℝ, 0 ≤ K ∧ ∀ S : ℝ, 1 ≤ S → ∀ σ : ℝ,
    ‖𝓕 (fun u : ℝ => ((Fourier.chiInfinity u / u * chi0 (u / S) : ℝ) : ℂ)) σ‖ * (1 + σ ^ 2) ^ d ≤ K

/-- The filtered DH23 profile: main's `ApproxNT.resProfile` with each extracted pole multiplied by `χ₀(·/S_j)`
(filters on integrable coordinates are absorbed into `Ψ₁` by FL-COEF). -/
noncomputable def filtProfile {n : ℕ} (J : Finset (Fin n)) (S : Fin n → ℝ)
    (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (Ω : Fin n → ℝ) : ℂ :=
  (∏ j ∈ J, ((Fourier.chiInfinity (Ω j) / Ω j * chi0 (Ω j / S j) : ℝ) : ℂ)) *
    Ψ₁ (WithLp.toLp 2 (fun i : {j // j ∉ J} => Ω i))

/-- **D5c FILT-NT, o82 Thm 10.1 (10.5)**: main's `RegAsymp.crude_normalized_sum` for the filtered profile, uniformly in
the filter scales (with the `C₀^n` Gevrey constant of `ApproxNT.dh23_prop_6_4`). -/
def FiltCrudeNormalizedSum : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ {γ η : ℝ}, γ ∈ Set.Ioo (0 : ℝ) 1 → 0 < η → η ≤ 1 / 20 →
    η ≤ ((d : ℝ) - 1) * (1 - γ) → η ≤ γ → ∀ C₀ : ℝ, 1 ≤ C₀ →
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L ^ (-(η / 2)) ≤ δ → δ ≤ 1 → ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.log L ^ A →
      ∀ H : ℝ, 0 ≤ H →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → ApproxNT.Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x, y) ∈ ApproxNT.supportSet xs ys a b lam) →
      (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖ApproxNT.fourierW W τ.1 τ.2‖ₑ *
        ENNReal.ofReal (1 + 2 * Real.pi * ApproxNT.freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal H →
      ∀ (J : Finset (Fin n)) (S : Fin n → ℝ), (∀ j, 1 ≤ S j) →
      ∀ Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ, ContDiff ℝ (⊤ : ℕ∞) Ψ →
      ApproxNT.WordDerivL1 Ψ (fun k => C₀ ^ n * ((4 * k).factorial : ℝ)) →
      ‖(((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) : ℂ) *
        ApproxNT.approxSum L (L ^ (2 * γ) * δ) W (filtProfile J S Ψ)‖ ≤
        (∏ j, lam j) ^ (2 * d) * (C * δ / 4) ^ n * H

/-! ## §4 Pinned protected objects (D3 PROT-PIN) -/

/-- **D3 export** (R172: on a canonical ambient, `ProtAmbient`) (o73 Props 13.2–13.3, (17.2); o82 Cor 15.2; o104 Props 7.4, 7.6 (revised §13.2); U-clock (L2)–(L4)):
every pinned protected object, with its star weights and upper filters, in the local output norm `X^{θ,30d,0}`, with
its full incoherency gain. Explicit boundary phases are functions of the external `t, s` and of the object's own
exceptional pair; they are inside the kernel, so the bound is for the consumed (actual) object. `θ = η` costs
`L^{31d+6}`; `θ = 1/4` (a slot at a selected residual vertex) is needed only for `none`/`term` and costs `L^{47d+2}`.
The time box is `cfg.box` (R176): `timeBoxGt p q'`, cut to `t ≤ ts 0` for the configurations that pin the root at `t`. -/
def ProtBoundAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ (w : ℕ) (LG : LayeredGarden w) (X : RegChain),
  ProtShape p X LG → protSize X LG = 2 * n →
  ∀ (cfg : ProtCfg), cfg.Valid X LG p → ProtAmbient p X LG → ∀ (θ c : ℝ),
    (θ = P.η ∧ c = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ c = 47 * P.d + 2 ∧ (cfg = .none ∨ cfg = .term)) →
  ∀ (s t : ℝ), (p : ℝ) < s → s < t → t < p + 1 → ∀ q' : ℕ, q' ≤ p →
  ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
  ∀ (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) →
  ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
  ∀ (ind : (GNode LG.garden.tree → Mom P.d) → ℝ), TermChildIndicator X ind →
    ((cfg = .none ∨ cfg = .root ∨ cfg = .trace) → ∀ κ, ind κ = 1) →
  ∀ (H : LeafProfiles w P.d) (B : (Fin w × TTree.Path) → NNReal), LeafwiseControlled LG H B →
  ∀ (b₀ c₀ : Mom P.d),
    XNormRestr θ (30 * P.d) 0 (cfg.box X t p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ * filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (cfg.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) *
        ENNReal.ofReal (leafSizeProduct LG B)

def ProtBoundGate : Prop := WTPrefix ProtBoundAt

/-- **D3 export for a selected vertex** (ruling R181; D6b finding F-D6b-2): `ProtBoundAt` in the configuration `term`
(terminal node pinned at `s`) for trees and cap couples, with ONE selected annular filter
`chiDN(|Ω_v|/M₂)` (the normalized `MkDefs.chiDN = chiD / chiDNorm`, `|chiDN| ≤ 1`; R179) at scale `M₂ ≥ L` on a chain
vertex `v` of tree `0` other than the pinned terminal node, its time still integrated; in `X^{1/4}` at `L^{47d+2}`
(no `M₂` gain is claimed). The other filters, star weights and dagger are as in `ProtBoundAt`, except `v ∉ F` (R182,
finding F-D3-Sel-1: the selected filter replaces `F`'s filter at `v`; the D5 gates take two filter layers).
Consumed by D6b (`ProtAnnBoundAt` with `pin = true` and a selection: D6a's pointwise bound and `FoldInterpolation`). -/
def ProtBoundSelAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ (w : ℕ) (LG : LayeredGarden w) (X : RegChain),
  ProtShape p X LG → protSize X LG = 2 * n → X.lonePath ≠ [] → ProtAmbient p X LG →
  ∀ (v : GBranch LG.garden.tree), v.1.1.val = 0 → v.1.2 <+: X.lonePath → v.1.2 ≠ X.lonePath →
    v.1.2 ≠ X.lonePath.dropLast →
  ∀ (M₂ : ℝ), P.L ≤ M₂ → ∀ (s : ℝ), (p : ℝ) < s → s < p + 1 → ∀ q' : ℕ, q' ≤ p →
  ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
  ∀ (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) → v ∉ F →
  ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
  ∀ (ind : (GNode LG.garden.tree → Mom P.d) → ℝ), TermChildIndicator X ind →
  ∀ (H : LeafProfiles w P.d) (B : (Fin w × TTree.Path) → NNReal), LeafwiseControlled LG H B →
  ∀ (b₀ c₀ : Mom P.d),
    XNormRestr (1 / 4) (30 * P.d) 0 (timeBoxGt p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ *
          ((Flower.MkDefs.chiDN (|omegaNode LG.garden κ v| / M₂) : ℝ) : ℂ) * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s s (ts 0)) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (47 * P.d + 2)) * regBound P n (protIncoh X LG) *
        ENNReal.ofReal (leafSizeProduct LG B)

def ProtBoundSelGate : Prop := WTPrefix ProtBoundSelAt

/-! ## §5 Whole protected objects with selections (D6 PROT-WHOLE) and wholly regular components (F-4) -/

/-- **D6 export** (R172: on a canonical ambient, `ProtAmbient`) (o82 Thm 18.2 / o73 (17.3)): a protected object with `a = #Sel` selected annular occurrences on its
chain (times still integrated, factor `chiD(|Ω|/M₂)`; at most one, ruling R178, finding F-D6a-1: adjacent linked
selected vertices cancel phases and give one `1/|ω|`, not two) and `b₀ ∈ {0,1}` terminal pin, `r = b₀ + a ≥ 1`, upper filters
elsewhere: the whole signed face collection (= the original annular kernel) gains `M₂^{-a/18}` at cost
`L^{(47d+5)r}`, with every incoherency unit retained. For a paired tree (`w = 1`) the port box is the
native one: the lone node lies in layer `q'` (ruling R183, finding F-D6b-4; D5's form). -/
def ProtAnnBoundAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ (w : ℕ) (LG : LayeredGarden w) (X : RegChain),
  ProtShape p X LG → protSize X LG = 2 * n →
  ∀ (pin : Bool) (Sel : Finset (GBranch LG.garden.tree)), (pin = true → X.lonePath ≠ []) →
    (∀ b ∈ Sel, b.1.1.val = 0 ∧ b.1.2 <+: X.lonePath ∧ b.1.2 ≠ X.lonePath ∧
      (pin = true → b.1.2 ≠ X.lonePath.dropLast)) →
    1 ≤ (if pin then 1 else 0) + Sel.card → Sel.card ≤ 1 → ProtAmbient p X LG →
  ∀ (M₂ : ℝ), P.L ≤ M₂ → ∀ (s : ℝ), (p : ℝ) < s → s < p + 1 → ∀ q' : ℕ, q' ≤ p →
    (w = 1 → ∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') →
  ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
  ∀ (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) →
  ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
  ∀ (ind : (GNode LG.garden.tree → Mom P.d) → ℝ), TermChildIndicator X ind →
    (pin = false → ∀ κ, ind κ = 1) →
  ∀ (H : LeafProfiles w P.d) (B : (Fin w × TTree.Path) → NNReal), LeafwiseControlled LG H B →
  ∀ (b₀ c₀ : Mom P.d),
    XNormRestr P.η (30 * P.d) 0 (timeBoxGt p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ *
          filtWeight (F ∪ Sel) (fun b => decide (b ∈ Sel)) (fun b => if b ∈ Sel then M₂ else M b) κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) ((if pin then ProtCfg.term else ProtCfg.none).fix X s s (ts 0)) k
        (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) *
        ENNReal.ofReal (P.L ^ ((47 * P.d + 5) * ((if pin then 1 else 0) + Sel.card : ℕ)) *
          M₂ ^ (-((Sel.card : ℝ) / 18))) *
        regBound P n (protIncoh X LG) * ENNReal.ofReal (leafSizeProduct LG B)

def ProtAnnBoundGate : Prop := WTPrefix ProtAnnBoundAt

/-- **F-4, pointwise per garden (`RegularComponentPointwiseAt`; R172: on a canonical ambient)** (o82 §19: in a wholly regular capped component the output is fixed, so the
fixed-output bound suffices): a cap couple whose near tree is a whole original tree, at fixed `(t, s, k')`, with any
valid configuration (and optional selections): the pointwise corollary of `ProtBoundAt`/`ProtAnnBoundAt`
(`|F(t,s)| ≤ ‖F‖_{X^{θ,0,0}}`). -/
def RegularComponentPointwiseAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ (LG : LayeredGarden 2) (X : RegChain),
  ProtShape p X LG → protSize X LG = 2 * n →
  ∀ (cfg : ProtCfg), cfg.Valid X LG p → ∀ (Sel : Finset (GBranch LG.garden.tree)),
    (∀ b ∈ Sel, b.1.1.val = 0 ∧ b.1.2 <+: X.lonePath ∧ b.1.2 ≠ X.lonePath ∧
      cfg.fix X 0 0 0 b = none) →
    (Sel.Nonempty → cfg = .none ∨ cfg = .term) → ProtAmbient p X LG →
  ∀ (M₂ : ℝ), P.L ≤ M₂ → ∀ (s t : ℝ), (p : ℝ) < s → s < t → t < p + 1 →
  ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
  ∀ (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) →
  ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
  ∀ (ind : (GNode LG.garden.tree → Mom P.d) → ℝ), TermChildIndicator X ind →
    ((cfg = .none ∨ cfg = .root ∨ cfg = .trace) → ∀ κ, ind κ = 1) →
  ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
  ∀ k' : Mom P.d,
    ‖kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ *
          filtWeight (F ∪ Sel) (fun b => decide (b ∈ Sel)) (fun b => if b ∈ Sel then M₂ else M b) κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => t) s (cfg.fix X s t t) k' (fun _ => 0) 0‖ₑ ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) *
        ENNReal.ofReal (P.L ^ ((47 * P.d + 6) * (2 + Sel.card : ℕ)) * M₂ ^ (-((Sel.card : ℝ) / 18))) *
        regBound P n (protIncoh X LG) * ENNReal.ofReal (leafSizeProduct LG B)

/-! ## §6 The protected-amplitude interface (for B0 / B3b) -/

/-- A **protected slot** of a Stage-1′ piece: the native-clock function of a protected regular object (an exterior
slot of `G_sb`, never regional), its time box, local output set, weight `θ` and mass. -/
structure ProtSlot (d : ℕ) where
  θ : ℝ
  box : Set (Fin 2 → ℝ)
  out : Set (Mom d)
  F : (Fin 2 → ℝ) → Mom d → ℂ
  mass : ℝ

/-- The interface contract: `θ ≥ η` at a lower slot (U-clock (U.2)), `θ ≥ 1/4` at a slot adjacent to a selected
residual vertex (o73 (20.2)), `θ ≥ 0` (time weight one) otherwise (o73 §16); local output norm bounded by the mass. -/
def ProtSlot.OK {d : ℕ} (σ : ProtSlot d) (η : ℝ) (lower selAdj : Bool) : Prop :=
  0 ≤ σ.θ ∧ (lower = true → η ≤ σ.θ) ∧ (selAdj = true → 1 / 4 ≤ σ.θ) ∧
    XNormRestr σ.θ (30 * d) 0 σ.box σ.out σ.F ≤ ENNReal.ofReal σ.mass

/-- B3b's conversion (main's `Represents.exists_supM` through an extension agreeing on `box × out`): an OK
protected slot is a superposition with normalized amplitudes (`SNorm (30d) 0 ≤ 1`) and moment mass `C · mass`.
Ruling R179 (F-B3s-3): the slot function is continuous in its clocks on the box (a point mass in time has `XNorm` `0`
but is not `0`, while a `SupM` superposition is continuous on the box). -/
def ProtSlotSupM : Prop :=
  ∀ (d : ℕ) (θ : ℝ), 0 ≤ θ → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (σ : ProtSlot d), σ.θ = θ →
    σ.box ⊆ VineEstS3.FS.cell (fun _ => (0 : ℝ)) → σ.box ⊆ closure (interior σ.box) →
    (∀ k ∈ σ.out, ContinuousOn (fun ts => σ.F ts k) σ.box) →
    XNormRestr σ.θ (30 * d) 0 σ.box σ.out σ.F ≤ ENNReal.ofReal σ.mass →
    ∃ G : (Fin 2 → ℝ) → Mom d → ℂ, (∀ ts ∈ σ.box, ∀ k ∈ σ.out, G ts k = σ.F ts k) ∧
      Represents.SupM θ (30 * d) σ.box G (C * ENNReal.ofReal σ.mass)

end WaveTurbulence.Flower.ProtDefs
