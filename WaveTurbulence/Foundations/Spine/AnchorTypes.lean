/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GateTypes
public import WaveTurbulence.Foundations.WaveB.MoleculeStatements
public import WaveTurbulence.Frozen.Defs.SumintDatum
public import WaveTurbulence.Frozen.Defs.SumintDatumAdmissible
public import WaveTurbulence.Frozen.Defs.SumintDatumEllVec
public import WaveTurbulence.Frozen.Defs.SumintDatumExpr
public import WaveTurbulence.Frozen.Defs.SumintDatumKVec
public import WaveTurbulence.Frozen.Defs.SumintDatumM0
public import WaveTurbulence.Frozen.Defs.SumintDatumM1
public import WaveTurbulence.Frozen.Defs.SumintDatumPhase
public import WaveTurbulence.Frozen.Defs.SumintDatumTimeDom
public import WaveTurbulence.Frozen.Defs.SumintShape
public import WaveTurbulence.Frozen.Defs.SumintShapeLexLt
public import WaveTurbulence.Frozen.Defs.SumintShapeM
public import WaveTurbulence.Frozen.Defs.SumintShapeN
public import WaveTurbulence.Frozen.Defs.SumintShapeTVar
public import WaveTurbulence.Frozen.Defs.SumintShapeUSlot
public import WaveTurbulence.Frozen.Defs.SumintShapeVIdx
public import WaveTurbulence.Frozen.Defs.SumintShapeX0Slot
public import WaveTurbulence.Frozen.Defs.SumintShapeXSlot
public import WaveTurbulence.Frozen.Defs.SumintShapeYSlot
public import WaveTurbulence.Foundations.WaveB.FrozenB1
/-! Exact source-anchor proposition aliases for the LG dependency map. No draft theorem is imported.
These aliases are available for source checking; redundant upstream inputs are not automatically part of the minimal spine. -/
@[expose] public section
open WaveTurbulence.Induct
namespace WaveTurbulence.LGSpine
open MeasureTheory Finset Set
open scoped Classical ENNReal

/-- TARGET L761–779; snapshot-7 B1.2. Literal snapshot proposition. -/
abbrev LayergardenGate : Prop := Induct.LayergardenGate

/-- TARGET L1145–1232; B2.1. Literal snapshot proposition. -/
abbrev RegularAsymptoticsGate : Prop := WTPrefix fun P =>
    ∀ p : ℕ, p < P.D → ∀ r : ℕ, r ≤ p → ∀ R : Mom P.d → ℝ, InputRemainder P R r →
    ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
      let F : Mom P.d → ℝ := fun k => P.φ (P.δ * r) k + R k
      -- (1) regular couples
      (∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ a, LG.layer a = r) →
        XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox r r) Set.univ
          (fun ts k => KQstar P.L P.γ P.δ (fun _ => F) LG (ts 0) (ts 1) k -
            Q.app P.δ r F (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      -- (2) regular trees
      (∀ X : RegChain, X.wf = true → X.size = 2 * n → ∀ LG : LayeredGarden 1,
        X.DecodesTree LG.garden → ∀ q' : ℕ, q' ≤ r →
        (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else r) →
        XNormRestr P.η (30 * P.d) 0 (timeBoxGt r q') Set.univ
          (fun ts k => KTstar P.L P.γ P.δ (fun _ => F) LG (ts 0) (ts 1) k -
            X.app P.δ r F (LG.garden.sig 0) (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      -- (3) the factors
      (∀ Q : RegCpl, Q.wf = true → Q.dominant = true → Q.size = 2 * n →
        XNorm00Restr (V := Unit) (1 - P.η) (timeBox r r) Set.univ
            (fun ts _ => (Q.JB r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
          ∀ Z ∈ specialSets Q.links,
            SNormR (30 * P.d) (30 * P.d) (Q.Mstar F Z (0, []) (1, [])) ≤
              ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
      (∀ X : RegChain, X.wf = true → X.dominant = true → X.size = 2 * n → ∀ ζ : ℤˣ,
        ∀ q' : ℕ, q' ≤ r →
        XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt r q') Set.univ
            (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
          ∀ Z ∈ specialSets (X.treeLinks ζ),
            SNormR (30 * P.d) 0 (X.Nstar F Z ζ (0, [])) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
      -- (4) the WKE identity (corrected regref1-5)
      (r = p → (∀ k, R k = 0) → ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k : Mom P.d,
        ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.dominant = true ∧ Q.size = 2 * n),
            Q.app P.δ p F t t k =
          (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ))

/-- TARGET L953–956; B2.2. Literal snapshot proposition. -/
abbrev IncoherentDecayGate : Prop := WTPrefix fun P =>
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, (∀ q ≤ p, InputRemainder P (R q) q) →
    ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
      -- (1) regular couples
      (∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
        LG.layer (GNode.root LG.garden.tree 0) ≤ q → LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
        1 ≤ LG.incoherency Q.links →
        XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
          (fun ts k => KQstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k) ≤
          regBound P n (LG.incoherency Q.links)) ∧
      -- (2) regular trees
      (∀ X : RegChain, X.wf = true → X.size = 2 * n → ∀ LG : LayeredGarden 1,
        X.DecodesTree LG.garden → (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q' ≤ q → q ≤ p →
        LG.layer (GNode.root LG.garden.tree 0) ≤ q →
        (∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') →
        1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) →
        XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q') Set.univ
          (fun ts k => KTstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k) ≤
          regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0))))

/-- TARGET L2192–2200 / DH23 Prop 9.6; B2.3, F69b disputed. Literal snapshot proposition. -/
abbrev RigidityGate : Prop := WTPrefix fun P =>
    ∀ (V D : Type) [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (lab : V → AtomLabel) (Rw : ℕ) (w : Mom P.d) (kFix : Finset (Mom P.d))
      (prevGaps : V → (D → (Fin P.d → ℤ)) → Set (Mom P.d)) (Pl : Finset V → ℝ)
      (Adm : (D → (Fin P.d → ℤ)) → Prop),
      1 ≤ Rw → kFix.card ≤ 2 * Rw → M.FinalShape lab →
      M.DecorationHyp P.L P.γ P.η w kFix lab prevGaps Pl Adm →
      M.countA P.L P.γ P.δ P.C₁ w Adm Pl ≤ ENNReal.ofReal (M.rigidityRHS P lab Rw)

/-- TARGET L1595–1640; B1.6. Literal snapshot proposition. -/
abbrev SumintGate : Prop := WTPrefixA fun A P =>
    ∀ (D : SumintDatum P.d) (hI : 0 < D.S.I), D.Admissible A P.L P.γ P.η P.D →
      D.S.M ≤ P.N 1 ^ 4 →
      let B : Set (Fin 3 → ℝ) := {tt | (∀ c, (D.qOut c : ℝ) ≤ tt c ∧ tt c ≤ D.qOut c + 1) ∧
        max (tt 1) (tt 2) < tt 0}
      let K : Set (Fin 4 → Mom P.d) := {v | (∀ c, (∃ nv : Fin P.d → ℤ, v c = D.wBar +
          latticePoint P.L nv) ∧ ‖v c - D.centre c‖ ≤ 1) ∧ v 0 - v 1 = v 3 - v 2 ∧ v 0 ≠ v 1 ∧
        ‖v 0 - v 1‖ ≤ P.L ^ (-P.γ + P.η)}
      let maxPar : ℝ := ⨆ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D.param v)
      XNorm00Restr (2 * P.η ^ 8) B K (fun tt v => D.expr hI P.L P.γ P.δ P.η tt v) ≤
        ENNReal.ofReal (P.C₁ * maxPar ^ (P.η ^ 6) * (P.C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M *
          P.L ^ ((D.S.M : ℝ) * (P.d - P.γ) -
            P.η ^ 2 * ((Finset.univ.filter fun i => D.S.nor i = false).card + D.M₁) -
            P.η ^ 8 * D.M₀ + P.η ^ 7))

/-- TARGET Lemma A.8; B1.7. Literal snapshot proposition. -/
abbrev CountLemmaGate : Prop := ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Ioc 0 η₀,
    ∀ c₀ : ℝ, 1 ≤ c₀ → ∃ C : ℝ, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ α β : ℝ,
    ∀ (nr nv : Fin d → ℤ) (Pr : ℝ), (Pr = 0 ∨ Pr ∈ Icc L⁻¹ 1) →
      (Pr = 0 → nr = 0) →
      (0 < Pr → Pr < 1 → c₀⁻¹ * Pr ≤ ‖latticePoint L nr‖ ∧ ‖latticePoint L nr‖ ≤ c₀ * Pr) →
      (Pr = 1 → c₀⁻¹ ≤ ‖latticePoint L nr‖ ∧ ‖latticePoint L nr‖ ≤ c₀) →
    ∀ ax ay az : Mom d, ∀ ξsel : Fin 3, ∀ ζsel : Fin 3,
      let r := latticePoint L nr
      let v := latticePoint L nv
      let 𝔛 := min (Real.log L ^ 2) (1 + δ * L ^ (2 * γ) * Pr)
      let tol := δ⁻¹ * L ^ (-2 * γ)
      let S₁ : Set ((Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L ax q.1 ∧ NearLattice L ay q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2) - α| ≤ tol ∧
        |inner ℝ r (![latticePoint L q.1, latticePoint L q.2,
            latticePoint L q.1 + latticePoint L q.2] ξsel) - β| ≤ tol}
      let S₂ : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L ax q.1 ∧
        NearLattice L ay q.2.1 ∧ NearLattice L az q.2.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2.1) - α| ≤ tol ∧
        |inner ℝ (![latticePoint L q.1 - v, latticePoint L q.1 + latticePoint L q.2.1 - v,
            latticePoint L q.1 + latticePoint L q.2.1 - v - latticePoint L q.2.2] ζsel)
          (latticePoint L q.2.2) - β| ≤ tol}
      (S₁.Finite ∧ (S₁.ncard : ℝ) ≤ C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) * 𝔛⁻¹) ∧
      (S₂.Finite ∧ (S₂.ncard : ℝ) ≤
        C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ)))

/-- TARGET Lemma A.9; B1.8. Literal snapshot proposition. -/
abbrev AtomCountLemmaGate : Prop := ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η → η ≤ min γ (1 - γ) / 2 →
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ β : ℝ, ∀ nk : Fin d → ℤ, ∀ a₁ a₂ a₃ : Mom d,
      let k := latticePoint L nk
      let tol := δ⁻¹ * L ^ (-2 * γ)
      let S₂ (ε : ℤˣ) : Set ((Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L a₁ q.1 ∧
        NearLattice L a₂ q.2 ∧ q.1 + (ε : ℤ) • q.2 = nk ∧
        |‖latticePoint L q.1‖ ^ 2 + (ε : ℤ) * ‖latticePoint L q.2‖ ^ 2 - β| ≤ tol}
      let S₃ : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L a₁ q.1 ∧
        NearLattice L a₂ q.2.1 ∧ NearLattice L a₃ q.2.2 ∧ q.1 - q.2.1 + q.2.2 = nk ∧
        |‖latticePoint L q.1‖ ^ 2 - ‖latticePoint L q.2.1‖ ^ 2 + ‖latticePoint L q.2.2‖ ^ 2 - β| ≤
          tol}
      (∀ ε : ℤˣ, (S₂ ε).Finite) ∧
      (∀ ε : ℤˣ, (ε = -1 → nk ≠ 0) →
        ((S₂ ε).ncard : ℝ) ≤ C * δ⁻¹ * min (L ^ d) (L ^ ((d : ℝ) + 1 - 2 * γ))) ∧
      (L ^ (-γ + η) ≤ ‖k‖ → ((S₂ (-1)).ncard : ℝ) ≤ C * δ⁻¹ * L ^ ((d : ℝ) - γ - η)) ∧
      (S₃.Finite ∧ (S₃.ncard : ℝ) ≤ C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)))

/-- TARGET L970–977 / DH23 Lemma 6.6(2); B1.9. Literal snapshot proposition. -/
abbrev QuadExpSum2Gate : Prop := ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η → ∀ T₀ : ℝ, 0 < T₀ →
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ a b ξ ξ' : Mom d,
      ∫ s in {s : ℝ | L ≤ |s| ∧ |s| ≤ T₀ * L ^ (2 * γ)},
          ‖∑' q : (Fin d → ℤ) × (Fin d → ℤ),
            ((chi0Vec (latticePoint L q.1 - a) * chi0Vec (latticePoint L q.2 - b) : ℝ) : ℂ) *
              eZ (inner ℝ (latticePoint L q.1) ξ + inner ℝ (latticePoint L q.2) ξ' +
                s * inner ℝ (latticePoint L q.1) (latticePoint L q.2))‖ ≤
        C * L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η)

/-- TARGET L1554–1593; B1.10. Literal snapshot proposition. -/
abbrev QuadExpSum3Gate : Prop := ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ T₀ : ℝ, 0 < T₀ →
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ Λsel : Bool, ∀ a b c ξ ξ' ξ'' : Mom d,
      let Λf : Mom d → Mom d → Mom d → ℝ := fun x y z =>
        if Λsel then inner ℝ x z else inner ℝ z (x + y - z)
      ∫ ts in {ts : ℝ × ℝ | L ≤ max |ts.1| |ts.2| ∧ |ts.1| ≤ T₀ * L ^ (2 * γ) ∧
          |ts.2| ≤ T₀ * L ^ (2 * γ)},
          ‖∑' q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ),
            ((chi0Vec (latticePoint L q.1 - a) * chi0Vec (latticePoint L q.2.1 - b) *
                chi0Vec (latticePoint L q.2.2 - c) : ℝ) : ℂ) *
              eZ (ts.1 * inner ℝ (latticePoint L q.1) (latticePoint L q.2.1) +
                ts.2 * Λf (latticePoint L q.1) (latticePoint L q.2.1) (latticePoint L q.2.2) +
                inner ℝ ξ (latticePoint L q.1) + inner ℝ ξ' (latticePoint L q.2.1) +
                inner ℝ ξ'' (latticePoint L q.2.2))‖ ≤
        C * L ^ (3 * (d : ℝ) + γ - 2 * min γ (1 - γ)) * Real.log L

/-- TARGET L2259–2335; snapshot-7 B1.12 (downstream of layergarden). Literal snapshot proposition. -/
abbrev LayergardenFlowerGate : Prop := WTPrefixP fun Pm P =>
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
      ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
        (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
        (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
        ‖flowerSum P (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n'‖ ≤
          jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^
              (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
            P.L ^ ((if ∀ j, pat j = .plain then 1 else 2) * (100 * P.d : ℝ) ^ 3 * Pm) *
            P.δ ^ (2 * P.ν * N) *
            (cut1.elim 1 fun j₁ => ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ))) *
            (cut2.elim 1 fun j₂ =>
              if ∀ j, pat j = .plain then ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) else 1)) ∧
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ k : Mom P.d, ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : TreeKind)
        (dt : Bool), (kind = .tr → dt = true) →
        ‖coupleSum P (inputsF P R) p N kind dt t k‖ ≤
          jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * N))

end WaveTurbulence.LGSpine
