/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.TermNat3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AmbEng
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatCert
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.FlatBase

/-! # P4-W2 (session 12, step 1d): `termCertW_nat`, the certificate of a term with no exceptional record

For a term `ψ0` of the level `lv` with the native row form `RowFormNE .. ∅ ∅` (the `QNE` witness with `recs = []`), the modulated term `modPsi b λ ψ0`
carries `TermCertW` at every size `β' ≥ certBeta ..` (`traceConst² · pre · ∏ C·2 rowBoundH`), with the uniform row constant `C` (depending on `d, η` only).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B
open scoped ENNReal

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem termCertW_nat {A : ℝ} (d : ℕ) (η : ℝ) (hd : 1 ≤ d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (P : WTParams), P.d = d → P.η = η → ∀ (Z0 : AmbP A P) (hA : 6561 ≤ A)
      (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (hC1 : 1 ≤ P.C₁) (hL1 : 1 ≤ P.L)
      (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
      (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
      (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (lv : Lvl B) {n' : ℕ} (B' : CLChainAssembly G lv.region n')
      (RD : ReconstructionData G) (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
      (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (hl1 : clLocalOrder1 lv.region ≤ P.N 1 ^ 4)
      (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ)
      (hcoh : RowCoherent hM9 B' RD hG layer hLayer
        (step3W hM9 B' RD hG layer hLayer (canonBadKind hM9 B' RD hG layer) (qOutOf RD hG layer lv.c.a lv.c.b lv.region) centre wBar)
        P.L P.γ P.δ h p)
      (ψ0 : PsiT G P.d) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop)
      (Xq : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin P.d → ℤ)) → ℂ)
      (hNE : RowFormNE RD hG P.L P.γ P.δ h layer hLayer lv.region wBar ψ0 Dm ∅ ∅ Xq)
      (hDm : ∀ t u, u lv.c.a = t 0 → (Dm t u ↔ ClDom lv.region (fun v => layer (RD.coreBranch hG v).toNode) t u))
      (hfree : ∀ i : Fin n', (assemblyPieceAt B' i).vineType.IsBad = true → ¬ AClause hM9 B' RD hG layer i →
        ∃ v : (assemblyShape hM9 B').VIdx, v.1 = i ∧
          1 ≤ max (rowCoupleG hM9 B' RD hG layer hLayer v) (rowTreeG hM9 B' RD hG layer hLayer v))
      (Bx : Set (Fin 3 → ℝ)) (K : Set (Fin 4 → Mom P.d))
      (hBx : Bx ⊆ WaveTurbulence.VineEstS3Par.Eng.outBox
        (natEng hM9 B' RD hG layer hLayer (qOutOf RD hG layer lv.c.a lv.c.b lv.region) centre wBar lam))
      (hK : K = WaveTurbulence.VineEstS3Par.Eng.outSet
        (natEng hM9 B' RD hG layer hLayer (qOutOf RD hG layer lv.c.a lv.c.b lv.region) centre wBar lam) P.L P.γ P.η)
      (β' : ℝ≥0∞),
      certBeta P (natEng hM9 B' RD hG layer hLayer (qOutOf RD hG layer lv.c.a lv.c.b lv.region) centre wBar lam)
          ((3 : ℝ) ^ (clLocalOrder1 lv.region + 1))
          (fun ρ => C * ENNReal.ofReal (2 * rowBoundH hM9 B' RD hG layer hLayer P Bh
            (termW hM9 B' RD hG layer hLayer (canonBadKind hM9 B' RD hG layer) (qOutOf RD hG layer lv.c.a lv.c.b lv.region) centre wBar lam) ρ)) ≤ β' →
        TermCertW (A := A) B hG (kparOf P.L P.γ P.δ h wBar) lv (modPsi lv.c.b lam ψ0) Bx K β' := by
  classical
  obtain ⟨C, hC0, hall⟩ := natRows_family d η hd
  refine ⟨C, hC0, fun P hPd hPη Z0 hA hgate hinc hC1 hL1 hw {p} hp {h} {Bh} hB hBpos hM9 B lv {n'} B' RD hG layer hLayer hlay hord hl1
    centre wBar lam hcoh ψ0 Dm Xq hNE hDm hfree Bx K hBx hK β' hβ' => ?_⟩
  have hd' : 1 ≤ P.d := hPd ▸ hd
  have hL0 : 0 < P.L := by linarith
  set qOut := qOutOf RD hG layer lv.c.a lv.c.b lv.region with hqOut
  set bk := canonBadKind hM9 B' RD hG layer with hbk
  set W := termW hM9 B' RD hG layer hLayer bk qOut centre wBar lam with hW
  set wN := 30 * P.d - 1 with hwNd
  set wDec := 30 * P.d with hwDecd
  set cons := consX hM9 B' (fun v => layer (RD.coreBranch hG v).toNode) ∅ ∅ with hcons
  set g := rowCoupleG hM9 B' RD hG layer hLayer with hg
  set g' := rowTreeG hM9 B' RD hG layer hLayer with hg'
  have hI := assemblyShape_I_pos hM9 B'
  -- eligibility of the native rows
  have hel : ∀ v, CoupleEligible hM9 B' RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v ∧
      TreeEligible hM9 B' RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v := fun v =>
    eligible_of hM9 B' RD hG layer hLayer W rfl rfl P.L P.γ P.δ h (P.N (p + 1) ^ 4) p hlay
      (rowSizes_of_order hM9 B' RD hG hord) hcoh v
  have hqq : ∀ v, (rowQ hM9 B' RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 ≤
      (rowQ hM9 B' RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1 := fun v => (hel v).2.1
  have hη6 : 6 * P.η ^ 6 ≤ P.η := Z0.hθη
  obtain ⟨Rw, hRW, hRS, hRb, hAe, hWs⟩ := hall P hPd hPη hgate hinc hη6 Z0.hη1 hC1 Z0.hδ hL1 hw hp hB hBpos hM9 B' RD hG layer hLayer hlay W
    hel hqq wN wDec (by omega) (by omega) bk cons g g'
  obtain ⟨Mx, hmass, hMx⟩ := exists_mix_native hM9 B' hG W hL0.ne' wBar
  have hq : ∀ v, W.q v + 1 ≤ P.D := fun v => Nat.succ_le_of_lt (lt_of_le_of_lt (hlay _) hp)
  have hqo : ∀ c, W.qOut c + 1 ≤ P.D := by
    intro c
    refine Nat.succ_le_of_lt (lt_of_le_of_lt ?_ hp)
    fin_cases c <;> simp only [W, termW, step3W, hqOut, qOutOf] <;> exact hlay _
  have hS := structAdm_engDatum hM9 B' hG W (L := P.L) (γ := P.γ) (η := P.η) hA hq hqo wN wDec (by omega) (by omega) bk cons g g'
  have hbad := badClauseP_native hM9 B' RD hG layer hLayer W wN wDec hfree
  have hgap : ∀ i (hh : (engDatum hM9 B' hG W wN wDec bk cons g g').S.nor i = false ∧
      (engDatum hM9 B' hG W wN wDec bk cons g g').badKind i = 2 ∧ 0 < (engDatum hM9 B' hG W wN wDec bk cons g g').S.m i),
      |(((engDatum hM9 B' hG W wN wDec bk cons g g').q (.inl ⟨i, ⟨1, by omega⟩⟩) : ℕ) : ℝ) -
        (((engDatum hM9 B' hG W wN wDec bk cons g g').q (.inr (.inl ⟨i, ⟨0, hh.2.2⟩⟩)) : ℕ) : ℝ)| ≤ 0 := by
    intro i hh
    exfalso
    have h2 : bk i = 2 := hh.2.1
    rcases canonBadKind_cases hM9 B' RD hG layer i with h' | h' <;> rw [hbk, h'] at h2 <;> exact absurd h2 (by decide)
  let Z := ambW_engDatum Z0 hM9 B' hG W wN wDec bk cons g g' hS hbad Mx 0 le_rfl hgap (by omega)
    (by rw [assemblyShape_M]; exact hl1)
  have hleafmem : ∀ tt ∈ Bx, WaveTurbulence.VineEstS3.leafT qOut (LeafPos B lv) (LeafNeg B lv) tt ∈
      WaveTurbulence.VineEstS3.Eng.outBox (sourceSumintDatum hM9 B' hG W) := fun tt htt =>
    leafT_mem_boxQ qOut _ _ (hBx htt)
  have hind' : ∀ (t : Fin 3 → ℝ) (β'' : Fin 4 → Mom P.d) (κ : CLLocalDecoration lv.region P.L W.wBar β'') (u : GBranch G.tree → ℝ),
      u lv.c.a = t 0 → modPsi lv.c.b lam ψ0 (clExtendIndices lv.region κ.1) t u = modPsi lv.c.b lam ψ0 (clExtendIndices lv.region κ.1)
        (WaveTurbulence.VineEstS3.leafT qOut (LeafPos B lv) (LeafNeg B lv) t) u := by
    intro t β'' κ u hu
    show Complex.exp _ * ψ0 _ t u = Complex.exp _ * ψ0 _ _ u
    congr 1
    refine hind_native RD hG P.L P.γ P.δ h layer hLayer wBar ψ0 Dm Xq hNE hDm t _
      (WaveTurbulence.VineEstS3.leafT_zero qOut _ _ t).symm ?_ ?_ β'' κ u hu
    · by_cases hh : LeafPos B lv
      · exact Or.inl hh
      · exact Or.inr (by rw [WaveTurbulence.VineEstS3.leafT_one]; simp [hh])
    · by_cases hh : LeafNeg B lv
      · exact Or.inl hh
      · exact Or.inr (by rw [WaveTurbulence.VineEstS3.leafT_two]; simp [hh])
  have hbk' : ∀ i, bk i ≠ 1 ∧ bk i ≠ 2 := fun i => by
    rcases canonBadKind_cases hM9 B' RD hG layer i with h' | h' <;> rw [hbk, h'] <;> decide
  have hD : ∀ tt ∈ Bx, ∀ (β : Fin 4 → (Fin P.d → ℤ))
      (hβ : ((G.sign lv.c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)) ∈
        outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η →
      FreeDict hM9 B' hG W hL0.ne' P.γ P.δ P.η W.wBar β hβ
        (WaveTurbulence.VineEstS3.leafT qOut (LeafPos B lv) (LeafNeg B lv) tt)
        (modPsi lv.c.b lam ψ0) wN wDec bk cons g g' Mx (allCR Rw) := by
    intro tt htt β hβ _
    refine freeDict_native_NE hM9 B' RD hG W hL0.ne' P.γ P.δ P.η h layer hLayer wBar β hβ _ (hleafmem tt htt)
      (modPsi lv.c.b lam ψ0) ψ0 lam (fun x t u => rfl) Dm Xq hNE hDm wN wDec bk g g' Rw hRW hRS Mx (fun v => rfl)
      (fun x => hMx β hβ x) rfl (step3W_ok hM9 B' RD hG layer hLayer bk qOut centre wBar) rfl hbk' ?_ ?_
    · by_cases hh : LeafPos B lv
      · refine Or.inr ?_
        rw [WaveTurbulence.VineEstS3.leafT_one]
        simp only [hh, if_true]
        exact qOutOf_one_le hM9 B' RD hG layer hLayer hI
      · exact Or.inl (by simpa [LeafPos] using hh)
    · by_cases hh : LeafNeg B lv
      · refine Or.inr ?_
        rw [WaveTurbulence.VineEstS3.leafT_two]
        simp only [hh, if_true]
        exact qOutOf_two_le hM9 B' RD hG layer hLayer hI
      · exact Or.inl (by simpa [LeafNeg] using hh)
  have hβfinal : Regref.traceConst (r := 3) (2 * P.η ^ 8) WaveTurbulence.VineEstS3.chiUnit ^ 2 *
      (Z.pre * ∏ ρ, (Rw ρ).b) ≤ β' := by
    refine le_trans (certBeta_mono P (engDatum hM9 B' hG W wN wDec bk cons g g') Mx.mass
      (Rb := fun ρ => (Rw ρ).b)
      (Rb' := fun ρ => C * ENNReal.ofReal (2 * rowBoundH hM9 B' RD hG layer hLayer P Bh W ρ)) hRb) ?_
    rw [hmass]
    exact hβ'
  exact ⟨n', hM9, B', W, wN, wDec, bk, cons, g, g', Z, Rw, hL0.ne', hAe, hWs, rfl, hBx, hK, hind', hD, hβfinal⟩

end WaveTurbulence.VineEstS5C.P4.W2
