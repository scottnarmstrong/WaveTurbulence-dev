/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Damaged
public import WaveTurbulence.Foundations.FinalCount.Damaged96
public import WaveTurbulence.Foundations.FinalCount.G3MapDec
public import WaveTurbulence.Foundations.FinalCount.Final96c
/-! **FINALCOUNT-ASSEMBLY: G8's `prop96` and `prop96_damaged` (quantifier order of R34: `Cstar` before `m`) in G3's shapes.**
G3's `damaged_component_bound` quantifies `m` BEFORE `Cstar` (it was compiled against the pre-QUANT G8 `buildD`); it is NOT used here.
The field-wise conversions `FinalShape.toG8`, `FinalDec.toG8` are new (copies of G3's `DamagedShape.toG8` pattern); the damaged ones are
reused from G3Prop96Dam (they do not mention `m`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3


/-- The class map into G8's `Cls` (copy of G3Prop96Dam's, to avoid importing the stale-compiled module). -/
def g8Cls : G8Copy.Cls → WaveTurbulence.FinalCountG8.Cls
  | .eps => .eps
  | .alpha R κ => .alpha R κ
  | .beta => .beta

theorem g8Cls_isEps {c : G8Copy.Cls} : (g8Cls c).IsEps ↔ c.IsEps := by
  cases c <;> simp [g8Cls, G8Copy.Cls.IsEps, WaveTurbulence.FinalCountG8.Cls.IsEps]
theorem g8Cls_isAlpha {c : G8Copy.Cls} : (g8Cls c).IsAlpha ↔ c.IsAlpha := by
  cases c <;> simp [g8Cls, G8Copy.Cls.IsAlpha, WaveTurbulence.FinalCountG8.Cls.IsAlpha]
theorem g8Cls_lab (c : G8Copy.Cls) : (g8Cls c).lab = c.lab := by
  cases c <;> simp [g8Cls, G8Copy.Cls.lab, WaveTurbulence.FinalCountG8.Cls.lab]

theorem g8Cls_isBeta {c : G8Copy.Cls} : (g8Cls c).IsBeta ↔ c.IsBeta := by
  cases c <;> simp [g8Cls, G8Copy.Cls.IsBeta, WaveTurbulence.FinalCountG8.Cls.IsBeta]
theorem g8Cls_kap (c : G8Copy.Cls) : (g8Cls c).kap = c.kap := by
  cases c <;> simp [g8Cls, G8Copy.Cls.kap, WaveTurbulence.FinalCountG8.Cls.kap]

section transfer
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} {cls : V → G8Copy.Cls}

theorem alphaAtoms_g8 (atoms : Finset V) (cls : V → G8Copy.Cls) :
    WaveTurbulence.FinalCountG8.alphaAtoms atoms (fun a => g8Cls (cls a)) = G8Copy.alphaAtoms atoms cls := by
  unfold WaveTurbulence.FinalCountG8.alphaAtoms G8Copy.alphaAtoms
  ext v; simp [Finset.mem_filter, g8Cls_isAlpha]

theorem IsChainSet_g8 {K : Finset V} (h : WaveTurbulence.FinalCountG8.IsChainSet M (fun a => g8Cls (cls a)) K) :
    G8Copy.IsChainSet M cls K := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, fun v hv => fun he => h3 v hv (g8Cls_isEps.2 he), fun u hu v huv hv => h4 u hu v huv
    (fun he => hv (g8Cls_isEps.1 he)), h5⟩

theorem G8Copy.FinalShape.toG8 {odd : Prop} (h : G8Copy.FinalShape M cls odd) :
    WaveTurbulence.FinalCountG8.FinalShape M (fun a => g8Cls (cls a)) odd where
  nonempty := h.nonempty
  caps := h.caps
  noLoop := h.noLoop
  conn := h.conn
  degPos := h.degPos
  classes := fun a ha => by rw [g8Cls_isEps]; exact h.classes a ha
  dir2 := h.dir2
  oddDeg := h.oddDeg
  evenDeg := h.evenDeg
  noTriple := h.noTriple
  evenBeta := fun hn => by
    obtain ⟨a, ha, hb⟩ := h.evenBeta hn
    exact ⟨a, ha, g8Cls_isBeta.2 hb⟩
  cycle := fun hc => by
    have := h.cycle hc
    rwa [alphaAtoms_g8]
  chains := fun hn hnc K hK => by
    obtain ⟨y₁, y₂, h1, h2, h3, h4, h5⟩ := h.chains hn hnc K (IsChainSet_g8 hK)
    exact ⟨y₁, y₂, h1, h2, g8Cls_isEps.2 h3, g8Cls_isEps.2 h4, h5⟩

theorem G8Copy.FinalDec.toG8 {d : ℕ} {L γ η : ℝ} {Adm : (D → (Fin d → ℤ)) → Prop}
    (h : G8Copy.FinalDec M cls L γ η Adm) :
    WaveTurbulence.FinalCountG8.FinalDec M (fun a => g8Cls (cls a)) L γ η Adm where
  labRange := fun a ha hα => by rw [g8Cls_lab]; exact h.labRange a ha (g8Cls_isAlpha.1 hα)
  kapVals := fun a ha hα => by rw [g8Cls_kap]; exact h.kapVals a ha (g8Cls_isAlpha.1 hα)
  epsLG := fun κ hκ a ha he => h.epsLG κ hκ a ha (g8Cls_isEps.1 he)
  alphaGap := fun κ hκ a ha hα x y hx hy hxy => by
    rw [g8Cls_lab]; exact h.alphaGap κ hκ a ha (g8Cls_isAlpha.1 hα) x y hx hy hxy
  alphaSG := fun κ hκ a ha hα => h.alphaSG κ hκ a ha (g8Cls_isAlpha.1 hα)
  betaGap := fun κ hκ a ha hb => h.betaGap κ hκ a ha (g8Cls_isBeta.1 hb)
  vineLG := h.vineLG
  noBetaCut := h.noBetaCut
  iota := fun κ hκ v₁ h1 v₂ h2 v₃ h3 hne hα1 hα2 hβ3 hk x₁ y₁ x₂ y₂ x₃ y₃ hx1 hy1 hxy1 hx2 hy2 hxy2 hx3 hy3 hxy3 g1 g2 g3 hs => by
    have := h.iota κ hκ v₁ h1 v₂ h2 v₃ h3 hne (g8Cls_isAlpha.1 hα1) (g8Cls_isAlpha.1 hα2) (g8Cls_isBeta.1 hβ3)
      (by rw [← g8Cls_kap, ← g8Cls_kap] at *; exact hk) x₁ y₁ x₂ y₂ x₃ y₃ hx1 hy1 hxy1 hx2 hy2 hxy2 hx3 hy3 hxy3 g1 g2 g3 hs
    rwa [g8Cls_lab, g8Cls_lab] 


theorem G8Copy.DamagedShape.toG8 (h : G8Copy.DamagedShape M cls) :
    WaveTurbulence.FinalCountG8.DamagedShape M (fun a => g8Cls (cls a)) where
  nonempty := h.nonempty
  isMolecule := h.isMolecule
  noLoop := h.noLoop
  conn := h.conn
  degPos := h.degPos
  abLow := fun a ha hne => h.abLow a ha (fun he => hne (g8Cls_isEps.2 he))
  noTriple := h.noTriple
  imperf := by
    obtain ⟨a, ha, hh⟩ := h.imperf
    exact ⟨a, ha, by simpa only [g8Cls_isEps] using hh⟩

theorem G8Copy.DamagedDec.toG8 {d : ℕ} {L γ η : ℝ} {Adm : (D → (Fin d → ℤ)) → Prop}
    (h : G8Copy.DamagedDec M cls L γ η Adm) :
    WaveTurbulence.FinalCountG8.DamagedDec M (fun a => g8Cls (cls a)) L γ η Adm where
  labRange := fun a ha hα => by
    rw [g8Cls_lab]; exact h.labRange a ha (g8Cls_isAlpha.1 hα)
  epsLG := fun κ hκ a ha he x y hx hy hxy => h.epsLG κ hκ a ha (g8Cls_isEps.1 he) x y hx hy hxy

end transfer

end WaveTurbulence.FinalCountAsm
