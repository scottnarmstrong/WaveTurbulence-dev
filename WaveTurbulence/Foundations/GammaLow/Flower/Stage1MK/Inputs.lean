/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.TVine.Struct.Statement
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.Main
public import WaveTurbulence.Foundations.TVine.Struct.Final
public import WaveTurbulence.Foundations.TVine.Struct.SubObjBridge
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.TVine.Chart.Contract
public import WaveTurbulence.Foundations.TVine.Chart.Unconditional
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstGamma
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts

/-! # FLOWER-LOW (packet L8), item I: the inputs of the marked Stage 1′ over `𝒱_γ`

Theorem 7.5′-low (M3 §5) uses the T-vine facts TV1–TV7 (M3 §2) and, for Stage 1′'s analytic part, the vine estimate
for chains containing T-vines (VE-low). Each input is bound to its producer's published statement, at universe `0`
(the molecules of a garden live in `Type`):

| M3 | Source (refereed) | Producer's published statement | here |
|---|---|---|---|
| TV1 | N2 Lemma 8.1′ (DV′; N2 N6, REF2) | L3 `TVine.Struct.VinechainStatement` | `VinechainInput` |
| TV2 | N2 Theorem 1.15 (F1)–(F6) (REF2 R1, N3 §2.1) | L3 `SubObjectsStatement` (= L5c `Famc.SubObjectsInput`), **proved** (`TVine.Struct.subObjects_holds`) | `subObjectsInput`, `tvineF1Input` (F1, L5a's form) |
| TV3 | N3 Cor 1.16′ (1)–(3), single container (REF3) | L3 `Cor116SingleStatement`, **proved** (`cor116Single_holds`) | `cor116Input` |
| TV4 | N3 Theorem 6 (iv), (i)–(iii) (REF3) | L3 `LaddersStatement` (open, L3 helper), `LayervineStatement` **proved** (`layervine_holds`) | `LaddersInput`, `layervineInput` |
| — | N2 Lemma 5.2 (drawn ⊂ T-vines; REF2) | L3 `DrawnTVineStatement`, **proved** (`TVine.Struct.Drawn.drawnTVineStatement`) | `drawnTVineInput` |
| chart | M4 Theorem C (with REF-M4 R1; groups N3 §4.2) | L4 `TVine.Chart.TVineChartStatement`, **proved** (`tvineChart_holds`) | `tvineChartInput`, `chartSupply` |
| VE-low | TARGET `vineest` L1742–L1751 over `𝒱_γ` | L5b `Famb.VineEstGammaHalfMK`, **proved** (`Famb.vineEstGammaHalfMK`) | `vineEstLow` (re-export) |

L5b's estimate quantifies over the chart supply `NormalChartSupply P.γ` (main's `VINEPARAM` binder);
`chartSupply_of_input` obtains it from L4's Theorem C (L5b's `normalChartSupply_of_tvine`). -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.Flower

/-- **TV1** (N2 Lemma 8.1′, TARGET `vinechainlem` L1930–L1933 with DV′): L3's `VinechainStatement` at universe `0`. -/
def VinechainInput : Prop := TVine.Struct.VinechainStatement.{0, 0}

/-- **TV3** (N3 Cor 1.16′ (1)–(3), single-vine container, sources' removal semantics): L3's statement at universe `0`. -/
def Cor116Input : Prop := TVine.Struct.Cor116SingleStatement.{0, 0}

/-- **TV4** (N3 Theorem 6 (iv): ≤ 3 ladders, ≤ 13 further atoms): L3's `LaddersStatement` at universe `0`. -/
def LaddersInput : Prop := TVine.Struct.LaddersStatement.{0, 0}

/-- **TV4** (N3 Theorem 6 (i)–(iii), TARGET `layervine` for T-vines): L3's `LayervineStatement` at universe `0`. -/
def LayervineInput : Prop := TVine.Struct.LayervineStatement.{0, 0}

/-- **TV2** is proved (L3: `TVine.Struct.subObjects_holds`, N2 Theorem 1.15 (F1)–(F6), unconditional). -/
theorem subObjectsInput : Famc.SubObjectsInput := TVine.Struct.subObjects_holds

/-- **TV2 (F1)** in L5a's form `Fama.TVineF1Input` (L3: `TVine.Struct.f1_mol`). -/
theorem tvineF1Input : Fama.TVineF1Input := fun _ _ _ _ hT => TVine.Struct.f1_mol hT

instance : Fact Fama.TVineF1Input := ⟨tvineF1Input⟩

/-- **TV3** is proved (L3: `TVine.Struct.cor116Single_holds`). -/
theorem cor116Input : Cor116Input := TVine.Struct.cor116Single_holds

/-- **TV4 (i)–(iii)** is proved (L3: `TVine.Struct.layervine_holds`). -/
theorem layervineInput : LayervineInput := TVine.Struct.layervine_holds

/-- N2 Lemma 5.2 (every expansion of a drawn template (III)–(VIII) is a T-vine): L3's statement at universe `0`. -/
def DrawnTVineInput : Prop := TVine.Struct.DrawnTVineStatement.{0, 0}

/-- N2 Lemma 5.2 is proved (L3: `TVine.Struct.Drawn.drawnTVineStatement`, unconditional). -/
theorem drawnTVineInput : DrawnTVineInput := TVine.Struct.Drawn.drawnTVineStatement

/-- **The chart supply** (M4 Theorem C with groups = pieces): L4's `TVineChartStatement`. -/
def TVineChartInput : Prop := TVine.Chart.TVineChartStatement

/-- The chart supply of L5b's vine estimate, from L4's Theorem C. -/
theorem chartSupply_of_input (hT : TVineChartInput) (γ : ℝ) : Famb.NormalChartSupply γ :=
  Famb.normalChartSupply_of_tvine hT γ

/-- **Theorem C** is proved (L4: `TVine.Chart.tvineChart_holds`, unconditional). -/
theorem tvineChartInput : TVineChartInput := TVine.Chart.tvineChart_holds

/-- The chart supply of L5b's vine estimate, unconditionally. -/
theorem chartSupply (γ : ℝ) : Famb.NormalChartSupply γ := chartSupply_of_input tvineChartInput γ

/-- **VE-low** (TARGET `vineest` over `𝒱_γ`, main's `VineEstCanonLayerHalfMK` form): L5b's theorem, re-exported. -/
theorem vineEstLow : WTPrefix Famb.VineEstGammaHalfMK := Famb.vineEstGammaHalfMK

end WaveTurbulence.GammaLow.Flower
