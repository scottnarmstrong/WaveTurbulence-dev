/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Statement

/-!
# Named inputs of the chart theorem (owned by L3)

M4 Theorem C uses, besides N1 Lemma D (proved here, `Chart.LemmaD`) and the local charts (decided here,
`Chart.Configs*`), three structure theorems of the T-vine combinatorics, owned by packet L3. They are taken as named
inputs, stated **exactly** as L3 states them in its published `TVine.Struct.Statement` (the statements L3 prepared for
L4; L3 HANDOFF §Exports), at the universe of `TVineChartStatement`:

| input | statement | source |
|---|---|---|
| `PieceShapeInput` | `Struct.PieceShapeStatement` | N2 Prop 1.17(b) (M4 §2.2 L218–L222) |
| `LayervineInput` | `Struct.LayervineStatement` | N3 Theorem 6 (i)–(iii), atom level, both labellings (N3 L142–L174) |
| `AttachInput` | `Struct.AttachStatement` | M4 Lemma A (M4 L253–L266), atom form |

wt-orch discharges each by `exact` with L3's theorem.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Chart

/-- **Named input** (L3): N2 Proposition 1.17(b), the piece-shape theorem. -/
def PieceShapeInput : Prop := Struct.PieceShapeStatement.{0, 0}

/-- **Named input** (L3): N3 Theorem 6 (i)–(iii) (`layervine` for T-vines), both joint labellings. -/
def LayervineInput : Prop := Struct.LayervineStatement.{0, 0}

/-- **Named input** (L3): M4 Lemma A (attachment), atom form. -/
def AttachInput : Prop := Struct.AttachStatement.{0, 0}

end WaveTurbulence.TVine.Chart
