module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepSequence
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainDifficulty

/-!
# Bad surfaces of step diagrams, varying branch numbers and varying unions of fourfolds

For a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` of fourfolds with bad loci `W^± ⊆ X^±`, a
*negative-side bad surface* is an irreducible closed subvariety `V ⊆ W⁻` of dimension two, and a
*positive-side bad surface* is an irreducible closed subvariety `V ⊆ W⁺` of dimension two.

Let `(p_i, Θ_i)_{i ≥ 0}`, `p_i : Y_i ⟶ X_i`, be a terminal chain over a stabilized small klt tail
of fourfolds, with labels `S_h`. On a model `(Y, Θ)` of the chain, the *varying branch number* at
an irreducible surface `V ⊆ Y` is `r_V^var = ∑_{h varying} r_{V,h}`, the sum of the branch numbers
of the varying labels. At a junction `p_i : (Y_i, Θ_i) ⟶ (X_i, B_i)` the *varying union* `Q` is the
union of the varying labels `S_h` on `Y_i`, with its reduced structure.

## Main definitions

* `MMP.Fourfold.IsNegativeBadSurface`, `MMP.Fourfold.IsPositiveBadSurface`: the bad surfaces
  `V ⊆ W⁻` and `V ⊆ W⁺`.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsVaryingBranchNumber`: `r = r_V^var`.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.varyingUnion`: the varying union `Q ⊆ Y_i`
  at a junction, and `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.varyingUnionIdeal` the
  ideal sheaf of its reduced structure.

## Main results

* `MMP.Fourfold.not_isNegativeBadSurface_of_badLocusMinus_eq_bot`,
  `MMP.Fourfold.not_isPositiveBadSurface_of_badLocusPlus_eq_bot`: an empty bad locus contains no
  bad surface.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.exists_isVaryingBranchNumber`: the varying
  branch number exists at every irreducible closed subset of every model.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.isVaryingBranchNumber_zero_of_not_subset`:
  `r_V^var = 0` for `V ⊄ Q` on a junction.
* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.isClosed_image_varyingUnion`,
  `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.topologicalKrullDim_image_varyingUnion_le`:
  on a prepared chain, `p_i` maps the varying union onto a closed set of dimension at most one.

## Implementation notes

* The bad loci `W^±` are the closed sets `MMP.Fourfold.badLocusMinus` and
  `MMP.Fourfold.badLocusPlus`, defined for any two morphisms `f^± : X^± ⟶ Z` with a common
  target, and the bad surfaces are defined in the same generality; the source considers them for
  a step diagram (`MMP.Fourfold.IsFourfoldStepDiagram`). An irreducible closed subvariety is an
  irreducible closed subset `V` (`TopologicalSpace.IrreducibleCloseds`, with its reduced
  structure), and "of dimension two" is `topologicalKrullDim V = 2`.
* Branch numbers on a model of a terminal chain are a predicate on their value
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelBranchNumber`), so the varying
  branch number is too. The sum over the varying labels is the finitely supported sum `∑ᶠ`, a
  finite sum since there are finitely many labels
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.finite_label`). As the branch number, it is
  defined at every irreducible closed subset of a model; the source considers surfaces.
* The varying union is defined at every junction of a terminal chain, the source considering
  those of a prepared chain: the union of the supports of the centres `S_h^{Y_i}` on `Y_i` of the
  varying labels which are prime divisors of `Y_i`, as in
  `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain`. Its reduced structure is the closed
  subscheme cut out by the vanishing ideal sheaf
  (`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`) of its closure, the reduced induced
  structure on the closure. The union is a finite union of prime divisors, hence closed, so this
  is the reduced induced structure on `Q` itself.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

/-! ### Bad surfaces -/

section BadSurface

variable {Xm Xp Z : Scheme.{u}} (fm : Xm ⟶ Z) (fp : Xp ⟶ Z)

/-- A *negative-side bad surface* of a step diagram `X⁻ → Z ← X⁺` (by `f^±`): an irreducible
closed subvariety `V ⊆ W⁻` of dimension two, `W⁻ = (f⁻)⁻¹(Σ)` the negative-side bad locus
(`MMP.Fourfold.badLocusMinus`). -/
@[mmp "def_oai4_negative_side_bad_surface"]
def IsNegativeBadSurface (V : IrreducibleCloseds Xm) : Prop :=
  (V : Set Xm) ⊆ badLocusMinus fm fp ∧ topologicalKrullDim (V : Set Xm) = 2

/-- A *positive-side bad surface* of a step diagram `X⁻ → Z ← X⁺` (by `f^±`): an irreducible
closed subvariety `V ⊆ W⁺` of dimension two, `W⁺ = (f⁺)⁻¹(Σ)` the positive-side bad locus
(`MMP.Fourfold.badLocusPlus`). -/
@[mmp "def_oai4_positive_side_bad_surface"]
def IsPositiveBadSurface (V : IrreducibleCloseds Xp) : Prop :=
  (V : Set Xp) ⊆ badLocusPlus fm fp ∧ topologicalKrullDim (V : Set Xp) = 2

variable {fm fp}

/-- Characterisation of a negative-side bad surface. -/
theorem isNegativeBadSurface_iff {V : IrreducibleCloseds Xm} :
    IsNegativeBadSurface fm fp V ↔
      (V : Set Xm) ⊆ badLocusMinus fm fp ∧ topologicalKrullDim (V : Set Xm) = 2 :=
  Iff.rfl

/-- Characterisation of a positive-side bad surface. -/
theorem isPositiveBadSurface_iff {V : IrreducibleCloseds Xp} :
    IsPositiveBadSurface fm fp V ↔
      (V : Set Xp) ⊆ badLocusPlus fm fp ∧ topologicalKrullDim (V : Set Xp) = 2 :=
  Iff.rfl

/-- A negative-side bad surface lies in the negative-side bad locus. -/
theorem IsNegativeBadSurface.subset {V : IrreducibleCloseds Xm}
    (h : IsNegativeBadSurface fm fp V) : (V : Set Xm) ⊆ badLocusMinus fm fp :=
  h.1

/-- A negative-side bad surface has dimension two. -/
theorem IsNegativeBadSurface.topologicalKrullDim_eq {V : IrreducibleCloseds Xm}
    (h : IsNegativeBadSurface fm fp V) : topologicalKrullDim (V : Set Xm) = 2 :=
  h.2

/-- A positive-side bad surface lies in the positive-side bad locus. -/
theorem IsPositiveBadSurface.subset {V : IrreducibleCloseds Xp}
    (h : IsPositiveBadSurface fm fp V) : (V : Set Xp) ⊆ badLocusPlus fm fp :=
  h.1

/-- A positive-side bad surface has dimension two. -/
theorem IsPositiveBadSurface.topologicalKrullDim_eq {V : IrreducibleCloseds Xp}
    (h : IsPositiveBadSurface fm fp V) : topologicalKrullDim (V : Set Xp) = 2 :=
  h.2

/-- An empty negative-side bad locus contains no bad surface. -/
theorem not_isNegativeBadSurface_of_badLocusMinus_eq_bot (h : badLocusMinus fm fp = ⊥)
    (V : IrreducibleCloseds Xm) : ¬ IsNegativeBadSurface fm fp V := fun hV => by
  obtain ⟨x, hx⟩ := V.isIrreducible.nonempty
  simpa [h] using hV.subset hx

/-- An empty positive-side bad locus contains no bad surface. -/
theorem not_isPositiveBadSurface_of_badLocusPlus_eq_bot (h : badLocusPlus fm fp = ⊥)
    (V : IrreducibleCloseds Xp) : ¬ IsPositiveBadSurface fm fp V := fun hV => by
  obtain ⟨x, hx⟩ := V.isIrreducible.nonempty
  simpa [h] using hV.subset hx

end BadSurface

namespace StabilizedSmallKltTail

namespace TerminalChain

variable {T : StabilizedSmallKltTail} (C : TerminalChain T)

/-! ### Varying branch numbers -/

/-- `r` is the *varying branch number* `r_V^var = ∑_{h varying} r_{V,h}` at an irreducible closed
subset `V` (an irreducible surface in the source) of the model `C.model x` indexed by `x`: the
sum, over the varying labels `S_h`, of their branch numbers `r_{V,h}`
(`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelBranchNumber`). -/
@[mmp "def_oai4_varying_branch_number"]
def IsVaryingBranchNumber (x : C.ModelIndex) (V : IrreducibleCloseds (C.model x)) (r : ℕ) : Prop :=
  ∃ r' : C.Label → ℕ, (∀ S, C.IsVaryingLabel S → C.IsLabelBranchNumber S x V (r' S)) ∧
    r = ∑ᶠ (S) (_ : C.IsVaryingLabel S), r' S

variable {C}

/-- The varying branch number exists at every irreducible closed subset of every model. -/
theorem exists_isVaryingBranchNumber (x : C.ModelIndex) (V : IrreducibleCloseds (C.model x)) :
    ∃ r, C.IsVaryingBranchNumber x V r := by
  choose r' hr' using fun S => C.exists_isLabelBranchNumber S x V
  exact ⟨_, r', fun S _ => hr' S, rfl⟩

variable (C)

/-! ### Varying unions -/

/-- The *varying union* `Q ⊆ Y_i` at the junction `p_i : (Y_i, Θ_i) ⟶ (X_i, B_i)` of a terminal
chain: the union of the varying labels on `Y_i`, that is, of the supports of the prime divisors
`S_h^{Y_i}` of `Y_i` for the varying labels `S_h`. Its reduced structure is
`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.varyingUnionIdeal`. -/
@[mmp "def_oai4_varying_union"]
def varyingUnion (i : ℕ) : Set (C.junction i).Y :=
  {y | ∃ S : C.Label, C.IsVaryingLabel S ∧
    ∃ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩), C.IsLabelCentre S ⟨i, none⟩ P ∧
      y ∈ P.support}

/-- Membership in the varying union. -/
theorem mem_varyingUnion_iff {i : ℕ} {y : (C.junction i).Y} :
    y ∈ C.varyingUnion i ↔ ∃ S : C.Label, C.IsVaryingLabel S ∧
      ∃ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩), C.IsLabelCentre S ⟨i, none⟩ P ∧
        y ∈ P.support :=
  Iff.rfl

/-- The ideal sheaf of the varying union `Q ⊆ Y_i` with its reduced structure: the ideal of the
functions vanishing on `Q`. The reduced closed subscheme `Q` is
`(C.varyingUnionIdeal i).subscheme`. -/
@[mmp "def_oai4_varying_union"]
def varyingUnionIdeal (i : ℕ) : (C.junction i).Y.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure (C.varyingUnion i), isClosed_closure⟩

/-- The support of the ideal sheaf of the varying union is the closure of the varying union. -/
@[simp]
theorem coe_support_varyingUnionIdeal (i : ℕ) :
    ((C.varyingUnionIdeal i).support : Set (C.junction i).Y) = closure (C.varyingUnion i) :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

variable {C}

/-- The support of a varying label on `Y_i` lies in the varying union. -/
theorem support_subset_varyingUnion {i : ℕ} {S : C.Label} (hS : C.IsVaryingLabel S)
    {P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩)} (hP : C.IsLabelCentre S ⟨i, none⟩ P) :
    (P.support : Set (C.junction i).Y) ⊆ C.varyingUnion i :=
  fun _ hy => ⟨S, hS, P, hP, hy⟩

/-- At a junction, the varying branch number vanishes at an irreducible closed subset not
contained in the varying union: `r_V^var = 0` for `V ⊄ Q`. -/
theorem isVaryingBranchNumber_zero_of_not_subset {i : ℕ}
    {V : IrreducibleCloseds (C.model ⟨i, none⟩)}
    (hV : ¬ (V : Set (C.model ⟨i, none⟩)) ⊆ C.varyingUnion i) :
    C.IsVaryingBranchNumber ⟨i, none⟩ V 0 := by
  refine ⟨fun _ => 0, fun S hS => isLabelBranchNumber_zero_of_not_subset fun P hP hVP =>
    hV (hVP.trans (support_subset_varyingUnion hS hP)), ?_⟩
  simp

end TerminalChain

namespace PreparedChain

variable {T : StabilizedSmallKltTail} (Q : PreparedChain T)

/-- At a junction `p_i : (Y_i, Θ_i) ⟶ (X_i, B_i)`, `i ≥ i₀`, of a prepared chain, `p_i` maps the
varying union onto a closed set. -/
theorem isClosed_image_varyingUnion {i : ℕ} (hi : Q.start ≤ i) :
    IsClosed ((Q.chain.junction i).p '' Q.chain.varyingUnion i) :=
  Q.isClosed_image_varyingLabels i hi

/-- At a junction `p_i : (Y_i, Θ_i) ⟶ (X_i, B_i)`, `i ≥ i₀`, of a prepared chain, `p_i` maps the
varying union onto a set of dimension at most one. -/
theorem topologicalKrullDim_image_varyingUnion_le {i : ℕ} (hi : Q.start ≤ i) :
    topologicalKrullDim ((Q.chain.junction i).p '' Q.chain.varyingUnion i) ≤ 1 :=
  Q.topologicalKrullDim_image_varyingLabels_le i hi

end PreparedChain

end StabilizedSmallKltTail

end MMP.Fourfold
