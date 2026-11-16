module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryDlt
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail

/-!
# Bad loci of step diagrams, step sequences and stabilized small klt tails

For a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` of fourfolds, let `U ⊆ Z` be the largest open subset
over which both `f⁻` and `f⁺` are isomorphisms. The *bad locus of the base* is `Σ = Z ∖ U` with its
reduced structure, and the *bad loci* of the two sides are the preimages `W^± = (f^±)⁻¹(Σ)`, again
with their reduced structures.

A *step sequence* is a sequence of step diagrams `(X_i, B_i) → Z_i ← (X_{i+1}, B_{i+1})`,
`i ≥ 0`. It is *small from the index `i₀`* if `f_i` is small for every `i ≥ i₀`; its *small tail*
is the shifted step sequence `(X_{i₀ + i}, B_{i₀ + i})_{i ≥ 0}`.

For a klt pair `(X, B)`, the *low-discrepancy set* `I(X, B)` is the set of normalized divisorial
valuations `ξ` exceptional over `X` with log discrepancy `a(ξ; X, B) ≤ 1`. For a step sequence of
klt pairs, `I_i = I(X_i, B_i)` and `a_i(ξ) = a(ξ; X_i, B_i)`, and, when the sequence is small from
the index `0`, the *stable low-discrepancy set* is `I_∞ = ⋂_{i ≥ 0} I_i`. A *stabilized small klt
tail* is a step sequence small from the index `0` through klt pairs with `I_i = I_∞` for all `i`.

## Main definitions

* `MMP.Fourfold.badLocusBaseIdeal`, `MMP.Fourfold.badLocusMinusIdeal`,
  `MMP.Fourfold.badLocusPlusIdeal`: the ideal sheaves of the reduced closed subschemes `Σ`, `W⁻`,
  `W⁺`, supported on the closed sets `MMP.Fourfold.badLocusBase`, `MMP.Fourfold.badLocusMinus`,
  `MMP.Fourfold.badLocusPlus`.
* `MMP.Fourfold.StepSequence`: step sequences of fourfolds.
* `MMP.Fourfold.StepSequence.IsSmallFrom`, `MMP.Fourfold.StepSequence.shift`: step sequences
  small from an index, and their small tails.
* `MMP.Fourfold.StepSequence.lowDiscrepancySetAt`, `MMP.Fourfold.StepSequence.IsLogDiscrepancyAt`:
  `I_i` and `a_i`.
* `MMP.Fourfold.StepSequence.Corresponds`: the identification of valuations of `k(X_0)` and of
  `k(X_i)` along the birational maps of the sequence.
* `MMP.Fourfold.StepSequence.stableLowDiscrepancySet`: `I_∞ = ⋂ I_i`.
* `MMP.Fourfold.StepSequence.IsStabilizedSmallKltTail`: stabilized small klt tails.

## Main results

* `MMP.Fourfold.support_badLocusBaseIdeal` (and its analogues for `W^±`): the reduced closed
  subschemes are supported on the bad loci.
* `MMP.Fourfold.badLocusPlus_nonempty_iff_of_isIso`: when `f⁺` is an
  isomorphism, `W⁺` is nonempty exactly when `f⁻` is not an isomorphism.
* `MMP.Fourfold.StepSequence.isSmallMorphism_fp`: each `f_i⁺` of a step sequence is small.

## Implementation notes

* The open `U` and the closed sets `Σ`, `W^±` are `MMP.Fourfold.commonBiregularLocus`,
  `MMP.Fourfold.badLocusBase`, `MMP.Fourfold.badLocusMinus`, `MMP.Fourfold.badLocusPlus`, defined
  for any two morphisms with a common target. The reduced structure on a closed set `T` of a
  scheme is the closed subscheme cut out by the ideal sheaf `vanishingIdeal T` of all functions
  vanishing on `T` (`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`); the reduced
  subschemes are `(badLocusBaseIdeal fm fp).subscheme` and so on.
* The models of a step sequence carry canonical divisors `K_i`, cut out by one rational top form:
  `K_{i+1} = (f_i⁺)⁻¹_* (f_i)_* K_i`, the convention of `MMP.Fourfold.IsFourfoldStepDiagram`,
  which also gives `B_{i+1} = (f_i⁺)⁻¹_* (f_i)_* B_i`, as in `MMP.Fourfold.StabilizedTail`.
* `I(X, B)` is `MMP.Fourfold.lowDiscrepancySet`, defined for every pair; the source considers it
  for klt pairs. Log discrepancies of valuations are the predicate
  `MMP.Fourfold.IsValuationLogDiscrepancy`, so `a_i(ξ) = a` is `S.IsLogDiscrepancyAt i ξ a`.
* The sets `I_i` are sets of valuations of the different function fields `k(X_i)`. These are
  identified through `k(X_i) ≅ k(Z_i) ≅ k(X_{i+1})`, given by the birational morphisms `f_i`,
  `f_i⁺`: a valuation `η` of `k(X_i)` corresponds to the valuation `η'` of `k(X_{i+1})` with the
  same restriction to `k(Z_i)` (`MMP.Fourfold.StepSequence.IsTransportedValuation`, as in
  `MMP.Fourfold.StabilizedTail.IsTransportedValuation`), and a valuation `ξ` of `k(X_0)` to the
  valuation `ξ_i` of `k(X_i)` obtained by composing these
  (`MMP.Fourfold.StepSequence.Corresponds`); since the field maps are isomorphisms, `ξ_i` exists
  and is unique. `I_∞` is then the set of valuations `ξ` of `k(X_0)` with `ξ_i ∈ I_i` for every
  `i`, and `I_i = I_∞` means that `ξ ↦ ξ_i` maps `I_∞` onto `I_i`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Bad loci -/

attribute [mmp "def_oai4_bad_locus_base"] commonBiregularLocus badLocusBase
attribute [mmp "def_oai4_bad_locus_negative"] badLocusMinus
attribute [mmp "def_oai4_bad_locus_positive"] badLocusPlus

section BadLoci

variable {Xm Xp Z : Scheme.{u}} (fm : Xm ⟶ Z) (fp : Xp ⟶ Z)

/-- The ideal sheaf of the *bad locus of the base* `Σ = Z ∖ U` with its reduced structure, `U` the
largest open of `Z` over which both `f⁻` and `f⁺` are isomorphisms: the ideal of the functions
vanishing on `Σ`. The reduced closed subscheme `Σ` is `(badLocusBaseIdeal fm fp).subscheme`. -/
@[mmp "def_oai4_bad_locus_base"]
def badLocusBaseIdeal : Z.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (badLocusBase fm fp)

/-- The ideal sheaf of the *negative-side bad locus* `W⁻ = (f⁻)⁻¹(Σ) ⊆ X⁻` with its reduced
structure. The reduced closed subscheme `W⁻` is `(badLocusMinusIdeal fm fp).subscheme`. -/
@[mmp "def_oai4_bad_locus_negative"]
def badLocusMinusIdeal : Xm.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (badLocusMinus fm fp)

/-- The ideal sheaf of the *positive-side bad locus* `W⁺ = (f⁺)⁻¹(Σ) ⊆ X⁺` with its reduced
structure. The reduced closed subscheme `W⁺` is `(badLocusPlusIdeal fm fp).subscheme`. -/
@[mmp "def_oai4_bad_locus_positive"]
def badLocusPlusIdeal : Xp.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (badLocusPlus fm fp)

/-- The reduced closed subscheme `Σ` is supported on the bad locus of the base. -/
@[simp]
theorem support_badLocusBaseIdeal : (badLocusBaseIdeal fm fp).support = badLocusBase fm fp :=
  Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal _)

/-- The reduced closed subscheme `W⁻` is supported on the negative-side bad locus. -/
@[simp]
theorem support_badLocusMinusIdeal :
    (badLocusMinusIdeal fm fp).support = badLocusMinus fm fp :=
  Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal _)

/-- The reduced closed subscheme `W⁺` is supported on the positive-side bad locus. -/
@[simp]
theorem support_badLocusPlusIdeal : (badLocusPlusIdeal fm fp).support = badLocusPlus fm fp :=
  Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal _)

/-- If the positive morphism `f⁺` is an isomorphism (as for a step diagram coming from a
divisorial contraction), the positive-side bad locus `W⁺` is nonempty exactly when `f⁻` is not an
isomorphism. -/
@[mmp "def_oai4_bad_locus_positive"]
theorem badLocusPlus_nonempty_iff_of_isIso [IsIso fp] :
    (badLocusPlus fm fp : Set Xp).Nonempty ↔ ¬ IsIso fm := by
  have h1 : biregularLocus fp = ⊤ :=
    top_le_iff.mp (le_biregularLocus ((isBiregular_top_iff fp).mpr inferInstance))
  have h2 : IsIso fm ↔ biregularLocus fm = ⊤ := by
    rw [← isBiregular_top_iff, isBiregular_iff_le_biregularLocus, top_le_iff]
  have hs : Function.Surjective fp := (inferInstance : Surjective fp).surj
  rw [coe_badLocusPlus, hs.nonempty_preimage, coe_badLocusBase, commonBiregularLocus, h1,
    inf_top_eq, h2, Set.nonempty_compl, ne_eq, not_congr]
  rw [← Opens.coe_top, SetLike.coe_set_eq]

end BadLoci

/-! ### Step sequences -/

/-- A *step sequence* `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}`: pairs `(X_i, B_i)` with canonical
divisors `K_i`, normal projective varieties `Z_i` and morphisms `f_i : X_i ⟶ Z_i`,
`f_i⁺ : X_{i+1} ⟶ Z_i` such that every `(X_i, B_i) → Z_i ← (X_{i+1}, B_{i+1})` by `f_i`, `f_i⁺`
is a step diagram (`MMP.Fourfold.IsFourfoldStepDiagram`): in particular `X_i` are normal
projective complex fourfolds, `B_i` effective `ℚ`-divisors and `B_{i+1}` (and `K_{i+1}`) the
strict transform of `(f_i)_* B_i` (of `(f_i)_* K_i`). Its bad loci are
`Σ_i ⊆ Z_i`, `W_i⁻ ⊆ X_i` and `W_i⁺ ⊆ X_{i+1}`
(`MMP.Fourfold.StepSequence.badLocusBaseAt` and its analogues). -/
@[mmp "def_oai4_step_sequence"]
structure StepSequence where
  /-- The models `X_i`. -/
  X : ℕ → Scheme.{0}
  /-- The structure morphism `X_i ⟶ Spec ℂ`. -/
  sX : ∀ i, X i ⟶ Spec (.of ℂ)
  [isIntegral : ∀ i, IsIntegral (X i)]
  [compactSpace : ∀ i, CompactSpace (X i)]
  [isLocallyNoetherian : ∀ i, IsLocallyNoetherian (X i)]
  [isNormal : ∀ i, IsNormal (X i)]
  /-- The canonical divisor `K_i` of `X_i`. -/
  K : ∀ i, Divisor (X i)
  /-- The boundary `B_i` on `X_i`. -/
  B : ∀ i, QDivisor (X i)
  /-- The base `Z_i` of the `i`-th step diagram. -/
  Z : ℕ → Scheme.{0}
  /-- The structure morphism `Z_i ⟶ Spec ℂ`. -/
  sZ : ∀ i, Z i ⟶ Spec (.of ℂ)
  /-- The morphism `f_i : X_i ⟶ Z_i`. -/
  f : ∀ i, X i ⟶ Z i
  /-- The morphism `f_i⁺ : X_{i+1} ⟶ Z_i`. -/
  fp : ∀ i, X (i + 1) ⟶ Z i
  /-- Each `(X_i, B_i) → Z_i ← (X_{i+1}, B_{i+1})` by `f_i`, `f_i⁺` is a step diagram. -/
  isFourfoldStepDiagram : ∀ i,
    IsFourfoldStepDiagram (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (f i) (fp i)
  /-- `K_{i+1}` is the strict transform of `(f_i)_* K_i`. -/
  K_eq : ∀ i, K (i + 1) = flipTransform (f i) (fp i) (K i)
  /-- `B_{i+1}` is the strict transform of `(f_i)_* B_i`. -/
  B_eq : ∀ i, B (i + 1) = flipTransform (f i) (fp i) (B i)

attribute [instance] StepSequence.isIntegral StepSequence.compactSpace
  StepSequence.isLocallyNoetherian StepSequence.isNormal

namespace StepSequence

variable (S : StepSequence)

/-- The bad locus `Σ_i ⊆ Z_i` of the `i`-th step diagram, as a closed set. -/
@[mmp "def_oai4_step_sequence"]
abbrev badLocusBaseAt (i : ℕ) : Closeds (S.Z i) := badLocusBase (S.f i) (S.fp i)

/-- The negative-side bad locus `W_i⁻ ⊆ X_i` of the `i`-th step diagram, as a closed set. -/
@[mmp "def_oai4_step_sequence"]
abbrev badLocusMinusAt (i : ℕ) : Closeds (S.X i) := badLocusMinus (S.f i) (S.fp i)

/-- The positive-side bad locus `W_i⁺ ⊆ X_{i+1}` of the `i`-th step diagram, as a closed set. -/
@[mmp "def_oai4_step_sequence"]
abbrev badLocusPlusAt (i : ℕ) : Closeds (S.X (i + 1)) := badLocusPlus (S.f i) (S.fp i)

/-- The ideal sheaf of the reduced bad locus `Σ_i ⊆ Z_i` of the `i`-th step diagram. -/
@[mmp "def_oai4_step_sequence"]
abbrev badLocusBaseIdealAt (i : ℕ) : (S.Z i).IdealSheafData := badLocusBaseIdeal (S.f i) (S.fp i)

/-- The ideal sheaf of the reduced negative-side bad locus `W_i⁻ ⊆ X_i`. -/
@[mmp "def_oai4_step_sequence"]
abbrev badLocusMinusIdealAt (i : ℕ) : (S.X i).IdealSheafData :=
  badLocusMinusIdeal (S.f i) (S.fp i)

/-- The ideal sheaf of the reduced positive-side bad locus `W_i⁺ ⊆ X_{i+1}`. -/
@[mmp "def_oai4_step_sequence"]
abbrev badLocusPlusIdealAt (i : ℕ) : (S.X (i + 1)).IdealSheafData :=
  badLocusPlusIdeal (S.f i) (S.fp i)

/-- Each base `Z_i` of a step sequence is an integral scheme. -/
instance isIntegral_Z (i : ℕ) : IsIntegral (S.Z i) :=
  (S.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral

/-- Each `f_i : X_i ⟶ Z_i` is dominant (it is birational). -/
instance isDominant_f (i : ℕ) : IsDominant (S.f i) :=
  (S.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant

/-- Each `f_i⁺ : X_{i+1} ⟶ Z_i` is dominant (it is birational). -/
instance isDominant_fp (i : ℕ) : IsDominant (S.fp i) :=
  (S.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant

/-! ### Small tails -/

/-- A step sequence is *small from the index `i₀`* if `f_i` is small for every `i ≥ i₀` (each
`f_i⁺` is small by definition, `MMP.Fourfold.StepSequence.isSmallMorphism_fp`). -/
@[mmp "def_oai4_small_tail"]
def IsSmallFrom (i₀ : ℕ) : Prop :=
  ∀ i, i₀ ≤ i → IsSmallMorphism (S.sX i) (S.sZ i) (S.f i)

/-- Each `f_i⁺` of a step sequence is small. -/
@[mmp "def_oai4_small_tail"]
theorem isSmallMorphism_fp (i : ℕ) : IsSmallMorphism (S.sX (i + 1)) (S.sZ i) (S.fp i) :=
  (S.isFourfoldStepDiagram i).isSmallMorphism_plus

/-- The shifted step sequence
`(X_{i₀ + i}, B_{i₀ + i}, Z_{i₀ + i}, f_{i₀ + i}, f_{i₀ + i}⁺)_{i ≥ 0}`;
for a step sequence small from the index `i₀`, this is its *small tail*. -/
@[mmp "def_oai4_small_tail"]
def shift (i₀ : ℕ) : StepSequence where
  X i := S.X (i₀ + i)
  sX i := S.sX (i₀ + i)
  K i := S.K (i₀ + i)
  B i := S.B (i₀ + i)
  Z i := S.Z (i₀ + i)
  sZ i := S.sZ (i₀ + i)
  f i := S.f (i₀ + i)
  fp i := S.fp (i₀ + i)
  isFourfoldStepDiagram i := S.isFourfoldStepDiagram (i₀ + i)
  K_eq i := S.K_eq (i₀ + i)
  B_eq i := S.B_eq (i₀ + i)

/-- The models of the shifted step sequence are `X_{i₀ + i}`. -/
@[simp] theorem shift_X (i₀ i : ℕ) : (S.shift i₀).X i = S.X (i₀ + i) := rfl

/-- The bases of the shifted step sequence are `Z_{i₀ + i}`. -/
@[simp] theorem shift_Z (i₀ i : ℕ) : (S.shift i₀).Z i = S.Z (i₀ + i) := rfl

/-- The canonical divisors of the shifted step sequence are `K_{i₀ + i}`. -/
@[simp] theorem shift_K (i₀ i : ℕ) : (S.shift i₀).K i = S.K (i₀ + i) := rfl

/-- The boundaries of the shifted step sequence are `B_{i₀ + i}`. -/
@[simp] theorem shift_B (i₀ i : ℕ) : (S.shift i₀).B i = S.B (i₀ + i) := rfl

/-- The structure morphisms of the models of the shifted step sequence are those of
`X_{i₀ + i}`. -/
theorem shift_sX (i₀ i : ℕ) : (S.shift i₀).sX i = S.sX (i₀ + i) := rfl

/-- The structure morphisms of the bases of the shifted step sequence are those of
`Z_{i₀ + i}`. -/
theorem shift_sZ (i₀ i : ℕ) : (S.shift i₀).sZ i = S.sZ (i₀ + i) := rfl

/-- The morphisms `f_i` of the shifted step sequence are `f_{i₀ + i}`. -/
theorem shift_f (i₀ i : ℕ) : (S.shift i₀).f i = S.f (i₀ + i) := rfl

/-- The morphisms `f_i⁺` of the shifted step sequence are `f_{i₀ + i}⁺`. -/
theorem shift_fp (i₀ i : ℕ) : (S.shift i₀).fp i = S.fp (i₀ + i) := rfl

/-- The small tail of a step sequence small from the index `i₀` is small from the index `0`. -/
theorem IsSmallFrom.shift {S : StepSequence} {i₀ : ℕ} (h : S.IsSmallFrom i₀) :
    (S.shift i₀).IsSmallFrom 0 :=
  fun i _ => h (i₀ + i) (Nat.le_add_right i₀ i)

/-! ### Low-discrepancy sets -/

attribute [mmp "def_oai4_low_discrepancy_set"] MMP.Fourfold.lowDiscrepancySet

/-- `I_i = I(X_i, B_i)`, the low-discrepancy set of the `i`-th model of a step sequence (of klt
pairs): the normalized divisorial valuations of `k(X_i)` exceptional over `X_i` with
`a(ξ; X_i, B_i) ≤ 1`. -/
@[mmp "def_oai4_low_discrepancy_set"]
abbrev lowDiscrepancySetAt (i : ℕ) :
    Set (Valuation (S.X i).functionField (WithZero (Multiplicative ℤ))) :=
  lowDiscrepancySet (S.sX i) (S.B i)

/-- `a = a_i(ξ) = a(ξ; X_i, B_i)` for a valuation `ξ` of `k(X_i)`. -/
@[mmp "def_oai4_low_discrepancy_set"]
abbrev IsLogDiscrepancyAt (i : ℕ)
    (ξ : Valuation (S.X i).functionField (WithZero (Multiplicative ℤ))) (a : ℝ) : Prop :=
  IsValuationLogDiscrepancy (S.sX i) (S.B i) ξ a

/-- A step sequence *of klt pairs*: every `(X_i, B_i)` is klt. -/
@[mmp "def_oai4_low_discrepancy_set"]
def IsKlt : Prop := ∀ i, IsKltPair (S.sX i) (S.B i)

/-! ### The stable low-discrepancy set -/

/-- The valuation `η'` of `k(X_{i+1})` corresponds to the valuation `η` of `k(X_i)` under the
identifications `k(X_i) ≅ k(Z_i) ≅ k(X_{i+1})` given by the birational morphisms `f_i`, `f_i⁺`:
their restrictions to `k(Z_i)` agree. -/
def IsTransportedValuation (i : ℕ)
    (η : Valuation (S.X i).functionField (WithZero (Multiplicative ℤ)))
    (η' : Valuation (S.X (i + 1)).functionField (WithZero (Multiplicative ℤ))) : Prop :=
  η'.comap (functionFieldMap (S.fp i)) = η.comap (functionFieldMap (S.f i))

/-- The valuation `η` of `k(X_i)` corresponds to the valuation `ξ` of `k(X_0)` under the
composite identification `k(X_0) ≅ k(X_1) ≅ ⋯ ≅ k(X_i)` along the birational maps of the step
sequence: `η = ξ` for `i = 0`, and `η` is transported
(`MMP.Fourfold.StepSequence.IsTransportedValuation`) from a valuation of `k(X_{i-1})`
corresponding to `ξ` otherwise. -/
def Corresponds : ∀ i : ℕ, Valuation (S.X 0).functionField (WithZero (Multiplicative ℤ)) →
    Valuation (S.X i).functionField (WithZero (Multiplicative ℤ)) → Prop
  | 0, ξ, η => η = ξ
  | i + 1, ξ, η => ∃ ζ, Corresponds i ξ ζ ∧ S.IsTransportedValuation i ζ η

/-- At the index `0`, the valuation of `k(X_0)` corresponding to `ξ` is `ξ` itself. -/
@[simp] theorem corresponds_zero
    {ξ η : Valuation (S.X 0).functionField (WithZero (Multiplicative ℤ))} :
    S.Corresponds 0 ξ η ↔ η = ξ := Iff.rfl

/-- A valuation of `k(X_{i+1})` corresponds to `ξ` exactly when it is transported from a
valuation of `k(X_i)` corresponding to `ξ`. -/
theorem corresponds_succ (i : ℕ)
    {ξ : Valuation (S.X 0).functionField (WithZero (Multiplicative ℤ))}
    {η : Valuation (S.X (i + 1)).functionField (WithZero (Multiplicative ℤ))} :
    S.Corresponds (i + 1) ξ η ↔ ∃ ζ, S.Corresponds i ξ ζ ∧ S.IsTransportedValuation i ζ η :=
  Iff.rfl

/-- The *stable low-discrepancy set* `I_∞ = ⋂_{i ≥ 0} I_i` of a step sequence (small from the
index `0`, of klt pairs), as a set of valuations of `k(X_0)`: the valuations `ξ` of `k(X_0)` whose
corresponding valuation of `k(X_i)` (`MMP.Fourfold.StepSequence.Corresponds`) lies in `I_i` for
every `i ≥ 0`. -/
@[mmp "def_oai4_stable_low_discrepancy_set"]
def stableLowDiscrepancySet :
    Set (Valuation (S.X 0).functionField (WithZero (Multiplicative ℤ))) :=
  {ξ | ∀ i, ∃ η ∈ S.lowDiscrepancySetAt i, S.Corresponds i ξ η}

/-- `ξ ∈ I_∞` exactly when, for every `i`, some valuation of `k(X_i)` in `I_i` corresponds to
`ξ`. -/
theorem mem_stableLowDiscrepancySet
    {ξ : Valuation (S.X 0).functionField (WithZero (Multiplicative ℤ))} :
    ξ ∈ S.stableLowDiscrepancySet ↔ ∀ i, ∃ η ∈ S.lowDiscrepancySetAt i, S.Corresponds i ξ η :=
  Iff.rfl

/-- `I_∞ ⊆ I_0`. -/
theorem stableLowDiscrepancySet_subset :
    S.stableLowDiscrepancySet ⊆ S.lowDiscrepancySetAt 0 := by
  rintro ξ hξ
  obtain ⟨η, hη, rfl⟩ := hξ 0
  exact hη

/-! ### Stabilized small klt tails -/

/-- A step sequence is a *stabilized small klt tail* if it is small from the index `0`, every
`(X_i, B_i)` is a klt pair, and `I_i = I_∞` for every `i ≥ 0`: the valuations of `k(X_i)`
corresponding to the elements of `I_∞` are exactly the elements of `I_i`. -/
@[mmp "def_oai4_stabilized_tail"]
structure IsStabilizedSmallKltTail : Prop where
  /-- The sequence is small from the index `0`. -/
  isSmallFrom_zero : S.IsSmallFrom 0
  /-- Every `(X_i, B_i)` is klt. -/
  isKlt : S.IsKlt
  /-- `I_i = I_∞`: `I_i` consists of the valuations corresponding to the elements of `I_∞`. -/
  lowDiscrepancySetAt_eq : ∀ i,
    S.lowDiscrepancySetAt i = {η | ∃ ξ ∈ S.stableLowDiscrepancySet, S.Corresponds i ξ η}

end StepSequence

/-- A *stabilized small klt tail* `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}`: a step sequence which is
small from the index `0`, in which every `(X_i, B_i)` is a klt pair, and in which `I_i = I_∞` for
every `i ≥ 0`. -/
@[mmp "def_oai4_stabilized_tail"]
structure StabilizedSmallKltTail extends StepSequence where
  /-- The underlying step sequence is a stabilized small klt tail. -/
  isStabilizedSmallKltTail : toStepSequence.IsStabilizedSmallKltTail

end MMP.Fourfold
