module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Singularities.Slc.NormalizedSections
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
import MMP.AlgebraicGeometry.MMP.BasepointFree.DltFloorSemiample
import MMP.AlgebraicGeometry.MMP.Surface.LcNefBigKltModel
import MMP.AlgebraicGeometry.MMP.Surface.CrepantDltModification
import MMP.AlgebraicGeometry.MMP.Surface.KltNefBigSemiample
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Singularities.CrepantBoundaryKlt
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Divisor.AlgebraicHartogsUnits
import MMP.AlgebraicGeometry.Singularities.Adjunction.ForwardDiscrepancy
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero
import MMP.AlgebraicGeometry.MMP.Abundance.NormalizedSectionDegreeZero
import MMP.AlgebraicGeometry.Singularities.Slc.NodeResidueForm
import MMP.AlgebraicGeometry.Resolution.SNCAffineLineExample
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
import MMP.RingTheory.PowerSeries.CompleteLocalRing
import MMP.AlgebraicGeometry.Singularities.Semismooth.SingularLocus
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentEffective
import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.Singularities.DltDiscrepancy
import MMP.AlgebraicGeometry.MMP.Threefold.Discrepancy
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.RingTheory.DiscreteValuationRing.Integrality
import MMP.AlgebraicGeometry.Singularities.PltFloorNormalProjective
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.Surface.DiscrepancyMultiplicity
import MMP.AlgebraicGeometry.Singularities.Surface.LogTerminalReducedBoundary
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolution
import MMP.AlgebraicGeometry.Singularities.PltCodimTwoCyclicModel
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyDictionary
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.Surface.ReducedBoundaryLc
import MMP.AlgebraicGeometry.Divisor.PrimeDivisorValuationSubring
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.MMP.Abundance.Curve.SlcPrescribedSections
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField

/-!
# Relative basepoint freeness for nef and big lc adjoint divisors on projective surfaces

Let `(X, B)` be an lc pair with effective `ℚ`-boundary `B` on a normal projective complex surface
`X`, and let `f : X ⟶ Z` be a morphism to a projective complex variety. If `K_X + B` is nef and
big over `Z`, then it is semiample over `Z`: some positive multiple `m (K_X + B)` is Cartier and
`f^* f_* 𝒪_X(m (K_X + B)) → 𝒪_X(m (K_X + B))` is surjective.

## Main results

* `MMP.Fourfold.QDivisor.isRelativelySemiample_of_isLcPair_of_isRelativelyNef_of_isRelativelyBig`:
  the theorem above.

## Implementation notes

Source and base are both globally projective over `ℂ`. The pair is `MMP.Mori.IsLcPair` with
canonical divisor `K` of dimension `2`, and `B` is required effective, as for a boundary.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.SurfaceProjectiveLcNefBigSemiample

section ClosedSubscheme

open CategoryTheory AlgebraicGeometry MMP.Mori

/-! ### Closed integral subschemes -/

/-- A closed immersion `ι : Y ⟶ W` from an integral scheme is, up to isomorphism over `W`, the
closed immersion of the reduced closure of `ι(η_Y)`. -/
private theorem exists_iso_curveSubschemeAt_of_isClosedImmersion {Y W : Scheme.{0}} [IsIntegral Y]
    (ι : Y ⟶ W) [IsClosedImmersion ι] :
    ∃ e : Y ≅ curveSubschemeAt (ι (genericPoint Y)), e.hom ≫ curveSubschemeAtι _ = ι := by
  have hrange : closure (Set.range ι) = closure {ι (genericPoint Y)} := by
    rw [ι.isClosedEmbedding.isClosed_range.closure_eq, ← Set.image_singleton,
      ι.isClosedEmbedding.closure_image_eq, (genericPoint_spec Y).def, Set.image_univ]
  have hker : ι.ker = (curveSubschemeAtι (ι (genericPoint Y))).ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    unfold curveSubschemeAtι
    rw [Scheme.IdealSheafData.ker_subschemeι]
    congr 1
    ext1
    simp only [TopologicalSpace.Closeds.coe_closure]
    exact hrange
  have : IsIso (IsClosedImmersion.lift (curveSubschemeAtι (ι (genericPoint Y))) ι hker.ge) :=
    IsClosedImmersion.isIso_of_ker_eq ι (curveSubschemeAtι _) _
      (IsClosedImmersion.lift_fac _ _ _) hker
  exact ⟨asIso (IsClosedImmersion.lift (curveSubschemeAtι (ι (genericPoint Y))) ι hker.ge),
    IsClosedImmersion.lift_fac _ _ _⟩

end ClosedSubscheme

/-! ### Residue adjunction on the whole floor of a dlt surface pair -/

namespace Residue

open CategoryTheory AlgebraicGeometry MMP MMP.Fourfold MMP.Mori MMP.Flips

section Generators

variable {k : Type} [Field k] {S C : Scheme.{0}} (sS : S ⟶ Spec (.of k))
  [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] (B : QDivisor S) (ι : C ⟶ S)
  {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
  (N : NormalizationComponents (ι ≫ sS) hC)

/-- The components of the normalization of the floor are the components of `⌊B⌋`, meeting
transversally in nodes: each maps to `S` by a closed immersion onto a prime divisor of
coefficient one in `B`, different components have different images and every prime divisor of
coefficient one is the image of one; two different components meet only over double normal
crossing points of `C`, no three meet, and over a node functions on the two branches with the
same value lift to a function near the node. -/
private structure IsFloorNormalization : Prop where
  isClosedImmersion : ∀ i, IsClosedImmersion (N.n i ≫ ι)
  exists_primeDivisor : ∀ i, ∃ Γ : Mori.PrimeDivisor S, B.coeff Γ = 1 ∧
    (N.n i ≫ ι).base (genericPoint (N.X i)) = Γ.genericPoint
  exists_index : ∀ Γ : Mori.PrimeDivisor S, B.coeff Γ = 1 →
    ∃ i, (N.n i ≫ ι).base (genericPoint (N.X i)) = Γ.genericPoint
  injective : Function.Injective fun i => (N.n i ≫ ι).base (genericPoint (N.X i))
  isDoubleNormalCrossingPoint : ∀ (i j : N.ι) (y : N.X i) (y' : N.X j),
    (N.n i ≫ ι).base y = (N.n j ≫ ι).base y' → i ≠ j →
      IsDoubleNormalCrossingPoint (ι ≫ sS) 1 ((N.n i).base y)
  atMostTwo : ∀ (i j l : N.ι) (y : N.X i) (y' : N.X j) (y'' : N.X l),
    (N.n i ≫ ι).base y = (N.n j ≫ ι).base y' → (N.n i ≫ ι).base y = (N.n l ≫ ι).base y'' →
      i = j ∨ j = l ∨ i = l
  nodeLift : ∀ (i j : N.ι) (P : Mori.PrimeDivisor (N.X i)) (P' : Mori.PrimeDivisor (N.X j))
    (hPP' : (N.n i ≫ ι).base P.genericPoint = (N.n j ≫ ι).base P'.genericPoint), i ≠ j →
    ∀ (g : (N.X i).functionField) (g' : (N.X j).functionField) (a : k),
      g ∈ Set.range (algebraMap ((N.X i).presheaf.stalk P.genericPoint) (N.X i).functionField) →
      g' ∈ Set.range (algebraMap ((N.X j).presheaf.stalk P'.genericPoint) (N.X j).functionField) →
      (letI := functionFieldAlgebra (N.n i ≫ ι ≫ sS);
        g - algebraMap k _ a = 0 ∨ 1 ≤ (N.X i).ord (g - algebraMap k _ a) P.genericPoint) →
      (letI := functionFieldAlgebra (N.n j ≫ ι ≫ sS);
        g' - algebraMap k _ a = 0 ∨ 1 ≤ (N.X j).ord (g' - algebraMap k _ a) P'.genericPoint) →
      ∃ (W : S.Opens) (hW : (N.n i ≫ ι).base P.genericPoint ∈ W) (h : Γ(S, W)),
        haveI : Nonempty ((N.n i ≫ ι) ⁻¹ᵁ W) := ⟨⟨P.genericPoint, hW⟩⟩
        haveI : Nonempty ((N.n j ≫ ι) ⁻¹ᵁ W) :=
          ⟨⟨P'.genericPoint, show (N.n j ≫ ι).base P'.genericPoint ∈ W from hPP' ▸ hW⟩⟩
        (N.X i).germToFunctionField _ ((N.n i ≫ ι).app W h) = g ∧
          (N.X j).germToFunctionField _ ((N.n j ≫ ι).app W h) = g'

/-- Local residue generators of `𝒪_S(m(K_S + B))` along the floor `C`: near every point of `S`
there is a form `τ` generating `𝒪_S(m(K_S + B))` whose residues along the components `Cᵢ` of
the normalization of `C` are nonzero, have order `-m Δᵢ` at every point of `Cᵢ` over the
neighbourhood (`Δᵢ` the boundary `MMP.Flips.NormalizationComponents.componentBoundaryCoeff`),
and have equal leading coefficients at the two points over a node. -/
private def HasResidueGenerators (Δ : QWeilDivisor C) (m : ℕ) : Prop :=
  ∀ x : S, ∃ V : S.Opens, x ∈ V ∧ ∃ τ : RationalPluriForms sS 2 m, GeneratesOn B m V τ ∧
    (∀ i : N.ι, (Set.range (N.n i ≫ ι).base ∩ V).Nonempty →
      ∃ ρ, IsPoincareResidue sS (N.n i ≫ ι) 1 m τ ρ) ∧
    (∀ (i : N.ι) (ρ : RationalPluriForms ((N.n i ≫ ι) ≫ sS) 1 m),
      (Set.range (N.n i ≫ ι).base ∩ V).Nonempty → IsPoincareResidue sS (N.n i ≫ ι) 1 m τ ρ →
      ρ ≠ 0 ∧ ∀ P : Mori.PrimeDivisor (N.X i), ι.base ((N.n i).base P.genericPoint) ∈ V →
        ((P.ordForm (k := k) ρ : ℤ) : ℚ) = -(m * N.componentBoundaryCoeff Δ i P)) ∧
    ∀ (i j : N.ι) (P : Mori.PrimeDivisor (N.X i)) (P' : Mori.PrimeDivisor (N.X j))
      (ρ : RationalPluriForms ((N.n i ≫ ι) ≫ sS) 1 m)
      (ρ' : RationalPluriForms ((N.n j ≫ ι) ≫ sS) 1 m),
      IsPoincareResidue sS (N.n i ≫ ι) 1 m τ ρ → IsPoincareResidue sS (N.n j ≫ ι) 1 m τ ρ' →
      (N.n i).base P.genericPoint = (N.n j).base P'.genericPoint →
      ι.base ((N.n i).base P.genericPoint) ∈ V →
      IsDoubleNormalCrossingPoint (ι ≫ sS) 1 ((N.n i).base P.genericPoint) →
      (⟨i, P.genericPoint⟩ : Σ i, N.X i) ≠ ⟨j, P'.genericPoint⟩ →
      ∃ c : k, N.IsLeadingCoeff i P ρ c ∧ N.IsLeadingCoeff j P' ρ' c

end Generators

/-! ### Orders in discrete valuation stalks -/

/-- A unit of the stalk at a point of coheight one has order zero. -/
private theorem ord_algebraMap_eq_zero_of_isUnit {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {z : X} (hz : Order.coheight z = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk z)] {u : X.presheaf.stalk z} (hu : IsUnit u) :
    X.ord (algebraMap _ X.functionField u) z = 0 :=
  (Scheme.ord_eq_iff hz (hu.map _).ne_zero).mpr (Ring.ordFrac_of_isUnit hu)

/-- A nonzero element of the maximal ideal of a discrete valuation stalk at a point of coheight
one has order at least one. -/
private theorem one_le_ord_of_mem_maximalIdeal' {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {z : X} (hz : Order.coheight z = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk z)] {a : X.presheaf.stalk z}
    (ha : a ∈ IsLocalRing.maximalIdeal _) (ha0 : algebraMap _ X.functionField a ≠ 0) :
    1 ≤ X.ord (algebraMap _ X.functionField a) z := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.mem_span_singleton'] at ha
  obtain ⟨b, rfl⟩ := ha
  have hϖ0 : algebraMap _ X.functionField ϖ ≠ 0 := by
    rw [map_mul] at ha0; exact right_ne_zero_of_mul ha0
  have hb0 : algebraMap _ X.functionField b ≠ 0 := by
    rw [map_mul] at ha0; exact left_ne_zero_of_mul ha0
  have h1 : X.ord (algebraMap _ X.functionField ϖ) z = 1 :=
    (Scheme.ord_eq_iff hz hϖ0).mpr (Ring.ordFrac_irreducible hϖ)
  have h2 : 0 ≤ X.ord (algebraMap _ X.functionField b) z :=
    (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hz hb0).mp ⟨b, rfl⟩
  rw [map_mul, Scheme.ord_mul hb0 hϖ0, h1]
  omega

/-! ### Vanishing to a given order -/

section OrdGE

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {k : Type} [Field k] [PerfectField k] {sX : X ⟶ Spec (.of k)} {d : ℕ} {e : ℤ}

/-- `τ` is zero or has order at least `n` along `P`. -/
private def OrdGE (P : Mori.PrimeDivisor X) (n : ℤ) (τ : RationalPluriForms sX d e) : Prop :=
  τ = 0 ∨ n ≤ P.ordForm τ

private theorem OrdGE.zero (P : Mori.PrimeDivisor X) (n : ℤ) :
    OrdGE P n (0 : RationalPluriForms sX d e) :=
  Or.inl rfl

private theorem OrdGE.mono {P : Mori.PrimeDivisor X} {n n' : ℤ} {τ : RationalPluriForms sX d e}
    (h : OrdGE P n τ) (hn : n' ≤ n) : OrdGE P n' τ :=
  h.imp_right hn.trans

private theorem OrdGE.add {P : Mori.PrimeDivisor X} {n : ℤ} {τ τ' : RationalPluriForms sX d e}
    (h : OrdGE P n τ) (h' : OrdGE P n τ') : OrdGE P n (τ + τ') := by
  rcases h with rfl | h
  · rwa [zero_add]
  rcases h' with rfl | h'
  · rw [add_zero]; exact Or.inr h
  by_cases h0 : τ + τ' = 0
  · exact Or.inl h0
  exact Or.inr (le_trans (le_min h h') (P.min_ordForm_le_ordForm_add h0))

private theorem OrdGE.neg {P : Mori.PrimeDivisor X} {n : ℤ} {τ : RationalPluriForms sX d e}
    (h : OrdGE P n τ) : OrdGE P n (-τ) := by
  rcases h with rfl | h
  · rw [neg_zero]; exact Or.inl rfl
  · exact Or.inr (by rwa [P.ordForm_neg])

private theorem OrdGE.sub {P : Mori.PrimeDivisor X} {n : ℤ} {τ τ' : RationalPluriForms sX d e}
    (h : OrdGE P n τ) (h' : OrdGE P n τ') : OrdGE P n (τ - τ') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

private theorem OrdGE.smul [LocallyOfFiniteType sX]
    (htr : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {P : Mori.PrimeDivisor X} {n a : ℤ} {τ : RationalPluriForms sX d e} (h : OrdGE P n τ)
    {f : X.functionField} (hf : f = 0 ∨ a ≤ X.ord f P.genericPoint) :
    OrdGE P (a + n) (f • τ) := by
  rcases h with rfl | h
  · rw [smul_zero]; exact Or.inl rfl
  rcases hf with rfl | hf
  · rw [zero_smul]; exact Or.inl rfl
  by_cases hf0 : f = 0
  · rw [hf0, zero_smul]; exact Or.inl rfl
  by_cases hτ0 : τ = 0
  · rw [hτ0, smul_zero]; exact Or.inl rfl
  refine Or.inr ?_
  rw [P.ordForm_smul htr hf0 hτ0]
  omega

/-- A form of order exactly `n` times a function vanishing to order `≥ n + a` gives order
`≥ a` for the function. -/
private theorem le_ord_of_ordGE_smul [LocallyOfFiniteType sX]
    (htr : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {P : Mori.PrimeDivisor X} {n a : ℤ} {τ : RationalPluriForms sX d e} (hτ0 : τ ≠ 0)
    (hτ : P.ordForm τ = n) {f : X.functionField} (h : OrdGE P (a + n) (f • τ)) :
    f = 0 ∨ a ≤ X.ord f P.genericPoint := by
  rcases h with h | h
  · exact Or.inl ((smul_eq_zero.mp h).resolve_right hτ0)
  by_cases hf0 : f = 0
  · exact Or.inl hf0
  refine Or.inr ?_
  rw [P.ordForm_smul htr hf0 hτ0, hτ] at h
  omega

end OrdGE

/-! ### Logarithmic forms on a normal curve -/

section DLog

variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}

/-- On `Fin 1`, updating a constant family gives a constant family. -/
private theorem update_const_fin_one {α : Type*} (a x : α) :
    Function.update (fun _ : Fin 1 => a) 0 x = fun _ => x :=
  funext fun j => by fin_cases j; simp

/-- **Independence of the local parameter.** On a normal curve, for two local parameters
`z, z'` at `P` the difference `(dz'/z')^m - (dz/z)^m` vanishes or has a pole of order `< m`
along `P`. -/
private theorem ordGE_dlogPow_sub (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 1)
    (P : Mori.PrimeDivisor X) {z z' : X.functionField} (hz : X.ord z P.genericPoint = 1)
    (hz' : X.ord z' P.genericPoint = 1) (m : ℕ) :
    OrdGE P (1 - m) (dlogPow sX z' m - dlogPow sX z m) := by
  letI := functionFieldAlgebra sX
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd1 : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  have htr := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd1
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hz'0 : z' ≠ 0 := by rintro rfl; simp at hz'
  set u := z' * z⁻¹ with hudef
  have hu0 : u ≠ 0 := mul_ne_zero hz'0 (inv_ne_zero hz0)
  have hord_inv : ∀ {f : X.functionField}, f ≠ 0 → X.ord f⁻¹ P.genericPoint =
      -X.ord f P.genericPoint := fun {f} hf => by
    have := Scheme.ord_mul (x := P.genericPoint) hf (inv_ne_zero hf)
    rw [mul_inv_cancel₀ hf] at this
    have h1 : X.ord (1 : X.functionField) P.genericPoint = 0 := by
      have := Scheme.ord_mul (x := P.genericPoint) (one_ne_zero (α := X.functionField))
        one_ne_zero
      rw [mul_one] at this; omega
    omega
  have hu : X.ord u P.genericPoint = 0 := by
    rw [hudef, Scheme.ord_mul hz'0 (inv_ne_zero hz0), hord_inv hz0, hz, hz']; omega
  have hzu : z' = u * z := by rw [hudef, mul_assoc, inv_mul_cancel₀ hz0, mul_one]
  -- the logarithmic `1`-forms
  let η : X.functionField → ⋀[X.functionField]^1 Ω[X.functionField⁄k] := fun w =>
    w⁻¹ • exteriorPower.ιMulti X.functionField 1 fun _ => KaehlerDifferential.D k _ w
  have hdl : ∀ (w : X.functionField) (n : ℕ),
      dlogPow sX w n = (PiTensorProduct.tprod X.functionField fun _ : Fin n => η w :
        RationalPluriForms sX 1 n) := fun _ _ => rfl
  let δ : RationalPluriForms sX 1 (1 : ℕ) := PiTensorProduct.tprod X.functionField
    fun _ : Fin 1 => exteriorPower.ιMulti X.functionField 1 fun _ =>
      KaehlerDifferential.D k X.functionField u
  -- `dz'/z' = dz/z + du/u`
  have hη : η z' = η z + u⁻¹ • exteriorPower.ιMulti X.functionField 1 fun _ =>
      KaehlerDifferential.D k X.functionField u := by
    have hD : KaehlerDifferential.D k X.functionField z' =
        u • KaehlerDifferential.D k X.functionField z +
          z • KaehlerDifferential.D k X.functionField u := by
      rw [hzu, Derivation.leibniz]
    have hlin : ∀ (a b : Ω[X.functionField⁄k]),
        exteriorPower.ιMulti X.functionField 1 (fun _ => a + b) =
          exteriorPower.ιMulti X.functionField 1 (fun _ => a) +
            exteriorPower.ιMulti X.functionField 1 (fun _ => b) := fun a b => by
      have := (exteriorPower.ιMulti X.functionField 1).map_update_add (fun _ => a) 0 a b
      simpa only [update_const_fin_one] using this
    have hsm : ∀ (c : X.functionField) (a : Ω[X.functionField⁄k]),
        exteriorPower.ιMulti X.functionField 1 (fun _ => c • a) =
          c • exteriorPower.ιMulti X.functionField 1 (fun _ => a) := fun c a => by
      have := (exteriorPower.ιMulti X.functionField 1).map_update_smul (fun _ => a) 0 c a
      simpa only [update_const_fin_one] using this
    change z'⁻¹ • _ = z⁻¹ • _ + _
    rw [hD, hlin, hsm, hsm, smul_add, smul_smul, smul_smul, hzu, mul_inv, mul_comm u⁻¹ z⁻¹,
      mul_assoc, inv_mul_cancel₀ hu0, mul_one, mul_comm z⁻¹ u⁻¹, mul_assoc,
      inv_mul_cancel₀ hz0, mul_one]
  have hlin1 : ∀ (a b : ⋀[X.functionField]^1 Ω[X.functionField⁄k]),
      (PiTensorProduct.tprod X.functionField fun _ : Fin 1 => a + b :
        RationalPluriForms sX 1 (1 : ℕ)) =
        PiTensorProduct.tprod X.functionField (fun _ : Fin 1 => a) +
          PiTensorProduct.tprod X.functionField (fun _ : Fin 1 => b) := fun a b => by
    have := (PiTensorProduct.tprod X.functionField (s := fun _ : Fin 1 =>
      ⋀[X.functionField]^1 Ω[X.functionField⁄k])).map_update_add (fun _ => a) 0 a b
    simpa only [update_const_fin_one] using this
  have hsm1 : ∀ (c : X.functionField) (a : ⋀[X.functionField]^1 Ω[X.functionField⁄k]),
      (PiTensorProduct.tprod X.functionField fun _ : Fin 1 => c • a :
        RationalPluriForms sX 1 (1 : ℕ)) =
        c • PiTensorProduct.tprod X.functionField (fun _ : Fin 1 => a) := fun c a => by
    have := (PiTensorProduct.tprod X.functionField (s := fun _ : Fin 1 =>
      ⋀[X.functionField]^1 Ω[X.functionField⁄k])).map_update_smul (fun _ => a) 0 c a
    simpa only [update_const_fin_one] using this
  have h1 : dlogPow sX z' 1 = dlogPow sX z 1 + u⁻¹ • δ := by
    rw [hdl, hdl, hη, hlin1, hsm1 u⁻¹]
    rfl
  -- write `du/u` as a multiple of `dz/z`
  obtain ⟨hω0, hωP⟩ := MMP.Flips.ordForm_dlogPow_one_of_ord_eq_one hX hdim P z hz
  have hrank : Module.finrank X.functionField (RationalPluriForms sX 1 (1 : ℕ)) = 1 := by
    obtain ⟨b₀⟩ := MMP.Fourfold.exists_basis_topForms (sX := sX) (d := 1) hd1
    let bb : Module.Basis Unit X.functionField (RationalPluriForms sX 1 (1 : ℕ)) :=
      ZTensorPower.basis b₀ ((1 : ℕ) : ℤ)
    rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]
  obtain ⟨ψ, hψ⟩ := (finrank_eq_one_iff_of_nonzero' _ hω0).mp hrank (u⁻¹ • δ)
  have hδ : OrdGE P 0 δ := by
    by_cases hδ0 : δ = 0
    · exact Or.inl hδ0
    · exact Or.inr (MMP.Flips.zero_le_ordForm_d hX hdim P u hu.ge δ rfl hδ0)
  have hψ1 : ψ = 0 ∨ 1 ≤ X.ord ψ P.genericPoint := by
    have h2 : OrdGE P (0 + 0) (u⁻¹ • δ) := hδ.smul htr (Or.inr (by rw [hord_inv hu0, hu]; rfl))
    rw [← hψ] at h2
    exact le_ord_of_ordGE_smul htr hω0 hωP (by simpa using h2)
  -- `η z' = φ η z` with `φ = 1 + ψ`
  have hφ : η z' = (1 + ψ) • η z := by
    apply MMP.Fourfold.tprod_fin_one_injective (F := X.functionField)
    change dlogPow sX z' 1 = PiTensorProduct.tprod _ (fun _ : Fin 1 => (1 + ψ) • η z)
    rw [hsm1, add_smul, one_smul, h1, ← hψ]
    rfl
  have hpow : dlogPow sX z' m = (1 + ψ) ^ m • dlogPow sX z m := by
    rw [hdl, hdl, hφ]
    have := (PiTensorProduct.tprod X.functionField (s := fun _ : Fin m =>
      ⋀[X.functionField]^1 Ω[X.functionField⁄k])).map_smul_univ (fun _ => 1 + ψ) (fun _ => η z)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact this
  have hsub : dlogPow sX z' m - dlogPow sX z m = ((1 + ψ) ^ m - 1) • dlogPow sX z m := by
    rw [hpow, sub_smul, one_smul]
  obtain ⟨hD0, hDord⟩ := MMP.Flips.ordForm_dlogPow_eq_mul hX hdim z hω0 m
  have hD : OrdGE P (-(m : ℤ)) (dlogPow sX z m) :=
    Or.inr (by rw [hDord P, hωP]; omega)
  -- `(1 + ψ)^m - 1` vanishes at `P`
  have hf : (1 + ψ) ^ m - 1 = 0 ∨ 1 ≤ X.ord ((1 + ψ) ^ m - 1) P.genericPoint := by
    rcases hψ1 with rfl | hψ1
    · left; rw [add_zero, one_pow, sub_self]
    have hψ0 : ψ ≠ 0 := by rintro rfl; simp at hψ1
    have := P.isDiscreteValuationRing_localRing
    have hcoh := P.coheight_genericPoint
    obtain ⟨a, rfl⟩ := (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hcoh hψ0).mpr
      (by omega)
    have ha : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk P.genericPoint) := by
      by_contra ha
      rw [ord_algebraMap_eq_zero_of_isUnit hcoh (IsLocalRing.notMem_maximalIdeal.mp ha)] at hψ1
      omega
    have hm : (1 + a) ^ m - 1 ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk P.genericPoint) := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_add, map_one,
        (IsLocalRing.residue_eq_zero_iff a).mpr ha, add_zero, one_pow, sub_self]
    have he : (1 + algebraMap _ X.functionField a) ^ m - 1 =
        algebraMap (X.presheaf.stalk P.genericPoint) X.functionField ((1 + a) ^ m - 1) := by
      simp
    rw [he]
    by_cases h0 : algebraMap (X.presheaf.stalk P.genericPoint) X.functionField
        ((1 + a) ^ m - 1) = 0
    · exact Or.inl h0
    · exact Or.inr (one_le_ord_of_mem_maximalIdeal' hcoh hm h0)
  rw [hsub]
  exact (hD.smul htr hf).mono (by omega)

end DLog

/-! ### From residue generators to the sheaf statements -/

section Sections

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {S C : Scheme.{0}}
  {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
  [LocallyOfFiniteType sS] {B : QDivisor S} {ι : C ⟶ S} [IsClosedImmersion ι]
  {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
  {N : NormalizationComponents (ι ≫ sS) hC} {Δ : QWeilDivisor C} {m : ℕ} {Gm : Divisor S}

/-- Rational `m`-canonical forms on a surface form a line over the function field. -/
private theorem finrank_rationalPluriForms (hdim : topologicalKrullDim S = 2) :
    Module.finrank S.functionField (RationalPluriForms sS 2 m) = 1 := by
  let := functionFieldAlgebra sS
  obtain ⟨b₀⟩ := MMP.Fourfold.exists_basis_topForms (sX := sS) (d := 2) (by rw [hdim]; rfl)
  let bb : Module.Basis Unit S.functionField (RationalPluriForms sS 2 m) :=
    ZTensorPower.basis b₀ m
  rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]

/-- **Sections near a generator.** If `τ₀` generates `𝒪_S(m(K_S + B))` on `V`, every section
over a nonempty open `W ⊆ V` is `h τ₀` with `h` regular on `W`. -/
private theorem exists_eq_smul_of_generatesOn (hdim : topologicalKrullDim S = 2)
    (hGm : Divisor.toQDivisor Gm = (m : ℚ) • B) {V W : S.Opens} {τ₀ : RationalPluriForms sS 2 m}
    (hgen : GeneratesOn B m V τ₀) (hWV : W ≤ V) [Nonempty W] {τ : RationalPluriForms sS 2 m}
    (hτ : τ ∈ pluricanonicalSections sS 2 m Gm W) :
    ∃ h : Γ(S, W), τ = S.germToFunctionField W h • τ₀ := by
  let := functionFieldAlgebra sS
  obtain ⟨f, hf⟩ := (finrank_eq_one_iff_of_nonzero' τ₀ hgen.1).mp
    (finrank_rationalPluriForms (m := m) hdim) τ
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, by rw [← hf, map_zero, zero_smul]⟩
  have htr := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hdim
  obtain ⟨h, hh⟩ := MMP.Threefold.Bridges.exists_germToFunctionField_eq_of_forall_zero_le_ord W f
    fun Γ hΓ => by
      have hτ0 : τ ≠ 0 := by rw [← hf]; exact smul_ne_zero hf0 hgen.1
      have h1 := hτ.2 Γ hΓ hτ0
      have h2 := hgen.2 Γ ⟨hΓ.choose, hΓ.choose_spec.1, hWV hΓ.choose_spec.2⟩
      have h3 : Γ.ordForm τ = S.ord f Γ.genericPoint + Γ.ordForm τ₀ := by
        rw [← hf]; exact Γ.ordForm_smul htr hf0 hgen.1
      have h4 : (Gm.coeff Γ : ℚ) = m * B.coeff Γ := by
        have := congrArg (fun D : QDivisor S => D.coeff Γ) hGm
        simpa [Divisor.coeff_toQDivisor] using this
      have h5 : (0 : ℚ) ≤ (Γ.ordForm τ : ℚ) + Gm.coeff Γ := by exact_mod_cast h1
      rw [h3, h4] at h5
      push_cast at h5
      have : (0 : ℚ) ≤ S.ord f Γ.genericPoint := by linarith
      exact_mod_cast this
  exact ⟨h, by rw [hh, hf]⟩

/-- The residue of `h τ`, for `h` regular on an open `W` containing the generic point of the image
of `T`, is `h|_T Res τ`. -/
private theorem isPoincareResidue_germToFunctionField_smul {T : Scheme.{0}} [IsIntegral T]
    {j : T ⟶ S} {n : ℕ} {τ : RationalPluriForms sS (n + 1) m}
    {ρ : RationalPluriForms (j ≫ sS) n m} (h : IsPoincareResidue sS j n m τ ρ) {W : S.Opens}
    (hW : j.base (genericPoint T) ∈ W) (f : Γ(S, W)) :
    haveI : Nonempty W := ⟨⟨_, hW⟩⟩
    haveI : Nonempty (j ⁻¹ᵁ W) := ⟨⟨genericPoint T, hW⟩⟩
    IsPoincareResidue sS j n m (S.germToFunctionField W f • τ)
      (T.germToFunctionField (j ⁻¹ᵁ W) (j.app W f) • ρ) := by
  haveI : Nonempty W := ⟨⟨_, hW⟩⟩
  obtain ⟨t, g, x, ht, hτ, hρ⟩ := h
  refine ⟨t, S.presheaf.germ W _ hW f * g, x, ht, ?_, ?_⟩
  · subst hτ
    rw [map_mul, mul_smul, Scheme.algebraMap_germ_eq_germToFunctionField]
    rfl
  · subst hρ
    rw [map_mul, mul_smul]
    congr 1
    exact (Scheme.Hom.germ_stalkMap_apply j W (genericPoint T) hW f).symm

/-- A regular function has nonnegative order along every prime divisor meeting its domain. -/
private theorem zero_le_ord_germToFunctionField {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {W : X.Opens} [Nonempty W] (f : Γ(X, W))
    (P : Mori.PrimeDivisor X) (hP : P.genericPoint ∈ W) :
    0 ≤ X.ord (X.germToFunctionField W f) P.genericPoint := by
  rcases eq_or_ne (X.germToFunctionField W f) 0 with h0 | h0
  · rw [h0]
    have := congrFun Scheme.ord_zero P.genericPoint
    simp only [Pi.zero_apply] at this
    omega
  exact (MMP.Intersection.exists_germToFunctionField_eq_iff_forall_zero_le_ord W h0).mp ⟨f, rfl⟩
    P ⟨P.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, hP⟩

/-- Sections of `𝒪_S(mK_S + G)` restrict to smaller nonempty opens. -/
private theorem mem_pluricanonicalSections_of_le {d : ℕ} {G : Divisor S} {U W : S.Opens}
    {τ : RationalPluriForms sS d m} (hτ : τ ∈ pluricanonicalSections sS d m G U) (hWU : W ≤ U)
    [Nonempty W] : τ ∈ pluricanonicalSections sS d m G W :=
  ⟨fun hW => absurd hW (by
      obtain ⟨⟨x, hx⟩⟩ := (inferInstance : Nonempty W)
      intro h; rw [h] at hx; exact hx),
    fun Γ ⟨x, hxΓ, hxW⟩ hτ0 => hτ.2 Γ ⟨x, hxΓ, hWU hxW⟩ hτ0⟩

/-- The image of a closed immersion of an integral scheme onto a prime divisor is its support. -/
private theorem range_eq_support {T : Scheme.{0}} [IsIntegral T] (j : T ⟶ S) [IsClosedImmersion j]
    (Γ : Mori.PrimeDivisor S) (hΓ : j.base (genericPoint T) = Γ.genericPoint) :
    Set.range j.base = (Γ.support : Set S) := by
  have hs : (Γ.support : Set S) = closure {Γ.genericPoint} :=
    AlgebraicGeometry.PrimeDivisor.support_eq_closure Γ
  have hc : closure ({genericPoint T} : Set T) = Set.univ := genericPoint_spec T
  rw [hs, ← hΓ, ← Set.image_univ, ← hc, ← Set.image_singleton]
  exact (j.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous
    j.base.hom.continuous _).symm

/-- The components of the floor are curves: their function fields have transcendence degree one. -/
private theorem toNat_trdeg_component (hdim : topologicalKrullDim S = 2)
    (hfl : IsFloorNormalization sS B ι N) (i : N.ι) :
    (letI := functionFieldAlgebra (N.n i ≫ ι ≫ sS);
      (Algebra.trdeg k (N.X i).functionField).toNat) = 1 := by
  haveI := hfl.isClosedImmersion i
  obtain ⟨P, -, hP⟩ := hfl.exists_primeDivisor i
  haveI : LocallyOfFiniteType (N.n i ≫ ι ≫ sS) := (N.isNormalVariety i).1.toLocallyOfFiniteType
  have hdim' : topologicalKrullDim S = ((1 : ℕ) : WithBot ℕ∞) + 1 := by rw [hdim]; rfl
  have hdimi := MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support sS hdim' (N.n i ≫ ι) P
    (range_eq_support (N.n i ≫ ι) P hP)
  exact toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := N.n i ≫ ι ≫ sS) hdimi

/-- **Residues near a generator.** Near a point `x` of `U`, a section `τ` over `U` is `h τ₀` for
a generator `τ₀` on `V ∋ x` and `h` regular on `U ∩ V`; its residue along every integral closed
subscheme whose generic point is that of a prime divisor and lies in `U ∩ V` is
`h|_T Res τ₀`. -/
private theorem exists_residue_eq_smul (hdim : topologicalKrullDim S = 2)
    (hGm : Divisor.toQDivisor Gm = (m : ℚ) • B)
    {U V : S.Opens} {x : S} (hxU : x ∈ U) (hxV : x ∈ V) {τ₀ : RationalPluriForms sS 2 m}
    (hgen : GeneratesOn B m V τ₀) {τ : RationalPluriForms sS 2 m}
    (hτ : τ ∈ pluricanonicalSections sS 2 m Gm U) :
    haveI : Nonempty (U ⊓ V : S.Opens) := ⟨⟨x, hxU, hxV⟩⟩
    ∃ h : Γ(S, U ⊓ V), τ = S.germToFunctionField (U ⊓ V) h • τ₀ ∧
      ∀ {T : Scheme.{0}} [IsIntegral T] (j : T ⟶ S) [IsClosedImmersion j]
        (P : Mori.PrimeDivisor S), j.base (genericPoint T) = P.genericPoint →
        ∀ (ρ₀ ρ : RationalPluriForms (j ≫ sS) 1 m) (hη : j.base (genericPoint T) ∈ U ⊓ V),
        IsPoincareResidue sS j 1 m τ₀ ρ₀ → IsPoincareResidue sS j 1 m τ ρ →
        haveI : Nonempty (j ⁻¹ᵁ (U ⊓ V)) := ⟨⟨genericPoint T, hη⟩⟩
        ρ = T.germToFunctionField (j ⁻¹ᵁ (U ⊓ V)) (j.app _ h) • ρ₀ := by
  haveI : Nonempty (U ⊓ V : S.Opens) := ⟨⟨x, hxU, hxV⟩⟩
  obtain ⟨h, rfl⟩ := exists_eq_smul_of_generatesOn hdim hGm hgen inf_le_right
    (mem_pluricanonicalSections_of_le hτ inf_le_left)
  refine ⟨h, rfl, fun j _ P hP ρ₀ ρ hη hρ₀ hρ => ?_⟩
  exact MMP.Fourfold.isPoincareResidue_unique hP hρ
    (isPoincareResidue_germToFunctionField_smul hρ₀ hη h)

/-- A generator of `𝒪_S(m(K_S + B))` on a nonempty open is a section there. -/
private theorem mem_pluricanonicalSections_of_generatesOn
    (hGm : Divisor.toQDivisor Gm = (m : ℚ) • B) {V : S.Opens} [Nonempty V]
    {τ : RationalPluriForms sS 2 m} (hτ : GeneratesOn B m V τ) :
    τ ∈ pluricanonicalSections sS 2 m Gm V := by
  refine ⟨fun hV => absurd hV (by
      obtain ⟨⟨x, hx⟩⟩ := (inferInstance : Nonempty V)
      intro h; rw [h] at hx; exact hx), fun Γ hΓ _ => ?_⟩
  have h1 := hτ.2 Γ hΓ
  have h2 : (Gm.coeff Γ : ℚ) = m * B.coeff Γ := by
    have := congrArg (fun G : QDivisor S => G.coeff Γ) hGm
    simpa [DivisorWithCoeffs.coeff_smul] using this
  have h3 : ((Γ.ordForm τ + Gm.coeff Γ : ℤ) : ℚ) = 0 := by push_cast; linarith
  have h4 : Γ.ordForm τ + Gm.coeff Γ = 0 := by exact_mod_cast h3
  exact h4.ge

/-- **Orders of residues do not depend on the generator.** If `τ` and `τ'` generate
`𝒪_S(m(K_S + B))` on `V` and `V'`, their residues along a component have the same order at every
point over `V ∩ V'`: they differ by the restriction of a unit. -/
private theorem ordForm_eq_of_generatesOn (hdim : topologicalKrullDim S = 2)
    (hGm : Divisor.toQDivisor Gm = (m : ℚ) • B) {V V' : S.Opens}
    {τ τ' : RationalPluriForms sS 2 m} (hτ : GeneratesOn B m V τ) (hτ' : GeneratesOn B m V' τ')
    {T : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] (j : T ⟶ S)
    [IsClosedImmersion j] [LocallyOfFiniteType (j ≫ sS)] (P : Mori.PrimeDivisor S)
    (hP : j.base (genericPoint T) = P.genericPoint)
    (htr : letI := functionFieldAlgebra (j ≫ sS); (Algebra.trdeg k T.functionField).toNat = 1)
    {ρ ρ' : RationalPluriForms (j ≫ sS) 1 m} (hρ : IsPoincareResidue sS j 1 m τ ρ)
    (hρ' : IsPoincareResidue sS j 1 m τ' ρ') (Q : Mori.PrimeDivisor T)
    (hQ : j.base Q.genericPoint ∈ V ⊓ V') :
    Q.ordForm ρ' = Q.ordForm ρ := by
  have hxV : j.base Q.genericPoint ∈ V := hQ.1
  have hxV' : j.base Q.genericPoint ∈ V' := hQ.2
  haveI : Nonempty V' := ⟨⟨_, hxV'⟩⟩
  haveI : Nonempty V := ⟨⟨_, hxV⟩⟩
  have hsp : j.base (genericPoint T) ⤳ j.base Q.genericPoint :=
    ((genericPoint_spec T).specializes trivial).map j.base.hom.continuous
  have hη : j.base (genericPoint T) ∈ V' ⊓ V :=
    ⟨hsp.mem_open V'.isOpen hxV', hsp.mem_open V.isOpen hxV⟩
  have hη' : j.base (genericPoint T) ∈ V ⊓ V' := ⟨hη.2, hη.1⟩
  obtain ⟨h, -, hres⟩ := exists_residue_eq_smul hdim hGm hxV' hxV hτ
    (mem_pluricanonicalSections_of_generatesOn hGm hτ')
  have hρeq := hres j P hP ρ ρ' hη hρ hρ'
  obtain ⟨h', -, hres'⟩ := exists_residue_eq_smul hdim hGm hxV hxV' hτ'
    (mem_pluricanonicalSections_of_generatesOn hGm hτ)
  have hρeq' := hres' j P hP ρ' ρ hη' hρ' hρ
  haveI : Nonempty (j ⁻¹ᵁ (V' ⊓ V)) := ⟨⟨genericPoint T, hη⟩⟩
  haveI : Nonempty (j ⁻¹ᵁ (V ⊓ V')) := ⟨⟨genericPoint T, hη'⟩⟩
  set a := T.germToFunctionField (j ⁻¹ᵁ (V' ⊓ V)) (j.app _ h) with ha
  set b := T.germToFunctionField (j ⁻¹ᵁ (V ⊓ V')) (j.app _ h') with hb
  by_cases hρ0 : ρ = 0
  · have : ρ' = 0 := by rw [hρeq, hρ0, smul_zero]
    rw [this, hρ0]
  have hab : (b * a) • ρ = (1 : T.functionField) • ρ := by
    rw [one_smul, mul_smul, ← hρeq, ← hρeq']
  have hab1 : b * a = 1 := by
    have := sub_eq_zero.mpr hab
    rw [← sub_smul, smul_eq_zero] at this
    exact sub_eq_zero.mp (this.resolve_right hρ0)
  have ha0 : a ≠ 0 := fun h0 => by rw [h0, mul_zero] at hab1; exact zero_ne_one hab1
  have hb0 : b ≠ 0 := fun h0 => by rw [h0, zero_mul] at hab1; exact zero_ne_one hab1
  have hQW : Q.genericPoint ∈ j ⁻¹ᵁ (V' ⊓ V) := show j.base Q.genericPoint ∈ V' ⊓ V from
    ⟨hxV', hxV⟩
  have hQW' : Q.genericPoint ∈ j ⁻¹ᵁ (V ⊓ V') := show j.base Q.genericPoint ∈ V ⊓ V' from hQ
  have hQa : 0 ≤ T.ord a Q.genericPoint := zero_le_ord_germToFunctionField _ Q hQW
  have hQb : 0 ≤ T.ord b Q.genericPoint := zero_le_ord_germToFunctionField _ Q hQW'
  have hsum : T.ord b Q.genericPoint + T.ord a Q.genericPoint = 0 := by
    rw [← Scheme.ord_mul hb0 ha0, hab1, AlgebraicGeometry.ord_one']
  rw [hρeq, Q.ordForm_smul htr ha0 hρ0]
  omega

/-- A nonzero element of the maximal ideal of the local ring along a prime divisor has order at
least one. -/
private theorem one_le_ord_of_mem_maximalIdeal {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (P : Mori.PrimeDivisor X)
    {a : X.presheaf.stalk P.genericPoint} (ha : a ∈ IsLocalRing.maximalIdeal _)
    (ha0 : algebraMap _ X.functionField a ≠ 0) :
    1 ≤ X.ord (algebraMap _ X.functionField a) P.genericPoint := by
  have := P.isDiscreteValuationRing_localRing
  have hz := P.coheight_genericPoint
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk P.genericPoint)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.mem_span_singleton'] at ha
  obtain ⟨b, rfl⟩ := ha
  have hϖ0 : algebraMap _ X.functionField ϖ ≠ 0 := by
    rw [map_mul] at ha0; exact right_ne_zero_of_mul ha0
  have hb0 : algebraMap _ X.functionField b ≠ 0 := by
    rw [map_mul] at ha0; exact left_ne_zero_of_mul ha0
  have h1 : X.ord (algebraMap _ X.functionField ϖ) P.genericPoint = 1 :=
    (Scheme.ord_eq_iff hz hϖ0).mpr (Ring.ordFrac_irreducible hϖ)
  have h2 : 0 ≤ X.ord (algebraMap _ X.functionField b) P.genericPoint :=
    (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hz hb0).mp ⟨b, rfl⟩
  rw [map_mul, Scheme.ord_mul hb0 hϖ0, h1]
  omega

/-- Nonzero constants have order zero along every prime divisor. -/
private theorem ord_algebraMap_const {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} (P : Mori.PrimeDivisor X) {a : k} (ha : a ≠ 0) :
    letI := functionFieldAlgebra sX
    X.ord (algebraMap k X.functionField a) P.genericPoint = 0 := by
  letI := functionFieldAlgebra sX
  letI := stalkAlgebra sX P.genericPoint
  haveI := isScalarTower_stalk_functionField sX P.genericPoint
  rw [IsScalarTower.algebraMap_apply k (X.presheaf.stalk P.genericPoint) X.functionField]
  exact P.ord_algebraMap_of_isUnit ((IsUnit.mk0 a ha).map _)

/-- **Leading coefficients of multiples.** If `ρ` has a pole of order at most `m` at `P` with
leading coefficient `c`, and `f - a` vanishes at `P` for a constant `a`, then `f ρ` has leading
coefficient `a c`. -/
private theorem isLeadingCoeff_smul {i : N.ι} {P : Mori.PrimeDivisor (N.X i)}
    [LocallyOfFiniteType (N.n i ≫ ι ≫ sS)]
    (htr : letI := functionFieldAlgebra (N.n i ≫ ι ≫ sS);
      (Algebra.trdeg k (N.X i).functionField).toNat = 1)
    {ρ : RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m} {c : k} (hρ : N.IsLeadingCoeff i P ρ c)
    (hρ0 : ρ ≠ 0) (hρm : -(m : ℤ) ≤ P.ordForm ρ) {f : (N.X i).functionField} (a : k)
    (hfa : letI := functionFieldAlgebra (N.n i ≫ ι ≫ sS);
      f - algebraMap k _ a = 0 ∨ 1 ≤ (N.X i).ord (f - algebraMap k _ a) P.genericPoint) :
    N.IsLeadingCoeff i P (f • ρ) (a * c) := by
  letI := functionFieldAlgebra (N.n i ≫ ι ≫ sS)
  obtain ⟨z, hz, hE⟩ := hρ
  refine ⟨z, hz, ?_⟩
  set D := dlogPow (N.n i ≫ ι ≫ sS) z m
  set E := ρ - algebraMap k (N.X i).functionField c • D with hEdef
  have hsplit : f • ρ - algebraMap k (N.X i).functionField (a * c) • D =
      algebraMap k (N.X i).functionField a • E + (f - algebraMap k _ a) • ρ := by
    rw [hEdef, smul_sub, sub_smul, map_mul, mul_smul]
    abel
  rw [hsplit]
  by_cases hsum : algebraMap k (N.X i).functionField a • E + (f - algebraMap k _ a) • ρ = 0
  · exact Or.inl hsum
  refine Or.inr ?_
  -- the two summands have order at least `1 - m`
  have hA : algebraMap k (N.X i).functionField a • E ≠ 0 →
      1 - (m : ℤ) ≤ P.ordForm (algebraMap k (N.X i).functionField a • E) := by
    intro h0
    have ha : a ≠ 0 := by rintro rfl; apply h0; rw [map_zero, zero_smul]
    have hE0 : E ≠ 0 := by rintro hE0; apply h0; rw [hE0, smul_zero]
    have ha' : algebraMap k (N.X i).functionField a ≠ 0 := (map_ne_zero _).mpr ha
    rw [P.ordForm_smul htr ha' hE0, ord_algebraMap_const P ha, zero_add]
    exact hE.resolve_left hE0
  have hB : (f - algebraMap k _ a) • ρ ≠ 0 → 1 - (m : ℤ) ≤ P.ordForm ((f - algebraMap k _ a) • ρ) := by
    intro h0
    have hfa0 : f - algebraMap k _ a ≠ 0 := by rintro h; apply h0; rw [h, zero_smul]
    rw [P.ordForm_smul htr hfa0 hρ0]
    have := hfa.resolve_left hfa0
    omega
  by_cases h1 : algebraMap k (N.X i).functionField a • E = 0
  · rw [h1, zero_add] at hsum ⊢
    exact hB hsum
  by_cases h2 : (f - algebraMap k _ a) • ρ = 0
  · rw [h2, add_zero] at hsum ⊢
    exact hA hsum
  exact le_trans (le_min (hA h1) (hB h2)) (P.min_ordForm_le_ordForm_add hsum)

/-- The structure maps to the stalks commute with stalk maps of morphisms over `k`. -/
private theorem stalkMap_stalkAlgebra {T : Scheme.{0}} (j : T ⟶ S) (y : T) (a : k) :
    (j.stalkMap y).hom (@algebraMap k _ _ _ (stalkAlgebra sS (j.base y)) a) =
      @algebraMap k _ _ _ (stalkAlgebra (j ≫ sS) y) a := by
  have key := Scheme.Hom.germ_stalkMap j ⊤ y trivial
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ sS.appTop ≫ (S.presheaf.germ ⊤ (j.base y) trivial ≫
      j.stalkMap y)).hom a = ((Scheme.ΓSpecIso (.of k)).inv ≫ (sS.appTop ≫ j.appTop) ≫
      T.presheaf.germ ⊤ y trivial).hom a
  rw [key]
  rfl

/-- **Values at closed points.** If `h` is regular near a closed point `x` of `S`, there is a
constant `a` such that `h - a` vanishes at every point lying over `x`: for every morphism
`j : T ⟶ S` from a normal integral scheme and every prime divisor `P` of `T` with `j(P) = x`,
`j^*h - a` is zero or has positive order along `P`. -/
private theorem exists_const_sub_vanishes {x : S} (hx : IsClosed ({x} : Set S)) {W : S.Opens}
    (hxW : x ∈ W) (h : Γ(S, W)) :
    ∃ a : k, ∀ {T : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] (j : T ⟶ S)
      (P : Mori.PrimeDivisor T) (hP : j.base P.genericPoint = x),
      haveI : Nonempty (j ⁻¹ᵁ W) :=
        ⟨⟨P.genericPoint, show j.base P.genericPoint ∈ W from hP ▸ hxW⟩⟩
      letI := functionFieldAlgebra (j ≫ sS)
      T.germToFunctionField (j ⁻¹ᵁ W) (j.app W h) - algebraMap k _ a = 0 ∨
        1 ≤ T.ord (T.germToFunctionField (j ⁻¹ᵁ W) (j.app W h) - algebraMap k _ a)
          P.genericPoint := by
  letI := stalkAlgebra sS x
  haveI := MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sS x hx
  obtain ⟨a, ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
    (K := IsLocalRing.ResidueField (S.presheaf.stalk x))).2
    (IsLocalRing.residue _ (S.presheaf.germ W x hxW h))
  refine ⟨a, fun {T} _ _ _ j P hP => ?_⟩
  subst hP
  haveI : Nonempty (j ⁻¹ᵁ W) := ⟨⟨P.genericPoint, hxW⟩⟩
  letI := functionFieldAlgebra (j ≫ sS)
  letI := stalkAlgebra (j ≫ sS) P.genericPoint
  haveI := isScalarTower_stalk_functionField (j ≫ sS) P.genericPoint
  -- `germ h - a` lies in the maximal ideal at `x`, hence its image at `P` does too
  have hmx : S.presheaf.germ W _ hxW h - algebraMap k _ a ∈
      IsLocalRing.maximalIdeal (S.presheaf.stalk (j.base P.genericPoint)) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← ha]
    exact sub_eq_zero.mpr rfl
  have hmP : (j.stalkMap P.genericPoint).hom (S.presheaf.germ W _ hxW h - algebraMap k _ a) ∈
      IsLocalRing.maximalIdeal (T.presheaf.stalk P.genericPoint) :=
    map_nonunit (j.stalkMap P.genericPoint).hom _ hmx
  rw [map_sub, Scheme.Hom.germ_stalkMap_apply] at hmP
  have hcomp : (j.stalkMap P.genericPoint).hom (algebraMap k _ a) = algebraMap k _ a :=
    stalkMap_stalkAlgebra j P.genericPoint a
  rw [hcomp] at hmP
  have hP' : P.genericPoint ∈ j ⁻¹ᵁ W := hxW
  have e1 : algebraMap (T.presheaf.stalk P.genericPoint) T.functionField
      (T.presheaf.germ (j ⁻¹ᵁ W) P.genericPoint hP' (j.app W h)) =
        T.germToFunctionField (j ⁻¹ᵁ W) (j.app W h) :=
    Scheme.algebraMap_germ_eq_germToFunctionField T hP' _
  have hK : T.germToFunctionField (j ⁻¹ᵁ W) (j.app W h) - algebraMap k _ a =
      algebraMap (T.presheaf.stalk P.genericPoint) T.functionField
        (T.presheaf.germ (j ⁻¹ᵁ W) P.genericPoint hP' (j.app W h) - algebraMap k _ a) := by
    rw [map_sub, e1, ← IsScalarTower.algebraMap_apply]
  rw [hK]
  by_cases h0 : algebraMap (T.presheaf.stalk P.genericPoint) T.functionField
      (T.presheaf.germ (j ⁻¹ᵁ W) P.genericPoint hP' (j.app W h) - algebraMap k _ a) = 0
  · exact Or.inl h0
  exact Or.inr (one_le_ord_of_mem_maximalIdeal P hmP h0)

/-- **Vanishing along a component.** For `h` regular near the generic point of the image of a
closed immersion `j : T ⟶ S` onto a prime divisor `Γ`, the restriction `h|_T` vanishes exactly when
`h` is zero or has positive order along `Γ`. -/
private theorem germToFunctionField_app_eq_zero_iff {T : Scheme.{0}} [IsIntegral T] (j : T ⟶ S)
    [IsClosedImmersion j] (Γ : Mori.PrimeDivisor S)
    (hΓ : j.base (genericPoint T) = Γ.genericPoint) {W : S.Opens}
    (hW : j.base (genericPoint T) ∈ W) (h : Γ(S, W)) :
    haveI : Nonempty W := ⟨⟨_, hW⟩⟩
    haveI : Nonempty (j ⁻¹ᵁ W) := ⟨⟨genericPoint T, hW⟩⟩
    T.germToFunctionField (j ⁻¹ᵁ W) (j.app W h) = 0 ↔
      (S.germToFunctionField W h = 0 ∨ 1 ≤ S.ord (S.germToFunctionField W h) Γ.genericPoint) := by
  haveI : Nonempty W := ⟨⟨_, hW⟩⟩
  haveI : Nonempty (j ⁻¹ᵁ W) := ⟨⟨genericPoint T, hW⟩⟩
  have hz : Order.coheight (j.base (genericPoint T)) = 1 := hΓ ▸ Γ.coheight_genericPoint
  haveI : IsDiscreteValuationRing (S.presheaf.stalk (j.base (genericPoint T))) := by
    rw [hΓ]; exact Γ.isDiscreteValuationRing_localRing
  have e1 : T.germToFunctionField (j ⁻¹ᵁ W) (j.app W h) =
      (j.stalkMap (genericPoint T)).hom (S.presheaf.germ W _ hW h) :=
    (Scheme.Hom.germ_stalkMap_apply j W (genericPoint T) hW h).symm
  have e2 : S.germToFunctionField W h =
      algebraMap (S.presheaf.stalk (j.base (genericPoint T))) S.functionField
        (S.presheaf.germ W _ hW h) :=
    (Scheme.algebraMap_germ_eq_germToFunctionField S hW h).symm
  have hsurj := SurjectiveOnStalks.stalkMap_surjective j (genericPoint T)
  have hker : RingHom.ker (j.stalkMap (genericPoint T)).hom =
      IsLocalRing.maximalIdeal (S.presheaf.stalk (j.base (genericPoint T))) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)
  rw [e1, e2, ← RingHom.mem_ker, hker, ← hΓ]
  constructor
  · intro hm
    by_cases h0 : algebraMap (S.presheaf.stalk (j.base (genericPoint T))) S.functionField
        (S.presheaf.germ W _ hW h) = 0
    · exact Or.inl h0
    · exact Or.inr (one_le_ord_of_mem_maximalIdeal' hz hm h0)
  · rintro (h0 | h1)
    · have : S.presheaf.germ W _ hW h = 0 :=
        IsFractionRing.injective (S.presheaf.stalk (j.base (genericPoint T))) S.functionField
          (h0.trans (map_zero _).symm)
      rw [this]; exact Ideal.zero_mem _
    · by_contra hm
      have hu := (IsLocalRing.notMem_maximalIdeal.mp hm)
      rw [ord_algebraMap_eq_zero_of_isUnit hz hu] at h1
      omega

/-- The components of the floor are curves. -/
private theorem topologicalKrullDim_component (hdim : topologicalKrullDim S = 2)
    (hfl : IsFloorNormalization sS B ι N) (i : N.ι) : topologicalKrullDim (N.X i) = 1 := by
  haveI : LocallyOfFiniteType (N.n i ≫ ι ≫ sS) := (N.isNormalVariety i).1.toLocallyOfFiniteType
  have h := toENat_trdeg_functionField (sX := N.n i ≫ ι ≫ sS)
  have htr := toNat_trdeg_component hdim hfl i
  letI := functionFieldAlgebra (N.n i ≫ ι ≫ sS)
  have hfin : Algebra.trdeg k (N.X i).functionField < Cardinal.aleph0 := by
    by_contra hc
    rw [Cardinal.toNat_eq_zero.mpr (Or.inr (not_lt.mp hc))] at htr
    exact zero_ne_one htr
  rw [← h, ← Cardinal.cast_toNat_of_lt_aleph0 hfin, htr]
  simp

/-- **Values from leading coefficients.** If `ρ₀` has a pole of order exactly `m` at `P` with
leading coefficient `c₀` and `g ρ₀` has leading coefficient `c`, then `c₀ ≠ 0` and `g` takes the
value `c / c₀` at `P`. -/
private theorem value_of_isLeadingCoeff (hdim : topologicalKrullDim S = 2)
    (hfl : IsFloorNormalization sS B ι N) {i : N.ι} {P : Mori.PrimeDivisor (N.X i)}
    {ρ₀ : RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m} (hρ₀0 : ρ₀ ≠ 0)
    (hρ₀ : P.ordForm ρ₀ = -(m : ℤ)) {c₀ c : k} (hc₀ : N.IsLeadingCoeff i P ρ₀ c₀)
    {g : (N.X i).functionField} (hc : N.IsLeadingCoeff i P (g • ρ₀) c) :
    c₀ ≠ 0 ∧ (letI := functionFieldAlgebra (N.n i ≫ ι ≫ sS);
      g - algebraMap k _ (c / c₀) = 0 ∨
        1 ≤ (N.X i).ord (g - algebraMap k _ (c / c₀)) P.genericPoint) := by
  letI := functionFieldAlgebra (N.n i ≫ ι ≫ sS)
  haveI : LocallyOfFiniteType (N.n i ≫ ι ≫ sS) := (N.isNormalVariety i).1.toLocallyOfFiniteType
  have htr := toNat_trdeg_component hdim hfl i
  have hdimi := topologicalKrullDim_component hdim hfl i
  obtain ⟨z₀, hz₀, h₀⟩ := hc₀
  obtain ⟨z, hz, h⟩ := hc
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_smul, sub_zero] at h₀
    rcases h₀ with h₀ | h₀
    · exact hρ₀0 h₀
    · rw [hρ₀] at h₀; omega
  refine ⟨hc₀0, ?_⟩
  have hconst : ∀ a : k, algebraMap k (N.X i).functionField a = 0 ∨
      0 ≤ (N.X i).ord (algebraMap k (N.X i).functionField a) P.genericPoint := fun a => by
    by_cases ha : a = 0
    · left; rw [ha, map_zero]
    · right; rw [ord_algebraMap_const (sX := N.n i ≫ ι ≫ sS) P ha]
  have hD := ordGE_dlogPow_sub (N.isNormalVariety i) hdimi P hz₀ hz m
  -- `ρ₀ - c₀ (dz/z)^m` vanishes to order `1 - m`
  have h₁ : OrdGE P (1 - m) (ρ₀ - algebraMap k (N.X i).functionField c₀ • dlogPow (N.n i ≫ ι ≫ sS) z m) := by
    have e : ρ₀ - algebraMap k (N.X i).functionField c₀ • dlogPow (N.n i ≫ ι ≫ sS) z m =
        (ρ₀ - algebraMap k (N.X i).functionField c₀ • dlogPow (N.n i ≫ ι ≫ sS) z₀ m) -
          algebraMap k (N.X i).functionField c₀ • (dlogPow (N.n i ≫ ι ≫ sS) z m -
            dlogPow (N.n i ≫ ι ≫ sS) z₀ m) := by
      rw [smul_sub]; abel
    rw [e]
    exact OrdGE.sub h₀ ((hD.smul htr (hconst c₀)).mono (by omega))
  have e : (g - algebraMap k (N.X i).functionField (c / c₀)) • ρ₀ =
      (g • ρ₀ - algebraMap k (N.X i).functionField c • dlogPow (N.n i ≫ ι ≫ sS) z m) -
        algebraMap k (N.X i).functionField (c / c₀) • (ρ₀ - algebraMap k (N.X i).functionField c₀ • dlogPow (N.n i ≫ ι ≫ sS) z m) := by
    rw [sub_smul, smul_sub, smul_smul, ← map_mul, div_mul_cancel₀ c hc₀0]
    abel
  have h₂ : OrdGE P (1 + -(m : ℤ)) ((g - algebraMap k (N.X i).functionField (c / c₀)) • ρ₀) := by
    rw [e]
    exact (OrdGE.sub h ((h₁.smul htr (hconst _)).mono (by omega))).mono (by omega)
  exact le_ord_of_ordGE_smul htr hρ₀0 hρ₀ h₂

/-- The normalization of the floor has finitely many components. -/
private theorem finite_index (hfl : IsFloorNormalization sS B ι N) : Finite N.ι := by
  classical
  choose Γ hΓ1 hΓ using hfl.exists_primeDivisor
  let f : N.ι → B.support := fun i => ⟨Γ i, by
    rw [Finsupp.mem_support_iff]
    change B.coeff (Γ i) ≠ 0
    rw [hΓ1 i]; exact one_ne_zero⟩
  refine Finite.of_injective f fun i j hij => hfl.injective ?_
  have : Γ i = Γ j := congrArg Subtype.val hij
  change (N.n i ≫ ι).base _ = (N.n j ≫ ι).base _
  rw [hΓ i, hΓ j, this]

/-- **Lifting along one branch.** A rational function on `T` regular at `y` is the restriction of
a function regular near `j(y)`, for a closed immersion `j : T ⟶ S`. -/
private theorem exists_lift_of_mem_range {T : Scheme.{0}} [IsIntegral T] (j : T ⟶ S)
    [IsClosedImmersion j] (y : T) {g : T.functionField}
    (hg : g ∈ Set.range (algebraMap (T.presheaf.stalk y) T.functionField)) {W₀ : S.Opens}
    (hW₀ : j.base y ∈ W₀) :
    ∃ (W : S.Opens) (hW : j.base y ∈ W), W ≤ W₀ ∧ ∃ h : Γ(S, W),
      haveI : Nonempty (j ⁻¹ᵁ W) := ⟨⟨y, hW⟩⟩
      T.germToFunctionField _ (j.app W h) = g := by
  obtain ⟨t, rfl⟩ := hg
  obtain ⟨u, hu⟩ := SurjectiveOnStalks.stalkMap_surjective j y t
  obtain ⟨W, hWW₀, hW, h, rfl⟩ := S.presheaf.exists_le_germ_eq u hW₀
  refine ⟨W, hW, hWW₀, h, ?_⟩
  haveI : Nonempty (j ⁻¹ᵁ W) := ⟨⟨y, hW⟩⟩
  rw [← hu, Scheme.Hom.germ_stalkMap_apply]
  exact (Scheme.algebraMap_germ_eq_germToFunctionField T (show y ∈ j ⁻¹ᵁ W from hW) _).symm

/-- A regular multiple of a generator is a section. -/
private theorem germToFunctionField_smul_mem (hdim : topologicalKrullDim S = 2)
    (hGm : Divisor.toQDivisor Gm = (m : ℚ) • B) {V W : S.Opens} {τ₀ : RationalPluriForms sS 2 m}
    (hgen : GeneratesOn B m V τ₀) (hWV : W ≤ V) [Nonempty W] (h : Γ(S, W)) :
    S.germToFunctionField W h • τ₀ ∈ pluricanonicalSections sS 2 m Gm W := by
  have htr := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hdim
  refine ⟨fun hW => absurd hW (by
      obtain ⟨⟨x, hx⟩⟩ := (inferInstance : Nonempty W)
      intro h; rw [h] at hx; exact hx), fun Γ hΓ hτ0 => ?_⟩
  have hf0 : S.germToFunctionField W h ≠ 0 := by rintro hf; apply hτ0; rw [hf, zero_smul]
  rw [Γ.ordForm_smul htr hf0 hgen.1]
  have h1 := zero_le_ord_germToFunctionField h Γ
    (MMP.Intersection.genericPoint_mem_of_support_inter_nonempty Γ hΓ)
  have h2 := hgen.2 Γ ⟨hΓ.choose, hΓ.choose_spec.1, hWV hΓ.choose_spec.2⟩
  have h4 : (Gm.coeff Γ : ℚ) = m * B.coeff Γ := by
    have := congrArg (fun D : QDivisor S => D.coeff Γ) hGm
    simpa [Divisor.coeff_toQDivisor] using this
  have : (0 : ℚ) ≤ ((S.ord (S.germToFunctionField W h) Γ.genericPoint + Γ.ordForm τ₀ : ℤ) : ℚ) +
      Gm.coeff Γ := by
    push_cast; rw [h4]
    have : (0 : ℚ) ≤ S.ord (S.germToFunctionField W h) Γ.genericPoint := by exact_mod_cast h1
    linarith
  exact_mod_cast this

/-- The rational `m`-canonical forms on a component of the floor form a line. -/
private theorem exists_eq_smul_component (hdim : topologicalKrullDim S = 2)
    (hfl : IsFloorNormalization sS B ι N) (i : N.ι)
    {ρ₀ : RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m} (hρ₀ : ρ₀ ≠ 0)
    (s : RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m) :
    ∃ g : (N.X i).functionField, s = g • ρ₀ := by
  letI := functionFieldAlgebra (N.n i ≫ ι ≫ sS)
  haveI : LocallyOfFiniteType (N.n i ≫ ι ≫ sS) := (N.isNormalVariety i).1.toLocallyOfFiniteType
  have hd1 : topologicalKrullDim (N.X i) = ((1 : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast topologicalKrullDim_component hdim hfl i
  obtain ⟨b₀⟩ := MMP.Fourfold.exists_basis_topForms (sX := N.n i ≫ ι ≫ sS) (d := 1) hd1
  let bb : Module.Basis Unit (N.X i).functionField (RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m) :=
    ZTensorPower.basis b₀ m
  have hrank : Module.finrank (N.X i).functionField
      (RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m) = 1 := by
    rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]
  obtain ⟨g, hg⟩ := (finrank_eq_one_iff_of_nonzero' ρ₀ hρ₀).mp hrank s
  exact ⟨g, hg.symm⟩

/-- **Quotients of sections by residues of generators are regular.** If `s` satisfies the order
conditions of `ω_C^{⊗m}(mΔ)` on `Cᵢ` over `U` and `ρ₀` is the residue of a generator on `V`,
then `s / ρ₀` is regular at every point of `Cᵢ` over `U ∩ V`. -/
private theorem mem_range_of_ordForm_bound (hdim : topologicalKrullDim S = 2)
    (hfl : IsFloorNormalization sS B ι N) {U V : S.Opens} {i : N.ι}
    {ρ₀ : RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m} (hρ₀0 : ρ₀ ≠ 0)
    (hρ₀ : ∀ P : Mori.PrimeDivisor (N.X i), ι.base ((N.n i).base P.genericPoint) ∈ V →
      ((P.ordForm ρ₀ : ℤ) : ℚ) = -(m * N.componentBoundaryCoeff Δ i P))
    {s : RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m}
    (hs : ∀ P : Mori.PrimeDivisor (N.X i), ι.base ((N.n i).base P.genericPoint) ∈ U →
      s ≠ 0 → 0 ≤ ((P.ordForm s : ℤ) : ℚ) + m * N.componentBoundaryCoeff Δ i P)
    {g : (N.X i).functionField} (hg : s = g • ρ₀) (y : N.X i)
    (hy : (N.n i ≫ ι).base y ∈ U ⊓ V) :
    g ∈ Set.range (algebraMap ((N.X i).presheaf.stalk y) (N.X i).functionField) := by
  haveI : LocallyOfFiniteType (N.n i ≫ ι ≫ sS) := (N.isNormalVariety i).1.toLocallyOfFiniteType
  have htr := toNat_trdeg_component hdim hfl i
  rcases eq_or_ne g 0 with rfl | hg0
  · exact ⟨0, map_zero _⟩
  have hs0 : s ≠ 0 := by rw [hg]; exact smul_ne_zero hg0 hρ₀0
  obtain ⟨r, hr⟩ := MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord y hg0
    fun Q hQ => by
      have hsp : Q.genericPoint ⤳ y := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hQ
        exact specializes_iff_mem_closure.mpr hQ
      have hQUV : (N.n i ≫ ι).base Q.genericPoint ∈ U ⊓ V :=
        (hsp.map (N.n i ≫ ι).base.hom.continuous).mem_open (U ⊓ V).isOpen hy
      have h1 := hs Q hQUV.1 hs0
      have h2 := hρ₀ Q hQUV.2
      rw [hg, Q.ordForm_smul htr hg0 hρ₀0] at h1
      push_cast at h1
      have : (0 : ℚ) ≤ (N.X i).ord g Q.genericPoint := by linarith
      exact_mod_cast this
  exact ⟨r, hr⟩

/-- A point of a component of the floor lying over a closed point of `S` is the generic point of
a prime divisor of the component. -/
private theorem exists_primeDivisor_of_isClosed (hdim : topologicalKrullDim S = 2)
    (hfl : IsFloorNormalization sS B ι N) (i : N.ι) (y : N.X i)
    (hy : IsClosed ({(N.n i ≫ ι).base y} : Set S)) :
    ∃ P : Mori.PrimeDivisor (N.X i), P.genericPoint = y := by
  haveI := hfl.isClosedImmersion i
  have hdimi := topologicalKrullDim_component hdim hfl i
  have hpre : (N.n i ≫ ι).base ⁻¹' {(N.n i ≫ ι).base y} = {y} := by
    rw [← Set.image_singleton,
      Set.preimage_image_eq _ (N.n i ≫ ι).isClosedEmbedding.injective]
  have hyc : IsClosed ({y} : Set (N.X i)) := by
    rw [← hpre]; exact hy.preimage (N.n i ≫ ι).base.hom.continuous
  have hne : y ≠ genericPoint (N.X i) := by
    rintro rfl
    exact MMP.Fourfold.not_isClosed_genericPoint hdimi hyc
  have hcoh := MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hdimi hne
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hcoh,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hcoh⟩

/-- Restricting a function before pulling it back to `T` does not change the rational function. -/
private theorem germToFunctionField_app_res {T : Scheme.{0}} [IsIntegral T] (j : T ⟶ S)
    {W W₁ : S.Opens} (hle : W ≤ W₁) (h₁ : Γ(S, W₁)) (hη : j.base (genericPoint T) ∈ W) :
    haveI : Nonempty (j ⁻¹ᵁ W) := ⟨⟨genericPoint T, hη⟩⟩
    haveI : Nonempty (j ⁻¹ᵁ W₁) := ⟨⟨genericPoint T, hle hη⟩⟩
    T.germToFunctionField _ (j.app W (S.presheaf.map (homOfLE hle).op h₁)) =
      T.germToFunctionField _ (j.app W₁ h₁) := by
  haveI : Nonempty (j ⁻¹ᵁ W) := ⟨⟨genericPoint T, hη⟩⟩
  haveI : Nonempty (j ⁻¹ᵁ W₁) := ⟨⟨genericPoint T, hle hη⟩⟩
  change T.presheaf.germ _ (genericPoint T) hη _ = T.presheaf.germ _ (genericPoint T) (hle hη) _
  rw [← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply,
    TopCat.Presheaf.germ_res_apply]

/-- **Local lifts.** Near every point of `U`, a section of `ω_C^{⊗m}(mΔ)` over `C ∩ U` is the
family of residues of a section of `𝒪_S(m(K_S + B))`. -/
private theorem exists_local_lift (hdim : topologicalKrullDim S = 2)
    (hfl : IsFloorNormalization sS B ι N) (hGm : Divisor.toQDivisor Gm = (m : ℚ) • B)
    (hres : HasResidueGenerators sS B ι N Δ m) {U : S.Opens}
    (s : ∀ i : N.ι, RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m)
    (hs1 : ∀ i (P : Mori.PrimeDivisor (N.X i)), ι.base ((N.n i).base P.genericPoint) ∈ U →
        s i ≠ 0 → 0 ≤ ((P.ordForm (s i) : ℤ) : ℚ) + m * N.componentBoundaryCoeff Δ i P)
    (hs2 : ∀ (i j : N.ι) (P : Mori.PrimeDivisor (N.X i)) (P' : Mori.PrimeDivisor (N.X j)),
        (N.n i).base P.genericPoint = (N.n j).base P'.genericPoint →
        ι.base ((N.n i).base P.genericPoint) ∈ U →
        IsDoubleNormalCrossingPoint (ι ≫ sS) 1 ((N.n i).base P.genericPoint) →
        (⟨i, P.genericPoint⟩ : Σ i, N.X i) ≠ ⟨j, P'.genericPoint⟩ →
        ∃ c : k, N.IsLeadingCoeff i P (s i) c ∧ N.IsLeadingCoeff j P' (s j) c)
    (x : S) (hxU : x ∈ U) :
    ∃ W : S.Opens, x ∈ W ∧ W ≤ U ∧ ∃ τ ∈ pluricanonicalSections sS 2 m Gm W,
      ∀ i, (Set.range (N.n i ≫ ι).base ∩ W).Nonempty →
        IsPoincareResidue sS (N.n i ≫ ι) 1 m τ (s i) := by
  classical
  haveI := finite_index hfl
  obtain ⟨V, hxV, τ₀, hgen, hex, hord, hnode⟩ := hres x
  -- remove the components not through `x`
  set Z : Set S := ⋃ i ∈ {i : N.ι | x ∉ Set.range (N.n i ≫ ι).base},
    Set.range (N.n i ≫ ι).base with hZdef
  have hZ : IsClosed Z := (Set.toFinite _).isClosed_biUnion fun i _ => by
    haveI := hfl.isClosedImmersion i
    exact (N.n i ≫ ι).isClosedEmbedding.isClosed_range
  have hxZ : x ∉ Z := by
    rw [hZdef, Set.mem_iUnion₂]
    rintro ⟨i, hi, hxi⟩
    exact hi hxi
  let W₀ : S.Opens := U ⊓ V ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩
  have hxW₀ : x ∈ W₀ := ⟨⟨hxU, hxV⟩, hxZ⟩
  have hthrough : ∀ W : S.Opens, W ≤ W₀ → ∀ i, (Set.range (N.n i ≫ ι).base ∩ W).Nonempty →
      x ∈ Set.range (N.n i ≫ ι).base := by
    rintro W hW i ⟨z, hz, hzW⟩
    by_contra hx
    exact (hW hzW).2 (Set.mem_biUnion (x := i) hx hz)
  -- a function whose restrictions divide `s` by the residues of `τ₀` gives the lift
  have finish : ∀ (W : S.Opens) (hxW : x ∈ W) (hWW₀ : W ≤ W₀) (h : Γ(S, W)),
      (∀ i (y : N.X i) (hy : (N.n i ≫ ι).base y = x) (ρ₀ : RationalPluriForms _ 1 m),
        IsPoincareResidue sS (N.n i ≫ ι) 1 m τ₀ ρ₀ →
        haveI : Nonempty ((N.n i ≫ ι) ⁻¹ᵁ W) := ⟨⟨y, show _ ∈ W from hy ▸ hxW⟩⟩
        (N.X i).germToFunctionField _ ((N.n i ≫ ι).app W h) • ρ₀ = s i) →
      ∃ W : S.Opens, x ∈ W ∧ W ≤ U ∧ ∃ τ ∈ pluricanonicalSections sS 2 m Gm W,
        ∀ i, (Set.range (N.n i ≫ ι).base ∩ W).Nonempty →
          IsPoincareResidue sS (N.n i ≫ ι) 1 m τ (s i) := by
    intro W hxW hWW₀ h hh
    haveI : Nonempty W := ⟨⟨x, hxW⟩⟩
    refine ⟨W, hxW, fun z hz => (hWW₀ hz).1.1,
      _, germToFunctionField_smul_mem hdim hGm hgen (fun z hz => (hWW₀ hz).1.2) h,
      fun i hi => ?_⟩
    obtain ⟨y, hy⟩ := hthrough W hWW₀ i hi
    obtain ⟨ρ₀, hρ₀⟩ := hex i ⟨x, ⟨y, hy⟩, hxV⟩
    have hη : (N.n i ≫ ι).base (genericPoint (N.X i)) ∈ W :=
      (((genericPoint_spec (N.X i)).specializes trivial).map
        (N.n i ≫ ι).base.hom.continuous).mem_open W.isOpen (hy ▸ hxW)
    have := isPoincareResidue_germToFunctionField_smul hρ₀ hη h
    rwa [hh i y hy ρ₀ hρ₀] at this
  by_cases h0 : ∃ i, x ∈ Set.range (N.n i ≫ ι).base
  swap
  · push Not at h0
    exact finish W₀ hxW₀ le_rfl 0 fun i y hy => absurd ⟨y, hy⟩ (h0 i)
  obtain ⟨i, y, hy⟩ := h0
  haveI := hfl.isClosedImmersion i
  have hxi : x ∈ Set.range (N.n i ≫ ι).base := ⟨y, hy⟩
  obtain ⟨ρ₀, hρ₀⟩ := hex i ⟨x, hxi, hxV⟩
  obtain ⟨hρ₀0, hρ₀ord⟩ := hord i ρ₀ ⟨x, hxi, hxV⟩ hρ₀
  have hP := hfl.exists_primeDivisor i
  obtain ⟨g, hg⟩ := exists_eq_smul_component hdim hfl i (ρ₀ := ρ₀) hρ₀0 (s i)
  have hyUV : (N.n i ≫ ι).base y ∈ U ⊓ V := hy ▸ ⟨hxU, hxV⟩
  have hgreg := mem_range_of_ordForm_bound hdim hfl (ρ₀ := ρ₀) hρ₀0 (hρ₀ord ·)
    (hs1 i) hg y hyUV
  by_cases h1 : ∃ j, j ≠ i ∧ x ∈ Set.range (N.n j ≫ ι).base
  swap
  · -- one branch through `x`
    push Not at h1
    obtain ⟨W, hW, hWW₀, h, hhg⟩ := exists_lift_of_mem_range (N.n i ≫ ι) y hgreg
      (show (N.n i ≫ ι).base y ∈ W₀ from hy ▸ hxW₀)
    refine finish W (hy ▸ hW) hWW₀ h fun l y' hy' ρ₀' hρ₀' => ?_
    have hl : l = i := by
      by_contra hl
      exact h1 l hl ⟨y', hy'⟩
    subst hl
    obtain ⟨Γ, -, hΓ⟩ := hP
    rw [MMP.Fourfold.isPoincareResidue_unique hΓ hρ₀' hρ₀, hg]
    exact congrArg (· • ρ₀) hhg
  -- two branches through `x`: a node
  obtain ⟨j, hji, y', hy'⟩ := h1
  haveI := hfl.isClosedImmersion j
  have hxj : x ∈ Set.range (N.n j ≫ ι).base := ⟨y', hy'⟩
  obtain ⟨ρ₀', hρ₀'⟩ := hex j ⟨x, hxj, hxV⟩
  obtain ⟨hρ₀0', hρ₀ord'⟩ := hord j ρ₀' ⟨x, hxj, hxV⟩ hρ₀'
  have hP' := hfl.exists_primeDivisor j
  obtain ⟨g', hg'⟩ := exists_eq_smul_component hdim hfl j (ρ₀ := ρ₀') hρ₀0' (s j)
  have hy'UV : (N.n j ≫ ι).base y' ∈ U ⊓ V := hy' ▸ ⟨hxU, hxV⟩
  have hgreg' := mem_range_of_ordForm_bound hdim hfl (ρ₀ := ρ₀') hρ₀0' (hρ₀ord' ·)
    (hs1 j) hg' y' hy'UV
  have hyy' : (N.n i ≫ ι).base y = (N.n j ≫ ι).base y' := hy.trans hy'.symm
  have hdnc := hfl.isDoubleNormalCrossingPoint i j y y' hyy' hji.symm
  have hxc : IsClosed ({(N.n i ≫ ι).base y} : Set S) := by
    change IsClosed {ι.base ((N.n i).base y)}
    rw [← Set.image_singleton]
    exact ι.isClosedEmbedding.isClosedMap _ hdnc.2.1
  obtain ⟨P, rfl⟩ := exists_primeDivisor_of_isClosed hdim hfl i y hxc
  obtain ⟨P', rfl⟩ := exists_primeDivisor_of_isClosed hdim hfl j y' (hyy' ▸ hxc)
  have hnn : (N.n i).base P.genericPoint = (N.n j).base P'.genericPoint :=
    ι.isClosedEmbedding.injective hyy'
  have hne : (⟨i, P.genericPoint⟩ : Σ i, N.X i) ≠ ⟨j, P'.genericPoint⟩ := fun h =>
    hji (congrArg Sigma.fst h).symm
  have hdnc' : IsDoubleNormalCrossingPoint (ι ≫ sS) 1 ((N.n j).base P'.genericPoint) :=
    hnn ▸ hdnc
  obtain ⟨c, hc, hc'⟩ := hs2 i j P P' hnn (hy ▸ hxU) hdnc hne
  obtain ⟨c₀, hc₀, hc₀'⟩ := hnode i j P P' ρ₀ ρ₀' hρ₀ hρ₀' hnn (hy ▸ hxV) hdnc hne
  have hcb : N.componentBoundaryCoeff Δ i P = 1 := by
    simp [NormalizationComponents.componentBoundaryCoeff, hdnc]
  have hcb' : N.componentBoundaryCoeff Δ j P' = 1 := by
    simp [NormalizationComponents.componentBoundaryCoeff, hdnc']
  have hm1 : P.ordForm (k := k) ρ₀ = -(m : ℤ) := by
    have := hρ₀ord P (hy ▸ hxV)
    rw [hcb, mul_one] at this
    exact_mod_cast this
  have hm2 : P'.ordForm (k := k) ρ₀' = -(m : ℤ) := by
    have := hρ₀ord' P' (hy' ▸ hxV)
    rw [hcb', mul_one] at this
    exact_mod_cast this
  rw [hg] at hc
  rw [hg'] at hc'
  obtain ⟨-, hv⟩ := value_of_isLeadingCoeff hdim hfl hρ₀0 hm1 hc₀ hc
  obtain ⟨-, hv'⟩ := value_of_isLeadingCoeff hdim hfl hρ₀0' hm2 hc₀' hc'
  obtain ⟨W₁, hW₁, h₁, hr, hr'⟩ := hfl.nodeLift i j P P' hyy' hji.symm g g' (c / c₀)
    hgreg hgreg' hv hv'
  have hxW₁ : x ∈ W₁ := hy ▸ hW₁
  refine finish (W₁ ⊓ W₀) ⟨hxW₁, hxW₀⟩ inf_le_right
    (S.presheaf.map (homOfLE inf_le_left).op h₁) fun l z hz ρ₁ hρ₁ => ?_
  have hzW : (N.n l ≫ ι).base z ∈ W₁ ⊓ W₀ := hz ▸ ⟨hxW₁, hxW₀⟩
  have hηl : (N.n l ≫ ι).base (genericPoint (N.X l)) ∈ W₁ ⊓ W₀ :=
    (((genericPoint_spec (N.X l)).specializes trivial).map
      (N.n l ≫ ι).base.hom.continuous).mem_open (W₁ ⊓ W₀).isOpen hzW
  rw [germToFunctionField_app_res (N.n l ≫ ι) inf_le_left h₁ hηl]
  rcases hfl.atMostTwo i j l P.genericPoint P'.genericPoint z hyy' (hy.trans hz.symm) with
    hij | hjl | hil
  · exact absurd hij hji.symm
  · subst hjl
    obtain ⟨Γ, -, hΓ⟩ := hP'
    rw [MMP.Fourfold.isPoincareResidue_unique hΓ hρ₁ hρ₀', hg']
    exact congrArg (· • ρ₀') hr'
  · subst hil
    obtain ⟨Γ, -, hΓ⟩ := hP
    rw [MMP.Fourfold.isPoincareResidue_unique hΓ hρ₁ hρ₀, hg]
    exact congrArg (· • ρ₀) hr

/-- A regular function on `U` vanishing nowhere on `D(f) ∩ T = ∅` restricts to zero on `T`: if the
generic point of the image of `T` lies outside `D(f)`, then `f|_T = 0`. -/
private theorem germToFunctionField_app_eq_zero_of_notMem_basicOpen {T : Scheme.{0}}
    [IsIntegral T] (j : T ⟶ S) {U : S.Opens} (f : Γ(S, U))
    (hη : j.base (genericPoint T) ∈ U) (hD : j.base (genericPoint T) ∉ S.basicOpen f) :
    haveI : Nonempty (j ⁻¹ᵁ U) := ⟨⟨genericPoint T, hη⟩⟩
    T.germToFunctionField _ (j.app U f) = 0 := by
  haveI : Nonempty (j ⁻¹ᵁ U) := ⟨⟨genericPoint T, hη⟩⟩
  have hD' : ¬ IsUnit (S.presheaf.germ U _ hη f) := fun h =>
    hD ((S.mem_basicOpen f _ hη).mpr h)
  have hm : (j.stalkMap (genericPoint T)).hom (S.presheaf.germ U _ hη f) ∈
      IsLocalRing.maximalIdeal T.functionField :=
    map_nonunit (j.stalkMap (genericPoint T)).hom _ hD'
  rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hm
  rw [← hm]
  exact (Scheme.Hom.germ_stalkMap_apply j U (genericPoint T) hη f).symm

/-- Sections are stable under multiplication by regular functions. -/
private theorem germToFunctionField_smul_mem_of_mem (hdim : topologicalKrullDim S = 2)
    {G : Divisor S} {U : S.Opens} [Nonempty U] (a : Γ(S, U)) {τ : RationalPluriForms sS 2 m}
    (hτ : τ ∈ pluricanonicalSections sS 2 m G U) :
    S.germToFunctionField U a • τ ∈ pluricanonicalSections sS 2 m G U := by
  have htr := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hdim
  refine ⟨fun hU => absurd hU (by
      obtain ⟨⟨x, hx⟩⟩ := (inferInstance : Nonempty U)
      intro h; rw [h] at hx; exact hx), fun Γ hΓ hτ0 => ?_⟩
  have ha0 : S.germToFunctionField U a ≠ 0 := by rintro h; apply hτ0; rw [h, zero_smul]
  have hτ0' : τ ≠ 0 := by rintro h; apply hτ0; rw [h, smul_zero]
  rw [Γ.ordForm_smul htr ha0 hτ0']
  have h1 := zero_le_ord_germToFunctionField a Γ
    (MMP.Intersection.genericPoint_mem_of_support_inter_nonempty Γ hΓ)
  have h2 := hτ.2 Γ hΓ hτ0'
  omega

/-- The zero form has residue zero along every closed integral subscheme onto a prime
divisor. -/
private theorem isPoincareResidue_zero {T : Scheme.{0}} [IsIntegral T] (j : T ⟶ S)
    (Γ : Mori.PrimeDivisor S) (hΓ : j.base (genericPoint T) = Γ.genericPoint) {n : ℕ} :
    IsPoincareResidue sS j n m 0 0 := by
  have hz : Order.coheight (j.base (genericPoint T)) = 1 := hΓ ▸ Γ.coheight_genericPoint
  haveI : IsDiscreteValuationRing (S.presheaf.stalk (j.base (genericPoint T))) := by
    rw [hΓ]; exact Γ.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible
    (S.presheaf.stalk (j.base (genericPoint T)))
  have hϖ0 : algebraMap _ S.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  refine ⟨ϖ, 0, fun _ => 0, (Scheme.ord_eq_iff hz hϖ0).mpr (Ring.ordFrac_irreducible hϖ), ?_, ?_⟩
  · rw [map_zero, zero_smul]; rfl
  · rw [map_zero, zero_smul]; rfl

/-- **Additivity of residues** of sections of `𝒪_S(m(K_S + B))` along a component meeting `U`. -/
private theorem isPoincareResidue_add (hdim : topologicalKrullDim S = 2)
    (hfl : IsFloorNormalization sS B ι N) (hGm : Divisor.toQDivisor Gm = (m : ℚ) • B)
    (hres : HasResidueGenerators sS B ι N Δ m) {U : S.Opens} {τ τ' : RationalPluriForms sS 2 m}
    (hτ : τ ∈ pluricanonicalSections sS 2 m Gm U) (hτ' : τ' ∈ pluricanonicalSections sS 2 m Gm U)
    (i : N.ι) (hi : (Set.range (N.n i ≫ ι).base ∩ U).Nonempty)
    {ρ ρ' : RationalPluriForms ((N.n i ≫ ι) ≫ sS) 1 m}
    (hρ : IsPoincareResidue sS (N.n i ≫ ι) 1 m τ ρ)
    (hρ' : IsPoincareResidue sS (N.n i ≫ ι) 1 m τ' ρ') :
    IsPoincareResidue sS (N.n i ≫ ι) 1 m (τ + τ') (ρ + ρ') := by
  haveI := hfl.isClosedImmersion i
  obtain ⟨P, -, hP⟩ := hfl.exists_primeDivisor i
  obtain ⟨-, ⟨y, rfl⟩, hyU⟩ := hi
  obtain ⟨V, hxV, τ₀, hgen, hex, -, -⟩ := hres ((N.n i ≫ ι).base y)
  obtain ⟨ρ₀, hρ₀⟩ := hex i ⟨_, ⟨y, rfl⟩, hxV⟩
  obtain ⟨h, rfl, hh⟩ := exists_residue_eq_smul hdim hGm hyU hxV hgen hτ
  obtain ⟨h', hτh', hh'⟩ := exists_residue_eq_smul hdim hGm hyU hxV hgen hτ'
  subst hτh'
  have hη : (N.n i ≫ ι).base (genericPoint (N.X i)) ∈ U ⊓ V :=
    (((genericPoint_spec (N.X i)).specializes trivial).map
      (N.n i ≫ ι).base.hom.continuous).mem_open (U ⊓ V).isOpen ⟨hyU, hxV⟩
  rw [hh (N.n i ≫ ι) P hP ρ₀ ρ hη hρ₀ hρ, hh' (N.n i ≫ ι) P hP ρ₀ ρ' hη hρ₀ hρ', ← add_smul,
    ← add_smul, ← map_add, ← map_add, ← map_add]
  exact isPoincareResidue_germToFunctionField_smul hρ₀ hη (h + h')

/-- `ord (f ^ n) = n ord f`. -/
private theorem ord_pow_eq {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X.functionField} (hf : f ≠ 0) (z : X) : ∀ n : ℕ, X.ord (f ^ n) z = n * X.ord f z
  | 0 => by
    have := Scheme.ord_mul (x := z) (one_ne_zero (α := X.functionField)) one_ne_zero
    rw [mul_one] at this
    simp only [pow_zero, Nat.cast_zero, zero_mul]; omega
  | n + 1 => by
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ hf) hf, ord_pow_eq hf z n]; push_cast; ring

/-- **Clearing denominators on an affine.** A section `τ` over the basic open `D(f)` of `U`
becomes a section over `U` after multiplication by a power `f^n`, `n > 0`, which moreover
vanishes to order `≥ 1 - m` along every prime divisor meeting `U` but not `D(f)`. -/
private theorem exists_pow_smul_mem [CompactSpace S] (hdim : topologicalKrullDim S = 2)
    {U : S.Opens} [Nonempty U] (f : Γ(S, U)) {τ : RationalPluriForms sS 2 m}
    (hτ : τ ∈ pluricanonicalSections sS 2 m Gm (S.basicOpen f)) :
    ∃ n : ℕ, 0 < n ∧ S.germToFunctionField U (f ^ n) • τ ∈ pluricanonicalSections sS 2 m Gm U ∧
      ∀ Γ : Mori.PrimeDivisor S, (Γ.support ∩ U).Nonempty →
        ¬ (Γ.support ∩ S.basicOpen f).Nonempty →
        OrdGE Γ (1 - m) (S.germToFunctionField U (f ^ n) • τ) := by
  classical
  have htr := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hdim
  by_cases hτ0 : τ = 0
  · subst hτ0
    exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _, fun _ _ _ => by
      rw [smul_zero]; exact OrdGE.zero _ _⟩
  by_cases hf0 : S.germToFunctionField U f = 0
  · refine ⟨1, one_pos, ?_, fun _ _ _ => ?_⟩
    · rw [pow_one, hf0, zero_smul]; exact zero_mem _
    · rw [pow_one, hf0, zero_smul]; exact OrdGE.zero _ _
  let Bad : Finset (Mori.PrimeDivisor S) := (finite_ordForm_ne_zero τ).toFinset ∪ Gm.support
  set Ssum : ℕ := ∑ Γ ∈ Bad, ((Γ.ordForm τ).natAbs + (Gm.coeff Γ).natAbs) with hSdef
  set n : ℕ := 1 + Ssum with hndef
  have hnz : (n : ℤ) = 1 + (Ssum : ℤ) := by rw [hndef]; push_cast; rfl
  have hbound : ∀ Γ : Mori.PrimeDivisor S,
      (1 : ℤ) + |Gm.coeff Γ| ≤ n + Γ.ordForm τ := by
    intro Γ
    by_cases hΓ : Γ ∈ Bad
    · have h1 : (Γ.ordForm τ).natAbs + (Gm.coeff Γ).natAbs ≤ Ssum :=
        Finset.single_le_sum (f := fun Γ => (Γ.ordForm τ).natAbs + (Gm.coeff Γ).natAbs)
          (fun _ _ => Nat.zero_le _) hΓ
      have h1' : ((Γ.ordForm τ).natAbs : ℤ) + ((Gm.coeff Γ).natAbs : ℤ) ≤ (Ssum : ℤ) := by
        exact_mod_cast h1
      rw [Int.natCast_natAbs, Int.natCast_natAbs] at h1'
      have h2 := neg_abs_le (Γ.ordForm τ)
      omega
    · have h1 : Γ.ordForm τ = 0 := by
        by_contra h; exact hΓ (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr h))
      have h2 : Gm.coeff Γ = 0 := by
        by_contra h
        exact hΓ (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr h))
      rw [h1, h2, abs_zero]
      omega
  have hord : ∀ Γ : Mori.PrimeDivisor S, (Γ.support ∩ U).Nonempty →
      Γ.ordForm (S.germToFunctionField U (f ^ n) • τ) =
        n * S.ord (S.germToFunctionField U f) Γ.genericPoint + Γ.ordForm τ := by
    intro Γ hΓ
    rw [map_pow, Γ.ordForm_smul htr (pow_ne_zero _ hf0) hτ0, ord_pow_eq hf0]
  have hout : ∀ Γ : Mori.PrimeDivisor S, (Γ.support ∩ U).Nonempty →
      ¬ (Γ.support ∩ S.basicOpen f).Nonempty → 1 ≤ S.ord (S.germToFunctionField U f) Γ.genericPoint := by
    intro Γ hΓ hD
    have hηU := MMP.Intersection.genericPoint_mem_of_support_inter_nonempty Γ hΓ
    have hηD : Γ.genericPoint ∉ S.basicOpen f := fun h =>
      hD (MMP.Intersection.support_inter_nonempty_of_genericPoint_mem Γ h)
    have hm : S.presheaf.germ U _ hηU f ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk Γ.genericPoint) :=
      fun h => hηD ((S.mem_basicOpen f _ hηU).mpr h)
    have e := Scheme.algebraMap_germ_eq_germToFunctionField S hηU f
    rw [← e] at hf0 ⊢
    exact one_le_ord_of_mem_maximalIdeal Γ hm hf0
  have hlow : ∀ Γ : Mori.PrimeDivisor S, (Γ.support ∩ U).Nonempty →
      ¬ (Γ.support ∩ S.basicOpen f).Nonempty →
      (1 : ℤ) + |Gm.coeff Γ| ≤ Γ.ordForm (S.germToFunctionField U (f ^ n) • τ) := by
    intro Γ hΓ hD
    rw [hord Γ hΓ]
    have h1 := hout Γ hΓ hD
    have h2 : (n : ℤ) ≤ n * S.ord (S.germToFunctionField U f) Γ.genericPoint :=
      le_mul_of_one_le_right (by positivity) h1
    have := hbound Γ
    omega
  refine ⟨n, by omega, ⟨fun hU => absurd hU (by
      obtain ⟨⟨x, hx⟩⟩ := (inferInstance : Nonempty U)
      intro h; rw [h] at hx; exact hx), fun Γ hΓ _ => ?_⟩, fun Γ hΓ hD => Or.inr ?_⟩
  · by_cases hD : (Γ.support ∩ S.basicOpen f).Nonempty
    · have h1 := hτ.2 Γ hD hτ0
      rw [hord Γ hΓ]
      have h2 := zero_le_ord_germToFunctionField f Γ
        (MMP.Intersection.genericPoint_mem_of_support_inter_nonempty Γ hΓ)
      have h3 : (0 : ℤ) ≤ n * S.ord (S.germToFunctionField U f) Γ.genericPoint :=
        mul_nonneg (by positivity) h2
      omega
    · have := hlow Γ hΓ hD
      have := neg_abs_le (Gm.coeff Γ)
      omega
  · have := hlow Γ hΓ hD
    have := abs_nonneg (Gm.coeff Γ)
    omega

/-- **Vanishing residues.** A section of `𝒪_S(m(K_S + B))` over `U` of order `≥ 1 - m` along a
component of the floor meeting `U` has residue zero along it. -/
private theorem isPoincareResidue_zero_of_ordGE (hdim : topologicalKrullDim S = 2)
    (hfl : IsFloorNormalization sS B ι N) (hGm : Divisor.toQDivisor Gm = (m : ℚ) • B)
    (hres : HasResidueGenerators sS B ι N Δ m) {U : S.Opens} {τ : RationalPluriForms sS 2 m}
    (hτ : τ ∈ pluricanonicalSections sS 2 m Gm U) (i : N.ι)
    (hi : (Set.range (N.n i ≫ ι).base ∩ U).Nonempty) (Γ : Mori.PrimeDivisor S)
    (hΓ : (N.n i ≫ ι).base (genericPoint (N.X i)) = Γ.genericPoint) (hB1 : B.coeff Γ = 1)
    (h : OrdGE Γ (1 - m) τ) : IsPoincareResidue sS (N.n i ≫ ι) 1 m τ 0 := by
  haveI := hfl.isClosedImmersion i
  have htr := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hdim
  obtain ⟨x, hxr, hxU⟩ := hi
  obtain ⟨V, hxV, τ₀, hgen, hex, -, -⟩ := hres x
  obtain ⟨ρ₀, hρ₀⟩ := hex i ⟨x, hxr, hxV⟩
  obtain ⟨g, hτg, -⟩ := exists_residue_eq_smul hdim hGm hxU hxV hgen hτ
  have hη : (N.n i ≫ ι).base (genericPoint (N.X i)) ∈ U ⊓ V := by
    obtain ⟨y, rfl⟩ := hxr
    exact (((genericPoint_spec (N.X i)).specializes trivial).map
      (N.n i ≫ ι).base.hom.continuous).mem_open (U ⊓ V).isOpen ⟨hxU, hxV⟩
  haveI : Nonempty (U ⊓ V : S.Opens) := ⟨⟨x, hxU, hxV⟩⟩
  have hres' := isPoincareResidue_germToFunctionField_smul hρ₀ hη g
  rw [← hτg] at hres'
  have hΓV : (Γ.support ∩ (V : Set S)).Nonempty := by
    refine ⟨x, ?_, hxV⟩
    rw [← range_eq_support (N.n i ≫ ι) Γ hΓ]; exact hxr
  have hgΓ := hgen.2 Γ hΓV
  rw [hB1, mul_one] at hgΓ
  have hτ₀Γ : Γ.ordForm τ₀ = -(m : ℤ) := by
    have : ((Γ.ordForm τ₀ : ℤ) : ℚ) = -(m : ℚ) := by linarith
    exact_mod_cast this
  haveI : Nonempty ((N.n i ≫ ι) ⁻¹ᵁ (U ⊓ V)) := ⟨⟨genericPoint _, hη⟩⟩
  have hzero : (N.X i).germToFunctionField ((N.n i ≫ ι) ⁻¹ᵁ (U ⊓ V))
      ((N.n i ≫ ι).app _ g) = 0 := by
    refine (germToFunctionField_app_eq_zero_iff (N.n i ≫ ι) Γ hΓ hη g).mpr ?_
    by_cases hg : S.germToFunctionField (U ⊓ V) g = 0
    · exact Or.inl hg
    refine Or.inr ?_
    have hτ0 : τ ≠ 0 := by rw [hτg]; exact smul_ne_zero hg hgen.1
    have := h.resolve_left hτ0
    rw [hτg, Γ.ordForm_smul htr hg hgen.1, hτ₀Γ] at this
    omega
  rw [hzero, zero_smul] at hres'
  exact hres'

/-- **Residues of finite sums.** -/
private theorem isPoincareResidue_sum (hdim : topologicalKrullDim S = 2)
    (hfl : IsFloorNormalization sS B ι N) (hGm : Divisor.toQDivisor Gm = (m : ℚ) • B)
    (hres : HasResidueGenerators sS B ι N Δ m) {U : S.Opens} {α : Type*} (F : Finset α)
    (τ : α → RationalPluriForms sS 2 m) (hτ : ∀ a ∈ F, τ a ∈ pluricanonicalSections sS 2 m Gm U)
    (i : N.ι) (hi : (Set.range (N.n i ≫ ι).base ∩ U).Nonempty)
    (ρ : α → RationalPluriForms ((N.n i ≫ ι) ≫ sS) 1 m)
    (hρ : ∀ a ∈ F, IsPoincareResidue sS (N.n i ≫ ι) 1 m (τ a) (ρ a)) :
    IsPoincareResidue sS (N.n i ≫ ι) 1 m (∑ a ∈ F, τ a) (∑ a ∈ F, ρ a) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨Γ, -, hΓ⟩ := hfl.exists_primeDivisor i
    rw [Finset.sum_empty, Finset.sum_empty]
    exact isPoincareResidue_zero (N.n i ≫ ι) Γ hΓ
  | insert a F haF ih =>
    rw [Finset.sum_insert haF, Finset.sum_insert haF]
    exact isPoincareResidue_add hdim hfl hGm hres (hτ a (Finset.mem_insert_self a F))
      (sum_mem fun b hb => hτ b (Finset.mem_insert_of_mem hb)) i hi
      (hρ a (Finset.mem_insert_self a F))
      (ih (fun b hb => hτ b (Finset.mem_insert_of_mem hb))
        (fun b hb => hρ b (Finset.mem_insert_of_mem hb)))

/-- Residues of sections of `𝒪_S(m(K_S + B))` along the components of the floor exist and are
unique. -/
private theorem existsUnique_isPoincareResidue (hdim : topologicalKrullDim S = 2)
    (hfl : IsFloorNormalization sS B ι N) (hGm : Divisor.toQDivisor Gm = (m : ℚ) • B)
    (hres : HasResidueGenerators sS B ι N Δ m) {U : S.Opens} {τ : RationalPluriForms sS 2 m}
    (hτ : τ ∈ pluricanonicalSections sS 2 m Gm U) (i : N.ι)
    (hi : (Set.range (N.n i ≫ ι).base ∩ U).Nonempty) :
    ∃! ρ, IsPoincareResidue sS (N.n i ≫ ι) 1 m τ ρ := by
  haveI := hfl.isClosedImmersion i
  obtain ⟨P, -, hP⟩ := hfl.exists_primeDivisor i
  obtain ⟨-, ⟨y, rfl⟩, hyU⟩ := hi
  obtain ⟨V, hxV, τ₀, hgen, hex, -, -⟩ := hres ((N.n i ≫ ι).base y)
  obtain ⟨ρ₀, hρ₀⟩ := hex i ⟨_, ⟨y, rfl⟩, hxV⟩
  haveI : Nonempty (U ⊓ V : S.Opens) := ⟨⟨_, hyU, hxV⟩⟩
  obtain ⟨h, rfl⟩ := exists_eq_smul_of_generatesOn hdim hGm hgen inf_le_right
    (mem_pluricanonicalSections_of_le hτ inf_le_left)
  have hη : (N.n i ≫ ι).base (genericPoint (N.X i)) ∈ U ⊓ V :=
    (((genericPoint_spec (N.X i)).specializes trivial).map
      (N.n i ≫ ι).base.hom.continuous).mem_open (U ⊓ V).isOpen ⟨hyU, hxV⟩
  refine ⟨_, isPoincareResidue_germToFunctionField_smul hρ₀ hη h, fun ρ hρ => ?_⟩
  exact MMP.Fourfold.isPoincareResidue_unique hP hρ
    (isPoincareResidue_germToFunctionField_smul hρ₀ hη h)

/-- The residues of a section of `𝒪_S(m(K_S + B))` over `U` are a section of
`ω_C^{⊗m}(mΔ)` over `C ∩ U`. -/
private theorem isSection_of_isPoincareResidue (hdim : topologicalKrullDim S = 2)
    (hfl : IsFloorNormalization sS B ι N) (hGm : Divisor.toQDivisor Gm = (m : ℚ) • B)
    (hres : HasResidueGenerators sS B ι N Δ m) {U : S.Opens} {τ : RationalPluriForms sS 2 m}
    (hτ : τ ∈ pluricanonicalSections sS 2 m Gm U)
    (ρ : ∀ i : N.ι, RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m)
    (hρ : ∀ i, (Set.range (N.n i ≫ ι).base ∩ U).Nonempty →
      IsPoincareResidue sS (N.n i ≫ ι) 1 m τ (cast (congrArg (fun f => RationalPluriForms f 1 m)
        (Category.assoc (N.n i) ι sS).symm) (ρ i))) :
    (∀ i (P : Mori.PrimeDivisor (N.X i)), ι.base ((N.n i).base P.genericPoint) ∈ U →
        ρ i ≠ 0 → 0 ≤ ((P.ordForm (ρ i) : ℤ) : ℚ) + m * N.componentBoundaryCoeff Δ i P) ∧
      ∀ (i j : N.ι) (P : Mori.PrimeDivisor (N.X i)) (P' : Mori.PrimeDivisor (N.X j)),
        (N.n i).base P.genericPoint = (N.n j).base P'.genericPoint →
        ι.base ((N.n i).base P.genericPoint) ∈ U →
        IsDoubleNormalCrossingPoint (ι ≫ sS) 1 ((N.n i).base P.genericPoint) →
        (⟨i, P.genericPoint⟩ : Σ i, N.X i) ≠ ⟨j, P'.genericPoint⟩ →
        ∃ c : k, N.IsLeadingCoeff i P (ρ i) c ∧ N.IsLeadingCoeff j P' (ρ j) c := by
  refine ⟨fun i P hxU hρ0 => ?_, fun i j P P' hPP' hxU hdnc hne => ?_⟩
  · haveI := hfl.isClosedImmersion i
    obtain ⟨Γ, -, hΓ⟩ := hfl.exists_primeDivisor i
    obtain ⟨V, hxV, τ₀, hgen, hex, hord, -⟩ := hres (ι.base ((N.n i).base P.genericPoint))
    have hxr : ι.base ((N.n i).base P.genericPoint) ∈ Set.range (N.n i ≫ ι).base :=
      ⟨P.genericPoint, rfl⟩
    obtain ⟨ρ₀, hρ₀⟩ := hex i ⟨_, hxr, hxV⟩
    obtain ⟨hρ₀0, hρ₀ord⟩ := hord i ρ₀ ⟨_, hxr, hxV⟩ hρ₀
    obtain ⟨h, -, hh⟩ := exists_residue_eq_smul hdim hGm hxU hxV hgen hτ
    have hPη : (N.n i ≫ ι).base P.genericPoint ∈ U ⊓ V := ⟨hxU, hxV⟩
    have hη : (N.n i ≫ ι).base (genericPoint (N.X i)) ∈ U ⊓ V :=
      (((genericPoint_spec (N.X i)).specializes trivial).map
        (N.n i ≫ ι).base.hom.continuous).mem_open (U ⊓ V).isOpen hPη
    have heq := (cast_eq _ (ρ i)).symm.trans (hh (N.n i ≫ ι) Γ hΓ ρ₀ _ hη hρ₀ (hρ i ⟨_, hxr, hxU⟩))
    haveI : Nonempty ((N.n i ≫ ι) ⁻¹ᵁ (U ⊓ V)) := ⟨⟨genericPoint _, hη⟩⟩
    haveI : LocallyOfFiniteType (N.n i ≫ ι ≫ sS) := (N.isNormalVariety i).1.toLocallyOfFiniteType
    set f := (N.X i).germToFunctionField ((N.n i ≫ ι) ⁻¹ᵁ (U ⊓ V)) ((N.n i ≫ ι).app _ h)
    let ρ₁ : RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m := ρ₀
    have heq' : ρ i = f • ρ₁ := heq
    have hρ₁0 : ρ₁ ≠ 0 := hρ₀0
    have h1 : ((P.ordForm ρ₁ : ℤ) : ℚ) = -(m * N.componentBoundaryCoeff Δ i P) := hρ₀ord P hxV
    have hf0 : f ≠ 0 := by
      rintro hf
      apply hρ0
      rw [heq', hf, zero_smul]
    have hsm := P.ordForm_smul (toNat_trdeg_component hdim hfl i) hf0 hρ₁0
    have hfP : 0 ≤ (N.X i).ord f P.genericPoint := zero_le_ord_germToFunctionField _ P hPη
    rw [heq', hsm]
    push_cast
    have : (0 : ℚ) ≤ (N.X i).ord f P.genericPoint := by exact_mod_cast hfP
    linarith
  · haveI := hfl.isClosedImmersion i
    haveI := hfl.isClosedImmersion j
    obtain ⟨Γ, -, hΓ⟩ := hfl.exists_primeDivisor i
    obtain ⟨Γ', -, hΓ'⟩ := hfl.exists_primeDivisor j
    obtain ⟨V, hxV, τ₀, hgen, hex, hord, hnode⟩ := hres (ι.base ((N.n i).base P.genericPoint))
    have hxr : ι.base ((N.n i).base P.genericPoint) ∈ Set.range (N.n i ≫ ι).base :=
      ⟨P.genericPoint, rfl⟩
    have hxr' : ι.base ((N.n i).base P.genericPoint) ∈ Set.range (N.n j ≫ ι).base :=
      ⟨P'.genericPoint, by simp [hPP']⟩
    obtain ⟨ρ₀, hρ₀⟩ := hex i ⟨_, hxr, hxV⟩
    obtain ⟨ρ₀', hρ₀'⟩ := hex j ⟨_, hxr', hxV⟩
    obtain ⟨hρ₀0, hρ₀ord⟩ := hord i ρ₀ ⟨_, hxr, hxV⟩ hρ₀
    obtain ⟨hρ₀0', hρ₀ord'⟩ := hord j ρ₀' ⟨_, hxr', hxV⟩ hρ₀'
    have hdnc' : IsDoubleNormalCrossingPoint (ι ≫ sS) 1 ((N.n j).base P'.genericPoint) :=
      hPP' ▸ hdnc
    obtain ⟨c, hc, hc'⟩ := hnode i j P P' ρ₀ ρ₀' hρ₀ hρ₀' hPP' hxV hdnc hne
    obtain ⟨h, -, hh⟩ := exists_residue_eq_smul hdim hGm hxU hxV hgen hτ
    have hPη : (N.n i ≫ ι).base P.genericPoint ∈ U ⊓ V := ⟨hxU, hxV⟩
    have hPη' : (N.n j ≫ ι).base P'.genericPoint ∈ U ⊓ V := by
      change ι.base ((N.n j).base P'.genericPoint) ∈ U ⊓ V
      rw [← hPP']; exact hPη
    have hη : (N.n i ≫ ι).base (genericPoint (N.X i)) ∈ U ⊓ V :=
      (((genericPoint_spec (N.X i)).specializes trivial).map
        (N.n i ≫ ι).base.hom.continuous).mem_open (U ⊓ V).isOpen hPη
    have hη' : (N.n j ≫ ι).base (genericPoint (N.X j)) ∈ U ⊓ V :=
      (((genericPoint_spec (N.X j)).specializes trivial).map
        (N.n j ≫ ι).base.hom.continuous).mem_open (U ⊓ V).isOpen hPη'
    have heq := (cast_eq _ (ρ i)).symm.trans
      (hh (N.n i ≫ ι) Γ hΓ ρ₀ _ hη hρ₀ (hρ i ⟨_, hxr, hxU⟩))
    have heq' := (cast_eq _ (ρ j)).symm.trans
      (hh (N.n j ≫ ι) Γ' hΓ' ρ₀' _ hη' hρ₀' (hρ j ⟨_, hxr', hxU⟩))
    -- the value of `h` at the node
    have hxc : IsClosed ({ι.base ((N.n i).base P.genericPoint)} : Set S) := by
      rw [← Set.image_singleton]
      exact ι.isClosedEmbedding.isClosedMap _ hdnc.2.1
    obtain ⟨a, ha⟩ := exists_const_sub_vanishes (sS := sS) hxc hPη h
    haveI : LocallyOfFiniteType (N.n i ≫ ι ≫ sS) := (N.isNormalVariety i).1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (N.n j ≫ ι ≫ sS) := (N.isNormalVariety j).1.toLocallyOfFiniteType
    have hcb : N.componentBoundaryCoeff Δ i P = 1 := by
      simp [NormalizationComponents.componentBoundaryCoeff, hdnc]
    have hcb' : N.componentBoundaryCoeff Δ j P' = 1 := by
      simp [NormalizationComponents.componentBoundaryCoeff, hdnc']
    have hm1 : -(m : ℤ) ≤ P.ordForm (k := k) ρ₀ := by
      have := hρ₀ord P hxV
      rw [hcb, mul_one] at this
      exact_mod_cast this.ge
    have hm2 : -(m : ℤ) ≤ P'.ordForm (k := k) ρ₀' := by
      have := hρ₀ord' P' (by rw [← hPP']; exact hxV)
      rw [hcb', mul_one] at this
      exact_mod_cast this.ge
    refine ⟨a * c, ?_, ?_⟩
    · rw [heq]
      exact isLeadingCoeff_smul (toNat_trdeg_component hdim hfl i) hc hρ₀0 hm1 a
        (ha (N.n i ≫ ι) P rfl)
    · rw [heq']
      exact isLeadingCoeff_smul (toNat_trdeg_component hdim hfl j) hc' hρ₀0' hm2 a
        (ha (N.n j ≫ ι) P' (by simp [hPP']))

/-- The residues of a section of `𝒪_S(m(K_S + B))` over `U` all vanish exactly when it is a
section of `𝒪_S(m(K_S + B) - ⌊B⌋)`. -/
private theorem isPoincareResidue_zero_iff (hdim : topologicalKrullDim S = 2)
    (hfl : IsFloorNormalization sS B ι N) (hGm : Divisor.toQDivisor Gm = (m : ℚ) • B)
    (hB01 : ∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1)
    (hres : HasResidueGenerators sS B ι N Δ m) {U : S.Opens} {τ : RationalPluriForms sS 2 m}
    (hτ : τ ∈ pluricanonicalSections sS 2 m Gm U) :
    (∀ i : N.ι, (Set.range (N.n i ≫ ι).base ∩ U).Nonempty →
        IsPoincareResidue sS (N.n i ≫ ι) 1 m τ
          (cast (congrArg (fun f => RationalPluriForms f 1 m)
            (Category.assoc (N.n i) ι sS).symm) (0 : RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m))) ↔
      τ ∈ pluricanonicalSections sS 2 m (Gm - B.roundDown) U := by
  have htr := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hdim
  have hGmc : ∀ Γ : Mori.PrimeDivisor S, (Gm.coeff Γ : ℚ) = m * B.coeff Γ := fun Γ => by
    have := congrArg (fun D : QDivisor S => D.coeff Γ) hGm
    simpa [Divisor.coeff_toQDivisor] using this
  have hfloor : ∀ Γ : Mori.PrimeDivisor S,
      B.roundDown.coeff Γ = if B.coeff Γ = 1 then 1 else 0 := fun Γ => by
    rw [DivisorWithCoeffs.coeff_roundDown]
    split_ifs with h1
    · rw [h1]; simp
    · exact Int.floor_eq_zero_iff.mpr ⟨(hB01 Γ).1, lt_of_le_of_ne (hB01 Γ).2 h1⟩
  -- the local picture along a component through a point of `U`
  have key : ∀ (i : N.ι) (Γ : Mori.PrimeDivisor S),
      (N.n i ≫ ι).base (genericPoint (N.X i)) = Γ.genericPoint → B.coeff Γ = 1 →
      (Γ.support ∩ (U : Set S)).Nonempty →
      ((∃ ρ, IsPoincareResidue sS (N.n i ≫ ι) 1 m τ ρ ∧ ρ = 0) ↔
        (τ ≠ 0 → 1 - (m : ℤ) ≤ Γ.ordForm τ)) := by
    intro i Γ hΓ hB1 ⟨x, hxΓ, hxU⟩
    haveI := hfl.isClosedImmersion i
    have hxr : x ∈ Set.range (N.n i ≫ ι).base := by
      rw [range_eq_support (N.n i ≫ ι) Γ hΓ]; exact hxΓ
    obtain ⟨V, hxV, τ₀, hgen, hex, hord, -⟩ := hres x
    obtain ⟨ρ₀, hρ₀⟩ := hex i ⟨_, hxr, hxV⟩
    obtain ⟨hρ₀0, -⟩ := hord i ρ₀ ⟨_, hxr, hxV⟩ hρ₀
    obtain ⟨h, hτh, hh⟩ := exists_residue_eq_smul hdim hGm hxU hxV hgen hτ
    have hη : (N.n i ≫ ι).base (genericPoint (N.X i)) ∈ U ⊓ V := by
      obtain ⟨y, rfl⟩ := hxr
      exact (((genericPoint_spec (N.X i)).specializes trivial).map
        (N.n i ≫ ι).base.hom.continuous).mem_open (U ⊓ V).isOpen ⟨hxU, hxV⟩
    haveI : Nonempty (U ⊓ V : S.Opens) := ⟨⟨x, hxU, hxV⟩⟩
    haveI : Nonempty ((N.n i ≫ ι) ⁻¹ᵁ (U ⊓ V)) := ⟨⟨genericPoint _, hη⟩⟩
    have hres' : IsPoincareResidue sS (N.n i ≫ ι) 1 m τ
        ((N.X i).germToFunctionField ((N.n i ≫ ι) ⁻¹ᵁ (U ⊓ V)) ((N.n i ≫ ι).app _ h) • ρ₀) := by
      rw [hτh]; exact isPoincareResidue_germToFunctionField_smul hρ₀ hη h
    have hzero := germToFunctionField_app_eq_zero_iff (N.n i ≫ ι) Γ hΓ hη h
    have hΓV : (Γ.support ∩ (V : Set S)).Nonempty := ⟨x, hxΓ, hxV⟩
    have hgΓ := hgen.2 Γ hΓV
    rw [hB1, mul_one] at hgΓ
    have hτ₀Γ : Γ.ordForm τ₀ = -(m : ℤ) := by
      have : ((Γ.ordForm τ₀ : ℤ) : ℚ) = -(m : ℚ) := by linarith
      exact_mod_cast this
    constructor
    · rintro ⟨ρ, hρ, rfl⟩ hτ0
      have h0 := MMP.Fourfold.isPoincareResidue_unique hΓ hρ hres'
      have hf0 := (smul_eq_zero.mp h0.symm).resolve_right hρ₀0
      rcases hzero.mp hf0 with hg | hg
      · exact absurd (by rw [hτh, hg, zero_smul]) hτ0
      · rw [hτh, Γ.ordForm_smul htr (by rintro h'; apply hτ0; rw [hτh, h', zero_smul])
          hgen.1, hτ₀Γ]
        omega
    · intro hle
      refine ⟨_, hres', ?_⟩
      have : (N.X i).germToFunctionField ((N.n i ≫ ι) ⁻¹ᵁ (U ⊓ V)) ((N.n i ≫ ι).app _ h) = 0 := by
        refine hzero.mpr ?_
        by_cases hg : S.germToFunctionField (U ⊓ V) h = 0
        · exact Or.inl hg
        · refine Or.inr ?_
          have hτ0 : τ ≠ 0 := by rw [hτh]; exact smul_ne_zero hg hgen.1
          have := hle hτ0
          rw [hτh, Γ.ordForm_smul htr hg hgen.1, hτ₀Γ] at this
          omega
      rw [this, zero_smul]
  constructor
  · intro H
    refine ⟨hτ.1, fun Γ hΓU hτ0 => ?_⟩
    have hle := hτ.2 Γ hΓU hτ0
    rw [DivisorWithCoeffs.coeff_sub, hfloor]
    split_ifs with hB1
    · obtain ⟨i, hi⟩ := hfl.exists_index Γ hB1
      haveI := hfl.isClosedImmersion i
      have hiU : (Set.range (N.n i ≫ ι).base ∩ U).Nonempty := by
        rwa [range_eq_support (N.n i ≫ ι) Γ hi]
      have := ((key i Γ hi hB1 hΓU).mp ⟨_, H i hiU, cast_eq _ _⟩) hτ0
      have h2 : (Gm.coeff Γ : ℚ) = m := by rw [hGmc, hB1, mul_one]
      have h3 : Gm.coeff Γ = (m : ℤ) := by exact_mod_cast h2
      omega
    · omega
  · intro H i hi
    obtain ⟨Γ, hB1, hΓ⟩ := hfl.exists_primeDivisor i
    haveI := hfl.isClosedImmersion i
    have hΓU : (Γ.support ∩ (U : Set S)).Nonempty := by
      rwa [← range_eq_support (N.n i ≫ ι) Γ hΓ]
    obtain ⟨ρ, hρ, hρ0⟩ := (key i Γ hΓ hB1 hΓU).mpr fun hτ0 => by
      have := H.2 Γ hΓU hτ0
      rw [DivisorWithCoeffs.coeff_sub, hfloor, if_pos hB1] at this
      have h2 : (Gm.coeff Γ : ℚ) = m := by rw [hGmc, hB1, mul_one]
      have h3 : Gm.coeff Γ = (m : ℤ) := by exact_mod_cast h2
      omega
    rw [hρ0] at hρ
    exact (cast_eq _ (0 : RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m)).symm ▸ hρ

/-- Over an affine open `U`, every section of `ω_C^{⊗m}(mΔ)` over `C ∩ U` is the family of
residues of a section of `𝒪_S(m(K_S + B))` over `U`. -/
private theorem exists_isPoincareResidue_of_isAffineOpen [CompactSpace S]
    (hdim : topologicalKrullDim S = 2)
    (hfl : IsFloorNormalization sS B ι N) (hGm : Divisor.toQDivisor Gm = (m : ℚ) • B)
    (hres : HasResidueGenerators sS B ι N Δ m) {U : S.Opens} (hU : IsAffineOpen U)
    (s : ∀ i : N.ι, RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m)
    (hs1 : ∀ i (P : Mori.PrimeDivisor (N.X i)), ι.base ((N.n i).base P.genericPoint) ∈ U →
        s i ≠ 0 → 0 ≤ ((P.ordForm (s i) : ℤ) : ℚ) + m * N.componentBoundaryCoeff Δ i P)
    (hs2 : ∀ (i j : N.ι) (P : Mori.PrimeDivisor (N.X i)) (P' : Mori.PrimeDivisor (N.X j)),
        (N.n i).base P.genericPoint = (N.n j).base P'.genericPoint →
        ι.base ((N.n i).base P.genericPoint) ∈ U →
        IsDoubleNormalCrossingPoint (ι ≫ sS) 1 ((N.n i).base P.genericPoint) →
        (⟨i, P.genericPoint⟩ : Σ i, N.X i) ≠ ⟨j, P'.genericPoint⟩ →
        ∃ c : k, N.IsLeadingCoeff i P (s i) c ∧ N.IsLeadingCoeff j P' (s j) c) :
    ∃ τ ∈ pluricanonicalSections sS 2 m Gm U, ∀ i, (Set.range (N.n i ≫ ι).base ∩ U).Nonempty →
      IsPoincareResidue sS (N.n i ≫ ι) 1 m τ
        (cast (congrArg (fun f => RationalPluriForms f 1 m)
          (Category.assoc (N.n i) ι sS).symm) (s i)) := by
  classical
  by_cases hU0 : U = ⊥
  · refine ⟨0, zero_mem _, fun i hi => ?_⟩
    exfalso
    obtain ⟨x, -, hx⟩ := hi
    rw [hU0] at hx
    exact hx
  haveI : Nonempty U := by
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty U).mp hU0
    exact ⟨⟨x, hx⟩⟩
  -- local lifts at every point of `U`, on basic opens of `U`
  choose W hxW hWU τ' hτ' hres' using fun x : U =>
    exists_local_lift hdim hfl hGm hres s hs1 hs2 x.1 x.2
  choose f hfW hxf using fun x : U => hU.exists_basicOpen_le ⟨x.1, hxW x⟩ x.2
  have hτD : ∀ x : U, τ' x ∈ pluricanonicalSections sS 2 m Gm (S.basicOpen (f x)) := fun x => by
    haveI : Nonempty (S.basicOpen (f x)) := ⟨⟨x.1, hxf x⟩⟩
    exact mem_pluricanonicalSections_of_le (hτ' x) (hfW x)
  choose n hn hτU hvan using fun x : U => exists_pow_smul_mem (Gm := Gm) hdim (f x) (hτD x)
  let g : U → Γ(S, U) := fun x => f x ^ n x
  -- the `g x` generate the unit ideal of `Γ(S, U)`
  have hspan : Ideal.span (Set.range g) = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hxU
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨⟨g ⟨x, hxU⟩, ⟨x, hxU⟩, rfl⟩, ?_⟩
    change x ∈ S.basicOpen (f ⟨x, hxU⟩ ^ n ⟨x, hxU⟩)
    rw [Scheme.basicOpen_pow _ _ (hn _)]
    exact hxf _
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (hspan ▸ Submodule.mem_top : (1 : Γ(S, U)) ∈ Ideal.span (Set.range g))
  refine ⟨∑ x ∈ c.support, S.germToFunctionField U (c x) • (S.germToFunctionField U (g x) • τ' x),
    sum_mem fun x _ => germToFunctionField_smul_mem_of_mem hdim (c x) (hτU x), fun i hi => ?_⟩
  haveI := hfl.isClosedImmersion i
  obtain ⟨Γ, hB1, hΓ⟩ := hfl.exists_primeDivisor i
  have hηU : (N.n i ≫ ι).base (genericPoint (N.X i)) ∈ U := by
    obtain ⟨_, ⟨y, rfl⟩, hyU⟩ := hi
    exact (((genericPoint_spec (N.X i)).specializes trivial).map
      (N.n i ≫ ι).base.hom.continuous).mem_open U.isOpen hyU
  haveI : Nonempty ((N.n i ≫ ι) ⁻¹ᵁ U) := ⟨⟨_, hηU⟩⟩
  let r : Γ(S, U) →+* (N.X i).functionField :=
    ((N.n i ≫ ι).app U ≫ (N.X i).germToFunctionField _).hom
  -- the residue of each term
  have hterm : ∀ x : U, IsPoincareResidue sS (N.n i ≫ ι) 1 m
      (S.germToFunctionField U (g x) • τ' x) (r (g x) • s i) := by
    intro x
    by_cases hD : (Set.range (N.n i ≫ ι).base ∩ S.basicOpen (f x)).Nonempty
    · have hiW : (Set.range (N.n i ≫ ι).base ∩ W x).Nonempty :=
        hD.mono (Set.inter_subset_inter_right _ (hfW x))
      exact isPoincareResidue_germToFunctionField_smul (hres' x i hiW) hηU (g x)
    · have hΓU : (Γ.support ∩ (U : Set S)).Nonempty := by
        rw [← range_eq_support _ Γ hΓ]; exact hi
      have hΓD : ¬ (Γ.support ∩ (S.basicOpen (f x) : Set S)).Nonempty := by
        rwa [← range_eq_support _ Γ hΓ]
      have h0 := isPoincareResidue_zero_of_ordGE hdim hfl hGm hres (hτU x) i hi Γ hΓ hB1
        (hvan x Γ hΓU hΓD)
      have hη' : (N.n i ≫ ι).base (genericPoint (N.X i)) ∉ S.basicOpen (f x) := fun h =>
        hD ⟨_, ⟨_, rfl⟩, h⟩
      have hr0 : r (g x) = 0 := by
        change r (f x ^ n x) = 0
        rw [map_pow]
        have : r (f x) = 0 :=
          germToFunctionField_app_eq_zero_of_notMem_basicOpen (N.n i ≫ ι) (f x) hηU hη'
        rw [this, zero_pow (hn x).ne']
      rw [hr0, zero_smul]
      exact h0
  -- the residue of the combination
  have hsum := isPoincareResidue_sum hdim hfl hGm hres c.support
    (fun x => S.germToFunctionField U (c x) • (S.germToFunctionField U (g x) • τ' x))
    (fun x _ => germToFunctionField_smul_mem_of_mem hdim (c x) (hτU x)) i hi
    (fun x => r (c x) • r (g x) • s i)
    (fun x _ => isPoincareResidue_germToFunctionField_smul (hterm x) hηU (c x))
  have hone : ∑ x ∈ c.support, r (c x) • r (g x) • s i = s i := by
    simp_rw [smul_smul, ← Finset.sum_smul, ← map_mul, ← map_sum]
    have : ∑ x ∈ c.support, c x * g x = 1 := hc
    rw [this, map_one, one_smul]
  have hone' : (∑ x ∈ c.support, r (c x) • r (g x) • s i :
      RationalPluriForms ((N.n i ≫ ι) ≫ sS) 1 m) = s i := hone
  rw [hone'] at hsum
  exact (cast_eq _ (s i)).symm ▸ hsum

end Sections

section NodeCompletion

open IsLocalRing

/-- **Cohen structure on a regular local ring of dimension two.** Let `R` be a Noetherian local
`k`-algebra with residue field `k` and `z₀, z₁` a regular system of parameters. Then
`R̂ ⧸ (z₀z₁) ≅ k[[X₀, X₁]] ⧸ (X₀X₁)`, compatibly with the constants. -/
private theorem exists_ringEquiv_adicCompletion_quotient_mul (k R : Type*) [Field k] [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [Algebra k R]
    (hres : ∀ r : R, ∃ c : k, r - algebraMap k R c ∈ maximalIdeal R)
    {z : Fin 2 → R} (hz : IsRegularSystemOfParameters z) :
    ∃ e : AdicCompletion (maximalIdeal R) R ⧸
        Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) (z 0 * z 1)} ≃+*
      MvPowerSeries (Fin 2) k ⧸
        Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)},
      ∀ c : k, e (Ideal.Quotient.mk _ (algebraMap R _ (algebraMap k R c))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C c) := by
  set Â := AdicCompletion (maximalIdeal R) R
  have hspan := MMP.Flips.ResolutionInputs.span_range_algebraMap_eq_maximalIdeal hz
  obtain ⟨F, hFs, hFX, hFC⟩ := Stacks.CompleteLocalRing.CohenStructure.exists_surjective_eval₂Hom
    (maximalIdeal Â) (fun i => algebraMap R Â (z i)) hspan
    ((algebraMap R Â).comp (algebraMap k R)) (by
      intro y
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ (maximalIdeal R) w)
      obtain ⟨c, hc⟩ := hres r
      refine ⟨c, ?_⟩
      rw [RingHom.comp_apply, Ideal.Quotient.eq, AdicCompletion.maximalIdeal_eq_map,
        ← AdicCompletion.ker_evalOneₐ_eq_map _ (IsNoetherian.noetherian _)]
      change AdicCompletion.evalOneₐ (maximalIdeal R) _ = 0
      rw [map_sub, ← hr, RingHom.comp_apply, AlgHom.commutes, Ideal.Quotient.algebraMap_eq,
        ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← neg_sub]
      exact neg_mem hc)
  have hinj := MMP.Flips.ResolutionInputs.injective_of_surjective_of_ringKrullDim_le F hFs
    (MvPowerSeries.ringKrullDim_le k 2)
    (by rw [IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal, hz.2])
  let eF : MvPowerSeries (Fin 2) k ≃+* Â := RingEquiv.ofBijective F ⟨hinj, hFs⟩
  have heF : eF.symm (algebraMap R Â (z 0 * z 1)) = MvPowerSeries.X 0 * MvPowerSeries.X 1 := by
    rw [RingEquiv.symm_apply_eq]
    change _ = F _
    rw [map_mul, map_mul, hFX, hFX]
  refine ⟨Ideal.quotientEquiv _ _ eF.symm ?_, fun c => ?_⟩
  · rw [Ideal.map_span, Set.image_singleton]
    erw [heF]
  · have : eF.symm (algebraMap R Â (algebraMap k R c)) = MvPowerSeries.C c := by
      rw [RingEquiv.symm_apply_eq]; exact (hFC c).symm
    change Ideal.Quotient.mk _ (eF.symm _) = _
    rw [this]

/-- **Completion commutes with quotients**: `(R ⧸ J)^ ≅ R̂ ⧸ J R̂`, compatibly with `R`. -/
private theorem exists_ringEquiv_adicCompletion_quotient {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J : Ideal R) [IsLocalRing (R ⧸ J)] :
    ∃ E : AdicCompletion (maximalIdeal (R ⧸ J)) (R ⧸ J) ≃+*
        AdicCompletion (maximalIdeal R) R ⧸ J.map (algebraMap R (AdicCompletion (maximalIdeal R) R)),
      ∀ r : R, E (algebraMap (R ⧸ J) _ (Ideal.Quotient.mk J r)) =
        Ideal.Quotient.mk _ (algebraMap R _ r) := by
  refine ⟨(RingHom.quotientKerEquivOfSurjective (adicCompletionMapQuotient_surjective J)).symm.trans
    (Ideal.quotEquivOfEq (ker_adicCompletionMapQuotient J)), fun r => ?_⟩
  have h : adicCompletionMapQuotient J (algebraMap R _ r) =
      algebraMap (R ⧸ J) _ (Ideal.Quotient.mk J r) := by
    apply AdicCompletion.ext
    intro n
    rw [completionQuotientMap_val, val_algebraMap]
    rfl
  rw [RingEquiv.trans_apply, ← h]
  have h2 : (RingHom.quotientKerEquivOfSurjective (adicCompletionMapQuotient_surjective J)).symm
      (adicCompletionMapQuotient J (algebraMap R _ r)) = Ideal.Quotient.mk _ (algebraMap R _ r) := by
    rw [RingEquiv.symm_apply_eq]; rfl
  rw [h2]; rfl

/-- **The completed local ring of a node.** Let `R` be a Noetherian local `k`-algebra with
residue field `k`, `z₀, z₁` a regular system of parameters, and `φ : R → A` a surjection with
kernel `(z₀z₁)`. Then `Â ≅ k[[X₀, X₁]] ⧸ (X₀X₁)` as `k`-algebras. -/
private theorem exists_ringEquiv_adicCompletion_of_ker_eq (k R A : Type*) [Field k]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra k R] [CommRing A] [IsLocalRing A]
    (hres : ∀ r : R, ∃ c : k, r - algebraMap k R c ∈ maximalIdeal R)
    {z : Fin 2 → R} (hz : IsRegularSystemOfParameters z) (φ : R →+* A)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = Ideal.span {z 0 * z 1}) :
    ∃ e : AdicCompletion (maximalIdeal A) A ≃+*
      MvPowerSeries (Fin 2) k ⧸
        Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)},
      ∀ c : k, e (algebraMap A _ (φ (algebraMap k R c))) = Ideal.Quotient.mk _ (MvPowerSeries.C c) := by
  set J := RingHom.ker φ
  let eA : R ⧸ J ≃+* A := RingHom.quotientKerEquivOfSurjective hφ
  haveI : Nontrivial (R ⧸ J) := eA.toEquiv.nontrivial
  haveI : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  obtain ⟨E₁, hE₁⟩ := Stacks.AdicCompletionFibreUniverse.exists_adicCompletion_ringEquiv_of_map_eq
    eA.symm (maximalIdeal A) (maximalIdeal (R ⧸ J)) (IsLocalRing.map_ringEquiv_maximalIdeal eA.symm)
  obtain ⟨E₂, hE₂⟩ := exists_ringEquiv_adicCompletion_quotient J
  have hJ : J.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) =
      Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) (z 0 * z 1)} := by
    rw [hker, Ideal.map_span, Set.image_singleton]
  obtain ⟨E₃, hE₃⟩ := exists_ringEquiv_adicCompletion_quotient_mul k R hres hz
  refine ⟨E₁.trans (E₂.trans ((Ideal.quotEquivOfEq hJ).trans E₃)), fun c => ?_⟩
  simp only [RingEquiv.trans_apply]
  rw [hE₁]
  have : eA.symm (φ (algebraMap k R c)) = Ideal.Quotient.mk J (algebraMap k R c) := by
    rw [RingEquiv.symm_apply_eq]; rfl
  rw [this, hE₂, Ideal.quotEquivOfEq_mk, hE₃]

/-- Neither member of a regular system of parameters of length two divides the other. -/
private theorem notMem_span_singleton_of_isRegularSystemOfParameters {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {z : Fin 2 → R} (hz : IsRegularSystemOfParameters z)
    {i j : Fin 2} (hij : i ≠ j) : z i ∉ Ideal.span {z j} := by
  intro h
  have hm : maximalIdeal R = Ideal.span {z j} := by
    rw [← hz.1]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨l, rfl⟩
      by_cases hl : l = j
      · subst hl; exact Ideal.mem_span_singleton_self _
      · have : l = i := by fin_cases l <;> fin_cases i <;> fin_cases j <;> simp_all
        subst this; exact h
    · exact Ideal.span_mono (by rintro _ rfl; exact ⟨j, rfl⟩)
  have h1 := ringKrullDim_le_spanFinrank_maximalIdeal (R := R)
  have h2 : (Ideal.span {z j}).spanFinrank ≤ 1 := by
    simpa using Submodule.spanFinrank_span_le_ncard_of_finite (R := R)
      (s := ({z j} : Set R)) (Set.finite_singleton _)
  rw [hm, hz.2] at h1
  have h3 : ((2 : ℕ) : WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞) := h1.trans (by exact_mod_cast h2)
  exact absurd (WithBot.coe_le_coe.mp h3) (by decide)

/-- In a domain, `(a) ∩ (b) = (ab)` for a prime `b` not dividing `a`. -/
private theorem span_singleton_inf_span_singleton_of_prime {R : Type*} [CommRing R] [IsDomain R]
    {a b : R} (hb : Prime b) (hab : a ∉ Ideal.span {b}) :
    Ideal.span {a} ⊓ Ideal.span {b} = Ideal.span {a * b} := by
  apply le_antisymm
  · intro y hy
    obtain ⟨ha', hb'⟩ := Submodule.mem_inf.mp hy
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha'
    rw [Ideal.mem_span_singleton] at hb' hab ⊢
    obtain ⟨s, rfl⟩ := (hb.dvd_or_dvd hb').resolve_right hab
    exact ⟨s, by ring⟩
  · rw [← Ideal.span_singleton_mul_span_singleton]
    exact Ideal.mul_le_inf

end NodeCompletion

section FloorPerturbation

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {S : Scheme.{0}}
  {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
  {K : Divisor S} {B : QDivisor S}

/-- **The dlt floor minus one component.** For a dlt surface pair `(S, B)` and a component `Γ` of
`⌊B⌋`, the pair `(S, B - ½(⌊B⌋ - Γ))` is plt; it agrees with `B` off the other components of
`⌊B⌋`. -/
private theorem exists_isPltPair_sub_floor (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS)
    {Γ : Mori.PrimeDivisor S} (hΓ : B.coeff Γ = 1) :
    ∃ B'' : QDivisor S, B''.IsEffective ∧ B''.coeff Γ = 1 ∧ IsPltPair sS 2 K B'' ∧
      (∀ E : Mori.PrimeDivisor S, B''.coeff E ≠ B.coeff E →
        B.coeff E = 1 ∧ E ≠ Γ) ∧ ∀ E : Mori.PrimeDivisor S, E ≠ Γ → B''.coeff E < 1 := by
  classical
  have hB01 := hdlt.2.1
  set F : QDivisor S := Divisor.toQDivisor B.roundDown - Finsupp.single Γ 1 with hF
  have hFc : ∀ E, F.coeff E = if B.coeff E = 1 ∧ E ≠ Γ then 1 else 0 := fun E => by
    rw [hF, DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor,
      DivisorWithCoeffs.coeff_roundDown]
    by_cases hE : E = Γ
    · subst hE; rw [hΓ, DivisorWithCoeffs.coeff_single_self]; simp
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hE)]
      by_cases h1 : B.coeff E = 1
      · rw [h1]; simp [hE]
      · rw [Int.floor_eq_zero_iff.mpr ⟨(hB01 E).1, lt_of_le_of_ne (hB01 E).2 h1⟩]; simp [h1]
  set B'' : QDivisor S := B - (1 / 2 : ℚ) • F with hB''
  have hB''c : ∀ E, B''.coeff E = B.coeff E - (1 / 2) * F.coeff E := fun E => by
    rw [hB'', DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  have hB''e : B''.IsEffective := fun E => by
    rw [hB''c, hFc]
    split_ifs with h
    · rw [h.1]; norm_num
    · simpa using (hB01 E).1
  have hFe : ((1 / 2 : ℚ) • F).IsEffective := fun E => by
    rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul, hFc]
    split_ifs <;> norm_num
  have hsum : B'' + (1 / 2 : ℚ) • F = B := by rw [hB'']; abel
  have hX : IsNormalVariety k sS := hdlt.1.1
  have hdlt'' : IsDltPair sS 2 K B'' :=
    MMP.Threefold.Mori.IsDltPair.of_add ⟨hX, hdlt.1.2.1, isQCartier_of_isQFactorial sS hQ _⟩
      hB''e hFe (isQCartier_of_isQFactorial sS hQ _) (by rwa [hsum])
  have hfl : ∀ E, B''.roundDown.coeff E ≠ 0 → E = Γ := by
    intro E hE
    by_contra hEΓ
    apply hE
    rw [DivisorWithCoeffs.coeff_roundDown, hB''c, hFc]
    split_ifs with h
    · rw [h.1]; norm_num
    · have h1 : B.coeff E ≠ 1 := fun h1 => h ⟨h1, hEΓ⟩
      rw [mul_zero, sub_zero]
      exact Int.floor_eq_zero_iff.mpr ⟨(hB01 E).1, lt_of_le_of_ne (hB01 E).2 h1⟩
  have hplt : IsPltPair sS 2 K B'' :=
    hdlt''.isPltPair_of_pairwise_disjoint le_rfl
      (DivisorWithCoeffs.isEffective_iff_nonneg.mp hB''e)
      (fun P hP Q hQ hPQ => absurd ((hfl P hP).trans (hfl Q hQ).symm) hPQ)
  refine ⟨B'', hB''e, by rw [hB''c, hFc, if_neg (fun h => h.2 rfl), hΓ]; norm_num, hplt,
    fun E hE => ?_, fun E hE => ?_⟩
  · rw [hB''c, hFc] at hE
    split_ifs at hE with h
    · exact h
    · simp at hE
  · rw [hB''c, hFc]
    split_ifs with h
    · rw [h.1]; norm_num
    · have h1 : B.coeff E ≠ 1 := fun h1 => h ⟨h1, hE⟩
      simpa using lt_of_le_of_ne (hB01 E).2 h1

end FloorPerturbation

section FloorIntersection

/-- On a smooth scheme, a `ℚ`-divisor with nonnegative coefficients and two distinct components
of coefficient one through `x` has multiplicity at least two at `x`. -/
private theorem two_le_multiplicityAt {k : Type} [Field k] {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} (hsm : IsSmoothScheme sX) {Δ : QDivisor X}
    (hΔ : ∀ P, 0 ≤ Δ.coeff P) {P P' : Mori.PrimeDivisor X} (hP : Δ.coeff P = 1)
    (hP' : Δ.coeff P' = 1) (hne : P ≠ P') {x : X} (hx : x ∈ P.support)
    (hx' : x ∈ P'.support) : 2 ≤ Δ.multiplicityAt x := by
  classical
  have h1 : ∀ Q : Mori.PrimeDivisor X, x ∈ Q.support → 1 ≤ (Q.multiplicityAt x).toNat := by
    intro Q hQ
    have hne := MMP.Threefold.Resolution.multiplicityAt_ne_top Q
      (MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm Q) x
    have hle : 1 ≤ Q.multiplicityAt x := by
      refine le_iSup₂_of_le 1 ?_ (by simp)
      rw [pow_one]
      exact Q.idealSheaf.stalkIdeal_le_maximalIdeal_of_mem_support hQ
    rw [← ENat.coe_toNat hne] at hle
    exact_mod_cast hle
  have hPs : P ∈ Δ.support := Finsupp.mem_support_iff.mpr (by
    change Δ.coeff P ≠ 0; rw [hP]; exact one_ne_zero)
  have hP's : P' ∈ Δ.support := Finsupp.mem_support_iff.mpr (by
    change Δ.coeff P' ≠ 0; rw [hP']; exact one_ne_zero)
  have hterm : ∀ Q, x ∈ Q.support → Δ.coeff Q = 1 →
      (1 : ℚ) ≤ (Q.multiplicityAt x).toNat • Δ Q := by
    intro Q hQ hQ1
    change (1 : ℚ) ≤ (Q.multiplicityAt x).toNat • Δ.coeff Q
    rw [hQ1, nsmul_eq_mul, mul_one]
    exact_mod_cast h1 Q hQ
  rw [DivisorWithCoeffs.multiplicityAt, Finsupp.sum]
  have hsub : ({P, P'} : Finset (Mori.PrimeDivisor X)) ⊆ Δ.support :=
    Finset.insert_subset_iff.mpr ⟨hPs, Finset.singleton_subset_iff.mpr hP's⟩
  calc (2 : ℚ) ≤ ∑ Q ∈ ({P, P'} : Finset (Mori.PrimeDivisor X)),
        (Q.multiplicityAt x).toNat • Δ Q := by
        rw [Finset.sum_pair hne]
        linarith [hterm P hx hP, hterm P' hx' hP']
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun Q _ _ =>
        nsmul_nonneg (hΔ Q) _

/-- **Two boundary components of coefficient one through a smooth point.** If `x` is a closed
point of the smooth locus of a surface pair `(S, B)`, `B ≥ 0`, through which two components of
coefficient one pass, the exceptional curve of the blow-up of `x` has discrepancy `≤ -1`. -/
private theorem exists_isDiscrepancy_le_neg_one_of_mem_smoothLocus {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {S : Scheme.{0}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S]
    [IsNormal S] {K : Divisor S} {B : QDivisor S}
    (hpair : IsPairWith sS 2 K B) (hB0 : ∀ P, 0 ≤ B.coeff P) {Γ Γ' : Mori.PrimeDivisor S}
    (hΓ : B.coeff Γ = 1) (hΓ' : B.coeff Γ' = 1) (hne : Γ ≠ Γ') {x : S} (hx : x ∈ Γ.support)
    (hx' : x ∈ Γ'.support) (hxs : x ∈ smoothLocus sS) (hxc : IsClosed ({x} : Set S)) :
    ∃ D : DivisorOver k sS, D.f D.E.genericPoint = x ∧ ∃ a : ℚ, a ≤ -1 ∧
      IsDiscrepancy sS 2 K B D a := by
  set V := smoothLocus sS
  haveI : Nonempty V := ⟨⟨x, hxs⟩⟩
  have hV := hpair.restrictOpen V
  have hsmV : IsSmoothScheme (V.ι ≫ sS) := by
    rw [IsSmoothScheme, eq_top_iff]
    intro y _
    obtain ⟨W, hyW, hW⟩ := mem_smoothLocus_iff.1 (y.2 : V.ι y ∈ smoothLocus sS)
    refine mem_smoothLocus_iff.2 ⟨V.ι ⁻¹ᵁ W, hyW, ?_⟩
    have : Smooth (W.ι ≫ sS) := hW
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    infer_instance
  let x' : V := ⟨x, hxs⟩
  have hx'c : IsClosed ({x'} : Set V) := by
    have : ({x'} : Set V) = V.ι.base ⁻¹' {x} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ rfl, fun h => V.ι.isOpenEmbedding.injective h⟩
    rw [this]
    exact hxc.preimage V.ι.base.hom.continuous
  obtain ⟨D, hD, hDη, hDa⟩ := exists_isExceptional_isDiscrepancy_one_sub_multiplicityAt hV.1.1
    hsmV hV.2.1.topologicalKrullDim_eq hV.2.1 (B.restrictOpen V) hx'c
  obtain ⟨D₁, -, hη, -, hD₁a⟩ := hpair.exists_isDiscrepancy_of_restrictOpen V hD hDa
  refine ⟨D₁, by rw [hη, hDη]; rfl, _, ?_, hD₁a⟩
  obtain ⟨W, hW⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    V.ι Γ x' hx
  obtain ⟨W', hW'⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    V.ι Γ' x' hx'
  have hxW : x' ∈ W.support :=
    (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff V.ι W x').mp
      (hW ▸ hx)
  have hxW' : x' ∈ W'.support :=
    (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff V.ι W' x').mp
      (hW' ▸ hx')
  have hWW : W ≠ W' := fun h => hne (hW.symm.trans (h ▸ hW'))
  have h2 := two_le_multiplicityAt hsmV (Δ := B.restrictOpen V)
    (fun P => by rw [DivisorWithCoeffs.coeff_restrictOpen]; exact hB0 _)
    (by rw [DivisorWithCoeffs.coeff_restrictOpen, hW]; exact hΓ)
    (by rw [DivisorWithCoeffs.coeff_restrictOpen, hW']; exact hΓ') hWW hxW hxW'
  linarith

/-- **Germ neighbourhoods on a normal surface.** On a normal surface over a perfect field whose
smooth locus is nonempty, every point `x` has an open neighbourhood on which `x` is the only
possible singular point: the singular points have coheight two, hence are closed, and a closed
set of closed points of a Noetherian space is finite. -/
private theorem exists_nhds_forall_ne_mem_smoothLocus {k : Type} [Field k] [PerfectField k]
    {S : Scheme.{0}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hX : IsNormalVariety k sS) (hdim : topologicalKrullDim S = 2)
    (hne : (smoothLocus sS : Set S).Nonempty) (x : S) :
    ∃ V : S.Opens, x ∈ V ∧ ∀ y ∈ V, y ≠ x → y ∈ smoothLocus sS := by
  classical
  have : IsNoetherian S := {}
  set T : Set S := (smoothLocus sS : Set S)ᶜ with hTdef
  have hT : IsClosed T := (smoothLocus sS).isOpen.isClosed_compl
  have hη : genericPoint S ∈ smoothLocus sS := by
    obtain ⟨z, hz⟩ := hne
    exact ((genericPoint_spec S).specializes trivial).mem_open (smoothLocus sS).isOpen hz
  have hcoh_le : ∀ y : S, Order.coheight y ≤ 2 := by
    intro y
    have h1 := Order.coheight_le_krullDim y
    rw [Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim, hdim] at h1
    have h2 : ((Order.coheight y : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := h1
    exact WithBot.coe_le_coe.mp h2
  have hsing : ∀ y ∈ T, Order.coheight y = 2 := by
    intro y hy
    refine le_antisymm (hcoh_le y) ?_
    by_contra hlt
    push Not at hlt
    have hle : Order.coheight y ≤ 1 := Order.le_of_lt_add_one hlt
    rcases (show Order.coheight y = 0 ∨ Order.coheight y = 1 by
      generalize Order.coheight y = d at hle ⊢
      induction d using ENat.recTopCoe with
      | top => exact absurd hle (by decide)
      | coe d =>
        have : d ≤ 1 := by exact_mod_cast hle
        interval_cases d <;> simp) with h0 | h1
    · have hmax : IsMax y := Order.coheight_eq_zero.mp h0
      have hs1 : genericPoint S ⤳ y := (genericPoint_spec S).specializes trivial
      have hs2 : y ⤳ genericPoint S :=
        Scheme.le_iff_specializes.mp (hmax (Scheme.le_iff_specializes.mpr hs1))
      have : y = genericPoint S := (hs2.antisymm hs1).eq
      exact hy (this ▸ hη)
    · have := MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hX
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y h1)
      have hg := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y h1
      change (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y h1).genericPoint ∈ _ at this
      rw [hg] at this
      exact hy this
  have hclosed : ∀ y ∈ T, IsClosed ({y} : Set S) := by
    intro y hy
    rw [← closure_subset_iff_isClosed]
    intro y' hy'
    rw [Set.mem_singleton_iff]
    by_contra hne'
    have hlt : y' < y := lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr
      (specializes_iff_mem_closure.mpr hy'),
      fun h' => hne' ((Scheme.le_iff_specializes.mp h').antisymm
        (specializes_iff_mem_closure.mpr hy')).eq⟩
    have h1 := Order.coheight_add_one_le hlt
    rw [hsing y hy] at h1
    have h2 := hcoh_le y'
    have : (2 : ℕ∞) + 1 ≤ 2 := h1.trans h2
    exact absurd this (by decide)
  have hfin : T.Finite := by
    obtain ⟨𝒮, h𝒮fin, h𝒮cl, h𝒮irr, h𝒮⟩ :=
      TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hT
    rw [h𝒮]
    refine h𝒮fin.sUnion fun t ht => ?_
    obtain ⟨g, hg⟩ := QuasiSober.sober (h𝒮irr t ht) (h𝒮cl t ht)
    have hgt : g ∈ t := hg.mem
    have hgT : g ∈ T := h𝒮 ▸ Set.mem_sUnion_of_mem hgt ht
    have : t = {g} := by rw [← hg.def, (hclosed g hgT).closure_eq]
    rw [this]
    exact Set.finite_singleton g
  have hcl : IsClosed (T \ {x}) := by
    have := (hfin.diff (t := {x})).isClosed_biUnion fun y hy => hclosed y hy.1
    rwa [Set.biUnion_of_singleton] at this
  refine ⟨⟨_, hcl.isOpen_compl⟩, fun h => h.2 rfl, fun y hy hyx => ?_⟩
  by_contra hns
  exact hy ⟨hns, hyx⟩

/-- **Boundary points of a germ resolution over each boundary component.** For a resolution `g`
of a surface germ `(X, P)` and a prime divisor `C` of `X` through `P`, the birational transform
`C'` of `C` meets the fibre over `P`. -/
private theorem exists_inverseTransform_mem_fibre {k : Type} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {P : X} {g : Y ⟶ X}
    (hg : IsGermResolution sX P g) (C : Mori.PrimeDivisor X) (hPC : P ∈ C.support) :
    ∃ C' : Mori.PrimeDivisor Y, inverseTransformPrimeDivisor g C = some C' ∧
      g C'.genericPoint = C.genericPoint ∧ ∃ y ∈ C'.support, g y = P := by
  have hXs := hg.isSurfaceGerm
  have : IsProper g := hg.isSmoothResolution.isProper
  obtain ⟨U, hU, hiso⟩ := hg.isIso_away
  obtain ⟨C', hC', hgC'⟩ := exists_inverseTransformPrimeDivisor_eq_some C <|
    le_biregularLocus (V := U) hiso <| show C.genericPoint ∈ (U : Set X) by
      rw [hU]
      intro h
      have h2 := C.coheight_genericPoint
      rw [h, MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hXs.1.1 hXs.2.1
        hXs.2.2.1] at h2
      exact absurd h2 (by decide)
  obtain ⟨y, hyC', hyP⟩ : ∃ y ∈ C'.support, g y = P :=
    (AlgebraicGeometry.PrimeDivisor.support_eq_closure C ▸
      (g.isClosedMap _ C'.idealSheaf.support.isClosed).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr ⟨_, show C'.genericPoint ∈ C'.support by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact subset_closure rfl, hgC'⟩)) hPC
  exact ⟨C', hC', hgC', y, hyC', hyP⟩

/-- **Two floor components cannot meet at a singular point off the snc locus.** Let `(S, B)` be a
`ℚ`-factorial surface pair with `B ≥ 0`, two components `Γ ≠ Γ'` of coefficient one through a
closed singular point `x`, and `V ∋ x` open with `V ∖ {x}` smooth. If every exceptional divisor
over `x` has discrepancy `> -1`, then the germ `(V, x; Γ + Γ')` has positive log discrepancies on
its minimal resolution, so it is of type (3) of FA Fig. 3, which has a single boundary branch: a
contradiction. -/
private theorem false_of_notMem_smoothLocus {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {S : Scheme.{0}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] {K : Divisor S} {B : QDivisor S}
    (hpair : IsPairWith sS 2 K B) (hQ : MMP.Fourfold.IsQFactorial sS) (hB0 : ∀ P, 0 ≤ B.coeff P)
    {Γ Γ' : Mori.PrimeDivisor S} (hΓ : B.coeff Γ = 1) (hΓ' : B.coeff Γ' = 1) (hne : Γ ≠ Γ')
    {x : S} (hx : x ∈ Γ.support) (hx' : x ∈ Γ'.support) (hxc : IsClosed ({x} : Set S))
    (hxs : x ∉ smoothLocus sS) {V : S.Opens} (hxV : x ∈ V)
    (hVsm : ∀ y ∈ V, y ≠ x → y ∈ smoothLocus sS)
    (h0 : ∀ {Y : Scheme.{0}} {f : Y ⟶ V} [QuasiCompact (f ≫ V.ι ≫ sS)] [IsLocallyNoetherian Y]
      [IsNormal Y] {E : Fin 0 → Mori.PrimeDivisor Y},
      IsGermResolution (V.ι ≫ sS) ⟨x, hxV⟩ f → IsExceptionalCurveEnumeration f ⟨x, hxV⟩ E →
        IsSmoothScheme (V.ι ≫ sS))
    (hEnum : ∀ {Y : Scheme.{0}} {f : Y ⟶ V} [QuasiCompact (f ≫ V.ι ≫ sS)]
      [IsLocallyNoetherian Y], IsGermResolution (V.ι ≫ sS) ⟨x, hxV⟩ f →
        ∃ (n : ℕ) (E : Fin n → Mori.PrimeDivisor Y), IsExceptionalCurveEnumeration f ⟨x, hxV⟩ E)
    (hdisc : ∀ (D : DivisorOver k sS) (a : ℚ), D.IsExceptional → D.f D.E.genericPoint = x →
      IsDiscrepancy sS 2 K B D a → -1 < a) : False := by
  classical
  have hX := hpair.1
  have : LocallyOfFiniteType sS := hX.1.toLocallyOfFiniteType
  have : IsNoetherian S := {}
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  haveI : CompactSpace V :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  set sV := V.ι ≫ sS with hsV
  have hsmι : ∀ y : V, y ∈ smoothLocus sV ↔ V.ι y ∈ smoothLocus sS := by
    have : LocallyOfFinitePresentation sS :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
    intro y
    rw [smoothLocus_eq_smoothLocus, smoothLocus_eq_smoothLocus,
      ← Scheme.Hom.preimage_smoothLocus_eq]
    rfl
  -- the pair `(S, Γ + Γ')` and the restrictions to `V`
  set G : QDivisor S := Finsupp.single Γ 1 + Finsupp.single Γ' 1 with hG
  have hpairG : IsPairWith sS 2 K G := ⟨hX, hpair.2.1, MMP.Fourfold.isQCartier_of_isQFactorial sS hQ _⟩
  have hV := hpair.restrictOpen V
  have hVG := hpairG.restrictOpen V
  have hVdim : topologicalKrullDim V = 2 := by exact_mod_cast hV.2.1.topologicalKrullDim_eq
  let x' : V := ⟨x, hxV⟩
  have hx'c : IsClosed ({x'} : Set V) := by
    have : ({x'} : Set V) = V.ι.base ⁻¹' {x} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ rfl, fun h => V.ι.isOpenEmbedding.injective h⟩
    rw [this]
    exact hxc.preimage V.ι.base.hom.continuous
  have hgerm : IsSurfaceGerm sV x' := ⟨hV.1, hVdim, hx'c, fun y hy =>
    (hsmι y).2 (hVsm _ y.2 fun h => hy (Subtype.ext h))⟩
  -- the two branches on `V`
  obtain ⟨W, hW⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    V.ι Γ x' hx
  obtain ⟨W', hW'⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    V.ι Γ' x' hx'
  have hxW : x' ∈ W.support :=
    (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff V.ι W x').mp (hW ▸ hx)
  have hxW' : x' ∈ W'.support :=
    (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff V.ι W' x').mp
      (hW' ▸ hx')
  have hWW : W ≠ W' := fun h => hne (hW.symm.trans (h ▸ hW'))
  have hmapW : ∀ E, OpenWeilRestriction.primeDivisorMap V.ι E = Γ ↔ E = W := fun E =>
    ⟨fun h => OpenWeilRestriction.primeDivisorMap_injective V.ι (h.trans hW.symm),
      fun h => h ▸ hW⟩
  have hmapW' : ∀ E, OpenWeilRestriction.primeDivisorMap V.ι E = Γ' ↔ E = W' := fun E =>
    ⟨fun h => OpenWeilRestriction.primeDivisorMap_injective V.ι (h.trans hW'.symm),
      fun h => h ▸ hW'⟩
  set Bg : QDivisor V := G.restrictOpen V with hBgdef
  have hBgc : ∀ E, Bg.coeff E = (if E = W then 1 else 0) + (if E = W' then 1 else 0) := by
    intro E
    rw [hBgdef, DivisorWithCoeffs.coeff_restrictOpen, hG, DivisorWithCoeffs.coeff_add]
    simp only [DivisorWithCoeffs.coeff, Finsupp.single_apply, eq_comm (a := Γ),
      eq_comm (a := Γ'), hmapW, hmapW']
  have hBgeq : Bg = Finsupp.single W 1 + Finsupp.single W' 1 := by
    refine DivisorWithCoeffs.ext' fun E => ?_
    rw [hBgc, DivisorWithCoeffs.coeff_add]
    simp only [DivisorWithCoeffs.coeff, Finsupp.single_apply, eq_comm (a := W), eq_comm (a := W')]
  have hBgW : Bg.coeff W = 1 := by rw [hBgc, if_pos rfl, if_neg hWW, add_zero]
  have hBgW' : Bg.coeff W' = 1 := by rw [hBgc, if_neg hWW.symm, if_pos rfl, zero_add]
  have hsuppBg : ∀ E, Bg.coeff E ≠ 0 → E = W ∨ E = W' := by
    intro E hE
    rw [hBgc] at hE
    by_contra h
    push Not at h
    rw [if_neg h.1, if_neg h.2, add_zero] at hE
    exact hE rfl
  have hBgle : ∀ E, Bg.coeff E ≤ (B.restrictOpen V).coeff E := by
    intro E
    rw [show (B.restrictOpen V).coeff E = B.coeff (OpenWeilRestriction.primeDivisorMap V.ι E)
      from rfl]
    rcases em (E = W) with rfl | h1
    · rw [hBgW, hW, hΓ]
    rcases em (E = W') with rfl | h2
    · rw [hBgW', hW', hΓ']
    rw [hBgc, if_neg h1, if_neg h2, add_zero]
    exact hB0 _
  have hB : IsSurfaceGermWithBoundary sV x' Bg := by
    refine ⟨hgerm, fun C hC => ?_, fun C => ?_⟩
    · rcases hsuppBg C (Finsupp.mem_support_iff.mp hC) with rfl | rfl
      · exact hxW
      · exact hxW'
    · change 0 ≤ Bg.coeff C ∧ Bg.coeff C ≤ 1
      rw [hBgc]
      split_ifs with h1 h2 <;> first | (subst h1; subst h2; exact absurd rfl hWW) | norm_num
  have hred : IsReducedBoundary Bg := by
    intro C hC
    change Bg.coeff C = 1
    rcases hsuppBg C (Finsupp.mem_support_iff.mp hC) with rfl | rfl
    · exact hBgW
    · exact hBgW'
  have hBg0 : Bg ≠ 0 := fun h => by
    have := hBgW
    rw [h] at this
    exact zero_ne_one this
  -- the minimal resolution of the germ has an exceptional curve
  obtain ⟨Y, f, _, _, _, hf⟩ := exists_isMinimalGermResolution sV hgerm
  obtain ⟨n, E, hE⟩ := hEnum hf.1
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      have hsm := h0 hf.1 hE
      exact hxs ((hsmι x').1 (by rw [hsm]; trivial))
    · exact hn
  -- the log discrepancies are positive
  have hKB : HoldsOnGerm ({x'} : Set V.toScheme) fun U : V.toScheme.Opens => IsCartierCombination
      (DivisorWithCoeffs.restrictOpen U (Divisor.toRDivisor (K.restrictOpen V) +
        QDivisor.toRDivisor Bg)) := by
    refine ⟨⊤, by simp, ?_⟩
    haveI : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨x', trivial⟩⟩
    have hq := (hVG.restrictOpen ⊤).2.2
    obtain ⟨m, r, L, hL, hsum⟩ := (MMP.Mori.QDivisor.isCartierCombination_iff_isQCartier _).mpr hq
    refine ⟨m, fun j => (r j : ℝ), L, hL, ?_⟩
    refine DivisorWithCoeffs.ext' fun P => ?_
    have hc := congrArg (fun D : QDivisor _ => D.coeff P) hsum
    simp only [DivisorWithCoeffs.coeff, Finsupp.finset_sum_apply, Finsupp.smul_apply,
      smul_eq_mul, Finsupp.add_apply] at hc ⊢
    change ((K.restrictOpen V) (OpenWeilRestriction.primeDivisorMap (⊤ : V.toScheme.Opens).ι P) : ℝ) +
      ((Bg (OpenWeilRestriction.primeDivisorMap (⊤ : V.toScheme.Opens).ι P) : ℚ) : ℝ) = _
    have hc' : ((((K.restrictOpen V) (OpenWeilRestriction.primeDivisorMap (⊤ : V.toScheme.Opens).ι P) :
        ℚ) + Bg (OpenWeilRestriction.primeDivisorMap (⊤ : V.toScheme.Opens).ι P) : ℚ) : ℝ) =
        ((∑ j, r j * ((L j).mapCoeffs (Int.cast : ℤ → ℚ) Int.cast_zero) P : ℚ) : ℝ) := by
      rw [← hc]; rfl
    rw [Rat.cast_add, Rat.cast_intCast] at hc'
    rw [hc', Rat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [DivisorWithCoeffs.mapCoeffs]
  have hpos : ∀ a : Fin n → ℚ, IsGermLogDiscrepancyVector sV x' Bg f E a → ∀ j, 0 < a j := by
    intro a ha j
    obtain ⟨-, hgr, hE', -⟩ := id ha
    obtain ⟨hY, -, -⟩ := hgr.isSmoothResolution.isNormalVariety hV.1
    have hg := hgr.isSmoothResolution.isBirationalMorphism
    have hp := hgr.isSmoothResolution.isProper
    have hlog := ha.isLogDiscrepancy hV.2.1 hKB j hY hg hp
    let PD : ProperDivisorOver k sV := ProperDivisorOver.mk ⟨Y, f, hY, hg, E j⟩ hp
    have hlogI := (ProperDivisorOver.isLogDiscrepancy_iff hVG PD
      hgr.isSmoothResolution.isSmoothScheme (a j)).mpr hlog
    obtain ⟨q, hq⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hVG.isPair hV.2.1
      PD.toDivisorOver
    have hlogq := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hq hp
    have h1 : ((a j : ℚ) : ℝ) = 1 + (q : ℝ) :=
      MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlogI hlogq rfl
    obtain ⟨q', hq'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hV.isPair hV.2.1
      PD.toDivisorOver
    have heff : (B.restrictOpen V - Bg).IsEffective := fun P => by
      rw [DivisorWithCoeffs.coeff_sub]
      exact sub_nonneg.mpr (hBgle P)
    have hle : q' ≤ q := MMP.Threefold.Mori.Helpers.isDiscrepancy_le_of_effective heff hq
      (by rwa [add_sub_cancel])
    have hmem : (E j).genericPoint ∈ (E j).support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have hη : f (E j).genericPoint = x' := (hE'.isGermExceptionalCurve j).1.prop.2 hmem
    have hexc : PD.toDivisorOver.IsExceptional := by
      refine (DivisorOver.isExceptional_iff_two_le_coheight hV.1 _).mpr ?_
      change 2 ≤ Order.coheight (f (E j).genericPoint)
      rw [hη, MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hV.1.1 hVdim hx'c]
    obtain ⟨D₁, hD₁, hη₁, -, hD₁a⟩ := hpair.exists_isDiscrepancy_of_restrictOpen V hexc hq'
    have hlt := hdisc D₁ q' hD₁ (by rw [hη₁]; change V.ι (f (E j).genericPoint) = x; rw [hη]; rfl)
      hD₁a
    have : (0 : ℝ) < ((a j : ℚ) : ℝ) := by
      rw [h1]
      have : (-1 : ℝ) < (q : ℝ) := by exact_mod_cast hlt.trans_le hle
      linarith
    exact_mod_cast this
  obtain ⟨-, Y', f', _, _, _, n', E', hf', -, h⟩ := hf.isFig3Type3_of_pos hB hred hBg0 hE hn hpos
  have hWs : W ∈ Bg.support := Finsupp.mem_support_iff.mpr (by
    change Bg.coeff W ≠ 0; rw [hBgW]; exact one_ne_zero)
  have hW's : W' ∈ Bg.support := Finsupp.mem_support_iff.mpr (by
    change Bg.coeff W' ≠ 0; rw [hBgW']; exact one_ne_zero)
  rcases h with ⟨-, C, hsupp, -⟩ | ⟨-, pt, Γe, -, hext, -⟩
  · rw [hsupp, Finset.mem_singleton] at hWs hW's
    exact hWW (hWs.trans hW's.symm)
  -- the boundary points over `W` and `W'`
  have hbp : ∀ C : Mori.PrimeDivisor V, (C = W ∨ C = W') → ∃ C' y,
      IsGermBoundaryPoint f' x' Bg C' y ∧ f' C'.genericPoint = C.genericPoint := by
    intro C hC
    have hxC : x' ∈ C.support := by rcases hC with rfl | rfl <;> assumption
    obtain ⟨C', hC', hgC', y, hy, hyx⟩ := exists_inverseTransform_mem_fibre hf'.1 C hxC
    obtain ⟨CW, hCW, -⟩ := exists_inverseTransform_mem_fibre hf'.1 W hxW
    obtain ⟨CW', hCW', -⟩ := exists_inverseTransform_mem_fibre hf'.1 W' hxW'
    refine ⟨C', y, ⟨?_, hy, hyx⟩, hgC'⟩
    rw [hBgeq, map_add, inverseTransformDivisor_single_of_eq_some hCW,
      inverseTransformDivisor_single_of_eq_some hCW']
    have hC'W : C' = CW ∨ C' = CW' := by
      rcases hC with rfl | rfl
      · left; exact Option.some_injective _ (hC'.symm.trans hCW)
      · right; exact Option.some_injective _ (hC'.symm.trans hCW')
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    rcases hC'W with rfl | rfl
    · simp only [if_pos (rfl : C' = C')]
      split_ifs <;> norm_num
    · simp only [if_pos (rfl : C' = C')]
      split_ifs <;> norm_num
  obtain ⟨C₁, y₁, hb₁, hg₁⟩ := hbp W (Or.inl rfl)
  obtain ⟨C₂, y₂, hb₂, hg₂⟩ := hbp W' (Or.inr rfl)
  obtain ⟨l₁, hl₁⟩ := hext.exists_eq _ _ hb₁
  obtain ⟨l₂, hl₂⟩ := hext.exists_eq _ _ hb₂
  have hl : l₁ = l₂ := Subsingleton.elim _ _
  subst hl
  have hC : C₁ = C₂ := congrArg Prod.fst (hl₁.symm.trans hl₂)
  subst hC
  exact hWW (AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hg₁.symm.trans hg₂))

end FloorIntersection

section Geometry

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
  {S C : Scheme.{0}} {sS : S ⟶ Spec (.of k)}
  [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [QuasiCompact sS]
  {K : Divisor S} {B : QDivisor S} {ι : C ⟶ S} [IsClosedImmersion ι]

/-- An embedding identifies the dimension of a subset with that of its image. -/
private theorem topologicalKrullDim_image_of_isEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Topology.IsEmbedding f) (A : Set X) :
    topologicalKrullDim A = topologicalKrullDim (f '' A) := by
  have he : Topology.IsEmbedding (f ∘ ((↑) : A → X)) := hf.comp Topology.IsEmbedding.subtypeVal
  have h1 := IsHomeomorph.topologicalKrullDim_eq _ he.toHomeomorph.isHomeomorph
  have e : Set.range (f ∘ ((↑) : A → X)) = f '' A := by rw [Set.range_comp, Subtype.range_coe]
  rw [h1, e]

/-- The image of the floor is the union of the components of `⌊B⌋`. -/
private theorem range_floor (hι : ι.ker = B.roundDown.suppIdeal) :
    Set.range ι.base = {x | ∃ Γ : Mori.PrimeDivisor S, B.roundDown.coeff Γ ≠ 0 ∧
      x ∈ Γ.support} := by
  have h1 : Set.range ι.base = (ι.ker.support : Set S) := by
    rw [Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq]
  rw [h1, hι]
  ext x
  change x ∈ ((Scheme.IdealSheafData.vanishingIdeal B.roundDown.supp).support : Set S) ↔ _
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact DivisorWithCoeffs.mem_supp_iff

/-- A prime divisor of a surface is a curve. -/
private theorem topologicalKrullDim_support (hdim : topologicalKrullDim S = 2)
    [LocallyOfFiniteType sS] (Γ : Mori.PrimeDivisor S) :
    topologicalKrullDim (Γ.support : Set S) = 1 := by
  have hdim' : topologicalKrullDim S = ((1 : ℕ) : WithBot ℕ∞) + 1 := by rw [hdim]; rfl
  have hr : Set.range Γ.idealSheaf.subschemeι.base = (Γ.support : Set S) :=
    Scheme.IdealSheafData.range_subschemeι _
  have h := MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support sS hdim'
    Γ.idealSheaf.subschemeι Γ hr
  rw [← hr, ← (IsHomeomorph.topologicalKrullDim_eq _ (Topology.IsEmbedding.toHomeomorph
    Γ.idealSheaf.subschemeι.isEmbedding).isHomeomorph), h]
  rfl

/-- The preimage under an inducing map of an irreducible set inside its range is irreducible. -/
private theorem isIrreducible_preimage_of_isInducing {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Topology.IsInducing f) {t : Set Y}
    (ht : IsIrreducible t) (htr : t ⊆ Set.range f) : IsIrreducible (f ⁻¹' t) := by
  refine ⟨?_, fun u v hu hv ⟨a, hat, hau⟩ ⟨b, hbt, hbv⟩ => ?_⟩
  · obtain ⟨y, hy⟩ := ht.nonempty
    obtain ⟨x, rfl⟩ := htr hy
    exact ⟨x, hy⟩
  obtain ⟨u', hu', rfl⟩ := hf.isOpen_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := hf.isOpen_iff.mp hv
  obtain ⟨y, hyt, hyu, hyv⟩ := ht.2 u' v' hu' hv' ⟨f a, hat, hau⟩ ⟨f b, hbt, hbv⟩
  obtain ⟨x, rfl⟩ := htr hyt
  exact ⟨x, hyt, hyu, hyv⟩

/-- The generic point of `S` is not on the floor. -/
private theorem genericPoint_notMem_range_floor (hι : ι.ker = B.roundDown.suppIdeal) :
    genericPoint S ∉ Set.range ι.base := by
  rw [range_floor hι]
  rintro ⟨Γ, -, hΓ⟩
  have h1 : Γ.genericPoint ⤳ genericPoint S := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hΓ
    exact specializes_iff_mem_closure.mpr hΓ
  have h2 : genericPoint S ⤳ Γ.genericPoint := (genericPoint_spec S).specializes trivial
  have heq : Γ.genericPoint = genericPoint S := (h1.antisymm h2).eq
  have := Γ.coheight_genericPoint
  rw [heq, Order.coheight_eq_zero.mpr fun b _ => (genericPoint_spec S).specializes trivial]
    at this
  exact zero_ne_one this

/-- The local rings of the floor have dimension at most one. -/
private theorem ringKrullDim_stalk_floor_le_one (hdim : topologicalKrullDim S = 2)
    (hι : ι.ker = B.roundDown.suppIdeal) (x : C) :
    ringKrullDim (C.presheaf.stalk x) ≤ 1 := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (show ι.base x ∈ (⊤ : S.Opens)
    from trivial)
  have hηV : genericPoint S ∈ V :=
    ((genericPoint_spec S).mem_open_set_iff V.isOpen).mpr ⟨_, trivial, hxV⟩
  -- a nonzero function on `V` vanishing on the floor
  have hker : RingHom.ker (ι.app V).hom ≠ ⊥ := by
    intro h
    apply genericPoint_notMem_range_floor hι
    have hsupp : genericPoint S ∈ ι.ker.support := by
      rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hηV,
        Scheme.Hom.ker_apply ι ⟨V, hV⟩]
      change genericPoint S ∈ S.zeroLocus (U := V) (RingHom.ker (ι.app V).hom : Set Γ(S, V))
      rw [h, Scheme.mem_zeroLocus_iff]
      intro f hf
      rw [Submodule.bot_coe, Set.mem_singleton_iff] at hf
      rw [hf, Scheme.basicOpen_zero]
      exact id
    have hsupp' : genericPoint S ∈ (ι.ker.support : Set S) := hsupp
    rwa [Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq] at hsupp'
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  set r := S.presheaf.germ V (ι.base x) hxV f
  have hr0 : r ≠ 0 := fun h => hf0 (germ_injective_of_isIntegral S (ι.base x) hxV
    (h.trans (map_zero _).symm))
  have hrk : r ∈ RingHom.ker (ι.stalkMap x).hom := by
    rw [RingHom.mem_ker, Scheme.Hom.germ_stalkMap_apply, RingHom.mem_ker.mp hf, map_zero]
  have hsurj := SurjectiveOnStalks.stalkMap_surjective ι x
  -- `dim 𝒪_{C,x} ≤ dim 𝒪_{S,x} / (r) ≤ dim 𝒪_{S,x} - 1 ≤ 1`
  have h1 : ringKrullDim (C.presheaf.stalk x) ≤
      ringKrullDim (S.presheaf.stalk (ι.base x) ⧸ Ideal.span {r}) := by
    refine ringKrullDim_le_of_surjective
      ((RingHom.quotientKerEquivOfSurjective hsurj).toRingHom.comp
        (Ideal.Quotient.factor (by rw [Ideal.span_le]; simpa using hrk))) ?_
    exact (RingHom.quotientKerEquivOfSurjective hsurj).surjective.comp
      (Ideal.Quotient.factor_surjective _)
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hr0)
  have h3 : ringKrullDim (S.presheaf.stalk (ι.base x)) ≤ 2 := by
    rw [ringKrullDim_stalk_eq_coheight, ← hdim,
      ← Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim]
    exact Order.coheight_le_krullDim _
  have h4 : ringKrullDim (S.presheaf.stalk (ι.base x) ⧸ Ideal.span {r}) + 1 ≤ 2 := h2.trans h3
  refine h1.trans ?_
  generalize ringKrullDim (S.presheaf.stalk (ι.base x) ⧸ Ideal.span {r}) = d at h4
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd h4 (by decide)
    | coe d =>
      have h5 : (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        push_cast; exact h4
      have h6 : d + 1 ≤ 2 := ENat.coe_le_coe.mp (WithBot.coe_le_coe.mp h5)
      have h7 : (((d : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((1 : ℕ) : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (ENat.coe_le_coe.mpr (by omega))
      simpa using h7

/-- A reduced Noetherian local ring of positive dimension has a nonzerodivisor in its maximal
ideal. -/
private theorem exists_mem_maximalIdeal_mem_nonZeroDivisors (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [IsReduced R]
    (hm : IsLocalRing.maximalIdeal R ∉ minimalPrimes R) :
    ∃ a ∈ IsLocalRing.maximalIdeal R, a ∈ nonZeroDivisors R := by
  classical
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  have hnot : ¬ ((IsLocalRing.maximalIdeal R : Set R) ⊆ ⋃ p ∈ minimalPrimes R, (id p : Set R)) := by
    intro h
    obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime_finite (f := id) hfin ⊥ ⊥
      (fun p hp _ _ => hp.1.1)).mp h
    have : p = IsLocalRing.maximalIdeal R :=
      le_antisymm (IsLocalRing.le_maximalIdeal hp.1.1.ne_top) hmp
    exact hm (this ▸ hp)
  obtain ⟨a, ham, ha⟩ := Set.not_subset.mp hnot
  have key : ∀ y : R, y * a = 0 → y = 0 := by
    intro y hy
    have hy : y ∈ (⊥ : Ideal R).radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro p hp
      have hpa : a ∉ p := fun h => ha (Set.mem_biUnion hp h)
      have : y * a ∈ p := by rw [hy]; exact p.zero_mem
      exact (hp.1.1.mem_or_mem this).resolve_right hpa
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hy
    exact IsReduced.eq_zero y ⟨n, (Ideal.mem_bot.mp hn)⟩
  exact ⟨a, ham, mem_nonZeroDivisors_iff.mpr
    ⟨fun y hy => key y (by rw [mul_comm]; exact hy), key⟩⟩

/-- The floor is a reduced separated curve of finite type. -/
private theorem roundDown_coeff_ne_zero_iff (hdlt : IsDltPair sS 2 K B) (Γ : Mori.PrimeDivisor S) :
    B.roundDown.coeff Γ ≠ 0 ↔ B.coeff Γ = 1 := by
  rw [DivisorWithCoeffs.coeff_roundDown]
  obtain ⟨h0, h1⟩ := hdlt.2.1 Γ
  constructor
  · intro h
    by_contra hne
    exact h (Int.floor_eq_zero_iff.mpr ⟨h0, lt_of_le_of_ne h1 hne⟩)
  · intro h; rw [h]; simp

/-- The irreducible components of the floor are the components of `⌊B⌋`. -/
private theorem exists_floor_eq_preimage (hdlt : IsDltPair sS 2 K B)
    (hι : ι.ker = B.roundDown.suppIdeal) {Z : Set C} (hZ : Z ∈ irreducibleComponents C) :
    ∃ Γ : Mori.PrimeDivisor S, B.coeff Γ = 1 ∧ Z = ι.base ⁻¹' (Γ.support : Set S) := by
  classical
  have hirr : IsIrreducible (ι.base '' Z) := hZ.1.image _ ι.base.hom.continuous.continuousOn
  let t : Finset (Set S) := B.roundDown.support.image fun Γ => (Γ.support : Set S)
  have hsub : ι.base '' Z ⊆ ⋃₀ (t : Set (Set S)) := by
    rintro _ ⟨z, -, rfl⟩
    have hz : ι.base z ∈ Set.range ι.base := ⟨z, rfl⟩
    rw [range_floor hι] at hz
    obtain ⟨Γ, hΓ, hzΓ⟩ := hz
    exact ⟨Γ.support, Finset.mem_coe.mpr
      (Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hΓ)), hzΓ⟩
  obtain ⟨_, hΓt, hZΓ⟩ := (isIrreducible_iff_sUnion_isClosed.mp hirr) t
    (fun z hz => by
      obtain ⟨Γ, -, rfl⟩ := Finset.mem_image.mp hz
      exact Γ.idealSheaf.support.isClosed) hsub
  obtain ⟨Γ, hΓ, rfl⟩ := Finset.mem_image.mp hΓt
  have hΓr : (Γ.support : Set S) ⊆ Set.range ι.base := by
    intro x hx
    rw [range_floor hι]
    exact ⟨Γ, Finsupp.mem_support_iff.mp hΓ, hx⟩
  have hpre : IsIrreducible (ι.base ⁻¹' (Γ.support : Set S)) :=
    isIrreducible_preimage_of_isInducing ι.isClosedEmbedding.isInducing
      (AlgebraicGeometry.PrimeDivisor.support_eq_closure Γ ▸ isIrreducible_singleton.closure) hΓr
  exact ⟨Γ, (roundDown_coeff_ne_zero_iff hdlt Γ).mp (Finsupp.mem_support_iff.mp hΓ),
    le_antisymm (fun z hz => hZΓ ⟨z, hz, rfl⟩) (hZ.2 hpre fun z hz => hZΓ ⟨z, hz, rfl⟩)⟩

/-- The components of `⌊B⌋` lie on the floor. -/
private theorem support_subset_range_floor (hdlt : IsDltPair sS 2 K B)
    (hι : ι.ker = B.roundDown.suppIdeal) {Γ : Mori.PrimeDivisor S} (hΓ : B.coeff Γ = 1) :
    (Γ.support : Set S) ⊆ Set.range ι.base := by
  intro x hx
  rw [range_floor hι]
  exact ⟨Γ, (roundDown_coeff_ne_zero_iff hdlt Γ).mpr hΓ, hx⟩

private theorem isNFold_floor (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hι : ι.ker = B.roundDown.suppIdeal) :
    IsNFold (ι ≫ sS) 1 := by
  haveI := hSp.toIsVariety
  have hdim : topologicalKrullDim S = 2 := hdlt.1.2.1.topologicalKrullDim_eq
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, ?_, fun Z hZ => ?_⟩
  · haveI : IsReduced ι.image := by
      change IsReduced ι.ker.subscheme
      rw [hι]
      exact (inferInstance : IsReduced
        (Scheme.IdealSheafData.vanishingIdeal B.roundDown.supp).subscheme)
    exact isReduced_of_isOpenImmersion ι.toImage
  obtain ⟨Γ, hΓ, rfl⟩ := exists_floor_eq_preimage hdlt hι hZ
  rw [topologicalKrullDim_image_of_isEmbedding ι.isClosedEmbedding.isEmbedding,
    Set.image_preimage_eq_of_subset (support_subset_range_floor hdlt hι hΓ),
    topologicalKrullDim_support (sS := sS) hdim Γ]
  rfl

/-- The floor satisfies Serre's condition `S₂` (it is a reduced curve). -/
private theorem satisfiesS2_floor (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hι : ι.ker = B.roundDown.suppIdeal) : SatisfiesS2 C := by
  haveI := hSp.toIsVariety
  have hdim : topologicalKrullDim S = 2 := hdlt.1.2.1.topologicalKrullDim_eq
  haveI : IsReduced C := (isNFold_floor hSp hdlt hι).2.1
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sS)
  intro x
  have hd := ringKrullDim_stalk_floor_le_one hdim hι x
  by_cases hm : IsLocalRing.maximalIdeal (C.presheaf.stalk x) ∈ minimalPrimes (C.presheaf.stalk x)
  · refine ⟨[], by simp, RingTheory.Sequence.IsRegular.nil _ _, ?_⟩
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, Ideal.height_eq_zero_iff.mpr hm]
    simp
  · obtain ⟨a, ham, ha⟩ := exists_mem_maximalIdeal_mem_nonZeroDivisors _ hm
    have hall : ∀ b ∈ [a], b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x) :=
      List.forall_mem_singleton.mpr ham
    refine ⟨[a], hall, ?_, ?_⟩
    · refine RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ hall ?_
      rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      refine isSMulRegular_iff_right_eq_zero_of_smul.mpr fun m hm' => ?_
      rw [smul_eq_mul] at hm'
      exact (mem_nonZeroDivisors_iff_left.mp ha) m hm'
    · exact min_le_of_right_le (hd.trans (by simp))

/-- The generic point of an integral scheme is a generic point of an irreducible component. -/
private theorem genericPoint_mem_genericPoints (X : Scheme.{0}) [IsIntegral X] :
    genericPoint X ∈ genericPoints X := by
  change closure {genericPoint X} ∈ irreducibleComponents X
  have hc : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  rw [hc, irreducibleComponents_eq_singleton]
  rfl

/-- The generic points of the floor lie over the generic points of the components of `⌊B⌋`. -/
private theorem exists_floor_of_mem_genericPoints (hdlt : IsDltPair sS 2 K B)
    (hι : ι.ker = B.roundDown.suppIdeal) {c : C} (hc : c ∈ genericPoints C) :
    ∃ Γ : Mori.PrimeDivisor S, B.coeff Γ = 1 ∧ ι.base c = Γ.genericPoint := by
  obtain ⟨Γ, hΓ, hZ⟩ := exists_floor_eq_preimage hdlt hι hc
  refine ⟨Γ, hΓ, ?_⟩
  have h1 : closure ({ι.base c} : Set S) = ι.base '' closure {c} := by
    rw [← Set.image_singleton]
    exact (ι.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous
      ι.base.hom.continuous _)
  rw [hZ, Set.image_preimage_eq_of_subset (support_subset_range_floor hdlt hι hΓ),
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  have g1 : IsGenericPoint (ι.base c) (closure {Γ.genericPoint}) := by
    rw [← h1]; exact isGenericPoint_closure
  exact g1.eq isGenericPoint_closure

/-- The only generic point of an integral scheme is its generic point. -/
private theorem eq_genericPoint_of_mem_genericPoints {X : Scheme.{0}} [IsIntegral X] {x : X}
    (hx : x ∈ genericPoints X) : x = genericPoint X := by
  have h : closure ({x} : Set X) ∈ irreducibleComponents X := hx
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h
  exact (show IsGenericPoint x Set.univ from h).eq (genericPoint_spec X)

/-- The closed immersion of a prime divisor sends the generic point to the generic point. -/
private theorem subschemeι_genericPoint (Γ : Mori.PrimeDivisor S) :
    haveI : IsIntegral Γ.idealSheaf.subscheme := Γ.integral
    Γ.idealSheaf.subschemeι.base (genericPoint Γ.idealSheaf.subscheme) = Γ.genericPoint := by
  haveI : IsIntegral Γ.idealSheaf.subscheme := Γ.integral
  have hr : Set.range Γ.idealSheaf.subschemeι.base = (Γ.support : Set S) :=
    Scheme.IdealSheafData.range_subschemeι _
  have h1 : closure ({Γ.idealSheaf.subschemeι.base (genericPoint Γ.idealSheaf.subscheme)} :
      Set S) = closure {Γ.genericPoint} := by
    have hc : closure ({genericPoint Γ.idealSheaf.subscheme} : Set Γ.idealSheaf.subscheme) =
        Set.univ := genericPoint_spec _
    rw [← Set.image_singleton, Γ.idealSheaf.subschemeι.isClosedEmbedding.isClosedMap
      |>.closure_image_eq_of_continuous Γ.idealSheaf.subschemeι.base.hom.continuous, hc,
      Set.image_univ, hr, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have g1 : IsGenericPoint (Γ.idealSheaf.subschemeι.base (genericPoint Γ.idealSheaf.subscheme))
      (closure {Γ.genericPoint}) := by rw [← h1]; exact isGenericPoint_closure
  exact g1.eq isGenericPoint_closure

/-- Two points of coheight one, one specializing to the other, are equal. -/
private theorem eq_of_specializes_of_coheight_eq_one {X : Scheme.{0}} {a b : X} (h : a ⤳ b)
    (ha : Order.coheight a = 1) (hb : Order.coheight b = 1) : a = b := by
  by_contra hne
  have hlt : b < a := lt_of_le_not_ge h fun h2 => hne (h.antisymm h2).eq
  have := Order.coheight_add_one_le hlt
  rw [ha, hb] at this
  exact absurd this (by decide)

/-- The prime divisor of `S` through a point of a component of `⌊B⌋` whose image is the generic
point of a prime divisor is that prime divisor. -/
private theorem eq_of_genericPoint_mem_support {Γ Γ' : Mori.PrimeDivisor S}
    (h : Γ.genericPoint ∈ (Γ'.support : Set S)) : Γ = Γ' := by
  refine (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_specializes_of_coheight_eq_one ?_ Γ'.coheight_genericPoint
      Γ.coheight_genericPoint)).symm
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  exact specializes_iff_mem_closure.mpr h

/-- An isomorphism of integral schemes sends the generic point to the generic point. -/
private theorem iso_hom_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (e : X ≅ Y) :
    e.hom.base (genericPoint X) = genericPoint Y :=
  eq_genericPoint_of_mem_genericPoints (mem_genericPoints_of_iso e
    (genericPoint_mem_genericPoints X))

/-- **Normality of the components of the floor** of a `ℚ`-factorial projective dlt surface. -/
private theorem isNormal_floor_component (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS) (Γ : Mori.PrimeDivisor S)
    (hΓ : B.coeff Γ = 1) : IsNormal Γ.idealSheaf.subscheme := by
  classical
  obtain ⟨B'', hB''e, hB''Γ, hplt, -, hlt⟩ := exists_isPltPair_sub_floor hdlt hQ hΓ
  set B₀ : QDivisor S := B'' - Finsupp.single Γ 1 with hB₀
  have hB₀c : ∀ E, B₀.coeff E = B''.coeff E - if E = Γ then 1 else 0 := fun E => by
    rw [hB₀, DivisorWithCoeffs.coeff_sub]
    by_cases h : E = Γ
    · subst h; rw [DivisorWithCoeffs.coeff_single_self, if_pos rfl]
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm h), if_neg h]
  have hB₀e : B₀.IsEffective := fun E => by
    rw [hB₀c]
    split_ifs with h
    · subst h; rw [hB''Γ]; norm_num
    · simpa using hB''e E
  have hB₀Γ : B₀.coeff Γ = 0 := by rw [hB₀c, if_pos rfl, hB''Γ, sub_self]
  have hB₀0 : B₀.roundDown = 0 := by
    ext E
    change B₀.roundDown.coeff E = 0
    rw [DivisorWithCoeffs.coeff_roundDown, Int.floor_eq_zero_iff]
    refine ⟨hB₀e E, ?_⟩
    by_cases h : E = Γ
    · subst h; rw [hB₀Γ]; norm_num
    · rw [hB₀c, if_neg h, sub_zero]; exact hlt E h
  have hsum : Finsupp.single Γ 1 + B₀ = B'' := by rw [hB₀]; abel
  exact IsPltPair.isNormal_subscheme_of_isQFactorial_of_charZero hQ hSp hB₀e hB₀0 hB₀Γ (hsum ▸ hplt)

/-- A point of a prime divisor of a surface other than its generic point is closed. -/
private theorem isClosed_singleton_of_mem_support (hdim : topologicalKrullDim S = 2)
    [LocallyOfFiniteType sS] (Γ : Mori.PrimeDivisor S) {x : S} (hx : x ∈ (Γ.support : Set S))
    (hxne : x ≠ Γ.genericPoint) : IsClosed ({x} : Set S) := by
  haveI : IsIntegral Γ.idealSheaf.subscheme := Γ.integral
  have hr : Set.range Γ.idealSheaf.subschemeι.base = (Γ.support : Set S) :=
    Scheme.IdealSheafData.range_subschemeι _
  obtain ⟨y, rfl⟩ := hr ▸ hx
  have hdim' : topologicalKrullDim S = ((1 : ℕ) : WithBot ℕ∞) + 1 := by rw [hdim]; rfl
  have hdimΓ := MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support sS hdim'
    Γ.idealSheaf.subschemeι Γ hr
  have hyne : y ≠ genericPoint Γ.idealSheaf.subscheme := by
    rintro rfl
    exact hxne (subschemeι_genericPoint Γ)
  have hyc := Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint
    Γ.idealSheaf.subscheme (by exact_mod_cast hdimΓ) hyne
  rw [← Set.image_singleton]
  exact Γ.idealSheaf.subschemeι.isClosedEmbedding.isClosedMap _ hyc

/-- **The floor meets itself only in the snc locus.** For a `ℚ`-factorial projective dlt surface
pair there is an open `U` in the smooth locus on which `B` is snc, containing every point where
two components of `⌊B⌋` meet: such a point is an lc centre, while every divisor over the
complement of the snc locus has discrepancy `> -1`. -/
private theorem exists_snc_open_floor_inter (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS) :
    ∃ U : S.Opens, U ≤ smoothLocus sS ∧ (B.restrictOpen U).IsSNC (U.ι ≫ sS) ∧
      ∀ Γ Γ' : Mori.PrimeDivisor S, B.coeff Γ = 1 → B.coeff Γ' = 1 → Γ ≠ Γ' →
        (Γ.support : Set S) ∩ Γ'.support ⊆ U := by
  haveI := hSp.toIsVariety
  have hdim : topologicalKrullDim S = 2 := hdlt.1.2.1.topologicalKrullDim_eq
  haveI : LocallyOfFiniteType sS := hdlt.1.1.1.toLocallyOfFiniteType
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  obtain ⟨hpair, hcoeff, U, hUsm, hUsnc, hZ⟩ := id hdlt
  refine ⟨U, hUsm, hUsnc, fun Γ Γ' hΓ hΓ' hne x ⟨hx, hx'⟩ => ?_⟩
  by_contra hxU
  have hxne : x ≠ Γ.genericPoint := fun h => hne (eq_of_genericPoint_mem_support (h ▸ hx'))
  have hxc : IsClosed ({x} : Set S) :=
    isClosed_singleton_of_mem_support (sS := sS) hdim Γ hx hxne
  have hB0 : ∀ P, 0 ≤ B.coeff P := fun P => (hcoeff P).1
  -- every divisor over `x` has its center `{x}` outside `U`
  have hdisc : ∀ (D : DivisorOver k sS) (a : ℚ), D.f D.E.genericPoint = x →
      IsDiscrepancy sS 2 K B D a → -1 < a := by
    intro D a hDx ha
    refine hZ D a ?_ ha
    rw [D.center_eq_closure_genericPoint, hDx, hxc.closure_eq, Set.singleton_subset_iff]
    exact hxU
  by_cases hxs : x ∈ smoothLocus sS
  · obtain ⟨D, hDx, a, ha, hDa⟩ := exists_isDiscrepancy_le_neg_one_of_mem_smoothLocus hpair hB0
      hΓ hΓ' hne hx hx' hxs hxc
    linarith [hdisc D a hDx hDa]
  · obtain ⟨V, hxV, hVsm⟩ := exists_nhds_forall_ne_mem_smoothLocus hpair.1 hdim
      ⟨Γ.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hpair.1 Γ⟩ x
    haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
    haveI : CompactSpace V := isCompact_iff_compactSpace.mp
      (@TopologicalSpace.NoetherianSpace.isCompact _ _
        (haveI : IsNoetherian S := {}; inferInstance) _)
    exact false_of_notMem_smoothLocus hpair hQ hB0 hΓ hΓ' hne hx hx' hxc hxs hxV hVsm
      (fun hf hE => hf.isSmoothScheme_of_isExceptionalCurveEnumeration hE)
      (fun hf => hf.exists_isExceptionalCurveEnumeration) fun D a _ hDx hDa => hdisc D a hDx hDa

/-- **Nodes of the floor.** Two components of the floor meet transversally at smooth points of
`S` through which no other component of `B` passes. -/
private theorem exists_regularParameters_of_mem_floor_inter
    (hSp : AlgebraicGeometry.IsProjectiveVariety k sS) (hdlt : IsDltPair sS 2 K B)
    (hQ : IsQFactorial sS) {Γ Γ' : Mori.PrimeDivisor S} (hΓ : B.coeff Γ = 1)
    (hΓ' : B.coeff Γ' = 1) (hne : Γ ≠ Γ') {x : S} (hx : x ∈ Γ.support) (hx' : x ∈ Γ'.support) :
    x ∈ smoothLocus sS ∧ ∃ z : Fin 2 → S.presheaf.stalk x, IsRegularSystemOfParameters z ∧
      AlgebraicGeometry.IdealSheafData.stalk Γ.idealSheaf x = Ideal.span {z 0} ∧
      AlgebraicGeometry.IdealSheafData.stalk Γ'.idealSheaf x = Ideal.span {z 1} ∧
      ∀ E ∈ B.support, x ∈ E.support → E = Γ ∨ E = Γ' := by
  classical
  haveI := hSp.toIsVariety
  have hdim : topologicalKrullDim S = 2 := hdlt.1.2.1.topologicalKrullDim_eq
  obtain ⟨U, hUsm, hUsnc, hinter⟩ := exists_snc_open_floor_inter hSp hdlt hQ
  have hxU : x ∈ U := hinter Γ Γ' hΓ hΓ' hne ⟨hx, hx'⟩
  refine ⟨hUsm hxU, ?_⟩
  -- `x` is a closed point, so `𝒪_{S,x}` has dimension two
  have hxne : x ≠ Γ.genericPoint := by
    rintro rfl
    exact hne (eq_of_genericPoint_mem_support hx')
  have hxc : IsClosed ({x} : Set S) := isClosed_singleton_of_mem_support (sS := sS) hdim Γ hx hxne
  have hd2 := MMP.Mori.SurfaceAux.ringKrullDim_stalk_eq_two (sY := sS) (this : MMP.Mori.IsVariety k sS) hdim x hxc
  -- the snc data at `x`
  let u : U.toScheme := ⟨x, hxU⟩
  obtain ⟨n, z, jj, ⟨hzspan, hzdim⟩, hj, hI⟩ :=
    (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι B u).mp (hUsnc.2 u)
  change Fin n → S.presheaf.stalk x at z
  have hn : n = 2 := by
    have h := hzdim.symm.trans hd2
    exact_mod_cast h
  subst hn
  have hmem : ∀ {E : Mori.PrimeDivisor S}, B.coeff E = 1 → x ∈ E.support →
      E ∈ B.support ∧ U.ι u ∈ E.support := by
    intro E hE hxE
    refine ⟨Finsupp.mem_support_iff.mpr ?_, hxE⟩
    change B.coeff E ≠ 0
    rw [hE]; exact one_ne_zero
  let a : {E : Mori.PrimeDivisor S // E ∈ B.support ∧ U.ι u ∈ E.support} := ⟨Γ, hmem hΓ hx⟩
  let b : {E : Mori.PrimeDivisor S // E ∈ B.support ∧ U.ι u ∈ E.support} := ⟨Γ', hmem hΓ' hx'⟩
  have hab : jj a ≠ jj b := fun h => hne (congrArg Subtype.val (hj h))
  let σ : Fin 2 → Fin 2 := ![jj a, jj b]
  have hσ : Function.Injective σ := by
    intro p q hpq
    fin_cases p <;> fin_cases q
    · rfl
    · exact absurd hpq hab
    · exact absurd hpq.symm hab
    · rfl
  have hσs : Function.Surjective σ := Finite.injective_iff_surjective.mp hσ
  refine ⟨z ∘ σ, ⟨?_, hzdim⟩, hI a, hI b, ?_⟩
  · rw [Set.range_comp, hσs.range_eq, Set.image_univ]
    exact hzspan
  · intro E hE hxE
    obtain ⟨p, hp⟩ := hσs (jj ⟨E, hE, hxE⟩)
    fin_cases p
    · left; exact congrArg Subtype.val (hj (hp.symm.trans rfl : jj ⟨E, hE, hxE⟩ = jj a))
    · right; exact congrArg Subtype.val (hj (hp.symm.trans rfl : jj ⟨E, hE, hxE⟩ = jj b))

/-- **The components of the normalization of the floor.** Each component `Cᵢ` of the
normalization of the floor is isomorphic over `S` to the reduced closed subscheme of a component
`Γ` of `⌊B⌋`: the components of `⌊B⌋` are normal, so the normalization lifts them. -/
private theorem exists_iso_component (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal)
    (hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite)
    (N : NormalizationComponents (ι ≫ sS) hC) (i : N.ι) :
    ∃ Γ : Mori.PrimeDivisor S, B.coeff Γ = 1 ∧ ∃ e : N.X i ≅ Γ.idealSheaf.subscheme,
      e.hom ≫ Γ.idealSheaf.subschemeι = N.n i ≫ ι := by
  classical
  obtain ⟨φ₀, hφ₀⟩ := N.exists_iso
  let φ : ∐ N.X ≅ C.normalizationScheme hC := φ₀
  have hφ : φ.hom ≫ C.normalization hC = Limits.Sigma.desc N.n := hφ₀
  have hιi : Limits.Sigma.ι N.X i ≫ φ.hom ≫ C.normalization hC = N.n i := by
    rw [hφ, Limits.Sigma.ι_desc]
  have hgenX : ∀ η : genericPoints (N.X i), (N.n i) η.1 ∈ genericPoints C := by
    intro η
    have h1 := mem_genericPoints_of_generalizingMap
      (Limits.Sigma.ι N.X i ≫ φ.hom).isOpenEmbedding.generalizingMap η.2
    rw [← hιi, Scheme.Hom.comp_apply]
    exact Scheme.normalization_mem_genericPoints _ hC h1
  have hc := hgenX ⟨_, genericPoint_mem_genericPoints (N.X i)⟩
  obtain ⟨Γ, hΓ, hcΓ⟩ := exists_floor_of_mem_genericPoints hdlt hι hc
  haveI : IsIntegral Γ.idealSheaf.subscheme := Γ.integral
  haveI : IsNormal Γ.idealSheaf.subscheme := isNormal_floor_component hSp hdlt hQ Γ hΓ
  have hΓv : Γ.idealSheaf = Scheme.IdealSheafData.vanishingIdeal Γ.idealSheaf.support :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl
  -- `h : Cᵢ ⟶ Γ`
  have hrange : Set.range (N.n i ≫ ι).base ⊆ (Γ.support : Set S) := by
    rintro _ ⟨y, rfl⟩
    have hsp := ((genericPoint_spec (N.X i)).specializes (Set.mem_univ y)).map
      (N.n i ≫ ι).base.hom.continuous
    have h0 : (N.n i ≫ ι).base (genericPoint (N.X i)) = Γ.genericPoint := hcΓ
    rw [h0] at hsp
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
    exact hsp
  have H : Γ.idealSheaf.subschemeι.ker ≤ (N.n i ≫ ι).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, (N.n i ≫ ι).ker_eq_vanishingIdeal_closure_range,
      hΓv]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono
      (TopologicalSpace.Closeds.closure_le.mpr hrange)
  let h := IsClosedImmersion.lift Γ.idealSheaf.subschemeι (N.n i ≫ ι) H
  have hh : h ≫ Γ.idealSheaf.subschemeι = N.n i ≫ ι := IsClosedImmersion.lift_fac _ _ _
  -- `g : Γ ⟶ C`
  have Hg : ι.ker ≤ Γ.idealSheaf.subschemeι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hι, hΓv]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono fun x hx => ?_
    have : x ∈ Set.range ι.base := support_subset_range_floor hdlt hι hΓ hx
    rw [range_floor hι] at this
    obtain ⟨E, hE, hxE⟩ := this
    exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hE, hxE⟩
  let g := IsClosedImmersion.lift ι Γ.idealSheaf.subschemeι Hg
  have hg : g ≫ ι = Γ.idealSheaf.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have hgen_g : ∀ η : genericPoints Γ.idealSheaf.subscheme, g η.1 ∈ genericPoints C := by
    rintro ⟨η, hη⟩
    obtain rfl := eq_genericPoint_of_mem_genericPoints hη
    have : g (genericPoint Γ.idealSheaf.subscheme) = N.n i (genericPoint (N.X i)) := by
      apply ι.isClosedEmbedding.injective
      change (g ≫ ι).base _ = _
      rw [hg, subschemeι_genericPoint]
      exact hcΓ.symm
    rwa [this]
  -- the two lifts to the normalization
  obtain ⟨ĝ, hĝ, -⟩ := Scheme.existsUnique_lift_normalization hC g hgen_g
  obtain ⟨_, -, huniq⟩ := Scheme.existsUnique_lift_normalization hC (N.n i) hgenX
  have hhg : h ≫ g = N.n i := by
    rw [← cancel_mono ι, Category.assoc, hg, hh]
  have hhĝ : h ≫ ĝ = Limits.Sigma.ι N.X i ≫ φ.hom := by
    rw [huniq (h ≫ ĝ) (by beta_reduce; rw [Category.assoc, hĝ, hhg]),
      huniq (Limits.Sigma.ι N.X i ≫ φ.hom) (by beta_reduce; rw [Category.assoc]; exact hιi)]
  let g₀ := ĝ ≫ φ.inv
  have hhg₀ : h ≫ g₀ = Limits.Sigma.ι N.X i := by
    simp only [g₀]
    rw [← Category.assoc, hhĝ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hrange₀ : Set.range g₀ ⊆ Set.range (Limits.Sigma.ι N.X i) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨⟨i', y⟩, hy⟩ := (sigmaMk N.X).surjective (g₀ a)
    rw [sigmaMk_mk] at hy
    by_cases hi : i' = i
    · subst hi
      exact ⟨y, hy⟩
    · exfalso
      obtain ⟨x⟩ : Nonempty (N.X i) := inferInstance
      have hU : IsOpen (g₀ ⁻¹' Set.range (Limits.Sigma.ι N.X i)) :=
        (Limits.Sigma.ι N.X i).isOpenEmbedding.isOpen_range.preimage g₀.continuous
      have hV : IsOpen (g₀ ⁻¹' Set.range (Limits.Sigma.ι N.X i')) :=
        (Limits.Sigma.ι N.X i').isOpenEmbedding.isOpen_range.preimage g₀.continuous
      have hx : g₀ (h x) = Limits.Sigma.ι N.X i x := by
        rw [← Scheme.Hom.comp_apply, hhg₀]
      obtain ⟨b, -, ⟨u, hu⟩, ⟨v, hv⟩⟩ :=
        (IrreducibleSpace.isIrreducible_univ Γ.idealSheaf.subscheme).2 _ _ hU hV
          ⟨h x, trivial, ⟨x, hx.symm⟩⟩ ⟨a, trivial, ⟨y, hy⟩⟩
      have := (sigmaι_eq_iff N.X i i' u v).mp (hu.trans hv.symm)
      exact hi (congrArg Sigma.fst this).symm
  let g' := IsOpenImmersion.lift (Limits.Sigma.ι N.X i) g₀ hrange₀
  have hg' : g' ≫ Limits.Sigma.ι N.X i = g₀ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Γ, hΓ, ⟨h, g', ?_, ?_⟩, hh⟩
  · rw [← cancel_mono (Limits.Sigma.ι N.X i), Category.assoc, hg', hhg₀, Category.id_comp]
  · rw [← cancel_mono Γ.idealSheaf.subschemeι, Category.assoc, hh, Category.id_comp, ← hιi]
    simp only [Category.assoc]
    rw [reassoc_of% hg']
    simp only [g₀, Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% hĝ, hg]

/-- The components of the normalization map generic points to generic points. -/
private theorem normalizationComponent_mem_genericPoints
    {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
    (N : NormalizationComponents (ι ≫ sS) hC) (i : N.ι) (η : genericPoints (N.X i)) :
    (N.n i) η.1 ∈ genericPoints C := by
  obtain ⟨φ₀, hφ₀⟩ := N.exists_iso
  let φ : ∐ N.X ≅ C.normalizationScheme hC := φ₀
  have hφ : φ.hom ≫ C.normalization hC = Limits.Sigma.desc N.n := hφ₀
  have hιi : Limits.Sigma.ι N.X i ≫ φ.hom ≫ C.normalization hC = N.n i := by
    rw [hφ, Limits.Sigma.ι_desc]
  have h1 := mem_genericPoints_of_generalizingMap
    (Limits.Sigma.ι N.X i ≫ φ.hom).isOpenEmbedding.generalizingMap η.2
  rw [← hιi, Scheme.Hom.comp_apply]
  exact Scheme.normalization_mem_genericPoints _ hC h1

/-- The generic point of a component of the normalization lies over the generic point of a
component of `⌊B⌋`. -/
private theorem exists_genericPoint_component (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal)
    {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
    (N : NormalizationComponents (ι ≫ sS) hC) (i : N.ι) :
    ∃ Γ : Mori.PrimeDivisor S, B.coeff Γ = 1 ∧
      (N.n i ≫ ι).base (genericPoint (N.X i)) = Γ.genericPoint ∧
      ∃ e : N.X i ≅ Γ.idealSheaf.subscheme, e.hom ≫ Γ.idealSheaf.subschemeι = N.n i ≫ ι := by
  obtain ⟨Γ, hΓ, e, he⟩ := exists_iso_component hSp hdlt hQ hι hC N i
  haveI : IsIntegral Γ.idealSheaf.subscheme := Γ.integral
  refine ⟨Γ, hΓ, ?_, e, he⟩
  rw [← he, Scheme.Hom.comp_apply, iso_hom_genericPoint e, subschemeι_genericPoint]

/-- Different components of the normalization lie over different components of `⌊B⌋`. -/
private theorem injective_component (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal)
    {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
    (N : NormalizationComponents (ι ≫ sS) hC) :
    Function.Injective fun i => (N.n i ≫ ι).base (genericPoint (N.X i)) := by
  intro i j hij
  simp only at hij
  obtain ⟨Γ, hΓ, hgi, e, he⟩ := exists_genericPoint_component hSp hdlt hQ hι N i
  obtain ⟨Γ', hΓ', hgj, e', he'⟩ := exists_genericPoint_component hSp hdlt hQ hι N j
  obtain rfl : Γ = Γ' :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hgi.symm.trans (hij.trans hgj))
  haveI : IsIntegral Γ.idealSheaf.subscheme := Γ.integral
  haveI : IsNormal Γ.idealSheaf.subscheme := isNormal_floor_component hSp hdlt hQ Γ hΓ
  obtain ⟨φ₀, hφ₀⟩ := N.exists_iso
  let φ : ∐ N.X ≅ C.normalizationScheme hC := φ₀
  have hφ : φ.hom ≫ C.normalization hC = Limits.Sigma.desc N.n := hφ₀
  have hιi : ∀ l, Limits.Sigma.ι N.X l ≫ φ.hom ≫ C.normalization hC = N.n l := fun l => by
    rw [hφ, Limits.Sigma.ι_desc]
  let g := e.inv ≫ N.n i
  have hgj' : e'.inv ≫ N.n j = g := by
    rw [← cancel_mono ι, Category.assoc, Category.assoc, ← he, ← he']
    simp
  have hgen : ∀ η : genericPoints Γ.idealSheaf.subscheme, g η.1 ∈ genericPoints C := by
    rintro ⟨η, hη⟩
    obtain rfl := eq_genericPoint_of_mem_genericPoints hη
    change (N.n i) (e.symm.hom.base (genericPoint _)) ∈ _
    rw [iso_hom_genericPoint e.symm]
    exact normalizationComponent_mem_genericPoints N i ⟨_, genericPoint_mem_genericPoints _⟩
  obtain ⟨_, -, huniq⟩ := Scheme.existsUnique_lift_normalization hC g hgen
  have h1 := huniq (e.inv ≫ Limits.Sigma.ι N.X i ≫ φ.hom) (by
    beta_reduce; simp only [Category.assoc]; rw [hιi])
  have h2 := huniq (e'.inv ≫ Limits.Sigma.ι N.X j ≫ φ.hom) (by
    beta_reduce; simp only [Category.assoc]; rw [hιi, hgj'])
  have h3 := congrArg (fun f => (f ≫ φ.inv).base (genericPoint Γ.idealSheaf.subscheme))
    (h1.trans h2.symm)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Scheme.Hom.comp_apply] at h3
  exact congrArg Sigma.fst ((sigmaι_eq_iff N.X i j _ _).mp h3)

/-- Every component of `⌊B⌋` is the image of a component of the normalization. -/
private theorem exists_index_component (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal)
    {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
    (N : NormalizationComponents (ι ≫ sS) hC) (Γ : Mori.PrimeDivisor S) (hΓ : B.coeff Γ = 1) :
    ∃ i, (N.n i ≫ ι).base (genericPoint (N.X i)) = Γ.genericPoint := by
  obtain ⟨c, hc⟩ : Γ.genericPoint ∈ Set.range ι.base := support_subset_range_floor hdlt hι hΓ
    (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  obtain ⟨φ₀, hφ₀⟩ := N.exists_iso
  let φ : ∐ N.X ≅ C.normalizationScheme hC := φ₀
  have hφ : φ.hom ≫ C.normalization hC = Limits.Sigma.desc N.n := hφ₀
  obtain ⟨z, hz⟩ := (Scheme.surjective_normalization C hC).surj c
  obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk N.X).surjective (φ.inv.base z)
  rw [sigmaMk_mk] at hy
  have hny : (N.n i) y = c := by
    have hφz : φ.hom.base (φ.inv.base z) = z := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    rw [← hz, ← Limits.Sigma.ι_desc (f := N.X) N.n i, ← hφ, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply, hy, hφz]
  obtain ⟨Γ', -, hgi, e, he⟩ := exists_genericPoint_component hSp hdlt hQ hι N i
  refine ⟨i, hgi.trans ?_⟩
  have hmem : Γ.genericPoint ∈ (Γ'.support : Set S) := by
    have hr : Set.range Γ'.idealSheaf.subschemeι.base = (Γ'.support : Set S) :=
      Scheme.IdealSheafData.range_subschemeι _
    rw [← hc, ← hny, ← hr]
    exact ⟨e.hom.base y, by rw [← Scheme.Hom.comp_apply, he]; rfl⟩
  rw [eq_of_genericPoint_mem_support hmem]

/-- The components of the normalization map to `S` by closed immersions. -/
private theorem isFloorNormalization_closedImmersion
    (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal)
    {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
    (N : NormalizationComponents (ι ≫ sS) hC) (i : N.ι) : IsClosedImmersion (N.n i ≫ ι) := by
  obtain ⟨Γ, -, -, e, he⟩ := exists_genericPoint_component hSp hdlt hQ hι N i
  rw [← he]
  infer_instance

/-- The image of a component of the normalization is the corresponding component of `⌊B⌋`. -/
private theorem range_component (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal)
    {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
    (N : NormalizationComponents (ι ≫ sS) hC) (i : N.ι) :
    ∃ Γ : Mori.PrimeDivisor S, B.coeff Γ = 1 ∧
      (N.n i ≫ ι).base (genericPoint (N.X i)) = Γ.genericPoint ∧
      Set.range (N.n i ≫ ι).base = (Γ.support : Set S) := by
  obtain ⟨Γ, hΓ, hg, e, he⟩ := exists_genericPoint_component hSp hdlt hQ hι N i
  refine ⟨Γ, hΓ, hg, ?_⟩
  rw [← he, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (ConcreteCategory.bijective_of_isIso e.hom.base).2.range_eq, Set.image_univ]
  exact Scheme.IdealSheafData.range_subschemeι _

/-- **Nodes of the floor are double normal crossing points**: over a point where two components
of `⌊B⌋` meet, the completed local ring of the floor is `k[[x₀, x₁]]/(x₀x₁)`. -/
private theorem isDoubleNormalCrossingPoint_of_mem_inter
    (hSp : AlgebraicGeometry.IsProjectiveVariety k sS) (hdlt : IsDltPair sS 2 K B)
    (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal) {Γ Γ' : Mori.PrimeDivisor S}
    (hΓ : B.coeff Γ = 1) (hΓ' : B.coeff Γ' = 1) (hne : Γ ≠ Γ') {c : C}
    (hc : ι.base c ∈ (Γ.support : Set S)) (hc' : ι.base c ∈ (Γ'.support : Set S)) :
    IsDoubleNormalCrossingPoint (ι ≫ sS) 1 c := by
  classical
  haveI := hSp.toIsVariety
  have hdim : topologicalKrullDim S = 2 := hdlt.1.2.1.topologicalKrullDim_eq
  set x := ι.base c with hxdef
  obtain ⟨-, z, hz, hz0, hz1, hE⟩ :=
    exists_regularParameters_of_mem_floor_inter hSp hdlt hQ hΓ hΓ' hne hc hc'
  -- `x` and `c` are closed points
  have hxne : x ≠ Γ.genericPoint := fun h => hne (eq_of_genericPoint_mem_support (h ▸ hc'))
  have hxc : IsClosed ({x} : Set S) := isClosed_singleton_of_mem_support (sS := sS) hdim Γ hc hxne
  have hcc : IsClosed ({c} : Set C) := by
    have : ({c} : Set C) = ι.base ⁻¹' {x} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ rfl, fun h => ι.isClosedEmbedding.injective h⟩
    rw [this]
    exact hxc.preimage ι.base.hom.continuous
  refine ⟨isNFold_floor hSp hdlt hι, hcc, ?_⟩
  -- the stalk of `⌊B⌋` at `x` is `(z₀z₁)`
  have hfilt : (B.roundDown.support.filter fun E => x ∈ E.support) = {Γ, Γ'} := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hEs, hxE⟩
      have hE1 := (roundDown_coeff_ne_zero_iff hdlt E).mp (Finsupp.mem_support_iff.mp hEs)
      refine hE E (Finsupp.mem_support_iff.mpr ?_) hxE
      change B.coeff E ≠ 0
      rw [hE1]; exact one_ne_zero
    · rintro (rfl | rfl)
      · exact ⟨Finsupp.mem_support_iff.mpr ((roundDown_coeff_ne_zero_iff hdlt _).mpr hΓ), hc⟩
      · exact ⟨Finsupp.mem_support_iff.mpr ((roundDown_coeff_ne_zero_iff hdlt _).mpr hΓ'), hc'⟩
  have hprime : Prime (z 1) := by
    obtain ⟨q, -, hq, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support Γ' hc'
    have hz1ne : z 1 ≠ 0 := fun h0 => notMem_span_singleton_of_isRegularSystemOfParameters hz
      (i := 1) (j := 0) (by decide) (h0 ▸ zero_mem _)
    rw [← Ideal.span_singleton_prime hz1ne, ← hz1, hq]
    exact q.isPrime
  have hker : RingHom.ker (ι.stalkMap c).hom = Ideal.span {z 0 * z 1} := by
    rw [← AlgebraicGeometry.IdealSheafData.stalk_ker_of_isClosedImmersion, hι,
      MMP.Intersection.stalk_suppIdeal, hfilt, Finset.inf_insert, Finset.inf_singleton, hz0, hz1]
    exact span_singleton_inf_span_singleton_of_prime hprime
      (notMem_span_singleton_of_isRegularSystemOfParameters hz (by decide))
  -- residue field `k`
  letI := stalkAlgebra sS x
  haveI := MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sS x hxc
  have hres : ∀ r : S.presheaf.stalk x, ∃ a : k,
      r - algebraMap k _ a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk x) := by
    intro r
    obtain ⟨a, ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
      (K := IsLocalRing.ResidueField (S.presheaf.stalk x))).2 (IsLocalRing.residue _ r)
    refine ⟨a, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← ha]
    exact sub_eq_zero.mpr rfl
  obtain ⟨e, he⟩ := exists_ringEquiv_adicCompletion_of_ker_eq k (S.presheaf.stalk x)
    (C.presheaf.stalk c) hres hz (ι.stalkMap c).hom (ι.stalkMap_surjective c) hker
  letI := (stalkStructureMap (ι ≫ sS) c).toAlgebra
  refine ⟨AlgEquiv.ofRingEquiv (f := e) fun a => ?_⟩
  have h1 : algebraMap k (CompletedLocalRing C c) a =
      algebraMap (C.presheaf.stalk c) _ ((ι.stalkMap c).hom (algebraMap k _ a)) := by
    rw [IsScalarTower.algebraMap_apply k (C.presheaf.stalk c), RingHom.algebraMap_toAlgebra]
    congr 1
    exact (MMP.Flips.stalkMap_stalkStructureMap ι c a).symm
  rw [h1, he]
  rfl

/-- **Points on one component are smooth points of the floor.** -/
private theorem mem_smoothLocus_of_forall_eq (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal)
    {Γ : Mori.PrimeDivisor S} (hΓ : B.coeff Γ = 1) {c : C} (hc : ι.base c ∈ (Γ.support : Set S))
    (huniq : ∀ Γ' : Mori.PrimeDivisor S, B.coeff Γ' = 1 → ι.base c ∈ (Γ'.support : Set S) →
      Γ' = Γ) : c ∈ smoothLocus (ι ≫ sS) := by
  classical
  haveI := hSp.toIsVariety
  have hdim : topologicalKrullDim S = 2 := hdlt.1.2.1.topologicalKrullDim_eq
  haveI : IsIntegral Γ.idealSheaf.subscheme := Γ.integral
  haveI : IsNormal Γ.idealSheaf.subscheme := isNormal_floor_component hSp hdlt hQ Γ hΓ
  haveI : IsReduced C := (isNFold_floor hSp hdlt hι).2.1
  set jΓ := Γ.idealSheaf.subschemeι
  have hjr : Set.range jΓ.base = (Γ.support : Set S) := Scheme.IdealSheafData.range_subschemeι _
  -- the open set `V` avoiding the other components of `⌊B⌋`
  let Z : Set S := ⋃ E ∈ B.roundDown.support.filter (· ≠ Γ), (E.support : Set S)
  have hZ : IsClosed Z := isClosed_biUnion_finset fun E _ => E.idealSheaf.support.isClosed
  let V : S.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have hcV : ι.base c ∈ V := by
    intro hcZ
    simp only [Z, Set.mem_iUnion, Finset.mem_filter] at hcZ
    obtain ⟨E, ⟨hE, hEΓ⟩, hcE⟩ := hcZ
    exact hEΓ (huniq E ((roundDown_coeff_ne_zero_iff hdlt E).mp (Finsupp.mem_support_iff.mp hE))
      hcE)
  -- on `V`, the floor and `Γ` are the same reduced closed subscheme
  have hrange : ∀ v : V, (v : S) ∈ Set.range ι.base ↔ (v : S) ∈ Set.range jΓ.base := by
    intro v
    rw [hjr, range_floor hι]
    constructor
    · rintro ⟨E, hE, hvE⟩
      by_contra hvΓ
      have hEΓ : E ≠ Γ := fun h => hvΓ (h ▸ hvE)
      exact v.2 (Set.mem_biUnion (x := E) (Finset.mem_filter.mpr
        ⟨Finsupp.mem_support_iff.mpr hE, hEΓ⟩) hvE)
    · intro hvΓ
      exact ⟨Γ, (roundDown_coeff_ne_zero_iff hdlt Γ).mpr hΓ, hvΓ⟩
  have hmr : ∀ {T : Scheme.{0}} (f : T ⟶ S) (v : V),
      v ∈ Set.range (f ∣_ V).base ↔ (v : S) ∈ Set.range f.base := by
    intro T f v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, (morphismRestrict_base_coe f V x).symm⟩
    · rintro ⟨x, hx⟩
      have hxV : x ∈ f ⁻¹ᵁ V := by
        change f.base x ∈ V; rw [hx]; exact v.2
      exact ⟨⟨x, hxV⟩, Subtype.ext ((morphismRestrict_base_coe f V _).trans hx)⟩
  have hrV : Set.range (ι ∣_ V).base = Set.range (jΓ ∣_ V).base := by
    ext v
    exact (hmr ι v).trans ((hrange v).trans (hmr jΓ v).symm)
  have hker : (ι ∣_ V).ker = (jΓ ∣_ V).ker := by
    rw [(ι ∣_ V).ker_eq_vanishingIdeal_closure_range, (jΓ ∣_ V).ker_eq_vanishingIdeal_closure_range,
      hrV]
  let f := IsClosedImmersion.lift (jΓ ∣_ V) (ι ∣_ V) hker.symm.le
  have hf : f ≫ (jΓ ∣_ V) = ι ∣_ V := IsClosedImmersion.lift_fac _ _ _
  haveI : IsIso f := IsClosedImmersion.isIso_of_ker_eq (ι ∣_ V) (jΓ ∣_ V) f hf hker
  -- `Γ` is a smooth curve
  haveI : LocallyOfFiniteType (jΓ ≫ sS) := inferInstance
  haveI : IsLocallyNoetherian Γ.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (jΓ ≫ sS)
  have hdim' : topologicalKrullDim S = ((1 : ℕ) : WithBot ℕ∞) + 1 := by rw [hdim]; rfl
  have hdimΓ := MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support sS hdim' jΓ Γ hjr
  haveI : Smooth (jΓ ≫ sS) := smooth_of_isRegular_over_perfectField (jΓ ≫ sS)
    (isRegular_of_isNormal_of_topologicalKrullDim_le_one _ (by rw [hdimΓ]; rfl))
  have hcomp : (ι ⁻¹ᵁ V).ι ≫ ι ≫ sS = f ≫ (jΓ ⁻¹ᵁ V).ι ≫ jΓ ≫ sS := by
    rw [← Category.assoc, ← morphismRestrict_ι, ← hf, Category.assoc, Category.assoc,
      morphismRestrict_ι_assoc]
  have hsm : Smooth ((ι ⁻¹ᵁ V).ι ≫ ι ≫ sS) := by
    rw [hcomp]; infer_instance
  exact le_sSup (show (ι ⁻¹ᵁ V) ∈ {U : C.Opens | Smooth (U.ι ≫ ι ≫ sS)} from hsm) hcV

/-- **Double points of the floor.** Two different components of the normalization meet only over
double normal crossing points of the floor. -/
private theorem isDoubleNormalCrossingPoint_of_ne (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal)
    {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
    (N : NormalizationComponents (ι ≫ sS) hC) (i j : N.ι) (y : N.X i) (y' : N.X j)
    (hyy : (N.n i ≫ ι).base y = (N.n j ≫ ι).base y') (hij : i ≠ j) :
    IsDoubleNormalCrossingPoint (ι ≫ sS) 1 ((N.n i).base y) := by
  obtain ⟨Γ, hΓ, hgi, hri⟩ := range_component hSp hdlt hQ hι N i
  obtain ⟨Γ', hΓ', hgj, hrj⟩ := range_component hSp hdlt hQ hι N j
  have hne : Γ ≠ Γ' := fun h => hij (injective_component hSp hdlt hQ hι N
    (by simp only; rw [hgi, hgj, h]))
  exact isDoubleNormalCrossingPoint_of_mem_inter hSp hdlt hQ hι hΓ hΓ' hne
    (hri ▸ ⟨y, rfl⟩) (hrj ▸ ⟨y', hyy.symm⟩)

/-- The kernel of the stalk map of a component of the normalization is the stalk of the ideal of
the corresponding component of `⌊B⌋`. -/
private theorem ker_stalkMap_component (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal)
    {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
    (N : NormalizationComponents (ι ≫ sS) hC) (i : N.ι) {Γ : Mori.PrimeDivisor S}
    (hr : Set.range (N.n i ≫ ι).base = (Γ.support : Set S)) (y : N.X i) :
    haveI : IsClosedImmersion (N.n i ≫ ι) := (isFloorNormalization_closedImmersion hSp hdlt hQ hι N i)
    RingHom.ker ((N.n i ≫ ι).stalkMap y).hom =
      AlgebraicGeometry.IdealSheafData.stalk Γ.idealSheaf ((N.n i ≫ ι).base y) := by
  haveI : IsClosedImmersion (N.n i ≫ ι) := isFloorNormalization_closedImmersion hSp hdlt hQ hι N i
  haveI : IsIntegral Γ.idealSheaf.subscheme := Γ.integral
  have hker : (N.n i ≫ ι).ker = Γ.idealSheaf := by
    rw [(N.n i ≫ ι).ker_eq_vanishingIdeal_closure_range,
      Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme Γ.idealSheaf _ rfl]
    congr 1
    ext x
    change x ∈ closure (Set.range (N.n i ≫ ι).base) ↔ x ∈ (Γ.support : Set S)
    rw [(N.n i ≫ ι).isClosedEmbedding.isClosed_range.closure_eq, hr]
  rw [← AlgebraicGeometry.IdealSheafData.stalk_ker_of_isClosedImmersion, hker]

/-- **Values lift along closed immersions.** If the image `t` at `P` of a germ `u` at `j(P)` has
value `a` (that is, `t - a` vanishes at `P`), then `u - a` lies in the maximal ideal. -/
private theorem sub_mem_maximalIdeal_of_vanishes [LocallyOfFiniteType sS] {T : Scheme.{0}}
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] (j : T ⟶ S) (P : Mori.PrimeDivisor T)
    (u : S.presheaf.stalk (j.base P.genericPoint)) (a : k)
    (hv : letI := functionFieldAlgebra (j ≫ sS)
      algebraMap _ T.functionField ((j.stalkMap P.genericPoint).hom u) - algebraMap k _ a = 0 ∨
        1 ≤ T.ord (algebraMap _ T.functionField ((j.stalkMap P.genericPoint).hom u) -
          algebraMap k _ a) P.genericPoint) :
    letI := stalkAlgebra sS (j.base P.genericPoint)
    u - algebraMap k _ a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk (j.base P.genericPoint)) := by
  letI := stalkAlgebra sS (j.base P.genericPoint)
  letI := functionFieldAlgebra (j ≫ sS)
  letI := stalkAlgebra (j ≫ sS) P.genericPoint
  haveI := isScalarTower_stalk_functionField (j ≫ sS) P.genericPoint
  have := P.isDiscreteValuationRing_localRing
  have hcoh := P.coheight_genericPoint
  have hw : algebraMap _ T.functionField ((j.stalkMap P.genericPoint).hom u) - algebraMap k _ a =
      algebraMap (T.presheaf.stalk P.genericPoint) T.functionField
        ((j.stalkMap P.genericPoint).hom (u - algebraMap k _ a)) := by
    rw [map_sub, stalkMap_stalkAlgebra j P.genericPoint a, map_sub,
      ← IsScalarTower.algebraMap_apply]
  rw [hw] at hv
  by_contra hm
  have hu := (IsLocalRing.notMem_maximalIdeal.mp hm).map (j.stalkMap P.genericPoint).hom
  rcases hv with h0 | h1
  · exact hu.ne_zero (IsFractionRing.injective _ _ (h0.trans (map_zero _).symm))
  · rw [ord_algebraMap_eq_zero_of_isUnit hcoh hu] at h1
    omega

/-- **Functions at a node.** Over a node, functions on the two branches with the same value lift
to a function near the node. -/
private theorem nodeLift_of_ne (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal)
    {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
    (N : NormalizationComponents (ι ≫ sS) hC) (i j : N.ι) (P : Mori.PrimeDivisor (N.X i))
    (P' : Mori.PrimeDivisor (N.X j))
    (hPP' : (N.n i ≫ ι).base P.genericPoint = (N.n j ≫ ι).base P'.genericPoint) (hij : i ≠ j)
    (g : (N.X i).functionField) (g' : (N.X j).functionField) (a : k)
    (hg : g ∈ Set.range (algebraMap ((N.X i).presheaf.stalk P.genericPoint) (N.X i).functionField))
    (hg' : g' ∈ Set.range (algebraMap ((N.X j).presheaf.stalk P'.genericPoint)
      (N.X j).functionField))
    (hv : letI := functionFieldAlgebra (N.n i ≫ ι ≫ sS);
      g - algebraMap k _ a = 0 ∨ 1 ≤ (N.X i).ord (g - algebraMap k _ a) P.genericPoint)
    (hv' : letI := functionFieldAlgebra (N.n j ≫ ι ≫ sS);
      g' - algebraMap k _ a = 0 ∨ 1 ≤ (N.X j).ord (g' - algebraMap k _ a) P'.genericPoint) :
    ∃ (W : S.Opens) (hW : (N.n i ≫ ι).base P.genericPoint ∈ W) (h : Γ(S, W)),
      haveI : Nonempty ((N.n i ≫ ι) ⁻¹ᵁ W) := ⟨⟨P.genericPoint, hW⟩⟩
      haveI : Nonempty ((N.n j ≫ ι) ⁻¹ᵁ W) :=
        ⟨⟨P'.genericPoint, show (N.n j ≫ ι).base P'.genericPoint ∈ W from hPP' ▸ hW⟩⟩
      (N.X i).germToFunctionField _ ((N.n i ≫ ι).app W h) = g ∧
        (N.X j).germToFunctionField _ ((N.n j ≫ ι).app W h) = g' := by
  classical
  haveI := hSp.toIsVariety
  haveI := isFloorNormalization_closedImmersion hSp hdlt hQ hι N i
  haveI := isFloorNormalization_closedImmersion hSp hdlt hQ hι N j
  set x := (N.n i ≫ ι).base P.genericPoint with hxdef
  obtain ⟨Γ, hΓ, hgi, hri⟩ := range_component hSp hdlt hQ hι N i
  obtain ⟨Γ', hΓ', hgj, hrj⟩ := range_component hSp hdlt hQ hι N j
  have hΓΓ' : Γ ≠ Γ' := fun h => hij (injective_component hSp hdlt hQ hι N
    (by simp only; rw [hgi, hgj, h]))
  have hxΓ : (N.n i ≫ ι).base P.genericPoint ∈ (Γ.support : Set S) := hri ▸ ⟨_, rfl⟩
  have hxΓ' : (N.n i ≫ ι).base P.genericPoint ∈ (Γ'.support : Set S) :=
    hrj ▸ ⟨P'.genericPoint, hPP'.symm⟩
  obtain ⟨-, z, ⟨hzspan, -⟩, hI, hI', -⟩ :=
    exists_regularParameters_of_mem_floor_inter hSp hdlt hQ hΓ hΓ' hΓΓ' hxΓ hxΓ'
  have hk := ker_stalkMap_component hSp hdlt hQ hι N i hri P.genericPoint
  have hk' := ker_stalkMap_component hSp hdlt hQ hι N j hrj P'.genericPoint
  -- lift `g` and `g'` to germs on `S`
  obtain ⟨t, rfl⟩ := hg
  obtain ⟨t', rfl⟩ := hg'
  obtain ⟨u, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective (N.n i ≫ ι) P.genericPoint t
  obtain ⟨u', rfl⟩ := SurjectiveOnStalks.stalkMap_surjective (N.n j ≫ ι) P'.genericPoint t'
  have hu := sub_mem_maximalIdeal_of_vanishes (N.n i ≫ ι) P u a hv
  have hu' := sub_mem_maximalIdeal_of_vanishes (N.n j ≫ ι) P' u' a hv'
  obtain ⟨W', hxW', s', rfl⟩ := S.presheaf.exists_germ_eq u'
  have hxW'x : x ∈ W' := hPP' ▸ hxW'
  -- the value of `s'` at `x`
  have hu'x : letI := stalkAlgebra sS x
      S.presheaf.germ W' x hxW'x s' - algebraMap k _ a ∈
        IsLocalRing.maximalIdeal (S.presheaf.stalk x) := by
    have key : ∀ w (hw : w ∈ W'), w = (N.n j ≫ ι).base P'.genericPoint →
        letI := stalkAlgebra sS w
        S.presheaf.germ W' w hw s' - algebraMap k _ a ∈
          IsLocalRing.maximalIdeal (S.presheaf.stalk w) := by
      rintro w hw rfl
      exact hu'
    exact key x hxW'x hPP'
  -- `u - s'` lies in `𝔪_x = (z₀, z₁)`
  have hdiff : u - S.presheaf.germ W' x hxW'x s' ∈ Ideal.span {z 0, z 1} := by
    have hr : Set.range z = {z 0, z 1} := by
      ext w; constructor
      · rintro ⟨l, rfl⟩
        fin_cases l
        exacts [Or.inl rfl, Or.inr rfl]
      · rintro (rfl | rfl) <;> exact ⟨_, rfl⟩
    rw [← hr, hzspan]
    have := (IsLocalRing.maximalIdeal (S.presheaf.stalk x)).sub_mem hu hu'x
    rwa [sub_sub_sub_cancel_right] at this
  obtain ⟨r₀, r₁, hr⟩ := Ideal.mem_span_pair.mp hdiff
  have hz₀ : z 0 ∈ RingHom.ker ((N.n i ≫ ι).stalkMap P.genericPoint).hom := by
    rw [hk, hI]; exact Ideal.mem_span_singleton_self _
  have hz₁ : z 1 ∈ AlgebraicGeometry.IdealSheafData.stalk Γ'.idealSheaf x := by
    rw [hI']; exact Ideal.mem_span_singleton_self _
  -- the lift `h = u - r₀ z₀ = s' + r₁ z₁` near `x`
  obtain ⟨W, hxW, h, hh⟩ := S.presheaf.exists_germ_eq (u - r₀ * z 0)
  have hx' : (N.n j ≫ ι).base P'.genericPoint ∈ W := hPP' ▸ hxW
  haveI : Nonempty ((N.n i ≫ ι) ⁻¹ᵁ W) := ⟨⟨P.genericPoint, hxW⟩⟩
  haveI : Nonempty ((N.n j ≫ ι) ⁻¹ᵁ W) := ⟨⟨P'.genericPoint, hx'⟩⟩
  refine ⟨W, hxW, h, ?_, ?_⟩
  · rw [← Scheme.algebraMap_germ_eq_germToFunctionField (N.X i)
      (show P.genericPoint ∈ (N.n i ≫ ι) ⁻¹ᵁ W from hxW), ← Scheme.Hom.germ_stalkMap_apply, hh,
      map_sub, map_mul, RingHom.mem_ker.mp hz₀, mul_zero, sub_zero]
  · -- transport the identity `h - s' ∈ 𝓘_{Γ'}` from `x` to the point over `P'`
    have hdx : S.presheaf.germ W x hxW h - S.presheaf.germ W' x hxW'x s' ∈
        AlgebraicGeometry.IdealSheafData.stalk Γ'.idealSheaf x := by
      rw [hh, show u - r₀ * z 0 - S.presheaf.germ W' x hxW'x s' = r₁ * z 1 by
        linear_combination -hr]
      exact Ideal.mul_mem_left _ _ hz₁
    have key : ∀ w (h₁ : w ∈ W) (h₂ : w ∈ W'), w = x →
        S.presheaf.germ W w h₁ h - S.presheaf.germ W' w h₂ s' ∈
          AlgebraicGeometry.IdealSheafData.stalk Γ'.idealSheaf w := by
      rintro w h₁ h₂ rfl
      exact hdx
    have hd' := key _ hx' hxW' hPP'.symm
    rw [← hk', RingHom.mem_ker, map_sub, sub_eq_zero] at hd'
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField (N.X j)
      (show P'.genericPoint ∈ (N.n j ≫ ι) ⁻¹ᵁ W from hx'), ← Scheme.Hom.germ_stalkMap_apply, hd']

/-- **The normalization of the floor** is the disjoint union of its components. -/
private theorem isFloorNormalization (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal)
    (hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite)
    (N : NormalizationComponents (ι ≫ sS) hC) : IsFloorNormalization sS B ι N := by
  refine ⟨fun i => ?_, fun i => ?_, exists_index_component hSp hdlt hQ hι N,
    injective_component hSp hdlt hQ hι N, isDoubleNormalCrossingPoint_of_ne hSp hdlt hQ hι N,
    fun i j l y y' y'' h1 h2 => ?_, nodeLift_of_ne hSp hdlt hQ hι N⟩
  · exact isFloorNormalization_closedImmersion hSp hdlt hQ hι N i
  · obtain ⟨Γ, hΓ, hg, -⟩ := exists_genericPoint_component hSp hdlt hQ hι N i
    exact ⟨Γ, hΓ, hg⟩
  · -- no three components through a point
    by_contra hne
    push Not at hne
    obtain ⟨hij, hjl, hil⟩ := hne
    obtain ⟨Γi, hΓi, hgi, hri⟩ := range_component hSp hdlt hQ hι N i
    obtain ⟨Γj, hΓj, hgj, hrj⟩ := range_component hSp hdlt hQ hι N j
    obtain ⟨Γl, hΓl, hgl, hrl⟩ := range_component hSp hdlt hQ hι N l
    have hinj := injective_component hSp hdlt hQ hι N
    have hΓij : Γi ≠ Γj := fun h => hij (hinj (by simp only; rw [hgi, hgj, h]))
    have hΓil : Γl ≠ Γi := fun h => hil (hinj (by simp only; rw [hgi, hgl, h])).symm
    have hΓjl : Γl ≠ Γj := fun h => hjl (hinj (by simp only; rw [hgj, hgl, h])).symm
    have hxi : (N.n i ≫ ι).base y ∈ (Γi.support : Set S) := hri ▸ ⟨y, rfl⟩
    have hxj : (N.n i ≫ ι).base y ∈ (Γj.support : Set S) := hrj ▸ h1 ▸ ⟨y', rfl⟩
    have hxl : (N.n i ≫ ι).base y ∈ (Γl.support : Set S) := hrl ▸ h2 ▸ ⟨y'', rfl⟩
    obtain ⟨-, -, -, -, -, hothers⟩ :=
      exists_regularParameters_of_mem_floor_inter hSp hdlt hQ hΓi hΓj hΓij hxi hxj
    have hΓlB : Γl ∈ B.support := Finsupp.mem_support_iff.mpr (by
      change B.coeff Γl ≠ 0
      rw [hΓl]
      exact one_ne_zero)
    rcases hothers Γl hΓlB hxl with h | h
    · exact hΓil h
    · exact hΓjl h

/-- **The singular points of the floor are nodes.** -/
private theorem isDoubleNormalCrossingPoint_of_notMem_smoothLocus
    (hSp : AlgebraicGeometry.IsProjectiveVariety k sS) (hdlt : IsDltPair sS 2 K B)
    (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal) (x : C)
    (hx : IsClosed ({x} : Set C)) (hxs : x ∉ smoothLocus (ι ≫ sS)) :
    IsDoubleNormalCrossingPoint (ι ≫ sS) 1 x := by
  obtain ⟨Γ, hΓ, hcΓ⟩ : ∃ Γ : Mori.PrimeDivisor S, B.coeff Γ = 1 ∧
      ι.base x ∈ (Γ.support : Set S) := by
    have hx' : ι.base x ∈ Set.range ι.base := ⟨x, rfl⟩
    rw [range_floor hι] at hx'
    obtain ⟨Γ, hΓ, hxΓ⟩ := hx'
    exact ⟨Γ, (roundDown_coeff_ne_zero_iff hdlt Γ).mp hΓ, hxΓ⟩
  by_cases h : ∃ Γ' : Mori.PrimeDivisor S, B.coeff Γ' = 1 ∧ ι.base x ∈ (Γ'.support : Set S) ∧
      Γ' ≠ Γ
  · obtain ⟨Γ', hΓ', hcΓ', hne⟩ := h
    exact isDoubleNormalCrossingPoint_of_mem_inter hSp hdlt hQ hι hΓ hΓ' hne.symm hcΓ hcΓ'
  · push Not at h
    exact absurd (mem_smoothLocus_of_forall_eq hSp hdlt hQ hι hΓ hcΓ
      fun Γ' hΓ' hc' => h Γ' hΓ' hc') hxs

end Geometry

/-! ### Residues along isomorphic subschemes -/

/-- The pull-back of rational forms along a morphism inducing an isomorphism of function fields
vanishes only on `0`. -/
private theorem pullbackRationalPluriForms_eq_zero_iff {k : Type} [Field k] [PerfectField k]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms sX d m) : pullbackRationalPluriForms sX f τ = 0 ↔ τ = 0 := by
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (f ≫ sX)
  letI := functionFieldMapAlgebra f
  haveI := isScalarTower_functionFieldMap sX f
  have key : ∀ σ : PluriForms k X.functionField d m,
      pullbackForms (K' := Y.functionField) m σ = 0 ↔ σ = 0 := by
    intro σ
    rw [pullbackForms_eq hω, pullbackFormsAlong, smul_eq_zero,
      map_eq_zero_iff _ (algebraMap X.functionField Y.functionField).injective]
    refine ⟨fun h => ?_, fun h => Or.inl (by simp [h])⟩
    rcases h with h | h
    · have : (ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr σ = 0 :=
        Finsupp.ext fun u => by cases u; simpa using h
      simpa using this
    · exact absurd h ((ZTensorPower.basis _ m).ne_zero ())
  exact key τ

section ResidueDifferent

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {S : Scheme.{0}}
  {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
  [LocallyOfFiniteType sS] [CompactSpace S] {K : Divisor S} {B : QDivisor S}

/-- **Residues along isomorphic subschemes.** If `e : T₁ ≅ T₂` and `ρ₂` is the residue of `τ`
along `j₂ : T₂ ⟶ S`, then `e^*ρ₂` is the residue of `τ` along `e ≫ j₂`; it has the same orders at
corresponding points and vanishes exactly when `ρ₂` does. -/
private theorem isPoincareResidue_iso (hdim : topologicalKrullDim S = 2)
    {T₁ T₂ : Scheme.{0}} [IsIntegral T₁] [IsIntegral T₂] [IsLocallyNoetherian T₁] [IsNormal T₁]
    [IsLocallyNoetherian T₂] [IsNormal T₂] (j₂ : T₂ ⟶ S)
    [LocallyOfFiniteType (j₂ ≫ sS)] (e : T₁ ≅ T₂)
    (Γ : Mori.PrimeDivisor S) (hΓ : j₂ (genericPoint T₂) = Γ.genericPoint)
    (hdT : letI := functionFieldAlgebra (j₂ ≫ sS); (Algebra.trdeg k T₂.functionField).toNat = 1)
    {m : ℕ} {τ : RationalPluriForms sS 2 m} {ρ₂ : RationalPluriForms (j₂ ≫ sS) 1 m}
    (h₂ : IsPoincareResidue sS j₂ 1 m τ ρ₂) :
    IsPoincareResidue sS (e.hom ≫ j₂) 1 m τ (pullbackRationalPluriForms (j₂ ≫ sS) e.hom ρ₂) ∧
      (∀ (Q₁ : Mori.PrimeDivisor T₁) (Q₂ : Mori.PrimeDivisor T₂), e.hom Q₁.genericPoint =
        Q₂.genericPoint → Q₁.ordForm (pullbackRationalPluriForms (j₂ ≫ sS) e.hom ρ₂) =
          Q₂.ordForm ρ₂) ∧
      (pullbackRationalPluriForms (j₂ ≫ sS) e.hom ρ₂ = 0 ↔ ρ₂ = 0) := by
  have hdY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hdim
  have hgb : Function.Bijective (functionFieldMap (𝟙 S)) := by
    have : ⇑(functionFieldMap (𝟙 S)) = id := funext functionFieldMap_id_apply
    rw [this]; exact Function.bijective_id
  have hhb : Function.Bijective (functionFieldMap e.hom) :=
    functionFieldMap_bijective_of_isOpenImmersion e.hom ⊤ ⟨genericPoint T₁, trivial⟩
  have hΓ₁ : (e.hom ≫ j₂) (genericPoint T₁) = Γ.genericPoint := by
    rw [Scheme.Hom.comp_apply, iso_hom_genericPoint e, hΓ]
  have h := MMP.Fourfold.isPoincareResidue_pullback (𝟙 S) j₂ (e.hom ≫ j₂) e.hom sS hgb hhb
    (by rw [Category.comp_id]) Γ hΓ Γ hΓ₁ hdY hdT h₂
  change IsPoincareResidue sS (e.hom ≫ j₂) 1 m (pullbackRationalPluriForms sS (𝟙 S) τ :
    RationalPluriForms sS 2 m) _ at h
  rw [pullbackRationalPluriForms_id hdY τ] at h
  exact ⟨h, fun Q₁ Q₂ hQ =>
    MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso e.hom hhb hdT Q₁ Q₂ hQ ρ₂,
    pullbackRationalPluriForms_eq_zero_iff e.hom hhb hdT ρ₂⟩

/-- Plt is independent of the canonical divisor in its linear equivalence class. -/
private theorem IsPltPair.of_linearlyEquivalent (hQ : IsQFactorial sS) {n : ℕ}
    {K K' : Divisor S} {Δ : QDivisor S} (h : IsPltPair sS n K Δ)
    (hK' : K'.LinearlyEquivalent K) : IsPltPair sS n K' Δ := by
  obtain ⟨⟨hX, hK, -⟩, hd⟩ := h
  refine ⟨⟨hX, hK.of_linearlyEquivalent hK', isQCartier_of_isQFactorial sS hQ _⟩,
    lt_of_lt_of_le hd (le_discrep_iff.mpr fun D a hD ha => discrep_le hD
      (MMP.Spreading.isDiscrepancy_of_linearlyEquivalent ha hK'.symm))⟩

/-- A rational top form with a simple pole along a normal prime divisor of a surface and a nonzero
residue along it. -/
private theorem exists_simplePole_form (hX : IsNormalVariety k sS)
    (hdim : topologicalKrullDim S = 2)
    {T : Scheme.{0}} [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T] [CompactSpace T]
    (j : T ⟶ S) [IsClosedImmersion j] (hT : IsNormalVariety k (j ≫ sS))
    (Γ : Mori.PrimeDivisor S) (hj : Set.range j.base = (Γ.support : Set S)) :
    ∃ τ : RationalPluriForms sS (1 + 1) 1, τ ≠ 0 ∧ Γ.ordForm τ = -1 ∧
      ∃ ρ : RationalPluriForms (j ≫ sS) 1 1, IsPoincareResidue sS j 1 1 τ ρ ∧ ρ ≠ 0 := by
  have hdim' : topologicalKrullDim S = ((1 : ℕ) : WithBot ℕ∞) + 1 := by rw [hdim]; rfl
  have hdimT : topologicalKrullDim T = 1 := by
    exact_mod_cast topologicalKrullDim_eq_of_range_eq_support sS hdim' j Γ hj
  obtain ⟨y, -, hy⟩ := (isClosed_univ (X := T)).exists_closed_singleton Set.univ_nonempty
  have hne : y ≠ genericPoint T := fun h => MMP.Fourfold.not_isClosed_genericPoint hdimT (h ▸ hy)
  have hcoh := MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hdimT hne
  obtain ⟨τ, hτ0, hτΓ, -, ρ, hρ, hρ0, -⟩ := MMP.Fourfold.exists_form_of_residue_order sS hX
    hdim' j hT Γ hj (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hcoh)
  exact ⟨τ, hτ0, hτΓ, ρ, hρ, hρ0⟩

/-- **The residue different of a boundary along a normal component of coefficient one.** For an
effective `B` with `coeff_Γ B = 1` and a normal closed integral `j : T ⟶ S` onto `Γ`, there is a
`ℚ`-divisor `B_T ≥ 0` on `T` such that near every point of `T` the residue of a local generator of
`𝒪_S(m(K_S + B))` generates `𝒪_T(m(K_T + B_T))`, for every `m > 0` with `m(K_S + B)` Cartier, and
`B_T < 1` when `(S, B)` is plt. -/
private theorem exists_residueDifferent_core (hX : IsNormalVariety k sS)
    (hdim : topologicalKrullDim S = 2) {K : Divisor S} (hK : K.IsCanonicalDivisor sS 2)
    (hQ : IsQFactorial sS) {B : QDivisor S} (hB : B.IsEffective) {Γ : Mori.PrimeDivisor S}
    (hΓ : B.coeff Γ = 1) {T : Scheme.{0}} [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    (j : T ⟶ S) [IsClosedImmersion j] (hj : Set.range j.base = (Γ.support : Set S)) :
    ∃ BS : QDivisor T, (∀ Q, 0 ≤ BS.coeff Q) ∧ (IsPltPair sS 2 K B → ∀ Q, BS.coeff Q < 1) ∧
      ∀ m : ℕ, 0 < m → ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor →
        (∀ Q, ((m : ℚ) * BS.coeff Q).den = 1) ∧
        ∀ y : T, ∃ U : S.Opens, j.base y ∈ U ∧ ∃ τ : RationalPluriForms sS 2 m,
          GeneratesOn B m U τ ∧ ∃ ρ : RationalPluriForms (j ≫ sS) 1 m,
            IsPoincareResidue sS j 1 m τ ρ ∧ GeneratesOn BS m (j ⁻¹ᵁ U) ρ := by
  classical
  have hdim' : topologicalKrullDim S = ((1 : ℕ) : WithBot ℕ∞) + 1 := by rw [hdim]; rfl
  haveI : CompactSpace T := j.isClosedEmbedding.compactSpace
  haveI : IsSeparated sS := hX.1.toIsSeparated
  have hT : IsNormalVariety k (j ≫ sS) := ⟨{}, inferInstance⟩
  have hdimT := topologicalKrullDim_eq_of_range_eq_support sS hdim' j Γ hj
  obtain ⟨τ, hτ0, hτΓ, ρ, hρ, hρ0⟩ := exists_simplePole_form hX hdim j hT Γ hj
  set B' : QDivisor S := B - Finsupp.single Γ 1 with hB'
  have hBB' : Finsupp.single Γ 1 + B' = B := by rw [hB']; abel
  have hB'c : ∀ E, B'.coeff E = B.coeff E - if E = Γ then 1 else 0 := fun E => by
    rw [hB', DivisorWithCoeffs.coeff_sub]
    by_cases h : E = Γ
    · subst h; rw [DivisorWithCoeffs.coeff_single_self, if_pos rfl]
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm h), if_neg h]
  have hB'e : B'.IsEffective := fun E => by
    rw [hB'c]
    split_ifs with h
    · subst h; rw [hΓ]; norm_num
    · simpa using hB E
  have hB'Γ : B'.coeff Γ = 0 := by rw [hB'c, if_pos rfl, hΓ, sub_self]
  set D : QDivisor S := Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single Γ 1 + B' with hD
  have hDq : D.IsQCartier := isQCartier_of_isQFactorial sS hQ D
  have hDΓ : D.coeff Γ = 0 := by
    rw [hD, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor,
      coeff_divisorOfForm, hτΓ, DivisorWithCoeffs.coeff_single_self, hB'Γ]
    norm_num
  have hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp := by
    intro Z hZ
    rw [componentGenericPoint_eq_genericPoint, CyclicChartDifferent.Aux.map_genericPoint_eq j Γ hj,
      DivisorWithCoeffs.mem_supp_iff] at hZ
    obtain ⟨E, hE, hΓE⟩ := hZ
    rw [← eq_of_genericPoint_mem_support hΓE] at hE
    exact hE hDΓ
  obtain ⟨Dp, hDp, -⟩ := hDq.existsUnique_isPullback (f := j) hgen
  set BS := Dp - Divisor.toQDivisor (divisorOfForm ρ)
  have hpb : D.IsPullback j hgen (Divisor.toQDivisor (divisorOfForm ρ) + BS) := by
    rwa [add_sub_cancel]
  refine ⟨BS, fun Q => coeff_nonneg_of_isPullback_divisorOfForm_isPoincareResidue_of_charZero sS hX
    hdim' j hT Γ hj B' hB'e hB'Γ τ hτ0 hτΓ ρ hρ hDq BS hgen hpb Q, fun hplt Q => ?_,
    fun m hm hmC => ?_⟩
  · obtain ⟨KS, hKS⟩ := MMP.Mori.exists_isCanonicalDivisor (j ≫ sS) hT hdimT
    have hplt' : IsPltPair sS (1 + 1) (divisorOfForm τ) (Finsupp.single Γ 1 + B') :=
      IsPltPair.of_linearlyEquivalent hQ (hBB' ▸ hplt) (by
        simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ0)
    exact CyclicChartDifferent.Aux.coeff_lt_one_of_isPltPair' sS hX hdim' j hT hdimT Γ hj τ hτ0 hτΓ ρ hρ Q B'
      hB'e hB'Γ hplt' BS ⟨hgen, hpb⟩ KS hKS
      (fun h => MMP.Fourfold.isCartierDivisor_of_forall_generatesOn hT hKS h)
      (fun K hK KS hKS B hB hBP hD BS hBS F =>
        MMP.Fourfold.exists_isExceptional_isDiscrepancy_iff_of_isPoincareResidue sS hX 1 K hK Γ
          j hT hj KS hKS B hB hBP hD BS hBS F)
  obtain ⟨Dm, hDm, hDmc⟩ := hmC
  obtain ⟨φ, hφ⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ0
  set DM := Dm + (m : ℤ) • principalDivisor φ with hDMdef
  have hDM : Divisor.toQDivisor DM = (m : ℤ) • D := by
    have h1 : divisorOfForm τ = K + principalDivisor φ := by
      rw [← hφ, one_smul]; abel
    rw [hDMdef, map_add, hDm, map_zsmul, hD, h1, map_add, ← hBB']
    simp only [smul_add]
    abel
  have hDMc : DM.IsCartier := hDmc.add ((Divisor.isCartier_principalDivisor φ).zsmul _)
  refine ⟨fun Q => ?_, fun y => ?_⟩
  · obtain ⟨D', hD', -⟩ := hpb m hm DM hDM hDMc
    have hc := congrArg (fun G : QDivisor T => G.coeff Q) hD'
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, zsmul_eq_mul, Int.cast_natCast] at hc
    have : (m : ℚ) * BS.coeff Q = ((D'.coeff Q - m * (divisorOfForm ρ).coeff Q : ℤ) : ℚ) := by
      push_cast; rw [hc]; ring
    rw [this, Rat.den_intCast]
  · obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
    obtain ⟨U, hU, τ', hτ', ρ', hρ', hρg⟩ :=
      CyclicChartDifferent.Aux.exists_generatesOn_isPoincareResidue sS hdim' j hT hdimT Γ hj B' τ
        hτ0 ρ hρ hρ0 BS hgen hpb M DM hDM hDMc y
    exact ⟨U, hU, τ', hBB' ▸ hτ', ρ', hρ', hρg⟩

/-- The `ℚ`-Cartier multiples: `n • (m D)` is Cartier when `m D` is. -/
private theorem isCartierDivisor_mul {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} {m : ℕ} (h : ((m : ℤ) • D).IsCartierDivisor) (n : ℕ) :
    (((n * m : ℕ) : ℤ) • D).IsCartierDivisor := by
  obtain ⟨D', hD', hc⟩ := h
  refine ⟨(n : ℤ) • D', ?_, hc.zsmul _⟩
  rw [map_zsmul, hD', smul_smul]
  push_cast; rfl

/-- **The residue different on a component of the floor.** -/
private theorem exists_residueDifferent (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS)
    {Γ : Mori.PrimeDivisor S} (hΓ : B.coeff Γ = 1) {T : Scheme.{0}} [IsIntegral T] [IsNormal T]
    [IsLocallyNoetherian T] (j : T ⟶ S) [IsClosedImmersion j]
    (hj : Set.range j.base = (Γ.support : Set S)) :
    ∃ BS : QDivisor T, (∀ Q, 0 ≤ BS.coeff Q) ∧
      (∀ Q : Mori.PrimeDivisor T, (∀ Γ' : Mori.PrimeDivisor S, B.coeff Γ' = 1 → Γ' ≠ Γ →
        j.base Q.genericPoint ∉ (Γ'.support : Set S)) → BS.coeff Q < 1) ∧
      ∀ m : ℕ, 0 < m → ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor →
        (∀ Q, ((m : ℚ) * BS.coeff Q).den = 1) ∧
        ∀ y : T, ∃ U : S.Opens, j.base y ∈ U ∧ ∃ τ : RationalPluriForms sS 2 m,
          GeneratesOn B m U τ ∧ ∃ ρ : RationalPluriForms (j ≫ sS) 1 m,
            IsPoincareResidue sS j 1 m τ ρ ∧ GeneratesOn BS m (j ⁻¹ᵁ U) ρ := by
  classical
  have hX : IsNormalVariety k sS := hdlt.1.1
  have hK := hdlt.1.2.1
  have hdim : topologicalKrullDim S = 2 := hK.topologicalKrullDim_eq
  have hBe : B.IsEffective := fun E => (hdlt.2.1 E).1
  obtain ⟨BS, h0, -, hgens⟩ := exists_residueDifferent_core hX hdim hK hQ hBe hΓ j hj
  obtain ⟨B'', hB''e, hB''Γ, hplt, hdiff, -⟩ := exists_isPltPair_sub_floor hdlt hQ hΓ
  obtain ⟨BS'', -, hlt'', hgens''⟩ := exists_residueDifferent_core hX hdim hK hQ hB''e hB''Γ j hj
  refine ⟨BS, h0, fun Q hQ' => ?_, hgens⟩
  obtain ⟨m₁, hm₁, hC₁⟩ := hdlt.1.2.2.exists_pos
  obtain ⟨m₂, hm₂, hC₂⟩ := (isQCartier_of_isQFactorial sS hQ (Divisor.toQDivisor K + B'')).exists_pos
  have hm : 0 < m₂ * m₁ := Nat.mul_pos hm₂ hm₁
  have hC : (((m₂ * m₁ : ℕ) : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor :=
    isCartierDivisor_mul hC₁ m₂
  have hC'' : (((m₂ * m₁ : ℕ) : ℤ) • (Divisor.toQDivisor K + B'')).IsCartierDivisor := by
    have := isCartierDivisor_mul hC₂ m₁; rwa [Nat.mul_comm] at this
  obtain ⟨U, hU, τ, hτ, ρ, hρ, hρg⟩ := (hgens _ hm hC).2 Q.genericPoint
  obtain ⟨U'', hU'', τ'', hτ'', ρ'', hρ'', hρg''⟩ := (hgens'' _ hm hC'').2 Q.genericPoint
  -- the other components of `⌊B⌋`
  set Z : Set S := ⋃ E ∈ (B.support.filter fun E => B.coeff E = 1 ∧ E ≠ Γ),
    (E.support : Set S) with hZdef
  have hZ : IsClosed Z := isClosed_biUnion_finset fun E _ => E.idealSheaf.support.isClosed
  set V : S.Opens := U ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩ with hV
  have hQV : j.base Q.genericPoint ∈ V := by
    refine ⟨hU, fun hz => ?_⟩
    simp only [hZdef, Set.mem_iUnion, Finset.mem_filter] at hz
    obtain ⟨E, ⟨-, hE1, hEΓ⟩, hzE⟩ := hz
    exact hQ' E hE1 hEΓ hzE
  have hτV : GeneratesOn B'' (m₂ * m₁) V τ := ⟨hτ.1, fun E hE => by
    have h1 := hτ.2 E (hE.mono (Set.inter_subset_inter_right _ fun z hz => hz.1))
    by_cases hEB : B''.coeff E = B.coeff E
    · rwa [hEB]
    · exfalso
      obtain ⟨hE1, hEΓ⟩ := hdiff E hEB
      obtain ⟨z, hzE, hzV⟩ := hE
      refine hzV.2 ?_
      simp only [hZdef, Set.mem_iUnion, Finset.mem_filter]
      refine ⟨E, ⟨Finsupp.mem_support_iff.mpr ?_, hE1, hEΓ⟩, hzE⟩
      change B.coeff E ≠ 0
      rw [hE1]; exact one_ne_zero⟩
  obtain ⟨D'', hD'', -⟩ := hC''
  have hGm : Divisor.toQDivisor (D'' - ((m₂ * m₁ : ℕ) : ℤ) • K) = ((m₂ * m₁ : ℕ) : ℚ) • B'' := by
    rw [map_sub, hD'', map_zsmul, smul_add, add_sub_cancel_left, ← Int.cast_smul_eq_zsmul ℚ]
    push_cast; rfl
  haveI : LocallyOfFiniteType (j ≫ sS) := inferInstance
  have hdim' : topologicalKrullDim S = ((1 : ℕ) : WithBot ℕ∞) + 1 := by rw [hdim]; rfl
  have hdimT := topologicalKrullDim_eq_of_range_eq_support sS hdim' j Γ hj
  have htr := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := j ≫ sS) hdimT
  have hjη := CyclicChartDifferent.Aux.map_genericPoint_eq j Γ hj
  have heq := ordForm_eq_of_generatesOn hdim hGm hτ'' hτV j Γ hjη htr hρ'' hρ Q ⟨hU'', hQV⟩
  have hQs : ∀ W : S.Opens, j.base Q.genericPoint ∈ W → (Q.support ∩ (j ⁻¹ᵁ W : Set T)).Nonempty :=
    fun W hW => ⟨Q.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, hW⟩
  have e1 := hρg.2 Q (hQs U hU)
  have e2 := hρg''.2 Q (hQs U'' hU'')
  rw [heq] at e1
  have hm0 : ((m₂ * m₁ : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have : BS.coeff Q = BS''.coeff Q := by
    have := e1.trans e2.symm
    exact mul_left_cancel₀ hm0 (by linarith)
  rw [this]
  exact hlt'' hplt Q

end ResidueDifferent

section NodeE2

variable {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]

/-- The prime of the generization `η_Γ ⤳ x` in `𝒪_{S,x}` is the stalk of the ideal of `Γ`. -/
private theorem primeOfSpecializes_eq_stalk {x : S} (Γ : Mori.PrimeDivisor S)
    (hx : x ∈ (Γ.support : Set S)) (hsp : Γ.genericPoint ⤳ x) :
    MMP.Intersection.primeOfSpecializes hsp = IdealSheafData.stalk Γ.idealSheaf x := by
  obtain ⟨q, hq, hqs, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support Γ hx
  have h := MMP.Intersection.fromSpecStalk_primeOfSpecializes hsp
  have hinj := (S.fromSpecStalk x).isEmbedding.injective
  have := hinj (h.trans hq.symm)
  rw [hqs, ← this]

open Classical in
/-- **Orders of a local equation of a prime divisor.** If the ideal of `Γ` at `x` is generated by
`π`, then `π` has order one along `Γ` and order zero along every other prime divisor through
`x`. -/
private theorem ord_algebraMap_of_stalk_eq_span {x : S} {Γ : Mori.PrimeDivisor S}
    (hx : x ∈ (Γ.support : Set S)) {π : S.presheaf.stalk x}
    (hπ : IdealSheafData.stalk Γ.idealSheaf x = Ideal.span {π}) (E : Mori.PrimeDivisor S)
    (hxE : x ∈ (E.support : Set S)) :
    S.ord (algebraMap (S.presheaf.stalk x) S.functionField π) E.genericPoint =
      if E = Γ then 1 else 0 := by
  have hspE : E.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hxE
  have hsp : Γ.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hx
  have hpΓ := (primeOfSpecializes_eq_stalk Γ hx hsp).trans hπ
  haveI := E.isDiscreteValuationRing_localRing
  have hcoh := E.coheight_genericPoint
  rw [← CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' S hspE π]
  split_ifs with hEΓ
  · subst hEΓ
    letI := (S.presheaf.stalkSpecializes hsp).hom.toAlgebra
    haveI := MMP.Intersection.isLocalization_stalkSpecializes hsp
    have hmax := IsLocalization.AtPrime.map_eq_maximalIdeal
      (MMP.Intersection.primeOfSpecializes hsp) (S.presheaf.stalk E.genericPoint)
    rw [hpΓ, Ideal.map_span, Set.image_singleton] at hmax
    have hirr : Irreducible ((S.presheaf.stalkSpecializes hsp).hom π) :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax.symm
    exact (Scheme.ord_eq_iff hcoh ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      hirr.ne_zero)).mpr (Ring.ordFrac_irreducible hirr)
  · have hnot : π ∉ MMP.Intersection.primeOfSpecializes hspE := by
      intro hmem
      have hle : MMP.Intersection.primeOfSpecializes hsp ≤
          MMP.Intersection.primeOfSpecializes hspE := by
        rw [hpΓ, Ideal.span_le, Set.singleton_subset_iff]; exact hmem
      have h1 := MMP.Intersection.specializes_of_primeOfSpecializes_le hsp hspE hle
      exact hEΓ (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (eq_of_specializes_of_coheight_eq_one h1 Γ.coheight_genericPoint hcoh).symm)
    have hu : IsUnit ((S.presheaf.stalkSpecializes hspE).hom π) := by
      by_contra h
      exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr h)
    exact ord_algebraMap_eq_zero_of_isUnit hcoh hu

end NodeE2

section Node

variable {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]

/-- The ideal of a closed immersion of an integral scheme onto a prime divisor `Γ` is the ideal of
`Γ`. -/
private theorem ker_eq_idealSheaf {T : Scheme.{0}} [IsIntegral T] (j : T ⟶ S) [IsClosedImmersion j]
    (Γ : Mori.PrimeDivisor S) (hj : Set.range j.base = (Γ.support : Set S)) :
    j.ker = Γ.idealSheaf := by
  haveI : IsIntegral Γ.idealSheaf.subscheme := Γ.integral
  rw [j.ker_eq_vanishingIdeal_closure_range,
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme Γ.idealSheaf _ rfl]
  congr 1
  ext x
  change x ∈ closure (Set.range j.base) ↔ x ∈ (Γ.support : Set S)
  rw [j.isClosedEmbedding.isClosed_range.closure_eq, hj]

/-- **The second parameter is a uniformizer on the first branch.** If `z₀, z₁` is a regular
system of parameters at `j(P)` and the ideal of `Γ = j(T)` there is `(z₀)`, then `z₁` restricts to
a uniformizer of `T` at `P`. -/
private theorem ord_stalkMap_eq_one {T : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] (j : T ⟶ S) [IsClosedImmersion j] (Γ : Mori.PrimeDivisor S)
    (hj : Set.range j.base = (Γ.support : Set S)) (P : Mori.PrimeDivisor T)
    {z : Fin 2 → S.presheaf.stalk (j.base P.genericPoint)} (hz : IsRegularSystemOfParameters z)
    (hz0 : IdealSheafData.stalk Γ.idealSheaf (j.base P.genericPoint) = Ideal.span {z 0}) :
    T.ord (algebraMap _ T.functionField ((j.stalkMap P.genericPoint).hom (z 1)))
      P.genericPoint = 1 := by
  haveI := P.isDiscreteValuationRing_localRing
  have hsurj := SurjectiveOnStalks.stalkMap_surjective j P.genericPoint
  have hker : RingHom.ker (j.stalkMap P.genericPoint).hom = Ideal.span {z 0} := by
    rw [← IdealSheafData.stalk_ker_of_isClosedImmersion, ker_eq_idealSheaf j Γ hj, hz0]
  have hmax : IsLocalRing.maximalIdeal (T.presheaf.stalk P.genericPoint) =
      Ideal.span {(j.stalkMap P.genericPoint).hom (z 1)} := by
    have h1 := IsLocalRing.map_maximalIdeal_of_surjective _ hsurj
    rw [← hz.1] at h1
    rw [← h1, Ideal.map_span]
    have hr : Set.range z = {z 0, z 1} := by
      ext w; constructor
      · rintro ⟨l, rfl⟩; fin_cases l
        exacts [Or.inl rfl, Or.inr rfl]
      · rintro (rfl | rfl) <;> exact ⟨_, rfl⟩
    have h0 : (j.stalkMap P.genericPoint).hom (z 0) = 0 := by
      rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _
    rw [hr, Set.image_pair, h0, Ideal.span_insert_zero]
  have hirr : Irreducible ((j.stalkMap P.genericPoint).hom (z 1)) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  exact (Scheme.ord_eq_iff P.coheight_genericPoint ((map_ne_zero_iff _
    (IsFractionRing.injective _ _)).mpr hirr.ne_zero)).mpr (Ring.ordFrac_irreducible hirr)

open Classical in
/-- An element outside the ideal of `Γ` at `x` has order zero along `Γ`. -/
private theorem ord_algebraMap_eq_zero_of_notMem_stalk {x : S} {Γ : Mori.PrimeDivisor S}
    (hx : x ∈ (Γ.support : Set S)) {c : S.presheaf.stalk x}
    (hc : c ∉ IdealSheafData.stalk Γ.idealSheaf x) :
    S.ord (algebraMap (S.presheaf.stalk x) S.functionField c) Γ.genericPoint = 0 := by
  have hsp : Γ.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hx
  haveI := Γ.isDiscreteValuationRing_localRing
  rw [← CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' S hsp c]
  have hu : IsUnit ((S.presheaf.stalkSpecializes hsp).hom c) := by
    by_contra h
    refine hc ?_
    rw [← primeOfSpecializes_eq_stalk Γ hx hsp]
    exact (IsLocalRing.mem_maximalIdeal _).mpr h
  exact ord_algebraMap_eq_zero_of_isUnit Γ.coheight_genericPoint hu

end Node

section NodeForm

variable {k : Type} [Field k] {S : Scheme.{0}} (sS : S ⟶ Spec (.of k)) [IsIntegral S]
  [IsLocallyNoetherian S] [IsNormal S]

/-- The form `(dz₀ ∧ dz₁ / (z₀ z₁))^{⊗m}` of a pair of functions near a point. -/
private noncomputable def nodeForm {x : S} (z : Fin 2 → S.presheaf.stalk x) (m : ℕ) :
    RationalPluriForms sS 2 m :=
  letI := functionFieldAlgebra sS
  (formPow ((algebraMap _ S.functionField (z 0) * algebraMap _ S.functionField (z 1))⁻¹ •
    exteriorPower.ιMulti S.functionField 2 fun i =>
      KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (z i))) m :
    PluriForms k S.functionField 2 m)

variable {sS}

/-- **The residue of `(dz₀ ∧ dz₁ / (z₀ z₁))^{⊗m}` along `z₀ = 0` is `(dz₁/z₁)^{⊗m}`.** -/
private theorem isPoincareResidue_nodeForm {T : Scheme.{0}} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] (j : T ⟶ S) [IsClosedImmersion j]
    (Γ : Mori.PrimeDivisor S) (hj : Set.range j.base = (Γ.support : Set S))
    (P : Mori.PrimeDivisor T) {z : Fin 2 → S.presheaf.stalk (j.base P.genericPoint)}
    (hz : IsRegularSystemOfParameters z)
    (hz0 : IdealSheafData.stalk Γ.idealSheaf (j.base P.genericPoint) = Ideal.span {z 0})
    (m : ℕ) :
    IsPoincareResidue sS j 1 m (nodeForm sS z m) (dlogPow (j ≫ sS)
      (algebraMap _ T.functionField ((j.stalkMap P.genericPoint).hom (z 1))) m) := by
  letI := functionFieldAlgebra sS
  letI := functionFieldAlgebra (j ≫ sS)
  have hη := CyclicChartDifferent.Aux.map_genericPoint_eq j Γ hj
  have hx : j.base P.genericPoint ∈ (Γ.support : Set S) := hj ▸ ⟨P.genericPoint, rfl⟩
  have hsp : j.base (genericPoint T) ⤳ j.base P.genericPoint :=
    ((genericPoint_spec T).specializes trivial).map j.base.hom.continuous
  set φ := (S.presheaf.stalkSpecializes hsp).hom with hφ
  have hcoh : Order.coheight (j.base (genericPoint T)) = 1 := hη ▸ Γ.coheight_genericPoint
  haveI : IsDiscreteValuationRing (S.presheaf.stalk (j.base (genericPoint T))) := by
    rw [hη]; exact Γ.isDiscreteValuationRing_localRing
  have ha : algebraMap _ S.functionField (φ (z 0)) = algebraMap _ S.functionField (z 0) :=
    CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' S hsp _
  have hb : algebraMap _ S.functionField (φ (z 1)) = algebraMap _ S.functionField (z 1) :=
    CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' S hsp _
  have ht : S.ord (algebraMap _ S.functionField (φ (z 0))) (j.base (genericPoint T)) = 1 := by
    rw [ha, hη, ord_algebraMap_of_stalk_eq_span hx hz0 Γ hx, if_pos rfl]
  have hz1 : z 1 ∉ IdealSheafData.stalk Γ.idealSheaf (j.base P.genericPoint) := by
    rw [hz0]
    exact notMem_span_singleton_of_isRegularSystemOfParameters hz (by decide)
  have hb0 : S.ord (algebraMap _ S.functionField (φ (z 1))) (j.base (genericPoint T)) = 0 := by
    rw [hb, hη, ord_algebraMap_eq_zero_of_notMem_stalk hx hz1]
  have hbne : algebraMap _ S.functionField (φ (z 1)) ≠ 0 := by
    intro h0
    apply hz1
    rw [hb] at h0
    have : z 1 = 0 := IsFractionRing.injective _ S.functionField (h0.trans (map_zero _).symm)
    rw [this]; exact zero_mem _
  obtain ⟨r, hr⟩ := (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hcoh
    (inv_ne_zero hbne)).mpr (by
      have := Scheme.ord_mul (x := j.base (genericPoint T)) hbne (inv_ne_zero hbne)
      rw [mul_inv_cancel₀ hbne, CyclicChartDifferent.Aux.ord_one', hb0] at this
      omega)
  -- `r = z₁⁻¹` near the generic point of `T`
  have hr1 : r * φ (z 1) = 1 := IsFractionRing.injective _ S.functionField (by
    rw [map_mul, hr, inv_mul_cancel₀ hbne, map_one])
  set w : T.functionField :=
    algebraMap _ T.functionField ((j.stalkMap P.genericPoint).hom (z 1)) with hw
  have hsp' : genericPoint T ⤳ P.genericPoint := (genericPoint_spec T).specializes trivial
  have hw' : (j.stalkMap (genericPoint T)).hom (φ (z 1)) = w := by
    rw [hφ, Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ hsp', hw,
      ← CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' T hsp',
      CyclicChartDifferent.Aux.algebraMap_stalk_genericPoint]
  have hwr : (j.stalkMap (genericPoint T)).hom r = w⁻¹ := by
    have := congrArg (j.stalkMap (genericPoint T)).hom hr1
    rw [map_mul, map_one, hw'] at this
    exact eq_inv_of_mul_eq_one_left this
  refine ⟨φ (z 0), r ^ m, fun _ => φ (z 1), ht, ?_, ?_⟩
  · have hfun : (fun i : Fin 2 => KaehlerDifferential.D k S.functionField
        (algebraMap _ S.functionField (z i))) = Fin.cons (KaehlerDifferential.D k S.functionField
          (algebraMap _ S.functionField (φ (z 0)))) fun _ : Fin 1 =>
            KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (φ (z 1))) := by
      funext i; fin_cases i
      · simp [ha]
      · simp [hb]
    change (formPow _ m : PluriForms k S.functionField 2 m) = _
    rw [formPow_smul, hfun, map_pow, hr, ha, hb]
    unfold formPow
    rw [tprod_const_smul, smul_smul, mul_inv, mul_pow, mul_comm]
    simp only [hb]
    rfl
  · change (PiTensorProduct.tprod T.functionField fun _ : Fin m =>
      w⁻¹ • exteriorPower.ιMulti T.functionField 1 fun _ => KaehlerDifferential.D k _ w) = _
    rw [tprod_const_smul, map_pow, hwr]
    simp only [hw']

/-- **The node form is symmetric in even degree.** Exchanging `z₀` and `z₁` changes
`(dz₀ ∧ dz₁ / (z₀ z₁))^{⊗m}` by `(-1)^m`. -/
private theorem nodeForm_swap {x : S} (z : Fin 2 → S.presheaf.stalk x) {m : ℕ} (hm : Even m) :
    nodeForm sS ![z 1, z 0] m = nodeForm sS z m := by
  letI := functionFieldAlgebra sS
  have hω : (exteriorPower.ιMulti S.functionField 2 fun i =>
      KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (![z 1, z 0] i))) =
      -exteriorPower.ιMulti S.functionField 2 fun i =>
        KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (z i)) := by
    have := (exteriorPower.ιMulti S.functionField 2 (M := Ω[S.functionField⁄k])).map_swap
      (fun i => KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (z i)))
      (i := 0) (j := 1) (by decide)
    convert this using 2
    funext i; fin_cases i <;> rfl
  change (formPow _ m : PluriForms k S.functionField 2 m) = (formPow _ m : PluriForms k _ 2 m)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hω, smul_neg, ← neg_one_smul S.functionField, formPow_smul, hm.neg_one_pow, one_smul,
    mul_comm]

/-- `ω^{⊗(M+1)}` is the `(M+1)`-th power of `ω`. -/
private theorem formPow_eq_pluriPow {d : ℕ}
    (ω : letI := functionFieldAlgebra sS; ⋀[S.functionField]^d Ω[S.functionField⁄k]) :
    ∀ M : ℕ, letI := functionFieldAlgebra sS
      (formPow ω (M + 1) : RationalPluriForms sS d ((M + 1 : ℕ) : ℤ)) =
        CyclicChartDifferent.Aux.pluriPow (formPow ω 1 : RationalPluriForms sS d 1) M
  | 0 => rfl
  | M + 1 => by
    letI := functionFieldAlgebra sS
    have ih := formPow_eq_pluriPow ω M
    change _ = RationalPluriForms.mul sS d (M + 1) 1
      (CyclicChartDifferent.Aux.pluriPow (formPow ω 1 : RationalPluriForms sS d 1) M)
      (formPow ω 1 : RationalPluriForms sS d 1)
    exact (pluriFormsMul_formPow ω (M + 1) 1).symm.trans
      (congrArg (fun τ => RationalPluriForms.mul sS d (M + 1) 1 τ
        (formPow ω 1 : RationalPluriForms sS d 1)) ih)

end NodeForm

section NodeKaehler

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {S : Scheme.{0}}
  {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
  [LocallyOfFiniteType sS] [CompactSpace S]

/-- **Regular parameters at a smooth closed point give a generator of the top forms.** If `x` is
a closed point of the smooth locus of a surface and `z₀, z₁` a regular system of parameters of
`𝒪_{S,x}`, then `dz₀ ∧ dz₁` generates `Ω²_{𝒪_{S,x}/k}`. -/
private theorem span_ιMulti_D_eq_top {x : S} (hx : x ∈ smoothLocus sS)
    (hxc : IsClosed ({x} : Set S)) {z : Fin 2 → S.presheaf.stalk x}
    (hz : IsRegularSystemOfParameters z) :
    letI := stalkAlgebra sS x
    Submodule.span (S.presheaf.stalk x)
      {exteriorPower.ιMulti (S.presheaf.stalk x) 2 fun i =>
        KaehlerDifferential.D k (S.presheaf.stalk x) (z i)} = ⊤ := by
  letI := stalkAlgebra sS x
  obtain ⟨U, hU, hxU⟩ : ∃ U : S.Opens, Smooth (U.ι ≫ sS) ∧ x ∈ U := by
    have h := hx
    rw [smoothLocus, TopologicalSpace.Opens.mem_sSup] at h
    obtain ⟨U, hU, hxU⟩ := h
    exact ⟨U, hU, hxU⟩
  obtain ⟨h1, h2, h3⟩ := MMP.Flips.ResolutionInputs.stalk_facts (U.ι ≫ sS) ⟨x, hxU⟩
  letI := stalkAlgebra (U.ι ≫ sS) ⟨x, hxU⟩
  let y : U.toScheme := ⟨x, hxU⟩
  haveI hiso : IsIso (U.ι.stalkMap y) :=
    AlgebraicGeometry.IsOpenImmersion.instIsIsoCommRingCatStalkMap U.ι y
  let e₀ : S.presheaf.stalk x ≃+* U.toScheme.presheaf.stalk y :=
    (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv
  let e : S.presheaf.stalk x ≃ₐ[k] U.toScheme.presheaf.stalk y :=
    AlgEquiv.ofRingEquiv (f := e₀) fun a => by
      change (U.ι.stalkMap y).hom _ = _
      exact stalkMap_stalkAlgebra U.ι y a
  haveI : Algebra.FormallySmooth k (S.presheaf.stalk x) := Algebra.FormallySmooth.of_equiv e.symm
  haveI : Algebra.EssFiniteType k (S.presheaf.stalk x) :=
    (Algebra.EssFiniteType.iff_of_algEquiv e).mpr h3
  have : Module.Finite k (IsLocalRing.ResidueField (S.presheaf.stalk x)) :=
    MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sS x hxc
  have : Algebra.FormallyUnramified k (IsLocalRing.ResidueField (S.presheaf.stalk x)) :=
    Algebra.FormallyUnramified.of_isSeparable _ _
  obtain ⟨ht0, hli, hsp⟩ := MMP.Flips.ResolutionInputs.cotangent_basis_of_regular z hz.1 hz.2
  have hli' := MMP.Flips.ResolutionInputs.linearIndependent_tmul_D k z ht0 hli
  have hsp' := MMP.Flips.ResolutionInputs.span_tmul_D k z hz.1
  have : Module.Projective (S.presheaf.stalk x) Ω[S.presheaf.stalk x⁄k] :=
    ((Algebra.formallySmooth_iff _ _).mp ‹_›).1
  have hbij : Function.Bijective (Finsupp.linearCombination (S.presheaf.stalk x)
      (fun i => KaehlerDifferential.D k (S.presheaf.stalk x) (z i))) := by
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    refine ⟨hli', ?_⟩
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact top_le_iff.mp hsp'
  let b := Module.Basis.ofRepr (LinearEquiv.ofBijective _ hbij).symm
  have hb : ∀ i, b i = KaehlerDifferential.D k (S.presheaf.stalk x) (z i) := fun i => by
    simp [b, Module.Basis.ofRepr]
  have hspan : Submodule.span (S.presheaf.stalk x) (Set.range fun i =>
      KaehlerDifferential.D k (S.presheaf.stalk x) (z i)) = ⊤ := by
    rw [← b.span_eq]; congr 1; ext; simp [hb]
  have h2 := exteriorPower.ιMulti_family_span_of_span (S.presheaf.stalk x) (n := 2) hspan
  refine eq_top_iff.mpr (h2.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨s, rfl⟩
  have he : ∀ e : Fin 2 ↪o Fin 2, ∀ i, e i = i := by
    intro e i
    have h01 : e 0 < e 1 := e.strictMono (by decide)
    rw [Fin.lt_def] at h01
    have h0 := (e 0).isLt
    have h1 := (e 1).isLt
    fin_cases i <;> ext <;> simp <;> omega
  change exteriorPower.ιMulti _ 2 (_ ∘ _) ∈ _
  convert Set.mem_singleton _ using 2
  funext i
  simp only [Function.comp_apply]
  rw [he]

/-- **`dz₀ ∧ dz₁` has no zero or pole through `x`.** For a regular system of parameters `z₀, z₁` at
a closed point `x` of the smooth locus of a surface, the rational `2`-form `dz₀ ∧ dz₁` has order
zero along every prime divisor through `x`. -/
private theorem ordForm_tprod_ιMulti_D_eq_zero (hdim : topologicalKrullDim S = 2) {x : S}
    (hx : x ∈ smoothLocus sS) (hxc : IsClosed ({x} : Set S)) {z : Fin 2 → S.presheaf.stalk x}
    (hz : IsRegularSystemOfParameters z) (E : Mori.PrimeDivisor S)
    (hxE : x ∈ (E.support : Set S)) :
    letI := functionFieldAlgebra sS
    E.ordForm (sX := sS) (d := 2) (m := 1) (PiTensorProduct.tprod S.functionField
      fun _ : Fin 1 => exteriorPower.ιMulti S.functionField 2 fun i =>
        KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (z i)) :
      TensorPower S.functionField 1 (⋀[S.functionField]^2 Ω[S.functionField⁄k])) = 0 := by
  letI := stalkAlgebra sS x
  letI := functionFieldAlgebra sS
  haveI := isScalarTower_stalk_functionField sS x
  have hσ := span_ιMulti_D_eq_top hx hxc hz
  set σ := exteriorPower.ιMulti (S.presheaf.stalk x) 2 fun i =>
    KaehlerDifferential.D k (S.presheaf.stalk x) (z i) with hσdef
  obtain ⟨b₀⟩ := MMP.Fourfold.exists_basis_topForms (sX := sS) (d := 2) (by rw [hdim]; rfl)
  haveI : Nontrivial (⋀[S.functionField]^2 Ω[S.functionField⁄k]) :=
    ⟨⟨b₀ (), 0, b₀.ne_zero ()⟩⟩
  have h0 : topFormsMap k (S.presheaf.stalk x) S.functionField 2 σ ≠ 0 :=
    topFormsMap_ne_zero_of_span_eq_top hσ
  have hτ := ZTensorPower.basis_ofNat (topFormsBasis _ hσ h0) 1
  have e : topFormsMap k (S.presheaf.stalk x) S.functionField 2 σ =
      exteriorPower.ιMulti S.functionField 2 fun i =>
        KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (z i)) := by
    rw [hσdef, topFormsMap_ιMulti]
    simp only [KaehlerDifferential.map_D]
  rw [topFormsBasis_apply, e] at hτ
  have key : E.ordForm (sX := sS) (d := 2) (m := 1)
      (ZTensorPower.basis (topFormsBasis _ hσ h0) (Int.ofNat 1) ()) = 0 := by
    have h := MMP.Threefold.Resolution.ordForm_eq_ord_formCoeff sS x E hxE hσ h0 (d := 2)
      (m := 1) (ZTensorPower.basis (topFormsBasis _ hσ h0) (Int.ofNat 1) ())
    have h1 : formCoeff (S.presheaf.stalk x) hσ h0
        (ZTensorPower.basis (topFormsBasis _ hσ h0) (Int.ofNat 1) ()) = 1 := by
      simp [formCoeff]
    exact h.trans (by rw [h1]; exact CyclicChartDifferent.Aux.ord_one' _)
  exact (congrArg (fun τ : RationalPluriForms sS 2 1 => E.ordForm τ) hτ.symm).trans key

/-- For a regular system of parameters at a closed point of the smooth locus, `dz₀ ∧ dz₁ ≠ 0`. -/
private theorem ιMulti_D_ne_zero (hdim : topologicalKrullDim S = 2) {x : S}
    (hx : x ∈ smoothLocus sS) (hxc : IsClosed ({x} : Set S)) {z : Fin 2 → S.presheaf.stalk x}
    (hz : IsRegularSystemOfParameters z) :
    letI := functionFieldAlgebra sS
    (exteriorPower.ιMulti S.functionField 2 fun i =>
      KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (z i))) ≠ 0 := by
  letI := stalkAlgebra sS x
  letI := functionFieldAlgebra sS
  haveI := isScalarTower_stalk_functionField sS x
  have hσ := span_ιMulti_D_eq_top hx hxc hz
  obtain ⟨b₀⟩ := MMP.Fourfold.exists_basis_topForms (sX := sS) (d := 2) (by rw [hdim]; rfl)
  haveI : Nontrivial (⋀[S.functionField]^2 Ω[S.functionField⁄k]) :=
    ⟨⟨b₀ (), 0, b₀.ne_zero ()⟩⟩
  have h0 := topFormsMap_ne_zero_of_span_eq_top (K := S.functionField) hσ
  rw [topFormsMap_ιMulti] at h0
  simpa only [KaehlerDifferential.map_D] using h0

/-- **The residue at a node, on one branch.** Let `z₀, z₁` be a regular system of parameters at
`x = j(P)` with the ideal of `Γ = j(T)` equal to `(z₀)`, and `τ = u (dz₀ ∧ dz₁ / (z₀ z₁))^{⊗m}`
with `u` a unit at `x` of value `c`. Then the residue of `τ` along `T` has a pole of order exactly
`m` at `P`, with leading coefficient `c`. -/
private theorem ordForm_isPoincareResidue_of_eq_smul_nodeForm (hX : IsNormalVariety k sS)
    (hdim : topologicalKrullDim S = 2)
    {T : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] (j : T ⟶ S)
    [IsClosedImmersion j] (Γ : Mori.PrimeDivisor S) (hj : Set.range j.base = (Γ.support : Set S))
    (P : Mori.PrimeDivisor T) {z : Fin 2 → S.presheaf.stalk (j.base P.genericPoint)}
    (hz : IsRegularSystemOfParameters z)
    (hz0 : IdealSheafData.stalk Γ.idealSheaf (j.base P.genericPoint) = Ideal.span {z 0})
    {u : S.presheaf.stalk (j.base P.genericPoint)} (hu : IsUnit u) (c : k)
    (hc : letI := stalkAlgebra sS (j.base P.genericPoint)
      u - algebraMap k _ c ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk (j.base P.genericPoint)))
    {m : ℕ} (hm : 0 < m) {τ : RationalPluriForms sS 2 m}
    (hτ : τ = algebraMap _ S.functionField u • nodeForm sS z m)
    {ρ : RationalPluriForms (j ≫ sS) 1 m} (hρ : IsPoincareResidue sS j 1 m τ ρ) :
    P.ordForm ρ = -(m : ℤ) ∧ (letI := functionFieldAlgebra (j ≫ sS)
      ∃ w : T.functionField, T.ord w P.genericPoint = 1 ∧
        (ρ - algebraMap k T.functionField c • dlogPow (j ≫ sS) w m = 0 ∨
          1 - (m : ℤ) ≤ P.ordForm (ρ - algebraMap k T.functionField c •
            dlogPow (j ≫ sS) w m))) := by
  letI := functionFieldAlgebra (j ≫ sS)
  haveI : CompactSpace T := j.isClosedEmbedding.compactSpace
  haveI : IsSeparated sS := hX.1.toIsSeparated
  have hT : IsNormalVariety k (j ≫ sS) := ⟨{}, inferInstance⟩
  haveI : LocallyOfFiniteType (j ≫ sS) := inferInstance
  have hdim' : topologicalKrullDim S = ((1 : ℕ) : WithBot ℕ∞) + 1 := by rw [hdim]; rfl
  have hdimT := topologicalKrullDim_eq_of_range_eq_support sS hdim' j Γ hj
  have hdimT1 : topologicalKrullDim T = 1 := by exact_mod_cast hdimT
  have htr := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := j ≫ sS) hdimT
  have hη := CyclicChartDifferent.Aux.map_genericPoint_eq j Γ hj
  have hsp : j.base (genericPoint T) ⤳ j.base P.genericPoint :=
    ((genericPoint_spec T).specializes trivial).map j.base.hom.continuous
  have hsp' : genericPoint T ⤳ P.genericPoint := (genericPoint_spec T).specializes trivial
  set uη := (S.presheaf.stalkSpecializes hsp).hom u with huη
  set w : T.functionField :=
    algebraMap _ T.functionField ((j.stalkMap P.genericPoint).hom (z 1)) with hw
  set ū : T.functionField :=
    algebraMap _ T.functionField ((j.stalkMap P.genericPoint).hom u) with hū
  have hūη : (j.stalkMap (genericPoint T)).hom uη = ū := by
    rw [huη, Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ hsp', hū,
      ← CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' T hsp',
      CyclicChartDifferent.Aux.algebraMap_stalk_genericPoint]
  -- the residue of `τ`
  have hres := CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul
    (isPoincareResidue_nodeForm j Γ hj P hz hz0 m (sS := sS)) uη
  rw [CyclicChartDifferent.Aux.algebraMap_stalkSpecializes', ← hτ, hūη] at hres
  have hρeq : ρ = ū • dlogPow (j ≫ sS) w m := MMP.Fourfold.isPoincareResidue_unique hη hρ hres
  -- orders
  have hw1 : T.ord w P.genericPoint = 1 := ord_stalkMap_eq_one j Γ hj P hz hz0
  obtain ⟨hD10, hD1⟩ := MMP.Flips.ordForm_dlogPow_one_of_ord_eq_one hT hdimT1 P w hw1
  obtain ⟨hDm0, hDm⟩ := MMP.Flips.ordForm_dlogPow_eq_mul hT hdimT1 w hD10 m
  have hcoh := P.coheight_genericPoint
  haveI := P.isDiscreteValuationRing_localRing
  have hūu : IsUnit ((j.stalkMap P.genericPoint).hom u) := hu.map _
  have hū0 : ū = 0 ∨ 0 ≤ T.ord ū P.genericPoint := Or.inr
    (ord_algebraMap_eq_zero_of_isUnit hcoh hūu).ge
  have hū0' : ū ≠ 0 := (hūu.map (algebraMap _ T.functionField)).ne_zero
  refine ⟨?_, w, hw1, ?_⟩
  · rw [hρeq, P.ordForm_smul htr hū0' hDm0, ord_algebraMap_eq_zero_of_isUnit hcoh hūu,
      hDm P, hD1]
    ring
  · -- `ū - c` vanishes at `P`
    have hval : ū - algebraMap k T.functionField c = 0 ∨
        1 ≤ T.ord (ū - algebraMap k T.functionField c) P.genericPoint := by
      letI := stalkAlgebra sS (j.base P.genericPoint)
      letI := stalkAlgebra (j ≫ sS) P.genericPoint
      haveI := isScalarTower_stalk_functionField (j ≫ sS) P.genericPoint
      have hmP : (j.stalkMap P.genericPoint).hom (u - algebraMap k _ c) ∈
          IsLocalRing.maximalIdeal (T.presheaf.stalk P.genericPoint) := map_nonunit _ _ hc
      rw [map_sub, stalkMap_stalkAlgebra j P.genericPoint c] at hmP
      have hK : ū - algebraMap k T.functionField c = algebraMap _ T.functionField
          ((j.stalkMap P.genericPoint).hom u - algebraMap k _ c) := by
        rw [map_sub, hū, ← IsScalarTower.algebraMap_apply]
      rw [hK]
      by_cases h0 : algebraMap _ T.functionField
          ((j.stalkMap P.genericPoint).hom u - algebraMap k _ c) = 0
      · exact Or.inl h0
      · exact Or.inr (one_le_ord_of_mem_maximalIdeal P hmP h0)
    have e : ρ - algebraMap k T.functionField c • dlogPow (j ≫ sS) w m =
        (ū - algebraMap k T.functionField c) • dlogPow (j ≫ sS) w m := by
      rw [hρeq, sub_smul]
    rw [e]
    have hD : OrdGE P (-(m : ℤ)) (dlogPow (j ≫ sS) w m) := Or.inr (by rw [hDm P, hD1]; ring_nf; rfl)
    have := hD.smul htr hval
    rcases this with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)

open Classical in
/-- **A local generator at a node.** If `x` is a closed point of the smooth locus where exactly the
two components `Γ, Γ'` of `B` pass, both of coefficient one, with local equations `z₀, z₁` forming
a regular system of parameters, then a generator of `𝒪_S(m(K_S + B))` near `x` is
`u (dz₀ ∧ dz₁ / (z₀ z₁))^{⊗m}` with `u` a unit at `x`. -/
private theorem exists_isUnit_eq_smul_nodeForm (hdim : topologicalKrullDim S = 2) {B : QDivisor S}
    {x : S} (hxs : x ∈ smoothLocus sS) (hxc : IsClosed ({x} : Set S)) {Γ Γ' : Mori.PrimeDivisor S}
    (hne : Γ ≠ Γ') (hΓ : B.coeff Γ = 1) (hΓ' : B.coeff Γ' = 1) (hx : x ∈ (Γ.support : Set S))
    (hx' : x ∈ (Γ'.support : Set S)) {z : Fin 2 → S.presheaf.stalk x}
    (hz : IsRegularSystemOfParameters z) (hz0 : IdealSheafData.stalk Γ.idealSheaf x = Ideal.span {z 0})
    (hz1 : IdealSheafData.stalk Γ'.idealSheaf x = Ideal.span {z 1})
    (hB : ∀ E : Mori.PrimeDivisor S, B.coeff E ≠ 0 → x ∈ (E.support : Set S) → E = Γ ∨ E = Γ')
    {m : ℕ} (hm : 0 < m) {U : S.Opens} (hxU : x ∈ U) {τ : RationalPluriForms sS 2 m}
    (hτ : GeneratesOn B m U τ) :
    ∃ u : S.presheaf.stalk x, IsUnit u ∧ τ = algebraMap _ S.functionField u • nodeForm sS z m := by
  letI := functionFieldAlgebra sS
  have htr := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hdim
  have hω0 := ιMulti_D_ne_zero hdim hxs hxc hz
  set ω := exteriorPower.ιMulti S.functionField 2 fun i =>
    KaehlerDifferential.D k S.functionField (algebraMap _ S.functionField (z i)) with hωdef
  set a := algebraMap _ S.functionField (z 0)
  set b := algebraMap _ S.functionField (z 1)
  have hoa : ∀ E : Mori.PrimeDivisor S, x ∈ (E.support : Set S) →
      S.ord a E.genericPoint = if E = Γ then 1 else 0 :=
    fun E hE => ord_algebraMap_of_stalk_eq_span hx hz0 E hE
  have hob : ∀ E : Mori.PrimeDivisor S, x ∈ (E.support : Set S) →
      S.ord b E.genericPoint = if E = Γ' then 1 else 0 :=
    fun E hE => ord_algebraMap_of_stalk_eq_span hx' hz1 E hE
  have ha0 : a ≠ 0 := by
    intro h; have := hoa Γ hx; rw [if_pos rfl, h] at this
    have h0 := congrFun Scheme.ord_zero Γ.genericPoint
    simp only [Pi.zero_apply] at h0; omega
  have hb0 : b ≠ 0 := by
    intro h; have := hob Γ' hx'; rw [if_pos rfl, h] at this
    have h0 := congrFun Scheme.ord_zero Γ'.genericPoint
    simp only [Pi.zero_apply] at h0; omega
  have hab0 : (a * b)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero ha0 hb0)
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  have h1 : (formPow ω 1 : RationalPluriForms sS 2 1) ≠ 0 := fun h =>
    hω0 (MMP.Fourfold.tprod_fin_one_injective (F := S.functionField) (h.trans
      ((PiTensorProduct.tprod S.functionField).map_coord_zero
        (m := fun _ : Fin 1 => (0 : ⋀[S.functionField]^2 Ω[S.functionField⁄k])) 0 rfl).symm))
  set F : RationalPluriForms sS 2 ((M + 1 : ℕ) : ℤ) := formPow ω (M + 1) with hFdef
  have hF : F = CyclicChartDifferent.Aux.pluriPow (formPow ω 1 : RationalPluriForms sS 2 1) M :=
    formPow_eq_pluriPow ω M
  have hpow : F ≠ 0 := by
    rw [hF]
    exact CyclicChartDifferent.Aux.pluriPow_ne_zero hdim h1 M
  have hτx : nodeForm sS z (M + 1) = ((a * b)⁻¹) ^ (M + 1) • F := by
    change (formPow _ _ : PluriForms k S.functionField 2 _) = _
    rw [formPow_smul]
    rfl
  have hτx0 : nodeForm sS z (M + 1) ≠ 0 := by
    rw [hτx]; exact smul_ne_zero (pow_ne_zero _ hab0) hpow
  -- orders of `τ_x` and `τ` through `x`
  have hordx : ∀ E : Mori.PrimeDivisor S, x ∈ (E.support : Set S) →
      E.ordForm (nodeForm sS z (M + 1)) =
        -((M + 1 : ℕ) : ℤ) * ((if E = Γ then 1 else 0) + (if E = Γ' then 1 else 0)) := by
    intro E hE
    have hω1 : E.ordForm (sX := sS) (d := 2) (m := 1) (formPow ω 1) = 0 :=
      ordForm_tprod_ιMulti_D_eq_zero hdim hxs hxc hz E hE
    rw [hτx, E.ordForm_smul htr (pow_ne_zero _ hab0) hpow, hF,
      CyclicChartDifferent.Aux.ordForm_pluriPow hdim h1 E M, hω1, ord_pow_eq hab0,
      ← hoa E hE, ← hob E hE]
    have hinv : S.ord (a * b)⁻¹ E.genericPoint = -(S.ord a E.genericPoint +
        S.ord b E.genericPoint) := by
      have := Scheme.ord_mul (x := E.genericPoint) (mul_ne_zero ha0 hb0) hab0
      rw [mul_inv_cancel₀ (mul_ne_zero ha0 hb0), CyclicChartDifferent.Aux.ord_one',
        Scheme.ord_mul ha0 hb0] at this
      omega
    rw [hinv]; push_cast; ring
  have hord : ∀ E : Mori.PrimeDivisor S, x ∈ (E.support : Set S) →
      E.ordForm τ = -((M + 1 : ℕ) : ℤ) * ((if E = Γ then 1 else 0) + (if E = Γ' then 1 else 0)) := by
    intro E hE
    have h := hτ.2 E ⟨x, hE, hxU⟩
    have hc : B.coeff E = ((if E = Γ then 1 else 0) + (if E = Γ' then 1 else 0) : ℤ) := by
      by_cases h1 : E = Γ
      · subst h1; rw [if_pos rfl, if_neg hne, hΓ]; norm_num
      by_cases h2 : E = Γ'
      · subst h2; rw [if_neg h1, if_pos rfl, hΓ']; norm_num
      rw [if_neg h1, if_neg h2]
      by_contra h3
      rcases hB E (by simpa using h3) hE with h4 | h4
      · exact h1 h4
      · exact h2 h4
    rw [hc] at h
    have : ((E.ordForm τ : ℤ) : ℚ) = ((-((M + 1 : ℕ) : ℤ) * ((if E = Γ then 1 else 0) +
        (if E = Γ' then 1 else 0)) : ℤ) : ℚ) := by push_cast at h ⊢; linarith
    exact_mod_cast this
  -- the quotient `τ / τ_x`
  obtain ⟨f, hf⟩ := (finrank_eq_one_iff_of_nonzero' _ hτx0).mp
    (finrank_rationalPluriForms (m := M + 1) hdim) τ
  have hf0 : f ≠ 0 := by rintro rfl; rw [zero_smul] at hf; exact hτ.1 hf.symm
  have hof : ∀ E : Mori.PrimeDivisor S, x ∈ (E.support : Set S) → S.ord f E.genericPoint = 0 := by
    intro E hE
    have := E.ordForm_smul htr hf0 hτx0
    rw [hf, hord E hE, hordx E hE] at this
    omega
  obtain ⟨u, hu⟩ := MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord x hf0
    fun E hE => (hof E hE).ge
  obtain ⟨u', hu'⟩ := MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord x
    (inv_ne_zero hf0) fun E hE => by
      have := Scheme.ord_mul (x := E.genericPoint) hf0 (inv_ne_zero hf0)
      rw [mul_inv_cancel₀ hf0, CyclicChartDifferent.Aux.ord_one', hof E hE] at this
      omega
  have huu : u * u' = 1 := IsFractionRing.injective _ S.functionField (by
    rw [map_mul, hu, hu', mul_inv_cancel₀ hf0, map_one])
  exact ⟨u, ⟨⟨u, u', huu, by rw [mul_comm]; exact huu⟩, rfl⟩, by rw [hu, hf]⟩

/-- Exchanging two parameters keeps a regular system of parameters. -/
private theorem isRegularSystemOfParameters_swap {R : Type*} [CommRing R] [IsLocalRing R]
    {z : Fin 2 → R} (hz : IsRegularSystemOfParameters z) :
    IsRegularSystemOfParameters ![z 1, z 0] := by
  refine ⟨?_, hz.2⟩
  rw [← hz.1]
  congr 1
  ext w; constructor
  · rintro ⟨l, rfl⟩; fin_cases l
    exacts [⟨1, rfl⟩, ⟨0, rfl⟩]
  · rintro ⟨l, rfl⟩; fin_cases l
    exacts [⟨1, rfl⟩, ⟨0, rfl⟩]

/-- **Equal leading coefficients at a node.** At a node `x` of the floor (as in
`exists_isUnit_eq_smul_nodeForm`), for even `m` the residues of a local generator of
`𝒪_S(m(K_S + B))` along the two branches have poles of order exactly `m` at the points over `x`,
with the same leading coefficient. -/
private theorem exists_leadingCoeff_node (hX : IsNormalVariety k sS)
    (hdim : topologicalKrullDim S = 2) {B : QDivisor S}
    {x : S} (hxs : x ∈ smoothLocus sS) (hxc : IsClosed ({x} : Set S)) {Γ Γ' : Mori.PrimeDivisor S}
    (hne : Γ ≠ Γ') (hΓ : B.coeff Γ = 1) (hΓ' : B.coeff Γ' = 1) (hx : x ∈ (Γ.support : Set S))
    (hx' : x ∈ (Γ'.support : Set S)) {z : Fin 2 → S.presheaf.stalk x}
    (hz : IsRegularSystemOfParameters z) (hz0 : IdealSheafData.stalk Γ.idealSheaf x = Ideal.span {z 0})
    (hz1 : IdealSheafData.stalk Γ'.idealSheaf x = Ideal.span {z 1})
    (hB : ∀ E : Mori.PrimeDivisor S, B.coeff E ≠ 0 → x ∈ (E.support : Set S) → E = Γ ∨ E = Γ')
    {m : ℕ} (hm : 0 < m) (hme : Even m) {U : S.Opens} (hxU : x ∈ U)
    {τ : RationalPluriForms sS 2 m} (hτ : GeneratesOn B m U τ) :
    ∃ c : k, ∀ {T : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] (j : T ⟶ S)
      [IsClosedImmersion j],
      (Set.range j.base = (Γ.support : Set S) ∨ Set.range j.base = (Γ'.support : Set S)) →
      ∀ (P : Mori.PrimeDivisor T), j.base P.genericPoint = x →
      ∀ {ρ : RationalPluriForms (j ≫ sS) 1 m}, IsPoincareResidue sS j 1 m τ ρ →
        P.ordForm ρ = -(m : ℤ) ∧ (letI := functionFieldAlgebra (j ≫ sS)
          ∃ w : T.functionField, T.ord w P.genericPoint = 1 ∧
            (ρ - algebraMap k T.functionField c • dlogPow (j ≫ sS) w m = 0 ∨
              1 - (m : ℤ) ≤ P.ordForm (ρ - algebraMap k T.functionField c •
                dlogPow (j ≫ sS) w m))) := by
  obtain ⟨u, hu, hτu⟩ :=
    exists_isUnit_eq_smul_nodeForm hdim hxs hxc hne hΓ hΓ' hx hx' hz hz0 hz1 hB hm hxU hτ
  letI := stalkAlgebra sS x
  haveI := MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sS x hxc
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
    (K := IsLocalRing.ResidueField (S.presheaf.stalk x))).2 (IsLocalRing.residue _ u)
  have hc' : u - algebraMap k _ c ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk x) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc]
    exact sub_eq_zero.mpr rfl
  refine ⟨c, fun {T} _ _ _ j _ hj P hP ρ hρ => ?_⟩
  subst hP
  rcases hj with hj | hj
  · exact ordForm_isPoincareResidue_of_eq_smul_nodeForm hX hdim j Γ hj P hz hz0 hu c hc' hm hτu hρ
  · exact ordForm_isPoincareResidue_of_eq_smul_nodeForm hX hdim j Γ' hj P
      (isRegularSystemOfParameters_swap hz) (by simpa using hz1) hu c hc' hm
      (by rw [nodeForm_swap z hme]; exact hτu) hρ

end NodeKaehler

section Assembly

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {S : Scheme.{0}}
  {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
  [LocallyOfFiniteType sS] {B : QDivisor S} {m : ℕ} {Gm : Divisor S}

/-- **Comparing local generators along a component.** If `τ₀, τ₁` generate `𝒪_S(m(K_S + B))` on
`U₀, U₁` and `ρ₁ ≠ 0` is the residue of `τ₁` along `T`, then near a point of `T` over `U₀ ∩ U₁`
the form `τ₀` has a nonzero residue along `T`, with the orders of `ρ₁` over `U₀ ∩ U₁`. -/
private theorem exists_isPoincareResidue_of_generatesOn (hdim : topologicalKrullDim S = 2)
    (hGm : Divisor.toQDivisor Gm = (m : ℚ) • B) {Γ : Mori.PrimeDivisor S} {T : Scheme.{0}}
    [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T] (j : T ⟶ S) [IsClosedImmersion j]
    (hj : Set.range j.base = (Γ.support : Set S)) {U₀ U₁ : S.Opens}
    {τ₀ τ₁ : RationalPluriForms sS 2 m} (h₀ : GeneratesOn B m U₀ τ₀) (h₁ : GeneratesOn B m U₁ τ₁)
    {ρ₁ : RationalPluriForms (j ≫ sS) 1 m} (hρ₁ : IsPoincareResidue sS j 1 m τ₁ ρ₁)
    (hρ₁0 : ρ₁ ≠ 0) (y : T) (hy : j.base y ∈ U₀ ⊓ U₁) :
    ∃ ρ₀ : RationalPluriForms (j ≫ sS) 1 m, IsPoincareResidue sS j 1 m τ₀ ρ₀ ∧ ρ₀ ≠ 0 ∧
      ∀ Q : Mori.PrimeDivisor T, j.base Q.genericPoint ∈ U₀ ⊓ U₁ →
        Q.ordForm ρ₀ = Q.ordForm ρ₁ := by
  haveI : LocallyOfFiniteType (j ≫ sS) := inferInstance
  have hdim' : topologicalKrullDim S = ((1 : ℕ) : WithBot ℕ∞) + 1 := by rw [hdim]; rfl
  have hdimT := topologicalKrullDim_eq_of_range_eq_support sS hdim' j Γ hj
  have htr := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := j ≫ sS) hdimT
  have hjη := CyclicChartDifferent.Aux.map_genericPoint_eq j Γ hj
  have hη : j.base (genericPoint T) ∈ U₀ ⊓ U₁ :=
    (((genericPoint_spec T).specializes trivial).map j.base.hom.continuous).mem_open
      (U₀ ⊓ U₁).isOpen hy
  haveI : Nonempty U₀ := ⟨⟨_, hy.1⟩⟩
  haveI : Nonempty U₁ := ⟨⟨_, hy.2⟩⟩
  obtain ⟨h, hτh, -⟩ := exists_residue_eq_smul hdim hGm hy.1 hy.2 h₁
    (mem_pluricanonicalSections_of_generatesOn hGm h₀)
  have hres := isPoincareResidue_germToFunctionField_smul hρ₁ hη h
  rw [← hτh] at hres
  refine ⟨_, hres, fun h0 => ?_, fun Q hQ =>
    (ordForm_eq_of_generatesOn hdim hGm h₀ h₁ j Γ hjη htr hres hρ₁ Q hQ).symm⟩
  -- symmetrically `τ₁ = h' τ₀`, so `ρ₁ = h̄' ρ₀`
  obtain ⟨h', -, hres'⟩ := exists_residue_eq_smul hdim hGm hy.2 hy.1 h₀
    (mem_pluricanonicalSections_of_generatesOn hGm h₁)
  have := hres' j Γ hjη _ ρ₁ ⟨hη.2, hη.1⟩ hres hρ₁
  rw [h0, smul_zero] at this
  exact hρ₁0 this

end Assembly

section Geometry

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
  {S C : Scheme.{0}} {sS : S ⟶ Spec (.of k)}
  [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [QuasiCompact sS]
  {K : Divisor S} {B : QDivisor S} {ι : C ⟶ S} [IsClosedImmersion ι]

/-- **Smooth points of the floor are Weil prime divisors.** A point of a component of the
normalization of the floor lying over a point of `C` that is not a node is the generic point of a
prime divisor of `C` with discrete valuation local ring. -/
private theorem exists_weilDivisorPrime_of_not_isDoubleNormalCrossingPoint
    (hSp : AlgebraicGeometry.IsProjectiveVariety k sS) (hdlt : IsDltPair sS 2 K B)
    (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal)
    {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
    (N : NormalizationComponents (ι ≫ sS) hC) (i : N.ι) (P : Mori.PrimeDivisor (N.X i))
    (hnd : ¬ IsDoubleNormalCrossingPoint (ι ≫ sS) 1 ((N.n i).base P.genericPoint)) :
    ∃ c : WeilDivisorPrime C, c.1.genericPoint = (N.n i).base P.genericPoint := by
  haveI := hSp.toIsVariety
  have hdim : topologicalKrullDim S = 2 := hdlt.1.2.1.topologicalKrullDim_eq
  have hfl := isFloorNormalization hSp hdlt hQ hι hC N
  haveI := hfl.isClosedImmersion i
  set p := (N.n i).base P.genericPoint with hp
  -- `p` is a closed point
  have hdimi := topologicalKrullDim_component hdim hfl i
  have hPne : P.genericPoint ≠ genericPoint (N.X i) := by
    intro h
    have := P.coheight_genericPoint
    rw [h, Order.coheight_eq_zero.mpr fun b _ => (genericPoint_spec (N.X i)).specializes trivial]
      at this
    exact zero_ne_one this
  have hPc : IsClosed ({P.genericPoint} : Set (N.X i)) :=
    Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint (N.X i)
      (by exact_mod_cast hdimi) hPne
  have hpc : IsClosed ({p} : Set C) := by
    have h1 : IsClosed ({(N.n i ≫ ι).base P.genericPoint} : Set S) := by
      rw [← Set.image_singleton]; exact (N.n i ≫ ι).isClosedEmbedding.isClosedMap _ hPc
    have : ({p} : Set C) = ι.base ⁻¹' {(N.n i ≫ ι).base P.genericPoint} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ rfl, fun h => ι.isClosedEmbedding.injective h⟩
    rw [this]; exact h1.preimage ι.base.hom.continuous
  -- `p` is a smooth point, so `𝒪_{C,p}` is regular
  have hps : p ∈ smoothLocus (ι ≫ sS) := by
    by_contra hns
    exact hnd (isDoubleNormalCrossingPoint_of_notMem_smoothLocus hSp hdlt hQ hι p hpc hns)
  obtain ⟨U, hpU, hU⟩ := mem_smoothLocus_iff.mp hps
  haveI : Smooth (U.ι ≫ ι ≫ sS) := hU
  haveI := isRegularLocalRing_stalk_of_smooth_over_field (U.ι ≫ ι ≫ sS) ⟨p, hpU⟩
  haveI hreg : IsRegularLocalRing (C.presheaf.stalk p) :=
    IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨p, hpU⟩).commRingCatIsoToRingEquiv
  -- `p` has coheight one
  have hq : (N.n i).base (genericPoint (N.X i)) ⤳ p :=
    ((genericPoint_spec (N.X i)).specializes trivial).map (N.n i).base.hom.continuous
  have hqne : p ≠ (N.n i).base (genericPoint (N.X i)) := by
    intro h
    exact hPne ((N.n i ≫ ι).isClosedEmbedding.injective (by
      change ι.base p = ι.base _; rw [h]; rfl))
  have hlt := MMP.Intersection.lt_of_specializes_of_ne hq hqne
  have hcoh1 : 1 ≤ Order.coheight p := by
    have := Order.coheight_add_one_le hlt
    exact le_trans (by simp) this
  have hle := ringKrullDim_stalk_floor_le_one hdim hι p
  rw [ringKrullDim_stalk_eq_coheight] at hle
  have hcoh : Order.coheight p = 1 := by
    refine le_antisymm ?_ hcoh1
    exact_mod_cast hle
  have hd1 : ringKrullDim (C.presheaf.stalk p) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hcoh]; rfl
  have hdvr := MMP.Resolution.Kollar.isDiscreteValuationRing_of_ringKrullDim_eq_one hd1
  set Γ := AlgebraicGeometry.PrimeDivisor.ofCoheightOne p hcoh
  have hΓ : Γ.genericPoint = p := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne p hcoh
  refine ⟨⟨Γ, ?_⟩, hΓ⟩
  change ∃ _ : IsDomain (C.presheaf.stalk Γ.genericPoint),
    IsDiscreteValuationRing (C.presheaf.stalk Γ.genericPoint)
  rw [hΓ]
  exact hdvr

/-- Residues along isomorphic subschemes, for a composite `j₁ = e ≫ j₂`. -/
private theorem exists_isPoincareResidue_of_iso [LocallyOfFiniteType sS] [CompactSpace S]
    (hdim : topologicalKrullDim S = 2)
    {T₁ T₂ : Scheme.{0}} [IsIntegral T₁] [IsIntegral T₂] [IsLocallyNoetherian T₁] [IsNormal T₁]
    [IsLocallyNoetherian T₂] [IsNormal T₂] (j₁ : T₁ ⟶ S) (j₂ : T₂ ⟶ S)
    [LocallyOfFiniteType (j₂ ≫ sS)] (e : T₁ ≅ T₂) (he : e.hom ≫ j₂ = j₁)
    (Γ : Mori.PrimeDivisor S) (hΓ : j₂ (genericPoint T₂) = Γ.genericPoint)
    (hdT : letI := functionFieldAlgebra (j₂ ≫ sS); (Algebra.trdeg k T₂.functionField).toNat = 1)
    {m : ℕ} {τ : RationalPluriForms sS 2 m} {ρ₂ : RationalPluriForms (j₂ ≫ sS) 1 m}
    (h₂ : IsPoincareResidue sS j₂ 1 m τ ρ₂) :
    ∃ ρ₁ : RationalPluriForms (j₁ ≫ sS) 1 m, IsPoincareResidue sS j₁ 1 m τ ρ₁ ∧
      (∀ (Q₁ : Mori.PrimeDivisor T₁) (Q₂ : Mori.PrimeDivisor T₂), e.hom Q₁.genericPoint =
        Q₂.genericPoint → Q₁.ordForm ρ₁ = Q₂.ordForm ρ₂) ∧ (ρ₁ = 0 ↔ ρ₂ = 0) := by
  subst he
  exact ⟨_, isPoincareResidue_iso hdim j₂ e Γ hΓ hdT h₂⟩

/-- At a node of the floor a second component of `⌊B⌋` passes. -/
private theorem exists_ne_of_isDoubleNormalCrossingPoint
    (hSp : AlgebraicGeometry.IsProjectiveVariety k sS) (hdlt : IsDltPair sS 2 K B)
    (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal) {Γ : Mori.PrimeDivisor S}
    (hΓ : B.coeff Γ = 1) {c : C} (hc : ι.base c ∈ (Γ.support : Set S))
    (hdnc : IsDoubleNormalCrossingPoint (ι ≫ sS) 1 c) :
    ∃ Γ' : Mori.PrimeDivisor S, B.coeff Γ' = 1 ∧ ι.base c ∈ (Γ'.support : Set S) ∧ Γ' ≠ Γ := by
  haveI := hSp.toIsVariety
  haveI : LocallyOfFiniteType (ι ≫ sS) := inferInstance
  by_contra h
  push Not at h
  exact hdnc.notMem_smoothLocus (mem_smoothLocus_of_forall_eq hSp hdlt hQ hι hΓ hc
    fun Γ' hΓ' hc' => h Γ' hΓ' hc')

open Classical in
/-- The sum defining `componentBoundaryCoeff` at the generic point of a Weil prime divisor. -/
private theorem sum_ite_genericPoint_eq (Δ : QWeilDivisor C) (c : WeilDivisorPrime C) {p : C}
    (hp : c.1.genericPoint = p) :
    (∑ Γ ∈ Δ.support, if p = Γ.1.genericPoint then Δ Γ else 0) = Δ c := by
  classical
  have key : ∀ Γ : WeilDivisorPrime C, p = Γ.1.genericPoint ↔ Γ = c := fun Γ =>
    ⟨fun h => Subtype.ext (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (h.symm.trans hp.symm)), fun h => h ▸ hp.symm⟩
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

/-- The points of `C` with a discrete valuation local ring are not nodes. -/
private theorem not_isDoubleNormalCrossingPoint_of_weilDivisorPrime (Γ : WeilDivisorPrime C) :
    ¬ IsDoubleNormalCrossingPoint (ι ≫ sS) 1 Γ.1.genericPoint := by
  obtain ⟨hdom, hdvr⟩ := Γ.2
  intro hx
  have hreg : IsRegularLocalRing (C.presheaf.stalk Γ.1.genericPoint) := inferInstance
  have hcomp : IsRegularLocalRing (AdicCompletion
      (IsLocalRing.maximalIdeal (C.presheaf.stalk Γ.1.genericPoint))
      (C.presheaf.stalk Γ.1.genericPoint)) :=
    isRegularLocalRing_iff_adicCompletion_maximalIdeal.mp hreg
  have hd := IsRegularLocalRing.isDomain (AdicCompletion
    (IsLocalRing.maximalIdeal (C.presheaf.stalk Γ.1.genericPoint))
    (C.presheaf.stalk Γ.1.genericPoint))
  obtain ⟨-, -, ⟨e⟩⟩ := hx
  let := (stalkStructureMap (ι ≫ sS) Γ.1.genericPoint).toAlgebra
  exact MMP.Flips.not_isDomain_quotient_X_mul_X k (e.symm.toRingEquiv.toMulEquiv.isDomain _)

/-- **The different.** There are a boundary `Δ` on the floor with coefficients in `[0, 1)` and an
even `r > 0` with `rΔ` integral such that, for every normalization of the floor and every positive
multiple `m` of `r`, `m(K + B)` is Cartier with residue generators near every point. -/
private theorem exists_floorDifferent (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS) (hι : ι.ker = B.roundDown.suppIdeal) :
    ∃ Δ : QWeilDivisor C, (∀ Γ, 0 ≤ Δ Γ ∧ Δ Γ < 1) ∧
      ∃ r : ℕ, 0 < r ∧ Even r ∧ (∀ Γ, ((r : ℚ) * Δ Γ).den = 1) ∧
      ∀ (hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite)
        (N : NormalizationComponents (ι ≫ sS) hC), IsFloorNormalization sS B ι N →
        ∀ m : ℕ, 0 < m → r ∣ m →
          ∃ Gm : Divisor S, Divisor.toQDivisor Gm = (m : ℚ) • B ∧
            ((m : ℤ) • K + Gm).IsCartier ∧ HasResidueGenerators sS B ι N Δ m := by
  classical
  haveI := hSp.toIsVariety
  have hX : IsNormalVariety k sS := hdlt.1.1
  have hK := hdlt.1.2.1
  have hdim : topologicalKrullDim S = 2 := hK.topologicalKrullDim_eq
  haveI : LocallyOfFiniteType sS := hX.1.toLocallyOfFiniteType
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  obtain ⟨m₀, hm₀, hC₀⟩ := hdlt.1.2.2.exists_pos
  -- the residue differents on the components of `⌊B⌋`
  have hBSex : ∀ (Γ : Mori.PrimeDivisor S) (hΓ : B.coeff Γ = 1),
      haveI := Γ.integral
      haveI := isNormal_floor_component hSp hdlt hQ Γ hΓ
      haveI : IsLocallyNoetherian Γ.idealSheaf.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (Γ.idealSheaf.subschemeι ≫ sS)
      ∃ BS : QDivisor Γ.idealSheaf.subscheme, (∀ Q, 0 ≤ BS.coeff Q) ∧
        (∀ Q : Mori.PrimeDivisor Γ.idealSheaf.subscheme,
          (∀ Γ' : Mori.PrimeDivisor S, B.coeff Γ' = 1 → Γ' ≠ Γ →
            Γ.idealSheaf.subschemeι.base Q.genericPoint ∉ (Γ'.support : Set S)) →
          BS.coeff Q < 1) ∧
        ∀ m : ℕ, 0 < m → ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor →
          (∀ Q, ((m : ℚ) * BS.coeff Q).den = 1) ∧
          ∀ y : Γ.idealSheaf.subscheme, ∃ U : S.Opens, Γ.idealSheaf.subschemeι.base y ∈ U ∧
            ∃ τ : RationalPluriForms sS 2 m, GeneratesOn B m U τ ∧
              ∃ ρ : RationalPluriForms (Γ.idealSheaf.subschemeι ≫ sS) 1 m,
                IsPoincareResidue sS Γ.idealSheaf.subschemeι 1 m τ ρ ∧
                  GeneratesOn BS m (Γ.idealSheaf.subschemeι ⁻¹ᵁ U) ρ := by
    intro Γ hΓ
    haveI := Γ.integral
    haveI := isNormal_floor_component hSp hdlt hQ Γ hΓ
    haveI : IsLocallyNoetherian Γ.idealSheaf.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (Γ.idealSheaf.subschemeι ≫ sS)
    exact exists_residueDifferent hdlt hQ hΓ _ (Scheme.IdealSheafData.range_subschemeι _)
  choose BS hBS0 hBSlt hBSgen using hBSex
  -- the coefficient of the different at a point of `S`
  let δ : S → ℚ := fun x => if h : ∃ (Γ : Mori.PrimeDivisor S) (hΓ : B.coeff Γ = 1)
      (Q : Mori.PrimeDivisor Γ.idealSheaf.subscheme),
      Γ.idealSheaf.subschemeι.base Q.genericPoint = x then
    (BS h.choose h.choose_spec.choose).coeff h.choose_spec.choose_spec.choose else 0
  -- `δ` at a point of a single component of `⌊B⌋`
  have hδeq : ∀ (Γ : Mori.PrimeDivisor S) (hΓ : B.coeff Γ = 1)
      (Q : Mori.PrimeDivisor Γ.idealSheaf.subscheme),
      (∀ Γ' : Mori.PrimeDivisor S, B.coeff Γ' = 1 →
        Γ.idealSheaf.subschemeι.base Q.genericPoint ∈ (Γ'.support : Set S) → Γ' = Γ) →
      δ (Γ.idealSheaf.subschemeι.base Q.genericPoint) = (BS Γ hΓ).coeff Q := by
    intro Γ hΓ Q huniq
    have hex : ∃ (Γ₁ : Mori.PrimeDivisor S) (hΓ₁ : B.coeff Γ₁ = 1)
        (Q₁ : Mori.PrimeDivisor Γ₁.idealSheaf.subscheme),
        Γ₁.idealSheaf.subschemeι.base Q₁.genericPoint =
          Γ.idealSheaf.subschemeι.base Q.genericPoint := ⟨Γ, hΓ, Q, rfl⟩
    have key : ∀ (Γ₁ : Mori.PrimeDivisor S) (hΓ₁ : B.coeff Γ₁ = 1)
        (Q₁ : Mori.PrimeDivisor Γ₁.idealSheaf.subscheme),
        Γ₁.idealSheaf.subschemeι.base Q₁.genericPoint =
          Γ.idealSheaf.subschemeι.base Q.genericPoint →
        (BS Γ₁ hΓ₁).coeff Q₁ = (BS Γ hΓ).coeff Q := by
      intro Γ₁ hΓ₁ Q₁ hQ₁
      have hr : Set.range Γ₁.idealSheaf.subschemeι.base = (Γ₁.support : Set S) :=
        Scheme.IdealSheafData.range_subschemeι _
      have hmem : Γ.idealSheaf.subschemeι.base Q.genericPoint ∈ (Γ₁.support : Set S) := by
        rw [← hQ₁, ← hr]; exact ⟨_, rfl⟩
      obtain rfl := huniq Γ₁ hΓ₁ hmem
      have : Q₁ = Q := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (Γ₁.idealSheaf.subschemeι.isClosedEmbedding.injective hQ₁)
      subst this
      rfl
    dsimp only [δ]
    rw [dif_pos hex]
    exact key _ _ _ hex.choose_spec.choose_spec.choose_spec
  have hδ0 : ∀ x, 0 ≤ δ x := fun x => by
    dsimp only [δ]
    split_ifs with h
    · exact hBS0 _ _ _
    · exact le_rfl
  have hδden : ∀ x, ((m₀ : ℚ) * δ x).den = 1 := fun x => by
    dsimp only [δ]
    split_ifs with h
    · exact (hBSgen _ _ m₀ hm₀ hC₀).1 _
    · simp
  -- finitely many points carry a nonzero coefficient
  have hδfin : {x : S | δ x ≠ 0}.Finite := by
    refine (B.roundDown.support.finite_toSet.biUnion fun Γ _ =>
      (show {x : S | ∃ (hΓ : B.coeff Γ = 1) (Q : Mori.PrimeDivisor Γ.idealSheaf.subscheme),
        Q ∈ (BS Γ hΓ).support ∧ Γ.idealSheaf.subschemeι.base Q.genericPoint = x}.Finite from ?_)).subset
        ?_
    · by_cases hΓ : B.coeff Γ = 1
      · refine ((BS Γ hΓ).support.finite_toSet.image
          fun Q => Γ.idealSheaf.subschemeι.base Q.genericPoint).subset ?_
        rintro x ⟨hΓ', Q, hQ, rfl⟩
        exact ⟨Q, hQ, rfl⟩
      · convert Set.finite_empty
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hΓ', -⟩
        exact hΓ hΓ'
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx
      dsimp only [δ] at hx
      split_ifs at hx with h
      · refine Set.mem_biUnion (x := h.choose) ?_ ⟨h.choose_spec.choose,
          h.choose_spec.choose_spec.choose, Finsupp.mem_support_iff.mpr hx,
          h.choose_spec.choose_spec.choose_spec⟩
        rw [Finset.mem_coe, Finsupp.mem_support_iff]
        exact (roundDown_coeff_ne_zero_iff hdlt _).mpr h.choose_spec.choose
      · exact absurd rfl hx
  -- the boundary `Δ` on the floor
  let f : WeilDivisorPrime C → S := fun c => ι.base c.1.genericPoint
  have hfinj : Function.Injective f := fun c c' h => Subtype.ext
    (AlgebraicGeometry.PrimeDivisor.genericPoint_injective (ι.isClosedEmbedding.injective h))
  let Δ : QWeilDivisor C := Finsupp.ofSupportFinite (fun c => δ (f c))
    ((hδfin.preimage hfinj.injOn).subset fun c hc => hc)
  have hΔ : ∀ c, Δ c = δ (f c) := fun c => rfl
  -- a Weil prime divisor of `C` lies on a single component of `⌊B⌋`
  have huniqc : ∀ (c : WeilDivisorPrime C) (Γ Γ' : Mori.PrimeDivisor S), B.coeff Γ = 1 →
      B.coeff Γ' = 1 → f c ∈ (Γ.support : Set S) → f c ∈ (Γ'.support : Set S) → Γ' = Γ := by
    intro c Γ Γ' hΓ hΓ' h h'
    by_contra hne
    exact not_isDoubleNormalCrossingPoint_of_weilDivisorPrime (sS := sS) (ι := ι) c
      (isDoubleNormalCrossingPoint_of_mem_inter hSp hdlt hQ hι hΓ hΓ' (Ne.symm hne) h h')
  have hmemΓ : ∀ (Γ : Mori.PrimeDivisor S) (Q : Mori.PrimeDivisor Γ.idealSheaf.subscheme),
      Γ.idealSheaf.subschemeι.base Q.genericPoint ∈ (Γ.support : Set S) := fun Γ Q => by
    have hr : Set.range Γ.idealSheaf.subschemeι.base = (Γ.support : Set S) :=
      Scheme.IdealSheafData.range_subschemeι _
    rw [← hr]; exact ⟨_, rfl⟩
  refine ⟨Δ, fun c => ⟨by rw [hΔ]; exact hδ0 _, ?_⟩, 2 * m₀, by omega, ⟨m₀, by ring⟩,
    fun c => ?_, ?_⟩
  · -- coefficients `< 1`
    by_cases h : δ (f c) = 0
    · rw [hΔ, h]; norm_num
    have hx : ∃ (Γ : Mori.PrimeDivisor S) (hΓ : B.coeff Γ = 1)
        (Q : Mori.PrimeDivisor Γ.idealSheaf.subscheme),
        Γ.idealSheaf.subschemeι.base Q.genericPoint = f c := by
      by_contra hn
      apply h
      dsimp only [δ]
      rw [dif_neg hn]
    obtain ⟨Γ, hΓ, Q, hQ⟩ := hx
    have huniq : ∀ Γ' : Mori.PrimeDivisor S, B.coeff Γ' = 1 →
        Γ.idealSheaf.subschemeι.base Q.genericPoint ∈ (Γ'.support : Set S) → Γ' = Γ :=
      fun Γ' hΓ' h' => huniqc c Γ Γ' hΓ hΓ' (hQ ▸ hmemΓ Γ Q) (hQ ▸ h')
    rw [hΔ, ← hQ, hδeq Γ hΓ Q huniq]
    exact hBSlt Γ hΓ Q fun Γ' hΓ' hne h' => hne (huniq Γ' hΓ' h')
  · -- `2 m₀ Δ` is integral
    have h1 := hδden (f c)
    rw [hΔ, show ((2 * m₀ : ℕ) : ℚ) * δ (f c) = ((2 * ((m₀ : ℚ) * δ (f c)).num : ℤ) : ℚ) by
      push_cast; rw [Rat.coe_int_num_of_den_eq_one h1]; ring]
    exact Rat.den_intCast _
  -- the residue generators
  intro hC N hfl m hm hrm
  have hme : Even m := (even_two_mul m₀).two_dvd.trans hrm |> even_iff_two_dvd.mpr
  have hCm : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor := by
    obtain ⟨l, hl⟩ := hrm
    have := isCartierDivisor_mul hC₀ (2 * l)
    rwa [show 2 * l * m₀ = m by rw [hl]; ring] at this
  obtain ⟨Dm, hDm, hDmc⟩ := id hCm
  have hGm : Divisor.toQDivisor (Dm - (m : ℤ) • K) = (m : ℚ) • B := by
    rw [map_sub, hDm, map_zsmul, smul_add, add_sub_cancel_left, ← Int.cast_smul_eq_zsmul ℚ]
    push_cast; rfl
  refine ⟨Dm - (m : ℤ) • K, hGm, by rwa [add_sub_cancel], fun x => ?_⟩
  obtain ⟨-, U₀, hxU₀, τ₀, hτ₀⟩ := MMP.Positivity.IsPair.exists_generatesOn hdlt.isPair hK hCm x
  -- generators along the components of `⌊B⌋` through `x`
  have hgenΓ : ∀ (Γ : Mori.PrimeDivisor S) (hΓ : B.coeff Γ = 1), x ∈ (Γ.support : Set S) →
      haveI := Γ.integral
      haveI : IsLocallyNoetherian Γ.idealSheaf.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (Γ.idealSheaf.subschemeι ≫ sS)
      ∃ U : S.Opens, x ∈ U ∧ ∃ τ : RationalPluriForms sS 2 m, GeneratesOn B m U τ ∧
        ∃ ρ : RationalPluriForms (Γ.idealSheaf.subschemeι ≫ sS) 1 m,
          IsPoincareResidue sS Γ.idealSheaf.subschemeι 1 m τ ρ ∧
            GeneratesOn (BS Γ hΓ) m (Γ.idealSheaf.subschemeι ⁻¹ᵁ U) ρ := by
    intro Γ hΓ hx
    haveI := Γ.integral
    have hr : Set.range Γ.idealSheaf.subschemeι.base = (Γ.support : Set S) :=
      Scheme.IdealSheafData.range_subschemeι _
    obtain ⟨y, rfl⟩ : x ∈ Set.range Γ.idealSheaf.subschemeι.base := by rw [hr]; exact hx
    exact (hBSgen Γ hΓ m hm hCm).2 y
  choose UΓ hxUΓ τΓ hτΓ ρΓ hρΓ hρΓg using hgenΓ
  -- the open `V`
  set Z : Set S := ⋃ Γ ∈ B.roundDown.support.filter (fun Γ => x ∉ (Γ.support : Set S)),
    (Γ.support : Set S) with hZdef
  have hZ : IsClosed Z := isClosed_biUnion_finset fun E _ => E.idealSheaf.support.isClosed
  set Wset : Set S := ⋂ Γ ∈ B.roundDown.support.filter (fun Γ => x ∈ (Γ.support : Set S)),
    if h : B.coeff Γ = 1 ∧ x ∈ (Γ.support : Set S) then (UΓ Γ h.1 h.2 : Set S) else Set.univ
    with hWset
  have hWo : IsOpen Wset :=
    isOpen_biInter_finset fun Γ _ => by split_ifs <;> simp [TopologicalSpace.Opens.isOpen]
  let W : S.Opens := ⟨Wset, hWo⟩
  have hmemW : ∀ z, z ∈ W ↔ z ∈ Wset := fun _ => TopologicalSpace.Opens.mem_mk
  let V : S.Opens := U₀ ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩ ⊓ W
  have hmemV : ∀ z, z ∈ V ↔ (z ∈ U₀ ∧ z ∈ Zᶜ) ∧ z ∈ Wset := fun _ =>
    TopologicalSpace.Opens.mem_inf.trans (and_congr (TopologicalSpace.Opens.mem_inf.trans
      (and_congr_right' TopologicalSpace.Opens.mem_mk)) (hmemW _))
  clear_value V W
  have hxV : x ∈ V := by
    refine (hmemV x).2 ⟨⟨hxU₀, fun hz => ?_⟩, ?_⟩
    · simp only [hZdef, Set.mem_iUnion, Finset.mem_filter] at hz
      obtain ⟨Γ, ⟨-, hΓ⟩, hxΓ⟩ := hz
      exact hΓ hxΓ
    · rw [hWset]
      simp only [Set.mem_iInter]
      intro Γ _
      split_ifs with h
      · exact hxUΓ Γ h.1 h.2
      · trivial
  have hVU₀ : V ≤ U₀ := fun z hz => ((hmemV z).1 hz).1.1
  have hVΓ : ∀ (Γ : Mori.PrimeDivisor S) (hΓ : B.coeff Γ = 1) (hx : x ∈ (Γ.support : Set S)),
      V ≤ UΓ Γ hΓ hx := by
    intro Γ hΓ hx z hz
    have hz' := ((hmemV z).1 hz).2
    rw [hWset] at hz'
    simp only [Set.mem_iInter] at hz'
    have := hz' Γ (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr
      ((roundDown_coeff_ne_zero_iff hdlt Γ).mpr hΓ), hx⟩)
    rwa [dif_pos ⟨hΓ, hx⟩] at this
  have hthrough : ∀ Γ : Mori.PrimeDivisor S, B.coeff Γ = 1 →
      ((Γ.support : Set S) ∩ V).Nonempty → x ∈ (Γ.support : Set S) := by
    rintro Γ hΓ ⟨z, hzΓ, hzV⟩
    by_contra hx
    refine ((hmemV z).1 hzV).1.2 ?_
    simp only [hZdef, Set.mem_iUnion, Finset.mem_filter]
    exact ⟨Γ, ⟨Finsupp.mem_support_iff.mpr ((roundDown_coeff_ne_zero_iff hdlt Γ).mpr hΓ), hx⟩,
      hzΓ⟩
  -- the components of the normalization
  haveI hci : ∀ i, IsClosedImmersion (N.n i ≫ ι) := hfl.isClosedImmersion
  have hcomp : ∀ i : N.ι, ∃ (Γ : Mori.PrimeDivisor S) (_ : B.coeff Γ = 1),
      (N.n i ≫ ι).base (genericPoint (N.X i)) = Γ.genericPoint ∧
      ∃ e : N.X i ≅ Γ.idealSheaf.subscheme, e.hom ≫ Γ.idealSheaf.subschemeι = N.n i ≫ ι := by
    intro i
    obtain ⟨Γ, hΓ, hg, e, he⟩ := exists_genericPoint_component hSp hdlt hQ hι N i
    exact ⟨Γ, hΓ, hg, e, he⟩
  choose Γi hΓi hgi ei hei using hcomp
  have hri : ∀ i, Set.range (N.n i ≫ ι).base = ((Γi i).support : Set S) := by
    intro i
    haveI := (Γi i).integral
    rw [← hei i, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      (ConcreteCategory.bijective_of_isIso (ei i).hom.base).2.range_eq, Set.image_univ]
    exact Scheme.IdealSheafData.range_subschemeι _
  have hdim' : topologicalKrullDim S = ((1 : ℕ) : WithBot ℕ∞) + 1 := by rw [hdim]; rfl
  -- the residue of `τ₀` along a component through `x`
  have hres : ∀ i, x ∈ ((Γi i).support : Set S) →
      ∃ ρ : RationalPluriForms ((N.n i ≫ ι) ≫ sS) 1 m,
        IsPoincareResidue sS (N.n i ≫ ι) 1 m τ₀ ρ ∧ ρ ≠ 0 ∧
        ∀ P : Mori.PrimeDivisor (N.X i), (N.n i ≫ ι).base P.genericPoint ∈ V →
          haveI := (Γi i).integral
          ∀ Q : Mori.PrimeDivisor (Γi i).idealSheaf.subscheme,
            (ei i).hom.base P.genericPoint = Q.genericPoint →
            ((P.ordForm ρ : ℤ) : ℚ) = -(m * (BS (Γi i) (hΓi i)).coeff Q) := by
    intro i hx
    haveI := (Γi i).integral
    haveI := isNormal_floor_component hSp hdlt hQ (Γi i) (hΓi i)
    haveI : IsLocallyNoetherian (Γi i).idealSheaf.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian ((Γi i).idealSheaf.subschemeι ≫ sS)
    have hr : Set.range (Γi i).idealSheaf.subschemeι.base = ((Γi i).support : Set S) :=
      Scheme.IdealSheafData.range_subschemeι _
    obtain ⟨y, hy⟩ : x ∈ Set.range (Γi i).idealSheaf.subschemeι.base := by rw [hr]; exact hx
    have hdimT := topologicalKrullDim_eq_of_range_eq_support sS hdim'
      (Γi i).idealSheaf.subschemeι (Γi i) hr
    have htrT := toNat_trdeg_functionField_of_topologicalKrullDim_eq
      (sX := (Γi i).idealSheaf.subschemeι ≫ sS) hdimT
    obtain ⟨ρ₀, hρ₀, hρ₀0, hρ₀ord⟩ := exists_isPoincareResidue_of_generatesOn hdim hGm
      (Γi i).idealSheaf.subschemeι hr hτ₀ (hτΓ (Γi i) (hΓi i) hx) (hρΓ (Γi i) (hΓi i) hx)
      (hρΓg (Γi i) (hΓi i) hx).1 y (by rw [hy]; exact ⟨hxU₀, hxUΓ _ _ hx⟩)
    obtain ⟨ρ₁, hρ₁, hρ₁ord, hρ₁0⟩ := exists_isPoincareResidue_of_iso hdim (N.n i ≫ ι)
      (Γi i).idealSheaf.subschemeι (ei i) (hei i) (Γi i) (subschemeι_genericPoint (Γi i)) htrT hρ₀
    refine ⟨ρ₁, hρ₁, fun h => hρ₀0 (hρ₁0.mp h), fun P hP Q hPQ => ?_⟩
    have hjQ : (Γi i).idealSheaf.subschemeι.base Q.genericPoint = (N.n i ≫ ι).base P.genericPoint := by
      rw [← hPQ, ← Scheme.Hom.comp_apply, hei i]
    have hQV : (Γi i).idealSheaf.subschemeι.base Q.genericPoint ∈ V := hjQ ▸ hP
    rw [hρ₁ord P Q hPQ, hρ₀ord Q ⟨hVU₀ hQV, hVΓ _ _ hx hQV⟩]
    have hgen := (hρΓg (Γi i) (hΓi i) hx).2 Q ⟨Q.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
      hVΓ _ _ hx hQV⟩
    linarith
  -- points of `S` where two components of `⌊B⌋` meet are nodes with a local generator
  have hnodeData : ∀ (Γ Γ' : Mori.PrimeDivisor S), B.coeff Γ = 1 → B.coeff Γ' = 1 → Γ ≠ Γ' →
      ∀ y : S, y ∈ (Γ.support : Set S) → y ∈ (Γ'.support : Set S) → y ∈ V →
      ∃ c : k, ∀ {T : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
        (j : T ⟶ S) [IsClosedImmersion j],
        (Set.range j.base = (Γ.support : Set S) ∨ Set.range j.base = (Γ'.support : Set S)) →
        ∀ (P : Mori.PrimeDivisor T), j.base P.genericPoint = y →
        ∀ {ρ : RationalPluriForms (j ≫ sS) 1 m}, IsPoincareResidue sS j 1 m τ₀ ρ →
          P.ordForm ρ = -(m : ℤ) ∧ (letI := functionFieldAlgebra (j ≫ sS)
            ∃ w : T.functionField, T.ord w P.genericPoint = 1 ∧
              (ρ - algebraMap k T.functionField c • dlogPow (j ≫ sS) w m = 0 ∨
                1 - (m : ℤ) ≤ P.ordForm (ρ - algebraMap k T.functionField c •
                  dlogPow (j ≫ sS) w m))) := by
    intro Γ Γ' hΓ hΓ' hne y hy hy' hyV
    obtain ⟨hys, z, hz, hz0, hz1, hE⟩ :=
      exists_regularParameters_of_mem_floor_inter hSp hdlt hQ hΓ hΓ' hne hy hy'
    have hyne : y ≠ Γ.genericPoint := fun h => hne (eq_of_genericPoint_mem_support (h ▸ hy'))
    have hyc : IsClosed ({y} : Set S) := isClosed_singleton_of_mem_support (sS := sS) hdim Γ hy hyne
    exact exists_leadingCoeff_node hX hdim hys hyc hne hΓ hΓ' hy hy' hz hz0 hz1
      (fun E hE0 hyE => hE E (Finsupp.mem_support_iff.mpr hE0) hyE) hm hme (hVU₀ hyV) hτ₀
  have hmemi : ∀ i (P : Mori.PrimeDivisor (N.X i)),
      ι.base ((N.n i).base P.genericPoint) ∈ ((Γi i).support : Set S) := fun i P => by
    rw [← hri i]; exact ⟨P.genericPoint, rfl⟩
  have hgη : ∀ i, (N.n i ≫ ι).base (genericPoint (N.X i)) = (Γi i).genericPoint := hgi
  refine ⟨V, hxV, τ₀, hτ₀.mono hVU₀, fun i hi => ?_, fun i ρ hi hρ => ?_, ?_⟩
  · -- residues exist
    obtain ⟨ρ, hρ, -⟩ := hres i (hthrough (Γi i) (hΓi i) (hri i ▸ hi))
    exact ⟨ρ, hρ⟩
  · -- residues are nonzero with the orders of the different
    obtain ⟨ρ₁, hρ₁, hρ₁0, hord⟩ := hres i (hthrough (Γi i) (hΓi i) (hri i ▸ hi))
    have hρeq : ρ = ρ₁ := MMP.Fourfold.isPoincareResidue_unique (hgη i) hρ hρ₁
    subst hρeq
    refine ⟨hρ₁0, fun P hP => ?_⟩
    by_cases hdnc : IsDoubleNormalCrossingPoint (ι ≫ sS) 1 ((N.n i).base P.genericPoint)
    · -- a node
      have hcb : N.componentBoundaryCoeff Δ i P = 1 := by
        simp [NormalizationComponents.componentBoundaryCoeff, hdnc]
      obtain ⟨Γ', hΓ', hyΓ', hne⟩ := exists_ne_of_isDoubleNormalCrossingPoint hSp hdlt hQ hι
        (hΓi i) (hmemi i P) hdnc
      obtain ⟨c, H⟩ := hnodeData (Γi i) Γ' (hΓi i) hΓ' (Ne.symm hne) _ (hmemi i P) hyΓ' hP
      have h1 := (H (N.n i ≫ ι) (Or.inl (hri i)) P rfl hρ).1
      rw [hcb, h1]
      push_cast; ring
    · -- a smooth point of the floor
      obtain ⟨c, hc⟩ :=
        exists_weilDivisorPrime_of_not_isDoubleNormalCrossingPoint hSp hdlt hQ hι N i P hdnc
      have hcb : N.componentBoundaryCoeff Δ i P = Δ c := by
        rw [NormalizationComponents.componentBoundaryCoeff, if_neg hdnc]
        exact sum_ite_genericPoint_eq Δ c hc
      haveI := (Γi i).integral
      have hcohQ : Order.coheight ((ei i).hom.base P.genericPoint) = 1 := by
        rw [Topology.IsOpenEmbedding.coheight_eq _ (ei i).hom.isOpenEmbedding]
        exact P.coheight_genericPoint
      set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcohQ
      have hQ : Q.genericPoint = (ei i).hom.base P.genericPoint :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcohQ
      have hjQ : (Γi i).idealSheaf.subschemeι.base Q.genericPoint = f c := by
        rw [hQ, ← Scheme.Hom.comp_apply, hei i]
        change _ = ι.base c.1.genericPoint
        rw [hc]; rfl
      have huniq : ∀ Γ' : Mori.PrimeDivisor S, B.coeff Γ' = 1 →
          (Γi i).idealSheaf.subschemeι.base Q.genericPoint ∈ (Γ'.support : Set S) →
            Γ' = Γi i :=
        fun Γ' hΓ' h' => huniqc c (Γi i) Γ' (hΓi i) hΓ' (hjQ ▸ hmemΓ (Γi i) Q) (hjQ ▸ h')
      rw [hcb, hΔ, ← hjQ, hδeq (Γi i) (hΓi i) Q huniq]
      exact hord P hP Q hQ.symm
  · -- equal leading coefficients at the nodes
    intro i j P P' ρ ρ' hρ hρ' hPP' hPV hdnc hne
    have hij : i ≠ j := by
      rintro rfl
      apply hne
      have : P.genericPoint = P'.genericPoint :=
        (N.n i ≫ ι).isClosedEmbedding.injective (by
          rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hPP'])
      rw [this]
    have hΓij : Γi i ≠ Γi j := by
      intro h
      apply hij
      apply injective_component hSp hdlt hQ hι N
      simp only
      rw [hgη i, hgη j, h]
    have hy' : ι.base ((N.n i).base P.genericPoint) ∈ ((Γi j).support : Set S) := by
      rw [hPP']; exact hmemi j P'
    obtain ⟨c, H⟩ := hnodeData (Γi i) (Γi j) (hΓi i) (hΓi j) hΓij _ (hmemi i P) hy' hPV
    exact ⟨c, (H (N.n i ≫ ι) (Or.inl (hri i)) P rfl hρ).2,
      (H (N.n j ≫ ι) (Or.inr (hri j)) P' (by rw [Scheme.Hom.comp_apply, hPP']) hρ').2⟩

end Geometry

/-- **The geometry of the floor.** For a `ℚ`-factorial projective dlt surface pair `(S, B)` with
reduced floor `C`, there is a boundary `Δ` on `C` making it an slc curve with coefficients `< 1`,
and an even `r > 0` with `rΔ` integral, such that for every normalization of `C` each component
maps to `S` by a closed immersion and for every positive multiple `m` of `r` the divisor
`m(K + B)` is Cartier with residue generators near every point. -/
private theorem exists_isSlcCurve_and_hasResidueGenerators
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {S C : Scheme.{0}} (sS : S ⟶ Spec (.of k))
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [QuasiCompact sS]
    (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (K : Divisor S) (B : QDivisor S)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS)
    (ι : C ⟶ S) [IsClosedImmersion ι] (hι : ι.ker = B.roundDown.suppIdeal) :
    ∃ Δ : QWeilDivisor C, IsSlcCurve (ι ≫ sS) Δ ∧ (∀ Γ, Δ Γ < 1) ∧
      (∀ Γ ∈ Δ.support, ¬ IsDoubleNormalCrossingPoint (ι ≫ sS) 1 Γ.1.genericPoint) ∧
      ∃ r : ℕ, 0 < r ∧ Even r ∧ (∀ Γ, ((r : ℚ) * Δ Γ).den = 1) ∧
      ∀ (hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite)
        (N : NormalizationComponents (ι ≫ sS) hC),
        IsFloorNormalization sS B ι N ∧
        ∀ m : ℕ, 0 < m → r ∣ m →
          ∃ Gm : Divisor S, Divisor.toQDivisor Gm = (m : ℚ) • B ∧
            ((m : ℤ) • K + Gm).IsCartier ∧ HasResidueGenerators sS B ι N Δ m := by
  obtain ⟨Δ, hΔ, r, hr0, hrev, hrden, hgen⟩ := exists_floorDifferent hSp hdlt hQ hι
  refine ⟨Δ, ⟨isNFold_floor hSp hdlt hι, fun x hx hxs =>
      isDoubleNormalCrossingPoint_of_notMem_smoothLocus hSp hdlt hQ hι x hx hxs,
    (isNFold_floor hSp hdlt hι).1, (isNFold_floor hSp hdlt hι).2.1, satisfiesS2_floor hSp hdlt hι,
    fun Γ => hΔ Γ |>.imp_right le_of_lt⟩, fun Γ => (hΔ Γ).2,
    fun Γ _ => not_isDoubleNormalCrossingPoint_of_weilDivisorPrime Γ, r, hr0, hrev, hrden,
    fun hC N => ⟨isFloorNormalization hSp hdlt hQ hι hC N,
      hgen hC N (isFloorNormalization hSp hdlt hQ hι hC N)⟩⟩

/-- **Residue adjunction on the whole floor of a dlt surface pair.** -/
private theorem exists_isSlcCurve_and_isPoincareResidue_of_isDltPair
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {S C : Scheme.{0}} (sS : S ⟶ Spec (.of k))
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [QuasiCompact sS]
    (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (K : Divisor S) (B : QDivisor S)
    (hdlt : IsDltPair sS 2 K B) (hQ : IsQFactorial sS)
    (ι : C ⟶ S) [IsClosedImmersion ι] (hι : ι.ker = B.roundDown.suppIdeal) :
    ∃ Δ : QWeilDivisor C, IsSlcCurve (ι ≫ sS) Δ ∧ (∀ Γ, Δ Γ < 1) ∧
      (∀ Γ ∈ Δ.support, ¬ IsDoubleNormalCrossingPoint (ι ≫ sS) 1 Γ.1.genericPoint) ∧
      ∀ (hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite)
        (N : NormalizationComponents (ι ≫ sS) hC),
        (∀ i, IsClosedImmersion (N.n i ≫ ι)) ∧
        ∃ m₀ : ℕ, 0 < m₀ ∧ Even m₀ ∧ ∀ m : ℕ, 0 < m → m₀ ∣ m →
          (∀ Γ, ((m : ℚ) * Δ Γ).den = 1) ∧
          ∃ Gm : Divisor S, Divisor.toQDivisor Gm = (m : ℚ) • B ∧ ((m : ℤ) • K + Gm).IsCartier ∧
          ∀ U : S.Opens,
            let IsSection : (∀ i : N.ι, RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m) → Prop :=
              fun s =>
                (∀ i (P : Mori.PrimeDivisor (N.X i)), ι.base ((N.n i).base P.genericPoint) ∈ U →
                    s i ≠ 0 →
                    0 ≤ ((P.ordForm (s i) : ℤ) : ℚ) + m * N.componentBoundaryCoeff Δ i P) ∧
                ∀ (i j : N.ι) (P : Mori.PrimeDivisor (N.X i)) (P' : Mori.PrimeDivisor (N.X j)),
                  (N.n i).base P.genericPoint = (N.n j).base P'.genericPoint →
                  ι.base ((N.n i).base P.genericPoint) ∈ U →
                  IsDoubleNormalCrossingPoint (ι ≫ sS) 1 ((N.n i).base P.genericPoint) →
                  (⟨i, P.genericPoint⟩ : Σ i, N.X i) ≠ ⟨j, P'.genericPoint⟩ →
                  ∃ c : k, N.IsLeadingCoeff i P (s i) c ∧ N.IsLeadingCoeff j P' (s j) c
            let IsResidues : RationalPluriForms sS 2 m →
                (∀ i : N.ι, RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m) → Prop :=
              fun τ ρ => ∀ i, (Set.range (N.n i ≫ ι).base ∩ U).Nonempty →
                IsPoincareResidue sS (N.n i ≫ ι) 1 m τ
                  (cast (congrArg (fun f => RationalPluriForms f 1 m)
                    (Category.assoc (N.n i) ι sS).symm) (ρ i))
            (∀ τ ∈ pluricanonicalSections sS 2 m Gm U, ∀ i,
                (Set.range (N.n i ≫ ι).base ∩ U).Nonempty →
                ∃! ρ, IsPoincareResidue sS (N.n i ≫ ι) 1 m τ ρ) ∧
            (∀ τ ∈ pluricanonicalSections sS 2 m Gm U, ∀ ρ, IsResidues τ ρ → IsSection ρ) ∧
            (∀ τ ∈ pluricanonicalSections sS 2 m Gm U,
                IsResidues τ 0 ↔ τ ∈ pluricanonicalSections sS 2 m (Gm - B.roundDown) U) ∧
            (IsAffineOpen U → ∀ s, IsSection s →
                ∃ τ ∈ pluricanonicalSections sS 2 m Gm U, IsResidues τ s) := by
  have hdim : topologicalKrullDim S = 2 := hdlt.1.2.1.topologicalKrullDim_eq
  have : LocallyOfFiniteType sS := hdlt.1.1.1.toLocallyOfFiniteType
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  obtain ⟨Δ, hslc, hlt, hnode, r, hr0, hrev, hrden, hgen⟩ :=
    exists_isSlcCurve_and_hasResidueGenerators sS hSp K B hdlt hQ ι hι
  refine ⟨Δ, hslc, hlt, hnode, fun hC N => ?_⟩
  obtain ⟨hfl, hm⟩ := hgen hC N
  refine ⟨hfl.isClosedImmersion, r, hr0, hrev, fun m hm0 hrm => ?_⟩
  obtain ⟨Gm, hGm, hGmC, hres⟩ := hm m hm0 hrm
  refine ⟨fun Γ => ?_, Gm, hGm, hGmC, fun U => ?_⟩
  · obtain ⟨l, rfl⟩ := hrm
    have h := hrden Γ
    have : ((r * l : ℕ) : ℚ) * Δ Γ = (l : ℤ) * ((r : ℚ) * Δ Γ) := by push_cast; ring
    rw [this, Rat.mul_den, h]
    simp
  intro IsSection IsResidues
  refine ⟨fun τ hτ i hi => existsUnique_isPoincareResidue hdim hfl hGm hres hτ i hi,
    fun τ hτ ρ hρ => isSection_of_isPoincareResidue hdim hfl hGm hres hτ ρ hρ,
    fun τ hτ => isPoincareResidue_zero_iff hdim hfl hGm hdlt.2.1 hres hτ,
    fun hU s hs => exists_isPoincareResidue_of_isAffineOpen hdim hfl hGm hres hU s hs.1 hs.2⟩

end Residue

/-! ### The whole floor of a dlt surface pair carries a relatively semiample adjoint -/

namespace Floor

open CategoryTheory AlgebraicGeometry MMP.Mori Opposite

universe u

/-- The counit of `G^* ⊣ G_*` at `F` is an epimorphism if `G_*` is faithful on maps out of `F`. -/
private theorem epi_counit_of_pushforward_map_injective {X Y : Scheme.{u}} (G : X ⟶ Y) (F : X.Modules)
    (h : ∀ (Q : X.Modules) (g₁ g₂ : F ⟶ Q),
      (Scheme.Modules.pushforward G).map g₁ = (Scheme.Modules.pushforward G).map g₂ → g₁ = g₂) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction G).counit.app F) := by
  set adj := Scheme.Modules.pullbackPushforwardAdjunction G
  constructor
  intro Q g₁ g₂ hg
  have e : ∀ g : F ⟶ Q, adj.homEquiv _ _ (adj.counit.app F ≫ g) =
      (Scheme.Modules.pushforward G).map g := by
    intro g
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      adj.right_triangle_components, Category.id_comp]
  exact h Q g₁ g₂ (by rw [← e, ← e, hg])

private theorem natural_apply {X : Scheme.{u}} {M N : X.Modules} (g : M ⟶ N) {U V : X.Opens} (i : V ⟶ U)
    (x : Γ(M, U)) : N.presheaf.map i.op (g.app U x) = g.app V (M.presheaf.map i.op x) :=
  (ConcreteCategory.congr_hom (g.mapPresheaf.naturality i.op) x).symm

private theorem map_map_apply {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens} (i : V ⟶ U)
    (j : W ⟶ V) (x : Γ(F, U)) :
    F.presheaf.map j.op (F.presheaf.map i.op x) = F.presheaf.map (j ≫ i).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private theorem pushforward_comp_map_injective {T S Z : Scheme.{u}} (ι : T ⟶ S) (f : S ⟶ Z)
    (L : S.Modules)
    (h : ∀ (U : S.Opens) (τ : Γ(L, U)) (t : T), t ∈ ι ⁻¹ᵁ U →
      ∃ (W : T.Opens) (hWU : W ≤ ι ⁻¹ᵁ U) (V : Z.Opens) (hWV : W ≤ (ι ≫ f) ⁻¹ᵁ V)
        (σ : Γ((Scheme.Modules.pullback ι).obj L, (ι ≫ f) ⁻¹ᵁ V)) (a : Γ(T, W)),
        t ∈ W ∧
        ((Scheme.Modules.pullback ι).obj L).presheaf.map (homOfLE hWU).op
          (((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app L).app U τ) =
        a • ((Scheme.Modules.pullback ι).obj L).presheaf.map (homOfLE hWV).op σ)
    (Q : T.Modules) (g₁ g₂ : (Scheme.Modules.pullback ι).obj L ⟶ Q)
    (hg : (Scheme.Modules.pushforward (ι ≫ f)).map g₁ =
      (Scheme.Modules.pushforward (ι ≫ f)).map g₂) : g₁ = g₂ := by
  set adjι := Scheme.Modules.pullbackPushforwardAdjunction ι
  apply (adjι.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  refine AddCommGrpCat.ext fun τ => ?_
  obtain ⟨e, he⟩ : ∃ e : Γ((Scheme.Modules.pullback ι).obj L, ι ⁻¹ᵁ U), (adjι.unit.app L).app U τ = e := ⟨_, rfl⟩
  change g₁.app (ι ⁻¹ᵁ U) ((adjι.unit.app L).app U τ) = g₂.app (ι ⁻¹ᵁ U) ((adjι.unit.app L).app U τ)
  rw [he]
  choose W hWU V hWV σ a hmem heq using h U τ
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨Q.presheaf, Q.isSheaf⟩
    (fun t : (ι ⁻¹ᵁ U : Set T) => W t.1 t.2) (ι ⁻¹ᵁ U) (fun t => homOfLE (hWU t.1 t.2))
    (fun t ht => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨t, ht⟩, hmem t ht⟩) _ _ fun t => ?_
  have hσ : g₁.app ((ι ≫ f) ⁻¹ᵁ V t.1 t.2) (σ t.1 t.2) =
      g₂.app ((ι ≫ f) ⁻¹ᵁ V t.1 t.2) (σ t.1 t.2) :=
    congrArg (fun φ => φ.app (V t.1 t.2) (σ t.1 t.2)) hg
  have heq' := heq t.1 t.2
  rw [he] at heq'
  change Q.presheaf.map (homOfLE (hWU t.1 t.2)).op (g₁.app _ e) =
    Q.presheaf.map (homOfLE (hWU t.1 t.2)).op (g₂.app _ e)
  rw [natural_apply, natural_apply, heq', Scheme.Modules.Hom.app_smul,
    Scheme.Modules.Hom.app_smul, ← natural_apply, ← natural_apply, hσ]

/-- **A section generating `𝒪(D)` at a point generates it nearby.** If `ψ` is a unit of `K(X)` with
`D + div ψ` effective on `U` and of coefficient `0` along every prime divisor through `x`, every
section `τ` of `𝒪_X(D)` near `x` is, on a neighbourhood of `x`, a regular multiple of `ψ`. -/
private theorem exists_eq_smul_divisorialSectionOfUnit {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {D : Divisor X} {U O : X.Opens}
    (ψ : (RationalFunctions X)ˣ)
    (hψ : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ U).Nonempty → 0 ≤ D.coeff P + P.ord ψ)
    {x : X} (hxU : x ∈ U) (hxO : x ∈ O)
    (hψx : ∀ P : MMP.Mori.PrimeDivisor X, x ∈ P.support → D.coeff P + P.ord ψ = 0)
    (τ : Γ(D.divisorialSheaf, O)) :
    ∃ (Ω : X.Opens) (hΩO : Ω ≤ O) (hΩU : Ω ≤ U) (ρ : Γ(X, Ω)), x ∈ Ω ∧
      D.divisorialSheaf.presheaf.map (homOfLE hΩO).op τ =
        ρ • D.divisorialSheaf.presheaf.map (homOfLE hΩU).op
          (MMP.Fourfold.divisorialSectionOfUnit ψ hψ) := by
  classical
  set A : Divisor X := D + principalDivisor ψ with hA
  let A' : Divisor X := A.filter (fun P => x ∉ P.support)
  have hxA' : x ∉ A'.supp := by
    rw [DivisorWithCoeffs.mem_supp_iff]
    rintro ⟨E, hE, hxE⟩
    exact hE (by
      rw [DivisorWithCoeffs.coeff_apply,
        Finsupp.filter_apply_neg (fun P => x ∉ P.support) A (not_not.mpr hxE)])
  let Ω : X.Opens := O ⊓ U ⊓ ⟨(A'.supp : Set X)ᶜ, A'.isClosed_supp.isOpen_compl⟩
  have hxΩ : x ∈ Ω := ⟨⟨hxO, hxU⟩, hxA'⟩
  have hΩO : Ω ≤ O := inf_le_left.trans inf_le_left
  have hΩU : Ω ≤ U := inf_le_left.trans inf_le_right
  have hA0 : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ Ω).Nonempty → D.coeff E + E.ord ψ = 0 := by
    intro E hE
    by_cases hxE : x ∈ E.support
    · exact hψx E hxE
    · by_contra hne
      obtain ⟨z, hzE, hzΩ⟩ := hE
      apply hzΩ.2
      rw [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff]
      refine ⟨E, ?_, hzE⟩
      have hAE : A.coeff E = D.coeff E + E.ord ψ := by
        rw [hA, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.filter_apply_pos (fun P => x ∉ P.support) A hxE,
        ← DivisorWithCoeffs.coeff_apply, hAE]
      exact hne
  let t' : D.divisorialSubmodule O := τ
  let ρfun : ToType ((rationalFunctionsPresheaf X).obj (op Ω)) := fun Z =>
    t'.1 ⟨Z.1, hΩO Z.2⟩ * ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1
  have hρ : (0 : Divisor X).IsDivisorialSection Ω ρfun := by
    intro E hE
    have h1 := t'.2 E (hE.mono (Set.inter_subset_inter_right _ hΩO))
    have h2 : E.OrdGE (D.coeff E) (((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)
        E.component) := Or.inr (by
      rw [E.valuation_component, MMP.Mori.PrimeDivisor.ord_inv, WithZero.exp_le_exp]
      linarith [hA0 E hE])
    have h3 := h1.mul h2
    rw [neg_add_cancel] at h3
    rw [DivisorWithCoeffs.coeff_zero, neg_zero]
    exact h3
  obtain ⟨ρ, hρeq⟩ := hρ.exists_eq
  refine ⟨Ω, hΩO, hΩU, ρ, hxΩ, ?_⟩
  refine Subtype.ext (funext fun Z => ?_)
  have hZ := congrFun hρeq Z
  change t'.1 ⟨Z.1, hΩO Z.2⟩ = X.presheaf.germ Ω _ Z.2 ρ * (ψ : RationalFunctions X) Z.1
  rw [toRationalFunctionsPresheaf_app_apply] at hZ
  rw [hZ]
  simp only [ρfun]
  rw [mul_assoc, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Pi.one_apply,
    mul_one]

/-- **A divisorial sheaf restricted along `ι` is generated over `Z` when it is generated near the
image of every point.** Let `D` be a divisor on a normal integral scheme `S`, `ι : T ⟶ S` and
`f : S ⟶ Z`. Suppose that every `t ∈ T` has an open `V ∋ f(ι t)` of `Z`, a section `σ` of
`ι^* 𝒪_S(D)` over `(ι ≫ f)⁻¹ V` and a unit `ψ` of `K(S)`, defining a section of `𝒪_S(D)` over a
neighbourhood `U ⊆ f⁻¹ V` of `ι t` that generates `𝒪_S(D)` at `ι t`, whose restriction to `T` is
`σ`. Then the counit `(ι ≫ f)^* (ι ≫ f)_* ι^* 𝒪_S(D) ⟶ ι^* 𝒪_S(D)` is an epimorphism. -/
private theorem epi_counit_comp_of_forall_exists {T S Z : Scheme.{u}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] (ι : T ⟶ S) (f : S ⟶ Z) (D : Divisor S)
    (h : ∀ t : T, ∃ (V : Z.Opens)
      (σ : Γ((Scheme.Modules.pullback ι).obj D.divisorialSheaf, (ι ≫ f) ⁻¹ᵁ V))
      (U : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (ψ : (RationalFunctions S)ˣ)
      (hψ : ∀ P : MMP.Mori.PrimeDivisor S, (P.support ∩ U).Nonempty → 0 ≤ D.coeff P + P.ord ψ),
      ι t ∈ U ∧ (∀ P : MMP.Mori.PrimeDivisor S, ι t ∈ P.support → D.coeff P + P.ord ψ = 0) ∧
      ((Scheme.Modules.pullback ι).obj D.divisorialSheaf).presheaf.map
          (homOfLE (fun x hx => hUV hx : ι ⁻¹ᵁ U ≤ (ι ≫ f) ⁻¹ᵁ V)).op σ =
        ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app D.divisorialSheaf).app U
          (MMP.Fourfold.divisorialSectionOfUnit ψ hψ)) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction (ι ≫ f)).counit.app
      ((Scheme.Modules.pullback ι).obj D.divisorialSheaf)) := by
  refine epi_counit_of_pushforward_map_injective _ _ fun Q g₁ g₂ hg => ?_
  refine pushforward_comp_map_injective ι f _ (fun U' τ t ht => ?_) Q g₁ g₂ hg
  obtain ⟨V, σ, U, hUV, ψ, hψ, htU, hψt, hσ⟩ := h t
  obtain ⟨Ω, hΩO, hΩU, ρ, htΩ, hτ⟩ :=
    exists_eq_smul_divisorialSectionOfUnit ψ hψ htU ht hψt τ
  let η : D.divisorialSheaf ⟶ (Scheme.Modules.pushforward ι).obj
      ((Scheme.Modules.pullback ι).obj D.divisorialSheaf) :=
    (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app D.divisorialSheaf
  refine ⟨ι ⁻¹ᵁ Ω, fun x hx => hΩO hx, V, fun x hx => hUV (hΩU hx), σ, ι.app Ω ρ, htΩ, ?_⟩
  have h1 := natural_apply η (homOfLE hΩO) τ
  have h2 := natural_apply η (homOfLE hΩU) (MMP.Fourfold.divisorialSectionOfUnit ψ hψ)
  rw [hτ, Scheme.Modules.Hom.app_smul] at h1
  change ((Scheme.Modules.pullback ι).obj D.divisorialSheaf).presheaf.map _ (η.app U' τ) = _
  refine h1.trans ?_
  rw [← h2]
  change ι.app Ω ρ • ((Scheme.Modules.pullback ι).obj D.divisorialSheaf).presheaf.map
    (homOfLE (fun x hx => hΩU hx : ι ⁻¹ᵁ Ω ≤ ι ⁻¹ᵁ U)).op
    (η.app U (MMP.Fourfold.divisorialSectionOfUnit ψ hψ)) = _
  rw [← hσ, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- **Gluing restrictions to `T`.** Sections `s j` of `L` over opens `U j` of `S` whose
restrictions to `T` agree on the overlaps glue to a section of `ι^* L` over any open `W` of `T`
covered by the `ι⁻¹ U j`. -/
private theorem exists_restrict_eq_unit_app {T S : Scheme.{u}} (ι : T ⟶ S) (L : S.Modules) {J : Type*}
    (U : J → S.Opens) (s : ∀ j, Γ(L, U j)) (W : T.Opens) (hW : W ≤ ⨆ j, ι ⁻¹ᵁ U j)
    (hWj : ∀ j, ι ⁻¹ᵁ U j ≤ W)
    (hcompat : ∀ i j,
      ((Scheme.Modules.pullback ι).obj L).presheaf.map
          (homOfLE (inf_le_left : ι ⁻¹ᵁ U i ⊓ ι ⁻¹ᵁ U j ≤ ι ⁻¹ᵁ U i)).op
          (((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app L).app (U i) (s i)) =
        ((Scheme.Modules.pullback ι).obj L).presheaf.map
          (homOfLE (inf_le_right : ι ⁻¹ᵁ U i ⊓ ι ⁻¹ᵁ U j ≤ ι ⁻¹ᵁ U j)).op
          (((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app L).app (U j) (s j))) :
    ∃ σ : Γ((Scheme.Modules.pullback ι).obj L, W), ∀ j,
      ((Scheme.Modules.pullback ι).obj L).presheaf.map (homOfLE (hWj j)).op σ =
        ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app L).app (U j) (s j) := by
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨((Scheme.Modules.pullback ι).obj L).presheaf, ((Scheme.Modules.pullback ι).obj L).isSheaf⟩ :
      TopCat.Sheaf Ab T) (fun j => ι ⁻¹ᵁ U j) W (fun j => homOfLE (hWj j)) hW
    (fun j => ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app L).app (U j) (s j))
    (fun i j => hcompat i j)
  exact ⟨σ, hσ⟩

section Forms

variable {X : Scheme.{0}} [IsIntegral X]

/-- The unique irreducible component of an integral scheme. -/
private noncomputable def topComponent (X : Scheme.{0}) [IsIntegral X] : irreducibleComponents X :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private theorem subsingleton_irreducibleComponents : Subsingleton (irreducibleComponents X) := by
  rw [irreducibleComponents_eq_singleton]; infer_instance

/-- The image in `k(X)` of a unit of the ring of rational functions `K(X)`. -/
private noncomputable def unitValue (ψ : (RationalFunctions X)ˣ) : X.functionField :=
  (MMP.Positivity.componentToFunctionField (topComponent X)).hom (ψ.val (topComponent X))

private theorem unitValue_mul (ψ φ : (RationalFunctions X)ˣ) :
    unitValue (ψ * φ) = unitValue ψ * unitValue φ := by
  simp [unitValue]

private theorem unitValue_ne_zero (ψ : (RationalFunctions X)ˣ) : unitValue ψ ≠ 0 :=
  ((ψ.isUnit.map (Pi.evalRingHom _ (topComponent X))).map _).ne_zero

variable [IsLocallyNoetherian X] [IsNormal X]

private theorem ord_eq_ord_unitValue (P : MMP.Mori.PrimeDivisor X) (ψ : (RationalFunctions X)ˣ) :
    P.ord ψ = X.ord (unitValue ψ) P.genericPoint := by
  haveI := subsingleton_irreducibleComponents (X := X)
  rw [MMP.Positivity.ord_eq_ord_componentToFunctionField P ψ, unitValue,
    Subsingleton.elim P.component (topComponent X)]

private theorem exists_unitValue_eq {h : X.functionField} (hh : h ≠ 0) :
    ∃ ψ : (RationalFunctions X)ˣ, unitValue ψ = h := by
  obtain ⟨ψ, hψ⟩ := MMP.Mori.PrimeDivisor.exists_units_algebraMap_eq hh
  exact ⟨ψ, hψ (topComponent X)⟩

end Forms

section Orders

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A unit of the local ring at a point `x` has order `0` along every prime divisor through `x`. -/
private theorem ord_algebraMap_eq_zero_of_isUnit {x : X} {b : X.presheaf.stalk x} (hb : IsUnit b)
    (Q : MMP.Mori.PrimeDivisor X) (hQ : x ∈ Q.support) :
    X.ord (algebraMap _ X.functionField b) Q.genericPoint = 0 := by
  have hspec : Q.genericPoint ⤳ x := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hQ
    exact specializes_iff_mem_closure.2 hQ
  set b' := X.presheaf.stalkSpecializes hspec b
  have hb' : IsUnit b' := hb.map _
  have hbb' : algebraMap _ X.functionField b' = algebraMap _ X.functionField b := by
    change (X.presheaf.stalkSpecializes hspec ≫ X.presheaf.stalkSpecializes _).hom b = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  rw [← hbb']
  have hbK : algebraMap _ X.functionField b' ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb'.ne_zero
  rw [Scheme.ord_eq_iff Q.coheight_genericPoint hbK]
  have := Q.isDiscreteValuationRing_localRing
  have hz := Q.coheight_genericPoint
  have : Ring.KrullDimLE 1 (X.presheaf.stalk Q.genericPoint) :=
    krullDimLE_of_coheight_le hz.le
  change Ring.ordFrac _ (algebraMap _ X.functionField b') = _
  rw [Ring.ordFrac_eq_ord _ hb'.ne_zero]
  simp [Ring.ordMonoidWithZeroHom, hb'.mem_nonZeroDivisors, Ring.ord_of_isUnit hb',
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 hb']

end Orders

section ResidueSmul

variable {k : Type} [Field k] {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsIntegral T] {j : T ⟶ Y}

/-- The residue of `b τ`, for `b` in the local ring at the generic point of `T`, is `b̄ Res τ`. -/
private theorem isPoincareResidue_algebraMap_smul {n m : ℕ} {τ : RationalPluriForms sY (n + 1) m}
    {ρ : RationalPluriForms (j ≫ sY) n m} (h : MMP.Fourfold.IsPoincareResidue sY j n m τ ρ)
    (b : Y.presheaf.stalk (j (genericPoint T))) :
    MMP.Fourfold.IsPoincareResidue sY j n m (algebraMap _ Y.functionField b • τ)
      ((j.stalkMap (genericPoint T)).hom b • ρ) := by
  obtain ⟨t, g, x, ht, hτ, hρ⟩ := h
  refine ⟨t, b * g, x, ht, ?_, ?_⟩
  · subst hτ
    rw [map_mul, mul_smul]
    rfl
  · subst hρ
    rw [map_mul, mul_smul]
    rfl

end ResidueSmul

section Values

variable {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]

/-- If `ψ' = ρ ψ` as sections of `𝒪_S(D)` over `Ω`, then `ψ' = ρ ψ` in `k(S)`. -/
private theorem unitValue_eq_of_restrict_eq_smul {D : Divisor S} {U U' Ω : S.Opens}
    {ψ ψ' : (RationalFunctions S)ˣ}
    (hψ : ∀ P : MMP.Mori.PrimeDivisor S, (P.support ∩ U).Nonempty → 0 ≤ D.coeff P + P.ord ψ)
    (hψ' : ∀ P : MMP.Mori.PrimeDivisor S, (P.support ∩ U').Nonempty → 0 ≤ D.coeff P + P.ord ψ')
    (hΩU : Ω ≤ U) (hΩU' : Ω ≤ U') (ρ : Γ(S, Ω)) [Nonempty Ω]
    (h : D.divisorialSheaf.presheaf.map (homOfLE hΩU').op
        (MMP.Fourfold.divisorialSectionOfUnit ψ' hψ') =
      ρ • D.divisorialSheaf.presheaf.map (homOfLE hΩU).op
        (MMP.Fourfold.divisorialSectionOfUnit ψ hψ)) :
    unitValue ψ' = S.germToFunctionField Ω ρ * unitValue ψ := by
  have hgen : componentGenericPoint S (topComponent S) ∈ Ω := by
    rw [genericPoint_mem_iff]
    obtain ⟨⟨z, hz⟩⟩ := (inferInstance : Nonempty Ω)
    exact ⟨z, hz, trivial⟩
  have := congrArg (fun φ : Γ(D.divisorialSheaf, Ω) =>
    (show D.divisorialSubmodule Ω from φ).1 ⟨topComponent S, hgen⟩) h
  change ψ'.val (topComponent S) =
    S.presheaf.germ Ω _ hgen ρ * ψ.val (topComponent S) at this
  rw [unitValue, unitValue, this, map_mul]
  congr 1
  change (S.presheaf.germ Ω _ hgen ≫ S.presheaf.stalkSpecializes _).hom ρ = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

end Values

/-! ### Normalization components -/

section Components

/-- The components of the normalization cover the curve. -/
private theorem exists_n_eq {k : Type} [Field k] {C : Scheme.{0}} {sC : C ⟶ Spec (.of k)}
    {hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite}
    (N : MMP.Flips.NormalizationComponents sC hC) (c : C) :
    ∃ i, ∃ z : N.X i, (N.n i).base z = c := by
  obtain ⟨φ, hφ⟩ := N.exists_iso
  obtain ⟨w, hw⟩ := (Scheme.surjective_normalization C hC).surj c
  obtain ⟨⟨i, z⟩, hz⟩ := (sigmaMk N.X).surjective (φ.inv.base w)
  refine ⟨i, z, ?_⟩
  have h1 : (Limits.Sigma.ι N.X i ≫ Limits.Sigma.desc N.n) = N.n i := Limits.Sigma.ι_desc _ _
  rw [← h1, ← hφ, Scheme.Hom.comp_apply, ← sigmaMk_mk, hz]
  have h2 : (φ.inv ≫ φ.hom ≫ MMP.Flips.slcCurveNormalization C hC) w = c := by
    rw [Iso.inv_hom_id_assoc]; exact hw
  exact h2

/-- A curve of finite type over a field has finitely many normalization components. -/
private theorem finite_ι {k : Type} [Field k] {C : Scheme.{0}} {sC : C ⟶ Spec (.of k)} [LocallyOfFiniteType sC] [CompactSpace C]
    {hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite}
    (N : MMP.Flips.NormalizationComponents sC hC) : Finite N.ι := by
  classical
  obtain ⟨φ, -⟩ := N.exists_iso
  have hfin : IsFinite (MMP.Flips.slcCurveNormalization C hC) := isFinite_normalizationOverField k sC
  haveI : CompactSpace (Stacks.AlgebraicGeometry.Normalization.normalizationScheme C hC) :=
    QuasiCompact.compactSpace_of_compactSpace (MMP.Flips.slcCurveNormalization C hC)
  haveI : CompactSpace (∐ N.X : Scheme) :=
    (Scheme.homeoOfIso φ).symm.compactSpace
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (Set.range (Limits.Sigma.ι N.X i).base)) (fun i => (Limits.Sigma.ι N.X i).isOpenEmbedding.isOpen_range)
    (fun x _ => by
      obtain ⟨⟨i, z⟩, rfl⟩ := (sigmaMk N.X).surjective x
      exact Set.mem_iUnion.2 ⟨i, z, (sigmaMk_mk N.X i z).symm⟩)
  have hmem : ∀ i, i ∈ F := by
    intro i
    obtain ⟨z⟩ := (inferInstance : Nonempty (N.X i))
    obtain ⟨j, hj, hz⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ ((Limits.Sigma.ι N.X i).base z)))
    by_contra hiF
    have hij : i ≠ j := fun h => hiF (h ▸ hj)
    obtain ⟨w, hw⟩ := hz
    have := (sigmaι_eq_iff N.X j i w z).1 hw
    exact hij (congrArg Sigma.fst this).symm
  exact Set.finite_univ_iff.mp ((F.finite_toSet).subset fun i _ => hmem i)

/-- **Normalization components exist.** The normalization of a scheme of finite type over a field
is the disjoint union of the open subschemes on its irreducible components. -/
private theorem nonempty_normalizationComponents {k : Type} [Field k] {C : Scheme.{0}}
    (sC : C ⟶ Spec (.of k)) [LocallyOfFiniteType sC] [IsSeparated sC] [QuasiCompact sC]
    (hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite) :
    Nonempty (MMP.Flips.NormalizationComponents sC hC) := by
  classical
  set T := Stacks.AlgebraicGeometry.Normalization.normalizationScheme C hC with hT
  set ν := MMP.Flips.slcCurveNormalization C hC with hν
  haveI : IsNormal T := Scheme.isNormal_normalizationScheme C hC
  haveI : IsFinite ν := isFinite_normalizationOverField k sC
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (ν ≫ sC)
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace ν
  haveI : IsNoetherian T := {}
  have hfinc : (irreducibleComponents T).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  -- each point lies on a unique component
  have huniq : ∀ (x : T) (Z Z' : irreducibleComponents T), x ∈ Z.1 → x ∈ Z'.1 → Z' = Z := by
    intro x Z Z' hZ hZ'
    obtain ⟨V, hxV, hV⟩ := MMP.Mori.exists_mem_opens_forall_irreducibleComponents_eq hZ
    exact hV Z' ⟨x, hZ', hxV⟩
  let U : irreducibleComponents T → T.Opens := fun Z =>
    ⟨(⋃ Z' ∈ {Z' : irreducibleComponents T | Z' ≠ Z}, (Z'.1 : Set T))ᶜ, by
      refine isOpen_compl_iff.2 ?_
      haveI := hfinc.to_subtype
      exact (Set.toFinite _).isClosed_biUnion fun Z' _ => isClosed_of_mem_irreducibleComponents _ Z'.2⟩
  have hU : ∀ Z, (U Z : Set T) = Z.1 := by
    intro Z
    ext x
    simp only [U, TopologicalSpace.Opens.coe_mk, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq,
      not_exists, not_and]
    constructor
    · intro hx
      obtain ⟨W, hxW⟩ := MMP.Mori.exists_mem_irreducibleComponents x
      by_cases hWZ : W = Z
      · rw [← hWZ]; exact hxW
      · exact absurd hxW (hx W hWZ)
    · intro hx Z' hZ' hxZ'
      exact hZ' (huniq x Z Z' hx hxZ')
  have hint : ∀ Z, IsIntegral (U Z).toScheme := by
    intro Z
    haveI : IsNormal (U Z).toScheme := isNormal_of_isOpenImmersion (U Z).ι
    haveI : IsReduced (U Z).toScheme := by
      haveI : ∀ x : (U Z).toScheme, _root_.IsReduced ((U Z).toScheme.presheaf.stalk x) :=
        fun x => by haveI := IsNormal.stalk_isDomain x; exact isReduced_of_noZeroDivisors
      exact isReduced_of_isReduced_stalk _
    haveI : IrreducibleSpace (U Z) := by
      have h : IsIrreducible ((U Z : Set T)) := by rw [hU]; exact Z.2.1
      exact Subtype.irreducibleSpace h
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  have hcov : ⨆ Z, ((U Z).ι).opensRange = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨W, hxW⟩ := MMP.Mori.exists_mem_irreducibleComponents x
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨W, ?_⟩
    rw [Scheme.Opens.opensRange_ι]
    change x ∈ (U W : Set T)
    rw [hU]; exact hxW
  have hdisj : Pairwise (Function.onFun Disjoint fun Z => ((U Z).ι).opensRange) := by
    intro Z Z' hZZ'
    simp only [Function.onFun, Scheme.Opens.opensRange_ι]
    rw [disjoint_iff, eq_bot_iff]
    intro x ⟨hx, hx'⟩
    change x ∈ (U Z : Set T) at hx
    change x ∈ (U Z' : Set T) at hx'
    rw [hU] at hx hx'
    exact hZZ' (huniq x Z' Z hx' hx)
  obtain ⟨hcol⟩ := nonempty_isColimit_cofanMk_of (fun Z => (U Z).ι) hcov hdisj
  have hiso : IsIso (Limits.Sigma.desc fun Z => (U Z).ι) := by
    have := (Limits.Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Limits.Cofan.mk T fun Z => (U Z).ι)).1 ⟨hcol⟩
    simpa using this
  refine ⟨⟨↥(irreducibleComponents T), fun Z => (U Z).toScheme, fun Z => (U Z).ι ≫ ν,
    fun Z => ⟨?_, isNormal_of_isOpenImmersion (U Z).ι⟩,
    ⟨asIso (Limits.Sigma.desc fun Z => (U Z).ι), ?_⟩⟩⟩
  · haveI := hint Z
    exact {}
  · refine Limits.Sigma.hom_ext _ _ fun Z => ?_
    simp
    rfl

/-- In a Noetherian quasi-sober space, a closed set all of whose points are closed is finite. -/
private theorem finite_of_isClosed_of_forall_isClosed {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] {A : Set X} (hA : IsClosed A)
    (h : ∀ x ∈ A, IsClosed ({x} : Set X)) : A.Finite := by
  obtain ⟨S, hSf, hScl, hSirr, rfl⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hA
  refine hSf.sUnion fun t ht => ?_
  have hg := (hSirr t ht).isGenericPoint_genericPoint (hScl t ht)
  have hgt : (hSirr t ht).genericPoint ∈ t := hg.mem
  have hcl := h _ (Set.mem_sUnion_of_mem hgt ht)
  rw [← hg.def, hcl.closure_eq]
  exact Set.finite_singleton _

/-- On an integral scheme of dimension one, a closed set missing the generic point is finite. -/
private theorem finite_of_isClosed_of_genericPoint_notMem {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X] (hdim : topologicalKrullDim X = 1) {A : Set X}
    (hA : IsClosed A) (hη : genericPoint X ∉ A) : A.Finite := by
  haveI : IsNoetherian X := {}
  exact finite_of_isClosed_of_forall_isClosed hA fun x hx =>
    Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint X hdim
      fun h => hη (h ▸ hx)

/-- A scheme of finite type over a field of dimension one has infinitely many prime divisors. -/
private theorem infinite_primeDivisor {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType sX] [CompactSpace X]
    (hdim : topologicalKrullDim X = 1) : Infinite (MMP.Mori.PrimeDivisor X) := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hsub : closedPoints X ⊆
      Set.range (fun P : MMP.Mori.PrimeDivisor X => P.genericPoint) ∪ {genericPoint X} := by
    intro x _
    by_cases hx : x = genericPoint X
    · exact Or.inr hx
    · exact Or.inl ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x
        (MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hdim hx),
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _⟩
  have hfinc : (closedPoints X).Finite :=
    ((Set.finite_range _).union (Set.finite_singleton _)).subset hsub
  have hcl : IsClosed (closedPoints X) := by
    rw [← Set.biUnion_of_singleton (closedPoints X)]
    exact hfinc.isClosed_biUnion fun x hx => hx
  have huniv : closedPoints X = Set.univ := by
    rw [← hcl.closure_eq, closure_closedPoints]
  have hη : IsClosed ({genericPoint X} : Set X) := by
    have : genericPoint X ∈ closedPoints X := huniv ▸ Set.mem_univ _
    exact this
  have hsing : ∀ x : X, x = genericPoint X := fun x => by
    have h1 : x ∈ closure ({genericPoint X} : Set X) := by
      rw [(genericPoint_spec X).def]; trivial
    rwa [hη.closure_eq] at h1
  haveI : Subsingleton X := ⟨fun a b => (hsing a).trans (hsing b).symm⟩
  have h0 := Order.krullDim_nonpos_of_subsingleton (α := X)
  rw [Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim, hdim] at h0
  exact absurd h0 (by decide)

/-- The image of the generic point of a normalization component lies in every dense open set. -/
private theorem map_genericPoint_mem_of_dense {k : Type} [Field k] {C : Scheme.{0}}
    {sC : C ⟶ Spec (.of k)} [CompactSpace C] [IsLocallyNoetherian C]
    {hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite}
    (N : MMP.Flips.NormalizationComponents sC hC) (i : N.ι) {O : Set C} (hO : IsOpen O)
    (hd : Dense O) : (N.n i).base (genericPoint (N.X i)) ∈ O := by
  classical
  haveI : IsNoetherian C := {}
  obtain ⟨x, hx⟩ := MMP.Flips.NormalizationComponents.exists_point_generic N i
  set g := (N.n i).base x
  have hW : closure {g} ∈ irreducibleComponents C := hx
  have hfin : (irreducibleComponents C).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  set V : Set C := (⋃ W ∈ {W : Set C | W ∈ irreducibleComponents C ∧ W ≠ closure {g}}, W)ᶜ
  have hVo : IsOpen V :=
    isOpen_compl_iff.2 ((hfin.subset fun W hW => hW.1).isClosed_biUnion fun W hW =>
      isClosed_of_mem_irreducibleComponents W hW.1)
  have hcomp : ∀ W ∈ irreducibleComponents C, g ∈ W → W = closure {g} := by
    intro W hWc hgW
    have h1 : closure {g} ⊆ W :=
      (isClosed_of_mem_irreducibleComponents W hWc).closure_subset_iff.2
        (Set.singleton_subset_iff.2 hgW)
    exact le_antisymm (hW.2 hWc.1 h1) h1
  have hgV : g ∈ V := by
    intro hg
    obtain ⟨W, hWc, hgW⟩ := Set.mem_iUnion₂.1 hg
    exact hWc.2 (hcomp W hWc.1 hgW)
  obtain ⟨y, hyV, hyO⟩ := hd.inter_open_nonempty V hVo ⟨g, hgV⟩
  obtain ⟨W', hW', hyW'⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {y}
    isIrreducible_singleton
  have hW'eq : W' = closure {g} := by
    by_contra hne
    exact hyV (Set.mem_iUnion₂.2 ⟨W', ⟨hW', hne⟩, hyW' rfl⟩)
  have hgy : g ⤳ y := specializes_iff_mem_closure.2 (hW'eq ▸ hyW' rfl)
  have hgO : g ∈ O := hgy.mem_open hO hyO
  exact ((genericPoint_specializes x).map (N.n i).base.hom.continuous).mem_open hO hgO

/-- On a component not contracted by `g`, only finitely many prime divisors lie over a closed
point. -/
private theorem finite_setOf_map_eq {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [CompactSpace X] (hdim : topologicalKrullDim X = 1) (g : X ⟶ Z) {p : Z}
    (hp : IsClosed ({p} : Set Z)) (hnc : ¬ ∀ x, g.base x = g.base (genericPoint X)) :
    {P : MMP.Mori.PrimeDivisor X | g.base P.genericPoint = p}.Finite := by
  have hA : IsClosed (g.base ⁻¹' {p}) := hp.preimage g.base.hom.continuous
  have hη : genericPoint X ∉ g.base ⁻¹' {p} := by
    intro hη
    apply hnc
    intro x
    have hx : x ∈ g.base ⁻¹' {p} := by
      have h1 : closure ({genericPoint X} : Set X) ⊆ g.base ⁻¹' {p} :=
        hA.closure_subset_iff.2 (Set.singleton_subset_iff.2 hη)
      rw [(genericPoint_spec X).def] at h1
      exact h1 trivial
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx hη
    rw [hx, hη]
  exact (finite_of_isClosed_of_genericPoint_notMem hdim hA hη).preimage
    (fun a _ b _ h => AlgebraicGeometry.PrimeDivisor.genericPoint_injective h)

end Components

/-! ### Sections on one smooth proper curve -/

section CurveSections

variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- Every prime divisor of a normal integral scheme has a uniformizer. -/
private theorem exists_ord_genericPoint_eq_one (E : MMP.Mori.PrimeDivisor X) :
    ∃ t : X.functionField, X.ord t E.genericPoint = 1 := by
  have := E.isDiscreteValuationRing_localRing
  have h1 := E.coheight_genericPoint
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le h1.le
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  have hne : algebraMap E.localRing X.functionField ϖ ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero))
  refine ⟨algebraMap E.localRing X.functionField ϖ, ?_⟩
  rw [Scheme.ord_eq_iff h1 hne]
  exact Ring.ordFrac_irreducible hϖ

/-- **Genus one, no boundary.** On a smooth proper curve of genus one, `𝒪(nK)` has a section
without zeros. -/
private theorem exists_section_of_genus_one (hC : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) (hp : IsProper sX) (hdim : topologicalKrullDim X = 1)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 1) (hg : K.h0 k sX = 1) (n : ℕ)
    (Q : MMP.Mori.PrimeDivisor X) :
    ∃ s : RationalPluriForms sX 1 (n : ℕ), s ≠ 0 ∧
      ∀ P : MMP.Mori.PrimeDivisor X, P.ordForm s = 0 := by
  classical
  have : LocallyOfFiniteType sX := hC.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hC.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI := subsingleton_irreducibleComponents (X := X)
  -- a nonzero section of `𝒪(K)`
  obtain ⟨φ, hφ0⟩ : ∃ φ : K.divisorialSubmodule ⊤, φ ≠ 0 := by
    by_contra h
    push Not at h
    have hsub : Subsingleton (K.divisorialSubmodule ⊤) := ⟨fun a b => (h a).trans (h b).symm⟩
    letI : Module k (K.divisorialSubmodule ⊤) :=
      Module.compHom _ (MMP.Mori.scalarsToGlobalSections k sX)
    have h0 : Module.finrank k (K.divisorialSubmodule ⊤) = 0 :=
      Module.finrank_zero_of_subsingleton
    have h1 : K.h0 k sX = 0 := h0
    omega
  have hmem : componentGenericPoint X (topComponent X) ∈ (⊤ : X.Opens) := trivial
  set c := φ.1 ⟨topComponent X, hmem⟩ with hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply hφ0
    refine Subtype.ext (funext fun Z => ?_)
    have : Z = ⟨topComponent X, hmem⟩ := Subtype.ext (Subsingleton.elim _ _)
    rw [this]
    exact h0
  letI := (RationalFunctions.isField_stalk X (topComponent X)).toField
  have hf0 : (MMP.Positivity.componentToFunctionField (topComponent X)).hom c ≠ 0 :=
    (map_ne_zero _).2 hc0
  obtain ⟨ψ, hψ⟩ := exists_unitValue_eq hf0
  have hψc : ψ.val (topComponent X) = c :=
    (MMP.Positivity.componentToFunctionField (topComponent X)).hom.injective hψ
  -- `div ψ + K ≥ 0`
  have hge : ∀ P : MMP.Mori.PrimeDivisor X, 0 ≤ P.ord ψ + K.coeff P := by
    intro P
    have hP : (P.support ∩ (⊤ : X.Opens)).Nonempty :=
      ⟨P.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, trivial⟩
    have h := φ.2 P hP
    have hcomp : P.component = topComponent X := Subsingleton.elim _ _
    have key : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ (⊤ : X.Opens)),
        Z = topComponent X → φ.1 ⟨Z, hZ⟩ = (ψ : RationalFunctions X) Z := by
      rintro Z hZ rfl
      exact hψc.symm
    have hval := key P.component (P.componentGenericPoint_mem_of_nonempty hP) hcomp
    rw [hval] at h
    rcases h with h | h
    · exact absurd h (ψ.isUnit.map (Pi.evalRingHom _ P.component)).ne_zero
    · rw [P.valuation_component, WithZero.exp_le_exp] at h
      omega
  -- the divisor `div ψ + K` is effective of degree `0`, hence zero
  have hdK : (K.sum fun _ a => (a : ℚ)) = 0 := by
    rw [MMP.Flips.sum_coeff_canonical_eq hC hsm hp hK, hg]; norm_num
  have hsum := MMP.Flips.sum_principalDivisor_eq_zero hC hsm hp hdim ψ
  set E : Divisor X := principalDivisor ψ + K with hE
  have hEc : ∀ P, E.coeff P = P.ord ψ + K.coeff P := fun P => by
    rw [hE, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  have hEsum : (E.sum fun _ a => a) = 0 := by
    have hK0 : (K.sum fun _ a => a) = 0 := by
      have : ((K.sum fun _ a => a : ℤ) : ℚ) = 0 := by rw [← hdK]; simp [Finsupp.sum]
      exact_mod_cast this
    rw [hE, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hsum, hK0, add_zero]
  have hE0 : ∀ P, E.coeff P = 0 := by
    intro P
    by_cases hP : P ∈ E.support
    · exact (Finset.sum_eq_zero_iff_of_nonneg (fun Q _ => by rw [← DivisorWithCoeffs.coeff_apply, hEc]; exact hge Q)).1
        hEsum P hP
    · exact Finsupp.notMem_support_iff.1 hP
  obtain ⟨θ, hθ0, hθ⟩ := MMP.Flips.exists_ordForm_eq_mul_coeff hC hK Q n
  refine ⟨unitValue (ψ ^ n) • θ, smul_ne_zero (unitValue_ne_zero _) hθ0, fun P => ?_⟩
  rw [P.ordForm_smul_of_topologicalKrullDim_eq (d := 1) (by rw [hdim]; rfl)
    (unitValue_ne_zero _) hθ0, ← ord_eq_ord_unitValue, MMP.Mori.PrimeDivisor.ord_pow, hθ]
  have := hE0 P
  rw [hEc] at this
  simp only [nsmul_eq_mul]
  rw [← mul_add, show P.ord ψ + K.coeff P = 0 from this, mul_zero]

/-- **Sections with leading coefficient one along the floor.** On a smooth proper curve with
`deg(K + Δ) ≥ 0`, `Δ` a boundary and `mΔ = G''` integral, there is a nonzero section of
`𝒪(24m(K + Δ))` whose leading coefficient is `1` at every point of coefficient one of `Δ` and
which has exact order at every point of a finite set `R`. -/
private theorem exists_curveSection (hC : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    (hp : IsProper sX) (hdim : topologicalKrullDim X = 1) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 1) {m : ℕ} (hm : 0 < m) {Δ : QDivisor X}
    (hΔ0 : Δ.IsEffective) (hΔ1 : ∀ P, Δ.coeff P ≤ 1) {G'' : Divisor X}
    (hG'' : Divisor.toQDivisor G'' = (m : ℤ) • Δ)
    (hdeg : 0 ≤ (K.sum fun _ a => (a : ℚ)) + Δ.sum fun _ a => a)
    (R : Finset (MMP.Mori.PrimeDivisor X)) (hR : R.Nonempty) :
    ∃ s : RationalPluriForms sX 1 (24 * m : ℕ), s ≠ 0 ∧
      s ∈ pluricanonicalSections sX 1 (24 * m : ℕ) ((24 : ℤ) • G'') ⊤ ∧
      (∀ P, 1 ≤ Δ.coeff P → ∃ z : X.functionField, X.ord z P.genericPoint = 1 ∧
        (s - MMP.Flips.dlogPow sX z (24 * m) = 0 ∨
          1 - ((24 * m : ℕ) : ℤ) ≤ P.ordForm (s - MMP.Flips.dlogPow sX z (24 * m)))) ∧
      ∀ P ∈ R, P.ordForm s + ((24 : ℤ) • G'').coeff P = 0 := by
  classical
  -- `G''` has coefficient `m` at the points of coefficient one
  have hGc : ∀ P, ((G''.coeff P : ℤ) : ℚ) = m * Δ.coeff P := fun P => by
    have := congrArg (fun D => DivisorWithCoeffs.coeff D P) hG''
    simpa [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] using this
  have h24 : ∀ P, 1 ≤ Δ.coeff P → ((24 : ℤ) • G'').coeff P = ((24 * m : ℕ) : ℤ) := by
    intro P hP
    have h1 : Δ.coeff P = 1 := le_antisymm (hΔ1 P) hP
    have h2 : ((G''.coeff P : ℤ) : ℚ) = ((m : ℤ) : ℚ) := by rw [hGc, h1]; push_cast; ring
    have h3 : G''.coeff P = m := by exact_mod_cast h2
    simp [DivisorWithCoeffs.coeff_apply] at h3 ⊢
    omega
  have htop : (⊤ : X.Opens) ≠ ⊥ := fun h => by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [h] at hx; exact hx
  rcases hdeg.lt_or_eq with hpos | hzero
  · choose z hz using fun P : MMP.Mori.PrimeDivisor X => exists_ord_genericPoint_eq_one P
    obtain ⟨s, hs, hvan, hR'⟩ :=
      MMP.Flips.NormalizationComponents.exists_mem_pluricanonicalSections_sub_dlogPow_of_proper_pos
        hC hsm hp hK hm hΔ0 hΔ1 hG'' hpos z hz R
    obtain ⟨P₀, hP₀⟩ := hR
    refine ⟨s, (hR' P₀ hP₀).1, hs, fun P hP => ⟨z P, hz P, ?_⟩, fun P hP => (hR' P hP).2⟩
    rcases hvan P hP with h | h
    · exact Or.inl h
    · right; rw [h24 P hP] at h; omega
  · have hbd : (MMP.Fourfold.QDivisor.toQWeilDivisor Δ).IsBoundary sX := by
      refine ⟨⟨hC.1.toIsSeparated, hC.1.toLocallyOfFiniteType, hC.1.toQuasiCompact⟩,
        inferInstance, ?_, fun Γ => ⟨hΔ0 Γ.1, hΔ1 Γ.1⟩⟩
      exact MMP.Flips.satisfiesS2_iff_forall_min_le_depth.mpr
        ((isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one X).mp inferInstance).1
    have hsumW : (MMP.Fourfold.QDivisor.toQWeilDivisor Δ).sum (fun _ a => a) =
        Δ.sum (fun _ a => a) :=
      Finsupp.sum_subtypeDomain_index (h := fun _ a => a)
        fun Γ _ => ⟨inferInstance, Γ.isDiscreteValuationRing_localRing⟩
    have hdeg' : (K.sum fun _ a => (a : ℚ)) +
        (MMP.Fourfold.QDivisor.toQWeilDivisor Δ).sum (fun _ a => a) = 0 := by
      rw [hsumW]; exact hzero.symm
    rcases hbd.degree_zero_curve_types hC hsm hp hK hdeg' with ⟨hg, hΔ0'⟩ | ⟨hg, hΔ2, -⟩
    · obtain rfl : Δ = 0 := MMP.Fourfold.QDivisor.toQWeilDivisor_injective (by rw [hΔ0']; rfl)
      have hG0 : ∀ P, ((24 : ℤ) • G'').coeff P = 0 := fun P => by
        have h := hGc P
        simp only [DivisorWithCoeffs.coeff_zero, mul_zero] at h
        have : G''.coeff P = 0 := by exact_mod_cast h
        simp [DivisorWithCoeffs.coeff_apply] at this ⊢
        omega
      obtain ⟨s, hs0, hs⟩ := exists_section_of_genus_one hC hsm hp hdim hK hg (24 * m) hR.choose
      refine ⟨s, hs0, (mem_pluricanonicalSections_of_ne_bot htop).2 fun Q _ _ => by
          rw [hs Q, hG0 Q]; rfl, fun P hP => ?_, fun P _ => by rw [hs P, hG0 P]; rfl⟩
      simp only [DivisorWithCoeffs.coeff_zero] at hP
      norm_num at hP
    · have hG' : Divisor.toQDivisor ((2 : ℤ) • G'') = ((2 * m : ℕ) : ℤ) • Δ := by
        rw [map_zsmul, hG'', smul_smul]; push_cast; ring_nf
      obtain ⟨s, hs0, hsP, hsF⟩ := MMP.Flips.exists_ordForm_add_eq_zero_of_genus_zero sX hC hsm
        hp hdim hK hbd hG' hg hΔ2
      have e24 : (12 : ℕ) • (2 : ℤ) • G'' = (24 : ℤ) • G'' := by
        rw [← Nat.cast_smul_eq_nsmul ℤ, smul_smul]; norm_num
      rw [e24] at hsP hsF
      rw [show 24 * m = 12 * (2 * m) by ring]
      refine ⟨s, hs0, (mem_pluricanonicalSections_of_ne_bot htop).2 fun Q _ _ => by
          have := hsP Q; omega, fun P hP => ?_, fun P _ => hsP P⟩
      obtain ⟨w, hw, hw'⟩ := hsF P hP
      refine ⟨w, hw, hw'.imp id fun h => ?_⟩
      rw [h24 P hP] at h
      push_cast at h ⊢
      omega

end CurveSections

/-! ### The residue dictionary of the floor -/

section ResidueData

variable {k : Type} [Field k] {S C : Scheme.{0}} (sS : S ⟶ Spec (.of k)) [IsIntegral S]
  [IsLocallyNoetherian S] (ι : C ⟶ S)
  {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
  (N : MMP.Flips.NormalizationComponents (ι ≫ sS) hC)

/-- A family of forms on the components of the normalization of `C` is a section of
`ω_C^{⊗m}(mΔ)` over `C ∩ U`: bounded poles at the points over `U`, and equal leading coefficients
at the two branches of every node over `U`. -/
private def IsResSection (Δ : MMP.Flips.QWeilDivisor C) (m : ℕ) (U : S.Opens)
    (s : ∀ i : N.ι, RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m) : Prop :=
  (∀ i (P : MMP.Mori.PrimeDivisor (N.X i)), ι.base ((N.n i).base P.genericPoint) ∈ U →
      s i ≠ 0 → 0 ≤ ((P.ordForm (s i) : ℤ) : ℚ) + m * N.componentBoundaryCoeff Δ i P) ∧
    ∀ (i j : N.ι) (P : MMP.Mori.PrimeDivisor (N.X i)) (P' : MMP.Mori.PrimeDivisor (N.X j)),
      (N.n i).base P.genericPoint = (N.n j).base P'.genericPoint →
      ι.base ((N.n i).base P.genericPoint) ∈ U →
      MMP.Flips.IsDoubleNormalCrossingPoint (ι ≫ sS) 1 ((N.n i).base P.genericPoint) →
      (⟨i, P.genericPoint⟩ : Σ i, N.X i) ≠ ⟨j, P'.genericPoint⟩ →
      ∃ c : k, N.IsLeadingCoeff i P (s i) c ∧ N.IsLeadingCoeff j P' (s j) c

/-- `ρ` is the family of Poincaré residues of `τ` along the components meeting `U`. -/
private def IsResidues (m : ℕ) (U : S.Opens) (τ : RationalPluriForms sS 2 m)
    (ρ : ∀ i : N.ι, RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m) : Prop :=
  ∀ i, (Set.range (N.n i ≫ ι).base ∩ U).Nonempty →
    MMP.Fourfold.IsPoincareResidue sS (N.n i ≫ ι) 1 m τ
      (cast (congrArg (fun f => RationalPluriForms f 1 m)
        (Category.assoc (N.n i) ι sS).symm) (ρ i))

/-- `y` is a *good point* for the family `s`: on every component through `y`, `s` is nonzero of
exact order at the point over `y`. -/
private def IsGoodPoint (Δ : MMP.Flips.QWeilDivisor C) (m : ℕ)
    (s : ∀ i : N.ι, RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m) (y : C) : Prop :=
  ∀ i (z : N.X i), (N.n i).base z = y → ∃ P : MMP.Mori.PrimeDivisor (N.X i),
    P.genericPoint = z ∧ s i ≠ 0 ∧
      ((P.ordForm (s i) : ℤ) : ℚ) + m * N.componentBoundaryCoeff Δ i P = 0

variable {sS ι N} in
private theorem IsResSection.mono {Δ : MMP.Flips.QWeilDivisor C} {m : ℕ} {U V : S.Opens}
    (hVU : V ≤ U) {s : ∀ i : N.ι, RationalPluriForms (N.n i ≫ ι ≫ sS) 1 m}
    (h : IsResSection sS ι N Δ m U s) : IsResSection sS ι N Δ m V s :=
  ⟨fun i P hP => h.1 i P (hVU hP), fun i j P P' h1 hP => h.2 i j P P' h1 (hVU hP)⟩

end ResidueData

section Multiples

/-- On an integral scheme of dimension `d`, the rational `m`-canonical forms of degree `d` are a
line over `k(X)`: every form is a multiple of a given nonzero one. -/
private theorem exists_eq_smul_of_ne_zero {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d) {m : ℤ} {u : RationalPluriForms sX d m} (hu : u ≠ 0)
    (w : RationalPluriForms sX d m) : ∃ h : X.functionField, w = h • u := by
  let := functionFieldAlgebra sX
  obtain ⟨b⟩ := MMP.Fourfold.exists_basis_topForms (sX := sX) hd
  let B := ZTensorPower.basis b m
  have hu' := basis_unit_repr_smul B u
  have hw' := basis_unit_repr_smul B w
  have hru : B.repr u () ≠ 0 := by
    intro h; rw [h, zero_smul] at hu'; exact hu hu'.symm
  refine ⟨B.repr w () / B.repr u (), ?_⟩
  have key : (B.repr w () / B.repr u ()) • (B.repr u () • B ()) = B.repr w () • B () := by
    rw [smul_smul, div_mul_cancel₀ _ hru]
  rw [hu'] at key
  exact hw'.symm.trans key.symm

end Multiples

section Generation

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {S C : Scheme.{0}}
  {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
  [LocallyOfFiniteType sS] {ι : C ⟶ S}
  {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
  {N : MMP.Flips.NormalizationComponents (ι ≫ sS) hC}

private theorem mem_pluricanonicalSections_of_le {d : ℕ} {m : ℤ} {G : Divisor S} {U V : S.Opens}
    (hVU : V ≤ U) {τ : RationalPluriForms sS d m} (hτ : τ ∈ pluricanonicalSections sS d m G U)
    (hV : V ≠ ⊥) : τ ∈ pluricanonicalSections sS d m G V :=
  (mem_pluricanonicalSections_of_ne_bot hV).2 fun Γ hΓ hτ0 =>
    hτ.2 Γ (hΓ.mono (Set.inter_subset_inter_right _ hVU)) hτ0

private theorem ordForm_unitValue_smul (hdimS : topologicalKrullDim S = 2) {M : ℕ}
    {θ : RationalPluriForms sS 2 M} (hθ0 : θ ≠ 0) (ψ : (RationalFunctions S)ˣ)
    (Γ : MMP.Mori.PrimeDivisor S) :
    Γ.ordForm (unitValue ψ • θ) = Γ.ord ψ + Γ.ordForm θ := by
  rw [Γ.ordForm_smul_of_topologicalKrullDim_eq (d := 2) (by rw [hdimS]; rfl)
    (unitValue_ne_zero ψ) hθ0, ord_eq_ord_unitValue]

/-- If `φ` is a local equation of `MK + G` on `U` and `θ` has divisor `MK`, then `φ⁻¹ θ` is a
section of `𝒪_S(MK + G)` over `U`. -/
private theorem unitValue_inv_smul_mem_pluricanonicalSections (hdimS : topologicalKrullDim S = 2)
    {M : ℕ} {K Gm : Divisor S} {θ : RationalPluriForms sS 2 M} (hθ0 : θ ≠ 0)
    (hθ : ∀ Γ : MMP.Mori.PrimeDivisor S, Γ.ordForm θ = M * K.coeff Γ) {U : S.Opens}
    (hU : U ≠ ⊥) {φ : (RationalFunctions S)ˣ} (hφ : ((M : ℤ) • K + Gm).IsLocalEquation U φ) :
    unitValue φ⁻¹ • θ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U := by
  refine (mem_pluricanonicalSections_of_ne_bot hU).2 fun Γ hΓ _ => ?_
  rw [ordForm_unitValue_smul hdimS hθ0, MMP.Mori.PrimeDivisor.ord_inv, ← hφ Γ hΓ, hθ]
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  omega

/-- A form with a nonzero Poincaré residue is a unit multiple `ψ θ` of a given nonzero form. -/
private theorem exists_eq_unitValue_smul_of_isPoincareResidue
    (hdimS : topologicalKrullDim S = 2) {M : ℕ} {θ : RationalPluriForms sS 2 M} (hθ0 : θ ≠ 0)
    {T : Scheme.{0}} [IsIntegral T] {j : T ⟶ S} {τ : RationalPluriForms sS 2 M}
    {ρ : RationalPluriForms (j ≫ sS) 1 M} (h : MMP.Fourfold.IsPoincareResidue sS j 1 M τ ρ)
    (hu : ∃! ρ, MMP.Fourfold.IsPoincareResidue sS j 1 M τ ρ) (hρ : ρ ≠ 0) :
    ∃ ψ : (RationalFunctions S)ˣ, τ = unitValue ψ • θ := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    exact hρ (hu.unique h (by simpa using isPoincareResidue_algebraMap_smul h 0))
  obtain ⟨g, rfl⟩ := exists_eq_smul_of_ne_zero (d := 2) (by rw [hdimS]; rfl) hθ0 τ
  obtain ⟨ψ, rfl⟩ := exists_unitValue_eq (left_ne_zero_of_smul hτ0)
  exact ⟨ψ, rfl⟩

/-- The residues of a section of `𝒪_S(MK + G)` over `U` form a section of `ω_C^{⊗M}(MΔ)`. -/
private theorem exists_isResidues_isResSection {Δ : MMP.Flips.QWeilDivisor C} {M : ℕ}
    {Gm : Divisor S}
    (hres1 : ∀ U : S.Opens, ∀ τ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U, ∀ i,
      (Set.range (N.n i ≫ ι).base ∩ U).Nonempty →
      ∃! ρ, MMP.Fourfold.IsPoincareResidue sS (N.n i ≫ ι) 1 M τ ρ)
    (hres2 : ∀ U : S.Opens, ∀ τ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U, ∀ ρ,
      IsResidues sS ι N M U τ ρ → IsResSection sS ι N Δ M U ρ)
    {U : S.Opens} {τ : RationalPluriForms sS 2 M}
    (hτ : τ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U) :
    ∃ ρ, IsResidues sS ι N M U τ ρ ∧ IsResSection sS ι N Δ M U ρ := by
  have hex : ∀ i, ∃ ρ : RationalPluriForms (N.n i ≫ ι ≫ sS) 1 M,
      (Set.range (N.n i ≫ ι).base ∩ U).Nonempty →
        MMP.Fourfold.IsPoincareResidue sS (N.n i ≫ ι) 1 M τ ρ := fun i => by
    by_cases h : (Set.range (N.n i ≫ ι).base ∩ U).Nonempty
    · exact ⟨_, fun _ => (hres1 U τ hτ i h).exists.choose_spec⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose ρ hρ using hex
  exact ⟨ρ, hρ, hres2 U τ hτ ρ hρ⟩

/-- **A section whose residue has exact order generates.** Let `τ = ψ θ` be a section of
`𝒪_S(MK + G_M)` over `U` whose residues `s` along the components of the floor have, on some
component, exact order at a point `P` over `x ∈ U`. Then `ψ` generates `𝒪_S(MK + G_M)` at `x`. -/
private theorem coeff_add_ord_eq_zero_of_isResidues
    (hdimX : ∀ i, topologicalKrullDim (N.X i) = 1) (hdimS : topologicalKrullDim S = 2)
    {Δ : MMP.Flips.QWeilDivisor C} {M : ℕ} {K Gm : Divisor S} {θ : RationalPluriForms sS 2 M}
    (hθ0 : θ ≠ 0) (hθ : ∀ Γ : MMP.Mori.PrimeDivisor S, Γ.ordForm θ = M * K.coeff Γ)
    (hcart : ((M : ℤ) • K + Gm).IsCartier)
    (hres1 : ∀ U : S.Opens, ∀ τ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U, ∀ i,
      (Set.range (N.n i ≫ ι).base ∩ U).Nonempty →
      ∃! ρ, MMP.Fourfold.IsPoincareResidue sS (N.n i ≫ ι) 1 M τ ρ)
    (hres2 : ∀ U : S.Opens, ∀ τ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U, ∀ ρ,
      IsResidues sS ι N M U τ ρ → IsResSection sS ι N Δ M U ρ)
    {U : S.Opens} {ψ : (RationalFunctions S)ˣ}
    (hτ : unitValue ψ • θ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U)
    {s : ∀ i : N.ι, RationalPluriForms (N.n i ≫ ι ≫ sS) 1 M}
    (hs : IsResidues sS ι N M U (unitValue ψ • θ) s)
    (i : N.ι) (P : MMP.Mori.PrimeDivisor (N.X i))
    (hPU : ι.base ((N.n i).base P.genericPoint) ∈ U) (hsi : s i ≠ 0)
    (hex : ((P.ordForm (s i) : ℤ) : ℚ) + M * N.componentBoundaryCoeff Δ i P = 0) :
    ∀ Q : MMP.Mori.PrimeDivisor S, ι.base ((N.n i).base P.genericPoint) ∈ Q.support →
      ((M : ℤ) • K + Gm).coeff Q + Q.ord ψ = 0 := by
  classical
  set x := ι.base ((N.n i).base P.genericPoint) with hx
  set D : Divisor S := (M : ℤ) • K + Gm with hD
  have hDc : ∀ Γ : MMP.Mori.PrimeDivisor S, D.coeff Γ = M * K.coeff Γ + Gm.coeff Γ := by
    intro Γ; simp [hD, DivisorWithCoeffs.coeff_apply]
  obtain ⟨U₁, hxU₁, φ₁, hφ₁⟩ := hcart x
  have hU₁ne : U₁ ≠ ⊥ := fun h => by rw [h] at hxU₁; exact hxU₁
  set τ₁ := unitValue φ₁⁻¹ • θ with hτ₁def
  have hτ₁ : τ₁ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U₁ :=
    unitValue_inv_smul_mem_pluricanonicalSections hdimS hθ0 hθ hU₁ne hφ₁
  set a := ψ * φ₁ with ha
  have hpos : ∀ Γ : MMP.Mori.PrimeDivisor S, x ∈ Γ.support →
      0 ≤ S.ord (unitValue a) Γ.genericPoint := by
    intro Γ hΓ
    have h1 := hτ.2 Γ ⟨x, hΓ, hPU⟩ (smul_ne_zero (unitValue_ne_zero ψ) hθ0)
    rw [ordForm_unitValue_smul hdimS hθ0, hθ] at h1
    rw [← ord_eq_ord_unitValue, ha, MMP.Mori.PrimeDivisor.ord_mul, ← hφ₁ Γ ⟨x, hΓ, hxU₁⟩, hDc]
    push_cast at h1 ⊢; omega
  obtain ⟨r, hr⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg x
    (unitValue_ne_zero a) hpos
  by_cases hru : IsUnit r
  · intro Q hQ
    rw [hφ₁ Q ⟨x, hQ, hxU₁⟩, add_comm, ← MMP.Mori.PrimeDivisor.ord_mul, ← ha,
      ord_eq_ord_unitValue, ← hr]
    exact ord_algebraMap_eq_zero_of_isUnit hru Q hQ
  exfalso
  have hrm : r ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal r).2 hru
  have hηP : genericPoint (N.X i) ⤳ P.genericPoint := genericPoint_specializes _
  have hspec : (N.n i ≫ ι).base (genericPoint (N.X i)) ⤳ x :=
    hηP.map (N.n i ≫ ι).base.hom.continuous
  set r' := S.presheaf.stalkSpecializes hspec r with hr'def
  have hr' : algebraMap _ S.functionField r' = unitValue a := by
    rw [← hr, hr'def]
    change (S.presheaf.stalkSpecializes hspec ≫ S.presheaf.stalkSpecializes _).hom r = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  have hτeq : unitValue ψ • θ = algebraMap _ S.functionField r' • τ₁ := by
    rw [hr', hτ₁def, smul_smul, ← unitValue_mul, ha, mul_inv_cancel_right]
  have hmeet₁ : (Set.range (N.n i ≫ ι).base ∩ U₁).Nonempty := ⟨x, ⟨P.genericPoint, rfl⟩, hxU₁⟩
  obtain ⟨(ρ₁ : RationalPluriForms (N.n i ≫ ι ≫ sS) 1 M), hρ₁, -⟩ := hres1 U₁ τ₁ hτ₁ i hmeet₁
  have hρ := isPoincareResidue_algebraMap_smul hρ₁ r'
  rw [← hτeq] at hρ
  have hUU₁ne : U ⊓ U₁ ≠ ⊥ := fun h => by
    have : x ∈ U ⊓ U₁ := ⟨hPU, hxU₁⟩
    rw [h] at this; exact this
  have hτUU := mem_pluricanonicalSections_of_le inf_le_left hτ hUU₁ne
  have hmeet : (Set.range (N.n i ≫ ι).base ∩ (U ⊓ U₁)).Nonempty := ⟨x, ⟨_, rfl⟩, hPU, hxU₁⟩
  have hsi' := hs i ⟨x, ⟨_, rfl⟩, hPU⟩
  have heq : s i = ((N.n i ≫ ι).stalkMap (genericPoint (N.X i))).hom r' • ρ₁ :=
    (hres1 _ _ hτUU i hmeet).unique hsi' hρ
  obtain ⟨ρ₁', hρ₁', hsec₁⟩ := exists_isResidues_isResSection hres1 hres2 hτ₁
  have hρ₁'i : ρ₁' i = ρ₁ := (hres1 U₁ τ₁ hτ₁ i hmeet₁).unique (hρ₁' i hmeet₁) hρ₁
  have hsec₁ := hsec₁.1 i P hxU₁
  rw [hρ₁'i] at hsec₁
  have hρ₁0 : ρ₁ ≠ 0 := fun h0 => hsi (by rw [heq, h0, smul_zero])
  have hr'0 : ((N.n i ≫ ι).stalkMap (genericPoint (N.X i))).hom r' ≠ 0 := fun h0 =>
    hsi (by rw [heq, h0, zero_smul])
  have hsec₁' := hsec₁ hρ₁0
  haveI : LocallyOfFiniteType (N.n i ≫ ι ≫ sS) := (N.isNormalVariety i).1.toLocallyOfFiniteType
  have hord := P.ordForm_smul_of_topologicalKrullDim_eq (d := 1) (sX := N.n i ≫ ι ≫ sS)
    (by rw [hdimX i]; rfl) hr'0 hρ₁0
  rw [← heq] at hord
  -- the restriction of `r` vanishes at `P`
  have hb := Scheme.Hom.stalkSpecializes_stalkMap_apply (N.n i ≫ ι) _ _ hηP r
  set b := ((N.n i ≫ ι).stalkMap P.genericPoint).hom r with hbdef
  haveI : IsLocalHom ((N.n i ≫ ι).stalkMap P.genericPoint).hom := (N.n i ≫ ι).prop _
  have hbm : b ∈ IsLocalRing.maximalIdeal _ :=
    (map_mem_nonunits_iff ((N.n i ≫ ι).stalkMap P.genericPoint).hom
      (show S.presheaf.stalk ((N.n i ≫ ι).base P.genericPoint) from r)).2 hrm
  have hr'b : ((N.n i ≫ ι).stalkMap (genericPoint (N.X i))).hom r' =
      algebraMap _ (N.X i).functionField b := hb
  have hb0 : b ≠ 0 := fun h0 => hr'0 (by rw [hr'b, h0, map_zero])
  have h1 := MMP.Flips.one_le_ord_algebraMap_of_mem_maximalIdeal P hbm hb0
  rw [hr'b] at hord
  have hcast : ((P.ordForm (s i) : ℤ) : ℚ) =
      ((N.X i).ord (algebraMap _ (N.X i).functionField b) P.genericPoint : ℚ) +
        ((P.ordForm ρ₁ : ℤ) : ℚ) := by
    exact_mod_cast hord
  have h1q : (1 : ℚ) ≤
      ((N.X i).ord (algebraMap _ (N.X i).functionField b) P.genericPoint : ℚ) := by
    exact_mod_cast h1
  linarith

/-- **Two sections with the same residues agree on the floor near a good point.** Let `τ = ψ θ`
and `τ' = ψ' θ` be sections of `𝒪_S(MK + G_M)` over `U` and `U'` with the same residues `s`,
and `y` a point of the floor over `U ∩ U'` at which `s` is nonzero of exact order on every
component through `y`. Then the restrictions of `ψ` and `ψ'` to the floor agree near `y`. -/
private theorem exists_restrict_unit_eq_of_isResidues [CompactSpace S] [IsReduced C]
    [IsClosedImmersion ι] [Finite N.ι] (hcl : ∀ i, IsClosedImmersion (N.n i ≫ ι))
    (hsurj : ∀ c : C, ∃ i, ∃ z : N.X i, (N.n i).base z = c)
    (hdimX : ∀ i, topologicalKrullDim (N.X i) = 1) (hdimS : topologicalKrullDim S = 2)
    {Δ : MMP.Flips.QWeilDivisor C} {M : ℕ} {K Gm : Divisor S} {θ : RationalPluriForms sS 2 M}
    (hθ0 : θ ≠ 0) (hθ : ∀ Γ : MMP.Mori.PrimeDivisor S, Γ.ordForm θ = M * K.coeff Γ)
    (hcart : ((M : ℤ) • K + Gm).IsCartier)
    (hres1 : ∀ U : S.Opens, ∀ τ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U, ∀ i,
      (Set.range (N.n i ≫ ι).base ∩ U).Nonempty →
      ∃! ρ, MMP.Fourfold.IsPoincareResidue sS (N.n i ≫ ι) 1 M τ ρ)
    (hres2 : ∀ U : S.Opens, ∀ τ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U, ∀ ρ,
      IsResidues sS ι N M U τ ρ → IsResSection sS ι N Δ M U ρ)
    {U U' : S.Opens} {ψ ψ' : (RationalFunctions S)ˣ}
    (hτ : unitValue ψ • θ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U)
    (hτ' : unitValue ψ' • θ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U')
    {s : ∀ i : N.ι, RationalPluriForms (N.n i ≫ ι ≫ sS) 1 M}
    (hs : IsResidues sS ι N M U (unitValue ψ • θ) s)
    (hs' : IsResidues sS ι N M U' (unitValue ψ' • θ) s)
    (hψ : ∀ P : MMP.Mori.PrimeDivisor S, (P.support ∩ U).Nonempty →
      0 ≤ ((M : ℤ) • K + Gm).coeff P + P.ord ψ)
    (hψ' : ∀ P : MMP.Mori.PrimeDivisor S, (P.support ∩ U').Nonempty →
      0 ≤ ((M : ℤ) • K + Gm).coeff P + P.ord ψ')
    (y : C) (hyU : ι.base y ∈ U) (hyU' : ι.base y ∈ U')
    (hgood : ∀ i (z : N.X i), (N.n i).base z = y → ∃ P : MMP.Mori.PrimeDivisor (N.X i),
      P.genericPoint = z ∧ s i ≠ 0 ∧
        ((P.ordForm (s i) : ℤ) : ℚ) + M * N.componentBoundaryCoeff Δ i P = 0) :
    ∃ Ω : S.Opens, ι.base y ∈ Ω ∧ ∃ (hΩ : Ω ≤ U) (hΩ' : Ω ≤ U'),
      ((Scheme.Modules.pullback ι).obj ((M : ℤ) • K + Gm).divisorialSheaf).presheaf.map
          (homOfLE (fun x hx => hΩ hx : ι ⁻¹ᵁ Ω ≤ ι ⁻¹ᵁ U)).op
          (((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app
            ((M : ℤ) • K + Gm).divisorialSheaf).app U
            (MMP.Fourfold.divisorialSectionOfUnit ψ hψ)) =
        ((Scheme.Modules.pullback ι).obj ((M : ℤ) • K + Gm).divisorialSheaf).presheaf.map
          (homOfLE (fun x hx => hΩ' hx : ι ⁻¹ᵁ Ω ≤ ι ⁻¹ᵁ U')).op
          (((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app
            ((M : ℤ) • K + Gm).divisorialSheaf).app U'
            (MMP.Fourfold.divisorialSectionOfUnit ψ' hψ')) := by
  classical
  set D : Divisor S := (M : ℤ) • K + Gm with hD
  set x := ι.base y with hx
  obtain ⟨i₀, z₀, hz₀⟩ := hsurj y
  obtain ⟨P₀, hP₀, hs₀, hex₀⟩ := hgood i₀ z₀ hz₀
  have hψx : ∀ Q : MMP.Mori.PrimeDivisor S, x ∈ Q.support → D.coeff Q + Q.ord ψ = 0 := by
    have h := coeff_add_ord_eq_zero_of_isResidues hdimX hdimS hθ0 hθ hcart hres1 hres2 hτ hs i₀
      P₀ (by rw [hP₀, hz₀]; exact hyU) hs₀ hex₀
    rwa [hP₀, hz₀] at h
  obtain ⟨Ω, hΩO, hΩU, ρ, hxΩ, hρ⟩ := exists_eq_smul_divisorialSectionOfUnit ψ hψ hyU hyU' hψx
    (MMP.Fourfold.divisorialSectionOfUnit ψ' hψ')
  haveI : Nonempty Ω := ⟨⟨x, hxΩ⟩⟩
  have hval := unitValue_eq_of_restrict_eq_smul hψ hψ' hΩU hΩO ρ hρ
  have hrange : ∀ i (z : N.X i), (N.n i).base z = y → x ∈ Set.range (N.n i ≫ ι).base :=
    fun i z hz => ⟨z, by rw [Scheme.Hom.comp_apply, hz]⟩
  -- on every component through `y`, `ρ = 1` at the generic point
  have hkey : ∀ i, (∃ z : N.X i, (N.n i).base z = y) →
      ∀ hw : (N.n i ≫ ι).base (genericPoint (N.X i)) ∈ Ω,
        (N.n i ≫ ι).base (genericPoint (N.X i)) ∉ S.basicOpen (ρ - 1) := by
    rintro i ⟨z, hz⟩ hw hmem
    obtain ⟨P, -, hsi, -⟩ := hgood i z hz
    set b := S.presheaf.germ Ω _ hw ρ with hbdef
    have hb : algebraMap _ S.functionField b = S.germToFunctionField Ω ρ :=
      Scheme.algebraMap_germ_eq_germToFunctionField S hw ρ
    have hτeq : unitValue ψ' • θ = algebraMap _ S.functionField b • (unitValue ψ • θ) := by
      rw [hb, hval, mul_smul]
    have hxi : (Set.range (N.n i ≫ ι).base ∩ U).Nonempty := ⟨x, hrange i z hz, hyU⟩
    have hxi' : (Set.range (N.n i ≫ ι).base ∩ U').Nonempty := ⟨x, hrange i z hz, hyU'⟩
    have h1 := isPoincareResidue_algebraMap_smul (hs i hxi) b
    rw [← hτeq] at h1
    have h2 : s i = ((N.n i ≫ ι).stalkMap (genericPoint (N.X i))).hom b • s i :=
      (hres1 U' _ hτ' i hxi').unique (hs' i hxi') h1
    have h3 : ((N.n i ≫ ι).stalkMap (genericPoint (N.X i))).hom b = 1 := by
      have h4 : (((N.n i ≫ ι).stalkMap (genericPoint (N.X i))).hom b - 1) • s i = 0 := by
        rw [sub_smul, one_smul, ← h2, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h4).resolve_right hsi)
    rw [Scheme.mem_basicOpen S (ρ - 1) _ hw, map_sub, map_one] at hmem
    have h5 := hmem.map ((N.n i ≫ ι).stalkMap (genericPoint (N.X i))).hom
    rw [map_sub, map_one, ← hbdef, h3, sub_self] at h5
    exact not_isUnit_zero h5
  -- remove the components not through `y`
  let bad : Set N.ι := {i | ¬ ∃ z : N.X i, (N.n i).base z = y}
  let Ω' : S.Opens := ⟨(Ω : Set S) ∩ ⋂ i ∈ bad, (Set.range (N.n i ≫ ι).base)ᶜ,
    Ω.isOpen.inter ((Set.toFinite bad).isOpen_biInter fun i _ =>
      (N.n i ≫ ι).isClosedEmbedding.isClosed_range.isOpen_compl)⟩
  have hΩ'Ω : Ω' ≤ Ω := fun c hc => hc.1
  have hxΩ' : x ∈ Ω' := by
    refine ⟨hxΩ, Set.mem_iInter₂.2 fun i hi ⟨z, hz⟩ => hi ⟨z, ?_⟩⟩
    rw [Scheme.Hom.comp_apply] at hz
    exact ι.isClosedEmbedding.injective hz
  set ρ' := S.presheaf.map (homOfLE hΩ'Ω).op ρ with hρ'
  have h0 : ι.app Ω' (ρ' - 1) = 0 := by
    refine eq_zero_of_basicOpen_eq_bot _ ?_
    rw [← Scheme.preimage_basicOpen, eq_bot_iff]
    intro c hc
    have hρ'1 : ρ' - 1 = S.presheaf.map (homOfLE hΩ'Ω).op (ρ - 1) := by
      rw [map_sub, map_one]
    change ι.base c ∈ S.basicOpen (ρ' - 1) at hc
    rw [hρ'1, Scheme.basicOpen_res] at hc
    obtain ⟨hcΩ', hcb⟩ := hc
    obtain ⟨i, z, hz⟩ := hsurj c
    by_cases hi : i ∈ bad
    · exact (Set.mem_iInter₂.1 hcΩ'.2 i hi) ⟨z, by rw [Scheme.Hom.comp_apply, hz]⟩
    · have hsp : (N.n i ≫ ι).base (genericPoint (N.X i)) ⤳ ι.base c := by
        rw [← hz, ← Scheme.Hom.comp_apply]
        exact (genericPoint_specializes z).map (N.n i ≫ ι).base.hom.continuous
      have hw : (N.n i ≫ ι).base (genericPoint (N.X i)) ∈ Ω := hsp.mem_open Ω.isOpen hcΩ'.1
      exact hkey i (not_not.1 hi) hw (hsp.mem_open (S.basicOpen (ρ - 1)).isOpen hcb)
  have hρ'1 : ι.app Ω' ρ' = 1 := by
    rw [← sub_eq_zero, ← map_one (ι.app Ω').hom, ← map_sub]
    exact h0
  refine ⟨Ω', hxΩ', fun c hc => hΩU (hΩ'Ω hc), fun c hc => hΩO (hΩ'Ω hc), ?_⟩
  let η : D.divisorialSheaf ⟶ (Scheme.Modules.pushforward ι).obj
      ((Scheme.Modules.pullback ι).obj D.divisorialSheaf) :=
    (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app D.divisorialSheaf
  have e1 := natural_apply η (homOfLE (fun c hc => hΩU (hΩ'Ω hc) : Ω' ≤ U))
    (MMP.Fourfold.divisorialSectionOfUnit ψ hψ)
  have e2 := natural_apply η (homOfLE (fun c hc => hΩO (hΩ'Ω hc) : Ω' ≤ U'))
    (MMP.Fourfold.divisorialSectionOfUnit ψ' hψ')
  change ((Scheme.Modules.pullback ι).obj D.divisorialSheaf).presheaf.map _ (η.app U _) =
    ((Scheme.Modules.pullback ι).obj D.divisorialSheaf).presheaf.map _ (η.app U' _)
  refine e1.trans (Eq.trans ?_ e2.symm)
  have e3 : D.divisorialSheaf.presheaf.map (homOfLE (fun c hc => hΩO (hΩ'Ω hc) : Ω' ≤ U')).op
      (MMP.Fourfold.divisorialSectionOfUnit ψ' hψ') =
      ρ' • D.divisorialSheaf.presheaf.map (homOfLE (fun c hc => hΩU (hΩ'Ω hc) : Ω' ≤ U)).op
        (MMP.Fourfold.divisorialSectionOfUnit ψ hψ) := by
    have h := congrArg (D.divisorialSheaf.presheaf.map (homOfLE hΩ'Ω).op) hρ
    rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp] at h
    exact h
  rw [e3, Scheme.Modules.Hom.app_smul]
  change _ = ι.app Ω' ρ' • (show Γ((Scheme.Modules.pullback ι).obj D.divisorialSheaf, ι ⁻¹ᵁ Ω')
    from η.app Ω' (D.divisorialSheaf.presheaf.map
    (homOfLE (fun c hc => hΩU (hΩ'Ω hc) : Ω' ≤ U)).op
    (MMP.Fourfold.divisorialSectionOfUnit ψ hψ)))
  rw [hρ'1, one_smul]

/-- A form `ψ θ` in `𝒪_S(MK + G)` over `U` is the unit `ψ` of `𝒪_S(MK + G)` over `U`. -/
private theorem coeff_add_ord_nonneg_of_mem (hdimS : topologicalKrullDim S = 2) {M : ℕ}
    {K Gm : Divisor S} {θ : RationalPluriForms sS 2 M} (hθ0 : θ ≠ 0)
    (hθ : ∀ Γ : MMP.Mori.PrimeDivisor S, Γ.ordForm θ = M * K.coeff Γ) {U : S.Opens}
    {ψ : (RationalFunctions S)ˣ}
    (hτ : unitValue ψ • θ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U) :
    ∀ P : MMP.Mori.PrimeDivisor S, (P.support ∩ U).Nonempty →
      0 ≤ ((M : ℤ) • K + Gm).coeff P + P.ord ψ := by
  intro P hP
  have h := hτ.2 P hP (smul_ne_zero (unitValue_ne_zero ψ) hθ0)
  rw [ordForm_unitValue_smul hdimS hθ0, hθ] at h
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  linarith

/-- **The local construction from residue sections.** Given an open `V` of `Z` and a family `s`
of forms on the components of the floor which is a section of `ω_C^{⊗M}(MΔ)` over `f⁻¹ V`,
nonzero on every component meeting it, with finitely many bad closed points over `V`, the lifts
of `s` to affine opens of `S` glue on the floor to a section of `ι^* 𝒪_S(MK + G)` over
`(ι ≫ f)⁻¹ V`, generated near every good point `t`. -/
private theorem exists_local_data_of_sections [CompactSpace S] [IsReduced C]
    [IsClosedImmersion ι] [Finite N.ι] [JacobsonSpace C]
    (hcl : ∀ i, IsClosedImmersion (N.n i ≫ ι))
    (hsurj : ∀ c : C, ∃ i, ∃ z : N.X i, (N.n i).base z = c)
    (hdimX : ∀ i, topologicalKrullDim (N.X i) = 1) (hdimS : topologicalKrullDim S = 2)
    {Δ : MMP.Flips.QWeilDivisor C} {M : ℕ} {K Gm : Divisor S} {θ : RationalPluriForms sS 2 M}
    (hθ0 : θ ≠ 0) (hθ : ∀ Γ : MMP.Mori.PrimeDivisor S, Γ.ordForm θ = M * K.coeff Γ)
    (hcart : ((M : ℤ) • K + Gm).IsCartier)
    (hres1 : ∀ U : S.Opens, ∀ τ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U, ∀ i,
      (Set.range (N.n i ≫ ι).base ∩ U).Nonempty →
      ∃! ρ, MMP.Fourfold.IsPoincareResidue sS (N.n i ≫ ι) 1 M τ ρ)
    (hres2 : ∀ U : S.Opens, ∀ τ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U, ∀ ρ,
      IsResidues sS ι N M U τ ρ → IsResSection sS ι N Δ M U ρ)
    (hres4 : ∀ U : S.Opens, IsAffineOpen U → ∀ s, IsResSection sS ι N Δ M U s →
      ∃ τ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U, IsResidues sS ι N M U τ s)
    {Z : Scheme.{0}} (f : S ⟶ Z) (V : Z.Opens)
    (s : ∀ i : N.ι, RationalPluriForms (N.n i ≫ ι ≫ sS) 1 M)
    (hsV : IsResSection sS ι N Δ M (f ⁻¹ᵁ V) s)
    (hs_ne : ∀ i (z : N.X i), ι.base ((N.n i).base z) ∈ f ⁻¹ᵁ V → s i ≠ 0)
    (hZ₀ : {y : C | ι.base y ∈ f ⁻¹ᵁ V ∧ IsClosed ({y} : Set C) ∧
      ¬ IsGoodPoint sS ι N Δ M s y}.Finite)
    (t : C) (htV : ι.base t ∈ f ⁻¹ᵁ V) (ht : IsGoodPoint sS ι N Δ M s t) :
    ∃ (σ : Γ((Scheme.Modules.pullback ι).obj ((M : ℤ) • K + Gm).divisorialSheaf, (ι ≫ f) ⁻¹ᵁ V))
      (U : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (ψ : (RationalFunctions S)ˣ)
      (hψ : ∀ P : MMP.Mori.PrimeDivisor S, (P.support ∩ U).Nonempty →
        0 ≤ ((M : ℤ) • K + Gm).coeff P + P.ord ψ),
      ι.base t ∈ U ∧ (∀ P : MMP.Mori.PrimeDivisor S, ι.base t ∈ P.support →
        ((M : ℤ) • K + Gm).coeff P + P.ord ψ = 0) ∧
      ((Scheme.Modules.pullback ι).obj ((M : ℤ) • K + Gm).divisorialSheaf).presheaf.map
          (homOfLE (fun x hx => hUV hx : ι ⁻¹ᵁ U ≤ (ι ≫ f) ⁻¹ᵁ V)).op σ =
        ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app
          ((M : ℤ) • K + Gm).divisorialSheaf).app U
          (MMP.Fourfold.divisorialSectionOfUnit ψ hψ) := by
  classical
  set D : Divisor S := (M : ℤ) • K + Gm with hD
  set W := f ⁻¹ᵁ V with hW
  set Z₀ := {y : C | ι.base y ∈ W ∧ IsClosed ({y} : Set C) ∧
    ¬ IsGoodPoint sS ι N Δ M s y} with hZ₀def
  have hZ₀cl : IsClosed (ι.base '' Z₀) := by
    rw [← Set.biUnion_of_singleton Z₀, Set.image_iUnion₂]
    exact hZ₀.isClosed_biUnion fun y hy => ι.isClosedEmbedding.isClosedMap _ hy.2.1
  -- affine neighbourhoods meeting at most one bad point
  have hU : ∀ c : C, ι.base c ∈ W → ∃ U : S.Opens, IsAffineOpen U ∧ ι.base c ∈ U ∧ U ≤ W ∧
      ∀ y ∈ Z₀, ι.base y ∈ U → y = c := by
    intro c hc
    have hcl' : IsClosed (ι.base '' (Z₀ \ {c})) := by
      rw [← Set.biUnion_of_singleton (Z₀ \ {c}), Set.image_iUnion₂]
      exact (hZ₀.diff).isClosed_biUnion fun y hy =>
        ι.isClosedEmbedding.isClosedMap _ hy.1.2.1
    have hO : IsOpen ((W : Set S) ∩ (ι.base '' (Z₀ \ {c}))ᶜ) :=
      W.isOpen.inter hcl'.isOpen_compl
    have hcO : ι.base c ∈ (W : Set S) ∩ (ι.base '' (Z₀ \ {c}))ᶜ :=
      ⟨hc, fun ⟨y, hy, hyc⟩ => hy.2 (ι.isClosedEmbedding.injective hyc)⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hcU, hUO⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hcO hO
    exact ⟨U, hU, hcU, fun x hx => (hUO hx).1, fun y hy hyU => by_contra fun h =>
      (hUO hyU).2 ⟨y, ⟨hy, h⟩, rfl⟩⟩
  let J := {c : C // ι.base c ∈ W}
  choose U hUaff hcU hUW hUZ using fun c : J => hU c.1 c.2
  -- lifts of `s`
  have hlift : ∀ c : J, ∃ ψ : (RationalFunctions S)ˣ,
      unitValue ψ • θ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm (U c) ∧
        IsResidues sS ι N M (U c) (unitValue ψ • θ) s := by
    intro c
    obtain ⟨τ, hτ, hτs⟩ := hres4 (U c) (hUaff c) s (hsV.mono (hUW c))
    obtain ⟨i, z, hz⟩ := hsurj c.1
    have hmeet : (Set.range (N.n i ≫ ι).base ∩ U c).Nonempty :=
      ⟨_, ⟨z, rfl⟩, by rw [Scheme.Hom.comp_apply, hz]; exact hcU c⟩
    obtain ⟨ψ, rfl⟩ := exists_eq_unitValue_smul_of_isPoincareResidue hdimS hθ0 (hτs i hmeet)
      (hres1 (U c) _ hτ i hmeet) (hs_ne i z (by rw [hz]; exact hUW c (hcU c)))
    exact ⟨ψ, hτ, hτs⟩
  choose ψ hψτ hψs using hlift
  have hψD := fun c => coeff_add_ord_nonneg_of_mem hdimS hθ0 hθ (hψτ c)
  set F := (Scheme.Modules.pullback ι).obj D.divisorialSheaf with hF
  set η := (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app D.divisorialSheaf with hη
  -- compatibility on overlaps
  have hcompat : ∀ c c' : J,
      F.presheaf.map (homOfLE (inf_le_left : ι ⁻¹ᵁ U c ⊓ ι ⁻¹ᵁ U c' ≤ ι ⁻¹ᵁ U c)).op
          (η.app (U c) (MMP.Fourfold.divisorialSectionOfUnit (ψ c) (hψD c))) =
        F.presheaf.map (homOfLE (inf_le_right : ι ⁻¹ᵁ U c ⊓ ι ⁻¹ᵁ U c' ≤ ι ⁻¹ᵁ U c')).op
          (η.app (U c') (MMP.Fourfold.divisorialSectionOfUnit (ψ c') (hψD c'))) := by
    intro c c'
    by_cases hcc : c = c'
    · subst hcc; rfl
    have hloc : ∀ y ∈ (ι ⁻¹ᵁ U c ⊓ ι ⁻¹ᵁ U c' : C.Opens), ∃ Ω : S.Opens, y ∈ ι ⁻¹ᵁ Ω ∧
        ∃ (hΩ : Ω ≤ U c) (hΩ' : Ω ≤ U c'),
          F.presheaf.map (homOfLE (fun x hx => hΩ hx : ι ⁻¹ᵁ Ω ≤ ι ⁻¹ᵁ U c)).op
              (η.app (U c) (MMP.Fourfold.divisorialSectionOfUnit (ψ c) (hψD c))) =
            F.presheaf.map (homOfLE (fun x hx => hΩ' hx : ι ⁻¹ᵁ Ω ≤ ι ⁻¹ᵁ U c')).op
              (η.app (U c') (MMP.Fourfold.divisorialSectionOfUnit (ψ c') (hψD c'))) := by
      intro y hy
      obtain ⟨y', ⟨hyy', hy'O⟩, hy'cl⟩ := nonempty_inter_closedPoints
        (Z := closure {y} ∩ ((ι ⁻¹ᵁ U c ⊓ ι ⁻¹ᵁ U c' : C.Opens) : Set C))
        ⟨y, subset_closure rfl, hy⟩
        (isClosed_closure.isLocallyClosed.inter (ι ⁻¹ᵁ U c ⊓ ι ⁻¹ᵁ U c').isOpen.isLocallyClosed)
      have hgood : IsGoodPoint sS ι N Δ M s y' := by
        by_contra hng
        have hmem : y' ∈ Z₀ := ⟨hUW c hy'O.1, hy'cl, hng⟩
        exact hcc (Subtype.ext ((hUZ c y' hmem hy'O.1).symm.trans (hUZ c' y' hmem hy'O.2)))
      obtain ⟨Ω, hy'Ω, hΩ, hΩ', heq⟩ := exists_restrict_unit_eq_of_isResidues hcl hsurj hdimX
        hdimS hθ0 hθ hcart hres1 hres2 (hψτ c) (hψτ c') (hψs c) (hψs c') (hψD c) (hψD c') y'
        hy'O.1 hy'O.2 hgood
      exact ⟨Ω, ((specializes_iff_mem_closure.2 hyy').map ι.base.hom.continuous).mem_open
        Ω.isOpen hy'Ω, hΩ, hΩ', heq⟩
    choose Ω hyΩ hΩ hΩ' heq using hloc
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨F.presheaf, F.isSheaf⟩
      (fun y : ((ι ⁻¹ᵁ U c ⊓ ι ⁻¹ᵁ U c' : C.Opens) : Set C) => ι ⁻¹ᵁ Ω y.1 y.2)
      (ι ⁻¹ᵁ U c ⊓ ι ⁻¹ᵁ U c')
      (fun y => homOfLE fun x hx => ⟨hΩ y.1 y.2 hx, hΩ' y.1 y.2 hx⟩)
      (fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyΩ y hy⟩) _ _ fun y => ?_
    refine (map_map_apply F _ _ _).trans (Eq.trans ?_ (map_map_apply F _ _ _).symm)
    exact heq y.1 y.2
  -- gluing
  obtain ⟨σ, hσ⟩ := exists_restrict_eq_unit_app ι D.divisorialSheaf (fun c : J => U c)
    (fun c => MMP.Fourfold.divisorialSectionOfUnit (ψ c) (hψD c)) ((ι ≫ f) ⁻¹ᵁ V)
    (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hcU ⟨x, hx⟩⟩)
    (fun c x hx => hUW c hx) hcompat
  -- the generator at `t`
  let t' : J := ⟨t, htV⟩
  obtain ⟨i, z, hz⟩ := hsurj t
  obtain ⟨P, hPz, hsi, hex⟩ := ht i z hz
  have hgen := coeff_add_ord_eq_zero_of_isResidues hdimX hdimS hθ0 hθ hcart hres1 hres2
    (hψτ t') (hψs t') i P (by rw [hPz, hz]; exact hcU t') hsi hex
  rw [hPz, hz] at hgen
  exact ⟨σ, U t', hUW t', ψ t', hψD t', hcU t', hgen, hσ t'⟩

end Generation

/-- A pointwise inequality of finitely supported functions gives the inequality of their sums. -/
private theorem finsupp_sum_le {α : Type*} (A B : α →₀ ℚ) (h : ∀ a, A a ≤ B a) :
    (A.sum fun _ x => x) ≤ B.sum fun _ x => x := by
  have h1 : 0 ≤ (B - A).sum fun _ x => x :=
    Finsupp.sum_nonneg fun a _ => by simp only [Finsupp.coe_sub, Pi.sub_apply]; linarith [h a]
  rw [Finsupp.sum_sub_index (fun _ _ _ => rfl)] at h1
  linarith

/-- Powers of a nonzero rational top form: for every `a > 0` a nonzero `a`-canonical form of
order `a · ord(ω)` along every prime divisor. -/
private theorem exists_pow_form {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType sX]
    {d : ℕ} (hd : topologicalKrullDim X = d) {ω : RationalPluriForms sX d 1} (hω : ω ≠ 0) :
    ∀ a : ℕ, 0 < a → ∃ θ : RationalPluriForms sX d (a : ℕ), θ ≠ 0 ∧
      ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm θ = a * Γ.ordForm ω := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => exact ⟨ω, hω, fun Γ => by simp⟩
  | succ a ha ih =>
    obtain ⟨θ, hθ0, hθ⟩ := ih
    refine ⟨MMP.Fourfold.RationalPluriForms.mul sX d a 1 θ ω,
      MMP.Fourfold.RationalPluriForms.mul_ne_zero hd hθ0 hω, fun Γ => ?_⟩
    rw [MMP.Fourfold.ordForm_mul Γ hθ0 hω, hθ Γ]
    push_cast; ring

/-- On an integral scheme the order `v_Γ(w)` of a unit of the local ring at the generic point of
the component of `Γ` is the order of vanishing of its image in the function field. -/
private theorem ordUnit_eq_ord {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (Γ : MMP.Mori.PrimeDivisor X)
    (w : (X.presheaf.stalk (componentGenericPoint X Γ.component))ˣ) :
    Γ.ordUnit w = X.ord ((MMP.Positivity.componentToFunctionField Γ.component).hom w)
      Γ.genericPoint := by
  set y := (w : X.presheaf.stalk (componentGenericPoint X Γ.component))
  have hz := Γ.coheight_genericPoint
  have hne : (MMP.Positivity.componentToFunctionField Γ.component).hom y ≠ 0 :=
    (w.isUnit.map _).ne_zero
  rw [eq_comm, Scheme.ord_eq_iff hz hne]
  rw [show ((Multiplicative.ofAdd (Γ.ordUnit w) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) = Γ.valuation y from (Γ.valuation_eq_exp_ordUnit w).symm]
  let := Γ.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions Γ.genericPoint_mem_component
  have : Ring.KrullDimLE 1 Γ.localRing := krullDimLE_of_coheight_le hz.le
  let ψ := IsLocalization.algEquiv (nonZeroDivisors Γ.localRing)
    (X.presheaf.stalk (componentGenericPoint X Γ.component)) (FractionRing Γ.localRing)
  change Ring.ordFrac (X.presheaf.stalk Γ.genericPoint) _ = Ring.ordFrac Γ.localRing (ψ y)
  have key := MMP.Positivity.ordFrac_map_of_comp (R := Γ.localRing)
    (K₁ := FractionRing Γ.localRing) (K₂ := X.functionField)
    ((MMP.Positivity.componentToFunctionField Γ.component).hom.comp (ψ.symm : _ →+* _)) ?_
    (ψ y)
  · simpa using key
  · intro r
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, AlgEquiv.commutes]
    change (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom r =
      (X.presheaf.stalkSpecializes _).hom r
    rw [TopCat.Presheaf.stalkSpecializes_comp]

/-- If an element `u` of the local ring at `y` represents the unit `ψ` of `K(X)`, its image in
the function field is `ψ`. -/
private theorem stalkSpecializes_eq_unitValue {X : Scheme.{0}} [IsIntegral X] {y : X}
    {W : irreducibleComponents X} (hW : y ∈ W.1) {u : X.presheaf.stalk y}
    {ψ : (RationalFunctions X)ˣ}
    (hu : (stalkToRationalFunctions X hW).hom u = (ψ : RationalFunctions X) W) :
    (X.presheaf.stalkSpecializes (genericPoint_specializes y)).hom u = unitValue ψ := by
  haveI := subsingleton_irreducibleComponents (X := X)
  obtain rfl := Subsingleton.elim W (topComponent X)
  rw [unitValue, ← hu]
  change _ = (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom u
  rw [TopCat.Presheaf.stalkSpecializes_comp]

/-- On a curve, an open set containing the generic point contains the generic points of all
but finitely many prime divisors. -/
private theorem exists_primeDivisor_mem_open {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType sX]
    [CompactSpace X] (hdim : topologicalKrullDim X = 1) {O : Set X} (hO : IsOpen O)
    (hη : genericPoint X ∈ O) (F : Set (MMP.Mori.PrimeDivisor X)) (hF : F.Finite) :
    ∃ P : MMP.Mori.PrimeDivisor X, P ∉ F ∧ P.genericPoint ∈ O := by
  have hA := finite_of_isClosed_of_genericPoint_notMem hdim hO.isClosed_compl
    (by simpa using hη)
  have hB : {P : MMP.Mori.PrimeDivisor X | P.genericPoint ∉ O}.Finite :=
    hA.preimage (fun a _ b _ h => AlgebraicGeometry.PrimeDivisor.genericPoint_injective h)
  haveI := infinite_primeDivisor (sX := sX) hdim
  obtain ⟨P, hP⟩ := (hF.union hB).infinite_compl.nonempty
  exact ⟨P, fun h => hP (Or.inl h), by_contra fun h => hP (Or.inr h)⟩

/-- The degree along a curve depends on the structure morphism only through its value. -/
private theorem degreeOn_congr_structure {k : Type} [Field k] {X C : Scheme.{0}}
    {sX sX' : X ⟶ Spec (.of k)} (h : sX = sX') (i : C ⟶ X) [IsProper (i ≫ sX)]
    [IsProper (i ≫ sX')] (hdim : topologicalKrullDim C ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    MMP.Mori.degreeOn k sX i hdim L = MMP.Mori.degreeOn k sX' i hdim L := by
  subst h
  rfl

/-! ### Nefness on the contracted components and the choice of sections -/

/-- **Adjunction for nefness.** On a component `Cᵢ` of the floor contracted by `f`, the adjoint
`K_{Cᵢ} + Δᵢ` has nonnegative degree. -/
private theorem sum_nonneg_of_isContracted {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {S Z C : Scheme.{0}} (sS : S ⟶ Spec (.of k))
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [QuasiCompact sS]
    (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (f : S ⟶ Z) (K : Divisor S) (B : QDivisor S)
    (hdlt : IsDltPair sS 2 K B)
    (hnef : QDivisor.IsRelativelyNef sS f (Divisor.toQDivisor K + B))
    (ι : C ⟶ S) [IsClosedImmersion ι]
    {Δ : MMP.Flips.QWeilDivisor C} (hslc : MMP.Flips.IsSlcCurve (ι ≫ sS) Δ)
    {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
    (N : MMP.Flips.NormalizationComponents (ι ≫ sS) hC)
    (hcl : ∀ i, IsClosedImmersion (N.n i ≫ ι))
    {M : ℕ} (hM : 0 < M) (Gm : Divisor S) (hGm : Divisor.toQDivisor Gm = (M : ℚ) • B)
    (hcart : ((M : ℤ) • K + Gm).IsCartier)
    (hres1 : ∀ U : S.Opens, ∀ τ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U, ∀ i,
      (Set.range (N.n i ≫ ι).base ∩ U).Nonempty →
      ∃! ρ, MMP.Fourfold.IsPoincareResidue sS (N.n i ≫ ι) 1 M τ ρ)
    (hres2 : ∀ U : S.Opens, ∀ τ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U, ∀ ρ,
      IsResidues sS ι N M U τ ρ → IsResSection sS ι N Δ M U ρ)
    (hres4 : ∀ U : S.Opens, IsAffineOpen U → ∀ s, IsResSection sS ι N Δ M U s →
      ∃ τ ∈ pluricanonicalSections sS 2 (M : ℕ) Gm U, IsResidues sS ι N M U τ s)
    (hdimX : ∀ i, topologicalKrullDim (N.X i) = 1)
    (i : N.ι)
    (hcontr : ∀ x, (N.n i ≫ ι ≫ f).base x = (N.n i ≫ ι ≫ f).base (genericPoint (N.X i)))
    {Ki : Divisor (N.X i)} (hKi : Ki.IsCanonicalDivisor (N.n i ≫ ι ≫ sS) 1)
    {Δi : QDivisor (N.X i)} (hΔi : ∀ P, Δi.coeff P = N.componentBoundaryCoeff Δ i P) :
    0 ≤ (Ki.sum fun _ a => (a : ℚ)) + Δi.sum fun _ a => a := by
  classical
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have hXS : IsNormalVariety k sS := hdlt.1.1
  haveI : LocallyOfFiniteType sS := hXS.1.toLocallyOfFiniteType
  have hdimS : topologicalKrullDim S = 2 := hdlt.1.2.1.1
  haveI := hcl i
  set j := N.n i ≫ ι with hj
  have hXi : IsNormalVariety k (N.n i ≫ ι ≫ sS) := N.isNormalVariety i
  haveI : LocallyOfFiniteType (N.n i ≫ ι ≫ sS) := hXi.1.toLocallyOfFiniteType
  have hdimXi : topologicalKrullDim (N.X i) = 1 := hKi.1
  set D : Divisor S := (M : ℤ) • K + Gm with hD
  -- the forms `θ_S` and `θ_X` of divisors `MK` and `MKᵢ`
  obtain ⟨θ, hθ0, hθ⟩ : ∃ θ : RationalPluriForms sS 2 (M : ℕ), θ ≠ 0 ∧
      ∀ Γ : MMP.Mori.PrimeDivisor S, Γ.ordForm θ = (M : ℤ) * K.coeff Γ := by
    obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXS hdlt.1.2.1
    obtain ⟨θ, hθ0, hθ⟩ := exists_pow_form (d := 2) (by rw [hdimS]; rfl) hω0 M hM
    exact ⟨θ, hθ0, fun Γ => by rw [hθ Γ, hω Γ]⟩
  obtain ⟨θX, hθX0, hθX⟩ : ∃ θ : RationalPluriForms (N.n i ≫ ι ≫ sS) 1 (M : ℕ), θ ≠ 0 ∧
      ∀ P : MMP.Mori.PrimeDivisor (N.X i), P.ordForm θ = (M : ℤ) * Ki.coeff P := by
    obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXi hKi
    obtain ⟨θ, hθ0, hθ⟩ := exists_pow_form (d := 1) (by rw [hdimXi]; rfl) hω0 M hM
    exact ⟨θ, hθ0, fun P => by rw [hθ P, hω P]⟩
  haveI : QuasiCompact (N.n i ≫ ι ≫ sS) := hXi.1.toQuasiCompact
  haveI : CompactSpace (N.X i) := QuasiCompact.compactSpace_of_compactSpace (N.n i ≫ ι ≫ sS)
  -- the family `s` which is `θ_X` on `Cᵢ` and `0` on the other components
  set s : ∀ i' : N.ι, RationalPluriForms (N.n i' ≫ ι ≫ sS) 1 (M : ℕ) :=
    Function.update (fun _ => 0) i θX with hsdef
  have hsi : s i = θX := by rw [hsdef, Function.update_self]
  have hsne : ∀ i', i' ≠ i → s i' = 0 := fun i' h => by rw [hsdef, Function.update_of_ne h]
  -- an affine neighbourhood `U₁` of the generic point of `Cᵢ` avoiding the nodes and `Supp Kᵢ`
  have hηK : ∀ P : MMP.Mori.PrimeDivisor (N.X i),
      genericPoint (N.X i) ∉ closure {P.genericPoint} := by
    intro P h
    have h1 : P.genericPoint ⤳ genericPoint (N.X i) := specializes_iff_mem_closure.2 h
    have h2 : P.genericPoint = genericPoint (N.X i) :=
      (h1.antisymm (genericPoint_specializes _)).eq
    have h3 := P.coheight_genericPoint
    rw [h2, show genericPoint (N.X i) = (⊤ : N.X i) from rfl, Order.coheight_top] at h3
    exact zero_ne_one h3
  set Zc : Set C := ((MMP.Mori.smoothLocus (ι ≫ sS) : C.Opens) : Set C)ᶜ with hZcdef
  have hZc : IsClosed Zc := (MMP.Mori.smoothLocus (ι ≫ sS)).isOpen.isClosed_compl
  set A : Set (N.X i) :=
    ⋃ P ∈ (Ki.support : Set (MMP.Mori.PrimeDivisor (N.X i))), closure {P.genericPoint} with hAdef
  have hA : IsClosed A := Ki.support.finite_toSet.isClosed_biUnion fun _ _ => isClosed_closure
  set O : S.Opens := ⟨(ι.base '' Zc ∪ j.base '' A)ᶜ,
    ((ι.isClosedEmbedding.isClosedMap _ hZc).union
      (j.isClosedEmbedding.isClosedMap _ hA)).isOpen_compl⟩ with hOdef
  have hηO : j.base (genericPoint (N.X i)) ∈ O := by
    haveI : IsReduced C := hslc.1.2.1
    haveI : LocallyOfFiniteType (ι ≫ sS) := hslc.1.1.2.1
    haveI : QuasiCompact (ι ≫ sS) := hslc.1.1.2.2
    haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (ι ≫ sS)
    haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sS)
    haveI : LocallyOfFinitePresentation (ι ≫ sS) := inferInstance
    have hdense : Dense ((MMP.Mori.smoothLocus (ι ≫ sS) : C.Opens) : Set C) := by
      rw [MMP.Mori.smoothLocus_eq_smoothLocus]
      exact Scheme.Hom.dense_smoothLocus_of_perfectField _
    rintro (⟨c, hc, hce⟩ | ⟨a, ha, hae⟩)
    · have : c = (N.n i).base (genericPoint (N.X i)) := ι.isClosedEmbedding.injective hce
      exact hc (this ▸ map_genericPoint_mem_of_dense N i
        (MMP.Mori.smoothLocus (ι ≫ sS)).isOpen hdense)
    · have : a = genericPoint (N.X i) := j.isClosedEmbedding.injective hae
      obtain ⟨P, hP, hPa⟩ := Set.mem_iUnion₂.1 ha
      exact hηK P (this ▸ hPa)
  obtain ⟨U₁, hU₁aff, hU₁, hU₁O⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens S) hηO
  have hsec : IsResSection sS ι N Δ M U₁ s := by
    refine ⟨fun i' P hP hs0 => ?_, fun i₁ i₂ P P' _ hP hnode _ => ?_⟩
    · by_cases h : i' = i
      · subst h
        rw [hsi, hθX P]
        have hK : 0 ≤ Ki.coeff P := by
          by_contra hneg
          have hmem : P ∈ Ki.support := Finsupp.mem_support_iff.2 (by
            have : Ki.coeff P ≠ 0 := by omega
            simpa [DivisorWithCoeffs.coeff_apply] using this)
          exact hU₁O hP (Or.inr ⟨P.genericPoint, Set.mem_biUnion hmem (subset_closure rfl), rfl⟩)
        have hc := (MMP.Flips.NormalizationComponents.componentBoundaryCoeff_mem_Icc N hslc i' P).1
        have hK' : (0 : ℚ) ≤ Ki.coeff P := by exact_mod_cast hK
        push_cast
        positivity
      · exact absurd (hsne i' h) hs0
    · exact absurd (hU₁O hP) fun h => h (Or.inl
        ⟨_, MMP.Flips.IsDoubleNormalCrossingPoint.notMem_smoothLocus hnode, rfl⟩)
  obtain ⟨τ, hτ, hτres⟩ := hres4 U₁ hU₁aff s hsec
  have hmeet₁ : (Set.range j.base ∩ U₁).Nonempty := ⟨_, ⟨_, rfl⟩, hU₁⟩
  have hres₁i : MMP.Fourfold.IsPoincareResidue sS j 1 M τ θX := by
    have := hτres i hmeet₁
    simp only [hsi] at this
    exact this
  obtain ⟨ψ₁, rfl⟩ := exists_eq_unitValue_smul_of_isPoincareResidue hdimS hθ0 hres₁i
    (hres1 U₁ τ hτ i hmeet₁) hθX0
  set D' : Divisor S := D + principalDivisor ψ₁ with hD'
  -- `Cᵢ` is not in the support of `D'`
  have hB : ∀ Z : irreducibleComponents (N.X i),
      j.base (componentGenericPoint (N.X i) Z) ∉ D'.supp := by
    intro Z hZ
    obtain ⟨P, hPF, hPW⟩ := exists_primeDivisor_mem_open (sX := N.n i ≫ ι ≫ sS) hdimXi
      (j ⁻¹ᵁ U₁).isOpen hU₁ ((Ki.support : Set _) ∪ (Δi.support : Set _))
      (Ki.support.finite_toSet.union Δi.support.finite_toSet)
    have hK0 : Ki.coeff P = 0 := by
      by_contra h
      exact hPF (Or.inl (Finsupp.mem_support_iff.2 (by
        simpa [DivisorWithCoeffs.coeff_apply] using h)))
    have hΔ0 : N.componentBoundaryCoeff Δ i P = 0 := by
      rw [← hΔi]
      by_contra h
      exact hPF (Or.inr (Finsupp.mem_support_iff.2 (by
        simpa [DivisorWithCoeffs.coeff_apply] using h)))
    have hgen := coeff_add_ord_eq_zero_of_isResidues hdimX hdimS hθ0 hθ hcart hres1 hres2 hτ
      hτres i P hPW (by rw [hsi]; exact hθX0) (by rw [hsi, hθX P, hK0, hΔ0]; simp)
    obtain ⟨Q, hQ, hxQ⟩ := DivisorWithCoeffs.mem_supp_iff.1 hZ
    apply hQ
    have hsp : componentGenericPoint (N.X i) Z ⤳ P.genericPoint := by
      rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
      exact genericPoint_specializes _
    have hmem : j.base P.genericPoint ∈ Q.support :=
      (hsp.map j.base.hom.continuous).mem_closed
        (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure) hxQ
    rw [hD', DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
    exact hgen Q hmem
  have hD'c : D'.IsCartier := hcart.add (Divisor.isCartier_principalDivisor ψ₁)
  set E : Divisor (N.X i) := D'.pullback hD'c hB with hE
  -- the coefficientwise inequality
  have hineq : ∀ P : MMP.Mori.PrimeDivisor (N.X i),
      ((E.coeff P : ℤ) : ℚ) ≤ (M : ℚ) * Ki.coeff P + M * Δi.coeff P := by
    intro P
    set x := j.base P.genericPoint with hx
    obtain ⟨Ux, hxUx, φ₁, hφ₁⟩ := hcart x
    have hUxne : Ux ≠ ⊥ := fun h => by rw [h] at hxUx; exact hxUx
    set τx := unitValue φ₁⁻¹ • θ with hτxdef
    have hτx : τx ∈ pluricanonicalSections sS 2 (M : ℕ) Gm Ux :=
      unitValue_inv_smul_mem_pluricanonicalSections hdimS hθ0 hθ hUxne hφ₁
    have hmeetx : (Set.range j.base ∩ Ux).Nonempty := ⟨x, ⟨_, rfl⟩, hxUx⟩
    obtain ⟨ρx, hρx, hsecx⟩ := exists_isResidues_isResSection hres1 hres2 hτx
    have hsecx := hsecx.1 i P hxUx
    -- the local equation `φ₁ ψ₁` of `D'` near `x` and the pull-back coefficient
    have hloc : D'.IsLocalEquation Ux (φ₁ * ψ₁) :=
      hφ₁.add (Divisor.isLocalEquation_principalDivisor ψ₁ Ux)
    have hPE : (P.support ∩ j ⁻¹ᵁ Ux).Nonempty := (P.genericPoint_mem_iff (j ⁻¹ᵁ Ux)).mp hxUx
    have hEP := Divisor.isPullback_pullback hD'c hB Ux _ hloc P hPE
    have hZ := P.map_componentGenericPoint_mem j hPE
    obtain ⟨u0, hu0⟩ := hloc.exists_unit_stalk hZ (hB _) (mem_pointComponent _)
    rw [pullbackComponent_eq hB hloc hZ (mem_pointComponent _) u0 hu0, ordUnit_eq_ord] at hEP
    have hηc : genericPoint (N.X i) ⤳ componentGenericPoint (N.X i) P.component := by
      rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
    have hsp : j.base (genericPoint (N.X i)) ⤳ j.base (componentGenericPoint (N.X i) P.component) :=
      hηc.map j.base.hom.continuous
    set r := (S.presheaf.stalkSpecializes hsp).hom
      (u0 : S.presheaf.stalk (j.base (componentGenericPoint (N.X i) P.component))) with hrdef
    have hr : algebraMap _ S.functionField r = unitValue (φ₁ * ψ₁) := by
      rw [← stalkSpecializes_eq_unitValue (mem_pointComponent _) hu0, hrdef]
      change (S.presheaf.stalkSpecializes hsp ≫ S.presheaf.stalkSpecializes _).hom _ = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
    have hτeq : unitValue ψ₁ • θ = algebraMap _ S.functionField r • τx := by
      rw [hr, hτxdef, smul_smul, ← unitValue_mul, mul_comm φ₁ ψ₁, mul_inv_cancel_right]
    have hρ := isPoincareResidue_algebraMap_smul (hρx i hmeetx) r
    rw [← hτeq] at hρ
    have heq : θX = (j.stalkMap (genericPoint (N.X i))).hom r • ρx i :=
      (hres1 U₁ _ hτ i hmeet₁).unique hres₁i hρ
    have hρ0 : ρx i ≠ 0 := fun h0 => hθX0 (by rw [heq, h0, smul_zero])
    have hc0 : (j.stalkMap (genericPoint (N.X i))).hom r ≠ 0 := fun h0 =>
      hθX0 (by rw [heq, h0, zero_smul])
    have hord := P.ordForm_smul_of_topologicalKrullDim_eq (d := 1) (sX := N.n i ≫ ι ≫ sS)
      (by rw [hdimXi]; rfl) hc0 hρ0
    rw [← heq, hθX P] at hord
    have hcE : (j.stalkMap (genericPoint (N.X i))).hom r =
        (MMP.Positivity.componentToFunctionField P.component).hom
          ((j.stalkMap (componentGenericPoint (N.X i) P.component)).hom u0) :=
      Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ hηc
        (u0 : S.presheaf.stalk (j.base (componentGenericPoint (N.X i) P.component)))
    have hE' : E.coeff P = (N.X i).ord ((j.stalkMap (genericPoint (N.X i))).hom r)
        P.genericPoint := by
      rw [hcE]; exact hEP
    have hsecx' := hsecx hρ0
    rw [hΔi]
    have h1 : (((M : ℤ) * Ki.coeff P : ℤ) : ℚ) =
        ((N.X i).ord ((j.stalkMap (genericPoint (N.X i))).hom r) P.genericPoint : ℚ) +
          ((P.ordForm (ρx i) : ℤ) : ℚ) := by exact_mod_cast hord
    rw [← hE'] at h1
    push_cast at h1
    linarith
  -- the degree of `E` is the intersection number `M (K + B) · Cᵢ ≥ 0`
  have hdegE : (0 : ℤ) ≤ E.sum fun _ a => a := by
    have hsm : IsSmoothScheme (N.n i ≫ ι ≫ sS) :=
      MMP.Flips.NormalizationComponents.isSmoothScheme_n N hslc i
    haveI : IsProper sS := by
      haveI := hSp
      exact (inferInstance : AlgebraicGeometry.IsProperVariety k sS).toIsProper
    have hp : IsProper (N.n i ≫ ι ≫ sS) := (inferInstance : IsProper ((N.n i ≫ ι) ≫ sS))
    haveI := hp
    have hu : IsIso (MMP.Mori.smoothLocus (N.n i ≫ ι ≫ sS)).ι := by
      have h : MMP.Mori.smoothLocus (N.n i ≫ ι ≫ sS) = ⊤ := hsm
      generalize MMP.Mori.smoothLocus (N.n i ≫ ι ≫ sS) = U at h ⊢
      subst h
      rw [← Scheme.topIso_hom]
      infer_instance
    have hdim' : topologicalKrullDim (MMP.Mori.smoothLocus (N.n i ≫ ι ≫ sS)).toScheme ≤ 1 := by
      rw [IsHomeomorph.topologicalKrullDim_eq _
        (Scheme.homeoOfIso (asIso (MMP.Mori.smoothLocus (N.n i ≫ ι ≫ sS)).ι)).isHomeomorph,
        hdimXi]
    have h1 := MMP.Flips.degreeOn_smoothLocus_eq_sum hXi hsm hp hdimXi hdim' E
    rw [← h1]
    -- the curve `Γ = j(Cᵢ)` of `S`, contracted by `f`
    obtain ⟨e₀, he₀⟩ := exists_iso_curveSubschemeAt_of_isClosedImmersion j
    have hΓ : IsProperCurve sS (j.base (genericPoint (N.X i))) :=
      isProperCurve_of_isProper sS (by
        rw [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e₀).isHomeomorph]
        exact hdimXi)
    set Γ : ProperCurve sS := ⟨_, hΓ⟩ with hΓdef
    have hcon : Γ.IsContractedBy f := by
      intro x hx
      have hsub : closure {Γ.point} ⊆ Set.range j.base :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨_, rfl⟩) j.isClosedEmbedding.isClosed_range
      obtain ⟨y, rfl⟩ := hsub hx
      exact hcontr y
    haveI := hD'c.isInvertibleModule_divisorialSheaf
    haveI := hcart.isInvertibleModule_divisorialSheaf
    haveI := (MMP.Fourfold.isCartier_of_isSmoothScheme hsm E).isInvertibleModule_divisorialSheaf
    obtain ⟨e₁⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hD'c j hB
    have hdeg : E.degreeOn k (N.n i ≫ ι ≫ sS) (MMP.Mori.smoothLocus (N.n i ≫ ι ≫ sS)).ι hdim'
        (MMP.Fourfold.isCartier_of_isSmoothScheme hsm E) =
        D.degreeOn k sS Γ.ι Γ.dim_le hcart := by
      unfold Divisor.degreeOn
      rw [MMP.Mori.degreeOn_eq_of_iso k _ _ _ e₁,
        degreeOn_congr_structure (Category.assoc (N.n i) ι sS).symm,
        ← MMP.Threefold.Resolution.degreeOn_comp k sS j,
        MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sS _ Γ.ι hdim' Γ.dim_le
          (asIso (MMP.Mori.smoothLocus (N.n i ≫ ι ≫ sS)).ι ≪≫ e₀)
          (by rw [Iso.trans_hom, asIso_hom, Category.assoc]; exact congrArg _ he₀)]
      exact MMP.Mori.degreeOn_eq_of_iso k sS Γ.ι Γ.dim_le
        (Divisor.divisorialSheafMulIso ψ₁ fun Q => by
          rw [hD', DivisorWithCoeffs.coeff_add, coeff_principalDivisor])
    rw [hdeg]
    have hq := hnef.1
    have h0 := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sS hnef hq Γ hcon
    have hDq : Divisor.toQDivisor D = ((M : ℕ) : ℤ) • (Divisor.toQDivisor K + B) := by
      rw [hD, map_add, map_zsmul, hGm, smul_add]
      simp only [natCast_zsmul, Nat.cast_smul_eq_nsmul]
    rw [QDivisor.intersectionNumber_eq_of_smul k sS Γ.ι Γ.dim_le _ hq hM D hcart hDq] at h0
    have hMq : (0 : ℚ) < M := by exact_mod_cast hM
    have h2 : (0 : ℚ) ≤ (D.degreeOn k sS Γ.ι Γ.dim_le hcart : ℚ) := by
      rwa [le_div_iff₀ hMq, zero_mul] at h0
    exact_mod_cast h2
  -- summing up
  have hsumle : ((E.sum fun _ a => a : ℤ) : ℚ) ≤
      (M : ℚ) * ((Ki.sum fun _ a => (a : ℚ)) + Δi.sum fun _ a => a) := by
    have hcast : ∀ G : Divisor (N.X i), ((G.sum fun _ a => a : ℤ) : ℚ) =
        (Divisor.toQDivisor G).sum fun _ a => a := fun G => by
      have : Divisor.toQDivisor G = Finsupp.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero G := rfl
      rw [this, Finsupp.sum_mapRange_index (fun _ => rfl)]
      simp [Finsupp.sum]
    have hle := finsupp_sum_le (Divisor.toQDivisor E)
      ((M : ℚ) • Divisor.toQDivisor Ki + (M : ℚ) • Δi) fun P => by
        have h := hineq P
        simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact h
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_smul_index' (fun _ => rfl), Finsupp.sum_smul_index' (fun _ => rfl)] at hle
    simp only [smul_eq_mul] at hle
    rw [← Finsupp.mul_sum, ← Finsupp.mul_sum, ← hcast E, ← hcast Ki] at hle
    have hKq : ((Ki.sum fun _ a => a : ℤ) : ℚ) = Ki.sum fun _ a => (a : ℚ) := by
      simp [Finsupp.sum]
    rw [hKq] at hle
    linarith
  have hMpos : (0 : ℚ) < M := by exact_mod_cast hM
  have h0 : (0 : ℚ) ≤ ((E.sum fun _ a => a : ℤ) : ℚ) := by exact_mod_cast hdegE
  nlinarith

/-- **Sections of `ω_C^{⊗M}(MΔ)` over a neighbourhood of a point of the floor.** For a closed
point `t` of the floor there are an open `V ∋ f(t)` and a family `s` of forms on the components
which is a section of `ω_C^{⊗M}(MΔ)` over `f⁻¹ V`, nonzero on every component meeting it, with
finitely many bad closed points and good at `t`. -/
private theorem exists_residueSection {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {S Z C : Scheme.{0}} (sS : S ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [QuasiCompact sS]
    (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hZ : AlgebraicGeometry.IsProjectiveVariety k sZ)
    (f : S ⟶ Z) (hf : f ≫ sZ = sS)
    (ι : C ⟶ S) [IsClosedImmersion ι]
    {Δ : MMP.Flips.QWeilDivisor C} (hslc : MMP.Flips.IsSlcCurve (ι ≫ sS) Δ)
    (hΔ1 : ∀ Γ, Δ Γ < 1)
    {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
    (N : MMP.Flips.NormalizationComponents (ι ≫ sS) hC) [Finite N.ι]
    (hcl : ∀ i, IsClosedImmersion (N.n i ≫ ι))
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hden : ∀ Γ, ((m₀ : ℚ) * Δ Γ).den = 1)
    (hnefC : ∀ i, (∀ x, (N.n i ≫ ι ≫ f).base x = (N.n i ≫ ι ≫ f).base (genericPoint (N.X i))) →
      ∀ {Ki : Divisor (N.X i)}, Ki.IsCanonicalDivisor (N.n i ≫ ι ≫ sS) 1 →
      ∀ {Δi : QDivisor (N.X i)}, (∀ P, Δi.coeff P = N.componentBoundaryCoeff Δ i P) →
        0 ≤ (Ki.sum fun _ a => (a : ℚ)) + Δi.sum fun _ a => a)
    (t : C) (ht : IsClosed ({t} : Set C)) :
    ∃ V : Z.Opens, ι.base t ∈ f ⁻¹ᵁ V ∧
      ∃ s : ∀ i : N.ι, RationalPluriForms (N.n i ≫ ι ≫ sS) 1 (24 * m₀ : ℕ),
        IsResSection sS ι N Δ (24 * m₀) (f ⁻¹ᵁ V) s ∧
        (∀ i (z : N.X i), ι.base ((N.n i).base z) ∈ f ⁻¹ᵁ V → s i ≠ 0) ∧
        {y : C | ι.base y ∈ f ⁻¹ᵁ V ∧ IsClosed ({y} : Set C) ∧
          ¬ IsGoodPoint sS ι N Δ (24 * m₀) s y}.Finite ∧
        IsGoodPoint sS ι N Δ (24 * m₀) s t := by
  classical
  haveI : LocallyOfFiniteType (ι ≫ sS) := hslc.1.1.2.1
  haveI : QuasiCompact (ι ≫ sS) := hslc.1.1.2.2
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (ι ≫ sS)
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sS)
  haveI : IsReduced C := hslc.1.2.1
  -- the components
  have hCv : ∀ i, IsNormalVariety k (N.n i ≫ ι ≫ sS) := N.isNormalVariety
  have hsm : ∀ i, IsSmoothScheme (N.n i ≫ ι ≫ sS) := fun i =>
    MMP.Flips.NormalizationComponents.isSmoothScheme_n N hslc i
  have hdim : ∀ i, topologicalKrullDim (N.X i) = 1 := fun i =>
    MMP.Flips.NormalizationComponents.topologicalKrullDim_X N hslc.1 i
  haveI : IsProper sS := by
    haveI := hSp
    exact (inferInstance : AlgebraicGeometry.IsProperVariety k sS).toIsProper
  haveI : IsSeparated sZ := hZ.toIsSeparated
  haveI : IsProper f := by
    rw [← hf] at *
    exact IsProper.of_comp f sZ
  have hprop : ∀ i, IsProper (N.n i ≫ ι ≫ sS) := fun i => by
    haveI := hcl i
    exact (inferInstance : IsProper ((N.n i ≫ ι) ≫ sS))
  haveI : ∀ i, CompactSpace (N.X i) := fun i =>
    MMP.Flips.NormalizationComponents.compactSpace_X N hslc i
  have hfinn : ∀ i, IsFinite (N.n i) := fun i =>
    MMP.Flips.NormalizationComponents.isFinite_n N i
  -- the boundaries `Δᵢ`
  have hfinsupp : ∀ i, {P : MMP.Mori.PrimeDivisor (N.X i) |
      N.componentBoundaryCoeff Δ i P ≠ 0}.Finite := by
    intro i
    haveI := hfinn i
    set Zc : Set C := ((MMP.Mori.smoothLocus (ι ≫ sS) : C.Opens) : Set C)ᶜ with hZcdef
    have hZc : IsClosed Zc := (MMP.Mori.smoothLocus (ι ≫ sS)).isOpen.isClosed_compl
    haveI : LocallyOfFinitePresentation (ι ≫ sS) := inferInstance
    have hdense : Dense ((MMP.Mori.smoothLocus (ι ≫ sS) : C.Opens) : Set C) := by
      rw [MMP.Mori.smoothLocus_eq_smoothLocus]
      exact Scheme.Hom.dense_smoothLocus_of_perfectField _
    have hηsm : (N.n i).base (genericPoint (N.X i)) ∉ Zc := fun h =>
      h (map_genericPoint_mem_of_dense N i (MMP.Mori.smoothLocus (ι ≫ sS)).isOpen hdense)
    have hA1 : ((N.n i).base ⁻¹' Zc).Finite :=
      finite_of_isClosed_of_genericPoint_notMem (hdim i)
        (hZc.preimage (N.n i).base.hom.continuous) hηsm
    have hA2 : ((N.n i).base ⁻¹'
        ((fun Γ : MMP.Flips.WeilDivisorPrime C => Γ.1.genericPoint) '' (Δ.support : Set _))).Finite :=
      Scheme.Hom.finite_preimage _ (Δ.support.finite_toSet.image _)
    refine ((hA1.union hA2).preimage (f := fun P : MMP.Mori.PrimeDivisor (N.X i) => P.genericPoint)
      (fun a _ b _ h => AlgebraicGeometry.PrimeDivisor.genericPoint_injective h)).subset
      fun P hP => ?_
    simp only [Set.mem_setOf_eq] at hP
    unfold MMP.Flips.NormalizationComponents.componentBoundaryCoeff at hP
    split_ifs at hP with hnode
    · exact Or.inl (MMP.Flips.IsDoubleNormalCrossingPoint.notMem_smoothLocus hnode)
    · obtain ⟨Γ, hΓ, hΓ0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
      refine Or.inr ⟨Γ, hΓ, ?_⟩
      by_contra hne
      exact hΓ0 (if_neg (Ne.symm hne))
  let Δi : ∀ i, QDivisor (N.X i) := fun i =>
    Finsupp.ofSupportFinite (fun P => N.componentBoundaryCoeff Δ i P) (hfinsupp i)
  have hΔi : ∀ i P, (Δi i).coeff P = N.componentBoundaryCoeff Δ i P := fun i P => rfl
  have hΔic : ∀ i P, 0 ≤ (Δi i).coeff P ∧ (Δi i).coeff P ≤ 1 := fun i P => by
    rw [hΔi]
    exact MMP.Flips.NormalizationComponents.componentBoundaryCoeff_mem_Icc N hslc i P
  choose K hK using fun i => haveI := (hCv i).1
    MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (N.n i ≫ ι ≫ sS) (hsm i) (hdim i)
  -- the point `p = f(t)` and the contracted components
  set p := f.base (ι.base t) with hp
  have hpcl : IsClosed ({p} : Set Z) := by
    have h := (ι ≫ f).isClosedMap _ ht
    rwa [Set.image_singleton] at h
  -- three auxiliary points on every non-contracted component
  have hR'ex : ∀ i, ¬ (∀ x, (N.n i ≫ ι ≫ f).base x =
      (N.n i ≫ ι ≫ f).base (genericPoint (N.X i))) →
      ∃ R' : Finset (MMP.Mori.PrimeDivisor (N.X i)), R'.card = 3 ∧
        ∀ P ∈ R', (Δi i).coeff P = 0 ∧ (N.n i ≫ ι ≫ f).base P.genericPoint ≠ p := by
    intro i hnc
    haveI := (hCv i).1.toLocallyOfFiniteType
    have hinf := infinite_primeDivisor (sX := N.n i ≫ ι ≫ sS) (hdim i)
    have hA : {P : MMP.Mori.PrimeDivisor (N.X i) |
        (Δi i).coeff P = 0 ∧ (N.n i ≫ ι ≫ f).base P.genericPoint ≠ p}.Infinite := by
      have hco : {P : MMP.Mori.PrimeDivisor (N.X i) |
          (Δi i).coeff P = 0 ∧ (N.n i ≫ ι ≫ f).base P.genericPoint ≠ p}ᶜ ⊆
          {P | N.componentBoundaryCoeff Δ i P ≠ 0} ∪
            {P | (N.n i ≫ ι ≫ f).base P.genericPoint = p} := by
        intro P hP
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_not] at hP
        rcases hP with h | h
        · exact Or.inl (show N.componentBoundaryCoeff Δ i P ≠ 0 by rw [← hΔi]; exact h)
        · exact Or.inr h
      exact Set.infinite_of_finite_compl (((hfinsupp i).union
        (finite_setOf_map_eq (hdim i) (N.n i ≫ ι ≫ f) hpcl hnc)).subset hco)
    obtain ⟨R', hR'sub, hR'card⟩ := hA.exists_subset_card_eq 3
    exact ⟨R', hR'card, fun P hP => hR'sub hP⟩
  let R' : ∀ i, Finset (MMP.Mori.PrimeDivisor (N.X i)) := fun i =>
    if h : ∀ x, (N.n i ≫ ι ≫ f).base x = (N.n i ≫ ι ≫ f).base (genericPoint (N.X i)) then ∅
    else (hR'ex i h).choose
  -- the open `V`
  have himcl : ∀ i (P : MMP.Mori.PrimeDivisor (N.X i)),
      IsClosed ({(N.n i ≫ ι ≫ f).base P.genericPoint} : Set Z) := fun i P => by
    haveI := hcl i
    have hPcl : IsClosed ({P.genericPoint} : Set (N.X i)) :=
      Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint _ (hdim i)
        fun h => by
          have h1 := P.coheight_genericPoint
          rw [h, show genericPoint (N.X i) = (⊤ : N.X i) from rfl, Order.coheight_top] at h1
          exact zero_ne_one h1
    have h := ((N.n i ≫ ι) ≫ f).isClosedMap _ hPcl
    rwa [Set.image_singleton] at h
  let bad : Set Z := ⋃ i, ⋃ P ∈ (R' i : Set (MMP.Mori.PrimeDivisor (N.X i))),
    {(N.n i ≫ ι ≫ f).base P.genericPoint}
  have hbadcl : IsClosed bad := by
    haveI : Finite N.ι := inferInstance
    exact isClosed_iUnion_of_finite fun i => (R' i).finite_toSet.isClosed_biUnion
      fun P _ => himcl i P
  have hpbad : p ∉ bad := by
    simp only [bad, Set.mem_iUnion, Set.mem_singleton_iff, not_exists]
    intro i P hP hPp
    by_cases h : ∀ x, (N.n i ≫ ι ≫ f).base x = (N.n i ≫ ι ≫ f).base (genericPoint (N.X i))
    · simp only [R', dif_pos h, Finset.coe_empty, Set.mem_empty_iff_false] at hP
    · simp only [R', dif_neg h] at hP
      exact ((hR'ex i h).choose_spec.2 P hP).2 hPp.symm
  let V : Z.Opens := ⟨badᶜ, hbadcl.isOpen_compl⟩
  have hR'V : ∀ i (P : MMP.Mori.PrimeDivisor (N.X i)), P ∈ R' i →
      ι.base ((N.n i).base P.genericPoint) ∉ f ⁻¹ᵁ V :=
    fun i P hP hPV => hPV (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion₂.2 ⟨P, hP, rfl⟩⟩)
  -- prime divisors over `t`
  have hTfin : ∀ i, {P : MMP.Mori.PrimeDivisor (N.X i) | (N.n i).base P.genericPoint = t}.Finite :=
    fun i => by
      haveI := hfinn i
      exact (Scheme.Hom.finite_preimage (N.n i) (Set.finite_singleton t)).preimage
        (fun a _ b _ h => AlgebraicGeometry.PrimeDivisor.genericPoint_injective h)
  have hP₀ : ∀ i, Nonempty (MMP.Mori.PrimeDivisor (N.X i)) := fun i => by
    haveI := (hCv i).1.toLocallyOfFiniteType
    haveI := infinite_primeDivisor (sX := N.n i ≫ ι ≫ sS) (hdim i)
    infer_instance
  -- the section on one component meeting `f⁻¹ V`
  have hcomp : ∀ i, ∃ si : RationalPluriForms (N.n i ≫ ι ≫ sS) 1 (24 * m₀ : ℕ), si ≠ 0 ∧
      (∀ P : MMP.Mori.PrimeDivisor (N.X i), ι.base ((N.n i).base P.genericPoint) ∈ f ⁻¹ᵁ V →
        0 ≤ ((P.ordForm si : ℤ) : ℚ) + (24 * m₀ : ℕ) * N.componentBoundaryCoeff Δ i P) ∧
      (∀ P : MMP.Mori.PrimeDivisor (N.X i), ι.base ((N.n i).base P.genericPoint) ∈ f ⁻¹ᵁ V →
        N.componentBoundaryCoeff Δ i P = 1 → N.IsLeadingCoeff i P si 1) ∧
      (∀ P : MMP.Mori.PrimeDivisor (N.X i), (N.n i).base P.genericPoint = t →
        ((P.ordForm si : ℤ) : ℚ) + (24 * m₀ : ℕ) * N.componentBoundaryCoeff Δ i P = 0) ∧
      {P : MMP.Mori.PrimeDivisor (N.X i) |
        ((P.ordForm si : ℤ) : ℚ) + (24 * m₀ : ℕ) * N.componentBoundaryCoeff Δ i P ≠ 0}.Finite := by
    intro i
    have hR'0 : ∀ P ∈ R' i, (Δi i).coeff P = 0 := by
      intro P hP
      by_cases h : ∀ x, (N.n i ≫ ι ≫ f).base x = (N.n i ≫ ι ≫ f).base (genericPoint (N.X i))
      · simp only [R', dif_pos h, Finset.notMem_empty] at hP
      · simp only [R', dif_neg h] at hP
        exact ((hR'ex i h).choose_spec.2 P hP).1
    set Δ' : QDivisor (N.X i) := Δi i + ∑ r ∈ R' i, Finsupp.single r 1 with hΔ'
    have hΔ'c : ∀ P, Δ'.coeff P = (Δi i).coeff P + if P ∈ R' i then 1 else 0 := by
      intro P
      simp only [hΔ', DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.finset_sum_apply,
        Finsupp.single_apply]
      rw [Finset.sum_ite_eq']
    have hΔ'0 : Δ'.IsEffective := fun P => by
      rw [hΔ'c]; split_ifs <;> linarith [(hΔic i P).1]
    have hΔ'1 : ∀ P, Δ'.coeff P ≤ 1 := fun P => by
      rw [hΔ'c]; split_ifs with h
      · rw [hR'0 P h]; norm_num
      · simpa using (hΔic i P).2
    obtain ⟨G'', hG''⟩ : ∃ G'' : Divisor (N.X i), Divisor.toQDivisor G'' = (m₀ : ℤ) • Δ' :=
      MMP.Flips.NormalizationComponents.exists_divisor_eq_smul Δ' m₀ fun P => by
        obtain ⟨a, ha⟩ := MMP.Flips.NormalizationComponents.exists_int_eq_mul_componentBoundaryCoeff
          N hden i P
        refine ⟨a + if P ∈ R' i then m₀ else 0, ?_⟩
        rw [hΔ'c, hΔi, mul_add, ← ha]
        split_ifs <;> push_cast <;> ring
    have hdeg : 0 ≤ ((K i).sum fun _ a => (a : ℚ)) + Δ'.sum fun _ a => a := by
      by_cases hc : ∀ x, (N.n i ≫ ι ≫ f).base x = (N.n i ≫ ι ≫ f).base (genericPoint (N.X i))
      · have hR'e : R' i = ∅ := by simp only [R', dif_pos hc]
        have hΔ'e : Δ' = Δi i := by rw [hΔ', hR'e, Finset.sum_empty, add_zero]
        rw [hΔ'e]
        exact hnefC i hc (hK i) (hΔi i)
      · have hcard : (R' i).card = 3 := by
          simp only [R', dif_neg hc]; exact (hR'ex i hc).choose_spec.1
        have hKs : (-2 : ℚ) ≤ (K i).sum fun _ a => (a : ℚ) := by
          rw [MMP.Flips.sum_coeff_canonical_eq (hCv i) (hsm i) (hprop i) (hK i)]
          have : (0 : ℚ) ≤ ((K i).h0 k (N.n i ≫ ι ≫ sS) : ℚ) := Nat.cast_nonneg _
          linarith
        have hΔs : (0 : ℚ) ≤ (Δi i).sum fun _ a => a :=
          Finsupp.sum_nonneg fun P _ => (hΔic i P).1
        have hsum : (Δ'.sum fun _ a => a) = ((Δi i).sum fun _ a => a) + (R' i).card := by
          rw [hΔ', Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
            ← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
          simp
        rw [hsum, hcard]
        push_cast
        linarith
    let P₀ : MMP.Mori.PrimeDivisor (N.X i) := Classical.arbitrary _
    let R : Finset (MMP.Mori.PrimeDivisor (N.X i)) := (hTfin i).toFinset ∪ {P₀}
    obtain ⟨si, hsi0, hmem, hlead, hexact⟩ := exists_curveSection (hCv i) (hsm i) (hprop i)
      (hdim i) (hK i) hm₀ hΔ'0 hΔ'1 hG'' hdeg R ⟨P₀, Finset.mem_union_right _
        (Finset.mem_singleton_self _)⟩
    -- the coefficients of `24 G''`
    have hG24 : ∀ P, ((((24 : ℤ) • G'').coeff P : ℤ) : ℚ) = (24 * m₀ : ℕ) * Δ'.coeff P := by
      intro P
      have h1 := congrArg (fun D => DivisorWithCoeffs.coeff D P) hG''
      simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h1
      simp only [DivisorWithCoeffs.coeff_smul, smul_eq_mul]
      push_cast
      rw [h1]; push_cast; ring
    have hcoV : ∀ P : MMP.Mori.PrimeDivisor (N.X i),
        ι.base ((N.n i).base P.genericPoint) ∈ f ⁻¹ᵁ V → Δ'.coeff P = N.componentBoundaryCoeff Δ i P :=
      fun P hP => by
        rw [hΔ'c, if_neg fun h => hR'V i P h hP, add_zero, hΔi]
    have htV : ι.base t ∈ f ⁻¹ᵁ V := hpbad
    refine ⟨si, hsi0, fun P hP => ?_, fun P hP h1 => ?_, fun P hP => ?_, ?_⟩
    · have h := hmem.2 P ⟨P.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
        trivial⟩ hsi0
      have hq : (0 : ℚ) ≤ ((P.ordForm si : ℤ) : ℚ) + ((((24 : ℤ) • G'').coeff P : ℤ) : ℚ) := by
        exact_mod_cast h
      rw [hG24, hcoV P hP] at hq
      exact hq
    · obtain ⟨z, hz, hz'⟩ := hlead P (by rw [hcoV P hP, h1])
      refine ⟨z, hz, ?_⟩
      rw [map_one, one_smul]
      exact hz'
    · have hPR : P ∈ R := Finset.mem_union_left _ ((hTfin i).mem_toFinset.2 hP)
      have h := hexact P hPR
      have hq : ((P.ordForm si : ℤ) : ℚ) + ((((24 : ℤ) • G'').coeff P : ℤ) : ℚ) = 0 := by
        exact_mod_cast h
      rw [hG24, hcoV P (by rw [hP]; exact htV)] at hq
      exact hq
    · haveI := (hCv i).1.toLocallyOfFiniteType
      refine ((MMP.Mori.finite_ordForm_ne_zero si).union (hfinsupp i)).subset fun P hP => ?_
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
      apply hP
      rw [hc.1, hc.2]; simp
  choose s hs0 hsord hslead hst hsfin using hcomp
  refine ⟨V, hpbad, s, ⟨fun i P hP _ => hsord i P hP, ?_⟩, fun i _ _ => hs0 i, ?_, ?_⟩
  · -- the nodes: leading coefficient one on both branches
    intro i j P P' hPP' hPV hnode _
    have hc1 : ∀ (i : N.ι) (P : MMP.Mori.PrimeDivisor (N.X i)),
        MMP.Flips.IsDoubleNormalCrossingPoint (ι ≫ sS) 1 ((N.n i).base P.genericPoint) →
        N.componentBoundaryCoeff Δ i P = 1 := fun i P h => by
      unfold MMP.Flips.NormalizationComponents.componentBoundaryCoeff; rw [if_pos h]
    refine ⟨1, hslead i P hPV (hc1 i P hnode), hslead j P' (hPP' ▸ hPV) (hc1 j P' (hPP' ▸ hnode))⟩
  · -- finitely many bad points
    refine ((Set.finite_range fun i => (N.n i).base (genericPoint (N.X i))).union
      (Set.finite_iUnion fun i => (hsfin i).image fun P => (N.n i).base P.genericPoint)).subset ?_
    rintro y ⟨-, -, hng⟩
    unfold IsGoodPoint at hng
    push Not at hng
    obtain ⟨i, z, hz, hzbad⟩ := hng
    by_cases hzη : z = genericPoint (N.X i)
    · exact Or.inl ⟨i, by show (N.n i).base (genericPoint (N.X i)) = y; rw [← hzη]; exact hz⟩
    · right
      have hco := MMP.Fourfold.coheight_eq_one_of_ne_genericPoint (hdim i) hzη
      have hgz : MMP.Mori.PrimeDivisor.genericPoint
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hco) = z :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      refine Set.mem_iUnion.2 ⟨i, AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hco, ?_, ?_⟩
      · exact hzbad _ hgz (hs0 i)
      · show (N.n i).base (MMP.Mori.PrimeDivisor.genericPoint _) = y
        rw [hgz, hz]
  · -- the point `t` is good
    intro i z hz
    have hzη : z ≠ genericPoint (N.X i) := by
      intro hzη
      haveI := hfinn i
      have hall : ∀ x : N.X i, (N.n i).base x = t := by
        intro x
        have hx : x ∈ (N.n i).base ⁻¹' {t} := by
          have h1 : closure ({genericPoint (N.X i)} : Set (N.X i)) ⊆ (N.n i).base ⁻¹' {t} :=
            (ht.preimage (N.n i).base.hom.continuous).closure_subset_iff.2
              (Set.singleton_subset_iff.2 (by rw [← hzη]; exact hz))
          rw [(genericPoint_spec (N.X i)).def] at h1
          exact h1 trivial
        exact hx
      haveI := (hCv i).1.toLocallyOfFiniteType
      have hinf := infinite_primeDivisor (sX := N.n i ≫ ι ≫ sS) (hdim i)
      have hfin : Set.Finite (Set.univ : Set (MMP.Mori.PrimeDivisor (N.X i))) :=
        (hTfin i).subset fun P _ => hall P.genericPoint
      exact (Set.infinite_univ_iff.2 hinf) hfin
    have hco := MMP.Fourfold.coheight_eq_one_of_ne_genericPoint (hdim i) hzη
    have hgz : MMP.Mori.PrimeDivisor.genericPoint
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hco) = z :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hco, hgz, hs0 i,
      hst i _ (by rw [hgz, hz])⟩

/-! ### The local construction at a closed point of the floor -/

/-- **The local construction.** At a closed point `t` of the floor there are an open `V ∋ f(t)` of
`Z`, a section of `ι^* 𝒪_S(D)` over the inverse image of `V`, and a generator of `𝒪_S(D)` at `t`
on a neighbourhood `U ⊆ f⁻¹ V` restricting to it. -/
private theorem exists_local_data {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {S Z C : Scheme.{0}} (sS : S ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [QuasiCompact sS]
    (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hZ : AlgebraicGeometry.IsProjectiveVariety k sZ)
    (f : S ⟶ Z) (hf : f ≫ sZ = sS) (K : Divisor S) (B : QDivisor S)
    (hdlt : IsDltPair sS 2 K B)
    (hnef : QDivisor.IsRelativelyNef sS f (Divisor.toQDivisor K + B))
    (ι : C ⟶ S) [IsClosedImmersion ι] (hιker : ι.ker = B.roundDown.suppIdeal)
    {Δ : MMP.Flips.QWeilDivisor C} (hslc : MMP.Flips.IsSlcCurve (ι ≫ sS) Δ)
    (hΔ1 : ∀ Γ, Δ Γ < 1)
    (hnode : ∀ Γ ∈ Δ.support,
      ¬ MMP.Flips.IsDoubleNormalCrossingPoint (ι ≫ sS) 1 Γ.1.genericPoint)
    {hC : ∀ V : C.Opens, IsCompact (V : Set C) → (irreducibleComponents V).Finite}
    (N : MMP.Flips.NormalizationComponents (ι ≫ sS) hC) [Finite N.ι]
    (hcl : ∀ i, IsClosedImmersion (N.n i ≫ ι))
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hden : ∀ Γ, ((m₀ : ℚ) * Δ Γ).den = 1)
    (Gm : Divisor S) (hGm : Divisor.toQDivisor Gm = ((24 * m₀ : ℕ) : ℚ) • B)
    (hcart : (((24 * m₀ : ℕ) : ℤ) • K + Gm).IsCartier)
    (hsec : ∀ U : S.Opens,
      (∀ τ ∈ pluricanonicalSections sS 2 (24 * m₀ : ℕ) Gm U, ∀ i,
        (Set.range (N.n i ≫ ι).base ∩ U).Nonempty →
        ∃! ρ, MMP.Fourfold.IsPoincareResidue sS (N.n i ≫ ι) 1 (24 * m₀) τ ρ) ∧
      (∀ τ ∈ pluricanonicalSections sS 2 (24 * m₀ : ℕ) Gm U, ∀ ρ,
        IsResidues sS ι N (24 * m₀) U τ ρ → IsResSection sS ι N Δ (24 * m₀) U ρ) ∧
      (∀ τ ∈ pluricanonicalSections sS 2 (24 * m₀ : ℕ) Gm U,
        IsResidues sS ι N (24 * m₀) U τ 0 ↔
          τ ∈ pluricanonicalSections sS 2 (24 * m₀ : ℕ) (Gm - B.roundDown) U) ∧
      (IsAffineOpen U → ∀ s, IsResSection sS ι N Δ (24 * m₀) U s →
        ∃ τ ∈ pluricanonicalSections sS 2 (24 * m₀ : ℕ) Gm U,
          IsResidues sS ι N (24 * m₀) U τ s))
    (t : C) (ht : IsClosed ({t} : Set C)) :
    haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
    ∃ (V : Z.Opens) (σ : Γ((Scheme.Modules.pullback ι).obj
        (((24 * m₀ : ℕ) : ℤ) • K + Gm).divisorialSheaf, (ι ≫ f) ⁻¹ᵁ V))
      (U : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (ψ : (RationalFunctions S)ˣ)
      (hψ : ∀ P : MMP.Mori.PrimeDivisor S, (P.support ∩ U).Nonempty →
        0 ≤ (((24 * m₀ : ℕ) : ℤ) • K + Gm).coeff P + P.ord ψ),
      ι t ∈ U ∧ (∀ P : MMP.Mori.PrimeDivisor S, ι t ∈ P.support →
        (((24 * m₀ : ℕ) : ℤ) • K + Gm).coeff P + P.ord ψ = 0) ∧
      ((Scheme.Modules.pullback ι).obj
          (((24 * m₀ : ℕ) : ℤ) • K + Gm).divisorialSheaf).presheaf.map
          (homOfLE (fun x hx => hUV hx : ι ⁻¹ᵁ U ≤ (ι ≫ f) ⁻¹ᵁ V)).op σ =
        ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app
          (((24 * m₀ : ℕ) : ℤ) • K + Gm).divisorialSheaf).app U
          (MMP.Fourfold.divisorialSectionOfUnit ψ hψ) := by
  classical
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have hX : IsNormalVariety k sS := hdlt.1.1
  haveI : LocallyOfFiniteType sS := hX.1.toLocallyOfFiniteType
  have hdimS : topologicalKrullDim S = 2 := hdlt.1.2.1.1
  haveI : IsReduced C := hslc.1.2.1
  haveI : LocallyOfFiniteType (ι ≫ sS) := hslc.1.1.2.1
  haveI : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace (ι ≫ sS)
  have hsurj : ∀ c : C, ∃ i, ∃ z : N.X i, (N.n i).base z = c := exists_n_eq N
  have hdimX : ∀ i, topologicalKrullDim (N.X i) = 1 := fun i =>
    MMP.Flips.NormalizationComponents.topologicalKrullDim_X N hslc.1 i
  obtain ⟨θ, hθ0, hθ⟩ : ∃ θ : RationalPluriForms sS 2 (24 * m₀ : ℕ), θ ≠ 0 ∧
      ∀ Γ : MMP.Mori.PrimeDivisor S, Γ.ordForm θ = ((24 * m₀ : ℕ) : ℤ) * K.coeff Γ := by
    obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hdlt.1.2.1
    obtain ⟨θ, hθ0, hθ⟩ := exists_pow_form (d := 2) (by rw [hdimS]; rfl) hω0 (24 * m₀)
      (by positivity)
    exact ⟨θ, hθ0, fun Γ => by rw [hθ Γ, hω Γ]⟩
  have hnefC : ∀ i, (∀ x, (N.n i ≫ ι ≫ f).base x =
        (N.n i ≫ ι ≫ f).base (genericPoint (N.X i))) →
      ∀ {Ki : Divisor (N.X i)}, Ki.IsCanonicalDivisor (N.n i ≫ ι ≫ sS) 1 →
      ∀ {Δi : QDivisor (N.X i)}, (∀ P, Δi.coeff P = N.componentBoundaryCoeff Δ i P) →
        0 ≤ (Ki.sum fun _ a => (a : ℚ)) + Δi.sum fun _ a => a :=
    fun i hcontr _ hKi _ hΔi =>
      sum_nonneg_of_isContracted sS hSp f K B hdlt hnef ι hslc N hcl (by positivity) Gm hGm
        hcart (fun U => (hsec U).1) (fun U => (hsec U).2.1) (fun U => (hsec U).2.2.2) hdimX i
        hcontr hKi hΔi
  obtain ⟨V, htV, s, hsV, hs_ne, hZ₀, hgood⟩ := exists_residueSection sS sZ hSp hZ f hf ι hslc
    hΔ1 N hcl hm₀ hden hnefC t ht
  obtain ⟨σ, U, hUV, ψ, hψ, hU, hgen, hσ⟩ := exists_local_data_of_sections hcl hsurj hdimX hdimS
    hθ0 hθ hcart (fun U => (hsec U).1) (fun U => (hsec U).2.1) (fun U => (hsec U).2.2.2) f V s
    hsV hs_ne hZ₀ t htV hgood
  exact ⟨V, σ, U, hUV, ψ, hψ, hU, hgen, hσ⟩

/-- For a `ℚ`-factorial dlt surface pair with `K + B` nef over `Z`, some multiple `m(K + B)` is
Cartier and its restriction to `⌊B⌋` is globally generated over `Z`. -/
private theorem exists_epi_counit_pullback_suppScheme_of_isDltPair_of_isRelativelyNef
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {S Z : Scheme.{0}} (sS : S ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [QuasiCompact sS]
    (hSp : AlgebraicGeometry.IsProjectiveVariety k sS)
    (hZ : AlgebraicGeometry.IsProjectiveVariety k sZ)
    (f : S ⟶ Z) (hf : f ≫ sZ = sS) (K : Divisor S) (B : QDivisor S)
    (hdlt : IsDltPair sS 2 K B) (hQ : MMP.Fourfold.IsQFactorial sS)
    (hnef : QDivisor.IsRelativelyNef sS f (Divisor.toQDivisor K + B)) :
    ∃ m : ℕ, 0 < m ∧ ∃ Dm : Divisor S,
      Divisor.toQDivisor Dm = (m : ℚ) • (Divisor.toQDivisor K + B) ∧ Dm.IsCartier ∧
      Epi ((Scheme.Modules.pullbackPushforwardAdjunction
          (B.roundDown.suppIdeal.subschemeι ≫ f)).counit.app
        ((Scheme.Modules.pullback B.roundDown.suppIdeal.subschemeι).obj Dm.divisorialSheaf)) := by
  classical
  have hιker : B.roundDown.suppIdeal.subschemeι.ker = B.roundDown.suppIdeal :=
    Scheme.IdealSheafData.ker_subschemeι _
  obtain ⟨Δ, hslc, hΔ1, hnode, hres⟩ :=
    Residue.exists_isSlcCurve_and_isPoincareResidue_of_isDltPair sS hSp K B hdlt hQ
      B.roundDown.suppIdeal.subschemeι hιker
  have hC : ∀ V : B.roundDown.suppIdeal.subscheme.Opens,
      IsCompact (V : Set B.roundDown.suppIdeal.subscheme) →
      (irreducibleComponents V).Finite := by
    haveI : LocallyOfFiniteType sS := hSp.toIsVariety.toLocallyOfFiniteType
    exact AlgebraicGeometry.finite_irreducibleComponents_of_locallyOfFiniteType k
      (B.roundDown.suppIdeal.subschemeι ≫ sS)
  haveI : IsSeparated (B.roundDown.suppIdeal.subschemeι ≫ sS) := hslc.1.1.1
  haveI : LocallyOfFiniteType (B.roundDown.suppIdeal.subschemeι ≫ sS) := hslc.1.1.2.1
  haveI : QuasiCompact (B.roundDown.suppIdeal.subschemeι ≫ sS) := hslc.1.1.2.2
  obtain ⟨N⟩ : Nonempty (MMP.Flips.NormalizationComponents
      (B.roundDown.suppIdeal.subschemeι ≫ sS) hC) := nonempty_normalizationComponents _ hC
  obtain ⟨hcl, m₀, hm₀, hev, hm⟩ := hres hC N
  obtain ⟨-, Gm, hGm, hcart, hsec⟩ := hm (24 * m₀) (by positivity) (dvd_mul_left _ _)
  haveI : Finite N.ι := by
    haveI : LocallyOfFiniteType (B.roundDown.suppIdeal.subschemeι ≫ sS) :=
      hslc.1.1.2.1
    haveI : CompactSpace B.roundDown.suppIdeal.subscheme :=
      QuasiCompact.compactSpace_of_compactSpace (B.roundDown.suppIdeal.subschemeι ≫ sS)
    exact finite_ι N
  have hdenm₀ := (hm m₀ hm₀ dvd_rfl).1
  refine ⟨24 * m₀, by positivity, ((24 * m₀ : ℕ) : ℤ) • K + Gm, ?_, hcart, ?_⟩
  · rw [map_add, map_zsmul, hGm, smul_add]
    congr 1
  · haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
    refine epi_counit_comp_of_forall_exists _ f _ fun t => ?_
    haveI : JacobsonSpace B.roundDown.suppIdeal.subscheme :=
      LocallyOfFiniteType.jacobsonSpace (B.roundDown.suppIdeal.subschemeι ≫ sS)
    obtain ⟨t', htt', ht'⟩ := nonempty_inter_closedPoints (Z := closure {t})
      ⟨t, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    have hspec : t ⤳ t' := specializes_iff_mem_closure.2 htt'
    obtain ⟨V, σ, U, hUV, ψ, hψ, hU, hψt, hσ⟩ := exists_local_data sS sZ hSp hZ f hf K B hdlt
      hnef _ hιker hslc hΔ1 hnode N hcl hm₀ hdenm₀ Gm hGm hcart hsec t' ht'
    refine ⟨V, σ, U, hUV, ψ, hψ, ?_, fun P hP => hψt P ?_, hσ⟩
    · exact (hspec.map B.roundDown.suppIdeal.subschemeι.base.hom.continuous).mem_open U.isOpen hU
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hP ⊢
      exact (hspec.map B.roundDown.suppIdeal.subschemeι.base.hom.continuous).mem_closed
        isClosed_closure hP

end Floor

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold Filter _root_.Topology

/-! ### Semiampleness and relatively free multiples -/

section WeilOfCartier

open Opposite MMP.Intersection

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

private theorem genericPoint_specializes (C : irreducibleComponents Y) :
    genericPoint Y ⤳ componentGenericPoint Y C :=
  (genericPoint_spec Y).specializes trivial

/-- The order of a regular function at a point of coheight one is the length of its quotient. -/
private theorem scheme_ord_algebraMap {z : Y} (hz : Order.coheight z = 1)
    {a : Y.presheaf.stalk z} (ha : a ≠ 0) :
    Y.ord (algebraMap (Y.presheaf.stalk z) Y.functionField a) z = (Ring.ord _ a).toNat := by
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have hne : algebraMap (Y.presheaf.stalk z) Y.functionField a ≠ 0 := by
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff]
  rw [Scheme.ord_eq_iff hz hne]
  unfold Scheme.ordHom
  rw [Ring.ordFrac_eq_ord _ ha]
  have hnzd : a ∈ nonZeroDivisors _ := mem_nonZeroDivisors_of_ne_zero ha
  exact Ring.ordMonoidWithZeroHom_eq_coe (R := Y.presheaf.stalk z) hnzd
    (ENat.natCast_toNat (Ring.ord_ne_top hnzd)).symm

/-- On an integral locally Noetherian scheme, a point of coheight zero lies in the support of no
Cartier divisor. -/
private theorem notMem_cartierSupport_of_coheight_eq_zero (A : Y.CartierDivisor) {x : Y}
    (hx : Order.coheight x = 0) : x ∉ cartierSupport A := by
  have : Ring.KrullDimLE 0 (Y.presheaf.stalk x) := krullDimLE_of_coheight_le (by simp [hx])
  have : IsArtinianRing (Y.presheaf.stalk x) := isArtinianRing_iff_krullDimLE_zero.mpr this
  exact notMem_cartierSupport_of_isArtinianRing A x

/-- Every Cartier divisor on a Noetherian integral scheme has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier [TopologicalSpace.NoetherianSpace Y]
    (A : Y.CartierDivisor) : ∃ w : Divisor Y, IsWeilDivisorOfCartier A w := by
  have hfin := MMP.Mori.finite_setOf_genericPoint_mem (isClosed_cartierSupport A)
    (fun s hs h0 => notMem_cartierSupport_of_coheight_eq_zero A h0 hs)
  refine ⟨Finsupp.ofSupportFinite (fun P => primeDivisorOrder P A) (hfin.subset fun P hP => ?_),
    fun P => ?_⟩
  · by_contra h
    have hg : (primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset fun h' => h ?_)
    show P.genericPoint ∈ cartierSupport A
    rw [← hg]
    exact genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact isOrderAlong_primeDivisorOrder A P

variable [IsNormal Y]

/-- `v_P` on the factor `𝒪_{Y,η}` of `K(Y)` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation (P : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y P.component)) :
    P.valuation s = (P.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes P.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

/-- The principal Cartier divisor of a nonzero rational function `r` has order `ord_Q r` along
every prime divisor `Q`. -/
private theorem primeDivisorOrder_principalDivisor_functionField {r : Y.functionField}
    (hr : r ≠ 0) (Q : MMP.Mori.PrimeDivisor Y) :
    primeDivisorOrder Q (MMP.Intersection.principalDivisor
      (Units.map (MMP.CartierDivisorSheaf.ofFunctionField
        (X := Y) ⊤).toMonoidHom (Units.mk0 r hr))) = Scheme.ord r Q.genericPoint := by
  set c : (Y.totalQuotientSheaf.obj.obj (Opposite.op ⊤))ˣ :=
    Units.map (MMP.CartierDivisorSheaf.ofFunctionField (X := Y) ⊤).toMonoidHom
      (Units.mk0 r hr) with hc
  obtain ⟨⟨a, b⟩, hab⟩ :=
    IsLocalization.surj (nonZeroDivisors (Y.presheaf.stalk Q.genericPoint)) r
  have hbK : algebraMap _ Y.functionField (b : Y.presheaf.stalk Q.genericPoint) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact mul_ne_zero hr hbK hab
  have hfrac : IsFraction (Y.totalQuotientSheaf.presheaf.germ ⊤ Q.genericPoint trivial (c : _))
      a b := by
    refine ⟨isUnit_stalkToTotalQuotient_of_mem_nonZeroDivisors b.2, ?_⟩
    apply (totalQuotientStalkToFunctionField_bijective Q.genericPoint).1
    rw [map_mul, totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      totalQuotientStalkToFunctionField_stalkToTotalQuotient]
    erw [MMP.CartierDivisorSheaf.totalQuotientStalkToFunctionField_germ_top_ofFunctionField]
    rw [mul_comm]
    exact hab
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk (primeDivisorSubvariety Q).genericPoint) :=
    krullDimLE_of_coheight_le Q.coheight_genericPoint.le
  rw [(isOrderAlong_of_isFraction (V := primeDivisorSubvariety Q)
    ⟨⊤, trivial, c, isLocalEquationOn_principalDivisor c, rfl⟩
    (mem_nonZeroDivisors_of_ne_zero ha0) b.2 hfrac).primeDivisorOrder_eq]
  have h1 := Scheme.ord_mul (x := Q.genericPoint) hr hbK
  rw [hab, scheme_ord_algebraMap Q.coheight_genericPoint ha0,
    scheme_ord_algebraMap Q.coheight_genericPoint (nonZeroDivisors.ne_zero b.2)] at h1
  change ((Ring.ord _ a).toNat : ℤ) -
    ((Ring.ord _ (b : Y.presheaf.stalk Q.genericPoint)).toNat : ℤ) = _
  omega

/-- A principal divisor is the Weil divisor of the principal Cartier divisor of the same
rational function. -/
private theorem exists_isWeilDivisorOfCartier_principalDivisor [CompactSpace Y]
    (φ : (RationalFunctions Y)ˣ) :
    ∃ A : Y.CartierDivisor, IsWeilDivisorOfCartier A (MMP.Mori.principalDivisor φ) := by
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents Y) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  have : Subsingleton (irreducibleComponents Y) :=
    (irreducibleComponents_eq_singleton (X := Y) ▸ Set.subsingleton_singleton).coe_sort
  set r₀ : Y.functionField := (Y.presheaf.stalkSpecializes (genericPoint_specializes Z₀)).hom
    ((φ : RationalFunctions Y) Z₀)
  have hr0 : r₀ ≠ 0 :=
    ((φ.isUnit.map (Pi.evalMonoidHom (fun C : irreducibleComponents Y =>
      Y.presheaf.stalk (componentGenericPoint Y C)) Z₀)).map
        (Y.presheaf.stalkSpecializes (genericPoint_specializes Z₀)).hom).ne_zero
  refine ⟨MMP.Intersection.principalDivisor (Units.map
    (MMP.CartierDivisorSheaf.ofFunctionField (X := Y) ⊤).toMonoidHom
      (Units.mk0 r₀ hr0)), fun Q => ?_⟩
  have hord : Q.ord φ = Scheme.ord r₀ Q.genericPoint := by
    have h := valuation_eq_inv_divisorialValuation Q ((φ : RationalFunctions Y) Q.component)
    obtain rfl := Subsingleton.elim Q.component Z₀
    rw [Q.valuation_component,
      MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hr0, ← WithZero.exp_neg,
      neg_neg] at h
    exact WithZero.exp_injective h
  rw [coeff_principalDivisor, hord, ← primeDivisorOrder_principalDivisor_functionField hr0]
  exact isOrderAlong_primeDivisorOrder _ Q

/-- A Cartier Weil divisor is the Weil divisor of a Cartier divisor: `𝒪_X(D) ≅ 𝒪_X(E₀)` for a
Cartier divisor `E₀` with Weil divisor `w₀`, then `D - w₀ = div φ` and `E₀ + div φ` works. -/
private theorem exists_isWeilDivisorOfCartier_of_isCartier [CompactSpace Y] {D : Divisor Y}
    (hD : D.IsCartier) : ∃ E : Y.CartierDivisor, IsWeilDivisorOfCartier E D := by
  haveI : IsNoetherian Y := ⟨⟩
  have := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨E₀, ⟨e₀⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  obtain ⟨w₀, hw₀⟩ := exists_isWeilDivisorOfCartier E₀
  obtain ⟨e₁⟩ := hw₀.nonempty_sheaf_iso_divisorialSheaf
  obtain ⟨φ, hφ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (e₀ ≪≫ e₁)
  obtain ⟨Pc, hPc⟩ := exists_isWeilDivisorOfCartier_principalDivisor φ
  refine ⟨E₀ + Pc, fun Q => ?_⟩
  have h := (hw₀ Q).add (hPc Q)
  rwa [← DivisorWithCoeffs.coeff_add, ← hφ, add_sub_cancel] at h

end WeilOfCartier

section Semiample

variable {X Z : Scheme.{0}}

/-- An epimorphic counit of `f^* ⊣ f_*` stays epimorphic along an isomorphism of modules. -/
private theorem epi_counit_of_iso (f : X ⟶ Z) {M N : X.Modules} (e : N ≅ M)
    (h : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app N) := by
  set adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have heq : adj.counit.app N =
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).map e.hom ≫
        adj.counit.app M ≫ e.inv := by
    rw [← Category.assoc, adj.counit.naturality e.hom, Functor.id_map, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

private theorem realization_congr {c c' : KCartierDivisor ℚ X}
    (e : c = c') (h : ∀ D, ∃ n : ℤ, c D = n) (h' : ∀ D, ∃ n : ℤ, c' D = n) :
    KCartierDivisor.realization c h = KCartierDivisor.realization c' h' := by
  subst e; rfl

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- A `ℚ`-divisor `Q` with a positive multiple `nQ` a relatively free Cartier divisor is
semiample over `Z`. -/
private theorem isRelativelySemiample_of_isRelativelyFreeDivisor (f : X ⟶ Z) (Q : QDivisor X)
    {n : ℕ} (hn : 0 < n) {D : Divisor X} (hDc : D.IsCartier)
    (hQ : Divisor.toQDivisor D = (n : ℤ) • Q) (hfree : IsRelativelyFreeDivisor f D) :
    MMP.Fourfold.QDivisor.IsRelativelySemiample f Q := by
  classical
  obtain ⟨E, hE⟩ := exists_isWeilDivisorOfCartier_of_isCartier hDc
  obtain ⟨e⟩ := hE.nonempty_sheaf_iso_divisorialSheaf
  have hfreeE : IsRelativelyFreeCartier f E := epi_counit_of_iso f e hfree
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨Finsupp.single E ((n : ℚ)⁻¹), fun P => ?_, n, hn, ?_⟩
  · rw [Finsupp.sum_single_index (by simp),
      (MMP.Intersection.isOrderAlong_primeDivisorOrder E P).unique (hE P)]
    have hP := congrArg (fun F : QDivisor X => F.coeff P) hQ
    simp only [Divisor.coeff_toQDivisor] at hP
    rw [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at hP
    push_cast at hP
    rw [hP]
    field_simp
  · have hc : (n : ℚ) • Finsupp.single E ((n : ℚ)⁻¹) =
        (Finsupp.single E (1 : ℤ)).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
      rw [Finsupp.smul_single, Finsupp.mapRange_single, smul_eq_mul, mul_inv_cancel₀ hn',
        Int.cast_one]
    refine ⟨fun D => ⟨(Finsupp.single E (1 : ℤ)) D, by rw [hc]; rfl⟩, ?_⟩
    rw [realization_congr hc _ (fun D => ⟨(Finsupp.single E (1 : ℤ)) D, rfl⟩),
      KCartierDivisor.realization_eq_sum, Finsupp.sum_single_index (by simp), one_smul]
    exact hfreeE

/-- The order along `P` of the realization of an integral `ℚ`-Cartier divisor `c` is its Weil
coefficient `∑ c_E ord_P E`. -/
private theorem primeDivisorOrder_realization (c : KCartierDivisor ℚ X)
    (h : ∀ E, ∃ n : ℤ, c E = n) (P : MMP.Mori.PrimeDivisor X) :
    (MMP.Intersection.primeDivisorOrder P (KCartierDivisor.realization c h) : ℚ) =
      c.sum fun E a => a * (MMP.Intersection.primeDivisorOrder P E : ℚ) := by
  rw [KCartierDivisor.realization, map_finsuppSum]
  push_cast
  refine Finset.sum_congr rfl fun E _ => ?_
  dsimp only
  rw [map_zsmul, smul_eq_mul]
  push_cast
  rw [← (h E).choose_spec]

/-- A `ℚ`-divisor semiample over `Z` has a positive multiple which is a relatively free Cartier
divisor. -/
private theorem exists_isRelativelyFreeDivisor_of_isRelativelySemiample (f : X ⟶ Z)
    {Q : QDivisor X} (h : MMP.Fourfold.QDivisor.IsRelativelySemiample f Q) :
    ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor X, Divisor.toQDivisor M = (m : ℤ) • Q ∧ M.IsCartier ∧
      IsRelativelyFreeDivisor f M := by
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨C, hC, N, hN, hint, hfree⟩ := h
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier (KCartierDivisor.realization _ hint)
  refine ⟨N, hN, w, ?_, hw.isCartier, ?_⟩
  · ext P
    have h1 : (w.coeff P : ℚ) = (MMP.Intersection.primeDivisorOrder P
        (KCartierDivisor.realization _ hint) : ℚ) := by
      exact_mod_cast ((MMP.Intersection.isOrderAlong_primeDivisorOrder _ P).unique (hw P)).symm
    rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, hC P, h1,
      primeDivisorOrder_realization]
    rw [Finsupp.sum_smul_index' (fun _ => zero_mul _), zsmul_eq_mul, Finsupp.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun E _ => by ring
  · obtain ⟨e⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
    exact epi_counit_of_iso f e.symm hfree

end Semiample

/-! ### Pull-back and descent of semiampleness -/

section PullbackDescent

variable {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

omit [IsIntegral X] [CompactSpace X] [IsIntegral Y] [CompactSpace Y] in
/-- The pull-back of a Cartier divisor `G` has coefficient zero along every prime divisor through
a point of `g⁻¹(X ∖ Supp G)`. -/
private theorem coeff_eq_zero_of_isPullback {g : Y ⟶ X} {G : Divisor X}
    {hB : ∀ C : irreducibleComponents Y, g (componentGenericPoint Y C) ∉ G.supp} {G' : Divisor Y}
    (h : G.IsPullback g hB G') {y : Y} (hy : g y ∉ G.supp) (F : MMP.Mori.PrimeDivisor Y)
    (hF : y ∈ F.support) : G'.coeff F = 0 := by
  let U : X.Opens := ⟨(G.supp : Set X)ᶜ, G.isClosed_supp.isOpen_compl⟩
  have hloc : G.IsLocalEquation U 1 := by
    intro E ⟨x, hxE, hxU⟩
    rw [PrimeDivisor.ord_one]
    by_contra hne
    exact hxU (DivisorWithCoeffs.support_subset_supp hne hxE)
  have hF' : (F.support ∩ g ⁻¹ᵁ U).Nonempty := ⟨y, hF, hy⟩
  rw [h U 1 hloc F hF', pullbackComponent_eq hB hloc _ (mem_pointComponent _) 1 (by simp),
    map_one, PrimeDivisor.ordUnit_one]

/-- The pull-back of a relatively free Cartier divisor along a dominant morphism is relatively
free over the same base: a relative section generating `M` at `g y` pulls back to one generating
`g^*M` at `y`. -/
private theorem isRelativelyFreeDivisor_of_isPullback (g : Y ⟶ X) [IsDominant g] (f : X ⟶ Z)
    {M : Divisor X} (hMc : M.IsCartier)
    {hB : ∀ C : irreducibleComponents Y, g (componentGenericPoint Y C) ∉ M.supp}
    {M' : Divisor Y} (h : M.IsPullback g hB M') (hfree : IsRelativelyFreeDivisor f M) :
    IsRelativelyFreeDivisor (g ≫ f) M' := by
  have hadd : ∀ {T : Scheme.{0}} [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
      (N : Divisor T)
      (φ : (RationalFunctions T)ˣ) (P : MMP.Mori.PrimeDivisor T),
      (N + principalDivisor φ).coeff P = N.coeff P + P.ord φ := fun N φ P => by
    rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  apply isRelativelyFreeDivisor_of_forall_exists
  intro y
  obtain ⟨U, hU, ψ, h1, h2⟩ := exists_coeff_add_ord_eq_zero_of_isRelativelyFree f hMc hfree (g y)
  have hψ := map_componentGenericPoint_notMem_supp_of_isDominant g (principalDivisor ψ)
  have hG := Divisor.IsPullback.add hMc (Divisor.isCartier_principalDivisor ψ)
    (map_componentGenericPoint_notMem_supp_of_isDominant g _) h
    (Divisor.isPullback_principalDivisor ψ hψ)
  refine ⟨U, hU, pullbackRationalFunction g ψ hψ, fun F hF => ?_, fun F hF => ?_⟩
  · rw [← hadd]
    exact coeff_nonneg_of_isPullback_of_isEffectiveOn
      (hMc.add (Divisor.isCartier_principalDivisor ψ)) (V := f ⁻¹ᵁ U)
      (fun P hP => by rw [hadd]; exact h1 P hP) hG F hF
  · rw [← hadd]
    refine coeff_eq_zero_of_isPullback hG (y := y) ?_ F hF
    intro hmem
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    exact hE (by rw [hadd]; exact h2 E hxE)

/-- Semiampleness pulls back along dominant morphisms. -/
private theorem exists_isRelativelyFreeDivisor_of_isPullback (g : Y ⟶ X) [IsDominant g]
    (f : X ⟶ Z) {L : QDivisor X}
    {hB : ∀ C : irreducibleComponents Y, g (componentGenericPoint Y C) ∉ L.supp}
    {L' : QDivisor Y} (h : L.IsPullback g hB L')
    (hL : ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor X, Divisor.toQDivisor M = (m : ℤ) • L ∧ M.IsCartier ∧
      IsRelativelyFreeDivisor f M) :
    ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor Y, Divisor.toQDivisor M = (m : ℤ) • L' ∧ M.IsCartier ∧
      IsRelativelyFreeDivisor (g ≫ f) M := by
  obtain ⟨m, hm, M, hM, hMc, hMf⟩ := hL
  obtain ⟨M', hM', hp⟩ := h m hm M hM hMc
  exact ⟨m, hm, M', hM', isCartier_of_isPullback g hMc hp,
    isRelativelyFreeDivisor_of_isPullback g f hMc hp hMf⟩

/-- Semiampleness descends along proper birational morphisms of normal complex varieties. -/
private theorem exists_isRelativelyFreeDivisor_of_isPullback_of_isBirationalMorphism
    {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) (g : Y ⟶ X) [IsProper g]
    (hY : IsNormalVariety ℂ (g ≫ sX)) (hg : IsBirationalMorphism g) (f : X ⟶ Z)
    {L : QDivisor X} (hLq : L.IsQCartier)
    {hB : ∀ C : irreducibleComponents Y, g (componentGenericPoint Y C) ∉ L.supp}
    {L' : QDivisor Y} (h : L.IsPullback g hB L')
    (hL' : ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor Y, Divisor.toQDivisor M = (m : ℤ) • L' ∧
      M.IsCartier ∧ IsRelativelyFreeDivisor (g ≫ f) M) :
    ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor X, Divisor.toQDivisor M = (m : ℤ) • L ∧ M.IsCartier ∧
      IsRelativelyFreeDivisor f M := by
  haveI : IsDominant g := hg.isDominant
  have hbij := hg.functionFieldMap_bijective
  have hfin : letI := functionFieldMapAlgebra g; Module.Finite X.functionField Y.functionField :=
    RingHom.Finite.of_surjective _ hbij.2
  refine exists_isRelativelyFreeDivisor_of_pullback (g ≫ sX) sX hY hX g rfl hfin f L hLq ?_
  obtain ⟨m, hm, M, hM, hMc, hMf⟩ := hL'
  exact ⟨m, hm, M, by rw [hM, h.pullback_eq hLq], hMc, hMf⟩

end PullbackDescent

/-! ### Linearity of pull-backs of `ℚ`-Cartier `ℚ`-divisors -/

section LinearPullback

variable {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y]
  [CompactSpace Y] in
/-- A dominant morphism of integral schemes maps the generic point of `Y` outside the support of
every `ℚ`-divisor. -/
private theorem map_componentGenericPoint_notMem_qSupp (g : Y ⟶ X) [IsDominant g]
    (D : QDivisor X) (C : irreducibleComponents Y) : g (componentGenericPoint Y C) ∉ D.supp := by
  intro hmem
  obtain ⟨E, -, hE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
  rw [componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant,
    ← componentGenericPoint_eq_genericPoint (pointComponent (genericPoint X))] at hE
  exact MMP.Flips.componentGenericPoint_notMem_support _ E hE

/-- `B'` is the pull-back of `B` as soon as one positive multiple `N B` is a Cartier divisor whose
pull-back is `N B'`. -/
private theorem QDivisor.isPullback_of_exists {g : Y ⟶ X} [IsDominant g] {B : QDivisor X}
    (hB : ∀ C : irreducibleComponents Y, g (componentGenericPoint Y C) ∉ B.supp) {B' : QDivisor Y}
    {N : ℕ} (hN : 0 < N) {E : Divisor X} (hE : Divisor.toQDivisor E = (N : ℤ) • B)
    (hEc : E.IsCartier) {E' : Divisor Y} (hE' : Divisor.toQDivisor E' = (N : ℤ) • B')
    (hp : E.IsPullback g (map_componentGenericPoint_notMem_supp_of_isDominant g E) E') :
    B.IsPullback g hB B' := by
  intro m hm D hD hDc
  have key : (N : ℤ) • D = (m : ℤ) • E := Divisor.toQDivisor_injective (by
    rw [map_zsmul, map_zsmul, hD, hE, smul_smul, smul_smul, mul_comm])
  have hDB := map_componentGenericPoint_notMem_supp_of_isDominant g D
  have hD' := Divisor.isPullback_pullback hDc hDB
  refine ⟨D.pullback hDc hDB, ?_, hD'⟩
  have h1 := hD'.zsmul hDc (N : ℤ) (map_componentGenericPoint_notMem_supp_of_isDominant g _)
  have h2 := (hp.zsmul hEc (m : ℤ) (map_componentGenericPoint_notMem_supp_of_isDominant g _)).of_eq
    key.symm (hB₂ := map_componentGenericPoint_notMem_supp_of_isDominant g _)
  have h3 : (N : ℤ) • D.pullback hDc hDB = (m : ℤ) • E' := h1.eq (hDc.zsmul _) h2
  have h4 := congrArg Divisor.toQDivisor h3
  rw [map_zsmul, map_zsmul, hE', smul_smul, mul_comm, ← smul_smul] at h4
  exact smul_right_injective _ (by exact_mod_cast hN.ne') h4

/-- **Linearity of the pull-back.** `g^*(A + cT) = g^*A + c g^*T` for `ℚ`-Cartier `A`, `T`. -/
private theorem QDivisor.IsPullback.add_smul {g : Y ⟶ X} [IsDominant g] {A T : QDivisor X}
    (hA : A.IsQCartier) (hT : T.IsQCartier)
    {hAB : ∀ C : irreducibleComponents Y, g (componentGenericPoint Y C) ∉ A.supp}
    {hTB : ∀ C : irreducibleComponents Y, g (componentGenericPoint Y C) ∉ T.supp}
    {A' T' : QDivisor Y} (h₁ : A.IsPullback g hAB A') (h₂ : T.IsPullback g hTB T') (c : ℚ)
    (hB : ∀ C : irreducibleComponents Y, g (componentGenericPoint Y C) ∉ (A + c • T).supp) :
    (A + c • T).IsPullback g hB (A' + c • T') := by
  obtain ⟨NA, hNA, DA, hDA, hDAc⟩ := hA.exists_pos
  obtain ⟨NT, hNT, DT, hDT, hDTc⟩ := hT.exists_pos
  obtain ⟨DA', hDA', hpA⟩ := h₁ NA hNA DA hDA hDAc
  obtain ⟨DT', hDT', hpT⟩ := h₂ NT hNT DT hDT hDTc
  set a : ℤ := c.num
  set b : ℕ := c.den
  have hb : 0 < b := c.den_pos
  have hc : c = a / b := (Rat.num_div_den c).symm
  have hcomb : ∀ (U : Scheme.{0}) [IsLocallyNoetherian U] [IsNormal U] (A₀ T₀ : QDivisor U)
      (DA₀ DT₀ : Divisor U), Divisor.toQDivisor DA₀ = (NA : ℤ) • A₀ →
      Divisor.toQDivisor DT₀ = (NT : ℤ) • T₀ →
      Divisor.toQDivisor (((NT * b : ℕ) : ℤ) • DA₀ + ((NA : ℤ) * a) • DT₀) =
        ((NA * NT * b : ℕ) : ℤ) • (A₀ + c • T₀) := by
    intro U _ _ A₀ T₀ DA₀ DT₀ h1 h2
    rw [map_add, map_zsmul, map_zsmul, h1, h2]
    ext P
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      zsmul_eq_mul]
    rw [hc]
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast
    field_simp
  refine QDivisor.isPullback_of_exists hB (by positivity : 0 < NA * NT * b)
    (hcomb X A T DA DT hDA hDT) ((hDAc.zsmul _).add (hDTc.zsmul _))
    (hcomb Y A' T' DA' DT' hDA' hDT') ?_
  exact Divisor.IsPullback.add (hDAc.zsmul _) (hDTc.zsmul _) _
    (hpA.zsmul hDAc _ (map_componentGenericPoint_notMem_supp_of_isDominant g _))
    (hpT.zsmul hDTc _ (map_componentGenericPoint_notMem_supp_of_isDominant g _))

end LinearPullback

/-! ### Coefficients of lc pairs and of crepant boundaries -/

section Coefficients

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- The coefficients of the boundary of an lc surface pair are at most one: a coefficient
`> 1` makes the total discrepancy `< -1`, hence the discrepancy `-∞`. -/
private theorem IsLcPair.coeff_le_one {K : Divisor X} {B : QDivisor X}
    (hlc : IsLcPair sX 2 K B) (G : MMP.Mori.PrimeDivisor X) : B.coeff G ≤ 1 := by
  by_contra h
  push Not at h
  have ht : totalDiscrep sX 2 K B < -1 := by
    refine (totalDiscrep_le_neg_coeff hlc.1.1 (P := G)
      (MMP.Positivity.IsPair.exists_isDiscrepancy hlc.isPair hlc.1.2.1 _)).trans_lt ?_
    have h1 : (((-B.coeff G : ℚ) : ℝ) : EReal) < ((-1 : ℝ) : EReal) :=
      EReal.coe_lt_coe_iff.mpr (by push_cast; exact_mod_cast (by linarith : -B.coeff G < -1))
    simpa using h1
  have h2 := hlc.2
  rw [MMP.Mori.discrep_eq_bot_of_totalDiscrep_lt_neg_one hlc.1 le_rfl ht] at h2
  have h3 : ((-1 : ℝ) : EReal) ≤ ⊥ := by simpa using h2
  exact absurd (le_bot_iff.mp h3) (EReal.coe_ne_bot _)

/-- A divisor `D` over `X` which is not exceptional has, for every pair, the discrepancy
`-coeff_G` along the prime divisor `G` of `X` with the valuation of `D`. -/
private theorem exists_eq_neg_coeff_of_not_isExceptional (hX : IsNormalVariety ℂ sX)
    (D : DivisorOver ℂ sX) (hD : ¬ D.IsExceptional) :
    ∃ G : MMP.Mori.PrimeDivisor X, ∀ {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℚ},
      IsDiscrepancy sX n K Δ D a → a = -Δ.coeff G := by
  obtain ⟨G, hv⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hD
  refine ⟨G, fun {n K Δ a} ha => ?_⟩
  obtain ⟨hX, hK, m, hm, -, V, hV, τ, hτ, hmτ⟩ := ha
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX hn hv τ,
    DivisorOver.ordPullback_ofPrimeDivisor hX hn G τ] at hmτ
  have hx : D.f D.E.genericPoint = G.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  have hGV : (G.support ∩ (V : Set X)).Nonempty := by
    refine ⟨G.genericPoint, ?_, hx ▸ hV⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have e := hτ.2 G hGV
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hm0
  linear_combination hmτ + e

/-- An lc surface pair with effective boundary is log canonical in the sense of log
discrepancies: every log discrepancy is one plus a discrepancy, which is `≥ -1`. -/
private theorem isLogCanonicalPair_of_isLcPair {K : Divisor X} {B : QDivisor X}
    (hlc : IsLcPair sX 2 K B) (hB : 0 ≤ B) : MMP.Intersection.IsLogCanonicalPair sX B := by
  refine ⟨hlc.isPair, fun P => hB P, fun n D a ha => ?_⟩
  have hn := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
  have hn2 : n = 2 := by
    have h := hn.symm.trans hlc.1.2.1.topologicalKrullDim_eq
    exact_mod_cast h
  subst hn2
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hlc.isPair hlc.1.2.1 D
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha' ha]
  have h1 : -1 ≤ a' := by
    by_cases hD : D.IsExceptional
    · have h := hlc.2.trans (discrep_le hD ha')
      rw [show (-1 : EReal) = ((-1 : ℝ) : EReal) by simp] at h
      exact_mod_cast EReal.coe_le_coe_iff.mp h
    · obtain ⟨G, hG⟩ := exists_eq_neg_coeff_of_not_isExceptional hlc.1.1 D hD
      rw [hG ha']
      linarith [IsLcPair.coeff_le_one hlc G]
  have h2 : (-1 : ℝ) ≤ a' := by exact_mod_cast h1
  linarith

/-- A prime divisor `F` of `Y` which is not exceptional over `X` has, in every crepant boundary,
the coefficient of the boundary along the prime divisor `G` of `X` with the valuation of `F`. -/
private theorem exists_coeff_eq_of_isCrepantBoundary {Y : Scheme.{0}} (hX : IsNormalVariety ℂ sX)
    {r : Y ⟶ X} (hY : IsNormalVariety ℂ (r ≫ sX)) (hr : IsBirationalMorphism r)
    (F : MMP.Mori.PrimeDivisor Y)
    (hF : ¬ RationalMap.IsExceptional (X := Y) r.toRationalMap F) :
    ∃ G : MMP.Mori.PrimeDivisor X, ∀ {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {ΔY : QDivisor Y},
      IsCrepantBoundary sX n K Δ r hY hr ΔY → ΔY.coeff F = Δ.coeff G := by
  obtain ⟨G, hG⟩ := exists_eq_neg_coeff_of_not_isExceptional hX ⟨Y, r, hY, hr, F⟩ hF
  exact ⟨G, fun h => neg_injective (hG (h F))⟩

end Coefficients

/-! ### Relative nefness -/

section Curves

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- A proper curve over `k` is a curve over `k`. -/
private theorem isCurve_properCurve (C : ProperCurve sX) :
    AlgebraicGeometry.IsCurve k (C.ι ≫ sX) where
  toIsIntegral := inferInstance
  toIsSeparated := inferInstance
  toLocallyOfFiniteType := (inferInstance : IsProper (C.ι ≫ sX)).toLocallyOfFiniteType
  toQuasiCompact := inferInstance
  topologicalKrullDim_eq_one := C.dim_eq

/-- The underlying set of a proper curve is the closure of its generic point. -/
private theorem range_properCurve_ι (C : ProperCurve sX) :
    Set.range C.ι = closure ({C.point} : Set X) := by
  unfold ProperCurve.ι curveSubschemeAtι
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- Intersection numbers are unchanged by an isomorphism of curves over `X`. -/
private theorem intersectionNumber_eq_of_iso_comp [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] {C C' : Scheme.{0}} (i : C ⟶ X) (i' : C' ⟶ X)
    [IsProper (i ≫ sX)] [IsProper (i' ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (e : C ≅ C') (he : e.hom ≫ i' = i) (D : QDivisor X)
    (hD : D.IsQCartier) :
    D.intersectionNumber k sX i hdim hD = D.intersectionNumber k sX i' hdim' hD := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  unfold QDivisor.intersectionNumber Divisor.degreeOn
  have := (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor
    |>.isInvertibleModule_divisorialSheaf
  rw [MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i i' hdim hdim' e he]

/-- Two closed subschemes cut out by equal ideal sheaves are isomorphic over `X`. -/
private theorem exists_iso_subscheme_of_eq {I J : X.IdealSheafData} (h : I = J) :
    ∃ e : I.subscheme ≅ J.subscheme, e.hom ≫ J.subschemeι = I.subschemeι := by
  subst h
  exact ⟨Iso.refl _, by simp⟩

end Curves

private theorem intersectionNumber_pullback_eq_zero_or {k : Type} [Field k]
    {V W Y : Scheme.{0}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    (u : V ⟶ W) [IsProper u] (hu : u ≫ sW = sV) (f : W ⟶ Y) {L : QDivisor W}
    (hL : L.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') (hL' : L'.IsQCartier) (C : ProperCurve sV)
    (hC : C.IsContractedBy (u ≫ f)) :
    L'.intersectionNumber k sV C.ι C.dim_le hL' = 0 ∨
      ∃ d : ℚ, 0 ≤ d ∧ ∃ C'' : ProperCurve sW, C''.IsContractedBy f ∧
        L'.intersectionNumber k sV C.ι C.dim_le hL' =
          d * L.intersectionNumber k sW C''.ι C''.dim_le hL := by
  have := isCurve_properCurve C
  set φ := C.ι ≫ u with hφ
  by_cases hpt : ∃ w : W, Set.range φ = {w}
  · left
    exact intersectionNumber_pullback_eq_zero k sV sW u hu C.ι hL h hpt
  · right
    have : AlgebraicGeometry.IsCurve k (φ ≫ sW) := by rw [hφ, Category.assoc, hu]; infer_instance
    have : IsProper (φ ≫ sW) := by rw [hφ, Category.assoc, hu]; infer_instance
    have hcurve := isCurve_imageι_comp sW φ hpt
    have key := intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu C.ι hL h hcurve
    have hrange : closure (Set.range φ) = closure ({u C.point} : Set W) := by
      rw [hφ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_properCurve_ι,
        closure_image_closure u.continuous, Set.image_singleton]
    have hker : φ.ker = Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure ({u C.point} : Set W)) := by
      rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
      congr 1
      ext1
      simp only [TopologicalSpace.Closeds.coe_closure]
      exact hrange
    obtain ⟨e, he⟩ := exists_iso_subscheme_of_eq hker
    have : IsProper φ := IsProper.of_comp φ sW
    have : IsProper (φ.imageι ≫ sW) := isProper_imageι_comp φ sW
    have hdim : topologicalKrullDim (curveSubschemeAt (u C.point)) = 1 :=
      (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph).symm.trans
        hcurve.topologicalKrullDim_eq_one
    have hι : curveSubschemeAtι (u C.point) = e.inv ≫ φ.imageι := by
      rw [Iso.eq_inv_comp]; exact he
    have hprop : IsProper (curveSubschemeAtι (u C.point) ≫ sW) := by
      rw [hι, Category.assoc]; infer_instance
    let C'' : ProperCurve sW := ⟨u C.point, ⟨hdim, hprop⟩⟩
    have hC'' : C''.IsContractedBy f := by
      intro x hx
      have hsub : closure ({u C.point} : Set W) ⊆ u '' closure ({C.point} : Set V) :=
        (u.isClosedMap _ isClosed_closure).closure_subset_iff.mpr (by
          rintro _ rfl; exact ⟨C.point, subset_closure rfl, rfl⟩)
      obtain ⟨z, hz, rfl⟩ := hsub hx
      have := hC z hz
      simpa only [Scheme.Hom.comp_apply] using this
    refine ⟨(degreeOver φ.toImage : ℚ), by positivity, C'', hC'', key.trans ?_⟩
    rw [intersectionNumber_eq_of_iso_comp sW φ.imageι C''.ι _ C''.dim_le e he _ hL]

section Nef

/-- `q D` is `ℚ`-Cartier for `D` `ℚ`-Cartier and `q ∈ ℚ`. -/
private theorem isQCartier_smul {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (hD : D.IsQCartier) (q : ℚ) : (q • D).IsQCartier := by
  obtain ⟨m, hm, E, hE, hEc⟩ := hD.exists_pos
  refine ⟨((q.den * m : ℕ) : ℤ), by positivity, q.num • E, ?_, hEc.zsmul _⟩
  refine Finsupp.ext fun P => ?_
  have h1 := congrArg (fun G : QDivisor X => G P) hE
  simp only [Finsupp.smul_apply, zsmul_eq_mul, smul_eq_mul] at h1 ⊢
  change ((q.num • E) P : ℚ) = _
  rw [Finsupp.smul_apply, smul_eq_mul, Int.cast_mul]
  change _ * ((E P : ℤ) : ℚ) = _
  have h2 : ((E P : ℤ) : ℚ) = (Divisor.toQDivisor E) P := rfl
  rw [h2, h1]
  have := Rat.mul_den_eq_num q
  push_cast
  rw [← this]
  ring

/-- A limit of relatively nef `ℚ`-Cartier divisors `D - δT`, `δ → 0⁺`, is relatively nef. -/
private theorem isRelativelyNef_of_forall_sub_smul {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {f : X ⟶ Y} {D T : QDivisor X}
    (hD : D.IsQCartier) (hT : T.IsQCartier) {ε : ℚ} (hε : 0 < ε)
    (h : ∀ δ : ℚ, 0 < δ → δ ≤ ε → (D - δ • T).IsRelativelyNef sX f) :
    D.IsRelativelyNef sX f := by
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hD fun C hC => ?_
  set a := D.intersectionNumber ℂ sX C.ι C.dim_le hD
  set t := T.intersectionNumber ℂ sX C.ι C.dim_le hT
  have key : ∀ δ : ℚ, 0 < δ → δ ≤ ε → δ * t ≤ a := by
    intro δ hδ0 hδε
    have hn := h δ hδ0 hδε
    have hsq := isQCartier_smul hT (-δ)
    have h0 := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hn
      hn.1 C hC
    rw [MMP.Fourfold.intersectionNumber_congr sX C.ι C.dim_le hn.1 (hD.add hsq)
        (by rw [sub_eq_add_neg, neg_smul]),
      QDivisor.intersectionNumber_add' ℂ sX C.ι C.dim_le _ _ hD hsq,
      MMP.Fourfold.intersectionNumber_smul sX C.ι C.dim_le T hT (-δ) hsq] at h0
    linarith
  by_contra hneg
  push Not at hneg
  set δ := min ε (-a / (2 * |t| + 1)) with hδdef
  have hden : 0 < 2 * |t| + 1 := by positivity
  have hδ0 : 0 < δ := lt_min hε (div_pos (by linarith) hden)
  have hδ1 : δ ≤ -a / (2 * |t| + 1) := min_le_right _ _
  have h1 := key δ hδ0 (min_le_left _ _)
  have h2 : -(δ * |t|) ≤ δ * t := by
    have := neg_abs_le t
    nlinarith
  have h3 : δ * (2 * |t| + 1) ≤ -a := (le_div_iff₀ hden).mp hδ1
  nlinarith [abs_nonneg t]

/-- The pull-back of a relatively nef `ℚ`-Cartier divisor along a proper morphism `u` is nef
relative to the composite. -/
private theorem isRelativelyNef_of_isPullback {W V T : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsProjectiveVariety ℂ sV] (u : W ⟶ V)
    [IsProper u] [IsDominant u] {g : V ⟶ T} {D : QDivisor V} (hD : D.IsRelativelyNef sV g)
    {hB : ∀ C : irreducibleComponents W, u (componentGenericPoint W C) ∉ D.supp}
    {P : QDivisor W} (hp : D.IsPullback u hB P) :
    haveI : QuasiCompact (u ≫ sV) := inferInstance
    P.IsRelativelyNef (u ≫ sV) (u ≫ g) := by
  haveI : AlgebraicGeometry.IsVariety ℂ (u ≫ sV) :=
    { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
  have hPq := hp.isQCartier hD.1
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (u ≫ sV) hPq
    fun C hC => ?_
  rcases intersectionNumber_pullback_eq_zero_or u rfl g hD.1 hp hPq C hC with
    h0 | ⟨d, hd, C'', hC'', heq⟩
  · rw [h0]
  · rw [heq]
    exact mul_nonneg hd
      (MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sV hD hD.1 C'' hC'')

end Nef

/-! ### The semiampleness of `K' + B'` on the `ε`-model -/

/-- **Semiampleness on the `ε`-model.** Let `(X', B')` be a projective `ℚ`-factorial lc complex
surface pair over the projective variety `Z` such that `(X', B' - δ⌊B'⌋)` is klt with nef and big
adjoint over `Z` for all small `δ > 0`. Then `K' + B'` is semiample over `Z`. -/
private theorem exists_isRelativelyFreeDivisor_of_isKltPair_sub
    {X' Z : Scheme.{0}} [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX' : X' ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsProjectiveVariety ℂ sX'] [QuasiCompact sX']
    {sZ : Z ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsProjectiveVariety ℂ sZ]
    {f' : X' ⟶ Z} (hf' : f' ≫ sZ = sX') (hQ' : IsQFactorial sX') {K' : Divisor X'}
    {B' : QDivisor X'} (hlc' : IsLcPair sX' 2 K' B') (hB' : 0 ≤ B') {ε : ℚ} (hε : 0 < ε)
    (hδ : ∀ δ : ℚ, 0 < δ → δ ≤ ε →
      IsKltPair sX' 2 K' (B' - δ • Divisor.toQDivisor B'.roundDown) ∧
      (Divisor.toQDivisor K' + (B' - δ • Divisor.toQDivisor B'.roundDown)).IsRelativelyNef
        sX' f' ∧
      (Divisor.toQDivisor K' + (B' - δ • Divisor.toQDivisor B'.roundDown)).IsRelativelyBig f') :
    ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor X', Divisor.toQDivisor M =
      (m : ℤ) • (Divisor.toQDivisor K' + B') ∧ M.IsCartier ∧ IsRelativelyFreeDivisor f' M := by
  haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace sX'
  have hX'v : IsNormalVariety ℂ sX' := ⟨inferInstance, inferInstance⟩
  have hK' : K'.IsCanonicalDivisor sX' 2 := hlc'.1.2.1
  have hdim' : topologicalKrullDim X' = 2 := hK'.topologicalKrullDim_eq
  have hcoeff : ∀ G, B'.coeff G ≤ 1 := IsLcPair.coeff_le_one hlc'
  obtain ⟨Y, _, _, _, r, hr, hYQ, Δ, hrp, hYp, hdlt, hcrep, hexc⟩ :=
    MMP.Threefold.exists_crepant_dltModification_of_surface sX' inferInstance hdim'
      (isLogCanonicalPair_of_isLcPair hlc' hB')
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (r ≫ sX') := hYp
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (r ≫ sX')
  haveI : IsProper r := IsProper.of_comp r sX'
  haveI : IsDominant r := hr.isDominant
  have hYv : IsNormalVariety ℂ (r ≫ sX') := hYQ.1
  have hdimY : topologicalKrullDim Y = 2 := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX' (r ≫ sX') hr,
      hdim']
  -- A canonical divisor of `Y` compatible with `K'`.
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX'v hK'
  have hωK : divisorOfForm ω = K' := Finsupp.ext hω
  have hτ0 : pullbackRationalPluriForms sX' r ω ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' r hr.functionFieldMap_bijective
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX') hdim') hω0
  set KY := divisorOfForm (pullbackRationalPluriForms sX' r ω) with hKY_def
  obtain ⟨K₀, hK₀⟩ := exists_isCanonicalDivisor (r ≫ sX') hYv (n := 2) hdimY
  have hKY : KY.IsCanonicalDivisor (r ≫ sX') 2 := by
    have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYv hK₀ hτ0
    rw [one_zsmul] at h
    exact hK₀.of_linearlyEquivalent h
  have hcompat : ∃ ω' : RationalPluriForms sX' 2 1, ω' ≠ 0 ∧ divisorOfForm ω' = K' ∧
      divisorOfForm (pullbackRationalPluriForms sX' r ω') = KY := ⟨ω, hω0, hωK, rfl⟩
  have hcr := hcrep K' hK'
  obtain ⟨-, -, hB1, hpb⟩ :=
    IsPair.isPullback_of_isCrepantBoundary hlc'.isPair r hYv hr hK' hKY (Or.inl hcompat) hcr
  have hdltM : IsDltPair (r ≫ sX') 2 KY Δ :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair _ hKY Δ).mp hdlt
  -- The floor `T'` and its pull-back `P`.
  set T' : QDivisor X' := Divisor.toQDivisor B'.roundDown with hT'_def
  have hT'q : T'.IsQCartier := by
    obtain ⟨m, hm, hmc⟩ := hQ'.2 B'.roundDown
    exact ⟨m, by exact_mod_cast hm.ne', _, by rw [map_zsmul], hmc⟩
  have hT'B := map_componentGenericPoint_notMem_supp_of_isQCartier r hT'q
  set P : QDivisor Y := QDivisor.pullback T' hT'q hT'B with hP_def
  have hP := QDivisor.isPullback_pullback hT'q hT'B
  have hQ'q : (Divisor.toQDivisor K' + B').IsQCartier := hlc'.1.2.2
  have hpbδ : ∀ δ : ℚ, ∃ hB, (Divisor.toQDivisor K' + (B' - δ • T')).IsPullback r hB
      (Divisor.toQDivisor KY + (Δ - δ • P)) := by
    intro δ
    have hB := map_componentGenericPoint_notMem_qSupp r
      (Divisor.toQDivisor K' + B' + (-δ) • T')
    refine ⟨?_, ?_⟩
    · simpa [sub_eq_add_neg, add_assoc] using hB
    · have h := QDivisor.IsPullback.add_smul hQ'q hT'q hpb hP (-δ) hB
      simpa [sub_eq_add_neg, add_assoc] using h
  -- The crepant boundary of `(X', B' - δT')` on `Y` is `Δ - δP`.
  have hcrδ : ∀ δ : ℚ, 0 < δ → δ ≤ ε →
      IsCrepantBoundary sX' 2 K' (B' - δ • T') r hYv hr (Δ - δ • P) := by
    intro δ hδ0 hδε
    have hklt := (hδ δ hδ0 hδε).1
    have hPδ : MMP.Mori.IsPair sX' (B' - δ • T') := hklt.isPair
    obtain ⟨⟨Δδ, hΔδ, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hPδ hK' r hYv hr
    obtain ⟨-, -, hB2, hpb2⟩ :=
      IsPair.isPullback_of_isCrepantBoundary hPδ r hYv hr hK' hKY (Or.inl hcompat) hΔδ
    obtain ⟨hB3, hpb3⟩ := hpbδ δ
    have e : Divisor.toQDivisor KY + Δδ = Divisor.toQDivisor KY + (Δ - δ • P) :=
      (QDivisor.IsPullback.pullback_eq hklt.1.2.2 hpb2).symm.trans
        (QDivisor.IsPullback.pullback_eq hklt.1.2.2 hpb3)
    rwa [← add_left_cancel e]
  -- Coefficients of `P`.
  have hΔle : ∀ F, Δ.coeff F ≤ 1 := hdlt.2.1
  have hΔnn : ∀ F, 0 ≤ Δ.coeff F := hdlt.1.2.1
  set ε₁ : ℚ := min ε 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε one_pos
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  have hT'coeff : ∀ G, T'.coeff G = ⌊B'.coeff G⌋ := fun G => by
    rw [hT'_def, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundDown]
  have hPcoeff : ∀ F, 0 ≤ P.coeff F ∧ (P.coeff F ≠ 0 ↔ Δ.coeff F = 1) := by
    intro F
    have hlt := MMP.Positivity.IsKltPair.coeff_lt_one_of_isCrepantBoundary
      (hδ ε₁ hε₁0 hε₁ε).1 hYv hr (hcrδ ε₁ hε₁0 hε₁ε) F
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at hlt
    by_cases hE : RationalMap.IsExceptional (X := Y) r.toRationalMap F
    · have h1 : Δ.coeff F = 1 := (hexc F hE).2
      have hpos : 0 < P.coeff F := by
        rw [h1] at hlt
        exact pos_of_mul_pos_right (by linarith) hε₁0.le
      exact ⟨hpos.le, ⟨fun _ => h1, fun _ => hpos.ne'⟩⟩
    · obtain ⟨G, hG⟩ := exists_coeff_eq_of_isCrepantBoundary hX'v hYv hr F hE
      have e1 := hG hcr
      have e2 := hG (hcrδ ε₁ hε₁0 hε₁ε)
      rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
        DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul, e1] at e2
      have hPT : P.coeff F = T'.coeff G := mul_left_cancel₀ hε₁0.ne' (by linarith)
      rw [hPT, hT'coeff, e1]
      have h0 : 0 ≤ B'.coeff G := hB' G
      have h1 := hcoeff G
      rcases h1.lt_or_eq with h1 | h1
      · have : ⌊B'.coeff G⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩
        simp [this, h1.ne]
      · simp [h1]
  have hPeff : P.IsEffective :=
    DivisorWithCoeffs.isEffective_iff_nonneg.mpr fun F => (hPcoeff F).1
  have hPq : P.IsQCartier := hP.isQCartier hT'q
  have hPT : P.supp = Δ.roundDown.supp := by
    ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff,
      DivisorWithCoeffs.mem_supp_iff]
    simp only [DivisorWithCoeffs.coeff_roundDown]
    refine exists_congr fun F => and_congr_left fun _ => ?_
    rw [(hPcoeff F).2]
    refine ⟨fun h => by simp [h], fun h => ?_⟩
    by_contra h1
    exact h (Int.floor_eq_zero_iff.mpr ⟨hΔnn F, lt_of_le_of_ne (hΔle F) h1⟩)
  -- Every small pencil `K_Y + Δ - δP` is semiample over `Z`.
  have hrf : r ≫ f' ≫ sZ = r ≫ sX' := by rw [hf']
  have hpencil : ∀ δ : ℚ, 0 < δ → δ ≤ ε₁ → MMP.Fourfold.QDivisor.IsRelativelySemiample (r ≫ f')
      (Divisor.toQDivisor KY + Δ - δ • P) := by
    intro δ hδ0 hδ1
    have hδε : δ ≤ ε := hδ1.trans hε₁ε
    obtain ⟨hklt, hnefδ, hbigδ⟩ := hδ δ hδ0 hδε
    have hB0 : 0 ≤ B' - δ • T' := fun G => by
      change (0 : ℚ) ≤ DivisorWithCoeffs.coeff (B' - δ • T') G
      rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul, hT'coeff]
      have h0 : 0 ≤ B'.coeff G := hB' G
      have h1 := hcoeff G
      have hfl : (⌊B'.coeff G⌋ : ℚ) ≤ B'.coeff G := Int.floor_le _
      have hfl0 : (0 : ℚ) ≤ ⌊B'.coeff G⌋ := by exact_mod_cast Int.floor_nonneg.mpr h0
      have hδ1' : δ ≤ 1 := hδ1.trans (min_le_right _ _)
      nlinarith
    have hsemi := IsKltPair.isRelativelySemiample_of_isRelativelyNef_of_isRelativelyBig hf' hQ'
      hklt hB0 hnefδ hbigδ
    obtain ⟨hB3, hpb3⟩ := hpbδ δ
    obtain ⟨m, hm, M, hM, hMc, hMf⟩ := exists_isRelativelyFreeDivisor_of_isPullback r f' hpb3
      (exists_isRelativelyFreeDivisor_of_isRelativelySemiample f' hsemi)
    rw [add_sub_assoc]
    exact isRelativelySemiample_of_isRelativelyFreeDivisor _ _ hm hMc hM hMf
  have hεev : ∀ᶠ δ : ℚ in 𝓝[>] 0, MMP.Fourfold.QDivisor.IsRelativelySemiample (r ≫ f')
      (Divisor.toQDivisor KY + Δ - δ • P) :=
    Filter.mem_of_superset (Ioc_mem_nhdsGT hε₁0) fun δ hδ' => hpencil δ hδ'.1 hδ'.2
  -- `K_Y + Δ` is nef over `Z`.
  have hnef' : (Divisor.toQDivisor K' + B').IsRelativelyNef sX' f' :=
    isRelativelyNef_of_forall_sub_smul hQ'q hT'q hε fun δ hδ0 hδε => by
      rw [add_sub_assoc]
      exact (hδ δ hδ0 hδε).2.1
  have hnefY : QDivisor.IsRelativelyNef (r ≫ sX') (r ≫ f') (Divisor.toQDivisor KY + Δ) :=
    isRelativelyNef_of_isPullback r hnef' hpb
  -- The whole-floor lemma and the whole-floor criterion.
  have hT := Floor.exists_epi_counit_pullback_suppScheme_of_isDltPair_of_isRelativelyNef
    (r ≫ sX') sZ hYp inferInstance (r ≫ f') (by rw [Category.assoc, hf']) KY Δ hdltM hYQ hnefY
  have hfp : IsProjectiveMorphism (r ≫ f') := hrp.comp
    (IsProjectiveMorphism.of_comp f' sZ (by
      rw [hf']; exact AlgebraicGeometry.IsProjectiveVariety.isProjective))
  have hsemiY := QDivisor.isRelativelySemiample_of_isDltPair_of_restrict_roundDown (r ≫ sX') sZ
    inferInstance (r ≫ f') (by rw [Category.assoc, hf']) hfp KY Δ hYQ hdltM P hPeff hPq hPT
    hεev hT
  -- Descent along `r`.
  exact exists_isRelativelyFreeDivisor_of_isPullback_of_isBirationalMorphism hX'v r hYv hr f'
    hQ'q hpb (exists_isRelativelyFreeDivisor_of_isRelativelySemiample _ hsemiY)

/-! ### The theorem -/

private theorem isRelativelySemiample_of_isLcPair
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] (sZ : Z ⟶ Spec (.of ℂ))
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    (K : Divisor X) (B : QDivisor X) (hB : B.IsEffective) (hlc : IsLcPair sX 2 K B)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    (hbig : (Divisor.toQDivisor K + B).IsRelativelyBig f) :
    MMP.Fourfold.QDivisor.IsRelativelySemiample f (Divisor.toQDivisor K + B) := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  obtain ⟨X', _, _, _, sX', hX', _, K', B', f', hf', hQ', hlc', hB', hW, ε, hε, hδ⟩ :=
    IsLcPair.exists_isKltPair_sub_smul_roundDown_of_isRelativelyNef_of_isRelativelyBig hf hlc
      (DivisorWithCoeffs.isEffective_iff_nonneg.mp hB) hnef hbig
  obtain ⟨W, _, _, _, p, q, hWp, hp, hq, hpq, hpX, hqX', DW, hDp, hDq⟩ := hW
  -- Step 1: `K' + B'` is semiample over `Z`.
  have h1 := exists_isRelativelyFreeDivisor_of_isKltPair_sub hf' hQ' hlc' hB' hε hδ
  -- Step 2: pull back to `W` and descend to `X`.
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (p ≫ sX) := hWp
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace sX'
  haveI : IsProper p := IsProper.of_comp p sX
  haveI : IsDominant q := hq.isDominant
  have h2 := exists_isRelativelyFreeDivisor_of_isPullback q f' hDq h1
  rw [← hpq] at h2
  have hXv : IsNormalVariety ℂ sX := ⟨inferInstance, inferInstance⟩
  have hWv : IsNormalVariety ℂ (p ≫ sX) := ⟨inferInstance, inferInstance⟩
  obtain ⟨m, hm, M, hM, hMc, hMf⟩ :=
    exists_isRelativelyFreeDivisor_of_isPullback_of_isBirationalMorphism hXv p hWv hp f
      hlc.1.2.2 hDp h2
  exact isRelativelySemiample_of_isRelativelyFreeDivisor f _ hm hMc hM hMf

end MMP.SurfaceProjectiveLcNefBigSemiample

namespace MMP.Fourfold

open MMP.Mori

/-- **Relative lc nef-big basepoint freeness on projective surfaces.** Let `X` be a normal
projective complex surface with canonical divisor `K`, `B` an effective `ℚ`-divisor with `(X, B)`
lc, and `f : X ⟶ Z` a morphism of projective complex varieties. If `K + B` is `f`-nef and `f`-big,
then `K + B` is semiample over `Z`. -/
@[mmp "thm_mmp_surface_projective_lc_nef_big_semiample"]
public theorem QDivisor.isRelativelySemiample_of_isLcPair_of_isRelativelyNef_of_isRelativelyBig
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] (sZ : Z ⟶ Spec (.of ℂ))
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (_hdim : topologicalKrullDim X = 2)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    (K : Divisor X) (B : QDivisor X) (hB : B.IsEffective) (hlc : IsLcPair sX 2 K B)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    (hbig : (Divisor.toQDivisor K + B).IsRelativelyBig f) :
    QDivisor.IsRelativelySemiample f (Divisor.toQDivisor K + B) :=
  MMP.SurfaceProjectiveLcNefBigSemiample.isRelativelySemiample_of_isLcPair sX sZ hX hZ f hf K B hB
    hlc hnef hbig

end MMP.Fourfold
