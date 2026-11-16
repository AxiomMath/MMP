module

public import MMP.Analysis.Convex.FiniteDimensional
public import MMP.AlgebraicGeometry.Intersection.PicardNumberFiniteComplex
public import MMP.AlgebraicGeometry.Geometrically.CurveClassesBaseChange
import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModels

/-!
# Finite dimensionality of `N₁(X)` for projective varieties

Let `k` be an algebraically closed field of characteristic zero and `X` a projective variety
over `k`. The real vector space `N₁(X)` of numerical classes of real 1-cycles on `X`
(`MMP.Mori.NumericalCurveClasses`), where numerical equivalence is tested against the degrees
`(Z · L)` of all invertible sheaves `L` (equivalently, of the sheaves `𝒪_X(D)` of all Cartier
divisors `D`), is finite dimensional over `ℝ`.

The finitely many equations of `X` in a projective space have their coefficients in a finitely
generated subring of `k`, so `X` is the base change of a projective variety `X₀` over the
algebraic closure `k₀ ⊆ k` of that subring, a countable algebraically closed field. A countable
field of characteristic zero embeds in `ℂ`. Base extension between algebraically closed fields
does not change `N₁` (`MMP.Fourfold.numericalCurveClassesBaseChange`), so
`N₁(X) ≃ N₁(X₀) ≃ N₁(X₀ ×_{k₀} ℂ)`, and the last space is finite dimensional by the finiteness
of the Picard number of a projective complex variety
(`MMP.Mori.picardNumber_lt_top_of_isProjectiveVariety`).

## Main results

* `MMP.Mori.NumericalCurveClasses.finiteDimensional_of_isProjectiveVariety`: `N₁(X)` is finite
  dimensional over `ℝ` for a projective variety `X` over an algebraically closed field of
  characteristic zero.

## Implementation notes

The source descends, together with `X`, finitely many curves and invertible sheaves to a finitely
generated field and compares the degree matrices over `k` and over `ℂ`. Here the comparison of
curves and invertible sheaves is the base-change isomorphism on `N₁` between algebraically closed
fields, so only `X` itself is descended.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Chapter 1.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

/-- A scheme `X₀` with an H-projective morphism to `Spec k₀` whose base change to a field
extension `k₀ → k` is an integral scheme is a projective variety over `k₀`. -/
private theorem isProjectiveVariety_of_isPullback {k₀ k : Type} [Field k₀] [Field k]
    [Algebra k₀ k] {X X₀ : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {s₀ : X₀ ⟶ Spec (.of k₀)}
    {π : X ⟶ X₀} (h : IsPullback π sX s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))))
    [IsIntegral X] (hP : IsProjectiveMorphism s₀) : MMP.Mori.IsProjectiveVariety k₀ s₀ := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k₀ k))
  have := isProper_of_isProjectiveMorphism _ hP
  have : IsSchemeTheoreticallyDominant g := IsSchemeTheoreticallyDominant.of_isDominant g
  have : IsSchemeTheoreticallyDominant π := IsSchemeTheoreticallyDominant.of_isPullback h.flip
  have : QuasiCompact π := MorphismProperty.of_isPullback h.flip inferInstance
  have : Surjective π := MorphismProperty.of_isPullback h.flip inferInstance
  have : IsReduced X₀ := IsSchemeTheoreticallyDominant.isReduced π
  have : IrreducibleSpace X₀ := by
    have := (IrreducibleSpace.isIrreducible_univ X).image π.base π.continuous.continuousOn
    rw [Set.image_univ, π.surjective.range_eq] at this
    exact (irreducibleSpace_def X₀).mpr this
  have : IsIntegral X₀ := isIntegral_of_irreducibleSpace_of_isReduced X₀
  exact (MMP.Mori.isProjectiveVariety_iff k₀ _).2
    ⟨(MMP.Mori.isVariety_iff k₀ _).2 ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
      hP⟩

/-- A projective variety over an algebraically closed field `k` of characteristic zero is the
base change of a projective variety over a countable algebraically closed subfield of `k`. -/
private theorem exists_countable_isAlgClosed_isPullback {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX] :
    ∃ (k₀ : Subfield k) (_ : Countable k₀) (_ : IsAlgClosed k₀) (X₀ : Scheme.{0})
      (s₀ : X₀ ⟶ Spec (.of k₀)) (π : X ⟶ X₀),
      IsPullback π sX s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) ∧
        MMP.Mori.IsProjectiveVariety k₀ s₀ := by
  classical
  obtain ⟨n, i, hi, hio⟩ := AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k) (f := sX)
  let F : Discrete PUnit.{1} ⥤ Over (Spec (.of k)) := (Functor.const _).obj (Over.mk sX)
  have : ∀ _ : Discrete PUnit.{1}, IsImmersion i := fun _ => inferInstance
  obtain ⟨R, hR⟩ := MMP.CoefficientModels.exists_fgSubalgebra_diagram_model ℤ k F n
    (fun _ => i) (fun _ => hio)
  obtain ⟨Y, ιY, p, -, -, hover, hpb, -, -, hcl, -⟩ := hR R le_rfl
  let j : Discrete PUnit.{1} := ⟨⟨⟩⟩
  have hYP : IsProjectiveMorphism (Y.obj j).hom := ⟨n, ιY j, hcl j hi, hover j⟩
  have hS : ((R.1 : Subalgebra ℤ k) : Set k).Countable := by
    obtain ⟨t, ht⟩ := R.2
    have := t.finite_toSet.to_subtype
    rw [← ht, Algebra.adjoin_eq_range]
    exact Set.countable_range _
  obtain ⟨hc, halg⟩ :=
    MMP.Resolution.Bridges.nonempty_ringHom_complex_and_countable_algebraicClosure.2 k _ hS
  let L := algebraicClosure (Subfield.closure ((R.1 : Subalgebra ℤ k) : Set k)) k
  let k₀ : Subfield k := L.toSubfield
  have hmem : ∀ x : R.1, (x : k) ∈ k₀ := fun x =>
    L.algebraMap_mem ⟨x, Subfield.subset_closure x.2⟩
  let φ : R.1 →+* k₀ := RingHom.codRestrict R.1.val.toRingHom k₀ hmem
  let g := Spec.map (CommRingCat.ofHom φ)
  have hg : Spec.map (CommRingCat.ofHom (algebraMap R.1 k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ k)) ≫ g := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hbig : IsPullback (p j) sX (Y.obj j).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)) ≫ g) := hg ▸ hpb j
  have hw : p j ≫ (Y.obj j).hom = (sX ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) ≫ g :=
    hbig.w.trans (Category.assoc _ _ _).symm
  refine ⟨k₀, hc, halg, Limits.pullback (Y.obj j).hom g, Limits.pullback.snd _ _,
    Limits.pullback.lift (p j) (sX ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) hw, ?_⟩
  have hπ : IsPullback (Limits.pullback.lift (p j)
      (sX ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) hw)
      sX (Limits.pullback.snd (Y.obj j).hom g)
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) :=
    IsPullback.of_right (by rwa [Limits.pullback.lift_fst]) (Limits.pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback _ _)
  exact ⟨hπ, isProjectiveVariety_of_isPullback hπ (hYP.baseChange g)⟩

/-- The base change of a projective variety over an algebraically closed field to any field
extension is a projective variety. -/
private theorem isProjectiveVariety_pullback_snd {k K : Type} [Field k] [IsAlgClosed k]
    [Field K] [Algebra k K] {Y : Scheme.{0}} (s : Y ⟶ Spec (.of k))
    [MMP.Mori.IsProjectiveVariety k s] :
    MMP.Mori.IsProjectiveVariety K
      (Limits.pullback.snd s (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hP : IsProjectiveMorphism (Limits.pullback.snd s g) :=
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k) (f := s)).baseChange g
  have := isProper_of_isProjectiveMorphism _ hP
  have : GeometricallyIrreducible s :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k Y s
  have : GeometricallyReduced s := geometricallyReduced_of_isReduced s
  have : IsIntegral (Limits.pullback s g) :=
    (GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible s).1 g _ _
      (IsPullback.of_hasPullback s g)
  exact (MMP.Mori.isProjectiveVariety_iff K _).2
    ⟨(MMP.Mori.isVariety_iff K _).2
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hP⟩

/-- `N₁` of a projective variety over a countable algebraically closed field of characteristic
zero is finite dimensional. -/
private theorem finiteDimensional_of_countable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]
    [CharZero k₀] [Countable k₀] {X₀ : Scheme.{0}} (s₀ : X₀ ⟶ Spec (.of k₀))
    [MMP.Mori.IsProjectiveVariety k₀ s₀] :
    FiniteDimensional ℝ (NumericalCurveClasses s₀) := by
  obtain ⟨ι⟩ := (MMP.Resolution.Bridges.nonempty_ringHom_complex_and_countable_algebraicClosure.1
    k₀ : Nonempty (k₀ →+* ℂ))
  letI : Algebra k₀ ℂ := ι.toAlgebra
  let g := Spec.map (CommRingCat.ofHom (algebraMap k₀ ℂ))
  have := isProjectiveVariety_pullback_snd (K := ℂ) s₀
  have : FiniteDimensional ℝ (NumericalCurveClasses (Limits.pullback.snd s₀ g)) :=
    Module.rank_lt_aleph0_iff.1 (Cardinal.toENat_lt_top.1
      (picardNumber_lt_top_of_isProjectiveVariety (Limits.pullback.snd s₀ g)))
  exact (MMP.Fourfold.numericalCurveClassesBaseChange s₀ (Limits.pullback.snd s₀ g)
    (Limits.pullback.fst s₀ g) (IsPullback.of_hasPullback s₀ g) ‹_›).symm.finiteDimensional

/-- For a projective variety `X` over an algebraically closed field `k` of characteristic zero,
the real vector space `N₁(X)` of numerical classes of curves is finite dimensional. -/
@[mmp "lem_mmp_foundation_projective_n1_finite_alg_closed_char_zero"]
public theorem NumericalCurveClasses.finiteDimensional_of_isProjectiveVariety
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX] :
    FiniteDimensional ℝ (NumericalCurveClasses sX) := by
  obtain ⟨k₀, _, _, X₀, s₀, π, hπ, _⟩ := exists_countable_isAlgClosed_isPullback sX
  have := finiteDimensional_of_countable s₀
  exact (MMP.Fourfold.numericalCurveClassesBaseChange s₀ sX π hπ ‹_›).finiteDimensional

end MMP.Mori
