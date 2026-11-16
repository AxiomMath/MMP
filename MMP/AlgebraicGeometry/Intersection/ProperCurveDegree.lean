module
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Morphisms.ChowLemma
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationGlobal

/-!
# Degrees along proper curves, normal Chow modifications, separable base change

This file collects four foundational facts.

* **Additivity of the degree.** For a field `k`, a `k`-scheme `X` and a morphism `i : C ⟶ X`
  from a scheme of dimension at most one proper over `k`, the degree
  `deg_C L = χ(C, i^* L) - χ(C, 𝒪_C)` of invertible sheaves on `X` is additive:
  `deg_C (L ⊗ M) = deg_C L + deg_C M`.
* **The projection formula along a proper curve.** Let `h : V ⟶ X` be a morphism of varieties
  over `k`, `C ⊆ V` a proper integral curve and `L = ∑ⱼ cⱼ Lⱼ` a `ℚ`-Cartier divisor on `X`.
  Then `(h^*L · C) = ∑ⱼ cⱼ deg_C (h|_C)^* 𝒪_X(Lⱼ)` vanishes when `h(C)` is a point, and otherwise
  equals `[k(C) : k(h(C))] · (L · h(C))`. Neither `h` nor `X` is assumed proper, and `X` is not
  assumed normal.
* **Normal projective Chow modification.** A proper birational morphism `f : Y ⟶ X` of varieties
  is dominated by a projective birational `h : Y' ⟶ Y` from a normal variety with `h ≫ f`
  projective: normalize the variety given by the relative Chow lemma.
* **Separable base change preserves reducedness.** If `L` is a separable `k`-algebra and `A` a
  reduced `k`-algebra, then `L ⊗[k] A` is reduced.

## Main results

* `MMP.Mori.degreeOn_tensorSheaf_eq_add`: `deg_C (L ⊗ M) = deg_C L + deg_C M`.
* `MMP.Mori.KCartierDivisor.sum_degreeOn_comp_eq_degreeOver_mul`: both cases of the projection
  formula.
* `MMP.Resolution.Bridges.exists_isProjective_isBirational_isNormal_chowModification`: the normal
  projective Chow modification.
* `MMP.isReduced_tensorProduct_of_isSeparable`: `IsReduced (L ⊗[k] A)`.

## Implementation notes

* The invertibility of `L ⊗ M`, needed to form its degree, is supplied by
  `Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible` rather than assumed.
* Since `h` may contract `C`, the pull-back `h^*L` need not be a Cartier divisor. As in [KM,
  Notation 0.4(5)], `(h^*L · C)` is computed on `X` along the composite `i ≫ h : C ⟶ X`, as
  `∑ⱼ cⱼ · MMP.Mori.degreeOn k s_X (i ≫ h) _ 𝒪_X(Lⱼ)`, where `𝒪_X(Lⱼ)` is
  `MMP.CartierDivisor.sheaf Lⱼ`. The curve `h(C)` is the scheme-theoretic image
  `(i ≫ h).image`, and `[k(C) : k(h(C))]` is `AlgebraicGeometry.degreeOver (i ≫ h).toImage`.
* Projectivity is `AlgebraicGeometry.IsProjective` (Stacks 01W8: a closed immersion into the
  projective bundle of a quasi-coherent module of finite type over the base), the convention in
  which a finite morphism is projective and projective morphisms compose over a quasi-compact
  quasi-separated base.
* The separable extension `L` is only required to be a commutative `k`-algebra with
  `Algebra.IsSeparable k L`. The proof reduces twice to finitely generated subalgebras
  (`IsReduced.tensorProduct_of_flat_of_forall_fg`). A finitely generated subalgebra of `L` is
  Artinian and reduced, so a finite product of finite separable field extensions `F / k`; a
  finitely generated reduced `k`-algebra embeds into the product of the fraction fields `K` of its
  quotients by minimal primes; and `K ⊗[k] F` is reduced, being formally unramified over `K`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0AYZ](https://stacks.math.columbia.edu/tag/0AYZ)
* [Stacks Project, Tag 030U](https://stacks.math.columbia.edu/tag/030U)
* [Stacks Project, Tag 00I3](https://stacks.math.columbia.edu/tag/00I3)
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace MMP.Mori

/-- **Additivity of the degree** [Stacks, Tag 0AYX]: for invertible sheaves `L` and `M` on `X`
and a curve `i : C ⟶ X` proper over `k`, `deg_C (L ⊗ M) = deg_C L + deg_C M`. -/
@[mmp "lem_mmp_threefold_proper_curve_degree_additive"]
public theorem degreeOn_tensorSheaf_eq_add (k : Type u) [Field k] {X C : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) (L M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    letI := Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf
      X.ringCatSheaf.2 L M
    degreeOn k sX i hdim (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj L).obj M) =
      degreeOn k sX i hdim L + degreeOn k sX i hdim M :=
  degreeOn_tensorSheaf k sX i hdim L M

namespace KCartierDivisor

/-- **The projection formula along a proper curve.** Let `h : V ⟶ X` be a morphism of
varieties over `k` (`h ≫ s_X = s_V`), `i : C ⟶ V` a proper integral curve in `V`, and
`L = ∑ⱼ cⱼ Lⱼ` a `ℚ`-Cartier divisor on `X`. Then `(h^*L · C) = ∑ⱼ cⱼ deg_C (i ≫ h)^* 𝒪_X(Lⱼ)`
is `0` if `h(C)` is a point. Otherwise it equals `[k(C) : k(h(C))] · (L · h(C))`, where `h(C)` is
the reduced image `(i ≫ h).image`. -/
@[mmp "lem_mmp_fa15_curve_projection"]
public theorem sum_degreeOn_comp_eq_degreeOver_mul {k : Type u} [Field k]
    {V X C : Scheme.{u}} (sV : V ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    [IsVariety k sV] [IsVariety k sX]
    (h : V ⟶ X) (hh : h ≫ sX = sV)
    (i : C ⟶ V) [IsClosedImmersion i] [IsCurve k (i ≫ sV)] [IsProper (i ≫ sV)]
    (L : KCartierDivisor ℚ X) :
    haveI : IsProper ((i ≫ h) ≫ sX) := by rw [Category.assoc, hh]; infer_instance
    haveI : IsCurve k ((i ≫ h) ≫ sX) := by rw [Category.assoc, hh]; infer_instance
    haveI : IsProper (i ≫ h) := IsProper.of_comp (i ≫ h) sX
    haveI : IsProper ((i ≫ h).imageι ≫ sX) := isProper_imageι_comp (i ≫ h) sX
    haveI : QuasiCompact (i ≫ h) := instQuasiCompactOfUniversallyClosed (i ≫ h)
    haveI : LocallyOfFiniteType (i ≫ h) := IsProper.toLocallyOfFiniteType
    haveI : IsIntegral (i ≫ h).image := isIntegral_image (i ≫ h)
    ((∃ x : X, Set.range (i ≫ h) = {x}) →
        (L.sum fun E c => c * (degreeOn k sX (i ≫ h)
          (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sV)).le
          (MMP.CartierDivisor.sheaf E) : ℚ)) = 0) ∧
      (¬ (∃ x : X, Set.range (i ≫ h) = {x}) →
        (L.sum fun E c => c * (degreeOn k sX (i ≫ h)
          (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sV)).le
          (MMP.CartierDivisor.sheaf E) : ℚ)) =
          (degreeOver (i ≫ h).toImage : ℚ) *
            L.sum fun E c => c * (degreeOn k sX (i ≫ h).imageι
              (topologicalKrullDim_image_le_one sX (i ≫ h))
              (MMP.CartierDivisor.sheaf E) : ℚ)) := by
  have : IsProper ((i ≫ h) ≫ sX) := by rw [Category.assoc, hh]; infer_instance
  have : IsCurve k ((i ≫ h) ≫ sX) := by rw [Category.assoc, hh]; infer_instance
  refine ⟨fun hpt => Finset.sum_eq_zero fun E _ => ?_, fun hnc => ?_⟩
  · simp [degreeOn_eq_zero_of_range_eq_singleton sX (i ≫ h) _ hpt]
  · rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun E _ => ?_
    rw [degreeOn_eq_degreeOver_mul sX (i ≫ h) _ hnc]
    push_cast
    ring

end KCartierDivisor

end MMP.Mori

namespace MMP.Resolution.Bridges

/-- **Normal projective Chow modification.** Let `f : Y ⟶ X` be a proper birational morphism of
varieties over a field `k`. Then there is a projective birational morphism `h : Y' ⟶ Y` from a
normal variety `Y'` such that `h ≫ f` is projective. -/
@[mmp "lem_mmp_foundation_fa_normal_relative_chow"]
public theorem exists_isProjective_isBirational_isNormal_chowModification (k : Type u) [Field k]
    {Y X : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)}
    (hY : IsVariety k sY) (hX : IsVariety k sX) (f : Y ⟶ X) (hf : f ≫ sX = sY)
    (hfp : IsProper f) (hfb : IsBirational f) :
    ∃ (Y' : Scheme.{u}) (h : Y' ⟶ Y), IsVariety k (h ≫ sY) ∧ IsNormal Y' ∧
      IsProjective h ∧ IsBirational h ∧ IsProjective (h ≫ f) := by
  obtain ⟨T, p, hT, hp, -, hpb, hpf⟩ :=
    (exists_isProjectiveMorphism_isBirational_chowModification k).1 hY hX f hf hfp
  have hlft : LocallyOfFiniteType (p ≫ sY) := hT.toLocallyOfFiniteType
  let n₀ := @normalizationOverField k _ T (p ≫ sY) hlft
  have hcomp := @finite_irreducibleComponents_of_locallyOfFiniteType k _ T (p ≫ sY) hlft
  have hfin : IsFinite n₀ := @isFinite_normalizationOverField k _ T (p ≫ sY) hlft
  have hn₀v : IsVariety k (n₀ ≫ p ≫ sY) := @isVariety_normalizationOverField k _ T (p ≫ sY) hT
  have hn₀p : IsProjective n₀ :=
    @Stacks.FiniteMorphismProjective.isProjective_of_isFinite _ _ n₀ hfin
  have : CompactSpace Y := by
    haveI := hY.toQuasiCompact; exact (quasiCompact_iff_compactSpace sY).1 inferInstance
  have : CompactSpace X := by
    haveI := hX.toQuasiCompact; exact (quasiCompact_iff_compactSpace sX).1 inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  refine ⟨_, n₀ ≫ p, by simpa only [Category.assoc] using hn₀v,
    Scheme.isNormal_normalizationScheme T hcomp, hn₀p.comp hp.isProjective,
    (Scheme.isBirational_normalization T hcomp).comp hpb, ?_⟩
  rw [Category.assoc]
  exact hn₀p.comp hpf.isProjective

end MMP.Resolution.Bridges

namespace MMP

/-- A separable algebra over a field is reduced. -/
private theorem isReduced_of_isSeparable (k L : Type*) [Field k] [CommRing L] [Algebra k L]
    [Algebra.IsSeparable k L] : IsReduced L := by
  refine ⟨fun x ⟨n, hn⟩ ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simpa using congrArg (· * x) hn
  have hdvd : minpoly k x ∣ Polynomial.X ^ n := minpoly.dvd k x (by simp [hn])
  rw [(Algebra.IsSeparable.isSeparable k x).squarefree.dvd_pow_iff_dvd hpos.ne'] at hdvd
  obtain ⟨q, hq⟩ := hdvd
  simpa using congrArg (Polynomial.aeval x) hq

/-- Separability passes to the target of a surjective algebra homomorphism. -/
private theorem isSeparable_of_surjective {k B C : Type*} [Field k] [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] [Algebra.IsSeparable k B] (f : B →ₐ[k] C)
    (hf : Function.Surjective f) : Algebra.IsSeparable k C := ⟨fun c ↦ by
  obtain ⟨b, rfl⟩ := hf c
  exact (Algebra.IsSeparable.isSeparable k b).of_dvd (minpoly.dvd k (f b) (by
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]))⟩

/-- Reducedness of a tensor product does not depend on the order of the factors. -/
private theorem isReduced_tensorProduct_comm {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [IsReduced (A ⊗[R] B)] : IsReduced (B ⊗[R] A) :=
  isReduced_of_injective (Algebra.TensorProduct.comm R B A)
    (Algebra.TensorProduct.comm R B A).injective

/-- `A ⊗[R] ∏ᵢ Bᵢ` is reduced when every `A ⊗[R] Bᵢ` is, for a finite product. -/
private theorem isReduced_tensorProduct_pi {R A ι : Type*} {B : ι → Type*} [Fintype ι]
    [DecidableEq ι] [CommRing R] [CommRing A] [Algebra R A] [∀ i, CommRing (B i)]
    [∀ i, Algebra R (B i)] [∀ i, IsReduced (A ⊗[R] B i)] : IsReduced (A ⊗[R] ∀ i, B i) :=
  isReduced_of_injective (Algebra.TensorProduct.piRight R R A B)
    (Algebra.TensorProduct.piRight R R A B).injective

/-- Reducedness of `A ⊗[R] B` descends along an injection `S →ₐ[R] B`, for `A` flat. -/
private theorem isReduced_tensorProduct_of_injective_right {R A S B : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A] [CommRing S] [CommRing B] [Algebra R S]
    [Algebra R B] (f : S →ₐ[R] B) (hf : Function.Injective f) [IsReduced (A ⊗[R] B)] :
    IsReduced (A ⊗[R] S) :=
  isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id R A) f)
    (Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf)

/-- A reduced ring embeds into the product of the fraction fields of its quotients by minimal
primes. -/
private theorem injective_pi_fractionRing_minimalPrimes (C : Type*) [CommRing C] [IsReduced C] :
    Function.Injective (Pi.ringHom fun p : minimalPrimes C ↦
      algebraMap C (FractionRing (C ⧸ (p : Ideal C)))) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmem : x ∈ sInf (minimalPrimes C) := Submodule.mem_sInf.2 fun p hp ↦ by
    have h : algebraMap C (FractionRing (C ⧸ (p : Ideal C))) x = 0 := congrFun hx ⟨p, hp⟩
    have : Ideal.IsPrime p := hp.1.1
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    refine IsFractionRing.injective (C ⧸ (p : Ideal C)) (FractionRing (C ⧸ (p : Ideal C))) ?_
    rw [map_zero, ← h, IsScalarTower.algebraMap_apply C (C ⧸ (p : Ideal C)),
      Ideal.Quotient.algebraMap_eq]
  rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hmem
  exact IsReduced.eq_zero x hmem

/-- Base change of a reduced Noetherian algebra along a finite separable field extension is
reduced. -/
private theorem isReduced_tensorProduct_of_isNoetherianRing {k F C : Type*} [Field k] [Field F]
    [Algebra k F] [Algebra.IsSeparable k F] [FiniteDimensional k F] [CommRing C] [Algebra k C]
    [IsReduced C] [IsNoetherianRing C] : IsReduced (F ⊗[k] C) := by
  classical
  have : Fintype (minimalPrimes C) := (minimalPrimes.finite_of_isNoetherianRing C).fintype
  have (p : minimalPrimes C) : (p : Ideal C).IsPrime := p.2.1.1
  have := Algebra.FormallyUnramified.of_isSeparable k F
  have (p : minimalPrimes C) : IsReduced (F ⊗[k] FractionRing (C ⧸ (p : Ideal C))) :=
    have : IsReduced (FractionRing (C ⧸ (p : Ideal C)) ⊗[k] F) :=
      Algebra.FormallyUnramified.isReduced_of_field (FractionRing (C ⧸ (p : Ideal C))) _
    isReduced_tensorProduct_comm
  have := isReduced_tensorProduct_pi (R := k) (A := F)
    (B := fun p : minimalPrimes C ↦ FractionRing (C ⧸ (p : Ideal C)))
  exact isReduced_tensorProduct_of_injective_right
    (Pi.algHom k (fun p : minimalPrimes C ↦ FractionRing (C ⧸ (p : Ideal C)))
      fun p ↦ IsScalarTower.toAlgHom k C _)
    (injective_pi_fractionRing_minimalPrimes C)

/-- Base change of a reduced algebra along a finite separable field extension is reduced. -/
private theorem isReduced_tensorProduct_of_finiteDimensional {k F A : Type*} [Field k] [Field F]
    [Algebra k F] [Algebra.IsSeparable k F] [FiniteDimensional k F] [CommRing A] [Algebra k A]
    [IsReduced A] : IsReduced (F ⊗[k] A) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun C hC ↦ ?_
  have : Algebra.FiniteType k C := (Subalgebra.fg_iff_finiteType C).mp hC
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  have : IsReduced C := isReduced_of_injective C.val Subtype.val_injective
  exact isReduced_tensorProduct_of_isNoetherianRing

/-- Base change of a reduced algebra along a finite-dimensional separable algebra is reduced. -/
private theorem isReduced_tensorProduct_of_finite {k B A : Type*} [Field k] [CommRing B]
    [Algebra k B] [Algebra.IsSeparable k B] [Module.Finite k B] [CommRing A] [Algebra k A]
    [IsReduced A] : IsReduced (A ⊗[k] B) := by
  classical
  have : IsArtinianRing B := IsArtinianRing.of_finite k B
  have : IsReduced B := isReduced_of_isSeparable k B
  have : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  have (m : MaximalSpectrum B) : IsReduced (A ⊗[k] (B ⧸ m.asIdeal)) := by
    have := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    have := isSeparable_of_surjective (Ideal.Quotient.mkₐ k m.asIdeal)
      (Ideal.Quotient.mkₐ_surjective k _)
    have : IsReduced ((B ⧸ m.asIdeal) ⊗[k] A) := isReduced_tensorProduct_of_finiteDimensional
    exact isReduced_tensorProduct_comm
  have := isReduced_tensorProduct_pi (R := k) (A := A)
    (B := fun m : MaximalSpectrum B ↦ B ⧸ m.asIdeal)
  exact isReduced_tensorProduct_of_injective_right
    ((IsArtinianRing.equivPi B).toAlgHom.restrictScalars k) (IsArtinianRing.equivPi B).injective

/-- Base change of a reduced commutative `k`-algebra `A` along a separable `k`-algebra `L`
(e.g. a separable algebraic field extension) is reduced [Stacks, Tag 030U]. -/
@[mmp "lem_mmp_threefold_reduced_separable_scalar_extension"]
public theorem isReduced_tensorProduct_of_isSeparable (k L A : Type*) [Field k] [CommRing L]
    [Algebra k L] [Algebra.IsSeparable k L] [CommRing A] [Algebra k A] [IsReduced A] :
    IsReduced (L ⊗[k] A) := by
  suffices IsReduced (A ⊗[k] L) from isReduced_tensorProduct_comm
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB ↦ ?_
  have : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).mp hB
  have : Algebra.IsSeparable k B :=
    Subalgebra.isSeparable_iff.2 fun x _ ↦ Algebra.IsSeparable.isSeparable k x
  have : Module.Finite k B := Algebra.IsIntegral.finite
  exact isReduced_tensorProduct_of_finite

end MMP
