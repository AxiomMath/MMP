module

public import MMP.AlgebraicGeometry.Singularities.CyclicCover.Algebra
import all MMP.AlgebraicGeometry.Singularities.CyclicCover.Algebra

/-!
# Affine charts of a cyclic cover

Let `p : Z ⟶ X` be the cyclic cover of an invertible sheaf `N = L⁻¹`, of `m` and of
`σ = ⟨·, s⟩ : Symᵐ(N) ⟶ 𝒪_X`. Every point of `X` has an affine open neighbourhood `U` on which
`N` is trivial, with basis `t`; over such a `U` the map `Γ(X, U)[T] ⟶ Γ(Z, p⁻¹U)`, `T ↦ t`, is
surjective with kernel `(Tᵐ - f)` for `f = σ(tᵐ)`, and the ideal of the zero scheme `(s = 0)` on
`U` is `(f)`. The cover is an affine morphism, and for `0 < m` it is finite, flat and surjective.

## Main results

* `MMP.Mori.isAffineHom_cyclicCoverToBase`
* `MMP.Mori.exists_cyclicCover_chart`
* `MMP.Mori.zeroSchemeIdeal_ideal_eq_span_range`
* `MMP.Mori.isFinite_cyclicCoverToBase`, `MMP.Mori.flat_cyclicCoverToBase`,
  `MMP.Mori.surjective_cyclicCoverToBase`: for `0 < m` the cover is finite, flat and surjective,
  since `Γ(X, U)[T]/(Tᵐ - f)` is free of rank `m ≥ 1` over `Γ(X, U)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.50
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Polynomial

universe u

namespace MMP.Mori

variable {X : Scheme.{u}} (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (m : ℕ) (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit X.ringCatSheaf)

/-- The cyclic cover is an affine morphism. -/
public theorem isAffineHom_cyclicCoverToBase : IsAffineHom (cyclicCoverToBase N m σ) := by
  haveI : IsAffineHom (symSpecToBase N) := Stacks.RelativeSpec.isAffineHom_toBase _
  unfold cyclicCoverToBase
  infer_instance

/-- **Affine charts of a cyclic cover.** Every point `x` of `X` lies in an affine open `U` with
an element `f ∈ Γ(X, U)` and a surjection `φ : Γ(X, U)[T] ⟶ Γ(Z, p⁻¹U)` restricting to `p` on
constants, with kernel `(Tᵐ - f)`, such that the zero scheme of `σ` has ideal `(f)` on `U`. -/
public theorem exists_cyclicCover_chart (x : X) :
    ∃ (U : X.affineOpens) (_ : x ∈ U.1) (f : Γ(X, U.1))
      (φ : Γ(X, U.1)[X] →+* Γ(cyclicCover N m σ, cyclicCoverToBase N m σ ⁻¹ᵁ U.1)),
      Function.Surjective φ ∧ φ.comp C = ((cyclicCoverToBase N m σ).app U.1).hom ∧
        RingHom.ker φ = Ideal.span {Polynomial.X ^ m - C f} ∧
        (zeroSchemeIdeal N m σ).ideal U = Ideal.span {f} := by
  obtain ⟨U, ⟨hU, -, ⟨b⟩⟩, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
    (cyclicCoverSituation N).isBasis_chartOpens (show x ∈ (⊤ : X.Opens) from trivial)
  refine ⟨⟨U, hU⟩, hxU, chartCoeff N ⟨U, hU⟩ b m σ, chartPresentation N ⟨U, hU⟩ b m σ,
    chartPresentation_surjective N ⟨U, hU⟩ b m σ, chartPresentation_comp_C N ⟨U, hU⟩ b m σ,
    ker_chartPresentation N ⟨U, hU⟩ b m σ, ?_⟩
  rw [zeroSchemeIdeal_ideal]
  refine le_antisymm (Ideal.span_le.mpr ?_)
    ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.subset_span ⟨_, rfl⟩))
  rintro _ ⟨y, rfl⟩
  obtain ⟨c, rfl⟩ := exists_eq_smul_basisPow N ⟨U, hU⟩ b m y
  rw [(σ.val.app (op U)).hom.map_smul]
  exact Ideal.mul_mem_left _ c (Ideal.subset_span rfl)

/-- If `ψ : R[T] → A` is surjective with kernel `(Tᵐ - f)` and `0 < m`, then `R → A` is finite,
flat and surjective on spectra: `A` is free of rank `m` over `R`. -/
private theorem finite_flat_surjective_of_ker {R A : Type u} [CommRing R] [CommRing A]
    (ψ : R[X] →+* A) (hs : Function.Surjective ψ) {m : ℕ} (hm : 0 < m) {f : R}
    (hk : RingHom.ker ψ = Ideal.span {Polynomial.X ^ m - C f}) :
    (ψ.comp C).Finite ∧ (ψ.comp C).Flat ∧
      Function.Surjective (PrimeSpectrum.comap (ψ.comp C)) := by
  letI := (ψ.comp C).toAlgebra
  let e : AdjoinRoot (Polynomial.X ^ m - C f) ≃ₐ[R] A := AlgEquiv.ofRingEquiv
    (f := (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hs))
    fun _ => rfl
  have hmon : (Polynomial.X ^ m - C f).Monic := monic_X_pow_sub_C f hm.ne'
  have := hmon.finite_adjoinRoot
  have := hmon.free_adjoinRoot
  have : Module.Free R A := Module.Free.of_equiv e.toLinearEquiv
  refine ⟨RingHom.finite_algebraMap.mpr (Module.Finite.equiv e.toLinearEquiv),
    RingHom.flat_algebraMap_iff.mpr inferInstance, ?_⟩
  by_cases hR : Nontrivial R
  · have hd : 0 < (AdjoinRoot.powerBasis' hmon).dim := by
      rwa [AdjoinRoot.powerBasis'_dim, natDegree_X_pow_sub_C]
    have : Nontrivial (AdjoinRoot (Polynomial.X ^ m - C f)) :=
      nontrivial_of_ne _ 0 ((AdjoinRoot.powerBasis' hmon).basis.ne_zero ⟨0, hd⟩)
    have : Nontrivial A := e.toEquiv.symm.nontrivial
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := A)
  · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    exact fun x => (x.isPrime.ne_top (Subsingleton.elim _ ⊤)).elim

/-- For `0 < m` the cyclic cover is finite, flat and surjective. -/
private theorem isFinite_flat_surjective_cyclicCoverToBase (hm : 0 < m) :
    IsFinite (cyclicCoverToBase N m σ) ∧ Flat (cyclicCoverToBase N m σ) ∧
      Surjective (cyclicCoverToBase N m σ) := by
  let T := {U : X.affineOpens // Nonempty (Module.Basis PUnit.{u + 1} Γ(X, U.1) Γ(N, U.1))}
  have hT : ⨆ U : T, (U.1 : X.affineOpens).1 = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨U, ⟨hU, -, hb⟩, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
      (cyclicCoverSituation N).isBasis_chartOpens (show x ∈ (⊤ : X.Opens) from trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, hb⟩, hxU⟩
  haveI := isAffineHom_cyclicCoverToBase N m σ
  haveI := Stacks.Morphisms.isFinite_isZariskiLocalAtTarget.{u}
  haveI := Stacks.Morphisms.isFinite_respectsIso.{u}
  haveI : IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Flat)
  refine ⟨(IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _ hT).2 fun U => ?_,
    (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Flat) _ hT).2 fun U => ?_,
    (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Surjective) _ hT).2 fun U => ?_⟩ <;>
  obtain ⟨U, ⟨b⟩⟩ := U <;>
  haveI : IsAffine (cyclicCoverToBase N m σ ⁻¹ᵁ U.1).toScheme := U.2.preimage _ <;>
  haveI : IsAffine U.1.toScheme := U.2 <;>
  have h := chartPresentation_comp_C N U b m σ ▸ finite_flat_surjective_of_ker _
    (chartPresentation_surjective N U b m σ) hm (ker_chartPresentation N U b m σ)
  · rw [MorphismProperty.arrow_mk_iso_iff @IsFinite (arrowIsoSpecΓOfIsAffine _),
      IsFinite.SpecMap_iff]
    exact appTop_morphismRestrict _ _ _ h.1
  · exact (HasRingHomProperty.iff_of_isAffine (P := @Flat)).2 (appTop_morphismRestrict _ _ _ h.2.1)
  · rw [MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine _)]
    exact ⟨appTop_morphismRestrict _ _
      (fun {R S} [CommRing R] [CommRing S] (φ : R →+* S) =>
        Function.Surjective (PrimeSpectrum.comap φ)) h.2.2⟩

/-- For `0 < m` the cyclic cover is finite. -/
public theorem isFinite_cyclicCoverToBase (hm : 0 < m) : IsFinite (cyclicCoverToBase N m σ) :=
  (isFinite_flat_surjective_cyclicCoverToBase N m σ hm).1

/-- For `0 < m` the cyclic cover is flat. -/
public theorem flat_cyclicCoverToBase (hm : 0 < m) : Flat (cyclicCoverToBase N m σ) :=
  (isFinite_flat_surjective_cyclicCoverToBase N m σ hm).2.1

/-- For `0 < m` the cyclic cover is surjective. -/
public theorem surjective_cyclicCoverToBase (hm : 0 < m) : Surjective (cyclicCoverToBase N m σ) :=
  (isFinite_flat_surjective_cyclicCoverToBase N m σ hm).2.2

/-- On an affine open `V` the ideal of the zero scheme `(s = 0)` is generated by the image of
`σ = ⟨·, s⟩` on `V`. -/
public theorem zeroSchemeIdeal_ideal_eq_span_range (V : X.affineOpens) :
    (zeroSchemeIdeal N m σ).ideal V =
      (Ideal.span (Set.range (σ.val.app (op V.1))) : Ideal Γ(X, V.1)) := by
  rw [zeroSchemeIdeal_ideal]
  rfl

end MMP.Mori
