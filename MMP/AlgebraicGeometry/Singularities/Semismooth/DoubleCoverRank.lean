/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Singularities.Semismooth.DoubleCoverFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteOverFieldStalks
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.RingTheory.AdicCompletion.LiftToComplete

/-!
# The rank of the double cover of the double locus

The rank of a finite flat morphism `f : X ⟶ S` at `s` is the dimension of the ring of functions
on the fibre `X_s` over `κ(s)`. When every residue field of the fibre is `κ(s)`, this is the sum
over the points of the fibre of the lengths of their local rings, the local ring of `X_s` at a
point `x` being `𝒪_{X,x} ⧸ 𝔪_s 𝒪_{X,x}`.

## Main results

* `MMP.Flips.finrank_eq_finsum_length_of_surjective`,
  `MMP.Flips.finrank_eq_finsum_length_quotient`: the rank of a finite flat morphism at a point
  with rational fibre is the sum of the lengths of the local rings of the fibre.
* `MMP.Flips.length_quotient_eq_length_quotient_map_adicCompletion`: the length of an Artinian
  quotient of a Noetherian local ring is read on the completion.
* `MMP.Flips.length_quotient_map_maximalIdeal_of_dnc`,
  `MMP.Flips.length_quotient_map_maximalIdeal_of_pinch`: the closed fibre of a factor of the
  normalization of the double normal crossing model is a point, that of the pinch point model is
  `k[u] ⧸ (u²)`.
* `MMP.Flips.natCard_preimage_normalization_of_dnc`,
  `MMP.Flips.natCard_preimage_normalization_of_pinch`: the normalization has two points over a
  double normal crossing point and one over a pinch point.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 12.2.1
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace MMP.Flips

/-- **The rank of a finite flat morphism at a point with rational fibre.** Let `f : X ⟶ S` be
finite and flat and `s ∈ S` a point at which every residue field of the fibre `X_s` is `κ(s)`.
Then the rank of `f` at `s` is the sum over the points `w` of `X_s` of the lengths of
`𝒪_{X_s,w}`. -/
theorem finrank_eq_finsum_length_of_surjective {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [IsFinite f] (s : S)
    (hres : ∀ w : f.fiber s, ∀ b : (f.fiber s).presheaf.stalk w, ∃ c : S.residueField s,
      b - ((f.fiber s).presheaf.germ ⊤ w (by simp)).hom
        (((Scheme.ΓSpecIso (S.residueField s)).inv ≫ (f.fiberToSpecResidueField s).appTop).hom c)
        ∈ maximalIdeal ((f.fiber s).presheaf.stalk w)) :
    f.finrank s = ∑ᶠ w : f.fiber s,
      (Module.length ((f.fiber s).presheaf.stalk w) ((f.fiber s).presheaf.stalk w)).toNat := by
  have : IsFinite (f.fiberToSpecResidueField s) := MorphismProperty.of_isPullback (P := @IsFinite)
    (IsPullback.of_hasPullback f (S.fromSpecResidueField s)) ‹IsFinite f›
  have : Flat (f.fiberToSpecResidueField s) := MorphismProperty.of_isPullback (P := @Flat)
    (IsPullback.of_hasPullback f (S.fromSpecResidueField s)) ‹Flat f›
  set t : Spec (S.residueField s) := IsLocalRing.closedPoint _
  have ht : S.fromSpecResidueField s t = s := Scheme.fromSpecResidueField_apply s t
  have hpb := Scheme.Hom.finrank_pullback_snd f (S.fromSpecResidueField s) t
  rw [ht] at hpb
  rw [← hpb]
  change (f.fiberToSpecResidueField s).finrank t = _
  refine (@Stacks.Morphisms.finrank_eq_finrank_sections_of_specField _ _ _
      (f.fiberToSpecResidueField s) ‹_› ‹_› t).trans
    ((@finrank_globalSections_eq_finsum_finrank_stalk (S.residueField s) _ _
      (f.fiberToSpecResidueField s) ‹_›).trans ?_)
  refine finsum_congr fun w => ?_
  refine (@finrank_stalk_eq_length_mul_finrank_residueField (S.residueField s) _ _
    (f.fiberToSpecResidueField s) ‹_› w).trans ?_
  let : Algebra (S.residueField s) ((f.fiber s).presheaf.stalk w) :=
    (((f.fiber s).presheaf.germ ⊤ w (by simp)).hom.comp
      ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
        (f.fiberToSpecResidueField s).appTop).hom).toAlgebra
  have hsurj : Function.Surjective (algebraMap (S.residueField s)
      (ResidueField ((f.fiber s).presheaf.stalk w))) := by
    intro r
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨c, hc⟩ := hres w b
    refine ⟨c, ?_⟩
    rw [IsScalarTower.algebraMap_apply (S.residueField s) ((f.fiber s).presheaf.stalk w)]
    exact (Ideal.Quotient.eq.mpr hc).symm
  have h1 : Module.finrank (S.residueField s) (ResidueField ((f.fiber s).presheaf.stalk w)) = 1 :=
    (LinearEquiv.finrank_eq (AlgEquiv.ofBijective (Algebra.ofId _ _)
      ⟨fun a b h => (algebraMap (S.residueField s)
        (ResidueField ((f.fiber s).presheaf.stalk w))).injective h,
        hsurj⟩).toLinearEquiv).symm.trans (Module.finrank_self _)
  rw [h1, mul_one]

/-- **Rational residue fields of a fibre.** Let `f : X ⟶ S` be a morphism over a field `k` and
`w` a point of the fibre `X_s`. If the residue field of `X` at the image of `w` is spanned by `k`,
then the residue field of `X_s` at `w` is spanned by `κ(s)`. -/
theorem exists_sub_mem_maximalIdeal_fiber {k : Type u} [Field k] {X S : Scheme.{u}}
    (sS : S ⟶ Spec (.of k)) (f : X ⟶ S) (s : S) (w : f.fiber s)
    (hX : ∀ b : X.presheaf.stalk (f.fiberι s w), ∃ c : k,
      b - stalkStructureMap (f ≫ sS) (f.fiberι s w) c ∈
        maximalIdeal (X.presheaf.stalk (f.fiberι s w)))
    (b : (f.fiber s).presheaf.stalk w) : ∃ c : S.residueField s,
      b - ((f.fiber s).presheaf.germ ⊤ w (by simp)).hom
        (((Scheme.ΓSpecIso (S.residueField s)).inv ≫ (f.fiberToSpecResidueField s).appTop).hom c)
        ∈ maximalIdeal ((f.fiber s).presheaf.stalk w) := by
  obtain ⟨b', rfl⟩ := (f.fiberι s).stalkMap_surjective w b
  obtain ⟨c, hc⟩ := hX b'
  set q := S.fromSpecResidueField s ≫ sS
  refine ⟨(Scheme.ΓSpecIso (S.residueField s)).hom.hom
    (q.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)), ?_⟩
  have h1 := map_nonunit ((f.fiberι s).stalkMap w).hom _ hc
  rw [map_sub, stalkMap_stalkStructureMap] at h1
  have h2 : stalkStructureMap (f.fiberι s ≫ f ≫ sS) w c =
      ((f.fiber s).presheaf.germ ⊤ w (by simp)).hom
        (((Scheme.ΓSpecIso (S.residueField s)).inv ≫ (f.fiberToSpecResidueField s).appTop).hom
          ((Scheme.ΓSpecIso (S.residueField s)).hom.hom
            (q.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)))) := by
    rw [← Category.assoc, Scheme.Hom.fiber_fac, Category.assoc]
    simp only [stalkStructureMap, q, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply, Category.assoc]
    congr 2
    simp
  rwa [← h2]

/-- The length of a ring over itself is invariant under ring isomorphisms. -/
theorem length_self_eq_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R'] (e : R ≃+* R') :
    Module.length R R = Module.length R' R' := by
  let := e.toRingHom.toAlgebra
  rw [← Module.length_eq_of_surjective (R := R') (S := R) (M := R') e.surjective]
  let φ : R ≃ₗ[R] R' :=
    { e.toAddEquiv with map_smul' := fun r x => show e (r * x) = e r * e x from map_mul e r x }
  exact φ.length_eq

/-- **The rank of a finite flat morphism over a field, with rational fibres.** Let `f : X ⟶ S`
be finite and flat, over a field `k`, and `s ∈ S` a point such that every residue field of `X`
over `s` is spanned by `k`. Then the rank of `f` at `s` is the sum, over the points `x` of `X`
over `s`, of the lengths of the fibre rings `𝒪_{X,x} ⧸ 𝔪_s 𝒪_{X,x}`. -/
theorem finrank_eq_finsum_length_quotient {k : Type u} [Field k] {X S : Scheme.{u}}
    (sS : S ⟶ Spec (.of k)) (f : X ⟶ S) [Flat f] [IsFinite f] (s : S)
    (hX : ∀ x : X, f x = s → ∀ b : X.presheaf.stalk x, ∃ c : k,
      b - stalkStructureMap (f ≫ sS) x c ∈ maximalIdeal (X.presheaf.stalk x)) :
    f.finrank s = ∑ᶠ x : f ⁻¹' {s},
      (Module.length (X.presheaf.stalk x.1 ⧸
          (maximalIdeal (S.presheaf.stalk (f x.1))).map (f.stalkMap x.1).hom)
        (X.presheaf.stalk x.1 ⧸
          (maximalIdeal (S.presheaf.stalk (f x.1))).map (f.stalkMap x.1).hom)).toNat := by
  have hmem : ∀ w : f.fiber s, f (f.fiberι s w) = s := fun w => by
    have := ((f.fiberHomeo s) w).2
    rwa [Scheme.Hom.fiberHomeo_apply] at this
  rw [finrank_eq_finsum_length_of_surjective f s
    (fun w b => exists_sub_mem_maximalIdeal_fiber sS f s w (hX _ (hmem w)) b)]
  rw [← finsum_comp_equiv (f.fiberHomeo s).toEquiv]
  refine finsum_congr fun w => ?_
  have key : ∀ (x : X) (s : S) (h : f x = s) (w : f.fiber s), f.fiberι s w = x →
      Module.length ((f.fiber s).presheaf.stalk w) ((f.fiber s).presheaf.stalk w) =
        Module.length (X.presheaf.stalk x ⧸
            (maximalIdeal (S.presheaf.stalk (f x))).map (f.stalkMap x).hom)
          (X.presheaf.stalk x ⧸
            (maximalIdeal (S.presheaf.stalk (f x))).map (f.stalkMap x).hom) := by
    intro x s h w hw
    subst h
    obtain rfl : w = f.asFiber x :=
      (f.fiberι (f x)).isEmbedding.injective (hw.trans (f.fiberι_asFiber x).symm)
    exact (length_self_eq_of_ringEquiv (quotientStalkEquivFiberStalk f x)).symm
  rw [key _ s (hmem w) w rfl]
  rfl

/-- **The length of an Artinian quotient is read on the completion.** For a Noetherian local
ring `R` and a proper ideal `K` with `R ⧸ K` Artinian, `R ⧸ K ≅ R̂ ⧸ K R̂`. -/
theorem length_quotient_eq_length_quotient_map_adicCompletion {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (K : Ideal R) (hK : K ≠ ⊤) [IsArtinianRing (R ⧸ K)] :
    Module.length (R ⧸ K) (R ⧸ K) =
      Module.length (AdicCompletion (maximalIdeal R) R ⧸
          K.map (algebraMap R (AdicCompletion (maximalIdeal R) R)))
        (AdicCompletion (maximalIdeal R) R ⧸
          K.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
  have : Nontrivial (R ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hK
  have : IsLocalRing (R ⧸ K) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  have hker := ker_adicCompletionMap_of_surjective (Ideal.Quotient.mk K)
    Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at hker
  let ê : (AdicCompletion (maximalIdeal R) R ⧸
      K.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) ≃+*
      AdicCompletion (maximalIdeal (R ⧸ K)) (R ⧸ K) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective
      (adicCompletionMap_surjective_of_surjective _ Ideal.Quotient.mk_surjective))
  have hcomp : IsAdicComplete (maximalIdeal (R ⧸ K)) (R ⧸ K) := by
    refine IsAdicComplete.of_isNilpotent _ ?_
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  have hbij : Function.Bijective (algebraMap (R ⧸ K)
      (AdicCompletion (maximalIdeal (R ⧸ K)) (R ⧸ K))) :=
    AdicCompletion.of_bijective_iff.mpr hcomp
  rw [length_self_eq_of_ringEquiv (RingEquiv.ofBijective _ hbij),
    length_self_eq_of_ringEquiv ê]

section Models

variable {k : Type u} [Field k]

/-- The maximal ideal of `k[[x]] ⧸ (h)` is generated by the classes of the variables. -/
theorem maximalIdeal_quotient_eq_span_range_X {m : ℕ} (h : MvPowerSeries (Fin m) k)
    [IsLocalRing (MvPowerSeries (Fin m) k ⧸ Ideal.span {h})] :
    maximalIdeal (MvPowerSeries (Fin m) k ⧸ Ideal.span {h}) =
      Ideal.span (Set.range fun i => Ideal.Quotient.mk _ (MvPowerSeries.X i)) := by
  have hmax : Ideal.span (Set.range (MvPowerSeries.X : Fin m → MvPowerSeries (Fin m) k)) =
      maximalIdeal _ := by
    rw [MvPowerSeries.span_X_eq_ker_constantCoeff,
      IsLocalRing.ker_eq_maximalIdeal (MvPowerSeries.constantCoeff :
        MvPowerSeries (Fin m) k →+* k) fun c => ⟨MvPowerSeries.C c, by simp⟩]
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {h}))
    Ideal.Quotient.mk_surjective, ← hmax, Ideal.map_span, ← Set.range_comp]
  rfl

/-- **The fibre of a factor of the normalization of the double normal crossing model is a
point**: `L ⧸ 𝔪 L` is a field. -/
theorem length_quotient_map_maximalIdeal_of_dnc {m : ℕ} {L : Type*}
    [CommRing L] [IsLocalRing L] [IsDomain L] [IsIntegrallyClosed L]
    [IsLocalRing (MvPowerSeries (Fin (m + 1 + 1)) k ⧸ Ideal.span
      {(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)})]
    (ψ : (MvPowerSeries (Fin (m + 1 + 1)) k ⧸ Ideal.span
      {(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)}) →+* L)
    (hint : ∀ l, ψ.IsIntegralElem l)
    (hbir : ∀ l, ∃ r s, s ∈ nonZeroDivisors _ ∧ ψ s * l = ψ r)
    (hnz : ∀ s ∈ nonZeroDivisors _, ψ s ≠ 0) :
    Module.length (L ⧸ (maximalIdeal _).map ψ) (L ⧸ (maximalIdeal _).map ψ) = 1 := by
  rw [IsLocalRing.map_maximalIdeal_of_surjective ψ (surjective_and_comap_of_dnc ψ hint hbir hnz).1]
  let : Field (L ⧸ maximalIdeal L) := Ideal.Quotient.field _
  exact Module.length_eq_one _ _

open PowerSeries in
/-- The kernel of `B⟦u⟧ → k⟦u⟧ ⧸ (u²)`, `B = k[[x₀, …, x_m]]`, reducing the coefficients modulo
the maximal ideal of `B`, is `(u², x₀, …, x_m)`. -/
theorem ker_quotient_comp_map_constantCoeff {m : ℕ} :
    RingHom.ker ((Ideal.Quotient.mk (maximalIdeal k⟦X⟧ ^ 2)).comp
      (PowerSeries.map (MvPowerSeries.constantCoeff : MvPowerSeries (Fin (m + 1)) k →+* k))) =
      Ideal.span (insert (PowerSeries.X ^ 2) (Set.range fun j : Fin (m + 1) =>
        PowerSeries.C (MvPowerSeries.X j : MvPowerSeries (Fin (m + 1)) k))) := by
  have hm2 : maximalIdeal k⟦X⟧ ^ 2 = Ideal.span {PowerSeries.X ^ 2} := by
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow]
  refine le_antisymm (fun f hf => ?_) ?_
  · rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hm2,
      Ideal.mem_span_singleton] at hf
    obtain ⟨g, hg⟩ := hf
    have hcoef : ∀ n, ∃ c : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) k,
        PowerSeries.coeff n f - MvPowerSeries.C (MvPowerSeries.constantCoeff
          (PowerSeries.coeff n f)) = ∑ j, MvPowerSeries.X j * c j := by
      intro n
      have hmem : PowerSeries.coeff n f - MvPowerSeries.C (MvPowerSeries.constantCoeff
          (PowerSeries.coeff n f)) ∈
          Ideal.span (Set.range
            (MvPowerSeries.X : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) k)) := by
        rw [MvPowerSeries.span_X_eq_ker_constantCoeff, RingHom.mem_ker]
        simp
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
      exact ⟨c, by rw [← hc]; simp [smul_eq_mul, mul_comm]⟩
    choose c hc using hcoef
    have hf : f = ∑ j, PowerSeries.C (MvPowerSeries.X j) * PowerSeries.mk (fun n => c n j) +
        PowerSeries.X ^ 2 * PowerSeries.map
          (MvPowerSeries.C : k →+* MvPowerSeries (Fin (m + 1)) k) g := by
      refine PowerSeries.ext fun n => ?_
      have h1 : PowerSeries.coeff n (PowerSeries.X ^ 2 * PowerSeries.map
          (MvPowerSeries.C : k →+* MvPowerSeries (Fin (m + 1)) k) g) =
          MvPowerSeries.C (MvPowerSeries.constantCoeff (PowerSeries.coeff n f)) := by
        have : PowerSeries.X ^ 2 * PowerSeries.map (MvPowerSeries.C :
            k →+* MvPowerSeries (Fin (m + 1)) k) g =
            PowerSeries.map MvPowerSeries.C (PowerSeries.X ^ 2 * g) := by simp
        rw [this, PowerSeries.coeff_map, ← hg, PowerSeries.coeff_map]
      rw [map_add, h1, map_sum]
      simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
      rw [← hc n]
      ring
    rw [hf]
    refine add_mem (sum_mem fun j _ => Ideal.mul_mem_right _ _
      (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _)))
  · rw [Ideal.span_le]
    rintro _ (rfl | ⟨j, rfl⟩)
    · rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
        hm2, map_pow, PowerSeries.map_X]
      exact Ideal.mem_span_singleton_self _
    · rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, PowerSeries.map_C,
        MvPowerSeries.constantCoeff_X, map_zero, map_zero]

open PowerSeries in
/-- `k⟦u⟧ ⧸ (u²)` has length `2`. -/
theorem length_quotient_maximalIdeal_sq_powerSeries :
    Module.length (k⟦X⟧ ⧸ maximalIdeal k⟦X⟧ ^ 2) (k⟦X⟧ ⧸ maximalIdeal k⟦X⟧ ^ 2) = 2 := by
  rw [← Module.length_eq_of_surjective (S := k⟦X⟧) Ideal.Quotient.mk_surjective,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  rfl

open PowerSeries in
/-- **The fibre of a factor of the normalization of the pinch point model** is `k[u] ⧸ (u²)`, of
length `2`. -/
theorem length_quotient_map_maximalIdeal_of_pinch {m : ℕ} {L : Type*}
    [CommRing L] [IsLocalRing L] [IsDomain L] [IsIntegrallyClosed L]
    [IsLocalRing (MvPowerSeries (Fin (m + 3)) k ⧸ Ideal.span
      {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin (m + 3)) k)})]
    (ψ : (MvPowerSeries (Fin (m + 3)) k ⧸ Ideal.span
      {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin (m + 3)) k)}) →+* L)
    (hint : ∀ l, ψ.IsIntegralElem l)
    (hbir : ∀ l, ∃ r s, s ∈ nonZeroDivisors _ ∧ ψ s * l = ψ r)
    (hnz : ∀ s ∈ nonZeroDivisors _, ψ s ≠ 0) :
    Module.length (L ⧸ (maximalIdeal _).map ψ) (L ⧸ (maximalIdeal _).map ψ) = 2 := by
  obtain ⟨σ, h0, h1, h2, -⟩ := exists_ringEquiv_powerSeries_of_pinch ψ hint hbir hnz
  set T : Ideal (MvPowerSeries (Fin (m + 1)) k)⟦X⟧ :=
    Ideal.span (insert (PowerSeries.X ^ 2) (Set.range fun j : Fin (m + 1) =>
      PowerSeries.C (MvPowerSeries.X j : MvPowerSeries (Fin (m + 1)) k)))
  have hJ : T = ((maximalIdeal _).map ψ).map σ := by
    rw [maximalIdeal_quotient_eq_span_range_X, Ideal.map_span, Ideal.map_span, ← Set.range_comp,
      ← Set.range_comp]
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le]
      rintro _ (rfl | ⟨j, rfl⟩)
      · exact Ideal.subset_span ⟨1, h1⟩
      · exact Ideal.subset_span ⟨j.succ.succ, h2 j⟩
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · change σ (ψ (Ideal.Quotient.mk _ (MvPowerSeries.X 0))) ∈ T
        rw [h0]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨0, rfl⟩))
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · change σ (ψ (Ideal.Quotient.mk _ (MvPowerSeries.X 1))) ∈ T
        rw [h1]
        exact Ideal.subset_span (Set.mem_insert _ _)
      · change σ (ψ (Ideal.Quotient.mk _ (MvPowerSeries.X j'.succ.succ))) ∈ T
        rw [h2]
        exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j', rfl⟩)
  let e₁ : (L ⧸ (maximalIdeal _).map ψ) ≃+* ((MvPowerSeries (Fin (m + 1)) k)⟦X⟧ ⧸ T) :=
    Ideal.quotientEquiv _ T σ hJ
  have hsurj : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal k⟦X⟧ ^ 2)).comp
      (PowerSeries.map (MvPowerSeries.constantCoeff : MvPowerSeries (Fin (m + 1)) k →+* k))) := by
    refine Ideal.Quotient.mk_surjective.comp fun g => ⟨PowerSeries.map MvPowerSeries.C g, ?_⟩
    ext n
    simp
  let e₂ : ((MvPowerSeries (Fin (m + 1)) k)⟦X⟧ ⧸ T) ≃+* (k⟦X⟧ ⧸ maximalIdeal k⟦X⟧ ^ 2) :=
    (Ideal.quotEquivOfEq ker_quotient_comp_map_constantCoeff.symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)
  rw [length_self_eq_of_ringEquiv (e₁.trans e₂), length_quotient_maximalIdeal_sq_powerSeries]

/-- Every element of `k[[x]] ⧸ (h)` is congruent to a constant modulo the maximal ideal. -/
theorem sub_algebraMap_constantCoeff_mem_maximalIdeal {m : ℕ} (h : MvPowerSeries (Fin m) k)
    [IsLocalRing (MvPowerSeries (Fin m) k ⧸ Ideal.span {h})] (f : MvPowerSeries (Fin m) k) :
    Ideal.Quotient.mk (Ideal.span {h}) f -
      algebraMap k _ (MvPowerSeries.constantCoeff f) ∈ maximalIdeal _ := by
  have hc : algebraMap k (MvPowerSeries (Fin m) k ⧸ Ideal.span {h})
      (MvPowerSeries.constantCoeff f) =
      Ideal.Quotient.mk _ (MvPowerSeries.C (MvPowerSeries.constantCoeff f)) := rfl
  rw [hc, ← map_sub, ← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
  refine Ideal.mem_map_of_mem _ ?_
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
  simp

/-- **The residue field of a factor of the normalization of the double normal crossing model is
`k`.** -/
theorem exists_sub_mem_maximalIdeal_of_dnc {m : ℕ} {L : Type*}
    [CommRing L] [IsLocalRing L] [IsDomain L] [IsIntegrallyClosed L]
    [IsLocalRing (MvPowerSeries (Fin (m + 1 + 1)) k ⧸ Ideal.span
      {(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)})]
    (ψ : (MvPowerSeries (Fin (m + 1 + 1)) k ⧸ Ideal.span
      {(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)}) →+* L)
    (hint : ∀ l, ψ.IsIntegralElem l)
    (hbir : ∀ l, ∃ r s, s ∈ nonZeroDivisors _ ∧ ψ s * l = ψ r)
    (hnz : ∀ s ∈ nonZeroDivisors _, ψ s ≠ 0) (l : L) :
    ∃ c : k, l - ψ (algebraMap k _ c) ∈ maximalIdeal L := by
  have hsurj := (surjective_and_comap_of_dnc ψ hint hbir hnz).1
  obtain ⟨r, rfl⟩ := hsurj l
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨MvPowerSeries.constantCoeff f, ?_⟩
  rw [← map_sub, ← IsLocalRing.map_maximalIdeal_of_surjective ψ hsurj]
  exact Ideal.mem_map_of_mem _ (sub_algebraMap_constantCoeff_mem_maximalIdeal _ f)

open PowerSeries in
/-- **The residue field of a factor of the normalization of the pinch point model is `k`.** -/
theorem exists_sub_mem_maximalIdeal_of_pinch {m : ℕ} {L : Type*}
    [CommRing L] [IsLocalRing L] [IsDomain L] [IsIntegrallyClosed L]
    (ψ : (MvPowerSeries (Fin (m + 3)) k ⧸ Ideal.span
      {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin (m + 3)) k)}) →+* L)
    (hint : ∀ l, ψ.IsIntegralElem l)
    (hbir : ∀ l, ∃ r s, s ∈ nonZeroDivisors _ ∧ ψ s * l = ψ r)
    (hnz : ∀ s ∈ nonZeroDivisors _, ψ s ≠ 0) (l : L) :
    ∃ c : k, l - ψ (algebraMap k _ c) ∈ maximalIdeal L := by
  obtain ⟨σ, -, -, -, hc⟩ := exists_ringEquiv_powerSeries_of_pinch ψ hint hbir hnz
  refine ⟨MvPowerSeries.constantCoeff (PowerSeries.constantCoeff (σ l)), ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := hu.map σ
  rw [map_sub, hc, PowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.isUnit_iff_constantCoeff]
    at this
  simp at this

/-- In `k[[x]] ⧸ (x₀ x₁)`, written as `k[[x]] ⧸ (xᵢ xⱼ)`, the class of `xⱼ` is nonzero. -/
theorem mk_X_ne_zero_of_mul_X_eq {m : ℕ} {i j : Fin (m + 1 + 1)}
    (hij : (MvPowerSeries.X i * MvPowerSeries.X j : MvPowerSeries (Fin (m + 1 + 1)) k) =
      MvPowerSeries.X 0 * MvPowerSeries.X 1) :
    Ideal.Quotient.mk (Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 :
      MvPowerSeries (Fin (m + 1 + 1)) k)}) (MvPowerSeries.X j) ≠ 0 := by
  have : IsRegularLocalRing (MvPowerSeries (Fin (m + 1 + 1)) k) :=
    MvPowerSeries.isRegularLocalRing k (m + 1 + 1)
  have : IsDomain (MvPowerSeries (Fin (m + 1 + 1)) k) := IsRegularLocalRing.isDomain _
  intro h
  rw [Ideal.Quotient.eq_zero_iff_dvd, ← hij] at h
  obtain ⟨q, hq⟩ := h
  have hXj : (MvPowerSeries.X j : MvPowerSeries (Fin (m + 1 + 1)) k) ≠ 0 := fun h0 => by
    simpa using congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) h0
  have h1 : (1 : MvPowerSeries (Fin (m + 1 + 1)) k) = MvPowerSeries.X i * q :=
    mul_left_cancel₀ hXj (by linear_combination hq)
  have hu : IsUnit (MvPowerSeries.X i : MvPowerSeries (Fin (m + 1 + 1)) k) :=
    isUnit_iff_exists_inv.mpr ⟨q, h1.symm⟩
  rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at hu
  exact not_isUnit_zero hu

/-- Two factors of the normalization of the double normal crossing model which both kill `x₀`
have the same kernel. -/
theorem map_eq_zero_iff_of_dnc {m : ℕ} {L L' : Type*}
    [CommRing L] [IsLocalRing L] [IsDomain L] [IsIntegrallyClosed L]
    [CommRing L'] [IsLocalRing L'] [IsDomain L'] [IsIntegrallyClosed L']
    (ψ : (MvPowerSeries (Fin (m + 1 + 1)) k ⧸ Ideal.span
      {(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)}) →+* L)
    (ψ' : (MvPowerSeries (Fin (m + 1 + 1)) k ⧸ Ideal.span
      {(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)}) →+* L')
    (hψ : (∀ l, ψ.IsIntegralElem l) ∧ (∀ l, ∃ r s, s ∈ nonZeroDivisors _ ∧ ψ s * l = ψ r) ∧
      ∀ s ∈ nonZeroDivisors _, ψ s ≠ 0)
    (h0 : ψ (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) = 0)
    (hψ' : (∀ l, ψ'.IsIntegralElem l) ∧ (∀ l, ∃ r s, s ∈ nonZeroDivisors _ ∧ ψ' s * l = ψ' r) ∧
      ∀ s ∈ nonZeroDivisors _, ψ' s ≠ 0)
    (h0' : ψ' (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) = 0) (r) :
    ψ r = 0 ↔ ψ' r = 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [eq_zero_iff_dvd_of_dnc ψ hψ.1 hψ.2.1 hψ.2.2 h0,
    eq_zero_iff_dvd_of_dnc ψ' hψ'.1 hψ'.2.1 hψ'.2.2 h0']

end Models

/-- **The factors of a normalization have distinct kernels.** Let `N ≅ ∏ᵢ Lᵢ` be the integral
closure of `Ac` in its total ring of fractions, with nontrivial factors. Then `Ac → ∏ᵢ Lᵢ` is
injective, and two factor maps `Ac → Lᵢ`, `Ac → Lᵢ'` with the same kernel have `i = i'`. -/
theorem injective_and_eq_of_ker_eq_of_normalization {Ac N : Type*} [CommRing Ac] [CommRing N]
    {I : Type*} {L : I → Type*} [∀ i, CommRing (L i)] [∀ i, Nontrivial (L i)] (j : Ac →+* N)
    (e : N ≃+* ∀ i, L i) (g : N →+* FractionRing Ac) (hg : Function.Injective g)
    (hrange : g.range = (integralClosure Ac (FractionRing Ac)).toSubring)
    (hgj : ∀ y, g (j y) = algebraMap Ac (FractionRing Ac) y) :
    (∀ r, (∀ i, e (j r) i = 0) → r = 0) ∧
      ∀ i i', (∀ r, e (j r) i = 0 ↔ e (j r) i' = 0) → i = i' := by
  classical
  refine ⟨fun r hr => ?_, fun i i' hii' => ?_⟩
  · have h2 : g (j r) = 0 := by rw [e.map_eq_zero_iff.mp (funext hr), map_zero]
    rw [hgj] at h2
    exact IsFractionRing.injective Ac (FractionRing Ac) (h2.trans (map_zero _).symm)
  · by_contra hne
    obtain ⟨-, -, hnz⟩ := factor_props_of_normalization j e g hg hrange hgj i
    set m := e.symm (Pi.single i 1)
    obtain ⟨x, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors Ac) (g m)
    have hmul : g (j x.2 * m) = g (j x.1) := by
      rw [map_mul, hgj, hgj, ← hab, mul_comm]
      exact IsLocalization.mk'_spec (FractionRing Ac) x.1 x.2
    have heq := congrArg e (hg hmul)
    have hi := congrFun heq i
    have hi' := congrFun heq i'
    simp only [map_mul, Pi.mul_apply, m, RingEquiv.apply_symm_apply, Pi.single_eq_same,
      mul_one, Pi.single_eq_of_ne' hne, mul_zero] at hi hi'
    have h0 : e (j x.1) i = 0 := (hii' x.1).mpr hi'.symm
    exact hnz _ x.2.2 (hi.trans h0)

section Normalization

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- The completed local rings of the normalization of a reduced scheme of finite type over a
field are local normal domains. -/
theorem isLocalRing_and_isNormalDomain_adicCompletion_normalization [LocallyOfFiniteType sX]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (w : X.normalizationScheme hX) :
    IsLocalRing (AdicCompletion (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk w))
        ((X.normalizationScheme hX).presheaf.stalk w)) ∧
      IsNormalDomain (AdicCompletion (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk w))
        ((X.normalizationScheme hX).presheaf.stalk w)) := by
  have : IsFinite (X.normalization hX) := Scheme.isFinite_normalization
    (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
  have : LocallyOfFiniteType (X.normalization hX ≫ sX) := inferInstance
  have hexc : IsExcellent ((X.normalizationScheme hX).presheaf.stalk w) :=
    AlgebraicGeometry.isExcellent_stalk_of_locallyOfFiniteType_of_isExcellent k
      ((isExcellent_of_standard_classes_and_finiteType.{u, u}).1 k) (X.normalization hX ≫ sX) w
  have : IsNoetherianRing ((X.normalizationScheme hX).presheaf.stalk w) := hexc.1.1
  have hNormal : IsNormal (X.normalizationScheme hX) := Scheme.isNormal_normalizationScheme X hX
  have hn : IsNormalRing ((X.normalizationScheme hX).presheaf.stalk w) := by
    have : IsDomain ((X.normalizationScheme hX).presheaf.stalk w) := hNormal.stalk_isDomain w
    have : IsIntegrallyClosed ((X.normalizationScheme hX).presheaf.stalk w) :=
      hNormal.stalk_normal w
    exact IsNormalRing.of_isIntegrallyClosed _
  exact ⟨AdicCompletion.isLocalRing_of_fg (IsNoetherian.noetherian _),
    AlgebraicGeometry.isNormalDomain_adicCompletion_of_isExcellent _ hexc hn⟩

/-- **The factors of the completed normalization over a point.** For `x ∈ X`, the completions of
the local rings of `X^ν` at the points over `x` receive `𝒪̂_{X,x}`, each integrally and
birationally with no non-zero-divisor in the kernel; jointly injectively; and with pairwise
distinct kernels. -/
theorem exists_factors_normalization_completion [IsReduced X] [LocallyOfFiniteType sX]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    ∃ ψ : ∀ y : (X.normalization hX).base ⁻¹' {x}, CompletedLocalRing X x →+*
        AdicCompletion (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk y))
          ((X.normalizationScheme hX).presheaf.stalk y),
      (∀ y, (∀ l, (ψ y).IsIntegralElem l) ∧
        (∀ l, ∃ r s, s ∈ nonZeroDivisors _ ∧ ψ y s * l = ψ y r) ∧
        (∀ s ∈ nonZeroDivisors _, ψ y s ≠ 0)) ∧
      (∀ r, (∀ y, ψ y r = 0) → r = 0) ∧
      ∀ y y', (∀ r, ψ y r = 0 ↔ ψ y' r = 0) → y = y' := by
  obtain ⟨-, ⟨e₁, -⟩, g, hg, hrange, hgy⟩ :=
    MMP.Resolution.isReduced_adicCompletion_stalk_and_normalization_completion X sX hX x
  let : Algebra (X.presheaf.stalk x) (Scheme.normalizationPushforwardStalk X hX x) :=
    Scheme.normalizationPushforwardStalkAlgebra X hX x
  have : ∀ y : (X.normalization hX).base ⁻¹' {x}, Nontrivial (AdicCompletion
      (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk y))
      ((X.normalizationScheme hX).presheaf.stalk y)) := fun y => by
    have := (isLocalRing_and_isNormalDomain_adicCompletion_normalization (sX := sX) hX y).1
    infer_instance
  obtain ⟨hinj, hdist⟩ := injective_and_eq_of_ker_eq_of_normalization
    Algebra.TensorProduct.includeRight.toRingHom e₁ g hg hrange hgy
  exact ⟨fun y => (Pi.evalRingHom _ y).comp (e₁.toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom),
    fun y => factor_props_of_normalization _ e₁ g hg hrange hgy y, hinj, hdist⟩

/-- **The normalization of a pinch point has one point over it**: the model is a domain. -/
theorem natCard_preimage_normalization_of_pinch [IsReduced X] [LocallyOfFiniteType sX]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) {x : X} {m : ℕ}
    (hmod : HasCompletedLocalModel sX x
      (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin (m + 3)) k)) :
    Nat.card ((X.normalization hX).base ⁻¹' {x}) = 1 := by
  obtain ⟨ψ, hprops, hinj, hdist⟩ := exists_factors_normalization_completion (sX := sX) hX x
  let := (stalkStructureMap sX x).toAlgebra
  obtain ⟨e⟩ := hmod
  have := isDomain_quotient_pinch (k := k) m
  have : IsDomain (CompletedLocalRing X x) := e.toRingEquiv.toMulEquiv.isDomain
  have hker : ∀ y r, ψ y r = 0 ↔ r = 0 := fun y r =>
    ⟨fun h => by_contra fun hr => (hprops y).2.2 r (mem_nonZeroDivisors_of_ne_zero hr) h,
      fun h => by rw [h, map_zero]⟩
  have : Subsingleton ((X.normalization hX).base ⁻¹' {x}) :=
    ⟨fun y y' => hdist y y' fun r => by rw [hker, hker]⟩
  have : Nonempty ((X.normalization hX).base ⁻¹' {x}) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have : Nontrivial (CompletedLocalRing X x) := e.toRingEquiv.toEquiv.nontrivial
    exact one_ne_zero (hinj 1 isEmptyElim)
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

/-- **The normalization of a double normal crossing point has two points over it**, one on each
branch. -/
theorem natCard_preimage_normalization_of_dnc [IsReduced X] [LocallyOfFiniteType sX]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) {x : X} {m : ℕ}
    (hmod : HasCompletedLocalModel sX x
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)) :
    Nat.card ((X.normalization hX).base ⁻¹' {x}) = 2 := by
  obtain ⟨ψ, hprops, hinj, hdist⟩ := exists_factors_normalization_completion (sX := sX) hX x
  let := (stalkStructureMap sX x).toAlgebra
  obtain ⟨e⟩ := hmod
  set e' := e.toRingEquiv
  obtain ⟨τ, hτ⟩ := exists_ringEquiv_swap_dnc (k := k) m
  have hL := fun y : (X.normalization hX).base ⁻¹' {x} =>
    isLocalRing_and_isNormalDomain_adicCompletion_normalization (sX := sX) hX y
  have := fun y => (hL y).1
  have := fun y => (hL y).2.isDomain
  have := fun y => (hL y).2.isIntegrallyClosed
  set ψ' := fun y => (ψ y).comp e'.symm.toRingHom
  have hψ' : ∀ y r, ψ y r = ψ' y (e' r) := fun y r => by simp [ψ']
  have props' := fun y => props_comp_symm_of_ringEquiv (ψ y) e' (hprops y).1 (hprops y).2.1
    (hprops y).2.2
  have hprod : ∀ y, ψ' y (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) = 0 ∨
      ψ' y (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) = 0 := fun y => by
    refine mul_eq_zero.mp ?_
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
      map_zero]
  have key0 : ∀ y y', ψ' y (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) = 0 →
      ψ' y' (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) = 0 → y = y' := fun y y' h h' =>
    hdist y y' fun r => by
      rw [hψ', hψ']
      exact map_eq_zero_iff_of_dnc (ψ' y) (ψ' y') (props' y) h (props' y') h' _
  set ψ'' := fun y => (ψ' y).comp τ.symm.symm.toRingHom
  have props'' := fun y => props_comp_symm_of_ringEquiv (ψ' y) τ.symm (props' y).1
    (props' y).2.1 (props' y).2.2
  have h0 : ∀ y, ψ' y (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) = 0 →
      ψ'' y (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) = 0 := fun y hy => by
    simpa only [ψ'', RingEquiv.symm_symm, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, hτ] using hy
  have key1 : ∀ y y', ψ' y (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) = 0 →
      ψ' y' (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) = 0 → y = y' := fun y y' h h' =>
    hdist y y' fun r => by
      have hr : ∀ y, ψ y r = ψ'' y (τ.symm (e' r)) := fun y => by simp [ψ'', hψ']
      rw [hr, hr]
      exact map_eq_zero_iff_of_dnc (ψ'' y) (ψ'' y') (props'' y) (h0 y h) (props'' y') (h0 y' h') _
  have hex : ∀ i : Fin (m + 1 + 1), Ideal.Quotient.mk (Ideal.span {(MvPowerSeries.X 0 *
      MvPowerSeries.X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)}) (MvPowerSeries.X i) ≠ 0 →
      ∃ y, ψ' y (Ideal.Quotient.mk _ (MvPowerSeries.X i)) ≠ 0 := fun i hi => by
    by_contra hall
    simp only [not_exists, not_not] at hall
    refine hi (e'.symm.injective ((hinj _ fun y => ?_).trans (map_zero _).symm))
    rw [hψ', RingEquiv.apply_symm_apply]
    exact hall y
  obtain ⟨y1, hy1⟩ := hex 0 (mk_X_ne_zero_of_mul_X_eq (mul_comm _ _))
  obtain ⟨y0, hy0⟩ := hex 1 (mk_X_ne_zero_of_mul_X_eq rfl)
  have hy0' := (hprod y0).resolve_right hy0
  refine Nat.card_eq_two_iff.mpr ⟨y0, y1, fun h => hy1 (h ▸ hy0'),
    Set.eq_univ_of_forall fun y => ?_⟩
  exact (hprod y).imp (key0 y y0 · hy0') (key1 y y1 · ((hprod y1).resolve_left hy1))

end Normalization

end MMP.Flips
