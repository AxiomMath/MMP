module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.PairClasses
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGermTypes
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward
import StacksFrontier.AlgebraicGeometry.Chow.FlatPullbackCycles.SchemeTheoreticImage
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
import MMP.AlgebraicGeometry.Intersection.CurveCartierLocal
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowup
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Intersection.SelfIntersectionHilbertDegree
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
import MMP.AlgebraicGeometry.Positivity.FreePencilCrepant
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.NormalThreefoldSlice
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula

/-!
# Exceptional curves of surface resolutions: Noether's formula and log canonical obstructions

Let `Y` be a smooth surface over an algebraically closed field `k`, `y ∈ Y` a closed point and
`π : Y' ⟶ Y` the blow-up of `y`, with exceptional curve `F`. For distinct curves `C`, `D` through
`y` with strict transforms `C'`, `D'`, *Noether's formula* reads
`(C · D)_y = mult_y C · mult_y D + ∑_{q ∈ F ∩ C' ∩ D'} (C' · D')_q`.
It is proved through the projection formula for the birational morphism of curves `D' ⟶ D`
induced by `π`: with `f` a local equation of `C` at `y`, `(C · D)_y` is the order of vanishing of
`f|_D` at `y`, the sum of the orders of `π^* f|_{D'}` over `F ∩ D'`; since `π^* C = C' + m F`
with `m = mult_y C`, each term is `(C' · D')_q + m (F · D')_q`, and
`∑_{q ∈ F ∩ D'} (F · D')_q = (D' · F) = mult_y D`.

For a resolution `g : Y ⟶ X` of a surface germ with boundary `(X, P; B)`, exceptional curves
`E_1, …, E_n`, log discrepancy vector `a` and `Θ_{g,a} = g⁻¹_* B + ∑_j (1 - a_j) E_j`:

* a closed point `y ∈ g⁻¹(P)` with `mult_y Θ_{g,a} > 2` obstructs log canonicity, since blowing
  up `y` produces the log discrepancy `2 - mult_y Θ_{g,a} < 0`;
* so do two components of `Θ_{g,a}` with coefficient `1`, smooth at `y` and tangent there
  (`(C₁ · C₂)_y ≥ 2`): after one blow-up Noether's formula makes their strict transforms meet on
  the exceptional curve, at a point of multiplicity at least `3` of the new boundary;
* every component of `B` meets some `E_j`, as the fibre `g⁻¹(P)` is connected;
* if the weighted dual graph of `g` is a rational tree, the `E_j` are smooth rational curves
  meeting transversally, at most once per pair, with no triple points.

## Main results

* `MMP.Threefold.Resolution.localIntersectionNumber_eq_multiplicityAt_mul_add_finsum`:
  Noether's formula.
* `MMP.Flips.IsGermLogDiscrepancyVector.not_isLogCanonical_of_two_lt_multiplicityAt`: a point
  of multiplicity `> 2` of `Θ_{g,a}` over `P` obstructs log canonicity near `P`.
* `MMP.Flips.IsGermLogDiscrepancyVector.not_isLogCanonical_of_two_le_localIntersectionNumber`:
  the tangency obstruction.
* `MMP.Flips.IsGermResolution.exists_one_le_inverseTransform_intersectionNumber`: every
  component `B_i` of `B` has `(g⁻¹_* B_i · E_j) ≥ 1` for some `j`.
* `MMP.Flips.IsWeightedDualGraph.simpleNormalCrossing_of_isRationalTree`: a rational-tree dual
  graph forces simple normal crossings.

## Implementation notes

Curves on a surface are prime divisors. Local intersection numbers are
`MMP.Mori.localIntersectionNumber`, the `k`-dimension of `𝒪_q / (I_C + I_D)`; Noether's formula
is stated in `ℕ∞`, where multiplicities live, with a `finsum` over the finite set
`F ∩ C' ∩ D'`. Its projection formula is Stacks 02RT
(`Stacks.Chow.properPushforward_principalDivisorCycle`) in the field situation, with orders of
vanishing at closed points identified with `k`-dimensions through lengths. "Smooth at `y`" for a
curve `C` is the existence of a point of the closed subscheme `C` over `y` in the smooth locus
of `C ↪ Y ⟶ Spec k`. Global intersection numbers are the relation
`MMP.Mori.IsIntersectionNumber`. The statement about boundary components holds over any field.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 3.1.4–3.1.6,
  3.3.2
* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution]
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

namespace MMP.Threefold.Resolution

open IsLocalRing

/-- For a local `k`-algebra `O` whose residue field is `k`, the `k`-dimension of a quotient of `O`
is its length. -/
private theorem finrank_quotient_eq_length (k : Type*) [Field k] {O : Type*} [CommRing O]
    [IsLocalRing O] [Algebra k O]
    (hk : Function.Surjective (algebraMap k (O ⧸ maximalIdeal O))) (J : Ideal O) :
    Module.finrank k (O ⧸ J) = (Module.length O (O ⧸ J)).toNat := by
  have : IsLocalHom (algebraMap k O) :=
    ⟨fun a ha ↦ by
      rcases eq_or_ne a 0 with rfl | h
      · rw [map_zero] at ha
        exact absurd ha not_isUnit_zero
      · exact isUnit_iff_ne_zero.2 h⟩
  have key := IsLocalRing.length_restrictScalars k O (O ⧸ J)
  have h2 : Module.length (ResidueField k) (ResidueField O) = Module.length k (ResidueField O) :=
    (Module.length_eq_of_surjective (S := k) (R := ResidueField k)
      IsLocalRing.residue_surjective).symm
  have hbij : Function.Bijective (algebraMap k (ResidueField O)) :=
    ⟨(algebraMap k (ResidueField O)).injective, hk⟩
  have h1 : Module.length k (ResidueField O) = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId k (ResidueField O)) hbij).toLinearEquiv.length_eq,
      Module.length_eq_finrank, Module.finrank_self]
    rfl
  rw [h2, h1, mul_one] at key
  rw [Module.finrank, ← Cardinal.toNat_toENat, ← Module.length_eq_rank, key]

/-- For a surjection `φ : R → S`, the length of `S / (φ t)` over `S` is the length of
`R / (ker φ + (t))` over `R`. -/
private theorem length_quotient_span_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (t : R) :
    Module.length S (S ⧸ Ideal.span {φ t}) =
      Module.length R (R ⧸ (RingHom.ker φ ⊔ Ideal.span {t})) := by
  let : Algebra R S := φ.toAlgebra
  set J : Ideal S := Ideal.span {φ t}
  let g : R →ₐ[R] S ⧸ J := (Ideal.Quotient.mkₐ R J).comp (Algebra.ofId R S)
  have hg : Function.Surjective g := (Ideal.Quotient.mk_surjective).comp hφ
  have hker : RingHom.ker g = RingHom.ker φ ⊔ Ideal.span {t} := by
    have h1 : RingHom.ker g = Ideal.comap φ J := by
      ext r
      simp only [RingHom.mem_ker, Ideal.mem_comap]
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [h1, show J = Ideal.map φ (Ideal.span {t}) by rw [Ideal.map_span, Set.image_singleton],
      Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot, sup_comm]
  have e := (Ideal.quotientKerAlgEquivOfSurjective hg).toLinearEquiv
  rw [← Module.length_eq_of_surjective (S := R) (R := S) hφ, ← e.length_eq]
  exact congrArg (fun I : Ideal R => Module.length R (R ⧸ I)) hker

/-- On a locally Noetherian integral scheme, the order of vanishing at a point of codimension one
of a nonzero element `c` of the local ring is the length of the quotient by `c`. -/
private theorem ord_algebraMap_eq_length {X : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X]
    {z : X} (hz : Order.coheight z = 1) {c : X.presheaf.stalk z} (hc0 : c ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk z) X.functionField c) z =
      ((Module.length (X.presheaf.stalk z) ((X.presheaf.stalk z) ⧸ Ideal.span {c})).toNat :
        ℤ) := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have hc : c ∈ nonZeroDivisors (X.presheaf.stalk z) := mem_nonZeroDivisors_of_ne_zero hc0
  have hfin : Ring.ord (X.presheaf.stalk z) c ≠ ⊤ := Ring.ord_ne_top hc
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hne : algebraMap (X.presheaf.stalk z) X.functionField c ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  rw [Scheme.ord_eq_iff hz hne]
  change Ring.ordFrac _ _ = _
  rw [Ring.ordFrac_eq_ord _ hc0, Ring.ordMonoidWithZeroHom_eq_coe _ hc hn.symm]
  have hlen : (Module.length (X.presheaf.stalk z)
      ((X.presheaf.stalk z) ⧸ Ideal.span {c})).toNat = n := by
    change (Ring.ord (X.presheaf.stalk z) c).toNat = n
    rw [← hn, ENat.toNat_natCast]
  rw [hlen]

/-- On an integral closed subscheme `Z` of a scheme `Y` locally of finite type over an
algebraically closed field `k`, the order of vanishing at a point `x` of codimension one with
closed image of the restriction of `t ∈ 𝒪_{Y,x}` is `dim_k 𝒪_{Y,x} / (I_{Z,x} + (t))`. -/
private theorem ord_stalkMap_subschemeι_eq_finrank {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (I : Y.IdealSheafData)
    [IsIntegral I.subscheme] [IsLocallyNoetherian I.subscheme] {x : I.subscheme}
    (hx : Order.coheight x = 1) (hcl : IsClosed ({I.subschemeι x} : Set Y))
    (t : Y.presheaf.stalk (I.subschemeι x)) (ht : (I.subschemeι.stalkMap x).hom t ≠ 0) :
    I.subscheme.ord (algebraMap _ I.subscheme.functionField ((I.subschemeι.stalkMap x).hom t)) x =
      ((letI := MMP.Mori.stalkAlgebra sY (I.subschemeι x)
        Module.finrank k (Y.presheaf.stalk (I.subschemeι x) ⧸
          (IdealSheafData.stalk I (I.subschemeι x) ⊔ Ideal.span {t})) : ℕ) : ℤ) := by
  let := MMP.Mori.stalkAlgebra sY (I.subschemeι x)
  rw [ord_algebraMap_eq_length hx ht, length_quotient_span_map _
    (Scheme.Hom.stalkMap_surjective I.subschemeι x) t,
    Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk,
    finrank_quotient_eq_length k (MMP.Mori.SurfaceAux.residue_surjective sY _ hcl)]

/-- A proper specialization lowers the coheight: if `ξ ⤳ η` with `ξ ≠ η` then
`coheight ξ + 1 ≤ coheight η`. -/
private theorem coheight_add_one_le_of_specializes {Y : Scheme.{u}} {ξ η : Y} (h : ξ ⤳ η)
    (hne : ξ ≠ η) : Order.coheight ξ + 1 ≤ Order.coheight η :=
  Order.coheight_add_one_le (lt_of_le_not_ge (α := Y) h fun h' => hne (h.antisymm h').eq)

/-- In a scheme of dimension at most one, a point of codimension one is closed. -/
private theorem isClosed_singleton_of_coheight_eq_one {X : Scheme.{u}}
    (hdim : topologicalKrullDim X ≤ 1) {x : X} (hx : Order.coheight x = 1) :
    IsClosed ({x} : Set X) := by
  refine closure_subset_iff_isClosed.mp fun w hw => ?_
  have hwx : w ≤ x := specializes_iff_mem_closure.mpr hw
  by_contra hne
  have h4 := coheight_add_one_le_of_specializes hwx (Ne.symm hne)
  have h5 := coheight_le_topologicalKrullDim w
  rw [hx] at h4
  have h6 : (1 : ℕ∞) + 1 ≤ 1 := h4.trans (WithBot.coe_le_coe.mp (h5.trans hdim))
  exact absurd h6 (by decide)

/-- At a closed point `x` of a scheme locally of finite type over an algebraically closed field,
the residue field map of a morphism over `k` is bijective. -/
private theorem bijective_residueFieldMap_of_isClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (ν : X ⟶ Z) [LocallyOfFiniteType (ν ≫ sZ)]
    {x : X} (hx : IsClosed ({x} : Set X)) : Function.Bijective (ν.residueFieldMap x).hom := by
  refine ⟨(ν.residueFieldMap x).hom.injective, fun w => ?_⟩
  obtain ⟨s, rfl⟩ := X.residue_surjective x w
  let := MMP.Mori.stalkAlgebra (ν ≫ sZ) x
  let := MMP.Mori.stalkAlgebra sZ (ν x)
  obtain ⟨c, hc⟩ := MMP.Mori.SurfaceAux.residue_surjective (ν ≫ sZ) x hx
    (Ideal.Quotient.mk _ s)
  refine ⟨Z.residue (ν x) (algebraMap k (Z.presheaf.stalk (ν x)) c), ?_⟩
  have h1 := congrArg (fun g : Z.presheaf.stalk (ν x) ⟶ X.residueField x =>
    g.hom (algebraMap k (Z.presheaf.stalk (ν x)) c)) (Scheme.residue_residueFieldMap ν x)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h1
  erw [h1, MMP.Threefold.Resolution.stalkMap_algebraMap]
  rw [← Ideal.Quotient.mk_algebraMap] at hc
  exact hc

/-- **The local projection formula for a birational morphism of curves.** Let `ν : X ⟶ Z` be a
proper dominant morphism of integral schemes, `Z` locally of finite type over an algebraically
closed field `k`, with `dim X ≤ 1` and `ν` surjective on the local ring at the generic point.
Then for every nonzero rational function `a` on `Z` and every point `z`,
`ord_z(a) = ∑_{x ↦ z} ord_x(ν^* a)`. This is Stacks 02RT, the norm being trivial. -/
private theorem ord_eq_finsum_ord_preimage {k : Type u} [Field k] [IsAlgClosed k]
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] (sZ : Z ⟶ Spec (.of k))
    [LocallyOfFiniteType sZ] (ν : X ⟶ Z) [IsProper ν] [IsDominant ν]
    (hgen : Function.Surjective (ν.stalkMap (genericPoint X)).hom)
    (hdim : topologicalKrullDim X ≤ 1) (z : Z) {a : Z.functionField} (ha : a ≠ 0) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (ν ≫ sZ)
    Z.ord a z = ∑ᶠ x ∈ ν.base ⁻¹' {z}, X.ord (dominantFunctionFieldMap ν a) x := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (ν ≫ sZ)
  set C := Stacks.Chow.fieldChowSituation k
  let : Algebra Z.functionField X.functionField := (dominantFunctionFieldMap ν).toAlgebra
  have halg : algebraMap Z.functionField X.functionField = dominantFunctionFieldMap ν :=
    RingHom.algebraMap_toAlgebra _
  -- the function field map is bijective
  have hsurj : Function.Surjective (dominantFunctionFieldMap ν) := by
    have hcast : dominantFunctionFieldMap ν =
        ((Z.presheaf.stalkCongr (.of_eq
          (AlgebraicGeometry.map_genericPoint_of_isDominant ν).symm)).hom ≫
            ν.stalkMap (genericPoint X)).hom := by
      dsimp [dominantFunctionFieldMap]
      rw [AlgebraicGeometry.stalkMap_cast_target]
      rfl
    rw [hcast, CommRingCat.hom_comp, RingHom.coe_comp]
    exact hgen.comp (Z.presheaf.stalkCongr (.of_eq
      (AlgebraicGeometry.map_genericPoint_of_isDominant ν).symm)
      ).commRingCatIsoToRingEquiv.surjective
  have hbij : Function.Bijective (algebraMap Z.functionField X.functionField) := by
    rw [halg]; exact ⟨(dominantFunctionFieldMap ν).injective, hsurj⟩
  have hrank : Module.finrank Z.functionField X.functionField = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId Z.functionField X.functionField)
      hbij).toLinearEquiv.finrank_eq, Module.finrank_self]
  have hnorm : Algebra.norm Z.functionField (dominantFunctionFieldMap ν a) = a := by
    rw [← halg, Algebra.norm_algebraMap, hrank, pow_one]
  -- residue fields
  have hfinres : ∀ x : X, Function.Bijective (ν.residueFieldMap x).hom →
      letI := (ν.residueFieldMap x).hom.toAlgebra
      Module.Finite (Z.residueField (ν.base x)) (X.residueField x) := by
    intro x hx
    let := (ν.residueFieldMap x).hom.toAlgebra
    exact Module.Finite.of_surjective (Algebra.linearMap _ _) hx.2
  have hresgen : Function.Bijective (ν.residueFieldMap (genericPoint X)).hom := by
    refine ⟨(ν.residueFieldMap _).hom.injective, fun w => ?_⟩
    obtain ⟨s, rfl⟩ := X.residue_surjective _ w
    obtain ⟨t, rfl⟩ := hgen s
    refine ⟨Z.residue _ t, ?_⟩
    exact congrArg (fun g : Z.presheaf.stalk (ν (genericPoint X)) ⟶ X.residueField _ => g.hom t)
      (Scheme.residue_residueFieldMap ν (genericPoint X))
  -- dimensions
  have hgenpt : ν.base (genericPoint X) = genericPoint Z :=
    AlgebraicGeometry.map_genericPoint_of_isDominant ν
  set n := Stacks.Chow.relativeDimension C.dimensionFunction sZ (genericPoint Z)
  have hnZ : Stacks.Chow.schemeDeltaDimension C sZ = (n : EInt) :=
    Stacks.Chow.schemeDeltaDimension_eq_genericPoint C sZ
  have hnX : Stacks.Chow.schemeDeltaDimension C (ν ≫ sZ) = (n : EInt) := by
    rw [Stacks.Chow.schemeDeltaDimension_eq_genericPoint C (ν ≫ sZ),
      Stacks.Chow.relativeDimension_eq_of_finite_residueField C.dimensionFunction sZ ν _
        (hfinres _ hresgen), hgenpt]
  have hf : dominantFunctionFieldMap ν a ≠ 0 := (map_ne_zero _).mpr ha
  have key := congrArg (fun c => (c : Stacks.Chow.CycleGroup C sZ (n - 1)).1 z)
    (Stacks.Chow.properPushforward_principalDivisorCycle C (ν ≫ sZ) sZ hnX hnZ ν rfl
      (dominantFunctionFieldMap ν a) hf)
  rw [Stacks.Chow.properPushforward_apply, Stacks.Chow.principalDivisorCycle_apply,
    hnorm] at key
  rw [← key]
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  rw [Stacks.Chow.principalDivisorCycle_apply]
  by_cases hco : Order.coheight x = 1
  · have hcl := isClosed_singleton_of_coheight_eq_one hdim hco
    have hres := bijective_residueFieldMap_of_isClosed sZ ν hcl
    rw [ite_eq_left (Stacks.Chow.relativeDimension_eq_of_finite_residueField C.dimensionFunction
      sZ ν x (hfinres x hres))]
    have hdeg : ν.residueDegree x = 1 := by
      unfold Scheme.Hom.residueDegree
      let := (ν.residueFieldMap x).hom.toAlgebra
      rw [← (AlgEquiv.ofBijective (Algebra.ofId (Z.residueField (ν.base x)) (X.residueField x))
        hres).toLinearEquiv.finrank_eq, Module.finrank_self]
    rw [hdeg, Nat.cast_one, mul_one]
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hco, zero_mul]

section Points

/-- A point other than the generic point of an integral scheme of dimension at most one has
codimension one. -/
private theorem coheight_eq_one_of_ne_genericPoint {X : Scheme.{u}} [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) {x : X} (hx : x ≠ genericPoint X) :
    Order.coheight x = 1 := by
  have hle : x ≤ genericPoint X :=
    specializes_iff_mem_closure.mpr (by rw [genericPoint_closure]; trivial)
  have h1 : 1 ≤ Order.coheight x :=
    le_trans (by simp) (coheight_add_one_le_of_specializes hle hx.symm)
  have h2 : (Order.coheight x : WithBot ℕ∞) ≤ 1 := (coheight_le_topologicalKrullDim x).trans hdim
  have h2' : Order.coheight x ≤ 1 := by exact_mod_cast h2
  exact le_antisymm h2' h1

/-- A point common to two distinct prime divisors of a surface is a closed point. -/
private theorem isClosed_singleton_of_mem_inter' {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X]
    (hdim : topologicalKrullDim X = 2) {C D : Mori.PrimeDivisor X} (hCD : C ≠ D) {y : X}
    (hy : y ∈ C.support ∩ D.support) : IsClosed ({y} : Set X) := by
  have hne : y ≠ C.genericPoint := by
    rintro rfl
    exact hCD (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support D C hy.2).symm
  have hle : y ≤ C.genericPoint := by
    have h := hy.1
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
    exact specializes_iff_mem_closure.mpr h
  have h2 := coheight_add_one_le_of_specializes hle hne.symm
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint] at h2
  refine closure_subset_iff_isClosed.mp fun w hw => ?_
  have hwy : w ≤ y := specializes_iff_mem_closure.mpr hw
  by_contra hne
  have h4 := coheight_add_one_le_of_specializes hwy (Ne.symm hne)
  have h5 := coheight_le_topologicalKrullDim w
  rw [hdim] at h5
  have h6 : (1 : ℕ∞) + 1 + 1 ≤ 2 :=
    (add_le_add h2 (le_refl (1 : ℕ∞))).trans (h4.trans (WithBot.coe_le_coe.mp h5))
  exact absurd h6 (by decide)

/-- On a smooth scheme, a generator of the ideal of a prime divisor `P` at a point `q` of another
prime divisor `Q ≠ P` does not lie in the ideal of `Q`. -/
private theorem notMem_stalk_of_ne {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (hsm : MMP.Mori.IsSmoothScheme sX)
    {P Q : Mori.PrimeDivisor X} (hPQ : P ≠ Q) {q : X} (hq : q ∈ Q.support)
    {c : X.presheaf.stalk q} (hc : IdealSheafData.stalk P.idealSheaf q = Ideal.span {c}) :
    c ∉ IdealSheafData.stalk Q.idealSheaf q := by
  intro hcQ
  by_cases hP : q ∈ P.support
  · obtain ⟨p, hp, hpP⟩ := MMP.Resolution.Aux.exists_prime_stalk_idealSheaf sX hsm P hP
    obtain ⟨r, hr, hrQ⟩ := MMP.Resolution.Aux.exists_prime_stalk_idealSheaf sX hsm Q hq
    have hle : IdealSheafData.stalk P.idealSheaf q ≤ IdealSheafData.stalk Q.idealSheaf q := by
      rwa [hc, Ideal.span_le, Set.singleton_subset_iff]
    rw [hpP, hrQ, Ideal.span_singleton_le_span_singleton] at hle
    have hass := hr.associated_of_dvd hp hle
    have heq : IdealSheafData.stalk P.idealSheaf q = IdealSheafData.stalk Q.idealSheaf q := by
      rw [hpP, hrQ]; exact (Ideal.span_singleton_eq_span_singleton.2 hass).symm
    exact hPQ (MMP.Resolution.Aux.eq_of_stalk_idealSheaf_eq sX hsm P Q hP hq heq)
  · have htop := (IdealSheafData.stalk_eq_top_iff_notMem_support P.idealSheaf q).2 hP
    rw [hc, Ideal.span_singleton_eq_top] at htop
    have hQtop : IdealSheafData.stalk Q.idealSheaf q = ⊤ := Ideal.eq_top_of_isUnit_mem _ hcQ htop
    exact ((IdealSheafData.stalk_eq_top_iff_notMem_support Q.idealSheaf q).1 hQtop) hq

/-- Germs of the pull-backs of a section along two equal morphisms agree. -/
private theorem germ_app_congr {A B : Scheme.{u}} {φ ψ : A ⟶ B} (e : φ = ψ) (W : B.Opens)
    (s : Γ(B, W)) (x : A) (hx : x ∈ φ ⁻¹ᵁ W) :
    (A.presheaf.germ (φ ⁻¹ᵁ W) x hx).hom (φ.app W s) =
      (A.presheaf.germ (ψ ⁻¹ᵁ W) x (e ▸ hx)).hom (ψ.app W s) := by
  subst e; rfl

/-- Points of a commutative square of schemes. -/
private theorem apply_eq_of_comp_eq {A B B' T : Scheme.{u}} {f : A ⟶ B} {g : B ⟶ T}
    {f' : A ⟶ B'} {g' : B' ⟶ T} (e : f ≫ g = f' ≫ g') (x : A) : g (f x) = g' (f' x) := by
  simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] using
    congrArg (fun φ => φ.base x) e

end Points

section LocalEquation

/-- The local ideal of a prime divisor is its ideal stalk. -/
private theorem localIdeal_single_one {Z : Scheme.{u}} (P : Mori.PrimeDivisor Z) (z : Z) :
    localIdeal z (Finsupp.single P 1) = IdealSheafData.stalk P.idealSheaf z := by
  rw [localIdeal, Finsupp.support_single _ one_ne_zero, Finset.prod_singleton,
    Finsupp.single_eq_same, Int.toNat_one, pow_one]

/-- Near any point `q`, a prime divisor `P` on a smooth scheme has a local equation `φ` which is a
regular function `f` on an open `W ∋ q` and whose germ at `q` generates the ideal of `P`. -/
private theorem exists_localEquation_single {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian Y] [IsNormal Y] (hsm : IsSmoothScheme sY)
    (P : Mori.PrimeDivisor Y)
    (q : Y) :
    ∃ (W : Y.Opens) (hq : q ∈ W) (f : Γ(Y, W)) (φ : (RationalFunctions Y)ˣ),
      Divisor.IsLocalEquation (Finsupp.single P 1 : Divisor Y) W φ ∧
      (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ W),
        (φ : RationalFunctions Y) Z = (Y.presheaf.germ W _ hZ).hom f) ∧
      IdealSheafData.stalk P.idealSheaf q = Ideal.span {(Y.presheaf.germ W q hq).hom f} := by
  classical
  have := P.integral
  by_cases hx : q ∈ P.support
  · obtain ⟨W, hW, hxW, f, hf, hspan⟩ :=
      Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
        P.idealSheaf
        (MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P) q
    have hgerm : ∀ y (hy : y ∈ W), IdealSheafData.stalk P.idealSheaf y =
        Ideal.span {(Y.presheaf.germ W y hy).hom f} := by
      intro y hy
      rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ P.idealSheaf y ⟨W, hW⟩ hy, hspan,
        Ideal.map_span, Set.image_singleton]
    have hnzd : ∀ y (hy : y ∈ W), (Y.presheaf.germ W y hy).hom f ∈
        nonZeroDivisors (Y.presheaf.stalk y) := fun y hy =>
      Stacks.Divisors.germ_mem_nonZeroDivisors hW hf y hy
    have hfield : ∀ Z : irreducibleComponents Y,
        IsField (Y.presheaf.stalk (componentGenericPoint Y Z)) :=
      fun Z => RationalFunctions.isField_stalk Y Z
    let u : ∀ Z : irreducibleComponents Y, (Y.presheaf.stalk (componentGenericPoint Y Z))ˣ :=
      fun Z => if h : componentGenericPoint Y Z ∈ W then
        (by
          letI := (hfield Z).toField
          exact (isUnit_iff_ne_zero.2 (nonZeroDivisors.ne_zero (hnzd _ h))).unit)
        else 1
    let φ : (RationalFunctions Y)ˣ := (RationalFunctions.unitsEquiv Y).symm u
    have hφ : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ W),
        (φ : RationalFunctions Y) Z = (Y.presheaf.germ W _ hZ).hom f := by
      intro Z hZW
      change ((u Z : (Y.presheaf.stalk (componentGenericPoint Y Z))ˣ) :
        Y.presheaf.stalk (componentGenericPoint Y Z)) = _
      simp only [u]
      rw [dite_eq_left hZW]
      rfl
    refine ⟨W, hxW, f, φ, ?_, hφ, hgerm q hxW⟩
    rintro E ⟨y, hyE, hyW⟩
    have hηW : E.genericPoint ∈ W := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
      exact (specializes_iff_mem_closure.mpr hyE).mem_open W.isOpen hyW
    have hZW : componentGenericPoint Y E.component ∈ W :=
      E.specializes_genericPoint.mem_open W.isOpen hηW
    have key : E.toComponent.hom ((Y.presheaf.germ W _ hηW).hom f) =
        (φ : RationalFunctions Y) E.component := by
      rw [hφ _ hZW]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    by_cases hEP : P = E
    · subst hEP
      rw [DivisorWithCoeffs.coeff_single_self]
      have hmem : P.genericPoint ∈ P.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      have hg0 := nonZeroDivisors.ne_zero (hnzd _ hηW)
      have hprime : Prime ((Y.presheaf.germ W _ hηW).hom f) := by
        rw [← Ideal.span_singleton_prime hg0, ← hgerm _ hηW]
        have hxr : P.genericPoint ∈ Set.range P.idealSheaf.subschemeι := by
          rwa [Scheme.IdealSheafData.range_subschemeι]
        obtain ⟨y', hy'⟩ := hxr
        rw [← hy']
        rw [← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
        exact RingHom.ker_isPrime _
      exact (P.ord_eq_one_of_irreducible hprime.irreducible key).symm
    · rw [DivisorWithCoeffs.coeff_single_of_ne hEP]
      have hnm : E.genericPoint ∉ P.support := fun h =>
        hEP (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support P E h)
      have htop := (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support
        P.idealSheaf _).2 hnm
      rw [hgerm _ hηW, Ideal.span_singleton_eq_top] at htop
      exact (E.ord_eq_zero_of_isUnit htop key).symm
  · refine ⟨⟨(P.support)ᶜ, P.idealSheaf.support.isClosed.isOpen_compl⟩, hx, 1, 1, ?_, ?_, ?_⟩
    · rintro E ⟨y, hyE, hyP⟩
      have hne : P ≠ E := by
        rintro rfl
        exact hyP hyE
      rw [DivisorWithCoeffs.coeff_single_of_ne hne]
      simp
    · intro Z hZ
      simp
    · rw [map_one, Ideal.span_singleton_one]
      exact (IdealSheafData.stalk_eq_top_iff_notMem_support P.idealSheaf q).2 hx

/-- **Local equations of a pulled-back divisor.** Let `π : Y' ⟶ Y` be a morphism of locally
Noetherian normal schemes, `B` a divisor on `Y` with pull-back `B' = π^* B`, `f` a regular
function on `W ⊆ Y` which is a local equation of `B` there, and `g` a regular function on
`V ⊆ Y'` which is a local equation of `B'` there. Then at every `q ∈ V ∩ π⁻¹(W)` the germ of
`π^* f` is a unit multiple of the germ of `g`. -/
private theorem exists_unit_germ_app_eq_mul {Y Y' : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] [IsLocallyNoetherian Y'] [IsNormal Y'] (π : Y' ⟶ Y) {B : Divisor Y}
    (hB : ∀ Z : irreducibleComponents Y', π (componentGenericPoint Y' Z) ∉ B.supp)
    {B' : Divisor Y'} (hpb : B.IsPullback π hB B') {W : Y.Opens} {f : Γ(Y, W)}
    {φ : (RationalFunctions Y)ˣ} (hφ : B.IsLocalEquation W φ)
    (hφf : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ W),
      (φ : RationalFunctions Y) Z = (Y.presheaf.germ W _ hZ).hom f)
    {V : Y'.Opens} {g : Γ(Y', V)} {ψ : (RationalFunctions Y')ˣ} (hψ : B'.IsLocalEquation V ψ)
    (hψg : ∀ (Z : irreducibleComponents Y') (hZ : componentGenericPoint Y' Z ∈ V),
      (ψ : RationalFunctions Y') Z = (Y'.presheaf.germ V _ hZ).hom g)
    {q : Y'} (hqW : π q ∈ W) (hqV : q ∈ V) :
    ∃ w : (Y'.presheaf.stalk q)ˣ, (Y'.presheaf.germ (π ⁻¹ᵁ W) q hqW).hom (π.app W f) =
      w * (Y'.presheaf.germ V q hqV).hom g := by
  classical
  set Z0 := pointComponent q with hZ0
  have hq0 : q ∈ Z0.1 := mem_pointComponent q
  have hsp0 : componentGenericPoint Y' Z0 ⤳ q :=
    (isGenericPoint_componentGenericPoint Y' Z0).specializes hq0
  have h0W : π (componentGenericPoint Y' Z0) ∈ W :=
    (π.base.hom.map_specializes hsp0).mem_open W.isOpen hqW
  have h0V : componentGenericPoint Y' Z0 ∈ V := hsp0.mem_open V.isOpen hqV
  let Ψ : (RationalFunctions Y')ˣ := (RationalFunctions.unitsEquiv Y').symm fun Z =>
    if h : π (componentGenericPoint Y' Z) ∈ W then pullbackComponent π hB hφ Z h else 1
  have hΨ : ∀ Z (h : π (componentGenericPoint Y' Z) ∈ W),
      Units.map (RationalFunctions.component Y' Z).toMonoidHom Ψ =
        pullbackComponent π hB hφ Z h := by
    intro Z h
    ext1
    change ((if h : π (componentGenericPoint Y' Z) ∈ W then pullbackComponent π hB hφ Z h
      else 1 : (Y'.presheaf.stalk (componentGenericPoint Y' Z))ˣ) :
        Y'.presheaf.stalk (componentGenericPoint Y' Z)) = _
    rw [dite_eq_left h]
  have hord : ∀ E : Mori.PrimeDivisor Y', q ∈ E.support → E.ord (Ψ * ψ⁻¹) = 0 := by
    intro E hE
    have hEW : (E.support ∩ π ⁻¹ᵁ W).Nonempty := ⟨q, hE, hqW⟩
    have hEV : (E.support ∩ V).Nonempty := ⟨q, hE, hqV⟩
    rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_inv, ← hψ E hEV, PrimeDivisor.ord_eq_ordUnit,
      hΨ _ (E.map_componentGenericPoint_mem π hEW), ← hpb W φ hφ E hEW, add_neg_cancel]
  obtain ⟨w, hw⟩ := exists_unit_stalk_of_forall_ord_eq_zero hq0 (Ψ * ψ⁻¹) hord
  refine ⟨w, stalkToRationalFunctions_injective hq0 ?_⟩
  -- the image of the right side
  have hr : (stalkToRationalFunctions Y' hq0).hom (↑w * (Y'.presheaf.germ V q hqV).hom g) =
      (Ψ : RationalFunctions Y') Z0 := by
    rw [map_mul, hw]
    have hg : (stalkToRationalFunctions Y' hq0).hom ((Y'.presheaf.germ V q hqV).hom g) =
        (ψ : RationalFunctions Y') Z0 := by
      rw [hψg Z0 h0V]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [hg, Units.val_mul, Pi.mul_apply, mul_assoc, ← Pi.mul_apply, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Pi.one_apply, mul_one]
  rw [hr]
  -- the image of the left side
  have hl : (stalkToRationalFunctions Y' hq0).hom
      ((Y'.presheaf.germ (π ⁻¹ᵁ W) q hqW).hom (π.app W f)) =
      (Y'.presheaf.germ (π ⁻¹ᵁ W) _ h0W).hom (π.app W f) :=
    TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  rw [hl]
  set W1 := pointComponent (π (componentGenericPoint Y' Z0))
  have hW1 : π (componentGenericPoint Y' Z0) ∈ W1.1 := mem_pointComponent _
  have hsp1 : componentGenericPoint Y W1 ⤳ π (componentGenericPoint Y' Z0) :=
    (isGenericPoint_componentGenericPoint Y W1).specializes hW1
  have h1W : componentGenericPoint Y W1 ∈ W := hsp1.mem_open W.isOpen h0W
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk h0W (hB Z0) hW1
  have hafa : (a : Y.presheaf.stalk (π (componentGenericPoint Y' Z0))) =
      (Y.presheaf.germ W _ h0W).hom f := by
    refine stalkToRationalFunctions_injective hW1 ?_
    rw [ha, hφf W1 h1W]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm
  have hcomp : (Ψ : RationalFunctions Y') Z0 =
      ((pullbackComponent π hB hφ Z0 h0W : (Y'.presheaf.stalk (componentGenericPoint Y' Z0))ˣ) :
        Y'.presheaf.stalk (componentGenericPoint Y' Z0)) :=
    congrArg Units.val (hΨ Z0 h0W)
  rw [hcomp, pullbackComponent_eq hB hφ h0W hW1 a ha]
  change _ = (π.stalkMap (componentGenericPoint Y' Z0)).hom (a : Y.presheaf.stalk _)
  rw [hafa, Scheme.Hom.germ_stalkMap_apply]

end LocalEquation

section Blowup

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

set_option hygiene false in
/-- The blow-up `π : Y' ⟶ Y` of the reduced closed point `y`. -/
local notation "πy" => blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds _))

set_option hygiene false in
/-- The blow-up `Y'` of the reduced closed point `y`. -/
local notation "Y'y" => blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds _))

/-- The generic point of a curve on a surface is not a closed point. -/
private theorem genericPoint_ne_of_isClosed (hY : Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) {y : Y} (hy : IsClosed ({y} : Set Y))
    (P : Mori.PrimeDivisor Y) : P.genericPoint ≠ y := by
  intro h
  have h1 := coheight_eq_two_of_isClosed hY hYd hy
  rw [← h, Mori.PrimeDivisor.coheight_genericPoint] at h1
  exact absurd h1 (by decide)

/-- The exceptional curve of the blow-up of a point is not the strict transform of a curve. -/
private theorem ne_of_inverseTransformPrimeDivisor_eq_some (hY : Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) {y : Y} (hy : IsClosed ({y} : Set Y))
    {F : Mori.PrimeDivisor Y'y}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    {P : Mori.PrimeDivisor Y} {P' : Mori.PrimeDivisor Y'y}
    (hP' : inverseTransformPrimeDivisor πy P = some P') : F ≠ P' := by
  rintro rfl
  have h1 := (mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hy hF F.genericPoint).mp (by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  rw [(map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP').1] at h1
  exact genericPoint_ne_of_isClosed hY hYd hy P h1

/-- **The strict transform meets the exceptional curve with multiplicity `mult_y D`.** With
`π^* D = D' + (mult_y D) F`, `(π^* D · F) = 0` and `F² = -1`, `(D' · F) = mult_y D`. -/
private theorem isIntersectionNumber_strictTransform_exceptional (hY : Mori.IsVariety k sY)
    (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) {y : Y}
    (hy : IsClosed ({y} : Set Y)) {F : Mori.PrimeDivisor Y'y}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    {D : Mori.PrimeDivisor Y} {D' : Mori.PrimeDivisor Y'y}
    (hD' : inverseTransformPrimeDivisor πy D = some D') :
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).2
    haveI := (isVariety_blowUp_singleton hY hYd hy).toQuasiCompact
    IsIntersectionNumber (πy ≫ sY) (Finsupp.single D' (1 : ℚ)) F.idealSheaf
      ((D.multiplicityAt y).toNat : ℚ) := by
  have hYsm := isSmoothScheme_blowUp_singleton hY hYs hYd hy
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYsm).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYsm).2
  have hvar := isVariety_blowUp_singleton hY hYd hy
  have := hvar.toQuasiCompact
  have : IsIntegral Y'y := hvar.toIsIntegral
  have : IsSeparated sY := hY.toIsSeparated
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : QuasiCompact sY := hY.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have := compactSpace_blowUp_singleton hY hYd hy
  -- the exceptional curve is a proper curve
  obtain ⟨-, -, -, -, F₀, hF₀, -, hprop, hself⟩ :=
    blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection hY hYs hYd hy
  have hFF₀ : F₀ = F := Mori.PrimeDivisor.ext_idealSheaf (by rw [hF₀, hF])
  subst hFF₀
  set F' : ProperCurve (πy ≫ sY) := ⟨F₀.genericPoint, hprop⟩
  have hFmem := mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hy hF
  -- `(F · F) = -1`
  have hFF : IsIntersectionNumber (πy ≫ sY) (Finsupp.single F₀ (1 : ℚ)) F₀.idealSheaf (-1) := by
    have h := isIntersectionNumber_of_properCurve (Divisor.toQDivisor (Finsupp.single F₀ 1))
      (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hYsm F₀) F' F₀ rfl
    rw [hself F' rfl, toQDivisor_single, Int.cast_one] at h
    exact h
  -- `(π^* D · F) = 0`
  have hD := MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hYs D
  have hB := blowUpToBase_componentGenericPoint_notMem_supp hY hYd hy (Finsupp.single D (1 : ℤ))
  have hcon : F'.IsContractedBy πy := by
    intro q hq
    change q ∈ closure {F₀.genericPoint} at hq
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hq
    rw [(hFmem q).mp hq, (hFmem _).mp (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)]
  have h0 := Divisor.degreeOn_pullback_eq_zero_of_isContractedBy (sY := sY)
    (sX := πy ≫ sY) πy rfl hD hB F' hcon
  have hD'c := hD.isCartier_pullback πy hB
  have : IsProper (F'.ι ≫ πy ≫ sY) := ProperCurve.isProper_ι_comp F'
  have hpb := isIntersectionNumber_of_properCurve (Divisor.toQDivisor (Divisor.pullback
    (f := πy) _ hD hB)) (QDivisor.isQCartier_toQDivisor hD'c) F' F₀ rfl
  rw [QDivisor.intersectionNumber_toQDivisor k _ _ _ _ hD'c, h0, Int.cast_zero] at hpb
  have hpbeq := pullback_single_blowUp_singleton hY hYs hYd hy hF D
  rw [hpbeq, map_add, inverseTransformDivisor_single, hD'] at hpb
  change IsIntersectionNumber _ (Divisor.toQDivisor (Finsupp.single D' 1) +
    Divisor.toQDivisor (Finsupp.single F₀ _)) _ 0 at hpb
  rw [toQDivisor_single, toQDivisor_single, Int.cast_one, Int.cast_natCast] at hpb
  -- `(D' · F)` exists
  obtain ⟨x, hx⟩ : ∃ x, IsIntersectionNumber (πy ≫ sY) (Finsupp.single D' (1 : ℚ))
      F₀.idealSheaf x := by
    obtain ⟨hp, hdim, -, -⟩ := hFF
    exact ⟨_, hp, hdim, MMP.Fourfold.isQCartier_of_isSmoothScheme hYsm _, rfl⟩
  have hsm := hFF.smul ((D.multiplicityAt y).toNat : ℚ)
    (MMP.Fourfold.isQCartier_of_isSmoothScheme hYsm _)
  rw [Finsupp.smul_single, smul_eq_mul, mul_one] at hsm
  have hsum := MMP.Flips.isIntersectionNumber_add hx hsm
  have := hsum.unique hpb
  have hxeq : x = ((D.multiplicityAt y).toNat : ℚ) := by linarith
  rwa [hxeq] at hx

/-- The generic point of the integral subscheme of a prime divisor is its generic point. -/
private theorem subschemeι_genericPoint {X : Scheme.{u}} (P : Mori.PrimeDivisor X) :
    haveI := P.integral
    P.idealSheaf.subschemeι (genericPoint P.idealSheaf.subscheme) = P.genericPoint := by
  have := P.integral
  refine IsGenericPoint.eq (MMP.Resolution.closure_subschemeι_genericPoint P.idealSheaf) ?_
  change closure {P.genericPoint} = (P.support : Set X)
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]

/-- **The strict transform of a curve maps to the curve.** If `D' = π⁻¹_* D`, the blow-up `π`
restricts to a proper dominant morphism `ν : D' ⟶ D` of the reduced curves, which is an
isomorphism on the local rings at the generic points (it is surjective there). -/
private theorem exists_curveMap_of_inverseTransformPrimeDivisor {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] (g : X ⟶ Y) [IsProper g] {D : Mori.PrimeDivisor Y}
    {D' : Mori.PrimeDivisor X}
    (hD' : inverseTransformPrimeDivisor g D = some D') :
    haveI := D.integral
    haveI := D'.integral
    ∃ ν : D'.idealSheaf.subscheme ⟶ D.idealSheaf.subscheme,
      ν ≫ D.idealSheaf.subschemeι = D'.idealSheaf.subschemeι ≫ g ∧ IsProper ν ∧
      IsDominant ν ∧ Function.Surjective (ν.stalkMap (genericPoint _)).hom := by
  have := D.integral
  have := D'.integral
  obtain ⟨hη, hV⟩ := map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD'
  have hle : D.idealSheaf ≤ D'.idealSheaf.map g := by
    rw [Scheme.IdealSheafData.le_map_iff_comap_le,
      ← vanishingIdeal_closure_genericPoint_eq_idealSheaf D',
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro z hz
    change z ∈ closure {D'.genericPoint} at hz
    change z ∈ ((D.idealSheaf.comap g).support : Set X)
    rw [Scheme.IdealSheafData.support_comap]
    refine closure_minimal ?_ (D.idealSheaf.support.isClosed.preimage g.continuous) hz
    rw [Set.singleton_subset_iff, Set.mem_preimage, hη]
    change D.genericPoint ∈ D.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  set ν := Scheme.IdealSheafData.subschemeMap D'.idealSheaf D.idealSheaf g hle
  have hfac : ν ≫ D.idealSheaf.subschemeι = D'.idealSheaf.subschemeι ≫ g :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have : IsProper (ν ≫ D.idealSheaf.subschemeι) := by rw [hfac]; infer_instance
  have : IsProper ν := IsProper.of_comp ν D.idealSheaf.subschemeι
  have hgen : ν (genericPoint _) = genericPoint _ := by
    apply D.idealSheaf.subschemeι.isClosedEmbedding.injective
    rw [apply_eq_of_comp_eq hfac, subschemeι_genericPoint D', hη, subschemeι_genericPoint D]
  have : IsDominant ν := ((tfae_isDominant_of_isIntegral ν).out 1 2).mpr hgen
  refine ⟨ν, hfac, inferInstance, inferInstance, ?_⟩
  have hcongr : ∀ (φ ψ : D'.idealSheaf.subscheme ⟶ Y) (_ : φ = ψ) (x : D'.idealSheaf.subscheme),
      Function.Surjective (ψ.stalkMap x).hom → Function.Surjective (φ.stalkMap x).hom := by
    rintro φ ψ rfl x h
    exact h
  have hiso : IsIso (g.stalkMap (D'.idealSheaf.subschemeι (genericPoint _))) := by
    apply isIso_stalkMap_of_mem_biregularLocus
    rwa [subschemeι_genericPoint D']
  have h2 : Function.Surjective
      ((D'.idealSheaf.subschemeι ≫ g).stalkMap (genericPoint D'.idealSheaf.subscheme)).hom := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (show Function.Surjective ((D'.idealSheaf.subschemeι.stalkMap _).hom.comp
      (g.stalkMap (D'.idealSheaf.subschemeι (genericPoint _))).hom) from
      (Scheme.Hom.stalkMap_surjective _ _).comp
        (asIso (g.stalkMap _)).commRingCatIsoToRingEquiv.surjective)
  have hsurj : Function.Surjective ((ν.stalkMap (genericPoint _)).hom.comp
      (D.idealSheaf.subschemeι.stalkMap (ν (genericPoint D'.idealSheaf.subscheme))).hom) := by
    have := hcongr _ _ hfac (genericPoint _) h2
    rwa [Scheme.Hom.stalkMap_comp] at this
  rw [RingHom.coe_comp] at hsurj
  exact Function.Surjective.of_comp hsurj

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Noether's formula.** Let `Y` be a smooth surface over an algebraically closed field `k`,
`y ∈ Y` a closed point, `π : Y' ⟶ Y` the blow-up of `y` with exceptional curve `F`, and `C ≠ D`
curves through `y` with strict transforms `C'`, `D'`. Then
`(C · D)_y = mult_y C · mult_y D + ∑_{q ∈ F ∩ C' ∩ D'} (C' · D')_q`. -/
@[mmp "thm_mmp_threefold_surface_noether_formula"]
public theorem localIntersectionNumber_eq_multiplicityAt_mul_add_finsum
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    (hY : Mori.IsVariety k sY) (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    {y : Y} (hy : IsClosed ({y} : Set Y))
    {F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    {C D : Mori.PrimeDivisor Y} (hCD : C ≠ D) (hyC : y ∈ C.support) (hyD : y ∈ D.support)
    {C' D' : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hC' : inverseTransformPrimeDivisor
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) C = some C')
    (hD' : inverseTransformPrimeDivisor
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) D = some D') :
    (localIntersectionNumber sY y (Finsupp.single C 1) (Finsupp.single D 1) : ℕ∞) =
      C.multiplicityAt y * D.multiplicityAt y +
        ((∑ᶠ q ∈ F.support ∩ C'.support ∩ D'.support,
          localIntersectionNumber
            (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY) q
            (Finsupp.single C' 1) (Finsupp.single D' 1) : ℕ) : ℕ∞) := by
  classical
  -- the surface `Y`
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsIntegral Y := hY.toIsIntegral
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
  -- the blow-up `Y'`
  have hY's := isSmoothScheme_blowUp_singleton hY hYs hYd hy
  have hY'v := isVariety_blowUp_singleton hY hYd hy
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hY's).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hY's).2
  have : IsIntegral Y'y := hY'v.toIsIntegral
  have : LocallyOfFiniteType (πy ≫ sY) := hY'v.toLocallyOfFiniteType
  have : QuasiCompact (πy ≫ sY) := hY'v.toQuasiCompact
  obtain ⟨-, _, -⟩ :=
    blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection hY hYs hYd hy
  have hY'd : topologicalKrullDim Y'y = 2 := by
    have := topologicalKrullDim_blowUp sY _ (isSmoothBlowup_vanishingIdeal_singleton sY hYs hy)
      (isIrreducible_support_vanishingIdeal_singleton hy)
      (one_le_codimension_vanishingIdeal_singleton hYd hy) (d := 2) (by rw [hYd]; rfl)
    rw [this]; rfl
  have hFmem := mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hy hF
  -- multiplicities
  set m := (C.multiplicityAt y).toNat
  set n := (D.multiplicityAt y).toNat
  have hmC : C.multiplicityAt y = m := (ENat.natCast_toNat (multiplicityAt_ne_top C
    (isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hYs C) y)).symm
  have hnD : D.multiplicityAt y = n := (ENat.natCast_toNat (multiplicityAt_ne_top D
    (isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hYs D) y)).symm
  -- generic points
  obtain ⟨hηC, -⟩ := map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hC'
  obtain ⟨hηD, -⟩ := map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD'
  have hyne := genericPoint_ne_of_isClosed hY hYd hy
  have hFD' := ne_of_inverseTransformPrimeDivisor_eq_some hY hYd hy hF hD'
  have hC'D' : C' ≠ D' := by
    rintro rfl
    rw [hηC] at hηD
    exact hCD (AlgebraicGeometry.PrimeDivisor.genericPoint_injective hηD)
  -- `(D' · F) = mult_y D` and the exceptional sum
  have hexc := isIntersectionNumber_strictTransform_exceptional hY hYs hYd hy hF hD'
  obtain ⟨hFprop, -, -, -⟩ := id hexc
  obtain ⟨hfinFD, hFD'num, -⟩ :=
    isIntersectionNumber_finsum_localIntersectionNumber_of_ne (πy ≫ sY) hY'v hY's hY'd hFD'
      hFprop
  have hsumF : (∑ᶠ q ∈ F.support ∩ D'.support,
      (localIntersectionNumber (πy ≫ sY) q (Finsupp.single F 1) (Finsupp.single D' 1) : ℚ)) =
      (n : ℚ) := hFD'num.unique hexc
  -- the curves `D` and `D'`, and `ν : D' ⟶ D`
  have := D.integral
  have := D'.integral
  obtain ⟨ν, hfac, _, _, hνgen⟩ := exists_curveMap_of_inverseTransformPrimeDivisor πy hD'
  have : IsLocallyNoetherian D.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (D.idealSheaf.subschemeι ≫ sY)
  have : IsLocallyNoetherian D'.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (D'.idealSheaf.subschemeι ≫ πy ≫ sY)
  have hdimD : topologicalKrullDim D.idealSheaf.subscheme ≤ 1 :=
    Stacks.ResolutionOfSurfaces.topologicalKrullDim_subscheme_le_one hYd D.idealSheaf
      (isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hYs D)
  have hdimD' : topologicalKrullDim D'.idealSheaf.subscheme ≤ 1 :=
    Stacks.ResolutionOfSurfaces.topologicalKrullDim_subscheme_le_one hY'd D'.idealSheaf
      (isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hY's D')
  -- the point `y` on `D`
  obtain ⟨y0, hy0⟩ : y ∈ Set.range D.idealSheaf.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  have hy0ne : y0 ≠ genericPoint D.idealSheaf.subscheme := by
    intro h
    apply hyne D
    rw [← hy0, h, subschemeι_genericPoint D]
  have hy0co : Order.coheight y0 = 1 := coheight_eq_one_of_ne_genericPoint hdimD hy0ne
  have hcl0 : IsClosed ({D.idealSheaf.subschemeι y0} : Set Y) := by rwa [hy0]
  -- a local equation `f` of `C` at `y`
  obtain ⟨W, hyW, f, φ, hφ, hφf, hfspan⟩ :=
    exists_localEquation_single hYs C (D.idealSheaf.subschemeι y0)
  have hyC0 : D.idealSheaf.subschemeι y0 ∈ C.support := by rwa [hy0]
  have hyD0 : D.idealSheaf.subschemeι y0 ∈ D.support := by rwa [hy0]
  have hfD : (Y.presheaf.germ W _ hyW).hom f ∉
      IdealSheafData.stalk D.idealSheaf (D.idealSheaf.subschemeι y0) :=
    notMem_stalk_of_ne sY hYs hCD hyD0 hfspan
  have hf0 : (D.idealSheaf.subschemeι.stalkMap y0).hom ((Y.presheaf.germ W _ hyW).hom f) ≠ 0 := by
    intro h
    apply hfD
    rw [← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
    exact h
  -- the rational function `f|_D`
  have hy0W : y0 ∈ D.idealSheaf.subschemeι ⁻¹ᵁ W := hyW
  have : Nonempty (D.idealSheaf.subschemeι ⁻¹ᵁ W) := ⟨⟨y0, hy0W⟩⟩
  set a := D.idealSheaf.subscheme.germToFunctionField (D.idealSheaf.subschemeι ⁻¹ᵁ W)
    (D.idealSheaf.subschemeι.app W f) with ha
  have ha0 : a = algebraMap _ D.idealSheaf.subscheme.functionField
      ((D.idealSheaf.subschemeι.stalkMap y0).hom ((Y.presheaf.germ W _ hyW).hom f)) := by
    rw [ha, Scheme.Hom.germ_stalkMap_apply]
    exact (Scheme.algebraMap_germ_eq_germToFunctionField _ hy0W _).symm
  have hane : a ≠ 0 := by
    rw [ha0]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hf0
  -- the left side
  have hLHS : D.idealSheaf.subscheme.ord a y0 =
      (localIntersectionNumber sY y (Finsupp.single C 1) (Finsupp.single D 1) : ℤ) := by
    rw [ha0, ord_stalkMap_subschemeι_eq_finrank sY D.idealSheaf hy0co hcl0 _ hf0, ← hy0,
      localIntersectionNumber, localIdeal_single_one, localIdeal_single_one, hfspan, sup_comm]
  -- the local projection formula
  have hproj := ord_eq_finsum_ord_preimage (D.idealSheaf.subschemeι ≫ sY) ν hνgen hdimD' y0 hane
  -- the pull-back of `C`
  have hB := blowUpToBase_componentGenericPoint_notMem_supp hY hYd hy (Finsupp.single C (1 : ℤ))
  have hpb := isPullback_single_blowUp_singleton hY hYs hYd hy hF C hB
  rw [inverseTransformDivisor_single, hC'] at hpb
  change Divisor.IsPullback πy (Finsupp.single C 1) hB
    (Finsupp.single C' 1 + (m : ℤ) • Finsupp.single F 1) at hpb
  -- each term
  have hterm : ∀ x ∈ ν.base ⁻¹' {y0},
      D'.idealSheaf.subscheme.ord (dominantFunctionFieldMap ν a) x =
        ((localIntersectionNumber (πy ≫ sY) (D'.idealSheaf.subschemeι x) (Finsupp.single C' 1)
            (Finsupp.single D' 1) +
          m * localIntersectionNumber (πy ≫ sY) (D'.idealSheaf.subschemeι x)
            (Finsupp.single F 1) (Finsupp.single D' 1) : ℕ) : ℤ) := by
    intro x hx
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    set q := D'.idealSheaf.subschemeι x with hqdef
    have hfacx : D.idealSheaf.subschemeι (ν x) = πy q := apply_eq_of_comp_eq hfac x
    have hqy : πy q = y := by rw [← hfacx, hx, hy0]
    have hqF : q ∈ F.support := (hFmem q).mpr hqy
    have hqD' : q ∈ D'.support := by
      change q ∈ (D'.idealSheaf.support : Set _)
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
    have hxne : x ≠ genericPoint D'.idealSheaf.subscheme := by
      intro h
      apply hyne D
      rw [← hqy, hqdef, h, subschemeι_genericPoint D', hηD]
    have hxco := coheight_eq_one_of_ne_genericPoint hdimD' hxne
    have hqcl : IsClosed ({q} : Set Y'y) := isClosed_singleton_of_mem_inter' hY'd hFD' ⟨hqF, hqD'⟩
    -- local equations of `C'` and `F` at `q`
    obtain ⟨V1, hq1, g1, φ1, hφ1, hφ1g, hspan1⟩ := exists_localEquation_single hY's C' q
    obtain ⟨V2, hq2, g2, φ2, hφ2, hφ2g, hspan2⟩ := exists_localEquation_single hY's F q
    set V := V1 ⊓ V2
    have hqV : q ∈ V := ⟨hq1, hq2⟩
    set g : Γ(Y'y, V) := (Y'y).presheaf.map (homOfLE inf_le_left).op g1 *
      ((Y'y).presheaf.map (homOfLE inf_le_right).op g2) ^ m
    have hψ : Divisor.IsLocalEquation
        (Finsupp.single C' 1 + (m : ℤ) • Finsupp.single F 1 : Divisor Y'y) V
        (φ1 * φ2 ^ (m : ℤ)) :=
      (hφ1.mono inf_le_left).add ((hφ2.mono inf_le_right).zsmul m)
    have hgerm : ∀ z (hz : z ∈ V), ((Y'y).presheaf.germ V z hz).hom g =
        ((Y'y).presheaf.germ V1 z hz.1).hom g1 * (((Y'y).presheaf.germ V2 z hz.2).hom g2) ^ m := by
      intro z hz
      simp only [g, map_mul, map_pow]
      rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    have hψg : ∀ (Z : irreducibleComponents Y'y) (hZ : componentGenericPoint Y'y Z ∈ V),
        ((φ1 * φ2 ^ (m : ℤ) : (RationalFunctions Y'y)ˣ) : RationalFunctions Y'y) Z =
          ((Y'y).presheaf.germ V _ hZ).hom g := by
      intro Z hZ
      rw [hgerm, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val, Pi.mul_apply,
        Pi.pow_apply, hφ1g Z hZ.1, hφ2g Z hZ.2]
    have hqW : πy q ∈ W := by rw [← hfacx, hx]; exact hyW
    obtain ⟨w, hw⟩ := exists_unit_germ_app_eq_mul πy hB hpb hφ hφf hψ hψg hqW hqV
    -- the pull-back of `a` at `x`
    have hxU : x ∈ ν ⁻¹ᵁ (D.idealSheaf.subschemeι ⁻¹ᵁ W) := by
      change D.idealSheaf.subschemeι (ν x) ∈ W
      rw [hx]; exact hyW
    have : Nonempty (ν ⁻¹ᵁ (D.idealSheaf.subschemeι ⁻¹ᵁ W)) := ⟨⟨x, hxU⟩⟩
    have hpull : dominantFunctionFieldMap ν a = algebraMap _ D'.idealSheaf.subscheme.functionField
        ((D'.idealSheaf.subschemeι.stalkMap x).hom
          (((Y'y).presheaf.germ (πy ⁻¹ᵁ W) q hqW).hom ((πy).app W f))) := by
      have h1 := congrArg (fun φ => φ (D.idealSheaf.subschemeι.app W f))
        (Stacks.Chow.appLE_germToFunctionField_commutes ν (D.idealSheaf.subschemeι ⁻¹ᵁ W)
          (ν ⁻¹ᵁ (D.idealSheaf.subschemeι ⁻¹ᵁ W)) le_rfl)
      simp only [RingHom.comp_apply] at h1
      rw [ha, ← h1, Scheme.Hom.appLE_eq_app,
        ← Scheme.algebraMap_germ_eq_germToFunctionField _ hxU]
      erw [Scheme.Hom.germ_stalkMap_apply (f := D'.idealSheaf.subschemeι) (πy ⁻¹ᵁ W) x hqW]
      congr 1
      exact germ_app_congr hfac W f x hxU
    -- the three factors
    set ι' := D'.idealSheaf.subschemeι
    have hker : ∀ t : (Y'y).presheaf.stalk q, t ∉ IdealSheafData.stalk D'.idealSheaf q →
        (ι'.stalkMap x).hom t ≠ 0 := by
      intro t ht h
      apply ht
      have hmem : t ∈ RingHom.ker (ι'.stalkMap x).hom := h
      rwa [Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk] at hmem
    have hc1 := hker _ (notMem_stalk_of_ne (πy ≫ sY) hY's hC'D' hqD' hspan1)
    have hc2 := hker _ (notMem_stalk_of_ne (πy ≫ sY) hY's hFD' hqD' hspan2)
    have hwu : IsUnit ((ι'.stalkMap x).hom (w : (Y'y).presheaf.stalk q)) :=
      w.isUnit.map _
    have hinj := IsFractionRing.injective (D'.idealSheaf.subscheme.presheaf.stalk x)
      D'.idealSheaf.subscheme.functionField
    have hA1 : algebraMap _ D'.idealSheaf.subscheme.functionField
        ((ι'.stalkMap x).hom (((Y'y).presheaf.germ V1 q hq1).hom g1)) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr hc1
    have hA2 : algebraMap _ D'.idealSheaf.subscheme.functionField
        ((ι'.stalkMap x).hom (((Y'y).presheaf.germ V2 q hq2).hom g2)) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr hc2
    have hA0 : algebraMap _ D'.idealSheaf.subscheme.functionField
        ((ι'.stalkMap x).hom (w : (Y'y).presheaf.stalk q)) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr hwu.ne_zero
    have hord0 : D'.idealSheaf.subscheme.ord (algebraMap _ D'.idealSheaf.subscheme.functionField
        ((ι'.stalkMap x).hom (w : (Y'y).presheaf.stalk q))) x = 0 := by
      rw [ord_stalkMap_subschemeι_eq_finrank (πy ≫ sY) D'.idealSheaf hxco hqcl _ hwu.ne_zero,
        (Ideal.span_singleton_eq_top).mpr w.isUnit, sup_top_eq]
      let := MMP.Mori.stalkAlgebra (πy ≫ sY) q
      rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
    have hord1 : D'.idealSheaf.subscheme.ord (algebraMap _ D'.idealSheaf.subscheme.functionField
        ((ι'.stalkMap x).hom (((Y'y).presheaf.germ V1 q hq1).hom g1))) x =
        (localIntersectionNumber (πy ≫ sY) q (Finsupp.single C' 1) (Finsupp.single D' 1) : ℤ) := by
      rw [ord_stalkMap_subschemeι_eq_finrank (πy ≫ sY) D'.idealSheaf hxco hqcl _ hc1,
        localIntersectionNumber, localIdeal_single_one, localIdeal_single_one, hspan1, sup_comm]
    have hord2 : D'.idealSheaf.subscheme.ord (algebraMap _ D'.idealSheaf.subscheme.functionField
        ((ι'.stalkMap x).hom (((Y'y).presheaf.germ V2 q hq2).hom g2))) x =
        (localIntersectionNumber (πy ≫ sY) q (Finsupp.single F 1) (Finsupp.single D' 1) : ℤ) := by
      rw [ord_stalkMap_subschemeι_eq_finrank (πy ≫ sY) D'.idealSheaf hxco hqcl _ hc2,
        localIntersectionNumber, localIdeal_single_one, localIdeal_single_one, hspan2, sup_comm]
    rw [hpull, hw, hgerm q hqV]
    simp only [map_mul, map_pow]
    rw [Scheme.ord_mul hA0 (mul_ne_zero hA1 (pow_ne_zero _ hA2)),
      Scheme.ord_mul hA1 (pow_ne_zero _ hA2), Scheme.ord_pow hA2, hord0, hord1, hord2]
    push_cast; ring
  -- the fibre of `ν` over `y` is `F ∩ D'`
  have himage : D'.idealSheaf.subschemeι '' (ν.base ⁻¹' {y0}) = F.support ∩ D'.support := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
      have hfacx := apply_eq_of_comp_eq hfac x
      have hxD' : D'.idealSheaf.subschemeι x ∈ D'.support := by
        change D'.idealSheaf.subschemeι x ∈ (D'.idealSheaf.support : Set _)
        rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
      exact ⟨(hFmem _).mpr (by rw [← hfacx, hx, hy0]), hxD'⟩
    · rintro ⟨hqF, hqD'⟩
      obtain ⟨x, rfl⟩ : q ∈ Set.range D'.idealSheaf.subschemeι := by
        rwa [Scheme.IdealSheafData.range_subschemeι]
      refine ⟨x, ?_, rfl⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      apply D.idealSheaf.subschemeι.isClosedEmbedding.injective
      rw [apply_eq_of_comp_eq hfac x, (hFmem _).mp hqF, hy0]
  have hinjOn : Set.InjOn D'.idealSheaf.subschemeι (ν.base ⁻¹' {y0}) :=
    D'.idealSheaf.subschemeι.isClosedEmbedding.injective.injOn
  -- assembling
  set L1 : Y'y → ℕ := fun q =>
    localIntersectionNumber (πy ≫ sY) q (Finsupp.single C' 1) (Finsupp.single D' 1)
  set L2 : Y'y → ℕ := fun q =>
    localIntersectionNumber (πy ≫ sY) q (Finsupp.single F 1) (Finsupp.single D' 1)
  have hmain : (localIntersectionNumber sY y (Finsupp.single C 1) (Finsupp.single D 1) : ℤ) =
      ((∑ᶠ q ∈ F.support ∩ D'.support, (L1 q + m * L2 q) : ℕ) : ℤ) := by
    rw [← hLHS, hproj, finsum_mem_congr rfl hterm, Nat.cast_finsum_mem hfinFD, ← himage,
      finsum_mem_image hinjOn]
  have hmain' : localIntersectionNumber sY y (Finsupp.single C 1) (Finsupp.single D 1) =
      ∑ᶠ q ∈ F.support ∩ D'.support, (L1 q + m * L2 q) := by exact_mod_cast hmain
  have hL2sum : ∑ᶠ q ∈ F.support ∩ D'.support, L2 q = n := by
    rw [← Nat.cast_finsum_mem hfinFD] at hsumF
    exact_mod_cast hsumF
  have hL1sum : ∑ᶠ q ∈ F.support ∩ D'.support, L1 q =
      ∑ᶠ q ∈ F.support ∩ C'.support ∩ D'.support, L1 q := by
    apply finsum_mem_inter_support_eq
    ext q
    simp only [Set.mem_inter_iff, Function.mem_support]
    constructor
    · rintro ⟨⟨hqF, hqD'⟩, hq⟩
      refine ⟨⟨⟨hqF, ?_⟩, hqD'⟩, hq⟩
      by_contra hqC'
      apply hq
      change localIntersectionNumber (πy ≫ sY) q (Finsupp.single C' 1) (Finsupp.single D' 1) = 0
      rw [localIntersectionNumber, localIdeal_single_one, localIdeal_single_one,
        (IdealSheafData.stalk_eq_top_iff_notMem_support C'.idealSheaf q).2 hqC', top_sup_eq]
      let := MMP.Mori.stalkAlgebra (πy ≫ sY) q
      exact Module.finrank_zero_of_subsingleton
    · rintro ⟨⟨⟨hqF, -⟩, hqD'⟩, hq⟩
      exact ⟨⟨hqF, hqD'⟩, hq⟩
  rw [finsum_mem_add_distrib hfinFD, ← mul_finsum_mem' _ _ hfinFD, hL2sum, hL1sum] at hmain'
  rw [hmain', hmC, hnD]
  push_cast
  ring

end Blowup

end MMP.Threefold.Resolution

namespace MMP.Flips

open MMP.Mori MMP.Threefold.Resolution MMP.Resolution

/-- On a smooth variety a prime divisor has multiplicity at least one at each of its points. -/
private theorem one_le_toNat_multiplicityAt {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)}
    (hsm : IsSmoothScheme sY) (P : Mori.PrimeDivisor Y) {y : Y} (hy : y ∈ P.support) :
    1 ≤ (P.multiplicityAt y).toNat := by
  have htop := MMP.Threefold.Resolution.multiplicityAt_ne_top P
    (isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P) y
  have h1 : (1 : ℕ∞) ≤ P.multiplicityAt y := by
    refine le_iSup₂_of_le (f := fun (m : ℕ) (_ : P.idealSheaf.stalkIdeal y ≤
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ m) => (m : ℕ∞)) 1 ?_ (by simp)
    rw [pow_one]
    exact IsLocalRing.le_maximalIdeal
      ((Scheme.IdealSheafData.stalkIdeal_eq_top_iff _).not.mpr (not_not.mpr hy))
  lift P.multiplicityAt y to ℕ using htop with m
  exact_mod_cast h1

/-- If every component of `Θ` through `x` has nonnegative coefficient and multiplicity at least
one at `x`, then the coefficients of any finite set of components through `x` sum to at most
`mult_x Θ`. -/
private theorem sum_le_multiplicityAt {Y : Scheme.{u}} {Θ : QDivisor Y} {x : Y}
    (hnn : ∀ D : Mori.PrimeDivisor Y, x ∈ D.support → 0 ≤ Θ D)
    (hpos : ∀ D : Mori.PrimeDivisor Y, x ∈ D.support → 1 ≤ (D.multiplicityAt x).toNat)
    (S : Finset (Mori.PrimeDivisor Y)) (hS : ∀ D ∈ S, x ∈ D.support) :
    ∑ D ∈ S, Θ D ≤ DivisorWithCoeffs.multiplicityAt Θ x := by
  classical
  set f : Mori.PrimeDivisor Y → ℚ := fun D => (D.multiplicityAt x).toNat • Θ D with hf
  have hf0 : ∀ D, 0 ≤ f D := by
    intro D
    by_cases hD : x ∈ D.support
    · exact nsmul_nonneg (hnn D hD) _
    · simp [hf, PrimeDivisor.multiplicityAt_eq_zero_of_notMem D hD]
  have hmult : DivisorWithCoeffs.multiplicityAt Θ x = ∑ D ∈ S ∪ Θ.support, f D := by
    unfold DivisorWithCoeffs.multiplicityAt
    exact Finsupp.sum_of_support_subset _ Finset.subset_union_right _ (fun _ _ => smul_zero _)
  rw [hmult]
  calc ∑ D ∈ S, Θ D ≤ ∑ D ∈ S, f D := by
        refine Finset.sum_le_sum fun D hD => ?_
        have h1 := hpos D (hS D hD)
        have h0 := hnn D (hS D hD)
        simp only [hf, nsmul_eq_mul]
        nlinarith [show (1 : ℚ) ≤ ((D.multiplicityAt x).toNat : ℚ) by exact_mod_cast h1]
    _ ≤ ∑ D ∈ S ∪ Θ.support, f D :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun D _ _ => hf0 D

/-- The coefficient of `g⁻¹_*(D)` in `g⁻¹_* B` is that of `D` in `B`. -/
private theorem inverseTransformDivisor_apply_of_eq_some {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {g : Y ⟶ X} {D : Mori.PrimeDivisor X} {C : Mori.PrimeDivisor Y}
    (hD : inverseTransformPrimeDivisor g D = some C) (B : DivisorWithCoeffs R X) :
    inverseTransformDivisor g B C = B D :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hD (fun _ hD' =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      (map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD').1.symm.trans
      (map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD).1) B

/-- A prime divisor in the support of `mapPrimeDivisors φ D` is in the image of `φ`. -/
private theorem exists_eq_some_of_mem_support_mapPrimeDivisors {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)}
    {D : DivisorWithCoeffs R X} {Q : Mori.PrimeDivisor Y}
    (hQ : Q ∈ (DivisorWithCoeffs.mapPrimeDivisors φ D).support) : ∃ E, φ E = some Q := by
  classical
  by_contra! h
  refine Finsupp.mem_support_iff.mp hQ ?_
  clear hQ
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, Finsupp.add_apply, hD, hD', add_zero]
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases hφ : φ E with _ | Q'
    · rfl
    · simp [show Q' ≠ Q from fun h' => h E (h' ▸ hφ)]

/-- A point in the image of the closed subscheme of a prime divisor lies on its support. -/
private theorem mem_support_of_exists_subschemeι_eq {Y : Scheme.{u}} {C : Mori.PrimeDivisor Y}
    {y : Y} {p : C.idealSheaf.subscheme → Prop}
    (h : ∃ z : C.idealSheaf.subscheme, C.idealSheaf.subschemeι z = y ∧ p z) :
    y ∈ C.support := by
  obtain ⟨z, rfl, -⟩ := h
  exact (Scheme.IdealSheafData.range_subschemeι C.idealSheaf).le ⟨z, rfl⟩

/-- Let `π : X ⟶ Y` be an isomorphism away from `y`, with exceptional prime divisor `F` lying
exactly over `y`. A prime divisor `D' ≠ F` through a point of `F` is the strict transform of a
prime divisor of `Y` through `y`. -/
private theorem exists_inverseTransformPrimeDivisor_eq_some_of_mem_support {X Y : Scheme.{u}}
    {π : X ⟶ Y} {y : Y} {F : Mori.PrimeDivisor X} (hFy : ∀ q, q ∈ F.support ↔ π q = y)
    (hbir : ∀ x, x ≠ y → x ∈ biregularLocus π) {D' : Mori.PrimeDivisor X} (hD'F : D' ≠ F)
    {q : X} (hq : q ∈ F.support) (hqD' : q ∈ D'.support) :
    ∃ D : Mori.PrimeDivisor Y, inverseTransformPrimeDivisor π D = some D' ∧ y ∈ D.support := by
  have hπη : π D'.genericPoint ≠ y := fun h =>
    hD'F (eq_of_genericPoint_mem_support ((hFy _).2 h)).symm
  have hV := hbir _ hπη
  have hcoh : Order.coheight (π D'.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus π hV]
    exact D'.coheight_genericPoint
  have hDη := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh
  refine ⟨_, inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hDη.symm hV, ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hqD' ⊢
  rw [hDη, ← (hFy q).1 hq]
  exact specializes_iff_mem_closure.mp
    (π.base.hom.map_specializes (specializes_iff_mem_closure.mpr hqD'))

section LogCanonical

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  {P : X} {B : QDivisor X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y]
  [IsNormal Y] {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y}

/-- **A point of multiplicity `> 2` of `Θ_{g,a}` obstructs log canonicity** (FA 3.1.5, 3.3.2).
Let `a` be the log discrepancy vector of `(X, P; B)` on a resolution `g` of `(X, P)` with
exceptional curves `E_1, …, E_n`, and let `y ∈ g⁻¹(P)` be a closed point with
`mult_y Θ_{g,a} > 2`, where `Θ_{g,a} = logPullbackBoundary g B E a`. Then `(X, B)` is not log
canonical near `P`: on no open neighbourhood `U` of `P` is `(U, B|_U)` log canonical with
canonical divisor `K_X|_U`. -/
@[mmp "lem_fa3_high_multiplicity_not_lc"]
public theorem IsGermLogDiscrepancyVector.not_isLogCanonical_of_two_lt_multiplicityAt
    {a : Fin n → ℚ} (ha : IsGermLogDiscrepancyVector sX P B g E a) {y : Y}
    (hy : IsClosed ({y} : Set Y)) (hyP : g.base y = P)
    (hmult : 2 < DivisorWithCoeffs.multiplicityAt (logPullbackBoundary g B E a) y)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2) :
    ¬ HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogCanonical (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B)) := by
  intro hlc
  have hgr := ha.2.1
  have : LocallyOfFiniteType (g ≫ sX) := hgr.isVariety.toLocallyOfFiniteType
  have : IsIntegral Y := hgr.isVariety.toIsIntegral
  have hgr' := hgr.comp_blowUpToBase hy hyP
  have := hgr'.quasiCompact_comp
  obtain ⟨_, _⟩ := isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    hgr'.isSmoothResolution.isSmoothScheme
  obtain ⟨-, E', -, -, hiff⟩ := isGermLogDiscrepancyVector_snoc_blowUp_iff ha hy hyP
    (F := MMP.Resolution.exceptionalPrimeDivisor (g ≫ sX) _
      (isSmoothBlowup_vanishingIdeal_singleton (g ≫ sX) hgr.isSmoothResolution.isSmoothScheme hy)
      (isIrreducible_support_vanishingIdeal_singleton hy)
      (one_le_codimension_vanishingIdeal_singleton hgr.topologicalKrullDim_eq hy)) rfl
  have := ((hiff _).mpr rfl).nonneg_of_isLogCanonical hK hlc (Fin.last n)
  rw [Fin.snoc_last] at this
  linarith

/-- **The tangency obstruction** (FA 3.1.4, 3.1.5). Let `a` be the log discrepancy vector of
`(X, P; B)` on a resolution `g` of `(X, P)` with exceptional curves `E_1, …, E_n`,
`Θ = logPullbackBoundary g B E a`, and `y ∈ g⁻¹(P)` a closed point such that every component of
`Θ` through `y` has nonnegative coefficient. If `C₁ ≠ C₂` are components of `Θ` with coefficient
`1`, both smooth at `y`, with `(C₁ · C₂)_y ≥ 2`, then `(X, B)` is not log canonical near `P`:
on no open neighbourhood `U` of `P` is `(U, B|_U)` log canonical with canonical divisor
`K_X|_U`. -/
@[mmp "lem_fa3_tangency_obstruction"]
public theorem IsGermLogDiscrepancyVector.not_isLogCanonical_of_two_le_localIntersectionNumber
    {a : Fin n → ℚ} (ha : IsGermLogDiscrepancyVector sX P B g E a) {y : Y}
    (hy : IsClosed ({y} : Set Y)) (hyP : g.base y = P)
    (hnonneg : ∀ D : Mori.PrimeDivisor Y, y ∈ D.support → 0 ≤ logPullbackBoundary g B E a D)
    {C₁ C₂ : Mori.PrimeDivisor Y} (hC₁₂ : C₁ ≠ C₂)
    (hC₁ : logPullbackBoundary g B E a C₁ = 1) (hC₂ : logPullbackBoundary g B E a C₂ = 1)
    (hsm₁ : ∃ z : C₁.idealSheaf.subscheme, C₁.idealSheaf.subschemeι z = y ∧
      z ∈ smoothLocus (C₁.idealSheaf.subschemeι ≫ g ≫ sX))
    (hsm₂ : ∃ z : C₂.idealSheaf.subscheme, C₂.idealSheaf.subschemeι z = y ∧
      z ∈ smoothLocus (C₂.idealSheaf.subschemeι ≫ g ≫ sX))
    (hint : 2 ≤ localIntersectionNumber (g ≫ sX) y (Finsupp.single C₁ 1) (Finsupp.single C₂ 1))
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2) :
    ¬ HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogCanonical (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B)) := by
  classical
  set Θ := logPullbackBoundary g B E a with hΘ
  have hg := ha.2.1
  have hYv := hg.isVariety
  have hYs := hg.isSmoothResolution.isSmoothScheme
  have hYd := hg.topologicalKrullDim_eq
  have hyC₁ := mem_support_of_exists_subschemeι_eq hsm₁
  have hyC₂ := mem_support_of_exists_subschemeι_eq hsm₂
  -- `mult_y Θ ≥ 2`
  have hm2 : 2 ≤ DivisorWithCoeffs.multiplicityAt Θ y := by
    have := sum_le_multiplicityAt hnonneg
      (fun D hD => one_le_toNat_multiplicityAt hYs D hD) {C₁, C₂}
      (by intro D hD; simp only [Finset.mem_insert, Finset.mem_singleton] at hD
          rcases hD with rfl | rfl <;> assumption)
    rw [Finset.sum_pair hC₁₂, hC₁, hC₂] at this
    linarith
  rcases lt_or_ge 2 (DivisorWithCoeffs.multiplicityAt Θ y) with hlt | hle
  · exact ha.not_isLogCanonical_of_two_lt_multiplicityAt hy hyP hlt hK
  have hm : DivisorWithCoeffs.multiplicityAt Θ y = 2 := le_antisymm hle hm2
  -- blow up `y`
  have : LocallyOfFiniteType (g ≫ sX) := hYv.toLocallyOfFiniteType
  have : IrreducibleSpace Y := by have := hYv.toIsIntegral; infer_instance
  have hsb := isSmoothBlowup_vanishingIdeal_singleton (sY := g ≫ sX) hYs hy
  let F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) :=
    exceptionalPrimeDivisor (g ≫ sX) _ hsb (isIrreducible_support_vanishingIdeal_singleton hy)
      (one_le_codimension_vanishingIdeal_singleton hYd hy)
  have hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) :=
    rfl
  obtain ⟨hres', E', hE', -, hiff⟩ := isGermLogDiscrepancyVector_snoc_blowUp_iff ha hy hyP hF
  set π := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))
  have := (hg.comp_blowUpToBase hy hyP).quasiCompact_comp
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    (hg.comp_blowUpToBase hy hyP).isSmoothResolution.isSmoothScheme).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    (hg.comp_blowUpToBase hy hyP).isSmoothResolution.isSmoothScheme).2
  have := compactSpace_blowUp_singleton hYv hYd hy
  set a' : Fin (n + 1) → ℚ := Fin.snoc a (2 - DivisorWithCoeffs.multiplicityAt Θ y) with ha'def
  have ha' : IsGermLogDiscrepancyVector sX P B (π ≫ g) (Fin.snoc E' F : Fin (n + 1) → _) a' :=
    (hiff a').2 rfl
  set Θ' := logPullbackBoundary (π ≫ g) B (Fin.snoc E' F : Fin (n + 1) → _) a' with hΘ'def
  have hΘ' : Θ' = inverseTransformDivisor π Θ + Finsupp.single F 1 := by
    rw [hΘ'def, hΘ, logPullbackBoundary, logPullbackBoundary,
      hg.inverseTransformDivisor_comp_blowUpToBase hy hyP, Fin.sum_univ_castSucc, map_add,
      map_sum]
    simp only [ha'def, Fin.snoc_castSucc, Fin.snoc_last, hm,
      inverseTransformDivisor_single_of_eq_some (hE' _)]
    rw [add_assoc]
    norm_num
    rfl
  have hY's := hres'.isSmoothResolution.isSmoothScheme
  have hFy : ∀ q, q ∈ F.support ↔ π q = y :=
    mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hy hF
  have hFnot : ∀ (D : Mori.PrimeDivisor Y) (D' : Mori.PrimeDivisor _),
      inverseTransformPrimeDivisor π D = some D' → D' ≠ F := fun _ _ h =>
    (ne_of_inverseTransformPrimeDivisor_eq_some hYv hYd hy hF h).symm
  have hΘ'F : Θ' F = 1 := by
    rw [hΘ', Finsupp.add_apply, Finsupp.single_eq_same]
    have h0 : inverseTransformDivisor π Θ F = 0 := by
      by_contra h0
      obtain ⟨D, hD⟩ := exists_eq_some_of_mem_support_mapPrimeDivisors
        (Finsupp.mem_support_iff.2 h0)
      exact hFnot D F hD rfl
    rw [h0, zero_add]
  have hΘ'tr : ∀ (D : Mori.PrimeDivisor Y) (D' : Mori.PrimeDivisor _),
      inverseTransformPrimeDivisor π D = some D' → Θ' D' = Θ D := by
    intro D D' h
    rw [hΘ', Finsupp.add_apply, inverseTransformDivisor_apply_of_eq_some h]
    simp [Ne.symm (hFnot D D' h)]
  have hnonneg' : ∀ q ∈ F.support, ∀ D' : Mori.PrimeDivisor _, q ∈ D'.support → 0 ≤ Θ' D' := by
    intro q hq D' hqD'
    by_cases hD'F : D' = F
    · rw [hD'F, hΘ'F]; norm_num
    obtain ⟨D, hDD', hyD⟩ := exists_inverseTransformPrimeDivisor_eq_some_of_mem_support hFy
      (fun _ hx => mem_biregularLocus_blowUpToBase_singleton hy hx) hD'F hq hqD'
    rw [hΘ'tr D D' hDD']
    exact hnonneg D hyD
  -- the strict transforms of `C₁`, `C₂`
  obtain ⟨C₁', hC₁', hη₁⟩ := exists_inverseTransformPrimeDivisor_eq_some (g := π) C₁
    (mem_biregularLocus_blowUpToBase_singleton hy (genericPoint_ne_of_isClosed hYv hYd hy C₁))
  obtain ⟨C₂', hC₂', hη₂⟩ := exists_inverseTransformPrimeDivisor_eq_some (g := π) C₂
    (mem_biregularLocus_blowUpToBase_singleton hy (genericPoint_ne_of_isClosed hYv hYd hy C₂))
  have hC₁₂' : C₁' ≠ C₂' := by
    rintro rfl
    exact hC₁₂ (AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hη₁.symm.trans hη₂))
  -- Noether's formula: `C₁'` and `C₂'` meet on `F`
  have hN := localIntersectionNumber_eq_multiplicityAt_mul_add_finsum hYv hYs hYd hy hF hC₁₂
    hyC₁ hyC₂ hC₁' hC₂'
  rw [(multiplicityAt_eq_one_iff_exists_mem_smoothLocus hYv hYs hYd C₁ hyC₁).2 hsm₁,
    (multiplicityAt_eq_one_iff_exists_mem_smoothLocus hYv hYs hYd C₂ hyC₂).2 hsm₂] at hN
  have hS : (F.support ∩ C₁'.support ∩ C₂'.support : Set _).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, finsum_mem_empty] at hN
    norm_num at hN
    omega
  obtain ⟨q, ⟨⟨hqF, hq₁⟩, hq₂⟩, hqc⟩ := IsClosed.exists_closed_singleton
    ((F.idealSheaf.support.isClosed.inter C₁'.idealSheaf.support.isClosed).inter
      C₂'.idealSheaf.support.isClosed) hS
  have hqP : (π ≫ g).base q = P := by
    rw [Scheme.Hom.comp_apply, (hFy q).1 hqF, hyP]
  have hmult' : 2 < DivisorWithCoeffs.multiplicityAt Θ' q := by
    have := sum_le_multiplicityAt (hnonneg' q hqF)
      (fun D hD => one_le_toNat_multiplicityAt hY's D hD) {C₁', C₂', F}
      (by intro D hD; simp only [Finset.mem_insert, Finset.mem_singleton] at hD
          rcases hD with rfl | rfl | rfl <;> assumption)
    rw [Finset.sum_insert (by simp [hC₁₂', hFnot C₁ C₁' hC₁']),
      Finset.sum_pair (hFnot C₂ C₂' hC₂'), hΘ'tr C₁ C₁' hC₁', hΘ'tr C₂ C₂' hC₂', hC₁, hC₂,
      hΘ'F] at this
    linarith
  exact ha'.not_isLogCanonical_of_two_lt_multiplicityAt hqc hqP hmult' hK

end LogCanonical

/-- In a Noetherian quasi-sober space, a closed point `y` of a closed preconnected set `F` with
`F ≠ {y}` is a proper specialization of some other point of `F`. -/
private theorem exists_ne_specializes_of_isPreconnected {T : Type*} [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] [QuasiSober T] {F : Set T} (hF : IsClosed F)
    (hFc : IsPreconnected F) {y : T} (hyF : y ∈ F) (hy : IsClosed ({y} : Set T))
    (hne : ¬ F ⊆ {y}) : ∃ η ∈ F, η ≠ y ∧ η ⤳ y := by
  classical
  by_contra H
  push Not at H
  set G := closure (F \ {y})
  have hGF : G ⊆ F := closure_minimal Set.sdiff_subset hF
  obtain ⟨S, hSirr, hS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finset_irreducible ⟨G, isClosed_closure⟩
  have hS' : G = ⋃ (K : TopologicalSpace.Closeds T) (_ : K ∈ S), (K : Set T) := by
    have := congrArg (fun K : TopologicalSpace.Closeds T => (K : Set T)) hS
    rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_eq_iSup] at this
    simpa [Set.iSup_eq_iUnion] using this
  set S' := S.filter (fun K : TopologicalSpace.Closeds T => (K : Set T) ≠ {y})
  have hsub : G ⊆ ⋃ (K : TopologicalSpace.Closeds T) (_ : K ∈ S'), (K : Set T) := by
    refine closure_minimal ?_ (isClosed_biUnion_finset
      (f := fun K : TopologicalSpace.Closeds T => (K : Set T)) fun K _ => K.isClosed)
    intro x hx
    have hxG : x ∈ G := subset_closure hx
    rw [hS'] at hxG
    obtain ⟨K, hK, hxK⟩ := Set.mem_iUnion₂.mp hxG
    refine Set.mem_iUnion₂.mpr ⟨K, Finset.mem_filter.mpr ⟨hK, fun h => ?_⟩, hxK⟩
    rw [h] at hxK
    exact hx.2 hxK
  have hyG : y ∉ G := by
    intro hyG
    obtain ⟨K, hK, hyK⟩ := Set.mem_iUnion₂.mp (hsub hyG)
    obtain ⟨hKS, hKy⟩ := Finset.mem_filter.mp hK
    have hKirr : IsIrreducible (K : Set T) := hSirr ⟨K, hKS⟩
    have hgen := hKirr.isGenericPoint_genericPoint_closure
    rw [K.isClosed.closure_eq] at hgen
    have hKG : (K : Set T) ⊆ G := by
      rw [hS']; exact Set.subset_biUnion_of_mem (u := fun K : TopologicalSpace.Closeds T =>
        (K : Set T)) hKS
    refine H _ (hGF (hKG hgen.mem)) (fun h => hKy ?_) (hgen.specializes hyK)
    rw [← hgen.def, h, hy.closure_eq]
  obtain ⟨x, hxF, hxy⟩ := Set.not_subset.mp hne
  have := isPreconnected_closed_iff.mp hFc G {y} isClosed_closure hy
    (fun z hz => by
      by_cases hzy : z = y
      · exact Or.inr hzy
      · exact Or.inl (subset_closure ⟨hz, hzy⟩))
    ⟨x, hxF, subset_closure ⟨hxF, hxy⟩⟩ ⟨y, hyF, rfl⟩
  obtain ⟨z, -, hzG, rfl⟩ := this
  exact hyG hzG

/-- A point of a proper closed subset does not have dense closure. -/
private theorem closure_singleton_ne_univ {T : Type*} [TopologicalSpace T] {F : Set T}
    (hF : IsClosed F) (hFne : F ≠ Set.univ) {x : T} (hx : x ∈ F) :
    closure ({x} : Set T) ≠ Set.univ := fun h =>
  hFne (Set.eq_univ_of_univ_subset
    (h ▸ hF.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)))

/-- On an irreducible scheme, a point whose closure is not everything has positive coheight. -/
private theorem coheight_ne_zero {Y : Scheme.{u}} [IrreducibleSpace Y] {x : Y}
    (hx : closure ({x} : Set Y) ≠ Set.univ) : Order.coheight x ≠ 0 := by
  intro h0
  have hgx : genericPoint Y ≤ x :=
    Order.coheight_eq_zero.mp h0 ((genericPoint_spec Y).specializes (Set.mem_univ x))
  refine hx (Set.eq_univ_of_univ_subset ?_)
  rw [← (genericPoint_spec Y).def]
  exact isClosed_closure.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hgx))

/-- On an integral scheme of dimension two, locally of finite type over a field, a non-closed
point whose closure is not the whole scheme has coheight one. -/
private theorem coheight_eq_one_of_not_isClosed {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (hYd : topologicalKrullDim Y = 2) {x : Y} (hx : ¬ IsClosed ({x} : Set Y))
    (hx' : closure ({x} : Set Y) ≠ Set.univ) : Order.coheight x = 1 := by
  obtain ⟨z, hz, hzx⟩ : ∃ z ∈ closure ({x} : Set Y), z ≠ x := by
    by_contra! h
    exact hx (isClosed_of_closure_subset h)
  have hz2 : Order.coheight z ≤ 2 := by
    have h := topologicalKrullDim_closure_singleton_add_coheight sY z
    rw [hYd] at h
    generalize topologicalKrullDim (closure ({z} : Set Y)) = d at h
    induction d using WithBot.recBotCoe with
    | bot => simp at h
    | coe d => exact le_add_self.trans_eq (WithBot.coe_inj.mp (by push_cast; exact h))
  have h := (coheight_add_one_le_of_specializes (specializes_iff_mem_closure.mpr hz)
    hzx.symm).trans hz2
  rw [← one_add_one_eq_two, ENat.add_le_add_iff_right ENat.one_ne_top] at h
  exact h.antisymm (Order.one_le_iff_ne_zero.mpr (coheight_ne_zero hx'))

/-- On an irreducible scheme, a point `η` of coheight one is specialized to only by itself
among the points whose closure is not the whole scheme. -/
private theorem eq_of_specializes_of_coheight_eq_one {Y : Scheme.{u}} [IrreducibleSpace Y]
    {ξ η : Y} (hη : Order.coheight η = 1) (h : ξ ⤳ η)
    (hξ : closure ({ξ} : Set Y) ≠ Set.univ) : ξ = η := by
  by_contra hne
  have h1 := coheight_add_one_le_of_specializes h hne
  rw [hη] at h1
  exact coheight_ne_zero hξ
    (nonpos_iff_eq_zero.mp ((ENat.add_le_add_iff_right ENat.one_ne_top).mp (by simpa using h1)))

/-- The support of a curve is not contained in a single point. -/
private theorem not_support_subset_singleton {Z : Scheme.{u}} {D : Mori.PrimeDivisor Z}
    (hD : IsCurveIn D.idealSheaf) (p : Z) : ¬ D.support ⊆ {p} := by
  intro h
  have h1 := hD.2
  rw [topologicalKrullDim_subscheme] at h1
  have : Subsingleton (D.idealSheaf.support : Set Z) :=
    ((Set.subsingleton_singleton).anti h).coe_sort
  have : DiscreteTopology (D.idealSheaf.support : Set Z) := Subsingleton.discreteTopology
  have h0 := topologicalKrullDim_zero_of_discreteTopology (D.idealSheaf.support : Set Z)
  rw [h1] at h0
  exact absurd h0 (by decide)

section Fibre

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
  (hYv : Mori.IsVariety k sY) (hYd : topologicalKrullDim Y = 2) {g : Y ⟶ X} {P : X}
  (hFcl : IsClosed (g.base ⁻¹' {P})) (hFne : g.base ⁻¹' {P} ≠ Set.univ)

include hYv hYd hFcl hFne

/-- On a surface `Y`, the closure of a coheight-one point `η` of a proper closed fibre
`g⁻¹(P)` is an exceptional curve of `g` over `P`. -/
private theorem isGermExceptionalCurve_ofCoheightOne {η : Y} (hηF : η ∈ g.base ⁻¹' {P})
    (hη1 : Order.coheight η = 1) :
    IsGermExceptionalCurve g P (AlgebraicGeometry.PrimeDivisor.ofCoheightOne η hη1) := by
  have : IsIntegral Y := hYv.toIsIntegral
  have hsupp : (AlgebraicGeometry.PrimeDivisor.ofCoheightOne η hη1).support = closure {η} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  refine ⟨⟨⟨?_, ?_⟩, fun Z ⟨hZirr, hZF⟩ hle => ?_⟩,
    isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hYv hYd _⟩
  · rw [hsupp]; exact isIrreducible_singleton.closure
  · rw [hsupp]; exact hFcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηF)
  · rw [hsupp] at hle ⊢
    have hgen := hZirr.isGenericPoint_genericPoint_closure
    have hξF : hZirr.genericPoint ∈ g.base ⁻¹' {P} := hFcl.closure_subset_iff.mpr hZF hgen.mem
    have hξ := eq_of_specializes_of_coheight_eq_one hη1
      (hgen.specializes (subset_closure (hle (subset_closure rfl))))
      (closure_singleton_ne_univ hFcl hFne hξF)
    rw [← hξ, hgen.def]
    exact subset_closure

/-- Every point `y` of a connected fibre `g⁻¹(P)` of a surface which contains an exceptional
curve lies on an exceptional curve. -/
private theorem exists_mem_support_exceptional [IsNoetherian Y]
    (hFconn : _root_.IsPreconnected (g.base ⁻¹' {P})) {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y}
    (hE : IsExceptionalCurveEnumeration g P E) (hn : 0 < n) {y : Y}
    (hyF : y ∈ g.base ⁻¹' {P}) : ∃ j, y ∈ (E j).support := by
  have : IsIntegral Y := hYv.toIsIntegral
  have : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  obtain ⟨η, hηF, hηcl, hηy⟩ : ∃ η ∈ g.base ⁻¹' {P}, ¬ IsClosed ({η} : Set Y) ∧ η ⤳ y := by
    by_cases hy : IsClosed ({y} : Set Y)
    · have h0 := hE.isGermExceptionalCurve ⟨0, hn⟩
      obtain ⟨η, hηF, hηy, hsp⟩ := exists_ne_specializes_of_isPreconnected hFcl hFconn hyF hy
        fun h => not_support_subset_singleton h0.2 y (h0.1.prop.2.trans h)
      exact ⟨η, hηF, fun hc => hηy (hc.closure_eq ▸ hsp.mem_closure).symm, hsp⟩
    · exact ⟨y, hyF, hy, specializes_rfl⟩
  have hη1 :=
    coheight_eq_one_of_not_isClosed sY hYd hηcl (closure_singleton_ne_univ hFcl hFne hηF)
  obtain ⟨j, hj⟩ :=
    hE.exists_eq _ (isGermExceptionalCurve_ofCoheightOne hYv hYd hFcl hFne hηF hη1)
  refine ⟨j, ?_⟩
  rw [hj, AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  exact hηy.mem_closure

end Fibre

/-- Two distinct curves on a smooth surface, the first proper, that share a point have
intersection number at least one. -/
private theorem exists_one_le_isIntersectionNumber {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hYv : Mori.IsVariety k sY) (hsm : IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2) {C D : Mori.PrimeDivisor Y} (hCD : C ≠ D)
    (hC : IsProper (C.idealSheaf.subschemeι ≫ sY)) {y : Y} (hy : y ∈ C.support ∩ D.support) :
    ∃ x : ℚ, IsIntersectionNumber sY (Finsupp.single D 1) C.idealSheaf x ∧ 1 ≤ x := by
  obtain ⟨hfin, hint, hpos⟩ :=
    isIntersectionNumber_finsum_localIntersectionNumber_of_ne sY hYv hsm hYd hCD hC
  refine ⟨_, hint, ?_⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact le_trans (by exact_mod_cast hpos y hy) (Finset.single_le_sum
    (fun _ _ => Nat.cast_nonneg _) ((Set.Finite.mem_toFinset hfin).mpr hy))

/-- (FA 3.1.4–3.1.6) Let `g` be a resolution of the surface germ with boundary `(X, P; B)` with
exceptional curves `E_1, …, E_n`, `n ≥ 1`. Then for every component `C` of `B` there is `j` such
that the intersection number `(g⁻¹_* C · E_j)` is defined and at least `1`. -/
@[mmp "lem_fa3_boundary_meets_exceptional"]
public theorem IsGermResolution.exists_one_le_inverseTransform_intersectionNumber
    {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {B : QDivisor X}
    {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
    {E : Fin n → Mori.PrimeDivisor Y}
    (hg : IsGermResolution sX P g) (hB : IsSurfaceGermWithBoundary sX P B)
    (hE : IsExceptionalCurveEnumeration g P E) (hn : 0 < n)
    {C : Mori.PrimeDivisor X} (hC : C ∈ B.support) :
    ∃ (j : Fin n) (x : ℚ), IsIntersectionNumber (g ≫ sX)
      (inverseTransformDivisor g (Finsupp.single C (1 : ℚ))) (E j).idealSheaf x ∧ 1 ≤ x := by
  have hXs := hg.isSurfaceGerm
  have hXv : Mori.IsNormalVariety k sX := hXs.1
  have : IsIntegral X := hXv.1.toIsIntegral
  have : IsIntegral Y := hg.isIntegral
  have : IsProper g := hg.isSmoothResolution.isProper
  have : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  have : IsSeparated sX := hXv.1.toIsSeparated
  have : QuasiCompact sX := hXv.1.toQuasiCompact
  have hYv : Mori.IsVariety k (g ≫ sX) := ⟨⟩
  have hYd := hg.topologicalKrullDim_eq
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : IsNoetherian Y := ⟨⟩
  have hFcl : IsClosed (g.base ⁻¹' {P}) := hXs.2.2.1.preimage g.continuous
  -- the transform `C'` of `C`; its generic point lies over that of `C`, which is not `P`
  have hCc := isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hXv.1 hXs.2.1 C
  have hηP : C.genericPoint ≠ P := by
    intro h
    refine not_support_subset_singleton hCc P fun z hz => ?_
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hz
    change z ∈ closure {C.genericPoint} at hz
    rwa [h, hXs.2.2.1.closure_eq] at hz
  have hηV : C.genericPoint ∈ biregularLocus g := by
    obtain ⟨U, hU, hiso⟩ := hg.isIso_away
    refine le_biregularLocus (V := U) hiso ?_
    change C.genericPoint ∈ (U : Set X)
    rw [hU]
    exact hηP
  obtain ⟨C', hC', hgC'⟩ := exists_inverseTransformPrimeDivisor_eq_some C hηV
  have hC'F : C'.genericPoint ∉ g.base ⁻¹' {P} := fun h => hηP (hgC' ▸ h)
  have hC'mem : C'.genericPoint ∈ C'.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  -- `g` is closed, so `g(C') ⊇ C ∋ P`: a point `y` of `C'` lies over `P`
  obtain ⟨y, hyC', hyP⟩ : ∃ y ∈ C'.support, g y = P := by
    refine (AlgebraicGeometry.PrimeDivisor.support_eq_closure C ▸
      (g.isClosedMap _ C'.idealSheaf.support.isClosed).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr ⟨_, hC'mem, hgC'⟩)) (hB.2.1 C hC)
  obtain ⟨j, hyj⟩ :=
    exists_mem_support_exceptional hYv hYd hFcl (fun h => hC'F (h ▸ Set.mem_univ _))
    ((MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism (g ≫ sX) sX hYv
      hXv g hg.isSmoothResolution.isBirationalMorphism).2 P).isPreconnected hE hn hyP
  have hEj := hE.isGermExceptionalCurve j
  rw [inverseTransformDivisor_single_of_eq_some hC']
  exact ⟨j, exists_one_le_isIntersectionNumber hYv hg.isSmoothResolution.isSmoothScheme hYd
    (fun h : E j = C' => hC'F (hEj.1.prop.2 (h ▸ hC'mem)))
    (IsGermExceptionalCurve.isProper sX hg hEj).2 ⟨hyj, hyC'⟩⟩

/-- A finite set of points carrying positive natural numbers summing to at most `1` is empty or a
singleton on which the number is `1`. -/
private lemma eq_empty_or_eq_singleton_of_sum_le_one {α : Type*} {s : Finset α} {f : α → ℕ}
    (hpos : ∀ y ∈ s, 0 < f y) (hle : ∑ y ∈ s, f y ≤ 1) :
    s = ∅ ∨ ∃ y, s = {y} ∧ f y = 1 := by
  rcases Finset.eq_empty_or_nonempty s with h | ⟨y, hy⟩
  · exact Or.inl h
  · have hsum := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hy).trans hle
    have hy1 : f y = 1 := by have := hpos y hy; omega
    refine Or.inr ⟨y, Finset.eq_singleton_iff_unique_mem.mpr ⟨hy, fun z hz => ?_⟩, hy1⟩
    by_contra hzy
    have := Finset.add_le_sum (f := f) (fun _ _ => Nat.zero_le _) hz hy hzy
    have := hpos z hz
    omega

section

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {P : X} {B : QDivisor X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] {n : ℕ} {E : Fin n → MMP.Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}

/-- For `j ≠ l`, the edge weight `m_{lj}` is the sum of the (positive) local intersection numbers
of `E_j` and `E_l` over their finite intersection. -/
private lemma edgeWeight_eq_sum (hΓ : IsWeightedDualGraph sX P B g E Γ) {j l : Fin n}
    (hjl : j ≠ l) :
    ∃ s : Finset Y, ((E j).support ∩ (E l).support : Set Y) = ↑s ∧
      Γ.edgeWeight l j = ∑ y ∈ s,
        localIntersectionNumber (g ≫ sX) y (Finsupp.single (E j) 1) (Finsupp.single (E l) 1) ∧
      ∀ y ∈ s, 0 <
        localIntersectionNumber (g ≫ sX) y (Finsupp.single (E j) 1) (Finsupp.single (E l) 1) := by
  have hg := hΓ.isGermResolution
  have hCD : E j ≠ E l := fun h => hjl (hΓ.isExceptionalCurveEnumeration.injective h)
  have hC := ((hΓ.isExceptionalCurveEnumeration.isGermExceptionalCurve j).isProper sX hg).2
  obtain ⟨hfin, hI, hpos⟩ := isIntersectionNumber_finsum_localIntersectionNumber_of_ne (g ≫ sX)
    (MMP.Flips.IsGermResolution.isVariety hg)
    hg.isSmoothResolution.isSmoothScheme hg.topologicalKrullDim_eq hCD hC
  have heq := (hΓ.edgeWeight l j (Ne.symm hjl)).unique hI
  refine ⟨hfin.toFinset, by simp, ?_, fun y hy => hpos y (by simpa using hy)⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at heq
  exact_mod_cast heq

/-- A common point of `E_j` and `E_l` (`j ≠ l`) makes `v_j` and `v_l` adjacent in `Γ`. -/
private lemma adj_of_mem_inter (hΓ : IsWeightedDualGraph sX P B g E Γ) {j l : Fin n}
    (hjl : j ≠ l) {y : Y} (hy : y ∈ ((E j).support ∩ (E l).support : Set Y)) :
    Γ.underlyingGraph.Adj l j := by
  obtain ⟨s, hs, hw, hpos⟩ := edgeWeight_eq_sum hΓ hjl
  have hys : y ∈ s := by rwa [hs] at hy
  refine ⟨Ne.symm hjl, ?_⟩
  rw [hw]
  exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨y, hys, hpos y hys⟩

end

/-- **Rational trees are simple normal crossing** (FA 3.1.6.2, 3.3.2). Let `g` be a resolution
of a surface germ with boundary `(X, P; B)` over an algebraically closed field, with exceptional
curves `E_1, …, E_n` and weighted dual graph `Γ = Γ(g)`. If `Γ` is a rational tree, then every
`E_j` is a smooth rational curve; any two distinct `E_j`, `E_l` are disjoint or meet in exactly
one point `y`, transversally (`(E_j · E_l)_y = 1`); and no three distinct `E_j` have a common
point. -/
@[mmp "lem_fa3_tree_snc"]
public theorem IsWeightedDualGraph.simpleNormalCrossing_of_isRationalTree {k : Type u}
    [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
    {B : QDivisor X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hΓ : IsWeightedDualGraph sX P B g E Γ) (hT : Γ.IsRationalTree) :
    (∀ j, IsSmoothRationalCurve (g ≫ sX) (E j).idealSheaf) ∧
    (∀ j l, j ≠ l →
      ((E j).support ∩ (E l).support : Set Y) = ∅ ∨
        ∃ y : Y, ((E j).support ∩ (E l).support : Set Y) = {y} ∧
          localIntersectionNumber (g ≫ sX) y (Finsupp.single (E j) 1)
            (Finsupp.single (E l) 1) = 1) ∧
    (∀ j l m, j ≠ l → l ≠ m → j ≠ m →
      ((E j).support ∩ (E l).support ∩ (E m).support : Set Y) = ∅) := by
  refine ⟨fun j => ?_, fun j l hjl => ?_, fun j l m hjl hlm hjm => ?_⟩
  · -- `p_a(E_j) = 0` gives `E_j ≅ ℙ¹_k`
    have hcurve := (hΓ.isExceptionalCurveEnumeration.isGermExceptionalCurve j).isProper sX
      hΓ.isGermResolution
    obtain ⟨_, _, hp⟩ := hΓ.genus j
    have : IsIntegral (E j).idealSheaf.subscheme := hcurve.1.1
    obtain ⟨-, hiff⟩ := arithmeticGenus_nonneg_and_eq_zero_iff
      ((E j).idealSheaf.subschemeι ≫ g ≫ sX) hcurve.1.2
    obtain ⟨e, he⟩ := hiff.mp (by rw [← hp, hT.genus_eq_zero j]; rfl)
    exact ⟨⟨hcurve.1, hcurve.2, e.hom, he, inferInstance, isBirationalMorphism_of_isIso _⟩,
      e, he⟩
  · -- `m_{lj} ≤ 1` is a sum of positive local terms
    obtain ⟨s, hs, hw, hpos⟩ := edgeWeight_eq_sum hΓ hjl
    rw [hs]
    rcases eq_empty_or_eq_singleton_of_sum_le_one hpos
        (hw ▸ hT.edgeWeight_le_one l j) with h | ⟨y, rfl, hy⟩
    · exact Or.inl (by simp [h])
    · exact Or.inr ⟨y, by simp, hy⟩
  · -- a triple point would be a triangle in the tree
    refine Set.eq_empty_of_forall_notMem fun y ⟨⟨hj, hl⟩, hm⟩ => ?_
    have hT' : Γ.underlyingGraph.IsAcyclic := by
      rcases hT.isTree_or_isEmpty with h | h
      · exact h.isAcyclic
      · exact (h.false j).elim
    refine hT'.cliqueFree le_rfl {j, l, m} ?_
    rw [SimpleGraph.is3Clique_triple_iff]
    exact ⟨(adj_of_mem_inter hΓ hjl ⟨hj, hl⟩).symm, (adj_of_mem_inter hΓ hjm ⟨hj, hm⟩).symm,
      (adj_of_mem_inter hΓ hlm ⟨hl, hm⟩).symm⟩

end MMP.Flips
