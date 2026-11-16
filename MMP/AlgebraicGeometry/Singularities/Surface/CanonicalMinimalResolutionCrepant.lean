module
public import MMP.AlgebraicGeometry.Singularities.RamifiedCyclicCover
public import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupNumericalDiscrepancy
public import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceCurves
public import MMP.AlgebraicGeometry.Intersection.Surface.NumericalPullback
public import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolutionCanonicalNef

/-!
# Minimal resolutions of canonical surface pairs are crepant

Let `(0 ∈ X, Δ)` be a surface germ over an algebraically closed field `k` of characteristic zero,
with `Δ` an effective `ℚ`-divisor such that `(X, Δ)` is canonical, and let `f : Y ⟶ X` be the
minimal resolution. Then every `f`-exceptional curve `E` has discrepancy `a(E, X, Δ) = 0`.

## Main results

* `MMP.Mori.IsCanonicalPair.isDiscrepancy_zero_of_isMinimalSurfaceResolution`: on a minimal
  resolution of a canonical surface germ with effective boundary, every exceptional curve has
  discrepancy `0`.

## Implementation notes

The discrepancy is the predicate `MMP.Mori.IsDiscrepancy`, which determines its value uniquely;
the conclusion says that this value is `0`. The germ is replaced by `X` itself, on which `(X, Δ)`
is assumed canonical, as the convention for germs allows. The exceptional curves are all the
`f`-exceptional curves of `Y`; on a germ these are exactly the curves over `0`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  proof of Theorem 4.5.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

/-- A morphism contracting a curve `C` to a point `x` sends every point of `C` to `x`. -/
private lemma apply_eq_of_image_eq {X Y : Scheme.{u}} {f : Y ⟶ X} {C : Y.IdealSheafData} {x : X}
    (hx : f.base '' C.support = {x}) {y : Y} (hy : y ∈ (C.support : Set Y)) : f y = x :=
  Set.mem_singleton_iff.mp (hx ▸ Set.mem_image_of_mem f.base hy)

/-- A proper morphism contracts a curve to a closed point. -/
private lemma isClosed_singleton_of_image_eq {X Y : Scheme.{u}} {f : Y ⟶ X} [IsProper f]
    {C : Y.IdealSheafData} {x : X} (hx : f.base '' C.support = {x}) : IsClosed ({x} : Set X) := by
  rw [← hx]
  exact f.isClosedMap _ C.support.isClosed

/-- An exceptional curve of a proper morphism to a scheme locally of finite type over `k` is
proper over `k`. -/
private lemma isProper_subschemeι_comp_of_isExceptionalCurve {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {f : Y ⟶ X} [IsProper f]
    {C : Y.IdealSheafData} (hC : IsExceptionalCurve f C) : IsProper (C.subschemeι ≫ f ≫ sX) := by
  obtain ⟨hCc, x, hx⟩ := hC
  have : IsIntegral C.subscheme := hCc.1
  rw [← Category.assoc]
  refine isProper_comp_of_range_subset_singleton sX _ (isClosed_singleton_of_image_eq hx) ?_
  rintro _ ⟨z, rfl⟩
  exact apply_eq_of_image_eq hx (C.range_subschemeι ▸ ⟨z, rfl⟩)

/-! ### Exceptional curves as exceptional divisors -/

/-- An exceptional curve of a resolution of a normal surface is an exceptional divisor of the
resolution. -/
private theorem isExceptional_of_isExceptionalCurve {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {f : Y ⟶ X}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsSmoothResolution sX f) (F : PrimeDivisor Y)
    (hF : IsExceptionalCurve f F.idealSheaf) :
    RationalMap.IsExceptional (X := Y) f.toRationalMap F := by
  obtain ⟨hYv, -, -⟩ := hf.isNormalVariety hX
  have : IsProper f := hf.isProper
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ Limits.terminal Scheme) := by
    rw [show (X ↘ Limits.terminal Scheme) = sX ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : QuasiCompact (f ≫ sX) := hYv.1.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsIntegral Y := hf.isIntegral
  have : IsNoetherian Y := ⟨⟩
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight]
  obtain ⟨-, x, hx⟩ := hF
  intro y hy
  have hxcl := isClosed_singleton_of_image_eq hx
  have hy' : y ∈ closure (f.base '' (F.idealSheaf.support : Set Y)) := hy
  rw [hx, hxcl.closure_eq] at hy'
  rw [Set.mem_singleton_iff.mp hy']
  exact (MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hX.1 hdim hxcl).ge

/-! ### The inverse transform of the boundary -/

open Classical in
/-- The coefficient of `h⁻¹_* a` at a prime divisor `P` of `Y'`. -/
private theorem inverseTransformDivisor_apply {Y Y' : Scheme.{u}} (h : Y' ⟶ Y)
    (a : QDivisor Y) (P : PrimeDivisor Y') :
    inverseTransformDivisor h a P =
      ∑ E ∈ a.support, if inverseTransformPrimeDivisor h E = some P then a E else 0 := by
  classical
  conv_lhs => rw [← Finsupp.sum_single a]
  rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [inverseTransformDivisor_single]
  cases inverseTransformPrimeDivisor h E with
  | none => simp
  | some C => simp [Finsupp.single_apply]

/-- The inverse transform of an effective `ℚ`-divisor is effective. -/
private theorem isEffective_inverseTransformDivisor {Y Y' : Scheme.{u}} (h : Y' ⟶ Y)
    {a : QDivisor Y} (ha : a.IsEffective) : (inverseTransformDivisor h a).IsEffective := by
  classical
  intro P
  rw [DivisorWithCoeffs.coeff_apply, inverseTransformDivisor_apply]
  exact Finset.sum_nonneg fun E _ => ite_nonneg (ha E) le_rfl

/-- An exceptional curve of a resolution of a normal surface is not a component of the inverse
transform `f⁻¹_* Δ` of a `ℚ`-divisor. -/
private theorem notMem_support_inverseTransformDivisor {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {f : Y ⟶ X} [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsSmoothResolution sX f) (Δ : QDivisor X)
    {F : PrimeDivisor Y} (hF : IsExceptionalCurve f F.idealSheaf) :
    F ∉ (inverseTransformDivisor f Δ).support := by
  rw [Finsupp.notMem_support_iff, inverseTransformDivisor_apply]
  refine Finset.sum_eq_zero fun E _ => if_neg fun hs => ?_
  obtain ⟨hη, -⟩ :=
    MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hs
  obtain ⟨-, x, hx⟩ := hF
  have : IsProper f := hf.isProper
  have hmem : f F.genericPoint = x := apply_eq_of_image_eq hx <| by
    change F.genericPoint ∈ F.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have h2 := MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hX.1 hdim
    (isClosed_singleton_of_image_eq hx)
  rw [← hmem, hη, PrimeDivisor.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- On a resolution of a normal surface, `f⁻¹_* Δ` meets every exceptional curve nonnegatively,
for `Δ` effective. -/
private theorem exists_isIntersectionNumber_inverseTransformDivisor_nonneg {k : Type u}
    [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {f : Y ⟶ X}
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsSmoothResolution sX f) {Δ : QDivisor X} (hΔ : Δ.IsEffective)
    {F : PrimeDivisor Y} (hF : IsExceptionalCurve f F.idealSheaf) :
    ∃ n : ℚ, IsIntersectionNumber (f ≫ sX) (inverseTransformDivisor f Δ) F.idealSheaf n ∧
      0 ≤ n := by
  obtain ⟨hYn, hdimY, -⟩ := hf.isNormalVariety hX
  have : IsProper f := hf.isProper
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨n, hn, hn0, -⟩ := nonneg_intersectionNumber_of_notMem_support (f ≫ sX) hYn.1
    hf.isSmoothScheme (hdimY.trans hdim) F (isProper_subschemeι_comp_of_isExceptionalCurve sX hF)
    (isEffective_inverseTransformDivisor f hΔ)
    (notMem_support_inverseTransformDivisor hX hdim hf Δ hF)
  exact ⟨n, hn, hn0⟩

/-! ### The theorem -/

/-- **Minimal resolutions of canonical surface pairs are crepant** (KM, proof of Theorem 4.5).
Let `(x ∈ X)` be a surface germ over an algebraically closed field `k` of characteristic zero, `Δ`
an effective `ℚ`-divisor on `X` and `K_X` a canonical divisor such that `(X, Δ)` is canonical,
and let `f : Y ⟶ X` be a minimal resolution. Then every `f`-exceptional curve `E` has discrepancy
`a(E, X, Δ) = 0`. -/
@[mmp "lem_km4a_canonical_surface_minimal_resolution_crepant"]
public theorem IsCanonicalPair.isDiscrepancy_zero_of_isMinimalSurfaceResolution {k : Type u}
    [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {f : Y ⟶ X} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    {x : X} (hX : IsSurfaceGerm sX x) {Δ : QDivisor X} (hΔ : Δ.IsEffective)
    {KX : Divisor X} (hc : IsCanonicalPair sX 2 KX Δ)
    (hf : IsMinimalSurfaceResolution sX f)
    {E : PrimeDivisor Y} (hE : IsExceptionalCurve f E.idealSheaf) :
    IsDiscrepancy sX 2 KX Δ
      ⟨Y, f, (hf.1.isNormalVariety hX.1).1, hf.1.isBirationalMorphism, E⟩ 0 := by
  have hXv := hX.1
  have hdim := hX.2.1
  obtain ⟨hYn, hdimY, -⟩ := hf.1.isNormalVariety hXv
  haveI := hYn.1
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hf.1.isSmoothScheme
    (n := 2) (hdimY.trans hdim)
  obtain ⟨a, ha, -⟩ := existsUnique_isNumericalPullbackSolution sX f hXv hdim hf.1 KY hKY Δ
  have hle : a ≤ 0 := ha.nonpos hXv hdim fun Ej hEj b hb => by
    obtain ⟨n₁, h₁, h₁0⟩ := hf.exists_isIntersectionNumber_canonical_nonneg hXv hdim hKY hEj
    obtain ⟨n₂, h₂, h₂0⟩ :=
      exists_isIntersectionNumber_inverseTransformDivisor_nonneg hXv hdim hf.1 hΔ hEj
    have := (MMP.Flips.isIntersectionNumber_add h₁ h₂).unique hb
    linarith
  have hdisc := (isNumericalDiscrepancy_iff_isDiscrepancy hc.isPair hdim hc.1.2.1 hf.1 hKY hE
    (a E)).1 ⟨hE, a, ha, rfl⟩
  have hge : (0 : ℚ) ≤ a E := by
    exact_mod_cast EReal.coe_nonneg.mp <| hc.2.trans <|
      discrep_le (D := ⟨Y, f, hYn, hf.1.isBirationalMorphism, E⟩)
        (isExceptional_of_isExceptionalCurve hXv hdim hf.1 E hE) hdisc
  rwa [le_antisymm (Finsupp.le_def.mp hle E) hge] at hdisc

end MMP.Mori

end
