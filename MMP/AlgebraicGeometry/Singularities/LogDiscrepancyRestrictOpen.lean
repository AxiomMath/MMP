module
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal

/-!
# Log discrepancies are local at the centre

Let `(Y, B)` be a pair, `ξ` a normalized divisorial valuation of `k(Y)` with centre `c_Y(ξ)`, and
`U ⊆ Y` an open subset meeting `c_Y(ξ)`. Then the log discrepancy of `ξ`, regarded as a valuation
of `k(U) = k(Y)`, with respect to `(U, B|_U)` equals its log discrepancy with respect to `(Y, B)`.

A divisor `(W, g, E)` over `Y` realizing `ξ`, with `g` proper, has `g(η_E) ∈ U`, so it restricts
to the divisor `(g⁻¹U, g|_{g⁻¹U}, E ∩ g⁻¹U)` over `U`, with the same valuation and the same
discrepancy with respect to `(U, B|_U)` (`MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff`).
The log discrepancy is one plus the discrepancy, and it does not depend on the model realizing
the valuation (`MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq`).

## Main results

* `MMP.Fourfold.isValuationLogDiscrepancy_restrict_iff`: `a(ξ; U, B|_U) = a ↔ a(ξ; Y, B) = a`.

## Implementation notes

* The log discrepancy is the relation `MMP.Fourfold.IsValuationLogDiscrepancy`, so the equality
  `a(ξ; U, B|_U) = a(ξ; Y, B)` is stated as: a real number is one exactly when it is the other.
  Its canonical divisors are those of nonzero rational top forms, chosen existentially; forms on
  `Y` restrict to forms on `U`, which is the compatible choice of canonical divisors.
* The valuation of `k(U)` is the `ξ_U` with `ξ_U ∘ ι^* = ξ`, for `ι^* : k(Y) → k(U)` the
  isomorphism of function fields induced by the open immersion `ι : U ⟶ Y`.
* `B|_U` is the inverse transform `MMP.Mori.inverseTransformDivisor` of `B` along `ι`, whose prime
  divisors are the `P ∩ U`. It agrees with the restriction
  `MMP.Mori.DivisorWithCoeffs.restrictOpen`, because `U` lies in the biregular locus of the
  inclusion.
-/

public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- An open immersion `U ⟶ X` restricted to its image is an isomorphism, so the open `U` is
contained in the biregular locus of `U.ι`. -/
private theorem isIso_ι_restrict_self {X : Scheme.{u}} (U : X.Opens) : IsIso (U.ι ∣_ U) := by
  have : Surjective (U.ι ∣_ U) := by
    refine ⟨fun y => ?_⟩
    let x : (U.ι ⁻¹ᵁ U).toScheme := ⟨y, by simp⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    have := Scheme.Hom.comp_apply (U.ι ∣_ U) U.ι x
    rw [morphismRestrict_ι] at this
    exact this.symm
  exact isIso_of_mono_of_strongEpi (U.ι ∣_ U)

/-- The inverse transform of a divisor along the inclusion of an open subscheme is its
restriction. -/
private theorem inverseTransformDivisor_ι_eq_restrictOpen {X : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] (U : X.Opens) (B : DivisorWithCoeffs R X) :
    inverseTransformDivisor U.ι B = B.restrictOpen U := by
  have hbir : ∀ x : U.toScheme, U.ι x ∈ biregularLocus U.ι := fun x =>
    le_biregularLocus (isIso_ι_restrict_self U)
      (by rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩)
  refine Finsupp.ext fun W => ?_
  refine (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (E := OpenWeilRestriction.primeDivisorMap U.ι W)
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι W).symm (hbir _))
    (fun E' hE' => ?_) B).trans rfl
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE').1]

/-- Pulling valuations back along the inclusion of a nonempty open subscheme is injective:
`k(U) = k(X)`. -/
private theorem comap_functionFieldMap_injective {X : Scheme.{u}} [IsIntegral X]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (U : X.Opens) [Nonempty U] :
    haveI := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
    Function.Injective (Valuation.comap (Γ₀ := Γ₀) (functionFieldMap U.ι)) := by
  haveI := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
  have hsurj := (functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤
    ⟨_, Set.mem_univ (Classical.arbitrary U)⟩).2
  intro v w hvw
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  exact congrArg (fun v => v y) hvw

/-- If `U` meets the centre `Z` of `ξ`, then every divisor over `Y` realizing `ξ` has the image
of its generic point in `U`. -/
private theorem genericPoint_mem_of_valuation_eq (hX : IsNormalVariety k sY)
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))} {Z : IrreducibleCloseds Y}
    (hZ : MMP.Intersection.IsCentre k sY ξ Z) {U : Y.Opens} (hUZ : ((U : Set Y) ∩ Z).Nonempty)
    (D : DivisorOver k sY) (hD : D.valuation = ξ) : D.f D.E.genericPoint ∈ U := by
  obtain ⟨D₀, -, hv₀, rfl⟩ := hZ
  have hc := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX (hD.trans hv₀)
  obtain ⟨y, hyU, hyZ⟩ := hUZ
  rw [D₀.center_eq_closure_genericPoint, ← hc] at hyZ
  exact (specializes_iff_mem_closure.mpr hyZ).mem_open U.isOpen hyU

/-- A normalized divisorial valuation has a log discrepancy with respect to a pair. -/
private theorem exists_isLogDiscrepancy_of_isNormalizedDivisorialValuation [PerfectField k]
    {B : QDivisor Y} (hB : MMP.Mori.IsPair sY B)
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    (hξ : MMP.Intersection.IsNormalizedDivisorialValuation k sY ξ) :
    ∃ (n : ℕ) (D : DivisorOver k sY) (b : ℝ), D.valuation = ξ ∧
      MMP.Intersection.IsLogDiscrepancy sY n (QDivisor.toRDivisor B) D b := by
  obtain ⟨D, hp, rfl⟩ := hξ
  obtain ⟨n, K, hK, -⟩ := hB.2
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB hK D
  exact ⟨n, D, _, rfl, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hp⟩

/-- **Restriction of a log discrepancy to an open subset.** A divisor `(W, g, E)` over `Y`, with
`g` proper and `g(η_E) ∈ U`, restricts to a divisor over `U` with the corresponding valuation and
the same log discrepancy with respect to `(U, B|_U)`. -/
private theorem exists_isLogDiscrepancy_restrict [PerfectField k] {B : QDivisor Y}
    (hB : MMP.Mori.IsPair sY B) (U : Y.Opens) [Nonempty U] {n : ℕ} {D : DivisorOver k sY}
    {a : ℝ} (hD : MMP.Intersection.IsLogDiscrepancy sY n (QDivisor.toRDivisor B) D a)
    (hDU : D.f D.E.genericPoint ∈ U) :
    haveI := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
    ∃ D' : DivisorOver k (U.ι ≫ sY), IsProper D'.f ∧
      D'.valuation.comap (functionFieldMap U.ι) = D.valuation ∧
      MMP.Intersection.IsLogDiscrepancy (U.ι ≫ sY) n
        (QDivisor.toRDivisor (inverseTransformDivisor U.ι B)) D' a := by
  haveI := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
  obtain ⟨hX, n₀, K, hK, hQ⟩ := hB
  obtain rfl : n₀ = n := by
    exact_mod_cast hK.topologicalKrullDim_eq.symm.trans
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hD)
  have hP : MMP.Mori.IsPairWith sY n₀ K B := ⟨hX, hK, hQ⟩
  have hc : ((D.center : Set Y) ∩ U).Nonempty :=
    ⟨_, by rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl, hDU⟩
  obtain ⟨hY, hf, E', -, hv, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hP D U hc
  obtain ⟨c, hc₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hK D
  have hp : IsProper D.f := hD.2.1
  have hpU : IsProper (D.f ∣_ U) := inferInstance
  refine ⟨⟨_, D.f ∣_ U, hY, hf, E'⟩, hpU, hv.symm, ?_⟩
  have hab : a = 1 + (c : ℝ) := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc₀ hp) rfl
  rw [hab, inverseTransformDivisor_ι_eq_restrictOpen]
  exact MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ((hiff c).1 hc₀) hpU

/-- **Log discrepancies are local at the centre.** Let `(Y, B)` be a pair, `ξ` a normalized
divisorial valuation of `k(Y)` with centre `Z`, and `U ⊆ Y` an open subset meeting `Z`. If `ξ_U`
is the valuation of `k(U)` corresponding to `ξ`, then `a` is the log discrepancy of `ξ_U` with
respect to `(U, B|_U)` if and only if it is the log discrepancy of `ξ` with respect to `(Y, B)`. -/
@[mmp "lem_mmp_indexd_log_discrepancy_local"]
public theorem isValuationLogDiscrepancy_restrict_iff {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor Y} (hB : IsPair sY B)
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    (hξ : MMP.Intersection.IsNormalizedDivisorialValuation k sY ξ)
    {Z : IrreducibleCloseds Y} (hZ : MMP.Intersection.IsCentre k sY ξ Z)
    (U : Y.Opens) [Nonempty U] (hUZ : ((U : Set Y) ∩ Z).Nonempty)
    {ξU : Valuation U.toScheme.functionField (WithZero (Multiplicative ℤ))}
    (hξU : haveI := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
      ξU.comap (functionFieldMap U.ι) = ξ) (a : ℝ) :
    IsValuationLogDiscrepancy (U.ι ≫ sY) (inverseTransformDivisor U.ι B) ξU a ↔
      IsValuationLogDiscrepancy sY B ξ a := by
  haveI := hB.isAlgClosed
  haveI := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
  have hinj := comap_functionFieldMap_injective (Γ₀ := WithZero (Multiplicative ℤ)) U
  have hmem := genericPoint_mem_of_valuation_eq hB.isPair.1 hZ hUZ
  constructor
  · rintro ⟨n', D', -, hv', hl'⟩
    obtain ⟨n, D, b, hv, hl⟩ :=
      exists_isLogDiscrepancy_of_isNormalizedDivisorialValuation hB.isPair hξ
    obtain ⟨D'', -, hv'', hl''⟩ := exists_isLogDiscrepancy_restrict hB.isPair U hl (hmem D hv)
    have hab : b = a := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hl'' hl'
      (hinj (hv''.trans (hv.trans (hξU.symm.trans (congrArg _ hv'.symm)))))
    exact ⟨n, D, hl.2.1, hv, hab ▸ hl⟩
  · rintro ⟨n, D, -, hv, hl⟩
    obtain ⟨D', hp', hv', hl'⟩ := exists_isLogDiscrepancy_restrict hB.isPair U hl (hmem D hv)
    exact ⟨n, D', hp', hinj (hv'.trans (hv.trans hξU.symm)), hl'⟩

end MMP.Fourfold

end
