module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltRelativeConeTheorem
import MMP.AlgebraicGeometry.MMP.Contraction.DltRelativeContractionExists
import MMP.AlgebraicGeometry.MMP.Contraction.DltContractionQFactorial
import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialContractionDlt
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.LowerDimDltModel
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.SurfaceBirationalSimplicial
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
import MMP.AlgebraicGeometry.Divisor.ExceptionalNullDivisor
import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition

/-!
# Crepant dlt modifications of projective lc surfaces

Let `(X, B)` be a log canonical pair with rational boundary (`MMP.Intersection.IsLogCanonicalPair`)
on a normal projective complex surface `X`. Then there is a projective birational morphism
`q : Y ⟶ X` from a projective `ℚ`-factorial surface `Y` and an effective rational dlt boundary
`Δ` on `Y` (`MMP.Intersection.IsDltPair`) with `K_Y + Δ = q^*(K_X + B)`, such that every
`q`-exceptional prime divisor `E` of `Y` has log discrepancy `a(E; X, B) = 0`, hence coefficient
one in `Δ`.

The proof starts from a log resolution `W → X` with boundary the strict transform of `B` plus the
reduced exceptional divisor, and runs the dlt surface program over `X`. Every step is divisorial
and contracts an exceptional curve with positive coefficient in the crepant remainder `F`; the
negativity of the exceptional intersection form forces `F = 0` at the end. No flip occurs.

## Main results

* `MMP.Threefold.exists_crepant_dltModification_of_surface`: the modification.

## Implementation notes

* `K_Y + Δ = q^*(K_X + B)` is `MMP.Mori.IsCrepantBoundary`, asserted for every canonical
  divisor `K_X` of dimension `2`. Effectivity of `Δ` is part of `MMP.Intersection.IsDltPair`.
* A `q`-exceptional prime divisor of `Y` is one that `q` contracts
  (`MMP.Mori.RationalMap.IsExceptional`); its log discrepancy is that of the divisor `(Y, q, E)`
  over `X`. These are exactly the exceptional primes of the log resolution with log discrepancy
  zero that the program never contracts.

## References

* [OAI4] *A crepant dlt modification of a projective lc surface*.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Threefold

universe u

/-! ### Intersection numbers and crepant pull-backs -/

section Crepancy

/-- `X ⟶ ⊤_ Scheme` is separated when `X` is separated over a field. -/
private theorem isSeparated_terminal_from {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ Limits.terminal Scheme) := by
  rw [show (X ↘ Limits.terminal Scheme) = sX ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

variable {k : Type u} [Field k] [PerfectField k] {X U : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace U] [IsLocallyNoetherian U]
    [IsNormal U] in
/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX)
    {p : U ⟶ X} [IsDominant p] (hp : IsBirationalMorphism p) {n : ℕ}
    (hn : topologicalKrullDim X = n) {m : ℤ} {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX p τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := hp.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX p hbij hd
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  have hpull : pullbackRationalPluriForms sX p τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField U.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

end Crepancy

/-- The divisors of two nonzero rational top forms on a normal variety are linearly
equivalent. -/
private theorem linearlyEquivalent_divisorOfForm {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ ω : RationalPluriForms sX n 1} (hτ : τ ≠ 0)
    (hω : ω ≠ 0) : Divisor.LinearlyEquivalent (divisorOfForm τ) (divisorOfForm ω) := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hX hn
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  set e := (ZTensorPower.basis b 1).repr τ () with he_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω
  have he : e ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero he (inv_ne_zero hc))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 ω hω
  have e2 := hN 1 τ hτ
  rw [← hc_def] at e1
  rw [← he_def] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ,
    Scheme.ord_mul he (inv_ne_zero hc), ← zpow_neg_one, ord_zpow _ hc, coeff_divisorOfForm,
    coeff_divisorOfForm, e1, e2]
  ring

/-- **`(K_Y + Δ) · C = 0` on contracted curves.** If `Δ` is the crepant boundary of `(X, B)` on a
proper birational `q : Y ⟶ X`, then `K_Y + Δ` has degree zero on every curve contracted by `q`,
for every canonical divisor `K_Y`. -/
private theorem intersectionNumber_eq_zero_of_isCrepantBoundary {k : Type u} [Field k]
    [PerfectField k] {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} (hKB : (Divisor.toQDivisor K + B).IsQCartier)
    {q : Y ⟶ X} (hY : IsNormalVariety k (q ≫ sX)) (hq : IsBirationalMorphism q)
    {Δ : QDivisor Y} (hΔ : IsCrepantBoundary sX n K B q hY hq Δ) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor (q ≫ sX) n) [QuasiCompact (q ≫ sX)]
    (hQ : (Divisor.toQDivisor KY + Δ).IsQCartier) (C : ProperCurve (q ≫ sX))
    (hC : C.IsContractedBy q) :
    (Divisor.toQDivisor KY + Δ).intersectionNumber k (q ≫ sX) C.ι C.dim_le hQ = 0 := by
  have : IsDominant q := hq.isDominant
  have : LocallyOfFiniteType (q ≫ sX) := hY.1.toLocallyOfFiniteType
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : AlgebraicGeometry.IsVariety k (q ≫ sX) := hY.1
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hLB : ∀ W : irreducibleComponents Y, q (componentGenericPoint Y W) ∉
      (Divisor.toQDivisor K + B).supp := fun W => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp _
  have hpb := MMP.Mori.IsCrepantBoundary.isPullback_divisorOfForm_add hX hY hq hK hΔ hω0 hωK hLB
  have hA := hpb.isQCartier hKB
  have hcurve := C.isCurve
  have hpt : ∃ w : X, Set.range (C.ι ≫ q) = {w} := by
    refine ⟨q C.point, ?_⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, C.range_ι]
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨C.point, subset_closure rfl, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hC x hx
  have h0 := intersectionNumber_pullback_eq_zero k (q ≫ sX) sX q rfl C.ι hKB hpb hpt
  obtain ⟨σ, hσ0, hσK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hY hKY
  have hKYσ : KY = divisorOfForm σ := by
    ext Γ
    rw [coeff_divisorOfForm, hσK]
  have hnY : topologicalKrullDim Y = n := hKY.topologicalKrullDim_eq
  have hlin : KY.LinearlyEquivalent (divisorOfForm (pullbackRationalPluriForms sX q ω)) := by
    rw [hKYσ]
    exact linearlyEquivalent_divisorOfForm hY hnY hσ0
      (pullbackRationalPluriForms_ne_zero hX hq hK.topologicalKrullDim_eq hω0)
  rw [MMP.Mori.QDivisor.intersectionNumber_add_eq_of_linearlyEquivalent (q ≫ sX) C.ι C.dim_le hlin
    Δ hQ hA]
  exact h0

/-- An exceptional prime divisor of a morphism `q` to a separated scheme does not lie over a prime
divisor of the target. -/
private theorem map_genericPoint_ne_of_isExceptional {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of k)} [IsSeparated sX] {q : Y ⟶ X} {E : MMP.Mori.PrimeDivisor Y}
    (hE : RationalMap.IsExceptional (X := Y) q.toRationalMap E) (Q : MMP.Mori.PrimeDivisor X) :
    q E.genericPoint ≠ Q.genericPoint := by
  intro h
  have := isSeparated_terminal_from sX
  rw [MMP.Positivity.isExceptional_toRationalMap_iff] at hE
  have hmem : Q.genericPoint ∈
      (Closeds.closure (q '' (E.idealSheaf.support : Set Y)) : Set X) := by
    rw [Closeds.coe_closure]
    refine subset_closure ⟨E.genericPoint, ?_, h⟩
    change E.genericPoint ∈ E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hE _ hmem
  rw [Q.coheight_genericPoint] at this
  norm_num at this

/-! ### The log resolution -/

section LogResolution

/-- A birational morphism `μ : Y ⟶ X` from an integral Noetherian scheme has an exceptional
divisor `Exc(μ)_red`: only finitely many prime divisors of `Y` lie in the exceptional locus, a
proper closed subset, each being one of its irreducible components. -/
private theorem exists_isExceptionalDivisorSum {Y X : Scheme.{0}} [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] {μ : Y ⟶ X} (hμ : IsBirationalMorphism μ) :
    ∃ E : Divisor Y, MMP.Intersection.IsExceptionalDivisorSum μ E := by
  classical
  have : AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  obtain ⟨e, he⟩ := hμ
  obtain ⟨W, hW, hWe, hWr, hWeq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
  have hWe' : W ≤ e.source := hWe
  have hWι : IsOpenImmersion (W.ι ≫ μ) := by
    have h : W.ι ≫ μ = Y.homOfLE hWe' ≫ e.iso.hom ≫ e.target.ι := by
      have h := hWeq.symm
      simp only [Scheme.PartialMap.restrict_hom, Scheme.Hom.toPartialMap_hom] at h
      rw [Scheme.topIso_hom] at h
      change Y.homOfLE (le_top : W ≤ ⊤) ≫ (⊤ : Y.Opens).ι ≫ μ =
        Y.homOfLE hWe' ≫ e.iso.hom ≫ e.target.ι at h
      rw [← Category.assoc, Scheme.homOfLE_ι] at h
      exact h
    rw [h]; infer_instance
  have hη : genericPoint Y ∈ W :=
    ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr (by
      obtain ⟨y, hy⟩ := hW.nonempty; exact ⟨y, trivial, hy⟩)
  have hsub : ∀ P : MMP.Mori.PrimeDivisor Y,
      P.support ⊆ MMP.Intersection.exceptionalLocus μ → P.genericPoint ∉ W := by
    intro P hP hmem
    exact MMP.Intersection.mem_exceptionalLocus_iff.mp
      (hP (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl))
      W hmem hWι
  have hfin : {P : MMP.Mori.PrimeDivisor Y |
      P.support ⊆ MMP.Intersection.exceptionalLocus μ}.Finite := by
    refine Set.Finite.of_finite_image
      ((MMP.Mori.finite_coheight_eq_one_mem_closure_notMem (genericPoint Y) W hη).subset ?_)
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
    rintro - ⟨P, hP, rfl⟩
    exact ⟨by rw [(genericPoint_spec Y).def]; trivial, hsub P hP, P.coheight_genericPoint⟩
  refine ⟨Finsupp.ofSupportFinite
    (fun P => if P.support ⊆ MMP.Intersection.exceptionalLocus μ then (1 : ℤ) else 0)
    (hfin.subset fun P hP => by by_contra h; exact hP (if_neg h)), fun P => ?_⟩
  rfl

/-- A projective complex normal variety `S`, with a `ℚ`-divisor `B`,
has a projective log resolution `p : Y ⟶ S` of `(S, B)` with `Y` a projective `ℚ`-factorial
normal variety of the dimension of `S`. -/
private theorem exists_projective_log_resolution
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hX : IsNormalVariety ℂ sS) (B : QDivisor S) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : CompactSpace Y) (_ : IsLocallyNoetherian Y)
      (_ : IsNormal Y) (p : Y ⟶ S),
      IsLogResolution sS (QDivisor.toRDivisor B) p ∧ IsProjectiveMorphism p ∧
      IsNormalVariety ℂ (p ≫ sS) ∧ MMP.Mori.IsProjectiveVariety ℂ (p ≫ sS) ∧
      topologicalKrullDim Y = topologicalKrullDim S ∧ IsQFactorial (p ≫ sS) := by
  obtain ⟨Y, p, hlog, hproj⟩ :=
    MMP.Mori.exists_isLogResolution_isProjectiveMorphism sS hX (QDivisor.toRDivisor B)
  obtain ⟨hW, hdimW, -⟩ := hlog.toIsSmoothResolution.isNormalVariety hX
  haveI : IsIntegral Y := hW.1.toIsIntegral
  haveI : LocallyOfFiniteType (p ≫ sS) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sS)
  haveI : IsNormal Y := hW.2
  haveI : AlgebraicGeometry.IsVariety ℂ (p ≫ sS) := hW.1
  haveI : AlgebraicGeometry.IsVariety ℂ sS := hS.toIsVariety
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (p ≫ sS)
  refine ⟨Y, inferInstance, inferInstance, inferInstance, inferInstance, p, hlog, hproj, hW,
    ⟨hproj.comp hS.isProjective⟩, hdimW, hW, fun D => ⟨1, one_pos, ?_⟩⟩
  simpa using MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hlog.isSmoothScheme D

open MMP.Threefold.Mori.OpenRestriction in
/-- The restriction of an snc divisor to an open subscheme is snc. -/
private theorem isSNC_restrictOpen {R : Type*} [Zero R] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ E : MMP.Mori.PrimeDivisor X, LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ g)]
    {D : DivisorWithCoeffs R X} (hD : D.IsSNC g) (U : X.Opens) :
    (D.restrictOpen U).IsSNC (U.ι ≫ g) := by
  refine ⟨fun E₀ hE₀ => ?_, fun x => (sncStalk_restrict_iff U.ι D x).mpr (hD.2 (U.ι x))⟩
  have hsm := hD.1 (OpenWeilRestriction.primeDivisorMap U.ι E₀)
    (Finsupp.mem_support_iff.2 (Finsupp.mem_support_iff.1 hE₀ : D.restrictOpen U E₀ ≠ 0))
  rw [IsSmoothScheme, smoothLocus_eq_smoothLocus] at hsm
  exact (isSmoothScheme_comap_iff U.ι g (OpenWeilRestriction.primeDivisorMap U.ι E₀).idealSheaf
    E₀.idealSheaf (idealSheaf_comap_primeDivisorMap U.ι E₀)).mpr fun z _ => hsm ▸ trivial

/-- A divisor on the source of a log resolution of `(S, D)` all of whose components lie in
`Ex(p) ∪ p⁻¹(Supp D)` is snc. -/
private theorem isSNC_of_isLogResolution {k : Type u} [Field k] {S Y : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} {D : RDivisor S} {p : Y ⟶ S} (hlog : IsLogResolution sS D p)
    [LocallyOfFinitePresentation (p ≫ sS)] {R : Type*} [Zero R] (Γ : DivisorWithCoeffs R Y)
    (hΓ : ∀ P ∈ Γ.support,
      P.support ⊆ ((exceptionalSet p ⊔ D.supp.preimage p.continuous : Closeds Y) : Set Y)) :
    Γ.IsSNC (p ≫ sS) := by
  classical
  have hη : ∀ P : MMP.Mori.PrimeDivisor Y, P.genericPoint ∈ P.support := fun P => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  rcases hlog.isSNCSubset with h | ⟨s, hs, hsnc⟩
  · refine (DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := R) (p ≫ sS)
      hlog.isSmoothScheme).of_support_subset fun P hP => ?_
    have := hΓ P hP (hη P)
    simp [h] at this
  · refine hsnc.of_support_subset fun P hP => ?_
    have hP' := hΓ P hP (hη P)
    rw [← hs] at hP'
    obtain ⟨E, hE, hPE⟩ := Set.mem_iUnion₂.mp hP'
    have hEP := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hPE
    subst hEP
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, hE]

end LogResolution

/-! ### Contractions of surfaces -/

section Contraction

/-- The target of a proper morphism `ψ` from a normal integral scheme which induces isomorphisms
`Γ(Z, U) ≅ Γ(Y, ψ⁻¹ U)` is a normal integral scheme, onto which `ψ` is surjective. -/
private theorem surjective_isIntegral_isNormal_of_isIso_app {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsNormal Y] (ψ : Y ⟶ Z) [IsProper ψ] (h : ∀ U : Z.Opens, IsIso (ψ.app U)) :
    Function.Surjective ψ ∧ IsIntegral Z ∧ IsNormal Z := by
  have hne : ∀ U : Z.Opens, (U : Set Z).Nonempty → ((ψ ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
    intro U hU
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    have hbot : ψ ⁻¹ᵁ U = ⊥ := SetLike.coe_injective (by simpa using hc)
    haveI : Nonempty U := hU.to_subtype
    have e := (asIso (ψ.app U)).commRingCatIsoToRingEquiv
    have hsub : Subsingleton Γ(Y, ψ ⁻¹ᵁ U) := by rw [hbot]; infer_instance
    exact not_subsingleton Γ(Z, U) e.injective.subsingleton
  have hsurj : Function.Surjective ψ := by
    have hd : DenseRange ψ := by
      refine dense_iff_inter_open.mpr fun U hU hUne => ?_
      obtain ⟨y, hy⟩ := hne ⟨U, hU⟩ hUne
      exact ⟨ψ y, hy, y, rfl⟩
    have hc : IsClosed (Set.range ψ) := ψ.isClosedMap.isClosed_range
    intro z
    have : z ∈ closure (Set.range ψ) := by rw [hd.closure_range]; trivial
    rw [hc.closure_eq] at this
    exact this
  have hirr : IrreducibleSpace Z := by
    rw [irreducibleSpace_def]
    have := (IrreducibleSpace.isIrreducible_univ Y).image ψ ψ.continuous.continuousOn
    rwa [Set.image_univ_of_surjective hsurj] at this
  have hred : IsReduced Z := ⟨fun U => isReduced_of_injective (ψ.app U).hom
    (ConcreteCategory.bijective_of_isIso (ψ.app U)).1⟩
  haveI := hirr
  haveI := hred
  haveI : IsIntegral Z := isIntegral_of_irreducibleSpace_of_isReduced Z
  refine ⟨hsurj, inferInstance, ?_⟩
  rw [isNormal_iff_forall_affineOpen_normal]
  intro U hU
  haveI : Nonempty (ψ ⁻¹ᵁ U.1) :=
    (hne U.1 (by obtain ⟨x⟩ := hU; exact ⟨x.1, x.2⟩)).to_subtype
  have h1 : IsIntegrallyClosed Γ((ψ ⁻¹ᵁ U.1).toScheme, ⊤) := normal_globalSections _
  have h2 : IsIntegrallyClosed Γ(Y, ψ ⁻¹ᵁ U.1) :=
    h1.of_equiv (Scheme.Opens.topIso (ψ ⁻¹ᵁ U.1)).commRingCatIsoToRingEquiv
  exact h2.of_equiv (asIso (ψ.app U.1)).commRingCatIsoToRingEquiv.symm

/-- The closure of the generic point of a proper curve is one-dimensional. -/
private theorem topologicalKrullDim_closure_point {k : Type u} [Field k] {S : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} (C : ProperCurve sS) :
    topologicalKrullDim (closure {C.point} : Set S) = 1 := by
  have := C.dim_eq
  rwa [MMP.Mori.topologicalKrullDim_subscheme_eq,
    Scheme.IdealSheafData.coe_support_vanishingIdeal] at this

/-- The generic point of a proper curve is not a closed point. -/
private theorem not_isClosed_of_properCurve {k : Type u} [Field k] {S : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} (C : ProperCurve sS) : ¬ IsClosed ({C.point} : Set S) := by
  intro h
  have hcl := topologicalKrullDim_closure_point C
  rw [h.closure_eq] at hcl
  have : topologicalKrullDim ({C.point} : Set S) ≤ 0 :=
    topologicalKrullDim_zero_of_discreteTopology _
  rw [hcl] at this
  exact absurd this (by decide)

/-- On an integral surface the generic point of a proper curve is not the generic point. -/
private theorem point_ne_genericPoint {k : Type u} [Field k] {S : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} [IsIntegral S] (hdim : topologicalKrullDim S = 2)
    (C : ProperCurve sS) : C.point ≠ genericPoint S := by
  intro h
  have hcl := topologicalKrullDim_closure_point C
  rw [h, (genericPoint_spec S).def,
    (Homeomorph.Set.univ S).isHomeomorph.topologicalKrullDim_eq, hdim] at hcl
  exact absurd hcl (by decide)

/-- On an integral surface the generic point of a proper curve has coheight one. -/
private theorem coheight_point_eq_one {k : Type u} [Field k] {S : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} [IsIntegral S] [CompactSpace S]
    (hdim : topologicalKrullDim S = 2) (C : ProperCurve sS) : Order.coheight C.point = 1 := by
  have hK : Order.krullDim S = 2 := by
    rw [← hdim]; exact (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := S))).symm
  have hnc := not_isClosed_of_properCurve C
  have hη := point_ne_genericPoint hdim C
  obtain ⟨z, -, hxz, hne⟩ := MMP.Mori.exists_isClosed_singleton_specializes hnc
  have hzx : z < C.point := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hxz) fun h =>
    hne (hxz.antisymm (Scheme.le_iff_specializes.1 h)).eq
  have hηx : genericPoint S ⤳ C.point := (genericPoint_spec S).specializes trivial
  have hxη : C.point < genericPoint S := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hηx)
    fun h => hη (hηx.antisymm (Scheme.le_iff_specializes.1 h)).eq.symm
  have h1 := Order.height_add_one_le hzx
  have h2 := Order.coheight_add_one_le hxη
  have h3 : Order.height C.point + Order.coheight C.point ≤ 2 := by
    have := Order.height_add_coheight_le_krullDim C.point
    rw [hK] at this
    have h2 : ((Order.height C.point + Order.coheight C.point : ℕ∞) : WithBot ℕ∞) ≤
        ((2 : ℕ∞) : WithBot ℕ∞) := by
      push_cast; exact this
    exact WithBot.coe_le_coe.mp h2
  generalize Order.height C.point = a at h1 h3
  generalize Order.coheight C.point = b at h2 h3 ⊢
  have ha : 1 ≤ a := le_trans le_add_self h1
  have hb : 1 ≤ b := le_trans le_add_self h2
  induction a using ENat.recTopCoe with
  | top => simp at h3
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp at h3
    | coe b =>
      norm_cast at ha hb h3 ⊢
      omega

/-- On an integral proper surface, a point which is neither closed nor the generic point is the
generic point of a proper curve. -/
private theorem isProperCurve_of_not_isClosed {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y] (sY : Y ⟶ Spec (.of k)) [IsProper sY]
    (hdim : topologicalKrullDim Y = 2) {w : Y} (hw : ¬ IsClosed ({w} : Set Y))
    (hwη : w ≠ genericPoint Y) : IsProperCurve sY w := by
  have : AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  refine isProperCurve_of_isProper sY ?_
  rw [MMP.Mori.topologicalKrullDim_subscheme_eq, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  obtain ⟨c, -, hwc, hne⟩ := MMP.Mori.exists_isClosed_singleton_specializes hw
  refine MMP.Mori.topologicalKrullDim_eq_one_of_ne_univ hdim.le isClosed_closure ?_
    (subset_closure rfl) (specializes_iff_mem_closure.mp hwc) hwc hne
  intro h
  exact hwη ((show IsGenericPoint w Set.univ from h).eq (genericPoint_spec Y))

/-- A morphism restricting to an isomorphism over `V` is injective on the preimage of `V`. -/
private theorem eq_of_isIso_morphismRestrict {X Y : Scheme.{u}} (g : X ⟶ Y) (V : Y.Opens)
    [IsIso (g ∣_ V)] {a b : X} (ha : g a ∈ V) (h : g a = g b) : a = b := by
  have hb : g b ∈ V := h ▸ ha
  have hopen : IsOpenImmersion ((g ⁻¹ᵁ V).ι ≫ g) := by
    rw [← morphismRestrict_ι]; infer_instance
  have := ((g ⁻¹ᵁ V).ι ≫ g).isOpenEmbedding.injective
    (a₁ := (⟨a, ha⟩ : g ⁻¹ᵁ V)) (a₂ := ⟨b, hb⟩) h
  exact congrArg Subtype.val this

/-- **The exceptional set of the contraction of one curve.** Let `ψ : Y ⟶ Z` be a proper
birational morphism from an integral proper surface onto a normal integral scheme, with connected
fibres, contracting exactly one proper curve `C`. Then `Ex(ψ)` is the support of the prime divisor
whose generic point is that of `C`. -/
private theorem exceptionalSet_eq_support {k : Type u} [Field k] {Y Z : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y] [IsIntegral Z] [IsNormal Z]
    [IsLocallyNoetherian Z] (sY : Y ⟶ Spec (.of k)) [IsProper sY]
    (hdim : topologicalKrullDim Y = 2) (hZ : ¬ IsClosed ({genericPoint Z} : Set Z))
    (ψ : Y ⟶ Z) [IsProper ψ] (hψ : IsBirational ψ)
    (hconn : ∀ z : Z, _root_.IsConnected (ψ ⁻¹' {z}))
    (C : ProperCurve sY) (hψC : C.IsContractedBy ψ)
    (honly : ∀ D : ProperCurve sY, D.IsContractedBy ψ → D = C)
    (E : MMP.Mori.PrimeDivisor Y) (hE : E.genericPoint = C.point) :
    (exceptionalSet ψ : Set Y) = E.support := by
  classical
  have : AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  have hEsupp : (E.support : Set Y) = closure {C.point} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact congrArg (fun x => closure ({x} : Set Y)) hE
  have hEcl : IsClosed (E.support : Set Y) := hEsupp ▸ isClosed_closure
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso ψ hψ).1
    inferInstance
  have hFF : (⟨_, hU⟩ : Z.Opens) ≤ biregularLocus ψ := le_biregularLocus hiso
  obtain ⟨-, hScl⟩ := MMP.Mori.finite_and_isClosed_singleton_compl_finiteFibreLocus ψ hψ hdim.le
  have hgen : ∀ w : Y, ψ w ∉ MMP.Resolution.Bridges.finiteFibreLocus ψ →
      ¬ IsClosed ({w} : Set Y) → w = C.point := by
    intro w hw hwc
    have hz := hScl (ψ w) hw
    have hF : IsClosed (ψ ⁻¹' {ψ w}) := hz.preimage ψ.continuous
    have hsub : closure {w} ⊆ ψ ⁻¹' {ψ w} :=
      closure_minimal (Set.singleton_subset_iff.mpr rfl) hF
    have hwη : w ≠ genericPoint Y := by
      rintro rfl
      apply hZ
      rwa [MMP.Mori.map_genericPoint_eq ψ hψ] at hz
    let D : ProperCurve sY := ⟨w, isProperCurve_of_not_isClosed sY hdim hwc hwη⟩
    have hD : D.IsContractedBy ψ := fun x hx => hsub hx
    exact congrArg ProperCurve.point (honly D hD)
  ext y
  constructor
  · intro hy
    have hy' : ψ y ∉ MMP.Resolution.Bridges.finiteFibreLocus ψ := fun h => hy (hFF h)
    set F := ψ ⁻¹' {ψ y}
    have hFc : IsClosed F := (hScl (ψ y) hy').preimage ψ.continuous
    obtain ⟨Zs, hZf, hZc, hZirr, hZeq⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hFc
    have hgW : ∀ W ∈ Zs, ∃ x : Y, IsGenericPoint x W := fun W hW =>
      QuasiSober.sober (hZirr W hW) (hZc W hW)
    choose! gen hgen' using hgW
    set v : Set Y := gen '' Zs
    set v' : Set Y := {x ∈ v | x ∉ (E.support : Set Y)}
    have hv'fin : v'.Finite := (hZf.image gen).subset fun x hx => hx.1
    have hv'cl : ∀ x ∈ v', IsClosed ({x} : Set Y) := by
      rintro x ⟨⟨W, hW, rfl⟩, hxE⟩
      by_contra hcl
      have hmem : gen W ∈ F := by
        rw [hZeq]; exact ⟨W, hW, (hgen' W hW).mem⟩
      have := hgen (gen W) (by simpa [F] using hmem ▸ hy') hcl
      apply hxE
      rw [hEsupp, this]
      exact subset_closure rfl
    have hv'c : IsClosed v' := by
      rw [← Set.biUnion_of_singleton v']
      exact hv'fin.isClosed_biUnion fun x hx => hv'cl x hx
    have hFsub : F ⊆ (E.support : Set Y) ∪ v' := by
      intro x hx
      rw [hZeq] at hx
      obtain ⟨W, hW, hxW⟩ := hx
      by_cases hcl : IsClosed ({gen W} : Set Y)
      · have hWeq : W = {gen W} := by
          have := (hgen' W hW).def
          rw [hcl.closure_eq] at this
          exact this.symm
        rw [hWeq] at hxW
        rw [Set.mem_singleton_iff.mp hxW]
        by_cases hxE : gen W ∈ (E.support : Set Y)
        · exact Or.inl hxE
        · exact Or.inr ⟨⟨W, hW, rfl⟩, hxE⟩
      · have hmem : gen W ∈ F := by rw [hZeq]; exact ⟨W, hW, (hgen' W hW).mem⟩
        have hF' : ψ (gen W) = ψ y := hmem
        have := hgen (gen W) (by rw [hF']; exact hy') hcl
        left
        rw [hEsupp, ← this, (hgen' W hW).def]
        exact hxW
    by_contra hyE
    have hdisj : F ∩ ((E.support : Set Y) ∩ v') = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hxE hxv
      exact hxv.2 hxE
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp (hconn (ψ y)).isPreconnected _ _
      hEcl hv'c hFsub hdisj with h | h
    · exact hyE (h rfl)
    · exact hy' (hv'fin.subset h)
  · intro hy
    by_contra hyx
    have hV : ψ y ∈ biregularLocus ψ := by simpa [exceptionalSet] using hyx
    haveI : IsIso (ψ ∣_ biregularLocus ψ) := isBiregular_biregularLocus ψ
    have hyC : y ∈ closure ({C.point} : Set Y) := hEsupp ▸ hy
    have hCy : ψ y = ψ C.point := hψC y hyC
    obtain ⟨c, hcC, hcl⟩ := isClosed_closure.exists_closed_singleton
      (S := closure ({C.point} : Set Y)) ⟨C.point, subset_closure rfl⟩
    have hcy : ψ c = ψ y := by rw [hψC c hcC, hCy]
    have hnc := not_isClosed_of_properCurve C
    by_cases hyp : y = C.point
    · subst hyp
      have := eq_of_isIso_morphismRestrict ψ (biregularLocus ψ) (hcy ▸ hV) hcy
      exact hnc (this ▸ hcl)
    · exact hyp (eq_of_isIso_morphismRestrict ψ (biregularLocus ψ) hV hCy)

end Contraction

/-! ### Curve forms on relative classes -/

section CurveForm

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y)
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- The curve form of a `ℚ`-Cartier divisor on the image of a relative class in `N₁(X)` is its
relative curve form. -/
private theorem curveForm_relativeToAbsolute (D : QDivisor X) (h : D.IsQCartier)
    (z : RelativeNumericalCurveClasses sX f) :
    QDivisor.curveForm sX D h (relativeToAbsolute sX f z) =
      QDivisor.relativeCurveForm sX f D h z := by
  unfold QDivisor.curveForm QDivisor.relativeCurveForm
  simp only [Finsupp.sum]
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply]
  congr 1
  obtain ⟨Zc, rfl⟩ := relativeNumericalClass_surjective sX f z
  rfl

/-- The relative curve form of a `ℚ`-Cartier divisor on the class of a contracted curve is its
intersection number with that curve. -/
private theorem relativeCurveForm_relativeClass [QuasiCompact sX] (D : QDivisor X)
    (h : D.IsQCartier) (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    QDivisor.relativeCurveForm sX f D h (C.relativeClass f hC) =
      (D.intersectionNumber k sX C.ι C.dim_le h : ℝ) := by
  rw [← curveForm_relativeToAbsolute]
  exact MMP.ProgramBaseChange.curveForm_numericalClass_cycle sX D h C

end CurveForm

section Program

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  (sX : X ⟶ Spec (.of ℂ))

/-- A *stage* of the program over `X`: a projective birational morphism `q : Y ⟶ X` from a
projective `ℚ`-factorial surface, a canonical divisor `K_Y` and a dlt boundary `Γ` on `Y` such
that `Γ + a(F, X, B) ≥ 0` for every prime divisor `F` of `Y`, `Γ` has the coefficient of `B`
along prime divisors lying over prime divisors of `X`, and coefficient one along the others. -/
private structure IsStage (K : Divisor X) (B : QDivisor X) {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (q : Y ⟶ X) (KY : Divisor Y) (Γ : QDivisor Y) :
    Prop where
  isBirationalMorphism : IsBirationalMorphism q
  isProjectiveMorphism : IsProjectiveMorphism q
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ (q ≫ sX)
  isQFactorial : IsQFactorial (q ≫ sX)
  isDltPair : MMP.Mori.IsDltPair (q ≫ sX) 2 KY Γ
  disc : ∀ F : MMP.Mori.PrimeDivisor Y, ∃ a : ℚ,
    IsDiscrepancy sX 2 K B ⟨Y, q, isQFactorial.1, isBirationalMorphism, F⟩ a ∧
      0 ≤ Γ.coeff F + a
  coeff_of_map_eq : ∀ (F : MMP.Mori.PrimeDivisor Y) (Q : MMP.Mori.PrimeDivisor X),
    q F.genericPoint = Q.genericPoint → Γ.coeff F = B.coeff Q
  coeff_of_forall_ne : ∀ F : MMP.Mori.PrimeDivisor Y,
    (∀ Q : MMP.Mori.PrimeDivisor X, q F.genericPoint ≠ Q.genericPoint) → Γ.coeff F = 1

/-- The conclusion of the theorem, for a fixed `(X, B)`. -/
private def Conclusion (B : QDivisor X) : Prop :=
  ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (q : Y ⟶ X) (hq : IsBirationalMorphism q) (hY : IsQFactorial (q ≫ sX))
      (Δ : QDivisor Y),
      IsProjectiveMorphism q ∧ MMP.Mori.IsProjectiveVariety ℂ (q ≫ sX) ∧
      MMP.Intersection.IsDltPair (q ≫ sX) Δ ∧
      (∀ K : Divisor X, K.IsCanonicalDivisor sX 2 →
        IsCrepantBoundary sX 2 K B q hY.1 hq Δ) ∧
      ∀ E : MMP.Mori.PrimeDivisor Y, RationalMap.IsExceptional (X := Y) q.toRationalMap E →
        MMP.Intersection.IsLogDiscrepancy sX 2 (QDivisor.toRDivisor B)
          (⟨Y, q, hY.1, hq, E⟩ : DivisorOver ℂ sX) 0 ∧
        Δ.coeff E = 1

/-- **The first model.** A projective log resolution with the strict transform of `B` plus the
reduced exceptional divisor as boundary is a stage. -/
private theorem exists_isStage (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 2) {B : QDivisor X}
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 2) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (q : Y ⟶ X) (KY : Divisor Y) (Γ : QDivisor Y), IsStage sX K B q KY Γ := by
  classical
  have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
  have hPB : MMP.Mori.IsPair sX B := hB.1
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.toIsVariety
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨Y, _, _, _, _, p, hlog, hproj, hW, hYproj, hdimY, hQ⟩ :=
    exists_projective_log_resolution sX hX hXn B
  have hbir : IsBirationalMorphism p := hlog.isBirationalMorphism
  haveI : IsProper p := hlog.isProper
  haveI : LocallyOfFiniteType (p ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety ℂ (p ≫ sX) := hW.1
  obtain ⟨KY, hKY⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (p ≫ sX)
    hlog.isSmoothScheme (n := 2) (hdimY.trans hdim)
  obtain ⟨E, hE⟩ := exists_isExceptionalDivisorSum hbir
  obtain ⟨Δ, hΔ, -⟩ := (hPB.existsUnique_isCrepantBoundary hK p hW hbir).1
  set st : MMP.Mori.PrimeDivisor Y → Prop :=
    fun F => ∃ Q : MMP.Mori.PrimeDivisor X, p F.genericPoint = Q.genericPoint
  have hnst : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ st F → F ∈ E.support := by
    intro F hF
    rw [Finsupp.mem_support_iff]
    change E.coeff F ≠ 0
    rw [hE F, if_pos]
    · exact one_ne_zero
    · by_contra hc
      obtain ⟨Q, hQ, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hc
      exact hF ⟨Q, hQ.symm⟩
  set Γ : QDivisor Y := Δ + ∑ F ∈ E.support,
    (if st F then (0 : ℚ) else 1 - Δ.coeff F) • Finsupp.single F (1 : ℚ)
  have hΓ : ∀ F : MMP.Mori.PrimeDivisor Y, Γ.coeff F = if st F then Δ.coeff F else 1 := by
    intro F
    change (Δ + ∑ F ∈ E.support,
      (if st F then (0 : ℚ) else 1 - Δ.coeff F) • Finsupp.single F (1 : ℚ)) F = _
    rw [Finsupp.add_apply, Finsupp.finset_sum_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    by_cases h : st F
    · simp only [if_pos h, ite_self, add_zero]
      rfl
    · simp only [if_neg h, if_pos (hnst F h)]
      change Δ.coeff F + (1 - Δ.coeff F) = 1
      ring
  have hlc : ∀ F : MMP.Mori.PrimeDivisor Y, Δ.coeff F ≤ 1 := by
    intro F
    have hlogd := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy (hΔ F)
      (1 + ((-Δ.coeff F : ℚ) : ℝ))).mpr ⟨hlog.isProper, rfl⟩
    have h0 := hB.2.2 2 _ _ hlogd
    have : (0 : ℝ) ≤ ((1 + -Δ.coeff F : ℚ) : ℝ) := by push_cast at h0 ⊢; exact h0
    have : (0 : ℚ) ≤ 1 + -Δ.coeff F := by exact_mod_cast this
    linarith
  have hst : ∀ (F : MMP.Mori.PrimeDivisor Y) (Q : MMP.Mori.PrimeDivisor X),
      p F.genericPoint = Q.genericPoint → Δ.coeff F = B.coeff Q := by
    intro F Q h
    have := MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq
      (D := ⟨Y, p, hW, hbir, F⟩) h (hΔ F)
    linarith
  have hcoeff : ∀ F : MMP.Mori.PrimeDivisor Y, 0 ≤ Γ.coeff F ∧ Γ.coeff F ≤ 1 := by
    intro F
    rw [hΓ F]
    split_ifs with h
    · obtain ⟨Q, hQ⟩ := h
      refine ⟨?_, hlc F⟩
      rw [hst F Q hQ]
      exact hB.2.1 Q
    · norm_num
  have hsupp : ∀ P ∈ Γ.support, P.support ⊆
      ((exceptionalSet p ⊔ (QDivisor.toRDivisor B).supp.preimage p.continuous : Closeds Y) :
        Set Y) := by
    intro P hP
    by_cases h : st P
    · obtain ⟨Q, hPQ⟩ := h
      have hBQ : B.coeff Q ≠ 0 := by
        have h1 := Finsupp.mem_support_iff.mp hP
        have h2 : Γ.coeff P = Δ.coeff P := by rw [hΓ P, if_pos ⟨Q, hPQ⟩]
        rw [← hst P Q hPQ, ← h2]
        exact h1
      have hBQ' : (QDivisor.toRDivisor B).coeff Q ≠ 0 := by
        simpa [QDivisor.toRDivisor] using hBQ
      have hclosed : IsClosed (((QDivisor.toRDivisor B).supp.preimage p.continuous : Closeds Y) :
          Set Y) := Closeds.isClosed _
      have hηP : P.genericPoint ∈
          ((QDivisor.toRDivisor B).supp.preimage p.continuous : Closeds Y) := by
        change p P.genericPoint ∈ ((QDivisor.toRDivisor B).supp : Set X)
        rw [hPQ]
        refine DivisorWithCoeffs.support_subset_supp hBQ' ?_
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      intro x hx
      right
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
      exact hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηP) hx
    · have hF : P.support ⊆ MMP.Intersection.exceptionalLocus p := by
        by_contra hc
        obtain ⟨Q, hQ, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hc
        exact h ⟨Q, hQ.symm⟩
      exact (hF.trans (MMP.Flips.exceptionalLocus_subset_exceptionalSet p)).trans
        (fun x hx => Or.inl hx)
  have hsnc : Γ.IsSNC (p ≫ sX) := isSNC_of_isLogResolution hlog Γ hsupp
  have hdlt : MMP.Mori.IsDltPair (p ≫ sX) 2 KY Γ := by
    refine ⟨⟨hW, hKY, MMP.Fourfold.isQCartier_of_isQFactorial _ hQ _⟩, hcoeff, ⊤, ?_, ?_, ?_⟩
    · exact hlog.isSmoothScheme.ge
    · exact isSNC_restrictOpen (p ≫ sX) hsnc ⊤
    · intro D a hD _
      exfalso
      obtain ⟨x, hx⟩ := D.center.isIrreducible.nonempty
      exact hD hx (by simp)
  refine ⟨Y, inferInstance, inferInstance, inferInstance, p, KY, Γ,
    { isBirationalMorphism := hbir
      isProjectiveMorphism := hproj
      isProjectiveVariety := hYproj
      isQFactorial := hQ
      isDltPair := hdlt
      disc := fun F => ⟨-Δ.coeff F, hΔ F, ?_⟩
      coeff_of_map_eq := fun F Q h => ?_
      coeff_of_forall_ne := fun F hF => ?_ }⟩
  · rw [hΓ F]
    split_ifs
    · linarith
    · linarith [hlc F]
  · rw [hΓ F, if_pos ⟨Q, h⟩, hst F Q h]
  · rw [hΓ F, if_neg]
    rintro ⟨Q, hQ⟩
    exact hF Q hQ

/-- **A step of the program.** If `K_Y + Γ` is negative on a curve contracted by `q`, the
contraction of the ray of that curve is a new stage with fewer contracted curves. -/
private theorem exists_isStage_lt (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 2) {B : QDivisor X}
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 2) {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {q : Y ⟶ X} [QuasiCompact (q ≫ sX)] {KY : Divisor Y} {Γ : QDivisor Y}
    (hS : IsStage sX K B q KY Γ) (C : ProperCurve (q ≫ sX)) (hC : C.IsContractedBy q)
    (hneg : (Divisor.toQDivisor KY + Γ).intersectionNumber ℂ (q ≫ sX) C.ι C.dim_le
      hS.isDltPair.1.2.2 < 0) :
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (_ : IsLocallyNoetherian Z) (_ : IsNormal Z)
      (g : Z ⟶ X) (KZ : Divisor Z) (ΓZ : QDivisor Z), IsStage sX K B g KZ ΓZ ∧
      Nat.card {D : ProperCurve (g ≫ sX) // D.IsContractedBy g} <
        Nat.card {D : ProperCurve (q ≫ sX) // D.IsContractedBy q} := by
  classical
  have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
  have hPB : MMP.Mori.IsPair sX B := hB.1
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.toIsVariety
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : MMP.Mori.IsProjectiveVariety ℂ sX := hX
  have hq := hS.isBirationalMorphism
  have hQ := hS.isQFactorial
  have hYn : IsNormalVariety ℂ (q ≫ sX) := hQ.1
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hS.isProjectiveMorphism
  haveI : MMP.Mori.IsProjectiveVariety ℂ (q ≫ sX) := hS.isProjectiveVariety
  haveI : AlgebraicGeometry.IsVariety ℂ (q ≫ sX) := hYn.1
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (q ≫ sX)
  haveI : IsProper (q ≫ sX) :=
    isProper_of_isProjectiveMorphism _ hS.isProjectiveVariety.isProjective
  have hKB : (Divisor.toQDivisor K + B).IsQCartier := by
    obtain ⟨-, n', K', hK', hQ'⟩ := hPB
    exact hQ'.add_of_linearlyEquivalent
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hXn hK' hK)
  have hPBw : IsPairWith sX 2 K B := ⟨hXn, hK, hKB⟩
  have hdimY : topologicalKrullDim Y = 2 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (q ≫ sX) hq).symm.trans
      hdim
  -- the relative cone of `q` is simplicial
  obtain ⟨hfin, -, hext, hli⟩ := relativeClosedConeOfCurves_eq_hull_of_isBirationalMorphism hQ
    hXn (AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ (q ≫ sX))
    (AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ sX) hdimY hdim q rfl
    hS.isProjectiveMorphism.isProjective hq
  set R : Set (RelativeNumericalCurveClasses (q ≫ sX) q) :=
    {w | ∃ c : ℝ, 0 ≤ c ∧ c • C.relativeClass q hC = w}
  have hR : IsExtremalRay ℝ (relativeClosedConeOfCurves (q ≫ sX) q :
      Set (RelativeNumericalCurveClasses (q ≫ sX) q)) R := hext ⟨C, hC⟩
  have hRadd : ∀ u ∈ R, ∀ v ∈ R, u + v ∈ R := hR.1.2.2.1
  have hDQ := hS.isDltPair.1.2.2
  have hform : QDivisor.relativeCurveForm (q ≫ sX) q (Divisor.toQDivisor KY + Γ) hDQ
      (C.relativeClass q hC) =
        ((Divisor.toQDivisor KY + Γ).intersectionNumber ℂ (q ≫ sX) C.ι C.dim_le hDQ : ℝ) :=
    relativeCurveForm_relativeClass (q ≫ sX) q _ hDQ C hC
  have hRneg : ∀ z ∈ R, z ≠ 0 →
      QDivisor.relativeCurveForm (q ≫ sX) q (Divisor.toQDivisor KY + Γ) hDQ z < 0 := by
    rintro _ ⟨c, hc, rfl⟩ hz
    have hc' : 0 < c := lt_of_le_of_ne hc (by rintro rfl; exact hz (zero_smul _ _))
    rw [map_smul, smul_eq_mul, hform]
    exact mul_neg_of_pos_of_neg hc' (by exact_mod_cast hneg)
  -- the contraction of the ray
  obtain ⟨Z, ψ, g, hc⟩ :=
    IsDltPair.exists_isRelativeContractionOfFace sX q rfl hS.isDltPair hQ hR.1 hRadd hRneg
  have hψg : ψ ≫ g = q := hc.comp_eq
  have hgp : IsProjectiveMorphism g := hc.isProjectiveMorphism
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hgp
  haveI : IsProper ψ := by
    haveI : IsProper (ψ ≫ g) := by rw [hψg]; infer_instance
    exact IsProper.of_comp ψ g
  obtain ⟨hψs, hZi, hZnl⟩ := surjective_isIntegral_isNormal_of_isIso_app ψ hc.isIso_app
  haveI := hZi
  haveI := hZnl
  haveI : LocallyOfFiniteType (g ≫ sX) := inferInstance
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have hZv : AlgebraicGeometry.IsVariety ℂ (g ≫ sX) :=
    { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
  haveI := hZv
  have hZn : IsNormalVariety ℂ (g ≫ sX) := ⟨hZv, inferInstance⟩
  have hZp : MMP.Mori.IsProjectiveVariety ℂ (g ≫ sX) :=
    { toIsVariety := hZv, isProjective := hgp.comp hX.isProjective }
  haveI := hZp
  have hcomp : ψ ≫ g ≫ sX = q ≫ sX := by rw [← Category.assoc, hψg]
  have hqx : ∀ y : Y, q y = g (ψ y) := fun y => by rw [← Scheme.Hom.comp_apply, hψg]
  -- `ψ` and `g` are birational
  haveI : IsDominant q := hq.isDominant
  haveI : IsDominant ψ := ⟨by rw [DenseRange, Set.range_eq_univ.mpr hψs]; exact dense_univ⟩
  haveI : IsDominant (ψ ≫ g) := by rw [hψg]; infer_instance
  haveI : IsDominant g := IsDominant.of_comp ψ g
  have hψb : IsBirationalMorphism ψ := by
    refine MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_of_isBirational ψ
      (AlgebraicGeometry.isBirational_of_surjective_functionFieldMap ψ fun t => ?_)
    obtain ⟨z, hz⟩ := hq.functionFieldMap_bijective.2 t
    exact ⟨functionFieldMap g z, by
      rw [MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply ψ g hψg, hz]⟩
  have hgb : IsBirationalMorphism g :=
    MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_of_comp_left ψ g hψb (by rw [hψg]; exact hq)
  have hdimZ : topologicalKrullDim Z = 2 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hgb).symm.trans
      hdim
  -- `ψ` contracts exactly the curve `C`
  have hψC : C.IsContractedBy ψ :=
    (hc.isContractedBy_iff C hC).mpr ⟨1, zero_le_one, one_smul _ _⟩
  have honly : ∀ D : ProperCurve (q ≫ sX), D.IsContractedBy ψ → D = C := by
    intro D hD
    have hDq : D.IsContractedBy q := fun x hx => by rw [hqx, hqx, hD x hx]
    obtain ⟨c, -, hcD⟩ := (hc.isContractedBy_iff D hDq).mp hD
    by_contra hne
    have hne' : (⟨D, hDq⟩ : {C : ProperCurve (q ≫ sX) // C.IsContractedBy q}) ≠ ⟨C, hC⟩ :=
      fun h => hne (congrArg Subtype.val h)
    have key := linearIndependent_iff'.mp hli {⟨D, hDq⟩, ⟨C, hC⟩}
      (fun i => if i = ⟨D, hDq⟩ then (1 : ℝ) else -c) (by
        rw [Finset.sum_pair hne']
        simp only [if_pos rfl, if_neg hne'.symm, one_smul, neg_smul]
        rw [← hcD]
        simp)
      ⟨D, hDq⟩ (Finset.mem_insert_self _ _)
    simp at key
  -- the exceptional set of `ψ` is the curve `C`
  have hcoh := coheight_point_eq_one hdimY C
  set E0 : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne C.point hcoh
  have hE0 : E0.genericPoint = C.point :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne C.point hcoh
  have hZη : ¬ IsClosed ({genericPoint Z} : Set Z) := by
    intro h
    have huniv : ({genericPoint Z} : Set Z) = Set.univ := by
      rw [← h.closure_eq]; exact (genericPoint_spec Z).def
    haveI : Subsingleton Z := ⟨fun a b => by
      have ha : a ∈ ({genericPoint Z} : Set Z) := huniv ▸ trivial
      have hb : b ∈ ({genericPoint Z} : Set Z) := huniv ▸ trivial
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology Z
    rw [hdimZ] at h0
    exact absurd h0 (by decide)
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    (q ≫ sX) (g ≫ sX) hYn.1 hZn ψ hψb).2
  have hEx : (exceptionalSet ψ : Set Y) = E0.support :=
    exceptionalSet_eq_support (q ≫ sX) hdimY hZη ψ
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hψb) hconn C hψC honly E0 hE0
  -- the absolute ray
  set R' : Set (NumericalCurveClasses (q ≫ sX)) := relativeToAbsolute (q ≫ sX) q '' R
  have hR' : IsExtremalRay ℝ (closedConeOfCurves (q ≫ sX) :
      Set (NumericalCurveClasses (q ≫ sX))) R' :=
    isExtremalRay_image_relativeToAbsolute (q ≫ sX) sX q rfl hR
  have hR'neg : ∀ u ∈ R', u ≠ 0 →
      QDivisor.curveForm (q ≫ sX) (Divisor.toQDivisor KY + Γ) hDQ u < 0 := by
    rintro _ ⟨z, hz, rfl⟩ hz0
    rw [curveForm_relativeToAbsolute]
    exact hRneg z hz (by rintro rfl; exact hz0 (map_zero _))
  have hR'add : ∀ u ∈ R', ∀ v ∈ R', u + v ∈ R' := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a + b, hRadd a ha b hb, map_add _ _ _⟩
  obtain ⟨H, hHinv, hH⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hZp
  have hcontr : IsContractionOfFace ℂ (q ≫ sX) (g ≫ sX) R' ψ :=
    { isProjectiveVariety_source := hS.isProjectiveVariety
      isProjectiveVariety_target := hZp
      comp_eq := hcomp
      isExtremalFace := hR'.1
      isContractedBy_iff := fun D => by
        constructor
        · intro hD
          obtain rfl := honly D hD
          exact ⟨D.relativeClass q hC, ⟨1, zero_le_one, one_smul _ _⟩, rfl⟩
        · rintro ⟨_, ⟨c, -, rfl⟩, hz⟩
          refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero ψ hcomp H hH D ?_
          have hC0 := ProperCurve.degree_pullback_eq_zero_of_isContractedBy ψ hcomp C hψC H
          have e : NumericalCurveClasses.degree (q ≫ sX) ((Scheme.Modules.pullback ψ).obj H)
              (OneCycle.numericalClass (q ≫ sX) (D.cycle ℝ)) =
                c * NumericalCurveClasses.degree (q ≫ sX) ((Scheme.Modules.pullback ψ).obj H)
                  (OneCycle.numericalClass (q ≫ sX) (C.cycle ℝ)) := by
            rw [← hz, map_smul, map_smul, smul_eq_mul]
            rfl
          rw [NumericalCurveClasses.degree_numericalClass,
            NumericalCurveClasses.degree_numericalClass,
            OneCycle.degree_cycle, OneCycle.degree_cycle, hC0] at e
          exact_mod_cast
            (by simpa using e : (D.degree ℂ ((Scheme.Modules.pullback ψ).obj H) : ℝ) = 0)
      isIso_app := hc.isIso_app }
  have hdiv : IsDivisorialContraction ℂ (q ≫ sX) (g ≫ sX) R' ψ :=
    ⟨hYn, hR', hcontr, hψb, ⟨E0, hEx⟩⟩
  -- the new model
  have hZQ : IsQFactorial (g ≫ sX) :=
    isQFactorial_of_isDltPair_of_isDivisorialContraction_or_isFiberTypeContraction hQ
      hS.isDltPair ⟨hR'.1, hR'add, hR'neg⟩ (Or.inl hdiv)
  have hdltZ := IsDivisorialContraction.isDltPair_transformDivisor hQ ⟨hDQ, hR', hR'neg⟩ hdiv
    hS.isDltPair
  have hYn' : IsNormalVariety ℂ (ψ ≫ g ≫ sX) := by rw [hcomp]; exact hYn
  -- strict transforms of prime divisors of `Z`
  have hstrict : ∀ P : MMP.Mori.PrimeDivisor Z, ∃ P' : MMP.Mori.PrimeDivisor Y,
      ψ P'.genericPoint = P.genericPoint ∧
      (⟨Z, g, hZQ.1, hgb, P⟩ : DivisorOver ℂ sX).valuation =
        (⟨Y, q, hYn, hq, P'⟩ : DivisorOver ℂ sX).valuation ∧
      ∀ D : QDivisor Y, (RationalMap.transformDivisor (X := Y) ψ.toRationalMap D).coeff P =
        D.coeff P' := by
    intro P
    obtain ⟨P', hψP, -, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZn hYn' hψb P
    refine ⟨P', hψP, ?_, htr⟩
    have := P.isDiscreteValuationRing_localRing
    have hV : P.genericPoint ∈ biregularLocus ψ :=
      MMP.Flips.mem_biregularLocus_of_valuationRing hZn hYn'.1 hψb _
    haveI : IsIso (ψ ∣_ biregularLocus ψ) := isBiregular_biregularLocus ψ
    have hU : P'.genericPoint ∈ ψ ⁻¹ᵁ biregularLocus ψ := show ψ _ ∈ _ from hψP ▸ hV
    refine (MMP.Positivity.DivisorOver.valuation_eq_of_iso
      (⟨Y, q, hYn, hq, P'⟩ : DivisorOver ℂ sX) (⟨Z, g, hZQ.1, hgb, P⟩ : DivisorOver ℂ sX)
      (ψ ⁻¹ᵁ biregularLocus ψ) (biregularLocus ψ) hU hV (asIso (ψ ∣_ biregularLocus ψ))
      ?_ ?_).symm
    · change (ψ ∣_ biregularLocus ψ) ≫ (biregularLocus ψ).ι ≫ g = (ψ ⁻¹ᵁ biregularLocus ψ).ι ≫ q
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hψg]
    · apply (biregularLocus ψ).ι.isOpenEmbedding.injective
      refine (MMP.Mori.ι_morphismRestrict_apply ψ (biregularLocus ψ) _).trans ?_
      rw [Scheme.Opens.ι_apply]
      exact hψP
  have hqP : ∀ (P : MMP.Mori.PrimeDivisor Z) (P' : MMP.Mori.PrimeDivisor Y),
      ψ P'.genericPoint = P.genericPoint → q P'.genericPoint = g P.genericPoint := by
    intro P P' h
    rw [hqx, h]
  refine ⟨Z, inferInstance, inferInstance, inferInstance, g,
    RationalMap.transformDivisor (X := Y) ψ.toRationalMap KY,
    RationalMap.transformDivisor (X := Y) ψ.toRationalMap Γ,
    { isBirationalMorphism := hgb
      isProjectiveMorphism := hgp
      isProjectiveVariety := hZp
      isQFactorial := hZQ
      isDltPair := hdltZ
      disc := fun P => ?_
      coeff_of_map_eq := fun P Q hPQ => ?_
      coeff_of_forall_ne := fun P hP => ?_ }, ?_⟩
  · obtain ⟨P', hψP, hv, htr⟩ := hstrict P
    obtain ⟨a, ha, ha0⟩ := hS.disc P'
    obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPB hK
      (⟨Z, g, hZQ.1, hgb, P⟩ : DivisorOver ℂ sX)
    have heq := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPBw hv ha' ha
    refine ⟨a', ha', ?_⟩
    rw [htr Γ, heq]
    exact ha0
  · obtain ⟨P', hψP, -, htr⟩ := hstrict P
    rw [htr Γ]
    exact hS.coeff_of_map_eq P' Q ((hqP P P' hψP).trans hPQ)
  · obtain ⟨P', hψP, -, htr⟩ := hstrict P
    rw [htr Γ]
    exact hS.coeff_of_forall_ne P' fun Q hQ => hP Q ((hqP P P' hψP).symm.trans hQ)
  -- the number of contracted curves drops
  · have hpt : ∀ D : {D : ProperCurve (g ≫ sX) // D.IsContractedBy g}, ∃ w : Y,
        ψ w = D.1.point := fun D => hψs _
    choose w hw using hpt
    have hDnc : ∀ D : ProperCurve (g ≫ sX), ¬ IsClosed ({D.point} : Set Z) :=
      not_isClosed_of_properCurve
    have hwc : ∀ D, ¬ IsClosed ({w D} : Set Y) := by
      intro D h
      apply hDnc D.1
      have := ψ.isClosedMap _ h
      rwa [Set.image_singleton, hw D] at this
    have hwη : ∀ D, w D ≠ genericPoint Y := fun D h =>
      point_ne_genericPoint hdimZ D.1 (by rw [← hw D, h, map_genericPoint_of_isDominant])
    let Φ : {D : ProperCurve (g ≫ sX) // D.IsContractedBy g} →
        {D : ProperCurve (q ≫ sX) // D.IsContractedBy q} := fun D =>
      ⟨⟨w D, isProperCurve_of_not_isClosed (q ≫ sX) hdimY (hwc D) (hwη D)⟩, fun x hx => by
        have hsp : ψ (w D) ⤳ ψ x := (specializes_iff_mem_closure.mpr hx).map ψ.continuous
        rw [hw D] at hsp
        have h1 := D.2 (ψ x) (specializes_iff_mem_closure.mp hsp)
        change q x = q (w D)
        rw [hqx, hqx, h1, hw D]⟩
    have hΦinj : Function.Injective Φ := by
      intro D₁ D₂ h
      have h1 : w D₁ = w D₂ := congrArg (fun E => E.1.point) h
      have h2 : D₁.1.point = D₂.1.point := by rw [← hw D₁, ← hw D₂, h1]
      exact Subtype.ext (ProperCurve.ext h2)
    have hΦC : (⟨C, hC⟩ : {D : ProperCurve (q ≫ sX) // D.IsContractedBy q}) ∉ Set.range Φ := by
      rintro ⟨D, hD⟩
      have h1 : w D = C.point := congrArg (fun E => E.1.point) hD
      obtain ⟨c, hcC, hcl⟩ := isClosed_closure.exists_closed_singleton
        (S := closure ({C.point} : Set Y)) ⟨C.point, subset_closure rfl⟩
      apply hDnc D.1
      rw [← hw D, h1, ← hψC c hcC, ← Set.image_singleton]
      exact ψ.isClosedMap _ hcl
    haveI : Finite {D : ProperCurve (q ≫ sX) // D.IsContractedBy q} := hfin.to_subtype
    haveI : Finite {D : ProperCurve (g ≫ sX) // D.IsContractedBy g} := Finite.of_injective Φ hΦinj
    haveI := Fintype.ofFinite {D : ProperCurve (q ≫ sX) // D.IsContractedBy q}
    haveI := Fintype.ofFinite {D : ProperCurve (g ≫ sX) // D.IsContractedBy g}
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_lt_of_injective_of_notMem Φ hΦinj hΦC

/-- **The last model.** If `K_Y + Γ` is nef over `X`, then `Γ` is the crepant boundary and the
stage is a crepant dlt modification. -/
private theorem conclusion_of_isStage (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 2) {B : QDivisor X}
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 2) {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {q : Y ⟶ X} [QuasiCompact (q ≫ sX)] {KY : Divisor Y} {Γ : QDivisor Y}
    (hS : IsStage sX K B q KY Γ) (hnef : ∀ C : ProperCurve (q ≫ sX), C.IsContractedBy q →
      0 ≤ (Divisor.toQDivisor KY + Γ).intersectionNumber ℂ (q ≫ sX) C.ι C.dim_le
        hS.isDltPair.1.2.2) :
    Conclusion sX B := by
  classical
  have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
  have hPB : MMP.Mori.IsPair sX B := hB.1
  have hq := hS.isBirationalMorphism
  have hQ := hS.isQFactorial
  have hYn : IsNormalVariety ℂ (q ≫ sX) := hQ.1
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hS.isProjectiveMorphism
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.toIsVariety
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (q ≫ sX)
  have hKY := hS.isDltPair.1.2.1
  obtain ⟨Δ, hΔ, -⟩ := (hPB.existsUnique_isCrepantBoundary hK q hYn hq).1
  have hKB : (Divisor.toQDivisor K + B).IsQCartier := by
    obtain ⟨-, n', K', hK', hQ'⟩ := hPB
    exact hQ'.add_of_linearlyEquivalent
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hXn hK' hK)
  have hGeff : (Γ - Δ).IsEffective := by
    intro F
    obtain ⟨a, ha, ha0⟩ := hS.disc F
    have := IsDiscrepancy.eq (hΔ F) ha
    rw [DivisorWithCoeffs.coeff_sub]
    linarith
  have hGexc : ∀ F : MMP.Mori.PrimeDivisor Y,
      ¬ MMP.Flips.IsExceptionalPrimeDivisor sX q F → (Γ - Δ).coeff F = 0 := by
    intro F hF
    have hnot : ¬ (MMP.Flips.ProperDivisorOver.mk ⟨Y, q, hYn, hq, F⟩ inferInstance :
        MMP.Flips.ProperDivisorOver ℂ sX).IsExceptional :=
      fun h => hF ⟨hYn, hq, inferInstance, h⟩
    obtain ⟨Q, -, hQ', -⟩ :=
      MMP.Flips.ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hXn _ hnot
    have h1 := hS.coeff_of_map_eq F Q hQ'
    have h2 := MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq
      (D := ⟨Y, q, hYn, hq, F⟩) hQ' (hΔ F)
    rw [DivisorWithCoeffs.coeff_sub, h1]
    linarith
  have hA := hS.isDltPair.1.2.2
  have hB' := isQCartier_of_isQFactorial _ hQ (Divisor.toQDivisor KY + Δ)
  have hnefG : (Γ - Δ).IsRelativelyNef (q ≫ sX) q := by
    have hsub : Γ - Δ = (Divisor.toQDivisor KY + Γ) + -(Divisor.toQDivisor KY + Δ) := by abel
    have hGq : (Γ - Δ).IsQCartier := isQCartier_of_isQFactorial _ hQ _
    refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (q ≫ sX) hGq
      fun C hC => ?_
    have hBn := MMP.Fourfold.Oai4C1.isQCartier_neg hB'
    rw [MMP.Fourfold.intersectionNumber_congr (q ≫ sX) C.ι C.dim_le hGq (hA.add hBn) hsub,
      QDivisor.intersectionNumber_add' ℂ (q ≫ sX) C.ι C.dim_le _ _ hA hBn,
      MMP.Mori.QDivisor.intersectionNumber_neg ℂ (q ≫ sX) C.ι C.dim_le hB' hBn,
      intersectionNumber_eq_zero_of_isCrepantBoundary hXn hK hKB hYn hq hΔ hKY hB' C hC]
    linarith [hnef C hC]
  have hG0 := MMP.Mori.QDivisor.eq_zero_of_isEffective_of_isRelativelyNef ℂ sX (q ≫ sX) hXn hYn q
    rfl hq (isQCartier_of_isQFactorial _ hQ _) hGexc hGeff hnefG
  obtain rfl : Γ = Δ := sub_eq_zero.mp hG0
  refine ⟨Y, inferInstance, inferInstance, inferInstance, q, hq, hQ, Γ, hS.isProjectiveMorphism,
    hS.isProjectiveVariety,
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair (q ≫ sX) hKY Γ).mpr hS.isDltPair,
    fun K' hK' F => MMP.Spreading.isDiscrepancy_of_linearlyEquivalent (hΔ F)
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hXn hK' hK),
    fun E hE => ?_⟩
  have h1 := hS.coeff_of_forall_ne E (map_genericPoint_ne_of_isExceptional (sX := sX) hE)
  refine ⟨?_, h1⟩
  have := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hΔ E)
    (inferInstance : IsProper q)
  rw [h1] at this
  norm_num at this
  exact this

/-- **Termination.** Every stage leads to the conclusion, by induction on the number of curves
contracted over `X`. -/
private theorem conclusion_of_card (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 2) {B : QDivisor X}
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 2) (n : ℕ) :
    ∀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {q : Y ⟶ X}
      {KY : Divisor Y} {Γ : QDivisor Y}, IsStage sX K B q KY Γ →
      Nat.card {D : ProperCurve (q ≫ sX) // D.IsContractedBy q} = n → Conclusion sX B := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y _ _ _ q KY Γ hS hn
    haveI := hS.isProjectiveVariety
    haveI : QuasiCompact (q ≫ sX) := inferInstance
    by_cases hnef : ∀ C : ProperCurve (q ≫ sX), C.IsContractedBy q →
        0 ≤ (Divisor.toQDivisor KY + Γ).intersectionNumber ℂ (q ≫ sX) C.ι C.dim_le
          hS.isDltPair.1.2.2
    · exact conclusion_of_isStage sX hX hdim hB hK hS hnef
    · push Not at hnef
      obtain ⟨C, hC, hlt⟩ := hnef
      obtain ⟨Z, _, _, _, g, KZ, ΓZ, hSZ, hcard⟩ :=
        exists_isStage_lt sX hX hdim hB hK hS C hC hlt
      exact ih _ (hn ▸ hcard) hSZ rfl

end Program

/-- **Crepant dlt modification of a projective lc surface.** Let `(X, B)` be a log canonical
pair with `B` a `ℚ`-divisor on a normal projective complex surface `X`. Then there is a projective
birational `q : Y ⟶ X` from a projective `ℚ`-factorial surface `Y` and a dlt boundary `Δ` on `Y`
(effective, with rational coefficients) such that `K_Y + Δ = q^*(K_X + B)` for every canonical
divisor `K_X`, and every `q`-exceptional prime divisor `E` of `Y` has log discrepancy
`a(E; X, B) = 0` and coefficient one in `Δ`. -/
@[mmp "thm_mmp_surface_projective_crepant_dlt_modification"]
public theorem exists_crepant_dltModification_of_surface
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 2) {B : QDivisor X}
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (q : Y ⟶ X) (hq : IsBirationalMorphism q) (hY : IsQFactorial (q ≫ sX))
      (Δ : QDivisor Y),
      IsProjectiveMorphism q ∧ MMP.Mori.IsProjectiveVariety ℂ (q ≫ sX) ∧
      MMP.Intersection.IsDltPair (q ≫ sX) Δ ∧
      (∀ K : Divisor X, K.IsCanonicalDivisor sX 2 →
        IsCrepantBoundary sX 2 K B q hY.1 hq Δ) ∧
      ∀ E : MMP.Mori.PrimeDivisor Y, RationalMap.IsExceptional (X := Y) q.toRationalMap E →
        MMP.Intersection.IsLogDiscrepancy sX 2 (QDivisor.toRDivisor B)
          (⟨Y, q, hY.1, hq, E⟩ : DivisorOver ℂ sX) 0 ∧
        Δ.coeff E = 1 := by
  obtain ⟨-, n, K, hK, -⟩ := hB.1
  have hn : n = 2 := by
    have := hK.topologicalKrullDim_eq.symm.trans hdim
    exact_mod_cast this
  subst hn
  obtain ⟨Y, _, _, _, q, KY, Γ, hS⟩ := exists_isStage sX hX hdim hB hK
  exact conclusion_of_card sX hX hdim hB hK _ hS rfl

end MMP.Threefold
