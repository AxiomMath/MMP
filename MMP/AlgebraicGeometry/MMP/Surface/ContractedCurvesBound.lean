module

public import Mathlib
public import MMP.Attr
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.Intersection.N1FiniteDimensionalProjective
public import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# A uniform bound on the curves contracted from a normal surface

Let `k` be an algebraically closed field of characteristic zero and `S` a normal surface over
`k`. There is a natural number `M` such that every proper birational `k`-morphism `σ : S ⟶ S'`
onto a normal surface `S'` contracts at most `M` integral curves of `S`. One may take
`M = dim N₁(T)` for a smooth projective model `T` of `S`: the classes of the strict transforms
of contracted curves are linearly independent in `N₁(T)`, their intersection matrix being
negative definite.

## Main results

* `MMP.Mori.exists_encard_setOf_isExceptionalCurve_le`: the statement above.

## Implementation notes

A surface over `k` is a normal variety `X` with `topologicalKrullDim X = 2`. A curve of `S`
contracted by `σ` is an `MMP.Mori.IsExceptionalCurve σ`: an integral closed subscheme of
dimension one whose image under `σ` is a point. The count is the extended cardinality
`Set.encard`, so the bound also asserts that only finitely many curves are contracted.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori.NormalSurfaceContractionBound

/-- Every curve contracted by `σ` is the image of a proper curve of `Y`. Let `τ : Y ⟶ S` be a
proper birational morphism from a surface `Y`, of finite type over `k`, onto a normal surface `S`,
and `σ : S ⟶ S'` proper, with `S'` locally of finite type over `k`. Every curve `E ⊆ S` contracted
by `σ` is the image of the closure of a point `ξ` of codimension one of `Y`; that closure is a
proper curve over `k`, contracted by `τ ≫ σ`. -/
private theorem exists_point_of_isExceptionalCurve {k : Type} [Field k]
    {S S' Y : Scheme.{0}} (sS' : S' ⟶ Spec (.of k)) [LocallyOfFiniteType sS']
    (sY : Y ⟶ Spec (.of k)) [IsIntegral S] [IsIntegral Y] [IsNormal S] [IsLocallyNoetherian S]
    [NoetherianSpace Y] [LocallyOfFiniteType sY]
    (τ : Y ⟶ S) [IsProper τ] (hτ : IsBirational τ) (σ : S ⟶ S') [IsProper σ]
    (hfs : τ ≫ σ ≫ sS' = sY)
    (hdimY : topologicalKrullDim Y = 2) (hdimS : topologicalKrullDim S = 2)
    {E : S.IdealSheafData} (hE : IsExceptionalCurve σ E) :
    ∃ ξ : Y, closure ({τ ξ} : Set S) = E.support ∧ Order.coheight ξ = 1 ∧
      IsProperCurve sY ξ ∧ ∀ y ∈ closure ({ξ} : Set Y), σ (τ y) = σ (τ ξ) := by
  obtain ⟨hcurve, himage⟩ := isCurveIn_inverseTransformIdeal τ hτ hdimY.le hdimS hE.1
  obtain ⟨x', hx'⟩ := hE.2
  obtain ⟨ξ, hξ, -⟩ := hcurve.exists_isGenericPoint
  rw [support_inverseTransformIdeal] at hξ
  have hT : inverseTransform τ E.support = Closeds.closure ({ξ} : Set Y) :=
    Closeds.ext (by rw [Closeds.coe_closure]; exact hξ.symm)
  have hE' : inverseTransformIdeal τ E.support =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({ξ} : Set Y)) := by
    rw [inverseTransformIdeal, hT]
  have himξ : τ.base '' closure ({ξ} : Set Y) = E.support := by rw [hξ]; exact himage
  have hmem : ∀ y ∈ closure ({ξ} : Set Y), σ (τ y) = x' := by
    intro y hy
    have : σ.base (τ.base y) ∈ σ.base '' (E.support : Set S) :=
      ⟨τ.base y, himξ ▸ ⟨y, hy, rfl⟩, rfl⟩
    rw [hx'] at this
    exact this
  refine ⟨ξ, ?_, ?_, ⟨?_, ?_⟩, fun y hy => (hmem y hy).trans (hmem ξ (subset_closure rfl)).symm⟩
  · rw [← himξ, ← IsClosedMap.closure_image_eq_of_continuous τ.isClosedMap τ.continuous,
      Set.image_singleton]
  · have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY ξ
    have h1 : topologicalKrullDim (closure ({ξ} : Set Y)) = 1 := by
      have := hcurve.2
      rw [topologicalKrullDim_subscheme_eq, support_inverseTransformIdeal] at this
      rw [hξ]; exact this
    rw [h1, hdimY] at h
    induction h' : Order.coheight ξ using ENat.recTopCoe with
    | top => rw [h'] at h; exact absurd h (by decide)
    | coe n =>
      rw [h'] at h
      have h2 : ((1 + n : ℕ) : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) := by push_cast; exact h
      have h3 : 1 + n = 2 := by exact_mod_cast h2
      obtain rfl : n = 1 := by omega
      rfl
  · change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({ξ} : Set Y))).subscheme = 1
    rw [← hE']
    exact hcurve.2
  · have hx'cl : IsClosed ({x'} : Set S') := by
      rw [← hx']; exact σ.isClosedMap _ E.support.isClosed
    have hrange : Set.range (curveSubschemeAtι ξ ≫ τ ≫ σ) ⊆ {x'} := by
      rintro _ ⟨t, rfl⟩
      have ht : curveSubschemeAtι ξ t ∈ closure ({ξ} : Set Y) := by
        rw [← MMP.Mori.range_curveSubschemeAtι]; exact ⟨t, rfl⟩
      exact hmem _ ht
    have := isProper_comp_of_range_subset_singleton sS' (curveSubschemeAtι ξ ≫ τ ≫ σ) hx'cl
      hrange
    simpa [hfs] using this

/-- A proper curve on an open subscheme `V` of a separated `k`-scheme `Y` is a proper curve of
`Y`, whose closure stays inside `V`. -/
private theorem exists_properCurve_of_opens {k : Type} [Field k] {Y : Scheme.{0}}
    (s : Y ⟶ Spec (.of k)) [IsSeparated s] (V : Y.Opens) (C : ProperCurve (V.ι ≫ s)) :
    ∃ CY : ProperCurve s, V.ι C.point = CY.point ∧ closure ({CY.point} : Set Y) ⊆ V := by
  set g := curveSubschemeAtι C.point ≫ V.ι with hg
  have : IsProper (g ≫ s) := by rw [hg, Category.assoc]; exact C.isProper_ι_comp
  have : IsProper g := IsProper.of_comp g s
  have hrange : Set.range g = V.ι.base '' closure ({C.point} : Set V) := by
    rw [hg, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      MMP.Mori.range_curveSubschemeAtι]
  have hcl : closure ({V.ι C.point} : Set Y) ⊆ V := by
    refine (closure_minimal ?_ g.isClosedMap.isClosed_range).trans ?_
    · rw [Set.singleton_subset_iff, hrange]; exact ⟨C.point, subset_closure rfl, rfl⟩
    · rw [hrange]; rintro _ ⟨z, -, rfl⟩; exact z.2
  obtain ⟨e, he⟩ := MMP.Threefold.Resolution.exists_curveSubschemeAt_iso V.ι C.point rfl (by
    rw [Scheme.Opens.range_ι]; exact hcl)
  refine ⟨⟨V.ι C.point, ⟨?_, ?_⟩⟩, rfl, hcl⟩
  · rw [← IsHomeomorph.topologicalKrullDim_eq e.hom e.hom.homeomorph.isHomeomorph]
    exact C.dim_eq
  · have h : curveSubschemeAtι (V.ι C.point) = e.inv ≫ curveSubschemeAtι C.point ≫ V.ι := by
      rw [← he, Iso.inv_hom_id_assoc]
    rw [h, Category.assoc, Category.assoc]
    have : IsProper (curveSubschemeAtι C.point ≫ V.ι ≫ s) := C.isProper_ι_comp
    infer_instance

/-- A set all of whose injective `Fin n`-indexed families have `n ≤ M` has at most `M`
elements. -/
private theorem encard_le_of_forall_injective {α : Type*} {s : Set α} {M : ℕ}
    (h : ∀ (n : ℕ) (E : Fin n → α), Function.Injective E → (∀ i, E i ∈ s) → n ≤ M) :
    s.encard ≤ M := by
  by_contra hlt
  push Not at hlt
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)
  have htf : t.Finite := Set.finite_of_encard_eq_coe (k := M + 1) (by rw [htc]; norm_cast)
  have hcard : htf.toFinset.card = M + 1 := by
    have := htf.encard_eq_coe_toFinset_card
    rw [htc] at this
    exact_mod_cast this.symm
  let e := htf.toFinset.equivFin
  have := h (M + 1) (fun i => (e.symm (Fin.cast hcard.symm i)).1)
    (fun i j hij => by simpa using Subtype.val_injective hij)
    (fun i => hts ((Set.Finite.mem_toFinset htf).mp (e.symm (Fin.cast hcard.symm i)).2))
  omega

end MMP.Mori.NormalSurfaceContractionBound

namespace MMP.Mori

/-- Over an algebraically closed field `k` of characteristic zero, a normal surface `S` admits a
bound `M` such that every proper birational `k`-morphism `σ : S ⟶ S'` onto a normal surface
contracts at most `M` integral curves of `S`. -/
@[mmp "lem_mmp_foundation_normal_surface_uniform_curve_contraction_bound"]
public theorem exists_encard_setOf_isExceptionalCurve_le
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] {S : Scheme.{0}}
    (sS : S ⟶ Spec (.of k)) (hS : IsNormalVariety k sS) (hdim : topologicalKrullDim S = 2) :
    ∃ M : ℕ, ∀ (S' : Scheme.{0}) (sS' : S' ⟶ Spec (.of k)) (σ : S ⟶ S'),
      IsNormalVariety k sS' → topologicalKrullDim S' = 2 → σ ≫ sS' = sS →
        IsProper σ → IsBirationalMorphism σ →
          {C : S.IdealSheafData | IsExceptionalCurve σ C}.encard ≤ M := by
  obtain ⟨T, sT, U, τ, hTp, hTsm, hTdim, hcomm, hτp, hτb⟩ :=
    exists_smooth_projective_open_isProper_isBirationalMorphism k sS hS hdim
  have : AlgebraicGeometry.IsProjectiveVariety k sT := hTp
  have := NumericalCurveClasses.finiteDimensional_of_isProjectiveVariety sT
  refine ⟨Module.finrank ℝ (NumericalCurveClasses sT), ?_⟩
  intro S' sS' σ hS' hdim' hσs hσp hσb
  -- the schemes `S`, `S'`, `T` and `T° = U`
  have hSv : AlgebraicGeometry.IsVariety k sS := hS.1
  have hS'v : AlgebraicGeometry.IsVariety k sS' := hS'.1
  have : IsIntegral S := hSv.toIsIntegral
  have : IsIntegral S' := hS'v.toIsIntegral
  have : IsNormal S := hS.2
  have : IsNormal S' := hS'.2
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  have : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian sS'
  have hTv : AlgebraicGeometry.IsVariety k sT := hTp.toIsVariety
  have : IsIntegral T := hTv.toIsIntegral
  have hTs : IsSmoothScheme sT := MMP.Mori.isSmoothScheme_of_smooth hTsm
  obtain ⟨_, _⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hTs
  have : Nonempty U := (IsBirationalMorphism.isDominant hτb).denseRange.nonempty
  have hUv : AlgebraicGeometry.IsVariety k (U.ι ≫ sT) :=
    Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι k sT U
  have : IsIntegral U := hUv.toIsIntegral
  have : IsNormal U := isNormal_of_isOpenImmersion U.ι
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sT)
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sT)
  have : IsNoetherian U := {}
  have hUdim : topologicalKrullDim U = 2 := by
    rw [Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_opens k sT U, hTdim]
  have hUs := MMP.Threefold.Resolution.isSmoothScheme_ι k hTs U
  -- the morphisms
  have hτb' := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hτb
  have hσb' := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hσb
  have hfb : IsBirationalMorphism (τ ≫ σ) := isBirationalMorphism_comp_of_isBirational σ τ hσb' hτb'
  have hfs : (τ ≫ σ) ≫ sS' = U.ι ≫ sT := by rw [Category.assoc, hσs, hcomm]
  -- every injective family of contracted curves has at most `dim N₁(T)` members
  refine NormalSurfaceContractionBound.encard_le_of_forall_injective fun n E hEinj hE => ?_
  choose ξ hξS hξh hξp hξc using fun i =>
    NormalSurfaceContractionBound.exists_point_of_isExceptionalCurve sS' (U.ι ≫ sT) τ hτb' σ
      (by rw [← Category.assoc, hfs]) hUdim hdim (hE i)
  -- the strict transforms, as prime divisors and proper curves of `T°`
  let P : Fin n → MMP.Mori.PrimeDivisor U := fun i => PrimeDivisor.ofCoheightOne (ξ i) (hξh i)
  let C : Fin n → ProperCurve (U.ι ≫ sT) := fun i => ⟨ξ i, hξp i⟩
  have hPgen : ∀ i, (P i).genericPoint = ξ i := fun i =>
    PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hPinj : Function.Injective P := by
    intro i j hij
    have hξij : ξ i = ξ j := by rw [← hPgen i, ← hPgen j, hij]
    apply hEinj
    have := (hE i).1.1
    have := (hE j).1.1
    rw [← vanishingIdeal_support_eq_self (E i), ← vanishingIdeal_support_eq_self (E j)]
    congr 1
    apply Closeds.ext
    rw [← hξS i, ← hξS j, hξij]
  have hpos := MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism
    hUv hUs hUdim hS'v hfs hfb P hPinj C (fun i => (hPgen i).symm)
    (fun i y hy => by simpa using hξc i y hy)
  -- the same curves and divisors on `T`
  choose CT hCT hclT using fun i =>
    NormalSurfaceContractionBound.exists_properCurve_of_opens sT U (C i)
  let PT : Fin n → MMP.Mori.PrimeDivisor T := fun i => OpenWeilRestriction.primeDivisorMap U.ι (P i)
  haveI := fun i => MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme
    hTs (PT i)
  let L : Fin n → T.Modules := fun i => Stacks.Divisors.invertibleSheaf' (PT i).idealSheaf
  let φ : Fin n → NumericalCurveClasses sT →ₗ[ℝ] ℝ := fun i =>
    NumericalCurveClasses.degree sT (L i)
  let z : Fin n → NumericalCurveClasses sT := fun j => OneCycle.numericalClass sT ((CT j).cycle ℝ)
  haveI := fun j => (C j).isProper_ι_comp
  have hmat : (Matrix.of fun i j => φ i (z j)) = Matrix.of fun i j : Fin n =>
      ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k (U.ι ≫ sT) (C j).ι
        (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hUs (P i)) : ℝ) := by
    ext i j
    simp only [Matrix.of_apply, φ, z, NumericalCurveClasses.degree_numericalClass,
      OneCycle.degree_cycle]
    rw [MMP.Threefold.Resolution.intersectionNumber_restrict_open k hTs U (PT i) (P i) rfl (CT j)
      (C j) (hCT j) (hclT j),
      MMP.Threefold.Resolution.intersectionNumber_single_eq_degreeOn_invertibleSheaf' k hTs (PT i)
        (CT j)]
    rfl
  have hu : IsUnit (Matrix.of fun i j => φ i (z j)) := by
    rw [hmat]; simpa using hpos.isUnit.neg
  have hli : LinearIndependent ℝ z :=
    (Matrix.linearIndependent_cols_of_isUnit hu).of_comp (LinearMap.pi φ)
  simpa using hli.fintype_card_le_finrank

end MMP.Mori
