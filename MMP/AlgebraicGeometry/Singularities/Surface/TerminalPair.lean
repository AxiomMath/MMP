module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Singularities.Surface.CanonicalMinimalResolutionCrepant
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolution
import MMP.AlgebraicGeometry.Singularities.RamifiedCyclicCover
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupNumericalDiscrepancy
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowup
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicTopology.PoincareDualityGoodCover
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry

/-!
# Terminal surface pairs

Let `(x ∈ X)` be a surface germ over an algebraically closed field `k` of characteristic zero:
a normal surface, smooth away from the closed point `x`. Let `Δ` be an effective `ℚ`-divisor and
`K_X` a canonical divisor with `K_X + Δ` `ℚ`-Cartier. Then `(X, Δ)` is terminal near `x` if and
only if `X` is smooth at `x` and `mult_x Δ < 1`.

*Terminal implies smooth.* On a neighbourhood `U` where `(U, Δ|_U)` is terminal, the pair is
canonical, so every exceptional curve of the minimal resolution of `U` has discrepancy `0`. That
contradicts `discrep > 0`, so the minimal resolution has no exceptional curve and `x` is a smooth
point. The blow-up of `x` then has exceptional curve `F` with `a(F) = 1 - mult_x Δ > 0`.

*Smooth with `mult_x Δ < 1` implies terminal.* The locus where the multiplicity of `Δ` is `≥ 1`
is closed, and the multiplicities `< 1` take finitely many values. So there are a neighbourhood
`U` of `x` and `μ < 1` with `mult_p Δ ≤ μ` at every point of `U`. For an exceptional divisor `E`
over `U`, blow up its centres successively. If the centre on the `n`-th blow-up `Yₙ` is the
closed point `cₙ`, the crepant boundary `Θₙ` of `(U, Δ)` on `Yₙ` satisfies `Θₙ ≤ Aₙ`, where `Aₙ`
is the strict transform of `Δ` and `mult_{cₙ} Aₙ ≤ μ`. The exceptional curve `F` of the blow-up of
`cₙ` has discrepancy `1 - mult_{cₙ} Θₙ ≥ 1 - μ`. If `a(E) < 1 - μ`, then every centre stays a
closed point, because the alternative is that `E` is the divisor `F`. Zariski's theorem forbids
such an infinite tower. Hence `discrep(U, Δ|_U) ≥ 1 - μ > 0`.

## Main results

* `MMP.Mori.IsSurfaceGerm.holdsOnGerm_isTerminalPair_iff`: a surface germ with effective boundary
  is terminal near its point exactly when it is smooth there and the boundary has multiplicity
  `< 1` there.

## Implementation notes

"Terminal near `x`" is `MMP.Mori.HoldsOnGerm {x}` applied to the property that, on the open
neighbourhood `U`, the pair `(U, Δ|_U)` with canonical divisor `K_X|_U` is terminal
(`MMP.Mori.IsTerminalPair`), restrictions taken by `MMP.Mori.DivisorWithCoeffs.restrictOpen`.
The terminal property is stated for a fixed canonical divisor `K_X` of `X`.

The induction on the number of blow-ups is replaced by an infinite tower: under the assumption
`a(E) < 1 - μ` the tower of blow-ups at the centres of `E` never ends, which contradicts the
theorem that a sequence of blow-ups at the centres of a divisorial valuation reaches the divisor.
Each step blows up the open subscheme `⊤` of the previous surface, the form in which that theorem
is stated. Discrepancies are carried down the tower by crepant invariance (Kollár–Mori 2.30) and
by restriction to open subschemes.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  Theorem 4.5(1).
-/

universe u

namespace MMP.Mori.TerminalSurfacePairs

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MMP.Threefold.Resolution
  (blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection)

section InverseTransformIso

variable {X Y : Scheme.{u}}

/-- The biregular locus of an isomorphism is everything. -/
private theorem biregularLocus_eq_top_of_isIso (g : Y ⟶ X) [IsIso g] : biregularLocus g = ⊤ :=
  top_le_iff.mp (le_biregularLocus ((isBiregular_top_iff g).mpr inferInstance))

/-- Under an isomorphism `g`, the inverse transform of a closed subset is its preimage. -/
private theorem coe_inverseTransform_of_isIso (g : Y ⟶ X) [IsIso g] (Z : Closeds X) :
    (inverseTransform g Z : Set Y) = g ⁻¹' (Z : Set X) := by
  rw [inverseTransform, biregularLocus_eq_top_of_isIso, Closeds.coe_closure]
  simp only [Opens.coe_top, Set.inter_univ]
  exact (Z.isClosed.preimage g.continuous).closure_eq

/-- The ideal sheaf of a prime divisor is the vanishing ideal of its support. -/
private theorem idealSheaf_eq_vanishingIdeal_support (D : MMP.Mori.PrimeDivisor X) :
    D.idealSheaf = Scheme.IdealSheafData.vanishingIdeal D.idealSheaf.support := by
  have := D.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl

/-- Under an isomorphism `g`, `g⁻¹_* D = E` exactly when `E` is supported on `g⁻¹(D)`. -/
private theorem inverseTransformPrimeDivisor_eq_some_iff_of_isIso (g : Y ⟶ X) [IsIso g]
    (D : MMP.Mori.PrimeDivisor X) (E : MMP.Mori.PrimeDivisor Y) :
    inverseTransformPrimeDivisor g D = some E ↔ E.support = g ⁻¹' D.support := by
  rw [inverseTransformPrimeDivisor_eq_some_iff, biregularLocus_eq_top_of_isIso]
  have hne : (D.support ∩ ((⊤ : X.Opens) : Set X)).Nonempty := by
    have := D.integral
    obtain ⟨x⟩ : Nonempty D.idealSheaf.subscheme := inferInstance
    refine ⟨D.idealSheaf.subschemeι x, ?_, trivial⟩
    rw [AlgebraicGeometry.PrimeDivisor.support, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨x, rfl⟩
  simp only [hne, true_and]
  rw [inverseTransformIdeal]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congrArg (fun I ↦ (I.support : Set Y)) h
    simp only [Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    rw [AlgebraicGeometry.PrimeDivisor.support, this, coe_inverseTransform_of_isIso]
  · rw [idealSheaf_eq_vanishingIdeal_support E]
    congr 1
    ext1
    rwa [coe_inverseTransform_of_isIso]

/-- The inverse transform under the identity is the identity: `(𝟙_Y)⁻¹_* D = D`. -/
private theorem inverseTransformDivisor_id {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Y) :
    inverseTransformDivisor (𝟙 Y) D = D := by
  have : inverseTransformDivisor (R := R) (𝟙 Y) = AddMonoidHom.id _ := by
    refine Finsupp.addHom_ext fun P r ↦ ?_
    rw [AddMonoidHom.id_apply]
    exact inverseTransformDivisor_single_of_eq_some
      ((inverseTransformPrimeDivisor_eq_some_iff_of_isIso _ P P).mpr rfl) r
  exact DFunLike.congr_fun this D

end InverseTransformIso

/-! ### Restriction to open subschemes -/

open IsLocalRing in
private theorem map_le_pow_maximalIdeal_iff {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R →+* S) (he : Function.Bijective e) (I : Ideal R)
    (k : ℕ) : I.map e ≤ maximalIdeal S ^ k ↔ I ≤ maximalIdeal R ^ k := by
  have hm : (maximalIdeal R).map e = maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv (RingEquiv.ofBijective e he))
  rw [← hm, ← Ideal.map_pow]
  refine ⟨fun h ↦ ?_, Ideal.map_mono⟩
  have := Ideal.comap_mono (f := e) h
  rwa [Ideal.comap_map_of_bijective e he, Ideal.comap_map_of_bijective e he] at this

/-- The multiplicity of a prime divisor of an open subscheme at a point is that of its closure. -/
private theorem multiplicityAt_primeDivisorMap {V X : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j] (E' : MMP.Mori.PrimeDivisor V) (v : V) :
    E'.multiplicityAt v =
      MMP.Mori.PrimeDivisor.multiplicityAt (OpenWeilRestriction.primeDivisorMap j E') (j v) := by
  unfold PrimeDivisor.multiplicityAt
  simp only [Scheme.IdealSheafData.stalkIdeal_eq_stalk]
  rw [← MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap j E',
    MMP.Threefold.Mori.OpenRestriction.stalk_comap_eq_map]
  have : IsIso (j.stalkMap v) := (IsOpenImmersion.iff_isIso_stalkMap.mp ‹_›).2 v
  have hbij := ConcreteCategory.bijective_of_isIso (j.stalkMap v)
  refine iSup_congr fun k => iSup_congr_Prop ?_ fun _ => rfl
  exact map_le_pow_maximalIdeal_iff (j.stalkMap v).hom hbij _ k

/-- The multiplicity of the restriction of a `ℚ`-divisor to an open subscheme. -/
private theorem multiplicityAt_restrictOpen {X : Scheme.{u}} (U : X.Opens) (Δ : QDivisor X)
    (y : U) : (Δ.restrictOpen U).multiplicityAt y = Δ.multiplicityAt (U.ι y) := by
  classical
  unfold DivisorWithCoeffs.multiplicityAt
  rw [Finsupp.sum, Finsupp.sum]
  refine Finset.sum_bij_ne_zero (fun W _ _ => OpenWeilRestriction.primeDivisorMap U.ι W)
    (fun W hW _ => ?_) (fun W₁ _ _ W₂ _ _ h => OpenWeilRestriction.primeDivisorMap_injective _ h)
    (fun P hP hne => ?_) (fun W _ _ => ?_)
  · simpa [DivisorWithCoeffs.restrictOpen, Finsupp.mem_support_iff] using hW
  · have hmem : U.ι y ∈ P.support := by
      by_contra h
      rw [PrimeDivisor.multiplicityAt_eq_zero_of_notMem P h] at hne
      simp at hne
    obtain ⟨W, rfl⟩ :=
      MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support U.ι P y hmem
    refine ⟨W, ?_, ?_, rfl⟩
    · simpa [DivisorWithCoeffs.restrictOpen, Finsupp.mem_support_iff] using hP
    · rwa [multiplicityAt_primeDivisorMap U.ι W y, DivisorWithCoeffs.restrictOpen,
        Finsupp.comapDomain_apply]
  · rw [multiplicityAt_primeDivisorMap U.ι W y, DivisorWithCoeffs.restrictOpen,
      Finsupp.comapDomain_apply]

/-- The restriction of an effective divisor to an open subscheme is effective. -/
private theorem isEffective_restrictOpen {X : Scheme.{u}} (U : X.Opens) {Δ : QDivisor X}
    (hΔ : Δ.IsEffective) : (Δ.restrictOpen U).IsEffective := fun W => by
  simpa [DivisorWithCoeffs.coeff_restrictOpen] using hΔ _

/-- For `X` locally of finite presentation over `S`, a point of an open subscheme `U` is smooth
exactly when its image in `X` is. -/
private theorem mem_smoothLocus_ι_iff {X S : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFinitePresentation sX] (U : X.Opens) (y : U) :
    y ∈ smoothLocus (U.ι ≫ sX) ↔ U.ι y ∈ smoothLocus sX := by
  rw [smoothLocus_eq_smoothLocus, smoothLocus_eq_smoothLocus,
    ← Scheme.Hom.preimage_smoothLocus_eq]
  rfl

/-- An open subscheme of a smooth scheme is smooth. -/
private theorem isSmoothScheme_ι {X S : Scheme.{u}} {sX : X ⟶ S}
    [LocallyOfFinitePresentation sX] (h : IsSmoothScheme sX) (U : X.Opens) :
    IsSmoothScheme (U.ι ≫ sX) :=
  eq_top_iff.2 fun y _ => (mem_smoothLocus_ι_iff sX U y).2 (by rw [h]; trivial)

/-- A scheme smooth at `x` and at every other point is smooth. -/
private theorem isSmoothScheme_of_forall_ne {X S : Scheme.{u}} {sX : X ⟶ S} {x : X}
    (hx : x ∈ smoothLocus sX) (h : ∀ y, y ≠ x → y ∈ smoothLocus sX) : IsSmoothScheme sX :=
  eq_top_iff.2 fun y _ => (em (y = x)).elim (fun hy => hy ▸ hx) (h y)

/-- The identity contracts no curve. -/
private theorem not_isExceptionalCurve_id {T : Scheme.{u}} (C : T.IdealSheafData) :
    ¬ IsExceptionalCurve (𝟙 T) C := by
  rintro ⟨⟨-, hdim⟩, x, hx⟩
  have hs : (C.support : Set T) = {x} := by rw [← hx]; ext; simp
  have hsub : Subsingleton C.subscheme := by
    refine ⟨fun a b => ?_⟩
    apply C.subschemeι.isEmbedding.injective
    have ha : C.subschemeι a ∈ (C.support : Set T) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨a, rfl⟩
    have hb : C.subschemeι b ∈ (C.support : Set T) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨b, rfl⟩
    rw [hs] at ha hb
    exact ha.trans hb.symm
  have : DiscreteTopology C.subscheme := @Subsingleton.discreteTopology _ _ hsub
  have := topologicalKrullDim_zero_of_discreteTopology C.subscheme
  rw [hdim] at this
  exact absurd this (by decide)

/-- On a smooth scheme, `0` solves the numerical pull-back equations on the identity. -/
private theorem isNumericalPullbackSolution_id {k : Type u} [Field k] {T : Scheme.{u}}
    {sT : T ⟶ Spec (.of k)} [QuasiCompact (𝟙 T ≫ sT)] [IsLocallyNoetherian T] [IsNormal T]
    (hTs : IsSmoothScheme sT) {K : Divisor T} {n : ℕ} (hK : K.IsCanonicalDivisor sT n)
    (Θ : QDivisor T) :
    IsNumericalPullbackSolution sT (𝟙 T) K Θ 0 := by
  refine ⟨⟨inferInstance, isBirationalMorphism_of_isIso _, by rwa [Category.id_comp]⟩,
    ⟨n, by rwa [Category.id_comp]⟩, by simp,
    fun Ej hEj => absurd hEj (not_isExceptionalCurve_id _)⟩

/-- In a quasi-compact scheme of dimension at most two, a point of coheight at least two is
closed. -/
private theorem isClosed_of_two_le_coheight {X : Scheme.{u}} [CompactSpace X]
    (hdim : topologicalKrullDim X ≤ 2) {x : X} (hx : 2 ≤ Order.coheight x) :
    IsClosed ({x} : Set X) := by
  by_contra hcl
  obtain ⟨c, -, hxc, hne⟩ := exists_isClosed_singleton_specializes hcl
  obtain ⟨p, hp, hl⟩ := Order.exists_series_of_le_coheight x (n := 2) (by exact_mod_cast hx)
  let cl : X → TopologicalSpace.IrreducibleCloseds X := fun z =>
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hlt : ∀ {z w : X}, z < w → cl z < cl w := by
    intro z w h
    have hsub : ∀ {z w : X}, z ≤ w → (closure {z} : Set X) ⊆ closure {w} := fun h =>
      closure_minimal (Set.singleton_subset_iff.mpr
        (specializes_iff_mem_closure.mp (Scheme.le_iff_specializes.mp h))) isClosed_closure
    refine lt_of_le_not_ge (hsub h.le) fun hle => h.2 ?_
    exact Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr
      ((hle : (closure {w} : Set X) ⊆ closure {z}) (subset_closure rfl)))
  have hcx : c < x := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hxc)
    fun h => hne (hxc.antisymm (Scheme.le_iff_specializes.mp h)).eq
  have h0 : x < p ⟨1, by omega⟩ := by
    rw [← hp]
    exact p.step ⟨0, by omega⟩
  have h1 : p ⟨1, by omega⟩ < p ⟨2, by omega⟩ := p.step ⟨1, by omega⟩
  exact false_of_lt_lt_lt_of_topologicalKrullDim_le_two hdim (hlt hcx) (hlt h0) (hlt h1)

/-- On a resolution of a normal surface, a prime divisor is exceptional exactly when it is an
exceptional curve. -/
private theorem isExceptional_iff_isExceptionalCurve {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {f : Y ⟶ X}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsSmoothResolution sX f) (F : MMP.Mori.PrimeDivisor Y) :
    RationalMap.IsExceptional (X := Y) f.toRationalMap F ↔ IsExceptionalCurve f F.idealSheaf := by
  obtain ⟨hYv, hdimY, -⟩ := hf.isNormalVariety hX
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
  have hη : F.genericPoint ∈ (F.idealSheaf.support : Set Y) := by
    change F.genericPoint ∈ F.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have himg : f '' (F.idealSheaf.support : Set Y) ⊆ closure {f F.genericPoint} := by
    change f '' F.support ⊆ _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have := image_closure_subset_closure_image (f := f) (s := {F.genericPoint}) f.continuous
    rwa [Set.image_singleton] at this
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h2 := h _ (subset_closure ⟨_, hη, rfl⟩)
    have hcl := isClosed_of_two_le_coheight (by rw [hdim]) h2
    refine ⟨MMP.Flips.isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hYv.1
      (hdimY.trans hdim) F, f F.genericPoint, ?_⟩
    apply Set.Subset.antisymm
    · rwa [hcl.closure_eq] at himg
    · rintro _ rfl
      exact ⟨_, hη, rfl⟩
  · rintro ⟨-, x, hx⟩ y hy
    have hxcl : IsClosed ({x} : Set X) := by
      rw [← hx]; exact f.isClosedMap _ F.idealSheaf.support.isClosed
    have hy' : y ∈ closure (f.base '' (F.idealSheaf.support : Set Y)) := hy
    rw [hx, hxcl.closure_eq] at hy'
    rw [Set.mem_singleton_iff.mp hy']
    exact (MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hX.1 hdim hxcl).ge

/-- Two divisors over `X` with equal morphisms are equal. -/
private theorem divisorOver_mk_congr {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {g g' : Y ⟶ X} (h : g = g') (hY : IsNormalVariety k (g ≫ sX))
    (hb : IsBirationalMorphism g) (hY' : IsNormalVariety k (g' ≫ sX))
    (hb' : IsBirationalMorphism g') (E : MMP.Mori.PrimeDivisor Y) :
    (⟨Y, g, hY, hb, E⟩ : DivisorOver k sX) = ⟨Y, g', hY', hb', E⟩ := by
  subst h; rfl

/-- **The discrepancy of the blow-up of a point of a smooth surface.** For the blow-up of a
closed point `p` of a smooth surface `T`, with exceptional curve `F`, `a(F, T, Θ) = 1 - mult_p Θ`
for every `ℚ`-divisor `Θ`. -/
private theorem isDiscrepancy_blowUp_singleton {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {T : Scheme.{u}} {sT : T ⟶ Spec (.of k)} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T]
    (hT : IsNormalVariety k sT) (hTs : IsSmoothScheme sT) (hTd : topologicalKrullDim T = 2)
    {K : Divisor T} (hK : K.IsCanonicalDivisor sT 2) (Θ : QDivisor T) {p : T}
    (hp : IsClosed ({p} : Set T)) :
    ∃ (hY : IsNormalVariety k
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sT))
      (hb : IsBirationalMorphism (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)))
      (F : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))),
      F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ∧
      (⟨_, _, hY, hb, F⟩ : DivisorOver k sT).IsExceptional ∧
      IsDiscrepancy sT 2 K Θ ⟨_, _, hY, hb, F⟩ (1 - Θ.multiplicityAt p) ∧
      IsProper (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) ∧
      IsSmoothScheme (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sT) ∧
      topologicalKrullDim (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) = 2 ∧
      ∀ C, IsExceptionalCurve (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) C ↔
        C = F.idealSheaf := by
  set π := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
  have hTv := hT.1
  obtain ⟨-, hprop, hbir, -, F, hF, -⟩ :=
    blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection
      hTv hTs hTd hp
  have hYs := MMP.Threefold.Resolution.isSmoothScheme_blowUp_singleton hTv hTs hTd hp
  haveI := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
  haveI := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
  have hvar := MMP.Threefold.Resolution.isVariety_blowUp_singleton hTv hTd hp
  haveI : QuasiCompact (𝟙 T ≫ sT) := by rw [Category.id_comp]; exact hTv.toQuasiCompact
  have ha := isNumericalPullbackSolution_id (sT := sT) hTs hK Θ
  have hvar' : MMP.Mori.IsVariety k ((π ≫ 𝟙 T) ≫ sT) := by simpa using hvar
  haveI : AlgebraicGeometry.IsVariety k ((π ≫ 𝟙 T) ≫ sT) := hvar'
  have hYs' : IsSmoothScheme ((π ≫ 𝟙 T) ≫ sT) := by simpa using hYs
  have hres : IsSmoothResolution sT (π ≫ 𝟙 T) :=
    ⟨by simpa using hprop, by simpa using hbir, hYs'⟩
  have hYd : topologicalKrullDim (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) = 2 :=
    (hres.isNormalVariety hT).2.1.trans hTd
  haveI : CompactSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) :=
    QuasiCompact.compactSpace_of_compactSpace ((π ≫ 𝟙 T) ≫ sT)
  obtain ⟨K', hK'⟩ := exists_isCanonicalDivisor_of_isSmoothScheme ((π ≫ 𝟙 T) ≫ sT) hYs'
    (n := 2) (by exact_mod_cast hYd)
  obtain ⟨hiff, hsol⟩ := ha.isNumericalPullbackSolution_blowUpToBase_comp hT hTd hp hF ⟨2, hK'⟩
  have hE : IsExceptionalCurve (π ≫ 𝟙 T) F.idealSheaf := (hiff _).2 (Or.inr rfl)
  have hval : (inverseTransformDivisor π (0 : QDivisor T) +
      Finsupp.single F (1 - (logPullback (𝟙 T) Θ 0).multiplicityAt p)) F =
        1 - Θ.multiplicityAt p := by
    simp only [logPullback, map_zero, sub_zero, zero_add, Finsupp.single_eq_same]
    exact congrArg (fun D : QDivisor T => 1 - D.multiplicityAt p)
      (inverseTransformDivisor_id Θ)
  have hP : IsPair sT Θ := ⟨hT, 2, K, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hTs _⟩
  have hd := (isNumericalDiscrepancy_iff_isDiscrepancy hP hTd hK hsol.1 hK' hE _).1
    ⟨hE, _, hsol, hval⟩
  have hexc := (isExceptional_iff_isExceptionalCurve hT hTd hsol.1 F).2 hE
  have hY : IsNormalVariety k (π ≫ sT) := by
    simpa using (hsol.1.isNormalVariety hT).1
  have hb : IsBirationalMorphism π := by simpa using hsol.1.isBirationalMorphism
  rw [divisorOver_mk_congr (Category.comp_id π) _ _ hY hb] at hd
  refine ⟨hY, hb, F, hF, ?_, hd, hprop, hYs, hYd, fun C => ?_⟩
  · change RationalMap.IsExceptional (X := _) π.toRationalMap F
    simpa using hexc
  · have h := hiff C
    rw [Category.comp_id] at h
    rw [h]
    refine ⟨?_, Or.inr⟩
    rintro (⟨E, hE, -⟩ | h)
    exacts [absurd hE (not_isExceptionalCurve_id _), h]

/-! ### Canonical divisors on open subschemes -/

section OpenRestriction

open Opposite

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an irreducible scheme is dense. -/
private theorem isDominant_opens_ι {Y : Scheme.{u}} [IrreducibleSpace Y] (V : Y.Opens)
    [Nonempty V] : IsDominant V.ι :=
  Opens.isDominant_ι (V.isOpen.dense ⟨_, (Classical.arbitrary V).2⟩)

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- A nonempty open subscheme of a variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
private theorem topologicalKrullDim_opens_eq (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-! ### The divisorial sheaf on an open subscheme -/

section DivisorialRestrict

/-- On an irreducible scheme every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {Y : Scheme.{u}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem genericPoint_specializes {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem specializes_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (MMP.Fourfold.componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective (Y.presheaf.stalkSpecializes (genericPoint_specializes Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom h
  rwa [TopCat.Presheaf.stalkSpecializes_comp_apply,
    TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at this

private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hsp : genericPoint U.toScheme ⤳ x := (genericPoint_spec U.toScheme).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The unique irreducible component `Y` of an irreducible scheme `Y`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]; exact h⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, TopCat.Presheaf.stalkSpecializes_comp_apply,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap U.ι).injective h1)

private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom
      ((X.presheaf.stalkSpecializes (specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply]

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    Divisor.IsDivisorialSection (D.restrictOpen U) V (restrictRF U V ψ) ↔
      D.IsDivisorialSection (U.ι ''ᵁ V) ψ := by
  have key : ∀ (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF]
    rw [evFF_restrictRF U V ψ _ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective,
      DivisorWithCoeffs.coeff_restrictOpen]
    rfl
  have hmem : ∀ E' : MMP.Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff, ← MMP.Mori.PrimeDivisor.genericPoint_mem_iff,
      show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    refine ⟨fun h ↦ ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨x, hx, hxe⟩
    rwa [U.ι.isOpenEmbedding.injective hxe] at hx
  refine ⟨fun h P hP ↦ ?_, fun h E' hE' ↦
    (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))⟩
  have hPU : P.genericPoint ∈ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
    rw [← hx]
    exact x.2
  obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
  exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))

private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

private theorem restrictRF_add (V : U.toScheme.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V (ψ₁ + ψ₂) = restrictRF U V ψ₁ + restrictRF U V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction `𝒪_X(D)|_U ⟶ 𝒪_U(D|_U)` of divisorial sections to an open subscheme. -/
private noncomputable def divisorialSheafRestrictHom (D : Divisor X) :
    D.divisorialSheaf.restrict U.ι ⟶ Divisor.divisorialSheaf (D.restrictOpen U) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun ψ := (⟨restrictRF U V.unop (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).1,
            (isDivisorialSection_restrictRF_iff U D V.unop _).2
              (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).2⟩ :
              Divisor.divisorialSubmodule (D.restrictOpen U) V.unop)
          map_zero' := Subtype.ext (restrictRF_zero U V.unop)
          map_add' ψ₁ ψ₂ := Subtype.ext (restrictRF_add U V.unop _ _) }
      naturality V V' i := by ext ψ; rfl }
    fun V r ψ => Subtype.ext (restrictRF_smul U V.unop r _)⟩

private theorem isIso_divisorialSheafRestrictHom (D : Divisor X) :
    IsIso (divisorialSheafRestrictHom U D) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun (ψ₁ ψ₂ : D.divisorialSubmodule (U.ι ''ᵁ V)) h => ?_, fun φ => ?_⟩
  · have h' : restrictRF U V ψ₁.1 = restrictRF U V ψ₂.1 := congrArg Subtype.val h
    exact Subtype.ext (restrictRF_injective U V h')
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective U V (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff U D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).2)⟩ :
        D.divisorialSubmodule (U.ι ''ᵁ V)), Subtype.ext hψ⟩

end DivisorialRestrict

/-- The divisorial sheaf of the restriction `D|_U` of a divisor to an open subscheme is the
restriction `𝒪_X(D)|_U` of its divisorial sheaf. -/
private theorem nonempty_divisorialSheaf_restrictOpen_iso (D : Divisor X) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] :
    Nonempty (Divisor.divisorialSheaf (D.restrictOpen U) ≅ D.divisorialSheaf.restrict U.ι) :=
  ⟨(@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom U D)).symm⟩

/-- Relative differential forms restrict along an open immersion: for `ψ : Z ⟶ Y` an open
immersion and `p' = ψ ≫ p`, `(Ω^n_{Y/S})|_Z ≅ Ω^n_{Z/S}`. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (p' : Z ⟶ S) (h : ψ ≫ p = p') (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  have hc : ψ ≫ p = p' ≫ 𝟙 S := by rw [h, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p p' (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' (𝟙 S) hc n)⟩

/-- The smooth locus of an open subscheme `U ⊆ X` lies in the smooth locus of `X`. -/
private theorem range_smoothLocus_subset (U : X.Opens) :
    Set.range ((smoothLocus (U.ι ≫ sX)).ι ≫ U.ι) ⊆ Set.range (smoothLocus sX).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  obtain ⟨W, hxW, hW⟩ := mem_smoothLocus_iff.1 x.2
  let V := (W.ι ≫ U.ι).opensRange
  have e : (W.ι ≫ U.ι).isoOpensRange.inv ≫ (W.ι ≫ U.ι) = V.ι := by
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  have hV : Smooth (V.ι ≫ sX) := by
    rw [← e, Category.assoc, Category.assoc]
    infer_instance
  exact le_smoothLocus sX hV ⟨⟨x.1, hxW⟩, rfl⟩

/-- On the smooth locus of a nonempty open subscheme `U`, the divisorial sheaf of `K|_U` is the
canonical sheaf when that of `K` is on the smooth locus of `X`. -/
private theorem nonempty_restrict_smoothLocus_iso {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (U : X.Opens) [Nonempty U] [IsDominant U.ι] :
    Nonempty ((Divisor.divisorialSheaf (K.restrictOpen U)).restrict (smoothLocus (U.ι ≫ sX)).ι ≅
      canonicalSheaf (U.ι ≫ sX) n) := by
  obtain ⟨e₀⟩ := nonempty_divisorialSheaf_restrictOpen_iso K U
  let T := smoothLocus (U.ι ≫ sX)
  let S := smoothLocus sX
  let ψ : T.toScheme ⟶ S := IsOpenImmersion.lift S.ι (T.ι ≫ U.ι) (range_smoothLocus_subset U)
  have hψ : ψ ≫ S.ι = T.ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso ψ (S.ι ≫ sX)
    (T.ι ≫ U.ι ≫ sX) (by rw [← Category.assoc, hψ, Category.assoc]) n
  exact ⟨(Scheme.Modules.restrictFunctor T.ι).mapIso e₀ ≪≫
    (Scheme.Modules.restrictFunctorComp T.ι U.ι).symm.app _ ≪≫
    (Scheme.Modules.restrictFunctorCongr hψ.symm).app _ ≪≫
    (Scheme.Modules.restrictFunctorComp ψ S.ι).app _ ≪≫
    (Scheme.Modules.restrictFunctor ψ).mapIso hK.iso ≪≫ e₁⟩

/-- The restriction of a canonical divisor to a nonempty open subscheme is canonical. -/
private theorem isCanonicalDivisor_restrictOpen {n : ℕ} {K : Divisor X}
    (hX : IsNormalVariety k sX) (hK : K.IsCanonicalDivisor sX n) (U : X.Opens) [Nonempty U]
    [IsDominant U.ι] :
    Divisor.IsCanonicalDivisor (U.ι ≫ sX) n (K.restrictOpen U) :=
  ⟨(topologicalKrullDim_opens_eq hX U).trans hK.1, nonempty_restrict_smoothLocus_iso hK U⟩

end OpenRestriction

/-! ### Divisors over a birational model -/

section Comp

variable {k : Type u} [Field k]

/-- A divisor `(W, g, F)` over `Y`, for a birational morphism `f : Y ⟶ X` of varieties, regarded
as the divisor `(W, f ∘ g, F)` over `X`. -/
private noncomputable def compDivisorOver {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (E : DivisorOver k (f ≫ sX)) : DivisorOver k sX :=
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI := E.isIntegral
  { Y := E.Y
    f := E.f ≫ f
    isNormalVariety := by rw [Category.assoc]; exact E.isNormalVariety
    isBirationalMorphism := isBirationalMorphism_comp E.isBirationalMorphism hf
    E := E.E }

/-- The valuation of `(W, f ∘ g, F)` is that of `(W, g, F)`, read on `k(X)` through `f^*`. -/
private theorem valuation_compDivisorOver {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (E : DivisorOver k (f ≫ sX)) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : IsDominant f := hf.isDominant
    (compDivisorOver f hY hf E).valuation = E.valuation.comap (functionFieldMap f) := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsDominant f := hf.isDominant
  have := E.isIntegral
  have := E.isDominant
  have := E.isNormal
  have := E.isLocallyNoetherian
  ext t
  change E.E.divisorialValuation (functionFieldMap (E.f ≫ f) t) =
    E.E.divisorialValuation (functionFieldMap E.f (functionFieldMap f t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

end Comp

/-! ### Transferring discrepancies to the base -/

section Transfer

open scoped WithZero

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]

/-- Valuations agreeing after composition with a surjective ring map agree. -/
private theorem valuation_eq_of_comap_eq {R S : Type*} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : Function.Surjective f) {v w : Valuation S ℤᵐ⁰}
    (h : v.comap f = w.comap f) : v = w := by
  ext x
  obtain ⟨y, rfl⟩ := hf x
  exact congrArg (fun u : Valuation R ℤᵐ⁰ => u y) h

/-- **Discrepancies over an open subscheme.** A discrepancy of a divisor `E` over a nonempty open
`W` of `(Y, Θ)`, for `K|_W` and `Θ|_W`, is the discrepancy of `E` regarded as a divisor over
`Y`. -/
private theorem isDiscrepancy_compDivisorOver_ι {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ} {K : Divisor Y}
    {Θ : QDivisor Y} (hP : IsPairWith s n K Θ) (W : Y.Opens) [Nonempty W]
    (hPW : IsPairWith (W.ι ≫ s) n (K.restrictOpen W) (Θ.restrictOpen W))
    (hW : IsNormalVariety k (W.ι ≫ s)) (hb : IsBirationalMorphism W.ι)
    (E : DivisorOver k (W.ι ≫ s)) {b : ℚ}
    (hE : IsDiscrepancy (W.ι ≫ s) n (K.restrictOpen W) (Θ.restrictOpen W) E b) :
    IsDiscrepancy s n K Θ (compDivisorOver W.ι hW hb E) b := by
  haveI := isDominant_opens_ι W
  set E₁ := compDivisorOver W.ι hW hb E with hE₁
  obtain ⟨b₁, hb₁⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hP.2.1 E₁
  have hcen : ((E₁.center : Set Y) ∩ W).Nonempty := by
    refine ⟨E₁.f E₁.E.genericPoint, ?_, ?_⟩
    · rw [E₁.center_eq_closure_genericPoint]; exact subset_closure rfl
    · change W.ι (E.f E.E.genericPoint) ∈ W
      exact (E.f E.E.genericPoint).2
  obtain ⟨hY', hf', E', -, hval, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hP E₁ W hcen
  have hb₁' := (hiff b₁).1 hb₁
  have hv : (⟨_, E₁.f ∣_ W, hY', hf', E'⟩ : DivisorOver k (W.ι ≫ s)).valuation = E.valuation := by
    have h1 := valuation_compDivisorOver W.ι hW hb E
    rw [← hE₁, hval] at h1
    exact valuation_eq_of_comap_eq (functionFieldMap_opens_ι_bijective W).2 h1
  have := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPW hv hb₁' hE
  rwa [this] at hb₁

/-- **Discrepancies over a model with a crepant boundary.** If `Θ_Y` is the crepant boundary of
`(X, Δ)` on a birational model `f : Y ⟶ X`, a discrepancy of a divisor `E` over `(Y, Θ_Y)` is the
discrepancy of `E` regarded as a divisor over `X`. -/
private theorem isDiscrepancy_compDivisorOver_of_isCrepantBoundary {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hP : IsPair sX Δ) (hK : K.IsCanonicalDivisor sX n) (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor (f ≫ sX) n) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) (E : DivisorOver k (f ≫ sX)) {b : ℚ}
    (hE : IsDiscrepancy (f ≫ sX) n KY ΔY E b) :
    IsDiscrepancy sX n K Δ (compDivisorOver f hY hf E) b :=
  ((hP.isDiscrepancy_iff_of_crepant f hY hf hK hKY (Or.inl hΔY)).2 E _
    (valuation_compDivisorOver f hY hf E) b).1 hE

end Transfer

/-! ### Centres of valuations on blow-ups -/

section Centre

open MMP.Flips
open scoped WithZero

/-- A valuation `ν'` of `k(X')` is a divisor of `k(X')` if its restriction `ν` along a morphism
`f : X' ⟶ X` inducing an isomorphism of function fields is a divisor of `k(X)`. -/
private theorem isDivisorOfFunctionField_of_comap {k : Type u} [Field k] {X X' : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral X'] (f : X' ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {ν : Valuation X.functionField ℤᵐ⁰}
    {ν' : Valuation X'.functionField ℤᵐ⁰} (hν : ν'.comap (functionFieldMap f) = ν)
    (h : IsDivisorOfFunctionField k sX ν) : IsDivisorOfFunctionField k (f ≫ sX) ν' := by
  let := functionFieldAlgebra sX
  obtain ⟨Y, sY, hY, E, e, he⟩ := h
  let := functionFieldAlgebra (f ≫ sX)
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsNormal Y := hY.2
  have : IsLocallyNoetherian Y :=
    have := hY.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian sY
  let := functionFieldAlgebra sY
  refine ⟨Y, sY, hY, E, (functionFieldAlgEquiv sX f hf).symm.trans e, ?_⟩
  ext a
  obtain ⟨b, rfl⟩ := hf.2 a
  have hb : (functionFieldAlgEquiv sX f hf).symm (functionFieldMap f b) = b :=
    (functionFieldAlgEquiv sX f hf).symm_apply_apply b
  have h1 := congrArg (fun w : Valuation X.functionField ℤᵐ⁰ => w b) he
  have h2 := congrArg (fun w : Valuation X.functionField ℤᵐ⁰ => w b) hν
  simp only [Valuation.comap_apply] at h1 h2 ⊢
  rw [h2, h1]
  change _ = E.divisorialValuation (e ((functionFieldAlgEquiv sX f hf).symm _))
  rw [hb]
  rfl

/-- The blow-up of an open `U ⊆ X` of an integral scheme in an ideal sheaf whose support is not
all of `U` induces an isomorphism of function fields `k(X) ≅ k(Bl U)`. -/
private theorem functionFieldMap_bijective_blowUp {X : Scheme.{u}} [IsIntegral X] (U : X.Opens)
    (I : (U : Scheme.{u}).IdealSheafData) [IsIntegral (blowUp I)]
    [IsDominant (blowUpToBase I ≫ U.ι)] (hI : (I.support : Set U) ≠ Set.univ) :
    Function.Bijective (functionFieldMap (blowUpToBase I ≫ U.ι)) := by
  obtain ⟨u, hu⟩ := (Set.ne_univ_iff_exists_notMem _).1 hI
  let W := (blowUpToBase I) ⁻¹ᵁ I.support.compl
  have hW : (W : Set (blowUp I)).Nonempty := by
    let w := (asIso (blowUpToBase I ∣_ I.support.compl)).inv ⟨u, hu⟩
    exact ⟨w.1, w.2⟩
  have : IsOpenImmersion (W.ι ≫ blowUpToBase I ≫ U.ι) := by
    rw [← Category.assoc, ← morphismRestrict_ι]
    infer_instance
  exact functionFieldMap_bijective_of_isOpenImmersion _ W hW

/-- The image of the generic point of `E` is the generic point of the center of a divisor
`(Y, f, E)` over `X`. -/
private theorem isGenericPoint_center {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (D : ProperDivisorOver k sX) :
    IsGenericPoint (D.f D.E.genericPoint) (D.center : Set X) := by
  have := D.isProper
  rw [IsGenericPoint, ProperDivisorOver.coe_center,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure D.E,
    ← D.f.isClosedMap.closure_image_eq_of_continuous D.f.continuous, Set.image_singleton]

/-- The center of a divisor over an integral scheme `X` does not contain the generic point of
`X`: the valuation is nontrivial, so it does not dominate `𝒪_{X,η} = k(X)`. -/
private theorem genericPoint_notMem_center {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (D : ProperDivisorOver k sX) :
    genericPoint X ∉ (D.center : Set X) := by
  intro h
  have hx : genericPoint X = D.f D.E.genericPoint := by
    refine (genericPoint_spec X).eq ?_
    rw [IsGenericPoint, (isGenericPoint_center D).def]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec X).def]
    exact (D.center.isClosed.closure_subset_iff).2 (Set.singleton_subset_iff.2 h)
  obtain ⟨g, hg⟩ := MMP.Positivity.DivisorOver.exists_valuation_eq_exp_neg_one D.toDivisorOver
  obtain ⟨b, hb⟩ : ∃ b : X.presheaf.stalk (genericPoint X),
      @algebraMap _ X.functionField _ _ (stalkFunctionFieldAlgebra X (genericPoint X)) b = g⁻¹ :=
    ⟨g⁻¹, by
      rw [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl]
      rfl⟩
  have h1 := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D.toDivisorOver _ hx b
  have h3 : D.valuation g⁻¹ ≤ 1 := by
    convert h1 using 2
    exact hb.symm
  rw [map_inv₀, hg] at h3
  exact absurd h3 (by simp)

/-- Two ring maps out of a stalk `𝒪_{X,x}` agree once they induce the same morphism through
`Spec 𝒪_{X,x} ⟶ X`: on an affine neighbourhood, `Spec 𝒪_{X,x} ⟶ X` is `Spec` of the germ map
followed by an open immersion. -/
private theorem stalk_hom_ext_of_SpecMap {X : Scheme.{u}} {x : X} {A : CommRingCat.{u}}
    (φ φ' : X.presheaf.stalk x ⟶ A)
    (h : Spec.map φ ≫ X.fromSpecStalk x = Spec.map φ' ≫ X.fromSpecStalk x) : φ = φ' := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU => ?_
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  rw [← hW.fromSpecStalk_eq_fromSpecStalk hxW] at h
  change Spec.map φ ≫ Spec.map (X.presheaf.germ _ x hxW) ≫ hW.fromSpec =
    Spec.map φ' ≫ Spec.map (X.presheaf.germ _ x hxW) ≫ hW.fromSpec at h
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc] at h
  have : IsOpenImmersion hW.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec hW
  have : Mono hW.fromSpec := IsOpenImmersion.mono _
  have h' := Spec.map_injective ((cancel_mono hW.fromSpec).1 h)
  rw [← X.presheaf.germ_res (homOfLE hWU) x hxW, Category.assoc, Category.assoc, h']

/-- **Lifting the center along a blow-up.** If the restriction `ν` of a valuation `ν'` of the
function field of the blow-up `Bl U` of an open `U ⊆ X` dominates the local ring of a point
`x ∈ U`, then `ν'` dominates the local ring of some point of `Bl U` (valuative criterion of
properness for `Bl U ⟶ U`). -/
private theorem exists_dominated_point_blowUp {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (U : X.Opens) (I : (U : Scheme.{u}).IdealSheafData)
    [IsIntegral (blowUp I)] [IsDominant (blowUpToBase I ≫ U.ι)]
    (ν' : Valuation (blowUp I).functionField ℤᵐ⁰) (x : X) (hxU : x ∈ U)
    (h1 : ∀ a : X.presheaf.stalk x,
      ν'.comap (functionFieldMap (blowUpToBase I ≫ U.ι)) (algebraMap _ X.functionField a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      ν'.comap (functionFieldMap (blowUpToBase I ≫ U.ι)) (algebraMap _ X.functionField a) < 1) :
    ∃ x' : blowUp I, (∀ a : (blowUp I).presheaf.stalk x',
        ν' (algebraMap _ (blowUp I).functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal ((blowUp I).presheaf.stalk x'),
        ν' (algebraMap _ (blowUp I).functionField a) < 1 := by
  let g := blowUpToBase I ≫ U.ι
  let R := ν'.valuationSubring
  let K := (blowUp I).functionField
  let ψ : X.presheaf.stalk x →+* R :=
    ((functionFieldMap g).comp (algebraMap (X.presheaf.stalk x) X.functionField)).codRestrict R
      fun a => (ν'.mem_valuationSubring_iff _).2 (h1 a)
  have hψ : IsLocalHom ψ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hlt := h2 a ((IsLocalRing.mem_maximalIdeal _).2 hna)
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    have hb' : functionFieldMap g (algebraMap _ X.functionField a) * (b : K) = 1 :=
      congrArg Subtype.val hb
    have := mul_lt_one_of_lt_of_le hlt ((ν'.mem_valuationSubring_iff _).1 b.2)
    rw [Valuation.comap_apply, ← map_mul, hb', map_one] at this
    exact lt_irrefl _ this
  let i₂X : Spec (.of R) ⟶ X := Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x
  have hrange : Set.range i₂X ⊆ Set.range U.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hsp : X.fromSpecStalk x (Spec.map (CommRingCat.ofHom ψ) p) ⤳ x := by
      have := Set.mem_range_self (f := X.fromSpecStalk x) (Spec.map (CommRingCat.ofHom ψ) p)
      rwa [Scheme.range_fromSpecStalk] at this
    exact hsp.mem_open U.isOpen hxU
  let i₂ : Spec (.of R) ⟶ U := IsOpenImmersion.lift U.ι i₂X hrange
  have hi₂ : i₂ ≫ U.ι = i₂X := IsOpenImmersion.lift_fac _ _ _
  have hX : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hη : g (genericPoint (blowUp I)) ⤳ genericPoint X :=
    (Inseparable.of_eq (map_genericPoint_of_isDominant g)).specializes
  have hsq : (blowUp I).fromSpecStalk (genericPoint _) ≫ blowUpToBase I =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂ := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hi₂]
    change _ ≫ g = _
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk g,
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (hη.trans hX), ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    congr 2
    rw [← TopCat.Presheaf.stalkSpecializes_comp X.presheaf hη hX]
    ext a
    rfl
  have hex : ValuativeCriterion.Existence (blowUpToBase I) := by
    have h : IsProper (blowUpToBase I) := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq (blowUpToBase I) :=
    { R := R
      K := K
      i₁ := (blowUp I).fromSpecStalk (genericPoint _)
      i₂ := i₂
      commSq := ⟨hsq⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l =
      (blowUp I).fromSpecStalk (genericPoint _) := hl₁
  set x' := l (IsLocalRing.closedPoint R)
  have hgx' : genericPoint (blowUp I) ⤳ x' := (genericPoint_spec _).specializes trivial
  have key : Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap R K) =
      (blowUp I).presheaf.stalkSpecializes hgx' := by
    apply stalk_hom_ext_of_SpecMap
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Spec.map_comp_assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁']
  have hval : ∀ a : (blowUp I).presheaf.stalk x',
      algebraMap _ (blowUp I).functionField a =
        ((Scheme.stalkClosedPointTo l).hom a : K) := fun a =>
    (congrArg (fun φ => φ.hom a) key).symm
  refine ⟨x', fun a => ?_, fun a ha => ?_⟩
  · rw [hval]
    exact (ν'.mem_valuationSubring_iff _).1 ((Scheme.stalkClosedPointTo l).hom a).2
  · rw [hval]
    set r := (Scheme.stalkClosedPointTo l).hom a
    have hr : r ∈ IsLocalRing.maximalIdeal R :=
      map_nonunit (Scheme.stalkClosedPointTo l).hom a ha
    refine lt_of_le_of_ne ((ν'.mem_valuationSubring_iff _).1 r.2) fun h1r => hr ?_
    have hr0 : (r : K) ≠ 0 := fun h0 => by simp [h0] at h1r
    refine isUnit_iff_exists_inv.2 ⟨⟨(r : K)⁻¹, (ν'.mem_valuationSubring_iff _).2 ?_⟩, ?_⟩
    · rw [map_inv₀, h1r, inv_one]
    · exact Subtype.ext (mul_inv_cancel₀ hr0)

/-- One blow-up step keeps a nonempty center: if `ν` has nonempty center on `X`, `U ⊆ X` is an
open containing the generic point of the center `Z` with `Z ∩ U` smooth, and `X' = Bl_{Z ∩ U} U`,
then the valuation `ν'` of `k(X')` with `ν' ∘ β^* = ν` has nonempty center on `X'`. -/
private theorem hasNonemptyCenter_blowUp {k : Type u} [Field k]
    {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral X']
    (hvar : MMP.Mori.IsVariety k sX) (hvar' : MMP.Mori.IsVariety k sX')
    (ν : Valuation X.functionField ℤᵐ⁰) (ν' : Valuation X'.functionField ℤᵐ⁰)
    (hν₀ : HasNonemptyCenter k sX ν)
    (U : X.Opens) (I : (U : Scheme.{u}).IdealSheafData)
    (hY : X' = blowUp I) (β : X' ⟶ X)
    (hβ : β = eqToHom hY ≫ blowUpToBase I ≫ U.ι)
    (hs : sX' = β ≫ sX) [IsDominant β]
    (hν : ν'.comap (functionFieldMap β) = ν)
    (hcen : ∀ D : ProperDivisorOver k sX, D.valuation = ν →
      (∀ z : X, IsGenericPoint z (D.center : Set X) → z ∈ U) ∧
      I = Scheme.IdealSheafData.vanishingIdeal
        ⟨U.ι ⁻¹' (D.center : Set X), D.center.isClosed.preimage U.ι.continuous⟩ ∧
      IsSmoothScheme (I.subschemeι ≫ U.ι ≫ sX)) :
    HasNonemptyCenter k sX' ν' := by
  subst hY hs
  have hβ' : β = blowUpToBase I ≫ U.ι := by simpa using hβ
  subst hβ'
  obtain ⟨hdiv, D, hD⟩ := hν₀
  obtain ⟨hxU, hI, -⟩ := hcen D hD
  have hx := hxU _ (isGenericPoint_center D)
  have hsupp : (I.support : Set U) ≠ Set.univ := by
    intro h
    have hη : genericPoint X ∈ U :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 ⟨_, trivial, hx⟩
    have hmem : (⟨genericPoint X, hη⟩ : U) ∈ (I.support : Set U) := h ▸ trivial
    rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hmem
    exact genericPoint_notMem_center D hmem
  have hdiv' := isDivisorOfFunctionField_of_comap sX _
    (functionFieldMap_bijective_blowUp U I hsupp) hν hdiv
  refine ⟨hdiv', ?_⟩
  have : MMP.Mori.IsVariety k sX := hvar
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : MMP.Mori.IsVariety k ((blowUpToBase I ≫ U.ι) ≫ sX) := hvar'
  obtain ⟨x', h1, h2⟩ := exists_dominated_point_blowUp U I ν' _ hx
    (fun a => by
      rw [hν, ← hD]
      exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D.toDivisorOver _ rfl a)
    (fun a ha => by
      rw [hν, ← hD]
      exact MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D.toDivisorOver _ rfl a ha)
  obtain ⟨D', -, hD', -⟩ :=
    exists_properDivisorOver_isProjective_of_dominates _ hdiv' x' h1 h2
  exact ⟨D', hD'⟩

end Centre

/-! ### The tower of point blow-ups at the centres of a valuation -/

section Tower

open MMP.Flips
open scoped WithZero

variable (k : Type u) [Field k]

/-- A smooth surface over `k` with a valuation of its function field and a closed point (the
centre of the valuation, in the tower below). -/
private structure State where
  Y : Scheme.{u}
  s : Y ⟶ Spec (.of k)
  [isIntegral : IsIntegral Y]
  [isLocallyNoetherian : IsLocallyNoetherian Y]
  [isNormal : IsNormal Y]
  hY : IsNormalVariety k s
  hsm : IsSmoothScheme s
  hdim : topologicalKrullDim Y = 2
  ν : Valuation Y.functionField ℤᵐ⁰
  c : Y
  hc : IsClosed ({c} : Set Y)

attribute [local instance] State.isIntegral State.isLocallyNoetherian State.isNormal

variable {k}

/-- The point `c` of the open subscheme `⊤`. -/
private def State.cTop (S : State k) : (⊤ : S.Y.Opens).toScheme := ⟨S.c, trivial⟩

private theorem State.isClosed_cTop (S : State k) :
    IsClosed ({S.cTop} : Set (⊤ : S.Y.Opens).toScheme) := by
  have : ({S.cTop} : Set (⊤ : S.Y.Opens).toScheme) = (⊤ : S.Y.Opens).ι ⁻¹' {S.c} := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩
  rw [this]
  exact S.hc.preimage (⊤ : S.Y.Opens).ι.continuous

private theorem State.nonempty_top (S : State k) : Nonempty (⊤ : S.Y.Opens) := ⟨S.cTop⟩

/-- The reduced point `c` of `⊤`, blown up in the next step. -/
private noncomputable def State.ideal (S : State k) : (⊤ : S.Y.Opens).toScheme.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨{S.cTop}, S.isClosed_cTop⟩

private theorem State.isBirationalMorphism_top (S : State k) :
    IsBirationalMorphism (⊤ : S.Y.Opens).ι := by
  have : IsIso (⊤ : S.Y.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  exact isBirationalMorphism_of_isIso _

private theorem State.top_spec (S : State k) :
    IsNormalVariety k ((⊤ : S.Y.Opens).ι ≫ S.s) ∧ IsSmoothScheme ((⊤ : S.Y.Opens).ι ≫ S.s) ∧
      topologicalKrullDim (⊤ : S.Y.Opens) = 2 := by
  haveI := S.nonempty_top
  haveI := isDominant_opens_ι (⊤ : S.Y.Opens)
  have : LocallyOfFiniteType S.s := S.hY.1.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation S.s :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
  exact ⟨isNormalVariety_ι S.hY _, isSmoothScheme_ι S.hsm _,
    (topologicalKrullDim_opens_eq S.hY _).trans S.hdim⟩

private theorem State.blowUp_spec [IsAlgClosed k] (S : State k) :
    IsNormalVariety k (blowUpToBase S.ideal ≫ (⊤ : S.Y.Opens).ι ≫ S.s) ∧
      IsSmoothScheme (blowUpToBase S.ideal ≫ (⊤ : S.Y.Opens).ι ≫ S.s) ∧
      topologicalKrullDim (blowUp S.ideal) = 2 ∧ IsBirationalMorphism (blowUpToBase S.ideal) ∧
      IsProper (blowUpToBase S.ideal) := by
  haveI := S.nonempty_top
  obtain ⟨hT, hTs, hTd⟩ := S.top_spec
  obtain ⟨-, hprop, hbir, -, -⟩ :=
    blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection
      hT.1 hTs hTd S.isClosed_cTop
  have hYs := MMP.Threefold.Resolution.isSmoothScheme_blowUp_singleton hT.1 hTs hTd S.isClosed_cTop
  have hres : IsSmoothResolution ((⊤ : S.Y.Opens).ι ≫ S.s) (blowUpToBase S.ideal) :=
    ⟨hprop, hbir, hYs⟩
  obtain ⟨h1, h2, -⟩ := hres.isNormalVariety hT
  exact ⟨h1, hYs, h2.trans hTd, hbir, hprop⟩

open Classical in
/-- **One step of the tower.** Blow up the point `c` (of `⊤`), carry the valuation to the blow-up,
and choose as new point the closed centre of the valuation, when it has one. -/
private noncomputable def State.next [IsAlgClosed k] (S : State k) : State k :=
  haveI := S.nonempty_top
  haveI := isDominant_opens_ι (⊤ : S.Y.Opens)
  have hspec := S.blowUp_spec
  haveI : IsIntegral (blowUp S.ideal) := hspec.1.1.toIsIntegral
  haveI := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    hspec.2.1).1
  haveI := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    hspec.2.1).2
  haveI : IsDominant (blowUpToBase S.ideal) := hspec.2.2.2.1.isDominant
  let eW := RingEquiv.ofBijective (functionFieldMap (⊤ : S.Y.Opens).ι)
    (functionFieldMap_opens_ι_bijective _)
  let eπ := RingEquiv.ofBijective (functionFieldMap (blowUpToBase S.ideal))
    hspec.2.2.2.1.functionFieldMap_bijective
  let ν' := (S.ν.comap eW.symm.toRingHom).comap eπ.symm.toRingHom
  haveI : CompactSpace (blowUp S.ideal) :=
    haveI := hspec.1.1.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace (blowUpToBase S.ideal ≫ (⊤ : S.Y.Opens).ι ≫ S.s)
  let cz : {z : blowUp S.ideal // IsClosed ({z} : Set (blowUp S.ideal))} :=
    if h : ∃ z : blowUp S.ideal, IsClosed ({z} : Set (blowUp S.ideal)) ∧
        ∀ E : ProperDivisorOver k (blowUpToBase S.ideal ≫ (⊤ : S.Y.Opens).ι ≫ S.s),
          E.valuation = ν' → (E.center : Set (blowUp S.ideal)) = {z}
    then ⟨h.choose, h.choose_spec.1⟩
    else
      ⟨(isClosed_univ.exists_closed_singleton (Set.univ_nonempty)).choose,
        (isClosed_univ.exists_closed_singleton (Set.univ_nonempty)).choose_spec.2⟩
  { Y := blowUp S.ideal
    s := blowUpToBase S.ideal ≫ (⊤ : S.Y.Opens).ι ≫ S.s
    hY := hspec.1
    hsm := hspec.2.1
    hdim := hspec.2.2.1
    ν := ν'
    c := cz.1
    hc := cz.2 }

private theorem State.isDominant_blowUpToBase [IsAlgClosed k] (S : State k) :
    IsDominant (blowUpToBase S.ideal) := S.blowUp_spec.2.2.2.1.isDominant

/-- The valuation of the next step restricts to the valuation of this one. -/
private theorem State.next_ν_comap [IsAlgClosed k] (S : State k) :
    haveI := S.nonempty_top
    haveI := isDominant_opens_ι (⊤ : S.Y.Opens)
    haveI := S.isDominant_blowUpToBase
    haveI : IsIntegral (blowUp S.ideal) := S.next.isIntegral
    ((S.next.ν).comap (functionFieldMap (blowUpToBase S.ideal))).comap
      (functionFieldMap (⊤ : S.Y.Opens).ι) = S.ν := by
  haveI := S.nonempty_top
  haveI := isDominant_opens_ι (⊤ : S.Y.Opens)
  haveI := S.isDominant_blowUpToBase
  haveI : IsIntegral (blowUp S.ideal) := S.next.isIntegral
  ext t
  simp only [Valuation.comap_apply]
  change S.ν _ = S.ν t
  refine congrArg S.ν ((RingEquiv.symm_apply_eq _).2 ((RingEquiv.symm_apply_eq _).2 ?_))
  simp only [RingEquiv.ofBijective_apply, RingHom.coe_toMonoidWithZeroHom,
    MonoidWithZeroHom.coe_ofClass]

/-- The valuation of the next step restricts to the valuation of this one, along the blow-up. -/
private theorem State.next_ν_comap_comp [IsAlgClosed k] (S : State k) :
    haveI := S.nonempty_top
    haveI := isDominant_opens_ι (⊤ : S.Y.Opens)
    haveI := S.isDominant_blowUpToBase
    haveI : IsIntegral (blowUp S.ideal) := S.next.isIntegral
    (S.next.ν).comap (functionFieldMap (blowUpToBase S.ideal ≫ (⊤ : S.Y.Opens).ι)) = S.ν := by
  haveI := S.nonempty_top
  haveI := isDominant_opens_ι (⊤ : S.Y.Opens)
  haveI := S.isDominant_blowUpToBase
  haveI : IsIntegral (blowUp S.ideal) := S.next.isIntegral
  rw [← S.next_ν_comap]
  refine Eq.trans ?_ (Valuation.comap_comp _ _ _)
  exact congrArg (fun f => S.next.ν.comap f) (RingHom.ext fun t =>
    (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply _ _ t).symm)

/-- A divisor over the next step with the valuation of the next step, regarded as a divisor
over this one, has the valuation of this one. -/
private theorem State.valuation_compDivisorOver_next [IsAlgClosed k] (S : State k)
    (hT : IsNormalVariety k ((⊤ : S.Y.Opens).ι ≫ S.s))
    (hWb : IsBirationalMorphism (⊤ : S.Y.Opens).ι)
    (hY : IsNormalVariety k (blowUpToBase S.ideal ≫ (⊤ : S.Y.Opens).ι ≫ S.s))
    (hb : IsBirationalMorphism (blowUpToBase S.ideal))
    (E : DivisorOver k S.next.s)
    (hE : E.valuation = S.next.ν) :
    haveI := S.nonempty_top
    (compDivisorOver (⊤ : S.Y.Opens).ι hT hWb
      (compDivisorOver (blowUpToBase S.ideal) hY hb E)).valuation = S.ν := by
  haveI := S.nonempty_top
  haveI := isDominant_opens_ι (⊤ : S.Y.Opens)
  haveI := S.isDominant_blowUpToBase
  haveI : IsIntegral (blowUp S.ideal) := S.next.isIntegral
  refine (valuation_compDivisorOver _ _ _ _).trans ?_
  refine (congrArg (Valuation.comap _) (valuation_compDivisorOver _ _ _ _)).trans ?_
  exact (congrArg (fun v : Valuation (blowUp S.ideal).functionField ℤᵐ⁰ =>
    (v.comap (functionFieldMap (blowUpToBase S.ideal))).comap
      (functionFieldMap (⊤ : S.Y.Opens).ι)) hE).trans S.next_ν_comap

/-- The point of the next step is the centre of its valuation, when that centre is closed. -/
private theorem State.next_c_spec [IsAlgClosed k] (S : State k)
    (h : ∃ z : S.next.Y, IsClosed ({z} : Set S.next.Y) ∧
      ∀ E : ProperDivisorOver k S.next.s, E.valuation = S.next.ν →
        (E.center : Set S.next.Y) = {z}) :
    ∀ E : ProperDivisorOver k S.next.s, E.valuation = S.next.ν →
      (E.center : Set S.next.Y) = {S.next.c} := by
  unfold State.next at h ⊢
  dsimp only at h ⊢
  rw [dif_pos h]
  exact h.choose_spec.2

/-- The blown-up ideal is the reduced centre of the valuation, a smooth point. -/
private theorem State.hcen_spec [IsAlgClosed k] (S : State k)
    (hcen : ∀ E : ProperDivisorOver k S.s, E.valuation = S.ν → (E.center : Set S.Y) = {S.c})
    (D : ProperDivisorOver k S.s) (hD : D.valuation = S.ν) :
    (∀ z : S.Y, IsGenericPoint z (D.center : Set S.Y) → z ∈ (⊤ : S.Y.Opens)) ∧
      S.ideal = Scheme.IdealSheafData.vanishingIdeal
        ⟨(⊤ : S.Y.Opens).ι ⁻¹' (D.center : Set S.Y),
          D.center.isClosed.preimage (⊤ : S.Y.Opens).ι.continuous⟩ ∧
      IsSmoothScheme (S.ideal.subschemeι ≫ (⊤ : S.Y.Opens).ι ≫ S.s) := by
  have : LocallyOfFiniteType ((⊤ : S.Y.Opens).ι ≫ S.s) :=
    (S.top_spec.1.1).toLocallyOfFiniteType
  refine ⟨fun _ _ => trivial, ?_, ?_⟩
  · refine congrArg Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.ext ?_)
    ext y
    change y = S.cTop ↔ (⊤ : S.Y.Opens).ι y ∈ (D.center : Set S.Y)
    rw [hcen D hD, Set.mem_singleton_iff]
    exact ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩
  · haveI := MMP.Threefold.Resolution.isIso_subschemeι_vanishingIdeal_singleton_comp
      ((⊤ : S.Y.Opens).ι ≫ S.s) S.isClosed_cTop
    have : LocallyOfFinitePresentation (S.ideal.subschemeι ≫ (⊤ : S.Y.Opens).ι ≫ S.s) := by
      unfold State.ideal; infer_instance
    rw [isSmoothScheme_iff]
    unfold State.ideal
    infer_instance

end Tower

/-! ### One point blow-up -/

/-- The inverse transform of an effective `ℚ`-divisor is effective. -/
private theorem inverseTransformDivisor_nonneg {X Y : Scheme.{u}} (g : Y ⟶ X) {D : QDivisor X}
    (hD : 0 ≤ D) : 0 ≤ inverseTransformDivisor g D := by
  classical
  conv_rhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_nonneg fun E _ => ?_
  rw [inverseTransformDivisor_single]
  cases inverseTransformPrimeDivisor g E with
  | none => exact le_rfl
  | some C => exact Finsupp.single_nonneg.2 (hD E)

/-- The multiplicity of an effective `ℚ`-divisor is nonnegative. -/
private theorem multiplicityAt_nonneg {X : Scheme.{u}} {D : QDivisor X} (hD : 0 ≤ D) (x : X) :
    0 ≤ D.multiplicityAt x := by
  unfold DivisorWithCoeffs.multiplicityAt
  exact Finset.sum_nonneg fun P _ => nsmul_nonneg (hD P) _

/-- The multiplicity is monotone in the divisor. -/
private theorem multiplicityAt_mono {X : Scheme.{u}} {D D' : QDivisor X} (h : D ≤ D') (x : X) :
    D.multiplicityAt x ≤ D'.multiplicityAt x := by
  have h1 := DivisorWithCoeffs.multiplicityAt_add D (D' - D) x
  rw [add_sub_cancel] at h1
  have h2 := multiplicityAt_nonneg (sub_nonneg.2 h) x
  linarith

/-- **One point blow-up.** Let `T` be a smooth surface, `Θ ≤ A` with `A` effective and
`mult_c A ≤ μ ≤ 1` at a closed point `c`. On the blow-up `π` of `c`, the crepant boundary `Θ'` of
`(T, Θ)` satisfies `Θ' ≤ π⁻¹_* A`, the effective divisor `π⁻¹_* A` has multiplicity `≤ μ` at every
point over `c`, and every prime divisor of the blow-up lying over `c` has discrepancy
`-coeff(Θ') ≥ 1 - μ`. -/
private theorem exists_isCrepantBoundary_blowUp_singleton {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {T : Scheme.{u}} {sT : T ⟶ Spec (.of k)} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T]
    (hT : IsNormalVariety k sT) (hTs : IsSmoothScheme sT) (hTd : topologicalKrullDim T = 2)
    {K : Divisor T} (hK : K.IsCanonicalDivisor sT 2) {Θ A : QDivisor T} (hA : 0 ≤ A)
    (hΘA : Θ ≤ A) {μ : ℚ} (hμ : μ ≤ 1) {c : T} (hc : IsClosed ({c} : Set T))
    (hcA : A.multiplicityAt c ≤ μ) :
    ∃ (hY : IsNormalVariety k
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{c}, hc⟩) ≫ sT))
      (hb : IsBirationalMorphism (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{c}, hc⟩)))
      (Θ' : QDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{c}, hc⟩))),
      IsProper (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{c}, hc⟩)) ∧
      IsSmoothScheme (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{c}, hc⟩) ≫ sT) ∧
      topologicalKrullDim (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{c}, hc⟩)) = 2 ∧
      IsCrepantBoundary sT 2 K Θ _ hY hb Θ' ∧
      Θ' ≤ inverseTransformDivisor
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{c}, hc⟩)) A ∧
      0 ≤ inverseTransformDivisor
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{c}, hc⟩)) A ∧
      (∀ q, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{c}, hc⟩) q = c →
        (inverseTransformDivisor (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{c}, hc⟩))
          A).multiplicityAt q ≤ μ) ∧
      ∀ P : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{c}, hc⟩)),
        blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{c}, hc⟩) P.genericPoint = c →
          1 - μ ≤ -Θ' P := by
  classical
  set I := Scheme.IdealSheafData.vanishingIdeal ⟨{c}, hc⟩
  set π := blowUpToBase I
  obtain ⟨hY, hb, F, hF, -, hdF, hprop, hYs, hYd, hexcF⟩ :=
    isDiscrepancy_blowUp_singleton hT hTs hTd hK Θ hc
  have hP : IsPair sT Θ := ⟨hT, 2, K, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hTs _⟩
  haveI := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
  haveI := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
  haveI : IsIntegral (blowUp I) := hY.1.toIsIntegral
  haveI : IsProper π := hprop
  obtain ⟨⟨Θ', hΘ', -⟩, -⟩ := hP.existsUnique_isCrepantBoundary hK π hY hb
  have hΘ'F : Θ' F = Θ.multiplicityAt c - 1 := by
    have := (hΘ' F).eq hdF
    change -Θ' F = _ at this
    linarith
  have hres : IsSmoothResolution sT π := ⟨hprop, hb, hYs⟩
  have hexc : ∀ P, RationalMap.IsExceptional (X := blowUp I) π.toRationalMap P → P = F :=
    fun P hP' => PrimeDivisor.ext_idealSheaf
      ((hexcF _).1 ((isExceptional_iff_isExceptionalCurve hT hTd hres P).1 hP'))
  obtain ⟨hdecomp, -⟩ := IsCrepantBoundary.eq_inverseTransformDivisor_add_exceptional hP hΘ'
  have hcΘ := multiplicityAt_mono hΘA c
  have hA' := inverseTransformDivisor_nonneg π hA
  refine ⟨hY, hb, Θ', hprop, hYs, hYd, hΘ', fun P => ?_, hA', fun q hq => ?_, fun P hP' => ?_⟩
  · by_cases hPF : P = F
    · subst hPF
      rw [hΘ'F]
      have := hA' P
      simp only [Finsupp.coe_zero, Pi.zero_apply] at this
      linarith
    · rw [hdecomp, Finsupp.add_apply,
        Finsupp.filter_apply_neg _ _ (fun h => hPF (hexc P h)), add_zero]
      have := inverseTransformDivisor_nonneg π (sub_nonneg.2 hΘA) P
      rw [map_sub, Finsupp.sub_apply] at this
      simp only [Finsupp.coe_zero, Pi.zero_apply] at this
      linarith
  · have hq' := (MMP.Threefold.Resolution.mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hc
      hF q).2 hq
    exact (MMP.Threefold.Resolution.multiplicityAt_inverseTransformDivisor_blowUpToBase_le hT.1
      hTs hTd hc hF hA hq').trans hcA
  · have hcurve : IsExceptionalCurve π P.idealSheaf := by
      refine ⟨MMP.Flips.isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hY.1 hYd P, c, ?_⟩
      change π '' P.support = {c}
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine Set.Subset.antisymm ?_ ?_
      · refine (image_closure_subset_closure_image π.continuous).trans ?_
        rw [Set.image_singleton, hP', hc.closure_eq]
      · rintro _ rfl
        exact ⟨P.genericPoint, subset_closure rfl, hP'⟩
    have hPF : P = F := PrimeDivisor.ext_idealSheaf ((hexcF _).1 hcurve)
    subst hPF
    rw [hΘ'F]
    linarith

/-! ### The invariant of the tower -/

section Invariant

open MMP.Flips

attribute [local instance] State.isIntegral State.isLocallyNoetherian State.isNormal

variable {k : Type u} [Field k]

/-- The invariant of the tower over a pair `(V, Δ)`, for a divisor `D` over `V` with discrepancy
`a`: the valuation has a centre, which is the closed point `c`; there are a canonical divisor `K`
and the crepant boundary `Θ` of `(V, Δ)`, through which every divisor with the valuation of `D`
has discrepancy `a`, and an effective `A ≥ Θ` with `mult_c A ≤ μ`. -/
private def State.Good (μ a : ℚ) (S : State k) : Prop :=
  HasNonemptyCenter k S.s S.ν ∧
    (∀ E : ProperDivisorOver k S.s, E.valuation = S.ν → (E.center : Set S.Y) = {S.c}) ∧
    ∃ (K : Divisor S.Y) (Θ A : QDivisor S.Y), K.IsCanonicalDivisor S.s 2 ∧ 0 ≤ A ∧ Θ ≤ A ∧
      A.multiplicityAt S.c ≤ μ ∧
      ∀ (E : DivisorOver k S.s) (b : ℚ), E.valuation = S.ν → IsDiscrepancy S.s 2 K Θ E b → b = a

/-- **The invariant propagates**, as long as `a < 1 - μ`: otherwise the valuation would be that of
the exceptional curve of a blow-up, whose discrepancy is `≥ 1 - μ`. -/
private theorem State.good_next [IsAlgClosed k] [CharZero k] {μ a : ℚ} (hμ : μ ≤ 1)
    (hlt : a < 1 - μ) (S : State k) (h : S.Good μ a) : S.next.Good μ a := by
  obtain ⟨hnc, hcen, K, Θ, A, hK, hA, hΘA, hcA, hΘ⟩ := h
  haveI := S.nonempty_top
  haveI := isDominant_opens_ι (⊤ : S.Y.Opens)
  obtain ⟨hT, hTs, hTd⟩ := S.top_spec
  have hWb := S.isBirationalMorphism_top
  have hKT := isCanonicalDivisor_restrictOpen S.hY hK (⊤ : S.Y.Opens)
  have hAT : 0 ≤ A.restrictOpen (⊤ : S.Y.Opens) := fun W => hA _
  have hΘAT : Θ.restrictOpen (⊤ : S.Y.Opens) ≤ A.restrictOpen (⊤ : S.Y.Opens) := fun W => hΘA _
  have hcAT : (A.restrictOpen (⊤ : S.Y.Opens)).multiplicityAt S.cTop ≤ μ :=
    (multiplicityAt_restrictOpen _ A S.cTop).trans_le hcA
  obtain ⟨hY', hb, Θ', hprop, hYs, hYd, hcrep, hΘ'A, hA', hmult, hbound⟩ :=
    exists_isCrepantBoundary_blowUp_singleton hT hTs hTd hKT hAT hΘAT hμ S.isClosed_cTop hcAT
  haveI := S.isDominant_blowUpToBase
  haveI : IsIntegral (blowUp S.ideal) := S.next.isIntegral
  haveI : IsLocallyNoetherian (blowUp S.ideal) := S.next.isLocallyNoetherian
  haveI : IsNormal (blowUp S.ideal) := S.next.isNormal
  haveI : IsProper (blowUpToBase S.ideal) := hprop
  haveI : IsDominant (blowUpToBase S.ideal ≫ (⊤ : S.Y.Opens).ι) := inferInstance
  haveI : AlgebraicGeometry.IsVariety k S.next.s := S.next.hY.1
  haveI : QuasiCompact S.next.s := S.next.hY.1.toQuasiCompact
  haveI : CompactSpace S.next.Y := QuasiCompact.compactSpace_of_compactSpace S.next.s
  obtain ⟨K', hK'⟩ := exists_isCanonicalDivisor_of_isSmoothScheme S.next.s S.next.hsm (n := 2)
    (by exact_mod_cast S.next.hdim)
  have hPY : IsPairWith S.s 2 K Θ :=
    ⟨S.hY, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme S.hsm _⟩
  have hPT : IsPairWith ((⊤ : S.Y.Opens).ι ≫ S.s) 2 (K.restrictOpen ⊤) (Θ.restrictOpen ⊤) :=
    ⟨hT, hKT, MMP.Fourfold.isQCartier_of_isSmoothScheme hTs _⟩
  -- every divisor with the valuation of `D` has discrepancy `a` over `(Y', Θ')`
  have hΘ' : ∀ (E : DivisorOver k S.next.s) (b : ℚ), E.valuation = S.next.ν →
      IsDiscrepancy S.next.s 2 K' Θ' E b → b = a := by
    intro E b hEv hEb
    have h1 := isDiscrepancy_compDivisorOver_of_isCrepantBoundary hPT.isPair hKT
      (blowUpToBase S.ideal) hY' hb hK' hcrep E hEb
    exact hΘ _ b (S.valuation_compDivisorOver_next hT hWb hY' hb E hEv)
      (isDiscrepancy_compDivisorOver_ι hPY ⊤ hPT hT hWb _ h1)
  -- the valuation has a centre on the blow-up
  haveI hβdom : @IsDominant S.next.Y S.Y (blowUpToBase S.ideal ≫ (⊤ : S.Y.Opens).ι) :=
    (inferInstance : IsDominant (blowUpToBase S.ideal ≫ (⊤ : S.Y.Opens).ι))
  have hnc' : HasNonemptyCenter k S.next.s S.next.ν :=
    hasNonemptyCenter_blowUp S.s S.next.s S.hY.1 S.next.hY.1 S.ν S.next.ν hnc
      ⊤ S.ideal rfl (blowUpToBase S.ideal ≫ (⊤ : S.Y.Opens).ι)
      (by erw [eqToHom_refl, Category.id_comp]; rfl)
      (Category.assoc _ _ _).symm S.next_ν_comap_comp (S.hcen_spec hcen)
  obtain ⟨-, D', hD'⟩ := id hnc'
  set z := D'.f D'.E.genericPoint with hz_def
  have hηE : D'.E.genericPoint ∈ D'.E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  -- the centre of the valuation on the blow-up lies over `c`
  have hπz : blowUpToBase S.ideal z = S.cTop := by
    haveI := D'.isProper
    haveI : IsIso (⊤ : S.Y.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
    let D₁ := compDivisorOver (blowUpToBase S.ideal) hY' hb D'.toDivisorOver
    let D₂ := compDivisorOver (⊤ : S.Y.Opens).ι hT hWb D₁
    have hp : IsProper D₂.f := by
      change IsProper ((D'.f ≫ blowUpToBase S.ideal) ≫ (⊤ : S.Y.Opens).ι)
      haveI : IsProper (D'.f ≫ blowUpToBase S.ideal) :=
        @IsProper.instCompScheme _ _ _ D'.f (blowUpToBase S.ideal) D'.isProper hprop
      infer_instance
    have h := hcen ⟨D₂, hp⟩ (S.valuation_compDivisorOver_next hT hWb hY' hb _ hD')
    have hmem : D₂.f D₂.E.genericPoint ∈
        ((⟨D₂, hp⟩ : ProperDivisorOver k S.s).center : Set S.Y) :=
      ⟨D₂.E.genericPoint, hηE, rfl⟩
    rw [h] at hmem
    exact Subtype.ext hmem
  have hgen : closure ({z} : Set S.next.Y) = (D'.center : Set S.next.Y) :=
    isGenericPoint_center D'
  by_cases h2 : 2 ≤ codimension D'.toDivisorOver.center
  · have hcoh : 2 ≤ Order.coheight z := by
      rwa [MMP.Positivity.DivisorOver.codimension_center] at h2
    have hzc : IsClosed ({z} : Set S.next.Y) :=
      isClosed_of_two_le_coheight (by rw [S.next.hdim]) hcoh
    have hP : ∃ z' : S.next.Y, IsClosed ({z'} : Set S.next.Y) ∧
        ∀ E : ProperDivisorOver k S.next.s, E.valuation = S.next.ν →
          (E.center : Set S.next.Y) = {z'} := by
      refine ⟨z, hzc, fun E hE => ?_⟩
      rw [ProperDivisorOver.center_eq_of_valuation_eq S.next.hY.1 (hE.trans hD'.symm), ← hgen,
        hzc.closure_eq]
    have hcen' := S.next_c_spec hP
    have hc' : S.next.c = z := by
      have hzmem : z ∈ (D'.center : Set S.next.Y) := ⟨_, hηE, rfl⟩
      rw [hcen' D' hD'] at hzmem
      exact hzmem.symm
    refine ⟨hnc', hcen', K', Θ', inverseTransformDivisor (blowUpToBase S.ideal)
      (A.restrictOpen (⊤ : S.Y.Opens)), hK', hA', hΘ'A, ?_, hΘ'⟩
    rw [hc']
    exact hmult z hπz
  · exfalso
    have hne := (MMP.Positivity.DivisorOver.two_le_codimension_center_iff S.next.hY
      D'.toDivisorOver).not.1 h2
    push Not at hne
    obtain ⟨G, hG⟩ := hne
    have hGz : G.genericPoint = z :=
      (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq S.next.hY.1 hG).symm
    have hbG := hbound G ((congrArg (blowUpToBase S.ideal) hGz).trans hπz)
    have hPn : IsPair S.next.s Θ' :=
      ⟨S.next.hY, 2, K', hK', MMP.Fourfold.isQCartier_of_isSmoothScheme S.next.hsm _⟩
    obtain ⟨q, hq⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPn hK'
      (DivisorOver.ofPrimeDivisor k S.next.hY G)
    have hq1 := hq.eq_neg_coeff_of_ofPrimeDivisor S.next.hY
    have hq2 := hΘ' _ q (hG.symm.trans hD') hq
    change q = -Θ' G at hq1
    linarith

end Invariant

/-! ### The tower is finite -/

section Termination

open MMP.Flips

attribute [local instance] State.isIntegral State.isLocallyNoetherian State.isNormal

variable {k : Type u} [Field k]

/-- The tower of point blow-ups starting from `S`. -/
private noncomputable def State.tower [IsAlgClosed k] (S : State k) : ℕ → State k
  | 0 => S
  | n + 1 => (S.tower n).next

/-- **Zariski's theorem forbids an infinite tower.** Under the invariant, if `a < 1 - μ` then every
step of the tower blows up a closed centre, so the centres never reach codimension one; this
contradicts the fact that the valuation is that of a divisor. -/
private theorem State.false_of_good [IsAlgClosed k] [CharZero k] {μ a : ℚ} (hμ : μ ≤ 1)
    (hlt : a < 1 - μ) (S : State k) (h : S.Good μ a) : False := by
  have hgood : ∀ n, (S.tower n).Good μ a := fun n => by
    induction n with
    | zero => exact h
    | succ n ih => exact State.good_next hμ hlt _ ih
  have hint : ∀ r, IsIntegral (S.tower r).Y := fun r => (S.tower r).isIntegral
  have hdom : ∀ r, @IsDominant (S.tower (r + 1)).Y (S.tower r).Y
      (blowUpToBase (S.tower r).ideal ≫ (⊤ : (S.tower r).Y.Opens).ι) := fun r => by
    haveI := (S.tower r).nonempty_top
    haveI := isDominant_opens_ι (⊤ : (S.tower r).Y.Opens)
    haveI := (S.tower r).isDominant_blowUpToBase
    exact (inferInstance :
      IsDominant (blowUpToBase (S.tower r).ideal ≫ (⊤ : (S.tower r).Y.Opens).ι))
  obtain ⟨-, r, D, hD, z, hz, hcoh⟩ :=
    @hasNonemptyCenter_and_exists_coheight_eq_one_of_blowUp k _ (fun r => (S.tower r).Y)
      (fun r => (S.tower r).s) hint (fun r => (S.tower r).hY.1) (fun r => (S.tower r).hsm)
      (fun r => (S.tower r).ν) (hgood 0).1 (fun r => ⊤) (fun r => (S.tower r).ideal)
      (fun r => rfl) (fun r => blowUpToBase (S.tower r).ideal ≫ (⊤ : (S.tower r).Y.Opens).ι)
      (fun r => by erw [eqToHom_refl, Category.id_comp]; rfl)
      (fun r => (Category.assoc _ _ _).symm) hdom
      (fun r => (S.tower r).next_ν_comap_comp)
      (fun r D hD => (S.tower r).hcen_spec (hgood r).2.1 D hD)
  have hc := (hgood r).2.1 D hD
  have hzc : z = (S.tower r).c := by
    have hmem : z ∈ closure ({z} : Set (S.tower r).Y) := subset_closure rfl
    rw [hz.def, hc] at hmem
    exact hmem
  have h2 := MMP.Threefold.Resolution.coheight_eq_two_of_isClosed (S.tower r).hY.1
    (S.tower r).hdim (S.tower r).hc
  rw [← hzc, hcoh] at h2
  exact absurd h2 (by decide)

end Termination

/-! ### Discrepancies over a smooth surface -/

section SmoothSurface

open MMP.Flips

/-- **Discrepancies over a smooth surface** (KM, proof of Theorem 4.5). Let `V` be a smooth surface
over an algebraically closed field of characteristic zero and `Δ` an effective `ℚ`-divisor with
`mult_p Δ ≤ μ ≤ 1` at every closed point `p`. Then every exceptional divisor over `V` has
discrepancy `a(E, V, Δ) ≥ 1 - μ`. -/
private theorem le_of_isDiscrepancy_of_isExceptional {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {V : Scheme.{u}} {sV : V ⟶ Spec (.of k)} [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] (hV : IsNormalVariety k sV) (hVs : IsSmoothScheme sV)
    (hVd : topologicalKrullDim V = 2) {K : Divisor V} (hK : K.IsCanonicalDivisor sV 2)
    {Δ : QDivisor V} (hΔ : 0 ≤ Δ) {μ : ℚ} (hμ : μ ≤ 1)
    (hmult : ∀ p : V, IsClosed ({p} : Set V) → Δ.multiplicityAt p ≤ μ)
    (D : DivisorOver k sV) (hD : D.IsExceptional) {a : ℚ} (ha : IsDiscrepancy sV 2 K Δ D a) :
    1 - μ ≤ a := by
  by_contra hlt
  push Not at hlt
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have : IsSeparated sV := hV.1.toIsSeparated
  have : IsSeparated (V ↘ Limits.terminal Scheme) := by
    rw [show (V ↘ Limits.terminal Scheme) = sV ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hηE : D.E.genericPoint ∈ D.E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hcoh : 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
    have h := (MMP.Positivity.isExceptional_toRationalMap_iff D.E).1 hD
    rw [MMP.Flips.le_closedsCodimension_iff_le_coheight] at h
    exact h _ (subset_closure ⟨D.E.genericPoint, hηE, rfl⟩)
  have : QuasiCompact sV := hV.1.toQuasiCompact
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have hp : IsClosed ({D.f D.E.genericPoint} : Set V) :=
    isClosed_of_two_le_coheight (by rw [hVd]) hcoh
  haveI : AlgebraicGeometry.IsVariety k sV := hV.1
  have hdiv : IsDivisorOfFunctionField k sV D.valuation :=
    ⟨D.Y, D.f ≫ sV, D.isNormalVariety, D.E,
      functionFieldAlgEquiv sV D.f D.isBirationalMorphism.functionFieldMap_bijective, rfl⟩
  obtain ⟨D', -, hD', -⟩ := exists_properDivisorOver_isProjective_of_dominates sV hdiv
    (D.f D.E.genericPoint) (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl)
  let S : State k :=
    { Y := V, s := sV, hY := hV, hsm := hVs, hdim := hVd, ν := D.valuation,
      c := D.f D.E.genericPoint, hc := hp }
  refine State.false_of_good hμ hlt S ⟨⟨hdiv, D', hD'⟩, fun E hE => ?_, K, Δ, Δ, hK, hΔ, le_rfl,
    hmult _ hp, fun E b hE hb => ?_⟩
  · change (E.center : Set V) = {D.f D.E.genericPoint}
    rw [ProperDivisorOver.center_eq_toDivisorOver_center,
      MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hV.1 hE,
      D.center_eq_closure_genericPoint, hp.closure_eq]
  · exact MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq
      ⟨hV, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hVs _⟩ hE hb ha

end SmoothSurface

/-- A curve on an integral surface of finite type over `k` is a prime divisor, and its support is
the closure of the generic point of that divisor. -/
private lemma exists_primeDivisor_of_isCurveIn {k : Type u} [Field k] {Y : Scheme.{u}}
    (s : Y ⟶ Spec (.of k)) [IsIntegral Y]
    [LocallyOfFiniteType s] [IsLocallyNoetherian Y] [IsNormal Y] (hYd : topologicalKrullDim Y = 2)
    {C : Y.IdealSheafData}
    (hC : IsCurveIn C) :
    ∃ Q : MMP.Mori.PrimeDivisor Y, Q.idealSheaf = C ∧
      closure ({Q.genericPoint} : Set Y) = C.support := by
  have : IsIntegral C.subscheme := hC.1
  obtain ⟨c, hcC, -⟩ := hC.exists_isGenericPoint
  have hcoh : Order.coheight c = 1 := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight s c
    rw [hcC, ← topologicalKrullDim_subscheme_eq, hC.2, hYd] at h
    generalize Order.coheight c = d at h ⊢
    induction d using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe d =>
      have : 1 + d = 2 := Nat.cast_injective (R := WithBot ℕ∞) (by push_cast; exact h)
      obtain rfl : d = 1 := by omega
      rfl
  let Q : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne c hcoh
  have hQξ : Q.genericPoint = c := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  refine ⟨Q, ?_, by rw [hQξ, hcC]⟩
  rw [← vanishingIdeal_closure_genericPoint_eq_idealSheaf, hQξ,
    ← vanishingIdeal_support_eq_self C]
  exact congrArg _ (TopologicalSpace.Closeds.ext hcC)

/-! ### Terminal surface germs are smooth -/

/-- **A terminal surface germ is smooth, with boundary of multiplicity `< 1`.** If `(U, Δ|_U)` is
terminal for an open neighbourhood `U` of the point `x` of a surface germ, then `X` is smooth at
`x` and `mult_x Δ < 1`. -/
private theorem mem_smoothLocus_and_multiplicityAt_lt_one {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {x : X} (hX : IsSurfaceGerm sX x) {Δ : QDivisor X} (hΔ : Δ.IsEffective)
    {KX : Divisor X} (U : X.Opens) (hxU : x ∈ U) [Nonempty U]
    (hT : IsTerminalPair (U.ι ≫ sX) 2 (KX.restrictOpen U) (Δ.restrictOpen U)) :
    x ∈ smoothLocus sX ∧ Δ.multiplicityAt x < 1 := by
  set x' : U := ⟨x, hxU⟩
  have hXU : IsNormalVariety k (U.ι ≫ sX) := hT.1.1
  have hKU := hT.1.2.1
  have hdimU : topologicalKrullDim U = 2 := hKU.1
  have : LocallyOfFiniteType sX := hX.1.1.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
  have hx'cl : IsClosed ({x'} : Set U) := by
    have : ({x'} : Set U) = U.ι ⁻¹' {x} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩
    rw [this]
    exact hX.2.2.1.preimage U.ι.continuous
  have hsm : ∀ y : U, y ≠ x' → y ∈ smoothLocus (U.ι ≫ sX) := fun y hy =>
    (mem_smoothLocus_ι_iff sX U y).2 (hX.2.2.2 _ fun h => hy (Subtype.ext h))
  have hgerm : IsSurfaceGerm (U.ι ≫ sX) x' := ⟨hXU, hdimU, hx'cl, hsm⟩
  obtain ⟨Y, f, hYv, hYd, ⟨_, _, _, hf⟩, -⟩ :=
    exists_isMinimalSurfaceResolution (U.ι ≫ sX) hXU hdimU
  have hx's : x' ∈ smoothLocus (U.ι ≫ sX) := by
    refine (mem_smoothLocus_iff_forall_not_isExceptionalCurve (U.ι ≫ sX) hgerm f hf).2
      fun C hC => ?_
    have : IsIntegral Y := hYv.toIsIntegral
    have : LocallyOfFiniteType (f ≫ U.ι ≫ sX) := hYv.toLocallyOfFiniteType
    obtain ⟨E, rfl, -⟩ := exists_primeDivisor_of_isCurveIn (f ≫ U.ι ≫ sX) hYd hC.1
    have h0 := IsCanonicalPair.isDiscrepancy_zero_of_isMinimalSurfaceResolution hgerm
      (isEffective_restrictOpen U hΔ) hT.isCanonicalPair hf hC
    have hexc := (isExceptional_iff_isExceptionalCurve hXU hdimU hf.1 E).2 hC
    have := hT.2.trans_le (discrep_le (D := ⟨Y, f, _, _, E⟩) hexc h0)
    simp at this
  refine ⟨(mem_smoothLocus_ι_iff sX U x').1 hx's, ?_⟩
  obtain ⟨hY, hb, F, -, hexc, hd, -⟩ := isDiscrepancy_blowUp_singleton hXU
    (isSmoothScheme_of_forall_ne hx's hsm) hdimU hKU
    (Δ.restrictOpen U) hx'cl
  have h := hT.2.trans_le (discrep_le hexc hd)
  rw [multiplicityAt_restrictOpen] at h
  have h' : (0 : ℚ) < 1 - Δ.multiplicityAt x := by exact_mod_cast EReal.coe_pos.mp h
  linarith

/-! ### Shrinking to an open set where the multiplicity is `< 1` -/

section Shrink

/-- The multiplicity of a prime divisor at a point is the order of its ideal there. -/
private theorem multiplicityAt_eq_multAt {X : Scheme.{u}} (P : MMP.Mori.PrimeDivisor X) (x : X) :
    P.multiplicityAt x = MMP.Resolution.multAt P.idealSheaf x := by
  unfold PrimeDivisor.multiplicityAt MMP.Resolution.multAt MMP.Resolution.idealOrder
  simp only [Scheme.IdealSheafData.stalkIdeal_eq_stalk]

/-- **Multiplicities near a point.** On a scheme smooth over a field of characteristic zero, if
an effective `ℚ`-divisor `Δ` has `mult_x Δ < 1`, then there are an open neighbourhood `U` of `x`
and `μ < 1` with `mult_p Δ ≤ μ` for every `p ∈ U`: the locus where a prime divisor has
multiplicity `≥ m` is closed, and the multiplicities `< 1` take finitely many values. -/
private theorem exists_opens_forall_multiplicityAt_le {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] [Smooth sX]
    (hXs : IsSmoothScheme sX) {Δ : QDivisor X} (hΔ : 0 ≤ Δ) {x : X}
    (hx : Δ.multiplicityAt x < 1) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ μ : ℚ, μ < 1 ∧ ∀ p ∈ U, Δ.multiplicityAt p ≤ μ := by
  classical
  set S := Δ.support
  have hpos : ∀ P : S, 0 < Δ P := fun P =>
    lt_of_le_of_ne (hΔ P.1) (Ne.symm (Finsupp.mem_support_iff.1 P.2))
  set N : ℕ := S.sup fun P => ⌈(Δ P)⁻¹⌉₊
  have hN : ∀ P : S, 1 ≤ (N : ℚ) * Δ P := fun P => by
    have h1 : (Δ P.1)⁻¹ ≤ (N : ℚ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast Finset.le_sup (f := fun P => ⌈(Δ P)⁻¹⌉₊) P.2)
    have := hpos P
    calc (1 : ℚ) = (Δ P.1)⁻¹ * Δ P := by field_simp
      _ ≤ N * Δ P := by gcongr
  -- the multiplicity as a sum over the components
  let t : S → X → ℕ := fun P p => (P.1.multiplicityAt p).toNat
  have hmult : ∀ p, Δ.multiplicityAt p = ∑ P : S, (t P p : ℚ) * Δ P := fun p => by
    unfold DivisorWithCoeffs.multiplicityAt
    rw [Finsupp.sum, ← Finset.sum_coe_sort]
    simp only [t, nsmul_eq_mul]
    rfl
  let T := Fintype.piFinset fun _ : S => Finset.range (N + 1)
  let val : (S → ℕ) → ℚ := fun m => ∑ P : S, (m P : ℚ) * Δ P
  -- the closed locus where the multiplicity is `≥ 1`
  let B : Set X := ⋃ m ∈ T.filter (fun m => 1 ≤ val m),
    ⋂ P : S, {p | ((m P : ℕ) : ℕ∞) ≤ P.1.multiplicityAt p}
  have hB : IsClosed B := by
    refine Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun m _ => ?_
    refine isClosed_iInter fun P => ?_
    simp_rw [multiplicityAt_eq_multAt]
    exact MMP.Resolution.isClosed_setOf_le_multAt sX P.1.idealSheaf _
  have hfin : ∀ (P : S) p, P.1.multiplicityAt p ≠ ⊤ := fun P p =>
    MMP.Threefold.Resolution.multiplicityAt_ne_top P.1
      (MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hXs P.1) p
  -- at a point off `B` the multiplicity is a value `< 1` of `val` on `T`
  have hoff : ∀ p, p ∉ B → ∃ m ∈ T, val m < 1 ∧ Δ.multiplicityAt p = val m := by
    intro p hp
    let m : S → ℕ := fun P => min (t P p) N
    have hmT : m ∈ T := Fintype.mem_piFinset.2 fun P =>
      Finset.mem_range.2 (Nat.lt_succ_of_le (min_le_right _ _))
    have hm1 : val m < 1 := by
      by_contra h1
      refine hp (Set.mem_biUnion (Finset.mem_filter.2 ⟨hmT, not_lt.1 h1⟩) ?_)
      refine Set.mem_iInter.2 fun P => ?_
      change ((min (t P p) N : ℕ) : ℕ∞) ≤ _
      exact (Nat.cast_le.2 (min_le_left _ _)).trans (ENat.coe_toNat_le_self _)
    have hle : ∀ P : S, t P p ≤ N := by
      intro P
      by_contra hlt
      have hmP : m P = N := min_eq_right (le_of_not_ge hlt)
      have hge : (m P : ℚ) * Δ P ≤ val m :=
        Finset.single_le_sum (f := fun P => (m P : ℚ) * Δ P)
          (fun P _ => mul_nonneg (Nat.cast_nonneg _) (hpos P).le) (Finset.mem_univ P)
      rw [hmP] at hge
      linarith [hN P]
    refine ⟨m, hmT, hm1, ?_⟩
    rw [hmult]
    refine Finset.sum_congr rfl fun P _ => ?_
    simp only [m, min_eq_left (hle P)]
  have hxB : x ∉ B := by
    intro hxB
    obtain ⟨m, hm, hmx⟩ := Set.mem_iUnion₂.1 hxB
    have h1 := (Finset.mem_filter.1 hm).2
    have hle : val m ≤ Δ.multiplicityAt x := by
      rw [hmult]
      refine Finset.sum_le_sum fun P _ => ?_
      have hP := Set.mem_iInter.1 hmx P
      have : m P ≤ t P x := by
        change ((m P : ℕ) : ℕ∞) ≤ _ at hP
        rw [← ENat.coe_toNat (hfin P x)] at hP
        exact_mod_cast hP
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) (hpos P).le
    linarith
  let V := (T.image val).filter (· < 1)
  have hV0 : (0 : ℚ) ∈ V := Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨fun _ => 0,
    Fintype.mem_piFinset.2 fun _ => Finset.mem_range.2 (Nat.succ_pos _), by simp [val]⟩,
    one_pos⟩
  refine ⟨⟨Bᶜ, hB.isOpen_compl⟩, hxB, V.max' ⟨0, hV0⟩,
    (Finset.mem_filter.1 (V.max'_mem ⟨0, hV0⟩)).2, fun p hp => ?_⟩
  obtain ⟨m, hmT, hm1, hpm⟩ := hoff p hp
  rw [hpm]
  exact V.le_max' _ (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hmT, hm1⟩)

end Shrink

/-! ### Smooth germs with boundary of multiplicity `< 1` are terminal -/

/-- **A smooth surface germ with boundary of multiplicity `< 1` is terminal near its point.** -/
private theorem holdsOnGerm_isTerminalPair {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {x : X} (hX : IsSurfaceGerm sX x) {Δ : QDivisor X} (hΔ : Δ.IsEffective)
    {KX : Divisor X} (hK : KX.IsCanonicalDivisor sX 2) (hxs : x ∈ smoothLocus sX)
    (hm : Δ.multiplicityAt x < 1) :
    HoldsOnGerm {x} (fun U : X.Opens => ∀ [Nonempty U],
        IsTerminalPair (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U KX)
          (DivisorWithCoeffs.restrictOpen U Δ)) := by
  have hXs : IsSmoothScheme sX := isSmoothScheme_of_forall_ne hxs hX.2.2.2
  have : LocallyOfFiniteType sX := hX.1.1.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
  haveI : Smooth sX := (isSmoothScheme_iff sX).1 hXs
  have hΔ0 : 0 ≤ Δ := DivisorWithCoeffs.isEffective_iff_nonneg.1 hΔ
  obtain ⟨U, hxU, μ, hμ1, hμ⟩ := exists_opens_forall_multiplicityAt_le hXs hΔ0 hm
  refine ⟨U, Set.singleton_subset_iff.2 hxU, ?_⟩
  intro _
  haveI := isDominant_opens_ι U
  have hUv : IsNormalVariety k (U.ι ≫ sX) := isNormalVariety_ι hX.1 U
  have hUs := isSmoothScheme_ι hXs U
  have hUd : topologicalKrullDim U = 2 := (topologicalKrullDim_opens_eq hX.1 U).trans hX.2.1
  have hKU := isCanonicalDivisor_restrictOpen hX.1 hK U
  have hΔU : 0 ≤ Δ.restrictOpen U := fun W => hΔ0 _
  refine ⟨⟨hUv, hKU, MMP.Fourfold.isQCartier_of_isSmoothScheme hUs _⟩, ?_⟩
  have hb : ((((1 - μ : ℚ)) : ℝ) : EReal) ≤
      discrep (U.ι ≫ sX) 2 (KX.restrictOpen U) (Δ.restrictOpen U) := by
    refine le_discrep_iff.2 fun D a hD ha => ?_
    have h := le_of_isDiscrepancy_of_isExceptional hUv hUs hUd hKU hΔU hμ1.le
      (fun p _ => (multiplicityAt_restrictOpen U Δ p).trans_le (hμ _ p.2)) D hD ha
    exact EReal.coe_le_coe_iff.2 (by exact_mod_cast h)
  exact lt_of_lt_of_le (EReal.coe_pos.2 (by exact_mod_cast sub_pos.2 hμ1)) hb

end MMP.Mori.TerminalSurfacePairs

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open TerminalSurfacePairs

/-- **Terminal surface pairs** (KM, Theorem 4.5(1)). Let `(x ∈ X)` be a surface germ over an
algebraically closed field `k` of characteristic zero, `Δ` an effective `ℚ`-divisor on `X` and
`K_X` a canonical divisor with `K_X + Δ` `ℚ`-Cartier. Then `(X, Δ)` is terminal near `x` (on some
open neighbourhood `U` of `x`, `(U, Δ|_U)` with canonical divisor `K_X|_U` is terminal) if and
only if `X` is smooth at `x` and `mult_x Δ < 1`. -/
@[mmp "thm_km4a_terminal_surface_pairs"]
public theorem IsSurfaceGerm.holdsOnGerm_isTerminalPair_iff {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {x : X} (hX : IsSurfaceGerm sX x) {Δ : QDivisor X} (hΔ : Δ.IsEffective)
    {KX : Divisor X} (hK : KX.IsCanonicalDivisor sX 2)
    (hKΔ : (Divisor.toQDivisor KX + Δ).IsQCartier) :
    HoldsOnGerm {x} (fun U : X.Opens => ∀ [Nonempty U],
        IsTerminalPair (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U KX)
          (DivisorWithCoeffs.restrictOpen U Δ)) ↔
      x ∈ smoothLocus sX ∧ DivisorWithCoeffs.multiplicityAt Δ x < 1 := by
  refine ⟨fun ⟨U, hxU, hU⟩ ↦ ?_, fun ⟨hxs, hm⟩ ↦ holdsOnGerm_isTerminalPair hX hΔ hK hxs hm⟩
  have hxU' : x ∈ U := hxU rfl
  haveI : Nonempty U := ⟨⟨x, hxU'⟩⟩
  exact mem_smoothLocus_and_multiplicityAt_lt_one hX hΔ U hxU' hU

end MMP.Mori

end
