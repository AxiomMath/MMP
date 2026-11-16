module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChainLabel
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolutionExists
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.CurveRankShrinking
import MMP.Topology.Sheaves.LocalSystem.ParallelTransport
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight

/-!
# Two local computations: surface singularities and punctured local systems

This file collects two independent results used in the study of singular threefolds and fourfolds.

**Log discrepancies over a singular surface point.** Let `(S, Δ)` be an effective pair with
rational boundary on a normal quasi-projective surface over a field `K` of characteristic zero
and `p ∈ S` a singular closed point. Let `f : T ⟶ S` be the minimal resolution, so that `K_T` is
`f`-nef. Since `S` is singular at `p` and `T` is smooth, the fibre of `f` over `p` is infinite
(over the locus of finite fibres `f` is an isomorphism), so it contains a prime divisor of `T`.
Write `f^*(K_S + Δ) = K_T + Δ_T`; the coefficient of `Δ_T` along a prime divisor `F` of `T` is
`-a(F; S, Δ)`. On the non-exceptional primes `Δ_T` is the strict transform of `Δ`, which is
effective, and an exceptional prime lies over a closed point. If every prime `Eᵢ` over `p` had
`a(Eᵢ; S, Δ) > 0`, negative definiteness of the intersection matrix of the `Eᵢ` would give some
`j` with `(Δ_T · Eⱼ) > 0`, while `(f^*(K_S + Δ) · Eⱼ) = 0` and `(K_T · Eⱼ) ≥ 0` force
`(Δ_T · Eⱼ) ≤ 0`. Hence some `Eᵢ` has log discrepancy `1 + a(Eᵢ; S, Δ) ≤ 1`.

**The rank of a punctured local system.** Let `Y` be a normal complex fourfold, `T ⊆ Sing Y` an
irreducible curve, `T° ⊆ T` a local-system open (`MMP.Fourfold.IsLocalSystemOpen`) and
`t ∈ T°(ℂ)`. The rank `b_T = dim_ℚ H²_c(T°, 𝒱_T)` (`MMP.Fourfold.curveLocalSystemRank`) is the
dimension of the monodromy coinvariants of the fibre `𝒱_{T,t}`
(`MMP.Fourfold.curveLocalSystemFibre`). Parallel transport makes the monodromy image `G` a set of
linear automorphisms closed under composition. When `G` is finite, averaging over `G` splits the
fibre as the direct sum of the invariants and the span of the `w - g w`, so
`b_T = dim_ℚ 𝒱_{T,t}^G`.

## Main results

* `MMP.Threefold.exists_isLogDiscrepancy_le_one_of_notMem_smoothLocus`: over a singular closed
  point `p` of a surface pair there is a divisor `(T, f, E)`, with `f` projective and `T` smooth
  over `K`, whose centre on `S` is `p` and whose log discrepancy is at most one.
* `MMP.Fourfold.IsLocalSystemOpen.curveLocalSystemRank_eq_finrank_invariants`: if the monodromy
  image is finite, `b_T` is the dimension of the monodromy invariants of `𝒱_{T,t}`.

## Implementation notes

The monodromy image is the set of linear automorphisms `g` of `𝒱_{T,t}` realised by parallel
transport along some loop `γ` at `t`: `g w = v` exactly when some global section of the inverse
image `γ^* 𝒱_T` on `[0, 1]` has germ `w` at `0` and germ `v` at `1`, the fibres of `γ^* 𝒱_T`
being identified with those of `𝒱_T` by `MMP.Fourfold.stalkToPullbackStalk`. The invariants are
the intersection of the fixed spaces `ker (g - 1)` for `g` in the image.

## References

* [KM98] Kollár, Mori, *Birational geometry of algebraic varieties*, 2.25, 4.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Threefold

open MMP.Mori

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Dimension theory on surfaces -/

/-- In a scheme, a proper specialization `y ⤳ x` is a strict inequality `x < y`. -/
private theorem lt_of_specializes_of_ne {X : Scheme.{u}} {x y : X} (h : y ⤳ x) (hne : x ≠ y) :
    x < y :=
  lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr h,
    fun h' => hne ((Scheme.le_iff_specializes.mp h').antisymm h).eq⟩

/-- In a quasi-compact scheme of dimension at most two, a point of coheight at least two is
closed. -/
private theorem isClosed_singleton_of_two_le_coheight {X : Scheme.{u}} [CompactSpace X]
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
  have hcx : c < x := lt_of_specializes_of_ne hxc (Ne.symm hne)
  have h0 : x < p ⟨1, by omega⟩ := by
    rw [← hp]
    exact p.step ⟨0, by omega⟩
  have h1 : p ⟨1, by omega⟩ < p ⟨2, by omega⟩ := p.step ⟨1, by omega⟩
  exact false_of_lt_lt_lt_of_topologicalKrullDim_le_two hdim (hlt hcx) (hlt h0) (hlt h1)

/-- The dimension of a scheme is the Krull dimension of its points under specialization. -/
private theorem topologicalKrullDim_eq_krullDim (X : Scheme.{u}) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-- On an integral surface, a point which is neither closed nor the generic point has coheight
one. -/
private theorem coheight_eq_one_of_not_isClosed {S : Scheme.{u}} [IsIntegral S]
    (hS : topologicalKrullDim S = 2) {a : S} (hgen : a ≠ genericPoint S)
    (hna : ¬ IsClosed ({a} : Set S)) : Order.coheight a = 1 := by
  have hlt : a < genericPoint S :=
    lt_of_specializes_of_ne ((genericPoint_spec S).specializes (Set.mem_univ a)) hgen
  obtain ⟨z, hza, hzne⟩ : ∃ z ∈ closure ({a} : Set S), z ≠ a := by
    by_contra! hcon
    exact hna (closure_subset_iff_isClosed.mp fun z hz => Set.mem_singleton_iff.mpr (hcon z hz))
  have hzlt : z < a := lt_of_specializes_of_ne (specializes_iff_mem_closure.mpr hza) hzne
  have h1 : ((Order.height a + Order.coheight a : ℕ∞) : WithBot ℕ∞) ≤ 2 := by
    rw [← hS, topologicalKrullDim_eq_krullDim,
      Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun b : S => Order.height b + Order.coheight b) a)
  have h2 : 1 ≤ Order.height a := le_trans (by simp) (Order.height_add_one_le hzlt)
  refine le_antisymm ?_ (le_trans (by simp) (Order.coheight_add_one_le hlt))
  exact (ENat.add_le_add_iff_left ENat.one_ne_top).mp
    ((add_le_add_left h2 _).trans (WithBot.coe_le_coe.mp h1) : 1 + Order.coheight a ≤ 1 + 1)

/-- On an integral surface locally of finite type over a field, the generic point of a prime
divisor is not closed. -/
private theorem not_isClosed_singleton_genericPoint {K : Type u} [Field K] {T : Scheme.{u}}
    [IsIntegral T] (sT : T ⟶ Spec (.of K)) [LocallyOfFiniteType sT]
    (hT : topologicalKrullDim T = 2) (G : MMP.Mori.PrimeDivisor T) :
    ¬ IsClosed ({G.genericPoint} : Set T) := by
  intro hcl
  letI : T.Over (Spec (.of K)) := ⟨sT⟩
  haveI : LocallyOfFiniteType (T ↘ Spec (.of K)) := ‹LocallyOfFiniteType sT›
  have h := MMP.height_add_coheight_eq_krullDim K G.genericPoint
  have hc : Order.coheight G.genericPoint = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint G
  have hh : Order.height G.genericPoint = 0 := by
    rw [Order.height_eq_zero]
    intro b hb
    have hb' : b ∈ closure {G.genericPoint} :=
      specializes_iff_mem_closure.mp (Scheme.le_iff_specializes.mp hb)
    rw [hcl.closure_eq] at hb'
    rw [Set.mem_singleton_iff.mp hb']
  have hk : Order.krullDim T = 2 := (topologicalKrullDim_eq_krullDim T).symm.trans hT
  rw [hc, hh, hk] at h
  norm_num at h

/-! ### Curves over a closed point -/

open MMP.Resolution in
/-- A prime divisor of a surface `T`, projective over a variety `S`, whose generic point maps to a
closed point is (the generic point of) a projective curve contracted by the morphism. -/
private theorem exists_isContractedProjectiveCurve_of_map_eq {K : Type u} [Field K]
    {S T : Scheme.{u}} {sS : S ⟶ Spec (.of K)} (hS : AlgebraicGeometry.IsVariety K sS)
    [IsIntegral T] (f : T ⟶ S) (hT : AlgebraicGeometry.IsVariety K (f ≫ sS))
    (hdimT : topologicalKrullDim T = 2) (hproj : IsProjectiveMorphism f) {p : S}
    (hp : IsClosed ({p} : Set S)) (G : MMP.Mori.PrimeDivisor T) (hG : f G.genericPoint = p) :
    ∃ C : ProperCurve (f ≫ sS), C.point = G.genericPoint ∧
      IsContractedProjectiveCurve (f ≫ sS) f C := by
  haveI : QuasiCompact (f ≫ sS) := hT.toQuasiCompact
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (f ≫ sS)
  haveI : LocallyOfFiniteType (f ≫ sS) := hT.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sS)
  haveI : IsNoetherian T := ⟨⟩
  have hsupp : (G.support : Set T) = closure {G.genericPoint} :=
    AlgebraicGeometry.PrimeDivisor.support_eq_closure G
  have hna := not_isClosed_singleton_genericPoint (f ≫ sS) hdimT G
  obtain ⟨c, -, hηc, hne⟩ := exists_isClosed_singleton_specializes hna
  have hGdim : topologicalKrullDim (G.support : Set T) = 1 := by
    refine topologicalKrullDim_eq_one_of_ne_univ (by rw [hdimT]) (hsupp ▸ isClosed_closure) ?_
      (e := G.genericPoint) (c := c) (by rw [hsupp]; exact subset_closure rfl)
      (by rw [hsupp]; exact specializes_iff_mem_closure.mp hηc) hηc hne
    intro huniv
    have hg : genericPoint T ∈ closure ({G.genericPoint} : Set T) :=
      hsupp ▸ huniv ▸ Set.mem_univ _
    have heq : G.genericPoint = genericPoint T :=
      (specializes_iff_mem_closure.mpr hg).antisymm
        ((genericPoint_spec T).specializes trivial) |>.eq
    have h1 : Order.coheight G.genericPoint = 1 :=
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint G
    rw [heq, Order.coheight_eq_zero.mpr (fun b _ => Scheme.le_iff_specializes.mpr
      ((genericPoint_spec T).specializes trivial))] at h1
    exact absurd h1 (by decide)
  have himg : closure (f.base '' (G.support : Set T)) = {p} := by
    apply Set.Subset.antisymm
    · refine closure_minimal ?_ hp
      rintro _ ⟨y, hy, rfl⟩
      rw [hsupp] at hy
      have h' : f y ∈ closure {f G.genericPoint} :=
        specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hy).map f.continuous)
      rwa [hG, hp.closure_eq] at h'
    · rintro _ rfl
      exact subset_closure ⟨G.genericPoint, by rw [hsupp]; exact subset_closure rfl, hG⟩
  have hP : topologicalKrullDim (closure (f.base '' (G.support : Set T))) <
      topologicalKrullDim (G.support : Set T) := by
    rw [hGdim, himg]
    have h0 : topologicalKrullDim ({p} : Set S) ≤ 0 :=
      @topologicalKrullDim_zero_of_discreteTopology _ _
        (@Subsingleton.discreteTopology _ _ (Set.subsingleton_singleton (a := p)).coe_sort)
    exact lt_of_le_of_lt h0 (by decide)
  exact exists_isContractedProjectiveCurve_of_isExceptional hT hdimT hS f rfl hproj G hP

/-! ### Intersection numbers on a smooth scheme -/

/-- On a smooth scheme the intersection number with a proper curve is linear in the divisor:
`(D · C) = ∑_G d_G (G · C)`. -/
private theorem intersectionNumber_eq_sum {K : Type u} [Field K] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of K)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (hsm : IsSmoothScheme sX) (C : ProperCurve sX) (D : QDivisor X) :
    D.intersectionNumber K sX C.ι C.dim_le (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm D) =
      ∑ G ∈ D.support,
        D G * QDivisor.intersectionNumber K sX C.ι C.dim_le (Finsupp.single G (1 : ℚ))
        (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _) := by
  classical
  have hq := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  let L : QDivisor X →+ ℚ :=
    { toFun := fun D => D.intersectionNumber K sX C.ι C.dim_le (hq D)
      map_zero' := by
        simpa using QDivisor.intersectionNumber_smul K sX C.ι C.dim_le 0 0 (hq 0) (hq ((0 : ℚ) • 0))
      map_add' := fun D D' => QDivisor.intersectionNumber_add' K sX C.ι C.dim_le D D' _ _ _ }
  change L D = ∑ G ∈ D.support, D G * L (Finsupp.single G 1)
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun G _ => ?_
  rw [show Finsupp.single G (D G) = D G • Finsupp.single G (1 : ℚ) by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
  exact QDivisor.intersectionNumber_smul K sX C.ι C.dim_le _ _ _ _

/-- The intersection number depends only on the divisor, not on the proof that it is
`ℚ`-Cartier. -/
private theorem intersectionNumber_congr {K : Type u} [Field K] {X C : Scheme.{u}}
    {sX : X ⟶ Spec (.of K)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] (i : C ⟶ X)
    [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) {D D' : QDivisor X} (h : D = D')
    (hD : D.IsQCartier) (hD' : D'.IsQCartier) :
    D.intersectionNumber K sX i hdim hD = D'.intersectionNumber K sX i hdim hD' := by
  subst h
  rfl

/-- The `ℚ`-divisor of a prime divisor `G` with coefficient one. -/
private theorem toQDivisor_single_one {X : Scheme.{u}} (G : MMP.Mori.PrimeDivisor X) :
    Divisor.toQDivisor (Finsupp.single G (1 : ℤ)) = Finsupp.single G (1 : ℚ) := by
  simpa using MMP.Threefold.Resolution.toQDivisor_single G 1

/-! ### Relative nefness of the canonical divisor on the minimal resolution -/

open MMP.Resolution in
/-- If `𝒪_X(D)` is the divisorial sheaf of a Cartier Weil divisor `D'`, then the intersection
number of `D` with a projective curve is the degree of `D'` along it. -/
private lemma cartierCurveIntersection_eq_degreeOn {k : Type u} [Field k] {S : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} [IsNormal S] [IsLocallyNoetherian S] [QuasiCompact sS]
    {D : S.CartierDivisor} {D' : Divisor S} (hD' : D'.IsCartier)
    (e : MMP.CartierDivisor.sheaf D ≅ D'.divisorialSheaf) (C : ProperCurve sS)
    (hC : IsProjectiveMorphism (C.ι ≫ sS)) :
    cartierCurveIntersection D C = D'.degreeOn k sS C.ι C.dim_le hD' := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sS
  haveI hinv := hD'.isInvertibleModule_divisorialSheaf
  haveI : Stacks.Ample.IsInvertibleModule S (MMP.CartierDivisor.sheaf D) :=
    Stacks.UFDExtensionGlobal.isInvertible_of_iso e.symm hinv
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      (MMP.CartierDivisor.sheaf D) := this
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf := hinv
  have hcurve : AlgebraicGeometry.IsCurve k (C.ι ≫ sS) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := C.dim_eq }
  have : AlgebraicGeometry.IsProjectiveVariety k (C.ι ≫ sS) :=
    { toIsVariety := hcurve.toIsVariety
      isProjective := hC }
  have : Stacks.Ample.IsInvertibleModule C.scheme
      ((Scheme.Modules.pullback C.ι).obj (MMP.CartierDivisor.sheaf D)) :=
    MMP.Mori.isInvertible_pullback_obj C.ι _
  unfold cartierCurveIntersection lineBundleCurveIntersection
  rw [MMP.Resolution.degree_eq_invertibleCurveDegree (C.ι ≫ sS) _ C.dim_le,
    ← MMP.Mori.degreeOn_eq_invertibleCurveDegree, MMP.Mori.degreeOn_eq_of_iso k sS C.ι C.dim_le e]
  rfl

open MMP.Resolution in
/-- **`K_T` is relatively nef on a minimal resolution.** For the minimal resolution `f : T ⟶ S`
and a nonzero rational `2`-form `ω` on `T`, the divisor `div(ω)` meets every projective curve
contracted by `f` nonnegatively. -/
private theorem intersectionNumber_divisorOfForm_nonneg {K : Type u} [Field K]
    {S T : Scheme.{u}} {sS : S ⟶ Spec (.of K)} [IsIntegral T] [IsNoetherian T] {f : T ⟶ S}
    [LocallyOfFiniteType (f ≫ sS)] (hmin : MMP.Resolution.IsMinimalSurfaceResolution sS f)
    [IsNormal T] [QuasiCompact (f ≫ sS)]
    (ω : RationalPluriForms (f ≫ sS) 2 1) (hω : ω ≠ 0) (C : ProperCurve (f ≫ sS))
    (hC : IsContractedProjectiveCurve (f ≫ sS) f C) :
    0 ≤ (Divisor.toQDivisor (divisorOfForm ω)).intersectionNumber K (f ≫ sS) C.ι C.dim_le
      (MMP.Fourfold.isQCartier_of_isSmoothScheme hmin.1.isSmoothScheme _) := by
  have hf := hmin.1
  haveI : AlgebraicGeometry.IsVariety K sS := hf.isVariety
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  haveI hXv : AlgebraicGeometry.IsVariety K (f ≫ sS) := {}
  haveI : IsSmoothVariety K (f ≫ sS) :=
    { toIsVariety := hXv,
      toSmooth := (@isSmoothScheme_iff _ _ _
        (LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance)).mp
          hf.isSmoothScheme }
  obtain ⟨Kc, hKc, hnef⟩ := hmin.2 ω hω
  set B : Divisor T := divisorOfForm ω
  have hBK : weilDivisorEquivFinsupp (cartierWeilDivisor Kc) = B := by
    ext P
    refine (hKc P).trans ?_
    simp only [divisorOfFormOnSmoothLocus, Finsupp.filter_apply]
    split_ifs with hP
    · rfl
    · refine absurd ⟨AlgebraicGeometry.PrimeDivisor.genericPoint P, ?_, ?_⟩ hP
      · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      · rw [show smoothLocus (f ≫ sS) = ⊤ from hf.isSmoothScheme]; trivial
  obtain ⟨hcart, -, -, hdict, -, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety K (f ≫ sS)
  have eB : MMP.CartierDivisor.sheaf Kc ≅ B.divisorialSheaf := by
    have e := (hdict Kc).some
    rw [hBK] at e
    exact e.symm
  have hnefC := hnef C hC
  simp only [curveIntersectionPairing, MMP.Mori.KCartierDivisor.ofCartier,
    MMP.Mori.ProperCurve.cycle, Finsupp.linearCombination_single, LinearMap.smul_apply,
    one_smul] at hnefC
  rw [QDivisor.intersectionNumber_toQDivisor K (f ≫ sS) C.ι C.dim_le B (hcart B),
    ← cartierCurveIntersection_eq_degreeOn (hcart B) eB C hC.1]
  exact_mod_cast hnefC

/-! ### Discrepancies on a model -/

/-- The pull-back of a nonzero rational pluricanonical form along a divisor over `X` is
nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : DivisorOver k sX) {m : ℤ}
    {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) :
    haveI := D.isIntegral
    haveI := D.isDominant
    pullbackRationalPluriForms sX D.f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have := D.isIntegral
  have := D.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := D.isBirationalMorphism.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX D.f hbij hd
  let := functionFieldAlgebra (D.f ≫ sX)
  let := functionFieldMapAlgebra D.f
  have := isScalarTower_functionFieldMap sX D.f
  have hpull : pullbackRationalPluriForms sX D.f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField D.Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← repr_pullbackFormsAlong hω m τ, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- **The discrepancy against a fixed form and a fixed Cartier multiple.** Let `K = div(ω)` and
`M = m(K + Δ)` a Cartier divisor with pull-back `M'` to `Y`. For a divisor `(Y, f, E)` over `X`
with `f` proper and discrepancy `a`, `a = ord_E(f^*ω) - coeff_E(M')/m`. -/
private theorem eq_ordPullback_sub_of_isDiscrepancy {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : DivisorOver k sX} {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) (hfp : IsProper D.f)
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) (hω : ∀ Γ, Γ.ordForm ω = K.coeff Γ)
    {m : ℕ} (hm : 0 < m) {M : Divisor X}
    (hM : Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + Δ)) (hMc : M.IsCartier)
    {M' : Divisor D.Y}
    (hM' : haveI := D.isLocallyNoetherian; haveI := D.isNormal; ∃ hC, M.IsPullback D.f hC M') :
    a = D.ordPullback ω - (m : ℚ)⁻¹ * M'.coeff D.E := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hb : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ) D
      (1 + (D.ordPullback ω : ℝ) - ∑ _i : Fin 1, (1 / (m : ℝ)) * (M'.coeff D.E : ℝ)) := by
    refine ⟨ha.1, hfp, ω, hω0, ⟨K, ha.2.1, fun Γ => (hω Γ).symm⟩, 1, fun _ => 1 / (m : ℝ),
      fun _ => M, fun _ => M', fun _ => hMc, fun Γ => ?_, fun _ => hM', rfl⟩
    have hMΓ : (M.coeff Γ : ℚ) = m * (K.coeff Γ + Δ.coeff Γ) := by
      have := congrArg (fun G : QDivisor X => G.coeff Γ) hM
      simp at this
      linear_combination this
    have hMΓ' : (M.coeff Γ : ℝ) = m * (K.coeff Γ + Δ.coeff Γ) := by exact_mod_cast hMΓ
    rw [QDivisor.coeff_toRDivisor, Fin.sum_univ_one, hMΓ', hω Γ]
    field_simp
  have h := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha hb
  rw [Fin.sum_univ_one, one_div] at h
  have h' : ((a : ℚ) : ℝ) =
      (((D.ordPullback ω : ℚ) - (m : ℚ)⁻¹ * (M'.coeff D.E : ℚ) : ℚ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h'

open Classical in
/-- The coefficient of `h⁻¹_* a` at a prime divisor `P` of `Y'`. -/
private theorem inverseTransformDivisor_apply {Y Y' : Scheme.{u}} (h : Y' ⟶ Y)
    (a : QDivisor Y) (P : MMP.Mori.PrimeDivisor Y') :
    inverseTransformDivisor h a P =
      ∑ E ∈ a.support, if inverseTransformPrimeDivisor h E = some P then a E else 0 := by
  conv_lhs => rw [← Finsupp.sum_single a]
  rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [inverseTransformDivisor_single]
  cases inverseTransformPrimeDivisor h E with
  | none => simp
  | some C => simp [Finsupp.single_apply]

/-- The inverse transform of an effective `ℚ`-divisor is effective. -/
private theorem inverseTransformDivisor_nonneg {Y Y' : Scheme.{u}} (h : Y' ⟶ Y)
    {a : QDivisor Y} (ha : ∀ P, 0 ≤ a.coeff P) (P : MMP.Mori.PrimeDivisor Y') :
    0 ≤ inverseTransformDivisor h a P := by
  classical
  rw [inverseTransformDivisor_apply]
  refine Finset.sum_nonneg fun E _ => ?_
  split_ifs
  · exact ha E
  · exact le_rfl

/-! ### The fibre over a singular point -/

/-- **The fibre over a singular point contains a curve.** Let `f : T ⟶ S` be a proper birational
morphism of integral surfaces, `S` normal and `T` smooth over `k`, and `p` a closed point of `S`
at which `S` is not smooth. Then some prime divisor of `T` has generic point over `p`. -/
private theorem exists_primeDivisor_map_genericPoint_eq {k : Type u} [Field k]
    {S T : Scheme.{u}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [IsIntegral T] [IsNoetherian T] (hdim : topologicalKrullDim S = 2)
    (hdimT : topologicalKrullDim T = 2) (f : T ⟶ S) [IsProper f] (hb : IsBirational f)
    (hsm : Smooth (f ≫ sS)) {p : S}
    (hp : IsClosed ({p} : Set S)) (hsing : p ∉ smoothLocus sS) :
    ∃ F : MMP.Mori.PrimeDivisor T, f F.genericPoint = p := by
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f hb).1
    inferInstance
  set U : S.Opens := ⟨_, hU⟩
  -- `S` is smooth over the locus of finite fibres
  have hpU : p ∉ MMP.Resolution.Bridges.finiteFibreLocus f := by
    intro hpU
    apply hsing
    refine le_smoothLocus sS (U := U) ?_ hpU
    have h1 : Smooth ((f ⁻¹ᵁ U).ι ≫ f ≫ sS) := inferInstance
    rw [← morphismRestrict_ι_assoc] at h1
    have h2 : U.ι ≫ sS = inv (f ∣_ U) ≫ (f ∣_ U ≫ U.ι ≫ sS) := by simp
    rw [h2]
    infer_instance
  -- the fibre over `p` has a point which is not closed
  have hT : IsClosed (f.base ⁻¹' {p}) := hp.preimage f.continuous
  obtain ⟨Z, hZf, hZc, hZirr, hZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  obtain ⟨e, hep, hecl⟩ : ∃ e ∈ f.base ⁻¹' {p}, ¬ IsClosed ({e} : Set T) := by
    by_contra! hall
    apply hpU
    change (f.base ⁻¹' {p}).Finite
    rw [hZ]
    refine hZf.sUnion fun W hW => ?_
    obtain ⟨g, hg⟩ := QuasiSober.sober (hZirr W hW) (hZc W hW)
    have hgcl := hall g (hZ ▸ Set.mem_sUnion_of_mem hg.mem hW)
    rw [← hg.def, hgcl.closure_eq]
    exact Set.finite_singleton g
  have hfe : f e = p := hep
  -- it is not the generic point, since the generic point of `S` is not closed
  have hgen : e ≠ genericPoint T := by
    rintro rfl
    have hfg : f (genericPoint T) = genericPoint S := map_genericPoint_eq f hb
    have hsub : Subsingleton S := ⟨fun x y => by
      have hx : x ∈ closure ({p} : Set S) := by
        rw [← hfe, hfg]; exact (genericPoint_spec S).specializes trivial |>.mem_closure
      have hy : y ∈ closure ({p} : Set S) := by
        rw [← hfe, hfg]; exact (genericPoint_spec S).specializes trivial |>.mem_closure
      rw [hp.closure_eq] at hx hy
      exact hx.trans hy.symm⟩
    have h0 : Order.krullDim S ≤ 0 := Order.krullDim_nonpos_of_subsingleton
    rw [← topologicalKrullDim_eq_krullDim, hdim] at h0
    exact absurd h0 (by decide)
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne e
    (coheight_eq_one_of_not_isClosed hdimT hgen hecl), ?_⟩
  change f (AlgebraicGeometry.PrimeDivisor.genericPoint _) = p
  rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  exact hfe

/-! ### Negativity over a closed point -/

/-- A point of the support of a prime divisor `G` maps to the image of the generic point of `G`
when that image is closed. -/
private theorem map_eq_of_mem_support {S T : Scheme.{u}} (f : T ⟶ S) (G : MMP.Mori.PrimeDivisor T)
    (hcl : IsClosed ({f G.genericPoint} : Set S)) {y : T} (hy : y ∈ (G.support : Set T)) :
    f y = f G.genericPoint := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
  have h' : f y ∈ closure {f G.genericPoint} :=
    specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hy).map f.continuous)
  rwa [hcl.closure_eq] at h'

/-- If `∑ᵢ ∑ⱼ xᵢ xⱼ Aᵢⱼ < 0` for a nonnegative vector `x`, then `∑ᵢ xᵢ Aᵢⱼ < 0` for some `j`. -/
private theorem exists_sum_mul_neg_of_sum_sum_mul_neg {ι R : Type*} [Fintype ι] [CommRing R]
    [LinearOrder R] [IsStrictOrderedRing R] {x : ι → R}
    (hx : ∀ i, 0 ≤ x i) {A : ι → ι → R} (h : ∑ i, ∑ j, x i * x j * A i j < 0) :
    ∃ j, ∑ i, x i * A i j < 0 := by
  by_contra! hall
  refine h.not_ge ?_
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun j _ => ?_
  have : ∑ i, x i * x j * A i j = x j * ∑ i, x i * A i j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  exact mul_nonneg (hx j) (hall j)

/-- On a smooth scheme a prime divisor `G` other than the prime divisor `P` swept out by a proper
curve `C` meets `C` nonnegatively. -/
private theorem intersectionNumber_single_nonneg_of_ne {K : Type u} [Field K] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of K)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (hsm : IsSmoothScheme sX) (C : ProperCurve sX) {P G : MMP.Mori.PrimeDivisor X}
    (hC : C.point = P.genericPoint) (hGP : G ≠ P) :
    0 ≤ QDivisor.intersectionNumber K sX C.ι C.dim_le (Finsupp.single G (1 : ℚ))
      (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _) := by
  have hdeg := MMP.Threefold.Resolution.degreeOn_nonneg_of_coeff_eq_zero hsm
    (Finsupp.single G 1) (Finsupp.single_nonneg.2 zero_le_one) C P hC
    (by simp [Finsupp.single_apply, hGP])
  rw [intersectionNumber_congr _ _ (toQDivisor_single_one G).symm _
      (QDivisor.isQCartier_toQDivisor
        (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _)),
    QDivisor.intersectionNumber_toQDivisor K sX C.ι C.dim_le _
      (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _)]
  exact_mod_cast hdeg

/-- On a smooth scheme over `S`, a prime divisor `G` lying over a closed point other than `p`
does not meet a proper curve `C` lying over `p`. -/
private theorem intersectionNumber_single_eq_zero_of_map_ne {K : Type u} [Field K]
    {S T : Scheme.{u}} {sT : T ⟶ Spec (.of K)} [QuasiCompact sT] [IsLocallyNoetherian T]
    [IsNormal T] (hsm : IsSmoothScheme sT) (f : T ⟶ S) {p : S} (hp : IsClosed ({p} : Set S))
    (C : ProperCurve sT) (hC : f C.point = p) {G : MMP.Mori.PrimeDivisor T}
    (hcl : IsClosed ({f G.genericPoint} : Set S)) (hG : f G.genericPoint ≠ p) :
    QDivisor.intersectionNumber K sT C.ι C.dim_le (Finsupp.single G (1 : ℚ))
      (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _) = 0 := by
  have hdisj : Disjoint (G.support : Set T) (closure ({C.point} : Set T)) := by
    refine Set.disjoint_left.2 fun y hyG hyF => hG ?_
    have h1 : f y ∈ closure {f C.point} :=
      specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hyF).map f.continuous)
    rw [hC, hp.closure_eq, map_eq_of_mem_support f G hcl hyG] at h1
    exact h1
  rw [intersectionNumber_congr _ _ (toQDivisor_single_one G).symm _
    (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm G)]
  exact MMP.Threefold.Resolution.intersectionNumber_single_eq_zero_of_disjoint hsm G C hdisj

open Classical in
/-- If every negative component of `Δ_T` not over `p` lies over a closed point, then for a proper
curve `C` over `p` the intersection number `(Δ_T · C)` is at least the contribution of the
components of `Δ_T` over `p`. -/
private theorem sum_filter_le_intersectionNumber {K : Type u} [Field K] {S T : Scheme.{u}}
    {sT : T ⟶ Spec (.of K)} [QuasiCompact sT] [IsLocallyNoetherian T] [IsNormal T]
    (hsm : IsSmoothScheme sT) (f : T ⟶ S) {p : S} (hp : IsClosed ({p} : Set S))
    (C : ProperCurve sT) {P : MMP.Mori.PrimeDivisor T} (hC : C.point = P.genericPoint)
    (hP : f P.genericPoint = p) (ΔT : QDivisor T)
    (hoff : ∀ G : MMP.Mori.PrimeDivisor T, f G.genericPoint ≠ p → ΔT G < 0 →
      IsClosed ({f G.genericPoint} : Set S)) :
    ∑ G ∈ ΔT.support.filter (fun G => f G.genericPoint = p),
        ΔT G * QDivisor.intersectionNumber K sT C.ι C.dim_le (Finsupp.single G 1)
          (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _) ≤
      ΔT.intersectionNumber K sT C.ι C.dim_le
        (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm ΔT) := by
  rw [intersectionNumber_eq_sum hsm C ΔT,
    ← Finset.sum_filter_add_sum_filter_not ΔT.support (fun G => f G.genericPoint = p)]
  refine le_add_of_nonneg_right (Finset.sum_nonneg fun G hG => ?_)
  rw [Finset.mem_filter] at hG
  rcases le_or_gt 0 (ΔT G) with h0 | h0
  · exact mul_nonneg h0 (intersectionNumber_single_nonneg_of_ne hsm C hC fun h => hG.2 (h ▸ hP))
  · rw [intersectionNumber_single_eq_zero_of_map_ne hsm f hp C (by rw [hC, hP])
      (hoff G hG.2 h0) hG.2, mul_zero]

open MMP.Resolution in
/-- **Negativity lemma over a closed point.** Let `f : T ⟶ S` be a projective birational morphism
from a smooth surface to a quasi-projective variety, `p ∈ S` a closed point over which some prime
divisor of `T` lies, and `Δ_T` a `ℚ`-divisor on `T` with `(Δ_T · C) ≤ 0` for every projective
curve `C` contracted by `f`, and whose negative components not over `p` lie over closed points.
Then some prime divisor over `p` has nonnegative coefficient in `Δ_T`. -/
private theorem exists_nonneg_coeff_of_intersectionNumber_nonpos {K : Type u} [Field K]
    {S T : Scheme.{u}} {sS : S ⟶ Spec (.of K)} (hS : AlgebraicGeometry.IsVariety K sS)
    (hSqp : Stacks.HProjective.IsHQuasiProjective sS) [IsIntegral S] [IsLocallyNoetherian S]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] (f : T ⟶ S) [IsProper f]
    (hT : AlgebraicGeometry.IsVariety K (f ≫ sS)) [QuasiCompact (f ≫ sS)]
    (hsm : IsSmoothScheme (f ≫ sS)) (hdimT : topologicalKrullDim T = 2)
    (hproj : IsProjectiveMorphism f) (hb : MMP.Mori.IsBirationalMorphism f) {p : S}
    (hp : IsClosed ({p} : Set S)) {E₀ : MMP.Mori.PrimeDivisor T} (hE₀ : f E₀.genericPoint = p)
    (ΔT : QDivisor T)
    (hnef : ∀ C : ProperCurve (f ≫ sS), IsContractedProjectiveCurve (f ≫ sS) f C →
      ΔT.intersectionNumber K (f ≫ sS) C.ι C.dim_le
        (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm ΔT) ≤ 0)
    (hoff : ∀ G : MMP.Mori.PrimeDivisor T, f G.genericPoint ≠ p → ΔT G < 0 →
      IsClosed ({f G.genericPoint} : Set S)) :
    ∃ F : MMP.Mori.PrimeDivisor T, f F.genericPoint = p ∧ 0 ≤ ΔT F := by
  classical
  by_contra! hneg
  set Fib := ΔT.support.filter (fun G => f G.genericPoint = p) with hFib
  have hmemFib : ∀ G, G ∈ Fib ↔ f G.genericPoint = p := fun G => by
    rw [hFib, Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨fun h => h.2, fun h => ⟨(hneg G h).ne, h⟩⟩
  -- the prime divisors `E₁, …, E_r` over `p`, with their proper curves
  let P : Fin Fib.card → MMP.Mori.PrimeDivisor T := fun i => (Fib.equivFin.symm i : _)
  have hPinj : Function.Injective P := fun i j h => Fib.equivFin.symm.injective (Subtype.ext h)
  have hPp : ∀ i, f (P i).genericPoint = p := fun i => (hmemFib _).mp (Fib.equivFin.symm i).2
  choose C hCpt hCexc using fun i =>
    exists_isContractedProjectiveCurve_of_map_eq hS f hT hdimT hproj hp (P i) (hPp i)
  -- the coefficients `a(Eᵢ; S, Δ) = -Δ_T(Eᵢ) > 0`
  let x : Fin Fib.card → ℝ := fun i => ((-ΔT (P i) : ℚ) : ℝ)
  have hxpos : ∀ i, 0 < x i := fun i => by
    simpa [x] using hneg (P i) (hPp i)
  have hr : 0 < Fib.card := Finset.card_pos.mpr ⟨E₀, (hmemFib E₀).mpr hE₀⟩
  have hx0 : x ≠ 0 := fun h => (hxpos ⟨0, hr⟩).ne' (congrFun h _)
  -- negative definiteness: `(D · Eⱼ) < 0` for some `j`
  let A : Fin Fib.card → Fin Fib.card → ℚ := fun i j =>
    (Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber K (f ≫ sS) (C j).ι
      (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (P i))
  have hneg2 : ∑ i, ∑ j, x i * x j * (A i j : ℝ) < 0 :=
    MMP.Threefold.Resolution.sum_mul_intersectionNumber_mul_neg_of_isContractedProjectiveCurve
      hT hsm hdimT hS hSqp rfl hproj
      (MMP.Threefold.Resolution.exists_isFinite_morphismRestrict_of_isBirationalMorphism hb)
      P hPinj C hCpt hCexc x hx0
  obtain ⟨j, hj⟩ := exists_sum_mul_neg_of_sum_sum_mul_neg (fun i => (hxpos i).le) hneg2
  -- the intersection number with the curve `Eⱼ`
  let I : QDivisor T → ℚ := fun D => D.intersectionNumber K (f ≫ sS) (C j).ι (C j).dim_le
    (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm D)
  have hfib : ∑ G ∈ Fib, ΔT G * I (Finsupp.single G 1) =
      -∑ i, -ΔT (P i) * A i j := by
    rw [← Finset.sum_coe_sort Fib, ← Finset.sum_neg_distrib]
    refine (Fintype.sum_equiv Fib.equivFin.symm _ _ fun i => ?_).symm
    change -(-ΔT (P i) * A i j) = ΔT (P i) * I (Finsupp.single (P i) 1)
    rw [show A i j = I (Finsupp.single (P i) 1) from
      intersectionNumber_congr _ _ (toQDivisor_single_one (P i)) _ _]
    ring
  have hjQ : ∑ i, -ΔT (P i) * A i j < 0 := by
    have hj' : ((∑ i, -ΔT (P i) * A i j : ℚ) : ℝ) < 0 := by
      push_cast
      simpa [x] using hj
    exact_mod_cast hj'
  -- every component of `Δ_T` not over `p` meets `Eⱼ` nonnegatively
  have hsum : ∑ G ∈ Fib, ΔT G * I (Finsupp.single G 1) ≤ I ΔT :=
    sum_filter_le_intersectionNumber hsm f hp (C j) (hCpt j) (hPp j) ΔT hoff
  have hle : I ΔT ≤ 0 := hnef (C j) (hCexc j)
  linarith

end

open MMP.Resolution in
/-- On the minimal resolution `f : T ⟶ S`, for a Cartier divisor `M` on `S` and a nonzero rational
`2`-form `ω` on `T`, the divisor `m⁻¹ f^*M - div(ω)` meets every projective curve contracted by
`f` nonpositively. -/
private theorem intersectionNumber_inv_smul_pullback_sub_divisorOfForm_nonpos {K : Type u}
    [Field K] {S T : Scheme.{u}} {sS : S ⟶ Spec (.of K)} [IsSeparated sS]
    [LocallyOfFiniteType sS] [QuasiCompact sS] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    [IsIntegral T] [IsNoetherian T] [IsNormal T] {f : T ⟶ S} [LocallyOfFiniteType (f ≫ sS)]
    [QuasiCompact (f ≫ sS)] (hmin : MMP.Resolution.IsMinimalSurfaceResolution sS f)
    {M : Divisor S} (hMc : M.IsCartier)
    (hB : ∀ Z : irreducibleComponents T, f (componentGenericPoint T Z) ∉ M.supp)
    (m : ℕ) {ω : RationalPluriForms (f ≫ sS) 2 1} (hω : ω ≠ 0) (C : ProperCurve (f ≫ sS))
    (hC : IsContractedProjectiveCurve (f ≫ sS) f C) :
    ((m : ℚ)⁻¹ • Divisor.toQDivisor (M.pullback hMc hB) -
        Divisor.toQDivisor (divisorOfForm ω)).intersectionNumber K (f ≫ sS) C.ι C.dim_le
      (MMP.Fourfold.isQCartier_of_isSmoothScheme hmin.1.isSmoothScheme _) ≤ 0 := by
  have hq := MMP.Fourfold.isQCartier_of_isSmoothScheme hmin.1.isSmoothScheme
  have hM'0 : (Divisor.toQDivisor (M.pullback hMc hB)).intersectionNumber K (f ≫ sS) C.ι
      C.dim_le (hq _) = 0 := by
    rw [QDivisor.intersectionNumber_toQDivisor K (f ≫ sS) C.ι C.dim_le _
        (hMc.isCartier_pullback f hB),
      Divisor.degreeOn_pullback_eq_zero_of_isContractedBy f rfl hMc hB C hC.2, Int.cast_zero]
  have hKT0 := intersectionNumber_divisorOfForm_nonneg hmin ω hω C hC
  have hadd := QDivisor.intersectionNumber_add' K (f ≫ sS) C.ι C.dim_le
    ((m : ℚ)⁻¹ • Divisor.toQDivisor (M.pullback hMc hB) - Divisor.toQDivisor (divisorOfForm ω))
    (Divisor.toQDivisor (divisorOfForm ω)) (hq _) (hq _) (hq _)
  rw [sub_add_cancel, QDivisor.intersectionNumber_smul K _ _ _ _ _ (hq _) (hq _), hM'0,
    mul_zero] at hadd
  linarith

open Classical in
/-- If `Δ ≥ 0` and `Δ_T = f⁻¹_* Δ + (exceptional part of Δ_T)`, then a component of `Δ_T` with
negative coefficient is exceptional, so lies over a closed point of the surface `S`. -/
private theorem isClosed_map_genericPoint_of_coeff_neg {S T : Scheme.{u}} [IsLocallyNoetherian S]
    [IsNormal S] [IsSeparated (S ↘ Limits.terminal Scheme)] [CompactSpace S]
    [IsLocallyNoetherian T] [IsNormal T] (hdim : topologicalKrullDim S = 2) (f : T ⟶ S)
    {Δ : QDivisor S} (hΔ : ∀ P, 0 ≤ Δ.coeff P) {ΔT : QDivisor T}
    (hdec : ΔT = inverseTransformDivisor f Δ +
      ΔT.filter fun E => RationalMap.IsExceptional (X := T) f.toRationalMap E)
    {G : MMP.Mori.PrimeDivisor T} (hG : ΔT G < 0) : IsClosed ({f G.genericPoint} : Set S) := by
  have hGexc : RationalMap.IsExceptional (X := T) f.toRationalMap G := by
    by_contra hne
    have h1 := congrArg (fun D : QDivisor T => D G) hdec
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.filter_apply, if_neg hne,
      add_zero] at h1
    have h2 := inverseTransformDivisor_nonneg f hΔ G
    linarith
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight] at hGexc
  refine isClosed_singleton_of_two_le_coheight (by rw [hdim])
    (hGexc _ (subset_closure ⟨G.genericPoint, ?_, rfl⟩))
  change G.genericPoint ∈ G.support
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

open MMP.Resolution in
/-- **The singular-point bound on the minimal resolution.** Let `f : T ⟶ S` be the minimal
resolution of an effective surface pair `(S, Δ)` over a field of characteristic zero and `p` a
singular closed point of `S`. Some prime divisor of `T` over `p` has log discrepancy at most
one. -/
private theorem exists_isLogDiscrepancy_le_one_of_isMinimalSurfaceResolution
    {K : Type u} [Field K] {S T : Scheme.{u}} {sS : S ⟶ Spec (.of K)}
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [hSv : AlgebraicGeometry.IsVariety K sS]
    [LocallyOfFiniteType sS] [QuasiCompact sS] [IsSeparated sS] [CompactSpace S]
    [IsSeparated (S ↘ Limits.terminal Scheme)]
    (hSqp : Stacks.HProjective.IsHQuasiProjective sS) (hdim : topologicalKrullDim S = 2)
    {Δ : QDivisor S} (hΔ : MMP.Fourfold.IsCharZeroPair sS Δ) {p : S}
    (hp : IsClosed ({p} : Set S)) (hsing : p ∉ smoothLocus sS)
    [IsIntegral T] [IsNoetherian T] [IsNormal T] {f : T ⟶ S} [IsProper f] [IsDominant f]
    [LocallyOfFiniteType (f ≫ sS)] [LocallyOfFinitePresentation (f ≫ sS)] [QuasiCompact (f ≫ sS)]
    (hmin : MMP.Resolution.IsMinimalSurfaceResolution sS f) (hTv : IsNormalVariety K (f ≫ sS))
    (hbir : IsBirational f) :
    ∃ D : DivisorOver K sS, IsProjectiveMorphism D.f ∧ IsSmoothScheme (D.f ≫ sS) ∧
      (D.center : Set S) = {p} ∧
      ∃ a : ℝ, a ≤ 1 ∧
        MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor Δ) D a := by
  classical
  haveI := hΔ.charZero
  have hP : IsPair sS Δ := hΔ.isPair
  have hX : IsNormalVariety K sS := hP.isNormalVariety
  have hf := hmin.1
  have hsm : IsSmoothScheme (f ≫ sS) := hf.isSmoothScheme
  have hdimT : topologicalKrullDim T = 2 := hf.dim_source_eq
  haveI hTv' : AlgebraicGeometry.IsVariety K (f ≫ sS) := hTv.1
  -- a canonical divisor `K_S`, the discrepancies of the prime divisors of `T`
  obtain ⟨-, n, KS, hKS, -⟩ := id hP
  obtain rfl : n = 2 := by exact_mod_cast hKS.topologicalKrullDim_eq.symm.trans hdim
  let Dv : MMP.Mori.PrimeDivisor T → DivisorOver K sS :=
    fun F => ⟨T, f, hTv, hf.isBirationalMorphism, F⟩
  choose disc hdisc using fun F => MMP.Positivity.IsPair.exists_isDiscrepancy hP hKS (Dv F)
  obtain ⟨E₀, hE₀⟩ := exists_primeDivisor_map_genericPoint_eq hdim hdimT f hbir
    ((isSmoothScheme_iff (f ≫ sS)).mp hsm) hp hsing
  -- `K_S = div(ω)`, `M = m(K_S + Δ)` Cartier, `M' = f^*M`, `K_T = div(f^*ω)`
  obtain ⟨-, -, m, hm, ⟨M, hM, hMc⟩, -⟩ := hdisc E₀
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hKS
  have hB := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp f M
  set M' : Divisor T := M.pullback hMc hB
  have hωT0 : pullbackRationalPluriForms sS f ω ≠ 0 :=
    pullbackRationalPluriForms_ne_zero hX (by rw [hdim]; rfl) (Dv E₀) hω0
  set KT : Divisor T := divisorOfForm (pullbackRationalPluriForms sS f ω)
  -- the crepant boundary `Δ_T = f^*(K_S + Δ) - K_T`, with coefficients `-a(F; S, Δ)`
  set ΔY : QDivisor T := (m : ℚ)⁻¹ • Divisor.toQDivisor M' - Divisor.toQDivisor KT
  have hΔYc : ∀ F, -ΔY.coeff F = disc F := fun F => by
    rw [eq_ordPullback_sub_of_isDiscrepancy (D := Dv F) (hdisc F) (inferInstanceAs (IsProper f))
      hω0 hω hm hM hMc ⟨hB, Divisor.isPullback_pullback hMc hB⟩]
    simp [ΔY, KT]
    rfl
  have hcrep : IsCrepantBoundary sS 2 KS Δ f hTv hf.isBirationalMorphism ΔY := fun F => by
    rw [hΔYc F]; exact hdisc F
  obtain ⟨hdec, -⟩ := IsCrepantBoundary.eq_inverseTransformDivisor_add_exceptional hP hcrep
  -- some prime divisor over `p` has `a(F; S, Δ) ≤ 0`
  obtain ⟨F, hFp, hF0⟩ := exists_nonneg_coeff_of_intersectionNumber_nonpos hSv hSqp f hTv' hsm
    hdimT hf.isProjectiveMorphism hf.isBirationalMorphism hp hE₀ ΔY
    (intersectionNumber_inv_smul_pullback_sub_divisorOfForm_nonpos hmin hMc hB m hωT0)
    (fun G _ hG => isClosed_map_genericPoint_of_coeff_neg hdim f hΔ.nonneg hdec hG)
  -- the divisor `F` over `p` has log discrepancy `1 + a(F; S, Δ) ≤ 1`
  refine ⟨Dv F, hf.isProjectiveMorphism, hsm, ?_, 1 + (disc F : ℝ), ?_,
    MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hdisc F)
      (inferInstanceAs (IsProper f))⟩
  · rw [DivisorOver.center_eq_closure_genericPoint]
    change closure {f F.genericPoint} = _
    rw [hFp, hp.closure_eq]
  · have h2 : (disc F : ℝ) ≤ 0 := by
      rw [← hΔYc F]
      exact_mod_cast neg_nonpos.mpr hF0
    linarith

/-- **Over a singular point of a surface pair there is a divisor of log discrepancy at most one.**
Let `K` be a field of characteristic zero, `S` a normal quasi-projective surface over `K` and
`(S, Δ)` an effective pair with `ℚ`-boundary. For every singular closed point `p` of `S` there is
a divisor `(T, f, E)` over `S`, with `f : T ⟶ S` projective and `T` smooth over `K`, whose centre
on `S` is `{p}` and with log discrepancy `a(E; S, Δ) ≤ 1`. -/
@[mmp "lem_mmp_threefold_singular_surface_mld_bound"]
public theorem exists_isLogDiscrepancy_le_one_of_notMem_smoothLocus
    {K : Type u} [Field K] {S : Scheme.{u}} (sS : S ⟶ Spec (.of K))
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [IsQuasiProjectiveVariety K sS]
    (hdim : topologicalKrullDim S = 2) {Δ : QDivisor S} (hΔ : MMP.Fourfold.IsCharZeroPair sS Δ)
    {p : S} (hp : IsClosed ({p} : Set S)) (hsing : p ∉ smoothLocus sS) :
    ∃ D : DivisorOver K sS, IsProjectiveMorphism D.f ∧ IsSmoothScheme (D.f ≫ sS) ∧
      (D.center : Set S) = {p} ∧
      ∃ a : ℝ, a ≤ 1 ∧
        MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor Δ) D a := by
  haveI := hΔ.charZero
  have hX : IsNormalVariety K sS := hΔ.isPair.isNormalVariety
  haveI hSv : AlgebraicGeometry.IsVariety K sS := hX.1
  haveI : LocallyOfFiniteType sS := hSv.toLocallyOfFiniteType
  haveI : QuasiCompact sS := hSv.toQuasiCompact
  haveI : IsSeparated sS := hSv.toIsSeparated
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  haveI : IsSeparated (S ↘ Limits.terminal Scheme) := by
    rw [show (S ↘ Limits.terminal Scheme) = sS ≫ (Spec (.of K) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hSqp : Stacks.HProjective.IsHQuasiProjective sS :=
    ((isQuasiProjectiveVariety_iff_isHQuasiProjective K sS).1 inferInstance).2
  -- the minimal resolution `f : T ⟶ S`
  obtain ⟨T, hTi, hTn, f, hft, hmin, -⟩ := MMP.Resolution.exists_isMinimalSurfaceResolution sS hdim
  have hf := hmin.1
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  have hres : IsSmoothResolution sS f :=
    ⟨inferInstance, hf.isBirationalMorphism, hf.isSmoothScheme⟩
  obtain ⟨hTv, -, hbir⟩ := hres.isNormalVariety hX
  haveI : IsNormal T := hTv.2
  haveI : QuasiCompact (f ≫ sS) := hTv.1.toQuasiCompact
  haveI : IsDominant f := hf.isBirationalMorphism.isDominant
  haveI : LocallyOfFinitePresentation (f ≫ sS) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  exact exists_isLogDiscrepancy_le_one_of_isMinimalSurfaceResolution hSqp hdim hΔ hp hsing hmin
    hTv hbir

end MMP.Threefold

namespace MMP.Fourfold

open TopologicalSpace Opposite MMP.Mori MMP.Analytic
  MMP.Analytic.ComplexPoints

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Averaging

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

open scoped Classical

omit [CharZero K] in
/-- Composing on either side with a fixed member permutes a finite set of linear automorphisms
closed under composition, so a sum over it is unchanged. -/
private lemma sum_mul_eq {G : Set (V ≃ₗ[K] V)} (hfin : G.Finite)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) {h : V ≃ₗ[K] V} (hh : h ∈ G)
    (f : (V ≃ₗ[K] V) → V) :
    ∑ g ∈ hfin.toFinset, f (g * h) = ∑ g ∈ hfin.toFinset, f g ∧
      ∑ g ∈ hfin.toFinset, f (h * g) = ∑ g ∈ hfin.toFinset, f g := by
  have key : ∀ φ : (V ≃ₗ[K] V) → V ≃ₗ[K] V, Function.Injective φ → (∀ g ∈ G, φ g ∈ G) →
      ∑ g ∈ hfin.toFinset, f (φ g) = ∑ g ∈ hfin.toFinset, f g := fun φ hφ hG => by
    have him : hfin.toFinset.image φ = hfin.toFinset :=
      Finset.eq_of_subset_of_card_le
        (Finset.image_subset_iff.2 fun g hg => hfin.mem_toFinset.2 (hG g (hfin.mem_toFinset.1 hg)))
        (Finset.card_image_of_injective _ hφ).ge
    conv_rhs => rw [← him, Finset.sum_image fun x _ y _ hxy => hφ hxy]
  exact ⟨key _ (mul_left_injective h) fun g hg => hmul g hg h hh,
    key _ (mul_right_injective h) fun g hg => hmul h hh g hg⟩

/-- **Averaging over a finite set of automorphisms closed under composition.**
For a finite nonempty set `G` of linear automorphisms closed under composition, in
characteristic zero, the span of the `w - g w` is a complement of the common fixed space. -/
private lemma isCompl_span_sub_iInf_ker (G : Set (V ≃ₗ[K] V))
    (hfin : G.Finite) (hne : G.Nonempty) (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) :
    IsCompl (Submodule.span K {u | ∃ g ∈ G, ∃ w, u = w - g w})
      (⨅ g ∈ G, LinearMap.ker ((g : V →ₗ[K] V) - LinearMap.id)) := by
  set s := hfin.toFinset
  have hn : (s.card : K) ≠ 0 := Nat.cast_ne_zero.2 (hfin.toFinset_nonempty.2 hne).card_pos.ne'
  have hmemI : ∀ v, v ∈ (⨅ g ∈ G, LinearMap.ker ((g : V →ₗ[K] V) - LinearMap.id)) ↔
      ∀ g ∈ G, g v = v := fun v => by
    simp [Submodule.mem_iInf, sub_eq_zero]
  let avg : V →ₗ[K] V := (s.card : K)⁻¹ • ∑ g ∈ s, (g : V →ₗ[K] V)
  have avg_apply : ∀ v, avg v = (s.card : K)⁻¹ • ∑ g ∈ s, g v := fun v => by
    simp [avg, LinearMap.sum_apply]
  have avg_sub : ∀ v, v - avg v = (s.card : K)⁻¹ • ∑ g ∈ s, (v - g v) := fun v => by
    rw [avg_apply, Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul K, smul_sub,
      smul_smul, inv_mul_cancel₀ hn, one_smul]
  refine ⟨Submodule.disjoint_def.2 fun v hvS hvI => ?_, codisjoint_iff.2 (eq_top_iff.2 ?_)⟩
  · have hker : Submodule.span K {u | ∃ g ∈ G, ∃ w, u = w - g w} ≤ LinearMap.ker avg := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, hg, w, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero, avg_apply, avg_apply]
      exact congrArg _ (sum_mul_eq hfin hmul hg fun x => x w).1.symm
    rw [sub_eq_zero.1 ((avg_sub v).trans ?_)]
    · exact hker hvS
    · rw [Finset.sum_congr rfl fun g hg =>
        sub_eq_zero.2 ((hmemI v).1 hvI g (hfin.mem_toFinset.1 hg)).symm, Finset.sum_const_zero,
        smul_zero]
  · intro v _
    rw [← sub_add_cancel v (avg v)]
    refine Submodule.add_mem_sup ?_ ((hmemI _).2 fun h hh => ?_)
    · rw [avg_sub]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g hg =>
        Submodule.subset_span ⟨g, hfin.mem_toFinset.1 hg, v, rfl⟩)
    · rw [avg_apply, map_smul, map_sum]
      exact congrArg _ (sum_mul_eq hfin hmul hh fun x => x v).2

end Averaging

section Sheaves

/-- The identification of stalks at equal points is a cast. -/
private lemma stalkCongr_of_eq_apply {X : TopCat.{0}} (F : TopCat.Presheaf (ModuleCat.{0} ℚ) X)
    {x y : X} (h : x = y) (e : (ToType (F.stalk x)) = ToType (F.stalk y)) (w : F.stalk x) :
    (F.stalkCongr (.of_eq h)).hom.hom w = cast e w := by
  subst h
  change (F.stalkSpecializes (specializes_refl x)).hom w = w
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The global section of the constant sheaf with value `e`. -/
private noncomputable def constSection {W : TopCat.{0}} (E : ModuleCat.{0} ℚ) (e : E) :
    ToType (((TopCat.Sheaf.forget _ W).obj
      ((constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj E)).obj (op ⊤)) :=
  ((CategoryTheory.toSheafify (Opens.grothendieckTopology W)
    ((Functor.const (Opens W)ᵒᵖ).obj E)).app (op ⊤)).hom e

/-- Every germ of a constant sheaf is the germ of a constant section. -/
private theorem exists_germ_constSection_eq {W : TopCat.{0}} (E : ModuleCat.{0} ℚ)
    (p : W) (c : ToType (((TopCat.Sheaf.forget _ W).obj
      ((constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj E)).stalk p)) :
    ∃ e : E, ((TopCat.Sheaf.forget _ W).obj
      ((constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj E)).germ
          ⊤ p (Opens.mem_top p) (constSection E e) = c := by
  let K : TopCat.Presheaf (ModuleCat.{0} ℚ) W := (Functor.const (Opens W)ᵒᵖ).obj E
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso p (ModuleCat.{0} ℚ) K
  obtain ⟨c', hc'⟩ := (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) p).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology W) K))).2 c
  obtain ⟨U, hU, e, rfl⟩ := K.exists_germ_eq c'
  refine ⟨e, ?_⟩
  have this : K.germ U p hU e = K.germ ⊤ p (Opens.mem_top p) e :=
    TopCat.Presheaf.germ_res_apply K (homOfLE (le_top : U ≤ ⊤)) p hU e
  rw [← hc', this]
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := K) ⊤ p (Opens.mem_top p)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology W) K) e).symm

/-- A sheaf isomorphic to a constant sheaf has a global section with any prescribed germ. -/
private lemma exists_global_germ_eq {W : TopCat.{0}} {P : TopCat.Sheaf (ModuleCat.{0} ℚ) W}
    {E : ModuleCat.{0} ℚ}
    (φ : P ≅ (constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj E) (x : W)
    (c : ((TopCat.Sheaf.forget _ W).obj P).stalk x) :
    ∃ s : ToType (P.obj.obj (op ⊤)),
      c = (((TopCat.Sheaf.forget _ W).obj P).germ ⊤ x trivial).hom s := by
  obtain ⟨e, he⟩ := exists_germ_constSection_eq E x
    ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ W).map φ.hom) c)
  refine ⟨(((TopCat.Sheaf.forget _ _).map φ.inv).app (op ⊤)).hom (constSection E e), ?_⟩
  refine Eq.trans ?_ (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial _ _)
  exact (((TopCat.Presheaf.stalkFunctor _ x).mapIso
    ((TopCat.Sheaf.forget _ W).mapIso φ)).hom_inv_id_apply c).symm.trans (congrArg _ he.symm)

end Sheaves

/-- `w` and `v` are the end germs of a global section of the inverse image of `L` along the
loop `γ`: the parallel transport of `w` along `γ` is `v`. -/
private def LoopRel {X : TopCat.{0}} (L : TopCat.Sheaf (ModuleCat.{0} ℚ) X) {t : X}
    (γ : Path t t) (w v : ((TopCat.Sheaf.forget _ _).obj L).stalk t) : Prop :=
  ∃ s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
      (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj L).obj.obj (op ⊤)),
    (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
        L 0).hom
      ((((TopCat.Sheaf.forget _ _).obj L).stalkCongr (.of_eq γ.source.symm)).hom.hom w) =
      (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj L)).germ
          ⊤ 0 trivial).hom s ∧
    (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
        L 1).hom
      ((((TopCat.Sheaf.forget _ _).obj L).stalkCongr (.of_eq γ.target.symm)).hom.hom v) =
      (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj L)).germ
          ⊤ 1 trivial).hom s

/-- In a local system on a locally path-connected space, the transport relation along a loop
is the graph of a parallel transport `tr`, compatible with concatenation. -/
private lemma exists_loopRel_iff {X : TopCat.{0}} [LocallyPathConnectedSpace X]
    {L : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (hL : IsLocalSystem L) (t : X) :
    ∃ tr : Path t t → (((TopCat.Sheaf.forget _ _).obj L).stalk t ≃ₗ[ℚ]
        ((TopCat.Sheaf.forget _ _).obj L).stalk t),
      (∀ γ w v, LoopRel L γ w v ↔ tr γ w = v) ∧ ∀ γ δ, tr γ * tr δ = tr (δ.trans γ) := by
  have hinj : ∀ {a b : X} (h : a = b), Function.Injective
      (((TopCat.Sheaf.forget _ X).obj L).stalkCongr (.of_eq h)).hom.hom := fun h =>
    (ConcreteCategory.bijective_of_isIso (C := ModuleCat.{0} ℚ) _).1
  refine ⟨fun γ => (hL.parallelTransport (Path.Homotopic.Quotient.mk γ)).toLinearEquiv, ?_, ?_⟩
  · intro γ w v
    constructor
    · rintro ⟨s, h0, h1⟩
      have key := hL.parallelTransport_germ γ s w
        (by rw [← stalkCongr_of_eq_apply _ γ.source.symm]; exact h0)
      rw [← stalkCongr_of_eq_apply _ γ.target.symm] at key
      have := isIso_stalkToPullbackStalk
        (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap) L 1
      exact hinj γ.target.symm
        ((ConcreteCategory.bijective_of_isIso (C := ModuleCat.{0} ℚ) _).1 (key.trans h1.symm))
    · rintro rfl
      obtain ⟨φ⟩ := hL.nonempty_pullback_path_iso_constantSheaf γ
      obtain ⟨s, h0⟩ := exists_global_germ_eq φ 0
        ((stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
          L 0).hom ((((TopCat.Sheaf.forget _ X).obj L).stalkCongr
            (.of_eq γ.source.symm)).hom.hom w))
      have h1 := hL.parallelTransport_germ γ s w
        (by rw [← stalkCongr_of_eq_apply _ γ.source.symm]; exact h0)
      rw [← stalkCongr_of_eq_apply _ γ.target.symm] at h1
      exact ⟨s, h0, h1⟩
  · intro γ δ
    ext w
    change _ = (hL.parallelTransport
      ((Path.Homotopic.Quotient.mk δ).trans (Path.Homotopic.Quotient.mk γ))).hom w
    rw [hL.parallelTransport_trans]
    rfl

/-- **The rank is an invariant dimension.** Let `Y` be a normal complex fourfold, `T ⊆ Sing Y`
an irreducible curve, `T°` a local-system open of `T` and `t ∈ T°(ℂ)`. If the monodromy image
`G ⊆ GL(𝒱_{T,t})` — the automorphisms of the fibre given by parallel transport along loops at
`t` — is finite, then `b_T = dim_ℚ H²_c(T°, 𝒱_T)` is the dimension of the invariants
`⋂_{g ∈ G} ker (g - 1)`. -/
@[mmp "lem_oai4_c2_rank_equals_invariants"]
public theorem IsLocalSystemOpen.curveLocalSystemRank_eq_finrank_invariants
    {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} (hY : MMP.Mori.IsVariety ℂ sY) [IsNormal Y]
    (hdim : topologicalKrullDim Y = 4) {T : IrreducibleCloseds Y}
    (hT : topologicalKrullDim (T : Set Y) = 1) (hTsing : (T : Set Y) ⊆ singularLocus sY)
    {To : (curveScheme T).Opens} (hTo : IsLocalSystemOpen sY To)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (G : Set (curveLocalSystemFibre sY To t ≃ₗ[ℚ] curveLocalSystemFibre sY To t))
    (hG : ∀ g, g ∈ G ↔ ∃ γ : Path t t, ∀ w v : curveLocalSystemFibre sY To t,
        (∃ s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
            (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
              (curveLocalSystem sY To)).obj.obj (op ⊤)),
          (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
              (curveLocalSystem sY To) 0).hom
            ((((TopCat.Sheaf.forget _ _).obj (curveLocalSystem sY To)).stalkCongr
              (.of_eq γ.source.symm)).hom.hom w) =
            (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
              (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
                (curveLocalSystem sY To))).germ ⊤ 0 trivial).hom s ∧
          (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
              (curveLocalSystem sY To) 1).hom
            ((((TopCat.Sheaf.forget _ _).obj (curveLocalSystem sY To)).stalkCongr
              (.of_eq γ.target.symm)).hom.hom v) =
            (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
              (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
                (curveLocalSystem sY To))).germ ⊤ 1 trivial).hom s) ↔
        g w = v)
    (hGfin : G.Finite) :
    curveLocalSystemRank sY To = Module.finrank ℚ
      (⨅ g ∈ G, LinearMap.ker ((g : curveLocalSystemFibre sY To t →ₗ[ℚ]
        curveLocalSystemFibre sY To t) - LinearMap.id) :
        Submodule ℚ (curveLocalSystemFibre sY To t)) := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY
  haveI := locallyPathConnectedSpace_analyticSpace (To.ι ≫ curveι T ≫ sY)
  obtain ⟨tr, htr, hmul⟩ := exists_loopRel_iff hTo.isLocalSystem t
  have hG' : ∀ g, g ∈ G ↔ ∃ γ : Path t t, ∀ w v, LoopRel _ γ w v ↔ g w = v := hG
  have hGtr : ∀ g, g ∈ G ↔ ∃ γ, tr γ = g := by
    intro g
    rw [hG']
    refine exists_congr fun γ => ⟨fun h => ?_, fun h w v => ?_⟩
    · ext w
      exact (htr γ w (g w)).1 ((h w (g w)).2 rfl)
    · rw [htr, h]
  have hne : G.Nonempty := ⟨tr (Path.refl t), (hGtr _).2 ⟨_, rfl⟩⟩
  have hGmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G := by
    intro g hg h hh
    obtain ⟨γ, rfl⟩ := (hGtr g).1 hg
    obtain ⟨δ, rfl⟩ := (hGtr h).1 hh
    exact (hGtr _).2 ⟨_, (hmul γ δ).symm⟩
  rw [(IsLocalSystemOpen.curveLocalSystemRank_eq hY hdim hT hTsing hTo hTo).2 t,
    ← (Submodule.quotientEquivOfIsCompl _ _
      (isCompl_span_sub_iInf_ker G hGfin hne hGmul)).finrank_eq]
  congr 3
  all_goals
    ext u
    constructor
    · rintro ⟨γ, s, w, v, h0, h1, rfl⟩
      have hv : tr γ w = v := (htr γ w v).1 ⟨s, h0, h1⟩
      exact ⟨tr γ, (hGtr _).2 ⟨γ, rfl⟩, w, hv ▸ rfl⟩
    · rintro ⟨g, hg, w, rfl⟩
      obtain ⟨γ, rfl⟩ := (hGtr g).1 hg
      obtain ⟨s, h0, h1⟩ := (htr γ w (tr γ w)).2 rfl
      exact ⟨γ, s, w, tr γ w, h0, h1, rfl⟩

end MMP.Fourfold
