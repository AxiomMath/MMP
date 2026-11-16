module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.Intersection.RelativeN1FiniteDimensional
public import MMP.AlgebraicGeometry.Singularities.SurfaceNodalBoundary
public import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
public import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
public import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Resolution.Surface.SemilocalRing
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolutionUnique
public import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
public import MMP.AlgebraicGeometry.Curves.NormalizationLiftInvertible
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso

section

/-!
## Proof of the existence of a procedure datum

Let `X` be a normal variety over an algebraically closed field `k` of characteristic zero, `D`
a boundary on `X` and `f : X ⟶ Z` a small projective contraction onto a quasi-projective
variety. Then a procedure datum `(π, (F_j), H')` for `(X, D, f)` exists.

Take a strong resolution `π : Z' ⟶ Z`; `Z'` is quasi-projective, so `N¹(Z'/Z)` is spanned by
finitely many classes of Cartier divisors. On the smooth variety `Z'` every Weil divisor is
Cartier, and by weak approximation for the finitely many discrete valuations along the strict
transforms of the components of `f_*D`, each spanning divisor is linearly equivalent to one with
none of them as a component; its positive and negative parts are the divisors `F_j`. Then the
closed set `T₀ = f(Ex f) ∪ Sing Z ∪ Sing(Supp f_*D) ∪ ⋃ π(F) ∪ f(⌊D⌋)` contains none of the
points of codimension at most one considered below, and a reduced Cartier divisor `H'` with
`T₀ ⊆ Supp H'` missing the images of the components of `D` with coefficient `< 1` is the third
piece of the datum.
-/

namespace MMP.FourfoldProofs.Fa18FlippingProcedureDivisorExistsProof

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Points of codimension at most one -/

section Codimension

variable {X : Scheme.{0}}

/-- The generic point of an integral scheme has coheight zero. -/
private theorem coheight_genericPoint_eq_zero [IsIntegral X] :
    Order.coheight (genericPoint X) = 0 :=
  Order.coheight_eq_zero.mpr fun y _ => (genericPoint_spec X).specializes (Set.mem_univ y)

/-- On an integral scheme, a generization of a point of coheight at most one is the point
itself or the generic point. -/
private theorem eq_or_eq_genericPoint_of_specializes [IsIntegral X] {z w : X}
    (hz : Order.coheight z ≤ 1) (h : w ⤳ z) : w = z ∨ w = genericPoint X := by
  by_contra! hne
  have hηw : genericPoint X ⤳ w := (genericPoint_spec X).specializes (Set.mem_univ w)
  have h1 : z < w := lt_of_le_not_ge h fun h' => hne.1 (h.antisymm h').eq
  have h2 : w < genericPoint X := lt_of_le_not_ge hηw fun h' =>
    hne.2 (Specializes.antisymm (show w ⤳ genericPoint X from h') hηw).eq
  have hw : Order.coheight w ≠ 0 := fun h0 => h2.not_isMax (Order.coheight_eq_zero.mp h0)
  have h3 := Order.coheight_strictAnti h1
    (lt_of_le_of_lt ((Order.coheight_anti h1.le).trans hz) ENat.one_lt_top)
  have h4 : (1 : ℕ∞) < Order.coheight z := (ENat.one_le_iff_ne_zero.mpr hw).trans_lt h3
  exact (h4.trans_le hz).false

/-- On an integral scheme, a point of coheight at least one is not the generic point. -/
private theorem ne_genericPoint_of_one_le_coheight [IsIntegral X] {z : X}
    (h : 1 ≤ Order.coheight z) : z ≠ genericPoint X := by
  rintro rfl
  rw [coheight_genericPoint_eq_zero] at h
  exact absurd h (by decide)

/-- If a morphism `g` sends a point `x` of a prime divisor `P` to a point of coheight at most one,
and the image of the generic point of `P` has coheight at least one, then `g(η_P) = g(x)`. -/
private theorem map_genericPoint_eq_of_mem_support {W : Scheme.{0}} [IsIntegral X] (g : W ⟶ X)
    (P : MMP.Mori.PrimeDivisor W) {x : W} (hx : x ∈ P.support)
    (hz : Order.coheight (g x) ≤ 1) (hP : 1 ≤ Order.coheight (g P.genericPoint)) :
    g P.genericPoint = g x :=
  (eq_or_eq_genericPoint_of_specializes hz
    ((MMP.Resolution.Aux.genericPoint_specializes_of_mem_support P hx).map
      g.continuous)).resolve_right
    (ne_genericPoint_of_one_le_coheight hP)

variable [IsLocallyNoetherian X] [IsNormal X]

/-- On a locally Noetherian normal scheme the local ring at a point of coheight one is a discrete
valuation ring. -/
private theorem isDiscreteValuationRing_stalk_of_coheight_eq_one {x : X}
    (hx : Order.coheight x = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have h5 : IsNoetherianRing (X.presheaf.stalk x) ∧ IsLocalRing (X.presheaf.stalk x) ∧
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧
      ringKrullDim (X.presheaf.stalk x) = 1 :=
    ⟨inferInstance, inferInstance, inferInstance, IsNormal.stalk_normal _, by
      rw [ringKrullDim_stalk_eq_coheight, hx]; rfl⟩
  obtain ⟨_, h⟩ := ((_root_.isDiscreteValuationRing_tfae (X.presheaf.stalk x)).out 5 1).mp h5
  exact h

/-- On a locally Noetherian normal scheme the local ring at a point of coheight at most one is
regular. -/
private theorem isRegularLocalRing_stalk_of_coheight_le_one {x : X}
    (hx : Order.coheight x ≤ 1) : IsRegularLocalRing (X.presheaf.stalk x) := by
  rcases hx.eq_or_lt with h | h
  · have := isDiscreteValuationRing_stalk_of_coheight_eq_one h
    infer_instance
  · exact MMP.Flips.isRegularLocalRing_stalk_of_coheight_eq_zero (ENat.lt_one_iff_eq_zero.mp h)

end Codimension

/-- On a locally Noetherian integral scheme, the reduced support of a divisor is regular at every
point lying over a point of coheight at most one. -/
private theorem isRegularLocalRing_stalk_suppScheme {R : Type*} [Zero R] {Z : Scheme.{0}}
    [IsIntegral Z] [IsLocallyNoetherian Z] (B : MMP.Mori.DivisorWithCoeffs R Z) (y : B.suppScheme)
    (hy : Order.coheight (B.suppIdeal.subschemeι y) ≤ 1) :
    IsRegularLocalRing (B.suppScheme.presheaf.stalk y) := by
  set ι := B.suppIdeal.subschemeι
  have hmax : Order.coheight y = 0 := by
    refine Order.coheight_eq_zero.mpr fun y' hy' => ?_
    have hmem : ι y' ∈ (B.supp : Set Z) := by
      rw [← MMP.Mori.DivisorWithCoeffs.coe_support_suppIdeal,
        ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨y', rfl⟩
    rcases eq_or_eq_genericPoint_of_specializes hy
      ((show y' ⤳ y from hy').map ι.continuous) with h | h
    · exact (ι.isClosedEmbedding.injective h).le
    · obtain ⟨E, -, hE⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.mp (h ▸ hmem)
      exact absurd hE (MMP.Threefold.Mori.OpenRestriction.genericPoint_notMem_support E)
  haveI : IsReduced B.suppScheme := by
    change IsReduced (Scheme.IdealSheafData.vanishingIdeal _).subscheme
    infer_instance
  haveI : IsLocallyNoetherian B.suppScheme := LocallyOfFiniteType.isLocallyNoetherian ι
  exact MMP.Flips.isRegularLocalRing_stalk_of_coheight_eq_zero hmax

/-! ### Birational morphisms over points of codimension one -/

section Birational

/-- A separated birational morphism of integral schemes is injective over the points of
coheight one of a locally Noetherian normal target. -/
private theorem eq_of_map_eq_of_coheight_eq_one {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsNormal X] (g : Y ⟶ X) [IsSeparated g]
    (hg : IsBirationalMorphism g) {a b : Y} (hab : g a = g b)
    (hb : Order.coheight (g b) = 1) : a = b := by
  haveI : IsDominant g := hg.isDominant
  have hbij := hg.functionFieldMap_bijective
  haveI := isDiscreteValuationRing_stalk_of_coheight_eq_one hb
  haveI : ValuationRing (X.presheaf.stalk (g a)) := by rw [hab]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing g hbij a
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing g hbij b
  exact (MMP.Positivity.eq_of_isIso_stalkMap g hbij hab).symm

/-- A birational morphism of varieties preserves the dimension. -/
private theorem topologicalKrullDim_eq_of_isBirationalMorphism {k : Type} [Field k]
    {T Y' : Scheme.{0}} {sT : T ⟶ Spec (.of k)} [IsIntegral T] [LocallyOfFiniteType sT]
    {h : Y' ⟶ T} [IsIntegral Y'] [LocallyOfFiniteType (h ≫ sT)] (hh : IsBirationalMorphism h) :
    topologicalKrullDim Y' = topologicalKrullDim T := by
  haveI : IsDominant h := hh.isDominant
  rw [← toENat_trdeg_functionField (sX := h ≫ sT),
    ← trdeg_functionField_eq_of_bijective sT h hh.functionFieldMap_bijective,
    toENat_trdeg_functionField (sX := sT)]

end Birational

/-! ### The resolution -/

/-- A quasi-projective variety over a field of characteristic zero has a resolution
`π : Z' ⟶ Z` by a smooth quasi-projective variety, with `π` projective and birational. -/
private theorem exists_projective_resolution {k : Type} [Field k] [CharZero k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} (hZ : IsQuasiProjectiveVariety k sZ) :
    ∃ (Y : Scheme.{0}) (π : Y ⟶ Z), IsQuasiProjectiveVariety k (π ≫ sZ) ∧ IsProjective π ∧
      IsProjectiveMorphism π ∧ IsBirationalMorphism π ∧ IsSmoothScheme (π ≫ sZ) := by
  obtain ⟨Y, g, hYv, hgp, hgb, hgs, -, -⟩ :=
    MMP.Resolution.exists_isStrongResolution sZ hZ.toIsVariety
  have hqp : IsQuasiProjective (g ≫ sZ) :=
    isQuasiProjective_comp_of_exists_isAmple g sZ ⟨_, inferInstance,
      Stacks.Ample.isAmple_unitModule_of_isAffine _⟩ hgp.isQuasiProjective hZ.isQuasiProjective
  have hYqp : IsQuasiProjectiveVariety k (g ≫ sZ) :=
    (isQuasiProjectiveVariety_iff k _).mpr ⟨hYv, hqp⟩
  haveI := hgp.isProper
  haveI := hZ.toIsVariety
  exact ⟨Y, g, hYqp, hgp,
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety (g ≫ sZ) sZ g rfl, hgb, hgs⟩

/-! ### Birational transforms of prime divisors -/

section Transform

variable {X Y : Scheme.{0}}

private theorem source_ι_comp_eq_of_toRationalMap_eq [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

private theorem apply_hom_eq_of_isInverse [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- The transform of a prime divisor `P` under a morphism `f` has generic point `f(η_P)`. -/
private theorem genericPoint_eq_map_of_transformPrimeDivisor_eq_some [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (f : X ⟶ Y) {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor f.toRationalMap P = some E) :
    E.genericPoint = f P.genericPoint := by
  rw [MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h f.toPartialMap rfl trivial]
  rfl

/-- The transform of `Q` under the inverse of a birational morphism `π` is a prime divisor `P`
with `π(η_P) = η_Q`. -/
private theorem map_genericPoint_of_transformPrimeDivisor_inverse_eq_some [IsReduced X]
    [IsReduced Y] [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] (π : Y ⟶ X)
    (hπ : IsBirationalMorphism π) {Q : MMP.Mori.PrimeDivisor X} {P : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor
      (MMP.Mori.RationalMap.IsBirational.inverse hπ) Q = some P) :
    π P.genericPoint = Q.genericPoint := by
  obtain ⟨e, he, he'⟩ := hπ.isInverse_inverse
  obtain ⟨g', hQ, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp
    (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hQ]
  exact apply_hom_eq_of_isInverse π e he g' (hg'.trans he'.symm) hQ

/-- A prime divisor with nonzero coefficient in the image of `D` under the linear extension of a
partial map `φ` on prime divisors is the image of a component of `D`. -/
private theorem exists_of_mapPrimeDivisors_apply_ne_zero {R : Type*} [AddCommMonoid R]
    {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)} {P : MMP.Mori.PrimeDivisor Y}
    (D : DivisorWithCoeffs R X) (h : DivisorWithCoeffs.mapPrimeDivisors φ D P ≠ 0) :
    ∃ E, D E ≠ 0 ∧ φ E = some P := by
  classical
  by_contra! hne
  apply h
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun E hE => ?_
  rw [DivisorWithCoeffs.mapPrimeDivisors_single]
  rcases hφ : φ E with _ | Q
  · rfl
  · have : Q ≠ P := fun hQ => hne E (Finsupp.mem_support_iff.mp hE) (hφ.trans (congrArg some hQ))
    simp [Finsupp.single_apply, this]

end Transform

/-! ### Weak approximation along finitely many prime divisors -/

section Approximation

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **Approximation with equality at one prime divisor.** Let `S` be a finite set of prime
divisors whose generic points lie in an affine open `W`, and `P₀ ∈ S`. For all integers `n_P`
there is a unit `t` of `K(Y)` with `v_{P₀}(t) = n_{P₀}` and `v_P(t) ≥ n_P` for `P ∈ S`. -/
private theorem exists_unit_ord_eq_and_le {W : Y.Opens} (hW : IsAffineOpen W)
    (S : Finset (MMP.Mori.PrimeDivisor Y)) (hSW : ∀ P ∈ S, P.genericPoint ∈ W)
    {P₀ : MMP.Mori.PrimeDivisor Y} (hP₀ : P₀ ∈ S) (n : MMP.Mori.PrimeDivisor Y → ℤ) :
    ∃ t : (RationalFunctions Y)ˣ, P₀.ord t = n P₀ ∧ ∀ P ∈ S, n P ≤ P.ord t := by
  classical
  have hφ : ∀ P : MMP.Mori.PrimeDivisor Y, ∃ φ : (RationalFunctions Y)ˣ,
      (∀ Q ∈ S, 0 ≤ Q.ord φ) ∧ P₀.ord φ = 0 ∧ (P ∈ S → P ≠ P₀ → 1 ≤ P.ord φ) := by
    intro P
    by_cases hP : P ∈ S ∧ P ≠ P₀
    · obtain ⟨hPS, hPP₀⟩ := hP
      have hcl : IsClosed P.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isClosed_closure
      let V : Y.Opens := W ⊓ ⟨(P.support)ᶜ, hcl.isOpen_compl⟩
      obtain ⟨a, haV, ha⟩ := hW.exists_basicOpen_le (V := V)
        ⟨P₀.genericPoint, hSW P₀ hP₀,
          MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support_of_ne hPP₀.symm⟩ (hSW P₀ hP₀)
      obtain ⟨φ, hφ⟩ := MMP.Fourfold.exists_unit_of_section a ⟨_, ha⟩
      refine ⟨φ, fun Q hQ => (hφ Q (hSW Q hQ)).1, (hφ P₀ (hSW P₀ hP₀)).2.1 ha,
        fun _ _ => (hφ P (hSW P hPS)).2.2 fun h =>
          (haV h).2 (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P)⟩
    · exact ⟨1, fun Q _ => by simp, by simp, fun h1 h2 => absurd ⟨h1, h2⟩ hP⟩
  choose φ hφS hφ₀ hφP using hφ
  obtain ⟨π, hπ⟩ := MMP.Flips.exists_primeDivisor_ord_eq P₀ 1
  let N : ℕ := ∑ P ∈ S, (n P - n P₀ * P.ord π).toNat
  let t : (RationalFunctions Y)ˣ := π ^ n P₀ * ∏ Q ∈ S, φ Q ^ N
  have hord : ∀ P : MMP.Mori.PrimeDivisor Y,
      P.ord t = n P₀ * P.ord π + ∑ Q ∈ S, (N : ℤ) * P.ord (φ Q) := by
    intro P
    rw [MMP.Mori.PrimeDivisor.ord_mul, MMP.Mori.PrimeDivisor.ord_zpow,
      MMP.Fourfold.PrimeDivisor.ord_prod, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [MMP.Mori.PrimeDivisor.ord_pow, nsmul_eq_mul]
  have ht₀ : P₀.ord t = n P₀ := by
    rw [hord, hπ, mul_one, Finset.sum_eq_zero fun Q _ => by rw [hφ₀, mul_zero], add_zero]
  refine ⟨t, ht₀, fun P hP => ?_⟩
  obtain rfl | hPP₀ := eq_or_ne P P₀
  · exact ht₀.ge
  have hsum : (N : ℤ) * P.ord (φ P) ≤ ∑ Q ∈ S, (N : ℤ) * P.ord (φ Q) :=
    Finset.single_le_sum (f := fun Q => (N : ℤ) * P.ord (φ Q))
      (fun Q _ => mul_nonneg (Int.natCast_nonneg N) (hφS Q P hP)) hP
  have hN : n P - n P₀ * P.ord π ≤ (N : ℤ) := by
    have h2 : (n P - n P₀ * P.ord π).toNat ≤ N :=
      Finset.single_le_sum (f := fun P => (n P - n P₀ * P.ord π).toNat)
        (fun _ _ => Nat.zero_le _) hP
    have h3 := Int.self_le_toNat (n P - n P₀ * P.ord π)
    omega
  have h4 : (N : ℤ) ≤ (N : ℤ) * P.ord (φ P) := by
    simpa using mul_le_mul_of_nonneg_left (hφP P hP hPP₀) (Int.natCast_nonneg N)
  rw [hord]
  linarith

/-- The strict triangle inequality for `v_E`: if `v_E(f) = n` and `v_E(g) ≥ n + 1`, then
`v_E(f + g) = n`. -/
private theorem valuation_add_eq_of_ordGE (E : MMP.Mori.PrimeDivisor Y)
    {f g : Y.presheaf.stalk (componentGenericPoint Y E.component)} {n : ℤ}
    (hf : E.valuation f = WithZero.exp n) (hg : E.OrdGE (n + 1) g) :
    E.valuation (f + g) = WithZero.exp n := by
  rcases hg with rfl | hg
  · rw [add_zero, hf]
  have hlt : WithZero.exp n < E.valuation g :=
    lt_of_lt_of_le (WithZero.exp_lt_exp.mpr (lt_add_one n)) hg
  have hfg : f + g ≠ 0 := by
    intro h
    have hg' : g = -f := eq_neg_of_add_eq_zero_right h
    rw [hg', E.valuation_neg, hf] at hlt
    exact lt_irrefl _ hlt
  have h1 := E.valuation_add hfg
  rw [hf, min_eq_left hlt.le] at h1
  refine le_antisymm ?_ h1
  by_contra! hcon'
  have hf' : f = (f + g) + -g := by ring
  have hfne : (f + g) + -g ≠ 0 := by
    rw [← hf']
    intro h0
    rw [h0, map_zero] at hf
    exact WithZero.exp_ne_zero hf.symm
  have h2 := E.valuation_add hfne
  rw [← hf', E.valuation_neg, hf] at h2
  exact absurd h2 (not_le.mpr (lt_min hcon' hlt))

/-- **Weak approximation.** For finitely many prime divisors `P` whose generic points lie in an
affine open and integers `n_P`, there is a unit `t` of `K(Y)` with `v_P(t) = n_P` for every `P`.
-/
private theorem exists_unit_ord_eq {W : Y.Opens} (hW : IsAffineOpen W)
    (S : Finset (MMP.Mori.PrimeDivisor Y)) (hSW : ∀ P ∈ S, P.genericPoint ∈ W)
    (n : MMP.Mori.PrimeDivisor Y → ℤ) :
    ∃ t : (RationalFunctions Y)ˣ, ∀ P ∈ S, P.ord t = n P := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨P₁, hP₁⟩
  · exact ⟨1, by simp⟩
  choose! u hu₀ hu using fun P₀ (hP₀ : P₀ ∈ S) => exists_unit_ord_eq_and_le hW S hSW hP₀
    (fun P => if P = P₀ then n P else n P + 1)
  set s : RationalFunctions Y := ∑ P₀ ∈ S, (u P₀ : RationalFunctions Y) with hs_def
  have hval : ∀ P ∈ S, P.valuation (s P.component) = WithZero.exp (n P) := by
    intro P hP
    have hs : s P.component = (u P : RationalFunctions Y) P.component +
        ∑ P₀ ∈ S.erase P, (u P₀ : RationalFunctions Y) P.component := by
      rw [hs_def, Finset.sum_apply, ← Finset.add_sum_erase S _ hP]
    rw [hs]
    refine valuation_add_eq_of_ordGE P ?_
      (Finset.sum_induction _ (P.OrdGE (n P + 1)) (fun _ _ ha hb => ha.add hb)
        (MMP.Mori.PrimeDivisor.OrdGE.zero _) fun P₀ hP₀ => Or.inr ?_)
    · rw [P.valuation_component, hu₀ P hP, if_pos rfl]
    · rw [P.valuation_component, WithZero.exp_le_exp]
      have := hu P₀ (Finset.mem_of_mem_erase hP₀) P hP
      rwa [if_neg (Finset.ne_of_mem_erase hP₀).symm] at this
  have : Subsingleton (irreducibleComponents Y) := MMP.Fourfold.subsingleton_irreducibleComponents
  have hunit : IsUnit s := by
    rw [Pi.isUnit_iff]
    intro Z
    obtain rfl : Z = P₁.component := Subsingleton.elim _ _
    have hne : s P₁.component ≠ 0 := fun h0 => by
      have := hval P₁ hP₁
      rw [h0, map_zero] at this
      exact WithZero.exp_ne_zero this.symm
    obtain ⟨b, hb⟩ := (MMP.Mori.RationalFunctions.isField_stalk Y P₁.component).mul_inv_cancel hne
    exact IsUnit.of_mul_eq_one b hb
  refine ⟨hunit.unit, fun P hP => ?_⟩
  have := P.valuation_component hunit.unit
  rw [IsUnit.unit_spec, hval P hP] at this
  exact (WithZero.exp_injective this).symm

end Approximation

/-! ### Intersection numbers along normalizations of curves -/

section Normalization

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- Every proper curve has a normalization, of dimension at most one. -/
private theorem exists_curveNormalization (C : ProperCurve sX) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ C.scheme) (_ : IsCurveNormalization ν),
      topologicalKrullDim N ≤ 1 := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  exact ⟨_, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le⟩

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{0}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- An integral scheme proper over `k` is a `k`-variety. -/
private theorem isVariety_of_isProper {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ Spec (.of k))
    [hp : IsProper f] : AlgebraicGeometry.IsVariety k f :=
  { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
    toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{0}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have := isVariety_of_isProper (ν ≫ C.ι ≫ sX)
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme.{0}} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) [IsDominant f]
    [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_comp_eq_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{0}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp_of_isCurveNormalization C hν hdim
  have hc2 := C.isCurve
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- For a presentation `D = ∑ⱼ rⱼ Lⱼ`, the number `∑ⱼ rⱼ deg_C 𝒪_X(Lⱼ)` is a value of `D · C`. -/
private theorem isRIntersectionNumber_sum_degreeOn (D : RDivisor X) {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) (C : ProperCurve sX) :
    IsRIntersectionNumber k sX D r L C (∑ j, r j * (L j).degreeOn k sX C.ι C.dim_le (hL j)) := by
  obtain ⟨N, ν, hν, hdim⟩ := exists_curveNormalization C
  refine ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), hD, fun j => ?_, rfl⟩
  refine ⟨N, ν, hν, hdim, ?_⟩
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := (hL j).isInvertibleModule_divisorialSheaf
  exact (degreeOn_comp_eq_of_isCurveNormalization C hν hdim _).symm

end Normalization

/-! ### Generators of `N¹(Z'/Z)` avoiding finitely many prime divisors -/

section Generators

/-- A spanning family of a finite-dimensional real vector space has a finite spanning
subfamily. -/
private theorem exists_fin_span_range_eq_top {ι V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (v : ι → V) (h : Submodule.span ℝ (Set.range v) = ⊤) :
    ∃ (n : ℕ) (g : Fin n → ι), Submodule.span ℝ (Set.range (v ∘ g)) = ⊤ := by
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℝ v
  haveI : Finite κ := hli.finite
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  refine ⟨n, a ∘ e.symm, ?_⟩
  rw [← h, ← hspan]
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨e j, by simp⟩

variable {k : Type} [Field k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y]

/-- If `𝒪_Y(D) ≅ 𝒪_Y(E)` for a Cartier divisor `E`, then `(C · E) = deg_C 𝒪_Y(D)` on every proper
curve `C`. -/
private theorem intersectionNumber_ofCartier_eq_degreeOn {E : Y.CartierDivisor} {D : Divisor Y}
    (hD : D.IsCartier) (e : D.divisorialSheaf ≅ MMP.CartierDivisor.sheaf E)
    (C : ProperCurve sY) :
    (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) =
      (D.degreeOn k sY C.ι C.dim_le hD : ℝ) := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := hD.isInvertibleModule_divisorialSheaf
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  exact_mod_cast (degreeOn_eq_of_iso k sY C.ι C.dim_le e).symm

/-- Every Cartier divisor `D` has the degrees of a Cartier divisor `E ∈ Div(Y)` on the proper
curves of `Y`. -/
private theorem exists_cartierDivisor_intersectionNumber_eq (D : Divisor Y) (hD : D.IsCartier) :
    ∃ E : Y.CartierDivisor, ∀ C : ProperCurve sY,
      (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) =
        (D.degreeOn k sY C.ι C.dim_le hD : ℝ) := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  exact ⟨E, intersectionNumber_ofCartier_eq_degreeOn hD e⟩

/-- Every divisor `M` is linearly equivalent to a divisor with coefficient zero along finitely many
prime divisors whose generic points lie in an affine open. -/
private theorem exists_linearlyEquivalent_coeff_eq_zero [CompactSpace Y] {W : Y.Opens}
    (hW : IsAffineOpen W) (S : Finset (MMP.Mori.PrimeDivisor Y))
    (hSW : ∀ P ∈ S, P.genericPoint ∈ W) (M : Divisor Y) :
    ∃ M' : Divisor Y, M'.LinearlyEquivalent M ∧ ∀ P ∈ S, M'.coeff P = 0 := by
  obtain ⟨t, ht⟩ := exists_unit_ord_eq hW S hSW (fun P => -M.coeff P)
  refine ⟨M + principalDivisor t, ⟨t, add_sub_cancel_left _ _⟩, fun P hP => ?_⟩
  rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor, ht P hP, add_neg_cancel]

/-- Linearly equivalent Cartier divisors have the same degree on every proper curve. -/
private theorem degreeOn_eq_of_linearlyEquivalent [CompactSpace Y] {C : Scheme.{0}} (i : C ⟶ Y)
    [IsProper (i ≫ sY)] (hdim : topologicalKrullDim C ≤ 1) {D D' : Divisor Y}
    (hD : D.IsCartier) (hD' : D'.IsCartier) (h : D.LinearlyEquivalent D') :
    D.degreeOn k sY i hdim hD = D'.degreeOn k sY i hdim hD' := by
  obtain ⟨φ, hφ⟩ := h
  have h0 : (D - D').LinearlyEquivalent 0 := ⟨φ, by rw [sub_zero, hφ]⟩
  have hc : (D - D').IsCartier := hD.sub hD'
  have h1 := Divisor.degreeOn_eq_zero_of_linearlyEquivalent sY i hdim hc h0
  have h2 := Divisor.degreeOn_add k sY i hdim (D - D') D' hc hD'
  rwa [Divisor.degreeOn_congr (sub_add_cancel D D') (hc.add hD') hD, h1, zero_add] at h2

/-- The degree of a difference is the difference of the degrees:
`deg_C (A - B) = deg_C A - deg_C B`. -/
private theorem degreeOn_sub {C : Scheme.{0}} (i : C ⟶ Y) [IsProper (i ≫ sY)]
    (hdim : topologicalKrullDim C ≤ 1) {A B : Divisor Y} (hA : A.IsCartier) (hB : B.IsCartier) :
    (A - B).degreeOn k sY i hdim (hA.sub hB) =
      A.degreeOn k sY i hdim hA - B.degreeOn k sY i hdim hB := by
  have h := Divisor.degreeOn_add k sY i hdim (A - B) B (hA.sub hB) hB
  rw [Divisor.degreeOn_congr (sub_add_cancel A B) ((hA.sub hB).add hB) hA] at h
  omega

end Generators

/-- On a smooth quasi-projective variety `Y` projective over `Z`, there are finitely many
effective Cartier divisors whose classes span `N¹(Y/Z)` and none of whose components lies in a
given finite set of prime divisors. -/
private theorem exists_generators {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)} (hZ : IsQuasiProjectiveVariety k sZ)
    (π : Y ⟶ Z) (hY : IsQuasiProjectiveVariety k (π ≫ sZ)) (hπ : IsProjective π)
    (hYs : IsSmoothScheme (π ≫ sZ)) [IsLocallyNoetherian Y] [IsNormal Y]
    [QuasiCompact (π ≫ sZ)] (S : Set (MMP.Mori.PrimeDivisor Y)) (hS : S.Finite) :
    ∃ (r : ℕ) (F : Fin r → Divisor Y), (∀ j, (F j).IsCartier) ∧
      (∀ j, DivisorWithCoeffs.IsEffective (F j)) ∧
      (∀ L : RDivisor Y, IsCartierCombination L → ∃ c : Fin r → ℝ,
        IsNumericallyEquivalentOver k (π ≫ sZ) π L (∑ j, c j • Divisor.toRDivisor (F j))) ∧
      ∀ j P, (F j).coeff P ≠ 0 → P ∉ S := by
  classical
  set sY := π ≫ sZ
  haveI := hY.toIsVariety
  haveI : IsIntegral Y := hY.toIsVariety.toIsIntegral
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := hY
  haveI := hZ
  have hcart : ∀ D : Divisor Y, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hYs
  -- a finite family of Cartier divisors spanning `N¹(Y/Z)`
  obtain ⟨hfd, hspanN⟩ :=
    MMP.Fourfold.RelativeNumericalDivisorClasses.finiteDimensional_and_span_ofCartier_eq_top
      sY sZ π hπ rfl
  obtain ⟨n, G, hG⟩ := exists_fin_span_range_eq_top _ hspanN
  -- Weil divisors with the sheaves of the `G i`
  have hM : ∀ i, ∃ M : Divisor Y,
      Nonempty (M.divisorialSheaf ≅ MMP.CartierDivisor.sheaf (G i)) :=
    fun i => exists_divisorialSheaf_iso_of_isInvertible _
  choose M hMe using hM
  -- moving them off `S`
  obtain ⟨W, hW, hSW⟩ := MMP.Resolution.exists_isAffineOpen_finite_subset sY
    hY.isQuasiProjective (hS.image fun P => P.genericPoint)
  have hmove : ∀ i, ∃ M' : Divisor Y, M'.LinearlyEquivalent (M i) ∧
      ∀ P ∈ hS.toFinset, M'.coeff P = 0 := fun i =>
    exists_linearlyEquivalent_coeff_eq_zero hW hS.toFinset
      (fun P hP => hSW ⟨P, hS.mem_toFinset.mp hP, rfl⟩) (M i)
  choose M' hM'le hM'0 using hmove
  -- positive and negative parts
  let A : Fin n → Divisor Y := fun i => (M' i).mapRange (fun a => max a 0) (by simp)
  let B : Fin n → Divisor Y := fun i => (M' i).mapRange (fun a => max (-a) 0) (by simp)
  have hAB : ∀ i, M' i = A i - B i := fun i => by
    refine Finsupp.ext fun P => ?_
    simp only [A, B, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply]
    omega
  -- degrees along curves
  have hdeg : ∀ (C : ProperCurve sY) i,
      (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ (G i)) =
        ((A i).degreeOn k sY C.ι C.dim_le (hcart _) : ℝ) -
          ((B i).degreeOn k sY C.ι C.dim_le (hcart _) : ℝ) := by
    intro C i
    rw [intersectionNumber_ofCartier_eq_degreeOn (hcart (M i)) (hMe i).some C,
      ← degreeOn_eq_of_linearlyEquivalent C.ι C.dim_le (hcart _) (hcart _) (hM'le i),
      Divisor.degreeOn_congr (hAB i) (hcart _) ((hcart _).sub (hcart _)),
      degreeOn_sub C.ι C.dim_le (hcart _) (hcart _)]
    push_cast
    ring
  refine ⟨n + n, Fin.append A B, fun j => hcart _, ?_, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      intro P
      simp [A, DivisorWithCoeffs.coeff]
    · rw [Fin.append_right]
      intro P
      simp [B, DivisorWithCoeffs.coeff]
  · intro L ⟨m, r, L', hL'c, hL⟩
    choose E hE using fun a => exists_cartierDivisor_intersectionNumber_eq (sY := sY) (L' a)
      (hL'c a)
    set cls := MMP.Fourfold.relativeNumericalDivisorClass sY π
    set δ : KCartierDivisor ℝ Y := ∑ a, r a • KCartierDivisor.ofCartier ℝ (E a) with hδ
    have hmem : cls δ ∈ Submodule.span ℝ
        (Set.range ((fun E : Y.CartierDivisor => cls (KCartierDivisor.ofCartier ℝ E)) ∘ G)) :=
      hG ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    have hker : ∀ C : ProperCurve sY, C.IsContractedBy π →
        ∑ i, c i * (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ (G i)) =
          ∑ a, r a * (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ (E a)) := by
      intro C hC
      have h1 : cls (∑ i, c i • KCartierDivisor.ofCartier ℝ (G i)) = cls δ := by
        rw [map_sum]
        simp_rw [map_smul]
        exact hc
      simpa [MMP.Fourfold.relativeDegreeMap, OneCycle.intersectionNumber, hδ, map_sum, map_smul,
        LinearMap.sum_apply, LinearMap.smul_apply, sub_eq_zero] using
        congrFun (LinearMap.mem_ker.mp ((Submodule.Quotient.eq _).mp h1)) ⟨C, hC⟩
    refine ⟨Fin.append c (-c), ⟨m, r, L', hL'c, hL⟩,
      ⟨n + n, Fin.append c (-c), Fin.append A B, fun j => hcart _, ?_⟩, ?_⟩
    · simp_rw [toRDivisor_eq_mapCoeffs]
    intro C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂
    have hLc : L = ∑ a, r a • Divisor.toRDivisor (L' a) := by
      rw [hL]
      simp_rw [toRDivisor_eq_mapCoeffs]
    have e₁ := (IsRIntersectionNumber.eq_and_linear k sY C).1 L r₁ L₁ r L' x₁ _ h₁
      (isRIntersectionNumber_sum_degreeOn L r L' hL'c hLc C)
    have e₂ := (IsRIntersectionNumber.eq_and_linear k sY C).1 _ r₂ L₂ (Fin.append c (-c))
      (Fin.append A B) x₂ _ h₂
      (isRIntersectionNumber_sum_degreeOn _ (Fin.append c (-c)) (Fin.append A B)
        (fun j => hcart _) rfl C)
    rw [e₁, e₂, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.neg_apply]
    have := hker C hC
    simp_rw [hdeg C, hE _ C] at this
    rw [← this]
    simp only [mul_sub, Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib]
    ring
  · intro j P hP hPS
    have h0 : ∀ i, (M' i) P = 0 := fun i => hM'0 i P (hS.mem_toFinset.mpr hPS)
    revert hP
    refine Fin.addCases (motive := fun j => (Fin.append A B j).coeff P ≠ 0 → False)
      (fun i hP => ?_) (fun i hP => ?_) j
    · rw [Fin.append_left] at hP
      apply hP
      simp [A, DivisorWithCoeffs.coeff, h0 i]
    · rw [Fin.append_right] at hP
      apply hP
      simp [B, DivisorWithCoeffs.coeff, h0 i]

/-- Let `X` be a normal variety over an algebraically closed field `k` of characteristic zero, `D`
a boundary on `X` and `f : X ⟶ Z` a small projective morphism to a quasi-projective variety `Z`.
Then a procedure datum for `(X, D, f)` exists. -/
theorem nonempty_procedureDatum {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsLocallyNoetherian Z] [IsNormal Z] {D : RDivisor X} {f : X ⟶ Z}
    (hX : IsNormalVariety k sX) (hD : IsBoundary D) (hf : IsSmall k sZ sX f)
    (_hfp : IsProjectiveMorphism f) (hZ : IsQuasiProjectiveVariety k sZ) :
    Nonempty (ProcedureDatum k sZ D f) := by
  classical
  -- instances on `X` and `Z`
  haveI : IsIntegral X := hX.1.toIsIntegral
  haveI := hX.1
  haveI : IsNormal X := hX.2
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI := hZ.toIsVariety
  haveI : IsIntegral Z := hZ.toIsVariety.toIsIntegral
  haveI : IsProper f := hf.isProper
  have hfb : IsBirationalMorphism f := hf.surjective_and_isBirational.2
  have hsepZ : IsSeparated (Z ↘ ⊤_ Scheme) := by
    rw [show (Z ↘ ⊤_ Scheme) = sZ ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  -- the resolution
  obtain ⟨Y, π, hYqp, hπp, hπP, hπb, hYs⟩ := exists_projective_resolution hZ
  obtain ⟨hYln, hYn⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs
  haveI := hYqp.toIsVariety
  haveI : IsIntegral Y := hYqp.toIsVariety.toIsIntegral
  haveI : IsProper π := hπp.isProper
  have hsepY : IsSeparated (Y ↘ ⊤_ Scheme) := by
    rw [show (Y ↘ ⊤_ Scheme) = (π ≫ sZ) ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  -- coheights along `f` and `π`
  have hEx : ∀ x ∈ MMP.Flips.exceptionalSet f, 2 ≤ Order.coheight x :=
    (le_closedsCodimension_iff_le_coheight (C := MMP.Flips.exceptionalCloseds f)).mp
      ((isSmall_iff_two_le_closedsCodimension_exceptionalSet hf.toIsBirationalContraction).mp hf)
  have hcohf : ∀ x : X, Order.coheight x ≤ Order.coheight (f x) :=
    coheight_le_coheight_map sZ sX hf.isVariety_target hf.isVariety_source f hf.comp_eq hf.dim_eq
  have hcohπ : ∀ y : Y, Order.coheight y ≤ Order.coheight (π y) :=
    coheight_le_coheight_map sZ (π ≫ sZ) hZ.toIsVariety hYqp.toIsVariety π rfl
      (topologicalKrullDim_eq_of_isBirationalMorphism (sT := sZ) hπb)
  have hfQ : ∀ Q : MMP.Mori.PrimeDivisor X, Order.coheight (f Q.genericPoint) = 1 := by
    intro Q
    have hQ : Q.genericPoint ∉ MMP.Flips.exceptionalSet f := fun h => by
      have := hEx _ h
      rw [Q.coheight_genericPoint] at this
      exact absurd this (by decide)
    rw [coheight_map_of_notMem_exceptionalSet hQ, Q.coheight_genericPoint]
  have hfinj : ∀ Q Q' : MMP.Mori.PrimeDivisor X, f Q.genericPoint = f Q'.genericPoint → Q = Q' :=
    fun Q Q' h => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_map_eq_of_coheight_eq_one f hfb h (hfQ Q'))
  -- the strict transforms of the components of `f_*D`
  set SY : Set (MMP.Mori.PrimeDivisor Y) :=
    {P | ∃ Q : MMP.Mori.PrimeDivisor X, D Q ≠ 0 ∧ π P.genericPoint = f Q.genericPoint}
  have hSY : SY.Finite := by
    refine (D.support.finite_toSet.biUnion fun Q _ =>
      (show ({P : MMP.Mori.PrimeDivisor Y | π P.genericPoint = f Q.genericPoint}).Finite from
        Set.Subsingleton.finite fun P hP P' hP' =>
          AlgebraicGeometry.PrimeDivisor.genericPoint_injective
            (eq_of_map_eq_of_coheight_eq_one π hπb (hP.trans hP'.symm)
              (by rw [show π P'.genericPoint = f Q.genericPoint from hP']; exact hfQ Q)))).subset ?_
    rintro P ⟨Q, hQ, hPQ⟩
    exact Set.mem_biUnion (Finsupp.mem_support_iff.mpr hQ) hPQ
  obtain ⟨r, F, hFc, hFe, hspan, hFS⟩ :=
    exists_generators hZ π hYqp hπp hYs SY hSY
  -- the closed set `T₀`
  set B := divisorPushforward f D
  set ι := B.suppIdeal.subschemeι
  set A₁ : Set Z := f '' MMP.Flips.exceptionalSet f
  set A₂ : Set Z := (regularLocus Z)ᶜ
  set A₃ : Set Z := ι '' (regularLocus B.suppScheme)ᶜ
  set A₄ : Set Z := ⋃ j, ⋃ P ∈ (F j).support, π '' P.support
  set A₅ : Set Z := f '' (reducedPart D).supp
  set T₀ : Set Z := A₁ ∪ A₂ ∪ A₃ ∪ A₄ ∪ A₅
  have hA₁c : IsClosed A₁ := f.isClosedMap _ (isClosed_exceptionalSet f)
  have hA₂c : IsClosed A₂ := (isOpen_regularLocus_of_locallyOfFiniteType sZ).isClosed_compl
  have hA₃c : IsClosed A₃ := by
    exact ι.isClosedEmbedding.isClosedMap _
      (isOpen_regularLocus_of_locallyOfFiniteType (ι ≫ sZ)).isClosed_compl
  have hA₄c : IsClosed A₄ :=
    isClosed_iUnion_of_finite fun j => (F j).support.finite_toSet.isClosed_biUnion fun P _ =>
      π.isClosedMap _ P.idealSheaf.support.isClosed
  have hA₅c : IsClosed A₅ := f.isClosedMap _ (reducedPart D).isClosed_supp
  have hT₀c : IsClosed T₀ := (((hA₁c.union hA₂c).union hA₃c).union hA₄c).union hA₅c
  -- a point of coheight at most one in `T₀` is the image of a component of some `F j` or of `⌊D⌋`
  have hT₀mem : ∀ z ∈ T₀, Order.coheight z ≤ 1 →
      (∃ j, ∃ P ∈ (F j).support, π P.genericPoint = z) ∨
        ∃ Q : MMP.Mori.PrimeDivisor X, (reducedPart D).coeff Q ≠ 0 ∧ f Q.genericPoint = z := by
    rintro z ((((⟨x, hx, rfl⟩ | h) | ⟨y, hy, rfl⟩) | h) | ⟨x, hx, rfl⟩) hz
    · exact absurd (((hEx x hx).trans (hcohf x)).trans hz) (by decide)
    · exact absurd (isRegularLocalRing_stalk_of_coheight_le_one hz) h
    · exact absurd (isRegularLocalRing_stalk_suppScheme B y hz) hy
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
      obtain ⟨P, hP, x, hx, rfl⟩ := Set.mem_iUnion₂.mp hj
      exact Or.inl ⟨j, P, hP, map_genericPoint_eq_of_mem_support π P hx hz
        (P.coheight_genericPoint.ge.trans (hcohπ _))⟩
    · obtain ⟨Q, hQ, hxQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
      exact Or.inr ⟨Q, hQ, map_genericPoint_eq_of_mem_support f Q hxQ hz (hfQ Q).ge⟩
  have hT₀ne : T₀ ≠ Set.univ := fun h => by
    rcases hT₀mem _ (h ▸ Set.mem_univ (genericPoint Z))
        (by rw [coheight_genericPoint_eq_zero]; exact zero_le_one) with
      ⟨j, P, -, hP⟩ | ⟨Q, -, hQ⟩
    · exact ne_genericPoint_of_one_le_coheight (P.coheight_genericPoint.ge.trans (hcohπ _)) hP
    · exact ne_genericPoint_of_one_le_coheight (hfQ Q).ge hQ
  -- the images of the components of `D` with coefficient `< 1`
  set S : Set Z := (fun Q : MMP.Mori.PrimeDivisor X => f Q.genericPoint) ''
    {Q | D Q ≠ 0 ∧ D Q < 1}
  have hSfin : S.Finite :=
    (D.support.finite_toSet.subset fun Q hQ => Finsupp.mem_support_iff.mpr hQ.1).image _
  have hST : Disjoint S T₀ := by
    rw [Set.disjoint_left]
    rintro _ ⟨Q, ⟨hQ0, hQ1⟩, rfl⟩ h
    rcases hT₀mem _ h (hfQ Q).le with ⟨j, P, hP, hPQ⟩ | ⟨Q₁, hQ₁, hQ₁Q⟩
    · exact hFS j P (Finsupp.mem_support_iff.mp hP) ⟨Q, hQ0, hPQ⟩
    · obtain rfl := hfinj Q₁ Q hQ₁Q
      apply hQ₁
      rw [DivisorWithCoeffs.coeff_roundDown, Int.floor_eq_zero_iff]
      exact ⟨(hD Q₁).1, hQ1⟩
  -- the divisor `H'`
  obtain ⟨H', hH'c, hH'r, hTH', hSH', -, -⟩ :=
    MMP.Mori.exists_isCartier_reduced_supp_superset sZ T₀ hT₀c hT₀ne S hSfin hST
  refine ⟨{
    resolution := Y
    π := π
    isLocallyNoetherian_resolution := hYln
    isNormal_resolution := hYn
    quasiCompact_resolution := inferInstance
    isVariety_resolution := hYqp.toIsVariety
    isSmoothScheme_resolution := hYs
    isProjectiveMorphism := hπP
    isBirationalMorphism := hπb
    r := r
    F := F
    isCartier_F := hFc
    isEffective_F := hFe
    span_F := hspan
    not_strictTransform := ?_
    H' := H'
    isCartier_H' := hH'c
    isReduced_H' := hH'r
    image_exceptionalSet_subset := fun z hz => hTH' (Or.inl (Or.inl (Or.inl (Or.inl hz))))
    nonregular_subset := fun z hz => hTH' (Or.inl (Or.inl (Or.inl (Or.inr hz))))
    nonregular_supp_subset := ?_
    image_component_subset := fun j P hP z hz =>
      hTH' (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion₂.mpr
        ⟨P, Finsupp.mem_support_iff.mpr hP, hz⟩⟩)))
    image_roundDown_subset := fun z hz => hTH' (Or.inr hz)
    image_ne_component := ?_ }⟩
  · intro j P hP Q hQ h
    obtain ⟨Q₀, hQ₀, hQ₀Q⟩ := exists_of_mapPrimeDivisors_apply_ne_zero D hQ
    exact hFS j P hP ⟨Q₀, hQ₀, (map_genericPoint_of_transformPrimeDivisor_inverse_eq_some π hπb
      h).trans (genericPoint_eq_map_of_transformPrimeDivisor_eq_some f hQ₀Q)⟩
  · intro z hz hnr
    obtain ⟨y, rfl⟩ : z ∈ Set.range ι := by
      rw [Scheme.IdealSheafData.range_subschemeι, DivisorWithCoeffs.coe_support_suppIdeal]
      exact hz
    refine hTH' (Or.inl (Or.inl (Or.inr ⟨y, fun hy => hnr ?_, rfl⟩)))
    haveI : IsRegularLocalRing (B.suppScheme.presheaf.stalk y) := hy
    exact IsRegularLocalRing.of_ringEquiv
      (MMP.Flips.ResolutionInputs.stalkQuotientEquiv B.suppIdeal y).symm
  · intro P hP Q hQ0 hQ1 heq
    have hmem : f Q.genericPoint ∈ P.support :=
      heq ▸ ⟨_, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' Q, rfl⟩
    exact Set.disjoint_left.mp hSH' ⟨Q, ⟨hQ0, hQ1⟩, rfl⟩
      (DivisorWithCoeffs.support_subset_supp hP hmem)

end MMP.FourfoldProofs.Fa18FlippingProcedureDivisorExistsProof

end

section

/-!
# Existence of a procedure datum for the log flipping procedure

Let `k` be an algebraically closed field of characteristic zero, `X` a normal `k`-variety, `D` a
boundary on `X` (not assumed `ℝ`-Cartier) and `f : X ⟶ Z` a small projective contraction onto a
quasi-projective variety `Z`. Then a procedure datum `(π, (F_j), H')` for `(X, D, f)` exists:
a projective resolution `π : Z' ⟶ Z`, effective Cartier divisors `F_j` on `Z'` spanning
`N¹(Z'/Z)` and avoiding the strict transforms of the components of `f_*D`, and a reduced
effective Cartier divisor `H'` on `Z` whose support contains `f(Ex(f))`, the singular loci of `Z`
and of `Supp f_*D`, the images of the components of the `F_j` and `f(⌊D⌋)`, and none of whose
components is the image of a component of `D` with coefficient `< 1`.

## Main results

* `MMP.Flips.ProcedureDatum.nonempty`

## Implementation notes

The ground field of the source is `ℂ`; here it is any algebraically closed field of
characteristic zero, which is what resolution of singularities and the Bertini argument
producing `H'` need.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 18.12.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori

/-- **Existence of a procedure datum** (FA 18.12.1). Let `k` be algebraically closed of
characteristic zero, `X` a normal `k`-variety, `D` a boundary on `X` and `f : X ⟶ Z` a small
projective contraction onto a quasi-projective `k`-variety `Z`. Then there is a procedure datum
`MMP.Flips.ProcedureDatum k sZ D f` for `(X, D, f)`. -/
@[mmp "lem_fa18_flipping_procedure_divisor_exists"]
public theorem ProcedureDatum.nonempty {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsLocallyNoetherian Z] [IsNormal Z] {D : RDivisor X} {f : X ⟶ Z}
    (hX : IsNormalVariety k sX) (hD : IsBoundary D) (hf : IsSmall k sZ sX f)
    (hfp : IsProjectiveMorphism f) (hZ : IsQuasiProjectiveVariety k sZ) :
    Nonempty (ProcedureDatum k sZ D f) :=
  MMP.FourfoldProofs.Fa18FlippingProcedureDivisorExistsProof.nonempty_procedureDatum hX hD hf hfp hZ

end MMP.Flips

end
