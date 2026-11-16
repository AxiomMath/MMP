module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.ProjectiveSpace.LinearProjection
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Positivity.AmpleTwistRealPerturbation
import MMP.AlgebraicGeometry.Intersection.Nef
import MMP.AlgebraicGeometry.Intersection.OneCycles
import MMP.AlgebraicGeometry.Singularities.Slc.NodeResidueForm
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Morphisms.Smooth.IrreducibleComponents
import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Threefold.Basic
import MMP.AlgebraicGeometry.Positivity.NakaiMoishezonKleiman
import MMP.AlgebraicGeometry.Morphisms.Birational.IsoInCodimOne
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Intersection.Surface.Basic
import MMP.AlgebraicGeometry.Intersection.Surface.NefTrivialCurves
import MMP.AlgebraicGeometry.Normalization.IntegralScheme

/-!
# A trivially connected prime divisor of a threefold is numerically trivial along itself

Let `X` be a normal projective threefold over `ℂ` with canonical divisor `K_X`, `Δ_X` a
`ℚ`-divisor with `L = K_X + Δ_X` nef (in particular `ℚ`-Cartier), and `D` an `L`-trivially
connected prime divisor. Then `L · Γ = 0` for every irreducible curve `Γ ⊆ D`.

Suppose `L · Γ₀ > 0` for some curve `Γ₀ ⊆ D`. Resolve the normalization of `D` by a smooth
projective surface `μ : S ⟶ D`, and let `N` be a Cartier divisor on `S` with
`𝒪_S(N) ≅ μ^* 𝒪_X(rL)`. By the projection formula, `N · Γ' = 0` when `μ(Γ')` is a point, and
`N · Γ' = d · (L · μ(Γ'))` with `d > 0` otherwise. So `N` is nef and not numerically trivial,
and a curve `Γ ⊆ D` is `L`-trivial exactly when the curves of `S` dominating it are `N`-trivial.
The `N`-trivial curves of `S` that are numerically equivalent to a positive multiple of `N` are
disjoint from every other `N`-trivial curve. The remaining `N`-trivial curves have pairwise
distinct numerical classes, so there are countably many of them. Consequently only countably many
trivial curves pass through a point of `D`, and only countably many meet a given trivial curve.
Since `D` is trivially connected, the closed points of `D` then lie on the countably many trivial
curves reachable from one closed point. This contradicts the fact that a projective surface over
the uncountable field `ℂ` is not covered, along its closed points, by countably many curves.

## Main results

* `MMP.Flips.intersectionNumber_eq_zero_of_isTriviallyConnected`

## Implementation notes

The prime divisor `D` is the divisor `Finsupp.single E 1` of a prime divisor `E`; trivial
connectedness is `MMP.Flips.IsTriviallyConnected`, which carries the normality and properness
of `X`, the canonicity of `K_X`, the effectivity of `D` and the `ℚ`-Cartierness of `L`. Nefness
is `MMP.Mori.QDivisor.IsNef`, whose first component is the `ℚ`-Cartierness used to form the
intersection numbers. An irreducible curve `Γ ⊆ X` is a `MMP.Mori.ProperCurve` (every curve of
the proper variety `X` is proper), and `Γ ⊆ D` is the inclusion of its closure in `Supp D`.

The curves of `S` are its prime divisors, and the pairing of `ℚ`-divisors on `S` is the bilinear
extension of `MMP.Mori.Divisor.intersectionNumberOn`, as in
`MMP.Mori.exists_forall_isCartier_and_intersectionNumberOn_of_smooth`. The surface `S` is a
resolution (`MMP.Mori.exists_smooth_isProper_isBirationalMorphism_of_isNormalVariety`) of the
normalization (`MMP.Threefold.normalization_spec`) of the reduced closed subscheme on `D`. It is
projective by `MMP.isProjectiveMorphism_of_smooth_of_isProper_of_topologicalKrullDim_eq_two`.
Dimensions of closures of points are heights in the specialization order. The final
contradiction is `MMP.exists_isClosed_singleton_notMem_iUnion_of_topologicalKrullDim_le_one`,
applied to `D` embedded in projective space.

## References

* [KollarFlips] J. Kollár et al., *Flips and abundance for algebraic threefolds*, Chapter 15
  (15.9).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.Flips

section Helpers

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

/-! ### Prime divisors of a surface as proper curves -/

section Curves

open Order

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- The dimension of the reduced closed subscheme on `{x}⁻` is the height of `x`. -/
private theorem topologicalKrullDim_curveSubschemeAt (x : X) :
    topologicalKrullDim (curveSubschemeAt x) = (height x : WithBot ℕ∞) := by
  have h := MMP.Intersection.subvarietyDim_eq_height (MMP.Intersection.associatedSubvariety x)
  rwa [MMP.Intersection.genericPoint_associatedSubvariety] at h

/-- The generic point of a proper curve has height one. -/
private theorem height_point_eq_one (C : ProperCurve sX) : height C.point = 1 := by
  have h := C.dim_eq
  rw [topologicalKrullDim_curveSubschemeAt] at h
  exact_mod_cast h

/-- On an integral `k`-scheme of dimension `n`, locally of finite type,
`height x + coheight x = n`. -/
private theorem height_add_coheight_of_dim_eq [IsIntegral X] [LocallyOfFiniteType sX]
    {n : ℕ}
    (hdim : topologicalKrullDim X = n) (x : X) : height x + coheight x = n := by
  let : X.Over (Spec (.of k)) := ⟨sX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := ‹LocallyOfFiniteType sX›
  have hpure : MMP.Intersection.IsPureDimensional X n := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [(Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq, hdim]
  exact MMP.Intersection.height_add_coheight_eq_of_isPureDimensional k hpure x

/-- The closed subscheme `{x}⁻` is integral. -/
private theorem isIntegral_curveSubschemeAt (x : X) : IsIntegral (curveSubschemeAt x) :=
  StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
    isIrreducible_singleton.closure

/-- The generic point of a prime divisor of a proper surface is the generic point of a proper
curve. -/
private theorem isProperCurve_genericPoint [IsProper sX] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hdim : topologicalKrullDim X = 2)
    (P : MMP.Mori.PrimeDivisor X) : IsProperCurve sX P.genericPoint := by
  refine isProperCurve_of_isProper sX ?_
  rw [topologicalKrullDim_curveSubschemeAt]
  have h :=
    height_add_coheight_of_dim_eq sX (n := 2) (by rw [hdim]; rfl) P.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P] at h
  have h1 : height P.genericPoint = 1 :=
    WithTop.add_right_cancel ENat.one_ne_top (h.trans one_add_one_eq_two.symm)
  rw [h1]
  rfl

/-- The proper curve of a prime divisor of a proper surface. -/
private noncomputable def primeCurve [IsProper sX] [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (hdim : topologicalKrullDim X = 2) (P : MMP.Mori.PrimeDivisor X) :
    ProperCurve sX :=
  ⟨P.genericPoint, isProperCurve_genericPoint sX hdim P⟩

variable [IsProper sX] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  (hsm : IsSmoothScheme sX) (hdim : topologicalKrullDim X = 2)

include hsm in
/-- **Cutting down by a curve.** On a smooth proper surface the intersection number of two prime
divisors `P, P'` is the degree of `𝒪_X(P)` along the proper curve of `P'`. -/
private theorem intersectionNumberOn_eq_degreeOn (P P' : MMP.Mori.PrimeDivisor X)
    (hc : ∀ j, Divisor.IsCartier (![Finsupp.single P 1, Finsupp.single P' 1] j : Divisor X)) :
    Divisor.intersectionNumberOn k sX (𝟙 X) 2 hdim.le
        ![Finsupp.single P 1, Finsupp.single P' 1] hc =
      Divisor.degreeOn k sX (primeCurve sX hdim P').ι (primeCurve sX hdim P').dim_le
        (Finsupp.single P 1) (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  set C := primeCurve sX hdim P'
  have hP := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm (Finsupp.single P 1)
  have hP' := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm (Finsupp.single P' 1)
  have := hP.isInvertibleModule_divisorialSheaf
  have := hP'.isInvertibleModule_divisorialSheaf
  have := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P'
  obtain ⟨e⟩ := MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' P'
    inferInstance hP'
  have hd : topologicalKrullDim X ≤ ((1 + 1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  have hinv : ∀ j : Fin 2, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (![Divisor.divisorialSheaf (Finsupp.single P' 1 : Divisor X),
        Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor X)] j) := by
    intro j
    fin_cases j <;> assumption
  have h1 : Divisor.intersectionNumberOn k sX (𝟙 X) 2 hdim.le
        ![Finsupp.single P 1, Finsupp.single P' 1] hc =
      AlgebraicGeometry.intersectionNumber k sX (𝟙 X) 2 hd
        ![Divisor.divisorialSheaf (Finsupp.single P' 1 : Divisor X),
          Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor X)] := by
    have hinv' : ∀ j : Fin 2, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (Divisor.divisorialSheaf (![Finsupp.single P 1, Finsupp.single P' 1] j : Divisor X)) :=
      fun j => (hc j).isInvertibleModule_divisorialSheaf
    rw [Divisor.intersectionNumberOn, Snapper.sheafIntersectionNumber_eq_intersectionNumber,
      ← AlgebraicGeometry.intersectionNumber_comp_perm k sX (𝟙 X) 2 hd
        ![Divisor.divisorialSheaf (Finsupp.single P' 1 : Divisor X),
          Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor X)] (Equiv.swap 0 1)]
    exact AlgebraicGeometry.intersectionNumber_congr_family k sX (𝟙 X) 2 _
      (funext fun j => by fin_cases j <;> rfl)
  rw [h1]
  have hL : (Scheme.Modules.pullback (𝟙 X)).obj
      (![Divisor.divisorialSheaf (Finsupp.single P' 1 : Divisor X),
        Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor X)] 0) ≅
      (Stacks.Divisors.invertibleSheaf P'.idealSheaf : X.Modules) :=
    (Scheme.Modules.pullbackId X).app _ ≪≫ e
  rw [AlgebraicGeometry.intersectionNumber_eq_of_isEffectiveCartierDivisor' k sX (𝟙 X) 1
    hd _ P'.idealSheaf hL, Divisor.degreeOn, degreeOn,
    ← AlgebraicGeometry.intersectionNumber_one_eq_invertibleCurveDegree k sX C.ι C.dim_le _,
    AlgebraicGeometry.intersectionNumber_congr_family k sX _ 1 _
    (show (fun t : Fin 1 => ![Divisor.divisorialSheaf (Finsupp.single P' 1 : Divisor X),
        Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor X)] t.succ) =
      fun _ => Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor X) from
      funext fun t => by fin_cases t; rfl),
    ← Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  have hker : (P'.idealSheaf.subschemeι ≫ 𝟙 X).ker = C.ι.ker := by
    rw [Category.comp_id, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι]
    exact (MMP.Mori.vanishingIdeal_closure_genericPoint_eq_idealSheaf P').symm
  exact (sheafIntersectionNumber_eq_of_ker_eq k sX _ _ hker 1 _ C.dim_le _).trans
    (Snapper.sheafIntersectionNumber_eq_intersectionNumber k sX C.ι 1 _ _)

omit [IsIntegral X] in
include hsm in
/-- On a smooth scheme the intersection number of a `ℚ`-divisor `D = ∑ a_P P` with a curve is
`∑ a_P deg_C 𝒪_X(P)`. -/
private theorem intersectionNumber_eq_sum {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hd : topologicalKrullDim C ≤ 1) (D : QDivisor X) (hD : D.IsQCartier) :
    D.intersectionNumber k sX i hd hD = D.sum fun P a =>
      a * (Divisor.degreeOn k sX i hd (Finsupp.single P 1)
        (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _) : ℚ) := by
  have hq := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  induction D using Finsupp.induction_linear with
  | zero =>
    rw [Finsupp.sum_zero_index, QDivisor.intersectionNumber_eq_of_smul k sX i hd 0 hD one_pos 0
      Divisor.isCartier_zero (by simp), Divisor.degreeOn_zero']
    simp
  | add f g hf hg =>
    rw [QDivisor.intersectionNumber_add' k sX i hd f g (hq f) (hq g) hD, hf (hq f), hg (hq g),
      Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  | single P a =>
    rw [Finsupp.sum_single_index (zero_mul _)]
    have hP := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
      (Finsupp.single P 1 : Divisor X)
    have key : ∀ (D' : QDivisor X) (hD' : D'.IsQCartier),
        D' = a • Divisor.toQDivisor (Finsupp.single P 1) →
        D'.intersectionNumber k sX i hd hD' =
          a * (Divisor.degreeOn k sX i hd (Finsupp.single P 1) hP : ℚ) := by
      rintro _ hD' rfl
      rw [QDivisor.intersectionNumber_smul k sX i hd a _ (QDivisor.isQCartier_toQDivisor hP) hD',
        QDivisor.intersectionNumber_toQDivisor k sX i hd _ hP]
    refine key _ hD ?_
    rw [MMP.Threefold.Resolution.toQDivisor_single, Finsupp.smul_single, smul_eq_mul,
      Int.cast_one, mul_one]

end Curves

section Degree

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- `D ≡ D'` as soon as `D' - D` is numerically trivial. -/
private theorem numericallyEquivalent_of_isNumericallyTrivial_sub {D D' : QDivisor X}
    (hD : D.IsQCartier) (hD' : D'.IsQCartier) (h : (D' - D).IsNumericallyTrivial k sX) :
    D.NumericallyEquivalent k sX D' := by
  obtain ⟨hDD, h0⟩ := (QDivisor.isNumericallyTrivial_iff _).1 h
  refine ⟨hD, hD', fun C i _ _ _ hC => ?_⟩
  have key : ∀ (E : QDivisor X) (hE : E.IsQCartier), E = (D' - D) + D →
      E.intersectionNumber k sX i hC.le hE = D.intersectionNumber k sX i hC.le hD := by
    rintro _ hE rfl
    rw [QDivisor.intersectionNumber_add' k sX i hC.le _ _ hDD hD hE, h0 C i hC, zero_add]
  exact (key D' hD' (sub_add_cancel D' D).symm).symm

end Degree

section NefTrivialCurves

/-- **The `N`-trivial curves of a surface.** Let `N` be a nef, not numerically trivial
`ℚ`-divisor on a smooth projective surface `S`. An `N`-trivial curve numerically equivalent to a
positive multiple of `N` is disjoint from every other `N`-trivial curve, and only countably many
`N`-trivial curves are not numerically equivalent to a positive multiple of `N`. -/
private theorem disjoint_support_and_countable_of_isNef {S : Scheme.{0}}
    (sS : S ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsProjectiveVariety ℂ sS] [Smooth sS]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] (hSd : topologicalKrullDim S = 2)
    (N : QDivisor S) (hN : N.IsNef ℂ sS) (hNnt : ¬ N.IsNumericallyTrivial ℂ sS) :
    (∀ P P' : MMP.Mori.PrimeDivisor S,
      (∃ c : ℚ, 0 < c ∧ QDivisor.NumericallyEquivalent ℂ sS (Finsupp.single P 1) (c • N)) →
      N.intersectionNumber ℂ sS (primeCurve sS hSd P').ι (primeCurve sS hSd P').dim_le hN.1 = 0 →
      P' ≠ P → Disjoint P.support P'.support) ∧
    {P : MMP.Mori.PrimeDivisor S |
      N.intersectionNumber ℂ sS (primeCurve sS hSd P).ι (primeCurve sS hSd P).dim_le hN.1 = 0 ∧
      ¬ ∃ c : ℚ, 0 < c ∧
        QDivisor.NumericallyEquivalent ℂ sS (Finsupp.single P 1) (c • N)}.Countable := by
  classical
  have hsm : IsSmoothScheme sS := MMP.Flips.isSmoothScheme_of_smooth sS
  have hq := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  obtain ⟨_, hpa, -, -, Nsub, hNsub, -, hcount⟩ :=
    MMP.Mori.exists_forall_isCartier_and_intersectionNumberOn_of_smooth sS hSd
  let I : MMP.Mori.PrimeDivisor S → MMP.Mori.PrimeDivisor S → ℤ := fun C C' =>
    Divisor.intersectionNumberOn ℂ sS (𝟙 S) 2 hSd.le
      ![Finsupp.single C 1, Finsupp.single C' 1] fun j => by
        fin_cases j <;>
          exact MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm _
  let Q : QDivisor S → QDivisor S → ℚ := fun A B =>
    A.sum fun C a => B.sum fun C' b => a * b * I C C'
  have hQsingle : ∀ (A : QDivisor S) (P : MMP.Mori.PrimeDivisor S),
      Q A (Finsupp.single P 1) = A.intersectionNumber ℂ sS (primeCurve sS hSd P).ι
        (primeCurve sS hSd P).dim_le (hq A) := by
    intro A P
    rw [intersectionNumber_eq_sum sS hsm (primeCurve sS hSd P).ι (primeCurve sS hSd P).dim_le A
      (hq A)]
    refine Finsupp.sum_congr fun C _ => ?_
    simp only [I]
    rw [Finsupp.sum_single_index (by simp), intersectionNumberOn_eq_degreeOn sS hsm hSd C P]
    ring
  refine ⟨fun P P' ⟨c, hc, heq⟩ hP' hne => ?_, ?_⟩
  · have : IsIntegral (primeCurve sS hSd P').scheme := isIntegral_curveSubschemeAt _
    have hI : (I P P' : ℚ) = 0 := by
      have h1 : (I P P' : ℚ) = Q (Finsupp.single P 1) (Finsupp.single P' 1) := by
        simp only [Q]
        rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
        ring
      rw [h1, hQsingle, heq.intersectionNumber_eq (hq _) (hq _) (primeCurve sS hSd P').ι
          (primeCurve sS hSd P').dim_eq,
        QDivisor.intersectionNumber_smul ℂ sS _ _ c N (hq N) (hq _)]
      have : N.intersectionNumber ℂ sS (primeCurve sS hSd P').ι (primeCurve sS hSd P').dim_le
        (hq N) = 0 := hP'
      rw [this, mul_zero]
    exact ((hpa P P' hne.symm).2).1 (by exact_mod_cast hI)
  · refine Set.MapsTo.countable_of_injOn
      (f := fun P => (QuotientAddGroup.mk (Finsupp.single P 1) : Divisor S ⧸ Nsub))
      (fun P _ => Set.mem_range_self P) ?_ hcount
    intro B hB B' hB' heq
    by_contra hne
    have htriv := (hNsub _).1 (QuotientAddGroup.eq.1 heq)
    rw [map_add, map_neg, MMP.Threefold.Resolution.toQDivisor_single,
      MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one, neg_add_eq_sub] at htriv
    have hBB' := numericallyEquivalent_of_isNumericallyTrivial_sub sS (hq _) (hq _) htriv
    obtain ⟨-, c, hc, hc'⟩ :=
      (MMP.Mori.selfIntersection_eq_zero_and_exists_numericallyEquivalent_smul_of_isNef sS hSd
        N hN hNnt).1 B B' hne ((hQsingle N B).trans hB.1) ((hQsingle N B').trans hB'.1) hBB'
    exact hB.2 ⟨c, hc, hc'⟩

end NefTrivialCurves

section Combinatorics

/-- Countably many members of `T` meet the closed set `F` without being contained in it. -/
private theorem countable_meets_of_disjoint {S X ι κ : Type*} (μ : S → X) (supp : κ → Set S)
    (cl : ι → Set X) (T : Set ι) (tS Pos : κ → Prop)
    (hO : {P | tS P ∧ ¬ Pos P}.Countable)
    (hdisj : ∀ P P', Pos P → tS P' → P' ≠ P → Disjoint (supp P) (supp P'))
    (lift : ι → κ) (hlt : ∀ Γ ∈ T, tS (lift Γ)) (hli : ∀ Γ ∈ T, μ '' supp (lift Γ) = cl Γ)
    (hcl : Set.InjOn cl T) (F : Set X) (Q : Set S) (hQ : Q.Finite)
    (hdich : ∀ q, μ q ∈ F → q ∈ Q ∨ ∃ P, supp P ⊆ μ ⁻¹' F ∧ q ∈ supp P)
    (h1 : ∀ P, supp P ⊆ μ ⁻¹' F → tS P) :
    {Γ | Γ ∈ T ∧ (cl Γ ∩ F).Nonempty ∧ ¬ cl Γ ⊆ F}.Countable := by
  classical
  set A := {Γ | Γ ∈ T ∧ (cl Γ ∩ F).Nonempty ∧ ¬ cl Γ ⊆ F}
  have hinj : Set.InjOn lift A := fun Γ₁ h₁ Γ₂ h₂ h =>
    hcl h₁.1 h₂.1 (by rw [← hli Γ₁ h₁.1, ← hli Γ₂ h₂.1, h])
  have hA : A ⊆ {Γ | Γ ∈ A ∧ ¬ Pos (lift Γ)} ∪ {Γ | Γ ∈ A ∧ Pos (lift Γ)} := by
    intro Γ h
    by_cases hp : Pos (lift Γ)
    exacts [Or.inr ⟨h, hp⟩, Or.inl ⟨h, hp⟩]
  refine Set.Countable.mono hA (Set.Countable.union ?_ ?_)
  · exact Set.MapsTo.countable_of_injOn (f := lift) (t := {P | tS P ∧ ¬ Pos P})
      (fun Γ h => ⟨hlt Γ h.1.1, h.2⟩) (hinj.mono fun _ h => h.1) hO
  · have key : ∀ Γ ∈ {Γ | Γ ∈ A ∧ Pos (lift Γ)}, ∃ q ∈ Q, q ∈ supp (lift Γ) := by
      rintro Γ ⟨⟨hT, ⟨x, hxc, hxF⟩, hnot⟩, hpos⟩
      rw [← hli Γ hT] at hxc
      obtain ⟨q, hq, rfl⟩ := hxc
      rcases hdich q hxF with hqQ | ⟨P, hPF, hqP⟩
      · exact ⟨q, hqQ, hq⟩
      · exfalso
        have hne : P ≠ lift Γ := by
          rintro rfl
          exact hnot (by rw [← hli Γ hT]; exact Set.image_subset_iff.2 hPF)
        exact Set.disjoint_left.mp (hdisj _ _ hpos (h1 P hPF) hne) hq hqP
    have key' : ∀ Γ : {Γ // Γ ∈ A ∧ Pos (lift Γ)}, ∃ q : Q, q.1 ∈ supp (lift Γ.1) :=
      fun Γ => by
        obtain ⟨q, hq, hqs⟩ := key Γ.1 Γ.2
        exact ⟨⟨q, hq⟩, hqs⟩
    choose q hqs using key'
    have : Countable Q := hQ.countable.to_subtype
    refine Set.countable_coe_iff.mp (Function.Injective.countable (f := q) ?_)
    intro Γ₁ Γ₂ h
    by_contra hne
    have hne' : lift Γ₂.1 ≠ lift Γ₁.1 := fun h' =>
      hne (Subtype.ext (hinj Γ₁.2.1 Γ₂.2.1 h'.symm))
    exact Set.disjoint_left.mp (hdisj _ _ Γ₁.2.2 (hlt Γ₂.1 Γ₂.2.1.1) hne') (hqs Γ₁)
      (by rw [h]; exact hqs Γ₂)

/-- The members of `T` joined to `x₀` by connected finite unions form a countable cover. -/
private theorem exists_countable_cover_of_isConnected {X ι : Type*} [TopologicalSpace X]
    (cl : ι → Set X) (hcl : ∀ Γ, IsClosed (cl Γ)) (T : Set ι) (x₀ : X)
    (h0 : {Γ | Γ ∈ T ∧ x₀ ∈ cl Γ}.Countable)
    (hstep : ∀ Γ' ∈ T, {Γ | Γ ∈ T ∧ (cl Γ ∩ cl Γ').Nonempty}.Countable) (p : X → Prop)
    (hconn : ∀ x, p x → ∃ s : Finset ι, IsConnected (⋃ C ∈ s, cl C) ∧
      x₀ ∈ (⋃ C ∈ s, cl C) ∧ x ∈ (⋃ C ∈ s, cl C) ∧ ∀ C ∈ s, C ∈ T) :
    ∃ K : Set ι, K.Countable ∧ ∀ x, p x → ∃ Γ ∈ K, x ∈ cl Γ := by
  classical
  let K : ℕ → Set ι := fun n => Nat.rec {Γ | Γ ∈ T ∧ x₀ ∈ cl Γ}
    (fun _ Kn => {Γ | Γ ∈ T ∧ ∃ Γ' ∈ Kn, (cl Γ ∩ cl Γ').Nonempty}) n
  have hK0 : K 0 = {Γ | Γ ∈ T ∧ x₀ ∈ cl Γ} := rfl
  have hKs : ∀ n, K (n + 1) = {Γ | Γ ∈ T ∧ ∃ Γ' ∈ K n, (cl Γ ∩ cl Γ').Nonempty} := fun _ => rfl
  have hKT : ∀ n, K n ⊆ T := by
    intro n
    cases n with
    | zero => rw [hK0]; exact fun Γ h => h.1
    | succ n => rw [hKs]; exact fun Γ h => h.1
  have hKc : ∀ n, (K n).Countable := by
    intro n
    induction n with
    | zero => rw [hK0]; exact h0
    | succ n ih =>
      have : K (n + 1) ⊆ ⋃ Γ' ∈ K n, {Γ | Γ ∈ T ∧ (cl Γ ∩ cl Γ').Nonempty} := by
        rw [hKs]
        rintro Γ ⟨hT, Γ', hΓ', hne⟩
        exact Set.mem_biUnion hΓ' ⟨hT, hne⟩
      exact (ih.biUnion fun Γ' h => hstep Γ' (hKT n h)).mono this
  refine ⟨⋃ n, K n, Set.countable_iUnion hKc, fun x hx => ?_⟩
  obtain ⟨s, hs, hx₀, hxs, hsT⟩ := hconn x hx
  set U := ⋃ C ∈ s, cl C
  set A := ⋃ C ∈ s.filter (fun C => C ∈ ⋃ n, K n), cl C
  set B := ⋃ C ∈ s.filter (fun C => C ∉ ⋃ n, K n), cl C
  have hAc : IsClosed A := isClosed_biUnion_finset fun C _ => hcl C
  have hBc : IsClosed B := isClosed_biUnion_finset fun C _ => hcl C
  have hcov : U ⊆ A ∪ B := by
    intro y hy
    obtain ⟨C, hC, hyC⟩ := Set.mem_iUnion₂.mp hy
    by_cases hCK : C ∈ ⋃ n, K n
    · exact Or.inl (Set.mem_biUnion (Finset.mem_filter.mpr ⟨hC, hCK⟩) hyC)
    · exact Or.inr (Set.mem_biUnion (Finset.mem_filter.mpr ⟨hC, hCK⟩) hyC)
  have hdisj : ∀ y, y ∈ A → y ∉ B := by
    intro y hyA hyB
    obtain ⟨C₁, hC₁, hy₁⟩ := Set.mem_iUnion₂.mp hyA
    obtain ⟨C₂, hC₂, hy₂⟩ := Set.mem_iUnion₂.mp hyB
    obtain ⟨hC₁s, hC₁K⟩ := Finset.mem_filter.mp hC₁
    obtain ⟨hC₂s, hC₂K⟩ := Finset.mem_filter.mp hC₂
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hC₁K
    apply hC₂K
    refine Set.mem_iUnion.mpr ⟨n + 1, ?_⟩
    rw [hKs]
    exact ⟨hsT C₂ hC₂s, C₁, hn, y, hy₂, hy₁⟩
  have hAne : (U ∩ A).Nonempty := by
    refine ⟨x₀, hx₀, ?_⟩
    obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx₀
    have hCK : C ∈ ⋃ n, K n := Set.mem_iUnion.mpr ⟨0, by rw [hK0]; exact ⟨hsT C hC, hxC⟩⟩
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hC, hCK⟩) hxC
  have hxA : x ∈ A := (hcov hxs).resolve_right fun h => by
    obtain ⟨y, -, hyA, hyB⟩ :=
      isPreconnected_closed_iff.mp hs.isPreconnected A B hAc hBc hcov hAne ⟨x, hxs, h⟩
    exact hdisj y hyA hyB
  obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hxA
  exact ⟨C, (Finset.mem_filter.mp hC).2, hxC⟩

end Combinatorics

section Setup

open Order

/-- **A smooth projective surface onto a prime divisor.** For a point `x` of height two of a
projective variety `X` over `ℂ`, there is a smooth projective surface `S` and a morphism
`μ : S ⟶ X` over `ℂ` with image `{x}⁻`: a resolution of the normalization of `{x}⁻`. -/
private theorem exists_smooth_projective_surface_range_eq {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsProjectiveVariety ℂ sX] (x : X)
    (hx : height x = 2) :
    ∃ (S : Scheme.{0}) (sS : S ⟶ Spec (.of ℂ)) (μ : S ⟶ X),
      AlgebraicGeometry.IsProjectiveVariety ℂ sS ∧ Smooth sS ∧ topologicalKrullDim S = 2 ∧
        μ ≫ sX = sS ∧ Set.range μ = closure {x} := by
  set ι := curveSubschemeAtι x
  have : IsIntegral (curveSubschemeAt x) := isIntegral_curveSubschemeAt x
  have hXp := (inferInstance : AlgebraicGeometry.IsProjectiveVariety ℂ sX)
  have : AlgebraicGeometry.IsVariety ℂ sX := hXp.toIsVariety
  have : AlgebraicGeometry.IsVariety ℂ (ι ≫ sX) := { }
  have hZd : topologicalKrullDim (curveSubschemeAt x) = 2 := by
    rw [topologicalKrullDim_curveSubschemeAt, hx]; rfl
  have hZp : AlgebraicGeometry.IsProjectiveVariety ℂ (ι ≫ sX) := by
    obtain ⟨n, i, hi, hi'⟩ := hXp.isProjective
    exact { isProjective := ⟨n, ι ≫ i, inferInstance, by rw [Category.assoc, hi']⟩ }
  obtain ⟨⟨hνv, hνn, hνf, hνs, hνb⟩, -, -, -, hνp⟩ := MMP.Threefold.normalization_spec (ι ≫ sX)
  set hfin := MMP.finite_irreducibleComponents_of_isIntegral
    (curveSubschemeAt x)
  set ν := (curveSubschemeAt x).normalization hfin
  have := hνv
  have := hνn
  have := hνf
  have hdn : topologicalKrullDim ((curveSubschemeAt x).normalizationScheme hfin) = 2 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (ι ≫ sX) (ν ≫ ι ≫ sX)
      hνb).symm.trans hZd
  obtain ⟨Y, sY, f, hYv, hYs, hYd, hf, hfp, hfb⟩ :=
    MMP.Mori.exists_smooth_isProper_isBirationalMorphism_of_isNormalVariety ℂ (ν ≫ ι ≫ sX)
      ⟨hνv, hνn⟩ hdn
  have := hYv
  have := hYs
  have := hfp
  have : IsDominant f := hfb.isDominant
  have hfsurj : Function.Surjective f := by
    rw [← Set.range_eq_univ, ← f.isClosedMap.isClosed_range.closure_eq]
    exact f.denseRange.closure_range
  have : IsProper sX := inferInstance
  have : IsProper sY := by rw [← hf]; infer_instance
  have hproj : AlgebraicGeometry.IsProjectiveVariety ℂ sY :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ sY).2 ⟨hYv,
      MMP.isProjectiveMorphism_of_smooth_of_isProper_of_topologicalKrullDim_eq_two sY hYd⟩
  refine ⟨Y, sY, f ≫ ν ≫ ι, hproj, hYs, hYd, by rw [← hf]; simp only [Category.assoc], ?_⟩
  rw [show ((f ≫ ν ≫ ι : Y ⟶ X) : Y → X) = ι ∘ ν ∘ f from rfl,
    (hνs.surj.comp hfsurj).range_comp, MMP.Mori.range_curveSubschemeAtι]

/-- **A surface is not covered by countably many curves.** For a point `x` of height two of a
projective variety over `ℂ` and countably many proper curves, some closed point of `{x}⁻` lies on
none of them. -/
private theorem exists_isClosed_mem_closure_notMem_of_countable {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsProjectiveVariety ℂ sX] {x : X}
    (hx : height x = 2) {K : Set (ProperCurve sX)} (hK : K.Countable) :
    ∃ y ∈ closure {x}, IsClosed ({y} : Set X) ∧ ∀ C ∈ K, y ∉ closure {C.point} := by
  obtain ⟨n, i₀, hi₀, -⟩ :=
    (inferInstance : AlgebraicGeometry.IsProjectiveVariety ℂ sX).isProjective
  set b := Pi.basisFun ℂ (Fin (n + 1))
  set j : X ⟶ projectiveSpaceOfModule ℂ (Fin (n + 1) → ℂ) :=
    i₀ ≫ (projectiveSpaceOfModuleIso b).inv
  have hrj : ∀ x : X, Set.range (curveSubschemeAtι x ≫ j) = j '' closure {x} := by
    intro x
    rw [show ((curveSubschemeAtι x ≫ j : _ ⟶ _) : _ → _) = j ∘ curveSubschemeAtι x from rfl,
      Set.range_comp, MMP.Mori.range_curveSubschemeAtι]
  have hdimj : ∀ x : X, topologicalKrullDim (Set.range (curveSubschemeAtι x ≫ j)) = height x := by
    intro x
    rw [← (curveSubschemeAtι x ≫ j).isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph
        |>.topologicalKrullDim_eq,
      topologicalKrullDim_curveSubschemeAt]
  have : Countable K := hK.to_subtype
  have : Uncountable ℂ := Complex.ofReal_injective.uncountable
  have := isIntegral_curveSubschemeAt x
  obtain ⟨z, hzZ, hzc, hzB⟩ := exists_isClosed_singleton_notMem_iUnion_of_topologicalKrullDim_le_one
    (Z := Set.range (curveSubschemeAtι x ≫ j))
    (curveSubschemeAtι x ≫ j).isClosedEmbedding.isClosed_range
    (by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _
        (curveSubschemeAtι x ≫ j).continuous.continuousOn)
    (by rw [hdimj, hx]; rfl)
    (fun C : K => Set.range (curveSubschemeAtι C.1.point ≫ j))
    (fun C => (curveSubschemeAtι C.1.point ≫ j).isClosedEmbedding.isClosed_range)
    (fun C => by rw [hdimj, height_point_eq_one]; rfl)
  rw [hrj] at hzZ
  obtain ⟨y, hyx, rfl⟩ := hzZ
  refine ⟨y, hyx, ?_, fun C hC hyC =>
    hzB (Set.mem_iUnion.2 ⟨⟨C, hC⟩, by rw [hrj]; exact ⟨y, hyC, rfl⟩⟩)⟩
  have h1 : (j : X → _) ⁻¹' {j y} = {y} := by
    rw [← Set.image_singleton, Set.preimage_image_eq _ j.isClosedEmbedding.injective]
  rw [← h1]
  exact hzc.preimage j.continuous

end Setup

section Projection

/-- The intersection number along a closed subscheme depends only on its ideal sheaf. -/
private theorem intersectionNumber_subschemeι_congr {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (L : QDivisor X) (hL : L.IsQCartier) {I J : X.IdealSheafData} (h : I = J)
    [IsProper (I.subschemeι ≫ sX)] [IsProper (J.subschemeι ≫ sX)]
    (hI : topologicalKrullDim I.subscheme ≤ 1) (hJ : topologicalKrullDim J.subscheme ≤ 1) :
    L.intersectionNumber k sX I.subschemeι hI hL =
      L.intersectionNumber k sX J.subschemeι hJ hL := by
  subst h
  rfl

/-- The reduced image of a morphism from a reduced scheme onto the closure of a proper curve
`Γ` has the intersection numbers of `Γ`. -/
private theorem intersectionNumber_imageι_eq {k : Type u} [Field k] {X C : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (L : QDivisor X) (hL : L.IsQCartier) (φ : C ⟶ X) [IsReduced C]
    [IsProper (φ.imageι ≫ sX)] (hd : topologicalKrullDim φ.image ≤ 1) (Γ : ProperCurve sX)
    (hφ : Set.range φ = closure {Γ.point}) :
    L.intersectionNumber k sX φ.imageι hd hL = L.intersectionNumber k sX Γ.ι Γ.dim_le hL := by
  have hker : φ.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure {Γ.point}) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    ext1
    simp [hφ]
  exact intersectionNumber_subschemeι_congr sX L hL hker hd Γ.dim_le

variable {S X : Scheme.{0}} (sS : S ⟶ Spec (.of ℂ)) (sX : X ⟶ Spec (.of ℂ))
  [AlgebraicGeometry.IsProperVariety ℂ sS] [AlgebraicGeometry.IsProperVariety ℂ sX]
  [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian S] [IsNormal S]
  (μ : S ⟶ X) (hμ : μ ≫ sX = sS) (L : QDivisor X) (hL : L.IsQCartier)
  (M : Divisor X) (hM : M.IsCartier) (r : ℕ) (hr : 0 < r)
  (hML : Divisor.toQDivisor M = (r : ℤ) • L) (N₀ : Divisor S) (hN₀ : N₀.IsCartier)

include hμ hr hML hM hN₀ in
/-- **The projection formula for the pull-back `N` of `L = (1/r) M`.** Let `N₀` be a Cartier
divisor on `S` with `𝒪_S(N₀) ≅ μ^* 𝒪_X(M)`, and `C ⊆ S` an integral closed curve. If `μ(C)` is a
point, `N₀ · C = 0`; otherwise `N₀ · C = d · (L · μ(C))` for a rational `d > 0`, where `μ(C)` is
the reduced image of `C`, an integral proper curve. -/
private theorem intersectionNumber_pullback_curve
    (e : N₀.divisorialSheaf ≅ (Scheme.Modules.pullback μ).obj M.divisorialSheaf)
    (C : Scheme.{0}) (i : C ⟶ S) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sS)]
    (hC : topologicalKrullDim C = 1) (hq : (Divisor.toQDivisor N₀).IsQCartier) :
    ((∃ y : X, Set.range (i ≫ μ) = {y}) →
        (Divisor.toQDivisor N₀).intersectionNumber ℂ sS i hC.le hq = 0) ∧
      (¬ (∃ y : X, Set.range (i ≫ μ) = {y}) →
        ∃ d : ℚ, 0 < d ∧ ∃ (_ : IsProper ((i ≫ μ).imageι ≫ sX))
          (hT : topologicalKrullDim (i ≫ μ).image = 1),
          (Divisor.toQDivisor N₀).intersectionNumber ℂ sS i hC.le hq =
            d * L.intersectionNumber ℂ sX (i ≫ μ).imageι hT.le hL) := by
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have := hN₀.isInvertibleModule_divisorialSheaf
  have := hM.isInvertibleModule_divisorialSheaf
  have : AlgebraicGeometry.IsVariety ℂ (i ≫ sS) := { }
  have : AlgebraicGeometry.IsCurve ℂ (i ≫ sS) :=
    (AlgebraicGeometry.isCurve_iff ℂ _).2 ⟨inferInstance, hC⟩
  have hdeg : (Divisor.toQDivisor N₀).intersectionNumber ℂ sS i hC.le hq =
      MMP.Mori.degreeOn ℂ sS i
        (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := i ≫ sS)).le
        ((Scheme.Modules.pullback μ).obj M.divisorialSheaf) := by
    rw [QDivisor.intersectionNumber_toQDivisor ℂ sS i hC.le N₀ hN₀]
    exact_mod_cast invertibleCurveDegree_eq_of_iso ℂ (i ≫ sS) _
      ((Scheme.Modules.pullback i).mapIso e)
  have hφ : (i ≫ μ) ≫ sX = i ≫ sS := by rw [Category.assoc, hμ]
  have : IsProper ((i ≫ μ) ≫ sX) := hφ ▸ inferInstance
  have : AlgebraicGeometry.IsCurve ℂ ((i ≫ μ) ≫ sX) := hφ ▸ inferInstance
  refine ⟨fun hpt => ?_, fun hnc => ?_⟩
  · rw [hdeg]
    exact_mod_cast degreeOn_pullback_divisorialSheaf_eq_zero sS sX μ i hμ M hM hpt
  · have hcurve := isCurve_imageι_comp sX (i ≫ μ) hnc
    have : IsProper ((i ≫ μ).imageι ≫ sX) := isProper_imageι_comp (i ≫ μ) sX
    have : IsProper (i ≫ μ) := IsProper.of_comp (i ≫ μ) sX
    have hT := hcurve.topologicalKrullDim_eq_one
    have key := degreeOn_pullback_divisorialSheaf_eq_degreeOver_mul_intersectionNumber sS sX μ i
      hμ M hM hcurve
    have hpos := AlgebraicGeometry.degreeOver_pos_of_not_constant ℂ ((i ≫ μ) ≫ sX)
      ((i ≫ μ).imageι ≫ sX)
      (i ≫ μ).toImage (by simp) (not_exists_toImage_eq (i ≫ μ) hnc)
    refine ⟨(degreeOver (i ≫ μ).toImage : ℚ) * r, ?_, inferInstance, hT, ?_⟩
    · have : (0 : ℚ) < degreeOver (i ≫ μ).toImage := by exact_mod_cast hpos
      positivity
    · rw [hdeg, key, QDivisor.intersectionNumber_toQDivisor ℂ sX _ _ M hM,
        QDivisor.intersectionNumber_eq_of_smul ℂ sX _ hT.le L hL hr M hM hML]
      have : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp

include hμ hr hML hM hN₀ hL in
/-- The pull-back `N₀` of a nef `L` is nef. -/
private theorem isNef_toQDivisor_of_isNef
    (e : N₀.divisorialSheaf ≅ (Scheme.Modules.pullback μ).obj M.divisorialSheaf)
    (hq : (Divisor.toQDivisor N₀).IsQCartier) (hN : L.IsNef ℂ sX) :
    (Divisor.toQDivisor N₀).IsNef ℂ sS := by
  have KF := intersectionNumber_pullback_curve sS sX μ hμ L hL M hM r hr hML N₀ hN₀ e
  refine ⟨hq, fun C i _ _ _ hC => ?_⟩
  by_cases hc : ∃ y : X, Set.range (i ≫ μ) = {y}
  · rw [(KF C i hC hq).1 hc]
  · obtain ⟨d, hd, hprop, hT, heq⟩ := (KF C i hC hq).2 hc
    rw [heq]
    have : IsProper ((i ≫ μ) ≫ sX) := by rw [Category.assoc, hμ]; infer_instance
    have : IsProper (i ≫ μ) := IsProper.of_comp (i ≫ μ) sX
    have : IsIntegral (i ≫ μ).image := isIntegral_image (i ≫ μ)
    exact mul_nonneg hd.le (hN.2 _ (i ≫ μ).imageι hT)

end Projection

section Points

open Order

/-- A point of a scheme has height zero exactly when it is a closed point. -/
private theorem height_eq_zero_iff_isClosed {X : Scheme.{u}} (x : X) :
    height x = 0 ↔ IsClosed ({x} : Set X) := by
  refine ⟨fun h => isClosed_of_closure_subset fun y hy => ?_, Scheme.height_of_isClosed⟩
  have hyx : y ≤ x := (specializes_iff_mem_closure.2 hy : x ⤳ y)
  have hxy : y ⤳ x := (Order.height_eq_zero.1 h hyx : x ≤ y)
  exact Set.mem_singleton_iff.2 (hxy.antisymm (specializes_iff_mem_closure.2 hy)).eq

/-- In the specialization order on a scheme, `x ≤ y` and `x ≠ y` give `x < y`. -/
private theorem lt_of_le_of_ne_of_specializes {X : Scheme.{u}} {x y : X} (h : x ≤ y)
    (hne : x ≠ y) : x < y :=
  lt_of_le_not_ge h fun h' => hne (Specializes.antisymm (h' : x ⤳ y) (h : y ⤳ x)).eq

/-- Two comparable points of the same finite height coincide. -/
private theorem eq_of_le_of_height_eq {X : Scheme.{u}} {x y : X} (h : x ≤ y)
    (hxy : height x = height y) (hfin : height x < ⊤) : x = y := by
  by_contra hne
  exact (Order.height_strictMono (lt_of_le_of_ne_of_specializes h hne) hfin).ne hxy

/-- A strict specialization of a point of height one is a closed point. -/
private theorem isClosed_singleton_of_lt_of_height_eq_one {X : Scheme.{u}} {x y : X} (h : y < x)
    (hx : height x = 1) : IsClosed ({y} : Set X) := by
  have hle := Order.height_mono h.le
  rw [hx] at hle
  have hlt := Order.height_strictMono h (hle.trans_lt ENat.one_lt_top)
  rw [hx] at hlt
  exact (height_eq_zero_iff_isClosed _).1 (Order.lt_one_iff.1 hlt)

/-- A closed map sends the closure of a point onto the closure of its image. -/
private theorem image_closure_singleton_eq {S X : Scheme.{u}} (μ : S ⟶ X) [UniversallyClosed μ]
    (x : S) : μ '' closure {x} = closure {μ x} := by
  rw [← μ.isClosedMap.closure_image_eq_of_continuous μ.continuous, Set.image_singleton]

/-- In `ℕ∞`, if `a + b = 2` with `a, b ≠ 0`, then `b = 1`. -/
private theorem eq_one_of_add_eq_two_of_ne_zero {a b : ℕ∞} (h : a + b = ((2 : ℕ) : ℕ∞))
    (ha : a ≠ 0) (hb : b ≠ 0) : b = 1 := by
  have hat : a ≠ ⊤ := by rintro rfl; simp at h
  have hbt : b ≠ ⊤ := by rintro rfl; simp at h
  lift a to ℕ using hat
  lift b to ℕ using hbt
  norm_cast at h ha hb ⊢
  omega

/-- On an integral surface, a point of positive height whose closure is not everything has
coheight one. -/
private theorem coheight_eq_one_of_dim_two {k : Type u} [Field k] {S : Scheme.{u}}
    (sS : S ⟶ Spec (.of k)) [IsIntegral S] [LocallyOfFiniteType sS]
    (hSd : topologicalKrullDim S = 2) (ζ : S) (hh : height ζ ≠ 0)
    (hne : closure {ζ} ≠ Set.univ) : coheight ζ = 1 := by
  have hc : coheight ζ ≠ 0 := by
    intro h0
    rw [Order.coheight_eq_zero] at h0
    apply hne
    have hle : ζ ≤ genericPoint S :=
      ((genericPoint_spec S).specializes (Set.mem_univ ζ) : genericPoint S ⤳ ζ)
    have hge : ζ ⤳ genericPoint S := (h0 hle : genericPoint S ≤ ζ)
    refine Set.eq_univ_of_forall fun y => specializes_iff_mem_closure.1 ?_
    exact hge.trans ((genericPoint_spec S).specializes (Set.mem_univ y))
  exact eq_one_of_add_eq_two_of_ne_zero (height_add_coheight_of_dim_eq sS hSd ζ) hh hc

/-- On a Noetherian integral surface, the points of a proper closed subset `G` lie, outside a
finite set, on prime divisors contained in `G`. -/
private theorem exists_finite_forall_mem_or_exists_primeDivisor {k : Type u} [Field k]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of k)) [IsIntegral S] [LocallyOfFiniteType sS]
    [IsNoetherian S] (hSd : topologicalKrullDim S = 2) {G : Set S} (hG : IsClosed G)
    (hGne : G ≠ Set.univ) :
    ∃ Qs : Set S, Qs.Finite ∧ ∀ q ∈ G, q ∈ Qs ∨
      ∃ P : MMP.Mori.PrimeDivisor S, P.support ⊆ G ∧ q ∈ P.support := by
  obtain ⟨Ts, hTirr, hTeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finset_irreducible
      (⟨G, hG⟩ : TopologicalSpace.Closeds S)
  refine ⟨⋃ Z ∈ Ts, {ζ | IsGenericPoint ζ (Z : Set S)},
    Ts.finite_toSet.biUnion fun Z _ => Set.Subsingleton.finite fun a ha b hb => ha.eq hb,
    fun q hq => ?_⟩
  have hq' : q ∈ ((Ts.sup id : TopologicalSpace.Closeds S) : Set S) := by rwa [← hTeq]
  rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion] at hq'
  obtain ⟨Z, hZ, hqZ⟩ := Set.mem_iUnion₂.mp hq'
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hTirr ⟨Z, hZ⟩) Z.isClosed
  by_cases hqζ : q = ζ
  · exact Or.inl (Set.mem_biUnion hZ (hqζ ▸ hζ))
  right
  have hZG : (Z : Set S) ⊆ G := by
    intro y hy
    have : y ∈ ((Ts.sup id : TopologicalSpace.Closeds S) : Set S) := by
      rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
      exact Set.mem_biUnion hZ hy
    rwa [← hTeq] at this
  have hqcl : q ∈ closure {ζ} := by rwa [hζ.def]
  have hh : height ζ ≠ 0 := by
    intro h0
    rw [((height_eq_zero_iff_isClosed ζ).1 h0).closure_eq, Set.mem_singleton_iff] at hqcl
    exact hqζ hqcl
  have hne : closure {ζ} ≠ Set.univ := by
    rw [hζ.def]
    intro h
    exact hGne (Set.eq_univ_of_univ_subset (h ▸ hZG))
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne ζ
    (coheight_eq_one_of_dim_two sS hSd ζ hh hne), ?_, ?_⟩
  · rwa [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hζ.def]
  · rwa [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]

/-- Let `μ : S ⟶ X` be a closed morphism from an integral surface onto the closure of a point `x`
of height two. Every proper curve of `X` inside `{x}⁻` is the image of the generic point of a
prime divisor of `S`. -/
private theorem exists_primeDivisor_map_genericPoint_eq {k : Type u} [Field k]
    {S X : Scheme.{u}} (sS : S ⟶ Spec (.of k)) [IsIntegral S] [LocallyOfFiniteType sS]
    (hSd : topologicalKrullDim S = 2) (sX : X ⟶ Spec (.of k)) (μ : S ⟶ X) [UniversallyClosed μ]
    {x : X} (hx : height x = 2) (hrange : Set.range μ = closure {x}) (C : ProperCurve sX)
    (hC : closure {C.point} ⊆ closure {x}) :
    ∃ P : MMP.Mori.PrimeDivisor S, μ P.genericPoint = C.point := by
  obtain ⟨ξ, hξ⟩ : C.point ∈ Set.range μ := hrange ▸ hC (subset_closure rfl)
  have hh : height ξ ≠ 0 := by
    intro h0
    have hcl : IsClosed ({C.point} : Set X) := by
      rw [← hξ, ← Set.image_singleton]
      exact μ.isClosedMap _ ((height_eq_zero_iff_isClosed ξ).1 h0)
    have h1 := Scheme.height_of_isClosed hcl
    rw [height_point_eq_one] at h1
    exact one_ne_zero h1
  have hne : closure {ξ} ≠ Set.univ := by
    intro hu
    have h1 : closure {x} ⊆ closure {C.point} := by
      rw [← hrange, ← Set.image_univ, ← hu, image_closure_singleton_eq, hξ]
    have h2 : x ≤ C.point :=
      (specializes_iff_mem_closure.2 (h1 (subset_closure rfl)) : C.point ⤳ x)
    have h3 := Order.height_mono h2
    rw [hx, height_point_eq_one] at h3
    exact absurd h3 (by norm_num)
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ
    (coheight_eq_one_of_dim_two sS hSd ξ hh hne),
      (congrArg μ (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne ξ _)).trans hξ⟩

end Points

end Helpers

open Order in
/-- **A trivially connected prime divisor is numerically trivial along itself.** Let `X` be a
normal projective threefold over `ℂ` with canonical divisor `K`, `Δ` a `ℚ`-divisor such that
`L = K + Δ` is nef, and `E` a prime divisor such that `E` is `L`-trivially connected
(`MMP.Flips.IsTriviallyConnected`). Then `L · Γ = 0` for every irreducible curve `Γ ⊆ E`. -/
@[mmp "lem_fa15_trivially_connected_numerically_trivial"]
public theorem intersectionNumber_eq_zero_of_isTriviallyConnected {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsLocallyNoetherian X] [IsNormal X]
    [AlgebraicGeometry.IsProjectiveVariety ℂ sX] (hdim : topologicalKrullDim X = 3) (K : Divisor X)
    (Δ : QDivisor X) (hN : (Divisor.toQDivisor K + Δ).IsNef ℂ sX) (E : Mori.PrimeDivisor X)
    (hD : IsTriviallyConnected ℂ sX 3 K Δ (Finsupp.single E 1)) (Γ : ProperCurve sX)
    (hΓ : closure {Γ.point} ⊆ (DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor X) : Set X)) :
    (Divisor.toQDivisor K + Δ).intersectionNumber ℂ sX Γ.ι Γ.dim_le hN.fst = 0 := by
  classical
  set L := Divisor.toQDivisor K + Δ
  have hL : L.IsQCartier := hN.fst
  obtain ⟨-, -, -, _, -, hconn⟩ := hD
  have : IsIntegral X := (inferInstance : AlgebraicGeometry.IsProjectiveVariety ℂ sX).toIsIntegral
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  set D : Set X := closure {E.genericPoint} with hDdef
  have hsupp : ((DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor X)) : Set X) = D := by
    rw [hDdef, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_antisymm (DivisorWithCoeffs.supp_single_le E 1)
      (DivisorWithCoeffs.support_subset_supp (by simp [DivisorWithCoeffs.coeff]))
  rw [hsupp] at hΓ
  have hE2 : height E.genericPoint = 2 := by
    have h := height_add_coheight_of_dim_eq sX hdim E.genericPoint
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E] at h
    exact WithTop.add_right_cancel ENat.one_ne_top (h.trans rfl)
  have hcurve1 : ∀ C : ProperCurve sX, height C.point = 1 := height_point_eq_one sX
  obtain ⟨S, sS, μ, hSp, hSs, hSd, hμ, hrange⟩ :=
    exists_smooth_projective_surface_range_eq sX E.genericPoint hE2
  replace hrange : Set.range μ = D := hrange
  have := hSp
  have := hSs
  have : IsIntegral S := hSp.toIsIntegral
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  have : IsNormal (Spec (.of ℂ)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed ℂ)
  have : IsNormal S := isNormal_of_smooth sS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : IsNoetherian S := { }
  have : IsProper (μ ≫ sX) := hμ ▸ inferInstance
  have : IsProper μ := IsProper.of_comp μ sX
  have hsm : IsSmoothScheme sS := MMP.Flips.isSmoothScheme_of_smooth sS
  have hq := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  set hLc := QDivisor.isCartierDivisor_cartierIndex_smul hL
  set M := hLc.toDivisor
  have hM : M.IsCartier := hLc.isCartier_toDivisor
  set r := L.cartierIndex hL
  have hr : 0 < r := QDivisor.cartierIndex_pos hL
  have hML : Divisor.toQDivisor M = (r : ℤ) • L := hLc.toQDivisor_toDivisor
  have := hM.isInvertibleModule_divisorialSheaf
  have hinv := MMP.Mori.isInvertible_pullback_obj μ M.divisorialSheaf
  obtain ⟨N₀, ⟨e⟩⟩ := @exists_divisorialSheaf_iso_of_isInvertible S _ _ _ _
    ((Scheme.Modules.pullback μ).obj M.divisorialSheaf) hinv
  have hN₀ : N₀.IsCartier := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm N₀
  set N := Divisor.toQDivisor N₀
  have KF := intersectionNumber_pullback_curve sS sX μ hμ L hL M hM r hr hML N₀ hN₀ e
  let cP : MMP.Mori.PrimeDivisor S → ProperCurve sS := fun P => primeCurve sS hSd P
  have hcPi : ∀ P, IsIntegral (cP P).scheme := fun _ => isIntegral_curveSubschemeAt _
  let tS : MMP.Mori.PrimeDivisor S → Prop := fun P =>
    N.intersectionNumber ℂ sS (cP P).ι (cP P).dim_le (hq N) = 0
  have hrangeP : ∀ P : MMP.Mori.PrimeDivisor S,
      Set.range ((cP P).ι ≫ μ) = closure {μ P.genericPoint} := by
    intro P
    rw [show (((cP P).ι ≫ μ : _ ⟶ X) : _ → X) = μ ∘ (cP P).ι from rfl, Set.range_comp,
      show Set.range (cP P).ι = closure {P.genericPoint} from
      MMP.Mori.range_curveSubschemeAtι P.genericPoint]
    exact image_closure_singleton_eq μ P.genericPoint
  have hcontr : ∀ P : MMP.Mori.PrimeDivisor S,
      (∃ y : X, Set.range ((cP P).ι ≫ μ) = {y}) → tS P := fun P h => by
    have := hcPi P
    exact (KF _ (cP P).ι (cP P).dim_eq (hq N)).1 h
  have hval : ∀ (P : MMP.Mori.PrimeDivisor S) (C : ProperCurve sX), μ P.genericPoint = C.point →
      ∃ d : ℚ, 0 < d ∧ N.intersectionNumber ℂ sS (cP P).ι (cP P).dim_le (hq N) =
        d * L.intersectionNumber ℂ sX C.ι C.dim_le hL := by
    intro P C hPC
    have := hcPi P
    have hr' := hrangeP P
    rw [hPC] at hr'
    have hnc : ¬ ∃ y : X, Set.range ((cP P).ι ≫ μ) = {y} := by
      rintro ⟨y, hy⟩
      rw [hr'] at hy
      have hmem : C.point ∈ ({y} : Set X) := hy ▸ subset_closure rfl
      rw [Set.mem_singleton_iff] at hmem
      subst hmem
      have hcl : IsClosed ({C.point} : Set X) := hy ▸ isClosed_closure
      have h0 := Scheme.height_of_isClosed hcl
      rw [hcurve1] at h0
      exact one_ne_zero h0
    obtain ⟨d, hd, hprop, hT, heq⟩ := (KF _ (cP P).ι (cP P).dim_eq (hq N)).2 hnc
    refine ⟨d, hd, heq.trans ?_⟩
    congr 1
    exact intersectionNumber_imageι_eq sX L hL _ hT.le C hr'
  have hNnef : N.IsNef ℂ sS :=
    isNef_toQDivisor_of_isNef sS sX μ hμ L hL M hM r hr hML N₀ hN₀ e (hq N) hN
  have hlift : ∀ C : ProperCurve sX, closure {C.point} ⊆ D →
      ∃ P : MMP.Mori.PrimeDivisor S, μ P.genericPoint = C.point :=
    exists_primeDivisor_map_genericPoint_eq sS hSd sX μ hE2 hrange
  by_contra hΓ0
  have hNnt : ¬ N.IsNumericallyTrivial ℂ sS := by
    intro htr
    obtain ⟨P, hP⟩ := hlift Γ hΓ
    obtain ⟨d, hd, hv⟩ := hval P Γ hP
    obtain ⟨_, h0⟩ := (QDivisor.isNumericallyTrivial_iff N).1 htr
    have := hcPi P
    have h1 := h0 _ (cP P).ι (cP P).dim_eq
    rw [hv] at h1
    exact hΓ0 ((mul_eq_zero.1 h1).resolve_left hd.ne')
  let Pos : MMP.Mori.PrimeDivisor S → Prop := fun P =>
    ∃ c : ℚ, 0 < c ∧ QDivisor.NumericallyEquivalent ℂ sS (Finsupp.single P 1) (c • N)
  obtain ⟨hdisj, hO⟩ := disjoint_support_and_countable_of_isNef sS hSd N hNnef hNnt
  let cl : ProperCurve sX → Set X := fun C => closure {C.point}
  let T : Set (ProperCurve sX) :=
    {C | cl C ⊆ D ∧ L.intersectionNumber ℂ sX C.ι C.dim_le hL = 0}
  have htT : ∀ (P : MMP.Mori.PrimeDivisor S) (C : ProperCurve sX), C ∈ T →
      μ P.genericPoint = C.point → tS P := fun P C hC hPC => by
    obtain ⟨d, -, h⟩ := hval P C hPC
    change N.intersectionNumber ℂ sS (cP P).ι (cP P).dim_le (hq N) = 0
    rw [h, hC.2, mul_zero]
  have hclinj : Set.InjOn cl T := fun C₁ _ C₂ _ h =>
    ProperCurve.ext (inseparable_iff_closure_eq.2 h).eq
  have hlift' : ∀ C : ProperCurve sX, ∃ P : MMP.Mori.PrimeDivisor S,
      cl C ⊆ D → μ P.genericPoint = C.point := by
    intro C
    by_cases hC : cl C ⊆ D
    · obtain ⟨P, hP⟩ := hlift C hC
      exact ⟨P, fun _ => hP⟩
    · obtain ⟨P, -⟩ := hlift Γ hΓ
      exact ⟨P, fun h => absurd h hC⟩
  choose lift hliftspec using hlift'
  have hli : ∀ C ∈ T, μ '' (lift C).support = cl C := fun C hC => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, image_closure_singleton_eq,
      hliftspec C hC.1]
  have hlt : ∀ C ∈ T, tS (lift C) := fun C hC => htT _ C hC (hliftspec C hC.1)
  have hclaim : ∀ F : Set X, IsClosed F → ¬ D ⊆ F →
      (∀ P : MMP.Mori.PrimeDivisor S, P.support ⊆ μ ⁻¹' F → tS P) →
      {C | C ∈ T ∧ (cl C ∩ F).Nonempty ∧ ¬ cl C ⊆ F}.Countable := by
    intro F hF hDF h1
    obtain ⟨Qs, hQs, hdichF⟩ := exists_finite_forall_mem_or_exists_primeDivisor sS hSd
      (hF.preimage μ.continuous) fun h => hDF (by
        rw [← hrange, ← Set.image_univ, ← h]
        exact Set.image_preimage_subset μ F)
    exact countable_meets_of_disjoint μ (fun P => P.support) cl T tS Pos hO hdisj lift hlt hli
      hclinj F Qs hQs (fun q hq => hdichF q hq) h1
  obtain ⟨x₀, hx₀D, hx₀c⟩ := (isClosed_closure : IsClosed D).exists_closed_singleton
    (⟨E.genericPoint, subset_closure rfl⟩ : D.Nonempty)
  have hx₀h : height x₀ = 0 := Scheme.height_of_isClosed hx₀c
  have hDx₀ : ¬ D ⊆ {x₀} := fun h => by
    have h1 : E.genericPoint = x₀ := h (subset_closure rfl)
    rw [h1, hx₀h] at hE2
    exact absurd hE2 (by norm_num)
  have h0 : {C | C ∈ T ∧ x₀ ∈ cl C}.Countable := by
    refine (hclaim {x₀} hx₀c hDx₀ fun P hP => ?_).mono ?_
    · apply hcontr P
      have hgp : μ P.genericPoint = x₀ := hP (by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
      exact ⟨x₀, by rw [hrangeP, hgp, hx₀c.closure_eq]⟩
    · rintro C ⟨hT, hx⟩
      refine ⟨hT, ⟨x₀, hx, rfl⟩, fun h => ?_⟩
      have hpt : C.point = x₀ := h (subset_closure rfl)
      have h1 := hcurve1 C
      rw [hpt, hx₀h] at h1
      exact zero_ne_one h1
  have hstep : ∀ C' ∈ T, {C | C ∈ T ∧ (cl C ∩ cl C').Nonempty}.Countable := by
    intro C' hC'
    have hDC' : ¬ D ⊆ cl C' := fun h => by
      have h2 : E.genericPoint ≤ C'.point :=
        (specializes_iff_mem_closure.2 (h (subset_closure rfl)) : C'.point ⤳ E.genericPoint)
      have h3 := Order.height_mono h2
      rw [hE2, hcurve1] at h3
      exact absurd h3 (by norm_num)
    have h1 : ∀ P : MMP.Mori.PrimeDivisor S, P.support ⊆ μ ⁻¹' cl C' → tS P := by
      intro P hP
      have hgp : μ P.genericPoint ∈ cl C' := hP (by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
      by_cases heq : μ P.genericPoint = C'.point
      · exact htT P C' hC' heq
      · exact hcontr P ⟨μ P.genericPoint, by
          rw [hrangeP, (isClosed_singleton_of_lt_of_height_eq_one (lt_of_le_of_ne_of_specializes
            (specializes_iff_mem_closure.2 hgp : C'.point ⤳ μ P.genericPoint) heq)
            (hcurve1 C')).closure_eq]⟩
    have hsub : {C | C ∈ T ∧ (cl C ∩ cl C').Nonempty} ⊆
        {C'} ∪ {C | C ∈ T ∧ (cl C ∩ cl C').Nonempty ∧ ¬ cl C ⊆ cl C'} := by
      rintro C ⟨hT, hne⟩
      by_cases hs : cl C ⊆ cl C'
      · left
        have hle : C.point ≤ C'.point :=
          (specializes_iff_mem_closure.2 (hs (subset_closure rfl)) : C'.point ⤳ C.point)
        exact ProperCurve.ext (eq_of_le_of_height_eq hle (by rw [hcurve1, hcurve1])
          (by rw [hcurve1]; exact ENat.one_lt_top))
      · exact Or.inr ⟨hT, hne, hs⟩
    exact ((Set.countable_singleton C').union (hclaim (cl C') isClosed_closure hDC' h1)).mono hsub
  obtain ⟨Kset, hKc, hKcov⟩ := exists_countable_cover_of_isConnected cl
    (fun _ => isClosed_closure) T x₀ h0 hstep (fun x => x ∈ D ∧ IsClosed ({x} : Set X)) (by
      rintro x ⟨hxD, hxc⟩
      obtain ⟨s, hs, hsD, hx₀s, hxs, hsL⟩ :=
        hconn x₀ (by rwa [hsupp]) x (by rwa [hsupp]) hx₀c hxc
      refine ⟨s, hs, hx₀s, hxs, fun C hC => ⟨?_, hsL C hC⟩⟩
      have hsD' : MMP.Flips.curveUnion sX s ⊆ D := by rwa [← hsupp]
      exact (Set.subset_biUnion_of_mem (u := cl) hC).trans hsD')
  obtain ⟨x, hxD, hxc, hxK⟩ := exists_isClosed_mem_closure_notMem_of_countable sX hE2 hKc
  obtain ⟨C, hCK, hxC⟩ := hKcov x ⟨hxD, hxc⟩
  exact hxK C hCK hxC

end MMP.Flips
