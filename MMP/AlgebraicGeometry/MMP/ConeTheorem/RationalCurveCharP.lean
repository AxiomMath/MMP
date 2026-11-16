module
public import MMP.AlgebraicGeometry.Intersection.CartierRestriction
public import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
public import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
public import MMP.AlgebraicGeometry.Curves.RationalCurveImage
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Basic
public import MMP.AlgebraicGeometry.Intersection.Surface.RiemannRochHodgeIndex
public import MMP.AlgebraicGeometry.Intersection.CurveLineBundleDegree
public import MMP.AlgebraicGeometry.ProjectiveBundle.UniversalProperty
public import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
public import MMP.AlgebraicGeometry.SpreadingOut.CountableFieldOfDefinition
public import MMP.AlgebraicGeometry.Curves.MarkedMapFamilyDimension
public import MMP.AlgebraicGeometry.Divisor.FloorSectionAlgebraFG
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor

/-!
# A bounded rational curve from a curve in a smooth open, in positive characteristic

Let `V` be a projective scheme over an algebraically closed field `k` of characteristic `p > 0`,
let `U ⊆ V` be an open subscheme which is smooth of pure relative dimension `n` over `k`, with
canonical sheaf `ω_U = Ωⁿ_{U/k}`, and let `C ⊆ U` be a smooth projective curve of genus
`g ≥ 1`. Suppose `κ = -deg(ω_U|_C) > 0`. Then for every ample invertible sheaf `H` on `V` there
is a rational curve `L ⊆ V` with

`0 < H · L ≤ 2n (H · C) / κ`.

This is Mori's bend-and-break. For `q = p ^ a`, the `a`-fold absolute Frobenius of `C` is a
morphism of degree `q` over `k` from the curve `C_q` (the scheme `C` with its structure morphism
twisted by the Frobenius of `k`) to `C`; composing with `C ⊆ U` gives `f : C_q ⟶ U` with
`deg f^*ω_U = -qκ`. With `b = ⌊(qκ - 1 - 2g)/n⌋ + 1 - g` marked points, the deformations of `f`
fixing them form a space of dimension at least `χ(f^* T_U) - nb - 2g ≥ 1`, so `f` moves in a
one-parameter family `C_q × T° ⟶ V`. Its image is a surface: otherwise the family maps into `C`,
the induced rational map `C_q × T ⇢ C` extends across point blow-ups because rational curves map
to points of `C`, and the rigidity lemma makes the family constant. A degree estimate on the
resolved product surface then splits off a rational curve `L` with `H · L < 2 q (H · C) / b`,
and `q → ∞` gives the bound.

## Main results

* `MMP.Fourfold.exists_isRationalCurve_degreeOn_le_of_charP`: the bounded rational curve.

## Implementation notes

The ample Cartier divisor `H` is recorded by its invertible sheaf, ample in the sense of
`Stacks.Ample.IsAmple`; intersection numbers with curves are `MMP.Mori.degreeOn`, the degree of
the restriction to the curve. `V` is not assumed normal or integral, so no Weil divisor enters.
The smooth open of pure dimension `n` is an open `U` with `U ⟶ Spec k` smooth of relative
dimension `n`, and `ω_U` is `AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms` in
degree `n`, invertible by `Stacks.Discriminant.isInvertible_relativeDifferentialForms`. The curve
`C` is a closed immersion `i : C ⟶ U`; being proper over `k`, it is also closed in `V`. A curve
(`AlgebraicGeometry.IsCurve`) is integral, so in particular connected.

The deformation space is built for a morphism into a quasi-projective variety, so `f` is first
factored through the connected component `U'` of `U` containing the image of `C_q`; it is integral
because `U` is smooth, and `T_{U'} = T_U|_{U'}` because `U' ⟶ U` is an open immersion. A
one-dimensional local ring of the deformation space at `[f]` gives an integral curve through
`[f]`, whose normalization, compactified, is the smooth projective curve `T` of the family. The
degree of `H` on the fibres `C_q × {t}` is independent of the `k`-point `t`, by local constancy of
fibre Euler characteristics in a proper flat family [Stacks, Tag 0B9T].

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 1.13
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MMP.Threefold.Resolution

universe u

namespace MMP.Fourfold

open MMP MMP.Mori

section Curve

/-- A space of topological Krull dimension one has two distinct points. -/
private theorem not_subsingleton_of_topologicalKrullDim_eq_one {X : Type*} [TopologicalSpace X]
    (h : topologicalKrullDim X = 1) : ¬ Subsingleton X := by
  intro _
  have h0 := topologicalKrullDim_zero_of_discreteTopology X
  rw [h] at h0
  exact absurd h0 (by decide)

end Curve

section Pairing

variable (k : Type u) [Field k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) [IsProper f]
  (hd : topologicalKrullDim S ≤ (2 : ℕ))

private theorem isInvertible_pair (N₁ N₂ : S.Modules)
    [h₁ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [h₂ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] :
    ∀ j : Fin 2, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (![N₁, N₂] j) := by
  intro j
  fin_cases j
  exacts [h₁, h₂]

private noncomputable def pair (N₁ N₂ : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] : ℤ :=
  haveI := isInvertible_pair N₁ N₂
  AlgebraicGeometry.intersectionNumber k f (𝟙 S) 2 hd ![N₁, N₂]

private theorem pair_comm (N₁ N₂ : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] :
    pair k f hd N₁ N₂ = pair k f hd N₂ N₁ := by
  haveI := isInvertible_pair N₁ N₂
  haveI := isInvertible_pair N₂ N₁
  unfold pair
  rw [← AlgebraicGeometry.intersectionNumber_comp_perm k f (𝟙 S) 2 hd ![N₂, N₁] (Equiv.swap 0 1)]
  exact AlgebraicGeometry.intersectionNumber_congr_family k f (𝟙 S) 2 hd
    (funext fun j => by fin_cases j <;> rfl)

private theorem sheafIntersectionNumber_two_eq_pair (L : Fin 2 → S.Modules)
    [hL : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (L j)]
    (hd' : topologicalKrullDim S ≤ (2 : ℕ)) :
    sheafIntersectionNumber k f (𝟙 S) 2 hd' L = pair k f hd (L 0) (L 1) := by
  haveI := isInvertible_pair (L 0) (L 1)
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber, pair]
  exact AlgebraicGeometry.intersectionNumber_congr_family k f (𝟙 S) 2 hd
    (funext fun j => by fin_cases j <;> rfl)

private theorem sheafCombinationIntersectionNumber_two_eq_sum {s : ℕ} (c : Fin s → ℚ)
    (M : Fin s → S.Modules) [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M j)]
    (hd' : topologicalKrullDim S ≤ ((2 + 0 : ℕ) : WithBot ℕ∞)) :
    haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
    sheafCombinationIntersectionNumber k f (𝟙 S) ℚ c M 2 ![] hd' =
      ∑ i, ∑ j, c i * c j * (pair k f hd (M i) (M j) : ℚ) := by
  haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
  rw [sheafCombinationIntersectionNumber, ← Fintype.sum_prod_type',
    ← (finTwoArrowEquiv (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun p => ?_
  rw [Fin.prod_univ_two]
  congr 1
  exact_mod_cast sheafIntersectionNumber_two_eq_pair k f hd _ hd'
    (hL := isInvertible_finAppend (a := 2) (b := 0) _ _)

private theorem sheafCombinationIntersectionNumber_one_eq_sum {s : ℕ} (c : Fin s → ℚ)
    (M : Fin s → S.Modules) [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M j)]
    (H : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 H]
    (hd' : topologicalKrullDim S ≤ ((1 + 1 : ℕ) : WithBot ℕ∞)) :
    haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![H] : Fin 1 → S.Modules) j) := fun _ => by simpa
    sheafCombinationIntersectionNumber k f (𝟙 S) ℚ c M 1 ![H] hd' =
      ∑ i, c i * (pair k f hd (M i) H : ℚ) := by
  haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![H] : Fin 1 → S.Modules) j) := fun _ => by simpa
  rw [sheafCombinationIntersectionNumber, ← (Equiv.funUnique (Fin 1) (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [Fin.prod_univ_one]
  congr 1
  exact_mod_cast sheafIntersectionNumber_two_eq_pair k f hd _ hd'
    (hL := isInvertible_finAppend (a := 1) (b := 1) _ _)

/-- The pairing depends only on the isomorphism class of the first sheaf. -/
private theorem pair_congr_left {N₁ N₁' : S.Modules} (N₂ : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁']
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] (e : N₁ ≅ N₁') :
    pair k f hd N₁ N₂ = pair k f hd N₁' N₂ := by
  haveI := isInvertible_pair N₁ N₂
  haveI := isInvertible_pair N₁' N₂
  unfold pair
  exact AlgebraicGeometry.intersectionNumber_eq_of_iso_at k f (𝟙 S) 2 hd _ _ 0
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl) e

/-- The pairing depends only on the isomorphism class of the second sheaf. -/
private theorem pair_congr_right (N₁ : S.Modules) {N₂ N₂' : S.Modules}
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂'] (e : N₂ ≅ N₂') :
    pair k f hd N₁ N₂ = pair k f hd N₁ N₂' := by
  rw [pair_comm, pair_congr_left k f hd N₁ e, pair_comm]

/-- The pairing of a Weil divisor sum: `(𝒪(D + D') · N) = (𝒪(D) · N) + (𝒪(D') · N)`. -/
private theorem pair_divisorialSheaf_add [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {D D' : Divisor S} (hD : D.IsCartier) (hD' : D'.IsCartier) (N : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N] :
    haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D.divisorialSheaf :=
      hD.isInvertibleModule_divisorialSheaf
    haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf :=
      hD'.isInvertibleModule_divisorialSheaf
    haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (D + D').divisorialSheaf :=
      (hD.add hD').isInvertibleModule_divisorialSheaf
    pair k f hd (D + D').divisorialSheaf N =
      pair k f hd D.divisorialSheaf N + pair k f hd D'.divisorialSheaf N := by
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D.divisorialSheaf :=
    hD.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf :=
    hD'.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (D + D').divisorialSheaf :=
    (hD.add hD').isInvertibleModule_divisorialSheaf
  haveI := isInvertible_pair (D + D').divisorialSheaf N
  haveI := isInvertible_pair D.divisorialSheaf N
  haveI := isInvertible_pair D'.divisorialSheaf N
  unfold pair
  exact AlgebraicGeometry.intersectionNumber_tensor k f (𝟙 S) 2 hd 0 _ _ _
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl)
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl)
    (hD.divisorialSheafTensorIso hD').symm

/-- **Cutting down by a curve.** On a smooth proper surface, the pairing of an invertible sheaf
`I ≅ 𝒪_S(P)` of a prime divisor `P` with `N` is the degree of `N` on the proper curve `C` with
the same generic point. -/
private theorem pair_eq_degree_of_iso_invertibleSheaf' [IsLocallyNoetherian S] [IsNormal S]
    (hsm : IsSmoothScheme f) (P : MMP.Mori.PrimeDivisor S) (C : ProperCurve f)
    (hC : C.point = P.genericPoint) (I N : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 I]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N]
    (e : I ≅ (Stacks.Divisors.invertibleSheaf' P.idealSheaf : S.Modules)) :
    pair k f hd I N = C.degree k N := by
  haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P
  haveI := isInvertible_pair I N
  have hL : (Scheme.Modules.pullback (𝟙 S)).obj (![I, N] 0) ≅
      (Stacks.Divisors.invertibleSheaf P.idealSheaf : S.Modules) :=
    (Scheme.Modules.pullbackId S).app I ≪≫ e
  rw [pair, AlgebraicGeometry.intersectionNumber_eq_of_isEffectiveCartierDivisor' k f (𝟙 S) 1
    hd ![I, N] P.idealSheaf hL]
  rw [ProperCurve.degree, degreeOn,
    ← AlgebraicGeometry.intersectionNumber_one_eq_invertibleCurveDegree k f C.ι C.dim_le N]
  rw [AlgebraicGeometry.intersectionNumber_congr_family k f _ 1 _
    (show (fun t : Fin 1 => ![I, N] t.succ) = fun _ => N from funext fun t => by fin_cases t; rfl)]
  rw [← Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  have hker : (P.idealSheaf.subschemeι ≫ 𝟙 S).ker = C.ι.ker := by
    rw [Category.comp_id, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι, hC,
      MMP.Mori.vanishingIdeal_closure_genericPoint_eq_idealSheaf]
  exact (sheafIntersectionNumber_eq_of_ker_eq k f _ _ hker 1 _ C.dim_le _).trans
    (Snapper.sheafIntersectionNumber_eq_intersectionNumber k f C.ι 1 _ _)

end Pairing

section Dimension

open Order

variable {k : Type u} [Field k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k))

/-- The dimension of the reduced closed subscheme on `{x}⁻` is the height of `x`. -/
private theorem topologicalKrullDim_curveSubschemeAt (x : S) :
    topologicalKrullDim (curveSubschemeAt x) = (height x : WithBot ℕ∞) := by
  have h := MMP.Intersection.subvarietyDim_eq_height (MMP.Intersection.associatedSubvariety x)
  rw [MMP.Intersection.genericPoint_associatedSubvariety] at h
  exact h

/-- On an integral `k`-surface locally of finite type, `height x + coheight x = 2`. -/
private theorem height_add_coheight_eq_two [IsIntegral S] [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim S = 2) (x : S) : height x + coheight x = 2 := by
  letI : S.Over (Spec (.of k)) := ⟨f⟩
  have : LocallyOfFiniteType (S ↘ Spec (.of k)) := ‹LocallyOfFiniteType f›
  have hpure : MMP.Intersection.IsPureDimensional S 2 := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [(Homeomorph.Set.univ S).isHomeomorph.topologicalKrullDim_eq, hdim]
    rfl
  exact MMP.Intersection.height_add_coheight_eq_of_isPureDimensional k hpure x

private theorem eq_one_of_add_eq_two {a b : ℕ∞} (h : a + b = 2) (hb : b = 1) : a = 1 := by
  subst hb
  exact WithTop.add_right_cancel ENat.one_ne_top (h.trans one_add_one_eq_two.symm)

/-- The generic point of a prime divisor on a proper surface is the generic point of a proper
curve. -/
private theorem isProperCurve_genericPoint [IsProper f] [IsIntegral S]
    (hdim : topologicalKrullDim S = 2) (P : MMP.Mori.PrimeDivisor S) :
    IsProperCurve f P.genericPoint := by
  refine isProperCurve_of_isProper f ?_
  rw [topologicalKrullDim_curveSubschemeAt]
  have h := height_add_coheight_eq_two f hdim P.genericPoint
  rw [eq_one_of_add_eq_two h (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)]
  rfl

end Dimension

section DivisorPairing

variable (k : Type u) [Field k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) [IsProper f]
  (hd : topologicalKrullDim S ≤ (2 : ℕ))

/-- The proper curve with the generic point of a prime divisor of a proper surface. -/
private noncomputable def curveOf [IsIntegral S] (hdim : topologicalKrullDim S = 2)
    (P : MMP.Mori.PrimeDivisor S) : ProperCurve f :=
  ⟨P.genericPoint, isProperCurve_genericPoint f hdim P⟩

/-- **The pairing with a divisorial sheaf is a sum of degrees**: on a smooth proper surface,
`(𝒪_S(D) · N) = ∑_P n_P deg_P N` for `D = ∑ n_P P`. -/
private theorem pair_divisorialSheaf_eq_sum [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hsm : IsSmoothScheme f) (hdim : topologicalKrullDim S = 2)
    (D : Divisor S) (N : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N] :
    haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D.divisorialSheaf :=
      (isCartier_of_isSmoothScheme hsm D).isInvertibleModule_divisorialSheaf
    pair k f hd D.divisorialSheaf N =
      ∑ P ∈ D.support, D P * (curveOf k f hdim P).degree k N := by
  have hcart := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
  haveI hinv : ∀ D : Divisor S, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      D.divisorialSheaf := fun D => (hcart D).isInvertibleModule_divisorialSheaf
  let φ : Divisor S →+ ℤ :=
    AddMonoidHom.mk' (fun D => pair k f hd D.divisorialSheaf N)
      (fun D D' => pair_divisorialSheaf_add k f hd (hcart D) (hcart D') N)
  have hφ : φ D = D.sum fun P n => n * φ (Finsupp.single P 1) := by
    conv_lhs => rw [← Finsupp.sum_single D]
    rw [map_finsuppSum]
    refine Finsupp.sum_congr fun P _ => ?_
    rw [← Finsupp.smul_single_one, map_zsmul, smul_eq_mul]
  have hdeg : ∀ P, φ (Finsupp.single P 1) = (curveOf k f hdim P).degree k N := by
    intro P
    haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P
    obtain ⟨eP⟩ := MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' P
      inferInstance (hcart _)
    exact pair_eq_degree_of_iso_invertibleSheaf' k f hd hsm P (curveOf k f hdim P) rfl _ _ eP
  change φ D = _
  rw [hφ, Finsupp.sum]
  simp only [hdeg]

end DivisorPairing

section Birational

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme.{u}} [IsIntegral Y]
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

/-- **Intersection numbers are invariant under a surjective birational morphism**
([Stacks, Tag 0BET] with degree one). -/
private theorem pair_pullback_of_isBirationalMorphism (k : Type u) [Field k] {Y X : Scheme.{u}}
    (pY : Y ⟶ Spec (.of k)) (pX : X ⟶ Spec (.of k)) [IsProper pY] [IsProper pX]
    (g : Y ⟶ X) (hg : g ≫ pX = pY) [IsIntegral Y] [IsIntegral X]
    (hgb : IsBirationalMorphism g) [Surjective g]
    (hY : topologicalKrullDim Y = 2) (hX : topologicalKrullDim X = 2)
    (hdY : topologicalKrullDim Y ≤ (2 : ℕ)) (hdX : topologicalKrullDim X ≤ (2 : ℕ))
    (N₁ N₂ : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N₂] :
    pair k pY hdY ((Scheme.Modules.pullback g).obj N₁) ((Scheme.Modules.pullback g).obj N₂) =
      pair k pX hdX N₁ N₂ := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  haveI : IsDominant g := (isDominant_iff g).mpr g.surjective.denseRange
  haveI : IsProper (g ≫ pX) := hg ▸ inferInstance
  haveI : IsProper g := IsProper.of_comp g pX
  haveI : IsProper (𝟙 Y ≫ g) := by rw [Category.id_comp]; infer_instance
  haveI : Surjective (𝟙 Y ≫ g) := by rw [Category.id_comp]; infer_instance
  haveI : Surjective (𝟙 Y ≫ g).imageι := surjective_imageι (𝟙 Y ≫ g)
  haveI : IsIso (𝟙 Y ≫ g).imageι :=
    isIso_of_isClosedImmersion_of_surjective (𝟙 Y ≫ g).imageι
  haveI : IsIntegral (𝟙 Y ≫ g).image := Stacks.Chow.isIntegral_image (𝟙 Y ≫ g)
  haveI : IsProper (𝟙 Y ≫ g).toImage := Stacks.Chow.isProper_toImage (𝟙 Y ≫ g)
  have hY' : topologicalKrullDim Y = ((2 : ℕ) : WithBot ℕ∞) := hY
  have hIm : topologicalKrullDim (𝟙 Y ≫ g).image = ((2 : ℕ) : WithBot ℕ∞) :=
    (IsHomeomorph.topologicalKrullDim_eq (𝟙 Y ≫ g).imageι
      (isHomeomorph_iff_isEmbedding_surjective.mpr
        ⟨(𝟙 Y ≫ g).imageι.isEmbedding, (𝟙 Y ≫ g).imageι.surjective⟩)).trans hX
  haveI := isInvertible_pair N₁ N₂
  have hpull := AlgebraicGeometry.intersectionNumber_pullback_eq_degreeOver_mul k pY pX g hg
      (𝟙 Y) 2 hY'
    ![N₁, N₂] hIm
  have hdeg : degreeOver (𝟙 Y ≫ g).toImage = 1 := by
    rw [← degreeOver_eq_degreeOver_of_isIso g (𝟙 Y ≫ g).toImage (𝟙 Y ≫ g).imageι
      ((𝟙 Y ≫ g).toImage_imageι.trans (Category.id_comp g))]
    exact degreeOver_eq_one_of_isBirationalMorphism g hgb
  have hint : intersectionNumber k pX (𝟙 Y ≫ g).imageι 2 hIm.le ![N₁, N₂] =
      intersectionNumber k pX (𝟙 X) 2 hdX ![N₁, N₂] :=
    intersectionNumber_eq_intersectionNumber_id k pX (𝟙 Y ≫ g).imageι 2 hIm.le hdX _
  rw [hdeg, hint, Nat.cast_one, one_mul] at hpull
  haveI := isInvertible_pair ((Scheme.Modules.pullback g).obj N₁)
    ((Scheme.Modules.pullback g).obj N₂)
  unfold pair
  rw [← hpull]
  exact AlgebraicGeometry.intersectionNumber_congr_family k pY (𝟙 Y) 2 hdY
    (funext fun j => by fin_cases j <;> rfl)

end Birational

section Blowup

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- The reduced closed point `{w}`, as an ideal sheaf. -/
local notation "𝓘[" w ", " hw "]" =>
  Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : TopologicalSpace.Closeds _)

/-- **The blow-up of a closed point of a smooth projective surface**: the clauses used along a
chain of point blow-ups. -/
private theorem blowUp_basic (hY : MMP.Mori.IsVariety k sY) (hYs : IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2) (hYp : MMP.Mori.IsProjectiveVariety k sY) {w : Y}
    (hw : IsClosed ({w} : Set Y)) :
    MMP.Mori.IsVariety k (blowUpToBase 𝓘[w, hw] ≫ sY) ∧
      IsSmoothScheme (blowUpToBase 𝓘[w, hw] ≫ sY) ∧
      topologicalKrullDim (blowUp 𝓘[w, hw]) = 2 ∧
      MMP.Mori.IsProjectiveVariety k (blowUpToBase 𝓘[w, hw] ≫ sY) ∧
      IsProper (blowUpToBase 𝓘[w, hw]) ∧
      IsBirationalMorphism (blowUpToBase 𝓘[w, hw]) ∧ Surjective (blowUpToBase 𝓘[w, hw]) ∧
      ∀ y : Y, y ≠ w → y ∈ biregularLocus (blowUpToBase 𝓘[w, hw]) := by
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsIntegral Y := hY.toIsIntegral
  have : Smooth sY := smooth_of_isSmoothScheme hYs
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨hV, hsm, hdim, hproj, hbir, hiso, -⟩ :=
    MMP.Threefold.Resolution.isProjective_blowUpToBase_vanishingIdeal_singleton_and_isMinusOneCurve
        sY hY hYd hw
  have hsb := isSmoothBlowup_vanishingIdeal_singleton sY hYs hw
  have hirr := isIrreducible_support_vanishingIdeal_singleton hw
  have hcodim := codimension_vanishingIdeal_singleton_eq_two hY hYd hw
  obtain ⟨-, -, -, -, -, hprojc⟩ :=
    smooth_isProjective_isBirationalMorphism_blowUpToBase sY _ hsb hirr hcodim.ge
  have hproper : IsProper (blowUpToBase 𝓘[w, hw]) :=
    TwoStepTower.isProper_blowUpToBase (TwoStepTower.isFiniteType_of_isLocallyNoetherian _)
  have hYpr : IsProjective sY := by
    have : AlgebraicGeometry.IsVariety k sY := hY
    exact (AlgebraicGeometry.isProjectiveVariety_iff_isProjective k sY).mp hYp
  have : AlgebraicGeometry.IsVariety k (blowUpToBase 𝓘[w, hw] ≫ sY) := hV
  have hproj' : MMP.Mori.IsProjectiveVariety k (blowUpToBase 𝓘[w, hw] ≫ sY) :=
    (AlgebraicGeometry.isProjectiveVariety_iff_isProjective k _).mpr (hprojc hYpr)
  have : IrreducibleSpace Y := inferInstance
  have hdom := isDominant_blowUpToBase_singleton hYd hw
  have hsurj : Surjective (blowUpToBase 𝓘[w, hw]) :=
    surjective_of_isDominant_of_isClosed_range _
      (blowUpToBase 𝓘[w, hw]).isClosedMap.isClosed_range
  exact ⟨hV, (MMP.Mori.isSmoothScheme_iff _).mpr hsm, hdim, hproj', hproper, hbir, hsurj,
    fun y hy => mem_biregularLocus_blowUpToBase_singleton hw hy⟩

section ProjectiveLine

variable (k : Type u) [Field k]

/-- The projective line over a field is normal: it is isomorphic to `Proj k[T₀, T₁]`. -/
private theorem isNormal_projectiveLine : IsNormal (projectiveLine k) := by
  haveI := Stacks.ResolutionOfSurfaces.isNormal_projectiveLineProj k
  exact isNormal_of_isOpenImmersion (projectiveLineIsoProj k).hom

/-- The projective line over a field has Krull dimension at most one. -/
private theorem krullDim_projectiveLine_le : Order.krullDim (projectiveLine k) ≤ 1 := by
  rw [Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim,
    (projectiveLine_isCurve k).topologicalKrullDim_eq_one]

/-- The projective line, as the closed subscheme of itself cut out by the zero ideal, is a
rational curve. -/
private theorem isRationalCurve_projectiveLine :
    haveI := projectiveLine_isIntegral k
    IsRationalCurve (projectiveLine k ↘ Spec (.of k)) (⊥ : (projectiveLine k).IdealSheafData) := by
  haveI := projectiveLine_isIntegral k
  let e : (⊥ : (projectiveLine k).IdealSheafData).subscheme ≅ projectiveLine k :=
    asIso (⊥ : (projectiveLine k).IdealSheafData).subschemeι
  haveI : Nonempty (⊥ : (projectiveLine k).IdealSheafData).subscheme :=
    ⟨e.inv (Classical.arbitrary _)⟩
  haveI : IsIntegral (⊥ : (projectiveLine k).IdealSheafData).subscheme :=
    isIntegral_of_isOpenImmersion e.hom
  refine ⟨⟨inferInstance, ?_⟩, inferInstance,
    inv (⊥ : (projectiveLine k).IdealSheafData).subschemeι,
    by simp, inferInstance, isBirationalMorphism_of_isIso _⟩
  rw [← (projectiveLine_isCurve k).topologicalKrullDim_eq_one]
  exact IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph

/-- The local rings of the projective line are valuation rings. -/
private theorem valuationRing_stalk_projectiveLine (x : projectiveLine k) :
    ValuationRing ((projectiveLine k).presheaf.stalk x) := by
  haveI := isNormal_projectiveLine k
  haveI := projectiveLine_isIntegral k
  haveI : IsLocallyNoetherian (projectiveLine k) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveLine k ↘ Spec (.of k))
  exact MMP.valuationRing_stalk
    (MMP.coheight_le_one (krullDim_projectiveLine_le k) x)

end ProjectiveLine

/-- A morphism which is an isomorphism over `V` is injective over `V`. -/
private theorem eq_of_mem_biregularLocus {Y Y' : Scheme.{u}} (π : Y' ⟶ Y) {a b : Y'}
    (ha : π a ∈ biregularLocus π) (h : π a = π b) : a = b := by
  set V := biregularLocus π
  have : IsIso (π ∣_ V) := isBiregular_biregularLocus π
  have hb : π b ∈ V := h ▸ ha
  let pa : (π ⁻¹ᵁ V).toScheme := ⟨a, ha⟩
  let pb : (π ⁻¹ᵁ V).toScheme := ⟨b, hb⟩
  have e : ∀ p : (π ⁻¹ᵁ V).toScheme, V.ι ((π ∣_ V) p) = π ((π ⁻¹ᵁ V).ι p) := fun p => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have h1 : (π ∣_ V) pa = (π ∣_ V) pb := V.ι.isOpenEmbedding.injective (by rwa [e, e])
  exact congrArg Subtype.val ((π ∣_ V).homeomorph.injective h1)

/-- **Lifting a parametrized curve through a proper morphism.** If `π : Y' ⟶ Y` is proper and
`g : ℙ¹ ⟶ Y` maps the generic point into the locus over which `π` is an isomorphism, then `g`
lifts to `ℙ¹ ⟶ Y'`. -/
private theorem exists_lift_projectiveLine {Y Y' : Scheme.{u}} (π : Y' ⟶ Y) [IsProper π]
    (g : projectiveLine k ⟶ Y) (hg : g (genericPoint (projectiveLine k)) ∈ biregularLocus π) :
    ∃ g' : projectiveLine k ⟶ Y', g' ≫ π = g := by
  haveI := projectiveLine_isIntegral k
  haveI : IsNoetherian (projectiveLine k) := {}
  set V := biregularLocus π
  have : IsIso (π ∣_ V) := isBiregular_biregularLocus π
  set U : (projectiveLine k).Opens := g ⁻¹ᵁ V
  have hU : Dense (U : Set (projectiveLine k)) := IsOpen.dense U.isOpen ⟨_, hg⟩
  let f : (U : Scheme.{u}) ⟶ Y' := (g ∣_ V) ≫ inv (π ∣_ V) ≫ (π ⁻¹ᵁ V).ι
  have hf : f ≫ π = U.ι ≫ g := by
    show ((g ∣_ V) ≫ inv (π ∣_ V) ≫ (π ⁻¹ᵁ V).ι) ≫ π = U.ι ≫ g
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
      morphismRestrict_ι]
  obtain ⟨V', hUV, g'', hg'', -, hall⟩ :=
    Stacks.ResolutionOfSurfaces.exists_extension_of_valuationRing_stalks g π U hU f hf
  have hV' : V' = ⊤ := eq_top_iff.mpr fun x _ => hall x (valuationRing_stalk_projectiveLine k x)
  subst hV'
  refine ⟨(projectiveLine k).topIso.inv ≫ g'', ?_⟩
  rw [Category.assoc, hg'', ← Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id,
    Category.id_comp]

/-- **The exceptional curve of a point blow-up**: its support is the fibre over the point, it is
parametrized by `ℙ¹_k`, and `𝒪(F)` has degree `-1` on it. -/
private theorem blowUp_exceptional (hY : MMP.Mori.IsVariety k sY) (hYs : IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2) {w : Y} (hw : IsClosed ({w} : Set Y)) :
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hw)).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hw)).2
    haveI := (isVariety_blowUp_singleton hY hYd hw).toQuasiCompact
    haveI := compactSpace_blowUp_singleton hY hYd hw
    ∃ F : MMP.Mori.PrimeDivisor (blowUp 𝓘[w, hw]),
      F.idealSheaf = exceptionalIdeal 𝓘[w, hw] ∧
      (∀ q, q ∈ F.support ↔ blowUpToBase 𝓘[w, hw] q = w) ∧
      (∃ g : projectiveLine k ⟶ blowUp 𝓘[w, hw],
        g ≫ blowUpToBase 𝓘[w, hw] ≫ sY = projectiveLine k ↘ Spec (.of k) ∧
          g (genericPoint (projectiveLine k)) = F.genericPoint) ∧
      ∀ C : ProperCurve (blowUpToBase 𝓘[w, hw] ≫ sY), C.point = F.genericPoint →
        haveI := (isCartier_of_isSmoothScheme (isSmoothScheme_blowUp_singleton hY hYs hYd hw)
          (Finsupp.single F 1)).isInvertibleModule_divisorialSheaf
        C.degree k (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single F 1)) = -1 := by
  have hsm' := isSmoothScheme_blowUp_singleton hY hYs hYd hw
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm').1
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm').2
  haveI := (isVariety_blowUp_singleton hY hYd hw).toQuasiCompact
  haveI := compactSpace_blowUp_singleton hY hYd hw
  have : Smooth sY := smooth_of_isSmoothScheme hYs
  obtain ⟨-, -, -, -, -, -, F, hF, -, hmin⟩ :=
    MMP.Threefold.Resolution.isProjective_blowUpToBase_vanishingIdeal_singleton_and_isMinusOneCurve
      sY hY hYd hw
  obtain ⟨-, ⟨e, he⟩, -⟩ := hmin
  refine ⟨F, hF, fun q => mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hw hF q, ?_, ?_⟩
  · haveI := F.integral
    haveI := projectiveLine_isIntegral k
    refine ⟨e.hom ≫ F.idealSheaf.subschemeι, by rw [Category.assoc, he], ?_⟩
    rw [Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion e.hom]
    rfl
  · intro C hC
    have h := intersectionNumber_exceptional_self_eq_neg_one hY hYs hYd hw F hF C hC
    rw [MMP.Mori.QDivisor.intersectionNumber_toQDivisor k _ C.ι C.dim_le _
      (isCartier_of_isSmoothScheme hsm' _)] at h
    exact_mod_cast h

section Transform

variable (hY : MMP.Mori.IsVariety k sY) (hYs : IsSmoothScheme sY)
  (hYd : topologicalKrullDim Y = 2) {w : Y} (hw : IsClosed ({w} : Set Y))

include hY hYd hw in
/-- The generic point of a prime divisor of a surface is not a closed point. -/
private theorem genericPoint_ne_of_isClosed (R : MMP.Mori.PrimeDivisor Y) : R.genericPoint ≠ w := by
  intro h
  have h1 := R.coheight_genericPoint
  rw [h, coheight_eq_two_of_isClosed hY hYd hw] at h1
  exact absurd h1 (by decide)

include hY hYd in
/-- The generic point of a prime divisor lies in the biregular locus of the blow-up of `w`. -/
private theorem genericPoint_mem_biregularLocus (R : MMP.Mori.PrimeDivisor Y) :
    R.genericPoint ∈ biregularLocus (blowUpToBase 𝓘[w, hw]) :=
  mem_biregularLocus_blowUpToBase_singleton hw (genericPoint_ne_of_isClosed hY hYd hw R)

/-- The strict transform of a prime divisor under the blow-up of `w`. -/
private noncomputable def strictTransform (R : MMP.Mori.PrimeDivisor Y) :
    MMP.Mori.PrimeDivisor (blowUp 𝓘[w, hw]) :=
  (MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some (g := blowUpToBase 𝓘[w, hw]) R
    (genericPoint_mem_biregularLocus hY hYd hw R)).choose

private theorem inverseTransformPrimeDivisor_eq_strictTransform (R : MMP.Mori.PrimeDivisor Y) :
    inverseTransformPrimeDivisor (blowUpToBase 𝓘[w, hw]) R =
      some (strictTransform hY hYd hw R) :=
  (MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some (g := blowUpToBase 𝓘[w, hw]) R
    (genericPoint_mem_biregularLocus hY hYd hw R)).choose_spec.1

private theorem map_genericPoint_strictTransform (R : MMP.Mori.PrimeDivisor Y) :
    blowUpToBase 𝓘[w, hw] (strictTransform hY hYd hw R).genericPoint = R.genericPoint :=
  (MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some (g := blowUpToBase 𝓘[w, hw]) R
    (genericPoint_mem_biregularLocus hY hYd hw R)).choose_spec.2

private theorem strictTransform_injective : Function.Injective (strictTransform hY hYd hw) := by
  intro R R' h
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  have h1 := map_genericPoint_strictTransform hY hYd hw R
  have h2 := map_genericPoint_strictTransform hY hYd hw R'
  rw [h] at h1
  exact h1.symm.trans h2

/-- The strict transform of a divisor is the push-forward of its coefficients along the strict
transform of prime divisors. -/
private theorem inverseTransformDivisor_eq_mapDomain (D : Divisor Y) :
    inverseTransformDivisor (blowUpToBase 𝓘[w, hw]) D =
      Finsupp.mapDomain (strictTransform hY hYd hw) D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add, h, h', Finsupp.mapDomain_add]
  | single R a =>
    rw [inverseTransformDivisor_single, inverseTransformPrimeDivisor_eq_strictTransform hY hYd hw,
      Finsupp.mapDomain_single]
    rfl

/-- The total transform `π^* D = π⁻¹_* D + (mult_w D) F` of a divisor. -/
private noncomputable def totalTransform (F : MMP.Mori.PrimeDivisor (blowUp 𝓘[w, hw]))
    (D : Divisor Y) :
    Divisor (blowUp 𝓘[w, hw]) :=
  Finsupp.mapDomain (strictTransform hY hYd hw) D + Finsupp.single F (D.multiplicityAt w)

private theorem totalTransform_add (F : MMP.Mori.PrimeDivisor (blowUp 𝓘[w, hw]))
    (D D' : Divisor Y) :
    totalTransform hY hYd hw F (D + D') =
      totalTransform hY hYd hw F D + totalTransform hY hYd hw F D' := by
  simp only [totalTransform, Finsupp.mapDomain_add, DivisorWithCoeffs.multiplicityAt_add,
    Finsupp.single_add]
  abel

private theorem totalTransform_zero (F : MMP.Mori.PrimeDivisor (blowUp 𝓘[w, hw])) :
    totalTransform hY hYd hw F 0 = 0 := by
  simp [totalTransform, DivisorWithCoeffs.multiplicityAt]

/-- The total transform as an additive map. -/
private noncomputable def totalTransformHom (F : MMP.Mori.PrimeDivisor (blowUp 𝓘[w, hw])) :
    Divisor Y →+ Divisor (blowUp 𝓘[w, hw]) where
  toFun := totalTransform hY hYd hw F
  map_zero' := totalTransform_zero hY hYd hw F
  map_add' := totalTransform_add hY hYd hw F

private theorem totalTransform_nonneg (F : MMP.Mori.PrimeDivisor (blowUp 𝓘[w, hw])) {D : Divisor Y}
    (hD : 0 ≤ D) : 0 ≤ totalTransform hY hYd hw F D := by
  refine add_nonneg (fun R => ?_) (Finsupp.single_nonneg.mpr ?_)
  · by_cases hR : R ∈ Set.range (strictTransform hY hYd hw)
    · obtain ⟨R₀, rfl⟩ := hR
      rw [Finsupp.mapDomain_apply_of_injective (strictTransform_injective hY hYd hw)]
      exact hD R₀
    · rw [Finsupp.mapDomain_notin_range _ _ hR]
      simp
  · exact Finsupp.sum_nonneg fun P _ => nsmul_nonneg (hD P) _

private theorem totalTransform_mono (F : MMP.Mori.PrimeDivisor (blowUp 𝓘[w, hw])) {D E : Divisor Y}
    (h : D ≤ E) : totalTransform hY hYd hw F D ≤ totalTransform hY hYd hw F E := by
  rw [show E = D + (E - D) by abel, totalTransform_add]
  exact le_add_of_nonneg_right (totalTransform_nonneg hY hYd hw F (sub_nonneg.mpr h))

include hY hYs in
/-- A prime divisor through `x` has multiplicity at least one at `x`, on a smooth scheme. -/
private theorem one_le_multiplicityAt_toNat (P : MMP.Mori.PrimeDivisor Y) {x : Y}
    (hx : x ∈ P.support) : 1 ≤ (P.multiplicityAt x).toNat := by
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
  have : QuasiCompact sY := hY.toQuasiCompact
  have hne := multiplicityAt_ne_top P
    (isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hYs P) x
  have h1 : 1 ≤ P.multiplicityAt x := by
    refine le_iSup₂_of_le 1 ?_ (by simp)
    rw [pow_one]
    exact P.idealSheaf.stalkIdeal_le_maximalIdeal_of_mem_support hx
  rw [← ENat.coe_toNat hne] at h1
  exact_mod_cast h1

/-- The exceptional curve is not a strict transform. -/
private theorem strictTransform_ne (F : MMP.Mori.PrimeDivisor (blowUp 𝓘[w, hw]))
    (hF : blowUpToBase 𝓘[w, hw] F.genericPoint = w) (R : MMP.Mori.PrimeDivisor Y) :
    strictTransform hY hYd hw R ≠ F := by
  intro h
  apply genericPoint_ne_of_isClosed hY hYd hw R
  rw [← map_genericPoint_strictTransform hY hYd hw R, h, hF]

private theorem totalTransform_apply_strictTransform (F : MMP.Mori.PrimeDivisor (blowUp 𝓘[w, hw]))
    (hF : blowUpToBase 𝓘[w, hw] F.genericPoint = w) (D : Divisor Y) (R : MMP.Mori.PrimeDivisor Y) :
    totalTransform hY hYd hw F D (strictTransform hY hYd hw R) = D R := by
  rw [totalTransform, Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective
      (strictTransform_injective hY hYd hw),
    Finsupp.single_eq_of_ne (strictTransform_ne hY hYd hw F hF R), add_zero]

private theorem totalTransform_apply_self (F : MMP.Mori.PrimeDivisor (blowUp 𝓘[w, hw]))
    (hF : blowUpToBase 𝓘[w, hw] F.genericPoint = w) (D : Divisor Y) :
    totalTransform hY hYd hw F D F = D.multiplicityAt w := by
  rw [totalTransform, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.mapDomain_notin_range, zero_add]
  rintro ⟨R, hR⟩
  exact strictTransform_ne hY hYd hw F hF R hR

/-- The components of a total transform are the strict transforms of the components and possibly
the exceptional curve. -/
private theorem mem_support_totalTransform (F : MMP.Mori.PrimeDivisor (blowUp 𝓘[w, hw]))
    {D : Divisor Y} {R : MMP.Mori.PrimeDivisor (blowUp 𝓘[w, hw])}
    (hR : R ∈ (totalTransform hY hYd hw F D).support) :
    R = F ∨ ∃ R₀ ∈ D.support, R = strictTransform hY hYd hw R₀ := by
  by_cases hRF : R = F
  · exact Or.inl hRF
  right
  have hR' : (totalTransform hY hYd hw F D) R ≠ 0 := Finsupp.mem_support_iff.mp hR
  rw [totalTransform, Finsupp.add_apply, Finsupp.single_eq_of_ne hRF, add_zero] at hR'
  by_contra hcon
  push Not at hcon
  apply hR'
  by_cases hran : R ∈ Set.range (strictTransform hY hYd hw)
  · obtain ⟨R₀, rfl⟩ := hran
    rw [Finsupp.mapDomain_apply_of_injective (strictTransform_injective hY hYd hw)]
    by_contra h0
    exact hcon R₀ (Finsupp.mem_support_iff.mpr h0) rfl
  · exact Finsupp.mapDomain_notin_range _ _ hran

include hY hYs in
/-- The multiplicity of an effective divisor at a point of one of its components is positive. -/
private theorem one_le_multiplicityAt_of_mem {D : Divisor Y} (hD : 0 ≤ D)
    {P : MMP.Mori.PrimeDivisor Y}
    (hP : P ∈ D.support) {x : Y} (hx : x ∈ P.support) : 1 ≤ D.multiplicityAt x := by
  have h1 := one_le_multiplicityAt_toNat hY hYs P hx
  have hDP : 1 ≤ D P := by
    have := hD P
    have h0 : D P ≠ 0 := Finsupp.mem_support_iff.mp hP
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  rw [DivisorWithCoeffs.multiplicityAt, Finsupp.sum]
  calc (1 : ℤ) ≤ (P.multiplicityAt x).toNat • D P := by
        rw [nsmul_eq_mul]; nlinarith
    _ ≤ ∑ a ∈ D.support, (a.multiplicityAt x).toNat • D a :=
        Finset.single_le_sum (f := fun a => (a.multiplicityAt x).toNat • D a)
          (fun a _ => nsmul_nonneg (hD a) _) hP

/-- The multiplicity of a divisor at a point off its support is zero. -/
private theorem multiplicityAt_eq_zero_of_forall {D : Divisor Y} {x : Y}
    (h : ∀ P ∈ D.support, x ∉ P.support) : D.multiplicityAt x = 0 := by
  rw [DivisorWithCoeffs.multiplicityAt, Finsupp.sum]
  refine Finset.sum_eq_zero fun P hP => ?_
  rw [P.multiplicityAt_eq_zero_of_notMem (h P hP)]
  simp

include hYs in
/-- **The total transform computes the pull-back sheaf**:
`π^* 𝒪_Y(D) ≅ 𝒪_{Y'}(π⁻¹_* D + (mult_w D) F)`. -/
private theorem nonempty_pullback_divisorialSheaf_iso (F : MMP.Mori.PrimeDivisor (blowUp 𝓘[w, hw]))
    (hF : F.idealSheaf = exceptionalIdeal 𝓘[w, hw]) (D : Divisor Y) :
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hw)).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hw)).2
    Nonempty ((Scheme.Modules.pullback (blowUpToBase 𝓘[w, hw])).obj D.divisorialSheaf ≅
      (totalTransform hY hYd hw F D).divisorialSheaf) := by
  have hsm' := isSmoothScheme_blowUp_singleton hY hYs hYd hw
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm').1
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm').2
  haveI := compactSpace_blowUp_singleton hY hYd hw
  have : QuasiCompact sY := hY.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsIntegral (blowUp 𝓘[w, hw]) := (isVariety_blowUp_singleton hY hYd hw).toIsIntegral
  have hDc := isCartier_of_isSmoothScheme hYs D
  have hB := blowUpToBase_componentGenericPoint_notMem_supp hY hYd hw D
  obtain ⟨e⟩ := MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso hDc
    (blowUpToBase 𝓘[w, hw]) hB
  have hpb : D.pullback hDc hB = totalTransform hY hYd hw F D := by
    rw [totalTransform, ← inverseTransformDivisor_eq_mapDomain hY hYd hw]
    exact Divisor.IsPullback.pullback_eq hDc
      (isPullback_blowUp_singleton hY hYs hYd hw hF D hB)
  rw [hpb] at e
  exact ⟨e.symm⟩

end Transform

end Blowup

section DPair

variable (k : Type u) [Field k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) [IsProper f]
  [IsLocallyNoetherian S] [IsNormal S]

/-- The intersection number `(D · D')` of two divisors on a smooth proper surface. -/
private noncomputable def dpair (hsm : IsSmoothScheme f) (hd : topologicalKrullDim S = 2)
    (D D' : Divisor S) : ℤ :=
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace f
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D.divisorialSheaf :=
    (isCartier_of_isSmoothScheme hsm D).isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf :=
    (isCartier_of_isSmoothScheme hsm D').isInvertibleModule_divisorialSheaf
  pair k f (by rw [hd]; rfl) D.divisorialSheaf D'.divisorialSheaf

private theorem dpair_comm (hsm : IsSmoothScheme f) (hd : topologicalKrullDim S = 2)
    (D D' : Divisor S) :
    dpair k f hsm hd D D' = dpair k f hsm hd D' D := by
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace f
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D.divisorialSheaf :=
    (isCartier_of_isSmoothScheme hsm D).isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf :=
    (isCartier_of_isSmoothScheme hsm D').isInvertibleModule_divisorialSheaf
  exact pair_comm k f _ D.divisorialSheaf D'.divisorialSheaf

/-- The pairing of divisors as a sum of degrees of the first along the components of the
second. -/
private theorem dpair_eq_sum [IsIntegral S] (hsm : IsSmoothScheme f)
    (hd : topologicalKrullDim S = 2)
    (D D' : Divisor S) :
    haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace f
    haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D.divisorialSheaf :=
      (isCartier_of_isSmoothScheme hsm D).isInvertibleModule_divisorialSheaf
    dpair k f hsm hd D D' =
      ∑ P ∈ D'.support, D' P * (curveOf k f hd P).degree k D.divisorialSheaf := by
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace f
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D.divisorialSheaf :=
    (isCartier_of_isSmoothScheme hsm D).isInvertibleModule_divisorialSheaf
  rw [dpair_comm]
  exact pair_divisorialSheaf_eq_sum k f _ hsm hd D' D.divisorialSheaf

omit [IsLocallyNoetherian S] [IsNormal S] in
private theorem dpair_eq [IsLocallyNoetherian S] [IsNormal S] (hsm : IsSmoothScheme f)
    (hd : topologicalKrullDim S = 2) (D D' : Divisor S) [CompactSpace S]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D.divisorialSheaf]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf] :
    dpair k f hsm hd D D' = pair k f (by rw [hd]; rfl) D.divisorialSheaf D'.divisorialSheaf :=
  rfl

end DPair

section Chain

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsLocallyNoetherian X] [IsNormal X]

/-- **The data carried along a chain of point blow-ups** `p : Y ⟶ X` over `T₀`: the total
transforms `D j` of the successive exceptional curves, with the points `x j ∈ T₀` they lie over,
their intersection matrix `(D j · D l) = -δⱼₗ`, the parametrizations of their components by
`ℙ¹`, and the strict and total transforms of the prime divisors of `X`. -/
private structure ChainData (T₀ : Set X) {Y : Scheme.{u}} (p : Y ⟶ X) (sY : Y ⟶ Spec (.of k))
    [IsProper sY] [IsLocallyNoetherian Y] [IsNormal Y] (hsm : IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2) : Type u where
  n : ℕ
  D : Fin n → Divisor Y
  x : Fin n → X
  mem : ∀ j, x j ∈ T₀
  nonneg : ∀ j, 0 ≤ D j
  comp_point : ∀ j, ∀ P ∈ (D j).support, p P.genericPoint = x j
  comp_param : ∀ j, ∀ P ∈ (D j).support, ∃ g : projectiveLine k ⟶ Y,
    g ≫ sY = projectiveLine k ↘ Spec (.of k) ∧ g (genericPoint (projectiveLine k)) = P.genericPoint
  orth : ∀ j l, dpair k sY hsm hYd (D j) (D l) = if j = l then -1 else 0
  strict : ∀ G : MMP.Mori.PrimeDivisor X, ∃ (G' : MMP.Mori.PrimeDivisor Y) (μ : Fin n → ℕ),
    p G'.genericPoint = G.genericPoint ∧
    Nonempty ((Scheme.Modules.pullback p).obj (Divisor.divisorialSheaf (Finsupp.single G 1)) ≅
      Divisor.divisorialSheaf (Finsupp.single G' 1 + ∑ j, (μ j : ℤ) • D j)) ∧
    ∀ j, x j ∉ G.support → μ j = 0
  total : ∀ G : MMP.Mori.PrimeDivisor X, ∃ Q : Divisor Y, 0 ≤ Q ∧
    Nonempty ((Scheme.Modules.pullback p).obj (Divisor.divisorialSheaf (Finsupp.single G 1)) ≅
      Q.divisorialSheaf) ∧
    (∀ R ∈ Q.support, p R.genericPoint ∈ G.support) ∧
    (∀ y, p y ∈ G.support → ∃ R ∈ Q.support, y ∈ R.support) ∧
    ∀ j, x j ∈ G.support → D j ≤ Q

/-- The reduced closed point `{w}`, as an ideal sheaf. -/
local notation "𝓘[" w ", " hw "]" =>
  Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : TopologicalSpace.Closeds _)

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section StepPairing

variable {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)} [IsProper sW] [IsLocallyNoetherian W]
  [IsNormal W] (hW : MMP.Mori.IsVariety k sW) (hWs : IsSmoothScheme sW)
  (hWd : topologicalKrullDim W = 2) (hWp : MMP.Mori.IsProjectiveVariety k sW) {w : W}
  (hw : IsClosed ({w} : Set W))
  [IsProper (blowUpToBase 𝓘[w, hw] ≫ sW)] [IsLocallyNoetherian (blowUp 𝓘[w, hw])]
  [IsNormal (blowUp 𝓘[w, hw])]
  (F : MMP.Mori.PrimeDivisor (blowUp 𝓘[w, hw])) (hF : F.idealSheaf = exceptionalIdeal 𝓘[w, hw])

include hWp hF in
/-- Total transforms have the intersection numbers of the original divisors. -/
private theorem dpair_totalTransform (A B : Divisor W) :
    dpair k (blowUpToBase 𝓘[w, hw] ≫ sW) (isSmoothScheme_blowUp_singleton hW hWs hWd hw)
        (blowUp_basic hW hWs hWd hWp hw).2.2.1
        (totalTransform hW hWd hw F A) (totalTransform hW hWd hw F B) =
      dpair k sW hWs hWd A B := by
  obtain ⟨hV', hs', hd', -, hπp, hπb, hπs, -⟩ := blowUp_basic hW hWs hWd hWp hw
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : CompactSpace (blowUp 𝓘[w, hw]) :=
    QuasiCompact.compactSpace_of_compactSpace (blowUpToBase 𝓘[w, hw] ≫ sW)
  have hc := isCartier_of_isSmoothScheme hWs
  have hc' := isCartier_of_isSmoothScheme hs'
  haveI : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 A.divisorialSheaf :=
    (hc A).isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 B.divisorialSheaf :=
    (hc B).isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible (blowUp 𝓘[w, hw]).presheaf (blowUp 𝓘[w, hw]).ringCatSheaf.2
      (totalTransform hW hWd hw F A).divisorialSheaf :=
    (hc' _).isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible (blowUp 𝓘[w, hw]).presheaf (blowUp 𝓘[w, hw]).ringCatSheaf.2
      (totalTransform hW hWd hw F B).divisorialSheaf :=
    (hc' _).isInvertibleModule_divisorialSheaf
  haveI : IsIntegral W := hW.toIsIntegral
  haveI : IsIntegral (blowUp 𝓘[w, hw]) := hV'.toIsIntegral
  obtain ⟨eA⟩ := nonempty_pullback_divisorialSheaf_iso hW hWs hWd hw F hF A
  obtain ⟨eB⟩ := nonempty_pullback_divisorialSheaf_iso hW hWs hWd hw F hF B
  rw [dpair_eq, dpair_eq, ← pair_congr_left k _ _ _ eA, ← pair_congr_right k _ _ _ eB]
  exact pair_pullback_of_isBirationalMorphism k _ sW (blowUpToBase 𝓘[w, hw]) rfl hπb hd' hWd
    _ _ A.divisorialSheaf B.divisorialSheaf

include hWp hF in
/-- Total transforms are orthogonal to the exceptional curve. -/
private theorem dpair_totalTransform_exceptional (A : Divisor W) :
    dpair k (blowUpToBase 𝓘[w, hw] ≫ sW) (isSmoothScheme_blowUp_singleton hW hWs hWd hw)
        (blowUp_basic hW hWs hWd hWp hw).2.2.1
        (totalTransform hW hWd hw F A) (Finsupp.single F 1) = 0 := by
  obtain ⟨hV', hs', hd', -, hπp, hπb, hπs, -⟩ := blowUp_basic hW hWs hWd hWp hw
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : CompactSpace (blowUp 𝓘[w, hw]) :=
    QuasiCompact.compactSpace_of_compactSpace (blowUpToBase 𝓘[w, hw] ≫ sW)
  have hc := isCartier_of_isSmoothScheme hWs
  have hc' := isCartier_of_isSmoothScheme hs'
  haveI : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 A.divisorialSheaf :=
    (hc A).isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible (blowUp 𝓘[w, hw]).presheaf (blowUp 𝓘[w, hw]).ringCatSheaf.2
      (totalTransform hW hWd hw F A).divisorialSheaf :=
    (hc' _).isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible (blowUp 𝓘[w, hw]).presheaf (blowUp 𝓘[w, hw]).ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single F 1 : Divisor (blowUp 𝓘[w, hw]))) :=
    (hc' _).isInvertibleModule_divisorialSheaf
  haveI : IsIntegral (blowUp 𝓘[w, hw]) := hV'.toIsIntegral
  have : LocallyOfFiniteType sW := hW.toLocallyOfFiniteType
  have : IsSeparated sW := hW.toIsSeparated
  obtain ⟨eA⟩ := nonempty_pullback_divisorialSheaf_iso hW hWs hWd hw F hF A
  rw [dpair_comm, dpair_eq, ← pair_congr_right k _ _ _ eA]
  rw [pair_divisorialSheaf_eq_sum k _ _ hs' hd', Finsupp.support_single_ne_zero _ one_ne_zero,
    Finset.sum_singleton, Finsupp.single_eq_same, one_mul]
  refine ProperCurve.degree_pullback_eq_zero_of_isContractedBy _ rfl _ ?_ _
  intro x hx
  have hF' : ∀ q, q ∈ F.support ↔ blowUpToBase 𝓘[w, hw] q = w := fun q =>
    mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hw hF q
  have hxF : x ∈ F.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact hx
  have hηF : F.genericPoint ∈ F.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  change blowUpToBase 𝓘[w, hw] x = blowUpToBase 𝓘[w, hw] F.genericPoint
  rw [(hF' x).mp hxF, (hF' _).mp hηF]

include hWp in
/-- The exceptional curve has self-intersection `-1`. -/
private theorem dpair_exceptional_self (hFexc : ∀ C : ProperCurve (blowUpToBase 𝓘[w, hw] ≫ sW),
      C.point = F.genericPoint →
        haveI := compactSpace_blowUp_singleton hW hWd hw
        haveI := (isCartier_of_isSmoothScheme (isSmoothScheme_blowUp_singleton hW hWs hWd hw)
          (Finsupp.single F 1)).isInvertibleModule_divisorialSheaf
        C.degree k (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single F 1)) = -1) :
    dpair k (blowUpToBase 𝓘[w, hw] ≫ sW) (isSmoothScheme_blowUp_singleton hW hWs hWd hw)
        (blowUp_basic hW hWs hWd hWp hw).2.2.1 (Finsupp.single F 1) (Finsupp.single F 1) = -1 := by
  obtain ⟨hV', hs', hd', -, -, -, -, -⟩ := blowUp_basic hW hWs hWd hWp hw
  haveI : IsIntegral (blowUp 𝓘[w, hw]) := hV'.toIsIntegral
  haveI : CompactSpace (blowUp 𝓘[w, hw]) :=
    QuasiCompact.compactSpace_of_compactSpace (blowUpToBase 𝓘[w, hw] ≫ sW)
  rw [dpair_eq_sum, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_eq_same, one_mul]
  exact hFexc _ rfl

end StepPairing

/-- **One more point blow-up.** The chain data on `W` give the chain data on the blow-up of a
closed point `w` of `W` lying over `T₀`. -/
private theorem ChainData.nonempty_blowUp (T₀ : Set X) (hT₀ : ∀ x ∈ T₀, IsClosed ({x} : Set X))
    {W : Scheme.{u}} {h : W ⟶ X} {sW : W ⟶ Spec (.of k)} [IsProper sW] [IsLocallyNoetherian W]
    [IsNormal W] (hW : MMP.Mori.IsVariety k sW) (hWs : IsSmoothScheme sW)
    (hWd : topologicalKrullDim W = 2) (hWp : MMP.Mori.IsProjectiveVariety k sW)
    (cd : ChainData T₀ h sW hWs hWd) {w : W} (hw : IsClosed ({w} : Set W)) (hwT : h w ∈ T₀) :
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hW hWs hWd hw)).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hW hWs hWd hw)).2
    haveI : IsProper (blowUpToBase 𝓘[w, hw] ≫ sW) :=
      haveI := (blowUp_basic hW hWs hWd hWp hw).2.2.2.2.1
      inferInstance
    Nonempty (ChainData T₀ (blowUpToBase 𝓘[w, hw] ≫ h) (blowUpToBase 𝓘[w, hw] ≫ sW)
      (isSmoothScheme_blowUp_singleton hW hWs hWd hw) (blowUp_basic hW hWs hWd hWp hw).2.2.1) := by
  obtain ⟨hV', hs', hd', hp', hπp, hπb, hπs, hπbir⟩ := blowUp_basic hW hWs hWd hWp hw
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hs').1
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hs').2
  haveI : IsProper (blowUpToBase 𝓘[w, hw]) := hπp
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  obtain ⟨F, hFI, hFsupp, ⟨gF, hgF, hgFη⟩, hFexc⟩ := blowUp_exceptional hW hWs hWd hw
  have hηF : F.genericPoint ∈ F.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hFw : blowUpToBase 𝓘[w, hw] F.genericPoint = w := (hFsupp _).mp hηF
  -- images of supports
  have hcl : ∀ (P : MMP.Mori.PrimeDivisor W) (y : W), y ∈ P.support →
      h y ∈ closure ({h P.genericPoint} : Set X) := fun P y hy => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
    exact map_mem_closure h.continuous hy (by intro z hz; rw [Set.mem_singleton_iff.mp hz]; rfl)
  have hclG : ∀ (G : MMP.Mori.PrimeDivisor X) {x : X}, x ∈ G.support →
      closure ({x} : Set X) ⊆ G.support := fun G x hx =>
    closure_minimal (Set.singleton_subset_iff.mpr hx) G.idealSheaf.support.isClosed
  -- the multiplicity at `w` detects the components through `w`
  have hmul : ∀ {A : Divisor W}, A.multiplicityAt w ≠ 0 → ∃ R ∈ A.support, w ∈ R.support := by
    intro A hA
    by_contra hcon
    push Not at hcon
    exact hA (multiplicityAt_eq_zero_of_forall hcon)
  -- the composite isomorphism for pull-backs
  have hpb : ∀ (N : X.Modules) (A : Divisor W),
      Nonempty ((Scheme.Modules.pullback h).obj N ≅ A.divisorialSheaf) →
      Nonempty ((Scheme.Modules.pullback (blowUpToBase 𝓘[w, hw] ≫ h)).obj N ≅
        (totalTransform hW hWd hw F A).divisorialSheaf) := by
    rintro N A ⟨e⟩
    obtain ⟨e3⟩ := nonempty_pullback_divisorialSheaf_iso hW hWs hWd hw F hFI A
    exact ⟨((Scheme.Modules.pullbackComp (blowUpToBase 𝓘[w, hw]) h).app N).symm ≪≫
      (Scheme.Modules.pullback (blowUpToBase 𝓘[w, hw])).mapIso e ≪≫ e3⟩
  refine ⟨{ n := cd.n + 1
            D := Fin.snoc (fun j => totalTransform hW hWd hw F (cd.D j)) (Finsupp.single F 1)
            x := Fin.snoc cd.x (h w)
            mem := ?_, nonneg := ?_, comp_point := ?_, comp_param := ?_, orth := ?_,
            strict := ?_, total := ?_ }⟩
  · intro j
    induction j using Fin.lastCases with
    | last => simpa using hwT
    | cast i => simpa using cd.mem i
  · intro j
    induction j using Fin.lastCases with
    | last => simpa using Finsupp.single_nonneg.mpr zero_le_one
    | cast i => simpa using totalTransform_nonneg hW hWd hw F (cd.nonneg i)
  · intro j P hP
    rw [Scheme.Hom.comp_apply]
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last] at hP ⊢
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hP), hFw]
    | cast i =>
      simp only [Fin.snoc_castSucc] at hP ⊢
      rcases mem_support_totalTransform hW hWd hw F hP with hPF | ⟨R, hR, hPR⟩
      · rw [hPF] at hP ⊢
        rw [hFw]
        have hne : (cd.D i).multiplicityAt w ≠ 0 := by
          have := Finsupp.mem_support_iff.mp hP
          rwa [totalTransform_apply_self hW hWd hw F hFw] at this
        obtain ⟨R, hR, hwR⟩ := hmul hne
        have := hcl R w hwR
        rw [cd.comp_point i R hR, (hT₀ _ (cd.mem i)).closure_eq] at this
        exact this
      · rw [hPR, map_genericPoint_strictTransform, cd.comp_point i R hR]
  · intro j P hP
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last] at hP
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hP)]
      exact ⟨gF, hgF, hgFη⟩
    | cast i =>
      simp only [Fin.snoc_castSucc] at hP
      rcases mem_support_totalTransform hW hWd hw F hP with hPF | ⟨R, hR, hPR⟩
      · rw [hPF]; exact ⟨gF, hgF, hgFη⟩
      · rw [hPR]
        obtain ⟨g, hg, hgη⟩ := cd.comp_param i R hR
        have hgb : g (genericPoint (projectiveLine k)) ∈
            biregularLocus (blowUpToBase 𝓘[w, hw]) := by
          rw [hgη]; exact genericPoint_mem_biregularLocus hW hWd hw R
        obtain ⟨g', hg'⟩ := exists_lift_projectiveLine (blowUpToBase 𝓘[w, hw]) g hgb
        refine ⟨g', by rw [← Category.assoc, hg', hg], ?_⟩
        apply eq_of_mem_biregularLocus (blowUpToBase 𝓘[w, hw])
        · rw [← Scheme.Hom.comp_apply, hg']; exact hgb
        · rw [← Scheme.Hom.comp_apply, hg', hgη, map_genericPoint_strictTransform]
  · intro j l
    induction j using Fin.lastCases with
    | last =>
      induction l using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, if_true]
        exact dpair_exceptional_self hW hWs hWd hWp hw F hFexc
      | cast i' =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last i').ne', dpair_comm]
        exact dpair_totalTransform_exceptional hW hWs hWd hWp hw F hFI _
    | cast i =>
      induction l using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last i).ne]
        exact dpair_totalTransform_exceptional hW hWs hWd hWp hw F hFI _
      | cast i' =>
        simp only [Fin.snoc_castSucc, Fin.castSucc_inj]
        rw [dpair_totalTransform hW hWs hWd hWp hw F hFI]
        exact cd.orth i i'
  · intro G
    obtain ⟨G', μ, hG'η, ⟨e⟩, hμ⟩ := cd.strict G
    have hηG : G.genericPoint ∈ G.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    refine ⟨strictTransform hW hWd hw G', Fin.snoc μ (G'.multiplicityAt w).toNat, ?_, ?_, ?_⟩
    · rw [Scheme.Hom.comp_apply, map_genericPoint_strictTransform, hG'η]
    · obtain ⟨e'⟩ := hpb _ _ ⟨e⟩
      have heq : totalTransform hW hWd hw F (Finsupp.single G' 1 + ∑ j, (μ j : ℤ) • cd.D j) =
          Finsupp.single (strictTransform hW hWd hw G') 1 +
            ∑ j, ((Fin.snoc μ (G'.multiplicityAt w).toNat : Fin (cd.n + 1) → ℕ) j : ℤ) •
              (Fin.snoc (fun j => totalTransform hW hWd hw F (cd.D j)) (Finsupp.single F 1) :
                Fin (cd.n + 1) → Divisor _) j := by
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        change totalTransformHom hW hWd hw F _ = _
        rw [map_add, map_sum]
        simp only [map_zsmul]
        have h1 : totalTransformHom hW hWd hw F (Finsupp.single G' 1) =
            Finsupp.single (strictTransform hW hWd hw G') 1 +
              Finsupp.single F ((G'.multiplicityAt w).toNat : ℤ) := by
          change totalTransform hW hWd hw F _ = _
          rw [totalTransform, Finsupp.mapDomain_single, DivisorWithCoeffs.multiplicityAt_single,
            nsmul_eq_mul, mul_one]
        rw [h1, Finsupp.smul_single, smul_eq_mul, mul_one]
        simp only [totalTransformHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        abel
      rw [heq] at e'
      exact ⟨e'⟩
    · intro j hj
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last] at hj ⊢
        have hw' : w ∉ G'.support := fun hwG =>
          hj (hclG G hηG (by rw [← hG'η]; exact hcl G' w hwG))
        rw [G'.multiplicityAt_eq_zero_of_notMem hw']
        rfl
      | cast i =>
        simp only [Fin.snoc_castSucc] at hj ⊢
        exact hμ i hj
  · intro G
    obtain ⟨Q, hQ0, ⟨e⟩, hQcomp, hQcov, hQD⟩ := cd.total G
    refine ⟨totalTransform hW hWd hw F Q, totalTransform_nonneg hW hWd hw F hQ0, hpb _ _ ⟨e⟩,
      ?_, ?_, ?_⟩
    · intro R' hR'
      rw [Scheme.Hom.comp_apply]
      rcases mem_support_totalTransform hW hWd hw F hR' with hRF | ⟨R, hR, hRR⟩
      · rw [hRF] at hR' ⊢
        rw [hFw]
        have hne : Q.multiplicityAt w ≠ 0 := by
          have := Finsupp.mem_support_iff.mp hR'
          rwa [totalTransform_apply_self hW hWd hw F hFw] at this
        obtain ⟨R, hR, hwR⟩ := hmul hne
        exact hclG G (hQcomp R hR) (hcl R w hwR)
      · rw [hRR, map_genericPoint_strictTransform]
        exact hQcomp R hR
    · intro y' hy'
      rw [Scheme.Hom.comp_apply] at hy'
      obtain ⟨R, hR, hyR⟩ := hQcov _ hy'
      by_cases hyw : blowUpToBase 𝓘[w, hw] y' = w
      · refine ⟨F, ?_, (hFsupp y').mpr hyw⟩
        rw [Finsupp.mem_support_iff, totalTransform_apply_self hW hWd hw F hFw]
        have := one_le_multiplicityAt_of_mem hW hWs hQ0 hR (hyw ▸ hyR)
        omega
      · refine ⟨strictTransform hW hWd hw R, ?_, ?_⟩
        · rw [Finsupp.mem_support_iff, totalTransform_apply_strictTransform hW hWd hw F hFw]
          exact Finsupp.mem_support_iff.mp hR
        · have hsp : (strictTransform hW hWd hw R).genericPoint ⤳ y' := by
            apply specializes_of_mem_biregularLocus (blowUpToBase 𝓘[w, hw])
            · rw [map_genericPoint_strictTransform]
              exact genericPoint_mem_biregularLocus hW hWd hw R
            · exact mem_biregularLocus_blowUpToBase_singleton hw hyw
            · rw [map_genericPoint_strictTransform]
              rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyR
              exact specializes_iff_mem_closure.mpr hyR
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact specializes_iff_mem_closure.mp hsp
    · intro j hj
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last] at hj ⊢
        obtain ⟨R, hR, hwR⟩ := hQcov w hj
        have h1 := one_le_multiplicityAt_of_mem hW hWs hQ0 hR hwR
        rw [Finsupp.le_def]
        intro P
        by_cases hP : P = F
        · rw [hP, Finsupp.single_eq_same, totalTransform_apply_self hW hWd hw F hFw]
          exact h1
        · rw [Finsupp.single_eq_of_ne hP]
          exact totalTransform_nonneg hW hWd hw F hQ0 P
      | cast i =>
        simp only [Fin.snoc_castSucc] at hj ⊢
        exact totalTransform_mono hW hWd hw F (hQD i hj)

/-- The chain data on the source of the identity. -/
private theorem ChainData.nonempty_id (T₀ : Set X) [IsProper sX] (hXs : IsSmoothScheme sX)
    (hXd : topologicalKrullDim X = 2) : Nonempty (ChainData T₀ (𝟙 X) sX hXs hXd) := by
  refine ⟨{ n := 0
            D := Fin.elim0
            x := Fin.elim0
            mem := fun j => j.elim0
            nonneg := fun j => j.elim0
            comp_point := fun j => j.elim0
            comp_param := fun j => j.elim0
            orth := fun j => j.elim0
            strict := ?_
            total := ?_ }⟩
  · intro G
    refine ⟨G, Fin.elim0, by rfl, ?_, fun j => j.elim0⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact ⟨(Scheme.Modules.pullbackId X).app _⟩
  · intro G
    have hηG : G.genericPoint ∈ G.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    refine ⟨Finsupp.single G 1, Finsupp.single_nonneg.mpr zero_le_one,
      ⟨(Scheme.Modules.pullbackId X).app _⟩, ?_, ?_, fun j => j.elim0⟩
    · intro R hR
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hR)]
      exact hηG
    · intro y hy
      exact ⟨G, by simp, hy⟩

/-- **The chain data along a chain of point blow-ups** of a smooth projective surface, over a
set `T₀` of closed points missed by an open `U₀`. -/
private theorem exists_chainData (hX : MMP.Mori.IsVariety k sX) (hXs : IsSmoothScheme sX)
    (hXd : topologicalKrullDim X = 2) (hXp : MMP.Mori.IsProjectiveVariety k sX) [IsProper sX]
    (T₀ : Set X) (hT₀ : ∀ x ∈ T₀, IsClosed ({x} : Set X)) (U₀ : X.Opens)
    (hU₀ : ∀ x ∈ T₀, x ∉ U₀) {Y : Scheme.{u}} {p : Y ⟶ X}
    (hc : Stacks.ResolutionOfSurfaces.PointBlowupChain X T₀ Y p) :
    ∃ (sY : Y ⟶ Spec (.of k)) (_ : p ≫ sX = sY) (hY : MMP.Mori.IsVariety k sY)
      (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
      (hYp : MMP.Mori.IsProjectiveVariety k sY) (_ : IsProper p) (_ : Surjective p)
      (_ : IsIso (p ∣_ U₀)),
      haveI : AlgebraicGeometry.IsProjectiveVariety k sY := hYp
      haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
      haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
      Nonempty (ChainData T₀ p sY hYs hYd) := by
  induction hc with
  | refl =>
    refine ⟨sX, Category.id_comp _, hX, hXs, hXd, hXp, inferInstance, inferInstance,
      inferInstance, ?_⟩
    exact ChainData.nonempty_id sX T₀ hXs hXd
  | @step W h hh w hw hwT ih =>
    obtain ⟨sW, hsW, hW, hWs, hWd, hWp, hhp, hhs, hhiso, hcd⟩ := ih
    haveI : AlgebraicGeometry.IsProjectiveVariety k sW := hWp
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs).2
    obtain ⟨cd⟩ := hcd
    obtain ⟨hV', hs', hd', hp', hπp, hπb, hπs, hπbir⟩ := blowUp_basic hW hWs hWd hWp hw
    haveI := hπp
    haveI := hπs
    have hiso : IsIso ((blowUpToBase 𝓘[w, hw] ≫ h) ∣_ U₀) := by
      rw [morphismRestrict_comp]
      have hle : h ⁻¹ᵁ U₀ ≤ biregularLocus (blowUpToBase 𝓘[w, hw]) := by
        intro y hy
        refine hπbir y ?_
        rintro rfl
        exact hU₀ _ hwT hy
      haveI : IsIso (blowUpToBase 𝓘[w, hw] ∣_ biregularLocus (blowUpToBase 𝓘[w, hw])) :=
        isBiregular_biregularLocus _
      have h1 := MMP.Resolution.Kollar.isIso_morphismRestrict_of_le (blowUpToBase 𝓘[w, hw]) hle
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 hhiso
    refine ⟨blowUpToBase 𝓘[w, hw] ≫ sW, by rw [Category.assoc, hsW], hV', hs', hd', hp',
      inferInstance, inferInstance, hiso, ?_⟩
    exact ChainData.nonempty_blowUp T₀ hT₀ hW hWs hWd hWp cd hw hwT

end Chain

section Product

variable {k : Type u} [Field k]

/-- A smooth proper connected scheme over a field is a variety. -/
private theorem isVariety_of_smooth_of_connected {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    [IsProper sZ]
    [Smooth sZ] [ConnectedSpace Z] : AlgebraicGeometry.IsVariety k sZ :=
  haveI := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth sZ
  ⟨⟩

/-- A proper curve over a field is projective. -/
private theorem isProjective_of_curve {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    [AlgebraicGeometry.IsVariety k sZ] (hZ : topologicalKrullDim Z = 1) : IsProjective sZ :=
  (isProjective_iff_isProjectiveMorphism_of_isAffine sZ).mpr
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
      ⟨Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral sZ hZ, inferInstance⟩)

variable [IsAlgClosed k] {C T : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))

/-- **The product of two smooth proper connected curves is a smooth projective surface.** -/
private theorem product_facts [IsProper sC] [Smooth sC] [ConnectedSpace C]
    (hC : topologicalKrullDim C = 1)
    [IsProper sT] [Smooth sT] [ConnectedSpace T] (hT : topologicalKrullDim T = 1) :
    MMP.Mori.IsVariety k (pullback.fst sC sT ≫ sC) ∧
      IsSmoothScheme (pullback.fst sC sT ≫ sC) ∧
      topologicalKrullDim (Limits.pullback sC sT : Scheme.{u}) = 2 ∧
      MMP.Mori.IsProjectiveVariety k (pullback.fst sC sT ≫ sC) := by
  haveI := isVariety_of_smooth_of_connected sC
  haveI := isVariety_of_smooth_of_connected sT
  obtain ⟨hv, hd⟩ := isVariety_and_topologicalKrullDim_pullback k sC sT
  refine ⟨hv, (MMP.Mori.isSmoothScheme_iff _).mpr inferInstance, ?_, ?_⟩
  · rw [hd, hC, hT]; rfl
  · have : AlgebraicGeometry.IsVariety k (pullback.fst sC sT ≫ sC) := hv
    exact (AlgebraicGeometry.isProjectiveVariety_iff_isProjective k _).mpr
      (IsProjective.comp (IsProjective.pullback_fst sC (isProjective_of_curve sT hT))
        (isProjective_of_curve sC hC))

end Product

section Fibre

variable {X B Z : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian B]
  [IsNormal B]

/-- **A fibre which is an integral curve is a prime divisor.** Let `q : X ⟶ B` be a morphism
from an integral surface and `P` a prime divisor of `B` whose scheme-theoretic inverse image
`q⁻¹(P)` is isomorphic to an integral scheme of dimension one. Then the ideal sheaf of `q⁻¹(P)`
is that of a prime divisor `G` of `X`, with support `q⁻¹(P)`. -/
private theorem exists_primeDivisor_fibre {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [IsIntegral X] (hXd : topologicalKrullDim X = 2) (q : X ⟶ B)
    (P : MMP.Mori.PrimeDivisor B)
    (e : (P.idealSheaf.comap q).subscheme ≅ Z) [IsIntegral Z] (hZ : topologicalKrullDim Z = 1) :
    ∃ G : MMP.Mori.PrimeDivisor X, G.idealSheaf = P.idealSheaf.comap q ∧
      (G.support : Set X) = q ⁻¹' P.support := by
  set J := P.idealSheaf.comap q with hJ
  haveI : IsIntegral J.subscheme := IsIntegral.of_isIso e.inv
  set x := J.subschemeι (genericPoint J.subscheme) with hx
  have hcl : closure {x} = (J.support : Set X) := MMP.Resolution.closure_subschemeι_genericPoint J
  -- the height of `x` is the dimension of the fibre
  have hheight : Order.height x = 1 := by
    have h1 := topologicalKrullDim_curveSubschemeAt x
    have h2 : topologicalKrullDim (curveSubschemeAt x) = topologicalKrullDim J.subscheme := by
      rw [MMP.Flips.topologicalKrullDim_subscheme, MMP.Flips.topologicalKrullDim_subscheme,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      change topologicalKrullDim (closure {x}) = _
      rw [hcl]
    rw [h2, IsHomeomorph.topologicalKrullDim_eq e.hom e.hom.homeomorph.isHomeomorph, hZ] at h1
    exact_mod_cast h1.symm
  have hcoh : Order.coheight x = 1 := by
    have := height_add_coheight_eq_two sX hXd x
    rw [hheight] at this
    rw [add_comm] at this
    exact eq_one_of_add_eq_two this rfl
  set G := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hcoh
  have hGη : G.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hcoh
  haveI : IsReduced J.subscheme := inferInstance
  have hJred : J = Scheme.IdealSheafData.vanishingIdeal J.support :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme J J.support rfl
  have hGJ : G.idealSheaf = J := by
    rw [← MMP.Mori.vanishingIdeal_closure_genericPoint_eq_idealSheaf, hJred]
    congr 1
    ext1
    change closure {G.genericPoint} = _
    rw [hGη, hcl]
  refine ⟨G, hGJ, ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support, hGJ, hJ, Scheme.IdealSheafData.support_comap]
  rfl

end Fibre

section FibreDivisor

variable {X B : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]
  [IsLocallyNoetherian B] [IsNormal B]

/-- **The pull-back of a point is its fibre**: if the inverse image ideal of a prime divisor `P`
of `B` is the ideal sheaf of a prime divisor `G` of `X`, then `q^*[P] = [G]`. -/
private theorem pullback_single_eq_of_idealSheaf_eq (q : X ⟶ B) (P : MMP.Mori.PrimeDivisor B)
    (hP : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf)
    (hPc : Divisor.IsCartier (Finsupp.single P 1 : Divisor B))
    (hB : ∀ Z : irreducibleComponents X,
      q (componentGenericPoint X Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor B))
    (G : MMP.Mori.PrimeDivisor X) (hG : G.idealSheaf = P.idealSheaf.comap q)
    (hGe : Stacks.Divisors.IsEffectiveCartierDivisor G.idealSheaf) :
    Divisor.pullback (f := q) (Finsupp.single P 1 : Divisor B) hPc hB = Finsupp.single G 1 := by
  ext E
  obtain ⟨n, hn, hcoeff⟩ := coeff_isPullback_single_eq_idealOrder P hP
    (Divisor.isPullback_pullback hPc hB) E
  rw [← hG] at hn
  rw [DivisorWithCoeffs.coeff, DivisorWithCoeffs.coeff] at *
  rw [hcoeff]
  by_cases hE : E = G
  · rw [hE] at hn ⊢
    have := G.isDiscreteValuationRing_localRing
    rw [stalk_idealSheaf_genericPoint_eq_maximalIdeal G hGe, idealOrder_maximalIdeal] at hn
    have : n = 1 := by exact_mod_cast hn.symm
    rw [this, Finsupp.single_eq_same]
    rfl
  · have hnot : E.genericPoint ∉ G.support := fun h =>
      hE (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (G.eq_genericPoint_of_mem_support h E.coheight_genericPoint))
    rw [(AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_not_mem_support _ _).mpr hnot,
      idealOrder_top] at hn
    have : n = 0 := by exact_mod_cast hn.symm
    rw [this, Finsupp.single_eq_of_ne hE]
    rfl

end FibreDivisor

section CurveDegree

variable (k : Type u) [Field k]

/-- **Degrees along a curve are computed on any closed immersion onto it.** -/
private theorem degree_curve_eq_degreeOn {X C : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX]
    (σ : C ⟶ X) [IsClosedImmersion σ] [IsIntegral C] [IsProper (σ ≫ sX)]
    (hdimC : topologicalKrullDim C ≤ 1) (Q : ProperCurve sX)
    (hQ : Q.point = σ (genericPoint C)) (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    Q.degree k N = MMP.Mori.degreeOn k sX σ hdimC N := by
  -- the kernels of `σ` and of the curve agree
  have hiso : IsIso (IsClosedImmersion.lift σ.ker.subschemeι σ
      (Scheme.IdealSheafData.ker_subschemeι _).le) :=
    IsClosedImmersion.isIso_lift _ _ (Scheme.IdealSheafData.ker_subschemeι _)
  haveI : IsReduced σ.ker.subscheme :=
    isReduced_of_isOpenImmersion (inv (IsClosedImmersion.lift σ.ker.subschemeι σ
      (Scheme.IdealSheafData.ker_subschemeι _).le))
  have hker : σ.ker = Q.ι.ker := by
    rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme σ.ker σ.ker.support rfl,
      Scheme.IdealSheafData.ker_subschemeι]
    congr 1
    apply TopologicalSpace.Closeds.ext
    rw [Scheme.Hom.support_ker, TopologicalSpace.Closeds.coe_closure, hQ]
    apply subset_antisymm
    · refine closure_minimal ?_ isClosed_closure
      rintro _ ⟨c, rfl⟩
      exact map_mem_closure σ.continuous (by rw [(genericPoint_spec C).def]; trivial)
        (by intro z hz; rw [Set.mem_singleton_iff.mp hz]; rfl)
    · exact closure_mono (Set.singleton_subset_iff.mpr ⟨_, rfl⟩)
  haveI := IsClosedImmersion.isIso_lift Q.ι σ hker.symm
  rw [ProperCurve.degree]
  exact (MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX σ Q.ι hdimC Q.dim_le
    (asIso (IsClosedImmersion.lift Q.ι σ hker.symm.le)) (IsClosedImmersion.lift_fac _ _ _) N).symm

/-- **A point of a smooth proper connected curve has degree one.** -/
private theorem invertibleCurveDegree_single_eq_one [IsAlgClosed k] {C : Scheme.{u}}
    (sC : C ⟶ Spec (.of k)) [IsProper sC] [Smooth sC] [ConnectedSpace C]
    (hC : topologicalKrullDim C = 1) [IsLocallyNoetherian C] [IsNormal C]
    (P : MMP.Mori.PrimeDivisor C)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor C))] :
    invertibleCurveDegree k sC hC.le
      (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor C)) = 1 := by
  haveI := isVariety_of_smooth_of_connected sC
  have hsm : IsSmoothScheme sC := (MMP.Mori.isSmoothScheme_iff sC).mpr inferInstance
  have hNV : MMP.Mori.IsNormalVariety k sC := ⟨inferInstance, inferInstance⟩
  have htop : smoothLocus sC = ⊤ := hsm
  haveI : IsIso (smoothLocus sC).ι := by rw [htop, ← Scheme.topIso_hom]; infer_instance
  have hdimU : topologicalKrullDim (smoothLocus sC).toScheme ≤ 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq (smoothLocus sC).ι
      (smoothLocus sC).ι.homeomorph.isHomeomorph, hC]
  have h := MMP.Flips.degreeOn_smoothLocus_eq_sum hNV hsm inferInstance hC hdimU
    (Finsupp.single P 1)
  rw [Finsupp.sum_single_index rfl] at h
  have h' : Divisor.degreeOn k sC (smoothLocus sC).ι hdimU (Finsupp.single P 1 : Divisor C)
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _) =
      invertibleCurveDegree k sC hC.le
        (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor C)) := by
    rw [Divisor.degreeOn, MMP.Mori.degreeOn, invertibleCurveDegree_pullback_of_isIso]
  exact h'.symm.trans h

end CurveDegree

section ProductFibres

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A closed point of a curve has coheight one. -/
private theorem coheight_eq_one_of_isClosed {Z : Scheme.{u}} [IsIntegral Z]
    (hZ : topologicalKrullDim Z = 1) {z : Z} (hz : IsClosed ({z} : Set Z)) :
    Order.coheight z = 1 := by
  have hle : Order.coheight z ≤ 1 := by
    have h := Order.coheight_le_krullDim z
    rw [Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim, hZ] at h
    exact_mod_cast h
  have hne : z ≠ genericPoint Z := fun h => not_isClosed_genericPoint hZ (h ▸ hz)
  have hsp : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes (Set.mem_univ _)
  have hle' : z ≤ genericPoint Z := Scheme.le_iff_specializes.mpr hsp
  have hlt : z < genericPoint Z :=
    lt_iff_le_not_ge.mpr ⟨hle', fun h' => hne (Scheme.le_iff_specializes.mp h' |>.antisymm hsp).eq⟩
  have h1 := Order.coheight_add_one_le hlt
  have : 1 ≤ Order.coheight z := le_trans (le_add_self) h1
  exact le_antisymm hle this

/-- The prime divisor of a closed point of a curve. -/
private noncomputable def pointDivisor {Z : Scheme.{u}} [IsIntegral Z]
    (hZ : topologicalKrullDim Z = 1) {z : Z} (hz : IsClosed ({z} : Set Z)) :
    MMP.Mori.PrimeDivisor Z :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne z (coheight_eq_one_of_isClosed hZ hz)

private theorem genericPoint_pointDivisor {Z : Scheme.{u}} [IsIntegral Z]
    (hZ : topologicalKrullDim Z = 1) {z : Z} (hz : IsClosed ({z} : Set Z)) :
    (pointDivisor hZ hz).genericPoint = z :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z _

private theorem idealSheaf_pointDivisor {Z : Scheme.{u}} [IsLocallyNoetherian Z] [IsNormal Z]
    [IsIntegral Z] (hZ : topologicalKrullDim Z = 1) {z : Z} (hz : IsClosed ({z} : Set Z)) :
    (pointDivisor hZ hz).idealSheaf =
      Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : TopologicalSpace.Closeds Z) := by
  rw [← MMP.Mori.vanishingIdeal_closure_genericPoint_eq_idealSheaf, genericPoint_pointDivisor]
  congr 1
  ext1
  exact hz.closure_eq

variable {C T : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
  [LocallyOfFiniteType sC] [LocallyOfFiniteType sT]

/-- The fibre of the first projection over a closed point is the second factor. -/
private noncomputable def fibreIsoFst {c : C} (hc : IsClosed ({c} : Set C)) :
    ((Scheme.IdealSheafData.vanishingIdeal (⟨{c}, hc⟩ : TopologicalSpace.Closeds C)).comap
      (pullback.fst sC sT)).subscheme ≅ T :=
  haveI := isIso_subschemeι_vanishingIdeal_singleton_comp sC hc
  Scheme.IdealSheafData.comapIso _ _ ≪≫ pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso sC sT _ ≪≫ asIso (pullback.snd _ sT)

/-- The fibre of the second projection over a closed point is the first factor. -/
private noncomputable def fibreIsoSnd {t : T} (ht : IsClosed ({t} : Set T)) :
    ((Scheme.IdealSheafData.vanishingIdeal (⟨{t}, ht⟩ : TopologicalSpace.Closeds T)).comap
      (pullback.snd sC sT)).subscheme ≅ C :=
  haveI := isIso_subschemeι_vanishingIdeal_singleton_comp sT ht
  Scheme.IdealSheafData.comapIso _ _ ≪≫ pullbackLeftPullbackSndIso sC sT _ ≪≫
    asIso (pullback.fst sC _)

end ProductFibres

section FibreSheaf

variable {k : Type u} [Field k] {X B Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]
  (sB : B ⟶ Spec (.of k)) [QuasiCompact sB] [IsLocallyNoetherian B] [IsNormal B]

/-- **A fibre divisor**: if the fibre of a dominant `q` over a prime divisor `P` is an integral
curve, it is a prime divisor `G` with support `q⁻¹(P)` and `𝒪_X(G) ≅ q^*𝒪_B(P)`. -/
private theorem exists_fibreDivisor [LocallyOfFiniteType sX] (hXs : IsSmoothScheme sX)
    (hXd : topologicalKrullDim X = 2) (hBs : IsSmoothScheme sB) (q : X ⟶ B) [IsDominant q]
    (P : MMP.Mori.PrimeDivisor B) (e : (P.idealSheaf.comap q).subscheme ≅ Z) [IsIntegral Z]
    (hZ : topologicalKrullDim Z = 1) :
    ∃ G : MMP.Mori.PrimeDivisor X, (G.support : Set X) = q ⁻¹' P.support ∧
      Nonempty (Divisor.divisorialSheaf (Finsupp.single G 1 : Divisor X) ≅
        (Scheme.Modules.pullback q).obj
          (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor B))) := by
  obtain ⟨G, hGI, hGs⟩ := exists_primeDivisor_fibre sX hXd q P e hZ
  have hP := isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hBs P
  have hGe := isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hXs G
  have hPc := isCartier_of_isSmoothScheme hBs (Finsupp.single P 1 : Divisor B)
  have hB : ∀ W : irreducibleComponents X, q (componentGenericPoint X W) ∉
      DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor B) := fun W =>
    map_componentGenericPoint_notMem_supp_of_isDominant' q _ W
  haveI : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace sB
  obtain ⟨e'⟩ := MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso hPc q hB
  rw [pullback_single_eq_of_idealSheaf_eq q P hP hPc hB G hGI hGe] at e'
  exact ⟨G, hGs, ⟨e'⟩⟩

end FibreSheaf

section CurvePullback

variable (k : Type u) [Field k]

/-- **Pull-backs from a curve have zero intersection number** on a surface. -/
private theorem pair_pullback_eq_zero_of_curve {X B : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    (pB : B ⟶ Spec (.of k)) [IsProper pX] [IsProper pB] (q : X ⟶ B) (hq : q ≫ pB = pX)
    [IsIntegral X] (hd : topologicalKrullDim X ≤ (2 : ℕ)) (hB : topologicalKrullDim B ≤ 1)
    (N N' : B.Modules) [SheafOfModules.IsInvertible B.presheaf B.ringCatSheaf.2 N]
    [SheafOfModules.IsInvertible B.presheaf B.ringCatSheaf.2 N'] :
    pair k pX hd ((Scheme.Modules.pullback q).obj N) ((Scheme.Modules.pullback q).obj N') = 0 := by
  haveI := isInvertible_pair N N'
  haveI : IsProper (q ≫ pB) := hq ▸ inferInstance
  haveI : IsProper q := IsProper.of_comp q pB
  haveI : IsProper (𝟙 X ≫ q) := by rw [Category.id_comp]; infer_instance
  have hIm : topologicalKrullDim (𝟙 X ≫ q).image < (2 : ℕ) := by
    have h1 : topologicalKrullDim (𝟙 X ≫ q).image ≤ topologicalKrullDim B :=
      (𝟙 X ≫ q).imageι.isEmbedding.isInducing.topologicalKrullDim_le
    refine lt_of_le_of_lt (h1.trans hB) ?_
    exact_mod_cast (by norm_num : (1 : ℕ∞) < 2)
  have h := AlgebraicGeometry.intersectionNumber_pullback_eq_zero k pX pB q hq (𝟙 X) 2 hd
    ![N, N'] hIm
  haveI := isInvertible_pair ((Scheme.Modules.pullback q).obj N)
      ((Scheme.Modules.pullback q).obj N')
  unfold pair
  rw [← h]
  exact AlgebraicGeometry.intersectionNumber_congr_family k pX (𝟙 X) 2 hd
    (funext fun j => by fin_cases j <;> rfl)

end CurvePullback

section Sections

variable {k : Type u} [Field k]

/-- The image of the generic point of an integral curve embedded in an integral surface has
coheight one: it is the generic point of a prime divisor. -/
private theorem coheight_map_genericPoint {X C : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [IsIntegral X] (hXd : topologicalKrullDim X = 2)
    (σ : C ⟶ X) [IsClosedImmersion σ] [IsIntegral C] (hC : topologicalKrullDim C = 1) :
    Order.coheight (σ (genericPoint C)) = 1 := by
  have hcl : closure ({σ (genericPoint C)} : Set X) = Set.range σ := by
    rw [← Set.image_singleton,
      σ.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous σ.continuous,
      genericPoint_closure, Set.image_univ]
  have hheight : Order.height (σ (genericPoint C)) = 1 := by
    have h1 := topologicalKrullDim_curveSubschemeAt (σ (genericPoint C))
    rw [MMP.Flips.topologicalKrullDim_subscheme, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      at h1
    change topologicalKrullDim (closure ({σ (genericPoint C)} : Set X)) = _ at h1
    rw [hcl, ← (σ.isClosedEmbedding.toIsEmbedding.toHomeomorph).isHomeomorph.topologicalKrullDim_eq,
      hC] at h1
    exact_mod_cast h1.symm
  have := height_add_coheight_eq_two sX hXd (σ (genericPoint C))
  rw [hheight, add_comm] at this
  exact eq_one_of_add_eq_two this rfl

variable [IsAlgClosed k] {C T : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))

/-- The section `c ↦ (c, t)` of the first projection through a `k`-point `t` of `T`. -/
private noncomputable def sectionAt (t : Spec (.of k) ⟶ T) (ht : t ≫ sT = 𝟙 _) :
    C ⟶ pullback sC sT :=
  pullback.lift (𝟙 C) (sC ≫ t) (by rw [Category.id_comp, Category.assoc, ht, Category.comp_id])

private theorem sectionAt_fst (t : Spec (.of k) ⟶ T) (ht : t ≫ sT = 𝟙 _) :
    sectionAt sC sT t ht ≫ pullback.fst sC sT = 𝟙 C :=
  pullback.lift_fst _ _ _

private theorem sectionAt_snd (t : Spec (.of k) ⟶ T) (ht : t ≫ sT = 𝟙 _) :
    sectionAt sC sT t ht ≫ pullback.snd sC sT = sC ≫ t :=
  pullback.lift_snd _ _ _

private theorem isClosedImmersion_sectionAt [IsSeparated sT] (t : Spec (.of k) ⟶ T)
    (ht : t ≫ sT = 𝟙 _) : IsClosedImmersion (sectionAt sC sT t ht) := by
  haveI : IsClosedImmersion (sectionAt sC sT t ht ≫ pullback.fst sC sT) := by
    rw [sectionAt_fst]; infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst sC sT)

end Sections

section FibrePairing

variable {k : Type u} [Field k] [IsAlgClosed k] {C T : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (sT : T ⟶ Spec (.of k)) [IsProper sC] [Smooth sC] [ConnectedSpace C]
  [IsProper sT] [Smooth sT] [ConnectedSpace T]

/-- **A horizontal and a vertical fibre of `C × T` meet once**: `(C × {t} · {c} × T) = 1`. -/
private theorem pair_fibre_eq_one (hC : topologicalKrullDim C = 1) [IsLocallyNoetherian C]
    [IsNormal C]
    [IsLocallyNoetherian (pullback sC sT)] [IsNormal (pullback sC sT)]
    [IsIntegral (pullback sC sT)] [IsProper (pullback.fst sC sT ≫ sC)]
    (hXs : IsSmoothScheme (pullback.fst sC sT ≫ sC))
    (hXd : topologicalKrullDim (pullback sC sT : Scheme.{u}) = 2)
    (Pc : MMP.Mori.PrimeDivisor C) (G Q : MMP.Mori.PrimeDivisor (pullback sC sT))
    (hG : Nonempty (Divisor.divisorialSheaf (Finsupp.single G 1 : Divisor (pullback sC sT)) ≅
      (Scheme.Modules.pullback (pullback.fst sC sT)).obj
        (Divisor.divisorialSheaf (Finsupp.single Pc 1 : Divisor C))))
    (t : Spec (.of k) ⟶ T) (ht : t ≫ sT = 𝟙 _) [IsIntegral C]
    (hQ : Q.genericPoint = sectionAt sC sT t ht (genericPoint C)) :
    dpair k (pullback.fst sC sT ≫ sC) hXs hXd (Finsupp.single Q 1) (Finsupp.single G 1) = 1 := by
  haveI : CompactSpace (pullback sC sT : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst sC sT ≫ sC)
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  have hCs : IsSmoothScheme sC := (MMP.Mori.isSmoothScheme_iff sC).mpr inferInstance
  haveI hPcinv : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single Pc 1 : Divisor C)) :=
    (isCartier_of_isSmoothScheme hCs _).isInvertibleModule_divisorialSheaf
  have hc := isCartier_of_isSmoothScheme hXs
  haveI : SheafOfModules.IsInvertible (pullback sC sT).presheaf (pullback sC sT).ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single G 1 : Divisor (pullback sC sT))) :=
    (hc _).isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible (pullback sC sT).presheaf (pullback sC sT).ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single Q 1 : Divisor (pullback sC sT))) :=
    (hc _).isInvertibleModule_divisorialSheaf
  obtain ⟨eG⟩ := hG
  haveI := isClosedImmersion_sectionAt sC sT t ht
  haveI : IsProper (sectionAt sC sT t ht ≫ pullback.fst sC sT ≫ sC) := by
    rw [← Category.assoc, sectionAt_fst, Category.id_comp]; infer_instance
  rw [dpair_eq, pair_congr_right k _ _ _ eG,
    pair_divisorialSheaf_eq_sum k _ _ hXs hXd, Finsupp.support_single_ne_zero _ one_ne_zero,
    Finset.sum_singleton, Finsupp.single_eq_same, one_mul,
    degree_curve_eq_degreeOn k _ (sectionAt sC sT t ht) hC.le (curveOf k _ hXd Q) hQ,
    MMP.Mori.degreeOn]
  rw [MMP.Threefold.Resolution.invertibleCurveDegree_congr k
    (by rw [← Category.assoc, sectionAt_fst, Category.id_comp] :
      sectionAt sC sT t ht ≫ pullback.fst sC sT ≫ sC = sC) hC.le]
  have e : (Scheme.Modules.pullback (sectionAt sC sT t ht)).obj
      ((Scheme.Modules.pullback (pullback.fst sC sT)).obj
        (Divisor.divisorialSheaf (Finsupp.single Pc 1 : Divisor C))) ≅
      Divisor.divisorialSheaf (Finsupp.single Pc 1 : Divisor C) :=
    ((Scheme.Modules.pullbackComp (sectionAt sC sT t ht) (pullback.fst sC sT)).app _) ≪≫
      eqToIso (by rw [sectionAt_fst]; rfl) ≪≫ (Scheme.Modules.pullbackId C).app _
  rw [invertibleCurveDegree_eq_of_iso k sC hC.le e]
  exact invertibleCurveDegree_single_eq_one k sC hC Pc

end FibrePairing

section Helpers

variable (k : Type u) [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsProper sY]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y] [CompactSpace Y]
  (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)

/-- The pairing with a fixed invertible sheaf, as an additive map on divisors. -/
private noncomputable def pairWith (N : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N] :
    Divisor Y →+ ℤ :=
  AddMonoidHom.mk' (fun D =>
    haveI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 D.divisorialSheaf :=
      (isCartier_of_isSmoothScheme hYs D).isInvertibleModule_divisorialSheaf
    pair k sY (by rw [hYd]; rfl) D.divisorialSheaf N)
    (fun D D' => pair_divisorialSheaf_add k sY (by rw [hYd]; rfl)
      (isCartier_of_isSmoothScheme hYs D) (isCartier_of_isSmoothScheme hYs D') N)

private theorem pairWith_apply (N : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N]
    (D : Divisor Y) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 D.divisorialSheaf] :
    pairWith k sY hYs hYd N D = pair k sY (by rw [hYd]; rfl) D.divisorialSheaf N := rfl

private theorem pairWith_eq_sum (N : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N]
    (D : Divisor Y) :
    pairWith k sY hYs hYd N D = ∑ P ∈ D.support, D P * (curveOf k sY hYd P).degree k N :=
  pair_divisorialSheaf_eq_sum k sY (by rw [hYd]; rfl) hYs hYd D N

/-- **A divisor contracted by `p` is orthogonal to pull-backs**. -/
private theorem pairWith_pullback_eq_zero {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsSeparated sX]
    [LocallyOfFiniteType sX] (p : Y ⟶ X) (hp : p ≫ sX = sY) (D : Divisor Y)
    (hD : ∀ P ∈ D.support, ∀ y ∈ closure ({P.genericPoint} : Set Y), p y = p P.genericPoint)
    (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    pairWith k sY hYs hYd ((Scheme.Modules.pullback p).obj N) D = 0 := by
  rw [pairWith_eq_sum]
  refine Finset.sum_eq_zero fun P hP => ?_
  rw [ProperCurve.degree_pullback_eq_zero_of_isContractedBy p hp (curveOf k sY hYd P) (hD P hP) N,
    mul_zero]

include hYs in
/-- `pairWith_pullback_eq_zero` as a pairing of sheaves: `(𝒪_Y(D) · p^*N) = 0` for a divisor
`D` contracted by `p`. -/
private theorem pair_divisorialSheaf_pullback_eq_zero {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsSeparated sX] [LocallyOfFiniteType sX] (p : Y ⟶ X) (hp : p ≫ sX = sY) (D : Divisor Y)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 D.divisorialSheaf]
    (hD : ∀ P ∈ D.support, ∀ y ∈ closure ({P.genericPoint} : Set Y), p y = p P.genericPoint)
    (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    pair k sY (by rw [hYd]; rfl) D.divisorialSheaf ((Scheme.Modules.pullback p).obj N) = 0 :=
  pairWith_pullback_eq_zero k sY hYs hYd sX p hp D hD N

include hYs in
/-- The degree of the divisorial sheaf of a prime divisor on a different prime curve is
nonnegative. -/
private theorem degree_single_nonneg (P R : MMP.Mori.PrimeDivisor Y) (hPR : R ≠ P)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y))] :
    0 ≤ (curveOf k sY hYd R).degree k (Divisor.divisorialSheaf
        (Finsupp.single P 1 : Divisor Y)) := by
  have h := intersectionNumber_single_eq_finrank (k := k) hYs R P hPR (curveOf k sY hYd R) rfl
  rw [MMP.Mori.QDivisor.intersectionNumber_toQDivisor k sY _ _ _
    (isCartier_of_isSmoothScheme hYs _)] at h
  have h0 : (0 : ℚ) ≤ ((curveOf k sY hYd R).degree k
      (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y)) : ℚ) := by
    have h2 : ((curveOf k sY hYd R).degree k
        (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y)) : ℚ) = _ := h
    rw [h2]; positivity
  exact_mod_cast h0

/-- **Nefness of a pulled-back ample sheaf**: `deg_C (h^*H) ≥ 0`, and if it is positive the image
of `C` is a proper curve `L` with `0 < deg_L H ≤ deg_C (h^*H)`. -/
private theorem degree_pullback_ample {V : Scheme.{u}} (sV : V ⟶ Spec (.of k)) [IsSeparated sV]
    [LocallyOfFiniteType sV] (h : Y ⟶ V) (hh : h ≫ sV = sY) (C : ProperCurve sY)
    (H : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 H]
    (hH : Scheme.Modules.IsAmple V H) :
    0 ≤ C.degree k ((Scheme.Modules.pullback h).obj H) ∧
      (0 < C.degree k ((Scheme.Modules.pullback h).obj H) →
        ∃ L : ProperCurve sV, L.point = h C.point ∧ 0 < L.degree k H ∧
          L.degree k H ≤ C.degree k ((Scheme.Modules.pullback h).obj H)) := by
  have hpos : ∀ L : ProperCurve sV, 0 < L.degree k H := by
    intro L
    have hcurve : AlgebraicGeometry.IsCurve k (L.ι ≫ sV) := by
      have hp : IsProper (L.ι ≫ sV) := inferInstance
      haveI : AlgebraicGeometry.IsVariety k (L.ι ≫ sV) :=
        { toIsIntegral := inferInstance, toIsSeparated := hp.toIsSeparated,
          toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
      exact ⟨L.dim_eq⟩
    exact invertibleCurveDegree_pos_of_isAmple_of_isCurve k (L.ι ≫ sV) L.dim_le _
      (isAmple_pullback_of_isFinite L.ι H hH)
  rw [ProperCurve.degree_pullback h hh C H]
  split_ifs with hL
  · have h1 := hpos ⟨h C.point, hL⟩
    refine ⟨by positivity, fun h2 => ⟨⟨h C.point, hL⟩, rfl, h1, ?_⟩⟩
    have hr : 0 < (residueFieldDegree h C.point : ℤ) := by
      by_contra hr
      have : (residueFieldDegree h C.point : ℤ) = 0 := by omega
      rw [this, zero_mul] at h2
      exact lt_irrefl _ h2
    nlinarith
  · exact ⟨le_rfl, fun h2 => absurd h2 (lt_irrefl _)⟩

end Helpers

section RationalImage

open TopologicalSpace

variable {k : Type u} [Field k]

/-- A surjective morphism, locally of finite type, of integral schemes inducing an isomorphism of
function fields is a birational morphism. -/
private theorem isBirationalMorphism_of_bijective_functionFieldMap' {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] (μ : X ⟶ T) [Surjective μ] [LocallyOfFiniteType μ]
    (hbij : Function.Bijective (functionFieldMap μ)) : IsBirationalMorphism μ := by
  let e := T.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant μ).symm)
  haveI : IsIso (e.hom ≫ μ.stalkMap (genericPoint X)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  haveI : IsIso (μ.stalkMap (genericPoint X)) := IsIso.of_isIso_comp_left e.hom _
  have hbir : AlgebraicGeometry.IsBirational μ := isBirational_of_isIso_stalkMap_genericPoint μ
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents T) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational μ hbir (Or.inl ⟨inferInstance, inferInstance⟩)
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE μ U V hU.nonempty hV.nonempty hUV hiso

/-- A birational morphism followed by an isomorphism is birational. -/
private theorem isBirationalMorphism_comp_isIso {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (f : X ⟶ Y) (hf : IsBirationalMorphism f) [Surjective f]
    [LocallyOfFiniteType f] (e : Y ⟶ Z) [IsIso e] : IsBirationalMorphism (f ≫ e) := by
  obtain ⟨e₀, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have he' : IsOpenImmersion e₀.toPartialMap.hom := by
    change IsOpenImmersion (e₀.iso.hom ≫ e₀.target.ι)
    infer_instance
  have hι : IsOpenImmersion (W.ι ≫ f) := by
    have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
      change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
      simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
    rw [this, ← h]
    infer_instance
  have : IsOpenImmersion (W.ι ≫ f ≫ e) := by rw [← Category.assoc]; infer_instance
  exact isBirationalMorphism_of_bijective_functionFieldMap' _
    (functionFieldMap_bijective_of_isOpenImmersion (f ≫ e) W hW.nonempty)

private theorem isIntegral_curveSubschemeAt {X : Scheme.{u}} (x : X) :
    IsIntegral (curveSubschemeAt x) :=
  haveI : IrreducibleSpace (curveSubschemeAt x) :=
    Subtype.irreducibleSpace isIrreducible_singleton.closure
  haveI := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal
    (Closeds.closure ({x} : Set X))
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- **A curve dominated by `ℙ¹` is rational.** If `ψ : ℙ¹_k ⟶ V` is a `k`-morphism into a proper
`k`-scheme whose generic point maps to the generic point of a proper curve `L ⊆ V`, then `L`
(with its reduced structure) is a rational curve. -/
private theorem isRationalCurve_of_projectiveLine [IsAlgClosed k] {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) [IsProper sV] (L : ProperCurve sV) (ψ : projectiveLine k ⟶ V)
    (hψ : ψ ≫ sV = projectiveLine k ↘ Spec (.of k))
    (hη : ψ (genericPoint (projectiveLine k)) = L.point) :
    IsRationalCurve sV (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        ({L.point} : Set V))) := by
  haveI := projectiveLine_isIntegral k
  haveI hLi := isIntegral_curveSubschemeAt L.point
  have hrange : closure (Set.range ψ) = closure ({L.point} : Set V) := by
    apply le_antisymm
    · refine closure_minimal ?_ isClosed_closure
      rintro _ ⟨y, rfl⟩
      rw [← hη, ← specializes_iff_mem_closure]
      exact ((genericPoint_spec (projectiveLine k)).specializes (Set.mem_univ y)).map
        ψ.continuous
    · exact closure_mono (Set.singleton_subset_iff.mpr ⟨_, hη⟩)
  have hker : ψ.ker = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
      ({L.point} : Set V)) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    exact Closeds.ext hrange
  refine ⟨⟨hLi, L.dim_eq⟩, L.isProperCurve.isProper, ?_⟩
  rw [← hker]
  haveI : IsIntegral ψ.ker.subscheme := by rw [hker]; exact hLi
  haveI : IsProper (ψ.ker.subschemeι ≫ sV) := by rw [hker]; exact L.isProperCurve.isProper
  haveI : AlgebraicGeometry.IsProperVariety k (ψ.ker.subschemeι ≫ sV) :=
    (AlgebraicGeometry.isProperVariety_iff k _).2 ⟨{}, inferInstance⟩
  have hf : ψ.toImage ≫ ψ.ker.subschemeι ≫ sV = projectiveLine k ↘ Spec (.of k) := by
    rw [← Category.assoc]
    exact (congrArg (· ≫ sV) ψ.toImage_imageι).trans hψ
  have hC := isRationalCurve_projectiveLine k
  have hnc : ¬ (ψ.toImage.base '' ((⊥ : (projectiveLine k).IdealSheafData).support :
      Set (projectiveLine k))).Subsingleton := by
    intro hsub
    have h1 : Set.range ψ.base ⊆ ψ.ker.subschemeι.base '' (ψ.toImage.base ''
        ((⊥ : (projectiveLine k).IdealSheafData).support : Set (projectiveLine k))) := by
      rintro _ ⟨y, rfl⟩
      refine ⟨ψ.toImage y, ⟨y, by simp, rfl⟩, ?_⟩
      rw [← Scheme.Hom.comp_apply]
      exact congrArg (fun g : projectiveLine k ⟶ V => g.base y) ψ.toImage_imageι
    have hs : (Set.range ψ.base).Subsingleton := (hsub.image _).anti h1
    haveI : IsProper (ψ ≫ sV) := by rw [hψ]; infer_instance
    haveI := IsProper.of_comp ψ sV
    have hcl : IsClosed (Set.range ψ.base) := ψ.isClosedMap.isClosed_range
    have hsx : closure ({L.point} : Set V) ⊆ {L.point} := by
      rw [← hrange, hcl.closure_eq]
      intro z hz
      exact hs hz ⟨_, hη⟩
    haveI : Subsingleton (curveSubschemeAt L.point) := ⟨fun a b => by
      apply (curveSubschemeAtι L.point).isClosedEmbedding.injective
      have ha : (curveSubschemeAtι L.point) a ∈ closure ({L.point} : Set V) := by
        have := Scheme.IdealSheafData.range_subschemeι
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({L.point} : Set V)))
        rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
        exact (Set.ext_iff.mp this _).mp ⟨a, rfl⟩
      have hb : (curveSubschemeAtι L.point) b ∈ closure ({L.point} : Set V) := by
        have := Scheme.IdealSheafData.range_subschemeι
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({L.point} : Set V)))
        rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
        exact (Set.ext_iff.mp this _).mp ⟨b, rfl⟩
      exact (hsx ha).trans (hsx hb).symm⟩
    exact not_subsingleton_of_topologicalKrullDim_eq_one L.dim_eq inferInstance
  have hK := IsRationalCurve.ker_subschemeι_comp hf hC hnc
  have hK0 : ((⊥ : (projectiveLine k).IdealSheafData).subschemeι ≫ ψ.toImage).ker = ⊥ := by
    haveI : IsReduced ψ.ker.subscheme := inferInstance
    haveI : QuasiCompact ψ := by
      haveI : IsProper (ψ ≫ sV) := by rw [hψ]; infer_instance
      haveI := IsProper.of_comp ψ sV
      infer_instance
    haveI : IsDominant ψ.toImage := inferInstance
    haveI : Surjective (⊥ : (projectiveLine k).IdealSheafData).subschemeι := inferInstance
    haveI : IsDominant (⊥ : (projectiveLine k).IdealSheafData).subschemeι := inferInstance
    haveI : IsDominant ((⊥ : (projectiveLine k).IdealSheafData).subschemeι ≫ ψ.toImage) :=
      inferInstance
    haveI := IsSchemeTheoreticallyDominant.of_isDominant
      ((⊥ : (projectiveLine k).IdealSheafData).subschemeι ≫ ψ.toImage)
    exact Scheme.Hom.ker_eq_bot _
  rw [hK0] at hK
  obtain ⟨-, -, ν, hν, hfin, hbir⟩ := hK
  haveI : Nonempty (⊥ : ψ.ker.subscheme.IdealSheafData).subscheme :=
    ⟨(inv (⊥ : ψ.ker.subscheme.IdealSheafData).subschemeι) (Classical.arbitrary _)⟩
  haveI : IsIntegral (⊥ : ψ.ker.subscheme.IdealSheafData).subscheme :=
    isIntegral_of_isOpenImmersion (⊥ : ψ.ker.subscheme.IdealSheafData).subschemeι
  haveI := hfin
  haveI : IsDominant ν := hbir.isDominant
  haveI : Surjective ν := ⟨by
    rw [← Set.range_eq_univ]
    have hcl : IsClosed (Set.range ν.base) := ν.isClosedMap.isClosed_range
    rw [← hcl.closure_eq]
    exact ν.denseRange.closure_range⟩
  refine ⟨ν ≫ (⊥ : ψ.ker.subscheme.IdealSheafData).subschemeι, ?_, inferInstance,
    isBirationalMorphism_comp_isIso ν hbir _⟩
  simpa only [Category.assoc] using hν

end RationalImage

section RationalExceptional

variable (k : Type u) [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsProper sY]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y] [CompactSpace Y]
  (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)

/-- An effective divisor pairs nonnegatively with a pulled-back ample sheaf. -/
private theorem pairWith_pullback_ample_nonneg {V : Scheme.{u}} (sV : V ⟶ Spec (.of k))
    [IsProper sV]
    (h : Y ⟶ V) (hh : h ≫ sV = sY) (H : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 H]
    (hH : Scheme.Modules.IsAmple V H) (D : Divisor Y) (hD : 0 ≤ D) :
    0 ≤ pairWith k sY hYs hYd ((Scheme.Modules.pullback h).obj H) D := by
  rw [pairWith_eq_sum]
  exact Finset.sum_nonneg fun P _ => mul_nonneg (hD P)
    (degree_pullback_ample k sY sV h hh (curveOf k sY hYd P) H hH).1

/-- **Rational curves from parametrized exceptional divisors.** If every component of the
effective divisor `D` is dominated by `ℙ¹_k` and `D` pairs positively with `h^*H` for an ample
`H`, then `V` contains a rational curve `L` with `0 < (H · L) ≤ (D · h^*H)`. -/
private theorem exists_isRationalCurve_of_pairWith_pos [IsAlgClosed k] {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) [IsProper sV]
    (h : Y ⟶ V) (hh : h ≫ sV = sY) (H : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 H]
    (hH : Scheme.Modules.IsAmple V H) (D : Divisor Y) (hD : 0 ≤ D)
    (hparam : ∀ P ∈ D.support, ∃ g : projectiveLine k ⟶ Y,
      g ≫ sY = projectiveLine k ↘ Spec (.of k) ∧
        g (genericPoint (projectiveLine k)) = P.genericPoint)
    (hpos : 0 < pairWith k sY hYs hYd ((Scheme.Modules.pullback h).obj H) D) :
    ∃ (L : V.IdealSheafData) (hL : IsRationalCurve sV L),
      haveI := hL.2.1
      0 < degreeOn k sV L.subschemeι hL.1.2.le H ∧
        degreeOn k sV L.subschemeι hL.1.2.le H ≤
          pairWith k sY hYs hYd ((Scheme.Modules.pullback h).obj H) D := by
  have hnn : ∀ P, 0 ≤ (curveOf k sY hYd P).degree k ((Scheme.Modules.pullback h).obj H) :=
    fun P => (degree_pullback_ample k sY sV h hh (curveOf k sY hYd P) H hH).1
  have hsum := pairWith_eq_sum k sY hYs hYd ((Scheme.Modules.pullback h).obj H) D
  rw [hsum] at hpos ⊢
  obtain ⟨P, hP, hPpos⟩ := Finset.exists_lt_of_sum_lt (s := D.support) (f := fun _ => (0 : ℤ))
    (by simpa using hpos)
  have hDP : 0 < D P := lt_of_le_of_ne (hD P) (Ne.symm (Finsupp.mem_support_iff.mp hP))
  have hdeg : 0 < (curveOf k sY hYd P).degree k ((Scheme.Modules.pullback h).obj H) :=
    pos_of_mul_pos_right hPpos hDP.le
  obtain ⟨L, hLpt, hL0, hL1⟩ :=
    (degree_pullback_ample k sY sV h hh (curveOf k sY hYd P) H hH).2 hdeg
  obtain ⟨g, hg, hgη⟩ := hparam P hP
  have hrat := isRationalCurve_of_projectiveLine sV L (g ≫ h)
    (by rw [Category.assoc, hh, hg]) (by rw [Scheme.Hom.comp_apply, hgη, hLpt]; rfl)
  refine ⟨_, hrat, hL0, ?_⟩
  calc L.degree k H ≤ (curveOf k sY hYd P).degree k ((Scheme.Modules.pullback h).obj H) := hL1
    _ ≤ D P * (curveOf k sY hYd P).degree k ((Scheme.Modules.pullback h).obj H) :=
        le_mul_of_one_le_left (hnn P) hDP
    _ ≤ _ := Finset.single_le_sum (f := fun P =>
          D P * (curveOf k sY hYd P).degree k ((Scheme.Modules.pullback h).obj H))
          (fun Q _ => mul_nonneg (hD Q) (hnn Q)) hP

end RationalExceptional

section SelfIntersection

variable (k : Type u) [Field k]

/-- **The pull-back of an ample sheaf along a generically finite map of surfaces has positive
self-intersection** ([Stacks, Tag 0BET] and [Stacks, Tag 0BEV]). -/
private theorem pair_pullback_ample_pos {Y V : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (sV : V ⟶ Spec (.of k)) [IsProper sY] [IsProper sV] (h : Y ⟶ V) (hh : h ≫ sV = sY)
    [IsIntegral Y] (hY : topologicalKrullDim Y = 2) (hdY : topologicalKrullDim Y ≤ (2 : ℕ))
    (hIm : topologicalKrullDim (closure (Set.range h.base)) = 2) (H : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 H]
    (hH : Scheme.Modules.IsAmple V H) :
    0 < pair k sY hdY ((Scheme.Modules.pullback h).obj H) ((Scheme.Modules.pullback h).obj H) := by
  haveI : IsProper (h ≫ sV) := hh ▸ inferInstance
  haveI : IsProper h := IsProper.of_comp h sV
  haveI : IsProper (𝟙 Y ≫ h) := by rw [Category.id_comp]; infer_instance
  haveI : IsIntegral (𝟙 Y ≫ h).image := Stacks.Chow.isIntegral_image (𝟙 Y ≫ h)
  haveI : IsProper (𝟙 Y ≫ h).toImage := Stacks.Chow.isProper_toImage (𝟙 Y ≫ h)
  have hY' : topologicalKrullDim Y = ((2 : ℕ) : WithBot ℕ∞) := hY
  have hIm' : topologicalKrullDim (𝟙 Y ≫ h).image = ((2 : ℕ) : WithBot ℕ∞) := by
    change topologicalKrullDim (𝟙 Y ≫ h).ker.subscheme = _
    rw [MMP.Flips.topologicalKrullDim_subscheme, Scheme.Hom.support_ker, Category.id_comp]
    exact hIm
  haveI := isInvertible_pair H H
  have hpull := AlgebraicGeometry.intersectionNumber_pullback_eq_degreeOver_mul k sY sV h hh
      (𝟙 Y) 2 hY'
    ![H, H] hIm'
  have hfin := MMP.Mori.finite_functionField_of_topologicalKrullDim_eq
    ((𝟙 Y ≫ h).imageι ≫ sV) (𝟙 Y ≫ h).toImage (hY.trans hIm'.symm)
  unfold MMP.Mori.functionFieldMapAlgebra at hfin
  rw [← MMP.Mori.dominantFunctionFieldMap_eq_functionFieldMap] at hfin
  have hdeg := degreeOver_pos (𝟙 Y ≫ h).toImage hfin
  have hpos := intersectionNumber_pos k sV (𝟙 Y ≫ h).imageι 2 hIm' ![H, H]
    (fun j => by fin_cases j <;> exact hH)
  haveI := isInvertible_pair ((Scheme.Modules.pullback h).obj H)
    ((Scheme.Modules.pullback h).obj H)
  have : pair k sY hdY ((Scheme.Modules.pullback h).obj H) ((Scheme.Modules.pullback h).obj H) =
      intersectionNumber k sY (𝟙 Y) 2 hY'.le
        (fun j => (Scheme.Modules.pullback h).obj (![H, H] j)) :=
    AlgebraicGeometry.intersectionNumber_congr_family k sY (𝟙 Y) 2 hdY
      (funext fun j => by fin_cases j <;> rfl)
  rw [this, hpull]
  exact mul_pos (by exact_mod_cast hdeg) hpos

end SelfIntersection

section ProductDivisors

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A nonempty open subset of a scheme locally of finite type over an algebraically closed field
contains a `k`-point. -/
private theorem exists_point_mem_of_isOpen {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f]
    {W : Set X} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ t : Spec (.of k) ⟶ X, t ≫ f = 𝟙 _ ∧ ∀ a, t a ∈ W := by
  haveI := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hxW, hxc⟩ := nonempty_inter_closedPoints hne hW.isLocallyClosed
  have hxc' : IsClosed ({x} : Set X) := hxc
  exact ⟨pointOfClosedPoint f x hxc', pointOfClosedPoint_comp f x hxc', fun a => by
    rw [pointOfClosedPoint_apply]; exact hxW⟩

/-- Two points of coheight one, one specializing to the other, are equal. -/
private theorem eq_of_specializes_of_coheight_eq_one {X : Scheme.{u}} {x y : X} (h : x ⤳ y)
    (hx : Order.coheight x = 1) (hy : Order.coheight y = 1) : x = y := by
  by_contra hne
  have hle : y ≤ x := Scheme.le_iff_specializes.mpr h
  have hlt : y < x := lt_iff_le_not_ge.mpr
    ⟨hle, fun h' => hne (h.antisymm (Scheme.le_iff_specializes.mp h')).eq⟩
  have h1 := Order.coheight_add_one_le hlt
  rw [hx, hy] at h1
  exact absurd h1 (by decide)

private theorem mem_support_pointDivisor {Z : Scheme.{u}} [IsIntegral Z]
    (hZ : topologicalKrullDim Z = 1)
    {z : Z} (hz : IsClosed ({z} : Set Z)) (x : Z) :
    x ∈ (pointDivisor hZ hz).support ↔ x = z := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  change x ∈ closure {(pointDivisor hZ hz).genericPoint} ↔ _
  rw [genericPoint_pointDivisor, hz.closure_eq, Set.mem_singleton_iff]

/-- A `k`-point of a separated `k`-scheme is a closed point. -/
private theorem isClosed_singleton_of_section {T : Scheme.{u}} (sT : T ⟶ Spec (.of k))
    [IsSeparated sT]
    (t : Spec (.of k) ⟶ T) (ht : t ≫ sT = 𝟙 _) (a : Spec (.of k)) :
    IsClosed ({t a} : Set T) := by
  haveI : IsClosedImmersion (t ≫ sT) := by rw [ht]; infer_instance
  haveI : IsClosedImmersion t := IsClosedImmersion.of_comp t sT
  have hr : Set.range t.base = {t a} := by
    ext y
    constructor
    · rintro ⟨b, rfl⟩
      rw [Set.mem_singleton_iff, Subsingleton.elim b a]
    · rintro rfl; exact ⟨a, rfl⟩
  rw [← hr]
  exact t.isClosedEmbedding.isClosed_range

variable {C T : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
  [IsProper sC] [Smooth sC] [ConnectedSpace C] [IsProper sT] [Smooth sT] [ConnectedSpace T]
  [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] [IsIntegral T] [IsLocallyNoetherian T]
  [IsNormal T] [IsLocallyNoetherian (pullback sC sT)] [IsNormal (pullback sC sT)]

/-- **The vertical fibre `{c} × T`** is a prime divisor `G` with `𝒪(G) ≅ pr₁^*𝒪_C(c)`. -/
private theorem exists_fibreDivisor_fst (hC : topologicalKrullDim C = 1)
    (hT : topologicalKrullDim T = 1)
    {c : C} (hc : IsClosed ({c} : Set C)) :
    ∃ (G : MMP.Mori.PrimeDivisor (pullback sC sT)),
      (∀ x, x ∈ G.support ↔ pullback.fst sC sT x = c) ∧
      Nonempty (Divisor.divisorialSheaf (Finsupp.single G 1 : Divisor (pullback sC sT)) ≅
        (Scheme.Modules.pullback (pullback.fst sC sT)).obj
          (Divisor.divisorialSheaf (Finsupp.single (pointDivisor hC hc) 1 : Divisor C))) := by
  haveI := isVariety_of_smooth_of_connected sC
  haveI := isVariety_of_smooth_of_connected sT
  obtain ⟨hXv, hXs, hXd, -⟩ := product_facts sC sT hC hT
  haveI : AlgebraicGeometry.IsVariety k (pullback.fst sC sT ≫ sC) := hXv
  haveI : IsIntegral (pullback sC sT) := hXv.toIsIntegral
  have hCs : IsSmoothScheme sC := (MMP.Mori.isSmoothScheme_iff _).mpr inferInstance
  haveI : CompactSpace (pullback sC sT : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst sC sT ≫ sC)
  haveI : Surjective sT := ⟨fun y => ⟨Classical.arbitrary T, Subsingleton.elim _ _⟩⟩
  haveI : IsDominant (pullback.fst sC sT) := inferInstance
  have e := eqToIso (congrArg (fun I => (I.comap (pullback.fst sC sT)).subscheme)
    (idealSheaf_pointDivisor hC hc)) ≪≫ fibreIsoFst sC sT hc
  obtain ⟨G, hG, hiso⟩ := exists_fibreDivisor (pullback.fst sC sT ≫ sC) sC hXs hXd hCs
    (pullback.fst sC sT) (pointDivisor hC hc) e hT
  refine ⟨G, fun x => ?_, hiso⟩
  rw [hG, Set.mem_preimage, mem_support_pointDivisor]

/-- **The horizontal fibre `C × {t}`** over a `k`-point `t` is a prime divisor `Φ` with
`𝒪(Φ) ≅ pr₂^*𝒪_T(t)`, whose generic point is the image of that of `C` under the section. -/
private theorem exists_fibreDivisor_snd (hC : topologicalKrullDim C = 1)
    (hT : topologicalKrullDim T = 1)
    (t : Spec (.of k) ⟶ T) (ht : t ≫ sT = 𝟙 _) :
    ∃ (Φ : MMP.Mori.PrimeDivisor (pullback sC sT)),
      (∀ x, x ∈ Φ.support ↔ pullback.snd sC sT x = t (IsLocalRing.closedPoint k)) ∧
      Nonempty (Divisor.divisorialSheaf (Finsupp.single Φ 1 : Divisor (pullback sC sT)) ≅
        (Scheme.Modules.pullback (pullback.snd sC sT)).obj
          (Divisor.divisorialSheaf (Finsupp.single (pointDivisor hT
            (isClosed_singleton_of_section sT t ht (IsLocalRing.closedPoint k))) 1 : Divisor T))) ∧
      Φ.genericPoint = sectionAt sC sT t ht (genericPoint C) := by
  haveI := isVariety_of_smooth_of_connected sC
  haveI := isVariety_of_smooth_of_connected sT
  obtain ⟨hXv, hXs, hXd, -⟩ := product_facts sC sT hC hT
  haveI : AlgebraicGeometry.IsVariety k (pullback.fst sC sT ≫ sC) := hXv
  haveI : IsIntegral (pullback sC sT) := hXv.toIsIntegral
  have hTs : IsSmoothScheme sT := (MMP.Mori.isSmoothScheme_iff _).mpr inferInstance
  haveI : CompactSpace (pullback sC sT : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst sC sT ≫ sC)
  haveI : Surjective sC := ⟨fun y => ⟨Classical.arbitrary C, Subsingleton.elim _ _⟩⟩
  haveI : IsDominant (pullback.snd sC sT) := inferInstance
  set hτ := isClosed_singleton_of_section sT t ht (IsLocalRing.closedPoint k)
  have e := eqToIso (congrArg (fun I => (I.comap (pullback.snd sC sT)).subscheme)
    (idealSheaf_pointDivisor hT hτ)) ≪≫ fibreIsoSnd sC sT hτ
  obtain ⟨Φ, hΦ, hiso⟩ := exists_fibreDivisor (pullback.fst sC sT ≫ sC) sT hXs hXd hTs
    (pullback.snd sC sT) (pointDivisor hT hτ) e hC
  have hmem : ∀ x, x ∈ Φ.support ↔ pullback.snd sC sT x = t (IsLocalRing.closedPoint k) :=
    fun x => by
      rw [hΦ, Set.mem_preimage, mem_support_pointDivisor]
  refine ⟨Φ, hmem, hiso, ?_⟩
  haveI := isClosedImmersion_sectionAt sC sT t ht
  have hσ : sectionAt sC sT t ht (genericPoint C) ∈ Φ.support := by
    rw [hmem, ← Scheme.Hom.comp_apply, sectionAt_snd, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hσ
  exact eq_of_specializes_of_coheight_eq_one hσ Φ.coheight_genericPoint
    (coheight_map_genericPoint (pullback.fst sC sT ≫ sC) hXd (sectionAt sC sT t ht) hC)

end ProductDivisors

section RestrictProduct

variable {S C T : Scheme.{u}} (sC : C ⟶ S) (sT : T ⟶ S) (U : T.Opens)

/-- The restriction of `C ×_S T` over an open `U ⊆ T` is `C ×_S U`. -/
private noncomputable def restrictProductIso :
    ((pullback.snd sC sT) ⁻¹ᵁ U).toScheme ≅ pullback sC (U.ι ≫ sT) :=
  (pullbackRestrictIsoRestrict (pullback.snd sC sT) U).symm ≪≫
    pullbackLeftPullbackSndIso sC sT U.ι

@[reassoc]
private theorem restrictProductIso_hom_fst :
    (restrictProductIso sC sT U).hom ≫ pullback.fst sC (U.ι ≫ sT) =
      ((pullback.snd sC sT) ⁻¹ᵁ U).ι ≫ pullback.fst sC sT := by
  simp [restrictProductIso, pullbackRestrictIsoRestrict_inv_fst_assoc]

@[reassoc]
private theorem restrictProductIso_hom_snd :
    (restrictProductIso sC sT U).hom ≫ pullback.snd sC (U.ι ≫ sT) ≫ U.ι =
      ((pullback.snd sC sT) ⁻¹ᵁ U).ι ≫ pullback.snd sC sT := by
  simp [restrictProductIso, ← pullback.condition, pullbackRestrictIsoRestrict_inv_fst_assoc]

end RestrictProduct

section Resolution

variable {k : Type u} [Field k] [IsAlgClosed k] {C T V : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (sT : T ⟶ Spec (.of k)) (sV : V ⟶ Spec (.of k))
  [IsProper sC] [Smooth sC] [ConnectedSpace C] [IsProper sT] [Smooth sT] [ConnectedSpace T]
  [IsProper sV]

/-- **Resolving `C × T ⇢ V` by point blow-ups** ([Stacks, Tag 0C5H]): the rational map defined
on `C × U` is resolved by a chain of point blow-ups `p : Y ⟶ C × T` at closed points outside
`C × U`, with the chain data of the exceptional curves. -/
private theorem exists_resolution [IsLocallyNoetherian (pullback sC sT)] [IsNormal (pullback sC sT)]
    (hC : topologicalKrullDim C = 1) (hT : topologicalKrullDim T = 1)
    (U : T.Opens) (hU : (U : Set T).Nonempty)
    (φ : pullback sC (U.ι ≫ sT) ⟶ V)
    (hφ : φ ≫ sV = pullback.snd sC (U.ι ≫ sT) ≫ U.ι ≫ sT) :
    ∃ (Y : Scheme.{u}) (sY : Y ⟶ Spec (.of k)) (p : Y ⟶ pullback sC sT) (h : Y ⟶ V)
      (T₀ : Set (pullback sC sT : Scheme.{u}))
      (_ : ∀ x ∈ T₀, IsClosed ({x} : Set (pullback sC sT : Scheme.{u})))
      (_ : ∀ x ∈ T₀, pullback.snd sC sT x ∉ U)
      (hY : MMP.Mori.IsVariety k sY) (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
      (hYp : MMP.Mori.IsProjectiveVariety k sY) (_ : IsProper p) (_ : Surjective p)
      (_ : IsIso (p ∣_ ((pullback.snd sC sT) ⁻¹ᵁ U))),
      p ≫ pullback.fst sC sT ≫ sC = sY ∧ h ≫ sV = sY ∧
      (p ⁻¹ᵁ ((pullback.snd sC sT) ⁻¹ᵁ U)).ι ≫ h =
        (p ∣_ ((pullback.snd sC sT) ⁻¹ᵁ U)) ≫ (restrictProductIso sC sT U).hom ≫ φ ∧
      haveI : AlgebraicGeometry.IsProjectiveVariety k sY := hYp
      haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
      haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
      Nonempty (ChainData T₀ p sY hYs hYd) := by
  haveI := isVariety_of_smooth_of_connected sC
  haveI := isVariety_of_smooth_of_connected sT
  obtain ⟨hXv, hXs, hXd, hXp⟩ := product_facts sC sT hC hT
  set X : Scheme.{u} := pullback sC sT
  set sX : X ⟶ Spec (.of k) := pullback.fst sC sT ≫ sC
  haveI : AlgebraicGeometry.IsVariety k sX := hXv
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : IsProper sX := inferInstance
  haveI : IsNoetherian X := isNoetherian_of_finiteType sX
  set O : X.Opens := (pullback.snd sC sT) ⁻¹ᵁ U
  haveI : Surjective sC := ⟨fun y => ⟨Classical.arbitrary C, Subsingleton.elim _ _⟩⟩
  have hO : Dense (O : Set X) := by
    obtain ⟨u, hu⟩ := hU
    obtain ⟨x, hx⟩ := (pullback.snd sC sT).surjective u
    exact O.isOpen.dense ⟨x, show pullback.snd sC sT x ∈ U from hx ▸ hu⟩
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  letI : V.Over (Spec (.of k)) := ⟨sV⟩
  let f : X.PartialMap V := ⟨O, hO, (restrictProductIso sC sT U).hom ≫ φ⟩
  haveI : f.IsOver (Spec (.of k)) := by
    rw [Scheme.PartialMap.isOver_iff]
    change ((restrictProductIso sC sT U).hom ≫ φ) ≫ sV = O.ι ≫ pullback.fst sC sT ≫ sC
    rw [Category.assoc, hφ, restrictProductIso_hom_snd_assoc, pullback.condition]
  haveI : IsProper (V ↘ Spec (.of k)) := inferInstanceAs (IsProper sV)
  have hreg := ((isRegular_iff_regular_stalks X).1
    (MMP.Resolution.Bridges.isRegular_of_isSmoothScheme sX hXs)).2
  have hdimX : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2 := fun x => by
    rw [← hXd, topologicalKrullDim_eq_iSup_krullDimOfRing_stalk X]
    exact le_iSup (fun z : X => ringKrullDim (X.presheaf.stalk z)) x
  obtain ⟨T₀, Y, p, h, hTc, -, hTO, hchain, hS, hagree⟩ :=
    Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap_of_isNoetherian
      (S := Spec (.of k)) hreg hdimX f
  obtain ⟨sY, hpsY, hY, hYs, hYd, hYp, hpp, hps, hiso, hcd⟩ :=
    exists_chainData sX hXv hXs hXd hXp (T₀ : Set X) hTc O (fun x hx => hTO x hx) hchain
  refine ⟨Y, sY, p, h, T₀, hTc, fun x hx => hTO x hx, hY, hYs, hYd, hYp, hpp, hps, hiso,
    hpsY, (hS.trans hpsY : h ≫ sV = sY), ?_, hcd⟩
  have h1 : (pullbackRestrictIsoRestrict p O).inv ≫ pullback.fst p O.ι ≫ h =
      (pullbackRestrictIsoRestrict p O).inv ≫ pullback.snd p O.ι ≫ f.hom := by rw [hagree]
  rw [← Category.assoc, pullbackRestrictIsoRestrict_inv_fst] at h1
  rw [h1]
  rfl

end Resolution

section LiftSection

variable {k : Type u} [Field k] [IsAlgClosed k] {C T V Y : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (sT : T ⟶ Spec (.of k)) (U : T.Opens) (φ : pullback sC (U.ι ≫ sT) ⟶ V)

/-- **Lifting a horizontal section to the resolution.** Over `C × U`, where the resolution `p` is
an isomorphism, the section `c ↦ (c, t)` of a `k`-point `t ∈ U` lifts to `Y`, and its composite
with the resolved map is the restriction of `φ` to `C × {t}`. -/
private theorem exists_lift_section (p : Y ⟶ pullback sC sT) (h : Y ⟶ V)
    [IsIso (p ∣_ ((pullback.snd sC sT) ⁻¹ᵁ U))]
    (hcompat : (p ⁻¹ᵁ ((pullback.snd sC sT) ⁻¹ᵁ U)).ι ≫ h =
        (p ∣_ ((pullback.snd sC sT) ⁻¹ᵁ U)) ≫ (restrictProductIso sC sT U).hom ≫ φ)
    (t : Spec (.of k) ⟶ U.toScheme) (ht : t ≫ U.ι ≫ sT = 𝟙 _) :
    ∃ ι : C ⟶ Y, ι ≫ p = sectionAt sC sT (t ≫ U.ι) (by rw [Category.assoc, ht]) ∧
      ι ≫ h = pullback.lift (𝟙 C) (sC ≫ t) (by simp [ht]) ≫ φ := by
  set O : (pullback sC sT : Scheme.{u}).Opens := (pullback.snd sC sT) ⁻¹ᵁ U
  set σ := sectionAt sC sT (t ≫ U.ι) (by rw [Category.assoc, ht])
  have hσO : Set.range σ.base ⊆ Set.range O.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨c, rfl⟩
    show pullback.snd sC sT (σ c) ∈ U
    rw [← Scheme.Hom.comp_apply, sectionAt_snd]
    exact (t (sC c)).2
  set σ' := IsOpenImmersion.lift O.ι σ hσO
  have hσ' : σ' ≫ O.ι = σ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨σ' ≫ inv (p ∣_ O) ≫ (p ⁻¹ᵁ O).ι, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hσ']
  · rw [Category.assoc, Category.assoc, hcompat, IsIso.inv_hom_id_assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, restrictProductIso_hom_fst, ← Category.assoc, hσ', sectionAt_fst,
        pullback.lift_fst]
    · rw [← cancel_mono U.ι, Category.assoc, Category.assoc, restrictProductIso_hom_snd,
        ← Category.assoc, hσ', sectionAt_snd, pullback.lift_snd, Category.assoc]

end LiftSection

section SurfaceData

/-- The geometric input: a smooth projective surface `Y` resolving `φ`, with the invertible
sheaves `M = h^*H`, `F` (a general fibre), `Aᵢ` (the marked sections) and `Eⱼ` (the total
transforms of the exceptional curves), their intersection numbers, and the rational curves
carried by the `Eⱼ`. -/
private theorem exists_surface_data (k : Type u) [Field k] [IsAlgClosed k]
    {C T V : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    (sV : V ⟶ Spec (.of k))
    [IsProper sC] [Smooth sC] [ConnectedSpace C] (hC : topologicalKrullDim C = 1)
    [IsProper sT] [Smooth sT] [ConnectedSpace T] (hT : topologicalKrullDim T = 1)
    [IsProper sV]
    (U : T.Opens) (hU : (U : Set T).Nonempty)
    (φ : pullback sC (U.ι ≫ sT) ⟶ V)
    (hφ : φ ≫ sV = pullback.snd sC (U.ι ≫ sT) ≫ U.ι ≫ sT)
    (hdim : topologicalKrullDim (closure (Set.range φ.base)) = 2)
    {b : ℕ} (hb : 0 < b) (P : Fin b → C) (hP : Function.Injective P)
    (hPc : ∀ i, IsClosed ({P i} : Set C))
    (hconst : ∀ i, ∃ v : V, ∀ z, (pullback.fst sC (U.ι ≫ sT)).base z = P i → φ.base z = v)
    (H : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 H]
    [Stacks.Ample.IsInvertibleModule V H] (hH : Stacks.Ample.IsAmple V H)
    (d : ℤ) (hd : 0 < d)
    (hgen : ∃ W : U.toScheme.Opens, (W : Set U.toScheme).Nonempty ∧
      ∀ (t : Spec (.of k) ⟶ U.toScheme) (ht : t ≫ U.ι ≫ sT = 𝟙 _),
        (∀ x, t.base x ∈ W) →
          invertibleCurveDegree k sC hC.le
            ((Scheme.Modules.pullback
              (pullback.lift (𝟙 C) (sC ≫ t) (by simp [ht]) ≫ φ)).obj H) = d) :
    ∃ (Y : Scheme.{u}) (sY : Y ⟶ Spec (.of k)) (_ : IsProper sY) (_ : Smooth sY)
      (_ : MMP.Mori.IsProjectiveVariety k sY) (hYd : topologicalKrullDim Y ≤ (2 : ℕ))
      (_ : topologicalKrullDim Y = 2)
      (M F : {N : Y.Modules // SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N})
      (A : Fin b → {N : Y.Modules // SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N})
      (n : ℕ)
      (E : Fin n → {N : Y.Modules // SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N})
      (μ : Fin b → Fin n → ℕ),
      @pair k _ Y sY _ hYd M.1 F.1 M.2 F.2 = d ∧
      @pair k _ Y sY _ hYd F.1 F.1 F.2 F.2 = 0 ∧
      (∀ i, @pair k _ Y sY _ hYd (A i).1 (A i).1 (A i).2 (A i).2 = 0) ∧
      (∀ i, @pair k _ Y sY _ hYd F.1 (A i).1 F.2 (A i).2 = 1) ∧
      (∀ j l, @pair k _ Y sY _ hYd (E j).1 (E l).1 (E j).2 (E l).2 = if j = l then -1 else 0) ∧
      (∀ j, @pair k _ Y sY _ hYd (E j).1 F.1 (E j).2 F.2 = 0) ∧
      (∀ i j, @pair k _ Y sY _ hYd (E j).1 (A i).1 (E j).2 (A i).2 = 0) ∧
      0 < @pair k _ Y sY _ hYd M.1 M.1 M.2 M.2 ∧
      (∀ j, 0 ≤ @pair k _ Y sY _ hYd M.1 (E j).1 M.2 (E j).2) ∧
      (∀ i, @pair k _ Y sY _ hYd M.1 (A i).1 M.2 (A i).2 =
        ∑ j, (μ i j : ℤ) * @pair k _ Y sY _ hYd M.1 (E j).1 M.2 (E j).2) ∧
      (∀ j, ∑ i, μ i j ≤ 1) ∧
      ∀ j, 0 < @pair k _ Y sY _ hYd M.1 (E j).1 M.2 (E j).2 →
        ∃ (L : V.IdealSheafData) (hL : IsRationalCurve sV L),
          haveI := hL.2.1
          0 < degreeOn k sV L.subschemeι hL.1.2.le H ∧
            degreeOn k sV L.subschemeι hL.1.2.le H ≤
              @pair k _ Y sY _ hYd M.1 (E j).1 M.2 (E j).2 := by
  -- the curves
  haveI hCv := isVariety_of_smooth_of_connected sC
  haveI hTv := isVariety_of_smooth_of_connected sT
  haveI : IsIntegral C := hCv.toIsIntegral
  haveI : IsIntegral T := hTv.toIsIntegral
  have hCs : IsSmoothScheme sC := (MMP.Mori.isSmoothScheme_iff _).mpr inferInstance
  have hTs : IsSmoothScheme sT := (MMP.Mori.isSmoothScheme_iff _).mpr inferInstance
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hCs).1
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hCs).2
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hTs).1
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hTs).2
  -- the product surface
  obtain ⟨hXv, hXs, hXd, hXp⟩ := product_facts sC sT hC hT
  haveI : AlgebraicGeometry.IsVariety k (pullback.fst sC sT ≫ sC) := hXv
  haveI : IsIntegral (pullback sC sT) := hXv.toIsIntegral
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hXs).1
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hXs).2
  haveI : CompactSpace (pullback sC sT : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst sC sT ≫ sC)
  have hXle : topologicalKrullDim (pullback sC sT : Scheme.{u}) ≤ (2 : ℕ) := by rw [hXd]; rfl
  -- the resolution
  obtain ⟨Y, sY, p, h, T₀, hT₀c, hT₀U, hY, hYs, hYd, hYp, hpp, hps, hiso, hpsY, hhsY, hcompat,
    hcd⟩ := exists_resolution sC sT sV hC hT U hU φ hφ
  haveI : AlgebraicGeometry.IsProjectiveVariety k sY := hYp
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI : IsProper sY := by rw [← hpsY]; infer_instance
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := hpp
  haveI := hps
  haveI := hiso
  obtain ⟨cd⟩ := hcd
  have hYle : topologicalKrullDim Y ≤ (2 : ℕ) := by rw [hYd]; rfl
  have hcY := isCartier_of_isSmoothScheme hYs
  have hcX := isCartier_of_isSmoothScheme hXs
  -- a general fibre
  obtain ⟨W, hWne, hWdeg⟩ := hgen
  obtain ⟨t, htk, htW⟩ := exists_point_mem_of_isOpen (U.ι ≫ sT) W.isOpen hWne
  have ht' : (t ≫ U.ι) ≫ sT = 𝟙 _ := by rw [Category.assoc, htk]
  obtain ⟨ι, hιp, hιh⟩ := exists_lift_section sC sT U φ p h hcompat t htk
  obtain ⟨Q, hQmem, ⟨eQ⟩, hQgen⟩ := exists_fibreDivisor_snd sC sT hC hT (t ≫ U.ι) ht'
  choose G hGmem hGiso using fun i => exists_fibreDivisor_fst sC sT hC hT (hPc i)
  choose G' μ hG'gen hG'iso hμ0 using fun i => cd.strict (G i)
  -- the sheaves
  haveI hQinv : SheafOfModules.IsInvertible (pullback sC sT : Scheme.{u}).presheaf
      (pullback sC sT : Scheme.{u}).ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single Q 1 : Divisor (pullback sC sT))) :=
    (hcX _).isInvertibleModule_divisorialSheaf
  haveI hGinv : ∀ i, SheafOfModules.IsInvertible (pullback sC sT : Scheme.{u}).presheaf
      (pullback sC sT : Scheme.{u}).ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single (G i) 1 : Divisor (pullback sC sT))) :=
    fun i => (hcX _).isInvertibleModule_divisorialSheaf
  haveI hDinv : ∀ j, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (cd.D j).divisorialSheaf := fun j => (hcY _).isInvertibleModule_divisorialSheaf
  let M : {N : Y.Modules // SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N} :=
    ⟨(Scheme.Modules.pullback h).obj H, inferInstance⟩
  let F : {N : Y.Modules // SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N} :=
    ⟨(Scheme.Modules.pullback p).obj
      (Divisor.divisorialSheaf (Finsupp.single Q 1 : Divisor (pullback sC sT))), inferInstance⟩
  let A : Fin b → {N : Y.Modules // SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N} :=
    fun i => ⟨(Scheme.Modules.pullback p).obj
      (Divisor.divisorialSheaf (Finsupp.single (G i) 1 : Divisor (pullback sC sT))), inferInstance⟩
  let E : Fin cd.n → {N : Y.Modules // SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N} :=
    fun j => ⟨(cd.D j).divisorialSheaf, inferInstance⟩
  -- the open set over which `p` is an isomorphism
  set O : (pullback sC sT : Scheme.{u}).Opens := (pullback.snd sC sT) ⁻¹ᵁ U with hOdef
  set σ := sectionAt sC sT (t ≫ U.ι) ht' with hσdef
  haveI := isClosedImmersion_sectionAt sC sT (t ≫ U.ι) ht'
  have hσO : ∀ c, σ c ∈ O := fun c => by
    show pullback.snd sC sT (σ c) ∈ U
    rw [← Scheme.Hom.comp_apply, sectionAt_snd, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact (t (sC c)).2
  have hinj : ∀ y₁ y₂ : Y, p y₁ ∈ O → p y₂ ∈ O → p y₁ = p y₂ → y₁ = y₂ := by
    intro y₁ y₂ h₁ h₂ h₁₂
    have hi := (p ∣_ O).homeomorph.injective
    have := @hi ⟨y₁, h₁⟩ ⟨y₂, h₂⟩ (by
      apply Subtype.ext
      exact (morphismRestrict_base_coe p O ⟨y₁, h₁⟩).trans
        (h₁₂.trans (morphismRestrict_base_coe p O ⟨y₂, h₂⟩).symm))
    exact congrArg Subtype.val this
  haveI : IsClosedImmersion (ι ≫ p) := by rw [hιp]; infer_instance
  haveI : IsClosedImmersion ι := IsClosedImmersion.of_comp ι p
  have hιsY : ι ≫ sY = sC := by
    rw [← hpsY, ← Category.assoc, hιp, ← Category.assoc, sectionAt_fst, Category.id_comp]
  haveI : IsProper (ι ≫ sY) := by rw [hιsY]; infer_instance
  -- `p` is birational, so pull-back preserves intersection numbers
  have hYO : ((p ⁻¹ᵁ O : Y.Opens) : Set Y).Nonempty := by
    obtain ⟨c⟩ : Nonempty C := inferInstance
    obtain ⟨y, hy⟩ := p.surjective (σ c)
    exact ⟨y, show p y ∈ O from hy ▸ hσO c⟩
  have hbir : IsBirationalMorphism p := by
    obtain ⟨c⟩ : Nonempty C := inferInstance
    refine MMP.Flips.isBirationalMorphism_of_isIso_resLE p (p ⁻¹ᵁ O) O hYO ⟨σ c, hσO c⟩ le_rfl ?_
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have hpsX : p ≫ (pullback.fst sC sT ≫ sC) = sY := hpsY
  have hbp : ∀ (N₁ N₂ : (pullback sC sT : Scheme.{u}).Modules)
      [SheafOfModules.IsInvertible (pullback sC sT : Scheme.{u}).presheaf
        (pullback sC sT : Scheme.{u}).ringCatSheaf.2 N₁]
      [SheafOfModules.IsInvertible (pullback sC sT : Scheme.{u}).presheaf
        (pullback sC sT : Scheme.{u}).ringCatSheaf.2 N₂],
      pair k sY hYle ((Scheme.Modules.pullback p).obj N₁) ((Scheme.Modules.pullback p).obj N₂) =
        pair k (pullback.fst sC sT ≫ sC) hXle N₁ N₂ := fun N₁ N₂ _ _ =>
    pair_pullback_of_isBirationalMorphism k sY _ p hpsX hbir hYd hXd hYle hXle N₁ N₂
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  haveI hPτinv : SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single (pointDivisor hT
        (isClosed_singleton_of_section sT (t ≫ U.ι) ht' (IsLocalRing.closedPoint k))) 1 :
          Divisor T)) :=
    (isCartier_of_isSmoothScheme hTs _).isInvertibleModule_divisorialSheaf
  haveI hPiinv : ∀ i, SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single (pointDivisor hC (hPc i)) 1 : Divisor C)) :=
    fun i => (isCartier_of_isSmoothScheme hCs _).isInvertibleModule_divisorialSheaf
  -- the exceptional curves are contracted by `p`
  have hcontr : ∀ j, ∀ P ∈ (cd.D j).support, ∀ y ∈ closure ({P.genericPoint} : Set Y),
      p y = p P.genericPoint := by
    intro j P hP y hy
    have h1 := cd.comp_point j P hP
    have h2 : p P.genericPoint ⤳ p y := (specializes_iff_mem_closure.mpr hy).map p.continuous
    rw [h1, specializes_iff_mem_closure, (hT₀c _ (cd.mem j)).closure_eq] at h2
    rw [h1]
    exact h2
  have hHa := Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple V H hH
  -- the image of `h` is the closure of the image of `φ`
  have hkey : (restrictProductIso sC sT U).inv ≫ inv (p ∣_ O) ≫ (p ⁻¹ᵁ O).ι ≫ h = φ := by
    rw [hcompat, IsIso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  have hrange : closure (Set.range h.base) = closure (Set.range φ.base) := by
    apply le_antisymm
    · refine closure_minimal ?_ isClosed_closure
      have hpre : IsClosed (h.base ⁻¹' closure (Set.range φ.base)) :=
        isClosed_closure.preimage h.continuous
      have hsub : ((p ⁻¹ᵁ O : Y.Opens) : Set Y) ⊆ h.base ⁻¹' closure (Set.range φ.base) := by
        intro y hy
        refine subset_closure ⟨(restrictProductIso sC sT U).hom ((p ∣_ O) ⟨y, hy⟩), ?_⟩
        have := congrArg (fun g => g.base ⟨y, hy⟩) hcompat
        simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
        exact this.symm
      have hdense := (p ⁻¹ᵁ O).isOpen.dense hYO
      rintro _ ⟨y, rfl⟩
      exact (hpre.closure_subset_iff.mpr hsub) (hdense.closure_eq ▸ Set.mem_univ y)
    · refine closure_mono ?_
      rintro _ ⟨z, rfl⟩
      refine ⟨(p ⁻¹ᵁ O).ι ((inv (p ∣_ O)) ((restrictProductIso sC sT U).inv z)), ?_⟩
      have := congrArg (fun g => g.base z) hkey
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
      exact this
  have hImh : topologicalKrullDim (closure (Set.range h.base)) = 2 := by rw [hrange]; exact hdim
  -- the strict transforms of the marked fibres are contracted by `h`
  have hGgenO : ∀ i, (G i).genericPoint ∈ O := fun i => by
    have hmem : σ (P i) ∈ (G i).support := by
      rw [hGmem, ← Scheme.Hom.comp_apply, sectionAt_fst]; rfl
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hmem
    exact hmem.mem_open O.isOpen (hσO _)
  have hGgen : ∀ i, pullback.fst sC sT (G i).genericPoint = P i := fun i =>
    (hGmem i _).mp (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  have hhO : ∀ (y : Y) (hy : p y ∈ O), h y =
      φ ((restrictProductIso sC sT U).hom ((p ∣_ O) ⟨y, hy⟩)) := fun y hy => by
    have := congrArg (fun g => g.base ⟨y, hy⟩) hcompat
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    exact this
  have hfstO : ∀ (y : Y) (hy : p y ∈ O), pullback.fst sC (U.ι ≫ sT)
      ((restrictProductIso sC sT U).hom ((p ∣_ O) ⟨y, hy⟩)) = pullback.fst sC sT (p y) :=
    fun y hy => by
      have := congrArg (fun g => g.base ((p ∣_ O) ⟨y, hy⟩)) (restrictProductIso_hom_fst sC sT U)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
      rw [this]
      congr 1
      exact morphismRestrict_base_coe p O ⟨y, hy⟩
  have hG'contr : ∀ i, ∀ y ∈ closure ({(G' i).genericPoint} : Set Y),
      h y = h (G' i).genericPoint := by
    intro i y hy
    obtain ⟨v, hv⟩ := hconst i
    have hG'O : p (G' i).genericPoint ∈ O := (hG'gen i).symm ▸ hGgenO i
    have h1 : h (G' i).genericPoint = v := by
      rw [hhO _ hG'O]
      exact hv _ (by rw [hfstO, hG'gen, hGgen])
    have h2 : (ι ≫ h) (P i) = v := by
      rw [hιh, Scheme.Hom.comp_apply]
      exact hv _ (by rw [← Scheme.Hom.comp_apply, pullback.lift_fst]; rfl)
    have hcl : IsClosed ({v} : Set V) := by
      haveI : IsProper ((ι ≫ h) ≫ sV) := by
        rw [Category.assoc, hhsY, hιsY]; infer_instance
      haveI := IsProper.of_comp (ι ≫ h) sV
      rw [← h2, ← Set.image_singleton]
      exact (ι ≫ h).isClosedMap _ (hPc i)
    have h3 : h (G' i).genericPoint ⤳ h y :=
      (specializes_iff_mem_closure.mpr hy).map h.continuous
    rw [h1, specializes_iff_mem_closure, hcl.closure_eq] at h3
    rw [h1]
    exact h3
  -- the multiplicities of the exceptional curves in the marked fibres
  haveI hinvY : ∀ D : Divisor Y, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      D.divisorialSheaf := fun D => (hcY D).isInvertibleModule_divisorialSheaf
  haveI hinvX : ∀ D : Divisor (pullback sC sT),
      SheafOfModules.IsInvertible (pullback sC sT : Scheme.{u}).presheaf
        (pullback sC sT : Scheme.{u}).ringCatSheaf.2 D.divisorialSheaf :=
    fun D => (hcX D).isInvertibleModule_divisorialSheaf
  have hηC : ∀ i, genericPoint C ≠ P i := fun i hη => by
    have h1 := coheight_eq_one_of_isClosed hC (hPc i)
    have h0 : Order.coheight (genericPoint C) = 0 := Order.coheight_eq_zero.mpr fun b _ =>
      Scheme.le_iff_specializes.mpr ((genericPoint_spec C).specializes (Set.mem_univ b))
    rw [← hη, h0] at h1
    exact absurd h1 (by decide)
  have hμ_eq : ∀ i j, pairWith k sY hYs hYd
      (Divisor.divisorialSheaf (Finsupp.single (G' i) 1 : Divisor Y)) (cd.D j) = μ i j := by
    intro i j
    obtain ⟨eG'⟩ := hG'iso i
    have h0 : pair k sY hYle (cd.D j).divisorialSheaf (A i).1 = 0 :=
      pair_divisorialSheaf_pullback_eq_zero k sY hYs hYd _ p hpsX (cd.D j) (hcontr j) _
    change pair k sY hYle (cd.D j).divisorialSheaf ((Scheme.Modules.pullback p).obj _) = 0 at h0
    rw [pair_congr_right k sY hYle _ eG', pair_comm, ← pairWith_apply k sY hYs hYd, map_add,
      map_sum] at h0
    have hl : ∀ l, pairWith k sY hYs hYd (cd.D j).divisorialSheaf ((μ i l : ℤ) • cd.D l) =
        if j = l then -(μ i l : ℤ) else 0 := fun l => by
      rw [map_zsmul, pairWith_apply k sY hYs hYd, ← dpair_eq k sY hYs hYd, dpair_comm,
        cd.orth j l]
      split_ifs <;> simp
    simp only [hl, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h0
    rw [pairWith_apply k sY hYs hYd, pair_comm, ← pairWith_apply k sY hYs hYd]
    linarith
  have hμle : ∀ i j, cd.x j ∈ (G i).support → μ i j ≤ 1 := by
    intro i j hxG
    have hxc := hT₀c _ (cd.mem j)
    set xk := pointOfClosedPoint (pullback.fst sC sT ≫ sC) (cd.x j) hxc
    have hxk : xk ≫ pullback.fst sC sT ≫ sC = 𝟙 _ := pointOfClosedPoint_comp _ _ _
    have htj : (xk ≫ pullback.snd sC sT) ≫ sT = 𝟙 _ := by
      rw [Category.assoc, ← pullback.condition]; exact hxk
    obtain ⟨Φ, hΦmem, ⟨eΦ⟩, hΦgen⟩ :=
      exists_fibreDivisor_snd sC sT hC hT (xk ≫ pullback.snd sC sT) htj
    have hxΦ : cd.x j ∈ Φ.support := by
      rw [hΦmem]
      exact (congrArg (fun z => pullback.snd sC sT z) (pointOfClosedPoint_apply _ _ hxc _)).symm
    obtain ⟨R, hR0, ⟨eR⟩, hRsupp, -, hDR⟩ := cd.total Φ
    have hDjR := hDR j hxΦ
    obtain ⟨eG'⟩ := hG'iso i
    -- `(Φ · Gᵢ) = 1` on `C × T`, pulled back to `Y`
    have h1 : pair k sY hYle ((Scheme.Modules.pullback p).obj
        (Divisor.divisorialSheaf (Finsupp.single Φ 1 : Divisor (pullback sC sT))))
        (A i).1 = 1 := by
      change pair k sY hYle _ ((Scheme.Modules.pullback p).obj _) = 1
      rw [hbp]
      exact (dpair_eq k _ hXs hXd _ _).symm.trans
        (pair_fibre_eq_one sC sT hC hXs hXd (pointDivisor hC (hPc i)) (G i) Φ (hGiso i)
          (xk ≫ pullback.snd sC sT) htj hΦgen)
    change pair k sY hYle _ ((Scheme.Modules.pullback p).obj _) = 1 at h1
    rw [pair_congr_left k sY hYle _ eR, pair_congr_right k sY hYle _ eG', pair_comm,
      ← pairWith_apply k sY hYs hYd, map_add, map_sum] at h1
    have hRD : ∀ l, pairWith k sY hYs hYd R.divisorialSheaf (cd.D l) = 0 := fun l => by
      rw [pairWith_apply k sY hYs hYd, pair_congr_right k sY hYle _ eR.symm]
      exact pair_divisorialSheaf_pullback_eq_zero k sY hYs hYd _ p hpsX (cd.D l) (hcontr l) _
    simp only [map_zsmul, hRD, smul_zero, Finset.sum_const_zero, add_zero] at h1
    -- `1 = (G'ᵢ · R) = μᵢⱼ + (G'ᵢ · (R - Dⱼ))`
    rw [pairWith_apply k sY hYs hYd, pair_comm, ← pairWith_apply k sY hYs hYd] at h1
    have hsplit : R = cd.D j + (R - cd.D j) := by abel
    rw [hsplit, map_add, hμ_eq] at h1
    have hnn : 0 ≤ pairWith k sY hYs hYd
        (Divisor.divisorialSheaf (Finsupp.single (G' i) 1 : Divisor Y)) (R - cd.D j) := by
      rw [pairWith_eq_sum]
      refine Finset.sum_nonneg fun P hP => mul_nonneg (sub_nonneg.mpr (hDjR P)) ?_
      refine degree_single_nonneg k sY hYs hYd (G' i) P ?_
      rintro rfl
      have hRG : (G' i) ∈ R.support := by
        rw [Finsupp.mem_support_iff] at hP ⊢
        intro h0
        have a1 := hDjR (G' i)
        have a2 : 0 ≤ cd.D j (G' i) := by simpa using cd.nonneg j (G' i)
        rw [Finsupp.sub_apply] at hP
        omega
      have hGΦ := hRsupp _ hRG
      rw [hG'gen, AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        ← specializes_iff_mem_closure] at hGΦ
      have heq := eq_of_specializes_of_coheight_eq_one hGΦ Φ.coheight_genericPoint
        (G i).coheight_genericPoint
      have := hGgen i
      have hΦgen' : AlgebraicGeometry.PrimeDivisor.genericPoint Φ = _ := hΦgen
      rw [← heq, hΦgen', ← Scheme.Hom.comp_apply, sectionAt_fst] at this
      exact hηC i this
    have : (μ i j : ℤ) ≤ 1 := by linarith
    exact_mod_cast this
  refine ⟨Y, sY, inferInstance, (MMP.Mori.isSmoothScheme_iff _).mp hYs, hYp, hYle, hYd, M, F, A,
    cd.n, E, μ, ?hMF, ?hFF, ?hAA, ?hFA, ?hEE, ?hEF, ?hEA, ?hMM, ?hME, ?hMA, ?hμ, ?hrat⟩
  case hMF =>
    obtain ⟨Q', μQ, hQ'gen, ⟨eQ'⟩, hμQ⟩ := cd.strict Q
    have hμQ0 : ∀ j, μQ j = 0 := fun j => hμQ j fun hx => by
      rw [hQmem] at hx
      refine hT₀U _ (cd.mem j) ?_
      rw [hx]
      exact (t _).2
    have hsum0 : ∑ j, (μQ j : ℤ) • cd.D j = 0 := by simp [hμQ0]
    have e1 : F.1 ≅ Divisor.divisorialSheaf (Finsupp.single Q' 1 : Divisor Y) :=
      eQ' ≪≫ eqToIso (by rw [hsum0, add_zero])
    haveI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
        (Divisor.divisorialSheaf (Finsupp.single Q' 1 : Divisor Y)) :=
      (hcY _).isInvertibleModule_divisorialSheaf
    have hQ'pt : (curveOf k sY hYd Q').point = ι (genericPoint C) := by
      change Q'.genericPoint = _
      have h1 : p Q'.genericPoint = σ (genericPoint C) := by rw [hQ'gen, hQgen]
      have h2 : p (ι (genericPoint C)) = σ (genericPoint C) := by
        rw [← Scheme.Hom.comp_apply, hιp]
      exact hinj _ _ (h1 ▸ hσO _) (h2 ▸ hσO _) (h1.trans h2.symm)
    change pair k sY hYle M.1 F.1 = d
    rw [pair_comm, pair_congr_left k sY hYle M.1 e1]
    have h3 := pairWith_eq_sum k sY hYs hYd M.1 (Finsupp.single Q' 1)
    rw [pairWith_apply, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same, one_mul] at h3
    rw [h3, degree_curve_eq_degreeOn k sY ι hC.le (curveOf k sY hYd Q') hQ'pt M.1,
      MMP.Mori.degreeOn, MMP.Threefold.Resolution.invertibleCurveDegree_congr k hιsY hC.le]
    have e2 : (Scheme.Modules.pullback ι).obj M.1 ≅ (Scheme.Modules.pullback
        (pullback.lift (𝟙 C) (sC ≫ t) (by simp [htk]) ≫ φ)).obj H :=
      (Scheme.Modules.pullbackComp ι h).app H ≪≫ eqToIso (by rw [hιh])
    rw [invertibleCurveDegree_eq_of_iso k sC hC.le e2]
    exact hWdeg t htk htW
  case hFF =>
    change pair k sY hYle F.1 F.1 = 0
    rw [hbp, pair_congr_left k _ hXle _ eQ, pair_congr_right k _ hXle _ eQ]
    exact pair_pullback_eq_zero_of_curve k _ sT (pullback.snd sC sT) pullback.condition.symm
      hXle hT.le _ _
  case hAA =>
    intro i
    obtain ⟨eG⟩ := hGiso i
    change pair k sY hYle (A i).1 (A i).1 = 0
    rw [hbp, pair_congr_left k _ hXle _ eG, pair_congr_right k _ hXle _ eG]
    exact pair_pullback_eq_zero_of_curve k _ sC (pullback.fst sC sT) rfl hXle hC.le _ _
  case hFA =>
    intro i
    change pair k sY hYle F.1 (A i).1 = 1
    rw [hbp]
    exact (dpair_eq k _ hXs hXd _ _).symm.trans
      (pair_fibre_eq_one sC sT hC hXs hXd (pointDivisor hC (hPc i)) (G i) Q (hGiso i)
        (t ≫ U.ι) ht' hQgen)
  case hEE =>
    intro j l
    exact (dpair_eq k sY hYs hYd _ _).symm.trans (cd.orth j l)
  case hEF =>
    intro j
    exact pair_divisorialSheaf_pullback_eq_zero k sY hYs hYd _ p hpsX (cd.D j) (hcontr j) _
  case hEA =>
    intro i j
    exact pair_divisorialSheaf_pullback_eq_zero k sY hYs hYd _ p hpsX (cd.D j) (hcontr j) _
  case hMM => exact pair_pullback_ample_pos k sY sV h hhsY hYd hYle hImh H hHa
  case hME =>
    intro j
    change 0 ≤ pair k sY hYle M.1 (E j).1
    rw [pair_comm, ← pairWith_apply k sY hYs hYd]
    exact pairWith_pullback_ample_nonneg k sY hYs hYd sV h hhsY H hHa (cd.D j) (cd.nonneg j)
  case hMA =>
    intro i
    obtain ⟨eG'⟩ := hG'iso i
    haveI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
        (Divisor.divisorialSheaf ((Finsupp.single (G' i) 1 : Divisor Y) +
          ∑ j, (μ i j : ℤ) • cd.D j)) := (hcY _).isInvertibleModule_divisorialSheaf
    have h0 : pairWith k sY hYs hYd M.1 (Finsupp.single (G' i) 1) = 0 := by
      refine pairWith_pullback_eq_zero k sY hYs hYd sV h hhsY _ (fun P hP => ?_) H
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hP
      subst hP
      exact hG'contr i
    change pair k sY hYle M.1 (A i).1 = ∑ j, (μ i j : ℤ) * pair k sY hYle M.1 (E j).1
    rw [pair_comm, pair_congr_left k sY hYle M.1 eG', ← pairWith_apply k sY hYs hYd, map_add,
      h0, zero_add, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_eq_mul, pairWith_apply k sY hYs hYd, pair_comm]
  case hμ =>
    intro j
    by_cases hex : ∃ i, pullback.fst sC sT (cd.x j) = P i
    · obtain ⟨i₀, hi₀⟩ := hex
      rw [Finset.sum_eq_single i₀ (fun i _ hi => hμ0 i j fun h' =>
        hi (hP (((hGmem i _).mp h').symm.trans hi₀))) (by simp)]
      exact hμle i₀ j ((hGmem i₀ _).mpr hi₀)
    · rw [Finset.sum_eq_zero fun i _ => hμ0 i j fun h' => hex ⟨i, (hGmem i _).mp h'⟩]
      exact zero_le_one
  case hrat =>
    intro j hj
    have hpw : pair k sY hYle M.1 (E j).1 = pairWith k sY hYs hYd M.1 (cd.D j) := by
      rw [pair_comm]; rfl
    rw [hpw] at hj ⊢
    exact exists_isRationalCurve_of_pairWith_pos k sY hYs hYd sV h hhsY H hHa (cd.D j)
      (cd.nonneg j) (cd.comp_param j) hj

end SurfaceData

section Numerics

/-- The elementary inequality behind the estimate. -/
private theorem exists_pos_lt_of_le {b n : ℕ} (hb : 0 < b) (d m : ℚ) (hd : 0 < d) (hm : 0 < m)
    (e : Fin n → ℚ) (he : ∀ j, 0 ≤ e j) (μ : Fin b → Fin n → ℕ) (hμ : ∀ j, ∑ i, μ i j ≤ 1)
    (i₀ : Fin b) (hmin : ∀ i, ∑ j, (μ i₀ j : ℚ) * e j ≤ ∑ j, (μ i j : ℚ) * e j)
    (hM : m ≤ 2 * (∑ j, (μ i₀ j : ℚ) * e j) * d - ∑ j, e j ^ 2) :
    ∃ j, 0 < e j ∧ e j < 2 * d / b := by
  by_contra hcon
  push Not at hcon
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  set c := ∑ j, (μ i₀ j : ℚ) * e j
  have hsq : ∀ j, (∑ i, (μ i j : ℚ)) * e j * (2 * d / b) ≤ e j ^ 2 := by
    intro j
    have hμj : (∑ i, (μ i j : ℚ)) ≤ 1 := by exact_mod_cast hμ j
    have hμ0 : (0 : ℚ) ≤ ∑ i, (μ i j : ℚ) := Finset.sum_nonneg fun i _ => by positivity
    rcases (he j).lt_or_eq with h | h
    · have h2 := hcon j h
      have : e j * (2 * d / b) ≤ e j ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hμj (by positivity : (0:ℚ) ≤ e j * (2 * d / b))]
    · rw [← h]; simp
  have hsum : (∑ j, (∑ i, (μ i j : ℚ)) * e j) * (2 * d / b) ≤ ∑ j, e j ^ 2 := by
    rw [Finset.sum_mul]; exact Finset.sum_le_sum fun j _ => hsq j
  have hswap : ∑ j, (∑ i, (μ i j : ℚ)) * e j = ∑ i, ∑ j, (μ i j : ℚ) * e j := by
    rw [Finset.sum_comm]; simp [Finset.sum_mul]
  have hbc : (b : ℚ) * c ≤ ∑ i, ∑ j, (μ i j : ℚ) * e j := by
    have := Finset.sum_le_sum (s := Finset.univ) fun i (_ : i ∈ Finset.univ) => hmin i
    simpa using this
  rw [hswap] at hsum
  have : 2 * c * d ≤ ∑ j, e j ^ 2 := by
    have h1 : (b : ℚ) * c * (2 * d / b) ≤ (∑ i, ∑ j, (μ i j : ℚ) * e j) * (2 * d / b) :=
      mul_le_mul_of_nonneg_right hbc (by positivity)
    have h2 : (b : ℚ) * c * (2 * d / b) = 2 * c * d := by field_simp
    linarith
  linarith

/-- The Hodge index inequality `(M²) ≤ 2 (M · A) (M · F) - ∑ⱼ (M · Eⱼ)²` for classes with the
intersection matrix of `F, A, E₁, …, Eₙ` on a blown-up product. -/
private theorem sq_le_of_hodge (k : Type u) [Field k] [IsAlgClosed k] {S : Scheme.{u}}
    (f : S ⟶ Spec (.of k)) [IsProper f] [Smooth f] (hS : MMP.Mori.IsProjectiveVariety k f)
    (hdim : topologicalKrullDim S = 2) {n : ℕ}
    (N : Fin (n + 3) → {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N})
    (hFF : @pair k _ S f _ (by rw [hdim]; rfl) (N 1).1 (N 1).1 (N 1).2 (N 1).2 = 0)
    (hAA : @pair k _ S f _ (by rw [hdim]; rfl) (N 2).1 (N 2).1 (N 2).2 (N 2).2 = 0)
    (hFA : @pair k _ S f _ (by rw [hdim]; rfl) (N 1).1 (N 2).1 (N 1).2 (N 2).2 = 1)
    (hEE : ∀ j l : Fin n, @pair k _ S f _ (by rw [hdim]; rfl) (N (j.addNat 3)).1 (N (l.addNat 3)).1
      (N _).2 (N _).2 = if j = l then -1 else 0)
    (hEF : ∀ j : Fin n, @pair k _ S f _ (by rw [hdim]; rfl) (N (j.addNat 3)).1 (N 1).1
      (N _).2 (N _).2 = 0)
    (hEA : ∀ j : Fin n, @pair k _ S f _ (by rw [hdim]; rfl) (N (j.addNat 3)).1 (N 2).1
      (N _).2 (N _).2 = 0) :
    (@pair k _ S f _ (by rw [hdim]; rfl) (N 0).1 (N 0).1 (N 0).2 (N 0).2 : ℚ) ≤
      2 * @pair k _ S f _ (by rw [hdim]; rfl) (N 0).1 (N 2).1 (N 0).2 (N 2).2 *
        @pair k _ S f _ (by rw [hdim]; rfl) (N 0).1 (N 1).1 (N 0).2 (N 1).2 -
      ∑ j : Fin n, (@pair k _ S f _ (by rw [hdim]; rfl) (N 0).1 (N (j.addNat 3)).1
        (N 0).2 (N _).2 : ℚ) ^ 2 := by
  have hd : topologicalKrullDim S ≤ (2 : ℕ) := by rw [hdim]; rfl
  -- the bundled pairing
  let P : {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N} →
      {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N} → ℚ :=
    fun A B => (@pair k _ S f _ hd A.1 B.1 A.2 B.2 : ℚ)
  have hP : ∀ A B, P A B = P B A := fun A B => by
    simp only [P]; exact_mod_cast @pair_comm k _ S f _ hd A.1 B.1 A.2 B.2
  set c := P (N 0) (N 2) with hc
  set d := P (N 0) (N 1) with hd'
  set e : Fin n → ℚ := fun j => P (N 0) (N (j.addNat 3)) with he
  -- the coefficients of `B = M - c F - d A + ∑ eⱼ Eⱼ`
  let β : Fin (n + 3) → ℚ := Fin.cons 1 (Fin.cons (-c) (Fin.cons (-d) e))
  let a : Fin 2 → ℚ := ![1, 1]
  let K : Fin 2 → {N : S.Modules // SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N} :=
    ![N 1, N 2]
  haveI : ∀ i, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (K i).1 := fun i => (K i).2
  haveI : ∀ i, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (N i).1 := fun i => (N i).2
  have hH := MMP.Mori.sheafCombinationIntersectionNumber_two_nonpos_of_pos k f hS hdim a
    (fun i => (K i).1) β (fun j => (N j).1)
  rw [sheafCombinationIntersectionNumber_two_eq_sum k f hd,
    sheafCombinationIntersectionNumber_two_eq_sum k f hd] at hH
  simp only [sheafCombinationIntersectionNumber_one_eq_sum k f hd] at hH
  have hH' : 0 < ∑ i, ∑ j, a i * a j * P (K i) (K j) →
      ∑ x, β x * ∑ i, a i * P (K i) (N x) = 0 →
      ∑ i, ∑ j, β i * β j * P (N i) (N j) ≤ 0 := fun h1 h2 => (hH h1 h2).1
  have hj3 : ∀ j : Fin n, (j.succ.succ.succ : Fin (n + 3)) = j.addNat 3 :=
    fun j => Fin.ext (by simp)
  have hFF' : P (N 1) (N 1) = 0 := by simp only [P]; exact_mod_cast hFF
  have hAA' : P (N 2) (N 2) = 0 := by simp only [P]; exact_mod_cast hAA
  have hFA' : P (N 1) (N 2) = 1 := by simp only [P]; exact_mod_cast hFA
  have hAF' : P (N 2) (N 1) = 1 := by rw [hP]; exact hFA'
  have hEE' : ∀ j l : Fin n, P (N (j.addNat 3)) (N (l.addNat 3)) = if j = l then -1 else 0 :=
    fun j l => by simp only [P]; rw [hEE j l]; split_ifs <;> simp
  have hEF' : ∀ j : Fin n, P (N (j.addNat 3)) (N 1) = 0 :=
    fun j => by simp only [P]; exact_mod_cast hEF j
  have hFE' : ∀ j : Fin n, P (N 1) (N (j.addNat 3)) = 0 := fun j => by rw [hP]; exact hEF' j
  have hEA' : ∀ j : Fin n, P (N (j.addNat 3)) (N 2) = 0 :=
    fun j => by simp only [P]; exact_mod_cast hEA j
  have hAE' : ∀ j : Fin n, P (N 2) (N (j.addNat 3)) = 0 := fun j => by rw [hP]; exact hEA' j
  have hME : ∀ j : Fin n, P (N 0) (N (j.addNat 3)) = e j := fun j => rfl
  have hEM : ∀ j : Fin n, P (N (j.addNat 3)) (N 0) = e j := fun j => by rw [hP]
  have hMF : P (N 0) (N 1) = d := rfl
  have hFM : P (N 1) (N 0) = d := by rw [hP]
  have hMA : P (N 0) (N 2) = c := rfl
  have hAM : P (N 2) (N 0) = c := by rw [hP]
  have k1 : (0 : ℚ) < ∑ i, ∑ j, a i * a j * P (K i) (K j) := by
    simp only [Fin.sum_univ_two, a, K, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    rw [hFF', hAA', hFA', hAF']; norm_num
  have k2 : ∑ x, β x * ∑ i, a i * P (K i) (N x) = 0 := by
    simp only [Fin.sum_univ_two, a, K, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, one_mul]
    simp only [Fin.sum_univ_succ, β, Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, hj3]
    rw [hFM, hAM, hFF', hAF', hFA', hAA']
    simp only [hFE', hAE', add_zero, Finset.sum_const_zero, mul_zero]
    ring
  have k3 : ∑ i, ∑ j, β i * β j * P (N i) (N j) =
      P (N 0) (N 0) - 2 * c * d + ∑ j, e j ^ 2 := by
    simp only [Fin.sum_univ_succ, β, Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, hj3]
    simp only [hFF', hAA', hFA', hAF', hEE', hEF', hFE', hEA', hAE', hME, hEM, hMF, hFM, hMA,
      hAM]
    simp only [mul_zero, Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_neg, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, one_mul, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, sq]
    ring
  have := hH' k1 k2
  rw [k3] at this
  show P (N 0) (N 0) ≤ 2 * c * d - ∑ j, e j ^ 2
  linarith

end Numerics

/-- **Marked product-surface degree estimate.** Let `C`, `T` be smooth proper connected curves
over an algebraically closed field `k`, `U ⊆ T` a nonempty open, and `φ : C ×_k U ⟶ V` a
`k`-morphism to a proper `k`-scheme `V` with two-dimensional image. If `φ` contracts each of the
sections `{P i} × U` over `b > 0` distinct closed points `P i ∈ C`, and the ample invertible sheaf
`H` on `V` has degree `d > 0` on the fibres `C × {t}` for `t` in a nonempty open of `U`, then `V`
contains a rational curve `L` with `0 < (H · L) < 2d / b`. -/
private theorem exists_isRationalCurve_degreeOn_lt_of_constant_on_sections
    (k : Type u) [Field k] [IsAlgClosed k]
    {C T V : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    (sV : V ⟶ Spec (.of k))
    [IsProper sC] [Smooth sC] [ConnectedSpace C] (hC : topologicalKrullDim C = 1)
    [IsProper sT] [Smooth sT] [ConnectedSpace T] (hT : topologicalKrullDim T = 1)
    [IsProper sV]
    (U : T.Opens) (hU : (U : Set T).Nonempty)
    (φ : pullback sC (U.ι ≫ sT) ⟶ V)
    (hφ : φ ≫ sV = pullback.snd sC (U.ι ≫ sT) ≫ U.ι ≫ sT)
    (hdim : topologicalKrullDim (closure (Set.range φ.base)) = 2)
    {b : ℕ} (hb : 0 < b) (P : Fin b → C) (hP : Function.Injective P)
    (hPc : ∀ i, IsClosed ({P i} : Set C))
    (hconst : ∀ i, ∃ v : V, ∀ z, (pullback.fst sC (U.ι ≫ sT)).base z = P i → φ.base z = v)
    (H : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 H]
    [Stacks.Ample.IsInvertibleModule V H] (hH : Stacks.Ample.IsAmple V H)
    (d : ℤ) (hd : 0 < d)
    (hgen : ∃ W : U.toScheme.Opens, (W : Set U.toScheme).Nonempty ∧
      ∀ (t : Spec (.of k) ⟶ U.toScheme) (ht : t ≫ U.ι ≫ sT = 𝟙 _),
        (∀ x, t.base x ∈ W) →
          invertibleCurveDegree k sC hC.le
            ((Scheme.Modules.pullback
              (pullback.lift (𝟙 C) (sC ≫ t) (by simp [ht]) ≫ φ)).obj H) = d) :
    ∃ (L : V.IdealSheafData) (hL : IsRationalCurve sV L),
      haveI := hL.2.1
      0 < degreeOn k sV L.subschemeι hL.1.2.le H ∧
        (degreeOn k sV L.subschemeι hL.1.2.le H : ℚ) < 2 * d / b := by
  obtain ⟨Y, sY, _, _, hYp, hYd, hYd2, M, F, A, n, E, μ, hMF, hFF, hAA, hFA, hEE, hEF, hEA, hMM,
    he, hc, hμ, hL⟩ := exists_surface_data k sC sT sV hC hT U hU φ hφ hdim hb P hP hPc hconst H hH
    d hd hgen
  -- the pairing, bundled
  set pr := fun A B : {N : Y.Modules // SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N}
    => @pair k _ Y sY _ hYd A.1 B.1 A.2 B.2 with hpr
  -- a marked section of least `M`-degree
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ
    (fun i => ∑ j, (μ i j : ℚ) * (pr M (E j) : ℚ)) ⟨⟨0, hb⟩, Finset.mem_univ _⟩
  let N : Fin (n + 3) → {N : Y.Modules // SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N}
    := Fin.cons M (Fin.cons F (Fin.cons (A i₀) E))
  have hN3 : ∀ j : Fin n, N (j.addNat 3) = E j := fun j => by
    have : (j.addNat 3 : Fin (n + 3)) = j.succ.succ.succ := Fin.ext (by simp)
    rw [this]; rfl
  have hsq := sq_le_of_hodge k sY hYp hYd2 N hFF (hAA i₀) (hFA i₀)
    (fun j l => by rw [hN3, hN3]; exact hEE j l) (fun j => by rw [hN3]; exact hEF j)
    (fun j => by rw [hN3]; exact hEA i₀ j)
  simp only [hN3] at hsq
  have hcq : ∀ i, (pr M (A i) : ℚ) = ∑ j, (μ i j : ℚ) * (pr M (E j) : ℚ) := fun i => by
    simp only [hpr]; rw [hc i]; push_cast; rfl
  obtain ⟨j, hj0, hj1⟩ := exists_pos_lt_of_le hb (d : ℚ) (pr M M : ℚ) (by exact_mod_cast hd)
    (by exact_mod_cast hMM) (fun j => (pr M (E j) : ℚ)) (fun j => by exact_mod_cast he j) μ hμ
    i₀ (fun i => hi₀ i (Finset.mem_univ _)) (by
      have h1 : (pr M (A i₀) : ℚ) = ∑ j, (μ i₀ j : ℚ) * (pr M (E j) : ℚ) := hcq i₀
      have h2 : (pr M F : ℚ) = d := by exact_mod_cast hMF
      rw [← h1, ← h2]
      exact hsq)
  obtain ⟨L, hLr, hL0, hL1⟩ := hL j (by exact_mod_cast hj0)
  refine ⟨L, hLr, hL0, ?_⟩
  have : (degreeOn k sV L.subschemeι hLr.1.2.le H : ℚ) ≤ (pr M (E j) : ℚ) := by
    haveI := hLr.2.1
    exact_mod_cast hL1
  exact lt_of_le_of_lt this hj1

section Frobenius

open Stacks.Frobenius TopologicalSpace

variable {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Over a perfect field the absolute Frobenius of the spectrum is an isomorphism. -/
private theorem isIso_absoluteFrobenius_spec [PerfectRing k p]
    (hS : IsInCharacteristic (Spec (.of k)) p) :
    IsIso (absoluteFrobenius (Spec (.of k)) p hS) := by
  have h := specMap_eq_absoluteFrobeniusPow (frobeniusEquiv k p).toRingHom p 1 hS
    (fun a => by simp [frobenius_def])
  have h1 : absoluteFrobeniusPow (Spec (.of k)) p hS 1 = absoluteFrobenius (Spec (.of k)) p hS :=
    by rw [absoluteFrobeniusPow, pow_one]
  rw [← h1, ← h]
  haveI : IsIso (CommRingCat.ofHom (frobeniusEquiv k p).toRingHom) :=
    (RingEquiv.toCommRingCatIso (frobeniusEquiv k p)).isIso_hom
  infer_instance

/-- Over a perfect field the `n`-fold absolute Frobenius of the spectrum is an isomorphism. -/
private theorem isIso_absoluteFrobeniusPow_spec [PerfectRing k p]
    (hS : IsInCharacteristic (Spec (.of k)) p) (n : ℕ) :
    IsIso (absoluteFrobeniusPow (Spec (.of k)) p hS n) := by
  haveI := isIso_absoluteFrobenius_spec p hS
  induction n with
  | zero => rw [absoluteFrobeniusPow_zero]; infer_instance
  | succ m ih => rw [absoluteFrobeniusPow_succ_eq_comp]; infer_instance

section FrobeniusTwist

open TopologicalSpace

/-- The relative Frobenius is a homeomorphism on underlying spaces, being a universal
homeomorphism. -/
private theorem isHomeomorph_relativeFrobenius (p : ℕ) [Fact p.Prime] {S : Scheme.{u}}
    (hS : IsInCharacteristic S p) (Z : Over S) :
    IsHomeomorph (relativeFrobenius S p hS Z).left :=
  (relativeFrobenius_universalHomeomorphism S p hS Z).universally_isHomeomorph
    _ _ _ IsPullback.of_id_snd

/-- **The Frobenius twist of a smooth scheme over a field is smooth.** The structure morphism of
the twist is the base change of that of `X` along the absolute Frobenius of `Spec k`. -/
private theorem smooth_frobeniusTwist_curve {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic (Spec (.of k)) p) {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    [Smooth pX] :
    Smooth ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom := by
  change Smooth (pullback.snd pX (absoluteFrobenius (Spec (.of k)) p hS))
  infer_instance

/-- The Frobenius twist of a smooth scheme over a field is reduced: it is normal, and a normal
local ring is a domain. -/
private theorem isReduced_frobeniusTwist_curve {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic (Spec (.of k)) p) {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    [Smooth pX] :
    IsReduced ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left := by
  have : Smooth ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom :=
    smooth_frobeniusTwist_curve p hS pX
  have : IsNormal ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left :=
    isNormal_of_isRegular _
      (isRegular_of_smooth_over_field ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom)
  have : ∀ x : ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left,
      _root_.IsReduced
        (((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left.presheaf.stalk x) :=
    fun _ => inferInstance
  exact isReduced_of_isReduced_stalk _

/-- The Frobenius twist of a smooth curve over a field is a curve over the field. -/
private theorem isCurve_frobeniusTwist_curve {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (hS : IsInCharacteristic (Spec (.of k)) p) {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    [AlgebraicGeometry.IsCurve k pX] [Smooth pX] :
    AlgebraicGeometry.IsCurve k ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom where
  toIsVariety := isVariety_frobeniusTwist_of_isReduced pX p (isReduced_frobeniusTwist_curve p hS pX)
  topologicalKrullDim_eq_one :=
    (IsHomeomorph.topologicalKrullDim_eq _
        (isHomeomorph_relativeFrobenius p hS (Over.mk pX))).symm.trans
      (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one pX)

/-- The relative Frobenius of a curve is not constant on underlying points. -/
private theorem not_constant_relativeFrobenius_curve {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic (Spec (.of k)) p) {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    [AlgebraicGeometry.IsCurve k pX] :
    ¬ ∃ y : ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left,
      ∀ x : X, (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left.base x = y := by
  rintro ⟨y, hy⟩
  have hinj := (isHomeomorph_relativeFrobenius p hS (Over.mk pX)).injective
  exact not_subsingleton_of_topologicalKrullDim_eq_one
    (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one pX)
    ⟨fun a b => hinj ((hy a).trans (hy b).symm)⟩

/-- **Stacks Project, Tag 0CCF at a smooth proper curve.** The relative Frobenius of a smooth
proper curve over a field of characteristic `p` has degree `p`.

The degree is `AlgebraicGeometry.degreeOver` of [Stacks, Tag 02NY] with its instance arguments
written out as `AlgebraicGeometry.curveDegree_pullback_eq_degreeOver_mul` writes them, so that
this is the value of the degree factor in that formula at the relative Frobenius. -/
private theorem degreeOver_relativeFrobenius_curve {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (hS : IsInCharacteristic (Spec (.of k)) p) {X : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsCurve k pX] [Smooth pX] [IsProper pX] :
    letI : AlgebraicGeometry.IsCurve k
        ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom :=
      isCurve_frobeniusTwist_curve p hS pX
    @degreeOver X ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left
        (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left inferInstance inferInstance
        (locallyOfFiniteType_of_isCurve_comp k pX
          ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom
          (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left
          (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).w)
        (isDominant_of_not_constant k pX
          ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom
          (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left
          (not_constant_relativeFrobenius_curve p hS pX)) = p := by
  let : AlgebraicGeometry.IsCurve k ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom :=
    isCurve_frobeniusTwist_curve p hS pX
  have h := degreeOver_relativeFrobenius pX p hS (isReduced_frobeniusTwist_curve p hS pX) 1
    (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one pX)
  rw [pow_one] at h
  exact h

/-- **The tower law for the degree** ([Stacks, Tag 02NZ]): for dominant morphisms of integral
schemes, locally of finite type, with finite extensions of function fields,
`deg(f ≫ g) = deg f · deg g`. -/
private theorem degreeOver_comp_of_pos {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [LocallyOfFiniteType f] [IsDominant f] [LocallyOfFiniteType g] [IsDominant g]
    [LocallyOfFiniteType (f ≫ g)]
    (hf : 0 < degreeOver f) (hg : 0 < degreeOver g) :
    degreeOver (f ≫ g) = degreeOver f * degreeOver g := by
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  letI : Algebra Z.functionField Y.functionField := (dominantFunctionFieldMap g).toAlgebra
  letI : Algebra Z.functionField X.functionField := (dominantFunctionFieldMap (f ≫ g)).toAlgebra
  have h1 : degreeOver f = Module.finrank Y.functionField X.functionField :=
    degreeOver_eq_finrank f rfl
  have h2 : degreeOver g = Module.finrank Z.functionField Y.functionField :=
    degreeOver_eq_finrank g rfl
  have h3 : degreeOver (f ≫ g) = Module.finrank Z.functionField X.functionField :=
    degreeOver_eq_finrank (f ≫ g) rfl
  haveI : FiniteDimensional Y.functionField X.functionField :=
    Module.finite_of_finrank_pos (h1 ▸ hf)
  haveI : FiniteDimensional Z.functionField Y.functionField :=
    Module.finite_of_finrank_pos (h2 ▸ hg)
  rw [h3, finrank_functionField_comp f g rfl rfl rfl, ← h1, ← h2]

/-- The degree only depends on the morphism, not on the proofs of its instance arguments. -/
private theorem degreeOver_congr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') [IsIntegral X]
    [IsIntegral Y] [LocallyOfFiniteType f] [IsDominant f] [LocallyOfFiniteType f']
    [IsDominant f'] : degreeOver f = degreeOver f' := by
  subst h
  rfl

variable {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
  {X : Scheme.{u}} (pX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsCurve k pX] [Smooth pX]
  [IsProper pX]
  (hX : IsInCharacteristic X p)

include pX in
/-- The `n`-fold absolute Frobenius of a curve over a perfect field is locally of finite type:
composed with the structure morphism it is the structure morphism followed by the `n`-fold
Frobenius of the spectrum of the field, an isomorphism. -/
private theorem locallyOfFiniteType_absoluteFrobeniusPow_curve (n : ℕ) :
    LocallyOfFiniteType (absoluteFrobeniusPow X p hX n) := by
  have hS : IsInCharacteristic (Spec (.of k)) p :=
    isInCharacteristic_spec k p (CharP.cast_eq_zero k p)
  haveI := isIso_absoluteFrobeniusPow_spec p hS n
  have hcomp : LocallyOfFiniteType (absoluteFrobeniusPow X p hX n ≫ pX) := by
    rw [absoluteFrobeniusPow_naturality pX p hX hS n]
    infer_instance
  exact locallyOfFiniteType_of_comp _ pX

include pX in
/-- The absolute Frobenius of a curve over a perfect field is dominant. -/
private theorem isDominant_absoluteFrobenius_curve : IsDominant (absoluteFrobenius X p hX) := by
  have hS : IsInCharacteristic (Spec (.of k)) p :=
    isInCharacteristic_spec k p (CharP.cast_eq_zero k p)
  haveI := isIso_absoluteFrobenius_spec p hS
  haveI : AlgebraicGeometry.IsCurve k ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom :=
    isCurve_frobeniusTwist_curve p hS pX
  haveI := isDominant_of_not_constant k pX
    ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom
    (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left
    (not_constant_relativeFrobenius_curve p hS pX)
  haveI : IsDominant (pullback.fst pX (absoluteFrobenius (Spec (.of k)) p hS)) :=
    (isDominant_iff _).mpr (Function.Surjective.denseRange
      (pullback.fst pX (absoluteFrobenius (Spec (.of k)) p hS)).homeomorph.surjective)
  change IsDominant (absoluteFrobenius (Over.mk pX).left p hX)
  rw [← relativeFrobenius_fst (Spec (.of k)) p hS (Over.mk pX)]
  infer_instance

include pX in
/-- **The absolute Frobenius of a smooth proper curve over a perfect field of characteristic `p`
has degree `p`** ([Stacks, Tag 0CCF]). -/
private theorem degreeOver_absoluteFrobenius_curve [IsDominant (absoluteFrobenius X p hX)]
    [LocallyOfFiniteType (absoluteFrobenius X p hX)] :
    degreeOver (absoluteFrobenius X p hX) = p := by
  have hS : IsInCharacteristic (Spec (.of k)) p :=
    isInCharacteristic_spec k p (CharP.cast_eq_zero k p)
  haveI := isIso_absoluteFrobenius_spec p hS
  haveI : AlgebraicGeometry.IsCurve k ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom :=
    isCurve_frobeniusTwist_curve p hS pX
  haveI := locallyOfFiniteType_of_isCurve_comp k pX
    ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom
    (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left
    (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).w
  haveI := isDominant_of_not_constant k pX
    ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom
    (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left
    (not_constant_relativeFrobenius_curve p hS pX)
  rw [degreeOver_eq_degreeOver_of_isIso (absoluteFrobenius X p hX)
    (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left
    (pullback.fst pX (absoluteFrobenius (Spec (.of k)) p hS))
    (relativeFrobenius_fst (Spec (.of k)) p hS (Over.mk pX))]
  exact degreeOver_relativeFrobenius_curve p hS pX

include pX in
/-- **The `(n + 1)`-fold absolute Frobenius of a smooth proper curve over a perfect field of
characteristic `p` is dominant and has degree `p ^ (n + 1)`.** -/
private theorem degreeOver_absoluteFrobeniusPow_curve (n : ℕ) :
    ∃ (_ : IsDominant (absoluteFrobeniusPow X p hX (n + 1)))
      (_ : LocallyOfFiniteType (absoluteFrobeniusPow X p hX (n + 1))),
      degreeOver (absoluteFrobeniusPow X p hX (n + 1)) = p ^ (n + 1) := by
  haveI := isDominant_absoluteFrobenius_curve p pX hX
  haveI : LocallyOfFiniteType (absoluteFrobenius X p hX) := by
    have h := locallyOfFiniteType_absoluteFrobeniusPow_curve p pX hX 1
    rwa [absoluteFrobeniusPow, pow_one] at h
  have h1 : degreeOver (absoluteFrobenius X p hX) = p :=
    degreeOver_absoluteFrobenius_curve p pX hX
  have hpos : 0 < p := (Fact.out : p.Prime).pos
  induction n with
  | zero =>
    have hF : absoluteFrobeniusPow X p hX (0 + 1) = absoluteFrobenius X p hX := by
      rw [zero_add, absoluteFrobeniusPow, pow_one]
    haveI : IsDominant (absoluteFrobeniusPow X p hX (0 + 1)) := by rw [hF]; infer_instance
    haveI := locallyOfFiniteType_absoluteFrobeniusPow_curve p pX hX (0 + 1)
    refine ⟨inferInstance, inferInstance, ?_⟩
    rw [degreeOver_congr hF, h1, zero_add, pow_one]
  | succ m ih =>
    obtain ⟨hdom, hlft, hdeg⟩ := ih
    haveI := hdom
    haveI := hlft
    have hsucc := absoluteFrobeniusPow_succ_eq_comp X p hX (m + 1)
    haveI : IsDominant (absoluteFrobeniusPow X p hX (m + 1 + 1)) := by
      rw [hsucc]; infer_instance
    haveI := locallyOfFiniteType_absoluteFrobeniusPow_curve p pX hX (m + 1 + 1)
    refine ⟨inferInstance, inferInstance, ?_⟩
    have key : degreeOver (absoluteFrobenius X p hX ≫ absoluteFrobeniusPow X p hX (m + 1)) =
        degreeOver (absoluteFrobenius X p hX) *
          degreeOver (absoluteFrobeniusPow X p hX (m + 1)) :=
      degreeOver_comp_of_pos _ _ (by rw [h1]; exact hpos)
        (by rw [hdeg]; exact pow_pos hpos _)
    rw [degreeOver_congr hsucc, key, h1, hdeg, ← pow_succ']

end FrobeniusTwist

section Cover

variable {k : Type u} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The `n`-fold absolute Frobenius fixes every point. -/
private theorem absoluteFrobeniusPow_base_apply (X : Scheme.{u}) (hX : IsInCharacteristic X p)
    (n : ℕ) (x : X) : (absoluteFrobeniusPow X p hX n).base x = x := by
  induction n with
  | zero => rw [absoluteFrobeniusPow_zero]; rfl
  | succ m ih =>
    rw [absoluteFrobeniusPow_succ_eq_comp, Scheme.Hom.comp_base, TopCat.comp_app]
    exact ih

/-- **The Frobenius cover of a curve.** For a smooth projective curve `C` over an algebraically
closed field of characteristic `p` and `q = p ^ (a + 1)`, the scheme `C` with its structure
morphism followed by the `q`-power Frobenius of `Spec k` is again a smooth projective curve
`C_q` over `k`, of the same genus, and the `(a + 1)`-fold absolute Frobenius is a surjective
morphism `C_q ⟶ C` over `k` multiplying degrees of invertible sheaves by `q`. -/
private theorem exists_frobeniusCover {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
    [AlgebraicGeometry.IsCurve k sC] [AlgebraicGeometry.IsProjectiveVariety k sC] [Smooth sC]
    (a : ℕ) :
    ∃ (sC' : C ⟶ Spec (.of k)) (φ : C ⟶ C) (_ : AlgebraicGeometry.IsCurve k sC')
      (_ : AlgebraicGeometry.IsProjectiveVariety k sC')
      (_ : Smooth sC'), φ ≫ sC = sC' ∧ Function.Surjective φ.base ∧ genus sC' = genus sC ∧
      ∀ (L : C.Modules) [Stacks.Ample.IsInvertibleModule C L],
        invertibleCurveDegree k sC'
            (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := sC)).le
            ((Scheme.Modules.pullback φ).obj L) =
          p ^ (a + 1) * invertibleCurveDegree k sC
            (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := sC)).le L := by
  have hS : IsInCharacteristic (Spec (.of k)) p :=
    isInCharacteristic_spec k p (CharP.cast_eq_zero k p)
  have hC : IsInCharacteristic C p := isInCharacteristic_of_hom sC p hS
  set σ := absoluteFrobeniusPow (Spec (.of k)) p hS (a + 1) with hσ
  haveI : IsIso σ := isIso_absoluteFrobeniusPow_spec p hS (a + 1)
  set φ := absoluteFrobeniusPow C p hC (a + 1) with hφdef
  have hφ : φ ≫ sC = sC ≫ σ := absoluteFrobeniusPow_naturality sC p hC hS (a + 1)
  have hcurve : AlgebraicGeometry.IsCurve k (sC ≫ σ) :=
    { toIsIntegral := inferInstance
      topologicalKrullDim_eq_one := AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := sC) }
  have hproj : AlgebraicGeometry.IsProjectiveVariety k (sC ≫ σ) :=
    { toIsVariety := hcurve.toIsVariety
      isProjective := isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
        ⟨Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral (sC ≫ σ)
          (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := sC)), inferInstance⟩ }
  have hbase : Function.Surjective φ.base := fun x =>
    ⟨x, absoluteFrobeniusPow_base_apply p C hC _ x⟩
  refine ⟨sC ≫ σ, φ, hcurve, hproj, inferInstance, hφ, hbase, ?_, ?_⟩
  · -- genus
    let e : k ≃+* k := iterateFrobeniusEquiv k p (a + 1)
    have he : Spec.map (CommRingCat.ofHom e.toRingHom) = σ :=
      specMap_eq_absoluteFrobeniusPow e.toRingHom p (a + 1) hS (fun x => by
        change iterateFrobenius k p (a + 1) x = _
        rw [iterateFrobenius_def])
    letI : Algebra k k := e.symm.toRingHom.toAlgebra
    have hinv : σ ≫ Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _ := by
      rw [← he, ← Spec.map_comp]
      convert Spec.map_id (CommRingCat.of k)
      ext x
      change e (e.symm x) = x
      simp
    haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
      have : Spec.map (CommRingCat.ofHom (algebraMap k k)) = inv σ := by
        rw [← cancel_epi σ, hinv, IsIso.hom_inv_id]
      rw [this]; infer_instance
    exact genus_baseChange k k (𝟙 C) (sC ≫ σ) sC
      (IsPullback.of_horiz_isIso ⟨by rw [Category.assoc, hinv]; simp⟩)
  · intro L _
    have hdim := (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := sC)).le
    have hnc : ¬ ∃ y : C, ∀ x : C, φ.base x = y := by
      rintro ⟨y, hy⟩
      refine not_subsingleton_of_topologicalKrullDim_eq_one
        (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := sC)) ⟨fun x x' => ?_⟩
      rw [← absoluteFrobeniusPow_base_apply p C hC (a + 1) x,
        ← absoluteFrobeniusPow_base_apply p C hC (a + 1) x']
      exact (hy x).trans (hy x').symm
    haveI : IsFinite φ := isFinite_of_not_constant k (sC ≫ σ) sC φ hφ hnc
    haveI : Surjective φ := ⟨hbase⟩
    haveI : IsDominant φ := inferInstance
    haveI : LocallyOfFiniteType φ := inferInstance
    have h := MMP.Resolution.degree_pullback_eq_degreeOver_mul sC (sC ≫ σ) φ hφ L
    rw [MMP.Resolution.degree_eq_invertibleCurveDegree _ _ hdim,
      MMP.Resolution.degree_eq_invertibleCurveDegree _ _ hdim] at h
    obtain ⟨_, _, hdegF⟩ := degreeOver_absoluteFrobeniusPow_curve p sC hC a
    rw [h, hdegF]
    push_cast; ring

end Cover

end Frobenius

section ProjectiveLineConstant

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **No nonconstant map from `ℙ¹` to a curve of positive genus.** A `k`-morphism from the
projective line to a smooth projective curve of genus `≥ 1` is constant: otherwise the curve is
dominated by `ℙ¹`, hence rational by Lüroth's theorem, and a finite birational map from `ℙ¹` onto
the normal curve is an isomorphism, so the genus would be `0`. -/
private theorem exists_forall_apply_eq_of_projectiveLine {E : Scheme.{u}} (sE : E ⟶ Spec (.of k))
    [AlgebraicGeometry.IsCurve k sE] [AlgebraicGeometry.IsProjectiveVariety k sE] [Smooth sE]
    (hg : 1 ≤ genus sE) (ψ : projectiveLine k ⟶ E) (hψ : ψ ≫ sE = projectiveLine k ↘ Spec (.of k)) :
    ∃ e : E, ∀ x, ψ x = e := by
  by_contra hnc
  haveI : IsIntegral (projectiveLine k) := projectiveLine_isIntegral k
  let e : (⊥ : (projectiveLine k).IdealSheafData).subscheme ≅ projectiveLine k :=
    asIso (⊥ : (projectiveLine k).IdealSheafData).subschemeι
  have hC := isRationalCurve_projectiveLine k
  haveI : IsIntegral (⊥ : (projectiveLine k).IdealSheafData).subscheme := hC.1.1
  have hnc' : ¬ (ψ.base '' ((⊥ : (projectiveLine k).IdealSheafData).support :
      Set (projectiveLine k))).Subsingleton := by
    intro hs
    apply hnc
    obtain ⟨x₀⟩ : Nonempty (projectiveLine k) := inferInstance
    refine ⟨ψ x₀, fun x => hs ⟨x, by simp, rfl⟩ ⟨x₀, by simp, rfl⟩⟩
  haveI : AlgebraicGeometry.IsProperVariety k sE := inferInstance
  have hR := MMP.Mori.IsRationalCurve.ker_subschemeι_comp hψ hC hnc'
  set J := ((⊥ : (projectiveLine k).IdealSheafData).subschemeι ≫ ψ).ker with hJdef
  have hη : ψ (genericPoint (projectiveLine k)) = genericPoint E :=
    map_genericPoint_of_not_constant k (projectiveLine k ↘ Spec (.of k)) sE ψ hnc
  have hJ : J = ⊥ := by
    rw [hJdef, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    have hdense : closure (Set.range ((⊥ : (projectiveLine k).IdealSheafData).subschemeι ≫
        ψ).base) = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← (genericPoint_spec E).def]
      refine closure_mono
        (Set.singleton_subset_iff.mpr ⟨e.inv (genericPoint (projectiveLine k)), ?_⟩)
      rw [← Scheme.Hom.comp_apply, ← Category.assoc]
      change ((e.inv ≫ e.hom) ≫ ψ) _ = _
      rw [e.inv_hom_id, Category.id_comp]
      exact hη
    have : TopologicalSpace.Closeds.closure
        (Set.range ((⊥ : (projectiveLine k).IdealSheafData).subschemeι ≫ ψ).base) = ⊤ :=
      TopologicalSpace.Closeds.ext (by rw [TopologicalSpace.Closeds.coe_closure, hdense]; rfl)
    rw [this, Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]
  obtain ⟨ν, hν, hνf, hνb⟩ := hR.2.2
  haveI : IsIso J.subschemeι := (Scheme.isIso_subschemeι_iff_eq_bot J).mpr hJ
  haveI : IsNormal E := isNormal_of_isRegular E (isRegular_of_smooth_over_field sE)
  haveI : IsNormal J.subscheme := isNormal_of_isOpenImmersion J.subschemeι
  haveI : IsIntegral J.subscheme := hR.1.1
  haveI := hνf
  haveI : IsIso ν := isIso_of_isIntegralHom_of_isBirational_of_isNormal ν
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hνb)
  have h0 : genus sE = 0 :=
    Stacks.Curves.genus_eq_zero_of_iso_projectiveLine
      ((asIso J.subschemeι).symm ≪≫ (asIso ν).symm ≪≫ projectiveLineIsoProj k) sE
  omega

end ProjectiveLineConstant

section Descent

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- The reduced closed point `{w}`, as an ideal sheaf. -/
local notation "𝓘[" w ", " hw "]" =>
  Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : TopologicalSpace.Closeds _)

/-- **Descent through the blow-up of a point.** A `k`-morphism from the blow-up of a closed point
of a smooth projective surface to a smooth projective curve of genus `≥ 1` factors through the
blow-up: the exceptional curve is dominated by `ℙ¹`, so it is contracted, and the blow-up is a
proper birational morphism onto a normal variety, so `π_* 𝒪 = 𝒪`. -/
private theorem exists_comp_blowUpToBase_eq (hY : MMP.Mori.IsVariety k sY)
    (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    (hYp : MMP.Mori.IsProjectiveVariety k sY) {w : Y} (hw : IsClosed ({w} : Set Y))
    {E : Scheme.{u}} (sE : E ⟶ Spec (.of k)) [AlgebraicGeometry.IsCurve k sE]
    [AlgebraicGeometry.IsProjectiveVariety k sE] [Smooth sE] (hgE : 1 ≤ genus sE)
    (g : blowUp 𝓘[w, hw] ⟶ E) (hg : g ≫ sE = blowUpToBase 𝓘[w, hw] ≫ sY) :
    ∃ h : Y ⟶ E, blowUpToBase 𝓘[w, hw] ≫ h = g ∧ h ≫ sE = sY := by
  obtain ⟨hV', hs', hd', hp', hπp, hπb, hπs, hbir⟩ := blowUp_basic hY hYs hYd hYp hw
  haveI := hπp
  have hnormY : MMP.Mori.IsNormalVariety k sY :=
    ⟨hY, (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2⟩
  haveI : IsIso (blowUpToBase 𝓘[w, hw]).c := by
    have h := fun U => MMP.Mori.isIso_app_of_isProper_of_isBirationalMorphism
      (blowUpToBase 𝓘[w, hw] ≫ sY) sY hV' hnormY (blowUpToBase 𝓘[w, hw]) hπb U
    exact NatIso.isIso_of_isIso_app _
  obtain ⟨F, -, hFsupp, ⟨gℙ, hgℙ, hgℙη⟩, -⟩ := blowUp_exceptional hY hYs hYd hw
  obtain ⟨e, he⟩ := exists_forall_apply_eq_of_projectiveLine sE hgE (gℙ ≫ g) (by
    rw [Category.assoc, hg]; exact hgℙ)
  have heCl : IsClosed ({e} : Set E) := by
    haveI : JacobsonSpace (projectiveLine k) :=
      LocallyOfFiniteType.jacobsonSpace (projectiveLine k ↘ Spec (.of k))
    obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := projectiveLine k))
      isClosed_univ.isLocallyClosed
    have hz' : IsClosed ({z} : Set (projectiveLine k)) := hz
    set s := pointOfClosedPoint (projectiveLine k ↘ Spec (.of k)) z hz' ≫ gℙ ≫ g with hsdef
    have hs : s ≫ sE = 𝟙 _ := by
      rw [hsdef, Category.assoc, Category.assoc, hg, hgℙ, pointOfClosedPoint_comp]
    haveI := isClosedImmersion_of_comp_eq_id sE s hs
    have hrange : Set.range s.base = {e} := by
      ext y
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨a, rfl⟩
        rw [hsdef, Scheme.Hom.comp_apply, he]
      · rintro rfl
        obtain ⟨a⟩ : Nonempty (Spec (.of k) : Scheme.{u}) := inferInstance
        exact ⟨a, by rw [hsdef, Scheme.Hom.comp_apply, he]⟩
    rw [← hrange]
    exact s.isClosedEmbedding.isClosed_range
  have hconst : ∀ q, blowUpToBase 𝓘[w, hw] q = w → g q = e := by
    intro q hq
    have hqF : q ∈ F.support := (hFsupp q).2 hq
    have hsp : F.genericPoint ⤳ q := by
      rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have : e ⤳ g q := by
      rw [← he (genericPoint _), Scheme.Hom.comp_apply, hgℙη]
      exact hsp.map g.continuous
    have := specializes_iff_mem_closure.mp this
    rwa [heCl.closure_eq] at this
  have hfib : ∀ x x', blowUpToBase 𝓘[w, hw] x = blowUpToBase 𝓘[w, hw] x' → g x = g x' := by
    intro x x' hxx
    by_cases hx : blowUpToBase 𝓘[w, hw] x = w
    · rw [hconst x hx, hconst x' (hxx ▸ hx)]
    · rw [eq_of_mem_biregularLocus _ (hbir _ hx) hxx]
  obtain ⟨h, hh, -⟩ := MMP.existsUnique_comp_eq_of_isIso_c (blowUpToBase 𝓘[w, hw]) g hfib
  refine ⟨h, hh, ?_⟩
  obtain ⟨h', -, huniq⟩ := MMP.existsUnique_comp_eq_of_isIso_c (blowUpToBase 𝓘[w, hw]) (g ≫ sE)
    (fun x x' hxx => by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hfib x x' hxx])
  rw [huniq (h ≫ sE) (show _ ≫ (h ≫ sE) = g ≫ sE by rw [← Category.assoc, hh]),
    huniq sY hg.symm]

/-- The properties of a smooth projective surface over `k` are invariant under precomposing the
structure morphism with an isomorphism. -/
private theorem surface_facts_iso_comp {Y Y' : Scheme.{u}} (φ : Y' ≅ Y) {sY : Y ⟶ Spec (.of k)}
    (hY : MMP.Mori.IsVariety k sY) (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    (hYp : MMP.Mori.IsProjectiveVariety k sY) :
    MMP.Mori.IsVariety k (φ.hom ≫ sY) ∧ IsSmoothScheme (φ.hom ≫ sY) ∧
      topologicalKrullDim Y' = 2 ∧ MMP.Mori.IsProjectiveVariety k (φ.hom ≫ sY) := by
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI : IsSeparated sY := hY.toIsSeparated
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  haveI : QuasiCompact sY := hY.toQuasiCompact
  haveI : Nonempty Y' := ⟨φ.inv (Classical.arbitrary Y)⟩
  haveI : IsIntegral Y' := isIntegral_of_isOpenImmersion φ.hom
  have hV : MMP.Mori.IsVariety k (φ.hom ≫ sY) := ⟨⟩
  haveI : Smooth sY := smooth_of_isSmoothScheme hYs
  have hsm : IsSmoothScheme (φ.hom ≫ sY) := by
    refine top_le_iff.mp (le_sSup ?_)
    change Smooth ((⊤ : Y'.Opens).ι ≫ φ.hom ≫ sY)
    infer_instance
  refine ⟨hV, hsm, ?_, ?_⟩
  · rw [← hYd]; exact IsHomeomorph.topologicalKrullDim_eq _ φ.hom.homeomorph.isHomeomorph
  · obtain ⟨m, i, hi, hif⟩ := hYp.isProjective
    exact { toIsVariety := hV, isProjective := ⟨m, φ.hom ≫ i, inferInstance, by
      rw [Category.assoc, hif]⟩ }

/-- **Descent along a tower of point blow-ups.** A `k`-morphism to a smooth projective curve of
genus `≥ 1` from the top of a tower of blow-ups of closed points, starting at a smooth
projective surface, factors through the tower. -/
private theorem exists_comp_eq_of_pointBlowupTower {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsVariety k sX) (hXs : IsSmoothScheme sX) (hXd : topologicalKrullDim X = 2)
    (hXp : MMP.Mori.IsProjectiveVariety k sX)
    (n : ℕ) (S : ℕ → Scheme.{u}) (σ : ∀ i, S (i + 1) ⟶ S i) (e : S 0 ≅ X)
    (p : ∀ j : Fin n, S j) (hp : ∀ j : Fin n, IsClosed ({p j} : Set (S j)))
    (hσ : ∀ j : Fin n, ∃ φ : S (j + 1) ≅ blowUp 𝓘[p j, hp j],
      σ j = φ.hom ≫ blowUpToBase 𝓘[p j, hp j])
    {E : Scheme.{u}} (sE : E ⟶ Spec (.of k)) [AlgebraicGeometry.IsCurve k sE]
    [AlgebraicGeometry.IsProjectiveVariety k sE] [Smooth sE] (hgE : 1 ≤ genus sE)
    (g : S n ⟶ E)
    (hg : g ≫ sE = (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le n)).op ≫ e.hom ≫ sX) :
    ∃ G : X ⟶ E,
      (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le n)).op ≫ e.hom ≫ G = g ∧
        G ≫ sE = sX ∧
        Function.Surjective ((Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le n)).op ≫
          e.hom).base := by
  -- `N j : S j ⟶ S 0` and the structure morphisms `sS j`
  let N : ∀ j, S j ⟶ S 0 := fun j => (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le j)).op
  have hN : ∀ j, N (j + 1) = σ j ≫ N j := fun j => by
    have h := (Functor.ofOpSequence σ).map_comp (homOfLE (Nat.le_succ j)).op
      (homOfLE (Nat.zero_le j)).op
    rwa [Functor.ofOpSequence_map_homOfLE_succ] at h
  have hN0 : N 0 = 𝟙 _ := by
    change (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le 0)).op = 𝟙 _
    rw [show (homOfLE (Nat.zero_le 0)).op = 𝟙 (Opposite.op 0) from rfl,
      (Functor.ofOpSequence σ).map_id]
  let sS : ∀ j, S j ⟶ Spec (.of k) := fun j => N j ≫ e.hom ≫ sX
  have hsS : ∀ j, sS (j + 1) = σ j ≫ sS j := fun j => by
    change N (j + 1) ≫ e.hom ≫ sX = σ j ≫ N j ≫ e.hom ≫ sX
    rw [hN, Category.assoc]
  -- every stage is a smooth projective surface
  have good : ∀ j, j ≤ n → MMP.Mori.IsVariety k (sS j) ∧ IsSmoothScheme (sS j) ∧
      topologicalKrullDim (S j) = 2 ∧ MMP.Mori.IsProjectiveVariety k (sS j) := by
    intro j
    induction j with
    | zero =>
      intro _
      have : sS 0 = e.hom ≫ sX := by
        change N 0 ≫ e.hom ≫ sX = _
        rw [hN0, Category.id_comp]
      rw [this]
      exact surface_facts_iso_comp e hX hXs hXd hXp
    | succ j ih =>
      intro hj
      obtain ⟨hV, hs, hd, hpr⟩ := ih (by omega)
      obtain ⟨φ, hφ⟩ := hσ ⟨j, by omega⟩
      obtain ⟨hV', hs', hd', hp', -⟩ := blowUp_basic hV hs hd hpr (hp ⟨j, by omega⟩)
      rw [hsS, show σ j = _ from hφ, Category.assoc]
      exact surface_facts_iso_comp φ hV' hs' hd' hp'
  -- descending the tower
  let M : ∀ j, j ≤ n → (S n ⟶ S j) := fun j hj => (Functor.ofOpSequence σ).map (homOfLE hj).op
  have hM : ∀ j (hj : j + 1 ≤ n), M j (by omega) = M (j + 1) hj ≫ σ j := fun j hj => by
    have h := (Functor.ofOpSequence σ).map_comp (homOfLE hj).op (homOfLE (Nat.le_succ j)).op
    rwa [Functor.ofOpSequence_map_homOfLE_succ] at h
  have hMn : M n le_rfl = 𝟙 _ := by
    change (Functor.ofOpSequence σ).map (homOfLE (le_refl n)).op = 𝟙 _
    rw [show (homOfLE (le_refl n)).op = 𝟙 (Opposite.op n) from rfl,
      (Functor.ofOpSequence σ).map_id]
  have key : ∀ m j (hj : j + m = n), ∃ gj : S j ⟶ E, M j (by omega) ≫ gj = g ∧
      gj ≫ sE = sS j ∧ Function.Surjective (M j (by omega)).base := by
    intro m
    induction m with
    | zero =>
      intro j hj
      subst hj
      exact ⟨g, by rw [hMn, Category.id_comp], hg, by rw [hMn]; exact Function.surjective_id⟩
    | succ m ih =>
      intro j hjm
      have hj : j + 1 ≤ n := by omega
      obtain ⟨g1, hM1, hs1, hsurj1⟩ := ih (j + 1) (by omega)
      obtain ⟨hV, hs, hd, hpr⟩ := good j (by omega)
      obtain ⟨φ, hφ⟩ := hσ ⟨j, hj⟩
      have hφ' : σ j = φ.hom ≫ blowUpToBase 𝓘[p ⟨j, hj⟩, hp ⟨j, hj⟩] := hφ
      obtain ⟨h, hh, hhs⟩ := exists_comp_blowUpToBase_eq hV hs hd hpr (hp ⟨j, hj⟩) sE hgE
        (φ.inv ≫ g1) (by
          rw [Category.assoc, hs1, hsS, hφ', Category.assoc, Iso.inv_hom_id_assoc])
      obtain ⟨-, -, -, -, -, -, hπs, -⟩ := blowUp_basic hV hs hd hpr (hp ⟨j, hj⟩)
      refine ⟨h, ?_, hhs, ?_⟩
      · rw [hM j hj, Category.assoc, hφ', Category.assoc, hh, Iso.hom_inv_id_assoc, hM1]
      · intro x
        obtain ⟨a, ha⟩ := hπs.surj x
        obtain ⟨b, hb⟩ := φ.hom.homeomorph.surjective a
        obtain ⟨c, hc⟩ := hsurj1 b
        refine ⟨c, ?_⟩
        rw [hM j hj, hφ', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hc]
        change blowUpToBase _ (φ.hom.homeomorph b) = x
        rw [hb, ha]
  obtain ⟨g0, hg0, hg0s, hsurj0⟩ := key n 0 (by omega)
  have hs0 : sS 0 = e.hom ≫ sX := by
    change N 0 ≫ e.hom ≫ sX = _; rw [hN0, Category.id_comp]
  refine ⟨e.inv ≫ g0, ?_, ?_, ?_⟩
  · show M 0 (Nat.zero_le n) ≫ e.hom ≫ e.inv ≫ g0 = g
    rw [Iso.hom_inv_id_assoc]; exact hg0
  · rw [Category.assoc, hg0s, hs0, Iso.inv_hom_id_assoc]
  · exact e.hom.homeomorph.surjective.comp hsurj0

end Descent

section Rigidity

variable {k : Type u} [Field k]

/-- A morphism from a `k`-scheme with `Γ(T, 𝒪_T) = k` to an affine scheme is constant. -/
private theorem apply_eq_of_isAffine {T A : Scheme.{u}} [IsAffine A] (sT : T ⟶ Spec (.of k))
    (hT : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ sT.appTop)) (h : T ⟶ A) (a b : T) :
    h a = h b := by
  have hnat := Scheme.toSpecΓ_naturality h
  have hsub : Subsingleton (Spec Γ(T, ⊤)) := by
    let e : Γ(T, ⊤) ≅ CommRingCat.of k := (asIso ((Scheme.ΓSpecIso (.of k)).inv ≫ sT.appTop)).symm
    have : IsIso (Spec.map e.hom) := inferInstance
    refine ⟨fun x y => (Spec.map e.inv).homeomorph.injective ?_⟩
    exact Subsingleton.elim _ _
  have hinj : Function.Injective A.toSpecΓ.base := A.toSpecΓ.homeomorph.injective
  apply hinj
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hnat]
  simp only [Scheme.Hom.comp_apply]
  rw [Subsingleton.elim (T.toSpecΓ a) (T.toSpecΓ b)]

variable [IsAlgClosed k]

/-- On a product over an algebraically closed field, a morphism which is constant along the
fibre `{c₀} × T`, as a morphism, takes the constant value at every closed point over `c₀`. -/
private theorem apply_eq_of_lift_comp_eq {C T E : Scheme.{u}} (sC : C ⟶ Spec (.of k))
    (sT : T ⟶ Spec (.of k)) [LocallyOfFiniteType sC] [LocallyOfFiniteType sT]
    (G : pullback sC sT ⟶ E) (c₀ : Spec (.of k) ⟶ C) (hc₀ : c₀ ≫ sC = 𝟙 _)
    (y₀ : Spec (.of k) ⟶ E)
    (hy : pullback.lift (sT ≫ c₀) (𝟙 T) (by rw [Category.assoc, hc₀, Category.comp_id,
      Category.id_comp]) ≫ G = sT ≫ y₀)
    (z : (pullback sC sT : Scheme.{u})) (hz : IsClosed ({z} : Set (pullback sC sT : Scheme.{u})))
    (pt : Spec (.of k)) (hzc : pullback.fst sC sT z = c₀ pt) : G z = y₀ pt := by
  set xpt := pointOfClosedPoint (pullback.fst sC sT ≫ sC) z hz with hxpt
  have hcpt : xpt ≫ pullback.fst sC sT = c₀ := by
    refine ext_of_apply_closedPoint_eq sC ?_ hc₀ ?_
    · rw [Category.assoc]; exact pointOfClosedPoint_comp _ _ _
    · have h1 : ∀ a : (Spec (.of k) : Scheme.{u}), (xpt ≫ pullback.fst sC sT) a = c₀ a :=
        fun a => by
          rw [Scheme.Hom.comp_apply, hxpt, pointOfClosedPoint_apply, hzc]
          congr 1; exact Subsingleton.elim _ _
      exact h1 _
  set tpt := xpt ≫ pullback.snd sC sT with htpt
  have htpt' : tpt ≫ sT = 𝟙 _ := by
    rw [htpt, Category.assoc, ← pullback.condition, ← Category.assoc, hcpt, hc₀]
  have hxj : xpt = tpt ≫ pullback.lift (sT ≫ c₀) (𝟙 T) (by rw [Category.assoc, hc₀,
      Category.comp_id, Category.id_comp]) := pullback.hom_ext (by
        rw [Category.assoc, pullback.lift_fst, ← Category.assoc, htpt', Category.id_comp, hcpt])
      (by rw [Category.assoc, pullback.lift_snd, Category.comp_id])
  have e1 : z = xpt pt := by rw [hxpt, pointOfClosedPoint_apply]
  rw [e1, ← Scheme.Hom.comp_apply, hxj, Category.assoc, hy, ← Category.assoc, htpt',
    Category.id_comp]

/-- **Rigidity on a product.** Let `T` be a proper `k`-scheme with `Γ(T, 𝒪_T) = k` and
`G : C ×_k T ⟶ E` a `k`-morphism to a separated `k`-scheme of finite type, on an integral
product. If `G` maps every closed point of the fibre over `c₀ ∈ C` to one point `y`, then `G`
factors through the first projection: `G = pr₁ ≫ (id, t₀) ≫ G` for every `k`-point `t₀` of `T`. -/
private theorem eq_fst_comp_lift_comp {C T E : Scheme.{u}} (sC : C ⟶ Spec (.of k))
    (sT : T ⟶ Spec (.of k)) (sE : E ⟶ Spec (.of k)) [LocallyOfFiniteType sC] [IsProper sT]
    [Nonempty T] [IsSeparated sE] [LocallyOfFiniteType sE] [IsIntegral (pullback sC sT)]
    (hT : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ sT.appTop))
    (G : pullback sC sT ⟶ E) (hG : G ≫ sE = pullback.fst sC sT ≫ sC)
    (c₀ : Spec (.of k) ⟶ C) (hc₀ : c₀ ≫ sC = 𝟙 _) (y₀ : Spec (.of k) ⟶ E)
    (hy : pullback.lift (sT ≫ c₀) (𝟙 T) (by rw [Category.assoc, hc₀, Category.comp_id,
      Category.id_comp]) ≫ G = sT ≫ y₀)
    (t₀ : Spec (.of k) ⟶ T) (ht₀ : t₀ ≫ sT = 𝟙 _) :
    G = pullback.fst sC sT ≫ pullback.lift (𝟙 C) (sC ≫ t₀) (by simp [ht₀]) ≫ G := by
  classical
  obtain ⟨pt₀⟩ : Nonempty (Spec (.of k) : Scheme.{u}) := inferInstance
  haveI : IsClosedImmersion c₀ := isClosedImmersion_of_comp_eq_id sC c₀ hc₀
  have hc₀cl : IsClosed ({c₀ pt₀} : Set C) := by
    have : Set.range c₀.base = {c₀ pt₀} := by
      ext y; simp only [Set.mem_range, Set.mem_singleton_iff]
      exact ⟨fun ⟨a, ha⟩ => ha ▸ congrArg _ (Subsingleton.elim _ _), fun h => ⟨pt₀, h.symm⟩⟩
    rw [← this]; exact c₀.isClosedEmbedding.isClosed_range
  set y := y₀ pt₀ with hydef
  have hy' : ∀ z, IsClosed ({z} : Set (pullback sC sT : Scheme.{u})) →
      pullback.fst sC sT z = c₀ pt₀ → G z = y := fun z hz hzc =>
    apply_eq_of_lift_comp_eq sC sT G c₀ hc₀ y₀ hy z hz pt₀ hzc
  set pr₁ := pullback.fst sC sT with hpr₁
  set pr₂ := pullback.snd sC sT with hpr₂
  obtain ⟨A, hA', hyA⟩ : ∃ A : E.Opens, IsAffineOpen A ∧ y ∈ A := by
    obtain ⟨A, hA, hyA, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp E.isBasis_affineOpens)
      (show y ∈ (⊤ : E.Opens) from trivial)
    exact ⟨A, hA, hyA⟩
  obtain ⟨pt⟩ : Nonempty (Spec (.of k) : Scheme.{u}) := inferInstance
  set Zc : Set (pullback sC sT : Scheme.{u}) := (G.base ⁻¹' (A : Set E))ᶜ with hZcdef
  have hZc : IsClosed Zc := (A.isOpen.preimage G.continuous).isClosed_compl
  set Zp : Set C := pr₁.base '' Zc with hZpdef
  have hZp : IsClosed Zp := pr₁.isClosedMap _ hZc
  haveI : LocallyOfFiniteType (pr₁ ≫ sC) := inferInstance
  haveI : JacobsonSpace (pullback sC sT : Scheme.{u}) :=
    LocallyOfFiniteType.jacobsonSpace (pr₁ ≫ sC)
  have hc₀' : c₀ pt₀ ∉ Zp := by
    rintro ⟨z, hz, hzc⟩
    have hcl : IsClosed (Zc ∩ pr₁.base ⁻¹' {c₀ pt₀}) :=
      hZc.inter (IsClosed.preimage pr₁.continuous hc₀cl)
    obtain ⟨z', ⟨hz'Z, hz'c⟩, hz'cl⟩ :=
      nonempty_inter_closedPoints (⟨z, hz, hzc⟩ : (Zc ∩ pr₁.base ⁻¹' {c₀ pt₀}).Nonempty)
        hcl.isLocallyClosed
    exact hz'Z (by
      change G z' ∈ (A : Set E)
      rw [hy' z' hz'cl hz'c]; exact hyA)
  set O : Set (pullback sC sT : Scheme.{u}) := pr₁.base ⁻¹' Zpᶜ with hOdef
  have hO : IsOpen O := hZp.isOpen_compl.preimage pr₁.continuous
  have hOne : O.Nonempty := by
    obtain ⟨z, hz⟩ := pr₁.surjective (c₀ pt₀)
    exact ⟨z, by rw [hOdef, Set.mem_preimage, hz]; exact hc₀'⟩
  haveI : LocallyOfFiniteType (G ≫ sE) := by rw [hG]; infer_instance
  haveI : IsReduced (pullback sC sT : Scheme.{u}) := isReduced_of_isIntegral _
  refine ext_of_apply_eq sE O hO.isLocallyClosed (hO.dense hOne) ?_ ?_
  · intro x hxO hxcl
    set xpt := pointOfClosedPoint (pr₁ ≫ sC) x hxcl with hxpt
    set cpt := xpt ≫ pr₁ with hcptdef
    set tpt := xpt ≫ pr₂ with htptdef
    have hcpt : cpt ≫ sC = 𝟙 _ := by
      rw [hcptdef, Category.assoc]; exact pointOfClosedPoint_comp _ _ _
    have htpt : tpt ≫ sT = 𝟙 _ := by
      rw [htptdef, Category.assoc, hpr₂, ← pullback.condition, ← Category.assoc]; exact hcpt
    let j : T ⟶ pullback sC sT := pullback.lift (sT ≫ cpt) (𝟙 T) (by
      rw [Category.assoc, hcpt, Category.comp_id, Category.id_comp])
    have hxj : xpt = tpt ≫ j := pullback.hom_ext (by
        simp only [j, Category.assoc, pullback.lift_fst]
        rw [← Category.assoc, htpt, Category.id_comp]) (by
        simp only [j, Category.assoc, pullback.lift_snd, Category.comp_id]; rfl)
    have hsj : cpt ≫ pullback.lift (𝟙 C) (sC ≫ t₀) (by simp [ht₀]) = t₀ ≫ j :=
      pullback.hom_ext (by
        simp only [j, Category.assoc, pullback.lift_fst, Category.comp_id]
        rw [← Category.assoc, ht₀, Category.id_comp]) (by
        simp only [j, Category.assoc, pullback.lift_snd, Category.comp_id]
        rw [← Category.assoc, hcpt, Category.id_comp])
    have e2 : pr₁ x = cpt pt := by
      rw [hcptdef, Scheme.Hom.comp_apply, hxpt, pointOfClosedPoint_apply]
    have hjA : Set.range (j ≫ G).base ⊆ Set.range A.ι.base := by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι]
      by_contra hn
      have hjt : j t ∈ Zc := hn
      have : pr₁ (j t) = pr₁ x := by
        rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, e2]
        congr 1; exact Subsingleton.elim _ _
      exact hxO (this ▸ ⟨j t, hjt, rfl⟩)
    let h : T ⟶ A := IsOpenImmersion.lift A.ι (j ≫ G) hjA
    have hh : h ≫ A.ι = j ≫ G := IsOpenImmersion.lift_fac _ _ _
    haveI : IsAffine A := hA'
    have key := apply_eq_of_isAffine sT hT h (tpt pt) (t₀ pt)
    have e1 : x = j (tpt pt) := by
      rw [← Scheme.Hom.comp_apply, ← hxj, hxpt, pointOfClosedPoint_apply]
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, e2]
    have e3 : (pullback.lift (𝟙 C) (sC ≫ t₀) (by simp [ht₀]) ≫ G) (cpt pt) = (j ≫ G) (t₀ pt) := by
      rw [← Scheme.Hom.comp_apply, ← Category.assoc, hsj, Category.assoc, Scheme.Hom.comp_apply]
    rw [← Scheme.Hom.comp_apply, e3, e1, ← Scheme.Hom.comp_apply j G, ← hh,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact congrArg A.ι.base key
  · rw [hG, Category.assoc, Category.assoc, hG, pullback.lift_fst_assoc, Category.id_comp]

/-- **Rigidity of a family of maps to a curve of positive genus.** Let `C`, `T` be smooth proper
connected curves over `k`, `T° ⊆ T` a nonempty open, and `G : C ×_k T° ⟶ E` a family of maps
to a smooth projective curve of genus `≥ 1` contracting `{P} × T°` to a point. Then all the
maps `G(-, t)` at `k`-points `t` of `T°` coincide. The rational map `C × T ⇢ E` is resolved by
point blow-ups, descends to a morphism on `C × T` because rational curves are contracted, and is
then independent of `t` by the rigidity lemma. -/
private theorem lift_comp_eq_of_contracts {C T E : Scheme.{u}} (sC : C ⟶ Spec (.of k))
    (sT : T ⟶ Spec (.of k)) (sE : E ⟶ Spec (.of k))
    [IsProper sC] [Smooth sC] [ConnectedSpace C] (hC : topologicalKrullDim C = 1)
    [IsProper sT] [Smooth sT] [ConnectedSpace T] (hT : topologicalKrullDim T = 1)
    [AlgebraicGeometry.IsCurve k sE] [AlgebraicGeometry.IsProjectiveVariety k sE] [Smooth sE]
    (hgE : 1 ≤ genus sE) (W : T.Opens) (hW : (W : Set T).Nonempty)
    (G : pullback sC (W.ι ≫ sT) ⟶ E) (hG : G ≫ sE = pullback.fst sC (W.ι ≫ sT) ≫ sC)
    (P : C) (hP : IsClosed ({P} : Set C))
    (hconst : ∃ v : E, ∀ z, pullback.fst sC (W.ι ≫ sT) z = P → G z = v)
    (t₀ t₁ : Spec (.of k) ⟶ W) (ht₀ : t₀ ≫ W.ι ≫ sT = 𝟙 _) (ht₁ : t₁ ≫ W.ι ≫ sT = 𝟙 _) :
    pullback.lift (𝟙 C) (sC ≫ t₀) (by simp [ht₀]) ≫ G =
      pullback.lift (𝟙 C) (sC ≫ t₁) (by simp [ht₁]) ≫ G := by
  classical
  obtain ⟨hXv, hXs, hXd, hXp⟩ := product_facts sC sT hC hT
  haveI : IsIntegral (pullback sC sT : Scheme.{u}) := hXv.toIsIntegral
  haveI : AlgebraicGeometry.IsVariety k sT := isVariety_of_smooth_of_connected sT
  haveI : AlgebraicGeometry.IsCurve k sT := ⟨hT⟩
  haveI : AlgebraicGeometry.IsVariety k sC := isVariety_of_smooth_of_connected sC
  set D : (pullback sC sT : Scheme.{u}).Opens := (pullback.snd sC sT) ⁻¹ᵁ W with hD
  set ψ : (D : Scheme.{u}) ⟶ E := (restrictProductIso sC sT W).hom ≫ G with hψ
  have hDne : (D : Set (pullback sC sT : Scheme.{u})).Nonempty := by
    obtain ⟨t, ht⟩ := hW
    obtain ⟨z, hz⟩ := (pullback.snd sC sT).surjective t
    exact ⟨z, by rw [hD]; change pullback.snd sC sT z ∈ W; rw [hz]; exact ht⟩
  let f : (pullback sC sT : Scheme.{u}).PartialMap E := ⟨D, D.isOpen.dense hDne, ψ⟩
  have hf : f.hom ≫ sE = f.domain.ι ≫ pullback.fst sC sT ≫ sC := by
    change ((restrictProductIso sC sT W).hom ≫ G) ≫ sE = D.ι ≫ pullback.fst sC sT ≫ sC
    rw [Category.assoc, hG, restrictProductIso_hom_fst_assoc]
  obtain ⟨n, S, σ, e, p, hp, hσ, ⟨g, hg1, hg2⟩, -⟩ :=
    MMP.Fourfold.exists_pointBlowups_comp_eq_of_partialMap k
      (pullback.fst sC sT ≫ sC) sE hXp hXs hXd
      (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k)) f hf
  obtain ⟨G', hG'1, hG'2, hsurj⟩ :=
    exists_comp_eq_of_pointBlowupTower hXv hXs hXd hXp n S σ e p hp hσ sE hgE g hg1
  let π : S n ⟶ (pullback sC sT : Scheme.{u}) :=
    (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le n)).op ≫ e.hom
  have hπG : π ≫ G' = g := (Category.assoc _ _ _).trans hG'1
  have hsurj' : Function.Surjective π.base := hsurj
  have hg2' : (π ⁻¹ᵁ D).ι ≫ g = (π ∣_ D) ≫ ψ := hg2
  -- `G'` extends the family on `D`
  haveI : IsReduced (pullback sC sT : Scheme.{u}) := isReduced_of_isIntegral _
  haveI : IsReduced (D : Scheme.{u}) := isReduced_of_isOpenImmersion D.ι
  have hext : D.ι ≫ G' = ψ := by
    haveI : LocallyOfFiniteType ((D.ι ≫ G') ≫ sE) := by
      rw [Category.assoc, hG'2]; infer_instance
    refine ext_of_apply_eq sE Set.univ isOpen_univ.isLocallyClosed dense_univ
      (fun d _ _ => ?_) ?_
    · obtain ⟨s, hs⟩ := hsurj' (D.ι d)
      have hsD : s ∈ π ⁻¹ᵁ D := by
        change π s ∈ D
        rw [hs]; exact d.2
      let s' : (π ⁻¹ᵁ D).toScheme := ⟨s, hsD⟩
      have hs' : (π ⁻¹ᵁ D).ι s' = s := rfl
      have h1 : g ((π ⁻¹ᵁ D).ι s') = ψ ((π ∣_ D) s') := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
        exact congrArg (fun φ => φ.base s') hg2'
      have h2 : (π ∣_ D) s' = d := by
        apply D.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hs']
        exact hs
      rw [Scheme.Hom.comp_apply, ← hs, ← Scheme.Hom.comp_apply π G', hπG, ← hs', h1, h2]
    · rw [Category.assoc, hG'2, hψ, Category.assoc, hG, restrictProductIso_hom_fst_assoc]
  -- the fibre over `P` is contracted, as a morphism
  obtain ⟨v, hv⟩ := hconst
  set c₀ := pointOfClosedPoint sC P hP with hc₀def
  have hc₀ : c₀ ≫ sC = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have hc₀pt : ∀ a, c₀ a = P := fun a => pointOfClosedPoint_apply _ _ _ a
  set y₀ := c₀ ≫ pullback.lift (𝟙 C) (sC ≫ t₀) (by simp [ht₀]) ≫ G with hy₀
  have hy₀v : ∀ a, y₀ a = v := fun a => by
    rw [hy₀, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    apply hv
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hc₀pt a
  set jP : T ⟶ pullback sC sT := pullback.lift (sT ≫ c₀) (𝟙 T) (by
    rw [Category.assoc, hc₀, Category.comp_id, Category.id_comp]) with hjP
  haveI : IsIntegral T := inferInstance
  have hfib : jP ≫ G' = sT ≫ y₀ := by
    haveI : LocallyOfFiniteType ((jP ≫ G') ≫ sE) := by
      rw [Category.assoc, hG'2, ← Category.assoc, hjP, pullback.lift_fst, Category.assoc, hc₀,
        Category.comp_id]
      infer_instance
    refine ext_of_apply_eq sE (W : Set T) W.isOpen.isLocallyClosed (W.isOpen.dense hW)
      (fun t ht _ => ?_) ?_
    · have htD : jP t ∈ D := by
        change pullback.snd sC sT (jP t) ∈ W
        rw [← Scheme.Hom.comp_apply, hjP, pullback.lift_snd]
        exact ht
      let d : (D : Scheme.{u}) := ⟨jP t, htD⟩
      have hd : G' (jP t) = ψ d := by
        rw [← hext]; rfl
      rw [Scheme.Hom.comp_apply, hd, hψ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy₀v]
      apply hv
      rw [← Scheme.Hom.comp_apply, restrictProductIso_hom_fst, Scheme.Hom.comp_apply]
      change pullback.fst sC sT (jP t) = P
      rw [← Scheme.Hom.comp_apply, hjP, pullback.lift_fst, Scheme.Hom.comp_apply, hc₀pt]
    · rw [Category.assoc, hG'2, ← Category.assoc, hjP, pullback.lift_fst, Category.assoc, hc₀,
        Category.comp_id, Category.assoc, hy₀, Category.assoc, Category.assoc, hG,
        pullback.lift_fst_assoc, Category.id_comp, hc₀, Category.comp_id]
  -- the rigidity lemma
  haveI : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ sT.appTop) :=
    GenusOne.isIso_globalSections_of_isAlgClosed sT
  have hM := eq_fst_comp_lift_comp sC sT sE inferInstance G' hG'2 c₀ hc₀ y₀ hfib (t₀ ≫ W.ι)
    (by rw [Category.assoc]; exact ht₀)
  have hGG' : G = (restrictProductIso sC sT W).inv ≫ D.ι ≫ G' := by
    rw [hext, hψ, Iso.inv_hom_id_assoc]
  have hsec : ∀ (t : Spec (.of k) ⟶ W) (ht : t ≫ W.ι ≫ sT = 𝟙 _),
      pullback.lift (𝟙 C) (sC ≫ t) (by simp [ht]) ≫ G =
        pullback.lift (𝟙 C) (sC ≫ t ≫ W.ι) (by simp [ht]) ≫ G' := by
    intro t ht
    rw [hGG']
    simp only [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, ← restrictProductIso_hom_fst, Iso.inv_hom_id_assoc,
        pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, Category.assoc, ← restrictProductIso_hom_snd, Iso.inv_hom_id_assoc,
        pullback.lift_snd_assoc, pullback.lift_snd, Category.assoc]
  rw [hsec t₀ ht₀, hsec t₁ ht₁, hM]
  simp only [← Category.assoc, pullback.lift_fst, Category.id_comp]

end Rigidity

section TangentEuler

open Stacks.AlgebraicGeometry.ReflexiveModules

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **The Euler characteristic of the pulled-back tangent sheaf.** For a smooth projective curve
`C`, a scheme `U` smooth of relative dimension `n` over `k` and `f : C ⟶ U`, the sheaf
`f^* T_U = f^*(Ω_{U/k})^∨` has `χ = -deg f^* ω_U + n (1 - g)`: Riemann–Roch for the rank-`n`
bundle, and `det (Ω^∨) ⊗ det Ω ≅ 𝒪` through the determinant pairing. -/
private theorem eulerCharacteristic_pullback_dualSheaf_relativeDifferentials
    {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) [AlgebraicGeometry.IsCurve k sC]
    [AlgebraicGeometry.IsProjectiveVariety k sC] [Smooth sC]
    (sU : U ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n sU] (f : C ⟶ U) :
    haveI : Stacks.Ample.IsInvertibleModule U (Scheme.Hom.relativeDifferentialForms sU n) :=
      Stacks.Discriminant.isInvertible_relativeDifferentialForms sU n
    ∃ _ : ((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsCoherent,
      eulerCharacteristic k sC ((Scheme.Modules.pullback f).obj
          (dualSheaf sU.relativeDifferentials)) =
        -invertibleCurveDegree k sC (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one
            (f := sC)).le
          ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms sU n)) +
          n * (1 - genus sC) := by
  haveI : Stacks.Ample.IsInvertibleModule U (Scheme.Hom.relativeDifferentialForms sU n) :=
    Stacks.Discriminant.isInvertible_relativeDifferentialForms sU n
  have hdim := (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := sC)).le
  set Ω := sU.relativeDifferentials with hΩdef
  haveI hΩ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Ω n :=
    Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials sU n
  haveI hD : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualSheaf Ω) n :=
    isFiniteLocallyFreeOfRank_dualSheaf Ω n hΩ
  haveI hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj (dualSheaf Ω)) n :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f _ n
  haveI hcoh : ((Scheme.Modules.pullback f).obj (dualSheaf Ω)).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k sC _ n
  refine ⟨hcoh, ?_⟩
  rw [MMP.Fourfold.eulerCharacteristic_eq_curveDegree_exteriorPower_add sC _ n]
  congr 1
  -- the two determinant lines on `C`
  set A := (dualSheaf Ω).exteriorPower n with hA
  set B := Ω.exteriorPower n with hB
  haveI hA1 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} A 1 := by
    simpa only [Nat.choose_self] using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower
      (dualSheaf Ω) n n
  haveI hB1 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} B 1 := by
    simpa only [Nat.choose_self] using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower Ω n n
  haveI hfA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj A) 1 :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f _ 1
  haveI hfB : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj B) 1 :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f _ 1
  haveI hEn : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback f).obj (dualSheaf Ω)).exteriorPower n) 1 := by
    simpa only [Nat.choose_self] using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower
      ((Scheme.Modules.pullback f).obj (dualSheaf Ω)) n n
  rw [curveDegree_eq_of_iso k sC hdim 1 (Scheme.Modules.exteriorPowerPullbackIso f _ n).symm]
  -- the determinant pairing on `U`, pulled back to `C`
  haveI := @Stacks.Duality.isIso_detDualPairing U.toTopCat U.sheaf Ω
    (SheafOfModules.algebras _ (dualSheaf Ω)) (SheafOfModules.algebras _ Ω) n hΩ
  let ε := asIso (Stacks.Duality.detDualPairing (SheafOfModules.algebras _ (dualSheaf Ω))
    (SheafOfModules.algebras _ Ω) n)
  let T : C.Modules := ((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨C.toRingedSpace.presheaf, C.toRingedSpace.IsSheaf⟩).obj
      ((Scheme.Modules.pullback f).obj A)).obj ((Scheme.Modules.pullback f).obj B)
  haveI hT : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T (1 * 1) :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf C ((Scheme.Modules.pullback f).obj A)
      ((Scheme.Modules.pullback f).obj B) 1 1
  let e : T ≅ SheafOfModules.unit C.ringCatSheaf :=
    ((Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).app (A, B)).symm ≪≫
      (Scheme.Modules.pullback f).mapIso ε ≪≫ Scheme.Modules.pullbackUnitIso f
  have h1 := curveDegree_tensorSheaf_eq_add k sC hdim ((Scheme.Modules.pullback f).obj A)
    ((Scheme.Modules.pullback f).obj B) 1 1
  haveI hO : SheafOfModules.IsCoherent (SheafOfModules.unit C.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k sC
  have h2 : curveDegree k sC hdim T (1 * 1) = 0 := by
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (SheafOfModules.unit C.ringCatSheaf) (1 * 1) :=
      SheafOfModules.isFiniteLocallyFreeOfRank_unit C
    rw [curveDegree_eq_of_iso k sC hdim (1 * 1) e]
    exact curveDegree_unit_eq_zero k sC hdim
  rw [invertibleCurveDegree_eq_curveDegree_one]
  change curveDegree k sC hdim T (1 * 1) = _ at h1
  have h3 : curveDegree k sC hdim ((Scheme.Modules.pullback f).obj B) 1 =
      curveDegree k sC hdim ((Scheme.Modules.pullback f).obj
        (Scheme.Hom.relativeDifferentialForms sU n)) 1 := rfl
  have key : curveDegree k sC hdim ((Scheme.Modules.pullback f).obj A) 1 +
      curveDegree k sC hdim ((Scheme.Modules.pullback f).obj B) 1 = 0 := by
    rw [← h2, h1]; ring
  rw [h3] at key
  change curveDegree k sC hdim ((Scheme.Modules.pullback f).obj A) 1 =
    -curveDegree k sC hdim ((Scheme.Modules.pullback f).obj
      (Scheme.Hom.relativeDifferentialForms sU n)) 1
  linarith

end TangentEuler

section TangentRestrict

open Stacks.AlgebraicGeometry.ReflexiveModules

variable {k : Type u} [Field k]

/-- The tangent sheaf of an open subscheme `U' ⊆ U` pulled back along `f : C ⟶ U'` is the tangent
sheaf of `U` pulled back along `C ⟶ U`. -/
private noncomputable def pullbackDualSheafRelativeDifferentialsIso {C U U' : Scheme.{u}}
    (sU : U ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n sU] (j : U' ⟶ U)
    [IsOpenImmersion j] (f : C ⟶ U') :
    (Scheme.Modules.pullback f).obj (dualSheaf (j ≫ sU).relativeDifferentials) ≅
      (Scheme.Modules.pullback (f ≫ j)).obj (dualSheaf sU.relativeDifferentials) := by
  haveI := Scheme.Hom.isIso_relativeDifferentialsMap_of_isOpenImmersion j sU (j ≫ sU) (𝟙 _)
    (Category.comp_id (j ≫ sU)).symm
  have hlf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      sU.relativeDifferentials :=
    haveI := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials sU n
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ n
  exact (Scheme.Modules.pullback f).mapIso
      (dualSheafIsoOfIso (asIso (j.relativeDifferentialsMap sU (j ≫ sU) (𝟙 _)
        (Category.comp_id (j ≫ sU)).symm)) ≪≫
      (@asIso _ _ _ _ (Stacks.Chow.pullbackDualMap j sU.relativeDifferentials)
        (Stacks.Chow.pullbackDualMap_isIso j _ hlf)).symm) ≪≫
    (Scheme.Modules.pullbackComp f j).app _

end TangentRestrict

section DegreeConstancy

open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

private theorem isFlatOver_of_isInvertibleModule {X S : Scheme.{u}} (π : X ⟶ S) [Flat π]
    (F : X.Modules) [Stacks.Ample.IsInvertibleModule X F] :
    IsFlatOver π.toLRSHom.toShHom F := by
  have h0 : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf _ _).mp ‹_›
  have : F.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule F
  have hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry F).mp
      (@Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ F h0)
  obtain ⟨-, hfree⟩ :=
    ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae F).out 4 2).mp hflf
  intro x
  letI := (π.stalkMap x).hom.toAlgebra
  have : Module.Flat (S.presheaf.stalk (π x)) (X.presheaf.stalk x) := Flat.stalkMap π x
  have := hfree x
  letI : Module (S.presheaf.stalk (π x)) (F.presheaf.stalk x) :=
    Module.compHom _ (π.stalkMap x).hom
  have : IsScalarTower (S.presheaf.stalk (π x)) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat (X.presheaf.stalk x) (F.presheaf.stalk x) := Module.Flat.of_free
  exact Module.Flat.trans (S.presheaf.stalk (π x)) (X.presheaf.stalk x) (F.presheaf.stalk x)

variable {k : Type u} [Field k]

/-- The Euler characteristic of an invertible module on `C ×ₖ W`, restricted to the slice
`C × {t}` of a `k`-point `t` of `W`, is the fibre Euler characteristic at `t`. -/
private theorem eulerSum_pullback_lift_eq {C W : Scheme.{u}} (sC : C ⟶ Spec (.of k))
    [IsProper sC] [Flat sC] [LocallyOfFinitePresentation sC] (sW : W ⟶ Spec (.of k))
    (F : (pullback sC sW).Modules) [Stacks.Ample.IsInvertibleModule _ F]
    (t : Spec (.of k) ⟶ W) (ht : t ≫ sW = 𝟙 _) (pt : Spec (.of k)) :
    eulerSum k sC ((Scheme.Modules.pullback
        (pullback.lift (𝟙 C) (sC ≫ t) (by simp [ht]))).obj F) =
      fibreEulerCharacteristic (pullback.snd sC sW) F (t pt) := by
  have hfp : FinitePresentation (pullback.snd sC sW) :=
    ⟨inferInstance, inferInstanceAs (QuasiCompact (pullback.snd sC sW)),
      @IsSeparated.instQuasiSeparated _ _ _ IsProper.toIsSeparated⟩
  have hF : F.IsFinitePresentation :=
    @Stacks.Divisors.isFinitePresentation_of_isInvertible _ F
      ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        _ _ _).mp ‹_›)
  have hflat := isFlatOver_of_isInvertibleModule (pullback.snd sC sW) F
  have hsq : IsPullback (pullback.lift (𝟙 C) (sC ≫ t) (by simp [ht])) sC
      (pullback.snd sC sW) t := by
    have hR : IsPullback (pullback.fst sC sW) (pullback.snd sC sW) sC sW :=
      IsPullback.of_hasPullback sC sW
    have hO : IsPullback (pullback.lift (𝟙 C) (sC ≫ t) (by simp [ht]) ≫ pullback.fst sC sW) sC
        sC (t ≫ sW) := by
      rw [pullback.lift_fst, ht]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    exact IsPullback.of_right hO (pullback.lift_snd _ _ _) hR
  have h := chiDerivedFibre_eq_eulerSum (pullback.snd sC sW) hfp F hF hflat k t _ sC hsq pt
  rw [← h, fibreEulerCharacteristic_eq_chiDerivedFibre _ hfp F hF hflat]

/-- **Degrees are constant along the `k`-points of a connected base.** For `C` proper and flat
over `k` of dimension at most one, `W` connected over `k`, and a map `Φ` from `C ×ₖ W`, the degree
of `Φ^* H` on the slice `C × {t}` does not depend on the `k`-point `t` of `W`. -/
private theorem invertibleCurveDegree_pullback_lift_comp_eq {C W V : Scheme.{u}}
    (sC : C ⟶ Spec (.of k)) [IsProper sC] [Flat sC] [LocallyOfFinitePresentation sC]
    (hC : topologicalKrullDim C ≤ 1) (sW : W ⟶ Spec (.of k)) [ConnectedSpace W]
    (Φ : pullback sC sW ⟶ V) (H : V.Modules) [Stacks.Ample.IsInvertibleModule V H]
    (t t' : Spec (.of k) ⟶ W) (ht : t ≫ sW = 𝟙 _) (ht' : t' ≫ sW = 𝟙 _) :
    invertibleCurveDegree k sC hC ((Scheme.Modules.pullback
        (pullback.lift (𝟙 C) (sC ≫ t) (by simp [ht]) ≫ Φ)).obj H) =
      invertibleCurveDegree k sC hC ((Scheme.Modules.pullback
        (pullback.lift (𝟙 C) (sC ≫ t') (by simp [ht']) ≫ Φ)).obj H) := by
  obtain ⟨pt⟩ : Nonempty (Spec (.of k)) := inferInstance
  have hfp : FinitePresentation (pullback.snd sC sW) :=
    ⟨inferInstance, inferInstanceAs (QuasiCompact (pullback.snd sC sW)),
      @IsSeparated.instQuasiSeparated _ _ _ IsProper.toIsSeparated⟩
  have hlc (F : (pullback sC sW).Modules) [Stacks.Ample.IsInvertibleModule _ F] :
      IsLocallyConstant (fibreEulerCharacteristic (pullback.snd sC sW) F) :=
    isLocallyConstant_fibreEulerCharacteristic _ hfp F
      (@Stacks.Divisors.isFinitePresentation_of_isInvertible _ F
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
          _ _ _).mp ‹_›))
      (isFlatOver_of_isInvertibleModule _ F)
  have key : ∀ (s : Spec (.of k) ⟶ W) (hs : s ≫ sW = 𝟙 _),
      invertibleCurveDegree k sC hC ((Scheme.Modules.pullback
          (pullback.lift (𝟙 C) (sC ≫ s) (by simp [hs]) ≫ Φ)).obj H) =
        fibreEulerCharacteristic (pullback.snd sC sW) ((Scheme.Modules.pullback Φ).obj H) (s pt) -
          fibreEulerCharacteristic (pullback.snd sC sW)
            (SheafOfModules.unit (pullback sC sW).ringCatSheaf) (s pt) := by
    intro s hs
    haveI hu : Stacks.Ample.IsInvertibleModule _
        (SheafOfModules.unit (pullback sC sW).ringCatSheaf) := inferInstance
    have e1 := eulerSum_pullback_lift_eq sC sW ((Scheme.Modules.pullback Φ).obj H) s hs pt
    have e2 := eulerSum_pullback_lift_eq sC sW
      (SheafOfModules.unit (pullback sC sW).ringCatSheaf) s hs pt
    rw [← e1, ← e2]
    have c1 := eulerSum_congr k sC ((Scheme.Modules.pullbackComp
      (pullback.lift (𝟙 C) (sC ≫ s) (by simp [hs])) Φ).app H)
    have c2 := eulerSum_congr k sC (Scheme.Modules.pullbackUnitIso
      (pullback.lift (f := sC) (g := sW) (𝟙 C) (sC ≫ s) (by simp [hs])))
    refine Eq.trans ?_ (congrArg₂ (· - ·) c1.symm c2.symm)
    rfl
  rw [key t ht, key t' ht']
  have : Stacks.Ample.IsInvertibleModule _ (SheafOfModules.unit (pullback sC sW).ringCatSheaf) :=
    inferInstance
  rw [(hlc ((Scheme.Modules.pullback Φ).obj H)).apply_eq_of_isPreconnected isPreconnected_univ
      (Set.mem_univ (t pt)) (Set.mem_univ (t' pt)),
    (hlc (SheafOfModules.unit _)).apply_eq_of_isPreconnected isPreconnected_univ
      (Set.mem_univ (t pt)) (Set.mem_univ (t' pt))]

end DegreeConstancy

section PointClosure

open MMP.Mori MMP.Fourfold

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The closure of a point has the dimension of its reduced closed subscheme. -/
private theorem topologicalKrullDim_closure_singleton (y : X) :
    topologicalKrullDim (closure ({y} : Set X)) = topologicalKrullDim (curveSubschemeAt y) := by
  let e := (curveSubschemeAtι y).isClosedEmbedding.isEmbedding.toHomeomorph
  let e' := e.trans (Homeomorph.setCongr (range_curveSubschemeAtι y))
  exact (IsHomeomorph.topologicalKrullDim_eq e' e'.isHomeomorph).symm

/-- **Curves through a point avoiding a closed set.** Let `X` be locally Noetherian and locally
of finite type over a field, `p` a closed point, `η ⤳ p` and `Z ∋ p` a closed subset not
containing `η`. There is a point `y` with `η ⤳ y ⤳ p`, `y ∉ Z` and `{y}⁻` of dimension one. -/
private theorem exists_curve_of_specializes (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] {η p : X} (hηp : η ⤳ p) (hp : IsClosed ({p} : Set X)) {Z : Set X}
    (hZ : IsClosed Z) (hpZ : p ∈ Z) (hηZ : η ∉ Z) :
    ∃ y : X, η ⤳ y ∧ y ⤳ p ∧ y ∉ Z ∧ topologicalKrullDim (closure ({y} : Set X)) = 1 := by
  classical
  set R := X.presheaf.stalk p
  set g := X.fromSpecStalk p
  obtain ⟨Q, hQ⟩ := Stacks.Chow.exists_fromSpecStalk_eq hηp
  have hT : IsClosed (g ⁻¹' Z : Set (PrimeSpectrum R)) := hZ.preimage g.continuous
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hT
  have hQT : ¬ ((I : Set R) ⊆ Q.asIdeal) := fun h => hηZ (hQ ▸ hI.ge h)
  obtain ⟨a, haI, haQ⟩ := Set.not_subset.mp hQT
  have hgM : g (IsLocalRing.closedPoint R) = p := Scheme.fromSpecStalk_closedPoint
  have hQM : Q.asIdeal < IsLocalRing.maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal Q.isPrime.ne_top) fun h => hηZ ?_
    rw [← hQ, show Q = IsLocalRing.closedPoint R from PrimeSpectrum.ext h,
      Scheme.fromSpecStalk_closedPoint]
    exact hpZ
  obtain ⟨q, hq, hQq, hqM, haq, himm⟩ := exists_isPrime_le_lt_notMem_of_lt hQM haQ
  set qpt : PrimeSpectrum R := ⟨q, hq⟩
  have hyZ : g qpt ∉ Z := by
    intro h
    have h' : qpt ∈ (g ⁻¹' Z : Set (PrimeSpectrum R)) := h
    rw [hI] at h'
    exact haq (h' haI)
  have hyp : g qpt ⤳ p := Stacks.Chow.specializes_fromSpecStalk p qpt
  refine ⟨g qpt, ?_, hyp, hyZ, ?_⟩
  · rw [← hQ]
    exact ((PrimeSpectrum.le_iff_specializes Q qpt).mp hQq).map g.continuous
  · rw [topologicalKrullDim_closure_singleton]
    refine topologicalKrullDim_curveSubschemeAt_eq_one sX hyp
      (fun h => hyZ (by rw [h]; exact hpZ)) hp fun z hyz hzp => ?_
    obtain ⟨r, rfl⟩ := Stacks.Chow.exists_fromSpecStalk_eq hzp
    have hle : r ≤ qpt := (Stacks.Chow.fromSpecStalk_le_iff p).mp hyz
    have hqr : q ≤ r.asIdeal := (PrimeSpectrum.le_iff_specializes qpt r).mpr hle
    rcases eq_or_lt_of_le hqr with h | h
    · left
      congr 1
      exact PrimeSpectrum.ext h.symm
    · right
      have := himm r.asIdeal r.isPrime h (IsLocalRing.le_maximalIdeal r.isPrime.ne_top)
      rw [show r = IsLocalRing.closedPoint R from PrimeSpectrum.ext this]
      exact hgM

end PointClosure

section CurveThrough

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A point whose local ring has positive dimension has a proper generization. -/
private theorem exists_specializes_ne_of_one_le_ringKrullDim {X : Scheme.{u}} (x : X)
    (h : (1 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x)) :
    ∃ η : X, η ⤳ x ∧ η ≠ x := by
  by_contra hne
  push Not at hne
  have hsub : ∀ q : PrimeSpectrum (X.presheaf.stalk x), q = IsLocalRing.closedPoint _ := by
    intro q
    apply (X.fromSpecStalk x).isEmbedding.injective
    rw [hne _ (Stacks.Chow.specializes_fromSpecStalk x q), Scheme.fromSpecStalk_closedPoint]
  haveI : Unique (PrimeSpectrum (X.presheaf.stalk x)) :=
    ⟨⟨IsLocalRing.closedPoint _⟩, hsub⟩
  have h0 : ringKrullDim (X.presheaf.stalk x) = 0 := Order.krullDim_eq_zero_of_unique
  rw [h0] at h
  exact absurd h (by decide)

/-- **A smooth projective model of a curve with two marked points.** The normalization
of a curve `Z` over `k`, compactified to a smooth projective curve `T`, gives an open `W ⊆ T`
mapping to `Z`, a `k`-point of `W` over a given closed point `z₀`, and a `k`-point of `W` not
over `z₀`. -/
private theorem exists_smooth_model_with_points {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    [AlgebraicGeometry.IsCurve k sZ] (z₀ : Z) (hz₀ : IsClosed ({z₀} : Set Z)) :
    ∃ (T : Scheme.{u}) (sT : T ⟶ Spec (.of k)) (_ : IsProper sT) (_ : Smooth sT)
      (_ : ConnectedSpace T) (_ : topologicalKrullDim T = 1) (W : T.Opens) (τ : W.toScheme ⟶ Z)
      (t₀ t₁ : Spec (.of k) ⟶ W.toScheme),
      τ ≫ sZ = W.ι ≫ sT ∧ t₀ ≫ W.ι ≫ sT = 𝟙 _ ∧ t₁ ≫ W.ι ≫ sT = 𝟙 _ ∧
        (∀ a, τ (t₀ a) = z₀) ∧ ∀ a, τ (t₁ a) ≠ z₀ := by
  haveI : LocallyOfFiniteType sZ := inferInstance
  set N := normalizationSchemeOverField k sZ with hNdef
  set ν := normalizationOverField k sZ with hνdef
  haveI hNc : AlgebraicGeometry.IsCurve k (ν ≫ sZ) := isCurve_normalizationOverField_comp k sZ
  haveI : IsFinite ν := isFinite_normalizationOverField k sZ
  haveI : IsDominant ν := isDominant_normalizationOverField k sZ
  haveI : IsNormal N := Scheme.isNormal_normalizationScheme Z _
  haveI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian (ν ≫ sZ)
  have hreg : AlgebraicGeometry.IsRegular N := isRegular_of_isNormal_of_topologicalKrullDim_le_one N
    (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := ν ≫ sZ)).le
  obtain ⟨-, T, sT, j, hj, hjq, hTc, hTp, -, hTs, -, -⟩ :=
    exists_smooth_isProjectiveMorphism_compactification_of_perfectField k (ν ≫ sZ) hreg
  haveI := hj
  haveI := hTc
  haveI : IsProper sT := isProper_of_isProjectiveMorphism sT hTp
  haveI : IsIntegral T := hTc.toIsIntegral
  -- `ν` is surjective
  have hνs : Function.Surjective ν.base := by
    have hcl : IsClosed (Set.range ν.base) := ν.isClosedMap.isClosed_range
    exact Set.range_eq_univ.mp (by rw [← hcl.closure_eq]; exact ν.denseRange.closure_eq)
  haveI : JacobsonSpace N := LocallyOfFiniteType.jacobsonSpace (ν ≫ sZ)
  -- a closed point of `N` over `z₀`
  have hF : IsClosed (ν.base ⁻¹' {z₀}) := hz₀.preimage ν.continuous
  obtain ⟨n₀', hn₀'⟩ := hνs z₀
  obtain ⟨n₀, hn₀F, hn₀cl⟩ :=
    nonempty_inter_closedPoints (⟨n₀', hn₀'⟩ : (ν.base ⁻¹' {z₀}).Nonempty) hF.isLocallyClosed
  -- a closed point of `N` not over `z₀`
  have hG : IsOpen (ν.base ⁻¹' {z₀})ᶜ := hF.isOpen_compl
  have hGne : ((ν.base ⁻¹' {z₀})ᶜ).Nonempty := by
    haveI : IsIntegral N := hNc.toIsIntegral
    haveI : IsIntegral Z := inferInstance
    refine ⟨genericPoint N, fun h => ?_⟩
    have hgen : ν.base (genericPoint N) = genericPoint Z := by
      first
        | exact map_genericPoint_of_isDominant ν
        | exact genericPoint_eq_of_isDominant ν
    have h' : genericPoint Z = z₀ := hgen ▸ h
    exact not_isClosed_genericPoint (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one
      (f := sZ)) (h' ▸ hz₀)
  obtain ⟨n₁, hn₁G, hn₁cl⟩ := nonempty_inter_closedPoints hGne hG.isLocallyClosed
  have hn₀cl' : IsClosed ({n₀} : Set N) := hn₀cl
  have hn₁cl' : IsClosed ({n₁} : Set N) := hn₁cl
  set p₀ := pointOfClosedPoint (ν ≫ sZ) n₀ hn₀cl' with hp₀
  set p₁ := pointOfClosedPoint (ν ≫ sZ) n₁ hn₁cl' with hp₁
  set e := j.isoOpensRange with he
  refine ⟨T, sT, inferInstance, hTs, inferInstance, hTc.topologicalKrullDim_eq_one,
    j.opensRange, e.inv ≫ ν, p₀ ≫ e.hom, p₁ ≫ e.hom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hjq, ← Category.assoc e.inv, Scheme.Hom.isoOpensRange_inv_comp]
  · rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, hjq, pointOfClosedPoint_comp]
  · rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, hjq, pointOfClosedPoint_comp]
  · intro a
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, Category.assoc p₀, Iso.hom_inv_id,
      Category.comp_id, Scheme.Hom.comp_apply, hp₀, pointOfClosedPoint_apply]
    exact hn₀F
  · intro a
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, Category.assoc p₁, Iso.hom_inv_id,
      Category.comp_id, Scheme.Hom.comp_apply, hp₁, pointOfClosedPoint_apply]
    exact hn₁G

/-- **An integral curve through a closed point of positive local dimension.** Inside an
affine neighbourhood of `x`, the closure of a suitable generization of `x` is an integral curve
through `x`. -/
private theorem exists_isCurve_through {M : Scheme.{u}} (sM : M ⟶ Spec (.of k))
    [LocallyOfFiniteType sM] (x : M) (hx : IsClosed ({x} : Set M))
    (hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim (M.presheaf.stalk x)) :
    ∃ (Z : Scheme.{u}) (sZ : Z ⟶ Spec (.of k)) (_ : AlgebraicGeometry.IsCurve k sZ) (ι : Z ⟶ M)
      (z₀ : Z), ι ≫ sM = sZ ∧ Function.Injective ι.base ∧ ι z₀ = x ∧
        IsClosed ({z₀} : Set Z) := by
  obtain ⟨A, hA, hxA⟩ : ∃ A : M.Opens, IsAffineOpen A ∧ x ∈ A := by
    obtain ⟨A, hA, hyA, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp M.isBasis_affineOpens)
      (show x ∈ (⊤ : M.Opens) from trivial)
    exact ⟨A, hA, hyA⟩
  haveI : IsAffine A := hA
  set xA : A.toScheme := ⟨x, hxA⟩ with hxAdef
  have hιxA : A.ι xA = x := rfl
  have hxAcl : IsClosed ({xA} : Set A.toScheme) := by
    have h := hx.preimage A.ι.continuous
    convert h using 1
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl; rfl
    · intro hz; exact A.ι.isOpenEmbedding.injective (hz.trans hιxA.symm)
  have hdimA : (1 : WithBot ℕ∞) ≤ ringKrullDim (A.toScheme.presheaf.stalk xA) := by
    haveI : IsIso (A.ι.stalkMap xA) := (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 xA
    have e : (A.toScheme.presheaf.stalk xA) ≃+* (M.presheaf.stalk x) :=
      (asIso (A.ι.stalkMap xA)).commRingCatIsoToRingEquiv.symm
    rwa [ringKrullDim_eq_of_ringEquiv e]
  obtain ⟨η, hη, hne⟩ := exists_specializes_ne_of_one_le_ringKrullDim xA hdimA
  haveI : LocallyOfFiniteType (A.ι ≫ sM) := inferInstance
  haveI : IsLocallyNoetherian A.toScheme := LocallyOfFiniteType.isLocallyNoetherian (A.ι ≫ sM)
  obtain ⟨y, -, hyx, hyZ, hdim1⟩ := exists_curve_of_specializes (A.ι ≫ sM) hη hxAcl hxAcl
    (Set.mem_singleton _) (fun h => hne (Set.mem_singleton_iff.mp h))
  haveI hint : IsIntegral (MMP.Mori.curveSubschemeAt y) :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure y
  haveI : IsAffineHom (A.ι ≫ sM) := isAffineHom_of_isAffine _
  haveI : IsSeparated (A.ι ≫ sM) := IsSeparated.of_isAffineHom _
  haveI : QuasiCompact (A.ι ≫ sM) :=
    quasiCompact_iff_forall_isAffineOpen.mpr fun _ hU ↦ (hU.preimage (A.ι ≫ sM)).isCompact
  have hcurve : AlgebraicGeometry.IsCurve k (MMP.Mori.curveSubschemeAtι y ≫ A.ι ≫ sM) :=
    { toIsIntegral := hint
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := (topologicalKrullDim_closure_singleton y).symm.trans hdim1 }
  have hmem : xA ∈ Set.range (MMP.Mori.curveSubschemeAtι y).base := by
    rw [show Set.range (MMP.Mori.curveSubschemeAtι y).base = closure {y} from
      MMP.Mori.range_curveSubschemeAtι y]
    exact specializes_iff_mem_closure.mp hyx
  obtain ⟨z₀, hz₀⟩ := hmem
  have hinj : Function.Injective (MMP.Mori.curveSubschemeAtι y).base :=
    (MMP.Mori.curveSubschemeAtι y).isClosedEmbedding.injective
  refine ⟨_, _, hcurve, MMP.Mori.curveSubschemeAtι y ≫ A.ι, z₀, Category.assoc _ _ _,
    ?_, ?_, ?_⟩
  · exact A.ι.isOpenEmbedding.injective.comp hinj
  · rw [Scheme.Hom.comp_apply, hz₀]; rfl
  · have h := hxAcl.preimage (MMP.Mori.curveSubschemeAtι y).continuous
    convert h using 1
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl; exact hz₀
    · intro hz; exact hinj (hz.trans hz₀.symm)

end CurveThrough

section Core

open Stacks.AlgebraicGeometry.ReflexiveModules

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A point of `X ×ₖ Y` over a `k`-point `P` of `X` lies on the section `Y ⟶ X ×ₖ Y` at `P`. -/
private theorem exists_lift_apply_eq_of_fst_eq {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) (P : Spec (.of k) ⟶ X) (hP : P ≫ sX = 𝟙 _)
    (w : (pullback sX sY : Scheme.{u}))
    (pt : Spec (.of k)) (hw : pullback.fst sX sY w = P pt) :
    ∃ y : Y, pullback.lift (sY ≫ P) (𝟙 Y) (by simp [hP]) y = w := by
  have hsq : IsPullback (pullback.lift (sY ≫ P) (𝟙 Y) (by simp [hP])) sY (pullback.fst sX sY)
      P := by
    have hR : IsPullback (pullback.snd sX sY) (pullback.fst sX sY) sY sX :=
      (IsPullback.of_hasPullback sX sY).flip
    have hO : IsPullback (pullback.lift (sY ≫ P) (𝟙 Y) (by simp [hP]) ≫ pullback.snd sX sY) sY
        sY (P ≫ sX) := by
      rw [pullback.lift_snd, hP]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    exact IsPullback.of_right hO (pullback.lift_fst _ _ _) hR
  have hmem : w ∈ Set.range (pullback.fst (pullback.fst sX sY) P) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨pt, hw.symm⟩
  obtain ⟨v, hv⟩ := hmem
  refine ⟨hsq.isoPullback.inv v, ?_⟩
  have h1 : hsq.isoPullback.inv ≫ pullback.lift (sY ≫ P) (𝟙 Y) (by simp [hP]) =
      pullback.fst (pullback.fst sX sY) P := by
    rw [Iso.inv_comp_eq, hsq.isoPullback_hom_fst]
  rw [← hv, ← h1]; rfl

/-- A curve has infinitely many closed points. -/
private theorem infinite_closedPoints {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [AlgebraicGeometry.IsCurve k sX] : (closedPoints X).Infinite := by
  intro hfin
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hclosed : IsClosed (closedPoints X) := by
    rw [← Set.biUnion_of_singleton (closedPoints X)]
    exact hfin.isClosed_biUnion fun x hx => hx
  have huniv : closedPoints X = Set.univ := by
    have := closure_closedPoints (X := X)
    rwa [hclosed.closure_eq] at this
  have hη : IsClosed ({genericPoint X} : Set X) :=
    (huniv ▸ Set.mem_univ _ : genericPoint X ∈ closedPoints X)
  exact not_isClosed_genericPoint (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one
    (f := sX)) hη

private theorem exists_isRationalCurve_of_cover
    {V : Scheme.{u}} (sV : V ⟶ Spec (.of k)) (hV : IsProjectiveMorphism sV)
    (U : V.Opens) (n : ℕ) [SmoothOfRelativeDimension n (U.ι ≫ sV)]
    {C : Scheme.{u}} (i : C ⟶ U.toScheme) [IsClosedImmersion i]
    [AlgebraicGeometry.IsCurve k (i ≫ U.ι ≫ sV)]
    [AlgebraicGeometry.IsProjectiveVariety k (i ≫ U.ι ≫ sV)] [Smooth (i ≫ U.ι ≫ sV)]
    (hg : 1 ≤ genus (i ≫ U.ι ≫ sV))
    (H : V.Modules) [Stacks.Ample.IsInvertibleModule V H] (hH : Stacks.Ample.IsAmple V H)
    {C' : Scheme.{u}} (sC' : C' ⟶ Spec (.of k)) [AlgebraicGeometry.IsCurve k sC']
    [AlgebraicGeometry.IsProjectiveVariety k sC'] [Smooth sC']
    (φ : C' ⟶ C) (hφ : φ ≫ i ≫ U.ι ≫ sV = sC') (hφs : Function.Surjective φ.base)
    (b : ℕ) (hb : 0 < b)
    (hχ : haveI : (Stacks.Ample.IsInvertibleModule U.toScheme
          (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n)) :=
        Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
      (n * b + 2 * genus sC' + 1 : ℤ) ≤
        -invertibleCurveDegree k sC'
          (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := sC')).le
            ((Scheme.Modules.pullback (φ ≫ i)).obj
              (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n)) + n * (1 - genus sC'))
    (hd : 0 < invertibleCurveDegree k sC'
      (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := sC')).le
        ((Scheme.Modules.pullback (φ ≫ i ≫ U.ι)).obj H)) :
    ∃ (L : V.IdealSheafData) (hL : Mori.IsRationalCurve sV L),
      haveI := hL.2.1
      0 < Mori.degreeOn k sV L.subschemeι hL.1.2.le H ∧
        (Mori.degreeOn k sV L.subschemeι hL.1.2.le H : ℚ) <
          2 * invertibleCurveDegree k sC'
            (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := sC')).le
              ((Scheme.Modules.pullback (φ ≫ i ≫ U.ι)).obj H) / b := by
  classical
  have hC'dim := AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := sC')
  haveI : IsIntegral C' := (inferInstance : AlgebraicGeometry.IsVariety k sC').toIsIntegral
  haveI : IsProper sC' := (inferInstance : AlgebraicGeometry.IsProperVariety k sC').toIsProper
  haveI : ConnectedSpace C' := inferInstance
  haveI : Smooth (U.ι ≫ sV) := (inferInstance : SmoothOfRelativeDimension n (U.ι ≫ sV)).smooth
  -- the connected component `U'` of `U` containing the image of `C'`
  set f₀ : C' ⟶ U.toScheme := φ ≫ i with hf₀
  obtain ⟨c₀⟩ : Nonempty C' := inferInstance
  have hopen := Stacks.Chow.isOpen_connectedComponent_of_smooth (U.ι ≫ sV) (f₀ c₀)
  set U' : U.toScheme.Opens := ⟨connectedComponent (f₀ c₀), hopen⟩ with hU'
  haveI : IsIntegral U'.toScheme :=
    Stacks.Chow.isIntegral_connectedComponent_of_smooth (U.ι ≫ sV) (f₀ c₀) hopen
  have hrange : Set.range f₀.base ⊆ Set.range U'.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact (isPreconnected_range f₀.continuous).subset_connectedComponent ⟨c₀, rfl⟩
  set f : C' ⟶ U'.toScheme := IsOpenImmersion.lift U'.ι f₀ hrange with hfdef
  have hf : f ≫ U'.ι = f₀ := IsOpenImmersion.lift_fac _ _ _
  set sU' : U'.toScheme ⟶ Spec (.of k) := U'.ι ≫ U.ι ≫ sV with hsU'
  haveI : IsProper sV := isProper_of_isProjectiveMorphism sV hV
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : IsNoetherian V := ⟨⟩
  haveI : TopologicalSpace.NoetherianSpace U'.toScheme := inferInstance
  haveI : SmoothOfRelativeDimension n sU' := by
    have := smoothOfRelativeDimension_comp (n := 0) (m := n) U'.ι (U.ι ≫ sV)
    rwa [zero_add] at this
  haveI : IsQuasiProjectiveVariety k sU' := by
    have hvar : AlgebraicGeometry.IsVariety k sU' :=
      { toIsIntegral := inferInstance
        toIsSeparated := inferInstance
        toLocallyOfFiniteType := inferInstance
        toQuasiCompact := quasiCompact_of_compactSpace _ }
    rw [isQuasiProjectiveVariety_iff_isHQuasiProjective]
    refine ⟨hvar, ?_⟩
    obtain ⟨N, ιV, hιV, hιVs⟩ := hV
    exact ⟨N, U'.ι ≫ U.ι ≫ ιV, inferInstance, inferInstance, by
      rw [Category.assoc, Category.assoc, hιVs]⟩
  have hfs : f ≫ sU' = sC' := by rw [hsU', ← Category.assoc, hf, hf₀, Category.assoc, hφ]
  -- `b` distinct closed points of `C'` and the `k`-points through them
  have hinf := infinite_closedPoints sC'
  let e := Set.Infinite.natEmbedding _ hinf
  let Q : Fin b → C' := fun j => (e j.val).1
  have hQc : ∀ j, IsClosed ({Q j} : Set C') := fun j => (e j.val).2
  have hQinj : Function.Injective Q := fun a a' h => Fin.ext (e.injective (Subtype.ext h))
  let P : Fin b → (Spec (.of k) ⟶ C') := fun j => pointOfClosedPoint sC' (Q j) (hQc j)
  have hP : ∀ j, P j ≫ sC' = 𝟙 _ := fun j => pointOfClosedPoint_comp _ _ _
  have hPapp : ∀ j a, P j a = Q j := fun j a => pointOfClosedPoint_apply _ _ _ _
  obtain ⟨pt⟩ : Nonempty (Spec (.of k)) := inferInstance
  have hPinj : Function.Injective P := fun a a' h =>
    hQinj (by rw [← hPapp a pt, ← hPapp a' pt, h])
  -- coherence
  haveI hΩ' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      sU'.relativeDifferentials n :=
    Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials sU' n
  haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualSheaf sU'.relativeDifferentials) n :=
    isFiniteLocallyFreeOfRank_dualSheaf _ n hΩ'
  haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj (dualSheaf sU'.relativeDifferentials)) n :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f _ n
  haveI hcoh : ((Scheme.Modules.pullback f).obj (dualSheaf sU'.relativeDifferentials)).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k sC' _ n
  haveI hO : (SheafOfModules.unit C'.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k sC'
  -- the deformation space of `f` fixing the marked points
  obtain ⟨M, sM, m, F, hm, hMlft, hMqc, hFs, hFm, hFP, hFinj, hMdim⟩ :=
    MMP.Fourfold.exists_fixedMarked_mapFamily_le_ringKrullDim k sC' sU' (n := n) f hfs P hP hPinj
  -- its dimension at `m` is positive
  have hdimm : (1 : WithBot ℕ∞) ≤ ringKrullDim (M.presheaf.stalk (m pt)) := by
    obtain ⟨hcoh0, hχ0⟩ :=
      eulerCharacteristic_pullback_dualSheaf_relativeDifferentials sC' (U.ι ≫ sV) n f₀
    have hχeq : eulerCharacteristic k sC' ((Scheme.Modules.pullback f).obj
        (dualSheaf sU'.relativeDifferentials)) = eulerCharacteristic k sC'
          ((Scheme.Modules.pullback f₀).obj (dualSheaf (U.ι ≫ sV).relativeDifferentials)) :=
      eulerCharacteristic_eq_of_iso k sC'
        (pullbackDualSheafRelativeDifferentialsIso (U.ι ≫ sV) n U'.ι f ≪≫
          (Scheme.Modules.pullbackCongr hf).app _)
    haveI := GenusOne.isIso_globalSections_of_isAlgClosed sC'
    have hga : arithmeticGenus sC' = genus sC' := by
      rw [arithmeticGenus, eulerCharacteristic_unit_eq_one_sub_genus k sC' hC'dim.le]; ring
    have hX : 1 ≤ (eulerCharacteristic k sC' ((Scheme.Modules.pullback f).obj
        (dualSheaf sU'.relativeDifferentials)) - n * b - 2 * arithmeticGenus sC').toNat := by
      rw [hχeq, hχ0, hga]; omega
    have h2 := hMdim
    rw [show (default : Spec (.of k)) = pt from Subsingleton.elim _ _] at h2
    exact le_trans (by exact_mod_cast hX) h2
  -- a curve through `m`, and a smooth model of it with two `k`-points
  haveI := hMlft
  have hmcl : IsClosed ({m pt} : Set M) := by
    have h := ((pointEquivClosedPoint sM) ⟨m, hm⟩).2
    have he : m.base pt = ((pointEquivClosedPoint sM) ⟨m, hm⟩ : M) :=
      congrArg m.base (Subsingleton.elim _ _)
    rw [he]; exact h
  obtain ⟨Z, sZ, hZ, ι, z₀, hιs, hιinj, hιz, hz₀⟩ := exists_isCurve_through sM (m pt) hmcl hdimm
  obtain ⟨T, sT, hTp, hTs, hTc, hT, W, τ', t₀, t₁, hτ', ht₀, ht₁, h₀, h₁⟩ :=
    exists_smooth_model_with_points sZ z₀ hz₀
  set τ : W.toScheme ⟶ M := τ' ≫ ι with hτdef
  have hτ : τ ≫ sM = W.ι ≫ sT := by rw [hτdef, Category.assoc, hιs, hτ']
  have ht₀τ : t₀ ≫ τ = m := by
    refine ext_of_apply_closedPoint_eq sM ?_ hm ?_
    · rw [Category.assoc, hτ, ht₀]
    · change ι (τ' (t₀ _)) = m _
      exact (congrArg ι.base (h₀ _)).trans (hιz.trans (congrArg m.base (Subsingleton.elim _ _)))
  have ht₁τ : t₁ ≫ τ ≠ m := by
    intro h
    apply h₁ pt
    apply hιinj
    rw [hιz]
    have h' : (t₁ ≫ τ).base pt = m.base pt := by rw [h]
    exact h'
  haveI : Nonempty W.toScheme := ⟨t₀ pt⟩
  have hWne : (W : Set T).Nonempty := ⟨(t₀ pt).1, (t₀ pt).2⟩
  -- the family `C' × W ⟶ V`
  set Ψ : pullback sC' (W.ι ≫ sT) ⟶ pullback sC' sM :=
    pullback.map sC' (W.ι ≫ sT) sC' sM (𝟙 _) τ (𝟙 _) (by simp) (by simp [hτ]) with hΨ
  set Φ : pullback sC' (W.ι ≫ sT) ⟶ V := Ψ ≫ F ≫ U'.ι ≫ U.ι with hΦdef
  have hslice : ∀ (t : Spec (.of k) ⟶ W.toScheme) (ht : t ≫ W.ι ≫ sT = 𝟙 _),
      pullback.lift (𝟙 C') (sC' ≫ t) (by simp [ht]) ≫ Ψ =
        pullback.lift (𝟙 C') (sC' ≫ t ≫ τ) (by simp [hτ, ht]) := by
    intro t ht
    apply pullback.hom_ext
    · rw [Category.assoc, hΨ, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id,
        pullback.lift_fst]
    · rw [Category.assoc, hΨ, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd,
        Category.assoc]
  have hΦ : Φ ≫ sV = pullback.snd sC' (W.ι ≫ sT) ≫ W.ι ≫ sT := by
    rw [hΦdef]
    simp only [Category.assoc]
    rw [show F ≫ U'.ι ≫ U.ι ≫ sV = F ≫ sU' from rfl, hFs, hΨ, pullback.lift_fst_assoc,
      Category.comp_id, pullback.condition]
  have hconst : ∀ j, ∃ v : V, ∀ z, (pullback.fst sC' (W.ι ≫ sT)).base z = Q j →
      Φ.base z = v := by
    intro j
    refine ⟨(f ≫ U'.ι ≫ U.ι).base (Q j), fun z hz => ?_⟩
    have hw' : (Ψ ≫ pullback.fst sC' sM).base z = Q j := by
      rw [hΨ, pullback.lift_fst, Category.comp_id]; exact hz
    have hw : pullback.fst sC' sM (Ψ z) = P j pt := hw'.trans (hPapp j pt).symm
    obtain ⟨y, hy⟩ := exists_lift_apply_eq_of_fst_eq sC' sM (P j) (hP j) (Ψ z) pt hw
    have hF : F.base (Ψ.base z) = f.base (Q j) := by
      rw [← hy]
      exact (congrArg (fun g => g.base y) (hFP j)).trans (by
        change f (P j (sM y)) = _
        rw [hPapp])
    change (U'.ι ≫ U.ι).base (F.base (Ψ.base z)) = (U'.ι ≫ U.ι).base (f.base (Q j))
    rw [hF]
  have hlm : pullback.lift (f := sC') (g := sM) (𝟙 C') (sC' ≫ t₀ ≫ τ) (by simp [hτ, ht₀]) =
      pullback.lift (f := sC') (g := sM) (𝟙 C') (sC' ≫ m) (by simp [hm]) :=
    pullback.hom_ext (by rw [pullback.lift_fst, pullback.lift_fst])
      (by rw [pullback.lift_snd, pullback.lift_snd, ht₀τ])
  have he : pullback.lift (𝟙 C') (sC' ≫ t₀) (by simp [ht₀]) ≫ Φ = φ ≫ i ≫ U.ι := by
    rw [hΦdef, ← Category.assoc, hslice t₀ ht₀, hlm, ← Category.assoc, hFm, ← Category.assoc,
      hf, hf₀, Category.assoc]
  have hdim : topologicalKrullDim (closure (Set.range Φ.base)) = 2 := by
    haveI : AlgebraicGeometry.IsVariety k sT := isVariety_of_smooth_of_connected sT
    haveI : IsIntegral T := (inferInstance : AlgebraicGeometry.IsVariety k sT).toIsIntegral
    obtain ⟨hXv, -, hXd, -⟩ := product_facts sC' sT hC'dim hT
    haveI : IsIntegral (pullback sC' sT) := hXv.toIsIntegral
    let eD := restrictProductIso sC' sT W
    set s₀ : C' ⟶ pullback sC' (W.ι ≫ sT) := pullback.lift (𝟙 C') (sC' ≫ t₀) (by simp [ht₀])
      with hs₀
    haveI : Nonempty (pullback sC' (W.ι ≫ sT) : Scheme.{u}) := ⟨s₀ c₀⟩
    haveI : IsIntegral (pullback sC' (W.ι ≫ sT) : Scheme.{u}) :=
      isIntegral_of_isOpenImmersion (eD.inv ≫ ((pullback.snd sC' sT) ⁻¹ᵁ W).ι)
    -- the upper bound
    have hXdim : topologicalKrullDim (pullback sC' (W.ι ≫ sT) : Scheme.{u}) ≤ 2 := by
      have h1 := IsHomeomorph.topologicalKrullDim_eq _ eD.inv.homeomorph.isHomeomorph
      have h2 := topologicalKrullDim_subspace_le (pullback sC' sT : Scheme.{u})
        (((pullback.snd sC' sT) ⁻¹ᵁ W : (pullback sC' sT : Scheme.{u}).Opens) : Set _)
      rw [← hXd]
      exact h1.le.trans h2
    have hup : topologicalKrullDim (closure (Set.range Φ.base)) ≤ 2 := by
      haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
      haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
      haveI : IsNoetherian T := ⟨⟩
      haveI : CompactSpace W.toScheme := inferInstance
      haveI : CompactSpace (pullback sC' (W.ι ≫ sT) : Scheme.{u}) :=
        QuasiCompact.compactSpace_of_compactSpace (pullback.snd sC' (W.ι ≫ sT))
      haveI : IsLocallyNoetherian (pullback sC' (W.ι ≫ sT) : Scheme.{u}) :=
        LocallyOfFiniteType.isLocallyNoetherian (pullback.fst sC' (W.ι ≫ sT) ≫ sC')
      haveI : IsNoetherian (pullback sC' (W.ι ≫ sT) : Scheme.{u}) := ⟨⟩
      haveI : QuasiCompact Φ := ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
      haveI : LocallyOfFiniteType (Φ ≫ sV) := by
        rw [hΦ, ← pullback.condition]; infer_instance
      haveI : LocallyOfFiniteType Φ := locallyOfFiniteType_of_comp Φ sV
      have hrange : Set.range Φ.imageι.base = closure (Set.range Φ.base) := by
        rw [show Φ.imageι = Φ.ker.subschemeι from rfl, Scheme.IdealSheafData.range_subschemeι,
          Scheme.Hom.support_ker]
      let e := Φ.imageι.isClosedEmbedding.isEmbedding.toHomeomorph
      let e' := e.trans (Homeomorph.setCongr hrange)
      rw [← IsHomeomorph.topologicalKrullDim_eq e' e'.isHomeomorph]
      exact (MMP.Mori.topologicalKrullDim_image_le sV Φ).trans hXdim
    -- the lower bound
    refine le_antisymm hup ?_
    -- `C ⟶ V` is a closed immersion
    haveI : IsProper ((i ≫ U.ι) ≫ sV) := by rw [Category.assoc]; infer_instance
    haveI : IsProper (i ≫ U.ι) := IsProper.of_comp (i ≫ U.ι) sV
    haveI hgci : IsClosedImmersion (i ≫ U.ι) :=
      (IsClosedImmersion.iff_isProper_and_mono (i ≫ U.ι)).mpr ⟨inferInstance, inferInstance⟩
    have hginj : Function.Injective (i ≫ U.ι).base := (i ≫ U.ι).isClosedEmbedding.injective
    have hΓ : IsClosed (Set.range (i ≫ U.ι).base) := (i ≫ U.ι).isClosedEmbedding.isClosed_range
    -- three points of the image
    set q : C' := Q ⟨0, hb⟩ with hq
    set a := Φ (genericPoint (pullback sC' (W.ι ≫ sT) : Scheme.{u})) with ha
    set γ := Φ (s₀ (genericPoint C')) with hγ
    set c := Φ (s₀ q) with hc
    have hγ' : γ = (i ≫ U.ι) (φ (genericPoint C')) := by
      rw [hγ, ← Scheme.Hom.comp_apply, he]; rfl
    have hc' : c = (i ≫ U.ι) (φ q) := by
      rw [hc, ← Scheme.Hom.comp_apply, he]; rfl
    have haγ : a ⤳ γ := (genericPoint_specializes _).map Φ.continuous
    have hγc : γ ⤳ c := ((genericPoint_specializes q).map s₀.continuous).map Φ.continuous
    have hγc' : γ ≠ c := by
      intro h
      rw [hγ', hc'] at h
      have h2 : φ (genericPoint C') = φ q := hginj h
      have hqcl : IsClosed ({φ q} : Set C) := by
        have hcl := ((pointEquivClosedPoint (i ≫ U.ι ≫ sV)) ⟨P ⟨0, hb⟩ ≫ φ, by
          rw [Category.assoc, hφ, hP]⟩).2
        have he' : φ q = (P ⟨0, hb⟩ ≫ φ).base (IsLocalRing.closedPoint k) :=
          congrArg φ.base (hPapp _ _).symm
        rw [he']
        exact hcl
      have key : ∀ x : C, x = φ q := fun x => by
        obtain ⟨x', rfl⟩ := hφs x
        have hs : φ (genericPoint C') ⤳ φ x' := (genericPoint_specializes x').map φ.continuous
        rw [h2] at hs
        have hm := specializes_iff_mem_closure.mp hs
        rw [hqcl.closure_eq] at hm
        exact hm
      exact not_subsingleton_of_topologicalKrullDim_eq_one
        (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := i ≫ U.ι ≫ sV))
        ⟨fun x y => by rw [key x, key y]⟩
    have haγ' : a ≠ γ := by
      intro haγeq
      have hsub : Set.range Φ.base ⊆ Set.range (i ≫ U.ι).base := by
        rintro _ ⟨z, rfl⟩
        have h1 : a ⤳ Φ z := (genericPoint_specializes z).map Φ.continuous
        rw [haγeq] at h1
        have h2 : γ ∈ Set.range (i ≫ U.ι).base := by rw [hγ']; exact ⟨_, rfl⟩
        exact closure_minimal (Set.singleton_subset_iff.mpr h2) hΓ
          (specializes_iff_mem_closure.mp h1)
      set Φ' : pullback sC' (W.ι ≫ sT) ⟶ U.toScheme := Ψ ≫ F ≫ U'.ι with hΦ'def
      have hΦΦ' : Φ = Φ' ≫ U.ι := by rw [hΦdef, hΦ'def]; simp only [Category.assoc]
      have hsub' : Set.range Φ'.base ⊆ Set.range i.base := by
        rintro _ ⟨z, rfl⟩
        obtain ⟨c1, hc1⟩ := hsub ⟨z, rfl⟩
        refine ⟨c1, U.ι.isOpenEmbedding.injective ?_⟩
        refine hc1.trans ?_
        rw [hΦΦ']; rfl
      have hker : i.ker ≤ Φ'.ker := by
        rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range i,
          Scheme.Hom.ker_eq_vanishingIdeal_closure_range Φ']
        exact Scheme.IdealSheafData.vanishingIdeal_antimono (fun x hx => closure_mono hsub' hx)
      set G : pullback sC' (W.ι ≫ sT) ⟶ C := IsClosedImmersion.lift i Φ' hker with hGdef
      have hG : G ≫ i = Φ' := IsClosedImmersion.lift_fac i Φ' hker
      have hGs : G ≫ i ≫ U.ι ≫ sV = pullback.fst sC' (W.ι ≫ sT) ≫ sC' := by
        rw [← Category.assoc, hG, ← Category.assoc, ← hΦΦ', hΦ, ← pullback.condition]
      have hGΦ : ∀ w, (i ≫ U.ι).base (G.base w) = Φ.base w := fun w => by
        rw [hΦΦ', ← hG]; rfl
      have hGconst : ∃ v : C, ∀ z, pullback.fst sC' (W.ι ≫ sT) z = q → G z = v := by
        obtain ⟨v, hv⟩ := hconst ⟨0, hb⟩
        refine ⟨G (s₀ q), fun z hz => ?_⟩
        have hzq : pullback.fst sC' (W.ι ≫ sT) (s₀ q) = q := by
          change (s₀ ≫ pullback.fst sC' (W.ι ≫ sT)).base q = q
          rw [hs₀, pullback.lift_fst]; rfl
        apply hginj
        rw [hGΦ, hGΦ, hv z hz, hv (s₀ q) hzq]
      have hrig := lift_comp_eq_of_contracts sC' sT (i ≫ U.ι ≫ sV) hC'dim hT hg W hWne G hGs q
        (hQc _) hGconst t₀ t₁ ht₀ ht₁
      have h4 : (pullback.lift (𝟙 C') (sC' ≫ t₀) (by simp [ht₀]) ≫ Ψ) ≫ F ≫ U'.ι =
          (pullback.lift (𝟙 C') (sC' ≫ t₁) (by simp [ht₁]) ≫ Ψ) ≫ F ≫ U'.ι := by
        have := congrArg (· ≫ i) hrig
        simp only [Category.assoc, hG, hΦ'def] at this
        simpa only [Category.assoc] using this
      rw [hslice t₀ ht₀, hslice t₁ ht₁] at h4
      have h5 : pullback.lift (f := sC') (g := sM) (𝟙 C') (sC' ≫ t₀ ≫ τ) (by simp [hτ, ht₀]) ≫ F =
          pullback.lift (f := sC') (g := sM) (𝟙 C') (sC' ≫ t₁ ≫ τ) (by simp [hτ, ht₁]) ≫ F :=
        (cancel_mono U'.ι).mp (by simpa only [Category.assoc] using h4)
      have hmap : ∀ (x : Spec (.of k) ⟶ M) (hx : x ≫ sM = 𝟙 _),
          pullback.map sC' (𝟙 _) sC' sM (𝟙 C') x (𝟙 _) (by simp) (by simp [hx]) =
            pullback.fst sC' (𝟙 _) ≫ pullback.lift (𝟙 C') (sC' ≫ x) (by simp [hx]) := by
        intro x hx
        apply pullback.hom_ext
        · rw [pullback.lift_fst, Category.comp_id, Category.assoc, pullback.lift_fst,
            Category.comp_id]
        · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc,
            pullback.condition, Category.comp_id]
      have hx0 : (t₀ ≫ τ) ≫ sM = 𝟙 _ := by rw [Category.assoc, hτ, ht₀]
      have hx1 : (t₁ ≫ τ) ≫ sM = 𝟙 _ := by rw [Category.assoc, hτ, ht₁]
      have hxy := hFinj k (𝟙 _) (t₀ ≫ τ) (t₁ ≫ τ) hx0 hx1 (by
        rw [hmap _ hx0, hmap _ hx1]
        exact (Category.assoc _ _ _).trans
          ((congrArg (pullback.fst sC' (𝟙 _) ≫ ·) h5).trans (Category.assoc _ _ _).symm))
      exact ht₁τ (hxy.symm.trans ht₀τ)
    exact MMP.Flips.two_le_topologicalKrullDim_of_specializes (subset_closure ⟨_, rfl⟩)
      (subset_closure ⟨_, rfl⟩) (subset_closure ⟨_, rfl⟩) haγ hγc haγ' hγc'
  have hd₀ : invertibleCurveDegree k sC' hC'dim.le ((Scheme.Modules.pullback
      (pullback.lift (𝟙 C') (sC' ≫ t₀) (by simp [ht₀]) ≫ Φ)).obj H) =
      invertibleCurveDegree k sC' hC'dim.le ((Scheme.Modules.pullback (φ ≫ i ≫ U.ι)).obj H) :=
    invertibleCurveDegree_eq_of_iso k sC' _ ((Scheme.Modules.pullbackCongr he).app H)
  have hgen : ∃ W' : W.toScheme.Opens, (W' : Set W.toScheme).Nonempty ∧
      ∀ (t : Spec (.of k) ⟶ W.toScheme) (ht : t ≫ W.ι ≫ sT = 𝟙 _),
        (∀ x, t.base x ∈ W') →
          invertibleCurveDegree k sC' hC'dim.le
            ((Scheme.Modules.pullback
              (pullback.lift (𝟙 C') (sC' ≫ t) (by simp [ht]) ≫ Φ)).obj H) =
            invertibleCurveDegree k sC' hC'dim.le
              ((Scheme.Modules.pullback (φ ≫ i ≫ U.ι)).obj H) := by
    haveI : AlgebraicGeometry.IsVariety k sT := isVariety_of_smooth_of_connected sT
    haveI : IsIntegral T := (inferInstance : AlgebraicGeometry.IsVariety k sT).toIsIntegral
    haveI : ConnectedSpace W.toScheme := inferInstance
    refine ⟨⊤, ⟨t₀ pt, trivial⟩, fun t ht _ => ?_⟩
    rw [← hd₀]
    exact invertibleCurveDegree_pullback_lift_comp_eq sC' hC'dim.le (W.ι ≫ sT) Φ H t t₀ ht ht₀
  obtain ⟨L, hL, hL0, hL1⟩ := exists_isRationalCurve_degreeOn_lt_of_constant_on_sections k sC' sT sV
    hC'dim hT W hWne Φ hΦ hdim hb Q hQinj hQc hconst H hH _ hd hgen
  exact ⟨L, hL, hL0, hL1⟩

end Core

/-- The arithmetic of the limit `q → ∞`: for `q = p ^ a` large, the number
`b = ⌊(q κ - 1 - 2 g) / n⌋ + 1 - g` of fixed points is positive, and any positive integer `x`
with `x b < 2 q D` is at most `2 n D / κ`. -/
private theorem exists_pow_bound (p : ℕ) (hp : 2 ≤ p) (n : ℕ) (hn : 1 ≤ n) (g : ℕ) (κ D : ℤ)
    (hκ : 0 < κ) :
    ∃ a : ℕ, 0 < ((p : ℤ) ^ (a + 1) * κ - 1 - 2 * g) / n + 1 - g ∧
      ∀ x : ℤ, 0 < x → x * (((p : ℤ) ^ (a + 1) * κ - 1 - 2 * g) / n + 1 - g) <
        2 * p ^ (a + 1) * D →
        (x : ℚ) ≤ 2 * n * D / κ := by
  set N : ℤ := ⌊(2 * n * D / κ : ℚ)⌋ with hN
  have hNlt : (2 * n * D / κ : ℚ) < N + 1 := Int.lt_floor_add_one _
  have hNle : (N : ℚ) ≤ 2 * n * D / κ := Int.floor_le _
  have hκq : (0 : ℚ) < κ := by exact_mod_cast hκ
  have hε : 2 * n * D < (N + 1) * κ := by
    have : (2 * n * D : ℚ) < (N + 1) * κ := by
      rw [div_lt_iff₀ hκq] at hNlt; exact hNlt
    exact_mod_cast this
  have hn0 : (0 : ℤ) < n := by exact_mod_cast hn
  set c : ℕ := (N.toNat + 1) * (2 * g + n * g) + 1 with hc
  obtain ⟨a, ha⟩ : ∃ a : ℕ, c < p ^ (a + 1) :=
    ⟨c, (Nat.lt_pow_self (by omega)).trans_le (Nat.pow_le_pow_right (by omega) (by omega))⟩
  set q : ℤ := (p : ℤ) ^ (a + 1) with hq
  have hcq : (c : ℤ) < q := by rw [hq]; exact_mod_cast ha
  have hq0 : 0 < q := by positivity
  set b := (q * κ - 1 - 2 * g) / n + 1 - g with hb
  have hdiv : (q * κ - 1 - 2 * g) - (n - 1) ≤ n * ((q * κ - 1 - 2 * g) / n) := by
    have h1 := Int.emod_add_mul_ediv (q * κ - 1 - 2 * g) n
    have h2 := Int.emod_lt_of_pos (q * κ - 1 - 2 * g) hn0
    linarith
  have hnb : q * κ - 2 * g - n * g ≤ n * b := by
    rw [hb, mul_sub, mul_add]; linarith
  have hc1 : (2 * g + n * g : ℤ) < q := by
    have : (2 * g + n * g : ℤ) ≤ c := by
      rw [hc]; push_cast
      have : (0:ℤ) ≤ 2 * g + n * g := by positivity
      nlinarith [show (0:ℤ) ≤ N.toNat from by positivity]
    linarith
  have hb0 : 0 < b := by
    have hκ1 : 1 ≤ κ := hκ
    have : 0 < n * b := by nlinarith
    exact pos_of_mul_pos_right this hn0.le
  refine ⟨a, hb0, ?_⟩
  intro x hx hxb
  rcases le_or_gt D 0 with hD | hD
  · exfalso
    nlinarith [mul_pos hx hb0]
  · have hN0 : 0 ≤ N := by
      rw [hN]; apply Int.floor_nonneg.mpr; positivity
    have hNt : (N.toNat : ℤ) = N := Int.toNat_of_nonneg hN0
    have hcN : (N + 1) * (2 * g + n * g) < q := by
      have : (N + 1) * (2 * g + n * g) ≤ (c : ℤ) := by
        rw [hc]; push_cast; rw [hNt]; linarith
      linarith
    have key : 2 * q * D * n < (N + 1) * (n * b) := by
      have h1 : (N + 1) * (q * κ - 2 * g - n * g) ≤ (N + 1) * (n * b) :=
        mul_le_mul_of_nonneg_left hnb (by linarith)
      have h2 : 2 * q * D * n < (N + 1) * (q * κ - 2 * g - n * g) := by
        have : q * (2 * n * D) < q * ((N + 1) * κ) := mul_lt_mul_of_pos_left hε hq0
        nlinarith
      linarith
    have hxN : x < N + 1 := by
      by_contra hcon
      have hcon : N + 1 ≤ x := not_lt.mp hcon
      have hb1 : 0 < n * b := mul_pos hn0 hb0
      have : (N + 1) * (n * b) ≤ x * (n * b) := mul_le_mul_of_nonneg_right hcon hb1.le
      nlinarith
    have : (x : ℚ) ≤ N := by exact_mod_cast (by omega : x ≤ N)
    linarith

/-- **A bounded rational curve from a curve in a smooth open, in characteristic `p > 0`.**
Let `V` be projective over an algebraically closed field `k` of characteristic `p > 0`, `U ⊆ V`
an open which is smooth of relative dimension `n` over `k`, and `i : C ⟶ U` a smooth projective
curve of genus `≥ 1` with `κ = -deg(Ωⁿ_{U/k}|_C) > 0`. For an ample invertible sheaf `H` on `V`
there is a rational curve `L ⊆ V` with `0 < H · L ≤ 2n (H · C) / κ`. -/
@[mmp "lem_fourfold_positive_characteristic_smooth_locus_slope"]
public theorem exists_isRationalCurve_degreeOn_le_of_charP
    {k : Type u} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {V : Scheme.{u}} (sV : V ⟶ Spec (.of k)) (hV : IsProjectiveMorphism sV)
    (U : V.Opens) (n : ℕ) [SmoothOfRelativeDimension n (U.ι ≫ sV)]
    {C : Scheme.{u}} (i : C ⟶ U.toScheme) [IsClosedImmersion i]
    [AlgebraicGeometry.IsCurve k (i ≫ U.ι ≫ sV)]
    [AlgebraicGeometry.IsProjectiveVariety k (i ≫ U.ι ≫ sV)] [Smooth (i ≫ U.ι ≫ sV)]
    (hg : 1 ≤ genus (i ≫ U.ι ≫ sV))
    (hκ :
      haveI : Stacks.Ample.IsInvertibleModule U.toScheme
          (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
        Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
      Mori.degreeOn k (U.ι ≫ sV) i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ U.ι ≫ sV)).le
        (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) < 0)
    (H : V.Modules) [Stacks.Ample.IsInvertibleModule V H] (hH : Stacks.Ample.IsAmple V H) :
    haveI : Stacks.Ample.IsInvertibleModule U.toScheme
        (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
      Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
    haveI : IsProper ((i ≫ U.ι) ≫ sV) := by rw [Category.assoc]; infer_instance
    ∃ (L : V.IdealSheafData) (hL : Mori.IsRationalCurve sV L),
      haveI := hL.2.1
      0 < Mori.degreeOn k sV L.subschemeι hL.1.2.le H ∧
        (Mori.degreeOn k sV L.subschemeι hL.1.2.le H : ℚ) ≤
          2 * n * Mori.degreeOn k sV (i ≫ U.ι) (IsCurve.topologicalKrullDim_eq_one
            (f := i ≫ U.ι ≫ sV)).le H /
            (-Mori.degreeOn k (U.ι ≫ sV) i (IsCurve.topologicalKrullDim_eq_one
              (f := i ≫ U.ι ≫ sV)).le (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n)) := by
  haveI hω : Stacks.Ample.IsInvertibleModule U.toScheme
      (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
    Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
  haveI : IsProper ((i ≫ U.ι) ≫ sV) := by rw [Category.assoc]; infer_instance
  have hdimC := (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := i ≫ U.ι ≫ sV)).le
  set κ : ℤ := -Mori.degreeOn k (U.ι ≫ sV) i hdimC
    (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) with hκdef
  set D : ℤ := Mori.degreeOn k sV (i ≫ U.ι) hdimC H with hDdef
  have hκ0 : 0 < κ := by rw [hκdef]; linarith
  have hn : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    refine lt_irrefl (0 : ℤ) (lt_of_eq_of_lt ?_ hκ)
    refine (invertibleCurveDegree_eq_zero_of_iso_unit k (i ≫ U.ι ≫ sV) hdimC _ ?_).symm
    exact (Scheme.Modules.pullback i).mapIso
      (Scheme.Hom.relativeDifferentialFormsZeroIso (U.ι ≫ sV)) ≪≫
        Scheme.Modules.pullbackUnitIso i
  obtain ⟨a, hb0, hx⟩ := exists_pow_bound p (Fact.out : p.Prime).two_le n hn
    (genus (i ≫ U.ι ≫ sV)) κ D hκ0
  obtain ⟨sC', φ, hc', hp', hs', hφ, hφs, hgen, hdeg⟩ := exists_frobeniusCover p (i ≫ U.ι ≫ sV) a
  set b : ℕ := ((((p : ℤ) ^ (a + 1) * κ - 1 - 2 * genus (i ≫ U.ι ≫ sV)) / n + 1 -
    genus (i ≫ U.ι ≫ sV)).toNat) with hbdef
  have hbz : (b : ℤ) = ((p : ℤ) ^ (a + 1) * κ - 1 - 2 * genus (i ≫ U.ι ≫ sV)) / n + 1 -
      genus (i ≫ U.ι ≫ sV) := Int.toNat_of_nonneg hb0.le
  have hbpos : 0 < b := by omega
  -- the degrees on the cover
  have hdegω : invertibleCurveDegree k sC' (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one
      (f := sC')).le ((Scheme.Modules.pullback (φ ≫ i)).obj
        (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n)) = -(p ^ (a + 1) * κ) := by
    let e : (Scheme.Modules.pullback (φ ≫ i)).obj
        (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) ≅ (Scheme.Modules.pullback φ).obj
          ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n)) :=
      ((Scheme.Modules.pullbackComp φ i).app _).symm
    rw [invertibleCurveDegree_eq_of_iso k sC' _ e, hdeg, hκdef]
    simp only [mul_neg, neg_neg]
    rfl
  have hdegH : invertibleCurveDegree k sC' (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one
      (f := sC')).le ((Scheme.Modules.pullback (φ ≫ i ≫ U.ι)).obj H) = p ^ (a + 1) * D := by
    let e : (Scheme.Modules.pullback (φ ≫ i ≫ U.ι)).obj H ≅ (Scheme.Modules.pullback φ).obj
        ((Scheme.Modules.pullback (i ≫ U.ι)).obj H) :=
      ((Scheme.Modules.pullbackComp φ (i ≫ U.ι)).app _).symm
    rw [invertibleCurveDegree_eq_of_iso k sC' _ e, hdeg, hDdef]
    congr 1
  have hD0 : 0 < D := by
    haveI : IsProper sV := isProper_of_isProjectiveMorphism sV hV
    haveI : IsProper ((i ≫ U.ι) ≫ sV) := by rw [Category.assoc]; infer_instance
    haveI : IsProper (i ≫ U.ι) := IsProper.of_comp (i ≫ U.ι) sV
    haveI : IsClosedImmersion (i ≫ U.ι) :=
      (IsClosedImmersion.iff_isProper_and_mono (i ≫ U.ι)).mpr ⟨inferInstance, inferInstance⟩
    haveI : AlgebraicGeometry.IsCurve k ((i ≫ U.ι) ≫ sV) := by
      rw [Category.assoc]; infer_instance
    exact invertibleCurveDegree_pos_of_isAmple_of_isCurve k ((i ≫ U.ι) ≫ sV) hdimC _
      (isAmple_pullback_of_isFinite (i ≫ U.ι) H
        (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple V H hH))
  have hdpos : 0 < invertibleCurveDegree k sC' (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one
      (f := sC')).le ((Scheme.Modules.pullback (φ ≫ i ≫ U.ι)).obj H) := by
    rw [hdegH]
    exact mul_pos (pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _) hD0
  obtain ⟨L, hL, hL0, hL1⟩ := exists_isRationalCurve_of_cover sV hV U n i hg H hH sC' φ hφ hφs b
    hbpos (by
      rw [hdegω, hgen, hbz, neg_neg]
      set X := (p : ℤ) ^ (a + 1) * κ - 1 - 2 * genus (i ≫ U.ι ≫ sV) with hX
      have h2 : (n : ℤ) * (X / n) ≤ X :=
        Int.mul_ediv_self_le (by exact_mod_cast (show n ≠ 0 by omega))
      have h3 : (n : ℤ) * (X / n + 1 - genus (i ≫ U.ι ≫ sV)) =
          n * (X / n) + n - n * genus (i ≫ U.ι ≫ sV) := by ring
      rw [h3]
      nlinarith) hdpos
  refine ⟨L, hL, hL0, ?_⟩
  apply hx _ hL0
  rw [← hbz]
  rw [hdegH] at hL1
  have hbq : (0 : ℚ) < b := by exact_mod_cast hbpos
  have hlt := (lt_div_iff₀ hbq).mp hL1
  haveI := hL.2.1
  have h' : ((Mori.degreeOn k sV L.subschemeι hL.1.2.le H * b : ℤ) : ℚ) <
      ((2 * p ^ (a + 1) * D : ℤ) : ℚ) := by
    push_cast at hlt ⊢; linarith
  exact_mod_cast h'

end MMP.Fourfold
