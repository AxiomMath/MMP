module

public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
public import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
public import MMP.RingTheory.PowerSeries.CompleteLocalRing
public import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings

/-!
# Surfaces, blow-ups and divisors: foundational inputs

This file collects four foundational facts about surfaces, blow-ups and divisors.

* **Numerical pull-back.** Let `X` be a normal surface over an algebraically closed field `k` of
  characteristic zero, `f : Y ⟶ X` a resolution with exceptional curves `E₁, …, E_r`, `K_Y` a
  canonical divisor of `Y` and `Δ` a `ℚ`-divisor on `X`. The linear system
  `∑ᵢ aᵢ (Eᵢ · Eⱼ) = ((K_Y + f⁻¹_* Δ) · Eⱼ)` has exactly one solution `a ∈ ℚ^r`. The exceptional
  curves are finitely many, being irreducible components of the preimage of the finite set of
  points with positive-dimensional fibre, and their intersection matrix is negative definite
  (`MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism`), hence
  invertible over `ℚ`.
* **Blow-ups of varieties.** The blow-up of a variety along a proper closed subscheme `W` is a
  projective birational morphism from a variety, and an isomorphism over the complement of `W`.
* **Cartier and Weil divisors.** On a non-singular variety of pure dimension `n` the cycle map
  `Div(X) → WDiv(X)` is an isomorphism of groups, every local ring being a UFD.
* **Formal coordinates.** At a closed point `y` of a smooth surface over an algebraically closed
  field, a regular system of parameters `x, z` gives `k[[X, Z]] ≅ 𝒪̂_{Y,y}`, by Cohen's
  structure theorem and a dimension count; and completion preserves the length of `𝒪_{Y,y}/I`
  for every ideal `I` of finite colength, since such an `I` contains a power of the maximal ideal.

## Main results

* `MMP.Mori.existsUnique_isNumericalPullbackSolution`: exactly one `ℚ`-divisor supported on the
  exceptional curves solves the numerical pull-back equations.
* `MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational_and_isIso_restrict`
  — the blow-up of a variety along a proper closed subscheme `W` is a variety, and the blow-up
  morphism is projective, birational and an isomorphism over the complement of `W`.
* `MMP.Intersection.coe_cycleMapAddEquivOfIsSmoothScheme`: the cycle map underlies an additive
  equivalence `X.CartierDivisor ≃+ WeilDivisor X n`.
* `MMP.Threefold.existsUnique_algHom_X_eq_bijective_and_length_quotient_map_eq`: formal
  coordinates at a closed point of a smooth surface, and invariance of finite lengths under
  completion.

## Implementation notes

* A vector `a ∈ ℚ^r` is encoded, as in `MMP.Mori.IsNumericalPullbackSolution`, as the
  `ℚ`-divisor `∑ᵢ aᵢ Eᵢ` on `Y` whose support consists of `f`-exceptional curves; this needs no
  enumeration of the exceptional curves.
* A closed subscheme `W` is encoded by its ideal sheaf `I : X.IdealSheafData`; `W ≠ X` is
  `I ≠ ⊥`, and `X ∖ W` is the open `I.support.compl`.
* "The cycle map is an isomorphism" is an `AddEquiv` whose underlying function is
  `MMP.Intersection.cycleMap`.
* The length statement is given for an arbitrary ideal of finite colength rather than only for
  the ideal `(f, g)` of two curves without common component through `y`, which has finite
  colength.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §0.4 and
  Notation 4.1
* [Lazarsfeld, *Positivity in Algebraic Geometry I*][lazarsfeld2004], Remark 1.1.4
* [Stacks Project, Tag 0C2M](https://stacks.math.columbia.edu/tag/0C2M)
-/

public section

universe u

open CategoryTheory AlgebraicGeometry

/-! ### The numerical pull-back on a resolution of a surface -/

namespace MMP.Mori

section NumericalPullback

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

section Helpers

variable {sX : X ⟶ Spec (.of k)} {f : Y ⟶ X}

/-- A resolution of a normal surface has finitely many exceptional curves. -/
private theorem finite_setOf_isExceptionalCurve [IsLocallyNoetherian Y] [CompactSpace Y]
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsSmoothResolution sX f) :
    {E : MMP.Mori.PrimeDivisor Y | IsExceptionalCurve f E.idealSheaf}.Finite := by
  obtain ⟨S, -, -, -, ⟨hT, -⟩, hexc, -⟩ :=
    exists_finite_isIso_and_isExceptionalCurve_iff hX hdim hf
  have : IsNoetherian Y := ⟨⟩
  obtain ⟨𝒮, h𝒮, h𝒮c, h𝒮i, h𝒮eq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  have hmem : ∀ E : MMP.Mori.PrimeDivisor Y,
      IsExceptionalCurve f E.idealSheaf → E.support ∈ 𝒮 := by
    intro E hE
    obtain ⟨-, hmax⟩ := (hexc _).1 hE
    obtain ⟨z, hz, hsub⟩ := (isIrreducible_iff_sUnion_isClosed.1 hmax.prop.1) h𝒮.toFinset
      (fun z hz => h𝒮c z (h𝒮.mem_toFinset.1 hz))
      (by
        rw [h𝒮.coe_toFinset, ← h𝒮eq]
        exact hmax.prop.2)
    have hz' := h𝒮.mem_toFinset.1 hz
    have hle : z ⊆ f.base ⁻¹' S := h𝒮eq ▸ Set.subset_sUnion_of_mem hz'
    have : E.support = z := le_antisymm hsub (hmax.2 ⟨h𝒮i z hz', hle⟩ hsub)
    exact this ▸ hz'
  refine (h𝒮.preimage ?_).subset hmem
  intro E _ E' _ h
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  have h' : closure ({E.genericPoint} : Set Y) = closure {E'.genericPoint} := by
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact h
  exact (inseparable_iff_closure_eq.2 h').eq

/-- An exceptional curve of a resolution of a normal surface is a proper curve of `Y`, with the
generic point of the curve, contracted by `f`. -/
private theorem exists_properCurve [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsSmoothResolution sX f) (E : MMP.Mori.PrimeDivisor Y)
    (hE : IsExceptionalCurve f E.idealSheaf) :
    ∃ C : ProperCurve (f ≫ sX), C.point = E.genericPoint ∧ C.IsContractedBy f := by
  obtain ⟨S, -, -, -, ⟨hT, hprop⟩, hexc, -⟩ :=
    exists_finite_isIso_and_isExceptionalCurve_iff hX hdim hf
  have h := vanishingIdeal_closure_genericPoint_eq_idealSheaf E
  have hcl : closure ({E.genericPoint} : Set Y) = E.support :=
    (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have hsub : E.support ⊆ f.base ⁻¹' S := ((hexc _).1 hE).2.prop.2
  have hp : IsProper (E.idealSheaf.subschemeι ≫ f ≫ sX) := by
    set T := Scheme.IdealSheafData.vanishingIdeal ⟨f.base ⁻¹' S, hT⟩
    have hle : T.subschemeι.ker ≤ E.idealSheaf.subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι, ← h]
      exact Scheme.IdealSheafData.vanishingIdeal_antimono (by
        change closure ({E.genericPoint} : Set Y) ⊆ f.base ⁻¹' S
        rwa [hcl])
    let l := IsClosedImmersion.lift T.subschemeι E.idealSheaf.subschemeι hle
    have hl : l ≫ T.subschemeι = E.idealSheaf.subschemeι := IsClosedImmersion.lift_fac _ _ hle
    have : IsProper (l ≫ T.subschemeι) := by
      rw [hl]
      infer_instance
    have : IsProper l := IsProper.of_comp l T.subschemeι
    rw [← hl, Category.assoc]
    infer_instance
  obtain ⟨x, hx⟩ := hE.2
  refine ⟨⟨E.genericPoint, ⟨?_, ?_⟩⟩, rfl, fun y hy => ?_⟩
  · change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal _).subscheme = 1
    rw [h]
    exact hE.1.2
  · change IsProper ((Scheme.IdealSheafData.vanishingIdeal _).subschemeι ≫ f ≫ sX)
    rw [h]
    exact hp
  · change y ∈ closure ({E.genericPoint} : Set Y) at hy
    rw [hcl] at hy
    have h1 : f y ∈ ({x} : Set X) := hx ▸ ⟨y, hy, rfl⟩
    have h2 : f E.genericPoint ∈ ({x} : Set X) :=
      hx ▸ ⟨E.genericPoint, (hcl ▸ subset_closure rfl : E.genericPoint ∈ E.support), rfl⟩
    change f y = f E.genericPoint
    rw [Set.mem_singleton_iff.1 h1, Set.mem_singleton_iff.1 h2]

/-- The `ℚ`-divisor `1 · P` of a prime divisor is the `ℚ`-divisor of the divisor `P`. -/
private theorem single_one_eq_toQDivisor (P : MMP.Mori.PrimeDivisor Y) :
    (Finsupp.single P 1 : QDivisor Y) = Divisor.toQDivisor (Finsupp.single P 1) := by
  ext F
  by_cases hF : P = F
  · subst hF
    simp [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom]
  · simp [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom, hF]

/-- **A nonsingular linear system has exactly one finitely supported solution.** If `E` is an
injective family indexed by `Fin n` and the matrix `(N (E i) j)` is nonsingular, then exactly
one finitely supported `a`, supported on the range of `E`, has `∑_F a F * N F j = β j` for every
`j`. -/
private theorem existsUnique_finsupp_sum_mul_eq {α : Type*} {n : ℕ} {E : Fin n → α}
    (hE : Function.Injective E) (N : α → Fin n → ℚ) (β : Fin n → ℚ)
    (hM : (Matrix.of fun i j => N (E i) j).det ≠ 0) :
    ∃! a : α →₀ ℚ, (∀ F ∈ a.support, F ∈ Set.range E) ∧
      ∀ j, ∑ F ∈ a.support, a F * N F j = β j := by
  classical
  have hsum : ∀ a : α →₀ ℚ, (∀ F ∈ a.support, F ∈ Set.range E) → ∀ j,
      ∑ F ∈ a.support, a F * N F j = ∑ i, a (E i) * N (E i) j := by
    intro a ha j
    rw [show ∑ i, a (E i) * N (E i) j = ∑ F ∈ Finset.univ.map ⟨E, hE⟩, a F * N F j by
      rw [Finset.sum_map]; rfl]
    refine Finset.sum_subset (fun F hF => ?_) (fun F _ hF => ?_)
    · obtain ⟨i, rfl⟩ := ha F hF
      exact Finset.mem_map_of_mem _ (Finset.mem_univ i)
    · rw [Finsupp.notMem_support_iff.1 hF, zero_mul]
  obtain ⟨c, hc, huniq⟩ := MMP.MatrixPosDef.existsUnique_add_sum_mul_eq_zero _ hM (-β)
  simp only [Pi.neg_apply, Matrix.of_apply, neg_add_eq_zero] at hc huniq
  set a := Finsupp.mapDomain E (Finsupp.equivFunOnFinite.symm c)
  have haE : ∀ i, a (E i) = c i := fun i => by simp [a, Finsupp.mapDomain_apply_of_injective hE]
  have ha0 : ∀ F ∉ Set.range E, a F = 0 := fun F hF => Finsupp.mapDomain_of_notMem_range _ _ hF
  have hsupp : ∀ F ∈ a.support, F ∈ Set.range E := fun F hF =>
    Classical.byContradiction fun h => Finsupp.mem_support_iff.1 hF (ha0 F h)
  refine ⟨a, ⟨hsupp, fun j => ?_⟩, fun a' ⟨ha's, ha'eq⟩ => ?_⟩
  · rw [hsum a hsupp j]
    simp only [haE, hc j]
  · have hvec : (fun i => a' (E i)) = c :=
      huniq _ fun j => by rw [← ha'eq j, hsum a' ha's j]
    ext F
    by_cases hF : F ∈ Set.range E
    · obtain ⟨i, rfl⟩ := hF
      rw [haE, ← hvec]
    · rw [ha0 F hF]
      exact Finsupp.notMem_support_iff.1 fun h => hF (ha's F h)

end Helpers

/-- **The numerical pull-back exists and is unique.** Let `X` be a normal surface over an
algebraically closed field `k` of characteristic zero, `f : Y ⟶ X` a resolution, `K` a canonical
divisor of `Y` and `Δ` a `ℚ`-divisor on `X`. Then exactly one `ℚ`-divisor `a = ∑ aᵢ Eᵢ`, supported
on the `f`-exceptional curves, satisfies `∑ᵢ aᵢ (Eᵢ · Eⱼ) = ((K + f⁻¹_* Δ) · Eⱼ)` for every
`f`-exceptional curve `Eⱼ`. -/
@[mmp "lem_mmp_foundation_algebraic_surface_numerical_pullback_unique"]
theorem existsUnique_isNumericalPullbackSolution [IsAlgClosed k] [CharZero k]
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsSmoothResolution sX f) (K : Divisor Y) (hK : K.IsCanonicalDivisor (f ≫ sX) 2)
    (Δ : QDivisor X) :
    ∃! a : QDivisor Y, IsNumericalPullbackSolution sX f K Δ a := by
  have hsm := hf.isSmoothScheme
  obtain ⟨hYn, hdimY, -⟩ := hf.isNormalVariety hX
  have : IsProper f := hf.isProper
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  obtain ⟨n, E, hErange⟩ := (finite_setOf_isExceptionalCurve hX hdim hf).fin_embedding
  have hexc : ∀ F : MMP.Mori.PrimeDivisor Y, IsExceptionalCurve f F.idealSheaf ↔ F ∈ Set.range E :=
    fun F => by rw [hErange]; rfl
  choose C hC hCc using fun i => exists_properCurve hX hdim hf (E i) ((hexc _).2 ⟨i, rfl⟩)
  let N : MMP.Mori.PrimeDivisor Y → Fin n → ℚ := fun F j =>
    (Divisor.toQDivisor (Finsupp.single F 1)).intersectionNumber k (f ≫ sX) (C j).ι
      (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm F)
  have hN : ∀ F j, IsIntersectionNumber (f ≫ sX) (Finsupp.single F 1) (E j).idealSheaf (N F j) := by
    intro F j
    rw [single_one_eq_toQDivisor]
    exact isIntersectionNumber_of_properCurve _ _ (C j) (E j) (hC j)
  set D₀ : QDivisor Y := Divisor.toQDivisor K + inverseTransformDivisor f Δ
  let β : Fin n → ℚ := fun j => D₀.intersectionNumber k (f ≫ sX) (C j).ι (C j).dim_le
    (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm D₀)
  have hβ : ∀ j, IsIntersectionNumber (f ≫ sX) D₀ (E j).idealSheaf (β j) := fun j =>
    isIntersectionNumber_of_properCurve _ _ (C j) (E j) (hC j)
  have hM := MMP.MatrixPosDef.det_ne_zero_of_posDef_neg_map (Matrix.of fun i j => N (E i) j)
    (MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism
      hYn.1 hsm (hdimY.trans hdim) hX.1 rfl hf.isBirationalMorphism E E.injective C hC hCc)
  refine (existsUnique_congr fun a => ?_).2 (existsUnique_finsupp_sum_mul_eq E.injective N β hM)
  refine ⟨fun ⟨_, _, hs, heq⟩ => ⟨fun F hF => (hexc F).1 (hs F hF), fun j => ?_⟩,
    fun ⟨hs, heq⟩ => ⟨hf, ⟨2, hK⟩, fun F hF => (hexc F).2 (hs F hF), fun Ej hEj => ?_⟩⟩
  · obtain ⟨c, b, h1, h2, h3⟩ := heq (E j) ((hexc _).2 ⟨j, rfl⟩)
    rw [← h2.unique (hβ j), ← h3]
    exact Finset.sum_congr rfl fun F hF => by rw [(h1 F hF).unique (hN F j)]
  · obtain ⟨j, rfl⟩ := (hexc Ej).1 hEj
    exact ⟨fun F => N F j, β j, fun F _ => hN F j, hβ j, heq j⟩

end NumericalPullback

end MMP.Mori

/-! ### The blow-up of a variety along a proper closed subscheme -/

namespace MMP.Flips.ResolutionInputs

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- **The blow-up of a variety along a proper closed subscheme.** Let `X` be a variety over `k`
with structure morphism `f` and `I ≠ ⊥` the ideal sheaf of a closed subscheme `W ⊊ X`. Then
`B_I X`, with structure morphism `blowUpToBase I ≫ f`, is a variety over `k`; the blow-up
`blowUpToBase I` is projective and birational; and it is an isomorphism over `X ∖ W`, i.e. its
restriction to `I.support.compl` is an isomorphism. -/
@[mmp "lem_mmp_foundation_km_blowup_variety_projective"]
theorem isVariety_blowUp_and_isProjective_and_isBirational_and_isIso_restrict
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsVariety k f]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    IsVariety k (blowUpToBase I ≫ f) ∧ IsProjective (blowUpToBase I) ∧
      IsBirational (blowUpToBase I) ∧ IsIso (blowUpToBase I ∣_ I.support.compl) :=
  let ⟨h₁, h₂, h₃⟩ := isVariety_blowUp_and_isProjective_and_isBirational f I hI
  ⟨h₁, h₂, h₃, inferInstance⟩

end MMP.Flips.ResolutionInputs

/-! ### Cartier and Weil divisors on a non-singular variety -/

namespace MMP.Intersection

/-- On a non-singular variety `X` of pure dimension `n` over a field `k`, the cycle map
`Div(X) → WDiv(X)` as an additive equivalence (Lazarsfeld Rem. 1.1.4). -/
@[expose] noncomputable def cycleMapAddEquivOfIsSmoothScheme {k : Type*} [Field k] {X : Scheme}
    [X.Over (Spec (.of k))] [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X] {n : ℕ}
    (hX : IsPureDimensional X n) [MMP.Mori.IsVariety k (X ↘ Spec (.of k))]
    (hsm : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of k))) :
    X.CartierDivisor ≃+ WeilDivisor X n :=
  AddEquiv.ofBijective _ (cycleMap_bijective_of_isSmoothScheme hX hsm)

/-- On a non-singular variety `X` of pure dimension `n` over a field `k`, the cycle map
`MMP.Intersection.cycleMap : X.CartierDivisor →+ WeilDivisor X n` is an isomorphism: it is the
underlying function of the additive equivalence `cycleMapAddEquivOfIsSmoothScheme`. -/
@[simp, mmp "lem_mmp_foundation_smooth_cartier_weil_cycle_isomorphism"]
theorem coe_cycleMapAddEquivOfIsSmoothScheme {k : Type*} [Field k] {X : Scheme}
    [X.Over (Spec (.of k))] [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X] {n : ℕ}
    (hX : IsPureDimensional X n) [MMP.Mori.IsVariety k (X ↘ Spec (.of k))]
    (hsm : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of k))) :
    ⇑(cycleMapAddEquivOfIsSmoothScheme hX hsm) = ⇑(cycleMap hX) :=
  rfl

end MMP.Intersection

/-! ### Formal coordinates at a closed point of a smooth surface -/

namespace MMP.Threefold

section FormalCoordinates

open IsLocalRing

/-- In a local ring, an ideal of finite colength contains a power of the maximal ideal. -/
private theorem exists_maximalIdeal_pow_le_of_length_ne_top {R : Type*} [CommRing R]
    [IsLocalRing R] {I : Ideal R}
    (hI : Module.length R (R ⧸ I) ≠ ⊤) : ∃ n : ℕ, maximalIdeal R ^ n ≤ I := by
  have : IsArtinian R (R ⧸ I) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hI)).2
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_tower R this
  exact exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I

/-- If `Mⁿ ⊆ I` with `M` finitely generated, then `R → R̂_M/IR̂_M` is surjective. -/
private theorem surjective_algebraMap_adicCompletion_quotient {R : Type*} [CommRing R]
    (M I : Ideal R) (hfg : M.FG) (n : ℕ) (h : M ^ n ≤ I) :
    Function.Surjective
      (algebraMap R (AdicCompletion M R ⧸ I.map (algebraMap R (AdicCompletion M R)))) := by
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ M n a)
  refine ⟨r, ?_⟩
  rw [IsScalarTower.algebraMap_apply R (AdicCompletion M R), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq]
  have hk : algebraMap R (AdicCompletion M R) r - a ∈ (AdicCompletion.eval M R n).ker := by
    have hle : M ^ n ≤ M ^ n • (⊤ : Submodule R R) := by simp
    rw [LinearMap.mem_ker, map_sub, ← AdicCompletion.factor_evalₐ_eq_eval _ _ hle,
      ← AdicCompletion.factor_evalₐ_eq_eval _ _ hle, sub_eq_zero]
    congr 1
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval hfg] at hk
  refine Submodule.smul_induction_on hk (fun m hm b _ => ?_) (fun _ _ => Ideal.add_mem _)
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (h hm))

/-- If `Mⁿ ⊆ I` with `M` finitely generated, then `ℓ(R̂_M/IR̂_M) = ℓ(R/I)`. -/
private theorem length_adicCompletion_quotient_map_eq {R : Type*} [CommRing R]
    (M I : Ideal R) (hfg : M.FG) (n : ℕ) (h : M ^ n ≤ I) :
    Module.length (AdicCompletion M R)
        (AdicCompletion M R ⧸ I.map (algebraMap R (AdicCompletion M R))) =
      Module.length R (R ⧸ I) := by
  set Â := AdicCompletion M R
  set J := I.map (algebraMap R Â)
  have hs := surjective_algebraMap_adicCompletion_quotient M I hfg n h
  let ψ : Â →ₐ[R] R ⧸ I := (Ideal.Quotient.factorₐ R h).comp (AdicCompletion.evalₐ M n)
  have hker : RingHom.ker (Algebra.ofId R (Â ⧸ J)) = I := by
    refine le_antisymm (fun r hr => ?_) (fun r hr => ?_)
    · have hJ : J ≤ RingHom.ker ψ := Ideal.map_le_iff_le_comap.mpr fun s hs' => by
        simp [ψ, AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem.mpr hs']
      rw [RingHom.mem_ker, Algebra.ofId_apply, IsScalarTower.algebraMap_apply R Â,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hr
      have := hJ hr
      rwa [RingHom.mem_ker, AlgHom.commutes, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem] at this
    · rw [RingHom.mem_ker, Algebra.ofId_apply,
        IsScalarTower.algebraMap_apply R Â, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hr
  let e : (R ⧸ I) ≃ₐ[R] Â ⧸ J :=
    (Ideal.quotientEquivAlgOfEq R hker).symm.trans (Ideal.quotientKerAlgEquivOfSurjective hs)
  rw [Module.length_eq_of_surjective (S := Â) (R := Â ⧸ J) Ideal.Quotient.mk_surjective,
    e.toLinearEquiv.length_eq, Module.length_eq_of_surjective (S := R) (R := Â ⧸ J) hs]

/-- Two `k`-algebra maps out of `k[[X₁, …, Xₙ]]` into an `I`-adically separated ring agree as
soon as they agree on the variables and send them into `I`. -/
private theorem algHom_ext_of_X_mem {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]
    (I : Ideal S) [IsHausdorff I S] {n : ℕ} {F G : MvPowerSeries (Fin n) k →ₐ[k] S}
    (hX : ∀ i, F (MvPowerSeries.X i) = G (MvPowerSeries.X i))
    (hI : ∀ i, F (MvPowerSeries.X i) ∈ I) : F = G :=
  AlgHom.coe_ringHom_injective <| mvPowerSeries_hom_ext I n _ _
    (fun r => by simp [MMP.Flips.ResolutionInputs.mvPowerSeries_C_eq_algebraMap]) hX hI

/-- If `k` maps onto the residue field of a Noetherian local `k`-algebra `R`, it maps onto the
residue field of the completion `R̂`. -/
private theorem surjective_residue_comp_algebraMap_adicCompletion {k R : Type*} [Field k]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra k R]
    (h : Function.Surjective (algebraMap k (R ⧸ maximalIdeal R))) :
    Function.Surjective ((Ideal.Quotient.mk (maximalIdeal (AdicCompletion (maximalIdeal R) R))).comp
      (algebraMap k (AdicCompletion (maximalIdeal R) R))) := by
  intro a
  obtain ⟨b, rfl⟩ := (AdicCompletion.residueField_map_bijective R).2 a
  obtain ⟨c, rfl⟩ := h b
  refine ⟨c, ?_⟩
  rw [RingHom.comp_apply, ← Ideal.Quotient.mk_algebraMap]
  erw [ResidueField.map_residue]

/-- **Formal coordinates at a closed point of a smooth surface.** Let `Y` be a smooth surface
over an algebraically closed field `k`, `y ∈ Y` a closed point and `x, z` a regular system of
parameters of `𝒪_{Y,y}`. Then there is exactly one `k`-algebra homomorphism
`F : k[[X, Z]] → 𝒪̂_{Y,y}` with `F X = x` and `F Z = z`, and it is bijective. Moreover, for every
ideal `I` of `𝒪_{Y,y}` with `𝒪_{Y,y}/I` of finite length, the quotient of the completion by the
extended ideal has the same length: `ℓ(𝒪̂_{Y,y}/I𝒪̂_{Y,y}) = ℓ(𝒪_{Y,y}/I)`. -/
@[mmp "lem_mmp_threefold_surface_formal_coordinates"]
theorem existsUnique_algHom_X_eq_bijective_and_length_quotient_map_eq
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (hY : MMP.Mori.IsVariety k sY) (hYs : MMP.Mori.IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2) {y : Y} (hy : IsClosed ({y} : Set Y))
    {x z : Y.presheaf.stalk y} (hxz : MMP.Mori.IsRegularSystemOfParameters ![x, z]) :
    letI := MMP.Mori.stalkAlgebra sY y
    (∃! F : MvPowerSeries (Fin 2) k →ₐ[k]
        AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y),
      F (MvPowerSeries.X 0) = algebraMap (Y.presheaf.stalk y) _ x ∧
        F (MvPowerSeries.X 1) = algebraMap (Y.presheaf.stalk y) _ z ∧ Function.Bijective F) ∧
    ∀ I : Ideal (Y.presheaf.stalk y),
      Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y ⧸ I) ≠ ⊤ →
        Module.length (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
            (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) ⧸
              I.map (algebraMap (Y.presheaf.stalk y)
                (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))) =
          Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y ⧸ I) := by
  letI := MMP.Mori.stalkAlgebra sY y
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let R := Y.presheaf.stalk y
  let Â := AdicCompletion (maximalIdeal R) R
  have hspan := MMP.Flips.ResolutionInputs.span_range_algebraMap_eq_maximalIdeal hxz
  have hres := surjective_residue_comp_algebraMap_adicCompletion
    (MMP.Mori.SurfaceAux.residue_surjective sY y hy)
  obtain ⟨F₀, hF₀s, hF₀X, hF₀C⟩ :=
    Stacks.CompleteLocalRing.CohenStructure.exists_surjective_eval₂Hom (maximalIdeal Â) _
      hspan (algebraMap k Â) hres
  let F : MvPowerSeries (Fin 2) k →ₐ[k] Â :=
    { F₀ with
      commutes' := fun r => by
        change F₀ (algebraMap k (MvPowerSeries (Fin 2) k) r) = _
        rw [← MMP.Flips.ResolutionInputs.mvPowerSeries_C_eq_algebraMap, hF₀C] }
  have hinj : Function.Injective F :=
    MMP.Flips.ResolutionInputs.injective_of_surjective_of_ringKrullDim_le F.toRingHom hF₀s
      (MvPowerSeries.ringKrullDim_le k 2)
      (by rw [← _root_.ringKrullDim_adicCompletion_maximalIdeal, hxz.2])
  refine ⟨⟨F, ⟨hF₀X 0, hF₀X 1, hinj, hF₀s⟩, fun G ⟨hG0, hG1, _⟩ => ?_⟩, fun I hI => ?_⟩
  · have hFX : ∀ i, F (MvPowerSeries.X i) = algebraMap R Â (![x, z] i) := hF₀X
    refine (algHom_ext_of_X_mem (maximalIdeal Â) (fun i => ?_) fun i => ?_).symm
    · rw [hFX]
      fin_cases i
      exacts [hG0.symm, hG1.symm]
    · rw [hFX, ← hspan]
      exact Ideal.subset_span ⟨i, rfl⟩
  · obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_length_ne_top hI
    exact length_adicCompletion_quotient_map_eq _ I (IsNoetherian.noetherian _) n hn

end FormalCoordinates

end MMP.Threefold

end
