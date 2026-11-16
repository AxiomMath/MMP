module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
import MMP.AlgebraicGeometry.MMP.Surface.RationalBirationalProgram
import MMP.AlgebraicGeometry.MMP.Surface.RealBirationalModel
import MMP.AlgebraicGeometry.MMP.BasepointFree.UniformRelativeFreeness
import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification
import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
import MMP.AlgebraicGeometry.Positivity.RelativeKodairaDecomposition
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoMonomialValuation
import MMP.AlgebraicGeometry.Divisor.FloorSectionsExceptionalPullback
import MMP.AlgebraicGeometry.Singularities.GenericSurfacePlaces
import MMP.AlgebraicGeometry.Divisor.FloorSectionAlgebraFG
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryAlgebra
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Positivity.AsymptoticAdjointIdeal
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# Birational finite generation for surfaces

We prove `BirationalFiniteGenerationProperty 2`. For a normal `ℚ`-factorial complex surface
projective and birational over a normal affine variety, with an effective real klt boundary, we
compactify, run the surface MMP over the compactified base, and deduce finite generation of the
floor-section algebra, persistence of the divisorial stable base primes, and the uniform
fixed-part bound along the smallest rational affine hull.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.Fold06.ThmMmpSurfaceBirationalPropertyF2

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Fourfold MMP.Mori

/-! ### Open immersions and birational morphisms -/

section OpenImmersions

/-- A nonempty open subscheme of a variety over `ℂ` has the dimension of the variety. -/
private theorem topologicalKrullDim_eq_of_isOpenImmersion {X Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [IsOpenImmersion f] [Nonempty X] : topologicalKrullDim X = topologicalKrullDim Y := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := inferInstanceAs (LocallyOfFiniteType sY)
  have hne : ((f.opensRange : Y.Opens) : Set Y).Nonempty :=
    ⟨_, ⟨Nonempty.some inferInstance, rfl⟩⟩
  have h := (AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ _ (_ ↘ Spec (.of ℂ)) _
      (TopologicalSpace.Opens.isOpen _) hne).symm
  rw [(Scheme.homeoOfIso f.isoOpensRange).isHomeomorph.topologicalKrullDim_eq]
  exact h

/-- Birational morphisms of varieties over `ℂ` preserve the dimension. -/
private theorem topologicalKrullDim_eq_of_isBirationalMorphism {X Y : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sY] {f : X ⟶ Y} (hf : IsBirationalMorphism f) :
    topologicalKrullDim X = topologicalKrullDim Y := by
  obtain ⟨W, hW, hWi⟩ := hf.exists_isOpenImmersion
  haveI : Nonempty W := ⟨⟨_, hW.some_mem⟩⟩
  rw [← topologicalKrullDim_eq_of_isOpenImmersion sX W.ι,
    topologicalKrullDim_eq_of_isOpenImmersion sY (W.ι ≫ f)]

/-- An open immersion of irreducible schemes from a nonempty scheme is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (j : X ⟶ Y) [IsOpenImmersion j] [Nonempty X] :
    IsBirationalMorphism j := by
  haveI : IsOpenImmersion ((⊤ : X.Opens).ι ≫ j) := inferInstance
  exact MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' j ⊤
    ⟨Classical.arbitrary X, trivial⟩

/-- In a pull-back square along an open immersion `ι`, a point lying over the range of `ι` lies
in the range of the base change `j`. -/
private theorem mem_range_of_isPullback {S Sb T Tb : Scheme.{0}} {j : S ⟶ Sb} {f : S ⟶ T}
    {fb : Sb ⟶ Tb} {ι : T ⟶ Tb} (h : IsPullback j f fb ι) {x : Sb}
    (hx : fb x ∈ Set.range ι) : x ∈ Set.range j := by
  have hx' : x ∈ Set.range (Limits.pullback.fst fb ι) := by
    rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨y, rfl⟩ := hx'
  refine ⟨h.isoPullback.inv y, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]

/-- In a commutative square of open immersions `j`, `ι`, a morphism `fb` restricting to a
birational morphism of irreducible schemes is birational. -/
private theorem isBirationalMorphism_of_comp_eq {S Sb T Tb : Scheme.{0}} [IrreducibleSpace S]
    [IrreducibleSpace Sb] [IrreducibleSpace Tb] [Nonempty S] {j : S ⟶ Sb} {f : S ⟶ T}
    {fb : Sb ⟶ Tb} {ι : T ⟶ Tb} [IsOpenImmersion j] [IsOpenImmersion ι]
    (h : j ≫ fb = f ≫ ι) (hf : IsBirationalMorphism f) : IsBirationalMorphism fb := by
  obtain ⟨W, hW, hWi⟩ := hf.exists_isOpenImmersion
  haveI := hWi
  have hcomp : (j ''ᵁ W).ι ≫ fb = (j.isoImage W).inv ≫ (W.ι ≫ f) ≫ ι := by
    rw [← Scheme.Hom.isoImage_inv_ι_assoc j W, h]
    simp only [Category.assoc]
  haveI : IsOpenImmersion ((j ''ᵁ W).ι ≫ fb) := by rw [hcomp]; infer_instance
  refine MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' fb (j ''ᵁ W) ?_
  obtain ⟨w, hw⟩ := hW
  exact ⟨j w, w, hw, rfl⟩

/-- Orders of a rational function pulled back along an open immersion are its orders along the
closures of the prime divisors. -/
private theorem ord_pullbackRationalFunction_of_isOpenImmersion {X Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (j : X ⟶ Y) [IsOpenImmersion j]
    [IsDominant j] (g : (RationalFunctions Y)ˣ)
    (hg : ∀ Z : irreducibleComponents X, j (componentGenericPoint X Z) ∉
      (principalDivisor g).supp) (P : MMP.Mori.PrimeDivisor X) :
    P.ord (pullbackRationalFunction j g hg) =
      MMP.Mori.PrimeDivisor.ord (OpenWeilRestriction.primeDivisorMap j P) g := by
  have h := MMP.Positivity.coeff_eq_of_isPullback (f := j) P
    (OpenWeilRestriction.primeDivisorMap j P)
    (OpenWeilRestriction.genericPoint_primeDivisorMap j P).symm
    (Divisor.isCartier_principalDivisor g) (Divisor.isPullback_principalDivisor g hg)
  simpa using h

/-- The pull-back of a nonzero rational pluricanonical form along a morphism inducing a bijection
of function fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra sX
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := (pullbackForms_eq hω m τ).symm.trans h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- **Extension of a canonical divisor** along an open immersion into a normal surface: a
canonical divisor of the open subscheme is the restriction of a canonical divisor of the
surface. -/
private theorem exists_isCanonicalDivisor_extension {S Sb : Scheme.{0}} [IsIntegral S]
    [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S] [IsIntegral Sb] [CompactSpace Sb]
    [IsLocallyNoetherian Sb] [IsNormal Sb] {sSb : Sb ⟶ Spec (.of ℂ)}
    (hSb : IsNormalVariety ℂ sSb) (hSbd : topologicalKrullDim Sb = (2 : ℕ))
    (j : S ⟶ Sb) [IsOpenImmersion j] (hS : IsNormalVariety ℂ (j ≫ sSb)) {K : Divisor S}
    (hK : K.IsCanonicalDivisor (j ≫ sSb) 2) :
    ∃ Kb : Divisor Sb, Kb.IsCanonicalDivisor sSb 2 ∧
      ∀ P, Kb.coeff (OpenWeilRestriction.primeDivisorMap j P) = K.coeff P := by
  haveI : LocallyOfFiniteType sSb := hSb.1.toLocallyOfFiniteType
  have hjb : IsBirationalMorphism j := isBirationalMorphism_of_isOpenImmersion j
  haveI : IsDominant j := hjb.isDominant
  let := functionFieldAlgebra sSb
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hSb hSbd
  set σ : RationalTopForms sSb 2 := b ()
  have hσ : σ ≠ 0 := b.ne_zero ()
  have hK0 := MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hSb hSbd hσ
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sSb) hSbd
  have hσ' : σ.toPluriForms sSb ≠ 0 := by
    intro h
    apply hσ
    have h' : (PiTensorProduct.tprod Sb.functionField
        fun _ : Fin 1 => (σ : ⋀[Sb.functionField]^2 Ω[Sb.functionField⁄ℂ])) = 0 := h
    have h'' := congrArg (PiTensorProduct.subsingletonEquiv (0 : Fin 1)) h'
    rwa [PiTensorProduct.subsingletonEquiv_apply_tprod, map_zero] at h''
  have hω' := pullbackRationalPluriForms_ne_zero j hjb.functionFieldMap_bijective hd hσ'
  obtain ⟨g, hg⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hS hK hω'
  obtain ⟨g', hg', rfl⟩ := exists_pullbackRationalFunction_eq hjb g
  refine ⟨divisorOfForm (σ.toPluriForms sSb) - principalDivisor g', ?_, fun P => ?_⟩
  · refine hK0.of_linearlyEquivalent ⟨g'⁻¹, ?_⟩
    ext P
    simp [topFormDivisor]
  · have h1 := congrArg (fun D : Divisor S => D.coeff P) hg
    simp only [DivisorWithCoeffs.coeff_sub, one_smul, coeff_principalDivisor] at h1
    rw [ord_pullbackRationalFunction_of_isOpenImmersion] at h1
    have h2 := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso j
      hjb.functionFieldMap_bijective hd P (OpenWeilRestriction.primeDivisorMap j P)
      (OpenWeilRestriction.genericPoint_primeDivisorMap j P).symm (σ.toPluriForms sSb)
    rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor]
    change PrimeDivisor.ordForm _ _ - _ = _
    change PrimeDivisor.ordForm _ _ - _ = _ at h1
    rw [h2] at h1
    omega

end OpenImmersions

/-! ### Push-forwards, stable base loci and rational polytopes -/

section Transfers

section Transform

variable {X Y : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {φ : X ⟶ Y} [IsProper φ]

/-- The push-forward of a divisor along a proper birational morphism commutes with regarding it as
an `ℝ`-divisor. -/
private theorem transformDivisor_toRDivisor (hY : IsNormalVariety ℂ sY)
    (hX : IsNormalVariety ℂ (φ ≫ sY)) (hφ : IsBirationalMorphism φ) (D : Divisor X) :
    RationalMap.transformDivisor φ.toRationalMap (Divisor.toRDivisor D) =
      Divisor.toRDivisor (RationalMap.transformDivisor φ.toRationalMap D) := by
  ext Q
  obtain ⟨E, -, -, hE⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX
    hφ Q
  rw [DivisorWithCoeffs.coeff_apply, hE, Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply,
    hE]
  rfl

/-- **The push-forward of a pull-back.** For a proper birational morphism `φ` of normal varieties,
`φ_*(φ^*L) = L` for every `ℝ`-Cartier divisor `L`. -/
private theorem transformDivisor_eq_of_isRCartierPullback (hY : IsNormalVariety ℂ sY)
    (hX : IsNormalVariety ℂ (φ ≫ sY)) (hφ : IsBirationalMorphism φ) {L : RDivisor Y}
    {G : RDivisor X} (h : MMP.Flips.IsRCartierPullback φ L G) :
    RationalMap.transformDivisor φ.toRationalMap G = L := by
  ext Q
  obtain ⟨E, hEQ, hiso, hE⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX hφ Q
  rw [DivisorWithCoeffs.coeff_apply, hE]
  exact coeff_eq_of_isRCartierPullback E Q hEQ h

end Transform

section Identity

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- The push-forward along the identity is the identity. -/
private theorem transformDivisor_toRationalMap_id (hX : IsNormalVariety ℂ sX) {R : Type*}
    [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor (Scheme.Hom.toRationalMap (𝟙 X)) D = D := by
  ext Q
  have hX' : IsNormalVariety ℂ (𝟙 X ≫ sX) := by rwa [Category.id_comp]
  obtain ⟨E, hEQ, -, hE⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX hX'
      (isBirationalMorphism_of_isIso (𝟙 X)) Q
  rw [DivisorWithCoeffs.coeff_apply, hE]
  obtain rfl : E = Q := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hEQ
  rfl

/-- Every `ℝ`-Cartier divisor is its own pull-back along the identity. -/
private theorem isRCartierPullback_id_of_isCartierCombination {L : RDivisor X}
    (hL : MMP.Flips.IsCartierCombination L) :
    MMP.Flips.IsRCartierPullback (𝟙 X) L L := by
  obtain ⟨G, hG, -⟩ := MMP.Flips.existsUnique_isRCartierPullback (𝟙 X) hL
  convert hG using 1
  ext Q
  exact (coeff_eq_of_isRCartierPullback Q Q rfl hG).symm

end Identity

/-- Extension by zero along an open immersion preserves effectivity. -/
private theorem coeff_mapDomain_primeDivisorMap_nonneg {S Sb : Scheme.{0}} (j : S ⟶ Sb)
    [IsOpenImmersion j] {Θ : RDivisor S} (hΘ : ∀ P, 0 ≤ Θ.coeff P)
    (P : MMP.Mori.PrimeDivisor Sb) :
    0 ≤ DivisorWithCoeffs.coeff
      (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j) Θ) P := by
  rw [DivisorWithCoeffs.coeff_apply]
  by_cases hP : P ∈ Set.range (OpenWeilRestriction.primeDivisorMap j)
  · obtain ⟨W, rfl⟩ := hP
    rw [Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective j)]
    exact hΘ W
  · rw [Finsupp.mapDomain_notin_range _ _ hP]

/-- Extension by zero along an open immersion commutes with regarding a `ℚ`-divisor as an
`ℝ`-divisor. -/
private theorem toRDivisor_mapDomain_primeDivisorMap {S Sb : Scheme.{0}} (j : S ⟶ Sb)
    [IsOpenImmersion j] (Θq : QDivisor S) :
    QDivisor.toRDivisor (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j) Θq) =
      Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j) (QDivisor.toRDivisor Θq) := by
  have hinj := OpenWeilRestriction.primeDivisorMap_injective j
  ext P
  rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply]
  by_cases hP : P ∈ Set.range (OpenWeilRestriction.primeDivisorMap j)
  · obtain ⟨W, rfl⟩ := hP
    rw [Finsupp.mapDomain_apply_of_injective hinj, Finsupp.mapDomain_apply_of_injective hinj]
    rfl
  · rw [Finsupp.mapDomain_notin_range _ _ hP, Finsupp.mapDomain_notin_range _ _ hP]
    simp

/-- Coordinates on the support of `Θ`: a real divisor `Θ'` supported on `supp Θ` extends to the
compactification as `∑ᵢ Θ'(Pᵢ) P̄ᵢ`. -/
private theorem exists_coordinates {S Sb : Scheme.{0}} (j : S ⟶ Sb) [IsOpenImmersion j]
    (Θ : RDivisor S) :
    ∃ (s : ℕ) (P : Fin s → MMP.Mori.PrimeDivisor S), Function.Injective P ∧
      ∀ Θ' : RDivisor S, Θ'.support ⊆ Θ.support →
        ∑ i, Θ'.coeff (P i) • Finsupp.single (OpenWeilRestriction.primeDivisorMap j (P i)) (1 : ℝ) =
          Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j) Θ' := by
  classical
  have hinj := OpenWeilRestriction.primeDivisorMap_injective j
  set e := Θ.support.equivFin
  set P : Fin Θ.support.card → MMP.Mori.PrimeDivisor S := fun i => (e.symm i).1 with hPdef
  refine ⟨Θ.support.card, P, fun i i' h => e.symm.injective (Subtype.ext h), fun Θ' hsub => ?_⟩
  ext Q
  have hl : DivisorWithCoeffs.coeff (∑ i, Θ'.coeff (P i) •
      Finsupp.single (OpenWeilRestriction.primeDivisorMap j (P i)) (1 : ℝ)) Q =
      ∑ i, if OpenWeilRestriction.primeDivisorMap j (P i) = Q then Θ'.coeff (P i) else 0 := by
    simp [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [hl]
  by_cases hQ : Q ∈ Set.range (OpenWeilRestriction.primeDivisorMap j)
  · obtain ⟨W, rfl⟩ := hQ
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.mapDomain_apply_of_injective hinj]
    simp_rw [hinj.eq_iff]
    by_cases hW : W ∈ Θ.support
    · have hiff : ∀ i, P i = W ↔ i = e ⟨W, hW⟩ := fun i => by
        rw [← Equiv.symm_apply_eq]
        exact ⟨fun h => Subtype.ext h, fun h => by
          rw [hPdef]
          exact congrArg Subtype.val h⟩
      simp_rw [hiff]
      rw [Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _)]
      simp [hPdef]
      rfl
    · rw [Finset.sum_eq_zero fun i _ =>
        if_neg (fun h : P i = W => hW (by rw [← h]; exact (e.symm i).2))]
      exact (Finsupp.notMem_support_iff.mp fun h => hW (hsub h)).symm
  · rw [Finset.sum_eq_zero fun i _ => if_neg (fun h => hQ ⟨_, h⟩),
      DivisorWithCoeffs.coeff_apply, Finsupp.mapDomain_notin_range _ _ hQ]

/-- The coefficients of `D + ∑ aⱼ div gⱼ`. -/
private theorem coeff_add_sum_smul_principalDivisor {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (D : RDivisor X) {s : ℕ} (a : Fin s → ℝ)
    (g : Fin s → (RationalFunctions X)ˣ)
    (P : MMP.Mori.PrimeDivisor X) :
    (D + ∑ i, a i • Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero
      (MMP.Mori.principalDivisor (g i))).coeff P = D.coeff P + ∑ i, a i * (P.ord (g i) : ℝ) := by
  simp [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
  rfl

/-- **Stable base loci under an open base change.** If `S = S̄ ×_{T̄} T` for an open immersion
`T ⟶ T̄` and `D̄` restricts to `D`, a prime divisor of `S` lies in the relative divisorial stable
base locus of `D` over `T` exactly when its closure lies in that of `D̄` over `T̄`. -/
private theorem isInRelativeDivisorialStableBase_iff_of_isPullback
    {S Sb T Tb : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    [IsIntegral Sb] [CompactSpace Sb] [IsLocallyNoetherian Sb] [IsNormal Sb]
    {j : S ⟶ Sb} [IsOpenImmersion j] {f : S ⟶ T} {fb : Sb ⟶ Tb} {ι : T ⟶ Tb}
    [IsOpenImmersion ι] (hpb : IsPullback j f fb ι) {D : RDivisor S} {Db : RDivisor Sb}
    (hD : ∀ P, Db.coeff (OpenWeilRestriction.primeDivisorMap j P) = D.coeff P)
    (G : MMP.Mori.PrimeDivisor S) :
    IsInRelativeDivisorialStableBase f D G ↔
      IsInRelativeDivisorialStableBase fb Db (OpenWeilRestriction.primeDivisorMap j G) := by
  classical
  have hjb : IsBirationalMorphism j := isBirationalMorphism_of_isOpenImmersion j
  haveI : IsDominant j := hjb.isDominant
  have hw : ∀ x, fb (j x) = ι (f x) := fun x => by
    rw [← Scheme.Hom.comp_apply, hpb.w, Scheme.Hom.comp_apply]
  have hgen : fb (OpenWeilRestriction.primeDivisorMap j G).genericPoint =
      ι (f G.genericPoint) := by
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
    exact hw _
  set pb : (RationalFunctions Sb)ˣ → (RationalFunctions S)ˣ := fun g =>
    pullbackRationalFunction j g (map_componentGenericPoint_notMem_supp_of_isDominant j _)
    with hpbdef
  have hcoeff : ∀ {s : ℕ} (a : Fin s → ℝ) (g : Fin s → (RationalFunctions Sb)ˣ)
      (P : MMP.Mori.PrimeDivisor S),
      (Db + ∑ i, a i • Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero
        (MMP.Mori.principalDivisor (g i))).coeff (OpenWeilRestriction.primeDivisorMap j P) =
      (D + ∑ i, a i • Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero
        (MMP.Mori.principalDivisor (pb (g i)))).coeff P := by
    intro s a g P
    rw [coeff_add_sum_smul_principalDivisor, coeff_add_sum_smul_principalDivisor, hD]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpbdef, ord_pullbackRationalFunction_of_isOpenImmersion]
  constructor
  · intro h U' hU' s a g hL
    rw [hcoeff]
    refine h (ι ⁻¹ᵁ U') (by
      change ι (f G.genericPoint) ∈ U'
      rw [← hgen]
      exact hU') s a (fun i => pb (g i)) fun P ⟨x, hxP, hxU⟩ => ?_
    rw [← hcoeff]
    refine hL _ ⟨j x, ?_, ?_⟩
    · exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff j P x).mpr hxP
    · change fb (j x) ∈ U'
      rw [hw]
      exact hxU
  · intro h U hU s a g hL
    choose g' hg' hg'eq using fun i => exists_pullbackRationalFunction_eq hjb (g i)
    have hpbg : ∀ i, pb (g' i) = g i := hg'eq
    have key := h (ι ''ᵁ U) (by rw [hgen]; exact ⟨_, hU, rfl⟩) s a g' ?_
    · rw [hcoeff] at key
      simpa only [hpbg] using key
    · intro Q ⟨y, hyQ, hyU⟩
      obtain ⟨t, ht, hty⟩ : fb y ∈ ι ''ᵁ U := hyU
      obtain ⟨x, rfl⟩ := mem_range_of_isPullback hpb ⟨t, hty⟩
      obtain ⟨P, rfl⟩ :=
        MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support j Q x hyQ
      rw [hcoeff]
      simp only [hpbg]
      refine hL P ⟨x, ?_, ?_⟩
      · exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff j P x).mp hyQ
      · change f x ∈ U
        rw [hw] at hty
        rwa [ι.isOpenEmbedding.injective hty] at ht

/-- A real vector satisfying every rational linear relation of a finite family of rational vectors
lies in their real span. -/
private theorem mem_span_of_forall_rat {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (a : κ → ι → ℚ) (x : ι → ℝ)
    (hx : ∀ c : ι → ℚ, (∀ k, ∑ i, c i * a k i = 0) → ∑ i, (c i : ℝ) * x i = 0) :
    x ∈ Submodule.span ℝ (Set.range fun k i => (a k i : ℝ)) := by
  classical
  have h := MMP.Fourfold.mem_span_rational_solutions {c | ∀ k, ∑ i, c i * a k i = 0} x
    hx
  refine Submodule.span_le.mpr ?_ h
  rintro _ ⟨y, hy, rfl⟩
  have hyW : y ∈ Submodule.span ℚ (Set.range a) := by
    by_contra hnot
    obtain ⟨g, hg, hgW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    let c : ι → ℚ := fun i => g (Pi.single i 1)
    have hgx : ∀ z : ι → ℚ, g z = ∑ i, c i * z i := fun z => by
      rw [LinearMap.pi_apply_eq_sum_univ g z]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [c, smul_eq_mul]
      rw [mul_comm]
      congr 2
      ext j
      simp [Pi.single_apply, eq_comm]
    have hc : ∀ k, ∑ i, c i * a k i = 0 := fun k => by
      rw [← hgx]
      have : g (a k) ∈ (Submodule.span ℚ (Set.range a)).map g :=
        ⟨a k, Submodule.subset_span ⟨k, rfl⟩, rfl⟩
      rw [hgW] at this
      exact (Submodule.mem_bot ℚ).mp this
    exact hg (by rw [hgx]; exact hy c hc)
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hyW
  rw [← hβ]
  have : (fun i => ((∑ k, β k • a k) i : ℝ)) = ∑ k, (β k : ℝ) • fun i => (a k i : ℝ) := by
    ext i
    simp [Finset.sum_apply]
  show (fun i => ((∑ k, β k • a k) i : ℝ)) ∈ _
  rw [this]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- A linear map from a finite-dimensional space has a bounded right inverse on its range. -/
private theorem exists_bound_preimage {κ E : Type*} [Fintype κ] [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : (κ → ℝ) →ₗ[ℝ] E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ LinearMap.range A, ∃ μ, A μ = w ∧ ‖μ‖ ≤ C * ‖w‖ := by
  obtain ⟨g, hg⟩ := A.rangeRestrict.exists_rightInverse_of_surjective A.range_rangeRestrict
  let gc := LinearMap.toContinuousLinearMap g
  refine ⟨‖gc‖, norm_nonneg _, fun w hw => ⟨g ⟨w, hw⟩, ?_, ?_⟩⟩
  · simpa using congrArg Subtype.val (LinearMap.congr_fun hg ⟨w, hw⟩)
  · exact gc.le_opNorm ⟨w, hw⟩

/-- A point `Δ` of the convex hull of a finite set from which every vertex can be pushed back
beyond `Δ` is a combination of all the vertices with positive weights. -/
private theorem exists_pos_weights {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]
    (V : Finset E) {Δ : E} (hΔ : Δ ∈ convexHull ℝ (V : Set E))
    (hext : ∀ v ∈ V, ∃ ε : ℝ, 0 < ε ∧ Δ + ε • (Δ - v) ∈ convexHull ℝ (V : Set E)) :
    ∃ w : E → ℝ, (∀ v ∈ V, 0 < w v) ∧ ∑ v ∈ V, w v = 1 ∧ ∑ v ∈ V, w v • v = Δ := by
  classical
  have hne : V.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hΔ
  choose! ε hε hz using hext
  have hz' : ∀ v ∈ V, ∃ ν : E → ℝ, (∀ u ∈ V, 0 ≤ ν u) ∧ ∑ u ∈ V, ν u = 1 ∧
      ∑ u ∈ V, ν u • u = Δ + ε v • (Δ - v) := fun v hv => by
    obtain ⟨ν, hν0, hν1, hνc⟩ := (Finset.mem_convexHull).mp (hz v hv)
    refine ⟨ν, hν0, hν1, ?_⟩
    rw [← hνc, Finset.centerMass_eq_of_sum_1 _ _ hν1]
    rfl
  choose! ν hν0 hν1 hνc using hz'
  set N : ℝ := (V.card : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr hne.card_pos
  let a : E → ℝ := fun v => 1 / (1 + ε v)
  have ha0 : ∀ v ∈ V, 0 < a v := fun v hv => by have := hε v hv; positivity
  have ha1 : ∀ v ∈ V, a v < 1 := fun v hv => by
    have := hε v hv
    simp only [a]; rw [div_lt_one (by linarith)]; linarith
  set c : E → E → ℝ := fun v u => a v * ν v u + (1 - a v) * if u = v then 1 else 0 with hc
  refine ⟨fun u => (1 / N) * ∑ v ∈ V, c v u, fun u hu => ?_, ?_, ?_⟩
  · refine mul_pos (by positivity) ?_
    have hnn : ∀ v ∈ V, 0 ≤ c v u := fun v hv => by
      have := mul_nonneg (ha0 v hv).le (hν0 v hv u hu)
      have h1 : 0 ≤ 1 - a v := by linarith [ha1 v hv]
      simp only [hc]
      split_ifs <;> nlinarith
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun v => c v u) hnn hu)
    simp only [hc, if_pos rfl, if_true, mul_one]
    have := ha1 u hu
    have := mul_nonneg (ha0 u hu).le (hν0 u hu u hu)
    linarith
  · rw [← Finset.mul_sum, Finset.sum_comm]
    have : ∀ v ∈ V, ∑ u ∈ V, c v u = 1 := fun v hv => by
      simp only [hc]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hν1 v hv, ← Finset.mul_sum,
        Finset.sum_ite_eq' V v, if_pos hv]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact one_div_mul_cancel hN.ne'
  · have key : ∀ v ∈ V, ∑ u ∈ V, c v u • u = Δ := fun v hv => by
      simp only [hc, add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hνc v hv,
        ite_smul, one_smul, zero_smul, smul_ite, smul_zero, Finset.sum_ite_eq' V v, if_pos hv]
      have h2 : (1 + ε v) * a v = 1 := by
        simp only [a]
        rw [mul_one_div, div_self]
        linarith [hε v hv]
      have h3 : a v • (Δ + ε v • (Δ - v)) + (1 - a v) • v = ((1 + ε v) * a v) • Δ +
          (1 - (1 + ε v) * a v) • v := by
        module
      rw [h3, h2]
      simp
    calc ∑ u ∈ V, ((1 / N) * ∑ v ∈ V, c v u) • u
        = (1 / N) • ∑ v ∈ V, ∑ u ∈ V, c v u • u := by
          rw [Finset.sum_comm, Finset.smul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [mul_smul, Finset.sum_smul]
      _ = (1 / N) • ∑ v ∈ V, Δ := by rw [Finset.sum_congr rfl key]
      _ = Δ := by
          rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
          rw [show 1 / N * (V.card : ℝ) = 1 from one_div_mul_cancel hN.ne', one_smul]

/-- **Rational polytope neighbourhoods.** Let `Δ` lie in the convex hull `C` of finitely many
`ℚ`-divisors, and suppose every point of `C` can be pushed back beyond `Δ` inside `C`. Then every
real divisor in the smallest rational affine hull of `Δ`, close enough to `Δ` coefficientwise, lies
in `C`. -/
private theorem exists_forall_mem_convexHull {X : Scheme.{0}} (VQ : Finset (QDivisor X))
    {Δ : RDivisor X}
    (hΔ : Δ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor X))))
    (hext : ∀ Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor X))), ∃ ε : ℝ, 0 < ε ∧
      Δ + ε • (Δ - Γ) ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor X)))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Ψ : RDivisor X, IsInSmallestRationalAffineHull Δ Ψ →
      (∀ P, |Ψ.coeff P - Δ.coeff P| < ε) →
      Ψ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor X))) := by
  classical
  have hC : QDivisor.toRDivisor '' (VQ : Set (QDivisor X)) = ↑(VQ.image QDivisor.toRDivisor) :=
    (Finset.coe_image).symm
  rw [hC] at hΔ hext ⊢
  obtain ⟨w, hw0, hw1, hwΔ⟩ := exists_pos_weights (VQ.image QDivisor.toRDivisor) hΔ
    fun v hv => hext v (subset_convexHull ℝ _ hv)
  let κ := {q // q ∈ VQ}
  let F : Finset (MMP.Mori.PrimeDivisor X) := VQ.biUnion fun q => q.support
  let lam : κ → ℝ := fun q => w (QDivisor.toRDivisor q.1)
  have hlam0 : ∀ q, 0 < lam q := fun q => hw0 _ (Finset.mem_image_of_mem _ q.2)
  have himg : ∀ {N : Type} [AddCommMonoid N] (g : RDivisor X → N),
      ∑ v ∈ VQ.image QDivisor.toRDivisor, g v = ∑ q : κ, g (QDivisor.toRDivisor q.1) := by
    intro N _ g
    rw [Finset.sum_image fun x _ y _ h => MMP.Mori.QDivisor.toRDivisor_injective h]
    exact (Finset.sum_coe_sort VQ fun q => g (QDivisor.toRDivisor q)).symm
  have hlam1 : ∑ q, lam q = 1 := by rw [← hw1, himg]
  have hlamΔ : ∑ q, lam q • QDivisor.toRDivisor q.1 = Δ := by rw [← hwΔ, himg]
  have hΔP : ∀ P, Δ.coeff P = ∑ q, lam q * (q.1.coeff P : ℝ) := fun P => by
    rw [← hlamΔ]
    simp [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, QDivisor.toRDivisor]
    rfl
  have hqF : ∀ (q : κ) (P), P ∉ F → q.1.coeff P = 0 := fun q P hP => by
    by_contra h
    exact hP (Finset.mem_biUnion.mpr ⟨q.1, q.2, Finsupp.mem_support_iff.mpr h⟩)
  have hΔF : ∀ P, P ∉ F → Δ.coeff P = 0 := fun P hP => by
    rw [hΔP]; simp [hqF _ P hP]
  let a : κ → Option F → ℚ := fun q o => o.elim 1 fun P => q.1.coeff P.1
  let A : (κ → ℝ) →ₗ[ℝ] (Option F → ℝ) := Fintype.linearCombination ℝ fun q o => (a q o : ℝ)
  have hA : ∀ μ o, A μ o = ∑ q, μ q * (a q o : ℝ) := fun μ o => by
    simp [A, Fintype.linearCombination_apply, Finset.sum_apply]
  obtain ⟨C₀, hC₀, hC₀A⟩ := exists_bound_preimage A
  haveI : Nonempty κ := by
    obtain ⟨v, hv⟩ : (VQ.image QDivisor.toRDivisor).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      simp [h] at hΔ
    obtain ⟨q, hq, -⟩ := Finset.mem_image.mp hv
    exact ⟨⟨q, hq⟩⟩
  obtain ⟨q₀, -, hq₀⟩ := Finset.exists_min_image Finset.univ lam Finset.univ_nonempty
  set m := lam q₀
  have hm : 0 < m := hlam0 q₀
  have hε : 0 < m / (C₀ + 1) := by positivity
  refine ⟨m / (C₀ + 1), hε, fun Ψ hΨ hclose => ?_⟩
  have hΨF : ∀ P, P ∉ F → Ψ.coeff P = 0 := fun P hP => by
    by_contra h
    have := hΨ.1 (Finsupp.mem_support_iff.mpr h)
    exact Finsupp.mem_support_iff.mp this (hΔF P hP)
  let wv : Option F → ℝ := fun o => o.elim 0 fun P => Ψ.coeff P.1 - Δ.coeff P.1
  have hwv : wv ∈ LinearMap.range A := by
    have hspan := mem_span_of_forall_rat a wv fun c hc => by
      have hrel : ∑ P : F, (c (some P) : ℝ) * Δ.coeff P.1 = -(c none : ℝ) := by
        have h0 : ∑ q, lam q * ∑ o, (c o : ℝ) * (a q o : ℝ) = 0 := by
          refine Finset.sum_eq_zero fun q _ => ?_
          rw [show ∑ o, (c o : ℝ) * (a q o : ℝ) = 0 by exact_mod_cast hc q, mul_zero]
        simp only [a, Fintype.sum_option, Option.elim, Rat.cast_one, mul_one, mul_add,
          Finset.sum_add_distrib, ← Finset.sum_mul, hlam1, one_mul] at h0
        have h1 : ∑ P : F, (c (some P) : ℝ) * Δ.coeff P.1 =
            ∑ x : κ, lam x * ∑ P : F, (c (some P) : ℝ) * (x.1.coeff P.1 : ℝ) := by
          simp_rw [hΔP, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        linarith
      let cP : MMP.Mori.PrimeDivisor X →₀ ℚ :=
        Finsupp.onFinset F (fun P => if h : P ∈ F then c (some ⟨P, h⟩) else 0) (by
          intro P hP; by_contra h; exact hP (dif_neg h))
      have hsum : ∀ D : RDivisor X,
          (cP.sum fun P cP => (cP : ℝ) * D.coeff P) =
            ∑ P : F, (c (some P) : ℝ) * D.coeff P.1 := fun D => by
        rw [Finsupp.sum_of_support_subset cP (Finsupp.support_onFinset_subset) _
          (fun _ _ => by simp), ← Finset.sum_coe_sort F]
        refine Finset.sum_congr rfl fun P _ => ?_
        simp [cP, Finsupp.onFinset_apply, dif_pos P.2]
      have hΨrel := hΨ.2 cP (-(c none)) (by rw [hsum, hrel]; push_cast; ring)
      rw [hsum] at hΨrel
      simp only [wv, Fintype.sum_option, Option.elim, mul_zero, zero_add, mul_sub,
        Finset.sum_sub_distrib, hrel]
      push_cast at hΨrel
      linarith
    obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
    exact ⟨μ, by rw [← hμ]; simp [A, Fintype.linearCombination_apply]⟩
  obtain ⟨μ', hμ'A, hμ'n⟩ := hC₀A wv hwv
  have hwvn : ‖wv‖ < m / (C₀ + 1) := by
    rw [pi_norm_lt_iff hε]
    rintro (_ | P)
    · simpa [wv] using hε
    · simpa [wv, Real.norm_eq_abs] using hclose P.1
  have hμ'small : ∀ q, |μ' q| < m := fun q => by
    have h1 : ‖μ' q‖ ≤ ‖μ'‖ := norm_le_pi_norm μ' q
    have h2 : C₀ * ‖wv‖ ≤ C₀ * (m / (C₀ + 1)) := mul_le_mul_of_nonneg_left hwvn.le hC₀
    have h3 : C₀ * (m / (C₀ + 1)) < m := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
    rw [← Real.norm_eq_abs]; linarith
  let μ : κ → ℝ := fun q => lam q + μ' q
  have hμ0 : ∀ q, 0 ≤ μ q := fun q => by
    have := hq₀ q (Finset.mem_univ _)
    have := (abs_lt.mp (hμ'small q)).1
    simp only [μ]; linarith
  have hAμ' : ∀ o, ∑ q, μ' q * (a q o : ℝ) = wv o := fun o => by
    rw [← hA, hμ'A]
  have hμ1 : ∑ q, μ q = 1 := by
    have := hAμ' none
    simp only [a, Option.elim, Rat.cast_one, mul_one, wv] at this
    simp only [μ, Finset.sum_add_distrib, hlam1, this, add_zero]
  have hμΨ : Ψ = ∑ q, μ q • QDivisor.toRDivisor q.1 := by
    ext P
    have hcoe : (∑ q, μ q • QDivisor.toRDivisor q.1).coeff P = ∑ q, μ q * (q.1.coeff P : ℝ) := by
      simp [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, QDivisor.toRDivisor]
      rfl
    rw [hcoe]
    by_cases hP : P ∈ F
    · have := hAμ' (some ⟨P, hP⟩)
      simp only [a, Option.elim, wv] at this
      simp only [μ, add_mul, Finset.sum_add_distrib, ← hΔP, this]
      ring
    · rw [hΨF P hP]
      simp [hqF _ P hP]
  rw [hμΨ]
  exact (convex_convexHull ℝ _).sum_mem (fun q _ => hμ0 q) hμ1 fun q _ =>
    subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ q.2))

end Transfers

/-! ### The compactified model -/

/-- The data produced by the compactification and the surface program for a pair `(S, Θ)`
projective and birational over the affine `T`: an open immersion `ι : T ⟶ T̄` into a normal
projective surface, a projective `ℚ`-factorial compactification `j : S ⟶ S̄` over it with
`S = S̄ ×_{T̄} T`, a canonical divisor `K̄` of `S̄` restricting to `K`, and the nef klt model
`φ : S̄ ⟶ Y` over `T̄` with the comparison `K̄ + Θ̄ = G + E`, `G = φ^*(K_Y + Θ_Y)`, `E ≥ 0`. -/
private structure SurfaceModel {S T : Scheme.{0}} (sS : S ⟶ Spec (.of ℂ))
    (sT : T ⟶ Spec (.of ℂ)) (f : S ⟶ T) (K : Divisor S) (Θ : RDivisor S) where
  /-- The compactified base. -/
  Tb : Scheme.{0}
  /-- Its structure morphism. -/
  sTb : Tb ⟶ Spec (.of ℂ)
  /-- The open immersion of the base. -/
  ι : T ⟶ Tb
  [isOpenImmersion_ι : IsOpenImmersion ι]
  hTb : IsNormalVariety ℂ sTb
  hTbp : MMP.Mori.IsProjectiveVariety ℂ sTb
  /-- The compactified source. -/
  Sb : Scheme.{0}
  [isIntegral_Sb : IsIntegral Sb]
  [compactSpace_Sb : CompactSpace Sb]
  [isLocallyNoetherian_Sb : IsLocallyNoetherian Sb]
  [isNormal_Sb : IsNormal Sb]
  /-- Its structure morphism. -/
  sSb : Sb ⟶ Spec (.of ℂ)
  /-- The compactified morphism. -/
  fb : Sb ⟶ Tb
  /-- The open immersion of the source. -/
  j : S ⟶ Sb
  [isOpenImmersion_j : IsOpenImmersion j]
  hSb : IsNormalVariety ℂ sSb
  hSbQ : IsQFactorial sSb
  hSbd : topologicalKrullDim Sb = (2 : ℕ)
  hfbs : fb ≫ sTb = sSb
  hfbb : IsBirationalMorphism fb
  hpb : IsPullback j f fb ι
  /-- The extended canonical divisor. -/
  Kb : Divisor Sb
  hKb : Kb.IsCanonicalDivisor sSb 2
  hKbj : ∀ P, Kb.coeff (OpenWeilRestriction.primeDivisorMap j P) = K.coeff P
  /-- The extended boundary. -/
  Θb : RDivisor Sb
  hΘb : Θb = Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j) Θ
  hhull : ∀ Ψ : RDivisor Sb, IsInSmallestRationalAffineHull Θb Ψ ↔
    ∃ Φ : RDivisor S, IsInSmallestRationalAffineHull Θ Φ ∧
      Ψ = Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j) Φ
  /-- The nef model. -/
  Y : Scheme.{0}
  [isIntegral_Y : IsIntegral Y]
  [compactSpace_Y : CompactSpace Y]
  [isLocallyNoetherian_Y : IsLocallyNoetherian Y]
  [isNormal_Y : IsNormal Y]
  /-- Its structure morphism. -/
  sY : Y ⟶ Spec (.of ℂ)
  /-- Its morphism to the base. -/
  πY : Y ⟶ Tb
  /-- The contraction to the model. -/
  φ : Sb ⟶ Y
  [isProper_φ : IsProper φ]
  hY : IsNormalVariety ℂ sY
  hYQ : IsQFactorial sY
  hYp : MMP.Mori.IsProjectiveVariety ℂ sY
  hπs : πY ≫ sTb = sY
  hφπ : φ ≫ πY = fb
  hφb : IsBirationalMorphism φ
  /-- The pushed-forward canonical divisor. -/
  KY : Divisor Y
  hKY : KY.IsCanonicalDivisor sY 2
  hKYφ : KY = RationalMap.transformDivisor φ.toRationalMap Kb
  /-- The pushed-forward boundary. -/
  ΘY : RDivisor Y
  hΘY : ΘY = RationalMap.transformDivisor φ.toRationalMap Θb
  hΘYk : IsRealKltPair sY ΘY
  hnef : MMP.Flips.IsRelativelyNef ℂ sY πY (Divisor.toRDivisor KY + ΘY)
  /-- The pull-back of the target adjoint. -/
  G : RDivisor Sb
  hG : MMP.Flips.IsRCartierPullback φ (Divisor.toRDivisor KY + ΘY) G
  hE : ∀ P, 0 ≤ (Divisor.toRDivisor Kb + Θb - G).coeff P
  hEexc : ∀ P, (Divisor.toRDivisor Kb + Θb - G).coeff P ≠ 0 →
    MMP.Flips.IsExceptionalPrimeDivisor sY φ P
  hrat : (∃ Θq : QDivisor S, QDivisor.toRDivisor Θq = Θ) →
    (∃ Bq : QDivisor Y, QDivisor.toRDivisor Bq = ΘY) ∧
      ∃ Eq : QDivisor Sb, QDivisor.toRDivisor Eq = Divisor.toRDivisor Kb + Θb - G

attribute [local instance] SurfaceModel.isOpenImmersion_ι SurfaceModel.isIntegral_Sb
  SurfaceModel.compactSpace_Sb SurfaceModel.isLocallyNoetherian_Sb SurfaceModel.isNormal_Sb
  SurfaceModel.isOpenImmersion_j SurfaceModel.isIntegral_Y SurfaceModel.compactSpace_Y
  SurfaceModel.isLocallyNoetherian_Y SurfaceModel.isNormal_Y SurfaceModel.isProper_φ

section Setup

variable {S : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
  {sS : S ⟶ Spec (.of ℂ)} {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)} {f : S ⟶ T}

/-- **The compactified model exists**: compactify by the rational birational program property
in dimension two, extend the canonical divisor, and run the surface program over the
compactified base. -/
private theorem nonempty_surfaceModel (hSQ : IsQFactorial sS)
    (hSd : topologicalKrullDim S = (2 : ℕ)) (hT : IsNormalVariety ℂ sT) [IsAffine T]
    (hfs : f ≫ sT = sS) (hfp : IsProjectiveMorphism f) (hfb : IsBirationalMorphism f)
    {Θ : RDivisor S} (hΘ : ∀ P, 0 ≤ Θ.coeff P) (hΘk : IsRealKltPair sS Θ) {K : Divisor S}
    (hK : K.IsCanonicalDivisor sS 2) : Nonempty (SurfaceModel sS sT f K Θ) := by
  have hSn : IsNormalVariety ℂ sS := hSQ.1
  obtain ⟨Tb, sTb, ι, hTbp, hTbn, hι, hιs, Sb, _, _, _, sSb, fb, j, hj, hSbp, hSbQ, hfbp, hfbs,
    hpb, hΘbk, hhull⟩ := exists_realKltCompactification_of_rationalBirationalProgramProperty
      le_rfl rationalBirationalProgramProperty_two sT hT sS hSQ hSd f hfs hfp Θ hΘ hΘk
  haveI : CompactSpace Sb := by
    haveI := hSbp.toIsVariety
    exact QuasiCompact.compactSpace_of_compactSpace sSb
  haveI : IsIntegral Tb := hTbn.1.toIsIntegral
  haveI : LocallyOfFiniteType sSb := hSbQ.1.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sTb := hTbn.1.toLocallyOfFiniteType
  have hjs : j ≫ sSb = sS := by
    rw [← hfbs, ← Category.assoc, hpb.w, Category.assoc, hιs, hfs]
  have hSbd : topologicalKrullDim Sb = (2 : ℕ) := by
    rw [← topologicalKrullDim_eq_of_isOpenImmersion sSb j]; exact hSd
  have hfbb : IsBirationalMorphism fb := isBirationalMorphism_of_comp_eq hpb.w hfb
  have hTbd : topologicalKrullDim Tb = (2 : ℕ) := by
    rw [← topologicalKrullDim_eq_of_isBirationalMorphism sSb sTb hfbb]; exact hSbd
  obtain ⟨Kb, hKb, hKbj⟩ := exists_isCanonicalDivisor_extension hSbQ.1 hSbd j (hjs ▸ hSn)
    (hjs ▸ hK)
  set Θb : RDivisor Sb := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j) Θ
    with hΘbdef
  obtain ⟨n, Ys, _, _, _, _, sYs, πYs, g, KYs, ΘYs, hchain, hYp, hYQ, hYk, hnef, φ, hφπ, hφb,
    hKY, hΘY, -, G, hG, hE0, hEexc, -, hrat⟩ :=
    exists_surface_divisorial_chain_isRealKltPair sSb sTb fb hSbp hSbQ.1 hSbd hSbQ hTbp hTbn hTbd
      hfbs hfbp hfbb Kb hKb Θb (coeff_mapDomain_primeDivisorMap_nonneg j hΘ) hΘbk
  have hπs : ∀ m ≤ n, modelMap fb πYs m ≫ sTb = modelStr sSb sYs m := by
    intro m hm
    cases m with
    | zero => exact hfbs
    | succ k => exact (hchain k hm).1
  have hφs : φ ≫ modelStr sSb sYs n = sSb := by
    rw [← hπs n le_rfl, ← Category.assoc, hφπ, hfbs]
  haveI : IsProper fb := isProper_of_isProjectiveMorphism fb hfbp
  haveI : IsSeparated (modelStr sSb sYs n) := hYp.toIsVariety.toIsSeparated
  haveI : IsSeparated (modelMap fb πYs n) := by
    haveI : IsSeparated (modelMap fb πYs n ≫ sTb) := by rw [hπs n le_rfl]; infer_instance
    exact IsSeparated.of_comp (modelMap fb πYs n) sTb
  haveI : IsProper (φ ≫ modelMap fb πYs n) := by rw [hφπ]; infer_instance
  haveI : IsProper φ := IsProper.of_comp φ (modelMap fb πYs n)
  haveI : LocallyOfFiniteType (modelStr sSb sYs n) := hYQ.1.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (φ ≫ modelStr sSb sYs n) := by rw [hφs]; infer_instance
  haveI : IsDominant φ := hφb.isDominant
  have hYd : topologicalKrullDim (modelSeq Sb Ys n) = (2 : ℕ) := by
    rw [← topologicalKrullDim_eq_of_isBirationalMorphism sSb (modelStr sSb sYs n) hφb]
    exact hSbd
  have hKYc : Divisor.IsCanonicalDivisor (modelStr sSb sYs n) 2 (divisorSeq Kb KYs n) := by
    let := functionFieldAlgebra (modelStr sSb sYs n)
    obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hYQ.1 hYd
    have hK0 := MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hYQ.1 hYd
      (b.ne_zero ())
    rw [hKY]
    exact Oai4C1.Main.isCanonicalDivisor_transformDivisor hYQ.1 (by rw [hφs]; exact hSbQ.1) hφb
      hK0 (by rw [hφs]; exact hKb)
  refine ⟨{
      Tb := Tb
      sTb := sTb
      ι := ι
      hTb := hTbn
      hTbp := hTbp
      Sb := Sb
      sSb := sSb
      fb := fb
      j := j
      hSb := hSbQ.1
      hSbQ := hSbQ
      hSbd := hSbd
      hfbs := hfbs
      hfbb := hfbb
      hpb := hpb
      Kb := Kb
      hKb := hKb
      hKbj := hKbj
      Θb := Θb
      hΘb := rfl
      hhull := hhull
      Y := modelSeq Sb Ys n
      sY := modelStr sSb sYs n
      πY := modelMap fb πYs n
      φ := φ
      hY := hYQ.1
      hYQ := hYQ
      hYp := hYp
      hπs := hπs n le_rfl
      hφπ := hφπ
      hφb := hφb
      KY := divisorSeq Kb KYs n
      hKY := hKYc
      hKYφ := hKY
      ΘY := divisorSeq Θb ΘYs n
      hΘY := hΘY
      hΘYk := hYk
      hnef := hnef
      G := G
      hG := hG
      hE := hE0
      hEexc := hEexc
      hrat := fun ⟨Θq, hΘq⟩ =>
        hrat ⟨Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j) Θq, by
          rw [toRDivisor_mapDomain_primeDivisorMap, hΘq]⟩
    }⟩

end Setup

/-! ### Klt coefficients and scheme-theoretic images -/

section KltImages

/-- On a klt pair every boundary coefficient is `< 1`, read off the klt dictionary
`MMP.Fourfold.isKltPair_iff_mori_isKltPair`. -/
private theorem coeff_lt_one_of_isKltPair' {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {Θ : QDivisor Y} (hΘ : IsKltPair sY Θ)
    (P : MMP.Mori.PrimeDivisor Y) : Θ.coeff P < 1 := by
  obtain ⟨-, n, K, hK, -⟩ := id hΘ.1.isPair
  exact MMP.Mori.roundDown_nonpos_iff.mp ((isKltPair_iff_mori_isKltPair sY hK hΘ.1).mp hΘ).2.2 P

/-- A dominant quasi-compact morphism of integral schemes has the whole target as its
scheme-theoretic image, so a birational one is birational onto its image. -/
private theorem isBirationalMorphism_toImage' {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [QuasiCompact f] (hfb : IsBirationalMorphism f) :
    IsBirationalMorphism f.toImage := by
  haveI := hfb.isDominant
  haveI : Surjective f.imageι := ⟨by
    rw [← Set.range_eq_univ, Scheme.Hom.range_imageι]
    exact f.denseRange.closure_eq⟩
  haveI : IsIso f.imageι := isIso_of_isClosedImmersion_of_surjective _
  rw [show f.toImage = f ≫ inv f.imageι by simp]
  exact MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hfb
    (isBirationalMorphism_of_isIso _)

end KltImages

/-! ### Consequences of the model -/

section ModelFacts

/-- An `ℝ`-Cartier divisor is a real combination of Cartier divisors. -/
private theorem isCartierCombination_of_isRCartier {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {D : RDivisor X} (h : RDivisor.IsRCartier D) :
    MMP.Flips.IsCartierCombination D := by
  obtain ⟨m, r, C, hC, hD⟩ := h
  refine ⟨m, r, C, hC, ?_⟩
  simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]
  ext Γ
  rw [hD Γ, MMP.Flips.coeff_sum_smul_toRDivisor]

/-- If `φ` and `φ ≫ π` are birational, then so is `π`. -/
private theorem isBirationalMorphism_of_comp {X Y Z : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] [IrreducibleSpace Z] {φ : X ⟶ Y} {π : Y ⟶ Z}
    (hφ : IsBirationalMorphism φ) (hcomp : IsBirationalMorphism (φ ≫ π)) :
    IsBirationalMorphism π := by
  haveI : Nonempty X := ⟨(IrreducibleSpace.isIrreducible_univ X).nonempty.some⟩
  obtain ⟨W₁, hW₁, h₁⟩ := hcomp.exists_isOpenImmersion
  obtain ⟨W₂, hW₂, h₂⟩ := hφ.exists_isOpenImmersion
  set U : X.Opens := W₁ ⊓ W₂
  have hU : (U : Set X).Nonempty := by
    have := (W₁.isOpen.dense hW₁).inter_of_isOpen_left (W₂.isOpen.dense hW₂) W₁.isOpen
    exact this.nonempty
  haveI : IsOpenImmersion (U.ι ≫ φ) := by
    rw [← X.homOfLE_ι (inf_le_right : U ≤ W₂), Category.assoc]; infer_instance
  haveI : IsOpenImmersion (U.ι ≫ φ ≫ π) := by
    rw [← X.homOfLE_ι (inf_le_left : U ≤ W₁), Category.assoc]; infer_instance
  let V := (U.ι ≫ φ).opensRange
  have hV : V.ι ≫ π = ((U.ι ≫ φ).isoOpensRange).inv ≫ U.ι ≫ φ ≫ π := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp_assoc]
    simp [Category.assoc]
  haveI : IsOpenImmersion (V.ι ≫ π) := by rw [hV]; infer_instance
  refine MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' π V ?_
  obtain ⟨x, hx⟩ := hU
  exact ⟨_, ⟨x, hx⟩, rfl⟩

variable {S T : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
  {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {f : S ⟶ T} {K : Divisor S}
  {Θ : RDivisor S}

private theorem SurfaceModel.hφs (M : SurfaceModel sS sT f K Θ) : M.φ ≫ M.sY = M.sSb := by
  rw [← M.hπs, ← Category.assoc, M.hφπ, M.hfbs]

private theorem SurfaceModel.hφn (M : SurfaceModel sS sT f K Θ) :
    IsNormalVariety ℂ (M.φ ≫ M.sY) := by
  rw [M.hφs]; exact M.hSb

private theorem SurfaceModel.fb_j (M : SurfaceModel sS sT f K Θ) (x : S) :
    M.fb (M.j x) = M.ι (f x) := by
  rw [← Scheme.Hom.comp_apply, M.hpb.w, Scheme.Hom.comp_apply]

private theorem SurfaceModel.πY_φ_j (M : SurfaceModel sS sT f K Θ) (x : S) :
    M.πY (M.φ (M.j x)) = M.ι (f x) := by
  rw [← Scheme.Hom.comp_apply, M.hφπ, M.fb_j]

/-- The strict transform on `S̄` of a prime divisor of the model. -/
private theorem SurfaceModel.exists_strictTransform (M : SurfaceModel sS sT f K Θ)
    (Q : MMP.Mori.PrimeDivisor M.Y) :
    ∃ E : MMP.Mori.PrimeDivisor M.Sb, M.φ E.genericPoint = Q.genericPoint ∧
      IsIso (M.φ.stalkMap E.genericPoint) ∧ ∀ {R : Type} [AddCommMonoid R]
        (D : DivisorWithCoeffs R M.Sb),
        RationalMap.transformDivisor M.φ.toRationalMap D Q = D E := by
  obtain ⟨E, h1, h2, h3⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply M.hY M.hφn M.hφb Q
  exact ⟨E, h1, h2, fun D => h3 D⟩

private theorem SurfaceModel.ΘY_nonneg (M : SurfaceModel sS sT f K Θ)
    (hΘ : ∀ P, 0 ≤ Θ.coeff P) (Q : MMP.Mori.PrimeDivisor M.Y) : 0 ≤ M.ΘY.coeff Q := by
  obtain ⟨E, -, -, hE⟩ := M.exists_strictTransform Q
  rw [M.hΘY, DivisorWithCoeffs.coeff_apply, hE]
  rw [M.hΘb]
  exact coeff_mapDomain_primeDivisorMap_nonneg M.j hΘ E

/-- `φ_*(K_{S̄} + Θ̄) = K_Y + Θ_Y`. -/
private theorem SurfaceModel.transformDivisor_adjoint (M : SurfaceModel sS sT f K Θ) :
    RationalMap.transformDivisor M.φ.toRationalMap (Divisor.toRDivisor M.Kb + M.Θb) =
      Divisor.toRDivisor M.KY + M.ΘY := by
  rw [map_add, transformDivisor_toRDivisor M.hY M.hφn M.hφb, ← M.hKYφ, ← M.hΘY]

/-- The comparison divisor `E = K_{S̄} + Θ̄ - φ^*(K_Y + Θ_Y)` is `φ`-exceptional. -/
private theorem SurfaceModel.transformDivisor_E (M : SurfaceModel sS sT f K Θ) :
    RationalMap.transformDivisor M.φ.toRationalMap (Divisor.toRDivisor M.Kb + M.Θb - M.G) = 0 := by
  rw [map_sub, M.transformDivisor_adjoint,
    transformDivisor_eq_of_isRCartierPullback M.hY M.hφn M.hφb M.hG, sub_self]

/-- The coefficient of `∑ᵢ vᵢ pᵢ` along `pᵢ`, for injective `p`. -/
private theorem coeff_sum_single_self {R : Type*} [AddCommMonoid R] {Y : Scheme.{0}} {r : ℕ}
    {p : Fin r → MMP.Mori.PrimeDivisor Y} (hp : Function.Injective p) (v : Fin r → R)
    (i : Fin r) :
    DivisorWithCoeffs.coeff (∑ i, Finsupp.single (p i) (v i) : DivisorWithCoeffs R Y) (p i) =
      v i := by
  classical
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.single_apply,
    hp.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The coefficient of `∑ᵢ vᵢ pᵢ` along a prime divisor outside the range of `p` vanishes. -/
private theorem coeff_sum_single_of_notMem {R : Type*} [AddCommMonoid R] {Y : Scheme.{0}}
    {r : ℕ} (p : Fin r → MMP.Mori.PrimeDivisor Y) (v : Fin r → R)
    {P : MMP.Mori.PrimeDivisor Y} (hP : P ∉ Set.range p) :
    DivisorWithCoeffs.coeff (∑ i, Finsupp.single (p i) (v i) : DivisorWithCoeffs R Y) P = 0 := by
  classical
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun i _ => by rw [Finsupp.single_apply, if_neg (fun h => hP ⟨i, h⟩)]

/-- **The relatively free cone on the model.** Relative-big-core uniform freeness on `Y`, with
core zero and the vertices of a rational klt polytope around `Θ_Y`: there are finitely many
Cartier divisors with relatively free multiples whose nonnegative real combinations contain every
adjoint `K_Y + Ψ`, for `Ψ` in the smallest rational affine hull of `Θ_Y` near `Θ_Y`; and a
uniform multiple of every Cartier multiple of `K_Y + Θ_Y` is relatively free. -/
private theorem SurfaceModel.exists_cone (M : SurfaceModel sS sT f K Θ)
    (hΘ : ∀ P, 0 ≤ Θ.coeff P) :
    ∃ H : Finset (Divisor M.Y), (∀ h ∈ H, h.IsCartier ∧
        ∃ p : ℕ, 0 < p ∧ IsRelativelyFreeDivisor M.πY ((p : ℤ) • h)) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ Ψ : RDivisor M.Y, IsInSmallestRationalAffineHull M.ΘY Ψ →
        (∀ Q, |Ψ.coeff Q - M.ΘY.coeff Q| < ε) →
        ∃ t : Divisor M.Y → ℝ, (∀ h, 0 ≤ t h) ∧
          Divisor.toRDivisor M.KY + Ψ = ∑ h ∈ H, t h • Divisor.toRDivisor h) ∧
      ∃ b : ℕ, 0 < b ∧ ∀ c : ℝ, 0 < c → ∀ D : Divisor M.Y, D.IsCartier →
        c • (Divisor.toRDivisor M.KY + M.ΘY) = Divisor.toRDivisor D →
        IsRelativelyFreeDivisor M.πY ((b : ℤ) • D) := by
  classical
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ M.sY := M.hYp
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ M.sTb := M.hTbp
  haveI : IsIntegral M.Tb := M.hTb.1.toIsIntegral
  haveI : LocallyOfFiniteType M.sY := M.hY.1.toLocallyOfFiniteType
  haveI : IsSeparated M.sTb := M.hTbp.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType (M.πY ≫ M.sTb) := by rw [M.hπs]; infer_instance
  haveI : LocallyOfFiniteType M.πY := LocallyOfFiniteType.of_comp (f := M.πY) (g := M.sTb) ‹_›
  haveI : QuasiCompact M.sY := M.hY.1.toQuasiCompact
  haveI : QuasiCompact (M.πY ≫ M.sTb) := by rw [M.hπs]; infer_instance
  haveI : QuasiCompact M.πY := QuasiCompact.of_comp M.πY M.sTb
  have hΘY0 : 0 ≤ M.ΘY := M.ΘY_nonneg hΘ
  set r := M.ΘY.support.card
  set e := M.ΘY.support.equivFin
  set p : Fin r → MMP.Mori.PrimeDivisor M.Y := fun i => (e.symm i).1 with hpdef
  have hp : Function.Injective p := fun i i' h => e.symm.injective (Subtype.ext h)
  have hΔp : ∀ P, M.ΘY.coeff P ≠ 0 → P ∈ Set.range p := fun P hP =>
    ⟨e ⟨P, Finsupp.mem_support_iff.mpr hP⟩, by simp [hpdef]⟩
  obtain ⟨V, -, hVint, hVlow, hVklt⟩ := exists_rationalPolytope_isKltPair_of_isRealKltPair M.sY
    M.hYp M.hYQ M.ΘY hΘY0 M.hΘYk 0 le_rfl (by rw [map_zero]; exact hΘY0) p hp hΔp
    (fun P hP => absurd rfl hP)
  let toDiv : (Fin r → ℚ) → QDivisor M.Y := fun v => ∑ i, Finsupp.single (p i) (v i)
  have hcoeffDiv : ∀ v i, (toDiv v).coeff (p i) = v i := coeff_sum_single_self hp
  have hcoeffDiv' : ∀ v P, P ∉ Set.range p → (toDiv v).coeff P = 0 := fun v _ =>
    coeff_sum_single_of_notMem p v
  have hVnn : ∀ v ∈ V, ∀ i, (0 : ℝ) ≤ v i := fun v hv i => by
    simpa using hVlow _ (subset_convexHull ℝ _ ⟨v, hv, rfl⟩) i
  let V' := V.image toDiv
  have hV'eff : ∀ Γ ∈ V', Γ.IsEffective := by
    intro Γ hΓ P
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hΓ
    by_cases hP : P ∈ Set.range p
    · obtain ⟨i, rfl⟩ := hP
      rw [hcoeffDiv]; exact_mod_cast hVnn v hv i
    · rw [hcoeffDiv' v P hP]
  have hV'klt : ∀ Γ ∈ V', IsKltPair M.sY Γ := by
    intro Γ hΓ
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hΓ
    exact hVklt v hv
  let L : (Fin r → ℝ) →ₗ[ℝ] RDivisor M.Y :=
    Fintype.linearCombination ℝ fun i => Finsupp.single (p i) (1 : ℝ)
  have hLt : ∀ t, L t = ∑ i, Finsupp.single (p i) (t i) := fun t => by
    simp only [L, Fintype.linearCombination_apply, Finsupp.smul_single_one]
  have hL : ∀ v : Fin r → ℚ, L (fun i => (v i : ℝ)) = QDivisor.toRDivisor (toDiv v) := fun v => by
    refine DivisorWithCoeffs.ext' fun P => ?_
    rw [hLt, QDivisor.coeff_toRDivisor]
    by_cases hP : P ∈ Set.range p
    · obtain ⟨i, rfl⟩ := hP
      rw [hcoeffDiv, coeff_sum_single_self hp]
    · rw [hcoeffDiv' v P hP, coeff_sum_single_of_notMem p _ hP, Rat.cast_zero]
  have hLΘ : L (fun i => M.ΘY.coeff (p i)) = M.ΘY := by
    refine DivisorWithCoeffs.ext' fun P => ?_
    rw [hLt]
    by_cases hP : P ∈ Set.range p
    · obtain ⟨i, rfl⟩ := hP
      rw [coeff_sum_single_self hp]
    · rw [coeff_sum_single_of_notMem p _ hP]
      by_contra h
      exact hP (hΔp P (Ne.symm h))
  have hΔ : M.ΘY ∈ convexHull ℝ (QDivisor.toRDivisor '' (V' : Set (QDivisor M.Y))) := by
    have h2 : L (fun i => M.ΘY.coeff (p i)) ∈
        L '' convexHull ℝ ((fun v : Fin r → ℚ => fun i => (v i : ℝ)) '' ↑V) :=
      ⟨_, intrinsicInterior_subset hVint, rfl⟩
    rw [LinearMap.image_convexHull, hLΘ, ← Set.image_comp] at h2
    convert h2 using 2
    ext Γ
    simp only [V', Finset.coe_image, Set.mem_image, Function.comp_apply, hL]
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  have hbir : IsBirationalMorphism M.πY := isBirationalMorphism_of_comp M.hφb (M.hφπ ▸ M.hfbb)
  obtain ⟨-, hbig⟩ :=
    isRelativelyPseudoEffective_and_isRelativelyBig_zero_of_isBirationalMorphism_toImage M.sY
      M.sTb M.πY M.hYp M.hYQ M.hTbp M.hTb M.hπs (isBirationalMorphism_toImage' M.πY hbir)
  obtain ⟨VQ, -, -, hΔVQ, hext, ⟨b, hb, hbfree⟩, H, hH, hdec⟩ :=
    QDivisor.IsRelativelyBig.exists_isRelativelyFreeDivisor_nsmul_of_isRelativelyNef M.sY M.sTb
      M.hYQ M.πY M.hπs ⟨2, M.hKY⟩ hbig (fun _ => le_rfl) V' hV'eff
      (fun Γ hΓ E => (coeff_lt_one_of_isKltPair' (hV'klt Γ hΓ) E).le)
      (fun Γ hΓ P => hV'eff Γ hΓ P) hV'klt hΔ M.hnef
  obtain ⟨ε, hε, hmem⟩ := exists_forall_mem_convexHull VQ hΔVQ hext
  exact ⟨H, hH, ⟨ε, hε, fun Ψ hΨ hclose => hdec Ψ (hmem Ψ hΨ hclose)⟩, b, hb,
    fun c hc D hD hcD => hbfree M.ΘY hΔVQ c hc D hD hcD⟩

end ModelFacts

/-! ### Persistence of the stable base primes -/

section Persistence

variable {S T : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
  {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {f : S ⟶ T} {K : Divisor S}
  {Θ : RDivisor S}

/-- The coefficients of `K̄ + Θ̄'` along the closure of a prime divisor of `S`. -/
private theorem SurfaceModel.coeff_extend (M : SurfaceModel sS sT f K Θ) (Θ' : RDivisor S)
    (P : MMP.Mori.PrimeDivisor S) :
    (Divisor.toRDivisor M.Kb + Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap M.j) Θ').coeff
        (OpenWeilRestriction.primeDivisorMap M.j P) =
      DivisorWithCoeffs.coeff (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K + Θ') P := by
  rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, M.hKbj]
  congr 1
  exact Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective M.j) Θ' P

/-- The decomposition of `K_Y + Θ_Y` into relatively free Cartier divisors, indexed by `Fin m`. -/
private theorem SurfaceModel.exists_free_decomposition (M : SurfaceModel sS sT f K Θ)
    (hΘ : ∀ P, 0 ≤ Θ.coeff P) :
    ∃ (m : ℕ) (c : Fin m → ℝ) (H : Fin m → Divisor M.Y), (∀ i, 0 ≤ c i) ∧
      (∀ i, (H i).IsCartier) ∧ (∀ i, IsRelativelyFreeDivisor M.πY (H i)) ∧
      Divisor.toRDivisor M.KY + M.ΘY = ∑ i, c i • Divisor.toRDivisor (H i) := by
  classical
  obtain ⟨H, hH, ⟨ε, hε, hcone⟩, -⟩ := M.exists_cone hΘ
  obtain ⟨t, ht, hdec⟩ := hcone M.ΘY ⟨le_rfl, fun _ _ h => h⟩
    (fun Q => by simpa using hε)
  choose! pH hpH hpHfree using fun h (hh : h ∈ H) => (hH h hh).2
  let eH := H.equivFin
  let Hf : Fin H.card → Divisor M.Y := fun i => (eH.symm i).1
  refine ⟨H.card, fun i => t (Hf i) / pH (Hf i), fun i => (pH (Hf i) : ℤ) • Hf i,
    fun i => div_nonneg (ht _) (Nat.cast_nonneg _),
    fun i => (hH _ (eH.symm i).2).1.zsmul _, fun i => hpHfree _ (eH.symm i).2, ?_⟩
  rw [hdec]
  have hterm : ∀ i, (t (Hf i) / pH (Hf i)) • Divisor.toRDivisor ((pH (Hf i) : ℤ) • Hf i) =
      t (Hf i) • Divisor.toRDivisor (Hf i) := fun i => by
    have hp0 : (pH (Hf i) : ℝ) ≠ 0 := by exact_mod_cast (hpH _ (eH.symm i).2).ne'
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, Int.cast_natCast,
      div_mul_cancel₀ _ hp0]
  simp_rw [hterm]
  rw [← Finset.sum_coe_sort H]
  exact (Equiv.sum_comp eH.symm (fun h : H => t h.1 • Divisor.toRDivisor h.1)).symm

/-- **Persistence of the stable base primes** for every boundary supported on the support of `Θ`
whose coefficients are close to those of `Θ`. -/
private theorem SurfaceModel.exists_isInRelativeDivisorialStableBase_of_close
    (M : SurfaceModel sS sT f K Θ)
    (hΘ : ∀ P, 0 ≤ Θ.coeff P) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Θ' : RDivisor S, Θ'.support ⊆ Θ.support →
      (∀ P, |Θ'.coeff P - Θ.coeff P| < ε) →
      ∀ G : MMP.Mori.PrimeDivisor S,
        IsInRelativeDivisorialStableBase f
          (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K + Θ) G →
        IsInRelativeDivisorialStableBase f
          (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K + Θ') G := by
  classical
  haveI : IsIntegral M.Tb := M.hTb.1.toIsIntegral
  haveI : IsDominant M.φ := M.hφb.isDominant
  obtain ⟨s, P, -, hext⟩ := exists_coordinates M.j Θ
  set Pb : Fin s → MMP.Mori.PrimeDivisor M.Sb :=
    fun i => OpenWeilRestriction.primeDivisorMap M.j (P i) with hPbdef
  let L : (Fin s → ℝ) →ₗ[ℝ] RDivisor M.Sb :=
    Fintype.linearCombination ℝ fun i => Finsupp.single (Pb i) (1 : ℝ)
  have hLcoeff : ∀ (t : Fin s → ℝ) Q, (L t).coeff Q = ∑ i, t i * if Pb i = Q then 1 else 0 :=
    fun t Q => by
      simp [L, Fintype.linearCombination_apply, DivisorWithCoeffs.coeff_apply,
        Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hLext : ∀ Θ' : RDivisor S, Θ'.support ⊆ Θ.support →
      L (fun i => Θ'.coeff (P i)) =
        Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap M.j) Θ' := fun Θ' hsub =>
    (Fintype.linearCombination_apply ℝ _ _).trans (hext Θ' hsub)
  let D : (Fin s → ℝ) →ᵃ[ℝ] RDivisor M.Sb :=
    ⟨fun t => Divisor.toRDivisor M.Kb + L t, L, fun t v => by
      simp only [vadd_eq_add, map_add]; abel⟩
  have hDt : ∀ t, D t = Divisor.toRDivisor M.Kb + L t := fun _ => rfl
  let D' : (Fin s → ℝ) →ᵃ[ℝ] RDivisor M.Y :=
    (RationalMap.transformDivisorₗ ℝ M.φ.toRationalMap).toAffineMap.comp D
  have hD't : ∀ t, D' t = RationalMap.transformDivisor M.φ.toRationalMap (D t) := fun _ => rfl
  have hDc : ∀ t, RDivisor.IsRCartier (D t) := fun t => IsQFactorial.isRCartier M.hSbQ _
  have hD'c : ∀ t, RDivisor.IsRCartier (D' t) := fun t => IsQFactorial.isRCartier M.hYQ _
  set Sfin : Finset (MMP.Mori.PrimeDivisor M.Sb) := M.Kb.support ∪ Finset.univ.image Pb
  have hDsupp : ∀ t, (D t).support ⊆ Sfin := fun t Q hQ => by
    by_contra hQS
    simp only [Sfin, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or,
      not_exists] at hQS
    apply Finsupp.mem_support_iff.mp hQ
    change (D t).coeff Q = 0
    rw [hDt, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
      show M.Kb.coeff Q = 0 from Finsupp.notMem_support_iff.mp hQS.1, hLcoeff]
    simp only [Int.cast_zero, zero_add]
    exact Finset.sum_eq_zero fun i _ => by rw [if_neg (hQS.2 i), mul_zero]
  choose Est hEst1 hEst2 hEst3 using M.exists_strictTransform
  have hEstinj : Function.Injective Est := fun Q Q' h =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective ((hEst1 Q).symm.trans
      (h ▸ hEst1 Q'))
  have hD'supp : ∀ t, (D' t).support ⊆ Sfin.preimage Est hEstinj.injOn := fun t Q hQ => by
    rw [Finset.mem_preimage]
    have h1 := Finsupp.mem_support_iff.mp hQ
    rw [hD't, hEst3] at h1
    exact hDsupp t (Finsupp.mem_support_iff.mpr h1)
  have hex : ∀ t, ∃ G, MMP.Flips.IsRCartierPullback M.φ (D' t) G := fun t =>
    (MMP.Flips.existsUnique_isRCartierPullback M.φ
      (isCartierCombination_of_isRCartier (hD'c t))).exists
  choose Q hQ using hex
  have hP : ∀ t, MMP.Flips.IsRCartierPullback (𝟙 M.Sb) (D t) (D t) := fun t =>
    isRCartierPullback_id_of_isCartierCombination (isCartierCombination_of_isRCartier (hDc t))
  have hqE : ∀ t, RationalMap.transformDivisor M.φ.toRationalMap (D t - Q t) = 0 := fun t => by
    rw [map_sub, transformDivisor_eq_of_isRCartierPullback M.hY M.hφn M.hφb (hQ t), hD't,
      sub_self]
  set δ : Fin s → ℝ := fun i => Θ.coeff (P i)
  have hDδ : D δ = Divisor.toRDivisor M.Kb + M.Θb := by
    rw [hDt, hLext Θ subset_rfl, M.hΘb]
  have hQδ : Q δ = M.G := by
    refine MMP.Flips.IsRCartierPullback.eq M.φ (hQ δ) ?_
    rw [hD't, hDδ, M.transformDivisor_adjoint]
    exact M.hG
  have key := eventually_isInRelativeDivisorialStableBase_of_coeff_pos (k := ℂ) M.hSb M.hY M.hSb
    M.hTb.1 (𝟙 M.Sb) M.φ M.fb M.πY (isBirationalMorphism_of_isIso _) M.hφb
    (Category.id_comp _) M.hφs M.hfbs M.hπs (by rw [Category.id_comp, M.hφπ]) D D' hDc hD'c
    ⟨Sfin, hDsupp⟩ ⟨_, hD'supp⟩ (fun t => D t) Q hP hQ hqE δ
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp key
  obtain ⟨m, c, H, hc, hHc, hHfree, hlin⟩ := M.exists_free_decomposition hΘ
  have hE0 : 0 ≤ Divisor.toRDivisor M.Kb + M.Θb - M.G := Finsupp.le_def.mpr M.hE
  have hiff := isInRelativeDivisorialStableBase_iff_pos_transformDivisor (k := ℂ) M.hSb M.hY
    M.hSb (𝟙 M.Sb) M.φ M.fb M.πY (isBirationalMorphism_of_isIso _) M.hφb (Category.id_comp _)
    M.hφs (by rw [Category.id_comp, M.hφπ])
    (isRCartierPullback_id_of_isCartierCombination (isCartierCombination_of_isRCartier
      (IsQFactorial.isRCartier M.hSbQ (Divisor.toRDivisor M.Kb + M.Θb)))) M.hG
    (by abel) hE0 M.transformDivisor_E c hc H hHc hHfree (s₀ := 0) Fin.elim0 Fin.elim0
    (by rw [hlin]; simp)
  refine ⟨ε, hε, fun Θ' hsub hclose G hG => ?_⟩
  have hGb := (isInRelativeDivisorialStableBase_iff_of_isPullback M.hpb
    (M.coeff_extend Θ) G).mp hG
  rw [← M.hΘb] at hGb
  set t' : Fin s → ℝ := fun i => Θ'.coeff (P i)
  have hdist : dist t' δ < ε := (dist_pi_lt_iff hε).mpr fun i => by
    rw [Real.dist_eq]; exact hclose (P i)
  have hEδ : (fun t => D t) δ - Q δ = Divisor.toRDivisor M.Kb + M.Θb - M.G := by
    simp only [hDδ, hQδ]
  have h1 := hball hdist (OpenWeilRestriction.primeDivisorMap M.j G)
    (by rw [hEδ]; exact (hiff _).mp hGb)
  rw [hDt, hLext Θ' hsub] at h1
  exact (isInRelativeDivisorialStableBase_iff_of_isPullback M.hpb (M.coeff_extend Θ') G).mpr h1

end Persistence

/-! ### Fixed parts along the smallest rational affine hull -/

section FixedPartLemmas

/-- A rational linear form `∑ᵢ cᵢ Pᵢ` evaluated on a real divisor. -/
private theorem sum_single_sum {S : Scheme.{0}} {s : ℕ} (P : Fin s → MMP.Mori.PrimeDivisor S)
    (hP : Function.Injective P) (c : Fin s → ℚ) (Ψ : RDivisor S) :
    ((∑ i, Finsupp.single (P i) (c i)).sum fun P cP => (cP : ℝ) * Ψ.coeff P) =
      ∑ i, (c i : ℝ) * Ψ.coeff (P i) := by
  classical
  rw [← Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum_single_index (by simp)]

/-- A rational affine function of the coordinates along `Pᵢ` that vanishes at `Θ` vanishes at
every divisor in the smallest rational affine hull of `Θ`. -/
private theorem eq_zero_of_isInSmallestRationalAffineHull {S : Scheme.{0}} {s : ℕ}
    {P : Fin s → MMP.Mori.PrimeDivisor S} (hP : Function.Injective P) {Θ Φ : RDivisor S}
    (hΦ : IsInSmallestRationalAffineHull Θ Φ) (c₀ : ℚ) (c : Fin s → ℚ)
    (h0 : (c₀ : ℝ) + ∑ i, (c i : ℝ) * Θ.coeff (P i) = 0) :
    (c₀ : ℝ) + ∑ i, (c i : ℝ) * Φ.coeff (P i) = 0 := by
  have h := hΦ.2 (∑ i, Finsupp.single (P i) (c i)) (-c₀)
    (by rw [sum_single_sum P hP]; push_cast; linarith)
  rw [sum_single_sum P hP] at h
  push_cast at h
  linarith

/-- A relatively free section of an integral combination of relatively free Cartier divisors,
generating at a given point. -/
private theorem exists_local_section {Y Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (π : Y ⟶ Z) (H : Finset (Divisor Y)) (pH : Divisor Y → ℕ)
    (hH : ∀ h ∈ H, h.IsCartier ∧ IsRelativelyFreeDivisor π ((pH h : ℤ) • h))
    (mH : Divisor Y → ℕ) (y : Y) :
    ∃ (U' : Z.Opens) (_ : π y ∈ U') (ψ : (RationalFunctions Y)ˣ),
      (∀ Q : MMP.Mori.PrimeDivisor Y, (Q.support ∩ π ⁻¹ᵁ U').Nonempty →
        0 ≤ ∑ h ∈ H, ((mH h : ℤ) * pH h) * h.coeff Q + Q.ord ψ) ∧
      ∀ Q : MMP.Mori.PrimeDivisor Y, y ∈ Q.support →
        ∑ h ∈ H, ((mH h : ℤ) * pH h) * h.coeff Q + Q.ord ψ = 0 := by
  classical
  let Dh : H → Divisor Y := fun h => ((mH h.1 : ℕ) : ℤ) • ((pH h.1 : ℤ) • h.1)
  obtain ⟨hNc, hNf⟩ := isRelativelyFreeDivisor_sum π Finset.univ (D := Dh)
    (fun h => (((hH h.1 h.2).1.zsmul _).zsmul _))
    (fun h => isRelativelyFreeDivisor_nsmul π ((hH h.1 h.2).1.zsmul _) (hH h.1 h.2).2 (mH h.1))
  obtain ⟨U', hU', ψ, h1, h2⟩ := exists_coeff_add_ord_eq_zero_of_isRelativelyFree π hNc hNf y
  have hcoeff : ∀ Q : MMP.Mori.PrimeDivisor Y, (∑ h : H, Dh h).coeff Q =
      ∑ h ∈ H, ((mH h : ℤ) * pH h) * h.coeff Q := fun Q => by
    rw [← Finset.sum_coe_sort H]
    simp only [Dh, DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul, mul_assoc]
  exact ⟨U', hU', ψ, fun Q hQ => hcoeff Q ▸ h1 Q hQ, fun Q hQ => hcoeff Q ▸ h2 Q hQ⟩

/-- **A nonzero global section** from a relative section near a fibre: over an affine base,
a unit `χ` with `D + div χ` effective over a neighbourhood `U` of `f x` gives a nonzero global
section of `𝒪_X(D)`, since `𝒪_X(D)` is quasi-coherent. -/
private theorem exists_ne_zero_mem_divisorialSubmodule_top {X T : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsAffine T] (f : X ⟶ T)
    (D : Divisor X) {U : T.Opens} {x : X} (hx : f x ∈ U) (χ : (RationalFunctions X)ˣ)
    (h : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ f ⁻¹ᵁ U).Nonempty →
      0 ≤ D.coeff P + P.ord χ) :
    ∃ σ ∈ D.divisorialSubmodule ⊤, σ ≠ 0 := by
  classical
  obtain ⟨g, hgle, hxg⟩ := (isAffineOpen_top T).exists_basicOpen_le (V := U) ⟨f x, hx⟩ trivial
  set s : Γ(X, f ⁻¹ᵁ ⊤) := f.app ⊤ g
  set O := X.basicOpen s
  have hOU : O ≤ f ⁻¹ᵁ U := by
    intro y hy
    have : y ∈ f ⁻¹ᵁ T.basicOpen g := by rw [Scheme.preimage_basicOpen]; exact hy
    exact hgle this
  have hxO : x ∈ O := by
    have : x ∈ f ⁻¹ᵁ T.basicOpen g := hxg
    rwa [Scheme.preimage_basicOpen] at this
  have hOW : O ≤ f ⁻¹ᵁ ⊤ := X.basicOpen_le s
  let χK : Γ(D.divisorialSheaf, O) :=
    ⟨fun Y' => (χ : RationalFunctions X) Y'.1, isDivisorialSection_of_unit χ
      fun P hP => h P (hP.mono (Set.inter_subset_inter_right _ hOU))⟩
  have hloc := Divisor.isLocalizedModule_divisorialSheaf_restrictₗ D s
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, ha⟩ := IsLocalizedModule.surj (Submonoid.powers s)
    (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ D.divisorialSheaf
      (X.basicOpen_le s)) χK
  simp only [Submonoid.smul_def] at ha
  set v : Γ(X, O) := X.presheaf.map (homOfLE hOW).op s
  have hvu : IsUnit v := RingedSpace.isUnit_res_basicOpen X.toRingedSpace s
  have hkey : ∀ Y' : {Y' : irreducibleComponents X // componentGenericPoint X Y' ∈ O},
      a.1 ⟨Y'.1, hOW Y'.2⟩ =
        X.presheaf.germ O _ Y'.2 (v ^ m) * (χ : RationalFunctions X) Y'.1 := by
    intro Y'
    have h' := congrFun (congrArg (fun z : Γ(D.divisorialSheaf, O) =>
      (show D.divisorialSubmodule O from z).1) ha) Y'
    refine h'.symm.trans ?_
    change X.presheaf.germ O _ Y'.2 (X.presheaf.map (homOfLE hOW).op (s ^ m)) *
      (χ : RationalFunctions X) Y'.1 = _
    rw [map_pow]
  refine ⟨a.1, a.2, fun h0 => ?_⟩
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents X) := ⟨pointComponent x⟩
  have hZ₀ : componentGenericPoint X Z₀ ∈ O :=
    (MMP.Mori.genericPoint_mem_iff Z₀ O).mpr
      ⟨x, hxO, Fourfold.mem_irreducibleComponent_of_irreducibleSpace Z₀ x⟩
  have hu : IsUnit (X.presheaf.germ O _ hZ₀ (v ^ m) * (χ : RationalFunctions X) Z₀) :=
    ((hvu.pow m).map (X.presheaf.germ O _ hZ₀).hom).mul
      (χ.isUnit.map (Pi.evalRingHom _ Z₀))
  exact hu.ne_zero ((hkey ⟨Z₀, hZ₀⟩).symm.trans (congrFun h0 ⟨Z₀, hOW hZ₀⟩))

/-- **Fixed multiplicity zero.** A unit `χ` with `D + div χ` effective over a neighbourhood `U` of
the image of the generic point of `G`, of coefficient zero along `G`, is a relative section of
`𝒪_X(D)` not vanishing along `G`. -/
private theorem relativeFixedMultiplicity_eq_zero {X Z : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (f : X ⟶ Z) (D : Divisor X) (G : MMP.Mori.PrimeDivisor X) {U : Z.Opens}
    (hU : f G.genericPoint ∈ U) (χ : (RationalFunctions X)ˣ)
    (h : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ f ⁻¹ᵁ U).Nonempty →
      0 ≤ D.coeff P + P.ord χ)
    (hG : D.coeff G + G.ord χ = 0) : relativeFixedMultiplicity f D G = 0 := by
  refine le_antisymm ?_ bot_le
  let σ : D.divisorialSubmodule (f ⁻¹ᵁ U) :=
    ⟨fun Z => (χ : RationalFunctions X) Z.1, isDivisorialSection_of_unit χ h⟩
  have hne := support_inter_preimage_nonempty f hU
  have hσ : σ ≠ 0 := by
    intro h0
    have := congrFun (congrArg Subtype.val h0)
      ⟨G.component, G.componentGenericPoint_mem_of_nonempty hne⟩
    exact (χ.isUnit.map (Pi.evalRingHom _ G.component)).ne_zero this
  calc relativeFixedMultiplicity f D G ≤ sectionVanishingOrder D G hne σ :=
        iInf_le_of_le U (iInf_le_of_le hU (iInf_le_of_le σ (iInf_le _ hσ)))
    _ = ((D.coeff G + G.ord χ).toNat : ℕ∞) := sectionVanishingOrder_eq_toNat hne σ χ rfl
    _ = 0 := by rw [hG]; rfl

end FixedPartLemmas

section FixedPartModel

variable {S T : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
  {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {f : S ⟶ T} {K : Divisor S}
  {Θ : RDivisor S}

/-- The push-forward to the model preserves smallest rational affine hulls. -/
private theorem SurfaceModel.isInSmallestRationalAffineHull_transform
    (M : SurfaceModel sS sT f K Θ) {A B : RDivisor M.Sb}
    (h : IsInSmallestRationalAffineHull A B) :
    IsInSmallestRationalAffineHull (RationalMap.transformDivisor M.φ.toRationalMap A)
      (RationalMap.transformDivisor M.φ.toRationalMap B) := by
  classical
  choose Est hEst1 hEst2 hEst3 using M.exists_strictTransform
  refine ⟨fun Q hQ => ?_, fun c q hc => ?_⟩
  · have h1 := Finsupp.mem_support_iff.mp hQ
    rw [hEst3] at h1
    rw [Finsupp.mem_support_iff, hEst3]
    exact Finsupp.mem_support_iff.mp (h.1 (Finsupp.mem_support_iff.mpr h1))
  · have key : ∀ D : RDivisor M.Sb,
        (c.sum fun Q cQ => (cQ : ℝ) *
          (RationalMap.transformDivisor M.φ.toRationalMap D).coeff Q) =
          ((c.mapDomain Est).sum fun P cP => (cP : ℝ) * D.coeff P) := fun D => by
      rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
      simp only [DivisorWithCoeffs.coeff_apply, hEst3]
    rw [key] at hc ⊢
    exact h.2 _ q hc

/-- **The rational affine family of comparison divisors.** Along a family
`K̄ + ∑ tᵢ P̄ᵢ` of real divisors on `S̄`, the pull-backs of the push-forwards form an affine
family, and every coefficient of the comparison divisor is a rational affine function of `t`. -/
private theorem SurfaceModel.exists_pullback_family (M : SurfaceModel sS sT f K Θ) {s : ℕ}
    (Pb : Fin s → MMP.Mori.PrimeDivisor M.Sb) :
    ∃ Q : (Fin s → ℝ) → RDivisor M.Sb, (∀ t, MMP.Flips.IsRCartierPullback M.φ
        (RationalMap.transformDivisor M.φ.toRationalMap
          (Divisor.toRDivisor M.Kb + ∑ i, t i • Finsupp.single (Pb i) (1 : ℝ))) (Q t)) ∧
      ∀ G : MMP.Mori.PrimeDivisor M.Sb, ∃ (c₀ : ℚ) (c : Fin s → ℚ), ∀ t,
        (Divisor.toRDivisor M.Kb + ∑ i, t i • Finsupp.single (Pb i) (1 : ℝ) - Q t).coeff G =
          c₀ + ∑ i, (c i : ℝ) * t i := by
  classical
  haveI : IsDominant M.φ := M.hφb.isDominant
  let A : Fin s → Divisor M.Y := fun i =>
    RationalMap.transformDivisor M.φ.toRationalMap (Finsupp.single (Pb i) (1 : ℤ))
  have hrat : ∀ B : Divisor M.Y, ∃ (m : ℕ) (L' : Divisor M.Sb), 0 < m ∧
      MMP.Flips.IsRCartierPullback M.φ (Divisor.toRDivisor B)
        ((1 / (m : ℝ)) • Divisor.toRDivisor L') := by
    intro B
    obtain ⟨m, hm, hmc⟩ := M.hYQ.2 B
    have hB : ∀ Z : irreducibleComponents M.Sb,
        M.φ (componentGenericPoint M.Sb Z) ∉ (((m : ℤ) • B).supp) := fun Z =>
      map_componentGenericPoint_notMem_supp_of_isDominant M.φ _ Z
    refine ⟨m, ((m : ℤ) • B).pullback hmc hB, hm, ?_⟩
    have := MMP.Flips.isRCartierPullback_of_zsmul_eq M.φ (D := Divisor.toQDivisor B) hm hmc
      (by ext P; simp [Divisor.coeff_toQDivisor]) ⟨hB, Divisor.isPullback_pullback hmc hB⟩
    convert this using 2
    ext P; simp
  obtain ⟨mK, LK, hmK, hK⟩ := hrat M.KY
  choose mA LA hmA hA using fun i => hrat (A i)
  refine ⟨fun t => (1 / (mK : ℝ)) • Divisor.toRDivisor LK +
    ∑ i, t i • ((1 / (mA i : ℝ)) • Divisor.toRDivisor (LA i)), fun t => ?_, fun G => ?_⟩
  · have htr : RationalMap.transformDivisor M.φ.toRationalMap
        (Divisor.toRDivisor M.Kb + ∑ i, t i • Finsupp.single (Pb i) (1 : ℝ)) =
        Divisor.toRDivisor M.KY + ∑ i, t i • Divisor.toRDivisor (A i) := by
      rw [map_add, transformDivisor_toRDivisor M.hY M.hφn M.hφb, ← M.hKYφ, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← RationalMap.transformDivisorₗ_apply ℝ, LinearMap.map_smul,
        RationalMap.transformDivisorₗ_apply]
      congr 1
      rw [show Finsupp.single (Pb i) (1 : ℝ) = Divisor.toRDivisor (Finsupp.single (Pb i) 1) by
        ext Q
        rw [Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
          Finsupp.single_apply, Finsupp.single_apply]
        split_ifs <;> simp]
      exact transformDivisor_toRDivisor M.hY M.hφn M.hφb _
    rw [htr]
    exact isRCartierPullback_add hK
      (isRCartierPullback_sum _ _ _ fun i _ => isRCartierPullback_smul _ (hA i))
  · refine ⟨(M.Kb.coeff G : ℚ) - (1 / (mK : ℚ)) * LK.coeff G,
      fun i => (if Pb i = G then 1 else 0) - (1 / (mA i : ℚ)) * (LA i).coeff G, fun t => ?_⟩
    have hsum : ∀ (c : Fin s → ℝ) (E : Fin s → RDivisor M.Sb),
        (∑ i, c i • E i).coeff G = ∑ i, c i * (E i).coeff G := fun c E => by
      simp [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
    have hsingle : ∀ i, DivisorWithCoeffs.coeff (Finsupp.single (Pb i) (1 : ℝ)) G =
        if Pb i = G then 1 else 0 :=
      fun i => by rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add,
      hsum, hsum]
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul, hsingle]
    have hc : ∀ i, (((if Pb i = G then 1 else 0) - 1 / (mA i : ℚ) * (LA i).coeff G : ℚ) : ℝ) *
        t i = t i * (if Pb i = G then 1 else 0) - t i * (1 / (mA i : ℝ) * (LA i).coeff G) :=
      fun i => by split_ifs <;> push_cast <;> ring
    simp_rw [hc]
    rw [Finset.sum_sub_distrib]
    push_cast
    ring

end FixedPartModel

section FixedPartMain

/-- **A pull-back coefficient vanishes** along a prime divisor `Γ` when the pulled-back
`ℝ`-Cartier divisor is effective near `h(η_Γ)` and has coefficient zero along every prime divisor
through `h(η_Γ)`. -/
private theorem coeff_eq_zero_of_isRCartierPullback {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (h : X ⟶ Y) [IsDominant h] {L : RDivisor Y} {G : RDivisor X}
    (hG : MMP.Flips.IsRCartierPullback h L G) (Γ : MMP.Mori.PrimeDivisor X) {V : Y.Opens}
    (hΓV : h Γ.genericPoint ∈ V)
    (hV : ∀ Q : MMP.Mori.PrimeDivisor Y, (Q.support ∩ V).Nonempty → 0 ≤ L.coeff Q)
    (hzero : ∀ Q : MMP.Mori.PrimeDivisor Y, h Γ.genericPoint ∈ Q.support → L.coeff Q = 0) :
    G.coeff Γ = 0 := by
  classical
  refine le_antisymm ?_ (coeff_nonneg_of_isRCartierPullback_of_isEffectiveOn h hG hV Γ
    ((MMP.Mori.PrimeDivisor.genericPoint_mem_iff Γ (h ⁻¹ᵁ V)).mp hΓV))
  set y := h Γ.genericPoint
  let Z : Set Y := ⋃ Q ∈ L.support.filter (fun Q => y ∉ Q.support), (Q.support : Set Y)
  have hZ : IsClosed Z := by
    refine Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun Q _ => ?_
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  let V' : Y.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have hyV' : y ∈ V' := by
    change y ∉ Z
    intro hyZ
    simp only [Z, Set.mem_iUnion] at hyZ
    obtain ⟨Q, hQ, hyQ⟩ := hyZ
    exact (Finset.mem_filter.mp hQ).2 hyQ
  have hneg : MMP.Flips.IsRCartierPullback h (-L) (-G) := by
    simpa using isRCartierPullback_smul (-1) hG
  have := coeff_nonneg_of_isRCartierPullback_of_isEffectiveOn h hneg (V := V')
    (fun Q ⟨z, hzQ, hzV⟩ => by
    by_cases hL : L.coeff Q = 0
    · simp [DivisorWithCoeffs.coeff_neg, hL]
    · by_cases hyQ : y ∈ Q.support
      · exact absurd (hzero Q hyQ) hL
      · exact absurd (Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_filter.mpr
          ⟨Finsupp.mem_support_iff.mpr hL, hyQ⟩)) hzQ) hzV) Γ
    ((MMP.Mori.PrimeDivisor.genericPoint_mem_iff Γ (h ⁻¹ᵁ V')).mp hyV')
  rw [DivisorWithCoeffs.coeff_neg] at this
  linarith

variable {S T : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
  {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {f : S ⟶ T} {K : Divisor S}
  {Θ : RDivisor S}

/-- The strict transform on `S̄` of a prime divisor of `Y` meeting `Y_T` is the closure of a prime
divisor of `S`. -/
private theorem SurfaceModel.exists_primeDivisorMap_eq (M : SurfaceModel sS sT f K Θ)
    {Q : MMP.Mori.PrimeDivisor M.Y} {E : MMP.Mori.PrimeDivisor M.Sb}
    (hEQ : M.φ E.genericPoint = Q.genericPoint)
    (hQ : (Q.support ∩ (M.πY ⁻¹ᵁ M.ι.opensRange : Set M.Y)).Nonempty) :
    ∃ P : MMP.Mori.PrimeDivisor S, OpenWeilRestriction.primeDivisorMap M.j P = E := by
  have h1 : Q.genericPoint ∈ M.πY ⁻¹ᵁ M.ι.opensRange :=
    (MMP.Mori.PrimeDivisor.genericPoint_mem_iff Q _).mpr hQ
  have h2 : M.fb E.genericPoint ∈ Set.range M.ι := by
    rw [← M.hφπ, Scheme.Hom.comp_apply, hEQ]; exact h1
  obtain ⟨x, hx⟩ := mem_range_of_isPullback M.hpb h2
  exact (OpenWeilRestriction.mem_range_primeDivisorMap_iff M.j E).mpr ⟨x, hx⟩

/-- **Fixed parts along the smallest rational affine hull.** -/
private theorem SurfaceModel.exists_fixedPart_bound (M : SurfaceModel sS sT f K Θ) [IsAffine T]
    (hΘ : ∀ P, 0 ≤ Θ.coeff P) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r : ℕ, 0 < r ∧ ∀ Φ : RDivisor S, IsInSmallestRationalAffineHull Θ Φ →
      (∀ P, |Φ.coeff P - Θ.coeff P| < ε) →
      ∀ k : ℕ, 0 < k → ∀ D : Divisor S,
        (∀ P, (k : ℝ) / r * (DivisorWithCoeffs.coeff
          (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K) P + Φ.coeff P) = D.coeff P) →
        (∃ φ ∈ ((r : ℤ) • D).divisorialSubmodule ⊤, φ ≠ 0) ∧
          ∀ G : MMP.Mori.PrimeDivisor S, 0 < relativeFixedMultiplicity f ((r : ℤ) • D) G →
            IsInRelativeDivisorialStableBase f
              (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K + Θ) G := by
  classical
  haveI : IsIntegral M.Tb := M.hTb.1.toIsIntegral
  haveI : IsDominant M.φ := M.hφb.isDominant
  have hjb : IsBirationalMorphism M.j := isBirationalMorphism_of_isOpenImmersion M.j
  haveI : IsDominant M.j := hjb.isDominant
  have hinj := OpenWeilRestriction.primeDivisorMap_injective M.j
  obtain ⟨s, P, hPinj, hext⟩ := exists_coordinates M.j Θ
  set Pb : Fin s → MMP.Mori.PrimeDivisor M.Sb :=
    fun i => OpenWeilRestriction.primeDivisorMap M.j (P i) with hPbdef
  obtain ⟨Q, hQ, hQrat⟩ := M.exists_pullback_family Pb
  set Dfam : (Fin s → ℝ) → RDivisor M.Sb :=
    fun t => Divisor.toRDivisor M.Kb + ∑ i, t i • Finsupp.single (Pb i) (1 : ℝ) with hDfam
  set δ : Fin s → ℝ := fun i => Θ.coeff (P i)
  have hDδ : Dfam δ = Divisor.toRDivisor M.Kb + M.Θb := by
    simp only [hDfam, δ, Pb]
    rw [M.hΘb, hext Θ subset_rfl]
  have hQδ : Q δ = M.G := MMP.Flips.IsRCartierPullback.eq M.φ (hQ δ) (by
    change MMP.Flips.IsRCartierPullback M.φ (RationalMap.transformDivisor M.φ.toRationalMap
      (Dfam δ)) M.G
    rw [hDδ, M.transformDivisor_adjoint]
    exact M.hG)
  have hE₀δ : Dfam δ - Q δ = Divisor.toRDivisor M.Kb + M.Θb - M.G := by rw [hDδ, hQδ]
  have hzero : ∀ Φ : RDivisor S, IsInSmallestRationalAffineHull Θ Φ → ∀ Gb,
      (Divisor.toRDivisor M.Kb + M.Θb - M.G).coeff Gb = 0 →
      (Dfam (fun i => Φ.coeff (P i)) - Q (fun i => Φ.coeff (P i))).coeff Gb = 0 := by
    intro Φ hΦ Gb h0
    obtain ⟨c₀, c, hc⟩ := hQrat Gb
    have h1 : (c₀ : ℝ) + ∑ i, (c i : ℝ) * δ i = 0 := by rwa [← hc δ, hE₀δ]
    rw [hc]
    exact eq_zero_of_isInSmallestRationalAffineHull hPinj hΦ c₀ c h1
  have hevpos : ∀ᶠ t in nhds δ, ∀ Gb ∈ (Divisor.toRDivisor M.Kb + M.Θb - M.G).support,
      0 < (Dfam t - Q t).coeff Gb := by
    rw [Filter.eventually_all_finset]
    intro Gb hGb
    obtain ⟨c₀, c, hc⟩ := hQrat Gb
    have hpos : 0 < (Dfam δ - Q δ).coeff Gb := by
      rw [hE₀δ]
      exact lt_of_le_of_ne (M.hE Gb) (Ne.symm (Finsupp.mem_support_iff.mp hGb))
    have hcont : Continuous fun t : Fin s → ℝ => (c₀ : ℝ) + ∑ i, (c i : ℝ) * t i := by fun_prop
    rw [hc] at hpos
    filter_upwards [(hcont.tendsto δ).eventually (lt_mem_nhds hpos)] with t ht
    rwa [hc]
  obtain ⟨ε₂, hε₂, hball⟩ := Metric.eventually_nhds_iff.mp hevpos
  obtain ⟨H, hH, ⟨ε₁, hε₁, hcone⟩, -⟩ := M.exists_cone hΘ
  choose! pH hpH hpHfree using fun h (hh : h ∈ H) => (hH h hh).2
  set Yo : M.Y.Opens := M.πY ⁻¹ᵁ M.ι.opensRange with hYo
  set FT := (H.biUnion fun h => h.support).filter
    fun Q' : MMP.Mori.PrimeDivisor M.Y => (Q'.support ∩ (Yo : Set M.Y)).Nonempty with hFT
  set eF := FT.equivFin
  obtain ⟨b, hb, hcomb⟩ := exists_nsmul_eq_sum_of_mem_cone (ι := H)
    (fun h jj => h.1.coeff (eF.symm jj).1) (fun h => pH h.1) (fun h => hpH _ h.2)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, b, hb, fun Φ hΦ hclose k hk D hD => ?_⟩
  set t : Fin s → ℝ := fun i => Φ.coeff (P i)
  set Φb := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap M.j) Φ
  have hDt : Dfam t = Divisor.toRDivisor M.Kb + Φb := by
    simp only [hDfam, t, Pb]
    rw [hext Φ hΦ.1]
  have hdist : dist t δ < ε₂ := (dist_pi_lt_iff hε₂).mpr fun i => by
    rw [Real.dist_eq]; exact (hclose (P i)).trans_le (min_le_right _ _)
  have hEΦ0 : ∀ Gb, 0 ≤ (Dfam t - Q t).coeff Gb := fun Gb => by
    by_cases h : (Divisor.toRDivisor M.Kb + M.Θb - M.G).coeff Gb = 0
    · rw [hzero Φ hΦ Gb h]
    · exact (hball hdist Gb (Finsupp.mem_support_iff.mpr h)).le
  set ΦY := RationalMap.transformDivisor M.φ.toRationalMap Φb
  have hΦYhull : IsInSmallestRationalAffineHull M.ΘY ΦY := by
    rw [M.hΘY]
    exact M.isInSmallestRationalAffineHull_transform ((M.hhull Φb).mpr ⟨Φ, hΦ, rfl⟩)
  choose Est hEst1 hEst2 hEst3 using M.exists_strictTransform
  have hΦYclose : ∀ Q', |ΦY.coeff Q' - M.ΘY.coeff Q'| < ε₁ := fun Q' => by
    rw [M.hΘY, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, hEst3, hEst3, M.hΘb]
    by_cases hE' : Est Q' ∈ Set.range (OpenWeilRestriction.primeDivisorMap M.j)
    · obtain ⟨W, hW⟩ := hE'
      rw [← hW, Finsupp.mapDomain_apply_of_injective hinj, Finsupp.mapDomain_apply_of_injective hinj]
      exact (hclose W).trans_le (min_le_left _ _)
    · rw [Finsupp.mapDomain_notin_range _ _ hE', Finsupp.mapDomain_notin_range _ _ hE', sub_self,
        abs_zero]
      exact hε₁
  obtain ⟨tH, htH, hdec⟩ := hcone ΦY hΦYhull hΦYclose
  have htrans : RationalMap.transformDivisor M.φ.toRationalMap (Dfam t) =
      Divisor.toRDivisor M.KY + ΦY := by
    rw [hDt, map_add, transformDivisor_toRDivisor M.hY M.hφn M.hφb, ← M.hKYφ]
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hrD : ∀ P' : MMP.Mori.PrimeDivisor S,
      ((((b : ℤ) • D).coeff P' : ℤ) : ℝ) = k * (K.coeff P' + Φ.coeff P') := fun P' => by
    have h := hD P'
    rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    push_cast
    rw [← h]
    change (b : ℝ) * ((k : ℝ) / b * ((K.coeff P' : ℤ) + Φ.coeff P')) = _
    field_simp
  have hYcoeff : ∀ Q', (Q'.support ∩ (Yo : Set M.Y)).Nonempty →
      ∃ P' : MMP.Mori.PrimeDivisor S,
        (k : ℝ) * (Divisor.toRDivisor M.KY + ΦY).coeff Q' = ((((b : ℤ) • D).coeff P' : ℤ) : ℝ) ∧
        OpenWeilRestriction.primeDivisorMap M.j P' = Est Q' := fun Q' hQ' => by
    obtain ⟨P', hP'⟩ := M.exists_primeDivisorMap_eq (hEst1 Q') hQ'
    refine ⟨P', ?_, hP'⟩
    rw [← htrans, DivisorWithCoeffs.coeff_apply, hEst3, ← hP', hrD, ← DivisorWithCoeffs.coeff_apply,
      hDt, M.coeff_extend Φ P']
    rfl
  have hx : ∀ jj : Fin FT.card, ∃ x : ℤ,
      (k : ℝ) * (Divisor.toRDivisor M.KY + ΦY).coeff (eF.symm jj).1 = b * x := fun jj => by
    have hmem := (Finset.mem_filter.mp (eF.symm jj).2).2
    obtain ⟨P', hP', -⟩ := hYcoeff _ hmem
    refine ⟨D.coeff P', ?_⟩
    rw [hP', DivisorWithCoeffs.coeff_smul, smul_eq_mul]; push_cast; ring
  choose x hxdef using hx
  have hcoeffdec : ∀ Q', (Divisor.toRDivisor M.KY + ΦY).coeff Q' =
      ∑ h : H, tH h.1 * (h.1.coeff Q' : ℝ) := fun Q' => by
    rw [hdec, ← Finset.sum_coe_sort H]
    simp [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
    rfl
  obtain ⟨mH, hmH⟩ := hcomb x ⟨fun h => (k : ℝ) / b * tH h.1, fun h => by
    have := htH h.1; positivity, fun jj => by
      have h1 := hxdef jj
      rw [hcoeffdec] at h1
      have h2 : (x jj : ℝ) = (k : ℝ) / b * ∑ h : H, tH h.1 * (h.1.coeff (eF.symm jj).1 : ℝ) := by
        field_simp; linarith
      rw [h2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun h _ => by ring⟩
  set mH' : Divisor M.Y → ℕ := fun h => if hh : h ∈ H then mH ⟨h, hh⟩ else 0 with hmH'
  have hstar : ∀ Q', (Q'.support ∩ (Yo : Set M.Y)).Nonempty →
      (k : ℝ) * (Divisor.toRDivisor M.KY + ΦY).coeff Q' =
        ((∑ h ∈ H, ((mH' h : ℤ) * pH h) * h.coeff Q' : ℤ) : ℝ) := fun Q' hQ' => by
    have hsub : ∑ h ∈ H, ((mH' h : ℤ) * pH h) * h.coeff Q' =
        ∑ h : H, ((mH h : ℤ) * pH h.1) * h.1.coeff Q' := by
      rw [← Finset.sum_coe_sort H]
      refine Finset.sum_congr rfl fun h _ => ?_
      simp [hmH', h.2]
    rw [hsub]
    by_cases hQF : Q' ∈ FT
    · have h1 := hmH (eF ⟨Q', hQF⟩)
      have h2 := hxdef (eF ⟨Q', hQF⟩)
      simp only [Equiv.symm_apply_apply] at h1 h2
      rw [h2]
      exact_mod_cast h1.trans (Finset.sum_congr rfl fun h _ => by push_cast; ring)
    · have hz : ∀ h ∈ H, h.coeff Q' = 0 := fun h hh => by
        by_contra hne
        exact hQF (Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨h, hh,
          Finsupp.mem_support_iff.mpr hne⟩, hQ'⟩)
      rw [hcoeffdec]
      simp [hz _ (Subtype.prop _)]
  have hlocal : ∀ y : M.Y, y ∈ Yo → ∃ (U'' : M.Tb.Opens) (_ : M.πY y ∈ U'')
      (_ : U'' ≤ M.ι.opensRange) (ψ : (RationalFunctions M.Y)ˣ),
      (∀ Q' : MMP.Mori.PrimeDivisor M.Y, (Q'.support ∩ M.πY ⁻¹ᵁ U'').Nonempty →
        0 ≤ (k : ℝ) * (Divisor.toRDivisor M.KY + ΦY).coeff Q' + Q'.ord ψ) ∧
      ∀ Q' : MMP.Mori.PrimeDivisor M.Y, y ∈ Q'.support →
        (k : ℝ) * (Divisor.toRDivisor M.KY + ΦY).coeff Q' + Q'.ord ψ = 0 := by
    intro y hy
    obtain ⟨U', hU', ψ, h1, h2⟩ := exists_local_section M.πY H pH
      (fun h hh => ⟨(hH h hh).1, hpHfree h hh⟩) mH' y
    refine ⟨U' ⊓ M.ι.opensRange, ⟨hU', hy⟩, inf_le_right, ψ, fun Q' hQ' => ?_, fun Q' hQ' => ?_⟩
    · have hQo : (Q'.support ∩ (Yo : Set M.Y)).Nonempty :=
        hQ'.mono (Set.inter_subset_inter_right _ fun z hz => hz.2)
      rw [hstar Q' hQo]
      exact_mod_cast h1 Q' (hQ'.mono (Set.inter_subset_inter_right _ fun z hz => hz.1))
    · rw [hstar Q' ⟨y, hQ', hy⟩]
      exact_mod_cast h2 Q' hQ'
  have htoS : ∀ y : M.Y, y ∈ Yo → ∃ (U'' : M.Tb.Opens) (_ : M.πY y ∈ U'')
      (χ : (RationalFunctions S)ˣ),
      (∀ P' : MMP.Mori.PrimeDivisor S, (P'.support ∩ f ⁻¹ᵁ (M.ι ⁻¹ᵁ U'')).Nonempty →
        0 ≤ ((b : ℤ) • D).coeff P' + P'.ord χ) ∧
      ∀ G : MMP.Mori.PrimeDivisor S,
        M.φ (OpenWeilRestriction.primeDivisorMap M.j G).genericPoint = y →
        (Divisor.toRDivisor M.Kb + M.Θb - M.G).coeff
          (OpenWeilRestriction.primeDivisorMap M.j G) = 0 →
        ((b : ℤ) • D).coeff G + G.ord χ = 0 := by
    intro y hy
    obtain ⟨U'', hyU'', -, ψ, h1, h2⟩ := hlocal y hy
    have hBψ := map_componentGenericPoint_notMem_supp_of_isDominant M.φ (principalDivisor ψ)
    set ψb := pullbackRationalFunction M.φ ψ hBψ
    have hBψb := map_componentGenericPoint_notMem_supp_of_isDominant M.j (principalDivisor ψb)
    set χ := pullbackRationalFunction M.j ψb hBψb
    have hGL : MMP.Flips.IsRCartierPullback M.φ
        ((k : ℝ) • (Divisor.toRDivisor M.KY + ΦY) + Divisor.toRDivisor (principalDivisor ψ))
        ((k : ℝ) • Q t + Divisor.toRDivisor (principalDivisor ψb)) :=
      isRCartierPullback_add (isRCartierPullback_smul _ (htrans ▸ hQ t))
        (isRCartierPullback_toRDivisor (Divisor.isCartier_principalDivisor ψ) hBψ
          (Divisor.isPullback_principalDivisor ψ hBψ))
    have hLcoeff : ∀ Q' : MMP.Mori.PrimeDivisor M.Y,
        ((k : ℝ) • (Divisor.toRDivisor M.KY + ΦY) +
          Divisor.toRDivisor (principalDivisor ψ)).coeff Q' =
          (k : ℝ) * (Divisor.toRDivisor M.KY + ΦY).coeff Q' + Q'.ord ψ := fun Q' => by
      rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
        coeff_principalDivisor, smul_eq_mul]
    have hV : ∀ Q' : MMP.Mori.PrimeDivisor M.Y, (Q'.support ∩ M.πY ⁻¹ᵁ U'').Nonempty →
        0 ≤ ((k : ℝ) • (Divisor.toRDivisor M.KY + ΦY) +
          Divisor.toRDivisor (principalDivisor ψ)).coeff Q' := fun Q' hQ' => by
      rw [hLcoeff]; exact h1 Q' hQ'
    have hMS : ∀ P' : MMP.Mori.PrimeDivisor S,
        ((((b : ℤ) • D).coeff P' + P'.ord χ : ℤ) : ℝ) =
          ((k : ℝ) • Q t + Divisor.toRDivisor (principalDivisor ψb)).coeff
              (OpenWeilRestriction.primeDivisorMap M.j P') +
            k * (Dfam t - Q t).coeff (OpenWeilRestriction.primeDivisorMap M.j P') := by
      intro P'
      have h3 := M.coeff_extend Φ P'
      rw [← hDt] at h3
      push_cast
      rw [hrD, ord_pullbackRationalFunction_of_isOpenImmersion, DivisorWithCoeffs.coeff_add,
        DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, coeff_principalDivisor,
        DivisorWithCoeffs.coeff_sub, h3, smul_eq_mul]
      rw [DivisorWithCoeffs.coeff_add]
      have hKc : DivisorWithCoeffs.coeff (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K) P' =
          (K.coeff P' : ℝ) := rfl
      rw [hKc]
      ring
    refine ⟨U'', hyU'', χ, fun P' ⟨x, hxP, hxU⟩ => ?_, fun G hG0 hGE => ?_⟩
    · have hmeet : ((OpenWeilRestriction.primeDivisorMap M.j P').support ∩
          M.φ ⁻¹ᵁ (M.πY ⁻¹ᵁ U'')).Nonempty := by
        refine ⟨M.j x,
          (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff M.j P' x).mpr hxP, ?_⟩
        change M.πY (M.φ (M.j x)) ∈ U''
        rw [M.πY_φ_j]
        exact hxU
      have hGL0 := coeff_nonneg_of_isRCartierPullback_of_isEffectiveOn M.φ hGL hV _ hmeet
      have : (0 : ℝ) ≤ ((((b : ℤ) • D).coeff P' + P'.ord χ : ℤ) : ℝ) := by
        rw [hMS]
        have := hEΦ0 (OpenWeilRestriction.primeDivisorMap M.j P')
        positivity
      exact_mod_cast this
    · have hGL0 := coeff_eq_zero_of_isRCartierPullback M.φ hGL
        (OpenWeilRestriction.primeDivisorMap M.j G) (V := M.πY ⁻¹ᵁ U'')
        (by change M.πY (M.φ _) ∈ U''; rw [hG0]; exact hyU'') hV
        (fun Q' hQ' => by rw [hLcoeff]; rw [hG0] at hQ'; exact h2 Q' hQ')
      have hEΦ := hzero Φ hΦ _ hGE
      have : ((((b : ℤ) • D).coeff G + G.ord χ : ℤ) : ℝ) = 0 := by
        rw [hMS, hGL0, hEΦ, mul_zero, add_zero]
      exact_mod_cast this
  refine ⟨?_, fun G hG => ?_⟩
  · obtain ⟨x₀⟩ : Nonempty S := inferInstance
    have hy : M.φ (M.j x₀) ∈ Yo := by
      change M.πY (M.φ (M.j x₀)) ∈ M.ι.opensRange
      rw [M.πY_φ_j]
      exact ⟨_, rfl⟩
    obtain ⟨U'', hyU'', χ, hχ, -⟩ := htoS _ hy
    have hU : f x₀ ∈ M.ι ⁻¹ᵁ U'' := by
      change M.ι (f x₀) ∈ U''
      rwa [M.πY_φ_j] at hyU''
    exact exists_ne_zero_mem_divisorialSubmodule_top f ((b : ℤ) • D) hU χ hχ
  · set Gb := OpenWeilRestriction.primeDivisorMap M.j G
    by_cases hpos : 0 < (Divisor.toRDivisor M.Kb + M.Θb - M.G).coeff Gb
    · have hSB : IsInRelativeDivisorialStableBase M.fb (Divisor.toRDivisor M.Kb + M.Θb) Gb :=
        isInRelativeDivisorialStableBase_of_pos_transformDivisor (k := ℂ) M.hSb M.hY M.hSb
          (𝟙 M.Sb) M.φ M.fb M.πY (isBirationalMorphism_of_isIso _) M.hφb (Category.id_comp _)
          M.hφs (by rw [Category.id_comp, M.hφπ])
          (isRCartierPullback_id_of_isCartierCombination (isCartierCombination_of_isRCartier
            (IsQFactorial.isRCartier M.hSbQ _))) M.hG (by abel) M.transformDivisor_E Gb
          (by rw [transformDivisor_toRationalMap_id M.hSb]; exact hpos)
      rw [M.hΘb] at hSB
      exact (isInRelativeDivisorialStableBase_iff_of_isPullback M.hpb (M.coeff_extend Θ) G).mpr
        hSB
    · have h0 : (Divisor.toRDivisor M.Kb + M.Θb - M.G).coeff Gb = 0 :=
        le_antisymm (not_lt.mp hpos) (M.hE Gb)
      have hy : M.φ Gb.genericPoint ∈ Yo := by
        change M.πY (M.φ Gb.genericPoint) ∈ M.ι.opensRange
        rw [OpenWeilRestriction.genericPoint_primeDivisorMap, M.πY_φ_j]
        exact ⟨_, rfl⟩
      obtain ⟨U'', hyU'', χ, hχ, hχG⟩ := htoS _ hy
      have hU : f G.genericPoint ∈ M.ι ⁻¹ᵁ U'' := by
        change M.ι (f G.genericPoint) ∈ U''
        rwa [OpenWeilRestriction.genericPoint_primeDivisorMap, M.πY_φ_j] at hyU''
      have h1 := relativeFixedMultiplicity_eq_zero f ((b : ℤ) • D) G hU χ hχ (hχG G rfl h0)
      rw [h1] at hG
      exact absurd hG (lt_irrefl 0)

end FixedPartMain

/-! ### Finite generation of the floor-section algebra -/

section FiniteGenerationLemmas

/-- On an integral scheme, the value on a component of the rational function defined by an element
of the function field generizes back to that element. -/
private theorem componentToFunctionField_rationalFunctionsEquivFunctionField_symm
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (Z : irreducibleComponents X) (g : X.functionField) :
    (MMP.Positivity.componentToFunctionField Z).hom
      ((rationalFunctionsEquivFunctionField X).symm g Z) = g := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.germ_exist (x := genericPoint X) g
  have hZ : componentGenericPoint X Z ∈ U := by
    rwa [componentGenericPoint_eq_genericPoint Z]
  rw [rationalFunctionsEquivFunctionField_symm_germ U s hx Z hZ,
    TopCat.Presheaf.germ_stalkSpecializes_apply]

/-- On a normal integral scheme, a rational function `g` is a section of `𝒪_X(D)` over `U`
exactly when `ord_E g ≥ -d_E` for every prime divisor `E` meeting `U`. -/
private theorem mem_divisorialSubmodule_iff' {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (D : Divisor X) (U : X.Opens) (g : X.functionField) :
    (rationalFunctionsPresheaf X).map (homOfLE le_top : U ⟶ ⊤).op
        ((rationalFunctionsPresheafTopEquiv X).symm
          ((rationalFunctionsEquivFunctionField X).symm g))
        ∈ D.divisorialSubmodule U ↔
      ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ U).Nonempty →
        g = 0 ∨ -D.coeff E ≤ X.ord g E.genericPoint := by
  refine forall₂_congr fun E _ => ?_
  rw [rationalFunctionsPresheaf_map_apply]
  change E.OrdGE _ ((rationalFunctionsEquivFunctionField X).symm g E.component) ↔ _
  by_cases hg : g = 0
  · subst hg
    simp only [map_zero, true_or, iff_true]
    exact PrimeDivisor.OrdGE.zero _
  · have hz : (rationalFunctionsEquivFunctionField X).symm g E.component ≠ 0 := by
      intro h0
      apply hg
      rw [← componentToFunctionField_rationalFunctionsEquivFunctionField_symm E.component g, h0,
        map_zero]
    rw [MMP.Fourfold.PrimeDivisor.ordGE_iff_le_ord E hz,
      componentToFunctionField_rationalFunctionsEquivFunctionField_symm]
    simp [hg]

/-- A positive multiple of a `ℚ`-divisor is integral. -/
private theorem exists_pos_nsmul_eq_toQDivisor {X : Scheme.{0}} (B : QDivisor X) :
    ∃ (N : ℕ) (W : Divisor X), 0 < N ∧ Divisor.toQDivisor W = (N : ℚ) • B := by
  classical
  set N : ℕ := ∏ P ∈ B.support, (B P).den with hN
  have hden : ∀ P, (B P).den ∣ N := fun P => by
    by_cases hP : P ∈ B.support
    · exact Finset.dvd_prod_of_mem _ hP
    · rw [Finsupp.notMem_support_iff.mp hP]; exact one_dvd _
  refine ⟨N, Finsupp.onFinset B.support (fun P => ((N / (B P).den : ℕ) : ℤ) * (B P).num)
    (fun P hP => by
      by_contra h
      rw [Finsupp.notMem_support_iff.mp h] at hP
      simp at hP), Finset.prod_pos fun P _ => (B P).den_pos, ?_⟩
  ext P
  have hd : ((B P).den : ℚ) ≠ 0 := by exact_mod_cast (B P).den_pos.ne'
  have hc : ((N / (B P).den : ℕ) : ℚ) * (B P).num = (N : ℚ) * B P := by
    rw [Nat.cast_div (hden P) hd, div_mul_eq_mul_div, mul_div_assoc, Rat.num_div_den]
  change ((((N / (B P).den : ℕ) : ℤ) * (B P).num : ℤ) : ℚ) = (N : ℚ) * B P
  push_cast
  exact hc

/-- On an integral scheme, rational functions over a nonempty open `U`: the function field is
identified with `𝒦_X(U)` by restriction from `X`. -/
private noncomputable def rationalFunctionsEquivOpens (X : Scheme.{0}) [IsIntegral X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) :
    X.functionField ≃+* (rationalFunctionsPresheaf X).obj (op U) :=
  RingEquiv.ofBijective
    (((rationalFunctionsPresheaf X).map (homOfLE le_top : U ⟶ ⊤).op).hom.comp
      ((rationalFunctionsPresheafTopEquiv X).symm.toRingHom.comp
        (rationalFunctionsEquivFunctionField X).symm.toRingHom)) (by
    obtain ⟨x, hx⟩ := hU
    have hmem : ∀ Z : irreducibleComponents X, componentGenericPoint X Z ∈ U := fun Z =>
      (MMP.Mori.genericPoint_mem_iff Z U).mpr
        ⟨x, hx, Fourfold.mem_irreducibleComponent_of_irreducibleSpace Z x⟩
    have hres : Function.Bijective ((rationalFunctionsPresheaf X).map
        (homOfLE le_top : U ⟶ ⊤).op) := by
      refine ⟨fun s t h => funext fun Z => ?_, fun t => ⟨fun Z => t ⟨Z.1, hmem Z.1⟩, ?_⟩⟩
      · exact congrFun h ⟨Z.1, hmem Z.1⟩
      · funext Z; rfl
    exact hres.comp ((rationalFunctionsPresheafTopEquiv X).symm.bijective.comp
      (rationalFunctionsEquivFunctionField X).symm.bijective))

private theorem rationalFunctionsEquivOpens_apply (X : Scheme.{0}) [IsIntegral X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) (g : X.functionField) :
    rationalFunctionsEquivOpens X U hU g = (rationalFunctionsPresheaf X).map
      (homOfLE le_top : U ⟶ ⊤).op ((rationalFunctionsPresheafTopEquiv X).symm
        ((rationalFunctionsEquivFunctionField X).symm g)) := rfl

/-- The section of `𝒦_X` defined by a regular function is its germ at the generic point. -/
private theorem rationalFunctionsEquivOpens_germ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) (s : Γ(X, U)) (h : genericPoint X ∈ U) :
    rationalFunctionsEquivOpens X U hU (X.presheaf.germ U (genericPoint X) h s) =
      algebraMap Γ(X, U) _ s := by
  funext Z
  rw [rationalFunctionsEquivOpens_apply, rationalFunctionsPresheaf_map_apply]
  exact rationalFunctionsEquivFunctionField_symm_germ U s h Z.1 Z.2

/-- `⌊m(K + Θ)⌋ = mK + ⌊mΘ⌋` for an integral divisor `K`. -/
private theorem roundDown_smul_add {X : Scheme.{0}} (K : Divisor X) (Θ : QDivisor X) (m : ℕ) :
    DivisorWithCoeffs.roundDown ((m : ℚ) • (Divisor.toQDivisor K + Θ)) =
      m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Θ) := by
  ext P
  simp only [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, smul_eq_mul, nsmul_eq_mul]
  rw [mul_add, show (m : ℚ) * (K.coeff P : ℚ) = ((m * K.coeff P : ℤ) : ℚ) by push_cast; ring,
    Int.floor_intCast_add]

/-- The pieces of the canonical ring are those of the floor-section algebra of `K + Θ`. -/
private theorem canonicalRingPiece_eq {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {s : X ⟶ Spec (.of ℂ)} {K : Divisor X} (hK : K.IsCanonicalDivisor s 2) (Θ : QDivisor X)
    (m : ℕ) : K.canonicalRingPiece s hK Θ m =
      (DivisorWithCoeffs.roundDown ((m : ℚ) • (Divisor.toQDivisor K + Θ))).divisorialSubmodule
        ⊤ := by
  rw [roundDown_smul_add]; rfl

/-- The canonical ring is closed under the ring operations. -/
private theorem closure_le_canonicalRing {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {s : X ⟶ Spec (.of ℂ)} {K : Divisor X} (hK : K.IsCanonicalDivisor s 2) (Θ : QDivisor X)
    (A : Set (Polynomial ((rationalFunctionsPresheaf X).obj (op ⊤))))
    (hA : A ⊆ (K.canonicalRing s hK Θ :
      Set (Polynomial ((rationalFunctionsPresheaf X).obj (op ⊤))))) :
    (Subring.closure A : Set _) ⊆ (K.canonicalRing s hK Θ :
      Set (Polynomial ((rationalFunctionsPresheaf X).obj (op ⊤)))) := by
  intro p hp
  set D := Divisor.toQDivisor K + Θ
  have hmem : ∀ q : Polynomial ((rationalFunctionsPresheaf X).obj (op ⊤)),
      q ∈ K.canonicalRing s hK Θ ↔ ∀ m : ℕ,
        q.coeff m ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • D)).divisorialSubmodule ⊤ :=
    fun q => forall_congr' fun m => by rw [canonicalRingPiece_eq]
  have hsup : ∀ a b : ℕ, DivisorWithCoeffs.roundDown ((a : ℚ) • D) +
      DivisorWithCoeffs.roundDown ((b : ℚ) • D) ≤
        DivisorWithCoeffs.roundDown (((a + b : ℕ) : ℚ) • D) := fun a b P => by
    change (DivisorWithCoeffs.roundDown ((a : ℚ) • D)).coeff P +
      (DivisorWithCoeffs.roundDown ((b : ℚ) • D)).coeff P ≤
        (DivisorWithCoeffs.roundDown (((a + b : ℕ) : ℚ) • D)).coeff P
    simp only [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, Nat.cast_add,
      add_smul]
    exact Int.le_floor_add _ _
  rw [SetLike.mem_coe, hmem]
  induction hp using Subring.closure_induction with
  | mem q hq => exact (hmem q).mp (hA hq)
  | zero => intro m; simp
  | one =>
    intro m
    rw [Polynomial.coeff_one]
    split_ifs with h
    · subst h
      have h0 : DivisorWithCoeffs.roundDown (((0 : ℕ) : ℚ) • D) = 0 :=
        DivisorWithCoeffs.ext' fun P => by simp
      rw [h0]
      exact Divisor.IsDivisorialSection.one le_rfl ⊤
    · exact Submodule.zero_mem _
  | add q r _ _ hq hr =>
    intro m; rw [Polynomial.coeff_add]; exact Submodule.add_mem _ (hq m) (hr m)
  | neg q _ hq => intro m; rw [Polynomial.coeff_neg]; exact Submodule.neg_mem _ (hq m)
  | mul q r _ _ hq hr =>
    intro m
    rw [Polynomial.coeff_mul]
    refine Submodule.sum_mem _ fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    refine Divisor.divisorialSubmodule_mono ?_ ⊤
      (Divisor.divisorialMul ⊤ ⟨_, hq x.1⟩ ⟨_, hr x.2⟩).2
    rw [← hx]
    exact hsup x.1 x.2

end FiniteGenerationLemmas

section FiniteGenerationMain

variable {S T : Scheme.{0}} [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
  {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {f : S ⟶ T} {K : Divisor S}
  {Θ : RDivisor S}

/-- `d + 2 ≤ 2` in `WithBot ℕ∞` forces `d < 1`. -/
private theorem lt_one_of_add_two_le_two {d : WithBot ℕ∞} (h : d + 2 ≤ 2) : d < 1 := by
  induction d using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    rw [← WithBot.coe_ofNat, ← WithBot.coe_add, WithBot.coe_le_coe] at h
    rw [← WithBot.coe_one, WithBot.coe_lt_coe]
    induction e using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe n =>
      have : n + 2 ≤ 2 := by exact_mod_cast h
      exact_mod_cast (by omega : n < 1)

/-- `d + 1 = 2` in `WithBot ℕ∞` forces `d = 1`. -/
private theorem eq_one_of_add_one_eq_two {d : WithBot ℕ∞} (h : d + 1 = 2) : d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by decide)
  | coe e =>
    rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_ofNat, WithBot.coe_inj] at h
    rw [← WithBot.coe_one, WithBot.coe_inj]
    induction e using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe n =>
      have : n + 1 = 2 := by exact_mod_cast h
      exact_mod_cast (by omega : n = 1)

/-- The comparison divisor is exceptional for the contraction to the model: its support consists of
curves contracted to points. -/
private theorem SurfaceModel.isExceptionalDivisorFor (M : SurfaceModel sS sT f K Θ)
    {E : QDivisor M.Sb} (hE : QDivisor.toRDivisor E = Divisor.toRDivisor M.Kb + M.Θb - M.G) :
    MMP.Resolution.IsExceptionalDivisorFor M.φ E := by
  intro P hP
  have hne : (Divisor.toRDivisor M.Kb + M.Θb - M.G).coeff P ≠ 0 := by
    rw [← hE, QDivisor.coeff_toRDivisor]
    exact_mod_cast Finsupp.mem_support_iff.mp hP
  obtain ⟨hYn, hfb', hp', hexc⟩ := M.hEexc P hne
  haveI : LocallyOfFiniteType M.sY := M.hY.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType M.sSb := M.hSb.1.toLocallyOfFiniteType
  have hYd : topologicalKrullDim M.Y = (2 : ℕ) := by
    rw [← topologicalKrullDim_eq_of_isBirationalMorphism M.sSb M.sY M.hφb]; exact M.hSbd
  have hP1 : topologicalKrullDim (P.support : Set M.Sb) = 1 := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight M.sSb P.genericPoint
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, M.hSbd,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
    exact eq_one_of_add_one_eq_two (by exact_mod_cast h)
  have hPc : IsClosed (P.support : Set M.Sb) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  have hcl : closure (M.φ.base '' P.support) = M.φ.base '' P.support :=
    (M.φ.isClosedMap _ hPc).closure_eq
  unfold MMP.Flips.ProperDivisorOver.IsExceptional at hexc
  rw [MMP.Flips.ProperDivisorOver.coe_center, hYd] at hexc
  rw [hcl, hP1]
  exact lt_one_of_add_two_le_two (by exact_mod_cast hexc)

/-- **Finite generation of the floor-section algebra** of `K_S + Θ` over the affine `T`, for
rational `Θ`. -/
private theorem SurfaceModel.exists_canonicalRing_eq_closure (M : SurfaceModel sS sT f K Θ) [IsAffine T]
    (hT : IsNormalVariety ℂ sT) (hfb : IsBirationalMorphism f) (hΘ : ∀ P, 0 ≤ Θ.coeff P)
    (hK : K.IsCanonicalDivisor sS 2) (Θq : QDivisor S) (hΘq : QDivisor.toRDivisor Θq = Θ) :
    ∃ G : Finset (Polynomial ((rationalFunctionsPresheaf S).obj (op ⊤))),
      (K.canonicalRing sS hK Θq : Set (Polynomial ((rationalFunctionsPresheaf S).obj (op ⊤)))) =
        Subring.closure (Set.range (relativeConstantsMap f) ∪ ↑G) := by
  classical
  haveI : IsIntegral M.Tb := M.hTb.1.toIsIntegral
  haveI : IsIntegral T := hT.1.toIsIntegral
  haveI : IsDominant M.φ := M.hφb.isDominant
  have hjb : IsBirationalMorphism M.j := isBirationalMorphism_of_isOpenImmersion M.j
  haveI : IsDominant M.j := hjb.isDominant
  haveI : IsDominant f := hfb.isDominant
  have hιb : IsBirationalMorphism M.ι := isBirationalMorphism_of_isOpenImmersion M.ι
  haveI : IsDominant M.ι := hιb.isDominant
  have hπb : IsBirationalMorphism M.πY := isBirationalMorphism_of_comp M.hφb (M.hφπ ▸ M.hfbb)
  haveI : IsDominant M.πY := hπb.isDominant
  haveI : IsDominant M.fb := M.hfbb.isDominant
  haveI : IsSeparated M.sTb := M.hTbp.toIsVariety.toIsSeparated
  have hinj := OpenWeilRestriction.primeDivisorMap_injective M.j
  obtain ⟨⟨Bq, hBq⟩, Eq, hEq⟩ := M.hrat ⟨Θq, hΘq⟩
  obtain ⟨-, -, -, b, hb, hbfree⟩ := M.exists_cone hΘ
  obtain ⟨N, W, hN, hW⟩ := exists_pos_nsmul_eq_toQDivisor Bq
  obtain ⟨m, hm, hmc⟩ := M.hYQ.2 ((N : ℤ) • M.KY + W)
  set DY : QDivisor M.Y := Divisor.toQDivisor M.KY + Bq with hDYdef
  set D₁ : Divisor M.Y := (m : ℤ) • ((N : ℤ) • M.KY + W) with hD₁
  have hcoeffD₁ : ∀ P, (D₁.coeff P : ℚ) = ((m * N : ℕ) : ℚ) * DY.coeff P := fun P => by
    have := congrArg (fun D : QDivisor M.Y => D.coeff P) hW
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at this
    simp only [hD₁, hDYdef, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, smul_eq_mul,
      Divisor.coeff_toQDivisor]
    push_cast
    rw [this]
    ring
  have hcD : ((m * N : ℕ) : ℝ) • (Divisor.toRDivisor M.KY + M.ΘY) = Divisor.toRDivisor D₁ := by
    ext P
    have h := congrArg (Rat.cast : ℚ → ℝ) (hcoeffD₁ P)
    rw [← hBq]
    simp only [hDYdef, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor] at h
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
      QDivisor.coeff_toRDivisor, smul_eq_mul]
    push_cast at h ⊢
    linarith
  have hfree := hbfree _ (by positivity) D₁ hmc hcD
  set q : ℕ := b * (m * N) with hqdef
  have hq : 0 < q := by positivity
  set B : Divisor M.Y := (b : ℤ) • D₁ with hBdef
  have hB : ∀ P, (B.coeff P : ℚ) = (q : ℚ) * DY.coeff P := fun P => by
    rw [hBdef, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    push_cast
    rw [hcoeffD₁ P, hqdef]
    push_cast
    ring
  set W₀ : M.Tb.Opens := M.ι ''ᵁ ⊤ with hW₀def
  have hW₀ : IsAffineOpen W₀ := (isAffineOpen_top T).image_of_isOpenImmersion M.ι
  have hπp : IsProjective M.πY := IsProjective.of_comp M.πY M.sTb (by
    rw [M.hπs]; exact ((isProjectiveVariety_iff_isProjective' ℂ M.sY).mp M.hYp).2)
  obtain ⟨GY, hGY, hGYgen⟩ := fg_roundDownSections_of_isRelativelyFreeDivisor M.sY M.sTb M.hY
    M.hTb M.πY hπp M.hπs hq B hB (hmc.zsmul _) hfree W₀ hW₀
  have hBQ : Divisor.toQDivisor B = (q : ℤ) • DY := by
    ext P
    rw [Divisor.coeff_toQDivisor, hB P, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul]
    push_cast; rfl
  have hBc : B.IsCartier := hmc.zsmul _
  have hDYq : DY.IsQCartier := ⟨q, by exact_mod_cast hq.ne', B, hBQ, hBc⟩
  set Θbq : QDivisor M.Sb := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap M.j) Θq
    with hΘbq
  set DX : QDivisor M.Sb := Divisor.toQDivisor M.Kb + Θbq with hDXdef
  have hDXq : DX.IsQCartier := by
    obtain ⟨N', W', hN', hW'⟩ := exists_pos_nsmul_eq_toQDivisor DX
    obtain ⟨m', hm', hm'c⟩ := M.hSbQ.2 W'
    refine ⟨(m' * N' : ℕ), by positivity, (m' : ℤ) • W', ?_, hm'c⟩
    ext P
    have := congrArg (fun D : QDivisor M.Sb => D.coeff P) hW'
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at this ⊢
    push_cast
    rw [this, zsmul_eq_mul]
    push_cast
    ring
  have hBY : ∀ Z : irreducibleComponents M.Sb,
      M.φ (componentGenericPoint M.Sb Z) ∉ DY.supp := by
    intro Z
    rw [← QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hq.ne') hBQ]
    exact map_componentGenericPoint_notMem_supp_of_isDominant M.φ B Z
  have hE0 : 0 ≤ Eq := Finsupp.le_def.mpr fun P => by
    have := M.hE P
    rw [← hEq, QDivisor.coeff_toRDivisor] at this
    exact_mod_cast this
  have hEx := M.isExceptionalDivisorFor hEq
  have htoRQ : ∀ {X : Scheme.{0}} (D : Divisor X),
      QDivisor.toRDivisor (Divisor.toQDivisor D) = Divisor.toRDivisor D := fun D => by
    ext P; simp
  have hpull : QDivisor.toRDivisor (DY.pullback hDYq hBY) = M.G := by
    obtain ⟨D', hD', hD'p⟩ := QDivisor.isPullback_pullback hDYq hBY q hq B hBQ hBc
    have h1 := MMP.Flips.isRCartierPullback_of_zsmul_eq M.φ (D := DY) hq hBc
      (by rw [hBQ]) ⟨_, hD'p⟩
    have hDYR : QDivisor.toRDivisor DY = Divisor.toRDivisor M.KY + M.ΘY := by
      rw [hDYdef, map_add, htoRQ, hBq]
    rw [hDYR] at h1
    have h2 := MMP.Flips.IsRCartierPullback.eq M.φ h1 M.hG
    rw [← h2]
    ext P
    have h3 := congrArg (fun D : QDivisor M.Sb => D.coeff P) hD'
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h3
    simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      smul_eq_mul]
    have h4 := congrArg (Rat.cast : ℚ → ℝ) h3
    push_cast at h4
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
    linarith
  have hΘbR : QDivisor.toRDivisor Θbq = M.Θb := by
    rw [M.hΘb, hΘbq, toRDivisor_mapDomain_primeDivisorMap, hΘq]
  have hD : DX = DY.pullback hDYq hBY + Eq := by
    apply MMP.Mori.QDivisor.toRDivisor_injective
    rw [hDXdef, map_add, map_add, hpull, hEq, htoRQ, hΘbR]
    abel
  have hfloor := fun n g => mem_divisorialSubmodule_roundDown_iff_of_eq_pullback_add M.sSb M.sY
    M.hSb M.hY M.φ M.hφb M.hφs M.fb M.πY M.hφπ DX DY hDXq hDYq hBY Eq hE0 hEx hD W₀ n g
  obtain ⟨x₀⟩ : Nonempty S := inferInstance
  have hfbW : ∀ x : S, M.fb (M.j x) ∈ W₀ := fun x => by rw [M.fb_j]; exact ⟨f x, trivial, rfl⟩
  have hUY : ((M.πY ⁻¹ᵁ W₀ : M.Y.Opens) : Set M.Y).Nonempty := ⟨M.φ (M.j x₀), by
    change M.πY (M.φ (M.j x₀)) ∈ W₀
    rw [← Scheme.Hom.comp_apply, M.hφπ]; exact hfbW x₀⟩
  have hUX : ((M.fb ⁻¹ᵁ W₀ : M.Sb.Opens) : Set M.Sb).Nonempty := ⟨M.j x₀, hfbW x₀⟩
  set ρY := rationalFunctionsEquivOpens M.Y (M.πY ⁻¹ᵁ W₀) hUY with hρY
  set ρX := rationalFunctionsEquivOpens M.Sb (M.fb ⁻¹ᵁ W₀) hUX with hρX
  set ρS := rationalFunctionsEquivOpens S ⊤ ⟨x₀, trivial⟩ with hρS
  set eφ : M.Y.functionField ≃+* M.Sb.functionField :=
    RingEquiv.ofBijective (functionFieldMap M.φ) M.hφb.functionFieldMap_bijective
  set ej : M.Sb.functionField ≃+* S.functionField :=
    RingEquiv.ofBijective (functionFieldMap M.j) hjb.functionFieldMap_bijective
  set Ψ₀ := ρY.symm.trans (eφ.trans (ej.trans ρS)) with hΨ₀def
  have hΨ₀ : ∀ g, Ψ₀ (ρY g) = ρS (functionFieldMap M.j (functionFieldMap M.φ g)) := fun g => by
    simp only [hΨ₀def, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
    rfl
  have hcoeff : ∀ (n : ℕ) (P : MMP.Mori.PrimeDivisor S),
      (DivisorWithCoeffs.roundDown ((n : ℚ) • DX)).coeff
          (OpenWeilRestriction.primeDivisorMap M.j P) =
        (DivisorWithCoeffs.roundDown ((n : ℚ) • (Divisor.toQDivisor K + Θq))).coeff P := by
    intro n P
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_roundDown,
      DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul, hDXdef,
      DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor,
      Divisor.coeff_toQDivisor, M.hKbj, hΘbq,
      show DivisorWithCoeffs.coeff (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap M.j) Θq)
        (OpenWeilRestriction.primeDivisorMap M.j P) = Θq.coeff P from
        Finsupp.mapDomain_apply_of_injective hinj Θq P]
  have hext : ∀ (n : ℕ) (h : M.Sb.functionField),
      ρX h ∈ (DivisorWithCoeffs.roundDown ((n : ℚ) • DX)).divisorialSubmodule (M.fb ⁻¹ᵁ W₀) ↔
        ρS (functionFieldMap M.j h) ∈ K.canonicalRingPiece sS hK Θq n := by
    intro n h
    have hρX' : ρX h = (rationalFunctionsPresheaf M.Sb).map (homOfLE le_top : M.fb ⁻¹ᵁ W₀ ⟶ ⊤).op
        ((rationalFunctionsPresheafTopEquiv M.Sb).symm
          ((rationalFunctionsEquivFunctionField M.Sb).symm h)) := rfl
    have hρS' : ρS (functionFieldMap M.j h) = (rationalFunctionsPresheaf S).map
        (homOfLE le_top : (⊤ : S.Opens) ⟶ ⊤).op ((rationalFunctionsPresheafTopEquiv S).symm
          ((rationalFunctionsEquivFunctionField S).symm (functionFieldMap M.j h))) := rfl
    rw [canonicalRingPiece_eq, hρX', hρS', mem_divisorialSubmodule_iff',
      mem_divisorialSubmodule_iff']
    have hord : ∀ P : MMP.Mori.PrimeDivisor S,
        S.ord (functionFieldMap M.j h) P.genericPoint =
          M.Sb.ord h (OpenWeilRestriction.primeDivisorMap M.j P).genericPoint := fun P =>
      MMP.Positivity.ord_functionFieldMap_of_isIso M.j P _
        (OpenWeilRestriction.genericPoint_primeDivisorMap M.j P).symm h
    have hzero : functionFieldMap M.j h = 0 ↔ h = 0 :=
      map_eq_zero_iff _ (functionFieldMap M.j).injective
    constructor
    · intro H P _
      have hP : ((OpenWeilRestriction.primeDivisorMap M.j P).support ∩
          (M.fb ⁻¹ᵁ W₀ : Set M.Sb)).Nonempty := by
        refine ⟨M.j P.genericPoint, ?_, hfbW _⟩
        rw [MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff,
          AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      exact (H _ hP).imp hzero.mpr fun hle => by rwa [hord, ← hcoeff]
    · rintro H E ⟨y, hyE, hyU⟩
      obtain ⟨t, -, ht⟩ := hyU
      obtain ⟨x, rfl⟩ := mem_range_of_isPullback M.hpb ⟨t, ht⟩
      obtain ⟨P, rfl⟩ :=
        MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support M.j E x hyE
      exact (H P ⟨x, (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff
        M.j P x).mp hyE, trivial⟩).imp hzero.mp fun hle => by rwa [hcoeff, ← hord]
  have hsec : ∀ (n : ℕ) (c : (rationalFunctionsPresheaf M.Y).obj (op (M.πY ⁻¹ᵁ W₀))),
      c ∈ (DivisorWithCoeffs.roundDown ((n : ℚ) • DY)).divisorialSubmodule (M.πY ⁻¹ᵁ W₀) ↔
        Ψ₀ c ∈ K.canonicalRingPiece sS hK Θq n := by
    intro n c
    obtain ⟨g, rfl⟩ := ρY.surjective c
    rw [hΨ₀, ← hext]
    exact hfloor n g
  have hconst : ∀ a : Γ(M.Tb, W₀), Polynomial.mapEquiv Ψ₀ (Polynomial.C
      (algebraMap Γ(M.Y, M.πY ⁻¹ᵁ W₀) _ (M.πY.app W₀ a))) ∈ Set.range (relativeConstantsMap f) := by
    intro a
    have hle : (⊤ : T.Opens) ≤ M.ι ⁻¹ᵁ W₀ := fun x _ => ⟨x, trivial, rfl⟩
    refine ⟨T.presheaf.map (homOfLE hle).op (M.ι.app W₀ a), ?_⟩
    rw [Polynomial.mapEquiv_apply, Polynomial.map_C]
    change Polynomial.C (((toRationalFunctionsPresheaf S).app (op ⊤)).hom
        (f.appTop.hom (T.presheaf.map (homOfLE hle).op (M.ι.app W₀ a)))) =
      Polynomial.C (Ψ₀ (algebraMap Γ(M.Y, M.πY ⁻¹ᵁ W₀) _ (M.πY.app W₀ a)))
    congr 1
    symm
    have hgTb : genericPoint M.Tb ∈ W₀ := by
      rw [← map_genericPoint_of_isDominant M.ι]; exact ⟨_, trivial, rfl⟩
    have hgY : genericPoint M.Y ∈ M.πY ⁻¹ᵁ W₀ := by
      change M.πY (genericPoint M.Y) ∈ W₀; rw [map_genericPoint_of_isDominant]; exact hgTb
    have hgT : genericPoint T ∈ M.ι ⁻¹ᵁ W₀ := hle trivial
    have hgS : genericPoint S ∈ f ⁻¹ᵁ (⊤ : T.Opens) := trivial
    have h1 : algebraMap Γ(M.Y, M.πY ⁻¹ᵁ W₀) _ (M.πY.app W₀ a) =
        ρY (functionFieldMap M.πY (M.Tb.presheaf.germ W₀ _ hgTb a)) := by
      rw [functionFieldMap_germ M.πY W₀ hgTb hgY a, hρY, rationalFunctionsEquivOpens_germ]
    rw [h1, hΨ₀, Oai4C1.functionFieldMap_comp_apply M.φ M.πY M.hφπ,
      Oai4C1.functionFieldMap_comp_apply M.j M.fb M.hpb.w,
      ← Oai4C1.functionFieldMap_comp_apply f M.ι rfl, functionFieldMap_germ M.ι W₀ hgTb hgT a,
      ← TopCat.Presheaf.germ_res_apply T.presheaf (homOfLE hle) _ trivial,
      functionFieldMap_germ f ⊤ trivial hgS]
    exact rationalFunctionsEquivOpens_germ S ⊤ _ _ trivial
  refine ⟨GY.image (Polynomial.mapEquiv Ψ₀), le_antisymm (fun p hp => ?_) ?_⟩
  · have hp' : ∀ n : ℕ, ((Polynomial.mapEquiv Ψ₀).symm p).coeff n ∈
        (DivisorWithCoeffs.roundDown ((n : ℚ) • DY)).divisorialSubmodule (M.πY ⁻¹ᵁ W₀) := by
      intro n
      rw [hsec, Polynomial.mapEquiv_symm_apply, Polynomial.coeff_map]
      simpa using hp n
    have h1 := hGYgen _ hp'
    have h2 : p ∈ (Subring.closure ((Set.range fun a : Γ(M.Tb, W₀) => Polynomial.C
        (algebraMap Γ(M.Y, M.πY ⁻¹ᵁ W₀) _ (M.πY.app W₀ a))) ∪ ↑GY)).map
          (Polynomial.mapEquiv Ψ₀).toRingHom :=
      ⟨_, h1, (Polynomial.mapEquiv Ψ₀).apply_symm_apply p⟩
    rw [RingHom.map_closure] at h2
    refine Subring.closure_mono ?_ h2
    rintro _ ⟨x, hx | hx, rfl⟩
    · obtain ⟨a, rfl⟩ := hx
      exact Or.inl (hconst a)
    · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))
  · refine closure_le_canonicalRing hK Θq _ ?_
    rintro _ (⟨a, rfl⟩ | hp)
    · intro n
      change (Polynomial.C (algebraMap Γ(S, ⊤) _ (f.appTop a))).coeff n ∈ _
      rw [Polynomial.coeff_C]
      split_ifs with hn
      · subst hn
        rw [canonicalRingPiece_eq]
        have h0 : DivisorWithCoeffs.roundDown (((0 : ℕ) : ℚ) • (Divisor.toQDivisor K + Θq)) = 0 :=
          DivisorWithCoeffs.ext' fun P => by simp
        rw [h0]
        exact Divisor.isDivisorialSection_algebraMap le_rfl _
      · exact Submodule.zero_mem _
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hp
      intro n
      rw [Polynomial.mapEquiv_apply, Polynomial.coeff_map]
      exact (hsec n _).mp (hGY g hg n)

end FiniteGenerationMain

end MMP.Fold06.ThmMmpSurfaceBirationalPropertyF2

namespace MMP.Fourfold

/-- **The birational finite-generation property holds for surfaces.** For a normal
`ℚ`-factorial complex surface projective and birational over a normal affine variety, with an
effective real klt boundary, the three assertions of `BirationalFiniteGenerationProperty` hold:
finite generation for rational boundaries, persistence of the divisorial stable base primes, and
the uniform fixed-part clause along the smallest rational affine hull. -/
@[mmp "thm_mmp_surface_birational_property_f2"]
public theorem birationalFiniteGenerationProperty_two : BirationalFiniteGenerationProperty 2 := by
  refine ⟨by norm_num, ?_⟩
  intro S _ _ _ _ sS T sT f hSQ hSd hT hTa hfs hfp hfb Θ hΘ hΘk K hK
  obtain ⟨M⟩ := MMP.Fold06.ThmMmpSurfaceBirationalPropertyF2.nonempty_surfaceModel hSQ hSd hT hfs
    hfp hfb hΘ hΘk hK
  obtain ⟨ε, hε, hpers⟩ := M.exists_isInRelativeDivisorialStableBase_of_close hΘ
  obtain ⟨ε', hε', r, hr, hfix⟩ := M.exists_fixedPart_bound hΘ
  exact ⟨M.exists_canonicalRing_eq_closure hT hfb hΘ hK,
    ⟨ε, hε, fun Θ' hsub _ _ hclose => hpers Θ' hsub hclose⟩,
    ⟨ε', hε', r, hr, fun Φ hΦ _ _ hclose k hk D _ hD => hfix Φ hΦ hclose k hk D hD⟩⟩

end MMP.Fourfold
