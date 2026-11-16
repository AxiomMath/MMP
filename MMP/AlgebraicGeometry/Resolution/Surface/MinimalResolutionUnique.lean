module

public import MMP.AlgebraicGeometry.Resolution.JacobianDivisorExceptional
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Blowup.PointBlowupSequence
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Resolution.OrderReduction.EmptyEntriesInert
import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialPart
import MMP.AlgebraicGeometry.Resolution.SncPairStratumBlowup

/-!
# The Jacobian divisor of a surface resolution, and uniqueness of minimal resolutions

Let `g : S ⟶ X` be a projective birational morphism from a normal surface `S` to a smooth variety
`X` over a field `k`, such that every prime divisor of `S` meets the smooth locus, and let `ω ≠ 0`
be a rational top form on `X`. The support of the effective `g`-exceptional divisor
`div_S(g^*ω) - g^* div_X(ω)` is exactly the union of the `g`-exceptional curves: a curve
contracted by `g` cannot have coefficient zero, since at a smooth point where the Jacobian is a
unit `g` would be unramified, hence quasi-finite, near the curve.

From this we deduce that a quasi-projective surface `Y` has at most one minimal resolution up to
unique isomorphism over `Y`. Given two minimal resolutions `f₁ : X₁ ⟶ Y`, `f₂ : X₂ ⟶ Y`, let `S`
be the normalization of the closure of the graph of `X₁ ⇢ X₂`, with `gᵢ : S ⟶ Xᵢ`. Pulling one
rational `2`-form of `Y` back to `S`, `X₁` and `X₂`, the difference of the two Jacobian divisors
is `B'₂ - B'₁`; the negativity lemma and minimality of `f₂` show that every `g₁`-exceptional
curve is `g₂`-exceptional, and symmetrically. Since no curve is exceptional for both, `g₁` and
`g₂` are isomorphisms. Uniqueness holds because two `Y`-morphisms `X₁ ⟶ X₂` agree on the dense
open over which `f₂` is an open immersion, `X₁` being reduced and `X₂` separated over `Y`.

## Main results

* `MMP.Resolution.supp_divisorOfFormOnSmoothLocus_sub_pullback_eq_iUnion`: the support of the
  Jacobian divisor is the exceptional locus.
* `MMP.Resolution.existsUnique_iso_comp_eq_of_isMinimalSurfaceResolution`: two minimal
  resolutions of a quasi-projective surface are isomorphic over the base by a unique isomorphism.

## Implementation notes

As in `MMP.Resolution.isEffective_and_isExceptional_divisorOfFormOnSmoothLocus_sub_pullback`,
`S` is a `k`-scheme through `g ≫ s_X`, and the pull-back `g^* div_X(ω)` is any divisor `B'`
satisfying the characterising predicate `MMP.Mori.Divisor.IsPullback`. A `g`-exceptional curve
is a proper curve `C` of `S` with `MMP.Resolution.IsContractedProjectiveCurve`; its underlying set
is the closure of its generic point `C.point`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Theorem 2.16 and its proof][kollar2007]
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori Topology TopologicalSpace

universe u

namespace MMP.Resolution

/-! ### The support of the Jacobian divisor -/

/-- A field essentially of finite type and formally smooth over `k` has `dim Ω_{K/k} = trdeg`. -/
private theorem finrank_kaehlerDifferential_of_formallySmooth (k K : Type*) [Field k] [Field K]
    [Algebra k K] [Algebra.EssFiniteType k K] [Algebra.FormallySmooth k K] :
    Module.finrank K Ω[K⁄k] = (Algebra.trdeg k K).toNat := by
  have h := trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k K
  have h2 := h.2.2
  rw [Module.finrank_zero_of_subsingleton (M := Algebra.H1Cotangent k K), Nat.cast_zero,
    sub_zero] at h2
  exact_mod_cast h2.symm

/-- If `⋀ b = c • σ` for a basis `b` of `M`, then `c` is a unit with inverse the determinant of
`σ` against `b`. -/
private theorem mul_det_eq_one_of_ιMulti_eq_smul {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] {n : ℕ} (b : Module.Basis (Fin n) A M) {σ : ⋀[A]^n M} {c : A}
    (hb : exteriorPower.ιMulti A n b = c • σ) :
    c * exteriorPower.alternatingMapLinearEquiv b.det σ = 1 := by
  have h := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) hb
  rwa [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Module.Basis.det_self, map_smul,
    smul_eq_mul, eq_comm] at h

open KaehlerDifferential in
/-- **Invertible top Jacobian.** If `A → B` is an algebra over `k` with `Ω_{A/k}` and `Ω_{B/k}`
free of rank `n`, with top-form generators `σA`, `σB` and `⋀ⁿ(A → B) σA = J σB` for a unit `J`,
then `Ω_{B/A} = 0`. -/
private theorem subsingleton_kaehler_of_topFormsMap_eq_smul {k A B : Type*} [CommRing k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    {n : ℕ} (bA : Module.Basis (Fin n) A Ω[A⁄k]) (bB : Module.Basis (Fin n) B Ω[B⁄k])
    {σA : ⋀[A]^n Ω[A⁄k]} (hσA : Submodule.span A {σA} = ⊤)
    {σB : ⋀[B]^n Ω[B⁄k]} (hσB : Submodule.span B {σB} = ⊤) {J : B} (hJ : IsUnit J)
    (hrel : MMP.Mori.topFormsMap k A B n σA = J • σB) : Subsingleton Ω[B⁄A] := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hσA ▸ Submodule.mem_top :
    exteriorPower.ιMulti A n bA ∈ Submodule.span A {σA})
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hσB ▸ Submodule.mem_top :
    exteriorPower.ιMulti B n bB ∈ Submodule.span B {σB})
  set v : Fin n → Ω[B⁄k] := fun i => KaehlerDifferential.map k k A B (bA i)
  have hvσ : exteriorPower.ιMulti B n v = (algebraMap A B a * J) • σB := by
    have h1 := congrArg (MMP.Mori.topFormsMap k A B n) ha
    rwa [MMP.Mori.topFormsMap_ιMulti, map_smul, hrel, ← algebraMap_smul B a, smul_smul,
      eq_comm] at h1
  have hdet : IsUnit (bB.det v) := by
    rw [← exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, hvσ, map_smul, smul_eq_mul]
    exact (((IsUnit.of_mul_eq_one _ (mul_det_eq_one_of_ιMulti_eq_smul bA ha.symm)).map _).mul
      hJ).mul (IsUnit.of_mul_eq_one_right _ (mul_det_eq_one_of_ιMulti_eq_smul bB hc.symm))
  have hzero : map k A B B = 0 :=
    LinearMap.ext_on_range (bB.is_basis_iff_det.mpr hdet).2 fun i => by
      simpa using (exact_mapBaseChange_map k A B).apply_apply_eq_zero (1 ⊗ₜ bA i)
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := map_surjective k A B x
  obtain ⟨y, rfl⟩ := map_surjective k A B y
  simp [hzero]

section Jacobian

variable {k : Type u} [Field k] {X S : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (g : S ⟶ X)

/-- At the generic point of a prime divisor in the smooth locus of a variety of dimension `n`,
`Ω_{𝒪_{S,P}/k}` is free of rank `n`. -/
private theorem nonempty_basis_kaehler_of_mem_smoothLocus {sS : S ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sS] [IsLocallyNoetherian S] [IsNormal S]
    {n : ℕ} (hn : topologicalKrullDim S = n) (P : MMP.Mori.PrimeDivisor S)
    (hP : P.genericPoint ∈ smoothLocus sS) :
    letI := stalkAlgebra sS P.genericPoint
    Nonempty (Module.Basis (Fin n) P.localRing Ω[P.localRing⁄k]) := by
  let := stalkAlgebra sS P.genericPoint
  let := functionFieldAlgebra sS
  have := isScalarTower_stalk_functionField sS P.genericPoint
  have : LocallyOfFiniteType sS := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : Algebra.FormallySmooth k P.localRing :=
    (MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus_iff P).mp hP
  have : Algebra.EssFiniteType k P.localRing := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ P.genericPoint) isOpen_univ
    have hU' : IsAffineOpen U := hU
    let x : U := ⟨P.genericPoint, hxU⟩
    let := sectionAlgebra sS U
    have := finiteType_sectionAlgebra sS hU'
    let : Algebra Γ(S, U) P.localRing := TopCat.Presheaf.algebra_section_stalk S.presheaf x
    have := isScalarTower_section_stalk sS U x
    have := hU'.isLocalization_stalk x
    have : Algebra.EssFiniteType Γ(S, U) P.localRing :=
      .of_isLocalization _ (hU'.primeIdealOf x).asIdeal.primeCompl
    exact .comp k Γ(S, U) P.localRing
  have := P.isDiscreteValuationRing_localRing
  have : Module.Free P.localRing Ω[P.localRing⁄k] := Module.free_of_flat_of_isLocalRing
  have : Algebra.FormallySmooth P.localRing S.functionField :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors P.localRing)
  have : Algebra.FormallySmooth k S.functionField := .comp k P.localRing S.functionField
  have := essFiniteType_functionField (sX := sS)
  have hK : Module.finrank S.functionField Ω[S.functionField⁄k] = n :=
    (finrank_kaehlerDifferential_of_formallySmooth k S.functionField).trans
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hn)
  exact ⟨Module.finBasisOfFinrankEq _ _
    ((finrank_kaehlerDifferential_eq_of_isFractionRing (K := S.functionField)).symm.trans hK)⟩

/-- An element `J` of the local ring along a prime divisor `P` whose image in the function field
is nonzero and has order zero along `P` is a unit. -/
private theorem isUnit_of_ord_algebraMap_eq_zero [IsIntegral S] [IsLocallyNoetherian S]
    (P : MMP.Mori.PrimeDivisor S) {J : P.localRing}
    (hJ0 : algebraMap P.localRing S.functionField J ≠ 0)
    (h : S.ord (algebraMap P.localRing S.functionField J) P.genericPoint = 0) : IsUnit J := by
  have hz := P.coheight_genericPoint
  rw [Scheme.ord_eq_iff hz hJ0, ofAdd_zero] at h
  have hJ : J ≠ 0 := fun h => hJ0 (by rw [h, map_zero])
  have : Ring.KrullDimLE 1 P.localRing := krullDimLE_of_coheight_le hz.le
  change Ring.ordFrac P.localRing (algebraMap P.localRing S.functionField J) = 1 at h
  rw [Ring.ordFrac_eq_ord _ hJ,
    Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero hJ)] at h
  apply MMP.Intersection.isUnit_of_ord_eq_zero
  cases h' : Ring.ord P.localRing J with
  | top => simp [h'] at h
  | coe m => simpa [h', ← WithZero.coe_one, WithZero.coe_inj] using h

/-- If the coefficient of a prime divisor `P` meeting the smooth locus in
`div_S(g^*ω) - g^* div_X(ω)` vanishes, the Jacobian is a unit at the generic point of `P`, so
`Ω_{𝒪_{S,P}/𝒪_{X,g(P)}} = 0`. -/
private theorem subsingleton_kaehler_stalkMap_of_coeff_eq_zero
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k (g ≫ sX)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian S] [CompactSpace X] [CompactSpace S]
    [IsNormal S] [IsNormal X]
    [IsDominant g] (hg : IsBirationalMorphism g)
    (hX : IsSmoothScheme sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    (ω : RationalPluriForms sX n 1) (hω : ω ≠ 0)
    (hB : ∀ Z : irreducibleComponents S,
      g (componentGenericPoint S Z) ∉ (divisorOfForm ω).supp)
    (B' : Divisor S) (hB' : (divisorOfForm ω).IsPullback g hB B')
    (P : MMP.Mori.PrimeDivisor S) (hP : P.genericPoint ∈ smoothLocus (g ≫ sX))
    (h0 : P.ordForm (pullbackRationalPluriForms sX g ω) - B'.coeff P = 0) :
    letI := (g.stalkMap P.genericPoint).hom.toAlgebra
    Subsingleton Ω[P.localRing⁄X.presheaf.stalk (g P.genericPoint)] := by
  have : LocallyOfFiniteType sX := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : Smooth sX := (isSmoothScheme_iff sX).mp hX
  let := stalkAlgebra sX (g P.genericPoint)
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX (g P.genericPoint)
  let := stalkAlgebra (g ≫ sX) P.genericPoint
  let := functionFieldAlgebra (g ≫ sX)
  have := isScalarTower_stalk_functionField (g ≫ sX) P.genericPoint
  let := (g.stalkMap P.genericPoint).hom.toAlgebra
  have := MMP.Threefold.Resolution.isScalarTower_stalkMap sX g P.genericPoint
  obtain ⟨σA, hσA, h0A⟩ :=
    MMP.Threefold.Resolution.exists_topForms_generator_stalk sX hn (g P.genericPoint)
  have hnS : topologicalKrullDim S = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hg).symm.trans hn
  obtain ⟨σB, hσB, h0B⟩ := exists_topForms_generator_of_mem_smoothLocus (sS := g ≫ sX) hnS P hP
  obtain ⟨J, hJ⟩ := Submodule.mem_span_singleton.mp
    (hσB ▸ Submodule.mem_top :
      topFormsMap k (X.presheaf.stalk (g P.genericPoint)) P.localRing n σA ∈
        Submodule.span P.localRing {σB})
  have hJ0 := algebraMap_ne_zero_of_topFormsMap_eq_smul sX g hg P h0A hJ.symm
  have hJu : IsUnit J := isUnit_of_ord_algebraMap_eq_zero P hJ0 <| by
    rw [← h0, MMP.Threefold.Resolution.ordForm_pullbackRationalPluriForms_eq sX g P hσA h0A hσB
      h0B J hJ.symm hJ0 hω, coeff_eq_ord_formCoeff_of_isPullback sX g hX ω hω hB B' hB' P hσA h0A]
    ring
  obtain ⟨n', ⟨bA⟩, hn'⟩ :=
    MMP.Threefold.Resolution.exists_basis_kaehler_stalk sX (g P.genericPoint)
  obtain rfl : n' = n := by
    have := (AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX
      (g P.genericPoint)).trans hn'
    rw [hn] at this
    exact_mod_cast this.symm
  obtain ⟨bB⟩ := nonempty_basis_kaehler_of_mem_smoothLocus (sS := g ≫ sX) hnS P hP
  exact subsingleton_kaehler_of_topFormsMap_eq_smul bA bB hσA hσB hJu hJ.symm

open Stacks.RelativeDifferentialStalkMap in
/-- A point `η` whose closure is contracted by `g` and is not closed does not have
`Ω_{𝒪_{S,η}/𝒪_{X,g(η)}} = 0`. -/
private theorem not_subsingleton_kaehler_stalkMap [LocallyOfFiniteType g] (η : S)
    (hcont : ∀ y ∈ closure ({η} : Set S), g y = g η)
    (hnc : ¬ IsClosed ({η} : Set S)) :
    ¬ (letI := (g.stalkMap η).hom.toAlgebra
      Subsingleton Ω[S.presheaf.stalk η⁄X.presheaf.stalk (g η)]) := by
  intro h
  classical
  have hsub : Subsingleton (Stacks.SmoothAtJacobian.relativeDifferentialStalk g η) := by
    let iG : Algebra (ToType (X.presheaf.stalk (g η))) (ToType (S.sheaf.presheaf.stalk η)) :=
      algebraStalkMap g η
    have : Subsingleton Ω[ToType (S.sheaf.presheaf.stalk η)⁄ToType (X.presheaf.stalk (g η))] := h
    exact (relativeDifferentialsStalkKaehlerEquiv g η).toEquiv.subsingleton
  have hq := (quasiFiniteAt_of_unramifiedAt g
    (unramifiedAt_of_subsingleton_relativeDifferentialStalk g hsub)).2
  have hcl := hq.isClopen_singleton_asFiber.isClosed
  have hcl' : IsClosed ({⟨η, rfl⟩} : Set (g ⁻¹' {g η})) := by
    have := (g.fiberHomeo (g η)).isClosed_image.mpr hcl
    rwa [Set.image_singleton, show g.fiberHomeo (g η) (g.asFiber η) = ⟨η, rfl⟩ from
      (g.fiberHomeo (g η)).apply_symm_apply _] at this
  refine hnc ?_
  rw [← closure_subset_iff_isClosed]
  intro y hy
  have hyT : g y = g η := hcont y hy
  have h1 : (⟨y, hyT⟩ : g ⁻¹' {g η}) ∈ closure ({⟨η, rfl⟩} : Set (g ⁻¹' {g η})) := by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.image_singleton]
    exact hy
  rw [hcl'.closure_eq] at h1
  exact congrArg Subtype.val h1

/-- The closure of the generic point of a proper curve has dimension one. -/
private theorem topologicalKrullDim_closure_point {sS : S ⟶ Spec (.of k)} (C : ProperCurve sS) :
    topologicalKrullDim (closure ({C.point} : Set S)) = 1 := by
  rw [← C.dim_eq]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    (C.ι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (range_curveSubschemeAtι C.point))).isHomeomorph).symm

/-- The generic point of a proper curve is not closed. -/
private theorem not_isClosed_singleton_point {sS : S ⟶ Spec (.of k)} (C : ProperCurve sS) :
    ¬ IsClosed ({C.point} : Set S) := fun hcl => by
  have h : topologicalKrullDim ({C.point} : Set S) ≤ 0 :=
    @topologicalKrullDim_zero_of_discreteTopology _ _
      (@Subsingleton.discreteTopology _ _ (Set.subsingleton_singleton (a := C.point)).coe_sort)
  rw [← hcl.closure_eq, topologicalKrullDim_closure_point] at h
  exact absurd h (by decide)

/-- The generic point of a proper curve on an integral surface is not the generic point of the
surface. -/
private theorem point_ne_genericPoint {sS : S ⟶ Spec (.of k)} [IsIntegral S]
    (hS : topologicalKrullDim S = 2) (C : ProperCurve sS) : C.point ≠ genericPoint S := by
  intro h
  have h1 := topologicalKrullDim_closure_point C
  rw [h, (genericPoint_spec S).def, (Homeomorph.Set.univ S).isHomeomorph.topologicalKrullDim_eq,
    hS] at h1
  exact absurd h1 (by decide)

/-- On an integral surface, a point which is neither closed nor the generic point has coheight
one, so is the generic point of a prime divisor. -/
private theorem coheight_eq_one_of_not_isClosed [IsIntegral S]
    (hS : topologicalKrullDim S = 2) {a : S} (hgen : a ≠ genericPoint S)
    (hna : ¬ IsClosed ({a} : Set S)) : Order.coheight a = 1 := by
  let : PartialOrder S := specializationOrder S
  have hlt : a < genericPoint S :=
    lt_of_le_of_ne ((genericPoint_spec S).specializes (Set.mem_univ a)) hgen
  obtain ⟨z, hza, hzne⟩ : ∃ z ∈ closure ({a} : Set S), z ≠ a := by
    by_contra! hcon
    exact hna (closure_subset_iff_isClosed.mp fun z hz => hcon z hz)
  have hzlt : z < a := lt_of_le_of_ne (specializes_iff_mem_closure.mpr hza) hzne
  have h1 : ((Order.height a + Order.coheight a : ℕ∞) : WithBot ℕ∞) ≤ 2 := by
    rw [← hS, ← Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim,
      Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun b : S => Order.height b + Order.coheight b) a)
  have h2 : 1 ≤ Order.height a := le_trans (by simp) (Order.height_add_one_le hzlt)
  refine le_antisymm ?_ (le_trans (by simp) (Order.coheight_add_one_le hlt))
  exact (ENat.add_le_add_iff_left ENat.one_ne_top).mp
    ((add_le_add_left h2 _).trans (WithBot.coe_le_coe.mp h1) : 1 + Order.coheight a ≤ 1 + 1)

end Jacobian

/-- A contracted projective curve lies in a prime divisor with nonzero coefficient in the
Jacobian divisor `div_S(g^*ω) - B'`. -/
private theorem exists_coeff_ne_zero_of_isContractedProjectiveCurve
    {k : Type u} [Field k] {X S : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (g : S ⟶ X)
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k (g ≫ sX)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian S] [CompactSpace X] [CompactSpace S]
    [IsNormal S] [IsNormal X]
    [IsDominant g] (hg : IsBirationalMorphism g)
    (hX : IsSmoothScheme sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    (hS : topologicalKrullDim S = 2)
    (hsm : ∀ P : AlgebraicGeometry.PrimeDivisor S,
      (P.support ∩ (smoothLocus (g ≫ sX) : Set S)).Nonempty)
    (ω : RationalPluriForms sX n 1) (hω : ω ≠ 0)
    (hB : ∀ Z : irreducibleComponents S,
      g (componentGenericPoint S Z) ∉ (divisorOfForm ω).supp)
    (B' : Divisor S) (hB' : (divisorOfForm ω).IsPullback g hB B')
    (C : ProperCurve (g ≫ sX)) (hC : IsContractedProjectiveCurve (g ≫ sX) g C) :
    ∃ E, (divisorOfFormOnSmoothLocus (pullbackRationalPluriForms sX g ω) - B').coeff E ≠ 0 ∧
      C.point ∈ E.support := by
  have hsl : ∀ P : MMP.Mori.PrimeDivisor S, P.genericPoint ∈ smoothLocus (g ≫ sX) := by
    intro P
    obtain ⟨x, hxP, hx⟩ := hsm P
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxP
    exact (specializes_iff_mem_closure.mpr hxP).mem_open (smoothLocus (g ≫ sX)).isOpen hx
  have hfil : MMP.Resolution.divisorOfFormOnSmoothLocus (pullbackRationalPluriForms sX g ω) =
      divisorOfForm (pullbackRationalPluriForms sX g ω) := by
    classical
    unfold MMP.Resolution.divisorOfFormOnSmoothLocus
    convert (Finsupp.filter_eq_self_iff _ _).mpr fun P _ => hsm P
  have hc : ∀ P : MMP.Mori.PrimeDivisor S,
      (divisorOfForm (pullbackRationalPluriForms sX g ω) - B').coeff P =
        P.ordForm (pullbackRationalPluriForms sX g ω) - B'.coeff P := fun P => by
    rw [DivisorWithCoeffs.coeff_sub, coeff_divisorOfForm]
  have hgen := point_ne_genericPoint hS C
  have hnc := not_isClosed_singleton_point C
  have hcoh := coheight_eq_one_of_not_isClosed hS hgen hnc
  set E : MMP.Mori.PrimeDivisor S := AlgebraicGeometry.PrimeDivisor.ofCoheightOne C.point hcoh
  have hEg : E.genericPoint = C.point :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh
  have : LocallyOfFiniteType (g ≫ sX) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g sX
  refine ⟨E, fun hzero => ?_, ?_⟩
  · rw [hfil, hc] at hzero
    have hsub := subsingleton_kaehler_stalkMap_of_coeff_eq_zero sX g hg hX hn ω hω hB B' hB' E
      (hsl E) hzero
    refine not_subsingleton_kaehler_stalkMap g E.genericPoint ?_ (by rwa [hEg]) hsub
    rw [hEg]
    exact hC.2
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    change C.point ∈ closure {E.genericPoint}
    rw [hEg]
    exact subset_closure rfl

/-- **Support of the Jacobian divisor.** In the setting of
`MMP.Resolution.isEffective_and_isExceptional_divisorOfFormOnSmoothLocus_sub_pullback`, assume
moreover that `S` is a surface and `g` is projective. Then the support of
`div_S(g^*ω) - B'`, where `B'` is the pull-back of `div_X(ω)`, is the union of all `g`-exceptional
curves of `S`. -/
@[mmp "lem_kr2a_jacobian_divisor_support_is_exceptional_locus"]
public theorem supp_divisorOfFormOnSmoothLocus_sub_pullback_eq_iUnion
    {k : Type u} [Field k] {X S : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (g : S ⟶ X)
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k (g ≫ sX)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian S] [CompactSpace X] [CompactSpace S]
    [IsNormal S] [IsNormal X]
    [IsProper g] [IsDominant g] (hg : IsBirationalMorphism g) (hgp : IsProjectiveMorphism g)
    (hX : IsSmoothScheme sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    (hS : topologicalKrullDim S = 2)
    (hsm : ∀ P : AlgebraicGeometry.PrimeDivisor S,
      (P.support ∩ (smoothLocus (g ≫ sX) : Set S)).Nonempty)
    (ω : RationalPluriForms sX n 1) (hω : ω ≠ 0)
    (hB : ∀ Z : irreducibleComponents S,
      g (componentGenericPoint S Z) ∉ (divisorOfForm ω).supp)
    (B' : Divisor S) (hB' : (divisorOfForm ω).IsPullback g hB B') :
    ((divisorOfFormOnSmoothLocus (pullbackRationalPluriForms sX g ω) - B').supp : Set S) =
      ⋃ (C : ProperCurve (g ≫ sX)) (_ : IsContractedProjectiveCurve (g ≫ sX) g C),
        closure {C.point} := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    obtain ⟨C, hCE, hC⟩ := exists_isContractedProjectiveCurve_of_isExceptional (sS := g ≫ sX)
      ‹_› hS ‹_› g rfl hgp E
      ((isEffective_and_isExceptional_divisorOfFormOnSmoothLocus_sub_pullback
        sX g hg hX hn hsm ω hω hB B' hB').2 E (Finsupp.mem_support_iff.mpr hE))
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← hCE] at hxE
    exact Set.mem_iUnion₂.mpr ⟨C, hC, hxE⟩
  · intro x hx
    obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨E, hE, hCE⟩ := exists_coeff_ne_zero_of_isContractedProjectiveCurve sX g hg hX hn
      hS hsm ω hω hB B' hB' C hC
    exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hE,
      closure_minimal (Set.singleton_subset_iff.mpr hCE) E.idealSheaf.support.isClosed hxC⟩

/-! ### Uniqueness of the minimal resolution -/

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- Dimension count: `a + 1 = d` and `b + c = d` with `c ≥ 2` and `d` finite and nonempty
force `b < a`. -/
private theorem lt_of_add_one_eq_of_add_eq {a b d : WithBot ℕ∞} {c : ℕ∞} (h1 : a + 1 = d)
    (h2 : b + c = d) (hc : 2 ≤ c) (hd : d ≠ ⊤) (hd' : d ≠ ⊥) : b < a := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl hd'
  | coe d =>
  induction d using ENat.recTopCoe with
  | top => exact absurd rfl hd
  | coe d =>
  induction a using WithBot.recBotCoe with
  | bot => simp at h1
  | coe a =>
  induction b using WithBot.recBotCoe with
  | bot => simp at h2
  | coe b =>
  rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_inj] at h1
  rw [← WithBot.coe_add, WithBot.coe_inj] at h2
  rw [WithBot.coe_lt_coe]
  induction a using ENat.recTopCoe with
  | top => simp at h1
  | coe a =>
  induction b using ENat.recTopCoe with
  | top => simp at h2
  | coe b =>
  induction c using ENat.recTopCoe with
  | top => simp at h2
  | coe c =>
  norm_cast at h1 h2 hc ⊢
  omega

/-- If a prime divisor `P` of `S` is not `g`-exceptional, its generic point is a smooth point of
`S`. -/
private theorem genericPoint_mem_smoothLocus_of_not_lt {k : Type u} [Field k] {X S : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (g : S ⟶ X)
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k (g ≫ sX)]
    [IsIntegral X] [IsIntegral S] [IsNormal X] [IsProper g] [IsLocallyNoetherian S]
    [CompactSpace X] (hg : IsBirationalMorphism g) (hX : IsSmoothScheme sX)
    (P : MMP.Mori.PrimeDivisor S)
    (hP : ¬ topologicalKrullDim (closure (g.base '' P.support)) <
      topologicalKrullDim P.support) :
    P.genericPoint ∈ smoothLocus (g ≫ sX) := by
  obtain ⟨W, hW, hiso⟩ :=
    MMP.Resolution.exists_two_le_closedsCodimension_compl_isIso_morphismRestrict (k := k)
      (sX := sX) ⟨inferInstance, inferInstance⟩ g inferInstance hg
  have hη : g P.genericPoint ∈ W := by
    by_contra hξ
    have h2 : 2 ≤ Order.coheight (g P.genericPoint) :=
      (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hW) _ hξ
    apply hP
    have hcl : closure (g.base '' P.support) = closure {g P.genericPoint} := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        closure_image_closure g.base.hom.continuous, Set.image_singleton]
    rw [hcl, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have : LocallyOfFiniteType sX := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
    have : LocallyOfFiniteType (g ≫ sX) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
    have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
    have hS := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (g ≫ sX)
      P.genericPoint
    have hX' := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
      (g P.genericPoint)
    have hd := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hg
    rw [P.coheight_genericPoint] at hS
    refine lt_of_add_one_eq_of_add_eq (hS.trans hd.symm) hX' h2
      (topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX)
      (Order.krullDim_ne_bot_iff.mpr
        ⟨⟨closure {g P.genericPoint}, isIrreducible_singleton.closure, isClosed_closure⟩⟩)
  have hsm : Smooth sX := (isSmoothScheme_iff sX).mp hX
  have : IsIso (g ∣_ W) := hiso
  have hs : Smooth ((g ⁻¹ᵁ W).ι ≫ g ≫ sX) := by
    rw [← Category.assoc, ← morphismRestrict_ι g W, Category.assoc]
    infer_instance
  exact mem_smoothLocus_iff.mpr ⟨g ⁻¹ᵁ W, hη, hs⟩

/-- The intersection number of an invertible sheaf with a projective curve is its degree
along the curve. -/
private theorem lineBundleCurveIntersection_eq_degreeOn {k : Type u} [Field k] {S : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} [QuasiCompact sS] (L : S.Modules)
    [hL : Stacks.Ample.IsInvertibleModule S L] (C : ProperCurve sS)
    (hC : IsProjectiveMorphism (C.ι ≫ sS)) :
    lineBundleCurveIntersection L C = MMP.Mori.degreeOn k sS C.ι C.dim_le L := by
  have : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L := hL
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
      ((Scheme.Modules.pullback C.ι).obj L) :=
    MMP.Mori.isInvertible_pullback_obj C.ι _
  unfold lineBundleCurveIntersection
  rw [MMP.Resolution.degree_eq_invertibleCurveDegree (C.ι ≫ sS) _ C.dim_le,
    ← MMP.Mori.degreeOn_eq_invertibleCurveDegree]

/-- **Degree of a pulled-back Cartier divisor on a curve.** Let `g : S ⟶ X` be a morphism of normal
varieties, `B` a Cartier divisor on `X` with pull-back `B'`, and `C ⊆ S` a projective curve. If `C`
is contracted by `g` then `(B' · C) = 0`; otherwise `(B' · C) = r (B · Γ)` for the projective curve
`Γ = g(C)` and a natural number `r`. -/
private theorem degreeOn_pullback {k : Type u} [Field k] {S X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k)) (g : S ⟶ X) (hs : g ≫ sX = sS)
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sS]
    [IsNormal S] [IsNormal X] [IsLocallyNoetherian S] [IsLocallyNoetherian X] [CompactSpace S]
    [CompactSpace X] [IsIntegral S]
    (B : Divisor X) (hBc : B.IsCartier)
    (hB : ∀ Z : irreducibleComponents S, g (componentGenericPoint S Z) ∉ B.supp)
    (B' : Divisor S) (hB' : B.IsPullback g hB B') (hB'c : B'.IsCartier)
    (C : ProperCurve sS) (hC : IsProjectiveMorphism (C.ι ≫ sS)) :
    (C.IsContractedBy g → B'.degreeOn k sS C.ι C.dim_le hB'c = 0) ∧
    (¬ C.IsContractedBy g → Stacks.HProjective.IsQuasiProjective sX →
      ∃ Γ : ProperCurve sX, Γ.point = g C.point ∧
        closure ({Γ.point} : Set X) = g '' closure ({C.point} : Set S) ∧
        IsProjectiveMorphism (Γ.ι ≫ sX) ∧
        ∃ r : ℕ, B'.degreeOn k sS C.ι C.dim_le hB'c =
          (r : ℤ) * B.degreeOn k sX Γ.ι Γ.dim_le hBc) := by
  subst hs
  have : QuasiCompact sX := AlgebraicGeometry.IsVariety.toQuasiCompact
  have : QuasiCompact (g ≫ sX) := AlgebraicGeometry.IsVariety.toQuasiCompact
  have : LocallyOfFiniteType sX := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g ≫ sX) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have hinv := hBc.isInvertibleModule_divisorialSheaf
  have hinv' := hB'c.isInvertibleModule_divisorialSheaf
  have e := hB'.divisorialSheafIso (hBc := hBc)
  have hdeg : B'.degreeOn k (g ≫ sX) C.ι C.dim_le hB'c =
      lineBundleCurveIntersection ((Scheme.Modules.pullback g).obj B.divisorialSheaf) C := by
    have : Stacks.Ample.IsInvertibleModule S ((Scheme.Modules.pullback g).obj B.divisorialSheaf) :=
      MMP.Mori.isInvertible_pullback_obj g _
    rw [lineBundleCurveIntersection_eq_degreeOn _ C hC]
    unfold Divisor.degreeOn
    exact MMP.Mori.degreeOn_eq_of_iso k (g ≫ sX) C.ι C.dim_le e
  obtain ⟨h1, h2⟩ := MMP.Resolution.lineBundleCurveIntersection_pullback (sX' := g ≫ sX) g rfl
    B.divisorialSheaf C hC
  refine ⟨fun hc => hdeg.trans (h1 hc), fun hnc hqp => ?_⟩
  obtain ⟨hΓ, hcl, hΓp, -, hval⟩ := h2 hnc hqp
  refine ⟨⟨g C.point, hΓ⟩, rfl, hcl, hΓp, residueFieldDegree g C.point, ?_⟩
  rw [hdeg, hval, lineBundleCurveIntersection_eq_degreeOn _ (⟨g C.point, hΓ⟩ : ProperCurve sX) hΓp]
  rfl

/-- On a smooth variety, an `f`-nef Cartier divisor `K` has nonnegative degree on every projective
`f`-contracted curve, computed with the Cartier Weil divisor `B` of `K`. -/
private theorem degreeOn_nonneg_of_isNef {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (f : X ⟶ Y) [IsIntegral X] [IsNoetherian X]
    [hsm : IsSmoothVariety k (f ≫ sY)] [IsNormal X]
    (K : X.CartierDivisor)
    (hnef : IsNefOnContractedCurves (f ≫ sY) f (KCartierDivisor.ofCartier ℝ K))
    (B : Divisor X) (hBK : ∀ P : AlgebraicGeometry.PrimeDivisor X, (cartierWeilDivisor K).1 P = B P)
    (hBc : B.IsCartier) (Γ : ProperCurve (f ≫ sY)) (hΓp : IsProjectiveMorphism (Γ.ι ≫ f ≫ sY))
    (hΓc : Γ.IsContractedBy f) :
    0 ≤ B.degreeOn k (f ≫ sY) Γ.ι Γ.dim_le hBc := by
  have h0 := hnef Γ ⟨hΓp, hΓc⟩
  have : QuasiCompact (f ≫ sY) := AlgebraicGeometry.IsVariety.toQuasiCompact
  have hcycle : curveIntersectionPairing (f ≫ sY) (KCartierDivisor.ofCartier ℝ K) (Γ.cycle ℝ) =
      (cartierCurveIntersection K Γ : ℝ) := by
    simp [curveIntersectionPairing, KCartierDivisor.ofCartier, ProperCurve.cycle]
  rw [hcycle] at h0
  have hZ : (0 : ℤ) ≤ cartierCurveIntersection K Γ := by exact_mod_cast h0
  obtain ⟨-, -, -, hdict, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k (f ≫ sY)
  obtain ⟨e⟩ := hdict K
  have hBeq : weilDivisorEquivFinsupp (cartierWeilDivisor K) = B := by
    ext P; exact hBK P
  rw [hBeq] at e
  have hinv := hBc.isInvertibleModule_divisorialSheaf
  have : Stacks.Ample.IsInvertibleModule X (MMP.CartierDivisor.sheaf K) :=
    Stacks.UFDExtensionGlobal.isInvertible_of_iso e hinv
  have hcur : cartierCurveIntersection K Γ = B.degreeOn k (f ≫ sY) Γ.ι Γ.dim_le hBc := by
    unfold cartierCurveIntersection
    rw [lineBundleCurveIntersection_eq_degreeOn _ Γ hΓp]
    unfold Divisor.degreeOn
    exact MMP.Mori.degreeOn_eq_of_iso k (f ≫ sY) Γ.ι Γ.dim_le e.symm
  rw [← hcur]; exact hZ

/-- Pull-back generators along a birational extension of a function field formally smooth over
`k`. -/
private theorem exists_isPullbackGenerator_of_formallySmooth {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (hK : letI := functionFieldAlgebra sX; Algebra.FormallySmooth k X.functionField) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (f ≫ sX)
    letI := functionFieldMapAlgebra f
    haveI := isScalarTower_functionFieldMap sX f
    ∃ ω : ⋀[X.functionField]^d Ω[X.functionField⁄k], IsPullbackGenerator Y.functionField ω := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have : Algebra.FormallyEtale X.functionField Y.functionField :=
    Algebra.FormallyEtale.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId X.functionField Y.functionField) hf)
  have := essFiniteType_functionField (sX := sX)
  exact exists_isPullbackGenerator_of_formallyEtale
    ((finrank_kaehlerDifferential_of_formallySmooth k X.functionField).trans hd)

/-- A nonzero rational `d`-form exists on a variety whose function field is formally smooth. -/
private theorem exists_ne_zero_rationalPluriForms {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (hK : letI := functionFieldAlgebra sX; Algebra.FormallySmooth k X.functionField) :
    ∃ ω : RationalPluriForms sX d 1, ω ≠ 0 := by
  let := functionFieldAlgebra sX
  have : Algebra.EssFiniteType k X.functionField := essFiniteType_functionField (sX := sX)
  have hrk := finrank_kaehlerDifferential_of_formallySmooth k X.functionField
  have hrk' : Module.finrank X.functionField Ω[X.functionField⁄k] = d := hrk.trans hd
  have := nontrivial_exteriorPower_of_finrank_eq k X.functionField hrk'
  obtain ⟨σ, hσ⟩ := exists_span_singleton_eq_top_exteriorPower hrk'
  have h0 : σ ≠ 0 := by
    rintro rfl
    rw [Submodule.span_zero_singleton] at hσ
    exact bot_ne_top hσ
  exact ⟨(ZTensorPower.basis (basisOfSpanSingleton hσ h0) 1) (),
    (ZTensorPower.basis (basisOfSpanSingleton hσ h0) 1).ne_zero ()⟩

/-- The pull-back of a nonzero rational form along a morphism inducing an isomorphism of function
fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero_of_formallySmooth {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (hK : letI := functionFieldAlgebra sX; Algebra.FormallySmooth k X.functionField) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_formallySmooth (sX := sX) f hf hd hK
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hpull : pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- **Pull-back of rational forms along a composite**: `g^*(f^*τ) = (f ∘ g)^*τ`, for
morphisms inducing isomorphisms of function fields, when `k(X)` is formally smooth. -/
private theorem pullbackRationalPluriForms_comp_of_formallySmooth {k : Type u} [Field k]
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f]
    [IsDominant g] [LocallyOfFiniteType (f ≫ sX)] (hf : Function.Bijective (functionFieldMap f))
    (hg : Function.Bijective (functionFieldMap g)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (hK : letI := functionFieldAlgebra sX; Algebra.FormallySmooth k X.functionField) {m : ℤ}
    (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ) =
      (pullbackRationalPluriForms sX (g ≫ f) τ : RationalPluriForms (g ≫ f ≫ sX) d m) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra (g ≫ f ≫ sX)
  let := functionFieldMapAlgebra f
  let := functionFieldMapAlgebra g
  let := functionFieldMapAlgebra (g ≫ f)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_functionFieldMap (f ≫ sX) g
  have : IsScalarTower k X.functionField Z.functionField :=
    isScalarTower_functionFieldMap sX (g ≫ f)
  have : IsScalarTower X.functionField Y.functionField Z.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f a).symm
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_formallySmooth (sX := sX) f hf hd hK
  have hd' : (Algebra.trdeg k Y.functionField).toNat = d := by
    rw [← trdeg_functionField_eq_of_bijective sX f hf]
    exact hd
  have hK' : Algebra.FormallySmooth k Y.functionField :=
    Algebra.FormallySmooth.of_equiv (functionFieldAlgEquiv sX f hf)
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator_of_formallySmooth (sX := f ≫ sX) g hg hd' hK'
  have hω' : IsPullbackGenerator Z.functionField
      (topFormsMap k X.functionField Y.functionField d ω0) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω0 hω' τ

/-- The divisor of a form on `S` for two equal structure morphisms. -/
private theorem divisorOfFormOnSmoothLocus_pullback_congr {k : Type u} [Field k]
    {Y S : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsIntegral S]
    [IsLocallyNoetherian S] [CompactSpace S] {d : ℕ} (a b : S ⟶ Y) [IsDominant a] [IsDominant b]
    [LocallyOfFiniteType (a ≫ sY)] [LocallyOfFiniteType (b ≫ sY)] (h : a = b)
    (ω : RationalPluriForms sY d 1) :
    divisorOfFormOnSmoothLocus (pullbackRationalPluriForms sY a ω) =
      divisorOfFormOnSmoothLocus (pullbackRationalPluriForms sY b ω) := by
  subst h
  rfl

/-- **Nonzero forms on two resolutions with the same pull-back divisor.** For birational
`f₁, f₂` to `Y` and `g₁, g₂` from a common `S` with `g₁ ≫ f₁ = g₂ ≫ f₂`, a nonzero top form `ω` on
`Y` pulls back to nonzero forms `ω₁, ω₂` on `X₁, X₂` with the same divisor on `S`. -/
private theorem exists_ne_zero_divisorOfFormOnSmoothLocus_pullback_eq {k : Type u} [Field k]
    {Y X₁ X₂ S : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsIntegral X₁] [IsIntegral X₂] [IsIntegral S]
    [LocallyOfFiniteType sY] [IsLocallyNoetherian S] [CompactSpace S]
    (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) (g₁ : S ⟶ X₁) (g₂ : S ⟶ X₂)
    [IsDominant f₁] [IsDominant f₂] [IsDominant g₁] [IsDominant g₂]
    [LocallyOfFiniteType (f₁ ≫ sY)] [LocallyOfFiniteType (f₂ ≫ sY)]
    [LocallyOfFiniteType (g₁ ≫ f₁ ≫ sY)] [LocallyOfFiniteType (g₂ ≫ f₂ ≫ sY)]
    (hf₁ : Function.Bijective (functionFieldMap f₁))
    (hf₂ : Function.Bijective (functionFieldMap f₂))
    (hg₁ : Function.Bijective (functionFieldMap g₁))
    (hg₂ : Function.Bijective (functionFieldMap g₂))
    (hc : g₁ ≫ f₁ = g₂ ≫ f₂) {d : ℕ}
    (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = d)
    (hK : letI := functionFieldAlgebra sY; Algebra.FormallySmooth k Y.functionField) :
    ∃ (ω₁ : RationalPluriForms (f₁ ≫ sY) d 1) (ω₂ : RationalPluriForms (f₂ ≫ sY) d 1),
      ω₁ ≠ 0 ∧ ω₂ ≠ 0 ∧
      divisorOfFormOnSmoothLocus (pullbackRationalPluriForms (f₁ ≫ sY) g₁ ω₁) =
        divisorOfFormOnSmoothLocus (pullbackRationalPluriForms (f₂ ≫ sY) g₂ ω₂) := by
  obtain ⟨ω, hω⟩ := exists_ne_zero_rationalPluriForms (sX := sY) hd hK
  refine ⟨pullbackRationalPluriForms sY f₁ ω, pullbackRationalPluriForms sY f₂ ω,
    pullbackRationalPluriForms_ne_zero_of_formallySmooth f₁ hf₁ hd hK hω,
    pullbackRationalPluriForms_ne_zero_of_formallySmooth f₂ hf₂ hd hK hω, ?_⟩
  rw [pullbackRationalPluriForms_comp_of_formallySmooth f₁ g₁ hf₁ hg₁ hd hK,
    pullbackRationalPluriForms_comp_of_formallySmooth f₂ g₂ hf₂ hg₂ hd hK]
  have : LocallyOfFiniteType ((g₁ ≫ f₁) ≫ sY) :=
    inferInstanceAs (LocallyOfFiniteType (g₁ ≫ f₁ ≫ sY))
  have : LocallyOfFiniteType ((g₂ ≫ f₂) ≫ sY) :=
    inferInstanceAs (LocallyOfFiniteType (g₂ ≫ f₂ ≫ sY))
  exact divisorOfFormOnSmoothLocus_pullback_congr sY (g₁ ≫ f₁) (g₂ ≫ f₂) hc ω

/-- **The Jacobian divisor of a projective birational morphism of surfaces.** For `g : S ⟶ X`
with `S` a normal surface all of whose prime divisors meet the smooth locus and `X` a smooth
surface, and `ω ≠ 0` a top form on `X`, the pull-back `B'` of `div_X(ω)` exists and is Cartier,
and `div_S(g^*ω) - B'` is effective and `g`-exceptional, with support the union of the
`g`-exceptional curves. -/
private theorem isCartier_divisorOfForm_and_exists_isPullback_isEffective {k : Type u} [Field k]
    {X S : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (g : S ⟶ X) [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k (g ≫ sX)]
    [IsIntegral X] [IsIntegral S] [IsLocallyNoetherian X] [IsLocallyNoetherian S]
    [CompactSpace X] [CompactSpace S] [IsNormal S] [IsNormal X] [IsProper g] [IsDominant g]
    (hg : IsBirationalMorphism g) (hgp : IsProjectiveMorphism g) (hX : IsSmoothScheme sX)
    (hn : topologicalKrullDim X = (2 : ℕ)) (hS : topologicalKrullDim S = 2)
    (hsm : ∀ P : AlgebraicGeometry.PrimeDivisor S,
      (P.support ∩ (smoothLocus (g ≫ sX) : Set S)).Nonempty)
    (ω : RationalPluriForms sX 2 1) (hω : ω ≠ 0) :
    (divisorOfForm ω).IsCartier ∧
      ∃ (hB : ∀ Z : irreducibleComponents S, g (componentGenericPoint S Z) ∉ (divisorOfForm ω).supp)
      (B' : Divisor S), (divisorOfForm ω).IsPullback g hB B' ∧ B'.IsCartier ∧
        divisorOfFormOnSmoothLocus ω = divisorOfForm ω ∧
        (divisorOfFormOnSmoothLocus (pullbackRationalPluriForms sX g ω) - B').IsEffective ∧
        IsExceptionalDivisorFor g
          (divisorOfFormOnSmoothLocus (pullbackRationalPluriForms sX g ω) - B') ∧
        ((divisorOfFormOnSmoothLocus (pullbackRationalPluriForms sX g ω) - B').supp : Set S) =
          ⋃ (C : ProperCurve (g ≫ sX)) (_ : IsContractedProjectiveCurve (g ≫ sX) g C),
            closure {C.point} := by
  have hBc : (divisorOfForm ω).IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hX _
  have hB : ∀ Z : irreducibleComponents S, g (componentGenericPoint S Z) ∉ (divisorOfForm ω).supp :=
    fun Z => MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant g _ Z
  obtain ⟨B', hB'⟩ := hBc.exists_isPullback hB
  refine ⟨hBc, hB, B', hB', hB'.isCartier hBc, ?_, ?_⟩
  · classical
    unfold MMP.Resolution.divisorOfFormOnSmoothLocus
    refine (Finsupp.filter_eq_self_iff _ _).mpr fun P _ => ?_
    have hsl : smoothLocus sX = ⊤ := hX
    obtain ⟨x, hx⟩ := P.support_nonempty
    exact ⟨x, hx, by rw [hsl]; trivial⟩
  · obtain ⟨he, hx⟩ := isEffective_and_isExceptional_divisorOfFormOnSmoothLocus_sub_pullback sX g
      hg hX hn hsm ω hω hB B' hB'
    exact ⟨he, hx, supp_divisorOfFormOnSmoothLocus_sub_pullback_eq_iUnion sX g hg hgp hX hn hS hsm
      ω hω hB B' hB'⟩

/-- On a surface with two projective birational morphisms to smooth surfaces and no curve
exceptional for both, every prime divisor meets the smooth locus. -/
private theorem support_inter_smoothLocus_nonempty_of_not_isContracted {k : Type u} [Field k]
    {X₁ X₂ S : Scheme.{u}}
    (sX₁ : X₁ ⟶ Spec (.of k)) (sX₂ : X₂ ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    (g₁ : S ⟶ X₁) (g₂ : S ⟶ X₂) (hs₁ : g₁ ≫ sX₁ = sS) (hs₂ : g₂ ≫ sX₂ = sS)
    [AlgebraicGeometry.IsVariety k sX₁] [AlgebraicGeometry.IsVariety k sX₂]
    [hS : AlgebraicGeometry.IsVariety k sS]
    [IsIntegral X₁] [IsIntegral X₂] [IsIntegral S] [IsNormal X₁] [IsNormal X₂]
    [IsLocallyNoetherian S] [CompactSpace X₁] [CompactSpace X₂]
    (hdim : topologicalKrullDim S = 2)
    (hp₁ : IsProjectiveMorphism g₁) (hb₁ : IsBirationalMorphism g₁)
    (hp₂ : IsProjectiveMorphism g₂) (hb₂ : IsBirationalMorphism g₂)
    (hX₁ : IsSmoothScheme sX₁) (hX₂ : IsSmoothScheme sX₂)
    (hno : ∀ C : ProperCurve sS,
        ¬ (IsContractedProjectiveCurve sS g₁ C ∧ IsContractedProjectiveCurve sS g₂ C))
    (P : AlgebraicGeometry.PrimeDivisor S) :
    (P.support ∩ (smoothLocus sS : Set S)).Nonempty := by
  have hv₁ : AlgebraicGeometry.IsVariety k (g₁ ≫ sX₁) := hs₁ ▸ hS
  have hv₂ : AlgebraicGeometry.IsVariety k (g₂ ≫ sX₂) := hs₂ ▸ hS
  have : IsProper g₁ := isProper_of_isProjectiveMorphism g₁ hp₁
  have : IsProper g₂ := isProper_of_isProjectiveMorphism g₂ hp₂
  have hmem : P.genericPoint ∈ smoothLocus sS := by
    by_cases h₁ : topologicalKrullDim (closure (g₁.base '' P.support)) <
        topologicalKrullDim P.support
    · by_cases h₂ : topologicalKrullDim (closure (g₂.base '' P.support)) <
          topologicalKrullDim P.support
      · exfalso
        obtain ⟨C₁, hC₁, hc₁⟩ :=
          exists_isContractedProjectiveCurve_of_isExceptional hS hdim ‹_› g₁ hs₁ hp₁ P h₁
        obtain ⟨C₂, hC₂, hc₂⟩ :=
          exists_isContractedProjectiveCurve_of_isExceptional hS hdim ‹_› g₂ hs₂ hp₂ P h₂
        exact hno C₁ ⟨hc₁, ProperCurve.ext (hC₁.trans hC₂.symm) ▸ hc₂⟩
      · have := genericPoint_mem_smoothLocus_of_not_lt sX₂ g₂ hb₂ hX₂ P h₂
        rwa [hs₂] at this
    · have := genericPoint_mem_smoothLocus_of_not_lt sX₁ g₁ hb₁ hX₁ P h₁
      rwa [hs₁] at this
  refine ⟨P.genericPoint, ?_, hmem⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- A point of a proper curve lying on a prime divisor of an integral surface is the generic point
of that prime divisor. -/
private theorem point_eq_genericPoint_of_mem_support {k : Type u} [Field k] {S : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} [IsIntegral S] (hS : topologicalKrullDim S = 2)
    (C : ProperCurve sS) (P : AlgebraicGeometry.PrimeDivisor S) (h : C.point ∈ P.support) :
    C.point = P.genericPoint := by
  by_contra hne
  let : PartialOrder S := specializationOrder S
  have hcoh := coheight_eq_one_of_not_isClosed hS (point_ne_genericPoint hS C)
    (not_isClosed_singleton_point C)
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  have hlt : C.point < P.genericPoint :=
    lt_of_le_of_ne (specializes_iff_mem_closure.mpr h) hne
  have h1 := Order.coheight_add_one_le hlt
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P, hcoh] at h1
  exact absurd h1 (by decide)

/-- A resolution of a quasi-projective surface is a variety and normal. -/
private theorem isVariety_and_isNormal_of_isProjectiveSurfaceResolution {k : Type u} [Field k]
    {Y X : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : IsQuasiProjectiveVariety k sY)
    [IsIntegral X] (f : X ⟶ Y) [LocallyOfFiniteType (f ≫ sY)]
    (hf : IsProjectiveSurfaceResolution sY f) :
    AlgebraicGeometry.IsVariety k (f ≫ sY) ∧ IsNormal X := by
  have := hY.toIsVariety
  have := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  exact ⟨{}, (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    hf.isSmoothScheme).2⟩

/-- A projective morphism to a quasi-projective `k`-scheme has quasi-projective source. -/
private theorem isQuasiProjective_comp_of_isProjectiveMorphism {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) (hf : IsProjectiveMorphism f)
    (hg : Stacks.HProjective.IsQuasiProjective g) :
    Stacks.HProjective.IsQuasiProjective (f ≫ g) :=
  isQuasiProjective_comp_of_exists_isAmple f g ⟨_, inferInstance,
    Stacks.Ample.isAmple_unitModule_of_isAffine _⟩
    (Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective f hf.isHQuasiProjective) hg

/-- The positive and negative parts of a `ℤ`-divisor have disjoint supports. -/
private theorem disjoint_support_posPart_negPart {X : Scheme.{u}} (D : Divisor X) :
    Disjoint D⁺.support D⁻.support := by
  classical
  rw [Finset.disjoint_left]
  intro P h1 h2
  simp only [Finsupp.mem_support_iff, posPart, negPart, Finsupp.sup_apply, Finsupp.neg_apply,
    Finsupp.coe_zero, Pi.zero_apply] at h1 h2
  omega

/-- The positive part of a `ℤ`-divisor, coefficientwise. -/
private theorem posPart_apply {X : Scheme.{u}} (D : Divisor X)
    (P : AlgebraicGeometry.PrimeDivisor X) :
    D⁺ P = max (D P) 0 := by
  simp [posPart, Finsupp.sup_apply]

/-- The degree along a curve is additive under differences of Cartier divisors. -/
private theorem degreeOn_sub {k : Type u} [Field k] {X C : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) {D E : Divisor X} (hD : D.IsCartier) (hE : E.IsCartier) :
    (D - E).degreeOn k sX i hdim (hD.sub hE) =
      D.degreeOn k sX i hdim hD - E.degreeOn k sX i hdim hE := by
  rw [Divisor.degreeOn_congr (sub_eq_add_neg D E) _ (hD.add hE.neg),
    Divisor.degreeOn_add k sX i hdim _ _ hD hE.neg, Divisor.degreeOn_neg' k sX i hdim _ hE,
    sub_eq_add_neg]

/-- **Negativity lemma, nef form.** Let `g : S ⟶ X` be a projective birational morphism from a
normal surface to a quasi-projective variety. A Cartier divisor `D` on `S` with `g`-exceptional
positive part and nonnegative degree on every `g`-contracted projective curve has `D⁺ = 0`,
that is `D ≤ 0`. -/
private theorem posPart_eq_zero_of_degreeOn_nonneg {k : Type u} [Field k] {S X : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)}
    (hS : AlgebraicGeometry.IsVariety k sS) (hSdim : topologicalKrullDim S = 2) [IsNormal S]
    (hX : AlgebraicGeometry.IsVariety k sX) (hXqp : Stacks.HProjective.IsHQuasiProjective sX)
    [IsIntegral S] [IsLocallyNoetherian S] (g : S ⟶ X) (hg : g ≫ sX = sS)
    (hproj : IsProjectiveMorphism g) (hbir : IsBirationalMorphism g)
    (D : Divisor S) (hD : D.IsCartier) (hexc : IsExceptionalDivisorFor g D⁺)
    (hnn : ∀ C : ProperCurve sS, IsContractedProjectiveCurve sS g C →
      0 ≤ D.degreeOn k sS C.ι C.dim_le hD) :
    D⁺ = 0 := by
  by_contra h
  have hD' : (D⁺ - D⁻).IsCartier := (posPart_sub_negPart D).symm ▸ hD
  obtain ⟨C, hC, -, hneg⟩ := exists_isContractedProjectiveCurve_degreeOn_neg hS hSdim hX hXqp g
    hg hproj hbir D⁺ D⁻ hD' (posPart_nonneg D) (negPart_nonneg D)
    (disjoint_support_posPart_negPart D) h hexc
  rw [Divisor.degreeOn_congr (posPart_sub_negPart D) hD' hD] at hneg
  exact (hnn C hC).not_gt hneg

/-- On a common normal surface `S` dominating two resolutions `f₁, f₂` of `Y` over `Y`, with no
curve exceptional for both `gᵢ : S ⟶ Xᵢ`, minimality of `f₂` forces every `g₁`-exceptional curve
to be `g₂`-exceptional. -/
private theorem isContractedProjectiveCurve_of_isMinimalSurfaceResolution {k : Type u} [Field k]
    {Y X₁ X₂ S : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : IsQuasiProjectiveVariety k sY)
    [IsIntegral X₁] [IsNoetherian X₁] [IsIntegral X₂] [IsNoetherian X₂]
    (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) [LocallyOfFiniteType (f₁ ≫ sY)]
    [LocallyOfFiniteType (f₂ ≫ sY)] (h₁ : IsProjectiveSurfaceResolution sY f₁)
    (h₂ : IsMinimalSurfaceResolution sY f₂) (sS : S ⟶ Spec (.of k)) [IsNormal S]
    (hqS : IsQuasiProjectiveVariety k sS) (hdim : topologicalKrullDim S = 2)
    (g₁ : S ⟶ X₁) (g₂ : S ⟶ X₂) (hs₁ : g₁ ≫ f₁ ≫ sY = sS) (hs₂ : g₂ ≫ f₂ ≫ sY = sS)
    (hc : g₁ ≫ f₁ = g₂ ≫ f₂)
    (hp₁ : IsProjectiveMorphism g₁) (hb₁ : MMP.Mori.IsBirationalMorphism g₁)
    (hp₂ : IsProjectiveMorphism g₂) (hb₂ : MMP.Mori.IsBirationalMorphism g₂)
    (hno : ∀ C : MMP.Mori.ProperCurve sS,
        ¬ (IsContractedProjectiveCurve sS g₁ C ∧ IsContractedProjectiveCurve sS g₂ C))
    (C : MMP.Mori.ProperCurve sS) (hC : IsContractedProjectiveCurve sS g₁ C) :
    IsContractedProjectiveCurve sS g₂ C := by
  subst hs₁
  have hYv := hY.toIsVariety
  have hSv : AlgebraicGeometry.IsVariety k (g₁ ≫ f₁ ≫ sY) := hqS.toIsVariety
  have hSi : IsIntegral S := hSv.toIsIntegral
  obtain ⟨hv₁, hN₁⟩ := isVariety_and_isNormal_of_isProjectiveSurfaceResolution sY hY f₁ h₁
  obtain ⟨hv₂, hN₂⟩ := isVariety_and_isNormal_of_isProjectiveSurfaceResolution sY hY f₂ h₂.1
  have hln₁ := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    h₁.isSmoothScheme).1
  have hln₂ := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    h₂.1.isSmoothScheme).1
  have hcs₁ : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace (f₁ ≫ sY)
  have hcs₂ : CompactSpace X₂ := QuasiCompact.compactSpace_of_compactSpace (f₂ ≫ sY)
  have hlnS : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) (g₁ ≫ f₁ ≫ sY)
  have hcsS : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (g₁ ≫ f₁ ≫ sY)
  have hdom₁ : IsDominant g₁ := hb₁.isDominant
  have hdom₂ : IsDominant g₂ := hb₂.isDominant
  have : IsProper g₁ := isProper_of_isProjectiveMorphism g₁ hp₁
  have : IsProper g₂ := isProper_of_isProjectiveMorphism g₂ hp₂
  have hsm := support_inter_smoothLocus_nonempty_of_not_isContracted (f₁ ≫ sY) (f₂ ≫ sY)
    (g₁ ≫ f₁ ≫ sY) g₁ g₂ rfl hs₂
    hdim hp₁ hb₁ hp₂ hb₂ h₁.isSmoothScheme h₂.1.isSmoothScheme hno
  have : AlgebraicGeometry.IsVariety k (g₂ ≫ f₂ ≫ sY) := hs₂ ▸ hSv
  have : IsIntegral Y := hYv.toIsIntegral
  have : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  have : IsDominant f₁ := h₁.isBirationalMorphism.isDominant
  have : IsDominant f₂ := h₂.1.isBirationalMorphism.isDominant
  have : Smooth (f₁ ≫ sY) := (isSmoothScheme_iff _).mp h₁.isSmoothScheme
  have hK : letI := functionFieldAlgebra sY; Algebra.FormallySmooth k Y.functionField := by
    let := functionFieldAlgebra sY
    let := functionFieldAlgebra (f₁ ≫ sY)
    have : Algebra.FormallySmooth k X₁.functionField :=
      (MMP.Flips.ResolutionInputs.stalk_facts (sX := f₁ ≫ sY) (genericPoint X₁)).1
    exact Algebra.FormallySmooth.of_equiv
      (functionFieldAlgEquiv sY f₁ h₁.isBirationalMorphism.functionFieldMap_bijective).symm
  obtain ⟨ω₁, ω₂, hω₁, hω₂, hdiv⟩ :=
    exists_ne_zero_divisorOfFormOnSmoothLocus_pullback_eq sY f₁ f₂ g₁ g₂
      h₁.isBirationalMorphism.functionFieldMap_bijective
      h₂.1.isBirationalMorphism.functionFieldMap_bijective hb₁.functionFieldMap_bijective
      hb₂.functionFieldMap_bijective hc
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY)
        (by exact_mod_cast h₁.dim_eq)) hK
  obtain ⟨hBc₁, hB₁, B'₁, hP₁, hB'c₁, -, he₁, hx₁, hsupp₁⟩ :=
    isCartier_divisorOfForm_and_exists_isPullback_isEffective (f₁ ≫ sY) g₁ hb₁ hp₁ h₁.isSmoothScheme
      (by exact_mod_cast h₁.dim_source_eq)
      hdim hsm ω₁ hω₁
  obtain ⟨hBc₂, hB₂, B'₂, hP₂, hB'c₂, hfil₂, he₂, hx₂, -⟩ :=
    isCartier_divisorOfForm_and_exists_isPullback_isEffective (f₂ ≫ sY) g₂ hb₂ hp₂
      h₂.1.isSmoothScheme
      (by exact_mod_cast h₂.1.dim_source_eq)
      hdim (hs₂ ▸ hsm) ω₂ hω₂
  rw [← hdiv] at he₂ hx₂
  set DS := divisorOfFormOnSmoothLocus (pullbackRationalPluriForms (f₁ ≫ sY) g₁ ω₁)
  -- `D = B'₂ - B'₁ = E₁ - E₂` with `Eᵢ = DS - B'ᵢ`
  set D : Divisor S := B'₂ - B'₁ with hD
  have hDE : ∀ P, D P = (DS - B'₁) P - (DS - B'₂) P := fun P => by
    rw [hD, ← Finsupp.sub_apply, sub_sub_sub_cancel_left]
  have hexc : IsExceptionalDivisorFor g₁ D⁺ := fun P hP => by
    have h1 := Finsupp.mem_support_iff.mp hP
    have h2 : 0 ≤ (DS - B'₂) P := he₂ P
    rw [posPart_apply, hDE] at h1
    exact hx₁ P (Finsupp.mem_support_iff.mpr (by omega))
  -- minimality of `f₂`: `D` is nonnegative on the `g₁`-contracted curves
  have hnn : ∀ C₀ : ProperCurve (g₁ ≫ f₁ ≫ sY), IsContractedProjectiveCurve _ g₁ C₀ →
      0 ≤ D.degreeOn k (g₁ ≫ f₁ ≫ sY) C₀.ι C₀.dim_le (hB'c₂.sub hB'c₁) := by
    intro C₀ hC₀
    have hdeg₁ := (degreeOn_pullback (f₁ ≫ sY) _ g₁ rfl (divisorOfForm ω₁) hBc₁ hB₁ B'₁ hP₁
      hB'c₁ C₀ hC₀.1).1 hC₀.2
    obtain ⟨Γ, hΓpt, hΓcl, hΓp, r, hr⟩ :=
      (degreeOn_pullback (f₂ ≫ sY) _ g₂ hs₂ (divisorOfForm ω₂) hBc₂ hB₂ B'₂ hP₂ hB'c₂ C₀
        hC₀.1).2 (fun h => hno C₀ ⟨hC₀, hC₀.1, h⟩)
        (isQuasiProjective_comp_of_isProjectiveMorphism f₂ sY h₂.1.isProjectiveMorphism
          hY.isQuasiProjective)
    have hΓc : Γ.IsContractedBy f₂ := by
      intro x hx
      rw [hΓcl] at hx
      obtain ⟨c, hc', rfl⟩ := hx
      rw [hΓpt]
      change (g₂ ≫ f₂) c = (g₂ ≫ f₂) C₀.point
      rw [← hc]
      change f₁ (g₁ c) = f₁ (g₁ C₀.point)
      rw [hC₀.2 c hc']
    obtain ⟨K₂, hK₂, hnef⟩ := h₂.2 ω₂ hω₂
    have : AlgebraicGeometry.IsSmoothVariety k (f₂ ≫ sY) :=
      { toIsVariety := hv₂, toSmooth := (isSmoothScheme_iff _).mp h₂.1.isSmoothScheme }
    rw [degreeOn_sub _ _ hB'c₂ hB'c₁, hdeg₁, hr, sub_zero]
    exact mul_nonneg (by positivity) (degreeOn_nonneg_of_isNef sY f₂ K₂ hnef (divisorOfForm ω₂)
      (fun P => by rw [hK₂ P, hfil₂]) hBc₂ Γ hΓp hΓc)
  have hD0 := posPart_eq_zero_of_degreeOn_nonneg hSv hdim hv₁
    (Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAmple (f₁ ≫ sY)
      (Stacks.Ample.unitModule (Spec (.of k))) (Stacks.Ample.isAmple_unitModule_of_isAffine _)
      (isQuasiProjective_comp_of_isProjectiveMorphism f₁ sY h₁.isProjectiveMorphism
        hY.isQuasiProjective))
    g₁ rfl hp₁ hb₁ D (hB'c₂.sub hB'c₁) hexc hnn
  -- hence `E₁ ≤ E₂`, and the component of `Supp E₁` through `C` is `g₂`-exceptional
  have hCsupp : C.point ∈ ((DS - B'₁).supp : Set S) := by
    rw [hsupp₁]
    exact Set.mem_iUnion₂.mpr ⟨C, hC, subset_closure rfl⟩
  obtain ⟨P, hP, hCP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hCsupp
  have hP₂ : (DS - B'₂) P ≠ 0 := by
    have h1 : D⁺ P = 0 := by rw [hD0]; rfl
    have h2 : 0 ≤ (DS - B'₁) P := he₁ P
    have h3 : (DS - B'₁) P ≠ 0 := hP
    rw [posPart_apply, hDE] at h1
    omega
  obtain ⟨C', hC'pt, hC'⟩ := exists_isContractedProjectiveCurve_of_isExceptional hSv hdim hv₂ g₂
    hs₂ hp₂ P (hx₂ P (Finsupp.mem_support_iff.mpr hP₂))
  rwa [ProperCurve.ext ((point_eq_genericPoint_of_mem_support hdim C P hCP).trans hC'pt.symm)]

/-- A morphism which is birational (`MMP.Mori.IsBirationalMorphism`) is an open immersion on
some dense open subscheme of its source. -/
private theorem exists_dense_isOpenImmersion_ι_comp {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hb : MMP.Mori.IsBirationalMorphism f) :
    ∃ W : X.Opens, Dense (W : Set X) ∧ IsOpenImmersion (W.ι ≫ f) := by
  obtain ⟨e, he⟩ := hb
  rw [Scheme.PartialIso.toRationalMap, Scheme.Hom.toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hWd, hW1, hW2, hWeq⟩ := he
  have e2 : ((Scheme.Hom.toPartialMap f).restrict W hWd hW2).hom = W.ι ≫ f := by
    change X.homOfLE (show W ≤ ⊤ from hW2) ≫ (⊤ : X.Opens).ι ≫ f = _
    rw [Scheme.homOfLE_ι_assoc]
  refine ⟨W, hWd, ?_⟩
  rw [← e2, ← hWeq]
  dsimp [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap]
  have : IsOpenImmersion (X.homOfLE (show W ≤ e.source from hW1)) := inferInstance
  exact IsOpenImmersion.comp _ _

/-- Two isomorphisms `φ ψ : X₁ ≅ X₂` with `X₁` integral and `φ.hom ≫ f = ψ.hom ≫ f`, for a
separated birational morphism `f : X₂ ⟶ Y`, are equal. -/
private theorem hom_eq_of_comp_eq {Y X₁ X₂ : Scheme.{u}} [IsIntegral X₁] (f : X₂ ⟶ Y)
    [IsSeparated f] (hb : MMP.Mori.IsBirationalMorphism f) (φ ψ : X₁ ≅ X₂)
    (h : φ.hom ≫ f = ψ.hom ≫ f) : φ.hom = ψ.hom := by
  obtain ⟨W, hWd, _⟩ := exists_dense_isOpenImmersion_ι_comp hb
  let U : X₁.Opens := φ.hom ⁻¹ᵁ W ⊓ ψ.hom ⁻¹ᵁ W
  have hd : ∀ χ : X₁ ≅ X₂, Dense ((χ.hom ⁻¹ᵁ W : X₁.Opens) : Set X₁) := fun χ =>
    hWd.preimage (Scheme.homeoOfIso χ).isOpenMap
  have hU : Dense (U : Set X₁) := (hd φ).inter_of_isOpen_left (hd ψ) (φ.hom ⁻¹ᵁ W).2
  have : IsDominant U.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  refine ext_of_isDominant_of_isSeparated f h U.ι ?_
  have h1 := Scheme.Hom.resLE_comp_ι φ.hom (inf_le_left : U ≤ φ.hom ⁻¹ᵁ W)
  have h2 := Scheme.Hom.resLE_comp_ι ψ.hom (inf_le_right : U ≤ ψ.hom ⁻¹ᵁ W)
  rw [← h1, ← h2]
  congr 1
  rw [← cancel_mono (W.ι ≫ f), reassoc_of% h1, reassoc_of% h2, h]

/-- A birational morphism `f₂ : X₂ ⟶ Y` with `X₂` integral and any dominant `f₁ : X₁ ⟶ Y` admit
a representative `h : U ⟶ X₂` of `f₂⁻¹ ∘ f₁` on a nonempty open `U ⊆ X₁`. -/
private theorem exists_opens_hom_comp_eq {Y X₁ X₂ : Scheme.{u}} [IsIntegral X₂]
    (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) [IsDominant f₁] (hb : MMP.Mori.IsBirationalMorphism f₂) :
    ∃ (U : X₁.Opens) (_ : (U : Set X₁).Nonempty) (h : U.toScheme ⟶ X₂), h ≫ f₂ = U.ι ≫ f₁ := by
  obtain ⟨W, hWd, hW⟩ := exists_dense_isOpenImmersion_ι_comp hb
  let U : X₁.Opens := f₁ ⁻¹ᵁ (W.ι ≫ f₂).opensRange
  have hU : (U : Set X₁).Nonempty := by
    obtain ⟨w, hw⟩ := hWd.nonempty
    exact f₁.denseRange.exists_mem_open (W.ι ≫ f₂).opensRange.2 ⟨_, ⟨w, hw⟩, rfl⟩
  have hr : Set.range (U.ι ≫ f₁) ⊆ Set.range (W.ι ≫ f₂) := by
    rintro _ ⟨x, rfl⟩
    exact x.2
  refine ⟨U, hU, IsOpenImmersion.lift (W.ι ≫ f₂) (U.ι ≫ f₁) hr ≫ W.ι, ?_⟩
  rw [Category.assoc, IsOpenImmersion.lift_fac]

/-- Existence: two minimal resolutions of a quasi-projective surface are isomorphic over `Y`. -/
private theorem exists_iso_comp_eq {k : Type u} [Field k]
    {Y X₁ X₂ : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : Stacks.HProjective.IsQuasiProjective sY)
    [IsIntegral X₁] [IsNoetherian X₁] [IsIntegral X₂] [IsNoetherian X₂]
    (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) [LocallyOfFiniteType (f₁ ≫ sY)]
    [LocallyOfFiniteType (f₂ ≫ sY)] (h₁ : IsMinimalSurfaceResolution sY f₁)
    (h₂ : IsMinimalSurfaceResolution sY f₂) :
    ∃ φ : X₁ ≅ X₂, φ.hom ≫ f₂ = f₁ := by
  have hY' : IsQuasiProjectiveVariety k sY :=
    { toIsVariety := h₁.1.isVariety, isQuasiProjective := hY }
  have := h₁.1.isBirationalMorphism.isDominant
  obtain ⟨U, hU, h, hh⟩ := exists_opens_hom_comp_eq f₁ f₂ h₂.1.isBirationalMorphism
  obtain ⟨hN, hqS, hdim, ⟨hp₁, hb₁⟩, ⟨hp₂, hb₂⟩, hc, hno⟩ :=
    IsProjectiveSurfaceResolution.graphNormalization_spec hY' h₁.1 h₂.1 U hU h hh
  set φ := pullback.lift U.ι h hh.symm
  set g₁ : φ.normalization ⟶ X₁ := φ.fromNormalization ≫ pullback.fst f₁ f₂
  set g₂ : φ.normalization ⟶ X₂ := φ.fromNormalization ≫ pullback.snd f₁ f₂
  have hs₂ : g₂ ≫ f₂ ≫ sY = g₁ ≫ f₁ ≫ sY := by rw [reassoc_of% hc]
  have hex₁ : ∀ C : MMP.Mori.ProperCurve (g₁ ≫ f₁ ≫ sY),
      ¬ IsContractedProjectiveCurve (g₁ ≫ f₁ ≫ sY) g₁ C := fun C hC =>
    hno C ⟨hC, isContractedProjectiveCurve_of_isMinimalSurfaceResolution sY hY' f₁ f₂ h₁.1 h₂
      _ hqS hdim g₁ g₂ rfl hs₂ hc hp₁ hb₁ hp₂ hb₂ hno C hC⟩
  have hex₂ : ∀ C : MMP.Mori.ProperCurve (g₁ ≫ f₁ ≫ sY),
      ¬ IsContractedProjectiveCurve (g₁ ≫ f₁ ≫ sY) g₂ C := fun C hC =>
    hno C ⟨isContractedProjectiveCurve_of_isMinimalSurfaceResolution sY hY' f₂ f₁ h₂.1 h₁
      _ hqS hdim g₂ g₁ hs₂ rfl hc.symm hp₂ hb₂ hp₁ hb₁ (fun C h => hno C h.symm) C hC, hC⟩
  obtain ⟨hv₁, _⟩ := isVariety_and_isNormal_of_isProjectiveSurfaceResolution sY hY' f₁ h₁.1
  obtain ⟨hv₂, _⟩ := isVariety_and_isNormal_of_isProjectiveSurfaceResolution sY hY' f₂ h₂.1
  have : IsIso g₁ := isIso_of_forall_not_isContractedProjectiveCurve hqS.toIsVariety hdim hv₁
    h₁.1.dim_source_eq g₁ rfl hp₁ hb₁ hex₁
  have : IsIso g₂ := isIso_of_forall_not_isContractedProjectiveCurve hqS.toIsVariety hdim hv₂
    h₂.1.dim_source_eq g₂ hs₂ hp₂ hb₂ hex₂
  refine ⟨(asIso g₁).symm ≪≫ asIso g₂, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc, ← hc,
    IsIso.inv_hom_id_assoc]

/-- **Uniqueness of the minimal resolution.** Two minimal resolutions `f₁ : X₁ ⟶ Y` and
`f₂ : X₂ ⟶ Y` of a quasi-projective surface `Y` over a field `k` are isomorphic over `Y` by a
unique isomorphism: there is exactly one `φ : X₁ ≅ X₂` with `φ.hom ≫ f₂ = f₁`. -/
@[mmp "thm_kr2a_minimal_resolution_unique"]
public theorem existsUnique_iso_comp_eq_of_isMinimalSurfaceResolution {k : Type u} [Field k]
    {Y X₁ X₂ : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : Stacks.HProjective.IsQuasiProjective sY)
    [IsIntegral X₁] [IsNoetherian X₁] [IsIntegral X₂] [IsNoetherian X₂]
    (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) [LocallyOfFiniteType (f₁ ≫ sY)]
    [LocallyOfFiniteType (f₂ ≫ sY)] (h₁ : IsMinimalSurfaceResolution sY f₁)
    (h₂ : IsMinimalSurfaceResolution sY f₂) :
    ∃! φ : X₁ ≅ X₂, φ.hom ≫ f₂ = f₁ := by
  obtain ⟨φ, hφ⟩ := exists_iso_comp_eq sY hY f₁ f₂ h₁ h₂
  refine ⟨φ, hφ, fun ψ hψ => Iso.ext ?_⟩
  have := isProper_of_isProjectiveMorphism f₂ h₂.1.isProjectiveMorphism
  exact hom_eq_of_comp_eq f₂ h₂.1.isBirationalMorphism _ _ (hψ.trans hφ.symm)

end

end MMP.Resolution
