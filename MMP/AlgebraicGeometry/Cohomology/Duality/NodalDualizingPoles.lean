module

public import MMP.AlgebraicGeometry.Singularities.Deminormal.Discrepancy
import MMP.RingTheory.SplitNodeNormalization
import MMP.AlgebraicGeometry.Modules.TotalQuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.FiniteTwistedTrace
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedProperNagata
public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.AffineFractionRing
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.RingEquivTransport

/-!
# The canonical generator has a simple pole on each nodal branch

Let `X` be a scheme of finite type and pure dimension `n` over a field `k` satisfying (2.6.1),
with dualizing sheaf `ω_X`, and let `P ∈ X` be a codimension-one point at which `X` is not
regular, so that `𝒪̂_{X,P} ≅ κ(P)[[u, v]]/(uv)`. Let `ν : X^ν ⟶ X` be the normalization and
`ω_{X^ν}` the dualizing sheaf of `X^ν`. There are exactly two points of `X^ν` over `P`, and a
section `s` of `ω_X` generating `ω_X` near `P` pulls back to a section of `ω_{X^ν}` with a
simple pole at each of them. On the formal node `S/(uv)`, `S = κ[[u, v]]`, the generator of
`Ext¹_S(S/(uv), S du ∧ dv)` is `(du ∧ dv)/(uv)`, whose restrictions to the two branches are
`du/u` and `-dv/v`.

## Main results

* `MMP.Flips.ncard_preimage_eq_two_and_isOrderOfSectionAt_neg_one`: the two points of the
  normalization over a singular codimension-one point, and the order `-1` of the pulled-back
  generator at each of them.
* `MMP.Flips.ncard_preimage_eq_two_and_isOrderOfSectionAt_neg_one_of_affine`: the same, for a
  trace given by finite duality on each affine open of `X`.

## Implementation notes

The pull-back of `s` to `X^ν` is taken through the trace `τ : ν_* ω_{X^ν} ⟶ ω_X`. The trace is
characterized, up to a unit of `Γ(X^ν, 𝒪)`, as a generator of `Hom(ν_* ω_{X^ν}, ω_X)` as a
`Γ(X^ν, 𝒪)`-module (duality for the finite morphism `ν`,
`ν_* 𝓗om(ω_{X^ν}, ω_{X^ν}) ≅ 𝓗om(ν_* ω_{X^ν}, ω_X)`); the statement is made for every such
generator. A section `t` of `ω_{X^ν}` over `ν⁻¹(W')` with `τ(t) = s|_{W'}` on an open `W'`
containing the generic points of `X` specializing to `P` is a pull-back of `s`; the orders are
those of `MMP.Flips.IsOrderOfSectionAt`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.6, 16.3.3
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

-- The Stacks results used here are stated at the locally small models of `D(R)`, `D(𝒪_X)` and
-- `D(SheafOfModules R)`, which Stacks scopes
-- (`StacksFrontier.Homology.DerivedCategory.LocallySmall`).
open scoped Stacks.SmallDerivedModel

namespace MMP.Flips

open MMP.Mori

-- `IsProjectiveVariety k f → IsProperVariety k f` solves `Field k` with `k` unknown and, reached
-- from `IsVariety.toIsIntegral`, sends every failing `IsIntegral X` search through all fields
attribute [-instance] AlgebraicGeometry.instIsProperVarietyOfIsProjectiveVariety

/-- The structure map `C ⟶ 𝒪_{Y, y}` of a scheme locally of finite type over `Spec C` is
essentially of finite type. -/
private theorem essFiniteType_stalkStructureMap {C : Type u} [CommRing C] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of C)) [LocallyOfFiniteType f] (y : Y) :
    ((f.stalkMap y).hom.comp ((Scheme.ΓSpecIso (.of C)).inv ≫
      (Spec (.of C)).presheaf.germ ⊤ (f.base y) (by simp)).hom).EssFiniteType := by
  have := (f.base y).isPrime
  have h0 : (algebraMap C (Localization.AtPrime (f.base y).asIdeal)).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization _ (f.base y).asIdeal.primeCompl
  have hiso : (Spec.stalkIso (.of C) (f.base y)).inv.hom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _
      (asIso (Spec.stalkIso (.of C) (f.base y)).inv).commRingCatIsoToRingEquiv.surjective
      ).essFiniteType
  have h1 : ((Scheme.ΓSpecIso (.of C)).inv ≫
      (Spec (.of C)).presheaf.germ ⊤ (f.base y) (by simp)).hom.EssFiniteType := by
    have e := congrArg CommRingCat.Hom.hom
      (Spec.algebraMap_stalkIso_inv (R := .of C) (x := f.base y))
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e
    rw [← e]
    exact h0.comp hiso
  exact h1.comp (LocallyOfFiniteType.stalkMap f y)

/-- There are exactly two points of the normalization over a singular codimension-one point. -/
private theorem ncard_preimage_eq_two {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hFA : SatisfiesFA261 sX)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (P : X) (hP : Order.coheight P = 1) (hPsing : ¬ IsRegularLocalRing (X.presheaf.stalk P)) :
    ((Stacks.AlgebraicGeometry.Normalization.normalization X hX).base ⁻¹' {P}).ncard = 2 := by
  classical
  obtain ⟨hlft, -, hred, -, hnode⟩ := hFA
  obtain ⟨e⟩ := (hnode P hP).resolve_left hPsing
  let A := X.presheaf.stalk P
  letI : Algebra k A := ((sX.stalkMap P).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (sX.base P) (by simp)).hom).toAlgebra
  haveI : Algebra.EssFiniteType k A := by
    rw [← RingHom.essFiniteType_algebraMap]
    exact essFiniteType_stalkStructureMap sX P
  haveI : IsReduced A := inferInstance
  have hdim : ringKrullDim A = 1 := by rw [ringKrullDim_stalk_eq_coheight, hP]; rfl
  obtain ⟨-, m₁, m₂, hm₁, hm₂, hne, hprimes, -⟩ :=
    MMP.exists_adicCompletion_localization_ringEquiv_powerSeries_of_splitNode k A hdim e
      (FractionRing A) (integralClosure A (FractionRing A))
  let B := integralClosure A (FractionRing A)
  have hmax : ∀ m : Ideal B, m.IsMaximal ↔ m ∈ ({m₁, m₂} : Set (Ideal B)) := fun m =>
    ⟨fun hm => hprimes ▸ ⟨hm.isPrime, ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) m)).symm⟩⟩,
      by rintro (rfl | rfl) <;> assumption⟩
  letI := Stacks.NormalizationStalkAmbient.normalizationPushforwardStalkAlgebra X hX P
  letI : Algebra A (FractionRing (A ⧸ nilradical A)) :=
    (Stacks.NormalizationStalkAmbient.reductionFractionRingHom A).toAlgebra
  let eS := (Stacks.NormalizationStalkAmbient.normalizationStalkAlgEquivIntegralClosureFractionRing
      X hX P).trans
    (Stacks.NormalizationStalkAmbient.fractionRingReductionAlgEquiv A
      inferInstance).mapIntegralClosure
  obtain ⟨F, -⟩ := normalizationFiberEquivMaximalSpectrum X hX P
  let G : MaximalSpectrum B ≃ ({m₁, m₂} : Set (Ideal B)) :=
    { toFun := fun m => ⟨m.asIdeal, (hmax _).1 m.isMaximal⟩
      invFun := fun m => ⟨m.1, (hmax _).2 m.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_coe_set_eq]
  calc Nat.card ((Stacks.AlgebraicGeometry.Normalization.normalization X hX).base ⁻¹' {P})
      = Nat.card ({m₁, m₂} : Set (Ideal B)) :=
        Nat.card_congr ((Equiv.subtypeEquivRight fun _ => Iff.rfl).trans
          ((F.trans (MaximalSpectrum.congr eS.toRingEquiv)).trans G))
    _ = 2 := by rw [Nat.card_coe_set_eq, Set.ncard_pair hne]

/-- `H^a(K⟦n⟧) ≅ H^{n + a}(K)` in a derived category. -/
private def homologyShiftNatIso (C : Type*) [Category C] [Abelian C]
    [HasDerivedCategory C] (n a a' : ℤ) (h : n + a = a') :
    shiftFunctor (DerivedCategory C) n ⋙ DerivedCategory.homologyFunctor C a ≅
      DerivedCategory.homologyFunctor C a' :=
  Functor.isoWhiskerLeft _ (eqToIso (DerivedCategory.shift_homologyFunctor C a)).symm ≪≫
    (DerivedCategory.homologyFunctor C 0).shiftIso n a a' h ≪≫
    eqToIso (DerivedCategory.shift_homologyFunctor C a')

/-- A complex with no cohomology below `-n` lies in degrees `≥ 0` after the shift by `-n`. -/
private theorem isGE_zero_shift {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (n : ℤ)
    (h : ∀ i < -n, Limits.IsZero ((DerivedCategory.homologyFunctor C i).obj K)) :
    (K⟦-n⟧).IsGE 0 := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact (h (-n + i) (by omega)).of_iso ((homologyShiftNatIso C (-n) i (-n + i) rfl).app K)

open Stacks.Duality Stacks.Duality.FiniteTrace Stacks.Duality.OpenImmersion in
/-- **Affine-local duality for the trace of a finite morphism.** For `g : Y ⟶ X` finite (proper
and affine) between Noetherian schemes, `E ∈ D^{≥0}` bounded below with `a(E) ∈ D^{≥0}`, and `U`
affine, every `Γ(X, U)`-linear map `Γ(Y, g⁻¹U) → Γ(U, H⁰E)` is `b ↦ t_E(b · m)` for exactly one
section `m` of `H⁰(a(E))` over `g⁻¹U`. This generalizes
`Stacks.Duality.FiniteTrace.exists_trace_smul_eq` and
`Stacks.Duality.FiniteTrace.eq_of_trace_smul_eq` from `E = 𝒪_X` to arbitrary `E`. -/
private theorem existsUnique_trace_smul_eq {X Y : Scheme.{u}} (g : Y ⟶ X) [IsProper g]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] [IsAffineHom g]
    (E : quasiCoherentDerivedCategory X) [E.obj.IsGE 0] [((FiniteTrace.twisted g).obj E).obj.IsGE 0]
    (hE : DerivedCategoryB.IsBoundedBelow E.obj) (U : X.Opens) (hU : IsAffineOpen U)
    (l : Γ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit Y.ringCatSheaf), U) →ₗ[Γ(X, U)]
      Γ((DerivedCategory.homologyFunctor X.Modules 0).obj E.obj, U)) :
    ∃! m : Γ(zeroTwisted g E, g ⁻¹ᵁ U),
      ∀ b : Γ(Y, g ⁻¹ᵁ U), (trace (g := g) E).app U (b • m) = l b := by
  haveI : IsLocallyNoetherian X := ‹AlgebraicGeometry.IsNoetherian X›.toIsLocallyNoetherian
  haveI : IsLocallyNoetherian Y := ‹AlgebraicGeometry.IsNoetherian Y›.toIsLocallyNoetherian
  haveI : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion U.ι
  haveI : QuasiSeparatedSpace U := IsLocallyNoetherian.quasiSeparatedSpace
  haveI : IsLocallyNoetherian (g ⁻¹ᵁ U) := isLocallyNoetherian_of_isOpenImmersion (g ⁻¹ᵁ U).ι
  haveI : QuasiSeparatedSpace (g ⁻¹ᵁ U) := IsLocallyNoetherian.quasiSeparatedSpace
  haveI : QuasiSeparated U.ι := (quasiSeparated_iff_quasiSeparatedSpace _).2 ‹_›
  haveI : QuasiSeparated (g ⁻¹ᵁ U).ι := (quasiSeparated_iff_quasiSeparatedSpace _).2 ‹_›
  let E' := (pushU U).obj ((restrictU U).obj E)
  let η : E ⟶ E' := (adjU U).unit.app E
  haveI hR : ((restrictU U).obj E).obj.IsGE 0 :=
    @isGE_derivedRestrict_obj _ _ _ _ _ 0 ‹E.obj.IsGE 0›
  haveI hE' : E'.obj.IsGE 0 := @isGE_derivedPushforward_obj' _ _ _ _ 0 hR
  haveI hRM : IsIso ((restrictionMap g U).app E) :=
    isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ _ _ (isPullback_restrict g U) E hE
  haveI hTR : ((FiniteTrace.twisted (g ∣_ U)).obj ((restrictU U).obj E)).obj.IsGE 0 :=
    haveI : DerivedCategory.TStructure.t.IsGE ((ObjectProperty.ι _).obj ((restrictV g U).obj
        ((FiniteTrace.twisted g).obj E))) 0 :=
      @isGE_derivedRestrict_obj _ _ _ _ _ 0 ‹_›
    DerivedCategory.TStructure.t.isGE_of_iso
      (X := (ObjectProperty.ι _).obj ((restrictV g U).obj ((FiniteTrace.twisted g).obj E)))
      ((ObjectProperty.ι _).mapIso (asIso ((restrictionMap g U).app E))) 0
  haveI hTE' : ((FiniteTrace.twisted g).obj E').obj.IsGE 0 :=
    haveI : DerivedCategory.TStructure.t.IsGE ((ObjectProperty.ι _).obj
        ((FiniteTrace.twisted (g ∣_ U) ⋙ quasiCoherentDerivedPushforward (g ⁻¹ᵁ U).ι
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            ((restrictU U).obj E))) 0 :=
      @isGE_derivedPushforward_obj' _ _ _ _ 0 hTR
    DerivedCategory.TStructure.t.isGE_of_iso (X := (ObjectProperty.ι _).obj
        ((FiniteTrace.twisted (g ∣_ U) ⋙ quasiCoherentDerivedPushforward (g ⁻¹ᵁ U).ι
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj ((restrictU U).obj E)))
      ((ObjectProperty.ι _).mapIso (asIso ((baseChangeMap g U).app ((restrictU U).obj E)))) 0
  -- `(j')^* H⁰(a(η))` is invertible
  have hRV : IsIso ((restrictV g U).map ((FiniteTrace.twisted g).map η)) :=
    (isIso_twistedInverseImageRestrictionMap_app_iff (g ⁻¹ᵁ U).ι (g ∣_ U) g U.ι
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _) (isPullback_restrict g U) _).1
      (isIso_twistedInverseImageRestrictionMap_app_of_isProper (g ⁻¹ᵁ U).ι (g ∣_ U) g U.ι
        (isPullback_restrict g U) E hE)
  let hη := (DerivedCategory.homologyFunctor Y.Modules 0).map ((FiniteTrace.twisted g).map η).hom
  let κ := (DerivedCategory.homologyFunctor X.Modules 0).map η.hom
  have hbij_hη : Function.Bijective (hη.app (g ⁻¹ᵁ U)) := by
    have h₁ : IsIso ((derivedRestrict (g ⁻¹ᵁ U).ι).map ((FiniteTrace.twisted g).map η).hom) :=
      inferInstanceAs (IsIso ((ObjectProperty.ι _).map
        ((restrictV g U).map ((FiniteTrace.twisted g).map η))))
    have h₂ : IsIso ((DerivedCategory.homologyFunctor _ 0).map
        ((derivedRestrict (g ⁻¹ᵁ U).ι).map ((FiniteTrace.twisted g).map η).hom)) := inferInstance
    have : IsIso ((Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι).map hη) :=
      (NatIso.isIso_map_iff
        ((Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι).mapDerivedCategoryHomologyIso 0) _).1 h₂
    exact bijective_app_of_isIso_restrict _ _
  have hbij_κ : Function.Bijective (κ.app U) := by
    have h₁ : η.hom = (derivedRestrictPushforwardAdjunction U.ι).unit.app E.obj :=
      map_liftDerivedRestrictPushforwardAdjunction_unit_app U.ι _ _ _ _ _
    have h₂ : IsIso ((DerivedCategory.homologyFunctor _ 0).map
        ((derivedRestrict U.ι).map η.hom)) := by
      rw [h₁]
      have := isIso_derivedRestrict_map_unit_app U.ι E.obj
      infer_instance
    have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map κ) :=
      (NatIso.isIso_map_iff
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryHomologyIso 0) _).1 h₂
    exact bijective_app_of_isIso_restrict _ _
  have hunitE : IsIso ((Scheme.Modules.restrictAdjunction U.ι).unit.app
      ((DerivedCategory.homologyFunctor X.Modules 0).obj E'.obj)) :=
    isIso_restrictAdjunction_unit_of_iso U (homologyPushforwardIso U ((restrictU U).obj E).obj)
  have hunitP : IsIso ((Scheme.Modules.restrictAdjunction (g ⁻¹ᵁ U).ι).unit.app
      (zeroTwisted g E')) :=
    isIso_restrictAdjunction_unit_of_iso (g ⁻¹ᵁ U)
      ((DerivedCategory.homologyFunctor Y.Modules 0).mapIso ((ObjectProperty.ι _).mapIso (asIso
        ((baseChangeMap g U).app ((restrictU U).obj E)))).symm ≪≫
        homologyPushforwardIso (g ⁻¹ᵁ U)
          ((FiniteTrace.twisted (g ∣_ U)).obj ((restrictU U).obj E)).obj)
  have hnat := trace_naturality (g := g) E E' η
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  have key : ∀ (b : Γ(Y, g ⁻¹ᵁ U)) (n : Γ(zeroTwisted g E, g ⁻¹ᵁ U)),
      (trace (g := g) E').app U (b • hη.app (g ⁻¹ᵁ U) n) =
        κ.app U ((trace (g := g) E).app U (b • n)) := by
    intro b n
    have e₁ := congrArg (fun χ => χ.app U (b • n)) hnat
    simp only [Scheme.Modules.Hom.comp_app] at e₁
    change (trace (g := g) E').app U (hη.app (g ⁻¹ᵁ U) (b • n)) = κ.app U _ at e₁
    rwa [Scheme.Modules.Hom.app_smul] at e₁
  have : (zeroTwisted g E').IsQuasicoherent := ((FiniteTrace.twisted g).obj E').2 0
  have : ((DerivedCategory.homologyFunctor X.Modules 0).obj E'.obj).IsQuasicoherent := E'.2 0
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨φ, hφ⟩ := Stacks.AlgebraicGeometry.exists_hom_app_affineOpen_of_isIso_unit U hU
      hunitE ((appLinear κ U).comp l)
    obtain ⟨ψ, hψ⟩ := (bijective_dualityMap (g := g) E' (SheafOfModules.unit Y.ringCatSheaf)).2 φ
    obtain ⟨m, hm⟩ := hbij_hη.2 (ψ.app (g ⁻¹ᵁ U) (unitOne _))
    refine ⟨m, fun b => hbij_κ.1 ?_⟩
    calc κ.app U ((trace (g := g) E).app U (b • m))
        = (trace (g := g) E').app U (b • hη.app (g ⁻¹ᵁ U) m) := (key b m).symm
      _ = (trace (g := g) E').app U (b • ψ.app (g ⁻¹ᵁ U) (unitOne _)) :=
          congrArg (fun z : Γ(zeroTwisted g E', g ⁻¹ᵁ U) => (trace (g := g) E').app U (b • z)) hm
      _ = (trace (g := g) E').app U (ψ.app (g ⁻¹ᵁ U) b) :=
          congrArg ((trace (g := g) E').app U) (app_eq_smul_app_one ψ _ b).symm
      _ = (dualityMap (g := g) E' ψ).app U b := (dualityMap_app_eq g U E' ψ b).symm
      _ = φ.app U b := by rw [hψ]
      _ = κ.app U (l b) :=
          (hφ b).trans ((LinearMap.comp_apply _ _ _).trans (appLinear_apply κ U _))
  · intro m m₀ hm hm₀
    obtain ⟨φ₁, hφ₁⟩ := Stacks.AlgebraicGeometry.exists_hom_app_affineOpen_of_isIso_unit
      (g ⁻¹ᵁ U) hV hunitP (N := SheafOfModules.unit Y.ringCatSheaf)
      (LinearMap.toSpanSingleton Γ(Y, g ⁻¹ᵁ U) _ (hη.app (g ⁻¹ᵁ U) m))
    obtain ⟨φ₂, hφ₂⟩ := Stacks.AlgebraicGeometry.exists_hom_app_affineOpen_of_isIso_unit
      (g ⁻¹ᵁ U) hV hunitP (N := SheafOfModules.unit Y.ringCatSheaf)
      (LinearMap.toSpanSingleton Γ(Y, g ⁻¹ᵁ U) _ (hη.app (g ⁻¹ᵁ U) m₀))
    have hdφ : dualityMap (g := g) E' φ₁ = dualityMap (g := g) E' φ₂ := by
      refine Stacks.AlgebraicGeometry.hom_ext_of_app_affineOpen_of_isIso_unit U hU hunitE
        fun b => ?_
      refine (dualityMap_app_eq g U E' φ₁ b).trans
        (Eq.trans ?_ (dualityMap_app_eq g U E' φ₂ b).symm)
      refine (congrArg _ (hφ₁ b)).trans (Eq.trans ?_ (congrArg _ (hφ₂ b)).symm)
      exact (key b m).trans ((congrArg (κ.app U) ((hm b).trans (hm₀ b).symm)).trans
        (key b m₀).symm)
    have hφ : φ₁ = φ₂ :=
      (bijective_dualityMap (g := g) E' (SheafOfModules.unit Y.ringCatSheaf)).1 hdφ
    have h₃ := (hφ₁ (unitOne _)).symm.trans
      ((congrArg (fun φ => φ.app (g ⁻¹ᵁ U) (unitOne _)) hφ).trans (hφ₂ (unitOne _)))
    have h₄ : hη.app (g ⁻¹ᵁ U) m = hη.app (g ⁻¹ᵁ U) m₀ := by
      have e₁ := LinearMap.toSpanSingleton_apply_one Γ(Y, g ⁻¹ᵁ U) _ (hη.app (g ⁻¹ᵁ U) m)
      have e₂ := LinearMap.toSpanSingleton_apply_one Γ(Y, g ⁻¹ᵁ U) _ (hη.app (g ⁻¹ᵁ U) m₀)
      exact e₁.symm.trans (h₃.trans e₂)
    exact hbij_hη.1 h₄

/-- **The trace of a finite morphism on dualizing sheaves.** Let `ν : Y ⟶ X` be finite, `ω_X` a
dualizing sheaf of `X` over `k` and `ω_Y` one of `Y` over `k` through `ν`, both of pure dimension
`n`. There is `T : ν_* ω_Y ⟶ ω_X` such that on every affine open `V ⊆ X`, every
`Γ(X, V)`-linear map `Γ(ν⁻¹V, 𝒪_Y) → Γ(V, ω_X)` is `b ↦ T(b · w)` for exactly one
`w ∈ Γ(ν⁻¹V, ω_Y)`. -/
private theorem exists_trace_existsUnique_smul_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (ν : Y ⟶ X) [IsFinite ν] (n : ℕ)
    (ωX : X.Modules) (hωX : IsDualizingSheaf sX n ωX)
    (ωY : Y.Modules) (hωY : IsDualizingSheaf (ν ≫ sX) n ωY) :
    ∃ T : (Scheme.Modules.pushforward ν).obj ωY ⟶ ωX,
      ∀ V : X.Opens, IsAffineOpen V →
        ∀ l : Γ((Scheme.Modules.pushforward ν).obj (SheafOfModules.unit Y.ringCatSheaf), V)
            →ₗ[Γ(X, V)] Γ(ωX, V),
          ∃! w : Γ(ωY, ν ⁻¹ᵁ V), ∀ b : Γ(Y, ν ⁻¹ᵁ V), T.app V (b • w) = l b := by
  obtain ⟨hNX, hLX⟩ := isNoetherian_and_locallyOfFiniteType_of_isDualizingSheaf hωX
  obtain ⟨hNY, hLY⟩ := isNoetherian_and_locallyOfFiniteType_of_isDualizingSheaf hωY
  haveI : IsLocallyNoetherian X := hNX.toIsLocallyNoetherian
  haveI : IsLocallyNoetherian Y := hNY.toIsLocallyNoetherian
  haveI : IsSeparated ν := IsSeparated.of_isAffineHom ν
  obtain ⟨eX⟩ := hωX.nonempty_iso_homology
  obtain ⟨eY⟩ := hωY.nonempty_iso_homology
  obtain ⟨-, -, hKX⟩ := normalizedDualizingComplexOverField_spec sX
  obtain ⟨-, -, hKY⟩ := normalizedDualizingComplexOverField_spec (ν ≫ sX)
  have vX := (hKX n hωX.1).1
  have vY := (hKY n hωY.1).1
  have e0 := Stacks.Duality.NormalizedOnOpens.twistedInverseImageObjIsoNagata (f := ν) rfl
    (Stacks.Duality.isDualizingComplex_derivedStructureSheafPlus_of_field k)
    (normalizedDualizingComplexOverField (ν ≫ sX)) (normalizedDualizingComplexOverField sX)
  letI := (Stacks.Duality.FiniteTrace.twistedAdj ν).rightAdjointCommShift ℤ
  let KX := (normalizedDualizingComplexOverField sX).complex.obj
  let KY := (normalizedDualizingComplexOverField (ν ≫ sX)).complex.obj
  let E := KX⟦(-(n : ℤ))⟧
  let e1 : (Stacks.Duality.FiniteTrace.twisted ν).obj E ≅ KY⟦(-(n : ℤ))⟧ :=
    ((Stacks.Duality.FiniteTrace.twisted ν).commShiftIso (-(n : ℤ))).app _ ≪≫
      (shiftFunctor _ (-(n : ℤ))).mapIso e0
  let iX : E.obj ≅ KX.obj⟦(-(n : ℤ))⟧ := ((ObjectProperty.ι _).commShiftIso (-(n : ℤ))).app KX
  let iY : ((Stacks.Duality.FiniteTrace.twisted ν).obj E).obj ≅ KY.obj⟦(-(n : ℤ))⟧ :=
    (ObjectProperty.ι _).mapIso e1 ≪≫ ((ObjectProperty.ι _).commShiftIso (-(n : ℤ))).app KY
  haveI hE : E.obj.IsGE 0 :=
    haveI := isGE_zero_shift _ _ fun i hi => vX i (Or.inl (by omega))
    DerivedCategory.TStructure.t.isGE_of_iso iX.symm 0
  haveI hTE : ((Stacks.Duality.FiniteTrace.twisted ν).obj E).obj.IsGE 0 :=
    haveI := isGE_zero_shift _ _ fun i hi => vY i (Or.inl (by omega))
    DerivedCategory.TStructure.t.isGE_of_iso iY.symm 0
  let hX0 : (DerivedCategory.homologyFunctor X.Modules 0).obj E.obj ≅ ωX :=
    (DerivedCategory.homologyFunctor X.Modules 0).mapIso iX ≪≫
      (homologyShiftNatIso X.Modules (-(n : ℤ)) 0 (-(n : ℤ)) (by simp)).app KX.obj ≪≫ eX.symm
  let hY0 : Stacks.Duality.FiniteTrace.zeroTwisted ν E ≅ ωY :=
    (DerivedCategory.homologyFunctor Y.Modules 0).mapIso iY ≪≫
      (homologyShiftNatIso Y.Modules (-(n : ℤ)) 0 (-(n : ℤ)) (by simp)).app KY.obj ≪≫ eY.symm
  have hbb : DerivedCategoryB.IsBoundedBelow E.obj :=
    ⟨0, fun i hi => DerivedCategory.isZero_of_isGE E.obj 0 i hi⟩
  have hinvhom : ∀ {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N) (W : Z.Opens) (x : Γ(N, W)),
      e.hom.app W (e.inv.app W x) = x := fun e W x =>
    congrArg (fun φ : _ ⟶ _ => Scheme.Modules.Hom.app φ W x) e.inv_hom_id
  have hhominv : ∀ {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N) (W : Z.Opens) (x : Γ(M, W)),
      e.inv.app W (e.hom.app W x) = x := fun e W x =>
    congrArg (fun φ : _ ⟶ _ => Scheme.Modules.Hom.app φ W x) e.hom_inv_id
  refine ⟨(Scheme.Modules.pushforward ν).map hY0.inv ≫ Stacks.Duality.FiniteTrace.trace E ≫
    hX0.hom, fun V hV l => ?_⟩
  let l' := (Stacks.Duality.FiniteTrace.appLinear hX0.inv V).comp l
  obtain ⟨m, hm, hmu⟩ := existsUnique_trace_smul_eq ν E hbb V hV l'
  have hT : ∀ x : Γ(ωY, ν ⁻¹ᵁ V),
      ((Scheme.Modules.pushforward ν).map hY0.inv ≫ Stacks.Duality.FiniteTrace.trace E ≫
        hX0.hom).app V x =
      hX0.hom.app V ((Stacks.Duality.FiniteTrace.trace E).app V (hY0.inv.app (ν ⁻¹ᵁ V) x)) :=
    fun x => rfl
  refine ⟨hY0.hom.app (ν ⁻¹ᵁ V) m, fun b => ?_, fun w hw => ?_⟩
  · rw [hT, ← Scheme.Modules.Hom.app_smul, hhominv, hm b]
    exact hinvhom hX0 V (l b)
  · have hw' : ∀ b : Γ(Y, ν ⁻¹ᵁ V),
        (Stacks.Duality.FiniteTrace.trace E).app V (b • hY0.inv.app (ν ⁻¹ᵁ V) w) = l' b := by
      intro b
      have := congrArg (hX0.inv.app V) (hw b)
      rwa [hT, hhominv, Scheme.Modules.Hom.app_smul] at this
    rw [← hmu _ hw', hinvhom]

/-- **Finite duality for the normalization, on affine opens.** There is a morphism
`T : ν_* ω_{X^ν} ⟶ ω_X` such that for every affine open `V ⊆ X` the map
`w ↦ (b ↦ T(b · w))` is a bijection
`Γ(ν⁻¹V, ω_{X^ν}) ≃ Hom_{Γ(V, 𝒪_X)}(Γ(ν⁻¹V, 𝒪_{X^ν}), Γ(V, ω_X))`. -/
private theorem exists_globalTrace {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (n : ℕ)
    (ωX : X.Modules) (hωX : IsDualizingSheaf sX n ωX)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (ων : (Stacks.AlgebraicGeometry.Normalization.normalizationScheme X hX).Modules)
    (hων : IsDualizingSheaf (Stacks.AlgebraicGeometry.Normalization.normalization X hX ≫ sX) n ων) :
    ∃ T : (Scheme.Modules.pushforward
        (Stacks.AlgebraicGeometry.Normalization.normalization X hX)).obj ων ⟶ ωX,
      ∀ V : X.Opens, IsAffineOpen V →
        ∀ l : Γ((Scheme.Modules.pushforward
            (Stacks.AlgebraicGeometry.Normalization.normalization X hX)).obj
              (SheafOfModules.unit
                (Stacks.AlgebraicGeometry.Normalization.normalizationScheme X hX).ringCatSheaf), V)
            →ₗ[Γ(X, V)] Γ(ωX, V),
          ∃! w : Γ(ων, Stacks.AlgebraicGeometry.Normalization.normalization X hX ⁻¹ᵁ V),
            ∀ b : Γ(Stacks.AlgebraicGeometry.Normalization.normalizationScheme X hX,
              Stacks.AlgebraicGeometry.Normalization.normalization X hX ⁻¹ᵁ V),
              T.app V (b • w) = l b := by
  obtain ⟨-, hLX⟩ := isNoetherian_and_locallyOfFiniteType_of_isDualizingSheaf hωX
  haveI : IsFinite (Stacks.AlgebraicGeometry.Normalization.normalization X hX) :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
  exact exists_trace_existsUnique_smul_eq sX _ n ωX hωX ων hων

/-- **If `B/A` is simple, `𝔪₁ ∩ 𝔪₂` lies in `A`.** Let `A ⊆ B` be an integral
extension of a local ring with `B/A` a simple `A`-module, and let `𝔪₁ ≠ 𝔪₂` be maximal ideals of
`B`. Then `𝔪₁ ∩ 𝔪₂ ⊆ A`. -/
private theorem inf_le_range_of_isSimpleModule {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (m₁ m₂ : Ideal B) [m₁.IsMaximal]
    [m₂.IsMaximal] (hne : m₁ ≠ m₂)
    (hsimple : IsSimpleModule A (B ⧸ LinearMap.range (Algebra.linearMap A B))) :
    (m₁ ⊓ m₂).restrictScalars A ≤ LinearMap.range (Algebra.linearMap A B) := by
  set N := LinearMap.range (Algebra.linearMap A B)
  rcases IsSimpleOrder.eq_bot_or_eq_top ((m₁ ⊓ m₂).restrictScalars A |>.map N.mkQ) with h | h
  · intro x hx
    have : N.mkQ x = 0 := by
      have : N.mkQ x ∈ ((m₁ ⊓ m₂).restrictScalars A).map N.mkQ := ⟨x, hx, rfl⟩
      rwa [h, Submodule.mem_bot] at this
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  · exfalso
    have hJ : N ⊔ (m₁ ⊓ m₂).restrictScalars A = ⊤ := (Submodule.map_mkQ_eq_top _ _).1 h
    have hcop : m₁ ⊔ m₂ = ⊤ := Ideal.IsMaximal.coprime_of_ne ‹_› ‹_› hne
    obtain ⟨e₁, he₁, e₂, he₂, he⟩ :=
      Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : B) ∈ m₁ ⊔ m₂)
    have hmem : e₂ ∈ N ⊔ (m₁ ⊓ m₂).restrictScalars A := hJ ▸ Submodule.mem_top
    obtain ⟨x, ⟨a, rfl⟩, j, hj, hxj⟩ := Submodule.mem_sup.1 hmem
    have hcomap : ∀ (m : Ideal B) [m.IsMaximal],
        m.comap (algebraMap A B) = IsLocalRing.maximalIdeal A :=
      fun m _ => IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal m)
    have ha₂ : algebraMap A B a ∈ m₂ := by
      have : algebraMap A B a = e₂ - j := by rw [← hxj]; simp
      rw [this]; exact m₂.sub_mem he₂ hj.2
    have ha₁ : algebraMap A B a ∈ m₁ := by
      have : a ∈ m₂.comap (algebraMap A B) := ha₂
      rwa [hcomap m₂, ← hcomap m₁] at this
    have : e₂ ∈ m₁ := by
      rw [← hxj]; exact m₁.add_mem (by simpa using ha₁) hj.1
    have h1 : (1 : B) ∈ m₁ := he ▸ m₁.add_mem he₁ this
    exact (‹m₁.IsMaximal›.ne_top) ((Ideal.eq_top_iff_one _).2 h1)

set_option hygiene false in
/-- The normalization `ν : X^ν ⟶ X`. -/
local notation "νX" => Stacks.AlgebraicGeometry.Normalization.normalization X hX

set_option hygiene false in
/-- The normalization scheme `X^ν`. -/
local notation "Xν" => Stacks.AlgebraicGeometry.Normalization.normalizationScheme X hX

/-- **A free rank-one restriction gives a local generator.** If `M|_W ≅ 𝒪_W`, the section of `M`
over `W` corresponding to `1` generates `M` on `W`. -/
private theorem exists_isLocalGenerator_of_restrict_iso_free {Y : Scheme.{u}} (M : Y.Modules)
    (W : Y.Opens) (e : M.restrict W.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin 1))) :
    ∃ g : Γ(M, W), IsLocalGenerator M g := by
  let φ : M.restrict W.ι ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf :=
    e ≪≫ Limits.coproductUniqueIso (fun _ : ULift.{u} (Fin 1) =>
      SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
  let ψ := φ.inv
  have hψ : ∀ V : (W : Scheme.{u}).Opens, Function.Bijective (ψ.app V) := by
    intro V
    refine ⟨fun a b h => ?_, fun m => ⟨φ.hom.app V m, ?_⟩⟩
    · have := congrArg (φ.hom.app V) h
      have e1 := congrArg (fun χ => Scheme.Modules.Hom.app χ V a) φ.inv_hom_id
      have e2 := congrArg (fun χ => Scheme.Modules.Hom.app χ V b) φ.inv_hom_id
      simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at e1 e2
      exact e1.symm.trans (this.trans e2)
    · exact congrArg (fun χ => Scheme.Modules.Hom.app χ V m) φ.hom_inv_id
  let n : Γ(M.restrict W.ι, ⊤) := ψ.app ⊤ (Stacks.Duality.FiniteTrace.unitOne ⊤)
  have hgen : IsLocalGenerator M (V := W.ι ''ᵁ ⊤) n := by
    intro V' hV'
    obtain ⟨V, rfl⟩ : ∃ V : (W : Scheme.{u}).Opens, W.ι ''ᵁ V = V' :=
      ⟨W.ι ⁻¹ᵁ V', by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
        exact inf_eq_right.2 (hV'.trans (by simp))⟩
    have hres : M.presheaf.map (homOfLE hV').op n =
        ψ.app V (Stacks.Duality.FiniteTrace.unitOne V) := by
      have := modulesHom_app_map ψ (le_top : V ≤ ⊤) (Stacks.Duality.FiniteTrace.unitOne ⊤)
      refine Eq.trans ?_ (this.symm.trans ?_)
      · rfl
      · congr 1
        change (W : Scheme.{u}).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (1 : Γ(W, ⊤)) = 1
        exact map_one _
    have key : ∀ r : Γ(Y, W.ι ''ᵁ V), r • M.presheaf.map (homOfLE hV').op n =
        ψ.app V ((W.ι.appIso V).hom r) := by
      intro r
      rw [hres]
      refine Eq.trans ?_ (Stacks.Duality.FiniteTrace.app_eq_smul_app_one ψ V _).symm
      exact congrArg (fun s : Γ(Y, W.ι ''ᵁ V) =>
        s • @id Γ(M, W.ι ''ᵁ V) (ψ.app V (Stacks.Duality.FiniteTrace.unitOne V)))
        (Iso.hom_inv_id_apply (W.ι.appIso V) r).symm
    refine ⟨fun a b hab => ?_, fun m => ?_⟩
    · have h1 := (hψ V).1 ((key a).symm.trans (hab.trans (key b)))
      have h2 := congrArg (W.ι.appIso V).inv h1
      rwa [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply] at h2
    · obtain ⟨t, rfl⟩ := (hψ V).2 m
      refine ⟨(W.ι.appIso V).inv t, ?_⟩
      refine (key _).trans ?_
      exact congrArg (ψ.app V) (Iso.inv_hom_id_apply (W.ι.appIso V) t)
  have hle : W ≤ W.ι ''ᵁ ⊤ := by simp
  exact ⟨_, hgen.restrict hle⟩

/-- **Generating is local.** A section that generates `M` on a neighbourhood of every point of
`O` generates `M` on `O`. -/
private theorem isLocalGenerator_of_forall_mem {Y : Scheme.{u}} (M : Y.Modules) {O : Y.Opens}
    (m : Γ(M, O))
    (h : ∀ x ∈ O, ∃ (V : Y.Opens) (hV : V ≤ O), x ∈ V ∧
      IsLocalGenerator M (M.presheaf.map (homOfLE hV).op m)) :
    IsLocalGenerator M m := by
  classical
  intro V' hV'
  choose Vx hVx hxV hgen using fun x : V' => h x.1 (hV' x.2)
  have hbij : ∀ (x : V') (W : Y.Opens) (hW : W ≤ Vx x),
      Function.Bijective fun r : Γ(Y, W) => r • M.presheaf.map (homOfLE (hW.trans (hVx x))).op m :=
    fun x W hW => by simpa only [MMP.Intersection.modules_map_map] using hgen x W hW
  let L : V' → Y.Opens := fun x => V' ⊓ Vx x
  have hLV : ∀ x, L x ≤ V' := fun _ => inf_le_left
  have hLO : ∀ x, L x ≤ Vx x := fun _ => inf_le_right
  have hcov : V' ≤ iSup L := fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hy, hxV _⟩
  have hres : ∀ (W W' : Y.Opens) (hW : W ≤ W') (hW' : W' ≤ O) (r : Γ(Y, W')),
      M.presheaf.map (homOfLE hW).op (r • M.presheaf.map (homOfLE hW').op m) =
        Y.presheaf.map (homOfLE hW).op r • M.presheaf.map (homOfLE (hW.trans hW')).op m := by
    intro W W' hW hW' r
    rw [Scheme.Modules.map_smul, MMP.Intersection.modules_map_map]
  refine ⟨fun a b hab => ?_, fun s => ?_⟩
  · refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf L V' (fun x => homOfLE (hLV x)) hcov a b
      (fun x => (hbij x (L x) (hLO x)).1 ?_)
    have := congrArg (M.presheaf.map (homOfLE (hLV x)).op) hab
    simp only at this
    rwa [hres _ _ _ hV', hres _ _ _ hV'] at this
  · -- local coefficients
    choose c hc using fun x : V' =>
      (hbij x (L x) (hLO x)).2 (M.presheaf.map (homOfLE (hLV x)).op s)
    have hcompat : TopCat.Presheaf.IsCompatible Y.sheaf.1 L c := by
      intro x y
      apply (hbij x (L x ⊓ L y) (inf_le_left.trans (hLO x))).1
      simp only
      have hx := congrArg (M.presheaf.map (homOfLE (inf_le_left : L x ⊓ L y ≤ L x)).op) (hc x)
      have hy := congrArg (M.presheaf.map (homOfLE (inf_le_right : L x ⊓ L y ≤ L y)).op) (hc y)
      simp only at hx hy
      rw [hres _ _ _ ((hLO x).trans (hVx x)), MMP.Intersection.modules_map_map] at hx
      rw [hres _ _ _ ((hLO y).trans (hVx y)), MMP.Intersection.modules_map_map] at hy
      exact (hx.trans hy.symm).trans rfl
    obtain ⟨r, hr, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf L V'
      (fun x => homOfLE (hLV x)) hcov c hcompat
    let r' : Γ(Y, V') := r
    refine ⟨r', ?_⟩
    refine TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf _).obj M) L V'
      (fun x => homOfLE (hLV x)) hcov _ _ (fun x => ?_)
    change M.presheaf.map (homOfLE (hLV x)).op (r' • M.presheaf.map (homOfLE hV').op m) =
      M.presheaf.map (homOfLE (hLV x)).op s
    rw [hres _ _ _ hV', ← hc x]
    congr 1
    exact hr x

/-- **The normalization is birational over affine opens.** Every section of `𝒪_{X^ν}` over
`ν⁻¹U`, `U` affine, is a fraction of sections of `𝒪_X` over `U` with a non-zero-divisor
denominator. -/
private theorem exists_mul_eq_app_of_isAffineOpen {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hFA : SatisfiesFA261 sX)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) (c : Γ(Xν, νX ⁻¹ᵁ U)) :
    ∃ r : Γ(X, U), (νX).app U r ∈ nonZeroDivisors Γ(Xν, νX ⁻¹ᵁ U) ∧
      ∃ r' : Γ(X, U), (νX).app U r * c = (νX).app U r' := by
  haveI : IsReduced X := hFA.2.2.1
  letI : Algebra Γ(X, U) Γ(Xν, νX ⁻¹ᵁ U) := ((νX).app U).hom.toAlgebra
  obtain ⟨e⟩ : Nonempty (Γ(Xν, νX ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) (FractionRing Γ(X, U))) :=
    ⟨AlgebraicGeometry.normalizationSectionsAlgEquivIntegralClosureFractionRing hX U hU⟩
  obtain ⟨⟨r', r⟩, hrr⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, U))
    (e c : FractionRing Γ(X, U))
  simp only at hrr
  have hal : ∀ a : Γ(X, U), (νX).app U a = algebraMap Γ(X, U) Γ(Xν, νX ⁻¹ᵁ U) a := fun _ => rfl
  have hunit : IsUnit (algebraMap Γ(X, U) (FractionRing Γ(X, U)) r) :=
    IsLocalization.map_units _ r
  have hco : ∀ a : Γ(X, U), ((e (algebraMap Γ(X, U) _ a) : integralClosure _ _) :
      FractionRing Γ(X, U)) = algebraMap Γ(X, U) (FractionRing Γ(X, U)) a := by
    intro a; rw [AlgEquiv.commutes]; rfl
  refine ⟨r, ?_, r', ?_⟩
  · rw [hal, mem_nonZeroDivisors_iff_right]
    intro z hz
    apply e.injective
    apply Subtype.ext
    have := congrArg (fun w => ((e w : integralClosure _ _) : FractionRing Γ(X, U))) hz
    simp only [map_mul, Subalgebra.coe_mul, map_zero, Subalgebra.coe_zero, hco] at this
    rw [map_zero, Subalgebra.coe_zero]
    exact (hunit.mul_left_eq_zero).1 this
  · rw [hal, hal]
    apply e.injective
    apply Subtype.ext
    simp only [map_mul, Subalgebra.coe_mul, hco]
    rw [mul_comm, hrr]

/-- The comorphism of the normalization is injective on sections. -/
private theorem app_injective_normalization {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hFA : SatisfiesFA261 sX)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U : X.Opens) : Function.Injective ((νX).app U) := by
  haveI : IsReduced X := hFA.2.2.1
  have hmono := Stacks.AlgebraicGeometry.Normalization.mono_toRingCatSheafHom_normalization X hX
  have := ((TopCat.Sheaf.forget RingCat.{u} X).map_mono
    (Scheme.Hom.toRingCatSheafHom (νX)))
  have := (NatTrans.mono_iff_mono_app _).1 this (op U)
  have h := (ConcreteCategory.mono_iff_injective_of_preservesPullback _).1 this
  exact h

/-- A morphism out of a pushforward is linear over the comorphism. -/
private theorem pushforward_hom_app_smul {X Y : Scheme.{u}} (f : Y ⟶ X) {M : Y.Modules}
    {N : X.Modules} (φ : (Scheme.Modules.pushforward f).obj M ⟶ N) (U : X.Opens) (r : Γ(X, U))
    (x : Γ(M, f ⁻¹ᵁ U)) : φ.app U (f.app U r • x) = r • φ.app U x :=
  Scheme.Modules.Hom.app_smul φ r x

/-- **The trace on a generator is multiplication by `θ`.** If `τ(g) = θ · s` on an affine `U`,
then `τ(c · g) = a · s` with `ν^♯ a = ν^♯θ · c`, for every section `c` of `𝒪_{X^ν}` over
`ν⁻¹U`. -/
private theorem exists_trace_smul_eq_mul {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hFA : SatisfiesFA261 sX) (ωX : X.Modules)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (ων : (Xν).Modules)
    (τ : (Scheme.Modules.pushforward νX).obj ων ⟶ ωX)
    {U : X.Opens} (hU : IsAffineOpen U) (sU : Γ(ωX, U)) (hsU : IsLocalGenerator ωX sU)
    (g : Γ(ων, νX ⁻¹ᵁ U)) (θ : Γ(X, U)) (hθ : τ.app U g = θ • sU)
    (c : Γ(Xν, νX ⁻¹ᵁ U)) :
    ∃ a : Γ(X, U), (νX).app U a = (νX).app U θ * c ∧ τ.app U (c • g) = a • sU := by
  have hbij := hsU U le_rfl
  simp only [MMP.Intersection.modules_map_id] at hbij
  obtain ⟨a, ha⟩ := hbij.2 (τ.app U (c • g))
  replace ha : a • sU = τ.app U (c • g) := ha
  refine ⟨a, ?_, ha.symm⟩
  obtain ⟨r, hr, r', hrr'⟩ := exists_mul_eq_app_of_isAffineOpen sX hFA hX hU c
  have h1 : (r * a) • sU = (r' * θ) • sU := by
    rw [mul_smul, ha, ← pushforward_hom_app_smul, smul_smul, hrr', pushforward_hom_app_smul, hθ,
      mul_smul]
  have h2 := congrArg (fun z => (νX).app U z) (hbij.1 h1)
  simp only at h2
  rw [map_mul, map_mul, ← hrr'] at h2
  exact (mul_cancel_left_mem_nonZeroDivisors hr).1 (h2.trans (by ring))

/-- Restriction commutes with the comorphism of a morphism of schemes. -/
private theorem app_res {X Y : Scheme.{u}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U)
    (a : Γ(X, U)) :
    Y.presheaf.map (homOfLE (f.preimage_mono h)).op (f.app U a) =
      f.app V (X.presheaf.map (homOfLE h).op a) :=
  (congrArg (fun φ => φ.hom a) (f.naturality (homOfLE h).op)).symm

/-- A morphism out of a pushforward commutes with restriction. -/
private theorem pushforward_hom_app_res {X Y : Scheme.{u}} (f : Y ⟶ X) {M : Y.Modules}
    {N : X.Modules} (φ : (Scheme.Modules.pushforward f).obj M ⟶ N) {U V : X.Opens} (h : V ≤ U)
    (x : Γ(M, f ⁻¹ᵁ U)) :
    φ.app V (M.presheaf.map (homOfLE (f.preimage_mono h)).op x) =
      N.presheaf.map (homOfLE h).op (φ.app U x) :=
  modulesHom_app_map φ h x

/-- **On an open `B ⊆ U ∩ W'`, the trace agrees on `(ν^♯θ · c) · t` and `c · g`.** -/
private theorem trace_smul_res_eq {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hFA : SatisfiesFA261 sX) (ωX : X.Modules)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (ων : (Xν).Modules)
    (τ : (Scheme.Modules.pushforward νX).obj ων ⟶ ωX)
    {W : X.Opens} (s : Γ(ωX, W)) {W' : X.Opens} (hW' : W' ≤ W)
    (t : Γ(ων, νX ⁻¹ᵁ W')) (ht : τ.app W' t = ωX.presheaf.map (homOfLE hW').op s)
    {U : X.Opens} (hUW : U ≤ W) (hU : IsAffineOpen U)
    (hsU : IsLocalGenerator ωX (ωX.presheaf.map (homOfLE hUW).op s))
    (g : Γ(ων, νX ⁻¹ᵁ U)) (θ : Γ(X, U))
    (hθ : τ.app U g = θ • ωX.presheaf.map (homOfLE hUW).op s)
    {B : X.Opens} (hBU : B ≤ U) (hBW : B ≤ W') (c : Γ(Xν, νX ⁻¹ᵁ U)) :
    τ.app B ((Xν).presheaf.map (homOfLE ((νX).preimage_mono hBU)).op ((νX).app U θ * c) •
        ων.presheaf.map (homOfLE ((νX).preimage_mono hBW)).op t) =
      τ.app B (ων.presheaf.map (homOfLE ((νX).preimage_mono hBU)).op (c • g)) := by
  obtain ⟨a, ha, hag⟩ := exists_trace_smul_eq_mul sX hFA ωX hX ων τ hU _ hsU g θ hθ c
  rw [← ha, app_res, pushforward_hom_app_smul, pushforward_hom_app_res, ht,
    pushforward_hom_app_res, hag, Scheme.Modules.map_smul, MMP.Intersection.modules_map_map,
    MMP.Intersection.modules_map_map]
  all_goals assumption

/-- **The pulled-back section is `g/θ` near the generic points.** -/
private theorem exists_smul_eq_generator {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hFA : SatisfiesFA261 sX) (ωX : X.Modules)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (ων : (Xν).Modules)
    (τ : (Scheme.Modules.pushforward νX).obj ων ⟶ ωX)
    (T : (Scheme.Modules.pushforward νX).obj ων ⟶ ωX)
    (hT : ∀ V : X.Opens, IsAffineOpen V →
      ∀ l : Γ((Scheme.Modules.pushforward νX).obj (SheafOfModules.unit (Xν).ringCatSheaf), V)
          →ₗ[Γ(X, V)] Γ(ωX, V),
        ∃! w : Γ(ων, νX ⁻¹ᵁ V), ∀ b : Γ(Xν, νX ⁻¹ᵁ V), T.app V (b • w) = l b)
    (a₀ : Γ(Xν, ⊤)) (ha₀ : ∀ (V : X.Opens) (x : Γ(ων, νX ⁻¹ᵁ V)),
      T.app V x = τ.app V
        (((Xν).presheaf.map (homOfLE (le_top : νX ⁻¹ᵁ V ≤ ⊤)).op a₀ : Γ(Xν, νX ⁻¹ᵁ V)) • x))
    (P : X) {W : X.Opens} (s : Γ(ωX, W))
    {W' : X.Opens} (hW' : W' ≤ W)
    (hW'gen : ∀ η : X, closure {η} ∈ irreducibleComponents X → η ⤳ P → η ∈ W')
    (t : Γ(ων, νX ⁻¹ᵁ W')) (ht : τ.app W' t = ωX.presheaf.map (homOfLE hW').op s)
    {U : X.Opens} (hPU : P ∈ U) (hUW : U ≤ W) (hU : IsAffineOpen U)
    (hsU : IsLocalGenerator ωX (ωX.presheaf.map (homOfLE hUW).op s))
    (g : Γ(ων, νX ⁻¹ᵁ U)) (θ : Γ(X, U))
    (hθ : τ.app U g = θ • ωX.presheaf.map (homOfLE hUW).op s)
    (y : Xν) (hy : νX y = P) :
    ∃ (V' : (Xν).Opens) (hV' : V' ≤ νX ⁻¹ᵁ U) (hW : V' ≤ νX ⁻¹ᵁ W'),
      (∀ η : Xν, closure {η} ∈ irreducibleComponents Xν → η ⤳ y → η ∈ V') ∧
      (Xν).presheaf.map (homOfLE hV').op ((νX).app U θ) • ων.presheaf.map (homOfLE hW).op t =
        ων.presheaf.map (homOfLE hV').op g := by
  classical
  haveI : LocallyOfFiniteType sX := hFA.1
  haveI : IsFinite (νX) :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
  have hUν : IsAffineOpen (νX ⁻¹ᵁ U) := hU.preimage (νX)
  refine ⟨νX ⁻¹ᵁ (U ⊓ W'), (νX).preimage_mono inf_le_left, (νX).preimage_mono inf_le_right,
    ?_, ?_⟩
  · intro η hη hηy
    have h1 : (νX) η ⤳ P := hy ▸ hηy.map (νX).continuous
    exact ⟨h1.mem_open U.isOpen hPU,
      hW'gen _ (AlgebraicGeometry.Scheme.normalization_mem_genericPoints X hX hη) h1⟩
  -- the identity on each basic open `B ⊆ U ∩ W'`
  have key : ∀ (h : Γ(X, U)) (hBD : X.basicOpen h ≤ U ⊓ W'),
      (Xν).presheaf.map (homOfLE ((νX).preimage_mono (hBD.trans inf_le_left))).op
          ((νX).app U θ) •
        ων.presheaf.map (homOfLE ((νX).preimage_mono (hBD.trans inf_le_right))).op t =
      ων.presheaf.map (homOfLE ((νX).preimage_mono (hBD.trans inf_le_left))).op g := by
    intro h hBD
    set B := X.basicOpen h
    have hBU : B ≤ U := hBD.trans inf_le_left
    have hBW : B ≤ W' := hBD.trans inf_le_right
    set L := (Xν).presheaf.map (homOfLE ((νX).preimage_mono hBU)).op ((νX).app U θ) •
        ων.presheaf.map (homOfLE ((νX).preimage_mono hBW)).op t
    set R := ων.presheaf.map (homOfLE ((νX).preimage_mono hBU)).op g
    have hτLR : ∀ b' : Γ(Xν, νX ⁻¹ᵁ B), τ.app B (b' • L) = τ.app B (b' • R) := by
      intro b'
      have hpre : νX ⁻¹ᵁ B = (Xν).basicOpen ((νX).app U h) := Scheme.preimage_basicOpen _ h
      obtain ⟨m, y, hy'⟩ := exists_eq_pow_mul_of_isAffineOpen (Xν) (νX ⁻¹ᵁ U) hUν
        ((νX).app U h) ((Xν).presheaf.map (homOfLE hpre.ge).op b')
      have hy'' := congrArg ((Xν).presheaf.map (homOfLE hpre.le).op) hy'
      simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_mul, map_pow,
        presheaf_map_map, MMP.Intersection.presheaf_map_id] at hy''
      rw [app_res (νX) hBU] at hy''
      have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h ^ m) :=
        (X.toRingedSpace.isUnit_res_basicOpen h).pow m
      rw [← hu.smul_left_cancel, ← pushforward_hom_app_smul, ← pushforward_hom_app_smul,
        smul_smul, smul_smul, map_pow, ← hy'']
      simp only [L, R, smul_smul, ← map_mul, ← Scheme.Modules.map_smul]
      rw [← hy'', ← Scheme.Modules.map_smul, mul_comm]
      exact trace_smul_res_eq sX hFA ωX hX ων τ s hW' t ht hUW hU hsU g θ hθ hBU hBW y
    refine sub_eq_zero.1 ((hT B (hU.basicOpen h) 0).unique (fun b => ?_) (fun b => ?_))
    · rw [ha₀, smul_smul, smul_sub]
      erw [map_sub, hτLR, sub_self]
      rfl
    · erw [smul_zero, map_zero]
      rfl
  choose hf hfle hfmem using fun z : (νX ⁻¹ᵁ (U ⊓ W') : Set Xν) =>
    hU.exists_basicOpen_le (V := U ⊓ W') ⟨(νX) z.1, z.2⟩ z.2.1
  refine TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf _).obj ων)
    (fun z => νX ⁻¹ᵁ X.basicOpen (hf z)) _ (fun z => homOfLE ((νX).preimage_mono (hfle z)))
    (fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hfmem ⟨z, hz⟩⟩) _ _ fun z => ?_
  have := key (hf z) (hfle z)
  change ων.presheaf.map _ (_ • _) = ων.presheaf.map _ _
  rwa [Scheme.Modules.map_smul, MMP.Intersection.modules_map_map,
    MMP.Intersection.modules_map_map, presheaf_map_map]

/-- **The conductor is generated by `θ`.** By finite duality on the affine `U`, a section `x`
of `𝒪_{X^ν}` over `ν⁻¹U` with `x · Γ(ν⁻¹U, 𝒪_{X^ν}) ⊆ Γ(U, 𝒪_X)` is a multiple of `ν^♯θ`. -/
private theorem exists_eq_mul_of_forall_exists_app_eq {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hFA : SatisfiesFA261 sX)
    (ωX : X.Modules)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (ων : (Xν).Modules)
    (τ : (Scheme.Modules.pushforward νX).obj ων ⟶ ωX)
    (T : (Scheme.Modules.pushforward νX).obj ων ⟶ ωX)
    (hT : ∀ V : X.Opens, IsAffineOpen V →
      ∀ l : Γ((Scheme.Modules.pushforward νX).obj (SheafOfModules.unit (Xν).ringCatSheaf), V)
          →ₗ[Γ(X, V)] Γ(ωX, V),
        ∃! w : Γ(ων, νX ⁻¹ᵁ V), ∀ b : Γ(Xν, νX ⁻¹ᵁ V), T.app V (b • w) = l b)
    (a₀ : Γ(Xν, ⊤)) (ha₀ : ∀ (V : X.Opens) (x : Γ(ων, νX ⁻¹ᵁ V)),
      T.app V x = τ.app V
        (((Xν).presheaf.map (homOfLE (le_top : νX ⁻¹ᵁ V ≤ ⊤)).op a₀ : Γ(Xν, νX ⁻¹ᵁ V)) • x))
    {U : X.Opens} (hU : IsAffineOpen U)
    (sU : Γ(ωX, U)) (hsU : IsLocalGenerator ωX sU)
    (g : Γ(ων, νX ⁻¹ᵁ U)) (hg : IsLocalGenerator ων g) (θ : Γ(X, U))
    (hθ : τ.app U g = θ • sU) (x : Γ(Xν, νX ⁻¹ᵁ U))
    (hx : ∀ c : Γ(Xν, νX ⁻¹ᵁ U), ∃ a : Γ(X, U), (νX).app U a = x * c) :
    ∃ β : Γ(Xν, νX ⁻¹ᵁ U), x = (νX).app U θ * β := by
  have hinj := app_injective_normalization sX hFA hX U
  have hbij := hsU U le_rfl
  simp only [MMP.Intersection.modules_map_id] at hbij
  choose f hf using hx
  have hadd : ∀ c d : Γ(Xν, νX ⁻¹ᵁ U), f (c + d) = f c + f d := by
    intro c d; apply hinj; rw [map_add, hf, hf, hf, mul_add]
  have hsmul : ∀ (r : Γ(X, U)) (c : Γ(Xν, νX ⁻¹ᵁ U)), f ((νX).app U r * c) = r * f c := by
    intro r c; apply hinj; rw [map_mul, hf, hf]; ring
  let l : Γ((Scheme.Modules.pushforward νX).obj
      (SheafOfModules.unit (Xν).ringCatSheaf), U) →ₗ[Γ(X, U)] Γ(ωX, U) :=
    { toFun := fun c => f c • sU
      map_add' := fun c d => by
        rw [← add_smul]
        exact congrArg (· • sU) (hadd c d)
      map_smul' := fun r c => by
        rw [RingHom.id_apply, smul_smul]
        exact congrArg (· • sU) (hsmul r c) }
  obtain ⟨w, hw, -⟩ := hT U hU l
  obtain ⟨β, hβ⟩ := (hg _ le_rfl).2 w
  simp only [MMP.Intersection.modules_map_id] at hβ
  replace hβ : β • g = w := hβ
  have h1 := hw 1
  rw [one_smul, ha₀, ← hβ, smul_smul] at h1
  obtain ⟨a, ha, hag⟩ := exists_trace_smul_eq_mul sX hFA ωX hX ων τ hU sU hsU g θ hθ
    ((Xν).presheaf.map (homOfLE (le_top : νX ⁻¹ᵁ U ≤ ⊤)).op a₀ * β)
  rw [hag] at h1
  have h2 : a = f 1 := hbij.1 h1
  refine ⟨(Xν).presheaf.map (homOfLE (le_top : νX ⁻¹ᵁ U ≤ ⊤)).op a₀ * β, ?_⟩
  rw [← ha, h2, hf, mul_one]

/-- **Incomparability.** Distinct primes of an integral extension lying over the same prime
are incomparable. -/
private theorem exists_mem_not_mem_of_comap_eq {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] {q q' : Ideal B} [q'.IsPrime]
    (h : q.comap (algebraMap A B) = q'.comap (algebraMap A B)) (hne : q ≠ q') :
    ∃ e ∈ q', e ∉ q := by
  by_contra! hle
  obtain ⟨w, hwq, hwq'⟩ : ∃ w ∈ q, w ∉ q' := by
    by_contra! h'
    exact hne (le_antisymm h' hle)
  exact (Ideal.comap_lt_comap_of_integral_mem_sdiff (R := A) hle ⟨hwq, hwq'⟩
    (Algebra.IsIntegral.isIntegral w)).ne h.symm

/-- **A generator of the conductor is a uniformizer (algebra).** Let `B` be a finite
`A`-algebra, `q ≠ q'` primes of `B` over a prime `p` of `A` with `B_q` a discrete valuation
ring, and suppose `q ∩ q'` lies in `A` after localizing at `p`. If `θ ∈ p` generates the conductor
`{x ∈ B | xB ⊆ A}`, then `θ` is a uniformizer of `B_q`. -/
private theorem irreducible_algebraMap_of_conductor {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (p : Ideal A) [p.IsPrime] (q q' : Ideal B) [q.IsPrime]
    [q'.IsPrime] (hqp : q.comap (algebraMap A B) = p) (hq'p : q'.comap (algebraMap A B) = p)
    (hne : q ≠ q') [IsDomain (Localization.AtPrime q)]
    [IsDiscreteValuationRing (Localization.AtPrime q)]
    (hJ : ∀ x ∈ q ⊓ q', ∀ b : B, ∃ s ∉ p, ∃ a : A,
      algebraMap A B a = algebraMap A B s * (x * b))
    (θ : A) (hθp : θ ∈ p)
    (hθ₂ : ∀ x : B, (∀ c : B, ∃ a : A, algebraMap A B a = x * c) →
      ∃ β : B, x = algebraMap A B θ * β) :
    Irreducible (algebraMap B (Localization.AtPrime q) (algebraMap A B θ)) := by
  classical
  set R := Localization.AtPrime q
  have hunit : ∀ b : B, b ∉ q → IsUnit (algebraMap B R b) := fun b hb =>
    IsLocalization.map_units R (⟨b, hb⟩ : q.primeCompl)
  -- an element of `q ∩ q'` that is a uniformizer of `B_q`
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨⟨b, t⟩, hbt⟩ := IsLocalization.surj q.primeCompl ϖ
  simp only at hbt
  have hb : Irreducible (algebraMap B R b) := by
    rw [← hbt]; exact (irreducible_mul_isUnit (hunit _ t.2)).2 hϖ
  have hbq : b ∈ q := by
    by_contra h; exact hb.not_isUnit (hunit b h)
  obtain ⟨e, he', heq⟩ := exists_mem_not_mem_of_comap_eq (hqp.trans hq'p.symm) hne
  set x := b * e
  have hx : Irreducible (algebraMap B R x) := by
    rw [map_mul]; exact (irreducible_mul_isUnit (hunit e heq)).2 hb
  have hxJ : x ∈ q ⊓ q' := ⟨q.mul_mem_right _ hbq, q'.mul_mem_left _ he'⟩
  -- a common denominator for `x · B ⊆ A_p`
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := B)
  choose! sf hsf af haf using hJ x hxJ
  let s : A := ∏ i ∈ S, sf i
  have hs : s ∉ p := Submonoid.prod_mem p.primeCompl (fun i _ => hsf i)
  have hcond : ∀ c : B, ∃ a : A, algebraMap A B a = (algebraMap A B s * x) * c := by
    let N : Submodule A B :=
      { carrier := {c | ∃ a : A, algebraMap A B a = (algebraMap A B s * x) * c}
        add_mem' := by
          rintro c d ⟨a, ha⟩ ⟨a', ha'⟩
          exact ⟨a + a', by rw [map_add, ha, ha', mul_add]⟩
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro r c ⟨a, ha⟩
          exact ⟨r * a, by rw [map_mul, ha, Algebra.smul_def]; ring⟩ }
    have hSN : (S : Set B) ⊆ N := by
      intro i hi
      refine ⟨(∏ j ∈ S.erase i, sf j) * af i, ?_⟩
      rw [map_mul, haf i, ← mul_assoc, ← map_mul, Finset.prod_erase_mul _ _ hi]
      ring
    have : N = ⊤ := top_le_iff.1 (hS ▸ Submodule.span_le.2 hSN)
    intro c
    exact (this ▸ Submodule.mem_top : c ∈ N)
  obtain ⟨β, hβ⟩ := hθ₂ _ hcond
  have hsq : algebraMap A B s ∉ q := fun h => hs (hqp ▸ h)
  have hθq : algebraMap A B θ ∈ q := by
    rwa [← Ideal.mem_comap, hqp]
  have hθnu : ¬ IsUnit (algebraMap B R (algebraMap A B θ)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff R q]
    exact not_not.2 hθq
  have hprod : algebraMap B R (algebraMap A B s) * algebraMap B R x =
      algebraMap B R (algebraMap A B θ) * algebraMap B R β := by
    rw [← map_mul, ← map_mul, hβ]
  have hinv : ((hunit _ hsq).unit⁻¹ : Rˣ) * algebraMap B R (algebraMap A B s) = 1 :=
    IsUnit.val_inv_mul _
  have heq2 : algebraMap B R x =
      algebraMap B R (algebraMap A B θ) * (algebraMap B R β * (hunit _ hsq).unit⁻¹) := by
    linear_combination (((hunit _ hsq).unit⁻¹ : Rˣ) : R) * hprod - algebraMap B R x * hinv
  rcases hx.isUnit_or_isUnit heq2 with h | h
  · exact absurd h hθnu
  · have := irreducible_mul_isUnit h (y := algebraMap B R (algebraMap A B θ))
    rw [← heq2] at this
    exact this.1 hx

/-- **The two branches through a prime over a split node.** Let `S` be the localization of a
finite `A`-algebra `B` at a prime `p` of `A`, with exactly two maximal ideals `M₁ ≠ M₂` over
`p A_p`, each with a discrete valuation ring as local ring, and with `M₁ ∩ M₂ ⊆ A_p`. Then every
prime `q` of `B` over `p` has a partner `q' ≠ q` over `p`, `B_q` is a discrete valuation ring, and
`q ∩ q'` lies in `A` after inverting an element outside `p`. -/
private theorem exists_prime_ne_and_isDVR_of_localization {A B R S : Type*} [CommRing A]
    [CommRing B] [CommRing R] [CommRing S] [Algebra A B] [Algebra A R] [Algebra R S]
    [Algebra B S] (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime R p]
    [IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) S]
    (hcomm : ∀ a : A, algebraMap R S (algebraMap A R a) = algebraMap B S (algebraMap A B a))
    (M₁ M₂ : Ideal S) [M₁.IsMaximal] [M₂.IsMaximal] (hne : M₁ ≠ M₂)
    (hprimes : (IsLocalization.AtPrime.isLocalRing R p).maximalIdeal.primesOver S = {M₁, M₂})
    (hdvr₁ : ∃ _ : IsDomain (Localization.AtPrime M₁),
      IsDiscreteValuationRing (Localization.AtPrime M₁))
    (hdvr₂ : ∃ _ : IsDomain (Localization.AtPrime M₂),
      IsDiscreteValuationRing (Localization.AtPrime M₂))
    (hrange : ∀ z ∈ M₁ ⊓ M₂, ∃ r : R, algebraMap R S r = z)
    (q : Ideal B) [q.IsPrime] (hqp : q.comap (algebraMap A B) = p) :
    ∃ q' : Ideal B, ∃ _ : q'.IsPrime, q'.comap (algebraMap A B) = p ∧ q ≠ q' ∧
      (∃ _ : IsDomain (Localization.AtPrime q),
        IsDiscreteValuationRing (Localization.AtPrime q)) ∧
      ∀ x ∈ q ⊓ q', ∀ b : B, ∃ s ∉ p, ∃ a : A,
        algebraMap A B a = algebraMap A B s * (x * b) := by
  classical
  haveI := IsLocalization.AtPrime.isLocalRing R p
  set T := Algebra.algebraMapSubmonoid B p.primeCompl
  have hcompA : ∀ (N : Ideal S), (N.comap (algebraMap R S)).comap (algebraMap A R) =
      (N.comap (algebraMap B S)).comap (algebraMap A B) := by
    intro N; ext a; simp [hcomm]
  have hmaxR : ∀ P' : Ideal R, P'.IsPrime → P'.comap (algebraMap A R) = p →
      P' = IsLocalRing.maximalIdeal R := by
    intro P' hP' h
    have h1 := IsLocalization.map_under p.primeCompl R P'
    have h2 : Ideal.map (algebraMap A R) (P'.comap (algebraMap A R)) = P' := h1
    rw [← h2, h, IsLocalization.AtPrime.map_eq_maximalIdeal]
  have hdisj : Disjoint (T : Set B) q := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsq
    exact hs (hqp ▸ hsq)
  set Q := q.map (algebraMap B S)
  haveI hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint T S q ‹_› hdisj
  have hQq : Q.comap (algebraMap B S) = q :=
    IsLocalization.under_map_of_isPrime_disjoint T S ‹_› hdisj
  have hQmem : Q ∈ (IsLocalRing.maximalIdeal R).primesOver S :=
    ⟨hQ, ⟨(hmaxR _ (Ideal.comap_isPrime _ _) (by rw [hcompA, hQq, hqp])).symm⟩⟩
  obtain ⟨M, M', hMmax, hM'max, hQM, hMM', hM'mem, ⟨hdomM, hdvrM⟩, hinf⟩ :
      ∃ M M' : Ideal S, ∃ _ : M.IsMaximal, M'.IsMaximal ∧ Q = M ∧ M ≠ M' ∧
        M' ∈ (IsLocalRing.maximalIdeal R).primesOver S ∧
        (∃ _ : IsDomain (Localization.AtPrime M),
          IsDiscreteValuationRing (Localization.AtPrime M)) ∧
        ∀ z ∈ M ⊓ M', ∃ r : R, algebraMap R S r = z := by
    have h := hQmem
    rw [hprimes] at h
    rcases h with h | h
    · exact ⟨M₁, M₂, ‹_›, ‹_›, h, hne, hprimes ▸ Or.inr rfl, hdvr₁, hrange⟩
    · exact ⟨M₂, M₁, ‹_›, ‹_›, h, hne.symm, hprimes ▸ Or.inl rfl, hdvr₂,
        fun z hz => hrange z ⟨hz.2, hz.1⟩⟩
  have hMq : M.comap (algebraMap B S) = q := hQM ▸ hQq
  have hM'R : M'.comap (algebraMap R S) = IsLocalRing.maximalIdeal R := by
    haveI := hM'mem.2
    exact (Ideal.over_def M' (IsLocalRing.maximalIdeal R)).symm
  have hM'p : (M'.comap (algebraMap B S)).comap (algebraMap A B) = p := by
    rw [← hcompA, hM'R]; exact IsLocalization.AtPrime.under_maximalIdeal R p
  refine ⟨M'.comap (algebraMap B S), Ideal.comap_isPrime _ _, hM'p, ?_, ?_, ?_⟩
  · intro h
    apply hMM'
    rw [← hQM]
    change q.map (algebraMap B S) = M'
    rw [h, IsLocalization.map_under T S M']
  · haveI : IsLocalization.AtPrime (Localization.AtPrime M) (M.comap (algebraMap B S)) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization T
        (Localization.AtPrime M) M
    haveI : IsLocalization.AtPrime (Localization.AtPrime M) q := hMq ▸ this
    let e := IsLocalization.algEquiv q.primeCompl
      (Localization.AtPrime M) (Localization.AtPrime q)
    haveI : IsDomain (Localization.AtPrime q) := e.symm.toMulEquiv.isDomain
    exact ⟨inferInstance, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e⟩
  · intro x hx b
    have hz : algebraMap B S (x * b) ∈ M ⊓ M' := by
      rw [map_mul, ← hQM]
      exact ⟨Q.mul_mem_right _ (Ideal.mem_map_of_mem _ hx.1), M'.mul_mem_right _ hx.2⟩
    obtain ⟨r, hr⟩ := hinf _ hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl r
    have h1 : algebraMap B S (algebraMap A B a) =
        algebraMap B S (algebraMap A B s * (x * b)) := by
      rw [map_mul, ← hcomm, ← hcomm, ← hr, ← map_mul, mul_comm, IsLocalization.mk'_spec]
    obtain ⟨⟨_, s', hs', rfl⟩, hc⟩ := IsLocalization.exists_of_eq (M := T) h1
    refine ⟨s' * s, p.primeCompl.mul_mem hs' s.2, s' * a, ?_⟩
    simp only at hc
    rw [map_mul, map_mul, hc]; ring

/-- **The points over the split node, on an affine chart.** Let `U ∋ P` be affine,
`A = Γ(U, 𝒪_X)`, `B = Γ(ν⁻¹U, 𝒪_{X^ν})`, and `y` a point of `X^ν` over `P`, with prime `q ⊆ B`.
Then `q` lies over the prime `p` of `P`, there is a second prime `q' ≠ q` of `B` over `p`, `B_q`
is a discrete valuation ring, and `q ∩ q'` lies in `A` after inverting an element outside `p`. -/
private theorem exists_prime_ne_and_isDVR_of_mem_preimage {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hFA : SatisfiesFA261 sX)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (P : X) (hP : Order.coheight P = 1) (hPsing : ¬ IsRegularLocalRing (X.presheaf.stalk P))
    {U : X.Opens} (hPU : P ∈ U) (hU : IsAffineOpen U) (hUν : IsAffineOpen (νX ⁻¹ᵁ U))
    (y : Xν) (hy : νX y = P) (hyU : y ∈ νX ⁻¹ᵁ U) :
    ((hUν.primeIdealOf ⟨y, hyU⟩).asIdeal.comap ((νX).app U).hom =
        (hU.primeIdealOf ⟨P, hPU⟩).asIdeal) ∧
      ∃ q' : Ideal Γ(Xν, νX ⁻¹ᵁ U), ∃ _ : q'.IsPrime,
        q'.comap ((νX).app U).hom = (hU.primeIdealOf ⟨P, hPU⟩).asIdeal ∧
        (hUν.primeIdealOf ⟨y, hyU⟩).asIdeal ≠ q' ∧
        (∃ _ : IsDomain (Localization.AtPrime (hUν.primeIdealOf ⟨y, hyU⟩).asIdeal),
          IsDiscreteValuationRing (Localization.AtPrime (hUν.primeIdealOf ⟨y, hyU⟩).asIdeal)) ∧
        ∀ x ∈ (hUν.primeIdealOf ⟨y, hyU⟩).asIdeal ⊓ q', ∀ b : Γ(Xν, νX ⁻¹ᵁ U),
          ∃ s ∉ (hU.primeIdealOf ⟨P, hPU⟩).asIdeal, ∃ a : Γ(X, U),
            (νX).app U a = (νX).app U s * (x * b) := by
  classical
  obtain ⟨hlft, -, hred, -, hnode⟩ := hFA
  haveI : IsReduced X := hred
  obtain ⟨e⟩ := (hnode P hP).resolve_left hPsing
  let R := X.presheaf.stalk P
  letI : Algebra k R := ((sX.stalkMap P).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (sX.base P) (by simp)).hom).toAlgebra
  haveI : Algebra.EssFiniteType k R := by
    rw [← RingHom.essFiniteType_algebraMap]
    exact essFiniteType_stalkStructureMap sX P
  haveI : IsReduced R := inferInstance
  have hdim : ringKrullDim R = 1 := by rw [ringKrullDim_stalk_eq_coheight, hP]; rfl
  obtain ⟨-, m₁, m₂, hm₁, hm₂, hne, hprimes, hdvr₁, hdvr₂, -⟩ :=
    MMP.exists_adicCompletion_localization_ringEquiv_powerSeries_of_splitNode k R hdim e
      (FractionRing R) (integralClosure R (FractionRing R))
  let B' := integralClosure R (FractionRing R)
  -- the delta invariant of `R` is one
  have hNagata : IsNagataRing R :=
    isNagataRing_of_isQuasiExcellent
      ((isQuasiExcellent_and_isExcellent_of_essFiniteType (R := k) (S := R)).2
        (isExcellent_of_standard_classes_and_finiteType.{_, 0}.1 k)).1
  have hdelta : Ring.deltaInvariant R = 1 := by
    rw [← Stacks.Curves.deltaInvariant_adicCompletion_maximalIdeal R hNagata hdim,
      Ring.deltaInvariant_eq_of_ringEquiv _ _
        (e.trans (Stacks.Curves.quotientAlgEquivMulticross
          (k := IsLocalRing.ResidueField R)).toRingEquiv)]
    exact Stacks.Curves.deltaInvariant_multicross
  have hsimple : IsSimpleModule R (B' ⧸ LinearMap.range (Algebra.linearMap R B')) :=
    Module.length_eq_one_iff.1 hdelta
  have hrange : ∀ z ∈ m₁ ⊓ m₂, ∃ r : R, algebraMap R B' r = z :=
    fun _ hz => inf_le_range_of_isSimpleModule m₁ m₂ hne hsimple hz
  -- the sections and the stalk
  let A := Γ(X, U)
  let B := Γ(Xν, νX ⁻¹ᵁ U)
  letI : Algebra A B := ((νX).app U).hom.toAlgebra
  haveI : Module.Finite A B := by
    haveI : IsFinite (νX) := Scheme.isFinite_normalization
      (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
    exact IsFinite.finite_app (νX) U hU
  set p := (hU.primeIdealOf ⟨P, hPU⟩).asIdeal
  set q := (hUν.primeIdealOf ⟨y, hyU⟩).asIdeal
  have hqp : q.comap (algebraMap A B) = p := by
    have := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU (νX ⁻¹ᵁ U) hUν le_rfl hyU)
    rw [Scheme.Hom.appLE_eq_app, PrimeSpectrum.comap_asIdeal] at this
    refine this.trans ?_
    congr 2
    exact Subtype.ext hy
  letI : Algebra A R := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨P, hPU⟩
  haveI : IsLocalization.AtPrime R p := hU.isLocalization_stalk ⟨P, hPU⟩
  letI := Stacks.NormalizationStalkAmbient.normalizationPushforwardStalkAlgebra X hX P
  letI : Algebra R (FractionRing (R ⧸ nilradical R)) :=
    (Stacks.NormalizationStalkAmbient.reductionFractionRingHom R).toAlgebra
  let eS := (Stacks.NormalizationStalkAmbient.normalizationStalkAlgEquivIntegralClosureFractionRing
      X hX P).trans
    (Stacks.NormalizationStalkAmbient.fractionRingReductionAlgEquiv R
      inferInstance).mapIntegralClosure
  let S := Stacks.NormalizationStalkAmbient.normalizationPushforwardStalk X hX P
  letI : Algebra B S :=
    (((νX).base _* (Xν).presheaf).germ U P hPU).hom.toAlgebra
  have hlocS : IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) S :=
    Stacks.NormalizationStalkAmbient.isLocalization_normalizationPushforwardStalk X hX hU hPU
  letI : Algebra B B' := (eS.toRingEquiv.toRingHom.comp (algebraMap B S)).toAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) B' :=
    (IsLocalization.isLocalization_iff_of_ringEquiv _ eS.toRingEquiv).1 hlocS
  have hcomm : ∀ a : A, algebraMap R B' (algebraMap A R a) =
      algebraMap B B' (algebraMap A B a) := by
    intro a
    change algebraMap R B' _ = eS (algebraMap B S _)
    rw [← eS.commutes]
    congr 1
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply U P hPU (νX).c a
  exact ⟨hqp, exists_prime_ne_and_isDVR_of_localization p hcomm m₁ m₂ hne hprimes hdvr₁ hdvr₂
    hrange q hqp⟩

/-- **A generator of the conductor is a uniformizer at each point over the node.** Let `U ∋ P`
be affine, `A = Γ(U, 𝒪_X)`, `B = Γ(ν⁻¹U, 𝒪_{X^ν})`, and let `θ ∈ A` generate the conductor
`{x ∈ B | xB ⊆ A}` as an ideal of `B`. Then `ν^♯θ` has order one at every point of `X^ν` over the
split node `P`. -/
private theorem germ_mem_nonZeroDivisors_and_ord_eq_one_of_conductor {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hFA : SatisfiesFA261 sX)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (P : X) (hP : Order.coheight P = 1) (hPsing : ¬ IsRegularLocalRing (X.presheaf.stalk P))
    {U : X.Opens} (hPU : P ∈ U) (hU : IsAffineOpen U) (θ : Γ(X, U))
    (hθ₁ : ∀ c : Γ(Xν, νX ⁻¹ᵁ U), ∃ a : Γ(X, U), (νX).app U a = (νX).app U θ * c)
    (hθ₂ : ∀ x : Γ(Xν, νX ⁻¹ᵁ U), (∀ c : Γ(Xν, νX ⁻¹ᵁ U), ∃ a : Γ(X, U), (νX).app U a = x * c) →
      ∃ β : Γ(Xν, νX ⁻¹ᵁ U), x = (νX).app U θ * β)
    (y : Xν) (hy : νX y = P) (hyU : y ∈ νX ⁻¹ᵁ U) :
    (Xν).presheaf.germ (νX ⁻¹ᵁ U) y hyU ((νX).app U θ) ∈ nonZeroDivisors ((Xν).presheaf.stalk y) ∧
      Ring.ord ((Xν).presheaf.stalk y) ((Xν).presheaf.germ (νX ⁻¹ᵁ U) y hyU ((νX).app U θ)) =
        ((1 : ℕ) : ℕ∞) := by
  classical
  haveI hlft : LocallyOfFiniteType sX := hFA.1
  haveI : IsFinite (νX) := Scheme.isFinite_normalization
    (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
  have hUν : IsAffineOpen (νX ⁻¹ᵁ U) := hU.preimage (νX)
  obtain ⟨hqp, q', hq', hq'p, hqq', ⟨hdomq, hdvrq⟩, hJ⟩ :=
    exists_prime_ne_and_isDVR_of_mem_preimage sX hFA hX P hP hPsing hPU hU hUν y hy hyU
  let A := Γ(X, U)
  let B := Γ(Xν, νX ⁻¹ᵁ U)
  letI : Algebra A B := ((νX).app U).hom.toAlgebra
  haveI : Module.Finite A B := IsFinite.finite_app (νX) U hU
  set p := (hU.primeIdealOf ⟨P, hPU⟩).asIdeal
  set q := (hUν.primeIdealOf ⟨y, hyU⟩).asIdeal
  replace hqp : q.comap (algebraMap A B) = p := hqp
  replace hq'p : q'.comap (algebraMap A B) = p := hq'p
  replace hJ : ∀ x ∈ q ⊓ q', ∀ b : B, ∃ s ∉ p, ∃ a : A,
      algebraMap A B a = algebraMap A B s * (x * b) := hJ
  -- `θ` lies in `p`
  have hθp : θ ∈ p := by
    by_contra hθ
    obtain ⟨z, hzq, hzq'⟩ := exists_mem_not_mem_of_comap_eq (hq'p.trans hqp.symm) hqq'.symm
    obtain ⟨a, ha⟩ := hθ₁ z
    have haq : algebraMap A B a ∈ q := by
      change (νX).app U a ∈ q
      rw [ha]; exact q.mul_mem_left _ hzq
    have hap : a ∈ p := hqp ▸ haq
    have haq' : algebraMap A B a ∈ q' := by
      rw [← Ideal.mem_comap, hq'p]; exact hap
    change (νX).app U a ∈ q' at haq'
    rw [ha] at haq'
    rcases hq'.mem_or_mem haq' with h | h
    · exact hθ (hq'p ▸ h)
    · exact hzq' h
  have hirr := irreducible_algebraMap_of_conductor p q q' hqp hq'p hqq' hJ θ hθp hθ₂
  -- transport to the stalk at `y`
  letI : Algebra B ((Xν).presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk (Xν).presheaf ⟨y, hyU⟩
  haveI : IsLocalization.AtPrime ((Xν).presheaf.stalk y) q :=
    hUν.isLocalization_stalk ⟨y, hyU⟩
  let eq := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
    ((Xν).presheaf.stalk y)
  have heq : eq (algebraMap B (Localization.AtPrime q) ((νX).app U θ)) =
      (Xν).presheaf.germ (νX ⁻¹ᵁ U) y hyU ((νX).app U θ) :=
    eq.commutes _
  haveI : IsDomain ((Xν).presheaf.stalk y) := eq.symm.toMulEquiv.isDomain
  haveI : IsDiscreteValuationRing ((Xν).presheaf.stalk y) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eq
  have hirr' : Irreducible ((Xν).presheaf.germ (νX ⁻¹ᵁ U) y hyU ((νX).app U θ)) := by
    rw [← heq]; exact (MulEquiv.irreducible_iff eq).2 hirr
  refine ⟨mem_nonZeroDivisors_of_ne_zero hirr'.ne_zero, ?_⟩
  rw [Ring.ord_of_irreducible hirr']
  rfl

/-- **`θ` vanishes to order one at each point over `P`.** -/
private theorem germ_app_mem_nonZeroDivisors_and_ord_eq_one {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hFA : SatisfiesFA261 sX) (ωX : X.Modules)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (ων : (Xν).Modules)
    (τ : (Scheme.Modules.pushforward νX).obj ων ⟶ ωX)
    (T : (Scheme.Modules.pushforward νX).obj ων ⟶ ωX)
    (hT : ∀ V : X.Opens, IsAffineOpen V →
      ∀ l : Γ((Scheme.Modules.pushforward νX).obj (SheafOfModules.unit (Xν).ringCatSheaf), V)
          →ₗ[Γ(X, V)] Γ(ωX, V),
        ∃! w : Γ(ων, νX ⁻¹ᵁ V), ∀ b : Γ(Xν, νX ⁻¹ᵁ V), T.app V (b • w) = l b)
    (a₀ : Γ(Xν, ⊤)) (ha₀ : ∀ (V : X.Opens) (x : Γ(ων, νX ⁻¹ᵁ V)),
      T.app V x = τ.app V
        (((Xν).presheaf.map (homOfLE (le_top : νX ⁻¹ᵁ V ≤ ⊤)).op a₀ : Γ(Xν, νX ⁻¹ᵁ V)) • x))
    (P : X) (hP : Order.coheight P = 1) (hPsing : ¬ IsRegularLocalRing (X.presheaf.stalk P))
    {U : X.Opens} (hPU : P ∈ U) (hU : IsAffineOpen U)
    (sU : Γ(ωX, U)) (hsU : IsLocalGenerator ωX sU)
    (g : Γ(ων, νX ⁻¹ᵁ U)) (hg : IsLocalGenerator ων g) (θ : Γ(X, U))
    (hθ : τ.app U g = θ • sU)
    (y : Xν) (hy : νX y = P) (hyU : y ∈ νX ⁻¹ᵁ U) :
    (Xν).presheaf.germ (νX ⁻¹ᵁ U) y hyU ((νX).app U θ) ∈ nonZeroDivisors ((Xν).presheaf.stalk y) ∧
      Ring.ord ((Xν).presheaf.stalk y) ((Xν).presheaf.germ (νX ⁻¹ᵁ U) y hyU ((νX).app U θ)) =
        ((1 : ℕ) : ℕ∞) :=
  germ_mem_nonZeroDivisors_and_ord_eq_one_of_conductor sX hFA hX P hP hPsing hPU hU θ
  (fun c => (exists_trace_smul_eq_mul sX hFA ωX hX ων τ hU sU hsU g θ hθ c).imp fun _ h => h.1)
    (exists_eq_mul_of_forall_exists_app_eq sX hFA ωX hX ων τ T hT a₀ ha₀
      hU sU hsU g hg θ hθ) y hy hyU

/-- **A unit multiple of a local generator is a local generator** on the locus where the
multiplier is a unit. -/
private theorem isLocalGenerator_smul_of_basicOpen {Y : Scheme.{u}} {M : Y.Modules}
    {W : Y.Opens} {g : Γ(M, W)} (hg : IsLocalGenerator M g) (c : Γ(Y, W)) :
    IsLocalGenerator M (M.presheaf.map (homOfLE (Y.basicOpen_le c)).op (c • g)) := by
  intro V' hV'
  have hle : V' ≤ W := hV'.trans (Y.basicOpen_le c)
  have hu : IsUnit (Y.presheaf.map (homOfLE hle).op c) := by
    have h1 := (Y.toRingedSpace.isUnit_res_basicOpen c).map (Y.presheaf.map (homOfLE hV').op).hom
    have h2 : Y.presheaf.map (homOfLE hV').op (Y.presheaf.map (homOfLE (Y.basicOpen_le c)).op c) =
        Y.presheaf.map (homOfLE hle).op c := presheaf_map_map _ _ c
    exact h2 ▸ h1
  have hfun : ∀ r : Γ(Y, V'), r • M.presheaf.map (homOfLE hV').op
      (M.presheaf.map (homOfLE (Y.basicOpen_le c)).op (c • g)) =
        (r * Y.presheaf.map (homOfLE hle).op c) • M.presheaf.map (homOfLE hle).op g := by
    intro r
    rw [MMP.Intersection.modules_map_map, Scheme.Modules.map_smul, mul_smul]
  have hb := hg V' hle
  refine ⟨fun a b hab => ?_, fun m => ?_⟩
  · have h' := (hfun a).symm.trans (hab.trans (hfun b))
    exact hu.mul_left_injective (hb.1 h')
  · obtain ⟨r, hr⟩ := hb.2 m
    refine ⟨r * ↑hu.unit⁻¹, ?_⟩
    refine (hfun _).trans ?_
    rw [mul_assoc, show (↑hu.unit⁻¹ : Γ(Y, V')) * Y.presheaf.map (homOfLE hle).op c = 1 from
      hu.val_inv_mul, mul_one]
    exact hr

/-- **Generating near a point from a unit coefficient.** If `g` generates `M` on `D(h) ⊆ V` and
`m|_{D(h)} = c · g` with `c` a unit at `y ∈ D(h)`, then `m` generates `M` near `y`. -/
private theorem exists_le_isLocalGenerator_of_eq_smul {Y : Scheme.{u}} {M : Y.Modules}
    {V : Y.Opens} (m : Γ(M, V)) (h : Γ(Y, V)) {g : Γ(M, Y.basicOpen h)}
    (hg : IsLocalGenerator M g) (c : Γ(Y, Y.basicOpen h))
    (hm : M.presheaf.map (homOfLE (Y.basicOpen_le h)).op m = c • g) (y : Y)
    (hy : y ∈ Y.basicOpen h) (hc : IsUnit (Y.presheaf.germ _ y hy c)) :
    ∃ (W : Y.Opens) (hW : W ≤ V), y ∈ W ∧
      IsLocalGenerator M (M.presheaf.map (homOfLE hW).op m) := by
  refine ⟨Y.basicOpen c, (Y.basicOpen_le c).trans (Y.basicOpen_le h),
    (Y.mem_basicOpen c y hy).2 hc, ?_⟩
  have := isLocalGenerator_smul_of_basicOpen hg c
  rwa [← hm, MMP.Intersection.modules_map_map] at this

/-- A section of a quasi-coherent module over a standard open `D(r)` of an affine open `W`
becomes, after multiplication by a power of `r`, the restriction of a section over `W`. -/
private theorem exists_map_eq_pow_smul_of_isAffineOpen {Y : Scheme.{u}} (M : Y.Modules)
    [M.IsQuasicoherent] {W : Y.Opens} (hW : IsAffineOpen W) (r : Γ(Y, W))
    (u : Γ(M, Y.basicOpen r)) :
    ∃ (x : Γ(M, W)) (k : ℕ), M.presheaf.map (homOfLE (Y.basicOpen_le r)).op x =
      (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op r) ^ k • u := by
  letI := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE M (Y.basicOpen_le r)
  haveI := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ
    M hW r rfl (Y.basicOpen_le r)
  obtain ⟨⟨x, ⟨_, k, rfl⟩⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers r)
    (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ M (Y.basicOpen_le r)) u
  refine ⟨x, k, ?_⟩
  rw [← map_pow]
  exact hx.symm

/-- **`ω_{X^ν}` is free on the full preimage of a small affine neighbourhood of `P`.** -/
private theorem exists_affineOpen_isLocalGenerator_preimage {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (n : ℕ) (hFA : SatisfiesFA261 sX)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (ων : (Xν).Modules) (hων : IsDualizingSheaf (νX ≫ sX) n ων)
    (P : X) (hP : Order.coheight P = 1) (hPsing : ¬ IsRegularLocalRing (X.presheaf.stalk P))
    (U₀ : X.Opens) (hPU₀ : P ∈ U₀) :
    ∃ U : X.Opens, U ≤ U₀ ∧ P ∈ U ∧ IsAffineOpen U ∧
      ∃ g : Γ(ων, νX ⁻¹ᵁ U), IsLocalGenerator ων g := by
  classical
  haveI hlft : LocallyOfFiniteType sX := hFA.1
  haveI : IsReduced X := hFA.2.2.1
  haveI : IsFinite (νX) := Scheme.isFinite_normalization
    (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
  obtain ⟨hNν, -⟩ := isNoetherian_and_locallyOfFiniteType_of_isDualizingSheaf hων
  haveI : IsLocallyNoetherian Xν := hNν.toIsLocallyNoetherian
  haveI : IsReduced Xν := AlgebraicGeometry.Scheme.isReduced_normalizationScheme X hX
  haveI : ων.IsQuasicoherent :=
    @isQuasicoherent_of_isCoherent _ _ _ ων
      (AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent
        (IsDualizingSheaf.isCoherent_exists_injective hων).1)
  -- the two points over `P`
  obtain ⟨y₁, y₂, hy12, hfib⟩ :=
    Set.ncard_eq_two.1 (ncard_preimage_eq_two sX hFA hX P hP hPsing)
  have hfib' : ∀ y : Xν, νX y = P ↔ y = y₁ ∨ y = y₂ := fun y => by
    simpa using Set.ext_iff.1 hfib y
  have hy₁ : νX y₁ = P := (hfib' y₁).2 (Or.inl rfl)
  have hy₂ : νX y₂ = P := (hfib' y₂).2 (Or.inr rfl)
  -- an affine chart
  obtain ⟨_, ⟨U₁, hU₁, rfl⟩, hPU₁, hU₁U₀⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hPU₀ U₀.isOpen
  replace hU₁U₀ : U₁ ≤ U₀ := hU₁U₀
  have hUν : IsAffineOpen (νX ⁻¹ᵁ U₁) := hU₁.preimage (νX)
  set V := νX ⁻¹ᵁ U₁
  have hyV : ∀ y : Xν, νX y = P → y ∈ V := fun y hy => by
    change νX y ∈ U₁; rw [hy]; exact hPU₁
  let A := Γ(X, U₁)
  let B := Γ(Xν, V)
  letI : Algebra A B := ((νX).app U₁).hom.toAlgebra
  haveI : Module.Finite A B := IsFinite.finite_app (νX) U₁ hU₁
  let q : ∀ y : Xν, y ∈ V → Ideal B := fun y hy => (hUν.primeIdealOf ⟨y, hy⟩).asIdeal
  have hqp : ∀ (y : Xν) (hy : νX y = P),
      (q y (hyV y hy)).comap (algebraMap A B) = (hU₁.primeIdealOf ⟨P, hPU₁⟩).asIdeal :=
    fun y hy => (exists_prime_ne_and_isDVR_of_mem_preimage sX hFA hX P hP hPsing hPU₁ hU₁ hUν
      y hy (hyV y hy)).1
  -- the stalks over `P` are regular
  have hreg : ∀ y : Xν, νX y = P → IsRegularLocalRing ((Xν).presheaf.stalk y) := by
    intro y hy
    obtain ⟨-, -, -, -, -, ⟨hdom, hdvr⟩, -⟩ :=
      exists_prime_ne_and_isDVR_of_mem_preimage sX hFA hX P hP hPsing hPU₁ hU₁ hUν y hy (hyV y hy)
    letI : Algebra B ((Xν).presheaf.stalk y) :=
      TopCat.Presheaf.algebra_section_stalk (Xν).presheaf ⟨y, hyV y hy⟩
    haveI : IsLocalization.AtPrime ((Xν).presheaf.stalk y) (q y (hyV y hy)) :=
      hUν.isLocalization_stalk ⟨y, hyV y hy⟩
    let e := IsLocalization.algEquiv (q y (hyV y hy)).primeCompl
      (Localization.AtPrime (q y (hyV y hy))) ((Xν).presheaf.stalk y)
    haveI : IsDomain ((Xν).presheaf.stalk y) := e.symm.toMulEquiv.isDomain
    haveI : IsDiscreteValuationRing ((Xν).presheaf.stalk y) :=
      IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
    infer_instance
  -- a generator on a standard open around each point, and its extension to `V`
  have hdata : ∀ y : Xν, νX y = P → ∃ (h : B) (hy : y ∈ (Xν).basicOpen h)
      (g' : Γ(ων, (Xν).basicOpen h)) (_ : IsLocalGenerator ων g') (m' : Γ(ων, V)) (k : ℕ),
      ων.presheaf.map (homOfLE ((Xν).basicOpen_le h)).op m' =
        ((Xν).presheaf.map (homOfLE ((Xν).basicOpen_le h)).op h) ^ k • g' := by
    intro y hy
    obtain ⟨W, hyW, ⟨e⟩⟩ := hων.exists_restrict_iso_free_of_isRegularLocalRing y (hreg y hy)
    obtain ⟨g, hg⟩ := exists_isLocalGenerator_of_restrict_iso_free ων W e
    obtain ⟨h, hhW, hyh⟩ := hUν.exists_basicOpen_le (V := W) ⟨y, hyW⟩ (hyV y hy)
    have hg' := hg.restrict hhW
    obtain ⟨m', k, hm'⟩ := exists_map_eq_pow_smul_of_isAffineOpen ων hUν h
      (ων.presheaf.map (homOfLE hhW).op g)
    exact ⟨h, hyh, _, hg', m', k, hm'⟩
  -- the local step: `a · m_y + b · m'` generates near `y` when `a ∉ q_y ∋ b`
  have hloc : ∀ (y : Xν) (hy : νX y = P) (h : B) (hyh : y ∈ (Xν).basicOpen h)
      (g' : Γ(ων, (Xν).basicOpen h)) (_ : IsLocalGenerator ων g') (my mo : Γ(ων, V)) (k : ℕ)
      (_ : ων.presheaf.map (homOfLE ((Xν).basicOpen_le h)).op my =
        ((Xν).presheaf.map (homOfLE ((Xν).basicOpen_le h)).op h) ^ k • g')
      (a b : B) (_ : a ∉ q y (hyV y hy)) (_ : b ∈ q y (hyV y hy)),
      ∃ (W : (Xν).Opens) (hW : W ≤ V), y ∈ W ∧
        IsLocalGenerator ων (ων.presheaf.map (homOfLE hW).op (a • my + b • mo)) := by
    intro y hy h hyh g' hg' my mo k hmy a b ha hb
    set res := (Xν).presheaf.map (homOfLE ((Xν).basicOpen_le h)).op
    obtain ⟨d, hd⟩ := (hg' _ le_rfl).2 (ων.presheaf.map (homOfLE ((Xν).basicOpen_le h)).op mo)
    simp only [MMP.Intersection.modules_map_id] at hd
    refine exists_le_isLocalGenerator_of_eq_smul (a • my + b • mo) h hg'
      (res a * res h ^ k + res b * d) ?_ y hyh ?_
    · change ων.presheaf.map _ (a • my + b • mo) = _
      rw [map_add, Scheme.Modules.map_smul, Scheme.Modules.map_smul, hmy]
      change _ + res b • ων.presheaf.map _ mo = _
      rw [← hd, add_smul, mul_smul, mul_smul]
    · letI : Algebra B ((Xν).presheaf.stalk y) :=
        TopCat.Presheaf.algebra_section_stalk (Xν).presheaf ⟨y, hyV y hy⟩
      haveI : IsLocalization.AtPrime ((Xν).presheaf.stalk y) (q y (hyV y hy)) :=
        hUν.isLocalization_stalk ⟨y, hyV y hy⟩
      have hgerm : ∀ x : B, (Xν).presheaf.germ _ y hyh (res x) =
          algebraMap B ((Xν).presheaf.stalk y) x := fun x =>
        TopCat.Presheaf.germ_res_apply _ _ _ _ _
      have hua : IsUnit (algebraMap B ((Xν).presheaf.stalk y) a) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff _ (q y (hyV y hy)) a).2 ha
      have huh : IsUnit (algebraMap B ((Xν).presheaf.stalk y) h) := by
        rw [← hgerm]
        have := ((Xν).mem_basicOpen h y (hyV y hy)).1 hyh
        rwa [TopCat.Presheaf.germ_res_apply]
      have hmb : algebraMap B ((Xν).presheaf.stalk y) b ∈
          IsLocalRing.maximalIdeal ((Xν).presheaf.stalk y) :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (q y (hyV y hy)) b).2 hb
      rw [map_add, map_mul, map_mul, map_pow, hgerm, hgerm, hgerm]
      by_contra hnu
      have h1 : algebraMap B ((Xν).presheaf.stalk y) a * algebraMap B _ h ^ k +
          algebraMap B _ b * (Xν).presheaf.germ _ y hyh d ∈
          IsLocalRing.maximalIdeal ((Xν).presheaf.stalk y) := hnu
      have h2 := Ideal.sub_mem _ h1
        (Ideal.mul_mem_right ((Xν).presheaf.germ _ y hyh d) _ hmb)
      rw [add_sub_cancel_right] at h2
      exact (IsLocalRing.mem_maximalIdeal _).1 h2 (hua.mul (huh.pow k))
  -- separating elements
  have hq12 : q y₁ (hyV y₁ hy₁) ≠ q y₂ (hyV y₂ hy₂) := by
    intro h
    apply hy12
    have e1 := hUν.fromSpec_primeIdealOf ⟨y₁, hyV y₁ hy₁⟩
    have e2 := hUν.fromSpec_primeIdealOf ⟨y₂, hyV y₂ hy₂⟩
    exact e1.symm.trans ((congrArg hUν.fromSpec (PrimeSpectrum.ext h)).trans e2)
  have hsep : ∀ (y z : Xν) (hy : νX y = P) (hz : νX z = P),
      q y (hyV y hy) ≠ q z (hyV z hz) → ∃ e ∈ q z (hyV z hz), e ∉ q y (hyV y hy) :=
    fun y z hy hz => exists_mem_not_mem_of_comap_eq ((hqp y hy).trans (hqp z hz).symm)
  obtain ⟨e₁, he₁₂, he₁₁⟩ := hsep y₁ y₂ hy₁ hy₂ hq12
  obtain ⟨e₂, he₂₁, he₂₂⟩ := hsep y₂ y₁ hy₂ hy₁ hq12.symm
  obtain ⟨h₁, hyh₁, g₁, hg₁, m₁, k₁, hm₁⟩ := hdata y₁ hy₁
  obtain ⟨h₂, hyh₂, g₂, hg₂, m₂, k₂, hm₂⟩ := hdata y₂ hy₂
  set m : Γ(ων, V) := e₁ • m₁ + e₂ • m₂
  obtain ⟨W₁, hW₁, hyW₁, hgW₁⟩ :=
    hloc y₁ hy₁ h₁ hyh₁ g₁ hg₁ m₁ m₂ k₁ hm₁ e₁ e₂ he₁₁ he₂₁
  obtain ⟨W₂, hW₂, hyW₂, hgW₂⟩ :=
    hloc y₂ hy₂ h₂ hyh₂ g₂ hg₂ m₂ m₁ k₂ hm₂ e₂ e₁ he₂₂ he₁₂
  rw [add_comm] at hgW₂
  -- `m` generates on `O = W₁ ∪ W₂`
  set O := W₁ ⊔ W₂
  have hOV : O ≤ V := sup_le hW₁ hW₂
  have hgO : IsLocalGenerator ων (ων.presheaf.map (homOfLE hOV).op m) := by
    refine isLocalGenerator_of_forall_mem ων _ fun x hx => ?_
    rcases hx with hx | hx
    · refine ⟨W₁, le_sup_left, hx, ?_⟩
      rwa [MMP.Intersection.modules_map_map]
    · refine ⟨W₂, le_sup_right, hx, ?_⟩
      rwa [MMP.Intersection.modules_map_map]
  -- shrink `U₁` so that `ν⁻¹U ⊆ O`
  have hZ : IsClosed ((νX).base '' (O : Set Xν)ᶜ) :=
    (νX).isClosedMap _ O.isOpen.isClosed_compl
  have hPZ : P ∉ (νX).base '' (O : Set Xν)ᶜ := by
    rintro ⟨y, hyO, hyP⟩
    rcases (hfib' y).1 hyP with rfl | rfl
    · exact hyO (Or.inl hyW₁)
    · exact hyO (Or.inr hyW₂)
  let U' : X.Opens := U₁ ⊓ ⟨_, hZ.isOpen_compl⟩
  obtain ⟨f, hfU', hPf⟩ := hU₁.exists_basicOpen_le (V := U') ⟨P, hPU₁, hPZ⟩ hPU₁
  have hfO : νX ⁻¹ᵁ X.basicOpen f ≤ O := by
    intro y hy
    by_contra hyO
    exact (hfU' hy).2 ⟨y, hyO, rfl⟩
  refine ⟨X.basicOpen f, (X.basicOpen_le f).trans hU₁U₀, hPf, hU₁.basicOpen f, _,
    hgO.restrict hfO⟩

/-- The pulled-back canonical generator has order `-1` at each point over `P`. -/
private theorem isOrderOfSectionAt_neg_one {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (n : ℕ) (hFA : SatisfiesFA261 sX)
    (ωX : X.Modules)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (ων : (Xν).Modules) (hων : IsDualizingSheaf (νX ≫ sX) n ων)
    (τ : (Scheme.Modules.pushforward νX).obj ων ⟶ ωX)
    (hTτ : ∃ T : (Scheme.Modules.pushforward νX).obj ων ⟶ ωX,
      (∀ V : X.Opens, IsAffineOpen V →
        ∀ l : Γ((Scheme.Modules.pushforward νX).obj (SheafOfModules.unit (Xν).ringCatSheaf), V)
            →ₗ[Γ(X, V)] Γ(ωX, V),
          ∃! w : Γ(ων, νX ⁻¹ᵁ V), ∀ b : Γ(Xν, νX ⁻¹ᵁ V), T.app V (b • w) = l b) ∧
      ∃ a₀ : Γ(Xν, ⊤), ∀ (V : X.Opens) (x : Γ(ων, νX ⁻¹ᵁ V)),
        T.app V x = τ.app V
          (((Xν).presheaf.map (homOfLE (le_top : νX ⁻¹ᵁ V ≤ ⊤)).op a₀ : Γ(Xν, νX ⁻¹ᵁ V)) • x))
    (P : X) (hP : Order.coheight P = 1) (hPsing : ¬ IsRegularLocalRing (X.presheaf.stalk P))
    {W : X.Opens} (s : Γ(ωX, W))
    (hs : ∃ (V : X.Opens) (_ : P ∈ V) (hVW : V ≤ W),
      IsLocalGenerator ωX (ωX.presheaf.map (homOfLE hVW).op s))
    {W' : X.Opens} (hW' : W' ≤ W)
    (hW'gen : ∀ η : X, closure {η} ∈ irreducibleComponents X → η ⤳ P → η ∈ W')
    (t : Γ(ων, νX ⁻¹ᵁ W'))
    (ht : τ.app W' t = ωX.presheaf.map (homOfLE hW').op s) :
    ∀ y : Xν, (νX).base y = P → IsOrderOfSectionAt ων t y (-1) := by
  intro y hy
  obtain ⟨T, hT, a₀, ha₀⟩ := hTτ
  obtain ⟨V₀, hPV₀, hV₀W, hsV₀⟩ := hs
  obtain ⟨U, hUV₀, hPU, hU, g, hg⟩ := exists_affineOpen_isLocalGenerator_preimage sX n hFA hX ων
    hων P hP hPsing V₀ hPV₀
  have hUW : U ≤ W := hUV₀.trans hV₀W
  have hsU : IsLocalGenerator ωX (ωX.presheaf.map (homOfLE hUW).op s) := by
    have := hsV₀.restrict hUV₀
    rwa [MMP.Intersection.modules_map_map] at this
  obtain ⟨θ, hθ⟩ := (hsU U le_rfl).2 (τ.app U g)
  simp only [MMP.Intersection.modules_map_id] at hθ
  have hyU : y ∈ νX ⁻¹ᵁ U := by
    change νX y ∈ U
    rw [hy]; exact hPU
  obtain ⟨V', hV', hVW, hgen, heq⟩ := exists_smul_eq_generator sX hFA ωX hX ων τ T hT a₀
    ha₀ P s hW' hW'gen t ht hPU hUW hU hsU g θ hθ.symm y hy
  obtain ⟨hθnzd, hθord⟩ := germ_app_mem_nonZeroDivisors_and_ord_eq_one sX hFA ωX hX ων τ
    T hT a₀ ha₀ P hP hPsing hPU hU _ hsU g hg θ hθ.symm y hy hyU
  refine ⟨νX ⁻¹ᵁ U, hyU, g, 1, (νX).app U θ, V', hV', hVW, hg, hgen, ?_, hθnzd, ?_, 0, 1, ?_,
    hθord, by norm_num⟩
  · rw [map_one]; exact one_mem _
  · rw [map_one, one_smul]; exact heq
  · rw [map_one, Ring.ord_one]; rfl

/-- **The canonical generator has a simple pole on each nodal branch.** Let `X` satisfy (2.6.1)
over `k`, of pure dimension `n`, with dualizing sheaf `ω_X`, let `X° ⊆ X` be an admissible choice
of `X°` (`MMP.Flips.IsInvertibleBigOpen`), and let `P` be a codimension-one point at which
`𝒪_{X,P}` is not regular. Let `ν : X^ν ⟶ X` be the normalization, `ω_{X^ν}` a dualizing sheaf of
`X^ν` and `τ : ν_* ω_{X^ν} ⟶ ω_X` a trace: every morphism `ν_* ω_{X^ν} ⟶ ω_X` is `τ ∘ (a · -)`
for some `a ∈ Γ(X^ν, 𝒪)`. Let `s ∈ Γ(W, ω_X)`, `W ⊆ X°`, generate `ω_X` on a neighbourhood of
`P`, and let `t ∈ Γ(ν⁻¹(W'), ω_{X^ν})` with `τ(t) = s|_{W'}`, for an open `W' ⊆ W` containing
every generic point of `X` specializing to `P`. Then there are exactly two points of `X^ν` over
`P`, and `t` has order `-1` at each of them. -/
@[mmp "lem_mmp_split_node_dualizing_poles"]
public theorem ncard_preimage_eq_two_and_isOrderOfSectionAt_neg_one {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (n : ℕ) (hFA : SatisfiesFA261 sX)
    (ωX : X.Modules) (hωX : IsDualizingSheaf sX n ωX) (Xo : X.Opens)
    (_hXo : IsInvertibleBigOpen ωX Xo)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (ων : (Xν).Modules) (hων : IsDualizingSheaf (νX ≫ sX) n ων)
    (τ : (Scheme.Modules.pushforward νX).obj ων ⟶ ωX)
    (hτ : ∀ φ : (Scheme.Modules.pushforward νX).obj ων ⟶ ωX,
      ∃ a : Γ(Xν, ⊤), ∀ (V : X.Opens) (x : Γ(ων, νX ⁻¹ᵁ V)),
        φ.app V x = τ.app V
          (((Xν).presheaf.map (homOfLE (le_top : νX ⁻¹ᵁ V ≤ ⊤)).op a : Γ(Xν, νX ⁻¹ᵁ V)) • x))
    (P : X) (hP : Order.coheight P = 1) (hPsing : ¬ IsRegularLocalRing (X.presheaf.stalk P))
    {W : X.Opens} (_hWXo : W ≤ Xo) (s : Γ(ωX, W))
    (hs : ∃ (V : X.Opens) (_ : P ∈ V) (hVW : V ≤ W),
      IsLocalGenerator ωX (ωX.presheaf.map (homOfLE hVW).op s))
    {W' : X.Opens} (hW' : W' ≤ W)
    (hW'gen : ∀ η : X, closure {η} ∈ irreducibleComponents X → η ⤳ P → η ∈ W')
    (t : Γ(ων, νX ⁻¹ᵁ W'))
    (ht : τ.app W' t = ωX.presheaf.map (homOfLE hW').op s) :
    ((νX).base ⁻¹' {P}).ncard = 2 ∧
      ∀ y : Xν, (νX).base y = P → IsOrderOfSectionAt ων t y (-1) :=
  ⟨ncard_preimage_eq_two sX hFA hX P hP hPsing,
    isOrderOfSectionAt_neg_one sX n hFA ωX hX ων hων τ
      ((exists_globalTrace sX n ωX hωX hX ων hων).imp fun T hT => ⟨hT, hτ T⟩)
      P hP hPsing s hs hW' hW'gen t ht⟩

/-- **The canonical generator has a simple pole on each nodal branch, affine-local trace.**
The conclusion of `MMP.Flips.ncard_preimage_eq_two_and_isOrderOfSectionAt_neg_one` when the
trace `τ : ν_* ω_{X^ν} ⟶ ω_X` is given by finite duality on affine opens: for every affine open
`V ⊆ X`, every `Γ(V, 𝒪_X)`-linear map `φ : Γ(ν⁻¹V, 𝒪_{X^ν}) → Γ(V, ω_X)` is `a ↦ τ(a · f)` for a
unique `f ∈ Γ(ν⁻¹V, ω_{X^ν})`. -/
public theorem ncard_preimage_eq_two_and_isOrderOfSectionAt_neg_one_of_affine {k : Type u}
    [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (n : ℕ) (hFA : SatisfiesFA261 sX)
    (ωX : X.Modules) (hωX : IsDualizingSheaf sX n ωX) (Xo : X.Opens)
    (_hXo : IsInvertibleBigOpen ωX Xo)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (ων : (Xν).Modules) (hων : IsDualizingSheaf (νX ≫ sX) n ων)
    (τ : (Scheme.Modules.pushforward νX).obj ων ⟶ ωX)
    (hτ : ∀ V : X.affineOpens,
      letI := ((νX).app V).hom.toAlgebra
      ∀ φ : Γ(Xν, νX ⁻¹ᵁ V) →ₗ[Γ(X, V)] Γ(ωX, V),
        ∃! f : Γ(ων, νX ⁻¹ᵁ V), ∀ a, φ a = τ.app V (a • f))
    (P : X) (hP : Order.coheight P = 1) (hPsing : ¬ IsRegularLocalRing (X.presheaf.stalk P))
    {W : X.Opens} (_hWXo : W ≤ Xo) (s : Γ(ωX, W))
    (hs : ∃ (V : X.Opens) (_ : P ∈ V) (hVW : V ≤ W),
      IsLocalGenerator ωX (ωX.presheaf.map (homOfLE hVW).op s))
    {W' : X.Opens} (hW' : W' ≤ W)
    (hW'gen : ∀ η : X, closure {η} ∈ irreducibleComponents X → η ⤳ P → η ∈ W')
    (t : Γ(ων, νX ⁻¹ᵁ W'))
    (ht : τ.app W' t = ωX.presheaf.map (homOfLE hW').op s) :
    ((νX).base ⁻¹' {P}).ncard = 2 ∧
      ∀ y : Xν, (νX).base y = P → IsOrderOfSectionAt ων t y (-1) := by
  refine ⟨ncard_preimage_eq_two sX hFA hX P hP hPsing,
    isOrderOfSectionAt_neg_one sX n hFA ωX hX ων hων τ
      ⟨τ, fun V hV l => ?_, 1, fun V x => by rw [map_one, one_smul]⟩
      P hP hPsing s hs hW' hW'gen t ht⟩
  obtain ⟨f, hf, huniq⟩ := hτ ⟨V, hV⟩ l
  exact ⟨f, fun b => (hf b).symm, fun w hw => huniq w fun b => (hw b).symm⟩

end MMP.Flips
