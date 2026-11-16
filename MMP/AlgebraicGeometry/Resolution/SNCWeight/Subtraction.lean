module

public import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso

/-!
# Smooth snc models and the subtraction step

Smooth projective birational models with a reduced snc boundary, and the subtraction algorithm,
which reduces a weight vector on the boundary components to a single component by repeatedly
blowing up codimension-two boundary strata.

* `BlowupTower`: blow-up sequences (`MMP.Resolution.ClosedBlowupSequence`) each of whose centres
  is the reduced intersection of two components of the current reduced total boundary
  (`BlowupTower.IsBoundaryStratumSequence`), and their extension by one more blow-up.
* `SNCModel.SModel`: smooth projective birational models with a reduced snc, log crepant
  boundary, closed under blow-ups of codimension-two boundary strata (`SNCModel.blowUpModel`).
* `CentreLifting`: orders of local equations and centres of valuations across one blow-up.
* `Subtraction`: one step of the subtraction algorithm on the weight vector, and its iteration
  down to a single component of weight one. Along the way the model stays the end of a blow-up
  sequence of the kind above (`SModel.IsStratumTower`), and the intersections of the components
  of positive weight stay connected (`Subtraction.StrataConnected`), so each centre is the whole
  intersection of two components.
-/

@[expose] public noncomputable section

universe uP

namespace MMP.Fourfold.SNCWeight

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing MvPolynomial
open scoped WithZero

namespace BlowupTower

open MMP.Resolution

variable {X : Scheme.{uP}}

/-- The centre `Z` on `Y`, which lies over `X` by `π`, is the intersection, with its reduced
structure, of two distinct irreducible components of the reduced total boundary
`π⁻¹(D) ∪ Ex(π)` of `π` with respect to the boundary `D ⊆ X`. -/
def IsBoundaryStratumCentre (D : Set X) {Y : Scheme.{uP}} (π : Y ⟶ X)
    (Z : Y.IdealSheafData) : Prop :=
  ∃ D₁ ∈ componentsOf (π.base ⁻¹' D ∪ (MMP.Mori.exceptionalSet π : Set Y)),
    ∃ D₂ ∈ componentsOf (π.base ⁻¹' D ∪ (MMP.Mori.exceptionalSet π : Set Y)),
      D₁ ≠ D₂ ∧ (Z.support : Set Y) = D₁ ∩ D₂ ∧
        Z = Scheme.IdealSheafData.vanishingIdeal Z.support

/-- Every centre of the blow-up sequence `B`, started on `Y` lying over `X` by `π`, is the
intersection of two components of the reduced total boundary of the composite down to `X`
(`IsBoundaryStratumCentre`). -/
def IsBoundaryStratumSequence (D : Set X) :
    {Y : Scheme.{uP}} → (Y ⟶ X) → ClosedBlowupSequence Y → Prop
  | _, _, .nil _ => True
  | _, π, .cons Z B =>
    IsBoundaryStratumCentre D π Z ∧ IsBoundaryStratumSequence D (blowUpToBase Z ≫ π) B

/-- The blow-up sequence `B` followed by the blow-up of `Z` on its last scheme. -/
def snoc : {Y : Scheme.{uP}} → (B : ClosedBlowupSequence Y) →
    B.target.IdealSheafData → ClosedBlowupSequence Y
  | _, .nil _, Z => .cons Z (.nil _)
  | _, .cons Z₀ B, Z => .cons Z₀ (snoc B Z)

/-- The last scheme of `snoc B Z` is the blow-up of `Z`. -/
theorem target_snoc : ∀ {Y : Scheme.{uP}} (B : ClosedBlowupSequence Y)
    (Z : B.target.IdealSheafData), (snoc B Z).target = blowUp Z
  | _, .nil _, _ => rfl
  | _, .cons _ B, Z => target_snoc B Z

/-- The composite of `snoc B Z` down to its base is the blow-up of `Z` followed by the composite
of `B`. -/
theorem toBase_snoc : ∀ {Y : Scheme.{uP}} (B : ClosedBlowupSequence Y)
    (Z : B.target.IdealSheafData),
    (snoc B Z).toBase = eqToHom (target_snoc B Z) ≫ blowUpToBase Z ≫ B.toBase
  | Y, .nil _, Z => by
    change 𝟙 _ ≫ blowUpToBase Z = eqToHom rfl ≫ blowUpToBase Z ≫ 𝟙 Y
    rw [eqToHom_refl, Category.id_comp, Category.id_comp]
    exact (Category.comp_id _).symm
  | _, .cons Z₀ B, Z => by
    change (snoc B Z).toBase ≫ blowUpToBase Z₀ = _
    rw [toBase_snoc B Z]
    change (eqToHom _ ≫ blowUpToBase Z ≫ B.toBase) ≫ blowUpToBase Z₀ =
      eqToHom _ ≫ blowUpToBase Z ≫ B.toBase ≫ blowUpToBase Z₀
    rw [Category.assoc]
    congr 1

/-- If every centre of `B` is a boundary stratum and `Z` is a boundary stratum of the last
scheme of `B`, then every centre of `snoc B Z` is a boundary stratum. -/
theorem isBoundaryStratumSequence_snoc (D : Set X) : ∀ {Y : Scheme.{uP}} (π : Y ⟶ X)
    (B : ClosedBlowupSequence Y) (Z : B.target.IdealSheafData),
    IsBoundaryStratumSequence D π B → IsBoundaryStratumCentre D (B.toBase ≫ π) Z →
      IsBoundaryStratumSequence D π (snoc B Z)
  | Y, π, .nil _, Z, _, hZ => by
    have e : (ClosedBlowupSequence.nil Y).toBase ≫ π = π := Category.id_comp π
    exact ⟨e ▸ hZ, trivial⟩
  | _, π, .cons Z₀ B, Z, hB, hZ => by
    have e : (ClosedBlowupSequence.cons Z₀ B).toBase ≫ π = B.toBase ≫ blowUpToBase Z₀ ≫ π :=
      Category.assoc _ _ _
    exact ⟨hB.1, isBoundaryStratumSequence_snoc D _ B Z hB.2 (e ▸ hZ)⟩

/-- A blow-up sequence over `X` whose last scheme is `Y`, followed by the blow-up of a centre `Z`
of `Y` of the required kind, is again such a blow-up sequence, ending at the blow-up of `Z`. -/
theorem exists_snoc (D : Set X) {Y : Scheme.{uP}} (B : ClosedBlowupSequence X)
    (h : Y = B.target) (g : Y ⟶ X) (hg : eqToHom h ≫ B.toBase = g)
    (hB : IsBoundaryStratumSequence D (𝟙 X) B) (Z : Y.IdealSheafData)
    (hZ : IsBoundaryStratumCentre D g Z) :
    ∃ (B' : ClosedBlowupSequence X) (h' : blowUp Z = B'.target),
      eqToHom h' ≫ B'.toBase = blowUpToBase Z ≫ g ∧ IsBoundaryStratumSequence D (𝟙 X) B' := by
  subst h
  subst hg
  refine ⟨snoc B Z, (target_snoc B Z).symm, ?_,
    isBoundaryStratumSequence_snoc D _ B Z hB (by simpa using hZ)⟩
  rw [toBase_snoc]
  simp

end BlowupTower

namespace SNCModel

open MMP.Mori

variable {k : Type uP} [Field k]

/-- A smooth projective birational model over `X` with an snc boundary. -/
structure SModel {X : Scheme.{uP}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X]
    (Δ : Divisor X) (n : ℕ) where
  /-- The scheme of the model. -/
  Y : Scheme.{uP}
  /-- The morphism from the model to `X`. -/
  g : Y ⟶ X
  /-- The model is a variety over `k`. -/
  isVariety : AlgebraicGeometry.IsVariety k (g ≫ sX)
  /-- The model is smooth over `k`. -/
  isSmooth : IsSmoothScheme (g ≫ sX)
  /-- The model has dimension `n`. -/
  dim : topologicalKrullDim Y = n
  /-- The morphism `g` is proper. -/
  isProper : IsProper g
  /-- The morphism `g` is projective whenever `X` is quasi-compact and quasi-separated. -/
  isProj : ∀ [CompactSpace X] [QuasiSeparatedSpace X], IsProjective g
  /-- The morphism `g` is birational. -/
  isBir : IsBirationalMorphism g
  /-- The boundary of the model. -/
  T : Divisor Y
  /-- The boundary `T` is reduced and effective. -/
  red : MMP.Intersection.IsReducedEffective T
  /-- The boundary `T` has simple normal crossings. -/
  snc : T.IsSNC (g ≫ sX)
  /-- The support of `T` is the preimage of the support of `Δ`. -/
  supp : (⋃ F ∈ T.support, (F.support : Set Y)) = g.base ⁻¹' ⋃ P ∈ Δ.support, (P.support : Set X)
  /-- The exceptional set of `g` lies in the support of `T`. -/
  exc : (exceptionalSet g : Set Y) ⊆ ⋃ F ∈ T.support, (F.support : Set Y)
  /-- The pair `(Y, T)` is log crepant over `(X, Δ)`: the order along each prime divisor `F` of
  the pull-back of a local generator of `ω_X(Δ)` is `-T.coeff F`. -/
  crep : haveI : IsIntegral Y := isVariety.toIsIntegral
    haveI : IsDominant g := isBir.isDominant
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
    ∀ (F : MMP.Mori.PrimeDivisor Y) (U0 : X.Opens) (τ : RationalPluriForms sX n 1),
      g F.genericPoint ∈ U0 → GeneratesOn (Divisor.toQDivisor Δ) 1 U0 τ →
        F.ordForm (pullbackRationalPluriForms sX g τ) = - T.coeff F

variable {X : Scheme.{uP}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
  {Δ : Divisor X} {n : ℕ}

/-- `ξ` dominates the local ring of `p`. -/
def Dominates {Y : Scheme.{uP}} [IsIntegral Y] (ξ : Valuation Y.functionField ℤᵐ⁰) (p : Y) :
    Prop :=
  (∀ a : Y.presheaf.stalk p, ξ (algebraMap _ Y.functionField a) ≤ 1) ∧
    ∀ a ∈ maximalIdeal (Y.presheaf.stalk p), ξ (algebraMap _ Y.functionField a) < 1

/-- `ξ` is centred at `η` with order vector `d • α` on the local equations `z`. -/
def IsWeightVal (η : X) {ι : Type*} (z : ι → X.presheaf.stalk η) (α : ι → ℕ)
    (ξ : Valuation X.functionField ℤᵐ⁰) (d : ℕ) : Prop :=
  0 < d ∧ Dominates ξ η ∧
    ∀ j, ξ (algebraMap _ X.functionField (z j)) = WithZero.exp (-((d * α j : ℕ) : ℤ))

namespace SModel

variable (M : SModel sX Δ n)

/-- The scheme of a model is integral. -/
theorem isIntegral : IsIntegral M.Y := M.isVariety.toIsIntegral

attribute [local instance] isIntegral

/-- The morphism of a model to `X` is dominant. -/
theorem isDominant : IsDominant M.g := M.isBir.isDominant

attribute [local instance] isDominant

/-- The scheme of a model is locally noetherian. -/
theorem isLocallyNoetherian : IsLocallyNoetherian M.Y :=
  haveI := M.isVariety.toLocallyOfFiniteType
  LocallyOfFiniteType.isLocallyNoetherian (M.g ≫ sX)

attribute [local instance] isLocallyNoetherian

/-- The scheme of a model is normal. -/
theorem isNormal : IsNormal M.Y := by
  haveI : Smooth (M.g ≫ sX) := MMP.Threefold.Resolution.smooth_of_isSmoothScheme M.isSmooth
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  exact AlgebraicGeometry.isNormal_of_smooth (M.g ≫ sX)

attribute [local instance] isNormal

/-- The order of the pull-back of `a` along a prime divisor `F` of the model. -/
def ordZ {η : X} (a : X.presheaf.stalk η) (F : MMP.Mori.PrimeDivisor M.Y) : ℤ :=
  M.Y.ord (functionFieldMap M.g (algebraMap _ X.functionField a)) F.genericPoint

/-- The tracking data: positive boundary components, their weights, and a connected set of
points containing the centres of all valuations of weight a multiple of `α`. -/
structure Track (η : X) {ι : Type*} [Fintype ι] (z : ι → X.presheaf.stalk η) (α : ι → ℕ) where
  /-- The boundary components of positive weight. -/
  P : Finset (MMP.Mori.PrimeDivisor M.Y)
  /-- The weights of the boundary components. -/
  c : MMP.Mori.PrimeDivisor M.Y → ℕ
  /-- A connected set of points containing the centres of the valuations. -/
  S : Set M.Y
  /-- The components in `P` are boundary components. -/
  P_sub : P ⊆ M.T.support
  /-- The weights of the components in `P` are positive. -/
  c_pos : ∀ F ∈ P, 0 < c F
  /-- The set `S` is preconnected. -/
  S_pre : _root_.IsPreconnected S
  /-- The set `S` is nonempty. -/
  S_ne : S.Nonempty
  /-- The set `S` lies in every component in `P`. -/
  S_sub : ∀ F ∈ P, S ⊆ F.support
  /-- Every point of `S` lies over `η`. -/
  S_over : ∀ y ∈ S, M.g y = η
  /-- The vector `α` is the weighted sum of the orders of the `z j` along the components in
  `P`. -/
  ray : ∀ j, (α j : ℤ) = ∑ F ∈ P, (c F : ℤ) * M.ordZ (z j) F
  /-- Every valuation of weight `d • α` at `η` has its centres on the model in `S`, lying on
  exactly the boundary components in `P`, and has order `d * c F` along each `F ∈ P`. -/
  cent : ∀ (ξ : Valuation X.functionField ℤᵐ⁰) (d : ℕ), IsWeightVal η z α ξ d →
    ∀ ξY : Valuation M.Y.functionField ℤᵐ⁰, ξY.comap (functionFieldMap M.g) = ξ →
    ∀ p : M.Y, Dominates ξY p → p ∈ S ∧ (∀ F ∈ M.T.support, p ∈ F.support ↔ F ∈ P) ∧
      ∀ F ∈ P, ∀ u, IdealSheafData.stalk F.idealSheaf p = Ideal.span {u} →
        ξY (algebraMap _ M.Y.functionField u) = WithZero.exp (-((d * c F : ℕ) : ℤ))

/-- The model is the last scheme of a blow-up sequence over `X`, each of whose centres is the
intersection of two components of the reduced total boundary at that stage. -/
def IsStratumTower : Prop :=
  ∃ (B : MMP.Resolution.ClosedBlowupSequence X) (h : M.Y = B.target),
    eqToHom h ≫ B.toBase = M.g ∧
      BlowupTower.IsBoundaryStratumSequence (⋃ P ∈ Δ.support, (P.support : Set X)) (𝟙 X) B

end SModel

attribute [local instance] SModel.isIntegral SModel.isDominant SModel.isLocallyNoetherian
  SModel.isNormal

/-- The hypotheses on the base. -/
structure BaseData (sX : X ⟶ Spec (.of k)) (Δ : Divisor X) (n : ℕ) (η : X) where
  isVariety : AlgebraicGeometry.IsVariety k sX
  isSmooth : IsSmoothScheme sX
  dim : topologicalKrullDim X = n
  red : MMP.Intersection.IsReducedEffective Δ
  snc : Δ.IsSNC sX
  mem : ∀ P ∈ Δ.support, η ∈ P.support

section Aux

open MMP.Mori

/-- The pull-back of a nonzero rational pluricanonical form along a dominant morphism inducing an
isomorphism of function fields is nonzero. -/
theorem pullbackRationalPluriForms_ne_zero' {k : Type uP} [Field k] [PerfectField k]
    {X : Scheme.{uP}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    {Y : Scheme.{uP}} [IsIntegral Y] (f : Y ⟶ X) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
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

/-- If `π` is an isomorphism off the closed set `Z`, and `B` contains both `Z` and the exceptional
set of `g`, then the exceptional set of `π ≫ g` lies in `π ⁻¹' B`. -/
theorem exceptionalSet_comp_subset {X Y Y' : Scheme.{uP}} (g : Y ⟶ X) [IsProper g] (π : Y' ⟶ Y)
    (Z : Closeds Y) (hπ : IsIso (π ∣_ ⟨(Z : Set Y)ᶜ, Z.isClosed.isOpen_compl⟩)) {B : Set Y}
    (hB : (exceptionalSet g : Set Y) ⊆ B) (hZ : (Z : Set Y) ⊆ B) :
    (exceptionalSet (π ≫ g) : Set Y') ⊆ π ⁻¹' B := by
  intro y' hy'
  by_contra hyB
  apply hy'
  set V0 : X.Opens := biregularLocus g ⊓
    ⟨(g '' (Z : Set Y))ᶜ, (g.isClosedMap _ Z.isClosed).isOpen_compl⟩
  have hgV : IsBiregular g V0 := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  have hπV : IsBiregular π (g ⁻¹ᵁ V0) := by
    refine isBiregular_iff_le_biregularLocus.mpr (le_trans ?_ (le_biregularLocus hπ))
    intro y hy hyZ
    exact hy.2 ⟨y, hyZ, rfl⟩
  have hV : IsBiregular (π ≫ g) V0 := by
    change IsIso ((π ≫ g) ∣_ V0)
    rw [morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hπV hgV
  have hyE : π y' ∉ (exceptionalSet g : Set Y) := fun h => hyB (hB h)
  refine le_biregularLocus hV ⟨not_not.mp hyE, ?_⟩
  · rintro ⟨c, hcZ, hc⟩
    rw [Scheme.Hom.comp_apply] at hc
    have hcB : g c ∈ biregularLocus g := by
      rw [hc]; exact not_not.mp hyE
    have hinj : c = π y' := by
      have hb' : g (π y') ∈ biregularLocus g := hc ▸ hcB
      exact ((MMP.Threefold.Resolution.specializes_of_mem_biregularLocus g hcB hb'
        (hc ▸ specializes_rfl)).antisymm
        (MMP.Threefold.Resolution.specializes_of_mem_biregularLocus g hb' hcB
          (hc ▸ specializes_rfl))).eq
    exact hyB (by rw [Set.mem_preimage, ← hinj]; exact hZ hcZ)

end Aux

section BlowUpModel

open PrimeDivisorUnion StratumBlowup SNCBlowup LocalEquation BlowupCrepancy MMP.Resolution
  MMP.Threefold.Resolution

variable [CharZero k] [IsNormal X] [LocallyOfFiniteType sX] (M : SModel sX Δ n)
  {F F' : MMP.Mori.PrimeDivisor M.Y}
  (hF : F ∈ M.T.support) (hF' : F' ∈ M.T.support) (hFF : F ≠ F') {I : M.Y.IdealSheafData}
  (hirr : IsIrreducible (I.support : Set M.Y)) (hIsm : IsSmoothScheme (I.subschemeι ≫ M.g ≫ sX))
  (hIsub : (I.support : Set M.Y) ⊆ (F.support : Set M.Y) ∩ F'.support)
  (hIst : ∀ y ∈ I.support, IdealSheafData.stalk I y =
    IdealSheafData.stalk F.idealSheaf y ⊔ IdealSheafData.stalk F'.idealSheaf y)

include hF hF' hFF hirr hIsm hIsub hIst in
/-- A smooth irreducible centre in the intersection of two distinct boundary components, with ideal
the sum of theirs, has codimension at least one. -/
theorem codim_one_le :
    1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds M.Y) := by
  rw [codimension_centre_eq_two (M.g ≫ sX) M.snc hF hF' hFF hirr hIsm hIsub hIst]; norm_num

include hIsm in
/-- The blow-up of a smooth centre on a model is a smooth blow-up. -/
theorem centre_isSmoothBlowup : IsSmoothBlowup (M.g ≫ sX) I := ⟨M.isSmooth, hIsm⟩

/-- The blow-up of a model along a codimension-two stratum. -/
abbrev blowUpModel : SModel sX Δ n where
  Y := blowUp I
  g := blowUpToBase I ≫ M.g
  isVariety := by
    haveI := M.isVariety
    have hI : I ≠ ⊥ :=
      ne_bot_of_one_le_codimension I hirr (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst)
    rw [Category.assoc]
    exact (MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      (M.g ≫ sX) I hI).1
  isSmooth := by
    have := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup (M.g ≫ sX) I
      (centre_isSmoothBlowup M hIsm)).1
    rw [Category.assoc]
    exact isSmoothScheme_of_smooth _
  dim := topologicalKrullDim_blowUp (M.g ≫ sX) I (centre_isSmoothBlowup M hIsm) hirr
    (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst) M.dim
  isProper := by
    haveI := M.isProper
    haveI : IsProper (blowUpToBase I) :=
      TwoStepTower.isProper_blowUpToBase (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
    infer_instance
  isProj := IsProjective.comp
    (Stacks.Blowup.isProjective_blowUpToBase I (TwoStepTower.isFiniteType_of_isLocallyNoetherian I))
    M.isProj
  isBir := by
    haveI := M.isProper
    haveI : IsProper (blowUpToBase I) :=
      TwoStepTower.isProper_blowUpToBase (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
    have hc := codim_one_le M hF hF' hFF hirr hIsm hIsub hIst
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
    exact MMP.Mori.isBirationalMorphism_comp_of_isBirational M.g (blowUpToBase I)
      (Bridges.isBirational_of_isBirationalMorphism M.isBir)
      (Bridges.isBirational_of_isBirationalMorphism (isBirationalMorphism_blowUpToBase I hirr hc))
  T := MMP.Intersection.reducedDivisorOf (newPrimes (M.g ≫ sX) hFF hIsub
    (centre_isSmoothBlowup M hIsm) hirr (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst) M.T)
  red := MMP.Intersection.isReducedEffective_reducedDivisorOf _
  snc := by
    haveI := M.isVariety
    rw [Category.assoc]
    exact isSNC_newBoundary (M.g ≫ sX) hFF hIsub (centre_isSmoothBlowup M hIsm) hirr _ M.isSmooth
      M.snc hF hF' hIst
  supp := by
    rw [MMP.Intersection.support_reducedDivisorOf, iUnion_newPrimes (M.g ≫ sX) hFF hIsub
      (centre_isSmoothBlowup M hIsm) hirr (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst) hF,
      M.supp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  exc := by
    haveI := M.isProper
    rw [MMP.Intersection.support_reducedDivisorOf, iUnion_newPrimes (M.g ≫ sX) hFF hIsub
      (centre_isSmoothBlowup M hIsm) hirr (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst) hF]
    exact exceptionalSet_comp_subset M.g (blowUpToBase I) I.support
      (isIso_blowUp_restrict_compl_support I) M.exc
      (fun y hy => Set.mem_biUnion hF (hIsub hy).1)
  crep := by
    intro H U0 τ hH hgen
    have hc := codim_one_le M hF hF' hFF hirr hIsm hIsub hIst
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
    haveI := isDominant_blowUpToBase I hirr hc
    haveI := M.isVariety
    have hbf := M.isBir.functionFieldMap_bijective
    have hbπ := (isBirationalMorphism_blowUpToBase I hirr hc).functionFieldMap_bijective
    have htrY := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq
      (sX := M.g ≫ sX) M.dim
    have htr : (letI := MMP.Mori.functionFieldAlgebra sX
        (Algebra.trdeg k X.functionField).toNat) = n := by
      rw [MMP.Mori.trdeg_functionField_eq_of_bijective sX M.g hbf]; exact htrY
    rw [← MMP.Flips.pullbackRationalPluriForms_comp M.g (blowUpToBase I) hbf hbπ htr τ]
    exact ordForm_pullback_blowUp (M.g ≫ sX) M.isSmooth M.red M.snc hF hF' hFF hirr hIsm hIsub
      hIst (centre_isSmoothBlowup M hIsm) hc M.dim _
      (pullbackRationalPluriForms_ne_zero' M.g hbf htr hgen.1) (M.g ⁻¹ᵁ U0)
      (fun G hG => M.crep G U0 τ hG hgen) H hH

include hF hF' hFF in
/-- Blowing up the intersection of two boundary components extends the blow-up sequence. -/
theorem blowUpModel_isStratumTower (hM : M.IsStratumTower)
    (hIFF : (I.support : Set M.Y) = (F.support : Set M.Y) ∩ F'.support)
    (hIv : I = Scheme.IdealSheafData.vanishingIdeal I.support) :
    (blowUpModel M hF hF' hFF hirr hIsm hIsub hIst).IsStratumTower := by
  obtain ⟨B, h, hg, hB⟩ := hM
  have hset : M.g.base ⁻¹' (⋃ P ∈ Δ.support, (P.support : Set X)) ∪
      (exceptionalSet M.g : Set M.Y) = ⋃ G ∈ M.T.support, (G.support : Set M.Y) := by
    rw [← M.supp]
    exact Set.union_eq_left.2 (M.supp ▸ M.exc)
  have hZ : BlowupTower.IsBoundaryStratumCentre (⋃ P ∈ Δ.support, (P.support : Set X)) M.g I := by
    unfold BlowupTower.IsBoundaryStratumCentre
    rw [hset, componentsOf_iUnion_support]
    exact ⟨F.support, ⟨F, hF, rfl⟩, F'.support, ⟨F', hF', rfl⟩,
      fun h => hFF (eq_of_support_subset h.le), hIFF, hIv⟩
  exact BlowupTower.exists_snoc _ B h M.g hg hB I hZ

end BlowUpModel

section Centre

/-- **Centres lift along proper morphisms** (valuative criterion). -/
theorem exists_dominates_of_isProper {X' Y : Scheme.{uP}} [IsIntegral X'] [IsIntegral Y]
    (g : Y ⟶ X') [IsProper g] [IsDominant g] (ξY : Valuation Y.functionField ℤᵐ⁰) (x : X')
    (hx : Dominates (ξY.comap (functionFieldMap g)) x) :
    ∃ y : Y, Dominates ξY y ∧ g y = x := by
  let R := ξY.valuationSubring
  let φ : X'.presheaf.stalk x →+* R :=
    ((functionFieldMap g).comp (algebraMap (X'.presheaf.stalk x) X'.functionField)).codRestrict R
      fun b => (ξY.mem_valuationSubring_iff _).2 (hx.1 b)
  have hgen : genericPoint X' ⤳ x := (genericPoint_spec X').specializes trivial
  have hex : ValuativeCriterion.Existence g := by
    have h : @IsProper _ _ g := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq g :=
    { R := R
      K := Y.functionField
      i₁ := Y.fromSpecStalk (genericPoint Y)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X'.fromSpecStalk x
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk g,
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫ l =
      Y.fromSpecStalk (genericPoint Y) := hl₁
  set y := l (IsLocalRing.closedPoint R)
  have hy : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes trivial
  let f := Scheme.stalkClosedPointTo l
  have hf : f ≫ CommRingCat.ofHom (algebraMap R Y.functionField) =
      Y.presheaf.stalkSpecializes hy := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk y)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hfa : ∀ a : Y.presheaf.stalk y,
      algebraMap _ Y.functionField a = ((f.hom a : R) : Y.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hf).symm
  refine ⟨y, ⟨fun a => ?_, fun a ha => ?_⟩, ?_⟩
  · rw [hfa]; exact (f.hom a).2
  · rw [hfa]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu))
  · have h2 : l ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ X'.fromSpecStalk x := hl₂
    have h3 : g (l (IsLocalRing.closedPoint R)) =
        X'.fromSpecStalk x (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint R)) :=
      congrArg (fun m : Spec (.of R) ⟶ X' => m (IsLocalRing.closedPoint R)) h2
    change g (l (IsLocalRing.closedPoint R)) = x
    rw [h3]
    have : IsLocalHom φ := by
      refine ⟨fun a ha => ?_⟩
      by_contra hna
      have hlt : ξY ((functionFieldMap g) (algebraMap _ X'.functionField a)) < 1 :=
        hx.2 a ((IsLocalRing.mem_maximalIdeal _).2 hna)
      obtain ⟨b, hb⟩ := ha.exists_right_inv
      have hb' : (functionFieldMap g) (algebraMap _ X'.functionField a) * (b : Y.functionField) =
          1 := congrArg Subtype.val hb
      have := mul_lt_one_of_lt_of_le hlt ((ξY.mem_valuationSubring_iff _).1 b.2)
      rw [← map_mul, hb', map_one] at this
      exact lt_irrefl _ this
    haveI : IsLocalHom (CommRingCat.ofHom φ).hom := this
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

end Centre

end SNCModel

namespace CentreLifting

open MMP.Mori MMP.Resolution MMP.Threefold.Resolution PrimeDivisorUnion StratumBlowup SNCBlowup
  LocalEquation BlowupCrepancy SNCModel

set_option linter.unusedSectionVars false

/-- A dominating valuation takes the value `1` on units of the local ring. -/
theorem valuation_algebraMap_eq_one_of_isUnit {Z : Scheme.{uP}} [IsIntegral Z] {y : Z}
    {ξ : Valuation Z.functionField ℤᵐ⁰} (hξ : Dominates ξ y) {r : Z.presheaf.stalk y}
    (hr : IsUnit r) : ξ (algebraMap _ Z.functionField r) = 1 :=
  Valuation.Integers.one_of_isUnit' hr hξ.1

section Factor

variable {Z : Scheme.{uP}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]

/-- The order along a prime divisor of a product of integer powers of nonzero rational functions
is the corresponding sum of orders. -/
theorem ord_prod_zpow (H0 : MMP.Mori.PrimeDivisor Z) (Q : Finset (MMP.Mori.PrimeDivisor Z))
    (w : MMP.Mori.PrimeDivisor Z → Z.functionField) (hw : ∀ H ∈ Q, w H ≠ 0)
    (e : MMP.Mori.PrimeDivisor Z → ℤ) :
    Z.ord (∏ H ∈ Q, w H ^ e H) H0.genericPoint = ∑ H ∈ Q, e H * Z.ord (w H) H0.genericPoint := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | insert H Q hH ih =>
    rw [Finset.prod_insert hH, Finset.sum_insert hH,
      Scheme.ord_mul (zpow_ne_zero _ (hw H (Finset.mem_insert_self H Q)))
        (Finset.prod_ne_zero_iff.mpr fun H' hH' =>
          zpow_ne_zero _ (hw H' (Finset.mem_insert_of_mem hH'))),
      MMP.Mori.ord_zpow _ (hw H (Finset.mem_insert_self H Q)),
      ih fun H' hH' => hw H' (Finset.mem_insert_of_mem hH')]

open Classical in
/-- **Hartogs factorization of a valuation.** If `ξ` dominates `𝒪_{Z,y}`, `Q` is a finite set of
prime divisors through `y` with local equations `u_H` at `y`, and `f` has order zero along every
other prime divisor through `y`, then `ξ(f) = ∏_{H ∈ Q} ξ(u_H)^{ord_H f}`. -/
theorem valuation_eq_prod (y : Z) (ξ : Valuation Z.functionField ℤᵐ⁰) (hξ : Dominates ξ y)
    (Q : Finset (MMP.Mori.PrimeDivisor Z)) (hQ : ∀ H ∈ Q, y ∈ (H.support : Set Z))
    (u : MMP.Mori.PrimeDivisor Z → Z.presheaf.stalk y)
    (hu : ∀ H ∈ Q, IdealSheafData.stalk H.idealSheaf y = Ideal.span {u H})
    (f : Z.functionField) (hf : f ≠ 0)
    (hf' : ∀ H : MMP.Mori.PrimeDivisor Z, y ∈ (H.support : Set Z) → H ∉ Q →
      Z.ord f H.genericPoint = 0) :
    ξ f = ∏ H ∈ Q, ξ (algebraMap _ Z.functionField (u H)) ^ Z.ord f H.genericPoint := by
  have hu0 : ∀ H ∈ Q, algebraMap _ Z.functionField (u H) ≠ 0 := fun H hH =>
    localEq_ne_zero H (hQ H hH) (hu H hH)
  set P := ∏ H ∈ Q, (algebraMap _ Z.functionField (u H)) ^ (-Z.ord f H.genericPoint) with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun H hH => zpow_ne_zero _ (hu0 H hH)
  have hb0 : f * P ≠ 0 := mul_ne_zero hf hP0
  have hordb : ∀ Γ : MMP.Mori.PrimeDivisor Z, y ∈ Γ.support → Z.ord (f * P) Γ.genericPoint = 0 := by
    intro Γ hΓ
    rw [Scheme.ord_mul hf hP0, hP, ord_prod_zpow Γ Q _ hu0]
    have hterm : ∀ H ∈ Q, -Z.ord f H.genericPoint *
        Z.ord (algebraMap _ Z.functionField (u H)) Γ.genericPoint =
          if Γ = H then -Z.ord f Γ.genericPoint else 0 := by
      intro H hH
      rw [ord_localEq Γ H hΓ (hQ H hH) (hu H hH)]
      split_ifs with h
      · subst h; ring
      · ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
    split_ifs with hΓQ
    · ring
    · rw [hf' Γ hΓ hΓQ]; ring
  obtain ⟨r, hr, hrb⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero y hb0 hordb
  have hfP : f = algebraMap _ Z.functionField r * P⁻¹ := by
    rw [hrb]; field_simp
  have hlhs : ξ f = (ξ P)⁻¹ := by
    conv_lhs => rw [hfP]
    rw [map_mul, valuation_algebraMap_eq_one_of_isUnit hξ hr, one_mul, map_inv₀]
  rw [hlhs, hP, map_prod, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun H _ => ?_
  rw [map_zpow₀, ← zpow_neg, neg_neg]

end Factor

/-- **The order valuation of a regular point.** At a point `y` with a regular system of
parameters `z`, some valuation dominating `𝒪_{Z,y}` takes the value `exp (-1)` on each `z i`. -/
theorem exists_orderValuation {Z : Scheme.{uP}} [IsIntegral Z] [IsLocallyNoetherian Z] (y : Z)
    {n : ℕ} {z : Fin n → Z.presheaf.stalk y} (hz : IsRegularSystemOfParameters z) :
    ∃ ν : Valuation Z.functionField ℤᵐ⁰, SNCModel.Dominates ν y ∧
      ∀ i, ν (algebraMap _ Z.functionField (z i)) = WithZero.exp (-1) := by
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  have := IsRegularLocalRing.isDomain (Z.presheaf.stalk y)
  obtain ⟨ν, -, hz', h1, h2⟩ := WeightedOrder.exists_valuation_weightedOrder' z (fun _ => 1)
    (K := Z.functionField) (fun _ => Nat.one_pos) hz.1 (by rw [hz.2]; simp)
  exact ⟨ν, ⟨h1, h2⟩, fun i => by simpa using hz' i⟩

section BlowupLocal

variable {k : Type uP} [Field k] {Y : Scheme.{uP}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y] {I : Y.IdealSheafData}
  (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
  (hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))

/-- Orders along a strict transform are orders downstairs. -/
theorem ord_blowUp_of_ne {H : MMP.Mori.PrimeDivisor (blowUp I)} (hH : H ≠ excE sY h hirr hc)
    (f : Y.functionField) :
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
    haveI := isDominant_blowUpToBase I hirr hc
    haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
    haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
    (blowUp I).ord (functionFieldMap (blowUpToBase I) f) H.genericPoint =
      Y.ord f (downPrime sY h hirr hc hH).genericPoint := by
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI := isDominant_blowUpToBase I hirr hc
  haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
  have hnot := map_genericPoint_notMem_of_ne sY h hirr hc hH
  haveI : IsIso ((blowUpToBase I).stalkMap H.genericPoint) :=
    isIso_stalkMap_of_mem_biregularLocus _ (mem_biregularLocus_of_notMem I hnot)
  exact MMP.Positivity.ord_functionFieldMap_of_isIso (blowUpToBase I) H _
    (genericPoint_downPrime sY h hirr hc hH).symm f

/-- The support of a non-exceptional prime divisor of the blow-up maps into the prime divisor
below it. -/
theorem map_mem_downPrime {H : MMP.Mori.PrimeDivisor (blowUp I)} (hH : H ≠ excE sY h hirr hc)
    {y' : blowUp I} (hy' : y' ∈ (H.support : Set (blowUp I))) :
    blowUpToBase I y' ∈ ((downPrime sY h hirr hc hH).support : Set Y) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    show AlgebraicGeometry.PrimeDivisor.genericPoint (downPrime sY h hirr hc hH) = _ from
      genericPoint_downPrime sY h hirr hc hH]
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy'
  have := image_closure_subset_closure_image (blowUpToBase I).continuous ⟨y', hy', rfl⟩
  rwa [Set.image_singleton] at this

/-- The image of the strict transform of a prime divisor `G` is `G`. -/
theorem downPrime_strictPrime {G : MMP.Mori.PrimeDivisor Y}
    (hG : G.genericPoint ∉ (I.support : Set Y)) (hne : strictPrime I G hG ≠ excE sY h hirr hc) :
    downPrime sY h hirr hc hne = G :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    ((genericPoint_downPrime sY h hirr hc hne).trans (map_genericPoint_strictPrime I hG))

/-- The strict transform of a prime divisor is not the exceptional divisor. -/
theorem strictPrime_ne_excE {G : MMP.Mori.PrimeDivisor Y}
    (hG : G.genericPoint ∉ (I.support : Set Y)) : strictPrime I G hG ≠ excE sY h hirr hc := by
  intro he
  have := map_genericPoint_strictPrime I hG
  rw [he] at this
  apply hG
  rw [← this, ← closure_map_genericPoint_excE sY h hirr hc]
  exact subset_closure rfl

/-- A prime divisor of the blow-up other than the exceptional divisor is the strict transform of
its image. -/
theorem strictPrime_downPrime {H : MMP.Mori.PrimeDivisor (blowUp I)} (hH : H ≠ excE sY h hirr hc)
    (hG : (downPrime sY h hirr hc hH).genericPoint ∉ (I.support : Set Y)) :
    strictPrime I (downPrime sY h hirr hc hH) hG = H :=
  strictPrime_eq_of_map I hG (genericPoint_downPrime sY h hirr hc hH).symm

omit [IsNormal Y] in
/-- The image of the generic point of the exceptional divisor specializes to every point of the
centre. -/
theorem map_genericPoint_excE_specializes {p : Y} (hp : p ∈ (I.support : Set Y)) :
    blowUpToBase I (excE sY h hirr hc).genericPoint ⤳ p := by
  rwa [specializes_iff_mem_closure, closure_map_genericPoint_excE sY h hirr hc]

open Classical in
/-- The order along the exceptional divisor of the pull-back of a local equation of a component
of the boundary. -/
theorem ord_excE_of_localEq [CharZero k] [LocallyOfFiniteType sY] [QuasiCompact sY]
    {T : Divisor Y} (hT : T.IsSNC sY) {F F' : MMP.Mori.PrimeDivisor Y} (hF : F ∈ T.support)
    (hF' : F' ∈ T.support) (hFF : F ≠ F') (hIsm : IsSmoothScheme (I.subschemeι ≫ sY))
    (hIsub : (I.support : Set Y) ⊆ (F.support : Set Y) ∩ F'.support)
    (hIst : ∀ y ∈ I.support, IdealSheafData.stalk I y =
      IdealSheafData.stalk F.idealSheaf y ⊔ IdealSheafData.stalk F'.idealSheaf y)
    {p : Y} (hp : p ∈ (I.support : Set Y)) {G : MMP.Mori.PrimeDivisor Y} (hG : G ∈ T.support)
    (hpG : p ∈ (G.support : Set Y)) {x : Y.presheaf.stalk p}
    (hx : IdealSheafData.stalk G.idealSheaf p = Ideal.span {x}) :
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
    haveI := isDominant_blowUpToBase I hirr hc
    haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
    haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
    (blowUp I).ord (functionFieldMap (blowUpToBase I) (algebraMap _ Y.functionField x))
      (excE sY h hirr hc).genericPoint = if G = F ∨ G = F' then 1 else 0 := by
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI := isDominant_blowUpToBase I hirr hc
  haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
  have hc2 := codimension_centre_eq_two sY hT hF hF' hFF hirr hIsm hIsub hIst
  set y0 := blowUpToBase I (excE sY h hirr hc).genericPoint with hy0
  have hsp : y0 ⤳ p := map_genericPoint_excE_specializes sY h hirr hc hp
  have hy0I : y0 ∈ (I.support : Set Y) := by
    rw [← closure_map_genericPoint_excE sY h hirr hc]; exact subset_closure rfl
  set x' := (Y.presheaf.stalkSpecializes hsp).hom x
  have halg : algebraMap _ Y.functionField x = algebraMap _ Y.functionField x' :=
    (MMP.Mori.algebraMap_stalkSpecializes hsp x).symm
  have hx' : IdealSheafData.stalk G.idealSheaf y0 = Ideal.span {x'} := by
    rw [MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes G.idealSheaf hsp, hx, Ideal.map_span,
      Set.image_singleton]
  have hdim := ringKrullDim_stalk_map_genericPoint_excE sY h hirr hc hc2
  obtain ⟨n, z, a, b, hz, hab, ha, hb⟩ :=
    exists_params_of_isSNC hT hF hF' hFF (hIsub hy0I).1 (hIsub hy0I).2
  have hJ : IdealSheafData.stalk I y0 = Ideal.span (z '' (({a, b} : Finset (Fin n)) : Set _)) :=
    by rw [hIst _ hy0I, ha, hb, span_pair_eq_span_image]
  have hfa : functionFieldMap (blowUpToBase I) (algebraMap _ Y.functionField x) =
      algebraMap _ (blowUp I).functionField
        (((blowUpToBase I).stalkMap (excE sY h hirr hc).genericPoint).hom x') := by
    rw [halg, MMP.Mori.functionFieldMap_algebraMap_stalk]
  rw [hfa]
  have hgen : ∀ c ∈ ({a, b} : Finset (Fin n)), ∀ w : Y.presheaf.stalk y0,
      Ideal.span {w} = Ideal.span {z c} →
      (blowUp I).ord (algebraMap _ (blowUp I).functionField
        (((blowUpToBase I).stalkMap (excE sY h hirr hc).genericPoint).hom w))
        (excE sY h hirr hc).genericPoint = 1 := by
    intro c hc' w hw
    obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hw
    have hval := divisorialValuation_excE_param sY h hirr hc hz hJ hc'
    have hv' : (excE sY h hirr hc).divisorialValuation (algebraMap _ (blowUp I).functionField
        (((blowUpToBase I).stalkMap (excE sY h hirr hc).genericPoint).hom w)) =
          WithZero.exp (-1) := by
      have e1 := congrArg (fun t => (excE sY h hirr hc).divisorialValuation
        (algebraMap _ (blowUp I).functionField
          (((blowUpToBase I).stalkMap (excE sY h hirr hc).genericPoint).hom t))) hv
      simp only [map_mul] at e1
      rwa [hval, divisorialValuation_algebraMap_of_isUnit' _ ((v.isUnit).map _), mul_one] at e1
    refine ord_eq_of_divisorialValuation_eq _ ?_ hv'
    intro h0
    rw [h0, map_zero] at hv'
    exact WithZero.zero_ne_coe hv'
  split_ifs with hGFF
  · rcases hGFF with rfl | rfl
    · exact hgen a (by simp) x' (by rw [← hx', ha])
    · exact hgen b (by simp) x' (by rw [← hx', hb])
  · have hy0G : y0 ∉ (G.support : Set Y) := fun hmem => hGFF <|
      mem_pair_of_ringKrullDim_eq_two sY hT hF hF' hFF (hIsub hy0I).1 (hIsub hy0I).2 hdim hG hmem
    have htop := MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support G hy0G
    rw [hx', Ideal.span_singleton_eq_top] at htop
    have hu := htop.map ((blowUpToBase I).stalkMap (excE sY h hirr hc).genericPoint).hom
    refine ord_eq_of_divisorialValuation_eq _ ?_ ?_
    · intro h0
      have := divisorialValuation_algebraMap_of_isUnit' _ hu
      rw [h0, map_zero] at this
      exact zero_ne_one this
    · rw [divisorialValuation_algebraMap_of_isUnit' _ hu]; rfl

open Classical in
/-- **The valuation of a pulled-back local equation at a point over the centre.** -/
theorem valuation_localEq_blowUp [CharZero k] [LocallyOfFiniteType sY] [QuasiCompact sY]
    {T : Divisor Y} (hT : T.IsSNC sY) {F F' : MMP.Mori.PrimeDivisor Y} (hF : F ∈ T.support)
    (hF' : F' ∈ T.support) (hFF : F ≠ F') (hIsm : IsSmoothScheme (I.subschemeι ≫ sY))
    (hIsub : (I.support : Set Y) ⊆ (F.support : Set Y) ∩ F'.support)
    (hIst : ∀ y ∈ I.support, IdealSheafData.stalk I y =
      IdealSheafData.stalk F.idealSheaf y ⊔ IdealSheafData.stalk F'.idealSheaf y)
    (y' : blowUp I) (hy : blowUpToBase I y' ∈ (I.support : Set Y))
    (u : MMP.Mori.PrimeDivisor (blowUp I) → (blowUp I).presheaf.stalk y')
    (hu : ∀ H ∈ newPrimes sY hFF hIsub h hirr hc T, y' ∈ (H.support : Set (blowUp I)) →
      IdealSheafData.stalk H.idealSheaf y' = Ideal.span {u H})
    {G : MMP.Mori.PrimeDivisor Y} (hG : G ∈ T.support)
    (hyG : blowUpToBase I y' ∈ (G.support : Set Y)) {x : Y.presheaf.stalk (blowUpToBase I y')}
    (hx : IdealSheafData.stalk G.idealSheaf (blowUpToBase I y') = Ideal.span {x}) :
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
    haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
    haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
    ∀ ξ' : Valuation (blowUp I).functionField ℤᵐ⁰, SNCModel.Dominates ξ' y' →
    ξ' (algebraMap _ (blowUp I).functionField (((blowUpToBase I).stalkMap y').hom x)) =
      (if G = F ∨ G = F' then ξ' (algebraMap _ _ (u (excE sY h hirr hc))) else 1) *
      (if y' ∈ ((strictPrime I G (genericPoint_notMem_of_subset_inter I hFF hIsub G)).support :
          Set (blowUp I))
        then ξ' (algebraMap _ _
          (u (strictPrime I G (genericPoint_notMem_of_subset_inter I hFF hIsub G))))
        else 1) := by
  intro ξ' hξ'
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI := isDominant_blowUpToBase I hirr hc
  haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
  set E := excE sY h hirr hc
  set hG0 := genericPoint_notMem_of_subset_inter I hFF hIsub G
  set sG := strictPrime I G hG0
  set Ps := newPrimes sY hFF hIsub h hirr hc T
  have hEPs : E ∈ Ps := (mem_newPrimes sY hFF hIsub h hirr hc).mpr (Or.inl rfl)
  have hsGPs : sG ∈ Ps := (mem_newPrimes sY hFF hIsub h hirr hc).mpr (Or.inr ⟨G, hG, rfl⟩)
  have hyE : y' ∈ (E.support : Set (blowUp I)) := by rw [coe_support_excE]; exact hy
  have hsGE : sG ≠ E := strictPrime_ne_excE sY h hirr hc hG0
  have hfeq : algebraMap _ (blowUp I).functionField (((blowUpToBase I).stalkMap y').hom x) =
      functionFieldMap (blowUpToBase I) (algebraMap _ Y.functionField x) :=
    (MMP.Mori.functionFieldMap_algebraMap_stalk _ _ _).symm
  have hx0 := localEq_ne_zero G hyG hx
  have hf0 : functionFieldMap (blowUpToBase I) (algebraMap _ Y.functionField x) ≠ 0 :=
    (map_ne_zero _).mpr hx0
  -- orders along prime divisors through `y'`
  have hord_ne : ∀ H : MMP.Mori.PrimeDivisor (blowUp I), (hH : H ≠ E) →
      y' ∈ (H.support : Set (blowUp I)) →
      (blowUp I).ord (functionFieldMap (blowUpToBase I) (algebraMap _ Y.functionField x))
        H.genericPoint = if H = sG then 1 else 0 := by
    intro H hH hyH
    rw [ord_blowUp_of_ne sY h hirr hc hH, ord_localEq _ G (map_mem_downPrime sY h hirr hc hH hyH)
      hyG hx]
    have hiff : downPrime sY h hirr hc hH = G ↔ H = sG := by
      constructor
      · intro hd
        rw [← strictPrime_downPrime sY h hirr hc hH
          (genericPoint_notMem_of_subset_inter I hFF hIsub _)]
        simp only [sG, hd]
      · rintro rfl; exact downPrime_strictPrime sY h hirr hc hG0 hH
    simp only [hiff]
  set Q := Ps.filter fun H => y' ∈ (H.support : Set (blowUp I))
  have hQ : ∀ H ∈ Q, y' ∈ (H.support : Set (blowUp I)) := fun H hH => (Finset.mem_filter.mp hH).2
  rw [hfeq, valuation_eq_prod y' ξ' hξ' Q hQ u (fun H hH => hu H (Finset.mem_filter.mp hH).1
    (hQ H hH)) _ hf0 ?_]
  · have hEQ : E ∈ Q := Finset.mem_filter.mpr ⟨hEPs, hyE⟩
    rw [← Finset.mul_prod_erase Q _ hEQ, ord_excE_of_localEq sY h hirr hc hT hF hF' hFF hIsm hIsub
      hIst hy hG hyG hx]
    congr 1
    · split_ifs <;> simp
    · rw [Finset.prod_congr rfl fun H hH => by
        rw [hord_ne H (Finset.ne_of_mem_erase hH) (hQ H (Finset.mem_of_mem_erase hH))]]
      have : ∀ H ∈ Q.erase E, ξ' (algebraMap _ _ (u H)) ^ (if H = sG then (1 : ℤ) else 0) =
          if H = sG then ξ' (algebraMap _ _ (u sG)) else 1 := by
        intro H _; split_ifs with h1 <;> simp [h1]
      rw [Finset.prod_congr rfl this, Finset.prod_ite_eq']
      congr 1
      simp only [Finset.mem_erase, Finset.mem_filter, Q]
      exact propext ⟨fun h1 => h1.2.2, fun h1 => ⟨hsGE, hsGPs, h1⟩⟩
  · intro H hyH hHQ
    have hHE : H ≠ E := fun h1 => hHQ (h1 ▸ Finset.mem_filter.mpr ⟨hEPs, hyE⟩)
    rw [hord_ne H hHE hyH, if_neg]
    rintro rfl
    exact hHQ (Finset.mem_filter.mpr ⟨hsGPs, hyH⟩)

open Classical in
/-- Local equations of the components of the new boundary at a point, and the order valuation
there. -/
theorem exists_localEqs_newPrimes [CharZero k] [LocallyOfFiniteType sY] [QuasiCompact sY]
    (hYs : IsSmoothScheme sY) {T : Divisor Y} (hT : T.IsSNC sY) {F F' : MMP.Mori.PrimeDivisor Y}
    (hF : F ∈ T.support) (hF' : F' ∈ T.support) (hFF : F ≠ F')
    (hIsub : (I.support : Set Y) ⊆ (F.support : Set Y) ∩ F'.support)
    (hIst : ∀ y ∈ I.support, IdealSheafData.stalk I y =
      IdealSheafData.stalk F.idealSheaf y ⊔ IdealSheafData.stalk F'.idealSheaf y)
    (y' : blowUp I) :
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
    haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
    haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
    ∃ u : MMP.Mori.PrimeDivisor (blowUp I) → (blowUp I).presheaf.stalk y',
      (∀ H ∈ newPrimes sY hFF hIsub h hirr hc T, y' ∈ (H.support : Set (blowUp I)) →
        IdealSheafData.stalk H.idealSheaf y' = Ideal.span {u H}) ∧
      ∃ ν : Valuation (blowUp I).functionField ℤᵐ⁰, SNCModel.Dominates ν y' ∧
        ∀ H ∈ newPrimes sY hFF hIsub h hirr hc T, y' ∈ (H.support : Set (blowUp I)) →
          ν (algebraMap _ _ (u H)) = WithZero.exp (-1) := by
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI := isDominant_blowUpToBase I hirr hc
  haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  have hsnc := isSNC_newBoundary sY hFF hIsub h hirr hc hYs hT hF hF' hIst
  obtain ⟨n, z', j', hz', hj', hI'⟩ := hsnc.2 y'
  let u : MMP.Mori.PrimeDivisor (blowUp I) → (blowUp I).presheaf.stalk y' := fun H =>
    if hH : H ∈ newPrimes sY hFF hIsub h hirr hc T ∧ y' ∈ (H.support : Set (blowUp I))
    then z' (j' ⟨H, by rwa [MMP.Intersection.support_reducedDivisorOf]⟩) else 0
  have hu : ∀ H (hH : H ∈ newPrimes sY hFF hIsub h hirr hc T) (hyH : y' ∈ (H.support : Set _)),
      u H = z' (j' ⟨H, by rw [MMP.Intersection.support_reducedDivisorOf]; exact ⟨hH, hyH⟩⟩) := by
    intro H hH hyH; simp only [u, dif_pos (And.intro hH hyH)]
  obtain ⟨ν, hν, hνz⟩ := exists_orderValuation y' hz'
  refine ⟨u, fun H hH hyH => ?_, ν, hν, fun H hH hyH => by rw [hu H hH hyH, hνz]⟩
  rw [hu H hH hyH]
  exact hI' ⟨H, by rwa [MMP.Intersection.support_reducedDivisorOf], hyH⟩

include h hirr hc in
/-- At a point over the centre, the strict transforms of `F` and `F'` do not both pass. -/
theorem not_and_mem_support_strictPrime [CharZero k] [LocallyOfFiniteType sY] [QuasiCompact sY]
    (hYs : IsSmoothScheme sY) {T : Divisor Y} (hT : T.IsSNC sY) {F F' : MMP.Mori.PrimeDivisor Y}
    (hF : F ∈ T.support) (hF' : F' ∈ T.support) (hFF : F ≠ F')
    (hIsm : IsSmoothScheme (I.subschemeι ≫ sY))
    (hIsub : (I.support : Set Y) ⊆ (F.support : Set Y) ∩ F'.support)
    (hIst : ∀ y ∈ I.support, IdealSheafData.stalk I y =
      IdealSheafData.stalk F.idealSheaf y ⊔ IdealSheafData.stalk F'.idealSheaf y)
    (y' : blowUp I) (hy : blowUpToBase I y' ∈ (I.support : Set Y)) :
    ¬ (y' ∈ ((strictPrime I F (genericPoint_notMem_of_subset_inter I hFF hIsub F)).support :
          Set (blowUp I)) ∧
        y' ∈ ((strictPrime I F' (genericPoint_notMem_of_subset_inter I hFF hIsub F')).support :
          Set (blowUp I))) := by
  classical
  rintro ⟨h1, h2⟩
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI := isDominant_blowUpToBase I hirr hc
  haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  obtain ⟨u, huI, ν, hν, hνu⟩ :=
    exists_localEqs_newPrimes sY h hirr hc hYs hT hF hF' hFF hIsub hIst y'
  obtain ⟨m, z, a, b, hz, hab, ha, hb⟩ :=
    exists_params_of_isSNC hT hF hF' hFF (hIsub hy).1 (hIsub hy).2
  set E := excE sY h hirr hc
  have hEPs : E ∈ newPrimes sY hFF hIsub h hirr hc T :=
    (mem_newPrimes sY hFF hIsub h hirr hc).mpr (Or.inl rfl)
  have hyE : y' ∈ (E.support : Set (blowUp I)) := by rw [coe_support_excE]; exact hy
  have hsF := (mem_newPrimes sY hFF hIsub h hirr hc).mpr (Or.inr ⟨F, hF, rfl⟩)
  have hsF' := (mem_newPrimes sY hFF hIsub h hirr hc).mpr (Or.inr ⟨F', hF', rfl⟩)
  have hvF := valuation_localEq_blowUp sY h hirr hc hT hF hF' hFF hIsm hIsub hIst y' hy u huI hF
    (hIsub hy).1 ha ν hν
  have hvF' := valuation_localEq_blowUp sY h hirr hc hT hF hF' hFF hIsm hIsub hIst y' hy u huI hF'
    (hIsub hy).2 hb ν hν
  rw [if_pos (Or.inl rfl), if_pos h1, hνu E hEPs hyE, hνu _ hsF h1] at hvF
  rw [if_pos (Or.inr rfl), if_pos h2, hνu E hEPs hyE, hνu _ hsF' h2] at hvF'
  -- the ideal of `E` at `y'`
  have hEst : IdealSheafData.stalk E.idealSheaf y' =
      Ideal.span {((blowUpToBase I).stalkMap y').hom (z a),
        ((blowUpToBase I).stalkMap y').hom (z b)} := by
    change IdealSheafData.stalk (I.comap (blowUpToBase I)) y' = _
    rw [IdealSheafData.stalk_comap, hIst _ hy, ha, hb, ← Ideal.span_insert, Ideal.map_span,
      Set.image_insert_eq, Set.image_singleton]
  have hmem : u E ∈ IdealSheafData.stalk E.idealSheaf y' := by
    rw [huI E hEPs hyE]; exact Ideal.subset_span rfl
  rw [hEst, Ideal.mem_span_pair] at hmem
  obtain ⟨c, d, hcd⟩ := hmem
  have hle : ν (algebraMap _ _ (u E)) ≤ WithZero.exp (-1) * WithZero.exp (-1) := by
    rw [← hcd, map_add, map_mul, map_mul]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [map_mul, hvF]; exact (mul_le_of_le_one_left' (hν.1 c)).trans le_rfl
    · rw [map_mul, hvF']; exact (mul_le_of_le_one_left' (hν.1 d)).trans le_rfl
  rw [hνu E hEPs hyE, ← WithZero.exp_add, WithZero.exp_le_exp] at hle
  norm_num at hle

include h hirr hc in
/-- Through a point over the centre pass the strict transforms of all other components of the
boundary through its image. -/
theorem mem_strictPrime_of_mem [CharZero k] [LocallyOfFiniteType sY] [QuasiCompact sY]
    (hYs : IsSmoothScheme sY) {T : Divisor Y} (hT : T.IsSNC sY) {F F' : MMP.Mori.PrimeDivisor Y}
    (hF : F ∈ T.support) (hF' : F' ∈ T.support) (hFF : F ≠ F')
    (hIsm : IsSmoothScheme (I.subschemeι ≫ sY))
    (hIsub : (I.support : Set Y) ⊆ (F.support : Set Y) ∩ F'.support)
    (hIst : ∀ y ∈ I.support, IdealSheafData.stalk I y =
      IdealSheafData.stalk F.idealSheaf y ⊔ IdealSheafData.stalk F'.idealSheaf y)
    (y' : blowUp I) (hy : blowUpToBase I y' ∈ (I.support : Set Y)) {G : MMP.Mori.PrimeDivisor Y}
    (hG : G ∈ T.support) (hGF : ¬ (G = F ∨ G = F'))
    (hyG : blowUpToBase I y' ∈ (G.support : Set Y)) :
    y' ∈ ((strictPrime I G (genericPoint_notMem_of_subset_inter I hFF hIsub G)).support :
      Set (blowUp I)) := by
  classical
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI := isDominant_blowUpToBase I hirr hc
  haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  obtain ⟨u, huI, ν, hν, -⟩ :=
    exists_localEqs_newPrimes sY h hirr hc hYs hT hF hF' hFF hIsub hIst y'
  obtain ⟨q, -, hq, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support G hyG
  obtain ⟨x, hx⟩ : ∃ x, IdealSheafData.stalk G.idealSheaf (blowUpToBase I y') = Ideal.span {x} := by
    obtain ⟨n, z, j, -, -, hI⟩ := hT.2 (blowUpToBase I y')
    exact ⟨_, hI ⟨G, hG, hyG⟩⟩
  have hv := valuation_localEq_blowUp sY h hirr hc hT hF hF' hFF hIsm hIsub hIst y' hy u huI hG hyG
    hx ν hν
  rw [if_neg hGF, one_mul] at hv
  by_contra hnot
  rw [if_neg hnot] at hv
  have hxm : x ∈ maximalIdeal (Y.presheaf.stalk (blowUpToBase I y')) :=
    IsLocalRing.le_maximalIdeal q.isPrime.ne_top (by rw [← hq, hx]; exact Ideal.subset_span rfl)
  have hφm : ((blowUpToBase I).stalkMap y').hom x ∈ maximalIdeal ((blowUp I).presheaf.stalk y') :=
    (IsLocalRing.mem_maximalIdeal _).2 fun hu' =>
      (IsLocalRing.mem_maximalIdeal _).1 hxm (isUnit_of_map_unit _ _ hu')
  have := hν.2 _ hφm
  rw [hv] at this
  exact lt_irrefl _ this

end BlowupLocal

section Topology

/-- The preimage of a preconnected set under a closed map with preconnected fibres,
onto a set containing it, is preconnected. -/
theorem isPreconnected_preimage_of_isClosedMap {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hcl : IsClosedMap f)
    (hfib : ∀ b, _root_.IsPreconnected (f ⁻¹' {b})) {s : Set β} (hs : _root_.IsPreconnected s)
    (hsf : s ⊆ Set.range f) : _root_.IsPreconnected (f ⁻¹' s) := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hsuv hdisj
  have hno : ∀ a, f a ∈ s → a ∈ u → a ∈ v → False := fun a h1 h2 h3 =>
    Set.eq_empty_iff_forall_notMem.1 hdisj a ⟨h1, h2, h3⟩
  -- each fibre lies in `u` or in `v`
  have hfib' : ∀ b ∈ s, f ⁻¹' {b} ⊆ u ∨ f ⁻¹' {b} ⊆ v := by
    intro b hb
    refine (isPreconnected_iff_subset_of_disjoint_closed.mp (hfib b)) u v hu hv
      (fun a ha => hsuv (show f a ∈ s by rw [Set.mem_singleton_iff.mp ha]; exact hb))
      (Set.eq_empty_iff_forall_notMem.2 fun a ⟨ha, hau, hav⟩ =>
        hno a (by rw [Set.mem_singleton_iff.mp ha]; exact hb) hau hav)
  have hdisj' : s ∩ (f '' u ∩ f '' v) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro b ⟨hb, ⟨a, hau, rfl⟩, ⟨a', ha'v, ha'⟩⟩
    rcases hfib' (f a) hb with h1 | h1
    · exact hno a' (by rw [ha']; exact hb) (h1 (by rw [Set.mem_preimage, ha']; rfl)) ha'v
    · exact hno a hb hau (h1 rfl)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hs) (f '' u) (f '' v)
    (hcl u hu) (hcl v hv) (fun b hb => by
      obtain ⟨a, rfl⟩ := hsf hb
      rcases hsuv hb with h | h
      exacts [Or.inl ⟨a, h, rfl⟩, Or.inr ⟨a, h, rfl⟩]) hdisj' with h | h
  · left
    intro a ha
    obtain ⟨a', ha'u, ha'⟩ := h ha
    rcases hfib' (f a) ha with h1 | h1
    · exact h1 rfl
    · exact (hno a' (by rw [ha']; exact ha) ha'u (h1 (by rw [Set.mem_preimage, ha']; rfl))).elim
  · right
    intro a ha
    obtain ⟨a', ha'v, ha'⟩ := h ha
    rcases hfib' (f a) ha with h1 | h1
    · exact (hno a' (by rw [ha']; exact ha) (h1 (by rw [Set.mem_preimage, ha']; rfl)) ha'v).elim
    · exact h1 rfl

end Topology

section PreimageCentre

variable {k : Type uP} [Field k] {Y : Scheme.{uP}} (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y]
  {I : Y.IdealSheafData} (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
  (hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))

include h hirr hc in
/-- The preimage of a preconnected subset of the centre is preconnected. -/
theorem isPreconnected_preimage_of_subset_centre {S : Set Y} (hS : _root_.IsPreconnected S)
    (hSI : S ⊆ I.support) : _root_.IsPreconnected (blowUpToBase I ⁻¹' S) := by
  set f := Stacks.AlgebraicGeometry.exceptionalSubschemeMap I
  have hfcl : IsClosedMap f := isClosedMap_exceptionalSubschemeMap I
  have hfib : ∀ z, _root_.IsPreconnected (f ⁻¹' {z}) := fun z =>
    (isConnected_preimage_exceptionalSubschemeMap sY I h hirr hc z).isPreconnected
  have hsurj : Function.Surjective f := surjective_exceptionalSubschemeMap sY I h hirr hc
  set S0 := I.subschemeι ⁻¹' S
  have hS0 : _root_.IsPreconnected S0 := by
    have himg : I.subschemeι '' S0 = S := Set.image_preimage_eq_of_subset (by
      rw [I.range_subschemeι]; exact hSI)
    rw [← himg] at hS
    exact (I.subschemeι.isClosedEmbedding.isInducing.isPreconnected_image).mp hS
  have h1 := isPreconnected_preimage_of_isClosedMap hfcl hfib hS0
    (fun z _ => hsurj z)
  have h2 := h1.image _ (exceptionalIdeal I).subschemeι.continuous.continuousOn
  convert h2 using 1
  ext y'
  constructor
  · intro hy'
    have hyE : y' ∈ ((exceptionalIdeal I).support : Set (blowUp I)) := by
      rw [exceptionalIdeal, Scheme.IdealSheafData.support_comap]
      exact hSI hy'
    rw [← (exceptionalIdeal I).range_subschemeι] at hyE
    obtain ⟨e, rfl⟩ := hyE
    refine ⟨e, ?_, rfl⟩
    change I.subschemeι (f e) ∈ S
    rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.subschemeMap_subschemeι,
      Scheme.Hom.comp_apply]
    exact hy'
  · rintro ⟨e, he, rfl⟩
    change blowUpToBase I ((exceptionalIdeal I).subschemeι e) ∈ S
    rw [← Scheme.Hom.comp_apply, ← Scheme.IdealSheafData.subschemeMap_subschemeι,
      Scheme.Hom.comp_apply]
    exact he

end PreimageCentre

section StepFacts

variable {k : Type uP} [Field k] [CharZero k] {X : Scheme.{uP}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX] {Δ : Divisor X}
  {n : ℕ} (M : SModel sX Δ n) {F F' : MMP.Mori.PrimeDivisor M.Y}
  (hF : F ∈ M.T.support) (hF' : F' ∈ M.T.support) (hFF : F ≠ F') {I : M.Y.IdealSheafData}
  (hirr : IsIrreducible (I.support : Set M.Y)) (hIsm : IsSmoothScheme (I.subschemeι ≫ M.g ≫ sX))
  (hIsub : (I.support : Set M.Y) ⊆ (F.support : Set M.Y) ∩ F'.support)
  (hIst : ∀ y ∈ I.support, IdealSheafData.stalk I y =
    IdealSheafData.stalk F.idealSheaf y ⊔ IdealSheafData.stalk F'.idealSheaf y)

attribute [local instance] SModel.isIntegral SModel.isDominant SModel.isLocallyNoetherian
  SModel.isNormal

/-- The order of `a` along the strict transform of a prime divisor `G` on the blown-up model is
its order along `G`. -/
theorem blowUpModel_ordZ_strict {η : X} (a : X.presheaf.stalk η) (G : MMP.Mori.PrimeDivisor M.Y) :
    (blowUpModel M hF hF' hFF hirr hIsm hIsub hIst).ordZ a
      (strictPrime I G (genericPoint_notMem_of_subset_inter I hFF hIsub G)) = M.ordZ a G := by
  have hc := codim_one_le M hF hF' hFF hirr hIsm hIsub hIst
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI := isDominant_blowUpToBase I hirr hc
  haveI : Smooth (M.g ≫ sX) := smooth_of_isSmoothScheme M.isSmooth
  have hne := strictPrime_ne_excE (M.g ≫ sX) (centre_isSmoothBlowup M hIsm) hirr hc
    (genericPoint_notMem_of_subset_inter I hFF hIsub G)
  haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup (M.g ≫ sX) I
    (centre_isSmoothBlowup M hIsm)).1
  haveI : IsLocallyNoetherian (blowUp I) :=
    isLocallyNoetherian_of_smooth (blowUpToBase I ≫ M.g ≫ sX)
  have key := ord_blowUp_of_ne (M.g ≫ sX) (centre_isSmoothBlowup M hIsm) hirr hc hne
    (functionFieldMap M.g (algebraMap _ X.functionField a))
  rw [downPrime_strictPrime] at key
  have e := MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply (blowUpToBase I) M.g
    (algebraMap _ X.functionField a)
  change (blowUp I).ord (functionFieldMap (blowUpToBase I ≫ M.g) (algebraMap _ X.functionField a))
    _ = M.Y.ord (functionFieldMap M.g (algebraMap _ _ a)) G.genericPoint
  rw [← e]
  exact key

open Classical in
/-- The order of a local equation `zj` of a component of `Δ` along the exceptional divisor of the
blown-up model is the sum of its orders along `F` and `F'`. -/
theorem blowUpModel_ordZ_excE {η : X} (zj : X.presheaf.stalk η) {P : MMP.Mori.PrimeDivisor X}
    (hP : P ∈ Δ.support) (hzP : IdealSheafData.stalk P.idealSheaf η = Ideal.span {zj})
    (hη : M.g (blowUpToBase I (excE (M.g ≫ sX) (centre_isSmoothBlowup M hIsm) hirr
      (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst)).genericPoint) ⤳ η) :
    (blowUpModel M hF hF' hFF hirr hIsm hIsub hIst).ordZ zj
      (excE (M.g ≫ sX) (centre_isSmoothBlowup M hIsm) hirr
        (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst)) = M.ordZ zj F + M.ordZ zj F' := by
  have hc := codim_one_le M hF hF' hFF hirr hIsm hIsub hIst
  have h := centre_isSmoothBlowup M hIsm
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI := isDominant_blowUpToBase I hirr hc
  haveI : Smooth (M.g ≫ sX) := smooth_of_isSmoothScheme M.isSmooth
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup (M.g ≫ sX) I h).1
  haveI : IsLocallyNoetherian (blowUp I) :=
    isLocallyNoetherian_of_smooth (blowUpToBase I ≫ M.g ≫ sX)
  haveI := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ M.g ≫ sX)
  haveI := M.isVariety
  set E := excE (M.g ≫ sX) h hirr hc
  set y0 := blowUpToBase I E.genericPoint
  set f := functionFieldMap M.g (algebraMap _ X.functionField zj)
  have hc2 := codimension_centre_eq_two (M.g ≫ sX) M.snc hF hF' hFF hirr hIsm hIsub hIst
  have hy0 : y0 ∈ (I.support : Set M.Y) := by
    rw [← closure_map_genericPoint_excE (M.g ≫ sX) h hirr hc]; exact subset_closure rfl
  have hdim := ringKrullDim_stalk_map_genericPoint_excE (M.g ≫ sX) h hirr hc hc2
  obtain ⟨m, w, a, b, hw, hab, ha, hb⟩ :=
    exists_params_of_isSNC M.snc hF hF' hFF (hIsub hy0).1 (hIsub hy0).2
  have hzj0 : algebraMap _ X.functionField zj ≠ 0 := by
    intro h0
    have h0' : zj = 0 := (map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h0
    by_cases hηP : η ∈ (P.support : Set X)
    · obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P hηP
      rw [hzP, h0', Ideal.span_singleton_eq_bot.mpr rfl] at hq
      rw [← hq, Ideal.height_bot] at hqh
      exact absurd hqh (by decide)
    · have := MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support P hηP
      rw [hzP, h0', Ideal.span_singleton_eq_bot.mpr rfl] at this
      exact bot_ne_top this
  have hf0 : f ≠ 0 := (map_ne_zero _).mpr hzj0
  -- `ξ = v_E` dominates the local ring at `y0`
  have hdom : SNCModel.Dominates (E.divisorialValuation.comap (functionFieldMap (blowUpToBase I)))
      y0 := by
    refine ⟨fun r => ?_, fun r hr => ?_⟩
    · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
      exact (E.divisorialValuation_le_one_iff _).2 ⟨_, rfl⟩
    · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
      refine (E.divisorialValuation_algebraMap_lt_one_iff _).2 ?_
      exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 hr (isUnit_of_map_unit _ _ hu)
  let u : MMP.Mori.PrimeDivisor M.Y → M.Y.presheaf.stalk y0 := fun G =>
    if G = F then w a else w b
  have hu : ∀ G ∈ ({F, F'} : Finset _), IdealSheafData.stalk G.idealSheaf y0 =
      Ideal.span {u G} := by
    intro G hG
    rcases Finset.mem_insert.mp hG with rfl | hG
    · simp only [u, if_pos rfl]; exact ha
    · rw [Finset.mem_singleton.mp hG]; simp only [u, if_neg (Ne.symm hFF)]; exact hb
  have hQ : ∀ G ∈ ({F, F'} : Finset _), y0 ∈ (G.support : Set M.Y) := by
    intro G hG
    rcases Finset.mem_insert.mp hG with rfl | hG
    · exact (hIsub hy0).1
    · rw [Finset.mem_singleton.mp hG]; exact (hIsub hy0).2
  have hf' : ∀ G : MMP.Mori.PrimeDivisor M.Y, y0 ∈ (G.support : Set M.Y) →
      G ∉ ({F, F'} : Finset _) → M.Y.ord f G.genericPoint = 0 := by
    intro G hG hGQ
    have hGT : G ∉ M.T.support := by
      intro hGT
      rcases mem_pair_of_ringKrullDim_eq_two (M.g ≫ sX) M.snc hF hF' hFF (hIsub hy0).1
        (hIsub hy0).2 hdim hGT hG with rfl | rfl
      · exact hGQ (by simp)
      · exact hGQ (by simp)
    have hsp : M.g G.genericPoint ⤳ η :=
      ((specializes_of_mem G hG).map M.g.continuous).trans hη
    have hwP : M.g G.genericPoint ∉ (P.support : Set X) := by
      intro hmem
      have : G.genericPoint ∈ ⋃ H ∈ M.T.support, (H.support : Set M.Y) := by
        rw [M.supp]; exact Set.mem_biUnion hP hmem
      obtain ⟨H, hH, hGH⟩ := Set.mem_iUnion₂.mp this
      exact hGT (eq_of_genericPoint_mem_support hGH ▸ hH)
    have htop := MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support P hwP
    rw [MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes P.idealSheaf hsp, hzP, Ideal.map_span,
      Set.image_singleton, Ideal.span_singleton_eq_top] at htop
    have hfeq : f = algebraMap _ M.Y.functionField
        ((M.g.stalkMap G.genericPoint).hom ((X.presheaf.stalkSpecializes hsp).hom zj)) := by
      simp only [f]
      rw [← MMP.Mori.algebraMap_stalkSpecializes hsp, MMP.Mori.functionFieldMap_algebraMap_stalk]
    rw [hfeq]
    exact G.ord_algebraMap_of_isUnit (htop.map _)
  have hval := valuation_eq_prod y0 _ hdom {F, F'} hQ u hu f hf0 hf'
  rw [Finset.prod_insert (by simpa using hFF), Finset.prod_singleton] at hval
  have hvF : (E.divisorialValuation.comap (functionFieldMap (blowUpToBase I)))
      (algebraMap _ M.Y.functionField (u F)) = WithZero.exp (-1) := by
    simp only [u, if_pos rfl, Valuation.comap_apply]
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact divisorialValuation_excE_param (M.g ≫ sX) h hirr hc hw
      (J := {a, b}) (by rw [hIst _ hy0, ha, hb, span_pair_eq_span_image]) (by simp)
  have hvF' : (E.divisorialValuation.comap (functionFieldMap (blowUpToBase I)))
      (algebraMap _ M.Y.functionField (u F')) = WithZero.exp (-1) := by
    simp only [u, if_neg (Ne.symm hFF), Valuation.comap_apply]
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact divisorialValuation_excE_param (M.g ≫ sX) h hirr hc hw
      (J := {a, b}) (by rw [hIst _ hy0, ha, hb, span_pair_eq_span_image]) (by simp)
  rw [hvF, hvF', ← WithZero.exp_zsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add] at hval
  have key : (blowUp I).ord (functionFieldMap (blowUpToBase I) f) E.genericPoint =
      M.Y.ord f F.genericPoint + M.Y.ord f F'.genericPoint := by
    refine ord_eq_of_divisorialValuation_eq E ((map_ne_zero _).mpr hf0) ?_
    rw [← Valuation.comap_apply, hval]
    congr 1; simp; ring
  have e := MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply (blowUpToBase I) M.g
    (algebraMap _ X.functionField zj)
  change (blowUp I).ord (functionFieldMap (blowUpToBase I ≫ M.g) (algebraMap _ X.functionField zj))
    _ = M.Y.ord f F.genericPoint + M.Y.ord f F'.genericPoint
  rw [← e]
  exact key

end StepFacts

end CentreLifting

namespace Subtraction

open MMP.Mori MMP.Resolution MMP.Threefold.Resolution PrimeDivisorUnion StratumBlowup SNCBlowup
  LocalEquation BlowupCrepancy SNCModel CentreLifting

set_option linter.unusedSectionVars false

/-- A nonzero element of `ℤᵐ⁰` is `exp n` for some integer `n`. -/
theorem exists_exp_of_ne_zero {x : ℤᵐ⁰} (hx : x ≠ 0) : ∃ n : ℤ, x = WithZero.exp n :=
  ⟨WithZero.log x, (WithZero.exp_log hx).symm⟩

/-- Two generators of a principal ideal have the same value under a dominating valuation. -/
theorem valuation_eq_of_span_eq {Z : Scheme.{uP}} [IsIntegral Z] {y : Z}
    {ξ : Valuation Z.functionField ℤᵐ⁰} (hξ : Dominates ξ y) {a b : Z.presheaf.stalk y}
    (hab : Ideal.span {a} = Ideal.span {b}) :
    ξ (algebraMap _ Z.functionField a) = ξ (algebraMap _ Z.functionField b) := by
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hab
  rw [← hv, map_mul, map_mul, valuation_algebraMap_eq_one_of_isUnit hξ v.isUnit, mul_one]

/-- If `ξ` dominates the local ring of `y`, its restriction along a dominant morphism `f`
dominates the local ring of `f y`. -/
theorem dominates_comap_of_stalkMap {Z Z' : Scheme.{uP}} [IsIntegral Z] [IsIntegral Z']
    (f : Z' ⟶ Z) [IsDominant f] {ξ : Valuation Z'.functionField ℤᵐ⁰} {y : Z'}
    (hξ : Dominates ξ y) : Dominates (ξ.comap (functionFieldMap f)) (f y) := by
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]; exact hξ.1 _
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact hξ.2 _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu))

/-- A valuation dominating the local ring of a point `y` of a prime divisor `H` takes a value less
than one on a local equation of `H` at `y`. -/
theorem valuation_lt_one_of_localEq {Z : Scheme.{uP}} [IsIntegral Z] {y : Z}
    {ξ : Valuation Z.functionField ℤᵐ⁰} (hξ : Dominates ξ y) (H : MMP.Mori.PrimeDivisor Z)
    (hyH : y ∈ (H.support : Set Z)) {u : Z.presheaf.stalk y}
    (hu : IdealSheafData.stalk H.idealSheaf y = Ideal.span {u}) :
    ξ (algebraMap _ Z.functionField u) < 1 := by
  refine hξ.2 _ ?_
  have : IdealSheafData.stalk H.idealSheaf y ≤ maximalIdeal _ :=
    (Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support H.idealSheaf y).mpr hyH
  exact this (hu ▸ Ideal.subset_span rfl)

/-- A component of an snc divisor has a local equation at each of its points. -/
theorem exists_localEq_of_isSNC {k : Type uP} [Field k] {Z : Scheme.{uP}} [IsIntegral Z]
    [IsLocallyNoetherian Z]
    {sZ : Z ⟶ Spec (.of k)} {T : Divisor Z} (hT : T.IsSNC sZ) {G : MMP.Mori.PrimeDivisor Z}
    (hG : G ∈ T.support) {y : Z} (hy : y ∈ (G.support : Set Z)) :
    ∃ x : Z.presheaf.stalk y, IdealSheafData.stalk G.idealSheaf y = Ideal.span {x} := by
  obtain ⟨n, z', j', -, -, hI'⟩ := hT.2 y
  exact ⟨_, hI' ⟨G, hG, hy⟩⟩

/-- Restricting a valuation along the function field maps of `a` and then `b` is restricting it
along that of `a ≫ b`. -/
theorem comap_comap_functionFieldMap {A B C : Scheme.{uP}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b]
    (ξ : Valuation A.functionField ℤᵐ⁰) :
    (ξ.comap (functionFieldMap a)).comap (functionFieldMap b) =
      ξ.comap (functionFieldMap (a ≫ b)) := by
  ext f
  simp only [Valuation.comap_apply]
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- If `exp (-(d * cF)) = a * vF` and `exp (-(d * cF')) = a * vF'`, where `vF` is a value less than
one when `pF` holds and `1` otherwise, likewise `vF'`, with `pF` and `pF'` not both true and
`cF ≤ cF'`, then `pF` fails, `a = exp (-(d * cF))`, `pF'` fails when `cF = cF'`, and when
`cF < cF'` the property `pF'` holds with `vF' = exp (-(d * (cF' - cF)))`. -/
theorem weights_split {pF pF' : Prop} [Decidable pF] [Decidable pF'] {a vF vF' : ℤᵐ⁰}
    {cF cF' d : ℕ} (hd : 0 < d) (hle : cF ≤ cF') (hpq : ¬ (pF ∧ pF'))
    (hvF : pF → vF < 1) (hvF' : pF' → vF' < 1)
    (h1 : WithZero.exp (-((d * cF : ℕ) : ℤ)) = a * (if pF then vF else 1))
    (h2 : WithZero.exp (-((d * cF' : ℕ) : ℤ)) = a * (if pF' then vF' else 1)) :
    ¬ pF ∧ a = WithZero.exp (-((d * cF : ℕ) : ℤ)) ∧ (cF = cF' → ¬ pF') ∧
      (cF < cF' → pF' ∧ vF' = WithZero.exp (-((d * (cF' - cF) : ℕ) : ℤ))) := by
  have hnF : ¬ pF := by
    intro hp
    have hp' : ¬ pF' := fun h => hpq ⟨hp, h⟩
    rw [if_neg hp', mul_one] at h2
    rw [if_pos hp, ← h2] at h1
    have : WithZero.exp (-((d * cF' : ℕ) : ℤ)) * vF < WithZero.exp (-((d * cF' : ℕ) : ℤ)) :=
      mul_lt_of_lt_one_right (by simp [zero_lt_iff]) (hvF hp)
    rw [← h1, WithZero.exp_lt_exp] at this
    have h3 : ((d * cF' : ℕ) : ℤ) < ((d * cF : ℕ) : ℤ) := by linarith
    have := Nat.lt_of_mul_lt_mul_left (Int.ofNat_lt.mp h3)
    omega
  rw [if_neg hnF, mul_one] at h1
  refine ⟨hnF, h1.symm, fun heq hp' => ?_, fun hlt => ?_⟩
  · rw [if_pos hp', ← h1, ← heq] at h2
    have : WithZero.exp (-((d * cF : ℕ) : ℤ)) * vF' < WithZero.exp (-((d * cF : ℕ) : ℤ)) :=
      mul_lt_of_lt_one_right (by simp [zero_lt_iff]) (hvF' hp')
    rw [← h2] at this
    exact lt_irrefl _ this
  · by_cases hp' : pF'
    · refine ⟨hp', ?_⟩
      rw [if_pos hp', ← h1] at h2
      have hv0 : vF' ≠ 0 := by
        rintro rfl; rw [mul_zero] at h2; exact WithZero.exp_ne_zero h2
      rw [← WithZero.exp_log hv0, ← WithZero.exp_add, WithZero.exp_inj] at h2
      rw [← WithZero.exp_log hv0, WithZero.exp_inj]
      have : d * cF ≤ d * cF' := Nat.mul_le_mul_left _ hle
      push_cast [Nat.mul_sub, Nat.cast_sub this] at h2 ⊢
      omega
    · rw [if_neg hp', mul_one, ← h1, WithZero.exp_inj] at h2
      have : d * cF < d * cF' := Nat.mul_lt_mul_of_pos_left hlt hd
      omega

/-- Every point of the centre of a smooth blow-up of codimension at least one lies in the image of
the blow-up. -/
theorem exists_preimage_of_mem_centre {k : Type uP} [Field k] {Y : Scheme.{uP}}
    (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] {I : Y.IdealSheafData} (h : IsSmoothBlowup sY I)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    {y : Y} (hy : y ∈ (I.support : Set Y)) : ∃ y' : blowUp I, blowUpToBase I y' = y := by
  obtain ⟨z0, hz0⟩ : y ∈ Set.range I.subschemeι := by rw [I.range_subschemeι]; exact hy
  obtain ⟨e, he⟩ := surjective_exceptionalSubschemeMap sY I h hirr hc z0
  refine ⟨(exceptionalIdeal I).subschemeι e, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.IdealSheafData.subschemeMap_subschemeι,
    Scheme.Hom.comp_apply]
  change I.subschemeι (Stacks.AlgebraicGeometry.exceptionalSubschemeMap I e) = y
  rw [he, hz0]

/-- Zariski's connectedness: every fibre of a proper birational morphism of integral schemes onto
a normal scheme is connected. -/
theorem isConnected_fibre_of_isBirational {X Z : Scheme.{uP}} [IsIntegral X] [IsIntegral Z]
    [IsNormal Z] (f : X ⟶ Z) [IsProper f] (hbir : IsBirational f) (z : Z) :
    _root_.IsConnected (f ⁻¹' {z}) := by
  have hfib : IsIso (f.fiberToSpecResidueField (genericPoint Z)) :=
    isIso_fiberToSpecResidueField_genericPoint_of_isBirational f hbir
  have hfibΓ : IsIso (f.fiberToSpecResidueField (genericPoint Z)).appTop := by
    have : IsIso (f.fiberToSpecResidueField (genericPoint Z)).c :=
      PresheafedSpace.c_isIso_of_iso (f.fiberToSpecResidueField (genericPoint Z)).toPshHom
    exact NatIso.isIso_app_of_isIso _ (Opposite.op ⊤)
  have hgen : ∀ x : X, x ∈ genericPoints X → f x = genericPoint Z := by
    intro x hx
    have hmem := hbir.1.mapsTo hx
    rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at hmem
  have : IsIso f.fromNormalization :=
    Stacks.SteinFactorization.isIso_fromNormalization_of_isNormal f hgen hfibΓ
  have := Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper f
  have hpre : f ⁻¹' {z} = f.toNormalization ⁻¹' {(inv f.fromNormalization) z} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hx : f x = f.fromNormalization (f.toNormalization x) := by
      rw [← Scheme.Hom.comp_apply, Stacks.SteinFactorization.toNormalization_fromNormalization]
    rw [hx]
    constructor
    · rintro rfl
      rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
      rfl
    · rintro hx
      rw [hx, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
  rw [hpre]
  exact f.toNormalization.isConnected_preimage_singleton _

/-- Let `π` be proper and `H` a prime divisor over a normal prime divisor `G`, with `π` mapping
the generic point of `H` to that of `G` by an isomorphism of local rings. For a preconnected
`S ⊆ G`, the intersection of `π⁻¹(S)` with `H` is preconnected, and nonempty if `S` is. -/
theorem preimage_inter_support_of_birational {Y Y' : Scheme.{uP}} (π : Y' ⟶ Y) [IsProper π]
    (H : AlgebraicGeometry.PrimeDivisor Y') (G : AlgebraicGeometry.PrimeDivisor Y)
    (hsupp : (H.idealSheaf.support : Set Y') ⊆ π ⁻¹' G.idealSheaf.support)
    (hgen : π H.genericPoint = G.genericPoint) (hiso : IsIso (π.stalkMap H.genericPoint))
    [IsNormal G.idealSheaf.subscheme] {S : Set Y} (hS : _root_.IsPreconnected S)
    (hSG : S ⊆ G.idealSheaf.support) :
    _root_.IsPreconnected (π ⁻¹' S ∩ H.idealSheaf.support) ∧
      (S.Nonempty → (π ⁻¹' S ∩ H.idealSheaf.support).Nonempty) := by
  haveI := H.integral
  haveI := G.integral
  have hle : G.idealSheaf ≤ H.idealSheaf.map π := by
    rw [Scheme.IdealSheafData.le_map_iff_comap_le]
    refine le_trans ?_ (le_of_eq
      (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme H.idealSheaf
        H.idealSheaf.support rfl).symm)
    rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro x hx
    rw [Scheme.IdealSheafData.support_comap]
    exact hsupp hx
  set h := Scheme.IdealSheafData.subschemeMap H.idealSheaf G.idealSheaf π hle with hh
  have hcomm : h ≫ G.idealSheaf.subschemeι = H.idealSheaf.subschemeι ≫ π :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  haveI : IsProper (h ≫ G.idealSheaf.subschemeι) := by rw [hcomm]; infer_instance
  haveI : IsProper h := IsProper.of_comp h G.idealSheaf.subschemeι
  have happ : ∀ x, G.idealSheaf.subschemeι (h x) = π (H.idealSheaf.subschemeι x) := fun x => by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  have hgen' : h (genericPoint H.idealSheaf.subscheme) = genericPoint G.idealSheaf.subscheme := by
    apply G.idealSheaf.subschemeι.isClosedEmbedding.injective
    rw [happ]
    exact hgen
  haveI : Surjective h := by
    refine ⟨fun z => ?_⟩
    have hcl : IsClosed (Set.range h) := h.isClosedMap.isClosed_range
    have hz : z ∈ closure {genericPoint G.idealSheaf.subscheme} := by
      rw [(genericPoint_spec G.idealSheaf.subscheme).def]; trivial
    have hm : genericPoint G.idealSheaf.subscheme ∈ Set.range h := ⟨_, hgen'⟩
    exact closure_minimal (Set.singleton_subset_iff.2 hm) hcl hz
  have hstalk : IsIso (h.stalkMap (genericPoint H.idealSheaf.subscheme)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · have hfield : IsField (G.idealSheaf.subscheme.presheaf.stalk
          (h (genericPoint H.idealSheaf.subscheme))) := by
        apply isField_stalk_of_closure_mem_irreducibleComponents
        rw [hgen', (genericPoint_spec _).def, irreducibleComponents_eq_singleton]
        exact Set.mem_singleton _
      letI := hfield.toField
      exact RingHom.injective _
    · have e := Scheme.Hom.stalkMap_congr_hom (h ≫ G.idealSheaf.subschemeι)
        (H.idealSheaf.subschemeι ≫ π) hcomm (genericPoint H.idealSheaf.subscheme)
      rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at e
      have hs : Function.Surjective ((G.idealSheaf.subschemeι.stalkMap
          (h (genericPoint H.idealSheaf.subscheme))) ≫
          h.stalkMap (genericPoint H.idealSheaf.subscheme)).hom := by
        have hiso' : IsIso (π.stalkMap
            (H.idealSheaf.subschemeι (genericPoint H.idealSheaf.subscheme))) := hiso
        rw [e]
        intro b
        obtain ⟨a2, rfl⟩ := H.idealSheaf.subschemeι.stalkMap_surjective _ b
        obtain ⟨a1, rfl⟩ := (ConcreteCategory.bijective_of_isIso (π.stalkMap
            (H.idealSheaf.subschemeι (genericPoint H.idealSheaf.subscheme)))).2 a2
        obtain ⟨a0, rfl⟩ := (ConcreteCategory.bijective_of_isIso
            (Y.presheaf.stalkCongr (.of_eq (happ _))).hom).2 a1
        exact ⟨a0, rfl⟩
      exact Function.Surjective.of_comp (g := (G.idealSheaf.subschemeι.stalkMap
        (h (genericPoint H.idealSheaf.subscheme))).hom) hs
  have hbir : IsBirational h := by
    rw [isBirational_iff, genericPoints_eq_singleton, genericPoints_eq_singleton]
    refine ⟨Set.bijOn_singleton.2 hgen', fun x hx => ?_⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hstalk
  have hfib : ∀ b, _root_.IsPreconnected (h ⁻¹' {b}) := fun b =>
    (isConnected_fibre_of_isBirational h hbir b).isPreconnected
  have hSg : _root_.IsPreconnected (G.idealSheaf.subschemeι ⁻¹' S) := by
    have himg : G.idealSheaf.subschemeι '' (G.idealSheaf.subschemeι ⁻¹' S) = S :=
      Set.image_preimage_eq_of_subset (by rw [G.idealSheaf.range_subschemeι]; exact hSG)
    rw [← himg] at hS
    exact (G.idealSheaf.subschemeι.isClosedEmbedding.isInducing.isPreconnected_image).mp hS
  have hP := isPreconnected_preimage_of_isClosedMap h.isClosedMap hfib hSg
    (fun z _ => h.surjective z)
  have heq : H.idealSheaf.subschemeι '' (h ⁻¹' (G.idealSheaf.subschemeι ⁻¹' S)) =
      π ⁻¹' S ∩ H.idealSheaf.support := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, ?_⟩
      · change π (H.idealSheaf.subschemeι w) ∈ S
        rw [← happ]; exact hw
      · rw [← H.idealSheaf.range_subschemeι]; exact ⟨w, rfl⟩
    · rintro ⟨hy, hyH⟩
      rw [← H.idealSheaf.range_subschemeι] at hyH
      obtain ⟨w, rfl⟩ := hyH
      refine ⟨w, ?_, rfl⟩
      change G.idealSheaf.subschemeι (h w) ∈ S
      rw [happ]; exact hy
  refine ⟨heq ▸ hP.image _ H.idealSheaf.subschemeι.continuous.continuousOn, ?_⟩
  rintro ⟨s, hs⟩
  have hs' : s ∈ Set.range G.idealSheaf.subschemeι := by
    rw [G.idealSheaf.range_subschemeι]; exact hSG hs
  obtain ⟨z, rfl⟩ := hs'
  obtain ⟨w, rfl⟩ := h.surjective z
  rw [← heq]
  exact ⟨_, w, hs, rfl⟩

section StepCore

variable {k : Type uP} [Field k] [CharZero k] {X : Scheme.{uP}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX] {Δ : Divisor X}
  {n : ℕ} (M : SModel sX Δ n) {F F' : MMP.Mori.PrimeDivisor M.Y}
  (hF : F ∈ M.T.support) (hF' : F' ∈ M.T.support) (hFF : F ≠ F') {I : M.Y.IdealSheafData}
  (hirr : IsIrreducible (I.support : Set M.Y)) (hIsm : IsSmoothScheme (I.subschemeι ≫ M.g ≫ sX))
  (hIsub : (I.support : Set M.Y) ⊆ (F.support : Set M.Y) ∩ F'.support)
  (hIst : ∀ y ∈ I.support, IdealSheafData.stalk I y =
    IdealSheafData.stalk F.idealSheaf y ⊔ IdealSheafData.stalk F'.idealSheaf y)
  {η : X} {ι : Type*} [Fintype ι] {z : ι → X.presheaf.stalk η} {α : ι → ℕ}

attribute [local instance] SModel.isIntegral SModel.isDominant SModel.isLocallyNoetherian
  SModel.isNormal

/-- Prime divisors with the same strict transform are equal. -/
theorem strictPrime_injective {Y : Scheme.{uP}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {I : Y.IdealSheafData}
    {G G' : MMP.Mori.PrimeDivisor Y} (hG : G.genericPoint ∉ (I.support : Set Y))
    (hG' : G'.genericPoint ∉ (I.support : Set Y)) (h : strictPrime I G hG = strictPrime I G' hG') :
    G = G' := by
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  have h1 := map_genericPoint_strictPrime I hG
  have h2 := map_genericPoint_strictPrime I hG'
  rw [h] at h1
  exact h1.symm.trans h2

open Classical in
/-- Let `F, F' ∈ t.P` and let the centre `I` contain `t.S`. Every centre `p'` on the blow-up of a
valuation `ξ'` lying over a valuation of weight `d • α` maps into `t.S` and lies on the
exceptional divisor; it lies on the strict transform of a boundary component `G ≠ F, F'` exactly
when `G ∈ t.P`; and the new boundary components through `p'` have local equations `u` at `p'`
such that `ξ'` takes the value `exp (-(d * t.c G))` on that of the strict transform of each such
`G ∈ t.P`, while `exp (-(d * t.c F))` is its value on that of the exceptional divisor times its
value on that of the strict transform of `F` when `p'` lies on it, and likewise for `F'`. -/
theorem step_core (t : M.Track η z α) (hFP : F ∈ t.P) (hF'P : F' ∈ t.P)
    (hSI : t.S ⊆ I.support) {ξ : Valuation X.functionField ℤᵐ⁰} {d : ℕ}
    (hξ : IsWeightVal η z α ξ d) :
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr
      (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst)
    haveI := isDominant_blowUpToBase I hirr (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst)
    ∀ ξ' : Valuation (blowUp I).functionField ℤᵐ⁰,
    ξ'.comap (functionFieldMap (blowUpToBase I ≫ M.g)) = ξ →
    ∀ p' : blowUp I, SNCModel.Dominates ξ' p' →
    blowUpToBase I p' ∈ t.S ∧
    p' ∈ ((excE (M.g ≫ sX) (centre_isSmoothBlowup M hIsm) hirr
      (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst)).support : Set (blowUp I)) ∧
    (∀ G ∈ M.T.support, ¬ (G = F ∨ G = F') →
      (p' ∈ ((strictPrime I G (genericPoint_notMem_of_subset_inter I hFF hIsub G)).support :
        Set (blowUp I)) ↔ G ∈ t.P)) ∧
    ∃ u : MMP.Mori.PrimeDivisor (blowUp I) → (blowUp I).presheaf.stalk p',
      (∀ H ∈ newPrimes (M.g ≫ sX) hFF hIsub (centre_isSmoothBlowup M hIsm) hirr
          (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst) M.T,
        p' ∈ (H.support : Set (blowUp I)) →
          IdealSheafData.stalk H.idealSheaf p' = Ideal.span {u H}) ∧
      (∀ G ∈ t.P, ¬ (G = F ∨ G = F') →
        ξ' (algebraMap _ _
          (u (strictPrime I G (genericPoint_notMem_of_subset_inter I hFF hIsub G))))
          = WithZero.exp (-((d * t.c G : ℕ) : ℤ))) ∧
      WithZero.exp (-((d * t.c F : ℕ) : ℤ)) =
        ξ' (algebraMap _ _ (u (excE (M.g ≫ sX) (centre_isSmoothBlowup M hIsm) hirr
          (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst)))) *
        (if p' ∈ ((strictPrime I F (genericPoint_notMem_of_subset_inter I hFF hIsub F)).support :
            Set (blowUp I))
          then ξ' (algebraMap _ _ (u (strictPrime I F
            (genericPoint_notMem_of_subset_inter I hFF hIsub F)))) else 1) ∧
      WithZero.exp (-((d * t.c F' : ℕ) : ℤ)) =
        ξ' (algebraMap _ _ (u (excE (M.g ≫ sX) (centre_isSmoothBlowup M hIsm) hirr
          (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst)))) *
        (if p' ∈ ((strictPrime I F' (genericPoint_notMem_of_subset_inter I hFF hIsub F')).support :
            Set (blowUp I))
          then ξ' (algebraMap _ _ (u (strictPrime I F'
            (genericPoint_notMem_of_subset_inter I hFF hIsub F')))) else 1) ∧
      ξ' (algebraMap _ _ (u (excE (M.g ≫ sX) (centre_isSmoothBlowup M hIsm) hirr
          (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst)))) < 1 ∧
      (p' ∈ ((strictPrime I F (genericPoint_notMem_of_subset_inter I hFF hIsub F)).support :
          Set (blowUp I)) →
        ξ' (algebraMap _ _ (u (strictPrime I F
          (genericPoint_notMem_of_subset_inter I hFF hIsub F)))) < 1) ∧
      (p' ∈ ((strictPrime I F' (genericPoint_notMem_of_subset_inter I hFF hIsub F')).support :
          Set (blowUp I)) →
        ξ' (algebraMap _ _ (u (strictPrime I F'
          (genericPoint_notMem_of_subset_inter I hFF hIsub F')))) < 1) ∧
      ¬ (p' ∈ ((strictPrime I F (genericPoint_notMem_of_subset_inter I hFF hIsub F)).support :
          Set (blowUp I)) ∧
        p' ∈ ((strictPrime I F' (genericPoint_notMem_of_subset_inter I hFF hIsub F')).support :
          Set (blowUp I))) := by
  have hc := codim_one_le M hF hF' hFF hirr hIsm hIsub hIst
  have h := centre_isSmoothBlowup M hIsm
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI := isDominant_blowUpToBase I hirr hc
  haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup (M.g ≫ sX) I h).1
  haveI : IsLocallyNoetherian (blowUp I) :=
    isLocallyNoetherian_of_smooth (blowUpToBase I ≫ M.g ≫ sX)
  haveI := M.isVariety
  haveI : Smooth (M.g ≫ sX) := smooth_of_isSmoothScheme M.isSmooth
  intro ξ' hcm p' hp'
  have hcmY : (ξ'.comap (functionFieldMap (blowUpToBase I))).comap (functionFieldMap M.g) = ξ := by
    rw [comap_comap_functionFieldMap]; exact hcm
  have hdomY : Dominates (ξ'.comap (functionFieldMap (blowUpToBase I))) (blowUpToBase I p') :=
    dominates_comap_of_stalkMap _ hp'
  obtain ⟨hS, hiff, hval⟩ := t.cent ξ d hξ _ hcmY _ hdomY
  have hyI : blowUpToBase I p' ∈ (I.support : Set M.Y) := hSI hS
  have hE : p' ∈ ((excE (M.g ≫ sX) h hirr hc).support : Set (blowUp I)) := by
    rw [coe_support_excE]; exact hyI
  have hvalφ : ∀ G ∈ t.P, ∀ x, IdealSheafData.stalk G.idealSheaf (blowUpToBase I p') =
      Ideal.span {x} → ξ' (algebraMap _ (blowUp I).functionField
        (((blowUpToBase I).stalkMap p').hom x)) = WithZero.exp (-((d * t.c G : ℕ) : ℤ)) := by
    intro G hG x hx
    have := hval G hG x hx
    rwa [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk] at this
  obtain ⟨u, hu, -⟩ := exists_localEqs_newPrimes (M.g ≫ sX) h hirr hc M.isSmooth M.snc hF hF'
    hFF hIsub hIst p'
  have hloc := fun {G} hG hyG {x} hx => valuation_localEq_blowUp (M.g ≫ sX) h hirr hc M.snc hF
    hF' hFF hIsm hIsub hIst p' hyI u hu (G := G) hG hyG (x := x) hx ξ' hp'
  have hlt : ∀ H ∈ newPrimes (M.g ≫ sX) hFF hIsub h hirr hc M.T,
      p' ∈ (H.support : Set (blowUp I)) → ξ' (algebraMap _ _ (u H)) < 1 :=
    fun H hH hpH => valuation_lt_one_of_localEq hp' H hpH (hu H hH hpH)
  have hEnew : excE (M.g ≫ sX) h hirr hc ∈ newPrimes (M.g ≫ sX) hFF hIsub h hirr hc M.T :=
    (mem_newPrimes (M.g ≫ sX) hFF hIsub h hirr hc).2 (Or.inl rfl)
  have hsnew : ∀ G ∈ M.T.support,
      strictPrime I G (genericPoint_notMem_of_subset_inter I hFF hIsub G)
      ∈ newPrimes (M.g ≫ sX) hFF hIsub h hirr hc M.T :=
    fun G hG => (mem_newPrimes (M.g ≫ sX) hFF hIsub h hirr hc).2 (Or.inr ⟨G, hG, rfl⟩)
  have hmemP : ∀ G ∈ t.P, blowUpToBase I p' ∈ (G.support : Set M.Y) :=
    fun G hG => (hiff G (t.P_sub hG)).2 hG
  refine ⟨hS, hE, fun G hG hGF => ⟨fun hpG => ?_, fun hGP => ?_⟩, u, hu, ?_, ?_, ?_, hlt _ hEnew hE,
    hlt _ (hsnew F hF), hlt _ (hsnew F' hF'),
    not_and_mem_support_strictPrime (M.g ≫ sX) h hirr hc M.isSmooth M.snc hF hF' hFF hIsm hIsub hIst
      p' hyI⟩
  · exact (hiff G hG).1 (support_strictPrime_subset I _ hpG)
  · exact mem_strictPrime_of_mem (M.g ≫ sX) h hirr hc M.isSmooth M.snc hF hF' hFF hIsm hIsub hIst
      p' hyI (t.P_sub hGP) hGF (hmemP G hGP)
  · intro G hG hGF
    obtain ⟨x, hx⟩ := exists_localEq_of_isSNC M.snc (t.P_sub hG) (hmemP G hG)
    have e1 := hloc (t.P_sub hG) (hmemP G hG) hx
    rw [if_neg hGF, one_mul, if_pos (mem_strictPrime_of_mem (M.g ≫ sX) h hirr hc M.isSmooth M.snc
      hF hF' hFF hIsm hIsub hIst p' hyI (t.P_sub hG) hGF (hmemP G hG))] at e1
    rw [← e1]; exact hvalφ G hG x hx
  · obtain ⟨x, hx⟩ := exists_localEq_of_isSNC M.snc hF (hmemP F hFP)
    have e1 := hloc hF (hmemP F hFP) hx
    rw [if_pos (Or.inl rfl)] at e1
    rw [← hvalφ F hFP x hx, e1]
  · obtain ⟨x, hx⟩ := exists_localEq_of_isSNC M.snc hF' (hmemP F' hF'P)
    have e1 := hloc hF' (hmemP F' hF'P) hx
    rw [if_pos (Or.inr rfl)] at e1
    rw [← hvalφ F' hF'P x hx, e1]

/-- The strict transform map, into the new model. -/
abbrev sP (G : MMP.Mori.PrimeDivisor M.Y) :
    MMP.Mori.PrimeDivisor (blowUpModel M hF hF' hFF hirr hIsm hIsub hIst).Y :=
  strictPrime I G (genericPoint_notMem_of_subset_inter I hFF hIsub G)

/-- The exceptional divisor, in the new model. -/
abbrev eY : MMP.Mori.PrimeDivisor (blowUpModel M hF hF' hFF hirr hIsm hIsub hIst).Y :=
  excE (M.g ≫ sX) (centre_isSmoothBlowup M hIsm) hirr
    (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst)

local notation "sPM" => sP M hF hF' hFF hirr hIsm hIsub hIst
local notation "eYM" => eY M hF hF' hFF hirr hIsm hIsub hIst

/-- The strict transform map `sP` is injective. -/
theorem sP_injective : Function.Injective sPM := fun G G' hGG =>
  strictPrime_injective _ _ hGG

/-- No strict transform is the exceptional divisor `eY`. -/
theorem sP_ne_eY (G : MMP.Mori.PrimeDivisor M.Y) : sPM G ≠ eYM :=
  strictPrime_ne_excE _ _ _ _ _

/-- The new weights. -/
def newWeight (t : M.Track η z α)
    (H : MMP.Mori.PrimeDivisor (blowUpModel M hF hF' hFF hirr hIsm hIsub hIst).Y) : ℕ :=
  open Classical in
  if H = eYM then t.c F
  else if H = sPM F' then t.c F' - t.c F
  else if hH : ∃ G, sPM G = H then t.c hH.choose else 0

/-- The new weight of the exceptional divisor is the weight of `F`. -/
theorem newWeight_excE (t : M.Track η z α) :
    newWeight M hF hF' hFF hirr hIsm hIsub hIst t eYM = t.c F := by
  rw [newWeight, if_pos rfl]

/-- The new weight of the strict transform of `F'` is the weight of `F'` minus that of `F`. -/
theorem newWeight_sP_F' (t : M.Track η z α) :
    newWeight M hF hF' hFF hirr hIsm hIsub hIst t (sPM F') = t.c F' - t.c F := by
  rw [newWeight, if_neg (sP_ne_eY M hF hF' hFF hirr hIsm hIsub hIst F'), if_pos rfl]

/-- The new weight of the strict transform of a prime divisor `G ≠ F'` is the weight of `G`. -/
theorem newWeight_sP (t : M.Track η z α) {G : MMP.Mori.PrimeDivisor M.Y} (hG : G ≠ F') :
    newWeight M hF hF' hFF hirr hIsm hIsub hIst t (sPM G) = t.c G := by
  have hex : ∃ G', sPM G' = sPM G := ⟨G, rfl⟩
  rw [newWeight, if_neg (sP_ne_eY M hF hF' hFF hirr hIsm hIsub hIst G),
    if_neg (fun h => hG (sP_injective M hF hF' hFF hirr hIsm hIsub hIst h)), dif_pos hex,
    sP_injective M hF hF' hFF hirr hIsm hIsub hIst hex.choose_spec]

/-- The boundary components of the blown-up model are the exceptional divisor and the strict
transforms of the boundary components of `M`. -/
theorem mem_newT {H : MMP.Mori.PrimeDivisor (blowUpModel M hF hF' hFF hirr hIsm hIsub hIst).Y} :
    H ∈ (blowUpModel M hF hF' hFF hirr hIsm hIsub hIst).T.support ↔
      H = eYM ∨ ∃ G ∈ M.T.support, sPM G = H := by
  change H ∈ (MMP.Intersection.reducedDivisorOf _).support ↔ _
  rw [MMP.Intersection.support_reducedDivisorOf]
  exact mem_newPrimes _ _ _ _ _ _

/-- The morphism of the blown-up model to `X` sends `y'` to the image under `M.g` of its image in
`M.Y`. -/
theorem blowUpModel_g_apply (y' : (blowUpModel M hF hF' hFF hirr hIsm hIsub hIst).Y) :
    (blowUpModel M hF hF' hFF hirr hIsm hIsub hIst).g y' = M.g (blowUpToBase I y') := by
  change (blowUpToBase I ≫ M.g) y' = _
  rw [Scheme.Hom.comp_apply]

include hF hF' hFF hirr hIsm hIsub hIst in
/-- If the centre contains `t.S`, the preimage of `t.S` in the blow-up is nonempty. -/
theorem exists_preimage_S (t : M.Track η z α) (hSI : t.S ⊆ I.support) :
    (blowUpToBase I ⁻¹' t.S).Nonempty := by
  obtain ⟨s0, hs0⟩ := t.S_ne
  obtain ⟨y', hy'⟩ := exists_preimage_of_mem_centre (M.g ≫ sX) (centre_isSmoothBlowup M hIsm)
    hirr (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst) (hSI hs0)
  exact ⟨y', by rw [Set.mem_preimage, hy']; exact hs0⟩

/-- If the centre contains `t.S`, the image in `X` of the generic point of the exceptional divisor
specializes to `η`. -/
theorem specializes_eta (t : M.Track η z α) (hSI : t.S ⊆ I.support) :
    M.g (blowUpToBase I (excE (M.g ≫ sX) (centre_isSmoothBlowup M hIsm) hirr
      (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst)).genericPoint) ⤳ η := by
  obtain ⟨s0, hs0⟩ := t.S_ne
  have := (map_genericPoint_excE_specializes (M.g ≫ sX) (centre_isSmoothBlowup M hIsm) hirr
    (codim_one_le M hF hF' hFF hirr hIsm hIsub hIst) (hSI hs0)).map M.g.continuous
  rwa [t.S_over s0 hs0] at this

open Classical in
/-- The new rays: the sum over the strict transforms of the untouched components. -/
theorem sum_rest_eq (t : M.Track η z α)
    (f : MMP.Mori.PrimeDivisor (blowUpModel M hF hF' hFF hirr hIsm hIsub hIst).Y → ℤ)
    (g : MMP.Mori.PrimeDivisor M.Y → ℤ) (hfg : ∀ G ∈ (t.P.erase F).erase F', f (sPM G) = g G) :
    ∑ H ∈ ((t.P.erase F).erase F').image sPM, f H = ∑ G ∈ (t.P.erase F).erase F', g G := by
  rw [Finset.sum_image (fun x _ y _ hxy => sP_injective M hF hF' hFF hirr hIsm hIsub hIst hxy)]
  exact Finset.sum_congr rfl hfg

open Classical in
/-- If `F, F' ∈ t.P` have equal weights and the centre contains `t.S`, the blown-up model carries
tracking data of smaller total weight, whose components are among the exceptional divisor and
the strict transforms of `F'` and of the components of `t.P` other than `F, F'`. -/
theorem step_eq (t : M.Track η z α) (hFP : F ∈ t.P) (hF'P : F' ∈ t.P) (hSI : t.S ⊆ I.support)
    (hceq : t.c F = t.c F')
    (hz : ∀ j, ∃ P ∈ Δ.support, IdealSheafData.stalk P.idealSheaf η = Ideal.span {z j}) :
    ∃ t' : (blowUpModel M hF hF' hFF hirr hIsm hIsub hIst).Track η z α,
      ∑ H ∈ t'.P, t'.c H < ∑ G ∈ t.P, t.c G ∧
        t'.P ⊆ insert eYM (insert (sPM F') (((t.P.erase F).erase F').image sPM)) := by
  have hc := codim_one_le M hF hF' hFF hirr hIsm hIsub hIst
  have h := centre_isSmoothBlowup M hIsm
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI := isDominant_blowUpToBase I hirr hc
  haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup (M.g ≫ sX) I h).1
  haveI : IsLocallyNoetherian (blowUp I) :=
    isLocallyNoetherian_of_smooth (blowUpToBase I ≫ M.g ≫ sX)
  haveI := M.isVariety
  have hF'1 : F' ∈ t.P.erase F := Finset.mem_erase.2 ⟨Ne.symm hFF, hF'P⟩
  have hEne : ∀ G, sPM G ≠ eYM := sP_ne_eY M hF hF' hFF hirr hIsm hIsub hIst
  have hEP0 : eYM ∉ ((t.P.erase F).erase F').image sPM := by
    intro hm; obtain ⟨G, -, hG⟩ := Finset.mem_image.1 hm; exact hEne G hG
  have hrest : ∀ G ∈ (t.P.erase F).erase F', G ∈ t.P ∧ G ≠ F ∧ G ≠ F' := by
    intro G hG
    obtain ⟨h1, h2⟩ := Finset.mem_erase.1 hG
    obtain ⟨h3, h4⟩ := Finset.mem_erase.1 h2
    exact ⟨h4, h3, h1⟩
  have hmemP0 : ∀ G, sPM G ∈ ((t.P.erase F).erase F').image sPM ↔
      G ∈ (t.P.erase F).erase F' := fun _ =>
    (sP_injective M hF hF' hFF hirr hIsm hIsub hIst).mem_finset_image
  have hEnew : excE (M.g ≫ sX) h hirr hc ∈ newPrimes (M.g ≫ sX) hFF hIsub h hirr hc M.T :=
    (mem_newPrimes (M.g ≫ sX) hFF hIsub h hirr hc).2 (Or.inl rfl)
  have hsnew : ∀ G ∈ M.T.support,
      strictPrime I G (genericPoint_notMem_of_subset_inter I hFF hIsub G)
      ∈ newPrimes (M.g ≫ sX) hFF hIsub h hirr hc M.T :=
    fun G hG => (mem_newPrimes (M.g ≫ sX) hFF hIsub h hirr hc).2 (Or.inr ⟨G, hG, rfl⟩)
  refine ⟨{
    P := insert eYM (((t.P.erase F).erase F').image sPM)
    c := newWeight M hF hF' hFF hirr hIsm hIsub hIst t
    S := blowUpToBase I ⁻¹' t.S
    P_sub := ?_
    c_pos := ?_
    S_pre := isPreconnected_preimage_of_subset_centre (M.g ≫ sX) h hirr hc t.S_pre hSI
    S_ne := exists_preimage_S M hF hF' hFF hirr hIsm hIsub hIst t hSI
    S_sub := ?_
    S_over := fun y' hy' => by
      rw [blowUpModel_g_apply]; exact t.S_over _ hy'
    ray := ?_
    cent := ?_ }, ?_, Finset.insert_subset_insert _ (Finset.subset_insert _ _)⟩
  · intro H hH
    rw [mem_newT]
    rcases Finset.mem_insert.1 hH with rfl | hH
    · exact Or.inl rfl
    · obtain ⟨G, hG, rfl⟩ := Finset.mem_image.1 hH
      exact Or.inr ⟨G, t.P_sub (hrest G hG).1, rfl⟩
  · intro H hH
    rcases Finset.mem_insert.1 hH with rfl | hH
    · rw [newWeight_excE]; exact t.c_pos F hFP
    · obtain ⟨G, hG, rfl⟩ := Finset.mem_image.1 hH
      rw [newWeight_sP M hF hF' hFF hirr hIsm hIsub hIst t (hrest G hG).2.2]
      exact t.c_pos G (hrest G hG).1
  · intro H hH y' hy'
    rcases Finset.mem_insert.1 hH with rfl | hH
    · change y' ∈ ((excE (M.g ≫ sX) h hirr hc).support : Set (blowUp I))
      rw [coe_support_excE]; exact hSI hy'
    · obtain ⟨G, hG, rfl⟩ := Finset.mem_image.1 hH
      obtain ⟨hGP, hGF, hGF'⟩ := hrest G hG
      exact mem_strictPrime_of_mem (M.g ≫ sX) h hirr hc M.isSmooth M.snc hF hF' hFF hIsm hIsub
        hIst y' (hSI hy') (t.P_sub hGP) (not_or.2 ⟨hGF, hGF'⟩) (t.S_sub G hGP hy')
  · intro j
    obtain ⟨P, hP, hzP⟩ := hz j
    rw [Finset.sum_insert hEP0, newWeight_excE, blowUpModel_ordZ_excE M hF hF' hFF hirr hIsm hIsub
      hIst (z j) hP hzP (specializes_eta M hF hF' hFF hirr hIsm hIsub hIst t hSI),
      sum_rest_eq M hF hF' hFF hirr hIsm hIsub hIst t _ (fun G => (t.c G : ℤ) * M.ordZ (z j) G)
        (fun G hG => by
        rw [newWeight_sP M hF hF' hFF hirr hIsm hIsub hIst t (hrest G hG).2.2,
          blowUpModel_ordZ_strict]),
      t.ray j, ← Finset.add_sum_erase _ _ hFP, ← Finset.add_sum_erase _ _ hF'1, hceq]
    ring
  · intro ξ d hξ ξY hcm p' hp'
    obtain ⟨hS, hE, hiffG, u, hu, hvG, h1, h2, hltE, hltF, hltF', hnb⟩ :=
      step_core M hF hF' hFF hirr hIsm hIsub hIst t hFP hF'P hSI hξ ξY hcm p' hp'
    obtain ⟨hnF, haE, heqc, -⟩ := weights_split hξ.1 hceq.le hnb hltF hltF' h1 h2
    have hnF' := heqc hceq
    refine ⟨hS, fun H hH => ?_, fun H hH v hv => ?_⟩
    · rcases (mem_newT M hF hF' hFF hirr hIsm hIsub hIst).1 hH with rfl | ⟨G, hG, rfl⟩
      · exact ⟨fun _ => Finset.mem_insert_self _ _, fun _ => hE⟩
      · by_cases hGF : G = F ∨ G = F'
        · constructor
          · intro hp; exfalso
            rcases hGF with rfl | rfl
            · exact hnF hp
            · exact hnF' hp
          · intro hm; exfalso
            rcases Finset.mem_insert.1 hm with he | hm
            · exact hEne G he
            · have := hrest G ((hmemP0 G).1 hm)
              rcases hGF with rfl | rfl
              · exact this.2.1 rfl
              · exact this.2.2 rfl
        · rw [hiffG G hG hGF]
          constructor
          · intro hGP
            exact Finset.mem_insert_of_mem ((hmemP0 G).2 (Finset.mem_erase.2
              ⟨fun e => hGF (Or.inr e), Finset.mem_erase.2 ⟨fun e => hGF (Or.inl e), hGP⟩⟩))
          · intro hm
            rcases Finset.mem_insert.1 hm with he | hm
            · exact absurd he (hEne G)
            · exact (hrest G ((hmemP0 G).1 hm)).1
    · rcases Finset.mem_insert.1 hH with rfl | hH
      · rw [newWeight_excE, ← haE]
        exact valuation_eq_of_span_eq hp' (hv.symm.trans (hu _ hEnew hE))
      · obtain ⟨G, hG, rfl⟩ := Finset.mem_image.1 hH
        obtain ⟨hGP, hGF, hGF'⟩ := hrest G hG
        have hpG := (hiffG G (t.P_sub hGP) (not_or.2 ⟨hGF, hGF'⟩)).2 hGP
        rw [newWeight_sP M hF hF' hFF hirr hIsm hIsub hIst t hGF',
          ← hvG G hGP (not_or.2 ⟨hGF, hGF'⟩)]
        exact valuation_eq_of_span_eq hp' (hv.symm.trans (hu _ (hsnew G (t.P_sub hGP)) hpG))
  · show ∑ H ∈ insert _ _, newWeight M hF hF' hFF hirr hIsm hIsub hIst t H < _
    rw [Finset.sum_insert hEP0, newWeight_excE,
      Finset.sum_image (fun x _ y _ hxy => sP_injective M hF hF' hFF hirr hIsm hIsub hIst hxy),
      ← Finset.add_sum_erase _ _ hFP, ← Finset.add_sum_erase _ _ hF'1,
      Finset.sum_congr rfl (fun G hG => newWeight_sP M hF hF' hFF hirr hIsm hIsub hIst t
        (hrest G hG).2.2)]
    have := t.c_pos F' hF'P
    omega

include hF hF' hFF hirr hIsm hIsub hIst in
/-- For a nonempty preconnected `S` in the centre, the intersection of its preimage with the
strict transform of `F'` is nonempty and preconnected. -/
theorem inter_strict_F' {S : Set M.Y} (hS : _root_.IsPreconnected S) (hSne : S.Nonempty)
    (hSI : S ⊆ I.support) :
    _root_.IsPreconnected (blowUpToBase I ⁻¹' S ∩ ((sPM F').support : Set (blowUp I))) ∧
      (blowUpToBase I ⁻¹' S ∩ ((sPM F').support : Set (blowUp I))).Nonempty := by
  have hc := codim_one_le M hF hF' hFF hirr hIsm hIsub hIst
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI : IsProper (blowUpToBase I) :=
    TwoStepTower.isProper_blowUpToBase (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
  have hG := genericPoint_notMem_of_subset_inter I hFF hIsub F'
  haveI : IsIso ((blowUpToBase I).stalkMap (sPM F').genericPoint) :=
    isIso_stalkMap_of_mem_biregularLocus _ (mem_biregularLocus_of_notMem I (by
      rw [map_genericPoint_strictPrime I hG]; exact hG))
  haveI : IsNormal F'.idealSheaf.subscheme := by
    haveI : Smooth (F'.idealSheaf.subschemeι ≫ M.g ≫ sX) :=
      smooth_of_isSmoothScheme (M.snc.1 F' hF')
    haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
    exact AlgebraicGeometry.isNormal_of_smooth (F'.idealSheaf.subschemeι ≫ M.g ≫ sX)
  obtain ⟨h1, h2⟩ := preimage_inter_support_of_birational (blowUpToBase I) (sPM F') F'
    (support_strictPrime_subset I hG) (map_genericPoint_strictPrime I hG) inferInstance hS
    (fun y hy => (hIsub (hSI hy)).2)
  exact ⟨h1, h2 hSne⟩

open Classical in
/-- If `F, F' ∈ t.P` with the weight of `F` less than that of `F'` and the centre contains `t.S`,
the blown-up model carries tracking data of smaller total weight, whose components are among the
exceptional divisor and the strict transforms of `F'` and of the components of `t.P` other than
`F, F'`. -/
theorem step_lt (t : M.Track η z α) (hFP : F ∈ t.P) (hF'P : F' ∈ t.P) (hSI : t.S ⊆ I.support)
    (hclt : t.c F < t.c F')
    (hz : ∀ j, ∃ P ∈ Δ.support, IdealSheafData.stalk P.idealSheaf η = Ideal.span {z j}) :
    ∃ t' : (blowUpModel M hF hF' hFF hirr hIsm hIsub hIst).Track η z α,
      ∑ H ∈ t'.P, t'.c H < ∑ G ∈ t.P, t.c G ∧
        t'.P ⊆ insert eYM (insert (sPM F') (((t.P.erase F).erase F').image sPM)) := by
  have hc := codim_one_le M hF hF' hFF hirr hIsm hIsub hIst
  have h := centre_isSmoothBlowup M hIsm
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI := isDominant_blowUpToBase I hirr hc
  haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup (M.g ≫ sX) I h).1
  haveI : IsLocallyNoetherian (blowUp I) :=
    isLocallyNoetherian_of_smooth (blowUpToBase I ≫ M.g ≫ sX)
  haveI := M.isVariety
  have hF'1 : F' ∈ t.P.erase F := Finset.mem_erase.2 ⟨Ne.symm hFF, hF'P⟩
  have hEne : ∀ G, sPM G ≠ eYM := sP_ne_eY M hF hF' hFF hirr hIsm hIsub hIst
  have hinj := sP_injective M hF hF' hFF hirr hIsm hIsub hIst
  have hrest : ∀ G ∈ (t.P.erase F).erase F', G ∈ t.P ∧ G ≠ F ∧ G ≠ F' := by
    intro G hG
    obtain ⟨h1, h2⟩ := Finset.mem_erase.1 hG
    obtain ⟨h3, h4⟩ := Finset.mem_erase.1 h2
    exact ⟨h4, h3, h1⟩
  have hmemP0 : ∀ G, sPM G ∈ ((t.P.erase F).erase F').image sPM ↔
      G ∈ (t.P.erase F).erase F' := fun _ => hinj.mem_finset_image
  have hF'P0 : sPM F' ∉ ((t.P.erase F).erase F').image sPM := fun hm =>
    (hrest F' ((hmemP0 F').1 hm)).2.2 rfl
  have hEP0 : eYM ∉ insert (sPM F') (((t.P.erase F).erase F').image sPM) := by
    intro hm
    rcases Finset.mem_insert.1 hm with he | hm
    · exact hEne F' he.symm
    · obtain ⟨G, -, hG⟩ := Finset.mem_image.1 hm; exact hEne G hG
  have hEnew : excE (M.g ≫ sX) h hirr hc ∈ newPrimes (M.g ≫ sX) hFF hIsub h hirr hc M.T :=
    (mem_newPrimes (M.g ≫ sX) hFF hIsub h hirr hc).2 (Or.inl rfl)
  have hsnew : ∀ G ∈ M.T.support,
      strictPrime I G (genericPoint_notMem_of_subset_inter I hFF hIsub G)
      ∈ newPrimes (M.g ≫ sX) hFF hIsub h hirr hc M.T :=
    fun G hG => (mem_newPrimes (M.g ≫ sX) hFF hIsub h hirr hc).2 (Or.inr ⟨G, hG, rfl⟩)
  obtain ⟨hSpre, hSne⟩ := inter_strict_F' M hF hF' hFF hirr hIsm hIsub hIst t.S_pre t.S_ne hSI
  refine ⟨{
    P := insert eYM (insert (sPM F') (((t.P.erase F).erase F').image sPM))
    c := newWeight M hF hF' hFF hirr hIsm hIsub hIst t
    S := blowUpToBase I ⁻¹' t.S ∩ ((sPM F').support : Set (blowUp I))
    P_sub := ?_
    c_pos := ?_
    S_pre := hSpre
    S_ne := hSne
    S_sub := ?_
    S_over := fun y' hy' => by
      rw [blowUpModel_g_apply]; exact t.S_over _ hy'.1
    ray := ?_
    cent := ?_ }, ?_, subset_rfl⟩
  · intro H hH
    rw [mem_newT]
    rcases Finset.mem_insert.1 hH with rfl | hH
    · exact Or.inl rfl
    rcases Finset.mem_insert.1 hH with rfl | hH
    · exact Or.inr ⟨F', hF', rfl⟩
    · obtain ⟨G, hG, rfl⟩ := Finset.mem_image.1 hH
      exact Or.inr ⟨G, t.P_sub (hrest G hG).1, rfl⟩
  · intro H hH
    rcases Finset.mem_insert.1 hH with rfl | hH
    · rw [newWeight_excE]; exact t.c_pos F hFP
    rcases Finset.mem_insert.1 hH with rfl | hH
    · rw [newWeight_sP_F']; omega
    · obtain ⟨G, hG, rfl⟩ := Finset.mem_image.1 hH
      rw [newWeight_sP M hF hF' hFF hirr hIsm hIsub hIst t (hrest G hG).2.2]
      exact t.c_pos G (hrest G hG).1
  · intro H hH y' hy'
    rcases Finset.mem_insert.1 hH with rfl | hH
    · change y' ∈ ((excE (M.g ≫ sX) h hirr hc).support : Set (blowUp I))
      rw [coe_support_excE]; exact hSI hy'.1
    rcases Finset.mem_insert.1 hH with rfl | hH
    · exact hy'.2
    · obtain ⟨G, hG, rfl⟩ := Finset.mem_image.1 hH
      obtain ⟨hGP, hGF, hGF'⟩ := hrest G hG
      exact mem_strictPrime_of_mem (M.g ≫ sX) h hirr hc M.isSmooth M.snc hF hF' hFF hIsm hIsub
        hIst y' (hSI hy'.1) (t.P_sub hGP) (not_or.2 ⟨hGF, hGF'⟩) (t.S_sub G hGP hy'.1)
  · intro j
    obtain ⟨P, hP, hzP⟩ := hz j
    rw [Finset.sum_insert hEP0, Finset.sum_insert hF'P0, newWeight_excE, newWeight_sP_F',
      blowUpModel_ordZ_excE M hF hF' hFF hirr hIsm hIsub
      hIst (z j) hP hzP (specializes_eta M hF hF' hFF hirr hIsm hIsub hIst t hSI),
      blowUpModel_ordZ_strict,
      sum_rest_eq M hF hF' hFF hirr hIsm hIsub hIst t _ (fun G => (t.c G : ℤ) * M.ordZ (z j) G)
        (fun G hG => by
          rw [newWeight_sP M hF hF' hFF hirr hIsm hIsub hIst t (hrest G hG).2.2,
            blowUpModel_ordZ_strict]),
      t.ray j, ← Finset.add_sum_erase _ _ hFP, ← Finset.add_sum_erase _ _ hF'1]
    push_cast [Nat.cast_sub hclt.le]
    ring
  · intro ξ d hξ ξY hcm p' hp'
    obtain ⟨hS, hE, hiffG, u, hu, hvG, h1, h2, hltE, hltF, hltF', hnb⟩ :=
      step_core M hF hF' hFF hirr hIsm hIsub hIst t hFP hF'P hSI hξ ξY hcm p' hp'
    obtain ⟨hnF, haE, -, hltc⟩ := weights_split hξ.1 hclt.le hnb hltF hltF' h1 h2
    obtain ⟨hpF', hvF'⟩ := hltc hclt
    refine ⟨⟨hS, hpF'⟩, fun H hH => ?_, fun H hH v hv => ?_⟩
    · rcases (mem_newT M hF hF' hFF hirr hIsm hIsub hIst).1 hH with rfl | ⟨G, hG, rfl⟩
      · exact ⟨fun _ => Finset.mem_insert_self _ _, fun _ => hE⟩
      · by_cases hGF : G = F
        · subst hGF
          constructor
          · intro hp; exact absurd hp hnF
          · intro hm; exfalso
            rcases Finset.mem_insert.1 hm with he | hm
            · exact hEne G he
            rcases Finset.mem_insert.1 hm with he | hm
            · exact hFF (hinj he)
            · exact (hrest G ((hmemP0 G).1 hm)).2.1 rfl
        by_cases hGF' : G = F'
        · subst hGF'
          exact ⟨fun _ => Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun _ => hpF'⟩
        have hGF2 : ¬ (G = F ∨ G = F') := not_or.2 ⟨hGF, hGF'⟩
        rw [hiffG G hG hGF2]
        constructor
        · intro hGP
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((hmemP0 G).2
            (Finset.mem_erase.2 ⟨hGF', Finset.mem_erase.2 ⟨hGF, hGP⟩⟩)))
        · intro hm
          rcases Finset.mem_insert.1 hm with he | hm
          · exact absurd he (hEne G)
          rcases Finset.mem_insert.1 hm with he | hm
          · exact absurd (hinj he) hGF'
          · exact (hrest G ((hmemP0 G).1 hm)).1
    · rcases Finset.mem_insert.1 hH with rfl | hH
      · rw [newWeight_excE, ← haE]
        exact valuation_eq_of_span_eq hp' (hv.symm.trans (hu _ hEnew hE))
      rcases Finset.mem_insert.1 hH with rfl | hH
      · rw [newWeight_sP_F', ← hvF']
        exact valuation_eq_of_span_eq hp' (hv.symm.trans (hu _ (hsnew F' hF') hpF'))
      · obtain ⟨G, hG, rfl⟩ := Finset.mem_image.1 hH
        obtain ⟨hGP, hGF, hGF'⟩ := hrest G hG
        have hpG := (hiffG G (t.P_sub hGP) (not_or.2 ⟨hGF, hGF'⟩)).2 hGP
        rw [newWeight_sP M hF hF' hFF hirr hIsm hIsub hIst t hGF',
          ← hvG G hGP (not_or.2 ⟨hGF, hGF'⟩)]
        exact valuation_eq_of_span_eq hp' (hv.symm.trans (hu _ (hsnew G (t.P_sub hGP)) hpG))
  · show ∑ H ∈ insert _ _, newWeight M hF hF' hFF hirr hIsm hIsub hIst t H < _
    rw [Finset.sum_insert hEP0, Finset.sum_insert hF'P0, newWeight_excE, newWeight_sP_F',
      Finset.sum_image (fun x _ y _ hxy => hinj hxy),
      ← Finset.add_sum_erase _ _ hFP, ← Finset.add_sum_erase _ _ hF'1,
      Finset.sum_congr rfl (fun G hG => newWeight_sP M hF hF' hFF hirr hIsm hIsub hIst t
        (hrest G hG).2.2)]
    have := t.c_pos F hFP
    omega

include hF hF' hFF hirr hIsm hIsub hIst in
/-- The preimage of a preconnected set under the blow-up is preconnected: the blow-up is proper
and birational onto a normal scheme, so its fibres are connected. -/
theorem isPreconnected_preimage_blowUpToBase {S : Set M.Y} (hS : _root_.IsPreconnected S) :
    _root_.IsPreconnected (blowUpToBase I ⁻¹' S) := by
  have hc := codim_one_le M hF hF' hFF hirr hIsm hIsub hIst
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI : IsProper (blowUpToBase I) :=
    TwoStepTower.isProper_blowUpToBase (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
  have hbir : IsBirational (blowUpToBase I) :=
    Bridges.isBirational_of_isBirationalMorphism (isBirationalMorphism_blowUpToBase I hirr hc)
  refine isPreconnected_preimage_of_isClosedMap (blowUpToBase I).isClosedMap
    (fun b => (isConnected_fibre_of_isBirational _ hbir b).isPreconnected) hS (fun y _ => ?_)
  by_cases hy : y ∈ (I.support : Set M.Y)
  · exact exists_preimage_of_mem_centre (M.g ≫ sX) (centre_isSmoothBlowup M hIsm) hirr hc hy
  · exact exists_preimage_of_notMem I hy

open Classical in
include hF hF' hFF hirr hIsm hIsub hIst in
/-- The strata of the tracked components stay connected under the blow-up of the intersection
of two of them: an intersection of new components is the preimage of a stratum below, cut down
by the strict transform of `F'` when that is one of them. -/
theorem isPreconnected_iInter_blowUp {P : Finset (MMP.Mori.PrimeDivisor M.Y)}
    (hPT : P ⊆ M.T.support) (hFP : F ∈ P) (hF'P : F' ∈ P)
    (hconn : ∀ K ⊆ P, _root_.IsPreconnected (⋂ G ∈ K, (G.support : Set M.Y)))
    (hIFF : (I.support : Set M.Y) = (F.support : Set M.Y) ∩ F'.support)
    {K' : Finset (MMP.Mori.PrimeDivisor (blowUpModel M hF hF' hFF hirr hIsm hIsub hIst).Y)}
    (hK' : K' ⊆ insert eYM (insert (sPM F') (((P.erase F).erase F').image sPM))) :
    _root_.IsPreconnected (⋂ H ∈ K', (H.support : Set (blowUp I))) := by
  have hc := codim_one_le M hF hF' hFF hirr hIsm hIsub hIst
  have h := centre_isSmoothBlowup M hIsm
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI : IsProper (blowUpToBase I) :=
    TwoStepTower.isProper_blowUpToBase (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
  haveI := M.isVariety
  set L := P.filter (fun G => sPM G ∈ K' ∨ (eYM ∈ K' ∧ (G = F ∨ G = F'))) with hL
  have hLP : L ⊆ P := Finset.filter_subset _ _
  set A := ⋂ G ∈ L, (G.support : Set M.Y) with hA
  have hAL : ∀ G ∈ L, A ⊆ G.support := fun G hG => Set.biInter_subset_of_mem hG
  have hfwd : ∀ y ∈ ⋂ H ∈ K', (H.support : Set (blowUp I)), blowUpToBase I y ∈ A := by
    intro y hy
    refine Set.mem_iInter₂.2 fun G hG => ?_
    have hy' := Set.mem_iInter₂.1 hy
    rcases (Finset.mem_filter.1 hG).2 with hGK | ⟨hEK, hGF⟩
    · exact support_strictPrime_subset I _ (hy' _ hGK)
    · have hyE := hy' _ hEK
      change y ∈ ((excE (M.g ≫ sX) h hirr hc).support : Set (blowUp I)) at hyE
      rw [coe_support_excE] at hyE
      rcases hGF with e | e
      · rw [e]; exact (hIsub hyE).1
      · rw [e]; exact (hIsub hyE).2
  have hbwd : ∀ y, blowUpToBase I y ∈ A →
      (sPM F' ∈ K' → y ∈ ((sPM F').support : Set (blowUp I))) →
      y ∈ ⋂ H ∈ K', (H.support : Set (blowUp I)) := by
    intro y hyA hyF'
    refine Set.mem_iInter₂.2 fun H hH => ?_
    rcases Finset.mem_insert.1 (hK' hH) with e | hH'
    · rw [e] at hH ⊢
      have hF1 : F ∈ L := Finset.mem_filter.2 ⟨hFP, Or.inr ⟨hH, Or.inl rfl⟩⟩
      have hF2 : F' ∈ L := Finset.mem_filter.2 ⟨hF'P, Or.inr ⟨hH, Or.inr rfl⟩⟩
      change y ∈ ((excE (M.g ≫ sX) h hirr hc).support : Set (blowUp I))
      rw [coe_support_excE, Set.mem_preimage, hIFF]
      exact ⟨hAL F hF1 hyA, hAL F' hF2 hyA⟩
    rcases Finset.mem_insert.1 hH' with e | hH''
    · rw [e] at hH ⊢; exact hyF' hH
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.1 hH''
    obtain ⟨hGF', hG1⟩ := Finset.mem_erase.1 hG
    obtain ⟨hGF, hGP⟩ := Finset.mem_erase.1 hG1
    have hGL : G ∈ L := Finset.mem_filter.2 ⟨hGP, Or.inl hH⟩
    have hyG := hAL G hGL hyA
    by_cases hyI : blowUpToBase I y ∈ (I.support : Set M.Y)
    · exact mem_strictPrime_of_mem (M.g ≫ sX) h hirr hc M.isSmooth M.snc hF hF' hFF hIsm hIsub
        hIst y hyI (hPT hGP) (not_or.2 ⟨hGF, hGF'⟩) hyG
    · exact mem_support_strictPrime I _ hyI hyG
  by_cases hF'K : sPM F' ∈ K'
  · have hF'L : F' ∈ L := Finset.mem_filter.2 ⟨hF'P, Or.inl hF'K⟩
    have heq : (⋂ H ∈ K', (H.support : Set (blowUp I))) =
        blowUpToBase I ⁻¹' A ∩ ((sPM F').support : Set (blowUp I)) := by
      ext y
      exact ⟨fun hy => ⟨hfwd y hy, Set.mem_iInter₂.1 hy _ hF'K⟩,
        fun hy => hbwd y hy.1 fun _ => hy.2⟩
    rw [heq]
    have hG := genericPoint_notMem_of_subset_inter I hFF hIsub F'
    haveI : IsIso ((blowUpToBase I).stalkMap (sPM F').genericPoint) :=
      isIso_stalkMap_of_mem_biregularLocus _ (mem_biregularLocus_of_notMem I (by
        rw [map_genericPoint_strictPrime I hG]; exact hG))
    haveI : IsNormal F'.idealSheaf.subscheme := by
      haveI : Smooth (F'.idealSheaf.subschemeι ≫ M.g ≫ sX) :=
        smooth_of_isSmoothScheme (M.snc.1 F' hF')
      haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
      exact AlgebraicGeometry.isNormal_of_smooth (F'.idealSheaf.subschemeι ≫ M.g ≫ sX)
    exact (preimage_inter_support_of_birational (blowUpToBase I) (sPM F') F'
      (support_strictPrime_subset I hG) (map_genericPoint_strictPrime I hG) inferInstance
      (hconn L hLP) (hAL F' hF'L)).1
  · have heq : (⋂ H ∈ K', (H.support : Set (blowUp I))) = blowUpToBase I ⁻¹' A := by
      ext y
      exact ⟨hfwd y, fun hy => hbwd y hy fun h' => absurd h' hF'K⟩
    rw [heq]
    exact isPreconnected_preimage_blowUpToBase M hF hF' hFF hirr hIsm hIsub hIst (hconn L hLP)

end StepCore

section Iterate

variable {k : Type uP} [Field k] [CharZero k] {X : Scheme.{uP}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX] {Δ : Divisor X}
  {n : ℕ} {η : X} {ι : Type*} [Fintype ι] {z : ι → X.presheaf.stalk η} {α : ι → ℕ}

attribute [local instance] SModel.isIntegral SModel.isDominant SModel.isLocallyNoetherian
  SModel.isNormal

/-- All intersections of members of `P` are preconnected. -/
def StrataConnected {Y : Scheme.{uP}} (P : Finset (MMP.Mori.PrimeDivisor Y)) : Prop :=
  ∀ K ⊆ P, _root_.IsPreconnected (⋂ G ∈ K, (G.support : Set Y))

/-- For distinct `F, F' ∈ t.P` with the weight of `F` at most that of `F'`, there is a model
which is again the end of a stratum tower, carrying tracking data of smaller total weight whose
strata are connected. -/
theorem exists_step_of_le (hz : ∀ j, ∃ P ∈ Δ.support,
      IdealSheafData.stalk P.idealSheaf η = Ideal.span {z j})
    (M : SModel sX Δ n) (t : M.Track η z α) (hconn : StrataConnected t.P)
    (htow : M.IsStratumTower) {F F' : MMP.Mori.PrimeDivisor M.Y}
    (hFP : F ∈ t.P) (hF'P : F' ∈ t.P) (hFF : F ≠ F') (hle : t.c F ≤ t.c F') :
    ∃ (M' : SModel sX Δ n) (t' : M'.Track η z α), ∑ H ∈ t'.P, t'.c H < ∑ G ∈ t.P, t.c G ∧
      StrataConnected t'.P ∧ M'.IsStratumTower := by
  classical
  haveI := M.isVariety
  have hF := t.P_sub hFP
  have hF' := t.P_sub hF'P
  obtain ⟨I, hirr, hIsm, hSI, hIsub, hIst, hIFF, hIv⟩ := exists_centre (M.g ≫ sX) M.snc hF hF'
    hFF t.S_pre t.S_ne (t.S_sub F hFP) (t.S_sub F' hF'P)
  have hIFF' : (I.support : Set M.Y) = (F.support : Set M.Y) ∩ F'.support := by
    refine hIFF ?_
    have := hconn {F, F'} (Finset.insert_subset hFP (Finset.singleton_subset_iff.2 hF'P))
    rwa [Finset.set_biInter_insert, Finset.set_biInter_singleton] at this
  have htow' := blowUpModel_isStratumTower M hF hF' hFF hirr hIsm hIsub hIst htow hIFF' hIv
  rcases eq_or_lt_of_le hle with heq | hlt
  · obtain ⟨t', ht', hP'⟩ := step_eq M hF hF' hFF hirr hIsm hIsub hIst t hFP hF'P hSI heq hz
    exact ⟨_, t', ht', fun K hK => isPreconnected_iInter_blowUp M hF hF' hFF hirr hIsm hIsub hIst
      t.P_sub hFP hF'P hconn hIFF' (hK.trans hP'), htow'⟩
  · obtain ⟨t', ht', hP'⟩ := step_lt M hF hF' hFF hirr hIsm hIsub hIst t hFP hF'P hSI hlt hz
    exact ⟨_, t', ht', fun K hK => isPreconnected_iInter_blowUp M hF hF' hFF hirr hIsm hIsub hIst
      t.P_sub hFP hF'P hconn hIFF' (hK.trans hP'), htow'⟩

/-- If `t.P` has at least two components, there is a model which is again the end of a stratum
tower, carrying tracking data of smaller total weight whose strata are connected. -/
theorem exists_step (hz : ∀ j, ∃ P ∈ Δ.support,
      IdealSheafData.stalk P.idealSheaf η = Ideal.span {z j})
    (M : SModel sX Δ n) (t : M.Track η z α) (hconn : StrataConnected t.P)
    (htow : M.IsStratumTower) (h2 : 2 ≤ t.P.card) :
    ∃ (M' : SModel sX Δ n) (t' : M'.Track η z α), ∑ H ∈ t'.P, t'.c H < ∑ G ∈ t.P, t.c G ∧
      StrataConnected t'.P ∧ M'.IsStratumTower := by
  obtain ⟨F, hFP, F', hF'P, hFF⟩ := Finset.one_lt_card.1 h2
  rcases le_total (t.c F) (t.c F') with hle | hle
  · exact exists_step_of_le hz M t hconn htow hFP hF'P hFF hle
  · exact exists_step_of_le hz M t hconn htow hF'P hFP (Ne.symm hFF) hle

/-- There is a model which is the end of a stratum tower, carrying tracking data with at most one
component of positive weight. -/
theorem exists_final (hz : ∀ j, ∃ P ∈ Δ.support,
      IdealSheafData.stalk P.idealSheaf η = Ideal.span {z j})
    (M : SModel sX Δ n) (t : M.Track η z α) (hconn : StrataConnected t.P)
    (htow : M.IsStratumTower) :
    ∃ (M : SModel sX Δ n) (t : M.Track η z α), t.P.card ≤ 1 ∧ M.IsStratumTower := by
  suffices H : ∀ N, ∀ (M : SModel sX Δ n) (t : M.Track η z α), ∑ F ∈ t.P, t.c F ≤ N →
      StrataConnected t.P → M.IsStratumTower →
      ∃ (M : SModel sX Δ n) (t : M.Track η z α), t.P.card ≤ 1 ∧ M.IsStratumTower from
    H _ M t le_rfl hconn htow
  intro N
  induction N with
  | zero =>
    intro M t hN _ htow
    refine ⟨M, t, ?_, htow⟩
    by_contra h
    push Not at h
    obtain ⟨F, hF⟩ : t.P.Nonempty := Finset.card_pos.mp (by omega)
    have := Finset.single_le_sum (f := t.c) (fun _ _ => Nat.zero_le _) hF
    have := t.c_pos F hF
    omega
  | succ N ih =>
    intro M t hN hconn htow
    by_cases h : t.P.card ≤ 1
    · exact ⟨M, t, h, htow⟩
    · push Not at h
      obtain ⟨M', t', hlt, hconn', htow'⟩ := exists_step hz M t hconn htow h
      exact ih M' t' (by omega) hconn' htow'

omit [CharZero k] [IsNormal X] [LocallyOfFiniteType sX] in
/-- On a separated scheme, a valuation dominates the local ring of at most one point. -/
theorem eq_of_dominates [IsSeparated sX] {ξ : Valuation X.functionField ℤᵐ⁰} {x x' : X}
    (h : Dominates ξ x) (h' : Dominates ξ x') : x = x' :=
  MMP.Positivity.DivisorOver.eq_of_dominates sX ξ h.1 h.2 h'.1 h'.2

omit [CharZero k] [IsNormal X] in
/-- The identity model. -/
abbrev baseModel (B : BaseData sX Δ n η) : SModel sX Δ n where
  Y := X
  g := 𝟙 X
  isVariety := by rw [Category.id_comp]; exact B.isVariety
  isSmooth := by rw [Category.id_comp]; exact B.isSmooth
  dim := B.dim
  isProper := inferInstance
  isProj := (MMP.isProjectiveMorphism_of_isClosedImmersion (𝟙 X)).isProjective
  isBir := MMP.Mori.isBirationalMorphism_of_isIso _
  T := Δ
  red := B.red
  snc := by rw [Category.id_comp]; exact B.snc
  supp := rfl
  exc := by
    rw [(MMP.Mori.exceptionalSet_eq_bot_iff (𝟙 X)).2 inferInstance]
    exact Set.empty_subset _
  crep := by
    intro F U0 τ hF hgen
    haveI := B.isVariety
    have hd := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) B.dim
    rw [MMP.Mori.pullbackRationalPluriForms_id hd τ]
    have := hgen.2 F ⟨_, genericPoint_mem_support F, hF⟩
    rw [Divisor.coeff_toQDivisor] at this
    push_cast at this
    have h2 : ((F.ordForm τ : ℤ) : ℚ) = ((-Δ.coeff F : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast h2

/-- The identity model is the empty blow-up sequence. -/
theorem baseModel_isStratumTower (B : BaseData sX Δ n η) : (baseModel B).IsStratumTower :=
  ⟨.nil X, rfl, by
    change eqToHom rfl ≫ 𝟙 X = 𝟙 X
    rw [eqToHom_refl, Category.id_comp], trivial⟩

end Iterate

end Subtraction

end MMP.Fourfold.SNCWeight

end
