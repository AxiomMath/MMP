module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksThomChart
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSection
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.ThomChartGeneric
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.PushforwardDegree
public import MMP.AlgebraicTopology.ThomClass.OfRank
public import MMP.AlgebraicTopology.LocalizedFirstChern.BallChart
public import MMP.AlgebraicGeometry.SubschemeOver
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.LocalCapGeneric
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ComplexSchemeSubscheme

/-!
# Fulton's Lemma 19.1.3 near a general point of a component: the cap side, Stacks bundles

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of rank one, on a complex variety
`X` of dimension `k + 1`, with vector bundle `π : 𝐕(ℰ) ⟶ X`, and let `σ : X ⟶ 𝐕(ℰ)` be a
section, with zero scheme `D = Z(σ)`. Let `c = (V, b)` be a chart of `ℰ` and
`O ⊆ V(ℂ) ∩ X_reg(ℂ)` an open set with a holomorphic ball product chart `Φ : O ≅ B_ε × B` whose
first coordinate `g` satisfies `(x^c ∘ σ)₀ = g ^ m` on `O` and `σ⁻¹(0) ∩ O = g⁻¹(0)`. Then
`W = {p ∈ D(ℂ) | ι p ∈ O} ≅ O ∩ σ⁻¹(0) ≅ B` carries the restriction to `W` of
`σ^*(u_ℰ) ∩ cl(X)` to `m · μ_B`. This is the cap side of the local computation in Fulton's
proof of Lemma 19.1.3, for the bundles `𝐕(ℰ)` of `MMP.Modules`.

## Main definitions

* `MMP.Modules.zeroLocusSet`: the zero locus `σ⁻¹(0(X(ℂ))) ⊆ X(ℂ)`.
* `MMP.Modules.zeroLocusInvHom`: the inverse `σ⁻¹(0(X(ℂ))) → Z(σ)(ℂ)` of `zeroLocusHom`.
* `MMP.Modules.localZeroHomeomorph`: the homeomorphism `O ∩ σ⁻¹(0) ≅ B`.
* `MMP.Modules.zeroLocusOpens`: the open set `W = {p ∈ D(ℂ) | ι p ∈ O}` of `D(ℂ)`.
* `MMP.Modules.zeroLocusOpensHomeomorph`: its homeomorphism with `O ∩ σ⁻¹(0)`.

## Main results

* `MMP.Modules.pushforward_opensInterMap_restrict_localizedTopChernCap`:
  `(σ^* u_ℰ ∩ a)|_{O ∩ σ⁻¹(0)} = (σ|_O)^* u_ℰ ∩ a|_O`.
* `MMP.Modules.pushforward_capProductSupportPullback_thomClass_eq_smul`: in a chart in which
  the local coordinate of `σ` is `g ^ m`, `(σ|_O)^* u_ℰ ∩ a = m · g^* u₀ ∩ a`.
* `MMP.Modules.pushforward_restrict_localizedTopChernCap_eq_smul`: the cap side in a ball
  product chart, `(σ^*(u_ℰ) ∩ cl(X))|_{O ∩ σ⁻¹(0)} ↦ m · μ_B`.
* `MMP.Modules.pushforward_restrict_zeroLocusOpens_eq_smul`: the same on `W ⊆ D(ℂ)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Set Metric
open MMP.UnderlyingSpace
open scoped MMP.SubschemeOver

namespace MMP.Modules

open MMP
open MMP.Intersection.Scheme (dimension)

open borelMooreHomology BorelMooreCross FundamentalClass

/-! ### The inverse of `Z(σ)(ℂ) ≅ σ⁻¹(0(X(ℂ)))` -/

section InvHom

variable (R : Type) [CommRing R] {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] {E : X.Modules}
  [E.IsQuasicoherent]

/-- The zero locus `σ⁻¹(0(X(ℂ))) ⊆ X(ℂ)` of `σ : X ⟶ 𝐕(ℰ)`. -/
abbrev zeroLocusSet (σ : X ⟶ totalSpace E) [σ.IsOver (Spec (.of ℂ))] :
    Set (TopCat.of (UnderlyingSpace ℂ X)) :=
  (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
    range (UnderlyingSpace.map (K := ℂ) (zeroSection E))

variable (σ : X ⟶ totalSpace E) [σ.IsOver (Spec (.of ℂ))]

/-- The inverse `σ⁻¹(0(X(ℂ))) → Z(σ)(ℂ)` of the homeomorphism `zeroLocusHom`. -/
def zeroLocusInvHom :
    TopCat.of (zeroLocusSet σ) ⟶ TopCat.of (UnderlyingSpace ℂ (zeroLocus E σ).subscheme) :=
  TopCat.ofHom ⟨(zeroLocusHomeomorph σ).symm, (zeroLocusHomeomorph σ).symm.continuous⟩

/-- `zeroLocusInvHom` is proper, being a homeomorphism. -/
lemma isProperMap_zeroLocusInvHom : IsProperMap (zeroLocusInvHom σ) :=
  (zeroLocusHomeomorph σ).symm.isProperMap

/-- `zeroLocusInvHom` is a left inverse of `zeroLocusHom`. -/
@[reassoc (attr := simp)]
lemma zeroLocusHom_comp_zeroLocusInvHom : zeroLocusHom σ ≫ zeroLocusInvHom σ = 𝟙 _ :=
  TopCat.hom_ext (ContinuousMap.ext fun p ↦ (zeroLocusHomeomorph σ).symm_apply_apply p)

/-- `zeroLocusInvHom` is a right inverse of `zeroLocusHom`. -/
@[reassoc (attr := simp)]
lemma zeroLocusInvHom_comp_zeroLocusHom : zeroLocusInvHom σ ≫ zeroLocusHom σ = 𝟙 _ :=
  TopCat.hom_ext (ContinuousMap.ext fun p ↦ (zeroLocusHomeomorph σ).apply_symm_apply p)

/-- Pushing a class of `Z(σ)(ℂ)` forward to `σ⁻¹(0(X(ℂ)))` and back gives it back. -/
@[simp]
lemma pushforward_zeroLocusInvHom_pushforward_zeroLocusHom (j : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (zeroLocus E σ).subscheme)) j) :
    borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroLocusInvHom σ)
        (isProperMap_zeroLocusInvHom σ) j
        (borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroLocusHom σ)
          (isProperMap_zeroLocusHom σ) j a) = a :=
  borelMooreHomology.pushforward_symm_pushforward_homeomorph R _ (zeroLocusHomeomorph σ) j a

/-- Pushing a class of `σ⁻¹(0(X(ℂ)))` forward to `Z(σ)(ℂ)` and back gives it back. -/
@[simp]
lemma pushforward_zeroLocusHom_pushforward_zeroLocusInvHom (j : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (zeroLocusSet σ)) j) :
    borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroLocusHom σ)
        (isProperMap_zeroLocusHom σ) j
        (borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroLocusInvHom σ)
          (isProperMap_zeroLocusInvHom σ) j a) = a :=
  borelMooreHomology.pushforward_symm_pushforward_homeomorph R _ (zeroLocusHomeomorph σ).symm j a

end InvHom

/-! ### The cap product restricted to an open set of a chart -/

section LocalCap

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsIntegral X]
  {E : X.Modules} [E.IsQuasicoherent]

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
  (R : Type) [CommRing R]

omit [IsIntegral X] in
/-- **The localized first Chern class restricted to an open set**:
`(σ^* u_ℰ ∩ a)|_{O ∩ σ⁻¹(0)} = (σ|_O)^* u_ℰ ∩ a|_O`. -/
lemma pushforward_opensInterMap_restrict_localizedTopChernCap (σ : X ⟶ totalSpace E)
    [σ.IsOver (Spec (.of ℂ))] (O : Opens (TopCat.of (UnderlyingSpace ℂ X)))
    (hTd : HasProperNeighbourhoodDeformations ((inclHom O).hom ⁻¹' zeroLocusSet σ)) (k : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) k) :
    (pushforward R (ModuleCat.of R R) (opensInterMap O (zeroLocusSet σ))
        (isProperMap_opensInterMap O (zeroLocusSet σ)) (k - (2 * 1 : ℕ))).hom
      ((restrict R (ModuleCat.of R R) (opensInter O (zeroLocusSet σ)) (k - (2 * 1 : ℕ))).hom
        (localizedTopChernCap σ R 1 k a)) =
      capProductSupportPullback R (inclHom O)
        ((isClosed_range_zeroSection (E := E)).preimage
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom.continuous) hTd (2 * 1 : ℕ) k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
          (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom
            (thomClass R E 1))
        ((restrict R (ModuleCat.of R R) O k).hom a) := by
  unfold localizedTopChernCap
  rw [capProductSupportPullback_apply]
  exact pushforward_opensInterMap_restrict_capProductSupport R _ O _
    (hasProperNeighbourhoodDeformations_preimage σ) hTd _ k _ a

omit [IsIntegral X] in
/-- **The cap side in a ball product chart, before the local computation** (steps (2) and (3)
of the proof of Fulton's Lemma 19.1.3, moved to `X_reg(ℂ) ∩ O`). Let `O ⊆ V(ℂ)` be an open
subset of `X_reg(ℂ)` inside the domain of a chart `c` of `ℰ`, `g : X_reg(ℂ) ∩ O → ℂ` continuous
(in the application, `g = pr₁ ∘ Φ` for a ball product chart `Φ : O ≅ B_ε × B`), and suppose the
local coordinate `(x^c ∘ σ)₀` of the section `σ` is `g ^ m` on `O` and `σ⁻¹(0) ∩ O = g⁻¹(0)`.
Then `(σ|_O)^* u_ℰ ∩ a|_O`, transported to `g⁻¹(0) ⊆ X_reg(ℂ) ∩ O`, is `m · g^* u₀ ∩ a|_O`. -/
theorem pushforward_capProductSupportPullback_thomClass_eq_smul (σ : X ⟶ totalSpace E)
    [σ.IsOver (Spec (.of ℂ))] (hσ : σ ≫ proj E = 𝟙 X) (c : Chart E 1)
    {O : Opens (TopCat.of (UnderlyingSpace ℂ X))} (hOc : (O : Set _) ⊆ chartBase c)
    (hO : O ≤ regularOpens ℂ X) (g : TopCat.of (regularOpensInter (𝕜 := ℂ) O) ⟶ TopCat.of ℂ)
    (m : ℕ)
    (hh : ∀ p : O, coord c (mapFun σ p.1) 0 = g (regularOpensInterMap hO p) ^ m)
    (hz : setInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ) =
      (regularOpensInterMap hO).hom ⁻¹' (g ⁻¹' {0}))
    (hTd : HasProperNeighbourhoodDeformations ((inclHom O).hom ⁻¹' zeroLocusSet σ))
    (hYd : HasProperNeighbourhoodDeformations (g ⁻¹' {0}))
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ℂ) {0} (2 : ℕ)}
    (hu₀ : IsLocalOrientationClass R Complex.basisOneI (0 : TopCat.of ℂ) u₀) (k : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of O) k) :
    (pushforward R (ModuleCat.of R R)
        (TopCat.ofHom ((regularOpensInterMap hO).hom.restrictPreimage (g ⁻¹' {0})))
        ((isProperMap_regularOpensInterMap hO).restrictPreimage _) (k - (2 * 1 : ℕ))).hom
      ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (Homeomorph.setCongr hz :
          C(setInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ),
            (regularOpensInterMap hO).hom ⁻¹' (g ⁻¹' {0}))))
          (Homeomorph.isProperMap _) (k - (2 * 1 : ℕ))).hom
        (capProductSupportPullback R (inclHom O)
          ((isClosed_range_zeroSection (E := E)).preimage
            (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom.continuous) hTd (2 * 1 : ℕ) k
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
            (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
            (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom
              (thomClass R E 1))
          a)) =
      (m : R) • capProductSupportPullback R g isClosed_singleton hYd (2 * 1 : ℕ) k u₀
        ((pushforward R (ModuleCat.of R R) (regularOpensInterMap hO)
          (isProperMap_regularOpensInterMap hO) k).hom a) := by
  set f := regularOpensInterMap hO
  have hz' : (inclHom O).hom ⁻¹' zeroLocusSet σ = (f ≫ g) ⁻¹' {0} := hz
  have hg : ((inclHom O).hom ⁻¹' zeroLocusSet σ)ᶜ ⊆ (f ≫ g) ⁻¹' ({0}ᶜ : Set (TopCat.of ℂ)) := by
    rw [hz']
    exact fun _ hx ↦ hx
  have key : (cohomologyWithSupports.pullback R (ModuleCat.of R R) (borelMooreHomology.inclHom O)
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
          (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom
            (thomClass R E 1)) =
      (m : R) •
        (relativeSingularCohomology.map R (ModuleCat.of R R) (f ≫ g) hg (2 * 1 : ℕ)).hom u₀ :=
    pullback_inclHom_pullback_thomClass_eq_smul R σ hσ c O hOc
      (TopCat.ofHom ⟨fun p ↦ (f ≫ g) p ^ m, (continuous_pow m).comp (f ≫ g).hom.continuous⟩)
      (fun p ↦ (hh p).symm) (f ≫ g) m (fun _ ↦ rfl) hg hu₀
  have hY'd : HasProperNeighbourhoodDeformations (f ⁻¹' (g ⁻¹' {0})) := by
    rwa [← hz]
  exact (pushforward_pushforward_capProductSupport_eq_smul R _ hTd ((2 * 1 : ℕ) : ℤ) k _ _ _ _
    key a).trans (congrArg _
      (pushforward_restrictPreimage_pushforward_setCongr_capProductSupport_map
      R f (isProperMap_regularOpensInterMap hO) g hz _ hTd hg hYd hY'd ((2 * 1 : ℕ) : ℤ) k u₀ a))

end LocalCap

/-! ### The cap side in a ball product chart -/

section LocalZero

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsIntegral X]
  {E : X.Modules} [E.IsQuasicoherent]

/-- The homeomorphism `O ∩ σ⁻¹(0) ≅ B` of a ball product chart `Φ : O ≅ B_ε × B` in which
`σ⁻¹(0) ∩ O` is `{(Φ p).1 = 0}`. -/
def localZeroHomeomorph (σ : X ⟶ totalSpace E) [σ.IsOver (Spec (.of ℂ))]
    {O : Opens (UnderlyingSpace ℂ X)}
    (hO : O ≤ regularOpens ℂ X) {B : Type} [TopologicalSpace B] {ε : ℝ} (hε : 0 < ε)
    (Φ : regularOpensInter (𝕜 := ℂ) O ≃ₜ ball (0 : ℂ) ε × B)
    (hz : setInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ) =
      (regularOpensInterMap hO).hom ⁻¹' (ballChartFst Φ ⁻¹' {0})) :
    opensInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ) ≃ₜ B :=
  (opensInterHomeo (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ)).trans
    ((Homeomorph.setCongr hz).trans
      (((subOpensHomeo (Y := TopCat.of (UnderlyingSpace ℂ X))
        (U := (regularOpens ℂ X : Opens (TopCat.of (UnderlyingSpace ℂ X)))) hO).sets rfl).trans
        (ballZeroFibreHomeomorph Φ hε (ballChartFst Φ) fun _ ↦ rfl)))

omit [IsIntegral X] in
/-- `localZeroHomeomorph`, as a morphism of spaces, is the composite of its four factors. -/
lemma ofHom_localZeroHomeomorph (σ : X ⟶ totalSpace E) [σ.IsOver (Spec (.of ℂ))]
    {O : Opens (UnderlyingSpace ℂ X)}
    (hO : O ≤ regularOpens ℂ X) {B : Type} [TopologicalSpace B] {ε : ℝ} (hε : 0 < ε)
    (Φ : regularOpensInter (𝕜 := ℂ) O ≃ₜ ball (0 : ℂ) ε × B)
    (hz : setInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ) =
      (regularOpensInterMap hO).hom ⁻¹' (ballChartFst Φ ⁻¹' {0})) :
    TopCat.ofHom (localZeroHomeomorph σ hO hε Φ hz : C(_, B)) =
      opensInterMap (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ) ≫
        TopCat.ofHom (Homeomorph.setCongr hz :
          C(setInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ),
            (regularOpensInterMap hO).hom ⁻¹' (ballChartFst Φ ⁻¹' {0}))) ≫
        TopCat.ofHom ((regularOpensInterMap hO).hom.restrictPreimage (ballChartFst Φ ⁻¹' {0})) ≫
        TopCat.ofHom (ballZeroFibreHomeomorph Φ hε (ballChartFst Φ) fun _ ↦ rfl :
          C((ballChartFst Φ ⁻¹' {0} : Set (TopCat.of (regularOpensInter (𝕜 := ℂ) O))), B)) :=
  rfl

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
  (R : Type) [CommRing R]

/-- The cap side in a ball product chart, as a chain of push-forwards along the four factors of
`localZeroHomeomorph`, for a first coordinate `g` of the chart. -/
theorem localizedTopChernCap_chain_eq_smul {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = dimension X) (σ : X ⟶ totalSpace E)
    [σ.IsOver (Spec (.of ℂ))] (hσ : σ ≫ proj E = 𝟙 X) (c : Chart E 1)
    {O : Opens (TopCat.of (UnderlyingSpace ℂ X))} (hOc : (O : Set _) ⊆ chartBase c)
    (hO : O ≤ regularOpens ℂ X) {B : Type} [TopologicalSpace B] [T2Space B] [ConnectedSpace B]
    [SecondCountableTopology B] [TopologicalSpace.MetrizableSpace B]
    [ChartedSpace (EuclideanSpace ℂ (Fin k)) B] {ε : ℝ} (hε : 0 < ε)
    (Φ : regularOpensInter (𝕜 := ℂ) O ≃ₜ ball (0 : ℂ) ε × B)
    (g : TopCat.of (regularOpensInter (𝕜 := ℂ) O) ⟶ TopCat.of ℂ) (hg : ∀ p, g p = ((Φ p).1 : ℂ))
    (hΦ : letI := regularChartedSpace (𝕜 := ℂ) hn
      ∀ c ∈ atlas (EuclideanSpace ℂ (Fin (k + 1))) (regularOpensInter (𝕜 := ℂ) O),
        ∀ c' ∈ atlas (EuclideanSpace ℂ (Fin k)) B, ∀ x ∈ c.source, (Φ x).2 ∈ c'.source →
          ∃ L : EuclideanSpace ℂ (Fin (k + 1)) →L[ℂ] ℂ × EuclideanSpace ℂ (Fin k),
            Function.Injective L ∧
            HasFDerivAt (fun y ↦ (((Φ (c.symm y)).1 : ℂ), c' (Φ (c.symm y)).2)) L (c x))
    (m : ℕ)
    (hh : ∀ p : O, coord c (mapFun σ p.1) 0 = g (regularOpensInterMap hO p) ^ m)
    (hz : setInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ) =
      (regularOpensInterMap hO).hom ⁻¹' (g ⁻¹' {0}))
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X))
      (2 * (k + 1) : ℕ)} (hμ : IsVarietyFundamentalClass R hn μ)
    {μB : borelMooreHomology R (ModuleCat.of R R) (TopCat.of B) (2 * k : ℕ)}
    (hμB : IsFundamentalClass R (euclideanComplexOrientationBasis k) μB)
    (hdeg : ((2 * (k + 1) : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ) = ((2 * k : ℕ) : ℤ)) :
    congrDegree R _ hdeg ((pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (ballZeroFibreHomeomorph Φ hε g hg :
          C((g ⁻¹' {0} : Set (TopCat.of (regularOpensInter (𝕜 := ℂ) O))), B)))
        (ballZeroFibreHomeomorph Φ hε g hg).isProperMap _).hom
      ((pushforward R (ModuleCat.of R R)
          (TopCat.ofHom ((regularOpensInterMap hO).hom.restrictPreimage (g ⁻¹' {0})))
          ((isProperMap_regularOpensInterMap hO).restrictPreimage _) _).hom
        ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (Homeomorph.setCongr hz :
            C(setInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ),
              (regularOpensInterMap hO).hom ⁻¹' (g ⁻¹' {0})))) (Homeomorph.isProperMap _)
              _).hom
          ((pushforward R (ModuleCat.of R R) (opensInterMap O (zeroLocusSet σ))
            (isProperMap_opensInterMap O (zeroLocusSet σ)) _).hom
            ((restrict R (ModuleCat.of R R) (opensInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O
              (zeroLocusSet σ)) _).hom (localizedTopChernCap σ R 1
                ((2 * (k + 1) : ℕ) : ℤ) μ)))))) =
      (m : R) • μB := by
  let := regularChartedSpace (𝕜 := ℂ) hn
  let f := regularOpensInterMap hO
  have hYd : HasProperNeighbourhoodDeformations (g ⁻¹' {0}) :=
    hasProperNeighbourhoodDeformations_ballChart hε Φ g hg
  have hTd : HasProperNeighbourhoodDeformations ((inclHom O).hom ⁻¹' zeroLocusSet σ) := by
    have := hYd.preimage_homeomorph (subOpensHomeo (Y := TopCat.of (UnderlyingSpace ℂ X))
      (U := (regularOpens ℂ X : Opens (TopCat.of (UnderlyingSpace ℂ X)))) hO)
    have e : (inclHom O).hom ⁻¹' zeroLocusSet σ =
      (subOpensHomeo (Y := TopCat.of (UnderlyingSpace ℂ X))
      (U := (regularOpens ℂ X : Opens (TopCat.of (UnderlyingSpace ℂ X)))) hO) ⁻¹' (g ⁻¹' {0}) := hz
    rw [e]
    exact this
  obtain ⟨u₀, hu₀⟩ := exists_isLocalOrientationClass (T := TopCat.of ℂ) (R := R)
    (isOrientedAtlas_of_isManifold_complex ℂ) (n := 2) two_pos Complex.basisOneI 0
  let μP := (restrict R (ModuleCat.of R R) (Y := TopCat.of (regularOpens ℂ X))
    (regularOpensInter O) (2 * (k + 1) : ℕ)).hom
    ((restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X))
      (regularOpens ℂ X : Opens (TopCat.of (UnderlyingSpace ℂ X))) (2 * (k + 1) : ℕ)).hom μ)
  have hμP : IsFundamentalClass R (euclideanComplexOrientationBasis (k + 1)) μP := hμ.restrict _
  have hfμ : (pushforward R (ModuleCat.of R R) f (isProperMap_regularOpensInterMap hO)
      (2 * (k + 1) : ℕ)).hom ((restrict R (ModuleCat.of R R) O (2 * (k + 1) : ℕ)).hom μ) = μP :=
    (restrict_regularOpensInter_restrict R hO _ μ).symm
  have hball := IsFundamentalClass.pushforward_ballZeroFibreHomeomorph_capProductSupportPullback R
    hμP hμB hε Φ hΦ g hg hu₀ hYd (by push_cast; ring)
  have hcap := pushforward_opensInterMap_restrict_localizedTopChernCap R σ O hTd
    (2 * (k + 1) : ℕ) μ
  have hthom := pushforward_capProductSupportPullback_thomClass_eq_smul R σ hσ c hOc hO g m hh
    hz hTd hYd hu₀ (2 * (k + 1) : ℕ) ((restrict R (ModuleCat.of R R) O (2 * (k + 1) : ℕ)).hom μ)
  rw [hcap, hthom, map_smul, map_smul]
  refine congrArg ((m : R) • ·) ?_
  rw [← pushforward_congrDegree_apply_of_eq,
    congrDegree_capProductSupportPullback_eq_of_heq R g isClosed_singleton hYd
      (show ((2 * 1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) from rfl) _ hdeg (by push_cast; ring) u₀ u₀ HEq.rfl]
  rwa [← hfμ] at hball

/-- **The cap side near a general point of a component of `D`, in a ball product chart.** Let
`O ⊆ V(ℂ) ∩ X_reg(ℂ)` be open, inside the domain of a chart `c` of `ℰ`, and
`Φ : O ≅ B_ε × B` a holomorphic ball product chart with first coordinate `g`, in which the local
coordinate `(x^c ∘ σ)₀` of the section `σ` is `g ^ m` and `σ⁻¹(0) ∩ O = g⁻¹(0)`. Then for every
fundamental class `cl(X)` and fundamental class `μ_B` of `B`, the homeomorphism
`O ∩ σ⁻¹(0) ≅ B` carries `(σ^*(u_ℰ) ∩ cl(X))|_{O ∩ σ⁻¹(0)}` to `m · μ_B` (Fulton, proof of
Lemma 19.1.3). -/
theorem pushforward_restrict_localizedTopChernCap_eq_smul {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = dimension X) (σ : X ⟶ totalSpace E)
    [σ.IsOver (Spec (.of ℂ))] (hσ : σ ≫ proj E = 𝟙 X) (c : Chart E 1)
    {O : Opens (TopCat.of (UnderlyingSpace ℂ X))} (hOc : (O : Set _) ⊆ chartBase c)
    (hO : O ≤ regularOpens ℂ X) {B : Type} [TopologicalSpace B] [T2Space B] [ConnectedSpace B]
    [SecondCountableTopology B] [TopologicalSpace.MetrizableSpace B]
    [ChartedSpace (EuclideanSpace ℂ (Fin k)) B] {ε : ℝ} (hε : 0 < ε)
    (Φ : regularOpensInter (𝕜 := ℂ) O ≃ₜ ball (0 : ℂ) ε × B)
    (hΦ : letI := regularChartedSpace (𝕜 := ℂ) hn
      ∀ c ∈ atlas (EuclideanSpace ℂ (Fin (k + 1))) (regularOpensInter (𝕜 := ℂ) O),
        ∀ c' ∈ atlas (EuclideanSpace ℂ (Fin k)) B, ∀ x ∈ c.source, (Φ x).2 ∈ c'.source →
          ∃ L : EuclideanSpace ℂ (Fin (k + 1)) →L[ℂ] ℂ × EuclideanSpace ℂ (Fin k),
            Function.Injective L ∧
            HasFDerivAt (fun y ↦ (((Φ (c.symm y)).1 : ℂ), c' (Φ (c.symm y)).2)) L (c x))
    (m : ℕ)
    (hh : ∀ p : O, coord c (mapFun σ p.1) 0 = ballChartFst Φ (regularOpensInterMap hO p) ^ m)
    (hz : setInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ) =
      (regularOpensInterMap hO).hom ⁻¹' (ballChartFst Φ ⁻¹' {0}))
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X))
      (2 * (k + 1) : ℕ)} (hμ : IsVarietyFundamentalClass R hn μ)
    {μB : borelMooreHomology R (ModuleCat.of R R) (TopCat.of B) (2 * k : ℕ)}
    (hμB : IsFundamentalClass R (euclideanComplexOrientationBasis k) μB)
    (hdeg : ((2 * (k + 1) : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ) = ((2 * k : ℕ) : ℤ)) :
    (pushforward R (ModuleCat.of R R) (TopCat.ofHom (localZeroHomeomorph σ hO hε Φ hz : C(_, B)))
        (localZeroHomeomorph σ hO hε Φ hz).isProperMap (2 * k : ℕ)).hom
      ((restrict R (ModuleCat.of R R) (opensInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O
          (zeroLocusSet σ)) (2 * k : ℕ)).hom
        (congrDegree R _ hdeg (localizedTopChernCap σ R 1 _ μ))) =
      (m : R) • μB := by
  let := regularChartedSpace (𝕜 := ℂ) hn
  let f := regularOpensInterMap hO
  let gP := ballChartFst Φ
  have hsplit : ∀ (d : ℤ) (x : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (opensInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ))) d),
      (pushforward R (ModuleCat.of R R) (TopCat.ofHom (localZeroHomeomorph σ hO hε Φ hz : C(_, B)))
        (localZeroHomeomorph σ hO hε Φ hz).isProperMap d).hom x =
      (pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (ballZeroFibreHomeomorph Φ hε gP fun _ ↦ rfl :
          C((gP ⁻¹' {0} : Set (TopCat.of (regularOpensInter (𝕜 := ℂ) O))), B)))
        (ballZeroFibreHomeomorph Φ hε gP fun _ ↦ rfl).isProperMap d).hom
      ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (f.hom.restrictPreimage (gP ⁻¹' {0})))
          ((isProperMap_regularOpensInterMap hO).restrictPreimage _) d).hom
        ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (Homeomorph.setCongr hz :
            C(setInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ),
              f.hom ⁻¹' (gP ⁻¹' {0})))) (Homeomorph.isProperMap _) d).hom
          ((pushforward R (ModuleCat.of R R) (opensInterMap O (zeroLocusSet σ))
            (isProperMap_opensInterMap O (zeroLocusSet σ)) d).hom x))) := by
    intro d x
    rw [pushforward_apply_eq_of_hom_eq R _ (ofHom_localZeroHomeomorph σ hO hε Φ hz) _
      (localZeroHomeomorph σ hO hε Φ hz).isProperMap,
      pushforward_comp R _ _ _ (isProperMap_opensInterMap O (zeroLocusSet σ))
        ((Homeomorph.setCongr hz).trans
          (((subOpensHomeo (Y := TopCat.of (UnderlyingSpace ℂ X))
          (U := (regularOpens ℂ X : Opens (TopCat.of (UnderlyingSpace ℂ X)))) hO).sets rfl).trans
          (ballZeroFibreHomeomorph Φ hε (ballChartFst Φ) fun _ ↦ rfl))).isProperMap,
      pushforward_comp R _ _ _ (Homeomorph.isProperMap _)
        ((((subOpensHomeo (Y := TopCat.of (UnderlyingSpace ℂ X))
          (U := (regularOpens ℂ X : Opens (TopCat.of (UnderlyingSpace ℂ X)))) hO).sets rfl).trans
          (ballZeroFibreHomeomorph Φ hε (ballChartFst Φ) fun _ ↦ rfl))).isProperMap,
      pushforward_comp R _ _ _ ((isProperMap_regularOpensInterMap hO).restrictPreimage _)
        (ballZeroFibreHomeomorph Φ hε gP fun _ ↦ rfl).isProperMap]
    rfl
  rw [congrDegree_restrict_apply_of_eq, pushforward_congrDegree_apply_of_eq, hsplit]
  exact localizedTopChernCap_chain_eq_smul R hn σ hσ c hOc hO hε Φ gP (fun _ ↦ rfl) hΦ m hh hz
    hμ hμB hdeg

end LocalZero

/-! ### The cap side on an open set of the zero scheme -/

section Component

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsIntegral X]
  {E : X.Modules} [E.IsQuasicoherent]

/-- The open set `W = {p ∈ D(ℂ) | ι p ∈ O}` of the complex points of the zero scheme
`D = Z(σ)` lying over an open `O ⊆ X(ℂ)`, as the preimage of `O ∩ σ⁻¹(0)` under
`D(ℂ) ≅ σ⁻¹(0)`. -/
abbrev zeroLocusOpens (σ : X ⟶ totalSpace E) [σ.IsOver (Spec (.of ℂ))]
    (O : Opens (UnderlyingSpace ℂ X)) :
    Opens (UnderlyingSpace ℂ (zeroLocus E σ).subscheme) :=
  Opens.comap (zeroLocusHom σ).hom
    (opensInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ))

/-- `W ≅ O ∩ σ⁻¹(0)`, the restriction of `D(ℂ) ≅ σ⁻¹(0)`. -/
def zeroLocusOpensHomeomorph (σ : X ⟶ totalSpace E) [σ.IsOver (Spec (.of ℂ))]
    (O : Opens (UnderlyingSpace ℂ X)) :
    zeroLocusOpens σ O ≃ₜ opensInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ) :=
  (zeroLocusHomeomorph σ).subtype fun _ ↦ Iff.rfl

variable (R : Type) [CommRing R]

omit [IsIntegral X] in
/-- Restricting a class of `σ⁻¹(0)` transported to `D(ℂ)`, to `W`, and pushing it to
`O ∩ σ⁻¹(0)` is restricting it to `O ∩ σ⁻¹(0)`. -/
lemma pushforward_zeroLocusOpensHomeomorph_restrict (σ : X ⟶ totalSpace E)
    [σ.IsOver (Spec (.of ℂ))] (O : Opens (UnderlyingSpace ℂ X)) (n : ℤ)
    (c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (zeroLocusSet σ)) n) :
    (pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (zeroLocusOpensHomeomorph σ O : C(zeroLocusOpens σ O, _)))
        (zeroLocusOpensHomeomorph σ O).isProperMap n).hom
      ((restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ (zeroLocus E σ).subscheme))
        (zeroLocusOpens σ O) n).hom
        ((pushforward R (ModuleCat.of R R) (zeroLocusInvHom σ)
          (isProperMap_zeroLocusInvHom σ) n).hom c)) =
      (restrict R (ModuleCat.of R R) (opensInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O
        (zeroLocusSet σ)) n).hom c := by
  have h1 := restrict_pushforward_apply R (ModuleCat.of R R) (zeroLocusHom σ)
    (isProperMap_zeroLocusHom σ)
    (opensInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ)) n
    ((pushforward R (ModuleCat.of R R) (zeroLocusInvHom σ)
          (isProperMap_zeroLocusInvHom σ) n).hom c)
  rw [pushforward_zeroLocusHom_pushforward_zeroLocusInvHom] at h1
  rw [h1]
  rfl

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]

/-- **The cap side on `W`.** In a ball product chart `Φ : O ≅ B_ε × B` inside the domain of a
chart `c` of `ℰ`, in which the local coordinate `(x^c ∘ σ)₀` of the section `σ` is `g ^ m`,
`g = pr₁ ∘ Φ`, the homeomorphism `W ≅ B` carries the restriction to
`W = {p ∈ D(ℂ) | ι p ∈ O}` of `σ^*(u_ℰ) ∩ cl(X)` to `m · μ_B`. -/
theorem pushforward_restrict_zeroLocusOpens_eq_smul {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = dimension X) (σ : X ⟶ totalSpace E)
    [σ.IsOver (Spec (.of ℂ))] (hσ : σ ≫ proj E = 𝟙 X) (c : Chart E 1)
    {O : Opens (TopCat.of (UnderlyingSpace ℂ X))} (hOc : (O : Set _) ⊆ chartBase c)
    (hO : O ≤ regularOpens ℂ X) {B : Type} [TopologicalSpace B] [T2Space B] [ConnectedSpace B]
    [SecondCountableTopology B] [TopologicalSpace.MetrizableSpace B]
    [ChartedSpace (EuclideanSpace ℂ (Fin k)) B] {ε : ℝ} (hε : 0 < ε)
    (Φ : regularOpensInter (𝕜 := ℂ) O ≃ₜ ball (0 : ℂ) ε × B)
    (hΦ : letI := regularChartedSpace (𝕜 := ℂ) hn
      ∀ c ∈ atlas (EuclideanSpace ℂ (Fin (k + 1))) (regularOpensInter (𝕜 := ℂ) O),
        ∀ c' ∈ atlas (EuclideanSpace ℂ (Fin k)) B, ∀ x ∈ c.source, (Φ x).2 ∈ c'.source →
          ∃ L : EuclideanSpace ℂ (Fin (k + 1)) →L[ℂ] ℂ × EuclideanSpace ℂ (Fin k),
            Function.Injective L ∧
            HasFDerivAt (fun y ↦ (((Φ (c.symm y)).1 : ℂ), c' (Φ (c.symm y)).2)) L (c x))
    (m : ℕ)
    (hh : ∀ p : O, coord c (mapFun σ p.1) 0 = ballChartFst Φ (regularOpensInterMap hO p) ^ m)
    (hz : setInter (Y := TopCat.of (UnderlyingSpace ℂ X)) O (zeroLocusSet σ) =
      (regularOpensInterMap hO).hom ⁻¹' (ballChartFst Φ ⁻¹' {0}))
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X))
      (2 * (k + 1) : ℕ)} (hμ : IsVarietyFundamentalClass R hn μ)
    {μB : borelMooreHomology R (ModuleCat.of R R) (TopCat.of B) (2 * k : ℕ)}
    (hμB : IsFundamentalClass R (euclideanComplexOrientationBasis k) μB)
    (hdeg : ((2 * (k + 1) : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ) = ((2 * k : ℕ) : ℤ)) :
    (pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (((zeroLocusOpensHomeomorph σ O).trans
          (localZeroHomeomorph σ hO hε Φ hz)) :
            C(zeroLocusOpens σ O, B)))
        ((zeroLocusOpensHomeomorph σ O).trans
          (localZeroHomeomorph σ hO hε Φ hz)).isProperMap
        (2 * k : ℕ)).hom
      ((restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ (zeroLocus E σ).subscheme))
        (zeroLocusOpens σ O) (2 * k : ℕ)).hom
        ((pushforward R (ModuleCat.of R R) (zeroLocusInvHom σ)
          (isProperMap_zeroLocusInvHom σ) (2 * k : ℕ)).hom
          (congrDegree R _ hdeg (localizedTopChernCap σ R 1 _ μ)))) =
      (m : R) • μB := by
  rw [pushforward_homeomorph_trans_apply R, pushforward_zeroLocusOpensHomeomorph_restrict]
  exact pushforward_restrict_localizedTopChernCap_eq_smul R hn σ hσ c hOc hO hε Φ hΦ m hh hz hμ
    hμB hdeg

end Component

end MMP.Modules
