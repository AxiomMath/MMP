module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalAntiampleDivisor
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Divisor.AlgebraicHartogsUnits
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
import MMP.AlgebraicGeometry.Vanishing.EtaleKltAmpleGap
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness

/-!
# Pushing forward the full reduced floor of a log resolution

Let `(X, B)` be a rational `ℚ`-factorial projective complex dlt pair, or more generally an
effective rational `ℚ`-factorial projective lc pair for which `(X, B - δ⌊B⌋)` is klt for some
`δ > 0`, and let `p : W ⟶ X` be a projective log resolution. Write the crepant boundary as
`K_W + T + Γ = p^*(K_X + B)`, where `T` is the sum of *all* prime divisors of coefficient one,
exceptional or not, and every coefficient of `Γ` is less than one. Put `E = -⌊Γ⌋` and let
`S = ⌊B⌋` with its reduced structure. Then

* `p_* 𝒪_W(E - T) = ℐ_S` inside the rational functions, and `R^i p_* 𝒪_W(E - T) = 0` for
  `i > 0`; that is, `Rp_* 𝒪_W(E - T) = ℐ_S`;
* `p` maps the reduced scheme `T` into `S`, and the induced `q : T ⟶ S` satisfies
  `𝒪_S = q_* 𝒪_T` as sheaves of algebras; in particular `q` is proper, surjective and has
  connected fibres.

The second identity holds even when `p` extracts divisors of log discrepancy zero.

The proof runs as follows.

* **The dlt case.** On a `ℚ`-factorial variety `(X, B - ⌊B⌋)` is klt, so the dlt case is the
  second one. A prime `F` of `W` with `coeff_F B_W = 1` then has centre in `S`: otherwise, by the
  change-of-boundary formula for discrepancies, it would have discrepancy `-1` for
  `(X, B - δ⌊B⌋)` as well.
* **Degree zero.** `E` is effective and has no component over a prime divisor of `X`, so by
  algebraic Hartogs every section of `𝒪_W(E - T)` over `p⁻¹ U` is `p^♯ f` for a regular function
  `f` on `U`. Such an `f` vanishes along every component of `S`, and conversely a function in
  `ℐ_S` vanishes along every prime of `T`, its centre lying in `S`.
* **Higher direct images.** For an effective exceptional `J` with `-J` relatively ample
  (Kollár–Mori 2.62) and `N ≫ 0`, the boundary `Γ + E + J/N` is snc with coefficients `< 1`, so
  klt, and `(E - T) - (K_W + Γ + E + J/N) = -p^*(K_X + B) - J/N` is `p`-ample. The klt ample-gap
  vanishing theorem gives `R^i p_* 𝒪_W(E - T) = 0` for `i > 0`.
* **The structure sheaf of the floor.** The floor `T` maps onto `S`, so `q^♯ : 𝒪_S ⟶ q_* 𝒪_T` is
  injective. A function on `T ∩ p⁻¹ U` is, near each point of `U`, the image of a section of the
  cokernel `Q` of `𝒪_W(E - T) ⟶ 𝒪_W(E)`. Since `R¹p_* 𝒪_W(E - T) = 0`, `p_*` keeps
  `0 ⟶ 𝒪_W(E - T) ⟶ 𝒪_W(E) ⟶ Q ⟶ 0` exact, so that section lifts locally on `X` to `𝒪_W(E)`.
  By Hartogs again the lift is a function on `X`. Hence `q^♯` is locally surjective, and so it
  is an isomorphism. The fibres of the proper map `q` are then connected.

## Main results

* `MMP.Fourfold.IsLogResolution.bijOn_idealSheaf_divisorialSubmodule_and_pushforward_floor`.

## Implementation notes

The crepant boundary `B_W = T + Γ` is `MMP.Mori.IsCrepantBoundary`; `T` is pinned as the divisor
with coefficient one exactly at the primes where `B_W` has coefficient one, and `Γ = B_W - T`.
The ideal sheaf `ℐ_S` of the reduced closed subscheme `ι_S : S ⟶ X` is the kernel of `ι_S^♯`, and
`p_* 𝒪_W(E - T)` has sections `𝒪_W(E - T)(p⁻¹ U)` over `U`; the identity `p_* 𝒪_W(E - T) = ℐ_S`
is that `f ↦ p^♯ f`, followed by the inclusion `𝒪_W ⟶ 𝒦_W`, is a bijection from `ℐ_S(U)` onto
these sections, for every open `U ⊆ X`. The higher direct images are the right derived functors
of `Scheme.Modules.pushforward p`. The identity `𝒪_S = q_* 𝒪_T` of algebras is that
`q^♯ : 𝒪_S(U) ⟶ 𝒪_T(q⁻¹ U)` is an isomorphism for every open `U`. The two hypotheses on the pair
(dlt, or lc with `(X, B - δ⌊B⌋)` klt) enter as a disjunction.

The source identifies `p_* 𝒪_T(E)` with `𝒪_S` and factors `𝒪_S ⟶ p_* 𝒪_T ⟶ p_* 𝒪_T(E)`.
Here the surjectivity of `𝒪_S ⟶ q_* 𝒪_T` is proved directly: local functions on `T` lift
through the closed immersion to `W`, their classes in `Q` glue since a regular function vanishing
on `T` lies in `𝒪_W(E - T)`, and lifting through `p_* 𝒪_W(E) ⟶ p_* Q` and Hartogs give a
function on `X`, which restricts to the given function on `T`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], 2.37,
  2.62, 5.22
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

universe u

/-- A prime divisor whose generic point maps off the support of a Cartier divisor has
coefficient zero in its pull-back. -/
private theorem divisor_coeff_eq_zero_of_isPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {B : Divisor Y}
    (hBc : B.IsCartier) {hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B.supp}
    {B' : Divisor X} (h : B.IsPullback f hB B') (E : Mori.PrimeDivisor X)
    (hE : f E.genericPoint ∉ B.supp) : B'.coeff E = 0 := by
  obtain ⟨U, hU, φ, hφ⟩ := hBc (f E.genericPoint)
  have hEU : (E.support ∩ f ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff _).mp hU
  rw [h U φ hφ E hEU]
  have hsp : componentGenericPoint X E.component ⤳ E.genericPoint := E.specializes_genericPoint
  have hsp' : f (componentGenericPoint X E.component) ⤳ f E.genericPoint :=
    f.base.hom.map_specializes hsp
  set W := pointComponent (f (componentGenericPoint X E.component))
  have hW : f (componentGenericPoint X E.component) ∈ W.1 := mem_pointComponent _
  have hyW : f E.genericPoint ∈ W.1 :=
    hsp'.mem_closed (isClosed_of_mem_irreducibleComponents _ W.2) hW
  obtain ⟨c, hc⟩ := hφ.exists_unit_stalk hU hE hyW
  let c' : (Y.presheaf.stalk (f (componentGenericPoint X E.component)))ˣ :=
    Units.map (Y.presheaf.stalkSpecializes hsp').hom.toMonoidHom c
  have hc' : (stalkToRationalFunctions Y hW).hom c' = (φ : RationalFunctions Y) W := by
    rw [← hc]
    change (Y.presheaf.stalkSpecializes hsp' ≫ Y.presheaf.stalkSpecializes _).hom c.val =
      (Y.presheaf.stalkSpecializes _).hom c.val
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  rw [pullbackComponent_eq hB hφ _ hW c' hc']
  refine E.ordUnit_eq_zero_of_isUnit ((c.isUnit).map (f.stalkMap E.genericPoint).hom) ?_
  change (X.presheaf.stalkSpecializes _).hom ((f.stalkMap E.genericPoint).hom
    c.val) = (f.stalkMap _).hom ((Y.presheaf.stalkSpecializes hsp').hom c.val)
  rw [Scheme.Hom.stalkSpecializes_stalkMap_apply]

/-- The same for `ℚ`-divisors. -/
private theorem qdivisor_coeff_eq_zero_of_isPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {B : QDivisor Y}
    (hBq : B.IsQCartier)
    {hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B.supp}
    {B' : QDivisor X} (h : B.IsPullback f hB B') (E : Mori.PrimeDivisor X)
    (hE : f E.genericPoint ∉ B.supp) : B'.coeff E = 0 := by
  obtain ⟨m, hm, D, hD, hDc⟩ := hBq.exists_pos
  obtain ⟨D', hD', hp⟩ := h m hm D hD hDc
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have h0 := divisor_coeff_eq_zero_of_isPullback hDc hp E (by
    rwa [QDivisor.supp_eq_of_toQDivisor_eq hm' hD])
  have := congrArg (fun G : QDivisor X => G.coeff E) hD'
  simp only [Divisor.coeff_toQDivisor, h0, DivisorWithCoeffs.coeff_smul, Int.cast_zero] at this
  exact (smul_eq_zero.mp this.symm).resolve_left hm'

/-! ### Sections of `𝒪_W(E - T)` -/

/-- An integral scheme has the single irreducible component `univ`. -/
private theorem component_eq_univ {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ := by
  obtain ⟨Z, h⟩ := Z
  exact (irreducibleComponents_eq_singleton (X := Y) ▸ h : Z ∈ ({Set.univ} : Set (Set Y)))

/-- In an irreducible scheme the generic point lies in every nonempty open. -/
private theorem genericPoint_mem_opens {X : Scheme.{u}} [IrreducibleSpace X] {U : X.Opens}
    (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

/-- A specialization between equal points induces an isomorphism of stalks. -/
private theorem isIso_stalkSpecializes {X : Scheme.{u}} {x y : X} (hsp : x ⤳ y)
    (h : x = y) : IsIso (X.presheaf.stalkSpecializes hsp) := by
  subst h; simp only [TopCat.Presheaf.stalkSpecializes_refl]; infer_instance

/-- On an integral scheme the generic point of every irreducible component is the generic
point. -/
private theorem componentGenericPoint_eq {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z = genericPoint Y := by
  refine (isGenericPoint_componentGenericPoint Y Z).eq ?_
  rw [component_eq_univ Z]
  exact genericPoint_spec Y

/-- The valuation `v_P` is carried to `v_F` by a map of the factors of `𝒦` compatible with an
isomorphism `𝒪_{X,P} ≅ 𝒪_{Y,F}`. -/
private theorem valuation_map {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] (P : MMP.Mori.PrimeDivisor X) (F : MMP.Mori.PrimeDivisor Y)
    (φ : P.localRing ≃+* F.localRing)
    (T : X.presheaf.stalk (componentGenericPoint X P.component) →+*
      Y.presheaf.stalk (componentGenericPoint Y F.component))
    (hT : ∀ a, T (P.toComponent.hom a) = F.toComponent.hom (φ a))
    (x : X.presheaf.stalk (componentGenericPoint X P.component)) :
    F.valuation (T x) = P.valuation x := by
  let := P.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions P.genericPoint_mem_component
  have : Ring.KrullDimLE 1 P.localRing := krullDimLE_of_coheight_le P.coheight_genericPoint.le
  have := P.isDiscreteValuationRing_localRing
  let := F.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions F.genericPoint_mem_component
  have : Ring.KrullDimLE 1 F.localRing := krullDimLE_of_coheight_le F.coheight_genericPoint.le
  have := F.isDiscreteValuationRing_localRing
  let eP := IsLocalization.algEquiv (nonZeroDivisors P.localRing)
    (X.presheaf.stalk (componentGenericPoint X P.component)) (FractionRing P.localRing)
  let eF := IsLocalization.algEquiv (nonZeroDivisors F.localRing)
    (Y.presheaf.stalk (componentGenericPoint Y F.component)) (FractionRing F.localRing)
  change Ring.ordFrac F.localRing (eF (T x)) = Ring.ordFrac P.localRing (eP x)
  have key := MMP.Positivity.ordFrac_map_of_ringEquiv (K := FractionRing P.localRing)
    (K' := FractionRing F.localRing) φ
    ((eF.toRingEquiv.toRingHom.comp T).comp eP.symm.toRingEquiv.toRingHom) (fun r => by
      have h1 : eP.symm (algebraMap _ (FractionRing P.localRing) r) = P.toComponent.hom r :=
        eP.symm.commutes r
      have h2 : eF (F.toComponent.hom (φ r)) = algebraMap _ (FractionRing F.localRing) (φ r) :=
        eF.commutes (φ r)
      simp only [RingHom.coe_comp, Function.comp_apply]
      change eF (T (eP.symm (algebraMap _ (FractionRing P.localRing) r))) = _
      rw [h1, hT, h2]) (eP x)
  simpa using key

/-- **Sections with no poles along strict transforms come from the base.** Let `f : Y ⟶ X` be a
dominant morphism of normal integral schemes with `f^* : k(X) ≅ k(Y)`, `U ⊆ X` open and `D` a
divisor on `Y` such that every prime divisor `P` of `X` meeting `U` is dominated by a prime
divisor `F` of `Y`, with `f` inducing `𝒪_{X,P} ≅ 𝒪_{Y,F}` and `coeff_F D ≤ 0`. Then every
section of `𝒪_Y(D)` over `f⁻¹ U` is `f^♯ r` for a regular function `r` on `U`: `v_P(φ) = v_F(φ)
≥ 0` for every `P` meeting `U`, and algebraic Hartogs applies on `X`. -/
private theorem exists_app_eq_of_mem_divisorialSubmodule {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ X) [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) (D : Divisor Y)
    (U : X.Opens)
    (hD : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ U).Nonempty →
      ∃ F : MMP.Mori.PrimeDivisor Y,
        f F.genericPoint = P.genericPoint ∧ IsIso (f.stalkMap F.genericPoint) ∧ D.coeff F ≤ 0)
    (ψ : D.divisorialSubmodule (f ⁻¹ᵁ U)) :
    ∃ r : Γ(X, U), (toRationalFunctionsPresheaf Y).app (Opposite.op (f ⁻¹ᵁ U)) (f.app U r) =
      ψ.1 := by
  by_cases hU : (U : Set X).Nonempty
  swap
  · exact ⟨0, funext fun Z => (hU ⟨_, Z.2⟩).elim⟩
  have hfη : f (genericPoint Y) = genericPoint X := map_genericPoint_of_isDominant f
  have hηX : genericPoint X ∈ U := genericPoint_mem_opens hU
  have hηY : genericPoint Y ∈ f ⁻¹ᵁ U := show f _ ∈ U from hfη ▸ hηX
  obtain ⟨ZY, -⟩ := exists_mem_irreducibleComponents (genericPoint Y)
  obtain ⟨ZX, -⟩ := exists_mem_irreducibleComponents (genericPoint X)
  have hZYU : componentGenericPoint Y ZY ∈ f ⁻¹ᵁ U := by
    rwa [componentGenericPoint_eq]
  have hZXU : componentGenericPoint X ZX ∈ U := by
    rwa [componentGenericPoint_eq]
  have hsub : ∀ Z Z' : irreducibleComponents Y, Z = Z' := fun Z Z' =>
    Subtype.ext (by rw [component_eq_univ Z, component_eq_univ Z'])
  let Φ := RingEquiv.ofBijective (functionFieldMap f) hf
  let eX : ∀ Z : irreducibleComponents X,
      X.presheaf.stalk (componentGenericPoint X Z) ≃+* X.functionField := fun Z =>
    (X.presheaf.stalkCongr
      (Inseparable.of_eq (componentGenericPoint_eq Z).symm)).commRingCatIsoToRingEquiv.symm
  let eY : ∀ Z : irreducibleComponents Y,
      Y.presheaf.stalk (componentGenericPoint Y Z) ≃+* Y.functionField := fun Z =>
    (Y.presheaf.stalkCongr
      (Inseparable.of_eq (componentGenericPoint_eq Z).symm)).commRingCatIsoToRingEquiv.symm
  have heX : ∀ Z a, eX Z a = algebraMap _ X.functionField a := fun _ _ => rfl
  have heY : ∀ Z a, eY Z a = algebraMap _ Y.functionField a := fun _ _ => rfl
  let φX : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op U)) := fun Z =>
    (eX Z.1).symm (Φ.symm (eY ZY (ψ.1 ⟨ZY, hZYU⟩)))
  have hφX : (0 : Divisor X).IsDivisorialSection U φX := by
    intro P hP
    obtain ⟨F, hFP, hiso, hF0⟩ := hD P hP
    have hFU : (F.support ∩ (f ⁻¹ᵁ U : Set Y)).Nonempty := by
      refine ⟨F.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support F, ?_⟩
      · change f _ ∈ U
        rw [hFP]
        exact P.genericPoint_mem_of_nonempty hP
    have hψF := (ψ.2 F hFU).mono (show -(0 : Divisor X).coeff P ≤ -D.coeff F by
      rw [DivisorWithCoeffs.coeff_zero]; omega)
    obtain rfl := hsub ZY F.component
    have hsp : f F.genericPoint ⤳ P.genericPoint := hFP ▸ specializes_rfl
    have := isIso_stalkSpecializes hsp hFP
    let φ : P.localRing ≃+* F.localRing :=
      (asIso (X.presheaf.stalkSpecializes hsp ≫
        f.stalkMap F.genericPoint)).commRingCatIsoToRingEquiv
    let T : X.presheaf.stalk (componentGenericPoint X P.component) →+*
        Y.presheaf.stalk (componentGenericPoint Y F.component) :=
      (eY F.component).symm.toRingHom.comp (Φ.toRingHom.comp (eX P.component).toRingHom)
    have hTinj : Function.Injective T :=
      (eY F.component).symm.injective.comp (Φ.injective.comp (eX P.component).injective)
    have hT : ∀ b, T (P.toComponent.hom b) = F.toComponent.hom (φ b) := by
      intro b
      apply (eY F.component).injective
      simp only [T, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        RingEquiv.apply_symm_apply]
      rw [heX, heY]
      change Φ (algebraMap _ X.functionField ((X.presheaf.stalkSpecializes _).hom b)) =
        algebraMap _ Y.functionField ((Y.presheaf.stalkSpecializes _).hom
          ((f.stalkMap F.genericPoint).hom ((X.presheaf.stalkSpecializes hsp).hom b)))
      rw [MMP.Mori.algebraMap_stalkSpecializes, MMP.Mori.algebraMap_stalkSpecializes,
        ← functionFieldMap_algebraMap_stalk, MMP.Mori.algebraMap_stalkSpecializes]
      rfl
    have hTa : T (φX ⟨P.component, P.componentGenericPoint_mem_of_nonempty hP⟩) =
        ψ.1 ⟨F.component, F.componentGenericPoint_mem_of_nonempty hFU⟩ := by
      simp [T, φX]
    rcases hψF with h0 | hv
    · left
      exact hTinj (by rwa [hTa, map_zero])
    · right
      rw [← valuation_map P F φ T hT, hTa]
      simpa using hv
  obtain ⟨s, hs⟩ := hφX.exists_eq
  refine ⟨s, funext fun Z' => ?_⟩
  obtain rfl : Z' = ⟨ZY, hZYU⟩ := Subtype.ext (hsub _ _)
  rw [toRationalFunctionsPresheaf_app_apply]
  apply (eY ZY).injective
  have h1 := congrFun hs ⟨ZX, hZXU⟩
  rw [toRationalFunctionsPresheaf_app_apply] at h1
  have hsp : componentGenericPoint X ZX ⤳ f (componentGenericPoint Y ZY) :=
    (isGenericPoint_componentGenericPoint X ZX).specializes (by rw [component_eq_univ ZX]; trivial)
  have hR : (eY ZY) (ψ.1 ⟨ZY, hZYU⟩) = Φ (eX ZX (X.presheaf.germ U _ hZXU s)) := by
    rw [h1]
    simp [φX]
  have h2 : Y.presheaf.germ (f ⁻¹ᵁ U) (componentGenericPoint Y ZY) hZYU (f.app U s) =
      f.stalkMap _ (X.presheaf.germ U _ hZYU s) :=
    (Scheme.Hom.germ_stalkMap_apply f U _ hZYU s).symm
  rw [hR, heY, heX]
  erw [h2]
  rw [← functionFieldMap_algebraMap_stalk,
    ← TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hZYU hsp,
    MMP.Mori.algebraMap_stalkSpecializes]
  rfl

/-- For a proper birational morphism `g : Y ⟶ X` of integral schemes with `X` locally Noetherian
and normal, the generic point of every prime divisor `P` of `X` is the image of the generic point
of a prime divisor `F` of `Y` at which `g` induces an isomorphism of local rings. -/
private theorem exists_primeDivisor_map_genericPoint_eq {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] (g : Y ⟶ X) [IsProper g]
    (hg : IsBirationalMorphism g) (P : MMP.Mori.PrimeDivisor X) :
    ∃ F : MMP.Mori.PrimeDivisor Y,
      g F.genericPoint = P.genericPoint ∧ IsIso (g.stalkMap F.genericPoint) := by
  have : IsDominant g := hg.isDominant
  have hbij := hg.functionFieldMap_bijective
  obtain ⟨y, hy, hc, -, -⟩ :=
    MMP.Intersection.exists_preimage_of_coheight_eq_one g hbij P.coheight_genericPoint
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk
    P.coheight_genericPoint
  have hF : g (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hc).genericPoint =
      P.genericPoint := by
    rwa [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  have : ValuationRing (X.presheaf.stalk
      (g (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hc).genericPoint)) := by
    rw [hF]; infer_instance
  exact ⟨_, hF, MMP.Positivity.isIso_stalkMap_of_valuationRing g hbij _⟩

/-- In `ℤᵐ⁰`, a value `≥ 1` other than `1` is `≥ exp 1`. -/
private theorem exp_one_le_of_one_le_of_ne_one {v : WithZero (Multiplicative ℤ)} (h1 : 1 ≤ v)
    (h2 : v ≠ 1) : WithZero.exp 1 ≤ v := by
  induction v using WithZero.recZeroCoe with
  | zero => exact absurd h1 (by simp)
  | coe m =>
    rw [← WithZero.exp_log (WithZero.coe_ne_zero (a := m))] at h1 h2 ⊢
    rw [WithZero.exp_le_exp]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    have : WithZero.log (m : WithZero (Multiplicative ℤ)) ≠ 0 := fun h =>
      h2 (by rw [h, WithZero.exp_zero])
    omega

/-- A nonzero non-unit of the local ring `𝒪_{X,E}` vanishes along `E`: `v_E ≥ 1`. -/
private theorem exp_one_le_valuation_toComponent {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (E : MMP.Mori.PrimeDivisor X) {a : E.localRing} (ha : a ≠ 0) (hna : ¬ IsUnit a) :
    WithZero.exp 1 ≤ E.valuation (E.toComponent.hom a) := by
  let := E.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions E.genericPoint_mem_component
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le E.coheight_genericPoint.le
  have := E.isDiscreteValuationRing_localRing
  change WithZero.exp 1 ≤ Ring.ordFrac E.localRing (IsLocalization.algEquiv
    (nonZeroDivisors E.localRing) _ (FractionRing E.localRing) (algebraMap E.localRing _ a))
  rw [AlgEquiv.commutes]
  refine exp_one_le_of_one_le_of_ne_one (Ring.ordFrac_ge_one_of_ne_zero ha) fun h => hna ?_
  exact Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing.mpr h

/-- The component of `𝒪_X ⟶ 𝒦_X` along the component of a prime divisor `F` is the germ at
`η_F` followed by `𝒪_{X,F} ⟶ 𝒪_{X,η}`. -/
private theorem toRationalFunctionsPresheaf_app_component {Y : Scheme.{u}} {V : Y.Opens}
    (s : Γ(Y, V)) (F : MMP.Mori.PrimeDivisor Y) (hF : F.genericPoint ∈ V)
    (hc : componentGenericPoint Y F.component ∈ V) :
    (toRationalFunctionsPresheaf Y).app (Opposite.op V) s ⟨F.component, hc⟩ =
      F.toComponent.hom (Y.presheaf.germ V F.genericPoint hF s) :=
  (TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hF _ s).symm

/-- A section `s` with `η_F ∉ D(s)` has `v_F(s) ≥ 1`, and every section has `v_F ≥ 0`. -/
private theorem ordGE_toRationalFunctionsPresheaf {W : Scheme.{u}}
    [IsLocallyNoetherian W] [IsNormal W] {V : W.Opens} (s : Γ(W, V)) (F : MMP.Mori.PrimeDivisor W)
    (hF : (F.support ∩ (V : Set W)).Nonempty) (n : ℤ) (hn : n ≤ 1)
    (hn0 : 0 < n → F.genericPoint ∉ W.basicOpen s) :
    F.OrdGE n ((toRationalFunctionsPresheaf W).app (Opposite.op V) s
      ⟨F.component, F.componentGenericPoint_mem_of_nonempty hF⟩) := by
  have hη := F.genericPoint_mem_of_nonempty hF
  rw [toRationalFunctionsPresheaf_app_component _ F hη]
  set a := W.presheaf.germ V F.genericPoint hη s
  by_cases ha : a = 0
  · left; rw [ha, map_zero]
  right
  rcases le_or_gt n 0 with h0 | h0
  · exact (WithZero.exp_le_exp.mpr h0).trans (by
      simpa using F.one_le_valuation_toComponent ha)
  · have hn1 : n = 1 := by omega
    subst hn1
    exact exp_one_le_valuation_toComponent F ha fun hu =>
      hn0 h0 ((W.mem_basicOpen _ _ hη).mpr hu)

/-- A point of a prime divisor is a specialization of its generic point. -/
private theorem specializes_of_mem_support {Y : Scheme.{u}} (F : MMP.Mori.PrimeDivisor Y) {y : Y}
    (hy : y ∈ F.support) : F.genericPoint ⤳ y := by
  rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact hy

/-- **A section of `𝒪_W(D)` vanishes along the primes with `coeff D ≤ -1`.** If `r` is regular on
`V` and lies in `𝒪_W(D)`, then the generic point of every prime divisor `F` meeting `V` with
`coeff_F D ≤ -1` lies outside `D(r)`: there `r` would be a unit, of valuation `0 < 1`. -/
private theorem genericPoint_notMem_basicOpen_of_mem_divisorialSubmodule {W : Scheme.{u}}
    [IsLocallyNoetherian W] [IsNormal W] {D : Divisor W} {V : W.Opens} (r : Γ(W, V))
    (hr : (toRationalFunctionsPresheaf W).app (Opposite.op V) r ∈ D.divisorialSubmodule V)
    (F : MMP.Mori.PrimeDivisor W) (hFV : (F.support ∩ (V : Set W)).Nonempty)
    (hF : D.coeff F ≤ -1) : F.genericPoint ∉ W.basicOpen r := by
  intro hηB
  have hηF := F.genericPoint_mem_of_nonempty hFV
  have hunit : IsUnit (W.presheaf.germ V F.genericPoint hηF r) :=
    (W.mem_basicOpen _ _ hηF).mp hηB
  have hord := (hr F hFV).mono (show (1 : ℤ) ≤ -D.coeff F by omega)
  rw [toRationalFunctionsPresheaf_app_component _ F hηF] at hord
  rcases hord with h0 | hv
  · exact not_isUnit_zero (h0 ▸ hunit.map F.toComponent.hom)
  · rw [F.valuation_toComponent_of_isUnit hunit] at hv
    exact absurd hv (by decide)

/-- **`p_* 𝒪_W(D) = ℐ_S`.** Let `p : W ⟶ X` be a dominant morphism of normal integral schemes
inducing an isomorphism of function fields, `ι_S : S ⟶ X` a reduced closed subscheme with
`S ⊆ ⋃_{P ∈ Σ} P`, and `D` a divisor on `W` with coefficients `≥ -1`, such that the primes with
coefficient `-1` lie over `S`, and every prime divisor `P` of `X` is dominated by a prime divisor
`F` of `W` with `𝒪_{X,P} ≅ 𝒪_{W,F}` and `coeff_F D ≤ 0`, with `coeff_F D = -1` when `P ∈ Σ`.
Then `f ↦ p^♯ f` is a bijection from `ℐ_S(U) = ker ι_S^♯` onto `𝒪_W(D)(p⁻¹ U)`. -/
private theorem bijOn_idealSheaf_divisorialSubmodule {X W Sred : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (p : W ⟶ X) [IsDominant p] [QuasiCompact p] (hbij : Function.Bijective (functionFieldMap p))
    (ιS : Sred ⟶ X) [IsReduced Sred] (Pf : Set (MMP.Mori.PrimeDivisor X))
    (hS : Set.range ιS.base ⊆ ⋃ P ∈ Pf, (P.support : Set X)) (D : Divisor W)
    (h1 : ∀ F, -1 ≤ D.coeff F) (h2 : ∀ F, D.coeff F < 0 → p F.genericPoint ∈ Set.range ιS.base)
    (h3 : ∀ P : MMP.Mori.PrimeDivisor X, ∃ F : MMP.Mori.PrimeDivisor W,
      p F.genericPoint = P.genericPoint ∧ IsIso (p.stalkMap F.genericPoint) ∧ D.coeff F ≤ 0 ∧
        (P ∈ Pf → D.coeff F = -1))
    (U : X.Opens) :
    Set.BijOn (fun f => (toRationalFunctionsPresheaf W).app (Opposite.op (p ⁻¹ᵁ U)) (p.app U f))
      {f | ιS.app U f = 0} (D.divisorialSubmodule (p ⁻¹ᵁ U)) := by
  -- a function killed by `ι_S^♯` vanishes at every point of `S`
  have hvan : ∀ f : Γ(X, U), ιS.app U f = 0 → ∀ x ∈ Set.range ιS.base, x ∉ X.basicOpen f := by
    rintro f hf x ⟨s, rfl⟩ hx
    have : s ∈ ιS ⁻¹ᵁ X.basicOpen f := hx
    rw [Scheme.preimage_basicOpen, hf, Scheme.basicOpen_zero] at this
    exact this
  refine ⟨fun f hf F hF => ?_, ?_, fun ψ hψ => ?_⟩
  · -- `MapsTo`
    refine ordGE_toRationalFunctionsPresheaf _ F hF _ (by linarith [h1 F]) fun hpos hmem => ?_
    rw [← Scheme.preimage_basicOpen] at hmem
    exact hvan f hf _ (h2 F (by omega)) hmem
  · -- `InjOn`
    have : IsSchemeTheoreticallyDominant p := IsSchemeTheoreticallyDominant.of_isDominant p
    intro f _ g _ hfg
    exact Scheme.Hom.app_injective p U (toRationalFunctionsPresheaf_app_injective (p ⁻¹ᵁ U) hfg)
  · -- `SurjOn`
    obtain ⟨r, hr⟩ := exists_app_eq_of_mem_divisorialSubmodule p hbij D U
      (fun P _ => (h3 P).imp fun F hF => ⟨hF.1, hF.2.1, hF.2.2.1⟩) ⟨ψ, hψ⟩
    refine ⟨r, ?_, hr⟩
    change ιS.app U r = 0
    refine eq_zero_of_basicOpen_eq_bot _ ?_
    rw [← Scheme.preimage_basicOpen, eq_bot_iff]
    intro s hs
    exfalso
    change ιS s ∈ X.basicOpen r at hs
    obtain ⟨P, hPf, hsP⟩ := Set.mem_iUnion₂.mp (hS ⟨s, rfl⟩)
    obtain ⟨F, hFP, -, -, hF1⟩ := h3 P
    have hxU : ιS s ∈ U := X.basicOpen_le r hs
    have hPU : (P.support ∩ (U : Set X)).Nonempty := ⟨_, hsP, hxU⟩
    have hηP : P.genericPoint ∈ X.basicOpen r :=
      (specializes_of_mem_support P hsP).mem_open (X.basicOpen r).isOpen hs
    have hFU : (F.support ∩ (p ⁻¹ᵁ U : Set W)).Nonempty :=
      ⟨F.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support F, show p _ ∈ U by
        rw [hFP]; exact P.genericPoint_mem_of_nonempty hPU⟩
    have hr' : (toRationalFunctionsPresheaf W).app (Opposite.op (p ⁻¹ᵁ U)) (p.app U r) = ψ := hr
    refine genericPoint_notMem_basicOpen_of_mem_divisorialSubmodule (p.app U r) (hr' ▸ hψ) F hFU
      (hF1 hPf).le ?_
    rw [← Scheme.preimage_basicOpen]
    change p F.genericPoint ∈ X.basicOpen r
    rwa [hFP]

/-- A prime divisor mapped to the generic point of a prime divisor is not exceptional. -/
private theorem not_isExceptional_of_map_genericPoint {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] {f : X ⟶ Y} {P : MMP.Mori.PrimeDivisor X}
    {Q : MMP.Mori.PrimeDivisor Y} (h : f P.genericPoint = Q.genericPoint) :
    ¬ RationalMap.IsExceptional (X := X) f.toRationalMap P := by
  intro hex
  have h2 := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
    ((MMP.Positivity.isExceptional_toRationalMap_iff (f := f) P).mp hex) _ <|
      subset_closure ⟨P.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support P, h⟩
  rw [Q.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- **A `ℚ`-factorial dlt pair minus its floor is klt.** If `(X, B)` is dlt and `X` is
`ℚ`-factorial, then `(X, B - ⌊B⌋)` is klt. -/
private theorem isKltPair_sub_roundDown_of_isDltPair {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X}
    (hQ : MMP.Fourfold.IsQFactorial sX) (hdlt : MMP.Intersection.IsDltPair sX B) :
    MMP.Fourfold.IsKltPair sX (B - (1 : ℚ) • Divisor.toQDivisor B.roundDown) := by
  have hcoeff : ∀ P, (B - (1 : ℚ) • Divisor.toQDivisor B.roundDown).coeff P =
      Int.fract (B.coeff P) := fun P => by
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
      DivisorWithCoeffs.coeff_roundDown, smul_eq_mul, one_mul]
    exact Int.self_sub_floor _
  refine MMP.Intersection.IsDltPair.isKltPair_of_forall_coeff_lt_one
    (MMP.Intersection.IsDltPair.of_le sX hdlt (fun P => ?_) (fun P => ?_)
      (MMP.Fourfold.isQCartier_of_isQFactorial sX hQ _)) (fun P => ?_)
  · change (0 : ℚ) ≤ (B - (1 : ℚ) • Divisor.toQDivisor B.roundDown).coeff P
    rw [hcoeff]; exact Int.fract_nonneg _
  · change (B - (1 : ℚ) • Divisor.toQDivisor B.roundDown).coeff P ≤ B.coeff P
    rw [hcoeff]
    have h0 : (0 : ℚ) ≤ B.coeff P := hdlt.1.2.1 P
    rw [Int.fract]
    have : (0 : ℤ) ≤ ⌊B.coeff P⌋ := Int.floor_nonneg.mpr h0
    have : (0 : ℚ) ≤ (⌊B.coeff P⌋ : ℚ) := by exact_mod_cast this
    linarith
  · rw [hcoeff]; exact Int.fract_lt_one _

/-! ### The vanishing of the higher direct images -/

/-- `𝒪_Y(mA) ≅ 𝒪_Y(A)^{⊗ m}` for a Cartier divisor `A`. -/
private noncomputable def divisorialSheafNsmulIso {V : Scheme.{u}} [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] {A : Divisor V} (hA : A.IsCartier) (m : ℕ) :
    haveI := hA.isInvertibleModule_divisorialSheaf
    (m • A).divisorialSheaf ≅ Stacks.Ample.tensorPowModule V A.divisorialSheaf (m : ℤ) := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  induction m with
  | zero =>
    exact eqToIso (by rw [zero_smul]) ≪≫ Divisor.divisorialSheafZeroIso ≪≫
      (Stacks.Ample.tensorPowModuleZeroIso V A.divisorialSheaf).symm
  | succ n ih =>
    exact eqToIso (by rw [succ_nsmul]) ≪≫
      ((hA.nsmul n).divisorialSheafTensorIso hA).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso ih).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso V A.divisorialSheaf).symm ≪≫
      Stacks.Ample.tensorPowModuleAddIso V A.divisorialSheaf (n : ℤ) 1 ≪≫
      eqToIso (by push_cast; rfl)

open RingedSpaceModuleAdjunction in
/-- A positive multiple of an `f`-ample Cartier divisor is `f`-ample. -/
private theorem isRelativelyAmple_nsmul {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {f : X ⟶ Y} {L : Divisor X} (hL : L.IsCartier)
    (h : L.IsRelativelyAmple f hL) (n : ℕ) (hn : 0 < n) :
    (n • L).IsRelativelyAmple f (hL.nsmul n) := by
  have := hL.isInvertibleModule_divisorialSheaf
  have := (hL.nsmul n).isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, hA⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  have e0 := divisorialSheafNsmulIso hL n
  have := Stacks.Ample.isInvertibleModule_tensorPowModule (f ⁻¹ᵁ V).toScheme
    ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L.divisorialSheaf) (n : ℤ)
  let e := (modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e0 ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (f ⁻¹ᵁ V).ι _ n
  rw [Stacks.RelativeVeryAmple.isAmple_congr _ _ e]
  exact (Stacks.AmplePositivePower.isAmple_iff_isAmple_tensorPowModule _ n hn).1 hA

/-- A `ℚ`-divisor whose prime components lie in an snc divisor is snc. -/
private theorem isSNC_of_subset {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFinitePresentation sY] (hsm : IsSmoothScheme sY) {S : TopologicalSpace.Closeds Y}
    (hS : IsSNCSubset sY S) {E : QDivisor Y}
    (hE : ∀ P : MMP.Mori.PrimeDivisor Y, E P ≠ 0 → (P.support : Set Y) ⊆ S) : E.IsSNC sY := by
  classical
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · refine (DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℤ) sY hsm).of_support_subset ?_
    intro P hP
    exact absurd (hE P (Finsupp.mem_support_iff.mp hP)
      (MMP.Flips.primeDivisor_genericPoint_mem_support P)) (by simp)
  · refine hsnc.of_support_subset ?_
    intro P hP
    obtain ⟨F, hFs, hPF⟩ :=
      MMP.Fourfold.SNCWeight.PrimeDivisorUnion.exists_subset_of_isIrreducible (s := s)
        (A := fun F : MMP.Mori.PrimeDivisor Y => (F.support : Set Y))
        (fun F _ => MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support F)
        (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isIrreducible_support P)
        (by rw [hs]; exact hE P (Finsupp.mem_support_iff.mp hP))
    rw [MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset hPF,
      Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply, hFs]

/-- **A small perturbation stays below one.** If `g i < 1` for all `i` and `d` vanishes off a
finite set, then `g i + d i / N < 1` for all `i` once `N` is large. -/
private theorem exists_nat_add_inv_mul_lt_one {ι : Type*} (s : Finset ι) {g d : ι → ℚ}
    (hg : ∀ i, g i < 1) (hd : ∀ i ∉ s, d i = 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, g i + (N : ℚ)⁻¹ * d i < 1 := by
  have h : ∀ i ∈ s, ∀ᶠ N : ℕ in Filter.atTop, g i + (N : ℚ)⁻¹ * d i < 1 := fun i _ => by
    have : Filter.Tendsto (fun N : ℕ => g i + (N : ℚ)⁻¹ * d i) Filter.atTop (nhds (g i)) := by
      simpa using tendsto_const_nhds.add (tendsto_inv_atTop_nhds_zero_nat.mul_const (d i))
    exact this.eventually (gt_mem_nhds (hg i))
  obtain ⟨N, hN, hN0⟩ :=
    (((Filter.eventually_all_finset s).2 h).and (Filter.eventually_gt_atTop 0)).exists
  refine ⟨N, hN0, fun i => ?_⟩
  by_cases hi : i ∈ s
  · exact hN i hi
  · simpa [hd i hi] using hg i

/-- On a smooth birational model `f : Y ⟶ X`, the pull-back `f^*ω` of a rational `n`-form with
canonical divisor `div ω` has canonical divisor. -/
private theorem isCanonicalDivisor_divisorOfForm_pullback {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {f : Y ⟶ X} [IsDominant f] [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety ℂ (f ≫ sX))
    (hf : IsBirationalMorphism f) (hYsm : IsSmoothScheme (f ≫ sX)) :
    (divisorOfForm (pullbackRationalPluriForms sX f ω)).IsCanonicalDivisor (f ≫ sX) n := by
  have hn := hK.topologicalKrullDim_eq
  have : AlgebraicGeometry.IsVariety ℂ sX := hX.1
  have : AlgebraicGeometry.IsVariety ℂ (f ≫ sX) := hY.1
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hYsm
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hf).symm.trans hn)
  exact hK₀.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀
      (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f
        hf.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn) hω0)

/-- **The higher direct images of `𝒪_W(E - T)` vanish.** With `B_W` the crepant boundary of the
pair `(X, B)` on a projective log resolution `p : W ⟶ X`, `T` the sum of the primes of coefficient
one, `Γ = B_W - T` and `E = -⌊Γ⌋`, we have `R^i p_* 𝒪_W(E - T) = 0` for `i > 0`: for an
effective exceptional `J` with `-J` `p`-ample (Kollár–Mori 2.62) and `N ≫ 0` the pair
`(W, Γ + E + J/N)` is snc klt, and `(E - T) - (K_W + Γ + E + J/N) = -p^*(K_X + B) - J/N` is
`p`-ample. -/
private theorem isZero_rightDerived_pushforward_divisorialSheaf
    {X W : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    [IsSeparated (X ↘ Limits.terminal Scheme)]
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : QDivisor X} (hX : IsNormalVariety ℂ sX) (hproj : Mori.IsProjectiveVariety ℂ sX)
    (hQ : MMP.Fourfold.IsQFactorial sX) (hPw : IsPairWith sX n K B)
    {p : W ⟶ X} (hp : MMP.Fourfold.IsLogResolution sX B p) [IsProper p] [IsDominant p]
    (hW : IsNormalVariety ℂ (p ≫ sX)) {BW : QDivisor W}
    (hcrep : IsCrepantBoundary sX n K B p hW hp.isBirationalMorphism BW)
    {T : Divisor W} (hT : ∀ F, T.coeff F = if BW.coeff F = 1 then 1 else 0)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward p).rightDerived i).obj
      (-(BW - Divisor.toQDivisor T).roundDown - T).divisorialSheaf) := by
  classical
  have hpb : IsBirationalMorphism p := hp.isBirationalMorphism
  have hsm : IsSmoothScheme (p ≫ sX) := hp.isSmoothScheme
  have : AlgebraicGeometry.IsVariety ℂ sX := hX.1
  have : AlgebraicGeometry.IsVariety ℂ (p ≫ sX) := hW.1
  have : LocallyOfFinitePresentation (p ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := p ≫ sX)).mpr inferInstance
  have hcart : ∀ D : Divisor W, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  -- the canonical divisors `K = div ω` and `K_W = div p^*ω`
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hKω : divisorOfForm ω = K := DivisorWithCoeffs.ext' hωK
  set KW : Divisor W := divisorOfForm (pullbackRationalPluriForms sX p ω) with hKWdef
  have hKW : KW.IsCanonicalDivisor (p ≫ sX) n :=
    isCanonicalDivisor_divisorOfForm_pullback hX hω0 (hKω ▸ hK) hW hpb hsm
  -- the crepant identity `K_W + B_W = p^*(K_X + B)`
  have hQKB : (Divisor.toQDivisor (divisorOfForm ω) + B).IsQCartier := hKω ▸ hPw.2.2
  set PKB : QDivisor W := QDivisor.pullback (f := p) _ hQKB
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier p hQKB) with hPKBdef
  have hcr : ∀ F, BW.coeff F = PKB.coeff F - (KW.coeff F : ℚ) := by
    intro F
    have h1 := isDiscrepancy_coeff_divisorOfForm_sub_pullback hX ω hω0 (hKω ▸ hK) B hQKB p hW
      hpb F
    have h2 := hcrep F
    rw [← hKω] at h2
    have := IsDiscrepancy.eq h1 h2
    rw [DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor] at this
    linarith
  -- a Cartier multiple `C = m₀(K_X + B)` and its pull-back `C' = m₀ p^*(K_X + B)`
  obtain ⟨m₀, hm₀, C, hCq, hCc⟩ := hQKB.exists_pos
  obtain ⟨C', hC'q, hC'pb⟩ := QDivisor.isPullback_pullback (f := p) hQKB
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier p hQKB) m₀ hm₀ C hCq hCc
  -- an effective exceptional `J = D_J` with `-J` relatively ample
  obtain ⟨FJ, e, he, hFJ0, hFJexc, DJ, hDJc, hDJq, hDJamp⟩ :=
    exists_isRelativelyAmple_neg_smul_of_isExceptional sX (p ≫ sX) hQ hW p rfl
      hp.isProjectiveMorphism hpb
  have hDJF : ∀ F, (DJ.coeff F : ℚ) = e * FJ.coeff F := fun F => by
    simpa using congrArg (fun G : QDivisor W => G.coeff F) hDJq
  have hDJ0 : ∀ F, (0 : ℚ) ≤ (DJ.coeff F : ℚ) := fun F => by
    rw [hDJF]; exact mul_nonneg (by positivity) (hFJ0 F)
  have hDJexc : ∀ F, DJ.coeff F ≠ 0 → RationalMap.IsExceptional (X := W) p.toRationalMap F :=
    fun F hF => hFJexc F fun h0 => hF <| by
      rw [← DivisorWithCoeffs.coeff_apply] at h0
      have h0' : (DJ.coeff F : ℚ) = 0 := (hDJF F).trans (by rw [h0, mul_zero])
      exact_mod_cast h0'
  -- the fractional part `G = Γ + E` of the crepant boundary
  set Γ : QDivisor W := BW - Divisor.toQDivisor T with hΓdef
  set G : QDivisor W := Γ + Divisor.toQDivisor (-Γ.roundDown) with hGdef
  have hG : ∀ F, G.coeff F = Int.fract (Γ.coeff F) := fun F => by
    rw [hGdef, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor,
      DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_roundDown, Int.cast_neg,
      ← sub_eq_add_neg]
    exact Int.self_sub_floor _
  -- `N ≫ 0`
  obtain ⟨N, hN, hNb⟩ := exists_nat_add_inv_mul_lt_one DJ.support (g := G.coeff)
    (d := fun F => (DJ.coeff F : ℚ)) (fun F => hG F ▸ Int.fract_lt_one _)
    (fun F hF => by
      have h := Finsupp.notMem_support_iff.mp hF
      rw [← DivisorWithCoeffs.coeff_apply] at h
      exact_mod_cast h)
  set B₀ : QDivisor W := G + (N : ℚ)⁻¹ • Divisor.toQDivisor DJ with hB₀def
  have hB₀ : ∀ F, B₀.coeff F = G.coeff F + (N : ℚ)⁻¹ * (DJ.coeff F : ℚ) := fun F => by
    rw [hB₀def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toQDivisor, smul_eq_mul]
  have hB₀0 : 0 ≤ B₀ := fun F => by
    change (0 : ℚ) ≤ B₀.coeff F
    rw [hB₀, hG]
    exact add_nonneg (Int.fract_nonneg _) (mul_nonneg (by positivity) (hDJ0 F))
  -- `(W, B₀)` is snc klt
  have hsnc : B₀.IsSNC (p ≫ sX) := by
    refine isSNC_of_subset hsm hp.isSNCSubset fun F hF x hx => ?_
    change B₀.coeff F ≠ 0 at hF
    by_cases hexc : RationalMap.IsExceptional (X := W) p.toRationalMap F
    · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet F hexc hx)
    · right
      have hDJF : DJ.coeff F = 0 := by
        by_contra h; exact hexc (hDJexc F h)
      obtain ⟨P, hc, hη, -⟩ := exists_coeff_eq_of_not_isExceptional hPw hW hpb hcrep
        (G := F) hexc
      have hBP : B.coeff P ≠ 0 := by
        intro h0
        apply hF
        rw [hB₀, hDJF, Int.cast_zero, mul_zero, add_zero, hG, hΓdef,
          DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor, hT F, hc, h0]
        simp
      change p x ∈ (QDivisor.toRDivisor B).supp
      refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, by simpa using hBP, ?_⟩
      have hsp : F.genericPoint ⤳ x := specializes_of_mem_support F hx
      exact (hsp.map p.base.hom.continuous).mem_closed
        (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support P)
        (hη ▸ MMP.Flips.primeDivisor_genericPoint_mem_support P)
  have hcoeff : ∀ F, B₀.coeff F < 1 := fun F => by rw [hB₀]; exact hNb F
  have hklt : Mori.IsKltPair (p ≫ sX) n KW B₀ := isKltPair_of_isSNC (p ≫ sX) hW hsm hKW hsnc hcoeff
  -- the divisors `L = E - T`, `M = -m₀ J - N C'` and `D = m L - M`
  set L : Divisor W := -Γ.roundDown - T with hLdef
  set m : ℕ := m₀ * N with hmdef
  have hm : 0 < m := Nat.mul_pos hm₀ hN
  set M : Divisor W := m₀ • (-DJ) + (-(N : ℤ)) • C' with hMdef
  set Dk : Divisor W := m • L - M with hDkdef
  have hC'q' : Divisor.toQDivisor C' = (m₀ : ℤ) • PKB := hC'q
  have hDk : Divisor.toQDivisor Dk = (m : ℚ) • (Divisor.toQDivisor KW + B₀) := by
    ext F
    have hC'F : (C'.coeff F : ℚ) = (m₀ : ℚ) * PKB.coeff F := by
      have := congrArg (fun G : QDivisor W => G.coeff F) hC'q'
      simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
      rw [this]; push_cast; ring
    rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toQDivisor, hB₀, hG, smul_eq_mul]
    simp only [hDkdef, hMdef, hLdef, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_roundDown,
      smul_eq_mul, nsmul_eq_mul, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, hmdef, Nat.cast_mul]
    have hfr := Int.self_sub_floor (Γ.coeff F)
    have hΓF : Γ.coeff F = BW.coeff F - (T.coeff F : ℚ) := by
      rw [hΓdef, DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor]
    rw [hcr F] at hΓF
    rw [← hfr, hΓF]
    have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    rw [hC'F]
    ring
  -- `𝒪_W(M)` is `p`-ample
  have hamp1 : (m₀ • (-DJ)).IsRelativelyAmple p (hDJc.neg.nsmul m₀) :=
    isRelativelyAmple_nsmul hDJc.neg hDJamp m₀ hm₀
  have hNC : ((-(N : ℤ)) • C).IsPullback p
      (fun Z hZ => (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant'
        p ((-(N : ℤ)) • C)) Z hZ) ((-(N : ℤ)) • C') :=
    hC'pb.zsmul hCc (-(N : ℤ)) _
  have hamp : M.IsRelativelyAmple p (hcart M) :=
    MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback p _ hamp1 (hCc.zsmul _) hNC
      (hcart _)
  -- the isomorphism `𝒪_W(L)^{⊗ m} ≅ 𝒪_W(D) ⊗ 𝒪_W(M)`
  have := (hcart L).isInvertibleModule_divisorialSheaf
  have := (hcart M).isInvertibleModule_divisorialSheaf
  have eiso : Stacks.Ample.tensorPowModule W L.divisorialSheaf (m : ℤ) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback (𝟙 W)).obj Dk.divisorialSheaf)).obj M.divisorialSheaf :=
    (divisorialSheafNsmulIso (hcart L) m).symm ≪≫
      eqToIso (congrArg Divisor.divisorialSheaf (show m • L = Dk + M by
        rw [hDkdef, sub_add_cancel])) ≪≫
      ((hcart Dk).divisorialSheafTensorIso (hcart M)).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).mapIso
          ((Scheme.Modules.pullbackId W).app Dk.divisorialSheaf).symm).app _
  -- the klt ample-gap vanishing
  have : AlgebraicGeometry.IsProjectiveVariety ℂ (p ≫ sX) :=
    { toIsVariety := hW.1
      isProjective := hp.isProjectiveMorphism.comp hproj.isProjective }
  exact isZero_rightDerived_pushforward_of_isPullback_etale_of_isKltPair (p ≫ sX) hklt hB₀0 sX p
    rfl hp.isProjectiveMorphism.isProjective (𝟙 X) (𝟙 W) p IsPullback.of_id_fst
    L.divisorialSheaf m hm Dk (hcart Dk) hDk M.divisorialSheaf hamp eiso i hi

/-! ### The structure sheaf of the floor -/

/-- **Exactness on sections.** For a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of
`𝒪_X`-modules, a section of `M₂` over `V` killed by `M₂ ⟶ M₃` comes from `M₁`. -/
private theorem exists_app_eq_of_app_eq_zero {X : Scheme.{0}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) {V : X.Opens} (h : Γ(S.X₂, V)) (hh : S.g.app V h = 0) :
    ∃ d, S.f.app V d = h := by
  let F : X.Modules ⥤ Ab := Scheme.Modules.toPresheaf X ⋙
    (evaluation (TopologicalSpace.Opens X)ᵒᵖ Ab).obj (Opposite.op V)
  have : PreservesFiniteLimits (Scheme.Modules.toPresheaf X) := inferInstance
  have : PreservesFiniteLimits
      ((evaluation (TopologicalSpace.Opens X)ᵒᵖ Ab).obj (Opposite.op V)) := inferInstance
  have hF : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have : F.Additive := ⟨fun {_ _ _ _} => rfl⟩
  have htfae : ∀ T : ShortComplex X.Modules, T.ShortExact → (T.map F).Exact ∧ Mono (F.map T.f) :=
    ((Functor.preservesFiniteLimits_tfae F).out 1 4).mpr hF
  have hex := (htfae S hS).1
  rw [ShortComplex.ab_exact_iff] at hex
  exact hex h hh

/-- **Local lifting through a quotient with `R¹p_* = 0`.** If `ι : M ⟶ N` is a monomorphism of
`𝒪_W`-modules with `R¹p_* M = 0`, every section of `coker ι` over `p⁻¹ U₀` lifts, near every
point of `U₀`, to a section of `N`. -/
private theorem exists_app_eq_map_of_isZero_rightDerived {X W : Scheme.{0}}
    (p : W ⟶ X) {M N : W.Modules} (ι : M ⟶ N) [Mono ι]
    (hvan : IsZero (((Scheme.Modules.pushforward p).rightDerived 1).obj M))
    (U₀ : X.Opens) (σ : Γ(cokernel ι, p ⁻¹ᵁ U₀)) (x : X) (hx : x ∈ U₀) :
    ∃ (U₁ : X.Opens) (h : U₁ ≤ U₀), x ∈ U₁ ∧ ∃ a : Γ(N, p ⁻¹ᵁ U₁),
      (cokernel.π ι).app _ a = (cokernel ι).presheaf.map (homOfLE (p.preimage_mono h)).op σ := by
  let S : ShortComplex W.Modules := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel ι)) inferInstance inferInstance
  have hS' := Stacks.Cohomology.shortExact_map_of_isZero_rightDerived_one
    (Scheme.Modules.pushforward p) hS hvan
  have hloc := @Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi _ _ _ _ _ _ _ _
    ((Scheme.Modules.pushforward p).map (cokernel.π ι)) hS'.epi_g
  have hloc' : TopCat.Presheaf.IsLocallySurjective
      ((PresheafOfModules.toPresheaf _).map
        ((Scheme.Modules.pushforward p).map (cokernel.π ι)).val) :=
    ⟨hloc.imageSieve_mem⟩
  obtain ⟨U₁, hU₁, ⟨a, ha⟩, hxU₁⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp hloc' U₀ σ x hx
  exact ⟨U₁, hU₁, hxU₁, a, ha⟩

/-- Morphisms of `𝒪_X`-modules commute with restriction of sections. -/
private theorem hom_app_map {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens}
    (i : V ⟶ U) (a : Γ(M, U)) : N.presheaf.map i.op (φ.app U a) = φ.app V (M.presheaf.map i.op a) :=
  (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) a).symm

/-- `f^♯` commutes with restriction of sections. -/
private theorem scheme_hom_app_map {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : Y.Opens} (i : V ⟶ U)
    (a : Γ(Y, U)) :
    f.app V (Y.presheaf.map i.op a) =
      X.presheaf.map (homOfLE (f.preimage_mono i.le)).op (f.app U a) :=
  ConcreteCategory.congr_hom (f.naturality i.op) a

/-- **Functions on `T` lift locally to `X`.** Let `p : W ⟶ X` and `ι_T : T ⟶ W` a closed
immersion, `D ≤ E` divisors on `W` with `E ≥ 0`, such that the sections of `𝒪_W(E)` over `p⁻¹ U`
are the functions on `U` (`hHartogs`), and a regular function lies in `𝒪_W(D)` exactly when it
vanishes on `T` (`hL1`, `hL2`). If `R¹p_* 𝒪_W(D) = 0`, then every function on `T ∩ p⁻¹ U₀` is,
near each point of `U₀`, the restriction to `T` of a function on `X`: push forward
`0 ⟶ 𝒪_W(D) ⟶ 𝒪_W(E) ⟶ Q ⟶ 0`. -/
private theorem exists_app_eq_restrict_of_isZero_rightDerived {X W Tred : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] (p : W ⟶ X)
    (ιT : Tred ⟶ W) [IsClosedImmersion ιT]
    (D E : Divisor W) (hDE : D ≤ E) (hE0 : 0 ≤ E)
    (hHartogs : ∀ (U₁ : X.Opens) (ψ : E.divisorialSubmodule (p ⁻¹ᵁ U₁)), ∃ f : Γ(X, U₁),
      (toRationalFunctionsPresheaf W).app (Opposite.op (p ⁻¹ᵁ U₁)) (p.app U₁ f) = ψ.1)
    (hL1 : ∀ (V : W.Opens) (r : Γ(W, V)),
      (toRationalFunctionsPresheaf W).app (Opposite.op V) r ∈ D.divisorialSubmodule V →
        ιT.app V r = 0)
    (hL2 : ∀ (V : W.Opens) (r : Γ(W, V)), ιT.app V r = 0 →
      (toRationalFunctionsPresheaf W).app (Opposite.op V) r ∈ D.divisorialSubmodule V)
    (hvan : IsZero (((Scheme.Modules.pushforward p).rightDerived 1).obj D.divisorialSheaf))
    (U₀ : X.Opens) (t : Γ(Tred, ιT ⁻¹ᵁ (p ⁻¹ᵁ U₀))) (x : X) (hx : x ∈ U₀) :
    ∃ (U₁ : X.Opens) (h : U₁ ≤ U₀), x ∈ U₁ ∧ ∃ f : Γ(X, U₁),
      ιT.app (p ⁻¹ᵁ U₁) (p.app U₁ f) =
        Tred.presheaf.map (homOfLE (ιT.preimage_mono (p.preimage_mono h))).op t := by
  classical
  let ι : D.divisorialSheaf ⟶ E.divisorialSheaf := Divisor.divisorialSheafInclusion hDE
  let S : ShortComplex W.Modules := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel ι)) inferInstance inferInstance
  let secE : ∀ V : W.Opens, Γ(W, V) → Γ(E.divisorialSheaf, V) := fun V r =>
    (⟨(toRationalFunctionsPresheaf W).app (Opposite.op V) r,
      Divisor.isDivisorialSection_algebraMap hE0 r⟩ : E.divisorialSubmodule V)
  have hres : ∀ {U V : W.Opens} (i : V ⟶ U) (r : Γ(W, U)),
      E.divisorialSheaf.presheaf.map i.op (secE U r) = secE V (W.presheaf.map i.op r) :=
    fun i r => Subtype.ext (toRationalFunctionsPresheaf_app_map i r).symm
  have hsub : ∀ (V : W.Opens) (r r' : Γ(W, V)), secE V (r - r') = secE V r - secE V r' :=
    fun V r r' => Subtype.ext (map_sub _ r r')
  have hkill : ∀ (V : W.Opens) (r : Γ(W, V)), ιT.app V r = 0 →
      (cokernel.π ι).app V (secE V r) = 0 := by
    intro V r hr
    let d : Γ(D.divisorialSheaf, V) := (⟨_, hL2 V r hr⟩ : D.divisorialSubmodule V)
    have hd : secE V r = ι.app V d := Subtype.ext rfl
    rw [hd]
    change (Scheme.Modules.Hom.app (ι ≫ cokernel.π ι) V) d = 0
    rw [cokernel.condition]
    rfl
  have hdetect : ∀ (V : W.Opens) (r : Γ(W, V)), (cokernel.π ι).app V (secE V r) = 0 →
      ιT.app V r = 0 := by
    intro V r hr
    obtain ⟨d, hd⟩ := exists_app_eq_of_app_eq_zero hS (secE V r) hr
    refine hL1 V r ?_
    have : (toRationalFunctionsPresheaf W).app (Opposite.op V) r =
        (d : D.divisorialSubmodule V).1 := (congrArg Subtype.val hd).symm
    rw [this]; exact d.2
  -- local lifts of `t` through `ι_T^♯`
  have hlift : ∀ w : W, w ∈ p ⁻¹ᵁ U₀ → ∃ (V : W.Opens) (hV : V ≤ p ⁻¹ᵁ U₀), w ∈ V ∧
      ∃ g : Γ(W, V), ιT.app V g = Tred.presheaf.map (homOfLE (ιT.preimage_mono hV)).op t := by
    intro w hw
    obtain ⟨_, ⟨V, hV, rfl⟩, hwV, hVle⟩ :=
      W.isBasis_affineOpens.exists_subset_of_mem_open hw (p ⁻¹ᵁ U₀).2
    obtain ⟨g, hg⟩ := ιT.app_surjective V hV
      (Tred.presheaf.map (homOfLE (ιT.preimage_mono hVle)).op t)
    exact ⟨V, hVle, hwV, g, hg⟩
  choose V hV hwV g hg using hlift
  let Q := cokernel ι
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := ⟨Q.presheaf, Q.isSheaf⟩)
    (fun w : (p ⁻¹ᵁ U₀ : Set W) => V w.1 w.2) (p ⁻¹ᵁ U₀) (fun w => homOfLE (hV w.1 w.2))
    (fun w hw => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨w, hw⟩, hwV w hw⟩)
    (fun w => (cokernel.π ι).app _ (secE _ (g w.1 w.2))) (by
      intro i j
      change Q.presheaf.map _ _ = Q.presheaf.map _ _
      rw [hom_app_map, hom_app_map, hres, hres, ← sub_eq_zero, ← map_sub, ← hsub]
      refine hkill _ _ ?_
      rw [map_sub, scheme_hom_app_map, scheme_hom_app_map, hg, hg, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      exact sub_eq_zero.mpr rfl)
  -- lift `σ` near `x` to `𝒪_W(E)`, then to `𝒪_X` by Hartogs
  have hσ' : ∀ i : (p ⁻¹ᵁ U₀ : Set W), (cokernel ι).presheaf.map (homOfLE (hV i.1 i.2)).op σ =
      (cokernel.π ι).app _ (secE _ (g i.1 i.2)) := hσ
  obtain ⟨U₁, hU₁, hxU₁, a, ha⟩ := exists_app_eq_map_of_isZero_rightDerived p ι hvan U₀ σ x hx
  obtain ⟨f, hf⟩ := hHartogs U₁ a
  have haf : a = secE _ (p.app U₁ f) := Subtype.ext hf.symm
  refine ⟨U₁, hU₁, hxU₁, f, ?_⟩
  refine TopCat.Presheaf.section_ext Tred.sheaf _ _ _ fun y hy => ?_
  have hw0 : ιT y ∈ p ⁻¹ᵁ U₀ := p.preimage_mono hU₁ hy
  set w := ιT y
  let V' : W.Opens := V w hw0 ⊓ p ⁻¹ᵁ U₁
  have hyV' : y ∈ ιT ⁻¹ᵁ V' := ⟨hwV w hw0, hy⟩
  change Tred.presheaf.germ _ y hy _ = Tred.presheaf.germ _ y hy _
  rw [← TopCat.Presheaf.germ_res_apply Tred.presheaf
      (homOfLE (ιT.preimage_mono (inf_le_right : V' ≤ p ⁻¹ᵁ U₁))) y hyV',
    ← TopCat.Presheaf.germ_res_apply Tred.presheaf
      (homOfLE (ιT.preimage_mono (inf_le_right : V' ≤ p ⁻¹ᵁ U₁))) y hyV']
  congr 1
  -- the two restrictions to `ι_T⁻¹ V'` agree
  have hzero : ιT.app V' (W.presheaf.map (homOfLE (inf_le_right : V' ≤ p ⁻¹ᵁ U₁)).op (p.app U₁ f) -
      W.presheaf.map (homOfLE (inf_le_left : V' ≤ V w hw0)).op (g w hw0)) = 0 := by
    refine hdetect _ _ ?_
    rw [hsub, map_sub, ← hres, ← hres, ← haf, ← hom_app_map, ← hom_app_map, ha, ← hσ' ⟨w, hw0⟩,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    exact sub_eq_zero.mpr rfl
  rw [map_sub, sub_eq_zero, scheme_hom_app_map, scheme_hom_app_map, hg] at hzero
  rw [hzero, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  rfl

/-- A regular function lying in `𝒪_W(D)`, where every point of the reduced closed subscheme
`T` lies on a prime divisor with `coeff D ≤ -1`, vanishes on `T`. -/
private theorem app_eq_zero_of_mem_divisorialSubmodule {W Tred : Scheme.{u}}
    [IsLocallyNoetherian W] [IsNormal W] (ιT : Tred ⟶ W) [IsReduced Tred] (D : Divisor W)
    (hT : ∀ y : Tred, ∃ F : MMP.Mori.PrimeDivisor W, ιT y ∈ F.support ∧ D.coeff F ≤ -1)
    {V : W.Opens} (r : Γ(W, V))
    (hr : (toRationalFunctionsPresheaf W).app (Opposite.op V) r ∈ D.divisorialSubmodule V) :
    ιT.app V r = 0 := by
  refine eq_zero_of_basicOpen_eq_bot _ ?_
  rw [← Scheme.preimage_basicOpen, eq_bot_iff]
  intro y hy
  exfalso
  change ιT y ∈ W.basicOpen r at hy
  obtain ⟨F, hyF, hF⟩ := hT y
  exact genericPoint_notMem_basicOpen_of_mem_divisorialSubmodule r hr F
    ⟨_, hyF, W.basicOpen_le r hy⟩ hF ((specializes_of_mem_support F hyF).mem_open
      (W.basicOpen r).isOpen hy)

/-- A regular function vanishing on a closed subscheme `T` that contains the generic point of
every prime divisor with negative coefficient in `D ≥ -1` lies in `𝒪_W(D)`. -/
private theorem mem_divisorialSubmodule_of_app_eq_zero {W Tred : Scheme.{u}}
    [IsLocallyNoetherian W] [IsNormal W] (ιT : Tred ⟶ W) (D : Divisor W)
    (h1 : ∀ F, -1 ≤ D.coeff F) (h2 : ∀ F, D.coeff F < 0 → F.genericPoint ∈ Set.range ιT.base)
    {V : W.Opens} (r : Γ(W, V)) (hr : ιT.app V r = 0) :
    (toRationalFunctionsPresheaf W).app (Opposite.op V) r ∈ D.divisorialSubmodule V := by
  intro F hF
  refine ordGE_toRationalFunctionsPresheaf r F hF _ (by linarith [h1 F]) fun hpos => ?_
  obtain ⟨y, hy⟩ := h2 F (by omega)
  intro hmem
  have : y ∈ ιT ⁻¹ᵁ W.basicOpen r := by
    change ιT y ∈ W.basicOpen r; rw [hy]; exact hmem
  rw [Scheme.preimage_basicOpen, hr, Scheme.basicOpen_zero] at this
  exact this

/-- A surjective morphism to a reduced scheme is injective on sections. -/
private theorem injective_app_of_surjective {Y Z : Scheme.{u}} (q : Y ⟶ Z) [IsReduced Z]
    (hq : Function.Surjective q.base) (U : Z.Opens) : Function.Injective (q.app U) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine eq_zero_of_basicOpen_eq_bot _ ?_
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨y, rfl⟩ := hq z
  have : y ∈ q ⁻¹ᵁ Z.basicOpen s := hz
  rw [Scheme.preimage_basicOpen, hs, Scheme.basicOpen_zero] at this
  exact this

/-- A morphism of schemes injective on sections and locally surjective on sections is bijective
on sections. -/
private theorem isIso_app_of_injective_of_locally {Y Z : Scheme.{0}} (q : Y ⟶ Z)
    (hinj : ∀ U, Function.Injective (q.app U))
    (hloc : ∀ (U : Z.Opens) (t : Γ(Y, q ⁻¹ᵁ U)) (z : Z), z ∈ U → ∃ (V : Z.Opens) (hV : V ≤ U),
      z ∈ V ∧ ∃ s : Γ(Z, V), q.app V s = Y.presheaf.map (homOfLE (q.preimage_mono hV)).op t)
    (U : Z.Opens) : IsIso (q.app U) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨hinj U, fun t => ?_⟩
  choose V hV hzV s hs using hloc U t
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' Z.sheaf
    (fun z : (U : Set Z) => V z.1 z.2) U (fun z => homOfLE (hV z.1 z.2))
    (fun z hz => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzV z hz⟩)
    (fun z => s z.1 z.2) (by
      intro i j
      apply hinj
      change q.app _ (Z.presheaf.map _ _) = q.app _ (Z.presheaf.map _ _)
      rw [scheme_hom_app_map, scheme_hom_app_map, hs, hs, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      rfl)
  let g' : Γ(Z, U) := g
  have hg' : ∀ z : (U : Set Z), Z.presheaf.map (homOfLE (hV z.1 z.2)).op g' = s z.1 z.2 := hg
  refine ⟨g', TopCat.Presheaf.section_ext Y.sheaf _ _ _ fun y hy => ?_⟩
  have hy0 : q y ∈ U := hy
  have hyV : y ∈ q ⁻¹ᵁ V (q y) hy0 := hzV (q y) hy0
  change Y.presheaf.germ _ y hy _ = Y.presheaf.germ _ y hy _
  rw [← TopCat.Presheaf.germ_res_apply Y.presheaf
      (homOfLE (q.preimage_mono (hV (q y) hy0))) y hyV,
    ← TopCat.Presheaf.germ_res_apply Y.presheaf
      (homOfLE (q.preimage_mono (hV (q y) hy0))) y hyV]
  congr 1
  rw [← scheme_hom_app_map, hg' ⟨q y, hy0⟩, hs]

/-- **Zero places have centre in the floor.** Let `(X, B)` be a pair such that `(X, B - δ⌊B⌋)` is
klt, on a `ℚ`-factorial normal variety, and let `B_W` be the crepant boundary of `(X, B)` on a
proper birational model `p : W ⟶ X`. If a prime divisor `F` of `W` has `coeff_F B_W = 1`, then
`p(η_F)` lies on a component of `⌊B⌋`. -/
private theorem exists_mem_roundDown_support_of_coeff_eq_one
    {X W : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hK : K.IsCanonicalDivisor sX n)
    (hPw : IsPairWith sX n K B) (hQ : MMP.Fourfold.IsQFactorial sX) {δ : ℚ}
    (hklt : MMP.Fourfold.IsKltPair sX (B - δ • Divisor.toQDivisor B.roundDown))
    {p : W ⟶ X} [IsProper p] (hW : IsNormalVariety ℂ (p ≫ sX)) (hpb : IsBirationalMorphism p)
    {BW : QDivisor W} (hcrep : IsCrepantBoundary sX n K B p hW hpb BW) (F : Mori.PrimeDivisor W)
    (hF : BW.coeff F = 1) :
    ∃ P ∈ B.roundDown.support, p F.genericPoint ∈ P.support := by
  by_contra hcon
  push Not at hcon
  set Fo : DivisorOver ℂ sX := ⟨W, p, hW, hpb, F⟩
  have ha : IsDiscrepancy sX n K B Fo (-1) := by simpa [hF] using hcrep F
  by_cases hexc : Fo.IsExceptional
  · have hS' := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ (Divisor.toQDivisor B.roundDown)
    obtain ⟨-, hsupp, hall⟩ := IsPairWith.isDiscrepancy_add_smul_iff hPw hS' Fo
    have hpull := QDivisor.isPullback_pullback (f := p) hS' hsupp
    have h0 : (QDivisor.pullback (Divisor.toQDivisor B.roundDown) hS' hsupp).coeff F = 0 := by
      refine qdivisor_coeff_eq_zero_of_isPullback hS' hpull F fun hmem => ?_
      obtain ⟨P, hP, hPF⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
      refine hcon P ?_ hPF
      rw [Finsupp.mem_support_iff]
      rw [Divisor.coeff_toQDivisor] at hP
      exact_mod_cast hP
    have hd := ((hall _ hpull).2 (-δ) (-1)).mpr ha
    rw [h0, mul_zero, sub_zero, neg_smul, ← sub_eq_add_neg] at hd
    have hk := (MMP.Fourfold.isKltPair_iff_mori_isKltPair sX hK hklt.1).mp hklt
    have h1 := discrep_le hexc hd
    have h2 : (((-1 : ℚ) : ℝ) : EReal) = -1 := by norm_num
    rw [h2] at h1
    exact lt_irrefl _ (hk.2.1.trans_le h1)
  · obtain ⟨P, hc, hη, -⟩ := exists_coeff_eq_of_not_isExceptional hPw hW hpb hcrep hexc
    refine hcon P ?_ ?_
    · rw [Finsupp.mem_support_iff]
      change (B.roundDown.coeff P) ≠ 0
      rw [DivisorWithCoeffs.coeff_roundDown, ← hc, hF]
      norm_num
    · rw [hη]
      exact MMP.Flips.primeDivisor_genericPoint_mem_support P

/-- **The full reduced floor of a log resolution pushes forward to the floor.** Let `(X, B)` be a
rational `ℚ`-factorial projective complex pair which is dlt (`MMP.Intersection.IsDltPair`), or
log canonical (`MMP.Intersection.IsLogCanonicalPair`) with `(X, B - δ⌊B⌋)` klt
(`MMP.Fourfold.IsKltPair`) for some `δ > 0`, and `p : W ⟶ X` a projective log resolution
(`MMP.Fourfold.IsLogResolution`). Let `B_W` be the crepant boundary
(`MMP.Mori.IsCrepantBoundary`), `K_W + B_W = p^*(K_X + B)`, `T` the sum of the primes of
coefficient one in `B_W`, `Γ = B_W - T` with all coefficients below one, and `E = -⌊Γ⌋`. Let
`ι_S : S ⟶ X` and `ι_T : T ⟶ W` be the reduced closed subschemes on `⌊B⌋` and on `T`. Then
* for every open `U ⊆ X`, `f ↦ p^♯ f` is a bijection from the sections of the ideal sheaf
  `ℐ_S = ker ι_S^♯` over `U` onto the sections of `𝒪_W(E - T)` over `p⁻¹ U`;
* `R^i p_* 𝒪_W(E - T) = 0` for every `i > 0`;
* there is `q : T ⟶ S` with `q ≫ ι_S = ι_T ≫ p`, and every such `q` has `q^♯ : 𝒪_S ⟶ q_* 𝒪_T`
  an isomorphism, is proper and surjective, and has connected fibres. -/
@[mmp "lem_fourfold_all_zero_floor_resolution_pushforward"]
public theorem IsLogResolution.bijOn_idealSheaf_divisorialSubmodule_and_pushforward_floor
    {X W : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {n : ℕ} (_hdim : topologicalKrullDim X = n) {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : QDivisor X} (hproj : Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hB : MMP.Intersection.IsDltPair sX B ∨
      (MMP.Intersection.IsLogCanonicalPair sX B ∧
        ∃ δ : ℚ, 0 < δ ∧ IsKltPair sX (B - δ • Divisor.toQDivisor B.roundDown)))
    {p : W ⟶ X} (hp : IsLogResolution sX B p) {BW : QDivisor W}
    (hBW : ∃ hW : IsNormalVariety ℂ (p ≫ sX),
      IsCrepantBoundary sX n K B p hW hp.isBirationalMorphism BW)
    {T : Divisor W} (hT : ∀ F, T.coeff F = if BW.coeff F = 1 then 1 else 0)
    (hΓ : ∀ F, (BW - Divisor.toQDivisor T).coeff F < 1)
    {Sred Tred : Scheme.{0}} (ιS : Sred ⟶ X) (ιT : Tred ⟶ W)
    [IsClosedImmersion ιS] [IsReduced Sred] [IsClosedImmersion ιT] [IsReduced Tred]
    (hS : Set.range ιS.base = ⋃ P ∈ B.roundDown.support, (P.support : Set X))
    (hTred : Set.range ιT.base = ⋃ F ∈ T.support, (F.support : Set W)) :
    (∀ U : X.Opens,
      Set.BijOn (fun f => (toRationalFunctionsPresheaf W).app (Opposite.op (p ⁻¹ᵁ U)) (p.app U f))
        {f | ιS.app U f = 0}
        ((-(BW - Divisor.toQDivisor T).roundDown - T).divisorialSubmodule (p ⁻¹ᵁ U))) ∧
    (∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward p).rightDerived i).obj
      (-(BW - Divisor.toQDivisor T).roundDown - T).divisorialSheaf)) ∧
    (∃ q : Tred ⟶ Sred, q ≫ ιS = ιT ≫ p) ∧
    ∀ q : Tred ⟶ Sred, q ≫ ιS = ιT ≫ p →
      (∀ U : Sred.Opens, IsIso (q.app U)) ∧ IsProper q ∧ Function.Surjective q.base ∧
        ∀ s : Sred, _root_.IsConnected (q.base ⁻¹' {s}) := by
  classical
  obtain ⟨hW, hcrep⟩ := hBW
  have hpb : IsBirationalMorphism p := hp.isBirationalMorphism
  have : IsProper p := hp.isProper
  have : IsDominant p := hpb.isDominant
  have hlc : MMP.Intersection.IsLogCanonicalPair sX B := hB.elim (fun h => h.1) (fun h => h.1)
  obtain ⟨⟨hX, n', K', hK', hQ'⟩, hBnn, -⟩ := hlc
  have : CompactSpace X := by
    have := hX.1
    exact QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace W := by
    have := hW.1
    exact QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  have : IsSeparated (X ↘ Limits.terminal Scheme) := by
    have := hX.1
    rw [show X ↘ Limits.terminal Scheme = sX ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hPw : IsPairWith sX n K B := ⟨hX, hK, hQ'.add_of_linearlyEquivalent
    (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK' hK)⟩
  obtain ⟨δ, -, hklt⟩ : ∃ δ : ℚ, 0 < δ ∧
      MMP.Fourfold.IsKltPair sX (B - δ • Divisor.toQDivisor B.roundDown) := by
    rcases hB with hdlt | ⟨-, h⟩
    · exact ⟨1, one_pos, isKltPair_sub_roundDown_of_isDltPair hQ hdlt⟩
    · exact h
  -- the coefficients of the crepant boundary
  have hΓF : ∀ F, (BW - Divisor.toQDivisor T).coeff F =
      if BW.coeff F = 1 then 0 else BW.coeff F := fun F => by
    rw [DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor, hT F]
    split_ifs with h <;> simp [h]
  have hBW1 : ∀ F, BW.coeff F ≤ 1 := fun F => by
    have := hΓF F ▸ hΓ F
    split_ifs at this with h
    · exact h.le
    · exact this.le
  set D : Divisor W := -(BW - Divisor.toQDivisor T).roundDown - T with hDdef
  have hD : ∀ F, D.coeff F = if BW.coeff F = 1 then -1 else -⌊BW.coeff F⌋ := fun F => by
    rw [hDdef, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_neg,
      DivisorWithCoeffs.coeff_roundDown, hΓF F, hT F]
    split_ifs with h <;> simp
  set E' : Divisor W := -(BW - Divisor.toQDivisor T).roundDown with hE'def
  have hE'F : ∀ F, E'.coeff F = if BW.coeff F = 1 then 0 else -⌊BW.coeff F⌋ := fun F => by
    rw [hE'def, DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_roundDown, hΓF F]
    split_ifs <;> simp
  have hT0 : 0 ≤ T := fun F => by
    change (0 : ℤ) ≤ T.coeff F
    rw [hT F]; split_ifs <;> norm_num
  have hDE : D ≤ E' := by rw [hDdef]; exact sub_le_self _ hT0
  have hTF : ∀ F, F ∈ T.support ↔ BW.coeff F = 1 := fun F => by
    rw [Finsupp.mem_support_iff]
    change T.coeff F ≠ 0 ↔ _
    rw [hT F]
    split_ifs with h <;> simp [h]
  have hfl : ∀ F, BW.coeff F ≠ 1 → ⌊BW.coeff F⌋ ≤ 0 := fun F h => by
    have := Int.floor_lt.mpr (show BW.coeff F < ((1 : ℤ) : ℚ) by
      exact_mod_cast lt_of_le_of_ne (hBW1 F) h)
    omega
  have hD1 : ∀ F, -1 ≤ D.coeff F := fun F => by
    rw [hD F]
    split_ifs with h
    · exact le_rfl
    · linarith [hfl F h]
  have hDneg : ∀ F, D.coeff F < 0 → BW.coeff F = 1 := fun F hF => by
    by_contra h
    simp only [hD F, h, ↓reduceIte] at hF
    linarith [hfl F h]
  have hE0 : 0 ≤ E' := fun F => by
    change (0 : ℤ) ≤ E'.coeff F
    rw [hE'F F]
    split_ifs with h
    · exact le_rfl
    · linarith [hfl F h]
  have hcentre := exists_mem_roundDown_support_of_coeff_eq_one hK hPw hQ hklt hW hpb hcrep
  have hnonexc : ∀ P : Mori.PrimeDivisor X, ∃ F : Mori.PrimeDivisor W,
      p F.genericPoint = P.genericPoint ∧ IsIso (p.stalkMap F.genericPoint) ∧
        BW.coeff F = B.coeff P := by
    intro P
    obtain ⟨F, hFP, hiso⟩ := exists_primeDivisor_map_genericPoint_eq p hpb P
    have hexc : ¬ (⟨W, p, hW, hpb, F⟩ : DivisorOver ℂ sX).IsExceptional :=
      not_isExceptional_of_map_genericPoint hFP
    obtain ⟨P', hc, hη, -⟩ := exists_coeff_eq_of_not_isExceptional hPw hW hpb hcrep hexc
    have : P' = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hη.symm.trans hFP)
    exact ⟨F, hFP, hiso, this ▸ hc⟩
  have hE'P : ∀ P F, BW.coeff F = B.coeff P → E'.coeff F = 0 := fun P F hc => by
    rw [hE'F F]
    split_ifs with h
    · rfl
    · simp [Int.floor_eq_zero_iff.mpr ⟨hc ▸ hBnn P, lt_of_le_of_ne (hBW1 F) h⟩]
  have hfloor : ∀ P ∈ B.roundDown.support, B.coeff P = 1 := by
    intro P hP
    rw [Finsupp.mem_support_iff] at hP
    change B.roundDown.coeff P ≠ 0 at hP
    rw [DivisorWithCoeffs.coeff_roundDown] at hP
    obtain ⟨F, -, -, hF⟩ := hnonexc P
    have h1 : B.coeff P ≤ 1 := hF ▸ hBW1 F
    have h0 := hBnn P
    by_contra hne
    exact hP (Int.floor_eq_zero_iff.mpr ⟨h0, lt_of_le_of_ne h1 hne⟩)
  have hrangeS : Set.range ιS.base ⊆ ⋃ P ∈ (↑B.roundDown.support : Set (Mori.PrimeDivisor X)),
      (P.support : Set X) := by
    rw [hS]; intro x hx; simpa using hx
  have hA : ∀ U : X.Opens,
      Set.BijOn (fun f => (toRationalFunctionsPresheaf W).app (Opposite.op (p ⁻¹ᵁ U)) (p.app U f))
        {f | ιS.app U f = 0} (D.divisorialSubmodule (p ⁻¹ᵁ U)) := by
    refine bijOn_idealSheaf_divisorialSubmodule p hpb.functionFieldMap_bijective ιS _ hrangeS D
      hD1 (fun F hF => ?_) (fun P => ?_)
    · obtain ⟨P, hP, hmem⟩ := hcentre F (hDneg F hF)
      rw [hS]; exact Set.mem_iUnion₂.mpr ⟨P, hP, hmem⟩
    · obtain ⟨F, hFP, hiso, hc⟩ := hnonexc P
      exact ⟨F, hFP, hiso, (hDE F).trans (hE'P P F hc).le,
        fun hP => by simp [hD F, hc.trans (hfloor P hP)]⟩
  -- the vanishing of the higher direct images
  have hB' : ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward p).rightDerived i).obj
      D.divisorialSheaf) := fun i hi =>
    isZero_rightDerived_pushforward_divisorialSheaf hK hX hproj hQ hPw hp hW hcrep hT i hi
  -- the floor of `W` maps into the floor of `X`
  have hrangeT : Set.range (ιT ≫ p).base ⊆ Set.range ιS.base := by
    rintro _ ⟨t, rfl⟩
    have ht : ιT t ∈ Set.range ιT.base := ⟨t, rfl⟩
    rw [hTred] at ht
    obtain ⟨F, hF, htF⟩ := Set.mem_iUnion₂.mp ht
    obtain ⟨P, hP, hmem⟩ := hcentre F ((hTF F).mp hF)
    have hsp : F.genericPoint ⤳ ιT t := specializes_of_mem_support F htF
    have hx : p (ιT t) ∈ P.support := (hsp.map p.base.hom.continuous).mem_closed
      (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support P) hmem
    rw [hS]
    exact Set.mem_iUnion₂.mpr ⟨P, hP, by simpa using hx⟩
  refine ⟨hA, hB', ⟨IsClosedImmersion.lift ιS (ιT ≫ p) ?_, IsClosedImmersion.lift_fac _ _ _⟩,
    fun q hq => ?_⟩
  · rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range (ιT ≫ p),
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro x hx
    change x ∈ (ιS.ker.support : Set X)
    rw [Scheme.Hom.support_ker]
    exact closure_mono hrangeT hx
  have : IsProper (q ≫ ιS) := by
    rw [hq]
    infer_instance
  have : IsProper q := IsProper.of_comp q ιS
  have hsurj : Function.Surjective q.base := by
    intro s
    have hs : ιS s ∈ Set.range ιS.base := ⟨s, rfl⟩
    rw [hS] at hs
    obtain ⟨P, hP, hsP⟩ := Set.mem_iUnion₂.mp hs
    obtain ⟨F, hFP, -, hc⟩ := hnonexc P
    have hF1 : BW.coeff F = 1 := hc.trans (hfloor P hP)
    have hcl : IsClosed (p.base '' (F.support : Set W)) :=
      p.isClosedMap _ (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support F)
    have hxim : ιS s ∈ p.base '' (F.support : Set W) := by
      have hsub : closure {P.genericPoint} ⊆ p.base '' (F.support : Set W) :=
        hcl.closure_subset_iff.mpr (by
          rintro _ rfl
          exact ⟨F.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support F, hFP⟩)
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hsP
      exact hsub hsP
    obtain ⟨w, hwF, hw⟩ := hxim
    have hwT : w ∈ Set.range ιT.base := by
      rw [hTred]
      exact Set.mem_iUnion₂.mpr ⟨F, (hTF F).mpr hF1, hwF⟩
    obtain ⟨t, rfl⟩ := hwT
    refine ⟨t, ιS.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply, hw]
  -- `𝒪_S ⟶ q_* 𝒪_T` is an isomorphism
  have hHartogs : ∀ (U₁ : X.Opens) (ψ : E'.divisorialSubmodule (p ⁻¹ᵁ U₁)), ∃ f : Γ(X, U₁),
      (toRationalFunctionsPresheaf W).app (Opposite.op (p ⁻¹ᵁ U₁)) (p.app U₁ f) = ψ.1 := by
    intro U₁ ψ
    refine exists_app_eq_of_mem_divisorialSubmodule p hpb.functionFieldMap_bijective E' U₁
      (fun P _ => ?_) ψ
    obtain ⟨F, hFP, hiso, hc⟩ := hnonexc P
    exact ⟨F, hFP, hiso, (hE'P P F hc).le⟩
  have hL1 : ∀ (V : W.Opens) (r : Γ(W, V)),
      (toRationalFunctionsPresheaf W).app (Opposite.op V) r ∈ D.divisorialSubmodule V →
        ιT.app V r = 0 := fun V r hr =>
    app_eq_zero_of_mem_divisorialSubmodule ιT D (fun y => by
      have hy : ιT y ∈ Set.range ιT.base := ⟨y, rfl⟩
      rw [hTred] at hy
      obtain ⟨F, hF, hyF⟩ := Set.mem_iUnion₂.mp hy
      exact ⟨F, hyF, by simp [hD F, (hTF F).mp hF]⟩) r hr
  have hL2 : ∀ (V : W.Opens) (r : Γ(W, V)), ιT.app V r = 0 →
      (toRationalFunctionsPresheaf W).app (Opposite.op V) r ∈ D.divisorialSubmodule V :=
    fun V r hr => mem_divisorialSubmodule_of_app_eq_zero ιT D hD1 (fun F hF => by
      rw [hTred]
      exact Set.mem_iUnion₂.mpr ⟨F, (hTF F).mpr (hDneg F hF),
        MMP.Flips.primeDivisor_genericPoint_mem_support F⟩) r hr
  have hiso : ∀ U : Sred.Opens, IsIso (q.app U) := by
    refine isIso_app_of_injective_of_locally q (injective_app_of_surjective q hsurj) ?_
    intro V t s hs
    obtain ⟨U₀, rfl⟩ : ∃ U₀ : X.Opens, ιS ⁻¹ᵁ U₀ = V := by
      obtain ⟨t', ht', heq⟩ := ιS.isClosedEmbedding.isInducing.isOpen_iff.mp V.2
      exact ⟨⟨t', ht'⟩, TopologicalSpace.Opens.ext heq⟩
    have hle : ιT ⁻¹ᵁ (p ⁻¹ᵁ U₀) ≤ q ⁻¹ᵁ (ιS ⁻¹ᵁ U₀) := by
      intro y hy
      change ιS (q y) ∈ U₀
      rw [← Scheme.Hom.comp_apply, hq]
      exact hy
    obtain ⟨U₁, hU₁, hxU₁, f, hf⟩ := exists_app_eq_restrict_of_isZero_rightDerived p ιT D E'
      hDE hE0 hHartogs hL1 hL2 (hB' 1 one_pos) U₀ (Tred.presheaf.map (homOfLE hle).op t)
      (ιS s) hs
    refine ⟨ιS ⁻¹ᵁ U₁, ιS.preimage_mono hU₁, hxU₁, ιS.app U₁ f, ?_⟩
    refine TopCat.Presheaf.section_ext Tred.sheaf _ _ _ fun y hy => ?_
    change Tred.presheaf.germ _ y hy _ = Tred.presheaf.germ _ y hy _
    have hy1 : (q ≫ ιS) y ∈ U₁ := hy
    have hy' : (ιT ≫ p) y ∈ U₁ := by rwa [← hq]
    have hyB : y ∈ ιT ⁻¹ᵁ (p ⁻¹ᵁ U₁) := hy'
    have hgen : ∀ (φ ψ : Tred ⟶ X), φ = ψ → ∀ (h1 : φ y ∈ U₁) (h2 : ψ y ∈ U₁),
        φ.stalkMap y (X.presheaf.germ U₁ (φ y) h1 f) =
          ψ.stalkMap y (X.presheaf.germ U₁ (ψ y) h2 f) := by
      rintro φ _ rfl h1 h2; rfl
    have e1 : Tred.presheaf.germ _ y hy (q.app (ιS ⁻¹ᵁ U₁) (ιS.app U₁ f)) =
        (q ≫ ιS).stalkMap y (X.presheaf.germ U₁ ((q ≫ ιS) y) hy1 f) := by
      rw [Scheme.Hom.germ_stalkMap_apply]
      rfl
    have e2 : Tred.presheaf.germ (ιT ⁻¹ᵁ (p ⁻¹ᵁ U₁)) y hyB (ιT.app (p ⁻¹ᵁ U₁) (p.app U₁ f)) =
        (ιT ≫ p).stalkMap y (X.presheaf.germ U₁ ((ιT ≫ p) y) hy' f) := by
      rw [Scheme.Hom.germ_stalkMap_apply]
      rfl
    rw [e1, hgen _ _ hq hy1 hy', ← e2, hf]
    simp only [TopCat.Presheaf.germ_res_apply]
  refine ⟨hiso, inferInstance, hsurj, fun s => ?_⟩
  have : ∀ U, IsIso (q.c.app U) := fun U => hiso U.unop
  have : IsIso q.c := NatIso.isIso_of_isIso_app q.c
  have hr : Set.range (q.fiberι s).base = q.base ⁻¹' {s} := Scheme.Hom.range_fiberι q s
  obtain ⟨t, ht⟩ := hsurj s
  obtain ⟨x, -⟩ : t ∈ Set.range (q.fiberι s).base := by rwa [hr]
  have : Nonempty (q.fiber s) := ⟨x⟩
  have := Stacks.AlgebraicGeometry.connectedSpace_fiber_of_extendsOverNeighbourhood q s
    inferInstance fun e he => Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper
      q s e he
  rw [← hr]
  exact isConnected_range (q.fiberι s).base.hom.continuous

end MMP.Fourfold
