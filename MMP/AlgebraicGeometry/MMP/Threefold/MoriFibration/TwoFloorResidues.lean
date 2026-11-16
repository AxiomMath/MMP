module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Fourfold.GraphDivisor
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.MMP.Threefold.MoriFibration.VerticalPrimeDivisors
import MMP.AlgebraicGeometry.MMP.MinimalModel.DltModification
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Divisor.AlgebraicHartogsUnits
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Morphisms.GenericallyFinite
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.Divisor.ExceptionalNullDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.LowerDimDltModel
import MMP.AlgebraicGeometry.Analytic.Surface.BirationalTopFormEigenvalue
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeCartier
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.MMP.Contraction.RelativeLineBundleDescent
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.ResidueField
import MMP.AlgebraicGeometry.FiberSpace.NumericallyTrivialDescent
import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.ProjectiveLine
import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.ProjectiveLineProperties
import MMP.AlgebraicGeometry.Singularities.Semismooth.Basic
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre

/-!
# Exact crepant residue identifications for a two-floor threefold Mori curve fibration

Let `r : Y ⟶ V` be a contraction of a `ℚ`-factorial projective threefold onto a projective
surface with `ρ(Y/V) = 1` and `-(K_Y + Γ)` relatively ample for some klt boundary `Γ`. Let `B` be
an lc boundary with `D = K_Y + B` numerically trivial over `V`, such that `(Y, B - ε⌊B⌋)` is klt
for some `ε > 0`, and whose horizontal floor (the coefficient-one components dominating `V`) has
degree two on the generic fibre of `r`.

The generic fibre is a genus-zero curve over `k(V)` on which the horizontal floor is a reduced
divisor `{0, ∞}` of degree two; the logarithmic form `dz/z` is intrinsic up to sign, so its even
powers descend over `k(V)`. Multiplying by the pull-back of a rational pluricanonical form `ω` on
`V` gives a rational `m`-canonical form `α` on `Y` with `div(α) + mB = r^*M` for a Cartier
divisor `M` on `V`, whose Poincaré residue along every horizontal floor branch of a crepant dlt
model is the pull-back of the same `ω`. Consequently two degree-one branches are identified by a
crepant birational map over `V`, and a degree-two branch carries a nontrivial crepant birational
involution over `V`.

## Main results

* `MMP.Fourfold.IsContraction.exists_isPoincareResidue_of_floor_degree_eq_two`.

## Implementation notes

The degree of the horizontal floor on the generic fibre is `∑_P [κ(η_P) : κ(r(η_P))]` over the
prime divisors `P` of coefficient one in `B` with `r(P) = V`: the generic fibre of `P` over `V`
is the closed point `η_P` of the generic fibre of `r`, with residue field `κ(η_P)`.

A normal crepant dlt model of `(Y, B)` is a projective birational morphism `p : U ⟶ Y` from a
normal variety `U` with a boundary `Δ` that is the crepant boundary of `(Y, B)` on `U`
(`MMP.Mori.IsCrepantBoundary`, for some canonical divisor of `Y`) such that `(U, Δ)` is dlt; no
`ℚ`-factoriality of `U` and no condition on the exceptional divisors is imposed. A horizontal
floor branch of such a model `(U, Δ)` is a normal
prime component `S ⊆ ⌊Δ⌋` together with its adjunction pair `(S, B_S)`
(`MMP.Fourfold.IsAdjunctionStep`, for `j : S ⟶ U`) such that `S ⟶ V` is dominant. Pull-backs
of rational forms along `p` and along `S ⟶ V` are taken along the function field maps
(`MMP.Fourfold.pluriformPullback`), and a crepant birational map is
`MMP.Fourfold.IsCrepantBirationalMap`; "over `V`" means compatibility with the function field
maps from `k(V)`. The Stein degree of a branch over `V` is `[k(S) : k(V)]`.

The form `α` and the divisor `M` are those of a single sufficiently divisible even `m`; the
equality `div(α) + mB = r^*M` is coefficientwise, `r^*M` being `MMP.Mori.Divisor.pullback`.

Pull-backs of forms and of `M` are taken along the maps of function fields and the pull-backs of
Cartier divisors; log discrepancies of divisors over a branch are compared through the
correspondence of divisorial valuations under the birational map, the divisor over the target
being produced by the valuative criterion of properness. Adjunction for `m`-canonical forms is
reduced to the adjunction formula for top forms with a simple pole, applied to `dt/t ∧ dx` and to
`g dt/t ∧ dx` for a presentation `g (dt/t ∧ dx)^{⊗m}` of the form.

The residue form is built on the generic fibre `C = Y_η`, a smooth proper geometrically connected
curve over `κ(η) = k(V)` with function field `k(Y)`, whose closed points are the horizontal prime
divisors of `Y`. Its canonical divisor is the restriction of `K_Y`, so the horizontal floor of
degree two forces `deg K_C = -2`, that is genus zero, and Riemann–Roch on `C` is read on `Y` along
the horizontal primes. It gives a floor coordinate `x` with a simple pole along each floor prime
and a top form `θ` with horizontal divisor minus the floor. Write `θ = G (dt/t ∧ dξ)` with
`t = x⁻¹`. Since `[k(Y) : k(V)(x)] ≤ 2`, the deck involution fixes `θ` up to sign, so
`G² ∈ k(V)(x)`, and `G²` takes one value `c₀ ∈ k(V)` along every floor prime. For even `m` the
residue of `c₁ θ^{⊗m}` along a horizontal floor branch is then `c₁ c₀^{m/2} (dξ̄)^{⊗m}`. That `G`
is a unit along the branch follows from the uniqueness of Poincaré residues.

The proof assembles the following steps. The divisor `m(K_Y + B)` is Cartier and numerically
trivial over `V`, so it descends along the contraction: `div α₀ + mB = r^*M`. On a crepant dlt
lift `p : (U, Δ) ⟶ (Y, B)` the same form gives `div(p^*α) + mΔ = (p ≫ r)^*M`, the discrepancy of
every prime divisor of `U` being computed by `α`. A horizontal coefficient-one prime of `Δ` is the
strict transform of one of `B`, with the same residue degree over `k(V)`, so the Stein degrees of
the horizontal floor of `Δ` sum to two; two distinct horizontal branches then have degree one and
are birational over `V`, and a branch of degree two is Galois over `V`. Adjunction for
`m`-canonical forms gives `div ρ + mB_S = (S → V)^*M` for the residue `ρ` on each branch, and a
birational map over `V` matching the residues of `α` is crepant, since the log discrepancies of
both sides are read off from `ρ` and the pull-back of `M`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.7(4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MMP.Mori
open scoped WithZero

namespace MMP.Fourfold

variable {k : Type} [Field k] [CharZero k] [IsAlgClosed k]

/-- Functoriality of the maps of function fields along dominant morphisms of integral schemes. -/
private theorem functionFieldMap_comp_apply {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)]
    (t : C.functionField) :
    functionFieldMap (a ≫ b) t = functionFieldMap a (functionFieldMap b t) := by
  have := Scheme.Hom.stalkMapOfEq_comp a b (genericPoint A) (genericPoint B) (genericPoint C)
    (map_genericPoint_of_isDominant a) (map_genericPoint_of_isDominant b)
    (map_genericPoint_of_isDominant (a ≫ b))
  exact congrArg (fun φ => φ.hom t) this

/-- **The discrepancy of a divisor over `S` when `div ρ + mB` is a Cartier pull-back.** Let
`g : S ⟶ V` be dominant, `M` a Cartier divisor on `V` with pull-back `M'` to `S`, and `ρ ≠ 0` a
rational `m`-canonical form on `S` with `ord_Γ ρ + m B_Γ = coeff_Γ M'` for every prime divisor
`Γ`. For a canonical divisor `K` of `S` and a divisor `(Y, f, E)` over `S`, with `M''` the
pull-back of `M` to `Y`, the discrepancy `a(E, S, B)` is `(ord_E(f^*ρ) - coeff_E M'') / m`. -/
private theorem isDiscrepancy_of_ordForm_add_eq_pullback {k : Type} [Field k] [PerfectField k]
    {S V : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] {sS : S ⟶ Spec (.of k)}
    (hS : IsNormalVariety k sS) {n : ℕ} {K : Divisor S} (hK : K.IsCanonicalDivisor sS n)
    (g : S ⟶ V) [IsDominant g] {M : Divisor V} (hM : M.IsCartier) {M' : Divisor S}
    (hM' : M.IsPullback g (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp g M) M')
    {m : ℕ} (hm : 0 < m) {ρ : RationalPluriForms sS n m} (hρ : ρ ≠ 0) {B : QDivisor S}
    (hB : ∀ Γ : MMP.Mori.PrimeDivisor S, (Γ.ordForm ρ : ℚ) + m * B.coeff Γ = M'.coeff Γ)
    (D : DivisorOver k sS) {M'' : Divisor D.Y}
    (hM'' : haveI := D.isLocallyNoetherian; haveI := D.isNormal; haveI := D.isDominant
      haveI := D.isIntegral
      M.IsPullback (D.f ≫ g)
        (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ g) M) M'') :
    IsDiscrepancy sS n K B D (((D.ordPullback ρ - M''.coeff D.E : ℤ) : ℚ) / m) := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  haveI := D.isIntegral
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  have hn := hK.topologicalKrullDim_eq
  have hb := D.isBirationalMorphism.functionFieldMap_bijective
  have hd : (letI := functionFieldAlgebra sS; Algebra.trdeg k S.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq hn
  have hdY : (letI := functionFieldAlgebra (D.f ≫ sS);
      Algebra.trdeg k D.Y.functionField).toNat = n := by
    rw [← trdeg_functionField_eq_of_bijective sS D.f hb]; exact hd
  haveI : LocallyOfFiniteType (D.f ≫ sS) := D.isNormalVariety.1.toLocallyOfFiniteType
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  -- a local equation `φ` of `M` near the centre, and `c = g^*φ`
  obtain ⟨U, hU, φ, hφ⟩ := hM (g (D.f D.E.genericPoint))
  set Z₀ : irreducibleComponents V := pointComponent (g (D.f D.E.genericPoint))
  set c : S.functionField :=
    functionFieldMap g (MMP.Threefold.Mori.Helpers.evalFF Z₀ (φ : RationalFunctions V))
  have hc0 : c ≠ 0 :=
    (map_ne_zero _).mpr (φ.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Z₀)).ne_zero
  have hci : c⁻¹ ≠ 0 := inv_ne_zero hc0
  have hM'c : ∀ Γ : MMP.Mori.PrimeDivisor S, (Γ.support ∩ g ⁻¹ᵁ U).Nonempty →
      M'.coeff Γ = S.ord c Γ.genericPoint := fun Γ hΓ =>
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hM' hφ Γ
      ((Γ.genericPoint_mem_iff (g ⁻¹ᵁ U)).mpr hΓ) Z₀
  set τ : RationalPluriForms sS n m := c⁻¹ • ρ
  have hτ0 : τ ≠ 0 := smul_ne_zero hci hρ
  have hordτ : ∀ Γ : MMP.Mori.PrimeDivisor S,
      Γ.ordForm τ = - S.ord c Γ.genericPoint + Γ.ordForm ρ := by
    intro Γ
    rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hn hci hρ, ← zpow_neg_one,
      MMP.Mori.ord_zpow _ hc0]
    ring
  -- `m (K + B)` is Cartier
  obtain ⟨χ, hχ⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hS hK hρ
  have hCc : (M' + -principalDivisor χ).IsCartier :=
    (hM'.isCartier hM).add (Divisor.isCartier_principalDivisor χ).neg
  have hC : Divisor.toQDivisor (M' + -principalDivisor χ) =
      (m : ℤ) • (Divisor.toQDivisor K + B) := by
    have hpr : -principalDivisor χ = (m : ℤ) • K - divisorOfForm ρ := by rw [← hχ]; abel
    rw [hpr]
    ext Γ
    have := hB Γ
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub, coeff_divisorOfForm] at this ⊢
    push_cast
    rw [zsmul_eq_mul]
    push_cast
    linear_combination -this
  refine ⟨hS, hK, m, hm, ⟨_, hC, hCc⟩, g ⁻¹ᵁ U, hU, τ, ⟨hτ0, fun Γ hΓ => ?_⟩, ?_⟩
  · rw [hordτ Γ, ← hM'c Γ hΓ]
    push_cast
    linear_combination hB Γ
  · -- the order of `f^*τ` along `E`
    have hpb : pullbackRationalPluriForms sS D.f τ =
        functionFieldMap D.f c⁻¹ • pullbackRationalPluriForms sS D.f ρ := by
      letI := functionFieldAlgebra sS
      letI := functionFieldAlgebra (D.f ≫ sS)
      letI := functionFieldMapAlgebra D.f
      haveI := isScalarTower_functionFieldMap sS D.f
      exact pullbackForms_smul (k := k) (K := S.functionField) (K' := D.Y.functionField)
        (d := n) (m := (m : ℤ)) c⁻¹ ρ
    have hρ' : pullbackRationalPluriForms sS D.f ρ ≠ 0 :=
      MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' (sX := sS) D.f hb hd hρ
    have hfc : functionFieldMap D.f c⁻¹ ≠ 0 := (map_ne_zero _).mpr hci
    have hE : M''.coeff D.E = D.Y.ord (functionFieldMap D.f c) D.E.genericPoint := by
      rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hM'' hφ D.E hU Z₀,
        functionFieldMap_comp_apply]
    have e1 : D.ordPullback τ = - D.Y.ord (functionFieldMap D.f c) D.E.genericPoint +
        D.ordPullback ρ := by
      change D.E.ordForm (pullbackRationalPluriForms sS D.f τ) = _
      rw [hpb, D.E.ordForm_smul hdY hfc hρ', map_inv₀, ← zpow_neg_one,
        MMP.Mori.ord_zpow _ ((map_ne_zero _).mpr hc0)]
      simp only [DivisorOver.ordPullback]
      ring
    rw [e1, hE]
    push_cast
    field_simp
    ring

/-- **Orders of forms are invariant under isomorphisms of function fields.** Let
`e : k(W') ≅ k(W)` be a `k`-isomorphism of function fields of normal varieties of dimension `n`
over a field of characteristic zero, and `E ⊆ W`, `E' ⊆ W'` prime divisors with
`v_E(e x) = v_{E'}(x)`. Then `ord_E(e_* τ) = ord_{E'}(τ)` for every rational `m`-canonical form
`τ` of `W'`. -/
private theorem ordForm_pluriformPullback_of_ord_eq {k : Type} [Field k] [CharZero k]
    {W W' : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral W']
    [IsLocallyNoetherian W'] [IsNormal W'] {sW : W ⟶ Spec (.of k)} {sW' : W' ⟶ Spec (.of k)}
    [LocallyOfFiniteType sW] [LocallyOfFiniteType sW'] {n : ℕ} (hW : topologicalKrullDim W = n)
    (hW' : topologicalKrullDim W' = n) (e : FunctionFieldEquiv sW sW')
    (E : MMP.Mori.PrimeDivisor W) (E' : MMP.Mori.PrimeDivisor W')
    (hord : ∀ x : W'.functionField, W.ord (e x) E.genericPoint = W'.ord x E'.genericPoint)
    {m : ℤ} (τ : RationalPluriForms sW' n m) :
    E.ordForm (pluriformPullback sW sW' e.toHom n m τ) = E'.ordForm τ := by
  letI := functionFieldAlgebra sW
  letI := functionFieldAlgebra sW'
  letI : Algebra W'.functionField W.functionField := e.toHom.toRingHom.toAlgebra
  haveI : IsScalarTower k W'.functionField W.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (e.toHom.commutes c).symm
  have hd' : (Algebra.trdeg k W'.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sW') hW'
  have hval : ∀ y : W'.functionField,
      E.divisorialValuation (e y) = E'.divisorialValuation y := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · have hey : e y ≠ 0 := (map_ne_zero e).mpr hy
      rw [E.divisorialValuation_eq_exp_neg_ord hey, E'.divisorialValuation_eq_exp_neg_ord hy,
        hord]
  letI := stalkAlgebra sW E.genericPoint
  letI := stalkAlgebra sW' E'.genericPoint
  haveI := isScalarTower_stalk_functionField sW E.genericPoint
  haveI := isScalarTower_stalk_functionField sW' E'.genericPoint
  have h12 : ∀ a1 : E'.localRing, ∃ a2 : E.localRing,
      algebraMap E.localRing W.functionField a2 =
        e (algebraMap E'.localRing W'.functionField a1) := by
    intro a1
    have : E'.divisorialValuation (algebraMap E'.localRing W'.functionField a1) ≤ 1 :=
      (E'.divisorialValuation_le_one_iff _).mpr ⟨a1, rfl⟩
    rw [← hval] at this
    exact (E.divisorialValuation_le_one_iff _).mp this
  have h21 : ∀ a2 : E.localRing, ∃ a1 : E'.localRing,
      e (algebraMap E'.localRing W'.functionField a1) =
        algebraMap E.localRing W.functionField a2 := by
    intro a2
    obtain ⟨y, hy⟩ := e.surjective (algebraMap E.localRing W.functionField a2)
    have : E'.divisorialValuation y ≤ 1 := by
      rw [← hval, hy]
      exact (E.divisorialValuation_le_one_iff _).mpr ⟨a2, rfl⟩
    obtain ⟨a1, ha1⟩ := (E'.divisorialValuation_le_one_iff _).mp this
    exact ⟨a1, by rwa [ha1]⟩
  obtain ⟨ψ, hψb, hψ⟩ := MMP.Threefold.Mori.ModelIndependence.exists_ringHom_bijective_of_range
    (e : W'.functionField →+* W.functionField) h12 h21
  letI : Algebra E'.localRing E.localRing := ψ.toAlgebra
  letI : Algebra E'.localRing W.functionField :=
    ((algebraMap E.localRing W.functionField).comp ψ).toAlgebra
  have hS1 : IsScalarTower k E'.localRing E.localRing := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    apply IsFractionRing.injective E.localRing W.functionField
    change _ = algebraMap E.localRing W.functionField (ψ (algebraMap k E'.localRing c))
    rw [hψ, ← IsScalarTower.algebraMap_apply k E'.localRing W'.functionField c,
      ← IsScalarTower.algebraMap_apply k E.localRing W.functionField c]
    exact IsScalarTower.algebraMap_apply k W'.functionField W.functionField c
  have hS2 : IsScalarTower E'.localRing E.localRing W.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hS3 : IsScalarTower E'.localRing W'.functionField W.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => hψ a
  have hS4 : IsScalarTower k E'.localRing W.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = algebraMap E.localRing W.functionField (ψ (algebraMap k E'.localRing c))
    rw [IsScalarTower.algebraMap_apply k E.localRing W.functionField c,
      IsScalarTower.algebraMap_apply k E'.localRing E.localRing c]
    rfl
  obtain ⟨σ, hσ, h0σ⟩ := E'.exists_topForms_generator (sX := sW') hd'
  have hωT : IsPullbackGenerator W.functionField
      (topFormsMap k E'.localRing W'.functionField n σ) :=
    isPullbackGenerator_functionFieldHom hW hW' e.toHom
      (span_singleton_topFormsMap (nonZeroDivisors _) hσ) h0σ
  exact MMP.Threefold.Mori.Helpers.ordAt_pullbackForms_eq (k := k)
    (K := W'.functionField) (K' := W.functionField)
    (A := E'.localRing) (A' := E.localRing) (d := n) (m := m) hψb
    (v := fun y => W'.ord y E'.genericPoint) (v' := fun y => W.ord y E.genericPoint)
    (fun x y hx hy => E'.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => E'.ord_algebraMap_of_isUnit ha)
    (fun x y hx hy => E.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => E.ord_algebraMap_of_isUnit ha)
    (fun x => hord x) hσ hωT τ

/-- The generic point `Spec k(W) ⟶ W ⟶ Spec k` is `Spec` of the structure map `k → k(W)`. -/
private theorem fromSpecStalk_genericPoint_comp {k : Type} [Field k] {W : Scheme.{0}} [IsIntegral W]
    (sW : W ⟶ Spec (.of k)) :
    letI := functionFieldAlgebra sW
    W.fromSpecStalk (genericPoint W) ≫ sW =
      Spec.map (CommRingCat.ofHom (algebraMap k W.functionField)) := by
  have h1 : sW = W.toSpecΓ ≫ Spec.map sW.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of k)).inv := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have h2 : W.fromSpecStalk (genericPoint W) ≫ sW = Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫
      sW.appTop ≫ W.presheaf.germ ⊤ (genericPoint W) trivial) := by
    conv_lhs => rw [h1]
    rw [← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp, ← Spec.map_comp,
      Category.assoc]
  rw [h2]
  rfl

/-- **The centre of a valuation ring on a proper scheme.** A valuation subring `R` of `k(W)`
containing `k`, for `W` proper over `k`, dominates the local ring of some point of `W`. -/
private theorem exists_dominates_valuationSubring_of_isProper {k : Type} [Field k]
    {W : Scheme.{0}} [IsIntegral W] (sW : W ⟶ Spec (.of k)) [IsProper sW]
    (R : ValuationSubring W.functionField)
    (hk : letI := functionFieldAlgebra sW; ∀ c : k, algebraMap k W.functionField c ∈ R) :
    ∃ x : W, (∀ a : W.presheaf.stalk x, algebraMap _ W.functionField a ∈ R) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk x),
        algebraMap _ W.functionField a ∈ R.nonunits := by
  letI := functionFieldAlgebra sW
  let φ : k →+* R := (algebraMap k W.functionField).codRestrict R hk
  have hex : ValuativeCriterion.Existence sW := by
    have h : @IsProper _ _ sW := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq sW :=
    { R := R
      K := W.functionField
      i₁ := W.fromSpecStalk (genericPoint W)
      i₂ := Spec.map (CommRingCat.ofHom φ)
      commSq := ⟨by
        rw [fromSpecStalk_genericPoint_comp, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R W.functionField)) ≫ l =
      W.fromSpecStalk (genericPoint W) := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint W ⤳ x := (genericPoint_spec W).specializes trivial
  let f := Scheme.stalkClosedPointTo l
  have hf : f ≫ CommRingCat.ofHom (algebraMap R W.functionField) =
      W.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (W.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hfa : ∀ a : W.presheaf.stalk x,
      algebraMap _ W.functionField a = ((f.hom a : R) : W.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hf).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hfa]; exact (f.hom a).2
  · rw [hfa, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal]
    exact fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu)

/-- **Centres of valuations on a proper variety.** A valuation of `k(W)`, trivial on `k`, of a
scheme `W` proper over `k` dominates the local ring of some point of `W`. -/
private theorem exists_dominates_of_isProper {k : Type} [Field k] {W : Scheme.{0}} [IsIntegral W]
    (sW : W ⟶ Spec (.of k)) [IsProper sW] (ξ : Valuation W.functionField ℤᵐ⁰)
    (hk : letI := functionFieldAlgebra sW; ∀ c : k, ξ (algebraMap k W.functionField c) ≤ 1) :
    ∃ x : W, (∀ a : W.presheaf.stalk x, ξ (algebraMap _ W.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk x),
        ξ (algebraMap _ W.functionField a) < 1 := by
  letI := functionFieldAlgebra sW
  obtain ⟨x, h1, h2⟩ := exists_dominates_valuationSubring_of_isProper sW ξ.valuationSubring
    fun c => (ξ.mem_valuationSubring_iff _).2 (hk c)
  refine ⟨x, fun a => (ξ.mem_valuationSubring_iff _).1 (h1 a), fun a ha => ?_⟩
  have h := (ValuationSubring.mem_nonunits_iff _).1 (h2 a ha)
  have e := Valuation.isEquiv_valuation_valuationSubring ξ 1 (algebraMap _ W.functionField a)
  rw [map_one, map_one] at e
  exact not_le.mp fun h' => not_le.mpr h (e.mp h')

/-- **Transport of divisors over a variety along an isomorphism of function fields.** For a
`k`-isomorphism `σ : k(S₂) ≅ k(S₁)` of function fields of normal varieties, `S₂` proper, and a
divisor `D` over `S₁` with valuation `v`, some divisor over `S₂`, proper over `S₂`, has
valuation `v ∘ σ`. -/
private theorem exists_divisorOver_valuation_eq_comap_of_functionFieldEquiv {k : Type} [Field k]
    {S₁ S₂ : Scheme.{0}}
    [IsIntegral S₁] [IsIntegral S₂] {s₁ : S₁ ⟶ Spec (.of k)} {s₂ : S₂ ⟶ Spec (.of k)}
    (h₂ : IsNormalVariety k s₂) [IsProper s₂] (σ : FunctionFieldEquiv s₁ s₂)
    (D : DivisorOver k s₁) :
    letI := functionFieldAlgebra s₁
    letI := functionFieldAlgebra s₂
    ∃ D' : DivisorOver k s₂, IsProper D'.f ∧
      D'.valuation = D.valuation.comap σ.toRingEquiv.toRingHom := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  letI := functionFieldAlgebra s₁
  letI := functionFieldAlgebra s₂
  letI := functionFieldAlgebra (D.f ≫ s₁)
  set ξ := D.valuation.comap σ.toRingEquiv.toRingHom
  have hb := D.isBirationalMorphism.functionFieldMap_bijective
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k s₂ ξ := by
    refine ⟨D.Y, D.f ≫ s₁, D.isNormalVariety, D.E,
      σ.trans (functionFieldAlgEquiv s₁ D.f hb), ?_⟩
    ext x
    rfl
  have hk : ∀ c : k, ξ (algebraMap k S₂.functionField c) ≤ 1 := by
    intro c
    change D.valuation (σ (algebraMap k S₂.functionField c)) ≤ 1
    rw [AlgEquiv.commutes]
    letI := stalkAlgebra s₁ (D.f D.E.genericPoint)
    haveI := isScalarTower_stalk_functionField s₁ (D.f D.E.genericPoint)
    rw [IsScalarTower.algebraMap_apply k (S₁.presheaf.stalk (D.f D.E.genericPoint))
      S₁.functionField c]
    exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl _
  obtain ⟨x, hle, hlt⟩ := exists_dominates_of_isProper s₂ ξ hk
  haveI : AlgebraicGeometry.IsVariety k s₂ := h₂.1
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates s₂ hdiv x hle hlt
  exact ⟨D'.toDivisorOver, D'.isProper, hv⟩

/-- The valuation of a divisor `(Y, f, E)` over `S`, restricted along a dominant `g : S ⟶ V`,
dominates the local ring of `V` at the image `g(f(η_E))` of the generic point of `E`. -/
private theorem valuation_comap_dominates {k : Type} [Field k] {S V : Scheme.{0}} [IsIntegral S]
    [IsIntegral V] {sS : S ⟶ Spec (.of k)} (g : S ⟶ V) [IsDominant g] (D : DivisorOver k sS) :
    (∀ a : V.presheaf.stalk (g (D.f D.E.genericPoint)),
      D.valuation.comap (functionFieldMap g) (algebraMap _ V.functionField a) ≤ 1) ∧
    ∀ a ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk (g (D.f D.E.genericPoint))),
      D.valuation.comap (functionFieldMap g) (algebraMap _ V.functionField a) < 1 := by
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl _
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    refine MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl _ ?_
    exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)

/-- The coefficient along `E` of the pull-back of a Cartier divisor `M` to a divisor `(Y, f, E)`
over `S`, through `g : S ⟶ V`, is read off from the valuation of `E` on `k(V)`:
`exp (-coeff_E (f^* g^* M)) = v_E(g^* φ)` for a local equation `φ` of `M` near `g(f(η_E))`. -/
private theorem valuation_eq_exp_neg_coeff {k : Type} [Field k] {S V : Scheme.{0}} [IsIntegral S]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] {sS : S ⟶ Spec (.of k)} (g : S ⟶ V)
    [IsDominant g] (D : DivisorOver k sS) {M : Divisor V} {U : V.Opens}
    {φ : (RationalFunctions V)ˣ} (hφ : M.IsLocalEquation U φ)
    (hU : g (D.f D.E.genericPoint) ∈ U) (Z : irreducibleComponents V) {M'' : Divisor D.Y}
    (hM'' : haveI := D.isLocallyNoetherian; haveI := D.isNormal; haveI := D.isDominant
      haveI := D.isIntegral
      M.IsPullback (D.f ≫ g)
        (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ g) M) M'') :
    D.valuation.comap (functionFieldMap g)
        (MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions V)) =
      WithZero.exp (-M''.coeff D.E) := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  haveI := D.isIntegral
  have hy : MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions V) ≠ 0 :=
    (φ.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Z)).ne_zero
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hM'' hφ D.E hU Z,
    functionFieldMap_comp_apply, Valuation.comap_apply]
  change D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g _)) = _
  exact D.E.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr ((map_ne_zero _).mpr hy))

/-- **Coefficients of Cartier pull-backs depend only on the valuation on `k(V)`.** Let
`g₁ : S₁ ⟶ V`, `g₂ : S₂ ⟶ V` be dominant, `V` normal and separated over `k`, and
`σ : k(S₂) ≅ k(S₁)` compatible with `g₁^*`, `g₂^*`. For divisors `D` over `S₁` and `D'` over `S₂`
with `v_{D'} = v_D ∘ σ`, the pull-backs of a Cartier divisor `M` of `V` have the same coefficient
along `D` and `D'`. -/
private theorem coeff_isPullback_eq_of_valuation_eq_comap {k : Type} [Field k]
    {S₁ S₂ V : Scheme.{0}}
    [IsIntegral S₁] [IsIntegral S₂] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {s₁ : S₁ ⟶ Spec (.of k)} {s₂ : S₂ ⟶ Spec (.of k)} (sV : V ⟶ Spec (.of k)) [IsSeparated sV]
    (g₁ : S₁ ⟶ V) (g₂ : S₂ ⟶ V) [IsDominant g₁] [IsDominant g₂]
    (σ : S₂.functionField ≃+* S₁.functionField)
    (hσ : ∀ x, σ (functionFieldMap g₂ x) = functionFieldMap g₁ x)
    (D : DivisorOver k s₁) (D' : DivisorOver k s₂)
    (hv : D'.valuation = D.valuation.comap σ.toRingHom) {M : Divisor V} (hM : M.IsCartier)
    {M₁ : Divisor D.Y}
    (h₁ : haveI := D.isLocallyNoetherian; haveI := D.isNormal; haveI := D.isDominant
      haveI := D.isIntegral
      M.IsPullback (D.f ≫ g₁)
        (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ g₁) M) M₁)
    {M₂ : Divisor D'.Y}
    (h₂ : haveI := D'.isLocallyNoetherian; haveI := D'.isNormal; haveI := D'.isDominant
      haveI := D'.isIntegral
      M.IsPullback (D'.f ≫ g₂)
        (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D'.f ≫ g₂) M) M₂) :
    M₁.coeff D.E = M₂.coeff D'.E := by
  have hw : D'.valuation.comap (functionFieldMap g₂) = D.valuation.comap (functionFieldMap g₁) := by
    ext x
    rw [Valuation.comap_apply, Valuation.comap_apply, hv, Valuation.comap_apply]
    exact congrArg D.valuation (hσ x)
  obtain ⟨d₁, d₁'⟩ := valuation_comap_dominates g₁ D
  obtain ⟨d₂, d₂'⟩ := valuation_comap_dominates g₂ D'
  rw [hw] at d₂ d₂'
  have hc : g₂ (D'.f D'.E.genericPoint) = g₁ (D.f D.E.genericPoint) :=
    MMP.Positivity.DivisorOver.eq_of_dominates sV _ d₂ d₂' d₁ d₁'
  obtain ⟨U, hU, φ, hφ⟩ := hM (g₁ (D.f D.E.genericPoint))
  set Z : irreducibleComponents V := pointComponent (g₁ (D.f D.E.genericPoint))
  have e₁ := valuation_eq_exp_neg_coeff g₁ D hφ hU Z h₁
  have e₂ := valuation_eq_exp_neg_coeff g₂ D' hφ (hc ▸ hU) Z h₂
  rw [hw, e₁] at e₂
  have := WithZero.exp_injective e₂
  omega

/-- **Crepancy criterion, one direction.** Let `g_i : S_i ⟶ V` be dominant morphisms of normal
varieties of dimension `d` over `k`, `S₂` proper, `M` a Cartier divisor of `V` with pull-backs
`M_i`, and `ρ_i ≠ 0` rational `m`-canonical forms with `ord ρ_i + m B_i = M_i`. Let
`σ : k(S₂) ≅ k(S₁)` be compatible with the maps from `k(V)` and with the orders of `ρ_i` along
divisors with corresponding valuations. Then every log discrepancy of `(S₁, B₁)` along a valuation
`v` is a log discrepancy of `(S₂, B₂)` along `v ∘ σ`. -/
private theorem hasLogDiscrepancy_comap_of_ordForm_add_eq_pullback
    {S₁ S₂ V : Scheme.{0}} [IsIntegral S₁] [IsLocallyNoetherian S₁] [IsNormal S₁]
    [CompactSpace S₁] [IsIntegral S₂] [IsLocallyNoetherian S₂] [IsNormal S₂] [CompactSpace S₂]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {s₁ : S₁ ⟶ Spec (.of k)} {s₂ : S₂ ⟶ Spec (.of k)} (sV : V ⟶ Spec (.of k)) [IsSeparated sV]
    (h₁ : IsNormalVariety k s₁) (h₂ : IsNormalVariety k s₂) [IsProper s₂]
    {d : ℕ} (hd₁ : topologicalKrullDim S₁ = d) (hd₂ : topologicalKrullDim S₂ = d)
    (g₁ : S₁ ⟶ V) (g₂ : S₂ ⟶ V) [IsDominant g₁] [IsDominant g₂]
    {M : Divisor V} (hM : M.IsCartier) {m : ℕ} (hm : 0 < m)
    {ρ₁ : RationalPluriForms s₁ d m} {ρ₂ : RationalPluriForms s₂ d m} (hρ₁ : ρ₁ ≠ 0)
    (hρ₂ : ρ₂ ≠ 0) {B₁ : QDivisor S₁} {B₂ : QDivisor S₂}
    {M₁ : Divisor S₁}
    (hM₁ : M.IsPullback g₁ (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp g₁ M) M₁)
    (hB₁ : ∀ Γ : MMP.Mori.PrimeDivisor S₁, (Γ.ordForm ρ₁ : ℚ) + m * B₁.coeff Γ = M₁.coeff Γ)
    {M₂ : Divisor S₂}
    (hM₂ : M.IsPullback g₂ (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp g₂ M) M₂)
    (hB₂ : ∀ Γ : MMP.Mori.PrimeDivisor S₂, (Γ.ordForm ρ₂ : ℚ) + m * B₂.coeff Γ = M₂.coeff Γ)
    (σ : FunctionFieldEquiv s₁ s₂) (hσ : ∀ x, σ (functionFieldMap g₂ x) = functionFieldMap g₁ x)
    (hord : letI := functionFieldAlgebra s₁; letI := functionFieldAlgebra s₂;
      ∀ (D : DivisorOver k s₁) (D' : DivisorOver k s₂),
      D'.valuation = D.valuation.comap σ.toRingEquiv.toRingHom →
        D.ordPullback ρ₁ = D'.ordPullback ρ₂)
    (v : Valuation S₁.functionField ℤᵐ⁰) (a : ℝ) (h : HasLogDiscrepancy s₁ B₁ v a) :
    letI := functionFieldAlgebra s₁; letI := functionFieldAlgebra s₂;
    HasLogDiscrepancy s₂ B₂ (v.comap σ.toRingEquiv.toRingHom) a := by
  letI := functionFieldAlgebra s₁
  letI := functionFieldAlgebra s₂
  obtain ⟨n, D, rfl, hD⟩ := h
  have hnd : n = d := by
    have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hD).symm.trans hd₁
    exact_mod_cast this
  subst hnd
  obtain ⟨-, -, -, -, ⟨K₁, hK₁, -⟩, -⟩ := id hD
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  haveI := D.isIntegral
  haveI : CompactSpace D.Y := by
    have := D.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D.f ≫ s₁)
  obtain ⟨M₁'', hM₁''⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant (D.f ≫ g₁) hM
  have hdisc := isDiscrepancy_of_ordForm_add_eq_pullback h₁ hK₁ g₁ hM hM₁ hm hρ₁ hB₁ D hM₁''
  have ha := ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hdisc a).mp hD).2
  obtain ⟨D', hD'p, hv⟩ := exists_divisorOver_valuation_eq_comap_of_functionFieldEquiv h₂ σ D
  obtain ⟨K₂, hK₂⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety s₂ h₂ hd₂
  haveI := D'.isLocallyNoetherian
  haveI := D'.isNormal
  haveI := D'.isDominant
  haveI := D'.isIntegral
  haveI : CompactSpace D'.Y := by
    have := D'.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D'.f ≫ s₂)
  obtain ⟨M₂'', hM₂''⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant (D'.f ≫ g₂) hM
  have hdisc' := isDiscrepancy_of_ordForm_add_eq_pullback h₂ hK₂ g₂ hM hM₂ hm hρ₂ hB₂ D' hM₂''
  have hc := coeff_isPullback_eq_of_valuation_eq_comap sV g₁ g₂ σ.toRingEquiv hσ D D' hv hM
    hM₁'' hM₂''
  have ho := hord D D' hv
  refine ⟨n, D', hv, ?_⟩
  rw [ha, ho, hc]
  exact MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hdisc' hD'p

/-- **Crepancy criterion.** Let `g_i : S_i ⟶ V` be dominant morphisms of proper normal varieties
of dimension `d` over `k`, `M` a Cartier divisor of `V` with pull-backs `M_i`, and `ρ_i ≠ 0`
rational `m`-canonical forms with `div ρ_i + m B_i = M_i`. A `k`-isomorphism
`σ : k(S₂) ≅ k(S₁)` over `k(V)` matching the orders of `ρ₁` and `ρ₂` along corresponding
divisors is crepant: the log discrepancies of `(S₁, B₁)` and `(S₂, B₂)` correspond. -/
private theorem isCrepantBirationalMap_of_ordForm_add_eq_pullback
    {S₁ S₂ V : Scheme.{0}} [IsIntegral S₁] [IsLocallyNoetherian S₁] [IsNormal S₁]
    [CompactSpace S₁] [IsIntegral S₂] [IsLocallyNoetherian S₂] [IsNormal S₂] [CompactSpace S₂]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {s₁ : S₁ ⟶ Spec (.of k)} {s₂ : S₂ ⟶ Spec (.of k)} (sV : V ⟶ Spec (.of k)) [IsSeparated sV]
    (h₁ : IsNormalVariety k s₁) (h₂ : IsNormalVariety k s₂) [IsProper s₁] [IsProper s₂]
    {d : ℕ} (hd₁ : topologicalKrullDim S₁ = d) (hd₂ : topologicalKrullDim S₂ = d)
    (g₁ : S₁ ⟶ V) (g₂ : S₂ ⟶ V) [IsDominant g₁] [IsDominant g₂]
    {M : Divisor V} (hM : M.IsCartier) {m : ℕ} (hm : 0 < m)
    {ρ₁ : RationalPluriForms s₁ d m} {ρ₂ : RationalPluriForms s₂ d m} (hρ₁ : ρ₁ ≠ 0)
    (hρ₂ : ρ₂ ≠ 0) {B₁ : QDivisor S₁} {B₂ : QDivisor S₂}
    {M₁ : Divisor S₁}
    (hM₁ : M.IsPullback g₁ (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp g₁ M) M₁)
    (hB₁ : ∀ Γ : MMP.Mori.PrimeDivisor S₁, (Γ.ordForm ρ₁ : ℚ) + m * B₁.coeff Γ = M₁.coeff Γ)
    {M₂ : Divisor S₂}
    (hM₂ : M.IsPullback g₂ (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp g₂ M) M₂)
    (hB₂ : ∀ Γ : MMP.Mori.PrimeDivisor S₂, (Γ.ordForm ρ₂ : ℚ) + m * B₂.coeff Γ = M₂.coeff Γ)
    (σ : FunctionFieldEquiv s₁ s₂) (hσ : ∀ x, σ (functionFieldMap g₂ x) = functionFieldMap g₁ x)
    (hord : letI := functionFieldAlgebra s₁; letI := functionFieldAlgebra s₂;
      ∀ (D : DivisorOver k s₁) (D' : DivisorOver k s₂),
      D'.valuation = D.valuation.comap σ.toRingEquiv.toRingHom →
        D.ordPullback ρ₁ = D'.ordPullback ρ₂) :
    IsCrepantBirationalMap s₁ s₂ B₁ B₂ σ := by
  letI := functionFieldAlgebra s₁
  letI := functionFieldAlgebra s₂
  intro v a
  refine ⟨hasLogDiscrepancy_comap_of_ordForm_add_eq_pullback sV h₁ h₂ hd₁ hd₂ g₁ g₂ hM hm hρ₁
    hρ₂ hM₁ hB₁ hM₂ hB₂ σ hσ hord v a, fun h => ?_⟩
  have hσ' : ∀ x, σ.symm (functionFieldMap g₁ x) = functionFieldMap g₂ x := by
    intro x
    rw [← hσ x, AlgEquiv.symm_apply_apply]
  have hord' : letI := functionFieldAlgebra s₁; letI := functionFieldAlgebra s₂;
      ∀ (D : DivisorOver k s₂) (D' : DivisorOver k s₁),
      D'.valuation = D.valuation.comap σ.symm.toRingEquiv.toRingHom →
        D.ordPullback ρ₂ = D'.ordPullback ρ₁ := by
    intro D D' hv
    refine (hord D' D ?_).symm
    ext x
    rw [Valuation.comap_apply, hv, Valuation.comap_apply]
    change D.valuation x = D.valuation (σ.symm (σ x))
    rw [AlgEquiv.symm_apply_apply]
  have := hasLogDiscrepancy_comap_of_ordForm_add_eq_pullback sV h₂ h₁ hd₂ hd₁ g₂ g₁ hM hm hρ₂
    hρ₁ hM₂ hB₂ hM₁ hB₁ σ.symm hσ' hord' _ a h
  have hvv : (v.comap σ.toRingEquiv.toRingHom).comap σ.symm.toRingEquiv.toRingHom = v := by
    ext x
    change v (σ (σ.symm x)) = v x
    rw [AlgEquiv.apply_symm_apply]
  rwa [hvv] at this

/-- A field extension of degree two in characteristic zero has a nontrivial automorphism of
order two: it is Galois with group of order two. -/
private theorem exists_algEquiv_ne_one_of_finrank_eq_two {F L : Type*} [Field F] [Field L]
    [Algebra F L] [CharZero F] (h : Module.finrank F L = 2) :
    ∃ σ : L ≃ₐ[F] L, σ ≠ 1 ∧ σ * σ = 1 := by
  haveI : FiniteDimensional F L := Module.finite_of_finrank_eq_succ h
  haveI : Algebra.IsQuadraticExtension F L := ⟨h⟩
  haveI : IsGalois F L := inferInstance
  have hc : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, h]
  haveI : Finite (L ≃ₐ[F] L) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : Nontrivial (L ≃ₐ[F] L) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; norm_num)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : L ≃ₐ[F] L)
  refine ⟨σ, hσ, ?_⟩
  have := pow_card_eq_one' (G := L ≃ₐ[F] L) (x := σ)
  rw [hc, sq] at this
  exact this

/-- The `k`-homomorphism `g^* : k(V) → k(S)` of function fields along a dominant morphism
`g : S ⟶ V`, for `S` over `k` through `g`. -/
private noncomputable def ffHom {S V : Scheme.{0}} [IsIntegral S] [IsIntegral V]
    (sV : V ⟶ Spec (.of k))
    (g : S ⟶ V) [IsDominant g] {s : S ⟶ Spec (.of k)} (hs : g ≫ sV = s) :
    FunctionFieldHom s sV :=
  letI := functionFieldAlgebra sV
  letI := functionFieldAlgebra s
  { toRingHom := functionFieldMap g
    commutes' := fun c => by
      subst hs
      letI := functionFieldMapAlgebra g
      have := isScalarTower_functionFieldMap sV g
      exact (IsScalarTower.algebraMap_apply k V.functionField S.functionField c).symm }

/-- **The deck involution of a degree-two branch.** If `k(S)` has degree two over `k(V)` along a
dominant `g : S ⟶ V`, there is a `k`-automorphism `σ ≠ 1` of `k(S)` over `k(V)` with
`σ² = 1`. -/
private theorem exists_functionFieldEquiv_involution {S V : Scheme.{0}} [IsIntegral S]
    [IsIntegral V] (sV : V ⟶ Spec (.of k)) (g : S ⟶ V) [IsDominant g] {s : S ⟶ Spec (.of k)}
    (hs : g ≫ sV = s)
    (h : (letI := functionFieldMapAlgebra g;
      Module.finrank V.functionField S.functionField) = 2) :
    ∃ σ : FunctionFieldEquiv s s, σ ≠ 1 ∧ σ * σ = 1 ∧
      ∀ x : V.functionField, σ (functionFieldMap g x) = functionFieldMap g x := by
  subst hs
  letI := functionFieldMapAlgebra g
  letI := functionFieldAlgebra sV
  letI := functionFieldAlgebra (g ≫ sV)
  haveI := isScalarTower_functionFieldMap sV g
  haveI : CharZero V.functionField :=
    charZero_of_injective_algebraMap (algebraMap k V.functionField).injective
  obtain ⟨τ, hτ1, hτ2⟩ := exists_algEquiv_ne_one_of_finrank_eq_two h
  refine ⟨τ.restrictScalars k, fun h1 => hτ1 ?_, ?_, fun x => τ.commutes x⟩
  · ext x
    exact congrArg (fun e : FunctionFieldEquiv (g ≫ sV) (g ≫ sV) => e x) h1
  · ext x
    exact congrArg (fun e : S.functionField ≃ₐ[V.functionField] S.functionField => e x) hτ2

/-- **Orders of pulled-back forms along corresponding divisors.** If `σ : k(S₂) ≅ k(S₁)` pulls
`ρ₂` back to `ρ₁`, then along divisors `D` over `S₁` and `D'` over `S₂` with `v_{D'} = v_D ∘ σ`
the orders agree: `ord_D ρ₁ = ord_{D'} ρ₂`. -/
private theorem ordPullback_eq_of_pluriformPullback_eq
    {S₁ S₂ : Scheme.{0}} [IsIntegral S₁] [IsLocallyNoetherian S₁] [IsNormal S₁]
    [IsIntegral S₂] [IsLocallyNoetherian S₂] [IsNormal S₂]
    {s₁ : S₁ ⟶ Spec (.of k)} {s₂ : S₂ ⟶ Spec (.of k)}
    (h₁ : IsNormalVariety k s₁) (h₂ : IsNormalVariety k s₂)
    {d : ℕ} (hd₁ : topologicalKrullDim S₁ = d) (hd₂ : topologicalKrullDim S₂ = d) {m : ℕ}
    {ρ₁ : RationalPluriForms s₁ d m} {ρ₂ : RationalPluriForms s₂ d m}
    (σ : FunctionFieldEquiv s₁ s₂) (hσρ : pluriformPullback s₁ s₂ σ.toHom d m ρ₂ = ρ₁) :
    letI := functionFieldAlgebra s₁; letI := functionFieldAlgebra s₂;
    ∀ (D : DivisorOver k s₁) (D' : DivisorOver k s₂),
      D'.valuation = D.valuation.comap σ.toRingEquiv.toRingHom →
        D.ordPullback ρ₁ = D'.ordPullback ρ₂ := by
  letI := functionFieldAlgebra s₁
  letI := functionFieldAlgebra s₂
  intro D D' hv
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  haveI := D.isIntegral
  haveI := D'.isLocallyNoetherian
  haveI := D'.isNormal
  haveI := D'.isDominant
  haveI := D'.isIntegral
  haveI : LocallyOfFiniteType s₁ := h₁.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType s₂ := h₂.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (D.f ≫ s₁) := D.isNormalVariety.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (D'.f ≫ s₂) := D'.isNormalVariety.1.toLocallyOfFiniteType
  letI := functionFieldAlgebra (D.f ≫ s₁)
  letI := functionFieldAlgebra (D'.f ≫ s₂)
  have hb₁ := D.isBirationalMorphism.functionFieldMap_bijective
  have hb₂ := D'.isBirationalMorphism.functionFieldMap_bijective
  have hY₁ : topologicalKrullDim D.Y = d := by
    haveI := h₁.1
    haveI := D.isNormalVariety.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism s₁ (D.f ≫ s₁)
      D.isBirationalMorphism, hd₁]
  have hY₂ : topologicalKrullDim D'.Y = d := by
    haveI := h₂.1
    haveI := D'.isNormalVariety.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism s₂ (D'.f ≫ s₂)
      D'.isBirationalMorphism, hd₂]
  let a₁ := functionFieldAlgEquiv s₁ D.f hb₁
  let a₂ := functionFieldAlgEquiv s₂ D'.f hb₂
  let e : FunctionFieldEquiv (D.f ≫ s₁) (D'.f ≫ s₂) := a₂.symm.trans (σ.trans a₁)
  have hpb₁ : pullbackRationalPluriForms s₁ D.f ρ₁ =
      pluriformPullback (D.f ≫ s₁) s₁ a₁.toAlgHom d m ρ₁ := rfl
  have hpb₂ : pullbackRationalPluriForms s₂ D'.f ρ₂ =
      pluriformPullback (D'.f ≫ s₂) s₂ a₂.toAlgHom d m ρ₂ := rfl
  have hcomp : (FunctionFieldEquiv.toHom _ _ e).comp a₂.toAlgHom =
      a₁.toAlgHom.comp (FunctionFieldEquiv.toHom _ _ σ) := by
    ext x
    change a₁ (σ (a₂.symm (a₂ x))) = a₁ (σ x)
    rw [AlgEquiv.symm_apply_apply]
  have key : pluriformPullback (D.f ≫ s₁) s₁ a₁.toAlgHom d m ρ₁ =
      pluriformPullback (D.f ≫ s₁) (D'.f ≫ s₂) (FunctionFieldEquiv.toHom _ _ e) d m
        (pluriformPullback (D'.f ≫ s₂) s₂ a₂.toAlgHom d m ρ₂) := by
    rw [← hσρ, pluriformPullback_comp hY₁ hd₁ hd₂, pluriformPullback_comp hY₁ hY₂ hd₂, hcomp]
  change D.E.ordForm (pullbackRationalPluriForms s₁ D.f ρ₁) =
    D'.E.ordForm (pullbackRationalPluriForms s₂ D'.f ρ₂)
  rw [hpb₁, hpb₂, key]
  refine ordForm_pluriformPullback_of_ord_eq hY₁ hY₂ e D.E D'.E (fun x => ?_) _
  by_cases hx : x = 0
  · subst hx
    simp [Scheme.ord_zero]
  · have hex : e x ≠ 0 := (map_ne_zero e).mpr hx
    have h1 := congrArg (fun w : Valuation S₂.functionField ℤᵐ⁰ => w (a₂.symm x)) hv
    change D'.E.divisorialValuation (functionFieldMap D'.f (a₂.symm x)) =
      D.E.divisorialValuation (functionFieldMap D.f (σ (a₂.symm x))) at h1
    have h2 : functionFieldMap D'.f (a₂.symm x) = x := a₂.apply_symm_apply x
    have h3 : functionFieldMap D.f (σ (a₂.symm x)) = e x := rfl
    rw [h2, h3, D'.E.divisorialValuation_eq_exp_neg_ord hx,
      D.E.divisorialValuation_eq_exp_neg_ord hex] at h1
    have := WithZero.exp_injective h1
    omega

/-- **Rational functions without horizontal poles come from the base.** Let `r : Y ⟶ V` be a
closed dominant morphism of integral schemes with `r_* 𝒪_Y = 𝒪_V`, `Y` normal and Noetherian. A
rational function `x` on `Y` with `ord_P x ≥ 0` along every prime divisor `P` dominating `V` is
the pull-back of a rational function on `V`: its poles are vertical, so `x` is regular over the
complement `W` of their images, and `Γ(r⁻¹W, 𝒪_Y) = Γ(W, 𝒪_V)`. -/
private theorem exists_functionFieldMap_eq_of_forall_ord_nonneg
    {Y V : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral V] (r : Y ⟶ V) [IsDominant r] (hr : ∀ U : V.Opens, IsIso (r.app U))
    (hcl : IsClosedMap r) (x : Y.functionField)
    (hx : ∀ P : MMP.Mori.PrimeDivisor Y, r P.genericPoint = genericPoint V →
      0 ≤ Y.ord x P.genericPoint) :
    ∃ y : V.functionField, functionFieldMap r y = x := by
  classical
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, map_zero _⟩
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero hx0
  set S : Set (MMP.Mori.PrimeDivisor Y) := {P | Y.ord x P.genericPoint < 0}
  have hS : S.Finite := by
    refine (MMP.Mori.principalDivisor φ).support.finite_toSet.subset fun P hP => ?_
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    change (MMP.Mori.principalDivisor φ).coeff P ≠ 0
    rw [MMP.Mori.coeff_principalDivisor, hφ]
    exact (Set.mem_setOf_eq ▸ hP).ne
  set Z : Set V := ⋃ P ∈ S, r '' (P.support : Set Y)
  have hZ : IsClosed Z := hS.isClosed_biUnion fun P _ => hcl _ P.idealSheaf.support.isClosed
  have hηZ : genericPoint V ∉ Z := by
    simp only [Z, Set.mem_iUnion]
    rintro ⟨P, hP, p, hp, hpη⟩
    have h1 : P.genericPoint ⤳ p := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hp
    have h2 : r P.genericPoint ⤳ genericPoint V := hpη ▸ h1.map r.continuous
    have h3 : r P.genericPoint = genericPoint V :=
      (h2.antisymm ((genericPoint_spec V).specializes trivial)).eq
    exact absurd (hx P h3) (not_le.mpr hP)
  let W : V.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have hηW : genericPoint V ∈ W := hηZ
  have hηY : genericPoint Y ∈ r ⁻¹ᵁ W := by
    change r (genericPoint Y) ∈ W
    rw [map_genericPoint_of_isDominant]
    exact hηW
  haveI : Nonempty W := ⟨⟨_, hηW⟩⟩
  haveI : Nonempty (r ⁻¹ᵁ W) := ⟨⟨_, hηY⟩⟩
  obtain ⟨s, hs⟩ := MMP.Threefold.Bridges.exists_germToFunctionField_eq_of_forall_zero_le_ord
    (r ⁻¹ᵁ W) x fun Γ ⟨p, hpΓ, hpW⟩ => by
      by_contra hneg
      exact hpW (Set.mem_biUnion (x := Γ) (not_le.mp hneg) ⟨p, hpΓ, rfl⟩)
  haveI := hr W
  refine ⟨V.germToFunctionField W (inv (r.app W) s), ?_⟩
  have hmem : r (genericPoint Y) ∈ W := hηY
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := V) hmem,
    functionFieldMap_algebraMap_stalk,
    Scheme.Hom.germ_stalkMap_apply, IsIso.inv_hom_id_apply]
  exact (Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hηY s).trans hs

/-- On an integral normal Noetherian scheme every invertible sheaf is `𝒪_Y(D)` for a Cartier
divisor `D`. -/
private theorem exists_isCartier_divisorialSheaf_iso {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    ∃ D : Divisor Y, D.IsCartier ∧ Nonempty (D.divisorialSheaf ≅ L) := by
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Y.toRingedSpace) L
  have : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    fun z => Y.isLocalRing z
  choose W hW a ha using fun y : Y =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  let F : LocalFrame L :=
    { W := W, mem := hW, a := a, isLocalGenerator := fun y V hV => ha y V hV, base := y₀ }
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

/-- **A divisor with relatively ample negative is negative on the closed relative cone.** If
`-D` has an `f`-ample Cartier multiple `A = m(-D)`, then by the relative Kleiman criterion
`(A · z) > 0` for every nonzero `z ∈ NE̅(X/Y)`, and `(D · z) = -(A · z)/m`. -/
private theorem curveForm_relativeToAbsolute_neg {X Y : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sY]
    {f : X ⟶ Y} (hfp : IsProjective f) (hfs : f ≫ sY = sX) {D : QDivisor X}
    (hD : D.IsQCartier) (hDa : (-D).HasRelativelyAmpleMultiple f)
    (z : RelativeNumericalCurveClasses sX f) (hz : z ∈ relativeClosedConeOfCurves sX f)
    (hz0 : z ≠ 0) : (QDivisor.curveForm sX D hD ∘ₗ relativeToAbsolute sX f) z < 0 := by
  obtain ⟨mA, hmA, LA, hLAc, hLA, hamp⟩ := hDa
  haveI := hLAc.isInvertibleModule_divisorialSheaf
  obtain ⟨A, ⟨e⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf LA.divisorialSheaf
  have hampA : MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf A) :=
    MMP.Fourfold.isRelativelyAmple_of_iso _ e hamp
  have hpos := (isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sY sX f
    hfp hfs A).mp hampA z hz hz0
  have hneg : (-D).IsQCartier := ⟨mA, by exact_mod_cast hmA.ne', LA, hLA, hLAc⟩
  have hform : QDivisor.curveForm sX D hD = (-(1 / (mA : ℝ))) •
      NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ A) := by
    refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle, LinearMap.smul_apply,
      NumericalCurveClasses.intersectionNumber_numericalClass,
      OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle,
      show C.degree k (MMP.CartierDivisor.sheaf A) = C.degree k LA.divisorialSheaf
        from (degreeOn_eq_of_iso k sX C.ι C.dim_le e).symm]
    have h1 := QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul k sX C.ι C.dim_le
      (Divisor.degreeOn_add k sX C.ι C.dim_le) (-D) hneg hmA LA hLAc hLA
    have h2 := MMP.Fourfold.intersectionNumber_smul sX C.ι C.dim_le (-D) hneg (-1)
      (by simpa using hD)
    rw [MMP.Fourfold.intersectionNumber_congr sX C.ι C.dim_le _ hD (by simp), h1] at h2
    rw [h2, ProperCurve.degree_divisorialSheaf C LA hLAc, smul_eq_mul]
    push_cast
    ring
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [LinearMap.comp_apply, isNaturalRelativeMap_relativeToAbsolute sX f Z, hform,
    LinearMap.smul_apply, NumericalCurveClasses.intersectionNumber_numericalClass]
  rw [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass] at hpos
  have : (0 : ℝ) < mA := by exact_mod_cast hmA
  rw [smul_eq_mul]
  nlinarith [div_pos one_pos this]

/-- **Cartier descent along the Mori contraction** (Kollár–Mori 3.7(4)). A Cartier divisor `N`
on `Y` of degree zero on every curve contracted by `r` is `r^*M + div φ` for a Cartier divisor
`M` of `V` and a rational function `φ`: `𝒪_Y(N)` descends along the contraction of the
`(K + Γ)`-negative relative cone. -/
private theorem exists_sub_pullback_eq_principalDivisor {Y V : Scheme.{0}}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [QuasiCompact sY] {r : Y ⟶ V}
    [IsDominant r] (hr : IsContraction sY sV r)
    (hY : MMP.Mori.IsProjectiveVariety k sY) (hV : MMP.Mori.IsProjectiveVariety k sV)
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {Γ : QDivisor Y} (hΓ : IsKltPair sY Γ)
    (hΓa : (-(Divisor.toQDivisor K + Γ)).HasRelativelyAmpleMultiple r)
    {N : Divisor Y} (hNc : N.IsCartier)
    (hL : ∀ C : ProperCurve sY, C.IsContractedBy r →
      haveI := hNc.isInvertibleModule_divisorialSheaf
      C.degree k N.divisorialSheaf = 0) :
    ∃ (M : Divisor V) (hM : M.IsCartier) (φ : (RationalFunctions Y)ˣ),
      N - M.pullback (f := r) hM
        (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp r M) = principalDivisor φ := by
  haveI : AlgebraicGeometry.IsProjectiveVariety k sY := hY
  haveI : AlgebraicGeometry.IsProjectiveVariety k sV := hV
  have hrs := hr.comp_eq
  have hrp : IsProjective r := IsProjectiveMorphism.isProjective hr.isProjectiveMorphism
  have hP := hΓ.1
  have hklt : MMP.Mori.IsKltPair sY n K Γ :=
    (MMP.Fourfold.isKltPair_iff_mori_isKltPair sY hK hP).mp hΓ
  have hset : IsProjectiveSetting k sY sV r := ⟨inferInstance, inferInstance, hY, hV, hrs⟩
  have hB0 : 0 ≤ Γ := fun P => hP.nonneg P
  set F := (relativeClosedConeOfCurves sY r : Set (RelativeNumericalCurveClasses sY r))
  have hFace : IsExtremalFace ℝ F F :=
    ⟨subset_rfl, isCone_coe _, fun u hu v hv => add_mem hu hv, fun u hu v hv _ => ⟨hu, hv⟩⟩
  have hF : IsNegativeExtremalFace ℝ F
      ((QDivisor.curveForm sY (Divisor.toQDivisor K + Γ) hklt.1.2.2).comp
        (relativeToAbsolute sY r)) F :=
    ⟨hFace, fun u hu v hv => add_mem hu hv, fun z hz hz0 =>
      curveForm_relativeToAbsolute_neg hrp hrs hklt.1.2.2 hΓa z hz hz0⟩
  have hψ : IsRelativeContractionOfFace r F r (𝟙 V) :=
    ⟨hFace, isProjectiveMorphism_id _, Category.comp_id r, hr.isIso_app, fun C hC =>
      ⟨fun _ => subset_closure (relativeClass_mem_relativeConeOfCurves hC), fun _ => hC⟩⟩
  haveI := hNc.isInvertibleModule_divisorialSheaf
  obtain ⟨LZ, hLZ, ⟨e⟩⟩ := exists_isInvertible_iso_pullback_of_isRelativeContractionOfFace hset
    hklt hB0 hF hψ N.divisorialSheaf (fun C hC _ => hL C hC)
  haveI := hLZ
  obtain ⟨M, hM, ⟨eM⟩⟩ := exists_isCartier_divisorialSheaf_iso LZ
  have hBM := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp r M
  obtain ⟨eP⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hM r hBM
  obtain ⟨φ, hφ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e ≪≫ (Scheme.Modules.pullback r).mapIso eM.symm ≪≫ eP.symm)
  exact ⟨M, hM, φ, hφ⟩

/-- **Cartier descent of the adjoint divisor** (Kollár–Mori 3.7(4)). In the Mori setting, if
`K_Y + B ≡_V 0` then for every sufficiently divisible `m` there are a nonzero rational
`m`-canonical form `α` on `Y` and a Cartier divisor `M` on `V` with `div α + mB = r^*M`:
`m(K_Y + B)` is Cartier, numerically trivial over `V`, hence `𝒪_Y(m(K_Y + B)) ≅ r^*𝒪_V(M)`, and
the intervening rational function is absorbed into `α`. -/
private theorem exists_ordForm_add_eq_pullback {Y V : Scheme.{0}}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [QuasiCompact sY] {r : Y ⟶ V}
    [IsDominant r] (hr : IsContraction sY sV r)
    (hY : MMP.Mori.IsProjectiveVariety k sY) (hV : MMP.Mori.IsProjectiveVariety k sV)
    (hQ : IsQFactorial sY) {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {Γ : QDivisor Y} (hΓ : IsKltPair sY Γ)
    (hΓa : (-(Divisor.toQDivisor K + Γ)).HasRelativelyAmpleMultiple r) {B : QDivisor Y}
    (hD : MMP.Flips.IsNumericallyTrivialOver k sY r
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B))) :
    ∃ m₁ : ℕ, 0 < m₁ ∧ ∀ m : ℕ, 0 < m → m₁ ∣ m →
      ∃ (α : RationalPluriForms sY n m) (M : Divisor V) (hM : M.IsCartier),
        α ≠ 0 ∧ ∀ P : MMP.Mori.PrimeDivisor Y,
          (P.ordForm α : ℚ) + (m : ℚ) * B P =
            ((M.pullback (f := r) hM
              (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp r M)) P : ℚ) := by
  classical
  haveI : AlgebraicGeometry.IsProjectiveVariety k sY := hY
  haveI : AlgebraicGeometry.IsProjectiveVariety k sV := hV
  have hrs := hr.comp_eq
  have hrp : IsProjective r := IsProjectiveMorphism.isProjective hr.isProjectiveMorphism
  have hYv : IsNormalVariety k sY := hQ.1
  haveI : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  have hn := hK.topologicalKrullDim_eq
  -- an integral Cartier multiple of `K + B`
  obtain ⟨m₁, hm₁, N₁, hN₁, hN₁c⟩ :=
    (isQCartier_of_isQFactorial sY hQ (Divisor.toQDivisor K + B)).exists_pos
  refine ⟨m₁, hm₁, fun m hm hdvd => ?_⟩
  obtain ⟨c, rfl⟩ := hdvd
  set N : Divisor Y := (c : ℤ) • N₁ with hNdef
  have hNc : N.IsCartier := hN₁c.zsmul _
  have hNq : Divisor.toQDivisor N = ((m₁ * c : ℕ) : ℤ) • (Divisor.toQDivisor K + B) := by
    rw [hNdef, map_zsmul, hN₁, smul_smul]
    push_cast
    ring_nf
  -- `N` has degree zero on the contracted curves
  have hL : ∀ C : ProperCurve sY, C.IsContractedBy r →
      haveI := hNc.isInvertibleModule_divisorialSheaf
      C.degree k N.divisorialSheaf = 0 := by
    haveI := hNc.isInvertibleModule_divisorialSheaf
    exact fun C hC => MMP.Flips.IsNumericallyTrivialOver.degree_eq_zero hD hm hNq hNc C hC
  -- descent along the klt-negative contraction
  obtain ⟨M, hM, φ, hφ⟩ := exists_sub_pullback_eq_principalDivisor hr hY hV hK hΓ hΓa hNc hL
  have hBM := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp r M
  -- a nonzero rational `m`-canonical form and its divisor
  letI := functionFieldAlgebra sY
  obtain ⟨b⟩ := exists_basis_topForms (sX := sY) hn
  set ρ₀ : RationalPluriForms sY n ((m₁ * c : ℕ) : ℤ) :=
    (ZTensorPower.basis b ((m₁ * c : ℕ) : ℤ)) ()
  have hρ₀ : ρ₀ ≠ 0 := (ZTensorPower.basis b ((m₁ * c : ℕ) : ℤ)).ne_zero ()
  obtain ⟨χ, hχ⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYv hK hρ₀
  -- the rational function absorbing `φ` and `χ`
  set Z₀ : irreducibleComponents Y := pointComponent (genericPoint Y)
  have hcomp : ∀ Γ : MMP.Mori.PrimeDivisor Y, Γ.component = Z₀ := fun Γ =>
    (MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := Y)).elim _ _
  set ψ : (RationalFunctions Y)ˣ := (φ * χ)⁻¹
  set w : Y.functionField :=
    MMP.Threefold.Mori.Helpers.evalFF Z₀ (ψ : RationalFunctions Y)
  have hw0 : w ≠ 0 := (ψ.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Z₀)).ne_zero
  have hordw : ∀ Γ : MMP.Mori.PrimeDivisor Y,
      Y.ord w Γ.genericPoint = -(Γ.ord φ + Γ.ord χ) := by
    intro Γ
    have h1 := MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord Γ ψ
    rw [hcomp Γ] at h1
    rw [← h1, PrimeDivisor.ord_inv, PrimeDivisor.ord_mul]
  refine ⟨w • ρ₀, M, hM, smul_ne_zero hw0 hρ₀, fun P => ?_⟩
  have hNP := congrArg (fun G : Divisor Y => DivisorWithCoeffs.coeff G P) hφ
  have hχP := congrArg (fun G : Divisor Y => DivisorWithCoeffs.coeff G P) hχ
  have hqP := congrArg (fun G : QDivisor Y => DivisorWithCoeffs.coeff G P) hNq
  simp only [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, coeff_divisorOfForm,
    DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add,
    zsmul_eq_mul, smul_eq_mul] at hNP hχP hqP
  change ((P.ordForm (w • ρ₀) : ℤ) : ℚ) + ((m₁ * c : ℕ) : ℚ) * B.coeff P =
    (((M.pullback (f := r) hM hBM).coeff P : ℤ) : ℚ)
  rw [P.ordForm_smul_of_topologicalKrullDim_eq hn hw0 hρ₀, hordw P]
  have hNP' : ((N.coeff P : ℤ) : ℚ) - (((M.pullback (f := r) hM hBM).coeff P : ℤ) : ℚ) =
      ((P.ord φ : ℤ) : ℚ) := by exact_mod_cast hNP
  have hχP' : ((P.ordForm ρ₀ : ℤ) : ℚ) - ((m₁ * c : ℕ) : ℚ) * ((K.coeff P : ℤ) : ℚ) =
      ((P.ord χ : ℤ) : ℚ) := by
    have := hχP
    push_cast at this ⊢
    exact_mod_cast this
  push_cast at hqP hNP' hχP' ⊢
  linear_combination hχP' - hqP + hNP'

/-- A strict specialization is a strict inequality in the order of the points of a scheme. -/
private theorem lt_of_specializes_of_ne {Y : Scheme} {a b : Y} (h : b ⤳ a) (hne : a ≠ b) :
    a < b := by
  refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr h) fun h' => hne ?_
  exact (h.antisymm (Scheme.le_iff_specializes.mp h')).eq.symm

open Order in
/-- **Lifting specializations along a closed map.** If `r` is closed, the dimension of the
closure of `r y` is at most that of the closure of `y`. -/
private theorem height_apply_le_height_of_isClosedMap {Y V : Scheme} (r : Y ⟶ V)
    (hr : IsClosedMap r) (y : Y) (hfin : height (r y) < ⊤) : height (r y) ≤ height y := by
  have key : ∀ (n : ℕ) (y : Y), height (r y) < ⊤ → (n : ℕ∞) ≤ height (r y) →
      (n : ℕ∞) ≤ height y := by
    intro n
    induction n with
    | zero => intros; simp
    | succ n ih =>
      intro y hy hn
      have hlt : (n : ℕ∞) < height (r y) :=
        lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hn
      obtain ⟨w, hw, hwn⟩ := (coe_lt_height_iff hy).mp hlt
      have hsp : r y ⤳ w := Scheme.le_iff_specializes.mp hw.le
      have hcl : w ∈ r '' closure {y} := by
        rw [← (hr _ (isClosed_closure (s := {y}))).closure_eq]
        refine closure_mono (Set.image_mono subset_closure) ?_
        rw [Set.image_singleton]
        exact specializes_iff_mem_closure.mp hsp
      obtain ⟨y', hy', rfl⟩ := hcl
      have hy'y : y' < y := by
        refine lt_of_specializes_of_ne (specializes_iff_mem_closure.mpr hy') ?_
        rintro rfl
        exact hw.ne rfl
      have := ih y' (lt_of_le_of_lt (height_mono hw.le) hy) hwn.ge
      calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
        _ ≤ height y' + 1 := by gcongr
        _ ≤ height y := height_add_one_le hy'y
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin.ne
  rw [← hm]
  exact key m y hfin hm.le

/-- On an integral variety of dimension `d` over `k`, `height y + coheight y = d`. -/
private theorem height_add_coheight_eq {Y : Scheme.{0}} [IsIntegral Y] (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sY] {d : ℕ} (hd : topologicalKrullDim Y = d) (y : Y) :
    Order.height y + Order.coheight y = (d : ℕ∞) := by
  letI : Y.Over (Spec (.of k)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of k)) := (inferInstance : LocallyOfFiniteType sY)
  have := MMP.height_add_coheight_eq_krullDim k y
  rw [Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim, hd] at this
  exact WithBot.coe_injective (by rw [this]; rfl)

/-- Every point of an irreducible scheme is a specialization of the generic point: in the order
of points, the generic point is the top. -/
private theorem le_genericPoint {Y : Scheme} [IrreducibleSpace Y] (y : Y) : y ≤ genericPoint Y :=
  Scheme.le_iff_specializes.mpr ((genericPoint_spec Y).specializes trivial)

/-- A point of an irreducible scheme of coheight zero is the generic point. -/
private theorem eq_genericPoint_of_coheight_eq_zero {Y : Scheme} [IrreducibleSpace Y] {y : Y}
    (h : Order.coheight y = 0) : y = genericPoint Y :=
  ((Scheme.le_iff_specializes.mp (Order.coheight_eq_zero.mp h (le_genericPoint y))).antisymm
    ((genericPoint_spec Y).specializes trivial)).eq

/-- **Points over the generic point of a surface have coheight at most one.** For a closed map
`r : Y ⟶ V` from a threefold to a surface over `k`, a point `y` with `r y = η_V` has
`coheight y ≤ 1`: its closure dominates `V`, so has dimension at least two. -/
private theorem coheight_le_one_of_map_eq_genericPoint {Y V : Scheme.{0}} [IsIntegral Y]
    [IsIntegral V] {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [LocallyOfFiniteType sY]
    [LocallyOfFiniteType sV] (r : Y ⟶ V) (hcl : IsClosedMap r) (hdY : topologicalKrullDim Y = 3)
    (hdV : topologicalKrullDim V = 2) {y : Y} (hy : r y = genericPoint V) :
    Order.coheight y ≤ 1 := by
  have e1 := height_add_coheight_eq sY hdY y
  have e2 := height_add_coheight_eq sV hdV (genericPoint V)
  rw [Order.coheight_eq_zero.mpr fun b _ => le_genericPoint b, add_zero] at e2
  have hle := height_apply_le_height_of_isClosedMap r hcl y
    (by rw [hy, e2]; exact ENat.coe_lt_top 2)
  rw [hy, e2] at hle
  have hct : Order.coheight y ≠ ⊤ := by
    intro h
    rw [h] at e1
    simp at e1
  have hht : Order.height y ≠ ⊤ := by
    intro h
    rw [h] at e1
    simp at e1
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hct
  obtain ⟨h', hh⟩ := ENat.ne_top_iff_exists.mp hht
  rw [← hc, ← hh] at e1
  rw [← hh] at hle
  rw [← hc]
  have e1' : h' + c = 3 := by exact_mod_cast e1
  have hle' : 2 ≤ h' := by exact_mod_cast hle
  exact_mod_cast (show c ≤ 1 by omega)

/-- **Places of the generic fibre are horizontal prime divisors.** Let `r : Y ⟶ V` be a closed
dominant morphism over `k` from a proper normal threefold to a surface. A valuation subring
`R ≠ k(Y)` of `k(Y)` containing `k(V)` is the local ring of a prime divisor `P` of `Y` dominating
`V`: its centre on `Y` lies over the generic point of `V`, so has coheight one, and a valuation
ring dominated by `R` equals `R`. -/
private theorem exists_primeDivisor_of_valuationSubring
    {Y V : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V]
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [IsProper sY] [LocallyOfFiniteType sY]
    [LocallyOfFiniteType sV] (r : Y ⟶ V) [IsDominant r] (hrs : r ≫ sV = sY)
    (hcl : IsClosedMap r) (hdY : topologicalKrullDim Y = 3) (hdV : topologicalKrullDim V = 2)
    (R : ValuationSubring Y.functionField) (hR : ∀ y : V.functionField, functionFieldMap r y ∈ R)
    (hRtop : R ≠ ⊤) :
    ∃ P : MMP.Mori.PrimeDivisor Y, r P.genericPoint = genericPoint V ∧
      ∀ x : Y.functionField, x ≠ 0 → (x ∈ R ↔ 0 ≤ Y.ord x P.genericPoint) := by
  have hk : letI := functionFieldAlgebra sY
      ∀ c : k, algebraMap k Y.functionField c ∈ R := by
    subst hrs
    letI := functionFieldAlgebra sV
    letI := functionFieldAlgebra (r ≫ sV)
    letI := functionFieldMapAlgebra r
    haveI := isScalarTower_functionFieldMap sV r
    intro c
    rw [IsScalarTower.algebraMap_apply k V.functionField Y.functionField c]
    exact hR _
  obtain ⟨y, hyR, hym⟩ := exists_dominates_valuationSubring_of_isProper sY R hk
  -- the centre lies over the generic point of `V`
  have hv : r y = genericPoint V := by
    by_contra hv
    have hco : Order.coheight (r y) ≠ 0 := fun h0 => hv (eq_genericPoint_of_coheight_eq_zero h0)
    have hnf : ¬ IsField (V.presheaf.stalk (r y)) := by
      intro hF
      have h1 := ringKrullDim_stalk_eq_coheight (r y)
      rw [ringKrullDim_eq_zero_of_isField hF] at h1
      exact hco (by exact_mod_cast h1.symm)
    obtain ⟨a, ha, ha0⟩ : ∃ a ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk (r y)), a ≠ 0 := by
      by_contra h
      push Not at h
      exact hnf ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr
        (eq_bot_iff.mpr fun a ha => (Submodule.mem_bot _).mpr (h a ha)))
    have h1 := hym _ (map_nonunit (r.stalkMap y).hom a ha)
    rw [← functionFieldMap_algebraMap_stalk] at h1
    set b := algebraMap (V.presheaf.stalk (r y)) V.functionField a
    have hb0 : b ≠ 0 := fun h0 =>
      ha0 (IsFractionRing.injective (V.presheaf.stalk (r y)) V.functionField
        (h0.trans (map_zero _).symm))
    have hu : (functionFieldMap r b) * (functionFieldMap r b⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hb0, map_one]
    have h2 := (R.valuation_le_one_iff _).mpr (hR b⁻¹)
    rw [R.mem_nonunits_iff] at h1
    have h3 := congrArg R.valuation hu
    rw [map_mul, map_one] at h3
    have : R.valuation (functionFieldMap r b) * R.valuation (functionFieldMap r b⁻¹) < 1 :=
      mul_lt_one_of_lt_of_le h1 h2
    rw [h3] at this
    exact lt_irrefl _ this
  -- the centre is not the generic point of `Y`
  have hyη : y ≠ genericPoint Y := by
    rintro rfl
    apply hRtop
    rw [eq_top_iff]
    intro x _
    have hid : @algebraMap (Y.presheaf.stalk (genericPoint Y)) Y.functionField _ _
        (stalkFunctionFieldAlgebra Y (genericPoint Y)) x = x := by
      change (Y.presheaf.stalkSpecializes _).hom x = x
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    have := hyR x
    rwa [hid] at this
  -- `y` has coheight one
  have hc1 : Order.coheight y = 1 :=
    le_antisymm (coheight_le_one_of_map_eq_genericPoint (sY := sY) (sV := sV) r hcl hdY hdV hv)
      (ENat.one_le_iff_ne_zero.mpr fun h0 => hyη (eq_genericPoint_of_coheight_eq_zero h0))
  set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hc1
  have hPg : P.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hc1
  refine ⟨P, (congrArg (fun z => r z) hPg).trans hv, fun x hx0 => ?_⟩
  change x ∈ R ↔ 0 ≤ Y.ord x (P : AlgebraicGeometry.PrimeDivisor Y).genericPoint
  rw [hPg, ← Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hc1 hx0]
  haveI := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hc1
  let f : Y.presheaf.stalk y →+* R :=
    (algebraMap (Y.presheaf.stalk y) Y.functionField).codRestrict R hyR
  haveI : IsLocalHom f := ⟨fun a hu => by
    by_contra ha
    have := hym a ((IsLocalRing.mem_maximalIdeal _).mpr ha)
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at this
    obtain ⟨_, hm⟩ := this
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hu⟩
  have hbij := bijective_rangeRestrict_comp_of_valuationRing f R.subtype (by ext; rfl)
  constructor
  · intro hxR
    obtain ⟨a, ha⟩ := hbij.2 ⟨x, ⟨⟨x, hxR⟩, rfl⟩⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a, rfl⟩
    exact hyR a

/-- A *normal crepant dlt model* `p : (U, Δ) ⟶ (Y, B)` of a pair on a normal variety `Y`, for
the canonical divisor `K` of `Y`: `p` is a projective birational morphism from a normal variety
`U`, `Δ` is the crepant boundary of `(Y, B)` on `U` and `(U, Δ)` is dlt. -/
private structure IsCrepantDltModel {Y U : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] (sY : Y ⟶ Spec (.of k))
    (K : Divisor Y) (B : QDivisor Y) (p : U ⟶ Y) (Δ : QDivisor U) : Prop where
  isNormalVariety_base : IsNormalVariety k sY
  isProjectiveMorphism : IsProjectiveMorphism p
  isBirationalMorphism : IsBirationalMorphism p
  isNormalVariety : IsNormalVariety k (p ≫ sY)
  isDltPair : MMP.Intersection.IsDltPair (p ≫ sY) Δ
  isCrepantBoundary : ∃ n : ℕ, IsCrepantBoundary sY n K B p isNormalVariety isBirationalMorphism Δ

/-- A projective birational morphism with crepant boundary for some canonical divisor of the
projective variety `Y` and dlt total space is a normal crepant dlt model for any canonical
divisor `K` of `Y`: discrepancies do not depend on the choice of the canonical divisor. -/
private theorem isCrepantDltModel_of {Y U : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    {sY : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsProjectiveVariety k sY) {n : ℕ} {K : Divisor Y}
    (hK : K.IsCanonicalDivisor sY n) {B : QDivisor Y} {p : U ⟶ Y} {Δ : QDivisor U}
    (hpp : IsProjectiveMorphism p)
    (hcb : ∃ (KY : Divisor Y) (hU : IsNormalVariety k (p ≫ sY)) (hp : IsBirationalMorphism p),
      IsCrepantBoundary sY 3 KY B p hU hp Δ)
    (hdlt : MMP.Intersection.IsDltPair (p ≫ sY) Δ) : IsCrepantDltModel sY K B p Δ := by
  obtain ⟨KY, hU, hp, hcb⟩ := hcb
  have hYv : IsNormalVariety k sY := ⟨hY.1, inferInstance⟩
  exact ⟨hYv, hpp, hp, hU, hdlt, 3, fun F => MMP.Spreading.isDiscrepancy_of_linearlyEquivalent
    (hcb F) (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sY hYv hK (hcb F).2.1)⟩

/-- On a pair `(U, Δ)`, `div τ + Δ` is `ℚ`-Cartier for every nonzero rational top form `τ`:
`div τ` is a canonical divisor, linearly equivalent to the one of the pair. -/
private theorem isQCartier_divisorOfForm_add_of_isPair {U : Scheme.{0}} [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] [CompactSpace U] {sU : U ⟶ Spec (.of k)}
    [LocallyOfFiniteType sU] {Δ : QDivisor U} (hP : MMP.Mori.IsPair sU Δ) {d : ℕ}
    (hd : topologicalKrullDim U = d) (τ : RationalPluriForms sU d ((1 : ℕ) : ℤ))
    (hτ : τ ≠ 0) : (Divisor.toQDivisor (divisorOfForm τ) + Δ).IsQCartier := by
  obtain ⟨hUv, _n, K0, hK0, hK0q⟩ := hP
  letI := functionFieldAlgebra sU
  set e := (PiTensorProduct.subsingletonEquiv (0 : Fin 1) :
    PiTensorProduct U.functionField (fun _ : Fin 1 => ⋀[U.functionField]^d Ω[U.functionField⁄k])
      ≃ₗ[U.functionField] ⋀[U.functionField]^d Ω[U.functionField⁄k])
  let ω : RationalTopForms sU d := e τ
  have hω : RationalTopForms.toPluriForms sU ω = τ := by
    change PiTensorProduct.tprod U.functionField (fun _ : Fin 1 => e τ) = τ
    exact e.injective (PiTensorProduct.subsingletonEquiv_apply_tprod _ _)
  have hω0 : ω ≠ 0 := fun h0 =>
    hτ (e.injective (h0.trans (map_zero e).symm))
  have hKω := MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hUv hd hω0
  have := hK0q.add_of_linearlyEquivalent
    (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sU hUv hK0 hKω)
  rwa [topFormDivisor, hω] at this

/-- **The divisor equation on a crepant dlt lift.** If `div α + mB = r^*M` on `Y` and
`p : (U, Δ) ⟶ (Y, B)` is a crepant dlt lift, then `div(p^*α) + mΔ = (p ≫ r)^*M` on `U`: along
every prime divisor `F` of `U` the discrepancy `a(F, Y, B) = -Δ_F` is computed by `α`. -/
private theorem ordForm_pullback_add_eq_of_isCrepantDltLift {Y V U : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    {sY : Y ⟶ Spec (.of k)} {r : Y ⟶ V} [IsDominant r] {n : ℕ} {K : Divisor Y}
    {B : QDivisor Y} {M : Divisor V} (hM : M.IsCartier) {M' : Divisor Y}
    (hM' : M.IsPullback r (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp r M) M')
    {m : ℕ} (hm : 0 < m) {α : RationalPluriForms sY n m} (hα : α ≠ 0)
    (hB : ∀ Γ : MMP.Mori.PrimeDivisor Y, (Γ.ordForm α : ℚ) + m * B.coeff Γ = M'.coeff Γ)
    (p : U ⟶ Y) [IsDominant p] {Δ : QDivisor U} (hlift : IsCrepantDltModel sY K B p Δ)
    (hK : K.IsCanonicalDivisor sY n) {MU : Divisor U}
    (hMU : M.IsPullback (p ≫ r)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (p ≫ r) M) MU)
    (F : MMP.Mori.PrimeDivisor U) :
    ((F.ordForm (pullbackRationalPluriForms sY p α) : ℤ) : ℚ) + m * Δ.coeff F = MU.coeff F := by
  have hYv : IsNormalVariety k sY := hlift.isNormalVariety_base
  let D : DivisorOver k sY := ⟨U, p, hlift.isNormalVariety, hlift.isBirationalMorphism, F⟩
  have h1 := isDiscrepancy_of_ordForm_add_eq_pullback hYv hK r hM hM' hm hα hB D hMU
  obtain ⟨n', hn'⟩ := hlift.isCrepantBoundary
  have h2 := hn' F
  have hnn : n' = n := by
    have e1 := (hn' F).2.1.topologicalKrullDim_eq
    have e2 := hK.topologicalKrullDim_eq
    exact_mod_cast e1.symm.trans e2
  subst hnn
  have := IsDiscrepancy.eq h1 h2
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  change ((D.ordPullback α : ℤ) : ℚ) + m * Δ.coeff F = MU.coeff F
  rw [div_eq_iff hm0] at this
  push_cast at this
  linarith

/-- **The order of a power of a form.** On a normal variety of dimension `d` over a perfect field,
`ord_Γ(f · v^{⊗m}) = ord_Γ f + m · ord_Γ v` for a nonzero `d`-form `v` and `f ≠ 0`. -/
private theorem ordForm_smul_formPow {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] (Γ : MMP.Mori.PrimeDivisor X) {d : ℕ}
    (hd : topologicalKrullDim X = d)
    {v : letI := functionFieldAlgebra sX; ⋀[X.functionField]^d Ω[X.functionField⁄k]}
    (hv : v ≠ 0) {f : X.functionField} (hf : f ≠ 0) (m : ℕ) :
    letI := functionFieldAlgebra sX
    Γ.ordForm (sX := sX) (d := d) (m := (m : ℤ)) (f • formPow v m) =
      X.ord f Γ.genericPoint +
        m * Γ.ordForm (sX := sX) (d := d) (m := ((1 : ℕ) : ℤ)) (formPow v 1) := by
  letI := functionFieldAlgebra sX
  have hdt := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hdt b
  set c := b.repr v ()
  have hv' : v = c • b () := (basis_unit_repr_smul b v).symm
  have hc : c ≠ 0 := by
    intro h0
    apply hv
    rw [hv', h0, zero_smul]
  have key : ∀ (a : ℕ) (g : X.functionField), g ≠ 0 →
      Γ.ordForm (sX := sX) (d := d) (m := (a : ℤ)) (g • formPow (b ()) a) =
        X.ord g Γ.genericPoint + a * N := by
    intro a g hg
    have hb0 : (formPow (b ()) a : PluriForms k X.functionField d a) ≠ 0 := by
      rw [← ZTensorPower.basis_natCast]
      exact (ZTensorPower.basis b a).ne_zero ()
    rw [hN (a : ℤ) (g • formPow (b ()) a) (smul_ne_zero hg hb0)]
    congr 2
    exact repr_smul_formPow b a g
  have e1 : (f • formPow v m : PluriForms k X.functionField d m) =
      ((f * c ^ m) • formPow (b ()) m : PluriForms k X.functionField d m) := by
    rw [hv', formPow_smul, smul_smul]
  have e2 : (formPow v 1 : PluriForms k X.functionField d (1 : ℕ)) =
      (c • formPow (b ()) 1 : PluriForms k X.functionField d (1 : ℕ)) := by
    rw [hv', formPow_smul, pow_one]
  rw [e1, e2, key _ _ (mul_ne_zero hf (pow_ne_zero _ hc)), key _ _ hc,
    Scheme.ord_mul hf (pow_ne_zero _ hc), ← zpow_natCast, MMP.Mori.ord_zpow _ hc]
  push_cast
  ring

open exteriorPower in
/-- **Forms of regular functions are regular.** Along a prime divisor `Γ` of a normal variety of
dimension `d`, the form `dy₁ ∧ ⋯ ∧ dy_d` of elements `yᵢ` of the local ring `𝒪_{X,Γ}` has
nonnegative order. -/
private theorem zero_le_ordForm_formPow_ιMulti {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] (Γ : MMP.Mori.PrimeDivisor X) {d : ℕ}
    (hd : topologicalKrullDim X = d) (y : Fin d → X.presheaf.stalk Γ.genericPoint) :
    letI := functionFieldAlgebra sX
    0 ≤ Γ.ordForm (sX := sX) (d := d) (m := ((1 : ℕ) : ℤ))
      (formPow (ιMulti X.functionField d fun i =>
        KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField (y i))) 1) := by
  letI := functionFieldAlgebra sX
  letI := stalkAlgebra sX Γ.genericPoint
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  have hdt := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd
  obtain ⟨σ, hσ, h0⟩ := Γ.exists_topForms_generator (sX := sX) hdt
  have e := MMP.Threefold.Resolution.ordForm_eq_ord_formCoeff sX Γ.genericPoint Γ
    (MMP.Flips.primeDivisor_genericPoint_mem_support Γ) hσ h0 (d := d) (m := ((1 : ℕ) : ℤ))
    (formPow (ιMulti X.functionField d fun i =>
      KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField (y i))) 1)
  refine le_of_le_of_eq ?_ e.symm
  obtain ⟨a, ha⟩ : ∃ a : X.presheaf.stalk Γ.genericPoint,
      a • σ = ιMulti (X.presheaf.stalk Γ.genericPoint) d fun i =>
        KaehlerDifferential.D k (X.presheaf.stalk Γ.genericPoint) (y i) :=
    Submodule.mem_span_singleton.mp (hσ ▸ Submodule.mem_top)
  have hmap : (ιMulti X.functionField d fun i =>
      KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField (y i))) =
      algebraMap _ X.functionField a •
        topFormsMap k (X.presheaf.stalk Γ.genericPoint) X.functionField d σ := by
    rw [algebraMap_smul, ← map_smul, ha, topFormsMap_ιMulti]
    simp only [KaehlerDifferential.map_D]
  have hc : formCoeff (k := k) (m := ((1 : ℕ) : ℤ)) (X.presheaf.stalk Γ.genericPoint) hσ h0
      (formPow (ιMulti X.functionField d fun i =>
        KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField (y i))) 1) =
      algebraMap _ X.functionField a := by
    rw [hmap, formPow_smul, pow_one, formCoeff, ← topFormsBasis_apply
      (A := X.presheaf.stalk Γ.genericPoint) hσ h0 (), repr_smul_formPow]
  rw [hc]
  rcases eq_or_ne (algebraMap (X.presheaf.stalk Γ.genericPoint) X.functionField a) 0 with h | h
  · rw [h]
    simp [Scheme.ord_zero]
  · exact (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Γ) h).mp ⟨a, rfl⟩

/-- **Pull-backs vanish along dominating prime divisors.** If `q : U ⟶ V` is dominant and
`P` is a prime divisor of `U` with `q(η_P) = η_V`, the pull-back of a Cartier divisor of `V` has
coefficient zero along `P`: near `η_V` the divisor has local equation `1`. -/
private theorem coeff_isPullback_eq_zero_of_map_genericPoint {U V : Scheme.{0}} [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {q : U ⟶ V} [IsDominant q] {M : Divisor V}
    {hB : ∀ Z : irreducibleComponents U, q (componentGenericPoint U Z) ∉ M.supp}
    {MU : Divisor U} (hMU : M.IsPullback q hB MU) (P : MMP.Mori.PrimeDivisor U)
    (hP : q P.genericPoint = genericPoint V) : MU.coeff P = 0 := by
  let W : V.Opens := ⟨(M.supp : Set V)ᶜ, M.isClosed_supp.isOpen_compl⟩
  have hηW : genericPoint V ∈ W := by
    change genericPoint V ∉ (M.supp : Set V)
    intro h
    obtain ⟨E, hE, hηE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    have hsp : E.genericPoint ⤳ genericPoint V := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hηE
    have heq : E.genericPoint = genericPoint V :=
      (hsp.antisymm ((genericPoint_spec V).specializes trivial)).eq
    have h1 : Order.coheight E.genericPoint = 1 :=
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
    rw [heq, Order.coheight_eq_zero.mpr fun b _ => le_genericPoint b] at h1
    exact zero_ne_one h1
  have hloc : M.IsLocalEquation W 1 := by
    intro E hE
    rw [PrimeDivisor.ord_one]
    by_contra h
    obtain ⟨x, hxE, hxW⟩ := hE
    exact hxW (DivisorWithCoeffs.support_subset_supp h hxE)
  have := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hMU hloc P (hP ▸ hηW)
    (pointComponent (genericPoint V))
  rw [this, Units.val_one, map_one, map_one]
  simp [Scheme.ord_one]

/-- The image of a prime divisor under a closed map onto an irreducible scheme is everything
exactly when its generic point maps to the generic point. -/
private theorem image_support_eq_univ_iff {X Z : Scheme.{0}} [IrreducibleSpace Z] (f : X ⟶ Z)
    (hcl : IsClosedMap f) (P : MMP.Mori.PrimeDivisor X) :
    f '' (P.support : Set X) = Set.univ ↔ f P.genericPoint = genericPoint Z := by
  have himg : f '' (P.support : Set X) = closure {f P.genericPoint} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine subset_antisymm ?_ ?_
    · exact (image_closure_subset_closure_image f.continuous).trans (by rw [Set.image_singleton])
    · refine closure_minimal ?_ (hcl _ isClosed_closure)
      rw [Set.singleton_subset_iff]
      exact ⟨_, subset_closure rfl, rfl⟩
  rw [himg]
  constructor
  · intro h
    have : IsGenericPoint (f P.genericPoint) Set.univ := by
      rw [isGenericPoint_def, h]
    exact this.eq (genericPoint_spec Z)
  · intro h
    rw [h]
    exact (genericPoint_spec Z).def

/-- On a prime divisor `F` of `U` not contained in the exceptional locus of `μ`, the crepant
boundary has the coefficient of the strict transform of `B`. -/
private theorem coeff_eq_of_not_subset_of_isCrepantBoundary {Y X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of k)} {n : ℕ}
    {K : Divisor X} {B : QDivisor X} {μ : Y ⟶ X} [IsProper μ] {hY : IsNormalVariety k (μ ≫ sX)}
    {hμ : IsBirationalMorphism μ} {ΔY : QDivisor Y}
    (h : IsCrepantBoundary sX n K B μ hY hμ ΔY) (F : MMP.Mori.PrimeDivisor Y)
    (hF : ¬ F.support ⊆ MMP.Intersection.exceptionalLocus μ) :
    ΔY.coeff F = (MMP.Flips.birationalInverseTransform μ hμ B).coeff F := by
  obtain ⟨Q, hQ, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hF
  have hX : IsNormalVariety k sX := (h F).1
  have e := IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq
    (D := ⟨Y, μ, hY, hμ, F⟩) hQ.symm (h F)
  have e2 := MMP.Flips.birationalInverseTransform_apply_of_genericPoint_eq hX μ hY.1 hμ B hQ.symm
  change _ = (MMP.Flips.birationalInverseTransform μ hμ B) F
  rw [e2]
  change ΔY.coeff F = B.coeff Q
  linarith

/-- **Horizontal primes of a crepant dlt lift are strict transforms.** For a crepant dlt lift
`p : (U, Δ) ⟶ (Y, B)` over the Mori fibration `r : Y ⟶ V`, a prime divisor `F` of `U` whose
generic point lies over the generic point of `V` is the strict transform of a prime divisor `Q`
of `Y`: `p(η_F) = η_Q`, `p` is an isomorphism of local rings at `η_F` and `Δ_F = B_Q`. -/
private theorem exists_primeDivisor_of_isCrepantDltLift {Y V U : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V]
    [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [LocallyOfFiniteType sY]
    [LocallyOfFiniteType sV] {r : Y ⟶ V} (hcl : IsClosedMap r)
    (hdY : topologicalKrullDim Y = 3) (hdV : topologicalKrullDim V = 2) {K : Divisor Y}
    {B : QDivisor Y} {p : U ⟶ Y} [IsDominant p] {Δ : QDivisor U}
    (hlift : IsCrepantDltModel sY K B p Δ) (F : MMP.Mori.PrimeDivisor U)
    (hF : r (p F.genericPoint) = genericPoint V) :
    ∃ Q : MMP.Mori.PrimeDivisor Y, Q.genericPoint = p F.genericPoint ∧
      IsIso (p.stalkMap F.genericPoint) ∧ Δ.coeff F = B.coeff Q := by
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hlift.isProjectiveMorphism
  have hYv : IsNormalVariety k sY := hlift.isNormalVariety_base
  have hco : Order.coheight (p F.genericPoint) ≤ 1 :=
    coheight_le_one_of_map_eq_genericPoint (sY := sY) (sV := sV) r hcl hdY hdV hF
  have hbir := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal p
    hlift.isBirationalMorphism hco
  have hnot : ¬ F.support ⊆ MMP.Intersection.exceptionalLocus p := by
    intro hsub
    have h1 := MMP.Flips.exceptionalLocus_subset_exceptionalSet p
      (hsub (MMP.Flips.primeDivisor_genericPoint_mem_support F))
    exact h1 hbir
  obtain ⟨Q, hQ, hiso⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hnot
  obtain ⟨n', hn'⟩ := hlift.isCrepantBoundary
  have e := coeff_eq_of_not_subset_of_isCrepantBoundary hn' F hnot
  have e2 := MMP.Flips.birationalInverseTransform_apply_of_genericPoint_eq hYv p
    hlift.isNormalVariety.1 hlift.isBirationalMorphism B hQ.symm
  refine ⟨Q, hQ, hiso, ?_⟩
  rw [e]
  exact e2

/-- Residue degrees are unchanged by a morphism inducing an isomorphism of residue fields. -/
private theorem finrank_residueField_comp_eq_of_isIso {X Y Z : Scheme.{0}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (x : X) [IsIso (f.residueFieldMap x)] :
    (letI := ((f ≫ g).residueFieldMap x).hom.toAlgebra;
      Module.finrank (Z.residueField ((f ≫ g) x)) (X.residueField x)) =
    (letI := (g.residueFieldMap (f x)).hom.toAlgebra;
      Module.finrank (Z.residueField (g (f x))) (Y.residueField (f x))) := by
  letI A1 : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  letI A2 := (g.residueFieldMap (f x)).hom.toAlgebra
  let e : Y.residueField (f x) ≃ₐ[Z.residueField (g (f x))] X.residueField x :=
    { (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv with
      commutes' := fun c => by
        change (f.residueFieldMap x).hom ((g.residueFieldMap (f x)).hom c) =
          ((f ≫ g).residueFieldMap x).hom c
        rw [Scheme.residueFieldMap_comp]
        rfl }
  exact e.toLinearEquiv.finrank_eq.symm

/-- Residue degrees are unchanged by a morphism that is an isomorphism of local rings. -/
private theorem finrank_residueField_comp_eq {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) [IsIso (f.stalkMap x)] :
    (letI := ((f ≫ g).residueFieldMap x).hom.toAlgebra;
      Module.finrank (Z.residueField ((f ≫ g) x)) (X.residueField x)) =
    (letI := (g.residueFieldMap (f x)).hom.toAlgebra;
      Module.finrank (Z.residueField (g (f x))) (Y.residueField (f x))) := by
  haveI : IsIso (f.residueFieldMap x) :=
    ((IsLocalRing.ResidueField.mapEquiv
      (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso).isIso_hom
  exact finrank_residueField_comp_eq_of_isIso f g x

/-- **The horizontal floor of a crepant dlt lift.** For a crepant dlt lift `p : (U, Δ) ⟶ (Y, B)`
over the Mori fibration `r : Y ⟶ V`, the horizontal coefficient-one primes of `Δ` are the strict
transforms of those of `B`, with the same residue degrees over `k(V)`; so the two Stein degree sums
agree. -/
private theorem sum_floor_finrank_eq {Y V U : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V]
    [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [LocallyOfFiniteType sY]
    [LocallyOfFiniteType sV] {r : Y ⟶ V} (hcl : IsClosedMap r)
    (hdY : topologicalKrullDim Y = 3) (hdV : topologicalKrullDim V = 2) {K : Divisor Y}
    {B : QDivisor Y} {p : U ⟶ Y} [IsDominant p] {Δ : QDivisor U}
    (hlift : IsCrepantDltModel sY K B p Δ) :
    (open scoped Classical in
      ∑ P ∈ Δ.support with Δ P = 1 ∧ (p ≫ r).base '' (P.support : Set U) = Set.univ,
        (letI := ((p ≫ r).residueFieldMap P.genericPoint).hom.toAlgebra;
          Module.finrank (V.residueField ((p ≫ r) P.genericPoint))
            (U.residueField P.genericPoint))) =
    (open scoped Classical in
      ∑ P ∈ B.support with B P = 1 ∧ r.base '' (P.support : Set Y) = Set.univ,
        (letI := (r.residueFieldMap P.genericPoint).hom.toAlgebra;
          Module.finrank (V.residueField (r P.genericPoint)) (Y.residueField P.genericPoint))) := by
  classical
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hlift.isProjectiveMorphism
  have hbij := hlift.isBirationalMorphism.functionFieldMap_bijective
  have hclU : IsClosedMap (p ≫ r) := fun Z hZ => by
    have := hcl _ (p.isClosedMap _ hZ)
    rwa [Set.image_image] at this
  have hkey : ∀ F : MMP.Mori.PrimeDivisor U,
      (p ≫ r).base '' (F.support : Set U) = Set.univ →
      ∃ Q : MMP.Mori.PrimeDivisor Y, Q.genericPoint = p F.genericPoint ∧
        IsIso (p.stalkMap F.genericPoint) ∧ Δ.coeff F = B.coeff Q := fun F hF =>
    exists_primeDivisor_of_isCrepantDltLift (sV := sV) hcl hdY hdV hlift F
      ((image_support_eq_univ_iff (p ≫ r) hclU F).mp hF)
  refine Finset.sum_bij (fun F hF => (hkey F (Finset.mem_filter.mp hF).2.2).choose) ?_ ?_ ?_ ?_
  · -- the image lies in the horizontal floor of `B`
    intro F hF
    obtain ⟨hQg, -, hc⟩ := (hkey F (Finset.mem_filter.mp hF).2.2).choose_spec
    set Q := (hkey F (Finset.mem_filter.mp hF).2.2).choose
    have h1 : Δ F = 1 := (Finset.mem_filter.mp hF).2.1
    have hQ1 : B Q = 1 := by
      change B.coeff Q = 1
      rw [← hc]
      exact h1
    have hrQ : r Q.genericPoint = genericPoint V := by
      rw [hQg]
      exact (image_support_eq_univ_iff (p ≫ r) hclU F).mp (Finset.mem_filter.mp hF).2.2
    refine Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by rw [hQ1]; exact one_ne_zero),
      hQ1, (image_support_eq_univ_iff r hcl Q).mpr hrQ⟩
  · -- injectivity
    intro F₁ hF₁ F₂ hF₂ h
    obtain ⟨hQ₁, hi₁, -⟩ := (hkey F₁ (Finset.mem_filter.mp hF₁).2.2).choose_spec
    obtain ⟨hQ₂, hi₂, -⟩ := (hkey F₂ (Finset.mem_filter.mp hF₂).2.2).choose_spec
    have hp : p F₂.genericPoint = p F₁.genericPoint := by
      rw [← hQ₁, ← hQ₂, h]
    have hco : Order.coheight (p F₁.genericPoint) = 1 := by
      rw [← hQ₁]
      exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint _
    haveI := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hco
    haveI := hi₁
    haveI := hi₂
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (MMP.Positivity.eq_of_isIso_stalkMap p hbij hp)
  · -- surjectivity
    intro Q hQ
    have hQ1 : B Q = 1 := (Finset.mem_filter.mp hQ).2.1
    have hrQ : r Q.genericPoint = genericPoint V :=
      (image_support_eq_univ_iff r hcl Q).mp (Finset.mem_filter.mp hQ).2.2
    have hco := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q
    haveI := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hco
    obtain ⟨x, hx, hiso⟩ := MMP.Intersection.exists_isIso_stalkMap_of_valuationRing p hbij
      Q.genericPoint
    have hxco : Order.coheight x = 1 := by
      have e1 := ringKrullDim_stalk_eq_coheight x
      have e2 := ringKrullDim_stalk_eq_coheight (p x)
      rw [hx, hco] at e2
      have e3 := ringKrullDim_eq_of_ringEquiv (asIso (p.stalkMap x)).commRingCatIsoToRingEquiv
      rw [hx] at e3
      have h4 : ((Order.coheight x : ℕ∞) : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := by
        rw [← e1, ← e3, e2]
      exact_mod_cast h4
    set F := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hxco
    have hFg : F.genericPoint = x :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hxco
    have hFim : (p ≫ r).base '' (F.support : Set U) = Set.univ := by
      refine (image_support_eq_univ_iff (p ≫ r) hclU F).mpr ?_
      change r (p F.genericPoint) = _
      rw [hFg, hx, hrQ]
    obtain ⟨hQ', -, hc'⟩ := (hkey F hFim).choose_spec
    have hQQ : (hkey F hFim).choose = Q := by
      apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      change (hkey F hFim).choose.genericPoint = Q.genericPoint
      rw [hQ']
      exact (congrArg (fun z => p z) hFg).trans hx
    have hΔ : Δ F = 1 := by
      change Δ.coeff F = 1
      rw [hc', hQQ]
      exact hQ1
    refine ⟨F, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by rw [hΔ]; exact one_ne_zero),
      hΔ, hFim⟩, hQQ⟩
  · -- the residue degrees agree
    intro F hF
    obtain ⟨hQg, hiso, -⟩ := (hkey F (Finset.mem_filter.mp hF).2.2).choose_spec
    haveI := hiso
    rw [finrank_residueField_comp_eq p r F.genericPoint, hQg]

/-- Residue-field maps of closed immersions are isomorphisms. -/
private theorem isIso_residueFieldMap_of_isClosedImmersion {S U : Scheme.{0}} (j : S ⟶ U)
    [IsClosedImmersion j] (x : S) : IsIso (j.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(j.residueFieldMap x).hom.injective, fun z => ?_⟩
  obtain ⟨a, rfl⟩ := S.residue_surjective x z
  obtain ⟨b, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective j x a
  refine ⟨U.residue (j x) b, ?_⟩
  have := ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap j x) b
  simpa using this

/-- **The degree of a branch is a residue degree.** For a closed immersion `j : S ⟶ U` of an
integral scheme and `q : U ⟶ V` with `j ≫ q` dominant,
`[k(S) : k(V)] = [κ(j η_S) : κ(q j η_S)]`. -/
private theorem finrank_functionField_eq_finrank_residueField {S U V : Scheme.{0}}
    [IsIntegral S] [IsIntegral V] (j : S ⟶ U) [IsClosedImmersion j] (q : U ⟶ V)
    [IsDominant (j ≫ q)] :
    (letI := functionFieldMapAlgebra (j ≫ q);
      Module.finrank V.functionField S.functionField) =
    (letI := (q.residueFieldMap (j (genericPoint S))).hom.toAlgebra;
      Module.finrank (V.residueField (q (j (genericPoint S))))
        (U.residueField (j (genericPoint S)))) := by
  have h1 := Stacks.Chow.finrank_functionField_eq_residueDegree (j ≫ q)
  rw [MMP.Mori.dominantFunctionFieldMap_eq_functionFieldMap] at h1
  refine h1.trans ?_
  haveI := isIso_residueFieldMap_of_isClosedImmersion j (genericPoint S)
  exact finrank_residueField_comp_eq_of_isIso j q (genericPoint S)

/-- **A horizontal floor branch.** A branch `j : S ⟶ U` of an adjunction step on the boundary of
a crepant dlt lift, dominating `V`, lies on a horizontal coefficient-one prime `P` of `Δ`, and the
degree `[k(S) : k(V)]` is the positive residue degree of `P` over `V`. -/
private theorem exists_floor_primeDivisor_of_isAdjunctionStep {Y V U S : Scheme.{0}}
    [IsIntegral Y] [IsIntegral V] [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [LocallyOfFiniteType sV] {r : Y ⟶ V}
    (hrs : r ≫ sV = sY) [IsLocallyNoetherian Y] [IsNormal Y] {K : Divisor Y} {B : QDivisor Y}
    {p : U ⟶ Y} [IsDominant p] {Δ : QDivisor U} (hlift : IsCrepantDltModel sY K B p Δ)
    (hcl : IsClosedMap (p ≫ r)) {j : S ⟶ U} {BS : QDivisor S} [IsDominant (j ≫ p ≫ r)]
    (hS : IsAdjunctionStep (p ≫ sY) Δ j BS) (hdS : topologicalKrullDim S = 2)
    (hdV : topologicalKrullDim V = 2) :
    ∃ P : MMP.Mori.PrimeDivisor U, Set.range j.base = (P.support : Set U) ∧ Δ P = 1 ∧
      (p ≫ r).base '' (P.support : Set U) = Set.univ ∧
      (letI := functionFieldMapAlgebra (j ≫ p ≫ r);
        Module.finrank V.functionField S.functionField) =
        (letI := ((p ≫ r).residueFieldMap P.genericPoint).hom.toAlgebra;
          Module.finrank (V.residueField ((p ≫ r) P.genericPoint))
            (U.residueField P.genericPoint)) ∧
      0 < (letI := functionFieldMapAlgebra (j ≫ p ≫ r);
        Module.finrank V.functionField S.functionField) := by
  obtain ⟨hT, P, hP1, hrange, hci, -⟩ := hS
  haveI := hci
  have hjT : j (genericPoint S) = P.genericPoint := by
    have h1 : closure ({j (genericPoint S)} : Set U) = Set.range j.base := by
      apply le_antisymm
      · rw [hrange]
        exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure P ▸
          isClosed_closure).closure_subset_iff.mpr
          (Set.singleton_subset_iff.mpr (hrange ▸ Set.mem_range_self _))
      · rintro _ ⟨z, rfl⟩
        have hz : genericPoint S ⤳ z := (genericPoint_spec S).specializes trivial
        exact specializes_iff_mem_closure.mp (hz.map j.continuous)
    have h2 : closure ({j (genericPoint S)} : Set U) = closure {P.genericPoint} := by
      rw [h1, hrange, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact (inseparable_iff_closure_eq.mpr h2).eq
  have hΔ1 : Δ P = 1 := le_antisymm (hlift.isDltPair.2.1 P) hP1
  have hηV : (p ≫ r) P.genericPoint = genericPoint V := by
    rw [← hjT]
    exact map_genericPoint_of_isDominant (j ≫ p ≫ r)
  have hfin := finrank_functionField_eq_finrank_residueField j (p ≫ r)
  refine ⟨P, hrange, hΔ1, (image_support_eq_univ_iff (p ≫ r) hcl P).mpr hηV, ?_, ?_⟩
  · rw [hfin, hjT]
  · letI := functionFieldMapAlgebra (j ≫ p ≫ r)
    haveI : LocallyOfFiniteType ((j ≫ p ≫ r) ≫ sV) := by
      rw [Category.assoc, Category.assoc, hrs]
      exact hT.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (j ≫ p ≫ r) := locallyOfFiniteType_of_comp (j ≫ p ≫ r) sV
    haveI : Module.Finite V.functionField S.functionField :=
      MMP.Mori.finite_functionField_of_topologicalKrullDim_eq sV (j ≫ p ≫ r) (by rw [hdS, hdV])
    exact Module.finrank_pos

/-- A divisor whose coefficient along `P` vanishes does not contain `η_P` in its support. -/
private theorem genericPoint_notMem_supp_of_coeff_eq_zero {R : Type*} [Zero R] {X : Scheme.{0}}
    {D : DivisorWithCoeffs R X} {P : MMP.Mori.PrimeDivisor X} (h : D.coeff P = 0) :
    P.genericPoint ∉ D.supp := by
  intro hP
  obtain ⟨E, hE, hPE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hP
  obtain rfl := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hPE
  exact hE h

open exteriorPower in
/-- **Forms of regular functions are regular**, at a point named by an equation. -/
private theorem zero_le_ordForm_formPow_ιMulti_of_eq {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] (Γ : MMP.Mori.PrimeDivisor X) {d : ℕ}
    (hd : topologicalKrullDim X = d) {z : X} (hz : z = Γ.genericPoint)
    (y : Fin d → X.presheaf.stalk z) :
    letI := functionFieldAlgebra sX
    0 ≤ Γ.ordForm (sX := sX) (d := d) (m := ((1 : ℕ) : ℤ))
      (formPow (ιMulti X.functionField d fun i =>
        KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField (y i))) 1) := by
  subst hz
  exact zero_le_ordForm_formPow_ιMulti Γ hd y

/-- `0^{⊗m} = 0` for `m > 0`. -/
private theorem formPow_zero_of_pos {K : Type} [Field K] [Algebra k K] {d m : ℕ} (hm : 0 < m) :
    (formPow (0 : ⋀[K]^d Ω[K⁄k]) m : PluriForms k K d m) = 0 := by
  rw [show (0 : ⋀[K]^d Ω[K⁄k]) = (0 : K) • 0 from (zero_smul _ _).symm, formPow_smul,
    zero_pow hm.ne', zero_smul]

/-- On a variety of dimension `d`, the `m`-th power of a nonzero top form is nonzero. -/
private theorem formPow_ne_zero_of_ne_zero {X : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] {d : ℕ} (hd : topologicalKrullDim X = d)
    {v : letI := functionFieldAlgebra sX; ⋀[X.functionField]^d Ω[X.functionField⁄k]}
    (hv : v ≠ 0) (m : ℕ) :
    letI := functionFieldAlgebra sX
    (formPow v m : PluriForms k X.functionField d m) ≠ 0 := by
  letI := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  have hv' : v = b.repr v () • b () := (basis_unit_repr_smul b v).symm
  have hc : b.repr v () ≠ 0 := fun h0 => hv (by rw [hv', h0, zero_smul])
  rw [hv', formPow_smul]
  refine smul_ne_zero (pow_ne_zero _ hc) ?_
  rw [← ZTensorPower.basis_natCast]
  exact (ZTensorPower.basis b m).ne_zero ()

open exteriorPower in
/-- **Adjunction for `m`-canonical forms.** Let `(S, B_S)` arise from `(U, Δ)` by an adjunction
step `j : S ⟶ U` onto `P`, `U` a `ℚ`-factorial normal variety over `k` of dimension `n + 1`, and
`q : U ⟶ V` with `j ≫ q` dominant. If a rational `m`-canonical form `τ` satisfies
`div τ + mΔ = q^*M` and `ρ ≠ 0` is its Poincaré residue along `S`, then
`div ρ + m B_S = (j ≫ q)^*M`. Writing `τ = g (dt/t ∧ dx)^{⊗m}`, this is the adjunction formula
for the `1`-forms `τ₁ = dt/t ∧ dx` and `g τ₁`, combined as
`div τ + mΔ = (div gτ₁ + Δ) + (m - 1)(div τ₁ + Δ)`. -/
private theorem exists_ordForm_add_eq_of_isPoincareResidue
    {U S V : Scheme.{0}} [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] [CompactSpace U]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    {sU : U ⟶ Spec (.of k)} [LocallyOfFiniteType sU] {Δ : QDivisor U} {j : S ⟶ U}
    {BS : QDivisor S} (hS : IsAdjunctionStep sU Δ j BS)
    {n : ℕ} (hQ : ∀ τ : RationalPluriForms sU (n + 1) ((1 : ℕ) : ℤ), τ ≠ 0 →
      (Divisor.toQDivisor (divisorOfForm τ) + Δ).IsQCartier) (hdim : topologicalKrullDim U = n + 1)
    (hdS : topologicalKrullDim S = n) (hΔle : ∀ P, Δ.coeff P ≤ 1)
    {q : U ⟶ V} [IsDominant q] [IsDominant (j ≫ q)] {M : Divisor V} (hM : M.IsCartier)
    {MU : Divisor U}
    (hMU : M.IsPullback q (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp q M) MU)
    {m : ℕ} (hm : 0 < m) {τ : RationalPluriForms sU (n + 1) m}
    (hτ : ∀ F : MMP.Mori.PrimeDivisor U, (F.ordForm τ : ℚ) + m * Δ.coeff F = MU.coeff F)
    {ρ : RationalPluriForms (j ≫ sU) n m} (hρ0 : ρ ≠ 0) (hρ : IsPoincareResidue sU j n m τ ρ) :
    ∃ MS : Divisor S, M.IsPullback (j ≫ q)
        (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (j ≫ q) M) MS ∧
      ∀ Γ : MMP.Mori.PrimeDivisor S, (Γ.ordForm ρ : ℚ) + m * BS.coeff Γ = MS.coeff Γ := by
  classical
  have hdim' : topologicalKrullDim U = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hdim]
    norm_cast
  have hT := hS.1
  haveI : LocallyOfFiniteType (j ≫ sU) := hT.1.toLocallyOfFiniteType
  obtain ⟨-, P, hP1, hrange, hci, -⟩ := id hS
  haveI := hci
  have hjT : j (genericPoint S) = P.genericPoint := by
    obtain ⟨P₀, hP₀, -⟩ := hS.exists_primeDivisor
    have h0 : P₀ = P := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support (by
      change P₀.genericPoint ∈ (P.support : Set U)
      rw [← hrange, ← hP₀]
      exact ⟨_, rfl⟩)
    rw [hP₀, h0]
  have hΔP : Δ.coeff P = 1 := le_antisymm (hΔle P) hP1
  have hqP : q P.genericPoint = genericPoint V := by
    rw [← hjT]
    exact map_genericPoint_of_isDominant (j ≫ q)
  have hMUP : MU.coeff P = 0 := coeff_isPullback_eq_zero_of_map_genericPoint hMU P hqP
  have hgenU : ∀ {D : Divisor U}, D.coeff P = 0 →
      ∀ Z : irreducibleComponents S, j (componentGenericPoint S Z) ∉ D.supp := fun hD Z => by
    rw [componentGenericPoint_eq_genericPoint, hjT]
    exact genericPoint_notMem_supp_of_coeff_eq_zero hD
  -- the residue presentation
  obtain ⟨t, g, x, ht, hτE, hρE⟩ := hρ
  letI := functionFieldAlgebra sU
  letI := functionFieldAlgebra (j ≫ sU)
  let v : ⋀[U.functionField]^(n + 1) Ω[U.functionField⁄k] :=
    (algebraMap _ U.functionField t)⁻¹ • ιMulti U.functionField (n + 1)
      (Fin.cons (KaehlerDifferential.D k U.functionField (algebraMap _ _ t))
        fun i => KaehlerDifferential.D k U.functionField (algebraMap _ _ (x i)))
  have hvdef : v =
      (algebraMap _ U.functionField t)⁻¹ • ιMulti U.functionField (n + 1)
      (Fin.cons (KaehlerDifferential.D k U.functionField (algebraMap _ _ t))
      fun i => KaehlerDifferential.D k U.functionField (algebraMap _ _ (x i))) := rfl
  let w : ⋀[S.functionField]^n Ω[S.functionField⁄k] :=
    ιMulti S.functionField n fun i =>
      KaehlerDifferential.D k S.functionField ((j.stalkMap (genericPoint S)).hom (x i))
  let gU : U.functionField := algebraMap _ U.functionField g
  let gS : S.functionField := (j.stalkMap (genericPoint S)).hom g
  have hgSdef : gS =
      (j.stalkMap (genericPoint S)).hom g := rfl
  let τ₁ : RationalPluriForms sU (n + 1) ((1 : ℕ) : ℤ) := formPow v 1
  let ρ₁ : RationalPluriForms (j ≫ sU) n ((1 : ℕ) : ℤ) := formPow w 1
  let σ : RationalPluriForms sU (n + 1) ((1 : ℕ) : ℤ) := gU • τ₁
  let ρσ : RationalPluriForms (j ≫ sU) n ((1 : ℕ) : ℤ) := gS • ρ₁
  have hτv : τ = (show RationalPluriForms sU (n + 1) m from gU • formPow v m) := hτE
  have hρw : ρ = (show RationalPluriForms (j ≫ sU) n m from gS • formPow w m) := hρE
  -- nonvanishing
  have hgS0 : gS ≠ 0 := fun h0 => hρ0 (by rw [hρw]; change gS • formPow w m = 0; rw [h0, zero_smul])
  have hw0 : w ≠ 0 := fun h0 => hρ0 (by
    rw [hρw]
    change gS • formPow w m = 0
    rw [show w = (0 : S.functionField) • w by rw [h0, smul_zero], formPow_smul,
      zero_pow hm.ne', zero_smul, smul_zero])
  have hgU0 : gU ≠ 0 := fun h0 => hgS0 (by
    have hg0 : g = 0 := IsFractionRing.injective _ U.functionField (h0.trans (map_zero _).symm)
    rw [hgSdef, hg0, map_zero])
  have hτ0 : τ ≠ 0 := by
    intro h0
    have := hτ P
    rw [h0, PrimeDivisor.ordForm_zero, hΔP, hMUP] at this
    push_cast at this
    have hm' : (0 : ℚ) < m := by exact_mod_cast hm
    linarith
  have hv0 : v ≠ 0 := fun h0 => hτ0 (by
    rw [hτv]
    change gU • formPow v m = 0
    rw [show v = (0 : U.functionField) • v by rw [h0, smul_zero], formPow_smul,
      zero_pow hm.ne', zero_smul, smul_zero])
  have hτ₁0 : τ₁ ≠ 0 := formPow_ne_zero_of_ne_zero hdim' hv0 1
  have hρ₁0 : ρ₁ ≠ 0 := formPow_ne_zero_of_ne_zero hdS hw0 1
  have hσ0 : σ ≠ 0 := smul_ne_zero hgU0 hτ₁0
  have hρσ0 : ρσ ≠ 0 := smul_ne_zero hgS0 hρ₁0
  -- orders on `U` and on `S`
  have hpowU : ∀ F : MMP.Mori.PrimeDivisor U,
      F.ordForm τ = U.ord gU F.genericPoint + m * F.ordForm τ₁ := fun F => by
    rw [hτv]
    exact ordForm_smul_formPow F hdim' hv0 hgU0 m
  have hσU : ∀ F : MMP.Mori.PrimeDivisor U,
      F.ordForm σ = U.ord gU F.genericPoint + F.ordForm τ₁ := fun F =>
    F.ordForm_smul_of_topologicalKrullDim_eq hdim' hgU0 hτ₁0
  have hpowS : ∀ Γ : MMP.Mori.PrimeDivisor S,
      Γ.ordForm ρ = S.ord gS Γ.genericPoint + m * Γ.ordForm ρ₁ := fun Γ => by
    rw [hρw]
    exact ordForm_smul_formPow Γ hdS hw0 hgS0 m
  have hσS : ∀ Γ : MMP.Mori.PrimeDivisor S,
      Γ.ordForm ρσ = S.ord gS Γ.genericPoint + Γ.ordForm ρ₁ := fun Γ =>
    Γ.ordForm_smul_of_topologicalKrullDim_eq hdS hgS0 hρ₁0
  -- the orders along `P`
  have hgP : 0 ≤ U.ord gU P.genericPoint := by
    rcases eq_or_ne gU 0 with h | h
    · exact absurd h hgU0
    · rw [← hjT]
      exact (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord
        (hjT ▸ AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P) h).mp ⟨g, rfl⟩
  have hτ₁P : -1 ≤ P.ordForm τ₁ := by
    have ht0 : algebraMap _ U.functionField t ≠ 0 := by
      intro h0
      rw [h0, Scheme.ord_zero] at ht
      exact zero_ne_one ht
    let ι₀ : ⋀[U.functionField]^(n + 1) Ω[U.functionField⁄k] := ιMulti U.functionField (n + 1)
      (Fin.cons (KaehlerDifferential.D k U.functionField (algebraMap _ _ t))
        fun i => KaehlerDifferential.D k U.functionField (algebraMap _ _ (x i)))
    have hι₀def : ι₀ =
        ιMulti U.functionField (n + 1)
        (Fin.cons (KaehlerDifferential.D k U.functionField (algebraMap _ _ t))
        fun i => KaehlerDifferential.D k U.functionField (algebraMap _ _ (x i))) := rfl
    have hfam : ι₀ = ιMulti U.functionField (n + 1) fun i => KaehlerDifferential.D k
        U.functionField (algebraMap _ U.functionField ((Fin.cons t x : Fin (n + 1) → _) i)) := by
      rw [hι₀def]
      congr 1
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    let ω₀ : RationalPluriForms sU (n + 1) ((1 : ℕ) : ℤ) := formPow ι₀ 1
    have hω₀def : ω₀ =
        formPow ι₀ 1 := rfl
    have hτ₁ω : τ₁ = (algebraMap _ U.functionField t)⁻¹ • ω₀ := by
      change (formPow v 1 : PluriForms k U.functionField (n + 1) ((1 : ℕ) : ℤ)) =
        ((algebraMap _ U.functionField t)⁻¹ • formPow ι₀ 1 :
          PluriForms k U.functionField (n + 1) ((1 : ℕ) : ℤ))
      rw [hvdef, formPow_smul, pow_one]
    have hω₀ne : ω₀ ≠ 0 := by
      intro h0
      apply hτ₁0
      rw [hτ₁ω, h0, smul_zero]
    have e := P.ordForm_smul_of_topologicalKrullDim_eq hdim' (inv_ne_zero ht0) hω₀ne
    have hreg := zero_le_ordForm_formPow_ιMulti_of_eq (sX := sU) P hdim' hjT (Fin.cons t x)
    have hreg' : 0 ≤ P.ordForm ω₀ := by
      rw [hω₀def, hfam]
      exact hreg
    rw [hτ₁ω, e, ← zpow_neg_one, MMP.Mori.ord_zpow _ ht0, ← hjT, ht]
    linarith
  have hP' := hτ P
  rw [hpowU P, hΔP, hMUP] at hP'
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hi : U.ord gU P.genericPoint + m * P.ordForm τ₁ = -m := by
    have : (U.ord gU P.genericPoint : ℚ) + m * (P.ordForm τ₁ : ℚ) = -m := by
      push_cast at hP'
      linarith
    exact_mod_cast this
  have hτ₁P' : P.ordForm τ₁ = -1 := by
    by_contra hne
    have h0 : 0 ≤ P.ordForm τ₁ := by omega
    linarith [mul_nonneg hm'.le h0]
  have hgP0 : U.ord gU P.genericPoint = 0 := by
    rw [hτ₁P'] at hi
    linarith
  have hσP : P.ordForm σ = -1 := by rw [hσU P, hgP0, hτ₁P', zero_add]
  -- the residues of the two `1`-forms
  have hres₁ : IsPoincareResidue sU j n 1 τ₁ ρ₁ :=
    ⟨t, 1, x, ht, by rw [map_one, one_smul]; rfl, by rw [map_one, one_smul]; rfl⟩
  have hresσ : IsPoincareResidue sU j n 1 σ ρσ := ⟨t, g, x, ht, rfl, rfl⟩
  obtain ⟨hgen₁, hpb₁⟩ := hS.isPullback_divisorOfForm_add_of_isPoincareResidue hdim P hrange τ₁
    hτ₁0 hτ₁P' ρ₁ hres₁ (hQ _ hτ₁0)
  obtain ⟨hgen₂, hpb₂⟩ := hS.isPullback_divisorOfForm_add_of_isPoincareResidue hdim P hrange σ
    hσ0 hσP ρσ hresσ (hQ _ hσ0)
  -- integral Cartier multiples
  obtain ⟨c₁, hc₁, A₁, hA₁, hA₁c⟩ := (hQ τ₁ hτ₁0).exists_pos
  obtain ⟨c₂, hc₂, A₂, hA₂, hA₂c⟩ := (hQ σ hσ0).exists_pos
  obtain ⟨A₁', hA₁', hpA₁⟩ := hpb₁ c₁ hc₁ A₁ hA₁ hA₁c
  obtain ⟨A₂', hA₂', hpA₂⟩ := hpb₂ c₂ hc₂ A₂ hA₂ hA₂c
  -- the pull-back of `MU`
  have hMUc : MU.IsCartier := by
    rw [← Divisor.IsPullback.pullback_eq hM hMU]
    exact hM.isCartier_pullback q _
  obtain ⟨MS, hMS⟩ := hMUc.exists_isPullback (f := j) (hgenU hMUP)
  have hMSV : M.IsPullback (j ≫ q)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (j ≫ q) M) MS :=
    MMP.ProgramBaseChange.divisor_isPullback_comp rfl hMU hMS _
  refine ⟨MS, hMSV, fun Γ => ?_⟩
  -- the identity of integral divisors on `U`
  have hcoefU : ∀ F : MMP.Mori.PrimeDivisor U, ((c₁ : ℚ) * c₂ * MU.coeff F : ℚ) =
      c₁ * (A₂.coeff F : ℚ) + ((m : ℚ) - 1) * c₂ * (A₁.coeff F : ℚ) := by
    intro F
    have h1 := congrArg (fun G : QDivisor U => G.coeff F) hA₁
    have h2 := congrArg (fun G : QDivisor U => G.coeff F) hA₂
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      coeff_divisorOfForm, zsmul_eq_mul, Int.cast_natCast] at h1 h2
    rw [h1, h2, hσU F, ← hτ F, hpowU F]
    push_cast
    ring
  have hidU : ((c₁ : ℤ) * c₂) • MU = (c₁ : ℤ) • A₂ + (((m : ℤ) - 1) * c₂) • A₁ := by
    refine Finsupp.ext fun F => ?_
    change DivisorWithCoeffs.coeff (((c₁ : ℤ) * c₂) • MU) F =
      DivisorWithCoeffs.coeff ((c₁ : ℤ) • A₂ + (((m : ℤ) - 1) * c₂) • A₁) F
    rw [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    have h : (((c₁ : ℤ) * c₂ * MU.coeff F : ℤ) : ℚ) =
        (((c₁ : ℤ) * A₂.coeff F + ((m : ℤ) - 1) * c₂ * A₁.coeff F : ℤ) : ℚ) := by
      push_cast
      linarith [hcoefU F]
    exact_mod_cast h
  -- pulling back along `j`
  have hA₁P : A₁.coeff P = 0 := by
    have := congrArg (fun G : QDivisor U => G.coeff P) hA₁
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      coeff_divisorOfForm, zsmul_eq_mul, hτ₁P', hΔP] at this
    exact_mod_cast (by rw [this]; push_cast; ring : ((A₁.coeff P : ℤ) : ℚ) = 0)
  have hA₂P : A₂.coeff P = 0 := by
    have := congrArg (fun G : QDivisor U => G.coeff P) hA₂
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      coeff_divisorOfForm, zsmul_eq_mul, hσP, hΔP] at this
    exact_mod_cast (by rw [this]; push_cast; ring : ((A₂.coeff P : ℤ) : ℚ) = 0)
  have hpA₁' := hpA₁.zsmul hA₁c (((m : ℤ) - 1) * c₂)
    (hgenU (by rw [DivisorWithCoeffs.coeff_smul, hA₁P, smul_zero]))
  have hpA₂' := hpA₂.zsmul hA₂c (c₁ : ℤ)
    (hgenU (by rw [DivisorWithCoeffs.coeff_smul, hA₂P, smul_zero]))
  have hpsum := hpA₂'.add (hA₂c.zsmul _) (hA₁c.zsmul _)
    (hgenU (by rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_smul, hA₁P, hA₂P, smul_zero, smul_zero, add_zero])) hpA₁'
  have hpN := hMS.zsmul hMUc ((c₁ : ℤ) * c₂)
    (hgenU (by rw [DivisorWithCoeffs.coeff_smul, hMUP, smul_zero]))
  have heq := hpN.eq (hMUc.zsmul _) (hpsum.of_eq hidU.symm)
  -- reading off the coefficient along `Γ`
  have hΓ := congrArg (fun G : Divisor S => G.coeff Γ) heq
  have h1 := congrArg (fun G : QDivisor S => G.coeff Γ) hA₁'
  have h2 := congrArg (fun G : QDivisor S => G.coeff Γ) hA₂'
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, smul_eq_mul] at hΓ
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
    coeff_divisorOfForm, zsmul_eq_mul, Int.cast_natCast] at h1 h2
  have hΓq : (((c₁ : ℤ) * c₂ * MS.coeff Γ : ℤ) : ℚ) =
      (((c₁ : ℤ) * A₂'.coeff Γ + ((m : ℤ) - 1) * c₂ * A₁'.coeff Γ : ℤ) : ℚ) := by
    rw [hΓ]
  push_cast at hΓq
  rw [h1, h2, hσS Γ] at hΓq
  rw [hpowS Γ]
  have hN0 : ((c₁ : ℚ) * c₂) ≠ 0 := by positivity
  apply mul_left_cancel₀ hN0
  push_cast at hΓq ⊢
  linear_combination hΓq.symm

/-- Rational functions on `V` pulled back along a dominant `r : Y ⟶ V` are regular along every
prime divisor `Q` of `Y` dominating `V`: they come from the stalk of `V` at `r(η_Q) = η_V`. -/
private theorem divisorialValuation_functionFieldMap_le_one {Y V : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V] (r : Y ⟶ V) [IsDominant r]
    (Q : MMP.Mori.PrimeDivisor Y) (hQ : r Q.genericPoint = genericPoint V) (c : V.functionField) :
    Q.divisorialValuation (functionFieldMap r c) ≤ 1 := by
  have key : ∀ (x : V), x = genericPoint V → ∀ c : V.functionField,
      ∃ a : V.presheaf.stalk x, algebraMap _ V.functionField a = c := by
    rintro x rfl c
    refine ⟨c, ?_⟩
    change (V.presheaf.stalkSpecializes _).hom c = c
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  obtain ⟨a, rfl⟩ := key _ hQ c
  rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
  exact (Q.divisorialValuation_le_one_iff _).2 ⟨_, rfl⟩

/- ### Global sections of `𝒪_X(D)` as rational functions -/

section DivisorialSections

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A global section of `𝒪_X(D)` on an integral scheme, read as a rational function through the
factor of `K(X)` along the component `Z`. -/
private noncomputable def componentSectionValue {D : Divisor X} (Z : irreducibleComponents X)
    (σ : D.divisorialSubmodule ⊤) : X.functionField :=
  (MMP.Positivity.componentToFunctionField Z).hom (σ.1 ⟨Z, trivial⟩)

/-- The generization `k(X) ⟶ 𝒪_{X,η_Z}` inverse to `MMP.Positivity.componentToFunctionField`. -/
private theorem exists_inverse_componentToFunctionField (Z : irreducibleComponents X) :
    ∃ j : X.functionField →+* X.presheaf.stalk (componentGenericPoint X Z),
      (∀ a, (MMP.Positivity.componentToFunctionField Z).hom (j a) = a) ∧
      ∀ b, j ((MMP.Positivity.componentToFunctionField Z).hom b) = b := by
  have hmem : genericPoint X ∈ Z.1 :=
    Z.2.2 (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _) trivial
  refine ⟨(X.presheaf.stalkSpecializes
    ((isGenericPoint_componentGenericPoint X Z).specializes hmem)).hom, fun a => ?_, fun b => ?_⟩
  · change (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom a = a
    rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  · change (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom b = b
    rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
    rfl

private theorem componentSectionValue_add {D : Divisor X} (Z : irreducibleComponents X)
    (σ τ : D.divisorialSubmodule ⊤) :
    componentSectionValue Z (σ + τ) = componentSectionValue Z σ + componentSectionValue Z τ :=
  map_add (MMP.Positivity.componentToFunctionField Z).hom _ _

private theorem componentSectionValue_smul {D : Divisor X} (Z : irreducibleComponents X)
    [Nonempty X]
    (s : Γ(X, ⊤)) (σ : D.divisorialSubmodule ⊤) :
    componentSectionValue Z (s • σ) = X.germToFunctionField ⊤ s * componentSectionValue Z σ := by
  unfold componentSectionValue
  rw [Submodule.coe_smul, rationalFunctions_smul_apply, map_mul]
  congr 1
  change (X.presheaf.germ ⊤ _ _ ≫ X.presheaf.stalkSpecializes _).hom s = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

private theorem componentSectionValue_injective {D : Divisor X} (Z : irreducibleComponents X) :
    Function.Injective (componentSectionValue (D := D) Z) := by
  intro σ τ h
  haveI := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)
  obtain ⟨j, -, hj⟩ := exists_inverse_componentToFunctionField Z
  have h1 : σ.1 ⟨Z, trivial⟩ = τ.1 ⟨Z, trivial⟩ := by
    rw [← hj (σ.1 ⟨Z, trivial⟩), ← hj (τ.1 ⟨Z, trivial⟩)]
    exact congrArg j h
  refine Subtype.ext (funext fun Z' => ?_)
  obtain ⟨Z', hZ'⟩ := Z'
  obtain rfl : Z' = Z := Subsingleton.elim _ _
  exact h1

/-- The rational function of a nonzero global section `σ` of `𝒪_X(D)` has `div σ + D ≥ 0`. -/
private theorem neg_coeff_le_ord_sectionValue {D : Divisor X} [CompactSpace X]
    (Z : irreducibleComponents X) {σ : D.divisorialSubmodule ⊤} (hσ : σ ≠ 0)
    (E : MMP.Mori.PrimeDivisor X) : -D E ≤ X.ord (componentSectionValue Z σ) E.genericPoint := by
  haveI := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)
  have h := D.zeroDivisor_nonneg σ hσ E
  rw [Divisor.zeroDivisor_eq] at h
  set u := (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  have e2 := MMP.Positivity.ord_eq_ord_componentToFunctionField E u
  have hZ : E.component = Z := Subsingleton.elim _ _
  have e3 : componentSectionValue Z σ =
      (MMP.Positivity.componentToFunctionField E.component).hom (u.val E.component) := by
    rw [hZ]
    rfl
  change 0 ≤ (principalDivisor u).coeff E + D.coeff E at h
  rw [coeff_principalDivisor, e2, ← e3] at h
  change -D.coeff E ≤ _
  omega

/-- A rational function with `div f + D ≥ 0` is a global section of `𝒪_X(D)`. -/
private theorem exists_sectionValue_eq {D : Divisor X} (Z : irreducibleComponents X)
    {f : X.functionField}
    (hf : ∀ E : MMP.Mori.PrimeDivisor X, f ≠ 0 → -D E ≤ X.ord f E.genericPoint) :
    ∃ σ : D.divisorialSubmodule ⊤, componentSectionValue Z σ = f := by
  choose j hj hj' using exists_inverse_componentToFunctionField (X := X)
  let φ : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op ⊤)) := fun Z => j Z.1 f
  have hφ : D.IsDivisorialSection ⊤ φ := by
    intro E _
    rcases eq_or_ne f 0 with hf0 | hf0
    · left
      change j E.component f = 0
      rw [hf0, map_zero]
    · right
      let u : (RationalFunctions X)ˣ :=
        Units.map (RingHom.pi j).toMonoidHom (Units.mk0 f hf0)
      have hu : φ ⟨E.component, E.componentGenericPoint_mem_of_nonempty ‹_›⟩ =
          (u : RationalFunctions X) E.component := rfl
      rw [hu, E.valuation_component, WithZero.exp_le_exp,
        MMP.Positivity.ord_eq_ord_componentToFunctionField]
      have : (MMP.Positivity.componentToFunctionField E.component).hom (u.val E.component) = f :=
        hj E.component f
      rw [this]
      exact hf E hf0
  exact ⟨⟨φ, hφ⟩, hj Z f⟩

end DivisorialSections

/-- **The constants of the generic fibre.** For `c ∈ k(V)`, the global function on the generic
fibre `C = Y_η` given by the residue of `c` in `κ(η)` has germ `ι^*(r^* c)` at the generic point
of `C`, where `ι : C ⟶ Y` is the inclusion. -/
private theorem germToFunctionField_appTop_residue {Y V : Scheme.{0}} [IsIntegral Y]
    [IsIntegral V] (r : Y ⟶ V) [IsDominant r] [IsIntegral (r.fiber (genericPoint V))]
    [IsDominant (r.fiberι (genericPoint V))] (c : V.functionField) :
    (r.fiber (genericPoint V)).germToFunctionField ⊤
      (((Scheme.ΓSpecIso (.of (V.residueField (genericPoint V)))).inv ≫
        (r.fiberToSpecResidueField (genericPoint V)).appTop).hom
          ((V.residue (genericPoint V)).hom c)) =
      functionFieldMap (r.fiberι (genericPoint V)) (functionFieldMap r c) := by
  obtain ⟨U, hηU, s, rfl⟩ := V.presheaf.exists_germ_eq c
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI : IsDominant (r.fiberι (genericPoint V) ≫ r) := inferInstance
  have hfac := Scheme.Hom.fiber_fac r (genericPoint V)
  have hgenU : ∀ x, (r.fiberι (genericPoint V) ≫ r) x ∈ U := by
    intro x
    rw [hfac, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact hηU
  have he : (⊤ : (r.fiber (genericPoint V)).Opens) ≤ (r.fiberι (genericPoint V) ≫ r) ⁻¹ᵁ U :=
    fun x _ => hgenU x
  haveI : Nonempty ((r.fiberι (genericPoint V) ≫ r) ⁻¹ᵁ U) :=
    ⟨⟨genericPoint _, hgenU _⟩⟩
  have he₁ : (⊤ : (Spec (.of (V.residueField (genericPoint V)))).Opens) ≤
      V.fromSpecResidueField (genericPoint V) ⁻¹ᵁ U := by
    intro x _
    change V.fromSpecResidueField _ x ∈ U
    rw [Scheme.fromSpecResidueField_apply]
    exact hηU
  have hev := MMP.Scheme.appLE_fromSpecResidueField_ΓSpecIso (X := V)
    (x := genericPoint V) (V.fromSpecResidueField (genericPoint V)) rfl U hηU he₁
  have h2 : ((Scheme.ΓSpecIso (.of (V.residueField (genericPoint V)))).inv).hom
      ((V.residue (genericPoint V)).hom (V.presheaf.germ U (genericPoint V) hηU s)) =
      ((V.fromSpecResidueField (genericPoint V)).appLE U ⊤ he₁).hom s := by
    change ((Scheme.ΓSpecIso _).inv).hom ((V.evaluation U (genericPoint V) hηU).hom s) = _
    rw [← hev, ← RingHom.comp_apply, ← CommRingCat.hom_comp, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hcongr : ∀ (φ ψ : r.fiber (genericPoint V) ⟶ V) (_ : φ = ψ) (e₁ : ⊤ ≤ φ ⁻¹ᵁ U)
      (e₂ : ⊤ ≤ ψ ⁻¹ᵁ U), φ.appLE U ⊤ e₁ = ψ.appLE U ⊤ e₂ := by
    rintro φ _ rfl _ _
    rfl
  have h3 : (r.fiberToSpecResidueField (genericPoint V)).appTop.hom
      (((V.fromSpecResidueField (genericPoint V)).appLE U ⊤ he₁).hom s) =
      ((r.fiberι (genericPoint V) ≫ r).appLE U ⊤ he).hom s := by
    have := Scheme.Hom.appLE_comp_appLE (r.fiberToSpecResidueField (genericPoint V))
      (V.fromSpecResidueField (genericPoint V)) U ⊤ ⊤ he₁ le_rfl
    rw [hcongr _ _ hfac.symm _ he] at this
    have := congrArg (fun φ => φ.hom s) this
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [← this]
    exact congrArg
      (fun φ => φ.hom (((V.fromSpecResidueField (genericPoint V)).appLE U ⊤ he₁).hom s))
      (Scheme.Hom.app_eq_appLE (f := r.fiberToSpecResidueField (genericPoint V)) (U := ⊤))
  change (r.fiber _).germToFunctionField ⊤ ((r.fiberToSpecResidueField _).appTop.hom
    ((Scheme.ΓSpecIso _).inv.hom ((V.residue _).hom (V.presheaf.germ U _ hηU s)))) = _
  erw [h2]
  rw [h3, ← functionFieldMap_comp_apply]
  have h4 : V.presheaf.germ U (genericPoint V) hηU s = algebraMap _ V.functionField
      (V.presheaf.germ U ((r.fiberι (genericPoint V) ≫ r) (genericPoint _)) (hgenU _) s) :=
    (Scheme.algebraMap_germ_eq_germToFunctionField V (hgenU _) s).symm
  rw [h4, MMP.Mori.functionFieldMap_algebraMap_stalk, Scheme.Hom.germ_stalkMap_apply]
  refine Eq.trans ?_ (Scheme.algebraMap_germ_eq_germToFunctionField (r.fiber (genericPoint V))
    (U := (r.fiberι (genericPoint V) ≫ r) ⁻¹ᵁ U) (hgenU _) _).symm
  change (r.fiber _).presheaf.germ ⊤ _ _ (((r.fiberι _ ≫ r).app U ≫
    (r.fiber _).presheaf.map (homOfLE he).op).hom s) = (r.fiber _).presheaf.germ _ _ _ _
  rw [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.germ_res_apply]

/- ### Riemann–Roch along the horizontal prime divisors

The prime divisors of `Y` dominating `V` are the closed points of the generic fibre
`Y_η = Y ×_V Spec k(V)`, a smooth proper curve over `k(V)` with function field `k(Y)`; the
statements below are its Riemann–Roch theory read on `Y`, the degree of a closed point `Q` being
`[κ(Q) : k(V)] = MMP.Flips.genericFiberPointDegree r Q`. -/

/-- The *horizontal Riemann–Roch space* `L(E) = {g ∈ k(Y) : v_Q(g) ≤ exp(E_Q)}` of a divisor `E`
of `Y` over `r : Y ⟶ V`, the conditions being imposed along the prime divisors `Q` dominating
`V` only: the global sections over `Y_η` of `𝒪(E)`, a `k(V)`-subspace of `k(Y)`. -/
private noncomputable def horizontalSections {Y V : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V] (r : Y ⟶ V) [IsDominant r]
    (E : Divisor Y) :
    letI := functionFieldMapAlgebra r
    Submodule V.functionField Y.functionField :=
  letI := functionFieldMapAlgebra r
  { carrier := {g | ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
        Q.divisorialValuation g ≤ WithZero.exp (E Q)}
    add_mem' := fun {a b} ha hb Q hQ =>
      ((Q.divisorialValuation).map_add a b).trans (max_le (ha Q hQ) (hb Q hQ))
    zero_mem' := fun Q _ => by simp
    smul_mem' := fun c g hg Q hQ => by
      rw [Algebra.smul_def, map_mul]
      calc Q.divisorialValuation (algebraMap V.functionField Y.functionField c) *
            Q.divisorialValuation g ≤ 1 * WithZero.exp (E Q) :=
            mul_le_mul' (divisorialValuation_functionFieldMap_le_one r Q hQ c) (hg Q hQ)
        _ = WithZero.exp (E Q) := one_mul _ }

private theorem mem_horizontalSections {Y V : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V] {r : Y ⟶ V} [IsDominant r]
    {E : Divisor Y} {g : Y.functionField} :
    letI := functionFieldMapAlgebra r
    g ∈ horizontalSections r E ↔ ∀ Q : MMP.Mori.PrimeDivisor Y,
      r Q.genericPoint = genericPoint V → Q.divisorialValuation g ≤ WithZero.exp (E Q) :=
  Iff.rfl

/-- The degree on the generic fibre of an integral divisor, as an integer sum. -/
private theorem genericFiberDegree_toQDivisor {Y V : Scheme.{0}} [IrreducibleSpace V] (r : Y ⟶ V)
    (E : Divisor Y) :
    MMP.Flips.genericFiberDegree r (Divisor.toQDivisor E) =
      ((∑ Q ∈ E.support, E Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) : ℤ) : ℚ) := by
  classical
  have hs : (Divisor.toQDivisor E).support = E.support := by
    ext Q
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
    change (Divisor.toQDivisor E).coeff Q ≠ 0 ↔ E Q ≠ 0
    rw [Divisor.coeff_toQDivisor, Int.cast_ne_zero]
    rfl
  unfold MMP.Flips.genericFiberDegree
  rw [hs]
  push_cast
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [Divisor.coeff_toQDivisor]
  rfl

/-- A divisor with nonnegative horizontal coefficients and degree zero on the generic fibre has
no horizontal component, closed points of the generic fibre having positive degree. -/
private theorem eq_zero_of_sum_eq_zero_of_nonneg {Y V : Scheme.{0}} [IrreducibleSpace V]
    {r : Y ⟶ V}
    (hpos : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      0 < MMP.Flips.genericFiberPointDegree r Q)
    {E : Divisor Y} (hE : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      0 ≤ E Q)
    (h0 : ∑ Q ∈ E.support, E Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) = 0)
    (Q : MMP.Mori.PrimeDivisor Y) (hQ : r Q.genericPoint = genericPoint V) : E Q = 0 := by
  classical
  have hnn : ∀ Q' ∈ E.support, 0 ≤ E Q' * (MMP.Flips.genericFiberPointDegree r Q' : ℤ) := by
    intro Q' _
    by_cases hQ' : r Q'.genericPoint = genericPoint V
    · exact mul_nonneg (hE Q' hQ') (Int.natCast_nonneg _)
    · have : MMP.Flips.genericFiberPointDegree r Q' = 0 := by
        unfold MMP.Flips.genericFiberPointDegree
        rw [if_neg hQ']
      rw [this, Nat.cast_zero, mul_zero]
  by_contra hne
  have hmem : Q ∈ E.support := Finsupp.mem_support_iff.mpr hne
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 Q hmem
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact hne h2
  · exact (hpos Q hQ).ne' (by exact_mod_cast h2)

/-- **Riemann–Roch on the generic fibre of a threefold Mori curve fibration.** Write `deg E` for
`∑_Q E_Q [κ(Q) : k(V)]` over the prime divisors `Q` dominating `V`, and `g` for the genus of the
generic fibre `C = Y_η`, a smooth proper geometrically connected curve over `κ(η) = k(V)` with
function field `k(Y)`. Then: a nonzero rational function has horizontal divisor of degree zero;
if `g = 0`, a horizontal divisor class of degree zero is principal and
`dim_{k(V)} L(E) = deg E + 1` for `E ≥ 0`; some nonzero rational top form has horizontal
canonical degree `2g - 2`; and closed points of `C` have positive degree. -/
private theorem genericFibre_riemannRoch {Y V : Scheme.{0}}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [QuasiCompact sY] {r : Y ⟶ V}
    [IsDominant r] (hr : IsContraction sY sV r)
    (hY : MMP.Mori.IsProjectiveVariety k sY) (hV : MMP.Mori.IsProjectiveVariety k sV)
    (hdY : topologicalKrullDim Y = 3) (hdV : topologicalKrullDim V = 2)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor sY 3) :
    haveI : LocallyOfFiniteType sY :=
      ((MMP.Mori.isProjectiveVariety_iff k sY).1 hY).1.toLocallyOfFiniteType
    -- a principal divisor has degree zero
    (∀ g : Y.functionField, g ≠ 0 → ∀ E : Divisor Y,
      (∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
        E Q = Y.ord g Q.genericPoint) →
      ∑ Q ∈ E.support, E Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) = 0) ∧
    -- in genus zero, a divisor of degree zero is principal along the horizontal primes
    (genus (r.fiberToSpecResidueField (genericPoint V)) = 0 →
      ∀ E : Divisor Y, ∑ Q ∈ E.support, E Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) = 0 →
      ∃ g : Y.functionField, g ≠ 0 ∧ ∀ Q : MMP.Mori.PrimeDivisor Y,
        r Q.genericPoint = genericPoint V → Y.ord g Q.genericPoint = E Q) ∧
    -- Riemann–Roch in genus zero
    (genus (r.fiberToSpecResidueField (genericPoint V)) = 0 → ∀ E : Divisor Y, 0 ≤ E →
      letI := functionFieldMapAlgebra r
      FiniteDimensional V.functionField (horizontalSections r E) ∧
        (Module.finrank V.functionField (horizontalSections r E) : ℤ) =
          ∑ Q ∈ E.support, E Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) + 1) ∧
    -- the canonical degree
    (∃ τ₀ : RationalPluriForms sY 3 ((1 : ℕ) : ℤ), τ₀ ≠ 0 ∧
      ∑ Q ∈ (divisorOfForm τ₀).support,
        (divisorOfForm τ₀) Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) =
          2 * (genus (r.fiberToSpecResidueField (genericPoint V)) : ℤ) - 2) ∧
    -- closed points of the generic fibre have finite residue fields
    (∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      0 < MMP.Flips.genericFiberPointDegree r Q) := by
  classical
  haveI : LocallyOfFiniteType sY :=
    ((MMP.Mori.isProjectiveVariety_iff k sY).1 hY).1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sV :=
    ((MMP.Mori.isProjectiveVariety_iff k sV).1 hV).1.toLocallyOfFiniteType
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.isProjectiveMorphism
  have hg : MMP.Flips.IsContraction k sV sY r :=
    ⟨((MMP.Mori.isProjectiveVariety_iff k sV).1 hV).1,
      ((MMP.Mori.isProjectiveVariety_iff k sY).1 hY).1, hr.comp_eq, inferInstance, hr.isIso_app⟩
  have hdimF' : topologicalKrullDim (r.fiber (genericPoint V)) = 1 :=
    MMP.Flips.topologicalKrullDim_genericFiber_eq_one sY sV r hr.comp_eq hr.surjective
      (by rw [hdY, hdV]; rfl)
  have hdimF : topologicalKrullDim (r.base ⁻¹' {genericPoint V}) = 1 := by
    rw [← (r.fiberHomeo (genericPoint V)).isHomeomorph.topologicalKrullDim_eq]
    exact hdimF'
  haveI := MMP.Flips.isCurve_fiberToSpecResidueField hg hdimF
  haveI := MMP.Flips.smooth_fiberToSpecResidueField hg hdimF
  haveI : IsProper (r.fiberToSpecResidueField (genericPoint V)) :=
    AlgebraicGeometry.isProper_fiberToSpecResidueField r _
  haveI := MMP.Flips.geometricallyConnected_fiberToSpecResidueField hg
  haveI := MMP.Flips.isIso_appTop_fiberToSpecResidueField hg hdimF
  haveI : IsNormal (r.fiber (genericPoint V)) := MMP.Flips.isNormal_genericFiber r
  haveI : IsLocallyNoetherian (r.fiber (genericPoint V)) :=
    LocallyOfFiniteType.isLocallyNoetherian (r.fiberToSpecResidueField (genericPoint V))
  haveI : IsIntegral (r.fiber (genericPoint V)) := by
    have := MMP.Flips.isIntegral_fiber_genericPoint r
    rwa [map_genericPoint_of_isDominant] at this
  haveI : CompactSpace (r.fiber (genericPoint V)) :=
    QuasiCompact.compactSpace_of_compactSpace (r.fiberToSpecResidueField (genericPoint V))
  have hdim1 : topologicalKrullDim (r.fiber (genericPoint V)) ≤ 1 := hdimF'.le
  have hcart : ∀ D : Divisor (r.fiber (genericPoint V)), D.IsCartier :=
    MMP.Fourfold.isCartier_of_isSmoothScheme
      ((isSmoothScheme_iff (r.fiberToSpecResidueField (genericPoint V))).mpr inferInstance)
  haveI : IsDominant (r.fiberι (genericPoint V)) := by
    refine ⟨dense_iff_closure_eq.mpr (Set.eq_univ_of_forall fun y => ?_)⟩
    have hy : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes trivial
    have hmem : genericPoint Y ∈ Set.range (r.fiberι (genericPoint V)) :=
      ⟨_, AlgebraicGeometry.Scheme.Hom.fiberι_genericFiberPoint r⟩
    exact closure_mono (Set.singleton_subset_iff.mpr hmem) (specializes_iff_mem_closure.mp hy)
  have hcl : IsClosedMap r := r.isClosedMap
  -- orders along the generic fibre
  have hordι : ∀ (Q : MMP.Mori.PrimeDivisor (r.fiber (genericPoint V))) (g : Y.functionField),
      (r.fiber (genericPoint V)).ord (functionFieldMap (r.fiberι (genericPoint V)) g)
        Q.genericPoint = Y.ord g (MMP.Flips.fiberPrimeDivisor r Q).genericPoint := by
    intro Q g
    haveI := isIso_stalkMap_fiberι_genericPoint' r Q.genericPoint
    exact MMP.Positivity.ord_functionFieldMap_of_isIso (r.fiberι (genericPoint V)) Q
      (MMP.Flips.fiberPrimeDivisor r Q) (MMP.Flips.genericPoint_fiberPrimeDivisor Q).symm g
  have hιbij : Function.Bijective (functionFieldMap (r.fiberι (genericPoint V))) := by
    haveI := isIso_stalkMap_fiberι_genericPoint' r (genericPoint (r.fiber (genericPoint V)))
    exact ConcreteCategory.bijective_of_isIso
      ((Y.presheaf.stalkCongr (Inseparable.of_eq
        (map_genericPoint_of_isDominant (r.fiberι (genericPoint V))).symm)).hom ≫
          (r.fiberι (genericPoint V)).stalkMap (genericPoint _))
  set ιe := RingEquiv.ofBijective (functionFieldMap (r.fiberι (genericPoint V))) hιbij
    with hιedef
  -- restricting divisors to the generic fibre
  let res : Divisor Y → Divisor (r.fiber (genericPoint V)) := fun E =>
    Finsupp.comapDomain (MMP.Flips.fiberPrimeDivisor r) E
      MMP.Flips.fiberPrimeDivisor_injective.injOn
  have hres : ∀ (E : Divisor Y) Q, (res E).coeff Q = E.coeff (MMP.Flips.fiberPrimeDivisor r Q) :=
    fun E Q => Finsupp.comapDomain_apply _ _ _ _
  have hdeg : ∀ (E : Divisor Y) [SheafOfModules.IsInvertible (r.fiber (genericPoint V)).presheaf
      (r.fiber (genericPoint V)).ringCatSheaf.2 (res E).divisorialSheaf],
      invertibleCurveDegree (V.residueField (genericPoint V))
        (r.fiberToSpecResidueField (genericPoint V)) hdim1 (res E).divisorialSheaf =
      ∑ Q ∈ E.support, E Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) := by
    intro E _
    have h := MMP.Flips.invertibleCurveDegree_eq_genericFiberDegree E (res E) (hres E) hdim1
    rw [genericFiberDegree_toQDivisor] at h
    exact_mod_cast h
  -- (I4)
  have hI4 : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      0 < MMP.Flips.genericFiberPointDegree r Q := fun Q hQ =>
    MMP.Flips.genericFiberPointDegree_pos_of_map_genericPoint_eq hQ
  -- (I0)
  have hI0 : ∀ g : Y.functionField, g ≠ 0 → ∀ E : Divisor Y,
      (∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
        E Q = Y.ord g Q.genericPoint) →
      ∑ Q ∈ E.support, E Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) = 0 := by
    intro g hg0 E hE
    obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (X := r.fiber (genericPoint V))
      ((map_ne_zero (functionFieldMap (r.fiberι (genericPoint V)))).mpr hg0)
    have hprinc : res E = principalDivisor φ := by
      ext Q
      change (res E).coeff Q = (principalDivisor φ).coeff Q
      rw [coeff_principalDivisor, hφ, hres, hordι]
      exact hE _ (MMP.Flips.map_genericPoint_fiberPrimeDivisor Q)
    have hlin : (res E).LinearlyEquivalent 0 := by
      rw [hprinc]
      exact Divisor.linearlyEquivalent_principalDivisor_zero φ
    haveI := (hcart (res E)).isInvertibleModule_divisorialSheaf
    have h := hdeg E
    rw [invertibleCurveDegree_eq_zero_of_iso_unit _ _ hdim1 _
      (hlin.divisorialSheafIso ≪≫ Divisor.divisorialSheafZeroIso)] at h
    exact h.symm
  -- (I3)
  have hI3 : ∃ τ₀ : RationalPluriForms sY 3 ((1 : ℕ) : ℤ), τ₀ ≠ 0 ∧
      ∑ Q ∈ (divisorOfForm τ₀).support,
        (divisorOfForm τ₀) Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) =
          2 * (genus (r.fiberToSpecResidueField (genericPoint V)) : ℤ) - 2 := by
    obtain ⟨DK, hDK, ⟨eK⟩⟩ := MMP.Flips.exists_divisor_fiber_canonical hg hK
    have h2g := MMP.Flips.two_mul_genus_sub_two_eq_genericFiberDegree DK hDK eK
    rw [genericFiberDegree_toQDivisor] at h2g
    letI := functionFieldAlgebra sY
    have hd3 : topologicalKrullDim Y = ((3 : ℕ) : WithBot ℕ∞) := by rw [hdY]; rfl
    obtain ⟨b⟩ := exists_basis_topForms (sX := sY) (d := 3) hd3
    set τ₀ : RationalPluriForms sY 3 ((1 : ℕ) : ℤ) :=
      (formPow (b ()) 1 : PluriForms k Y.functionField 3 ((1 : ℕ) : ℤ)) with hτ₀def
    have hτ₀0 : τ₀ ≠ 0 := formPow_ne_zero_of_ne_zero hd3 (b.ne_zero ()) 1
    refine ⟨τ₀, hτ₀0, ?_⟩
    obtain ⟨ψ, hψ⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul
      hr.isNormalVariety_source hK hτ₀0
    obtain ⟨g, hg0, hgψ⟩ := MMP.Positivity.exists_ord_eq_of_units ψ
    set w : MMP.Mori.PrimeDivisor Y → ℤ :=
      fun Q => (MMP.Flips.genericFiberPointDegree r Q : ℤ) with hwdef
    set degL : Divisor Y →ₗ[ℤ] ℤ := Finsupp.linearCombination ℤ w with hdegLdef
    have hdegL : ∀ E : Divisor Y, ∑ Q ∈ E.support, E Q * w Q = degL E := by
      intro E
      rw [hdegLdef, Finsupp.linearCombination_apply, Finsupp.sum]
      rfl
    have hP := hI0 g hg0 (principalDivisor ψ) fun Q _ => by
      change (principalDivisor ψ).coeff Q = _
      rw [coeff_principalDivisor, hgψ]
    change ∑ Q ∈ (principalDivisor ψ).support, (principalDivisor ψ) Q * w Q = 0 at hP
    rw [hdegL] at hP
    change ∑ Q ∈ (divisorOfForm τ₀).support, (divisorOfForm τ₀) Q * w Q = _
    rw [hdegL, eq_add_of_sub_eq hψ, map_add, hP, zero_add, Nat.cast_one, one_smul, ← hdegL]
    exact_mod_cast h2g.symm
  -- the constants of `C`
  have hresbij : Function.Bijective (V.residue (genericPoint V)).hom := by
    refine ⟨?_, V.residue_surjective _⟩
    change Function.Injective (IsLocalRing.residue (V.presheaf.stalk _))
    rw [RingHom.injective_iff_ker_eq_bot, IsLocalRing.ker_residue,
      IsLocalRing.maximalIdeal_eq_bot]
  set i : V.residueField (genericPoint V) →+* V.functionField :=
    (RingEquiv.ofBijective (V.residue (genericPoint V)).hom hresbij).symm.toRingHom with hidef
  have hi : ∀ c, (V.residue (genericPoint V)).hom (i c) = c := fun c =>
    (RingEquiv.ofBijective (V.residue (genericPoint V)).hom hresbij).apply_symm_apply c
  have hibij : Function.Bijective i :=
    (RingEquiv.ofBijective (V.residue (genericPoint V)).hom hresbij).symm.bijective
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents (r.fiber (genericPoint V))) := by
    obtain ⟨x⟩ : Nonempty (r.fiber (genericPoint V)) := inferInstance
    obtain ⟨Z, -⟩ := exists_mem_irreducibleComponents x
    exact ⟨Z⟩
  -- a nonzero global section of a degree-zero sheaf in genus zero
  refine ⟨hI0, fun hgen E hE => ?_, fun hgen E hE0 => ?_, hI3, hI4⟩
  · -- (I1)
    haveI := (hcart (res E)).isInvertibleModule_divisorialSheaf
    have hdeg0 : invertibleCurveDegree (V.residueField (genericPoint V))
        (r.fiberToSpecResidueField (genericPoint V)) hdim1 (res E).divisorialSheaf = 0 := by
      rw [hdeg E, hE]
    have hRR := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus
      (V.residueField (genericPoint V)) (r.fiberToSpecResidueField (genericPoint V)) hdim1
      (res E).divisorialSheaf
    rw [hdeg0] at hRR
    erw [hgen] at hRR
    have hpos : 0 < Module.finrank (V.residueField (genericPoint V))
        ((restrictScalarsOverBase (V.residueField (genericPoint V))
          (r.fiberToSpecResidueField (genericPoint V))).obj
            ((SheafOfModules.evaluation _ (Opposite.op ⊤)).obj (res E).divisorialSheaf)) := by
      rw [← (cohomologyOverFieldZeroLinearIso (V.residueField (genericPoint V))
        (r.fiberToSpecResidueField (genericPoint V))
          (res E).divisorialSheaf).toLinearEquiv.finrank_eq]
      have h1 := Int.natCast_nonneg (Module.finrank (V.residueField (genericPoint V))
        (cohomologyOverField (V.residueField (genericPoint V))
          (r.fiberToSpecResidueField (genericPoint V)) (res E).divisorialSheaf 1))
      push_cast at hRR
      omega
    haveI := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨σ', hσ'⟩ := exists_ne (0 : (restrictScalarsOverBase (V.residueField (genericPoint V))
          (r.fiberToSpecResidueField (genericPoint V))).obj
            ((SheafOfModules.evaluation _ (Opposite.op ⊤)).obj (res E).divisorialSheaf))
    set σ : (res E).divisorialSubmodule ⊤ := σ' with hσdef
    have hσ0 : σ ≠ 0 := hσ'
    have hval0 : componentSectionValue Z₀ σ ≠ 0 := by
      intro h0
      apply hσ0
      apply componentSectionValue_injective Z₀
      rw [h0]
      exact (map_zero (MMP.Positivity.componentToFunctionField Z₀).hom).symm
    set g₁ := ιe.symm (componentSectionValue Z₀ σ) with hg₁def
    have hg₁ : functionFieldMap (r.fiberι (genericPoint V)) g₁ = componentSectionValue Z₀ σ := by
      rw [hg₁def]
      exact ιe.apply_symm_apply _
    have hg₁0 : g₁ ≠ 0 := fun h0 => hval0 (by rw [← hg₁, h0, map_zero])
    have hle : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
        -E Q ≤ Y.ord g₁ Q.genericPoint := by
      intro Q hQ
      obtain ⟨Q', rfl⟩ := MMP.Flips.mem_range_fiberPrimeDivisor hQ
      have h1 := neg_coeff_le_ord_sectionValue Z₀ hσ0 Q'
      rw [← hg₁, hordι] at h1
      have h2 := hres E Q'
      change -(res E) Q' ≤ _ at h1
      change (res E) Q' = E (MMP.Flips.fiberPrimeDivisor r Q') at h2
      rw [h2] at h1
      exact h1
    obtain ⟨φ₁, hφ₁⟩ := MMP.Positivity.exists_units_of_ne_zero (X := Y) hg₁0
    have hP := hI0 g₁ hg₁0 (principalDivisor φ₁) fun Q _ => by
      change (principalDivisor φ₁).coeff Q = _
      rw [coeff_principalDivisor, hφ₁]
    set w : MMP.Mori.PrimeDivisor Y → ℤ :=
      fun Q => (MMP.Flips.genericFiberPointDegree r Q : ℤ) with hwdef
    set degL : Divisor Y →ₗ[ℤ] ℤ := Finsupp.linearCombination ℤ w with hdegLdef
    have hdegL : ∀ E : Divisor Y, ∑ Q ∈ E.support, E Q * w Q = degL E := by
      intro E
      rw [hdegLdef, Finsupp.linearCombination_apply, Finsupp.sum]
      rfl
    have hsum : ∑ Q ∈ (E + principalDivisor φ₁).support,
        (E + principalDivisor φ₁) Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) = 0 := by
      change ∑ Q ∈ _, _ * w Q = 0
      change ∑ Q ∈ _, _ * w Q = 0 at hE hP
      rw [hdegL] at hE hP ⊢
      rw [map_add, hE, hP, add_zero]
    have hzero := eq_zero_of_sum_eq_zero_of_nonneg hI4 (E := E + principalDivisor φ₁)
      (fun Q hQ => by
        change 0 ≤ E Q + (principalDivisor φ₁).coeff Q
        rw [coeff_principalDivisor, hφ₁]
        have := hle Q hQ
        omega) hsum
    refine ⟨g₁⁻¹, inv_ne_zero hg₁0, fun Q hQ => ?_⟩
    have h1 := hzero Q hQ
    change E Q + (principalDivisor φ₁).coeff Q = 0 at h1
    rw [coeff_principalDivisor, hφ₁] at h1
    rw [← zpow_neg_one, MMP.Mori.ord_zpow _ hg₁0]
    omega
  · -- (I2)
    letI := functionFieldMapAlgebra r
    have hE0' : ∀ Q, 0 ≤ E Q := fun Q => by
      have := hE0 Q
      simpa only [Finsupp.coe_zero, Pi.zero_apply] using this
    have hd0 : 0 ≤ ∑ Q ∈ E.support, E Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) :=
      Finset.sum_nonneg fun Q _ => mul_nonneg (hE0' Q) (Int.natCast_nonneg _)
    rcases hd0.lt_or_eq with hpos | hzero
    · -- positive degree: Riemann–Roch on `C`
      haveI := (hcart (res E)).isInvertibleModule_divisorialSheaf
      have hdegpos : 0 < invertibleCurveDegree (V.residueField (genericPoint V))
          (r.fiberToSpecResidueField (genericPoint V)) hdim1 (res E).divisorialSheaf := by
        rw [hdeg E]
        exact hpos
      have hRR := finrank_globalSections_eq_invertibleCurveDegree_add_one
        (V.residueField (genericPoint V)) (r.fiberToSpecResidueField (genericPoint V)) hdim1
        (res E).divisorialSheaf hgen hdegpos
      rw [hdeg E] at hRR
      -- the sections of `𝒪_C(E_C)` are the horizontal Riemann–Roch space
      have hmem : ∀ σ : (res E).divisorialSubmodule ⊤,
          ιe.symm (componentSectionValue Z₀ σ) ∈ horizontalSections r E := by
        intro σ
        rw [mem_horizontalSections]
        intro Q hQ
        obtain ⟨Q', rfl⟩ := MMP.Flips.mem_range_fiberPrimeDivisor hQ
        by_cases hσ : σ = 0
        · rw [hσ, show componentSectionValue Z₀ (0 : (res E).divisorialSubmodule ⊤) = 0 from
            map_zero (MMP.Positivity.componentToFunctionField Z₀).hom, map_zero, map_zero]
          exact WithZero.zero_le _
        · have hv0 : componentSectionValue Z₀ σ ≠ 0 := by
            intro h0
            apply hσ
            apply componentSectionValue_injective Z₀
            rw [h0]
            exact (map_zero (MMP.Positivity.componentToFunctionField Z₀).hom).symm
          have hg0 : ιe.symm (componentSectionValue Z₀ σ) ≠ 0 :=
            (map_ne_zero_iff _ ιe.symm.injective).mpr hv0
          have h1 := neg_coeff_le_ord_sectionValue Z₀ hσ Q'
          have h2 : functionFieldMap (r.fiberι (genericPoint V))
              (ιe.symm (componentSectionValue Z₀ σ)) =
              componentSectionValue Z₀ σ := ιe.apply_symm_apply _
          rw [← h2, hordι] at h1
          have h3 := hres E Q'
          change (res E) Q' = E (MMP.Flips.fiberPrimeDivisor r Q') at h3
          rw [h3] at h1
          rw [(MMP.Flips.fiberPrimeDivisor r Q').divisorialValuation_eq_exp_neg_ord hg0,
            WithZero.exp_le_exp]
          omega
      let jf : (res E).divisorialSubmodule ⊤ →+ horizontalSections r E :=
        { toFun := fun σ => ⟨ιe.symm (componentSectionValue Z₀ σ), hmem σ⟩
          map_zero' := Subtype.ext (by
            change ιe.symm (componentSectionValue Z₀ 0) = 0
            rw [show componentSectionValue Z₀ (0 : (res E).divisorialSubmodule ⊤) = 0 from
              map_zero (MMP.Positivity.componentToFunctionField Z₀).hom, map_zero])
          map_add' := fun σ τ => Subtype.ext (by
            change ιe.symm (componentSectionValue Z₀ (σ + τ)) =
              ιe.symm (componentSectionValue Z₀ σ) +
              ιe.symm (componentSectionValue Z₀ τ)
            rw [componentSectionValue_add, map_add]) }
      have hjinj : Function.Injective jf := by
        intro σ τ h
        have h1 : ιe.symm (componentSectionValue Z₀ σ) = ιe.symm (componentSectionValue Z₀ τ) :=
          congrArg Subtype.val h
        exact componentSectionValue_injective Z₀ (ιe.symm.injective h1)
      have hjsurj : Function.Surjective jf := by
        rintro ⟨g, hg⟩
        rw [mem_horizontalSections] at hg
        obtain ⟨σ, hσ⟩ := exists_sectionValue_eq (D := res E) Z₀
          (f := functionFieldMap (r.fiberι (genericPoint V)) g) fun E' hne => by
            have hg0 : g ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
            have h1 := hg _ (MMP.Flips.map_genericPoint_fiberPrimeDivisor E')
            rw [(MMP.Flips.fiberPrimeDivisor r E').divisorialValuation_eq_exp_neg_ord hg0,
              WithZero.exp_le_exp] at h1
            rw [hordι]
            have h3 := hres E E'
            change (res E) E' = E (MMP.Flips.fiberPrimeDivisor r E') at h3
            change -(res E) E' ≤ _
            rw [h3]
            omega
        refine ⟨σ, Subtype.ext ?_⟩
        change ιe.symm (componentSectionValue Z₀ σ) = g
        rw [hσ]
        exact ιe.symm_apply_apply g
      have hsmul : ∀ (c : V.residueField (genericPoint V))
          (σ : (restrictScalarsOverBase (V.residueField (genericPoint V))
            (r.fiberToSpecResidueField (genericPoint V))).obj
              ((SheafOfModules.evaluation _ (Opposite.op ⊤)).obj (res E).divisorialSheaf)),
          jf (show (res E).divisorialSubmodule ⊤ from c • σ) =
            i c • jf (show (res E).divisorialSubmodule ⊤ from σ) := by
        intro c σ
        refine Subtype.ext ?_
        change ιe.symm (componentSectionValue Z₀ ((((Scheme.ΓSpecIso _).inv ≫
          (r.fiberToSpecResidueField (genericPoint V)).appLE ⊤ ⊤ _).hom c) •
            (show (res E).divisorialSubmodule ⊤ from σ))) =
          i c • ιe.symm (componentSectionValue Z₀ (show (res E).divisorialSubmodule ⊤ from σ))
        rw [componentSectionValue_smul]
        have happ : (r.fiberToSpecResidueField (genericPoint V)).appLE ⊤ ⊤ (by simp) =
            (r.fiberToSpecResidueField (genericPoint V)).appTop :=
          Scheme.Hom.appLE_eq_app (f := r.fiberToSpecResidueField (genericPoint V)) (U := ⊤)
        have hιe : ∀ x, ιe.symm (functionFieldMap (r.fiberι (genericPoint V)) x) = x :=
          fun x => ιe.symm_apply_apply x
        rw [happ]
        conv_lhs => rw [← hi c]
        erw [germToFunctionField_appTop_residue r (i c)]
        rw [map_mul, hιe, Algebra.smul_def]
        rfl
      have hrank := rank_eq_of_equiv_equiv i
        (AddEquiv.ofBijective jf ⟨hjinj, hjsurj⟩ :
          (restrictScalarsOverBase (V.residueField (genericPoint V))
            (r.fiberToSpecResidueField (genericPoint V))).obj
              ((SheafOfModules.evaluation _ (Opposite.op ⊤)).obj (res E).divisorialSheaf) ≃+
            horizontalSections r E) hibij (fun c σ => hsmul c σ)
      have hfin : Module.finrank V.functionField (horizontalSections r E) =
          Module.finrank (V.residueField (genericPoint V))
            ((restrictScalarsOverBase (V.residueField (genericPoint V))
              (r.fiberToSpecResidueField (genericPoint V))).obj
                ((SheafOfModules.evaluation _ (Opposite.op ⊤)).obj (res E).divisorialSheaf)) := by
        unfold Module.finrank
        rw [hrank]
      have hfpos : 0 < Module.finrank V.functionField (horizontalSections r E) := by
        have : (0 : ℤ) < Module.finrank V.functionField (horizontalSections r E) := by
          rw [hfin, hRR]
          omega
        exact_mod_cast this
      exact ⟨Module.finite_of_finrank_pos hfpos, by rw [hfin, hRR]⟩
    · -- degree zero: the constants
      have hEh : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V → E Q = 0 :=
        eq_zero_of_sum_eq_zero_of_nonneg hI4 (fun Q _ => hE0' Q) hzero.symm
      have hspan : horizontalSections r E = Submodule.span V.functionField {1} := by
        ext g
        rw [mem_horizontalSections, Submodule.mem_span_singleton]
        constructor
        · intro hg
          obtain ⟨c, hc⟩ := exists_functionFieldMap_eq_of_forall_ord_nonneg r hr.isIso_app hcl g
            fun Q hQ => by
              rcases eq_or_ne g 0 with h0 | h0
              · rw [h0, Scheme.ord_zero, Pi.zero_apply]
              · have h1 := hg Q hQ
                rw [hEh Q hQ, Q.divisorialValuation_eq_exp_neg_ord h0, WithZero.exp_le_exp] at h1
                omega
          refine ⟨c, ?_⟩
          rw [Algebra.smul_def, mul_one]
          exact hc
        · rintro ⟨c, rfl⟩ Q hQ
          rw [hEh Q hQ, WithZero.exp_zero, Algebra.smul_def, mul_one]
          exact divisorialValuation_functionFieldMap_le_one r Q hQ c
      rw [hspan, finrank_span_singleton (one_ne_zero (α := Y.functionField)), ← hzero]
      exact ⟨inferInstance, by norm_num⟩

/-- **The floor coordinate and the logarithmic form of the generic conic.** Granting Riemann–Roch
on the generic fibre (`genericFibre_riemannRoch`) and a nonzero rational `m`-canonical form `α₀`
with `ord_Q α₀ = -m B_Q` along the horizontal primes, where `B ≥ 0` has horizontal floor of
degree two: there are a rational function `x` with a simple pole along every horizontal floor
prime and no other horizontal pole, and a rational top form `θ` whose horizontal divisor is
exactly minus the horizontal floor. -/
private theorem exists_floor_coordinate_and_form {Y V : Scheme.{0}}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V]
    [Infinite V.functionField]
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] {r : Y ⟶ V} [IsDominant r]
    (hdY : topologicalKrullDim Y = 3)
    (h0 : ∀ g : Y.functionField, g ≠ 0 → ∀ E : Divisor Y,
      (∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
        E Q = Y.ord g Q.genericPoint) →
      ∑ Q ∈ E.support, E Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) = 0)
    {gC : ℕ}
    (h1 : gC = 0 → ∀ E : Divisor Y,
      ∑ Q ∈ E.support, E Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) = 0 →
      ∃ g : Y.functionField, g ≠ 0 ∧ ∀ Q : MMP.Mori.PrimeDivisor Y,
        r Q.genericPoint = genericPoint V → Y.ord g Q.genericPoint = E Q)
    (h2 : gC = 0 → ∀ E : Divisor Y, 0 ≤ E →
      letI := functionFieldMapAlgebra r
      FiniteDimensional V.functionField (horizontalSections r E) ∧
        (Module.finrank V.functionField (horizontalSections r E) : ℤ) =
          ∑ Q ∈ E.support, E Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) + 1)
    (h3 : ∃ τ₀ : RationalPluriForms sY 3 ((1 : ℕ) : ℤ), τ₀ ≠ 0 ∧
      ∑ Q ∈ (divisorOfForm τ₀).support,
        (divisorOfForm τ₀) Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) = 2 * (gC : ℤ) - 2)
    (h4 : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      0 < MMP.Flips.genericFiberPointDegree r Q)
    {B : QDivisor Y} (hB0 : ∀ Q, 0 ≤ B Q)
    (hdeg : open scoped Classical in
      ∑ Q ∈ B.support with B Q = 1 ∧ r Q.genericPoint = genericPoint V,
        MMP.Flips.genericFiberPointDegree r Q = 2)
    {m : ℕ} (hm : 0 < m) {α₀ : RationalPluriForms sY 3 m} (hα₀ : α₀ ≠ 0)
    (hα : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      (Q.ordForm α₀ : ℚ) = -(m : ℚ) * B Q) :
    letI := functionFieldAlgebra sY
    gC = 0 ∧ ∃ (x : Y.functionField) (θ : ⋀[Y.functionField]^3 Ω[Y.functionField⁄k]), θ ≠ 0 ∧
      ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
        (B Q = 1 → Y.ord x Q.genericPoint = -1 ∧
          Q.ordForm (sX := sY) (d := 3) (m := ((1 : ℕ) : ℤ)) (formPow θ 1) = -1) ∧
        (B Q ≠ 1 → 0 ≤ Y.ord x Q.genericPoint ∧
          Q.ordForm (sX := sY) (d := 3) (m := ((1 : ℕ) : ℤ)) (formPow θ 1) = 0) := by
  classical
  letI := functionFieldAlgebra sY
  have hd3 : topologicalKrullDim Y = ((3 : ℕ) : WithBot ℕ∞) := by rw [hdY]; rfl
  -- the degree along the horizontal primes
  set w : MMP.Mori.PrimeDivisor Y → ℤ :=
    fun Q => (MMP.Flips.genericFiberPointDegree r Q : ℤ) with hwdef
  set degL : Divisor Y →ₗ[ℤ] ℤ := Finsupp.linearCombination ℤ w with hdegLdef
  have hdegL : ∀ E : Divisor Y, ∑ Q ∈ E.support, E Q * w Q = degL E := by
    intro E
    rw [hdegLdef, Finsupp.linearCombination_apply, Finsupp.sum]
    rfl
  have hwvert : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint ≠ genericPoint V → w Q = 0 := by
    intro Q hQ
    simp only [hwdef]
    unfold MMP.Flips.genericFiberPointDegree
    rw [if_neg hQ]
    rfl
  have hwnn : ∀ Q, 0 ≤ w Q := fun Q => Int.natCast_nonneg _
  obtain ⟨b⟩ := exists_basis_topForms (sX := sY) (d := 3) hd3
  -- the canonical form `θ₀`
  obtain ⟨τ₀, hτ₀0, hτ₀⟩ := h3
  set θ₀ : ⋀[Y.functionField]^3 Ω[Y.functionField⁄k] :=
    (ZTensorPower.basis b ((1 : ℕ) : ℤ)).repr τ₀ () • b () with hθ₀def
  have hτθ : τ₀ = (formPow θ₀ 1 : PluriForms k Y.functionField 3 ((1 : ℕ) : ℤ)) := by
    rw [hθ₀def, formPow_smul, pow_one]
    exact eq_repr_smul_formPow b τ₀
  have hθ₀0 : θ₀ ≠ 0 := by
    intro h
    apply hτ₀0
    rw [hτθ, h, show (0 : ⋀[Y.functionField]^3 Ω[Y.functionField⁄k]) = (0 : Y.functionField) • 0
      from (zero_smul _ _).symm, formPow_smul, pow_one]
    exact zero_smul _ _
  have hθ₀f0 : (formPow θ₀ 1 : RationalPluriForms sY 3 ((1 : ℕ) : ℤ)) ≠ 0 := by
    rwa [← hτθ]
  have hτord : ∀ Q : MMP.Mori.PrimeDivisor Y, Q.ordForm τ₀ =
      Q.ordForm (sX := sY) (d := 3) (m := ((1 : ℕ) : ℤ)) (formPow θ₀ 1) := fun Q => by
    rw [hτθ]
  -- `α₀ = F θ₀^{⊗m}`
  set cθ := b.repr θ₀ ()
  have hθb : θ₀ = cθ • b () := (basis_unit_repr_smul b θ₀).symm
  have hcθ : cθ ≠ 0 := fun h => hθ₀0 (by rw [hθb, h, zero_smul])
  set F : Y.functionField := (ZTensorPower.basis b m).repr α₀ () / cθ ^ m
  have hαF : α₀ = (F • formPow θ₀ m : PluriForms k Y.functionField 3 m) := by
    rw [hθb, formPow_smul, smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ hcθ)]
    exact eq_repr_smul_formPow b α₀
  have hF0 : F ≠ 0 := by
    rintro h
    apply hα₀
    rw [hαF, h]
    exact zero_smul _ _
  have hordF : ∀ Q : MMP.Mori.PrimeDivisor Y, Q.ordForm α₀ = Y.ord F Q.genericPoint +
      m * Q.ordForm (sX := sY) (d := 3) (m := ((1 : ℕ) : ℤ)) (formPow θ₀ 1) := by
    intro Q
    rw [hαF]
    exact ordForm_smul_formPow (sX := sY) Q hd3 hθ₀0 hF0 m
  -- (I0) for `F`
  set E₀ : Divisor Y := divisorOfForm α₀ - (m : ℤ) • divisorOfForm τ₀ with hE₀def
  have hE₀ : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      E₀ Q = Y.ord F Q.genericPoint := by
    intro Q _
    have h := hordF Q
    simp only [hE₀def, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
    change Q.ordForm α₀ - (m : ℤ) * Q.ordForm τ₀ = _
    rw [hτord]
    omega
  have hdeg0 := h0 F hF0 E₀ hE₀
  rw [hdegL, hE₀def, map_sub, map_smul, smul_eq_mul] at hdeg0
  -- the floor
  set H := B.support.filter (fun Q => B Q = 1 ∧ r Q.genericPoint = genericPoint V) with hHdef
  have hHw : ∑ Q ∈ H, w Q = 2 := by
    simp only [hwdef]
    exact_mod_cast hdeg
  -- `deg(div α₀) ≤ -2m`
  have hαdeg : degL (divisorOfForm α₀) ≤ -2 * m := by
    rw [← hdegL]
    have hHS : H ⊆ (divisorOfForm α₀).support := by
      intro Q hQ
      obtain ⟨-, hB1, hQh⟩ := Finset.mem_filter.mp hQ
      rw [Finsupp.mem_support_iff]
      change Q.ordForm α₀ ≠ 0
      intro h0'
      have := hα Q hQh
      rw [h0', hB1] at this
      have hm' : (0 : ℚ) < m := by exact_mod_cast hm
      push_cast at this
      linarith
    rw [← Finset.sum_sdiff hHS]
    have h1' : ∑ Q ∈ H, (divisorOfForm α₀) Q * w Q = -m * 2 := by
      rw [← hHw, Finset.mul_sum]
      refine Finset.sum_congr rfl fun Q hQ => ?_
      obtain ⟨-, hB1, hQh⟩ := Finset.mem_filter.mp hQ
      have := hα Q hQh
      rw [hB1] at this
      have h' : Q.ordForm α₀ = -m := by
        have : (Q.ordForm α₀ : ℚ) = -(m : ℚ) := by linarith
        exact_mod_cast this
      change Q.ordForm α₀ * w Q = -m * w Q
      rw [h']
    have h2' : ∑ Q ∈ (divisorOfForm α₀).support \ H, (divisorOfForm α₀) Q * w Q ≤ 0 := by
      refine Finset.sum_nonpos fun Q _ => ?_
      change Q.ordForm α₀ * w Q ≤ 0
      by_cases hQh : r Q.genericPoint = genericPoint V
      · have hq := hα Q hQh
        have hle : Q.ordForm α₀ ≤ 0 := by
          have : (Q.ordForm α₀ : ℚ) ≤ 0 := by
            rw [hq]
            have := hB0 Q
            have hm' : (0 : ℚ) ≤ m := by positivity
            nlinarith
          exact_mod_cast this
        exact mul_nonpos_of_nonpos_of_nonneg hle (hwnn Q)
      · rw [hwvert Q hQh, mul_zero]
    linarith
  have h3' : degL (divisorOfForm τ₀) = 2 * (gC : ℤ) - 2 := by
    rw [← hdegL]
    exact hτ₀
  have hle : degL (divisorOfForm τ₀) ≤ -2 := by
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    by_contra hc
    push Not at hc
    nlinarith
  have hgC : gC = 0 := by omega
  have hθdeg : degL (divisorOfForm τ₀) = -2 := by
    rw [h3', hgC]
    norm_num
  -- the floor divisor `D`
  set D : Divisor Y := ∑ Q ∈ H, Finsupp.single Q (1 : ℤ) with hDdef
  have hDQ : ∀ Q, D Q = if Q ∈ H then 1 else 0 := by
    intro Q
    rw [hDdef, Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hdegD : degL D = 2 := by
    rw [hDdef, map_sum]
    simp only [hdegLdef, Finsupp.linearCombination_single, one_smul]
    exact hHw
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun Q _ => Finsupp.single_nonneg.2 zero_le_one
  set E₁ := D + divisorOfForm τ₀ with hE₁def
  obtain ⟨g, hg0, hg⟩ := h1 hgC E₁ (by rw [hdegL, hE₁def, map_add, hdegD, hθdeg]; norm_num)
  have hθ0 : g⁻¹ • θ₀ ≠ 0 := smul_ne_zero (inv_ne_zero hg0) hθ₀0
  have hordθ : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      Q.ordForm (sX := sY) (d := 3) (m := ((1 : ℕ) : ℤ)) (formPow (g⁻¹ • θ₀) 1) = -D Q := by
    intro Q hQ
    rw [formPow_smul, pow_one, ordForm_smul_formPow (sX := sY) Q hd3 hθ₀0 (inv_ne_zero hg0) 1,
      ← zpow_neg_one, MMP.Mori.ord_zpow _ hg0, hg Q hQ]
    simp only [hE₁def, Finsupp.add_apply]
    change -1 * (D Q + Q.ordForm τ₀) + ((1 : ℕ) : ℤ) * Q.ordForm _ = -D Q
    rw [hτord]
    push_cast
    ring
  -- the floor coordinate `x`
  obtain ⟨hfinD, hrkD⟩ := h2 hgC D hD0
  have hrkD' : Module.finrank V.functionField (horizontalSections r D) = 3 := by
    rw [hdegL, hdegD] at hrkD
    omega
  letI := functionFieldMapAlgebra r
  have hsub : ∀ Q ∈ H, horizontalSections r (D - Finsupp.single Q 1) <
      horizontalSections r D := by
    intro Q hQ
    have hQD : D Q = 1 := by rw [hDQ, if_pos hQ]
    have hle : horizontalSections r (D - Finsupp.single Q 1) ≤ horizontalSections r D := by
      intro g hg
      rw [mem_horizontalSections] at hg ⊢
      intro Q' hQ'
      refine (hg Q' hQ').trans (WithZero.exp_le_exp.mpr ?_)
      rw [Finsupp.sub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    have hnonneg : 0 ≤ D - Finsupp.single Q 1 := by
      intro Q'
      rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply]
      split_ifs with h
      · subst h
        omega
      · have := hD0 Q'
        simp only [Finsupp.coe_zero, Pi.zero_apply] at this
        omega
    obtain ⟨-, hrk'⟩ := h2 hgC _ hnonneg
    refine lt_of_le_of_ne hle fun heq => ?_
    have h3e : Module.finrank V.functionField
        (horizontalSections r (D - Finsupp.single Q 1)) = 3 := by
      rw [heq]
      exact hrkD'
    rw [hdegL, map_sub, hdegD, hdegLdef, Finsupp.linearCombination_single, one_smul, h3e] at hrk'
    have hwQ : (0 : ℤ) < w Q := by
      simp only [hwdef]
      exact_mod_cast h4 Q (Finset.mem_filter.mp hQ).2.2
    omega
  set W := horizontalSections r D
  let p : H → Submodule V.functionField W :=
    fun Q => (horizontalSections r (D - Finsupp.single Q.1 1)).comap W.subtype
  have hp : ∀ Q, p Q ≠ ⊤ := by
    intro Q htop
    have hlt := hsub Q.1 Q.2
    have hle : W ≤ horizontalSections r (D - Finsupp.single Q.1 1) := by
      intro g hg
      have hmem : (⟨g, hg⟩ : W) ∈ p Q := by
        rw [htop]
        exact Submodule.mem_top
      exact hmem
    exact lt_irrefl _ (lt_of_lt_of_le hlt hle)
  obtain ⟨⟨x, hxD⟩, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  have hxQ : ∀ Q ∈ H, x ∉ horizontalSections r (D - Finsupp.single Q 1) :=
    fun Q hQ h => hx ⟨Q, hQ⟩ h
  have hHne : H.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro hH
    rw [hH, Finset.sum_empty] at hHw
    norm_num at hHw
  have hx0 : x ≠ 0 := by
    rintro rfl
    obtain ⟨Q, hQ⟩ := hHne
    exact hxQ Q hQ (Submodule.zero_mem _)
  have hxD' := mem_horizontalSections.mp hxD
  refine ⟨hgC, x, g⁻¹ • θ₀, hθ0, fun Q hQh => ⟨fun hB1 => ?_, fun hB1 => ?_⟩⟩
  · have hQH : Q ∈ H := Finset.mem_filter.mpr
      ⟨Finsupp.mem_support_iff.mpr (by rw [hB1]; norm_num), hB1, hQh⟩
    refine ⟨?_, by rw [hordθ Q hQh, hDQ, if_pos hQH]⟩
    have hle := hxD' Q hQh
    rw [hDQ, if_pos hQH, Q.divisorialValuation_eq_exp_neg_ord hx0] at hle
    have hnot := hxQ Q hQH
    rw [mem_horizontalSections] at hnot
    push Not at hnot
    obtain ⟨Q', hQ'h, hlt⟩ := hnot
    by_cases hQQ : Q' = Q
    · subst hQQ
      rw [Finsupp.sub_apply, Finsupp.single_eq_same, hDQ, if_pos hQH,
        Q'.divisorialValuation_eq_exp_neg_ord hx0] at hlt
      have h1 := WithZero.exp_le_exp.mp hle
      have h2 := WithZero.exp_lt_exp.mp hlt
      omega
    · exfalso
      have hle' := hxD' Q' hQ'h
      rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hQQ), sub_zero] at hlt
      exact absurd hle' (not_le.mpr hlt)
  · have hQH : Q ∉ H := fun h => hB1 (Finset.mem_filter.mp h).2.1
    refine ⟨?_, by rw [hordθ Q hQh, hDQ, if_neg hQH, neg_zero]⟩
    have hle := hxD' Q hQh
    rw [hDQ, if_neg hQH, Q.divisorialValuation_eq_exp_neg_ord hx0] at hle
    have := WithZero.exp_le_exp.mp hle
    omega

/-- A root of a monic polynomial whose coefficients have valuation at most one has valuation at
most one: the valuation ring is integrally closed. -/
private theorem valuation_le_one_of_monic_eval {L : Type*} [Field L] (v : Valuation L ℤᵐ⁰)
    {f : Polynomial L} (hf : f.Monic) (hc : ∀ i, v (f.coeff i) ≤ 1) {z : L}
    (hz : f.eval z = 0) : v z ≤ 1 := by
  have hlift : f ∈ Polynomial.lifts (algebraMap v.integer L) :=
    (Polynomial.lifts_iff_coeff_lifts f).mpr fun n => ⟨⟨f.coeff n, hc n⟩, rfl⟩
  obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hf
  have hint : IsIntegral v.integer z :=
    ⟨g, hgm, by rw [Polynomial.eval₂_eq_eval_map, hg, hz]⟩
  exact (Valuation.integer.integers v).isIntegral_iff_v_le_one.mp hint

/-- Along a prime divisor dominating `V` where `v(x) ≤ 1`, a polynomial in `x` over `k(V)` has
valuation at most one. -/
private theorem divisorialValuation_aeval_le_one {Y V : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V] (r : Y ⟶ V) [IsDominant r]
    (Q : MMP.Mori.PrimeDivisor Y) (hQ : r Q.genericPoint = genericPoint V) {x : Y.functionField}
    (hx : Q.divisorialValuation x ≤ 1) (f : Polynomial V.functionField) :
    letI := functionFieldMapAlgebra r
    Q.divisorialValuation (Polynomial.aeval x f) ≤ 1 := by
  letI := functionFieldMapAlgebra r
  rw [Polynomial.aeval_eq_sum_range]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [Algebra.smul_def, map_mul, map_pow]
  calc Q.divisorialValuation (algebraMap V.functionField Y.functionField (f.coeff i)) *
        Q.divisorialValuation x ^ i ≤ 1 * 1 :=
        mul_le_mul' (divisorialValuation_functionFieldMap_le_one r Q hQ _) (pow_le_one' hx i)
    _ = 1 := one_mul 1

/-- **Clearing the poles of an algebraic element.** If `y` is algebraic over `k(V)(x)`, some
nonzero polynomial `q(x)` makes `q(x) y` regular along every horizontal prime where `x` is
regular: `q(x) y` is a root of the polynomial obtained from the minimal polynomial of `y` by
scaling its roots by `q(x)`, whose coefficients are polynomials in `x`. -/
private theorem exists_aeval_mul_valuation_le_one {Y V : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V] (r : Y ⟶ V) [IsDominant r]
    {x y : Y.functionField}
    (hy : letI := functionFieldMapAlgebra r
      IsAlgebraic (IntermediateField.adjoin V.functionField {x}) y) :
    letI := functionFieldMapAlgebra r
    ∃ q : Polynomial V.functionField, Polynomial.aeval x q ≠ 0 ∧
      ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
        Q.divisorialValuation x ≤ 1 →
          Q.divisorialValuation (Polynomial.aeval x q * y) ≤ 1 := by
  classical
  letI := functionFieldMapAlgebra r
  set F₀ := IntermediateField.adjoin V.functionField {x}
  set μ := minpoly F₀ y
  have hμ : μ.Monic := minpoly.monic hy.isIntegral
  have hμy : Polynomial.aeval y μ = 0 := minpoly.aeval F₀ y
  have hden : ∀ c : F₀, ∃ p q : Polynomial V.functionField, Polynomial.aeval x q ≠ 0 ∧
      (c : Y.functionField) * Polynomial.aeval x q = Polynomial.aeval x p := by
    intro c
    obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff _ _).mp c.2
    by_cases hq : Polynomial.aeval x q = 0
    · refine ⟨0, 1, by simp, ?_⟩
      rw [hpq, hq, div_zero, zero_mul, map_zero]
    · exact ⟨p, q, hq, by rw [hpq, div_mul_cancel₀ _ hq]⟩
  choose P Qd hQd hPQ using hden
  set n := μ.natDegree
  set Qx : Polynomial V.functionField := ∏ i ∈ Finset.range n, Qd (μ.coeff i) with hQxdef
  have hQx : Polynomial.aeval x Qx ≠ 0 := by
    rw [hQxdef, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hQd _
  refine ⟨Qx, hQx, fun Q hQ hxQ => ?_⟩
  set s := Polynomial.aeval x Qx
  set μL := μ.map (algebraMap F₀ Y.functionField)
  have hnL : μL.natDegree = n := (hμ.natDegree_map _)
  have hfm : (μL.scaleRoots s).Monic := (Polynomial.monic_scaleRoots_iff s).mpr (hμ.map _)
  have hfz : (μL.scaleRoots s).eval (s * y) = 0 := by
    rw [Polynomial.scaleRoots_eval_mul, Polynomial.eval_map_algebraMap, hμy, mul_zero]
  refine valuation_le_one_of_monic_eval _ hfm (fun i => ?_) hfz
  rw [Polynomial.coeff_scaleRoots, hnL, Polynomial.coeff_map]
  rcases lt_trichotomy i n with hi | rfl | hi
  · -- `c_i s^{n-i} = (c_i s) s^{n-i-1}`, and `c_i s` is a polynomial in `x`
    have hsplit : s ^ (n - i) = s * s ^ (n - i - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hcs : (algebraMap F₀ Y.functionField (μ.coeff i)) * s =
        Polynomial.aeval x (P (μ.coeff i) * ∏ j ∈ (Finset.range n).erase i, Qd (μ.coeff j)) := by
      have hs : s = Polynomial.aeval x (Qd (μ.coeff i)) *
          Polynomial.aeval x (∏ j ∈ (Finset.range n).erase i, Qd (μ.coeff j)) := by
        rw [show s = Polynomial.aeval x Qx from rfl, hQxdef,
          ← Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hi), map_mul]
      rw [map_mul, ← hPQ, hs]
      change (μ.coeff i : Y.functionField) * _ = _
      ring
    rw [hsplit, ← mul_assoc, hcs, map_mul, map_pow]
    calc _ ≤ 1 * 1 ^ (n - i - 1) :=
          mul_le_mul' (divisorialValuation_aeval_le_one r Q hQ hxQ _)
            (pow_le_pow_left₀ zero_le' (divisorialValuation_aeval_le_one r Q hQ hxQ _) _)
      _ = 1 := by simp
  · rw [hμ.coeff_natDegree, map_one, Nat.sub_self, pow_zero, mul_one, map_one]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, map_zero, zero_mul, map_zero]
    exact zero_le'

/-- **Two normalized discrete valuations with the same valuation ring agree.** If `σ` is a field
automorphism of `k(Y)` with `ord_Q(σ g) ≥ 0 ↔ ord_{Q'}(g) ≥ 0` for every `g ≠ 0`, then
`ord_Q ∘ σ = ord_{Q'}`: both are surjective homomorphisms `k(Y)^* → ℤ` with the same
non-negative part. -/
private theorem ord_eq_of_forall_nonneg_iff {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (Q Q' : MMP.Mori.PrimeDivisor Y)
    (σ : Y.functionField ≃+* Y.functionField)
    (h : ∀ g : Y.functionField, g ≠ 0 →
      (0 ≤ Y.ord (σ g) Q.genericPoint ↔ 0 ≤ Y.ord g Q'.genericPoint))
    (g : Y.functionField) : Y.ord (σ g) Q.genericPoint = Y.ord g Q'.genericPoint := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [map_zero, Scheme.ord_zero]
    rfl
  have hinv : ∀ {P : MMP.Mori.PrimeDivisor Y} {f : Y.functionField}, f ≠ 0 →
      Y.ord f⁻¹ P.genericPoint = -Y.ord f P.genericPoint := by
    intro P f hf
    rw [← zpow_neg_one, MMP.Mori.ord_zpow _ hf]
    ring
  -- a uniformizer along `Q'`
  obtain ⟨π, hπ0, hπ⟩ := MMP.CyclicChartDifferent.Aux.exists_ord_eq Q' 1
  set k := Y.ord (σ π) Q.genericPoint with hkdef
  have hσπ0 : σ π ≠ 0 := (map_ne_zero σ).mpr hπ0
  have hk0 : 0 ≤ k := (h π hπ0).mpr (by rw [hπ]; norm_num)
  have hk1 : k ≠ 0 := by
    intro hk
    have := (h π⁻¹ (inv_ne_zero hπ0)).mp (by rw [map_inv₀, hinv hσπ0, ← hkdef, hk, neg_zero])
    rw [hinv hπ0, hπ] at this
    omega
  -- every element is `π^n u` with `u` a unit along both
  have hgen : ∀ f : Y.functionField, f ≠ 0 →
      Y.ord (σ f) Q.genericPoint = k * Y.ord f Q'.genericPoint := by
    intro f hf
    set n := Y.ord f Q'.genericPoint
    set u := f * π ^ (-n)
    have hu0 : u ≠ 0 := mul_ne_zero hf (zpow_ne_zero _ hπ0)
    have hu : Y.ord u Q'.genericPoint = 0 := by
      rw [Scheme.ord_mul hf (zpow_ne_zero _ hπ0), MMP.Mori.ord_zpow _ hπ0, hπ]
      ring
    have hσu1 : 0 ≤ Y.ord (σ u) Q.genericPoint := (h u hu0).mpr hu.ge
    have hσu2 : 0 ≤ Y.ord (σ u⁻¹) Q.genericPoint :=
      (h u⁻¹ (inv_ne_zero hu0)).mpr (by rw [hinv hu0, hu, neg_zero])
    rw [map_inv₀, hinv ((map_ne_zero σ).mpr hu0)] at hσu2
    have hσu : Y.ord (σ u) Q.genericPoint = 0 := by omega
    have hf' : f = u * π ^ n := by
      rw [mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
    rw [hf', map_mul, map_zpow₀, Scheme.ord_mul ((map_ne_zero σ).mpr hu0)
      (zpow_ne_zero _ hσπ0), MMP.Mori.ord_zpow _ hσπ0, hσu, ← hkdef]
    ring
  -- `k = 1`: `ord_Q ∘ σ` is surjective
  obtain ⟨π₀, hπ₀0, hπ₀⟩ := MMP.CyclicChartDifferent.Aux.exists_ord_eq Q 1
  have h1 := hgen (σ.symm π₀) ((map_ne_zero σ.symm).mpr hπ₀0)
  rw [RingEquiv.apply_symm_apply, hπ₀] at h1
  have hk : k = 1 := Int.eq_one_of_mul_eq_one_right hk0 h1.symm
  rw [hgen g hg, hk, one_mul]

/-- **The floor coordinate is a separating transcendental.** If `x ∈ k(Y)` is transcendental over
`k(V)`, with `dim Y = 3` and `dim V = 2`, then `k(Y)` is algebraic over `k(V)(x)`: the
transcendence degree of `k(Y)/k(V)` is one, so `{x}` is a transcendence basis. -/
private theorem isAlgebraic_adjoin_of_transcendental {Y V : Scheme.{0}} [IsIntegral Y]
    [IsIntegral V] {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [LocallyOfFiniteType sY]
    [LocallyOfFiniteType sV] {r : Y ⟶ V} [IsDominant r] (hrs : r ≫ sV = sY)
    (hdY : topologicalKrullDim Y = 3) (hdV : topologicalKrullDim V = 2) {x : Y.functionField}
    (htr : letI := functionFieldMapAlgebra r; Transcendental V.functionField x) :
    letI := functionFieldMapAlgebra r
    Algebra.IsAlgebraic (IntermediateField.adjoin V.functionField {x}) Y.functionField := by
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra sV
  letI := functionFieldMapAlgebra r
  haveI : IsScalarTower k V.functionField Y.functionField := by
    subst hrs
    exact isScalarTower_functionFieldMap sV r
  have hY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (d := 3)
    (by rw [hdY]; rfl)
  have hV := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sV) (d := 2)
    (by rw [hdV]; rfl)
  haveI : FaithfulSMul k V.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap k V.functionField).injective
  haveI : FaithfulSMul V.functionField Y.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap V.functionField Y.functionField).injective
  have hadd := trdeg_add_eq k V.functionField (A := Y.functionField)
  have hfinY : Algebra.trdeg k Y.functionField < Cardinal.aleph0 := by
    by_contra h
    push Not at h
    rw [Cardinal.toNat_apply_of_aleph0_le h] at hY
    norm_num at hY
  have h1 : Algebra.trdeg k Y.functionField = 3 := by
    rw [← Cardinal.cast_toNat_of_lt_aleph0 hfinY, hY]
    rfl
  have hfinV : Algebra.trdeg k V.functionField < Cardinal.aleph0 :=
    lt_of_le_of_lt le_self_add (by rw [hadd]; exact hfinY)
  have h2 : Algebra.trdeg k V.functionField = 2 := by
    rw [← Cardinal.cast_toNat_of_lt_aleph0 hfinV, hV]
    rfl
  have hle : Algebra.trdeg V.functionField Y.functionField ≤ 1 := by
    rw [h1, h2] at hadd
    have ht : Algebra.trdeg V.functionField Y.functionField < Cardinal.aleph0 :=
      lt_of_le_of_lt le_add_self (by rw [hadd]; exact_mod_cast
        (Cardinal.natCast_lt_aleph0 : ((3 : ℕ) : Cardinal) < Cardinal.aleph0))
    obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp ht
    rw [hn] at hadd ⊢
    have : (2 : ℕ) + n = 3 := by exact_mod_cast hadd
    exact_mod_cast (show n ≤ 1 by omega)
  have hind : AlgebraicIndependent V.functionField (fun _ : Unit => x) :=
    algebraicIndependent_unique_type_iff.mpr htr
  have hbasis := hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using hle)
  have := hbasis.isAlgebraic_field
  rwa [Set.range_const] at this

/-- **Pull-back of `c (da₁ ∧ ⋯ ∧ da_d)^{⊗m}`** along a homomorphism `φ` of function fields of
varieties of the same dimension: it is `φ(c) (dφ(a₁) ∧ ⋯ ∧ dφ(a_d))^{⊗m}`. -/
private theorem pluriformPullback_smul_formPow_ιMulti {k : Type} [Field k] [CharZero k]
    {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] {sX : X ⟶ Spec (.of k)}
    {sX' : X' ⟶ Spec (.of k)} [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] {d : ℕ}
    (hX : topologicalKrullDim X = d) (hX' : topologicalKrullDim X' = d)
    (φ : FunctionFieldHom sX sX') (c : X'.functionField) (a : Fin d → X'.functionField)
    (hne : letI := functionFieldAlgebra sX'
      exteriorPower.ιMulti X'.functionField d
        (fun i => KaehlerDifferential.D k X'.functionField (a i)) ≠ 0) (m : ℕ) :
    letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
    pluriformPullback sX sX' φ d m (c • formPow (exteriorPower.ιMulti X'.functionField d
        (fun i => KaehlerDifferential.D k X'.functionField (a i))) m :
          PluriForms k X'.functionField d m) =
      (φ c • formPow (exteriorPower.ιMulti X.functionField d
        (fun i => KaehlerDifferential.D k X.functionField (φ (a i)))) m :
          PluriForms k X.functionField d m) := by
  letI := functionFieldAlgebra sX'
  letI := functionFieldAlgebra sX
  letI : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  set ω := exteriorPower.ιMulti X'.functionField d
    (fun i => KaehlerDifferential.D k X'.functionField (a i)) with hωdef
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX') hX'
  have hspan : Submodule.span X'.functionField {ω} = ⊤ := by
    have hωb : ω = b.repr ω () • b () := (basis_unit_repr_smul b ω).symm
    have hc : b.repr ω () ≠ 0 := by
      intro h
      apply hne
      rw [hωb, h, zero_smul]
    rw [hωb, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hc), eq_top_iff]
    intro w _
    rw [Submodule.mem_span_singleton]
    exact ⟨b.repr w (), basis_unit_repr_smul b w⟩
  have hgen := isPullbackGenerator_functionFieldHom hX hX' φ hspan hne
  rw [pluriformPullback_smul_formPow (sX := sX) (sX' := sX') φ hgen m c, topFormsMap_ιMulti]
  simp only [KaehlerDifferential.map_D]
  rfl

/-- **The floor coordinate has degree at most two.** If `x` has a simple pole along each
horizontal floor prime and no other horizontal pole, then `[k(Y) : k(V)(x)] ≤ 2`: for `j` large
the space `L(jD)`, of dimension `2j + 1` by Riemann–Roch, contains `x^a b_i` for any
`k(V)(x)`-independent `b_i` made integral over `k(V)[x]`. -/
private theorem finrank_adjoin_floorCoordinate_le_two {Y V : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V]
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [LocallyOfFiniteType sY]
    [LocallyOfFiniteType sV] {r : Y ⟶ V} [IsDominant r] (hrs : r ≫ sV = sY)
    (hdY : topologicalKrullDim Y = 3) (hdV : topologicalKrullDim V = 2)
    (h2 : ∀ E : Divisor Y, 0 ≤ E →
      letI := functionFieldMapAlgebra r
      FiniteDimensional V.functionField (horizontalSections r E) ∧
        (Module.finrank V.functionField (horizontalSections r E) : ℤ) =
          ∑ Q ∈ E.support, E Q * (MMP.Flips.genericFiberPointDegree r Q : ℤ) + 1)
    {B : QDivisor Y}
    (hdeg : open scoped Classical in
      ∑ Q ∈ B.support with B Q = 1 ∧ r Q.genericPoint = genericPoint V,
        MMP.Flips.genericFiberPointDegree r Q = 2)
    {x : Y.functionField}
    (hx : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      (B Q = 1 → Y.ord x Q.genericPoint = -1) ∧ (B Q ≠ 1 → 0 ≤ Y.ord x Q.genericPoint)) :
    letI := functionFieldMapAlgebra r
    FiniteDimensional (IntermediateField.adjoin V.functionField {x}) Y.functionField ∧
      Module.finrank (IntermediateField.adjoin V.functionField {x}) Y.functionField ≤ 2 := by
  classical
  letI := functionFieldMapAlgebra r
  set F₀ := IntermediateField.adjoin V.functionField {x} with hF₀def
  set H := B.support.filter (fun Q => B Q = 1 ∧ r Q.genericPoint = genericPoint V) with hHdef
  have hHne : H.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro hH
    rw [hH, Finset.sum_empty] at hdeg
    exact absurd hdeg (by norm_num)
  have hx0 : x ≠ 0 := by
    obtain ⟨Q, hQ⟩ := hHne
    obtain ⟨-, hB1, hQh⟩ := Finset.mem_filter.mp hQ
    have hord := (hx Q hQh).1 hB1
    rintro rfl
    rw [Scheme.ord_zero] at hord
    exact absurd hord (by norm_num)
  have hfl : ∀ Q ∈ H, Q.divisorialValuation x = WithZero.exp 1 ∧
      r Q.genericPoint = genericPoint V := by
    intro Q hQ
    obtain ⟨-, hB1, hQh⟩ := Finset.mem_filter.mp hQ
    refine ⟨?_, hQh⟩
    rw [Q.divisorialValuation_eq_exp_neg_ord hx0, (hx Q hQh).1 hB1]
    rfl
  have hnfl : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V → Q ∉ H →
      Q.divisorialValuation x ≤ 1 := by
    intro Q hQh hQH
    have hB : B Q ≠ 1 := fun h => hQH (Finset.mem_filter.mpr
      ⟨Finsupp.mem_support_iff.mpr (by rw [h]; norm_num), h, hQh⟩)
    have := (hx Q hQh).2 hB
    rw [Q.divisorialValuation_eq_exp_neg_ord hx0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  -- `x` is transcendental over `k(V)`
  have htr : Transcendental V.functionField x := by
    intro halg
    obtain ⟨Q, hQ⟩ := hHne
    obtain ⟨hvx, hQh⟩ := hfl Q hQ
    have hint := halg.isIntegral
    have hle := valuation_le_one_of_monic_eval Q.divisorialValuation
      ((minpoly.monic hint).map (algebraMap V.functionField Y.functionField))
      (fun i => by
        rw [Polynomial.coeff_map]
        exact divisorialValuation_functionFieldMap_le_one r Q hQh _)
      (by rw [Polynomial.eval_map_algebraMap, minpoly.aeval])
    rw [hvx] at hle
    exact absurd hle (not_le.mpr (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num))
  haveI halgL : Algebra.IsAlgebraic F₀ Y.functionField :=
    isAlgebraic_adjoin_of_transcendental hrs hdY hdV htr
  have key : ∀ y : Fin 3 → Y.functionField, ¬ LinearIndependent F₀ y := by
    intro y hyind
    have halg : ∀ i, IsAlgebraic F₀ (y i) := fun i => Algebra.IsAlgebraic.isAlgebraic (y i)
    choose q hq0 hqv using fun i => exists_aeval_mul_valuation_le_one r (halg i)
    have hqmem : ∀ f : Polynomial V.functionField, Polynomial.aeval x f ∈ F₀ := fun f =>
      IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ _)
    set z : Fin 3 → Y.functionField := fun i => Polynomial.aeval x (q i) * y i with hzdef
    have hzind : LinearIndependent F₀ z := by
      have h := hyind.units_smul (fun i => Units.mk0 (⟨Polynomial.aeval x (q i), hqmem _⟩ : F₀)
        (fun h => hq0 i (congrArg Subtype.val h)))
      convert h using 1
      funext i
      simp only [Pi.smul_apply', Units.smul_def, Units.val_mk0]
      rfl
    have hz0 : ∀ i, z i ≠ 0 := fun i => hzind.ne_zero i
    -- a bound for the poles of the `zᵢ` along the floor
    obtain ⟨c, hc⟩ : ∃ c : ℕ, ∀ i, ∀ Q ∈ H,
        Q.divisorialValuation (z i) ≤ WithZero.exp (c : ℤ) := by
      refine ⟨∑ i, ∑ Q ∈ H, (Y.ord (z i) Q.genericPoint).natAbs, fun i Q hQ => ?_⟩
      rw [Q.divisorialValuation_eq_exp_neg_ord (hz0 i), WithZero.exp_le_exp]
      have h1 : (Y.ord (z i) Q.genericPoint).natAbs ≤
          ∑ Q ∈ H, (Y.ord (z i) Q.genericPoint).natAbs :=
        Finset.single_le_sum (f := fun Q => (Y.ord (z i) Q.genericPoint).natAbs)
          (fun _ _ => Nat.zero_le _) hQ
      have h2 : ∑ Q ∈ H, (Y.ord (z i) Q.genericPoint).natAbs ≤
          ∑ i, ∑ Q ∈ H, (Y.ord (z i) Q.genericPoint).natAbs :=
        Finset.single_le_sum (f := fun i => ∑ Q ∈ H, (Y.ord (z i) Q.genericPoint).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    -- the floor divisor and its degree
    set w : MMP.Mori.PrimeDivisor Y → ℤ :=
      fun Q => (MMP.Flips.genericFiberPointDegree r Q : ℤ) with hwdef
    set degL : Divisor Y →ₗ[ℤ] ℤ := Finsupp.linearCombination ℤ w with hdegLdef
    have hdegL : ∀ E : Divisor Y, ∑ Q ∈ E.support, E Q * w Q = degL E := by
      intro E
      rw [hdegLdef, Finsupp.linearCombination_apply, Finsupp.sum]
      rfl
    set D : Divisor Y := ∑ Q ∈ H, Finsupp.single Q (1 : ℤ) with hDdef
    have hDQ : ∀ Q, D Q = if Q ∈ H then 1 else 0 := by
      intro Q
      rw [hDdef, Finsupp.finset_sum_apply]
      simp only [Finsupp.single_apply]
      rw [Finset.sum_ite_eq']
    have hdegD : degL D = 2 := by
      rw [hDdef, map_sum]
      simp only [hdegLdef, Finsupp.linearCombination_single, one_smul]
      simp only [hwdef]
      exact_mod_cast hdeg
    set N := 2 * c + 1 with hNdef
    set j := N + c with hjdef
    have hjD0 : 0 ≤ (j : ℤ) • D := by
      intro Q
      rw [Finsupp.smul_apply, smul_eq_mul, hDQ, Finsupp.coe_zero, Pi.zero_apply]
      split_ifs <;> positivity
    obtain ⟨hfin, hrk⟩ := h2 _ hjD0
    rw [hdegL, map_smul, hdegD, smul_eq_mul] at hrk
    -- the elements `x^a z_i` lie in `L(jD)`
    have hmem : ∀ (a : Fin (N + 1)) (i : Fin 3),
        x ^ (a : ℕ) * z i ∈ horizontalSections r ((j : ℤ) • D) := by
      intro a i
      rw [mem_horizontalSections]
      intro Q hQ
      rw [map_mul, map_pow, Finsupp.smul_apply, smul_eq_mul, hDQ]
      by_cases hQH : Q ∈ H
      · rw [if_pos hQH, mul_one, (hfl Q hQH).1, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_one]
        have ha : (a : ℕ) ≤ N := Nat.lt_succ_iff.mp a.2
        calc WithZero.exp ((a : ℕ) : ℤ) * Q.divisorialValuation (z i) ≤
              WithZero.exp ((a : ℕ) : ℤ) * WithZero.exp (c : ℤ) := mul_le_mul' le_rfl (hc i Q hQH)
          _ = WithZero.exp (((a : ℕ) : ℤ) + c) := (WithZero.exp_add _ _).symm
          _ ≤ WithZero.exp (j : ℤ) := WithZero.exp_le_exp.mpr (by omega)
      · rw [if_neg hQH, mul_zero, WithZero.exp_zero]
        have hxle := hnfl Q hQ hQH
        calc Q.divisorialValuation x ^ (a : ℕ) * Q.divisorialValuation (z i) ≤ 1 * 1 :=
              mul_le_mul' (pow_le_one' hxle _) (hqv i Q hQ hxle)
          _ = 1 := one_mul 1
    -- linear independence over `k(V)`
    let fam : Fin (N + 1) × Fin 3 → horizontalSections r ((j : ℤ) • D) :=
      fun ai => ⟨x ^ (ai.1 : ℕ) * z ai.2, hmem ai.1 ai.2⟩
    have hind : LinearIndependent V.functionField fam := by
      rw [Fintype.linearIndependent_iff]
      intro g hg ai
      have hg' : ∑ i : Fin 3, (Polynomial.aeval x (∑ a : Fin (N + 1),
          Polynomial.C (g (a, i)) * Polynomial.X ^ (a : ℕ))) * z i = 0 := by
        have h := congrArg Subtype.val hg
        simp only [Submodule.coe_sum, Submodule.coe_smul, Fintype.sum_prod_type, fam,
          Submodule.coe_zero] at h
        rw [Finset.sum_comm] at h
        rw [← h]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.smul_def, mul_assoc]
      have hcoef := Fintype.linearIndependent_iff.mp hzind (fun i => ⟨Polynomial.aeval x
        (∑ a : Fin (N + 1), Polynomial.C (g (a, i)) * Polynomial.X ^ (a : ℕ)), hqmem _⟩)
        (by
          rw [← hg']
          rfl)
      have hpoly : (∑ a : Fin (N + 1), Polynomial.C (g (a, ai.2)) * Polynomial.X ^ (a : ℕ) :
          Polynomial V.functionField) = 0 := by
        have h := congrArg Subtype.val (hcoef ai.2)
        by_contra hne
        exact htr ⟨_, hne, h⟩
      have h := congrArg (fun f => Polynomial.coeff f (ai.1 : ℕ)) hpoly
      simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_zero] at h
      rw [Finset.sum_eq_single ai.1 (fun b _ hb => if_neg (fun h' => hb (Fin.ext h'.symm)))
        (fun h' => absurd (Finset.mem_univ _) h'), if_pos rfl] at h
      exact h
    have hcard := hind.fintype_card_le_finrank
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
    have : ((N + 1) * 3 : ℕ) ≤ 2 * j + 1 := by
      have h' : ((Module.finrank V.functionField (horizontalSections r ((j : ℤ) • D)) : ℕ) : ℤ) =
          (j : ℤ) * 2 + 1 := hrk
      omega
    omega
  -- at most two `k(V)(x)`-independent elements
  have hrank : Module.rank F₀ Y.functionField ≤ 2 := by
    refine rank_le fun s hs => ?_
    by_contra hcard
    push Not at hcard
    set e := s.equivFin.symm
    refine key (fun i => (e (Fin.castLE hcard i) : Y.functionField)) ?_
    exact hs.comp _ (e.injective.comp (Fin.castLE_injective hcard))
  have hfin : FiniteDimensional F₀ Y.functionField :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank (by exact_mod_cast
      (Cardinal.natCast_lt_aleph0 : ((2 : ℕ) : Cardinal) < Cardinal.aleph0)))
  exact ⟨hfin, Module.finrank_le_of_rank_le hrank⟩

/-- **The logarithmic form is anti-invariant up to a constant under the deck involution.** Let
`x` be the floor coordinate, of degree at most two, `θ` a rational top form with horizontal
divisor minus the floor, and `λ = dt/t ∧ dξ₁ ∧ dξ₂` with `t = x⁻¹` and `ξᵢ ∈ k(V)`. If
`θ = G λ` then `G² ∈ k(V)(x)`: the involution `ι` of `k(Y)/k(V)(x)` fixes `λ` and the horizontal
divisor of `θ`, so `ι^*θ = μθ` with `μ ∈ k(V)` and `μ² = 1`. -/
private theorem sq_mem_adjoin_of_eq_smul {Y V : Scheme.{0}}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral V] {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [IsProper sY]
    [LocallyOfFiniteType sY] [LocallyOfFiniteType sV] {r : Y ⟶ V} [IsDominant r]
    (hrs : r ≫ sV = sY) (hrapp : ∀ U : V.Opens, IsIso (r.app U)) (hcl : IsClosedMap r)
    (hdY : topologicalKrullDim Y = 3) (hdV : topologicalKrullDim V = 2) {B : QDivisor Y}
    {x : Y.functionField}
    (hx : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      (B Q = 1 → Y.ord x Q.genericPoint = -1) ∧ (B Q ≠ 1 → 0 ≤ Y.ord x Q.genericPoint))
    (hdeg2 : letI := functionFieldMapAlgebra r
      FiniteDimensional (IntermediateField.adjoin V.functionField {x}) Y.functionField ∧
        Module.finrank (IntermediateField.adjoin V.functionField {x}) Y.functionField ≤ 2)
    {θ : letI := functionFieldAlgebra sY; ⋀[Y.functionField]^3 Ω[Y.functionField⁄k]}
    (hθ0 : θ ≠ 0)
    (hθ : letI := functionFieldAlgebra sY
      ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      Q.ordForm (sX := sY) (d := 3) (m := ((1 : ℕ) : ℤ)) (formPow θ 1) =
        if B Q = 1 then -1 else 0)
    (ξ : Fin 2 → V.functionField) {G : Y.functionField}
    (hG : letI := functionFieldAlgebra sY
      θ = G • (x • exteriorPower.ιMulti Y.functionField 3
        (Fin.cons (KaehlerDifferential.D k Y.functionField x⁻¹)
          fun i => KaehlerDifferential.D k Y.functionField (functionFieldMap r (ξ i))))) :
    letI := functionFieldMapAlgebra r
    G ^ 2 ∈ IntermediateField.adjoin V.functionField {x} := by
  classical
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra sV
  letI := functionFieldMapAlgebra r
  haveI : IsScalarTower k V.functionField Y.functionField := by
    subst hrs
    exact isScalarTower_functionFieldMap sV r
  set F₀ := IntermediateField.adjoin V.functionField {x} with hF₀def
  obtain ⟨hfin, hle2⟩ := hdeg2
  have hd3 : topologicalKrullDim Y = ((3 : ℕ) : WithBot ℕ∞) := by rw [hdY]; rfl
  have hxF₀ : x ∈ F₀ := IntermediateField.mem_adjoin_simple_self _ _
  set lam : ⋀[Y.functionField]^3 Ω[Y.functionField⁄k] := x • exteriorPower.ιMulti Y.functionField 3
    (Fin.cons (KaehlerDifferential.D k Y.functionField x⁻¹)
      fun i => KaehlerDifferential.D k Y.functionField (functionFieldMap r (ξ i))) with hlamdef
  have hG0 : G ≠ 0 := by
    rintro rfl
    exact hθ0 (by rw [hG, zero_smul])
  have hlam0 : lam ≠ 0 := by
    intro h
    exact hθ0 (by rw [hG, h, smul_zero])
  have hpos : 0 < Module.finrank F₀ Y.functionField := Module.finrank_pos
  -- the trivial case `k(Y) = k(V)(x)`
  by_cases h1 : Module.finrank F₀ Y.functionField = 1
  · have htop := Subalgebra.bot_eq_top_of_finrank_eq_one (F := F₀) (E := Y.functionField) h1
    have hmem : G ^ 2 ∈ (⊥ : Subalgebra F₀ Y.functionField) := by
      rw [htop]
      exact Algebra.mem_top
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp hmem
    rw [← hc]
    exact c.2
  have h2 : Module.finrank F₀ Y.functionField = 2 := by omega
  haveI : CharZero V.functionField :=
    charZero_of_injective_algebraMap (algebraMap k V.functionField).injective
  haveI : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap V.functionField F₀).injective
  obtain ⟨σ, hσ1, hσ2⟩ := exists_algEquiv_ne_one_of_finrank_eq_two h2
  have hσF₀ : ∀ c : F₀, σ (c : Y.functionField) = c := fun c => σ.commutes c
  have hσx : σ x = x := hσF₀ ⟨x, hxF₀⟩
  have hσV : ∀ c : V.functionField, σ (functionFieldMap r c) = functionFieldMap r c :=
    fun c => hσF₀ (algebraMap V.functionField F₀ c)
  have hσσ : ∀ g, σ (σ g) = g := fun g => by
    have := congrArg (fun τ : Y.functionField ≃ₐ[F₀] Y.functionField => τ g) hσ2
    exact this
  -- `σ` as a `k`-automorphism of `k(Y)`
  let ι : FunctionFieldEquiv sY sY := (σ.restrictScalars V.functionField).restrictScalars k
  have hι : ∀ g, ι g = σ g := fun g => rfl
  -- `σ` permutes the horizontal primes, preserving the floor
  have hperm : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      ∃ Q' : MMP.Mori.PrimeDivisor Y, r Q'.genericPoint = genericPoint V ∧
        (B Q' = 1 ↔ B Q = 1) ∧
        ∀ g, Y.ord (σ g) Q.genericPoint = Y.ord g Q'.genericPoint := by
    intro Q hQ
    set R := (Q.divisorialValuation.comap σ.toRingEquiv.toRingHom).valuationSubring
    have hmemR : ∀ g : Y.functionField, g ≠ 0 → (g ∈ R ↔ 0 ≤ Y.ord (σ g) Q.genericPoint) := by
      intro g hg
      rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply]
      change Q.divisorialValuation (σ g) ≤ 1 ↔ _
      rw [Q.divisorialValuation_eq_exp_neg_ord ((map_ne_zero σ).mpr hg), ← WithZero.exp_zero,
        WithZero.exp_le_exp]
      omega
    have hR : ∀ y : V.functionField, functionFieldMap r y ∈ R := by
      intro y
      rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply]
      change Q.divisorialValuation (σ (functionFieldMap r y)) ≤ 1
      rw [hσV]
      exact divisorialValuation_functionFieldMap_le_one r Q hQ y
    have hRtop : R ≠ ⊤ := by
      obtain ⟨π, hπ0, hπ⟩ := MMP.CyclicChartDifferent.Aux.exists_ord_eq Q (-1)
      intro htop
      have hmem : σ.symm π ∈ R := htop ▸ ValuationSubring.mem_top _
      rw [hmemR _ ((map_ne_zero _).mpr hπ0), AlgEquiv.apply_symm_apply, hπ] at hmem
      omega
    obtain ⟨Q', hQ'h, hQ'⟩ := exists_primeDivisor_of_valuationSubring r hrs hcl hdY hdV R hR hRtop
    have hord : ∀ g, Y.ord (σ g) Q.genericPoint = Y.ord g Q'.genericPoint :=
      ord_eq_of_forall_nonneg_iff Q Q' σ.toRingEquiv fun g hg => by
        rw [← hQ' g hg, hmemR g hg]
        rfl
    refine ⟨Q', hQ'h, ?_, hord⟩
    have hxQ' : Y.ord x Q'.genericPoint = Y.ord x Q.genericPoint := by
      rw [← hord, hσx]
    constructor
    · intro hB'
      by_contra hB
      have := (hx Q hQ).2 hB
      have := (hx Q' hQ'h).1 hB'
      omega
    · intro hB
      by_contra hB'
      have := (hx Q' hQ'h).2 hB'
      have := (hx Q hQ).1 hB
      omega
  -- the pull-back of `θ = (G x) (dt ∧ dξ)`, `t = x⁻¹`
  set a : Fin 3 → Y.functionField := Fin.cons x⁻¹ fun i => functionFieldMap r (ξ i) with hadef
  set ω₀ := exteriorPower.ιMulti Y.functionField 3
    (fun i => KaehlerDifferential.D k Y.functionField (a i)) with hω₀def
  have hlamω : lam = x • ω₀ := by
    rw [hlamdef, hω₀def]
    congr 2
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [hadef]
  have hω₀0 : ω₀ ≠ 0 := fun h => hlam0 (by rw [hlamω, h, smul_zero])
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hlam0 (by rw [hlamω, zero_smul])
  have hθω : (formPow θ 1 : PluriForms k Y.functionField 3 ((1 : ℕ) : ℤ)) =
      (G * x) • formPow ω₀ 1 := by
    rw [hG, hlamω, smul_smul, formPow_smul, pow_one]
  have hσa : ∀ i, σ (a i) = a i := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [hadef, Fin.cons_zero, map_inv₀, hσx]
    · simp only [hadef, Fin.cons_succ, hσV]
  have hpb : pluriformPullback sY sY ι.toHom 3 ((1 : ℕ) : ℤ)
      (formPow θ 1 : PluriForms k Y.functionField 3 ((1 : ℕ) : ℤ)) =
      (σ (G * x) • formPow ω₀ 1 : PluriForms k Y.functionField 3 ((1 : ℕ) : ℤ)) := by
    rw [hθω, pluriformPullback_smul_formPow_ιMulti hd3 hd3 ι.toHom (G * x) a hω₀0 1]
    have hfun : (fun i => KaehlerDifferential.D k Y.functionField
        (FunctionFieldEquiv.toHom sY sY ι (a i))) =
        fun i => KaehlerDifferential.D k Y.functionField (a i) := by
      funext i
      change KaehlerDifferential.D k Y.functionField (σ (a i)) = _
      rw [hσa]
    rw [hfun]
    rfl
  -- `ι(G)` and `G` have the same horizontal orders
  have hordG : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      Y.ord (σ G) Q.genericPoint = Y.ord G Q.genericPoint := by
    intro Q hQ
    obtain ⟨Q', hQ'h, hBB, hord⟩ := hperm Q hQ
    have e1 := ordForm_pluriformPullback_of_ord_eq (k := k) (m := ((1 : ℕ) : ℤ)) hd3 hd3 ι Q Q'
      (fun g => by rw [hι]; exact hord g) (formPow θ 1)
    rw [hpb, hθ Q' hQ'h] at e1
    have e2 := hθ Q hQ
    rw [hθω] at e2
    have hGx : G * x ≠ 0 := mul_ne_zero hG0 hx0
    rw [ordForm_smul_formPow (sX := sY) Q hd3 hω₀0 ((map_ne_zero σ).mpr hGx) 1] at e1
    rw [ordForm_smul_formPow (sX := sY) Q hd3 hω₀0 hGx 1] at e2
    have hif : (if B Q' = 1 then (-1 : ℤ) else 0) = if B Q = 1 then -1 else 0 := by
      by_cases h : B Q = 1
      · rw [if_pos h, if_pos (hBB.mpr h)]
      · rw [if_neg h, if_neg (fun h' => h (hBB.mp h'))]
    rw [hif] at e1
    rw [map_mul, hσx, Scheme.ord_mul ((map_ne_zero σ).mpr hG0) hx0] at e1
    rw [Scheme.ord_mul hG0 hx0] at e2
    omega
  -- `ι(G) = μ G` with `μ ∈ k(V)`
  set μ := σ G / G with hμdef
  have hμ0 : μ ≠ 0 := div_ne_zero ((map_ne_zero σ).mpr hG0) hG0
  have hμord : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      0 ≤ Y.ord μ Q.genericPoint := by
    intro Q hQ
    rw [hμdef, div_eq_mul_inv, Scheme.ord_mul ((map_ne_zero σ).mpr hG0) (inv_ne_zero hG0),
      ← zpow_neg_one, MMP.Mori.ord_zpow _ hG0, hordG Q hQ]
    omega
  obtain ⟨c, hc⟩ := exists_functionFieldMap_eq_of_forall_ord_nonneg r hrapp hcl μ hμord
  have hσμ : σ μ = μ := by rw [← hc, hσV]
  have hσG : σ G = μ * G := by rw [hμdef, div_mul_cancel₀ _ hG0]
  have hμ2 : μ * μ = 1 := by
    have h := hσσ G
    rw [hσG, map_mul, hσμ, hσG, ← mul_assoc] at h
    exact mul_right_cancel₀ hG0 (h.trans (one_mul G).symm)
  have hσG2 : σ (G ^ 2) = G ^ 2 := by
    rw [map_pow, hσG, mul_pow, sq μ, hμ2, one_mul]
  -- `G²` is fixed by the Galois group of order two
  haveI : Algebra.IsQuadraticExtension F₀ Y.functionField := ⟨h2⟩
  haveI : IsGalois F₀ Y.functionField := inferInstance
  have hcard : Nat.card (Y.functionField ≃ₐ[F₀] Y.functionField) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, h2]
  haveI : Fintype (Y.functionField ≃ₐ[F₀] Y.functionField) := Fintype.ofFinite _
  have hall : ∀ τ : Y.functionField ≃ₐ[F₀] Y.functionField, τ (G ^ 2) = G ^ 2 := by
    intro τ
    by_cases hτ1 : τ = 1
    · rw [hτ1]
      rfl
    by_cases hτσ : τ = σ
    · rw [hτσ, hσG2]
    exfalso
    have h3 : ({1, σ, τ} : Finset (Y.functionField ≃ₐ[F₀] Y.functionField)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hτσ)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hσ1, Ne.symm hτ1⟩
    have h4 := Finset.card_le_univ ({1, σ, τ} : Finset (Y.functionField ≃ₐ[F₀] Y.functionField))
    rw [h3, ← Nat.card_eq_fintype_card, hcard] at h4
    omega
  obtain ⟨c', hc'⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := F₀) (G ^ 2)).mpr hall
  rw [← hc']
  exact c'.2

/-- Nonzero rational functions on `V` are units along the prime divisors of `Y` dominating `V`. -/
private theorem divisorialValuation_functionFieldMap_eq_one {Y V : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V] (r : Y ⟶ V) [IsDominant r]
    (Q : MMP.Mori.PrimeDivisor Y) (hQ : r Q.genericPoint = genericPoint V) {c : V.functionField}
    (hc : c ≠ 0) : Q.divisorialValuation (functionFieldMap r c) = 1 := by
  have h1 := divisorialValuation_functionFieldMap_le_one r Q hQ c
  have h2 := divisorialValuation_functionFieldMap_le_one r Q hQ c⁻¹
  have h3 : Q.divisorialValuation (functionFieldMap r c) *
      Q.divisorialValuation (functionFieldMap r c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  refine le_antisymm h1 (not_lt.mp fun hlt => ?_)
  have := mul_lt_one_of_lt_of_le hlt h2
  rw [h3] at this
  exact lt_irrefl _ this

/-- Along a prime divisor where `v(x) = exp 1`, a polynomial in `x` over `k(V)` has valuation at
most `exp (deg f)`. -/
private theorem divisorialValuation_aeval_le {Y V : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V] (r : Y ⟶ V) [IsDominant r]
    (Q : MMP.Mori.PrimeDivisor Y) (hQ : r Q.genericPoint = genericPoint V) {x : Y.functionField}
    (hx : Q.divisorialValuation x = WithZero.exp 1) (f : Polynomial V.functionField) :
    letI := functionFieldMapAlgebra r
    Q.divisorialValuation (Polynomial.aeval x f) ≤ WithZero.exp (f.natDegree : ℤ) := by
  letI := functionFieldMapAlgebra r
  rw [Polynomial.aeval_eq_sum_range]
  refine Valuation.map_sum_le _ fun i hi => ?_
  rw [Algebra.smul_def, map_mul, map_pow, hx]
  have hi' : (i : ℤ) ≤ f.natDegree := by
    have := Finset.mem_range.mp hi
    omega
  calc Q.divisorialValuation (algebraMap V.functionField Y.functionField (f.coeff i)) *
        WithZero.exp 1 ^ i ≤ 1 * WithZero.exp (i : ℤ) := by
        refine mul_le_mul' (divisorialValuation_functionFieldMap_le_one r Q hQ _) ?_
        rw [← WithZero.exp_nsmul, nsmul_eq_mul, mul_one]
    _ ≤ WithZero.exp (f.natDegree : ℤ) := by
        rw [one_mul]
        exact WithZero.exp_le_exp.mpr hi'

/-- Along a prime divisor where `v(x) = exp 1`, a nonzero polynomial in `x` over `k(V)` has
valuation exactly `exp (deg f)`: its leading term dominates. -/
private theorem divisorialValuation_aeval_eq {Y V : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V] (r : Y ⟶ V) [IsDominant r]
    (Q : MMP.Mori.PrimeDivisor Y) (hQ : r Q.genericPoint = genericPoint V) {x : Y.functionField}
    (hx : Q.divisorialValuation x = WithZero.exp 1) {f : Polynomial V.functionField} (hf : f ≠ 0) :
    letI := functionFieldMapAlgebra r
    Q.divisorialValuation (Polynomial.aeval x f) = WithZero.exp (f.natDegree : ℤ) := by
  letI := functionFieldMapAlgebra r
  have hlead : Q.divisorialValuation (Polynomial.aeval x
      (Polynomial.C f.leadingCoeff * Polynomial.X ^ f.natDegree)) =
      WithZero.exp (f.natDegree : ℤ) := by
    rw [map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_mul, map_pow, hx]
    change Q.divisorialValuation (functionFieldMap r f.leadingCoeff) * _ = _
    rw [divisorialValuation_functionFieldMap_eq_one r Q hQ
      (Polynomial.leadingCoeff_ne_zero.mpr hf), one_mul, ← WithZero.exp_nsmul, nsmul_eq_mul,
      mul_one]
  conv_lhs => rw [← Polynomial.eraseLead_add_C_mul_X_pow f]
  rw [map_add]
  rcases f.eraseLead_natDegree_lt_or_eraseLead_eq_zero with h | h
  · rw [Valuation.map_add_eq_of_lt_right _ (lt_of_le_of_lt
      (divisorialValuation_aeval_le r Q hQ hx _) ?_), hlead]
    rw [hlead]
    exact WithZero.exp_lt_exp.mpr (by exact_mod_cast h)
  · rw [h, map_zero, zero_add, hlead]

/-- **Elements of `k(V)(x)` have constant reductions along the floor.** If `y ∈ k(V)(x)`, there is
`c ∈ k(V)` such that `y - c` vanishes along every horizontal prime where `x` has a simple pole and
`y` is a unit: `y = p(x)/q(x)` with `deg p = deg q` there, and `c = lc(p)/lc(q)`. -/
private theorem exists_sub_mem_maximalIdeal_of_mem_adjoin {Y V : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V] {r : Y ⟶ V}
    [IsDominant r] {x y : Y.functionField}
    (hy : letI := functionFieldMapAlgebra r; y ∈ IntermediateField.adjoin V.functionField {x})
    (hy0 : y ≠ 0) :
    ∃ c : V.functionField, c ≠ 0 ∧ ∀ Q : MMP.Mori.PrimeDivisor Y,
      r Q.genericPoint = genericPoint V → Y.ord x Q.genericPoint = -1 →
        Y.ord y Q.genericPoint = 0 →
        Q.divisorialValuation (y - functionFieldMap r c) < 1 := by
  classical
  letI := functionFieldMapAlgebra r
  obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff _ _).mp hy
  have hqa : Polynomial.aeval x q ≠ 0 := by
    intro h
    rw [h, div_zero] at hpq
    exact hy0 hpq
  have hpa : Polynomial.aeval x p ≠ 0 := by
    intro h
    rw [h, zero_div] at hpq
    exact hy0 hpq
  have hp : p ≠ 0 := by
    rintro rfl
    exact hpa (map_zero _)
  have hq : q ≠ 0 := by
    rintro rfl
    exact hqa (map_zero _)
  refine ⟨p.leadingCoeff / q.leadingCoeff, div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp)
    (Polynomial.leadingCoeff_ne_zero.mpr hq), fun Q hQ hxQ hyQ => ?_⟩
  set c := p.leadingCoeff / q.leadingCoeff with hcdef
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Scheme.ord_zero] at hxQ
    exact absurd hxQ (by norm_num)
  have hvx : Q.divisorialValuation x = WithZero.exp 1 := by
    rw [Q.divisorialValuation_eq_exp_neg_ord hx0, hxQ]
    rfl
  have hvy : Q.divisorialValuation y = 1 := by
    rw [Q.divisorialValuation_eq_exp_neg_ord hy0, hyQ]
    rfl
  have hvp := divisorialValuation_aeval_eq r Q hQ hvx hp
  have hvq := divisorialValuation_aeval_eq r Q hQ hvx hq
  have hdeg : p.natDegree = q.natDegree := by
    rw [hpq, map_div₀, hvp, hvq, ← WithZero.exp_sub] at hvy
    have := WithZero.exp_injective (hvy.trans WithZero.exp_zero.symm)
    omega
  have hsub : y - functionFieldMap r c =
      Polynomial.aeval x (p - Polynomial.C c * q) / Polynomial.aeval x q := by
    rw [hpq, map_sub, map_mul, Polynomial.aeval_C]
    change _ - functionFieldMap r c = (_ - functionFieldMap r c * _) / _
    field_simp
  rw [hsub]
  by_cases h0 : p - Polynomial.C c * q = 0
  · rw [h0, map_zero, zero_div, map_zero]
    exact zero_lt_one
  have hdeglt : (p - Polynomial.C c * q).natDegree < p.natDegree := by
    refine Polynomial.natDegree_lt_natDegree h0 (Polynomial.degree_sub_lt ?_ hp ?_)
    · rw [Polynomial.degree_C_mul (div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp)
        (Polynomial.leadingCoeff_ne_zero.mpr hq)), Polynomial.degree_eq_natDegree hp,
        Polynomial.degree_eq_natDegree hq, hdeg]
    · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hcdef,
        div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hq)]
  rw [map_div₀, hvq]
  calc Q.divisorialValuation (Polynomial.aeval x (p - Polynomial.C c * q)) /
        WithZero.exp (q.natDegree : ℤ) ≤
        WithZero.exp ((p - Polynomial.C c * q).natDegree : ℤ) / WithZero.exp (q.natDegree : ℤ) :=
        by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul' (divisorialValuation_aeval_le r Q hQ hvx _) le_rfl
    _ < 1 := by
        rw [← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_lt_exp]
        omega

/-- A surface over `k` has two rational functions `ξ₁, ξ₂` with `dξ₁ ∧ dξ₂ ≠ 0`. -/
private theorem exists_ιMulti_D_ne_zero {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V]
    {sV : V ⟶ Spec (.of k)} [LocallyOfFiniteType sV] (hdV : topologicalKrullDim V = 2) :
    letI := functionFieldAlgebra sV
    ∃ ξ : Fin 2 → V.functionField,
      exteriorPower.ιMulti V.functionField 2
        (fun i => KaehlerDifferential.D k V.functionField (ξ i)) ≠ 0 := by
  letI := functionFieldAlgebra sV
  obtain ⟨b⟩ := exists_basis_topForms (sX := sV) (d := 2) (by rw [hdV]; rfl)
  by_contra h
  push Not at h
  have hspan := exteriorPower.ιMulti_span_of_span (R := V.functionField)
    (M := Ω[V.functionField⁄k]) (n := 2)
    (KaehlerDifferential.span_range_derivation k V.functionField)
  have htop : (⊤ : Submodule V.functionField (⋀[V.functionField]^2 Ω[V.functionField⁄k])) = ⊥ := by
    rw [← hspan, Submodule.span_eq_bot]
    rintro _ ⟨a, ha, rfl⟩
    choose ξ hξ using fun i => ha ⟨i, rfl⟩
    have ha' : a = fun i => KaehlerDifferential.D k V.functionField (ξ i) :=
      funext fun i => (hξ i).symm
    rw [ha']
    exact h ξ
  have hb : b () ∈ (⊤ : Submodule V.functionField (⋀[V.functionField]^2 Ω[V.functionField⁄k])) :=
    Submodule.mem_top
  rw [htop, Submodule.mem_bot] at hb
  exact b.ne_zero () hb

/-- **An `m`-canonical form with divisor `-mB` along the horizontal primes is a constant multiple
of `θ^{⊗m}`.** If `θ` has horizontal divisor minus the floor of `B ≥ 0` and `ord_Q α = -m B_Q`
along every horizontal prime, then `α = c · θ^{⊗m}` with `c ∈ k(V)^*`: the ratio has no
horizontal pole, so comes from `k(V)`. -/
private theorem exists_eq_functionFieldMap_smul_formPow {Y V : Scheme.{0}}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V]
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] {r : Y ⟶ V} [IsDominant r]
    (hrapp : ∀ U : V.Opens, IsIso (r.app U)) (hcl : IsClosedMap r)
    (hdY : topologicalKrullDim Y = 3) {B : QDivisor Y}
    (hB0 : ∀ Q, 0 ≤ B Q)
    {θ : letI := functionFieldAlgebra sY; ⋀[Y.functionField]^3 Ω[Y.functionField⁄k]}
    (hθ0 : θ ≠ 0)
    (hθ : letI := functionFieldAlgebra sY
      ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      Q.ordForm (sX := sY) (d := 3) (m := ((1 : ℕ) : ℤ)) (formPow θ 1) =
        if B Q = 1 then -1 else 0)
    {m : ℕ} {α : RationalPluriForms sY 3 m} (hα0 : α ≠ 0)
    (hα : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      (Q.ordForm α : ℚ) = -(m : ℚ) * B Q) :
    letI := functionFieldAlgebra sY
    ∃ c : V.functionField, c ≠ 0 ∧
      α = (functionFieldMap r c • formPow θ m : PluriForms k Y.functionField 3 m) := by
  letI := functionFieldAlgebra sY
  have hd3 : topologicalKrullDim Y = ((3 : ℕ) : WithBot ℕ∞) := by rw [hdY]; rfl
  obtain ⟨b⟩ := exists_basis_topForms (sX := sY) (d := 3) hd3
  set cθ := b.repr θ ()
  have hθb : θ = cθ • b () := (basis_unit_repr_smul b θ).symm
  have hcθ : cθ ≠ 0 := fun h => hθ0 (by rw [hθb, h, zero_smul])
  set F : Y.functionField := (ZTensorPower.basis b m).repr α () / cθ ^ m
  have hαF : α = (F • formPow θ m : PluriForms k Y.functionField 3 m) := by
    rw [hθb, formPow_smul, smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ hcθ)]
    exact eq_repr_smul_formPow b α
  have hF0 : F ≠ 0 := by
    rintro h
    apply hα0
    rw [hαF, h]
    exact zero_smul _ _
  have hord : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      0 ≤ Y.ord F⁻¹ Q.genericPoint := by
    intro Q hQ
    have e := ordForm_smul_formPow (sX := sY) Q hd3 hθ0 hF0 m
    rw [← hαF] at e
    have h1 := hα Q hQ
    have h2 := hθ Q hQ
    rw [← zpow_neg_one, MMP.Mori.ord_zpow _ hF0]
    have hBQ := hB0 Q
    split_ifs at h2 with hB
    · rw [h2] at e
      rw [hB] at h1
      have : (Y.ord F Q.genericPoint : ℚ) = 0 := by
        have e' : (Q.ordForm α : ℚ) = (Y.ord F Q.genericPoint : ℚ) + (m : ℚ) * (-1) := by
          exact_mod_cast e
        linarith
      have : Y.ord F Q.genericPoint = 0 := by exact_mod_cast this
      omega
    · rw [h2, mul_zero, add_zero] at e
      have : (Y.ord F Q.genericPoint : ℚ) ≤ 0 := by
        rw [← e, h1]
        have : (0 : ℚ) ≤ (m : ℚ) * B Q := mul_nonneg (by positivity) hBQ
        linarith
      have : Y.ord F Q.genericPoint ≤ 0 := by exact_mod_cast this
      omega
  obtain ⟨c', hc'⟩ := exists_functionFieldMap_eq_of_forall_ord_nonneg r hrapp hcl F⁻¹ hord
  refine ⟨c'⁻¹, ?_, ?_⟩
  · intro h
    rw [inv_eq_zero.mp h, map_zero] at hc'
    exact inv_ne_zero hF0 hc'.symm
  · rw [map_inv₀, hc', inv_inv]
    exact hαF

/-- **Restriction kills the maximal ideal.** Along an adjunction step `j : S ⟶ U`, an element of
`𝒪_{U,S}` vanishing to order at least one along `S` restricts to zero in `k(S)`. -/
private theorem stalkMap_eq_zero_of_one_le_ord {U S : Scheme.{0}} [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] [IsIntegral S] {sU : U ⟶ Spec (.of k)}
    [LocallyOfFiniteType sU] {Δ : QDivisor U} {j : S ⟶ U} {BS : QDivisor S}
    (hS : IsAdjunctionStep sU Δ j BS) {t₀ : U.presheaf.stalk (j (genericPoint S))}
    (ht₀ : U.ord (algebraMap _ U.functionField t₀) (j (genericPoint S)) = 1)
    (s : U.presheaf.stalk (j (genericPoint S)))
    (hs : algebraMap _ U.functionField s ≠ 0 →
      1 ≤ U.ord (algebraMap _ U.functionField s) (j (genericPoint S))) :
    (j.stalkMap (genericPoint S)).hom s = 0 := by
  obtain ⟨P, hP, -⟩ := hS.exists_primeDivisor
  have hco : Order.coheight (j (genericPoint S)) = 1 :=
    hP ▸ AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  obtain ⟨ϖ, -, hϖ0, -, -, -, hunit⟩ := hS.exists_uniformizer
  obtain ⟨u, -, hu⟩ := hunit t₀ ht₀
  have hinj : Function.Injective
      (algebraMap (U.presheaf.stalk (j (genericPoint S))) U.functionField) :=
    IsFractionRing.injective _ _
  have ht0 : algebraMap _ U.functionField t₀ ≠ 0 := by
    intro h
    rw [h, Scheme.ord_zero] at ht₀
    exact zero_ne_one ht₀
  by_cases hs0 : algebraMap _ U.functionField s = 0
  · rw [show s = 0 from hinj (hs0.trans (map_zero _).symm), map_zero]
  have hq0 : algebraMap _ U.functionField s * (algebraMap _ U.functionField t₀)⁻¹ ≠ 0 :=
    mul_ne_zero hs0 (inv_ne_zero ht0)
  obtain ⟨s', hs'⟩ := (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hco hq0).mpr (by
    rw [Scheme.ord_mul hs0 (inv_ne_zero ht0), ← zpow_neg_one, MMP.Mori.ord_zpow _ ht0, ht₀]
    have := hs hs0
    omega)
  have hss : s = s' * t₀ := hinj (by
    rw [map_mul, hs', mul_assoc, inv_mul_cancel₀ ht0, mul_one])
  have hϖ : (j.stalkMap (genericPoint S)).hom ϖ = 0 := hϖ0
  rw [hss, hu, map_mul, map_mul, hϖ, mul_zero, mul_zero]

/-- **Horizontal branches are proper normal surfaces.** A branch `j : S ⟶ U` of an adjunction
step on a crepant dlt lift `U` of the projective threefold `Y` is a proper normal variety of
dimension two. -/
private theorem isNormalVariety_of_isAdjunctionStep {Y U S : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral U] [IsLocallyNoetherian U]
    [IsNormal U] [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    {sY : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsProjectiveVariety k sY) {K : Divisor Y}
    {B : QDivisor Y} {p : U ⟶ Y} [IsDominant p] {Δ : QDivisor U}
    (hlift : IsCrepantDltModel sY K B p Δ) (hdU : topologicalKrullDim U = 3) {j : S ⟶ U}
    {BS : QDivisor S} (hS : IsAdjunctionStep (p ≫ sY) Δ j BS) :
    IsNormalVariety k (j ≫ p ≫ sY) ∧ IsProper (j ≫ p ≫ sY) ∧ CompactSpace S ∧
      topologicalKrullDim S = 2 := by
  have hUv : IsNormalVariety k (p ≫ sY) := hlift.isNormalVariety
  haveI : LocallyOfFiniteType (p ≫ sY) := hUv.1.toLocallyOfFiniteType
  have hv : IsNormalVariety k (j ≫ p ≫ sY) := hS.1
  obtain ⟨P, hP, hci⟩ := hS.exists_primeDivisor
  haveI := hci
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hlift.isProjectiveMorphism
  haveI : IsProper sY :=
    isProper_of_isProjectiveMorphism sY ((MMP.Mori.isProjectiveVariety_iff k sY).1 hY).2
  haveI hpr : IsProper (j ≫ p ≫ sY) := inferInstance
  refine ⟨hv, hpr, QuasiCompact.compactSpace_of_compactSpace (j ≫ p ≫ sY), ?_⟩
  haveI : LocallyOfFiniteType (j ≫ p ≫ sY) := hv.1.toLocallyOfFiniteType
  have h1 := trdeg_add_one_of_eq_genericPoint (sY := p ≫ sY) (j := j) P hP
  have h2 := topologicalKrullDim_eq_toNat_trdeg (p ≫ sY)
  rw [hdU] at h2
  have h3 : (letI := functionFieldAlgebra (p ≫ sY);
      (Algebra.trdeg k U.functionField).toNat) = 3 := by exact_mod_cast h2.symm
  rw [topologicalKrullDim_eq_toNat_trdeg (j ≫ p ≫ sY)]
  have h4 : (letI := functionFieldAlgebra (j ≫ p ≫ sY);
      (Algebra.trdeg k S.functionField).toNat) = 2 := by omega
  rw [h4]
  rfl

/-- A nonzero vector of a one-dimensional vector space has nonzero coordinate. -/
private theorem repr_unit_ne_zero {K L : Type*} [Semiring K] [AddCommMonoid L] [Module K L]
    (b : Module.Basis Unit K L) {x : L} (hx : x ≠ 0) : b.repr x () ≠ 0 := fun h0 =>
  hx (by rw [← basis_unit_repr_smul b x, h0]; exact zero_smul _ _)

/-- The zero form has the residue zero along `j : T ⟶ Y`, given a uniformizer at the generic
point of the image of `j`. -/
private theorem isPoincareResidue_zero_zero {k : Type} [Field k] {Y T : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsIntegral T] (j : T ⟶ Y)
    {n m : ℕ} {t : Y.presheaf.stalk (j (genericPoint T))}
    (ht : Y.ord (algebraMap _ Y.functionField t) (j (genericPoint T)) = 1)
    (x : Fin n → Y.presheaf.stalk (j (genericPoint T))) :
    IsPoincareResidue sY j n m 0 0 :=
  ⟨t, 0, x, ht, by rw [map_zero]; exact (zero_smul _ _).symm,
    by rw [map_zero]; exact (zero_smul _ _).symm⟩

/-- In a one-dimensional vector space with basis `b`, every vector is a multiple of a vector `σ`
with nonzero coordinate, the factor being the quotient of the coordinates. -/
private theorem eq_repr_div_smul {K L : Type*} [DivisionRing K] [AddCommMonoid L] [Module K L]
    (b : Module.Basis Unit K L) {σ : L} (hσ : b.repr σ () ≠ 0) (x : L) :
    x = (b.repr x () / b.repr σ ()) • σ := by
  calc x = b.repr x () • b () := (basis_unit_repr_smul b x).symm
    _ = (b.repr x () / b.repr σ ()) • (b.repr σ () • b ()) := by
      rw [smul_smul, div_mul_cancel₀ _ hσ]
    _ = _ := by rw [basis_unit_repr_smul b σ]

/-- **The residue of `c₁ θ^{⊗m}` along a horizontal floor branch of a crepant dlt lift.** Let
`θ = G (dt/t ∧ dξ)` with `t = x⁻¹`, where `x` is the floor coordinate, `θ` has horizontal
divisor minus the floor, and `G² ≡ c₀` modulo every floor prime along which `G` is a unit. For a
crepant dlt lift `p : (U, Δ) ⟶ (Y, B)` and a horizontal floor branch `j : S ⟶ U`, the Poincaré
residue of `p^*(c₁ θ^{⊗m})`, `m` even, is the pull-back of `c₁ c₀^{m/2} (dξ₁ ∧ dξ₂)^{⊗m}`. Along
the branch `G` is a unit: the form `dt/t ∧ dξ` has the nonzero residue `dξ̄`, so its order is
`-1` by uniqueness of residues, and so is that of `θ`. The branch alone already forces
`dt/t ∧ dξ ≠ 0`, the residue `dξ̄` of that form being nonzero. -/
private theorem isPoincareResidue_floor_of_eq_smul {Y V : Scheme.{0}}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [QuasiCompact sY] {r : Y ⟶ V}
    [IsDominant r] (hr : IsContraction sY sV r)
    (hY : MMP.Mori.IsProjectiveVariety k sY) (hV : MMP.Mori.IsProjectiveVariety k sV)
    (hdY : topologicalKrullDim Y = 3) (hdV : topologicalKrullDim V = 2)
    {K : Divisor Y} {B : QDivisor Y} {x : Y.functionField}
    (hx : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      (B Q = 1 → Y.ord x Q.genericPoint = -1) ∧ (B Q ≠ 1 → 0 ≤ Y.ord x Q.genericPoint))
    (ξ : Fin 2 → V.functionField)
    (hξ : letI := functionFieldAlgebra sV
      exteriorPower.ιMulti V.functionField 2
        (fun i => KaehlerDifferential.D k V.functionField (ξ i)) ≠ 0)
    (U : Scheme.{0}) [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    (p : U ⟶ Y) [IsDominant p] (Δ : QDivisor U) (hlift : IsCrepantDltModel sY K B p Δ)
    (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (j : S ⟶ U) (BS : QDivisor S) [IsDominant (j ≫ p ≫ r)]
    (hS : IsAdjunctionStep (p ≫ sY) Δ j BS)
    (ψ : FunctionFieldHom (p ≫ sY) sY) (φ : FunctionFieldHom (j ≫ p ≫ sY) sV)
    (hψ : ∀ x, ψ x = functionFieldMap p x) (hφ : ∀ x, φ x = functionFieldMap (j ≫ p ≫ r) x) :
    letI := functionFieldAlgebra sY
    letI := functionFieldAlgebra sV
    exteriorPower.ιMulti Y.functionField 3
        (Fin.cons (KaehlerDifferential.D k Y.functionField x⁻¹)
          fun i => KaehlerDifferential.D k Y.functionField (functionFieldMap r (ξ i))) ≠ 0 ∧
    ∀ {θ : ⋀[Y.functionField]^3 Ω[Y.functionField⁄k]},
      (∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
        Q.ordForm (sX := sY) (d := 3) (m := ((1 : ℕ) : ℤ)) (formPow θ 1) =
          if B Q = 1 then -1 else 0) →
      θ ≠ 0 → ∀ {G : Y.functionField},
      θ = G • (x • exteriorPower.ιMulti Y.functionField 3
        (Fin.cons (KaehlerDifferential.D k Y.functionField x⁻¹)
          fun i => KaehlerDifferential.D k Y.functionField (functionFieldMap r (ξ i)))) →
      ∀ {c₀ : V.functionField},
      (∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
        Y.ord x Q.genericPoint = -1 → Y.ord (G ^ 2) Q.genericPoint = 0 →
          Q.divisorialValuation (G ^ 2 - functionFieldMap r c₀) < 1) →
      ∀ (c₁ : V.functionField) {m : ℕ}, 0 < m → Even m →
      IsPoincareResidue (p ≫ sY) j 2 m
        (pluriformPullback (p ≫ sY) sY ψ 3 m
          (functionFieldMap r c₁ • formPow θ m : PluriForms k Y.functionField 3 m))
        (pluriformPullback (j ≫ p ≫ sY) sV φ 2 m
          ((c₁ * c₀ ^ (m / 2)) • formPow (exteriorPower.ιMulti V.functionField 2
            (fun i => KaehlerDifferential.D k V.functionField (ξ i))) m :
            PluriForms k V.functionField 2 m)) := by
  classical
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra sV
  letI := functionFieldAlgebra (p ≫ sY)
  letI := functionFieldAlgebra (j ≫ p ≫ sY)
  haveI : LocallyOfFiniteType sY :=
    ((MMP.Mori.isProjectiveVariety_iff k sY).1 hY).1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sV :=
    ((MMP.Mori.isProjectiveVariety_iff k sV).1 hV).1.toLocallyOfFiniteType
  haveI : IsProper sY :=
    isProper_of_isProjectiveMorphism sY ((MMP.Mori.isProjectiveVariety_iff k sY).1 hY).2
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.isProjectiveMorphism
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hlift.isProjectiveMorphism
  haveI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (p ≫ sY)
  have hUv : IsNormalVariety k (p ≫ sY) := hlift.isNormalVariety
  haveI : LocallyOfFiniteType (p ≫ sY) := hUv.1.toLocallyOfFiniteType
  have hdU : topologicalKrullDim U = 3 := by
    haveI := ((MMP.Mori.isProjectiveVariety_iff k sY).1 hY).1
    haveI := hUv.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (p ≫ sY)
      hlift.isBirationalMorphism, hdY]
  obtain ⟨hSv, -, hSc, hdS⟩ := isNormalVariety_of_isAdjunctionStep hY hlift hdU hS
  have hdY3 : topologicalKrullDim Y = ((3 : ℕ) : WithBot ℕ∞) := by rw [hdY]; rfl
  have hdU3 : topologicalKrullDim U = ((3 : ℕ) : WithBot ℕ∞) := by rw [hdU]; rfl
  have hdV2 : topologicalKrullDim V = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdV]; rfl
  have hdS2 : topologicalKrullDim S = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdS]; rfl
  haveI := hSc
  haveI : LocallyOfFiniteType (j ≫ p ≫ sY) := hSv.1.toLocallyOfFiniteType
  -- the branch is the strict transform of a horizontal floor prime `Q` of `Y`
  obtain ⟨-, P, hP1, hrange, hci, -⟩ := id hS
  haveI := hci
  have hjT : j (genericPoint S) = P.genericPoint := by
    obtain ⟨P₀, hP₀, -⟩ := hS.exists_primeDivisor
    have h0 : P₀ = P := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support (by
      change P₀.genericPoint ∈ (P.support : Set U)
      rw [← hrange, ← hP₀]
      exact ⟨_, rfl⟩)
    rw [hP₀, h0]
  have hΔP : Δ.coeff P = 1 := le_antisymm (hlift.isDltPair.2.1 P) hP1
  have hqP : r (p P.genericPoint) = genericPoint V := by
    rw [← hjT]
    exact map_genericPoint_of_isDominant (j ≫ p ≫ r)
  obtain ⟨Q, hQ, hiso, hΔQ⟩ :=
    exists_primeDivisor_of_isCrepantDltLift (sV := sV) r.isClosedMap hdY hdV hlift P hqP
  haveI := hiso
  have hBQ : B Q = 1 := hΔQ.symm.trans hΔP
  have hQV : r Q.genericPoint = genericPoint V := by rw [hQ]; exact hqP
  have hordp : ∀ g : Y.functionField,
      U.ord (ψ g) (j (genericPoint S)) = Y.ord g Q.genericPoint := fun g => by
    rw [hψ, hjT]
    exact MMP.Positivity.ord_functionFieldMap_of_isIso p P Q hQ.symm g
  have hxQ : Y.ord x Q.genericPoint = -1 := (hx Q hQV).1 hBQ
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Scheme.ord_zero] at hxQ
    exact absurd hxQ (by norm_num)
  have hco : Order.coheight (j (genericPoint S)) = 1 :=
    hjT ▸ AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  -- elements of `k(V)` are regular along the branch
  have hyV : (p ≫ r) (j (genericPoint S)) = genericPoint V :=
    map_genericPoint_of_isDominant (j ≫ p ≫ r)
  have key : ∀ (z : V), z = genericPoint V → ∀ c : V.functionField,
      ∃ a : V.presheaf.stalk z, algebraMap _ V.functionField a = c := by
    rintro z rfl c
    refine ⟨c, ?_⟩
    change (V.presheaf.stalkSpecializes _).hom c = c
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  choose a ha using key _ hyV
  let vU : V.functionField → U.presheaf.stalk (j (genericPoint S)) := fun c =>
    ((p ≫ r).stalkMap (j (genericPoint S))).hom (a c)
  have hvU : ∀ c, algebraMap _ U.functionField (vU c) = ψ (functionFieldMap r c) := fun c => by
    rw [hψ, ← functionFieldMap_comp_apply]
    calc algebraMap _ U.functionField (vU c)
        = functionFieldMap (p ≫ r) (algebraMap _ V.functionField (a c)) :=
          (MMP.Mori.functionFieldMap_algebraMap_stalk (p ≫ r) (j (genericPoint S)) (a c)).symm
      _ = functionFieldMap (p ≫ r) c := by rw [ha]
  have hvS : ∀ c, (j.stalkMap (genericPoint S)).hom (vU c) = φ c := fun c => by
    have h1 : ((j ≫ p ≫ r).stalkMap (genericPoint S)).hom (a c) =
        (j.stalkMap (genericPoint S)).hom (vU c) := by
      rw [Scheme.Hom.stalkMap_comp]
      rfl
    rw [← h1, hφ]
    have h2 := MMP.Mori.functionFieldMap_algebraMap_stalk (j ≫ p ≫ r) (genericPoint S) (a c)
    have h3 : algebraMap (V.presheaf.stalk ((j ≫ p ≫ r) (genericPoint S))) V.functionField
        (a c) = c := ha c
    rw [h3] at h2
    rw [h2]
    change _ = (S.presheaf.stalkSpecializes _).hom _
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  -- the uniformizer `t = x⁻¹`
  have hψx : U.ord (ψ x⁻¹) (j (genericPoint S)) = 1 := by
    rw [hordp, ← zpow_neg_one, MMP.Mori.ord_zpow _ hx0, hxQ]
    norm_num
  have hψx0 : ψ x⁻¹ ≠ 0 := (map_ne_zero ψ).mpr (inv_ne_zero hx0)
  obtain ⟨tU, htU⟩ :=
    (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hco hψx0).mpr (by rw [hψx]; norm_num)
  have hψx' : U.ord (algebraMap _ U.functionField tU) (j (genericPoint S)) = 1 := by
    rw [htU]
    exact hψx
  -- the forms `dt/t ∧ dξ` on `Y` and on `U`
  let a3 : Fin 3 → Y.functionField := Fin.cons x⁻¹ fun i => functionFieldMap r (ξ i)
  have ha3 : a3 =
      Fin.cons x⁻¹ fun i => functionFieldMap r (ξ i) := rfl
  let ιY := exteriorPower.ιMulti Y.functionField 3
    (fun i => KaehlerDifferential.D k Y.functionField (a3 i))
  have hιYdef : ιY =
      exteriorPower.ιMulti Y.functionField 3
      (fun i => KaehlerDifferential.D k Y.functionField (a3 i)) := rfl
  have hιY : exteriorPower.ιMulti Y.functionField 3
      (Fin.cons (KaehlerDifferential.D k Y.functionField x⁻¹)
        fun i => KaehlerDifferential.D k Y.functionField (functionFieldMap r (ξ i))) = ιY := by
    rw [hιYdef]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [ha3]
  let ιU := exteriorPower.ιMulti U.functionField 3
    (fun i => KaehlerDifferential.D k U.functionField (ψ (a3 i)))
  have hιUdef : ιU =
      exteriorPower.ιMulti U.functionField 3
      (fun i => KaehlerDifferential.D k U.functionField (ψ (a3 i))) := rfl
  have hιU : exteriorPower.ιMulti U.functionField 3
      (Fin.cons (KaehlerDifferential.D k U.functionField (algebraMap _ U.functionField tU))
        fun i => KaehlerDifferential.D k U.functionField (algebraMap _ U.functionField (vU (ξ i))))
      = ιU := by
    rw [hιUdef]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [ha3, htU, hvU]
  have hιU' : ιU = exteriorPower.ιMulti U.functionField 3 fun i =>
      KaehlerDifferential.D k U.functionField
        (algebraMap _ U.functionField ((Fin.cons tU fun i => vU (ξ i) : Fin 3 → _) i)) := by
    rw [← hιU]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  -- the residue of `τ₁ = dt/t ∧ dξ` is `dξ̄`
  let τ₁ : RationalPluriForms (p ≫ sY) 3 ((1 : ℕ) : ℤ) :=
    (formPow (ψ x • ιU) 1 : PluriForms k U.functionField 3 ((1 : ℕ) : ℤ))
  have hτ₁def : τ₁ =
      (formPow (ψ x • ιU) 1 : PluriForms k U.functionField 3 ((1 : ℕ) : ℤ)) := rfl
  let ρ₁ : RationalPluriForms (j ≫ p ≫ sY) 2 ((1 : ℕ) : ℤ) :=
    (formPow (exteriorPower.ιMulti S.functionField 2
      (fun i => KaehlerDifferential.D k S.functionField (φ (ξ i)))) 1 :
        PluriForms k S.functionField 2 ((1 : ℕ) : ℤ))
  have hres₁ : IsPoincareResidue (p ≫ sY) j 2 1 τ₁ ρ₁ := by
    refine ⟨tU, 1, fun i => vU (ξ i), hψx', ?_, ?_⟩
    · beta_reduce
      rw [map_one, one_smul, hιU, htU, map_inv₀, inv_inv]
      rfl
    · rw [map_one, one_smul]
      simp only [hvS]
      rfl
  have hρ₁0 : ρ₁ ≠ 0 := by
    have e : ρ₁ = pluriformPullback (j ≫ p ≫ sY) sV φ 2 ((1 : ℕ) : ℤ)
        ((1 : V.functionField) • formPow (exteriorPower.ιMulti V.functionField 2
          (fun i => KaehlerDifferential.D k V.functionField (ξ i))) 1 :
            PluriForms k V.functionField 2 ((1 : ℕ) : ℤ)) := by
      rw [pluriformPullback_smul_formPow_ιMulti hdS2 hdV2 φ 1 ξ hξ 1, map_one, one_smul]
    rw [e]
    intro h0
    have h1 := MMP.Fourfold.pluriformPullback_injective hdS2 hdV2 φ _ (h0.trans (map_zero _).symm)
    rw [one_smul] at h1
    exact formPow_ne_zero_of_ne_zero hdV2 hξ 1 h1
  -- a branch forces `dt/t ∧ dξ ≠ 0`: otherwise `τ₁ = 0` would have the residue `0 ≠ ρ₁`
  have hιU0 : ιU ≠ 0 := by
    intro h0
    have hτ0 : τ₁ = 0 := by
      rw [hτ₁def, h0, smul_zero]
      exact formPow_zero_of_pos one_pos
    have h2 : IsPoincareResidue (p ≫ sY) j 2 1 τ₁ 0 := by
      rw [hτ0]
      exact isPoincareResidue_zero_zero (p ≫ sY) j hψx' fun i => vU (ξ i)
    exact hρ₁0 (MMP.Fourfold.IsPoincareResidue.unique hS hres₁ h2)
  have hιY0 : ιY ≠ 0 := by
    intro h0
    apply hιU0
    letI : Algebra Y.functionField U.functionField := ψ.toRingHom.toAlgebra
    haveI : IsScalarTower k Y.functionField U.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
    have e := topFormsMap_ιMulti (k := k) (A := Y.functionField) (K := U.functionField) (d := 3)
      (fun i => KaehlerDifferential.D k Y.functionField (a3 i))
    simp only [KaehlerDifferential.map_D] at e
    have h1 : topFormsMap k Y.functionField U.functionField 3 ιY = 0 := by rw [h0, map_zero]
    rw [hιYdef, e] at h1
    exact h1
  refine ⟨by rw [hιY]; exact hιY0, ?_⟩
  intro θ hθ hθ0 G hG c₀ hc₀ c₁ m hm hev
  have hθ' : θ = (G * x) • ιY := by rw [hG, hιY, smul_smul]
  have hG0 : G ≠ 0 := fun h => hθ0 (by rw [hθ', h, zero_mul, zero_smul])
  have hpb : ∀ (c : Y.functionField) (n : ℕ),
      pluriformPullback (p ≫ sY) sY ψ 3 n (c • formPow ιY n : PluriForms k Y.functionField 3 n) =
        (ψ c • formPow ιU n : PluriForms k U.functionField 3 n) := fun c n =>
    pluriformPullback_smul_formPow_ιMulti hdU3 hdY3 ψ c a3 hιY0 n
  have hψxU0 : ψ x • ιU ≠ 0 := smul_ne_zero ((map_ne_zero ψ).mpr hx0) hιU0
  have hτ₁0 : τ₁ ≠ 0 := formPow_ne_zero_of_ne_zero hdU3 hψxU0 1
  have hιU1 : 0 ≤ P.ordForm (sX := p ≫ sY) (d := 3) (m := ((1 : ℕ) : ℤ)) (formPow ιU 1) := by
    rw [hιU']
    exact zero_le_ordForm_formPow_ιMulti_of_eq (sX := p ≫ sY) P hdU3 hjT _
  have hτ₁ord : P.ordForm τ₁ = -1 + P.ordForm (sX := p ≫ sY) (d := 3) (m := ((1 : ℕ) : ℤ))
      (formPow ιU 1) := by
    have e := ordForm_smul_formPow (sX := p ≫ sY) P hdU3 hιU0 ((map_ne_zero ψ).mpr hx0) 1
    rw [hτ₁def, formPow_smul, pow_one]
    rw [e, ← hjT, hordp, hxQ]
    norm_num
  -- uniqueness of residues: `τ₁` has order exactly `-1`
  obtain ⟨Γ₀⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdS2
    (by norm_num)
  obtain ⟨σ, hσ0, hσP, -, ρσ, hresσ, -, -⟩ :=
    MMP.Fourfold.exists_form_of_residue_order (p ≫ sY) hUv (n := 2)
      (by rw [hdU]; rfl) j hSv P hrange Γ₀
  obtain ⟨b⟩ := exists_basis_topForms (sX := p ≫ sY) hdU3
  let bb := ZTensorPower.basis b ((1 : ℕ) : ℤ)
  have hσr : bb.repr σ () ≠ 0 := repr_unit_ne_zero bb hσ0
  let h := bb.repr τ₁ () / bb.repr σ ()
  have hτσ : τ₁ = h • σ := eq_repr_div_smul bb hσr τ₁
  have hh0 : h ≠ 0 := fun h0 => hτ₁0 (by rw [hτσ, h0, zero_smul])
  have hτh : P.ordForm τ₁ = U.ord h P.genericPoint - 1 := by
    rw [hτσ, P.ordForm_smul_of_topologicalKrullDim_eq hdU3 hh0 hσ0, hσP]
    ring
  have hh_nonneg : 0 ≤ U.ord h (j (genericPoint S)) := by
    rw [hjT]
    have := hτ₁ord
    rw [hτh] at this
    omega
  obtain ⟨hs, hhs⟩ := (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hco hh0).mpr hh_nonneg
  have hres_h :
      IsPoincareResidue (p ≫ sY) j 2 1 τ₁ ((j.stalkMap (genericPoint S)).hom hs • ρσ) := by
    have := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hresσ hs
    rw [hhs, ← hτσ] at this
    exact this
  have huniq := MMP.Fourfold.IsPoincareResidue.unique hS hres₁ hres_h
  have hjs : (j.stalkMap (genericPoint S)).hom hs ≠ 0 := fun h0 =>
    hρ₁0 (by rw [huniq, h0, zero_smul])
  have hh_zero : U.ord h P.genericPoint = 0 := by
    by_contra hne
    apply hjs
    refine stalkMap_eq_zero_of_one_le_ord hS hψx' hs fun _ => ?_
    rw [hhs, hjT]
    have := hh_nonneg
    rw [hjT] at this
    omega
  have hιU1' : P.ordForm (sX := p ≫ sY) (d := 3) (m := ((1 : ℕ) : ℤ)) (formPow ιU 1) = 0 := by
    have := hτ₁ord
    rw [hτh, hh_zero] at this
    omega
  -- `G` is a unit along `Q`
  have htd3 : (Algebra.trdeg k Y.functionField).toNat = 3 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hdY3
  have hψe : ψ = ffHom sY p (rfl : p ≫ sY = p ≫ sY) := AlgHom.ext fun c => hψ c
  have htr := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso (sX := sY)
    (d := 3) (m := ((1 : ℕ) : ℤ)) p
    hlift.isBirationalMorphism.functionFieldMap_bijective htd3 P Q hQ.symm (formPow θ 1)
  have hpbθ : pullbackRationalPluriForms (d := 3) (m := ((1 : ℕ) : ℤ)) sY p (formPow θ 1) =
      (ψ (G * x) • formPow ιU 1 : PluriForms k U.functionField 3 ((1 : ℕ) : ℤ)) := by
    rw [← hpb, hψe, hθ', formPow_smul, pow_one]
    rfl
  rw [hpbθ, hθ Q hQV, if_pos hBQ,
    ordForm_smul_formPow (sX := p ≫ sY) P hdU3 hιU0 ((map_ne_zero ψ).mpr (mul_ne_zero hG0 hx0)) 1,
    hιU1', mul_zero, add_zero, ← hjT, hordp, Scheme.ord_mul hG0 hx0, hxQ] at htr
  have hGQ : Y.ord G Q.genericPoint = 0 := by omega
  have hψG : U.ord (ψ G) (j (genericPoint S)) = 0 := by rw [hordp, hGQ]
  obtain ⟨gG, hgG⟩ := (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hco
    ((map_ne_zero ψ).mpr hG0)).mpr hψG.ge
  -- `Ḡ² = c̄₀` on the branch
  have hG2 : Y.ord (G ^ 2) Q.genericPoint = 0 := by
    rw [pow_two, Scheme.ord_mul hG0 hG0, hGQ, add_zero]
  have hv := hc₀ Q hQV hxQ hG2
  have hjG : (j.stalkMap (genericPoint S)).hom gG ^ 2 = φ c₀ := by
    have h0 := stalkMap_eq_zero_of_one_le_ord hS hψx' (gG ^ 2 - vU c₀) fun hz => by
      have hz' : algebraMap _ U.functionField (gG ^ 2 - vU c₀) =
          ψ (G ^ 2 - functionFieldMap r c₀) := by
        rw [map_sub, map_pow, hgG, hvU, map_sub, map_pow]
      rw [hz'] at hz ⊢
      have hz0 : G ^ 2 - functionFieldMap r c₀ ≠ 0 := fun h0 => hz (by rw [h0, map_zero])
      rw [hordp]
      rw [Q.divisorialValuation_eq_exp_neg_ord hz0, ← WithZero.exp_zero,
        WithZero.exp_lt_exp] at hv
      omega
    rw [map_sub, map_pow, hvS, sub_eq_zero] at h0
    exact h0
  have hjGm : (j.stalkMap (genericPoint S)).hom gG ^ m = φ c₀ ^ (m / 2) := by
    rw [← hjG, ← pow_mul, Nat.two_mul_div_two_of_even hev]
  -- the presentation of `p^*(c₁ θ^{⊗m})`
  refine ⟨tU, vU c₁ * gG ^ m, fun i => vU (ξ i), hψx', ?_, ?_⟩
  · rw [hθ', formPow_smul, smul_smul, hpb]
    beta_reduce
    rw [hιU, htU, map_inv₀, inv_inv]
    change _ = (algebraMap _ U.functionField (vU c₁ * gG ^ m) • formPow (ψ x • ιU) m :
      PluriForms k U.functionField 3 m)
    rw [formPow_smul, smul_smul]
    congr 1
    simp only [map_mul, map_pow, hvU, hgG]
    ring
  · rw [pluriformPullback_smul_formPow_ιMulti hdS2 hdV2 φ _ ξ hξ m]
    beta_reduce
    simp only [map_mul, map_pow, hvS, hjGm]
    rfl

/-- **The residue form of a two-floor Mori curve fibration** (the descent of `(dz/z)^m`). In the
Mori setting, for every sufficiently divisible even `m` there are nonzero rational `m`-canonical
forms `α` on `Y` and `ω` on `V` and a Cartier divisor `M` with `div α + mB = r^*M`, such that the
Poincaré residue of `p^*α` along every horizontal floor branch of every crepant dlt lift is the
pull-back of `ω`. -/
private theorem exists_residueForm
    {Y V : Scheme.{0}}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [QuasiCompact sY] {r : Y ⟶ V}
    (hr : IsContraction sY sV r)
    (hY : MMP.Mori.IsProjectiveVariety k sY) (hV : MMP.Mori.IsProjectiveVariety k sV)
    (hdY : topologicalKrullDim Y = 3) (hdV : topologicalKrullDim V = 2)
    (hQ : IsQFactorial sY) (hρ : relativePicardNumberN1 sY r = 1)
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {Γ : QDivisor Y} (hΓ : IsKltPair sY Γ)
    (hΓa : (-(Divisor.toQDivisor K + Γ)).HasRelativelyAmpleMultiple r)
    {B : QDivisor Y} (hB : MMP.Intersection.IsLogCanonicalPair sY B)
    (hD : MMP.Flips.IsNumericallyTrivialOver k sY r
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    (hε : ∃ ε : ℚ, 0 < ε ∧
      IsKltPair sY (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))
    (hdeg : open scoped Classical in
      ∑ P ∈ B.support with B P = 1 ∧ r.base '' (P.support : Set Y) = Set.univ,
        (letI := (r.residueFieldMap P.genericPoint).hom.toAlgebra;
          Module.finrank (V.residueField (r P.genericPoint)) (Y.residueField P.genericPoint))
        = 2) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, 0 < m → m₀ ∣ m → Even m →
    ∃ (α : RationalPluriForms sY 3 m) (ω : RationalPluriForms sV 2 m) (M : Divisor V)
      (hM : M.IsCartier)
      (hrM : ∀ W : irreducibleComponents Y,
        r (componentGenericPoint Y W) ∉ DivisorWithCoeffs.supp M),
      α ≠ 0 ∧ ω ≠ 0 ∧
      (∀ P : MMP.Mori.PrimeDivisor Y,
        (P.ordForm α : ℚ) + (m : ℚ) * B P = ((M.pullback (f := r) hM hrM) P : ℚ)) ∧
      ∀ (U : Scheme.{0}) [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
        (p : U ⟶ Y) [IsDominant p] (Δ : QDivisor U), IsCrepantDltModel sY K B p Δ →
        (∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
          (j : S ⟶ U) (BS : QDivisor S) [IsDominant (j ≫ p ≫ r)],
          IsAdjunctionStep (p ≫ sY) Δ j BS →
          ∀ (ψ : FunctionFieldHom (p ≫ sY) sY) (φ : FunctionFieldHom (j ≫ p ≫ sY) sV),
            (∀ x, ψ x = functionFieldMap p x) →
            (∀ x, φ x = functionFieldMap (j ≫ p ≫ r) x) →
            IsPoincareResidue (p ≫ sY) j 2 m (pluriformPullback (p ≫ sY) sY ψ 3 m α)
              (pluriformPullback (j ≫ p ≫ sY) sV φ 2 m ω)) := by
  classical
  have hn3 : n = 3 := by
    have := hK.topologicalKrullDim_eq.symm.trans hdY
    exact_mod_cast this
  subst hn3
  haveI : LocallyOfFiniteType sY :=
    ((MMP.Mori.isProjectiveVariety_iff k sY).1 hY).1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sV :=
    ((MMP.Mori.isProjectiveVariety_iff k sV).1 hV).1.toLocallyOfFiniteType
  haveI : IsProper sY :=
    isProper_of_isProjectiveMorphism sY ((MMP.Mori.isProjectiveVariety_iff k sY).1 hY).2
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.isProjectiveMorphism
  haveI : IsDominant r := ⟨hr.surjective.denseRange⟩
  have hrs := hr.comp_eq
  have hrapp := hr.isIso_app
  have hcl : IsClosedMap r := r.isClosedMap
  obtain ⟨h0, h1, h2, h3, h4⟩ := genericFibre_riemannRoch hr hY hV hdY hdV hK
  obtain ⟨m₁, hm₁, hα⟩ := exists_ordForm_add_eq_pullback hr hY hV hQ hK hΓ hΓa hD
  have hB0 : ∀ Q, 0 ≤ B Q := fun Q => hB.2.1 Q
  have hdeg' : (∑ Q ∈ B.support with B Q = 1 ∧ r Q.genericPoint = genericPoint V,
      MMP.Flips.genericFiberPointDegree r Q) = 2 := by
    rw [← hdeg]
    refine Finset.sum_congr (Finset.filter_congr fun P _ => ?_) fun P hP => ?_
    · rw [image_support_eq_univ_iff r hcl P]
    · have hP' := (Finset.mem_filter.mp hP).2.2
      unfold MMP.Flips.genericFiberPointDegree
      rw [if_pos ((image_support_eq_univ_iff r hcl P).mp hP')]
  -- the horizontal coefficients of an `m`-form with `div α + mB = r^*M`
  have hhor : ∀ {m : ℕ} {α : RationalPluriForms sY 3 m} {M : Divisor V} (hM : M.IsCartier),
      (∀ P : MMP.Mori.PrimeDivisor Y, (P.ordForm α : ℚ) + (m : ℚ) * B P =
        ((M.pullback (f := r) hM
          (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp r M)) P : ℚ)) →
      ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
        (Q.ordForm α : ℚ) = -(m : ℚ) * B Q := by
    intro m α M hM hαM Q hQ
    have hz := coeff_isPullback_eq_zero_of_map_genericPoint (Divisor.isPullback_pullback hM
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp r M)) Q hQ
    have := hαM Q
    have hz' : (M.pullback (f := r) hM
        (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp r M)) Q = 0 := hz
    rw [hz'] at this
    push_cast at this
    linarith
  obtain ⟨α₁, M₁, hM₁, hα₁0, hα₁⟩ := hα m₁ hm₁ dvd_rfl
  haveI : Infinite V.functionField := by
    letI := functionFieldAlgebra sV
    exact Infinite.of_injective _ (algebraMap k V.functionField).injective
  obtain ⟨hgC, x, θ, hθ0, hxθ⟩ := exists_floor_coordinate_and_form hdY h0 h1 h2 h3 h4 hB0 hdeg'
    hm₁ hα₁0 (hhor hM₁ hα₁)
  have hx : ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      (B Q = 1 → Y.ord x Q.genericPoint = -1) ∧ (B Q ≠ 1 → 0 ≤ Y.ord x Q.genericPoint) :=
    fun Q hQ => ⟨fun h => ((hxθ Q hQ).1 h).1, fun h => ((hxθ Q hQ).2 h).1⟩
  have hθ : letI := functionFieldAlgebra sY
      ∀ Q : MMP.Mori.PrimeDivisor Y, r Q.genericPoint = genericPoint V →
      Q.ordForm (sX := sY) (d := 3) (m := ((1 : ℕ) : ℤ)) (formPow θ 1) =
        if B Q = 1 then -1 else 0 := by
    intro Q hQ
    split_ifs with h
    · exact ((hxθ Q hQ).1 h).2
    · exact ((hxθ Q hQ).2 h).2
  have hdeg2 := finrank_adjoin_floorCoordinate_le_two hrs hdY hdV (h2 hgC) hdeg' hx
  obtain ⟨ξ, hξ⟩ := exists_ιMulti_D_ne_zero (sV := sV) hdV
  letI := functionFieldAlgebra sY
  have hdV2 : topologicalKrullDim V = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdV]; rfl
  have hx0 : x ≠ 0 := by
    rintro rfl
    obtain ⟨Q, hQ, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hdeg'.trans_ne two_ne_zero)
    obtain ⟨-, hB1, hQh⟩ := Finset.mem_filter.mp hQ
    have hord := (hx Q hQh).1 hB1
    rw [Scheme.ord_zero] at hord
    exact absurd hord (by norm_num)
  by_cases hlam : exteriorPower.ιMulti Y.functionField 3
      (Fin.cons (KaehlerDifferential.D k Y.functionField x⁻¹)
        fun i => KaehlerDifferential.D k Y.functionField (functionFieldMap r (ξ i))) = 0
  · -- then there is no horizontal floor branch at all
    refine ⟨m₁, hm₁, fun m hm hdvd hev => ?_⟩
    obtain ⟨α, M, hM, hα0, hαM⟩ := hα m hm hdvd
    letI := functionFieldAlgebra sV
    refine ⟨α, (formPow (exteriorPower.ιMulti V.functionField 2
        (fun i => KaehlerDifferential.D k V.functionField (ξ i))) m :
          PluriForms k V.functionField 2 m), M, hM, _, hα0,
      formPow_ne_zero_of_ne_zero hdV2 hξ m, hαM, ?_⟩
    intro U _ _ _ p _ Δ hlift S _ _ _ j BS _ hS ψ φ hψ hφ
    exact absurd hlam (isPoincareResidue_floor_of_eq_smul hr hY hV hdY hdV hx ξ hξ
      U p Δ hlift S j BS hS ψ φ hψ hφ).1
  -- `θ = G (dt/t ∧ dξ)` with `t = x⁻¹`, the top forms of `k(Y)` being a line
  obtain ⟨G, hG⟩ : ∃ G : Y.functionField, θ = G • (x • exteriorPower.ιMulti Y.functionField 3
      (Fin.cons (KaehlerDifferential.D k Y.functionField x⁻¹)
        fun i => KaehlerDifferential.D k Y.functionField (functionFieldMap r (ξ i)))) := by
    obtain ⟨b⟩ := exists_basis_topForms (sX := sY) (d := 3) (by rw [hdY]; rfl)
    set lam := x • exteriorPower.ιMulti Y.functionField 3
      (Fin.cons (KaehlerDifferential.D k Y.functionField x⁻¹)
        fun i => KaehlerDifferential.D k Y.functionField (functionFieldMap r (ξ i))) with hlamdef
    have hl0 : lam ≠ 0 := smul_ne_zero hx0 hlam
    have hlr : b.repr lam () ≠ 0 := fun h0 =>
      hl0 (by rw [← basis_unit_repr_smul b lam, h0, zero_smul])
    refine ⟨b.repr θ () / b.repr lam (), ?_⟩
    have e3 : (b.repr θ () / b.repr lam ()) • (b.repr lam () • b ()) = b.repr θ () • b () := by
      rw [smul_smul, div_mul_cancel₀ _ hlr]
    rw [basis_unit_repr_smul, basis_unit_repr_smul] at e3
    exact e3.symm
  have hG0 : G ≠ 0 := by
    rintro rfl
    exact hθ0 (by rw [hG, zero_smul])
  have hG2 := sq_mem_adjoin_of_eq_smul hrs hrapp hcl hdY hdV hx hdeg2 hθ0 hθ ξ hG
  obtain ⟨c₀, hc₀0, hc₀⟩ := exists_sub_mem_maximalIdeal_of_mem_adjoin hG2 (pow_ne_zero 2 hG0)
  refine ⟨m₁, hm₁, fun m hm hdvd hev => ?_⟩
  obtain ⟨α, M, hM, hα0, hαM⟩ := hα m hm hdvd
  obtain ⟨c₁, hc₁0, hαθ⟩ :=
    exists_eq_functionFieldMap_smul_formPow hrapp hcl hdY hB0 hθ0 hθ hα0 (hhor hM hαM)
  letI := functionFieldAlgebra sV
  refine ⟨α, ((c₁ * c₀ ^ (m / 2)) • formPow (exteriorPower.ιMulti V.functionField 2
      (fun i => KaehlerDifferential.D k V.functionField (ξ i))) m :
        PluriForms k V.functionField 2 m), M, hM, _, hα0,
    smul_ne_zero (mul_ne_zero hc₁0 (pow_ne_zero _ hc₀0)) (formPow_ne_zero_of_ne_zero hdV2 hξ m),
    hαM, ?_⟩
  intro U _ _ _ p _ Δ hlift S _ _ _ j BS _ hS ψ φ hψ hφ
  rw [hαθ]
  exact (isPoincareResidue_floor_of_eq_smul hr hY hV hdY hdV hx ξ hξ U p Δ hlift S j BS hS ψ φ
    hψ hφ).2 hθ hθ0 hG hc₀ c₁ hm hev

/-- **Exact crepant residue identifications for a two-floor Mori curve fibration.** Let
`r : Y ⟶ V` be a contraction of a `ℚ`-factorial projective threefold onto a projective surface
with `ρ(Y/V) = 1` and `-(K + Γ)` relatively ample for a klt boundary `Γ`. Let `B` be an lc
boundary with `K + B ≡_V 0`, such that `(Y, B - ε⌊B⌋)` is klt for some rational `ε > 0`, and
whose horizontal floor has degree two on the generic fibre. Then for every sufficiently divisible
even `m` there are nonzero rational `m`-canonical forms `α` on `Y` and `ω` on `V` and a Cartier
divisor `M` on `V` with `div(α) + mB = r^*M`, such that for every normal crepant dlt model
`p : (U, Δ) ⟶ (Y, B)` (projective birational, crepant, dlt):
* the Poincaré residue of `p^*α` along every horizontal floor branch `S` of `Δ` is the pull-back
  of `ω` along `S ⟶ V`;
* the degrees `[k(S) : k(V)]` of the horizontal floor primes of `Δ` sum to two;
* any two distinct horizontal floor branches are identified by a crepant birational map over
  `V`;
* a horizontal floor branch of degree two has a nontrivial crepant birational involution over
  `V`. -/
@[mmp "lem_fourfold_mori_threefold_two_floor_residues"]
public theorem IsContraction.exists_isPoincareResidue_of_floor_degree_eq_two
    {Y V : Scheme.{0}}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [QuasiCompact sY] {r : Y ⟶ V}
    (hr : IsContraction sY sV r)
    (hY : MMP.Mori.IsProjectiveVariety k sY) (hV : MMP.Mori.IsProjectiveVariety k sV)
    (hdY : topologicalKrullDim Y = 3) (hdV : topologicalKrullDim V = 2)
    (hQ : IsQFactorial sY) (hρ : relativePicardNumberN1 sY r = 1)
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {Γ : QDivisor Y} (hΓ : IsKltPair sY Γ)
    (hΓa : (-(Divisor.toQDivisor K + Γ)).HasRelativelyAmpleMultiple r)
    {B : QDivisor Y} (hB : MMP.Intersection.IsLogCanonicalPair sY B)
    (hD : MMP.Flips.IsNumericallyTrivialOver k sY r
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    (hε : ∃ ε : ℚ, 0 < ε ∧
      IsKltPair sY (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))
    (hdeg : open scoped Classical in
      ∑ P ∈ B.support with B P = 1 ∧ r.base '' (P.support : Set Y) = Set.univ,
        (letI := (r.residueFieldMap P.genericPoint).hom.toAlgebra;
          Module.finrank (V.residueField (r P.genericPoint)) (Y.residueField P.genericPoint))
        = 2) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, 0 < m → m₀ ∣ m → Even m →
      ∃ (α : RationalPluriForms sY 3 m) (ω : RationalPluriForms sV 2 m) (M : Divisor V)
        (hM : M.IsCartier)
        (hrM : ∀ W : irreducibleComponents Y,
          r (componentGenericPoint Y W) ∉ DivisorWithCoeffs.supp M),
        α ≠ 0 ∧ ω ≠ 0 ∧
        (∀ P : MMP.Mori.PrimeDivisor Y,
          (P.ordForm α : ℚ) + (m : ℚ) * B P = ((M.pullback (f := r) hM hrM) P : ℚ)) ∧
        ∀ (U : Scheme.{0}) [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
          (p : U ⟶ Y) [IsDominant p] (Δ : QDivisor U), IsProjectiveMorphism p →
          (∃ (KY : Divisor Y) (hU : IsNormalVariety k (p ≫ sY)) (hp : IsBirationalMorphism p),
            IsCrepantBoundary sY 3 KY B p hU hp Δ) →
          MMP.Intersection.IsDltPair (p ≫ sY) Δ →
          -- the residues of `p^*α` on the horizontal floor branches are pull-backs of `ω`
          (∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
            (j : S ⟶ U) (BS : QDivisor S) [IsDominant (j ≫ p ≫ r)],
            IsAdjunctionStep (p ≫ sY) Δ j BS →
            ∀ (ψ : FunctionFieldHom (p ≫ sY) sY) (φ : FunctionFieldHom (j ≫ p ≫ sY) sV),
              (∀ x, ψ x = functionFieldMap p x) →
              (∀ x, φ x = functionFieldMap (j ≫ p ≫ r) x) →
              IsPoincareResidue (p ≫ sY) j 2 m (pluriformPullback (p ≫ sY) sY ψ 3 m α)
                (pluriformPullback (j ≫ p ≫ sY) sV φ 2 m ω)) ∧
          -- the Stein degrees of the horizontal floor of `Δ` sum to two
          (open scoped Classical in
            ∑ P ∈ Δ.support with Δ P = 1 ∧ (p ≫ r).base '' (P.support : Set U) = Set.univ,
              (letI := ((p ≫ r).residueFieldMap P.genericPoint).hom.toAlgebra;
                Module.finrank (V.residueField ((p ≫ r) P.genericPoint))
                  (U.residueField P.genericPoint)) = 2) ∧
          -- two distinct horizontal branches are crepant birationally identified over `V`
          (∀ (S₁ : Scheme.{0}) [IsIntegral S₁] [IsLocallyNoetherian S₁] [IsNormal S₁]
            (j₁ : S₁ ⟶ U) (B₁ : QDivisor S₁) [IsDominant (j₁ ≫ p ≫ r)]
            (S₂ : Scheme.{0}) [IsIntegral S₂] [IsLocallyNoetherian S₂] [IsNormal S₂]
            (j₂ : S₂ ⟶ U) (B₂ : QDivisor S₂) [IsDominant (j₂ ≫ p ≫ r)],
            IsAdjunctionStep (p ≫ sY) Δ j₁ B₁ → IsAdjunctionStep (p ≫ sY) Δ j₂ B₂ →
            Set.range j₁.base ≠ Set.range j₂.base →
            ∃ σ : FunctionFieldEquiv (j₁ ≫ p ≫ sY) (j₂ ≫ p ≫ sY),
              IsCrepantBirationalMap (j₁ ≫ p ≫ sY) (j₂ ≫ p ≫ sY) B₁ B₂ σ ∧
              ∀ x : V.functionField,
                σ (functionFieldMap (j₂ ≫ p ≫ r) x) = functionFieldMap (j₁ ≫ p ≫ r) x) ∧
          -- a horizontal branch of degree two has a crepant involution over `V`
          (∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
            (j : S ⟶ U) (BS : QDivisor S) [IsDominant (j ≫ p ≫ r)],
            IsAdjunctionStep (p ≫ sY) Δ j BS →
            (letI := functionFieldMapAlgebra (j ≫ p ≫ r);
              Module.finrank V.functionField S.functionField) = 2 →
            ∃ σ : FunctionFieldEquiv (j ≫ p ≫ sY) (j ≫ p ≫ sY),
              σ ≠ 1 ∧ σ * σ = 1 ∧
              IsCrepantBirationalMap (j ≫ p ≫ sY) (j ≫ p ≫ sY) BS BS σ ∧
              ∀ x : V.functionField,
                σ (functionFieldMap (j ≫ p ≫ r) x) = functionFieldMap (j ≫ p ≫ r) x) := by
  classical
  -- the residue form: the deep step
  have key := exists_residueForm hr hY hV hdY hdV hQ hρ hK hΓ hΓa hB hD hε hdeg
  obtain ⟨m₀, hm₀, hform⟩ := key
  refine ⟨m₀, hm₀, fun m hm hdvd hev => ?_⟩
  obtain ⟨α, ω, M, hM, hrM, hα, hω, hdiv, hres⟩ := hform m hm hdvd hev
  refine ⟨α, ω, M, hM, hrM, hα, hω, hdiv, fun U _ _ _ p _ Δ hpp hcb hdlt => ?_⟩
  have hlift : IsCrepantDltModel sY K B p Δ := isCrepantDltModel_of hY hK hpp hcb hdlt
  have hi := hres U p Δ hlift
  have hs3 : ∀ {T : Scheme.{0}} (j : T ⟶ U), (j ≫ p ≫ r) ≫ sV = j ≫ p ≫ sY := fun j => by
    simp only [Category.assoc, hr.comp_eq]
  haveI : IsSeparated sV := ((MMP.Mori.isProjectiveVariety_iff k sV).1 hV).1.toIsSeparated
  haveI : LocallyOfFiniteType sV :=
    ((MMP.Mori.isProjectiveVariety_iff k sV).1 hV).1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sY :=
    ((MMP.Mori.isProjectiveVariety_iff k sY).1 hY).1.toLocallyOfFiniteType
  have hUv : IsNormalVariety k (p ≫ sY) := hlift.isNormalVariety
  haveI : LocallyOfFiniteType (p ≫ sY) := hUv.1.toLocallyOfFiniteType
  have hdU : topologicalKrullDim U = 3 := by
    haveI := ((MMP.Mori.isProjectiveVariety_iff k sY).1 hY).1
    haveI := hUv.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (p ≫ sY)
      hlift.isBirationalMorphism, hdY]
  -- the pull-back of `ω` to a branch is nonzero
  have hρ0 : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
      (j : S ⟶ U) (BS : QDivisor S) [IsDominant (j ≫ p ≫ r)], IsAdjunctionStep (p ≫ sY) Δ j BS →
      pluriformPullback (j ≫ p ≫ sY) sV (ffHom sV (j ≫ p ≫ r) (hs3 j)) 2 m ω ≠ 0 := by
    intro S _ _ _ j BS _ hS h0
    obtain ⟨hv, -, -, hd⟩ := isNormalVariety_of_isAdjunctionStep hY hlift hdU hS
    haveI : LocallyOfFiniteType (j ≫ p ≫ sY) := hv.1.toLocallyOfFiniteType
    exact hω (MMP.Fourfold.pluriformPullback_injective hd hdV _ _ (h0.trans (map_zero _).symm))
  -- adjunction: on every horizontal branch, `div(g^*ω) + m B_S = g^*M`
  have hadj : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
      (j : S ⟶ U) (BS : QDivisor S) [IsDominant (j ≫ p ≫ r)],
      IsAdjunctionStep (p ≫ sY) Δ j BS →
      ∃ MS : Divisor S, M.IsPullback (j ≫ p ≫ r)
          (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (j ≫ p ≫ r) M) MS ∧
        ∀ Γ : MMP.Mori.PrimeDivisor S,
          (Γ.ordForm (pluriformPullback (j ≫ p ≫ sY) sV (ffHom sV (j ≫ p ≫ r) (hs3 j))
            2 m ω) : ℚ) + m * BS.coeff Γ = MS.coeff Γ := by
    intro S _ _ _ j BS _ hS
    obtain ⟨hv, hp, hc, hd⟩ := isNormalVariety_of_isAdjunctionStep hY hlift hdU hS
    haveI := hc
    haveI : IsProper p := isProper_of_isProjectiveMorphism p hlift.isProjectiveMorphism
    haveI : IsProper sY :=
      isProper_of_isProjectiveMorphism sY ((MMP.Mori.isProjectiveVariety_iff k sY).1 hY).2
    haveI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (p ≫ sY)
    haveI : IsDominant r := ⟨hr.surjective.denseRange⟩
    have hn3 : n = 3 := by
      have := hK.topologicalKrullDim_eq.symm.trans hdY
      exact_mod_cast this
    subst hn3
    obtain ⟨MU, hMU⟩ := hM.exists_isPullback (f := p ≫ r)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (p ≫ r) M)
    have hτ := ordForm_pullback_add_eq_of_isCrepantDltLift hM
      (Divisor.isPullback_pullback hM hrM) hm hα hdiv p hlift hK hMU
    have hres := hi S j BS hS (ffHom sY p rfl) (ffHom sV (j ≫ p ≫ r) (hs3 j)) (fun _ => rfl)
      (fun _ => rfl)
    exact exists_ordForm_add_eq_of_isPoincareResidue (V := V) hS
      (isQCartier_divisorOfForm_add_of_isPair hlift.isDltPair.1.1 (by rw [hdU]; rfl)) (n := 2)
      (by rw [hdU]; rfl) (by rw [hd]; rfl) hlift.isDltPair.2.1 hM hMU hm hτ
      (hρ0 S j BS hS) hres
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.isProjectiveMorphism
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hlift.isProjectiveMorphism
  have hclU : IsClosedMap (p ≫ r) := fun Z hZ => by
    have := r.isClosedMap _ (p.isClosedMap _ hZ)
    rwa [Set.image_image] at this
  -- the Stein degrees of the horizontal floor of `Δ`
  have hii : (open scoped Classical in
      ∑ P ∈ Δ.support with Δ P = 1 ∧ (p ≫ r).base '' (P.support : Set U) = Set.univ,
        (letI := ((p ≫ r).residueFieldMap P.genericPoint).hom.toAlgebra;
          Module.finrank (V.residueField ((p ≫ r) P.genericPoint))
            (U.residueField P.genericPoint))) = 2 := by
    rw [sum_floor_finrank_eq (sV := sV) r.isClosedMap hdY hdV hlift]
    exact hdeg
  -- a field extension of degree one is an isomorphism
  have hone : ∀ {S : Scheme.{0}} [IsIntegral S] (g : S ⟶ V) [IsDominant g],
      (letI := functionFieldMapAlgebra g; Module.finrank V.functionField S.functionField) = 1 →
      Function.Bijective (functionFieldMap g) := by
    intro S _ g _ h
    letI := functionFieldMapAlgebra g
    refine ⟨(functionFieldMap g).injective, fun x => ?_⟩
    have htop := Subalgebra.bot_eq_top_of_finrank_eq_one h
    have hx : x ∈ (⊥ : Subalgebra V.functionField S.functionField) := htop ▸ Algebra.mem_top
    obtain ⟨y, rfl⟩ := Algebra.mem_bot.mp hx
    exact ⟨y, rfl⟩
  refine ⟨hi, hii, ?_, ?_⟩
  · -- two distinct branches: both have degree one, so are birational over `V`
    intro S₁ _ _ _ j₁ B₁ _ S₂ _ _ _ j₂ B₂ _ h₁ h₂ hne
    obtain ⟨hv₁, hp₁, hc₁, hd₁⟩ := isNormalVariety_of_isAdjunctionStep hY hlift hdU h₁
    obtain ⟨hv₂, hp₂, hc₂, hd₂⟩ := isNormalVariety_of_isAdjunctionStep hY hlift hdU h₂
    have hbij : Function.Bijective (functionFieldMap (j₁ ≫ p ≫ r)) ∧
        Function.Bijective (functionFieldMap (j₂ ≫ p ≫ r)) := by
      classical
      obtain ⟨P₁, hr₁, hΔ₁, him₁, hf₁, hpos₁⟩ :=
        exists_floor_primeDivisor_of_isAdjunctionStep hr.comp_eq hlift hclU h₁ hd₁ hdV
      obtain ⟨P₂, hr₂, hΔ₂, him₂, hf₂, hpos₂⟩ :=
        exists_floor_primeDivisor_of_isAdjunctionStep hr.comp_eq hlift hclU h₂ hd₂ hdV
      have hne' : P₁ ≠ P₂ := fun h => hne (by rw [hr₁, hr₂, h])
      set f : MMP.Mori.PrimeDivisor U → ℕ := fun P =>
        letI := ((p ≫ r).residueFieldMap P.genericPoint).hom.toAlgebra
        Module.finrank (V.residueField ((p ≫ r) P.genericPoint)) (U.residueField P.genericPoint)
      have hmem : ∀ P : MMP.Mori.PrimeDivisor U, Δ P = 1 →
          (p ≫ r).base '' (P.support : Set U) = Set.univ →
          P ∈ Δ.support.filter
            (fun P => Δ P = 1 ∧ (p ≫ r).base '' (P.support : Set U) = Set.univ) :=
        fun P h1 h2 => Finset.mem_filter.mpr
          ⟨Finsupp.mem_support_iff.mpr (by rw [h1]; exact one_ne_zero), h1, h2⟩
      have hle : f P₁ + f P₂ ≤ 2 := by
        rw [← hii, ← Finset.sum_pair hne']
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.zero_le _
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hmem _ hΔ₁ him₁
        · rw [Finset.mem_singleton.mp hx]
          exact hmem _ hΔ₂ him₂
      have e₁ : f P₁ = (letI := functionFieldMapAlgebra (j₁ ≫ p ≫ r);
          Module.finrank V.functionField S₁.functionField) := hf₁.symm
      have e₂ : f P₂ = (letI := functionFieldMapAlgebra (j₂ ≫ p ≫ r);
          Module.finrank V.functionField S₂.functionField) := hf₂.symm
      rw [e₁, e₂] at hle
      exact ⟨hone _ (by omega), hone _ (by omega)⟩
    letI := functionFieldAlgebra sV
    letI := functionFieldAlgebra (j₁ ≫ p ≫ sY)
    letI := functionFieldAlgebra (j₂ ≫ p ≫ sY)
    let e₁ := AlgEquiv.ofBijective (ffHom sV (j₁ ≫ p ≫ r) (hs3 j₁)) hbij.1
    let e₂ := AlgEquiv.ofBijective (ffHom sV (j₂ ≫ p ≫ r) (hs3 j₂)) hbij.2
    let σ : FunctionFieldEquiv (j₁ ≫ p ≫ sY) (j₂ ≫ p ≫ sY) := e₂.symm.trans e₁
    have hσ : ∀ x : V.functionField,
        σ (functionFieldMap (j₂ ≫ p ≫ r) x) = functionFieldMap (j₁ ≫ p ≫ r) x := by
      intro x
      change e₁ (e₂.symm (e₂ x)) = _
      rw [AlgEquiv.symm_apply_apply]
      rfl
    obtain ⟨MS₁, hMS₁, hB₁⟩ := hadj S₁ j₁ B₁ h₁
    obtain ⟨MS₂, hMS₂, hB₂⟩ := hadj S₂ j₂ B₂ h₂
    have hσρ : pluriformPullback (j₁ ≫ p ≫ sY) (j₂ ≫ p ≫ sY) σ.toHom 2 m
        (pluriformPullback (j₂ ≫ p ≫ sY) sV (ffHom sV (j₂ ≫ p ≫ r) (hs3 j₂)) 2 m ω) =
        pluriformPullback (j₁ ≫ p ≫ sY) sV (ffHom sV (j₁ ≫ p ≫ r) (hs3 j₁)) 2 m ω := by
      haveI : LocallyOfFiniteType (j₁ ≫ p ≫ sY) := hv₁.1.toLocallyOfFiniteType
      haveI : LocallyOfFiniteType (j₂ ≫ p ≫ sY) := hv₂.1.toLocallyOfFiniteType
      rw [pluriformPullback_comp hd₁ hd₂ hdV]
      have : (FunctionFieldEquiv.toHom _ _ σ).comp (ffHom sV (j₂ ≫ p ≫ r) (hs3 j₂)) =
          ffHom sV (j₁ ≫ p ≫ r) (hs3 j₁) := AlgHom.ext fun x => hσ x
      rw [this]
    haveI := hp₁
    haveI := hp₂
    haveI := hc₁
    haveI := hc₂
    exact ⟨σ, isCrepantBirationalMap_of_ordForm_add_eq_pullback sV hv₁ hv₂ hd₁ hd₂
      (j₁ ≫ p ≫ r) (j₂ ≫ p ≫ r) hM hm (hρ0 S₁ j₁ B₁ h₁) (hρ0 S₂ j₂ B₂ h₂) hMS₁ hB₁ hMS₂ hB₂
      σ hσ (ordPullback_eq_of_pluriformPullback_eq hv₁ hv₂ hd₁ hd₂ σ hσρ), hσ⟩
  · -- a branch of degree two: its deck involution is crepant
    intro S _ _ _ j BS _ hS h2
    obtain ⟨hv, hp, hc, hd⟩ := isNormalVariety_of_isAdjunctionStep hY hlift hdU hS
    obtain ⟨σ, hσ1, hσ2, hσV⟩ := exists_functionFieldEquiv_involution sV (j ≫ p ≫ r)
      (hs3 j) h2
    obtain ⟨MS, hMS, hBS⟩ := hadj S j BS hS
    have hσρ : pluriformPullback (j ≫ p ≫ sY) (j ≫ p ≫ sY) σ.toHom 2 m
        (pluriformPullback (j ≫ p ≫ sY) sV (ffHom sV (j ≫ p ≫ r) (hs3 j)) 2 m ω) =
        pluriformPullback (j ≫ p ≫ sY) sV (ffHom sV (j ≫ p ≫ r) (hs3 j)) 2 m ω := by
      haveI : LocallyOfFiniteType (j ≫ p ≫ sY) := hv.1.toLocallyOfFiniteType
      letI := functionFieldAlgebra sV
      letI := functionFieldAlgebra (j ≫ p ≫ sY)
      rw [pluriformPullback_comp hd hd hdV]
      have : (FunctionFieldEquiv.toHom _ _ σ).comp (ffHom sV (j ≫ p ≫ r) (hs3 j)) =
          ffHom sV (j ≫ p ≫ r) (hs3 j) := AlgHom.ext fun x => hσV x
      rw [this]
    haveI := hp
    haveI := hc
    exact ⟨σ, hσ1, hσ2, isCrepantBirationalMap_of_ordForm_add_eq_pullback sV hv hv hd hd
      (j ≫ p ≫ r) (j ≫ p ≫ r) hM hm (hρ0 S j BS hS) (hρ0 S j BS hS) hMS hBS hMS hBS
      σ hσV (ordPullback_eq_of_pluriformPullback_eq hv hv hd hd σ hσρ), hσV⟩

end MMP.Fourfold
