module

public import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple

/-!
# Crepant invariance of the pluriform floor, and ample divisors on stratum blow-ups

Two results on a smooth projective variety `X` over an algebraically closed field of
characteristic zero with an snc boundary `B` and coefficient-one part `T = B^{=1}`:

* the subspace `H⁰(X, m(K_X + B) - aT)` of rational `m`-canonical forms vanishing to order at least
  `a` along `T` is carried onto itself by every crepant birational self-map of `(X, B)`: a crepant
  self-map sends a coefficient-one prime to a zero place, whose centre lies on a component of `T`;
* for a composite `p : W → X` of blow-ups of strata of the coefficient-one boundary and a
  `p`-exceptional prime `E` whose centre lies in every centre of the sequence, there is an
  effective `p`-ample `ℚ`-divisor supported in `p⁻¹(Supp T)` with coefficient zero exactly at
  `E` among the boundary primes, so that `p^*A + δF` is ample for `A` ample and small `δ > 0`.

## Main results

* `MMP.Fourfold.pluriformPullback_mem_pluricanonicalSections_sub_coeffOnePart_iff`.
* `MMP.Fourfold.exists_hasRelativelyAmpleMultiple_coeff_eq_zero_of_stratumBlowups`.

## Implementation notes

The auxiliary lemmas of each proof live in the namespace `Proof_<tag>` named after its label.
`H⁰(X, mD - aT)` is `MMP.Mori.pluricanonicalSections` of `⌊mB⌋ - aT`
(`MMP.Fourfold.coeffOnePart`). The composites of stratum blow-ups are described as the smallest
class of pairs `(q : Y ⟶ X, y ∈ Y)` closed under isomorphisms and under blowing up a reduced
stratum containing `y`'s image; the inductive invariant of the second proof is a `q`-ample
effective boundary divisor vanishing exactly at the boundary primes through `y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Proof_lem_fourfold_pluriform_floor_vanishing_invariant

open MMP.Mori MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Threefold.Mori.Helpers MMP.Threefold.Mori.ModelIndependence

/-- A field map matching the divisorial valuations of `E` and `Γ` matches their orders. -/
private theorem ord_eq_of_divisorialValuation_eq {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (Γ : MMP.Mori.PrimeDivisor X) (E : MMP.Mori.PrimeDivisor Y)
    (φ : Y.functionField →+* X.functionField)
    (hval : ∀ y, Γ.divisorialValuation (φ y) = E.divisorialValuation y) (y : Y.functionField) :
    X.ord (φ y) Γ.genericPoint = Y.ord y E.genericPoint := by
  by_cases hy : y = 0
  · subst hy
    simp [Scheme.ord_zero]
  · have hey : φ y ≠ 0 := (map_ne_zero φ).mpr hy
    have h1 := hval y
    rw [Γ.divisorialValuation_eq_exp_neg_ord hey, E.divisorialValuation_eq_exp_neg_ord hy,
      WithZero.exp_inj] at h1
    omega

/-- A surjective field map matching the divisorial valuations of `E` and `Γ` restricts to a
bijection `𝒪_{Y,E} → 𝒪_{X,Γ}` of the local rings. -/
private theorem exists_localRing_bijective_of_divisorialValuation_eq {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (Γ : MMP.Mori.PrimeDivisor X) (E : MMP.Mori.PrimeDivisor Y)
    (φ : Y.functionField →+* X.functionField) (hφs : Function.Surjective φ)
    (hval : ∀ y, Γ.divisorialValuation (φ y) = E.divisorialValuation y) :
    ∃ ψ : E.localRing →+* Γ.localRing, Function.Bijective ψ ∧
      ∀ a, algebraMap Γ.localRing X.functionField (ψ a) =
        φ (algebraMap E.localRing Y.functionField a) := by
  refine exists_ringHom_bijective_of_range φ (fun a1 => ?_) (fun a2 => ?_)
  · have : E.divisorialValuation (algebraMap E.localRing Y.functionField a1) ≤ 1 :=
      (E.divisorialValuation_le_one_iff _).mpr ⟨a1, rfl⟩
    rw [← hval] at this
    exact (Γ.divisorialValuation_le_one_iff _).mp this
  · obtain ⟨y, hy⟩ := hφs (algebraMap Γ.localRing X.functionField a2)
    have : E.divisorialValuation y ≤ 1 := by
      rw [← hval, hy]
      exact (Γ.divisorialValuation_le_one_iff _).mpr ⟨a2, rfl⟩
    obtain ⟨a1, ha1⟩ := (E.divisorialValuation_le_one_iff _).mp this
    exact ⟨a1, by rw [ha1, hy]⟩

/-- **Orders of pulled-back forms along a valuation.** Let `σ` be a `k`-automorphism of `k(X)`,
`Γ` a prime divisor of `X` and `(Y, f, E)` a divisor over `X` whose valuation is `v_Γ ∘ σ`. Then
`ord_Γ(σ^* τ) = ord_E(f^* τ)`: the isomorphism `φ = σ ∘ (f^*)⁻¹ : k(Y) → k(X)` carries `v_E` to
`v_Γ`, hence `𝒪_{Y,E}` onto `𝒪_{X,Γ}`, and `σ^* = φ^* ∘ f^*`. -/
private theorem ordForm_pluriformPullback_eq_ordPullback {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    (σ : FunctionFieldEquiv sX sX) (Γ : MMP.Mori.PrimeDivisor X) (D : DivisorOver k sX)
    (hv : ∀ g : X.functionField, D.valuation g = Γ.divisorialValuation ((σ.toHom) g))
    {m : ℤ} (τ : RationalPluriForms sX n m) :
    Γ.ordForm (pluriformPullback sX sX σ.toHom n m τ) = D.ordPullback τ := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D.f ≫ sX) := D.isNormalVariety.1.toLocallyOfFiniteType
  let A := functionFieldAlgebra sX
  let AY := functionFieldAlgebra (D.f ≫ sX)
  let Af := functionFieldMapAlgebra D.f
  have hT1 := isScalarTower_functionFieldMap sX D.f
  have hb := D.isBirationalMorphism.functionFieldMap_bijective
  let F := RingEquiv.ofBijective _ hb
  let φ : D.Y.functionField →+* X.functionField := (σ.toHom).toRingHom.comp F.symm.toRingHom
  have hφ : ∀ g, φ (functionFieldMap D.f g) = (σ.toHom) g := fun g => by
    change (σ.toHom) (F.symm (F g)) = _
    rw [F.symm_apply_apply]
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨g, rfl⟩ := σ.surjective z
    exact ⟨functionFieldMap D.f g, hφ g⟩
  have hval : ∀ y : D.Y.functionField,
      Γ.divisorialValuation (φ y) = D.E.divisorialValuation y := by
    intro y
    obtain ⟨g, rfl⟩ := hb.2 y
    rw [hφ g, ← hv g]
    rfl
  have hord := ord_eq_of_divisorialValuation_eq Γ D.E φ hval
  obtain ⟨ψ, hψb, hψ⟩ := exists_localRing_bijective_of_divisorialValuation_eq Γ D.E φ hφs hval
  have hd : (Algebra.trdeg k X.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have htr : Algebra.trdeg k X.functionField = Algebra.trdeg k D.Y.functionField :=
    trdeg_functionField_eq_of_bijective sX D.f hb
  have hd1 : (Algebra.trdeg k D.Y.functionField).toNat = n := by rwa [← htr]
  letI := stalkAlgebra (D.f ≫ sX) D.E.genericPoint
  letI := stalkAlgebra sX Γ.genericPoint
  haveI := isScalarTower_stalk_functionField (D.f ≫ sX) D.E.genericPoint
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  letI Aφ : Algebra D.Y.functionField X.functionField := φ.toAlgebra
  have hTφ : IsScalarTower k D.Y.functionField X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change algebraMap k X.functionField c = φ (algebraMap k D.Y.functionField c)
    rw [IsScalarTower.algebraMap_apply k X.functionField D.Y.functionField c]
    change _ = φ (functionFieldMap D.f (algebraMap k X.functionField c))
    rw [hφ]
    exact ((σ.toHom).commutes c).symm
  letI : Algebra D.E.localRing Γ.localRing := ψ.toAlgebra
  letI : Algebra D.E.localRing X.functionField :=
    ((algebraMap Γ.localRing X.functionField).comp ψ).toAlgebra
  have hS1 : IsScalarTower k D.E.localRing Γ.localRing := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    apply IsFractionRing.injective Γ.localRing X.functionField
    change _ = algebraMap Γ.localRing X.functionField (ψ (algebraMap k D.E.localRing c))
    rw [hψ, ← IsScalarTower.algebraMap_apply k D.E.localRing D.Y.functionField c,
      ← IsScalarTower.algebraMap_apply k Γ.localRing X.functionField c]
    exact IsScalarTower.algebraMap_apply k D.Y.functionField X.functionField c
  have hS2 : IsScalarTower D.E.localRing Γ.localRing X.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hS3 : IsScalarTower D.E.localRing D.Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq hψ
  have hS4 : IsScalarTower k D.E.localRing X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = algebraMap Γ.localRing X.functionField (ψ (algebraMap k D.E.localRing c))
    rw [IsScalarTower.algebraMap_apply k Γ.localRing X.functionField c,
      IsScalarTower.algebraMap_apply k D.E.localRing Γ.localRing c]
    rfl
  have : Algebra.EssFiniteType k D.Y.functionField := essFiniteType_functionField (sX := D.f ≫ sX)
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX D.f hb hd
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator (k := k) (K := D.Y.functionField)
    (K' := X.functionField) htr.symm hd1
  have hω0φ : IsPullbackGenerator X.functionField
      (topFormsMap k X.functionField D.Y.functionField n ω0) :=
    IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  obtain ⟨σE, hσE, h0σE⟩ := D.E.exists_topForms_generator (sX := D.f ≫ sX) hd1
  have hωT : IsPullbackGenerator X.functionField
      (topFormsMap k D.E.localRing D.Y.functionField n σE) :=
    IsPullbackGenerator.of_span hω1 (span_singleton_topFormsMap (nonZeroDivisors _) hσE) h0σE
  have key := ordAt_pullbackForms_eq (k := k) (K := D.Y.functionField) (K' := X.functionField)
    (A := D.E.localRing) (A' := Γ.localRing) (d := n) (m := m) hψb
    (v := fun y => D.Y.ord y D.E.genericPoint) (v' := fun y => X.ord y Γ.genericPoint)
    (fun x y hx hy => D.E.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => D.E.ord_algebraMap_of_isUnit ha)
    (fun x y hx hy => Γ.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => Γ.ord_algebraMap_of_isUnit ha)
    hord hσE hωT (pullbackForms (K' := D.Y.functionField) m τ)
  let Aσ : Algebra X.functionField X.functionField := (σ.toHom).toRingHom.toAlgebra
  have tσ : @IsScalarTower k X.functionField X.functionField _ Aσ.toSMul _ := by
    letI := Aσ
    exact IsScalarTower.of_algebraMap_eq fun c => ((σ.toHom).commutes c).symm
  have t3 : @IsScalarTower X.functionField D.Y.functionField X.functionField Af.toSMul
      Aφ.toSMul Aσ.toSMul :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ Af Aφ Aσ fun g => (hφ g).symm
  have hcomp := @pullbackForms_comp k _ n m X.functionField D.Y.functionField
    X.functionField _ _ _ A AY A Af Aφ Aσ hT1 hTφ tσ t3 ω0 hω0 hω0φ τ
  calc Γ.ordForm (pluriformPullback sX sX σ.toHom n m τ)
      = ordAt Γ.localRing (fun y => X.ord y Γ.genericPoint)
          (@pullbackForms k _ X.functionField X.functionField _ _ A A Aσ tσ n m τ) := rfl
    _ = ordAt Γ.localRing (fun y => X.ord y Γ.genericPoint)
          (pullbackForms (K' := X.functionField) m
            (pullbackForms (K' := D.Y.functionField) m τ)) := by rw [hcomp]
    _ = D.ordPullback τ := key

/-- A variety of dimension `n` with an exceptional divisor over it has `n ≥ 2`. -/
private theorem two_le_of_isExceptional {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {D : DivisorOver k sX} (hD : D.IsExceptional) : 2 ≤ n := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    (D.f D.E.genericPoint)
  rw [hn] at h
  have h0 : 0 ≤ topologicalKrullDim (closure {D.f D.E.genericPoint} : Set X) :=
    Order.krullDim_nonneg_iff.mpr ⟨⟨closure {⟨_, subset_closure rfl⟩},
      isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have : ((Order.coheight (D.f D.E.genericPoint) : ℕ∞) : WithBot ℕ∞) ≤ n :=
    h ▸ le_add_of_nonneg_left h0
  exact_mod_cast ((MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX D).mp hD).trans
    (WithBot.coe_le_coe.mp this)

/-- **The pull-back of a prime divisor is positive along divisors over it.** If `G` is a Cartier
prime divisor of `Y` and `E` a prime divisor of `W` with `g(η_E) ∈ G`, then `g^*G` has
coefficient at least `1` along `E`. -/
private theorem one_le_coeff_of_isPullback {W Y : Scheme.{u}} [IsLocallyNoetherian W]
    [IsNormal W] [IsLocallyNoetherian Y] [IsNormal Y] {g : W ⟶ Y} (G : MMP.Mori.PrimeDivisor Y)
    (hGc : Divisor.IsCartier (Finsupp.single G (1 : ℤ) : Divisor Y))
    {hB : ∀ Z : irreducibleComponents W,
      g (componentGenericPoint W Z) ∉ DivisorWithCoeffs.supp (Finsupp.single G (1 : ℤ) : Divisor Y)}
    {B : Divisor W} (h : Divisor.IsPullback g (Finsupp.single G (1 : ℤ)) hB B)
    (E : MMP.Mori.PrimeDivisor W) (hE : g E.genericPoint ∈ G.support) : 1 ≤ B.coeff E := by
  classical
  have heff : ∀ P : MMP.Mori.PrimeDivisor Y,
      0 ≤ DivisorWithCoeffs.coeff (Finsupp.single G (1 : ℤ) : Divisor Y) P :=
    fun P => by
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
      split_ifs <;> simp
  have h0 : 0 ≤ B.coeff E :=
    MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤) hGc (fun P _ => heff P) h E
      ((E.genericPoint_mem_iff _).mp trivial)
  have hG : DivisorWithCoeffs.coeff (Finsupp.single G (1 : ℤ) : Divisor Y) G ≠ 0 := by
    simp [DivisorWithCoeffs.coeff_apply]
  have hmem : E.genericPoint ∈ (B.supp : Set W) := by
    rw [MMP.Flips.supp_eq_preimage_supp_of_isPullback hGc heff h]
    exact DivisorWithCoeffs.support_subset_supp hG hE
  obtain ⟨E₂, hE₂, hηE₂⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
  obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hηE₂
  omega

/-- **Hartogs along a divisor over `X`.** A rational function with nonnegative order along every
prime divisor through the centre of a divisor `(Y, f, E)` over `X` has nonnegative order along
`E` after pull-back. -/
private theorem ord_functionFieldMap_nonneg_of_forall {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (D : DivisorOver k sX) {g : X.functionField} (hg : g ≠ 0)
    (h : ∀ Γ : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support →
      0 ≤ X.ord g Γ.genericPoint) :
    haveI := D.isIntegral
    haveI := D.isLocallyNoetherian
    haveI := D.isDominant
    0 ≤ D.Y.ord (functionFieldMap D.f g) D.E.genericPoint := by
  obtain ⟨r, hr⟩ := exists_algebraMap_stalk_eq_of_forall_ord_nonneg _ hg h
  exact ord_functionFieldMap_nonneg D hg r hr

open Classical in
/-- **A local equation of a prime divisor through the centre.** On a smooth variety, a prime
divisor `P` through the centre `x` of a divisor `(Y, f, E)` over `X` has a local equation `t`
near `x` (`ord_Γ t = [Γ = P]` for the prime divisors `Γ` meeting a neighbourhood of `x`), and
`f^* t` vanishes along `E`. -/
private theorem exists_localEquation_one_le_ord {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) (P : MMP.Mori.PrimeDivisor X)
    (D : DivisorOver k sX) (hx : D.f D.E.genericPoint ∈ P.support) :
    haveI := D.isIntegral
    haveI := D.isLocallyNoetherian
    haveI := D.isDominant
    ∃ (U : X.Opens) (t : X.functionField), D.f D.E.genericPoint ∈ U ∧ t ≠ 0 ∧
      (∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ U).Nonempty →
        X.ord t Γ.genericPoint = if P = Γ then 1 else 0) ∧
      1 ≤ D.Y.ord (functionFieldMap D.f t) D.E.genericPoint := by
  classical
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have : CompactSpace X := hX.1.toQuasiCompact.compactSpace_of_compactSpace
  have : CompactSpace D.Y := D.isNormalVariety.1.toQuasiCompact.compactSpace_of_compactSpace
  have hC := MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm P
  obtain ⟨C', hC'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f hC
  have h1 := one_le_coeff_of_isPullback P hC hC' D.E hx
  obtain ⟨U, hxU, φ, hφ⟩ := hC (D.f D.E.genericPoint)
  have hcoeff := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hC' hφ D.E hxU P.component
  set t := evalFF P.component (φ : RationalFunctions X) with ht
  have ht0 : t ≠ 0 := (φ.isUnit.map (evalFF P.component)).ne_zero
  refine ⟨U, t, hxU, ht0, fun Γ hΓ => ?_, hcoeff ▸ h1⟩
  have e1 := hφ Γ hΓ
  rw [ord_eq_scheme_ord] at e1
  have hcomp : Γ.component = P.component :=
    Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
  rw [hcomp] at e1
  rw [← e1, DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]

/-- An exceptional divisor of discrepancy `-1` over an snc subboundary pair has coefficient one
along every component of the boundary through its centre. -/
private theorem coeff_eq_one_of_isDiscrepancy_eq_neg_one {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {B : QDivisor X}
    (hXB : IsSNCSubboundaryPair sX B) (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) (hn2 : 2 ≤ n) (D : DivisorOver k sX)
    (hE : D.IsExceptional) {a : ℚ} (hdisc : IsDiscrepancy sX n K B D a) (ha : a = -1)
    {G : MMP.Mori.PrimeDivisor X} (hG0 : B.coeff G ≠ 0)
    (hxG : D.f D.E.genericPoint ∈ G.support) : B.coeff G = 1 := by
  classical
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : CompactSpace X := hX.1.toQuasiCompact.compactSpace_of_compactSpace
  have : CompactSpace D.Y := D.isNormalVariety.1.toQuasiCompact.compactSpace_of_compactSpace
  have hcart := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  set S : Finset (MMP.Mori.PrimeDivisor X) := B.support with hS
  have hsupp : B.support = (∑ G ∈ S, Finsupp.single G (1 : ℤ) : Divisor X).support := by
    ext G'
    simp [Finsupp.finset_sum_apply, Finsupp.single_apply, hS]
  have hsnc : DivisorWithCoeffs.IsSNC sX (∑ G ∈ S, Finsupp.single G (1 : ℤ) : Divisor X) :=
    (DivisorWithCoeffs.isSNC_iff_of_support_eq hsupp).mp hXB.isSNC
  obtain ⟨hB, hmain⟩ := MMP.Mori.sum_le_add_one_of_isSNC sX hX hsm hn2 hK S subset_rfl hsnc
    (fun G _ => hXB.coeff_le_one G) D hE hdisc
  let BB : MMP.Mori.PrimeDivisor X → Divisor D.Y := fun G =>
    if hG : G ∈ S then Divisor.pullback _ (hcart _) (hB G hG) else 0
  have hBpb : ∀ (G : MMP.Mori.PrimeDivisor X) (hG : G ∈ S),
      Divisor.IsPullback D.f (Finsupp.single G (1 : ℤ)) (hB G hG) (BB G) := fun G hG => by
    simp only [BB, dif_pos hG]
    exact Divisor.isPullback_pullback _ _
  obtain ⟨h0, hsum⟩ := hmain BB hBpb
  have hGS : G ∈ S := Finsupp.mem_support_iff.mpr hG0
  have h1G : 1 ≤ (BB G).coeff D.E :=
    one_le_coeff_of_isPullback G (hcart _) (hBpb G hGS) D.E hxG
  have hle := Finset.single_le_sum
    (f := fun G => (1 - B.coeff G) * ((BB G).coeff D.E : ℚ))
    (fun G hG => mul_nonneg (sub_nonneg.2 (hXB.coeff_le_one G)) (by exact_mod_cast h0 G hG))
    hGS
  have hb1 := hXB.coeff_le_one G
  have h1G' : (1 : ℚ) ≤ (BB G).coeff D.E := by exact_mod_cast h1G
  nlinarith

/-- On a smooth variety, an exceptional divisor of discrepancy `-1` has its centre on some
component of the boundary: away from the boundary the discrepancy is at least one. -/
private theorem exists_coeff_ne_zero_of_isDiscrepancy_eq_neg_one {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {B : QDivisor X}
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (hn2 : 2 ≤ n) {m : ℕ} (hm : 0 < m) (D : DivisorOver k sX)
    (hE : D.IsExceptional) {U : X.Opens} (hxU : D.f D.E.genericPoint ∈ U)
    {τ0 : RationalPluriForms sX n m} (hτ0 : GeneratesOn B m U τ0) {a : ℚ}
    (hma : (m : ℚ) * a = D.ordPullback τ0) (ha : a = -1) :
    ∃ G : MMP.Mori.PrimeDivisor X, B.coeff G ≠ 0 ∧ D.f D.E.genericPoint ∈ G.support := by
  classical
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : CompactSpace X := hX.1.toQuasiCompact.compactSpace_of_compactSpace
  have : CompactSpace D.Y := D.isNormalVariety.1.toQuasiCompact.compactSpace_of_compactSpace
  have hcart := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  by_contra hx
  push Not at hx
  have hxs : D.f D.E.genericPoint ∉ B.supp := by
    rw [DivisorWithCoeffs.mem_supp_iff]
    exact fun ⟨G, hG, hxG⟩ => hx G hG hxG
  let U' : X.Opens := U ⊓ B.supp.compl
  have hgen0 : GeneratesOn (0 : QDivisor X) m U' τ0 := by
    refine ⟨hτ0.1, fun Γ hΓ => ?_⟩
    have e := hτ0.2 Γ (hΓ.mono fun y hy => ⟨hy.1, hy.2.1⟩)
    have hb : B.coeff Γ = 0 := by
      by_contra hb
      obtain ⟨y, hyΓ, hyU'⟩ := hΓ
      exact hyU'.2 (DivisorWithCoeffs.mem_supp_iff.mpr ⟨Γ, hb, hyΓ⟩)
    rw [hb, mul_zero] at e
    simpa using e
  have hmK0 : ((m : ℤ) • (Divisor.toQDivisor K + 0)).IsCartierDivisor := by
    rw [add_zero, ← map_zsmul, QDivisor.isCartierDivisor_toQDivisor]
    exact hcart _
  have hdisc0 : IsDiscrepancy sX n K 0 D a :=
    ⟨hX, hK, m, hm, hmK0, U', ⟨hxU, hxs⟩, τ0, hgen0, hma⟩
  have hle := discrep_le hE hdisc0
  rw [MMP.Mori.discrep_eq_of_isSNC sX hX hsm hn2 hK (Δ := 0) ∅ (by simp)
    (by have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
        have : Smooth sX := (isSmoothScheme_iff sX).mp hsm
        simpa using DivisorWithCoeffs.isSNC_zero (R := ℤ) sX)
    (by simp), ha] at hle
  have h2 : ((1 : ℝ) : EReal) ≤ ((-1 : ℝ) : EReal) := by simpa using hle
  exact absurd (EReal.coe_le_coe_iff.mp h2) (by norm_num)

/-- A non-exceptional divisor of log discrepancy zero over a pair is a prime divisor of
coefficient one containing its centre. -/
private theorem exists_coeff_eq_one_of_not_isExceptional {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {B : QDivisor X} (hX : IsNormalVariety k sX)
    (hP : MMP.Mori.IsPair sX B) {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (D : DivisorOver k sX)
    (hD : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D 0)
    (hE : ¬D.IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, B.coeff P = 1 ∧ D.f D.E.genericPoint ∈ P.support := by
  classical
  obtain ⟨P, hPv⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hE
  refine ⟨P, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
      (DivisorOver.ofPrimeDivisor k hX P)
    have hc' := hc.eq_neg_coeff_of_ofPrimeDivisor hX
    have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
      (show IsProper (𝟙 X) by infer_instance)
    have h := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD hlog hPv
    rw [hc'] at h
    have : ((B.coeff P : ℚ) : ℝ) = 1 := by push_cast at h ⊢; linarith
    exact_mod_cast this
  · rw [MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hPv]
    change P.genericPoint ∈ P.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- **Zero places of an snc subboundary have centre on its coefficient-one part.** Let `X` be a
smooth projective variety, `B` an snc `ℚ`-divisor with coefficients at most one and `m(K_X + B)`
Cartier. A divisor `(Y, f, E)` over `X` with log discrepancy `a(E, X, B) = 0` has its centre on a
prime divisor `P` with `coeff_P B = 1`. If `E` is not exceptional it is a prime divisor `P` of
`X`, of log discrepancy `1 - coeff_P B`. If it is exceptional, its Kollár–Mori discrepancy is
`-1`; the snc bound `a(E, X, B) + 1 ≥ ∑_G (1 - coeff_G B) ord_E G` forces every component `G`
of `B` through the centre to have coefficient one, and if no component passes through the centre
then near it `B = 0`, where the discrepancy of the smooth `X` is at least one. -/
private theorem exists_coeff_eq_one_of_isLogDiscrepancy_eq_zero {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {B : QDivisor X}
    (hXB : IsSNCSubboundaryPair sX B) {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {m : ℕ}
    (hm : 0 < m) (hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor)
    (D : DivisorOver k sX) {n' : ℕ}
    (hD : MMP.Intersection.IsLogDiscrepancy sX n' (QDivisor.toRDivisor B) D 0) :
    ∃ P : MMP.Mori.PrimeDivisor X, B.coeff P = 1 ∧ D.f D.E.genericPoint ∈ P.support := by
  classical
  have hX : IsNormalVariety k sX := ⟨hXB.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hsm := hXB.isSmoothScheme
  have hn := hK.topologicalKrullDim_eq
  have hP : MMP.Mori.IsPair sX B := ⟨hX, n, K, hK, ⟨m, by exact_mod_cast hm.ne', hmD⟩⟩
  obtain rfl : n' = n := by
    exact_mod_cast
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hD).symm.trans hn
  by_cases hE : D.IsExceptional
  · have hn2 := two_le_of_isExceptional hX hn hE
    have := D.isLocallyNoetherian
    have := D.isNormal
    have : CompactSpace X := hX.1.toQuasiCompact.compactSpace_of_compactSpace
    have : CompactSpace D.Y := D.isNormalVariety.1.toQuasiCompact.compactSpace_of_compactSpace
    obtain ⟨-, U, hxU, τ0, hτ0⟩ :=
      MMP.Positivity.IsPair.exists_generatesOn hP hK hmD (D.f D.E.genericPoint)
    set a' : ℚ := (D.ordPullback τ0 : ℚ) / m with ha'
    have hma : (m : ℚ) * a' = D.ordPullback τ0 := by
      rw [ha']; field_simp
    have hdisc : IsDiscrepancy sX n' K B D a' := ⟨hX, hK, m, hm, hmD, U, hxU, τ0, hτ0, hma⟩
    have h1 := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hdisc hD
    have ha1 : a' = -1 := by
      have : ((a' : ℚ) : ℝ) = -1 := by linarith
      exact_mod_cast this
    obtain ⟨G, hG0, hxG⟩ :=
      exists_coeff_ne_zero_of_isDiscrepancy_eq_neg_one hX hsm hK hn2 hm D hE hxU hτ0 hma ha1
    exact ⟨G, coeff_eq_one_of_isDiscrepancy_eq_neg_one hXB hX hsm hK hn2 D hE hdisc ha1 hG0 hxG,
      hxG⟩
  · exact exists_coeff_eq_one_of_not_isExceptional hX hP hK D hD hE

/-- The coefficients of `⌊mB⌋ - a T` when `mB` is the divisor `D₀`. -/
private theorem coeff_roundDown_sub_coeffOnePart {X : Scheme.{u}} {B : QDivisor X} {m : ℕ}
    {D₀ : Divisor X} (hD₀ : Divisor.toQDivisor D₀ = (m : ℤ) • B) (a : ℤ)
    (P : MMP.Mori.PrimeDivisor X) :
    (DivisorWithCoeffs.roundDown ((m : ℤ) • B) - a • coeffOnePart B).coeff P =
        D₀.coeff P - a * (if B.coeff P = 1 then 1 else 0) ∧
      ((D₀.coeff P : ℤ) : ℚ) = m * B.coeff P := by
  have h : ((D₀.coeff P : ℤ) : ℚ) = m * B.coeff P := by
    simpa using congrArg (fun D : QDivisor X => D.coeff P) hD₀
  refine ⟨?_, h⟩
  rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_roundDown]
  have e1 : DivisorWithCoeffs.coeff ((m : ℤ) • B) P = ((D₀.coeff P : ℤ) : ℚ) := by
    rw [← hD₀]; simp
  have e2 : DivisorWithCoeffs.coeff (a • coeffOnePart B) P = a * (coeffOnePart B).coeff P := by
    simp [DivisorWithCoeffs.coeff_apply]
  rw [e1, Int.floor_intCast, e2, coeff_coeffOnePart]

/-- **Pull-back by a crepant self-map preserves the vanishing along `T`.** -/
private theorem pluriformPullback_mem_of_mem {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {B : QDivisor X} (hXB : IsSNCSubboundaryPair sX B)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {m : ℕ} (hm : 0 < m)
    (hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) {a : ℤ} (ha : 1 ≤ a)
    {σ : FunctionFieldEquiv sX sX} (hσ : σ ∈ crepantBirationalAutomorphisms sX B)
    {τ : RationalPluriForms sX n m}
    (hτ : τ ∈ pluricanonicalSections sX n m
      (DivisorWithCoeffs.roundDown ((m : ℤ) • B) - a • coeffOnePart B) ⊤) :
    pluriformPullback sX sX σ.toHom n m τ ∈ pluricanonicalSections sX n m
      (DivisorWithCoeffs.roundDown ((m : ℤ) • B) - a • coeffOnePart B) ⊤ := by
  classical
  have hX : IsNormalVariety k sX := ⟨hXB.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hsm := hXB.isSmoothScheme
  have hn := hK.topologicalKrullDim_eq
  have hP : MMP.Mori.IsPair sX B := ⟨hX, n, K, hK, ⟨m, by exact_mod_cast hm.ne', hmD⟩⟩
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  rw [mem_pluricanonicalSections_of_ne_bot top_ne_bot] at hτ ⊢
  intro Γ _ hτ'
  have hτne : τ ≠ 0 := fun h => hτ' (by rw [h, map_zero])
  -- the log discrepancy of `Γ`, transported by `σ`
  set DΓ := DivisorOver.ofPrimeDivisor k hX Γ
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK DΓ
  have hc' : c = -B.coeff Γ := hc.eq_neg_coeff_of_ofPrimeDivisor hX
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (show IsProper (𝟙 X) by infer_instance)
  have hσ' : IsCrepantBirationalMap sX sX B B σ := hσ
  obtain ⟨n', D, hDv, hDlog⟩ := (hσ' DΓ.valuation (1 + c)).mp ⟨n, DΓ, rfl, hlog⟩
  obtain rfl : n' = n := by
    exact_mod_cast
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hDlog).symm.trans hn
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have hv : ∀ g : X.functionField, D.valuation g = Γ.divisorialValuation ((σ.toHom) g) := by
    intro g
    rw [hDv]
    change Γ.divisorialValuation (functionFieldMap (𝟙 X) _) = _
    rw [functionFieldMap_id_apply]
    rfl
  have htrans := ordForm_pluriformPullback_eq_ordPullback hX hn σ Γ D hv τ
  -- a local generator at the centre of `D`
  set x := D.f D.E.genericPoint
  obtain ⟨⟨D₀, hD₀⟩, U, hxU, τ0, hτ0⟩ := MMP.Positivity.IsPair.exists_generatesOn hP hK hmD x
  have hdisc : IsDiscrepancy sX n' K B D ((D.ordPullback τ0 : ℚ) / m) :=
    ⟨hX, hK, m, hm, hmD, U, hxU, τ0, hτ0, by field_simp⟩
  have h1 := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hdisc hDlog
  have hτ0ord : (D.ordPullback τ0 : ℚ) = -(m * B.coeff Γ) := by
    have h2 : ((c : ℚ) : ℝ) = (((D.ordPullback τ0 : ℚ) / m : ℚ) : ℝ) := by linarith
    have h3 : c = (D.ordPullback τ0 : ℚ) / m := by exact_mod_cast h2
    rw [hc'] at h3
    have hm0 : (m : ℚ) ≠ 0 := by positivity
    field_simp at h3
    linarith
  -- `τ = g • τ0`
  let A := functionFieldAlgebra sX
  obtain ⟨bas, N, hN⟩ := D.exists_ordPullback_eq hX hn
  set cτ := (ZTensorPower.basis bas m).repr τ () with hcτ
  set c0 := (ZTensorPower.basis bas m).repr τ0 () with hc0
  have hcτ0 : cτ ≠ 0 := repr_ne_zero_of_ne_zero bas hτne
  have hc00 : c0 ≠ 0 := repr_ne_zero_of_ne_zero bas hτ0.1
  set g := cτ / c0 with hg
  have hg0 : g ≠ 0 := div_ne_zero hcτ0 hc00
  have hcτg : cτ = g * c0 := by rw [hg, div_mul_cancel₀ _ hc00]
  have hY : D.ordPullback τ =
      D.Y.ord (functionFieldMap D.f g) D.E.genericPoint + D.ordPullback τ0 := by
    rw [hN m τ hτne, hN m τ0 hτ0.1, ← hcτ, ← hc0, hcτg, map_mul,
      Scheme.ord_mul ((map_ne_zero _).mpr hg0) ((map_ne_zero _).mpr hc00)]
    ring
  have hXg : ∀ Γ' : MMP.Mori.PrimeDivisor X,
      Γ'.ordForm τ = X.ord g Γ'.genericPoint + Γ'.ordForm τ0 := by
    intro Γ'
    obtain ⟨N', hN'⟩ := Γ'.exists_ordForm_eq_ord_add_mul hd bas
    rw [hN' m τ hτne, hN' m τ0 hτ0.1, ← hcτ, ← hc0, hcτg, Scheme.ord_mul hg0 hc00]
    ring
  -- the order bound for `g` near `x`
  have hgx : ∀ Γ' : MMP.Mori.PrimeDivisor X, x ∈ Γ'.support →
      a * (if B.coeff Γ' = 1 then 1 else 0) ≤ X.ord g Γ'.genericPoint := by
    intro Γ' hxΓ'
    have h1 := hτ Γ' ⟨x, hxΓ', trivial⟩ hτne
    have h2 := hτ0.2 Γ' ⟨x, hxΓ', hxU⟩
    obtain ⟨hW, hD₀c⟩ := coeff_roundDown_sub_coeffOnePart hD₀ a Γ'
    rw [hW] at h1
    rw [← hD₀c] at h2
    have h3 : Γ'.ordForm τ0 = -D₀.coeff Γ' :=
      by exact_mod_cast (by push_cast; linarith : (Γ'.ordForm τ0 : ℚ) = ((-D₀.coeff Γ' : ℤ) : ℚ))
    rw [hXg Γ', h3] at h1
    linarith
  -- the goal
  obtain ⟨hWΓ, hD₀Γ⟩ := coeff_roundDown_sub_coeffOnePart hD₀ a Γ
  rw [htrans, hWΓ, hY]
  have hτ0D : D.ordPullback τ0 = -D₀.coeff Γ :=
    by exact_mod_cast (by push_cast; linarith : (D.ordPullback τ0 : ℚ) = ((-D₀.coeff Γ : ℤ) : ℚ))
  rw [hτ0D]
  by_cases hb1 : B.coeff Γ = 1
  · rw [if_pos hb1]
    have hDlog0 : MMP.Intersection.IsLogDiscrepancy sX n' (QDivisor.toRDivisor B) D 0 := by
      have : (1 : ℝ) + (c : ℝ) = 0 := by rw [hc', hb1]; norm_num
      rwa [← this]
    obtain ⟨P, hP1, hxP⟩ :=
      exists_coeff_eq_one_of_isLogDiscrepancy_eq_zero hXB hK hm hmD D hDlog0
    obtain ⟨U₂, t, hxU₂, ht0, htord, ht1⟩ :=
      exists_localEquation_one_le_ord hX hsm P D hxP
    have hG0 : g * t ^ (-a) ≠ 0 := mul_ne_zero hg0 (zpow_ne_zero _ ht0)
    have hG := ord_functionFieldMap_nonneg_of_forall D hG0 fun Γ' hxΓ' => by
      rw [Scheme.ord_mul hg0 (zpow_ne_zero _ ht0), ord_zpow _ ht0,
        htord Γ' ⟨x, hxΓ', hxU₂⟩]
      have := hgx Γ' hxΓ'
      by_cases hPΓ : P = Γ'
      · subst hPΓ
        rw [if_pos hP1] at this
        rw [if_pos rfl]
        linarith
      · rw [if_neg hPΓ]
        split_ifs at this <;> linarith
    rw [map_mul, map_zpow₀, Scheme.ord_mul ((map_ne_zero _).mpr hg0)
      (zpow_ne_zero _ ((map_ne_zero _).mpr ht0)), ord_zpow _ ((map_ne_zero _).mpr ht0)] at hG
    nlinarith
  · rw [if_neg hb1]
    have hG := ord_functionFieldMap_nonneg_of_forall D hg0 fun Γ' hxΓ' => by
      have := hgx Γ' hxΓ'
      split_ifs at this <;> linarith
    linarith

/-- Pull-back of forms along `k`-automorphisms of the function field is contravariantly
functorial: `σ^* ∘ τ^* = (σ τ)^*`. -/
private theorem pluriformPullback_pluriformPullback {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] {d : ℕ}
    (hX : topologicalKrullDim X = d) (m : ℤ) (σ τ : FunctionFieldEquiv sX sX)
    (x : RationalPluriForms sX d m) :
    pluriformPullback sX sX σ.toHom d m (pluriformPullback sX sX τ.toHom d m x) =
      pluriformPullback sX sX (σ * τ).toHom d m x := by
  let A := functionFieldAlgebra sX
  have := essFiniteType_functionField (sX := sX)
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hX
  let Aτ : Algebra X.functionField X.functionField := (τ.toHom).toRingHom.toAlgebra
  let Aσ : Algebra X.functionField X.functionField := (σ.toHom).toRingHom.toAlgebra
  let Aστ : Algebra X.functionField X.functionField := ((σ * τ).toHom).toRingHom.toAlgebra
  have tτ : @IsScalarTower k X.functionField X.functionField _ Aτ.toSMul _ := by
    letI := Aτ
    exact IsScalarTower.of_algebraMap_eq fun c => ((τ.toHom).commutes c).symm
  have tσ : @IsScalarTower k X.functionField X.functionField _ Aσ.toSMul _ := by
    letI := Aσ
    exact IsScalarTower.of_algebraMap_eq fun c => ((σ.toHom).commutes c).symm
  have tστ : @IsScalarTower k X.functionField X.functionField _ Aστ.toSMul _ := by
    letI := Aστ
    exact IsScalarTower.of_algebraMap_eq fun c => (((σ * τ).toHom).commutes c).symm
  have t3 : @IsScalarTower X.functionField X.functionField X.functionField Aτ.toSMul Aσ.toSMul
      Aστ.toSMul := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ Aτ Aσ Aστ fun c => rfl
  obtain ⟨ω, hω⟩ := @exists_isPullbackGenerator k X.functionField X.functionField _ _ _ _ A A Aτ
    tτ _ rfl d hd
  obtain ⟨ω', hω'⟩ := @exists_isPullbackGenerator k X.functionField X.functionField _ _ _ _ A A Aσ
    tσ _ rfl d hd
  have h2 := @IsPullbackGenerator.of_span k _ d X.functionField
    X.functionField _ _ A A Aσ tσ ω' _ hω' hω.2.1 hω.2.2
  exact @pullbackForms_comp k _ d m X.functionField X.functionField
    X.functionField _ _ _ A A A Aτ Aσ Aστ tτ tσ tστ t3 ω hω h2 x

/-- Pull-back along the identity of the function field is the identity. -/
private theorem pluriformPullback_one {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] {d : ℕ}
    (hX : topologicalKrullDim X = d) (m : ℤ) (x : RationalPluriForms sX d m) :
    pluriformPullback sX sX (1 : FunctionFieldEquiv sX sX).toHom d m x = x := by
  let A := functionFieldAlgebra sX
  have := essFiniteType_functionField (sX := sX)
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hX
  let A1 : Algebra X.functionField X.functionField :=
    ((1 : FunctionFieldEquiv sX sX).toHom).toRingHom.toAlgebra
  have t1 : @IsScalarTower k X.functionField X.functionField _ A1.toSMul _ := by
    letI := A1
    exact IsScalarTower.of_algebraMap_eq fun c =>
      (((1 : FunctionFieldEquiv sX sX).toHom).commutes c).symm
  obtain ⟨ω, hω⟩ := @exists_isPullbackGenerator k X.functionField X.functionField _ _ _ _ A A A1
    t1 _ rfl d hd
  exact pullbackForms_eq_self (k := k) ((1 : FunctionFieldEquiv sX sX).toHom).toRingHom
    (fun _ => rfl) hω.1 hω.ne_zero m x

end MMP.Proof_lem_fourfold_pluriform_floor_vanishing_invariant

namespace MMP.Fourfold

open MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Proof_lem_fourfold_pluriform_floor_vanishing_invariant

/-- **Vanishing along the coefficient-one boundary is crepant-invariant.** Let `X` be a smooth
projective variety over `k`, `B` an snc `ℚ`-divisor with all coefficients at most one
(`MMP.Fourfold.IsSNCSubboundaryPair`), `K` a canonical divisor, and `T = B^{=1}`
(`MMP.Fourfold.coeffOnePart`). Let `m > 0` with `m(K + B)` Cartier and `a ≥ 1`. For every crepant
birational self-map `σ` of `(X, B)` (`MMP.Fourfold.crepantBirationalAutomorphisms`) and every
rational `m`-canonical form `τ`, the pull-back `σ^* τ` lies in `H⁰(X, m(K + B) - aT)` if and only
if `τ` does. -/
@[mmp "lem_fourfold_pluriform_floor_vanishing_invariant"]
public theorem pluriformPullback_mem_pluricanonicalSections_sub_coeffOnePart_iff
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {B : QDivisor X} (hXB : IsSNCSubboundaryPair sX B)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {m : ℕ} (hm : 0 < m)
    (hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) {a : ℤ} (ha : 1 ≤ a)
    {σ : FunctionFieldEquiv sX sX} (hσ : σ ∈ crepantBirationalAutomorphisms sX B)
    (τ : RationalPluriForms sX n m) :
    pluriformPullback sX sX σ.toHom n m τ ∈
        pluricanonicalSections sX n m
          (DivisorWithCoeffs.roundDown ((m : ℤ) • B) - a • coeffOnePart B) ⊤ ↔
      τ ∈ pluricanonicalSections sX n m
          (DivisorWithCoeffs.roundDown ((m : ℤ) • B) - a • coeffOnePart B) ⊤ := by
  have hX : IsNormalVariety k sX := ⟨hXB.isProjectiveVariety.toIsVariety, inferInstance⟩
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hn := hK.topologicalKrullDim_eq
  refine ⟨fun h => ?_, pluriformPullback_mem_of_mem hXB hK hm hmD ha hσ⟩
  have h2 := pluriformPullback_mem_of_mem hXB hK hm hmD ha (inv_mem hσ) h
  rwa [pluriformPullback_pluriformPullback sX hn, inv_mul_cancel,
    pluriformPullback_one sX hn] at h2

end MMP.Fourfold

namespace MMP.Proof_lem_fourfold_stratum_blowup_ample_off_one_prime

open MMP MMP.Mori MMP.Resolution TopologicalSpace

/-! ### Relative ampleness of Cartier divisors -/

section Ample

open RingedSpaceModuleAdjunction Stacks.Ample Stacks.RelativeVeryAmple

/-- The ringed-space pull-back of a module along a morphism of schemes is the scheme pull-back. -/
private noncomputable def modulePullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) :
    (modulePullback f.toLRSHom.toShHom).obj F ≅ (Scheme.Modules.pullback f).obj F :=
  (Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction f)).app F

/-- For a quasi-compact morphism, `f`-ampleness gives ampleness over every affine open. -/
private theorem stacks_of_isRelativelyAmple {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    (L : X.Modules) [IsInvertibleModule X L] (hL : MMP.Mori.IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f L inferInstance hL

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

/-- **[Stacks, Tag 0C4K] for Cartier divisors.** Let `f : X ⟶ Y` and `g : Y ⟶ S` be
quasi-compact, `S` quasi-compact, `L` an `f`-ample Cartier divisor on `X` and `M` a `g`-ample
Cartier divisor on `Y` with pull-back `M' = f^*M`. Then `L + nM'` is `(f ≫ g)`-ample for all
large `n`. -/
private theorem exists_isRelativelyAmple_add_nsmul {X Y S : Scheme.{u}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace S]
    (f : X ⟶ Y) (g : Y ⟶ S) [QuasiCompact f] [QuasiCompact g]
    {L : Divisor X} (hL : L.IsCartier) (hLf : L.IsRelativelyAmple f hL)
    {M : Divisor Y} (hM : M.IsCartier) (hMg : M.IsRelativelyAmple g hM)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ M.supp}
    {M' : Divisor X} (hM' : M.IsPullback f hB M') :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (L + n • M').IsRelativelyAmple (f ≫ g) (hL.add ((hM'.isCartier hM).nsmul n)) := by
  have hM'c := hM'.isCartier hM
  haveI := hL.isInvertibleModule_divisorialSheaf
  haveI := hM.isInvertibleModule_divisorialSheaf
  haveI := hM'c.isInvertibleModule_divisorialSheaf
  obtain ⟨n₀, hn₀⟩ := Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp f g _ _
    (stacks_of_isRelativelyAmple f _ hLf) (stacks_of_isRelativelyAmple g _ hMg)
  refine ⟨n₀, fun n hn => ?_⟩
  haveI := (hL.add (hM'c.nsmul n)).isInvertibleModule_divisorialSheaf
  have eB : (modulePullback f.toLRSHom.toShHom).obj M.divisorialSheaf ≅ M'.divisorialSheaf :=
    modulePullbackIso f _ ≪≫ (hM'.divisorialSheafIso (hBc := hM)).symm
  have e : Stacks.AmplePullbackPart1.tensorPullbackPowModule f L.divisorialSheaf
      M.divisorialSheaf n ≅ (L + n • M').divisorialSheaf :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso X (Iso.refl _)
        (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso f _ n ≪≫
          Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso X _ _ eB n ≪≫
          (divisorialSheafNsmulIso hM'c n).symm) ≪≫
      hL.divisorialSheafTensorIso (hM'c.nsmul n)
  exact MMP.Mori.IsRelativelyAmple.of_stacks _ _
    ((Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mp (hn₀ n hn))

/-- If `φ = (a, b) : W ⟶ X ×_S Y` is affine, `L` is `f`-ample and `N` is `g`-ample, then
`a^* L ⊗ b^* N` is ample relative to `a ≫ f`. -/
private theorem isRelativelyAmple_tensorModules_of_isAffineHom {S X Y W : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} {a : W ⟶ X} {b : W ⟶ Y} (h : a ≫ f = b ≫ g)
    [IsAffineHom (Limits.pullback.lift a b h)] (L : X.Modules) (N : Y.Modules)
    [IsInvertibleModule X L] [IsInvertibleModule Y N]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hN : Stacks.RelativeAmple.IsRelativelyAmple g N) :
    Stacks.RelativeAmple.IsRelativelyAmple (a ≫ f)
      (tensorModules W ((modulePullback a.toLRSHom.toShHom).obj L)
        ((modulePullback b.toLRSHom.toShHom).obj N)) := by
  have h1 := Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom
    (Limits.pullback.lift a b h) (Limits.pullback.fst f g ≫ f) _
    (Stacks.AmpleExternalTensor.isRelativelyAmple_externalTensor f g L N hL hN)
  have e := Stacks.AmpleExternalTensor.pullbackExternalTensorIso f g
    (Limits.pullback.lift a b h) L N
  simp only [Limits.pullback.lift_fst, Limits.pullback.lift_snd] at e
  rw [← Category.assoc, Limits.pullback.lift_fst] at h1
  exact (isRelativelyAmple_congr _ _ _ e).mp h1

/-- For a quasi-compact separated morphism `f`, the sum of two `f`-ample Cartier divisors is
`f`-ample: `𝒪(A + B) ≅ Δ^*(𝒪(A) ⊠ 𝒪(B))` and the diagonal of `f` is affine. -/
private theorem isRelativelyAmple_add {S X : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {A B : Divisor X} (hA : A.IsCartier) (hAf : A.IsRelativelyAmple f hA)
    (hB : B.IsCartier) (hBf : B.IsRelativelyAmple f hB) :
    (A + B).IsRelativelyAmple f (hA.add hB) := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  haveI := hB.isInvertibleModule_divisorialSheaf
  haveI := (hA.add hB).isInvertibleModule_divisorialSheaf
  haveI : IsAffineHom (Limits.pullback.lift (𝟙 X) (𝟙 X) (rfl : 𝟙 X ≫ f = 𝟙 X ≫ f)) :=
    show IsAffineHom (Limits.pullback.diagonal f) from inferInstance
  have h := isRelativelyAmple_tensorModules_of_isAffineHom (rfl : 𝟙 X ≫ f = 𝟙 X ≫ f) _ _
    (stacks_of_isRelativelyAmple f _ hAf) (stacks_of_isRelativelyAmple f _ hBf)
  rw [Category.id_comp] at h
  refine MMP.Mori.IsRelativelyAmple.of_stacks _ _ ((isRelativelyAmple_congr _ _ _ ?_).mp h)
  exact tensorModulesMapIso X (modulePullbackIso _ _ ≪≫ (Scheme.Modules.pullbackId X).app _)
    (modulePullbackIso _ _ ≪≫ (Scheme.Modules.pullbackId X).app _) ≪≫
    hA.divisorialSheafTensorIso hB

/-- For a quasi-compact separated morphism `f`, every positive multiple of an `f`-ample Cartier
divisor is `f`-ample. -/
private theorem isRelativelyAmple_nsmul {S X : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {L : Divisor X} (hL : L.IsCartier) (hLf : L.IsRelativelyAmple f hL)
    (n : ℕ) (hn : 0 < n) : (n • L).IsRelativelyAmple f (hL.nsmul n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simpa using hLf
    · convert isRelativelyAmple_add _ (ih hn') _ hLf using 2
      rw [succ_nsmul]

/-- Relative ampleness of a Cartier divisor does not depend on the proof that it is Cartier, and
is transported along equalities of divisors. -/
private theorem isRelativelyAmple_of_eq {S X : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} {A B : Divisor X}
    (hAB : A = B) (hA : A.IsCartier) (hB : B.IsCartier) (hAf : A.IsRelativelyAmple f hA) :
    B.IsRelativelyAmple f hB := by
  subst hAB
  exact hAf

/-- Every Cartier divisor is ample relative to an isomorphism. -/
private theorem isRelativelyAmple_of_isIso {X Y : Scheme.{u}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (e : X ⟶ Y) [IsIso e] {L : Divisor X}
    (hL : L.IsCartier) : L.IsRelativelyAmple e hL := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  refine ⟨V, hV, hyV, ?_⟩
  haveI : IsAffine (e ⁻¹ᵁ V) := hV.preimage e
  haveI : CompactSpace (e ⁻¹ᵁ V) := inferInstance
  have hinv : Stacks.Ample.IsInvertibleModule (e ⁻¹ᵁ V).toScheme
      ((RingedSpaceModuleAdjunction.modulePullback (e ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
        L.divisorialSheaf) := inferInstance
  exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
    (@AlgebraicGeometry.Scheme.Modules.isAmple_of_isAffine_of_isInvertible _ _ _ _ hinv)

/-- Relative ampleness depends only on the isomorphism class of the invertible sheaf. -/
private theorem isRelativelyAmple_of_iso {X Y : Scheme.{u}} (f : X ⟶ Y) {L L' : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L')
    (h : MMP.Mori.IsRelativelyAmple f L) : MMP.Mori.IsRelativelyAmple f L' := by
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e)).1 hamp

/-- The Weil divisor of `-A` is minus the Weil divisor of `A`. -/
private theorem isWeilDivisorOfCartier_neg {X : Scheme.{u}} {A : X.CartierDivisor}
    {w : Divisor X} (h : MMP.Intersection.IsWeilDivisorOfCartier A w) :
    MMP.Intersection.IsWeilDivisorOfCartier (-A) (-w) := by
  intro P
  obtain ⟨a, b, ha, hb, ⟨g, ⟨U, hxU, g', hg', hgg⟩, hbu, hbg⟩, la, lb, hla, hlb, hN⟩ := h P
  have hgu : IsUnit g := hgg ▸ g'.isUnit.map _
  refine ⟨b, a, hb, ha, ⟨_, ⟨U, hxU, g'⁻¹, hg'.inv, rfl⟩, ?_, ?_⟩, lb, la, hlb, hla, ?_⟩
  · rw [← hbg]; exact hbu.mul hgu
  · rw [← hbg, ← hgg, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  · rw [DivisorWithCoeffs.coeff_neg, hN]; ring

/-- **The exceptional divisor of a smooth blow-up is relatively anti-ample**, as a Weil
divisor: if `G` is a prime divisor of `B_I Y` with ideal sheaf the exceptional ideal `I · 𝒪`,
and `B_I Y` is a smooth variety, then `-G` is `π`-ample. -/
private theorem isRelativelyAmple_neg_single_of_idealSheaf_eq {k : Type u} [Field k]
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] [CompactSpace Y] (sY : Y ⟶ Spec (.of k))
    (I : Y.IdealSheafData) [IsIntegral (blowUp I)] [IsLocallyNoetherian (blowUp I)]
    [IsNormal (blowUp I)] [CompactSpace (blowUp I)]
    (hvar : AlgebraicGeometry.IsVariety k (blowUpToBase I ≫ sY))
    (hsm : IsSmoothScheme (blowUpToBase I ≫ sY)) (G : Mori.PrimeDivisor (blowUp I))
    (hG : G.idealSheaf = exceptionalIdeal I)
    (hc : Divisor.IsCartier (-(Finsupp.single G (1 : ℤ) : Divisor (blowUp I)))) :
    Divisor.IsRelativelyAmple (blowUpToBase I) (-(Finsupp.single G (1 : ℤ) : Divisor (blowUp I)))
      hc := by
  haveI : IsNoetherian Y := ⟨⟩
  obtain ⟨A, hA⟩ := (MMP.Resolution.Bridges.uniqueFactorization_and_exists_isWeilDivisorOfCartier).2
    (blowUp I) (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hsm)
    (Finsupp.single G (1 : ℤ))
  obtain ⟨hAe, hAsub⟩ :=
    MMP.Intersection.IsWeilDivisorOfCartier.isEffective_and_subscheme_eq_of_isSmoothScheme
      (blowUpToBase I ≫ sY) hsm hA
  have hAneg := isWeilDivisorOfCartier_neg hA
  have e1 : exceptionalIdealModule I ≅ MMP.CartierDivisor.sheaf (-A) :=
    eqToIso (congrArg (fun K : (blowUp I).IdealSheafData =>
        Stacks.ClosedImmersion.idealSheaf K.subschemeι.toLRSHom.toShHom)
        (hAsub.trans hG).symm) ≪≫ MMP.CartierDivisor.idealSheafIsoSheafNeg A hAe
  have e2 : CartierDivisor.sheaf (-A)
      ≅ Divisor.divisorialSheaf (-(Finsupp.single G (1 : ℤ) : Divisor (blowUp I))) :=
    MMP.Intersection.IsWeilDivisorOfCartier.sheafIsoDivisorialSheaf hAneg
  obtain ⟨-, hinv, hamp, -⟩ := MMP.Foundations.isRelativelyAmple_exceptionalIdealModule I
    (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
  haveI := hc.isInvertibleModule_divisorialSheaf
  exact isRelativelyAmple_of_iso _ (e1 ≪≫ e2) hamp

end Ample

/-! ### Coefficients of pull-backs -/

section Pullbacks

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} [IsDominant f]

/-- **Coefficients of a pull-back where the morphism is a local isomorphism.** If the stalk map
of `f` at the generic point of `H` is an isomorphism and `f(η_H) = η_P`, then
`coeff_H(f^*C) = coeff_P(C)`. -/
private theorem coeff_isPullback_eq_of_isIso {C : Divisor X} (hCc : C.IsCartier)
    {hC : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ C.supp}
    {C' : Divisor Y} (h : C.IsPullback f hC C') (H : Mori.PrimeDivisor Y)
    (P : Mori.PrimeDivisor X) (hHP : f H.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap H.genericPoint)] : C'.coeff H = C.coeff P := by
  obtain ⟨V, hV, φ, hφ⟩ := hCc (f H.genericPoint)
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ H hV P.component,
    MMP.Positivity.ord_functionFieldMap_of_isIso f H P hHP,
    ← MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
    hφ P ⟨P.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P, hHP ▸ hV⟩]

/-- The coefficient along `H` of the pull-back of a Cartier divisor `C` vanishes when `C` has
coefficient zero along every prime divisor through `f(η_H)`. -/
private theorem coeff_isPullback_eq_zero_of_forall {C : Divisor X} (hCc : C.IsCartier)
    {hC : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ C.supp}
    {C' : Divisor Y} (h : C.IsPullback f hC C') (H : Mori.PrimeDivisor Y)
    (h0 : ∀ Γ : Mori.PrimeDivisor X, f H.genericPoint ∈ Γ.support → C.coeff Γ = 0) :
    C'.coeff H = 0 := by
  set x := f H.genericPoint with hx
  obtain ⟨V, hV, φ, hφ⟩ := hCc x
  set Z0 := MMP.Mori.pointComponent x with hZ0
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : MMP.Mori.RationalFunctions X) with hgdef
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ H hV Z0]
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := f) H
    (fun _ : Unit => g) (fun _ => hg) (fun _ => 1) fun Γ hΓ => by
      have hZ : Γ.component = Z0 := Subsingleton.elim
        (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
      have e := hφ Γ ⟨x, hΓ, hV⟩
      rw [h0 Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ] at e
      have e' : Scheme.ord g Γ.genericPoint = 0 := e.symm
      simp [e']
  simpa using key

end Pullbacks

/-! ### Prime divisors in snc closed subsets -/

/-- The reduced divisor with components a finite set `s` of prime divisors has support `s`. -/
private theorem support_sum_single {X : Scheme.{u}} (s : Finset (Mori.PrimeDivisor X)) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).support = s := by
  classical
  ext E
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

section SNCHelpers

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- A prime divisor whose generic point lies in a closed set is contained in it. -/
private theorem support_subset_of_genericPoint_mem {X : Scheme.{u}} (P : Mori.PrimeDivisor X)
    {C : Set X} (hC : IsClosed C) (h : P.genericPoint ∈ C) : (P.support : Set X) ⊆ C := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact closure_minimal (Set.singleton_subset_iff.mpr h) hC

/-- The ideal sheaf of a prime divisor is the vanishing ideal of its support. -/
private theorem idealSheaf_eq_vanishingIdeal {X : Scheme.{u}} (P : Mori.PrimeDivisor X)
    {T : Closeds X} (hT : (T : Set X) = P.support) :
    P.idealSheaf = Scheme.IdealSheafData.vanishingIdeal T := by
  have := P.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ (Closeds.ext hT.symm)

/-- An irreducible component of a closed subset of pure codimension one is the closure of a
point of coheight one. -/
private theorem exists_coheight_eq_one_of_mem_componentsOf {S : Set Y} (hSc : IsClosed S)
    (hS : MMP.Mori.IsPureCodimOne (⟨S, hSc⟩ : Closeds Y)) {V : Set Y}
    (hV : V ∈ componentsOf S) : ∃ ξ : Y, V = closure {ξ} ∧ Order.coheight ξ = 1 := by
  obtain ⟨ξ, -, hξ⟩ := Aux.exists_eq_closure_of_mem_componentsOf hSc hV
  refine ⟨ξ, hξ, ?_⟩
  rw [← MMP.Flips.codimension_closureSingleton]
  apply hS
  refine ⟨?_, fun W' hW' hle => ?_⟩
  · change closure {ξ} ⊆ S
    rw [← hξ]
    exact hV.1.2
  · have : (W' : Set Y) ⊆ V := hV.2 ⟨W'.isIrreducible, hW'⟩ (by rwa [hξ])
    change (W' : Set Y) ⊆ closure {ξ}
    rw [← hξ]
    exact this

/-- The support of a prime divisor contained in an snc closed subset `S` is an irreducible
component of `S`. -/
private theorem support_mem_componentsOf [NoetherianSpace Y] {S : Set Y}
    (hS : IsSNCClosedSubset sY S) {P : Mori.PrimeDivisor Y} (hP : (P.support : Set Y) ⊆ S) :
    (P.support : Set Y) ∈ componentsOf S := by
  obtain ⟨hSc, hempty | ⟨hpure, -, -⟩⟩ := hS
  · exfalso
    have := hP (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P)
    rw [hempty] at this
    exact this
  · obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf hSc
    obtain ⟨W, hW, hηW⟩ := hcov (hP (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P))
    obtain ⟨ξ, hWξ, hξ1⟩ := exists_coheight_eq_one_of_mem_componentsOf hSc hpure hW
    have hsp : ξ ⤳ P.genericPoint := specializes_iff_mem_closure.mpr (hWξ ▸ hηW)
    have hξη : ξ = P.genericPoint := by
      by_contra hne
      have hlt : P.genericPoint < ξ := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp)
        fun hle => hne (hsp.antisymm (Scheme.le_iff_specializes.mp hle)).eq
      have := Order.coheight_strictAnti hlt
      rw [hξ1, P.coheight_genericPoint] at this
      exact lt_irrefl _ (this (by simp))
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    change closure {P.genericPoint} ∈ _
    rw [← hξη, ← hWξ]
    exact hW

/-- Only finitely many prime divisors are contained in an snc closed subset. -/
private theorem finite_setOf_support_subset [NoetherianSpace Y] {S : Set Y}
    (hS : IsSNCClosedSubset sY S) :
    {P : Mori.PrimeDivisor Y | (P.support : Set Y) ⊆ S}.Finite := by
  refine Set.Finite.of_finite_image ((Aux.finite_and_cover_componentsOf hS.1).1.subset ?_)
    fun P _ Q _ h => MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset h.subset
  rintro - ⟨P, hP, rfl⟩
  exact support_mem_componentsOf hS hP

/-- **A reduced divisor whose components lie in an snc closed subset is snc.** -/
private theorem isSNC_sum_single_of_support_subset [LocallyOfFiniteType sY] [NoetherianSpace Y]
    [IsLocallyNoetherian Y] (hsm : IsSmoothScheme sY) {S : Set Y} (hS : IsSNCClosedSubset sY S)
    (s : Finset (Mori.PrimeDivisor Y)) (hs : ∀ P ∈ s, (P.support : Set Y) ⊆ S) :
    (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).IsSNC sY := by
  classical
  have hc : ∀ P ∈ s, (P.support : Set Y) ∈ componentsOf S := fun P hP =>
    support_mem_componentsOf hS (hs P hP)
  obtain ⟨hSc, hempty | ⟨-, -, hfam⟩⟩ := id hS
  · have hs0 : s = ∅ := Finset.eq_empty_of_forall_notMem fun P hP => by
      have := hs P hP (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P)
      rw [hempty] at this
      exact this
    subst hs0
    rw [Finset.sum_empty]
    exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme sY hsm
  have hG := support_sum_single s
  have hideal : ∀ P (hP : P ∈ s),
      P.idealSheaf = componentsFamily S ⟨(P.support : Set Y), hc P hP⟩ := fun P hP =>
    idealSheaf_eq_vanishingIdeal P (by
      rw [Closeds.coe_closure, (Aux.isClosed_of_mem_componentsOf hSc (hc P hP)).closure_eq])
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [hG] at hP
    rw [hideal P hP]
    exact (hfam.1 _).2.2
  · obtain ⟨m, z, c, hz, hcI, hcinj⟩ := hfam.2 x
    have hs' : ∀ P : {P : Mori.PrimeDivisor Y //
        P ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ x ∈ P.support},
        P.1 ∈ s := fun P => hG.subset P.2.1
    have hmem : ∀ P : {P : Mori.PrimeDivisor Y //
        P ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ x ∈ P.support},
        x ∈ (componentsFamily S ⟨(P.1.support : Set Y), hc P.1 (hs' P)⟩).support := fun P => by
      rw [← SetLike.mem_coe, coe_support_componentsFamily hSc]
      exact P.2.2
    refine ⟨m, z, fun P => c ⟨_, hmem P⟩, hz, fun P Q h => ?_, fun P => ?_⟩
    · have h1 := congrArg (fun V => (V.1.1 : Set Y)) (hcinj h)
      exact Subtype.ext (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset h1.subset)
    · rw [hideal P.1 (hs' P)]
      exact hcI ⟨_, hmem P⟩

end SNCHelpers

section Stratum

open MMP.Fourfold.SNCWeight

private theorem stalk_bot_eq {Y : Scheme.{u}} (x : Y) :
    IdealSheafData.stalk (⊥ : Y.IdealSheafData) x = ⊥ := by
  rw [IdealSheafData.stalk]
  refine le_bot_iff.mp (iSup₂_le fun U hs => ?_)
  rw [show (⊥ : Y.IdealSheafData).ideal U = ⊥ from rfl, Ideal.map_bot]

/-- The stalk of a finite supremum of ideal sheaves is the supremum of the stalks. -/
private theorem stalk_finset_sup {Y : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (f : ι → Y.IdealSheafData) (x : Y) :
    IdealSheafData.stalk (s.sup f) x = ⨆ i ∈ s, IdealSheafData.stalk (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, stalk_bot_eq]
    symm
    simp only [iSup_eq_bot]
    intro i hi
    exact absurd hi (Finset.notMem_empty i)
  | insert i s hi ih =>
    rw [Finset.sup_insert, IdealSheafData.stalk_sup, ih, Finset.iSup_insert]

/-- The support of a finite supremum of ideal sheaves is the intersection of the supports. -/
private theorem coe_support_finset_sup {Y : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (f : ι → Y.IdealSheafData) :
    ((s.sup f).support : Set Y) = ⋂ i ∈ s, ((f i).support : Set Y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sup_insert, Scheme.IdealSheafData.support_sup, Closeds.coe_inf, ih,
      Finset.set_biInter_insert]

/-- A supremum of principal ideals generated by members `z_j`, `j ∈ J`, of a family. -/
private theorem iSup_eq_span_image {R : Type*} [CommRing R] {N : ℕ} (z : Fin N → R)
    {ι : Type*} (T : Finset ι) (I : ι → Ideal R) (J : Finset (Fin N))
    (h1 : ∀ G ∈ T, ∃ j ∈ J, I G = Ideal.span {z j})
    (h2 : ∀ j ∈ J, ∃ G ∈ T, I G = Ideal.span {z j}) :
    ⨆ G ∈ T, I G = Ideal.span (z '' (J : Set (Fin N))) := by
  refine le_antisymm (iSup₂_le fun G hG => ?_) (Ideal.span_le.mpr ?_)
  · obtain ⟨j, hj, hIj⟩ := h1 G hG
    rw [hIj]
    exact Ideal.span_mono (Set.singleton_subset_iff.mpr ⟨j, hj, rfl⟩)
  · rintro _ ⟨j, hj, rfl⟩
    obtain ⟨G, hG, hIj⟩ := h2 j hj
    have : z j ∈ I G := by rw [hIj]; exact Ideal.mem_span_singleton_self _
    exact (le_iSup₂ (f := fun G _ => I G) G hG) this

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- **A component of an intersection of snc components.** Let `∑_{G ∈ T} G` be an snc divisor
on a scheme `Y` smooth over a perfect field, and `C` an irreducible component of
`⋂_{G ∈ T} G`. Then `C` is smooth with its reduced structure, and along `C` its ideal is
`∑_{G ∈ T} I_G`. -/
private theorem stratum_component [PerfectField k] (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sY] [QuasiCompact sY] {T : Finset (Mori.PrimeDivisor Y)}
    (hsnc : DivisorWithCoeffs.IsSNC sY (∑ G ∈ T, Finsupp.single G (1 : ℤ)))
    {C : Closeds Y} (hC : (C : Set Y) ∈ componentsOf (⋂ G ∈ T, (G.support : Set Y))) :
    IsSmoothScheme ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ sY) ∧
      ∀ x ∈ (C : Set Y), IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal C) x =
          ⨆ G ∈ T, IdealSheafData.stalk G.idealSheaf x := by
  classical
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := {}
  set D := T.sup (fun G => G.idealSheaf) with hDdef
  have hDsupp : (D.support : Set Y) = ⋂ G ∈ T, (G.support : Set Y) := coe_support_finset_sup _ _
  -- coordinates at a point of `D`
  have hcoord : ∀ x ∈ (D.support : Set Y), ∃ (N : ℕ) (z : Fin N → Y.presheaf.stalk x)
      (J : Finset (Fin N)), IsRegularSystemOfParameters z ∧
        IdealSheafData.stalk D x = Ideal.span (z '' (J : Set (Fin N))) := by
    intro x hx
    rw [hDsupp, Set.mem_iInter₂] at hx
    obtain ⟨N, z, j, hz, -, hI⟩ := MMP.Mori.exists_at_of_isSNC hsnc x
    let jT : T → Fin N := fun G => j ⟨G.1, G.2, hx G.1 G.2⟩
    refine ⟨N, z, Finset.univ.image jT, hz, ?_⟩
    rw [hDdef, stalk_finset_sup]
    refine iSup_eq_span_image z T _ _ (fun G hG => ⟨jT ⟨G, hG⟩,
      Finset.mem_image_of_mem _ (Finset.mem_univ _), hI ⟨G, hG, hx G hG⟩⟩) fun i hi => ?_
    obtain ⟨G, -, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨G.1, G.2, hI ⟨G.1, G.2, hx G.1 G.2⟩⟩
  have hDreg : ∀ x ∈ D.support,
      IsRegularLocalRing (Y.presheaf.stalk x ⧸ IdealSheafData.stalk D x) := by
    intro x hx
    obtain ⟨N, z, J, hz, hDx⟩ := hcoord x hx
    have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
    rw [hDx]
    exact MMP.Resolution.isRegularLocalRing_quotient_span_image z hz J
  have hDsm : IsSmoothScheme (D.subschemeι ≫ sY) :=
    PrimeDivisorUnion.isSmoothScheme_subscheme_of_isRegularLocalRing_quotient sY D hDreg
  have hDred : IsReduced D.subscheme := by
    have : LocallyOfFinitePresentation (D.subschemeι ≫ sY) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := D.subschemeι ≫ sY)).mpr
        inferInstance
    have hsm : Smooth (D.subschemeι ≫ sY) := (MMP.Mori.isSmoothScheme_iff _).1 hDsm
    haveI : ∀ x : D.subscheme, _root_.IsReduced (D.subscheme.presheaf.stalk x) := fun x => by
      have := isRegularLocalRing_stalk_of_smooth_over_field (D.subschemeι ≫ sY) x
      have := IsRegularLocalRing.isDomain (D.subscheme.presheaf.stalk x)
      exact isReduced_of_noZeroDivisors
    exact isReduced_of_isReduced_stalk _
  have hDcl : IsClosed (D.support : Set Y) := D.support.isClosed
  obtain ⟨hfin, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf hDcl
  rw [← hDsupp] at hC
  set B := ⋃₀ (componentsOf (D.support : Set Y) \ {(C : Set Y)}) with hB
  have hBcl : IsClosed B := (hfin.subset Set.sdiff_subset).isClosed_sUnion
    fun W hW => MMP.Resolution.Aux.isClosed_of_mem_componentsOf hDcl hW.1
  have hdisj : ∀ x ∈ (C : Set Y), x ∉ B := by
    rintro x hxC ⟨W, ⟨hW, hWC⟩, hxW⟩
    exact hWC (MMP.Resolution.Aux.eq_of_mem_componentsOf_of_isSmoothScheme sY D hDsm hW hC
      hxW hxC)
  have hCB : (C : Set Y) ∪ B = D.support := by
    refine le_antisymm (Set.union_subset hC.1.2 ?_) fun x hx => ?_
    · rintro x ⟨W, ⟨hW, -⟩, hxW⟩; exact hW.1.2 hxW
    · obtain ⟨W, hW, hxW⟩ := hcov hx
      by_cases h : W = (C : Set Y)
      · exact Or.inl (h ▸ hxW)
      · exact Or.inr ⟨W, ⟨hW, h⟩, hxW⟩
  have hstalk : ∀ x ∈ (C : Set Y), IdealSheafData.stalk
      (Scheme.IdealSheafData.vanishingIdeal C) x = IdealSheafData.stalk D x := fun x hx =>
    MMP.Mori.stalk_vanishingIdeal_eq_stalk_of_sup_eq D C ⟨B, hBcl⟩ (Closeds.ext hCB) (hdisj x hx)
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal C).support : Set Y) = C := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  refine ⟨?_, fun x hx => by rw [hstalk x hx, hDdef, stalk_finset_sup]⟩
  refine PrimeDivisorUnion.isSmoothScheme_subscheme_of_isRegularLocalRing_quotient sY _
    fun x hx => ?_
  rw [← SetLike.mem_coe, hsupp] at hx
  rw [hstalk x hx]
  exact hDreg x (hC.1.2 hx)

/-- **The centre has snc with the boundary.** If the ideal of `Z` is `∑_{G ∈ T} I_G` along `Z`,
for components `G ∈ T` of an snc divisor `D`, then `Z` has simple normal crossings with `D`. -/
private theorem hasSNCWith_of_stalk_eq {sY : Y ⟶ Spec (.of k)} [NoetherianSpace Y] {D : Set Y}
    (hD : IsSNCClosedSubset sY D) {Z : Y.IdealSheafData} {T : Finset (Mori.PrimeDivisor Y)}
    (hTne : T.Nonempty) (hTD : ∀ G ∈ T, (G.support : Set Y) ⊆ D)
    (hZT : ∀ G ∈ T, (Z.support : Set Y) ⊆ G.support)
    (hZst : ∀ x ∈ Z.support, IdealSheafData.stalk Z x =
      ⨆ G ∈ T, IdealSheafData.stalk G.idealSheaf x) :
    HasSNCWith (componentsFamily D) Z := by
  classical
  intro x hx
  have hGc : ∀ G ∈ T, (G.support : Set Y) ∈ componentsOf D := fun G hG =>
    support_mem_componentsOf hD (hTD G hG)
  obtain ⟨hDc, hempty | ⟨-, -, hfam⟩⟩ := hD
  · exfalso
    obtain ⟨G, hG⟩ := hTne
    have := hTD G hG (hZT G hG hx)
    rw [hempty] at this
    exact this
  have hideal : ∀ G (hG : G ∈ T), componentsFamily D ⟨_, hGc G hG⟩ = G.idealSheaf := fun G hG =>
    (idealSheaf_eq_vanishingIdeal G (by
      rw [Closeds.coe_closure, (Aux.isClosed_of_mem_componentsOf hDc (hGc G hG)).closure_eq])).symm
  have hmem : ∀ G (hG : G ∈ T), x ∈ (componentsFamily D ⟨_, hGc G hG⟩).support := fun G hG => by
    rw [hideal G hG]; exact hZT G hG hx
  obtain ⟨N, z, c, hz, hI, hcinj⟩ := hfam.2 x
  refine ⟨N, z, c, Finset.univ.filter
    (fun i => ∃ G, ∃ hG : G ∈ T, i = c ⟨⟨_, hGc G hG⟩, hmem G hG⟩), hz, hI, hcinj, ?_⟩
  rw [hZst x hx]
  refine iSup_eq_span_image z T _ _ (fun G hG => ⟨_, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, G, hG, rfl⟩, ?_⟩) fun i hi => ?_
  · rw [← hideal G hG]; exact hI ⟨⟨_, hGc G hG⟩, hmem G hG⟩
  · obtain ⟨-, G, hG, rfl⟩ := Finset.mem_filter.mp hi
    exact ⟨G, hG, by rw [← hideal G hG]; exact hI ⟨⟨_, hGc G hG⟩, hmem G hG⟩⟩

end Stratum

/-! ### Strata of the boundary and one blow-up -/

section BlowupHelpers

open MMP.Fourfold.SNCWeight MMP.Fourfold.SNCWeight.StratumBlowup
  MMP.Fourfold.SNCWeight.CentreLifting MMP.Fourfold.SNCWeight.LocalEquation

/-- **A finite set of components.** The members of a nonempty family `J` of irreducible components
of an snc closed subset `S` are the supports of the prime divisors of a nonempty finite set `T`
contained in `S`, and `⋂₀ J = ⋂_{P ∈ T} P`. -/
private theorem exists_finset_sInter_eq {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [NoetherianSpace Y] {S : Set Y} (hS : IsSNCClosedSubset sY S)
    {J : Set (Set Y)} (hJne : J.Nonempty) (hJS : J ⊆ componentsOf S) :
    ∃ T : Finset (Mori.PrimeDivisor Y), T.Nonempty ∧ (∀ P ∈ T, (P.support : Set Y) ⊆ S) ∧
      ⋂₀ J = ⋂ P ∈ T, (P.support : Set Y) := by
  classical
  have hW : ∀ W ∈ J, ∃ P : Mori.PrimeDivisor Y, (P.support : Set Y) = W := by
    intro W hWJ
    obtain ⟨hSc, hempty | ⟨hpure, -, -⟩⟩ := hS
    · exfalso
      obtain ⟨w, hw⟩ := (hJS hWJ).1.1.nonempty
      have := (hJS hWJ).1.2 hw
      rw [hempty] at this
      exact this
    · obtain ⟨ξ, hWξ, hξ1⟩ := exists_coheight_eq_one_of_mem_componentsOf hSc hpure (hJS hWJ)
      refine ⟨primeOfCoheightOne ξ hξ1, ?_⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hWξ]
      change closure {(primeOfCoheightOne ξ hξ1).genericPoint} = _
      rw [genericPoint_primeOfCoheightOne]
  set T := (finite_setOf_support_subset hS).toFinset.filter
    (fun P : Mori.PrimeDivisor Y => (P.support : Set Y) ∈ J) with hT
  have hmemT : ∀ P, P ∈ T ↔ (P.support : Set Y) ∈ J := fun P => by
    rw [hT, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨(hJS h).1.2, h⟩⟩
  refine ⟨T, ?_, fun P hP => ((hJS ((hmemT P).mp hP)).1.2), ?_⟩
  · obtain ⟨W, hWJ⟩ := hJne
    obtain ⟨P, hP⟩ := hW W hWJ
    exact ⟨P, (hmemT P).mpr (hP ▸ hWJ)⟩
  · ext z
    simp only [Set.mem_sInter, Set.mem_iInter]
    constructor
    · intro hz P hP
      exact hz _ ((hmemT P).mp hP)
    · intro hz W hWJ
      obtain ⟨P, rfl⟩ := hW W hWJ
      exact hz P ((hmemT P).mpr hWJ)

/-- In a local domain, if a principal ideal `(t) ≠ 0` is generated by finitely many elements
`w_i`, then it is generated by one of them. -/
private theorem exists_span_singleton_eq_of_span_range_eq {R : Type*} [CommRing R] [IsDomain R]
    [IsLocalRing R] {ι : Type*} [Fintype ι] (w : ι → R) {t : R} (ht : t ≠ 0)
    (h : Ideal.span (Set.range w) = Ideal.span {t}) :
    ∃ i, Ideal.span {w i} = Ideal.span {t} := by
  have hts : t ∈ Ideal.span (Set.range w) := h ▸ Ideal.mem_span_singleton_self t
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hts
  have hw : ∀ i, ∃ r, r * t = w i := fun i =>
    Ideal.mem_span_singleton'.mp (h ▸ Ideal.subset_span ⟨i, rfl⟩)
  choose r hr using hw
  have hsum : (∑ i, c i * r i) * t = t := by
    rw [Finset.sum_mul]
    conv_rhs => rw [← hc]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, hr]
  have hsum1 : ∑ i, c i * r i = 1 := mul_right_cancel₀ ht (hsum.trans (one_mul t).symm)
  by_contra hne
  simp only [not_exists] at hne
  have hmem : ∀ i, c i * r i ∈ IsLocalRing.maximalIdeal R := by
    intro i
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hru : IsUnit (r i) := isUnit_of_mul_isUnit_right hu
    apply hne i
    rw [← hr i, Ideal.span_singleton_mul_left_unit hru]
  have := Ideal.sum_mem (IsLocalRing.maximalIdeal R) fun i (_ : i ∈ Finset.univ) => hmem i
  rw [hsum1] at this
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr this)

/-- The stalks of an effective Cartier divisor are principal. -/
private theorem exists_stalk_eq_span_singleton {X : Scheme.{u}} (J : X.IdealSheafData)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (x : X) :
    ∃ t, IdealSheafData.stalk J x = Ideal.span {t} := by
  obtain ⟨U, hU, hxU, f, -, hf⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor J hJ x
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU, hf, Ideal.map_span, Set.image_singleton]
  exact ⟨_, rfl⟩

/-- **Some strict transform misses the point.** Let `Z` be a smooth irreducible centre of
positive codimension on a smooth `Y` whose ideal is `∑_{P ∈ T} I_P` along `Z`, for the components
`P ∈ T` of an snc divisor containing `Z`. At a point `y'` of the blow-up over `Z`, the ideal of
the exceptional divisor is generated by the pull-back of the local equation of one `P ∈ T`; the
strict transform of that `P` does not pass through `y'`. -/
private theorem exists_notMem_strictPrime {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Z : Y.IdealSheafData} (h : IsSmoothBlowup sY Z) (hirr : IsIrreducible (Z.support : Set Y))
    (hc : 1 ≤ codimension (⟨Z.support, hirr, Z.support.isClosed⟩ : IrreducibleCloseds Y))
    {T : Finset (Mori.PrimeDivisor Y)}
    (hsnc : DivisorWithCoeffs.IsSNC sY (∑ G ∈ T, Finsupp.single G (1 : ℤ)))
    (hZT : ∀ P ∈ T, (Z.support : Set Y) ⊆ P.support)
    (hZst : ∀ x ∈ Z.support, IdealSheafData.stalk Z x =
      ⨆ P ∈ T, IdealSheafData.stalk P.idealSheaf x)
    (y : AlgebraicGeometry.blowUp Z) (hy : blowUpToBase Z y ∈ Z.support) :
    ∃ P ∈ T, ∀ hP : P.genericPoint ∉ (Z.support : Set Y),
      y ∉ ((strictPrime Z P hP).support : Set (AlgebraicGeometry.blowUp Z)) := by
  classical
  haveI := MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension Z hirr hc
  haveI := MMP.Threefold.Resolution.isDominant_blowUpToBase Z hirr hc
  haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY Z h).1
  haveI : IsLocallyNoetherian (AlgebraicGeometry.blowUp Z) :=
    isLocallyNoetherian_of_smooth (blowUpToBase Z ≫ sY)
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase Z ≫ sY)
  set x := blowUpToBase Z y with hx
  set G := excE sY h hirr hc with hG
  obtain ⟨N, z, j, -, -, hI⟩ := MMP.Mori.exists_at_of_isSNC hsnc x
  let zP : T → Y.presheaf.stalk x := fun P => z (j ⟨P.1, P.2, hZT P.1 P.2 hy⟩)
  let w : T → (AlgebraicGeometry.blowUp Z).presheaf.stalk y :=
    fun P => ((blowUpToBase Z).stalkMap y).hom (zP P)
  have hZx : IdealSheafData.stalk Z x = Ideal.span (Set.range zP) := by
    rw [hZst x hy]
    refine le_antisymm (iSup₂_le fun P hP => ?_) (Ideal.span_le.mpr ?_)
    · rw [hI ⟨P, hP, hZT P hP hy⟩]
      exact Ideal.span_mono (Set.singleton_subset_iff.mpr ⟨⟨P, hP⟩, rfl⟩)
    · rintro _ ⟨P, rfl⟩
      have : zP P ∈ IdealSheafData.stalk P.1.idealSheaf x := by
        rw [hI ⟨P.1, P.2, hZT P.1 P.2 hy⟩]
        exact Ideal.mem_span_singleton_self _
      exact (le_iSup₂ (f := fun P (_ : P ∈ T) => IdealSheafData.stalk P.idealSheaf x) P.1 P.2)
        this
  have hEy : IdealSheafData.stalk G.idealSheaf y = Ideal.span (Set.range w) := by
    change IdealSheafData.stalk (Z.comap (blowUpToBase Z)) y = _
    rw [IdealSheafData.stalk_comap, hZx, Ideal.map_span, ← Set.range_comp]
    rfl
  obtain ⟨t, ht⟩ := exists_stalk_eq_span_singleton G.idealSheaf
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z) y
  have hyG : y ∈ (G.support : Set (AlgebraicGeometry.blowUp Z)) := by
    rwa [coe_support_excE]
  have ht0 : t ≠ 0 := fun h0 => localEq_ne_zero G hyG ht (by rw [h0, map_zero])
  haveI : IsDomain ((AlgebraicGeometry.blowUp Z).presheaf.stalk y) := by
    have := isRegularLocalRing_stalk_of_smooth_over_field (blowUpToBase Z ≫ sY) y
    exact IsRegularLocalRing.isDomain _
  obtain ⟨P, hP⟩ := exists_span_singleton_eq_of_span_range_eq w ht0 (hEy.symm.trans ht)
  refine ⟨P.1, P.2, fun hPZ hyH => ?_⟩
  set H := strictPrime Z P.1 hPZ with hH
  have hHG : H ≠ G := strictPrime_ne_excE sY h hirr hc hPZ
  -- the order of the pulled-back local equation along `H` is one
  have h1 : (AlgebraicGeometry.blowUp Z).ord
      (functionFieldMap (blowUpToBase Z) (algebraMap _ Y.functionField (zP P)))
      H.genericPoint = 1 := by
    rw [ord_blowUp_of_ne sY h hirr hc hHG, downPrime_strictPrime sY h hirr hc hPZ hHG,
      ord_localEq P.1 P.1 (hZT P.1 P.2 hy) (hZT P.1 P.2 hy) (hI ⟨P.1, P.2, hZT P.1 P.2 hy⟩),
      if_pos rfl]
  -- but it generates the ideal of `G`, which is trivial at the generic point of `H`
  have hsp : H.genericPoint ⤳ y := specializes_of_mem H hyH
  have hHnot : H.genericPoint ∉ (G.idealSheaf.support : Set (AlgebraicGeometry.blowUp Z)) := by
    intro hmem
    exact hHG (PrimeDivisorUnion.eq_of_support_subset
      (support_subset_of_genericPoint_mem H G.idealSheaf.support.isClosed hmem))
  have htop := (IdealSheafData.stalk_eq_top_iff_notMem_support G.idealSheaf _).mpr hHnot
  rw [MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes G.idealSheaf hsp, ht, ← hP,
    Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top] at htop
  have h0 : (AlgebraicGeometry.blowUp Z).ord
      (functionFieldMap (blowUpToBase Z) (algebraMap _ Y.functionField (zP P)))
      H.genericPoint = 0 := by
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk, ← MMP.Mori.algebraMap_stalkSpecializes hsp]
    exact H.ord_algebraMap_of_isUnit htop
  rw [h1] at h0
  exact one_ne_zero h0

/-- An irreducible closed subset contained in a prime divisor has positive codimension. -/
private theorem one_le_codimension_of_subset_support {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {Z : Y.IdealSheafData} (hirr : IsIrreducible (Z.support : Set Y))
    (P : Mori.PrimeDivisor Y) (hZP : (Z.support : Set Y) ⊆ P.support) :
    1 ≤ codimension (⟨Z.support, hirr, Z.support.isClosed⟩ : IrreducibleCloseds Y) := by
  set ξ := hirr.genericPoint
  have hgen : closure {ξ} = (Z.support : Set Y) := by
    have := hirr.isGenericPoint_genericPoint_closure
    rwa [Z.support.isClosed.closure_eq] at this
  have heq : (⟨Z.support, hirr, Z.support.isClosed⟩ : IrreducibleCloseds Y) =
      IrreducibleCloseds.closureSingleton ξ := by
    ext1
    exact hgen.symm
  rw [heq, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton, ← P.coheight_genericPoint]
  exact Order.coheight_anti <| Scheme.le_iff_specializes.mpr <|
    MMP.Fourfold.SNCWeight.LocalEquation.specializes_of_mem P (hZP (hgen ▸ subset_closure rfl))

end BlowupHelpers

section Setup

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The support `⋃_{coeff_D B = 1} D` of the coefficient-one part of an `ℝ`-divisor `B`. -/
private def oneLocus (B : RDivisor X) : Set X :=
  {x | ∃ D : Mori.PrimeDivisor X, B.coeff D = 1 ∧ x ∈ D.support}

/-- The positivity data on a model `q : Y ⟶ X` with marked point `y`: an effective `q`-ample
`ℚ`-divisor supported on the boundary `q⁻¹(D₀)`, vanishing exactly at the boundary primes
through `y`. -/
private def IsGoodDivisor (B : RDivisor X) {Y : Scheme.{u}} [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (q : Y ⟶ X) (y : Y) (F : QDivisor Y) : Prop :=
  0 ≤ F ∧ F.HasRelativelyAmpleMultiple q ∧
    (∀ D : Mori.PrimeDivisor Y, F.coeff D ≠ 0 →
      (D.support : Set Y) ⊆ q ⁻¹' oneLocus B ∧ y ∉ D.support) ∧
    ∀ D : Mori.PrimeDivisor Y, (D.support : Set Y) ⊆ q ⁻¹' oneLocus B → y ∉ D.support →
      0 < F.coeff D

/-- The invariant of the induction along the stratum blow-ups. -/
private structure IsAmpleModel (sX : X ⟶ Spec (.of k)) (B : RDivisor X) {Y : Scheme.{u}}
    (q : Y ⟶ X) (y : Y) : Prop where
  normal : IsNormalVariety k (q ≫ sX)
  smooth : IsSmoothScheme (q ≫ sX)
  proper : IsProper q
  snc : IsSNCClosedSubset (q ≫ sX) (q ⁻¹' oneLocus B)
  ample : ∃ (_ : CompactSpace Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y) (F : QDivisor Y),
    IsGoodDivisor B q y F

open scoped Classical in
/-- The coefficients of the reduced divisor `∑_{D ∈ S} D`. -/
private theorem coeff_sum_single {R : Type*} [AddCommMonoid R] [One R] {Y : Scheme.{u}}
    (S : Finset (Mori.PrimeDivisor Y)) (E : Mori.PrimeDivisor Y) :
    (∑ D ∈ S, Finsupp.single D (1 : R) : DivisorWithCoeffs R Y).coeff E =
      if E ∈ S then 1 else 0 := by
  classical
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

/-- **The pull-back of a reduced divisor through the image of a prime has positive order.** On a
locally factorial `V`, if some component `P₁` of the reduced divisor `C = ∑_{P ∈ S} P` passes
through `f(η_H)` and the local ring there is regular, then `ord_H(f^*C) ≥ 1`. -/
private theorem one_le_coeff_isPullback_sum_single {V V' : Scheme.{u}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [IsIntegral V'] [IsLocallyNoetherian V'] [IsNormal V']
    [CompactSpace V']
    {f : V' ⟶ V} [IsDominant f] (hcart : ∀ D : Divisor V, D.IsCartier)
    {S : Finset (Mori.PrimeDivisor V)} {P₁ : Mori.PrimeDivisor V} (hP₁S : P₁ ∈ S)
    (H : Mori.PrimeDivisor V') (hP₁ : f H.genericPoint ∈ P₁.support)
    {hC : ∀ Z : irreducibleComponents V', f (componentGenericPoint V' Z) ∉
      DivisorWithCoeffs.supp (∑ P ∈ S, Finsupp.single P (1 : ℤ) : Divisor V)}
    {C' : Divisor V'} (h : Divisor.IsPullback f (∑ P ∈ S, Finsupp.single P (1 : ℤ)) hC C') :
    1 ≤ C'.coeff H := by
  classical
  set R : Divisor V := ∑ P ∈ S.erase P₁, Finsupp.single P 1 with hR
  obtain ⟨P₁', hP₁'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant f
    (hcart (Finsupp.single P₁ 1))
  obtain ⟨R', hR'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant f (hcart R)
  have hsum := (hP₁'.add (hcart _) (hcart R)
    (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp f _) hR').of_eq
    (Finset.add_sum_erase S (fun P => (Finsupp.single P (1 : ℤ) : Divisor V)) hP₁S)
    (hB₂ := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp f _)
  have h1 := MMP.Proof_lem_fourfold_pluriform_floor_vanishing_invariant.one_le_coeff_of_isPullback
    P₁ (hcart _) hP₁' H hP₁
  have h2 : 0 ≤ R'.coeff H := by
    refine MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (hcart R) (V := ⊤)
      (fun P _ => ?_) hR' H
      ⟨H.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' H, trivial⟩
    rw [hR, coeff_sum_single]
    split_ifs <;> norm_num
  rw [h.eq (hcart _) hsum, DivisorWithCoeffs.coeff_add]
  omega

/-- A prime divisor contained in the coefficient-one locus is a coefficient-one component. -/
private theorem coeff_eq_one_of_support_subset {B : RDivisor X} {G : Mori.PrimeDivisor X}
    (h : (G.support : Set X) ⊆ oneLocus B) : B.coeff G = 1 := by
  obtain ⟨D, hD, hGD⟩ := h (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' G)
  rwa [MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset
    (support_subset_of_genericPoint_mem G
      (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support D) hGD)]

/-- Precomposing a normal variety with an isomorphism gives a normal variety. -/
private theorem isNormalVariety_comp_iso {Y Y' : Scheme.{u}}
    {s : Y ⟶ Spec (.of k)} (h : IsNormalVariety k s) (e : Y' ⟶ Y) [IsIso e] :
    IsNormalVariety k (e ≫ s) := by
  haveI : AlgebraicGeometry.IsVariety k s := h.1
  haveI : IsNormal Y := h.2
  haveI : IsIntegral Y := h.1.toIsIntegral
  haveI : Nonempty Y' := ⟨(inv e) (Nonempty.some (inferInstance : Nonempty Y))⟩
  haveI : IsIntegral Y' := isIntegral_of_isOpenImmersion e
  refine ⟨{}, ⟨fun y => ?_, fun y => ?_⟩⟩
  · haveI : IsIso (e.stalkMap y) := IsOpenImmersion.instIsIsoCommRingCatStalkMap e y
    haveI := IsNormal.stalk_isDomain (X := Y) (e y)
    exact MulEquiv.isDomain _ (asIso (e.stalkMap y)).commRingCatIsoToRingEquiv.symm.toMulEquiv
  · haveI : IsIso (e.stalkMap y) := IsOpenImmersion.instIsIsoCommRingCatStalkMap e y
    haveI := IsNormal.stalk_normal (X := Y) (e y)
    exact IsIntegrallyClosed.of_equiv (asIso (e.stalkMap y)).commRingCatIsoToRingEquiv

/-- Under an isomorphism `e` with `e(η_H) = η_P`, a point lies on `H` exactly when its image lies
on `P`. -/
private theorem mem_support_iff_of_isIso {Y Y' : Scheme.{u}} (e : Y' ⟶ Y) [IsIso e]
    {H : Mori.PrimeDivisor Y'} {P : Mori.PrimeDivisor Y} (hHP : e H.genericPoint = P.genericPoint)
    (z : Y') : z ∈ (H.support : Set Y') ↔ e z ∈ (P.support : Set Y) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure,
    ← specializes_iff_mem_closure]
  have h := e.isOpenEmbedding.isInducing.specializes_iff (x := H.genericPoint) (y := z)
  rw [hHP] at h
  exact h.symm

/-- Under an isomorphism `e` with `e(η_H) = η_P`, `H` lies in `e⁻¹ C` exactly when `P` lies in the
closed set `C`. -/
private theorem support_subset_preimage_iff_of_isIso {Y Y' : Scheme.{u}} (e : Y' ⟶ Y) [IsIso e]
    {H : Mori.PrimeDivisor Y'} {P : Mori.PrimeDivisor Y} (hHP : e H.genericPoint = P.genericPoint)
    {C : Set Y} (hC : IsClosed C) : (H.support : Set Y') ⊆ e ⁻¹' C ↔ (P.support : Set Y) ⊆ C := by
  refine ⟨fun hH => support_subset_of_genericPoint_mem _ hC ?_,
    fun hPC z hz => hPC ((mem_support_iff_of_isIso e hHP z).mp hz)⟩
  rw [← hHP]
  exact hH (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' H)

end Setup

section Steps

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {B : RDivisor X}

/-- The base of the induction: the identity, with any marked point. -/
private theorem isAmpleModel_id (hX : Mori.IsProjectiveVariety k sX) (hXs : IsSmoothScheme sX)
    (hB : B.IsSNC sX) (x : X) : IsAmpleModel sX B (𝟙 X) x := by
  classical
  haveI : AlgebraicGeometry.IsVariety k sX := hX.toIsVariety
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff _).1 hXs
  -- the coefficient-one components
  set S1 := B.support.filter (fun D => B.coeff D = 1) with hS1
  have hS1mem : ∀ D, D ∈ S1 ↔ B.coeff D = 1 := fun D => by
    rw [hS1, Finset.mem_filter, Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply]
    exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact one_ne_zero, h⟩⟩
  have hT : (∑ D ∈ S1, Finsupp.single D (1 : ℤ) : Divisor X).IsSNC sX := by
    refine hB.of_support_subset fun D hD => ?_
    have h1 := Finsupp.mem_support_iff.mp hD
    rw [← DivisorWithCoeffs.coeff_apply, coeff_sum_single] at h1
    split_ifs at h1 with h2
    · exact (Finset.mem_filter.mp h2).1
    · exact absurd rfl h1
  have hlocus : oneLocus B =
      ⋃ F ∈ (∑ D ∈ S1, Finsupp.single D (1 : ℤ) : Divisor X).support, (F.support : Set X) := by
    ext y
    simp only [oneLocus, Set.mem_setOf_eq, Set.mem_iUnion, Finsupp.mem_support_iff,
      ← DivisorWithCoeffs.coeff_apply, coeff_sum_single]
    refine ⟨fun ⟨D, hD, hy⟩ => ⟨D, by simp [(hS1mem D).mpr hD], hy⟩, fun ⟨D, hD, hy⟩ => ?_⟩
    split_ifs at hD with h
    · exact ⟨D, (hS1mem D).mp h, hy⟩
    · exact absurd rfl hD
  have hsnc : IsSNCClosedSubset sX (oneLocus B) := by
    rw [hlocus]
    exact MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC sX hT
  refine ⟨by rw [Category.id_comp]; exact ⟨hX.toIsVariety, inferInstance⟩,
    by rw [Category.id_comp]; exact hXs, inferInstance, by rw [Category.id_comp]; exact hsnc,
    inferInstance, inferInstance, inferInstance, ?_⟩
  -- the divisor `∑_{coeff_D B = 1, x ∉ D} D`
  set S := S1.filter (fun D => x ∉ D.support) with hS
  refine ⟨∑ D ∈ S, Finsupp.single D (1 : ℚ), ?_, ?_, fun D hD => ?_, fun D hD hxD => ?_⟩
  · intro E
    simp only [← DivisorWithCoeffs.coeff_apply]
    rw [DivisorWithCoeffs.coeff_zero, coeff_sum_single]
    split_ifs <;> norm_num
  · set L : Divisor X := ∑ D ∈ S, Finsupp.single D (1 : ℤ)
    have hLc : L.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hXs L
    refine ⟨1, one_pos, L, hLc, ?_, isRelativelyAmple_of_isIso _ hLc⟩
    ext E
    rw [Divisor.coeff_toQDivisor, coeff_sum_single, DivisorWithCoeffs.coeff_smul,
      coeff_sum_single]
    split_ifs <;> simp
  · rw [coeff_sum_single] at hD
    split_ifs at hD with h
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
      exact ⟨fun y hy => ⟨D, (hS1mem D).mp h1, hy⟩, h2⟩
    · exact absurd rfl hD
  · rw [coeff_sum_single, if_pos (Finset.mem_filter.mpr ⟨(hS1mem D).mpr
      (coeff_eq_one_of_support_subset hD), hxD⟩)]
    exact one_pos

/-- The invariant is stable under precomposition with isomorphisms. -/
private theorem IsAmpleModel.comp_iso {Y Y' : Scheme.{u}} (e : Y' ⟶ Y) [IsIso e] (q : Y ⟶ X)
    (y : Y') (h : IsAmpleModel sX B q (e y)) : IsAmpleModel sX B (e ≫ q) y := by
  classical
  haveI := h.proper
  have hn : IsNormalVariety k ((e ≫ q) ≫ sX) := by
    rw [Category.assoc]; exact isNormalVariety_comp_iso h.normal e
  haveI : AlgebraicGeometry.IsVariety k (q ≫ sX) := h.normal.1
  haveI : IsIntegral Y := h.normal.1.toIsIntegral
  haveI : IsNormal Y := h.normal.2
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (q ≫ sX)
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (q ≫ sX)
  haveI : AlgebraicGeometry.IsVariety k ((e ≫ q) ≫ sX) := hn.1
  haveI : IsIntegral Y' := hn.1.toIsIntegral
  haveI : IsNormal Y' := hn.2
  haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian ((e ≫ q) ≫ sX)
  haveI : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace ((e ≫ q) ≫ sX)
  haveI : Smooth (q ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 h.smooth
  have hsm : IsSmoothScheme ((e ≫ q) ≫ sX) := by
    rw [Category.assoc]; exact (MMP.Mori.isSmoothScheme_iff _).2 inferInstance
  refine ⟨hn, hsm, inferInstance, ?_, inferInstance, inferInstance, inferInstance, ?_⟩
  · rw [Category.assoc]
    exact h.snc.preimage_of_isIso e
  obtain ⟨_, _, _, F, hF0, ⟨N, hN, L, hLc, hLF, hLa⟩, hFs, hFp⟩ := h.ample
  obtain ⟨L', hL'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant e hLc
  have h0c : (0 : Divisor Y').IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm 0
  obtain ⟨n₀, hn₀⟩ := exists_isRelativelyAmple_add_nsmul e q h0c (isRelativelyAmple_of_isIso e h0c)
    hLc hLa hL'
  set n := n₀ + 1 with hn
  have hnN : (0 : ℚ) < ((n * N : ℕ) : ℚ) := by exact_mod_cast Nat.mul_pos (Nat.succ_pos _) hN
  set F' : QDivisor Y' := ((n * N : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (0 + n • L') with hF'
  -- the prime divisor of `Y` under a prime divisor of `Y'`
  have hcoh : ∀ H : Mori.PrimeDivisor Y', Order.coheight (e H.genericPoint) = 1 := fun H => by
    rw [Topology.IsOpenEmbedding.coheight_eq _ e.isOpenEmbedding, H.coheight_genericPoint]
  let P : Mori.PrimeDivisor Y' → Mori.PrimeDivisor Y := fun H =>
    MMP.Fourfold.SNCWeight.StratumBlowup.primeOfCoheightOne _ (hcoh H)
  have hP : ∀ H, e H.genericPoint = (P H).genericPoint := fun H =>
    (MMP.Fourfold.SNCWeight.StratumBlowup.genericPoint_primeOfCoheightOne _ _).symm
  have hcoeff : ∀ H, F'.coeff H = F.coeff (P H) := by
    intro H
    haveI : IsIso (e.stalkMap H.genericPoint) :=
      IsOpenImmersion.instIsIsoCommRingCatStalkMap e H.genericPoint
    have h1 := coeff_isPullback_eq_of_isIso hLc hL' H (P H) (hP H)
    have h2 := congrArg (fun D : QDivisor Y => D.coeff (P H)) hLF
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h2
    rw [hF', DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_zero, h1, smul_eq_mul, nsmul_eq_mul]
    have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_pos n₀).ne'
    push_cast
    rw [h2, Int.cast_natCast]
    field_simp
    ring
  have hbd : ∀ H : Mori.PrimeDivisor Y', (H.support : Set Y') ⊆ (e ≫ q) ⁻¹' oneLocus B ↔
      ((P H).support : Set Y) ⊆ q ⁻¹' oneLocus B := fun H =>
    support_subset_preimage_iff_of_isIso e (hP H) h.snc.1
  refine ⟨F', fun H => ?_, ⟨n * N, Nat.mul_pos (Nat.succ_pos _) hN, 0 + n • L',
    h0c.add ((hL'.isCartier hLc).nsmul n), ?_, hn₀ n (Nat.le_succ _)⟩, fun H hH => ?_,
    fun H hH hyH => ?_⟩
  · change (0 : QDivisor Y').coeff H ≤ F'.coeff H
    rw [hcoeff, DivisorWithCoeffs.coeff_zero]
    exact hF0 (P H)
  · ext E
    rw [hF', DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      smul_eq_mul]
    push_cast
    have : ((n : ℚ) * N) ≠ 0 := by exact_mod_cast hnN.ne'
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_pos n₀).ne'
    have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  · rw [hcoeff] at hH
    obtain ⟨h1, h2⟩ := hFs (P H) hH
    exact ⟨(hbd H).mpr h1, fun hy => h2 ((mem_support_iff_of_isIso e (hP H) y).mp hy)⟩
  · rw [hcoeff]
    exact hFp (P H) ((hbd H).mp hH) fun hy => hyH ((mem_support_iff_of_isIso e (hP H) y).mpr hy)

/-- The invariant passes from `(q, π y)` to `(π ≫ q, y)` along the blow-up `π` of a reduced
stratum `Z` of the coefficient-one boundary of `q`. -/
private theorem IsAmpleModel.blowUpToBase_comp {Y : Scheme.{u}} (q : Y ⟶ X)
    (Z : Y.IdealSheafData) (y : AlgebraicGeometry.blowUp Z)
    (h : IsAmpleModel sX B q (blowUpToBase Z y))
    (hJ : ∃ J : Set (Set Y), J.Nonempty ∧ J ⊆ componentsOf (q ⁻¹' oneLocus B) ∧
      (Z.support : Set Y) ∈ componentsOf (⋂₀ J))
    (hZ : Z = Scheme.IdealSheafData.vanishingIdeal Z.support)
    (hy : blowUpToBase Z y ∈ Z.support) : IsAmpleModel sX B (blowUpToBase Z ≫ q) y := by
  classical
  -- the scheme `Y`
  haveI := h.proper
  haveI : AlgebraicGeometry.IsVariety k (q ≫ sX) := h.normal.1
  haveI : IsIntegral Y := h.normal.1.toIsIntegral
  haveI : IsNormal Y := h.normal.2
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (q ≫ sX)
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (q ≫ sX)
  haveI : IsNoetherian Y := {}
  haveI : Smooth (q ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 h.smooth
  set S := q ⁻¹' oneLocus B with hS
  have hSsnc : IsSNCClosedSubset (q ≫ sX) S := h.snc
  set π := blowUpToBase Z with hπ
  set x := π y with hx
  -- the components through the centre
  obtain ⟨J, hJne, hJS, hZJ⟩ := hJ
  obtain ⟨T, hTne, hTS, hJT⟩ := exists_finset_sInter_eq hSsnc hJne hJS
  rw [hJT] at hZJ
  have hsncT := isSNC_sum_single_of_support_subset h.smooth hSsnc T hTS
  obtain ⟨hZsm, hZst⟩ := stratum_component (q ≫ sX) hsncT hZJ
  rw [← hZ] at hZsm hZst
  have hZT : ∀ P ∈ T, (Z.support : Set Y) ⊆ P.support := fun P hP =>
    hZJ.1.2.trans (Set.biInter_subset_of_mem hP)
  have hirr : IsIrreducible (Z.support : Set Y) := hZJ.1.1
  obtain ⟨P₀, hP₀⟩ := hTne
  have hZS : (Z.support : Set Y) ⊆ S := (hZT P₀ hP₀).trans (hTS P₀ hP₀)
  have hc1 := one_le_codimension_of_subset_support hirr P₀ (hZT P₀ hP₀)
  have hsb : IsSmoothBlowup (q ≫ sX) Z := ⟨h.smooth, hZsm⟩
  have hZbot : Z ≠ ⊥ := MMP.Threefold.Resolution.ne_bot_of_one_le_codimension Z hirr hc1
  -- the blow-up
  obtain ⟨hvar, hproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational (q ≫ sX) Z hZbot
  have hsmB := (isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal (q ≫ sX) Z hsb
    hirr hc1).1
  haveI := MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension Z hirr hc1
  haveI := MMP.Threefold.Resolution.isDominant_blowUpToBase Z hirr hc1
  haveI : Smooth (π ≫ q ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hsmB
  haveI : IsLocallyNoetherian (AlgebraicGeometry.blowUp Z) :=
    isLocallyNoetherian_of_smooth (π ≫ q ≫ sX)
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI : IsNormal (AlgebraicGeometry.blowUp Z) := AlgebraicGeometry.isNormal_of_smooth (π ≫ q ≫ sX)
  haveI : IsProper π := hproj.isProper
  haveI : AlgebraicGeometry.IsVariety k (π ≫ q ≫ sX) := hvar
  haveI : CompactSpace (AlgebraicGeometry.blowUp Z) :=
    QuasiCompact.compactSpace_of_compactSpace (π ≫ q ≫ sX)
  have hN : IsNormalVariety k ((π ≫ q) ≫ sX) := by
    rw [Category.assoc]
    exact ⟨hvar, inferInstance⟩
  have hsm' : IsSmoothScheme ((π ≫ q) ≫ sX) := by rwa [Category.assoc]
  have hpre : ∀ z : AlgebraicGeometry.blowUp Z, (π ≫ q) z = q (π z) := fun z => rfl
  refine ⟨hN, hsm', inferInstance, ?_, inferInstance, inferInstance, inferInstance, ?_⟩
  · have hZsnc := hasSNCWith_of_stalk_eq hSsnc ⟨P₀, hP₀⟩ hTS hZT hZst
    have := MMP.Resolution.isSNCClosedSubset_totalTransformStep (q ≫ sX) h.smooth hSsnc hZsnc
    rw [MMP.Fourfold.SNCWeight.SNCBlowup.totalTransformStep_eq hSsnc.1 hZS] at this
    rwa [Category.assoc]
  -- the exceptional divisor
  set G := MMP.Fourfold.SNCWeight.StratumBlowup.excE (q ≫ sX) hsb hirr hc1 with hG
  have hGsupp : (G.support : Set (AlgebraicGeometry.blowUp Z)) = π ⁻¹' Z.support :=
    MMP.Fourfold.SNCWeight.StratumBlowup.coe_support_excE (q ≫ sX) hsb hirr hc1
  have hyG : y ∈ (G.support : Set (AlgebraicGeometry.blowUp Z)) := by rwa [hGsupp]
  have hπG : π G.genericPoint ∈ (Z.support : Set Y) := by
    rw [← Set.mem_preimage, ← hGsupp]
    exact MMP.Positivity.PrimeDivisor.genericPoint_mem_support' G
  -- the downstairs datum
  obtain ⟨_, _, _, F, hF0, ⟨N, hNpos, L, hLc, hLF, hLa⟩, hFs, hFp⟩ := h.ample
  have hLF' : ∀ P, (L.coeff P : ℚ) = N * F.coeff P := fun P => by
    simpa [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] using
      congrArg (fun D : QDivisor Y => D.coeff P) hLF
  -- the boundary primes through `x` whose strict transform misses `y`
  have hfinS := finite_setOf_support_subset hSsnc
  set C0 := hfinS.toFinset.filter (fun P : Mori.PrimeDivisor Y => x ∈ P.support ∧
    ∀ hP : P.genericPoint ∉ (Z.support : Set Y),
      y ∉ ((MMP.Fourfold.SNCWeight.StratumBlowup.strictPrime Z P hP).support :
        Set (AlgebraicGeometry.blowUp Z))) with hC0
  have hmemC0 : ∀ P, P ∈ C0 ↔ (P.support : Set Y) ⊆ S ∧ x ∈ P.support ∧
      ∀ hP : P.genericPoint ∉ (Z.support : Set Y),
        y ∉ ((MMP.Fourfold.SNCWeight.StratumBlowup.strictPrime Z P hP).support :
          Set (AlgebraicGeometry.blowUp Z)) := fun P => by
    rw [hC0, Finset.mem_filter, Set.Finite.mem_toFinset]; rfl
  obtain ⟨P₁, hP₁T, hP₁⟩ := exists_notMem_strictPrime (q ≫ sX) hsb hirr hc1 hsncT hZT hZst y hy
  have hP₁C : P₁ ∈ C0 := (hmemC0 P₁).mpr ⟨hTS P₁ hP₁T, hZT P₁ hP₁T hy, hP₁⟩
  set C₀ : Divisor Y := ∑ P ∈ C0, Finsupp.single P 1 with hC₀
  have hC₀c : C₀.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme h.smooth C₀
  -- pull-backs
  obtain ⟨C₀', hC₀'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant π hC₀c
  obtain ⟨L', hL'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant π hLc
  have hC₀'c := hC₀'.isCartier hC₀c
  have hL'c := hL'.isCartier hLc
  set m := C₀'.coeff G with hm
  have hm1 : 1 ≤ m := one_le_coeff_isPullback_sum_single
    (MMP.Fourfold.isCartier_of_isSmoothScheme h.smooth) hP₁C G (hZT P₁ hP₁T hπG) hC₀'
  -- `π^*C₀ - mG` is `π`-ample
  have hGc :
    Divisor.IsCartier (-(Finsupp.single G (1 : ℤ) : Divisor (AlgebraicGeometry.blowUp Z))) :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hsmB _
  have hGa := isRelativelyAmple_neg_single_of_idealSheaf_eq (q ≫ sX) Z hvar hsmB G rfl hGc
  have hmGa := isRelativelyAmple_nsmul hGc hGa m.toNat (by omega)
  have hLneg := MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback π (hGc.nsmul _) hmGa
    hC₀c hC₀' hC₀'c
  -- Stacks 0C4K
  obtain ⟨n₀, hn₀⟩ := exists_isRelativelyAmple_add_nsmul π q _ hLneg hLc hLa hL'
  set n := n₀ + 1 with hn
  set D' : Divisor (AlgebraicGeometry.blowUp Z) :=
    m.toNat • (-(Finsupp.single G (1 : ℤ))) + C₀' + n • L' with hD'
  have hnN : (0 : ℚ) < ((n * N : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos (Nat.succ_pos _) hNpos
  set F' : QDivisor (AlgebraicGeometry.blowUp Z) :=
    ((n * N : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor D' with hF'
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_pos n₀).ne'
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hF'coeff : ∀ H, F'.coeff H = ((n * N : ℕ) : ℚ)⁻¹ * (D'.coeff H : ℚ) := fun H => by
    rw [hF', DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul]
  -- coefficients along the exceptional divisor
  have hL'G : L'.coeff G = 0 := by
    refine coeff_isPullback_eq_zero_of_forall hLc hL' G fun Γ hΓ => ?_
    have hxΓ : x ∈ (Γ.support : Set Y) := by
      have hsub : (Z.support : Set Y) ⊆ Γ.support := by
        rw [← MMP.Fourfold.SNCWeight.BlowupCrepancy.closure_map_genericPoint_excE (q ≫ sX) hsb
          hirr hc1]
        exact closure_minimal (Set.singleton_subset_iff.mpr hΓ)
          (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support Γ)
      exact hsub hy
    by_contra hne
    have hFne : F.coeff Γ ≠ 0 := fun h0 => hne (by
      have : (L.coeff Γ : ℚ) = 0 := by rw [hLF', h0, mul_zero]
      exact_mod_cast this)
    exact (hFs Γ hFne).2 hxΓ
  have hD'G : D'.coeff G = 0 := by
    rw [hD', DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_smul, hL'G, DivisorWithCoeffs.coeff_neg,
      DivisorWithCoeffs.coeff_single_self, ← hm]
    simp only [smul_eq_mul, nsmul_eq_mul, mul_neg, mul_one, mul_zero, add_zero]
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  -- coefficients along the other prime divisors
  have hD'H : ∀ H (hH : H ≠ G), D'.coeff H = C₀.coeff
      (MMP.Fourfold.SNCWeight.StratumBlowup.downPrime (q ≫ sX) hsb hirr hc1 hH) +
        n * L.coeff (MMP.Fourfold.SNCWeight.StratumBlowup.downPrime (q ≫ sX) hsb hirr hc1 hH) := by
    intro H hH
    have hnot := MMP.Fourfold.SNCWeight.StratumBlowup.map_genericPoint_notMem_of_ne (q ≫ sX) hsb
      hirr hc1 hH
    haveI : IsIso (π.stalkMap H.genericPoint) :=
      MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus _
        (MMP.Fourfold.SNCWeight.StratumBlowup.mem_biregularLocus_of_notMem Z hnot)
    have hgen := (MMP.Fourfold.SNCWeight.StratumBlowup.genericPoint_downPrime (q ≫ sX) hsb hirr
      hc1 hH).symm
    rw [hD', DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_neg,
      DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hH),
      coeff_isPullback_eq_of_isIso hC₀c hC₀' H _ hgen,
      coeff_isPullback_eq_of_isIso hLc hL' H _ hgen]
    simp [nsmul_eq_mul]
  -- the strict transforms
  have hdown : ∀ H (hH : H ≠ G) (z : AlgebraicGeometry.blowUp Z),
      z ∈ (H.support : Set (AlgebraicGeometry.blowUp Z)) →
      π z ∈ ((MMP.Fourfold.SNCWeight.StratumBlowup.downPrime (q ≫ sX) hsb hirr hc1 hH).support :
        Set Y) := fun H hH z hz =>
    MMP.Fourfold.SNCWeight.CentreLifting.map_mem_downPrime (q ≫ sX) hsb hirr hc1 hH hz
  have hstrict : ∀ H (hH : H ≠ G), ∃ hP : (MMP.Fourfold.SNCWeight.StratumBlowup.downPrime
      (q ≫ sX) hsb hirr hc1 hH).genericPoint ∉ (Z.support : Set Y),
      MMP.Fourfold.SNCWeight.StratumBlowup.strictPrime Z _ hP = H := fun H hH => by
    have hP : (MMP.Fourfold.SNCWeight.StratumBlowup.downPrime (q ≫ sX) hsb hirr hc1
        hH).genericPoint ∉ (Z.support : Set Y) := by
      rw [MMP.Fourfold.SNCWeight.StratumBlowup.genericPoint_downPrime]
      exact MMP.Fourfold.SNCWeight.StratumBlowup.map_genericPoint_notMem_of_ne (q ≫ sX) hsb hirr
        hc1 hH
    exact ⟨hP, MMP.Fourfold.SNCWeight.CentreLifting.strictPrime_downPrime (q ≫ sX) hsb hirr hc1
      hH hP⟩
  have hC₀nn : ∀ P, 0 ≤ C₀.coeff P := fun P => by
    rw [hC₀, coeff_sum_single]; split_ifs <;> norm_num
  have hLnn : ∀ P, (0 : ℚ) ≤ L.coeff P := fun P => by
    rw [hLF']
    exact mul_nonneg (Nat.cast_nonneg _) (hF0 P)
  refine ⟨F', fun H => ?_, ⟨n * N, Nat.mul_pos (Nat.succ_pos _) hNpos, D',
    ((hGc.nsmul _).add hC₀'c).add (hL'c.nsmul n), ?_, hn₀ n (Nat.le_succ _)⟩,
    fun H hH => ?_, fun H hH hyH => ?_⟩
  · -- effectivity
    change (0 : QDivisor (AlgebraicGeometry.blowUp Z)).coeff H ≤ F'.coeff H
    rw [DivisorWithCoeffs.coeff_zero, hF'coeff]
    by_cases hHG : H = G
    · rw [hHG, hD'G]; simp
    · rw [hD'H H hHG]
      refine mul_nonneg (inv_nonneg.mpr hnN.le) ?_
      push_cast
      exact add_nonneg (by exact_mod_cast hC₀nn _) (mul_nonneg (Nat.cast_nonneg _) (hLnn _))
  · -- the multiple
    ext E
    rw [hF', DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      smul_eq_mul]
    push_cast
    field_simp
  · -- the support
    have hHG : H ≠ G := by
      rintro rfl
      rw [hF'coeff, hD'G] at hH
      simp at hH
    rw [hF'coeff, hD'H H hHG] at hH
    set P := MMP.Fourfold.SNCWeight.StratumBlowup.downPrime (q ≫ sX) hsb hirr hc1 hHG with hPdef
    have hor : C₀.coeff P ≠ 0 ∨ F.coeff P ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hH
      rw [hcon.1]
      have : (L.coeff P : ℚ) = 0 := by rw [hLF', hcon.2, mul_zero]
      push_cast
      rw [this]
      simp
    have hPS : (P.support : Set Y) ⊆ S ∧ ∀ z ∈ (H.support : Set (AlgebraicGeometry.blowUp Z)),
        z ≠ y := by
      rcases hor with h1 | h1
      · have hPC : P ∈ C0 := by
          by_contra hn
          apply h1
          rw [hC₀, coeff_sum_single, if_neg hn]
        obtain ⟨hPS, -, hPy⟩ := (hmemC0 P).mp hPC
        obtain ⟨hP, hPH⟩ := hstrict H hHG
        refine ⟨hPS, fun z hz hzy => hPy hP ?_⟩
        rwa [hPH, ← hzy]
      · obtain ⟨hPS, hxP⟩ := hFs P h1
        refine ⟨hPS, fun z hz hzy => hxP ?_⟩
        simpa [hzy] using hdown H hHG z hz
    refine ⟨fun z hz => ?_, fun hy' => hPS.2 y hy' rfl⟩
    rw [Set.mem_preimage, hpre]
    exact hPS.1 (hdown H hHG z hz)
  · -- positivity
    have hHG : H ≠ G := by
      rintro rfl
      exact hyH hyG
    rw [hF'coeff, hD'H H hHG]
    set P := MMP.Fourfold.SNCWeight.StratumBlowup.downPrime (q ≫ sX) hsb hirr hc1 hHG with hPdef
    have hPS : (P.support : Set Y) ⊆ S := by
      refine support_subset_of_genericPoint_mem P hSsnc.1 ?_
      rw [hPdef, MMP.Fourfold.SNCWeight.StratumBlowup.genericPoint_downPrime]
      have := hH (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' H)
      rwa [Set.mem_preimage, hpre] at this
    refine mul_pos (inv_pos.mpr hnN) ?_
    push_cast
    by_cases hxP : x ∈ (P.support : Set Y)
    · have hPC : P ∈ C0 := by
        refine (hmemC0 P).mpr ⟨hPS, hxP, fun hP => ?_⟩
        obtain ⟨hP', hPH⟩ := hstrict H hHG
        rwa [hPH]
      have h1 : C₀.coeff P = 1 := by rw [hC₀, coeff_sum_single, if_pos hPC]
      rw [h1]
      push_cast
      exact add_pos_of_pos_of_nonneg one_pos (mul_nonneg (Nat.cast_nonneg _) (hLnn _))
    · have hFP := hFp P hPS hxP
      have hLP : (0 : ℚ) < L.coeff P := by
        rw [hLF']; exact mul_pos (by exact_mod_cast hNpos) hFP
      exact add_pos_of_nonneg_of_pos (by exact_mod_cast hC₀nn _)
        (mul_pos (by exact_mod_cast Nat.succ_pos n₀) hLP)

end Steps

section Final

variable {k : Type u} [Field k] {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]

/-- A positive rational `δ < m / (c n)` is `a / b` with `0 < a`, `0 < b` and `a c n ≤ b m`. -/
private theorem exists_eq_div_of_lt_div {δ : ℚ} (hδ : 0 < δ) {m c n : ℕ} (hc : 0 < c)
    (hn : 1 ≤ n) (hδ₀ : δ < m / (c * n)) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ δ = a / b ∧ a * c * n ≤ b * m := by
  set a : ℕ := δ.num.toNat with ha
  set b : ℕ := δ.den with hb
  have hnum : (δ.num : ℚ) = a := by
    rw [ha]
    exact_mod_cast (Int.toNat_of_nonneg (Rat.num_nonneg.mpr hδ.le)).symm
  have hδab : δ = (a : ℚ) / b := by rw [← hnum, hb, Rat.num_div_den]
  have hb0 : 0 < b := δ.den_pos
  have ha0 : 0 < a := by
    have := Rat.num_pos.mpr hδ
    omega
  refine ⟨a, b, ha0, hb0, hδab, ?_⟩
  have h1 : (a : ℚ) / b < m / (c * n) := hδab ▸ hδ₀
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb0
  have hcq : (0 : ℚ) < c * n := by
    have : (1 : ℚ) ≤ n := by exact_mod_cast hn
    have : (0 : ℚ) < c := by exact_mod_cast hc
    positivity
  rw [div_lt_div_iff₀ hbq hcq] at h1
  have : ((a * c * n : ℕ) : ℚ) < (b * m : ℕ) := by push_cast; linarith
  exact (Nat.cast_lt.mp this).le

/-- If `L + jM` is `f`-ample for every `j ≥ n`, then so is `sL + rM` whenever `0 < s` and
`sn ≤ r`: write `sL + rM = (s - ρ)(L + jM) + ρ(L + (j + 1)M)` with `r = sj + ρ`. -/
private theorem isRelativelyAmple_nsmul_add_nsmul {V S : Scheme.{u}} [CompactSpace V]
    [IsLocallyNoetherian V] [IsNormal V] {f : V ⟶ S} [QuasiCompact f] [IsSeparated f]
    {L M : Divisor V} (hL : L.IsCartier) (hM : M.IsCartier) {n : ℕ}
    (hK : ∀ j : ℕ, n ≤ j → (L + j • M).IsRelativelyAmple f (hL.add (hM.nsmul j)))
    {s r : ℕ} (hs0 : 0 < s) (hsr : s * n ≤ r) :
    (s • L + r • M).IsRelativelyAmple f ((hL.nsmul s).add (hM.nsmul r)) := by
  set j := r / s with hj
  set ρ := r % s with hρ
  have hjn : n ≤ j := (Nat.le_div_iff_mul_le hs0).mpr (by rw [mul_comm]; exact hsr)
  have hrj : r = s * j + ρ := (Nat.div_add_mod r s).symm
  have hρs : ρ < s := Nat.mod_lt _ hs0
  have hD : s • L + r • M = (s - ρ) • (L + j • M) + ρ • (L + (j + 1) • M) := by
    rw [hrj]
    ext E
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, nsmul_eq_mul]
    push_cast [Nat.cast_sub hρs.le]
    ring
  have hK1 := hK j hjn
  rcases Nat.eq_zero_or_pos ρ with h0 | hρ0
  · refine isRelativelyAmple_of_eq ?_ _ _ (isRelativelyAmple_nsmul _ hK1 s hs0)
    rw [hD, h0, Nat.sub_zero, zero_smul, add_zero]
  · refine isRelativelyAmple_of_eq hD.symm _ _ (isRelativelyAmple_add _
      (isRelativelyAmple_nsmul _ hK1 (s - ρ) (Nat.sub_pos_of_lt hρs)) _
      (isRelativelyAmple_nsmul _ (hK (j + 1) (hjn.trans (Nat.le_succ j))) ρ hρ0))

/-- **Ampleness of `p^*A + δF`.** If `F` is `p`-ample and `A` is ample on `X`, then `A' + δF` is
ample for every sufficiently small rational `δ > 0`, where `A' = p^*A`. -/
private theorem exists_hasRelativelyAmpleMultiple_add_smul (hX : Mori.IsProjectiveVariety k sX)
    (p : W ⟶ X) (hpv : AlgebraicGeometry.IsVariety k (p ≫ sX)) [IsProper p] {F : QDivisor W}
    (hF : F.HasRelativelyAmpleMultiple p) (A : QDivisor X) (hA : A.HasRelativelyAmpleMultiple sX)
    (hA0 : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ A.supp)
    (A' : QDivisor W) (hA' : QDivisor.IsPullback p A hA0 A') :
    ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 < δ → δ < δ₀ →
      (A' + δ • F).HasRelativelyAmpleMultiple (p ≫ sX) := by
  haveI : IsSeparated (p ≫ sX) := hpv.toIsSeparated
  haveI : QuasiCompact (p ≫ sX) := hpv.toQuasiCompact
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  obtain ⟨m, hm, L, hLc, hLF, hLa⟩ := hF
  obtain ⟨c, hc, M, hMc, hMA, hMa⟩ := hA
  obtain ⟨M', hM'A, hM'⟩ := hA' c hc M hMA hMc
  obtain ⟨n₀, hn₀⟩ := exists_isRelativelyAmple_add_nsmul p sX hLc hLa hMc hMa hM'
  have hM'c := hM'.isCartier hMc
  set n₁ := max n₀ 1 with hn₁
  have hn₁1 : 1 ≤ n₁ := le_max_right _ _
  have hK : ∀ j : ℕ, n₁ ≤ j → (L + j • M').IsRelativelyAmple (p ≫ sX)
      (hLc.add (hM'c.nsmul j)) := fun j hj => hn₀ j ((le_max_left _ _).trans hj)
  refine ⟨(m : ℚ) / (c * n₁), by positivity, fun δ hδ hδ₀ => ?_⟩
  obtain ⟨a, b, ha0, hb0, hδab, hsr⟩ := exists_eq_div_of_lt_div hδ hc hn₁1 hδ₀
  set s : ℕ := a * c with hs
  set r : ℕ := b * m with hr
  refine ⟨b * m * c, Nat.mul_pos (Nat.mul_pos hb0 hm) hc, s • L + r • M',
    (hLc.nsmul s).add (hM'c.nsmul r), ?_,
    isRelativelyAmple_nsmul_add_nsmul hLc hM'c hK (Nat.mul_pos ha0 hc) hsr⟩
  -- the coefficients
  rw [map_add, map_nsmul, map_nsmul, hLF, hM'A]
  ext E
  simp only [DivisorWithCoeffs.coeff_add, smul_eq_mul, hδab]
  change (s : ℚ) * ((m : ℤ) * F E) + (r : ℚ) * ((c : ℤ) * A' E) =
    ((b * m * c : ℕ) : ℤ) * (A' E + (a : ℚ) / b * F E)
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb0.ne'
  push_cast [hs, hr]
  field_simp
  ring

end Final

end MMP.Proof_lem_fourfold_stratum_blowup_ample_off_one_prime

namespace MMP.Fourfold

open MMP.Mori MMP.Resolution
open MMP.Proof_lem_fourfold_stratum_blowup_ample_off_one_prime

/-- **A relatively ample boundary divisor avoiding one exceptional prime.** Let `X` be a smooth
projective variety over an algebraically closed field `k` of characteristic zero, `B` an
effective snc boundary on `X` with coefficient-one locus `D₀`, `p : W ⟶ X` a composite of
blow-ups of strata of the coefficient-one boundary, and `E` a `p`-exceptional prime of `W` such
that every centre of the sequence contains the centre of `E` on the model it is blown up from.
Then there is an effective `p`-ample `ℚ`-divisor `F` supported in `p⁻¹(D₀)`, with
`coeff_E F = 0` and `coeff_D F > 0` for every other prime `D ⊆ p⁻¹(D₀)`.
For every ample `ℚ`-divisor `A` on `X` with pull-back `A'`, `A' + δF` is ample for all
sufficiently small rational `δ > 0`. -/
@[mmp "lem_fourfold_stratum_blowup_ample_off_one_prime"]
public theorem exists_hasRelativelyAmpleMultiple_coeff_eq_zero_of_stratumBlowups {k : Type u}
    [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (hX : Mori.IsProjectiveVariety k sX) (hXs : IsSmoothScheme sX)
    (B : RDivisor X) (hB0 : 0 ≤ B) (hB1 : ∀ P, B.coeff P ≤ 1) (hB : B.IsSNC sX)
    {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (p : W ⟶ X)
    (E : Mori.PrimeDivisor W) (hE : Mori.RationalMap.IsExceptional (X := W) p.toRationalMap E)
    (hp : ∀ P : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Y → Prop, (∀ x : X, P (𝟙 X) x) →
      (∀ {Y Y' : Scheme.{u}} (e : Y' ⟶ Y) [IsIso e] (q : Y ⟶ X) (y : Y'), P q (e y) →
        P (e ≫ q) y) →
      (∀ {Y : Scheme.{u}} (q : Y ⟶ X) (Z : Y.IdealSheafData) (y : blowUp Z),
        P q (blowUpToBase Z y) →
        (∃ J : Set (Set Y), J.Nonempty ∧
          J ⊆ componentsOf
            (q ⁻¹' {x | ∃ D : Mori.PrimeDivisor X, B.coeff D = 1 ∧ x ∈ D.support}) ∧
          (Z.support : Set Y) ∈ componentsOf (⋂₀ J)) →
        Z = Scheme.IdealSheafData.vanishingIdeal Z.support → blowUpToBase Z y ∈ Z.support →
        P (blowUpToBase Z ≫ q) y) → P p E.genericPoint) :
    ∃ F : QDivisor W, 0 ≤ F ∧ F.HasRelativelyAmpleMultiple p ∧ F.coeff E = 0 ∧
      (∀ D : Mori.PrimeDivisor W, F.coeff D ≠ 0 →
        D.support ⊆ p ⁻¹' {x | ∃ D : Mori.PrimeDivisor X, B.coeff D = 1 ∧ x ∈ D.support}) ∧
      (∀ D : Mori.PrimeDivisor W, D ≠ E →
        D.support ⊆ p ⁻¹' {x | ∃ D : Mori.PrimeDivisor X, B.coeff D = 1 ∧ x ∈ D.support} →
        0 < F.coeff D) ∧
      ∀ A : QDivisor X, A.HasRelativelyAmpleMultiple sX →
        ∀ (hA : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ A.supp)
          (A' : QDivisor W), QDivisor.IsPullback p A hA A' →
          ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 < δ → δ < δ₀ →
            (A' + δ • F).HasRelativelyAmpleMultiple (p ≫ sX) := by
  have hinv : IsAmpleModel sX B p E.genericPoint :=
    hp (fun q y => IsAmpleModel sX B q y) (isAmpleModel_id hX hXs hB)
      (fun e _ q y h => h.comp_iso e q y)
      (fun q Z y h hJ hZ hy => h.blowUpToBase_comp q Z y hJ hZ hy)
  obtain ⟨_, _, _, F, hF⟩ := hinv.ample
  obtain ⟨hF0, hFa, hFsupp, hFpos⟩ := hF
  haveI := hinv.proper
  refine ⟨F, hF0, hFa, ?_, fun D hD => (hFsupp D hD).1, fun D hDE hD => hFpos D hD ?_, ?_⟩
  · by_contra h
    exact (hFsupp E h).2 (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' E)
  · exact fun hED => hDE (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset
      (support_subset_of_genericPoint_mem E
        (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support D) hED)).symm
  · intro A hA hA0 A' hA'
    exact exists_hasRelativelyAmpleMultiple_add_smul hX p hinv.normal.1 hFa A hA hA0 A' hA'

end MMP.Fourfold
