module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.AlgebraicHartogsUnits

/-!
# Push-forward of `𝒪_Y(G)` for `G` effective with exceptional or small-image components

Let `h : X → Z` be a proper surjective morphism of normal varieties over an algebraically closed
field `k` of characteristic zero, with connected fibres, let `g : Y → X` be a proper birational
morphism from a normal variety `Y`, and put `f = h ∘ g`. Let `G` be an effective divisor on `Y`
each of whose components `Gᵢ` is either exceptional over `X` or has image `h(g(Gᵢ))` of
codimension at least two in `Z`. Then `f_* 𝒪_Y(G) = 𝒪_Z`: for every open `U ⊆ Z`, the natural
map `𝒪_Z(U) → 𝒪_Y(f⁻¹ U) → 𝒪_Y(G)(f⁻¹ U)` is bijective.

## Main results

* `MMP.Flips.bijective_structureSheafToDivisorialSheaf_app_comp`: `f_* 𝒪_Y(G) = 𝒪_Z`.
* `MMP.Flips.algebraMap_surjective_of_comap_injective`: an integral extension of a normal
  finitely generated algebra over an algebraically closed field of characteristic zero which is
  injective on spectra is surjective.
* `MMP.Flips.bijective_app_of_isFinite_of_injective`: a finite surjective injective morphism onto
  a normal integral scheme of finite type over such a field is bijective on sections over every
  nonempty affine open.
* `MMP.Flips.isIso_of_isFinite_of_injective`: a finite surjective injective morphism from an
  integral scheme onto a normal variety over such a field is an isomorphism.

## Implementation notes

The equality `f_* 𝒪_Y(G) = 𝒪_Z` is the statement that the canonical map
`𝒪_Z → f_* 𝒪_Y → f_* 𝒪_Y(G)`, built from `f^♯` and
`MMP.Mori.Divisor.structureSheafToDivisorialSheaf` (defined since `G ≥ 0`), is bijective on the
sections over every open of `Z`. The varieties `X` and `Y` carry the structure morphisms
`h ≫ sZ` and `g ≫ h ≫ sZ`, so that `h` and `g` are morphisms over `k`. The codimension of the
irreducible closed set `h(g(Gᵢ))` is the coheight of its generic point `h(g(η_{Gᵢ}))`.
"Connected fibres" is topological connectedness of every fibre `h⁻¹(z)`; over a field that is
not algebraically closed, or in positive characteristic, this does not force `h_* 𝒪_X = 𝒪_Z`
(a purely inseparable or a nontrivial finite field extension is a counterexample with `Y = X`
and `G = 0`), which is why `k` is assumed algebraically closed of characteristic zero.

The proof follows the source. First `h_* 𝒪_X = 𝒪_Z`: in the Stein factorization
`h = s ∘ h'` the finite map `s` is injective (its fibres are the connected components of the
fibres of `h`) and surjective onto the normal `Z`; an injective finite map onto a normal variety
over an algebraically closed field of characteristic zero is an isomorphism. Locally, for
`A = 𝒪_Z(U)` integrally closed and `B = 𝒪(s⁻¹ U)` integral over `A`, an element `b ∈ B ∖ A` has
minimal polynomial `P ∈ A[T]` of degree `d ≥ 2`, separable over `Frac A`; at a maximal ideal `m`
of `A` not containing the resultant of `P` and `P'`, `P mod m` has `d` distinct roots in
`A/m = k`, which give `d` distinct primes of `A[b]` over `m`, and by lying over `d` distinct
primes of `B` over `m`, contradicting injectivity. Second, a section `φ` of `𝒪_Y(G)` over
`f⁻¹ U` has no poles along the strict transform of any prime divisor of `X` meeting
`h⁻¹(U ∖ W)`, where `W` is the union of the images `h(g(Gᵢ))` of codimension at least two; so it
is regular on `h⁻¹(U ∖ W)`, hence a section of `𝒪_Z` over `U ∖ W`, and it extends over `U` by
algebraic Hartogs on `Z`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], proof of 17.4
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace MMP.Flips

open MMP.Mori

/-! ### An injective finite morphism onto a normal variety in characteristic zero -/

/-- A root `a` of `minpoly A b` modulo a maximal ideal `m` gives a prime `Q` of `B` over `m`
at which `b ≡ a`. -/
private theorem exists_prime_over_of_isRoot {A B : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B] (b : B) (m : Ideal A) [m.IsMaximal] (a : A ⧸ m)
    (ha : ((minpoly A b).map (Ideal.Quotient.mk m)).IsRoot a) :
    ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap (algebraMap A B) = m ∧
      ∀ x : A, b - algebraMap A B x ∈ Q ↔ Ideal.Quotient.mk m x = a := by
  let S := Algebra.adjoin A ({b} : Set B)
  let e := minpoly.equivAdjoin (Algebra.IsIntegral.isIntegral (R := A) b)
  have hroot : (minpoly A b).eval₂ (Ideal.Quotient.mk m) a = 0 := by
    rwa [← Polynomial.eval_map]
  let ψ : S →+* A ⧸ m := (AdjoinRoot.lift (Ideal.Quotient.mk m) a hroot).comp e.symm.toRingHom
  have hψA (x : A) : ψ (algebraMap A S x) = Ideal.Quotient.mk m x := by
    change AdjoinRoot.lift _ a hroot (e.symm (algebraMap A S x)) = _
    rw [e.symm.commutes]
    exact AdjoinRoot.lift_of hroot
  have hb : (⟨b, Algebra.self_mem_adjoin_singleton A b⟩ : S) = e (AdjoinRoot.root _) := by
    apply Subtype.ext
    rw [minpoly.coe_equivAdjoin, ← AdjoinRoot.mk_X, AdjoinRoot.Minpoly.coe_toAdjoin_mk_X]
  have hψb : ψ ⟨b, Algebra.self_mem_adjoin_singleton A b⟩ = a := by
    change AdjoinRoot.lift _ a hroot (e.symm _) = _
    rw [hb, e.symm_apply_apply]
    exact AdjoinRoot.lift_root hroot
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have : Algebra.IsIntegral S B := Algebra.IsIntegral.tower_top A
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker ψ)
    (⊥ : Ideal B) (Ideal.comap_bot_le_of_injective _ Subtype.val_injective)
  replace hQc : Ideal.comap (algebraMap S B) Q = RingHom.ker ψ := hQc
  refine ⟨Q, hQ, ?_, fun x => ?_⟩
  · rw [IsScalarTower.algebraMap_eq A S B, ← Ideal.comap_comap, hQc]
    ext x
    rw [Ideal.mem_comap, RingHom.mem_ker, hψA, Ideal.Quotient.eq_zero_iff_mem]
  · have hmem : b - algebraMap A B x =
        algebraMap S B (⟨b, Algebra.self_mem_adjoin_singleton A b⟩ - algebraMap A S x) := by
      rw [map_sub, ← IsScalarTower.algebraMap_apply]
      rfl
    rw [hmem, ← Ideal.mem_comap, hQc, RingHom.mem_ker, map_sub, hψb, hψA, sub_eq_zero, eq_comm]

/-- A nonzero element of a reduced Jacobson ring lies outside some maximal ideal. -/
private theorem exists_isMaximal_notMem_of_ne_zero {A : Type*} [CommRing A] [IsReduced A]
    [IsJacobsonRing A] {c : A} (hc : c ≠ 0) : ∃ m : Ideal A, m.IsMaximal ∧ c ∉ m := by
  have h := IsJacobsonRing.out (R := A) inferInstance (I := ⊥) Ideal.isRadical_bot
  by_contra! H
  have : c ∈ (⊥ : Ideal A).jacobson := Ideal.mem_sInf.mpr fun J hJ => H J hJ.2
  rw [h, Ideal.mem_bot] at this
  exact hc this

/-- If the resultant of `P` and `P'` avoids the maximal ideal `m`, then `P mod m` is
separable. -/
private theorem separable_map_of_resultant_notMem {A : Type*} [CommRing A] (P : A[X])
    (m : Ideal A) [m.IsMaximal] (hd0 : 0 < P.natDegree)
    (hcm : P.resultant (derivative P) P.natDegree (P.natDegree - 1) ∉ m) :
    (P.map (Ideal.Quotient.mk m)).Separable := by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  set c := P.resultant (derivative P) P.natDegree (P.natDegree - 1) with hc
  obtain ⟨p, q, -, -, e⟩ := exists_mul_add_mul_eq_C_resultant P (derivative P)
    (m := P.natDegree) (n := P.natDegree - 1) le_rfl (natDegree_derivative_le P) (Or.inl hd0.ne')
  have hu : IsUnit (Ideal.Quotient.mk m c) := by
    rwa [isUnit_iff_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]
  have e' := congrArg (Polynomial.map (Ideal.Quotient.mk m)) e
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ← hc] at e'
  have hinv : C (hu.unit⁻¹ : (A ⧸ m)ˣ).1 * C (Ideal.Quotient.mk m c) = 1 := by
    rw [← C_mul, hu.val_inv_mul, C_1]
  refine ⟨C (hu.unit⁻¹ : (A ⧸ m)ˣ).1 * p.map (Ideal.Quotient.mk m),
    C (hu.unit⁻¹ : (A ⧸ m)ˣ).1 * q.map (Ideal.Quotient.mk m), ?_⟩
  rw [derivative_map, ← hinv, ← e']
  ring

/-- For monic `P` separable over the field `K`, the resultant of `P` and `P'` is nonzero in
`K`. -/
private theorem algebraMap_resultant_derivative_ne_zero {A K : Type*} [CommRing A] [Field K]
    [CharZero K] [Algebra A K] {P : A[X]} (hmon : P.Monic)
    (hsep : (P.map (algebraMap A K)).Separable) :
    algebraMap A K (P.resultant (derivative P) P.natDegree (P.natDegree - 1)) ≠ 0 := by
  have h1 : (P.map (algebraMap A K)).resultant (derivative (P.map (algebraMap A K))) =
      algebraMap A K (P.resultant (derivative P) P.natDegree (P.natDegree - 1)) := by
    rw [derivative_map, ← resultant_map_map]
    congr 1
    · exact hmon.natDegree_map _
    · rw [← derivative_map, natDegree_derivative, hmon.natDegree_map]
  rw [← h1]
  exact resultant_ne_zero _ _ hsep

/-- An injective integral extension `A → B` of a normal finitely generated algebra over an
algebraically closed field of characteristic zero that is injective on spectra is surjective. -/
public theorem algebraMap_surjective_of_comap_injective
    (k : Type u) {A : Type u} {B : Type*} [Field k] [IsAlgClosed k] [CharZero k] [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B]
    (hinj : Function.Injective (algebraMap A B))
    (hspec : Function.Injective (PrimeSpectrum.comap (algebraMap A B))) :
    Function.Surjective (algebraMap A B) := by
  classical
  intro b
  by_contra hb
  have : Module.IsTorsionFree A B := (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj
  have hint : IsIntegral A b := Algebra.IsIntegral.isIntegral b
  set P := minpoly A b
  have hmon : P.Monic := minpoly.monic hint
  set d := P.natDegree
  have hd0 : 0 < d := minpoly.natDegree_pos hint
  have hd1 : d ≠ 1 := fun h => hb (minpoly.natDegree_eq_one_iff.mp h)
  have : CharZero A := charZero_of_injective_algebraMap (algebraMap k A).injective
  let K := FractionRing A
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  have hsep : (P.map (algebraMap A K)).Separable :=
    ((hmon.irreducible_iff_irreducible_map_fraction_map).mp (minpoly.irreducible hint)).separable
  set c := P.resultant (derivative P) d (d - 1)
  have hcK : algebraMap A K c ≠ 0 := algebraMap_resultant_derivative_ne_zero hmon hsep
  have hc0 : c ≠ 0 := fun h => hcK (by rw [h, map_zero])
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  obtain ⟨m, hm, hcm⟩ := exists_isMaximal_notMem_of_ne_zero hc0
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) (Ideal.Quotient.mkₐ_surjective k m)
  have : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have hsurj : Function.Surjective (algebraMap k (A ⧸ m)) := IsSepClosed.algebraMap_surjective k _
  have : IsAlgClosed (A ⧸ m) := IsAlgClosed.of_ringEquiv k (A ⧸ m)
    (RingEquiv.ofBijective (algebraMap k (A ⧸ m)) ⟨(algebraMap k _).injective, hsurj⟩)
  set Pm := P.map (Ideal.Quotient.mk m) with hPm_def
  have hPm : Pm.Separable := separable_map_of_resultant_notMem P m hd0 hcm
  have hPm0 : Pm ≠ 0 := (hmon.map _).ne_zero
  have hcard : Pm.roots.toFinset.card = d := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hPm), IsAlgClosed.card_roots_eq_natDegree,
      hPm_def, hmon.natDegree_map]
  obtain ⟨a₁, h₁, a₂, h₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < Pm.roots.toFinset.card)
  rw [Multiset.mem_toFinset, mem_roots hPm0] at h₁ h₂
  obtain ⟨Q₁, hQ₁, hQ₁m, hQ₁x⟩ := exists_prime_over_of_isRoot b m a₁ h₁
  obtain ⟨Q₂, hQ₂, hQ₂m, hQ₂x⟩ := exists_prime_over_of_isRoot b m a₂ h₂
  have hQ : Q₁ = Q₂ := congrArg PrimeSpectrum.asIdeal
    (@hspec ⟨Q₁, hQ₁⟩ ⟨Q₂, hQ₂⟩ (PrimeSpectrum.ext (hQ₁m.trans hQ₂m.symm)))
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective a₁
  exact hne (hx.symm.trans ((hQ₂x x).mp (hQ ▸ (hQ₁x x).mpr hx)))

/-- A finite surjective injective morphism from an integral scheme onto a normal integral scheme
locally of finite type over an algebraically closed field of characteristic zero is bijective on
the sections over every nonempty affine open. -/
public theorem bijective_app_of_isFinite_of_injective
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {W Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType sZ] (κ : W ⟶ Z)
    [IsIntegral W] [IsIntegral Z] [IsNormal Z] [IsFinite κ] [Surjective κ]
    (hinj : Function.Injective κ) (U : Z.Opens) (hU : IsAffineOpen U) [hne : Nonempty U] :
    Function.Bijective (κ.app U) := by
  have : Nonempty (κ ⁻¹ᵁ U) := by
    obtain ⟨⟨z, hz⟩⟩ := hne
    obtain ⟨w, rfl⟩ := κ.surjective z
    exact ⟨⟨w, hz⟩⟩
  have hV : IsAffineOpen (κ ⁻¹ᵁ U) := hU.preimage κ
  let := MMP.Mori.sectionAlgebra sZ U
  have := MMP.Mori.finiteType_sectionAlgebra sZ hU
  let : Algebra Γ(Z, U) Γ(W, κ ⁻¹ᵁ U) := (κ.app U).hom.toAlgebra
  have : IsIntegrallyClosed Γ(Z, U) :=
    (isNormal_iff_forall_affineOpen_normal Z).mp inferInstance ⟨U, hU⟩ hne
  have : Algebra.IsIntegral Γ(Z, U) Γ(W, κ ⁻¹ᵁ U) := ⟨κ.isIntegral_app U hU⟩
  have : IsSchemeTheoreticallyDominant κ := .of_isDominant κ
  have hinjA : Function.Injective (κ.app U) := κ.app_injective U
  have hspec : Function.Injective
      (PrimeSpectrum.comap (algebraMap Γ(Z, U) Γ(W, κ ⁻¹ᵁ U))) := by
    intro p q hpq
    have hsq := IsAffineOpen.SpecMap_appLE_fromSpec κ hU hV le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at hsq
    have e : ∀ x, hU.fromSpec ((Spec.map (κ.app U)) x) = κ (hV.fromSpec x) := fun x => by
      rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
    have h1 : κ (hV.fromSpec p) = κ (hV.fromSpec q) :=
      (e p).symm.trans ((congrArg hU.fromSpec hpq).trans (e q))
    exact hV.fromSpec.isOpenEmbedding.injective (hinj h1)
  exact ⟨hinjA, algebraMap_surjective_of_comap_injective k hinjA hspec⟩

/-- A finite surjective injective morphism from an integral scheme onto a normal variety over an
algebraically closed field of characteristic zero is an isomorphism. -/
public theorem isIso_of_isFinite_of_injective
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {W Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (κ : W ⟶ Z)
    (hZ : IsNormalVariety k sZ) [IsIntegral W]
    [IsFinite κ] [Surjective κ] (hinj : Function.Injective κ) : IsIso κ := by
  have := hZ.1.toIsIntegral
  have := hZ.2
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  let ι := {V : Z.affineOpens // ((V : Z.Opens) : Set Z).Nonempty}
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun V : ι => V.1.1) ?_).mpr fun V => ?_
  · refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, ⟨z, hzV⟩⟩, hzV⟩
  · have : Nonempty V.1.1 := ⟨⟨V.2.choose, V.2.choose_spec⟩⟩
    change IsIso _
    rw [isIso_morphismRestrict_iff_isIso_app κ V.1.2, ConcreteCategory.isIso_iff_bijective]
    exact bijective_app_of_isFinite_of_injective sZ κ hinj V.1.1 V.1.2

/-! ### `h_* 𝒪_X = 𝒪_Z` -/

/-- `h_* 𝒪_X = 𝒪_Z` for a proper surjective morphism with connected fibres between normal
varieties over an algebraically closed field of characteristic zero. -/
private theorem bijective_app_of_isConnected_fibres
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (h : X ⟶ Z)
    (hZ : IsNormalVariety k sZ) (hX : IsNormalVariety k (h ≫ sZ))
    [IsProper h] [Surjective h] (hfib : ∀ z : Z, _root_.IsConnected (h ⁻¹' {z}))
    (U : Z.Opens) : Function.Bijective (h.app U) := by
  obtain ⟨W, h', κ, ⟨hS⟩, hP, hs, hiso, -, hfin, hW⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isNormalVariety (h ≫ sZ) sZ hX hZ.1 h
      rfl
  have hcomp : h' ≫ κ = h := hS.comp
  subst hcomp
  have : Surjective κ := Surjective.of_comp h' κ
  have hinj : Function.Injective κ := fun a b hab => by
    have hc : _root_.IsPreconnected (κ ⁻¹' {κ a}) := by
      simpa only [Set.image_preimage_eq _ hs.surj, Scheme.Hom.comp_base,
        TopCat.coe_comp, Set.preimage_comp] using
        (hfib (κ a)).isPreconnected.image _ h'.continuous.continuousOn
    exact hc.isDiscrete_iff_subsingleton.mp (κ.isDiscrete_preimage_singleton _) rfl hab.symm
  have := hW.1.toIsIntegral
  have := isIso_of_isFinite_of_injective sZ κ hZ hinj
  rw [Scheme.Hom.comp_app]
  exact ((ConcreteCategory.isIso_iff_bijective _).mp (hiso _)).comp
    ((ConcreteCategory.isIso_iff_bijective (κ.app U)).mp inferInstance)

/-! ### Sections of `𝒪_Y(G)` -/

/-- An integral scheme has the single irreducible component `univ`. -/
private theorem component_eq_univ {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ := by
  obtain ⟨Z, h⟩ := Z
  exact (irreducibleComponents_eq_singleton (X := Y) ▸ h : Z ∈ ({Set.univ} : Set (Set Y)))

/-- In an irreducible scheme the generic point lies in every nonempty open. -/
private theorem genericPoint_mem {X : Scheme.{u}} [IrreducibleSpace X] {U : X.Opens}
    (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

/-- A specialization between equal points induces an isomorphism of stalks. -/
private theorem isIso_stalkSpecializes_of_eq {X : Scheme.{u}} {x y : X} (hsp : x ⤳ y)
    (h : x = y) : IsIso (X.presheaf.stalkSpecializes hsp) := by
  subst h
  simp only [TopCat.Presheaf.stalkSpecializes_refl]
  infer_instance

/-- On an integral scheme the generic point of every irreducible component is the generic
point. -/
private theorem componentGenericPoint_eq {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z = genericPoint Y := by
  refine (isGenericPoint_componentGenericPoint Y Z).eq ?_
  rw [component_eq_univ Z]
  exact genericPoint_spec Y

/-- The valuation `v_P` is carried to `v_F` by a map of the factors of `𝒦` compatible with an
isomorphism `𝒪_{X,P} ≅ 𝒪_{Y,F}`. -/
private theorem valuation_apply_eq_of_ringEquiv {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    (P : MMP.Mori.PrimeDivisor X) (F : MMP.Mori.PrimeDivisor Y)
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

/-- On an integral scheme, the stalk at the generic point of an irreducible component is the
function field. -/
private noncomputable def stalkComponentGenericPointEquiv (Y : Scheme.{u}) [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Y.presheaf.stalk (componentGenericPoint Y Z) ≃+* Y.functionField :=
  (Y.presheaf.stalkCongr
    (Inseparable.of_eq (componentGenericPoint_eq Z).symm)).commRingCatIsoToRingEquiv.symm

private theorem stalkComponentGenericPointEquiv_apply (Y : Scheme.{u}) [IsIntegral Y]
    (Z : irreducibleComponents Y) (a : Y.presheaf.stalk (componentGenericPoint Y Z)) :
    stalkComponentGenericPointEquiv Y Z a = algebraMap _ Y.functionField a :=
  rfl

/-- Under the hypotheses of `exists_app_eq_of_mem_divisorialSubmodule`, the rational function on
`X` corresponding to a section `ψ` of `𝒪_Y(D)` under `k(X) ≅ k(Y)` is a section of `𝒪_X`. -/
private theorem isDivisorialSection_zero_of_mem_divisorialSubmodule {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (f : Y ⟶ X) [IsDominant f] (hf : Function.Bijective (functionFieldMap f))
    (D : Divisor Y) (U : X.Opens)
    (hD : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ U).Nonempty →
      ∃ F : MMP.Mori.PrimeDivisor Y,
        f F.genericPoint = P.genericPoint ∧ IsIso (f.stalkMap F.genericPoint) ∧ D.coeff F = 0)
    (ψ : D.divisorialSubmodule (f ⁻¹ᵁ U)) (ZY : irreducibleComponents Y)
    (hZYU : componentGenericPoint Y ZY ∈ f ⁻¹ᵁ U)
    (φX : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op U)))
    (hφX : ∀ Z, φX Z = (stalkComponentGenericPointEquiv X Z.1).symm
      ((RingEquiv.ofBijective (functionFieldMap f) hf).symm
        (stalkComponentGenericPointEquiv Y ZY (ψ.1 ⟨ZY, hZYU⟩)))) :
    (0 : Divisor X).IsDivisorialSection U φX := by
  have hsub : ∀ Z Z' : irreducibleComponents Y, Z = Z' := fun Z Z' =>
    Subtype.ext (by rw [component_eq_univ Z, component_eq_univ Z'])
  set Φ := RingEquiv.ofBijective (functionFieldMap f) hf
  intro P hP
  obtain ⟨F, hFP, hiso, hF0⟩ := hD P hP
  have hFU : (F.support ∩ (f ⁻¹ᵁ U : Set Y)).Nonempty := by
    refine ⟨F.genericPoint, ?_, ?_⟩
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    · change f _ ∈ U
      rw [hFP]
      exact P.genericPoint_mem_of_nonempty hP
  have hψF := ψ.2 F hFU
  rw [hF0, neg_zero] at hψF
  obtain rfl := hsub ZY F.component
  have hsp : f F.genericPoint ⤳ P.genericPoint := hFP ▸ specializes_rfl
  have := isIso_stalkSpecializes_of_eq hsp hFP
  let φ : P.localRing ≃+* F.localRing :=
    (asIso (X.presheaf.stalkSpecializes hsp ≫
      f.stalkMap F.genericPoint)).commRingCatIsoToRingEquiv
  let T : X.presheaf.stalk (componentGenericPoint X P.component) →+*
      Y.presheaf.stalk (componentGenericPoint Y F.component) :=
    (stalkComponentGenericPointEquiv Y F.component).symm.toRingHom.comp
      (Φ.toRingHom.comp (stalkComponentGenericPointEquiv X P.component).toRingHom)
  have hTinj : Function.Injective T :=
    (stalkComponentGenericPointEquiv Y F.component).symm.injective.comp
      (Φ.injective.comp (stalkComponentGenericPointEquiv X P.component).injective)
  have hT : ∀ b, T (P.toComponent.hom b) = F.toComponent.hom (φ b) := by
    intro b
    apply (stalkComponentGenericPointEquiv Y F.component).injective
    simp only [T, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply]
    rw [stalkComponentGenericPointEquiv_apply X, stalkComponentGenericPointEquiv_apply Y]
    change Φ (algebraMap _ X.functionField ((X.presheaf.stalkSpecializes _).hom b)) =
      algebraMap _ Y.functionField ((Y.presheaf.stalkSpecializes _).hom
        ((f.stalkMap F.genericPoint).hom ((X.presheaf.stalkSpecializes hsp).hom b)))
    rw [algebraMap_stalkSpecializes, algebraMap_stalkSpecializes,
      ← functionFieldMap_algebraMap_stalk, algebraMap_stalkSpecializes]
    rfl
  have hTa : T (φX ⟨P.component, P.componentGenericPoint_mem_of_nonempty hP⟩) =
      ψ.1 ⟨F.component, F.componentGenericPoint_mem_of_nonempty hFU⟩ := by
    simp [T, hφX]
  rcases hψF with h0 | hv
  · exact Or.inl (hTinj (by rwa [hTa, map_zero]))
  · exact Or.inr (by rwa [← valuation_apply_eq_of_ringEquiv P F φ T hT, hTa])

/-- Let `f : Y ⟶ X` be a dominant morphism of normal integral schemes with `f^* : k(X) ≅ k(Y)`,
`U ⊆ X` open and `D` a divisor on `Y` such that every prime divisor `P` of `X` meeting `U` is
dominated by a prime divisor `F` of `Y` with `coeff_F D = 0`. Then every section of `𝒪_Y(D)` over
`f⁻¹ U` is `f^♯ r` for a regular function `r` on `U`. -/
private theorem exists_app_eq_of_mem_divisorialSubmodule {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ X) [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) (D : Divisor Y)
    (U : X.Opens)
    (hD : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ U).Nonempty →
      ∃ F : MMP.Mori.PrimeDivisor Y,
        f F.genericPoint = P.genericPoint ∧ IsIso (f.stalkMap F.genericPoint) ∧ D.coeff F = 0)
    (ψ : D.divisorialSubmodule (f ⁻¹ᵁ U)) :
    ∃ r : Γ(X, U), (toRationalFunctionsPresheaf Y).app (Opposite.op (f ⁻¹ᵁ U)) (f.app U r) =
      ψ.1 := by
  by_cases hU : (U : Set X).Nonempty
  swap
  · exact ⟨0, funext fun Z => (hU ⟨_, Z.2⟩).elim⟩
  have hfη : f (genericPoint Y) = genericPoint X := map_genericPoint_of_isDominant f
  have hηX : genericPoint X ∈ U := genericPoint_mem hU
  have hηY : genericPoint Y ∈ f ⁻¹ᵁ U := show f _ ∈ U from hfη ▸ hηX
  obtain ⟨ZY, -⟩ := exists_mem_irreducibleComponents (genericPoint Y)
  obtain ⟨ZX, -⟩ := exists_mem_irreducibleComponents (genericPoint X)
  have hZYU : componentGenericPoint Y ZY ∈ f ⁻¹ᵁ U := by
    rwa [componentGenericPoint_eq]
  have hZXU : componentGenericPoint X ZX ∈ U := by
    rwa [componentGenericPoint_eq]
  let Φ := RingEquiv.ofBijective (functionFieldMap f) hf
  let φX : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op U)) := fun Z =>
    (stalkComponentGenericPointEquiv X Z.1).symm
      (Φ.symm (stalkComponentGenericPointEquiv Y ZY (ψ.1 ⟨ZY, hZYU⟩)))
  obtain ⟨s, hs⟩ := (isDivisorialSection_zero_of_mem_divisorialSubmodule f hf D U hD ψ ZY hZYU φX
    fun _ => rfl).exists_eq
  refine ⟨s, funext fun Z' => ?_⟩
  obtain rfl : Z' = ⟨ZY, hZYU⟩ :=
    Subtype.ext (Subtype.ext (by rw [component_eq_univ Z'.1, component_eq_univ ZY]))
  rw [toRationalFunctionsPresheaf_app_apply]
  apply (stalkComponentGenericPointEquiv Y ZY).injective
  have h1 := congrFun hs ⟨ZX, hZXU⟩
  rw [toRationalFunctionsPresheaf_app_apply] at h1
  have hsp : componentGenericPoint X ZX ⤳ f (componentGenericPoint Y ZY) :=
    (isGenericPoint_componentGenericPoint X ZX).specializes (by rw [component_eq_univ ZX]; trivial)
  have hR : stalkComponentGenericPointEquiv Y ZY (ψ.1 ⟨ZY, hZYU⟩) =
      Φ (stalkComponentGenericPointEquiv X ZX (X.presheaf.germ U _ hZXU s)) := by
    rw [h1]
    simp [φX]
  have h2 : Y.presheaf.germ (f ⁻¹ᵁ U) (componentGenericPoint Y ZY) hZYU (f.app U s) =
      f.stalkMap _ (X.presheaf.germ U _ hZYU s) :=
    (Scheme.Hom.germ_stalkMap_apply f U _ hZYU s).symm
  rw [hR, stalkComponentGenericPointEquiv_apply Y, stalkComponentGenericPointEquiv_apply X]
  erw [h2]
  rw [← functionFieldMap_algebraMap_stalk,
    ← TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hZYU hsp, algebraMap_stalkSpecializes]
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
    rw [hF]
    infer_instance
  exact ⟨_, hF, MMP.Positivity.isIso_stalkMap_of_valuationRing g hbij _⟩

/-- For `d + c = n`, the bound `d + 2 ≤ n` is equivalent to `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add] at h
    have h := WithBot.coe_injective h
    obtain ⟨hd, hc⟩ : d ≠ ⊤ ∧ c ≠ ⊤ := by
      rw [← not_or, ← ENat.add_eq_top, h]
      exact ENat.natCast_ne_top n
    lift d to ℕ using hd
    lift c to ℕ using hc
    rw [show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_ofNat,
      ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_cast at h ⊢
    omega

/-- A variety over a field has finite dimension. -/
private theorem exists_topologicalKrullDim_eq_natCast {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] [CompactSpace X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  induction hd : topologicalKrullDim X using WithBot.recBotCoe with
  | bot =>
    exact ((Order.krullDim_eq_bot_iff.mp hd).false
      (⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        TopologicalSpace.IrreducibleCloseds X)).elim
  | coe d =>
    lift d to ℕ using fun h => h1 (by rw [hd, h]; rfl)
    exact ⟨d, rfl⟩

/-- A prime divisor `F` of `Y` whose image `g(η_F)` has codimension one in the normal variety `X`
is not exceptional over `X`. -/
private theorem not_isExceptionalPrimeDivisor_of_coheight_eq_one {k : Type u} [Field k]
    {X Y Z : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) (h : X ⟶ Z) (g : Y ⟶ X) (hX : IsNormalVariety k (h ≫ sZ))
    (F : MMP.Mori.PrimeDivisor Y) (hF : Order.coheight (g F.genericPoint) = 1) :
    ¬ IsExceptionalPrimeDivisor (h ≫ sZ) g F := by
  rintro ⟨_, _, _, hexc⟩
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType (h ≫ sZ) := hX.1.toLocallyOfFiniteType
  have : QuasiCompact (h ≫ sZ) := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (h ≫ sZ)
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast (h ≫ sZ)
  unfold ProperDivisorOver.IsExceptional at hexc
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint, hn] at hexc
  have hd := topologicalKrullDim_closure_singleton_add_coheight (h ≫ sZ) (g F.genericPoint)
  rw [hn] at hd
  have h2 := (withBot_add_two_le_iff hd).mp hexc
  change 2 ≤ Order.coheight (g F.genericPoint) at h2
  rw [hF] at h2
  exact absurd h2 (by decide)

/-- The union of the closures of finitely many points of coheight at least two is a closed set
all of whose points have coheight at least two. -/
private theorem exists_isClosed_forall_two_le_coheight {Z : Scheme.{u}} {ι : Type*}
    (S : Finset ι) (z : ι → Z) (hz : ∀ i ∈ S, 2 ≤ Order.coheight (z i)) :
    ∃ W : Set Z, IsClosed W ∧ (∀ w ∈ W, 2 ≤ Order.coheight w) ∧ ∀ i ∈ S, z i ∈ W := by
  refine ⟨⋃ i ∈ S, closure {z i}, isClosed_biUnion_finset fun _ _ => isClosed_closure,
    fun w hw => ?_, fun i hi => Set.mem_biUnion hi (subset_closure rfl)⟩
  obtain ⟨i, hi, hw⟩ := Set.mem_iUnion₂.mp hw
  exact (hz i hi).trans (Order.coheight_anti (specializes_iff_mem_closure.mpr hw))

/-- Algebraic Hartogs: on a normal locally Noetherian integral scheme, a section over `U' ⊆ U`
extends to `U` when `U'` contains the generic point of every prime divisor meeting `U`. -/
private theorem exists_map_homOfLE_eq_of_forall_genericPoint_mem {Z : Scheme.{u}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] {U U' : Z.Opens} (hle : U' ≤ U) [Nonempty U']
    (hU' : ∀ Γ : MMP.Mori.PrimeDivisor Z, (Γ.support ∩ U).Nonempty → Γ.genericPoint ∈ U')
    (s : Γ(Z, U')) : ∃ r : Γ(Z, U), Z.presheaf.map (homOfLE hle).op r = s := by
  have : Nonempty U := ⟨⟨_, hle (Classical.arbitrary U').2⟩⟩
  obtain ⟨r, hr⟩ := MMP.Threefold.Bridges.exists_germToFunctionField_eq_of_forall_zero_le_ord U
    (Z.germToFunctionField U' s) fun Γ hΓ => by
      have hΓU' := hU' Γ hΓ
      by_cases h0 : Z.germToFunctionField U' s = 0
      · rw [h0, Scheme.ord_zero]
        rfl
      have hv : Γ.divisorialValuation (Z.germToFunctionField U' s) ≤ 1 :=
        (Γ.divisorialValuation_le_one_iff _).mpr
          ⟨Z.presheaf.germ U' _ hΓU' s,
            Scheme.algebraMap_germ_eq_germToFunctionField (X := Z) hΓU' s⟩
      rw [Γ.divisorialValuation_eq_exp_neg_ord h0, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at hv
      linarith
  refine ⟨r, Z.germToFunctionField_injective U' ?_⟩
  rw [← hr]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- A prime divisor `P` of `X` meeting `h⁻¹(U')`, for `U'` disjoint from a closed set `W` that
contains the images of the components of `G` of codimension at least two, is dominated by a prime
divisor `F` of `Y` at which `g` is a local isomorphism and `G` vanishes. -/
private theorem exists_primeDivisor_coeff_eq_zero {k : Type u} [Field k] {X Y Z : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) (h : X ⟶ Z) (g : Y ⟶ X) [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] (hX : IsNormalVariety k (h ≫ sZ)) [IsProper g]
    (hg : IsBirationalMorphism g) (G : Divisor Y)
    (hcomp : ∀ E : Mori.PrimeDivisor Y, G E ≠ 0 →
      IsExceptionalPrimeDivisor (h ≫ sZ) g E ∨ 2 ≤ Order.coheight (h (g E.genericPoint)))
    {W : Set Z} (hWc : IsClosed W)
    (hGW : ∀ E : Mori.PrimeDivisor Y, G E ≠ 0 → 2 ≤ Order.coheight (h (g E.genericPoint)) →
      h (g E.genericPoint) ∈ W)
    {U' : Z.Opens} (hU' : (U' : Set Z) ⊆ Wᶜ) (P : MMP.Mori.PrimeDivisor X)
    (hP : (P.support ∩ h ⁻¹ᵁ U').Nonempty) :
    ∃ F : MMP.Mori.PrimeDivisor Y, g F.genericPoint = P.genericPoint ∧
      IsIso (g.stalkMap F.genericPoint) ∧ G.coeff F = 0 := by
  obtain ⟨F, hFP, hiso⟩ := exists_primeDivisor_map_genericPoint_eq g hg P
  refine ⟨F, hFP, hiso, ?_⟩
  by_contra hF0
  rcases hcomp F hF0 with hexc | h2
  · exact not_isExceptionalPrimeDivisor_of_coheight_eq_one sZ h g hX F
      (by rw [hFP]; exact P.coheight_genericPoint) hexc
  · obtain ⟨x, hxP, hxV⟩ := hP
    have hmem := hGW F hF0 h2
    rw [hFP] at hmem
    have hsp : P.genericPoint ⤳ x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxP
      exact specializes_iff_mem_closure.mpr hxP
    exact hU' hxV ((hsp.map h.continuous).mem_closed hWc hmem)

/-- Every section of `𝒪_Y(G)` over `f⁻¹ U` comes from `𝒪_Z(U)` (the second paragraph of the
proof of FA 17.4): it is regular on `h⁻¹(U ∖ W)` with `W = ⋃ h(g(Gᵢ))` over the components with
image of codimension at least two, hence a section of `h_* 𝒪_X = 𝒪_Z` over `U ∖ W`, and it extends
over `U` by algebraic Hartogs on `Z`. -/
private theorem surjective_structureSheafToDivisorialSheaf_app_comp
    {k : Type u} [Field k]
    {X Y Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (h : X ⟶ Z) (g : Y ⟶ X)
    [IsLocallyNoetherian Y] [IsNormal Y]
    (hZ : IsNormalVariety k sZ) (hX : IsNormalVariety k (h ≫ sZ))
    (hY : IsNormalVariety k (g ≫ h ≫ sZ))
    [Surjective h] (hh : ∀ V : Z.Opens, Function.Bijective (h.app V))
    [IsProper g] (hg : IsBirationalMorphism g)
    (G : Divisor Y) (hG : 0 ≤ G)
    (hcomp : ∀ E : Mori.PrimeDivisor Y, G E ≠ 0 →
      IsExceptionalPrimeDivisor (h ≫ sZ) g E ∨ 2 ≤ Order.coheight (h (g E.genericPoint)))
    (U : Z.Opens) :
    Function.Surjective fun r : Γ(Z, U) =>
      (Divisor.structureSheafToDivisorialSheaf hG).app ((g ≫ h) ⁻¹ᵁ U) ((g ≫ h).app U r) := by
  classical
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsNormal Z := hZ.2
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : LocallyOfFiniteType (h ≫ sZ) := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (h ≫ sZ)
  have : IsDominant g := hg.isDominant
  intro φ
  by_cases hU : (U : Set Z).Nonempty
  swap
  · exact ⟨0, Subtype.ext (funext fun Z0 => (hU ⟨_, Z0.2⟩).elim)⟩
  obtain ⟨W, hWc, hW2, hGW⟩ := exists_isClosed_forall_two_le_coheight
    (G.support.filter fun E => 2 ≤ Order.coheight (h (g E.genericPoint)))
    (fun E => h (g E.genericPoint)) fun E hE => (Finset.mem_filter.mp hE).2
  have hcodim : ∀ w ∈ W, Order.coheight w ≤ 1 → False := fun w hw h1 =>
    absurd ((hW2 w hw).trans h1) (by decide)
  let U' : Z.Opens := U ⊓ ⟨Wᶜ, hWc.isOpen_compl⟩
  have hηU' : genericPoint Z ∈ U' := ⟨genericPoint_mem hU, fun hw => hcodim _ hw
    (by rw [Order.coheight_eq_zero.mpr (fun z _ => genericPoint_specializes z)]; exact zero_le_one)⟩
  have : Nonempty U' := ⟨⟨_, hηU'⟩⟩
  let V : X.Opens := h ⁻¹ᵁ U'
  have hiV : g ⁻¹ᵁ V ≤ (g ≫ h) ⁻¹ᵁ U := fun _ hy => hy.1
  let ψ : G.divisorialSubmodule (g ⁻¹ᵁ V) := G.divisorialRestrict (homOfLE hiV) φ
  obtain ⟨r', hr'⟩ := exists_app_eq_of_mem_divisorialSubmodule g hg.functionFieldMap_bijective G
    V (exists_primeDivisor_coeff_eq_zero sZ h g hX hg G hcomp hWc
      (fun E hE h2 => hGW E (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hE, h2⟩))
      fun _ hz => hz.2) ψ
  obtain ⟨s, hs⟩ := (hh U').2 r'
  obtain ⟨r, hrs⟩ := exists_map_homOfLE_eq_of_forall_genericPoint_mem
    (inf_le_left : U' ≤ U) (fun Γ hΓ => ⟨Γ.genericPoint_mem_of_nonempty hΓ, fun hw =>
      hcodim _ hw Γ.coheight_genericPoint.le⟩) s
  refine ⟨r, Subtype.ext ?_⟩
  rw [Divisor.coe_structureSheafToDivisorialSheaf_app]
  funext Z0
  have hZ0 : componentGenericPoint Y Z0.1 ∈ g ⁻¹ᵁ V := by
    rw [componentGenericPoint_eq]
    change h (g (genericPoint Y)) ∈ U'
    rw [map_genericPoint_of_isDominant g, map_genericPoint_of_isDominant h]
    exact hηU'
  have e1 := congrFun hr' ⟨Z0.1, hZ0⟩
  rw [toRationalFunctionsPresheaf_app_apply] at e1 ⊢
  change _ = φ.1 ⟨Z0.1, _⟩ at e1
  have hnat : Y.presheaf.map (homOfLE hiV).op ((g ≫ h).app U r) = g.app V (h.app U' s) := by
    have := congrArg (fun φ => φ.hom r) ((g ≫ h).naturality (homOfLE (inf_le_left : U' ≤ U)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [← hrs]
    exact this.symm
  rw [← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hiV) _ hZ0, hnat, hs]
  exact e1

/-- Let `h : X ⟶ Z` be a proper surjective morphism of normal varieties over an algebraically
closed field of characteristic zero, with connected fibres, `g : Y ⟶ X` a proper birational
morphism from a normal variety, and `G ≥ 0` a divisor on `Y` each of whose components is
exceptional over `X` or has image in `Z` of codimension at least two. Then `(g ≫ h)_* 𝒪_Y(G) =
𝒪_Z`: on every open `U` of `Z` the map `𝒪_Z(U) → 𝒪_Y(G)((g ≫ h)⁻¹ U)` is bijective. -/
@[mmp "lem_fa17_pushforward_exceptional_effective_trivial"]
public theorem bijective_structureSheafToDivisorialSheaf_app_comp
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X Y Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (h : X ⟶ Z) (g : Y ⟶ X)
    [IsLocallyNoetherian Y] [IsNormal Y]
    (hZ : IsNormalVariety k sZ) (hX : IsNormalVariety k (h ≫ sZ))
    (hY : IsNormalVariety k (g ≫ h ≫ sZ))
    [IsProper h] [Surjective h] (hfib : ∀ z : Z, _root_.IsConnected (h ⁻¹' {z}))
    [IsProper g] (hg : IsBirationalMorphism g)
    (G : Divisor Y) (hG : 0 ≤ G)
    (hcomp : ∀ E : Mori.PrimeDivisor Y, G E ≠ 0 →
      IsExceptionalPrimeDivisor (h ≫ sZ) g E ∨ 2 ≤ Order.coheight (h (g E.genericPoint)))
    (U : Z.Opens) :
    Function.Bijective fun r : Γ(Z, U) =>
      (Divisor.structureSheafToDivisorialSheaf hG).app ((g ≫ h) ⁻¹ᵁ U) ((g ≫ h).app U r) := by
  have hh := bijective_app_of_isConnected_fibres sZ h hZ hX hfib
  refine ⟨fun r s hrs => ?_,
    surjective_structureSheafToDivisorialSheaf_app_comp sZ h g hZ hX hY hh hg G hG hcomp U⟩
  have hgU : Function.Bijective (g.app (h ⁻¹ᵁ U)) :=
    (ConcreteCategory.isIso_iff_bijective _).mp
      ((MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
        (g ≫ h ≫ sZ) (h ≫ sZ) hY.1 hX g hg).1 (h ⁻¹ᵁ U))
  have h1 := congrArg Subtype.val hrs
  simp only [Divisor.coe_structureSheafToDivisorialSheaf_app] at h1
  exact (hh U).1 (hgU.1 (toRationalFunctionsPresheaf_app_injective _ h1))

end MMP.Flips
