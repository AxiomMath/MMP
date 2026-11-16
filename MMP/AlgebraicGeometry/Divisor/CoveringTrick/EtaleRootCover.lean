module

public import MMP.AlgebraicGeometry.Singularities.DivisorialCyclicCoverNormal
public import MMP.AlgebraicGeometry.Positivity.AsymptoticAdjointIdeal
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen

/-!
# An étale cover extracting an `N`-th root of a rational function

Let `Y` be a normal variety over a field `k` of characteristic zero, and let `ψ ∈ K(Y)^×` and a
Cartier divisor `A` satisfy `div(ψ) = N A`. The divisorial cyclic
cover of `(-A, N, ψ)`, `Spec_Y ⊕_{i<N} 𝒪_Y(iA)` with multiplication by `ψ` on crossing degree
`N`, is finite, surjective and, `-A` being Cartier, étale. On a neighbourhood `U` of the generic
point where `-A` has a local equation `g`, its algebra is `𝒪_Y(U)[t]/(t^N - g^N ψ)`; so `t / g` is
an `N`-th root of `ψ` in the function field of every component. When `Y` is smooth, so is the
cover, and its connected components are integral; any of them is a finite étale surjective cover
of `Y` whose function field contains an `N`-th root of `ψ`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.isFinite_and_etale_and_surjective_toBase`: the divisorial
  cyclic cover of a trivialized multiple of a Cartier divisor is finite, étale and surjective.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_isIntegral_open_isClosed`: a scheme smooth over
  a field has integral open and closed subschemes through every point.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_pow_eq_functionFieldMap_toBase`: on an integral
  open subscheme of the cover dominating `Y`, the pull-back of `ψ` is an `N`-th power.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_etale_cover_pow_eq_functionFieldMap`: a finite
  étale surjective cover by an integral scheme on which `ψ` has an `N`-th root.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology MMP.Mori

variable {k : Type} [Field k] [CharZero k] {Y : Scheme.{0}} (f : Y ⟶ Spec (.of k))

/-- **The divisorial cyclic cover of a trivialized multiple of a Cartier divisor is finite étale
surjective.** Let `Y` be a normal variety over a field of characteristic zero, `M` a Cartier
divisor, `m` nonzero and `φ ∈ K(Y)^×` with `div(φ) + mM = 0`. -/
theorem isFinite_and_etale_and_surjective_toBase [IsIntegral Y] [LocallyOfFiniteType f]
    [QuasiCompact f] [IsNormal Y] [IsLocallyNoetherian Y] [CompactSpace Y] (m : ℕ) [NeZero m]
    (M : Divisor Y) (hM : M.IsCartier) (φ : (RationalFunctions Y)ˣ)
    (h : principalDivisor φ + m • M = 0) :
    IsFinite (DivisorialCyclicCover.toBase m M h.ge) ∧
      Etale (DivisorialCyclicCover.toBase m M h.ge) ∧
      Surjective (DivisorialCyclicCover.toBase m M h.ge) := by
  let : Y.Over (Spec (.of k)) := ⟨f⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := ‹LocallyOfFiniteType f›
  have : QuasiCompact (Y ↘ Spec (.of k)) := ‹QuasiCompact f›
  obtain ⟨hfin, -, -, hsurj, het, -⟩ :=
    DivisorialCyclicCover.isNormal_cover_of_principalDivisor_add_smul_eq_zero k Y m M φ h
  refine ⟨hfin, ?_, hsurj⟩
  have hx : ∀ x : Y, ∃ U : Y.Opens, x ∈ U ∧ Etale (DivisorialCyclicCover.toBase m M h.ge ∣_ U) :=
    fun x => (het x).2 (by
      obtain ⟨V, hxV, ψ, hψ⟩ := hM x
      exact MMP.Flips.isCartierAt_of_isLocalEquation hxV hψ)
  choose U hxU hU using hx
  have : IsZariskiLocalAtTarget @AlgebraicGeometry.Etale.{0} := by
    set_option backward.isDefEq.respectTransparency false in exact inferInstance
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @AlgebraicGeometry.Etale.{0}) U
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩) hU

omit [CharZero k] in
/-- A scheme smooth over a field has, through each of its points, an open and closed subscheme
which is integral: the connected component of the point. -/
theorem exists_isIntegral_open_isClosed {Z : Scheme.{0}} (p : Z ⟶ Spec (.of k)) [Smooth p]
    (z : Z) : ∃ U : Z.Opens, IsClosed (U : Set Z) ∧ z ∈ U ∧ IsIntegral U :=
  let hopen := Stacks.Chow.isOpen_connectedComponent_of_smooth p z
  ⟨⟨connectedComponent z, hopen⟩, isClosed_connectedComponent, mem_connectedComponent,
    Stacks.Chow.isIntegral_connectedComponent_of_smooth p z hopen⟩

/-- An open and closed subscheme of a scheme `Z`, universally open and universally closed over a
connected scheme `Y`, maps onto `Y` when it is non-empty: its image is open and closed. -/
theorem surjective_ι_comp_of_isClosed {Z : Scheme.{0}} (g : Z ⟶ Y) [UniversallyClosed g]
    [UniversallyOpen g] [ConnectedSpace Y] (U : Z.Opens) (hU : IsClosed (U : Set Z))
    (hne : (U : Set Z).Nonempty) : Surjective (U.ι ≫ g) := by
  have huniv : g '' (U : Set Z) = Set.univ :=
    IsClopen.eq_univ ⟨g.isClosedMap _ hU, g.isOpenMap _ U.isOpen⟩ (hne.image _)
  refine ⟨fun y => ?_⟩
  obtain ⟨z, hz, rfl⟩ : y ∈ g '' (U : Set Z) := huniv ▸ Set.mem_univ y
  exact ⟨⟨z, hz⟩, rfl⟩

/-- **An `m`-th root on the divisorial cyclic cover.** Let `Y` be an integral normal scheme, `M`
a Cartier divisor and `φ ∈ K(Y)^×` with `div(φ) + mM = 0`. On every integral open subscheme
`U'` of the cyclic cover of `(M, m, φ)` dominating `Y`, the pull-back of `φ` is an `m`-th power
in the function field of `U'`. -/
theorem exists_pow_eq_functionFieldMap_toBase [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y]
    [CompactSpace Y] (m : ℕ) [NeZero m] (M : Divisor Y) (hM : M.IsCartier)
    (φ : (RationalFunctions Y)ˣ) (h : principalDivisor φ + m • M = 0)
    (U' : (DivisorialCyclicCover.cover m M h.ge).Opens) [IsIntegral U']
    [IsDominant (U'.ι ≫ DivisorialCyclicCover.toBase m M h.ge)] :
    ∃ z : (U' : Scheme.{0}).functionField, z ^ m =
      functionFieldMap (U'.ι ≫ DivisorialCyclicCover.toBase m M h.ge)
        (rationalFunctionsEquivFunctionField Y φ) := by
  set p := DivisorialCyclicCover.toBase m M h.ge
  set q := U'.ι ≫ p
  obtain ⟨U, hηU, g, hg⟩ := hM (genericPoint Y)
  obtain ⟨v, hv, -, e, -⟩ :=
    DivisorialCyclicCover.exists_algEquiv_adjoinRoot_of_isLocalEquation m M h.ge hg
  let := ((DivisorialCyclicCover.localSubalgebra m M h.ge).algebraMap U).toAlgebra
  set r := e (AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C v))
  have hr : r ^ m = algebraMap Γ(Y, U) _ v := by
    have h0 : (AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C v)) ^ m =
        algebraMap Γ(Y, U) _ v := by
      have := AdjoinRoot.mk_self (f := Polynomial.X ^ m - Polynomial.C v)
      rwa [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at this
    rw [← map_pow, h0, AlgEquiv.commutes]
  set w := ((Stacks.RelativeSpec.universalAlgebraMap
    (DivisorialCyclicCover.situation m M h.ge)).right.app (op U)).hom r
  have hw : w ^ m = (p.app U).hom v := by
    rw [show w ^ m = ((Stacks.RelativeSpec.universalAlgebraMap
      (DivisorialCyclicCover.situation m M h.ge)).right.app (op U)).hom (r ^ m) from
        (map_pow _ _ _).symm, hr, Stacks.RelativeSpec.toBase_app]
    rfl
  have hη' : genericPoint U' ∈ q ⁻¹ᵁ U := by
    change q (genericPoint U') ∈ U
    rw [map_genericPoint_of_isDominant q]
    exact hηU
  set z₀ : (U' : Scheme.{0}).functionField :=
    ((U' : Scheme.{0}).presheaf.germ (q ⁻¹ᵁ U) (genericPoint U') hη').hom
      ((U'.ι.app (p ⁻¹ᵁ U)).hom w)
  have hz₀ : z₀ ^ m = functionFieldMap q (Y.presheaf.germ U (genericPoint Y) hηU v) := by
    rw [MMP.Fourfold.functionFieldMap_germ q U hηU hη' v]
    change ((U' : Scheme.{0}).presheaf.germ (q ⁻¹ᵁ U) (genericPoint U') hη').hom
      ((U'.ι.app (p ⁻¹ᵁ U)).hom w) ^ m = _
    erw [← map_pow, ← map_pow, hw]
    rfl
  have hgerm : Y.presheaf.germ U (genericPoint Y) hηU v =
      rationalFunctionsEquivFunctionField Y ((g ^ m * φ : (RationalFunctions Y)ˣ) :
        RationalFunctions Y) := by
    rw [← RingEquiv.symm_apply_eq]
    funext Z
    have hZ : componentGenericPoint Y Z ∈ U := by
      rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
    rw [MMP.Fourfold.rationalFunctionsEquivFunctionField_symm_germ U v hηU Z hZ]
    exact congrFun hv ⟨Z, hZ⟩
  set G := functionFieldMap q (rationalFunctionsEquivFunctionField Y (g : RationalFunctions Y))
  have hG : G ≠ 0 :=
    (map_ne_zero _).2 (g.isUnit.map (rationalFunctionsEquivFunctionField Y)).ne_zero
  refine ⟨z₀ * G⁻¹, ?_⟩
  rw [mul_pow, hz₀, hgerm, inv_pow, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow,
    map_mul, map_pow]
  change G ^ m * _ * (G ^ m)⁻¹ = _
  rw [mul_comm (G ^ m), mul_assoc, ← inv_pow, ← mul_pow, mul_inv_cancel₀ hG, one_pow, mul_one]

/-- **A finite étale cover extracting an `N`-th root.** Let `Y` be a smooth variety over a field of
characteristic zero, `N` nonzero, `A` a Cartier divisor and `ψ ∈ K(Y)^×`
with `div(ψ) = N A`. There is a finite étale surjective morphism `g : Y' ⟶ Y` from an integral
scheme such that the pull-back of `ψ` is an `N`-th power in the function field of `Y'`. -/
theorem exists_etale_cover_pow_eq_functionFieldMap [IsIntegral Y] [Smooth f] [QuasiCompact f]
    [IsNormal Y] [IsLocallyNoetherian Y] [CompactSpace Y] (N : ℕ) [NeZero N]
    (A : Divisor Y) (hA : A.IsCartier) (ψ : (RationalFunctions Y)ˣ)
    (hψ : principalDivisor ψ = N • A) :
    ∃ (Y' : Scheme.{0}) (g : Y' ⟶ Y) (_ : IsFinite g) (_ : Etale g) (_ : Surjective g)
      (_ : IsIntegral Y'), ∃ z : Y'.functionField,
        z ^ N = functionFieldMap g (rationalFunctionsEquivFunctionField Y ψ) := by
  have h : principalDivisor ψ + N • (-A) = 0 := by rw [hψ, smul_neg, add_neg_cancel]
  obtain ⟨hfin, het, hsurj⟩ := isFinite_and_etale_and_surjective_toBase f N (-A) hA.neg ψ h
  set p := DivisorialCyclicCover.toBase N (-A) h.ge
  obtain ⟨y', -⟩ := hsurj.surj (genericPoint Y)
  obtain ⟨U', hU'c, hy', hU'int⟩ := exists_isIntegral_open_isClosed (p ≫ f) y'
  have hsurj' : Surjective (U'.ι ≫ p) := surjective_ι_comp_of_isClosed p U' hU'c ⟨y', hy'⟩
  have : IsDominant (U'.ι ≫ p) := ⟨hsurj'.surj.denseRange⟩
  have : IsClosedImmersion U'.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rwa [Scheme.Opens.range_ι])
  obtain ⟨z, hz⟩ := exists_pow_eq_functionFieldMap_toBase N (-A) hA.neg ψ h U'
  exact ⟨U', U'.ι ≫ p, inferInstance, inferInstance, hsurj', hU'int, z, hz⟩

end MMP.FourfoldProofs.FractionalLogComplexProof
