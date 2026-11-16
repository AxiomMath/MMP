module

public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.CohomologySurjective
public import MMP.AlgebraicGeometry.Intersection.Surface.RiemannRochHodgeIndex

/-!
# The fundamental injectivity theorem for snc log canonical boundaries

Let `V` be a smooth projective complex variety and `Δ = S + B` a `ℚ`-divisor with simple
normal crossing support and coefficients in `[0, 1]`, so that `S = ⌊Δ⌋` is its reduced part and
`B = {Δ}` its fractional part. If `M` is a Cartier divisor with `M ∼_ℚ K_V + Δ`, then for every
effective divisor `D` whose components are components of `B`, the map
`H^q(V, 𝒪_V(M)) ⟶ H^q(V, 𝒪_V(M + D))` induced by `𝒪_V(M) ⊆ 𝒪_V(M + D)` is injective for
every `q`. The coefficient-one part `S` is allowed: the boundary need not be klt.

## Main results

* `MMP.Mori.injective_derivedCohomologyOverField_map_divisorialSheafInclusion`: the
  injectivity of `H^q(V, 𝒪_V(M)) ⟶ H^q(V, 𝒪_V(M + D))`.

## Implementation notes

By Serre duality, natural in the line bundle, the injectivity is the surjectivity of
`H^{n-q}(V, 𝒪_V(K - M - D)) ⟶ H^{n-q}(V, 𝒪_V(K - M))`. With `𝓛 = 𝒪_V(M - K - S)` this is the
surjectivity of `H^k(𝓛⁻¹(-S-D)) ⟶ H^k(𝓛⁻¹(-S))`, which follows from the `E₁`-degeneration of
the fractional logarithmic complex `C^• = Ω^•_V(log (S + Supp B)) ⊗ 𝓛⁻¹(-S)` and the fact that
the subcomplex `C^•(-D)` is quasi-isomorphic to `C^•`, the residues of the connection along the
components of `D` not being integers.

The complex `C^•` is realised on the open set `U' = V ∖ (Supp Δ ∪ Supp M)` by explicit models
of rational logarithmic forms, and the inclusion `C^•(-D) ⟶ C^•` is shown to be a
quasi-isomorphism one component of `D` at a time: near a component `B` of `D`, contraction with
the logarithmic vector field `t ∂/∂t` along `B` is a homotopy between the residue `Bn(B)/N ∉ ℤ`
times the identity and a map landing in `C^•(-B)`. The degree-zero term of `C^•` is identified
with `𝒪_V(-M - S)`, and the dual `𝒪_V(L)^∨` of a divisorial sheaf with `𝒪_V(-L)` through the
multiplication pairing `𝒪_V(-L) ⊗ 𝒪_V(L) ⟶ 𝒪_V`, naturally in `L`.

* The boundary `S + B` is a single `ℚ`-divisor `Δ` with coefficients in `[0, 1]`; then
  `S = ⌊Δ⌋` (`MMP.Mori.DivisorWithCoeffs.roundDown`) and `B = {Δ}`
  (`MMP.Mori.DivisorWithCoeffs.fract`). Simple normal crossings is
  `MMP.Mori.DivisorWithCoeffs.IsSNC` of `Δ`.
* `H^q(V, ℱ)` for `q : ℤ` is the `q`-th cohomology of `derivedGlobalSectionsOver f` applied to
  `ℱ` placed in degree zero, and the map is the image of
  `MMP.Mori.Divisor.divisorialSheafInclusion` under these functors.

## References

* [O. Fujino, *Fundamental theorems for the log minimal model program*][Fujino2011],
  Proposition 4.1, Theorem 5.1
* [H. Esnault, E. Viehweg, *Lectures on vanishing theorems*][EsnaultViehweg1992]
* [J. Kollár, *Higher direct images of dualizing sheaves I*][Kollar1986]
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Proof_thm_mmp_lc_bpf_fundamental_injectivity

open MMP.Mori

section Duality

open scoped Stacks.SmallDerivedModel

open Stacks.Duality.LocallyFreeTwist

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Surjectivity transfers backwards along a commutative square whose vertical sides are
isomorphisms. -/
private theorem surjective_of_comm_sq {R : Type*} [Ring R] {M₁ M₂ N₁ N₂ : ModuleCat R}
    (a : M₁ ⟶ M₂) (b : N₁ ⟶ N₂) (e₁ : M₁ ≅ N₁) (e₂ : M₂ ≅ N₂) (w : a ≫ e₂.hom = e₁.hom ≫ b)
    (hb : Function.Surjective b.hom) : Function.Surjective a.hom := by
  intro y
  obtain ⟨x, hx⟩ := hb (e₂.hom.hom y)
  refine ⟨e₁.inv.hom x, ?_⟩
  have h1 : e₂.hom.hom (a.hom (e₁.inv.hom x)) = b.hom x := by
    have := congrArg (fun φ => φ.hom (e₁.inv.hom x)) w
    simpa using this
  have h2 := congrArg e₂.inv.hom (h1.trans hx)
  simpa using h2

/-- Surjectivity of `F.map φ` transfers along a natural isomorphism `F ≅ G`. -/
private theorem surjective_map_of_natIso {C : Type*} [Category C] {R : Type*} [Ring R]
    {F G : C ⥤ ModuleCat R} (τ : F ≅ G) {A B : C} (φ : A ⟶ B)
    (h : Function.Surjective (G.map φ).hom) : Function.Surjective (F.map φ).hom :=
  surjective_of_comm_sq _ _ (τ.app A) (τ.app B) (τ.hom.naturality φ) h

/-- Surjectivity of `F.map` transfers along an isomorphism of arrows. -/
private theorem surjective_map_of_comm_sq {C : Type*} [Category C] {R : Type*} [Ring R]
    (F : C ⥤ ModuleCat R) {A₁ A₂ B₁ B₂ : C} (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂) (e₁ : A₁ ≅ B₁)
    (e₂ : A₂ ≅ B₂) (w : a ≫ e₂.hom = e₁.hom ≫ b) (h : Function.Surjective (F.map b).hom) :
    Function.Surjective (F.map a).hom :=
  surjective_of_comm_sq _ _ (F.mapIso e₁) (F.mapIso e₂)
    (by simp only [Functor.mapIso_hom, ← Functor.map_comp, w]) h

/-- `H^i(X, Y⟦n⟧) ≅ H^{n+i}(X, Y)`, naturally in `Y`. -/
private noncomputable def shiftHomologyNatIso [IsProper f] (n i : ℤ) :
    shiftFunctor (DerivedCategory X.Modules) n ⋙ derivedGlobalSectionsOver f ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} k) i ≅
      derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) (n + i) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((derivedGlobalSectionsOver f).commShiftIso n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (eqToIso (DerivedCategory.shift_homologyFunctor
          (ModuleCat.{u} k) i).symm) ≪≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftIso n i (n + i) rfl ≪≫
        eqToIso (DerivedCategory.shift_homologyFunctor (ModuleCat.{u} k) (n + i)))

set_option maxRecDepth 20000 in
/-- **Injectivity from the surjectivity of the Serre dual map.** On a scheme smooth and proper
of relative dimension `n` over a field, a morphism `g : E₁ ⟶ E₂` of finite locally free modules
induces an injection `H^q(X, E₁) ⟶ H^q(X, E₂)` as soon as the dual morphism
`ω_X ⊗ g^∨ : ω_X ⊗ E₂^∨ ⟶ ω_X ⊗ E₁^∨` induces a surjection on `H^{n-q}`. -/
private theorem injective_of_surjective_dualMap [IsProper f] (n : ℕ)
    [SmoothOfRelativeDimension n f] {E₁ E₂ : Stacks.Duality.LocallyFreeTwist.Mod X}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₂] (g : E₁ ⟶ E₂) (q : ℤ)
    (h : Function.Surjective ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (n - q)).map
      ((derivedGlobalSectionsOver f).map ((DerivedCategory.singleFunctor X.Modules 0).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).obj
          (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n)).map
            (dualMap g))))).hom) :
    Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) q).map
      ((derivedGlobalSectionsOver f).map
        ((DerivedCategory.singleFunctor X.Modules 0).map g))).hom := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨i, rfl⟩ : ∃ i, q = -i := ⟨-q, (neg_neg q).symm⟩
  rw [sub_neg_eq_add] at h
  let ω := Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n
  obtain ⟨e⟩ :=
    (Stacks.Duality.nonempty_relativeDualizingComplex_iso_and_relativeDualizingModule_iso_of_smooth
      f n).1
  let Hf : ℤ → DerivedCategory X.Modules ⥤ ModuleCat.{u} k := fun j =>
    derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) j
  let Y := (DerivedCategory.singleFunctor X.Modules 0).obj ω
  let ε : (Stacks.Duality.dualizingComplexOverField f).obj ≅ Y⟦(n : ℤ)⟧ :=
    e ≪≫ (((DerivedCategory.singleFunctors X.Modules).shiftIso (n : ℤ) (-(n : ℤ)) 0
      (by omega)).app ω).symm
  have hβ : Function.Surjective
      ((Hf i).map ((GTMap g).app (Stacks.Duality.dualizingComplexOverField f).obj)).hom := by
    refine surjective_map_of_comm_sq (Hf i) _ ((GTMap g).app (Y⟦(n : ℤ)⟧))
      ((GT E₂).mapIso ε) ((GT E₁).mapIso ε) ((GTMap g).naturality ε.hom).symm ?_
    refine surjective_map_of_comm_sq (Hf i) _ (((GTMap g).app Y)⟦(n : ℤ)⟧')
      (GTCommShiftIso E₂ n Y) (GTCommShiftIso E₁ n Y) (GTMap_commShift g n Y) ?_
    refine surjective_map_of_natIso (F := shiftFunctor (DerivedCategory X.Modules) (n : ℤ) ⋙ Hf i)
      (shiftHomologyNatIso f n i) ((GTMap g).app Y) ?_
    refine surjective_map_of_comm_sq (Hf (n + i)) _ _
      (((twist X (dual E₂)).mapDerivedCategorySingleFunctor 0).app ω)
      (((twist X (dual E₁)).mapDerivedCategorySingleFunctor 0).app ω)
      (NatTrans.mapDerivedCategory_app_singleFunctor (twistMap (dualMap g)) ω) ?_
    have ht : (twistMap (dualMap g)).app ω =
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).obj ω).map
          (dualMap g) := Functor.flip_map_app _ _ _
    rw [ht]
    exact (show Function.Surjective ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (n + i)).map
      ((derivedGlobalSectionsOver f).map ((DerivedCategory.singleFunctor X.Modules 0).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).obj ω).map
          (dualMap g))))).hom from h)
  refine LinearMap.dualMap_surjective_iff.1 fun ψ => ?_
  obtain ⟨y, hy⟩ := hβ (dualityTwistLinearEquiv E₁ f i ψ)
  refine ⟨(dualityTwistLinearEquiv E₂ f i).symm y, (dualityTwistLinearEquiv E₁ f i).injective ?_⟩
  rw [LinearMap.dualMap_apply', dualityTwistLinearEquiv_naturality g f i,
    LinearEquiv.apply_symm_apply]
  exact hy

end Duality

section Inclusion

open MMP.FourfoldProofs.FractionalLogComplexProof

variable (n : ℕ) {X T : Scheme.{u}} (f : X ⟶ T) [SmoothOfRelativeDimension n f]
  [IsLocallyNoetherian X] [IsNormal X] (D : Divisor X) (hD : D.IsRelativeSNC n f) (S : Divisor X)
  {M M' : Divisor X}

/-- `U ∩ W ∩ U'_M ≤ U ∩ W ∩ U'_{M'}` when `U'_M ≤ U'_{M'}`. -/
private theorem OO_le (hU : cU' D M ≤ cU' D M') (W : X.Opens) : OO D M W ≤ OO D M' W :=
  Scheme.Hom.preimage_mono _ (inf_le_inf_left W hU)

/-- The forms on `U ∩ W ∩ U'_{M'}`, restricted to `U ∩ W ∩ U'_M`. -/
private noncomputable abbrev trf (hU : cU' D M ≤ cU' D M') (p : ℤ) (W : X.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.obj
      (op (OO D M' W))) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.obj
      (op (OO D M W)) :=
  ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.map
    (homOfLE (OO_le D hU W)).op ω

omit [SmoothOfRelativeDimension n f] in
/-- A section of `𝒪_X(-M')` on `W' ∩ U'_{M'}` restricts to a section of `𝒪_X(-M)` on
`W' ∩ U'_M`, for `M ≤ M'`. -/
private theorem DivCond.transfer (hU : cU' D M ≤ cU' D M') (hMM : M ≤ M') {W' : X.Opens}
    {g : Γ(X, W' ⊓ cU' D M')} (hg : DivCond (D := D) (M := M') W' g) :
    DivCond (D := D) (M := M) W' (X.presheaf.map (homOfLE (inf_le_inf_left W' hU)).op g) := by
  obtain ⟨a, ha, he⟩ := hg
  refine ⟨a, Divisor.divisorialSubmodule_mono (neg_le_neg hMM) W' ha, ?_⟩
  calc (rationalFunctionsPresheaf X).map (homOfLE inf_le_left).op a =
      (rationalFunctionsPresheaf X).map (homOfLE (inf_le_inf_left W' hU)).op
        ((rationalFunctionsPresheaf X).map (homOfLE inf_le_left).op a) := rfl
    _ = (rationalFunctionsPresheaf X).map (homOfLE (inf_le_inf_left W' hU)).op
        ((toRationalFunctionsPresheaf X).app (op (W' ⊓ cU' D M')) g) := by rw [he]
    _ = _ := (congrArg (fun φ => φ.hom g)
      ((toRationalFunctionsPresheaf X).naturality (homOfLE (inf_le_inf_left W' hU)).op)).symm

/-- **`Cond` transfers to a smaller twist.** A section of `𝒪_X(-M') · Ω^p(log D)(-S)` on `W`,
restricted to `U ∩ W ∩ U'_M`, is a section of `𝒪_X(-M) · Ω^p(log D)(-S)`, for `M ≤ M'`. -/
private theorem Cond.transfer (hU : cU' D M ≤ cU' D M') (hMM : M ≤ M') {p : ℕ} {W : X.Opens}
    {ω} (hω : Cond n f D hD S M' p W ω) : Cond n f D hD S M p W (trf f D hU p W ω) := by
  intro x hx
  obtain ⟨W', hW', hx', m, g, η, hg, hη, he⟩ := hω x hx
  refine ⟨W', hW', hx', m, fun i => X.presheaf.map (homOfLE (inf_le_inf_left _ hU)).op (g i), η,
    fun i => DivCond.transfer D hU hMM (hg i), hη, ?_⟩
  set φ : op (OO D M' W') ⟶ op (OO D M W') := (homOfLE (OO_le D hU W')).op
  have hR : ∀ z, (TB ((cU D).ι ≫ f)).totalRestrictRingHom φ z =
      (TB ((cU D).ι ≫ f)).totalRestrict φ z := fun z =>
    (TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply φ z
  let P := ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val
  have hk : OO D M W' ≤ OO D M' W := Scheme.Hom.preimage_mono _ (inf_le_inf hW' hU)
  have e1 : P.map (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) hW'))).op
      (trf f D hU p W ω) = P.map φ (P.map (homOfLE (Scheme.Hom.preimage_mono _
        (inf_le_inf_right (cU' D M') hW'))).op ω) :=
    (piece_map_map P (homOfLE (OO_le D hU W)).op _ (homOfLE hk).op ω).trans
      (piece_map_map P (homOfLE (Scheme.Hom.preimage_mono _
        (inf_le_inf_right (cU' D M') hW'))).op φ (homOfLE hk).op ω).symm
  have key : (TB ((cU D).ι ≫ f)).incl (p : ℤ)
      (P.map (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) hW'))).op
        (trf f D hU p W ω)) =
      (TB ((cU D).ι ≫ f)).totalRestrict φ ((TB ((cU D).ι ≫ f)).incl (p : ℤ)
        (P.map (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M') hW'))).op ω)) :=
    (congrArg ((TB ((cU D).ι ≫ f)).incl (p : ℤ)) e1).trans (incl_map f D φ (p : ℤ) _)
  rw [key, he, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hR, map_mul, hR, hR]
  refine congrArg₂ (· * ·) (((TB ((cU D).ι ≫ f)).structureMap_naturality φ _).trans
    (congrArg _ (G1.app_restrict (inf_le_inf_left (W' : X.Opens) hU) (g i)))) ?_
  refine (incl_map f D φ (p : ℤ) _).symm.trans (congrArg _ ?_)
  have hk' : OO D M W' ≤ (cU D).ι ⁻¹ᵁ W' := Scheme.Hom.preimage_mono _ inf_le_left
  exact piece_map_map P _ φ (homOfLE hk').op (η i)

/-- The restriction `j'_{M'*}Ω^p_{U'_{M'}} ⟶ j'_{M*}Ω^p_{U'_M}`, on sections. -/
private noncomputable def ambTr (hU : cU' D M ≤ cU' D M') (p : ℤ) (W : X.Opens)
    (x : Γ(amb f D M' p, W)) : Γ(amb f D M p, W) :=
  trInv f D M p W (trf f D hU p W (tr f D M' p W x))

private theorem tr_ambTr (hU : cU' D M ≤ cU' D M') (p : ℤ) (W : X.Opens)
    (x : Γ(amb f D M' p, W)) :
    tr f D M p W (ambTr f D hU p W x) = trf f D hU p W (tr f D M' p W x) :=
  tr_trInv f D M p W _

private theorem ambTr_add (hU : cU' D M ≤ cU' D M') (p : ℤ) (W : X.Opens)
    (x y : Γ(amb f D M' p, W)) :
    ambTr f D hU p W (x + y) = ambTr f D hU p W x + ambTr f D hU p W y := by
  refine tr_injective f D M p W ?_
  refine (tr_ambTr f D hU p W _).trans ((congrArg (trf f D hU p W) (tr_add f D M' p x y)).trans
    ((map_add _ _ _).trans ((congrArg₂ (· + ·) (tr_ambTr f D hU p W x).symm
      (tr_ambTr f D hU p W y).symm).trans (tr_add f D M p _ _).symm)))

private theorem resO_trf (hU : cU' D M ≤ cU' D M') (W : X.Opens) (r : Γ(X, W)) :
    (cU D).toScheme.presheaf.map (homOfLE (OO_le D hU W)).op (resO D M' W r) = resO D M W r :=
  (G1.app_restrict (inf_le_inf_left W hU) _).trans
    (congrArg _ (presheaf_map_map _ _ _ r))

private theorem ambTr_smul (hU : cU' D M ≤ cU' D M') (p : ℤ) (W : X.Opens)
    (r : X.ringCatSheaf.obj.obj (op W)) (x : (amb f D M' p).val.obj (op W)) :
    ambTr f D hU p W (r • x) =
      r • (show (amb f D M p).val.obj (op W) from ambTr f D hU p W x) := by
  refine tr_injective f D M p W ?_
  refine (tr_ambTr f D hU p W _).trans ((congrArg (trf f D hU p W) (tr_smul f D M' p r x)).trans
    ((PresheafOfModules.map_smul _ _ _ _).trans ?_))
  refine Eq.trans ?_ (tr_smul f D M p r _).symm
  exact congrArg₂ (· • ·) (resO_trf D hU W r) (tr_ambTr f D hU p W x).symm

private theorem ambTr_restrict (hU : cU' D M ≤ cU' D M') (p : ℤ) {W W' : X.Opens} (h : W' ≤ W)
    (x : Γ(amb f D M' p, W)) :
    ambTr f D hU p W' ((amb f D M' p).val.map (homOfLE h).op x) =
      (amb f D M p).val.map (homOfLE h).op (ambTr f D hU p W x) := by
  refine tr_injective f D M p W' ?_
  let P := ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val
  have hk : OO D M W' ≤ OO D M' W := (OO_le D hU W').trans
    (Scheme.Hom.preimage_mono _ (inf_le_inf_right _ h))
  refine (tr_ambTr f D hU p W' _).trans ((congrArg (trf f D hU p W')
    (tr_restrict f D M' p h x)).trans ((show trf f D hU p W' (P.map (homOfLE
      (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M') h))).op (tr f D M' p W x)) =
        P.map (homOfLE hk).op (tr f D M' p W x) from piece_map_map P _ _ _ _).trans ?_))
  refine Eq.trans ?_ (tr_restrict f D M p h _).symm
  refine Eq.trans ?_ (congrArg _ (tr_ambTr f D hU p W x)).symm
  exact (show P.map (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) h))).op
      (trf f D hU p W (tr f D M' p W x)) = P.map (homOfLE hk).op (tr f D M' p W x) from
    piece_map_map P _ _ _ _).symm

/-- **The inclusion `C^p_{M'} ⟶ C^p_M`** of `𝒪_X`-modules, `M ≤ M'`: restriction of forms from
`U'_{M'}` to `U'_M`. -/
private noncomputable def cModIncl (hU : cU' D M ≤ cU' D M') (hMM : M ≤ M') (p : ℕ) :
    cMod n f D hD S M' p ⟶ cMod n f D hD S M p :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun x =>
          ⟨ambTr f D hU (p : ℤ) W.unop x.1,
            (congrArg (Cond n f D hD S M p W.unop) (tr_ambTr f D hU (p : ℤ) W.unop x.1)).mpr
              (Cond.transfer n f D hD S hU hMM x.2)⟩)
        (fun x y => Subtype.ext (ambTr_add f D hU (p : ℤ) W.unop x.1 y.1)))
      naturality := fun {W W'} g => by
        ext x
        refine Subtype.ext ?_
        rw [show g = (homOfLE (leOfHom g.unop)).op from Subsingleton.elim _ _]
        exact ambTr_restrict f D hU (p : ℤ) (leOfHom g.unop) x.1 }
    (fun W a x => Subtype.ext (ambTr_smul f D hU (p : ℤ) W.unop a x.1))⟩

variable {D} in
private theorem θW_trf (hU : cU' D M ≤ cU' D M') {u' c' : Γ(X, cU' D M')} {u c : Γ(X, cU' D M)}
    (hu : X.presheaf.map (homOfLE hU).op u' = u) (hc : X.presheaf.map (homOfLE hU).op c' = c)
    (W : X.Opens) : trf f D hU 1 W (θW f D M' u' c' W) = θW f D M u c W := by
  unfold θW
  refine (PresheafOfModules.map_smul _ _ _ _).trans ?_
  have hres : ∀ a : Γ(X, cU' D M'), (cU D).toScheme.presheaf.map (homOfLE (OO_le D hU W)).op
      (resU W a) = resU W (X.presheaf.map (homOfLE hU).op a) := fun a =>
    (G1.app_restrict (inf_le_inf_left W hU) _).trans
      (congrArg _ ((presheaf_map_map _ _ (homOfLE (inf_le_right.trans hU)).op a).trans
        (presheaf_map_map _ _ (homOfLE (inf_le_right.trans hU)).op a).symm))
  refine congrArg₂ (· • ·) ((hres c').trans (congrArg _ hc)) ?_
  exact (dF_restrict f D _ _).trans (congrArg _ ((hres u').trans (congrArg _ hu)))

variable {D} in
private theorem nabA_ambTr (hU : cU' D M ≤ cU' D M') {u' c' : Γ(X, cU' D M')}
    {u c : Γ(X, cU' D M)} (hu : X.presheaf.map (homOfLE hU).op u' = u)
    (hc : X.presheaf.map (homOfLE hU).op c' = c) (p : ℕ) (W : X.Opens)
    (x : Γ(amb f D M' (p : ℤ), W)) :
    nabA f D M u c p W (ambTr f D hU (p : ℤ) W x) =
      ambTr f D hU ((p + 1 : ℕ) : ℤ) W (nabA f D M' u' c' p W x) := by
  refine tr_injective f D M _ W ?_
  refine (tr_nabA f D M u c p W _).trans ?_
  refine (congrArg _ (tr_ambTr f D hU (p : ℤ) W x)).trans ?_
  refine Eq.trans ?_ (tr_ambTr f D hU _ W _).symm
  refine Eq.trans ?_ (congrArg (trf f D hU _ W) (tr_nabA f D M' u' c' p W x)).symm
  refine Eq.trans ?_ (nab_map _ p _ _).symm
  rw [← θW_trf f hU hu hc W]

/-- **The inclusion of complexes `C^•_{M'} ⟶ C^•_M`**, for `M ≤ M'`, when the functions `u'`, `c'`
on `U'_{M'}` restrict to `u`, `c` on `U'_M`. -/
private noncomputable def cCxIncl (hU : cU' D M ≤ cU' D M') (hMM : M ≤ M')
    {u' c' : Γ(X, cU' D M')} {u c : Γ(X, cU' D M)}
    (hu : X.presheaf.map (homOfLE hU).op u' = u) (hc : X.presheaf.map (homOfLE hU).op c' = c)
    (hst' : NabStable n f D hD S M' u' c') (hloc' : LocMon n f D hD S M')
    (hcu' : ∀ W : X.Opens, δ ((cU D).ι ≫ f) (OO D M' W) (resU W c') *
      δ ((cU D).ι ≫ f) (OO D M' W) (resU W u') = 0)
    (hst : NabStable n f D hD S M u c) (hloc : LocMon n f D hD S M)
    (hcu : ∀ W : X.Opens, δ ((cU D).ι ≫ f) (OO D M W) (resU W c) *
      δ ((cU D).ι ≫ f) (OO D M W) (resU W u) = 0) :
    cCx n f D hD S M' u' c' hst' hloc' hcu' ⟶ cCx n f D hD S M u c hst hloc hcu :=
  CochainComplex.ofHom (fun p => (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap f))).map (cModIncl n f D hD S hU hMM p))
    (fun p => by
      rw [cCx_d, cCx_d]
      ext W x
      exact Subtype.ext (nabA_ambTr f hU hu hc p W.unop x.1))

private theorem ambTr_trans {M'' : Divisor X} (hU₁ : cU' D M ≤ cU' D M') (hU₂ : cU' D M' ≤ cU' D M'')
    (p : ℤ) (W : X.Opens) (x : Γ(amb f D M'' p, W)) :
    ambTr f D (hU₁.trans hU₂) p W x = ambTr f D hU₁ p W (ambTr f D hU₂ p W x) := by
  refine tr_injective f D M p W ?_
  rw [tr_ambTr, tr_ambTr, tr_ambTr]
  exact (piece_map_map ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val
    (homOfLE (OO_le D hU₂ W)).op (homOfLE (OO_le D hU₁ W)).op
    (homOfLE (OO_le D (hU₁.trans hU₂) W)).op _).symm

private theorem ambTr_self (hU : cU' D M ≤ cU' D M) (p : ℤ) (W : X.Opens)
    (x : Γ(amb f D M p, W)) : ambTr f D hU p W x = x := by
  refine tr_injective f D M p W ?_
  rw [tr_ambTr]
  exact piece_map_id _ _ _

private theorem cModIncl_trans {M'' : Divisor X} (hU₁ : cU' D M ≤ cU' D M')
    (hU₂ : cU' D M' ≤ cU' D M'') (hMM₁ : M ≤ M') (hMM₂ : M' ≤ M'') (p : ℕ) :
    cModIncl n f D hD S (hU₁.trans hU₂) (hMM₁.trans hMM₂) p =
      cModIncl n f D hD S hU₂ hMM₂ p ≫ cModIncl n f D hD S hU₁ hMM₁ p := by
  ext W x
  exact Subtype.ext (ambTr_trans f D hU₁ hU₂ (p : ℤ) W x.1)

private theorem cModIncl_self (hU : cU' D M ≤ cU' D M) (hMM : M ≤ M) (p : ℕ) :
    cModIncl n f D hD S hU hMM p = 𝟙 _ := by
  ext W x
  exact Subtype.ext (ambTr_self f D hU (p : ℤ) W x.1)

variable {D} in
private theorem cCxIncl_trans {M'' : Divisor X} (hU₁ : cU' D M ≤ cU' D M')
    (hU₂ : cU' D M' ≤ cU' D M'') (hMM₁ : M ≤ M') (hMM₂ : M' ≤ M'')
    {u'' c'' : Γ(X, cU' D M'')} {u' c' : Γ(X, cU' D M')} {u c : Γ(X, cU' D M)}
    (hu₂ : X.presheaf.map (homOfLE hU₂).op u'' = u') (hc₂ : X.presheaf.map (homOfLE hU₂).op c'' = c')
    (hu₁ : X.presheaf.map (homOfLE hU₁).op u' = u) (hc₁ : X.presheaf.map (homOfLE hU₁).op c' = c)
    (hu : X.presheaf.map (homOfLE (hU₁.trans hU₂)).op u'' = u)
    (hc : X.presheaf.map (homOfLE (hU₁.trans hU₂)).op c'' = c)
    (hst'' : NabStable n f D hD S M'' u'' c'') (hloc'' : LocMon n f D hD S M'')
    (hcu'' : ∀ W : X.Opens, δ ((cU D).ι ≫ f) (OO D M'' W) (resU W c'') *
      δ ((cU D).ι ≫ f) (OO D M'' W) (resU W u'') = 0)
    (hst' : NabStable n f D hD S M' u' c') (hloc' : LocMon n f D hD S M')
    (hcu' : ∀ W : X.Opens, δ ((cU D).ι ≫ f) (OO D M' W) (resU W c') *
      δ ((cU D).ι ≫ f) (OO D M' W) (resU W u') = 0)
    (hst : NabStable n f D hD S M u c) (hloc : LocMon n f D hD S M)
    (hcu : ∀ W : X.Opens, δ ((cU D).ι ≫ f) (OO D M W) (resU W c) *
      δ ((cU D).ι ≫ f) (OO D M W) (resU W u) = 0) :
    cCxIncl n f D hD S (hU₁.trans hU₂) (hMM₁.trans hMM₂) hu hc hst'' hloc'' hcu'' hst hloc hcu =
      cCxIncl n f D hD S hU₂ hMM₂ hu₂ hc₂ hst'' hloc'' hcu'' hst' hloc' hcu' ≫
        cCxIncl n f D hD S hU₁ hMM₁ hu₁ hc₁ hst' hloc' hcu' hst hloc hcu := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  rw [HomologicalComplex.comp_f]
  exact (congrArg (fun φ => (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap f))).map φ)
      (cModIncl_trans n f D hD S hU₁ hU₂ hMM₁ hMM₂ p)).trans (Functor.map_comp _ _ _)

variable {D} in
private theorem cCxIncl_self (hU : cU' D M ≤ cU' D M) (hMM : M ≤ M) {u c : Γ(X, cU' D M)}
    (hu : X.presheaf.map (homOfLE hU).op u = u) (hc : X.presheaf.map (homOfLE hU).op c = c)
    (hst : NabStable n f D hD S M u c) (hloc : LocMon n f D hD S M)
    (hcu : ∀ W : X.Opens, δ ((cU D).ι ≫ f) (OO D M W) (resU W c) *
      δ ((cU D).ι ≫ f) (OO D M W) (resU W u) = 0) :
    cCxIncl n f D hD S hU hMM hu hc hst hloc hcu hst hloc hcu = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  rw [HomologicalComplex.id_f]
  exact (congrArg (fun φ => (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap f))).map φ)
      (cModIncl_self n f D hD S hU hMM p)).trans (CategoryTheory.Functor.map_id _ _)

end Inclusion

section Factorization

open MMP.FourfoldProofs.FractionalLogComplexProof

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (D M : Divisor X)

/-- **A factorization of a local generator on a chart.** Let `W₂` be an affine open on which the
ideals of the components `jₖ` of `D` are generated by `τₖ`, with `D = V(∏ τₖ)` on `W₂`, and on
which `M` has a local equation `φ₀`. If `N M = Bn + div ψ` with `Bn` effective and supported on
`D`, and `u = ψ` on `U'`, then a generator `g₀ = φ₀` of `𝒪_X(-M)` on `W₂` satisfies
`g₀^N = u · v · ∏ τₖ^{Bn(jₖ)}` on `W₂ ∩ U'` for a unit `v` on `W₂`. -/
private theorem exists_generator_factorization_on (uu : Γ(X, cU' D M)) (Bn : Divisor X) (N : ℕ)
    (ψ : (RationalFunctions X)ˣ) (hψ : (N : ℤ) • M = Bn + principalDivisor ψ)
    (hu : (toRationalFunctionsPresheaf X).app (op (cU' D M)) uu = ratRes (cU' D M) ψ)
    (hBn : ∀ E, 0 ≤ Bn E) (hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support) {W₂ : X.affineOpens} {r : ℕ}
    (τ : Fin r → Γ(X, W₂)) (j : Fin r → MMP.Mori.PrimeDivisor X) (hj : Function.Injective j)
    (hτ : ∀ k, (j k).idealSheaf.ideal W₂ = Ideal.span {τ k})
    (hDW₂ : D.suppIdeal.ideal W₂ = Ideal.span {∏ k, τ k}) {φ₀ : (RationalFunctions X)ˣ}
    (hφ₀ : M.IsLocalEquation W₂ φ₀) :
    ∃ (v : Γ(X, W₂)) (g₀ : Γ(X, (W₂ : X.Opens) ⊓ cU' D M)),
      IsUnit v ∧
      (toRationalFunctionsPresheaf X).app (op ((W₂ : X.Opens) ⊓ cU' D M)) g₀ =
        ratRes ((W₂ : X.Opens) ⊓ cU' D M) φ₀ ∧
      DivCond (D := D) (M := M) (W₂ : X.Opens) g₀ ∧
      (∀ (W₃ : X.Opens) (h₃ : W₃ ≤ W₂) (g : Γ(X, W₃ ⊓ cU' D M)), DivCond (D := D) (M := M) W₃ g →
        ∃ h : Γ(X, W₃), g = X.presheaf.map (homOfLE inf_le_left).op h *
          X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op g₀) ∧
      g₀ ^ N = X.presheaf.map (homOfLE inf_le_right).op uu *
        X.presheaf.map (homOfLE inf_le_left).op (v * ∏ k, τ k ^ (Bn (j k)).toNat) := by
  classical
  let b : Fin r → ℕ := fun k => (Bn (j k)).toNat
  have hord : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ (W₂ : X.Opens)).Nonempty →
      E.ord (φ₀ ^ N * ψ⁻¹) = ∑ k, if E = j k then (b k : ℤ) else 0 := by
    intro E hE
    have hBnE : Bn E = ∑ k, if E = j k then (b k : ℤ) else 0 := by
      by_cases hEj : ∃ k, E = j k
      · obtain ⟨k0, rfl⟩ := hEj
        rw [Finset.sum_eq_single k0 (fun k _ hk => ite_eq_right (fun h => hk (hj h).symm))
          (by simp), ite_eq_left rfl]
        exact (Int.toNat_of_nonneg (hBn _)).symm
      · rw [Finset.sum_eq_zero (fun k _ => ite_eq_right fun h => hEj ⟨k, h⟩)]
        by_contra hne
        obtain ⟨x, hxE, hxW⟩ := hE
        obtain ⟨k, hk⟩ := exists_eq_of_mem_chart τ le_rfl j hτ hDW₂ (hBD E hne)
          hxW hxE
        exact hEj ⟨k, hk.symm⟩
    have h1 := congrArg (fun F : Divisor X => F E) hψ
    simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul] at h1
    rw [MMP.Mori.PrimeDivisor.ord_mul, MMP.Mori.PrimeDivisor.ord_pow,
      MMP.Mori.PrimeDivisor.ord_inv, ← hφ₀ E hE, ← MMP.Mori.coeff_principalDivisor, ← hBnE,
      nsmul_eq_mul]
    change (N : ℤ) * M E + -(MMP.Mori.principalDivisor ψ) E = Bn E
    linarith
  obtain ⟨v, hvu, hvrel⟩ := exists_isUnit_mul_prod_pow W₂ τ j hτ b (φ₀ ^ N * ψ⁻¹) hord
  obtain ⟨g₀, hg₀rat, hg₀div, hg₀gen⟩ := exists_generator D M hφ₀
  have hX : g₀ ^ N = X.presheaf.map (homOfLE inf_le_right).op uu *
      X.presheaf.map (homOfLE inf_le_left).op (v * ∏ k, τ k ^ b k) := by
    apply toRationalFunctionsPresheaf_app_injective
    have n1 := congrArg (fun φ => φ.hom uu) ((toRationalFunctionsPresheaf X).naturality
      (homOfLE (inf_le_right : (W₂ : X.Opens) ⊓ cU' D M ≤ cU' D M)).op)
    have n2 := congrArg (fun φ => φ.hom (v * ∏ k, τ k ^ b k))
      ((toRationalFunctionsPresheaf X).naturality
        (homOfLE (inf_le_left : (W₂ : X.Opens) ⊓ cU' D M ≤ W₂)).op)
    rw [map_pow, map_mul, hg₀rat]
    erw [n1, n2]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [hu, hvrel]
    funext Z
    change ((φ₀ : RationalFunctions X) Z.1) ^ N =
      (ψ : RationalFunctions X) Z.1 * (↑(φ₀ ^ N * ψ⁻¹) : RationalFunctions X) Z.1
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Pi.mul_apply, Pi.pow_apply, mul_left_comm,
      ← Pi.mul_apply (↑ψ : RationalFunctions X), Units.mul_inv, Pi.one_apply, mul_one]
  exact ⟨v, g₀, hvu, hg₀rat, hg₀div, hg₀gen, hX⟩

/-- **The generator for the next twist.** If `φ₀`, `φ₀'` are local equations on `W₂` of `M` and
`M + B`, `B` a prime divisor with local equation `τ` on `W₂`, then the generators `g₀ = φ₀` and
`g₀' = φ₀'` satisfy `g₀' = v' τ g₀` on `W₂ ∩ U'_M` for a unit `v'` on `W₂`. -/
private theorem exists_generator_add_single (B : MMP.Mori.PrimeDivisor X) {M' : Divisor X}
    (hM' : M' = M + Finsupp.single B 1) (hU : cU' D M ≤ cU' D M') {W₂ : X.affineOpens}
    {τ : Γ(X, W₂)} (hτ : B.idealSheaf.ideal W₂ = Ideal.span {τ}) {φ₀ φ₀' : (RationalFunctions X)ˣ}
    (hφ₀ : M.IsLocalEquation W₂ φ₀) (hφ₀' : M'.IsLocalEquation W₂ φ₀')
    {g₀ : Γ(X, (W₂ : X.Opens) ⊓ cU' D M)} {g₀' : Γ(X, (W₂ : X.Opens) ⊓ cU' D M')}
    (hg₀ : (toRationalFunctionsPresheaf X).app (op ((W₂ : X.Opens) ⊓ cU' D M)) g₀ =
      ratRes ((W₂ : X.Opens) ⊓ cU' D M) φ₀)
    (hg₀' : (toRationalFunctionsPresheaf X).app (op ((W₂ : X.Opens) ⊓ cU' D M')) g₀' =
      ratRes ((W₂ : X.Opens) ⊓ cU' D M') φ₀') :
    ∃ v' : Γ(X, W₂), IsUnit v' ∧
      X.presheaf.map (homOfLE (inf_le_inf_left (W₂ : X.Opens) hU)).op g₀' =
        X.presheaf.map (homOfLE inf_le_left).op (v' * τ) * g₀ := by
  classical
  have hord : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ (W₂ : X.Opens)).Nonempty →
      E.ord (φ₀' * φ₀⁻¹) = ∑ k : Fin 1, if E = ![B] k then ((![1] : Fin 1 → ℕ) k : ℤ) else 0 := by
    intro E hE
    rw [MMP.Mori.PrimeDivisor.ord_mul, MMP.Mori.PrimeDivisor.ord_inv, ← hφ₀' E hE, ← hφ₀ E hE,
      hM']
    simp only [Fin.sum_univ_one, Matrix.cons_val_fin_one, Nat.cast_one]
    rw [DivisorWithCoeffs.coeff_add]
    unfold DivisorWithCoeffs.coeff
    rw [Finsupp.single_apply]
    by_cases h : B = E
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  obtain ⟨v', hv'u, hv'⟩ := exists_isUnit_mul_prod_pow W₂ ![τ] ![B]
    (fun k => by fin_cases k; exact hτ) ![1] (φ₀' * φ₀⁻¹) hord
  simp only [Fin.prod_univ_one, Matrix.cons_val_fin_one, pow_one] at hv'
  refine ⟨v', hv'u, toRationalFunctionsPresheaf_app_injective _ ?_⟩
  have n1 := congrArg (fun φ => φ.hom g₀') ((toRationalFunctionsPresheaf X).naturality
    (homOfLE (inf_le_inf_left (W₂ : X.Opens) hU)).op)
  have n2 := congrArg (fun φ => φ.hom (v' * τ)) ((toRationalFunctionsPresheaf X).naturality
    (homOfLE (inf_le_left : (W₂ : X.Opens) ⊓ cU' D M ≤ W₂)).op)
  rw [map_mul]
  erw [n1, n2]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [hg₀', hg₀, hv']
  funext Z
  change (φ₀' : RationalFunctions X) Z.1 =
    (↑(φ₀' * φ₀⁻¹) : RationalFunctions X) Z.1 * (φ₀ : RationalFunctions X) Z.1
  rw [Units.val_mul, Pi.mul_apply, mul_assoc, ← Pi.mul_apply (↑φ₀⁻¹ : RationalFunctions X),
    Units.inv_mul, Pi.one_apply, mul_one]

open Classical in
/-- **The ideal of a subdivisor on a chart.** On a chart `W` of the relative snc divisor `D`, the
ideal of the support of a divisor `S` whose components are components of `D` is generated by the
product of the coordinates of the components of `S`. -/
private theorem suppIdeal_eq_span_prod_of_chart (n : ℕ) {T : Scheme.{u}} (f : X ⟶ T)
    (S : Divisor X) (hSD : ∀ E ∈ S.support, E ∈ D.support) {W : X.affineOpens}
    {V : T.affineOpens} {e : (W : X.Opens) ≤ f ⁻¹ᵁ (V : T.Opens)} {t : Fin n → Γ(X, W)}
    (hb : letI := (f.appLE V W e).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄Γ(T, V)],
        ∀ i, b i = KaehlerDifferential.D Γ(T, V) Γ(X, W) (t i))
    {r : ℕ} (hr : r ≤ n) {j : Fin r → MMP.Mori.PrimeDivisor X}
    (hj : ∀ i, (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)})
    (hDW : D.suppIdeal.ideal W = Ideal.span {∏ i, t (Fin.castLE hr i)}) :
    S.suppIdeal.ideal W = Ideal.span {(∏ k ∈ Finset.univ.filter (fun k : Fin r => j k ∈ S.support),
      t (Fin.castLE hr k))} := by
  let := (f.appLE V W e).hom.toAlgebra
  obtain ⟨b, hb⟩ := hb
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian W
  set P := Finset.univ.filter (fun i : Fin r => j i ∈ S.support) with hP
  have hrad : ∀ k ∈ P.map (Fin.castLEEmb hr), (Ideal.span {t k}).IsRadical := by
    intro k hk
    obtain ⟨i0, -, rfl⟩ := Finset.mem_map.mp hk
    change (Ideal.span {t (Fin.castLE hr i0)}).IsRadical
    rw [← hj i0]
    exact isRadical_idealSheaf_ideal _ W
  have hSW : S.suppIdeal.ideal W = ⨅ k ∈ P.map (Fin.castLEEmb hr), Ideal.span {t k} := by
    rw [MMP.Intersection.suppIdeal_eq_finsetInf, finsetInf_ideal]
    refine le_antisymm (le_iInf₂ fun k hk => ?_) (Finset.le_inf fun E hE => ?_)
    · obtain ⟨i0, hi0, rfl⟩ := Finset.mem_map.mp hk
      exact (Finset.inf_le (Finset.mem_filter.mp hi0).2).trans (le_of_eq (hj i0))
    · by_cases hmeet : ∃ y ∈ (W : X.Opens), y ∈ E.support
      · obtain ⟨y, hyW, hyE⟩ := hmeet
        obtain ⟨i0, rfl⟩ := exists_eq_of_mem_chart t hr j hj hDW (hSD E hE)
          hyW hyE
        exact (iInf₂_le (Fin.castLE hr i0) (Finset.mem_map_of_mem (Fin.castLEEmb hr)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ i0, hE⟩))).trans (le_of_eq (hj i0).symm)
      · rw [ideal_eq_top_of_disjoint _ W (fun y hy hyE => hmeet ⟨y, hy, hyE⟩)]
        exact le_top
  rw [← span_prod_eq_iInf_of_basis_D t b hb _ hrad, Finset.prod_map] at hSW
  exact hSW

end Factorization

section LogLattice

open KaehlerDifferential exteriorPower

variable {k B : Type u} [Field k] [CommRing B] [Algebra k B] {n : ℕ} (β : Fin n → Ω[B⁄k])

/-- The forms `∑ c_w β_{w₁} ∧ ⋯ ∧ β_{w_p}` with coefficients `c_w` in an additive subgroup `J`. -/
private noncomputable def logLattice (J : AddSubgroup B) (p : ℕ) : AddSubgroup (⋀[B]^p (Ω[B⁄k])) :=
  AddSubgroup.closure {x | ∃ c ∈ J, ∃ w : Fin p → Fin n, x = c • ιMulti B p (β ∘ w)}

variable {β}

private theorem gen_mem_logLattice {J : AddSubgroup B} {p : ℕ} {c : B} (hc : c ∈ J)
    (w : Fin p → Fin n) : c • ιMulti B p (β ∘ w) ∈ logLattice β J p :=
  AddSubgroup.subset_closure ⟨c, hc, w, rfl⟩

private theorem logLattice_induction {J : AddSubgroup B} {p q : ℕ}
    (F : ⋀[B]^p (Ω[B⁄k]) →+ ⋀[B]^q (Ω[B⁄k])) (G : AddSubgroup (⋀[B]^q (Ω[B⁄k])))
    (h : ∀ c ∈ J, ∀ w : Fin p → Fin n, F (c • ιMulti B p (β ∘ w)) ∈ G) {x}
    (hx : x ∈ logLattice β J p) : F x ∈ G := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, w, rfl⟩ := hx
    exact h c hc w
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

/-- Scalar multiplication by a function `a` with `a J ⊆ J'` maps `logLattice β J` into
`logLattice β J'`. -/
private theorem smul_mem_logLattice {J J' : AddSubgroup B} {p : ℕ} {a : B}
    (ha : ∀ c ∈ J, a * c ∈ J') {x} (hx : x ∈ logLattice β J p) : a • x ∈ logLattice β J' p := by
  refine logLattice_induction (AddMonoidHom.mk' (fun x => a • x) (fun x y => smul_add a x y)) _
    (fun c hc w => ?_) hx
  change a • (c • ιMulti B p (β ∘ w)) ∈ _
  rw [smul_smul]
  exact gen_mem_logLattice (ha c hc) w

/-- Contraction against `φ` maps the lattice with coefficients in `J` into itself when the values
`φ(βᵢ)` multiply `J` into itself. -/
private theorem contraction_mem_logLattice (φ : Ω[B⁄k] →ₗ[B] B) {J : AddSubgroup B} {p : ℕ}
    (hφ : ∀ i, ∀ c ∈ J, φ (β i) * c ∈ J) {x} (hx : x ∈ logLattice β J (p + 1)) :
    contraction φ p x ∈ logLattice β J p := by
  refine logLattice_induction (contraction φ p).toAddMonoidHom _ (fun c hc w => ?_) hx
  change contraction φ p (c • ιMulti B (p + 1) (β ∘ w)) ∈ _
  rw [map_smul, contraction_ιMulti, Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  rw [smul_comm c ((-1 : ℤ) ^ (i : ℕ)), smul_smul]
  refine zsmul_mem ?_ _
  rw [mul_comm]
  exact gen_mem_logLattice (hφ (w i) c hc) (Fin.removeNth i w)

/-- The Lie derivative maps the lattice with coefficients in `J` into that with coefficients in
`J'` when it kills the monomials and `φ(dc) ∈ J'` for `c ∈ J`. -/
private theorem lie_mem_logLattice (φ : Ω[B⁄k] →ₗ[B] B) {J J' : AddSubgroup B} {p : ℕ}
    (hlie : ∀ w : Fin p → Fin n, Cartier.lie k φ p (ιMulti B p (β ∘ w)) = 0)
    (hD : ∀ c ∈ J, φ (D k B c) ∈ J') {x} (hx : x ∈ logLattice β J p) :
    Cartier.lie k φ p x ∈ logLattice β J' p := by
  refine logLattice_induction (Cartier.lie k φ p).toAddMonoidHom _ (fun c hc w => ?_) hx
  change Cartier.lie k φ p (c • ιMulti B p (β ∘ w)) ∈ _
  rw [Cartier.lie_smul, hlie, smul_zero, add_zero]
  exact gen_mem_logLattice (hD c hc) w

/-- **Cartan's formula for the twisted differential** `∇ = d + ξ ∧`:
`ι_φ ∇ η + ∇ ι_φ η = L_φ η + φ(ξ) η`. -/
private theorem cartan_twisted (φ : Ω[B⁄k] →ₗ[B] B) (ξ : Ω[B⁄k]) (p : ℕ)
    (η : ⋀[B]^(p + 1) (Ω[B⁄k])) :
    contraction φ (p + 1) (deRhamDifferential (A := k) (p + 1) η + wedgeLeft ξ (p + 1) η) +
        (deRhamDifferential (A := k) p (contraction φ p η) + wedgeLeft ξ p (contraction φ p η)) =
      Cartier.lie k φ (p + 1) η + φ ξ • η := by
  have hk := LinearMap.congr_fun
    (contraction_comp_wedgeLeft_add_wedgeLeft_comp_contraction φ ξ p) η
  simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq] at hk
  rw [Cartier.lie_succ_apply, ← hk, map_add]
  abel

/-- **Cartan's formula in degree zero**: `ι_φ ∇ η = L_φ η + φ(ξ) η` for a function `η`. -/
private theorem cartan_twisted_zero (φ : Ω[B⁄k] →ₗ[B] B) (ξ : Ω[B⁄k])
    (η : ⋀[B]^0 (Ω[B⁄k])) :
    contraction φ 0 (deRhamDifferential (A := k) 0 η + wedgeLeft ξ 0 η) =
      Cartier.lie k φ 0 η + φ ξ • η := by
  rw [map_add, Cartier.lie_zero_apply]
  exact congrArg _ (LinearMap.congr_fun (contraction_comp_wedgeLeft_zero φ ξ) η)

/-- **The homotopy for a twisted logarithmic differential.** Let `∇ = d + ξ ∧` with
`ξ = ∑ aᵢ βᵢ`, `aᵢ ∈ A`, and let `φ` be a functional with `φ(βᵢ) ∈ A`, whose Lie derivative kills
the monomials in the `βᵢ` and maps the coefficients `J` into `J'`, and with `φ(ξ) ≡ λ` modulo
`J'`, `λ ≠ 0` a scalar. If `η` has coefficients in `J` and `∇ η` coefficients in `J'`, then
`ι_φ η` has coefficients in `J` and `η - ∇(λ⁻¹ ι_φ η)` coefficients in `J'`. -/
private theorem sub_nab_contraction_mem (φ : Ω[B⁄k] →ₗ[B] B) {J J' : AddSubgroup B}
    (A : Subring B) (hJA : ∀ a ∈ A, ∀ c ∈ J, a * c ∈ J) (hJ'A : ∀ a ∈ A, ∀ c ∈ J', a * c ∈ J')
    (hkA : ∀ c : k, algebraMap k B c ∈ A) (hφ : ∀ i, φ (β i) ∈ A)
    (hlie : ∀ (q : ℕ) (w : Fin q → Fin n), Cartier.lie k φ q (ιMulti B q (β ∘ w)) = 0)
    (hD : ∀ c ∈ J, φ (D k B c) ∈ J') (a : Fin n → B) (ha : ∀ i, a i ∈ A) (lam : k)
    (hlam : lam ≠ 0)
    (hξ : ∀ c ∈ J, (φ (∑ i, a i • β i) - algebraMap k B lam) * c ∈ J')
    {p : ℕ} {η : ⋀[B]^(p + 1) (Ω[B⁄k])} (hη : η ∈ logLattice β J (p + 1))
    (hnab : deRhamDifferential (A := k) (p + 1) η + wedgeLeft (∑ i, a i • β i) (p + 1) η ∈
      logLattice β J' (p + 2)) :
    contraction φ p η ∈ logLattice β J p ∧
      η - (deRhamDifferential (A := k) p (lam⁻¹ • contraction φ p η) +
        wedgeLeft (∑ i, a i • β i) p (lam⁻¹ • contraction φ p η)) ∈ logLattice β J' (p + 1) := by
  set ξ := ∑ i, a i • β i
  set ι := contraction φ p η
  refine ⟨contraction_mem_logLattice φ (fun i c hc => hJA _ (hφ i) c hc) hη, ?_⟩
  have hcart := cartan_twisted φ ξ p η
  have hsm : deRhamDifferential (A := k) p (lam⁻¹ • ι) + wedgeLeft ξ p (lam⁻¹ • ι) =
      lam⁻¹ • (deRhamDifferential (A := k) p ι + wedgeLeft ξ p ι) := by
    rw [map_smul, smul_add, ← algebraMap_smul B lam⁻¹ ι, map_smul, algebraMap_smul]
  have e1 : contraction φ (p + 1) (deRhamDifferential (A := k) (p + 1) η + wedgeLeft ξ (p + 1) η)
      - Cartier.lie k φ (p + 1) η - (φ ξ - algebraMap k B lam) • η =
      algebraMap k B lam • η - (deRhamDifferential (A := k) p ι + wedgeLeft ξ p ι) := by
    rw [sub_smul, eq_sub_of_add_eq hcart]
    abel
  have e2 : η - lam⁻¹ • (deRhamDifferential (A := k) p ι + wedgeLeft ξ p ι) =
      algebraMap k B lam⁻¹ • (contraction φ (p + 1) (deRhamDifferential (A := k) (p + 1) η +
        wedgeLeft ξ (p + 1) η) - Cartier.lie k φ (p + 1) η - (φ ξ - algebraMap k B lam) • η) := by
    rw [e1, smul_sub, smul_smul, ← map_mul, inv_mul_cancel₀ hlam, map_one, one_smul,
      algebraMap_smul]
  rw [hsm, e2]
  refine smul_mem_logLattice (fun c hc => hJ'A _ (hkA _) c hc) (sub_mem (sub_mem ?_ ?_) ?_)
  · exact contraction_mem_logLattice φ (fun i c hc => hJ'A _ (hφ i) c hc) hnab
  · exact lie_mem_logLattice φ (hlie (p + 1)) hD hη
  · exact smul_mem_logLattice hξ hη

/-- **The homotopy in degree zero.** Under the hypotheses of `sub_nab_contraction_mem`, a
function `η` with coefficients in `J` and `∇ η` with coefficients in `J'` has coefficients in
`J'`. -/
private theorem mem_logLattice_of_nab_mem_zero (φ : Ω[B⁄k] →ₗ[B] B) {J J' : AddSubgroup B}
    (A : Subring B) (hJ'A : ∀ a ∈ A, ∀ c ∈ J', a * c ∈ J')
    (hkA : ∀ c : k, algebraMap k B c ∈ A) (hφ : ∀ i, φ (β i) ∈ A)
    (hlie : ∀ (q : ℕ) (w : Fin q → Fin n), Cartier.lie k φ q (ιMulti B q (β ∘ w)) = 0)
    (hD : ∀ c ∈ J, φ (D k B c) ∈ J') (a : Fin n → B) (lam : k) (hlam : lam ≠ 0)
    (hξ : ∀ c ∈ J, (φ (∑ i, a i • β i) - algebraMap k B lam) * c ∈ J')
    {η : ⋀[B]^0 (Ω[B⁄k])} (hη : η ∈ logLattice β J 0)
    (hnab : deRhamDifferential (A := k) 0 η + wedgeLeft (∑ i, a i • β i) 0 η ∈
      logLattice β J' 1) :
    η ∈ logLattice β J' 0 := by
  set ξ := ∑ i, a i • β i
  have hcart := cartan_twisted_zero φ ξ η
  have e : η = algebraMap k B lam⁻¹ • (contraction φ 0 (deRhamDifferential (A := k) 0 η +
      wedgeLeft ξ 0 η) - Cartier.lie k φ 0 η - (φ ξ - algebraMap k B lam) • η) := by
    have e1 : contraction φ 0 (deRhamDifferential (A := k) 0 η + wedgeLeft ξ 0 η) -
        Cartier.lie k φ 0 η - (φ ξ - algebraMap k B lam) • η = algebraMap k B lam • η := by
      rw [hcart, sub_smul]
      abel
    rw [e1, smul_smul, ← map_mul, inv_mul_cancel₀ hlam, map_one, one_smul]
  rw [e]
  refine smul_mem_logLattice (fun c hc => hJ'A _ (hkA _) c hc) (sub_mem (sub_mem ?_ ?_) ?_)
  · exact contraction_mem_logLattice φ (fun i c hc => hJ'A _ (hφ i) c hc) hnab
  · exact lie_mem_logLattice φ (hlie 0) hD hη
  · exact smul_mem_logLattice hξ hη

/-- The lattice with coefficients `c J` is `c` times the lattice with coefficients `J`. -/
private theorem exists_smul_of_mem_logLattice_map {J : AddSubgroup B} {p : ℕ} (c : B) {y}
    (hy : y ∈ logLattice β (J.map (AddMonoidHom.mulLeft c)) p) :
    ∃ y₁ ∈ logLattice β J p, y = c • y₁ := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨_, ⟨a, ha, rfl⟩, w, rfl⟩ := hx
    exact ⟨a • ιMulti B p (β ∘ w), gen_mem_logLattice ha w, by
      rw [smul_smul]; rfl⟩
  | zero => exact ⟨0, zero_mem _, (smul_zero c).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨x₁, hx₁, rfl⟩ := hx
    obtain ⟨y₁, hy₁, rfl⟩ := hy
    exact ⟨x₁ + y₁, add_mem hx₁ hy₁, (smul_add c x₁ y₁).symm⟩
  | neg x _ hx =>
    obtain ⟨x₁, hx₁, rfl⟩ := hx
    exact ⟨-x₁, neg_mem hx₁, (smul_neg c x₁).symm⟩

private theorem smul_mem_logLattice_map {J : AddSubgroup B} {p : ℕ} (c : B) {y}
    (hy : y ∈ logLattice β J p) : c • y ∈ logLattice β (J.map (AddMonoidHom.mulLeft c)) p :=
  smul_mem_logLattice (fun a ha => AddSubgroup.mem_map.mpr ⟨a, ha, rfl⟩) hy

private theorem map_mulLeft_one (J : AddSubgroup B) : J.map (AddMonoidHom.mulLeft (1 : B)) = J := by
  ext a
  simp

end LogLattice

section LogBasis

open KaehlerDifferential exteriorPower

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {n : ℕ} (t : Fin n → K) (r : ℕ)

/-- The logarithmic basis `dtᵢ/tᵢ` (`i < r`), `dtᵢ` (`i ≥ r`). -/
private noncomputable def logBasis : Fin n → Ω[K⁄k] := fun i =>
  if (i : ℕ) < r then (t i)⁻¹ • D k K (t i) else D k K (t i)

/-- The functional `tᵢ₀ · ∂/∂tᵢ₀` for a basis `dtᵢ` of `Ω`. -/
private noncomputable def logFunctional (b : Module.Basis (Fin n) K Ω[K⁄k]) (i₀ : Fin n) :
    Ω[K⁄k] →ₗ[K] K :=
  t i₀ • b.coord i₀

variable {t r}

private theorem logFunctional_D {b : Module.Basis (Fin n) K Ω[K⁄k]}
    (hb : ∀ i, b i = D k K (t i)) (i₀ i : Fin n) :
    logFunctional t b i₀ (D k K (t i)) = if i = i₀ then t i₀ else 0 := by
  rw [logFunctional, LinearMap.smul_apply, ← hb, Module.Basis.coord_apply, Module.Basis.repr_self]
  by_cases h : i = i₀
  · subst h
    simp
  · rw [if_neg h]
    simp [Finsupp.single_apply, h]

private theorem logFunctional_logBasis {b : Module.Basis (Fin n) K Ω[K⁄k]}
    (hb : ∀ i, b i = D k K (t i)) {i₀ : Fin n} (hi₀ : (i₀ : ℕ) < r) (ht : t i₀ ≠ 0) (i : Fin n) :
    logFunctional t b i₀ (logBasis t r i) = if i = i₀ then 1 else 0 := by
  unfold logBasis
  by_cases h₂ : i = i₀
  · subst h₂
    rw [if_pos hi₀, map_smul, logFunctional_D hb, if_pos rfl, if_pos rfl, smul_eq_mul,
      inv_mul_cancel₀ ht]
  · rw [if_neg h₂]
    split_ifs
    · rw [map_smul, logFunctional_D hb, if_neg h₂, smul_zero]
    · rw [logFunctional_D hb, if_neg h₂]

private theorem wedgeLeft_smul_left (s : K) (e : Ω[K⁄k]) (q : ℕ) (x : ⋀[K]^q (Ω[K⁄k])) :
    wedgeLeft (s • e) q x = s • wedgeLeft e q x := by
  refine Subtype.ext ?_
  rw [coe_wedgeLeft, Submodule.coe_smul, coe_wedgeLeft, map_smul, smul_mul_assoc]

private theorem wedgeLeft_zero_left (q : ℕ) (x : ⋀[K]^q (Ω[K⁄k])) :
    wedgeLeft (0 : Ω[K⁄k]) q x = 0 := by
  simpa using wedgeLeft_smul_left (0 : K) (0 : Ω[K⁄k]) q x

private theorem deRhamDifferential_ιMulti_zero (v : Fin 0 → Ω[K⁄k]) :
    deRhamDifferential (A := k) 0 (ιMulti K 0 v) = 0 := by
  have h := deRhamDifferential_smul_ιMulti_D (A := k) (B := K) 0 (fun _ => 1)
  rw [one_smul] at h
  rw [show v = (fun i : Fin 0 => D k K ((fun _ : Fin 1 => (1 : K)) i.succ)) from
    funext fun i => i.elim0, h]
  simp only [Derivation.map_one_eq_zero]
  exact (ιMulti K 1).map_coord_zero (0 : Fin 1) rfl

/-- **The Lie derivative along `tᵢ₀ ∂/∂tᵢ₀` kills the logarithmic monomials**, for `i₀ < r`. -/
private theorem lie_logBasis_ιMulti {b : Module.Basis (Fin n) K Ω[K⁄k]}
    (hb : ∀ i, b i = D k K (t i)) {i₀ : Fin n} (hi₀ : (i₀ : ℕ) < r) (ht : ∀ i, t i ≠ 0) :
    ∀ (q : ℕ) (w : Fin q → Fin n),
      Cartier.lie k (logFunctional t b i₀) q (ιMulti K q (logBasis t r ∘ w)) = 0 := by
  intro q
  induction q with
  | zero =>
    intro w
    rw [Cartier.lie_zero_apply, deRhamDifferential_ιMulti_zero, map_zero]
  | succ q ih =>
    intro w
    have hw : (logBasis t r ∘ w : Fin (q + 1) → Ω[K⁄k]) =
        Fin.cons (logBasis t r (w 0)) (logBasis t r ∘ Fin.tail w) := by
      ext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [Fin.tail]
    rw [hw, ← wedgeLeft_ιMulti]
    set x := ιMulti K q (logBasis (k := k) t r ∘ Fin.tail w)
    have hx : Cartier.lie k (logFunctional t b i₀) q x = 0 := ih _
    set i := w 0
    have hDφ : D k K (logFunctional t b i₀ (D k K (t i))) =
        if i = i₀ then D k K (t i) else 0 := by
      rw [logFunctional_D hb]
      split_ifs with h
      · rw [h]
      · exact Derivation.map_zero _
    unfold logBasis
    split_ifs with hr'
    · rw [wedgeLeft_smul_left, Cartier.lie_smul, Cartier.lie_wedgeLeft_D, hx, map_zero, add_zero,
        hDφ, Derivation.leibniz_inv, map_smul, logFunctional_D hb]
      split_ifs with h
      · rw [h, smul_eq_mul, neg_mul, pow_two, mul_assoc, inv_mul_cancel₀ (ht i₀), mul_one,
          neg_smul, neg_add_cancel]
      · rw [smul_zero, zero_smul, zero_add, wedgeLeft_zero_left, smul_zero]
    · have hne : i ≠ i₀ := fun h => hr' (h ▸ hi₀)
      rw [Cartier.lie_wedgeLeft_D, hx, map_zero, add_zero, hDφ, if_neg hne, wedgeLeft_zero_left]

omit [Field k] in
/-- The logarithmic derivative of a product of powers. -/
private theorem dlog_prod_pow {k : Type u} [Field k] [Algebra k K] {ι : Type*} (s : Finset ι)
    (T : ι → K) (hT : ∀ i ∈ s, T i ≠ 0) (b : ι → ℕ) :
    D k K (∏ i ∈ s, T i ^ b i) =
      (∏ i ∈ s, T i ^ b i) • ∑ i ∈ s, (b i : K) • (T i)⁻¹ • D k K (T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h0 : T a ≠ 0 := hT a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz,
      ih (fun i hi => hT i (Finset.mem_insert_of_mem hi)), Derivation.leibniz_pow, smul_add,
      add_comm]
    congr 1
    · rw [← Nat.cast_smul_eq_nsmul K, smul_smul, smul_smul, smul_smul, smul_smul]
      congr 1
      rcases Nat.eq_zero_or_pos (b a) with h | h
      · simp [h]
      · have e : T a ^ b a = T a * T a ^ (b a - 1) := by rw [← pow_succ', Nat.sub_add_cancel h]
        rw [e]; field_simp
    · rw [smul_smul]

/-- The logarithmic derivative of an `N`-th root. -/
private theorem dlog_of_pow_eq {N : ℕ} (hN : (N : K) ≠ 0) {g u : K} (hg : g ≠ 0)
    (h : g ^ N = u) : D k K g = g • ((N : K)⁻¹ • u⁻¹ • D k K u) := by
  subst h
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K]
  simp only [smul_smul]
  refine (one_smul K (D k K g)).symm.trans (congrArg (· • D k K g) ?_)
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · simp [h0] at hN
  · have e : g ^ N = g * g ^ (N - 1) := by rw [← pow_succ', Nat.sub_add_cancel h0]
    rw [e]; field_simp

/-- The logarithmic derivative of a product. -/
private theorem dlog_mul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b)⁻¹ • D k K (a * b) = a⁻¹ • D k K a + b⁻¹ • D k K b := by
  rw [Derivation.leibniz, smul_add, smul_smul, smul_smul, add_comm]
  congr 2 <;> field_simp

/-- **The connection form of an `N`-th root.** If `g^N = U V ∏ Tₖ^{bₖ}`, then
`dg = g (θ' + ξ)` with `θ' = N⁻¹ dU/U` and `ξ = N⁻¹ (dV/V + ∑ bₖ dTₖ/Tₖ)`. -/
private theorem D_eq_smul_of_pow_eq {N : ℕ} (hN : (N : K) ≠ 0) {r : ℕ} {g U V : K}
    {T : Fin r → K} (hg : g ≠ 0) (hU : U ≠ 0) (hV : V ≠ 0) (hT : ∀ i, T i ≠ 0) (b : Fin r → ℕ)
    (h : g ^ N = U * V * ∏ i, T i ^ b i) :
    D k K g = g • ((N : K)⁻¹ • U⁻¹ • D k K U +
      (N : K)⁻¹ • (V⁻¹ • D k K V + ∑ i, (b i : K) • (T i)⁻¹ • D k K (T i))) := by
  have hP : (∏ i, T i ^ b i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hT i)
  rw [dlog_of_pow_eq hN hg h, ← smul_add, dlog_mul (mul_ne_zero hU hV) hP, dlog_mul hU hV,
    dlog_prod_pow _ T (fun i _ => hT i) b, smul_smul (∏ i, T i ^ b i)⁻¹, inv_mul_cancel₀ hP,
    one_smul, add_assoc]

/-- `φ(∑ aᵢ βᵢ) = a_{i₀}` for the functional `tᵢ₀ ∂/∂tᵢ₀` and the logarithmic basis. -/
private theorem logFunctional_sum_logBasis {b : Module.Basis (Fin n) K Ω[K⁄k]}
    (hb : ∀ i, b i = D k K (t i)) {i₀ : Fin n} (hi₀ : (i₀ : ℕ) < r) (ht : t i₀ ≠ 0)
    (a : Fin n → K) : logFunctional t b i₀ (∑ i, a i • logBasis (k := k) t r i) = a i₀ := by
  rw [map_sum, Finset.sum_eq_single i₀]
  · rw [map_smul, logFunctional_logBasis hb hi₀ ht, if_pos rfl, smul_eq_mul, mul_one]
  · intro i _ hi
    rw [map_smul, logFunctional_logBasis hb hi₀ ht, if_neg hi, smul_zero]
  · intro h; exact absurd (Finset.mem_univ i₀) h

/-- **The residue conditions.** For the functional `φ = tᵢ₀ ∂/∂tᵢ₀`, `i₀ < r`, the logarithmic
basis `β`, coefficients `J` with `A J ⊆ J` and `∂/∂tᵢ₀ J ⊆ J`, and `J' = tᵢ₀ J`: `A J' ⊆ J'`,
`φ(βᵢ) ∈ A`, `φ(dc) ∈ J'` for `c ∈ J`, and `(φ(∑ aᵢ βᵢ) - λ) J ⊆ J'` when `a_{i₀} ≡ λ` modulo
`tᵢ₀ A`. -/
private theorem residue_conditions {b : Module.Basis (Fin n) K Ω[K⁄k]}
    (hb : ∀ i, b i = D k K (t i)) (ht : ∀ i, t i ≠ 0) {i₀ : Fin n} (hi₀ : (i₀ : ℕ) < r)
    (A : Subring K) (J : AddSubgroup K) (hJA : ∀ a ∈ A, ∀ c ∈ J, a * c ∈ J)
    (hJD : ∀ c ∈ J, b.coord i₀ (D k K c) ∈ J) (a : Fin n → K) (lam : k)
    (hres : ∃ e ∈ A, a i₀ - algebraMap k K lam = t i₀ * e) :
    (∀ x ∈ A, ∀ c ∈ J.map (AddMonoidHom.mulLeft (t i₀)),
        x * c ∈ J.map (AddMonoidHom.mulLeft (t i₀))) ∧
      (∀ i, logFunctional t b i₀ (logBasis (k := k) t r i) ∈ A) ∧
      (∀ c ∈ J, logFunctional t b i₀ (D k K c) ∈ J.map (AddMonoidHom.mulLeft (t i₀))) ∧
      ∀ c ∈ J, (logFunctional t b i₀ (∑ i, a i • logBasis (k := k) t r i) -
        algebraMap k K lam) * c ∈ J.map (AddMonoidHom.mulLeft (t i₀)) := by
  obtain ⟨e, heA, he⟩ := hres
  refine ⟨?_, fun i => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · rintro x hx _ ⟨c, hc, rfl⟩
    exact ⟨x * c, hJA x hx c hc, by simp only [AddMonoidHom.coe_mulLeft]; ring⟩
  · rw [logFunctional_logBasis hb hi₀ (ht i₀)]
    split_ifs
    · exact A.one_mem
    · exact A.zero_mem
  · refine ⟨b.coord i₀ (D k K c), hJD c hc, ?_⟩
    simp only [AddMonoidHom.coe_mulLeft, logFunctional, LinearMap.smul_apply, smul_eq_mul]
  · rw [logFunctional_sum_logBasis hb hi₀ (ht i₀), he, mul_assoc]
    exact ⟨e * c, hJA e heA c hc, rfl⟩

/-- **The residue homotopy on the logarithmic lattice.** Let `∇ = d + ξ ∧` with
`ξ = ∑ aᵢ βᵢ`, `aᵢ ∈ A`, for the logarithmic basis `β` of coordinates `tᵢ`, and let `φ` be the
functional `tᵢ₀ ∂/∂tᵢ₀`, `i₀ < r`. Suppose `A J ⊆ J`, that `∂/∂tᵢ₀` maps `J` into `J`, and that
`a_{i₀} ≡ λ` modulo `tᵢ₀ A` for a scalar `λ ≠ 0`. Put `J' = tᵢ₀ J`. If `η` has coefficients in `J`
and `∇ η` in `J'`, then `ι_φ η` has coefficients in `J` and `η - ∇(λ⁻¹ ι_φ η)` in `J'`. -/
private theorem logLattice_residue_homotopy {b : Module.Basis (Fin n) K Ω[K⁄k]}
    (hb : ∀ i, b i = D k K (t i)) (ht : ∀ i, t i ≠ 0) {i₀ : Fin n} (hi₀ : (i₀ : ℕ) < r)
    (A : Subring K) (hkA : ∀ c : k, algebraMap k K c ∈ A) (J : AddSubgroup K)
    (hJA : ∀ a ∈ A, ∀ c ∈ J, a * c ∈ J) (hJD : ∀ c ∈ J, b.coord i₀ (D k K c) ∈ J)
    (a : Fin n → K) (ha : ∀ i, a i ∈ A) (lam : k) (hlam : lam ≠ 0)
    (hres : ∃ e ∈ A, a i₀ - algebraMap k K lam = t i₀ * e) {p : ℕ}
    {η : ⋀[K]^(p + 1) (Ω[K⁄k])} (hη : η ∈ logLattice (logBasis (k := k) t r) J (p + 1))
    (hnab : deRhamDifferential (A := k) (p + 1) η +
      wedgeLeft (∑ i, a i • logBasis (k := k) t r i) (p + 1) η ∈
        logLattice (logBasis (k := k) t r) (J.map (AddMonoidHom.mulLeft (t i₀))) (p + 2)) :
    contraction (logFunctional t b i₀) p η ∈ logLattice (logBasis (k := k) t r) J p ∧
      η - (deRhamDifferential (A := k) p (lam⁻¹ • contraction (logFunctional t b i₀) p η) +
        wedgeLeft (∑ i, a i • logBasis (k := k) t r i) p
          (lam⁻¹ • contraction (logFunctional t b i₀) p η)) ∈
        logLattice (logBasis (k := k) t r) (J.map (AddMonoidHom.mulLeft (t i₀))) (p + 1) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := residue_conditions hb ht hi₀ A J hJA hJD a lam hres
  exact sub_nab_contraction_mem _ A hJA h₁ hkA h₂ (lie_logBasis_ιMulti hb hi₀ ht) h₃ a ha lam hlam
    h₄ hη hnab

/-- **The residue homotopy in degree zero.** Under the hypotheses of
`logLattice_residue_homotopy`, a function `η` with coefficients in `J` and `∇ η` with
coefficients in `tᵢ₀ J` has coefficients in `tᵢ₀ J`. -/
private theorem logLattice_residue_homotopy_zero {b : Module.Basis (Fin n) K Ω[K⁄k]}
    (hb : ∀ i, b i = D k K (t i)) (ht : ∀ i, t i ≠ 0) {i₀ : Fin n} (hi₀ : (i₀ : ℕ) < r)
    (A : Subring K) (hkA : ∀ c : k, algebraMap k K c ∈ A) (J : AddSubgroup K)
    (hJA : ∀ a ∈ A, ∀ c ∈ J, a * c ∈ J) (hJD : ∀ c ∈ J, b.coord i₀ (D k K c) ∈ J)
    (a : Fin n → K) (lam : k) (hlam : lam ≠ 0)
    (hres : ∃ e ∈ A, a i₀ - algebraMap k K lam = t i₀ * e)
    {η : ⋀[K]^0 (Ω[K⁄k])} (hη : η ∈ logLattice (logBasis (k := k) t r) J 0)
    (hnab : deRhamDifferential (A := k) 0 η +
      wedgeLeft (∑ i, a i • logBasis (k := k) t r i) 0 η ∈
        logLattice (logBasis (k := k) t r) (J.map (AddMonoidHom.mulLeft (t i₀))) 1) :
    η ∈ logLattice (logBasis (k := k) t r) (J.map (AddMonoidHom.mulLeft (t i₀))) 0 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := residue_conditions hb ht hi₀ A J hJA hJD a lam hres
  exact mem_logLattice_of_nab_mem_zero _ A h₁ hkA h₂ (lie_logBasis_ιMulti hb hi₀ ht) h₃ a lam hlam
    h₄ hη hnab

omit [Field K] [Algebra k K] in
private theorem sum_fin_castLE {M : Type*} [AddCommMonoid M] {r n : ℕ} (hr : r ≤ n)
    (f : Fin r → M) :
    ∑ k : Fin r, f k = ∑ i : Fin n, (if h : (i : ℕ) < r then f ⟨i, h⟩ else 0) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb hr)))]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Fin.castLEEmb]
  · intro i _ hi
    rw [dif_neg]
    intro h
    exact hi (Finset.mem_map.mpr ⟨⟨i, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)

private theorem smul_logBasis_of_lt {i : Fin n} (hi : (i : ℕ) < r) (ht : t i ≠ 0) :
    t i • logBasis (k := k) t r i = D k K (t i) := by
  unfold logBasis
  rw [if_pos hi, smul_smul, mul_inv_cancel₀ ht, one_smul]

/-- **The coefficients of the connection form.** In the logarithmic basis, the form
`N⁻¹ (dV/V + ∑ₖ bₖ dtₖ/tₖ)` (`V` a unit of `A`) has coefficients in `A`, and its coefficient
at `βᵢ₀`, `i₀ < r`, is `bᵢ₀ / N` modulo `tᵢ₀ A`. -/
private theorem exists_coeffs_dlog {b : Module.Basis (Fin n) K Ω[K⁄k]}
    (hb : ∀ i, b i = D k K (t i)) (ht : ∀ i, t i ≠ 0) (hr : r ≤ n) (A : Subring K)
    (hTA : ∀ i, t i ∈ A) (hreg : ∀ x ∈ A, ∀ i, b.repr (D k K x) i ∈ A) {N : ℕ}
    (hNA : (N : K)⁻¹ ∈ A) {V : K} (hVA : V ∈ A) (hViA : V⁻¹ ∈ A) (bb : Fin r → ℕ) :
    ∃ a : Fin n → K, (∀ i, a i ∈ A) ∧
      (N : K)⁻¹ • (V⁻¹ • D k K V + ∑ q : Fin r, (bb q : K) • (t (Fin.castLE hr q))⁻¹ •
        D k K (t (Fin.castLE hr q))) = ∑ i, a i • logBasis (k := k) t r i ∧
      ∀ (i₀ : Fin n) (hi₀ : (i₀ : ℕ) < r),
        ∃ e ∈ A, a i₀ - (N : K)⁻¹ * (bb ⟨i₀, hi₀⟩ : K) = t i₀ * e := by
  set c : Fin n → K := fun i => b.repr (D k K V) i
  refine ⟨fun i => (N : K)⁻¹ * (V⁻¹ * c i * (if (i : ℕ) < r then t i else 1) +
    if h : (i : ℕ) < r then (bb ⟨i, h⟩ : K) else 0), fun i => ?_, ?_, fun i₀ hi₀ => ?_⟩
  · refine A.mul_mem hNA (A.add_mem (A.mul_mem (A.mul_mem hViA (hreg V hVA i)) ?_) ?_)
    · split_ifs
      · exact hTA i
      · exact A.one_mem
    · split_ifs
      · exact natCast_mem A _
      · exact A.zero_mem
  · have hDV : D k K V = ∑ i, (c i * if (i : ℕ) < r then t i else 1) • logBasis (k := k) t r i := by
      conv_lhs => rw [← b.sum_repr (D k K V)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb i, mul_smul]
      congr 1
      split_ifs with h
      · exact (smul_logBasis_of_lt h (ht i)).symm
      · unfold logBasis
        rw [if_neg h, one_smul]
    have hsum : ∑ q : Fin r, (bb q : K) • (t (Fin.castLE hr q))⁻¹ • D k K (t (Fin.castLE hr q)) =
        ∑ i : Fin n, (if h : (i : ℕ) < r then (bb ⟨i, h⟩ : K) else 0) • logBasis (k := k) t r i := by
      rw [sum_fin_castLE hr]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · unfold logBasis
        rw [if_pos h]
        rfl
      · rw [zero_smul]
    rw [hDV, hsum, Finset.smul_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← add_smul, smul_smul]
    congr 1
    ring
  · refine ⟨(N : K)⁻¹ * V⁻¹ * c i₀, A.mul_mem (A.mul_mem hNA hViA) (hreg V hVA i₀), ?_⟩
    simp only [if_pos hi₀, dif_pos hi₀]
    ring

/-- The `i₀`-th coordinate of `d (∏_{i ∈ P} tᵢ)` vanishes when `i₀ ∉ P`. -/
private theorem coord_D_prod {b : Module.Basis (Fin n) K Ω[K⁄k]} (hb : ∀ i, b i = D k K (t i))
    (ht : ∀ i, t i ≠ 0) (P : Finset (Fin n)) {i₀ : Fin n} (hi₀ : i₀ ∉ P) :
    b.coord i₀ (D k K (∏ i ∈ P, t i)) = 0 := by
  have h := dlog_prod_pow (k := k) P t (fun i _ => ht i) (fun _ => 1)
  simp only [pow_one, Nat.cast_one, one_smul] at h
  rw [h, map_smul, map_sum, Finset.sum_eq_zero, smul_zero]
  intro i hi
  rw [map_smul, ← hb, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, if_neg (fun h' : i = i₀ => hi₀ (h' ▸ hi)), smul_zero]

/-- `∂/∂tᵢ₀` maps the multiples `(∏_{i ∈ P} tᵢ) A` into themselves when `i₀ ∉ P`. -/
private theorem coord_D_mem_of_eq_prod_mul {b : Module.Basis (Fin n) K Ω[K⁄k]}
    (hb : ∀ i, b i = D k K (t i)) (ht : ∀ i, t i ≠ 0) (A : Subring K)
    (hreg : ∀ x ∈ A, ∀ i, b.repr (D k K x) i ∈ A) (P : Finset (Fin n)) {i₀ : Fin n}
    (hi₀ : i₀ ∉ P) (J : AddSubgroup K) (hJ : ∀ c ∈ J, ∃ a ∈ A, c = (∏ i ∈ P, t i) * a)
    (hJ' : ∀ a ∈ A, (∏ i ∈ P, t i) * a ∈ J) : ∀ c ∈ J, b.coord i₀ (D k K c) ∈ J := by
  intro c hc
  obtain ⟨a, ha, rfl⟩ := hJ c hc
  rw [Derivation.leibniz, map_add, map_smul, map_smul, coord_D_prod hb ht P hi₀, smul_zero,
    add_zero, smul_eq_mul]
  exact hJ' _ (hreg a ha i₀)

/-- The homotopy conditions on `∇ = d + ξ ∧` for coefficient groups `J' ⊆ J` (as in the local
data of the residue homotopy): in positive degree an `η` with coefficients in `J` and `∇ η` in
`J'` agrees with some `∇ ι`, `ι` with coefficients in `J`, modulo `J'`; in degree zero such an
`η` has coefficients in `J'`. -/
private def HomotopyConds (β : Fin n → Ω[K⁄k]) (J J' : AddSubgroup K) (ξ : Ω[K⁄k]) : Prop :=
  (∀ (p : ℕ) (y), y ∈ logLattice β J (p + 1) →
      deRhamDifferential (A := k) (p + 1) y + wedgeLeft ξ (p + 1) y ∈ logLattice β J' (p + 2) →
      ∃ ι ∈ logLattice β J p,
        y - (deRhamDifferential (A := k) p ι + wedgeLeft ξ p ι) ∈ logLattice β J' (p + 1)) ∧
    ∀ (y), y ∈ logLattice β J 0 →
      deRhamDifferential (A := k) 0 y + wedgeLeft ξ 0 y ∈ logLattice β J' 1 →
      y ∈ logLattice β J' 0

/-- The homotopy conditions hold trivially for `J' = 1 · J = J`. -/
private theorem homotopyConds_of_eq_one (β : Fin n → Ω[K⁄k]) (J : AddSubgroup K) (ξ : Ω[K⁄k])
    {c : K} (hc : c = 1) : HomotopyConds β J (J.map (AddMonoidHom.mulLeft c)) ξ := by
  subst hc
  rw [map_mulLeft_one]
  refine ⟨fun p y hy _ => ⟨0, zero_mem _, ?_⟩, fun y hy _ => hy⟩
  rw [map_zero, map_zero, add_zero, sub_zero]
  exact hy

/-- **The residue homotopy on a chart.** With `J = (∏_{i ∈ P} tᵢ) A`, `i₀ ∉ P`, `i₀ < r`, and
`a_{i₀} ≡ λ ≠ 0` modulo `tᵢ₀ A`, the connection `∇ = d + (∑ aᵢ βᵢ) ∧` satisfies the homotopy
conditions for `J' = tᵢ₀ J`. -/
private theorem residue_homotopy_of_chart {b : Module.Basis (Fin n) K Ω[K⁄k]}
    (hb : ∀ i, b i = D k K (t i)) (ht : ∀ i, t i ≠ 0) {i₀ : Fin n} (hi₀ : (i₀ : ℕ) < r)
    (A : Subring K) (hkA : ∀ c : k, algebraMap k K c ∈ A)
    (hreg : ∀ x ∈ A, ∀ i, b.repr (D k K x) i ∈ A) (P : Finset (Fin n)) (hi₀P : i₀ ∉ P)
    (J : AddSubgroup K) (hJA : ∀ a ∈ A, ∀ c ∈ J, a * c ∈ J)
    (hJ : ∀ c ∈ J, ∃ a ∈ A, c = (∏ i ∈ P, t i) * a) (hJ' : ∀ a ∈ A, (∏ i ∈ P, t i) * a ∈ J)
    (a : Fin n → K) (ha : ∀ i, a i ∈ A) (lam : k) (hlam : lam ≠ 0)
    (hres : ∃ e ∈ A, a i₀ - algebraMap k K lam = t i₀ * e) {ξ : Ω[K⁄k]}
    (hξ : ξ = ∑ i, a i • logBasis (k := k) t r i) {c : K} (hc : c = t i₀) :
    HomotopyConds (logBasis (k := k) t r) J (J.map (AddMonoidHom.mulLeft c)) ξ := by
  subst hξ hc
  have hJD := coord_D_mem_of_eq_prod_mul hb ht A hreg P hi₀P J hJ hJ'
  refine ⟨fun p y hy hnab => ?_, fun y hy hnab =>
    logLattice_residue_homotopy_zero hb ht hi₀ A hkA J hJA hJD a lam hlam hres hy hnab⟩
  obtain ⟨h1, h2⟩ := logLattice_residue_homotopy hb ht hi₀ A hkA J hJA hJD a ha lam hlam hres
    hy hnab
  refine ⟨lam⁻¹ • contraction (logFunctional t b i₀) p y, ?_, h2⟩
  rw [← algebraMap_smul K lam⁻¹]
  exact smul_mem_logLattice (fun c hc => hJA _ (hkA _) c hc) h1

end LogBasis

section LocalQuasiIso

open HomologicalComplex TopologicalSpace

variable {Z : TopCat.{0}} {R : Sheaf (Opens.grothendieckTopology Z) RingCat.{0}}

private theorem sheafOfModules_eq_of_locally_eq {M : SheafOfModules.{0} R} {W : Opens Z}
    (s t : ToType (M.val.obj (op W)))
    (h : ∀ x ∈ W, ∃ (W' : Opens Z) (hW' : W' ≤ W), x ∈ W' ∧
      M.val.map (homOfLE hW').op s = M.val.map (homOfLE hW').op t) : s = t := by
  choose W' hW' hx hst using h
  exact TopCat.Sheaf.eq_of_locally_eq'
    (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{0} Z)
    (fun x : W ↦ W' x.1 x.2) W (fun x ↦ homOfLE (hW' x.1 x.2))
    (fun x hxW ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxW⟩, hx x hxW⟩) s t
    fun x ↦ hst x.1 x.2

private theorem sheafOfModules_app_injective_of_mono {M N : SheafOfModules.{0} R} (φ : M ⟶ N)
    [Mono φ] (W : Opens Z) : Function.Injective (φ.val.app (op W)) := by
  have h₁ : Mono ((SheafOfModules.toSheaf R).map φ) := inferInstance
  have h₂ : Mono ((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf R).map φ)) := inferInstance
  have h₃ : Mono (((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf R).map φ)).app (op W)) :=
    inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).1 h₃

private theorem sheafOfModules_exists_app_eq_of_epi {M N : SheafOfModules.{0} R} (φ : M ⟶ N)
    [Epi φ] {W : Opens Z} (s : ToType (N.val.obj (op W))) {x : Z} (hx : x ∈ W) :
    ∃ (W' : Opens Z) (h : W' ≤ W), x ∈ W' ∧ ∃ t : ToType (M.val.obj (op W')),
      φ.val.app (op W') t = N.val.map (homOfLE h).op s := by
  obtain ⟨T, hT, hTs⟩ :=
    @Stacks.SheafOfModules.EpiMono.exists_covering_of_epi _ _ _ _ _ _ M N φ ‹_› W s
  obtain ⟨W', g, hg, hxW'⟩ := (Opens.mem_grothendieckTopology _).1 hT x hx
  obtain ⟨t, ht⟩ := hTs g hg
  exact ⟨W', leOfHom g, hxW', t, ht⟩

variable {X Y : CochainComplex (SheafOfModules.{0} R) ℕ}

/-- **A morphism of complexes of sheaves of modules induces an isomorphism on `ℋ^q`** when every
cycle of the target is, near every point, the image of a cycle up to a boundary, and every
cycle of the source whose image is a boundary is, near every point, a boundary. -/
private theorem isIso_homologyMap_of_local (φ : X ⟶ Y) (q : ℕ)
    (ha : ∀ (W : Opens Z) (z : ToType ((Y.X q).val.obj (op W))),
      (Y.d q (q + 1)).val.app (op W) z = 0 → ∀ x ∈ W,
      ∃ (W' : Opens Z) (h : W' ≤ W), x ∈ W' ∧ ∃ (w : ToType ((X.X q).val.obj (op W')))
        (y : ToType ((Y.X ((ComplexShape.up ℕ).prev q)).val.obj (op W'))),
          (X.d q (q + 1)).val.app (op W') w = 0 ∧
          (Y.X q).val.map (homOfLE h).op z = (φ.f q).val.app (op W') w +
            (Y.d _ q).val.app (op W') y)
    (hb : ∀ (W : Opens Z) (w : ToType ((X.X q).val.obj (op W)))
      (y : ToType ((Y.X ((ComplexShape.up ℕ).prev q)).val.obj (op W))),
      (X.d q (q + 1)).val.app (op W) w = 0 → (φ.f q).val.app (op W) w =
        (Y.d _ q).val.app (op W) y → ∀ x ∈ W,
      ∃ (W' : Opens Z) (h : W' ≤ W), x ∈ W' ∧
        ∃ v : ToType ((X.X ((ComplexShape.up ℕ).prev q)).val.obj (op W')),
          (X.X q).val.map (homOfLE h).op w = (X.d _ q).val.app (op W') v) :
    IsIso (homologyMap φ q) := by
  have hiY : ∀ W : Opens Z, Function.Injective ((Y.iCycles q).val.app (op W)) := fun W =>
    sheafOfModules_app_injective_of_mono _ W
  have hiX : ∀ W : Opens Z, Function.Injective ((X.iCycles q).val.app (op W)) := fun W =>
    sheafOfModules_app_injective_of_mono _ W
  have hcyc : ∀ (W : Opens Z) (w : ToType ((X.cycles q).val.obj (op W))),
      (X.d q (q + 1)).val.app (op W) ((X.iCycles q).val.app (op W) w) = 0 := fun W w => by
    change (X.iCycles q ≫ X.d q (q + 1)).val.app (op W) w = 0
    rw [X.iCycles_d]
    rfl
  have nat : ∀ {M N : SheafOfModules.{0} R} (ψ : M ⟶ N) {W W' : Opens Z} (h : W' ≤ W)
      (s : ToType (M.val.obj (op W))),
      ψ.val.app (op W') (M.val.map (homOfLE h).op s) = N.val.map (homOfLE h).op
        (ψ.val.app (op W) s) := fun ψ _ _ h s => PresheafOfModules.naturality_apply ψ.val _ s
  refine MMP.DeRham.IsLocalCohomologyRep.isIso (C := Y) (q := q) (c := homologyMap φ q)
    (Rep := fun W s z => ∃ w : ToType ((X.cycles q).val.obj (op W)),
      (X.homologyπ q).val.app (op W) w = s ∧
      z = (φ.f q).val.app (op W) ((X.iCycles q).val.app (op W) w)) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro W W' h s z ⟨w, rfl, rfl⟩
    refine ⟨(X.cycles q).val.map (homOfLE h).op w, nat _ h w, ?_⟩
    exact ((congrArg ((φ.f q).val.app (op W')) (nat (X.iCycles q) h w)).trans
      (nat (φ.f q) h _)).symm
  · rintro W s z ⟨w, rfl, rfl⟩
    have h1 : (Y.d q (q + 1)).val.app (op W) ((φ.f q).val.app (op W) ((X.iCycles q).val.app (op W) w)) =
        (φ.f (q + 1)).val.app (op W) ((X.d q (q + 1)).val.app (op W) ((X.iCycles q).val.app (op W) w)) := by
      change (φ.f q ≫ Y.d q (q + 1)).val.app (op W) _ = (X.d q (q + 1) ≫ φ.f (q + 1)).val.app (op W) _
      rw [φ.comm]
    exact h1.trans (by rw [hcyc]; exact map_zero _)
  · rintro W s z ⟨w, rfl, hz⟩
    have hc : (cyclesMap φ q).val.app (op W) w = z := hiY W (by
      change (cyclesMap φ q ≫ Y.iCycles q).val.app (op W) w = (Y.iCycles q).val.app (op W) z
      rw [cyclesMap_i]
      exact hz.symm)
    change (X.homologyπ q ≫ homologyMap φ q).val.app (op W) w = (Y.homologyπ q).val.app (op W) z
    rw [homologyπ_naturality]
    change (Y.homologyπ q).val.app (op W) ((cyclesMap φ q).val.app (op W) w) = _
    rw [hc]
  · intro W s x hx
    obtain ⟨W', h, hx', w, hw⟩ := sheafOfModules_exists_app_eq_of_epi (X.homologyπ q) s hx
    exact ⟨W', h, hx', _, w, hw, rfl⟩
  · rintro W s z y ⟨w, rfl, rfl⟩ hy
    refine sheafOfModules_eq_of_locally_eq _ _ fun x hx => ?_
    obtain ⟨W', h, hx', v, hv⟩ := hb W _ y (hcyc W w) hy.symm x hx
    refine ⟨W', h, hx', ?_⟩
    have hv' : (X.cycles q).val.map (homOfLE h).op w = (X.toCycles _ q).val.app (op W') v :=
      hiX W' (by
        rw [nat, hv]
        change _ = (X.toCycles _ q ≫ X.iCycles q).val.app (op W') v
        rw [X.toCycles_i])
    rw [← nat, hv']
    change (X.toCycles _ q ≫ X.homologyπ q).val.app (op W') v = _
    rw [X.toCycles_comp_homologyπ]
    exact (map_zero _).symm
  · intro W z hz x hx
    obtain ⟨W', h, hx', w, y, hw, hzw⟩ := ha W z hz x hx
    obtain ⟨w', rfl⟩ := MMP.DeRham.exists_iCycles_app_eq X q W' w hw
    exact ⟨W', h, hx', _, y, _, ⟨w', rfl, rfl⟩, hzw⟩

end LocalQuasiIso

section RationalGlue

open MMP.FourfoldProofs.FractionalLogComplexProof KaehlerDifferential exteriorPower

variable {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] {sY : Y ⟶ Spec (.of k)}

/-- The rational form of a homogeneous form of degree `p`, restricted to a non-empty affine open,
is in degree `p`. -/
private theorem ratTotal_totalRestrict_incl_eq {Q : Y.Opens} (O : Y.affineOpens)
    [Nonempty (O : Y.Opens)] (hO : (O : Y.Opens) ≤ Q) (p : ℕ)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra sY).piece (p : ℤ)).val.obj (op Q)) :
    ratTotal sY O ((TB sY).totalRestrict (homOfLE hO).op ((TB sY).incl (p : ℤ) ω)) =
      (ratForm sY p O (Stacks.sectionRestrict ((Scheme.Hom.relativeDifferentialFormsAlgebra
        sY).piece (p : ℤ)).val (homOfLE hO).op ω) : _) := by
  rw [Stacks.GradedAlgebra.totalRestrict_incl]
  exact ratTotal_incl sY O p _

/-- `ratTotal` of `d x` is `d` of the rational form of `x`. -/
private theorem ratTotal_incl_d (O : Y.affineOpens) [Nonempty (O : Y.Opens)] (p : ℕ)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra sY).piece (p : ℤ)).val.obj
      (op (O : Y.Opens))) :
    letI := MMP.Mori.functionFieldAlgebra sY
    ratTotal sY O ((TB sY).incl ((p + 1 : ℕ) : ℤ)
        (((Scheme.Hom.deRhamComplex sY).d p (p + 1)).val.app (op (O : Y.Opens)) x)) =
      (deRhamDifferential (A := k) p (ratForm sY p O x) : _) :=
  (ratTotal_incl sY O (p + 1) _).trans (congrArg Subtype.val (ratForm_d sY p O x))

/-- **The rational form of `∇(g η)`.** Let `ω` be a `p`-form on `Q` with rational form `g η`
on `O ≤ Q`, and `θ` a `1`-form on `Q` with rational form `θ'`. If `dg = g (θ' + ξ)`, then the
rational form of `∇ω = dω - θ ∧ ω` is `g (dη + ξ ∧ η)`. -/
private theorem ratTotal_nab {Q : Y.Opens} (O : Y.affineOpens) [Nonempty (O : Y.Opens)]
    (hO : (O : Y.Opens) ≤ Q) (p : ℕ)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra sY).piece 1).val.obj (op Q))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra sY).piece (p : ℤ)).val.obj (op Q)) :
    letI := MMP.Mori.functionFieldAlgebra sY
    ∀ (θ' ξ : Ω[Y.functionField⁄k]) (g : Y.functionField)
      (η : ⋀[Y.functionField]^p (Ω[Y.functionField⁄k])),
      ratTotal sY O ((TB sY).totalRestrict (homOfLE hO).op ((TB sY).incl 1 θ)) =
        ExteriorAlgebra.ι Y.functionField θ' →
      ratTotal sY O ((TB sY).totalRestrict (homOfLE hO).op ((TB sY).incl (p : ℤ) ω)) =
        algebraMap _ _ g * (η : ExteriorAlgebra _ _) →
      D k Y.functionField g = g • (θ' + ξ) →
      ratTotal sY O ((TB sY).totalRestrict (homOfLE hO).op
          ((TB sY).incl ((p + 1 : ℕ) : ℤ) (nab sY p θ ω))) =
        algebraMap _ _ g * (deRhamDifferential (A := k) p η + wedgeLeft ξ p η :
          ExteriorAlgebra _ _) := by
  let := MMP.Mori.functionFieldAlgebra sY
  intro θ' ξ g η hθ hω hg
  set P := fun i : ℤ => ((Scheme.Hom.relativeDifferentialFormsAlgebra sY).piece i).val
  set x := Stacks.sectionRestrict (P (p : ℤ)) (homOfLE hO).op ω
  have hx : ratForm sY p O x = g • η := by
    refine Subtype.ext ?_
    rw [← ratTotal_totalRestrict_incl_eq, hω, Submodule.coe_smul_of_tower, Algebra.smul_def]
  -- the `d` part
  have hd : ratTotal sY O ((TB sY).totalRestrict (homOfLE hO).op (Δ sY Q p ((TB sY).incl (p : ℤ) ω)))
      = (deRhamDifferential (A := k) p (g • η) : ExteriorAlgebra _ _) := by
    have hres : (TB sY).totalRestrict (homOfLE hO).op ((TB sY).incl ((p + 1 : ℕ) : ℤ)
        (((Scheme.Hom.deRhamComplex sY).d p (p + 1)).val.app (op Q) ω)) =
        (TB sY).incl ((p + 1 : ℕ) : ℤ)
          (((Scheme.Hom.deRhamComplex sY).d p (p + 1)).val.app (op (O : Y.Opens)) x) := by
      refine ((TB sY).totalRestrict_incl _ _ _).trans (congrArg ((TB sY).incl _) ?_)
      exact (deRham_map (homOfLE hO).op p ω).symm
    rw [Δ_incl, hres, ratTotal_incl_d, hx]
  -- the wedge part
  have hw : ratTotal sY O ((TB sY).totalRestrict (homOfLE hO).op
      ((TB sY).incl 1 θ * (TB sY).incl (p : ℤ) ω)) =
      ExteriorAlgebra.ι Y.functionField θ' * (algebraMap _ _ g * (η : ExteriorAlgebra _ _)) := by
    rw [← hθ, ← hω, ← (TB sY).totalRestrictRingHom_apply, map_mul,
      (TB sY).totalRestrictRingHom_apply, (TB sY).totalRestrictRingHom_apply]
    refine ratTotal_mul sY O ?_ ?_
    · rw [Stacks.GradedAlgebra.totalRestrict_incl]
      exact incl_mem_nonnegForms sY _ 1 _
    · rw [Stacks.GradedAlgebra.totalRestrict_incl]
      exact incl_mem_nonnegForms sY _ p _
  rw [incl_nab, map_sub, map_sub, hd, hw, deRhamDifferential_smul, hg]
  simp only [Submodule.coe_add, coe_wedgeLeft, Submodule.coe_smul_of_tower, map_smul, map_add,
    Algebra.smul_def]
  rw [← mul_assoc (ExteriorAlgebra.ι _ θ'), ← Algebra.commutes g (ExteriorAlgebra.ι _ θ')]
  noncomm_ring

end RationalGlue

section FunctionFieldBasis

open MMP.FourfoldProofs.FractionalLogComplexProof KaehlerDifferential

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of k))
  (U : X.Opens) [Nonempty U]

/-- The germ in the function field of a non-empty open `U` of a section of `X` over `W`. -/
private noncomputable def gmU (W : X.Opens) [Nonempty (U.ι ⁻¹ᵁ W)] :
    Γ(X, W) →+* U.toScheme.functionField :=
  (U.toScheme.germToFunctionField (U.ι ⁻¹ᵁ W)).hom.comp (U.ι.app W).hom

private theorem openFunctionFieldEquiv_gmU (W : X.Opens) [Nonempty W] [Nonempty (U.ι ⁻¹ᵁ W)]
    (a : Γ(X, W)) : openFunctionFieldEquiv U (gmU U W a) = X.germToFunctionField W a :=
  openFunctionFieldEquiv_germ U W a

private theorem gmU_restrict {W W' : X.Opens} (h : W' ≤ W) [Nonempty (U.ι ⁻¹ᵁ W)]
    [Nonempty (U.ι ⁻¹ᵁ W')] (a : Γ(X, W)) :
    gmU U W' (X.presheaf.map (homOfLE h).op a) = gmU U W a := by
  have : Nonempty W := ⟨⟨U.ι (Classical.arbitrary (U.ι ⁻¹ᵁ W)).1,
    (Classical.arbitrary (U.ι ⁻¹ᵁ W)).2⟩⟩
  have : Nonempty W' := ⟨⟨U.ι (Classical.arbitrary (U.ι ⁻¹ᵁ W')).1,
    (Classical.arbitrary (U.ι ⁻¹ᵁ W')).2⟩⟩
  refine (openFunctionFieldEquiv U).injective ?_
  rw [openFunctionFieldEquiv_gmU, openFunctionFieldEquiv_gmU]
  change (X.presheaf.map (homOfLE h).op ≫ X.germToFunctionField W').hom a = _
  rw [Scheme.germToFunctionField, Scheme.germToFunctionField, TopCat.Presheaf.germ_res]

/-- **The function field of `U` is a fraction field of the sections over any affine open.** -/
private theorem isFractionRing_gmU {W : X.Opens} (hW : IsAffineOpen W) [Nonempty W]
    [Nonempty (U.ι ⁻¹ᵁ W)] :
    letI := (gmU U W).toAlgebra
    IsFractionRing Γ(X, W) U.toScheme.functionField := by
  let := (gmU U W).toAlgebra
  have := functionField_isFractionRing_of_isAffineOpen X W hW
  let e : X.functionField ≃ₐ[Γ(X, W)] U.toScheme.functionField :=
    { (openFunctionFieldEquiv U).symm with
      commutes' := fun a => by
        refine (RingEquiv.symm_apply_eq _).2 ?_
        exact (openFunctionFieldEquiv_gmU U W a).symm }
  exact IsLocalization.isLocalization_of_algEquiv _ e

private theorem isScalarTower_gmU (W : X.Opens) [Nonempty W] [Nonempty (U.ι ⁻¹ᵁ W)] :
    letI := MMP.Mori.sectionAlgebra f W
    letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ f)
    letI := (gmU U W).toAlgebra
    IsScalarTower k Γ(X, W) U.toScheme.functionField := by
  let := MMP.Mori.sectionAlgebra f W
  let := MMP.Mori.functionFieldAlgebra f
  let := MMP.Mori.functionFieldAlgebra (U.ι ≫ f)
  let := (gmU U W).toAlgebra
  have := MMP.Mori.isScalarTower_section_functionField f W
  refine IsScalarTower.of_algebraMap_eq fun c => (openFunctionFieldEquiv U).injective ?_
  rw [openFunctionFieldEquiv_algebraMap U f]
  change _ = openFunctionFieldEquiv U (gmU U W (algebraMap k Γ(X, W) c))
  rw [openFunctionFieldEquiv_gmU]
  exact IsScalarTower.algebraMap_apply k Γ(X, W) X.functionField c

/-- **A basis of `Ω` over an affine open gives a basis of `Ω` of the function field**, whose
coordinates on differentials of sections are the germs of their coordinates. -/
private theorem exists_basis_functionField {n : ℕ} {W : X.Opens} (hW : IsAffineOpen W)
    [Nonempty W] [Nonempty (U.ι ⁻¹ᵁ W)] (t : Fin n → Γ(X, W))
    (b : letI := MMP.Mori.sectionAlgebra f W
      Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄k])
    (hb : letI := MMP.Mori.sectionAlgebra f W
      ∀ i, b i = D k Γ(X, W) (t i)) :
    letI := MMP.Mori.sectionAlgebra f W
    letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ f)
    ∃ bK : Module.Basis (Fin n) U.toScheme.functionField Ω[U.toScheme.functionField⁄k],
      (∀ i, bK i = D k _ (gmU U W (t i))) ∧
      ∀ (a : Γ(X, W)) i, bK.repr (D k _ (gmU U W a)) i = gmU U W (b.repr (D k _ a) i) := by
  let := MMP.Mori.sectionAlgebra f W
  let := MMP.Mori.functionFieldAlgebra (U.ι ≫ f)
  let := (gmU U W).toAlgebra
  have := isFractionRing_gmU U hW
  have := isScalarTower_gmU f U W
  refine ⟨b.ofIsLocalizedModule U.toScheme.functionField (nonZeroDivisors Γ(X, W))
    (KaehlerDifferential.map k k Γ(X, W) U.toScheme.functionField), fun i => ?_, fun a i => ?_⟩
  · rw [Module.Basis.ofIsLocalizedModule_apply, hb, KaehlerDifferential.map_D]
    rfl
  · have h := Module.Basis.ofIsLocalizedModule_repr_apply U.toScheme.functionField
      (nonZeroDivisors Γ(X, W)) (KaehlerDifferential.map k k Γ(X, W) U.toScheme.functionField) b
      (D k Γ(X, W) a) i
    rw [KaehlerDifferential.map_D] at h
    exact h

/-- The basis of `Ω[Γ(X, W)⁄k]` of a chart, over the field `k` rather than `Γ(Spec k, V)`. -/
private theorem exists_basis_of_chart {n : ℕ} {W : X.Opens} {V : (Spec (.of k)).Opens}
    (hV : V = ⊤) (e : W ≤ f ⁻¹ᵁ V) (t : Fin n → Γ(X, W))
    (hb : letI := (f.appLE V W e).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄Γ(Spec (.of k), V)],
        ∀ i, b i = D Γ(Spec (.of k), V) Γ(X, W) (t i)) :
    letI := MMP.Mori.sectionAlgebra f W
    ∃ b : Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄k], ∀ i, b i = D k Γ(X, W) (t i) := by
  subst hV
  let := MMP.Mori.sectionAlgebra f W
  let := (f.appLE ⊤ W e).hom.toAlgebra
  obtain ⟨b, hb⟩ := hb
  let e : Ω[Γ(X, W)⁄Γ(Spec (.of k), ⊤)] ≃ₗ[Γ(X, W)] Ω[Γ(X, W)⁄k] :=
    MMP.DeRham.kaehlerSpecEquiv f W
  refine ⟨b.map e, fun i => ?_⟩
  rw [Module.Basis.map_apply, hb]
  exact MMP.DeRham.kaehlerBaseEquiv_d _ _ _ (t i)

/-- **A basis of `Ω` over an affine open restricts to a basis over a basic open.** -/
private theorem exists_basis_basicOpen {n : ℕ} {W : X.Opens} (hW : IsAffineOpen W)
    (t : Fin n → Γ(X, W))
    (b : letI := MMP.Mori.sectionAlgebra f W
      Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄k])
    (hb : letI := MMP.Mori.sectionAlgebra f W
      ∀ i, b i = D k Γ(X, W) (t i)) (g : Γ(X, W)) :
    letI := MMP.Mori.sectionAlgebra f W
    letI := MMP.Mori.sectionAlgebra f (X.basicOpen g)
    ∃ b' : Module.Basis (Fin n) Γ(X, X.basicOpen g) Ω[Γ(X, X.basicOpen g)⁄k],
      ∀ i, b' i = D k _ (X.presheaf.map (homOfLE (X.basicOpen_le g)).op (t i)) := by
  let := MMP.Mori.sectionAlgebra f W
  let := MMP.Mori.sectionAlgebra f (X.basicOpen g)
  let : Algebra Γ(X, W) Γ(X, X.basicOpen g) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res f (X.basicOpen_le g)
  have : IsLocalization.Away g Γ(X, X.basicOpen g) := hW.isLocalization_basicOpen g
  refine ⟨b.ofIsLocalizedModule Γ(X, X.basicOpen g) (Submonoid.powers g)
    (KaehlerDifferential.map k k Γ(X, W) Γ(X, X.basicOpen g)), fun i => ?_⟩
  rw [Module.Basis.ofIsLocalizedModule_apply, hb, KaehlerDifferential.map_D]
  rfl

end FunctionFieldBasis

section ChartLattice

open MMP.FourfoldProofs.FractionalLogComplexProof KaehlerDifferential exteriorPower

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (n : ℕ) (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f) [Nonempty (cU D)]

/-- The germ in the function field of `U = X ∖ D`, at a non-empty affine open `O ⊆ U ∩ W'`, of a
function on `W'`. -/
private noncomputable def gmO {W' : X.Opens} (O : (cU D).toScheme.affineOpens)
    [Nonempty (O : (cU D).toScheme.Opens)] (hO : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ W') :
    Γ(X, W') →+* (cU D).toScheme.functionField :=
  ((cU D).toScheme.germToFunctionField O).hom.comp
    (((cU D).toScheme.presheaf.map (homOfLE hO).op).hom.comp ((cU D).ι.app W').hom)

/-- The restriction of a form on `Q` to `Q' ⊆ Q`. -/
private noncomputable abbrev pr {Q Q' : (cU D).toScheme.Opens} (h : Q' ≤ Q) (p : ℤ)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.obj (op Q)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.obj (op Q') :=
  ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.map (homOfLE h).op x

/-- **The rational form of a logarithmic form lies in the logarithmic lattice.** On an affine
open `W'` inside a chart `W` of `D`, the rational form of a section of `I · Ω^p(log D)` over `W'`
is a combination of the logarithmic monomials with coefficients the germs of elements of `I(W')`.
-/
private theorem ratForm_mem_logLattice {x : X} {W : X.affineOpens}
    {V : (Spec (.of k)).affineOpens} {e : (W : X.Opens) ≤ f ⁻¹ᵁ (V : (Spec (.of k)).Opens)}
    {t : Fin n → Γ(X, W)} (hx : x ∈ (W : X.Opens))
    (hb : letI := (f.appLE V W e).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄Γ(Spec (.of k), V)],
        ∀ i, b i = KaehlerDifferential.D Γ(Spec (.of k), V) Γ(X, W) (t i))
    {r : ℕ} (hr : r ≤ n) {j : Fin r → MMP.Mori.PrimeDivisor X} (hj : Function.Injective j)
    (hjD : ∀ i, j i ∈ D.support ∧ x ∈ (j i).support ∧
      (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)})
    (hDW : D.suppIdeal.ideal W = Ideal.span {∏ i, t (Fin.castLE hr i)})
    {p : ℕ} {W' : X.affineOpens} (hW' : (W' : X.Opens) ≤ W) (I : X.IdealSheafData)
    {η : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ (W' : X.Opens)))}
    (hη : η ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W')
    (O : (cU D).toScheme.affineOpens) (hO : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ
      (W' : X.Opens)) [Nonempty (O : (cU D).toScheme.Opens)] :
    letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    ratForm ((cU D).ι ≫ f) p O
        ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hO).op η) ∈
      logLattice (logBasis (k := k)
          (fun i => gmO D O (hO.trans (Scheme.Hom.preimage_mono _ hW')) (t i)) r)
        ((I.ideal W').toAddSubgroup.map (gmO D O hO).toAddMonoidHom) p := by
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  have hsu : ∀ i : Fin r, IsUnit (((cU D).ι.app W).hom (t (Fin.castLE hr i))) := fun i =>
    B1.isUnit_res_of_ideal_eq D (hjD i).1 (hjD i).2.2
  let s : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W : X.Opens)) := fun i =>
    ((hsu i).unit⁻¹ : (Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W : X.Opens)))ˣ).val
  have hs : ∀ i, s i * ((cU D).ι.app W).hom (t (Fin.castLE hr i)) = 1 := fun i =>
    (hsu i).val_inv_mul
  obtain ⟨-, hiff, -⟩ := (MMP.Mori.Divisor.relativeLogForms_free_and_deRhamD_mem n f D hD).2 x W V
    e t hx hb r hr j hj hjD hDW s hs p W' hW'
  obtain ⟨c, hc, hcombo⟩ := (hiff I η).1 hη
  have hrat := ratForm_eq_sum_ιMulti_of_incl_eq_combo f D W t hr s hs _ rfl p W' hW' c η hcombo
    O hO
  rw [hrat]
  refine sum_mem fun K _ => ?_
  convert gen_mem_logLattice (β := logBasis (k := k)
      (fun i => gmO D O (hO.trans (Scheme.Hom.preimage_mono _ hW')) (t i)) r)
    (J := (I.ideal W').toAddSubgroup.map (gmO D O hO).toAddMonoidHom) ⟨c K, hc K, rfl⟩
    (fun j => K.1.orderEmbOfFin K.2 j) using 2
  · rfl
  · rfl

/-- A function, read as a form of degree zero on `U ∩ W'`. -/
private noncomputable def fnForm {W' : X.Opens} (a : Γ(X, W')) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece ((0 : ℕ) : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ W')) :=
  asStr (((cU D).ι.app W').hom a) •
    (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).toPresheafGradedAlgebra.one.eval _

private theorem incl_fnForm {W' : X.Opens} (a : Γ(X, W')) :
    (TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ) (fnForm f D a) =
      sm ((cU D).ι ≫ f) _ (((cU D).ι.app W').hom a) := by
  unfold fnForm
  rw [Stacks.GradedAlgebra.incl_smul]
  change _ • (TB ((cU D).ι ≫ f)).incl 0 _ = _
  rw [← Stacks.GradedAlgebra.one_eq_incl]
  rfl

/-- The products `ξ₁ ∧ ⋯ ∧ ξ_q ∧ a` of chosen `1`-forms with a function. -/
private noncomputable def monoForm {W' : X.Opens}
    (θ : Fin n → ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.obj
      (op ((cU D).ι ⁻¹ᵁ W'))) (a : Γ(X, W')) :
    (q : ℕ) → (Fin q → Fin n) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (q : ℤ)).val.obj
        (op ((cU D).ι ⁻¹ᵁ W'))
  | 0, _ => fnForm f D a
  | q + 1, w => wedgeOne ((cU D).ι ≫ f) q (θ (w 0)) (monoForm θ a q (Fin.tail w))

private theorem monoForm_mem {W' : X.affineOpens}
    (θ : Fin n → ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.obj
      (op ((cU D).ι ⁻¹ᵁ (W' : X.Opens))))
    (hθ : ∀ i, θ i ∈ MMP.Mori.Divisor.relativeLogForms n f D hD ⊤ 1 W') (I : X.IdealSheafData)
    {a : Γ(X, W')} (ha : a ∈ I.ideal W') :
    ∀ (q : ℕ) (w : Fin q → Fin n),
      monoForm n f D θ a q w ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I q W' := by
  intro q
  induction q with
  | zero =>
    intro w
    refine (B1.mem_relativeLogForms_iff f D n hD _ _ _ _).mpr fun x hx => ⟨W', le_rfl, hx, ?_⟩
    rw [piece_map_id]
    change (TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ) (fnForm f D a) ∈ _
    rw [incl_fnForm]
    refine AddSubgroup.subset_closure ⟨a, ha, 1, Subring.one_mem _, ?_⟩
    rw [mul_one]
  | succ q ih =>
    intro w
    exact B1.wedgeOne_mem_relativeLogForms f D n hD I q W' _ _ (hθ _) (ih _)

/-- The rational form of a product `ξ₁ ∧ ⋯ ∧ ξ_q ∧ a`. -/
private theorem ratTotal_monoForm {W' : X.Opens} (O : (cU D).toScheme.affineOpens)
    [Nonempty (O : (cU D).toScheme.Opens)] (hO : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ W')
    (θ : Fin n → ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.obj
      (op ((cU D).ι ⁻¹ᵁ W')))
    (β : letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
      Fin n → Ω[(cU D).toScheme.functionField⁄k])
    (hθ : ∀ i, ratTotal ((cU D).ι ≫ f) O ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hO).op
      ((TB ((cU D).ι ≫ f)).incl 1 (θ i))) = ExteriorAlgebra.ι _ (β i)) (a : Γ(X, W')) :
    ∀ (q : ℕ) (w : Fin q → Fin n),
      ratTotal ((cU D).ι ≫ f) O ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hO).op
        ((TB ((cU D).ι ≫ f)).incl (q : ℤ) (monoForm n f D θ a q w))) =
      algebraMap _ _ (gmO D O hO a) * ExteriorAlgebra.ιMulti _ q (β ∘ w) := by
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  intro q
  induction q with
  | zero =>
    intro w
    change ratTotal _ O ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hO).op
      ((TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ) (fnForm f D a))) = _
    rw [incl_fnForm, totalRestrict_sm]
    refine (ratTotal_structureMap _ O _).trans ?_
    rw [ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    rfl
  | succ q ih =>
    intro w
    change ratTotal _ O ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hO).op
      ((TB ((cU D).ι ≫ f)).incl ((q + 1 : ℕ) : ℤ)
        (wedgeOne ((cU D).ι ≫ f) q (θ (w 0)) (monoForm n f D θ a q (Fin.tail w))))) = _
    rw [incl_wedgeOne, ← (TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply, map_mul,
      (TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply,
      (TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply, ratTotal_mul _ O ?_ ?_, hθ, ih,
      ExteriorAlgebra.ιMulti_succ_apply, ← mul_assoc, ← Algebra.commutes, mul_assoc]
    · rfl
    · rw [Stacks.GradedAlgebra.totalRestrict_incl]
      exact incl_mem_nonnegForms _ _ 1 _
    · rw [Stacks.GradedAlgebra.totalRestrict_incl]
      exact incl_mem_nonnegForms _ _ q _

/-- The chart one-forms on `U ∩ W`: `sᵢ dtᵢ` (`= dtᵢ/tᵢ`) for `i < r`, and `dtᵢ` for `i ≥ r`. -/
private noncomputable def chartForm {W : X.Opens} {r : ℕ} (t : Fin n → Γ(X, W))
    (s : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ W)) (i : Fin n) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.obj
      (op ((cU D).ι ⁻¹ᵁ W)) :=
  if h : (i : ℕ) < r then asStr (s ⟨i, h⟩) • dF f D _ (((cU D).ι.app W).hom (t i))
  else dF f D _ (((cU D).ι.app W).hom (t i))

private theorem chartForm_mem {W : X.affineOpens} {r : ℕ} {t : Fin n → Γ(X, W)} (hr : r ≤ n)
    {j : Fin r → MMP.Mori.PrimeDivisor X}
    (hjD : ∀ i, j i ∈ D.support ∧ (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)})
    {s : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W : X.Opens))}
    (hs : ∀ i, s i * ((cU D).ι.app W).hom (t (Fin.castLE hr i)) = 1) (i : Fin n) :
    chartForm n f D t s i ∈ MMP.Mori.Divisor.relativeLogForms n f D hD ⊤ 1 W := by
  unfold chartForm
  split_ifs with h
  · exact B1.dlog_mem_relativeLogForms f D n hD (hjD ⟨i, h⟩).1 (hjD ⟨i, h⟩).2 (s ⟨i, h⟩)
      (hs ⟨i, h⟩)
  · exact B1.δ_mem_relativeLogForms f D n hD _ (t i)

private theorem ratTotal_chartForm {W W' : X.Opens} (hW' : W' ≤ W) {r : ℕ} {t : Fin n → Γ(X, W)}
    (hr : r ≤ n) {s : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ W)}
    (hs : ∀ i, s i * ((cU D).ι.app W).hom (t (Fin.castLE hr i)) = 1)
    (O : (cU D).toScheme.affineOpens) [Nonempty (O : (cU D).toScheme.Opens)]
    (hO : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ W') (i : Fin n) :
    letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    ratTotal ((cU D).ι ≫ f) O ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hO).op
      ((TB ((cU D).ι ≫ f)).incl 1
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.map
          (homOfLE (Scheme.Hom.preimage_mono _ hW')).op (chartForm n f D t s i)))) =
      ExteriorAlgebra.ι _ (logBasis (k := k)
        (fun i => gmO D O (hO.trans (Scheme.Hom.preimage_mono _ hW')) (t i)) r i) := by
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  have hO' : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ W := hO.trans (Scheme.Hom.preimage_mono _ hW')
  rw [incl_map f D _ 1, totalRestrict_totalRestrict _ _ (homOfLE hO').op]
  unfold chartForm logBasis
  split_ifs with h
  · rw [← sm_mul_incl]
    exact ratTotal_totalRestrict_logOne ((cU D).ι ≫ f) hO' (hs ⟨i, h⟩)
  · exact ratTotal_totalRestrict_exactOne ((cU D).ι ≫ f) hO' _

/-- The rational form at `O` of a form on an open containing `O`, as an additive map. -/
private noncomputable def ratAt {Q : (cU D).toScheme.Opens} (O : (cU D).toScheme.affineOpens)
    [Nonempty (O : (cU D).toScheme.Opens)] (hO : (O : (cU D).toScheme.Opens) ≤ Q) (p : ℤ) :
    letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.obj (op Q) →+
      ExteriorAlgebra (cU D).toScheme.functionField
        Ω[(cU D).toScheme.functionField⁄k] :=
  (ratTotal ((cU D).ι ≫ f) O).comp
    (((TB ((cU D).ι ≫ f)).totalRestrictRingHom (homOfLE hO).op).toAddMonoidHom.comp
      (AddMonoidHom.mk' ((TB ((cU D).ι ≫ f)).incl p) (fun x y => map_add _ x y)))

private theorem ratAt_apply {Q : (cU D).toScheme.Opens} (O : (cU D).toScheme.affineOpens)
    [Nonempty (O : (cU D).toScheme.Opens)] (hO : (O : (cU D).toScheme.Opens) ≤ Q) (p : ℤ) (x) :
    ratAt f D O hO p x = ratTotal ((cU D).ι ≫ f) O ((TB ((cU D).ι ≫ f)).totalRestrict
      (homOfLE hO).op ((TB ((cU D).ι ≫ f)).incl p x)) :=
  show ratTotal ((cU D).ι ≫ f) O ((TB ((cU D).ι ≫ f)).totalRestrictRingHom (homOfLE hO).op
      ((TB ((cU D).ι ≫ f)).incl p x)) = _ from
    congrArg (ratTotal ((cU D).ι ≫ f) O) ((TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply _ _)

/-- **Every element of the logarithmic lattice is the rational form of a logarithmic form.** On
an affine open `W'` inside a chart `W` of `D`, a combination of logarithmic monomials with
coefficients the germs of elements of `I(W')` is the rational form of a section of
`I · Ω^p(log D)` over `W'`. -/
private theorem exists_relativeLogForms_of_mem_logLattice {W : X.affineOpens} {r : ℕ}
    {t : Fin n → Γ(X, W)} (hr : r ≤ n) {j : Fin r → MMP.Mori.PrimeDivisor X}
    (hjD : ∀ i, j i ∈ D.support ∧ (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)})
    {s : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W : X.Opens))}
    (hs : ∀ i, s i * ((cU D).ι.app W).hom (t (Fin.castLE hr i)) = 1)
    {W' : X.affineOpens} (hW' : (W' : X.Opens) ≤ W) (I : X.IdealSheafData)
    (O : (cU D).toScheme.affineOpens) [Nonempty (O : (cU D).toScheme.Opens)]
    (hO : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ (W' : X.Opens)) {p : ℕ}
    {x : letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
      ⋀[(cU D).toScheme.functionField]^p (Ω[(cU D).toScheme.functionField⁄k])}
    (hx : letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
      x ∈ logLattice (logBasis (k := k)
          (fun i => gmO D O (hO.trans (Scheme.Hom.preimage_mono _ hW')) (t i)) r)
        ((I.ideal W').toAddSubgroup.map (gmO D O hO).toAddMonoidHom) p) :
    letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    ∃ η ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W',
      ratAt f D O hO p η = (x : ExteriorAlgebra _ _) := by
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  set θ' : Fin n → ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.obj
      (op ((cU D).ι ⁻¹ᵁ (W' : X.Opens))) := fun i =>
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.map
      (homOfLE (Scheme.Hom.preimage_mono _ hW')).op (chartForm n f D t s i)
  have hθ' : ∀ i, θ' i ∈ MMP.Mori.Divisor.relativeLogForms n f D hD ⊤ 1 W' := fun i =>
    G1.relativeLogForms_restrict n f D hD ⊤ 1 hW' (chartForm_mem n f D hD hr hjD hs i)
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, w, rfl⟩ := hx
    obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.mp hc
    refine ⟨monoForm n f D θ' a p w, monoForm_mem n f D hD θ' hθ' I ha p w, ?_⟩
    rw [ratAt_apply, ratTotal_monoForm n f D O hO θ' _
      (fun i => ratTotal_chartForm n f D hW' hr hs O hO i) a p w]
    rw [Submodule.coe_smul_of_tower, Algebra.smul_def, exteriorPower.ιMulti_apply_coe]
    rfl
  | zero => exact ⟨0, G1.zero_mem_relativeLogForms n f D hD I p W', map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨η₁, h₁, e₁⟩ := hx
    obtain ⟨η₂, h₂, e₂⟩ := hy
    exact ⟨η₁ + η₂, G1.add_mem_relativeLogForms n f D hD I p h₁ h₂, by
      rw [map_add, e₁, e₂, Submodule.coe_add]⟩
  | neg x _ hx =>
    obtain ⟨η, h, e⟩ := hx
    refine ⟨-η, ?_, by rw [map_neg, e, Submodule.coe_neg]⟩
    have h' := G1.smul_mem_relativeLogForms n f D hD I p (-1) h
    convert h' using 1
    refine Eq.trans ?_ (congrArg (· • η) (map_neg ((cU D).ι.app W').hom 1).symm)
    refine Eq.trans ?_ (congrArg (fun r => -r • η) (map_one ((cU D).ι.app W').hom).symm)
    exact (neg_one_smul ((Stacks.RingedSpace.structureRingSheaf
      (cU D).toScheme.toRingedSpace).obj.obj (op ((cU D).ι ⁻¹ᵁ (W' : X.Opens)))) η).symm

private theorem gmO_eq_gmU {W' : X.Opens} (O : (cU D).toScheme.affineOpens)
    [Nonempty (O : (cU D).toScheme.Opens)] (hO : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ W')
    [Nonempty ((cU D).ι ⁻¹ᵁ W')] (a : Γ(X, W')) : gmO D O hO a = gmU (cU D) W' a := by
  change ((cU D).toScheme.presheaf.map (homOfLE hO).op ≫
    (cU D).toScheme.germToFunctionField O).hom (((cU D).ι.app W').hom a) = _
  unfold Scheme.germToFunctionField
  rw [TopCat.Presheaf.germ_res]
  rfl

private theorem ratAt_restrict {Q Q' : (cU D).toScheme.Opens} (h : Q' ≤ Q)
    (O : (cU D).toScheme.affineOpens) [Nonempty (O : (cU D).toScheme.Opens)]
    (hO : (O : (cU D).toScheme.Opens) ≤ Q') (p : ℤ)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.obj (op Q)) :
    ratAt f D O hO p (pr f D h p x) = ratAt f D O (hO.trans h) p x := by
  rw [ratAt_apply, ratAt_apply]
  exact congrArg (ratTotal ((cU D).ι ≫ f) O) ((congrArg _ (incl_map f D (homOfLE h).op p x)).trans
    (totalRestrict_totalRestrict _ _ _ _))

/-- `ratTotal` turns multiplication by a function on `Q ⊇ O` into multiplication by its germ. -/
private theorem ratTotal_totalRestrict_sm_mul {Q : (cU D).toScheme.Opens}
    (O : (cU D).toScheme.affineOpens) [Nonempty (O : (cU D).toScheme.Opens)]
    (hO : (O : (cU D).toScheme.Opens) ≤ Q) [Nonempty Q] (a : Γ((cU D).toScheme, Q)) (p : ℕ)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op Q)) :
    letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    ratTotal ((cU D).ι ≫ f) O ((TB ((cU D).ι ≫ f)).totalRestrict (homOfLE hO).op
      (sm ((cU D).ι ≫ f) Q a * (TB ((cU D).ι ≫ f)).incl (p : ℤ) x)) =
      algebraMap _ _ ((cU D).toScheme.germToFunctionField Q a) * ratAt f D O hO p x := by
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  rw [ratAt_apply, ← (TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply, map_mul,
    (TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply, (TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply,
    totalRestrict_sm]
  rw [show sm ((cU D).ι ≫ f) (O : (cU D).toScheme.Opens)
      ((cU D).toScheme.presheaf.map (homOfLE hO).op a) =
      (TB ((cU D).ι ≫ f)).structureMap (op (O : (cU D).toScheme.Opens))
        ((cU D).toScheme.presheaf.map (homOfLE hO).op a) from rfl,
    ratTotal_mul _ O (structureMap_mem_nonnegForms _ _ _) ?_]
  · refine congrArg (· * _) ((ratTotal_structureMap _ O _).trans ?_)
    congr 1
    change ((cU D).toScheme.presheaf.map (homOfLE hO).op ≫
      (cU D).toScheme.germToFunctionField O).hom a = _
    unfold Scheme.germToFunctionField
    rw [TopCat.Presheaf.germ_res]
  · rw [Stacks.GradedAlgebra.totalRestrict_incl]
    exact incl_mem_nonnegForms _ _ p _

set_option maxRecDepth 4000 in
/-- The rational form of a form `η` over `U ∩ W'` at `O ⊆ U ∩ W'`, as the rational form of its
restriction. -/
private theorem ratAt_eq_ratForm {W' : X.Opens} (O : (cU D).toScheme.affineOpens)
    [Nonempty (O : (cU D).toScheme.Opens)] (hO : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ W')
    (p : ℕ) (η : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ W'))) :
    ratAt f D O hO p η = (ratForm ((cU D).ι ≫ f) p O
      ((((cU D).ι ≫ f).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hO).op η) : _) :=
  (ratAt_apply f D O hO p η).trans (ratTotal_totalRestrict_incl_eq O hO p η)

set_option maxRecDepth 4000 in
/-- **Extraction of the lattice from a local representation.** If a form on `U ∩ W' ∩ V'` is
`∑ gᵢ ηᵢ` with `ηᵢ ∈ I · Ω^p(log D)` on `W'`, and on `W'' ⊆ W'` (inside a chart `W`) each
`gᵢ = hᵢ g₀`, then its rational form is `g₀` times an element of the logarithmic lattice with
coefficients in the germs of `I(W'')`. -/
private theorem ratTotal_sum_mem_logLattice {x : X} {W : X.affineOpens}
    {V : (Spec (.of k)).affineOpens} {e : (W : X.Opens) ≤ f ⁻¹ᵁ (V : (Spec (.of k)).Opens)}
    {t : Fin n → Γ(X, W)} (hx : x ∈ (W : X.Opens))
    (hb : letI := (f.appLE V W e).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄Γ(Spec (.of k), V)],
        ∀ i, b i = KaehlerDifferential.D Γ(Spec (.of k), V) Γ(X, W) (t i))
    {r : ℕ} (hr : r ≤ n) {j : Fin r → MMP.Mori.PrimeDivisor X} (hj : Function.Injective j)
    (hjD : ∀ i, j i ∈ D.support ∧ x ∈ (j i).support ∧
      (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)})
    (hDW : D.suppIdeal.ideal W = Ideal.span {∏ i, t (Fin.castLE hr i)})
    {V' : X.Opens} {W' W'' : X.affineOpens} (hW''W : (W'' : X.Opens) ≤ W)
    (hW'' : (W'' : X.Opens) ≤ W') (I : X.IdealSheafData) {p m : ℕ}
    (g : Fin m → Γ(X, (W' : X.Opens) ⊓ V'))
    (η : Fin m → ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      (p : ℤ)).val.obj (op ((cU D).ι ⁻¹ᵁ (W' : X.Opens))))
    (hη : ∀ i, η i ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W')
    (g₀ : Γ(X, (W'' : X.Opens) ⊓ V')) (h : Fin m → Γ(X, W''))
    (hh : ∀ i, X.presheaf.map (homOfLE (inf_le_inf_right V' hW'')).op (g i) =
      X.presheaf.map (homOfLE inf_le_left).op (h i) * g₀)
    (O : (cU D).toScheme.affineOpens) [Nonempty (O : (cU D).toScheme.Opens)]
    (hO : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ ((W'' : X.Opens) ⊓ V')) :
    letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    haveI : Nonempty ((cU D).ι ⁻¹ᵁ (W : X.Opens)) :=
      ⟨⟨_, (hO.trans (Scheme.Hom.preimage_mono _ (inf_le_left.trans hW''W))) (Classical.arbitrary
        (O : (cU D).toScheme.Opens)).2⟩⟩
    haveI : Nonempty ((cU D).ι ⁻¹ᵁ (W'' : X.Opens)) :=
      ⟨⟨_, (hO.trans (Scheme.Hom.preimage_mono _ inf_le_left)) (Classical.arbitrary
        (O : (cU D).toScheme.Opens)).2⟩⟩
    haveI : Nonempty ((cU D).ι ⁻¹ᵁ ((W'' : X.Opens) ⊓ V')) :=
      ⟨⟨_, hO (Classical.arbitrary (O : (cU D).toScheme.Opens)).2⟩⟩
    ∃ y ∈ logLattice (logBasis (k := k) (fun i => gmU (cU D) W (t i)) r)
        ((I.ideal W'').toAddSubgroup.map (gmU (cU D) (W'' : X.Opens)).toAddMonoidHom) p,
      ratTotal ((cU D).ι ≫ f) O ((TB ((cU D).ι ≫ f)).totalRestrict
          (homOfLE (hO.trans (Scheme.Hom.preimage_mono _ (inf_le_inf_right V' hW'')))).op
          (∑ i, sm ((cU D).ι ≫ f) _ (((cU D).ι.app ((W' : X.Opens) ⊓ V')).hom (g i)) *
            (TB ((cU D).ι ≫ f)).incl (p : ℤ)
              (pr f D (Scheme.Hom.preimage_mono _ inf_le_left) (p : ℤ) (η i)))) =
        algebraMap _ _ (gmU (cU D) ((W'' : X.Opens) ⊓ V') g₀) * (y : ExteriorAlgebra _ _) := by
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  have : Nonempty ((cU D).ι ⁻¹ᵁ (W : X.Opens)) :=
    ⟨⟨_, (hO.trans (Scheme.Hom.preimage_mono _ (inf_le_left.trans hW''W))) (Classical.arbitrary
      (O : (cU D).toScheme.Opens)).2⟩⟩
  have : Nonempty ((cU D).ι ⁻¹ᵁ (W'' : X.Opens)) :=
    ⟨⟨_, (hO.trans (Scheme.Hom.preimage_mono _ inf_le_left)) (Classical.arbitrary
      (O : (cU D).toScheme.Opens)).2⟩⟩
  have : Nonempty ((cU D).ι ⁻¹ᵁ ((W'' : X.Opens) ⊓ V')) :=
    ⟨⟨_, hO (Classical.arbitrary (O : (cU D).toScheme.Opens)).2⟩⟩
  have : Nonempty ((cU D).ι ⁻¹ᵁ ((W' : X.Opens) ⊓ V')) :=
    ⟨⟨_, (hO.trans (Scheme.Hom.preimage_mono _ (inf_le_inf_right V' hW'')))
      (Classical.arbitrary (O : (cU D).toScheme.Opens)).2⟩⟩
  have hOW'' : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ (W'' : X.Opens) :=
    hO.trans (Scheme.Hom.preimage_mono _ inf_le_left)
  -- the lattice elements of the `ηᵢ`
  have hy : ∀ i, ratAt f D O hOW'' p (pr f D (Scheme.Hom.preimage_mono _ hW'') (p : ℤ)
        (η i)) ∈ (logLattice (logBasis (k := k) (fun i => gmU (cU D) W (t i)) r)
        ((I.ideal W'').toAddSubgroup.map (gmU (cU D) (W'' : X.Opens)).toAddMonoidHom) p).map
          (⋀[(cU D).toScheme.functionField]^p (Ω[(cU D).toScheme.functionField⁄k])).subtype.toAddMonoidHom := by
    intro i
    rw [ratAt_eq_ratForm]
    refine ⟨_, ?_, rfl⟩
    have hm := ratForm_mem_logLattice n f D hD hx hb hr hj hjD hDW hW''W I
      (G1.relativeLogForms_restrict n f D hD I p hW'' (hη i)) O hOW''
    have e1 : (fun i => gmO D O (hOW''.trans (Scheme.Hom.preimage_mono _ hW''W)) (t i)) =
        fun i => gmU (cU D) W (t i) := funext fun i => gmO_eq_gmU D O _ (t i)
    have e2 : (gmO D O hOW'').toAddMonoidHom = (gmU (cU D) (W'' : X.Opens)).toAddMonoidHom :=
      AddMonoidHom.ext fun a => gmO_eq_gmU D O _ a
    rw [e1, e2] at hm
    exact hm
  choose y hyJ hyeq using fun i => AddSubgroup.mem_map.mp (hy i)
  refine ⟨∑ i, gmU (cU D) (W'' : X.Opens) (h i) • y i, sum_mem fun i _ => smul_mem_logLattice
    (fun c hc => ?_) (hyJ i), ?_⟩
  · obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.mp hc
    exact ⟨h i * a, Ideal.mul_mem_left _ _ ha, by simp⟩
  · rw [← (TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply, map_sum, map_sum]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Algebra.smul_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply,
      ratTotal_totalRestrict_sm_mul f D O _ _ p,
      ratAt_restrict f D (Scheme.Hom.preimage_mono _ inf_le_left) O _ (p : ℤ),
      ← ratAt_restrict f D (Scheme.Hom.preimage_mono _ hW'') O hOW'' (p : ℤ)]
    change _ * ratAt f D O hOW'' p _ = _
    rw [← hyeq i]
    change algebraMap _ _ (gmU (cU D) ((W' : X.Opens) ⊓ V') (g i)) * _ = _
    rw [← gmU_restrict (cU D) (inf_le_inf_right V' hW''), hh i, map_mul,
      gmU_restrict (cU D) (inf_le_left : (W'' : X.Opens) ⊓ V' ≤ W''), map_mul]
    simp only [AddMonoidHom.coe_coe, Submodule.coe_subtype, LinearMap.toAddMonoidHom_coe]
    simp only [← mul_assoc, ← map_mul, mul_comm (gmU (cU D) (W'' : X.Opens) (h i))]

end ChartLattice

section ExteriorScalars

open exteriorPower

/-- Moving scalars out of a form: `(a b g) · y = g · (b • a • y)` in the exterior algebra. -/
private theorem algebraMap_mul_coe_smul_smul {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {p : ℕ} (a b g : K) (y : ⋀[K]^p V) :
    algebraMap K (ExteriorAlgebra K V) (a * b * g) * (y : ExteriorAlgebra K V) =
      algebraMap K (ExteriorAlgebra K V) g * ((b • a • y : ⋀[K]^p V) : ExteriorAlgebra K V) := by
  simp only [Submodule.coe_smul_of_tower, Algebra.smul_def, ← mul_assoc, ← map_mul]
  congr 2
  ring

/-- Moving scalars out of a form: `(a b g) · (a⁻¹ • y) = g · (b • y)` for `a ≠ 0`. -/
private theorem algebraMap_mul_coe_inv_smul {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {p : ℕ} {a : K} (ha : a ≠ 0) (b g : K) (y : ⋀[K]^p V) :
    algebraMap K (ExteriorAlgebra K V) (a * b * g) * ((a⁻¹ • y : ⋀[K]^p V) : ExteriorAlgebra K V) =
      algebraMap K (ExteriorAlgebra K V) g * ((b • y : ⋀[K]^p V) : ExteriorAlgebra K V) := by
  simp only [Submodule.coe_smul_of_tower, Algebra.smul_def]
  have hs : a * b * g * a⁻¹ = g * b :=
    calc a * b * g * a⁻¹ = a * a⁻¹ * (g * b) := by ring
      _ = g * b := by rw [mul_inv_cancel₀ ha, one_mul]
  rw [← mul_assoc, ← mul_assoc, ← (algebraMap K (ExteriorAlgebra K V)).map_mul,
    ← (algebraMap K (ExteriorAlgebra K V)).map_mul, hs]

end ExteriorScalars

section LocalHomotopy

open MMP.FourfoldProofs.FractionalLogComplexProof KaehlerDifferential exteriorPower

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  (n : ℕ) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (D : Divisor X)
  (hD : D.IsRelativeSNC n f) [Nonempty (cU D)] (S M : Divisor X)

/-- **Realization in `C^•`.** A combination `g₀ x` of logarithmic monomials, `g₀` a section of
`𝒪_X(-M)` on `W''` and `x` with coefficients in the germs of `I_S(W'')`, is the rational form of a
section of `C^p = 𝒪_X(-M) · Ω^p(log D)(-S)` over `W''`. -/
private theorem exists_cond_of_mem_logLattice {W : X.affineOpens} {r : ℕ}
    {t : Fin n → Γ(X, W)} (hr : r ≤ n) {j : Fin r → MMP.Mori.PrimeDivisor X}
    (hjD : ∀ i, j i ∈ D.support ∧ (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)})
    {s : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W : X.Opens))}
    (hs : ∀ i, s i * ((cU D).ι.app W).hom (t (Fin.castLE hr i)) = 1)
    {W'' : X.affineOpens} (hW'' : (W'' : X.Opens) ≤ W) {g₀ : Γ(X, (W'' : X.Opens) ⊓ cU' D M)}
    (hg₀ : DivCond (D := D) (M := M) (W'' : X.Opens) g₀)
    (O : (cU D).toScheme.affineOpens) [Nonempty (O : (cU D).toScheme.Opens)]
    (hO : (O : (cU D).toScheme.Opens) ≤ OO D M W'') {p : ℕ}
    {x : letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
      ⋀[(cU D).toScheme.functionField]^p (Ω[(cU D).toScheme.functionField⁄k])}
    (hx : letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
      haveI : Nonempty ((cU D).ι ⁻¹ᵁ (W : X.Opens)) :=
        ⟨⟨_, (hO.trans (Scheme.Hom.preimage_mono _ (inf_le_left.trans hW''))) (Classical.arbitrary
          (O : (cU D).toScheme.Opens)).2⟩⟩
      haveI : Nonempty ((cU D).ι ⁻¹ᵁ (W'' : X.Opens)) :=
        ⟨⟨_, (hO.trans (Scheme.Hom.preimage_mono _ inf_le_left)) (Classical.arbitrary
          (O : (cU D).toScheme.Opens)).2⟩⟩
      x ∈ logLattice (logBasis (k := k) (fun i => gmU (cU D) W (t i)) r)
        ((S.suppIdeal.ideal W'').toAddSubgroup.map (gmU (cU D) (W'' : X.Opens)).toAddMonoidHom) p) :
    letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    haveI : Nonempty ((cU D).ι ⁻¹ᵁ ((W'' : X.Opens) ⊓ cU' D M)) :=
      ⟨⟨_, hO (Classical.arbitrary (O : (cU D).toScheme.Opens)).2⟩⟩
    ∃ ζ, Cond n f D hD S M p W'' ζ ∧
      ratAt f D O hO p ζ = algebraMap _ _ (gmU (cU D) ((W'' : X.Opens) ⊓ cU' D M) g₀) *
        (x : ExteriorAlgebra _ _) := by
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  have : Nonempty ((cU D).ι ⁻¹ᵁ (W : X.Opens)) :=
    ⟨⟨_, (hO.trans (Scheme.Hom.preimage_mono _ (inf_le_left.trans hW''))) (Classical.arbitrary
      (O : (cU D).toScheme.Opens)).2⟩⟩
  have : Nonempty ((cU D).ι ⁻¹ᵁ (W'' : X.Opens)) :=
    ⟨⟨_, (hO.trans (Scheme.Hom.preimage_mono _ inf_le_left)) (Classical.arbitrary
      (O : (cU D).toScheme.Opens)).2⟩⟩
  have : Nonempty ((cU D).ι ⁻¹ᵁ ((W'' : X.Opens) ⊓ cU' D M)) :=
    ⟨⟨_, hO (Classical.arbitrary (O : (cU D).toScheme.Opens)).2⟩⟩
  have hO' : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ (W'' : X.Opens) :=
    hO.trans (Scheme.Hom.preimage_mono _ inf_le_left)
  have e1 : (fun i => gmU (cU D) W (t i)) =
      fun i => gmO D O (hO'.trans (Scheme.Hom.preimage_mono _ hW'')) (t i) :=
    funext fun i => (gmO_eq_gmU D O _ (t i)).symm
  have e2 : (gmU (cU D) (W'' : X.Opens)).toAddMonoidHom = (gmO D O hO').toAddMonoidHom :=
    AddMonoidHom.ext fun a => (gmO_eq_gmU D O _ a).symm
  rw [e1, e2] at hx
  obtain ⟨η, hη, hηx⟩ := exists_relativeLogForms_of_mem_logLattice n f D hD hr hjD hs hW''
    S.suppIdeal O hO' hx
  refine ⟨asStr (((cU D).ι.app ((W'' : X.Opens) ⊓ cU' D M)).hom g₀) •
    pr f D (Scheme.Hom.preimage_mono _ inf_le_left) (p : ℤ) η, fun y hy => ?_, ?_⟩
  · refine ⟨W'', le_rfl, hy, 1, fun _ => g₀, fun _ => η, fun _ => hg₀, fun _ => hη, ?_⟩
    rw [Fin.sum_univ_one, piece_map_id, ← sm_mul_incl]
    rfl
  · rw [ratAt_apply, ← sm_mul_incl, ratTotal_totalRestrict_sm_mul f D O hO, ratAt_restrict, hηx]
    rfl

include n in
set_option maxRecDepth 8000 in
/-- **Forms are determined by their rational forms** at a single non-empty affine open. -/
private theorem eq_of_ratAt_eq {Q : (cU D).toScheme.Opens} (O : (cU D).toScheme.affineOpens)
    [Nonempty (O : (cU D).toScheme.Opens)] (hO : (O : (cU D).toScheme.Opens) ≤ Q) (p : ℕ)
    {ω₁ ω₂ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op Q)} (h : ratAt f D O hO p ω₁ = ratAt f D O hO p ω₂) : ω₁ = ω₂ := by
  refine eq_of_ratTotal_eq ((cU D).ι ≫ f) (m := n) p ω₁ ω₂ fun W hW _ => ?_
  rw [ratTotal_totalRestrict_incl_eq, ratTotal_totalRestrict_incl_eq]
  rw [ratAt_apply, ratAt_apply, ratTotal_totalRestrict_incl_eq,
    ratTotal_totalRestrict_incl_eq] at h
  congr 1
  exact (ratForm_eq_of_le _ p ω₁ hW hO).trans ((Subtype.ext h).trans
    (ratForm_eq_of_le _ p ω₂ hW hO).symm)

/-- **The rational form of the connection form** `θ = c du`. -/
private theorem ratAt_θW (u c : Γ(X, cU' D M)) (W : X.Opens) (O : (cU D).toScheme.affineOpens)
    [Nonempty (O : (cU D).toScheme.Opens)] (hO : (O : (cU D).toScheme.Opens) ≤ OO D M W) :
    letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    haveI : Nonempty ((cU D).ι ⁻¹ᵁ cU' D M) :=
      ⟨⟨_, (hO.trans (Scheme.Hom.preimage_mono _ inf_le_right)) (Classical.arbitrary
        (O : (cU D).toScheme.Opens)).2⟩⟩
    ratAt f D O hO 1 (θW f D M u c W) = ExteriorAlgebra.ι _
      (gmU (cU D) (cU' D M) c • KaehlerDifferential.D k _ (gmU (cU D) (cU' D M) u)) := by
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  have : Nonempty ((cU D).ι ⁻¹ᵁ cU' D M) :=
    ⟨⟨_, (hO.trans (Scheme.Hom.preimage_mono _ inf_le_right)) (Classical.arbitrary
      (O : (cU D).toScheme.Opens)).2⟩⟩
  have : Nonempty (OO D M W) := ⟨⟨_, hO (Classical.arbitrary (O : (cU D).toScheme.Opens)).2⟩⟩
  have hg : ∀ a : Γ(X, cU' D M), (cU D).toScheme.germToFunctionField (OO D M W) (resU W a) =
      gmU (cU D) (cU' D M) a := fun a => gmU_restrict (cU D) inf_le_right a
  unfold θW
  rw [ratAt_apply, ← sm_mul_incl]
  refine (ratTotal_totalRestrict_sm_mul f D O hO (resU W c) 1 _).trans ?_
  rw [ratAt_apply]
  refine (congrArg _ (ratTotal_totalRestrict_exactOne ((cU D).ι ≫ f) hO (resU W u))).trans ?_
  rw [map_smul, Algebra.smul_def, hg c]
  congr 3
  change ((cU D).toScheme.presheaf.map (homOfLE hO).op ≫
    (cU D).toScheme.germToFunctionField O).hom (resU W u) = _
  unfold Scheme.germToFunctionField
  rw [TopCat.Presheaf.germ_res]
  exact hg u

/-- The rational form of `∇ω` from that of `ω`, at a non-empty affine open. -/
private theorem ratAt_nab {Q : (cU D).toScheme.Opens} (O : (cU D).toScheme.affineOpens)
    [Nonempty (O : (cU D).toScheme.Opens)] (hO : (O : (cU D).toScheme.Opens) ≤ Q) (p : ℕ)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.obj (op Q))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op Q)) :
    letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    ∀ (θ' ξ : Ω[(cU D).toScheme.functionField⁄k]) (g : (cU D).toScheme.functionField)
      (η : ⋀[(cU D).toScheme.functionField]^p (Ω[(cU D).toScheme.functionField⁄k])),
      ratAt f D O hO 1 θ = ExteriorAlgebra.ι _ θ' →
      ratAt f D O hO p ω = algebraMap _ _ g * (η : ExteriorAlgebra _ _) →
      KaehlerDifferential.D k _ g = g • (θ' + ξ) →
      ratAt f D O hO ((p + 1 : ℕ) : ℤ) (nab ((cU D).ι ≫ f) p θ ω) =
        algebraMap _ _ g * (deRhamDifferential (A := k) p η + wedgeLeft ξ p η :
          ExteriorAlgebra _ _) := by
  intro θ' ξ g η hθ hω hg
  rw [ratAt_apply] at hθ hω ⊢
  exact ratTotal_nab O hO p θ ω θ' ξ g η hθ hω hg

variable {M} in
/-- The local data of the residue homotopy near a point `x`: an affine neighbourhood `W''` of `x`
inside `W₀`, a non-empty affine open `O` of `U ∩ W'' ∩ U'_M` at which rational forms are taken,
the germ `g` of a local generator of `𝒪_X(-M)`, a logarithmic basis `β` and the coefficient groups
`J` (of `C_M`) and `J'` (of `C_{M'}`), the form `ξ` with `∇(g η) = g (dη + ξ ∧ η)`, and the
extraction, realization and homotopy statements. -/
private structure LocalData (u c : Γ(X, cU' D M)) {M' : Divisor X} (hU : cU' D M ≤ cU' D M')
    (x : X) (W₀ : X.Opens) where
  W'' : X.affineOpens
  mem : x ∈ (W'' : X.Opens)
  le : (W'' : X.Opens) ≤ W₀
  O : (cU D).toScheme.affineOpens
  ne : Nonempty (O : (cU D).toScheme.Opens)
  hO : (O : (cU D).toScheme.Opens) ≤ OO D M W''
  g : (cU D).toScheme.functionField
  hg : g ≠ 0
  ξ : letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    Ω[(cU D).toScheme.functionField⁄k]
  β : letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    Fin n → Ω[(cU D).toScheme.functionField⁄k]
  J : AddSubgroup (cU D).toScheme.functionField
  J' : AddSubgroup (cU D).toScheme.functionField
  extract : letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    ∀ (p : ℕ) (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      (p : ℤ)).val.obj (op (OO D M W''))), LocalRep n f D hD S M p W'' ω →
      ∃ y ∈ logLattice β J p, ratAt f D O hO p ω = algebraMap _ _ g * (y : ExteriorAlgebra _ _)
  extract' : letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    ∀ (p : ℕ) (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      (p : ℤ)).val.obj (op (OO D M' W''))), LocalRep n f D hD S M' p W'' ω →
      ∃ y ∈ logLattice β J' p, ratAt f D O (hO.trans (OO_le D hU W'')) p ω =
        algebraMap _ _ g * (y : ExteriorAlgebra _ _)
  realize : letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    ∀ (p : ℕ) (y), y ∈ logLattice β J p → ∃ ζ, Cond n f D hD S M p W'' ζ ∧
      ratAt f D O hO p ζ = algebraMap _ _ g * (y : ExteriorAlgebra _ _)
  realize' : letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    ∀ (p : ℕ) (y), y ∈ logLattice β J' p → ∃ ζ, Cond n f D hD S M' p W'' ζ ∧
      ratAt f D O (hO.trans (OO_le D hU W'')) p ζ = algebraMap _ _ g * (y : ExteriorAlgebra _ _)
  nabla : letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    ∀ (p : ℕ) (ζ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      (p : ℤ)).val.obj (op (OO D M W'')))
      (y : ⋀[(cU D).toScheme.functionField]^p (Ω[(cU D).toScheme.functionField⁄k])),
      ratAt f D O hO p ζ = algebraMap _ _ g * (y : ExteriorAlgebra _ _) →
      ratAt f D O hO ((p + 1 : ℕ) : ℤ) (nab ((cU D).ι ≫ f) p (θW f D M u c W'') ζ) =
        algebraMap _ _ g * (deRhamDifferential (A := k) p y + wedgeLeft ξ p y :
          ExteriorAlgebra _ _)
  homotopy : letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    ∀ (p : ℕ) (y), y ∈ logLattice β J (p + 1) →
      deRhamDifferential (A := k) (p + 1) y + wedgeLeft ξ (p + 1) y ∈ logLattice β J' (p + 2) →
      ∃ ι ∈ logLattice β J p,
        y - (deRhamDifferential (A := k) p ι + wedgeLeft ξ p ι) ∈ logLattice β J' (p + 1)
  homotopy0 : letI := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
    ∀ (y), y ∈ logLattice β J 0 →
      deRhamDifferential (A := k) 0 y + wedgeLeft ξ 0 y ∈ logLattice β J' 1 →
      y ∈ logLattice β J' 0

variable {M} in
/-- A local representation of the restriction of `ω` to `W₁` restricts to `W₂ ⊆ W₁`. -/
private theorem localRep_rO {p : ℕ} {W W₁ W₂ : X.Opens} (h₁ : W₁ ≤ W) (h₂ : W₂ ≤ W₁)
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op (OO D M W))}
    (hω : LocalRep n f D hD S M p W₁ (rO f (p : ℤ) h₁ ω)) :
    LocalRep n f D hD S M p W₂ (rO f (p : ℤ) (h₂.trans h₁) ω) :=
  rO_rO f D M (p : ℤ) h₁ h₂ ω ▸ LocalRep.restrict n f D hD S M h₂ hω

variable {M} in
/-- `∇` commutes with the restriction from `U'_{M'}` to `U'_M`. -/
private theorem trf_nab {M' : Divisor X} (hU : cU' D M ≤ cU' D M') {u c : Γ(X, cU' D M)}
    {u' c' : Γ(X, cU' D M')}
    (hu : X.presheaf.map (homOfLE hU).op u' = u) (hc : X.presheaf.map (homOfLE hU).op c' = c)
    (p : ℕ) (W : X.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op (OO D M' W))) :
    trf f D hU ((p + 1 : ℕ) : ℤ) W (nab ((cU D).ι ≫ f) p (θW f D M' u' c' W) ω) =
      nab ((cU D).ι ≫ f) p (θW f D M u c W) (trf f D hU (p : ℤ) W ω) :=
  (nab_map _ p _ _).trans
    (congrArg (fun θ => nab ((cU D).ι ≫ f) p θ _) (θW_trf f hU hu hc W))

variable {M} in
/-- `∇` of a difference. -/
private theorem nab_sub {Q : (cU D).toScheme.Opens} (p : ℕ)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.obj (op Q))
    (a b : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op Q)) :
    nab ((cU D).ι ≫ f) p θ (a - b) = nab ((cU D).ι ≫ f) p θ a - nab ((cU D).ι ≫ f) p θ b := by
  have h := nab_add (g := (cU D).ι ≫ f) p θ (a - b) b
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

variable {M} in
/-- **Local surjectivity on cycles, in positive degree.** Near every point, a `∇`-closed section of
`C^{p+1}_M` is the restriction of a `∇`-closed section of `C^{p+1}_{M'}` plus `∇` of a section of
`C^p_M`. -/
private theorem exists_cycle_add_nab (u c : Γ(X, cU' D M)) (hloc : LocMon n f D hD S M)
    (hcu : ∀ W : X.Opens, δ ((cU D).ι ≫ f) (OO D M W) (resU W c) *
      δ ((cU D).ι ≫ f) (OO D M W) (resU W u) = 0)
    {M' : Divisor X} (hU : cU' D M ≤ cU' D M') {u' c' : Γ(X, cU' D M')}
    (hu : X.presheaf.map (homOfLE hU).op u' = u) (hc : X.presheaf.map (homOfLE hU).op c' = c)
    (p : ℕ) {W : X.Opens}
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      ((p + 1 : ℕ) : ℤ)).val.obj (op (OO D M W)))
    (hω : Cond n f D hD S M (p + 1) W ω)
    (hcyc : nab ((cU D).ι ≫ f) (p + 1) (θW f D M u c W) ω = 0) {x : X} (hx : x ∈ W)
    (hLD : ∀ W₀ : X.Opens, x ∈ W₀ → Nonempty (LocalData n f D hD S u c hU x W₀)) :
    ∃ (W' : X.Opens) (h : W' ≤ W), x ∈ W' ∧
      ∃ ω' : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
        ((p + 1 : ℕ) : ℤ)).val.obj (op (OO D M' W')),
        Cond n f D hD S M' (p + 1) W' ω' ∧
        nab ((cU D).ι ≫ f) (p + 1) (θW f D M' u' c' W') ω' = 0 ∧
        ∃ ζ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
          (p : ℤ)).val.obj (op (OO D M W')),
          Cond n f D hD S M p W' ζ ∧
          rO f ((p + 1 : ℕ) : ℤ) h ω = trf f D hU ((p + 1 : ℕ) : ℤ) W' ω' +
            nab ((cU D).ι ≫ f) p (θW f D M u c W') ζ := by
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  obtain ⟨Wx, hWx, hxWx, hrep⟩ := (cond_iff n f D hD S M (p + 1) W ω).mp hω x hx
  obtain ⟨L⟩ := hLD Wx hxWx
  have := L.ne
  have hk : (L.W'' : X.Opens) ≤ W := L.le.trans hWx
  refine ⟨L.W'', hk, L.mem, ?_⟩
  have hrep'' : LocalRep n f D hD S M (p + 1) L.W'' (rO f ((p + 1 : ℕ) : ℤ) hk ω) :=
    localRep_rO n f D hD S hWx L.le hrep
  obtain ⟨y, hy, hyeq⟩ := L.extract (p + 1) _ hrep''
  have h0 : nab ((cU D).ι ≫ f) (p + 1) (θW f D M u c L.W'') (rO f ((p + 1 : ℕ) : ℤ) hk ω) = 0 := by
    rw [← θW_restrict f D M u c hk]
    refine (nab_map _ (p + 1) _ _).symm.trans ?_
    rw [hcyc]
    exact map_zero _
  have hn := L.nabla (p + 1) _ y hyeq
  rw [h0, map_zero] at hn
  have hdy := ((L.hg.isUnit.map (algebraMap _ _)).mul_right_eq_zero).mp hn.symm
  rw [ZeroMemClass.coe_eq_zero] at hdy
  obtain ⟨ι, hι, hρ⟩ := L.homotopy p y hy (by rw [hdy]; exact zero_mem _)
  obtain ⟨ζ, hζ, hζeq⟩ := L.realize p ι hι
  obtain ⟨ω', hω', hω'eq⟩ := L.realize' (p + 1) _ hρ
  have hnζ := L.nabla p ζ ι hζeq
  have heq : rO f ((p + 1 : ℕ) : ℤ) hk ω = trf f D hU ((p + 1 : ℕ) : ℤ) L.W'' ω' +
      nab ((cU D).ι ≫ f) p (θW f D M u c L.W'') ζ := by
    refine eq_of_ratAt_eq n f D L.O L.hO (p + 1) ?_
    rw [map_add, hyeq, hnζ]
    erw [ratAt_restrict f D (OO_le D hU L.W'') L.O L.hO]
    rw [hω'eq, ← mul_add, Submodule.coe_sub, Submodule.coe_add, sub_add_cancel]
  refine ⟨ω', hω', ?_, ζ, hζ, heq⟩
  refine eq_of_ratAt_eq n f D L.O (L.hO.trans (OO_le D hU L.W'')) (p + 1 + 1) ?_
  rw [map_zero, ← ratAt_restrict f D (OO_le D hU L.W'') L.O L.hO]
  change ratAt f D L.O L.hO _ (trf f D hU _ L.W'' _) = 0
  rw [trf_nab f D hU hu hc (p + 1) L.W'' ω']
  have h1 := nab_add (g := (cU D).ι ≫ f) (p + 1) (θW f D M u c L.W'')
    (trf f D hU ((p + 1 : ℕ) : ℤ) L.W'' ω') (nab ((cU D).ι ≫ f) p (θW f D M u c L.W'') ζ)
  rw [← heq, h0, nab_nab_eq_zero n f D hD S M u c hloc hcu p L.W'' ζ hζ, add_zero] at h1
  rw [← h1]
  exact map_zero _

variable {M} in
/-- **Local surjectivity on cycles, in degree zero.** Near every point, a `∇`-closed section of
`C^0_M` is the restriction of a `∇`-closed section of `C^0_{M'}`. -/
private theorem exists_cycle_zero (u c : Γ(X, cU' D M)) {M' : Divisor X}
    (hU : cU' D M ≤ cU' D M') {u' c' : Γ(X, cU' D M')}
    (hu : X.presheaf.map (homOfLE hU).op u' = u) (hc : X.presheaf.map (homOfLE hU).op c' = c)
    {W : X.Opens}
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      ((0 : ℕ) : ℤ)).val.obj (op (OO D M W)))
    (hω : Cond n f D hD S M 0 W ω)
    (hcyc : nab ((cU D).ι ≫ f) 0 (θW f D M u c W) ω = 0) {x : X} (hx : x ∈ W)
    (hLD : ∀ W₀ : X.Opens, x ∈ W₀ → Nonempty (LocalData n f D hD S u c hU x W₀)) :
    ∃ (W' : X.Opens) (h : W' ≤ W), x ∈ W' ∧
      ∃ ω' : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
        ((0 : ℕ) : ℤ)).val.obj (op (OO D M' W')),
        Cond n f D hD S M' 0 W' ω' ∧
        nab ((cU D).ι ≫ f) 0 (θW f D M' u' c' W') ω' = 0 ∧
        rO f ((0 : ℕ) : ℤ) h ω = trf f D hU ((0 : ℕ) : ℤ) W' ω' := by
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  obtain ⟨Wx, hWx, hxWx, hrep⟩ := (cond_iff n f D hD S M 0 W ω).mp hω x hx
  obtain ⟨L⟩ := hLD Wx hxWx
  have := L.ne
  have hk : (L.W'' : X.Opens) ≤ W := L.le.trans hWx
  refine ⟨L.W'', hk, L.mem, ?_⟩
  have hrep'' : LocalRep n f D hD S M 0 L.W'' (rO f ((0 : ℕ) : ℤ) hk ω) :=
    localRep_rO n f D hD S hWx L.le hrep
  obtain ⟨y, hy, hyeq⟩ := L.extract 0 _ hrep''
  have h0 : nab ((cU D).ι ≫ f) 0 (θW f D M u c L.W'') (rO f ((0 : ℕ) : ℤ) hk ω) = 0 := by
    rw [← θW_restrict f D M u c hk]
    refine (nab_map _ 0 _ _).symm.trans ?_
    rw [hcyc]
    exact map_zero _
  have hn := L.nabla 0 _ y hyeq
  rw [h0, map_zero] at hn
  have hdy := ((L.hg.isUnit.map (algebraMap _ _)).mul_right_eq_zero).mp hn.symm
  rw [ZeroMemClass.coe_eq_zero] at hdy
  have hy' := L.homotopy0 y hy (by rw [hdy]; exact zero_mem _)
  obtain ⟨ω', hω', hω'eq⟩ := L.realize' 0 y hy'
  have heq : rO f ((0 : ℕ) : ℤ) hk ω = trf f D hU ((0 : ℕ) : ℤ) L.W'' ω' := by
    refine eq_of_ratAt_eq n f D L.O L.hO 0 ?_
    rw [hyeq]
    erw [ratAt_restrict f D (OO_le D hU L.W'') L.O L.hO]
    rw [hω'eq]
  refine ⟨ω', hω', ?_, heq⟩
  refine eq_of_ratAt_eq n f D L.O (L.hO.trans (OO_le D hU L.W'')) (0 + 1) ?_
  rw [map_zero, ← ratAt_restrict f D (OO_le D hU L.W'') L.O L.hO]
  change ratAt f D L.O L.hO _ (trf f D hU ((0 + 1 : ℕ) : ℤ) L.W'' _) = 0
  rw [trf_nab f D hU hu hc 0, ← heq, h0, map_zero]

variable {M} in
set_option maxRecDepth 8000 in
/-- **Local injectivity on cohomology sheaves.** Near every point, a section of `C^{p+1}_{M'}`
whose restriction to `U'_M` is `∇` of a section of `C^p_M` is `∇` of a section of `C^p_{M'}`. -/
private theorem exists_eq_nab_of_trf_eq_nab (u c : Γ(X, cU' D M)) (hloc : LocMon n f D hD S M)
    (hcu : ∀ W : X.Opens, δ ((cU D).ι ≫ f) (OO D M W) (resU W c) *
      δ ((cU D).ι ≫ f) (OO D M W) (resU W u) = 0)
    {M' : Divisor X} (hU : cU' D M ≤ cU' D M') {u' c' : Γ(X, cU' D M')}
    (hu : X.presheaf.map (homOfLE hU).op u' = u) (hc : X.presheaf.map (homOfLE hU).op c' = c)
    (p : ℕ) {W : X.Opens}
    (w : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      ((p + 1 : ℕ) : ℤ)).val.obj (op (OO D M' W)))
    (hw : Cond n f D hD S M' (p + 1) W w)
    (ζ₀ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      (p : ℤ)).val.obj (op (OO D M W)))
    (hζ₀ : Cond n f D hD S M p W ζ₀)
    (hwζ : trf f D hU ((p + 1 : ℕ) : ℤ) W w = nab ((cU D).ι ≫ f) p (θW f D M u c W) ζ₀)
    {x : X} (hx : x ∈ W)
    (hLD : ∀ W₀ : X.Opens, x ∈ W₀ → Nonempty (LocalData n f D hD S u c hU x W₀)) :
    ∃ (W' : X.Opens) (h : W' ≤ W), x ∈ W' ∧
      ∃ v : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
        (p : ℤ)).val.obj (op (OO D M' W')),
        Cond n f D hD S M' p W' v ∧
        rO f (D := D) (M := M') ((p + 1 : ℕ) : ℤ) h w =
          nab ((cU D).ι ≫ f) p (θW f D M' u' c' W') v := by
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  obtain ⟨Wa, hWa, hxa, hrepa⟩ := (cond_iff n f D hD S M p W ζ₀).mp hζ₀ x hx
  obtain ⟨Wb, hWb, hxb, hrepb⟩ := (cond_iff n f D hD S M' (p + 1) W w).mp hw x hx
  obtain ⟨L⟩ := hLD ((Wa : X.Opens) ⊓ Wb) ⟨hxa, hxb⟩
  have := L.ne
  have hka : (L.W'' : X.Opens) ≤ Wa := L.le.trans inf_le_left
  have hkb : (L.W'' : X.Opens) ≤ Wb := L.le.trans inf_le_right
  have hk : (L.W'' : X.Opens) ≤ W := hka.trans hWa
  refine ⟨L.W'', hk, L.mem, ?_⟩
  have hrepa'' : LocalRep n f D hD S M p L.W'' (rO f (p : ℤ) hk ζ₀) :=
    localRep_rO n f D hD S hWa hka hrepa
  have hrepb'' : LocalRep n f D hD S M' (p + 1) L.W''
      (rO f (D := D) (M := M') ((p + 1 : ℕ) : ℤ) hk w) :=
    localRep_rO n f D hD S hWb hkb hrepb
  obtain ⟨y₀, hy₀, hy₀eq⟩ := L.extract p _ hrepa''
  obtain ⟨y', hy', hy'eq⟩ := L.extract' (p + 1) _ hrepb''
  -- `∇ ζ₀ = w` on `W''`
  have hnr : nab ((cU D).ι ≫ f) p (θW f D M u c L.W'') (rO f (p : ℤ) hk ζ₀) =
      trf f D hU ((p + 1 : ℕ) : ℤ) L.W'' (rO f (D := D) (M := M') ((p + 1 : ℕ) : ℤ) hk w) := by
    rw [← θW_restrict f D M u c hk]
    refine (nab_map _ p _ _).symm.trans ?_
    rw [← hwζ]
    exact (piece_map_map ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      ((p + 1 : ℕ) : ℤ)).val (homOfLE (OO_le D hU W)).op
      (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) hk))).op
      (homOfLE ((Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) hk)).trans
        (OO_le D hU W))).op w).trans
      (piece_map_map ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      ((p + 1 : ℕ) : ℤ)).val
      (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M') hk))).op
      (homOfLE (OO_le D hU L.W'')).op
      (homOfLE ((Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) hk)).trans
        (OO_le D hU W))).op w).symm
  have hn := L.nabla p _ y₀ hy₀eq
  rw [hnr] at hn
  erw [ratAt_restrict f D (OO_le D hU L.W'') L.O L.hO] at hn
  rw [hy'eq] at hn
  have hdy := (L.hg.isUnit.map (algebraMap _ _)).mul_left_cancel hn
  have hdy' : deRhamDifferential (A := k) p y₀ + wedgeLeft L.ξ p y₀ ∈
      logLattice L.β L.J' (p + 1) := (Subtype.ext hdy : y' = _) ▸ hy'
  -- conclude from `trf v = ζ₀ - ∇ ζ` (or `= ζ₀`)
  have key : ∀ v : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
        (p : ℤ)).val.obj (op (OO D M' L.W'')),
      nab ((cU D).ι ≫ f) p (θW f D M u c L.W'') (trf f D hU (p : ℤ) L.W'' v) =
        nab ((cU D).ι ≫ f) p (θW f D M u c L.W'') (rO f (p : ℤ) hk ζ₀) →
      rO f (D := D) (M := M') ((p + 1 : ℕ) : ℤ) hk w =
        nab ((cU D).ι ≫ f) p (θW f D M' u' c' L.W'') v := by
    intro v hv
    refine eq_of_ratAt_eq n f D L.O (L.hO.trans (OO_le D hU L.W'')) (p + 1) ?_
    rw [← ratAt_restrict f D (OO_le D hU L.W'') L.O L.hO,
      ← ratAt_restrict f D (OO_le D hU L.W'') L.O L.hO]
    change ratAt f D L.O L.hO _ (trf f D hU _ L.W'' _) =
      ratAt f D L.O L.hO _ (trf f D hU _ L.W'' _)
    rw [trf_nab f D hU hu hc p, hv, hnr]
  cases p with
  | zero =>
    have hy₀' := L.homotopy0 y₀ hy₀ hdy'
    obtain ⟨v, hv, hveq⟩ := L.realize' 0 y₀ hy₀'
    refine ⟨v, hv, key v ?_⟩
    congr 1
    refine eq_of_ratAt_eq n f D L.O L.hO 0 ?_
    erw [ratAt_restrict f D (OO_le D hU L.W'') L.O L.hO]
    rw [hveq, hy₀eq]
  | succ p =>
    obtain ⟨ι, hι, hρ⟩ := L.homotopy p y₀ hy₀ hdy'
    obtain ⟨ζ, hζ, hζeq⟩ := L.realize p ι hι
    obtain ⟨v, hv, hveq⟩ := L.realize' (p + 1) _ hρ
    have hnζ := L.nabla p ζ ι hζeq
    have htv : trf f D hU ((p + 1 : ℕ) : ℤ) L.W'' v = rO f ((p + 1 : ℕ) : ℤ) hk ζ₀ -
        nab ((cU D).ι ≫ f) p (θW f D M u c L.W'') ζ := by
      refine eq_of_ratAt_eq n f D L.O L.hO (p + 1) ?_
      erw [ratAt_restrict f D (OO_le D hU L.W'') L.O L.hO]
      rw [hveq, map_sub, hy₀eq, hnζ, ← mul_sub, Submodule.coe_sub]
    refine ⟨v, hv, key v ?_⟩
    rw [htv, nab_sub, nab_nab_eq_zero n f D hD S M u c hloc hcu p L.W'' ζ hζ, sub_zero]

/-- A non-empty affine open of `U` inside `U ∩ W ∩ U'`, for `W` non-empty. -/
private theorem exists_affine_le_OO {W : X.Opens} (hW : (W : Set X).Nonempty) :
    ∃ O : (cU D).toScheme.affineOpens, Nonempty (O : (cU D).toScheme.Opens) ∧
      (O : (cU D).toScheme.Opens) ≤ OO D M W := by
  have hgW : genericPoint X ∈ W :=
    (genericPoint_spec X).mem_open_set_iff W.isOpen |>.mpr (by rwa [Set.univ_inter])
  have hz : genericPoint (cU D).toScheme ∈ OO D M W := by
    change (cU D).ι (genericPoint (cU D).toScheme) ∈ W ⊓ cU' D M
    rw [genericPoint_eq_of_isOpenImmersion]
    exact ⟨hgW, genericPoint_mem_cU' D M⟩
  obtain ⟨O, hO, hzO, hle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (cU D).toScheme.isBasis_affineOpens hz
  exact ⟨⟨O, hO⟩, ⟨⟨_, hzO⟩⟩, hle⟩

private theorem presheaf_map_le_self {W : X.Opens} (h : W ≤ W) (a : Γ(X, W)) :
    X.presheaf.map (homOfLE h).op a = a := by
  rw [show (homOfLE h).op = 𝟙 (op W) from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
  rfl

variable {M} in
/-- **The local data of the residue homotopy exist near every point.** -/
private theorem nonempty_localData [CharZero k] [CompactSpace X] (u c : Γ(X, cU' D M)) (N : ℕ)
    (hN : 0 < N) (hcc : c * ((N : Γ(X, cU' D M)) * u) = 1) (Bn : Divisor X)
    (ψ : (RationalFunctions X)ˣ) (hψ : (N : ℤ) • M = Bn + principalDivisor ψ)
    (hu : (toRationalFunctionsPresheaf X).app (op (cU' D M)) u = ratRes (cU' D M) ψ)
    (hBn : ∀ E, 0 ≤ Bn E) (hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support) (hMC : M.IsCartier)
    (hSD : ∀ E ∈ S.support, E ∈ D.support) (B : MMP.Mori.PrimeDivisor X) (hBD' : B ∈ D.support)
    (hBS : B ∉ S.support) (hBn0 : Bn B ≠ 0) {M' : Divisor X}
    (hM' : M' = M + Finsupp.single B 1) (hMC' : M'.IsCartier) (hU : cU' D M ≤ cU' D M')
    (x : X) (W₀ : X.Opens) (hx : x ∈ W₀) : Nonempty (LocalData n f D hD S u c hU x W₀) := by
  classical
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  -- a chart and local equations at `x`
  obtain ⟨Wc, Vb, e, t, hxc, hb, r, hr, j, hj, hjD, hDW⟩ := hD.2 x
  obtain ⟨Wm, hxm, φ₀, hφ₀⟩ := hMC x
  obtain ⟨Wm', hxm', φ₀', hφ₀'⟩ := hMC' x
  -- a basic open `W''` of the chart inside everything
  obtain ⟨gW, hgW, hxg⟩ := Wc.2.exists_basicOpen_le
    (V := W₀ ⊓ Wm ⊓ Wm' ⊓ (Wc : X.Opens)) ⟨x, ⟨⟨⟨hx, hxm⟩, hxm'⟩, hxc⟩⟩ hxc
  let W'' : X.affineOpens := ⟨X.basicOpen gW, Wc.2.basicOpen gW⟩
  have hW''c : (W'' : X.Opens) ≤ Wc := X.basicOpen_le gW
  have hW''0 : (W'' : X.Opens) ≤ W₀ := hgW.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have hW''m : (W'' : X.Opens) ≤ Wm := hgW.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have hW''m' : (W'' : X.Opens) ≤ Wm' := hgW.trans (inf_le_left.trans inf_le_right)
  -- the coordinates restricted to `W''`
  set t'' : Fin n → Γ(X, W'') := fun i => X.presheaf.map (homOfLE hW''c).op (t i) with ht''
  have hτ'' : ∀ q, (j q).idealSheaf.ideal W'' = Ideal.span {t'' (Fin.castLE hr q)} := fun q => by
    rw [← (j q).idealSheaf.map_ideal hW''c, (hjD q).2.2, Ideal.map_span, Set.image_singleton]
    rfl
  have hDW'' : D.suppIdeal.ideal W'' = Ideal.span {∏ q, t'' (Fin.castLE hr q)} := by
    rw [← D.suppIdeal.map_ideal hW''c, hDW, Ideal.map_span, Set.image_singleton, map_prod]
    rfl
  -- the non-empty affine `O`
  obtain ⟨O, hOne, hO⟩ := exists_affine_le_OO D M (W := W'') ⟨x, hxg⟩
  have := hOne
  have hne : ∀ {Q : X.Opens}, (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ Q →
      Nonempty ((cU D).ι ⁻¹ᵁ Q) := fun hQ =>
    ⟨⟨_, hQ (Classical.arbitrary (O : (cU D).toScheme.Opens)).2⟩⟩
  have hOW'' : (O : (cU D).toScheme.Opens) ≤ (cU D).ι ⁻¹ᵁ (W'' : X.Opens) :=
    hO.trans (Scheme.Hom.preimage_mono _ inf_le_left)
  have : Nonempty ((cU D).ι ⁻¹ᵁ (W'' : X.Opens)) := hne hOW''
  have : Nonempty ((cU D).ι ⁻¹ᵁ (Wc : X.Opens)) := hne (hOW''.trans
    (Scheme.Hom.preimage_mono _ hW''c))
  have : Nonempty ((cU D).ι ⁻¹ᵁ ((W'' : X.Opens) ⊓ cU' D M)) := hne hO
  have : Nonempty ((cU D).ι ⁻¹ᵁ ((W'' : X.Opens) ⊓ cU' D M')) :=
    hne (hO.trans (Scheme.Hom.preimage_mono _ (inf_le_inf_left _ hU)))
  have : Nonempty (W'' : X.Opens) := ⟨⟨x, hxg⟩⟩
  -- the bases of differentials
  obtain ⟨V, hVa⟩ := Vb
  have hV : V = ⊤ := by
    ext z
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have hz : z = f x := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [hz]
    exact e hxc
  obtain ⟨bW, hbW⟩ := exists_basis_of_chart f hV e t hb
  obtain ⟨b'', hb''⟩ := exists_basis_basicOpen f Wc.2 t bW hbW gW
  obtain ⟨bK, hbK, hrepr⟩ := exists_basis_functionField f (cU D) (W'').2 t'' b'' hb''
  set T : Fin n → (cU D).toScheme.functionField := fun i => gmU (cU D) Wc (t i) with hTdef
  have hT : ∀ i, gmU (cU D) (W'' : X.Opens) (t'' i) = T i := fun i =>
    gmU_restrict (cU D) hW''c (t i)
  -- the coefficient ring `A` of functions on `W''`
  set gm := gmU (cU D) (W'' : X.Opens) with hgm
  set A : Subring (cU D).toScheme.functionField := gm.range with hA
  have hkA : ∀ c : k, algebraMap k (cU D).toScheme.functionField c ∈ A := by
    intro c
    let := MMP.Mori.sectionAlgebra f (W'' : X.Opens)
    let := gm.toAlgebra
    have := isScalarTower_gmU f (cU D) (W'' : X.Opens)
    exact ⟨algebraMap k Γ(X, (W'' : X.Opens)) c,
      (IsScalarTower.algebraMap_apply k Γ(X, (W'' : X.Opens)) _ c).symm⟩
  have hTA : ∀ i, T i ∈ A := fun i => ⟨t'' i, hT i⟩
  have hreg : ∀ y ∈ A, ∀ i, bK.repr (KaehlerDifferential.D k _ y) i ∈ A := by
    rintro _ ⟨a, rfl⟩ i
    exact ⟨_, (hrepr a i).symm⟩
  have hbK' : ∀ i, bK i = KaehlerDifferential.D k _ (T i) := fun i => by rw [hbK, hT]
  have ht : ∀ i, T i ≠ 0 := by
    intro i h
    have := bK.ne_zero i
    rw [hbK', h, map_zero] at this
    exact this rfl
  -- the coefficient group `J` of `I_S`
  set J : AddSubgroup (cU D).toScheme.functionField :=
    (S.suppIdeal.ideal W'').toAddSubgroup.map gm.toAddMonoidHom with hJdef
  have hJA : ∀ a ∈ A, ∀ c ∈ J, a * c ∈ J := by
    rintro _ ⟨a, rfl⟩ _ ⟨c, hc, rfl⟩
    exact ⟨a * c, Ideal.mul_mem_left _ _ hc, map_mul gm a c⟩
  have hSc := suppIdeal_eq_span_prod_of_chart D n f S hSD hb hr (fun i => (hjD i).2.2) hDW
  set P : Finset (Fin r) := Finset.univ.filter (fun q : Fin r => j q ∈ S.support) with hPdef
  have hSW'' : S.suppIdeal.ideal W'' = Ideal.span {∏ q ∈ P, t'' (Fin.castLE hr q)} := by
    rw [← S.suppIdeal.map_ideal hW''c, hSc, Ideal.map_span, Set.image_singleton, map_prod]
    rfl
  set P' : Finset (Fin n) := P.map (Fin.castLEEmb hr) with hP'def
  have hσ : gm (∏ q ∈ P, t'' (Fin.castLE hr q)) = ∏ i ∈ P', T i := by
    rw [map_prod, hP'def, Finset.prod_map]
    exact Finset.prod_congr rfl fun q _ => hT _
  have hJ : ∀ c ∈ J, ∃ a ∈ A, c = (∏ i ∈ P', T i) * a := by
    rintro _ ⟨c, hc, rfl⟩
    change c ∈ S.suppIdeal.ideal W'' at hc
    rw [hSW'', Ideal.mem_span_singleton'] at hc
    obtain ⟨d, rfl⟩ := hc
    exact ⟨gm d, ⟨d, rfl⟩, by
      change gm (d * _) = _
      rw [map_mul, hσ, mul_comm]⟩
  have hJ' : ∀ a ∈ A, (∏ i ∈ P', T i) * a ∈ J := by
    rintro _ ⟨d, rfl⟩
    refine ⟨(∏ q ∈ P, t'' (Fin.castLE hr q)) * d, ?_, ?_⟩
    · change _ ∈ S.suppIdeal.ideal W''
      rw [hSW'']
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · change gm (_ * d) = _
      rw [map_mul, hσ]
  -- the generator of `𝒪_X(-M)` and its factorization
  obtain ⟨v, g₀, hvu, hg₀rat, hg₀div, hg₀gen, hX⟩ := exists_generator_factorization_on D M u Bn N
    ψ hψ hu hBn hBD (W₂ := W'') (fun q => t'' (Fin.castLE hr q)) j hj hτ'' hDW''
    (hφ₀.mono hW''m)
  obtain ⟨g₀', hg₀rat', hg₀div', hg₀gen'⟩ := exists_generator D M' (hφ₀'.mono hW''m')
  -- a local equation `τ` of `B` on `W''`
  obtain ⟨τ, hτB, hτcase⟩ : ∃ τ : Γ(X, (W'' : X.Opens)),
      B.idealSheaf.ideal W'' = Ideal.span {τ} ∧
        ((∃ q : Fin r, j q = B ∧ τ = t'' (Fin.castLE hr q)) ∨ (x ∉ B.support ∧ τ = 1)) := by
    by_cases hxB : x ∈ B.support
    · obtain ⟨q, hq⟩ := exists_eq_of_mem_chart t hr j (fun i => (hjD i).2.2) hDW hBD' hxc hxB
      exact ⟨t'' (Fin.castLE hr q), hq ▸ hτ'' q, Or.inl ⟨q, hq, rfl⟩⟩
    · refine ⟨1, ?_, Or.inr ⟨hxB, rfl⟩⟩
      rw [Ideal.span_singleton_one]
      refine ideal_eq_top_of_disjoint _ W'' fun y hy hyB => hxB ?_
      obtain ⟨q, hq⟩ := exists_eq_of_mem_chart t hr j (fun i => (hjD i).2.2) hDW hBD'
        (hW''c hy) hyB
      exact hq ▸ (hjD q).2.1
  obtain ⟨v', hv'u, hrel⟩ := exists_generator_add_single D M B hM' hU hτB (hφ₀.mono hW''m)
    (hφ₀'.mono hW''m') hg₀rat hg₀rat'
  -- the germs of the generators
  have : Nonempty ((cU D).ι ⁻¹ᵁ cU' D M) := hne (hO.trans (Scheme.Hom.preimage_mono _ inf_le_right))
  set g := gmU (cU D) ((W'' : X.Opens) ⊓ cU' D M) g₀ with hgdef
  set G' := gmU (cU D) ((W'' : X.Opens) ⊓ cU' D M') g₀' with hG'def
  have hG' : G' = gm v' * gm τ * g := by
    have h1 := congrArg (gmU (cU D) ((W'' : X.Opens) ⊓ cU' D M)) hrel
    rw [gmU_restrict, map_mul, gmU_restrict, map_mul] at h1
    exact h1
  set U₀ := gmU (cU D) (cU' D M) u with hU₀
  set V₀ := gm v with hV₀
  have hgN : g ^ N = U₀ * V₀ * ∏ q : Fin r, T (Fin.castLE hr q) ^ (Bn (j q)).toNat := by
    have h1 := congrArg (gmU (cU D) ((W'' : X.Opens) ⊓ cU' D M)) hX
    rw [map_pow, map_mul, gmU_restrict, gmU_restrict, map_mul, map_prod] at h1
    rw [h1, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [map_pow, hT]
  have hNK : (N : (cU D).toScheme.functionField) ≠ 0 := by
    rw [← map_natCast (algebraMap k (cU D).toScheme.functionField)]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hN.ne')
  have hcU : gmU (cU D) (cU' D M) c * ((N : (cU D).toScheme.functionField) * U₀) = 1 := by
    have h1 := congrArg (gmU (cU D) (cU' D M)) hcc
    rwa [map_mul, map_mul, map_natCast, map_one] at h1
  have hU0 : U₀ ≠ 0 := fun h => by rw [h, mul_zero, mul_zero] at hcU; exact zero_ne_one hcU
  have hV0 : V₀ ≠ 0 := (hvu.map gm).ne_zero
  have hg : g ≠ 0 := by
    intro h
    have : g ^ N = 0 := by rw [h, zero_pow hN.ne']
    rw [hgN] at this
    refine (mul_ne_zero (mul_ne_zero hU0 hV0) (Finset.prod_ne_zero_iff.mpr fun q _ =>
      pow_ne_zero _ (ht _))) this
  -- the connection forms `θ'` and `ξ`
  set θ' : Ω[(cU D).toScheme.functionField⁄k] :=
    gmU (cU D) (cU' D M) c • KaehlerDifferential.D k _ U₀ with hθ'def
  set ξ : Ω[(cU D).toScheme.functionField⁄k] := (N : (cU D).toScheme.functionField)⁻¹ •
    (V₀⁻¹ • KaehlerDifferential.D k _ V₀ + ∑ q : Fin r, ((Bn (j q)).toNat : (cU D).toScheme.functionField) •
      (T (Fin.castLE hr q))⁻¹ • KaehlerDifferential.D k _ (T (Fin.castLE hr q))) with hξdef
  have hDg : KaehlerDifferential.D k _ g = g • (θ' + ξ) := by
    rw [D_eq_smul_of_pow_eq hNK hg hU0 hV0 (fun q => ht _) _ hgN]
    congr 2
    rw [hθ'def, smul_smul]
    congr 1
    rw [eq_comm, ← mul_inv]
    exact eq_inv_of_mul_eq_one_left hcU
  have hNA : (N : (cU D).toScheme.functionField)⁻¹ ∈ A := by
    rw [← map_natCast (algebraMap k (cU D).toScheme.functionField), ← map_inv₀]
    exact hkA _
  have hViA : V₀⁻¹ ∈ A := ⟨(hvu.unit⁻¹ : (Γ(X, (W'' : X.Opens)))ˣ).val, by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, hvu.val_inv_mul, map_one]⟩
  obtain ⟨a, ha, hξa, hres⟩ := exists_coeffs_dlog hbK' ht hr A hTA hreg hNA ⟨v, rfl⟩ hViA
    (fun q => (Bn (j q)).toNat)
  have hv'iA : (gm v')⁻¹ ∈ A := ⟨(hv'u.unit⁻¹ : (Γ(X, (W'' : X.Opens)))ˣ).val, by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, hv'u.val_inv_mul, map_one]⟩
  have hv'0 : gm v' ≠ 0 := (hv'u.map gm).ne_zero
  -- the inverses of the local equations on the chart
  have hsu : ∀ q : Fin r, IsUnit (((cU D).ι.app Wc).hom (t (Fin.castLE hr q))) := fun q =>
    B1.isUnit_res_of_ideal_eq D (hjD q).1 (hjD q).2.2
  let s : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (Wc : X.Opens)) := fun q =>
    ((hsu q).unit⁻¹ : (Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (Wc : X.Opens)))ˣ).val
  have hs : ∀ q, s q * ((cU D).ι.app Wc).hom (t (Fin.castLE hr q)) = 1 := fun q =>
    (hsu q).val_inv_mul
  have hjD2 : ∀ q, j q ∈ D.support ∧ (j q).idealSheaf.ideal Wc = Ideal.span {t (Fin.castLE hr q)} :=
    fun q => ⟨(hjD q).1, (hjD q).2.2⟩
  -- the residue data along `B`, when `τ` is a coordinate
  have hres_all : ∀ q : Fin r, j q = B → τ = t'' (Fin.castLE hr q) →
      ∃ i₀ : Fin n, (i₀ : ℕ) < r ∧ gm τ = T i₀ ∧ i₀ ∉ P' ∧
        ∃ lam : k, lam ≠ 0 ∧ ∃ e ∈ A, a i₀ - algebraMap k _ lam = T i₀ * e := by
    intro q hqB hτq
    refine ⟨Fin.castLE hr q, q.2, by rw [hτq, hT], ?_, ((Bn B).toNat : k) / N, ?_, ?_⟩
    · intro h
      obtain ⟨q', hq', hq'eq⟩ := Finset.mem_map.mp h
      have : q' = q := (Fin.castLEEmb hr).injective hq'eq
      subst this
      exact hBS (hqB ▸ (Finset.mem_filter.mp hq').2)
    · have hBnB : 0 < Bn B := lt_of_le_of_ne (hBn B) (Ne.symm hBn0)
      exact div_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr hN.ne')
    · obtain ⟨e, he, h⟩ := hres (Fin.castLE hr q) q.2
      beta_reduce at h
      refine ⟨e, he, ?_⟩
      have hq : (⟨Fin.castLE hr q, q.2⟩ : Fin r) = q := Fin.ext rfl
      rw [hq, hqB] at h
      rw [map_div₀, map_natCast, map_natCast, div_eq_inv_mul]
      exact h
  -- the homotopy conditions along `B`
  obtain ⟨hHom, hHom0⟩ : HomotopyConds (logBasis (k := k) T r) J
      (J.map (AddMonoidHom.mulLeft (gm τ))) ξ := by
    rcases hτcase with ⟨q, hqB, hτq⟩ | ⟨-, hτ1⟩
    · obtain ⟨i₀, hi₀, hgτ, hi₀P', lam, hlam, hres'⟩ := hres_all q hqB hτq
      exact residue_homotopy_of_chart hbK' ht hi₀ A hkA hreg P' hi₀P' J hJA hJ hJ' a ha lam hlam
        hres' (hξdef.trans hξa) hgτ
    · exact homotopyConds_of_eq_one _ J ξ (by rw [hτ1, map_one])
  refine ⟨{
    W'' := W''
    mem := hxg
    le := hW''0
    O := O
    ne := hOne
    hO := hO
    g := g
    hg := hg
    ξ := ξ
    β := logBasis (k := k) T r
    J := J
    J' := J.map (AddMonoidHom.mulLeft (gm τ))
    extract := ?_
    extract' := ?_
    realize := ?_
    realize' := ?_
    nabla := ?_
    homotopy := hHom
    homotopy0 := hHom0 }⟩
  · intro p ω hω
    obtain ⟨m, gg, η, hgg, hη, he⟩ := hω
    choose hh hhe using fun i => hg₀gen W'' le_rfl (gg i) (hgg i)
    obtain ⟨y, hy, hyeq⟩ := ratTotal_sum_mem_logLattice n f D hD hxc hb hr hj hjD hDW
      (V' := cU' D M) (W' := W'') (W'' := W'') hW''c le_rfl S.suppIdeal gg η hη g₀ hh
      (fun i => by rw [presheaf_map_le_self, hhe i, presheaf_map_le_self]) O hO
    refine ⟨y, hy, ?_⟩
    rw [ratAt_apply, he]
    exact hyeq
  · intro p ω hω
    obtain ⟨m, gg, η, hgg, hη, he⟩ := hω
    choose hh hhe using fun i => hg₀gen' W'' le_rfl (gg i) (hgg i)
    obtain ⟨y, hy, hyeq⟩ := ratTotal_sum_mem_logLattice n f D hD hxc hb hr hj hjD hDW
      (V' := cU' D M') (W' := W'') (W'' := W'') hW''c le_rfl S.suppIdeal gg η hη g₀' hh
      (fun i => by rw [presheaf_map_le_self, hhe i, presheaf_map_le_self]) O
      (hO.trans (OO_le D hU W''))
    refine ⟨gm τ • (gm v' • y), smul_mem_logLattice_map (gm τ)
      (smul_mem_logLattice (fun c hc => hJA _ ⟨v', rfl⟩ c hc) hy), ?_⟩
    rw [ratAt_apply, he]
    refine hyeq.trans ?_
    rw [← hG'def, hG']
    exact algebraMap_mul_coe_smul_smul _ _ _ y
  · intro p y hy
    exact exists_cond_of_mem_logLattice n f D hD S M hr hjD2 hs hW''c hg₀div O hO hy
  · intro p y hy
    obtain ⟨y₁, hy₁, rfl⟩ := exists_smul_of_mem_logLattice_map (gm τ) hy
    obtain ⟨ζ, hζ, hζeq⟩ := exists_cond_of_mem_logLattice n f D hD S M' hr hjD2 hs hW''c hg₀div' O
      (hO.trans (OO_le D hU W'')) (smul_mem_logLattice (a := (gm v')⁻¹)
        (fun c hc => hJA _ hv'iA c hc) hy₁)
    refine ⟨ζ, hζ, hζeq.trans ?_⟩
    rw [← hG'def, hG']
    exact algebraMap_mul_coe_inv_smul hv'0 _ _ y₁
  · intro p ζ y hζ
    exact ratAt_nab f D O hO p _ ζ θ' ξ g y (ratAt_θW f D M u c W'' O hO) hζ hDg

variable {M} in
/-- **The inclusion `C^•_{M'} ⟶ C^•_M` is a quasi-isomorphism** when the local data of the
residue homotopy exist near every point. -/
private theorem isIso_homologyMap_cCxIncl {M' : Divisor X} (hU : cU' D M ≤ cU' D M')
    (hMM : M ≤ M') {u' c' : Γ(X, cU' D M')} {u c : Γ(X, cU' D M)}
    (hu : X.presheaf.map (homOfLE hU).op u' = u) (hc : X.presheaf.map (homOfLE hU).op c' = c)
    (hst' : NabStable n f D hD S M' u' c') (hloc' : LocMon n f D hD S M')
    (hcu' : ∀ W : X.Opens, δ ((cU D).ι ≫ f) (OO D M' W) (resU W c') *
      δ ((cU D).ι ≫ f) (OO D M' W) (resU W u') = 0)
    (hst : NabStable n f D hD S M u c) (hloc : LocMon n f D hD S M)
    (hcu : ∀ W : X.Opens, δ ((cU D).ι ≫ f) (OO D M W) (resU W c) *
      δ ((cU D).ι ≫ f) (OO D M W) (resU W u) = 0)
    (hLD : ∀ (x : X) (W₀ : X.Opens), x ∈ W₀ → Nonempty (LocalData n f D hD S u c hU x W₀))
    (q : ℕ) : IsIso (HomologicalComplex.homologyMap
      (cCxIncl n f D hD S hU hMM hu hc hst' hloc' hcu' hst hloc hcu) q) := by
  let := MMP.Mori.functionFieldAlgebra ((cU D).ι ≫ f)
  refine isIso_homologyMap_of_local _ q ?_ ?_
  · intro W z hz x hx
    rw [cCx_d] at hz
    have h1 : nabA f D M u c q W z.1 = 0 := congrArg Subtype.val hz
    have hzc : nab ((cU D).ι ≫ f) q (θW f D M u c W) (tr f D M (q : ℤ) W z.1) = 0 :=
      (tr_nabA f D M u c q W z.1).symm.trans ((congrArg (tr f D M _ W) h1).trans (map_zero _))
    cases q with
    | zero =>
      obtain ⟨W', h, hx', ω', hω', hcyc', heq⟩ := exists_cycle_zero n f D hD S u c hU hu hc
        (tr f D M ((0 : ℕ) : ℤ) W z.1) z.2 hzc hx (hLD x)
      refine ⟨W', h, hx', ⟨trInv f D M' ((0 : ℕ) : ℤ) W' ω',
        (congrArg (Cond n f D hD S M' 0 W') (tr_trInv f D M' _ W' ω')).mpr hω'⟩, 0, ?_, ?_⟩
      · rw [cCx_d]
        refine Subtype.ext (tr_injective f D M' _ W' ?_)
        exact (tr_nabA f D M' u' c' 0 W' _).trans ((congrArg _ (tr_trInv f D M' _ W' ω')).trans
          (hcyc'.trans (map_zero _).symm))
      · rw [map_zero, add_zero]
        refine Subtype.ext (tr_injective f D M _ W' ?_)
        exact (tr_restrict f D M _ h z.1).trans (heq.trans ((congrArg (trf f D hU _ W')
          (tr_trInv f D M' _ W' ω')).symm.trans (tr_ambTr f D hU _ W' _).symm))
    | succ p =>
      rw [CochainComplex.prev_nat_succ]
      obtain ⟨W', h, hx', ω', hω', hcyc', ζ, hζ, heq⟩ := exists_cycle_add_nab n f D hD S u c hloc
        hcu hU hu hc p (tr f D M ((p + 1 : ℕ) : ℤ) W z.1) z.2 hzc hx (hLD x)
      refine ⟨W', h, hx', ⟨trInv f D M' ((p + 1 : ℕ) : ℤ) W' ω',
        (congrArg (Cond n f D hD S M' (p + 1) W') (tr_trInv f D M' _ W' ω')).mpr hω'⟩,
        ⟨trInv f D M (p : ℤ) W' ζ,
          (congrArg (Cond n f D hD S M p W') (tr_trInv f D M _ W' ζ)).mpr hζ⟩, ?_, ?_⟩
      · rw [cCx_d]
        refine Subtype.ext (tr_injective f D M' _ W' ?_)
        exact (tr_nabA f D M' u' c' (p + 1) W' _).trans ((congrArg _
          (tr_trInv f D M' _ W' ω')).trans (hcyc'.trans (map_zero _).symm))
      · rw [cCx_d]
        refine Subtype.ext (tr_injective f D M _ W' ?_)
        refine (tr_restrict f D M _ h z.1).trans (heq.trans (Eq.trans ?_
          (tr_add f D M _ (ambTr f D hU _ W' (trInv f D M' _ W' ω'))
            (nabA f D M u c p W' (trInv f D M _ W' ζ))).symm))
        exact congrArg₂ (· + ·) ((congrArg (trf f D hU _ W')
          (tr_trInv f D M' _ W' ω')).symm.trans (tr_ambTr f D hU _ W' _).symm)
          ((congrArg _ (tr_trInv f D M _ W' ζ)).symm.trans (tr_nabA f D M u c p W' _).symm)
  · intro W w y hw hφ x hx
    cases q with
    | zero =>
      have hY : (cCx n f D hD S M u c hst hloc hcu).d ((ComplexShape.up ℕ).prev 0) 0 = 0 :=
        HomologicalComplex.shape _ _ _ (by simp)
      have hX : (cCx n f D hD S M' u' c' hst' hloc' hcu').d ((ComplexShape.up ℕ).prev 0) 0 = 0 :=
        HomologicalComplex.shape _ _ _ (by simp)
      rw [hY] at hφ
      have h0 : ambTr f D hU ((0 : ℕ) : ℤ) W w.1 = 0 := congrArg Subtype.val hφ
      obtain ⟨L⟩ := hLD x W hx
      have := L.ne
      refine ⟨L.W'', L.le, L.mem, 0, ?_⟩
      rw [hX]
      refine Subtype.ext (tr_injective f D M' _ L.W'' ?_)
      refine (tr_restrict f D M' _ L.le w.1).trans (Eq.trans ?_ (map_zero _).symm)
      have e1 : trf f D hU ((0 : ℕ) : ℤ) W (tr f D M' ((0 : ℕ) : ℤ) W w.1) = 0 :=
        (tr_ambTr f D hU _ W w.1).symm.trans ((congrArg (tr f D M _ W) h0).trans (map_zero _))
      have e2 : pr f D (OO_le D hU L.W'') ((0 : ℕ) : ℤ) (((Scheme.Hom.relativeDifferentialFormsAlgebra
          ((cU D).ι ≫ f)).piece ((0 : ℕ) : ℤ)).val.map (homOfLE (Scheme.Hom.preimage_mono _
            (inf_le_inf_right (cU' D M') L.le))).op (tr f D M' ((0 : ℕ) : ℤ) W w.1)) =
          ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
            ((0 : ℕ) : ℤ)).val.map (homOfLE (Scheme.Hom.preimage_mono _
              (inf_le_inf_right (cU' D M) L.le))).op
            (trf f D hU ((0 : ℕ) : ℤ) W (tr f D M' ((0 : ℕ) : ℤ) W w.1)) :=
        (piece_map_map ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
          ((0 : ℕ) : ℤ)).val
          (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M') L.le))).op
          (homOfLE (OO_le D hU L.W'')).op
          (homOfLE ((Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) L.le)).trans
            (OO_le D hU W))).op _).trans
        (piece_map_map ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
          ((0 : ℕ) : ℤ)).val (homOfLE (OO_le D hU W)).op
          (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) L.le))).op
          (homOfLE ((Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) L.le)).trans
            (OO_le D hU W))).op _).symm
      refine eq_of_ratAt_eq n f D L.O (L.hO.trans (OO_le D hU L.W'')) 0 ?_
      refine (ratAt_restrict f D (OO_le D hU L.W'') L.O L.hO ((0 : ℕ) : ℤ) _).symm.trans ?_
      rw [e2, e1]
      simp only [map_zero]
      exact map_zero _
    | succ p =>
      revert y
      rw [CochainComplex.prev_nat_succ]
      intro y hφ
      rw [cCx_d] at hφ
      have hwy : ambTr f D hU ((p + 1 : ℕ) : ℤ) W w.1 = nabA f D M u c p W y.1 :=
        congrArg Subtype.val hφ
      have hwζ : trf f D hU ((p + 1 : ℕ) : ℤ) W (tr f D M' ((p + 1 : ℕ) : ℤ) W w.1) =
          nab ((cU D).ι ≫ f) p (θW f D M u c W) (tr f D M (p : ℤ) W y.1) :=
        (tr_ambTr f D hU _ W w.1).symm.trans ((congrArg (tr f D M _ W) hwy).trans
          (tr_nabA f D M u c p W y.1))
      obtain ⟨W', h, hx', v, hv, heq⟩ := exists_eq_nab_of_trf_eq_nab n f D hD S u c hloc hcu hU hu
        hc p (tr f D M' ((p + 1 : ℕ) : ℤ) W w.1) w.2 (tr f D M (p : ℤ) W y.1) y.2 hwζ hx (hLD x)
      refine ⟨W', h, hx', ⟨trInv f D M' (p : ℤ) W' v,
        (congrArg (Cond n f D hD S M' p W') (tr_trInv f D M' _ W' v)).mpr hv⟩, ?_⟩
      rw [cCx_d]
      refine Subtype.ext (tr_injective f D M' _ W' ?_)
      exact (tr_restrict f D M' _ h w.1).trans (heq.trans ((congrArg _
        (tr_trInv f D M' _ W' v)).symm.trans (tr_nabA f D M' u' c' p W' _).symm))

end LocalHomotopy

section Orders

open MMP.FourfoldProofs.FractionalLogComplexProof

variable {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]

/-- The germ of a function at the generic point of the component of a prime divisor `E` is the
image of its germ in the local ring `𝒪_{X,E}`. -/
private theorem germ_component_eq {E : MMP.Mori.PrimeDivisor X} {W : X.Opens}
    (hE : (E.support ∩ W).Nonempty) (c : Γ(X, W)) :
    (X.presheaf.germ W (componentGenericPoint X E.component)
      (E.componentGenericPoint_mem_of_nonempty hE)).hom c =
      E.toComponent.hom ((X.presheaf.germ W E.genericPoint
        (E.genericPoint_mem_of_nonempty hE)).hom c) :=
  (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf _ E.specializes_genericPoint c).symm

/-- A regular function has order `≥ 0` along every prime divisor. -/
private theorem ordGE_zero_germ {E : MMP.Mori.PrimeDivisor X} {W : X.Opens}
    (hE : (E.support ∩ W).Nonempty) (c : Γ(X, W)) :
    E.OrdGE 0 ((X.presheaf.germ W (componentGenericPoint X E.component)
      (E.componentGenericPoint_mem_of_nonempty hE)).hom c) := by
  rw [germ_component_eq hE]
  by_cases h : (X.presheaf.germ W E.genericPoint (E.genericPoint_mem_of_nonempty hE)).hom c = 0
  · left
    rw [h, map_zero]
  · right
    rw [WithZero.exp_zero]
    exact E.one_le_valuation_toComponent h

/-- A regular function vanishing at the generic point of `E` has order `≥ 1` along `E`. -/
private theorem ordGE_one_germ_of_notMem {E : MMP.Mori.PrimeDivisor X} {W : X.Opens}
    (hE : (E.support ∩ W).Nonempty) (c : Γ(X, W)) (h : E.genericPoint ∉ X.basicOpen c) :
    E.OrdGE 1 ((X.presheaf.germ W (componentGenericPoint X E.component)
      (E.componentGenericPoint_mem_of_nonempty hE)).hom c) := by
  rw [germ_component_eq hE]
  refine E.ordGE_one_toComponent ((IsLocalRing.mem_maximalIdeal _).mpr fun hu => h ?_)
  exact (X.mem_basicOpen c _ (E.genericPoint_mem_of_nonempty hE)).mpr hu

/-- A regular function of order `≥ 1` along `E` vanishes at the generic point of `E`. -/
private theorem notMem_basicOpen_of_ordGE_one {E : MMP.Mori.PrimeDivisor X} {W : X.Opens}
    (hE : (E.support ∩ W).Nonempty) (c : Γ(X, W))
    (h : E.OrdGE 1 ((X.presheaf.germ W (componentGenericPoint X E.component)
      (E.componentGenericPoint_mem_of_nonempty hE)).hom c)) :
    E.genericPoint ∉ X.basicOpen c := by
  intro hb
  have hu : IsUnit ((X.presheaf.germ W E.genericPoint (E.genericPoint_mem_of_nonempty hE)).hom c) :=
    (X.mem_basicOpen c _ (E.genericPoint_mem_of_nonempty hE)).mp hb
  rw [germ_component_eq hE] at h
  rcases h with h | h
  · haveI : Nontrivial (X.presheaf.stalk (componentGenericPoint X E.component)) :=
      (MMP.Mori.RationalFunctions.isField_stalk X E.component).toField.toNontrivial
    exact (hu.map E.toComponent.hom).ne_zero h
  · rw [E.valuation_toComponent_of_isUnit hu, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega

/-- **Sections of the ideal of a reduced divisor are sections of `𝒪_X(-S)`.** -/
private theorem mem_divisorialSubmodule_neg_of_mem_suppIdeal {S : Divisor X} (hS0 : 0 ≤ S)
    (hS1 : ∀ E, S E ≤ 1) {W : X.affineOpens} {c : Γ(X, W)} (hc : c ∈ S.suppIdeal.ideal W) :
    (toRationalFunctionsPresheaf X).app (op (W : X.Opens)) c ∈
      (-S).divisorialSubmodule (W : X.Opens) := by
  intro E hE
  rw [DivisorWithCoeffs.coeff_neg, neg_neg]
  change E.OrdGE _ ((X.presheaf.germ (W : X.Opens) (componentGenericPoint X E.component)
      (E.componentGenericPoint_mem_of_nonempty hE)).hom c)
  by_cases hES : E ∈ S.support
  · have h1 : S.coeff E = 1 := by
      rw [DivisorWithCoeffs.coeff_apply]
      have := Finsupp.mem_support_iff.mp hES
      have := hS0 E
      have := hS1 E
      simp only [Finsupp.coe_zero, Pi.zero_apply] at *
      omega
    rw [h1]
    refine ordGE_one_germ_of_notMem hE c ?_
    have hcE : c ∈ E.idealSheaf.ideal W := by
      rw [MMP.Intersection.suppIdeal_eq_finsetInf, finsetInf_ideal] at hc
      exact (Finset.inf_le (f := fun E => E.idealSheaf.ideal W) hES) hc
    exact (E.mem_ideal_idealSheaf_iff W c).mp hcE (E.genericPoint_mem_of_nonempty hE)
  · have h0 : S.coeff E = 0 := by
      rw [DivisorWithCoeffs.coeff_apply]
      exact Finsupp.notMem_support_iff.mp hES
    rw [h0]
    exact ordGE_zero_germ hE c

/-- A regular function of order `≥ 1` along every component of `S` is a section of its ideal. -/
private theorem mem_suppIdeal_of_ordGE {S : Divisor X} {W : X.affineOpens} {c : Γ(X, W)}
    (h : ∀ E ∈ S.support, ∀ hE : (E.support ∩ (W : X.Opens)).Nonempty,
      E.OrdGE 1 ((X.presheaf.germ (W : X.Opens) (componentGenericPoint X E.component)
        (E.componentGenericPoint_mem_of_nonempty hE)).hom c)) :
    c ∈ S.suppIdeal.ideal W := by
  rw [MMP.Intersection.suppIdeal_eq_finsetInf, finsetInf_ideal, ← Ideal.span_singleton_le_iff_mem]
  refine Finset.le_inf fun E hES => (Ideal.span_singleton_le_iff_mem _).mpr ?_
  refine (E.mem_ideal_idealSheaf_iff W c).mpr fun hη => ?_
  have hE : (E.support ∩ (W : X.Opens)).Nonempty := ⟨E.genericPoint, by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl, hη⟩
  exact notMem_basicOpen_of_ordGE_one hE c (h E hES hE)

end Orders

section DegreeZero

open MMP.FourfoldProofs.FractionalLogComplexProof

variable (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V]
  (D : Divisor V) (hD : D.IsRelativeSNC n π) (M : Divisor V) (N : ℕ) (u : Γ(V, cU' D M))
  {K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
  {F : ℕ → V.Modules}
  {e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p)}
  {ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W))}

variable {n π D hD M N u} in
/-- **The rational function of a section of `C^0` is a section of `𝒪_V(-M-S)`.** Locally the
section is `∑ gᵢ cᵢ` with `gᵢ` sections of `𝒪_V(-M)` and `cᵢ` sections of the ideal of the
reduced divisor `S`, that is of `𝒪_V(-S)`. -/
private theorem DegreeZeroRep.mem_neg_add {S : Divisor V} (hK : IsCModel n π D hD S M N u K F e ι)
    (hS0 : 0 ≤ S) (hS1 : ∀ E, S E ≤ 1) {W : V.Opens} {x : (F 0).val.obj (op W)}
    {a : ToType ((rationalFunctionsPresheaf V).obj (op W))}
    (hx : MMP.LcBpf.DegreeZeroRep ι W x a) : a ∈ (-(M + S)).divisorialSubmodule W := by
  classical
  obtain ⟨g, hga, hgx⟩ := hx
  have hω := (MMP.LcBpf.isCModel_range_iff_cond hK W _).1 ⟨x, rfl⟩
  intro E hE
  obtain ⟨y, hyE, hyW⟩ := id hE
  obtain ⟨W₁, h₁, hy₁, m, gs, η, hgs, hη, he⟩ := hω y hyW
  choose W'' hle hy'' c hc hce using fun i =>
    B1.exists_res_of_mem_relativeLogForms_zero π D n hD S.suppIdeal (hη i) hy₁
  obtain ⟨W', hy', hW'₀, hW''⟩ := exists_affine_forall Finset.univ
    (fun i (Z : V.Opens) => Z ≤ W'' i) (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun i _ => ⟨W'' i, hy'' i, le_rfl⟩) (W₁ : V.Opens) hy₁
  have k₁ : (W' : V.Opens) ≤ W₁ := hW'₀
  have k'' : ∀ i, (W' : V.Opens) ≤ W'' i := fun i => hW'' i (Finset.mem_univ i)
  have he₃ := (congrArg ((TB ((cU D).ι ≫ π)).incl ((0 : ℕ) : ℤ))
    (rO_rO π (D := D) (M := M) ((0 : ℕ) : ℤ) h₁ k₁ (ι 0 W x))).symm.trans
      (sum_rep_restrict π D M k₁ gs η he)
  have hi : ∀ i, (TB ((cU D).ι ≫ π)).incl ((0 : ℕ) : ℤ)
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece
        ((0 : ℕ) : ℤ)).val.map (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
          (inf_le_left.trans k₁))).op (η i)) =
      sm ((cU D).ι ≫ π) (OO D M W') (resO D M W' (V.presheaf.map (homOfLE (k'' i)).op (c i))) := by
    intro i
    have hψ : (W' : V.Opens) ⊓ cU' D M ≤ W'' i := inf_le_left.trans (k'' i)
    have e1 := congrArg ((TB ((cU D).ι ≫ π)).incl ((0 : ℕ) : ℤ))
      (piece_map_map _ ((TopologicalSpace.Opens.map (cU D).ι.base).map (homOfLE (hle i))).op
        (homOfLE (Scheme.Hom.preimage_mono (cU D).ι hψ)).op
        (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left.trans k₁))).op (η i))
    have e2 := incl_map π D (homOfLE (Scheme.Hom.preimage_mono (cU D).ι hψ)).op ((0 : ℕ) : ℤ)
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece
        ((0 : ℕ) : ℤ)).val.map ((TopologicalSpace.Opens.map (cU D).ι.base).map (homOfLE (hle i))).op (η i))
    refine (e1.symm.trans e2).trans ?_
    refine (congrArg _ (hce i)).trans ?_
    refine (totalRestrict_sm _ _).trans ?_
    exact congrArg _ ((G1.app_restrict hψ (c i)).trans
      (congrArg _ (presheaf_map_map _ _ _ _).symm))
  let G : Γ(V, (W' : V.Opens) ⊓ cU' D M) := ∑ i, V.presheaf.map
    (homOfLE (inf_le_inf_right _ k₁)).op (gs i) *
      V.presheaf.map (homOfLE inf_le_left).op (V.presheaf.map (homOfLE (k'' i)).op (c i))
  have heq : V.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) (k₁.trans h₁))).op g = G := by
    apply (MMP.LcBpf.ι_app_bijective (cU D) _
      (inf_le_right.trans (MMP.LcBpf.cU'_le_cU D M))).1
    apply MMP.LcBpf.sm_injective ((cU D).ι ≫ π) (OO D M W')
    have l1 : (TB ((cU D).ι ≫ π)).incl ((0 : ℕ) : ℤ)
        (rO π (D := D) (M := M) ((0 : ℕ) : ℤ) (k₁.trans h₁) (ι 0 W x)) =
        sm ((cU D).ι ≫ π) (OO D M W') ((cU D).ι.app ((W' : V.Opens) ⊓ cU' D M)
          (V.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) (k₁.trans h₁))).op g)) := by
      refine (incl_map π D _ _ _).trans ?_
      rw [hgx]
      refine (totalRestrict_sm _ _).trans ?_
      exact congrArg _ (G1.app_restrict (inf_le_inf_right (cU' D M) (k₁.trans h₁)) g)
    refine l1.symm.trans (he₃.trans ?_)
    refine (Finset.sum_congr rfl fun i _ => by rw [hi i]).trans ?_
    change ∑ i, sm ((cU D).ι ≫ π) (OO D M W') _ * _ = _
    simp only [← map_mul, ← map_sum]
    refine congrArg _ ?_
    simp only [G, map_sum, map_mul]
  -- the rational function on `W'`
  choose a' ha' hea' using fun i => DivCond.restrict D M k₁ (hgs i)
  have hb : (∑ i, a' i * (toRationalFunctionsPresheaf V).app (op (W' : V.Opens))
      (V.presheaf.map (homOfLE (k'' i)).op (c i))) ∈ (-(M + S)).divisorialSubmodule W' := by
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 := (ha' i).mul (mem_divisorialSubmodule_neg_of_mem_suppIdeal hS0 hS1
      (W := W') (S.suppIdeal.map_ideal (k'' i) ▸ Ideal.mem_map_of_mem _ (hc i)))
    rwa [← neg_add] at h1
  have hrestr : (rationalFunctionsPresheaf V).map (homOfLE (k₁.trans h₁)).op a =
      ∑ i, a' i * (toRationalFunctionsPresheaf V).app (op (W' : V.Opens))
        (V.presheaf.map (homOfLE (k'' i)).op (c i)) := by
    apply MMP.LcBpf.rationalFunctionsPresheaf_map_inf_injective
      (MMP.LcBpf.componentGenericPoint_mem_cU' D M)
    have r1 : (rationalFunctionsPresheaf V).map (homOfLE inf_le_left).op
        ((rationalFunctionsPresheaf V).map (homOfLE (k₁.trans h₁)).op a) =
        (rationalFunctionsPresheaf V).map (homOfLE (inf_le_inf_right (cU' D M) (k₁.trans h₁))).op
          ((rationalFunctionsPresheaf V).map (homOfLE inf_le_left).op a) := rfl
    rw [r1, hga, ← toRationalFunctionsPresheaf_app_map, heq]
    simp only [G, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [toRationalFunctionsPresheaf_app_map (homOfLE inf_le_left), ← hea' i]
  have hE' : (E.support ∩ (W' : V.Opens)).Nonempty := ⟨y, hyE, hy'⟩
  have key := (hrestr ▸ hb) E hE'
  exact key

variable {n π D hD M N u} in
/-- **Every section of `𝒪_V(-M-S)` comes from a section of `C^0`.** Near a point, a section `a`
of `𝒪_V(-M-S)` is `g₀ h` with `g₀` a local generator of `𝒪_V(-M)` and `h` a section of the ideal
of `S`. -/
private theorem DegreeZeroRep.surjective_of_mem [IsIntegral V] [CompactSpace V] [Nonempty (cU D)]
    {S : Divisor V} (hK : IsCModel n π D hD S M N u K F e ι) (hS0 : 0 ≤ S)
    (hSD : ∀ E ∈ S.support, E ∈ D.support) {W : V.Opens}
    {a : ToType ((rationalFunctionsPresheaf V).obj (op W))}
    (ha : a ∈ (-(M + S)).divisorialSubmodule W) : ∃ x, MMP.LcBpf.DegreeZeroRep ι W x a := by
  classical
  have : Smooth π := SmoothOfRelativeDimension.smooth n π
  have hsm : MMP.Mori.IsSmoothScheme π :=
    (MMP.Mori.isSmoothScheme_iff π).2 (SmoothOfRelativeDimension.smooth n π)
  have hMC : M.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm M
  -- the function `g` on `W ∩ U'`
  have hdiv : (0 : Divisor V).IsDivisorialSection (W ⊓ cU' D M)
      ((rationalFunctionsPresheaf V).map (homOfLE inf_le_left).op a) := by
    intro E hE
    have h1 := (Divisor.IsDivisorialSection.map (homOfLE inf_le_left) ha) E hE
    have hM0 : M E = 0 := coeff_eq_zero_of_meets
      (inf_le_right.trans (show cU' D M ≤ M.supp.compl from fun x hx hxM => hx (Or.inr hxM))) hE
    have hS0' : S E = 0 := by
      by_contra h
      obtain ⟨y, hyE, hyU⟩ := hE
      exact hyU.2 (Or.inl (MMP.Mori.DivisorWithCoeffs.support_subset_supp
        (Finsupp.mem_support_iff.mp (hSD E (Finsupp.mem_support_iff.mpr h))) hyE))
    have h2 : (-(M + S)).coeff E = (0 : Divisor V).coeff E := by
      rw [DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_zero,
        DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, hM0, hS0']
      rfl
    rw [h2] at h1
    exact h1
  obtain ⟨g, hg⟩ := hdiv.exists_eq
  let ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece
      ((0 : ℕ) : ℤ)).val.obj (op (OO D M W)) :=
    (show (Stacks.RingedSpace.structureRingSheaf (cU D).toScheme.toRingedSpace).obj.obj
      (op (OO D M W)) from (cU D).ι.app (W ⊓ cU' D M) g) •
      (TB ((cU D).ι ≫ π)).one.eval (op (OO D M W))
  have hω : (TB ((cU D).ι ≫ π)).incl ((0 : ℕ) : ℤ) ω =
      sm ((cU D).ι ≫ π) (OO D M W) ((cU D).ι.app (W ⊓ cU' D M) g) :=
    (MMP.LcBpf.sm_eq_incl_smul_one _ _ _).symm
  have hcond : Cond n π D hD S M 0 W ω := by
    intro y hy
    obtain ⟨Wm, hym, φ₀, hφ₀⟩ := hMC y
    obtain ⟨W', hyW', hle⟩ := G1.exists_affineOpens_le (X := V) (show y ∈ W ⊓ Wm from ⟨hy, hym⟩)
    have hW'W : (W' : V.Opens) ≤ W := hle.trans inf_le_left
    have hφ₀' : M.IsLocalEquation W' φ₀ := hφ₀.mono (hle.trans inf_le_right)
    obtain ⟨g₀, hg₀rat, hg₀div, -⟩ := exists_generator D M hφ₀'
    -- `h = a / φ₀`
    have hinv : M.IsDivisorialSection W' (ratRes (W' : V.Opens) ↑φ₀⁻¹) := by
      intro E hE
      refine Or.inr (le_of_eq ?_)
      change WithZero.exp (-M.coeff E) = E.valuation ((↑φ₀⁻¹ : RationalFunctions V) E.component)
      rw [E.valuation_component, MMP.Mori.PrimeDivisor.ord_inv, ← hφ₀' E hE]
    have hdivS : (-S).IsDivisorialSection W'
        ((rationalFunctionsPresheaf V).map (homOfLE hW'W).op a * ratRes (W' : V.Opens) ↑φ₀⁻¹) := by
      have := (Divisor.IsDivisorialSection.map (homOfLE hW'W) ha).mul hinv
      rwa [show -(M + S) + M = -S by abel] at this
    obtain ⟨h, hh⟩ := (hdivS.mono (neg_nonpos.mpr hS0)).exists_eq
    have hhS : h ∈ S.suppIdeal.ideal W' := by
      refine mem_suppIdeal_of_ordGE fun E hES hE => ?_
      have h1 := hdivS E hE
      rw [DivisorWithCoeffs.coeff_neg, neg_neg] at h1
      have h1' : (1 : ℤ) ≤ S.coeff E := by
        rw [DivisorWithCoeffs.coeff_apply]
        have := Finsupp.mem_support_iff.mp hES
        have := hS0 E
        simp only [Finsupp.coe_zero, Pi.zero_apply] at *
        omega
      have h2 := h1.mono h1'
      rw [← hh] at h2
      exact h2
    -- the representation
    refine ⟨W', hW'W, hyW', 1, fun _ => g₀, fun _ => fnForm π D h, fun _ => hg₀div,
      fun _ => monoForm_mem n π D hD (fun _ => 0)
        (fun _ => G1.zero_mem_relativeLogForms n π D hD _ _ _) S.suppIdeal hhS 0 Fin.elim0, ?_⟩
    rw [Fin.sum_univ_one]
    have hgg : V.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) hW'W)).op g =
        V.presheaf.map (homOfLE inf_le_left).op h * g₀ := by
      apply toRationalFunctionsPresheaf_app_injective
      rw [map_mul, toRationalFunctionsPresheaf_app_map, hg, hg₀rat,
        toRationalFunctionsPresheaf_app_map, hh]
      funext Z
      change a ⟨Z.1, hW'W Z.2.1⟩ = (a ⟨Z.1, hW'W Z.2.1⟩ * (↑φ₀⁻¹ : RationalFunctions V) Z.1) *
        (φ₀ : RationalFunctions V) Z.1
      rw [mul_assoc, ← Pi.mul_apply (↑φ₀⁻¹ : RationalFunctions V), Units.inv_mul, Pi.one_apply,
        mul_one]
    refine (MMP.LcBpf.incl_rO_of_eq π D M hW'W hω).trans ?_
    rw [hgg, map_mul, map_mul, sm_comm]
    exact congrArg (sm ((cU D).ι ≫ π) _ (((cU D).ι.app ((W' : V.Opens) ⊓ cU' D M)).hom g₀) * ·)
      (MMP.LcBpf.incl_map_eq_sm π D inf_le_left (incl_fnForm π D h)).symm
  obtain ⟨x, hx⟩ := (MMP.LcBpf.isCModel_range_iff_cond hK W ω).2 hcond
  exact ⟨x, g, hg.symm, by rw [hx]; exact hω⟩

variable {n π D hD M N u} in
/-- The section of `𝒪_V(-M-S)` representing a section of `C^0`. -/
private noncomputable def degZeroFun {S : Divisor V} (hK : IsCModel n π D hD S M N u K F e ι)
    (hS0 : 0 ≤ S) (hS1 : ∀ E, S E ≤ 1) (W : V.Opens) (x : (F 0).val.obj (op W)) :
    (-(M + S)).divisorialSubmodule W :=
  ⟨(MMP.LcBpf.DegreeZeroRep.exists hK W x).choose,
    DegreeZeroRep.mem_neg_add hK hS0 hS1 (MMP.LcBpf.DegreeZeroRep.exists hK W x).choose_spec.2⟩

variable {n π D hD M N u} in
private theorem degZeroFun_rep {S : Divisor V} (hK : IsCModel n π D hD S M N u K F e ι)
    (hS0 : 0 ≤ S) (hS1 : ∀ E, S E ≤ 1) (W : V.Opens) (x : (F 0).val.obj (op W)) :
    MMP.LcBpf.DegreeZeroRep ι W x (degZeroFun hK hS0 hS1 W x).1 :=
  (MMP.LcBpf.DegreeZeroRep.exists hK W x).choose_spec.2

variable {n π D hD M N u} in
/-- **The degree-zero term of a model of `C^•` is `𝒪_V(-M-S)`**: the morphism sending a section
to the rational function it represents. -/
private noncomputable def degZeroHom {S : Divisor V} (hK : IsCModel n π D hD S M N u K F e ι)
    (hS0 : 0 ≤ S) (hS1 : ∀ E, S E ≤ 1) : F 0 ⟶ (-(M + S)).divisorialSheaf :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk' (degZeroFun hK hS0 hS1 U.unop)
        (fun x y => Subtype.ext (MMP.LcBpf.DegreeZeroRep.unique
          (degZeroFun_rep hK hS0 hS1 U.unop (x + y))
          (MMP.LcBpf.DegreeZeroRep.add (degZeroFun_rep hK hS0 hS1 U.unop x)
            (degZeroFun_rep hK hS0 hS1 U.unop y) (MMP.LcBpf.isCModel_map_add hK U.unop x y)))))
      naturality U U' i := by
        ext x
        exact Subtype.ext (MMP.LcBpf.DegreeZeroRep.unique
          (degZeroFun_rep hK hS0 hS1 U'.unop ((F 0).val.map (homOfLE i.unop.le).op x))
          (MMP.LcBpf.DegreeZeroRep.restrict hK i.unop.le (degZeroFun_rep hK hS0 hS1 U.unop x))) }
    fun U r x => Subtype.ext (MMP.LcBpf.DegreeZeroRep.unique
      (degZeroFun_rep hK hS0 hS1 U.unop (r • x))
      (MMP.LcBpf.DegreeZeroRep.smul hK r (degZeroFun_rep hK hS0 hS1 U.unop x)))⟩

variable {n π D hD M N u} in
private theorem isIso_degZeroHom [IsIntegral V] [CompactSpace V] [Nonempty (cU D)]
    {S : Divisor V} (hK : IsCModel n π D hD S M N u K F e ι) (hS0 : 0 ≤ S) (hS1 : ∀ E, S E ≤ 1)
    (hSD : ∀ E ∈ S.support, E ∈ D.support) : IsIso (degZeroHom hK hS0 hS1) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y h => ?_, fun a => ?_⟩
  · change degZeroFun hK hS0 hS1 W x = degZeroFun hK hS0 hS1 W y at h
    refine MMP.LcBpf.DegreeZeroRep.injective hK (degZeroFun_rep hK hS0 hS1 W x) ?_
    rw [h]
    exact degZeroFun_rep hK hS0 hS1 W y
  · obtain ⟨x, hx⟩ := DegreeZeroRep.surjective_of_mem hK hS0 hSD a.2
    exact ⟨x, Subtype.ext (MMP.LcBpf.DegreeZeroRep.unique (degZeroFun_rep hK hS0 hS1 W x) hx)⟩

variable {n π D hD N} in
/-- **The degree-zero term of the inclusion of a twist is the inclusion of divisorial sheaves.** -/
private theorem cModIncl_comp_degZeroHom {S : Divisor V} (hS0 : 0 ≤ S) (hS1 : ∀ E, S E ≤ 1)
    {M M' : Divisor V} (hU : cU' D M ≤ cU' D M') (hMM : M ≤ M') {u c : Γ(V, cU' D M)}
    {u' c' : Γ(V, cU' D M')} (hcc : c * ((N : Γ(V, cU' D M)) * u) = 1)
    (hcc' : c' * ((N : Γ(V, cU' D M')) * u') = 1)
    (hst : NabStable n π D hD S M u c) (hloc : LocMon n π D hD S M)
    (hcu : ∀ W : V.Opens, δ ((cU D).ι ≫ π) (OO D M W) (resU W c) *
      δ ((cU D).ι ≫ π) (OO D M W) (resU W u) = 0)
    (hst' : NabStable n π D hD S M' u' c') (hloc' : LocMon n π D hD S M')
    (hcu' : ∀ W : V.Opens, δ ((cU D).ι ≫ π) (OO D M' W) (resU W c') *
      δ ((cU D).ι ≫ π) (OO D M' W) (resU W u') = 0) :
    cModIncl n π D hD S hU hMM 0 ≫
        degZeroHom (isCModel_cCx n π D hD S M N u c hcc hst hloc hcu) hS0 hS1 =
      degZeroHom (isCModel_cCx n π D hD S M' N u' c' hcc' hst' hloc' hcu') hS0 hS1 ≫
        Divisor.divisorialSheafInclusion (neg_le_neg (add_le_add hMM le_rfl)) := by
  ext W x
  refine Subtype.ext ?_
  refine MMP.LcBpf.DegreeZeroRep.unique (degZeroFun_rep (isCModel_cCx n π D hD S M N u c hcc hst hloc
    hcu) hS0 hS1 W _) ?_
  obtain ⟨g', hga', hgx'⟩ := degZeroFun_rep (isCModel_cCx n π D hD S M' N u' c' hcc' hst' hloc'
    hcu') hS0 hS1 W x
  refine ⟨V.presheaf.map (homOfLE (inf_le_inf_left W hU)).op g', ?_, ?_⟩
  · rw [toRationalFunctionsPresheaf_app_map, ← hga']
    rfl
  · change (TB ((cU D).ι ≫ π)).incl ((0 : ℕ) : ℤ) (tr π D M ((0 : ℕ) : ℤ) W
      (ambTr π D hU ((0 : ℕ) : ℤ) W x.1)) = _
    refine (congrArg ((TB ((cU D).ι ≫ π)).incl ((0 : ℕ) : ℤ))
      (tr_ambTr π D hU ((0 : ℕ) : ℤ) W x.1)).trans ?_
    refine (incl_map π D (homOfLE (OO_le D hU W)).op _ _).trans ?_
    refine (congrArg _ hgx').trans ?_
    refine (totalRestrict_sm _ _).trans ?_
    exact congrArg _ (G1.app_restrict (inf_le_inf_left W hU) g')

end DegreeZero

section Chain

open MMP.FourfoldProofs.FractionalLogComplexProof

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] (n : ℕ) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
  (D : Divisor X) (hD : D.IsRelativeSNC n f) (S : Divisor X)

/-- **The function `ψ` on `U' = X ∖ (D ∪ Supp M)`.** If `N M = Bn + div ψ` with `Bn` supported on
`D`, then `ψ` has neither zeros nor poles on `U'`, so it is the image of a function there. -/
private theorem exists_eq_ratRes (M Bn : Divisor X) (N : ℕ) (ψ : (RationalFunctions X)ˣ)
    (hψ : (N : ℤ) • M = Bn + principalDivisor ψ) (hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support) :
    ∃ u : Γ(X, cU' D M),
      (toRationalFunctionsPresheaf X).app (op (cU' D M)) u = ratRes (cU' D M) ψ := by
  have hdiv : (0 : Divisor X).IsDivisorialSection (cU' D M) (ratRes (cU' D M) ψ) := by
    intro E hE
    refine Or.inr ?_
    obtain ⟨y, hyE, hyU⟩ := hE
    have hM : M E = 0 := by
      by_contra h
      exact hyU (Or.inr (MMP.Mori.DivisorWithCoeffs.support_subset_supp h hyE))
    have hB0 : Bn E = 0 := by
      by_contra h
      exact hyU (Or.inl (MMP.Mori.DivisorWithCoeffs.support_subset_supp
        (Finsupp.mem_support_iff.1 (hBD E h)) hyE))
    have h := congrArg (fun F => F E) hψ
    simp only [Finsupp.smul_apply, Finsupp.add_apply, hM, hB0, smul_zero, zero_add] at h
    have hord : E.ord ψ = 0 := by
      rw [← MMP.Mori.coeff_principalDivisor]
      exact h.symm
    have h1 := E.valuation_component ψ
    rw [hord] at h1
    rw [DivisorWithCoeffs.coeff_zero, neg_zero]
    exact h1.ge
  exact hdiv.exists_eq

/-- **The model of `C^•` exists for every `Bn ≥ 0` supported on `D`**: `c = (N u)⁻¹`, and
`∇ = d - c du ∧` preserves `C^•`. -/
private theorem exists_model (hSD : ∀ E ∈ S.support, E ∈ D.support) (M Bn : Divisor X)
    (hBn : ∀ E, 0 ≤ Bn E) (hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support) (N : ℕ) (hN : 0 < N)
    (ψ : (RationalFunctions X)ˣ) (hψ : (N : ℤ) • M = Bn + principalDivisor ψ)
    (u : Γ(X, cU' D M))
    (hu : (toRationalFunctionsPresheaf X).app (op (cU' D M)) u = ratRes (cU' D M) ψ) :
    ∃ cc : Γ(X, cU' D M), cc * ((N : Γ(X, cU' D M)) * u) = 1 ∧ NabStable n f D hD S M u cc := by
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hsm : MMP.Mori.IsSmoothScheme f :=
    (MMP.Mori.isSmoothScheme_iff f).2 (SmoothOfRelativeDimension.smooth n f)
  have hMC : M.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm M
  have hNW : ∀ W : X.Opens, IsUnit (N : Γ(X, W)) := by
    intro W
    let φ : k →+* Γ(X, W) := (X.presheaf.map (homOfLE le_top).op).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
    simpa only [map_natCast] using
      ((Nat.cast_ne_zero.2 (by omega : N ≠ 0)).isUnit : IsUnit (N : k)).map φ
  have hunit : IsUnit u := by
    refine isUnit_of_ord_eq_zero u ψ hu fun E hE => ?_
    obtain ⟨y, hyE, hyU⟩ := hE
    have hM : M E = 0 := by
      by_contra h
      exact hyU (Or.inr (MMP.Mori.DivisorWithCoeffs.support_subset_supp h hyE))
    have hB0 : Bn E = 0 := by
      by_contra h
      exact hyU (Or.inl (MMP.Mori.DivisorWithCoeffs.support_subset_supp
        (Finsupp.mem_support_iff.1 (hBD E h)) hyE))
    have h := congrArg (fun F => F E) hψ
    simp only [Finsupp.smul_apply, Finsupp.add_apply, hM, hB0, smul_zero, zero_add] at h
    rw [← MMP.Mori.coeff_principalDivisor]
    exact h.symm
  have hNu : IsUnit ((N : Γ(X, cU' D M)) * u) := (hNW _).mul hunit
  have hcc : (↑hNu.unit⁻¹ : Γ(X, cU' D M)) * ((N : Γ(X, cU' D M)) * u) = 1 :=
    hNu.val_inv_mul
  exact ⟨_, hcc, nabStable_of_genData n f D hD S M u _ hSD fun y =>
    exists_genData n f D hD M u _ hMC Bn N ψ hψ hu hcc hNW (by omega) hBn hBD y⟩

private theorem locMon (M : Divisor X) : LocMon n f D hD S M :=
  fun _ _ _ hω _ hy => Cond.exists_monSet (hω := hω) (hy := hy)

/-- Adding a divisor supported on `D` enlarges `X ∖ (D ∪ Supp M)`. -/
private theorem cU'_le_add (M E : Divisor X) (hE : ∀ B ∈ E.support, B ∈ D.support) :
    cU' D M ≤ cU' D (M + E) := by
  have hsub : E.supp ≤ D.supp := by
    intro x hx
    obtain ⟨B, hB, hx⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.mp hx
    exact MMP.Mori.DivisorWithCoeffs.mem_supp_iff.mpr ⟨B,
      Finsupp.mem_support_iff.mp (hE B (Finsupp.mem_support_iff.mpr hB)), hx⟩
  have h : D.supp ⊔ (M + E).supp ≤ D.supp ⊔ M.supp :=
    sup_le le_sup_left ((MMP.Mori.DivisorWithCoeffs.supp_add_le M E).trans
      (sup_le le_sup_right (hsub.trans le_sup_left)))
  intro x hx hx'
  exact hx (h hx')

/-- Two functions with the same rational function `ψ` agree on the smaller open. -/
private theorem map_eq_of_toRat {M M' : Divisor X} (hU : cU' D M ≤ cU' D M')
    {u : Γ(X, cU' D M)} {u' : Γ(X, cU' D M')} {ψ : (RationalFunctions X)ˣ}
    (hu : (toRationalFunctionsPresheaf X).app (op (cU' D M)) u = ratRes (cU' D M) ψ)
    (hu' : (toRationalFunctionsPresheaf X).app (op (cU' D M')) u' = ratRes (cU' D M') ψ) :
    X.presheaf.map (homOfLE hU).op u' = u := by
  apply toRationalFunctionsPresheaf_app_injective
  rw [toRationalFunctionsPresheaf_app_map, hu', hu]
  rfl

/-- The inverse `c = (N u)⁻¹` restricts to the inverse. -/
private theorem map_eq_of_mul_eq_one {M M' : Divisor X} (hU : cU' D M ≤ cU' D M') (N : ℕ)
    {u c : Γ(X, cU' D M)} {u' c' : Γ(X, cU' D M')}
    (hu : X.presheaf.map (homOfLE hU).op u' = u) (hcc : c * ((N : Γ(X, cU' D M)) * u) = 1)
    (hcc' : c' * ((N : Γ(X, cU' D M')) * u') = 1) : X.presheaf.map (homOfLE hU).op c' = c := by
  have h1 := congrArg (X.presheaf.map (homOfLE hU).op).hom hcc'
  rw [map_mul, map_mul, map_natCast, map_one, hu] at h1
  linear_combination c * h1 - X.presheaf.map (homOfLE hU).op c' * hcc

variable (ψ : (RationalFunctions X)ˣ) (N : ℕ)

/-- **The chain property** of an effective divisor `E` (with natural coefficients): for every
model of `C^•` for `M` and every model for `M + E`, the inclusion `C^•_{M+E} ⟶ C^•_M` is a
quasi-isomorphism, provided every component of `E` is a component of `Bn` and not of `S`. -/
private def ChainQI (E : MMP.Mori.PrimeDivisor X →₀ ℕ) : Prop :=
  ∀ (M Bn : Divisor X), (∀ B, 0 ≤ Bn B) → (∀ B, Bn B ≠ 0 → B ∈ D.support) →
    (N : ℤ) • M = Bn + principalDivisor ψ → (∀ B ∈ E.support, Bn B ≠ 0 ∧ B ∉ S.support) →
    ∀ (u c : Γ(X, cU' D M)),
      (toRationalFunctionsPresheaf X).app (op (cU' D M)) u = ratRes (cU' D M) ψ →
      ∀ (hcc : c * ((N : Γ(X, cU' D M)) * u) = 1) (hst : NabStable n f D hD S M u c)
        (M' : Divisor X), M' = M + E.mapRange (fun m : ℕ => (m : ℤ)) Nat.cast_zero →
      ∀ (u' c' : Γ(X, cU' D M')),
        (toRationalFunctionsPresheaf X).app (op (cU' D M')) u' = ratRes (cU' D M') ψ →
      ∀ (hcc' : c' * ((N : Γ(X, cU' D M')) * u') = 1) (hst' : NabStable n f D hD S M' u' c'),
      ∃ (hU : cU' D M ≤ cU' D M') (hMM : M ≤ M') (hu'' : X.presheaf.map (homOfLE hU).op u' = u)
        (hc'' : X.presheaf.map (homOfLE hU).op c' = c), ∀ q,
        IsIso (HomologicalComplex.homologyMap (cCxIncl n f D hD S hU hMM hu'' hc'' hst'
          (locMon n f D hD S M') (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one f D M' N hcc') hst
          (locMon n f D hD S M)
          (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one f D M N hcc)) q)

private theorem chainQI_zero : ChainQI n f D hD S ψ N 0 := by
  intro M Bn hBn hBD hψ hE u c hu hcc hst M' hM' u' c' hu' hcc' hst'
  simp only [Finsupp.mapRange_zero, add_zero] at hM'
  subst hM'
  have e1 : u' = u := by
    have := map_eq_of_toRat D le_rfl hu hu'
    rwa [presheaf_map_le_self] at this
  subst e1
  have e2 : c' = c := by
    have := map_eq_of_mul_eq_one D le_rfl N (presheaf_map_le_self _ _) hcc hcc'
    rwa [presheaf_map_le_self] at this
  subst e2
  refine ⟨le_rfl, le_rfl, presheaf_map_le_self _ _, presheaf_map_le_self _ _, fun q => ?_⟩
  rw [cCxIncl_self, HomologicalComplex.homologyMap_id]
  infer_instance

private theorem chainQI_single [Nonempty (cU D)] (hSD : ∀ E ∈ S.support, E ∈ D.support)
    (hN : 0 < N) (B : MMP.Mori.PrimeDivisor X) : ChainQI n f D hD S ψ N (Finsupp.single B 1) := by
  classical
  intro M Bn hBn hBD hψ hE u c hu hcc hst M' hM' u' c' hu' hcc' hst'
  simp only [Finsupp.mapRange_single, Nat.cast_one] at hM'
  have hB := hE B (by simp)
  have hBD' : B ∈ D.support := hBD B hB.1
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hsm : MMP.Mori.IsSmoothScheme f :=
    (MMP.Mori.isSmoothScheme_iff f).2 (SmoothOfRelativeDimension.smooth n f)
  have hU : cU' D M ≤ cU' D M' := hM' ▸ cU'_le_add D M _ fun B' hB' => by
    rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hB'
    split_ifs at hB' with h
    · exact h ▸ hBD'
    · exact absurd rfl hB'
  have hMM : M ≤ M' := hM' ▸ le_add_of_nonneg_right (Finsupp.single_nonneg.mpr zero_le_one)
  have hu'' := map_eq_of_toRat D hU hu hu'
  have hc'' := map_eq_of_mul_eq_one D hU N hu'' hcc hcc'
  refine ⟨hU, hMM, hu'', hc'', isIso_homologyMap_cCxIncl n f D hD S hU hMM hu'' hc'' hst'
    (locMon n f D hD S M') (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one f D M' N hcc') hst
    (locMon n f D hD S M)
    (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one f D M N hcc) fun x W₀ hx =>
      nonempty_localData n f D hD S u c N hN hcc Bn ψ hψ hu hBn hBD
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsm M) hSD B hBD' hB.2 hB.1 hM'
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsm M') hU x W₀ hx⟩

private theorem chainQI_add (hSD : ∀ E ∈ S.support, E ∈ D.support) (hN : 0 < N)
    {e₁ e₂ : MMP.Mori.PrimeDivisor X →₀ ℕ} (h₁ : ChainQI n f D hD S ψ N e₁)
    (h₂ : ChainQI n f D hD S ψ N e₂) : ChainQI n f D hD S ψ N (e₁ + e₂) := by
  intro M Bn hBn hBD hψ hE u c hu hcc hst M' hM' u' c' hu' hcc' hst'
  have hsupp₁ : ∀ B ∈ e₁.support, B ∈ (e₁ + e₂).support := fun B hB => by
    rw [Finsupp.mem_support_iff] at hB ⊢
    simp only [Finsupp.add_apply]
    omega
  have hsupp₂ : ∀ B ∈ e₂.support, B ∈ (e₁ + e₂).support := fun B hB => by
    rw [Finsupp.mem_support_iff] at hB ⊢
    simp only [Finsupp.add_apply]
    omega
  set E₁ : Divisor X := e₁.mapRange (fun m : ℕ => (m : ℤ)) Nat.cast_zero with hE₁
  set M₁ : Divisor X := M + E₁ with hM₁
  set Bn₁ : Divisor X := Bn + (N : ℤ) • E₁ with hBn₁
  have hψ₁ : (N : ℤ) • M₁ = Bn₁ + principalDivisor ψ := by
    rw [hM₁, hBn₁, smul_add, hψ]
    abel
  have hBn₁0 : ∀ B, 0 ≤ Bn₁ B := fun B => by
    have := hBn B
    simp only [hBn₁, hE₁, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul]
    positivity
  have hBD₁ : ∀ B, Bn₁ B ≠ 0 → B ∈ D.support := by
    intro B hB
    by_cases h0 : Bn B = 0
    · have he : e₁ B ≠ 0 := by
        intro he
        apply hB
        simp only [hBn₁, hE₁, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
          he, h0, Nat.cast_zero, smul_zero, add_zero]
      exact absurd h0 (hE B (hsupp₁ B (Finsupp.mem_support_iff.mpr he))).1
    · exact hBD B h0
  obtain ⟨u₁, hu₁⟩ := exists_eq_ratRes D M₁ Bn₁ N ψ hψ₁ hBD₁
  obtain ⟨c₁, hcc₁, hst₁⟩ := exists_model n f D hD S hSD M₁ Bn₁ hBn₁0 hBD₁ N hN ψ hψ₁ u₁ hu₁
  obtain ⟨hU₁, hMM₁, hu₁', hc₁', hQ₁⟩ := h₁ M Bn hBn hBD hψ (fun B hB => hE B (hsupp₁ B hB))
    u c hu hcc hst M₁ rfl u₁ c₁ hu₁ hcc₁ hst₁
  have hE₂ : ∀ B ∈ e₂.support, Bn₁ B ≠ 0 ∧ B ∉ S.support := by
    intro B hB
    obtain ⟨h1, h2⟩ := hE B (hsupp₂ B hB)
    refine ⟨fun h => h1 ?_, h2⟩
    have := hBn B
    have h3 : 0 ≤ (N : ℤ) * (e₁ B : ℤ) := by positivity
    simp only [hBn₁, hE₁, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul] at h
    omega
  obtain ⟨hU₂, hMM₂, hu₂', hc₂', hQ₂⟩ := h₂ M₁ Bn₁ hBn₁0 hBD₁ hψ₁ hE₂ u₁ c₁ hu₁ hcc₁ hst₁ M'
    (by rw [hM', hM₁, hE₁, Finsupp.mapRange_add (fun _ _ => Nat.cast_add _ _), add_assoc])
    u' c' hu' hcc' hst'
  have hu'' := map_eq_of_toRat D (hU₁.trans hU₂) hu hu'
  have hc'' := map_eq_of_mul_eq_one D (hU₁.trans hU₂) N hu'' hcc hcc'
  refine ⟨hU₁.trans hU₂, hMM₁.trans hMM₂, hu'', hc'', fun q => ?_⟩
  rw [cCxIncl_trans n f hD S hU₁ hU₂ hMM₁ hMM₂ hu₂' hc₂' hu₁' hc₁' hu'' hc'' hst'
    (locMon n f D hD S M') (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one f D M' N hcc') hst₁
    (locMon n f D hD S M₁)
    (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one f D M₁ N hcc₁) hst (locMon n f D hD S M)
    (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one f D M N hcc),
    HomologicalComplex.homologyMap_comp]
  haveI := hQ₁ q
  haveI := hQ₂ q
  infer_instance

/-- **Every effective twist by components of `Bn` not in `S` is a quasi-isomorphism.** -/
private theorem chainQI [Nonempty (cU D)] (hSD : ∀ E ∈ S.support, E ∈ D.support) (hN : 0 < N)
    (E : MMP.Mori.PrimeDivisor X →₀ ℕ) : ChainQI n f D hD S ψ N E := by
  induction E using Finsupp.induction_linear with
  | zero => exact chainQI_zero n f D hD S ψ N
  | add e₁ e₂ h₁ h₂ => exact chainQI_add n f D hD S ψ N hSD hN h₁ h₂
  | single B b =>
    induction b with
    | zero => rw [Finsupp.single_zero]; exact chainQI_zero n f D hD S ψ N
    | succ b ih =>
      rw [show Finsupp.single B (b + 1) = Finsupp.single B b + Finsupp.single B 1 from
        Finsupp.single_add B b 1]
      exact chainQI_add n f D hD S ψ N hSD hN ih (chainQI_single n f D hD S ψ N hSD hN B)

end Chain

section Surjectivity

open MMP.FourfoldProofs.FractionalLogComplexProof
open scoped Stacks.SmallDerivedModel

variable (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V] [IsIntegral V]
  [CompactSpace V]

/-- **The surjectivity of the twisted inclusion on cohomology.** Let `D = S + Supp Bn` be relative
snc, `S` reduced, `0 ≤ Bn < N`, and `N L = Bn + div ψ`. For every effective `E` supported on
`Supp Bn`, the inclusion `𝒪_V(-L - E - S) ⟶ 𝒪_V(-L - S)` is surjective on `H^j(V, -)`: the
inclusion `C^•_{L+E} ⟶ C^•_L` of fractional logarithmic complexes is a quasi-isomorphism, `C^•_L`
degenerates at `E₁`, and the degree-zero terms are `𝒪_V(-L-E-S)` and `𝒪_V(-L-S)`. -/
private theorem surjective_homology_divisorialSheafInclusion_twist
    (hπ : IsProjective π) (D : Divisor V) (hD : D.IsRelativeSNC n π) [Nonempty (cU D)]
    (S Bn : Divisor V)
    (hS : 0 ≤ S) (hS1 : ∀ E, S E ≤ 1) (hSB : ∀ E, D E = S E + if Bn E = 0 then 0 else 1)
    (N : ℕ) (hN : 0 < N) (hB : ∀ E, 0 ≤ Bn E ∧ Bn E < N) (L : Divisor V)
    (ψ : (RationalFunctions V)ˣ) (hψ : (N : ℤ) • L = Bn + principalDivisor ψ)
    (E : MMP.Mori.PrimeDivisor V →₀ ℕ) (hE : ∀ B ∈ E.support, Bn B ≠ 0) (j : ℕ) :
    Function.Surjective ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) j).map
      ((derivedGlobalSectionsOver π).map ((DerivedCategory.singleFunctor V.Modules 0).map
        (Divisor.divisorialSheafInclusion (neg_le_neg (add_le_add
          (le_add_of_nonneg_right (Finsupp.le_def.mpr fun _ => by simp :
            (0 : Divisor V) ≤ E.mapRange (fun m : ℕ => (m : ℤ)) Nat.cast_zero)) le_rfl) :
            -((L + E.mapRange (fun m : ℕ => (m : ℤ)) Nat.cast_zero) + S) ≤ -(L + S)))))).hom := by
  classical
  have hBn : ∀ E, 0 ≤ Bn E := fun E => (hB E).1
  have hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support := by
    intro E hE
    have hSE : 0 ≤ S E := Finsupp.le_def.1 hS E
    rw [Finsupp.mem_support_iff, hSB E, ite_eq_right hE]
    omega
  have hSD : ∀ E ∈ S.support, E ∈ D.support := by
    intro E hE
    have hSE : 0 ≤ S E := Finsupp.le_def.1 hS E
    rw [Finsupp.mem_support_iff] at hE ⊢
    rw [hSB E]
    split_ifs <;> omega
  have hBS : ∀ B, Bn B ≠ 0 → B ∉ S.support := by
    intro B hB hBS
    have h1 := hD.1 B (hBD B hB)
    have h2 := hSB B
    rw [if_neg hB] at h2
    have h3 := Finsupp.mem_support_iff.mp hBS
    have h4 := hS1 B
    omega
  obtain ⟨E', hE'⟩ : ∃ E' : Divisor V, E' = E.mapRange (fun m : ℕ => (m : ℤ)) Nat.cast_zero :=
    ⟨_, rfl⟩
  -- the models for `L` and `L + E`
  obtain ⟨u, hu⟩ := exists_eq_ratRes D L Bn N ψ hψ hBD
  obtain ⟨c, hcc, hst⟩ := exists_model n π D hD S hSD L Bn hBn hBD N hN ψ hψ u hu
  obtain ⟨Bn', hBn'⟩ : ∃ Bn' : Divisor V, Bn' = Bn + (N : ℤ) • E' := ⟨_, rfl⟩
  have hψ' : (N : ℤ) • (L + E') = Bn' + principalDivisor ψ := by
    rw [hBn', smul_add, hψ]
    abel
  have hBn'0 : ∀ B, 0 ≤ Bn' B := fun B => by
    have := hBn B
    simp only [hBn', hE', Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul]
    positivity
  have hBD' : ∀ B, Bn' B ≠ 0 → B ∈ D.support := by
    intro B hB
    by_cases h0 : Bn B = 0
    · have he : E B ≠ 0 := by
        intro he
        apply hB
        simp only [hBn', hE', Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
          he, h0, Nat.cast_zero, smul_zero, add_zero]
      exact absurd h0 (hE B (Finsupp.mem_support_iff.mpr he))
    · exact hBD B h0
  obtain ⟨u', hu'⟩ := exists_eq_ratRes D (L + E') Bn' N ψ hψ' hBD'
  obtain ⟨c', hcc', hst'⟩ := exists_model n π D hD S hSD (L + E') Bn' hBn'0 hBD' N hN ψ hψ' u' hu'
  obtain ⟨hU, hMM, hu'', hc'', hQ⟩ := chainQI n π D hD S ψ N hSD hN E L Bn hBn hBD hψ
    (fun B hB => ⟨hE B hB, hBS B (hE B hB)⟩) u c hu hcc hst (L + E') (by rw [hE']) u' c' hu' hcc' hst'
  haveI : QuasiIso (cCxIncl n π D hD S hU hMM hu'' hc'' hst' (locMon n π D hD S (L + E'))
      (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one π D (L + E') N hcc') hst (locMon n π D hD S L)
      (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one π D L N hcc)) :=
    (quasiIso_iff _).2 fun q => (quasiIsoAt_iff_isIso_homologyMap _ q).2 (hQ q)
  have hK := isCModel_cCx n π D hD S L N u c hcc hst (locMon n π D hD S L)
    (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one π D L N hcc)
  have hK' := isCModel_cCx n π D hD S (L + E') N u' c' hcc' hst' (locMon n π D hD S (L + E'))
    (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one π D (L + E') N hcc')
  have hdeg := (Divisor.finrank_hypercohomology_eq_sum_of_fractionalLogComplex n π hπ D hD S Bn
    hS hSB N hN hB L ψ hψ u hu).2 (cCx n π D hD S L u c hst (locMon n π D hD S L)
      (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one π D L N hcc)) (cMod n π D hD S L)
      (fun _ => Iso.refl _)
      (fun p W x => tr π D L (p : ℤ) W x.1) hK j
  have h1 := MMP.LcBpf.surjective_derivedGlobalSectionsOver_map_of_quasiIso π
    (SheafOfModules.underlyingRingHom (φ := AlgebraicGeometry.inverseImageStructureMap π))
    (cCxIncl n π D hD S hU hMM hu'' hc'' hst' (locMon n π D hD S (L + E'))
      (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one π D (L + E') N hcc') hst (locMon n π D hD S L)
      (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one π D L N hcc))
    (cModIncl n π D hD S hU hMM 0) (Iso.refl _) (Iso.refl _) (by
      refine (Category.comp_id _).trans ?_
      refine Eq.trans ?_ (Category.id_comp _).symm
      rfl) j
    (fun p _ => MMP.LcBpf.finite_Hc_single0_X_of_isCModel n π hπ D hD S Bn hS hSB N hN hB L ψ
      hψ u hu hK p _) hdeg
  haveI := isIso_degZeroHom hK hS hS1 hSD
  haveI := isIso_degZeroHom hK' hS hS1 hSD
  subst hBn' hE'
  refine surjective_map_of_comm_sq (DerivedCategory.singleFunctor V.Modules 0 ⋙
      derivedGlobalSectionsOver π ⋙ DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) j) _ _
    (asIso (degZeroHom hK' hS hS1)).symm (asIso (degZeroHom hK hS hS1)).symm ?_ h1
  rw [Iso.symm_hom, Iso.symm_hom, asIso_inv, asIso_inv, IsIso.comp_inv_eq, Category.assoc,
    cModIncl_comp_degZeroHom hS hS1 hU hMM hcc hcc' hst (locMon n π D hD S L)
      (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one π D L N hcc) hst' (locMon n π D hD S _)
      (δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one π D _ N hcc'), IsIso.inv_hom_id_assoc]

end Surjectivity

section Setup

open MMP.FourfoldProofs.FractionalLogComplexProof
open scoped Stacks.SmallDerivedModel

variable (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V] [IsIntegral V]
  [CompactSpace V]

omit [SmoothOfRelativeDimension n π] [IsIntegral V] in
/-- If `N (M - (K + Δ)) = div ψ`, then the integral divisor `N (M - K - ⌊Δ⌋) - div ψ` is
`N {Δ}`. -/
private theorem coe_coeff_sub_principalDivisor (Δ : QDivisor V) (M K : Divisor V) (N : ℕ)
    (ψ : (RationalFunctions V)ˣ)
    (hψM : (N : ℤ) • (Divisor.toQDivisor M - (Divisor.toQDivisor K + Δ)) =
      Divisor.toQDivisor (principalDivisor ψ)) (E : MMP.Mori.PrimeDivisor V) :
    ((((N : ℤ) • (M - K - Δ.roundDown) - principalDivisor ψ : Divisor V) E : ℤ) : ℚ) =
      N * Int.fract (Δ.coeff E) := by
  have h := congrArg (fun D : QDivisor V => D E) hψM
  simp only [Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.add_apply] at h ⊢
  have h2 : (Divisor.toQDivisor (principalDivisor ψ)) E = ((principalDivisor ψ E : ℤ) : ℚ) := rfl
  have h3 : (Divisor.toQDivisor M) E = ((M E : ℤ) : ℚ) := rfl
  have h4 : (Divisor.toQDivisor K) E = ((K E : ℤ) : ℚ) := rfl
  have h5 : Δ.roundDown E = ⌊Δ.coeff E⌋ := DivisorWithCoeffs.coeff_roundDown Δ E
  rw [h2, h3, h4] at h
  rw [h5, Int.fract]
  change ((N : ℤ) • _ : ℚ) = _ at h
  rw [zsmul_eq_mul] at h
  simp only [smul_eq_mul]
  push_cast at h ⊢
  rw [← h]
  change _ = (N : ℚ) * (Δ E - _)
  ring

omit [SmoothOfRelativeDimension n π] [IsIntegral V] [CompactSpace V] in
/-- Surjectivity of `G` on an inclusion of divisorial sheaves depends only on the two divisors. -/
private theorem surjective_map_divisorialSheafInclusion_congr₂ {R : Type*} [Ring R]
    (G : V.Modules ⥤ ModuleCat R) {A A' B B' : Divisor V} (hA : A = A') (hB : B = B')
    (h : A ≤ B) (h' : A' ≤ B')
    (hs : Function.Surjective (G.map (Divisor.divisorialSheafInclusion h)).hom) :
    Function.Surjective (G.map (Divisor.divisorialSheafInclusion h')).hom := by
  subst hA hB
  exact hs

omit [SmoothOfRelativeDimension n π] [IsIntegral V] in
/-- For coefficients in `[0, 1]`, `⌊Δ⌋` is `1` exactly where the coefficient is `1`. -/
private theorem roundDown_eq_ite (Δ : QDivisor V) (hΔ0 : ∀ E, 0 ≤ Δ.coeff E)
    (hΔ1 : ∀ E, Δ.coeff E ≤ 1) (E : MMP.Mori.PrimeDivisor V) :
    Δ.roundDown E = if Δ.coeff E = 1 then 1 else 0 := by
  rw [show Δ.roundDown E = ⌊Δ.coeff E⌋ from DivisorWithCoeffs.coeff_roundDown Δ E]
  split_ifs with h
  · rw [h, Int.floor_one]
  · exact Int.floor_eq_zero_iff.mpr ⟨hΔ0 E, lt_of_le_of_ne (hΔ1 E) h⟩

/-- A nonnegative integer-valued finsupp has natural coefficients. -/
private theorem exists_natFinsupp_of_nonneg {α : Type*} {D : α →₀ ℤ} (hD : 0 ≤ D) :
    ∃ E : α →₀ ℕ, E.mapRange (fun m : ℕ => (m : ℤ)) Nat.cast_zero = D ∧
      E.support ⊆ D.support := by
  refine ⟨D.mapRange Int.toNat Int.toNat_zero, ?_, fun B hB => ?_⟩
  · ext B
    simp only [Finsupp.mapRange_apply]
    exact Int.toNat_of_nonneg (Finsupp.le_def.mp hD B)
  · rw [Finsupp.mem_support_iff] at hB ⊢
    intro h0
    apply hB
    simp [h0]

/-- For a coefficient `q ∈ [0, 1]`, `{q}` is `0` if `q = 1` and `q` otherwise. -/
private theorem fract_eq_ite_of_mem_Icc {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    Int.fract q = if q = 1 then 0 else q := by
  split_ifs with h
  · rw [h, Int.fract_one]
  · exact Int.fract_eq_self.mpr ⟨h0, lt_of_le_of_ne h1 h⟩

/-- An integer `b` with `b = N {q}` vanishes exactly when `{q}` does. -/
private theorem eq_zero_iff_fract_eq_zero_of_cast_eq {b : ℤ} {q : ℚ} {N : ℕ} (hN : 0 < N)
    (h : (b : ℚ) = N * Int.fract q) : b = 0 ↔ Int.fract q = 0 := by
  refine ⟨fun hb => ?_, fun hq => ?_⟩
  · rw [hb, Int.cast_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast hN.ne')
  · rw [hq, mul_zero] at h
    exact_mod_cast h

/-- An integer `b` with `b = N {q}` lies in `[0, N)`. -/
private theorem nonneg_and_lt_of_cast_eq {b : ℤ} {q : ℚ} {N : ℕ} (hN : 0 < N)
    (h : (b : ℚ) = N * Int.fract q) : 0 ≤ b ∧ b < N := by
  have h2 := Int.fract_nonneg q
  have h3 := Int.fract_lt_one q
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  refine ⟨?_, ?_⟩
  · have : (0 : ℚ) ≤ b := by
      rw [h]
      positivity
    exact_mod_cast this
  · have : (b : ℚ) < N := by
      rw [h]
      nlinarith
    exact_mod_cast this

include n in
/-- **The dual form of the injectivity theorem.** Let `Δ` be an snc divisor with coefficients in
`[0, 1]`, `M ∼_ℚ K + Δ` and `D ≥ 0` supported on `Supp {Δ}`. Then
`H^j(V, 𝒪_V(K - M - D)) ⟶ H^j(V, 𝒪_V(K - M))` is surjective for every `j`: with `S = ⌊Δ⌋`,
`L = M - K - S` and `N L = N {Δ} + div ψ` this is
`surjective_homology_divisorialSheafInclusion_twist` for the reduced divisor `Supp Δ`. -/
private theorem surjective_homology_divisorialSheafInclusion_sub (hπ : IsProjective π)
    (Δ : QDivisor V) (hΔ : Δ.IsSNC π) (hΔ0 : ∀ E, 0 ≤ Δ.coeff E) (hΔ1 : ∀ E, Δ.coeff E ≤ 1)
    (M K : Divisor V)
    (hM : (Divisor.toQDivisor M).QLinearlyEquivalent (Divisor.toQDivisor K + Δ))
    (D : Divisor V) (hD : 0 ≤ D) (hDB : D.support ⊆ Δ.fract.support) (j : ℕ) :
    Function.Surjective ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) j).map
      ((derivedGlobalSectionsOver π).map ((DerivedCategory.singleFunctor V.Modules 0).map
        (Divisor.divisorialSheafInclusion (sub_le_sub_left (le_add_of_nonneg_right hD) K :
          K - (M + D) ≤ K - M))))).hom := by
  classical
  obtain ⟨N, hN, ψ, hψM⟩ := hM
  have hcoef := coe_coeff_sub_principalDivisor Δ M K N ψ hψM
  obtain ⟨Bn, hBn⟩ : ∃ Bn : Divisor V,
      Bn = (N : ℤ) • (M - K - Δ.roundDown) - principalDivisor ψ := ⟨_, rfl⟩
  rw [← hBn] at hcoef
  have hSE := roundDown_eq_ite Δ hΔ0 hΔ1
  have hBn0 : ∀ E, Bn E = 0 ↔ Int.fract (Δ.coeff E) = 0 := fun E =>
    eq_zero_iff_fract_eq_zero_of_cast_eq hN (hcoef E)
  let Dm : Divisor V := Δ.mapCoeffs (fun q : ℚ => if q = 0 then (0 : ℤ) else 1) (by simp)
  have hDm : ∀ E, Dm E = if Δ.coeff E = 0 then 0 else 1 := fun E =>
    DivisorWithCoeffs.coeff_mapCoeffs _ _ Δ E
  have hsupp : Dm.support ⊆ Δ.support := fun E hE => by
    rw [Finsupp.mem_support_iff] at hE ⊢
    exact fun h0 => hE ((hDm E).trans (if_pos h0))
  have hrel : Dm.IsRelativeSNC n π := isRelativeSNC_of_isSNC π Dm (hΔ.of_support_subset hsupp)
    fun E hE => by
      rw [Finsupp.mem_support_iff, hDm] at hE
      rw [hDm]
      split_ifs at hE ⊢ with h
      · exact absurd rfl hE
      · rfl
  haveI : Nonempty (cU Dm) := ⟨⟨genericPoint V, MMP.Fourfold.genericPoint_notMem_supp Dm⟩⟩
  have hSB : ∀ E, Dm E = Δ.roundDown E + if Bn E = 0 then 0 else 1 := fun E => by
    simp only [hDm, hSE, hBn0, fract_eq_ite_of_mem_Icc (hΔ0 E) (hΔ1 E)]
    by_cases h0 : Δ.coeff E = 0
    · simp [h0]
    · by_cases h1 : Δ.coeff E = 1 <;> simp [h0, h1]
  have hS0 : 0 ≤ Δ.roundDown := Finsupp.le_def.mpr fun E => by
    change (0 : ℤ) ≤ Δ.roundDown E
    rw [hSE]
    split_ifs <;> norm_num
  have hS1 : ∀ E, Δ.roundDown E ≤ 1 := fun E => by
    rw [hSE]
    split_ifs <;> norm_num
  have hψ : (N : ℤ) • (M - K - Δ.roundDown) = Bn + principalDivisor ψ := by
    rw [hBn, sub_add_cancel]
  obtain ⟨E', hE'D, hE'⟩ := exists_natFinsupp_of_nonneg hD
  have hE : ∀ B ∈ E'.support, Bn B ≠ 0 := fun B hB => by
    rw [Ne, hBn0]
    exact Finsupp.mem_support_iff.mp (hDB (hE' hB))
  have h := surjective_homology_divisorialSheafInclusion_twist n π hπ Dm hrel Δ.roundDown Bn hS0
    hS1 hSB N hN (fun E => nonneg_and_lt_of_cast_eq hN (hcoef E)) (M - K - Δ.roundDown) ψ hψ E' hE j
  refine surjective_map_divisorialSheafInclusion_congr₂ (DerivedCategory.singleFunctor V.Modules 0 ⋙
    derivedGlobalSectionsOver π ⋙ DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) j) ?_ ?_ _ _ h
  · rw [hE'D]
    abel
  · abel

end Setup

section DivisorialDual

/-! ### The dual of a divisorial sheaf

For a Cartier divisor `L`, multiplication of sections `𝒪_X(-L) ⊗ 𝒪_X(L) ⟶ 𝒪_X(0) = 𝒪_X` is a
perfect pairing, so it identifies `𝒪_X(-L)` with the dual `𝒪_X(L)^∨`, naturally in `L` for the
inclusions `𝒪_X(L) ⟶ 𝒪_X(L')`, `L ≤ L'`. -/

open MonoidalCategory
open Stacks.Duality.LocallyFreeTwist (dual dualMap hasRightDual tensorLeftIsoTensor)

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- `𝒪_X(L)`, as an object of the monoidal category of `𝒪_X`-modules. -/
private noncomputable abbrev dsh (L : Divisor X) : Stacks.Duality.LocallyFreeTwist.Mod X :=
  L.divisorialSheaf

/-- The inclusion `𝒪_X(A) ⟶ 𝒪_X(B)` for `A ≤ B`, in the monoidal category of `𝒪_X`-modules. -/
private noncomputable abbrev inc {A B : Divisor X} (h : A ≤ B) : dsh A ⟶ dsh B :=
  Divisor.divisorialSheafInclusion h

/-- The multiplication `𝒪_X(A) ⊗ 𝒪_X(B) ⟶ 𝒪_X(A + B)`, in the monoidal category of
`𝒪_X`-modules. -/
private noncomputable abbrev tm (A B : Divisor X) : dsh A ⊗ dsh B ⟶ dsh (A + B) :=
  Divisor.divisorialSheafTensorMul A B

/-- `𝒪_X(0) ≅ 𝒪_X`, in the monoidal category of `𝒪_X`-modules. -/
private noncomputable abbrev zIso :
    dsh (0 : Divisor X) ≅ 𝟙_ (Stacks.Duality.LocallyFreeTwist.Mod X) :=
  Divisor.divisorialSheafZeroIso

omit [CompactSpace X] in
/-- Multiplication of sections commutes with the inclusions of divisorial sheaves. -/
@[reassoc]
private theorem tensorHom_comp_tm {A A' B B' : Divisor X} (hA : A ≤ A') (hB : B ≤ B') :
    (inc hA ⊗ₘ inc hB) ≫ tm A' B' = tm A B ≫ inc (add_le_add hA hB) := by
  apply Stacks.SheafOfModules.OnSpace.tensor_hom_ext X.toRingedSpace
  intro U a b
  have h1 := Stacks.SheafOfModules.OnSpace.tensorHom_tmul X.toRingedSpace
    (inc hA) (inc hB) U a b
  have h2 := Divisor.divisorialSheafTensorMul_unit U a b
  have h3 := Divisor.divisorialSheafTensorMul_unit (D := A') (D' := B') U
    ((inc hA).val.app U a) ((inc hB).val.app U b)
  refine (Stacks.SheafOfModules.OnSpace.sheaf_comp_app_apply X.toRingedSpace _ _ U _).trans ?_
  refine Eq.trans (congrArg _ h1) ?_
  refine h3.trans ?_
  refine Eq.trans ?_
    (Stacks.SheafOfModules.OnSpace.sheaf_comp_app_apply X.toRingedSpace _ _ U _).symm
  refine Eq.trans ?_ (congrArg _ h2.symm)
  rfl

omit [CompactSpace X] in
private theorem inc_refl (A : Divisor X) : inc (le_refl A) = 𝟙 _ :=
  Divisor.divisorialSheafInclusion_refl

omit [CompactSpace X] in
@[reassoc]
private theorem inc_comp {A B C : Divisor X} (h : A ≤ B) (h' : B ≤ C) :
    inc h ≫ inc h' = inc (h.trans h') :=
  Divisor.divisorialSheafInclusion_comp h h'

omit [CompactSpace X] in
private theorem isIso_inc_of_eq {A B : Divisor X} (h : A = B) : IsIso (inc h.le) := by
  subst h
  rw [inc_refl]
  infer_instance

private theorem isIso_tm {A B : Divisor X} (hA : A.IsCartier) (hB : B.IsCartier) :
    IsIso (tm A B) :=
  hA.isIso_divisorialSheafTensorMul hB

/-- The divisorial sheaf of a Cartier divisor is finite locally free. -/
private theorem isFiniteLocallyFree_dsh {L : Divisor X} (hL : L.IsCartier) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dsh L) := by
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L.divisorialSheaf :=
    hL.isInvertibleModule_divisorialSheaf
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L.divisorialSheaf 1

/-- The pairing `𝒪_X(-L) ⊗ 𝒪_X(L) ⟶ 𝒪_X`, `φ ⊗ ψ ↦ φψ`. -/
private noncomputable def mulUnit (L : Divisor X) :
    dsh (-L) ⊗ dsh L ⟶ 𝟙_ (Stacks.Duality.LocallyFreeTwist.Mod X) :=
  tm (-L) L ≫ inc (neg_add_cancel L).le ≫ zIso.hom

omit [CompactSpace X] in
/-- The pairing `mulUnit` is natural in `L`. -/
private theorem whiskerRight_inc_comp_mulUnit {L L' : Divisor X} (h : L ≤ L') :
    inc (neg_le_neg h) ▷ dsh L ≫ mulUnit L = dsh (-L') ◁ inc h ≫ mulUnit L' := by
  rw [← tensorHom_id, ← id_tensorHom, ← inc_refl, ← inc_refl, mulUnit, mulUnit,
    tensorHom_comp_tm_assoc, tensorHom_comp_tm_assoc, inc_comp_assoc, inc_comp_assoc]

/-- A morphism into a right dual `Eᘁ` is determined by its composite with the evaluation. -/
private theorem eq_of_whiskerRight_comp_evaluation {C : Type*} [Category C] [MonoidalCategory C]
    {E Y : C} [HasRightDual E] {φ ψ : Y ⟶ Eᘁ} (h : φ ▷ E ≫ ε_ E Eᘁ = ψ ▷ E ≫ ε_ E Eᘁ) :
    φ = ψ := by
  have := congrArg (tensorRightHomEquiv Y E Eᘁ (𝟙_ C)) h
  rw [tensorRightHomEquiv_whiskerRight_comp_evaluation,
    tensorRightHomEquiv_whiskerRight_comp_evaluation] at this
  exact (cancel_mono _).1 this

/-- Tensoring on the right with an object `P` having a tensor inverse reflects isomorphisms. -/
private theorem isIso_of_isIso_whiskerRight {C : Type*} [Category C] [MonoidalCategory C]
    {P Q : C} (e : P ⊗ Q ≅ 𝟙_ C) {M N : C} (φ : M ⟶ N) (h : IsIso (φ ▷ P)) : IsIso φ := by
  have : IsIso (φ ▷ (P ⊗ Q)) := by rw [whiskerRight_tensor]; infer_instance
  have : IsIso (φ ▷ 𝟙_ C) := by
    have hy : inv (M ◁ e.hom) ≫ (φ ▷ (P ⊗ Q) ≫ N ◁ e.hom) = φ ▷ 𝟙_ C := by
      rw [← whisker_exchange φ e.hom, IsIso.inv_hom_id_assoc]
    exact hy ▸ inferInstance
  exact (whiskerRight_id_symm φ).symm ▸
    (inferInstance : IsIso ((ρ_ M).inv ≫ φ ▷ 𝟙_ C ≫ (ρ_ N).hom))

variable (L : Divisor X) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dsh L)]

/-- The morphism `𝒪_X(-L) ⟶ 𝒪_X(L)^∨` adjoint to the pairing `mulUnit L`. -/
private noncomputable def toDual : dsh (-L) ⟶ dual (dsh L) :=
  letI := hasRightDual (dsh L)
  (tensorRightHomEquiv (dsh (-L)) (dsh L) (dsh L)ᘁ (𝟙_ _)) (mulUnit L) ≫ (λ_ _).hom

private theorem toDual_whiskerRight_comp_evaluation :
    letI := hasRightDual (dsh L)
    toDual L ▷ dsh L ≫ ε_ (dsh L) (dsh L)ᘁ = mulUnit L := by
  letI := hasRightDual (dsh L)
  apply (tensorRightHomEquiv (dsh (-L)) (dsh L) (dsh L)ᘁ (𝟙_ _)).injective
  rw [tensorRightHomEquiv_whiskerRight_comp_evaluation, toDual, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- `toDual` is natural: it carries the inclusion `𝒪_X(-L') ⟶ 𝒪_X(-L)` to the dual of the
inclusion `𝒪_X(L) ⟶ 𝒪_X(L')`. -/
private theorem inc_comp_toDual {L L' : Divisor X} (h : L ≤ L')
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dsh L)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dsh L')] :
    inc (neg_le_neg h) ≫ toDual L = toDual L' ≫ dualMap (inc h) := by
  letI := hasRightDual (dsh L)
  letI := hasRightDual (dsh L')
  apply eq_of_whiskerRight_comp_evaluation (E := dsh L)
  rw [comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
    toDual_whiskerRight_comp_evaluation, dualMap, rightAdjointMate_comp_evaluation]
  refine (whiskerRight_inc_comp_mulUnit h).trans ?_
  rw [← toDual_whiskerRight_comp_evaluation L']
  exact whisker_exchange_assoc _ _ _

/-- **`𝒪_X(L)^∨ ≅ 𝒪_X(-L)`** for a Cartier divisor `L`: the evaluation of the invertible sheaf
`𝒪_X(L)` and the pairing `mulUnit L` are both isomorphisms. -/
private theorem isIso_toDual (hL : L.IsCartier) : IsIso (toDual L) := by
  letI := hasRightDual (dsh L)
  haveI : IsIso (tm (-L) L) := isIso_tm hL.neg hL
  haveI : IsIso (tm L (-L)) := isIso_tm hL hL.neg
  haveI := isIso_inc_of_eq (neg_add_cancel L)
  haveI := isIso_inc_of_eq (add_neg_cancel L)
  haveI : IsIso (mulUnit L) := by unfold mulUnit; infer_instance
  haveI := hL.isInvertibleModule_divisorialSheaf
  haveI : IsIso (ε_ (dsh L) (dsh L)ᘁ) :=
    Stacks.SheafOfModules.isIso_evaluation_of_isInvertible (dsh L)
  haveI : IsIso (toDual L ▷ dsh L ≫ ε_ (dsh L) (dsh L)ᘁ) := by
    rw [toDual_whiskerRight_comp_evaluation]; infer_instance
  haveI := IsIso.of_isIso_comp_right (toDual L ▷ dsh L) (ε_ (dsh L) (dsh L)ᘁ)
  exact isIso_of_isIso_whiskerRight
    (asIso (tm L (-L)) ≪≫ asIso (inc (add_neg_cancel L).le) ≪≫ zIso) _ this

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dsh L)] in
private theorem sheafTensor_map_eq_whiskerLeft (N : Stacks.Duality.LocallyFreeTwist.Mod X)
    {A B : Stacks.Duality.LocallyFreeTwist.Mod X} (f : A ⟶ B) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (Stacks.Duality.LocallyFreeTwist.R X)).obj N).map f = N ◁ f := by
  have := (tensorLeftIsoTensor N).hom.naturality f
  simp only [tensorLeftIsoTensor, NatIso.ofComponents_hom_app, Iso.refl_hom, Category.comp_id,
    Category.id_comp] at this
  exact this.symm

variable {L}

/-- The isomorphism `ω ⊗ 𝒪_X(L)^∨ ≅ 𝒪_X(K - L)` for `ω ≅ 𝒪_X(K)`. -/
private noncomputable def tensorDualHom {K : Divisor X}
    {ω : Stacks.Duality.LocallyFreeTwist.Mod X} (eω : ω ≅ dsh K) (hL : L.IsCartier) :
    ω ⊗ dual (dsh L) ⟶ dsh (K - L) :=
  ω ◁ @inv _ _ _ _ (toDual L) (isIso_toDual L hL) ≫ eω.hom ▷ dsh (-L) ≫ tm K (-L) ≫
    inc (sub_eq_add_neg K L).symm.le

private theorem isIso_tensorDualHom {K : Divisor X} {ω : Stacks.Duality.LocallyFreeTwist.Mod X}
    (eω : ω ≅ dsh K) (hK : K.IsCartier) (hL : L.IsCartier) : IsIso (tensorDualHom eω hL) := by
  haveI := isIso_toDual L hL
  haveI := isIso_tm hK hL.neg
  haveI := isIso_inc_of_eq (sub_eq_add_neg K L).symm
  unfold tensorDualHom
  infer_instance

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dsh L)] in
/-- **The dual of an inclusion of divisorial sheaves.** For Cartier divisors `K, M ≤ M'` and
`ω ≅ 𝒪_X(K)`, the morphism `ω ⊗ 𝒪_X(M')^∨ ⟶ ω ⊗ 𝒪_X(M)^∨` is, up to isomorphism, the inclusion
`𝒪_X(K - M') ⟶ 𝒪_X(K - M)`; so a functor which is surjective on the latter is surjective on
the former. -/
private theorem surjective_map_dualMap_inc {A : Type*} [Ring A]
    (G : Stacks.Duality.LocallyFreeTwist.Mod X ⥤ ModuleCat A)
    {K M M' : Divisor X} {ω : Stacks.Duality.LocallyFreeTwist.Mod X} (eω : ω ≅ dsh K)
    (hK : K.IsCartier) (hM : M.IsCartier) (hM' : M'.IsCartier) (h : M ≤ M')
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dsh M)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dsh M')]
    (hb : Function.Surjective (G.map (inc (sub_le_sub_left h K))).hom) :
    Function.Surjective (G.map (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (Stacks.Duality.LocallyFreeTwist.R X)).obj ω).map (dualMap (inc h)))).hom := by
  haveI := isIso_toDual M hM
  haveI := isIso_toDual M' hM'
  have h1 : dualMap (inc h) ≫ inv (toDual M) = inv (toDual M') ≫ inc (neg_le_neg h) := by
    rw [IsIso.comp_inv_eq, Category.assoc, inc_comp_toDual h, IsIso.inv_hom_id_assoc]
  have w : ω ◁ dualMap (inc h) ≫ tensorDualHom eω hM = tensorDualHom eω hM' ≫
      inc (sub_le_sub_left h K) := by
    simp only [tensorDualHom]
    rw [← whiskerLeft_comp_assoc, h1, whiskerLeft_comp_assoc, whisker_exchange_assoc,
      ← id_tensorHom (dsh K) (inc (neg_le_neg h)),
      show 𝟙 (dsh K) = inc (le_refl K) from (inc_refl K).symm, tensorHom_comp_tm_assoc]
    simp only [Category.assoc, inc_comp]
  rw [sheafTensor_map_eq_whiskerLeft]
  exact surjective_map_of_comm_sq G _ _ (@asIso _ _ _ _ _ (isIso_tensorDualHom eω hK hM'))
    (@asIso _ _ _ _ _ (isIso_tensorDualHom eω hK hM)) w hb

end DivisorialDual

end Proof_thm_mmp_lc_bpf_fundamental_injectivity

@[expose] public section

namespace MMP.Mori

open scoped Stacks.SmallDerivedModel
open Proof_thm_mmp_lc_bpf_fundamental_injectivity

/-- **Fundamental injectivity theorem** (Kollár, Esnault–Viehweg; Fujino's form with a reduced
part). Let `V` be a smooth projective complex variety with canonical divisor `K`, and `Δ` a
`ℚ`-divisor with simple normal crossing support and coefficients in `[0, 1]`. If `M` is a divisor
with `M ∼_ℚ K + Δ` and `D` is an effective divisor whose components all lie in the support of the
fractional part `{Δ}`, then the map `H^q(V, 𝒪_V(M)) ⟶ H^q(V, 𝒪_V(M + D))` induced by
`𝒪_V(M) ⊆ 𝒪_V(M + D)` is injective for every `q`. -/
@[mmp "thm_mmp_lc_bpf_fundamental_injectivity"]
public theorem injective_derivedCohomologyOverField_map_divisorialSheafInclusion
    {V : Scheme.{0}}
    (f : V ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ f] (hsm : IsSmoothScheme f)
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] {n : ℕ} {K : Divisor V} (hK : K.IsCanonicalDivisor f n)
    (Δ : QDivisor V) (hΔ : Δ.IsSNC f) (hΔ0 : ∀ E, 0 ≤ Δ.coeff E) (hΔ1 : ∀ E, Δ.coeff E ≤ 1)
    (M : Divisor V)
    (hM : (Divisor.toQDivisor M).QLinearlyEquivalent (Divisor.toQDivisor K + Δ))
    (D : Divisor V) (hD : 0 ≤ D) (hDB : D.support ⊆ Δ.fract.support) (q : ℤ) :
    Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) q).map
      ((derivedGlobalSectionsOver f).map
        ((DerivedCategory.singleFunctor V.Modules 0).map
          (Divisor.divisorialSheafInclusion (le_add_of_nonneg_right hD :
            M ≤ M + D))))).hom := by
  haveI : IsProper f := isProper_of_isProjectiveMorphism f
    (inferInstance : AlgebraicGeometry.IsProjectiveVariety ℂ f).isProjective
  haveI : Smooth f := (isSmoothScheme_iff f).1 hsm
  haveI := smoothOfRelativeDimension_of_equidimensional ℂ f
    (TopologicalSpace.Equidimensional.of_preirreducibleSpace V) n hK.1
  have hπ : IsProjective f := (isProjectiveVariety_iff_isProjective ℂ f).mp inferInstance
  have hC : ∀ A : Divisor V, A.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  haveI := isFiniteLocallyFree_dsh (hC M)
  haveI := isFiniteLocallyFree_dsh (hC (M + D))
  obtain ⟨eω⟩ := hK.nonempty_exteriorPower_iso_divisorialSheaf ℂ f hsm
  refine injective_of_surjective_dualMap f n (E₁ := dsh M) (E₂ := dsh (M + D))
    (inc (le_add_of_nonneg_right hD)) q ?_
  refine surjective_map_dualMap_inc (DerivedCategory.singleFunctor V.Modules 0 ⋙
    derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) ((n : ℤ) - q))
    eω (hC K) (hC M) (hC (M + D)) (le_add_of_nonneg_right hD) ?_
  rcases lt_or_ge ((n : ℤ) - q) 0 with hneg | hpos
  · exact MMP.LcBpf.surjective_homology_map_of_neg f _ hneg
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (n : ℤ) - q = j := ⟨_, (Int.toNat_of_nonneg hpos).symm⟩
    have := surjective_homology_divisorialSheafInclusion_sub n f hπ Δ hΔ hΔ0 hΔ1 M K hM D hD
      hDB j
    rw [← hj] at this
    exact this

end MMP.Mori

end
