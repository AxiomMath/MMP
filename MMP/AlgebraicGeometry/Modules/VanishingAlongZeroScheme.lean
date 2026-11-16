module

public import MMP.AlgebraicGeometry.ChowForm.FibreRestriction

/-!
# Sections vanishing along the zero scheme of a section of an invertible module

Let `X` be an integral scheme, `N` an invertible `𝒪_X`-module, `s ≠ 0` a global section of `N`
with zero scheme `i : Z = Z(s) ⟶ X`, and `E` a finite locally free `𝒪_X`-module. Then a global
section of `E ⊗ N` whose restriction to `Z` vanishes is `s` times a global section of `E`:
the sequence

`0 ⟶ Γ(X, E) --(· s)--> Γ(X, E ⊗ N) ⟶ Γ(Z, i^*(E ⊗ N))`

is exact. Equivalently, the kernel of `E ⊗ N ⟶ i_* i^*(E ⊗ N)` is `I_Z · (E ⊗ N) = E ⊗ 𝒪(Z) ⊗
𝒪(-Z) ≅ E`, and global sections are left exact.

## Main results

* `MMP.Mori.exists_eq_mulSection_of_pullback_eq_zero`: a section of `E ⊗ N` vanishing on
  `Z(s)` is the image of a section of `E` under multiplication by `s`.
* `MMP.Mori.exists_eq_mulSection_of_pullback_eq_zero_of_iso`: the same for a module `ℰ`
  identified with `E ⊗ N`, e.g. `E = ℰ ⊗ N^{-1}`.
* `MMP.Mori.eq_zero_of_pullback_eq_zero_of_iso`: if moreover `Γ(X, E) = 0`, restriction of
  sections of `ℰ` to `Z(s)` is injective.
* `MMP.Mori.germ_mem_stalk_smul_top_of_pullback_eq_zero`: for any closed subscheme cut out by
  `I`, the germ at `y` of a section restricting to zero lies in `I_y · F_y`.

## Implementation notes

The statement is proved on stalks. At a point `y`, write `N_y = 𝒪_{X,y} · b` and `s_y = c • b`;
the ideal of `Z(s)` at `y` is `(c)` (`zeroScheme_ideal_of_trivialization`), and `c ≠ 0` because
`X` is integral and `s ≠ 0`. Multiplication by `s` on stalks is `E_y ⊗ (r ↦ r • s_y)`, which is
injective since `E_y` is free, and whose image contains `c · (E ⊗ N)_y`. The germ of a section
vanishing on `Z` lies in `I_{Z,y} · (E ⊗ N)_y`, since `(i^* (E ⊗ N))_z = 𝒪_{Z,z} ⊗ (E ⊗ N)_y`
(Stacks 0098) and `𝒪_{X,y} ⟶ 𝒪_{Z,z}` is surjective with kernel `I_{Z,y}`. A section of a sheaf
which lies stalkwise in the image of a stalkwise injective morphism lifts.

Multiplication by `s` is the morphism `E ≅ E ⊗ 𝒪_X ⟶ E ⊗ N`, the right unit constraint
followed by `E ⊗ (𝒪_X ⟶ N)`, where `𝒪_X ⟶ N` is the morphism `1 ↦ s`
(`Stacks.EnriquesSeveriZariski.sectionHom`). Taking `E = ℰ ⊗ N^{-1}` recovers the form
"a section of `ℰ` vanishing on `Z` comes from `Γ(X, ℰ ⊗ N^{-1})`".

## References

* [R. Hartshorne, *Algebraic Geometry*][Hartshorne1977], Proposition II.6.18
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

namespace MMP.Mori

section Stalks

variable {X : Scheme.{u}} (N : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] (s : Γ(N, ⊤))

/-- On the stalk at `y`, the image of multiplication by `s`, `𝒪_{X,y} ⟶ N_y`, contains
`I_y · N_y`, where `I` is the ideal of the zero scheme of `s`. -/
theorem smul_mem_range_stalkLinearMap_sectionHom (y : X) {c : X.presheaf.stalk y}
    (hc : c ∈ IdealSheafData.stalk (Stacks.Divisors.zeroScheme X N s) y)
    (n : N.presheaf.stalk y) :
    c • n ∈ LinearMap.range
      (stalkLinearMap _ _ (Stacks.EnriquesSeveriZariski.sectionHom N s) y) := by
  have : Stacks.Ample.IsInvertibleModule X N := ‹_›
  obtain ⟨V, hyV, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at N y
  obtain ⟨-, ⟨U, hU, rfl⟩, hyU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hyV V.isOpen
  have hUV' : U ≤ V := hUV
  set a : Γ(X, U) := Stacks.NonvanishingOpen.triv t (homOfLE hUV')
    (N.presheaf.map (homOfLE le_top).op s)
  have hideal : (Stacks.Divisors.zeroScheme X N s).ideal ⟨U, hU⟩ = Ideal.span {a} :=
    AlgebraicGeometry.zeroScheme_ideal_of_trivialization X N s ⟨U, hU⟩
      (t.θ U (homOfLE hUV')) a rfl
  set b := (N.presheaf.germ V y hyV).hom (Stacks.NonvanishingOpen.basis t)
  have hs : (N.presheaf.Γgerm y).hom s = (X.presheaf.germ U y hyU).hom a • b := by
    have e1 := Stacks.SectionProduct.eq_triv_smul_res_basis t (homOfLE hUV')
      (N.presheaf.map (homOfLE le_top).op s)
    have h1 : (N.presheaf.Γgerm y).hom s =
        (N.presheaf.germ U y hyU).hom (N.presheaf.map (homOfLE le_top).op s) :=
      (TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE le_top) y hyU s).symm
    rw [h1, e1, Scheme.Modules.germ_smul, TopCat.Presheaf.germ_res_apply]
  rw [IdealSheafData.stalk_eq_map_germ _ y ⟨U, hU⟩ hyU, hideal, Ideal.map_span,
    Set.image_singleton, Ideal.mem_span_singleton'] at hc
  obtain ⟨d, rfl⟩ := hc
  obtain ⟨r, rfl⟩ := Stacks.SectionProduct.exists_smul_germ_basis t hyV n
  refine ⟨(Stacks.Ample.unitStalkEquiv X y).symm (d * r), ?_⟩
  rw [Stacks.EnriquesSeveriZariski.stalkLinearMap_sectionHom, LinearEquiv.apply_symm_apply, hs,
    smul_smul, smul_smul]
  congr 1
  ring

/-- On an integral scheme, multiplication by a nonzero section `s` of an invertible module is
injective on every stalk. -/
theorem injective_stalkLinearMap_sectionHom [IsIntegral X] (hs : s ≠ 0) (y : X) :
    Function.Injective
      (stalkLinearMap _ _ (Stacks.EnriquesSeveriZariski.sectionHom N s) y) := by
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N := ‹_›
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  rw [Stacks.EnriquesSeveriZariski.stalkLinearMap_sectionHom] at hz
  obtain ⟨φ⟩ := Stacks.InvertibleStalk.nonempty_linearEquiv_stalk N y
  have h0 : (N.presheaf.Γgerm y).hom s ≠ 0 := Stacks.ChernCap42.germ_ne_zero_of_ne_zero N s hs y
  have h1 : φ ((N.presheaf.Γgerm y).hom s) ≠ 0 := by
    rwa [ne_eq, LinearEquiv.map_eq_zero_iff]
  have h2 := congrArg φ hz
  rw [map_smul, map_zero, smul_eq_mul] at h2
  have h3 : Stacks.Ample.unitStalkEquiv X y z = 0 := (mul_eq_zero.mp h2).resolve_right h1
  exact (Stacks.Ample.unitStalkEquiv X y).map_eq_zero_iff.mp h3

end Stalks

section Tensor

variable {X : Scheme.{u}} (E : X.Modules) {A B : X.Modules} (g : A ⟶ B) (y : X)

/-- Tensoring on the left by a module with flat stalk at `y` keeps a morphism injective on the
stalk at `y`. -/
theorem injective_stalkLinearMap_tensorLeftMap_of_injective
    [Module.Flat (X.presheaf.stalk y) (E.presheaf.stalk y)]
    (hg : Function.Injective (stalkLinearMap A B g y)) :
    Function.Injective (stalkLinearMap _ _ (Scheme.Modules.tensorLeftMap E g) y) := by
  intro z z' h
  have h' := congrArg (AlgebraicGeometry.tensorStalkEquiv E B y) h
  rw [Stacks.EnriquesSeveriZariski.tensorStalkEquiv_tensorLeftMap,
    Stacks.EnriquesSeveriZariski.tensorStalkEquiv_tensorLeftMap] at h'
  exact (AlgebraicGeometry.tensorStalkEquiv E A y).injective
    (Module.Flat.lTensor_preserves_injective_linearMap _ hg h')

/-- If the image of `g` on the stalk at `y` contains `J · B_y`, then the image of `E ⊗ g` on the
stalk at `y` contains `J · (E ⊗ B)_y`. -/
theorem mem_range_stalkLinearMap_tensorLeftMap (J : Ideal (X.presheaf.stalk y))
    (hg : ∀ c ∈ J, ∀ n : B.presheaf.stalk y, c • n ∈ LinearMap.range (stalkLinearMap A B g y))
    {t : (Scheme.Modules.tensorObj E B).presheaf.stalk y}
    (ht : t ∈ J • (⊤ : Submodule (X.presheaf.stalk y)
      ((Scheme.Modules.tensorObj E B).presheaf.stalk y))) :
    t ∈ LinearMap.range (stalkLinearMap _ _ (Scheme.Modules.tensorLeftMap E g) y) := by
  have key : ∀ w ∈ J • (⊤ : Submodule (X.presheaf.stalk y)
      (E.presheaf.stalk y ⊗[X.presheaf.stalk y] B.presheaf.stalk y)),
      w ∈ LinearMap.range (LinearMap.lTensor (E.presheaf.stalk y) (stalkLinearMap A B g y)) := by
    intro w hw
    refine Submodule.smul_induction_on hw (fun c hc w hw' => ?_) (fun _ _ h1 h2 => add_mem h1 h2)
    clear hw'
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
        obtain ⟨z, hz⟩ := hg c hc n
        exact ⟨m ⊗ₜ z, by rw [LinearMap.lTensor_tmul, hz, TensorProduct.tmul_smul]⟩
    | add w w' h h' => simpa only [smul_add] using add_mem h h'
  have ht' : AlgebraicGeometry.tensorStalkEquiv E B y t ∈ J • (⊤ : Submodule (X.presheaf.stalk y)
      (E.presheaf.stalk y ⊗[X.presheaf.stalk y] B.presheaf.stalk y)) :=
    Stacks.SheafOfModules.map_mem_ideal_smul_top J
      (AlgebraicGeometry.tensorStalkEquiv E B y).toLinearMap ht
  obtain ⟨w, hw⟩ := key _ ht'
  refine ⟨(AlgebraicGeometry.tensorStalkEquiv E A y).symm w,
    (AlgebraicGeometry.tensorStalkEquiv E B y).injective ?_⟩
  rwa [Stacks.EnriquesSeveriZariski.tensorStalkEquiv_tensorLeftMap, LinearEquiv.apply_symm_apply]

end Tensor

section Restriction

variable {X : Scheme.{u}}

/-- If `1 ⊗ m = 0` in `B ⊗_A M` for a surjective ring map `A ⟶ B`, then `m ∈ ker · M`. -/
theorem mem_ker_smul_top_of_one_tmul_eq_zero {A B M : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M] (hsurj : Function.Surjective (algebraMap A B))
    {m : M} (h : (1 : B) ⊗ₜ[A] m = 0) :
    m ∈ RingHom.ker (algebraMap A B) • (⊤ : Submodule A M) := by
  set K := RingHom.ker (algebraMap A B)
  let e0 : (A ⧸ K) ≃ₗ[A] B :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hsurj).toLinearEquiv
  have h2 : e0.symm (1 : B) = Ideal.Quotient.mk K 1 := by
    change (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hsurj).symm 1 = _
    rw [map_one, map_one]
    rfl
  have h1 : TensorProduct.quotTensorEquivQuotSMul M K
      (LinearMap.rTensor M e0.symm.toLinearMap ((1 : B) ⊗ₜ[A] m)) = Submodule.Quotient.mk m := by
    rw [LinearMap.rTensor_tmul, LinearEquiv.coe_coe, h2,
      TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [h, map_zero, map_zero] at h1
  exact (Submodule.Quotient.mk_eq_zero _).mp h1.symm

/-- **The germ of a section restricting to zero on a closed subscheme lies in the ideal times the
stalk.** If the restriction of `e ∈ Γ(X, F)` to the closed subscheme cut out by `I` vanishes, then
at every point `y` the germ of `e` lies in `I_y · F_y`. -/
theorem germ_mem_stalk_smul_top_of_pullback_eq_zero (I : X.IdealSheafData) (F : X.Modules)
    (e : Γ(F, ⊤))
    (he : ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app F).val.app
      (op ⊤) e = 0) (y : X) :
    F.presheaf.germ ⊤ y trivial e ∈
      IdealSheafData.stalk I y • (⊤ : Submodule (X.presheaf.stalk y) (F.presheaf.stalk y)) := by
  by_cases hy : y ∈ I.support
  · obtain ⟨z, rfl⟩ : y ∈ Set.range I.subschemeι := by
      rwa [Scheme.IdealSheafData.range_subschemeι]
    let : Algebra (X.presheaf.stalk (I.subschemeι z)) (I.subscheme.presheaf.stalk z) :=
      (I.subschemeι.stalkMap z).hom.toAlgebra
    have hgerm := Scheme.Modules.pullbackStalkEquiv_germ I.subschemeι F z ⊤ trivial e
    have hz : (ConcreteCategory.hom (TopCat.Presheaf.germ
        ((Scheme.Modules.pullback I.subschemeι).obj F).val.presheaf
          (I.subschemeι ⁻¹ᵁ ⊤) z trivial)) 0 = 0 := map_zero _
    have hz' : Scheme.Modules.pullbackStalkEquiv I.subschemeι F z
        (TopCat.Presheaf.germ (C := Ab.{u})
          ((Scheme.Modules.pullback I.subschemeι).obj F).val.presheaf (I.subschemeι ⁻¹ᵁ ⊤) z trivial
          (((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app F).val.app
            (op ⊤) e)) = 0 := by
      rw [he]
      exact (congrArg _ hz).trans (map_zero _)
    have hker : RingHom.ker (algebraMap (X.presheaf.stalk (I.subschemeι z))
        (I.subscheme.presheaf.stalk z)) = IdealSheafData.stalk I (I.subschemeι z) := by
      have h := IdealSheafData.stalk_ker_of_isClosedImmersion I.subschemeι z
      rw [Scheme.IdealSheafData.ker_subschemeι] at h
      exact h.symm
    exact hker ▸ mem_ker_smul_top_of_one_tmul_eq_zero
      (A := X.presheaf.stalk (I.subschemeι z)) (B := I.subscheme.presheaf.stalk z)
      (I.subschemeι.stalkMap_surjective z) (hgerm.symm.trans hz')
  · rw [(IdealSheafData.stalk_eq_top_iff_not_mem_support I y).mpr hy, Submodule.top_smul]
    exact Submodule.mem_top

end Restriction

/-- **A section vanishing along the zero scheme of `s` is divisible by `s`.** Let `X` be an
integral scheme, `N` an invertible `𝒪_X`-module, `s ≠ 0` a global section of `N` with zero scheme
`i : Z(s) ⟶ X`, and `E` a finite locally free `𝒪_X`-module. If a global section `e` of `E ⊗ N`
restricts to zero on `Z(s)`, then `e = e' · s` for a global section `e'` of `E`, multiplication
by `s` being `E ≅ E ⊗ 𝒪_X ⟶ E ⊗ N`. -/
theorem exists_eq_mulSection_of_pullback_eq_zero {X : Scheme.{u}} [IsIntegral X]
    (N : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (s : Γ(N, ⊤)) (hs : s ≠ 0)
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (e : Γ(Scheme.Modules.tensorObj E N, ⊤))
    (he : ((Scheme.Modules.pullbackPushforwardAdjunction
        (Stacks.Divisors.zeroScheme X N s).subschemeι).unit.app
          (Scheme.Modules.tensorObj E N)).val.app (op ⊤) e = 0) :
    ∃ e' : Γ(E, ⊤),
      ((Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) E).inv ≫
        Scheme.Modules.tensorLeftMap E (Stacks.EnriquesSeveriZariski.sectionHom N s)).val.app
          (op ⊤) e' = e := by
  set I := Stacks.Divisors.zeroScheme X N s
  set g := Stacks.EnriquesSeveriZariski.sectionHom N s
  set ρ := Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) E
  have hρ : ∀ y : X, Function.Bijective (stalkLinearMap _ _ ρ.inv y) := fun y =>
    Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_of_inverse _ _ ρ.inv_hom_id
      ρ.hom_inv_id y
  have hT : ∀ y : X, Function.Injective
      (stalkLinearMap _ _ (Scheme.Modules.tensorLeftMap E g) y) := fun y => by
    have hfree : Module.Free (X.presheaf.stalk y) (E.presheaf.stalk y) :=
      (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree E y).1
    have : Module.Flat (X.presheaf.stalk y) (E.presheaf.stalk y) := Module.Flat.of_free
    exact injective_stalkLinearMap_tensorLeftMap_of_injective E g y
      (injective_stalkLinearMap_sectionHom N s hs y)
  have hinj : ∀ y ∈ (⊤ : X.Opens), Function.Injective
      (stalkLinearMap _ _ (ρ.inv ≫ Scheme.Modules.tensorLeftMap E g) y) := by
    intro y _ z z' h
    have h1 := (Scheme.Modules.stalkLinearMap_comp ρ.inv (Scheme.Modules.tensorLeftMap E g) y
      z).symm.trans (h.trans (Scheme.Modules.stalkLinearMap_comp _ _ y z'))
    exact (hρ y).injective (hT y h1)
  have hrange : ∀ y (hy : y ∈ (⊤ : X.Opens)),
      (Scheme.Modules.tensorObj E N).presheaf.germ ⊤ y hy e ∈
        Set.range (stalkLinearMap _ _ (ρ.inv ≫ Scheme.Modules.tensorLeftMap E g) y) := by
    intro y _
    obtain ⟨w, hw⟩ := mem_range_stalkLinearMap_tensorLeftMap E g y (IdealSheafData.stalk I y)
      (fun c hc n => smul_mem_range_stalkLinearMap_sectionHom N s y hc n)
      (germ_mem_stalk_smul_top_of_pullback_eq_zero I _ e he y)
    obtain ⟨v, rfl⟩ := (hρ y).surjective w
    exact ⟨v, (Scheme.Modules.stalkLinearMap_comp _ _ y v).trans hw⟩
  exact MMP.Chow.DeterminantCurveForm.exists_app_eq_of_germ_mem_range_stalkLinearMap
    (ρ.inv ≫ Scheme.Modules.tensorLeftMap E g) ⊤ hinj e hrange

/-- **A section vanishing along the zero scheme of `s` comes from a twist down by `s`.** If `ℰ`
is identified with `E ⊗ N` by `φ`, then a global section of `ℰ` restricting to zero on `Z(s)` is
`φ⁻¹(e' · s)` for a global section `e'` of `E`. With `E = ℰ ⊗ N^{-1}` this is the statement that
a section of `ℰ` vanishing on `Z(s)` comes from `Γ(X, ℰ ⊗ N^{-1})`. -/
theorem exists_eq_mulSection_of_pullback_eq_zero_of_iso {X : Scheme.{u}} [IsIntegral X]
    (N : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (s : Γ(N, ⊤)) (hs : s ≠ 0)
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    {ℰ : X.Modules} (φ : ℰ ≅ Scheme.Modules.tensorObj E N) (e : Γ(ℰ, ⊤))
    (he : ((Scheme.Modules.pullbackPushforwardAdjunction
        (Stacks.Divisors.zeroScheme X N s).subschemeι).unit.app ℰ).val.app (op ⊤) e = 0) :
    ∃ e' : Γ(E, ⊤), φ.inv.val.app (op ⊤)
      (((Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) E).inv ≫
        Scheme.Modules.tensorLeftMap E (Stacks.EnriquesSeveriZariski.sectionHom N s)).val.app
          (op ⊤) e') = e := by
  have hnat : ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Divisors.zeroScheme X N s).subschemeι).unit.app
        (Scheme.Modules.tensorObj E N)).val.app (op ⊤) (φ.hom.val.app (op ⊤) e) =
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X N s).subschemeι ⋙
        Scheme.Modules.pushforward (Stacks.Divisors.zeroScheme X N s).subschemeι).map
          φ.hom).val.app (op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Stacks.Divisors.zeroScheme X N s).subschemeι).unit.app ℰ).val.app (op ⊤) e) :=
    congrArg (fun f => f.val.app (op ⊤) e)
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (Stacks.Divisors.zeroScheme X N s).subschemeι).unit.naturality φ.hom)
  rw [he] at hnat
  obtain ⟨e', he'⟩ := exists_eq_mulSection_of_pullback_eq_zero N s hs E (φ.hom.val.app (op ⊤) e)
    (hnat.trans (map_zero _))
  exact ⟨e', (congrArg _ he').trans (congrArg (fun f => f.val.app (op ⊤) e) φ.hom_inv_id)⟩

/-- **Restriction to the zero scheme is injective when the twist down has no sections.** If
`ℰ ≅ E ⊗ N` and `Γ(X, E) = 0`, a global section of `ℰ` restricting to zero on `Z(s)` is zero. -/
theorem eq_zero_of_pullback_eq_zero_of_iso {X : Scheme.{u}} [IsIntegral X]
    (N : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (s : Γ(N, ⊤)) (hs : s ≠ 0)
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [Subsingleton Γ(E, ⊤)]
    {ℰ : X.Modules} (φ : ℰ ≅ Scheme.Modules.tensorObj E N) (e : Γ(ℰ, ⊤))
    (he : ((Scheme.Modules.pullbackPushforwardAdjunction
        (Stacks.Divisors.zeroScheme X N s).subschemeι).unit.app ℰ).val.app (op ⊤) e = 0) :
    e = 0 := by
  obtain ⟨e', rfl⟩ := exists_eq_mulSection_of_pullback_eq_zero_of_iso N s hs E φ e he
  rw [Subsingleton.elim e' 0]
  exact (congrArg _ (map_zero _)).trans (map_zero _)

end MMP.Mori
