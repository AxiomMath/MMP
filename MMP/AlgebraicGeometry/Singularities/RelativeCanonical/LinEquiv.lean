module

public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.RingedSpace
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# `K_{X'/X} ≡_lin K_{X'} - μ^*K_X` (Lazarsfeld (9.1))

Let `μ : X' ⟶ X` be a birational morphism of varieties of dimension `n` over `k`, with `X`
non-singular. The relative canonical divisor `K_{X'/X}` is the divisor of the Jacobian section
`j_μ : μ^*ω_X ⟶ ω_{X'}`, `ω = Ω^n`; it is effective, and `𝒪_{X'}(K_{X'/X}) ⊗ μ^*ω_X ≅ ω_{X'}`,
i.e. `K_{X'/X} + μ^*K_X ≡_lin K_{X'}`.

This follows from a statement about any regular homomorphism `φ : L ⟶ M` of line bundles with
divisor `D` on a scheme, when `M ≅ 𝒪_X(B)` for a Cartier divisor `B`: seen inside `𝓜_X`, the
image of `φ` is `𝒪_X(B - D)`. Indeed, on an open `U` trivializing `L` by `e` on which `B` has
the local equation `g`, `φ(e) = r g⁻¹` with `r` a local equation of `D`, and `r g⁻¹` generates
`𝒪_X(B - D)|_U`, whose local equation is `g r⁻¹`. So `φ` is an isomorphism `L ≅ 𝒪_X(B - D)`,
and `𝒪_X(D) ⊗ L ≅ 𝒪_X(D) ⊗ 𝒪_X(B - D) ≅ 𝒪_X(B) ≅ M`.

## Main definitions

* `MMP.Intersection.IsDivisorOfHom.toLineBundleSub`: for `φ : L ⟶ 𝒪_X(B)` with divisor `D`,
  the morphism `L ⟶ 𝒪_X(B - D)`, `t ↦ φ(t)`; `MMP.Intersection.IsDivisorOfHom.isoLineBundleSub`
  is the isomorphism `L ≅ 𝒪_X(B - D)`.

## Main results

* `MMP.Intersection.IsDivisorOfHom.nonempty_lineBundle_tensor_iso`: `𝒪_X(div φ) ⊗ L ≅ M`.
* `MMP.Intersection.IsDivisorOfHom.linearlyEquivalent_add`: `div φ + P ≡_lin B` when
  `𝒪_X(P) ≅ L` and `𝒪_X(B) ≅ M`.
* `MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism`: birational varieties have
  the same dimension.
* `MMP.Intersection.IsRelativeCanonicalDivisor.isEffective`: `K_{X'/X}` is effective.
* `MMP.Intersection.IsRelativeCanonicalDivisor.nonempty_lineBundle_tensor_pullback_iso`:
  `𝒪_{X'}(K_{X'/X}) ⊗ μ^*ω_X ≅ ω_{X'}`.
* `MMP.Intersection.IsRelativeCanonicalDivisor.linearlyEquivalent_add_of_iso`:
  `K_{X'/X} + P ≡_lin K_{X'}` for every divisor `P` with `𝒪_{X'}(P) ≅ μ^*ω_X`.

## Implementation notes

* `ω_{X'}` is represented by a canonical divisor `K_{X'}`, `𝒪_{X'}(K_{X'}) ≅ Ω^n_{X'/k}`, as in
  the statement of the source; the argument uses neither properness of `μ` nor smoothness of
  `X'`, and smoothness of `X` only to know that `μ^*ω_X` is invertible.
* The divisor `μ^*K_X` enters through its line bundle `𝒪_{X'}(μ^*K_X) ≅ μ^*𝒪_X(K_X) ≅ μ^*ω_X`:
  the linear equivalence is stated for every divisor `P` with `𝒪_{X'}(P) ≅ μ^*ω_X`.

## References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry II*][lazarsfeld2004], §9.1.B, (9.1).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry MonoidalCategory

namespace MMP.Intersection

section DivisorOfHom

variable {X : Scheme.{u}} {L : X.Modules} {B D : X.CartierDivisor}
  {φ : L ⟶ MMP.CartierDivisor.sheaf B}

/-- Local data of a regular homomorphism `φ : L ⟶ 𝒪_X(B)` with divisor `D`: near every point there
is an open `W` trivializing `L` by `e`, a local equation `g` of `B` on `W`, and `r` with
`φ(e) = r g⁻¹`, a local equation of `D` on `W`. -/
theorem IsDivisorOfHom.exists_localData [Stacks.Ample.IsInvertibleModule X L]
    (hφ : IsDivisorOfHom φ D) {V : X.Opens} {x : X} (hx : x ∈ V) :
    ∃ (W : X.Opens) (_ : W ≤ V) (e : Γ(L, W)) (g : (X.totalQuotientSheaf.obj.obj (op W))ˣ)
      (hg : IsLocalEquationOn B W g) (r : Γ(X, W)) (hr : IsUnit (toTotalQuotient W r)),
      x ∈ W ∧ IsTrivializingGenerator L W e ∧ φ.app W e = r • MMP.CartierDivisor.invSection hg ∧
        IsLocalEquationOn D W hr.unit := by
  obtain ⟨U, hUV, e, hxU, he⟩ := exists_isTrivializingGenerator L hx
  obtain ⟨U', hxU', g, hg⟩ := exists_isLocalEquationOn B x
  have hg' := isLocalEquationOn_resUnit (homOfLE (inf_le_right : U ⊓ U' ≤ U')) hg
  have he' := he.res (inf_le_left : U ⊓ U' ≤ U)
  obtain ⟨r, hr⟩ := (MMP.CartierDivisor.isTrivializingGenerator_invSection hg').bijective.2
    (φ.app (U ⊓ U') (L.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op e))
  obtain ⟨hu, hloc⟩ := hφ.2.2 _ _ _ he' (MMP.CartierDivisor.isTrivializingGenerator_invSection hg')
      r hr.symm
  exact ⟨U ⊓ U', inf_le_left.trans hUV, _, _, hg', r, hu, ⟨hxU, hxU'⟩, he', hr.symm, hloc⟩

/-- If `φ(e) = r • g⁻¹` on `W` and `t|_W = b • e`, then in `𝓜_X` the restriction of `φ(t)` to `W`
is `b * (r * g⁻¹)`. -/
theorem IsDivisorOfHom.sectionVal_app_res {V W : X.Opens} (hWV : W ≤ V) (t : Γ(L, V))
    {e : Γ(L, W)} {g : (X.totalQuotientSheaf.obj.obj (op W))ˣ} (hg : IsLocalEquationOn B W g)
    {r b : Γ(X, W)} (hre : φ.app W e = r • MMP.CartierDivisor.invSection hg)
    (hb : b • e = L.presheaf.map (homOfLE hWV).op t) :
    X.totalQuotientSheaf.obj.map (homOfLE hWV).op
        (MMP.CartierDivisorSheaf.sectionVal (φ.val.app (op V) t)) =
      toTotalQuotient W b * (toTotalQuotient W r * ↑g⁻¹) := by
  have h1 : X.totalQuotientSheaf.obj.map (homOfLE hWV).op (MMP.CartierDivisorSheaf.sectionVal
      (φ.val.app (op V) t)) =
      MMP.CartierDivisorSheaf.sectionVal (φ.app W (L.presheaf.map (homOfLE hWV).op t)) := by
    change MMP.CartierDivisorSheaf.sectionVal
      ((MMP.CartierDivisor.sheaf B).presheaf.map (homOfLE hWV).op (φ.app V t)) = _
    congr 1
    exact (PresheafOfModules.naturality_apply φ.val (homOfLE hWV).op t).symm
  rw [h1, ← hb, Scheme.Modules.Hom.app_smul, hre, MMP.CartierDivisor.sectionVal_smul,
      MMP.CartierDivisor.sectionVal_smul]
  rfl

/-- The values of a regular homomorphism `φ : L ⟶ 𝒪_X(B)` with divisor `D` lie in
`𝒪_X(B - D)`. -/
theorem IsDivisorOfHom.mem_lineBundleSections_sub [Stacks.Ample.IsInvertibleModule X L]
    (hφ : IsDivisorOfHom φ D) {V : X.Opens} (t : Γ(L, V)) :
    MMP.CartierDivisorSheaf.sectionVal (φ.app V t) ∈ lineBundleSections (B - D) V := by
  refine mem_lineBundleSections_of_locally _ fun x hx => ?_
  obtain ⟨W, hWV, e, g, hg, r, hr, hxW, he, hre, hloc⟩ := hφ.exists_localData hx
  refine ⟨W, homOfLE hWV, hxW, ?_⟩
  have hBD : IsLocalEquationOn (B - D) W (g * hr.unit⁻¹) := by
    rw [sub_eq_add_neg]; exact hg.mul hloc.inv
  obtain ⟨b, hb⟩ := he.bijective.2 (L.presheaf.map (homOfLE hWV).op t)
  refine (mem_lineBundleSections_iff_of_isLocalEquationOn' hBD _).2 ⟨b, ?_⟩
  refine ((sectionVal_app_res hWV t hg hre hb).trans ?_).symm
  rw [mul_inv_rev, inv_inv, Units.val_mul, hr.unit_spec]

/-- A regular homomorphism `φ : L ⟶ 𝒪_X(B)` with divisor `D` takes values in `𝒪_X(B - D)`:
the morphism `L ⟶ 𝒪_X(B - D)`, `t ↦ φ(t)`, both sheaves seen inside `𝓜_X`. -/
def IsDivisorOfHom.toLineBundleSub [Stacks.Ample.IsInvertibleModule X L]
    (hφ : IsDivisorOfHom φ D) : L ⟶ MMP.CartierDivisor.sheaf (B - D) :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    { app := fun V => ModuleCat.ofHom
        { toFun := fun t => MMP.CartierDivisor.sectionOfMem
            (hφ.mem_lineBundleSections_sub (V := V.unop) t)
          map_add' := fun t t' => Subtype.ext
            (congrArg (MMP.CartierDivisorSheaf.sectionVal (D := B) (U := V.unop))
              ((φ.val.app V).hom.map_add t t'))
          map_smul' := fun a t => Subtype.ext
            (congrArg (MMP.CartierDivisorSheaf.sectionVal (D := B) (U := V.unop))
              ((φ.val.app V).hom.map_smul a t)) }
      naturality := fun {V W} i => by
        refine ModuleCat.hom_ext (LinearMap.ext fun t => Subtype.ext ?_)
        exact congrArg (MMP.CartierDivisorSheaf.sectionVal (D := B) (U := W.unop))
          (PresheafOfModules.naturality_apply φ.val i t) }

/-- In `𝓜_X`, the section `hφ.toLineBundleSub t` of `𝒪_X(B - D)` is `φ(t)`. -/
theorem IsDivisorOfHom.sectionVal_toLineBundleSub_app [Stacks.Ample.IsInvertibleModule X L]
    (hφ : IsDivisorOfHom φ D) {V : X.Opens} (t : Γ(L, V)) :
    MMP.CartierDivisorSheaf.sectionVal (hφ.toLineBundleSub.val.app (op V) t) =
        MMP.CartierDivisorSheaf.sectionVal (φ.val.app (op V) t) := rfl

/-- `hφ.toLineBundleSub t = σ` exactly when `φ(t)` and `σ` agree in `𝓜_X`. -/
theorem IsDivisorOfHom.toLineBundleSub_app_eq_iff [Stacks.Ample.IsInvertibleModule X L]
    (hφ : IsDivisorOfHom φ D) {V : X.Opens} (t : Γ(L, V))
    (σ : Γ(MMP.CartierDivisor.sheaf (B - D), V)) :
    hφ.toLineBundleSub.val.app (op V) t = σ ↔
      MMP.CartierDivisorSheaf.sectionVal (φ.val.app (op V) t) =
        MMP.CartierDivisorSheaf.sectionVal σ :=
  ⟨fun h => h ▸ rfl, (MMP.CartierDivisorSheaf.sectionVal_injective ·)⟩

/-- The morphism `L ⟶ 𝒪_X(B - D)`, `t ↦ φ(t)`, is an isomorphism. -/
instance IsDivisorOfHom.isIso_toLineBundleSub [Stacks.Ample.IsInvertibleModule X L]
    (hφ : IsDivisorOfHom φ D) : IsIso hφ.toLineBundleSub := by
  have hinj : ∀ V : (X.Opens)ᵒᵖ, Function.Injective (hφ.toLineBundleSub.val.app V) := by
    intro V t t' htt
    have h0 : MMP.CartierDivisorSheaf.sectionVal (φ.val.app (op V.unop) (t - t')) = 0 := by
      have : hφ.toLineBundleSub.val.app V (t - t') = 0 := by rw [map_sub, htt, sub_self]
      exact (hφ.toLineBundleSub_app_eq_iff (V := V.unop) _ 0).1 this
    rw [← sub_eq_zero]
    choose W hW e g hg r hr hxW he hre hloc using
      fun x : V.unop => hφ.exists_localData x.2
    refine TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf X.ringCatSheaf).obj L) W
      V.unop (fun x => homOfLE (hW x)) (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxW ⟨y, hy⟩⟩)
      _ _ fun x => ?_
    obtain ⟨b, hb⟩ := (he x).bijective.2 (L.presheaf.map (homOfLE (hW x)).op (t - t'))
    have h1 := sectionVal_app_res (hW x) (t - t') (hg x) (hre x) hb
    rw [h0, map_zero] at h1
    have hu : IsUnit (toTotalQuotient (W x) (r x) * ↑(g x)⁻¹) := (hr x).mul (g x)⁻¹.isUnit
    have hb0 : toTotalQuotient (W x) b = 0 := hu.mul_left_eq_zero.mp h1.symm
    have hb0' : b = 0 := injective_toTotalQuotient _ (by rw [hb0, map_zero])
    change L.presheaf.map (homOfLE (hW x)).op (t - t') = L.presheaf.map (homOfLE (hW x)).op 0
    rw [← hb, hb0']
    exact (zero_smul _ _).trans (map_zero _).symm
  have hsurj : TopCat.Presheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).map hφ.toLineBundleSub).hom := by
    refine (TopCat.Presheaf.isLocallySurjective_iff _).2 fun V σ x hx => ?_
    obtain ⟨W, hW, e, g, hg, r, hr, hxW, he, hre, hloc⟩ := hφ.exists_localData hx
    have hBD : IsLocalEquationOn (B - D) W (g * hr.unit⁻¹) := by
      rw [sub_eq_add_neg]; exact hg.mul hloc.inv
    obtain ⟨a, ha⟩ := (mem_lineBundleSections_iff_of_isLocalEquationOn' hBD _).1
      (res_mem (B - D) hW (MMP.CartierDivisor.sectionVal_mem_lineBundleSections σ))
    refine ⟨W, hW, ⟨a • e, ?_⟩, hxW⟩
    refine (hφ.toLineBundleSub_app_eq_iff (a • e) _).2 ?_
    have h1 := sectionVal_app_res (le_refl W) (a • e) hg hre (modules_map_id L _).symm
    rw [totalQuotient_map_id] at h1
    rw [h1]
    change _ = X.totalQuotientSheaf.obj.map (homOfLE hW).op
      (MMP.CartierDivisorSheaf.sectionVal σ)
    rw [← ha, mul_inv_rev, inv_inv, Units.val_mul, hr.unit_spec]
  have hiso := (Sheaf.isLocallyBijective_iff_isIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).map hφ.toLineBundleSub)).mp
      ⟨Presheaf.isLocallyInjective_of_injective _ _ hinj, hsurj⟩
  have hrefl : (SheafOfModules.toSheaf X.ringCatSheaf).ReflectsIsomorphisms := inferInstance
  exact @isIso_of_reflects_iso _ _ _ _ _ _ hφ.toLineBundleSub
    (SheafOfModules.toSheaf X.ringCatSheaf) hiso hrefl

/-- **The line bundle of the divisor of a homomorphism.** If `φ : L ⟶ 𝒪_X(B)` is a regular
homomorphism from an invertible module with divisor `D`, then `L ≅ 𝒪_X(B - D)`. -/
def IsDivisorOfHom.isoLineBundleSub [Stacks.Ample.IsInvertibleModule X L]
    (hφ : IsDivisorOfHom φ D) : L ≅ MMP.CartierDivisor.sheaf (B - D) :=
  asIso hφ.toLineBundleSub

/-- The forward map of `hφ.isoLineBundleSub` is `hφ.toLineBundleSub`. -/
@[simp]
theorem IsDivisorOfHom.isoLineBundleSub_hom [Stacks.Ample.IsInvertibleModule X L]
    (hφ : IsDivisorOfHom φ D) : hφ.isoLineBundleSub.hom = hφ.toLineBundleSub := rfl

end DivisorOfHom

section Iso

variable {X : Scheme.{u}} {L M N : X.Modules} {D : X.CartierDivisor} {φ : L ⟶ M}

/-- The divisor of a homomorphism does not change when its target is replaced by an isomorphic
module. -/
theorem IsDivisorOfHom.comp_inv (hφ : IsDivisorOfHom φ D) (β : N ≅ M) :
    IsDivisorOfHom (φ ≫ β.inv) D := by
  have key : ∀ (U : X.Opens) (e : Γ(L, U)) (e' : Γ(N, U)) (r : Γ(X, U)),
      (φ ≫ β.inv).app U e = r • e' → φ.app U e = r • β.hom.app U e' := by
    intro U e e' r h
    rw [← Scheme.Modules.Hom.app_smul, ← h, ← ConcreteCategory.comp_apply,
      ← Scheme.Modules.Hom.comp_app, Category.assoc, β.inv_hom_id, Category.comp_id]
  refine ⟨fun U e e' he he' r h => hφ.1 U e _ he (he'.map_iso β) r (key U e e' r h), hφ.2.1,
    fun U e e' he he' r h => hφ.2.2 U e _ he (he'.map_iso β) r (key U e e' r h)⟩

/-- **Lazarsfeld (9.1), for line bundles.** If `φ : L ⟶ M` is a regular homomorphism of
invertible modules with divisor `D`, and `M ≅ 𝒪_X(B)`, then `𝒪_X(D) ⊗ L ≅ M`. -/
theorem IsDivisorOfHom.nonempty_lineBundle_tensor_iso [Stacks.Ample.IsInvertibleModule X L]
    (hφ : IsDivisorOfHom φ D) {B : X.CartierDivisor} (β : MMP.CartierDivisor.sheaf B ≅ M) :
    Nonempty (MMP.CartierDivisor.sheaf D ⊗ L ≅ M) :=
  ⟨MMP.CartierDivisorSheaf.tensorIso (Iso.refl _) (hφ.comp_inv β).isoLineBundleSub ≪≫
    MMP.CartierDivisorSheaf.sheafMulIso D (B - D) ≪≫ eqToIso (congrArg MMP.CartierDivisor.sheaf
        (add_sub_cancel D B)) ≪≫ β⟩

/-- **Lazarsfeld (9.1), for divisors.** If `φ : L ⟶ M` is a regular homomorphism of invertible
modules with divisor `D`, `M ≅ 𝒪_X(B)` and `L ≅ 𝒪_X(P)`, then `D + P ≡_lin B`. -/
theorem IsDivisorOfHom.linearlyEquivalent_add [Stacks.Ample.IsInvertibleModule X L]
    (hφ : IsDivisorOfHom φ D) {B P : X.CartierDivisor} (β : MMP.CartierDivisor.sheaf B ≅ M)
    (π : MMP.CartierDivisor.sheaf P ≅ L) : LinearlyEquivalent (D + P) B := by
  have h := (MMP.CartierDivisor.nonempty_sheaf_iso_iff P (B - D)).1 ⟨π ≪≫ (hφ.comp_inv
      β).isoLineBundleSub⟩
  unfold LinearlyEquivalent at h ⊢
  convert h using 1
  abel

end Iso

/-! ### The relative canonical divisor -/

section RelativeCanonical

variable {k : Type u} [Field k] {X X' : Scheme.{u}}

/-- If `μ : X' ⟶ X` is a birational morphism of varieties over `k`, then `X` and `X'` have the
same topological Krull dimension. -/
theorem topologicalKrullDim_eq_of_isBirationalMorphism (sX : X ⟶ Spec (.of k))
    (sX' : X' ⟶ Spec (.of k)) [MMP.Mori.IsVariety k sX] [MMP.Mori.IsVariety k sX']
    {μ : X' ⟶ X} (hμ : MMP.Mori.IsBirationalMorphism μ) :
    topologicalKrullDim X = topologicalKrullDim X' := by
  obtain ⟨W, hWne, hW⟩ := hμ.exists_isOpenImmersion
  have : Nonempty W := hWne.to_subtype
  rw [AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen k X sX _
      (W.ι ≫ μ).isOpenEmbedding.isOpen_range (Set.range_nonempty _),
    AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen k X' sX' _ W.isOpen hWne]
  exact ((W.ι ≫ μ).isOpenEmbedding.toIsEmbedding.toHomeomorph).isHomeomorph
    |>.topologicalKrullDim_eq.symm

/-- `K_{X'/X}` is effective: it is the divisor of the Jacobian section. -/
@[mmp "lem_p09a_relative_canonical_divisor_linear_equivalence"]
theorem IsRelativeCanonicalDivisor.isEffective (sX : X ⟶ Spec (.of k)) [IsIntegral X']
    {μ : X' ⟶ X} (hμ : MMP.Mori.IsBirationalMorphism μ) {K : X'.CartierDivisor}
    (hK : IsRelativeCanonicalDivisor sX μ K) : IsEffective K := by
  obtain ⟨_, _, hdiv⟩ := hK.exists_isDivisorOfHom sX hμ
  exact hdiv.2.1

variable [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))]

omit [X'.Over (Spec (.of k))] in
/-- The pull-back `μ^*Ω^n_{X/k}` is invertible when `X` is a non-singular variety of
dimension `n`. -/
theorem isInvertibleModule_pullback_relativeDifferentialForms
    [MMP.Mori.IsVariety k (X ↘ Spec (.of k))] (hsmX : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of k)))
    (μ : X' ⟶ X) {n : ℕ} (hn : topologicalKrullDim X = n) :
    Stacks.Ample.IsInvertibleModule X' ((Scheme.Modules.pullback μ).obj
      (Scheme.Hom.relativeDifferentialForms (X ↘ Spec (.of k)) n)) := by
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) :=
    AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation (X ↘ Spec (.of k)) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : Smooth (X ↘ Spec (.of k)) := (MMP.Mori.isSmoothScheme_iff _).mp hsmX
  have := smoothOfRelativeDimension_of_isVariety (X ↘ Spec (.of k)) n hn
  have h := Stacks.Discriminant.isInvertible_relativeDifferentialForms (X ↘ Spec (.of k)) n
  exact @Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback _ _
    μ.toLRSHom.toShHom _ h

/-- **Lazarsfeld (9.1).** Let `μ : X' ⟶ X` be a birational morphism of varieties over `k` of
dimension `n`, with `X` non-singular, and let `K_{X'}` be a canonical divisor of `X'`. Then
`𝒪_{X'}(K_{X'/X}) ⊗ μ^*ω_X ≅ ω_{X'}`, where `ω = Ω^n`. -/
@[mmp "lem_p09a_relative_canonical_divisor_linear_equivalence"]
theorem IsRelativeCanonicalDivisor.nonempty_lineBundle_tensor_pullback_iso
    [MMP.Mori.IsVariety k (X ↘ Spec (.of k))] (hsmX : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of k)))
    [MMP.Mori.IsVariety k (X' ↘ Spec (.of k))] {μ : X' ⟶ X} [μ.IsOver (Spec (.of k))]
    (hμ : MMP.Mori.IsBirationalMorphism μ) {K KX' : X'.CartierDivisor}
    (hK : IsRelativeCanonicalDivisor (X ↘ Spec (.of k)) μ K) (hKX' : IsCanonicalDivisor k X' KX') :
    ∃ n : ℕ, Scheme.dimension X' = n ∧
      Nonempty (MMP.CartierDivisor.sheaf K ⊗ (Scheme.Modules.pullback μ).obj
        (Scheme.Hom.relativeDifferentialForms (X ↘ Spec (.of k)) n) ≅
          Scheme.Hom.relativeDifferentialForms (X' ↘ Spec (.of k)) n) := by
  obtain ⟨n, hn, hdiv⟩ := hK.exists_isDivisorOfHom _ hμ
  obtain ⟨m, hm, ⟨β⟩⟩ := hKX'
  obtain rfl : m = n := by exact_mod_cast hm.symm.trans hn
  have hdim := (topologicalKrullDim_eq_of_isBirationalMorphism (X ↘ Spec (.of k))
    (X' ↘ Spec (.of k)) hμ).trans hn
  have := isInvertibleModule_pullback_relativeDifferentialForms hsmX μ hdim
  have e : μ ≫ (X ↘ Spec (.of k)) = X' ↘ Spec (.of k) := CategoryTheory.comp_over μ _
  refine ⟨m, hm, ?_⟩
  rw [← e] at β ⊢
  exact hdiv.nonempty_lineBundle_tensor_iso β

/-- **Lazarsfeld (9.1), `K_{X'/X} + μ^*K_X ≡_lin K_{X'}`**, for a divisor `P` on `X'` with
`𝒪_{X'}(P) ≅ μ^*ω_X` in the role of `μ^*K_X`: under the hypotheses of
`MMP.Intersection.IsRelativeCanonicalDivisor.nonempty_lineBundle_tensor_pullback_iso`,
`K_{X'/X} + P ≡_lin K_{X'}`. -/
@[mmp "lem_p09a_relative_canonical_divisor_linear_equivalence"]
theorem IsRelativeCanonicalDivisor.linearlyEquivalent_add_of_iso
    [MMP.Mori.IsVariety k (X ↘ Spec (.of k))] (hsmX : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of k)))
    [MMP.Mori.IsVariety k (X' ↘ Spec (.of k))] {μ : X' ⟶ X} [μ.IsOver (Spec (.of k))]
    (hμ : MMP.Mori.IsBirationalMorphism μ) {K KX' P : X'.CartierDivisor}
    (hK : IsRelativeCanonicalDivisor (X ↘ Spec (.of k)) μ K) (hKX' : IsCanonicalDivisor k X' KX')
    (hP : ∃ n : ℕ, Scheme.dimension X = n ∧ Nonempty (MMP.CartierDivisor.sheaf P ≅
      (Scheme.Modules.pullback μ).obj
        (Scheme.Hom.relativeDifferentialForms (X ↘ Spec (.of k)) n))) :
    LinearlyEquivalent (K + P) KX' := by
  obtain ⟨n, hn, hdiv⟩ := hK.exists_isDivisorOfHom _ hμ
  obtain ⟨m, hm, ⟨β⟩⟩ := hKX'
  obtain rfl : m = n := by exact_mod_cast hm.symm.trans hn
  have hdim := (topologicalKrullDim_eq_of_isBirationalMorphism (X ↘ Spec (.of k))
    (X' ↘ Spec (.of k)) hμ).trans hn
  obtain ⟨p, hp, ⟨π⟩⟩ := hP
  obtain rfl : p = m := by exact_mod_cast hp.symm.trans hdim
  have := isInvertibleModule_pullback_relativeDifferentialForms hsmX μ hdim
  have e : μ ≫ (X ↘ Spec (.of k)) = X' ↘ Spec (.of k) := CategoryTheory.comp_over μ _
  rw [← e] at β
  exact hdiv.linearlyEquivalent_add β π

end RelativeCanonical

end MMP.Intersection
