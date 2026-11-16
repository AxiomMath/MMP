module

public import MMP.RingTheory.GradedAlgebra.Veronese
public import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback

/-!
# Finiteness over a Veronese subalgebra, and sections detected on a dominating subvariety

Let `R = ⨁_{m ≥ 0} R_m` be an `ℕ`-graded `A`-algebra which is a domain, and let `d ≥ 1`.
If the Veronese subalgebra `R^(d) = ⨁_m R_{dm}` is a Noetherian ring, then `R` is a finite
`R^(d)`-module: for each residue `i` mod `d`, multiplication by `t^(d-1)` for a nonzero
homogeneous `t` of degree `≡ i` embeds the residue-`i` part of `R` into `R^(d)` as an ideal,
and these finitely many parts span `R`.

Let `p : E ⟶ C` be a proper dominant morphism of complex varieties, with `C` a curve, and let
`M` be an invertible sheaf on `C`. If `i : A ⟶ E` is an integral closed subvariety with
`i ≫ p` dominant, then the restriction `Γ(E, p^*M) → Γ(A, i^*p^*M)` is injective. Over an
affine open `U ⊆ C` on which `M` has a generator `a`, a global section `s` with zero
restriction to `A` is `f • p^*a` on `p⁻¹U` with `i^♯ f = 0`. The ring `Γ(E, p⁻¹U)` is a domain
integral over `Γ(C, U)`, so if `f ≠ 0` some nonzero `r ∈ Γ(C, U)` dies under `(i ≫ p)^♯`,
which dominance forbids. Hence `s` vanishes on a nonempty open, and so everywhere.

## Main results

* `MMP.Fourfold.module_finite_veroneseSubalgebra`: `R` is a finite module over
  `MMP.Fourfold.veroneseSubalgebra 𝒜 d` when the latter is Noetherian and `0 < d`.
* `MMP.injective_restrict_sections_pullback_of_isDominant`: restricting sections of a
  pulled-back invertible sheaf to a dominating integral closed subvariety is injective.

## Implementation notes

The restriction of sections along `i` is the global-sections component of the unit
`p^*M ⟶ i_* i^* p^*M` of the adjunction `Scheme.Modules.pullbackPushforwardAdjunction i`.
The source works at the generic fibre, whose ring of regular functions is a finite field
extension of `K(C)` embedding into `K(A)`. Here the same integrality is used over an affine
open of `C` (`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`), and the embedding
into `K(A)` is replaced by `Ideal.comap_ne_bot_of_integral_mem`. Neither normality of `E` nor
geometric integrality of the generic fibre is used.
-/

@[expose] public section

namespace MMP.Fourfold

open DirectSum

section Veronese

variable {A R : Type*} [CommSemiring A] [CommSemiring R] [Algebra A R]
  (𝒜 : ℕ → Submodule A R) [GradedAlgebra 𝒜]

/-- The `R^(d)`-submodule of `R` spanned by the components `R_n` with `n % d = i`. -/
private def residueSpan (d i : ℕ) : Submodule (veroneseSubalgebra 𝒜 d) R :=
  Submodule.span _ {r | ∃ n, n % d = i ∧ r ∈ 𝒜 n}

variable {𝒜} in
private theorem pow_mul_mem_of_mem {d e n : ℕ} (hd : 0 < d) (hen : e % d = n % d) {t r : R}
    (ht : t ∈ 𝒜 e) (hr : r ∈ 𝒜 n) : t ^ (d - 1) * r ∈ veroneseSubalgebra 𝒜 d := by
  have hmem : t ^ (d - 1) * r ∈ 𝒜 ((d - 1) * e + n) :=
    SetLike.mul_mem_graded (by simpa [smul_eq_mul] using SetLike.pow_mem_graded (d - 1) ht) hr
  have hdvd : d ∣ (d - 1) * e + n := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, Nat.mul_mod, hen, ← Nat.mul_mod, ← Nat.add_mod, ← Nat.succ_mul,
      Nat.succ_eq_add_one, Nat.sub_add_cancel hd, Nat.mul_mod_right]
  obtain ⟨m, hm⟩ := hdvd
  exact mem_veroneseSubalgebra_of_mem (hm ▸ hmem)

variable {𝒜} in
private theorem pow_mul_mem_of_mem_residueSpan {d e i : ℕ} (hd : 0 < d) (hei : e % d = i)
    {t : R} (ht : t ∈ 𝒜 e) {x : R} (hx : x ∈ residueSpan 𝒜 d i) :
    t ^ (d - 1) * x ∈ veroneseSubalgebra 𝒜 d := by
  induction hx using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨n, hn, hr⟩ := hr
    exact pow_mul_mem_of_mem hd (hei.trans hn.symm) ht hr
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact add_mem hx hy
  | smul b x _ hx =>
    rw [Subalgebra.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem b.2 hx

private theorem residueSpan_fg [IsDomain R] {d : ℕ} (hd : 0 < d)
    [IsNoetherianRing (veroneseSubalgebra 𝒜 d)] (i : ℕ) : (residueSpan 𝒜 d i).FG := by
  by_cases h : ∃ e t, e % d = i ∧ t ∈ 𝒜 e ∧ t ≠ 0
  · obtain ⟨e, t, hei, ht, ht0⟩ := h
    set B := veroneseSubalgebra 𝒜 d
    let f : residueSpan 𝒜 d i →ₗ[B] B :=
      { toFun x := ⟨t ^ (d - 1) * x, pow_mul_mem_of_mem_residueSpan hd hei ht x.2⟩
        map_add' x y := Subtype.ext (by simp [mul_add])
        map_smul' b x := Subtype.ext (by
          simp only [SetLike.val_smul, Subalgebra.smul_def, RingHom.id_apply,
            MulMemClass.coe_mul, smul_eq_mul]
          ring) }
    have hf : Function.Injective f := fun x y hxy =>
      Subtype.ext (mul_left_cancel₀ (pow_ne_zero _ ht0) (congrArg Subtype.val hxy))
    exact (Submodule.fg_top _).mp
      (Submodule.fg_of_fg_map_injective f hf (IsNoetherian.noetherian _))
  · push Not at h
    rw [residueSpan, Submodule.span_eq_bot.mpr]
    · exact Submodule.fg_bot
    · rintro r ⟨n, hn, hr⟩
      exact h n r hn hr

end Veronese

/-- A graded domain `R` is a finite module over its `d`-th Veronese subalgebra `R^(d)`,
`d ≥ 1`, as soon as `R^(d)` is a Noetherian ring. -/
@[mmp "lem_fourfold_veronese_residue_modules"]
public theorem module_finite_veroneseSubalgebra {A R : Type*} [CommSemiring A]
    [CommSemiring R] [IsDomain R] [Algebra A R] (𝒜 : ℕ → Submodule A R) [GradedAlgebra 𝒜]
    {d : ℕ} (hd : 0 < d) [IsNoetherianRing (veroneseSubalgebra 𝒜 d)] :
    Module.Finite (veroneseSubalgebra 𝒜 d) R := by
  classical
  rw [Module.finite_def]
  have hsup : (⊤ : Submodule (veroneseSubalgebra 𝒜 d) R) =
      ⨆ i : Fin d, residueSpan 𝒜 d i := by
    refine (eq_top_iff.mpr fun x _ => ?_).symm
    rw [← sum_support_decompose 𝒜 x]
    refine Submodule.sum_mem _ fun n _ => ?_
    exact Submodule.mem_iSup_of_mem (⟨n % d, Nat.mod_lt _ hd⟩ : Fin d)
      (Submodule.subset_span ⟨n, rfl, (decompose 𝒜 x n).2⟩)
  rw [hsup]
  exact Submodule.fg_iSup _ fun i => residueSpan_fg 𝒜 hd i

end MMP.Fourfold

namespace MMP

open CategoryTheory AlgebraicGeometry Opposite

universe u

/-- Restricting a section of a module twice is restricting it once. -/
private theorem map_map_homOfLE {X : Scheme.{u}} (L : X.Modules) {P Q R : X.Opens} (h₁ : Q ≤ P)
    (h₂ : P ≤ R) (σ : Γ(L, R)) :
    L.presheaf.map (homOfLE h₁).op (L.presheaf.map (homOfLE h₂).op σ) =
      L.presheaf.map (homOfLE (h₁.trans h₂)).op σ := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting a section of a module to its own open does nothing. -/
private theorem map_homOfLE_refl {X : Scheme.{u}} (L : X.Modules) {W : X.Opens} (σ : Γ(L, W)) :
    L.presheaf.map (homOfLE (le_refl W)).op σ = σ := by
  rw [show homOfLE (le_refl W) = 𝟙 W from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- A generator of an invertible module over every open inside `K` pulls back, along the unit of
`b^* ⊣ b_*`, to a generator over every open inside `b⁻¹ K`. -/
private theorem bijective_smul_unit_app {X Y : Scheme.{u}} (b : X ⟶ Y) (A : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y A] {K : Y.Opens} (a : Γ(A, K))
    (ha : ∀ (W : Y.Opens) (hW : W ≤ K),
      Function.Bijective (fun c : Γ(Y, W) => c • A.presheaf.map (homOfLE hW).op a))
    (W : X.Opens) (hW : W ≤ b ⁻¹ᵁ K) :
    Function.Bijective (fun c : Γ(X, W) =>
      c • ((Scheme.Modules.pullback b).obj A).presheaf.map (homOfLE hW).op
        (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app A).app K a)) := by
  have hpb : Stacks.Ample.IsInvertibleModule X
      ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).obj A) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback b A
  have hpb' : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).obj A) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hpb
  refine Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
    (X := X.toRingedSpace) _ (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom A (op K) a)
    _ hW fun x hx => ?_
  have h1 := Scheme.Modules.germ_notMem_maximalSmul_of_bijective_smul A a ha (b.base x) (hW hx)
  rwa [← Stacks.NonvanishingLocusRestrict.mem_maximalSmul_germ_pullbackUnit_iff b A a x
    (hW hx), Stacks.NonvanishingPullback.mem_maximalSmul_iff] at h1

/-- A global section of an invertible module on an integral scheme vanishing on a nonempty open
vanishes. -/
private theorem eq_zero_of_map_eq_zero {X : Scheme.{u}} [IsIntegral X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {V : X.Opens} (hV : (V : Set X).Nonempty)
    (s : Γ(L, ⊤)) (hs : L.presheaf.map (homOfLE le_top : V ⟶ ⊤).op s = 0) : s = 0 := by
  have hL : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr ‹_›
  have key : ∀ x : X, ∃ (K : X.Opens) (_ : x ∈ K),
      L.presheaf.map (homOfLE le_top : K ⟶ ⊤).op s = 0 := by
    intro x
    obtain ⟨K, hx, a, ha⟩ : ∃ (K : X.Opens) (_ : x ∈ K) (a : Γ(L, K)), ∀ (W : X.Opens)
        (hW : W ≤ K), Function.Bijective
          (fun c : Γ(X, W) => c • L.presheaf.map (homOfLE hW).op a) :=
      @Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible X.toRingedSpace _ L hL x
    refine ⟨K, hx, ?_⟩
    obtain ⟨g, hg⟩ := (ha K le_rfl).2 (L.presheaf.map (homOfLE le_top : K ⟶ ⊤).op s)
    simp only [map_homOfLE_refl] at hg
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter K.2 V.2 ⟨x, hx⟩ hV
    have : Nonempty (K ⊓ V : X.Opens) := ⟨⟨z, hz⟩⟩
    -- `g` vanishes on `K ⊓ V`, hence on `K` since `X` is integral
    have hg0 : g = 0 := by
      refine map_injective_of_isIntegral X (homOfLE inf_le_left : K ⊓ V ⟶ K) ?_
      rw [map_zero]
      refine (ha (K ⊓ V) inf_le_left).1 ?_
      dsimp only
      rw [zero_smul, ← Scheme.Modules.map_smul, hg, map_map_homOfLE,
        ← map_map_homOfLE L (inf_le_right : K ⊓ V ≤ V) (le_top : V ≤ ⊤), hs, map_zero]
    rw [← hg, hg0, zero_smul]
  choose K hxK hK using key
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨L.presheaf, L.isSheaf⟩ K ⊤
    (fun x => homOfLE le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxK x⟩) s 0
    fun x => ?_
  change L.presheaf.map (homOfLE le_top : K x ⟶ ⊤).op s =
    L.presheaf.map (homOfLE le_top : K x ⟶ ⊤).op 0
  rw [hK x, map_zero]

/-- Sections of the structure sheaf over the preimage of an affine open under a universally
closed morphism are integral over the sections of the base. -/
private theorem isIntegral_app {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversallyClosed f]
    (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).hom.IsIntegral := by
  have : IsAffine U := hU
  have h := isIntegral_appTop_of_universallyClosed (f ∣_ U)
  rw [morphismRestrict_appTop] at h
  have key : ∀ {W : Y.Opens} {V' : X.Opens} (e : V' = f ⁻¹ᵁ W),
      (f.app W ≫ X.presheaf.map (eqToHom e).op).hom.IsIntegral → (f.app W).hom.IsIntegral := by
    rintro W _ rfl he
    simpa using he
  have h2 := key _ h
  rwa [Scheme.Opens.ι_image_top] at h2

/-- Let `p : E ⟶ C` be universally closed from an integral scheme to a reduced one, `U ⊆ C` an
affine open with nonempty preimage, and `i : A ⟶ E` a morphism with `i ≫ p` dominant and
quasi-compact. Then `i^♯ : Γ(E, p⁻¹U) → Γ(A, i⁻¹p⁻¹U)` has trivial kernel. -/
private theorem eq_zero_of_app_eq_zero {E C A : Scheme.{u}} [IsIntegral E] [IsReduced C]
    (p : E ⟶ C) [UniversallyClosed p] (i : A ⟶ E) [IsDominant (i ≫ p)]
    [QuasiCompact (i ≫ p)] {U : C.Opens} (hU : IsAffineOpen U)
    (hV : (p ⁻¹ᵁ U : Set E).Nonempty) {f : Γ(E, p ⁻¹ᵁ U)} (hf : i.app _ f = 0) : f = 0 := by
  by_contra hne
  let _ := (p.app U).hom.toAlgebra
  obtain ⟨e0, he0⟩ := hV
  have : Nonempty (p ⁻¹ᵁ U) := ⟨⟨e0, he0⟩⟩
  have : Nonempty U := ⟨⟨p e0, he0⟩⟩
  have : IsSchemeTheoreticallyDominant (i ≫ p) := .of_isDominant _
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem (I := RingHom.ker (i.app _).hom) hne hf
      (isIntegral_app p U hU f))
  refine hr0 ((i ≫ p).app_injective U ?_)
  rw [map_zero, Scheme.Hom.comp_app]
  exact hr

/-- Sections of a pulled-back line bundle on a complex variety proper and dominant over a curve
are detected on any integral closed subvariety dominating the curve: restriction
`Γ(E, p^*M) → Γ(A, i^*p^*M)` is injective. -/
@[mmp "lem_fourfold_vertical_component_section_detection"]
public theorem injective_restrict_sections_pullback_of_isDominant
    {E C A : Scheme.{0}} (sE : E ⟶ Spec (.of ℂ)) (sC : C ⟶ Spec (.of ℂ))
    [IsVariety ℂ sE] [IsCurve ℂ sC]
    (p : E ⟶ C) (_hp : p ≫ sC = sE) [IsProper p] [IsDominant p]
    (M : C.Modules) [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 M]
    (i : A ⟶ E) [IsClosedImmersion i] [IsIntegral A] [IsDominant (i ≫ p)] :
    Function.Injective
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        ((Scheme.Modules.pullback p).obj M)).app ⊤) := by
  have hMinv : Stacks.Ample.IsInvertibleModule C M := ‹_›
  set L := (Scheme.Modules.pullback p).obj M
  have : Stacks.Ample.IsInvertibleModule E L :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback p M
  set η := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L
  rw [injective_iff_map_eq_zero]
  intro s hs
  -- a generator `a` of `M` over an affine open `U` of `C` meeting the image of `p`
  obtain ⟨e0⟩ : Nonempty E := inferInstance
  obtain ⟨K, hyK, a, ha⟩ : ∃ (K : C.Opens) (_ : p e0 ∈ K) (a : Γ(M, K)), ∀ (W : C.Opens)
      (hW : W ≤ K), Function.Bijective
        (fun c : Γ(C, W) => c • M.presheaf.map (homOfLE hW).op a) :=
    @Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible C.toRingedSpace _ M
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).mpr hMinv) (p e0)
  obtain ⟨U, hUaff, hyU, hUK⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp C.isBasis_affineOpens hyK
  set V := p ⁻¹ᵁ U
  -- its pullback `e` generates `L` over `V`, and the pullback of `e` generates `i^*L` over `i⁻¹V`
  set e : Γ(L, V) := ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app U
    (M.presheaf.map (homOfLE hUK).op a)
  have hgen : ∀ (W : E.Opens) (hW : W ≤ V), Function.Bijective
      (fun c : Γ(E, W) => c • L.presheaf.map (homOfLE hW).op e) :=
    bijective_smul_unit_app p M _ (fun W hW => by
      simpa only [map_map_homOfLE] using ha W (hW.trans hUK))
  have hgenA := bijective_smul_unit_app i L e hgen (i ⁻¹ᵁ V) le_rfl
  -- the restriction `t` of `s` to `V` is `f • e`, and `i^♯ f • η e = η t = 0`
  set t := L.presheaf.map (homOfLE le_top : V ⟶ ⊤).op s
  obtain ⟨f, hf⟩ := (hgen V le_rfl).2 t
  simp only [map_homOfLE_refl] at hf
  have hηt : η.app V t = 0 := by
    refine (PresheafOfModules.naturality_apply η.val (homOfLE le_top : V ⟶ ⊤).op s).trans ?_
    change _ = (0 : _)
    erw [hs, map_zero]
    rfl
  have hif : i.app V f = 0 := by
    refine hgenA.1 ?_
    let ηe : Γ((Scheme.Modules.pullback i).obj L, i ⁻¹ᵁ V) := η.app V e
    change i.app V f • ((Scheme.Modules.pullback i).obj L).presheaf.map
        (homOfLE (le_refl (i ⁻¹ᵁ V))).op ηe = (0 : Γ(A, i ⁻¹ᵁ V)) •
      ((Scheme.Modules.pullback i).obj L).presheaf.map (homOfLE (le_refl (i ⁻¹ᵁ V))).op ηe
    rw [map_homOfLE_refl, zero_smul]
    refine Eq.trans ?_ hηt
    rw [← hf, Scheme.Modules.Hom.app_smul]
    rfl
  have ht0 : t = 0 := by
    rw [← hf, eq_zero_of_app_eq_zero p i hUaff ⟨e0, hyU⟩ hif, zero_smul]
  exact eq_zero_of_map_eq_zero L ⟨e0, hyU⟩ s ht0

end MMP

end
