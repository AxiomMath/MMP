/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Properties.CodimensionLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv

/-!
# The origin of the affine line is a simple normal crossing divisor

On the affine line `𝔸¹_k = Spec k[x]` over a field `k`, the closed subscheme `V(x)` (the origin
with its reduced structure) is a simple normal crossing divisor in the sense of
`MMP.Resolution.IsSNCFamily`: it is reduced, of pure codimension one and smooth over `k`
(it is `Spec k`), and at every point `x` of `𝔸¹_k` there is a regular system of parameters
adapted to it. At the origin this is the germ of `x`; at another closed point `(f)` it is the germ
of `f`, and no component passes through the point; at the generic point it is the empty family.

## Main results

* `MMP.Resolution.isSNCFamily_affineLine_origin`: the one-element family `V(x)` on `𝔸¹_k` is a
  simple normal crossing divisor.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Def. 3.24]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace MMP.Resolution

variable (k : Type u) [Field k]

/-- The ideal sheaf of the origin `V(x) ⊆ 𝔸¹_k = Spec k[x]`, induced by the ideal `(x)` of the
global sections. -/
noncomputable def affineLineOriginIdeal : (Spec (.of k[X])).IdealSheafData :=
  .ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of k[X])).inv.hom Polynomial.X})

/-- The closed subscheme `V(x)` of `𝔸¹_k` is affine. -/
instance : IsAffine (affineLineOriginIdeal k).subscheme :=
  isAffine_of_isAffineHom (affineLineOriginIdeal k).subschemeι

section AffineLine

private theorem span_X_isMaximal : (Ideal.span {(Polynomial.X : k[X])}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X

private theorem eq_span_X_of_mem (p : Ideal k[X]) [hp : p.IsPrime]
    (h : (Polynomial.X : k[X]) ∈ p) : p = Ideal.span {Polynomial.X} :=
  ((span_X_isMaximal k).eq_of_le hp.ne_top
    (by simpa [Ideal.span_singleton_le_iff_mem] using h)).symm

private theorem height_eq_one (p : Ideal k[X]) [hp : p.IsPrime] (h : p ≠ ⊥) : p.height = 1 := by
  have h2 : ringKrullDim k[X] = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one _ (Polynomial.not_isField k)
  have h1 : p.height ≤ 1 := by
    have := Ideal.height_le_ringKrullDim_of_ne_top hp.ne_top
    rw [h2] at this
    exact_mod_cast this
  have h0 : p.height ≠ 0 := by
    rwa [Ne, Ideal.height_eq_zero_iff_eq_bot]
  exact le_antisymm h1 (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr h0))

private theorem germ_eq (x : Spec (.of k[X])) (f : k[X]) :
    (Spec (.of k[X])).presheaf.germ ⊤ x trivial ((Scheme.ΓSpecIso (.of k[X])).inv.hom f) =
        (Spec.stalkIso (.of k[X]) x).commRingCatIsoToRingEquiv.symm
          (algebraMap k[X] (Localization.AtPrime (show PrimeSpectrum k[X] from x).asIdeal)
            f) :=
  (ConcreteCategory.congr_hom (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of k[X]) x) f).symm

private theorem stalk_origin (x : Spec (.of k[X])) :
    IdealSheafData.stalk (affineLineOriginIdeal k) x =
      Ideal.span {((Spec (.of k[X])).presheaf.germ ⊤ x trivial
        ((Scheme.ΓSpecIso (.of k[X])).inv.hom Polynomial.X))} := by
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨⊤, isAffineOpen_top _⟩ trivial, affineLineOriginIdeal,
    Stacks.Divisors.ideal_ofIdealTop_top (isAffineOpen_top _), Ideal.map_span, Set.image_singleton]

private theorem X_mem_of_mem_support (x : Spec (.of k[X]))
    (hx : x ∈ (affineLineOriginIdeal k).support) :
    (Polynomial.X : k[X]) ∈ (show PrimeSpectrum k[X] from x).asIdeal := by
  by_contra hX
  refine (IdealSheafData.stalk_eq_top_iff_not_mem_support _ x).mp ?_ hx
  rw [stalk_origin k x, Ideal.span_singleton_eq_top, germ_eq]
  exact (MulEquiv.isUnit_map _).mpr ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).mpr hX)

/-- At a point `x = (f)` of `𝔸¹_k` with `f ≠ 0`, the maximal ideal of the local ring is generated
by the germ of `f`, and the local ring has dimension one. -/
private theorem stalk_facts (x : Spec (.of k[X])) (f : k[X])
    (hp : (show PrimeSpectrum k[X] from x).asIdeal = Ideal.span {f}) (hf : f ≠ 0) :
    IsLocalRing.maximalIdeal ((Spec (.of k[X])).presheaf.stalk x) =
      Ideal.span {((Spec (.of k[X])).presheaf.germ ⊤ x trivial
        ((Scheme.ΓSpecIso (.of k[X])).inv.hom f))} ∧
    ringKrullDim ((Spec (.of k[X])).presheaf.stalk x) = 1 := by
  have : x.asIdeal.IsPrime := x.isPrime
  let e := (Spec.stalkIso (.of k[X]) x).commRingCatIsoToRingEquiv
  have h1 : IsLocalRing.maximalIdeal (Localization.AtPrime x.asIdeal) =
      Ideal.span {algebraMap k[X] (Localization.AtPrime x.asIdeal) f} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal x.asIdeal (Localization.AtPrime x.asIdeal)]
    calc Ideal.map (algebraMap k[X] (Localization.AtPrime x.asIdeal)) x.asIdeal
        = Ideal.map (algebraMap k[X] (Localization.AtPrime x.asIdeal)) (Ideal.span {f}) :=
          congrArg _ hp
      _ = _ := by rw [Ideal.map_span, Set.image_singleton]
  refine ⟨?_, ?_⟩
  · rw [germ_eq, ← IsLocalRing.map_ringEquiv_maximalIdeal e.symm, h1, Ideal.map_span,
      Set.image_singleton]
  · rw [ringKrullDim_eq_of_ringEquiv e,
      IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal (Localization.AtPrime x.asIdeal),
      height_eq_one k _ (by rwa [hp, Ne, Ideal.span_singleton_eq_bot])]
    rfl

/-- The local ring of `𝔸¹_k` at its generic point is a field: its maximal ideal is `0` and it has
dimension zero. -/
private theorem stalk_facts_generic (x : Spec (.of k[X]))
    (hx : (show PrimeSpectrum k[X] from x).asIdeal = ⊥) :
    IsLocalRing.maximalIdeal ((Spec (.of k[X])).presheaf.stalk x) = ⊥ ∧
    ringKrullDim ((Spec (.of k[X])).presheaf.stalk x) = 0 := by
  have : x.asIdeal.IsPrime := x.isPrime
  let e := (Spec.stalkIso (.of k[X]) x).commRingCatIsoToRingEquiv
  refine ⟨?_, ?_⟩
  · rw [← IsLocalRing.map_ringEquiv_maximalIdeal e.symm,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal x.asIdeal (Localization.AtPrime x.asIdeal),
      eq_bot_iff]
    exact (Ideal.map_mono ((Ideal.map_mono (le_of_eq hx)).trans (le_of_eq Ideal.map_bot))).trans
      (le_of_eq Ideal.map_bot)
  · rw [ringKrullDim_eq_of_ringEquiv e,
      IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal (Localization.AtPrime x.asIdeal)]
    rw [hx, Ideal.height_bot]
    rfl

/-- A surjective ring map out of `k[X]` whose kernel is `(X)` is bijective on constants. -/
theorem bijective_comp_C_of_forall_eq_zero_iff {R : Type*} [CommRing R] (φ : k[X] →+* R)
    (hφ : Function.Surjective φ) (hker : ∀ p, φ p = 0 ↔ (Polynomial.X : k[X]) ∣ p) :
    Function.Bijective (φ.comp C) := by
  refine ⟨fun a b hab => ?_, fun t => ?_⟩
  · have := (hker (C (a - b))).1 (by rw [C_sub, map_sub, sub_eq_zero]; exact hab)
    rwa [X_dvd_iff, coeff_C_zero, sub_eq_zero] at this
  · obtain ⟨g, rfl⟩ := hφ t
    refine ⟨g.coeff 0, ?_⟩
    have := (hker (g - C (g.coeff 0))).2 (by simp [X_dvd_iff])
    rw [map_sub, sub_eq_zero] at this
    exact this.symm

private theorem bijective_appTop : Function.Bijective
    ((affineLineOriginIdeal k).subschemeι ≫ Spec.map (CommRingCat.ofHom C)).appTop.hom := by
  set e := (Scheme.ΓSpecIso (.of k[X])).inv.hom with he
  set ε := (Scheme.ΓSpecIso (.of k[X])).hom.hom
  let ι := (affineLineOriginIdeal k).subschemeι
  let U : (Spec (.of k[X])).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hker : RingHom.ker (ι.app U).hom = Ideal.span {e X} := by
    rw [Scheme.IdealSheafData.ker_subschemeι_app, affineLineOriginIdeal,
      Stacks.Divisors.ideal_ofIdealTop_top]
  have hsurj : Function.Surjective (ι.app U).hom :=
    Scheme.IdealSheafData.subschemeι_app_surjective _ U
  have key : ∀ a : k,
      ((affineLineOriginIdeal k).subschemeι ≫ Spec.map (CommRingCat.ofHom C)).appTop.hom
      ((Scheme.ΓSpecIso (.of k)).inv.hom a) = (ι.app U).hom (e (C a)) := by
    intro a
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    have h1 := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (C : k →+* k[X]))) a
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
    rw [← h1]
    rfl
  have hψ : Function.Bijective (fun a : k => (ι.app U).hom (e (C a))) := by
    refine bijective_comp_C_of_forall_eq_zero_iff k ((ι.app U).hom.comp e)
      (hsurj.comp fun t => ⟨ε t, by simp [he, ε]⟩) fun p => ?_
    rw [RingHom.comp_apply, ← RingHom.mem_ker, hker, Ideal.mem_span_singleton]
    exact ⟨fun ⟨y, hy⟩ => ⟨ε y, by simpa [he, ε] using congrArg ε hy⟩,
      fun ⟨q, hq⟩ => ⟨e q, by rw [hq, map_mul]⟩⟩
  refine ⟨fun x y hxy => ?_, fun t => ?_⟩
  · have hx := key ((Scheme.ΓSpecIso (.of k)).hom.hom x)
    have hy := key ((Scheme.ΓSpecIso (.of k)).hom.hom y)
    rw [CommRingCat.inv_hom_apply] at hx hy
    have := hψ.1 (hx.symm.trans (hxy.trans hy))
    have h2 := congrArg (Scheme.ΓSpecIso (.of k)).inv.hom this
    rwa [CommRingCat.inv_hom_apply, CommRingCat.inv_hom_apply] at h2
  · obtain ⟨a, ha⟩ := hψ.2 t
    exact ⟨(Scheme.ΓSpecIso (.of k)).inv.hom a, (key a).trans ha⟩

end AffineLine

/-- **The origin of the affine line is a simple normal crossing divisor.** On `𝔸¹_k = Spec k[x]`
over a field `k`, the one-element family consisting of the closed subscheme `V(x)` is a simple
normal crossing divisor over `k` (Kollár Def. 3.24). -/
theorem isSNCFamily_affineLine_origin :
    IsSNCFamily (Spec.map (CommRingCat.ofHom (C : k →+* k[X])))
      (fun _ : Unit => affineLineOriginIdeal k) := by
  have hsm : Smooth ((affineLineOriginIdeal k).subschemeι ≫
      Spec.map (CommRingCat.ofHom (C : k →+* k[X]))) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
    exact RingHom.Smooth.of_bijective (bijective_appTop k)
  refine ⟨fun _ => ⟨?_, ?_, (MMP.Mori.isSmoothScheme_iff _).2 hsm⟩, fun x => ?_⟩
  · -- reduced: the global sections of `V(x)` are isomorphic to `k`
    let ε := RingEquiv.ofBijective _ (bijective_appTop k)
    let e := ε.symm.trans (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
    have : _root_.IsReduced Γ((affineLineOriginIdeal k).subscheme, ⊤) :=
      isReduced_of_injective e.toRingHom e.injective
    exact isReduced_of_isAffine_isReduced _
  · -- pure codimension one
    intro W hW
    have hcl := W.isClosed
    set ξ := W.isIrreducible.genericPoint
    have hξ : ξ ∈ (affineLineOriginIdeal k).support :=
      hW.prop ((W.isIrreducible.isGenericPoint_genericPoint hcl).mem)
    have : ξ.asIdeal.IsPrime := ξ.isPrime
    have hp := eq_span_X_of_mem k _ (X_mem_of_mem_support k ξ hξ)
    have hc := codimension_eq_ringKrullDim_stalk_genericPoint W
    rw [(stalk_facts k ξ Polynomial.X hp Polynomial.X_ne_zero).2] at hc
    exact_mod_cast hc
  · have : x.asIdeal.IsPrime := x.isPrime
    by_cases hX : (Polynomial.X : k[X]) ∈ (show PrimeSpectrum k[X] from x).asIdeal
    · have hp := eq_span_X_of_mem k _ hX
      obtain ⟨hm, hd⟩ := stalk_facts k x Polynomial.X hp Polynomial.X_ne_zero
      refine ⟨1, fun _ => (Spec (.of k[X])).presheaf.germ ⊤ x trivial
        ((Scheme.ΓSpecIso (.of k[X])).inv.hom Polynomial.X), fun _ => 0, ⟨?_, ?_⟩,
        fun _ => stalk_origin k x, fun a b _ => Subsingleton.elim a b⟩
      · rw [Set.range_const, hm]
      · rw [hd]
        rfl
    · have hns : ∀ i : {i : Unit // x ∈ (affineLineOriginIdeal k).support}, False :=
        fun i => hX (X_mem_of_mem_support k x i.2)
      by_cases h0 : (show PrimeSpectrum k[X] from x).asIdeal = ⊥
      · obtain ⟨hm, hd⟩ := stalk_facts_generic k x h0
        refine ⟨0, Fin.elim0, fun i => (hns i).elim, ⟨?_, ?_⟩, fun i => (hns i).elim,
          fun i => (hns i).elim⟩
        · rw [Set.range_eq_empty, Ideal.span_empty, hm]
        · rw [hd]
          rfl
      · obtain ⟨f, hf⟩ := (IsPrincipalIdealRing.principal x.asIdeal).principal
        have hf0 : f ≠ 0 := by
          rintro rfl
          exact h0 (by rw [hf]; simp)
        obtain ⟨hm, hd⟩ := stalk_facts k x f (by rw [hf]) hf0
        refine ⟨1, fun _ => (Spec (.of k[X])).presheaf.germ ⊤ x trivial
          ((Scheme.ΓSpecIso (.of k[X])).inv.hom f), fun i => (hns i).elim, ⟨?_, ?_⟩,
          fun i => (hns i).elim, fun i => (hns i).elim⟩
        · rw [Set.range_const, hm]
        · rw [hd]
          rfl

end MMP.Resolution
