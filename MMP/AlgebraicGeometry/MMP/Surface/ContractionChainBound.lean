module

public import Mathlib
public import MMP.Attr
import MMP.AlgebraicGeometry.MMP.Surface.ContractedCurvesBound
public import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Intersection.N1FiniteDimensionalProjective
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Divisor.RationalFunctionsProduct

/-!
# Chains of curve contractions from a normal surface are bounded

Let `K` be a field of characteristic zero and `S` a normal surface over `K`. There is a natural
number `M` such that every chain `S = S₀ → S₁ → ⋯ → S_r` of proper birational `K`-morphisms of
normal surfaces, each of which maps some integral curve to a point, has length `r ≤ M`.
Indeed, lifting a curve contracted at step `t` to an integral curve of `S₀` gives `r` distinct
curves contracted by the composite `S₀ → S_r`, and these are bounded uniformly in terms of `S`.

## Main results

* `MMP.Mori.exists_forall_length_le_of_isExceptionalCurve_chain`: the statement above.

## Implementation notes

A surface over `K` is a normal variety `X` with `topologicalKrullDim X = 2`. A chain of length
`r` is a family of `K`-schemes `X : ℕ → Scheme` with morphisms `f i : X i ⟶ X (i + 1)`, of which
only the indices `i ≤ r` (for the schemes) and `i < r` (for the morphisms) are constrained; the
first term is identified with `S` by an isomorphism of `K`-schemes rather than by an equality of
schemes. A curve of `X i` mapped to a point by `f i` is an `MMP.Mori.IsExceptionalCurve (f i)`:
an integral closed subscheme of dimension one whose image is a point.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori.ContractionChainBound

/-- The composites `g t : S ⟶ X t` of a chain `e : S ⟶ X 0`, `f i : X i ⟶ X (i + 1)`. -/
private noncomputable def chainComp {S : Scheme.{0}} (X : ℕ → Scheme.{0})
    (f : ∀ i, X i ⟶ X (i + 1)) (e : S ⟶ X 0) : ∀ t, S ⟶ X t
  | 0 => e
  | t + 1 => chainComp X f e t ≫ f t

/-- A later composite factors through an earlier one. -/
private theorem exists_chainComp_eq_comp {S : Scheme.{0}} (X : ℕ → Scheme.{0})
    (f : ∀ i, X i ⟶ X (i + 1)) (e : S ⟶ X 0) {t t' : ℕ} (h : t ≤ t') :
    ∃ φ : X t ⟶ X t', chainComp X f e t' = chainComp X f e t ≫ φ := by
  induction t', h using Nat.le_induction with
  | base => exact ⟨𝟙 _, (Category.comp_id _).symm⟩
  | succ n _ ih =>
    obtain ⟨φ, hφ⟩ := ih
    exact ⟨φ ≫ f n, by rw [chainComp, hφ, Category.assoc]⟩

/-- The support of a curve is not a single point. -/
private theorem support_ne_singleton_of_isCurveIn {Z : Scheme.{0}} {C : Z.IdealSheafData}
    (hC : IsCurveIn C) (x : Z) : (C.support : Set Z) ≠ {x} := by
  intro h
  have h1 := hC.2
  rw [topologicalKrullDim_subscheme_eq, h] at h1
  have : Subsingleton ({x} : Set Z) := Set.subsingleton_singleton.coe_sort
  have : Nonempty ({x} : Set Z) := ⟨⟨x, rfl⟩⟩
  rw [topologicalKrullDim_eq_zero_of_indiscreteTopology] at h1
  exact absurd h1 (by decide)

/-- The image of a set under a composite of morphisms of schemes. -/
private theorem image_comp_base {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (A : Set X) :
    (a ≫ b).base '' A = b.base '' (a.base '' A) := by
  rw [Set.image_image]
  rfl

/-- A normal variety is integral, normal, locally noetherian, quasi-compact and noetherian. -/
private theorem instances_of_isNormalVariety {K : Type} [Field K] {Z : Scheme.{0}}
    {s : Z ⟶ Spec (.of K)} (h : IsNormalVariety K s) :
    IsIntegral Z ∧ IsNormal Z ∧ IsLocallyNoetherian Z ∧ CompactSpace Z ∧ NoetherianSpace Z := by
  have := h.1
  have := h.2
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Z := ⟨⟩
  exact ⟨h.1.toIsIntegral, h.2, inferInstance, inferInstance, inferInstance⟩

/-- A curve on a scheme is determined by its support. -/
private theorem eq_of_isCurveIn_of_support_eq {Z : Scheme.{0}} {C C' : Z.IdealSheafData}
    (hC : IsCurveIn C) (hC' : IsCurveIn C') (h : (C.support : Set Z) = C'.support) : C = C' := by
  have := hC.1
  have := hC'.1
  rw [← vanishingIdeal_support_eq_self C, ← vanishingIdeal_support_eq_self C', Closeds.ext h]

/-- The composites of a chain of proper birational `K`-morphisms of normal varieties are proper
birational `K`-morphisms. -/
private theorem isProper_isBirationalMorphism_chainComp (K : Type) [Field K] {S : Scheme.{0}}
    (sS : S ⟶ Spec (.of K)) (hS : IsNormalVariety K sS) (r : ℕ)
    (X : ℕ → Scheme.{0}) (sX : ∀ i, X i ⟶ Spec (.of K))
    (f : ∀ i, X i ⟶ X (i + 1)) (e : S ≅ X 0) (he : e.hom ≫ sX 0 = sS)
    (hX : ∀ i ≤ r, IsNormalVariety K (sX i) ∧ topologicalKrullDim (X i) = 2)
    (hf : ∀ i < r, f i ≫ sX (i + 1) = sX i ∧ IsProper (f i) ∧ IsBirationalMorphism (f i) ∧
      ∃ C : (X i).IdealSheafData, IsExceptionalCurve (f i) C) (t : ℕ) (ht : t ≤ r) :
    chainComp X f e.hom t ≫ sX t = sS ∧ IsProper (chainComp X f e.hom t) ∧
      IsBirationalMorphism (chainComp X f e.hom t) := by
  obtain ⟨_, _, _, _, _⟩ := instances_of_isNormalVariety hS
  induction t with
  | zero => exact ⟨he, inferInstanceAs (IsProper e.hom), isBirationalMorphism_of_isIso e.hom⟩
  | succ t ih =>
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    obtain ⟨hf1, hf2, hf3, -⟩ := hf t (by omega)
    obtain ⟨_, _, _, _, _⟩ := instances_of_isNormalVariety (hX t (by omega)).1
    obtain ⟨_, _, _, _, _⟩ := instances_of_isNormalVariety (hX (t + 1) ht).1
    refine ⟨by simp only [chainComp, Category.assoc, hf1, h1],
      inferInstanceAs (IsProper (chainComp X f e.hom t ≫ f t)), ?_⟩
    exact isBirationalMorphism_comp_of_isBirational (f t) (chainComp X f e.hom t)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf3)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h3)

/-- **Chains of contractions are bounded by a bound on contracted curves.** If `M` bounds the
number of curves contracted by every proper birational `K`-morphism from the normal surface `S`
onto a normal surface, then every chain `S ≅ X 0 → ⋯ → X r` of proper birational morphisms of
normal surfaces, each contracting a curve, has `r ≤ M`. -/
private theorem length_le_of_forall_encard_le (K : Type) [Field K] {S : Scheme.{0}}
    (sS : S ⟶ Spec (.of K)) (hS : IsNormalVariety K sS) (hdim : topologicalKrullDim S = 2)
    (M : ℕ) (hM : ∀ (S' : Scheme.{0}) (sS' : S' ⟶ Spec (.of K)) (σ : S ⟶ S'),
      IsNormalVariety K sS' → topologicalKrullDim S' = 2 → σ ≫ sS' = sS →
        IsProper σ → IsBirationalMorphism σ →
          {C : S.IdealSheafData | IsExceptionalCurve σ C}.encard ≤ M)
    (r : ℕ) (X : ℕ → Scheme.{0}) (sX : ∀ i, X i ⟶ Spec (.of K))
    (f : ∀ i, X i ⟶ X (i + 1)) (e : S ≅ X 0) (he : e.hom ≫ sX 0 = sS)
    (hX : ∀ i ≤ r, IsNormalVariety K (sX i) ∧ topologicalKrullDim (X i) = 2)
    (hf : ∀ i < r, f i ≫ sX (i + 1) = sX i ∧ IsProper (f i) ∧ IsBirationalMorphism (f i) ∧
      ∃ C : (X i).IdealSheafData, IsExceptionalCurve (f i) C) : r ≤ M := by
  have hg := isProper_isBirationalMorphism_chainComp K sS hS r X sX f e he hX hf
  set g := chainComp X f e.hom
  obtain ⟨_, _, _, _, _⟩ := instances_of_isNormalVariety hS
  choose C hC using fun t : Fin r ↦ (hf t t.2).2.2.2
  set D : Fin r → S.IdealSheafData := fun t ↦ inverseTransformIdeal (g t) (C t).support
  have hD : ∀ t : Fin r, IsCurveIn (D t) ∧
      (g t).base '' ((D t).support : Set S) = (C t).support := by
    intro t
    obtain ⟨_, _, _, _, _⟩ := instances_of_isNormalVariety (hX t (by omega)).1
    obtain ⟨-, hp, hb⟩ := hg t (by omega)
    simpa only [D, support_inverseTransformIdeal] using isCurveIn_inverseTransformIdeal (g t)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb) hdim.le
      (hX t (by omega)).2 (hC t).1
  have hcon : ∀ (t : Fin r) (t' : ℕ), (t : ℕ) < t' →
      ∃ x, (g t').base '' ((D t).support : Set S) = {x} := by
    intro t t' htt'
    obtain ⟨φ, hφ⟩ := exists_chainComp_eq_comp X f e.hom (Nat.succ_le_of_lt htt')
    obtain ⟨x, hx⟩ := (hC t).2
    refine ⟨φ.base x, ?_⟩
    rw [show g t' = g (t + 1) ≫ φ from hφ, image_comp_base,
      show g (t + 1) = g t ≫ f t from rfl, image_comp_base, (hD t).2, hx, Set.image_singleton]
  have hne : ∀ t t' : Fin r, (t : ℕ) < t' → D t ≠ D t' := by
    intro t t' hlt h
    obtain ⟨x, hx⟩ := hcon t t' hlt
    rw [h, (hD t').2] at hx
    exact support_ne_singleton_of_isCurveIn (hC t').1 x hx
  have hinj : Function.Injective D := by
    intro t t' h
    by_contra htt
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne htt) with hlt | hlt
    · exact hne t t' hlt h
    · exact hne t' t hlt h.symm
  obtain ⟨hr1, hr2, hr3⟩ := hg r le_rfl
  have hsub : Set.range D ⊆ {C | IsExceptionalCurve (g r) C} := by
    rintro _ ⟨t, rfl⟩
    exact ⟨(hD t).1, hcon t r t.2⟩
  have h := (Set.encard_le_encard hsub).trans
    (hM (X r) (sX r) (g r) (hX r le_rfl).1 (hX r le_rfl).2 hr1 hr2 hr3)
  rw [← Set.image_univ, hinj.encard_image, Set.encard_univ, ENat.card_eq_coe_fintype_card,
    Fintype.card_fin] at h
  exact_mod_cast h

/-! ### Base change to an algebraic closure -/

/-- The base change morphism `Spec K̄ ⟶ Spec K` to an algebraic closure. -/
private noncomputable abbrev specAlgClosure (K : Type) [Field K] :
    Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))

private theorem isIntegralHom_specAlgClosure (K : Type) [Field K] :
    IsIntegralHom (specAlgClosure K) :=
  IsIntegralHom.SpecMap_iff.mpr fun x ↦ Algebra.IsIntegral.isIntegral x

private theorem flat_specAlgClosure (K : Type) [Field K] : Flat (specAlgClosure K) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- If `φ` is integral, two primes of `S` related by specialization with the same image under
`Spec φ` are equal. -/
private theorem eq_of_specializes_of_isIntegral_specMap {R S : CommRingCat} (φ : R ⟶ S)
    (hφ : φ.hom.IsIntegral) {p q : PrimeSpectrum S} (hpq : p ⤳ q)
    (hc : Spec.map φ p = Spec.map φ q) : p = q := by
  rw [← PrimeSpectrum.le_iff_specializes] at hpq
  letI := φ.hom.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hφ⟩
  by_contra hne
  exact (Ideal.IsIntegral.comap_lt_comap (R := R)
    (lt_of_le_of_ne (show p.asIdeal ≤ q.asIdeal from hpq) (mt PrimeSpectrum.ext hne))).ne
    (congrArg PrimeSpectrum.asIdeal hc)

/-- If `f` is an integral morphism of affine schemes, two points related by specialization with
the same image under `f` are equal. -/
private theorem eq_of_specializes_of_isIntegralHom_of_isAffine {X Z : Scheme} [IsAffine X]
    [IsAffine Z] (f : X ⟶ Z) [IsIntegralHom f] {t t' : X} (h : t ⤳ t') (he : f t = f t') :
    t = t' := by
  have hg : (f.appTop).hom.IsIntegral := f.isIntegral_app ⊤ (isAffineOpen_top Z)
  have hc : (Spec.map f.appTop) (X.isoSpec.hom t) = (Spec.map f.appTop) (X.isoSpec.hom t') := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, he]
  have heq := congrArg X.isoSpec.inv (eq_of_specializes_of_isIntegral_specMap _ hg
    (h.map X.isoSpec.hom.continuous) hc)
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Iso.hom_inv_id] at heq

/-- **Incomparability.** The fibres of an integral morphism carry no nontrivial
specializations. -/
private theorem eq_of_specializes_of_isIntegralHom {X Z : Scheme} (f : X ⟶ Z) [IsIntegralHom f]
    {t t' : X} (h : t ⤳ t') (he : f t = f t') : t = t' := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f t')) isOpen_univ
  have ht' : t' ∈ f ⁻¹ᵁ U := hmem
  have ht : t ∈ f ⁻¹ᵁ U := h.mem_open (f ⁻¹ᵁ U).isOpen ht'
  have : IsAffine U := hU
  have : IsAffine (f ⁻¹ᵁ U) := hU.preimage f
  let a : (f ⁻¹ᵁ U).toScheme := ⟨t, ht⟩
  let b : (f ⁻¹ᵁ U).toScheme := ⟨t', ht'⟩
  have hab : a ⤳ b := subtype_specializes_iff _ _ |>.2 h
  have hfab : (f ∣_ U) a = (f ∣_ U) b := Subtype.ext
    ((morphismRestrict_base_coe f U a).trans (he.trans (morphismRestrict_base_coe f U b).symm))
  exact congrArg Subtype.val (eq_of_specializes_of_isIntegralHom_of_isAffine (f ∣_ U) hab hfab)

/-- **Lifting a contracted curve along integral maps.** Let `τ : Y ⟶ Y'` lie over
`σ : S ⟶ S'` through integral morphisms `g : Y ⟶ S` and `g' : Y' ⟶ S'`. If `σ` contracts the
curve `C` and `g a` is the generic point of `C`, then `τ` contracts the curve `closure {a}`. -/
private theorem isExceptionalCurve_vanishingIdeal_closure {Y Y' S S' : Scheme.{0}}
    [CompactSpace S] (g : Y ⟶ S) (g' : Y' ⟶ S') [IsIntegralHom g] [IsIntegralHom g']
    {σ : S ⟶ S'} {τ : Y ⟶ Y'}
    (hτ : τ ≫ g' = g ≫ σ) {C : S.IdealSheafData} (hC : IsExceptionalCurve σ C) {a : Y}
    (ha : closure {g a} = (C.support : Set S)) (hcl : ¬ IsClosed {g a}) :
    IsExceptionalCurve τ
      (Scheme.IdealSheafData.vanishingIdeal ⟨closure {a}, isClosed_closure⟩) := by
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal ⟨closure {a}, isClosed_closure⟩).support :
      Set Y) = closure {a} := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hT : ∀ t ∈ closure ({a} : Set Y), g t ∈ (C.support : Set S) := fun t ht ↦ by
    rw [← ha]
    exact specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr ht).map g.continuous)
  have hC1 : topologicalKrullDim (C.support : Set S) = 1 := by
    rw [← topologicalKrullDim_subscheme_eq]
    exact hC.1.2
  refine ⟨⟨StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
    isIrreducible_singleton.closure, ?_⟩, ?_⟩
  · rw [topologicalKrullDim_subscheme_eq, hsupp]
    refine le_antisymm ?_ ?_
    · have : QuasiSober (closure ({a} : Set Y)) :=
        isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
      rw [← hC1]
      exact MMP.Flips.topologicalKrullDim_le_of_specializes_imp_eq
        (f := fun t : closure ({a} : Set Y) ↦ (⟨g t.1, hT t.1 t.2⟩ : (C.support : Set S)))
        ((g.continuous.comp continuous_subtype_val).subtype_mk _) fun t t' htt' heq ↦
          Subtype.ext (eq_of_specializes_of_isIntegralHom g (htt'.map continuous_subtype_val)
            (congrArg Subtype.val heq))
    · obtain ⟨c, -, hec, hne⟩ := exists_isClosed_singleton_specializes hcl
      obtain ⟨b, hab, rfl⟩ := g.isClosedMap.specializingMap hec
      exact one_le_topologicalKrullDim_of_specializes_of_ne
        (x := (⟨a, subset_closure rfl⟩ : closure ({a} : Set Y)))
        (y := ⟨b, specializes_iff_mem_closure.mp hab⟩) ((subtype_specializes_iff _ _).mpr hab)
        fun h ↦ hne (congrArg (fun t : closure ({a} : Set Y) ↦ g t.1) h)
  · obtain ⟨x0, hx0⟩ := hC.2
    have hσC : ∀ t ∈ closure ({a} : Set Y), σ (g t) = x0 := fun t ht ↦ by
      have : σ.base (g t) ∈ σ.base '' (C.support : Set S) := ⟨_, hT t ht, rfl⟩
      rwa [hx0] at this
    have hg' : ∀ t, g' (τ t) = σ (g t) := fun t ↦ by
      rw [← Scheme.Hom.comp_apply, hτ, Scheme.Hom.comp_apply]
    refine ⟨τ a, ?_⟩
    rw [hsupp]
    refine subset_antisymm ?_ (Set.singleton_subset_iff.mpr ⟨a, subset_closure rfl, rfl⟩)
    rintro _ ⟨t, ht, rfl⟩
    exact (eq_of_specializes_of_isIntegralHom g' ((specializes_iff_mem_closure.mpr ht).map
      τ.continuous) (by rw [hg', hg', hσC a (subset_closure rfl), hσC t ht])).symm

/-- A space of dimension two whose points all specialize from `η` has a chain `η ⤳ a ⤳ b` of
distinct points. -/
private theorem exists_specializes_specializes {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [T0Space X] {η : X} (hη : ∀ x, η ⤳ x) (hdim : topologicalKrullDim X = 2) :
    ∃ a b : X, η ⤳ a ∧ a ⤳ b ∧ η ≠ a ∧ a ≠ b := by
  obtain ⟨⟨n, f, hf⟩, hn⟩ := Order.le_krullDim_iff.mp
    (show ((2 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X by rw [hdim]; rfl)
  simp only at hn
  subst hn
  have h01 : f 0 < f 1 := hf 0
  have h12 : f 1 < f 2 := hf 1
  have hgen : ∀ i, IsGenericPoint (f i).isIrreducible.genericPoint (f i : Set X) := fun i ↦
    (f i).isIrreducible.isGenericPoint_genericPoint (f i).isClosed
  have heq : ∀ i j, (f i).isIrreducible.genericPoint = (f j).isIrreducible.genericPoint →
      f i = f j := fun i j h ↦ by
    ext1
    rw [← (hgen i).def, ← (hgen j).def, h]
  have hsp : ∀ i j, f i ≤ f j →
      (f j).isIrreducible.genericPoint ⤳ (f i).isIrreducible.genericPoint :=
    fun i j h ↦ (hgen j).specializes (h (hgen i).mem)
  refine ⟨(f 1).isIrreducible.genericPoint, (f 0).isIrreducible.genericPoint, hη _,
    hsp 0 1 h01.le, fun h ↦ h12.ne (heq 1 2 ?_), fun h ↦ h01.ne (heq 0 1 h.symm)⟩
  rw [← h]
  exact ((hη _).antisymm (h ▸ hsp 1 2 h12.le)).eq

/-- The base change of a normal surface over a field `K` of characteristic zero to an algebraic
closure `K̄` is normal, locally noetherian, quasi-compact, and of dimension two. -/
private theorem isNormal_baseChange_algClosure (K : Type) [Field K] [CharZero K] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of K)) (hX : IsNormalVariety K sX) (hdim : topologicalKrullDim X = 2) :
    IsNormal (pullback sX (specAlgClosure K) : Scheme.{0}) ∧
      IsLocallyNoetherian (pullback sX (specAlgClosure K) : Scheme.{0}) ∧
      CompactSpace (pullback sX (specAlgClosure K) : Scheme.{0}) ∧
      topologicalKrullDim (pullback sX (specAlgClosure K) : Scheme.{0}) = 2 := by
  have := hX.1
  have := hX.2
  have : Algebra.IsSeparableExtension K (AlgebraicClosure K) :=
    Algebra.isSeparableExtension_of_perfectField _ _
  have : IsLocallyNoetherian (pullback sX (specAlgClosure K) : Scheme.{0}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd sX (specAlgClosure K))
  refine ⟨isNormal_pullback_of_isSeparableExtension K (AlgebraicClosure K) sX, inferInstance,
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd sX (specAlgClosure K)), ?_⟩
  rw [topologicalKrullDim_baseChange K (AlgebraicClosure K) _ _ sX
    (IsPullback.of_hasPullback sX (specAlgClosure K)), hdim]

/-- An irreducible component `Z` of the base change `X_K̄` of a normal surface over `K` is an
open normal surface over `K̄`, and its generic point lies over the generic point of `X`. -/
private theorem baseChange_component (K : Type) [Field K] [CharZero K] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of K)) (hX : IsNormalVariety K sX) (hdim : topologicalKrullDim X = 2)
    {Z : Set (pullback sX (specAlgClosure K) : Scheme.{0})}
    (hZ : Z ∈ irreducibleComponents (pullback sX (specAlgClosure K) : Scheme.{0})) :
    ∃ U : (pullback sX (specAlgClosure K) : Scheme.{0}).Opens, (U : Set _) = Z ∧
      IsNormalVariety (AlgebraicClosure K) (U.ι ≫ pullback.snd sX (specAlgClosure K)) ∧
        topologicalKrullDim U = 2 ∧
        ∃ ζ ∈ Z, ∀ x : X, pullback.fst sX (specAlgClosure K) ζ ⤳ x := by
  obtain ⟨_, _, _, hd⟩ := isNormal_baseChange_algClosure K sX hX hdim
  obtain ⟨_, _, _, _, _⟩ := instances_of_isNormalVariety hX
  have := hX.1
  have := isIntegralHom_specAlgClosure K
  have := flat_specAlgClosure K
  have hclo := isClopen_of_mem_irreducibleComponents hZ
  have hirr : IsIrreducible Z := hZ.1
  let U : (pullback sX (specAlgClosure K) : Scheme.{0}).Opens := ⟨Z, hclo.isOpen⟩
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober hirr hclo.isClosed
  have hζZ : ζ ∈ Z := hζ.mem
  have hgen : ∀ x : X, pullback.fst sX (specAlgClosure K) ζ ⤳ x := by
    intro x
    obtain ⟨ζ', hζ', heq⟩ := Flat.generalizingMap (pullback.fst sX (specAlgClosure K))
      (genericPoint_specializes (pullback.fst sX (specAlgClosure K) ζ))
    have hζ'Z : ζ' ∈ Z := hζ'.mem_open hclo.isOpen hζZ
    rw [← (hζ'.antisymm (hζ.specializes hζ'Z)).eq, heq]
    exact genericPoint_specializes x
  have : IrreducibleSpace U.toScheme := isIrreducible_iff_irreducibleSpace.mp hirr
  have : IsNormal U.toScheme := isNormal_of_isOpenImmersion U.ι
  have : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced U.toScheme
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hclo.isClosed.isCompact
  have : QuasiCompact (U.ι ≫ pullback.snd sX (specAlgClosure K)) :=
    (quasiCompact_iff_compactSpace _).mpr inferInstance
  refine ⟨U, rfl, ⟨⟨⟩, inferInstance⟩, le_antisymm ?_ ?_, ζ, hζZ, hgen⟩
  · change topologicalKrullDim Z ≤ 2
    rw [← hd]
    exact topologicalKrullDim_subspace_le _ _
  · obtain ⟨a, b, hηa, hab, hne1, hne2⟩ := exists_specializes_specializes hgen hdim
    obtain ⟨z1, hz1, hpz1⟩ := (pullback.fst sX (specAlgClosure K)).isClosedMap.specializingMap hηa
    obtain ⟨z2, hz2, hpz2⟩ := (pullback.fst sX (specAlgClosure K)).isClosedMap.specializingMap
      (show pullback.fst sX (specAlgClosure K) z1 ⤳ b by rwa [hpz1])
    have hz1Z : z1 ∈ Z := hz1.mem_closed hclo.isClosed hζZ
    change 2 ≤ topologicalKrullDim Z
    exact MMP.Flips.two_le_topologicalKrullDim_of_specializes hζZ hz1Z
      (hz2.mem_closed hclo.isClosed hz1Z) hz1 hz2 (fun h ↦ hne1 (by rw [← hpz1, h]))
      (fun h ↦ hne2 (by rw [← hpz1, ← hpz2, h]))

/-- The base change `σk : S_K̄ ⟶ S'_K̄` of a proper `K`-morphism `σ : S ⟶ S'` is proper, lies over
`σ` and over `Spec K̄`, and is an open immersion over every open on which `σ` is one. -/
private theorem exists_baseChange_hom (K : Type) [Field K] {S S' : Scheme.{0}}
    (sS : S ⟶ Spec (.of K)) (sS' : S' ⟶ Spec (.of K)) (σ : S ⟶ S') (hσs : σ ≫ sS' = sS)
    (hσp : IsProper σ) :
    ∃ σk : (pullback sS (specAlgClosure K) : Scheme.{0}) ⟶ pullback sS' (specAlgClosure K),
      IsProper σk ∧
      σk ≫ pullback.fst sS' (specAlgClosure K) = pullback.fst sS (specAlgClosure K) ≫ σ ∧
      σk ≫ pullback.snd sS' (specAlgClosure K) = pullback.snd sS (specAlgClosure K) ∧
      ∀ W : S.Opens, IsOpenImmersion (W.ι ≫ σ) →
        IsOpenImmersion ((pullback.fst sS (specAlgClosure K) ⁻¹ᵁ W).ι ≫ σk) := by
  let σk : (pullback sS (specAlgClosure K) : Scheme.{0}) ⟶ pullback sS' (specAlgClosure K) :=
    pullback.map sS (specAlgClosure K) sS' (specAlgClosure K) σ (𝟙 _) (𝟙 _)
      (by simp [hσs]) (by simp)
  have hσq : σk ≫ pullback.fst sS' (specAlgClosure K) = pullback.fst sS (specAlgClosure K) ≫ σ :=
    pullback.lift_fst _ _ _
  have hσsnd : σk ≫ pullback.snd sS' (specAlgClosure K) = pullback.snd sS (specAlgClosure K) := by
    simp [σk]
  have hpb : IsPullback σk (pullback.fst sS (specAlgClosure K))
      (pullback.fst sS' (specAlgClosure K)) σ := by
    refine IsPullback.of_right ?_ hσq (IsPullback.of_hasPullback sS' (specAlgClosure K)).flip
    rw [hσsnd, hσs]
    exact (IsPullback.of_hasPullback sS (specAlgClosure K)).flip
  exact ⟨σk, MorphismProperty.of_isPullback hpb.flip hσp, hσq, hσsnd, fun W hWo ↦
    MorphismProperty.of_isPullback ((isPullback_morphismRestrict _ W).paste_vert hpb.flip) hWo⟩

/-- If `τ ≫ V'.ι = V.ι ≫ σ` and `σ` is an open immersion on `O`, then `τ` is an open immersion on
the preimage of `O` in `V`. -/
private theorem isOpenImmersion_preimage_ι_comp {T T' : Scheme.{0}} {V : T.Opens} {V' : T'.Opens}
    {σ : T ⟶ T'} {τ : V.toScheme ⟶ V'.toScheme} (hfac : τ ≫ V'.ι = V.ι ≫ σ) (O : T.Opens)
    [IsOpenImmersion (O.ι ≫ σ)] : IsOpenImmersion ((V.ι ⁻¹ᵁ O).ι ≫ τ) := by
  have h1 : Set.range ((V.ι ⁻¹ᵁ O).ι ≫ V.ι) ⊆ Set.range O.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact x.2
  have : IsOpenImmersion (IsOpenImmersion.lift O.ι ((V.ι ⁻¹ᵁ O).ι ≫ V.ι) h1 ≫ O.ι) := by
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  have := IsOpenImmersion.of_comp (IsOpenImmersion.lift O.ι ((V.ι ⁻¹ᵁ O).ι ≫ V.ι) h1) O.ι
  have : IsOpenImmersion (((V.ι ⁻¹ᵁ O).ι ≫ τ) ≫ V'.ι) := by
    rw [Category.assoc, hfac, ← Category.assoc,
      ← IsOpenImmersion.lift_fac O.ι ((V.ι ⁻¹ᵁ O).ι ≫ V.ι) h1, Category.assoc]
    infer_instance
  exact IsOpenImmersion.of_comp _ V'.ι

/-- Curves of `S` contracted by `σ` whose chosen lifts `w C` lie in the open `V` inject into the
curves of `V` contracted by a morphism `τ` lying over `σ` through integral morphisms. -/
private theorem encard_le_encard_setOf_isExceptionalCurve {T S S' Y' : Scheme.{0}}
    [CompactSpace S] (V : T.Opens) (p : T ⟶ S) (g' : Y' ⟶ S') [IsIntegralHom (V.ι ≫ p)]
    [IsIntegralHom g'] {σ : S ⟶ S'} {τ : V.toScheme ⟶ Y'} (hτ : τ ≫ g' = (V.ι ≫ p) ≫ σ)
    (w : S.IdealSheafData → T)
    (hw : ∀ C, IsExceptionalCurve σ C → closure {p (w C)} = (C.support : Set S))
    (hwcl : ∀ C, IsExceptionalCurve σ C → ¬ IsClosed {p (w C)}) (A : Set S.IdealSheafData)
    (hA : ∀ C ∈ A, IsExceptionalCurve σ C ∧ w C ∈ (V : Set T)) :
    A.encard ≤ {D | IsExceptionalCurve τ D}.encard := by
  let F : S.IdealSheafData → V.toScheme.IdealSheafData := fun C ↦
    Scheme.IdealSheafData.vanishingIdeal ⟨closure (V.ι ⁻¹' {w C}), isClosed_closure⟩
  have hpt : ∀ C ∈ A, ∃ a : V.toScheme, V.ι a = w C ∧ V.ι ⁻¹' {w C} = {a} := by
    intro C hC
    obtain ⟨a, ha⟩ : w C ∈ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      exact (hA C hC).2
    refine ⟨a, ha, Set.ext fun x ↦ ?_⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff, ← ha]
    exact V.ι.isOpenEmbedding.injective.eq_iff
  have hinj : Set.InjOn F A := by
    intro C hC C' hC' hFF
    obtain ⟨a, ha, hpa⟩ := hpt C hC
    obtain ⟨a', ha', hpa'⟩ := hpt C' hC'
    have hcl := congrArg (fun I : V.toScheme.IdealSheafData ↦ (I.support : Set V.toScheme)) hFF
    simp only [F, Scheme.IdealSheafData.coe_support_vanishingIdeal, hpa, hpa'] at hcl
    have hww : w C = w C' := by rw [← ha, ← ha', (inseparable_iff_closure_eq.mpr hcl).eq]
    exact eq_of_isCurveIn_of_support_eq (hA C hC).1.1 (hA C' hC').1.1
      (by rw [← hw C (hA C hC).1, ← hw C' (hA C' hC').1, hww])
  rw [← hinj.encard_image]
  refine Set.encard_le_encard ?_
  rintro _ ⟨C, hC, rfl⟩
  obtain ⟨a, ha, hpa⟩ := hpt C hC
  simp only [F, hpa]
  exact isExceptionalCurve_vanishingIdeal_closure (V.ι ≫ p) g' hτ (hA C hC).1
    (by rw [Scheme.Hom.comp_apply, ha, hw C (hA C hC).1])
    (by rw [Scheme.Hom.comp_apply, ha]; exact hwcl C (hA C hC).1)

/-- Let `σk : S_K̄ ⟶ S'_K̄` be the base change of `σ : S ⟶ S'`, and `V` an irreducible component of
`S_K̄` whose generic point lies over the open `W` on which `σ` is an open immersion. Then `σk`
restricts to a proper birational morphism `τ` from `V` onto a normal surface over `K̄`, and the
curves contracted by `σ` with chosen lifts `w C` in `V` are at most as many as those contracted
by `τ`. -/
private theorem exists_restrict_component (K : Type) [Field K] [CharZero K] {S S' : Scheme.{0}}
    (sS : S ⟶ Spec (.of K)) (sS' : S' ⟶ Spec (.of K)) (hS : IsNormalVariety K sS)
    (hS' : IsNormalVariety K sS') (hdim' : topologicalKrullDim S' = 2) {σ : S ⟶ S'}
    (σk : (pullback sS (specAlgClosure K) : Scheme.{0}) ⟶ pullback sS' (specAlgClosure K))
    [IsProper σk]
    (hσq : σk ≫ pullback.fst sS' (specAlgClosure K) = pullback.fst sS (specAlgClosure K) ≫ σ)
    (hσsnd : σk ≫ pullback.snd sS' (specAlgClosure K) = pullback.snd sS (specAlgClosure K))
    (W : S.Opens) [IsOpenImmersion ((pullback.fst sS (specAlgClosure K) ⁻¹ᵁ W).ι ≫ σk)]
    {Z : Set (pullback sS (specAlgClosure K) : Scheme.{0})} (hZ : Z ∈ irreducibleComponents _)
    {V : (pullback sS (specAlgClosure K) : Scheme.{0}).Opens} (hV : (V : Set _) = Z)
    (hVv : IsNormalVariety (AlgebraicClosure K) (V.ι ≫ pullback.snd sS (specAlgClosure K)))
    {ζ : (pullback sS (specAlgClosure K) : Scheme.{0})} (hζZ : ζ ∈ Z)
    (hζW : pullback.fst sS (specAlgClosure K) ζ ∈ W)
    (w : S.IdealSheafData → (pullback sS (specAlgClosure K) : Scheme.{0}))
    (hw : ∀ C, IsExceptionalCurve σ C →
      closure {pullback.fst sS (specAlgClosure K) (w C)} = (C.support : Set S))
    (hwcl : ∀ C, IsExceptionalCurve σ C → ¬ IsClosed {pullback.fst sS (specAlgClosure K) (w C)}) :
    ∃ (Y : Scheme.{0}) (sY : Y ⟶ Spec (.of (AlgebraicClosure K))) (τ : V.toScheme ⟶ Y),
      IsNormalVariety (AlgebraicClosure K) sY ∧ topologicalKrullDim Y = 2 ∧
      τ ≫ sY = V.ι ≫ pullback.snd sS (specAlgClosure K) ∧ IsProper τ ∧
      IsBirationalMorphism τ ∧
      {C : S.IdealSheafData | IsExceptionalCurve σ C ∧ w C ∈ Z}.encard ≤
        {D | IsExceptionalCurve τ D}.encard := by
  have := isIntegralHom_specAlgClosure K
  obtain ⟨_, _, _, _, _⟩ := instances_of_isNormalVariety hS
  obtain ⟨_, _, _, _, _⟩ := instances_of_isNormalVariety hVv
  obtain ⟨Z', hZ', hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (hZ.1.image σk.base σk.continuous.continuousOn)
  obtain ⟨V', hV', hV'v, hV'd, -⟩ := baseChange_component K sS' hS' hdim' hZ'
  obtain ⟨_, _, _, _, _⟩ := instances_of_isNormalVariety hV'v
  have hrange : Set.range (V.ι ≫ σk) ⊆ Set.range V'.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, hV']
    refine hsub ⟨V.ι x, ?_, by simp⟩
    rw [← hV, ← Scheme.Opens.range_ι]
    exact ⟨x, rfl⟩
  let σZ := IsOpenImmersion.lift V'.ι (V.ι ≫ σk) hrange
  have hfac : σZ ≫ V'.ι = V.ι ≫ σk := IsOpenImmersion.lift_fac _ _ _
  have : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι, hV]
    exact isClosed_of_mem_irreducibleComponents Z hZ)
  have : IsClosedImmersion V'.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι, hV']
    exact isClosed_of_mem_irreducibleComponents Z' hZ')
  have : IsProper σZ := by
    have : IsProper (σZ ≫ V'.ι) := by
      rw [hfac]
      infer_instance
    exact IsProper.of_comp σZ V'.ι
  have hW'ne : ((V.ι ⁻¹ᵁ (pullback.fst sS (specAlgClosure K) ⁻¹ᵁ W) : V.toScheme.Opens) :
      Set V.toScheme).Nonempty :=
    ⟨⟨ζ, show ζ ∈ (V : Set _) by rwa [hV]⟩, hζW⟩
  have := isOpenImmersion_preimage_ι_comp hfac (pullback.fst sS (specAlgClosure K) ⁻¹ᵁ W)
  refine ⟨_, _, σZ, hV'v, hV'd, by rw [← Category.assoc, hfac, Category.assoc, hσsnd],
    inferInstance, MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' σZ _ hW'ne,
    encard_le_encard_setOf_isExceptionalCurve V _ (V'.ι ≫ pullback.fst sS' (specAlgClosure K))
      (by rw [reassoc_of% hfac, hσq, Category.assoc]) w hw hwcl _ fun C hC ↦ ⟨hC.1, ?_⟩⟩
  rw [hV]
  exact hC.2

/-- **Uniform bound on contracted curves.** Over a field of characteristic zero, a normal surface
`S` admits a bound `M` on the number of curves contracted by any proper birational morphism onto
a normal surface. -/
private theorem exists_encard_setOf_isExceptionalCurve_le_of_charZero (K : Type) [Field K]
    [CharZero K] {S : Scheme.{0}} (sS : S ⟶ Spec (.of K)) (hS : IsNormalVariety K sS)
    (hdim : topologicalKrullDim S = 2) :
    ∃ M : ℕ, ∀ (S' : Scheme.{0}) (sS' : S' ⟶ Spec (.of K)) (σ : S ⟶ S'),
      IsNormalVariety K sS' → topologicalKrullDim S' = 2 → σ ≫ sS' = sS →
        IsProper σ → IsBirationalMorphism σ →
          {C : S.IdealSheafData | IsExceptionalCurve σ C}.encard ≤ M := by
  classical
  have := isIntegralHom_specAlgClosure K
  have := flat_specAlgClosure K
  obtain ⟨_, _, _, -⟩ := isNormal_baseChange_algClosure K sS hS hdim
  have : IsNoetherian (pullback sS (specAlgClosure K) : Scheme.{0}) := ⟨⟩
  have hfin := NoetherianSpace.finite_irreducibleComponents
    (α := (pullback sS (specAlgClosure K) : Scheme.{0}))
  choose! U hUZ hUv hUd hζ using fun (Z : Set (pullback sS (specAlgClosure K) : Scheme.{0}))
    (hZ : Z ∈ irreducibleComponents _) ↦ baseChange_component K sS hS hdim hZ
  choose! M hM using fun (Z : Set (pullback sS (specAlgClosure K) : Scheme.{0}))
    (hZ : Z ∈ irreducibleComponents _) ↦
    MMP.Mori.exists_encard_setOf_isExceptionalCurve_le (AlgebraicClosure K) _ (hUv Z hZ)
      (hUd Z hZ)
  refine ⟨∑ Z ∈ hfin.toFinset, M Z, ?_⟩
  intro S' sS' σ hS' hdim' hσs hσp hσb
  obtain ⟨_, _, _, _, _⟩ := instances_of_isNormalVariety hS
  obtain ⟨σk, _, hσq, hσsnd, hσW⟩ := exists_baseChange_hom K sS sS' σ hσs hσp
  have : Nonempty S := ⟨genericPoint S⟩
  obtain ⟨W, ⟨w₀, hw₀⟩, hWo⟩ := hσb.exists_isOpenImmersion
  have := hσW W hWo
  set p := pullback.fst sS (specAlgClosure K)
  have hw0 : ∀ C : S.IdealSheafData, IsExceptionalCurve σ C →
      ∃ w, closure {p w} = (C.support : Set S) ∧ ¬ IsClosed {p w} := by
    intro C hC
    obtain ⟨e, he, hecl⟩ := hC.1.exists_isGenericPoint
    obtain ⟨w, rfl⟩ := p.surjective e
    exact ⟨w, he, hecl⟩
  choose! w hw hwcl using hw0
  let Zc : S.IdealSheafData → Set (pullback sS (specAlgClosure K) : Scheme.{0}) :=
    fun C ↦ irreducibleComponent (w C)
  have hZc : ∀ C, Zc C ∈ irreducibleComponents _ := fun C ↦
    irreducibleComponent_mem_irreducibleComponents _
  have key : ∀ Z ∈ irreducibleComponents (pullback sS (specAlgClosure K) : Scheme.{0}),
      {C : S.IdealSheafData | IsExceptionalCurve σ C ∧ Zc C = Z}.encard ≤ M Z := by
    intro Z hZ
    obtain ⟨ζ, hζZ, hζgen⟩ := hζ Z hZ
    obtain ⟨Y, sY, τ, hY, hYd, hτs, hτp, hτb, hle⟩ := exists_restrict_component K sS sS' hS hS'
      hdim' σk hσq hσsnd W hZ (hUZ Z hZ) (hUv Z hZ) hζZ ((hζgen w₀).mem_open W.isOpen hw₀) w hw
      hwcl
    refine le_trans ?_ (hle.trans (hM Z hZ Y sY τ hY hYd hτs hτp hτb))
    exact Set.encard_le_encard fun C hC ↦ ⟨hC.1, hC.2 ▸ mem_irreducibleComponent⟩
  calc {C : S.IdealSheafData | IsExceptionalCurve σ C}.encard
      ≤ (⋃ Z ∈ hfin.toFinset, {C : S.IdealSheafData | IsExceptionalCurve σ C ∧ Zc C = Z}).encard :=
        Set.encard_le_encard fun C hC ↦ Set.mem_biUnion (by simpa using hZc C) ⟨hC, rfl⟩
    _ ≤ ∑ Z ∈ hfin.toFinset, {C : S.IdealSheafData | IsExceptionalCurve σ C ∧ Zc C = Z}.encard :=
        Finset.set_encard_biUnion_le _ _
    _ ≤ ∑ Z ∈ hfin.toFinset, (M Z : ℕ∞) :=
        Finset.sum_le_sum fun Z hZ ↦ key Z (by simpa using hZ)
    _ = _ := by push_cast; rfl

end MMP.Mori.ContractionChainBound

namespace MMP.Mori

/-- Over a field `K` of characteristic zero, a normal surface `S` admits a bound `M` on the length
`r` of every chain `S ≅ X 0 → X 1 → ⋯ → X r` of proper birational `K`-morphisms of normal
surfaces in which each `f i : X i ⟶ X (i + 1)` maps some integral curve of `X i` to a point. -/
@[mmp "lem_fa4_normal_surface_bounded_contractions"]
public theorem exists_forall_length_le_of_isExceptionalCurve_chain
    (K : Type) [Field K] [CharZero K] {S : Scheme.{0}}
    (sS : S ⟶ Spec (.of K)) (hS : IsNormalVariety K sS) (hdim : topologicalKrullDim S = 2) :
    ∃ M : ℕ, ∀ (r : ℕ) (X : ℕ → Scheme.{0}) (sX : ∀ i, X i ⟶ Spec (.of K))
      (f : ∀ i, X i ⟶ X (i + 1)) (e : S ≅ X 0),
      e.hom ≫ sX 0 = sS →
      (∀ i ≤ r, IsNormalVariety K (sX i) ∧ topologicalKrullDim (X i) = 2) →
      (∀ i < r, f i ≫ sX (i + 1) = sX i ∧ IsProper (f i) ∧ IsBirationalMorphism (f i) ∧
        ∃ C : (X i).IdealSheafData, IsExceptionalCurve (f i) C) →
      r ≤ M :=
  (ContractionChainBound.exists_encard_setOf_isExceptionalCurve_le_of_charZero K sS hS hdim).imp
    (ContractionChainBound.length_le_of_forall_encard_le K sS hS hdim)

end MMP.Mori
