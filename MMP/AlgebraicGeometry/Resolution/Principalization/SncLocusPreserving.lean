module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Basic
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Singularities.Semismooth.SingularLocus
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Divisor.EffectiveCartierCoheight
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus

/-!
# Simultaneous principalization preserving the joint snc locus

Let `X` be a variety over an algebraically closed field `k` of characteristic zero, let
`D_i` (`i ∈ κ`) be finitely many divisors on `X` and let `I_j` (`j ∈ ι`) be finitely many
nonzero ideal sheaves on `X`. There is a projective birational morphism `g : Y ⟶ X` from a
smooth variety `Y` such that every `I_j 𝒪_Y` is invertible, and the exceptional set `Ex(g)`, the
strict transforms of the `D_i` and all the inverse images `g⁻¹ V(I_j)` lie in one snc divisor
of `Y`. Moreover `g` is an isomorphism over the open locus of `X` where `X` is smooth, every
`I_j` is invertible, and the reduced union `⋃_j V(I_j) ∪ ⋃_i Supp D_i` is an snc divisor.

## Main results

* `MMP.Resolution.exists_isResolutionOfVariety_isSNCSubset_isIso_restrict`: simultaneous
  principalization of finitely many nonzero ideals, making finitely many divisors snc, by a
  resolution which is an isomorphism over the joint snc locus.

## Implementation notes

The inverse image ideal `I_j 𝒪_Y` is `(I j).comap g`; "invertible" for a nonzero ideal sheaf on
an integral scheme is `Stacks.Divisors.IsEffectiveCartierDivisor`. The divisors may have
coefficients in any `R` with a zero, since only their supports enter.

For a closed subset `S ⊆ Y`, containing `Ex(g)` and the strict transform of `Supp D_i` is the
same as containing `Ex(g)` and `g⁻¹(Supp D_i)`: off `Ex(g)` the two inverse images agree, and
`S` is closed. The snc divisor is a closed subset `S` with `MMP.Mori.IsSNCSubset`.

"An isomorphism over the locus `U`" is stated for every open `U ⊆ X` which is smooth over `k`,
on which every `I_j` is invertible, and on which the union of the `V(I_j)` and the `Supp D_i` is
an snc divisor; such opens are exactly the opens contained in that locus.

The proof's auxiliary lemmas live in the namespace
`Proof_thm_mmp_strong_simultaneous_snc_principalization`, opened only for the main result.

The morphism is a composite of four steps.

1. A strong resolution `r : Z ⟶ X`, an isomorphism over the smooth locus of `X`, hence over
   every such `U`; let `B ⊆ X` be its biregular locus.
2. On `Z` the ideal `J = (I_{X ∖ B} · ∏_j I_j) 𝒪_Z · ∏_Q I_Q`, where `Q` runs over the strict
   transforms on `Z` of the prime divisors of the `D_i` whose generic points lie in `B`. Every
   factor `I_Q` is invertible since `Z` is smooth, so `J` is invertible over `r⁻¹(U)`. Its
   support is `r⁻¹(X ∖ B) ∪ r⁻¹(⋃ V(I_j)) ∪ ⋃ Q`, which contains `r⁻¹(T)` for the joint set
   `T = ⋃_j V(I_j) ∪ ⋃_i Supp D_i` and meets `r⁻¹(B)` in `r⁻¹(T) ∩ r⁻¹(B)`.
3. The blow-up `p : Bl_J Z ⟶ Z`, followed by a strong resolution `s : Z₁ ⟶ Bl_J Z`. Each factor
   of `J` becomes invertible on `Bl_J Z` (Stacks, Tag 080A), and `p` is an isomorphism over every
   open on which `J` is already invertible (Stacks, Tags 0805 and 0807); since `Z` is smooth, so
   is `h₁ = s ≫ p`. The exceptional set of `h = h₁ ≫ r` lies in `h₁⁻¹ V(J)`.
4. The snc-preserving log resolution `f : Y ⟶ Z₁` of the reduced divisor whose components are
   the prime divisors of the effective Cartier divisor `J 𝒪_{Z₁}`.

Then `g = f ≫ h` works: over `h⁻¹(U) ≅ U` the support of `J 𝒪_{Z₁}` is the inverse image of `T`,
which is snc there, so `f` is an isomorphism over `h⁻¹(U)`.

## References

* [J. Kollár, *Lectures on resolution of singularities*], 3.26, 3.36
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 0.2, 0.3
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Resolution

universe u

namespace Proof_thm_mmp_strong_simultaneous_snc_principalization

/-! ### Isomorphisms over opens -/

/-- The inverse of an isomorphism over `V` is a section of `f` over `V`. -/
private theorem apply_ι_inv_morphismRestrict {X Y : Scheme.{u}} (f : Y ⟶ X) (V : X.Opens)
    [IsIso (f ∣_ V)] (x : (V : Scheme.{u})) :
    f ((f ⁻¹ᵁ V).ι (inv (f ∣_ V) x)) = V.ι x := by
  rw [← ι_morphismRestrict_apply]
  congr 1
  rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
  rfl

/-- A morphism of irreducible schemes which is an isomorphism over a nonempty open is
birational. -/
private theorem isBirationalMorphism_of_isIso_restrict {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (g : Y ⟶ X) (V : X.Opens) [IsIso (g ∣_ V)]
    (hV : (V : Set X).Nonempty) : IsBirationalMorphism g := by
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g _ _
    ⟨_, (inv (g ∣_ V) ⟨hV.some, hV.some_mem⟩).2⟩ hV le_rfl ?_
  rwa [Scheme.Hom.resLE_eq_morphismRestrict]

/-- A morphism to an irreducible scheme which is an isomorphism over a nonempty open is
dominant. -/
private theorem isDominant_of_isIso_restrict {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : Y ⟶ X) (V : X.Opens) [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) : IsDominant g :=
  ⟨Dense.mono (fun x hx => ⟨_, (apply_ι_inv_morphismRestrict g V ⟨x, hx⟩).trans rfl⟩)
    (V.isOpen.dense hV)⟩

/-- A composite of isomorphisms over `V` and over its inverse image is an isomorphism over `V`. -/
private theorem isIso_restrict_comp {X Y W : Scheme.{u}} (h : W ⟶ Y) (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] [IsIso (h ∣_ g ⁻¹ᵁ V)] : IsIso ((h ≫ g) ∣_ V) := by
  rw [morphismRestrict_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ ‹_› ‹_›

/-- An isomorphism over `V` preserves the coheight of the points over `V`. -/
private theorem coheight_apply_of_isIso_restrict {X Y : Scheme.{u}} (f : Y ⟶ X) (V : X.Opens)
    [IsIso (f ∣_ V)] {y : Y} (hy : f y ∈ V) : Order.coheight (f y) = Order.coheight y := by
  let y' : ((f ⁻¹ᵁ V : Y.Opens) : Scheme.{u}) := ⟨y, hy⟩
  have e : V.ι ((f ∣_ V) y') = f y := ι_morphismRestrict_apply f V y'
  have h1 := coheight_eq_of_isOpenImmersion (f ⁻¹ᵁ V).ι (x := y')
  rw [← e, coheight_eq_of_isOpenImmersion, coheight_eq_of_isOpenImmersion (f ∣_ V), ← h1]
  rfl

/-! ### Smooth loci -/

/-- An open of `X` which is smooth over `k` lies in the smooth locus. -/
private theorem le_smoothLocus_of_isSmoothScheme {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {U : X.Opens}
    (hU : IsSmoothScheme (U.ι ≫ sX)) : U ≤ smoothLocus sX := by
  have : LocallyOfFinitePresentation (U.ι ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := U.ι ≫ sX)).mpr inferInstance
  exact le_smoothLocus _ ((isSmoothScheme_iff _).1 hU)

/-- An open in the smooth locus is smooth over `k`. -/
private theorem isSmoothScheme_of_le_smoothLocus {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {U : X.Opens} (hU : U ≤ smoothLocus sX) :
    IsSmoothScheme (U.ι ≫ sX) := by
  refine top_le_iff.1 fun x' _ => ?_
  obtain ⟨V, hxV, hV⟩ := mem_smoothLocus_iff.1 (hU x'.2)
  refine mem_smoothLocus_iff.2 ⟨U.ι ⁻¹ᵁ V, hxV, ?_⟩
  have := hV
  rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι U.ι (le_refl (U.ι ⁻¹ᵁ V)), Category.assoc]
  infer_instance

/-- If `p` is an isomorphism over an open `V` of a smooth `k`-scheme, then `p⁻¹(V)` lies in the
smooth locus of the source. -/
private theorem preimage_le_smoothLocus_of_isIso_restrict {k : Type u} [Field k]
    {Z W : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType sZ] (hZ : IsSmoothScheme sZ)
    (p : W ⟶ Z) (V : Z.Opens) [IsIso (p ∣_ V)] : p ⁻¹ᵁ V ≤ smoothLocus (p ≫ sZ) := by
  have : Smooth sZ := Aux.smooth_of_isSmoothScheme' sZ hZ
  refine le_smoothLocus _ ?_
  have e : (p ⁻¹ᵁ V).ι ≫ p ≫ sZ = (p ∣_ V) ≫ V.ι ≫ sZ := by
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  rw [e]
  infer_instance

/-! ### Exceptional sets of composites -/

/-- The exceptional set of a composite `π ≫ g`, with `π` an isomorphism over an open `V` whose
complement lies in `B`, and `B` containing the exceptional set of `g`, lies in `π⁻¹ B`. -/
private theorem exceptionalSet_comp_subset {X Y Y' : Scheme.{u}} (g : Y ⟶ X) [IsProper g]
    (π : Y' ⟶ Y) (V : Y.Opens) (hπ : IsBiregular π V)
    {B : Set Y} (hB : (exceptionalSet g : Set Y) ⊆ B) (hV : (V : Set Y)ᶜ ⊆ B) :
    (exceptionalSet (π ≫ g) : Set Y') ⊆ π ⁻¹' B := by
  intro y' hy'
  by_contra hyB
  apply hy'
  have hy : g (π y') ∈ biregularLocus g :=
    not_not.mp (show π y' ∉ (exceptionalSet g : Set Y) from fun h => hyB (hB h))
  set V0 : X.Opens := biregularLocus g ⊓
    ⟨(g '' (V : Set Y)ᶜ)ᶜ, (g.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
  have : IsIso (g ∣_ V0) := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  have : IsIso (π ∣_ g ⁻¹ᵁ V0) := isBiregular_iff_le_biregularLocus.mpr
    (le_trans (fun y hy => not_not.mp fun hyV => hy.2 ⟨y, hyV, rfl⟩) (le_biregularLocus hπ))
  refine le_biregularLocus (isIso_restrict_comp π g V0) ⟨hy, ?_⟩
  rintro ⟨c, hcV, hc⟩
  rw [Scheme.Hom.comp_apply] at hc
  have hcB : g c ∈ biregularLocus g := by rwa [hc]
  have hinj : c = π y' :=
    ((MMP.Threefold.Resolution.specializes_of_mem_biregularLocus g hcB hy
      (hc ▸ specializes_rfl)).antisymm
      (MMP.Threefold.Resolution.specializes_of_mem_biregularLocus g hy hcB
        (hc ▸ specializes_rfl))).eq
  exact hyB (by rw [Set.mem_preimage, ← hinj]; exact hV hcV)

/-! ### Ideal sheaves and effective Cartier divisors -/

/-- A point lies in a finite supremum of closed sets if and only if it lies in one of them. -/
private theorem mem_iSup_closeds {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (f : ι → Closeds X) (x : X) :
    x ∈ ((⨆ i, f i : Closeds X) : Set X) ↔ ∃ i, x ∈ (f i : Set X) := by
  have := Fintype.ofFinite ι
  rw [← Finset.sup_univ_eq_iSup, Closeds.coe_finset_sup]
  simp

/-- The support of a finite product of ideal sheaves is the union of the supports. -/
private theorem coe_support_prod {X : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) :
    ((∏ j ∈ s, I j).support : Set X) = ⋃ j ∈ s, ((I j).support : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.IdealSheafData.support_mul, Closeds.coe_sup, ih,
      Finset.set_biUnion_insert]

/-- The inverse image of a finite product of ideal sheaves is the product of the inverse
images. -/
private theorem comap_prod {X Y : Scheme.{u}} (f : Y ⟶ X) {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) : (∏ j ∈ s, I j).comap f = ∏ j ∈ s, (I j).comap f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
      Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.comap_top]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, AlgebraicGeometry.comap_mul, ih]

/-- An ideal sheaf whose support misses the image of `f` pulls back to the unit ideal. -/
private theorem comap_eq_top_of_disjoint {X Y : Scheme.{u}} (f : Y ⟶ X) (I : X.IdealSheafData)
    (h : ∀ y, f y ∉ (I.support : Set X)) : I.comap f = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  ext y
  rw [Scheme.IdealSheafData.support_comap]
  simpa using h y

/-- The generic point of an integral scheme lies off the support of every nonzero ideal sheaf. -/
private theorem genericPoint_notMem_support_of_ne_bot {X : Scheme.{u}} [IsIntegral X]
    {I : X.IdealSheafData} (hI : I ≠ ⊥) : genericPoint X ∉ (I.support : Set X) := by
  intro h
  refine hI (Scheme.IdealSheafData.support_eq_top_iff.mp (Closeds.ext ?_))
  refine Set.eq_univ_of_univ_subset ?_
  rw [← (genericPoint_spec X).def]
  exact closure_minimal (Set.singleton_subset_iff.mpr h) I.support.isClosed

/-- The generic point of an integral scheme lies off every prime divisor. -/
private theorem genericPoint_notMem_support_primeDivisor {X : Scheme.{u}} [IsIntegral X]
    (E : MMP.Mori.PrimeDivisor X) : genericPoint X ∉ (E.support : Set X) := by
  intro hE
  have h1 : AlgebraicGeometry.PrimeDivisor.genericPoint E ⤳ genericPoint X :=
    Aux.genericPoint_specializes_of_mem_support E hE
  have h2 : AlgebraicGeometry.PrimeDivisor.genericPoint E = genericPoint X :=
    (h1.antisymm (genericPoint_specializes _)).eq
  have h3 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
  rw [h2, Order.coheight_eq_zero.2] at h3
  · exact absurd h3 (by norm_num)
  · intro b hb
    rw [Scheme.le_iff_specializes] at hb ⊢
    exact genericPoint_specializes _

/-- **Effective Cartier divisors pull back along a dominant morphism of integral schemes.** -/
private theorem isEffectiveCartierDivisor_comap_of_isDominant {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g] (F : X.IdealSheafData)
    (hF : Stacks.Divisors.IsEffectiveCartierDivisor F) :
    Stacks.Divisors.IsEffectiveCartierDivisor (F.comap g) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun y => ?_
  obtain ⟨W, hyW, -, t, ht, hgen⟩ :=
    Stacks.Blowup.exists_affineOpens_ideal_eq_span_le F hF (g y) ⊤ trivial
  obtain ⟨-, ⟨V, hV, rfl⟩, hyV, hVsub⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ g ⁻¹ᵁ (W : X.Opens) from hyW) (g ⁻¹ᵁ (W : X.Opens)).isOpen
  have hVW : (V : Y.Opens) ≤ g ⁻¹ᵁ (W : X.Opens) := hVsub
  refine ⟨V, hV, hyV, (g.appLE W.1 V hVW).hom t,
    ?_, Stacks.IdealSheaf.ideal_comap_eq_span F g W ⟨V, hV⟩ hVW hgen⟩
  have : Nonempty (V : Y.Opens) := ⟨⟨y, hyV⟩⟩
  refine IsRegular.of_ne_zero' ?_
  intro h0
  have hb := Scheme.basicOpen_appLE g V W.1 hVW t
  rw [h0, Scheme.basicOpen_zero] at hb
  have : Nonempty (W.1 : X.Opens) := ⟨⟨g y, hyW⟩⟩
  have hne : (X.basicOpen t : Set X).Nonempty := Set.nonempty_iff_ne_empty.2 fun hc =>
    ht.ne_zero ((basicOpen_eq_bot_iff _).1 (Opens.coe_eq_empty.1 hc))
  obtain ⟨y', hy'⟩ := g.denseRange.exists_mem_open (X.basicOpen t).isOpen hne
  have hne' : ((V : Y.Opens) ⊓ g ⁻¹ᵁ (X.basicOpen t) : Set Y).Nonempty :=
    (IrreducibleSpace.isIrreducible_univ Y).2 _ _ V.isOpen (g ⁻¹ᵁ (X.basicOpen t)).isOpen
      ⟨y, trivial, hyV⟩ ⟨y', trivial, hy'⟩ |>.mono fun _ h => h.2
  obtain ⟨z, hz⟩ := hne'
  have : z ∈ ((V ⊓ g ⁻¹ᵁ X.basicOpen t : Y.Opens) : Set Y) := hz
  rwa [← hb] at this

/-- The generic point of an integral scheme lies off the support of an effective Cartier
divisor. -/
private theorem genericPoint_notMem_support_of_isEffectiveCartierDivisor {Y : Scheme.{u}}
    [IsIntegral Y] {I : Y.IdealSheafData} (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    genericPoint Y ∉ (I.support : Set Y) := by
  intro hη
  obtain ⟨f, hf, hfI⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor I hI
      (genericPoint Y)
  have htop : IdealSheafData.stalk I (genericPoint Y) = ⊤ := by
    rw [hfI, Ideal.span_singleton_eq_top]
    exact (isUnit_iff_ne_zero (a := (f : Y.functionField))).2 hf.ne_zero
  exact ((IdealSheafData.stalk_eq_top_iff_notMem_support _ _).1 htop) hη

/-- **The blow-up is an isomorphism over every open on which the centre is already an effective
Cartier divisor** (Stacks, Tags 0805 and 0807). -/
private theorem isIso_blowUpToBase_restrict_of_isEffectiveCartierDivisor {Z : Scheme.{u}}
    (J : Z.IdealSheafData) (V : Z.Opens)
    (hV : Stacks.Divisors.IsEffectiveCartierDivisor (J.comap V.ι)) :
    IsIso (blowUpToBase J ∣_ V) := by
  obtain ⟨e, he⟩ := AlgebraicGeometry.exists_iso_blowUp_comap_opens J V
  have := Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor _ hV
  have h : e.hom ≫ (blowUpToBase J ∣_ V) = blowUpToBase (J.comap V.ι) := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, he]
  have h' : (blowUpToBase J ∣_ V) = e.inv ≫ blowUpToBase (J.comap V.ι) := by
    rw [← h, Iso.inv_hom_id_assoc]
  rw [h']
  infer_instance

/-! ### Prime divisors -/

/-- **Strict transforms of prime divisors under an isomorphism over `V`.** For a finite set of
prime divisors on `X` there is a finite set of prime divisors on `Y`, each lying over their union,
which covers the points of the inverse image of their union lying over `V`. -/
private theorem exists_finset_primeDivisor_preimage {X Y : Scheme.{u}} (r : Y ⟶ X)
    (V : X.Opens) [IsIso (r ∣_ V)] (Pset : Finset (MMP.Mori.PrimeDivisor X)) :
    ∃ Qset : Finset (MMP.Mori.PrimeDivisor Y),
      (∀ Q ∈ Qset, (Q.support : Set Y) ⊆ r ⁻¹' (⋃ P ∈ Pset, (P.support : Set X))) ∧
      ∀ y, r y ∈ V → r y ∈ (⋃ P ∈ Pset, (P.support : Set X)) →
        ∃ Q ∈ Qset, y ∈ (Q.support : Set Y) := by
  classical
  -- the generic point of the strict transform of a prime divisor meeting `V`
  have hζ : ∀ P : MMP.Mori.PrimeDivisor X, P.genericPoint ∈ V →
      ∃ ζ : Y, r ζ = P.genericPoint ∧ Order.coheight ζ = 1 ∧
        ∀ y, r y ∈ V → r y ∈ (P.support : Set X) → ζ ⤳ y := by
    intro P hP
    set x₀ : (V : Scheme.{u}) := ⟨P.genericPoint, hP⟩
    have hrζ : r ((r ⁻¹ᵁ V).ι (inv (r ∣_ V) x₀)) = P.genericPoint :=
      apply_ι_inv_morphismRestrict r V x₀
    refine ⟨(r ⁻¹ᵁ V).ι (inv (r ∣_ V) x₀), hrζ, ?_, ?_⟩
    · rw [← coheight_apply_of_isIso_restrict r V (by rwa [hrζ]), hrζ]
      exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
    · intro y hyV hyP
      let y' : ((r ⁻¹ᵁ V : Y.Opens) : Scheme.{u}) := ⟨y, hyV⟩
      have h1 : x₀ ⤳ (r ∣_ V) y' := by
        rw [← V.ι.isOpenEmbedding.isInducing.specializes_iff, ι_morphismRestrict_apply]
        exact Aux.genericPoint_specializes_of_mem_support P hyP
      have h2 := h1.map (inv (r ∣_ V)).continuous
      have h3 : inv (r ∣_ V) ((r ∣_ V) y') = y' := by
        rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
        rfl
      rw [h3] at h2
      exact h2.map (r ⁻¹ᵁ V).ι.continuous
  choose ζ hζr hζc hζs using hζ
  set Pf : Finset (MMP.Mori.PrimeDivisor X) := Pset.filter fun P => P.genericPoint ∈ V
  refine ⟨Pf.attach.image fun P : {P // P ∈ Pf} =>
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne (ζ P.1 (Finset.mem_filter.1 P.2).2)
      (hζc _ _), ?_, ?_⟩
  · intro Q hQ
    obtain ⟨⟨P, hP⟩, -, rfl⟩ := Finset.mem_image.1 hQ
    have hPs := Finset.mem_filter.1 hP
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    refine closure_minimal (Set.singleton_subset_iff.2 ?_)
      ((isClosed_biUnion_finset fun P _ => P.idealSheaf.support.isClosed).preimage r.continuous)
    rw [Set.mem_preimage, hζr]
    refine Set.mem_biUnion hPs.1 ?_
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  · intro y hyV hyP
    obtain ⟨P, hP, hyP'⟩ := Set.mem_iUnion₂.1 hyP
    have hPV : P.genericPoint ∈ V :=
      (Aux.genericPoint_specializes_of_mem_support P hyP').mem_open V.isOpen hyV
    have hPf' : P ∈ Pf := Finset.mem_filter.2 ⟨hP, hPV⟩
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨P, hPf'⟩), ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact specializes_iff_mem_closure.1 (hζs P _ y hyV hyP')

/-- The support of an effective Cartier divisor on a scheme locally of finite type over a field
is the union of finitely many prime divisors. -/
private theorem exists_finset_primeDivisor_sup_eq {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [CompactSpace Y] {I : Y.IdealSheafData}
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    ∃ s : Finset (MMP.Mori.PrimeDivisor Y),
      (s.sup fun E => (E.idealSheaf.support : Set Y)) = I.support := by
  classical
  let : Y.Over (Spec (.of k)) := ⟨sY⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := ‹LocallyOfFiniteType sY›
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : AlgebraicGeometry.IsNoetherian Y := {}
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf I.support.isClosed
  -- every irreducible component of `Supp I` is a prime divisor
  have hW : ∀ W ∈ componentsOf (I.support : Set Y),
      ∃ E : MMP.Mori.PrimeDivisor Y, (E.support : Set Y) = W := by
    intro W hW
    have hWc := Aux.isClosed_of_mem_componentsOf I.support.isClosed hW
    have hgen := hW.1.1.isGenericPoint_genericPoint_closure
    rw [hWc.closure_eq] at hgen
    have hc : Order.coheight hW.1.1.genericPoint = 1 := by
      refine MMP.coheight_eq_one_of_isEffectiveCartierDivisor k hI
        (hW.1.2 hgen.mem) fun y hy hyw => ?_
      have h1 : W ⊆ closure {y} := by
        rw [← hgen.def]
        exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hyw))
          isClosed_closure
      have h2 := hW.2 ⟨isIrreducible_singleton.closure,
        closure_minimal (Set.singleton_subset_iff.2 hy) I.support.isClosed⟩ h1
      have hyW : y ∈ closure {hW.1.1.genericPoint} := by
        rw [hgen.def]
        exact h2 (subset_closure rfl)
      exact (hyw.antisymm (specializes_iff_mem_closure.2 hyW)).eq
    refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc, ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hgen.def]
  choose E hE using hW
  refine ⟨hfin.toFinset.attach.image fun W => E W.1 (hfin.mem_toFinset.1 W.2), ?_⟩
  rw [Finset.sup_set_eq_biUnion]
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨E', hE', hyE'⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨⟨W, hW⟩, -, rfl⟩ := Finset.mem_image.1 hE'
    have : y ∈ (E W (hfin.mem_toFinset.1 hW)).support := hyE'
    rw [hE] at this
    exact (hfin.mem_toFinset.1 hW).1.2 this
  · intro y hy
    obtain ⟨W, hW, hyW⟩ := Set.mem_sUnion.1 (hcov hy)
    refine Set.mem_biUnion (Finset.mem_image_of_mem _
      (Finset.mem_attach _ ⟨W, hfin.mem_toFinset.2 hW⟩)) ?_
    change y ∈ (E W _).support
    rw [hE W]
    exact hyW

/-! ### Simple normal crossings -/

/-- A member of an snc family with irreducible support is a prime divisor. -/
private theorem exists_primeDivisor_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (i : ι) (hirr : IsIrreducible ((F i).support : Set X)) :
    ∃ P : MMP.Mori.PrimeDivisor X, P.idealSheaf = F i := by
  have hint := isIntegral_subscheme_of_isIrreducible s (F i) (hF.1 i).2.2 hirr
  refine ⟨⟨F i, hint, ?_⟩, rfl⟩
  have hcl := closure_subschemeι_genericPoint (F i)
  refine (hF.1 i).2.1 _ ⟨show closure _ ⊆ _ from hcl.le, fun V hV _ => ?_⟩
  exact show (V : Set X) ⊆ closure _ from hcl ▸ hV

/-- A divisor whose components are members of an snc family is snc. -/
private theorem isSNC_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (D : MMP.Mori.DivisorWithCoeffs ℤ X) (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
    MMP.Mori.DivisorWithCoeffs.IsSNC s D := by
  choose g hg using hD
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [← hg P hP]; exact (hF.1 _).2.2
  · obtain ⟨n, w, c, hw, hc, hinj⟩ := hF.2 x
    have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor X // P ∈ D.support ∧ x ∈ P.support},
        x ∈ (F (g P.1 P.2.1)).support := fun P => by rw [hg]; exact P.2.2
    refine ⟨n, w, fun P => c ⟨_, hmem P⟩, hw, fun P Q hPQ => ?_, fun P => ?_⟩
    · have h : g P.1 P.2.1 = g Q.1 Q.2.1 := congrArg Subtype.val (hinj hPQ)
      have : P.1.idealSheaf = Q.1.idealSheaf := by
        rw [← hg P.1 P.2.1, ← hg Q.1 Q.2.1, h]
      exact Subtype.ext (MMP.Mori.PrimeDivisor.ext_idealSheaf this)
    · have := hc ⟨_, hmem P⟩
      rwa [hg] at this

/-- A divisor with simple normal crossings in the sense of `MMP.Mori.IsSNCSubset` is one in the
sense of `IsSNCClosedSubset`. -/
private theorem isSNCClosedSubset_of_isSNCSubset {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {S : Closeds X} (hS : IsSNCSubset sX S) :
    IsSNCClosedSubset sX (S : Set X) := by
  classical
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · exact ⟨isClosed_empty, Or.inl rfl⟩
  · have h := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC sX hsnc
    have hsupp : (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).support = s := by
      ext E
      simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
    rwa [hsupp, hs] at h

/-- A divisor with simple normal crossings in the sense of `IsSNCClosedSubset` is one in the
sense of `MMP.Mori.IsSNCSubset`. -/
private theorem isSNCSubset_of_isSNCClosedSubset {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [NoetherianSpace X] {S : Closeds X}
    (hS : IsSNCClosedSubset sX (S : Set X)) : IsSNCSubset sX S := by
  classical
  obtain ⟨-, h | ⟨-, hfin, hfam⟩⟩ := hS
  · exact Or.inl (Closeds.ext (by rw [h]; rfl))
  · right
    have : Fintype (componentsOf (S : Set X)) := hfin.fintype
    have hP : ∀ W : componentsOf (S : Set X), ∃ P : MMP.Mori.PrimeDivisor X,
        P.idealSheaf = componentsFamily (S : Set X) W := fun W =>
      exists_primeDivisor_of_isSNCFamily hfam W (by
        rw [coe_support_componentsFamily S.isClosed W]; exact W.2.1.1)
    choose P hP using hP
    have hPs : ∀ W, (P W).support = (W : Set X) := fun W => by
      change ((P W).idealSheaf.support : Set X) = _
      rw [hP, coe_support_componentsFamily S.isClosed W]
    refine ⟨Finset.univ.image P, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.iUnion_exists,
          Set.iUnion_iUnion_eq', Set.iUnion_subset_iff]
        intro W
        rw [hPs]
        exact W.2.1.2
      · intro x hx
        obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf S.isClosed
        obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
        refine Set.mem_biUnion (x := P ⟨W, hW⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_
        rw [hPs]
        exact hxW
    · refine isSNC_of_isSNCFamily hfam _ fun Q hQ => ?_
      obtain ⟨E, hE, hQE⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hQ)
      have hQ' : Q = E := Finset.mem_singleton.1 (Finsupp.support_single_subset hQE)
      obtain ⟨W, -, rfl⟩ := Finset.mem_image.1 hE
      exact ⟨W, by rw [hQ', hP]⟩

/-! ### The principalizing ideal -/

/-- **The ideal to blow up on a partial resolution.** Let `r : Z ⟶ X` be an isomorphism over an
open `B`, on which every prime divisor is an effective Cartier divisor, and let `I_j` be finitely
many ideal sheaves and `P` finitely many prime divisors on `X`. The ideal
`J = (I_{X ∖ B} · ∏_j I_j) 𝒪_Z · ∏_Q I_Q`, with `Q` running over the strict transforms of the `P`
meeting `B`, has support `r⁻¹(X ∖ B) ∪ r⁻¹(⋃_j V(I_j) ∪ ⋃ P)`, has every `I_j 𝒪_Z` as a factor, and
is an effective Cartier divisor over every open `U ⊆ B` over which `r` is an isomorphism and the
`I_j` are invertible. -/
private theorem exists_idealSheafData_principalizing {X Z : Scheme.{u}} (r : Z ⟶ X) (B : X.Opens)
    [IsIso (r ∣_ B)]
    (hQ : ∀ Q : MMP.Mori.PrimeDivisor Z, Stacks.Divisors.IsEffectiveCartierDivisor Q.idealSheaf)
    {ι : Type*} [Finite ι] (I : ι → X.IdealSheafData) (Pset : Finset (MMP.Mori.PrimeDivisor X)) :
    ∃ J : Z.IdealSheafData,
      (∀ z, z ∈ (J.support : Set Z) ↔ r z ∉ B ∨ (∃ j, r z ∈ ((I j).support : Set X)) ∨
        r z ∈ ⋃ P ∈ Pset, (P.support : Set X)) ∧
      (∀ j, ∃ J' : Z.IdealSheafData, J = (I j).comap r * J') ∧
      ∀ U : X.Opens, IsIso (r ∣_ U) → U ≤ B →
        (∀ j, Stacks.Divisors.IsEffectiveCartierDivisor ((I j).comap U.ι)) →
        Stacks.Divisors.IsEffectiveCartierDivisor (J.comap (r ⁻¹ᵁ U).ι) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨Qset, hQsub, hQcov⟩ := exists_finset_primeDivisor_preimage r B Pset
  set IW : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal B.compl with hIW
  set K : X.IdealSheafData := IW * ∏ j, I j with hK
  set IQ : Z.IdealSheafData := ∏ Q ∈ Qset, Q.idealSheaf with hIQ
  set J : Z.IdealSheafData := K.comap r * IQ with hJ
  have hJsupp : ∀ z, z ∈ (J.support : Set Z) ↔ (r z ∉ B ∨ ∃ j, r z ∈ ((I j).support : Set X)) ∨
      ∃ Q ∈ Qset, z ∈ (Q.support : Set Z) := by
    intro z
    rw [hJ, Scheme.IdealSheafData.support_mul, Closeds.coe_sup, Set.mem_union,
      Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage, hK,
      Scheme.IdealSheafData.support_mul, Closeds.coe_sup, Set.mem_union, hIW,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, coe_support_prod, hIQ, coe_support_prod]
    simp only [Finset.mem_univ, Set.mem_iUnion, exists_prop, true_and]
    rfl
  refine ⟨J, fun z => ?_, fun j => ⟨(IW * ∏ i ∈ Finset.univ.erase j, I i).comap r * IQ, ?_⟩,
    fun U hrU hU hUc => ?_⟩
  · rw [hJsupp]
    refine ⟨?_, ?_⟩
    · rintro ((h | h) | ⟨Q, hQs, hzQ⟩)
      exacts [.inl h, .inr (.inl h), .inr (.inr (hQsub Q hQs hzQ))]
    · rintro (h | h | h)
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · by_cases hzB : r z ∈ B
        exacts [.inr (hQcov z hzB h), .inl (.inl hzB)]
  · rw [hJ, hK, ← Finset.mul_prod_erase Finset.univ I (Finset.mem_univ j)]
    simp only [AlgebraicGeometry.comap_mul]
    ring
  · have := hrU
    rw [hJ, AlgebraicGeometry.comap_mul]
    refine AlgebraicGeometry.isEffectiveCartierDivisor_mul _ _ ?_ ?_
    · rw [← Scheme.IdealSheafData.comap_comp, ← morphismRestrict_ι,
        Scheme.IdealSheafData.comap_comp]
      refine Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _ ?_ (r ∣_ U)
      rw [hK, AlgebraicGeometry.comap_mul, comap_eq_top_of_disjoint U.ι IW (fun y hy => by
        rw [hIW, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hy
        exact hy (hU y.2)), ← Scheme.IdealSheafData.one_eq_top, one_mul, comap_prod]
      simpa using Stacks.Divisors.isEffectiveCartierDivisor_prod Finset.univ
        (fun j => (I j).comap U.ι) (fun _ => 1) fun j _ => hUc j
    · rw [hIQ, comap_prod]
      simpa using Stacks.Divisors.isEffectiveCartierDivisor_prod Qset
        (fun Q => Q.idealSheaf.comap (r ⁻¹ᵁ U).ι) (fun _ => 1) fun Q _ =>
          Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _ (hQ Q) _

/-! ### The steps of the construction -/

/-- A point lies in the joint set `⋃_j V(I_j) ∪ ⋃_i Supp D_i` if and only if it lies in some
`V(I_j)` or in some prime divisor of some `D_i`. -/
private theorem mem_sup_iSup_iff {X : Scheme.{u}} [DecidableEq (MMP.Mori.PrimeDivisor X)]
    {ι κ : Type*} [Finite ι] [Fintype κ] (I : ι → X.IdealSheafData) {R : Type*} [Zero R]
    (D : κ → DivisorWithCoeffs R X) (x : X) :
    x ∈ (((⨆ j, (I j).support) ⊔ ⨆ i, (D i).supp : Closeds X) : Set X) ↔
      (∃ j, x ∈ ((I j).support : Set X)) ∨
        x ∈ ⋃ P ∈ Finset.univ.biUnion fun i => (D i).support, (P.support : Set X) := by
  rw [Closeds.coe_sup, Set.mem_union, mem_iSup_closeds, mem_iSup_closeds]
  refine or_congr Iff.rfl ?_
  simp only [DivisorWithCoeffs.coe_supp, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Set.mem_iUnion, exists_prop]
  exact ⟨fun ⟨i, E, hE, hx⟩ => ⟨E, ⟨i, hE⟩, hx⟩, fun ⟨E, ⟨i, hE⟩, hx⟩ => ⟨i, E, hE, hx⟩⟩

/-- The generic point of an integral scheme lies off the joint set of finitely many nonzero
ideals and divisors. -/
private theorem genericPoint_notMem_sup_iSup {X : Scheme.{u}} [IsIntegral X] {ι κ : Type*}
    [Finite ι] [Finite κ] {I : ι → X.IdealSheafData} (hI : ∀ j, I j ≠ ⊥) {R : Type*} [Zero R]
    (D : κ → DivisorWithCoeffs R X) :
    genericPoint X ∉ (((⨆ j, (I j).support) ⊔ ⨆ i, (D i).supp : Closeds X) : Set X) := by
  classical
  have := Fintype.ofFinite κ
  rw [mem_sup_iSup_iff]
  rintro (⟨j, hj⟩ | h)
  · exact genericPoint_notMem_support_of_ne_bot (hI j) hj
  · obtain ⟨P, -, hP⟩ := Set.mem_iUnion₂.1 h
    exact genericPoint_notMem_support_primeDivisor P hP

/-- **Steps 1 and 2.** A strong resolution `r : Z ⟶ X` and a nonzero ideal `J` on `Z` whose
support is `r⁻¹(X ∖ B) ∪ r⁻¹(T)`, for `B` the biregular locus of `r`, which has every `I_j 𝒪_Z`
as a factor and is invertible over every open `U ⊆ B` on which the `I_j` are invertible. -/
private theorem exists_strongResolution_idealSheafData {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : AlgebraicGeometry.IsVariety k sX)
    [IsIntegral X] {ι : Type*} [Fintype ι] (I : ι → X.IdealSheafData)
    (Pset : Finset (MMP.Mori.PrimeDivisor X)) (T : Closeds X)
    (hT : ∀ x, x ∈ (T : Set X) ↔
      (∃ j, x ∈ ((I j).support : Set X)) ∨ x ∈ ⋃ P ∈ Pset, (P.support : Set X))
    (hηT : genericPoint X ∉ (T : Set X))
    (hsm : ((smoothLocus sX : X.Opens) : Set X).Nonempty) :
    ∃ (Z : Scheme.{u}) (r : Z ⟶ X) (J : Z.IdealSheafData), AlgebraicGeometry.IsProjective r ∧
      AlgebraicGeometry.IsVariety k (r ≫ sX) ∧ IsSmoothScheme (r ≫ sX) ∧
      smoothLocus sX ≤ biregularLocus r ∧ J ≠ ⊥ ∧
      (∀ z, z ∈ (J.support : Set Z) ↔ r z ∉ biregularLocus r ∨ r z ∈ (T : Set X)) ∧
      (∀ j, ∃ J' : Z.IdealSheafData, J = (I j).comap r * J') ∧
      ∀ U : X.Opens, IsIso (r ∣_ U) → U ≤ biregularLocus r →
        (∀ j, Stacks.Divisors.IsEffectiveCartierDivisor ((I j).comap U.ι)) →
        Stacks.Divisors.IsEffectiveCartierDivisor (J.comap (r ⁻¹ᵁ U).ι) := by
  have := hX
  have := AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType sX
  obtain ⟨Z, r, hZv, hrproj, -, hZsm, hriso, -⟩ := exists_isStrongResolution sX hX
  have := hZv
  have : IsIntegral Z := hZv.toIsIntegral
  have := AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType (r ≫ sX)
  have : IsProper r := hrproj.isProper
  have : IsIso (r ∣_ biregularLocus r) := isBiregular_biregularLocus r
  have hsmB : smoothLocus sX ≤ biregularLocus r := le_biregularLocus hriso
  have hηB : genericPoint X ∈ biregularLocus r :=
    ((genericPoint_spec X).mem_open_set_iff (biregularLocus r).isOpen).2
      (by simpa using hsm.mono hsmB)
  have hrη : r (genericPoint Z) = genericPoint X := by
    obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Z, r z₀ = genericPoint X :=
      ⟨_, (apply_ι_inv_morphismRestrict r _
        (⟨genericPoint X, hηB⟩ : (biregularLocus r : Scheme.{u}))).trans rfl⟩
    have h1 : r (genericPoint Z) ⤳ genericPoint X :=
      hz₀ ▸ (genericPoint_specializes z₀).map r.continuous
    exact (h1.antisymm (genericPoint_specializes _)).eq
  obtain ⟨J, hJsupp', hJfac, hJcart⟩ := exists_idealSheafData_principalizing r (biregularLocus r)
    (fun Q => Aux.isEffectiveCartierDivisor_idealSheaf (r ≫ sX) hZsm Q) I Pset
  have hJsupp : ∀ z, z ∈ (J.support : Set Z) ↔ r z ∉ biregularLocus r ∨ r z ∈ (T : Set X) :=
    fun z => by rw [hJsupp', hT]
  refine ⟨Z, r, J, hrproj, hZv, hZsm, hsmB, fun hJ => hηT ?_, hJsupp, hJfac, hJcart⟩
  have : genericPoint Z ∈ (J.support : Set Z) := by
    rw [hJ, (Scheme.IdealSheafData.support_eq_top_iff).2 rfl]
    trivial
  rw [hJsupp, hrη] at this
  exact this.resolve_left (not_not.mpr hηB)

/-- **Step 3.** For a nonzero ideal `J` on a smooth variety `Z`, the blow-up of `J` followed by a
strong resolution is a projective morphism `h₁ : Z₁ ⟶ Z` from a smooth variety, which makes every
factor of `J` invertible, and is an isomorphism over the complement of `V(J)` and over every open
on which `J` is already invertible. -/
private theorem exists_principalization_of_isSmoothScheme {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {Z : Scheme.{u}} (t : Z ⟶ Spec (.of k)) (hZv : AlgebraicGeometry.IsVariety k t)
    (hZsm : IsSmoothScheme t) (J : Z.IdealSheafData) (hJ : J ≠ ⊥) :
    ∃ (Z₁ : Scheme.{u}) (h₁ : Z₁ ⟶ Z), AlgebraicGeometry.IsProjective h₁ ∧
      AlgebraicGeometry.IsVariety k (h₁ ≫ t) ∧ IsSmoothScheme (h₁ ≫ t) ∧
      (∀ K K' : Z.IdealSheafData, J = K * K' →
        Stacks.Divisors.IsEffectiveCartierDivisor (K.comap h₁)) ∧
      IsIso (h₁ ∣_ J.support.compl) ∧
      ∀ V : Z.Opens, Stacks.Divisors.IsEffectiveCartierDivisor (J.comap V.ι) → IsIso (h₁ ∣_ V) := by
  have := hZv
  have : IsIntegral Z := hZv.toIsIntegral
  have := AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType t
  obtain ⟨hBlv, hpproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational t J hJ
  have : IsIntegral (blowUp J) := hBlv.toIsIntegral
  obtain ⟨Z₁, s, hZ₁v, hsproj, -, hZ₁sm, hsiso, -⟩ :=
    exists_isStrongResolution (blowUpToBase J ≫ t) hBlv
  have : IsIntegral Z₁ := hZ₁v.toIsIntegral
  have hV : ∀ V : Z.Opens, IsIso (blowUpToBase J ∣_ V) → IsIso ((s ≫ blowUpToBase J) ∣_ V) := by
    intro V _
    have : IsIso (s ∣_ blowUpToBase J ⁻¹ᵁ V) := MMP.Mori.isBiregular_iff_le_biregularLocus.2
      ((preimage_le_smoothLocus_of_isIso_restrict t hZsm (blowUpToBase J) V).trans
        (le_biregularLocus hsiso))
    exact isIso_restrict_comp s (blowUpToBase J) V
  have : IsDominant s := by
    have : IsIso (s ∣_ smoothLocus (blowUpToBase J ≫ t)) := hsiso
    refine isDominant_of_isIso_restrict s (smoothLocus (blowUpToBase J ≫ t)) ?_
    rw [smoothLocus_eq_smoothLocus]
    exact (Scheme.Hom.dense_smoothLocus_of_perfectField _).nonempty
  refine ⟨Z₁, s ≫ blowUpToBase J, hsproj.comp hpproj, by rwa [Category.assoc],
    by rwa [Category.assoc], fun K K' hK => ?_, hV _ (isIso_blowUpToBase_restrict_compl_support J),
    fun V hV' => hV V (isIso_blowUpToBase_restrict_of_isEffectiveCartierDivisor J V hV')⟩
  rw [Scheme.IdealSheafData.comap_comp]
  exact isEffectiveCartierDivisor_comap_of_isDominant s _
    (Stacks.DenseOpenAdmissibleBlowup.isEffectiveCartierDivisor_comap_blowUpToBase_of_eq_mul hK)

/-- **Steps 1 to 3.** A projective morphism `h : Z₁ ⟶ X` from a smooth variety and an effective
Cartier divisor `J₁` on `Z₁` containing `Ex(h)` and `h⁻¹(T)`, such that every `I_j 𝒪_{Z₁}` is
invertible, and `h` is an isomorphism over every smooth open `U` on which the `I_j` are
invertible, with `V(J₁)` equal to `h⁻¹(T)` over `U`. -/
private theorem exists_partialPrincipalization {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : AlgebraicGeometry.IsVariety k sX)
    [IsIntegral X] {ι : Type*} [Fintype ι] (I : ι → X.IdealSheafData)
    (Pset : Finset (MMP.Mori.PrimeDivisor X)) (T : Closeds X)
    (hT : ∀ x, x ∈ (T : Set X) ↔
      (∃ j, x ∈ ((I j).support : Set X)) ∨ x ∈ ⋃ P ∈ Pset, (P.support : Set X))
    (hηT : genericPoint X ∉ (T : Set X))
    (hsm : ((smoothLocus sX : X.Opens) : Set X).Nonempty) :
    ∃ (Z₁ : Scheme.{u}) (h : Z₁ ⟶ X) (J₁ : Z₁.IdealSheafData), AlgebraicGeometry.IsProjective h ∧
      AlgebraicGeometry.IsVariety k (h ≫ sX) ∧ IsSmoothScheme (h ≫ sX) ∧
      Stacks.Divisors.IsEffectiveCartierDivisor J₁ ∧
      (∀ j, Stacks.Divisors.IsEffectiveCartierDivisor ((I j).comap h)) ∧
      (exceptionalSet h : Set Z₁) ⊆ J₁.support ∧
      (∀ z, h z ∈ (T : Set X) → z ∈ (J₁.support : Set Z₁)) ∧
      ∀ U : X.Opens, IsSmoothScheme (U.ι ≫ sX) →
        (∀ j, Stacks.Divisors.IsEffectiveCartierDivisor ((I j).comap U.ι)) →
        IsIso (h ∣_ U) ∧ ∀ z, h z ∈ U → (z ∈ (J₁.support : Set Z₁) ↔ h z ∈ (T : Set X)) := by
  obtain ⟨Z, r, J, hrproj, hZv, hZsm, hsmB, hJne, hJsupp, hJfac, hJcart⟩ :=
    exists_strongResolution_idealSheafData sX hX I Pset T hT hηT hsm
  obtain ⟨Z₁, h₁, hh₁proj, hZ₁v, hZ₁sm, hfac, hh₁J, hh₁V⟩ :=
    exists_principalization_of_isSmoothScheme (r ≫ sX) hZv hZsm J hJne
  have := hX
  have := AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType sX
  have := hZv
  have := AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType (r ≫ sX)
  have : IsProper r := hrproj.isProper
  have hUB : ∀ U : X.Opens, IsSmoothScheme (U.ι ≫ sX) → U ≤ biregularLocus r := fun U hU =>
    (le_smoothLocus_of_isSmoothScheme sX hU).trans hsmB
  refine ⟨Z₁, h₁ ≫ r, J.comap h₁, hh₁proj.comp hrproj, by rwa [Category.assoc],
    by rwa [Category.assoc], hfac J ⊤ (by rw [← Scheme.IdealSheafData.one_eq_top, mul_one]),
    fun j => ?_, fun y hy => ?_, fun z hz => ?_, fun U hUs hUc => ?_⟩
  · obtain ⟨J', hJ'⟩ := hJfac j
    rw [Scheme.IdealSheafData.comap_comp]
    exact hfac _ _ hJ'
  · rw [Scheme.IdealSheafData.support_comap]
    exact exceptionalSet_comp_subset r h₁ J.support.compl hh₁J
      (fun z hz => (hJsupp z).2 (Or.inl hz)) (fun _ => not_not.mp) hy
  · rw [Scheme.IdealSheafData.support_comap]
    exact (hJsupp _).2 (Or.inr hz)
  · have : IsIso (r ∣_ U) := MMP.Mori.isBiregular_iff_le_biregularLocus.2 (hUB U hUs)
    have : IsIso (h₁ ∣_ r ⁻¹ᵁ U) := hh₁V _ (hJcart U inferInstance (hUB U hUs) hUc)
    refine ⟨isIso_restrict_comp h₁ r U, fun z hz => ?_⟩
    rw [Scheme.IdealSheafData.support_comap]
    exact ⟨fun hz' => ((hJsupp _).1 hz').resolve_left (not_not.mpr (hUB U hUs hz)),
      fun hz' => (hJsupp _).2 (Or.inr hz')⟩

/-- **Step 4.** For an effective Cartier divisor `J` on a smooth variety `Z` there is a
resolution `f : Y ⟶ Z`, along which effective Cartier divisors pull back, with an snc divisor
containing `Ex(f) ∪ f⁻¹ V(J)`, and which is an isomorphism over every open on which `V(J)` is
snc. -/
private theorem exists_isResolutionOfVariety_isSNCSubset_support {k : Type u} [Field k]
    [CharZero k] {Z : Scheme.{u}} (t : Z ⟶ Spec (.of k)) (hZv : AlgebraicGeometry.IsVariety k t)
    (hZsm : IsSmoothScheme t) {J : Z.IdealSheafData}
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Z), IsResolutionOfVariety t f ∧
      (∀ K : Z.IdealSheafData, Stacks.Divisors.IsEffectiveCartierDivisor K →
        Stacks.Divisors.IsEffectiveCartierDivisor (K.comap f)) ∧
      (∃ S : Closeds Y, IsSNCSubset (f ≫ t) S ∧ (exceptionalSet f : Set Y) ⊆ S ∧
        f ⁻¹' (J.support : Set Z) ⊆ S) ∧
      ∀ V : Z.Opens, IsSNCClosedSubset (V.ι ≫ t) (V.ι ⁻¹' (J.support : Set Z)) →
        IsIso (f ∣_ V) := by
  have := hZv
  have : IsIntegral Z := hZv.toIsIntegral
  have := AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType t
  obtain ⟨D', hD'⟩ := exists_finset_primeDivisor_sup_eq t hJ
  have : Smooth t := Aux.smooth_of_isSmoothScheme' _ hZsm
  have : IsNormal Z := isNormal_of_smooth_over_field t
  obtain ⟨Y, f, hfres, -, hfsnc, hfiso⟩ :=
    exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset t ⟨hZv, inferInstance⟩ D'
  rw [hD'] at hfsnc hfiso
  have hfiso' : ∀ V : Z.Opens, IsSNCClosedSubset (V.ι ≫ t) (V.ι ⁻¹' (J.support : Set Z)) →
      IsIso (f ∣_ V) := fun V =>
    hfiso V (isSmoothScheme_of_le_smoothLocus _ (by rw [hZsm]; exact le_top))
  have := hfres.isVariety_source
  have : IsIntegral Y := hfres.isVariety_source.toIsIntegral
  have := AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType (f ≫ t)
  have : IsIso (f ∣_ J.support.compl) := by
    refine hfiso' _ ?_
    have : (Scheme.Opens.ι J.support.compl) ⁻¹' (J.support : Set Z) = ∅ :=
      Set.eq_empty_of_forall_notMem fun y hy => y.2 hy
    rw [this]
    exact ⟨isClosed_empty, Or.inl rfl⟩
  have : IsDominant f := isDominant_of_isIso_restrict f J.support.compl
    ⟨genericPoint Z, genericPoint_notMem_support_of_isEffectiveCartierDivisor hJ⟩
  exact ⟨Y, f, hfres, fun K hK => isEffectiveCartierDivisor_comap_of_isDominant f K hK,
    ⟨⟨_, (exceptionalSet f).isClosed.union (J.support.isClosed.preimage f.continuous)⟩,
      isSNCSubset_of_isSNCClosedSubset hfsnc, Set.subset_union_left, Set.subset_union_right⟩,
    hfiso'⟩

/-- **Isomorphism over the snc locus.** Let `h` be an isomorphism over `U` along which `V(J)`
agrees with `h⁻¹(T)` over `U`, and `f` an isomorphism over every open on which `V(J)` is snc. If
`T` is snc on `U`, then `f ≫ h` is an isomorphism over `U`. -/
private theorem isIso_restrict_comp_of_isSNCSubset {k : Type u} [Field k] [PerfectField k]
    {X Z Y : Scheme.{u}} [IsLocallyNoetherian X] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [QuasiCompact sX]
    (h : Z ⟶ X) (f : Y ⟶ Z) {J : Z.IdealSheafData} {T : Closeds X}
    (hf : ∀ V : Z.Opens, IsSNCClosedSubset (V.ι ≫ h ≫ sX) (V.ι ⁻¹' (J.support : Set Z)) →
      IsIso (f ∣_ V))
    (U : X.Opens) [IsIso (h ∣_ U)]
    (hJ : ∀ z, h z ∈ U → (z ∈ (J.support : Set Z) ↔ h z ∈ (T : Set X)))
    (hU : IsSNCSubset (U.ι ≫ sX) (T.preimage U.ι.continuous)) : IsIso ((f ≫ h) ∣_ U) := by
  have : QuasiCompact U.ι := instQuasiCompactOfIsLocallyNoetherianOfIsOpenImmersion
  have : IsIso (f ∣_ h ⁻¹ᵁ U) := by
    refine hf _ ?_
    have h1 : IsSNCClosedSubset (U.ι ≫ sX) (U.ι ⁻¹' (T : Set X)) :=
      isSNCClosedSubset_of_isSNCSubset hU
    have h2 := IsSNCClosedSubset.preimage_of_isIso (h ∣_ U) h1
    have e1 : (h ∣_ U) ≫ U.ι ≫ sX = (h ⁻¹ᵁ U).ι ≫ h ≫ sX := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    have e2 : (h ∣_ U) ⁻¹' (U.ι ⁻¹' (T : Set X)) = (h ⁻¹ᵁ U).ι ⁻¹' (J.support : Set Z) := by
      ext y
      rw [Set.mem_preimage, Set.mem_preimage, Set.mem_preimage, ι_morphismRestrict_apply]
      exact (hJ _ y.2).symm
    rwa [e1, e2] at h2
  exact isIso_restrict_comp f h U

end Proof_thm_mmp_strong_simultaneous_snc_principalization

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Resolution

open Proof_thm_mmp_strong_simultaneous_snc_principalization

/-- **Simultaneous principalization preserving the joint snc locus.** Let `X` be a variety over
an algebraically closed field `k` of characteristic zero, `D_i` finitely many divisors and `I_j`
finitely many nonzero ideal sheaves on `X`. There is a projective birational morphism
`g : Y ⟶ X` from a smooth variety such that every `I_j 𝒪_Y` is invertible, there is an snc
divisor `S` on `Y` containing `Ex(g)`, every `g⁻¹(Supp D_i)` and every `g⁻¹ V(I_j)`, and `g` is
an isomorphism over every open `U ⊆ X` which is smooth, on which every `I_j` is invertible and
on which `⋃_j V(I_j) ∪ ⋃_i Supp D_i` is an snc divisor. -/
@[mmp "thm_mmp_strong_simultaneous_snc_principalization"]
public theorem exists_isResolutionOfVariety_isSNCSubset_isIso_restrict {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : AlgebraicGeometry.IsVariety k sX) {R : Type*} [Zero R] {κ : Type*} [Finite κ]
    (D : κ → DivisorWithCoeffs R X) {ι : Type*} [Finite ι] (I : ι → X.IdealSheafData)
    (hI : ∀ j, I j ≠ ⊥) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), IsResolutionOfVariety sX g ∧
      (∀ j, Stacks.Divisors.IsEffectiveCartierDivisor ((I j).comap g)) ∧
      (∃ S : Closeds Y, IsSNCSubset (g ≫ sX) S ∧ exceptionalSet g ≤ S ∧
        (∀ i, (D i).supp.preimage g.continuous ≤ S) ∧
        ∀ j, (I j).support.preimage g.continuous ≤ S) ∧
      ∀ U : X.Opens, IsSmoothScheme (U.ι ≫ sX) →
        (∀ j, Stacks.Divisors.IsEffectiveCartierDivisor ((I j).comap U.ι)) →
        IsSNCSubset (U.ι ≫ sX)
          (((⨆ j, (I j).support) ⊔ ⨆ i, (D i).supp).preimage U.ι.continuous) →
        IsIso (g ∣_ U) := by
  classical
  have := hX
  have : IsIntegral X := hX.toIsIntegral
  have := AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType sX
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype κ := Fintype.ofFinite κ
  set T : Closeds X := (⨆ j, (I j).support) ⊔ ⨆ i, (D i).supp
  have hIT : ∀ j, (I j).support ≤ T := fun j =>
    (le_iSup (fun j => (I j).support) j).trans le_sup_left
  have hsm : ((smoothLocus sX : X.Opens) : Set X).Nonempty := by
    rw [smoothLocus_eq_smoothLocus]
    exact (Scheme.Hom.dense_smoothLocus_of_perfectField sX).nonempty
  have hηT : genericPoint X ∉ (T : Set X) := genericPoint_notMem_sup_iSup hI D
  obtain ⟨Z₁, h, J₁, hhproj, hZ₁v, hZ₁sm, hJ₁c, hIh, hExh, hJT, hU⟩ :=
    exists_partialPrincipalization sX hX I _ T (mem_sup_iSup_iff I D) hηT hsm
  obtain ⟨Y, f, hfres, hfK, ⟨S, hSsnc, hSex, hSJ⟩, hfiso⟩ :=
    exists_isResolutionOfVariety_isSNCSubset_support (h ≫ sX) hZ₁v hZ₁sm hJ₁c
  have hYv : AlgebraicGeometry.IsVariety k ((f ≫ h) ≫ sX) := by
    simpa only [Category.assoc] using hfres.isVariety_source
  have : IsIntegral Y := hYv.toIsIntegral
  have : IsProper h := hhproj.isProper
  have key : ∀ U : X.Opens, IsSmoothScheme (U.ι ≫ sX) →
      (∀ j, Stacks.Divisors.IsEffectiveCartierDivisor ((I j).comap U.ι)) →
      IsSNCSubset (U.ι ≫ sX) (T.preimage U.ι.continuous) → IsIso ((f ≫ h) ∣_ U) :=
    fun U hUs hUc => have := (hU U hUs hUc).1
      isIso_restrict_comp_of_isSNCSubset sX h f hfiso U (hU U hUs hUc).2
  set U₀ : X.Opens := smoothLocus sX ⊓ T.compl
  have hU₀ne : (U₀ : Set X).Nonempty :=
    ⟨genericPoint X, ((genericPoint_spec X).mem_open_set_iff (smoothLocus sX).isOpen).2
      (by simpa using hsm), hηT⟩
  have : IsIso ((f ≫ h) ∣_ U₀) := by
    refine key U₀ (isSmoothScheme_of_le_smoothLocus sX inf_le_left) (fun j => ?_) ?_
    · rw [comap_eq_top_of_disjoint U₀.ι (I j) fun y hy => y.2.2 (hIT j hy)]
      exact Stacks.Divisors.isEffectiveCartierDivisor_top
    · rw [show T.preimage U₀.ι.continuous = ⊥ from
        Closeds.ext (Set.eq_empty_of_forall_notMem fun y hy => y.2.2 hy)]
      exact IsSNCSubset.bot
  refine ⟨Y, f ≫ h, ⟨hX, hYv, hfres.isProjective.comp hhproj,
    isBirationalMorphism_of_isIso_restrict _ U₀ hU₀ne,
    by rw [Category.assoc]; exact hfres.isSmoothScheme⟩, fun j => ?_,
    ⟨S, by rw [Category.assoc]; exact hSsnc, fun y hy => ?_, fun i y hy => hSJ (hJT _
      ((show (D i).supp ≤ T from (le_iSup (fun i => (D i).supp) i).trans le_sup_right) hy)),
      fun j y hy => hSJ (hJT _ (hIT j hy))⟩, key⟩
  · rw [Scheme.IdealSheafData.comap_comp]
    exact hfK _ (hIh j)
  · rcases exceptionalSet_comp_subset h f _ (isBiregular_biregularLocus f)
      (B := ((biregularLocus f : Z₁.Opens) : Set Z₁)ᶜ ∪ J₁.support)
      (fun z hz => Or.inr (hExh hz)) Set.subset_union_left hy with h1 | h1
    · exact hSex h1
    · exact hSJ h1

end MMP.Resolution

end
