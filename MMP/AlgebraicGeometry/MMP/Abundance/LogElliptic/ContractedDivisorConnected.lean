module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization

/-!
# A divisor contracted by the Chow closure yields a trivially connected divisor

Let `(Z₀, Z̄, Ū)` be a Chow closure of the elliptic fibration `f_U : U ⟶ Z`
(`MMP.Flips.IsChowClosure`), with projections `g : Ū ⟶ Z̄` and `u : Ū ⟶ X`, and let `F` be a
prime divisor of `Ū` whose image `u(F)` has dimension at most one. Then `g(F)` is a curve `C_F`,
and some irreducible component `E₁` of `g⁻¹(C_F)` is mapped by `u` onto a prime divisor of `X`
which is `(K_X + Δ_X)`-trivially connected (`MMP.Flips.IsTriviallyConnected`): any two of its
points are joined by fibres of `g` over `C_F` and by a curve in `u(E₁ ∩ E₂)`, where `E₂` is a
component of `g⁻¹(C_F)` contracted by `u`.

## Main results

* `MMP.Flips.IsChowClosure.exists_isTriviallyConnected_of_dim_image_le_one`: if a prime divisor
  `F` of `Ū` has `dim u(F) ≤ 1`, then `X` has a `(K_X + Δ_X)`-trivially connected prime divisor.

## Implementation notes

The prime divisor `D` of `X` is the divisor `1 · D` (`Finsupp.single D 1`), as in
`MMP.Flips.not_dense_image_of_isTriviallyConnected`. A prime divisor of `Ū` is a
`MMP.Mori.PrimeDivisor` of the closed subscheme `Ū` of `Z̄ ×_k X`, and the dimension of `u(F)` is
the `topologicalKrullDim` of the image of its support.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], proof of 15.10
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Topology TopologicalSpace

universe u

namespace MMP.Flips

open MMP.Mori

/-- The reduced closed subscheme on a closed set `C` has the same topological Krull dimension as
`C`. -/
private theorem topologicalKrullDim_vanishingIdeal_subscheme {X : Scheme.{u}} (C : Closeds X) :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal C).subscheme =
      topologicalKrullDim C := by
  have hrange : Set.range (Scheme.IdealSheafData.vanishingIdeal C).subschemeι.base = C := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  let eH := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι.isClosedEmbedding.isEmbedding
    |>.toHomeomorph.trans (Homeomorph.setCongr hrange)
  exact IsHomeomorph.topologicalKrullDim_eq eH eH.isHomeomorph

section Dimension

variable (k : Type u) [Field k]

private theorem dim_closure_eq (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X) :
    topologicalKrullDim (closure ({x} : Set X)) =
      (natTrdegResidueField k X f x : WithBot ℕ∞) := by
  rw [topologicalKrullDim_closure_singleton_eq_trdeg k X f x]
  letI : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have : FinTrdeg k (X.residueField x) := residueField_finTrdeg k f x
  unfold natTrdegResidueField
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0 k (X.residueField x))
  rw [hn, Cardinal.toENat_nat, Cardinal.toNat_natCast]
  rfl

private theorem natTrdeg_add_trdeg {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] (φ : X ⟶ Y) (hφ : φ ≫ sY = sX) (x : X) :
    letI := (φ.residueFieldMap x).hom.toAlgebra
    natTrdegResidueField k X sX x = natTrdegResidueField k Y sY (φ x) +
      Cardinal.toNat (Algebra.trdeg (Y.residueField (φ x)) (X.residueField x)) := by
  subst hφ
  let A1 : Algebra k (Y.residueField (φ x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation (φ x)).hom.toAlgebra
  let A2 : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (φ ≫ sY).appTop ≫ X.Γevaluation x).hom.toAlgebra
  let A3 : Algebra (Y.residueField (φ x)) (X.residueField x) := (φ.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower k (Y.residueField (φ x)) (X.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ (φ ≫ sY).appTop ≫ X.Γevaluation x).hom a =
      (φ.residueFieldMap x).hom
        (((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation (φ x)).hom a)
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    exact (Scheme.Γevaluation_naturality_apply φ x _).symm
  have : FinTrdeg k (X.residueField x) := residueField_finTrdeg k (φ ≫ sY) x
  have : FinTrdeg k (Y.residueField (φ x)) := residueField_finTrdeg k sY (φ x)
  have : FaithfulSMul k (Y.residueField (φ x)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  have : FaithfulSMul (Y.residueField (φ x)) (X.residueField x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  have h := trdeg_add_eq k (Y.residueField (φ x)) (A := X.residueField x)
  unfold natTrdegResidueField
  rw [← h, Cardinal.toNat_add (trdeg_lt_aleph0 _ _) ?_]
  exact (le_add_self.trans_eq h).trans_lt (trdeg_lt_aleph0 _ _)

private theorem natTrdeg_eq_of_isIso {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] (φ : X ⟶ Y) (hφ : φ ≫ sY = sX) (x : X)
    [IsIso (φ.residueFieldMap x)] :
    natTrdegResidueField k X sX x = natTrdegResidueField k Y sY (φ x) := by
  rw [natTrdeg_add_trdeg k sX sY φ hφ x]
  letI := (φ.residueFieldMap x).hom.toAlgebra
  have hs : Function.Surjective (algebraMap (Y.residueField (φ x)) (X.residueField x)) :=
    (ConcreteCategory.bijective_of_isIso (φ.residueFieldMap x)).2
  have : Algebra.IsAlgebraic (Y.residueField (φ x)) (X.residueField x) :=
    ⟨fun a => (hs a).elim fun b hb => hb ▸ isAlgebraic_algebraMap b⟩
  rw [trdeg_eq_zero]
  simp

/-- Pins the instance search that `natTrdeg_snd_eq_of_mem` cannot do unaided. -/
private theorem isIso_residueFieldMap_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) : IsIso (f.residueFieldMap x) :=
  inferInstance

private theorem toENat_trdeg_eq (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    ((Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : ℕ∞) : WithBot ℕ∞) =
      (natTrdegResidueField k X f x : WithBot ℕ∞) := by
  rw [← dim_closure_eq k X f x, topologicalKrullDim_closure_singleton_eq_trdeg k X f x]

private theorem natTrdeg_add_coheight (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [IrreducibleSpace X] (x : X) :
    (natTrdegResidueField k X f x : WithBot ℕ∞) + (Order.coheight x : WithBot ℕ∞) =
      topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f x,
    topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X f x, ringKrullDim_stalk_eq_coheight,
    toENat_trdeg_eq]

private theorem natTrdeg_eq_dim_fiber_add {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ] (g : Y ⟶ Z)
    (hg : g ≫ sZ = sY) (y : Y) :
    (natTrdegResidueField k Y sY y : WithBot ℕ∞) =
      topologicalKrullDim (closure {(⟨y, rfl⟩ : g.base ⁻¹' {g.base y})}) +
        natTrdegResidueField k Z sZ (g y) := by
  set C : Closeds Y := Closeds.closure {y}
  set I := Scheme.IdealSheafData.vanishingIdeal C
  set ι := I.subschemeι
  have hrange : Set.range ι.base = (C : Set Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  let eH : I.subscheme ≃ₜ C :=
    ι.isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have hCi : IsIrreducible (C : Set Y) := isIrreducible_singleton.closure
  have : IrreducibleSpace C := Subtype.irreducibleSpace hCi
  have : IrreducibleSpace I.subscheme := eH.symm.surjective.irreducibleSpace eH.symm.continuous
  have hW : topologicalKrullDim I.subscheme = natTrdegResidueField k Y sY y := by
    rw [IsHomeomorph.topologicalKrullDim_eq eH eH.isHomeomorph]
    exact dim_closure_eq k Y sY y
  have hgen : ι (genericPoint I.subscheme) = y := by
    have h1 := (genericPoint_spec I.subscheme).image ι.continuous
    rw [Set.image_univ, hrange] at h1
    have h2 : closure ({ι (genericPoint I.subscheme)} : Set Y) = closure {y} := by
      rw [h1.def]
      exact closure_closure
    exact (inseparable_iff_closure_eq.mpr h2).eq
  set h := ι ≫ g
  have key := topologicalKrullDim_eq_fiber_add_closure_range h k (ι ≫ sY) sZ
    (by simp [h, hg])
  have hhξ : h (genericPoint I.subscheme) = g y := by
    simp only [h, Scheme.Hom.comp_apply, hgen]
  rw [hW, hhξ, closure_range_eq_closure_genericPoint, hhξ, dim_closure_eq k Z sZ] at key
  rw [key]
  congr 1
  -- the fibre of `h` over `g y` is the closure of `y` in the fibre of `g`
  rw [IsHomeomorph.topologicalKrullDim_eq _ (h.fiberHomeo (g y)).isHomeomorph]
  have hmem : ∀ a : h.base ⁻¹' {g y}, ι a.1 ∈ g.base ⁻¹' {g.base y} := fun a => by
    have := a.2
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at this ⊢
    exact this
  let ψ : h.base ⁻¹' {g y} → g.base ⁻¹' {g.base y} := fun a => ⟨ι a.1, hmem a⟩
  have hψ : IsEmbedding ψ :=
    (ι.isClosedEmbedding.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict _ hmem
  have hψr : Set.range ψ = closure {(⟨y, rfl⟩ : g.base ⁻¹' {g.base y})} := by
    ext p
    rw [closure_subtype, Set.image_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      have : ι a.1 ∈ Set.range ι.base := ⟨a.1, rfl⟩
      rwa [hrange] at this
    · intro hp
      obtain ⟨b, hb⟩ : p.1 ∈ Set.range ι.base := by rwa [hrange]
      have hb' : b ∈ h.base ⁻¹' {g y} := by
        simp only [Set.mem_preimage, Set.mem_singleton_iff, h, Scheme.Hom.comp_apply]
        rw [hb]
        exact p.2
      exact ⟨⟨b, hb'⟩, Subtype.ext hb⟩
  let e := hψ.toHomeomorph.trans (Homeomorph.setCongr hψr)
  exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph

/-- Pins the instance search, which times out on the composite morphisms below. -/
private theorem locallyQuasiFinite_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] :
    LocallyQuasiFinite f :=
  inferInstance

private theorem natTrdeg_le_of_specializes (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] {x x' : X} (hxx' : x ⤳ x') :
    natTrdegResidueField k X f x' ≤ natTrdegResidueField k X f x := by
  by_cases he : x = x'
  · rw [he]
  · exact (natTrdegResidueField_lt_of_specializes k X f hxx' he).le

private theorem isProperCurve_of_natTrdeg_eq_one {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [IsProper sX] {p : X}
    (hp : natTrdegResidueField k X sX p = 1) : IsProperCurve sX p := by
  refine isProperCurve_of_isProper sX ?_
  rw [topologicalKrullDim_vanishingIdeal_subscheme]
  change topologicalKrullDim (closure ({p} : Set X)) = 1
  rw [dim_closure_eq k X sX, hp]
  rfl

/-- A finite set of points of dimension one is the set of generic points of a finite set of
proper curves. -/
private theorem exists_finset_properCurve {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [IsProper sX] {P : Set X} (hP : P.Finite)
    (hP1 : ∀ p ∈ P, natTrdegResidueField k X sX p = 1) :
    ∃ S : Finset (ProperCurve sX), (∀ C ∈ S, C.point ∈ P) ∧
      curveUnion sX S = ⋃ p ∈ P, closure {p} := by
  have hfin : {C : ProperCurve sX | C.point ∈ P}.Finite :=
    Set.Finite.of_finite_image (hP.subset (Set.image_subset_iff.2 fun _ hC => hC))
      fun C _ D _ he => ProperCurve.ext he
  refine ⟨hfin.toFinset, fun C hC => by simpa using hC, ?_⟩
  ext x
  simp only [curveUnion, Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    exists_prop]
  exact ⟨fun ⟨C, hC, hx⟩ => ⟨C.point, hC, hx⟩,
    fun ⟨p, hp, hx⟩ => ⟨⟨p, isProperCurve_of_natTrdeg_eq_one k sX (hP1 p hp)⟩, hp, hx⟩⟩

end Dimension

section Arith

/-- If `a = d + b` in `WithBot ℕ∞` with `a b` natural, then `d` is natural too. -/
private theorem exists_natCast_of_eq_add {a b : ℕ} {d : WithBot ℕ∞}
    (h : (a : WithBot ℕ∞) = d + b) : ∃ n : ℕ, d = n ∧ a = n + b := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, top_add,
        WithBot.coe_inj] at h
      exact absurd h (ENat.coe_ne_top a)
    | coe n => exact ⟨n, rfl, by exact_mod_cast h⟩

private theorem le_add_one_of_eq_add {a b : ℕ} {d : WithBot ℕ∞} (h : (a : WithBot ℕ∞) = d + b)
    (hd : d ≤ 1) : a ≤ b + 1 := by
  obtain ⟨n, rfl, rfl⟩ := exists_natCast_of_eq_add h
  have : n ≤ 1 := by exact_mod_cast hd
  omega

private theorem add_one_le_of_eq_add {a b : ℕ} {d : WithBot ℕ∞} (h : (a : WithBot ℕ∞) = d + b)
    (hd : 1 ≤ d) : b + 1 ≤ a := by
  obtain ⟨n, rfl, rfl⟩ := exists_natCast_of_eq_add h
  have : 1 ≤ n := by exact_mod_cast hd
  omega

private theorem topologicalKrullDim_mono {α : Type*} [TopologicalSpace α] {s t : Set α}
    (hst : s ⊆ t) : topologicalKrullDim s ≤ topologicalKrullDim t :=
  (IsInducing.of_comp (continuous_inclusion hst) continuous_subtype_val
    IsInducing.subtypeVal).topologicalKrullDim_le

private theorem image_closure_singleton {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hc : Continuous f) (hf : IsClosedMap f) (x : α) :
    f '' closure {x} = closure {f x} := by
  rw [← hf.closure_image_eq_of_continuous hc, Set.image_singleton]

/-- A closed subset of a Noetherian sober space has finitely many "generic points" (those of its
irreducible components): every point of the subset specializes from one of them, and none of
them is a proper specialization of a point of the subset. -/
private theorem exists_finite_generic {α : Type*} [TopologicalSpace α] [NoetherianSpace α]
    [QuasiSober α] [T0Space α] {E : Set α} (hE : IsClosed E) :
    ∃ G : Set α, G.Finite ∧ G ⊆ E ∧ (∀ y ∈ E, ∃ e ∈ G, e ⤳ y) ∧
      ∀ e ∈ G, ∀ y ∈ E, y ⤳ e → y = e := by
  have : QuasiSober E := hE.isClosedEmbedding_subtypeVal.quasiSober
  refine ⟨Subtype.val '' genericPoints E,
    (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).image _,
    Set.image_subset_iff.2 fun e _ => e.2, ?_, ?_⟩
  · intro y hy
    obtain ⟨C, hC, hyC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      {(⟨y, hy⟩ : E)} isIrreducible_singleton
    let e := genericPoints.ofComponent ⟨C, hC⟩
    exact ⟨e.1.1, ⟨e.1, e.2, rfl⟩,
      ((genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩).specializes (hyC rfl)).map
        continuous_subtype_val⟩
  · rintro _ ⟨e, he, rfl⟩ y hy hye
    have hsp : (⟨y, hy⟩ : E) ⤳ e := IsInducing.subtypeVal.specializes_iff.mp hye
    have heq := he.2 isIrreducible_singleton.closure (specializes_iff_closure_subset.mp hsp)
    have : e ⤳ (⟨y, hy⟩ : E) := specializes_iff_mem_closure.mpr (heq (subset_closure rfl))
    exact congrArg Subtype.val (hsp.antisymm this).eq

/-- In a Jacobson space, the closure of a point with only finitely many closed specializations
is closed: the point is closed. -/
private theorem isClosed_singleton_of_finite {α : Type*} [TopologicalSpace α] [JacobsonSpace α]
    (x : α) (hfin : {z | z ∈ closure ({x} : Set α) ∧ IsClosed ({z} : Set α)}.Finite) :
    IsClosed ({x} : Set α) := by
  have hcl : IsClosed (closure ({x} : Set α) ∩ closedPoints α) := by
    have : closure ({x} : Set α) ∩ closedPoints α =
        ⋃ z ∈ {z | z ∈ closure ({x} : Set α) ∧ IsClosed ({z} : Set α)}, {z} := by
      ext z
      simp [mem_closedPoints_iff]
    rw [this]
    exact hfin.isClosed_biUnion fun z hz => hz.2
  have h1 := closure_inter_closedPoints (isClosed_closure (s := ({x} : Set α)))
  rw [hcl.closure_eq] at h1
  have hx : x ∈ closure ({x} : Set α) ∩ closedPoints α := by
    rw [h1]
    exact subset_closure rfl
  exact hx.2

private theorem coheight_eq_one_of_two_add {c : ℕ∞}
    (h : ((2 : ℕ) : WithBot ℕ∞) + (c : WithBot ℕ∞) = 3) : c = 1 := by
  induction c using ENat.recTopCoe with
  | top => exact absurd h (by decide)
  | coe n =>
    have : ((2 + n : ℕ) : WithBot ℕ∞) = ((3 : ℕ) : WithBot ℕ∞) := by
      push_cast
      exact h
    have : 2 + n = 3 := by exact_mod_cast this
    obtain rfl : n = 1 := by omega
    rfl

private theorem curveUnion_union {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [DecidableEq (ProperCurve sX)] (A B : Finset (ProperCurve sX)) :
    curveUnion sX (A ∪ B) = curveUnion sX A ∪ curveUnion sX B := by
  simp only [curveUnion, Finset.set_biUnion_union]

end Arith

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {U : X.Opens}
  {Z Zbar : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} {sZbar : Zbar ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [LocallyOfFiniteType sX] [QuasiCompact sX]

section ChowClosure

variable {K : Divisor X} {Δ : QDivisor X} {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens}
  {j : Z₀.toScheme ⟶ Zbar} {Ubar : (pullback sZbar sX).IdealSheafData}

set_option hygiene false in
/-- The projection `g : Ū ⟶ Z̄`. -/
local notation "gg" => (Ubar.subschemeι ≫ pullback.fst sZbar sX)

set_option hygiene false in
/-- The projection `u : Ū ⟶ X`. -/
local notation "uu" => (Ubar.subschemeι ≫ pullback.snd sZbar sX)

set_option hygiene false in
/-- `trdeg_k κ(y)` for `y ∈ Ū`. -/
local notation "NY" =>
  natTrdegResidueField k Ubar.subscheme (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX)

set_option hygiene false in
/-- `trdeg_k κ(x)` for `x ∈ X`. -/
local notation "NX" => natTrdegResidueField k X sX

set_option hygiene false in
/-- `trdeg_k κ(z)` for `z ∈ Z̄`. -/
local notation "NZ" => natTrdegResidueField k Zbar sZbar

private theorem fst_comp_eq : (Ubar.subschemeι ≫ pullback.fst sZbar sX) ≫ sZbar =
    Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX := by
  simp [pullback.condition]

/-- Points of `Ū` have dimension at most one more than their image in `Z̄`: the fibres of `g`
have pure dimension one. -/
private theorem natTrdeg_le_fst_add_one [LocallyOfFiniteType sZbar]
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) (y : Ubar.subscheme) :
    natTrdegResidueField k _ (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX) y ≤
      natTrdegResidueField k Zbar sZbar ((Ubar.subschemeι ≫ pullback.fst sZbar sX) y) + 1 := by
  have hFD := natTrdeg_eq_dim_fiber_add k _ sZbar (Ubar.subschemeι ≫ pullback.fst sZbar sX)
    fst_comp_eq y
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := (⟨y, rfl⟩ : (Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹'
      {(Ubar.subschemeι ≫ pullback.fst sZbar sX).base y}))).closure
  exact le_add_one_of_eq_add hFD
    ((topologicalKrullDim_mono hsub).trans (h.dim_fiber _ C hC).le)

/-- The generic point of a component of a fibre of `g` has dimension one more than its image. -/
private theorem natTrdeg_eq_fst_add_one [LocallyOfFiniteType sZbar]
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) (y : Ubar.subscheme)
    (hy : closure {(⟨y, rfl⟩ : (Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹'
      {(Ubar.subschemeι ≫ pullback.fst sZbar sX).base y})} ∈ irreducibleComponents _) :
    natTrdegResidueField k _ (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX) y =
      natTrdegResidueField k Zbar sZbar ((Ubar.subschemeι ≫ pullback.fst sZbar sX) y) + 1 := by
  have hFD := natTrdeg_eq_dim_fiber_add k _ sZbar (Ubar.subschemeι ≫ pullback.fst sZbar sX)
    fst_comp_eq y
  have h1 := h.dim_fiber _ _ hy
  exact le_antisymm (le_add_one_of_eq_add hFD h1.le) (add_one_le_of_eq_add hFD h1.ge)

/-- `u` does not raise dimensions. -/
private theorem natTrdeg_snd_le [LocallyOfFiniteType sZbar] (y : Ubar.subscheme) :
    natTrdegResidueField k X sX ((Ubar.subschemeι ≫ pullback.snd sZbar sX) y) ≤
      natTrdegResidueField k _ (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX) y := by
  rw [natTrdeg_add_trdeg k _ sX (Ubar.subschemeι ≫ pullback.snd sZbar sX) (by simp) y]
  exact Nat.le_add_right _ _

/-- On the open `g⁻¹(Z₀)`, where `u` is an open immersion, `u` preserves dimensions. -/
private theorem natTrdeg_snd_eq_of_mem [LocallyOfFiniteType sZbar]
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) (y : Ubar.subscheme)
    (hy : y ∈ (Ubar.subschemeι ≫ pullback.fst sZbar sX) ⁻¹ᵁ (haveI := h.isOpenImmersion;
      j.opensRange)) :
    natTrdegResidueField k X sX ((Ubar.subschemeι ≫ pullback.snd sZbar sX) y) =
      natTrdegResidueField k _ (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX) y := by
  have := h.isOpenImmersion
  have := h.isIntegral
  set W := (Ubar.subschemeι ≫ pullback.fst sZbar sX) ⁻¹ᵁ j.opensRange
  have : IsOpenImmersion (W.ι ≫ Ubar.subschemeι ≫ pullback.snd sZbar sX) :=
    h.isProjectiveMorphism_snd.2.2.2.1
  have : IsIso (W.ι.residueFieldMap ⟨y, hy⟩) := isIso_residueFieldMap_of_isOpenImmersion ..
  have : IsIso ((W.ι ≫ Ubar.subschemeι ≫ pullback.snd sZbar sX).residueFieldMap ⟨y, hy⟩) :=
    isIso_residueFieldMap_of_isOpenImmersion ..
  have h1 := natTrdeg_eq_of_isIso k (W.ι ≫ Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX)
    (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX) W.ι rfl (⟨y, hy⟩ : W)
  have h2 := natTrdeg_eq_of_isIso k (W.ι ≫ Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX) sX
    (W.ι ≫ Ubar.subschemeι ≫ pullback.snd sZbar sX) (by simp) (⟨y, hy⟩ : W)
  exact h2.symm.trans h1

private theorem dim_eq_natTrdeg_genericPoint (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [IrreducibleSpace X] :
    topologicalKrullDim X = natTrdegResidueField k X f (genericPoint X) := by
  rw [← dim_closure_eq k X f, (genericPoint_spec X).def]
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph).symm

/-- The generic point of `Ū` lies over `Z₀`. -/
private theorem genericPoint_mem (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) :
    haveI := h.isIntegral
    genericPoint Ubar.subscheme ∈
      (Ubar.subschemeι ≫ pullback.fst sZbar sX) ⁻¹ᵁ (haveI := h.isOpenImmersion; j.opensRange) := by
  have := h.isIntegral
  have := h.isOpenImmersion
  obtain ⟨-, -, -, -, hrange, hdense⟩ := h.isProjectiveMorphism_snd
  obtain ⟨x, hx⟩ := hdense.nonempty
  rw [← hrange] at hx
  obtain ⟨w, -⟩ := hx
  exact ((genericPoint_spec Ubar.subscheme).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr
    ⟨w.1, Set.mem_univ _, w.2⟩

/-- `Ū` is a threefold. -/
private theorem topologicalKrullDim_eq_three [LocallyOfFiniteType sZbar]
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) :
    haveI := h.isIntegral
    topologicalKrullDim Ubar.subscheme = 3 := by
  have := h.isIntegral
  have : Surjective (Ubar.subschemeι ≫ pullback.snd sZbar sX) := h.isProjectiveMorphism_snd.2.2.1
  have hu : (Ubar.subschemeι ≫ pullback.snd sZbar sX) (genericPoint Ubar.subscheme) =
      genericPoint X := map_genericPoint_of_isDominant _
  rw [dim_eq_natTrdeg_genericPoint (k := k) _ (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX),
    ← natTrdeg_snd_eq_of_mem h _ (genericPoint_mem h), hu,
    ← dim_eq_natTrdeg_genericPoint (k := k) X sX,
    h.satisfiesAbundanceAssumptions.dim_eq]

private theorem image_closure_snd (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar)
    (a : Ubar.subscheme) : (uu).base '' closure {a} = closure {uu a} := by
  have := isProper_of_isProjectiveMorphism _ h.isProjectiveMorphism_snd.1
  exact image_closure_singleton (Scheme.Hom.continuous _) (Scheme.Hom.isClosedMap _) a

/-- **Step 1.** The prime divisor `F` has dimension two, `u(F)` dimension at most one, and
`C_F = g(F)` is a curve. -/
private theorem natTrdeg_primeDivisor [LocallyOfFiniteType sZbar]
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) (F : Mori.PrimeDivisor Ubar.subscheme)
    (hF : topologicalKrullDim
      ((Ubar.subschemeι ≫ pullback.snd sZbar sX).base '' (F.support : Set Ubar.subscheme)) ≤ 1) :
    natTrdegResidueField k _ (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX) F.genericPoint = 2 ∧
      natTrdegResidueField k X sX
        ((Ubar.subschemeι ≫ pullback.snd sZbar sX) F.genericPoint) ≤ 1 ∧
      natTrdegResidueField k Zbar sZbar
        ((Ubar.subschemeι ≫ pullback.fst sZbar sX) F.genericPoint) = 1 := by
  have := h.isIntegral
  have := h.isOpenImmersion
  -- `dim F = 2`
  have h2 : natTrdegResidueField k _ (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX)
      F.genericPoint = 2 := by
    have := natTrdeg_add_coheight k _ (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX)
      F.genericPoint
    rw [topologicalKrullDim_eq_three h,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this
    have h3 : ((natTrdegResidueField k _ (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX)
        F.genericPoint + 1 : ℕ) : WithBot ℕ∞) = ((3 : ℕ) : WithBot ℕ∞) := by
      push_cast
      rw [← this]
      rfl
    have h4 : natTrdegResidueField k _ (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX)
        F.genericPoint + 1 = 3 := by exact_mod_cast h3
    omega
  -- `dim u(F) ≤ 1`
  have hu1 : natTrdegResidueField k X sX
      ((Ubar.subschemeι ≫ pullback.snd sZbar sX) F.genericPoint) ≤ 1 := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      image_closure_snd h,
      dim_closure_eq k X sX] at hF
    exact_mod_cast hF
  refine ⟨h2, hu1, le_antisymm ?_ ?_⟩
  · -- `g(ξ_F) ≠ g(ξ_Ū)`, a proper specialization of a point of dimension at most two
    have hne : (Ubar.subschemeι ≫ pullback.fst sZbar sX) (genericPoint Ubar.subscheme) ≠
        (Ubar.subschemeι ≫ pullback.fst sZbar sX) F.genericPoint := by
      intro he
      have hξW : F.genericPoint ∈ (Ubar.subschemeι ≫ pullback.fst sZbar sX) ⁻¹ᵁ j.opensRange := by
        have := genericPoint_mem h
        change (Ubar.subschemeι ≫ pullback.fst sZbar sX) (genericPoint Ubar.subscheme) ∈
          j.opensRange at this
        change (Ubar.subschemeι ≫ pullback.fst sZbar sX) F.genericPoint ∈ j.opensRange
        rwa [← he]
      have := natTrdeg_snd_eq_of_mem h F.genericPoint hξW
      omega
    have hlt := natTrdegResidueField_lt_of_specializes k Zbar sZbar
      ((genericPoint_spec Ubar.subscheme).specializes (Set.mem_univ F.genericPoint) |>.map
        (Scheme.Hom.continuous (Ubar.subschemeι ≫ pullback.fst sZbar sX))) hne
    have hle : natTrdegResidueField k Zbar sZbar
        ((Ubar.subschemeι ≫ pullback.fst sZbar sX) (genericPoint Ubar.subscheme)) + 1 ≤ 3 := by
      have hFD := natTrdeg_eq_dim_fiber_add k (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX)
        sZbar (Ubar.subschemeι ≫ pullback.fst sZbar sX) fst_comp_eq (genericPoint Ubar.subscheme)
      have h3 : natTrdegResidueField k _ (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX)
          (genericPoint Ubar.subscheme) = 3 := by
        have := topologicalKrullDim_eq_three h
        rw [dim_eq_natTrdeg_genericPoint (k := k) _
          (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX)] at this
        exact_mod_cast this
      rw [h3] at hFD
      refine add_one_le_of_eq_add hFD ?_
      obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
        (isIrreducible_singleton (x := (⟨genericPoint Ubar.subscheme, rfl⟩ :
          (Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹'
            {(Ubar.subschemeι ≫ pullback.fst sZbar sX).base (genericPoint Ubar.subscheme)})))
      rw [← h.dim_fiber _ C hC]
      refine topologicalKrullDim_mono fun p _ => ?_
      exact specializes_iff_mem_closure.mp (IsInducing.subtypeVal.specializes_iff.mp
        ((genericPoint_spec Ubar.subscheme).specializes (Set.mem_univ p.1)))
    omega
  · have := natTrdeg_le_fst_add_one h F.genericPoint
    omega

/-- Over a closed point `z̄`, the map `u` identifies no two distinct points of `g⁻¹(z̄)` one of
which specializes to the other. -/
private theorem eq_of_specializes_of_mem_fiber
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) {z : Zbar} (hz : IsClosed {z})
    {a b : Ubar.subscheme} (hab : a ⤳ b)
    (ha : (Ubar.subschemeι ≫ pullback.fst sZbar sX).base a = z)
    (hb : (Ubar.subschemeι ≫ pullback.fst sZbar sX).base b = z)
    (hu : (Ubar.subschemeι ≫ pullback.snd sZbar sX).base a =
      (Ubar.subschemeι ≫ pullback.snd sZbar sX).base b) : a = b := by
  have : LocallyOfFiniteType sZbar := h.isNormalVariety.1.toLocallyOfFiniteType
  have := isClosed_singleton_iff_isClosedImmersion.mp hz
  have : IsFinite (Zbar.fromSpecResidueField z ≫ sZbar) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have hpb : IsPullback ((pullback.fst sZbar sX).fiberι z ≫ pullback.snd sZbar sX)
      ((pullback.fst sZbar sX).fiberToSpecResidueField z) sX
      (Zbar.fromSpecResidueField z ≫ sZbar) :=
    (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback sZbar sX).flip
  have : IsFinite ((pullback.fst sZbar sX).fiberι z ≫ pullback.snd sZbar sX) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hpb.flip inferInstance
  set F := (pullback.fst sZbar sX).fiberι z ≫ pullback.snd sZbar sX
  have := locallyQuasiFinite_of_isFinite F
  set e := (pullback.fst sZbar sX).fiberHomeo z
  have hma : Ubar.subschemeι.base a ∈ (pullback.fst sZbar sX).base ⁻¹' {z} := ha
  have hmb : Ubar.subschemeι.base b ∈ (pullback.fst sZbar sX).base ⁻¹' {z} := hb
  set a' := e.symm ⟨_, hma⟩
  set b' := e.symm ⟨_, hmb⟩
  have hsub : (⟨_, hma⟩ : (pullback.fst sZbar sX).base ⁻¹' {z}) ⤳ ⟨_, hmb⟩ :=
    (Topology.IsInducing.subtypeVal.specializes_iff).mp (hab.map Ubar.subschemeι.continuous)
  have hab' : a' ⤳ b' := hsub.map e.symm.continuous
  have hfa : (pullback.fst sZbar sX).fiberι z a' = Ubar.subschemeι.base a :=
    Scheme.Hom.fiberι_fiberHomeo_symm _ _ _
  have hfb : (pullback.fst sZbar sX).fiberι z b' = Ubar.subschemeι.base b :=
    Scheme.Hom.fiberι_fiberHomeo_symm _ _ _
  have hF : F a' = F b' := by
    simp only [F, Scheme.Hom.comp_base, TopCat.comp_app] at hu ⊢
    rwa [hfa, hfb]
  have hab'' : a' = b' := eq_of_specializes_of_locallyQuasiFinite F hab' hF
  exact Ubar.subschemeι.isClosedEmbedding.injective (by rw [← hfa, ← hfb, hab''])

/-- Every point of a fibre of `g` over a closed point is a specialization of a point of that
fibre which has a proper specialization in the fibre (the fibre has pure dimension one). -/
private theorem exists_specializes_of_isClosed
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) {z : Zbar} (hz : IsClosed {z})
    {y : Ubar.subscheme} (hy : (Ubar.subschemeι ≫ pullback.fst sZbar sX) y = z) :
    ∃ y' b : Ubar.subscheme, (Ubar.subschemeι ≫ pullback.fst sZbar sX) y' = z ∧
      (Ubar.subschemeι ≫ pullback.fst sZbar sX) b = z ∧ y' ⤳ y ∧ y' ⤳ b ∧ b ≠ y' := by
  have hPc : IsClosed ((Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹' {z}) :=
    hz.preimage (Scheme.Hom.continuous _)
  have : QuasiSober ((Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹' {z}) :=
    hPc.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨C, hC, hyC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    {(⟨y, hy⟩ : (Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹' {z})} isIrreducible_singleton
  obtain ⟨q, hq⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
  have hdim := h.dim_fiber z C hC
  have hb : ∃ b ∈ C, b ≠ q := by
    by_contra hcon
    push Not at hcon
    have : Nonempty C := ⟨⟨q, hq.mem⟩⟩
    have : Subsingleton C := ⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩
    rw [topologicalKrullDim_eq_zero_of_subsingleton] at hdim
    exact absurd hdim (by decide)
  obtain ⟨b, hbC, hbq⟩ := hb
  exact ⟨q.1, b.1, q.2, b.2, (hq.specializes (hyC rfl)).map continuous_subtype_val,
    (hq.specializes hbC).map continuous_subtype_val, fun he => hbq (Subtype.ext he)⟩

/-- Every point of a fibre of `g` over a closed point is a specialization of a point of that
fibre whose image under `u` is not closed. -/
private theorem exists_specializes_one_le_natTrdeg [LocallyOfFiniteType sZbar]
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) {z : Zbar} (hz : IsClosed {z})
    {y : Ubar.subscheme} (hy : (Ubar.subschemeι ≫ pullback.fst sZbar sX) y = z) :
    ∃ y' : Ubar.subscheme, (Ubar.subschemeι ≫ pullback.fst sZbar sX) y' = z ∧ y' ⤳ y ∧
      1 ≤ natTrdegResidueField k X sX ((Ubar.subschemeι ≫ pullback.snd sZbar sX) y') := by
  obtain ⟨y', b, hy', hb, hy'y, hy'b, hne⟩ := exists_specializes_of_isClosed h hz hy
  refine ⟨y', hy', hy'y, ?_⟩
  have hne' : (Ubar.subschemeι ≫ pullback.snd sZbar sX) y' ≠
      (Ubar.subschemeι ≫ pullback.snd sZbar sX) b := fun he =>
    hne (eq_of_specializes_of_mem_fiber h hz hy'b hy' hb he).symm
  have := natTrdegResidueField_lt_of_specializes k X sX
    (hy'b.map (Scheme.Hom.continuous (Ubar.subschemeι ≫ pullback.snd sZbar sX))) hne'
  omega

private theorem noetherianSpace_subscheme [LocallyOfFiniteType sZbar]
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) : NoetherianSpace Ubar.subscheme := by
  have := isProper_of_isProjectiveMorphism _ h.isProjectiveMorphism_snd.1
  have : CompactSpace Ubar.subscheme := QuasiCompact.compactSpace_of_compactSpace uu
  have : IsLocallyNoetherian Ubar.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX)
  have : IsNoetherian Ubar.subscheme := {}
  infer_instance

/-- **Step 3, the components with `dim u = 2`.** If every component of `g⁻¹(C_F)` dominating
`C_F` had `dim u ≤ 1`, then over all but finitely many closed points of `C_F` the images
`u(g⁻¹(z̄))` would lie in one proper curve, contradicting (iv). -/
private theorem not_forall_natTrdeg_snd_le_one [LocallyOfFiniteType sZbar] [IsProper sX]
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) {ζ : Zbar} (hζ : NZ ζ = 1)
    {G : Set Ubar.subscheme} (hGfin : G.Finite) (hGE : G ⊆ (gg).base ⁻¹' closure {ζ})
    (hG1 : ∀ y ∈ (gg).base ⁻¹' closure {ζ}, ∃ e ∈ G, e ⤳ y)
    (hA : ∀ e ∈ G, gg e = ζ → NX (uu e) ≤ 1) : False := by
  have := LocallyOfFiniteType.jacobsonSpace sZbar
  set bad := (gg).base '' {e ∈ G | gg e ≠ ζ}
  have hbad : bad.Finite := (hGfin.subset fun e he => he.1).image _
  have hPfin : ((uu).base '' {e ∈ G | gg e = ζ ∧ NX (uu e) = 1}).Finite :=
    (hGfin.subset fun e he => he.1).image _
  obtain ⟨S, -, hSu⟩ := exists_finset_properCurve k sX hPfin
    (Set.forall_mem_image.2 fun _ he => he.2.2)
  have hcover : ∀ z, IsClosed {z} → z ∈ closure {ζ} → z ∉ bad →
      (uu).base '' ((gg).base ⁻¹' {z}) ⊆ curveUnion sX S := by
    rintro z hz hzC hzb _ ⟨y, hy, rfl⟩
    obtain ⟨y', hy', hy'y, hN⟩ := exists_specializes_one_le_natTrdeg h hz hy
    have hy'E : y' ∈ (gg).base ⁻¹' closure {ζ} := by
      change gg y' ∈ closure {ζ}; rwa [hy']
    obtain ⟨e, heG, hey'⟩ := hG1 y' hy'E
    have hge : gg e = ζ := by
      by_contra hne
      have hlt := natTrdegResidueField_lt_of_specializes k Zbar sZbar
        (specializes_iff_mem_closure.mpr (hGE heG)) (Ne.symm hne)
      have hcl : IsClosed {gg e} :=
        isClosed_singleton_of_natTrdegResidueField_eq_zero k Zbar sZbar _ (by omega)
      have hsp : gg e ⤳ z := hy' ▸ hey'.map (Scheme.Hom.continuous _)
      have : z ∈ ({gg e} : Set Zbar) := hsp.mem_closed hcl rfl
      exact hzb ⟨e, ⟨heG, hne⟩, this.symm⟩
    have hle := natTrdeg_le_of_specializes k X sX (hey'.map (Scheme.Hom.continuous uu))
    have h1 : NX (uu e) = 1 := by have := hA e heG hge; omega
    rw [hSu]
    exact Set.mem_biUnion ⟨e, ⟨heG, hge, h1⟩, rfl⟩
      (specializes_iff_mem_closure.mp ((hey'.trans hy'y).map (Scheme.Hom.continuous uu)))
  set Q := {z | z ∈ closure ({ζ} : Set Zbar) ∧ IsClosed ({z} : Set Zbar)}
  have hinf : ¬ Q.Finite := fun hfin => by
    have := natTrdegResidueField_eq_zero_of_isClosed k Zbar sZbar ζ
      (isClosed_singleton_of_finite ζ hfin)
    omega
  obtain ⟨z, ⟨hzC, hz⟩, hzb⟩ : (Q \ bad).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hne
    exact hinf (hbad.subset hne)
  obtain ⟨y, hy⟩ := (h.isConnected_fiber z).nonempty
  have hSne : S.Nonempty := by
    obtain ⟨C, hC, -⟩ := Set.mem_iUnion₂.mp (hcover z hz hzC hzb ⟨y, hy, rfl⟩)
    exact ⟨C, hC⟩
  refine hinf (((h.finite S hSne).union hbad).subset fun z hz => ?_)
  by_cases hzb : z ∈ bad
  · exact Or.inr hzb
  · exact Or.inl ⟨hz.2, hcover z hz.2 hz.1 hzb⟩

/-- **Step 3.** There are points `e_a`, `e_b` of `Ū` over the generic point of `C_F` (generic
points of components `E₁ = {e_a}⁻`, `E₂ = {e_b}⁻` of `g⁻¹(C_F)`), with `dim u(E₁) = 2`,
`dim E₂ = 2` and `dim u(E₂) ≤ 1`, both specializing to a point `m` over the generic point of
`C_F`. -/
private theorem exists_components [LocallyOfFiniteType sZbar] [IsProper sX]
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) (F : Mori.PrimeDivisor Ubar.subscheme)
    (hF : topologicalKrullDim ((uu).base '' (F.support : Set Ubar.subscheme)) ≤ 1) :
    ∃ ea eb m : Ubar.subscheme, ea ⤳ m ∧ eb ⤳ m ∧ gg ea = gg m ∧ gg eb = gg m ∧
      NX (uu ea) = 2 ∧ NY eb = 2 ∧ NZ (gg m) = 1 ∧ NX (uu eb) ≤ 1 := by
  have := h.isIntegral
  have := noetherianSpace_subscheme h
  obtain ⟨hF2, hFu, hζ⟩ := natTrdeg_primeDivisor h F hF
  obtain ⟨ζ, hζdef⟩ : ∃ ζ, gg F.genericPoint = ζ := ⟨_, rfl⟩
  rw [hζdef] at hζ
  have hEc : IsClosed ((gg).base ⁻¹' closure {ζ}) :=
    isClosed_closure.preimage (Scheme.Hom.continuous _)
  obtain ⟨G, hGfin, hGE, hG1, hG2⟩ := exists_finite_generic hEc
  -- the points of `G` specializing to a point over `ζ` lie over `ζ`
  have hdom : ∀ e ∈ G, ∀ y, e ⤳ y → gg y = ζ → gg e = ζ := by
    intro e he y hey hy
    have h1 : gg e ⤳ ζ := hy ▸ hey.map (Scheme.Hom.continuous _)
    have h2 : ζ ⤳ gg e := specializes_iff_mem_closure.mpr (hGE he)
    exact (h1.antisymm h2).eq
  -- the points of `G` over `ζ` are generic points of components of the fibre: dimension two
  have hN2 : ∀ e ∈ G, gg e = ζ → NY e = 2 := by
    intro e he hge
    have hcomp : closure {(⟨e, rfl⟩ : (gg).base ⁻¹' {(gg).base e})} ∈
        irreducibleComponents ((gg).base ⁻¹' {(gg).base e}) := by
      refine ⟨isIrreducible_singleton.closure, fun T hT hsub => ?_⟩
      obtain ⟨y₀, hy₀⟩ := QuasiSober.sober
        (hT.image Subtype.val continuous_subtype_val.continuousOn).closure isClosed_closure
      have hTE : closure (Subtype.val '' T) ⊆ (gg).base ⁻¹' closure {ζ} := by
        refine closure_minimal ?_ hEc
        rintro _ ⟨t, -, rfl⟩
        have ht := t.2
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at ht
        change gg t.1 ∈ closure {ζ}
        rw [ht, hge]
        exact subset_closure rfl
      have hey₀ : y₀ ⤳ e :=
        hy₀.specializes (subset_closure ⟨⟨e, rfl⟩, hsub (subset_closure rfl), rfl⟩)
      have hy₀e := hG2 e he y₀ (hTE hy₀.mem) hey₀
      intro t ht
      rw [closure_subtype, Set.image_singleton]
      have : t.1 ∈ closure {y₀} := by rw [hy₀.def]; exact subset_closure ⟨t, ht, rfl⟩
      rwa [hy₀e] at this
    have := natTrdeg_eq_fst_add_one h e hcomp
    rwa [hge, hζ] at this
  -- the generic point of `F` is one of them, with `dim u ≤ 1`
  have hξE : F.genericPoint ∈ (gg).base ⁻¹' closure {ζ} := by
    change gg F.genericPoint ∈ closure {ζ}; rw [hζdef]; exact subset_closure rfl
  obtain ⟨eF, heFG, heF⟩ := hG1 _ hξE
  have heFζ := hdom eF heFG _ heF hζdef
  have heFeq : eF = F.genericPoint := by
    by_contra hne
    have := natTrdegResidueField_lt_of_specializes k _
      (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX) heF hne
    have := hN2 eF heFG heFζ
    omega
  rw [heFeq] at heFG
  -- some component has `dim u = 2`
  have hA : ∃ ea ∈ G, gg ea = ζ ∧ NX (uu ea) = 2 := by
    by_contra hA
    push Not at hA
    refine not_forall_natTrdeg_snd_le_one h hζ hGfin hGE hG1 fun e he hge => ?_
    have := natTrdeg_snd_le (k := k) (sX := sX) e
    have := hN2 e he hge
    have := hA e he hge
    omega
  obtain ⟨ea0, hea0G, hea0ζ, hea02⟩ := hA
  -- the generic fibre is connected
  have htA : IsClosed (⋃ e ∈ {e ∈ G | gg e = ζ ∧ NX (uu e) = 2}, closure {e}) :=
    (hGfin.subset fun e he => he.1).isClosed_biUnion fun _ _ => isClosed_closure
  have htB : IsClosed (⋃ e ∈ {e ∈ G | gg e = ζ ∧ NX (uu e) ≤ 1}, closure {e}) :=
    (hGfin.subset fun e he => he.1).isClosed_biUnion fun _ _ => isClosed_closure
  have hcov : (gg).base ⁻¹' {ζ} ⊆ (⋃ e ∈ {e ∈ G | gg e = ζ ∧ NX (uu e) = 2}, closure {e}) ∪
      (⋃ e ∈ {e ∈ G | gg e = ζ ∧ NX (uu e) ≤ 1}, closure {e}) := by
    intro p hp
    have hp' : gg p = ζ := hp
    have hpE : p ∈ (gg).base ⁻¹' closure {ζ} := by
      change gg p ∈ closure {ζ}; rw [hp']; exact subset_closure rfl
    obtain ⟨e, heG, hep⟩ := hG1 p hpE
    have hge := hdom e heG p hep hp'
    have h2 := hN2 e heG hge
    have hle := natTrdeg_snd_le (k := k) (sX := sX) e
    by_cases hc : NX (uu e) = 2
    · exact Or.inl (Set.mem_biUnion ⟨heG, hge, hc⟩ (specializes_iff_mem_closure.mp hep))
    · exact Or.inr (Set.mem_biUnion ⟨heG, hge, by omega⟩ (specializes_iff_mem_closure.mp hep))
  have hneA : ((gg).base ⁻¹' {ζ} ∩
      ⋃ e ∈ {e ∈ G | gg e = ζ ∧ NX (uu e) = 2}, closure {e}).Nonempty :=
    ⟨ea0, hea0ζ, Set.mem_biUnion ⟨hea0G, hea0ζ, hea02⟩ (subset_closure rfl)⟩
  have hneB : ((gg).base ⁻¹' {ζ} ∩
      ⋃ e ∈ {e ∈ G | gg e = ζ ∧ NX (uu e) ≤ 1}, closure {e}).Nonempty :=
    ⟨F.genericPoint, hζdef, Set.mem_biUnion ⟨heFG, hζdef, hFu⟩ (subset_closure rfl)⟩
  obtain ⟨m, hm, hmA, hmB⟩ := isPreconnected_closed_iff.mp
    (h.isConnected_fiber ζ).isPreconnected _ _ htA htB hcov hneA hneB
  obtain ⟨ea, ⟨heaG, heaζ, hea2⟩, hmea⟩ := Set.mem_iUnion₂.mp hmA
  obtain ⟨eb, ⟨hebG, hebζ, heb1⟩, hmeb⟩ := Set.mem_iUnion₂.mp hmB
  have hm' : gg m = ζ := hm
  exact ⟨ea, eb, m, specializes_iff_mem_closure.mpr hmea, specializes_iff_mem_closure.mpr hmeb,
    heaζ.trans hm'.symm, hebζ.trans hm'.symm, hea2, hN2 eb hebG hebζ, by rwa [hm'],
    heb1⟩

/-- **Step 4, Stein factorization.** Let `E₁ = {e_a}⁻` and `m ∈ E₁` with `g(m) = g(e_a)`. Every
closed point of `E₁` lies in a closed connected subset of `E₁`, inside a fibre of `g` over a closed
point, which meets `{m}⁻`: a fibre of the Stein factorization `E₁ ⟶ C' ⟶ Z̄` of `g|_{E₁}`, all of
whose fibres meet `{m}⁻` since `{m}⁻` dominates `C'`. -/
private theorem exists_isConnected_fiber [LocallyOfFiniteType sZbar] [IsProper sX]
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) {ea m : Ubar.subscheme} (hm : ea ⤳ m)
    (hgm : gg ea = gg m) {y : Ubar.subscheme} (hy : y ∈ closure {ea}) (hyc : IsClosed {y}) :
    ∃ Φ : Set Ubar.subscheme, IsClosed Φ ∧ _root_.IsConnected Φ ∧ y ∈ Φ ∧ Φ ⊆ closure {ea} ∧
      (∃ z : Zbar, IsClosed {z} ∧ Φ ⊆ (gg).base ⁻¹' {z}) ∧ (Φ ∩ closure {m}).Nonempty := by
  have := isProper_of_isProjectiveMorphism _ h.isProjectiveMorphism_snd.1
  have := Stacks.Chow.isIntegral_integralComponentAt ea
  set I := Stacks.Chow.integralComponentAt ea
  set ι := I.subschemeι
  have hrange : Set.range ι.base = closure {ea} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Stacks.Chow.coe_support_integralComponentAt]
  have hP1 : IsProper (ι ≫ (Ubar.subschemeι ≫ pullback.snd sZbar sX) ≫ sX) := inferInstance
  have hassoc : ι ≫ (Ubar.subschemeι ≫ pullback.snd sZbar sX) ≫ sX =
      ι ≫ Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX := by simp
  rw [hassoc] at hP1
  have : AlgebraicGeometry.IsVariety k (ι ≫ Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX) :=
    ⟨⟩
  have : IsProper (ι ≫ gg) := inferInstance
  have hf : (ι ≫ gg) ≫ sZbar = ι ≫ Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX := by
    rw [Category.assoc, fst_comp_eq]
  obtain ⟨Y', f', κ, ⟨hS⟩, hP, hsurj, -, hconn, hfin, -⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety _ sZbar (ι ≫ gg) hf
  have hcomp : f' ≫ κ = ι ≫ gg := hS.comp
  have hκ : ∀ v, κ (f' v) = gg (ι v) := fun v => by
    rw [← Scheme.Hom.comp_apply, hcomp, Scheme.Hom.comp_apply]
  have := locallyQuasiFinite_of_isFinite κ
  -- the generic point of `E₁`
  have hgen : ι (genericPoint I.subscheme) = ea := by
    have h1 := (genericPoint_spec I.subscheme).image ι.continuous
    rw [Set.image_univ, hrange, closure_closure] at h1
    exact (inseparable_iff_closure_eq.mpr h1.def).eq
  -- every fibre of `E₁ ⟶ C'` meets `{m}⁻`
  obtain ⟨m₁, hm₁⟩ : m ∈ Set.range ι.base := by
    rw [hrange]; exact specializes_iff_mem_closure.mp hm
  have hξm : f' (genericPoint I.subscheme) = f' m₁ := by
    refine MMP.Flips.eq_of_specializes_of_locallyQuasiFinite κ
      (((genericPoint_spec I.subscheme).specializes (Set.mem_univ m₁)).map f'.continuous) ?_
    rw [hκ, hκ, hgen]
    change gg ea = gg (ι.base m₁)
    rw [hm₁, hgm]
  have hΘ : ∀ c : Y', ∃ θ, ι θ ∈ closure {m} ∧ f' θ = c := by
    intro c
    obtain ⟨w, rfl⟩ := hsurj.surj c
    have hcl : IsClosed (f'.base '' (ι.base ⁻¹' closure {m})) :=
      f'.isClosedMap _ (isClosed_closure.preimage ι.continuous)
    have hmem : f' (genericPoint I.subscheme) ∈ f'.base '' (ι.base ⁻¹' closure {m}) :=
      ⟨m₁, by
        show ι.base m₁ ∈ closure ({m} : Set Ubar.subscheme)
        rw [hm₁]; exact subset_closure rfl, hξm.symm⟩
    exact (((genericPoint_spec I.subscheme).specializes
      (Set.mem_univ w)).map f'.continuous).mem_closed hcl hmem
  -- the fibre through `y`
  obtain ⟨w, rfl⟩ : y ∈ Set.range ι.base := by rwa [hrange]
  have hwc : IsClosed {w} := by
    have : ι.base ⁻¹' {ι.base w} = {w} := by
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ι.isClosedEmbedding.injective.eq_iff
    rw [← this]
    exact hyc.preimage ι.continuous
  have hcc : IsClosed {f' w} := by
    simpa only [Set.image_singleton] using f'.isClosedMap _ hwc
  have hzc : IsClosed {κ (f' w)} := by
    simpa only [Set.image_singleton] using κ.isClosedMap _ hcc
  obtain ⟨θ, hθm, hθ⟩ := hΘ (f' w)
  refine ⟨ι.base '' (f'.base ⁻¹' {f' w}), ι.isClosedMap _ (hcc.preimage f'.continuous),
    (hconn _).image _ ι.continuous.continuousOn, ⟨w, rfl, rfl⟩, ?_,
    ⟨κ (f' w), hzc, ?_⟩, ⟨ι θ, ⟨θ, hθ, rfl⟩, hθm⟩⟩
  · rintro _ ⟨v, -, rfl⟩; rw [← hrange]; exact ⟨v, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    change gg (ι v) = κ (f' w)
    rw [← hκ]; exact congrArg κ hv

/-- **Step 4, the curves through a closed point.** Let `S = u({e_a}⁻)`, `m` and `Θ = {m}⁻` as in
`exists_isConnected_fiber`. A closed point `x ∈ S` lies on `u(Θ)`, or on a connected union of
`(K_X + Δ_X)`-trivial proper curves in `S` meeting `u(Θ)`: the image under `u` of a connected
fibre through a closed point over `x`, a curve in some `u(g⁻¹(z̄))` (FA 15.10 (iii)). -/
private theorem exists_curves_of_isClosed [LocallyOfFiniteType sZbar] [IsProper sX]
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) {ea m : Ubar.subscheme} (hm : ea ⤳ m)
    (hgm : gg ea = gg m) {x : X} (hx : x ∈ closure {uu ea}) (hxc : IsClosed {x}) :
    x ∈ closure {uu m} ∨ ∃ S : Finset (ProperCurve sX), _root_.IsConnected (curveUnion sX S) ∧
      curveUnion sX S ⊆ closure {uu ea} ∧ x ∈ curveUnion sX S ∧
      (curveUnion sX S ∩ closure {uu m}).Nonempty ∧
      ∀ C ∈ S, (Divisor.toQDivisor K + Δ).intersectionNumber k sX C.ι C.dim_le
        h.satisfiesAbundanceAssumptions.isQCartier = 0 := by
  have := noetherianSpace_subscheme h
  have := isProper_of_isProjectiveMorphism _ h.isProjectiveMorphism_snd.1
  have : CompactSpace Ubar.subscheme := QuasiCompact.compactSpace_of_compactSpace uu
  -- a closed point of `E₁` over `x`
  rw [← image_closure_snd h] at hx
  obtain ⟨y₀, hy₀, hy₀x⟩ := hx
  obtain ⟨y, ⟨hyE, hyx⟩, hyc⟩ := (isClosed_closure.inter
    (hxc.preimage (Scheme.Hom.continuous uu))).exists_closed_singleton ⟨y₀, hy₀, hy₀x⟩
  have hyx' : uu y = x := hyx
  obtain ⟨Φ, hΦc, hΦconn, hyΦ, hΦE, ⟨z, hz, hΦz⟩, ⟨θ, hθΦ, hθm⟩⟩ :=
    exists_isConnected_fiber h hm hgm hyE hyc
  obtain ⟨G, hGfin, hGΦ, hG1, hG2⟩ := exists_finite_generic hΦc
  by_cases htriv : ∃ q ∈ G, ∀ b ∈ Φ, q ⤳ b → b = q
  · -- `Φ` is a point
    left
    obtain ⟨q, hqG, hq⟩ := htriv
    have hqc : IsClosed {q} := by
      have : closure {q} = {q} := subset_antisymm (fun b hb => hq b
        (closure_minimal (Set.singleton_subset_iff.mpr (hGΦ hqG)) hΦc hb)
        (specializes_iff_mem_closure.mpr hb)) subset_closure
      rw [← this]; exact isClosed_closure
    have hK : IsClosed (⋃ q' ∈ G \ {q}, closure {q'}) :=
      (hGfin.diff).isClosed_biUnion fun _ _ => isClosed_closure
    have hcov : Φ ⊆ {q} ∪ ⋃ q' ∈ G \ {q}, closure {q'} := by
      intro v hv
      obtain ⟨q', hq'G, hq'v⟩ := hG1 v hv
      by_cases hq' : q' = q
      · subst hq'; exact Or.inl (hq v hv hq'v)
      · exact Or.inr (Set.mem_biUnion ⟨hq'G, hq'⟩ (specializes_iff_mem_closure.mp hq'v))
    have hdisj : ¬ (Φ ∩ ({q} ∩ ⋃ q' ∈ G \ {q}, closure {q'})).Nonempty := by
      rintro ⟨v, -, hvq, hv⟩
      rw [Set.mem_singleton_iff] at hvq
      subst hvq
      obtain ⟨q', ⟨hq'G, hq'⟩, hq'v⟩ := Set.mem_iUnion₂.mp hv
      exact hq' (hG2 v hqG q' (hGΦ hq'G) (specializes_iff_mem_closure.mpr hq'v))
    have hΦq : Φ ⊆ {q} := by
      intro v hv
      rcases hcov hv with hv' | hv'
      · exact hv'
      · exact absurd (isPreconnected_closed_iff.mp hΦconn.isPreconnected _ _ hqc hK hcov
          ⟨q, hGΦ hqG, rfl⟩ ⟨v, hv, hv'⟩) hdisj
    have hyθ : y = θ := (hΦq hyΦ).trans (hΦq hθΦ).symm
    rw [← hyx', hyθ, ← image_closure_snd h]
    exact ⟨θ, hθm, rfl⟩
  · -- `u(Φ)` is a union of curves
    right
    push Not at htriv
    have hNZ : NZ z = 0 := natTrdegResidueField_eq_zero_of_isClosed k Zbar sZbar z hz
    have hP1 : ∀ p ∈ (uu).base '' G, NX p = 1 := by
      rintro _ ⟨q, hqG, rfl⟩
      obtain ⟨b, hbΦ, hqb, hbq⟩ := htriv q hqG
      have hne : uu q ≠ uu b := fun he => hbq
        (eq_of_specializes_of_mem_fiber h hz hqb (hΦz (hGΦ hqG)) (hΦz hbΦ) he).symm
      have hlt := natTrdegResidueField_lt_of_specializes k X sX
        (hqb.map (Scheme.Hom.continuous uu)) hne
      have h1 := natTrdeg_snd_le (k := k) (sX := sX) q
      have h2 := natTrdeg_le_fst_add_one h q
      rw [show gg q = z from hΦz (hGΦ hqG), hNZ] at h2
      omega
    obtain ⟨S, hSP, hSu⟩ := exists_finset_properCurve k sX (hGfin.image _) hP1
    have hSeq : curveUnion sX S = (uu).base '' Φ := by
      rw [hSu]
      apply subset_antisymm
      · refine Set.iUnion₂_subset ?_
        rintro _ ⟨q, hqG, rfl⟩
        rw [← image_closure_snd h]
        exact Set.image_mono (closure_minimal (Set.singleton_subset_iff.mpr (hGΦ hqG)) hΦc)
      · rintro _ ⟨v, hv, rfl⟩
        obtain ⟨q, hqG, hqv⟩ := hG1 v hv
        exact Set.mem_biUnion ⟨q, hqG, rfl⟩
          (specializes_iff_mem_closure.mp (hqv.map (Scheme.Hom.continuous uu)))
    refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hSeq]; exact hΦconn.image _ (Scheme.Hom.continuous _).continuousOn
    · rw [hSeq, ← image_closure_snd h]; exact Set.image_mono hΦE
    · rw [hSeq]; exact ⟨y, hyΦ, hyx'⟩
    · rw [hSeq, ← image_closure_snd h]; exact ⟨uu θ, ⟨θ, hθΦ, rfl⟩, θ, hθm, rfl⟩
    · intro C hC
      obtain ⟨q, hqG, hq⟩ := hSP C hC
      refine h.intersectionNumber_eq_zero z hz C ?_
      rw [← hq, ← image_closure_snd h]
      exact Set.image_mono
        ((closure_minimal (Set.singleton_subset_iff.mpr (hGΦ hqG)) hΦc).trans hΦz)

/-- `u(Θ)`, `Θ = {m}⁻`, lies in a connected union of `(K_X + Δ_X)`-trivial proper curves in
`u({e_a}⁻)`. -/
private theorem exists_curves_closure_subset [LocallyOfFiniteType sZbar] [IsProper sX]
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar)
    {ea eb m : Ubar.subscheme} (hea : ea ⤳ m) (heb : eb ⤳ m) (hgea : gg ea = gg m)
    (hgeb : gg eb = gg m) (hea2 : NX (uu ea) = 2) (heb2 : NY eb = 2) (hm1 : NZ (gg m) = 1)
    (heb1 : NX (uu eb) ≤ 1) :
    ∃ ST : Finset (ProperCurve sX),
      _root_.IsConnected (curveUnion sX ST) ∧ curveUnion sX ST ⊆ closure {uu ea} ∧
      closure {uu m} ⊆ curveUnion sX ST ∧
      ∀ C ∈ ST, (Divisor.toQDivisor K + Δ).intersectionNumber k sX C.ι C.dim_le
        h.satisfiesAbundanceAssumptions.isQCartier = 0 := by
  have humle : NX (uu m) ≤ 1 :=
    (natTrdeg_le_of_specializes k X sX (heb.map (Scheme.Hom.continuous uu))).trans heb1
  have hmS : closure {uu m} ⊆ closure {uu ea} :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp
      (hea.map (Scheme.Hom.continuous uu)))) isClosed_closure
  rcases (by omega : NX (uu m) = 1 ∨ NX (uu m) = 0) with h1 | h0
  · let T₀ : ProperCurve sX := ⟨uu m, isProperCurve_of_natTrdeg_eq_one k sX h1⟩
    have hT₀ : curveUnion sX {T₀} = closure {uu m} := by
      simp only [curveUnion, Finset.set_biUnion_singleton]; rfl
    refine ⟨{T₀}, ?_, ?_, ?_, ?_⟩
    · rw [hT₀]; exact isConnected_singleton.closure
    · rw [hT₀]; exact hmS
    · rw [hT₀]
    · intro C hC
      rw [Finset.mem_singleton] at hC
      subst hC
      refine h.intersectionNumber_eq_zero_of_dim_image_le_one (E := closure {eb}) isClosed_closure
        isIrreducible_singleton.closure ?_ ?_ ?_ T₀ ?_
      · rw [dim_closure_eq k _ (Ubar.subschemeι ≫ pullback.snd sZbar sX ≫ sX), heb2]; rfl
      · rw [image_closure_singleton (Scheme.Hom.continuous _)
          (Scheme.Hom.isClosedMap (Ubar.subschemeι ≫ pullback.fst sZbar sX)),
          dim_closure_eq k Zbar sZbar, hgeb, hm1]; rfl
      · rw [image_closure_snd h, dim_closure_eq k X sX]; exact_mod_cast heb1
      · rw [image_closure_snd h]
        exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp
          (heb.map (Scheme.Hom.continuous uu)))) isClosed_closure
  · have hTc : IsClosed {uu m} :=
      isClosed_singleton_of_natTrdegResidueField_eq_zero k X sX _ h0
    obtain ⟨x₀, hx₀S, hx₀c, hx₀T⟩ : ∃ x₀ ∈ closure {uu ea}, IsClosed {x₀} ∧
        x₀ ∉ closure {uu m} := by
      by_contra hcon
      push Not at hcon
      have := LocallyOfFiniteType.jacobsonSpace sX
      have hcl := closure_inter_closedPoints (isClosed_closure (s := {uu ea}))
      have hsub : closure {uu ea} ⊆ closure {uu m} := by
        rw [← hcl]
        exact closure_minimal (fun x hx => hcon x hx.1 hx.2) isClosed_closure
      have := natTrdeg_le_of_specializes k X sX
        (specializes_iff_mem_closure.mpr (hsub (subset_closure rfl)))
      omega
    rcases exists_curves_of_isClosed h hea hgea hx₀S hx₀c with hx₀T' | ⟨S₀, h1, h2, -, h4, h5⟩
    · exact absurd hx₀T' hx₀T
    · refine ⟨S₀, h1, h2, ?_, h5⟩
      obtain ⟨p, hp, hpT⟩ := h4
      rw [hTc.closure_eq] at hpT ⊢
      rw [Set.singleton_subset_iff, ← Set.mem_singleton_iff.mp hpT]
      exact hp

/-- Every closed point of `u({e_a}⁻)` is joined to `u(Θ)` by a connected union of
`(K_X + Δ_X)`-trivial proper curves in `u({e_a}⁻)` extending `ST`. -/
private theorem exists_curves_union_of_isClosed [LocallyOfFiniteType sZbar] [IsProper sX]
    [DecidableEq (ProperCurve sX)]
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) {ea m : Ubar.subscheme} (hea : ea ⤳ m)
    (hgea : gg ea = gg m) {ST : Finset (ProperCurve sX)}
    (hSTconn : _root_.IsConnected (curveUnion sX ST))
    (hSTS : curveUnion sX ST ⊆ closure {uu ea}) (hTST : closure {uu m} ⊆ curveUnion sX ST)
    (hSTtriv : ∀ C ∈ ST, (Divisor.toQDivisor K + Δ).intersectionNumber k sX C.ι C.dim_le
      h.satisfiesAbundanceAssumptions.isQCartier = 0)
    {x : X} (hx : x ∈ closure {uu ea}) (hxc : IsClosed {x}) :
    ∃ Sx : Finset (ProperCurve sX),
      _root_.IsConnected (curveUnion sX (ST ∪ Sx)) ∧ curveUnion sX (ST ∪ Sx) ⊆ closure {uu ea} ∧
      x ∈ curveUnion sX (ST ∪ Sx) ∧ ∀ C ∈ ST ∪ Sx,
        (Divisor.toQDivisor K + Δ).intersectionNumber k sX C.ι C.dim_le
          h.satisfiesAbundanceAssumptions.isQCartier = 0 := by
  rcases exists_curves_of_isClosed h hea hgea hx hxc with hxT | ⟨Sx, h1, h2, h3, h4, h5⟩
  · refine ⟨∅, ?_, ?_, ?_, ?_⟩ <;> simp only [Finset.union_empty]
    · exact hSTconn
    · exact hSTS
    · exact hTST hxT
    · exact hSTtriv
  · refine ⟨Sx, ?_, ?_, ?_, ?_⟩
    · rw [curveUnion_union]
      obtain ⟨p, hp, hpT⟩ := h4
      exact hSTconn.union ⟨p, hTST hpT, hp⟩ h1
    · rw [curveUnion_union]; exact Set.union_subset hSTS h2
    · rw [curveUnion_union]; exact Or.inr h3
    · exact fun C hC => (Finset.mem_union.mp hC).elim (hSTtriv C) (h5 C)

/-- **Step 4, assembly.** With `e_a`, `e_b`, `m` as in `exists_components`, the prime divisor
`S = u({e_a}⁻)` of `X` is `(K_X + Δ_X)`-trivially connected: any two closed points of `S` are
joined, through `u(Θ)`, `Θ = {m}⁻`, by the curves of `exists_curves_of_isClosed`; `u(Θ)` is a
point or an `L`-trivial curve by `IsChowClosure.intersectionNumber_eq_zero_of_dim_image_le_one`
applied to `E₂ = {e_b}⁻`. -/
private theorem exists_isTriviallyConnected_of_components [LocallyOfFiniteType sZbar]
    [IsProper sX] (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar)
    {ea eb m : Ubar.subscheme} (hea : ea ⤳ m) (heb : eb ⤳ m) (hgea : gg ea = gg m)
    (hgeb : gg eb = gg m) (hea2 : NX (uu ea) = 2) (heb2 : NY eb = 2) (hm1 : NZ (gg m) = 1)
    (heb1 : NX (uu eb) ≤ 1) :
    ∃ D : Mori.PrimeDivisor X, IsTriviallyConnected k sX 3 K Δ (Finsupp.single D 1) := by
  classical
  have hA := h.satisfiesAbundanceAssumptions
  -- the prime divisor `S`
  have hcoh : Order.coheight (uu ea) = 1 := by
    have := natTrdeg_add_coheight k X sX (uu ea)
    rw [hA.dim_eq, hea2] at this
    exact coheight_eq_one_of_two_add this
  set D := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (uu ea) hcoh
  have hDsupp : (DivisorWithCoeffs.supp (R := ℤ) (Finsupp.single D 1) : Set X) =
      closure {uu ea} := by
    rw [DivisorWithCoeffs.coe_supp, Finsupp.support_single_ne_zero _ one_ne_zero,
      Finset.set_biUnion_singleton]
    change D.support = _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  obtain ⟨ST, hSTconn, hSTS, hTST, hSTtriv⟩ :=
    exists_curves_closure_subset h hea heb hgea hgeb hea2 heb2 hm1 heb1
  refine ⟨D, hA.isQFactorial.1, isProper_of_isProjectiveMorphism _
    ((AlgebraicGeometry.isProjectiveVariety_iff k sX).mp hA.isProjectiveVariety).2,
    hA.isKawamataLogTerminal.2.1, hA.isQCartier, ?_, ?_⟩
  · intro E
    change 0 ≤ (Finsupp.single D (1 : ℤ)) E
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num
  · intro x₁ hx₁ x₂ hx₂ hc₁ hc₂
    rw [hDsupp] at hx₁ hx₂ ⊢
    obtain ⟨S₁, h11, h12, h13, h14⟩ :=
      exists_curves_union_of_isClosed h hea hgea hSTconn hSTS hTST hSTtriv hx₁ hc₁
    obtain ⟨S₂, h21, h22, h23, h24⟩ :=
      exists_curves_union_of_isClosed h hea hgea hSTconn hSTS hTST hSTtriv hx₂ hc₂
    obtain ⟨p, hp⟩ : (closure {uu m}).Nonempty := ⟨uu m, subset_closure rfl⟩
    have hpST := hTST hp
    refine ⟨(ST ∪ S₁) ∪ (ST ∪ S₂), ?_, ?_, ?_, ?_, ?_⟩
    · rw [curveUnion_union]
      refine h11.union ⟨p, ?_, ?_⟩ h21 <;> rw [curveUnion_union] <;> exact Or.inl hpST
    · rw [curveUnion_union]; exact Set.union_subset h12 h22
    · rw [curveUnion_union]; exact Or.inl h13
    · rw [curveUnion_union]; exact Or.inr h23
    · exact fun C hC => (Finset.mem_union.mp hC).elim (h14 C) (h24 C)

end ChowClosure

/-- **A contracted divisor gives a trivially connected divisor** (FA, proof of 15.10). Let
`(Z₀, Z̄, Ū)` be a Chow closure of `f_U` (`MMP.Flips.IsChowClosure`), with projection
`u : Ū ⟶ X`, and let `F` be a prime divisor of `Ū` with `dim u(F) ≤ 1`. Then `X` contains a
`(K_X + Δ_X)`-trivially connected prime divisor (`MMP.Flips.IsTriviallyConnected`). -/
@[mmp "lem_fa15_contracted_divisor_gives_trivially_connected"]
public theorem IsChowClosure.exists_isTriviallyConnected_of_dim_image_le_one
    [IsAlgClosed k] [CharZero k] {K : Divisor X} {Δ : QDivisor X}
    {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens} {j : Z₀.toScheme ⟶ Zbar}
    {Ubar : (pullback sZbar sX).IdealSheafData}
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) (F : Mori.PrimeDivisor Ubar.subscheme)
    (hF : topologicalKrullDim
      ((Ubar.subschemeι ≫ pullback.snd sZbar sX).base '' (F.support : Set Ubar.subscheme)) ≤ 1) :
    ∃ D : Mori.PrimeDivisor X, IsTriviallyConnected k sX 3 K Δ (Finsupp.single D 1) := by
  have : IsProper sX := isProper_of_isProjectiveMorphism _
    ((AlgebraicGeometry.isProjectiveVariety_iff k sX).mp
      h.satisfiesAbundanceAssumptions.isProjectiveVariety).2
  have : LocallyOfFiniteType sZbar := h.isNormalVariety.1.toLocallyOfFiniteType
  obtain ⟨ea, eb, m, hea, heb, hgea, hgeb, hea2, heb2, hm1, heb1⟩ := exists_components h F hF
  exact exists_isTriviallyConnected_of_components h hea heb hgea hgeb hea2 heb2 hm1 heb1

end MMP.Flips
