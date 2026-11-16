module

public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Divisor.Canonical.PluricanonicalForms
public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.S2
public import MMP.AlgebraicGeometry.Modules.TotalQuotientSheaf
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.SmoothLocus
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSmoothLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.TsenFunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullbackCycles.SchemeTheoreticImage
public import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.Restriction
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexUpperShriek
public import StacksFrontier.AlgebraicGeometry.Divisors.ReflexiveEquivalence.StalkDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.UpperShriekStructureSheafTrivial

/-!
# The embedded dualizing sheaf of a normal variety is `𝒪_X(K_X)`

Let `X` be a normal variety of dimension `d` over a field `k` of characteristic zero, and let
`ω ⊆ K(X)` be a Weil divisorial subsheaf which is a dualizing sheaf of `X`
(`MMP.Flips.IsDualizingSheaf`). Then there is a nonzero rational top form `τ` whose divisor
`K = div τ` is a canonical divisor of `X` and `ω = 𝒪_X(K)` as subsheaves of `K(X)`. In
particular, for any canonical divisor `K'` of `X`, `ω` equals `𝒪_X(K')` up to multiplication by a
unit of `K(X)`.

## Main definitions

* `MMP.Flips.Divisor.toWeilDivisor`: a divisor regarded as a Weil divisor of FA 16.2.1.
* `MMP.Flips.rationalFunctionsStalkEval`: on an integral scheme, the value at the generic point
  of a germ of a rational function.

## Main results

* `MMP.Flips.IsDualizingSheaf.exists_eq_sheaf_toWeilDivisor`: `ω = 𝒪_X(div τ)` for a nonzero
  rational top form `τ`, and `div τ` is a canonical divisor.
* `MMP.Flips.WeilDivisorialSubsheaf.exists_eq_sheaf_toWeilDivisor`: on an integral normal scheme of
  finite type and pure dimension over a field, every Weil divisorial subsheaf is some `𝒪(D)`.
* `MMP.Flips.toModules_sheaf_toWeilDivisor`: the sheaf `𝒪(D)` of FA 16.2.2 is the divisorial sheaf
  `𝒪_X(D)` of KM Notation 0.4.
* `MMP.Flips.IsDualizingSheaf.nonempty_restrict_iso_relativeDifferentialForms`: on a smooth open
  `U` which embeds in a smooth proper scheme, `ω|_U ≅ ⋀ᵈ Ω_{U/k}`.
* `MMP.Flips.IsDualizingSheaf.nonempty_restrict_smoothLocus_iso`: `ω|_{X_sm} ≅ ⋀ᵈ Ω_{X_sm/k}`.

## Implementation notes

The dualizing sheaf is `H^{-d}(π^! k)`. On the smooth locus `X_sm` it is identified with
`⋀ᵈ Ω_{X_sm/k}` (Stacks, Tag 0EA0) once `X_sm` is embedded as an open subscheme of a smooth proper
variety. That variety is a strong resolution of the closure of `X` in a compactification, which
is an isomorphism over the smooth locus. A Weil divisorial subsheaf of `K(X)` on a normal scheme is
`𝒪_X(D)` for the divisor `D` read off at the generic points of the prime divisors, and
`𝒪_X(D)|_{X_sm} ≅ ⋀ᵈ Ω_{X_sm/k}` says that `D` is a canonical divisor. Characteristic zero is used
for the resolution, and for writing canonical divisors as divisors of forms.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.3.3
* [Stacks Project, Tag 0EA0](https://stacks.math.columbia.edu/tag/0EA0)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Flips

open MMP.Mori

variable {X : Scheme.{u}}

/-- A divisor `D = ∑ n_Γ Γ` regarded as the Weil divisor `∑ n_Γ Γ` of FA 16.2.1, the sum running
over the prime divisors `Γ` along which `𝒪_{X,Γ}` is a discrete valuation ring. -/
def Divisor.toWeilDivisor (D : MMP.Mori.Divisor X) : WeilDivisor X :=
  Finsupp.subtypeDomain
    (fun Γ : MMP.Mori.PrimeDivisor X =>
      ∃ _ : IsDomain Γ.localRing, IsDiscreteValuationRing Γ.localRing) D

/-- The coefficient of `Divisor.toWeilDivisor D` at a prime Weil divisor `Γ` is the coefficient of
`D` at `Γ`. -/
@[simp]
theorem Divisor.toWeilDivisor_apply (D : MMP.Mori.Divisor X) (Γ : WeilDivisorPrime X) :
    Divisor.toWeilDivisor D Γ = D.coeff Γ.1 :=
  rfl

/-! ### Evaluating germs of rational functions on an integral scheme -/

section Eval

open Opposite TopologicalSpace

variable [IsIntegral X]

omit [IsIntegral X] in
/-- On an irreducible space, every irreducible component is the whole space. -/
theorem irreducibleComponents_val_eq_univ [IrreducibleSpace X] (Z : irreducibleComponents X) :
    Z.1 = Set.univ := by
  simpa [irreducibleComponents_eq_singleton] using Z.2

omit [IsIntegral X] in
/-- An irreducible space has at most one irreducible component. -/
theorem subsingleton_irreducibleComponents [IrreducibleSpace X] :
    Subsingleton (irreducibleComponents X) :=
  ⟨fun a b => Subtype.ext ((irreducibleComponents_val_eq_univ a).trans
    (irreducibleComponents_val_eq_univ b).symm)⟩

omit [IsIntegral X] in
/-- On an irreducible scheme, the generic point of the irreducible component lies in every nonempty
open subset. -/
theorem componentGenericPoint_mem_of_nonempty [IrreducibleSpace X] (Z : irreducibleComponents X)
    {U : X.Opens} (hU : (U : Set X).Nonempty) : componentGenericPoint X Z ∈ U := by
  have h1 := isGenericPoint_componentGenericPoint X Z
  rw [irreducibleComponents_val_eq_univ Z] at h1
  exact (h1.mem_open_set_iff U.isOpen).mpr (by simpa using hU)

omit [IsIntegral X] in
/-- On an irreducible scheme, the generic point of the irreducible component specializes to every
point. -/
theorem componentGenericPoint_specializes [IrreducibleSpace X] (Z : irreducibleComponents X)
    (x : X) : componentGenericPoint X Z ⤳ x :=
  (isGenericPoint_componentGenericPoint X Z).specializes
    (by rw [irreducibleComponents_val_eq_univ Z]; trivial)

/-- On an integral scheme, the germ of a rational function at any point determines its value
`φ_Z ∈ 𝒪_{X,η_Z}` at the generic point: the map `K(X)_x → 𝒪_{X,η_Z}`. -/
def rationalFunctionsStalkEval (x : X) (Z : irreducibleComponents X) :
    (rationalFunctionsPresheaf X).stalk x ⟶ X.presheaf.stalk (componentGenericPoint X Z) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ rationalFunctionsPresheaf X)
    { pt := X.presheaf.stalk (componentGenericPoint X Z)
      ι :=
        { app := fun U => CommRingCat.ofHom (Pi.evalRingHom
              (fun Z' : {Z' : irreducibleComponents X // componentGenericPoint X Z' ∈ U.unop.1} =>
                X.presheaf.stalk (componentGenericPoint X Z'.1))
              ⟨Z, componentGenericPoint_mem_of_nonempty Z ⟨x, U.unop.2⟩⟩)
          naturality := fun U V i => by ext s; rfl } }

/-- `rationalFunctionsStalkEval x Z` sends the germ at `x` of a section `s` of rational functions
to the component of `s` at the generic point of `Z`. -/
theorem rationalFunctionsStalkEval_germ (x : X) (Z : irreducibleComponents X) {U : X.Opens}
    (hx : x ∈ U) (s : ToType ((rationalFunctionsPresheaf X).obj (op U))) :
    (rationalFunctionsStalkEval x Z).hom ((rationalFunctionsPresheaf X).germ U x hx s) =
      s ⟨Z, componentGenericPoint_mem_of_nonempty Z ⟨x, hx⟩⟩ := by
  show ((TopCat.Presheaf.germ _ U x hx ≫ rationalFunctionsStalkEval x Z).hom s) = _
  rw [TopCat.Presheaf.germ, rationalFunctionsStalkEval]
  erw [Limits.colimit.ι_desc]
  rfl

/-- On the image of `𝒪_{X,x}` in `K(X)_x`, `rationalFunctionsStalkEval x Z` is the specialization
map `𝒪_{X,x} → 𝒪_{X,η_Z}`. -/
theorem rationalFunctionsStalkEval_structure (x : X) (Z : irreducibleComponents X)
    (a : X.presheaf.stalk x) :
    (rationalFunctionsStalkEval x Z).hom ((structureStalkToRationalFunctionsStalk X x).hom a) =
      (X.presheaf.stalkSpecializes (componentGenericPoint_specializes Z x)).hom a := by
  obtain ⟨V, hV, r, rfl⟩ := X.presheaf.exists_germ_eq a
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply V x hV (toRationalFunctionsPresheaf X) r
  rw [structureStalkToRationalFunctionsStalk]
  erw [h]
  rw [rationalFunctionsStalkEval_germ, TopCat.Presheaf.germ_stalkSpecializes_apply]
  rfl

/-- On an integral scheme, `rationalFunctionsStalkEval x Z` is injective. -/
theorem rationalFunctionsStalkEval_injective (x : X) (Z : irreducibleComponents X) :
    Function.Injective (rationalFunctionsStalkEval x Z).hom := by
  have := subsingleton_irreducibleComponents (X := X)
  rw [injective_iff_map_eq_zero]
  intro g hg
  obtain ⟨U, hx, s, rfl⟩ := (rationalFunctionsPresheaf X).exists_germ_eq g
  rw [rationalFunctionsStalkEval_germ] at hg
  have hs : s = 0 := by
    funext Z'
    obtain ⟨Z', hZ'⟩ := Z'
    obtain rfl : Z' = Z := Subsingleton.elim _ _
    exact hg
  rw [hs, map_zero]

end Eval

section Valuation

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- At the generic point of a prime divisor `E`, `rationalFunctionsStalkEval` restricted to
`𝒪_{X,E}` is the map `E.toComponent` to the stalk at the generic point of `X`. -/
theorem rationalFunctionsStalkEval_structure_primeDivisor (E : MMP.Mori.PrimeDivisor X)
    (a : X.presheaf.stalk E.genericPoint) :
    (rationalFunctionsStalkEval E.genericPoint E.component).hom
        ((structureStalkToRationalFunctionsStalk X E.genericPoint).hom a) =
      E.toComponent.hom a :=
  rationalFunctionsStalkEval_structure _ _ a

/-- At the generic point of a prime divisor `E`, the germs `f · 𝒪_{X,E}` for a unit `f` of
`K(X)_E` are the germs `g` with `v_E(g) ≥ v_E(f)`. -/
theorem mem_range_unit_mul_iff_ordGE (E : MMP.Mori.PrimeDivisor X)
    (f : ((rationalFunctionsPresheaf X).stalk E.genericPoint)ˣ) {v : ℤ}
    (hv : E.valuation ((rationalFunctionsStalkEval E.genericPoint E.component).hom f) =
      WithZero.exp v)
    (g : (rationalFunctionsPresheaf X).stalk E.genericPoint) :
    g ∈ Set.range (fun a : X.presheaf.stalk E.genericPoint =>
        (f : (rationalFunctionsPresheaf X).stalk E.genericPoint) *
          (structureStalkToRationalFunctionsStalk X E.genericPoint).hom a) ↔
      E.OrdGE v ((rationalFunctionsStalkEval E.genericPoint E.component).hom g) := by
  set ev := (rationalFunctionsStalkEval E.genericPoint E.component).hom with hev
  constructor
  · rintro ⟨a, rfl⟩
    rw [map_mul, rationalFunctionsStalkEval_structure_primeDivisor]
    by_cases ha : a = 0
    · left
      rw [ha, map_zero, mul_zero]
    · right
      rw [map_mul, hv]
      exact le_mul_of_one_le_right' (E.one_le_valuation_toComponent ha)
  · rintro (h0 | h)
    · refine ⟨0, rationalFunctionsStalkEval_injective E.genericPoint E.component ?_⟩
      simpa only [map_mul, map_zero, mul_zero] using h0.symm
    · let u := Units.map ev.toMonoidHom f
      have hu : (u : X.presheaf.stalk (componentGenericPoint X E.component)) = ev f := rfl
      have huinv : E.valuation (↑u⁻¹ : X.presheaf.stalk (componentGenericPoint X E.component)) =
          (WithZero.exp v)⁻¹ := by
        have h1 : E.valuation (u : X.presheaf.stalk (componentGenericPoint X E.component)) *
            E.valuation (↑u⁻¹ : X.presheaf.stalk (componentGenericPoint X E.component)) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [hu, hv] at h1
        exact eq_inv_of_mul_eq_one_right h1
      have hc : 1 ≤ E.valuation (ev g * ↑u⁻¹) := by
        rw [map_mul, huinv]
        calc (1 : WithZero (Multiplicative ℤ)) = WithZero.exp v * (WithZero.exp v)⁻¹ := by
              rw [mul_inv_cancel₀ (WithZero.exp_ne_zero)]
          _ ≤ _ := mul_le_mul_left h _
      obtain ⟨b, hb⟩ := E.exists_toComponent_eq_of_one_le_valuation hc
      refine ⟨b, ?_⟩
      apply rationalFunctionsStalkEval_injective E.genericPoint E.component
      rw [← hev, map_mul, rationalFunctionsStalkEval_structure_primeDivisor, hb, ← hu,
        mul_left_comm, Units.mul_inv, mul_one]

/-- If a unit `w` has valuation `exp a` at a prime divisor `E`, then `w ^ n` has valuation
`exp (n * a)`. -/
theorem valuation_units_zpow (E : MMP.Mori.PrimeDivisor X)
    (w : (X.presheaf.stalk (componentGenericPoint X E.component))ˣ) {a : ℤ}
    (hw : E.valuation (w : X.presheaf.stalk (componentGenericPoint X E.component)) =
      WithZero.exp a) (n : ℤ) :
    E.valuation ((w ^ n : (X.presheaf.stalk (componentGenericPoint X E.component))ˣ) :
      X.presheaf.stalk (componentGenericPoint X E.component)) = WithZero.exp (n * a) := by
  have h : E.valuation ((w ^ n : (X.presheaf.stalk (componentGenericPoint X E.component))ˣ) :
      X.presheaf.stalk (componentGenericPoint X E.component)) =
      ((Units.map E.valuation.toMonoidHom (w ^ n) : (WithZero (Multiplicative ℤ))ˣ) :
        WithZero (Multiplicative ℤ)) := rfl
  rw [h, map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map]
  change (E.valuation (w : X.presheaf.stalk (componentGenericPoint X E.component))) ^ n = _
  rw [hw, ← WithZero.exp_zsmul, smul_eq_mul]

/-- At the generic point of a prime divisor `Γ` along which `X` is a discrete valuation ring, the
germs `t_Γ^n · 𝒪_{X,Γ}` are the germs `g` with `v_Γ(g) ≥ n`. -/
theorem mem_range_uniformizerUnit_zpow_mul_iff_ordGE [CompactSpace X] (Γ : WeilDivisorPrime X)
    (n : ℤ) (g : (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) :
    haveI : IsNoetherian X := {}
    g ∈ Set.range (fun a : X.presheaf.stalk Γ.1.genericPoint =>
        ((Γ.uniformizerUnit ^ n : ((rationalFunctionsPresheaf X).stalk Γ.1.genericPoint)ˣ) :
          (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) *
          (structureStalkToRationalFunctionsStalk X Γ.1.genericPoint).hom a) ↔
      Γ.1.OrdGE n ((rationalFunctionsStalkEval Γ.1.genericPoint Γ.1.component).hom g) := by
  haveI : IsNoetherian X := {}
  refine mem_range_unit_mul_iff_ordGE Γ.1 _ ?_ g
  set ev := (rationalFunctionsStalkEval Γ.1.genericPoint Γ.1.component).hom
  have hT : Γ.1.valuation ((Units.map ev.toMonoidHom Γ.uniformizerUnit :
      (X.presheaf.stalk (componentGenericPoint X Γ.1.component))ˣ) :
        X.presheaf.stalk (componentGenericPoint X Γ.1.component)) = WithZero.exp 1 := by
    change Γ.1.valuation (ev ((structureStalkToRationalFunctionsStalk X _).hom Γ.uniformizer)) = _
    rw [rationalFunctionsStalkEval_structure_primeDivisor]
    exact Γ.1.valuation_toComponent_of_irreducible Γ.irreducible_uniformizer
  have := valuation_units_zpow Γ.1 _ hT n
  rwa [mul_one, ← map_zpow] at this

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- At a point of coheight zero (the generic point) of an integral scheme, `𝒪_{X,x} → K(X)_x` is
surjective. -/
theorem structureStalkToRationalFunctionsStalk_surjective {x : X} (hx : Order.coheight x = 0) :
    Function.Surjective (structureStalkToRationalFunctionsStalk X x).hom := by
  obtain ⟨Z⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  have hmax : IsMax x := Order.coheight_eq_zero.mp hx
  have hsp : x ⤳ componentGenericPoint X Z :=
    Scheme.le_iff_specializes.mp (hmax (Scheme.le_iff_specializes.mpr
      (componentGenericPoint_specializes Z x)))
  intro g
  refine ⟨(X.presheaf.stalkSpecializes hsp).hom
    ((rationalFunctionsStalkEval x Z).hom g), ?_⟩
  apply rationalFunctionsStalkEval_injective x Z
  rw [rationalFunctionsStalkEval_structure, ← CommRingCat.comp_apply,
    TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- On an integral locally Noetherian normal scheme, a point of codimension at most one which is
not the generic point of a prime divisor is the generic point. -/
theorem coheight_eq_zero_of_forall_ne {x : X} (hc : Order.coheight x ≤ 1)
    (hΓ : ∀ Γ : WeilDivisorPrime X, Γ.1.genericPoint ≠ x) : Order.coheight x = 0 := by
  rcases le_iff_lt_or_eq.mp hc with h | h
  · exact ENat.lt_one_iff_eq_zero.mp h
  · exact absurd (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x h)
      (hΓ ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h, inferInstance,
        MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing _⟩)

/-- **The two sheaves `𝒪_X(D)` agree.** On an integral locally Noetherian normal quasi-compact
scheme, the sections of the sheaf `𝒪(D)` of FA 16.2.2 of the Weil divisor of a divisor `D`,
cut out by stalk conditions, are the sections of the divisorial sheaf `𝒪_X(D)` of KM Notation
0.4, cut out by orders of vanishing. -/
theorem sheaf_toWeilDivisor_sections [CompactSpace X] (D : MMP.Mori.Divisor X) (U : X.Opens) :
    (Divisor.toWeilDivisor D).sheaf.sections U = D.divisorialSubmodule U := by
  haveI : IsNoetherian X := {}
  ext s
  change (∀ (x : X) (hx : x ∈ U), (Divisor.toWeilDivisor D).StalkCondition x _) ↔
    D.IsDivisorialSection U s
  constructor
  · intro h E hE
    let Γ : WeilDivisorPrime X := ⟨E, inferInstance, E.isDiscreteValuationRing_localRing⟩
    have h' := h Γ.1.genericPoint (E.genericPoint_mem_of_nonempty hE)
    rwa [WeilDivisor.stalkCondition_genericPoint_iff,
      mem_range_uniformizerUnit_zpow_mul_iff_ordGE, rationalFunctionsStalkEval_germ] at h'
  · intro h x hx
    by_cases hc : Order.coheight x ≤ 1
    · by_cases hΓ : ∃ Γ : WeilDivisorPrime X, Γ.1.genericPoint = x
      · obtain ⟨Γ, rfl⟩ := hΓ
        rw [WeilDivisor.stalkCondition_genericPoint_iff,
          mem_range_uniformizerUnit_zpow_mul_iff_ordGE, rationalFunctionsStalkEval_germ]
        refine h Γ.1 ⟨_, ?_, hx⟩
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      · push Not at hΓ
        rw [WeilDivisor.stalkCondition_iff_of_forall_ne _ hc hΓ]
        exact structureStalkToRationalFunctionsStalk_surjective
          (coheight_eq_zero_of_forall_ne hc hΓ) _
    · exact WeilDivisor.stalkCondition_of_not_coheight_le_one _ hc _

/-- The sheaf `𝒪(D)` of a Weil divisor, cut out by stalk conditions at the points of codimension
at most one, is saturated. -/
theorem _root_.MMP.Flips.WeilDivisor.isSaturated_sheaf (D : WeilDivisor X) :
    D.sheaf.IsSaturated := by
  refine RationalFunctionsSubmodule.ext fun V => le_antisymm (D.sheaf.sections_le_saturation V)
    fun s hs => ?_
  intro x hx
  by_cases hc : Order.coheight x ≤ 1
  · obtain ⟨W, hxW, t, ht, hts⟩ := hs x hx hc
    rw [← hts]
    exact ht x hxW
  · exact WeilDivisor.stalkCondition_of_not_coheight_le_one _ hc _

/-- **The two sheaves `𝒪_X(D)` agree as `𝒪_X`-modules**: the sheaf `𝒪(D)` of FA 16.2.2 of the Weil
divisor of `D` is the divisorial sheaf `𝒪_X(D)` of KM Notation 0.4. -/
theorem toModules_sheaf_toWeilDivisor [CompactSpace X] (D : MMP.Mori.Divisor X) :
    (Divisor.toWeilDivisor D).sheaf.toModules = D.divisorialSheaf := by
  let G : RationalFunctionsSubmodule X :=
    { sections := D.divisorialSubmodule
      map_mem := fun i _ hs => Divisor.IsDivisorialSection.map i hs
      mem_of_locally := fun {U} {s} hs => by
        rw [← sheaf_toWeilDivisor_sections]
        exact (Divisor.toWeilDivisor D).sheaf.mem_of_locally fun x hx => by
          obtain ⟨W, i, hxW, h⟩ := hs x hx
          exact ⟨W, i, hxW, by rwa [sheaf_toWeilDivisor_sections]⟩ }
  rw [show (Divisor.toWeilDivisor D).sheaf = G from
    RationalFunctionsSubmodule.ext (sheaf_toWeilDivisor_sections D)]
  rfl

/-- A section of `K(X)` over a nonempty open of an integral scheme with nonzero value is a unit
of `K(X)`. -/
theorem exists_units_eq_of_ne_zero {V : X.Opens} (hV : (V : Set X).Nonempty)
    (s : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op V)))
    (hs : ∀ Z, s Z ≠ 0) :
    ∃ φ : (RationalFunctions X)ˣ,
      ∀ (Z : irreducibleComponents X) (h : componentGenericPoint X Z ∈ V),
        (φ : RationalFunctions X) Z = s ⟨Z, h⟩ := by
  have hu : ∀ Z : irreducibleComponents X, ∃ b : X.presheaf.stalk (componentGenericPoint X Z),
      s ⟨Z, componentGenericPoint_mem_of_nonempty Z hV⟩ * b = 1 := fun Z =>
    (RationalFunctions.isField_stalk X Z).mul_inv_cancel
      (hs ⟨Z, componentGenericPoint_mem_of_nonempty Z hV⟩)
  choose b hb using hu
  let φv : RationalFunctions X := fun Z => s ⟨Z, componentGenericPoint_mem_of_nonempty Z hV⟩
  have hφ : φv * b = 1 := funext hb
  exact ⟨⟨φv, b, hφ, (mul_comm _ _).trans hφ⟩, fun Z h => rfl⟩

/-- **A Weil divisorial subsheaf of a normal variety is `𝒪(D)`.** On an integral normal scheme of
finite type and pure dimension over a field, every Weil divisorial subsheaf `𝓛 ⊆ K(X)` is the
sheaf `𝒪(D)` of the Weil divisor of a divisor `D`, read off from the generators of `𝓛` at the
generic points of the prime divisors. -/
theorem WeilDivisorialSubsheaf.exists_eq_sheaf_toWeilDivisor [CompactSpace X] {k : Type u}
    [Field k] (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (L : WeilDivisorialSubsheaf X) :
    ∃ D : MMP.Mori.Divisor X,
      L.toRationalFunctionsSubmodule = (Divisor.toWeilDivisor D).sheaf := by
  haveI : IsNoetherian X := {}
  have hsub := subsingleton_irreducibleComponents (X := X)
  obtain ⟨Z⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  have hgen : ∀ E : MMP.Mori.PrimeDivisor X,
      ∃ f : ((rationalFunctionsPresheaf X).stalk E.genericPoint)ˣ,
        L.stalkSet E.genericPoint = Set.range fun a : X.presheaf.stalk E.genericPoint =>
          (f : (rationalFunctionsPresheaf X).stalk E.genericPoint) *
            (structureStalkToRationalFunctionsStalk X E.genericPoint).hom a :=
    fun E => L.principal_codim_one _ E.coheight_genericPoint.le
  choose f hf using hgen
  have hval : ∀ E : MMP.Mori.PrimeDivisor X, ∃ v : ℤ,
      E.valuation ((rationalFunctionsStalkEval E.genericPoint E.component).hom (f E)) =
        WithZero.exp v := by
    intro E
    have hu : IsUnit ((rationalFunctionsStalkEval E.genericPoint E.component).hom (f E)) :=
      (f E).isUnit.map _
    exact ⟨WithZero.log _, (WithZero.exp_log (hu.map E.valuation).ne_zero).symm⟩
  choose v hv using hval
  have hL : ∀ (E : MMP.Mori.PrimeDivisor X) g, g ∈ L.stalkSet E.genericPoint ↔
      E.OrdGE (v E) ((rationalFunctionsStalkEval E.genericPoint E.component).hom g) :=
    fun E g => by rw [hf E]; exact mem_range_unit_mul_iff_ordGE E (f E) (hv E) g
  have hLinv : ∀ (E : MMP.Mori.PrimeDivisor X) g, g ∈ L.inv.stalkSet E.genericPoint ↔
      E.OrdGE (-v E) ((rationalFunctionsStalkEval E.genericPoint E.component).hom g) := by
    intro E g
    rw [(WeilDivisorialSubsheaf.stalkSet_mul_inv_unit L L _ E.coheight_genericPoint.le
      (f E) (f E) (hf E) (hf E)).2.1]
    refine mem_range_unit_mul_iff_ordGE E (f E)⁻¹ ?_ g
    have h1 : E.valuation ((rationalFunctionsStalkEval E.genericPoint E.component).hom (f E)) *
        E.valuation ((rationalFunctionsStalkEval E.genericPoint E.component).hom
          ↑(f E)⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    rw [hv E] at h1
    rw [WithZero.exp_neg]
    exact eq_inv_of_mul_eq_one_right h1
  have hc0 := MMP.Flips.coheight_componentGenericPoint_le_one Z
  obtain ⟨f0, hf0⟩ := L.principal_codim_one _ hc0
  have hinv0 := (WeilDivisorialSubsheaf.stalkSet_mul_inv_unit L L _ hc0 f0 f0 hf0 hf0).2.1
  obtain ⟨V, hV, s, hs, hsg⟩ : (f0 : (rationalFunctionsPresheaf X).stalk _) ∈
      L.stalkSet (componentGenericPoint X Z) := by rw [hf0]; exact ⟨1, by simp⟩
  obtain ⟨V', hV', s', hs', hsg'⟩ : ((f0⁻¹ : ((rationalFunctionsPresheaf X).stalk _)ˣ) :
      (rationalFunctionsPresheaf X).stalk _) ∈ L.inv.stalkSet (componentGenericPoint X Z) := by
    rw [hinv0]; exact ⟨1, by simp⟩
  have hne : ∀ (u : ((rationalFunctionsPresheaf X).stalk (componentGenericPoint X Z))ˣ),
      (rationalFunctionsStalkEval (componentGenericPoint X Z) Z).hom u ≠ 0 := fun u =>
    ((u.isUnit.map _).ne_zero : _)
  have hs0 : ∀ Z', s Z' ≠ 0 := by
    rintro ⟨Z', hZ'⟩
    obtain rfl : Z' = Z := Subsingleton.elim _ _
    have := hne f0
    rwa [← hsg, rationalFunctionsStalkEval_germ] at this
  have hs0' : ∀ Z', s' Z' ≠ 0 := by
    rintro ⟨Z', hZ'⟩
    obtain rfl : Z' = Z := Subsingleton.elim _ _
    have := hne f0⁻¹
    rwa [← hsg', rationalFunctionsStalkEval_germ] at this
  obtain ⟨φ, hφ⟩ := exists_units_eq_of_ne_zero ⟨_, hV⟩ s hs0
  obtain ⟨φ', hφ'⟩ := exists_units_eq_of_ne_zero ⟨_, hV'⟩ s' hs0'
  have hle : ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ V → v E ≤ E.ord φ := by
    intro E hE
    have h := (hL E _).mp ⟨V, hE, s, hs, rfl⟩
    rw [rationalFunctionsStalkEval_germ] at h
    have hφE := hφ E.component (componentGenericPoint_mem_of_nonempty _ ⟨_, hV⟩)
    rw [← hφE] at h
    rcases h with h | h
    · exact absurd h (φ.isUnit.map (RationalFunctions.component X E.component)).ne_zero
    · rwa [E.valuation_component, WithZero.exp_le_exp] at h
  have hle' : ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ V' → -v E ≤ E.ord φ' := by
    intro E hE
    have h := (hLinv E _).mp ⟨V', hE, s', hs', rfl⟩
    rw [rationalFunctionsStalkEval_germ] at h
    have hφE := hφ' E.component (componentGenericPoint_mem_of_nonempty _ ⟨_, hV'⟩)
    rw [← hφE] at h
    rcases h with h | h
    · exact absurd h (φ'.isUnit.map (RationalFunctions.component X E.component)).ne_zero
    · rwa [E.valuation_component, WithZero.exp_le_exp] at h
  have hout : ∀ W : X.Opens, componentGenericPoint X Z ∈ W →
      {E : MMP.Mori.PrimeDivisor X | E.genericPoint ∉ W}.Finite := by
    intro W hW
    refine Set.Finite.of_finite_image ((finite_coheight_eq_one_mem_closure_notMem _ W hW).subset
      ?_) AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
    rintro - ⟨E, hE, rfl⟩
    refine ⟨?_, hE, E.coheight_genericPoint⟩
    rw [(isGenericPoint_componentGenericPoint X Z).def, irreducibleComponents_val_eq_univ]
    trivial
  have hfin : {E : MMP.Mori.PrimeDivisor X | -v E ≠ 0}.Finite := by
    refine (((finite_ord_ne_zero φ).union (finite_ord_ne_zero φ')).union
      ((hout V hV).union (hout V' hV'))).subset ?_
    intro E hE
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcon
    have a := hle E h3
    have b := hle' E h4
    exact hE (by omega)
  let D : MMP.Mori.Divisor X := Finsupp.ofSupportFinite (fun E => -v E) hfin
  have hD : ∀ E, D.coeff E = -v E := fun E => rfl
  refine ⟨D, RationalFunctionsSubmodule.eq_of_stalkSet_eq L.isSaturated
    (WeilDivisor.isSaturated_sheaf _) fun η hη => ?_⟩
  by_cases hΓ : ∃ Γ : WeilDivisorPrime X, Γ.1.genericPoint = η
  · obtain ⟨Γ, rfl⟩ := hΓ
    rw [WeilDivisor.stalkSet_sheaf_genericPoint π hd]
    ext g
    rw [hL Γ.1 g, mem_range_uniformizerUnit_zpow_mul_iff_ordGE,
      Divisor.toWeilDivisor_apply, hD, neg_neg]
  · push Not at hΓ
    have h0 := coheight_eq_zero_of_forall_ne hη hΓ
    obtain ⟨L', hL'⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf π hd
      (Divisor.toWeilDivisor D)
    rw [WeilDivisor.stalkSet_sheaf_of_coeff_eq_zero hL' hη fun Γ h => absurd h (hΓ Γ)]
    obtain ⟨f', hf'⟩ := L.principal_codim_one η hη
    rw [hf']
    ext g
    simp only [Set.mem_range, Units.val_one, one_mul]
    have hsurj := structureStalkToRationalFunctionsStalk_surjective h0
    constructor
    · intro _; exact hsurj g
    · intro _
      obtain ⟨a, ha⟩ := hsurj (((f'⁻¹ : ((rationalFunctionsPresheaf X).stalk η)ˣ) :
        (rationalFunctionsPresheaf X).stalk η) * g)
      exact ⟨a, by rw [ha, ← mul_assoc, Units.mul_inv, one_mul]⟩

end Valuation

/-- **The dualizing sheaf of a smooth open is the canonical sheaf**, given an embedding into a
smooth proper scheme (Stacks, Tag 0EA0). Let `ω` be a dualizing sheaf of `X` of dimension `d` over
a field `k`, and `U ⊆ X` an open on which `X` is smooth over `k`, of residue transcendence degree
`d` at its generic points, which is an open subscheme of a smooth proper `k`-scheme `P`. Then
`ω|_U ≅ ⋀ᵈ Ω_{U/k}`. -/
theorem IsDualizingSheaf.nonempty_restrict_iso_relativeDifferentialForms {k : Type u} [Field k]
    {π : X ⟶ Spec (.of k)} {d : ℕ} {ω : X.Modules} (hω : IsDualizingSheaf π d ω)
    [IsNoetherian X] {U : X.Opens} [Smooth (U.ι ≫ π)]
    (htr : ∀ ξ : U.toScheme, closure {ξ} ∈ irreducibleComponents U.toScheme →
      Stacks.Chow.residueTrdeg (U.ι ≫ π) ξ = (d : Cardinal))
    {P : Scheme.{u}} (ι : U.toScheme ⟶ P) [IsImmersion ι] (g : P ⟶ Spec (.of k)) [Smooth g]
    [IsProper g] (hfac : ι ≫ g = U.ι ≫ π) :
    Nonempty (ω.restrict U.ι ≅ Scheme.Hom.relativeDifferentialForms (U.ι ≫ π) d) := by
  obtain ⟨-, Xbar, j, hj, πbar, hp, hjp, ⟨e⟩⟩ := hω
  haveI := hj
  haveI := hp
  let XF := Stacks.Duality.curveFTS πbar
  let F := Stacks.Duality.curveFTSHom πbar
  haveI : IsSeparated π := by rw [← hjp]; infer_instance
  haveI : LocallyOfFiniteType π := by rw [← hjp]; infer_instance
  haveI : QuasiCompact (U.ι ≫ π) := by rw [← hjp]; infer_instance
  let UF : FTS (Spec (.of k)) := FTS.mk (U.ι ≫ π)
  let jU : UF ⟶ XF := MorphismProperty.Over.homMk (U.ι ≫ j)
    (by change (U.ι ≫ j) ≫ πbar = U.ι ≫ π; rw [Category.assoc, hjp])
  haveI : IsOpenImmersion jU.left := inferInstanceAs (IsOpenImmersion (U.ι ≫ j))
  let c := (Stacks.Duality.properCompactification F).precompOpen jU.left
  have hY : AlgebraicGeometry.IsCohenMacaulay (Spec (.of k)) :=
    Stacks.PurityRamification.isCohenMacaulay_spec k
  have he : (jU ≫ F).left = U.ι ≫ π := by
    rw [← hjp]; exact Category.assoc _ _ _
  have hfac' : ι ≫ g = (jU ≫ F).left := by rw [hfac, he]
  have hsm : ∀ x : UF.left, InfinitesimalLifting.SmoothAt (jU ≫ F).left x := by
    intro x
    have : Smooth (jU ≫ F).left := by
      rw [he]
      exact ‹Smooth (U.ι ≫ π)›
    exact InfinitesimalLifting.smoothAt_of_smooth _ x
  have hK : ∀ x : UF.left, ringKrullDim (UF.left.presheaf.stalk x) ≤ 1 →
      KoszulAt (jU ≫ F).left x := fun x _ =>
    Stacks.Duality.SmoothLocus.koszulAt_of_smoothAt (hsm x)
  have htr' : ∀ ξ : UF.left, closure {ξ} ∈ irreducibleComponents UF.left →
      Stacks.Chow.residueTrdeg (jU ≫ F).left ξ = (d : Cardinal) := by
    rw [he]
    exact htr
  haveI : IsImmersion (show UF.left ⟶ P from ι) := ‹IsImmersion ι›
  haveI : Smooth (show P ⟶ (Stacks.Duality.baseFTS k).left from g) := ‹Smooth g›
  haveI : IsProper (show P ⟶ (Stacks.Duality.baseFTS k).left from g) := ‹IsProper g›
  obtain ⟨φ, hφ⟩ := Stacks.Duality.SmoothLocus.exists_map_exteriorPower_isIso_of_smoothAt
    (jU ≫ F) d hY ι g hfac' hK htr' c
  have hiso : IsIso φ := by
    refine Stacks.AlgebraicGeometry.ReflexiveEquivalence.isIso_of_forall_isIso_stalkMapOfHom φ
      fun x => ?_
    have h := hφ x (hsm x)
    have hb := ConcreteCategory.bijective_of_isIso
      (AlgebraicGeometry.SheafOfModules.stalkMap (Sheaf.toRingCat (Opens.grothendieckTopology
        ↥UF.left.toLocallyRingedSpace.toRingedSpace.carrier)
        UF.left.toLocallyRingedSpace.toRingedSpace.sheaf) x φ)
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hb
  let e2 := Stacks.Duality.ClosedOpenProperFactorization.upperShriekHomologyRestrictIso jU F
    (Stacks.Duality.properCompactification F) (-(d : ℤ))
  let e3 : Stacks.Duality.ClosedOpenProperFactorization.upperShriekHomology F
      (Stacks.Duality.properCompactification F) (-(d : ℤ)) ≅
      @Stacks.Duality.dualizingModuleOverField k _ Xbar πbar hp (d : ℤ) :=
    (@DerivedCategory.homologyFunctor Xbar.Modules _ _
      (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory Xbar) (-(d : ℤ))).mapIso
      ((ObjectProperty.ι _).mapIso (Stacks.Duality.dualizingComplexOverFieldIsoUpperShriek πbar))
  let e4 : (Scheme.Modules.restrictFunctor (U.ι ≫ j)).obj
      (@Stacks.Duality.dualizingModuleOverField k _ Xbar πbar hp (d : ℤ)) ≅ ω.restrict U.ι :=
    (Scheme.Modules.restrictFunctorComp U.ι j).app _ ≪≫
      (Scheme.Modules.restrictFunctor U.ι).mapIso e.symm
  have hrel : Scheme.Hom.relativeDifferentialForms (jU ≫ F).left (d : ℤ) =
      Scheme.Hom.relativeDifferentialForms (U.ι ≫ π) d :=
    congrArg (Scheme.Hom.relativeDifferentialForms · (d : ℤ)) he
  exact ⟨e4.symm ≪≫ (Scheme.Modules.restrictFunctor jU.left).mapIso e3.symm ≪≫ e2.symm ≪≫
    (asIso φ).symm ≪≫ eqToIso hrel⟩

/-- At the generic point of the smooth locus of a variety of dimension `d` over `k`, the residue
field has transcendence degree `d` over `k`. -/
theorem residueTrdeg_smoothLocus_eq {k : Type u} [Field k] {π : X ⟶ Spec (.of k)} [IsIntegral X]
    (hX : IsNormalVariety k π) {d : ℕ} (hdim : topologicalKrullDim X = d)
    (ξ : (smoothLocus π).toScheme)
    (hξ : closure {ξ} ∈ irreducibleComponents (smoothLocus π).toScheme) :
    Stacks.Chow.residueTrdeg ((smoothLocus π).ι ≫ π) ξ = (d : Cardinal) := by
  haveI : LocallyOfFiniteType π := hX.1.toLocallyOfFiniteType
  haveI : Nonempty (smoothLocus π) := ⟨ξ⟩
  haveI : IsIntegral (smoothLocus π).toScheme := isIntegral_of_isOpenImmersion (smoothLocus π).ι
  have hξu : closure {ξ} = Set.univ := irreducibleComponents_val_eq_univ ⟨_, hξ⟩
  have hgen : (smoothLocus π).ι ξ = genericPoint X := by
    refine IsGenericPoint.eq ?_ (genericPoint_spec X)
    show closure {(smoothLocus π).ι ξ} = Set.univ
    refine Set.eq_univ_of_univ_subset ?_
    have hd : Dense ((smoothLocus π : X.Opens) : Set X) := (smoothLocus π).isOpen.dense ⟨_, ξ.2⟩
    rw [← hd.closure_eq]
    refine closure_minimal ?_ isClosed_closure
    intro y hy
    obtain ⟨y', rfl⟩ : ∃ y' : (smoothLocus π).toScheme, (smoothLocus π).ι y' = y := ⟨⟨y, hy⟩, rfl⟩
    have hy' : y' ∈ closure {ξ} := by rw [hξu]; trivial
    have := image_closure_subset_closure_image (f := (smoothLocus π).ι.base)
      (smoothLocus π).ι.continuous ⟨y', hy', rfl⟩
    simpa using this
  rw [Stacks.Chow.residueTrdeg_of_surjective_residueFieldMap_comp (smoothLocus π).ι π ξ
    (ConcreteCategory.bijective_of_isIso ((smoothLocus π).ι.residueFieldMap ξ)).2, hgen]
  set η := genericPoint X
  let K0 := (Spec (.of k)).residueField (π η)
  letI iK0 : Algebra k K0 :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (π η)).hom.toAlgebra
  letI : Algebra K0 (X.residueField η) := (π.residueFieldMap η).hom.toAlgebra
  letI : Algebra k (X.residueField η) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ X.Γevaluation η).hom.toAlgebra
  haveI : IsScalarTower k K0 (X.residueField η) := IsScalarTower.of_algebraMap_eq fun a =>
    (Scheme.Γevaluation_naturality_apply π η ((Scheme.ΓSpecIso (.of k)).inv a)).symm
  have hmax : (π η).asIdeal.IsMaximal := by
    have h : (π η).asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right (π η).isPrime.ne_top
    rw [h]
    exact Ideal.bot_isMaximal
  have hsurj : Function.Surjective (algebraMap k K0) := by
    have h := Scheme.Spec.algebraMap_residueFieldIso_inv (.of k) (π η)
    have : algebraMap k K0 = (CommRingCat.ofHom (algebraMap k (π η).asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of k) (π η)).inv).hom := by
      rw [h]; rfl
    rw [this]
    exact (ConcreteCategory.bijective_of_isIso
      (Scheme.Spec.residueFieldIso (.of k) (π η)).inv).2.comp
      (Ideal.algebraMap_residueField_surjective _)
  have hz : Algebra.trdeg k K0 = 0 := Stacks.Chow.trdeg_zero_of_surjective_algebraMap _ _ hsurj
  have hadd := trdeg_add_eq k K0 (A := X.residueField η)
  rw [hz, zero_add] at hadd
  exact hadd.trans (trdeg_residueField_genericPoint_eq k π hdim)

/-- **The smooth locus of a normal variety embeds in a smooth proper variety** (A1): compactify,
normalize and resolve, the resolution being an isomorphism over the smooth locus. -/
theorem exists_isOpenImmersion_smoothLocus_smooth_isProper {k : Type u} [Field k] [CharZero k]
    {π : X ⟶ Spec (.of k)} [IsIntegral X] (hX : IsNormalVariety k π) {Xbar : Scheme.{u}}
    (j : X ⟶ Xbar) [IsOpenImmersion j] (πbar : Xbar ⟶ Spec (.of k)) [IsProper πbar]
    (hjp : j ≫ πbar = π) :
    ∃ (P : Scheme.{u}) (ι : (smoothLocus π).toScheme ⟶ P) (g : P ⟶ Spec (.of k)),
      IsOpenImmersion ι ∧ Smooth g ∧ IsProper g ∧ ι ≫ g = (smoothLocus π).ι ≫ π := by
  haveI : AlgebraicGeometry.IsVariety k π := hX.1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  haveI : QuasiSeparatedSpace Xbar := quasiSeparatedSpace_of_quasiSeparated πbar
  haveI : QuasiCompact j := quasiCompact_of_compactSpace j
  let Z := j.image
  haveI : IsIntegral Z := j.isIntegral_image
  let ι₀ : X ⟶ Z := j.toImage
  haveI : IsOpenImmersion ι₀ := inferInstance
  let sZ : Z ⟶ Spec (.of k) := j.imageι ≫ πbar
  have hι₀ : ι₀ ≫ sZ = π := by
    simp only [ι₀, sZ, Scheme.Hom.toImage_imageι_assoc, hjp]
  haveI : AlgebraicGeometry.IsVariety k sZ := ⟨⟩
  obtain ⟨Y, g, hYv, hgp, -, hYsm, hiso, -⟩ :=
    MMP.Resolution.exists_isStrongResolution sZ inferInstance
  haveI : IsProper g := hgp.isProper
  haveI := hYv
  have hsmooth : Smooth (g ≫ sZ) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← smoothLocus_eq_smoothLocus]
    exact hYsm
  have hle : smoothLocus π ≤ ι₀ ⁻¹ᵁ smoothLocus sZ := by
    rw [smoothLocus_eq_smoothLocus π, smoothLocus_eq_smoothLocus sZ,
      Scheme.Hom.preimage_smoothLocus_eq]
    have key : ∀ (f g : X ⟶ Spec (.of k)) [LocallyOfFinitePresentation f]
        [LocallyOfFinitePresentation g], f = g → f.smoothLocus ≤ g.smoothLocus := by
      intro f g _ _ h
      subst h
      exact le_rfl
    exact key _ _ hι₀.symm
  let W := smoothLocus sZ
  let r : (smoothLocus π).toScheme ⟶ W.toScheme := ι₀.resLE W (smoothLocus π) hle
  have hr : r ≫ W.ι = (smoothLocus π).ι ≫ ι₀ := Scheme.Hom.resLE_comp_ι _ _
  haveI : IsOpenImmersion (r ≫ W.ι) := by rw [hr]; infer_instance
  haveI : IsOpenImmersion r := IsOpenImmersion.of_comp r W.ι
  haveI := hiso
  refine ⟨Y, r ≫ inv (g ∣_ W) ≫ (g ⁻¹ᵁ W).ι, g ≫ sZ, inferInstance, hsmooth, inferInstance, ?_⟩
  calc (r ≫ inv (g ∣_ W) ≫ (g ⁻¹ᵁ W).ι) ≫ g ≫ sZ
      = r ≫ inv (g ∣_ W) ≫ ((g ⁻¹ᵁ W).ι ≫ g) ≫ sZ := by simp only [Category.assoc]
    _ = r ≫ W.ι ≫ sZ := by
      rw [← morphismRestrict_ι]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    _ = (smoothLocus π).ι ≫ π := by rw [← Category.assoc, hr, Category.assoc, hι₀]

/-- A variety with a dualizing sheaf of dimension `d` has Krull dimension `d`. -/
theorem topologicalKrullDim_eq_of_isDualizingSheaf {k : Type u} [Field k]
    {π : X ⟶ Spec (.of k)} [IsIntegral X] {d : ℕ} {ω : X.Modules}
    (hω : IsDualizingSheaf π d ω) : topologicalKrullDim X = d := by
  rw [← hω.1 Set.univ (by rw [irreducibleComponents_eq_singleton]; rfl)]
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph).symm

/-- **The dualizing sheaf on the smooth locus is the canonical sheaf.** For a normal variety `X`
of dimension `d` over a field of characteristic zero, a dualizing sheaf `ω` of `X` restricts on the
smooth locus `X_sm` to `⋀ᵈ Ω_{X_sm/k}` (Stacks, Tag 0EA0). -/
theorem IsDualizingSheaf.nonempty_restrict_smoothLocus_iso {k : Type u} [Field k] [CharZero k]
    {π : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (hX : IsNormalVariety k π) {d : ℕ} {ω : X.Modules} (hω : IsDualizingSheaf π d ω) :
    Nonempty (ω.restrict (smoothLocus π).ι ≅ canonicalSheaf π d) := by
  obtain ⟨hN, hLFT⟩ := isNoetherian_and_locallyOfFiniteType_of_isDualizingSheaf hω
  obtain ⟨-, Xbar, j, hj, πbar, hp, hjp, -⟩ := id hω
  obtain ⟨P, ι, g, hι, hg, hgp, hfac⟩ :=
    exists_isOpenImmersion_smoothLocus_smooth_isProper hX j πbar hjp
  haveI : Smooth ((smoothLocus π).ι ≫ π) := by
    have h := AlgebraicGeometry.smooth_smoothLocus_ι_comp π
    rwa [← smoothLocus_eq_smoothLocus] at h
  exact hω.nonempty_restrict_iso_relativeDifferentialForms
    (residueTrdeg_smoothLocus_eq hX (topologicalKrullDim_eq_of_isDualizingSheaf hω)) ι g hfac

/-- **The embedded dualizing sheaf of a normal variety is `𝒪_X(K_X)`.** Let `X` be a normal
variety over a field `k` of characteristic zero and `ω ⊆ K(X)` a Weil divisorial subsheaf which
is a dualizing sheaf of `X` of dimension `d`. Then there are a nonzero rational top form `τ` and
a canonical divisor `K` of `X` with `K = div τ` and `ω = 𝒪_X(K)` as subsheaves of `K(X)`. -/
theorem IsDualizingSheaf.exists_eq_sheaf_toWeilDivisor {k : Type u} [Field k] [CharZero k]
    {π : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (hX : IsNormalVariety k π) {d : ℕ} {ω : WeilDivisorialSubsheaf X}
    (hω : IsDualizingSheaf π d ω.toModules) :
    ∃ τ : RationalPluriForms π d 1, τ ≠ 0 ∧ ∃ K : MMP.Mori.Divisor X,
      K.IsCanonicalDivisor π d ∧ (∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm τ = K.coeff Γ) ∧
        ω.toRationalFunctionsSubmodule = (Divisor.toWeilDivisor K).sheaf := by
  obtain ⟨-, hLFT⟩ := isNoetherian_and_locallyOfFiniteType_of_isDualizingSheaf hω
  obtain ⟨K, hK⟩ := WeilDivisorialSubsheaf.exists_eq_sheaf_toWeilDivisor π hω.1 ω
  have hmod : ω.toModules = K.divisorialSheaf := by
    rw [← toModules_sheaf_toWeilDivisor, ← hK]
  obtain ⟨e⟩ := IsDualizingSheaf.nonempty_restrict_smoothLocus_iso hX hω
  have hKc : K.IsCanonicalDivisor π d := ⟨topologicalKrullDim_eq_of_isDualizingSheaf hω, ⟨hmod ▸ e⟩⟩
  obtain ⟨τ, hτ, hτK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hKc
  exact ⟨τ, hτ, K, hKc, hτK, hK⟩

end MMP.Flips
