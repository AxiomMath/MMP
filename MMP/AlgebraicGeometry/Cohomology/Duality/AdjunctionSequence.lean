module

public import MMP.AlgebraicGeometry.MMP.Basic
public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.S2
import MMP.AlgebraicGeometry.Cohomology.SheafExtZero
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization

/-!
# The adjunction sequence, and small contractions to a common base

This file proves two results from Kollár et al., *Flips and abundance*.

**The adjunction sequence (FA 16.4).** Let `X` be a normal Cohen–Macaulay scheme of finite type
and pure dimension `d + 1` over a field `k`, with dualizing sheaf embedded as a Weil divisorial
subsheaf `ω_X ⊆ K(X)`, and let `i : S ⟶ X` be a reduced closed subscheme of pure codimension one
with dualizing sheaf `ω_S`. Write `S = ∑ Γ` for the reduced Weil divisor of its components. Then
the ideal sheaf of `S` is `𝒪_X(-S) ⊆ K(X)`, and there is a map `α : i^*(ω_X(S)) ⟶ ω_S` whose
adjoint `β : ω_X(S) ⟶ i_* ω_S` has kernel exactly `ω_X`; `α` is surjective and an isomorphism at
the generic points of `S`.

**Small contractions (FA 4.12.4).** Let `φ : X ⟶ Z` and `φ⁺ : X⁺ ⟶ Z` be small birational
contractions of normal varieties over `k`. Both are isomorphisms in codimension one, so
`k(X) = k(Z) = k(X⁺)` through `φ^*` and `φ⁺^*`, and `X`, `X⁺` agree in codimension one over `Z`.
Consequently a valuation of `k(X) = k(X⁺)` is an exceptional divisor with nonempty center on `X`
if and only if it is one on `X⁺`, and the induced birational map `g = φ⁺⁻¹ ∘ φ : X ⤏ X⁺` maps the
prime divisors of `X` bijectively onto those of `X⁺`, with `ord_{g_* P} = ord_P` on `k(Z)`.

## Main results

* `MMP.Flips.IsDualizingSheaf.exists_adjunction_exact_sequence`
* `MMP.Flips.exceptional_hasNonemptyCenter_iff_of_isSmall`
* `MMP.Flips.primeDivisorEquivOfModification`: the bijection `P ↦ g_* P` of prime divisors

## Implementation notes

The tensor product `ω_X(S) ⊗ 𝒪_S` is the pullback `i^*(ω_X(S))` along the closed immersion.
The map `α` is pinned by its adjoint `β = i_* α ∘ η`, `η` the unit of `i^* ⊣ i_*`: the kernel
of `β` is `ω_X ⊆ ω_X(S)`, so that `0 → ω_X → ω_X(S) → i_* ω_S → 0` is exact. This determines
`α` up to an automorphism of `ω_S`, the ambiguity of the identification
`ω_S ≅ 𝓔xt¹(𝒪_S, ω_X)` of `MMP.Flips.IsDualizingSheaf.nonempty_iso_ext`. The ideal sheaf `𝓘_S`
is described by its sections: on every open `U`, the image in `K(X)(U)` of the kernel of the
restriction `Γ(X, U) → Γ(S, i⁻¹ U)`. The proof identifies `ω_X(S) ≅ 𝓗om(𝓘_S, ω_X)` by
multiplication, through `𝓘_S = 𝒪_X(-S)` and `𝒪_X(-S)⁻¹ · ω_X = ω_X(S)` (equal stalks in
codimension `≤ 1`), and reads off `i_* ω_S` as the cokernel of `ω_X ⊆ ω_X(S)`.

The identification `k(X) = k(X⁺)` over `k(Z)` is through the function-field maps `φ^*` and
`φ⁺^*`: a valuation `v` of `k(X)` and a valuation `v⁺` of `k(X⁺)` are the same divisor when
`v ∘ φ^* = v⁺ ∘ φ⁺^*` on `k(Z)`. The map `g` is any modification of `φ` into `φ⁺`
(`MMP.Flips.IsModificationOf`), which is unique as a rational map; the push-forward of prime
divisors is `MMP.Mori.RationalMap.transformPrimeDivisor`. Both halves rest on transporting a
divisor `(Y, f, E)` over `X` to the divisor `(Y, φ ∘ f, E)` over `Z`, realised over `φ⁺` with
the same valuation and the same centre on `Z`; smallness then compares codimensions of centres.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.12.4, 16.4
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open scoped WithZero

namespace MMP.Flips

open MMP.Mori RationalFunctionsSubmodule

/-! ### The adjunction sequence -/

/-- A section of `𝒪_X` whose restriction to `S` vanishes is a non-unit in the local ring of `X`
at every point of `S`. -/
private theorem not_isUnit_germ_of_app_eq_zero {X S : Scheme.{u}} (i : S ⟶ X) {U : X.Opens}
    {f : Γ(X, U)} (hf : i.app U f = 0) {x : X} (hx : x ∈ U) {z : S} (hxz : x = i.base z) :
    ¬ IsUnit (X.presheaf.germ U x hx f) := by
  subst hxz
  intro h
  have := h.map (i.stalkMap z).hom
  rw [Scheme.Hom.germ_stalkMap_apply, hf, map_zero] at this
  exact not_isUnit_zero this

open scoped Classical in
/-- A section of `𝒪_X` vanishing on `S` is a section of `𝒪_X(-S)`. -/
private theorem algebraMap_mem_sheaf_neg {X S : Scheme.{u}} (i : S ⟶ X)
    (DS : MMP.Flips.WeilDivisor X)
    (hDS : ∀ Γ : WeilDivisorPrime X, DS Γ =
      if ∃ Z : irreducibleComponents S, Γ.1.genericPoint = i.base (componentGenericPoint S Z)
      then 1 else 0) {U : X.Opens} {f : Γ(X, U)} (hf : i.app U f = 0) :
    Algebra.linearMap Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) f ∈
      (-DS).sheaf.sections U := by
  intro x hx
  have hg : (rationalFunctionsPresheaf X).germ U x hx
      (Algebra.linearMap Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) f) =
      (structureStalkToRationalFunctionsStalk X x).hom (X.presheaf.germ U x hx f) :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (toRationalFunctionsPresheaf X) f).symm
  rw [hg]
  refine ⟨fun Γ h t ht => ?_, fun _ _ => ⟨_, rfl⟩⟩
  subst h
  rw [Finsupp.neg_apply, hDS Γ]
  split_ifs with hZ
  · obtain ⟨Z, hZ⟩ := hZ
    obtain ⟨_, hdvr⟩ := Γ.2
    have hm : X.presheaf.germ U _ hx f ∈ Ideal.span {t} := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (not_isUnit_germ_of_app_eq_zero i hf hx hZ)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hm
    refine ⟨a, ?_⟩
    rw [← ha, map_mul]
    simp only [Int.reduceNeg, neg_neg, Int.toNat_one, pow_one, pow_zero, one_mul]
    rw [show (-1 : ℤ).toNat = 0 from rfl, pow_zero, one_mul, mul_comm]
  · exact ⟨X.presheaf.germ U _ hx f, by simp⟩

/-- The sheaf of an anti-effective Weil divisor lies in `sat(𝒪_X)`. -/
private theorem sheaf_le_saturation_unit_of_nonpos {X : Scheme.{u}} {D : MMP.Flips.WeilDivisor X}
    (hD : ∀ Γ, D Γ ≤ 0) {U : X.Opens} {s : ToType ((rationalFunctionsPresheaf X).obj (op U))}
    (hs : s ∈ D.sheaf.sections U) :
    s ∈ (RationalFunctionsSubmodule.unit X).saturation.sections U := by
  intro η hη hc
  have h := hs η hη
  rw [RationalFunctionsSubmodule.stalkSet_unit]
  by_cases hΓ : ∃ Γ : WeilDivisorPrime X, Γ.1.genericPoint = η
  · obtain ⟨Γ, rfl⟩ := hΓ
    obtain ⟨a, ha⟩ := h.1 Γ rfl Γ.uniformizer Γ.irreducible_uniformizer
    rw [Int.toNat_eq_zero.mpr (hD Γ), pow_zero, one_mul] at ha
    exact ⟨Γ.uniformizer ^ (-D Γ).toNat * a, by rw [ha, map_mul, map_pow]⟩
  · push Not at hΓ
    exact h.2 hc hΓ

/-- On a normal locally Noetherian scheme, `𝒪_{X,x} → K(X)_x` is injective. -/
private theorem injective_structureStalkToRationalFunctionsStalk {X : Scheme.{u}} [IsNormal X]
    [IsLocallyNoetherian X] (x : X) :
    Function.Injective (structureStalkToRationalFunctionsStalk X x).hom := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨V, hxV, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
  have h1 : (structureStalkToRationalFunctionsStalk X x).hom (X.presheaf.germ V x hxV r) =
      (rationalFunctionsPresheaf X).germ V x hxV ((toRationalFunctionsPresheaf X).app (op V) r) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV (toRationalFunctionsPresheaf X) r
  rw [h1] at ha
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq (rationalFunctionsPresheaf X) x hxV hxV _
    0 (ha.trans (map_zero _).symm)
  rw [map_zero] at hW
  have hW' : (toRationalFunctionsPresheaf X).app (op W) (X.presheaf.map iU.op r) = 0 := by
    rwa [toRationalFunctionsPresheaf_app_map]
  obtain ⟨Z, hZ, hxZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
  let Z' : irreducibleComponents X := ⟨Z, hZ⟩
  have hηW : componentGenericPoint X Z' ∈ W :=
    ((isGenericPoint_componentGenericPoint X Z').specializes (hxZ rfl)).mem_open W.isOpen hxW
  have h2 : X.presheaf.germ W _ hηW (X.presheaf.map iU.op r) = 0 := congrFun hW' ⟨Z', hηW⟩
  rw [← X.presheaf.germ_res_apply iU x hxW r]
  apply stalkToRationalFunctions_injective (Z := Z') (hxZ rfl)
  rw [map_zero, ← h2]
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

/-- A point of coheight `≤ 1` does not have a local ring of dimension `≥ 2`. -/
private lemma not_two_le_ringKrullDim_of_coheight_le_one {X : Scheme.{u}} {η : X}
    (hη : Order.coheight η ≤ 1) : ¬ 2 ≤ ringKrullDim (X.presheaf.stalk η) := by
  rw [ringKrullDim_stalk_eq_coheight]
  intro h
  have h' : (2 : ℕ∞) ≤ Order.coheight η := WithBot.coe_le_coe.mp h
  exact absurd (h'.trans hη) (by decide)

/-- If every point of `V ∖ W` has a local ring of dimension `≥ 2`, then every generic point of
an irreducible component lying in `V` lies in `W`. -/
private lemma mem_of_two_le_ringKrullDim {X : Scheme.{u}} {V W : X.Opens}
    (hZ : ∀ z ∈ V, z ∉ W → 2 ≤ ringKrullDim (X.presheaf.stalk z))
    (Z : irreducibleComponents X) (hZV : componentGenericPoint X Z ∈ V) :
    componentGenericPoint X Z ∈ W := by
  by_contra hn
  exact not_two_le_ringKrullDim_of_coheight_le_one (coheight_componentGenericPoint_le_one Z)
    (hZ _ hZV hn)

/-- A locally Noetherian scheme with Cohen–Macaulay local rings satisfies `S₂`. -/
private theorem satisfiesS2_of_isCohenMacaulayLocalRing {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hCM : ∀ x : X, IsCohenMacaulayLocalRing (X.presheaf.stalk x)) : SatisfiesS2 X := by
  intro x
  have hS := hCM x
  obtain ⟨ss, hmem, hreg, hlen⟩ := exists_isRegular_length_eq_depth_of_cohenMacaulay hS
  refine ⟨ss, hmem, hreg, min_le_of_right_le (le_of_eq ?_)⟩
  have hsd := Module.supportDim_self_eq_ringKrullDim (X.presheaf.stalk x)
  rw [Module.supportDim] at hsd
  unfold IsCohenMacaulayLocalRing IsCohenMacaulayModule at hS
  rw [← hsd, ← hS, ← hlen]
  rfl

/-- A section of `𝒪_X ⊆ K(X)` over `V` is the image of a section of `𝒪_X` over `V`. -/
private theorem exists_toRationalFunctionsPresheaf_app_eq_of_mem_unit' {X : Scheme.{u}}
    [IsNormal X] [IsLocallyNoetherian X] {V : X.Opens}
    {t : ToType ((rationalFunctionsPresheaf X).obj (op V))}
    (ht : t ∈ (RationalFunctionsSubmodule.unit X).sections V) :
    ∃ r : Γ(X, V), (toRationalFunctionsPresheaf X).app (op V) r = t := by
  choose W i hxW hW using fun x : V => ht x.1 x.2
  have hr : ∀ x : V, ∃ r : Γ(X, W x), (toRationalFunctionsPresheaf X).app (op (W x)) r =
      (rationalFunctionsPresheaf X).map (i x).op t := fun x => Submodule.mem_one.mp (hW x)
  choose r hr using hr
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 W r := by
    intro x y
    apply toRationalFunctionsPresheaf_app_injective
    show (toRationalFunctionsPresheaf X).app (op (W x ⊓ W y))
        (X.presheaf.map (Opens.infLELeft (W x) (W y)).op (r x)) =
      (toRationalFunctionsPresheaf X).app (op (W x ⊓ W y))
        (X.presheaf.map (Opens.infLERight (W x) (W y)).op (r y))
    rw [toRationalFunctionsPresheaf_app_map, toRationalFunctionsPresheaf_app_map, hr x, hr y,
      rationalFunctionsPresheaf_map_map _ _ (Opens.infLELeft (W x) (W y) ≫ i x),
      rationalFunctionsPresheaf_map_map _ _ (Opens.infLELeft (W x) (W y) ≫ i x)]
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf W V i
    (fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hxW ⟨z, hz⟩⟩) r hcompat
  refine ⟨g, ?_⟩
  funext Z
  have hZ : componentGenericPoint X Z.1 ∈ V := Z.2
  have hx := hg ⟨_, hZ⟩
  have h2 : (rationalFunctionsPresheaf X).map (i ⟨_, hZ⟩).op
      ((toRationalFunctionsPresheaf X).app (op V) g) =
      (rationalFunctionsPresheaf X).map (i ⟨_, hZ⟩).op t := by
    rw [← toRationalFunctionsPresheaf_app_map (i ⟨_, hZ⟩) g]
    exact (congrArg _ hx).trans (hr _)
  exact congrFun h2 ⟨Z.1, hxW ⟨_, hZ⟩⟩

/-- On a normal locally Noetherian `S₂` scheme, a section of `sat(𝒪_X)` comes from `𝒪_X`
(FA 16.3.2, without quasi-compactness). -/
private theorem exists_algebraMap_eq_of_mem_saturation_unit {X : Scheme.{u}} [IsNormal X]
    [IsLocallyNoetherian X] (hS2 : SatisfiesS2 X) {V : X.Opens}
    {s : ToType ((rationalFunctionsPresheaf X).obj (op V))}
    (hs : s ∈ (RationalFunctionsSubmodule.unit X).saturation.sections V) :
    ∃ f : Γ(X, V), Algebra.linearMap Γ(X, V) ((rationalFunctionsPresheaf X).obj (op V)) f = s := by
  -- the open locus of `V` where `s` lies in `𝒪_X`
  let U : X.Opens := ⨆ (W : X.Opens) (i : W ⟶ V)
    (_ : (rationalFunctionsPresheaf X).map i.op s ∈
      (RationalFunctionsSubmodule.unit X).sections W), W
  have hUV : U ≤ V := iSup₂_le fun W i => iSup_le fun _ => i.le
  have hsU : (rationalFunctionsPresheaf X).map (homOfLE hUV).op s ∈
      (RationalFunctionsSubmodule.unit X).sections U := by
    refine (RationalFunctionsSubmodule.unit X).mem_of_locally fun x hx => ?_
    obtain ⟨W, hW⟩ := Opens.mem_iSup.mp hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hW
    obtain ⟨hm, hxW⟩ := Opens.mem_iSup.mp hi
    exact ⟨W, homOfLE (le_iSup₂_of_le W i (le_iSup (fun _ => W) hm)), hxW, hm⟩
  have hcod : ∀ z ∈ V, z ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk z) := by
    intro z hzV hzU
    rw [ringKrullDim_stalk_eq_coheight]
    by_contra hlt
    have hc : Order.coheight z ≤ 1 := by
      by_contra h1
      exact hlt (WithBot.coe_le_coe.mpr
        (show (2 : ℕ∞) ≤ Order.coheight z from Order.add_one_le_of_lt (not_le.mp h1)))
    obtain ⟨W, i, hzW, hm⟩ :=
      ((RationalFunctionsSubmodule.unit X).germ_mem_stalkSet_iff hzV s).mp (hs z hzV hc)
    exact hzU (Opens.mem_iSup.mpr ⟨W, Opens.mem_iSup.mpr ⟨i, Opens.mem_iSup.mpr ⟨hm, hzW⟩⟩⟩)
  obtain ⟨g, hg⟩ := exists_toRationalFunctionsPresheaf_app_eq_of_mem_unit' hsU
  obtain ⟨t, rfl⟩ := (bijective_presheaf_map_of_satisfiesS2 hS2 hUV hcod).2 g
  have hgen := fun Z hZV => mem_of_two_le_ringKrullDim (V := V) (W := U) hcod Z hZV
  refine ⟨t, ?_⟩
  funext Z
  have := congrFun hg ⟨Z.1, hgen Z.1 Z.2⟩
  rwa [toRationalFunctionsPresheaf_app_map] at this

/-- A function in `𝒪_X(D)` with `D` of coefficient `-1` along `Γ` is a non-unit at `Γ`. -/
private theorem not_isUnit_germ_of_mem_sheaf {X : Scheme.{u}} [IsNormal X]
    [IsLocallyNoetherian X] {D : MMP.Flips.WeilDivisor X} {U : X.Opens} {f : Γ(X, U)}
    (hf : Algebra.linearMap Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) f ∈
      D.sheaf.sections U)
    (Γ : WeilDivisorPrime X) (hΓ : D Γ = -1) {x : X} (hgx : Γ.1.genericPoint = x) (hx : x ∈ U) :
    ¬ IsUnit (X.presheaf.germ U x hx f) := by
  subst hgx
  intro hu
  obtain ⟨a, ha⟩ := (hf _ hx).1 Γ rfl Γ.uniformizer Γ.irreducible_uniformizer
  have hg : (rationalFunctionsPresheaf X).germ U Γ.1.genericPoint hx
      (Algebra.linearMap Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) f) =
      (structureStalkToRationalFunctionsStalk X _).hom (X.presheaf.germ U _ hx f) :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U _ hx (toRationalFunctionsPresheaf X) f).symm
  rw [hg, hΓ, show (-1 : ℤ).toNat = 0 from rfl, show (-(-1) : ℤ).toNat = 1 from rfl, pow_zero,
    one_mul, pow_one, ← map_mul] at ha
  have := injective_structureStalkToRationalFunctionsStalk _ ha
  rw [this] at hu
  exact Γ.irreducible_uniformizer.not_isUnit (isUnit_of_mul_isUnit_left hu)

open scoped Classical in
/-- A function in `𝒪_X(-S)` vanishes on the reduced subscheme `S`. -/
private theorem app_eq_zero_of_mem_sheaf_neg {X S : Scheme.{u}} [IsNormal X]
    [IsLocallyNoetherian X] (i : S ⟶ X) [IsReduced S]
    (hcodim : ∀ Z : irreducibleComponents S,
      Order.coheight (i.base (componentGenericPoint S Z)) = 1)
    (DS : MMP.Flips.WeilDivisor X)
    (hDS : ∀ Γ : WeilDivisorPrime X, DS Γ =
      if ∃ Z : irreducibleComponents S, Γ.1.genericPoint = i.base (componentGenericPoint S Z)
      then 1 else 0) {U : X.Opens} {f : Γ(X, U)}
    (hf : Algebra.linearMap Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) f ∈
      (-DS).sheaf.sections U) :
    i.app U f = 0 := by
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro y hy
  exfalso
  obtain ⟨Z, hZ, hyZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible {y} isIrreducible_singleton
  let Z' : irreducibleComponents S := ⟨Z, hZ⟩
  have hη := ((isGenericPoint_componentGenericPoint S Z').specializes (hyZ rfl)).mem_open
    (S.basicOpen _).isOpen hy
  have hηU : componentGenericPoint S Z' ∈ i ⁻¹ᵁ U := S.basicOpen_le _ hη
  have hη' := (Scheme.mem_basicOpen _ _ _ hηU).mp hη
  have hη'' : IsUnit ((i.stalkMap _).hom (X.presheaf.germ U _ hηU f)) :=
    (congrArg IsUnit (Scheme.Hom.germ_stalkMap_apply i U _ hηU f)).mpr hη'
  let Γ : WeilDivisorPrime X := ⟨PrimeDivisor.ofCoheightOne _ (hcodim Z'), inferInstance,
    MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing _⟩
  have hgp : Γ.1.genericPoint = i.base (componentGenericPoint S Z') :=
    PrimeDivisor.genericPoint_ofCoheightOne _ (hcodim Z')
  have hΓ : (-DS) Γ = -1 := by rw [Finsupp.neg_apply, hDS, if_pos ⟨Z', hgp⟩]
  exact not_isUnit_germ_of_mem_sheaf hf Γ hΓ hgp hηU (isUnit_of_map_unit _ _ hη'')

open scoped Classical in
/-- `𝓘_S = 𝒪_X(-S)`: sections of `𝒪_X(-S)` are the images of functions vanishing on `S`. -/
private theorem idealSheaf_eq {X S : Scheme.{u}} [IsNormal X] [IsLocallyNoetherian X]
    (hCM : ∀ x : X, IsCohenMacaulayLocalRing (X.presheaf.stalk x))
    (i : S ⟶ X) [IsReduced S]
    (hcodim : ∀ Z : irreducibleComponents S,
      Order.coheight (i.base (componentGenericPoint S Z)) = 1)
    (DS : MMP.Flips.WeilDivisor X)
    (hDS : ∀ Γ : WeilDivisorPrime X, DS Γ =
      if ∃ Z : irreducibleComponents S, Γ.1.genericPoint = i.base (componentGenericPoint S Z)
      then 1 else 0) (U : X.Opens) :
    (-DS).sheaf.sections U =
      Submodule.map (Algebra.linearMap Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)))
        (RingHom.ker (i.app U).hom) := by
  refine le_antisymm (fun s hs => ?_) (Submodule.map_le_iff_le_comap.mpr
    fun f hf => algebraMap_mem_sheaf_neg i DS hDS hf)
  have hnonpos : ∀ Γ, (-DS) Γ ≤ 0 := fun Γ => by
    rw [Finsupp.neg_apply, hDS Γ]; split_ifs <;> decide
  obtain ⟨f, rfl⟩ := exists_algebraMap_eq_of_mem_saturation_unit
    (satisfiesS2_of_isCohenMacaulayLocalRing hCM) (sheaf_le_saturation_unit_of_nonpos hnonpos hs)
  exact ⟨f, app_eq_zero_of_mem_sheaf_neg i hcodim DS hDS hs, rfl⟩

/-- The inclusion `𝓕 ⟶ 𝓖` of `𝒪_X`-submodules of `K(X)` with `𝓕 ⊆ 𝓖`. -/
private noncomputable def inclusionHom {X : Scheme.{u}} {F G : RationalFunctionsSubmodule X}
    (h : ∀ U, F.sections U ≤ G.sections U) : F.toModules ⟶ G.toModules :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (Submodule.inclusion (h U.unop)).toAddMonoidHom
      naturality := fun _ _ _ => rfl }
    (fun _ _ _ => rfl)⟩

private theorem mono_inclusionHom {X : Scheme.{u}} {F G : RationalFunctionsSubmodule X}
    (h : ∀ U, F.sections U ≤ G.sections U) : Mono (inclusionHom h) := by
  refine ⟨fun g₁ g₂ hg => ?_⟩
  ext U x
  exact Subtype.ext (congrArg (fun g => ((g.val.app (op U) x : G.sections U)).1) hg)

/-- A section of `𝓖` dies in `𝓖/𝓕` exactly when it is a section of `𝓕`. -/
private theorem cokernel_π_app_eq_zero_iff {X : Scheme.{u}} {F G : RationalFunctionsSubmodule X}
    (h : ∀ U, F.sections U ≤ G.sections U) (U : X.Opens) (s : G.sections U) :
    (cokernel.π (inclusionHom h)).val.app (op U) s = 0 ↔ s.1 ∈ F.sections U := by
  let Φ := SheafOfModules.forget X.ringCatSheaf ⋙ PresheafOfModules.evaluation X.ringCatSheaf.obj
    (op U)
  have : PreservesFiniteLimits Φ := by
    have : PreservesFiniteLimits (SheafOfModules.forget X.ringCatSheaf) := inferInstance
    have : PreservesFiniteLimits (PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)) :=
      inferInstance
    exact comp_preservesFiniteLimits _ _
  have hpl : PreservesLimitsOfShape WalkingParallelPair Φ :=
    PreservesFiniteLimits.preservesFiniteLimits _
  have hz : Φ.PreservesZeroMorphisms := ⟨fun _ _ => by ext; rfl⟩
  have hex := @ShortComplex.Exact.map_of_mono_of_preservesKernel _ _ _ _ _ _ _ _
    (ShortComplex.exact_cokernel (inclusionHom h)) Φ hz inferInstance (mono_inclusionHom h)
    hpl.preservesLimit
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  have hs := SetLike.ext_iff.mp hex s
  change _ ↔ (ModuleCat.Hom.hom ((cokernel.π (inclusionHom h)).val.app (op U))) s = 0 at hs
  rw [← hs]
  refine ⟨?_, fun hm => ⟨⟨s.1, hm⟩, rfl⟩⟩
  rintro ⟨t, rfl⟩
  exact t.2

/-- `1 ∈ 𝒪(D)` for an effective Weil divisor `D`. -/
private theorem one_mem_sheaf {X : Scheme.{u}} (D : MMP.Flips.WeilDivisor X) (hD : 0 ≤ D)
    (U : X.Opens) :
    (1 : ToType ((rationalFunctionsPresheaf X).obj (op U))) ∈ D.sheaf.sections U := by
  intro x hx
  rw [map_one]
  refine ⟨fun Γ hΓ t _ => ⟨(hΓ ▸ t) ^ (D Γ).toNat, ?_⟩, fun _ _ => ⟨1, map_one _⟩⟩
  rw [Int.toNat_eq_zero.mpr (neg_nonpos.mpr (hD Γ)), pow_zero, one_mul, mul_one, map_pow]

/-- `𝓛 ⊆ 𝓛(D)` for an effective Weil divisor `D`. -/
private theorem sections_le_twist {X : Scheme.{u}} (L : WeilDivisorialSubsheaf X)
    (D : MMP.Flips.WeilDivisor X) (hD : 0 ≤ D) (U : X.Opens) :
    L.sections U ≤ (L.twist D).sections U := by
  intro s hs
  refine sections_le_saturation _ U (mem_localClosure_of_mem ?_)
  rw [← mul_one s]
  exact Submodule.mul_mem_mul hs (one_mem_sheaf D hD U)

/-- Along a closed immersion, the adjoint of an epimorphism `F ⟶ i_* G` is an epimorphism. -/
private theorem epi_homEquiv_symm_of_epi {X S : Scheme.{u}} (i : S ⟶ X) [IsClosedImmersion i]
    {F : X.Modules} {G : S.Modules} (β : F ⟶ (Scheme.Modules.pushforward i).obj G) [Epi β] :
    Epi (((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm β) := by
  set α := ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm β
  have hβ : β = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F ≫
      (Scheme.Modules.pushforward i).map α :=
    (Equiv.apply_symm_apply _ β).symm.trans (Adjunction.homEquiv_unit _ _ _ _)
  have : Epi ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F ≫
      (Scheme.Modules.pushforward i).map α) := hβ ▸ inferInstance
  have : Epi ((Scheme.Modules.pushforward i).map α) :=
    epi_of_epi ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F) _
  exact (Scheme.Modules.pushforward i).epi_of_epi_map this

/-- The divisor of a reduced subscheme is effective. -/
private theorem nonneg_of_eq_ite {X S : Scheme.{u}} (i : S ⟶ X) (DS : MMP.Flips.WeilDivisor X)
    [∀ Γ : WeilDivisorPrime X, Decidable
      (∃ Z : irreducibleComponents S, Γ.1.genericPoint = i.base (componentGenericPoint S Z))]
    (hDS : ∀ Γ : WeilDivisorPrime X, DS Γ =
      if ∃ Z : irreducibleComponents S, Γ.1.genericPoint = i.base (componentGenericPoint S Z)
      then 1 else 0) : 0 ≤ DS := by
  intro Γ
  rw [hDS Γ]
  split_ifs <;> simp

/-- `𝒪(D)` is a Weil divisorial subsheaf, generated at every point `η` of codimension `≤ 1` by
`∏_Γ (t_Γ at η)^{-n_Γ}`. -/
theorem exists_weilDivisorialSubsheaf_sheaf_isGeneratedAt_prod {k : Type u} [Field k]
    {X : Scheme.{u}} [IsReduced X] [IsNoetherian X]
    (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d) (D : MMP.Flips.WeilDivisor X) :
    ∃ L : WeilDivisorialSubsheaf X, L.toRationalFunctionsSubmodule = D.sheaf ∧
      ∀ η : X, Order.coheight η ≤ 1 →
        L.IsGeneratedAt η (∏ Γ ∈ D.support, Γ.localGenerator η ^ (-D Γ)) := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  obtain ⟨G, hG⟩ := exists_isWShGroup π hd
  choose M hM using fun Γ => WeilDivisorPrime.exists_weilDivisorialSubsheaf_isGeneratedAt π hd Γ
  set N := ∏ Γ ∈ D.support, M Γ ^ (-D Γ)
  have hN : ∀ η : X, Order.coheight η ≤ 1 →
      N.IsGeneratedAt η (∏ Γ ∈ D.support, Γ.localGenerator η ^ (-D Γ)) :=
    fun η hη => hG.isGeneratedAt_prod _ _ hη _ fun Γ _ =>
      hG.isGeneratedAt_zpow hη (hM Γ η hη) _
  refine ⟨N, ?_, hN⟩
  have hcond : ∀ η : X, Order.coheight η ≤ 1 → ∀ g,
      D.StalkCondition η g ↔ g ∈ N.stalkSet η := by
    intro η hη g
    rw [hN η hη]
    by_cases h : ∃ Γ : WeilDivisorPrime X, Γ.1.genericPoint = η
    · obtain ⟨Γ, rfl⟩ := h
      rw [D.stalkCondition_genericPoint_iff Γ, Finset.prod_eq_single Γ
        (fun Γ' _ hne => by
          rw [Γ'.localGenerator_of_ne fun e => hne (WeilDivisorPrime.genericPoint_injective e),
            one_zpow])
        (fun hΓ => by rw [Finsupp.notMem_support_iff.mp hΓ]; simp), Γ.localGenerator_self]
    · push Not at h
      rw [D.stalkCondition_iff_of_forall_ne hη h, Finset.prod_eq_one fun Γ _ => by
        rw [Γ.localGenerator_of_ne (h Γ), one_zpow]]
      simp
  rw [show N.toRationalFunctionsSubmodule = N.saturation from N.isSaturated]
  ext V s
  rw [mem_saturation_iff]
  change _ ↔ ∀ (x : X) (hx : x ∈ V), D.StalkCondition x _
  refine ⟨fun h x hx => ?_, fun h η hη hc => (hcond η hc _).mp (h η hη)⟩
  by_cases hc : Order.coheight x ≤ 1
  · exact (hcond x hc _).mpr (h x hx hc)
  · exact D.stalkCondition_of_not_coheight_le_one hc _

/-- `𝒪(D)` is a Weil divisorial subsheaf, generated at the generic point of each prime divisor
`Γ` by `t_Γ^{-n_Γ}`. -/
theorem exists_weilDivisorialSubsheaf_sheaf_isGeneratedAt {k : Type u} [Field k]
    {X : Scheme.{u}} [IsReduced X] [IsNoetherian X]
    (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d) (D : MMP.Flips.WeilDivisor X) :
    ∃ L : WeilDivisorialSubsheaf X, L.toRationalFunctionsSubmodule = D.sheaf ∧
      ∀ Γ : WeilDivisorPrime X, L.IsGeneratedAt Γ.1.genericPoint (Γ.uniformizerUnit ^ (-D Γ)) := by
  obtain ⟨L, hL, hgen⟩ := exists_weilDivisorialSubsheaf_sheaf_isGeneratedAt_prod π hd D
  refine ⟨L, hL, fun Γ => ?_⟩
  have := hgen _ (MMP.Mori.PrimeDivisor.coheight_genericPoint Γ.1).le
  have key : (∏ i ∈ D.support, i.localGenerator Γ.1.genericPoint ^ (-D i)) =
      Γ.uniformizerUnit ^ (-D Γ) := by
    by_cases hs : Γ ∈ D.support
    · rw [Finset.prod_eq_single Γ
        (fun Γ' _ hne => by
          rw [Γ'.localGenerator_of_ne fun e => hne (WeilDivisorPrime.genericPoint_injective e),
            one_zpow])
        (fun hΓ => absurd hs hΓ), Γ.localGenerator_self]
    · rw [Finset.prod_eq_one fun Γ' hΓ' => by
        rw [Γ'.localGenerator_of_ne fun e => by
          obtain rfl := WeilDivisorPrime.genericPoint_injective e; exact hs hΓ', one_zpow],
        Finsupp.notMem_support_iff.mp hs, neg_zero, zpow_zero]
  rwa [key] at this

/-- At the generic point `η` of a component `Γ` of `S`, a section of `ω_X ⊆ ω_X(S)` is
`t_Γ c` times a fixed section of `ω_X(S)`, for a non-unit `c ∈ 𝒪_{X,η}`. -/
private theorem exists_twist_germ {X : Scheme.{u}} {k : Type u} [Field k] {π : X ⟶ Spec (.of k)}
    {d : ℕ} [IsLocallyNoetherian X] [IsNormal X]
    (ω : WeilDivisorialSubsheaf X) (hω : IsDualizingSheaf π (d + 1) ω.toModules)
    (DS : MMP.Flips.WeilDivisor X) (Γ : WeilDivisorPrime X) {η : X}
    (hΓη : Γ.1.genericPoint = η) (hΓ : DS Γ = 1) :
    ∃ (V₀ : X.Opens) (h₀ : η ∈ V₀) (s₀ : (ω.twist DS).sections V₀),
      ∀ (V : X.Opens) (hV : η ∈ V) (s : ToType ((rationalFunctionsPresheaf X).obj (op V))),
        s ∈ ω.sections V → ∃ c : X.presheaf.stalk η, ¬ IsUnit c ∧
          (rationalFunctionsPresheaf X).germ V η hV s =
            (structureStalkToRationalFunctionsStalk X η).hom c *
              (rationalFunctionsPresheaf X).germ V₀ η h₀ s₀.1 := by
  subst hΓη
  obtain ⟨hXN, hπ⟩ := isNoetherian_and_locallyOfFiniteType_of_isDualizingSheaf hω
  have : CompactSpace X := IsNoetherian.toCompactSpace
  have hη := (MMP.Mori.PrimeDivisor.coheight_genericPoint Γ.1).le
  obtain ⟨L, hL, hLgen⟩ := exists_weilDivisorialSubsheaf_sheaf_isGeneratedAt π hω.1 DS
  obtain ⟨f, hf⟩ := ω.principal_codim_one _ hη
  have htw := (WeilDivisorialSubsheaf.stalkSet_mul_inv_unit ω L _ hη f _ hf (hLgen Γ)).1
  have hmem : ((f * Γ.uniformizerUnit ^ (-DS Γ) : ((rationalFunctionsPresheaf X).stalk
      Γ.1.genericPoint)ˣ) : (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) ∈
      (ω.twist DS).stalkSet Γ.1.genericPoint := by
    change _ ∈ (ω.toRationalFunctionsSubmodule.mul DS.sheaf).stalkSet _
    rw [← hL]
    change _ ∈ (ω.mul L).stalkSet _
    rw [htw]
    exact ⟨1, by beta_reduce; rw [map_one, mul_one]⟩
  obtain ⟨V₀, h₀, s₀, hs₀, hgerm₀⟩ := hmem
  refine ⟨V₀, h₀, ⟨s₀, hs₀⟩, fun V hV s hs => ?_⟩
  have hs' : (rationalFunctionsPresheaf X).germ V _ hV s ∈ ω.stalkSet Γ.1.genericPoint :=
    ⟨V, hV, s, hs, rfl⟩
  rw [hf] at hs'
  obtain ⟨a, ha⟩ := hs'
  refine ⟨Γ.uniformizer * a, fun hu => Γ.irreducible_uniformizer.not_isUnit
    (isUnit_of_mul_isUnit_left hu), ?_⟩
  change _ = (structureStalkToRationalFunctionsStalk X _).hom (Γ.uniformizer * a) *
    (rationalFunctionsPresheaf X).germ V₀ _ h₀ s₀
  rw [hgerm₀, ← ha, map_mul, hΓ]
  have hτ : ((Γ.uniformizerUnit : ((rationalFunctionsPresheaf X).stalk Γ.1.genericPoint)ˣ) :
      (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) =
      (structureStalkToRationalFunctionsStalk X _).hom Γ.uniformizer := rfl
  have hτi := Units.mul_inv Γ.uniformizerUnit
  rw [hτ] at hτi
  simp only [Units.val_mul, zpow_neg, zpow_one]
  linear_combination (-((f : (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) *
    (structureStalkToRationalFunctionsStalk X _).hom a)) * hτi

/-- At the generic point `ξ` of a component of `S`, the image of a section of `ω_X ⊆ ω_X(S)`
in `𝒪_{S,ξ} ⊗ ω_X(S)_{i(ξ)}` vanishes. -/
private theorem one_tmul_germ_eq_zero {X S : Scheme.{u}} {k : Type u} [Field k]
    {π : X ⟶ Spec (.of k)} {d : ℕ} [IsLocallyNoetherian X] [IsNormal X]
    (ω : WeilDivisorialSubsheaf X) (hω : IsDualizingSheaf π (d + 1) ω.toModules)
    (i : S ⟶ X) [IsClosedImmersion i] [IsReduced S] (Z : irreducibleComponents S)
    (DS : MMP.Flips.WeilDivisor X) (Γ : WeilDivisorPrime X)
    (hΓη : Γ.1.genericPoint = i.base (componentGenericPoint S Z)) (hΓ : DS Γ = 1)
    (V : X.Opens) (hV : i.base (componentGenericPoint S Z) ∈ V) (s : (ω.twist DS).sections V)
    (hs : s.1 ∈ ω.sections V) :
    letI := (i.stalkMap (componentGenericPoint S Z)).hom.toAlgebra
    (1 : S.presheaf.stalk (componentGenericPoint S Z)) ⊗ₜ[X.presheaf.stalk
      (i.base (componentGenericPoint S Z))]
      (TopCat.Presheaf.germ (C := Ab.{u}) (ω.twist DS).toModules.val.presheaf V _ hV s) = 0 := by
  letI := (i.stalkMap (componentGenericPoint S Z)).hom.toAlgebra
  obtain ⟨V₀, h₀, s₀, H⟩ := exists_twist_germ ω hω DS Γ hΓη hΓ
  obtain ⟨c, hc, hgc⟩ := H V hV s.1 hs
  obtain ⟨V₁, h₁, r, hr⟩ := TopCat.Presheaf.germ_exist X.presheaf c
  have hW : i.base (componentGenericPoint S Z) ∈ V₀ ⊓ V₁ := ⟨h₀, h₁⟩
  let jW0 : V₀ ⊓ V₁ ⟶ V₀ := homOfLE inf_le_left
  let jW1 : V₀ ⊓ V₁ ⟶ V₁ := homOfLE inf_le_right
  let r' : Γ(X, V₀ ⊓ V₁) := X.presheaf.map jW1.op r
  let s₀' : (ω.twist DS).sections (V₀ ⊓ V₁) := (ω.twist DS).restrictHom jW0 s₀
  have hK : (rationalFunctionsPresheaf X).germ (V₀ ⊓ V₁) _ hW (r' • s₀'.1) =
      (rationalFunctionsPresheaf X).germ V _ hV s.1 := by
    rw [germ_smul_rationalFunctions, hgc]
    congr 1
    · rw [X.presheaf.germ_res_apply, hr]
    · exact (rationalFunctionsPresheaf X).germ_res_apply jW0 _ hW s₀.1
  have hF : TopCat.Presheaf.germ (C := Ab.{u}) (ω.twist DS).toModules.val.presheaf V _ hV s =
      c • TopCat.Presheaf.germ (C := Ab.{u}) (ω.twist DS).toModules.val.presheaf V₀ _ h₀ s₀ := by
    obtain ⟨W', hW', i1, i2, heq⟩ := TopCat.Presheaf.germ_eq _ _ hW hV _ _ hK
    have e1 : TopCat.Presheaf.germ (C := Ab.{u}) (ω.twist DS).toModules.val.presheaf V _ hV s =
        TopCat.Presheaf.germ (C := Ab.{u}) (ω.twist DS).toModules.val.presheaf (V₀ ⊓ V₁) _ hW
          (r' • s₀') :=
      TopCat.Presheaf.germ_ext _ W' hW' i2 i1 (Subtype.ext heq.symm)
    rw [e1]
    refine (Stacks.AlgebraicGeometry.Tag01YEStalkBridge.germ_smul (ω.twist DS).toModules _ _ hW r'
      s₀').trans ?_
    rw [X.presheaf.germ_res_apply, hr]
    congr 1
    exact TopCat.Presheaf.germ_res_apply (ω.twist DS).toModules.val.presheaf jW0 _ hW s₀
  rw [hF, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  have hcl : closure ({componentGenericPoint S Z} : Set S) ∈ irreducibleComponents S := by
    rw [(isGenericPoint_def.mp (isGenericPoint_componentGenericPoint S Z))]; exact Z.2
  have hfield : IsField (S.presheaf.stalk (componentGenericPoint S Z)) :=
    isField_stalk_of_closure_mem_irreducibleComponents S (componentGenericPoint S Z) hcl
  have h0 : algebraMap _ (S.presheaf.stalk (componentGenericPoint S Z)) c = 0 := by
    by_contra h0
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel h0
    exact hc (isUnit_of_map_unit (i.stalkMap (componentGenericPoint S Z)).hom c
      ⟨⟨_, b, hb, by rwa [mul_comm]⟩, rfl⟩)
  rw [h0, TensorProduct.zero_tmul]

/-- An epimorphism of modules on a scheme is surjective on stalks. -/
private theorem surjective_stalk_of_epi {X : Scheme.{u}} {A B : X.Modules} (g : A ⟶ B) [Epi g]
    (x : X) :
    Function.Surjective (ConcreteCategory.hom
      ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map g)) := by
  let T : ShortComplex X.Modules := ShortComplex.mk g (0 : B ⟶ B) (by simp)
  have hU := (SheafOfModules.exact_iff_stalkShortComplex_exact X.ringCatSheaf T).mp
    ((T.exact_iff_epi rfl).2 inferInstance) x
  exact (AddCommGrpCat.epi_iff_surjective _).mp <|
    (ShortComplex.exact_iff_epi _
      (Functor.map_zero (SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x) _ _)).1 hU

/-- In an abelian category, if `r ≫ δ = 0` is exact with `δ` epi and `ι ≫ m = u ≫ r` with `m` an
isomorphism and `u` an epimorphism, then the target of `δ` is the cokernel of `ι`. -/
private theorem nonempty_iso_cokernel_of_exact {C : Type*} [Category C] [Abelian C]
    {A B P Q T : C} (ι : A ⟶ B) (u : A ⟶ P) (r : P ⟶ Q) (m : B ≅ Q) (δ : Q ⟶ T)
    (hrδ : r ≫ δ = 0) [Epi u] [Epi δ] (hex : (ShortComplex.mk r δ hrδ).Exact)
    (hc : ι ≫ m.hom = u ≫ r) : Nonempty (T ≅ cokernel ι) := by
  have hz : ι ≫ m.hom ≫ δ = 0 := by rw [← Category.assoc, hc, Category.assoc, hrδ, comp_zero]
  let φ : ShortComplex.mk ι (m.hom ≫ δ) hz ⟶ ShortComplex.mk r δ hrδ :=
    { τ₁ := u, τ₂ := m.hom, τ₃ := 𝟙 T, comm₁₂ := hc.symm, comm₂₃ := by simp }
  have : IsIso φ.τ₂ := by dsimp [φ]; infer_instance
  have : Mono φ.τ₃ := by dsimp [φ]; infer_instance
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have h₁ := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hex
  have : Epi (ShortComplex.mk ι (m.hom ≫ δ) hz).g := by dsimp; infer_instance
  exact ⟨((colimit.isColimit _).coconePointUniqueUpToIso h₁.gIsCokernel).symm⟩

private theorem exists_inv_mul_eq_twist {X : Scheme.{u}} {k : Type u} [Field k]
    {π : X ⟶ Spec (.of k)} {d : ℕ} [IsLocallyNoetherian X] [IsNormal X]
    (ω : WeilDivisorialSubsheaf X) (hω : IsDualizingSheaf π (d + 1) ω.toModules)
    (DS : MMP.Flips.WeilDivisor X) :
    ∃ L : WeilDivisorialSubsheaf X, L.toRationalFunctionsSubmodule = (-DS).sheaf ∧
      L.inv.mul ω.toRationalFunctionsSubmodule = ω.twist DS := by
  obtain ⟨hXN, hπ⟩ := isNoetherian_and_locallyOfFiniteType_of_isDualizingSheaf hω
  obtain ⟨G, hG⟩ := exists_isWShGroup π hω.1
  obtain ⟨L, hL, hLgen⟩ := exists_weilDivisorialSubsheaf_sheaf_isGeneratedAt_prod π hω.1 (-DS)
  obtain ⟨M, hM, hMgen⟩ := exists_weilDivisorialSubsheaf_sheaf_isGeneratedAt_prod π hω.1 DS
  refine ⟨L, hL, ?_⟩
  refine RationalFunctionsSubmodule.eq_of_stalkSet_eq
    (RationalFunctionsSubmodule.isSaturated_saturation _)
    (RationalFunctionsSubmodule.isSaturated_saturation _) fun η hη => ?_
  obtain ⟨f, hf⟩ := ω.principal_codim_one η hη
  have h1 := (WeilDivisorialSubsheaf.stalkSet_mul_inv_unit L⁻¹ ω η hη _ f
    (hG.isGeneratedAt_inv hη (hLgen η hη)) hf).1
  have h2 := (WeilDivisorialSubsheaf.stalkSet_mul_inv_unit ω M η hη f _ hf (hMgen η hη)).1
  have hinv : (L⁻¹).toRationalFunctionsSubmodule = L.inv := hG.inv_eq L
  change ((L⁻¹).toRationalFunctionsSubmodule.mul ω.toRationalFunctionsSubmodule).stalkSet η =
    _ at h1
  rw [hinv] at h1
  rw [h1]
  change _ = (ω.toRationalFunctionsSubmodule.mul DS.sheaf).stalkSet η
  rw [← hM]
  change (ω.toRationalFunctionsSubmodule.mul M.toRationalFunctionsSubmodule).stalkSet η = _ at h2
  rw [h2]
  congr 3
  rw [Finsupp.support_neg, mul_comm, ← Finset.prod_inv_distrib]
  simp only [Finsupp.neg_apply, neg_neg, zpow_neg]

open scoped Classical in
/-- `ω_X(S) ≅ 𝓗om(𝓘_S, ω_X)`, `x ↦ (l ↦ x l)`, compatibly with `ω_X ≅ 𝓗om(𝒪_X, ω_X)`,
`s ↦ (a ↦ a s)`, and the inclusion `ω_X ⊆ ω_X(S)`. -/
private theorem exists_mulIso_internalHom_ideal {X S : Scheme.{u}} {k : Type u}
    [Field k] {π : X ⟶ Spec (.of k)} {d : ℕ} [IsLocallyNoetherian X] [IsNormal X]
    (hCM : ∀ x : X, IsCohenMacaulayLocalRing (X.presheaf.stalk x))
    (ω : WeilDivisorialSubsheaf X) (hω : IsDualizingSheaf π (d + 1) ω.toModules)
    (i : S ⟶ X) [IsClosedImmersion i] [IsReduced S]
    (hcodim : ∀ Z : irreducibleComponents S,
      Order.coheight (i.base (componentGenericPoint S Z)) = 1)
    (DS : MMP.Flips.WeilDivisor X)
    (hDS : ∀ Γ : WeilDivisorPrime X, DS Γ =
      if ∃ Z : irreducibleComponents S, Γ.1.genericPoint = i.base (componentGenericPoint S Z)
      then 1 else 0) :
    ∃ (m : (ω.twist DS).toModules ≅
        (Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor.{u, u, u, u}
          (Opens.grothendieckTopology X) X.sheaf (closedImmersionIdeal i).toSheafOfModules).obj
          ω.toModules)
      (v : ω.toModules ⟶
        (Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor.{u, u, u, u}
          (Opens.grothendieckTopology X) X.sheaf (SheafOfModules.unit X.ringCatSheaf)).obj
          ω.toModules),
      Epi v ∧ inclusionHom (sections_le_twist ω DS (nonneg_of_eq_ite i DS hDS)) ≫ m.hom =
        v ≫ (Stacks.SheafOfModules.InternalHom.internalHomMapLeftNatTrans X.sheaf
          (closedImmersionIdeal i).ι).app ω.toModules := by
  obtain ⟨hXN, hπ⟩ := isNoetherian_and_locallyOfFiniteType_of_isDualizingSheaf hω
  have : CompactSpace X := IsNoetherian.toCompactSpace
  obtain ⟨G, hG⟩ := exists_isWShGroup π hω.1
  obtain ⟨L, hL, heq⟩ := exists_inv_mul_eq_twist ω hω DS
  have hmulω := fun V => (WeilDivisorialSubsheaf.bijective_mulLocalHom π hω.1 L ω V).1
  -- `ω_X(S) · 𝓘_S ⊆ ω_X`
  have hcond : MulInternalHomCond (ω.twist DS) ω.toRationalFunctionsSubmodule
      (closedImmersionIdeal i).ι := by
    intro U W j x hx a
    rw [Algebra.smul_def, mul_comm]
    rw [← heq] at hx
    refine hmulω U x hx W j _ ?_
    rw [hL]
    exact algebraMap_mem_sheaf_neg i DS hDS a.2
  have hiso : IsIso (mulInternalHom hcond) := by
    refine isIso_of_bijective_app _ fun U => ?_
    have key : ∀ (F : RationalFunctionsSubmodule X)
        (hF : L.inv.mul ω.toRationalFunctionsSubmodule = F)
        (h : MulInternalHomCond F ω.toRationalFunctionsSubmodule (closedImmersionIdeal i).ι),
        Function.Bijective ((mulInternalHom h).val.app (op U)) := by
      intro F hF h
      subst hF
      obtain ⟨hmul, hbij⟩ := WeilDivisorialSubsheaf.bijective_mulLocalHom π hω.1 L ω U
      refine bijective_mulInternalHom_app (H := L.toRationalFunctionsSubmodule) h U
        (fun W a => ?_) (fun W a b hab => ?_) (fun W l hl => ?_) hmul hbij
      · rw [hL]; exact algebraMap_mem_sheaf_neg i DS hDS a.2
      · exact Subtype.ext (toRationalFunctionsPresheaf_app_injective W hab)
      · rw [hL, idealSheaf_eq hCM i hcodim DS hDS W] at hl
        obtain ⟨g, hg, rfl⟩ := hl
        exact ⟨⟨g, hg⟩, rfl⟩
    exact key _ heq hcond
  refine ⟨asIso (mulInternalHom hcond), mulInternalHom (mulInternalHomCond_id _), ?_, ?_⟩
  · exact @IsIso.epi_of_iso _ _ _ _ _ (isIso_mulInternalHom_id ω.toRationalFunctionsSubmodule)
  · exact SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun _ =>
      ModuleCat.hom_ext <| LinearMap.ext fun _ => restrFun_hom_ext fun _ _ => rfl

open scoped Classical in
/-- `i_* ω_S ≅ ω_X(S)/ω_X`, the cokernel of the inclusion `ω_X ⊆ ω_X(S)`. -/
private theorem nonempty_pushforward_iso_cokernel_inclusionHom {X S : Scheme.{u}} {k : Type u}
    [Field k] {π : X ⟶ Spec (.of k)} {d : ℕ} [IsLocallyNoetherian X] [IsNormal X]
    (hCM : ∀ x : X, IsCohenMacaulayLocalRing (X.presheaf.stalk x))
    (ω : WeilDivisorialSubsheaf X) (hω : IsDualizingSheaf π (d + 1) ω.toModules)
    (i : S ⟶ X) [IsClosedImmersion i] [IsReduced S]
    (hcodim : ∀ Z : irreducibleComponents S,
      Order.coheight (i.base (componentGenericPoint S Z)) = 1)
    {ωS : S.Modules} (hS : IsDualizingSheaf (i ≫ π) d ωS)
    (DS : MMP.Flips.WeilDivisor X)
    (hDS : ∀ Γ : WeilDivisorPrime X, DS Γ =
      if ∃ Z : irreducibleComponents S, Γ.1.genericPoint = i.base (componentGenericPoint S Z)
      then 1 else 0) :
    Nonempty ((Scheme.Modules.pushforward i).obj ωS ≅
      cokernel (inclusionHom (sections_le_twist ω DS (nonneg_of_eq_ite i DS hDS)))) := by
  obtain ⟨m, v, hv, hc⟩ := exists_mulIso_internalHom_ideal hCM ω hω i hcodim DS hDS
  obtain ⟨δ, hδ, hepi, hex⟩ := hω.exists_epi_exact_internalHom_ideal i hCM hS
  exact @nonempty_iso_cokernel_of_exact _ _ _ _ _ _ _ _ _ v _ m δ hδ hv hepi hex hc

section StalkHomEquivSymm

variable {X S : Scheme.{u}} (ω : WeilDivisorialSubsheaf X) (i : S ⟶ X) {ωS : S.Modules}
    (DS : MMP.Flips.WeilDivisor X)

private theorem exists_preimage_eq_of_isClosedImmersion [IsClosedImmersion i] (W : S.Opens) :
    ∃ V : X.Opens, i ⁻¹ᵁ V = W := by
  obtain ⟨V, hV, hVW⟩ := (i.isEmbedding.isInducing.isOpen_iff).mp W.2
  exact ⟨⟨V, hV⟩, Opens.ext hVW⟩

private theorem stalkMap_homEquiv_symm_germ_unit
    (β : (ω.twist DS).toModules ⟶ (Scheme.Modules.pushforward i).obj ωS) (x : S)
    (V : X.Opens) (hV : i.base x ∈ V) (s : Γ((ω.twist DS).toModules, V)) :
    ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map
        (((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm β).val))
      (TopCat.Presheaf.germ (C := Ab.{u}) ((Scheme.Modules.pullback i).obj
        (ω.twist DS).toModules).val.presheaf
        (i ⁻¹ᵁ V) _ hV (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (ω.twist DS).toModules).val.app (op V) s)) =
    TopCat.Presheaf.germ (C := Ab.{u}) ωS.val.presheaf (i ⁻¹ᵁ V) _ hV (β.val.app (op V) s) := by
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _).trans (congrArg _ ?_)
  exact (congrArg (fun g : (ω.twist DS).toModules ⟶ (Scheme.Modules.pushforward i).obj ωS =>
    g.val.app (op V) s) ((Equiv.apply_symm_apply _ β).symm.trans
      (Adjunction.homEquiv_unit _ _ _ _))).symm

private theorem exists_germ_unit_eq [IsClosedImmersion i] (x : S)
    (w : TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pullback i).obj (ω.twist DS).toModules).val.presheaf x) :
    ∃ (V : X.Opens) (hV : i.base x ∈ V) (s : Γ((ω.twist DS).toModules, V)),
      TopCat.Presheaf.germ (C := Ab.{u}) ((Scheme.Modules.pullback i).obj
        (ω.twist DS).toModules).val.presheaf
        (i ⁻¹ᵁ V) _ hV (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (ω.twist DS).toModules).val.app (op V) s) = w := by
  letI := (i.stalkMap x).hom.toAlgebra
  obtain ⟨m, hm⟩ := TensorProduct.mk_surjective _ _ _ (SurjectiveOnStalks.stalkMap_surjective i _)
    (Scheme.Modules.pullbackStalkEquiv i (ω.twist DS).toModules _ w)
  obtain ⟨V, hV, s, rfl⟩ := TopCat.Presheaf.germ_exist _ m
  exact ⟨V, hV, s, (Scheme.Modules.pullbackStalkEquiv_symm_one_tmul i _ _ V hV s).symm.trans
    ((congrArg _ hm).trans (LinearEquiv.symm_apply_apply _ _))⟩

private theorem injective_stalk_homEquiv_symm {k : Type u} [Field k] {π : X ⟶ Spec (.of k)}
    {d : ℕ} [IsLocallyNoetherian X] [IsNormal X] (hω : IsDualizingSheaf π (d + 1) ω.toModules)
    [IsClosedImmersion i] [IsReduced S]
    (Z : irreducibleComponents S) (Γ : WeilDivisorPrime X)
    (hE : Γ.1.genericPoint = i.base (componentGenericPoint S Z)) (hΓ : DS Γ = 1)
    (β : (ω.twist DS).toModules ⟶ (Scheme.Modules.pushforward i).obj ωS)
    (hβ : ∀ (U : X.Opens) (s : (ω.twist DS).sections U),
      β.val.app (op U) s = 0 ↔ s.1 ∈ ω.sections U) :
    Function.Injective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (componentGenericPoint S Z)).map
        ((PresheafOfModules.toPresheaf _).map
          (((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm β).val))) := by
  refine (injective_iff_map_eq_zero _).mpr fun w hw => ?_
  obtain ⟨V, hV, s, rfl⟩ := exists_germ_unit_eq ω i DS _ w
  obtain ⟨W, hW, j1, j2, hj⟩ := TopCat.Presheaf.germ_eq (C := Ab.{u}) ωS.val.presheaf
    (componentGenericPoint S Z) (show componentGenericPoint S Z ∈ i ⁻¹ᵁ V from hV)
    (show componentGenericPoint S Z ∈ i ⁻¹ᵁ V from hV) _ 0
    (((stalkMap_homEquiv_symm_germ_unit ω i DS β _ V hV s).symm.trans hw).trans (map_zero _).symm)
  rw [map_zero] at hj
  obtain ⟨V'', rfl⟩ := exists_preimage_eq_of_isClosedImmersion i W
  have hV' : i.base (componentGenericPoint S Z) ∈ V ⊓ V'' := ⟨hV, hW⟩
  let jV : V ⊓ V'' ⟶ V := homOfLE inf_le_left
  let s' : Γ((ω.twist DS).toModules, V ⊓ V'') := (ω.twist DS).toModules.val.presheaf.map jV.op s
  have hle : i ⁻¹ᵁ (V ⊓ V'') ≤ i ⁻¹ᵁ V'' := fun x hx => hx.2
  have hβs' : β.val.app (op (V ⊓ V'')) s' = 0 := by
    refine (PresheafOfModules.naturality_apply β.val jV.op s).trans ?_
    have e : ((Opens.map i.base).map jV).op = j1.op ≫ (homOfLE hle).op :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    change ConcreteCategory.hom (ωS.val.presheaf.map ((Opens.map i.base).map jV).op) _ = 0
    rw [e, Functor.map_comp]
    refine (ConcreteCategory.comp_apply _ _ _).trans ?_
    rw [hj, map_zero]
  have h1 := one_tmul_germ_eq_zero ω hω i Z DS Γ hE hΓ (V ⊓ V'') hV' s' ((hβ _ s').mp hβs')
  letI := (i.stalkMap (componentGenericPoint S Z)).hom.toAlgebra
  refine ((TopCat.Presheaf.germ_res_apply
    ((Scheme.Modules.pullback i).obj (ω.twist DS).toModules).val.presheaf
    ((Opens.map i.base).map jV) _ hV' _).symm.trans (congrArg _
    (PresheafOfModules.naturality_apply ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (ω.twist DS).toModules).val jV.op s).symm)).trans
    (((Scheme.Modules.pullbackStalkEquiv_symm_one_tmul i _ _ (V ⊓ V'') hV' s').symm).trans ?_)
  rw [h1]
  exact map_zero _

private theorem surjective_stalk_homEquiv_symm [IsClosedImmersion i]
    (β : (ω.twist DS).toModules ⟶ (Scheme.Modules.pushforward i).obj ωS) [Epi β] (x : S) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf _).map
          (((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm β).val))) := by
  intro y
  obtain ⟨W, hξW, t, rfl⟩ := TopCat.Presheaf.germ_exist _ y
  obtain ⟨V₀, rfl⟩ := exists_preimage_eq_of_isClosedImmersion i W
  obtain ⟨m, hm⟩ := surjective_stalk_of_epi β (i.base x)
    (TopCat.Presheaf.germ (C := Ab.{u}) ((Scheme.Modules.pushforward i).obj ωS).val.presheaf
      V₀ _ hξW t)
  obtain ⟨V, hV, s, rfl⟩ := TopCat.Presheaf.germ_exist _ m
  change ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} _).map
    ((PresheafOfModules.toPresheaf _).map β.val)) _ = _ at hm
  have hm := (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _).symm.trans hm
  obtain ⟨W', hW', j1, j2, hj⟩ := TopCat.Presheaf.germ_eq (C := Ab.{u})
    ((Scheme.Modules.pushforward i).obj ωS).val.presheaf _ hV hξW _ _ hm
  let s' : Γ((ω.twist DS).toModules, W') := (ω.twist DS).toModules.val.presheaf.map j1.op s
  refine ⟨TopCat.Presheaf.germ (C := Ab.{u}) ((Scheme.Modules.pullback i).obj
    (ω.twist DS).toModules).val.presheaf
    (i ⁻¹ᵁ W') _ hW' (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (ω.twist DS).toModules).val.app (op W') s'), ?_⟩
  refine (stalkMap_homEquiv_symm_germ_unit ω i DS β x W' hW' s').trans ?_
  have : β.val.app (op W') s' =
      ((Scheme.Modules.pushforward i).obj ωS).val.presheaf.map j2.op t := by
    rw [← hj]
    exact PresheafOfModules.naturality_apply β.val j1.op s
  rw [this]
  exact TopCat.Presheaf.germ_res_apply ωS.val.presheaf ((Opens.map i.base).map j2) _ hW' t

end StalkHomEquivSymm

open scoped Classical in
private theorem isIso_stalk_homEquiv_symm {X S : Scheme.{u}} {k : Type u}
    [Field k] {π : X ⟶ Spec (.of k)} {d : ℕ} [IsLocallyNoetherian X] [IsNormal X]
    (ω : WeilDivisorialSubsheaf X) (hω : IsDualizingSheaf π (d + 1) ω.toModules)
    (i : S ⟶ X) [IsClosedImmersion i] [IsReduced S]
    (hcodim : ∀ Z : irreducibleComponents S,
      Order.coheight (i.base (componentGenericPoint S Z)) = 1)
    {ωS : S.Modules} (DS : MMP.Flips.WeilDivisor X)
    (hDS : ∀ Γ : WeilDivisorPrime X, DS Γ =
      if ∃ Z : irreducibleComponents S, Γ.1.genericPoint = i.base (componentGenericPoint S Z)
      then 1 else 0)
    (β : (ω.twist DS).toModules ⟶ (Scheme.Modules.pushforward i).obj ωS) [Epi β]
    (hβ : ∀ (U : X.Opens) (s : (ω.twist DS).sections U),
      β.val.app (op U) s = 0 ↔ s.1 ∈ ω.sections U) (Z : irreducibleComponents S) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (componentGenericPoint S Z)).map
      ((PresheafOfModules.toPresheaf _).map
        (((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm β).val)) := by
  obtain ⟨hXN, hπ⟩ := isNoetherian_and_locallyOfFiniteType_of_isDualizingSheaf hω
  let E : MMP.Mori.PrimeDivisor X :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne (i.base (componentGenericPoint S Z)) (hcodim Z)
  have hE : E.genericPoint = i.base (componentGenericPoint S Z) :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  let Γ : WeilDivisorPrime X :=
    ⟨E, inferInstance, MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing E⟩
  have hΓ : DS Γ = 1 := by rw [hDS Γ, if_pos ⟨Z, hE⟩]
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨injective_stalk_homEquiv_symm ω i DS hω Z Γ hE hΓ β hβ,
    surjective_stalk_homEquiv_symm ω i DS β _⟩

open scoped Classical in
/-- The map `β : ω_X(S) ⟶ i_* ω_S`: an epimorphism with kernel `ω_X`, whose adjoint
`i^*(ω_X(S)) ⟶ ω_S` is an isomorphism at the generic points of `S`. -/
private theorem exists_beta {k : Type u} [Field k]
    {X S : Scheme.{u}} [IsNormal X] [IsLocallyNoetherian X] {π : X ⟶ Spec (.of k)} {d : ℕ}
    (hCM : ∀ x : X, IsCohenMacaulayLocalRing (X.presheaf.stalk x))
    {ω : WeilDivisorialSubsheaf X} (hX : IsDualizingSheaf π (d + 1) ω.toModules)
    (i : S ⟶ X) [IsClosedImmersion i] [IsReduced S]
    (hcodim : ∀ Z : irreducibleComponents S,
      Order.coheight (i.base (componentGenericPoint S Z)) = 1)
    {ωS : S.Modules} (hS : IsDualizingSheaf (i ≫ π) d ωS)
    (DS : MMP.Flips.WeilDivisor X)
    (hDS : ∀ Γ : WeilDivisorPrime X, DS Γ =
      if ∃ Z : irreducibleComponents S, Γ.1.genericPoint = i.base (componentGenericPoint S Z)
      then 1 else 0) :
    ∃ β : (ω.twist DS).toModules ⟶ (Scheme.Modules.pushforward i).obj ωS,
      Epi β ∧
      (∀ (U : X.Opens) (s : Γ((ω.twist DS).toModules, U)),
        (β.val.app (op U)) s = 0 ↔ s.1 ∈ ω.sections U) ∧
      ∀ Z : irreducibleComponents S,
        IsIso ((TopCat.Presheaf.stalkFunctor Ab (componentGenericPoint S Z)).map
          ((PresheafOfModules.toPresheaf _).map
            (((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm β).val)) := by
  obtain ⟨e⟩ := nonempty_pushforward_iso_cokernel_inclusionHom hCM ω hX i hcodim hS DS hDS
  set ι := inclusionHom (sections_le_twist ω DS (nonneg_of_eq_ite i DS hDS))
  let β := cokernel.π ι ≫ e.inv
  have hker : ∀ (U : X.Opens) (s : (ω.twist DS).sections U),
      β.val.app (op U) s = 0 ↔ s.1 ∈ ω.sections U := by
    intro U s
    rw [← cokernel_π_app_eq_zero_iff (sections_le_twist ω DS (nonneg_of_eq_ite i DS hDS)) U s]
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · have h2 : (e.hom.val.app (op U)) ((β.val.app (op U)) s) =
          (cokernel.π ι).val.app (op U) s := by
        change ((cokernel.π ι ≫ e.inv ≫ e.hom).val.app (op U)) s = _
        rw [Iso.inv_hom_id, Category.comp_id]
      rw [← h2, h0, map_zero]
    · change (e.inv.val.app (op U)) ((cokernel.π ι).val.app (op U) s) = 0
      rw [h0, map_zero]
  exact ⟨β, epi_comp _ _, hker, isIso_stalk_homEquiv_symm ω hX i hcodim DS hDS β hker⟩

open scoped Classical in
/-- The map `α : i^*(ω_X(S)) ⟶ ω_S` with adjoint kernel `ω_X`, surjective and an isomorphism
at the generic points of `S`. -/
private theorem exists_alpha {k : Type u} [Field k]
    {X S : Scheme.{u}} [IsNormal X] [IsLocallyNoetherian X] {π : X ⟶ Spec (.of k)} {d : ℕ}
    (hCM : ∀ x : X, IsCohenMacaulayLocalRing (X.presheaf.stalk x))
    {ω : WeilDivisorialSubsheaf X} (hX : IsDualizingSheaf π (d + 1) ω.toModules)
    (i : S ⟶ X) [IsClosedImmersion i] [IsReduced S]
    (hcodim : ∀ Z : irreducibleComponents S,
      Order.coheight (i.base (componentGenericPoint S Z)) = 1)
    {ωS : S.Modules} (hS : IsDualizingSheaf (i ≫ π) d ωS)
    (DS : MMP.Flips.WeilDivisor X)
    (hDS : ∀ Γ : WeilDivisorPrime X, DS Γ =
      if ∃ Z : irreducibleComponents S, Γ.1.genericPoint = i.base (componentGenericPoint S Z)
      then 1 else 0) :
    ∃ α : (Scheme.Modules.pullback i).obj (ω.twist DS).toModules ⟶ ωS,
      (∀ (U : X.Opens) (s : Γ((ω.twist DS).toModules, U)),
        (((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _ α).val.app (op U)) s = 0 ↔
          s.1 ∈ ω.sections U) ∧
      Epi α ∧
      ∀ Z : irreducibleComponents S,
        IsIso ((TopCat.Presheaf.stalkFunctor Ab (componentGenericPoint S Z)).map
          ((PresheafOfModules.toPresheaf _).map α.val)) := by
  obtain ⟨β, _, hker, hgen⟩ := exists_beta hCM hX i hcodim hS DS hDS
  refine ⟨((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm β,
    fun U s => ?_, epi_homEquiv_symm_of_epi i β, hgen⟩
  rw [Equiv.apply_symm_apply]
  exact hker U s

open scoped Classical in
/-- **The adjunction sequence** (FA 16.4). Let `X` be normal and Cohen–Macaulay, of finite type
and pure dimension `d + 1` over `k`, with embedded dualizing sheaf `ω ⊆ K(X)`, and `i : S ⟶ X` a
reduced closed subscheme of pure codimension one with dualizing sheaf `ω_S`, and let `DS` be the
reduced Weil divisor of `S`. Then
* the ideal sheaf of `S` is `𝒪_X(-DS)`: on every open `U`, `𝒪_X(-DS)(U)` is the image in
  `K(X)(U)` of the kernel of `Γ(X, U) → Γ(S, i⁻¹ U)`;
* there is `α : i^*(ω(DS)) ⟶ ω_S` whose adjoint `ω(DS) ⟶ i_* ω_S` has kernel `ω`, which is an
  epimorphism and induces isomorphisms on the stalks at the generic points of `S`. -/
@[mmp "lem_fa16a_adjunction_exact_sequence"]
public theorem IsDualizingSheaf.exists_adjunction_exact_sequence {k : Type u} [Field k]
    {X S : Scheme.{u}} [IsNormal X] [IsLocallyNoetherian X] {π : X ⟶ Spec (.of k)} {d : ℕ}
    (hCM : ∀ x : X, IsCohenMacaulayLocalRing (X.presheaf.stalk x))
    {ω : WeilDivisorialSubsheaf X} (hX : IsDualizingSheaf π (d + 1) ω.toModules)
    (i : S ⟶ X) [IsClosedImmersion i] [IsReduced S]
    (hcodim : ∀ Z : irreducibleComponents S,
      Order.coheight (i.base (componentGenericPoint S Z)) = 1)
    {ωS : S.Modules} (hS : IsDualizingSheaf (i ≫ π) d ωS)
    (DS : WeilDivisor X)
    (hDS : ∀ Γ : WeilDivisorPrime X, DS Γ =
      if ∃ Z : irreducibleComponents S, Γ.1.genericPoint = i.base (componentGenericPoint S Z)
      then 1 else 0) :
    (∀ U : X.Opens, (-DS).sheaf.sections U =
      Submodule.map (Algebra.linearMap Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)))
        (RingHom.ker (i.app U).hom)) ∧
    ∃ α : (Scheme.Modules.pullback i).obj (ω.twist DS).toModules ⟶ ωS,
      (∀ (U : X.Opens) (s : Γ((ω.twist DS).toModules, U)),
        (((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _ α).val.app (op U)) s = 0 ↔
          s.1 ∈ ω.sections U) ∧
      Epi α ∧
      ∀ Z : irreducibleComponents S,
        IsIso ((TopCat.Presheaf.stalkFunctor Ab (componentGenericPoint S Z)).map
          ((PresheafOfModules.toPresheaf _).map α.val)) :=
  ⟨idealSheaf_eq hCM i hcodim DS hDS, exists_alpha hCM hX i hcodim hS DS hDS⟩

/-! ### Small contractions to a common base -/

/-! ### Birational morphisms -/

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have he' : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- A composite of birational morphisms out of an irreducible scheme is birational. -/
private theorem isBirationalMorphism_comp {X Y Z : Scheme.{u}} [IrreducibleSpace X]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    IsBirationalMorphism (f ≫ g) := by
  have := hf.isDominant
  have := hg.isDominant
  obtain ⟨U₁, hU₁, h₁⟩ := exists_isOpenImmersion_of_isBirationalMorphism hf
  obtain ⟨U₂, hU₂, h₂⟩ := exists_isOpenImmersion_of_isBirationalMorphism hg
  let U : X.Opens := U₁ ⊓ f ⁻¹ᵁ U₂
  have hne : (U : Set X).Nonempty := by
    obtain ⟨x₀⟩ := (IrreducibleSpace.isIrreducible_univ X).nonempty
    have : Nonempty Y := ⟨f x₀⟩
    have hd : Dense (f '' U₁) := f.denseRange.dense_image f.continuous hU₁
    obtain ⟨y, hy₂, x, hx₁, rfl⟩ := (hU₂.inter_of_isOpen_left hd U₂.2).nonempty
    exact ⟨x, hx₁, hy₂⟩
  have hU : Dense (U : Set X) := U.2.dense hne
  have hle : U ≤ f ⁻¹ᵁ U₂ := inf_le_right
  have hle₁ : U ≤ U₁ := inf_le_left
  have hres : IsOpenImmersion (f.resLE U₂ U hle) := by
    have : f.resLE U₂ U hle ≫ U₂.ι = X.homOfLE hle₁ ≫ (U₁.ι ≫ f) := by
      rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.homOfLE_ι]
    have : IsOpenImmersion (f.resLE U₂ U hle ≫ U₂.ι) := by rw [this]; infer_instance
    exact IsOpenImmersion.of_comp _ U₂.ι
  have : IsOpenImmersion (U.ι ≫ f ≫ g) := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle, Category.assoc]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion (f ≫ g) U hU

/-! ### Small contractions -/

/-- A small morphism `φ : X ⟶ Z` is an open immersion off a closed subset `V` of codimension
`≥ 2`: points of `V` have coheight `≥ 2`, and off `V` the map `φ` is injective and preserves
coheights. -/
private theorem exists_closeds_of_isSmall {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φ : X ⟶ Z} (hφ : IsSmall k sZ sX φ) :
    ∃ V : Closeds X, (∀ x ∈ (V : Set X), 2 ≤ Order.coheight x) ∧
      (∀ x ∉ (V : Set X), Order.coheight (φ x) = Order.coheight x) ∧
      ∀ x ∉ (V : Set X), ∀ y ∉ (V : Set X), φ x = φ y → x = y := by
  obtain ⟨V, W, hV, -, h, hiso⟩ := hφ.exists_isIso
  let U : X.Opens := V.compl
  have hoi : IsOpenImmersion (U.ι ≫ φ) := by
    rw [← Scheme.Hom.resLE_comp_ι φ h]; infer_instance
  refine ⟨V, le_closedsCodimension_iff_le_coheight.mp hV, fun x hx => ?_,
    fun x hx y hy hxy => ?_⟩
  · exact coheight_map_of_notMem_exceptionalSet (f := φ) (fun hE => hE ⟨U, hx, hoi⟩)
  · have h' : (U.ι ≫ φ) (⟨x, hx⟩ : U.toScheme) = (U.ι ≫ φ) (⟨y, hy⟩ : U.toScheme) := hxy
    exact congrArg Subtype.val ((U.ι ≫ φ).isOpenEmbedding.injective h')

/-- A small morphism does not lower coheight. -/
private theorem coheight_le_coheight_map_of_isSmall {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φ : X ⟶ Z} (hφ : IsSmall k sZ sX φ)
    (x : X) : Order.coheight x ≤ Order.coheight (φ x) :=
  coheight_le_coheight_map sZ sX hφ.isVariety_target hφ.isVariety_source φ hφ.comp_eq hφ.dim_eq x

/-! ### Exceptional divisors and coheight -/

private theorem two_le_of_add_two_le_add {d : WithBot ℕ∞} {c : ℕ∞} (hd : d ≠ ⊤) (hd' : d ≠ ⊥)
    (h : d + 2 ≤ d + c) : 2 ≤ c := by
  obtain ⟨d, rfl⟩ := WithBot.ne_bot_iff_exists.mp hd'
  have hd2 : d ≠ ⊤ := fun h' => hd (by rw [h']; rfl)
  have h2 : ((d + 2 : ℕ∞) : WithBot ℕ∞) ≤ ((d + c : ℕ∞) : WithBot ℕ∞) := h
  exact (WithTop.add_le_add_iff_left hd2).mp (WithBot.coe_le_coe.mp h2)

/-- An exceptional divisor over a variety has center of coheight `≥ 2`. -/
private theorem two_le_coheight_of_isExceptional {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (hX : MMP.Mori.IsVariety k sX)
    (D : ProperDivisorOver k sX) (hD : D.IsExceptional) :
    2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := hX.toLocallyOfFiniteType
  have := hX.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  unfold ProperDivisorOver.IsExceptional at hD
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint,
    ← topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)] at hD
  have hsum := topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  have hne := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  refine two_le_of_add_two_le_add ?_ ?_ hD
  · intro htop
    rw [htop] at hsum
    refine hne (hsum.symm.trans ?_)
    rw [show (⊤ : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_add, top_add]
  · rw [topologicalKrullDim_closure_singleton_eq_trdeg k X sX]
    exact WithBot.coe_ne_bot

/-- The valuation `ord_E` of a divisor `(Y, f, E)` over `X` has nonempty center on `X`. -/
private theorem hasNonemptyCenter_valuation {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  refine ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

/-! ### Transporting a divisor from `X` to `X⁺` through `Z` -/

/-- A divisor `(Y, f, E)` over `X` is realized by a divisor `(Y₁, f₁, E₁)` over `X⁺` with the
same valuation of `k(Z)` and the same centre `φ(f(η_E)) = φ⁺(f₁(η_{E₁}))` on `Z`. -/
private theorem exists_properDivisorOver_map_eq {k : Type u} [Field k]
    {X X' Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {φ : X ⟶ Z} {φ' : X' ⟶ Z} [IsDominant φ] [IsDominant φ']
    (hφ : IsBirationalContraction k sZ sX φ) (hφ' : IsBirationalContraction k sZ sX' φ')
    (D : ProperDivisorOver k sX) :
    ∃ D₁ : ProperDivisorOver k sX',
      D₁.valuation.comap (functionFieldMap φ') = D.valuation.comap (functionFieldMap φ) ∧
      φ' (D₁.f D₁.E.genericPoint) = φ (D.f D.E.genericPoint) := by
  have hbφ : IsBirationalMorphism φ := hφ.surjective_and_isBirational.2
  have hbφ' : IsBirationalMorphism φ' := hφ'.surjective_and_isBirational.2
  have hZ := hφ.isVariety_target
  have hX' := hφ'.isVariety_source
  have := hφ.isProper
  have := hφ'.isProper
  have e := hφ.comp_eq
  have e' := hφ'.comp_eq
  subst e e'
  have := D.isIntegral
  have := D.isProper
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  let DZ : ProperDivisorOver k sZ :=
    { Y := D.Y
      f := D.f ≫ φ
      isNormalVariety := by simpa only [Category.assoc] using D.isNormalVariety
      isBirationalMorphism := isBirationalMorphism_comp D.isBirationalMorphism hbφ
      E := D.E
      isProper := inferInstance }
  have hDZ : DZ.valuation = D.valuation.comap (functionFieldMap φ) := by
    ext a
    change D.E.divisorialValuation _ = D.E.divisorialValuation _
    congr 1
    exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f φ a).symm
  obtain ⟨D₁, hD₁, hn, hb, hp, hD₁Z⟩ :=
    ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq hZ φ' hX' hbφ' DZ
  refine ⟨D₁, hD₁.trans hDZ, ?_⟩
  have hc := ProperDivisorOver.center_eq_of_valuation_eq hZ hD₁Z
  have h1 := congrArg (fun C : IrreducibleCloseds Z => (C : Set Z)) hc
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint, DivisorOver.center_eq_closure_genericPoint] at h1
  have h2 := (inseparable_iff_closure_eq.2 h1).eq
  simpa only [DZ, Scheme.Hom.comp_apply] using h2

/-! ### Exceptional divisors -/

private theorem hasNonemptyCenter_isExceptional_of_comap_eq {k : Type u} [Field k]
    {X X' Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {φ : X ⟶ Z} {φ' : X' ⟶ Z} [IsDominant φ] [IsDominant φ']
    (hφ : IsSmall k sZ sX φ) (hφ' : IsSmall k sZ sX' φ')
    {v : Valuation X.functionField ℤᵐ⁰} {v' : Valuation X'.functionField ℤᵐ⁰}
    (h : v.comap (functionFieldMap φ) = v'.comap (functionFieldMap φ')) :
    (HasNonemptyCenter k sX v ∧
        ∃ D : ProperDivisorOver k sX, D.valuation = v ∧ D.IsExceptional) →
      (HasNonemptyCenter k sX' v' ∧
        ∃ D : ProperDivisorOver k sX', D.valuation = v' ∧ D.IsExceptional) := by
  rintro ⟨-, D, rfl, hD⟩
  obtain ⟨D₁, hval, hpt⟩ :=
    exists_properDivisorOver_map_eq hφ.toIsBirationalContraction
      hφ'.toIsBirationalContraction D
  have hv' : D₁.valuation = v' := by
    have hb' : IsBirationalMorphism φ' := hφ'.surjective_and_isBirational.2
    have hbij := hb'.functionFieldMap_bijective
    ext a
    obtain ⟨b, rfl⟩ := hbij.2 a
    exact congrArg (fun w => w b) (hval.trans h)
  refine ⟨hv' ▸ hasNonemptyCenter_valuation D₁, D₁, hv', ?_⟩
  have := hφ'.isVariety_source.toLocallyOfFiniteType
  by_contra hne
  apply D₁.not_two_le_coheight_of_not_isExceptional hne
  obtain ⟨V', hV'2, hV'coh, -⟩ := exists_closeds_of_isSmall hφ'
  have h2 : 2 ≤ Order.coheight (φ' (D₁.f D₁.E.genericPoint)) := by
    rw [hpt]
    exact (two_le_coheight_of_isExceptional hφ.isVariety_source D hD).trans
      (coheight_le_coheight_map_of_isSmall hφ _)
  by_cases hm : D₁.f D₁.E.genericPoint ∈ (V' : Set X')
  · exact hV'2 _ hm
  · rwa [← hV'coh _ hm]

/-! ### Prime divisors -/

/-- The generic point of a prime divisor lies off the codimension-two locus of a small map. -/
private theorem genericPoint_notMem {X : Scheme.{u}} {V : Closeds X}
    (hV : ∀ x ∈ (V : Set X), 2 ≤ Order.coheight x) (P : MMP.Mori.PrimeDivisor X) :
    P.genericPoint ∉ (V : Set X) := by
  intro h
  have := hV _ h
  rw [P.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- A small morphism sends the generic point of a prime divisor to a point of coheight one. -/
private theorem coheight_map_genericPoint {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φ : X ⟶ Z} (hφ : IsSmall k sZ sX φ)
    (P : MMP.Mori.PrimeDivisor X) : Order.coheight (φ P.genericPoint) = 1 := by
  obtain ⟨V, hV2, hVcoh, -⟩ := exists_closeds_of_isSmall hφ
  rw [hVcoh _ (genericPoint_notMem hV2 P), P.coheight_genericPoint]

/-- Prime divisors of `X` with the same image of their generic points in `Z` are equal. -/
private theorem primeDivisor_eq_of_map_eq {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φ : X ⟶ Z} (hφ : IsSmall k sZ sX φ)
    {P Q : MMP.Mori.PrimeDivisor X} (h : φ P.genericPoint = φ Q.genericPoint) : P = Q := by
  obtain ⟨V, hV2, -, hinj⟩ := exists_closeds_of_isSmall hφ
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (hinj _ (genericPoint_notMem hV2 P) _ (genericPoint_notMem hV2 Q) h)

/-- A prime divisor `P` of `X` corresponds to a prime divisor `Q` of `X⁺` with
`φ⁺(η_Q) = φ(η_P)` and `ord_Q = ord_P` on `k(Z)`. -/
private theorem exists_primeDivisor_map_eq {k : Type u} [Field k]
    {X X' Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian X'] [IsNormal X] [IsNormal X']
    {φ : X ⟶ Z} {φ' : X' ⟶ Z} [IsDominant φ] [IsDominant φ']
    (hφ : IsSmall k sZ sX φ) (hφ' : IsSmall k sZ sX' φ') (P : MMP.Mori.PrimeDivisor X) :
    ∃ Q : MMP.Mori.PrimeDivisor X', φ' Q.genericPoint = φ P.genericPoint ∧
      Q.divisorialValuation.comap (functionFieldMap φ') =
        P.divisorialValuation.comap (functionFieldMap φ) := by
  have hXn : IsNormalVariety k sX := ⟨hφ.isVariety_source, inferInstance⟩
  have hX'n : IsNormalVariety k sX' := ⟨hφ'.isVariety_source, inferInstance⟩
  have := hφ'.isVariety_source.toLocallyOfFiniteType
  let D : ProperDivisorOver k sX :=
    { toDivisorOver := DivisorOver.ofPrimeDivisor k hXn P
      isProper := by change IsProper (𝟙 X); infer_instance }
  have hDv : D.valuation = P.divisorialValuation := by
    ext a
    change P.divisorialValuation (functionFieldMap (𝟙 X) a) = _
    rw [MMP.Mori.functionFieldMap_id_apply]
  have hDp : D.f D.E.genericPoint = P.genericPoint := rfl
  obtain ⟨D₁, hval, hpt⟩ :=
    exists_properDivisorOver_map_eq hφ.toIsBirationalContraction
      hφ'.toIsBirationalContraction D
  rw [hDp] at hpt
  rw [hDv] at hval
  have hne : ¬ D₁.IsExceptional := by
    intro hex
    have h2 := (two_le_coheight_of_isExceptional hφ'.isVariety_source D₁ hex).trans
      (coheight_le_coheight_map_of_isSmall hφ' _)
    rw [hpt, coheight_map_genericPoint hφ P] at h2
    exact absurd h2 (by decide)
  obtain ⟨Q, -, hQη, -, hQv⟩ := D₁.exists_primeDivisor_of_not_isExceptional hX'n hne
  exact ⟨Q, hQη ▸ hpt, hQv ▸ hval⟩

/-- A modification `g` of `φ` into `φ⁺` sends `P` to any prime divisor `Q` of `X⁺` with
`φ⁺(η_Q) = φ(η_P)`. -/
private theorem transformPrimeDivisor_eq_some_of_map_eq {k : Type u} [Field k]
    {X X' Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    [IsLocallyNoetherian X] [IsNormal X]
    {φ : X ⟶ Z} {φ' : X' ⟶ Z}
    (hφ : IsSmall k sZ sX φ) (hφ' : IsSmall k sZ sX' φ') (g : X.RationalMap X')
    (hg : IsModificationOf φ φ' g) (P : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor X')
    (hPQ : φ' Q.genericPoint = φ P.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor g P = some Q := by
  have := hφ'.isProper
  have hZs : IsSeparated sZ := hφ.isVariety_target.toIsSeparated
  have : Z.IsSeparated := ⟨by rw [← Limits.terminal.comp_from sZ]; infer_instance⟩
  have hX's : IsSeparated sX' := hφ'.isVariety_source.toIsSeparated
  have : X'.IsSeparated := ⟨by rw [← Limits.terminal.comp_from sX']; infer_instance⟩
  obtain ⟨V', hV'2, -, hinj'⟩ := exists_closeds_of_isSmall hφ'
  have hdom : P.genericPoint ∈ g.domain :=
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one φ φ' g hg.2
      P.coheight_genericPoint.le
  obtain ⟨g', hg'd, hg'⟩ := Scheme.RationalMap.mem_domain.mp hdom
  set y := g'.hom ⟨P.genericPoint, hg'd⟩ with hy
  have hφy : φ' y = φ P.genericPoint := by
    have h1 : (g'.compHom φ').toRationalMap = φ.toPartialMap.toRationalMap := by
      rw [Scheme.RationalMap.compHom_toRationalMap, hg']
      exact hg.2
    have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
      (g := g'.compHom φ') (g' := φ.toPartialMap) h1 hg'd trivial
    change (g'.hom ≫ φ') ⟨P.genericPoint, hg'd⟩ = (X.topIso.hom ≫ φ) ⟨P.genericPoint, trivial⟩
      at h2
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
    rw [Scheme.topIso_hom]
    rfl
  have hyV : y ∉ (V' : Set X') := by
    intro hm
    have h2 := (hV'2 _ hm).trans (coheight_le_coheight_map_of_isSmall hφ' y)
    rw [hφy, coheight_map_genericPoint hφ P] at h2
    exact absurd h2 (by decide)
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hg'd ?_
  exact hinj' _ (genericPoint_notMem hV'2 Q) _ hyV (hPQ.trans hφy.symm)

section PrimeDivisorEquiv

variable {k : Type u} [Field k] {X X' Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
  [IsLocallyNoetherian X] [IsLocallyNoetherian X'] [IsNormal X] [IsNormal X']
  {φ : X ⟶ Z} {φ' : X' ⟶ Z} [IsDominant φ] [IsDominant φ']

/-- Under a modification `g` of `φ` into `φ⁺`, the transform `g_* P` of a prime divisor `P` of `X`
is a prime divisor `Q` of `X⁺` with `φ⁺(η_Q) = φ(η_P)` and `ord_Q = ord_P` on `k(Z)`. -/
private theorem exists_transformPrimeDivisor_eq_some (hφ : IsSmall k sZ sX φ)
    (hφ' : IsSmall k sZ sX' φ') {g : X.RationalMap X'} (hg : IsModificationOf φ φ' g)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ Q : MMP.Mori.PrimeDivisor X', MMP.Mori.RationalMap.transformPrimeDivisor g P = some Q ∧
      φ' Q.genericPoint = φ P.genericPoint ∧
      Q.divisorialValuation.comap (functionFieldMap φ') =
        P.divisorialValuation.comap (functionFieldMap φ) := by
  obtain ⟨Q, hQ, hv⟩ := exists_primeDivisor_map_eq hφ hφ' P
  exact ⟨Q, transformPrimeDivisor_eq_some_of_map_eq hφ hφ' g hg P Q hQ, hQ, hv⟩

/-- Under a modification `g` of a small contraction `φ` into a small contraction `φ⁺`, the
transform `g_* P` is defined on every prime divisor `P` of `X`. -/
theorem isSome_transformPrimeDivisor_of_isModificationOf (hφ : IsSmall k sZ sX φ)
    (hφ' : IsSmall k sZ sX' φ') {g : X.RationalMap X'} (hg : IsModificationOf φ φ' g)
    (P : MMP.Mori.PrimeDivisor X) :
    (MMP.Mori.RationalMap.transformPrimeDivisor g P).isSome := by
  obtain ⟨Q, hQ, -⟩ := exists_transformPrimeDivisor_eq_some hφ hφ' hg P
  rw [hQ]
  rfl

private theorem transformPrimeDivisor_get_spec (hφ : IsSmall k sZ sX φ)
    (hφ' : IsSmall k sZ sX' φ') {g : X.RationalMap X'} (hg : IsModificationOf φ φ' g)
    (P : MMP.Mori.PrimeDivisor X) :
    φ' ((MMP.Mori.RationalMap.transformPrimeDivisor g P).get
        (isSome_transformPrimeDivisor_of_isModificationOf hφ hφ' hg P)).genericPoint =
        φ P.genericPoint ∧
      ((MMP.Mori.RationalMap.transformPrimeDivisor g P).get
        (isSome_transformPrimeDivisor_of_isModificationOf hφ hφ' hg P)).divisorialValuation.comap
          (functionFieldMap φ') = P.divisorialValuation.comap (functionFieldMap φ) := by
  obtain ⟨Q, hQ, hQη, hQv⟩ := exists_transformPrimeDivisor_eq_some hφ hφ' hg P
  simp only [hQ, Option.get_some]
  exact ⟨hQη, hQv⟩

/-- Under a modification `g` of a small contraction `φ` into a small contraction `φ⁺`, the
transform `P ↦ g_* P` is a bijection from the prime divisors of `X` to those of `X⁺`. -/
theorem bijective_transformPrimeDivisor_get (hφ : IsSmall k sZ sX φ)
    (hφ' : IsSmall k sZ sX' φ') {g : X.RationalMap X'} (hg : IsModificationOf φ φ' g) :
    Function.Bijective fun P : MMP.Mori.PrimeDivisor X ↦
      (MMP.Mori.RationalMap.transformPrimeDivisor g P).get
        (isSome_transformPrimeDivisor_of_isModificationOf hφ hφ' hg P) := by
  refine ⟨fun P₁ P₂ h ↦ primeDivisor_eq_of_map_eq hφ ?_, fun Q ↦ ?_⟩
  · rw [← (transformPrimeDivisor_get_spec hφ hφ' hg P₁).1,
      ← (transformPrimeDivisor_get_spec hφ hφ' hg P₂).1]
    exact congrArg (fun Q : MMP.Mori.PrimeDivisor X' ↦ φ' Q.genericPoint) h
  · obtain ⟨P, hP, -⟩ := exists_primeDivisor_map_eq hφ' hφ Q
    exact ⟨P, primeDivisor_eq_of_map_eq hφ'
      ((transformPrimeDivisor_get_spec hφ hφ' hg P).1.trans hP)⟩

/-- For small contractions `φ : X ⟶ Z`, `φ⁺ : X⁺ ⟶ Z` and a modification `g : X ⤏ X⁺` of `φ`
into `φ⁺`, the bijection `P ↦ g_* P` from the prime divisors of `X` to those of `X⁺`
(`MMP.Mori.RationalMap.transformPrimeDivisor g`, defined everywhere). -/
noncomputable def primeDivisorEquivOfModification (hφ : IsSmall k sZ sX φ)
    (hφ' : IsSmall k sZ sX' φ') {g : X.RationalMap X'} (hg : IsModificationOf φ φ' g) :
    MMP.Mori.PrimeDivisor X ≃ MMP.Mori.PrimeDivisor X' :=
  Equiv.ofBijective _ (bijective_transformPrimeDivisor_get hφ hφ' hg)

/-- `primeDivisorEquivOfModification` is the transform `P ↦ g_* P`. -/
theorem transformPrimeDivisor_eq_some_primeDivisorEquivOfModification (hφ : IsSmall k sZ sX φ)
    (hφ' : IsSmall k sZ sX' φ') {g : X.RationalMap X'} (hg : IsModificationOf φ φ' g)
    (P : MMP.Mori.PrimeDivisor X) :
    MMP.Mori.RationalMap.transformPrimeDivisor g P =
      some (primeDivisorEquivOfModification hφ hφ' hg P) :=
  (Option.some_get _).symm

/-- `g_* P` and `P` have the same valuation on `k(Z)`: `ord_{g_* P} ∘ φ⁺^* = ord_P ∘ φ^*`. -/
theorem divisorialValuation_comap_primeDivisorEquivOfModification (hφ : IsSmall k sZ sX φ)
    (hφ' : IsSmall k sZ sX' φ') {g : X.RationalMap X'} (hg : IsModificationOf φ φ' g)
    (P : MMP.Mori.PrimeDivisor X) :
    (primeDivisorEquivOfModification hφ hφ' hg P).divisorialValuation.comap
        (functionFieldMap φ') =
      P.divisorialValuation.comap (functionFieldMap φ) :=
  (transformPrimeDivisor_get_spec hφ hφ' hg P).2

end PrimeDivisorEquiv

/-- Let `φ : X ⟶ Z` and `φ⁺ : X⁺ ⟶ Z` be small birational contractions of normal varieties, and
`g : X ⤏ X⁺` the induced birational map over `Z`. Then a divisor of `k(X) = k(X⁺)` (identified
over `k(Z)`) is exceptional with nonempty center on `X` iff it is so on `X⁺`, and `g` maps the
prime divisors of `X` bijectively onto those of `X⁺`, preserving their valuations: `g_* P` is
`primeDivisorEquivOfModification hφ hφ' hg P`, and `ord_{g_* P} = ord_P` on `k(Z)`. -/
@[mmp "lem_fa4_flip_same_exceptional_divisors"]
public theorem exceptional_hasNonemptyCenter_iff_of_isSmall {k : Type u} [Field k]
    {X X' Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian X'] [IsNormal X] [IsNormal X']
    (φ : X ⟶ Z) (φ' : X' ⟶ Z) [IsDominant φ] [IsDominant φ']
    (hφ : IsSmall k sZ sX φ) (hφ' : IsSmall k sZ sX' φ') :
    (∀ (v : Valuation X.functionField ℤᵐ⁰) (v' : Valuation X'.functionField ℤᵐ⁰),
      v.comap (functionFieldMap φ) = v'.comap (functionFieldMap φ') →
      ((HasNonemptyCenter k sX v ∧
          ∃ D : ProperDivisorOver k sX, D.valuation = v ∧ D.IsExceptional) ↔
        (HasNonemptyCenter k sX' v' ∧
          ∃ D : ProperDivisorOver k sX', D.valuation = v' ∧ D.IsExceptional))) ∧
    ∀ (g : X.RationalMap X') (hg : IsModificationOf φ φ' g),
      ∀ P : Mori.PrimeDivisor X,
        Mori.RationalMap.transformPrimeDivisor g P =
            some (primeDivisorEquivOfModification hφ hφ' hg P) ∧
          (primeDivisorEquivOfModification hφ hφ' hg P).divisorialValuation.comap
              (functionFieldMap φ') =
            P.divisorialValuation.comap (functionFieldMap φ) :=
  ⟨fun _ _ h => ⟨hasNonemptyCenter_isExceptional_of_comap_eq hφ hφ' h,
      hasNonemptyCenter_isExceptional_of_comap_eq hφ' hφ h.symm⟩, fun _ hg P =>
    ⟨transformPrimeDivisor_eq_some_primeDivisorEquivOfModification hφ hφ' hg P,
      divisorialValuation_comap_primeDivisorEquivOfModification hφ hφ' hg P⟩⟩

end MMP.Flips
