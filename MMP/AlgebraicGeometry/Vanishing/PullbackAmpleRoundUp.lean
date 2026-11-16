module

public import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
public import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.Untwisting
public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.OpenSubscheme
public import MMP.AlgebraicGeometry.Curves.Maps.CoefficientSpace
public import MMP.AlgebraicGeometry.Vanishing.KawamataViehwegRoundUp
public import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
public import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
public import MMP.AlgebraicGeometry.SpreadingOut.CountableFieldOfDefinition

/-!
# Relative round-up vanishing for the pull-back of a relatively ample divisor

Let `f : X ⟶ S` be a projective morphism of varieties over an algebraically closed field `k` of
characteristic zero, `p : Y ⟶ X` a projective birational morphism with `Y` smooth, `K` a
canonical divisor of `Y`, and `L` an `f`-ample `ℚ`-Cartier divisor on `X`. If the fractional
part of the `ℚ`-divisor `p^*L` on `Y` has simple normal crossing support, then
`R^i (p ≫ f)_* 𝒪_Y(K + ⌈p^*L⌉) = 0` for every `i > 0`.

The divisor `p^*L` is only `(p ≫ f)`-nef and big, not `(p ≫ f)`-ample, so this is not a special
case of `MMP.Fourfold.isZero_rightDerived_pushforward_divisorialSheaf_canonical_add_roundUp`.
The proof compactifies over a projective closure of an affine chart of `S`, extending a
multiple of `L` as a relatively ample line bundle before pulling it back, and applies the
projective round-up vanishing to the twists by a large multiple of the hyperplane at infinity.

## Main results

* `MMP.Fourfold.isZero_rightDerived_pushforward_comp_roundUp_of_pullback_iso` is the vanishing
  for an `f`-ample invertible sheaf `𝓐` on `X` and a divisor `w` on `Y` with `p^*𝓐 ≅ 𝒪_Y(w)`,
  with `w/m` in place of `p^*L`.
* `MMP.Fourfold.isZero_rightDerived_pushforward_comp_divisorialSheaf_canonical_add_roundUp_pullback`
  is the vanishing above, its case `𝓐 = 𝒪_X(A)`.

## Implementation notes

* The source works over `ℂ`; the statement is over any algebraically closed field of
  characteristic zero.
* A `ℚ`-Cartier divisor on `X` is `(1/m) • A` for a Cartier divisor `A : X.CartierDivisor` and an
  integer `m > 0` (every element of `Div(X) ⊗ ℚ` has this form), and it is `f`-ample exactly
  when `A` is (`MMP.Resolution.IsRelativelyAmpleCartier`). No normality of `X` is assumed.
* `p^*L` is the `ℚ`-divisor `(1/m) • w` on `Y`, where `A'` is the pull-back of `A` along `p`
  (`MMP.Intersection.IsPullback`) and `w` is the Weil divisor of `A'`
  (`MMP.Intersection.IsWeilDivisorOfCartier`).
* "The fractional support of `p^*L` is snc" is `MMP.Mori.DivisorWithCoeffs.IsSNC` of
  `MMP.Mori.DivisorWithCoeffs.fract (p^*L)`, and `⌈p^*L⌉` is
  `MMP.Mori.DivisorWithCoeffs.roundUp`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Thm. 2.64,
  Cor. 2.68
-/

@[expose] public section

section

/-!
## Proof: Relative round-up vanishing for the pull-back of a relatively ample divisor

Let `f : X ⟶ S` be a projective morphism of varieties over an algebraically closed field of
characteristic zero, `p : Y ⟶ X` a projective birational morphism with `Y` smooth, `K` a
canonical divisor of `Y`, and `L = (1/m) A` an `f`-ample `ℚ`-Cartier divisor, `A` Cartier. If the
fractional part of `p^*L = (1/m) [p^*A]` has simple normal crossing support, then
`Rⁱ(p ≫ f)_* 𝒪_Y(K + ⌈p^*L⌉) = 0` for `i > 0`.

Higher direct images vanish once the cohomology of every preimage `W = p⁻¹(f⁻¹(V))` of an affine
open `V ⊆ S` does. A power of `𝒪_X(A)` embeds `f⁻¹(V)` into `ℙᴹ_V ⊆ ℙᴹ × ℙʳ`; its closure `X₀` is a
projective variety carrying an ample family `A_a = A_0 ⊗ H^{⊗ a}` with `H` cutting out the boundary
`X₀ ∖ f⁻¹(V)`. Closing `W ⟶ ℙᴺ_{f⁻¹(V)} ⊆ ℙᴺ_{X₀}` gives a projective variety `Y₀ ⊇ W` with a
projective birational `q : Y₀ ⟶ X₀` and `q⁻¹(f⁻¹(V)) = W`. A log resolution of `Y₀` which is an
isomorphism over `W` and makes the boundary snc compactifies `W` to a smooth projective `Ȳ`. The
ample `A_a` on `X₀` pull back to nef and big divisors `L + aE + Δ` on `Ȳ` extending `p^*L` by
integral multiples of the boundary `E`, which do not change the round-up on `W`. Kawamata–Viehweg
vanishing for round-ups on `Ȳ`, and the fact that `Hⁱ(W, -)` is the colimit of
`Hⁱ(Ȳ, - ⊗ 𝒪(aE))` (Stacks, Tag 09MR), give the vanishing over `W`.

## Main results

* The key step is `isZero_hgroup_preimage`, the vanishing over the preimage of one affine open
  of `S`.

## Implementation notes

* The pull-back `p^*𝒪_X(A) ≅ 𝒪_Y(p^*A)` along the dominant `p` is proved here
  (`nonempty_pullback_sheaf_iso`), and `𝒪_Y(p^*A) ≅ 𝒪_Y([p^*A])` on the normal `Y` is
  `MMP.Intersection.IsWeilDivisorOfCartier.sheafIsoDivisorialSheaf`.
* The ample class is extended to `X₀` before it is pulled back to `Ȳ`: `p^*L` itself need not
  be `(p ≫ f)`-ample, only nef and big after compactification.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Thm. 2.64,
  Cor. 2.68
-/

namespace MMP.FourfoldProofs.FourfoldPullbackAmpleRelativeVanishingProof

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.SheafOfModules Stacks.Cohomology.TwistedGradedModule

section Endgame

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

/-- **Cohomology of the nonvanishing open from vanishing of all twists.** Let `X` be a
quasi-compact quasi-separated scheme, `ℒ` an invertible module, `s ∈ Γ(X, ℒ)` and `𝒢` a
quasi-coherent module with `Hⁿ(X, 𝒢 ⊗ ℒ^{⊗ k}) = 0` for every `k ≥ 0`. Then `Hⁿ(X_s, 𝒢) = 0`
(cf. [Stacks, Tag 09MR]). -/
private theorem isZero_hgroup_nonvanishingOpen {X : Scheme.{0}} [QuasiSeparatedSpace X]
    [CompactSpace X]
    (L : SheafOfModules.{0} (structureSheafRing X.toRingedSpace))
    [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]
    (s : L.sections) (G : X.Modules) [G.IsQuasicoherent] (n : ℕ)
    (h : ∀ k : ℕ, IsZero (Hgroup X.ringCatSheaf ⊤ n (twist X L G (k : ℤ)))) :
    IsZero (Hgroup X.ringCatSheaf (nonvanishingOpen L s) n G) := by
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  refine ⟨fun η η' => ?_⟩
  suffices hz : ∀ η : Hgroup X.ringCatSheaf (nonvanishingOpen L s) n G, η = 0 by
    rw [hz η, hz η']
  intro η
  obtain ⟨-, hext⟩ := SectionPowerAnnihilation.annihilates_and_extends_of_isCompact s ⊤
    isCompact_univ n
  obtain ⟨k, ξ, hξ⟩ := hext (nonvanishingOpen L s) le_top (top_inf_eq _).symm G inferInstance η
  have hξ0 : ξ = 0 := by
    have := AddCommGrpCat.isZero_iff_subsingleton.mp (h k)
    exact Subsingleton.elim _ _
  rw [hξ0, map_zero] at hξ
  have hiso := Untwisting.isIso_hfunctor_map_sectionPowerAction X L s G k
    (nonvanishingOpen L s) le_rfl n
  have hinj : Function.Injective (ConcreteCategory.hom ((Hfunctor X.ringCatSheaf
      (nonvanishingOpen L s) n).map (SectionPowerComposition.mul X L s G k))) :=
    (ConcreteCategory.bijective_of_isIso _).1
  exact hinj (hξ.symm.trans (map_zero _).symm)

end Endgame

section SheafPullback

open MMP.Intersection MMP
open MMP.CartierDivisorSheaf Opposite
  TopologicalSpace

section KModel

variable {X : Scheme.{0}} [IsIntegral X]

private noncomputable def ιK (U : X.Opens) :
    X.functionField →+* X.totalQuotientSheaf.obj.obj (op U) :=
  ((functionFieldToTotalQuotientSheaf X).app (op U)).hom

private theorem genericPoint_mem {U : X.Opens} (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U := by
  obtain ⟨x, hx⟩ := hU
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, Set.mem_univ _, hx⟩

private theorem ιK_germ (U : X.Opens) (h : genericPoint X ∈ U) (a : Γ(X, U)) :
    ιK U (X.presheaf.germ U (genericPoint X) h a) = toK U a :=
  functionFieldToTotalQuotientSheaf_germ X U a h

private theorem ιK_res {U V : X.Opens} (h : V ≤ U) (c : X.functionField) :
    resK h (ιK U c) = ιK V c :=
  (congrArg (fun φ => φ.hom c)
    ((functionFieldToTotalQuotientSheaf X).naturality (homOfLE h).op)).symm

private theorem ιK_injective (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Function.Injective (ιK U) :=
  functionFieldToTotalQuotientSheaf_app_injective X U hU

private theorem ιK_surjective (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ιK U) := by
  intro s
  have : Nonempty U := hU.to_subtype
  obtain ⟨a, ha⟩ := exists_eq_constantSheafOnSpace_section X X.functionField U inferInstance
    (((totalQuotientSheafIsoConstant X).val.hom.hom.app (op U)) s)
  refine ⟨a, ?_⟩
  change ((totalQuotientSheafIsoConstant X).val.inv.hom.app (op U))
    (((toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U)) a) = s
  rw [← ha]
  exact ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (op U)) (totalQuotientSheafIsoConstant X).val.hom_inv_id) s

end KModel

section Dominant

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

private theorem functionFieldMap_germ (U : X.Opens) (hU : genericPoint X ∈ U) (a : Γ(X, U))
    (hY : genericPoint Y ∈ g ⁻¹ᵁ U) :
    functionFieldMap g (X.presheaf.germ U (genericPoint X) hU a) =
      Y.presheaf.germ (g ⁻¹ᵁ U) (genericPoint Y) hY (g.app U a) := by
  have hx : g (genericPoint Y) ∈ U := hY
  have h1 := MMP.Mori.functionFieldMap_algebraMap_stalk g (genericPoint Y)
    (X.presheaf.germ U (g (genericPoint Y)) hx a)
  have hn : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  have hn' : Nonempty (g ⁻¹ᵁ U) := ⟨⟨genericPoint Y, hY⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := U) hx a] at h1
  have hx' : genericPoint Y ∈ g ⁻¹ᵁ U := hY
  erw [Scheme.Hom.germ_stalkMap_apply g U (genericPoint Y) hx a] at h1
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) (U := g ⁻¹ᵁ U) hx' _] at h1
  exact h1

end Dominant

section LocalFraction

variable {Z : Scheme.{0}}

private theorem exists_common_rep (x : Z) (a b : Z.presheaf.stalk x) :
    ∃ (U : Z.Opens) (hx : x ∈ U) (A B : Γ(Z, U)),
      Z.presheaf.germ U x hx A = a ∧ Z.presheaf.germ U x hx B = b := by
  obtain ⟨U₁, hx₁, A₁, rfl⟩ := Z.presheaf.exists_germ_eq a
  obtain ⟨U₂, hx₂, B₂, rfl⟩ := Z.presheaf.exists_germ_eq b
  refine ⟨U₁ ⊓ U₂, ⟨hx₁, hx₂⟩, Z.presheaf.map (homOfLE inf_le_left).op A₁,
    Z.presheaf.map (homOfLE inf_le_right).op B₂, ?_, ?_⟩
  · exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  · exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

private theorem exists_local_fraction {D : Z.CartierDivisor} {x : Z} {U : Z.Opens} (hxU : x ∈ U)
    (A B : Γ(Z, U)) {e : Z.totalQuotientSheaf.presheaf.stalk x} (he : IsLocalEquationAt D x e)
    (hf : IsFraction e (Z.presheaf.germ U x hxU A) (Z.presheaf.germ U x hxU B)) :
    ∃ (U₀ : Z.Opens) (h₀ : U₀ ≤ U) (_ : x ∈ U₀) (f : (Z.totalQuotientSheaf.obj.obj (op U₀))ˣ),
      IsLocalEquationOn D U₀ f ∧
      toK U₀ (Z.presheaf.map (homOfLE h₀).op B) * (f : Z.totalQuotientSheaf.obj.obj (op U₀)) =
        toK U₀ (Z.presheaf.map (homOfLE h₀).op A) := by
  obtain ⟨U₁, hx₁, f₁, hf₁, rfl⟩ := he
  have h2 := hf.2
  rw [← germ_toTotalQuotient, ← germ_toTotalQuotient] at h2
  have hxW : x ∈ U ⊓ U₁ := ⟨hxU, hx₁⟩
  have e : Z.totalQuotientSheaf.presheaf.germ (U ⊓ U₁) x hxW
      (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op B) * resK inf_le_right (f₁ : _)) =
      Z.totalQuotientSheaf.presheaf.germ (U ⊓ U₁) x hxW
        (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op A)) := by
    rw [map_mul, ← resK_toK inf_le_left B, ← resK_toK inf_le_left A]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply]
    exact h2
  obtain ⟨U₀, hx₀, i, j, hij⟩ := Z.totalQuotientSheaf.presheaf.germ_eq x hxW hxW _ _ e
  have hij' : i = j := Subsingleton.elim _ _
  subst hij'
  refine ⟨U₀, i.le.trans inf_le_left, hx₀, MMP.Intersection.resUnit (i ≫ homOfLE inf_le_right) f₁,
    isLocalEquationOn_resUnit _ hf₁, ?_⟩
  have h3 : resK i.le (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op B) *
      resK inf_le_right (f₁ : _)) =
        resK i.le (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op A)) := hij
  rw [map_mul, ← resK_toK inf_le_left B, ← resK_toK inf_le_left A, resK_resK, resK_resK,
    resK_resK] at h3
  rw [← resK_toK _ B, ← resK_toK _ A]
  convert h3 using 2
  rfl

end LocalFraction

section Rho

private theorem subsingleton_totalQuotient_of_not_nonempty {Z : Scheme.{0}} {U : Z.Opens}
    (h : ¬ (U : Set Z).Nonempty) : Subsingleton (Z.totalQuotientSheaf.obj.obj (op U)) := by
  have : U = ⊥ := TopologicalSpace.Opens.coe_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp h)
  subst this
  exact CommRingCat.subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty Z.totalQuotientSheaf)

private def trivRingHom (R S : Type*) [NonAssocSemiring R] [NonAssocSemiring S] [Subsingleton S] :
    R →+* S where
  toFun _ := 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := rfl
  map_add' _ _ := Subsingleton.elim _ _

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

omit [IsIntegral X] [IsIntegral Y] [IsDominant g] in
private theorem not_nonempty_preimage {U : X.Opens} (h : ¬ (U : Set X).Nonempty) :
    ¬ ((g ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
  rintro ⟨y, hy⟩
  exact h ⟨g y, hy⟩

private theorem nonempty_preimage {U : X.Opens} (h : (U : Set X).Nonempty) :
    ((g ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
  have hη : genericPoint X ∈ U := genericPoint_mem h
  refine ⟨genericPoint Y, ?_⟩
  change g (genericPoint Y) ∈ U
  rw [map_genericPoint_of_isDominant g]; exact hη

open Classical in
/-- The ring map `𝓜_X(U) → 𝓜_Y(g⁻¹U)` induced by the extension of function fields. -/
private noncomputable def rho (U : X.Opens) :
    X.totalQuotientSheaf.obj.obj (op U) →+* Y.totalQuotientSheaf.obj.obj (op (g ⁻¹ᵁ U)) :=
  if hU : (U : Set X).Nonempty then
    (ιK (g ⁻¹ᵁ U)).comp ((functionFieldMap g).comp
      (RingEquiv.ofBijective (ιK U) ⟨ιK_injective U hU, ιK_surjective U hU⟩).symm.toRingHom)
  else
    haveI := subsingleton_totalQuotient_of_not_nonempty (not_nonempty_preimage g hU)
    trivRingHom _ _

private theorem rho_ιK {U : X.Opens} (hU : (U : Set X).Nonempty) (κ : X.functionField) :
    rho g U (ιK U κ) = ιK (g ⁻¹ᵁ U) (functionFieldMap g κ) := by
  unfold rho
  simp only [hU, ↓reduceDIte, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  have : (RingEquiv.ofBijective (ιK U) ⟨ιK_injective U hU, ιK_surjective U hU⟩).symm (ιK U κ) =
      κ :=
    (RingEquiv.ofBijective (ιK U) ⟨ιK_injective U hU, ιK_surjective U hU⟩).symm_apply_apply κ
  rw [this]

private theorem rho_res {U V : X.Opens} (h : V ≤ U) (σ : X.totalQuotientSheaf.obj.obj (op U)) :
    resK (g.preimage_mono h) (rho g U σ) = rho g V (resK h σ) := by
  by_cases hV : (V : Set X).Nonempty
  · have hU : (U : Set X).Nonempty := hV.mono h
    obtain ⟨κ, rfl⟩ := ιK_surjective U hU σ
    rw [rho_ιK g hU, ιK_res h, ιK_res (g.preimage_mono h), rho_ιK g hV]
  · have := subsingleton_totalQuotient_of_not_nonempty (not_nonempty_preimage g hV)
    exact Subsingleton.elim _ _

private theorem rho_toK (U : X.Opens) (a : Γ(X, U)) :
    rho g U (toK U a) = toK (g ⁻¹ᵁ U) (g.app U a) := by
  by_cases hU : (U : Set X).Nonempty
  · have hη : genericPoint X ∈ U := genericPoint_mem hU
    have hY : genericPoint Y ∈ g ⁻¹ᵁ U := genericPoint_mem (nonempty_preimage g hU)
    rw [← ιK_germ U hη a, rho_ιK g hU, functionFieldMap_germ g U hη a hY, ιK_germ _ hY]
  · have := subsingleton_totalQuotient_of_not_nonempty (not_nonempty_preimage g hU)
    exact Subsingleton.elim _ _

end Rho

section Key

private theorem exists_common_rep_le {Z : Scheme.{0}} (x : Z) (W : Z.Opens) (hxW : x ∈ W)
    (a b : Z.presheaf.stalk x) :
    ∃ (U : Z.Opens) (_ : U ≤ W) (hx : x ∈ U) (A B : Γ(Z, U)),
      Z.presheaf.germ U x hx A = a ∧ Z.presheaf.germ U x hx B = b := by
  obtain ⟨U, hx, A, B, h1, h2⟩ := exists_common_rep x a b
  refine ⟨U ⊓ W, inf_le_right, ⟨hx, hxW⟩, Z.presheaf.map (homOfLE inf_le_left).op A,
    Z.presheaf.map (homOfLE inf_le_left).op B, ?_, ?_⟩
  · rw [← h1]; exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  · rw [← h2]; exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

private theorem mul_left_cancel_totalQuotient {Z : Scheme.{0}} [IsIntegral Z] {V : Z.Opens}
    (hV : (V : Set Z).Nonempty) {B x y : Z.totalQuotientSheaf.obj.obj (op V)} (hB : B ≠ 0)
    (h : B * x = B * y) : x = y := by
  obtain ⟨x', rfl⟩ := ιK_surjective V hV x
  obtain ⟨y', rfl⟩ := ιK_surjective V hV y
  obtain ⟨B', rfl⟩ := ιK_surjective V hV B
  have hB' : B' ≠ 0 := fun h0 => hB (by rw [h0, map_zero])
  have h' : B' * x' = B' * y' := ιK_injective V hV (by simpa only [map_mul] using h)
  rw [mul_left_cancel₀ hB' h']

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

/-- Local equations of a pull-back are the pulled-back local equations. -/
private theorem exists_local_pullback_equation {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') (y : Y) (W : X.Opens) (hW : g y ∈ W) :
    ∃ (U₀ : X.Opens) (_ : U₀ ≤ W) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U₀) (_ : y ∈ V)
      (f₀ : (X.totalQuotientSheaf.obj.obj (op U₀))ˣ) (f' : (Y.totalQuotientSheaf.obj.obj (op V))ˣ),
      IsLocalEquationOn E U₀ f₀ ∧ IsLocalEquationOn E' V f' ∧
        resK hV (rho g U₀ (f₀ : X.totalQuotientSheaf.obj.obj (op U₀))) =
          (f' : Y.totalQuotientSheaf.obj.obj (op V)) := by
  obtain ⟨a, b, ⟨e, he, hf⟩, -, hb, e', he', hf'⟩ := h.2 y
  obtain ⟨U, hUW, hxU, A, B, rfl, rfl⟩ := exists_common_rep_le (g y) W hW a b
  obtain ⟨U₀, h₀, hx₀, f₀, hf₀, hAB⟩ := exists_local_fraction hxU A B he hf
  have hyU₀ : y ∈ g ⁻¹ᵁ U₀ := hx₀
  set A₀ := X.presheaf.map (homOfLE h₀).op A with hA₀
  set B₀ := X.presheaf.map (homOfLE h₀).op B with hB₀
  have hgA : X.presheaf.germ U₀ (g y) hx₀ A₀ = X.presheaf.germ U (g y) hxU A :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hgB : X.presheaf.germ U₀ (g y) hx₀ B₀ = X.presheaf.germ U (g y) hxU B :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hfr : IsFraction e' (Y.presheaf.germ (g ⁻¹ᵁ U₀) y hyU₀ (g.app U₀ A₀))
      (Y.presheaf.germ (g ⁻¹ᵁ U₀) y hyU₀ (g.app U₀ B₀)) := by
    rw [← Scheme.Hom.germ_stalkMap_apply g U₀ y hx₀, ← Scheme.Hom.germ_stalkMap_apply g U₀ y hx₀,
      hgA, hgB]
    exact hf'
  obtain ⟨V, h₁, hy₁, f', hf'', hAB'⟩ := exists_local_fraction hyU₀ _ _ he' hfr
  refine ⟨U₀, h₀.trans hUW, V, h₁, hy₁, f₀, f', hf₀, hf'', ?_⟩
  have hne : toK V (Y.presheaf.map (homOfLE h₁).op (g.app U₀ B₀)) ≠ 0 := by
    intro h0
    have h1 : Y.presheaf.map (homOfLE h₁).op (g.app U₀ B₀) = 0 :=
      MMP.Intersection.injective_toTotalQuotient V (by rw [h0, map_zero])
    have h2 : Y.presheaf.germ V y hy₁ (Y.presheaf.map (homOfLE h₁).op (g.app U₀ B₀)) =
        (g.stalkMap y).hom (X.presheaf.germ U (g y) hxU B) := by
      erw [TopCat.Presheaf.germ_res_apply]
      rw [← hgB]
      exact (Scheme.Hom.germ_stalkMap_apply g U₀ y hx₀ B₀).symm
    rw [h1, map_zero] at h2
    rw [← h2] at hb
    exact zero_notMem_nonZeroDivisors hb
  have e1 := congrArg (fun t => resK h₁ (rho g U₀ t)) hAB
  simp only [map_mul] at e1
  rw [rho_toK, rho_toK, resK_toK, resK_toK] at e1
  exact mul_left_cancel_totalQuotient ⟨y, hy₁⟩ hne (e1.trans hAB'.symm)

private theorem resK_rho_inv {U₀ : X.Opens} {V : Y.Opens} (hV : V ≤ g ⁻¹ᵁ U₀)
    {f₀ : (X.totalQuotientSheaf.obj.obj (op U₀))ˣ} {f' : (Y.totalQuotientSheaf.obj.obj (op V))ˣ}
    (hff : resK hV (rho g U₀ (f₀ : X.totalQuotientSheaf.obj.obj (op U₀))) =
      (f' : Y.totalQuotientSheaf.obj.obj (op V))) :
    resK hV (rho g U₀ (↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀))) =
      (↑f'⁻¹ : Y.totalQuotientSheaf.obj.obj (op V)) := by
  have hinv : resK hV (rho g U₀ (↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀))) *
      (f' : Y.totalQuotientSheaf.obj.obj (op V)) = 1 := by
    rw [← hff, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  exact Units.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hinv)

/-- The pull-back of a section of `𝒪_X(E)` over `W` is a section of `𝒪_Y(E')` over `g⁻¹W`. -/
private theorem mem_rho {E : X.CartierDivisor} {E' : Y.CartierDivisor} (h : IsPullback g E E')
    (W : X.Opens) (s : X.totalQuotientSheaf.obj.obj (op W)) (hs : Mem E W s) :
    Mem E' (g ⁻¹ᵁ W) (rho g W s) := by
  refine Mem.of_locally fun y hy => ?_
  obtain ⟨U₀, hU₀, V, hV, hyV, f₀, f', hf₀, hf', hff⟩ := exists_local_pullback_equation g h y W hy
  refine ⟨V, hV.trans (g.preimage_mono hU₀), hyV, ?_⟩
  refine (mem_iff (U := V) (V := V) hf' le_rfl _).2 ?_
  obtain ⟨C, hC⟩ := (mem_iff (U := U₀) (V := U₀) hf₀ le_rfl _).1 (hs.res hU₀)
  refine ⟨Y.presheaf.map (homOfLE hV).op (g.app U₀ C), ?_⟩
  have e1 : resK (hV.trans (g.preimage_mono hU₀)) (rho g W s) =
      resK hV (rho g U₀ (resK hU₀ s)) := by
    rw [← rho_res g hU₀ s, resK_resK]
  rw [e1, ← hC, map_mul, map_mul, rho_toK, resK_toK]
  simp only [resK_id]
  rw [resK_rho_inv g hV hff]

private theorem epi_of_surjective_on_covering {Z : Scheme.{0}} (B : Z.Opens → Prop)
    (hB : ∀ (U : Z.Opens) (T : CategoryTheory.Sieve U),
      (∀ ⦃V : Z.Opens⦄ (f : V ⟶ U), B V → T f) → T ∈ Opens.grothendieckTopology Z U)
    {M N : Z.Modules} (φ : M ⟶ N)
    (hφ : ∀ V : Z.Opens, B V → Function.Surjective (φ.val.app (op V))) : Epi φ := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Z)
      ((SheafOfModules.toSheaf Z.ringCatSheaf).map φ).hom :=
    ⟨fun s => hB _ _ fun V f hV => hφ V hV (N.val.map f.op s)⟩
  exact (SheafOfModules.toSheaf Z.ringCatSheaf).epi_of_epi_map (Sheaf.epi_of_isLocallySurjective _)

/-- The map `𝒪_X(E) ⟶ g_* 𝒪_Y(E')`, `s ↦ g^*s`. -/
private noncomputable def lambdaPre {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') :
    (MMP.CartierDivisor.sheaf E).val ⟶
      ((Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf E')).val :=
    (PresheafOfModules.homMk
      { app := fun U => AddCommGrpCat.ofHom
          { toFun := fun s => (⟨rho g U.unop (MMP.CartierDivisorSheaf.sectionVal s),
              mem_rho g h U.unop _ (show ↥((MMP.CartierDivisor.sheafSubmodule E).obj U) from s).2⟩ :
                ↥((MMP.CartierDivisor.sheafSubmodule E').obj (op (g ⁻¹ᵁ U.unop))))
            map_zero' := Subtype.ext (by change rho g U.unop 0 = 0; exact map_zero _)
            map_add' := fun s t => Subtype.ext (by
              exact map_add (rho g U.unop) _ _) }
        naturality := fun {U V} i => by
          ext s
          exact Subtype.ext (rho_res g i.unop.le _).symm }
      (fun U r s => Subtype.ext (by
        change rho g U.unop (toK U.unop r * MMP.CartierDivisorSheaf.sectionVal s) =
          toK (g ⁻¹ᵁ U.unop) (g.app U.unop r) *
            rho g U.unop (MMP.CartierDivisorSheaf.sectionVal s)
        rw [map_mul]
        exact congrArg (· * rho g U.unop (MMP.CartierDivisorSheaf.sectionVal s))
          (rho_toK g U.unop r))))

private noncomputable def lambdaHom {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') :
    MMP.CartierDivisor.sheaf E ⟶ (Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf E') :=
  (SheafOfModules.fullyFaithfulForget _).preimage (lambdaPre g h)

private theorem lambdaHom_val {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') : (lambdaHom g h).val = lambdaPre g h :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).map_preimage
    (show (SheafOfModules.forget X.ringCatSheaf).obj (MMP.CartierDivisor.sheaf E) ⟶
      (SheafOfModules.forget X.ringCatSheaf).obj
        ((Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf E')) from lambdaPre g h)

private theorem sectionVal_lambdaHom_app {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') (U : X.Opens) (s : Γ(MMP.CartierDivisor.sheaf E, U)) :
    MMP.CartierDivisorSheaf.sectionVal ((lambdaHom g h).app U s) =
      rho g U (MMP.CartierDivisorSheaf.sectionVal s) := by
  have := congrArg (fun φ => φ.app (op U) s) (lambdaHom_val g h)
  exact congrArg MMP.CartierDivisorSheaf.sectionVal this

end Key

private noncomputable abbrev sh {X : Scheme.{0}} (D : X.CartierDivisor) : X.Modules :=
  MMP.CartierDivisor.sheaf D

/-- **Pull-back of the sheaf of a Cartier divisor.** The pull-back of `𝒪_X(D)` along a dominant
morphism of integral schemes is `𝒪_Y(D')` for `D'` a pull-back of `D`: the map
`g^*𝒪_X(D) ⟶ 𝒪_Y(D')` adjoint to pulling back rational sections is an epimorphism of invertible
sheaves, hence an isomorphism. -/
private theorem nonempty_pullback_sheaf_iso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ X) [IsDominant g]
    {D : X.CartierDivisor} {D' : Y.CartierDivisor} (hD' : MMP.Intersection.IsPullback g D D') :
    Nonempty ((Scheme.Modules.pullback g).obj (sh D) ≅
      sh D') := by
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (sh D) := inferInstance
  have : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (sh D') := inferInstance
  have hinvpb : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj (sh D)) :=
    SheafOfModules.isInvertible_pullback g _
  let ℓ := lambdaHom g hD'
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  let ψ : (Scheme.Modules.pullback g).obj (sh D) ⟶
      sh D' := (adj.homEquiv _ _).symm ℓ
  have hψ : ∀ (U : X.Opens) (s : Γ(sh D, U)),
      ψ.app (g ⁻¹ᵁ U) ((adj.unit.app (sh D)).app U s) =
        ℓ.app U s := by
    have h1 : ℓ = adj.unit.app (sh D) ≫
        (Scheme.Modules.pushforward g).map ψ := by
      have := (adj.homEquiv _ _).apply_symm_apply ℓ
      rw [Adjunction.homEquiv_unit] at this
      exact this.symm
    intro U s
    exact (congrArg (fun φ => φ.app U s) h1).symm
  have hepi : Epi ψ := by
    refine epi_of_surjective_on_covering
      (fun V : Y.Opens => Function.Surjective (ψ.app V)) ?_ ψ (fun V hV => hV)
    intro U T hT
    rw [Opens.mem_grothendieckTopology]
    intro y hy
    obtain ⟨U₀, -, V₀, hV₀, hyV₀, f₀, f', hf₀, hf', hff⟩ :=
      exists_local_pullback_equation g hD' y ⊤ trivial
    refine ⟨V₀ ⊓ U, homOfLE inf_le_right, hT (homOfLE inf_le_right) ?_, ⟨hyV₀, hy⟩⟩
    have hVV₀ : V₀ ⊓ U ≤ V₀ := inf_le_left
    intro t
    have hmem : Mem D' (V₀ ⊓ U) (MMP.CartierDivisorSheaf.sectionVal t) :=
      (show ↥((MMP.CartierDivisor.sheafSubmodule D').obj (op (V₀ ⊓ U))) from t).2
    obtain ⟨a, ha⟩ := (mem_iff (U := V₀) (V := V₀ ⊓ U) hf' hVV₀ _).1 hmem
    let e₀ : Γ(sh D, U₀) :=
      (⟨(↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀)), mem_inv hf₀⟩ :
        ↥((MMP.CartierDivisor.sheafSubmodule D).obj (op U₀)))
    let ε := (adj.unit.app (sh D)).app U₀ e₀
    refine ⟨a • ((Scheme.Modules.pullback g).obj
      (sh D)).presheaf.map
        (homOfLE (hVV₀.trans hV₀)).op ε, ?_⟩
    apply MMP.CartierDivisorSheaf.sectionVal_injective
    rw [Scheme.Modules.Hom.app_smul]
    have nat := PresheafOfModules.naturality_apply ψ.val (homOfLE (hVV₀.trans hV₀)).op ε
    have h4 := nat.trans (congrArg
      ((sh D').val.map (homOfLE (hVV₀.trans hV₀)).op)
      (hψ U₀ e₀))
    have h3 : MMP.CartierDivisorSheaf.sectionVal
        (ψ.app (V₀ ⊓ U) (((Scheme.Modules.pullback g).obj
          (sh D)).presheaf.map
            (homOfLE (hVV₀.trans hV₀)).op ε)) =
        resK (hVV₀.trans hV₀) (rho g U₀ (↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀))) := by
      have h5 := congrArg MMP.CartierDivisorSheaf.sectionVal h4
      refine h5.trans ?_
      exact congrArg (resK (hVV₀.trans hV₀)) (sectionVal_lambdaHom_app g hD' U₀ e₀)
    change toK (V₀ ⊓ U) a * MMP.CartierDivisorSheaf.sectionVal
      (ψ.app (V₀ ⊓ U) (((Scheme.Modules.pullback g).obj
          (sh D)).presheaf.map
            (homOfLE (hVV₀.trans hV₀)).op ε)) = _
    rw [h3, ← ha, ← resK_resK hVV₀ hV₀, resK_rho_inv g hV₀ hff]
  exact ⟨@asIso _ _ _ _ ψ (Stacks.Chow.GenuineChern.isIso_of_epi_of_isInvertible ψ hinvpb
    inferInstance)⟩

end SheafPullback

section Main

open MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

private theorem roundUp_toQDivisor_add {X : Scheme.{0}} (D : Divisor X) (Δ : QDivisor X) :
    (Divisor.toQDivisor D + Δ).roundUp = D + Δ.roundUp := by
  ext E
  change (Divisor.toQDivisor D + Δ).roundUp.coeff E = D.coeff E + Δ.roundUp.coeff E
  rw [DivisorWithCoeffs.coeff_roundUp, DivisorWithCoeffs.coeff_roundUp,
    DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, Int.ceil_intCast_add]

/-- The prime divisor of `X` whose generic point is the image of the generic point of a prime
divisor of `W`, for an open immersion `u : W ⟶ X`. -/
private def openPrimeDivisor {W X : Scheme.{0}} (u : W ⟶ X) [IsOpenImmersion u]
    (P : MMP.Mori.PrimeDivisor W) :
    MMP.Mori.PrimeDivisor X :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne (u P.genericPoint)
    ((coheight_eq_of_isOpenImmersion u).trans P.coheight_genericPoint)

private theorem genericPoint_openPrimeDivisor {W X : Scheme.{0}} (u : W ⟶ X) [IsOpenImmersion u]
    (P : MMP.Mori.PrimeDivisor W) : (openPrimeDivisor u P).genericPoint = u P.genericPoint :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

/-- On a smooth variety a canonical divisor `K` of dimension `n` has `𝒪_X(K) ≅ ⋀ⁿ Ω_{X/k}`:
the defining isomorphism lives on the smooth locus, which is all of `X`. -/
private theorem nonempty_divisorialSheaf_iso_exteriorPower {k : Type} [Field k] {X : Scheme.{0}}
    {f : X ⟶ Spec (.of k)} (hsm : IsSmoothScheme f)
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor f n) :
    Nonempty (K.divisorialSheaf ≅
      Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n) :=
  MMP.Flips.nonempty_iso_of_restrict_iso hsm (hK.iso ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback (smoothLocus f).ι).app _ ≪≫
      Scheme.Modules.exteriorPowerPullbackIso (smoothLocus f).ι _ n ≪≫
      (Scheme.Modules.exteriorPowerFunctor _ n).mapIso
        (Scheme.Hom.etaleRelativeDifferentialsIso (smoothLocus f).ι f _ rfl)).symm)

/-- The pull-back of a canonical divisor of a smooth variety along an open immersion `ι` has
divisorial sheaf `⋀ⁿ Ω_{W/k}`. -/
private theorem nonempty_divisorialSheaf_iso_exteriorPower_of_isPullback {k : Type} [Field k]
    {W X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} (hsm : IsSmoothScheme sX)
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] (ι : W ⟶ X) [IsOpenImmersion ι] {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n)
    {hB : ∀ Z : irreducibleComponents W, ι (componentGenericPoint W Z) ∉ K.supp}
    {K' : Divisor W} (h : K.IsPullback ι hB K') :
    Nonempty (K'.divisorialSheaf ≅
      Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (ι ≫ sX)) n) := by
  have hKc : K.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm K
  obtain ⟨e⟩ := nonempty_divisorialSheaf_iso_exteriorPower hsm hK
  exact ⟨(Divisor.IsPullback.divisorialSheafIso (hBc := hKc) h) ≪≫
    (Scheme.Modules.pullback ι).mapIso e ≪≫
    Scheme.Modules.exteriorPowerPullbackIso ι _ n ≪≫
    (Scheme.Modules.exteriorPowerFunctor _ n).mapIso
      (Scheme.Hom.etaleRelativeDifferentialsIso ι sX _ rfl)⟩

/-- The coefficients of the pull-back of a Cartier divisor along an open immersion are those of
the corresponding prime divisors. -/
private theorem coeff_of_isPullback_of_isOpenImmersion {W X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian W] [IsNormal W] (ι : W ⟶ X) [IsOpenImmersion ι]
    {D : Divisor X} (hDc : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents W, ι (componentGenericPoint W Z) ∉ D.supp}
    {D' : Divisor W} (h : D.IsPullback ι hB D') (P : MMP.Mori.PrimeDivisor W) :
    D'.coeff P = D.coeff (openPrimeDivisor ι P) :=
  MMP.Positivity.coeff_eq_of_isPullback P _ (genericPoint_openPrimeDivisor ι P).symm hDc h

private theorem openPrimeDivisor_injective {W X : Scheme.{0}} (u : W ⟶ X) [IsOpenImmersion u] :
    Function.Injective (openPrimeDivisor u) := fun P Q h =>
  AlgebraicGeometry.PrimeDivisor.genericPoint_injective (u.isOpenEmbedding.injective (by
    rw [← genericPoint_openPrimeDivisor, h, genericPoint_openPrimeDivisor]))

private theorem openPrimeDivisor_eq_primeDivisorMap {W X : Scheme.{0}} (u : W ⟶ X)
    [IsOpenImmersion u] (P : MMP.Mori.PrimeDivisor W) :
    openPrimeDivisor u P = OpenWeilRestriction.primeDivisorMap u P :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_injective ((genericPoint_openPrimeDivisor u P).trans
    (OpenWeilRestriction.genericPoint_primeDivisorMap u P).symm)

/-- **Prime divisors through the complement of a support.** If an open immersion `ι : W ⟶ X` has
image `X ∖ Supp E`, then `E` has coefficient zero along the closure of every prime divisor of
`W`. -/
private theorem coeff_openPrimeDivisor_eq_zero {W X : Scheme.{0}} (ι : W ⟶ X) [IsOpenImmersion ι]
    {E : Divisor X} (h : Set.range ι = (E.supp : Set X)ᶜ) (P : MMP.Mori.PrimeDivisor W) :
    E.coeff (openPrimeDivisor ι P) = 0 := by
  by_contra hne
  have hmem : (openPrimeDivisor ι P).genericPoint ∈ (E.supp : Set X) :=
    DivisorWithCoeffs.support_subset_supp hne (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl)
  rw [genericPoint_openPrimeDivisor, ← Set.notMem_compl_iff, ← h] at hmem
  exact hmem ⟨_, rfl⟩

/-- **Comparison of divisorial sheaves along two open immersions.** Let `ι : W ⟶ X` and
`j : W ⟶ X'` be open immersions into smooth varieties over `k` compatible with the structure
morphisms, `K`, `K'` canonical divisors and `D`, `D'` divisors with the same coefficient along
corresponding prime divisors. Then `ι^* 𝒪_X(K + D) ≅ j^* 𝒪_{X'}(K' + D')`. -/
private theorem nonempty_restrict_divisorialSheaf_iso {k : Type} [Field k]
    {W X X' : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral X'] [CompactSpace X] [CompactSpace X']
    [IsLocallyNoetherian X] [IsLocallyNoetherian X'] [IsNormal X] [IsNormal X']
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (hsm : IsSmoothScheme sX) (hsm' : IsSmoothScheme sX')
    (ι : W ⟶ X) [IsOpenImmersion ι] (j : W ⟶ X') [IsOpenImmersion j]
    (hιj : ι ≫ sX = j ≫ sX') {n : ℕ} {K : Divisor X} {K' : Divisor X'}
    (hK : K.IsCanonicalDivisor sX n) (hK' : K'.IsCanonicalDivisor sX' n)
    (D : Divisor X) (D' : Divisor X')
    (hD : ∀ P : MMP.Mori.PrimeDivisor W,
      D.coeff (openPrimeDivisor ι P) = D'.coeff (openPrimeDivisor j P)) :
    Nonempty ((K + D).divisorialSheaf.restrict ι ≅ (K' + D').divisorialSheaf.restrict j) := by
  haveI : IsDominant ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion ι
  haveI : IsDominant j := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion j
  have hc : ∀ G : Divisor X, G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  have hc' : ∀ G : Divisor X', G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm'
  have hB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant ι
  have hB' := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant j
  obtain ⟨Kι, hKι⟩ := (hc K).exists_isPullback (hB K)
  obtain ⟨Dι, hDι⟩ := (hc D).exists_isPullback (hB D)
  obtain ⟨Kj, hKj⟩ := (hc' K').exists_isPullback (hB' K')
  obtain ⟨Dj, hDj⟩ := (hc' D').exists_isPullback (hB' D')
  have hDD : Dι = Dj := by
    ext P
    change Dι.coeff P = Dj.coeff P
    rw [coeff_of_isPullback_of_isOpenImmersion ι (hc D) hDι,
      coeff_of_isPullback_of_isOpenImmersion j (hc' D') hDj, hD P]
  subst hDD
  have hsum := Divisor.IsPullback.add (hc K) (hc D) (hB (K + D)) hKι hDι
  have hsum' := Divisor.IsPullback.add (hc' K') (hc' D') (hB' (K' + D')) hKj hDj
  have hKιc : Kι.IsCartier := hKι.isCartier (hc K)
  have hKjc : Kj.IsCartier := hKj.isCartier (hc' K')
  have hDc : Dι.IsCartier := hDι.isCartier (hc D)
  obtain ⟨eK⟩ := nonempty_divisorialSheaf_iso_exteriorPower_of_isPullback hsm ι hK hKι
  obtain ⟨eK'⟩ := nonempty_divisorialSheaf_iso_exteriorPower_of_isPullback hsm' j hK' hKj
  rw [hιj] at eK
  have e₁ : (K + D).divisorialSheaf.restrict ι ≅ (Kι + Dι).divisorialSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback ι).app _ ≪≫
      (Divisor.IsPullback.divisorialSheafIso (hBc := hc (K + D)) hsum).symm
  have e₂ : (K' + D').divisorialSheaf.restrict j ≅ (Kj + Dι).divisorialSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback j).app _ ≪≫
      (Divisor.IsPullback.divisorialSheafIso (hBc := hc' (K' + D')) hsum').symm
  exact ⟨e₁ ≪≫ (hKιc.divisorialSheafTensorIso hDc).symm ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso (eK ≪≫ eK'.symm)).app _ ≪≫
    hKjc.divisorialSheafTensorIso hDc ≪≫ e₂.symm⟩

/-- The tensor powers of `𝒪_X(E)` for a Cartier divisor `E`: `𝒪_X(E)^{⊗ k} ≅ 𝒪_X(kE)`. -/
private theorem nonempty_tensorPower_divisorialSheaf_iso {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {E : Divisor X} (hE : E.IsCartier) (k : ℕ) :
    haveI := hE.isInvertibleModule_divisorialSheaf
    Nonempty (Stacks.SheafOfModules.TensorPower.tensorPower
      (Stacks.SheafOfModules.sectionSiteRing X) (Stacks.SheafOfModules.sectionSiteSheaf X)
      E.divisorialSheaf (k : ℤ) ≅ (k • E).divisorialSheaf) := by
  haveI := hE.isInvertibleModule_divisorialSheaf
  induction k with
  | zero =>
    exact ⟨eqToIso (Stacks.SheafOfModules.TensorPower.tensorPower_zero _ _ _) ≪≫
      Divisor.divisorialSheafZeroIso.symm ≪≫ eqToIso (by rw [zero_nsmul])⟩
  | succ k ih =>
    obtain ⟨e⟩ := ih
    exact ⟨eqToIso (by rw [Nat.cast_succ]) ≪≫
      (Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso _ _ _ (k : ℤ)).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app E.divisorialSheaf ≪≫
      (hE.nsmul k).divisorialSheafTensorIso hE ≪≫ eqToIso (by rw [succ_nsmul])⟩

/-- The tensor powers of an invertible sheaf `M ≅ 𝒪_X(E)`, `E` Cartier, in the spelling of
`Stacks.Ample.tensorPowModule`: `M^{⊗ k} ≅ 𝒪_X(kE)`. -/
private theorem nonempty_tensorPowModule_iso_divisorialSheaf {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {E : Divisor X} (hE : E.IsCartier)
    (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] (e : M ≅ E.divisorialSheaf) (k : ℕ) :
    Nonempty (Stacks.Ample.tensorPowModule X M (k : ℤ) ≅ (k • E).divisorialSheaf) := by
  haveI := hE.isInvertibleModule_divisorialSheaf
  induction k with
  | zero =>
    exact ⟨Stacks.Ample.tensorPowModuleZeroIso X _ ≪≫ Divisor.divisorialSheafZeroIso.symm ≪≫
      eqToIso (by rw [zero_nsmul])⟩
  | succ k ih =>
    obtain ⟨e'⟩ := ih
    exact ⟨eqToIso (by rw [Nat.cast_succ]) ≪≫
      (Stacks.Ample.tensorPowModuleAddIso X _ (k : ℤ) 1).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso X e'
        (Stacks.Ample.tensorPowModuleOneIso X _ ≪≫ e) ≪≫
      (hE.nsmul k).divisorialSheafTensorIso hE ≪≫ eqToIso (by rw [succ_nsmul])⟩

/-- **The twists of a divisorial sheaf by `𝒪(E)` are divisorial.** For Cartier divisors `D`,
`E` on a Noetherian normal scheme, `𝒪_X(D) ⊗ 𝒪_X(E)^{⊗ k} ≅ 𝒪_X(D + kE)`. -/
private theorem nonempty_twist_divisorialSheaf_iso {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {D E : Divisor X} (hD : D.IsCartier) (hE : E.IsCartier) (k : ℕ) :
    haveI := hE.isInvertibleModule_divisorialSheaf
    Nonempty (twist X E.divisorialSheaf D.divisorialSheaf (k : ℤ) ≅
      (D + k • E).divisorialSheaf) := by
  haveI := hE.isInvertibleModule_divisorialSheaf
  obtain ⟨e⟩ := nonempty_tensorPower_divisorialSheaf_iso hE k
  exact ⟨((Stacks.SheafOfModules.Tensor.sheafTensor _).obj D.divisorialSheaf).mapIso e ≪≫
    hD.divisorialSheafTensorIso (hE.nsmul k)⟩

/-- The nonvanishing open of the canonical section `1` of `𝒪_X(E)`, for `E ≥ 0` Cartier, is the
complement of the support of `E`. -/
private theorem nonvanishingOpen_divisorialSheafOneSection {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {E : Divisor X} (hE : E.IsCartier) (hE0 : 0 ≤ E) :
    haveI := hE.isInvertibleModule_divisorialSheaf
    ((Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) E.divisorialSheaf
      (Stacks.SheafOfModules.sectionsOfTop (X := X.toRingedSpace) E.divisorialSheaf
        (MMP.Threefold.Mori.oneSection hE0)) : X.Opens) : Set X) = (E.supp : Set X)ᶜ :=
  (Stacks.AmpleBridge.nonvanishingLocus_sectionsOfTop _ _).trans
    (MMP.Threefold.Mori.nonvanishingLocus_oneSection hE0 hE)

/-- **EGA-projective over an H-projective variety is H-projective.** Over a field every scheme
has an ample invertible sheaf on the base, so the two notions of projectivity agree there
(Stacks, Tag 0B45); a projective morphism `g` to an H-projective `Y` is therefore H-projective,
and so is `g ≫ s_Y`. -/
private theorem isProjectiveMorphism_of_isProjective {k : Type} [Field k] {X Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (hY : IsProjectiveMorphism sY) (g : X ⟶ Y) (hg : IsProjective g) :
    IsProjectiveMorphism (g ≫ sY) ∧ IsProjectiveMorphism g := by
  have hS : HasAmpleInvertibleSheaf (Spec (.of k)) :=
    (hasAmpleInvertibleSheaf_iff _).mpr (Stacks.HProjective.exists_isAmple_of_isAffine _)
  have hsY : IsProjective sY :=
    (isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf sY hS).mpr hY
  have hc : IsProjective (g ≫ sY) := isProjective_comp_of_hasAmpleInvertibleSheaf g sY hS hsY hg
  have hcm := (isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf _ hS).mp hc
  haveI : IsProper sY := isProper_of_isProjectiveMorphism sY hY
  exact ⟨hcm, IsProjectiveMorphism.of_comp g sY hcm⟩

/-- **An open subscheme proper over an open is a full preimage.** Let `j : W ⟶ Y` be an open
immersion of a nonempty scheme into an integral scheme, `q : Y ⟶ Z` separated and `u : V ⟶ Z` an
open immersion with `j ≫ q = g ≫ u` for a proper `g`. Then `j(W) = q⁻¹(u(V))`: the lift of `j` to
`q⁻¹(u(V))` is open and proper, hence clopen, hence everything. -/
private theorem range_eq_preimage_range_of_isProper {W V Y Z : Scheme.{0}} [Nonempty W]
    [IsIntegral Y] (j : W ⟶ Y) [IsOpenImmersion j] (q : Y ⟶ Z) [IsSeparated q]
    (u : V ⟶ Z) [IsOpenImmersion u] (g : W ⟶ V) [IsProper g] (h : j ≫ q = g ≫ u) :
    Set.range j.base = q.base ⁻¹' Set.range u.base := by
  set Q : Y.Opens := q ⁻¹ᵁ u.opensRange
  have hjQ : Set.range j.base ⊆ Set.range Q.ι.base := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change q.base (j.base w) ∈ Set.range u.base
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  set j' := IsOpenImmersion.lift Q.ι j hjQ
  have hj'f : j' ≫ Q.ι = j := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion j' := by
    haveI : IsOpenImmersion (j' ≫ Q.ι) := by rw [hj'f]; infer_instance
    exact IsOpenImmersion.of_comp j' Q.ι
  have hcomp : j' ≫ (q ∣_ u.opensRange) = g ≫ u.isoOpensRange.hom := by
    rw [← cancel_mono u.opensRange.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hj'f,
      Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, h]
  haveI : IsProper (j' ≫ (q ∣_ u.opensRange)) := by rw [hcomp]; infer_instance
  haveI : IsProper j' := IsProper.of_comp j' (q ∣_ u.opensRange)
  obtain ⟨w⟩ := ‹Nonempty W›
  haveI : Nonempty Q := ⟨j' w⟩
  have huniv : Set.range j'.base = Set.univ :=
    (isClopen_iff.mp ⟨j'.isClosedMap.isClosed_range, j'.isOpenEmbedding.isOpen_range⟩).resolve_left
      (Set.Nonempty.ne_empty ⟨_, w, rfl⟩)
  rw [← hj'f, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, huniv, Set.image_univ,
    Scheme.Opens.range_ι]
  rfl

/-- The preimage of a quasi-compact open under a quasi-compact morphism is quasi-compact. -/
private theorem compactSpace_preimage {Y Z : Scheme.{0}} (f : Y ⟶ Z) [QuasiCompact f]
    {V : Z.Opens} (hV : IsCompact (V : Set Z)) : CompactSpace (f ⁻¹ᵁ V) :=
  isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := f) _ V.isOpen hV)

/-- The `i`-th coordinate section of `𝒪(1)` on `ℙⁿ_A` does not vanish exactly on the `i`-th
standard chart `D₊(Tᵢ)`. -/
private theorem mem_nonvanishingLocus_coordSectionTop_iff {A : Type} [CommRing A] (n : ℕ)
    (i : Fin (n + 1)) (z : projectiveSpaceOver n (Spec (.of A))) :
    z ∈ Stacks.Ample.nonvanishingLocus
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of A)))
        (MMP.Fourfold.coordSectionTop (A := A) n i) ↔
      z ∈ projectiveSpaceOver.standardChart n (Spec (.of A)) i :=
  MMP.Fourfold.mem_nonvanishingLocus_pullbackCoordSection_iff
    (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of A))) i z

/-- The data of a projective closure of an open `W ⊆ X` adapted to an invertible sheaf `L` on
`X`, in continuation-passing style: a projective variety `X₀ ⊇ W`, an invertible sheaf `H` on `X₀`
with a section `t` whose nonvanishing locus is `W`, and a sequence `A_a ≅ A_0 ⊗ H^{⊗ a}` of
invertible sheaves on `X₀`, ample for large `a`, with `A_0|_W ≅ L^{⊗ N}|_W` for some `N > 0`. -/
private abbrev InvertibleClosureData {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (W : X.Opens) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (C : Prop) : Prop :=
  ∀ (N : ℕ) (_ : 0 < N)
    (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Spec (.of k)) (_ : MMP.Mori.IsProjectiveVariety k s₀)
    (j : W.toScheme ⟶ X₀) (_ : IsOpenImmersion j) (_ : j ≫ s₀ = W.ι ≫ sX)
    (Hb : X₀.Modules) (_ : Stacks.Ample.IsInvertibleModule X₀ Hb) (t : Γ(Hb, ⊤))
    (_ : Set.range j = Stacks.Ample.nonvanishingLocus Hb t)
    (A : ℕ → X₀.Modules) (_ : ∀ a, Stacks.Ample.IsInvertibleModule X₀ (A a)) (a₀ : ℕ)
    (_ : ∀ a, a₀ ≤ a → Stacks.Ample.IsAmple X₀ (A a))
    (_ : ∀ a, Nonempty (A (a + 1) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X₀.toRingedSpace.sheaf).obj (A a)).obj Hb))
    (_ : Nonempty ((Scheme.Modules.pullback j).obj (A 0) ≅
      (Scheme.Modules.pullback W.ι).obj (Stacks.Ample.tensorPowModule X L (N : ℤ)))), C

/-- The data of a projective closure of an open `W ⊆ Y` over a projective variety `T₀`, adapted
to a `ℚ`-divisor `B` on `Y`, in continuation-passing style: a projective variety `Y₀ ⊇ W` with a
projective morphism `q : Y₀ ⟶ T₀` which is an open immersion on a nonempty open of `W`, an
invertible sheaf `H` on `T₀` with a section `t` whose nonvanishing locus pulls back to `W`, and a
sequence `A_a ≅ A_0 ⊗ H^{⊗ a}` of invertible sheaves on `T₀`, ample for large `a`, with
`A_0|_W ≅ 𝒪_Y(cB)|_W` for some `c > 0`. -/
private abbrev ProjectiveClosureData {k : Type} [Field k] {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    [IsLocallyNoetherian Y] [IsNormal Y] (W : Y.Opens) (B : QDivisor Y) (C : Prop) : Prop :=
  ∀ (c : ℕ) (_ : 0 < c) (Lc : Divisor Y) (_ : Divisor.toQDivisor Lc = (c : ℚ) • B)
    (T₀ : Scheme.{0}) (sT : T₀ ⟶ Spec (.of k)) (_ : MMP.Mori.IsProjectiveVariety k sT)
    (Y₀ : Scheme.{0}) (q : Y₀ ⟶ T₀) (_ : IsProjectiveMorphism q)
    (_ : MMP.Mori.IsProjectiveVariety k (q ≫ sT))
    (j : W.toScheme ⟶ Y₀) (_ : IsOpenImmersion j) (_ : j ≫ q ≫ sT = W.ι ≫ sY)
    (U : W.toScheme.Opens) (_ : (U : Set W.toScheme).Nonempty) (_ : IsOpenImmersion (U.ι ≫ j ≫ q))
    (Hb : T₀.Modules) (_ : Stacks.Ample.IsInvertibleModule T₀ Hb) (t : Γ(Hb, ⊤))
    (_ : Set.range j = q.base ⁻¹' Stacks.Ample.nonvanishingLocus Hb t)
    (A : ℕ → T₀.Modules) (_ : ∀ a, Stacks.Ample.IsInvertibleModule T₀ (A a)) (a₀ : ℕ)
    (_ : ∀ a, a₀ ≤ a → Stacks.Ample.IsAmple T₀ (A a))
    (_ : ∀ a, Nonempty (A (a + 1) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor T₀.toRingedSpace.sheaf).obj (A a)).obj Hb))
    (_ : Nonempty ((Scheme.Modules.pullback (j ≫ q)).obj (A 0) ≅
      Lc.divisorialSheaf.restrict W.ι)), C

/-- The conclusion of the compactification step, in continuation-passing style: a smooth
projective variety `X ⊇ W` whose boundary is the support of an effective divisor `E`, and a
decomposition `L + Δ` with `Δ` snc extending `B`, such that `L + mE + Δ` is nef and big for all
large `m`. -/
private abbrev CompactificationData {k : Type} [Field k] {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    [IsLocallyNoetherian Y] [IsNormal Y] (W : Y.Opens) (B : QDivisor Y) (C : Prop) : Prop :=
  ∀ (X : Scheme.{0}) (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX] [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (_ : IsSmoothScheme sX)
    (ι : W.toScheme ⟶ X) [IsOpenImmersion ι] (_ : ι ≫ sX = W.ι ≫ sY)
    (E L : Divisor X) (Δ : QDivisor X) (n₀ : ℕ) (_ : 0 ≤ E)
    (_ : Set.range ι = (E.supp : Set X)ᶜ) (_ : Δ.IsSNC sX)
    (_ : ∀ m : ℕ, n₀ ≤ m → (Divisor.toQDivisor (L + m • E) + Δ).IsNef k sX ∧
      (Divisor.toQDivisor (L + m • E) + Δ).IsBig k sX)
    (_ : ∀ P : MMP.Mori.PrimeDivisor W, (L + Δ.roundUp).coeff (openPrimeDivisor ι P) =
      B.roundUp.coeff (openPrimeDivisor W.ι P)), C

/-- **Projective closure of the preimage of an affine open.** For `f : X ⟶ Z` projective, `L`
an `f`-ample invertible sheaf and `V ⊆ Z` affine with `W = f⁻¹(V)` nonempty, a power `L^{⊗ N}` is
very ample over `V`; the embedding `W ⟶ ℙᴹ_V ⊆ ℙᴹ × ℙʳ` by its sections, followed by the closure,
gives the data of `InvertibleClosureData`. -/
private theorem exists_invertibleClosure
    {k : Type} [Field k]
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sZ]
    (f : X ⟶ Z) (hfs : f ≫ sZ = sX) (hf : IsProjectiveMorphism f)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hrel : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (V : Z.Opens) (hV : IsAffineOpen V) (hW : Nonempty (f ⁻¹ᵁ V)) (C : Prop)
    (H : InvertibleClosureData sX (f ⁻¹ᵁ V) L C) : C := by
  classical
  haveI : IsIntegral X := ‹AlgebraicGeometry.IsVariety k sX›.toIsIntegral
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
  haveI : IsAffine V.toScheme := hV
  -- Step 1: `L` is ample on `W = f⁻¹(V)`
  set LW := (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj L with hLW
  haveI : Stacks.Ample.IsInvertibleModule (f ⁻¹ᵁ V) LW :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  have hampW : Stacks.Ample.IsAmple (f ⁻¹ᵁ V) LW := hrel.2 V hV
  -- Step 2: a power of `LW` embeds `W` into `ℙᴹ_V` over `V`
  have hT := Stacks.AmpleRelativeFiniteType.tfae_six (f ∣_ V) LW
  obtain ⟨N₀, hN₀, himm⟩ := (hT.out 1 6).mp hampW
  obtain ⟨M, i, hi, hif, ⟨eL⟩⟩ := himm N₀ le_rfl
  -- Step 3: `V` is a closed subscheme of the standard chart `𝔸ʳ ⊆ ℙʳ_k`
  obtain ⟨r, c₀, hc₀, hc₀s⟩ := exists_isClosedImmersion_affineSpace (V.ι ≫ sZ)
  set Pr := projectiveSpaceOver r (Spec (.of k)) with hPr
  set ach : 𝔸(ULift.{0} (Fin r); Spec (.of k)) ⟶ Pr := projectiveSpaceOver.affineChart r 0
    (Equiv.ulift.{0}.trans (finSuccAboveEquiv (0 : Fin (r + 1)))) (Spec (.of k)) with hach
  set φ : V.toScheme ⟶ Pr := c₀ ≫ ach with hφ
  -- Step 4: `W ⟶ ℙᴹ_V ⟶ ℙᴹ_{ℙʳ}` and its scheme-theoretic image `Y₀`
  set P := projectiveSpaceOver M Pr with hP
  set πP : P ⟶ Pr := pullback.fst (terminal.from Pr) (terminal.from (projectiveSpaceAtUniverse M))
    with hπP
  set πPr : Pr ⟶ Spec (.of k) := pullback.fst (terminal.from (Spec (.of k)))
    (terminal.from (projectiveSpaceAtUniverse r)) with hπPr
  set b : projectiveSpaceOver M V.toScheme ⟶ P := projectiveSpaceOverMap M φ with hb
  set e : (f ⁻¹ᵁ V).toScheme ⟶ P := i ≫ b with he
  haveI := hi
  haveI := hc₀
  haveI : IsOpenImmersion ach := by rw [hach]; infer_instance
  haveI : IsImmersion φ := by rw [hφ]; infer_instance
  haveI : IsImmersion b :=
    MorphismProperty.of_isPullback (P := @IsImmersion) (isPullback_projectiveSpaceOverMap M φ).flip
      ‹IsImmersion φ›
  haveI : IsImmersion e := inferInstance
  haveI := compactSpace_preimage f hV.isCompact
  haveI : IsProper πPr := isProper_projectiveSpaceOver r (Spec (.of k))
  haveI : IsProper πP := isProper_projectiveSpaceOver M Pr
  haveI : QuasiCompact e := quasiCompact_of_compactSpace e
  set Y₀ := e.image with hY₀
  set j : (f ⁻¹ᵁ V).toScheme ⟶ Y₀ := e.toImage with hj
  set ι' : Y₀ ⟶ P := e.imageι with hι'
  set q : Y₀ ⟶ Pr := ι' ≫ πP with hq
  set s₀ : Y₀ ⟶ Spec (.of k) := q ≫ πPr with hs₀
  have hPP : IsProjectiveMorphism (πP ≫ πPr) :=
    IsProjectiveMorphism.comp ⟨M, 𝟙 _, inferInstance, Category.id_comp _⟩
      ⟨r, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hs₀' : s₀ = ι' ≫ πP ≫ πPr := by rw [hs₀, hq, Category.assoc]
  obtain ⟨hs₀p, -⟩ := isProjectiveMorphism_of_isProjective (πP ≫ πPr) hPP ι'
    (Stacks.FiniteMorphismProjective.isProjective_of_isFinite ι')
  have hY₀ : MMP.Mori.IsProjectiveVariety k s₀ := by
    rw [hs₀']
    haveI : IsProper (ι' ≫ πP ≫ πPr) := isProper_of_isProjectiveMorphism _ hs₀p
    haveI : IsIntegral (f ⁻¹ᵁ V).toScheme := inferInstance
    exact (MMP.Mori.isProjectiveVariety_iff k _).2
      ⟨@AlgebraicGeometry.IsVariety.mk k _ _ _ inferInstance inferInstance inferInstance
        inferInstance, hs₀p⟩
  have heπ : e ≫ πP = (f ∣_ V) ≫ φ := by
    rw [he, Category.assoc, hb, hπP, projectiveSpaceOverMap_fst, ← Category.assoc, hif]
  have hφπ : φ ≫ πPr = V.ι ≫ sZ := by
    rw [hφ, Category.assoc, hπPr]
    erw [projectiveSpaceOver.affineChart_over]
    exact hc₀s
  have hjs : j ≫ s₀ = (f ⁻¹ᵁ V).ι ≫ sX := by
    rw [hs₀, hq, ← Category.assoc, ← Category.assoc, hj, hι', Scheme.Hom.toImage_imageι,
      heπ, Category.assoc, hφπ, ← Category.assoc, morphismRestrict_ι, Category.assoc, hfs]
  -- the boundary section `t = q^* x₀`
  set Hb : Y₀.Modules := (Scheme.Modules.pullback q).obj
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf r (Spec (.of k))) with hHb
  haveI hHbi : Stacks.Ample.IsInvertibleModule Y₀ Hb :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  set t : Γ(Hb, ⊤) := pullbackGlobalSections q _ (MMP.Fourfold.coordSectionTop (A := k) r 0)
    with ht
  have hrange : Set.range j = Stacks.Ample.nonvanishingLocus Hb t := by
    have hNV : Stacks.Ample.nonvanishingLocus Hb t = q.base ⁻¹' Set.range ach.base := by
      ext y
      rw [Set.mem_preimage, ht, MMP.Fourfold.mem_nonvanishingLocus_pullbackGlobalSections_iff,
        mem_nonvanishingLocus_coordSectionTop_iff, hach, projectiveSpaceOver.range_affineChart]
      rfl
    rw [hNV]
    have hje : j ≫ ι' = e := by rw [hj, hι']; exact Scheme.Hom.toImage_imageι e
    haveI : IsSeparated q := by rw [hq]; infer_instance
    haveI : IsIntegral Y₀ := hY₀.toIsVariety.toIsIntegral
    haveI : Nonempty (f ⁻¹ᵁ V) := hW
    exact range_eq_preimage_range_of_isProper j q ach ((f ∣_ V) ≫ c₀)
      (by rw [hq, ← Category.assoc, hje, heπ, hφ, Category.assoc])
  -- the ample family `A_a = 𝒪(1) ⊗ q^* 𝒪(a)` restricted to `Y₀`
  set A : ℕ → Y₀.Modules := fun a => (Scheme.Modules.pullback ι').obj
    (Stacks.AmplePullbackPart1.tensorPullbackPowModule πP
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf M Pr)
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf r (Spec (.of k))) a) with hA
  have hAi : ∀ a, Stacks.Ample.IsInvertibleModule Y₀ (A a) := fun a =>
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  obtain ⟨a₀, hamp⟩ : ∃ a₀ : ℕ, ∀ a, a₀ ≤ a → Stacks.Ample.IsAmple Y₀ (A a) := by
    obtain ⟨a₀, ha₀⟩ := Stacks.AmplePullbackDatum.exists_threshold_isAmple πP _ _
      (Stacks.HProjective.isRelativelyAmple_projectiveSpaceTwistingSheaf M Pr)
      (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf (n := r) (S := Spec (.of k)))
    refine ⟨a₀, fun a ha => ?_⟩
    exact Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding ι' _
      (ha₀ a ha) (Or.inl ⟨inferInstance, inferInstance⟩)
  have eA : ∀ a, Nonempty (A (a + 1) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y₀.toRingedSpace.sheaf).obj (A a)).obj Hb) := by
    intro a
    set O1M := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf M Pr
    set O1r := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf r (Spec (.of k))
    have e1 : Stacks.Ample.tensorPowModule Pr O1r ((a + 1 : ℕ) : ℤ) ≅
        Stacks.RelativeVeryAmple.tensorModules Pr (Stacks.Ample.tensorPowModule Pr O1r (a : ℤ))
          O1r :=
      eqToIso (by push_cast; rfl) ≪≫ (Stacks.Ample.tensorPowModuleAddIso Pr O1r a 1).symm ≪≫
        Stacks.RelativeVeryAmple.tensorModulesMapIso Pr (Iso.refl _)
          (Stacks.Ample.tensorPowModuleOneIso Pr O1r)
    have e2 := (Scheme.Modules.pullback πP).mapIso e1 ≪≫
      Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso πP _ _
    have e3 := Stacks.RelativeVeryAmple.tensorModulesMapIso P (Iso.refl O1M) e2 ≪≫
      (Stacks.TensorSheafSpellingIso.tensorModulesAssociator P _ _ _).symm
    have e4 := (Scheme.Modules.pullback ι').mapIso e3 ≪≫
      Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso ι' _ _
    exact ⟨e4 ≪≫ Stacks.RelativeVeryAmple.tensorModulesMapIso Y₀ (Iso.refl _)
      ((Scheme.Modules.pullbackComp ι' πP).app O1r)⟩
  have eA0 : Nonempty ((Scheme.Modules.pullback j).obj (A 0) ≅
      (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj (Stacks.Ample.tensorPowModule X L (N₀ : ℤ))) := by
    set O1M := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf M Pr
    set O1r := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf r (Spec (.of k))
    have hje : j ≫ ι' = e := by rw [hj, hι']; exact Scheme.Hom.toImage_imageι e
    have hbs : b ≫ projectiveSpaceOver.toIntegralAtUniverse M Pr =
        projectiveSpaceOver.toIntegralAtUniverse M V.toScheme := projectiveSpaceOverMap_snd M φ
    have eT : Stacks.RelativeVeryAmple.tensorModules P O1M ((Scheme.Modules.pullback πP).obj
        (Stacks.Ample.tensorPowModule Pr O1r ((0 : ℕ) : ℤ))) ≅ O1M :=
      Stacks.RelativeVeryAmple.tensorModulesMapIso P (Iso.refl _)
        ((Scheme.Modules.pullback πP).mapIso (Stacks.Ample.tensorPowModuleZeroIso Pr O1r) ≪≫
          Stacks.PullbackAlgebra.pullbackUnitIso πP.toLRSHom.toShHom) ≪≫
        Stacks.TensorSheafSpellingIso.tensorModulesRightUnitor P O1M
    have eb : (Scheme.Modules.pullback b).obj O1M ≅
        Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf M V.toScheme :=
      (Scheme.Modules.pullbackComp b (projectiveSpaceOver.toIntegralAtUniverse M Pr)).app _ ≪≫
        eqToIso (by rw [hbs])
    exact ⟨(Scheme.Modules.pullbackComp j ι').app _ ≪≫ eqToIso (by rw [hje]; rfl) ≪≫
      (Scheme.Modules.pullback e).mapIso eT ≪≫ eqToIso (by rw [he]) ≪≫
      ((Scheme.Modules.pullbackComp i b).app O1M).symm ≪≫
      (Scheme.Modules.pullback i).mapIso eb ≪≫ eL.symm ≪≫
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (f ⁻¹ᵁ V).ι L N₀).symm⟩
  exact H N₀ (by omega) Y₀ s₀ hY₀ j inferInstance hjs Hb hHbi t hrange A hAi a₀ hamp eA eA0

/-- **Closing the graph of a projective morphism over a projective closure.** Let `p : Y ⟶ X` be
projective with `Y` integral, `W ⊆ X` open with `p⁻¹(W)` nonempty and quasi-compact, and
`j : W ⟶ X₀` an open immersion into a projective variety. The closure of the image of
`p⁻¹(W) ⟶ ℙᴹ_W ⊆ ℙᴹ_{X₀}` is a projective variety `Y₀ ⊇ p⁻¹(W)`, with a projective morphism
`q : Y₀ ⟶ X₀` extending `p` and satisfying `q⁻¹(j(W)) = p⁻¹(W)`. -/
private theorem exists_graphClosure {k : Type} [Field k] {X Y X₀ : Scheme.{0}}
    (p : Y ⟶ X) [IsIntegral Y] (hp : IsProjectiveMorphism p)
    (W : X.Opens) [Nonempty (p ⁻¹ᵁ W)] [CompactSpace (p ⁻¹ᵁ W)] (s₀ : X₀ ⟶ Spec (.of k))
    (hX₀ : MMP.Mori.IsProjectiveVariety k s₀) (j : W.toScheme ⟶ X₀) [IsOpenImmersion j] :
    ∃ (Y₀ : Scheme.{0}) (jY : (p ⁻¹ᵁ W).toScheme ⟶ Y₀) (q : Y₀ ⟶ X₀),
      IsOpenImmersion jY ∧ IsProjectiveMorphism q ∧ MMP.Mori.IsProjectiveVariety k (q ≫ s₀) ∧
        jY ≫ q = (p ∣_ W) ≫ j ∧ Set.range jY = q.base ⁻¹' Set.range j := by
  classical
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hp
  obtain ⟨M, i, hi, hip⟩ := hp
  haveI := hi
  set pW := p ∣_ W with hpW
  set πP : projectiveSpaceOver M X₀ ⟶ X₀ :=
    pullback.fst (terminal.from X₀) (terminal.from (projectiveSpaceAtUniverse M)) with hπP
  -- the embedding `p⁻¹(W) ⟶ ℙᴹ_W`
  set e₁ : (p ⁻¹ᵁ W).toScheme ⟶ projectiveSpaceOver M W.toScheme :=
    pullback.lift pW ((p ⁻¹ᵁ W).ι ≫ i ≫ projectiveSpaceOver.toIntegralAtUniverse M X)
      (terminal.hom_ext _ _) with he₁
  have he₁W : e₁ ≫ projectiveSpaceOverMap M W.ι = (p ⁻¹ᵁ W).ι ≫ i := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, projectiveSpaceOverMap_fst, ← Category.assoc, he₁, pullback.lift_fst,
        hpW, morphismRestrict_ι, Category.assoc, ← hip]
      rfl
    · rw [Category.assoc, projectiveSpaceOverMap_snd, he₁, pullback.lift_snd, Category.assoc]
  haveI : IsImmersion e₁ := by
    haveI : IsImmersion (e₁ ≫ projectiveSpaceOverMap M W.ι) := by
      rw [he₁W]; infer_instance
    exact IsImmersion.of_comp e₁ (projectiveSpaceOverMap M W.ι)
  haveI : IsOpenImmersion (projectiveSpaceOverMap M j) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_projectiveSpaceOverMap M j).flip inferInstance
  set e := e₁ ≫ projectiveSpaceOverMap M j with he
  haveI : IsImmersion e := inferInstance
  haveI : IsProper πP := isProper_projectiveSpaceOver M X₀
  haveI := hX₀.toIsVariety
  haveI : QuasiSeparatedSpace X₀ := quasiSeparatedSpace_of_quasiSeparated s₀
  haveI : QuasiSeparatedSpace (projectiveSpaceOver M X₀) := quasiSeparatedSpace_of_quasiSeparated πP
  haveI : QuasiCompact e := quasiCompact_of_compactSpace e
  set Y₀ := e.image with hY₀
  set jY : (p ⁻¹ᵁ W).toScheme ⟶ Y₀ := e.toImage with hjY
  set ι' : Y₀ ⟶ projectiveSpaceOver M X₀ := e.imageι with hι'
  set q : Y₀ ⟶ X₀ := ι' ≫ πP with hq
  have hqp : IsProjectiveMorphism q := ⟨M, ι', inferInstance, rfl⟩
  have hX₀p := ((MMP.Mori.isProjectiveVariety_iff k s₀).1 hX₀).2
  have hqs : IsProjectiveMorphism (q ≫ s₀) := IsProjectiveMorphism.comp hqp hX₀p
  have hje : jY ≫ ι' = e := by rw [hjY, hι']; exact Scheme.Hom.toImage_imageι e
  have heπ : e ≫ πP = pW ≫ j := by
    rw [he, Category.assoc, hπP, projectiveSpaceOverMap_fst, ← Category.assoc, he₁,
      pullback.lift_fst]
  have hjq : jY ≫ q = pW ≫ j := by rw [hq, ← Category.assoc, hje, heπ]
  have hY₀v : MMP.Mori.IsProjectiveVariety k (q ≫ s₀) := by
    haveI : IsProper (q ≫ s₀) := isProper_of_isProjectiveMorphism _ hqs
    haveI : IsIntegral (p ⁻¹ᵁ W).toScheme := inferInstance
    exact (MMP.Mori.isProjectiveVariety_iff k _).2
      ⟨@AlgebraicGeometry.IsVariety.mk k _ _ _ inferInstance inferInstance inferInstance
        inferInstance, hqs⟩
  haveI : IsIntegral Y₀ := hY₀v.toIsVariety.toIsIntegral
  refine ⟨Y₀, jY, q, inferInstance, hqp, hY₀v, hjq, ?_⟩
  haveI : IsSeparated q := by rw [hq]; infer_instance
  haveI : IsProper pW := by rw [hpW]; infer_instance
  exact range_eq_preimage_range_of_isProper jY q j pW hjq

/-- **Lifting an open immersion along a morphism that is an isomorphism over an open.** If
`g : X' ⟶ X` restricts to an isomorphism over `U` and `j : W ⟶ X` is an open immersion with image
in `U`, then `j` lifts to an open immersion `ι : W ⟶ X'` with image `g⁻¹(j(W))`. -/
private theorem exists_isOpenImmersion_lift {W X X' : Scheme.{0}} (g : X' ⟶ X) (U : X.Opens)
    [IsIso (g ∣_ U)] (j : W ⟶ X) [IsOpenImmersion j] (hj : Set.range j ⊆ U) :
    ∃ ι : W ⟶ X', IsOpenImmersion ι ∧ ι ≫ g = j ∧ Set.range ι = g ⁻¹' Set.range j := by
  have hjU : Set.range j ⊆ Set.range U.ι := by simpa using hj
  set j' : W ⟶ U.toScheme := IsOpenImmersion.lift U.ι j hjU with hj'def
  have hj' : j' ≫ U.ι = j := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion j' := by
    have : IsOpenImmersion (j' ≫ U.ι) := by rw [hj']; infer_instance
    exact IsOpenImmersion.of_comp j' U.ι
  have hfac : inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι ≫ g = U.ι := by
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  refine ⟨j' ≫ inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, hfac, hj']
  · ext x
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, hfac, hj']
    · rintro ⟨w, hw⟩
      have hxU : x ∈ g ⁻¹ᵁ U := by
        change g x ∈ U
        rw [← hw]
        exact hj ⟨w, rfl⟩
      let y : (g ⁻¹ᵁ U).toScheme := ⟨x, hxU⟩
      have hy : (g ⁻¹ᵁ U).ι y = x := rfl
      have h1 : (g ∣_ U) y = j' w := by
        apply U.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hy,
          ← Scheme.Hom.comp_apply, hj']
        exact hw.symm
      have h2 : inv (g ∣_ U) (j' w) = y := by
        rw [← h1, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
        rfl
      refine ⟨w, ?_⟩
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h2, hy]

/-- **The effective divisor of a section.** On an integral Noetherian normal scheme on which every
divisor is Cartier, a section `t` of an invertible sheaf `L` that does not vanish identically is
the canonical section `1` of `𝒪_X(E)` for an effective divisor `E` with `𝒪_X(E) ≅ L`; the
complement of `Supp E` is the nonvanishing locus of `t`. -/
private theorem exists_divisor_of_section {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (hcart : ∀ D : Divisor X, D.IsCartier)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (t : Γ(L, ⊤))
    (ht : (Stacks.Ample.nonvanishingLocus L t).Nonempty) :
    ∃ E : Divisor X, 0 ≤ E ∧ Nonempty (E.divisorialSheaf ≅ L) ∧
      (E.supp : Set X)ᶜ = Stacks.Ample.nonvanishingLocus L t := by
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    ‹Stacks.Ample.IsInvertibleModule X L›
  obtain ⟨D, ⟨e⟩⟩ := MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible L
  set sΓ : Γ(D.divisorialSheaf, ⊤) := e.inv.app ⊤ t with hsΓ
  have hts : e.hom.app ⊤ sΓ = t := by
    rw [hsΓ, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  have hsne : sΓ ≠ 0 := fun h => by
    obtain ⟨x, hx⟩ := ht
    rwa [← hts, h, map_zero, Stacks.Ample.nonvanishingLocus_zero] at hx
  set σ : D.divisorialSubmodule ⊤ := sΓ with hσ
  let ψ₀ : RationalFunctions X := fun Z => σ.1 ⟨Z, trivial⟩
  have hsub : Subsingleton (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  have hψ₀ : ∀ Z, ψ₀ Z ≠ 0 := by
    intro Z hZ
    apply hsne
    change σ = 0
    apply Subtype.ext
    funext Z'
    change σ.1 Z' = 0
    rwa [show Z' = ⟨Z, trivial⟩ from Subtype.ext (Subsingleton.elim _ _)]
  have hunit : IsUnit ψ₀ := by
    rw [Pi.isUnit_iff]
    intro Z
    obtain ⟨b, hb⟩ := (RationalFunctions.isField_stalk X Z).mul_inv_cancel (hψ₀ Z)
    exact IsUnit.of_mul_eq_one _ hb
  set ψ := hunit.unit with hψ
  set E : Divisor X := D + principalDivisor ψ with hE
  have hEc : ∀ P : MMP.Mori.PrimeDivisor X, E.coeff P = D.coeff P + P.ord ψ := fun P => by
    rw [hE, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  have hE0 : 0 ≤ E := by
    intro P
    change 0 ≤ E.coeff P
    rw [hEc]
    have h := σ.2 P ⟨P.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, trivial⟩
    rcases h with h | h
    · exact absurd h (hψ₀ _)
    · have h' : WithZero.exp (-D.coeff P) ≤ WithZero.exp (P.ord ψ) := by
        rwa [← P.valuation_component ψ]
      rw [WithZero.exp_le_exp] at h'
      linarith
  let eM : E.divisorialSheaf ≅ D.divisorialSheaf := Divisor.divisorialSheafMulIso ψ hEc
  have h1 : eM.hom.app ⊤ (MMP.Threefold.Mori.oneSection hE0) = sΓ := by
    change (⟨_, _⟩ : D.divisorialSubmodule ⊤) = σ
    apply Subtype.ext
    funext Z
    change (ψ : RationalFunctions X) Z.1 *
      ((Divisor.structureSheafToDivisorialSheaf hE0).app ⊤ (1 : Γ(X, ⊤))).1 Z = σ.1 Z
    rw [Divisor.coe_structureSheafToDivisorialSheaf_app, map_one]
    change (ψ : RationalFunctions X) Z.1 * 1 = σ.1 Z
    rw [mul_one]
    rfl
  refine ⟨E, hE0, ⟨eM ≪≫ e⟩, ?_⟩
  rw [← MMP.Threefold.Mori.nonvanishingLocus_oneSection hE0 (hcart E),
    ← Stacks.Ample.nonvanishingLocus_congr (eM ≪≫ e) (MMP.Threefold.Mori.oneSection hE0)]
  congr 1
  rw [Iso.trans_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, h1, hts]

/-- **Rational functions lift along an open immersion.** For an open immersion `ι : W ⟶ X` of
integral schemes, every unit of `K(W)` is the pull-back of a unit of `K(X)`: the stalk map of `ι`
at the generic point of `W` is an isomorphism. -/
private theorem exists_pullbackRationalFunction_eq {W X : Scheme.{0}} [IsIntegral W] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (ι : W ⟶ X) [IsOpenImmersion ι]
    (hφ' : ∀ (φ : (RationalFunctions X)ˣ) (Z : irreducibleComponents W),
      ι (componentGenericPoint W Z) ∉ (principalDivisor φ).supp)
    (ψ : (RationalFunctions W)ˣ) :
    ∃ φ : (RationalFunctions X)ˣ, pullbackRationalFunction ι φ (hφ' φ) = ψ := by
  have hsubW : Subsingleton (irreducibleComponents W) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents W) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  set η := componentGenericPoint W Z₀ with hη
  have hmem : ∀ W' : irreducibleComponents X, ι η ∈ W'.1 := fun W' => by
    have h : W'.1 ∈ ({Set.univ} : Set (Set X)) := by
      rw [← irreducibleComponents_eq_singleton]; exact W'.2
    rw [Set.mem_singleton_iff] at h
    rw [h]; trivial
  set a : (X.presheaf.stalk (ι η))ˣ :=
    Units.map (inv (ι.stalkMap η)).hom.toMonoidHom ((RationalFunctions.unitsEquiv W ψ) Z₀)
  refine ⟨(RationalFunctions.unitsEquiv X).symm
    (fun W' => Units.map (stalkToRationalFunctions X (hmem W')).hom.toMonoidHom a), ?_⟩
  apply (RationalFunctions.unitsEquiv W).injective
  funext Z
  obtain rfl : Z = Z₀ := Subsingleton.elim _ _
  obtain ⟨W₀⟩ : Nonempty (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  simp only [pullbackRationalFunction, MulEquiv.apply_symm_apply]
  rw [pullbackComponent_eq (hφ' _) (Divisor.isLocalEquation_principalDivisor _ ⊤) trivial
    (hmem W₀) a rfl]
  apply Units.ext
  change (ι.stalkMap η).hom ((inv (ι.stalkMap η)).hom _) = _
  rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]
  rfl

/-- **Extending a divisor from an open subscheme up to linear equivalence.** Let `ι : W ⟶ X` be
an open immersion of integral Noetherian normal schemes and `G` a Cartier divisor on `X` whose
pull-back to `W` has divisorial sheaf isomorphic to `𝒪_W(T)`. Then some `G' ∼ G` has coefficient
`T(P)` along the prime divisor of `X` through every prime divisor `P` of `W`. -/
private theorem exists_linearlyEquivalent_coeff_eq {W X : Scheme.{0}} [IsIntegral W] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] (ι : W ⟶ X) [IsOpenImmersion ι] {G : Divisor X} (hG : G.IsCartier)
    (T : Divisor W) (e : Nonempty ((Scheme.Modules.pullback ι).obj G.divisorialSheaf ≅
      T.divisorialSheaf)) :
    ∃ G' : Divisor X, Nonempty (G'.divisorialSheaf ≅ G.divisorialSheaf) ∧
      ∀ P : MMP.Mori.PrimeDivisor W, G'.coeff (openPrimeDivisor ι P) = T.coeff P := by
  haveI : IsDominant ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion ι
  have hB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant ι
  obtain ⟨Gι, hGι⟩ := hG.exists_isPullback (hB G)
  obtain ⟨e⟩ := e
  obtain ⟨ψ, hψ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    ((Divisor.IsPullback.divisorialSheafIso (hBc := hG) hGι) ≪≫ e)
  obtain ⟨φ, hφ⟩ := exists_pullbackRationalFunction_eq ι (fun φ => hB _) ψ
  refine ⟨G - principalDivisor φ, ⟨Divisor.LinearlyEquivalent.divisorialSheafIso
    ⟨φ⁻¹, by rw [MMP.Mori.principalDivisor_inv]; abel⟩⟩, fun P => ?_⟩
  have hpr := Divisor.isPullback_principalDivisor (f := ι) φ (hB _)
  rw [hφ] at hpr
  rw [DivisorWithCoeffs.coeff_sub, ← coeff_of_isPullback_of_isOpenImmersion ι hG hGι,
    ← coeff_of_isPullback_of_isOpenImmersion ι (Divisor.isCartier_principalDivisor φ) hpr]
  have := congrArg (DivisorWithCoeffs.coeff · P) hψ
  simp only [DivisorWithCoeffs.coeff_sub] at this
  rw [← this]
  ring

/-- A divisor whose components are members of an snc family is snc. -/
private theorem isSNC_of_isSNCFamily {k : Type} [Field k] {X : Scheme.{0}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData}
    (hF : MMP.Resolution.IsSNCFamily s F)
    {R : Type*} [Zero R] (D : MMP.Mori.DivisorWithCoeffs R X)
    (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
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

/-- A prime divisor contained in a closed set of pure codimension one is one of its irreducible
components. -/
private theorem mem_componentsOf_of_support_subset {X : Scheme.{0}} {S : Set X} (hS : IsClosed S)
    (hpure : MMP.Mori.IsPureCodimOne (⟨S, hS⟩ : TopologicalSpace.Closeds X))
    (P : MMP.Mori.PrimeDivisor X) (hP : (P.support : Set X) ⊆ S) :
    (P.support : Set X) ∈ MMP.Resolution.componentsOf S := by
  have hηS : P.genericPoint ∈ S :=
    hP (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  obtain ⟨W, hW, hηW⟩ := MMP.Resolution.exists_mem_componentsOf hηS
  have hWcl : IsClosed W := MMP.Resolution.isClosed_of_mem_componentsOf hS hW
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hW.1.1 hWcl
  have hmax : Maximal (fun W' : TopologicalSpace.IrreducibleCloseds X => (W' : Set X) ⊆ S)
      ⟨W, hW.1.1, hWcl⟩ :=
    ⟨hW.1.2, fun W' hW' hle => hW.2 ⟨W'.isIrreducible, hW'⟩ hle⟩
  have hcod := hpure _ hmax
  have hξc : Order.coheight ξ = 1 := by
    rw [← Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
    convert hcod using 2
    ext1
    exact hξ.def
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hξc with hQ
  have hQs : (Q.support : Set X) = W := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hξ.def
  have hPQ : (P.support : Set X) ⊆ Q.support := by
    rw [hQs, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηW) hWcl
  have hPQe := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset hPQ
  rw [hPQe, hQs]
  exact hW

/-- A divisor all of whose components lie in an snc closed subset is snc. -/
private theorem isSNC_of_isSNCClosedSubset {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] {S : Set X} (hS : MMP.Resolution.IsSNCClosedSubset sX S)
    {R : Type*} [Zero R] (Δ : MMP.Mori.DivisorWithCoeffs R X)
    (hΔ : ∀ P ∈ Δ.support, (P.support : Set X) ⊆ S) : Δ.IsSNC sX := by
  obtain ⟨hScl, hS0 | ⟨hpure, -, hfam⟩⟩ := hS
  · have hempty : ∀ P ∈ Δ.support, False := fun P hP => by
      have := hΔ P hP (show P.genericPoint ∈ P.support by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
      rw [hS0] at this
      exact this
    refine ⟨fun P hP => (hempty P hP).elim, fun x => ?_⟩
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sX x
    obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk x)
    exact ⟨n, z, fun P => (hempty P.1 P.2.1).elim, hz, fun P => (hempty P.1 P.2.1).elim,
      fun P => (hempty P.1 P.2.1).elim⟩
  · exact isSNC_of_isSNCFamily hfam Δ fun P hP =>
      ⟨⟨_, mem_componentsOf_of_support_subset hScl hpure P (hΔ P hP)⟩,
        MMP.Fourfold.SNCWeight.PrimeDivisorUnion.componentsFamily_eq_idealSheaf _ P rfl⟩

/-- The local snc condition at a point only depends on the support of the divisor. -/
private theorem sncStalk_of_support_iff {R R' : Type*} [Zero R] [Zero R'] {W : Scheme.{0}}
    (D : MMP.Mori.DivisorWithCoeffs R W) (D' : MMP.Mori.DivisorWithCoeffs R' W)
    (h : ∀ P, D P ≠ 0 ↔ D' P ≠ 0) (w : W)
    (hD : ∃ (n : ℕ) (z : Fin n → W.presheaf.stalk w)
      (jj : {E : MMP.Mori.PrimeDivisor W // E ∈ D.support ∧ w ∈ E.support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧ Function.Injective jj ∧
        ∀ E, AlgebraicGeometry.IdealSheafData.stalk E.1.idealSheaf w = Ideal.span {z (jj E)}) :
    ∃ (n : ℕ) (z : Fin n → W.presheaf.stalk w)
      (jj : {E : MMP.Mori.PrimeDivisor W // E ∈ D'.support ∧ w ∈ E.support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧ Function.Injective jj ∧
        ∀ E, AlgebraicGeometry.IdealSheafData.stalk E.1.idealSheaf w = Ideal.span {z (jj E)} := by
  have hs : D.support = D'.support := Finset.ext fun P => by
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]; exact h P
  rw [← hs]
  exact hD

/-- **Transport of the snc condition to the image of an open immersion.** Let `ι : W ⟶ X` and
`j : W ⟶ Y` be open immersions over `k`, `F` an snc divisor on `Y` and `D` a finite set of prime
divisors of `X` whose members through `ι(W)` are exactly the closures of the components of
`F|_W`. Then `D` restricted to `ι(W)` is an snc closed subset. -/
private theorem isSNCClosedSubset_opensRange {k : Type} [Field k] {W X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sY] (ι : W ⟶ X) [IsOpenImmersion ι] (jY : W ⟶ Y) [IsOpenImmersion jY]
    (h : ι ≫ sX = jY ≫ sY) {R : Type*} [Zero R] (F : MMP.Mori.DivisorWithCoeffs R Y)
    (hF : F.IsSNC sY) (D : Finset (MMP.Mori.PrimeDivisor X))
    (hD : ∀ Q : MMP.Mori.PrimeDivisor W,
      openPrimeDivisor ι Q ∈ D ↔ F.coeff (openPrimeDivisor jY Q) ≠ 0) :
    MMP.Resolution.IsSNCClosedSubset (ι.opensRange.ι ≫ sX)
      (ι.opensRange.ι ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X))) := by
  classical
  set U := ι.opensRange with hU
  set Rd : Divisor X := ∑ E ∈ D, Finsupp.single E (1 : ℤ) with hRd
  have hRd' : ∀ P, Rd P ≠ 0 ↔ P ∈ D := fun P => by
    rw [hRd, Finset.sum_apply']; simp [Finsupp.single_apply]
  set T : Divisor U := Rd.restrictOpen U with hT
  have hTc : ∀ Fc, T Fc = Rd (OpenWeilRestriction.primeDivisorMap U.ι Fc) := fun _ => rfl
  have hrangeU : Set.range U.ι = Set.range ι := by rw [Scheme.Opens.range_ι]; rfl
  have hlofp : ∀ {Z : Scheme.{0}} (I : Z.IdealSheafData) (s : Z ⟶ Spec (.of k))
      [LocallyOfFiniteType s], LocallyOfFinitePresentation (I.subschemeι ≫ s) := fun I s _ =>
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := I.subschemeι ≫ s)).mpr
      inferInstance
  have hTQ : ∀ Fc : MMP.Mori.PrimeDivisor U, Fc ∈ T.support →
      ∃ Q : MMP.Mori.PrimeDivisor W,
        OpenWeilRestriction.primeDivisorMap U.ι Fc = openPrimeDivisor ι Q ∧
          openPrimeDivisor ι Q ∈ D := by
    intro Fc hFc
    have hPD : OpenWeilRestriction.primeDivisorMap U.ι Fc ∈ D :=
      (hRd' _).1 (by rw [← hTc]; exact Finsupp.mem_support_iff.mp hFc)
    obtain ⟨w, hw⟩ : U.ι Fc.genericPoint ∈ Set.range ι := by
      rw [← hrangeU]; exact ⟨_, rfl⟩
    have hmem : ι w ∈ (OpenWeilRestriction.primeDivisorMap U.ι Fc).support := by
      rw [hw, MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    obtain ⟨Q, hQ⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
      ι _ w hmem
    refine ⟨Q, by rw [openPrimeDivisor_eq_primeDivisorMap, hQ], ?_⟩
    rw [openPrimeDivisor_eq_primeDivisorMap, hQ]
    exact hPD
  have hTsnc : T.IsSNC (U.ι ≫ sX) := by
    refine ⟨fun Fc hFc => ?_, fun x => ?_⟩
    · obtain ⟨Q, hPQ, hQD⟩ := hTQ Fc hFc
      have hFQ : F.coeff (openPrimeDivisor jY Q) ≠ 0 := (hD Q).1 hQD
      have hsmY := hF.1 (openPrimeDivisor jY Q) (Finsupp.mem_support_iff.mpr hFQ)
      haveI := hlofp (openPrimeDivisor jY Q).idealSheaf sY
      haveI := hlofp (OpenWeilRestriction.primeDivisorMap U.ι Fc).idealSheaf sX
      have h1 : MMP.Mori.IsSmoothScheme (Q.idealSheaf.subschemeι ≫ jY ≫ sY) := by
        refine (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff jY sY
          (openPrimeDivisor jY Q).idealSheaf Q.idealSheaf (by
            rw [openPrimeDivisor_eq_primeDivisorMap]
            exact MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap jY Q)).2
          fun z _ => ?_
        rw [← MMP.Mori.smoothLocus_eq_smoothLocus, hsmY]; trivial
      rw [← h] at h1
      have h2 := (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff ι sX
        (OpenWeilRestriction.primeDivisorMap U.ι Fc).idealSheaf Q.idealSheaf (by
          rw [hPQ, openPrimeDivisor_eq_primeDivisorMap]
          exact MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap ι Q)).1 h1
      exact (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff U.ι sX
        (OpenWeilRestriction.primeDivisorMap U.ι Fc).idealSheaf Fc.idealSheaf
        (MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap U.ι Fc)).2
        fun z hz => h2 z (by rw [← hrangeU]; exact hz)
    · obtain ⟨w, hw⟩ := x.2
      have hx : U.ι x = ι w := hw.symm
      refine (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι Rd x).2 ?_
      rw [hx]
      refine (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff ι Rd w).1 ?_
      have hY := (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff jY F w).2
        (hF.2 (jY w))
      refine sncStalk_of_support_iff _ _ (fun Q => ?_) w hY
      rw [Finsupp.comapDomain_apply, Finsupp.comapDomain_apply,
        ← openPrimeDivisor_eq_primeDivisorMap,
        ← openPrimeDivisor_eq_primeDivisorMap, hRd', hD Q]
      rfl
  have hset : U.ι ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X)) =
      ⋃ Fc ∈ T.support, (Fc.support : Set U) := by
    ext x
    simp only [Set.mem_preimage, Finset.sup_set_eq_biUnion, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨P, hP, hx⟩
      obtain ⟨Fc, hFc⟩ :=
        MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support U.ι P x hx
      refine ⟨Fc, ?_, ?_⟩
      · rw [Finsupp.mem_support_iff, hTc, hFc]; exact (hRd' P).2 hP
      · rw [← MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι, hFc]
        exact hx
    · rintro ⟨Fc, hFc, hx⟩
      exact ⟨_, (hRd' _).1 (by rw [← hTc]; exact Finsupp.mem_support_iff.mp hFc),
        (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι Fc x).2 hx⟩
  rw [hset]
  exact MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC _ hTsnc

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{0}} (f : X ⟶ Y)
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
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{0}} {f : X ⟶ Y}
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

/-- **Birationality from an open immersion on an open of an open subscheme.** A morphism
`h : Z ⟶ T` of irreducible schemes is birational if, for an open immersion `ι : W ⟶ Z` and a
nonempty open `U ⊆ W`, the composite `U ⟶ W ⟶ Z ⟶ T` is an open immersion. -/
private theorem isBirationalMorphism_of_isOpenImmersion_comp {W Z T : Scheme.{0}}
    [IrreducibleSpace Z] [IrreducibleSpace T] (h : Z ⟶ T) (ι : W ⟶ Z) [IsOpenImmersion ι]
    (U : W.Opens) (hU : (U : Set W).Nonempty) [IsOpenImmersion (U.ι ≫ ι ≫ h)] :
    IsBirationalMorphism h := by
  set φ : U.toScheme ⟶ Z := U.ι ≫ ι with hφ
  obtain ⟨x, hx⟩ := hU
  have hne : ((φ.opensRange : Z.Opens) : Set Z).Nonempty := ⟨φ ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩
  haveI : IsOpenImmersion (φ ≫ h) := by rw [hφ, Category.assoc]; infer_instance
  haveI : IsOpenImmersion (φ.opensRange.ι ≫ h) := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]
    infer_instance
  haveI : IsDominant h := by
    refine ⟨?_⟩
    have hd : Dense (Set.range (U.ι ≫ ι ≫ h).base) :=
      (U.ι ≫ ι ≫ h).isOpenEmbedding.isOpen_range.dense ⟨_, ⟨x, hx⟩, rfl⟩
    refine hd.mono ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨(U.ι ≫ ι).base y, by simp⟩
  exact isBirationalMorphism_of_isOpenImmersion h φ.opensRange (φ.opensRange.isOpen.dense hne)

/-- If `𝒪(G) ≅ f^*A₀`, `𝒪(E) ≅ f^*H` and `A_{a+1} ≅ A_a ⊗ H` for all `a`, then
`𝒪(G + aE) ≅ f^*A_a`. -/
private theorem nonempty_divisorialSheaf_add_nsmul_iso {X T : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (hcart : ∀ D : Divisor X, D.IsCartier) (f : X ⟶ T)
    {G E : Divisor X} {H : T.Modules} {A : ℕ → T.Modules}
    (eG : G.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj (A 0))
    (eE : E.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj H)
    (eA : ∀ a, Nonempty (A (a + 1) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor T.toRingedSpace.sheaf).obj (A a)).obj H))
    (a : ℕ) : Nonempty ((G + a • E).divisorialSheaf ≅ (Scheme.Modules.pullback f).obj (A a)) := by
  induction a with
  | zero => exact ⟨eqToIso (by rw [zero_nsmul, add_zero]) ≪≫ eG⟩
  | succ a ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨ea⟩ := eA a
    exact ⟨eqToIso (by rw [succ_nsmul, add_assoc]) ≪≫
      ((hcart _).divisorialSheafTensorIso (hcart E)).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso eE ≪≫
      (Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso f (A a) H).symm ≪≫
      (Scheme.Modules.pullback f).mapIso ea.symm⟩

/-- For `B = c⁻¹ G` with `c ≠ 0`, `G + (cm)E = c(⌊B⌋ + mE + {B})` as `ℚ`-divisors. -/
private theorem toQDivisor_add_mul_nsmul_eq {X : Scheme.{0}} (G E : Divisor X) {c : ℕ}
    (hc : (c : ℚ) ≠ 0) (m : ℕ) :
    Divisor.toQDivisor (G + (c * m) • E) =
      (c : ℚ) • (Divisor.toQDivisor (((c : ℚ)⁻¹ • Divisor.toQDivisor G).roundDown + m • E) +
        ((c : ℚ)⁻¹ • Divisor.toQDivisor G).fract) := by
  set Bb : QDivisor X := (c : ℚ)⁻¹ • Divisor.toQDivisor G
  ext P
  have h : ((Bb.roundDown P : ℤ) : ℚ) + Bb.fract P = Bb P :=
    congrArg (fun D : QDivisor X => D P) (DivisorWithCoeffs.roundDown_add_fract Bb)
  have hb : Bb P = (c : ℚ)⁻¹ * (G P : ℚ) := rfl
  change (((G + (c * m) • E) P : ℤ) : ℚ) =
    (c : ℚ) * ((((Bb.roundDown + m • E) P : ℤ) : ℚ) + Bb.fract P)
  simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul, Int.cast_add, Int.cast_mul,
    Int.cast_natCast]
  rw [add_right_comm, h, hb]
  field_simp
  push_cast
  ring

/-- **Resolution of a projective closure.** From the data of `ProjectiveClosureData`, a strong
resolution of `Y₀` followed by a log resolution of the closures of the components of `{B}` and
of the boundary, both isomorphisms over `W`, gives the data of `CompactificationData`. -/
private theorem exists_compactification_of_projectiveClosure
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    (hsm : IsSmoothScheme sY)
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (W : Y.Opens) [Nonempty W] [CompactSpace W]
    (B : QDivisor Y) (hBf : B.fract.IsSNC sY) (C : Prop)
    (H : CompactificationData sY W B C) : ProjectiveClosureData sY W B C := by
  classical
  intro c hc Lc hLc T₀ sT hT₀ Y₀ q hqp hY₀ j hjo hj U hUW hUq Hb hHb t ht A hA a₀ hamp eA eA0
  generalize hs₀ : q ≫ sT = s₀ at hY₀ hj
  haveI := hjo
  haveI := hHb
  haveI := hY₀
  have hY₀v : AlgebraicGeometry.IsVariety k s₀ := hY₀.toIsVariety
  haveI := hY₀v
  haveI : IsIntegral Y₀ := hY₀v.toIsIntegral
  haveI : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian s₀
  haveI : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace s₀
  have hsY : Smooth sY := (MMP.Mori.isSmoothScheme_iff sY).1 hsm
  have hWsm : Set.range j ⊆ (smoothLocus s₀ : Set Y₀) := by
    have hU : Smooth (j.opensRange.ι ≫ s₀) := by
      rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, hj]
      infer_instance
    have : j.opensRange ≤ smoothLocus s₀ := le_sSup hU
    exact fun _ hx => this hx
  obtain ⟨X₁, g₁, hX₁v, hg₁p, hg₁b, hX₁sm, hg₁iso, -⟩ :=
    MMP.Resolution.exists_isStrongResolution s₀ hY₀v
  haveI := hg₁iso
  obtain ⟨ι₁, hι₁o, hι₁, hι₁r⟩ := exists_isOpenImmersion_lift g₁ (smoothLocus s₀) j hWsm
  haveI := hι₁o
  haveI := hX₁v
  haveI : IsIntegral X₁ := hX₁v.toIsIntegral
  haveI : IsLocallyNoetherian X₁ := LocallyOfFiniteType.isLocallyNoetherian (g₁ ≫ s₀)
  haveI : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace (g₁ ≫ s₀)
  haveI : Smooth (g₁ ≫ s₀) := (MMP.Mori.isSmoothScheme_iff _).1 hX₁sm
  haveI : IsNormal X₁ := isNormal_of_smooth_over_field (g₁ ≫ s₀)
  have hcart₁ : ∀ D : Divisor X₁, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hX₁sm
  haveI : Stacks.Ample.IsInvertibleModule X₁ ((Scheme.Modules.pullback (g₁ ≫ q)).obj Hb) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj (g₁ ≫ q) Hb
  have hrange₁ : Set.range ι₁ = Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback (g₁ ≫ q)).obj Hb) (pullbackGlobalSections (g₁ ≫ q) Hb t) := by
    rw [hι₁r, ← Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections, ht]
    rfl
  obtain ⟨E₁, hE₁0, -, hE₁r⟩ := exists_divisor_of_section hcart₁ _
    (pullbackGlobalSections (g₁ ≫ q) Hb t) (by rw [← hrange₁]; exact Set.range_nonempty _)
  have hinjW : Function.Injective (openPrimeDivisor W.ι) := openPrimeDivisor_injective W.ι
  set S : Set (MMP.Mori.PrimeDivisor W) := {Q | B.fract.coeff (openPrimeDivisor W.ι Q) ≠ 0}
    with hSdef
  have hS : S.Finite := (B.fract.support.finite_toSet.preimage hinjW.injOn).subset
    fun Q hQ => Finsupp.mem_support_iff.mpr hQ
  set D : Finset (MMP.Mori.PrimeDivisor X₁) := hS.toFinset.image (openPrimeDivisor ι₁) ∪ E₁.support
    with hDdef
  have hX₁n : MMP.Mori.IsNormalVariety k (g₁ ≫ s₀) := ⟨hX₁v, inferInstance⟩
  obtain ⟨Yb, f₂, hres, -, hsnc, hiso⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset (g₁ ≫ s₀) hX₁n D
  have hU : IsIso (f₂ ∣_ ι₁.opensRange) := hiso _ ((MMP.Mori.isSmoothScheme_iff _).2 inferInstance)
    (isSNCClosedSubset_opensRange (g₁ ≫ s₀) sY ι₁ W.ι (by rw [← Category.assoc, hι₁, hj]) B.fract
      hBf D fun Q => by
        constructor
        · intro hQ
          rcases Finset.mem_union.mp hQ with hQ | hQ
          · obtain ⟨Q', hQ', hQQ'⟩ := Finset.mem_image.mp hQ
            rw [← openPrimeDivisor_injective ι₁ hQQ']
            exact hS.mem_toFinset.mp hQ'
          · exact absurd (coeff_openPrimeDivisor_eq_zero ι₁ (hrange₁.trans hE₁r.symm) Q)
              (Finsupp.mem_support_iff.mp hQ)
        · intro hQ
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Q, hS.mem_toFinset.mpr hQ, rfl⟩))
  obtain ⟨ι, hιo, hι, hιr⟩ := exists_isOpenImmersion_lift f₂ ι₁.opensRange ι₁ (by simp)
  haveI := hιo
  set g : Yb ⟶ Y₀ := f₂ ≫ g₁ with hg
  set gq : Yb ⟶ T₀ := g ≫ q with hgq
  have hιg : ι ≫ g = j := by rw [hg, ← Category.assoc, hι, hι₁]
  have hιgr : Set.range ι = g ⁻¹' Set.range j := by
    rw [hιr, hι₁r]; rfl
  have hgproj : IsProjective g := hres.isProjective.comp hg₁p
  obtain ⟨hYbpm, hgpm⟩ := isProjectiveMorphism_of_isProjective s₀
    ((MMP.Mori.isProjectiveVariety_iff k s₀).1 hY₀).2 g hgproj
  set sYb : Yb ⟶ Spec (.of k) := g ≫ s₀ with hsYb
  have hsYb' : sYb = f₂ ≫ g₁ ≫ s₀ := by rw [hsYb, hg, Category.assoc]
  have hYbv : AlgebraicGeometry.IsVariety k sYb := by rw [hsYb']; exact hres.isVariety_source
  haveI := hYbv
  haveI : MMP.Mori.IsProjectiveVariety k sYb :=
    (MMP.Mori.isProjectiveVariety_iff k sYb).2 ⟨hYbv, hYbpm⟩
  have hYbsm : IsSmoothScheme sYb := by rw [hsYb']; exact hres.isSmoothScheme
  haveI : IsIntegral Yb := hYbv.toIsIntegral
  haveI : IsLocallyNoetherian Yb := LocallyOfFiniteType.isLocallyNoetherian sYb
  haveI : CompactSpace Yb := QuasiCompact.compactSpace_of_compactSpace sYb
  haveI : Smooth sYb := (MMP.Mori.isSmoothScheme_iff _).1 hYbsm
  haveI : IsNormal Yb := isNormal_of_smooth_over_field sYb
  have hcart : ∀ D : Divisor Yb, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hYbsm
  haveI : Stacks.Ample.IsInvertibleModule Yb ((Scheme.Modules.pullback gq).obj Hb) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj gq Hb
  have hrange : Set.range ι = Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback gq).obj Hb) (pullbackGlobalSections gq Hb t) := by
    rw [hιgr, ← Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections, ht]
    rfl
  obtain ⟨E, hE0, ⟨eE⟩, hEr⟩ := exists_divisor_of_section hcart _
    (pullbackGlobalSections gq Hb t) (by rw [← hrange]; exact Set.range_nonempty _)
  haveI : Stacks.Ample.IsInvertibleModule Yb ((Scheme.Modules.pullback gq).obj (A 0)) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj gq (A 0)
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible Yb.sheaf.obj Yb.ringCatSheaf.property
      ((Scheme.Modules.pullback gq).obj (A 0)) :=
    ‹Stacks.Ample.IsInvertibleModule Yb ((Scheme.Modules.pullback gq).obj (A 0))›
  obtain ⟨G, ⟨eG⟩⟩ := MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible
    ((Scheme.Modules.pullback gq).obj (A 0))
  haveI : IsDominant W.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion W.ι
  have hcartY : ∀ D : Divisor Y, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  obtain ⟨T, hT⟩ := (hcartY Lc).exists_isPullback
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant W.ι Lc)
  have hιgq : ι ≫ gq = j ≫ q := by rw [hgq, ← Category.assoc, hιg]
  have eT : Nonempty ((Scheme.Modules.pullback ι).obj G.divisorialSheaf ≅ T.divisorialSheaf) := by
    obtain ⟨e0⟩ := eA0
    exact ⟨(Scheme.Modules.pullback ι).mapIso eG ≪≫
      (Scheme.Modules.pullbackComp ι gq).app _ ≪≫ (Scheme.Modules.pullbackCongr hιgq).app _ ≪≫
      e0 ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback W.ι).app _ ≪≫
      (Divisor.IsPullback.divisorialSheafIso (hBc := hcartY Lc) hT).symm⟩
  obtain ⟨G', ⟨eG'⟩, hG'⟩ := exists_linearlyEquivalent_coeff_eq ι (hcart G) T eT
  have hT₀v : AlgebraicGeometry.IsVariety k sT := hT₀.toIsVariety
  haveI : IsIntegral T₀ := hT₀v.toIsIntegral
  have hgqb : IsBirationalMorphism gq := by
    haveI : IsOpenImmersion (U.ι ≫ ι ≫ gq) := by rw [hιgq]; exact hUq
    exact isBirationalMorphism_of_isOpenImmersion_comp gq ι U hUW
  have hT₀p : IsProjectiveMorphism sT := ((MMP.Mori.isProjectiveVariety_iff k sT).1 hT₀).2
  have hgqpm : IsProjectiveMorphism gq := IsProjectiveMorphism.comp hgpm hqp
  set Bb : QDivisor Yb := ((c : ℚ)⁻¹) • Divisor.toQDivisor G' with hBb
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hBbc : ∀ P, Bb.coeff P = (c : ℚ)⁻¹ * G'.coeff P := fun P => rfl
  have hdecomp : Divisor.toQDivisor Bb.roundDown + Bb.fract = Bb :=
    DivisorWithCoeffs.roundDown_add_fract Bb
  have hBbW : ∀ Q : MMP.Mori.PrimeDivisor W,
      Bb.coeff (openPrimeDivisor ι Q) = B.coeff (openPrimeDivisor W.ι Q) := by
    intro Q
    rw [hBbc, hG' Q, coeff_of_isPullback_of_isOpenImmersion W.ι (hcartY Lc) hT Q]
    have := congrArg (DivisorWithCoeffs.coeff · (openPrimeDivisor W.ι Q)) hLc
    simp only [Divisor.coeff_toQDivisor] at this
    rw [this]
    change (c : ℚ)⁻¹ * ((c : ℚ) * B.coeff _) = B.coeff _
    rw [← mul_assoc, inv_mul_cancel₀ hcq, one_mul]
  refine H Yb sYb hYbsm ι ?_ E Bb.roundDown Bb.fract a₀ hE0 ?_ ?_ ?_ ?_
  · rw [hsYb, ← Category.assoc, hιg, hj]
  · rw [hrange, ← hEr]
  · have hsnc' : MMP.Resolution.IsSNCClosedSubset sYb
        ((exceptionalSet f₂ : Set Yb) ∪ f₂ ⁻¹' (D.sup fun E => E.idealSheaf.support)) := by
      rw [hsYb']; exact hsnc
    refine isSNC_of_isSNCClosedSubset sYb hsnc' Bb.fract fun P hP => ?_
    by_cases hPW : ∃ w, ι w ∈ P.support
    · obtain ⟨w, hw⟩ := hPW
      obtain ⟨Q, hQ⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
        ι P w hw
      rw [← openPrimeDivisor_eq_primeDivisorMap] at hQ
      subst hQ
      have hfr : B.fract.coeff (openPrimeDivisor W.ι Q) ≠ 0 := by
        have h := Finsupp.mem_support_iff.mp hP
        change Int.fract (Bb.coeff (openPrimeDivisor ι Q)) ≠ 0 at h
        rw [hBbW] at h
        rwa [DivisorWithCoeffs.coeff_fract]
      have hD : openPrimeDivisor ι₁ Q ∈ D :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Q, hS.mem_toFinset.mpr hfr, rfl⟩)
      have hcl : IsClosed (f₂ ⁻¹' ((openPrimeDivisor ι₁ Q).support : Set X₁)) :=
        (openPrimeDivisor ι₁ Q).idealSheaf.support.isClosed.preimage f₂.continuous
      intro y hy
      refine Or.inr ?_
      have hy' : y ∈ f₂ ⁻¹' ((openPrimeDivisor ι₁ Q).support : Set X₁) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
        refine closure_minimal ?_ hcl hy
        have hgp : AlgebraicGeometry.PrimeDivisor.genericPoint (openPrimeDivisor ι Q) =
            ι Q.genericPoint := genericPoint_openPrimeDivisor ι Q
        have hgp₁ : AlgebraicGeometry.PrimeDivisor.genericPoint (openPrimeDivisor ι₁ Q) =
            ι₁ Q.genericPoint := genericPoint_openPrimeDivisor ι₁ Q
        rw [Set.singleton_subset_iff, hgp]
        change f₂ (ι Q.genericPoint) ∈ ((openPrimeDivisor ι₁ Q).support : Set X₁)
        rw [← Scheme.Hom.comp_apply, hι, AlgebraicGeometry.PrimeDivisor.support_eq_closure, hgp₁]
        exact subset_closure rfl
      exact (Finset.le_sup (f := fun E : MMP.Mori.PrimeDivisor X₁ =>
        (E.idealSheaf.support : Set X₁)) hD) hy'
    · intro y hy
      refine Or.inr ?_
      have hyι : y ∉ Set.range ι := fun ⟨w, hw⟩ => hPW ⟨w, hw ▸ hy⟩
      rw [hιr, Set.mem_preimage, hrange₁, ← hE₁r, Set.notMem_compl_iff] at hyι
      obtain ⟨F, hF, hyF⟩ := DivisorWithCoeffs.mem_supp_iff.mp hyι
      have hD : F ∈ D := Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hF)
      exact (Finset.le_sup (f := fun E : MMP.Mori.PrimeDivisor X₁ =>
        (E.idealSheaf.support : Set X₁)) hD) hyF
  · intro m hm
    obtain ⟨e⟩ := nonempty_divisorialSheaf_add_nsmul_iso hcart gq (eG' ≪≫ eG) eE eA (c * m)
    haveI := hA (c * m)
    exact QDivisor.isNef_and_isBig_of_isBirationalMorphism sYb sT hYbv hYbpm hT₀v hT₀p gq
      (by rw [hgq, hsYb, Category.assoc, hs₀]) hgqpm hgqb (A (c * m))
      (hamp _ (hm.trans (Nat.le_mul_of_pos_left m hc))) c hc _ (hcart _) e _
      (toQDivisor_add_mul_nsmul_eq G' E hcq m)
  · intro P
    have h1 : Bb.roundDown + Bb.fract.roundUp = Bb.roundUp := by
      rw [← roundUp_toQDivisor_add, hdecomp]
    rw [h1, DivisorWithCoeffs.coeff_roundUp, DivisorWithCoeffs.coeff_roundUp, hBbW P]

/-- A nonempty open subscheme of a variety has the dimension of the variety. -/
private theorem topologicalKrullDim_eq_of_isOpenImmersion {k : Type} [Field k] {W X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX] (u : W ⟶ X) [IsOpenImmersion u]
    [Nonempty W] : topologicalKrullDim W = topologicalKrullDim X := by
  haveI : Nonempty u.opensRange := ⟨⟨u (Classical.arbitrary W), ⟨_, rfl⟩⟩⟩
  rw [← Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_opens k sX u.opensRange]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso u.isoOpensRange).isHomeomorph

/-- **Projective round-up vanishing, in the `Hgroup` spelling.** On a smooth projective variety,
if `L + Δ` is nef and big with `Δ` snc, then `Hⁱ(X, 𝒪_X(K + ⌈L + Δ⌉)) = 0` for `i > 0`. -/
private theorem isZero_hgroup_top_canonical_add_roundUp
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX] (hsm : IsSmoothScheme sX)
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (L : Divisor X) (Δ : QDivisor X) (hΔ : Δ.IsSNC sX)
    (hnef : (Divisor.toQDivisor L + Δ).IsNef k sX) (hbig : (Divisor.toQDivisor L + Δ).IsBig k sX)
    (i : ℕ) (hi : 0 < i) :
    IsZero (Hgroup X.ringCatSheaf ⊤ i
      (K + (Divisor.toQDivisor L + Δ).roundUp).divisorialSheaf) := by
  set F := (K + (Divisor.toQDivisor L + Δ).roundUp).divisorialSheaf
  haveI := MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_canonical_add_roundUp
    sX hsm hK L Δ hΔ hnef hbig (i : ℤ) (by exact_mod_cast hi)
  haveI : Subsingleton (cohomologyOverField k sX F i) :=
    (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k sX F
      i).toEquiv.subsingleton
  haveI : Subsingleton (Hgroup X.ringCatSheaf ⊤ i F) :=
    (AlgebraicGeometry.cohomologyOverFieldAddEquivHgroup k sX F i).symm.toEquiv.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- **Vanishing on a compactification.** Let `W ⊆ Y` be a nonempty quasi-compact open of a smooth
variety and `B` a `ℚ`-divisor on `Y`. Given the data of `CompactificationData` for `W` and `B`,
`Hⁱ(W, 𝒪_Y(K + ⌈B⌉)) = 0` for `i > 0`. -/
private theorem isZero_hgroup_of_compactificationData
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    (hsm : IsSmoothScheme sY)
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n) (B : QDivisor Y)
    (i : ℕ) (hi : 0 < i) (W : Y.Opens) [Nonempty W] [CompactSpace W] :
    CompactificationData sY W B
      (IsZero (Hgroup Y.ringCatSheaf W i (K + B.roundUp).divisorialSheaf)) := by
  classical
  intro X sX _ _ _ _ _ hsmX ι _ hιs E L Δ n₀ hE0 hrange hΔ hnb hcoeff
  have hdimX : topologicalKrullDim X = n := by
    rw [← hK.topologicalKrullDim_eq, ← topologicalKrullDim_eq_of_isOpenImmersion sX ι,
      topologicalKrullDim_eq_of_isOpenImmersion sY W.ι]
  obtain ⟨K', hK'⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sX hsmX hdimX
  have hEc : E.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsmX E
  set D : Divisor X := K' + (Divisor.toQDivisor (L + n₀ • E) + Δ).roundUp with hD
  haveI := hEc.isInvertibleModule_divisorialSheaf
  haveI := Divisor.isQuasicoherent_divisorialSheaf D
  have hT : ι ''ᵁ ⊤ = Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace)
      E.divisorialSheaf (Stacks.SheafOfModules.sectionsOfTop (X := X.toRingedSpace)
        E.divisorialSheaf (MMP.Threefold.Mori.oneSection hE0)) := by
    apply TopologicalSpace.Opens.ext
    rw [nonvanishingOpen_divisorialSheafOneSection hEc hE0, ← hrange]
    simp
  have hG : IsZero (Hgroup X.ringCatSheaf (ι ''ᵁ ⊤) i D.divisorialSheaf) := by
    rw [hT]
    refine isZero_hgroup_nonvanishingOpen (X := X) E.divisorialSheaf _ D.divisorialSheaf i
      fun k => ?_
    obtain ⟨e⟩ := nonempty_twist_divisorialSheaf_iso
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsmX D) hEc k
    refine IsZero.of_iso ?_ ((Hfunctor X.ringCatSheaf ⊤ i).mapIso e)
    have hDk : D + k • E = K' + (Divisor.toQDivisor (L + (n₀ + k) • E) + Δ).roundUp := by
      rw [hD, roundUp_toQDivisor_add, roundUp_toQDivisor_add, add_smul]
      abel
    rw [hDk]
    obtain ⟨h1, h2⟩ := hnb (n₀ + k) (Nat.le_add_right _ _)
    exact isZero_hgroup_top_canonical_add_roundUp sX hsmX hK' _ Δ hΔ h1 h2 i hi
  have hcoeff' : ∀ P : MMP.Mori.PrimeDivisor W,
      ((Divisor.toQDivisor (L + n₀ • E) + Δ).roundUp).coeff (openPrimeDivisor ι P) =
        B.roundUp.coeff (openPrimeDivisor W.ι P) := by
    intro P
    have hE : (n₀ • E).coeff (openPrimeDivisor ι P) = 0 := by
      change n₀ • E.coeff (openPrimeDivisor ι P) = 0
      rw [coeff_openPrimeDivisor_eq_zero ι hrange, smul_zero]
    rw [roundUp_toQDivisor_add, ← hcoeff P, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, hE, add_zero]
  obtain ⟨e3⟩ := nonempty_restrict_divisorialSheaf_iso sX sY hsmX hsm ι W.ι hιs hK' hK
    _ _ hcoeff'
  have e1 := (AlgebraicGeometry.CohomologyScalars.hfunctorOpenImmersionIso ι i).app
    D.divisorialSheaf
  have e2 := (AlgebraicGeometry.CohomologyScalars.hfunctorOpenImmersionIso W.ι i).app
    (K + B.roundUp).divisorialSheaf
  have hW' : W = W.ι ''ᵁ ⊤ := (Scheme.Opens.ι_image_top _).symm
  rw [hW']
  exact ((hG.of_iso e1.symm).of_iso ((Hfunctor _ ⊤ i).mapIso e3).symm).of_iso e2

/-- **`p^*𝓐^{⊗ N} ≅ 𝒪_Y(N w)`** for an invertible `𝓐` with `p^*𝓐 ≅ 𝒪_Y(w)`, `w` Cartier. -/
private theorem nonempty_pullback_tensorPowModule_iso_of_iso {X Y : Scheme.{0}}
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] (p : Y ⟶ X)
    (𝓐 : X.Modules) [Stacks.Ample.IsInvertibleModule X 𝓐] {w : Divisor Y}
    (ew : (Scheme.Modules.pullback p).obj 𝓐 ≅ w.divisorialSheaf) (hwc : w.IsCartier) (N : ℕ) :
    Nonempty ((Scheme.Modules.pullback p).obj (Stacks.Ample.tensorPowModule X 𝓐 (N : ℤ)) ≅
      (N • w).divisorialSheaf) := by
  haveI : Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback p).obj 𝓐) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  obtain ⟨e'⟩ := nonempty_tensorPowModule_iso_divisorialSheaf hwc
    ((Scheme.Modules.pullback p).obj 𝓐) ew N
  exact ⟨Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso p _ N ≪≫ e'⟩

/-- The vanishing `Hⁱ((p ≫ f)⁻¹V, 𝒪_Y(K + ⌈w/m⌉)) = 0`, for `i > 0`, over the preimage of one
affine open `V` of the base. -/
private theorem isZero_hgroup_preimage
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X S : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sS]
    (f : X ⟶ S) (hfs : f ≫ sS = sX) (hf : IsProjectiveMorphism f)
    {Y : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (p : Y ⟶ X) [AlgebraicGeometry.IsVariety k (p ≫ sX)] (hsm : IsSmoothScheme (p ≫ sX))
    (hp : IsProjectiveMorphism p) (hpb : IsBirationalMorphism p)
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor (p ≫ sX) n)
    (m : ℕ) (hm : 0 < m) (𝓐 : X.Modules) [Stacks.Ample.IsInvertibleModule X 𝓐]
    (h𝓐 : Stacks.RelativeAmple.IsRelativelyAmple f 𝓐)
    (w : Divisor Y) (ew : (Scheme.Modules.pullback p).obj 𝓐 ≅ w.divisorialSheaf)
    (hsnc : ((m : ℚ)⁻¹ • Divisor.toQDivisor w).fract.IsSNC (p ≫ sX))
    (i : ℕ) (hi : 0 < i) (V : S.Opens) (hV : IsAffineOpen V) :
    IsZero (Hgroup Y.ringCatSheaf ((p ≫ f) ⁻¹ᵁ V) i
      (K + ((m : ℚ)⁻¹ • Divisor.toQDivisor w).roundUp).divisorialSheaf) := by
  classical
  set B : QDivisor Y := (m : ℚ)⁻¹ • Divisor.toQDivisor w with hBdef
  set WX : X.Opens := f ⁻¹ᵁ V with hWX
  set W : Y.Opens := p ⁻¹ᵁ WX with hWdef
  change IsZero (Hgroup Y.ringCatSheaf W i (K + B.roundUp).divisorialSheaf)
  by_cases hWne : Nonempty W
  swap
  · have hbot : W = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hWne ⟨⟨x, hx⟩⟩
    rw [hbot]
    exact isZero_Hgroup_bot _ i
  haveI : IsIntegral X := ‹AlgebraicGeometry.IsVariety k sX›.toIsIntegral
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hp
  haveI : CompactSpace WX := compactSpace_preimage f hV.isCompact
  haveI : CompactSpace W := compactSpace_preimage p (isCompact_iff_compactSpace.mpr ‹_›)
  obtain ⟨w₀⟩ := hWne
  haveI : Nonempty W := ⟨w₀⟩
  haveI : Nonempty WX := ⟨⟨p w₀.1, w₀.2⟩⟩
  haveI : IsDominant p := hpb.isDominant
  have hwc : w.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm w
  have hC := isZero_hgroup_of_compactificationData (p ≫ sX) hsm hK B i hi W
  refine exists_invertibleClosure sX sS f hfs hf 𝓐 h𝓐 V hV inferInstance _ ?_
  intro N hN X₀ s₀X hX₀ jX hjXo hjX Hb hHb t ht Afam hAi a₀ hamp eA eA0X
  haveI := hjXo
  obtain ⟨Y₀, jY, q, hjYo, hqp, hY₀, hjq, hrY⟩ := exists_graphClosure p hp WX s₀X hX₀ jX
  haveI := hjYo
  -- a nonempty open of `W` on which `jY ≫ q` is an open immersion
  obtain ⟨U₁, hU₁, hU₁p⟩ := exists_isOpenImmersion_of_isBirationalMorphism hpb
  haveI := hU₁p
  set U : W.toScheme.Opens := W.ι ⁻¹ᵁ U₁ with hUdef
  have hUne : (U : Set W.toScheme).Nonempty := by
    obtain ⟨y, hyW, hyU⟩ := hU₁.inter_open_nonempty W W.isOpen ⟨w₀.1, w₀.2⟩
    exact ⟨⟨y, hyW⟩, hyU⟩
  have hUq : IsOpenImmersion (U.ι ≫ jY ≫ q) := by
    have h1 : (U.ι ≫ (p ∣_ WX)) ≫ WX.ι = (W.ι ∣_ U₁) ≫ U₁.ι ≫ p := by
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, ← morphismRestrict_ι W.ι U₁,
        Category.assoc]
    haveI : IsOpenImmersion ((U.ι ≫ (p ∣_ WX)) ≫ WX.ι) := by rw [h1]; infer_instance
    haveI := IsOpenImmersion.of_comp (U.ι ≫ (p ∣_ WX)) WX.ι
    rw [hjq, ← Category.assoc]
    infer_instance
  -- `A_0|_W ≅ 𝒪_Y(N w)|_W`
  obtain ⟨eP⟩ := nonempty_pullback_tensorPowModule_iso_of_iso p 𝓐 ew hwc N
  obtain ⟨eX⟩ := eA0X
  have eA0 : Nonempty ((Scheme.Modules.pullback (jY ≫ q)).obj (Afam 0) ≅
      (N • w).divisorialSheaf.restrict W.ι) :=
    ⟨(Scheme.Modules.pullbackCongr hjq).app _ ≪≫
      ((Scheme.Modules.pullbackComp (p ∣_ WX) jX).app _).symm ≪≫
      (Scheme.Modules.pullback (p ∣_ WX)).mapIso eX ≪≫
      (Scheme.Modules.pullbackComp (p ∣_ WX) WX.ι).app _ ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι p WX)).app _ ≪≫
      ((Scheme.Modules.pullbackComp W.ι p).app _).symm ≪≫
      (Scheme.Modules.pullback W.ι).mapIso eP ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app _).symm⟩
  have hLc : Divisor.toQDivisor (N • w) = ((N * m : ℕ) : ℚ) • B := by
    have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    ext P
    change (((N • w) P : ℤ) : ℚ) = ((N * m : ℕ) : ℚ) * ((m : ℚ)⁻¹ * ((w P : ℤ) : ℚ))
    simp only [Finsupp.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    field_simp
  have hjs : jY ≫ q ≫ s₀X = W.ι ≫ p ≫ sX := by
    rw [← Category.assoc, hjq, Category.assoc, hjX, ← Category.assoc, morphismRestrict_ι,
      Category.assoc]
  exact exists_compactification_of_projectiveClosure (p ≫ sX) hsm W B hsnc _ hC (N * m)
    (Nat.mul_pos hN hm) (N • w) hLc X₀ s₀X hX₀ Y₀ q hqp hY₀ jY inferInstance hjs U hUne hUq Hb hHb
    t (by rw [hrY, ht]) Afam hAi a₀ hamp eA eA0

end Main

end

end MMP.FourfoldProofs.FourfoldPullbackAmpleRelativeVanishingProof

end

section

public section

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.FourfoldProofs.FourfoldPullbackAmpleRelativeVanishingProof

/-- **Relative round-up vanishing for the pull-back of a relatively ample sheaf.** Let
`f : X ⟶ S` be a projective morphism of varieties over an algebraically closed field `k` of
characteristic zero, `p : Y ⟶ X` a projective birational morphism with `Y` smooth, `K` a
canonical divisor of `Y`, `𝓐` an `f`-ample invertible sheaf on `X` and `w` a divisor on `Y`
with `p^*𝓐 ≅ 𝒪_Y(w)`. If the fractional part of `w/m` has simple normal crossing support,
then `R^i (p ≫ f)_* 𝒪_Y(K + ⌈w/m⌉) = 0` for every `i > 0`. -/
public theorem isZero_rightDerived_pushforward_comp_roundUp_of_pullback_iso
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X S : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sS]
    (f : X ⟶ S) (hfs : f ≫ sS = sX) (hf : IsProjectiveMorphism f)
    {Y : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (p : Y ⟶ X) [AlgebraicGeometry.IsVariety k (p ≫ sX)] (hsm : IsSmoothScheme (p ≫ sX))
    (hp : IsProjectiveMorphism p) (hpb : IsBirationalMorphism p)
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor (p ≫ sX) n)
    (m : ℕ) (hm : 0 < m) (𝓐 : X.Modules) [Stacks.Ample.IsInvertibleModule X 𝓐]
    (h𝓐 : Stacks.RelativeAmple.IsRelativelyAmple f 𝓐)
    (w : Divisor Y) (ew : (Scheme.Modules.pullback p).obj 𝓐 ≅ w.divisorialSheaf)
    (hsnc : ((m : ℚ)⁻¹ • Divisor.toQDivisor w).fract.IsSNC (p ≫ sX)) (i : ℕ) (hi : 0 < i) :
    Limits.IsZero (((Scheme.Modules.pushforward (p ≫ f)).rightDerived i).obj
      (K + ((m : ℚ)⁻¹ • Divisor.toQDivisor w).roundUp).divisorialSheaf) := by
  letI := HasDerivedCategory.standard Y.Modules
  letI := HasDerivedCategory.standard S.Modules
  refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
    (Scheme.Modules.pushforward (p ≫ f)) (rfl : (i : ℤ) = (i : ℤ)) _).1 ?_
  exact Stacks.AffineHigherDirectImage.isZero_rightDerivedPlus_pushforward_of_isZero_hgroup_preimage
    (p ≫ f) _ i S.isBasis_affineOpens fun V hV =>
      isZero_hgroup_preimage sX sS f hfs hf p hsm hp hpb hK m hm 𝓐 h𝓐 w ew hsnc i hi V hV

/-- **Relative round-up vanishing for the pull-back of a relatively ample divisor.** Let
`f : X ⟶ S` be a projective morphism of varieties over an algebraically closed field `k` of
characteristic zero, `p : Y ⟶ X` a projective birational morphism with `Y` smooth, and `K` a
canonical divisor of `Y`. Let `L = (1/m) A` be an `f`-ample `ℚ`-Cartier divisor (`A` a Cartier
divisor, `m > 0`), `A'` the pull-back of `A` to `Y` and `w` its Weil divisor, so that
`p^*L = (1/m) w`. If the fractional part of `p^*L` has simple normal crossing support, then
`R^i (p ≫ f)_* 𝒪_Y(K + ⌈p^*L⌉) = 0` for every `i > 0`. -/
@[mmp "lem_fourfold_pullback_ample_relative_vanishing"]
public theorem isZero_rightDerived_pushforward_comp_divisorialSheaf_canonical_add_roundUp_pullback
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X S : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sS]
    (f : X ⟶ S) (hfs : f ≫ sS = sX) (hf : IsProjectiveMorphism f)
    {Y : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (p : Y ⟶ X) [AlgebraicGeometry.IsVariety k (p ≫ sX)] (hsm : IsSmoothScheme (p ≫ sX))
    (hp : IsProjectiveMorphism p) (hpb : IsBirationalMorphism p)
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor (p ≫ sX) n)
    (m : ℕ) (hm : 0 < m) (A : X.CartierDivisor)
    (hA : MMP.Resolution.IsRelativelyAmpleCartier f A)
    (A' : Y.CartierDivisor) (hA' : MMP.Intersection.IsPullback p A A')
    (w : Divisor Y) (hw : MMP.Intersection.IsWeilDivisorOfCartier A' w)
    (hsnc : ((m : ℚ)⁻¹ • Divisor.toQDivisor w).fract.IsSNC (p ≫ sX))
    (i : ℕ) (hi : 0 < i) :
    Limits.IsZero (((Scheme.Modules.pushforward (p ≫ f)).rightDerived i).obj
      (K + ((m : ℚ)⁻¹ • Divisor.toQDivisor w).roundUp).divisorialSheaf) := by
  haveI : IsIntegral X := ‹AlgebraicGeometry.IsVariety k sX›.toIsIntegral
  haveI : IsDominant p := hpb.isDominant
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
  obtain ⟨e⟩ := nonempty_pullback_sheaf_iso p hA'
  exact isZero_rightDerived_pushforward_comp_roundUp_of_pullback_iso sX sS f hfs hf p hsm hp
    hpb hK m hm _ (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _
      inferInstance hA) w (e ≪≫ hw.sheafIsoDivisorialSheaf) hsnc i hi

end MMP.Fourfold

end

end
