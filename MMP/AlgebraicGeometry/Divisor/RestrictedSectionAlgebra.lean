module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.LinearSystem

/-!
# The section algebra of a Weil divisor and its restriction algebra

Let `X` be a locally Noetherian normal scheme (for instance an integral normal variety) with ring
of rational functions `K(X)`, and let `B` be a Weil divisor on `X`. The *section algebra* of `B`
is the graded subring `⊕_{m ≥ 0} H⁰(X, 𝒪_X(mB)) tᵐ` of `K(X)[t]`: a polynomial `∑ gₘ tᵐ` lies in
it when every `gₘ` is zero or satisfies `div gₘ + mB ≥ 0`. Its degree-zero part is
`H⁰(X, 𝒪_X)`, by algebraic Hartogs.

For a prime divisor `S` not in the support of `B`, every `gₘ` is regular at the generic point
`η_S`, so lies in the discrete valuation ring `𝒪_{X,η_S}`; reducing modulo its maximal ideal is a
graded ring map to `k(S)[t]`, with `k(S) = κ(η_S)` the residue field at `η_S`. Its image is the
*restriction algebra* of `B` along `S`.

## Main definitions

* `MMP.Fourfold.divisorialSections`: `H⁰(X, 𝒪_X(D))` as an additive subgroup of `K(X)`.
* `MMP.Fourfold.weilSectionAlgebra`: the section algebra `⊕_{m ≥ 0} H⁰(X, 𝒪_X(mB)) tᵐ`.
* `MMP.Fourfold.localSubring`: the rational functions regular at the generic point of `S`.
* `MMP.Fourfold.residueAlong`: the residue map `𝒪_{X,η_S} → k(S)` on those.
* `MMP.Fourfold.weilRestrictionMap`, `MMP.Fourfold.weilRestrictionAlgebra`: the map
  `g tᵐ ↦ ḡ tᵐ` and its image.

## Main results

* `MMP.Fourfold.comap_C_weilSectionAlgebra`: the degree-zero part of the section algebra is the
  image of `Γ(X, 𝒪_X)` in `K(X)`; `MMP.Fourfold.weilSectionAlgebraDegreeZeroEquiv` identifies it
  with `Γ(X, 𝒪_X)`.
* `MMP.Fourfold.mem_weilRestrictionAlgebra_iff`: `q` lies in the restriction algebra exactly when
  some `p` in the section algebra has, in every degree `m`, a coefficient `p_m` whose component
  along `S` is the germ of some `a ∈ 𝒪_{X,η_S}` with `q_m = ā`.

## Implementation notes

The statements hold for any locally Noetherian normal scheme; integrality and being a variety
over a field are not used. The normality of `S` is not needed to define the restriction
algebra and is not assumed.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Polynomial

namespace MMP.Fourfold

open MMP.Mori

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-! ### Global sections of `𝒪_X(D)` inside `K(X)` -/

/-- The global sections `H⁰(X, 𝒪_X(D))`, as the additive subgroup of `K(X)` of the rational
functions `g` with `g = 0` or `div g + D ≥ 0`. -/
def divisorialSections (D : Divisor X) : AddSubgroup (RationalFunctions X) :=
  (D.divisorialSubmodule ⊤).toAddSubgroup.comap
    (rationalFunctionsPresheafTopEquiv X).symm.toAddMonoidHom

/-- A rational function `g` lies in `H⁰(X, 𝒪_X(D))` exactly when it is a divisorial section of
`D` over `X`. -/
theorem mem_divisorialSections {D : Divisor X} {g : RationalFunctions X} :
    g ∈ divisorialSections D ↔
      D.IsDivisorialSection ⊤ ((rationalFunctionsPresheafTopEquiv X).symm g) :=
  Iff.rfl

/-- For an effective divisor `D`, the constant function `1` lies in `H⁰(X, 𝒪_X(D))`. -/
theorem one_mem_divisorialSections {D : Divisor X} (hD : 0 ≤ D) :
    (1 : RationalFunctions X) ∈ divisorialSections D := by
  rw [mem_divisorialSections, map_one]
  exact Divisor.IsDivisorialSection.one hD ⊤

/-- The product of sections of `𝒪_X(D)` and `𝒪_X(D')` is a section of `𝒪_X(D + D')`. -/
theorem mul_mem_divisorialSections {D D' : Divisor X} {g h : RationalFunctions X}
    (hg : g ∈ divisorialSections D) (hh : h ∈ divisorialSections D') :
    g * h ∈ divisorialSections (D + D') := fun E hE => by
  rw [DivisorWithCoeffs.coeff_add, neg_add]
  exact (hg E hE).mul (hh E hE)

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The ring map `Γ(X, 𝒪_X) → K(X)` sending a regular function to its germs at the generic points
of the irreducible components. -/
def globalSectionsToRationalFunctions : Γ(X, ⊤) →+* RationalFunctions X :=
  (rationalFunctionsPresheafTopEquiv X).toRingHom.comp
    ((toRationalFunctionsPresheaf X).app (op ⊤)).hom

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The image of a regular function `s` in `K(X)` is its image under the presheaf map to
rational functions, read in `K(X)`. -/
theorem globalSectionsToRationalFunctions_apply (s : Γ(X, ⊤)) :
    globalSectionsToRationalFunctions s =
      rationalFunctionsPresheafTopEquiv X ((toRationalFunctionsPresheaf X).app (op ⊤) s) :=
  rfl

omit [IsLocallyNoetherian X] in
/-- On a normal scheme, a regular function is determined by its germs at the generic points:
the map `Γ(X, 𝒪_X) → K(X)` is injective. -/
theorem globalSectionsToRationalFunctions_injective :
    Function.Injective (globalSectionsToRationalFunctions (X := X)) :=
  (rationalFunctionsPresheafTopEquiv X).injective.comp (toRationalFunctionsPresheaf_app_injective ⊤)

/-- `H⁰(X, 𝒪_X(0))` is the image of `Γ(X, 𝒪_X)` in `K(X)` (algebraic Hartogs). -/
theorem mem_divisorialSections_zero_iff {g : RationalFunctions X} :
    g ∈ divisorialSections (0 : Divisor X) ↔
      g ∈ (globalSectionsToRationalFunctions (X := X)).range := by
  constructor
  · intro hg
    obtain ⟨s, hs⟩ := Divisor.IsDivisorialSection.exists_eq hg
    exact ⟨s, by
      rw [globalSectionsToRationalFunctions_apply, hs]
      exact (rationalFunctionsPresheafTopEquiv X).apply_symm_apply g⟩
  · rintro ⟨s, rfl⟩
    rw [mem_divisorialSections, globalSectionsToRationalFunctions_apply,
      RingEquiv.symm_apply_apply]
    exact Divisor.isDivisorialSection_algebraMap (le_refl 0) s

/-! ### The section algebra -/

/-- The *section algebra* `⊕_{m ≥ 0} H⁰(X, 𝒪_X(mB)) tᵐ ⊆ K(X)[t]` of a Weil divisor `B`: the
polynomials whose degree-`m` coefficient `g` is zero or satisfies `div g + mB ≥ 0`. -/
@[mmp "def_fourfold_weil_section_algebra"]
def weilSectionAlgebra (B : Divisor X) : Subring (RationalFunctions X)[X] where
  carrier := {p | ∀ m : ℕ, p.coeff m ∈ divisorialSections (m • B)}
  zero_mem' m := by
    rw [coeff_zero]
    exact zero_mem _
  one_mem' m := by
    rw [coeff_one]
    split_ifs with h
    · subst h
      rw [zero_smul]
      exact one_mem_divisorialSections le_rfl
    · exact zero_mem _
  add_mem' hp hq m := by
    rw [coeff_add]
    exact add_mem (hp m) (hq m)
  neg_mem' hp m := by
    rw [coeff_neg]
    exact neg_mem (hp m)
  mul_mem' {p q} hp hq m := by
    rw [coeff_mul]
    refine AddSubgroup.sum_mem _ fun x hx => ?_
    have h := mul_mem_divisorialSections (hp x.1) (hq x.2)
    have hx' : x.1 + x.2 = m := by simpa using hx
    rwa [← add_smul, hx'] at h

/-- A polynomial `p` lies in the section algebra of `B` exactly when its degree-`m` coefficient
lies in `H⁰(X, 𝒪_X(mB))` for every `m`. -/
theorem mem_weilSectionAlgebra {B : Divisor X} {p : (RationalFunctions X)[X]} :
    p ∈ weilSectionAlgebra B ↔ ∀ m : ℕ, p.coeff m ∈ divisorialSections (m • B) :=
  Iff.rfl

/-- The section algebra is graded: `g tᵐ` lies in it exactly when `g ∈ H⁰(X, 𝒪_X(mB))`. -/
theorem monomial_mem_weilSectionAlgebra {B : Divisor X} {m : ℕ} {g : RationalFunctions X} :
    monomial m g ∈ weilSectionAlgebra B ↔ g ∈ divisorialSections (m • B) := by
  refine ⟨fun h => by simpa using h m, fun h n => ?_⟩
  rw [coeff_monomial]
  split_ifs with hmn
  · exact hmn ▸ h
  · exact zero_mem _

/-- The degree-zero part of the section algebra is `H⁰(X, 𝒪_X)`, the image of `Γ(X, 𝒪_X)`. -/
@[mmp "def_fourfold_weil_section_algebra"]
theorem comap_C_weilSectionAlgebra (B : Divisor X) :
    (weilSectionAlgebra B).comap C = (globalSectionsToRationalFunctions (X := X)).range := by
  ext g
  rw [Subring.mem_comap, ← monomial_zero_left, monomial_mem_weilSectionAlgebra, zero_smul,
    mem_divisorialSections_zero_iff]

/-- The ring isomorphism from `Γ(X, 𝒪_X)` to the degree-zero part of the section algebra of `B`,
sending a regular function to its image in `K(X)`. -/
@[mmp "def_fourfold_weil_section_algebra"]
def weilSectionAlgebraDegreeZeroEquiv (B : Divisor X) :
    Γ(X, ⊤) ≃+* (weilSectionAlgebra B).comap C :=
  letI : Nonempty Γ(X, ⊤) := ⟨0⟩
  (RingEquiv.ofLeftInverse
    (Function.leftInverse_invFun globalSectionsToRationalFunctions_injective)).trans
    (RingEquiv.subringCongr (comap_C_weilSectionAlgebra B).symm)

/-- `weilSectionAlgebraDegreeZeroEquiv` sends a regular function to its image in `K(X)`. -/
@[simp]
theorem coe_weilSectionAlgebraDegreeZeroEquiv_apply (B : Divisor X) (s : Γ(X, ⊤)) :
    (weilSectionAlgebraDegreeZeroEquiv B s : RationalFunctions X) =
      globalSectionsToRationalFunctions s :=
  rfl

/-! ### Residues along a prime divisor -/

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The rational functions regular at the generic point `η_S` of a prime divisor `S`: those
whose component on the irreducible component of `S` comes from `𝒪_{X,η_S}`. -/
def localSubring (S : Mori.PrimeDivisor X) : Subring (RationalFunctions X) :=
  S.toComponent.hom.range.comap (RationalFunctions.component X S.component)

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A rational function `g` is regular at `η_S` exactly when its component along `S` is the
germ of some `a ∈ 𝒪_{X,η_S}`. -/
theorem mem_localSubring {S : Mori.PrimeDivisor X} {g : RationalFunctions X} :
    g ∈ localSubring S ↔ ∃ a : S.localRing, S.toComponent.hom a = g S.component :=
  Iff.rfl

/-- The residue `g ↦ ḡ ∈ k(S)` of a rational function regular at `η_S`, through the valuation
ring `𝒪_{X,η_S}`. -/
def residueAlong (S : Mori.PrimeDivisor X) : localSubring S →+* X.residueField S.genericPoint :=
  (X.residue S.genericPoint).hom.comp <|
    (RingEquiv.ofLeftInverse (Function.leftInverse_invFun
      (stalkToRationalFunctions_injective S.genericPoint_mem_component))).symm.toRingHom.comp <|
      ((RationalFunctions.component X S.component).comp (localSubring S).subtype).codRestrict _
        fun g => g.2

omit [IsLocallyNoetherian X] in
/-- The residue of `g` at `η_S` is the residue `ā` of any `a ∈ 𝒪_{X,η_S}` whose germ is the
component of `g` along `S`. -/
theorem residueAlong_eq {S : Mori.PrimeDivisor X} (g : localSubring S) {a : S.localRing}
    (ha : S.toComponent.hom a = (g : RationalFunctions X) S.component) :
    residueAlong S g = X.residue S.genericPoint a := by
  simp only [residueAlong, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.ofLeftInverse_symm_apply]
  congr 1
  change Function.invFun _ ((g : RationalFunctions X) S.component) = a
  rw [← ha]
  exact Function.leftInverse_invFun
    (stalkToRationalFunctions_injective S.genericPoint_mem_component) a

/-- Off the support of `B`, every section of `𝒪_X(mB)` is regular at the generic point of `S`. -/
theorem divisorialSections_le_localSubring {B : Divisor X} {S : Mori.PrimeDivisor X}
    (hS : B.coeff S = 0) (m : ℕ) :
    (divisorialSections (m • B) : Set (RationalFunctions X)) ⊆ localSubring S := by
  intro g hg
  have hne : (S.support ∩ (⊤ : X.Opens)).Nonempty := ⟨S.genericPoint, by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl, trivial⟩
  have h := hg S hne
  rw [DivisorWithCoeffs.coeff_smul, hS, smul_zero, neg_zero] at h
  change S.OrdGE 0 (g S.component) at h
  rcases h with h0 | hv
  · exact ⟨0, (map_zero _).trans h0.symm⟩
  · rw [WithZero.exp_zero] at hv
    exact S.exists_toComponent_eq_of_one_le_valuation hv

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The ring map `(localSubring S)[t] → K(X)[t]` induced by the inclusion of the functions
regular at `η_S`. -/
abbrev localPolynomialMap (S : Mori.PrimeDivisor X) :
    (localSubring S)[X] →+* (RationalFunctions X)[X] :=
  mapRingHom (localSubring S).subtype

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The inclusion of polynomials over the functions regular at `η_S` into `K(X)[t]` is
injective. -/
theorem localPolynomialMap_injective (S : Mori.PrimeDivisor X) :
    Function.Injective (localPolynomialMap S) :=
  map_injective _ Subtype.val_injective

/-- For `S` not in the support of `B`, every polynomial in the section algebra of `B` has all
its coefficients regular at `η_S`. -/
theorem weilSectionAlgebra_le_range {B : Divisor X} {S : Mori.PrimeDivisor X}
    (hS : B.coeff S = 0) : weilSectionAlgebra B ≤ (localPolynomialMap S).range := fun p hp =>
  (mem_lifts p).mp <| (lifts_iff_coeff_lifts p).mpr fun m =>
    ⟨⟨_, divisorialSections_le_localSubring hS m (hp m)⟩, rfl⟩

/-! ### The restriction algebra -/

/-- The graded *restriction map* `g tᵐ ↦ ḡ tᵐ` from the section algebra of `B` to `k(S)[t]`,
for a prime divisor `S` not in the support of `B`. -/
@[mmp "def_fourfold_weil_restriction_algebra"]
def weilRestrictionMap {B : Divisor X} {S : Mori.PrimeDivisor X} (hS : B.coeff S = 0) :
    weilSectionAlgebra B →+* (X.residueField S.genericPoint)[X] :=
  (mapRingHom (residueAlong S)).comp <|
    (RingEquiv.ofLeftInverse (Function.leftInverse_invFun
      (localPolynomialMap_injective S))).symm.toRingHom.comp <|
      Subring.inclusion (weilSectionAlgebra_le_range hS)

/-- The degree-`m` coefficient of the restriction of `p` is `ā`, for any `a ∈ 𝒪_{X,η_S}` whose
germ is the component along `S` of the degree-`m` coefficient of `p`. -/
theorem coeff_weilRestrictionMap {B : Divisor X} {S : Mori.PrimeDivisor X} (hS : B.coeff S = 0)
    (p : weilSectionAlgebra B) (m : ℕ) {a : S.localRing}
    (ha : S.toComponent.hom a = (p : (RationalFunctions X)[X]).coeff m S.component) :
    (weilRestrictionMap hS p).coeff m = X.residue S.genericPoint a := by
  set q := Function.invFun (localPolynomialMap S) (p : (RationalFunctions X)[X])
  have hqp : localPolynomialMap S q = p :=
    Function.invFun_eq (weilSectionAlgebra_le_range hS p.2)
  rw [show weilRestrictionMap hS p = q.map (residueAlong S) from rfl, coeff_map]
  refine residueAlong_eq _ ?_
  rw [ha, ← hqp]
  simp

/-- The *restriction algebra* of the section algebra of `B` along a prime divisor `S` not in the
support of `B`: the image in `k(S)[t]` of `g tᵐ ↦ ḡ tᵐ`. -/
@[mmp "def_fourfold_weil_restriction_algebra"]
def weilRestrictionAlgebra {B : Divisor X} {S : Mori.PrimeDivisor X} (hS : B.coeff S = 0) :
    Subring (X.residueField S.genericPoint)[X] :=
  (weilRestrictionMap hS).range

/-- `q ∈ k(S)[t]` lies in the restriction algebra exactly when some `p` in the section algebra
has, in every degree `m`, a coefficient whose component along `S` is the germ of some
`a ∈ 𝒪_{X,η_S}` with `q_m = ā`. -/
@[mmp "def_fourfold_weil_restriction_algebra"]
theorem mem_weilRestrictionAlgebra_iff {B : Divisor X} {S : Mori.PrimeDivisor X}
    (hS : B.coeff S = 0) {q : (X.residueField S.genericPoint)[X]} :
    q ∈ weilRestrictionAlgebra hS ↔ ∃ p ∈ weilSectionAlgebra B, ∀ m : ℕ,
      ∃ a : S.localRing, S.toComponent.hom a = p.coeff m S.component ∧
        q.coeff m = X.residue S.genericPoint a := by
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨p, p.2, fun m => ?_⟩
    obtain ⟨a, ha⟩ := divisorialSections_le_localSubring hS m (p.2 m)
    exact ⟨a, ha, coeff_weilRestrictionMap hS p m ha⟩
  · rintro ⟨p, hp, h⟩
    refine ⟨⟨p, hp⟩, ext fun m => ?_⟩
    obtain ⟨a, ha, hq⟩ := h m
    exact (coeff_weilRestrictionMap hS ⟨p, hp⟩ m ha).trans hq.symm

end MMP.Fourfold
