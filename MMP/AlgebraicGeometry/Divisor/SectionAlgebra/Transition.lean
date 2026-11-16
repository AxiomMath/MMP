module

public import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Twist
public import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections

/-!
# The transition functions of `𝒪(1)` on the relative `Proj` of a divisorial algebra

Let `Y` be an integral, quasi-compact, locally Noetherian, normal scheme, `D` a Weil divisor on
`Y`, `g : Z = Proj_Y ⨁_n 𝒪_Y(nD) ⟶ Y` with `Z` integral and normal, and `W` an affine open of
`Y`. For nonzero sections `a, b` of `𝒪_Y(D)(W)`, viewed as units `φ_a, φ_b` of `K(Y)`, the
section `a / b` of the chart `Proj ⨁_n 𝒪_Y(nD)(W)` over `D₊(b)` is, as a rational function on
`Z`, the pull-back `g^*(φ_a / φ_b)`.

The point is that `g` restricted to the chart `D₊(b) = Spec S_{(b)}` is induced by `r ↦ r / 1`
on `Γ(Y, W)`, and that `S_{(b)}` embeds in `K(Y) = Frac Γ(Y, W)` with `a / b ↦ φ_a / φ_b`: writing
`φ_a / φ_b = p / q` with `p, q ∈ Γ(Y, W)` gives `(a / b) · (q / 1) = p / 1` in `S_{(b)}`.

## Main results

* `MMP.Fourfold.DivisorialSectionAlgebra.germ_fracSection_mul_eq`: the identity at a point of
  `D₊(b)` lying over the generic point of `Y`.
* `MMP.Fourfold.DivisorialSectionAlgebra.algebraMap_fracSection_mul_pullbackRationalFunction_eq`:
  the identity `(a / b) · g^*φ_b = g^*φ_a` in `𝒦_Z` over `D₊(b)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], Lemma 6.2.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite HomogeneousLocalization

universe u

namespace MMP.Fourfold.DivisorialSectionAlgebra

open MMP.Mori MMP.Mori.Divisor Stacks.RelativeProj MMP.ProjFraction

section Chart

variable {S : Type u} [CommRing S] {σ : Type u} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- On the chart `Spec S_{(f)} ⟶ Proj S`, the germ of a fraction `x ∈ S_{(f)}`, read as a
function on `D₊(f)`, is the germ of `x` at the corresponding point of `Spec S_{(f)}`. -/
theorem stalkMap_awayι_germ_awayToSection {m : ℕ} {f : S} (hf : f ∈ 𝒮 m) (hm : 0 < m)
    (p : Spec (.of (Away 𝒮 f))) (hp : Proj.awayι 𝒮 f hf hm p ∈ Proj.basicOpen 𝒮 f)
    (x : Away 𝒮 f) :
    (Proj.awayι 𝒮 f hf hm).stalkMap p
        ((AlgebraicGeometry.Proj 𝒮).presheaf.germ (Proj.basicOpen 𝒮 f) _ hp
          ((Proj.awayToSection 𝒮 f).hom x)) =
      (Spec (.of (Away 𝒮 f))).presheaf.germ ⊤ p trivial
        ((Scheme.ΓSpecIso (.of (Away 𝒮 f))).inv.hom x) := by
  have e : (⊤ : (Spec (.of (Away 𝒮 f))).Opens) ≤
      Proj.awayι 𝒮 f hf hm ⁻¹ᵁ Proj.basicOpen 𝒮 f := fun q _ => by
    rw [← Proj.opensRange_awayι 𝒮 f hf hm]
    exact ⟨q, rfl⟩
  rw [← Stacks.AlgebraicGeometry.ProjTwistChain.appLE_awayι_awayToSection hm hf e x,
    Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply]
  exact (TopCat.Presheaf.germ_res_apply _ (homOfLE e) p trivial _).symm

/-- The fraction `a / b` of `S_{(b)}` is the section `a / b` of `Proj S` over `D₊(b)`. -/
theorem awayToSection_mk_eq_fracSection {a b : S} (ha : a ∈ 𝒮 1) (hb : b ∈ 𝒮 1)
    (ha' : a ∈ 𝒮 (1 • 1)) :
    (Proj.awayToSection 𝒮 b).hom (Away.mk 𝒮 hb 1 a ha') = fracSection 𝒮 ha hb le_rfl := by
  refine Subtype.ext (funext fun x => HomogeneousLocalization.val_injective _ ?_)
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  change _ = (fracFun _ ha hb le_rfl x).val
  erw [val_fracFun]
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.map_mk', Localization.mk_eq_mk']
  simp only [RingHom.id_apply, pow_one]

/-- Along an open immersion `j : Proj S ⟶ X`, the germ at a point of `j(D₊(f))` of a fraction
`x ∈ S_{(f)}`, read as a section of `X` over `j(D₊(f))` and pulled back to the chart
`Spec S_{(f)}`, is the germ of `x`. -/
theorem stalkMap_awayι_comp_germ_appIso_inv {X : Scheme.{u}} (j : AlgebraicGeometry.Proj 𝒮 ⟶ X)
    [IsOpenImmersion j] {m : ℕ} {f : S} (hf : f ∈ 𝒮 m) (hm : 0 < m)
    (p : Spec (.of (Away 𝒮 f))) (hp : Proj.awayι 𝒮 f hf hm p ∈ Proj.basicOpen 𝒮 f)
    (hjp : j (Proj.awayι 𝒮 f hf hm p) ∈ j ''ᵁ Proj.basicOpen 𝒮 f) (x : Away 𝒮 f) :
    (Proj.awayι 𝒮 f hf hm ≫ j).stalkMap p
        (X.presheaf.germ (j ''ᵁ Proj.basicOpen 𝒮 f) _ hjp
          ((j.appIso (Proj.basicOpen 𝒮 f)).inv ((Proj.awayToSection 𝒮 f).hom x))) =
      (Spec (.of (Away 𝒮 f))).presheaf.germ ⊤ p trivial
        ((Scheme.ΓSpecIso (.of (Away 𝒮 f))).inv.hom x) := by
  have hjS : (j.stalkMap (Proj.awayι 𝒮 f hf hm p)).hom
      (X.presheaf.germ (j ''ᵁ Proj.basicOpen 𝒮 f) _ hjp
        ((j.appIso (Proj.basicOpen 𝒮 f)).inv ((Proj.awayToSection 𝒮 f).hom x))) =
      (AlgebraicGeometry.Proj 𝒮).presheaf.germ (Proj.basicOpen 𝒮 f) _ hp
        ((Proj.awayToSection 𝒮 f).hom x) := by
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  refine (congrArg (fun φ => φ.hom (X.presheaf.germ (j ''ᵁ Proj.basicOpen 𝒮 f) _ hjp
    ((j.appIso (Proj.basicOpen 𝒮 f)).inv ((Proj.awayToSection 𝒮 f).hom x))))
      (Scheme.Hom.stalkMap_comp (Proj.awayι 𝒮 f hf hm) j p)).trans ?_
  exact (congrArg ((Proj.awayι 𝒮 f hf hm).stalkMap p).hom hjS).trans
    (stalkMap_awayι_germ_awayToSection 𝒮 hf hm p hp x)

/-- Along an open immersion `j : Proj S ⟶ X`, the germ at a point of `j(D₊(b))` of the section
`a / b`, `a, b` of degree one, pulled back to the chart `Spec S_{(b)}`, is the germ of `a / b`. -/
theorem stalkMap_awayι_comp_germ_appIso_inv_fracSection {X : Scheme.{u}}
    (j : AlgebraicGeometry.Proj 𝒮 ⟶ X) [IsOpenImmersion j] {a b : S} (ha : a ∈ 𝒮 1)
    (hb : b ∈ 𝒮 1) (ha' : a ∈ 𝒮 (1 • 1)) (p : Spec (.of (Away 𝒮 b)))
    (hp : Proj.awayι 𝒮 b hb one_pos p ∈ ProjectiveSpectrum.basicOpen 𝒮 b)
    (hjp : j (Proj.awayι 𝒮 b hb one_pos p) ∈ j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 b) :
    (Proj.awayι 𝒮 b hb one_pos ≫ j).stalkMap p
        (X.presheaf.germ (j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 b) _ hjp
          ((j.appIso (ProjectiveSpectrum.basicOpen 𝒮 b)).inv (fracSection 𝒮 ha hb le_rfl))) =
      (Spec (.of (Away 𝒮 b))).presheaf.germ ⊤ p trivial
        ((Scheme.ΓSpecIso (.of (Away 𝒮 b))).inv.hom (Away.mk 𝒮 hb 1 a ha')) := by
  have h := stalkMap_awayι_comp_germ_appIso_inv 𝒮 j hb one_pos p hp hjp (Away.mk 𝒮 hb 1 a ha')
  rwa [awayToSection_mk_eq_fracSection 𝒮 ha hb ha'] at h

end Chart

/-- The stalk maps of a composite `c ≫ g` after generization: for `g (c p) = y₀`, generizing to
`𝒪_{Y,y₀}` and mapping along `g` then `c` is generizing and mapping along `c ≫ g`. -/
theorem stalkMap_stalkSpecializes_stalkMap_comp {P X Y : Scheme.{u}} (c : P ⟶ X) (g : X ⟶ Y)
    (p : P) {y₀ : Y} (hx : g (c p) = y₀) (t : Y.presheaf.stalk y₀) :
    (c.stalkMap p).hom ((Y.presheaf.stalkSpecializes (specializes_of_eq hx) ≫
        g.stalkMap (c p)).hom t) =
      (Y.presheaf.stalkSpecializes (specializes_of_eq (show (c ≫ g) p = y₀ from hx)) ≫
        (c ≫ g).stalkMap p).hom t :=
  (congrArg (fun φ => φ.hom ((Y.presheaf.stalkSpecializes (specializes_of_eq hx)).hom t))
    (Scheme.Hom.stalkMap_comp c g p)).symm

/-- For a morphism `Spec R ⟶ Y` induced by a ring map `Φ : Γ(Y, W) → R` on an affine open `W`,
the stalk map sends the germ of `r ∈ Γ(Y, W)` to the germ of `Φ r`. -/
theorem stalkMap_germ_eq_of_eq_SpecMap_fromSpec {X : Scheme.{u}} {W : X.Opens}
    (hW : IsAffineOpen W) {R : CommRingCat.{u}} (Φ : Γ(X, W) ⟶ R) (G : Spec R ⟶ X)
    (hG : G = Spec.map Φ ≫ hW.fromSpec) (p : Spec R) (hp : G p ∈ W) (r : Γ(X, W)) :
    G.stalkMap p (X.presheaf.germ W _ hp r) =
      (Spec R).presheaf.germ ⊤ p trivial ((Scheme.ΓSpecIso R).inv.hom (Φ.hom r)) := by
  subst hG
  have hp'' : hW.fromSpec (Spec.map Φ p) ∈ W := hp
  have h3 : (Spec.map Φ ≫ hW.fromSpec).stalkMap p (X.presheaf.germ W _ hp r) =
      (Spec.map Φ).stalkMap p (hW.fromSpec.stalkMap (Spec.map Φ p)
        (X.presheaf.germ W (hW.fromSpec (Spec.map Φ p)) hp'' r)) :=
    congrArg (fun φ => φ.hom (X.presheaf.germ W _ hp r)) (Scheme.Hom.stalkMap_comp _ _ p)
  rw [h3, Scheme.Hom.germ_stalkMap_apply, IsAffineOpen.fromSpec_app_self_apply]
  erw [TopCat.Presheaf.germ_res_apply]
  rw [Scheme.Hom.germ_stalkMap_apply]
  have h := congrArg (fun φ : Γ(X, W) ⟶ Γ(Spec R, ⊤) => φ.hom r)
    (Scheme.ΓSpecIso_inv_naturality Φ)
  simp only [CommRingCat.comp_apply] at h
  exact (congrArg (fun s => (Spec R).presheaf.germ ⊤ p trivial s) h).symm

/-- An identity `e · g^*ψ = g^*φ` in a stalk of `X` can be checked after an open immersion
`c : P ⟶ X`, where it reads `e' · (c ≫ g)^*ψ = (c ≫ g)^*φ` for the image `e'` of `e`. -/
theorem mul_stalkMap_eq_of_stalkMap_comp {P X Y : Scheme.{u}} (c : P ⟶ X) [IsOpenImmersion c]
    (g : X ⟶ Y) (p : P) {y₀ : Y} (hx : g (c p) = y₀) (s t : Y.presheaf.stalk y₀)
    {e : X.presheaf.stalk (c p)} {e' : P.presheaf.stalk p} (he : (c.stalkMap p).hom e = e')
    (h : e' * (Y.presheaf.stalkSpecializes (specializes_of_eq (show (c ≫ g) p = y₀ from hx)) ≫
        (c ≫ g).stalkMap p).hom s =
      (Y.presheaf.stalkSpecializes (specializes_of_eq (show (c ≫ g) p = y₀ from hx)) ≫
        (c ≫ g).stalkMap p).hom t) :
    e * (Y.presheaf.stalkSpecializes (specializes_of_eq hx) ≫ g.stalkMap (c p)).hom s =
      (Y.presheaf.stalkSpecializes (specializes_of_eq hx) ≫ g.stalkMap (c p)).hom t := by
  have : IsIso (c.stalkMap p) := inferInstanceAs (IsIso (c.toLRSHom.stalkMap p))
  apply (asIso (c.stalkMap p)).commRingCatIsoToRingEquiv.injective
  change (c.stalkMap p).hom _ = (c.stalkMap p).hom _
  rwa [map_mul, he, stalkMap_stalkSpecializes_stalkMap_comp c g p hx,
    stalkMap_stalkSpecializes_stalkMap_comp c g p hx]

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {D : Divisor Y}
  (A : DivisorialSectionAlgebra (𝟙 Y) D)

/-- The inverse of the pull-back of `φ⁻¹` is the image of `φ` under the extension of function
fields. -/
theorem coe_inv_pullbackRationalFunction_inv_apply [CompactSpace Y] {X : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ Y) [IsDominant f] (φ : (RationalFunctions Y)ˣ)
    (hφ : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ (principalDivisor φ⁻¹).supp)
    (ZX : irreducibleComponents X) (ZY : irreducibleComponents Y) :
    (((pullbackRationalFunction f φ⁻¹ hφ)⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) ZX =
      fieldMap f ZY ZX ((φ : RationalFunctions Y) ZY) := by
  set P := pullbackRationalFunction f φ⁻¹ hφ
  have h1 : ((P⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) ZX *
      (P : RationalFunctions X) ZX = 1 := by
    rw [← Pi.mul_apply, Units.inv_mul, Pi.one_apply]
  have h2 : (P : RationalFunctions X) ZX =
      fieldMap f ZY ZX (((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) ZY) :=
    pullbackComponent_eq_fieldMap f hφ (Divisor.isLocalEquation_principalDivisor φ⁻¹ ⊤) ZX
      trivial ZY
  have h3 : fieldMap f ZY ZX ((φ : RationalFunctions Y) ZY) *
      fieldMap f ZY ZX (((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) ZY) = 1 := by
    rw [← map_mul, ← Pi.mul_apply, Units.mul_inv, Pi.one_apply, map_one]
  rw [h2] at h1
  linear_combination (-(((P⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) ZX)) * h3 +
    fieldMap f ZY ZX ((φ : RationalFunctions Y) ZY) * h1

/-- On an affine open `W`, every element `t` of a local ring `𝒪_{X,x}`, `x ∈ W`, is a fraction
`r / s` of sections over `W`: `r = t s` with `s` a unit at `x`. -/
theorem exists_germ_eq_mul_germ_of_isAffineOpen {X : Scheme.{u}} {W : X.Opens}
    (hW : IsAffineOpen W) {x : X} (hx : x ∈ W) (t : X.presheaf.stalk x) :
    ∃ r s : Γ(X, W), IsUnit (X.presheaf.germ W x hx s) ∧
      X.presheaf.germ W x hx r = t * X.presheaf.germ W x hx s := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (U := W) ⟨x, hx⟩
  have := hW.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl t
  exact ⟨r, s, IsLocalization.map_units _ s, h.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- **The transition identity in the chart ring.** Let `a, b` be sections of degree one over `W`,
`b ≠ 0`, equal at the generic point to units `φ, ψ` of `K(Y)`, and let `p, q ∈ Γ(Y, W)` with
`p ψ = φ q` at the generic point. Then `(a / b) · (q / 1) = p / 1` in `S_{(b)}`. -/
theorem away_mk_mul_fromZeroRingHom_eq {W : Y.Opens} (ZY : irreducibleComponents Y)
    (hZW : componentGenericPoint Y ZY ∈ W) (a b : A.situation.sectionPieces W 1) (hb0 : b ≠ 0)
    (φ ψ : (RationalFunctions Y)ˣ)
    (hφ : A.pieceToRationalFunctions W 1 a ⟨ZY, hZW⟩ = (φ : RationalFunctions Y) ZY)
    (hψ : A.pieceToRationalFunctions W 1 b ⟨ZY, hZW⟩ = (ψ : RationalFunctions Y) ZY)
    (p q : Γ(Y, W))
    (hpq : Y.presheaf.germ W _ hZW p * (ψ : RationalFunctions Y) ZY =
      (φ : RationalFunctions Y) ZY * Y.presheaf.germ W _ hZW q) :
    Away.mk (A.situation.sectionRingGrading W) (f := DirectSum.of _ 1 b) (d := 1)
        (show DirectSum.of _ 1 b ∈ A.situation.sectionRingGrading W 1 from ⟨b, rfl⟩) 1
        (DirectSum.of _ 1 a) (by rw [smul_eq_mul, mul_one]; exact ⟨a, rfl⟩) *
      fromZeroRingHom _ _ (Situation.sectionRingZeroMap A.situation W q) =
      fromZeroRingHom _ _ (Situation.sectionRingZeroMap A.situation W p) := by
  have hfb : DirectSum.of _ 1 b ∈ A.situation.sectionRingGrading W 1 := ⟨b, rfl⟩
  have hη : genericPoint Y ∈ W :=
    ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr ⟨_, Set.mem_univ _, hZW⟩
  let i : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W} := ⟨ZY, hZW⟩
  have hb0' : A.sectionRingToFunctionField i (DirectSum.of _ 1 b) ≠ 0 := fun h =>
    hb0 ((A.sectionRingToFunctionField_of_eq_zero_iff i 1 b).mp h)
  have hfa' : DirectSum.of _ 1 a ∈ A.situation.sectionRingGrading W (1 • 1) := by
    rw [smul_eq_mul, mul_one]
    exact ⟨a, rfl⟩
  have hθab : A.awayToFunctionField i hb0'
        (Away.mk (A.situation.sectionRingGrading W) hfb 1 (DirectSum.of _ 1 a) hfa') *
      algebraMap _ Y.functionField ((ψ : RationalFunctions Y) ZY) =
      algebraMap _ Y.functionField ((φ : RationalFunctions Y) ZY) := by
    have h := A.awayToFunctionField_mk_mul i hfb hb0' 1 (DirectSum.of _ 1 a) hfa'
    rwa [pow_one, sectionRingToFunctionField_of, sectionRingToFunctionField_of, hφ, hψ] at h
  have halg : ∀ r : Γ(Y, W), algebraMap (Y.presheaf.stalk (componentGenericPoint Y ZY))
      Y.functionField (Y.presheaf.germ W _ hZW r) = Y.presheaf.germ W (genericPoint Y) hη r := by
    intro r
    change (Y.presheaf.stalkSpecializes _).hom ((Y.presheaf.germ W _ hZW).hom r) = _
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  have hψu : IsUnit (algebraMap _ Y.functionField ((ψ : RationalFunctions Y) ZY)) :=
    (ψ.isUnit.map (Pi.evalRingHom _ ZY)).map _
  have hpq' := congrArg (algebraMap _ Y.functionField) hpq
  rw [map_mul, map_mul, halg, halg] at hpq'
  apply A.awayToFunctionField_injective i hfb hb0'
  rw [map_mul, A.awayToFunctionField_fromZeroRingHom i hb0' q hη,
    A.awayToFunctionField_fromZeroRingHom i hb0' p hη]
  apply hψu.mul_left_injective
  linear_combination Y.presheaf.germ W (genericPoint Y) hη q * hθab - hpq'

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
private theorem eq_of_mul_isUnit {R : Type*} [CommRing R] {e x y u v : R} (hu : IsUnit u)
    (h1 : e * u = v) (h2 : v * x = y * u) : e * x = y := by
  apply hu.mul_left_injective
  linear_combination x * h1 + h2

/-- **The transition identity on the chart ring.** Let `G : Spec S_{(b)} ⟶ Y` be the morphism
induced by `Γ(Y, W) → S_{(b)}`, `r ↦ r / 1`, and `p` a point over the generic point of `Y`. For
sections `a, b` of degree one over `W`, `b ≠ 0`, equal at the generic point to units `φ, ψ`
of `K(Y)`, the germ of `a / b` at `p` times the image of `ψ` is the image of `φ`. -/
theorem germ_away_mk_mul_eq {W : Y.Opens} (hW : IsAffineOpen W)
    (a b : A.situation.sectionPieces W 1)
    (hb0 : b ≠ 0) (φ ψ : (RationalFunctions Y)ˣ) (ZY : irreducibleComponents Y)
    (hZW : componentGenericPoint Y ZY ∈ W)
    (hφ : A.pieceToRationalFunctions W 1 a ⟨ZY, hZW⟩ = (φ : RationalFunctions Y) ZY)
    (hψ : A.pieceToRationalFunctions W 1 b ⟨ZY, hZW⟩ = (ψ : RationalFunctions Y) ZY)
    (G : Spec (.of (Away (A.situation.sectionRingGrading W) (DirectSum.of _ 1 b))) ⟶ Y)
    (hG : G = Spec.map (Situation.sectionRingZeroMap A.situation W ≫
        CommRingCat.ofHom (fromZeroRingHom _ _)) ≫ hW.fromSpec)
    (p : Spec (.of (Away (A.situation.sectionRingGrading W) (DirectSum.of _ 1 b))))
    (hp : G p = componentGenericPoint Y ZY) :
    (Spec _).presheaf.germ ⊤ p trivial ((Scheme.ΓSpecIso _).inv.hom
        (Away.mk (A.situation.sectionRingGrading W) (f := DirectSum.of _ 1 b) (d := 1)
          (show DirectSum.of _ 1 b ∈ A.situation.sectionRingGrading W 1 from ⟨b, rfl⟩) 1
          (DirectSum.of _ 1 a) (by rw [smul_eq_mul, mul_one]; exact ⟨a, rfl⟩))) *
        (Y.presheaf.stalkSpecializes (specializes_of_eq hp) ≫ G.stalkMap p).hom
          ((ψ : RationalFunctions Y) ZY) =
      (Y.presheaf.stalkSpecializes (specializes_of_eq hp) ≫ G.stalkMap p).hom
        ((φ : RationalFunctions Y) ZY) := by
  have h0 := exists_germ_eq_mul_germ_of_isAffineOpen hW hZW
  have h1 := h0 (((φ * ψ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) ZY)
  obtain ⟨p', q, hqu, hpq⟩ := h1
  rw [Units.val_mul, Pi.mul_apply] at hpq
  have hinv : (ψ : RationalFunctions Y) ZY *
      ((ψ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) ZY = 1 := by
    rw [← Pi.mul_apply, Units.mul_inv, Pi.one_apply]
  have hpq2 : Y.presheaf.germ W _ hZW p' * (ψ : RationalFunctions Y) ZY =
      (φ : RationalFunctions Y) ZY * Y.presheaf.germ W _ hZW q := by
    rw [hpq]
    linear_combination ((φ : RationalFunctions Y) ZY * Y.presheaf.germ W _ hZW q) * hinv
  have hAway := A.away_mk_mul_fromZeroRingHom_eq ZY hZW a b hb0 φ ψ hφ hψ p' q hpq2
  have hpW : G p ∈ W := hp ▸ hZW
  have hFR : ∀ r : Γ(Y, W),
      (Y.presheaf.stalkSpecializes (specializes_of_eq hp) ≫ G.stalkMap p).hom
        (Y.presheaf.germ W _ hZW r) =
      (Spec _).presheaf.germ ⊤ p trivial ((Scheme.ΓSpecIso _).inv.hom
        (fromZeroRingHom _ _ (Situation.sectionRingZeroMap A.situation W r))) := by
    intro r
    have h1 : (Y.presheaf.stalkSpecializes (specializes_of_eq hp)).hom
        (Y.presheaf.germ W _ hZW r) = Y.presheaf.germ W (G p) hpW r :=
      TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    have h2 := stalkMap_germ_eq_of_eq_SpecMap_fromSpec hW
      (Situation.sectionRingZeroMap A.situation W ≫ CommRingCat.ofHom (fromZeroRingHom _ _))
      G hG p hpW r
    exact (congrArg (G.stalkMap p).hom h1).trans h2
  have hu := Eq.mp (congrArg IsUnit (hFR q))
    (hqu.map (Y.presheaf.stalkSpecializes (specializes_of_eq hp) ≫ G.stalkMap p).hom)
  have e1 := congrArg (Y.presheaf.stalkSpecializes (specializes_of_eq hp) ≫ G.stalkMap p).hom hpq2
  have h2 := (congrArg (· * (Y.presheaf.stalkSpecializes (specializes_of_eq hp) ≫
      G.stalkMap p).hom ((ψ : RationalFunctions Y) ZY)) (hFR p')).symm.trans
    ((map_mul (Y.presheaf.stalkSpecializes (specializes_of_eq hp) ≫
      G.stalkMap p).hom _ _).symm.trans (e1.trans ((map_mul
        (Y.presheaf.stalkSpecializes (specializes_of_eq hp) ≫ G.stalkMap p).hom _ _).trans
      (congrArg ((Y.presheaf.stalkSpecializes (specializes_of_eq hp) ≫ G.stalkMap p).hom
        ((φ : RationalFunctions Y) ZY) * ·) (hFR q)))))
  have h1 := (map_mul (((Spec _).presheaf.germ ⊤ p trivial).hom.comp
      (Scheme.ΓSpecIso _).inv.hom) _ _).symm.trans
    (congrArg (((Spec _).presheaf.germ ⊤ p trivial).hom.comp (Scheme.ΓSpecIso _).inv.hom) hAway)
  exact eq_of_mul_isUnit hu h1 h2

set_option backward.isDefEq.respectTransparency false in
/-- **The transition identity at a point.** On the chart `Proj ⨁_n 𝒪_Y(nD)(W)` over an affine open
`W`, let `a, b` be nonzero sections of degree one, equal in `𝒦_Y(W)` to units `φ, ψ` of `K(Y)`.
At every point `x` of `D₊(b)` lying over the generic point of `Y`, the germ of the section
`a / b`, multiplied by the image of `ψ`, is the image of `φ`. -/
theorem germ_fracSection_mul_eq {W : Y.Opens} (hW : IsAffineOpen W)
    (j : AlgebraicGeometry.Proj (A.situation.sectionRingGrading W) ⟶ A.model)
    (hjo : IsOpenImmersion j) (hj : j = A.situation.relativeProjChart ⟨W, hW⟩)
    (a b : A.situation.sectionPieces W 1) (hb0 : b ≠ 0) (φ ψ : (RationalFunctions Y)ˣ)
    (hφ : ∀ i : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W},
      A.pieceToRationalFunctions W 1 a i = (φ : RationalFunctions Y) i.1)
    (hψ : ∀ i : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W},
      A.pieceToRationalFunctions W 1 b i = (ψ : RationalFunctions Y) i.1)
    (x : A.model)
    (hxU : x ∈ j ''ᵁ ProjectiveSpectrum.basicOpen _ (DirectSum.of _ 1 b))
    (ZY : irreducibleComponents Y) (hx : A.toBase x = componentGenericPoint Y ZY) :
    A.model.presheaf.germ _ x hxU (((j).appIso
          (ProjectiveSpectrum.basicOpen _ (DirectSum.of _ 1 b))).inv
          (fracSection (A.situation.sectionRingGrading W) (d := 1)
            (show DirectSum.of _ 1 a ∈ A.situation.sectionRingGrading W 1 from ⟨a, rfl⟩)
            (show DirectSum.of _ 1 b ∈ A.situation.sectionRingGrading W 1 from ⟨b, rfl⟩)
            le_rfl)) *
        (Y.presheaf.stalkSpecializes (specializes_of_eq hx) ≫ A.toBase.stalkMap x).hom
          ((ψ : RationalFunctions Y) ZY) =
      (Y.presheaf.stalkSpecializes (specializes_of_eq hx) ≫ A.toBase.stalkMap x).hom
        ((φ : RationalFunctions Y) ZY) := by
  classical
  have hfa : DirectSum.of _ 1 a ∈ A.situation.sectionRingGrading W 1 := ⟨a, rfl⟩
  have hfb : DirectSum.of _ 1 b ∈ A.situation.sectionRingGrading W 1 := ⟨b, rfl⟩
  set c := Proj.awayι _ _ hfb one_pos ≫ j with hc
  have hcg : c ≫ A.toBase =
      Spec.map (Situation.sectionRingZeroMap A.situation W ≫
        CommRingCat.ofHom (fromZeroRingHom _ _)) ≫ hW.fromSpec := by
    rw [hc, Category.assoc, hj, A.awayι_relativeProjChart_toBase hW hfb, Spec.map_comp,
      Category.assoc]
  obtain ⟨y, hy, rfl⟩ := hxU
  have hy' : y ∈ (Proj.awayι _ _ hfb one_pos).opensRange := by
    rw [Proj.opensRange_awayι]; exact hy
  obtain ⟨p, rfl⟩ := hy'
  have hZW : componentGenericPoint Y ZY ∈ W := by
    rw [← hx]
    change (c ≫ A.toBase) p ∈ W
    rw [hcg]
    exact hW.range_fromSpec.subset ⟨_, rfl⟩
  have hfa' : DirectSum.of _ 1 a ∈ A.situation.sectionRingGrading W (1 • 1) := by
    rw [smul_eq_mul, mul_one]; exact hfa
  have hS := stalkMap_awayι_comp_germ_appIso_inv_fracSection (A.situation.sectionRingGrading W) j
    hfa hfb hfa' p hy ⟨_, hy, rfl⟩
  exact mul_stalkMap_eq_of_stalkMap_comp c A.toBase p hx _ _ hS
    (A.germ_away_mk_mul_eq hW a b hb0 φ ψ ZY hZW (hφ ⟨ZY, hZW⟩) (hψ ⟨ZY, hZW⟩)
      (c ≫ A.toBase) hcg p hx)

/-- **The transition identity.** On the chart `Proj ⨁_n 𝒪_Y(nD)(W)` over an affine open `W`,
let `a, b` be sections of degree one, `b ≠ 0`, equal in `𝒦_Y(W)` to units `φ, ψ` of `K(Y)`. Then
on `j(D₊(b))` the section `a / b` of the chart, read in `𝒦_Z`, satisfies
`(a / b) · g^*ψ = g^*φ`, where `g^*φ` is the inverse of the pull-back of `φ⁻¹`. -/
theorem algebraMap_fracSection_mul_pullbackRationalFunction_eq [CompactSpace Y]
    [IsIntegral A.model] [IsDominant A.toBase] {W : Y.Opens} (hW : IsAffineOpen W)
    (j : AlgebraicGeometry.Proj (A.situation.sectionRingGrading W) ⟶ A.model)
    (hjo : IsOpenImmersion j) (hj : j = A.situation.relativeProjChart ⟨W, hW⟩)
    (a b : A.situation.sectionPieces W 1) (hb0 : b ≠ 0) (φ ψ : (RationalFunctions Y)ˣ)
    (hφ : ∀ i : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W},
      A.pieceToRationalFunctions W 1 a i = (φ : RationalFunctions Y) i.1)
    (hψ : ∀ i : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W},
      A.pieceToRationalFunctions W 1 b i = (ψ : RationalFunctions Y) i.1) :
    algebraMap Γ(A.model, j ''ᵁ
        ProjectiveSpectrum.basicOpen _ (DirectSum.of _ 1 b)) _
      ((j.appIso
        (ProjectiveSpectrum.basicOpen _ (DirectSum.of _ 1 b))).inv
        (fracSection (A.situation.sectionRingGrading W) (d := 1)
          (show DirectSum.of _ 1 a ∈ A.situation.sectionRingGrading W 1 from ⟨a, rfl⟩)
          (show DirectSum.of _ 1 b ∈ A.situation.sectionRingGrading W 1 from ⟨b, rfl⟩) le_rfl)) *
      rationalFunctionsRestrict (j ''ᵁ
        ProjectiveSpectrum.basicOpen _ (DirectSum.of _ 1 b))
        (((pullbackRationalFunction A.toBase ψ⁻¹ fun Z =>
        MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant A.toBase _ Z)⁻¹ :
          (RationalFunctions A.model)ˣ) : RationalFunctions A.model) =
    rationalFunctionsRestrict (j ''ᵁ
        ProjectiveSpectrum.basicOpen _ (DirectSum.of _ 1 b))
        (((pullbackRationalFunction A.toBase φ⁻¹ fun Z =>
        MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant A.toBase _ Z)⁻¹ :
          (RationalFunctions A.model)ˣ) : RationalFunctions A.model) := by
  funext i
  let ZY : irreducibleComponents Y :=
    ⟨Set.univ, by
      rw [irreducibleComponents_eq_singleton]
      exact Set.mem_singleton _⟩
  have hx := MMP.Fourfold.map_componentGenericPoint A.toBase i.1 ZY
  have h := A.germ_fracSection_mul_eq hW j hjo hj a b hb0 φ ψ hφ hψ _ i.2 ZY hx
  have e1 := coe_inv_pullbackRationalFunction_inv_apply A.toBase ψ
    (fun Z => MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant A.toBase _ Z) i.1 ZY
  have e2 := coe_inv_pullbackRationalFunction_inv_apply A.toBase φ
    (fun Z => MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant A.toBase _ Z) i.1 ZY
  exact (congrArg (_ * ·) e1).trans (h.trans e2.symm)

end MMP.Fourfold.DivisorialSectionAlgebra
