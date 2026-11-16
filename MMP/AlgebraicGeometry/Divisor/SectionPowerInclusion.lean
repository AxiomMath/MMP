module

public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictStalkDepth
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationGlobal

/-!
# Multiplication by a power of a section as an inclusion of divisorial sheaves

Let `X` be an integral, locally Noetherian, normal, quasi-compact scheme, `L` an invertible
`𝒪_X`-module and `s` a nonzero global section of `L^{⊗ m}`. Writing the powers of `L` as
divisorial sheaves, multiplication by `s^k` from `L^{⊗ -(r + mk)}` to `L^{⊗ -r}` becomes the
inclusion `𝒪_X(-rM - kD) ⊆ 𝒪_X(-rM)`, where `𝒪_X(M) ≅ L` and `D` is the divisor of zeros of `s`.

## Main results

* `MMP.LcBpf.exists_iso_comp_divisorialSheafInclusion`: a nonzero morphism of divisorial
  sheaves `𝒪_X(A) ⟶ 𝒪_X(B)` is an isomorphism `𝒪_X(A) ≅ 𝒪_X(C)` followed by the inclusion
  `𝒪_X(C) ⊆ 𝒪_X(B)`, for a divisor `C ≤ B`.
* `MMP.LcBpf.exists_iso_chain_eq_divisorialSheafInclusion_of_iso`: multiplication by `s^k` is,
  up to isomorphism, the inclusion of divisorial sheaves `𝒪_X(A - kD) ⊆ 𝒪_X(A)`.

## References

* [J. Kollár and S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  proof of Theorem 2.47
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MMP.Mori

universe u

namespace MMP.LcBpf

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- If multiplication by a unit `w` of `K(X)` maps `𝒪_X(A)` into `𝒪_X(B)`, then
`A - div w ≤ B`. -/
theorem sub_principalDivisor_le_of_mul [IrreducibleSpace X] [CompactSpace X] {A B : Divisor X}
    (β : A.divisorialSheaf ⟶ B.divisorialSheaf) (w : (RationalFunctions X)ˣ)
    (hβ : ∀ (V : X.Opens) (s : Γ(A.divisorialSheaf, V))
      (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ V}),
      Divisor.secVal B V (β.app V s) Z = (w : RationalFunctions X) Z.1 *
        Divisor.secVal A V s Z) :
    A - principalDivisor w ≤ B := by
  intro E
  obtain ⟨U, hE, t, ht, hts⟩ := MMP.Flips.exists_divisorialSection_ord_eq A E
  let σ : Γ(A.divisorialSheaf, U) := ⟨fun Z => (t : RationalFunctions X) Z.1, hts⟩
  have hmem := E.componentGenericPoint_mem_of_nonempty hE
  have key : E.OrdGE (-B.coeff E) (Divisor.secVal B U (β.app U σ) ⟨E.component, hmem⟩) :=
    (β.app U σ : B.divisorialSubmodule U).2 E hE
  rw [hβ U σ ⟨E.component, hmem⟩] at key
  rcases key with h0 | h
  · exact absurd h0 (((Pi.isUnit_iff.mp w.isUnit) E.component).mul
      ((Pi.isUnit_iff.mp t.isUnit) E.component)).ne_zero
  · rw [map_mul, E.valuation_component, E.valuation_component, ← WithZero.exp_add,
      WithZero.exp_le_exp, ht] at h
    change A E - (principalDivisor w) E ≤ B E
    rw [← DivisorWithCoeffs.coeff_apply (principalDivisor w), coeff_principalDivisor]
    change -B E ≤ E.ord w + -A E at h
    linarith

/-- **A nonzero morphism of divisorial sheaves is an isomorphism onto a smaller divisorial
sheaf.** On an integral, locally Noetherian, normal, quasi-compact scheme, a nonzero morphism
`α : 𝒪_X(A) ⟶ 𝒪_X(B)` is multiplication by a unit `w` of `K(X)`; it is the isomorphism
`𝒪_X(A) ≅ 𝒪_X(A - div w)` followed by the inclusion `𝒪_X(A - div w) ⊆ 𝒪_X(B)`. -/
theorem exists_iso_comp_divisorialSheafInclusion [IsIntegral X] [CompactSpace X]
    {A B : Divisor X} (α : A.divisorialSheaf ⟶ B.divisorialSheaf) (hα : α ≠ 0) :
    ∃ (C : Divisor X) (hC : C ≤ B) (e : A.divisorialSheaf ≅ C.divisorialSheaf),
      α = e.hom ≫ Divisor.divisorialSheafInclusion hC := by
  obtain ⟨u, hu⟩ := MMP.Flips.exists_eq_mul_of_divisorialSheaf_hom α
  have hu0 : u ≠ 0 := by
    rintro rfl
    refine hα (Divisor.divisorialSheaf_hom_ext fun V φ => funext fun Z => ?_)
    have := hu V φ Z
    rw [Pi.zero_apply, zero_mul] at this
    exact this
  have hunit : IsUnit u := by
    have e := rationalFunctionsEquivFunctionField X
    have h : e u ≠ 0 := (map_ne_zero_iff e e.injective).mpr hu0
    simpa using (isUnit_iff_ne_zero.mpr h).map e.symm
  set w := hunit.unit
  refine ⟨A - principalDivisor w, sub_principalDivisor_le_of_mul α w hu,
    Divisor.divisorialSheafMulIso w fun E => ?_, ?_⟩
  · rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor]
    ring
  · exact Divisor.divisorialSheaf_hom_ext fun V φ => funext (hu V φ)

/-! ### Images of stalk maps -/

section StalkRange

open Stacks.EnriquesSeveriZariski

variable {X : Scheme.{u}}

/-- The image of the stalk map of `φ : A ⟶ B` at `y` is `I · B_y`. -/
def StalkRange {A B : X.Modules} (φ : A ⟶ B) (y : X) (I : Ideal (X.presheaf.stalk y)) : Prop :=
  LinearMap.range (stalkLinearMap A B φ y) =
    I • (⊤ : Submodule (X.presheaf.stalk y) (B.presheaf.stalk y))

variable {A B C : X.Modules} {y : X}

/-- If the stalk map of `φ` at `y` is bijective, its image is `⊤ · B_y`. -/
theorem StalkRange.of_bijective {φ : A ⟶ B} (h : Function.Bijective (stalkLinearMap A B φ y)) :
    StalkRange φ y ⊤ := by
  rw [StalkRange, Submodule.top_smul, LinearMap.range_eq_top]
  exact h.2

/-- The stalk image at `y` of a morphism with a two-sided inverse is `⊤ · B_y`. -/
theorem StalkRange.of_inverse (u : A ⟶ B) (v : B ⟶ A) (h1 : u ≫ v = 𝟙 A) (h2 : v ≫ u = 𝟙 B) :
    StalkRange u y ⊤ :=
  StalkRange.of_bijective (bijective_stalkLinearMap_of_inverse u v h1 h2 y)

/-- The stalk image at `y` of an isomorphism is `⊤ · B_y`. -/
theorem StalkRange.of_iso (e : A ≅ B) : StalkRange e.hom y ⊤ :=
  StalkRange.of_inverse e.hom e.inv e.hom_inv_id e.inv_hom_id

/-- If the stalk images of `u` and `v` at `y` are `I · B_y` and `J · C_y`, the stalk image of
`u ≫ v` is `(I * J) · C_y`. -/
theorem StalkRange.comp {u : A ⟶ B} {v : B ⟶ C} {I J : Ideal (X.presheaf.stalk y)}
    (hu : StalkRange u y I) (hv : StalkRange v y J) : StalkRange (u ≫ v) y (I * J) := by
  unfold StalkRange at *
  have e : stalkLinearMap A C (u ≫ v) y =
      (stalkLinearMap B C v y).comp (stalkLinearMap A B u y) :=
    LinearMap.ext fun z => Scheme.Modules.stalkLinearMap_comp u v y z
  rw [e, LinearMap.range_comp, hu, Submodule.map_smul'', Submodule.map_top, hv,
    Submodule.mul_smul]

/-- If the range of `g : N →ₗ[R] P` is `I • P`, the range of `M ⊗ g` is `I • (M ⊗ P)`. -/
theorem range_lTensor_eq_smul_top {R : Type*} [CommRing R] {M N P : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] (I : Ideal R)
    (g : N →ₗ[R] P) (hg : LinearMap.range g = I • (⊤ : Submodule R P)) :
    LinearMap.range (LinearMap.lTensor M g) = I • (⊤ : Submodule R (TensorProduct R M P)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    exact lTensor_mem_ideal_smul_top I g (fun b => hg ▸ ⟨b, rfl⟩) z
  · refine Submodule.smul_le.2 fun a ha t _ => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m p =>
      rw [← TensorProduct.tmul_smul]
      have hp : a • p ∈ LinearMap.range g :=
        hg ▸ Submodule.smul_mem_smul ha Submodule.mem_top
      obtain ⟨n, hn⟩ := hp
      exact ⟨m ⊗ₜ n, by rw [LinearMap.lTensor_tmul, hn]⟩
    | add c d hc hd =>
      rw [smul_add]
      exact add_mem (hc trivial) (hd trivial)

/-- If the stalk image of `g` at `y` is `I · B_y`, the stalk image of `F ⊗ g` at `y` is
`I · (F ⊗ B)_y`. -/
theorem StalkRange.tensorLeftMap (F : X.Modules) {g : A ⟶ B} {I : Ideal (X.presheaf.stalk y)}
    (hg : StalkRange g y I) : StalkRange (Scheme.Modules.tensorLeftMap F g) y I := by
  unfold StalkRange at *
  have e : stalkLinearMap _ _ (Scheme.Modules.tensorLeftMap F g) y =
      (tensorStalkEquiv F B y).symm.toLinearMap ∘ₗ
        (LinearMap.lTensor (F.presheaf.stalk y) (stalkLinearMap A B g y)) ∘ₗ
          (tensorStalkEquiv F A y).toLinearMap := by
    refine LinearMap.ext fun z => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [← tensorStalkEquiv_tensorLeftMap, LinearEquiv.symm_apply_apply]
  rw [e, LinearMap.range_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (tensorStalkEquiv F A y).surjective, Submodule.map_top,
    range_lTensor_eq_smul_top I _ hg, Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (tensorStalkEquiv F B y).symm.surjective]

/-- The stalk image at `y` of the morphism `𝒪_X ⟶ M` given by a global section `σ` of an
invertible module `M` is `I · M_y` for some ideal `I` of `𝒪_{X,y}`. -/
theorem exists_stalkRange_sectionHom (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]
    (σ : Γ(M, ⊤)) (y : X) : ∃ I, StalkRange (sectionHom M σ) y I := by
  obtain ⟨V, hyV, b, hb⟩ := Stacks.InvertibleStalk.exists_germ_isStalkBasis M y
  generalize (ConcreteCategory.hom (M.presheaf.germ V y hyV)) b = bb at hb
  refine ⟨Ideal.span {hb.coord ((M.presheaf.Γgerm y).hom σ)}, le_antisymm ?_ ?_⟩
  · rintro _ ⟨z, rfl⟩
    rw [stalkLinearMap_sectionHom]
    generalize (Stacks.Ample.unitStalkEquiv X y) z = r
    generalize hg : (M.presheaf.Γgerm y).hom σ = g
    have e : r • g = hb.coord g • (r • bb) := by
      conv_lhs => rw [← hb.smul_coord g]
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  · refine Submodule.smul_le.2 fun a ha t _ => ?_
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨(Stacks.Ample.unitStalkEquiv X y).symm (d * hb.coord t), ?_⟩
    rw [stalkLinearMap_sectionHom, (Stacks.Ample.unitStalkEquiv X y).apply_symm_apply]
    generalize hg : (M.presheaf.Γgerm y).hom σ = g
    conv_lhs => rw [← hb.smul_coord g]
    conv_rhs => rw [← hb.smul_coord t]
    rw [smul_smul, smul_smul]
    congr 1
    ring

/-- If the stalk `B_y` has a basis, the ideal `I` with stalk image `I · B_y` is unique. -/
theorem StalkRange.unique_of_isStalkBasis {φ : A ⟶ B} {b : B.presheaf.stalk y}
    (hb : Stacks.Divisors.IsStalkBasis B y b) {I J : Ideal (X.presheaf.stalk y)}
    (hI : StalkRange φ y I) (hJ : StalkRange φ y J) : I = J := by
  have key : ∀ K : Ideal (X.presheaf.stalk y),
      K • (⊤ : Submodule (X.presheaf.stalk y) (B.presheaf.stalk y)) =
        Submodule.map hb.linearEquiv.toLinearMap K := by
    intro K
    have h1 : Submodule.map hb.linearEquiv.toLinearMap
        (K • (⊤ : Submodule (X.presheaf.stalk y) (X.presheaf.stalk y))) =
        K • (⊤ : Submodule (X.presheaf.stalk y) (B.presheaf.stalk y)) := by
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr hb.linearEquiv.surjective]
    rw [← h1, Ideal.smul_eq_mul, Ideal.mul_top]
  have h := hI.symm.trans hJ
  rw [key, key] at h
  exact Submodule.map_injective_of_injective hb.linearEquiv.injective h

/-- The ideal `I` with stalk image `I · B_y` is unique when `B` is invertible. -/
theorem StalkRange.unique {φ : A ⟶ B} [Stacks.Ample.IsInvertibleModule X B]
    {I J : Ideal (X.presheaf.stalk y)} (hI : StalkRange φ y I) (hJ : StalkRange φ y J) :
    I = J := by
  obtain ⟨_, _, _, hb⟩ := Stacks.InvertibleStalk.exists_germ_isStalkBasis B y
  exact StalkRange.unique_of_isStalkBasis hb hI hJ

variable (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- Multiplication by `σ` on the twist by `L^{⊗ n}` has the same stalk ideal at `y` as `σ`. -/
theorem StalkRange.mulSectionPow {e : ℕ} {σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤)}
    {I : Ideal (X.presheaf.stalk y)} (hσ : StalkRange (sectionHom _ σ) y I) (n : ℤ) :
    StalkRange (Stacks.EnriquesSeveriZariski.mulSectionPow L σ n) y I := by
  have h : StalkRange (Stacks.EnriquesSeveriZariski.mulSectionPow L σ n) y (⊤ * (I * ⊤)) := by
    unfold Stacks.EnriquesSeveriZariski.mulSectionPow
    exact (StalkRange.of_inverse _ _ (Iso.inv_hom_id _) (Iso.hom_inv_id _)).comp
      ((hσ.tensorLeftMap _).comp (StalkRange.of_inverse _ _ (Iso.hom_inv_id _) (Iso.inv_hom_id _)))
  rwa [Ideal.top_mul, Ideal.mul_top] at h

/-- Multiplication by `σ` from the twist of `F` by `L^{⊗ (n - e)}` to the twist by `L^{⊗ n}` has
the same stalk ideal at `y` as `σ`. -/
theorem StalkRange.mulSectionDown {e : ℕ} {σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤)}
    {I : Ideal (X.presheaf.stalk y)} (hσ : StalkRange (sectionHom _ σ) y I) (F : X.Modules)
    (n : ℤ) : StalkRange (Stacks.EnriquesSeveriZariski.mulSectionDown L σ F n) y I := by
  have h : StalkRange (Stacks.EnriquesSeveriZariski.mulSectionDown L σ F n) y (I * ⊤) := by
    unfold Stacks.EnriquesSeveriZariski.mulSectionDown Stacks.EnriquesSeveriZariski.mulSection
    exact ((hσ.mulSectionPow L (n - e)).tensorLeftMap F).comp
      (StalkRange.of_inverse _ (eqToHom (congrArg (twist L F) (by ring))) (by simp) (by simp))
  rwa [Ideal.mul_top] at h

/-- The composite of `j` multiplications by `σ` has stalk ideal `I ^ j` at `y`, where `I` is the
stalk ideal of `σ` at `y`. -/
theorem StalkRange.chain {e : ℕ} {σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤)}
    {I : Ideal (X.presheaf.stalk y)} (hσ : StalkRange (sectionHom _ σ) y I) (F : X.Modules)
    (n : ℤ) (j : ℕ) : StalkRange (Stacks.EnriquesSeveriZariski.chain L σ F n j) y (I ^ j) := by
  induction j with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, chain_zero]
    exact StalkRange.of_inverse _ _ (Category.id_comp _) (Category.id_comp _)
  | succ j ih =>
    rw [chain_succ, pow_succ']
    exact (hσ.mulSectionDown L F _).comp ih

end StalkRange

/-! ### Stalks of divisorial sheaves -/

section DivisorialStalk

open Stacks.Divisors

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- An irreducible space has at most one irreducible component. -/
theorem subsingleton_irreducibleComponents_of_irreducibleSpace [IrreducibleSpace X] :
    Subsingleton (irreducibleComponents X) :=
  (irreducibleComponents_eq_singleton (X := X) ▸ Set.subsingleton_singleton).coe_sort

/-- Two sections of `𝒪_X(B)` with the same germ at `y` have the same value at the generic point
of every irreducible component specializing to `y`. -/
theorem secVal_eq_of_germ_eq {B : Divisor X} {V W : X.Opens} {y : X} (hyV : y ∈ V) (hyW : y ∈ W)
    (φ : Γ(B.divisorialSheaf, V)) (ψ : Γ(B.divisorialSheaf, W))
    (h : B.divisorialSheaf.presheaf.germ V y hyV φ = B.divisorialSheaf.presheaf.germ W y hyW ψ)
    (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ⤳ y) :
    Divisor.secVal B V φ ⟨Z, hZ.mem_open V.isOpen hyV⟩ =
      Divisor.secVal B W ψ ⟨Z, hZ.mem_open W.isOpen hyW⟩ := by
  obtain ⟨W', hyW', i₁, i₂, h'⟩ := TopCat.Presheaf.germ_eq _ y hyV hyW φ ψ h
  exact congrArg (fun χ : Γ(B.divisorialSheaf, W') =>
    Divisor.secVal B W' χ ⟨Z, hZ.mem_open W'.isOpen hyW'⟩) h'

/-- The value in `K(X)` of `g • φ` is the germ of `g` times the value of `φ`. -/
theorem secVal_smul {B : Divisor X} {W : X.Opens} (g : Γ(X, W)) (φ : Γ(B.divisorialSheaf, W))
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W}) :
    Divisor.secVal B W (g • φ) Z = X.presheaf.germ W _ Z.2 g * Divisor.secVal B W φ Z := rfl

/-- The value in `K(X)` of the restriction of a section of `𝒪_X(B)` is the value of the section. -/
theorem secVal_map {B : Divisor X} {V W : X.Opens} (i : W ⟶ V) (φ : Γ(B.divisorialSheaf, V))
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W}) :
    Divisor.secVal B W (B.divisorialSheaf.presheaf.map i.op φ) Z =
      Divisor.secVal B V φ ⟨Z.1, i.le Z.2⟩ := rfl

/-- The value in `K(X)` of the zero section of `𝒪_X(B)` is zero. -/
@[simp]
theorem secVal_zero {B : Divisor X} {W : X.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W}) :
    Divisor.secVal B W 0 Z = 0 := rfl

/-- Two sections of `𝒪_X(B)` over `W` agree when they agree at the generic point of `X`. -/
theorem divisorialSheaf_section_ext [IrreducibleSpace X] {B : Divisor X} {W : X.Opens}
    {φ ψ : Γ(B.divisorialSheaf, W)}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W})
    (h : Divisor.secVal B W φ Z = Divisor.secVal B W ψ Z) : φ = ψ := by
  have := subsingleton_irreducibleComponents_of_irreducibleSpace (X := X)
  refine Subtype.ext (funext fun Z' => ?_)
  obtain rfl : Z' = Z := Subtype.ext (Subsingleton.elim _ _)
  exact h

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The image in `K(X)` of the germ at `y` of a function `g` is the germ of `g` at the generic
point of an irreducible component through `y`. -/
theorem stalkToRationalFunctions_germ {y : X} {Z : irreducibleComponents X} (hyZ : y ∈ Z.1)
    {W : X.Opens} (hyW : y ∈ W) (g : Γ(X, W)) :
    (stalkToRationalFunctions X hyZ).hom (X.presheaf.germ W y hyW g) =
      X.presheaf.germ W _
        (((isGenericPoint_componentGenericPoint X Z).specializes hyZ).mem_open W.isOpen hyW) g :=
  TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hyW _ g

/-- On an integral scheme, multiplication by the germ at `y` of a section `t` of `𝒪_X(B)` whose
value in `K(X)` is a unit is injective on `𝒪_{X,y}`. -/
theorem injective_smul_germ_of_isUnit_secVal [IsIntegral X] {B : Divisor X} {U : X.Opens}
    (t : Γ(B.divisorialSheaf, U)) {y : X} (hy : y ∈ U) {Z : irreducibleComponents X}
    (hyZ : y ∈ Z.1)
    (ht : IsUnit (Divisor.secVal B U t ⟨Z,
      ((isGenericPoint_componentGenericPoint X Z).specializes hyZ).mem_open U.isOpen hy⟩)) :
    Function.Injective fun r : X.presheaf.stalk y =>
      r • B.divisorialSheaf.presheaf.germ U y hy t := by
  have hZ := (isGenericPoint_componentGenericPoint X Z).specializes hyZ
  intro r₁ r₂ h
  obtain ⟨W, hyW, g, hg⟩ := X.presheaf.exists_germ_eq (r₁ - r₂)
  have h0 : (r₁ - r₂) • B.divisorialSheaf.presheaf.germ U y hy t = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr h
  let W₀ := W ⊓ U
  have hyW₀ : y ∈ W₀ := ⟨hyW, hy⟩
  let g₀ : Γ(X, W₀) := X.presheaf.map (homOfLE inf_le_left).op g
  let t₀ : Γ(B.divisorialSheaf, W₀) := B.divisorialSheaf.presheaf.map (homOfLE inf_le_right).op t
  have hgerm : B.divisorialSheaf.presheaf.germ W₀ y hyW₀ (g₀ • t₀) =
      B.divisorialSheaf.presheaf.germ W₀ y hyW₀ 0 := by
    rw [Stacks.ModuleStalk.germ_smul, map_zero]
    have e1 : X.presheaf.germ W₀ y hyW₀ g₀ = r₁ - r₂ := by
      rw [← hg]
      exact X.presheaf.germ_res_apply _ y hyW₀ g
    have e2 : B.divisorialSheaf.presheaf.germ W₀ y hyW₀ t₀ =
        B.divisorialSheaf.presheaf.germ U y hy t :=
      B.divisorialSheaf.presheaf.germ_res_apply _ y hyW₀ t
    rw [e1, e2]
    exact h0
  have hval := secVal_eq_of_germ_eq hyW₀ hyW₀ _ _ hgerm Z hZ
  rw [secVal_smul, secVal_map, secVal_zero] at hval
  have hg0 : X.presheaf.germ W₀ _ (hZ.mem_open W₀.isOpen hyW₀) g₀ = 0 :=
    (IsUnit.mul_left_eq_zero ht).mp hval
  have hg₀ : g₀ = 0 := germ_injective_of_isIntegral X _ (hZ.mem_open W₀.isOpen hyW₀)
    (hg0.trans (map_zero _).symm)
  refine sub_eq_zero.mp ?_
  rw [← hg, ← X.presheaf.germ_res_apply (homOfLE inf_le_left) y hyW₀ g]
  change X.presheaf.germ W₀ y hyW₀ g₀ = 0
  rw [hg₀, map_zero]

/-- On an integral scheme, multiplication by the germ at `y` of a section `t` of `𝒪_X(B)` is onto
the stalk when every section of `𝒪_X(B)` near `y` is, in `K(X)`, a multiple of `t` by an element
of `𝒪_{X,y}`. -/
theorem surjective_smul_germ_of_forall_secVal [IsIntegral X] {B : Divisor X} {U : X.Opens}
    (t : Γ(B.divisorialSheaf, U)) {y : X} (hy : y ∈ U) {Z : irreducibleComponents X}
    (hyZ : y ∈ Z.1)
    (hsurj : ∀ (V : X.Opens) (hyV : y ∈ V) (φ : Γ(B.divisorialSheaf, V)),
      ∃ b : X.presheaf.stalk y, (stalkToRationalFunctions X hyZ).hom b *
          Divisor.secVal B U t ⟨Z,
            ((isGenericPoint_componentGenericPoint X Z).specializes hyZ).mem_open U.isOpen hy⟩ =
        Divisor.secVal B V φ ⟨Z,
          ((isGenericPoint_componentGenericPoint X Z).specializes hyZ).mem_open V.isOpen hyV⟩) :
    Function.Surjective fun r : X.presheaf.stalk y =>
      r • B.divisorialSheaf.presheaf.germ U y hy t := by
  have hZ := (isGenericPoint_componentGenericPoint X Z).specializes hyZ
  intro z
  obtain ⟨V, hyV, φ, rfl⟩ := B.divisorialSheaf.presheaf.exists_germ_eq z
  obtain ⟨b, hb⟩ := hsurj V hyV φ
  obtain ⟨W, hyW, g, rfl⟩ := X.presheaf.exists_germ_eq b
  refine ⟨X.presheaf.germ W y hyW g, ?_⟩
  let W₀ := W ⊓ (U ⊓ V)
  have hyW₀ : y ∈ W₀ := ⟨hyW, hy, hyV⟩
  let g₀ : Γ(X, W₀) := X.presheaf.map (homOfLE inf_le_left).op g
  let t₀ : Γ(B.divisorialSheaf, W₀) :=
    B.divisorialSheaf.presheaf.map (homOfLE (inf_le_right.trans inf_le_left)).op t
  let φ₀ : Γ(B.divisorialSheaf, W₀) :=
    B.divisorialSheaf.presheaf.map (homOfLE (inf_le_right.trans inf_le_right)).op φ
  have heq : g₀ • t₀ = φ₀ := by
    refine divisorialSheaf_section_ext ⟨Z, hZ.mem_open W₀.isOpen hyW₀⟩ ?_
    rw [secVal_smul, secVal_map, secVal_map, ← hb, stalkToRationalFunctions_germ hyZ hyW g]
    congr 1
    exact X.presheaf.germ_res_apply _ _ _ g
  have e1 : X.presheaf.germ W₀ y hyW₀ g₀ = X.presheaf.germ W y hyW g :=
    X.presheaf.germ_res_apply _ y hyW₀ g
  have e2 : B.divisorialSheaf.presheaf.germ W₀ y hyW₀ t₀ =
      B.divisorialSheaf.presheaf.germ U y hy t :=
    B.divisorialSheaf.presheaf.germ_res_apply _ y hyW₀ t
  have e3 : B.divisorialSheaf.presheaf.germ W₀ y hyW₀ φ₀ =
      B.divisorialSheaf.presheaf.germ V y hyV φ :=
    B.divisorialSheaf.presheaf.germ_res_apply _ y hyW₀ φ
  change X.presheaf.germ W y hyW g • B.divisorialSheaf.presheaf.germ U y hy t = _
  rw [← e1, ← e2, ← Stacks.ModuleStalk.germ_smul, heq, e3]

/-- **A criterion for a germ to be a basis of a stalk of `𝒪_X(B)`.** On an integral scheme, the
germ at `y` of a section `t` of `𝒪_X(B)` whose value in `K(X)` is a unit is a basis of the stalk
when every section of `𝒪_X(B)` near `y` is, in `K(X)`, a multiple of `t` by an element of
`𝒪_{X,y}`. -/
theorem isStalkBasis_germ_divisorialSheaf [IsIntegral X] {B : Divisor X} {U : X.Opens}
    (t : Γ(B.divisorialSheaf, U)) {y : X} (hy : y ∈ U) {Z : irreducibleComponents X}
    (hyZ : y ∈ Z.1)
    (ht : IsUnit (Divisor.secVal B U t ⟨Z,
      ((isGenericPoint_componentGenericPoint X Z).specializes hyZ).mem_open U.isOpen hy⟩))
    (hsurj : ∀ (V : X.Opens) (hyV : y ∈ V) (φ : Γ(B.divisorialSheaf, V)),
      ∃ b : X.presheaf.stalk y, (stalkToRationalFunctions X hyZ).hom b *
          Divisor.secVal B U t ⟨Z,
            ((isGenericPoint_componentGenericPoint X Z).specializes hyZ).mem_open U.isOpen hy⟩ =
        Divisor.secVal B V φ ⟨Z,
          ((isGenericPoint_componentGenericPoint X Z).specializes hyZ).mem_open V.isOpen hyV⟩) :
    IsStalkBasis B.divisorialSheaf y (B.divisorialSheaf.presheaf.germ U y hy t) :=
  ⟨injective_smul_germ_of_isUnit_secVal t hy hyZ ht,
    surjective_smul_germ_of_forall_secVal t hy hyZ hsurj⟩

/-- At the generic point of `X`, the germ of the section `1` of `𝒪_X(B)` is a basis of the
stalk. -/
theorem isStalkBasis_germ_one_genericPoint [IsIntegral X] (B : Divisor X)
    (Z : irreducibleComponents X) :
    IsStalkBasis B.divisorialSheaf (componentGenericPoint X Z)
      (B.divisorialSheaf.presheaf.germ (MMP.Flips.divisorSuppCompl B) _
        (MMP.Flips.componentGenericPoint_mem_divisorSuppCompl B Z)
        (⟨1, fun E hE => Or.inr (by
          change WithZero.exp _ ≤ E.valuation 1
          rw [map_one, MMP.Flips.coeff_eq_zero_of_le_divisorSuppCompl le_rfl hE, neg_zero,
            WithZero.exp_zero])⟩ : Γ(B.divisorialSheaf, MMP.Flips.divisorSuppCompl B))) := by
  refine isStalkBasis_germ_divisorialSheaf _ _ (isGenericPoint_componentGenericPoint X Z).mem
    isUnit_one fun V hyV φ => ⟨Divisor.secVal B V φ ⟨Z, hyV⟩, ?_⟩
  calc _ = (X.presheaf.stalkSpecializes ((isGenericPoint_componentGenericPoint X Z).specializes
          (isGenericPoint_componentGenericPoint X Z).mem)).hom
          (Divisor.secVal B V φ ⟨Z, hyV⟩) * 1 := rfl
    _ = _ := by rw [mul_one, TopCat.Presheaf.stalkSpecializes_refl]; rfl

/-- Along a prime divisor `E`, the stalk of `𝒪_X(B)` at the generic point of `E` has a basis
whose value in `K(X)` is a unit of order `-B(E)` along `E`. -/
theorem exists_isStalkBasis_primeDivisor [IsIntegral X] [CompactSpace X] (B : Divisor X)
    (E : Mori.PrimeDivisor X) :
    ∃ (U : X.Opens) (hy : E.genericPoint ∈ U) (t : Γ(B.divisorialSheaf, U)),
      IsUnit (Divisor.secVal B U t ⟨E.component,
        E.specializes_genericPoint.mem_open U.isOpen hy⟩) ∧
      E.valuation (Divisor.secVal B U t ⟨E.component,
        E.specializes_genericPoint.mem_open U.isOpen hy⟩) = WithZero.exp (-B.coeff E) ∧
      IsStalkBasis B.divisorialSheaf E.genericPoint (B.divisorialSheaf.presheaf.germ U _ hy t) := by
  obtain ⟨U, hE, t, ht, hts⟩ := MMP.Flips.exists_divisorialSection_ord_eq B E
  have hy := E.genericPoint_mem_of_nonempty hE
  let σ : Γ(B.divisorialSheaf, U) := ⟨fun Z => (t : RationalFunctions X) Z.1, hts⟩
  have hunit : IsUnit ((t : RationalFunctions X) E.component) :=
    (Pi.isUnit_iff.mp t.isUnit) E.component
  have hval : E.valuation ((t : RationalFunctions X) E.component) = WithZero.exp (-B.coeff E) := by
    rw [E.valuation_component, ht]
  refine ⟨U, hy, σ, hunit, hval, ?_⟩
  refine isStalkBasis_germ_divisorialSheaf σ hy E.genericPoint_mem_component hunit
    fun V hyV φ => ?_
  have hEV : (E.support ∩ V).Nonempty := ⟨_, MMP.Flips.primeDivisor_genericPoint_mem_support E, hyV⟩
  set f := Divisor.secVal B V φ ⟨E.component, E.specializes_genericPoint.mem_open V.isOpen hyV⟩
  by_cases hf : f = 0
  · exact ⟨0, by simp [hf]⟩
  have hφ : E.OrdGE (-B.coeff E) f := (φ : B.divisorialSubmodule V).2 E hEV
  rcases hφ with h0 | hle
  · exact absurd h0 hf
  set u := hunit.unit
  have hq : 1 ≤ E.valuation (f * (u⁻¹ : (X.presheaf.stalk _)ˣ)) := by
    have hu : E.valuation (u : X.presheaf.stalk _) = WithZero.exp (-B.coeff E) := hval
    have hu' : WithZero.exp (-B.coeff E) *
        E.valuation ((u⁻¹ : (X.presheaf.stalk _)ˣ) : X.presheaf.stalk _) = 1 := by
      rw [← hu, ← map_mul, Units.mul_inv, map_one]
    rw [map_mul, ← hu']
    gcongr
  obtain ⟨b, hb⟩ := E.exists_toComponent_eq_of_one_le_valuation hq
  refine ⟨b, ?_⟩
  change E.toComponent.hom b * (u : X.presheaf.stalk _) = f
  rw [hb, mul_assoc, Units.inv_mul, mul_one]

/-- If `q · t` and `φ` have the same germ at `y`, then in `K(X)` the value of `φ` is `q` times the
value of `t`. -/
theorem secVal_mul_eq_of_smul_germ_eq {B : Divisor X} {y : X} {Z : irreducibleComponents X}
    (hyZ : y ∈ Z.1) {U₁ U₂ : X.Opens} (φ : Γ(B.divisorialSheaf, U₁))
    (t : Γ(B.divisorialSheaf, U₂)) (hy₁ : y ∈ U₁) (hy₂ : y ∈ U₂) (q : X.presheaf.stalk y)
    (h : q • B.divisorialSheaf.presheaf.germ U₂ y hy₂ t =
      B.divisorialSheaf.presheaf.germ U₁ y hy₁ φ) :
    (stalkToRationalFunctions X hyZ).hom q *
        Divisor.secVal B U₂ t ⟨Z,
          ((isGenericPoint_componentGenericPoint X Z).specializes hyZ).mem_open U₂.isOpen hy₂⟩ =
      Divisor.secVal B U₁ φ ⟨Z,
        ((isGenericPoint_componentGenericPoint X Z).specializes hyZ).mem_open U₁.isOpen hy₁⟩ := by
  have hZ := (isGenericPoint_componentGenericPoint X Z).specializes hyZ
  obtain ⟨W, hyW, g, rfl⟩ := X.presheaf.exists_germ_eq q
  let W₀ := W ⊓ U₂
  have hyW₀ : y ∈ W₀ := ⟨hyW, hy₂⟩
  let g₀ : Γ(X, W₀) := X.presheaf.map (homOfLE inf_le_left).op g
  let t₀ : Γ(B.divisorialSheaf, W₀) := B.divisorialSheaf.presheaf.map (homOfLE inf_le_right).op t
  have hgerm : B.divisorialSheaf.presheaf.germ W₀ y hyW₀ (g₀ • t₀) =
      B.divisorialSheaf.presheaf.germ U₁ y hy₁ φ := by
    rw [Stacks.ModuleStalk.germ_smul, ← h]
    congr 1
    · exact X.presheaf.germ_res_apply _ y hyW₀ g
    · exact B.divisorialSheaf.presheaf.germ_res_apply _ y hyW₀ t
  have hval := secVal_eq_of_germ_eq hyW₀ hy₁ _ _ hgerm Z hZ
  rw [secVal_smul, secVal_map] at hval
  rw [stalkToRationalFunctions_germ hyZ hyW g]
  refine Eq.trans ?_ hval
  congr 1
  exact (X.presheaf.germ_res_apply _ _ _ g).symm

/-- **The stalk of an inclusion of divisorial sheaves.** If `t_C` and `t_B` give bases of the
stalks of `𝒪_X(C) ⊆ 𝒪_X(B)` at `y`, the image of the stalk of the inclusion is `(q) · 𝒪_X(B)_y`,
where `q ∈ 𝒪_{X,y}` is `t_C / t_B` in `K(X)`. -/
theorem exists_stalkRange_divisorialSheafInclusion {C B : Divisor X} (h : C ≤ B)
    {y : X} {Z : irreducibleComponents X} (hyZ : y ∈ Z.1) {U₁ U₂ : X.Opens}
    (tC : Γ(C.divisorialSheaf, U₁)) (tB : Γ(B.divisorialSheaf, U₂)) (hy₁ : y ∈ U₁)
    (hy₂ : y ∈ U₂)
    (hC : IsStalkBasis C.divisorialSheaf y (C.divisorialSheaf.presheaf.germ U₁ y hy₁ tC))
    (hB : IsStalkBasis B.divisorialSheaf y (B.divisorialSheaf.presheaf.germ U₂ y hy₂ tB)) :
    ∃ q : X.presheaf.stalk y, (stalkToRationalFunctions X hyZ).hom q *
        Divisor.secVal B U₂ tB ⟨Z,
          ((isGenericPoint_componentGenericPoint X Z).specializes hyZ).mem_open U₂.isOpen hy₂⟩ =
        Divisor.secVal C U₁ tC ⟨Z,
          ((isGenericPoint_componentGenericPoint X Z).specializes hyZ).mem_open U₁.isOpen hy₁⟩ ∧
      StalkRange (Divisor.divisorialSheafInclusion h) y (Ideal.span {q}) := by
  set i := Divisor.divisorialSheafInclusion h
  set mB := B.divisorialSheaf.presheaf.germ U₂ y hy₂ tB
  set mC := C.divisorialSheaf.presheaf.germ U₁ y hy₁ tC
  have himg : stalkLinearMap _ _ i y mC =
      B.divisorialSheaf.presheaf.germ U₁ y hy₁ (i.val.app (op U₁) tC) :=
    AlgebraicGeometry.stalkLinearMap_germ _ _ i U₁ y hy₁ tC
  set q := hB.coord (stalkLinearMap _ _ i y mC)
  have hq : q • mB = stalkLinearMap _ _ i y mC := hB.smul_coord _
  refine ⟨q, secVal_mul_eq_of_smul_germ_eq hyZ (i.val.app (op U₁) tC) tB hy₁ hy₂ q
    (hq.trans himg), le_antisymm ?_ ?_⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨r, rfl⟩ := hC.surjective z
    change stalkLinearMap _ _ i y (r • mC) ∈ _
    rw [map_smul, ← hq, smul_smul, mul_comm, ← smul_smul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  · refine Submodule.smul_le.2 fun a ha t _ => ?_
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨(d * hB.coord t) • mC, ?_⟩
    rw [map_smul, ← hq]
    conv_rhs => rw [← hB.smul_coord t]
    rw [smul_smul, smul_smul]
    congr 1
    ring

/-- In the local ring along a prime divisor, generators of the same principal ideal have the same
order along the divisor. -/
theorem valuation_eq_of_span_eq (E : Mori.PrimeDivisor X) {a b : E.localRing}
    (h : Ideal.span {a} = Ideal.span {b}) :
    E.valuation (E.toComponent.hom a) = E.valuation (E.toComponent.hom b) := by
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨u, rfl⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  rw [map_mul, map_mul, E.valuation_toComponent_of_isUnit u.isUnit, mul_one]

end DivisorialStalk

/-! ### Multiplication by a power of a section as an inclusion -/

section Main

open Stacks.EnriquesSeveriZariski Stacks.Divisors

variable {X : Scheme.{u}}

/-- The stalk map of the zero morphism is zero. -/
@[simp]
theorem stalkLinearMap_zero_apply {A B : X.Modules} (y : X) (z : A.presheaf.stalk y) :
    stalkLinearMap A B 0 y z = 0 := by
  obtain ⟨U, hy, a, rfl⟩ := A.presheaf.exists_germ_eq z
  rw [AlgebraicGeometry.stalkLinearMap_germ]
  exact map_zero _

variable [IsLocallyNoetherian X] [IsNormal X]

/-- `D` is the divisor of zeros of the section `s` of `L^{⊗ m}`: for some divisor `G` and some
isomorphism `L^{⊗ m} ≅ 𝒪_X(G)`, multiplication by `s` is an isomorphism `𝒪_X ≅ 𝒪_X(G - D)`
followed by the inclusion `𝒪_X(G - D) ⊆ 𝒪_X(G)`. -/
def IsSectionDivisor (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {m : ℕ}
    (s : Γ(Stacks.Ample.tensorPowModule X L (m : ℤ), ⊤)) (D : Divisor X) : Prop :=
  ∃ (G : Divisor X) (ε : Stacks.Ample.tensorPowModule X L (m : ℤ) ≅ G.divisorialSheaf)
    (h : G - D ≤ G) (e : Stacks.Ample.unitModule X ≅ (G - D).divisorialSheaf),
    sectionHom _ s ≫ ε.hom = e.hom ≫ Divisor.divisorialSheafInclusion h

variable [IsIntegral X] [CompactSpace X]

/-- The stalk ideal of `s` at the generic point of a prime divisor `E` is generated by an element
of order `D(E)` along `E`. -/
theorem IsSectionDivisor.exists_stalkRange {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
    {m : ℕ} {s : Γ(Stacks.Ample.tensorPowModule X L (m : ℤ), ⊤)} {D : Divisor X}
    (hD : IsSectionDivisor L s D) (E : Mori.PrimeDivisor X) :
    ∃ q : E.localRing, E.valuation (E.toComponent.hom q) = WithZero.exp (D.coeff E) ∧
      StalkRange (sectionHom _ s) E.genericPoint (Ideal.span {q}) := by
  obtain ⟨G, ε, hGD, e, hε⟩ := hD
  obtain ⟨J, hJ⟩ := exists_stalkRange_sectionHom _ s E.genericPoint
  obtain ⟨UG, hyG, tG, -, hvG, hbG⟩ := exists_isStalkBasis_primeDivisor G E
  obtain ⟨U₁, hy₁, t₁, -, hv₁, hb₁⟩ := exists_isStalkBasis_primeDivisor (G - D) E
  obtain ⟨q, hq, hr⟩ := exists_stalkRange_divisorialSheafInclusion hGD
    E.genericPoint_mem_component t₁ tG hy₁ hyG hb₁ hbG
  have h1 := hJ.comp (StalkRange.of_iso ε)
  have h2 := (StalkRange.of_iso e).comp hr
  rw [hε, Ideal.mul_top] at h1
  rw [Ideal.top_mul] at h2
  refine ⟨q, ?_, (StalkRange.unique_of_isStalkBasis hbG h1 h2) ▸ hJ⟩
  have hv := congrArg E.valuation hq
  rw [map_mul, hvG, hv₁, DivisorWithCoeffs.coeff_sub] at hv
  have hne : (WithZero.exp (-G.coeff E) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  refine mul_right_cancel₀ hne (hv.trans ?_)
  rw [← WithZero.exp_add]
  congr 1
  ring

omit [CompactSpace X] in
/-- `α ≠ 0` for a morphism of divisorial sheaves whose stalk at the generic point is onto. -/
theorem ne_zero_of_stalkRange_top {A B : Divisor X} (α : A.divisorialSheaf ⟶ B.divisorialSheaf)
    (Z : irreducibleComponents X) (h : StalkRange α (componentGenericPoint X Z) ⊤) : α ≠ 0 := by
  rintro rfl
  obtain ⟨bb, hb⟩ : ∃ bb, IsStalkBasis B.divisorialSheaf (componentGenericPoint X Z) bb :=
    ⟨_, isStalkBasis_germ_one_genericPoint B Z⟩
  have hne : bb ≠ 0 := fun h0 => by
    have := hb.injective (a₁ := 1) (a₂ := 0) (by
      rw [one_smul, zero_smul, h0])
    exact one_ne_zero this
  rw [StalkRange, Submodule.top_smul] at h
  have hmem : bb ∈ LinearMap.range (stalkLinearMap _ _
      (0 : A.divisorialSheaf ⟶ B.divisorialSheaf) (componentGenericPoint X Z)) :=
    h ▸ Submodule.mem_top
  obtain ⟨z, hz⟩ := hmem
  rw [stalkLinearMap_zero_apply] at hz
  exact hne hz.symm

omit [CompactSpace X] in
/-- At the generic point of `X`, the stalk image of a section `s` with divisor of zeros `D` is the
whole stalk. -/
theorem IsSectionDivisor.stalkRange_top {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
    {m : ℕ} {s : Γ(Stacks.Ample.tensorPowModule X L (m : ℤ), ⊤)} {D : Divisor X}
    (hD : IsSectionDivisor L s D) (Z : irreducibleComponents X) :
    StalkRange (sectionHom _ s) (componentGenericPoint X Z) ⊤ := by
  obtain ⟨G, ε, hGD, e, hε⟩ := hD
  obtain ⟨J, hJ⟩ := exists_stalkRange_sectionHom _ s (componentGenericPoint X Z)
  obtain ⟨q, hq, hr⟩ := exists_stalkRange_divisorialSheafInclusion hGD
    (isGenericPoint_componentGenericPoint X Z).mem _ _ _ _
    (isStalkBasis_germ_one_genericPoint (G - D) Z) (isStalkBasis_germ_one_genericPoint G Z)
  have hq1 : q = 1 := by
    have : (stalkToRationalFunctions X (isGenericPoint_componentGenericPoint X Z).mem).hom q =
        q := by
      change (X.presheaf.stalkSpecializes _).hom q = q
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    rw [this] at hq
    exact (mul_one q).symm.trans hq
  rw [hq1, Ideal.span_singleton_one] at hr
  have h1 := hJ.comp (StalkRange.of_iso ε)
  have h2 := (StalkRange.of_iso e).comp hr
  rw [hε] at h1
  have hJ1 : J = ⊤ := by
    have := StalkRange.unique_of_isStalkBasis (isStalkBasis_germ_one_genericPoint G Z) h1 h2
    rwa [Ideal.mul_top, Ideal.top_mul] at this
  rwa [hJ1] at hJ

/-- If `𝒪_X(C) ⊆ 𝒪_X(A)` composed with an isomorphism onto `𝒪_X(C)` has stalk ideal at the
generic point of a prime divisor `E` generated by an element of order `d` along `E`, then
`C(E) = A(E) - d`. -/
theorem coeff_eq_sub_of_stalkRange_comp_divisorialSheafInclusion {F : X.Modules}
    {A C : Divisor X} (hC : C ≤ A) (eC : F ≅ C.divisorialSheaf) (E : Mori.PrimeDivisor X)
    {d : ℤ} (q : E.localRing) (hq : E.valuation (E.toComponent.hom q) = WithZero.exp d)
    (hr : StalkRange (eC.hom ≫ Divisor.divisorialSheafInclusion hC) E.genericPoint
      (Ideal.span {q})) :
    C E = A E - d := by
  obtain ⟨UA, hyA, tA, -, hvA, hbA⟩ := exists_isStalkBasis_primeDivisor A E
  obtain ⟨UC, hyC, tC, -, hvC, hbC⟩ := exists_isStalkBasis_primeDivisor C E
  obtain ⟨q', hq', hr'⟩ := exists_stalkRange_divisorialSheafInclusion hC
    E.genericPoint_mem_component tC tA hyC hyA hbC hbA
  have h2 := (StalkRange.of_iso eC).comp hr'
  rw [Ideal.top_mul] at h2
  have hqq := valuation_eq_of_span_eq E (StalkRange.unique_of_isStalkBasis hbA hr h2)
  have hv := congrArg E.valuation hq'
  rw [map_mul, hvA, hvC, ← hqq, hq, ← WithZero.exp_add, WithZero.exp_inj] at hv
  change d + -A E = -C E at hv
  linarith

/-- **Multiplication by `s^k` is an inclusion of divisorial sheaves.** Let `D` be the divisor of
zeros of a section `s` of `L^{⊗ m}`. For every isomorphism `L^{⊗ n} ≅ 𝒪_X(A)` (read on the twist
`𝒪_X ⊗ L^{⊗ n}`), there is an isomorphism `L^{⊗ (n - km)} ≅ 𝒪_X(A - kD)` carrying
multiplication by `s^k` to the inclusion `𝒪_X(A - kD) ⊆ 𝒪_X(A)`. -/
theorem exists_iso_chain_eq_divisorialSheafInclusion_of_iso (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {m : ℕ}
    (s : Γ(Stacks.Ample.tensorPowModule X L (m : ℤ), ⊤)) {D : Divisor X}
    (hD : IsSectionDivisor L s D) (n : ℤ) {A : Divisor X}
    (e₂ : twist L (Stacks.Ample.unitModule X) n ≅ A.divisorialSheaf) (k : ℕ) :
    ∃ (e₁ : twist L (Stacks.Ample.unitModule X) (descend m n k) ≅
        (A - (k : ℤ) • D).divisorialSheaf) (h : A - (k : ℤ) • D ≤ A),
      chain L s (Stacks.Ample.unitModule X) n k ≫ e₂.hom =
        e₁.hom ≫ Divisor.divisorialSheafInclusion h := by
  obtain ⟨A', ⟨f'⟩⟩ : ∃ A' : Divisor X, Nonempty (A'.divisorialSheaf ≅
      twist L (Stacks.Ample.unitModule X) (descend m n k)) := by
    have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
        (Stacks.Ample.tensorPowModule X L (descend m n k)) :=
      Stacks.Ample.isInvertibleModule_tensorPowModule X L _
    obtain ⟨A', ⟨f⟩⟩ := MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible
      (Stacks.Ample.tensorPowModule X L (descend m n k))
    exact ⟨A', ⟨f ≪≫ (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) _).symm⟩⟩
  set α := f'.hom ≫ chain L s (Stacks.Ample.unitModule X) n k ≫ e₂.hom with hαdef
  have hαE : ∀ E : Mori.PrimeDivisor X, ∃ q : E.localRing,
      E.valuation (E.toComponent.hom q) = WithZero.exp ((k : ℤ) * D.coeff E) ∧
        StalkRange α E.genericPoint (Ideal.span {q}) := by
    intro E
    obtain ⟨q, hq, hr⟩ := hD.exists_stalkRange E
    have h := (StalkRange.of_iso f').comp
      ((hr.chain L (Stacks.Ample.unitModule X) n k).comp
        (StalkRange.of_iso e₂))
    rw [Ideal.mul_top, Ideal.top_mul, Ideal.span_singleton_pow] at h
    refine ⟨q ^ k, ?_, h⟩
    rw [map_pow, map_pow, hq, ← WithZero.exp_nsmul, nsmul_eq_mul]
  have hα : α ≠ 0 := by
    obtain ⟨Z⟩ : Nonempty (irreducibleComponents X) := ⟨⟨Set.univ, by
      rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
    have h := (StalkRange.of_iso f').comp
      (((hD.stalkRange_top Z).chain L (Stacks.Ample.unitModule X) n k).comp
        (StalkRange.of_iso e₂))
    rw [Ideal.top_pow, Ideal.mul_top, Ideal.top_mul] at h
    exact ne_zero_of_stalkRange_top α Z h
  obtain ⟨C, hC, eC, hαC⟩ := exists_iso_comp_divisorialSheafInclusion α hα
  have hCeq : C = A - (k : ℤ) • D := by
    ext E
    obtain ⟨q, hq, hr⟩ := hαE E
    change C E = A E - (k : ℤ) * D E
    exact coeff_eq_sub_of_stalkRange_comp_divisorialSheafInclusion hC eC E q hq (hαC ▸ hr)
  subst hCeq
  refine ⟨f'.symm ≪≫ eC, hC, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hαC, hαdef, Iso.inv_hom_id_assoc]

end Main

end MMP.LcBpf
