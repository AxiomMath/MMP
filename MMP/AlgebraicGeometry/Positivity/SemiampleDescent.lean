module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.AlgebraicGeometry.Resolution.Surface.TopFormDivisors
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.RestrictEpi
public import MMP.AlgebraicGeometry.Morphisms.GenericallyFinite
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Semiampleness descends under proper generically finite covers

Let `q : S ⟶ Y` be a proper surjective generically finite morphism of normal varieties over an
infinite field `k`, and `π : Y ⟶ Z` a morphism. If `L` is a `ℚ`-Cartier `ℚ`-divisor on `Y` such
that `q^*L` is semiample over `Z`, then `L` is semiample over `Z`.

The proof is by norms. Let `S → W → Y` be the Stein factorization of `q`, with `κ : W ⟶ Y`
finite and `𝒪_W = h_* 𝒪_S`, and let `B = mL` be a Cartier divisor with `q^*B` generated over
`Z`. Fix `y ∈ Y`. The fibre `κ⁻¹(y)` is finite, and a section of `q^*B` vanishes at a point `x`
of `S` over `y` exactly when it vanishes at `h(x)`, since its local coefficients are pulled back
from `W`. Choosing, for each point of `κ⁻¹(y)`, a relative section of `q^*B` not vanishing at a
point over it, a combination with coefficients in `k` avoids all of them since `k` is infinite;
call it `ψ`. With `d = [K(S) : K(Y)]`, the field norm `N(ψ)` is a rational section of `dB`: for a
local equation `g` of `B`, the coefficient `q^*g · ψ` is a regular function on the inverse image
of an affine open `V`, integral over `Γ(Y, V)`, so its norm `g^d N(ψ)` is integral over the
integrally closed `𝒪_{Y,P}` for every prime divisor `P` meeting `V`. Near `y` the inverse of
`q^*g · ψ` is regular as well, so `N(ψ)` generates `𝒪_Y(dB)` at `y`.

## Main results

* `MMP.Fourfold.exists_isRelativelyFreeDivisor_of_pullback`: semiampleness of `ℚ`-Cartier
  `ℚ`-divisors descends under proper surjective generically finite morphisms.
* `MMP.Fourfold.exists_isRelativelyFreeDivisor_zsmul_of_isRelativelyFreeDivisor_pullback`: the
  same for Cartier divisors, with the multiple `[K(S) : K(Y)]`.
* `MMP.Fourfold.isRelativelyFreeDivisor_of_forall_exists`: a divisor generated near every point
  by relative sections is relatively free, the converse of
  `MMP.Fourfold.exists_coeff_add_ord_eq_zero_of_isRelativelyFree`.
* `MMP.Fourfold.exists_normSection`: the norm construction.
* `MMP.Fourfold.ordGE_zero_normAt`: norms of regular functions are regular on a normal base.

## Implementation notes

* A rational invertible sheaf on the normal variety `Y` is a `ℚ`-Cartier `ℚ`-divisor `L`, and its
  pull-back is `MMP.Mori.QDivisor.pullback`. Semiampleness of `L` over `Z` is expressed as in
  `MMP.Fourfold.IsEventuallyFree`, relative to `π`: some positive multiple `mL` is a Cartier
  divisor `M` with `π^* π_* 𝒪_Y(M) → 𝒪_Y(M)` surjective (`MMP.Fourfold.IsRelativelyFreeDivisor`).
  The structure morphism of `S` over `Z` is `q ≫ π`.
* Generic finiteness is finiteness of the extension of function fields `K(Y) ⊆ K(S)`.
* The base field is any infinite field, for instance `ℂ`; the only use of the base field is the
  choice of a combination of finitely many sections avoiding finitely many points. No hypothesis
  is placed on `Z` or on `π`: projectivity over a Noetherian base is not used.
* The function fields are the local rings at the generic points of the (unique) irreducible
  components, with the field structure `MMP.Resolution.componentField`, as for the orders of
  vanishing `MMP.Mori.PrimeDivisor.ord`. The norm is Mathlib's `Algebra.norm`, and the regularity
  of norms of integral elements over an integrally closed domain is `Algebra.isIntegral_norm`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

section RelativelyFree

variable {X Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- A unit `ψ` of `K(X)` with `D + div ψ` effective on `V`, as a section of `𝒪_X(D)` over `V`. -/
def divisorialSectionOfUnit {D : Divisor X} {V : X.Opens} (ψ : (RationalFunctions X)ˣ)
    (h : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ V).Nonempty → 0 ≤ D.coeff P + P.ord ψ) :
    Γ(D.divisorialSheaf, V) :=
  ⟨fun Z => (ψ : RationalFunctions X) Z.1, isDivisorialSection_of_unit ψ h⟩

omit [IsIntegral X] in
open Classical in
/-- If `D + div ψ` has coefficient `0` along every prime divisor through `x`, then it has
coefficient `0` along every prime divisor through a point outside the support of its part away
from `x`. -/
theorem coeff_add_ord_eq_zero_of_notMem_supp_filter {D : Divisor X}
    {ψ : (RationalFunctions X)ˣ} {x : X}
    (hψx : ∀ P : MMP.Mori.PrimeDivisor X, x ∈ P.support → D.coeff P + P.ord ψ = 0)
    (E : MMP.Mori.PrimeDivisor X) {z : X} (hzE : z ∈ E.support)
    (hz : z ∉ DivisorWithCoeffs.supp ((D + principalDivisor ψ).filter fun P => x ∉ P.support)) :
    D.coeff E + E.ord ψ = 0 := by
  by_cases hxE : x ∈ E.support
  · exact hψx E hxE
  · by_contra hne
    apply hz
    rw [DivisorWithCoeffs.mem_supp_iff]
    refine ⟨E, ?_, hzE⟩
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.filter_apply_pos
        (fun P : MMP.Mori.PrimeDivisor X => x ∉ P.support) _ hxE,
      ← DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
    exact hne

omit [IsIntegral X] [CompactSpace X] in
/-- If `t` is a section of `𝒪_X(D)` over `O ⊇ Ω` and `D + div ψ` has coefficient `0` along every
prime divisor meeting `Ω`, then `t ψ⁻¹` is a regular rational function on `Ω`. -/
theorem isDivisorialSection_zero_mul_inv {D : Divisor X} {O Ω : X.Opens} (hΩO : Ω ≤ O)
    (t : D.divisorialSubmodule O) (ψ : (RationalFunctions X)ˣ)
    (hψ : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ Ω).Nonempty → D.coeff E + E.ord ψ = 0) :
    (0 : Divisor X).IsDivisorialSection Ω fun Z =>
      t.1 ⟨Z.1, hΩO Z.2⟩ * ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 := by
  intro E hE
  have h₁ := t.2 E (hE.mono (Set.inter_subset_inter_right _ hΩO))
  have h₂ : E.OrdGE (D.coeff E) (((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)
      E.component) := Or.inr (by
    rw [E.valuation_component, PrimeDivisor.ord_inv, WithZero.exp_le_exp]
    linarith [hψ E hE])
  rw [DivisorWithCoeffs.coeff_zero, neg_zero, ← neg_add_cancel (D.coeff E)]
  exact h₁.mul h₂

omit [IsIntegral X] in
/-- **Local generating relative sections make a divisor relatively free.** Let `D` be a divisor
on a normal integral locally Noetherian scheme `X` and `f : X ⟶ Z`. If every `x ∈ X` has an
open `U ∋ f x` and a unit `ψ` of `K(X)` with `D + div ψ` effective on `f⁻¹U` and of coefficient
`0` along every prime divisor through `x`, then `f^* f_* 𝒪_X(D) → 𝒪_X(D)` is surjective. -/
theorem isRelativelyFreeDivisor_of_forall_exists (f : X ⟶ Z) {D : Divisor X}
    (h : ∀ x : X, ∃ (U : Z.Opens) (_ : f x ∈ U) (ψ : (RationalFunctions X)ˣ),
      (∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ f ⁻¹ᵁ U).Nonempty → 0 ≤ D.coeff P + P.ord ψ) ∧
      ∀ P : MMP.Mori.PrimeDivisor X, x ∈ P.support → D.coeff P + P.ord ψ = 0) :
    IsRelativelyFreeDivisor f D := by
  classical
  apply Stacks.AlgebraicGeometry.FiniteTypeSubmodule.epi_of_isLocallySurjective_mapPresheaf
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro O t x hxO
  obtain ⟨U, hxU, ψ, hψ, hψx⟩ := h x
  let A : Divisor X := D + principalDivisor ψ
  let A' : Divisor X := A.filter (fun P => x ∉ P.support)
  have hxA' : x ∉ A'.supp := by
    rw [DivisorWithCoeffs.mem_supp_iff]
    rintro ⟨E, hE, hxE⟩
    exact hE (by
      rw [DivisorWithCoeffs.coeff_apply,
        Finsupp.filter_apply_neg (fun P => x ∉ P.support) A (not_not.mpr hxE)])
  let Ω : X.Opens := O ⊓ f ⁻¹ᵁ U ⊓ ⟨(A'.supp : Set X)ᶜ, A'.isClosed_supp.isOpen_compl⟩
  have hxΩ : x ∈ Ω := ⟨⟨hxO, hxU⟩, hxA'⟩
  have hΩO : Ω ≤ O := inf_le_left.trans inf_le_left
  have hΩU : Ω ≤ f ⁻¹ᵁ U := inf_le_left.trans inf_le_right
  obtain ⟨Zx, hxZx⟩ := exists_mem_irreducibleComponents x
  let t' : D.divisorialSubmodule O := t
  let ρfun : ToType ((rationalFunctionsPresheaf X).obj (op Ω)) := fun Z =>
    t'.1 ⟨Z.1, hΩO Z.2⟩ * ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1
  have hρ : (0 : Divisor X).IsDivisorialSection Ω ρfun :=
    isDivisorialSection_zero_mul_inv hΩO t' ψ fun E ⟨_, hzE, hzΩ⟩ =>
      coeff_add_ord_eq_zero_of_notMem_supp_filter hψx E hzE hzΩ.2
  obtain ⟨ρ, hρeq⟩ := hρ.exists_eq
  let σ : Γ(D.divisorialSheaf, f ⁻¹ᵁ U) := divisorialSectionOfUnit ψ hψ
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let e := (adj.unit.app ((Scheme.Modules.pushforward f).obj D.divisorialSheaf)).app U σ
  have he : (adj.counit.app D.divisorialSheaf).app (f ⁻¹ᵁ U) e = σ :=
    congrArg (fun φ : (Scheme.Modules.pushforward f).obj D.divisorialSheaf ⟶
      (Scheme.Modules.pushforward f).obj D.divisorialSheaf => (φ.app U).hom σ)
      (adj.right_triangle_components D.divisorialSheaf)
  set F' := (Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj D.divisorialSheaf)
  have hnat : (adj.counit.app D.divisorialSheaf).app Ω (F'.presheaf.map (homOfLE hΩU).op e) =
      D.divisorialSheaf.presheaf.map (homOfLE hΩU).op σ := by
    rw [← he]
    exact ConcreteCategory.congr_hom
      ((adj.counit.app D.divisorialSheaf).mapPresheaf.naturality (homOfLE hΩU).op) e
  refine ⟨Ω, hΩO, ⟨ρ • F'.presheaf.map (homOfLE hΩU).op e, ?_⟩, hxΩ⟩
  change (adj.counit.app D.divisorialSheaf).app Ω (ρ • F'.presheaf.map (homOfLE hΩU).op e) = _
  rw [Scheme.Modules.Hom.app_smul, hnat]
  refine Subtype.ext (funext fun Z => ?_)
  have hZ := congrFun hρeq Z
  change X.presheaf.germ Ω _ Z.2 ρ * (ψ : RationalFunctions X) Z.1 = t'.1 ⟨Z.1, hΩO Z.2⟩
  rw [toRationalFunctionsPresheaf_app_apply] at hZ
  rw [hZ]
  simp only [ρfun]
  rw [mul_assoc, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Pi.one_apply,
    mul_one]

end RelativelyFree

/-! ### Auxiliary results -/

section Auxiliary

/-- **Avoiding finitely many hypersurfaces over an infinite field.** Let `k` be an infinite field,
`ι` a finite type, `n : ι → ℕ` injective, and for each `i` a ring homomorphism `ι_i : k → K_i`
into a field and values `v i j ∈ K_i` with `v i i ≠ 0`. Then some `t ∈ k` makes every
`∑_j ι_i(t)^{n_j} v_{ij}` nonzero: the polynomial `∑_j v_{ij} T^{n_j}` is nonzero, so it has
finitely many roots. -/
theorem exists_forall_sum_pow_mul_ne_zero {k : Type*} [Field k] [Infinite k] {ι : Type*}
    [Fintype ι] (n : ι → ℕ) (hn : Function.Injective n) (K : ι → Type*) [∀ i, Field (K i)]
    (e : ∀ i, k →+* K i) (v : ∀ i, ι → K i) (hv : ∀ i, v i i ≠ 0) :
    ∃ t : k, ∀ i, ∑ j, e i t ^ n j * v i j ≠ 0 := by
  classical
  let p : ∀ i, Polynomial (K i) := fun i => ∑ j, Polynomial.C (v i j) * Polynomial.X ^ n j
  have hp : ∀ i, p i ≠ 0 := by
    intro i h0
    have := congrArg (fun r => Polynomial.coeff r (n i)) h0
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single i (fun j _ hj => ite_eq_right fun h => hj (hn h).symm)
      (fun h => absurd (Finset.mem_univ i) h), ite_eq_left rfl] at this
    exact hv i this
  have hfin : (⋃ i, (e i) ⁻¹' ((p i).roots.toFinset : Set (K i))).Finite :=
    Set.finite_iUnion fun i => (Finset.finite_toSet _).preimage (e i).injective.injOn
  obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
  refine ⟨t, fun i h0 => ht (Set.mem_iUnion.mpr ⟨i, ?_⟩)⟩
  have heval : (p i).eval (e i t) = 0 := by
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [← h0]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  exact (Polynomial.mem_roots (hp i)).mpr heval

/-- **A combination avoiding finitely many points.** Let `k` be an infinite field with a ring
homomorphism `ι : k →+* Γ(W, U)`, and let `c_w ∈ Γ(W, U)` be invertible at `p_w ∈ U`, for `w` in
a finite type. For `n` injective, some `t ∈ k` makes `∑_j ι(t)^{n_j} c_j` invertible at every
`p_w`. -/
theorem exists_forall_mem_basicOpen_sum_pow_mul {k : Type*} [Field k] [Infinite k]
    {W : Scheme.{u}} {U : W.Opens} (ι : k →+* Γ(W, U)) {F : Type*} [Fintype F] (n : F → ℕ)
    (hn : Function.Injective n) (p : F → W) (hp : ∀ w, p w ∈ U) (c : F → Γ(W, U))
    (hc : ∀ w, p w ∈ W.basicOpen (c w)) :
    ∃ t : k, ∀ w, p w ∈ W.basicOpen (∑ j, ι t ^ n j * c j) := by
  let ev : ∀ w, Γ(W, U) →+* W.residueField (p w) := fun w => (W.evaluation U (p w) (hp w)).hom
  obtain ⟨t, ht⟩ := exists_forall_sum_pow_mul_ne_zero n hn (fun w => W.residueField (p w))
    (fun w => (ev w).comp ι) (fun w j => ev w (c j))
    (fun w => (W.evaluation_ne_zero_iff_mem_basicOpen (p w) (hp w) (c w)).mpr (hc w))
  refine ⟨t, fun w => ?_⟩
  rw [← W.evaluation_ne_zero_iff_mem_basicOpen (p w) (hp w)]
  simpa [ev] using ht w

/-- If `h.app U` is an isomorphism and `b` is a regular function on `h⁻¹U` invertible at `x`, then
the corresponding regular function on `U` is invertible at `h x`. -/
theorem mem_basicOpen_inv_app {S W : Scheme.{u}} (h : S ⟶ W) {U : W.Opens} [IsIso (h.app U)]
    (b : Γ(S, h ⁻¹ᵁ U)) {x : S} (hx : x ∈ S.basicOpen b) :
    h x ∈ W.basicOpen ((inv (h.app U)).hom b) := by
  have h₁ : x ∈ h ⁻¹ᵁ W.basicOpen ((inv (h.app U)).hom b) := by
    rw [Scheme.preimage_basicOpen]
    change x ∈ S.basicOpen ((inv (h.app U) ≫ h.app U).hom b)
    rw [IsIso.inv_hom_id]
    exact hx
  exact h₁

/-- **Shrinking around a fibre.** If `q : S ⟶ Y` is universally closed, `b` is a regular function
on `q⁻¹V` and `b` is invertible at every point over `y ∈ V`, then `b` is invertible on `q⁻¹V'` for
some open `V' ∋ y` contained in `V`. -/
theorem exists_preimage_le_basicOpen {S Y : Scheme.{u}} (q : S ⟶ Y) [UniversallyClosed q]
    {V : Y.Opens} (b : Γ(S, q ⁻¹ᵁ V)) {y : Y} (hy : y ∈ V)
    (hb : ∀ x : S, q x = y → x ∈ S.basicOpen b) :
    ∃ V' : Y.Opens, y ∈ V' ∧ V' ≤ V ∧ q ⁻¹ᵁ V' ≤ S.basicOpen b := by
  let K : Set S := closure ((q ⁻¹ᵁ V : Set S) ∩ (S.basicOpen b : Set S)ᶜ)
  have hK : K ⊆ (S.basicOpen b : Set S)ᶜ :=
    closure_minimal Set.inter_subset_right (S.basicOpen b).isOpen.isClosed_compl
  have hKc : IsClosed (q '' K) := q.isClosedMap _ isClosed_closure
  refine ⟨V ⊓ ⟨(q '' K)ᶜ, hKc.isOpen_compl⟩, ⟨hy, ?_⟩, inf_le_left, ?_⟩
  · rintro ⟨x, hxK, rfl⟩
    exact hK hxK (hb x rfl)
  · intro x ⟨hxV, hxK⟩
    by_contra hxb
    exact hxK ⟨x, subset_closure ⟨hxV, hxb⟩, rfl⟩

/-- **Integrality from the Stein factorization.** If `q = h ≫ κ` with `κ` finite and `h` inducing
isomorphisms on sections, then `Γ(Y, V) → Γ(S, q⁻¹V)` is integral for every affine open `V`. -/
theorem isIntegral_app_of_comp {S W Y : Scheme.{u}} {q : S ⟶ Y} {h : S ⟶ W} {κ : W ⟶ Y}
    (hq : h ≫ κ = q) [IsFinite κ] (hh : ∀ U : W.Opens, IsIso (h.app U)) {V : Y.Opens}
    (hV : IsAffineOpen V) : (q.app V).hom.IsIntegral := by
  subst hq
  exact RingHom.IsIntegral.trans _ _ (κ.finite_app V hV).to_isIntegral
    (RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (h.app _)).2)

end Auxiliary

/-! ### The extension of function fields -/

section FunctionFields

attribute [local instance] MMP.Resolution.componentField

variable {S Y : Scheme.{u}} [IsIntegral S] [IsIntegral Y] (q : S ⟶ Y) [IsDominant q]

/-- A dominant morphism of integral schemes maps the generic point to the generic point. -/
theorem map_componentGenericPoint (ZS : irreducibleComponents S) (ZY : irreducibleComponents Y) :
    q (componentGenericPoint S ZS) = componentGenericPoint Y ZY := by
  rw [componentGenericPoint_eq_genericPoint, componentGenericPoint_eq_genericPoint,
    map_genericPoint_of_isDominant]

/-- The extension `K(Y) → K(S)` of function fields of a dominant morphism `q : S ⟶ Y` of
integral schemes, on the local rings at the generic points of the components `ZY`, `ZS`. -/
def fieldMap (ZY : irreducibleComponents Y) (ZS : irreducibleComponents S) :
    Y.presheaf.stalk (componentGenericPoint Y ZY) →+*
      S.presheaf.stalk (componentGenericPoint S ZS) :=
  (Y.presheaf.stalkSpecializes (specializes_of_eq (map_componentGenericPoint q ZS ZY)) ≫
    q.stalkMap (componentGenericPoint S ZS)).hom

/-- `fieldMap` on germs. -/
theorem fieldMap_germ (ZY : irreducibleComponents Y) (ZS : irreducibleComponents S) {V : Y.Opens}
    (hV : componentGenericPoint Y ZY ∈ V) (s : Γ(Y, V)) :
    fieldMap q ZY ZS (Y.presheaf.germ V _ hV s) =
      S.presheaf.germ (q ⁻¹ᵁ V) (componentGenericPoint S ZS)
        (show q _ ∈ V by rw [map_componentGenericPoint q ZS ZY]; exact hV) (q.app V s) := by
  rw [fieldMap, CommRingCat.hom_comp, RingHom.comp_apply,
    TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

/-- The norm `N_{K(S)/K(Y)}` of the extension of function fields of `q`, on the local rings at the
generic points of the components `ZY`, `ZS`. -/
def normAt (ZY : irreducibleComponents Y) (ZS : irreducibleComponents S) :
    S.presheaf.stalk (componentGenericPoint S ZS) →*
      Y.presheaf.stalk (componentGenericPoint Y ZY) :=
  letI := (fieldMap q ZY ZS).toAlgebra
  Algebra.norm (Y.presheaf.stalk (componentGenericPoint Y ZY))

/-- The degree `[K(S) : K(Y)]` of the extension of function fields of `q`. -/
def fieldDegree (ZY : irreducibleComponents Y) (ZS : irreducibleComponents S) : ℕ :=
  letI := (fieldMap q ZY ZS).toAlgebra
  Module.finrank (Y.presheaf.stalk (componentGenericPoint Y ZY))
    (S.presheaf.stalk (componentGenericPoint S ZS))

/-- `N(θ a) = a^d` for `θ : K(Y) → K(S)` and `d = [K(S) : K(Y)]`. -/
theorem normAt_fieldMap (ZY : irreducibleComponents Y) (ZS : irreducibleComponents S)
    (a : Y.presheaf.stalk (componentGenericPoint Y ZY)) :
    normAt q ZY ZS (fieldMap q ZY ZS a) = a ^ fieldDegree q ZY ZS := by
  let := (fieldMap q ZY ZS).toAlgebra
  exact Algebra.norm_algebraMap a

/-- The degree does not depend on the choice of components. -/
theorem fieldDegree_eq (ZY ZY' : irreducibleComponents Y) (ZS ZS' : irreducibleComponents S) :
    fieldDegree q ZY ZS = fieldDegree q ZY' ZS' := by
  have := subsingleton_irreducibleComponents (X := Y)
  have := subsingleton_irreducibleComponents (X := S)
  obtain rfl := Subsingleton.elim ZY ZY'
  obtain rfl := Subsingleton.elim ZS ZS'
  rfl

/-- The norm of a unit is a unit. -/
theorem isUnit_normAt (ZY : irreducibleComponents Y) (ZS : irreducibleComponents S)
    {a : S.presheaf.stalk (componentGenericPoint S ZS)} (ha : IsUnit a) :
    IsUnit (normAt q ZY ZS a) :=
  ha.map _

/-- `fieldMap q ZY ZS` is the extension of function fields `functionFieldMap q` read through the
identifications of the local rings at the generic points of components with the function
fields. -/
theorem fieldMap_eq (ZY : irreducibleComponents Y) (ZS : irreducibleComponents S) :
    fieldMap q ZY ZS =
      (S.presheaf.stalkCongr
          (Inseparable.of_eq (componentGenericPoint_eq_genericPoint ZS))).inv.hom.comp
        ((functionFieldMap q).comp
          (Y.presheaf.stalkCongr
            (Inseparable.of_eq (componentGenericPoint_eq_genericPoint ZY))).hom.hom) := by
  ext a
  obtain ⟨V, hV, s, rfl⟩ := Y.presheaf.exists_germ_eq a
  rw [fieldMap_germ, RingHom.comp_apply, RingHom.comp_apply]
  change _ = (S.presheaf.stalkSpecializes
      (specializes_of_eq (componentGenericPoint_eq_genericPoint ZS))).hom
    (functionFieldMap q ((Y.presheaf.stalkSpecializes
      (specializes_of_eq (componentGenericPoint_eq_genericPoint ZY).symm)).hom
        (Y.presheaf.germ V _ hV s)))
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap, CommRingCat.hom_comp,
    RingHom.comp_apply]
  change _ = (S.presheaf.stalkSpecializes
      (specializes_of_eq (componentGenericPoint_eq_genericPoint ZS))).hom
    ((q.stalkMap (genericPoint S)).hom
    ((Y.presheaf.stalkSpecializes (specializes_of_eq (map_genericPoint_of_isDominant q))).hom
      (Y.presheaf.germ V _ ((componentGenericPoint_eq_genericPoint ZY) ▸ hV) s)))
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]

/-- A generically finite dominant morphism has a finite extension `fieldMap`. -/
theorem fieldMap_finite (ZY : irreducibleComponents Y) (ZS : irreducibleComponents S)
    (hfin : letI := functionFieldMapAlgebra q; Module.Finite Y.functionField S.functionField) :
    (fieldMap q ZY ZS).Finite := by
  rw [fieldMap_eq]
  refine RingHom.Finite.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (S.presheaf.stalkCongr _).inv).2)
    (RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Y.presheaf.stalkCongr _).hom).2))

variable [IsLocallyNoetherian Y] [IsNormal Y]

/-- The pull-back `q^*_i φ` of a local equation (`MMP.Mori.pullbackComponent`) is the image of `φ`
under the extension of function fields. -/
theorem pullbackComponent_eq_fieldMap {B : Divisor Y}
    (hB : ∀ Z : irreducibleComponents S, q (componentGenericPoint S Z) ∉ B.supp) {U : Y.Opens}
    {φ : (RationalFunctions Y)ˣ} (hφ : B.IsLocalEquation U φ) (ZS : irreducibleComponents S)
    (hZ : q (componentGenericPoint S ZS) ∈ U) (ZY : irreducibleComponents Y) :
    (pullbackComponent q hB hφ ZS hZ : S.presheaf.stalk _) =
      fieldMap q ZY ZS ((φ : RationalFunctions Y) ZY) := by
  have hW : q (componentGenericPoint S ZS) ∈ ZY.1 :=
    mem_irreducibleComponent_of_irreducibleSpace ZY _
  let h := specializes_of_eq (map_componentGenericPoint q ZS ZY)
  let a : (Y.presheaf.stalk (q (componentGenericPoint S ZS)))ˣ :=
    Units.map (Y.presheaf.stalkSpecializes h).hom.toMonoidHom
      (RationalFunctions.unitsEquiv Y φ ZY)
  have ha : (stalkToRationalFunctions Y hW).hom a = (φ : RationalFunctions Y) ZY := by
    change (Y.presheaf.stalkSpecializes h ≫ Y.presheaf.stalkSpecializes _).hom _ = _
    rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  rw [pullbackComponent_eq hB hφ hZ hW a ha]
  rfl

variable [IsLocallyNoetherian S] [IsNormal S]

/-- If `B' = q^*B` and `φ` is a local equation of `B` on `U`, then along every prime divisor `E`
of `S` meeting `q⁻¹U`, the image of `φ` in `K(S)` has order `B'_E`. -/
theorem valuation_fieldMap_of_isPullback {B : Divisor Y}
    {hB : ∀ Z : irreducibleComponents S, q (componentGenericPoint S Z) ∉ B.supp} {B' : Divisor S}
    (h : B.IsPullback q hB B') {U : Y.Opens} {φ : (RationalFunctions Y)ˣ}
    (hφ : B.IsLocalEquation U φ) (E : MMP.Mori.PrimeDivisor S)
    (hE : (E.support ∩ q ⁻¹ᵁ U).Nonempty) (ZY : irreducibleComponents Y) :
    E.valuation (fieldMap q ZY E.component ((φ : RationalFunctions Y) ZY)) =
      WithZero.exp (B'.coeff E) := by
  rw [h U φ hφ E hE, ← pullbackComponent_eq_fieldMap q hB hφ E.component _ ZY,
    PrimeDivisor.valuation_eq_exp_ordUnit]

/-- **Sections of `q^*B` as regular functions.** Let `B' = q^*B`, `g` a local equation of `B`
on `V₀` and `V ⊆ V₀`. If `ψ ∈ K(S)` has order `≥ -B'_E` along every prime divisor `E` meeting
`q⁻¹V`, then `q^*g · ψ` is a regular function on `q⁻¹V` (algebraic Hartogs). -/
theorem exists_section_eq_fieldMap_mul {B : Divisor Y}
    {hB : ∀ Z : irreducibleComponents S, q (componentGenericPoint S Z) ∉ B.supp} {B' : Divisor S}
    (h : B.IsPullback q hB B') {V₀ : Y.Opens} {g : (RationalFunctions Y)ˣ}
    (hg : B.IsLocalEquation V₀ g) {V : Y.Opens} (hV : V ≤ V₀) (ZY : irreducibleComponents Y)
    (ψ : RationalFunctions S)
    (hψ : ∀ E : MMP.Mori.PrimeDivisor S, (E.support ∩ q ⁻¹ᵁ V).Nonempty →
      E.OrdGE (-B'.coeff E) (ψ E.component)) :
    ∃ b : Γ(S, q ⁻¹ᵁ V), ∀ (Z : irreducibleComponents S) (hZ : componentGenericPoint S Z ∈ q ⁻¹ᵁ V),
      S.presheaf.germ _ _ hZ b = fieldMap q ZY Z ((g : RationalFunctions Y) ZY) * ψ Z := by
  have hsec : (0 : Divisor S).IsDivisorialSection (q ⁻¹ᵁ V)
      (fun Z => fieldMap q ZY Z.1 ((g : RationalFunctions Y) ZY) * ψ Z.1) := by
    intro E hE
    have h1 : E.OrdGE (B'.coeff E) (fieldMap q ZY E.component ((g : RationalFunctions Y) ZY)) :=
      Or.inr (le_of_eq (valuation_fieldMap_of_isPullback q h hg E
        (hE.mono (Set.inter_subset_inter_right _ fun x hx => hV hx)) ZY).symm)
    rw [DivisorWithCoeffs.coeff_zero, neg_zero, ← add_neg_cancel (B'.coeff E)]
    exact h1.mul (hψ E hE)
  obtain ⟨b, hb⟩ := hsec.exists_eq
  exact ⟨b, fun Z hZ => congrFun hb ⟨Z, hZ⟩⟩

/-- **A section generating at a point.** In the situation of
`MMP.Fourfold.exists_section_eq_fieldMap_mul`, if `ψ` is a unit and `B'_E + ord_E ψ = 0` along
every prime divisor `E` through `x ∈ q⁻¹V`, then the regular function `q^*g · ψ` is a unit at
`x`. -/
theorem mem_basicOpen_of_forall_ord_eq_zero {B : Divisor Y}
    {hB : ∀ Z : irreducibleComponents S, q (componentGenericPoint S Z) ∉ B.supp} {B' : Divisor S}
    (h : B.IsPullback q hB B') {V₀ : Y.Opens} {g : (RationalFunctions Y)ˣ}
    (hg : B.IsLocalEquation V₀ g) {V : Y.Opens} (hV : V ≤ V₀) (ZY : irreducibleComponents Y)
    (ψ : (RationalFunctions S)ˣ) (b : Γ(S, q ⁻¹ᵁ V))
    (hb : ∀ (Z : irreducibleComponents S) (hZ : componentGenericPoint S Z ∈ q ⁻¹ᵁ V),
      S.presheaf.germ _ _ hZ b =
        fieldMap q ZY Z ((g : RationalFunctions Y) ZY) * (ψ : RationalFunctions S) Z)
    {x : S} (hx : x ∈ q ⁻¹ᵁ V)
    (hψx : ∀ E : MMP.Mori.PrimeDivisor S, x ∈ E.support → B'.coeff E + E.ord ψ = 0) :
    x ∈ S.basicOpen b := by
  let χ : (RationalFunctions S)ˣ := (RationalFunctions.unitsEquiv S).symm fun Z =>
    Units.map (fieldMap q ZY Z).toMonoidHom (RationalFunctions.unitsEquiv Y g ZY) *
      RationalFunctions.unitsEquiv S ψ Z
  have hχ : ∀ Z, (χ : RationalFunctions S) Z =
      fieldMap q ZY Z ((g : RationalFunctions Y) ZY) * (ψ : RationalFunctions S) Z := fun Z => rfl
  have hord : ∀ E : MMP.Mori.PrimeDivisor S, x ∈ E.support → E.ord χ = 0 := by
    intro E hxE
    have h1 := E.valuation_component χ
    rw [hχ, map_mul, valuation_fieldMap_of_isPullback q h hg E ⟨x, hxE, hV hx⟩ ZY,
      E.valuation_component, ← WithZero.exp_add, hψx E hxE, WithZero.exp_zero] at h1
    exact WithZero.exp_eq_one.mp h1.symm
  obtain ⟨Zx, hxZ⟩ := exists_mem_irreducibleComponents x
  obtain ⟨a, ha⟩ := exists_unit_stalk_of_forall_ord_eq_zero hxZ χ hord
  have hZx : componentGenericPoint S Zx ∈ q ⁻¹ᵁ V :=
    (genericPoint_mem_iff Zx _).mpr ⟨x, hx, hxZ⟩
  have hgerm : S.presheaf.germ _ x hx b = a := by
    apply stalkToRationalFunctions_injective hxZ
    rw [ha, hχ, ← hb Zx hZx]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply S.presheaf _ _ _
  rw [Scheme.mem_basicOpen S b x hx, hgerm]
  exact a.isUnit

omit [IsLocallyNoetherian S] [IsNormal S] in
/-- **Norms of regular functions are regular.** Let `V ⊆ Y` be an open over which
`Γ(Y, V) → Γ(S, q⁻¹V)` is integral, and `P` a prime divisor of `Y` meeting `V`. For a regular
function `b` on `q⁻¹V`, the norm `N_{K(S)/K(Y)}(b)` has nonnegative order along `P`: `b` is
integral over `Γ(Y, V)`, hence so is its norm, which therefore lies in the integrally closed
local ring `𝒪_{Y,P}`. -/
theorem ordGE_zero_normAt {V : Y.Opens} (hint : (q.app V).hom.IsIntegral)
    (P : MMP.Mori.PrimeDivisor Y) (hPV : P.genericPoint ∈ V) (ZS : irreducibleComponents S)
    (hS : componentGenericPoint S ZS ∈ q ⁻¹ᵁ V) (b : Γ(S, q ⁻¹ᵁ V)) :
    P.OrdGE 0 (normAt q P.component ZS (S.presheaf.germ _ _ hS b)) := by
  have hYV : componentGenericPoint Y P.component ∈ V :=
    P.specializes_genericPoint.mem_open V.isOpen hPV
  let := (Y.presheaf.germ V _ hYV).hom.toAlgebra
  let := (fieldMap q P.component ZS).toAlgebra
  let : Algebra Γ(Y, V) (S.presheaf.stalk (componentGenericPoint S ZS)) :=
    ((fieldMap q P.component ZS).comp (Y.presheaf.germ V _ hYV).hom).toAlgebra
  have : IsScalarTower Γ(Y, V) (Y.presheaf.stalk (componentGenericPoint Y P.component))
      (S.presheaf.stalk (componentGenericPoint S ZS)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hβ : IsIntegral Γ(Y, V) (S.presheaf.germ _ _ hS b) := by
    obtain ⟨p, hp, hpb⟩ := hint b
    refine ⟨p, hp, ?_⟩
    have h1 := congrArg (S.presheaf.germ _ _ hS).hom hpb
    rw [Polynomial.hom_eval₂, map_zero] at h1
    rwa [show (S.presheaf.germ _ _ hS).hom.comp (q.app V).hom =
      algebraMap Γ(Y, V) (S.presheaf.stalk (componentGenericPoint S ZS)) from
        RingHom.ext fun s => (fieldMap_germ q P.component ZS hYV s).symm] at h1
  have hN := Algebra.isIntegral_norm (Y.presheaf.stalk (componentGenericPoint Y P.component)) hβ
  let := P.toComponent.hom.toAlgebra
  let : Algebra Γ(Y, V) P.localRing := (Y.presheaf.germ V _ hPV).hom.toAlgebra
  have : IsScalarTower Γ(Y, V) P.localRing
      (Y.presheaf.stalk (componentGenericPoint Y P.component)) :=
    IsScalarTower.of_algebraMap_eq fun s =>
      (TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf _ _ _).symm
  have hN' := hN.tower_top (A := P.localRing)
  have := isFractionRing_stalkToRationalFunctions P.genericPoint_mem_component
  have : IsIntegrallyClosed P.localRing := IsNormal.stalk_normal _
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hN'
  change P.OrdGE 0 (Algebra.norm _ _)
  rw [← hr]
  rcases eq_or_ne r 0 with rfl | hr0
  · exact Or.inl (map_zero _)
  · refine Or.inr ?_
    rw [WithZero.exp_zero]
    exact P.one_le_valuation_toComponent hr0

end FunctionFields

/-! ### Descent of local generating sections by norms -/

section Descent

attribute [local instance] MMP.Resolution.componentField

variable {S Y W Z : Scheme.{u}} [IsIntegral S] [IsIntegral Y]
  [IsLocallyNoetherian S] [IsNormal S] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **Norms of sections are sections.** Let `B' = q^*B` for a Cartier divisor `B`, with
`Γ(Y, V) → Γ(S, q⁻¹V)` integral for affine `V`. If `ψ ∈ K(S)` has order `≥ -B'_E` along every
prime divisor `E` meeting `q⁻¹O`, then `dB + div N(ψ) ≥ 0` on `O`, for `d = [K(S) : K(Y)]`. -/
theorem zero_le_coeff_smul_add_ord_of_normAt (q : S ⟶ Y) [IsDominant q]
    (hint : ∀ V : Y.Opens, IsAffineOpen V → (q.app V).hom.IsIntegral) {B : Divisor Y}
    (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents S, q (componentGenericPoint S Z) ∉ B.supp}
    {B' : Divisor S} (hpb : B.IsPullback q hB B') (ZY : irreducibleComponents Y)
    (ZS : irreducibleComponents S) {O : Y.Opens} (ψ : RationalFunctions S)
    (hψ : ∀ E : MMP.Mori.PrimeDivisor S, (E.support ∩ q ⁻¹ᵁ O).Nonempty →
      E.OrdGE (-B'.coeff E) (ψ E.component))
    (φ : (RationalFunctions Y)ˣ)
    (hφ : ∀ Z', (φ : RationalFunctions Y) Z' = normAt q Z' ZS (ψ ZS))
    (P : MMP.Mori.PrimeDivisor Y) (hP : (P.support ∩ O).Nonempty) :
    0 ≤ ((fieldDegree q ZY ZS : ℤ) • B).coeff P + P.ord φ := by
  have hηP : P.genericPoint ∈ O := (P.genericPoint_mem_iff _).mpr hP
  obtain ⟨V₀, hηV₀, g, hg⟩ := hBc P.genericPoint
  obtain ⟨V, hVaff, hηV, hVsub⟩ := exists_isAffineOpen_mem_and_subset
    (show P.genericPoint ∈ V₀ ⊓ O from ⟨hηV₀, hηP⟩)
  obtain ⟨b, hb⟩ := exists_section_eq_fieldMap_mul q hpb hg (fun z hz => (hVsub hz).1)
    P.component ψ
    (fun E hE => hψ E (hE.mono (Set.inter_subset_inter_right _ fun x hx => (hVsub hx).2)))
  have hS : componentGenericPoint S ZS ∈ q ⁻¹ᵁ V := by
    change q _ ∈ V
    rw [map_componentGenericPoint q ZS P.component]
    exact P.specializes_genericPoint.mem_open V.isOpen hηV
  have key := ordGE_zero_normAt q (hint V hVaff) P hηV ZS hS b
  rw [hb ZS hS, map_mul, normAt_fieldMap, ← hφ] at key
  have hv := key.resolve_left (mul_ne_zero
    (pow_ne_zero _ (g.isUnit.map (Pi.evalRingHom _ _)).ne_zero)
    (φ.isUnit.map (Pi.evalRingHom _ _)).ne_zero)
  rw [map_mul, map_pow, P.valuation_component, P.valuation_component, ← WithZero.exp_nsmul,
    ← WithZero.exp_add, WithZero.exp_le_exp] at hv
  rw [DivisorWithCoeffs.coeff_smul, hg P ((P.genericPoint_mem_iff V₀).mp hηV₀),
    fieldDegree_eq q ZY P.component ZS ZS]
  simp only [nsmul_eq_mul, zsmul_eq_mul] at hv ⊢
  exact hv

omit [IsLocallyNoetherian S] in
/-- **Norms of generating sections generate.** In the situation of
`MMP.Fourfold.zero_le_coeff_smul_add_ord_of_normAt`, let `g` be a local equation of `B` on `V₀`
and `b` a regular function on `q⁻¹V` with germ `q^*g · ψ`, invertible along `q⁻¹(y)`. Then
`dB + div N(ψ) ≤ 0` along every prime divisor through `y`, for `d = [K(S) : K(Y)]`. -/
theorem coeff_smul_add_ord_normAt_le_zero (q : S ⟶ Y) [UniversallyClosed q] [IsDominant q]
    (hint : ∀ V : Y.Opens, IsAffineOpen V → (q.app V).hom.IsIntegral) {B : Divisor Y}
    {V₀ : Y.Opens} {g : (RationalFunctions Y)ˣ} (hg : B.IsLocalEquation V₀ g)
    (ZY : irreducibleComponents Y) (ZS : irreducibleComponents S) (ψ : RationalFunctions S)
    (φ : (RationalFunctions Y)ˣ)
    (hφ : ∀ Z', (φ : RationalFunctions Y) Z' = normAt q Z' ZS (ψ ZS)) {V : Y.Opens}
    (b : Γ(S, q ⁻¹ᵁ V))
    (hb : ∀ hZ : componentGenericPoint S ZS ∈ q ⁻¹ᵁ V,
      S.presheaf.germ _ _ hZ b = fieldMap q ZY ZS ((g : RationalFunctions Y) ZY) * ψ ZS)
    {y : Y} (hyV : y ∈ V) (hyV₀ : y ∈ V₀) (hbfib : ∀ x : S, q x = y → x ∈ S.basicOpen b)
    (P : MMP.Mori.PrimeDivisor Y) (hyP : y ∈ P.support) :
    ((fieldDegree q ZY ZS : ℤ) • B).coeff P + P.ord φ ≤ 0 := by
  have := subsingleton_irreducibleComponents (X := Y)
  obtain ⟨V₁, hyV₁, hV₁V, hV₁b⟩ := exists_preimage_le_basicOpen q b hyV hbfib
  obtain ⟨V₂, hV₂aff, hyV₂, hV₂sub⟩ := exists_isAffineOpen_mem_and_subset hyV₁
  let i₂ : q ⁻¹ᵁ V₂ ⟶ q ⁻¹ᵁ V := homOfLE fun x hx => hV₁V (hV₂sub hx)
  let b₂ : Γ(S, q ⁻¹ᵁ V₂) := (S.presheaf.map i₂.op).hom b
  have hb₂ : IsUnit b₂ := RingedSpace.isUnit_of_isUnit_germ S.toRingedSpace _ b₂ fun x hx => by
    have h1 := (S.mem_basicOpen b x (i₂.le hx)).mp (hV₁b (hV₂sub hx))
    rwa [← TopCat.Presheaf.germ_res_apply S.presheaf i₂ x hx b] at h1
  have hspec : P.genericPoint ⤳ y := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyP
    exact specializes_iff_mem_closure.mpr hyP
  have hηP : P.genericPoint ∈ V₂ := hspec.mem_open V₂.isOpen hyV₂
  have hS : componentGenericPoint S ZS ∈ q ⁻¹ᵁ V₂ := by
    change q _ ∈ V₂
    rw [map_componentGenericPoint q ZS P.component]
    exact P.specializes_genericPoint.mem_open V₂.isOpen hηP
  have key := ordGE_zero_normAt q (hint V₂ hV₂aff) P hηP ZS hS (↑hb₂.unit⁻¹)
  have hgb : S.presheaf.germ _ _ hS b₂ =
      fieldMap q ZY ZS ((g : RationalFunctions Y) ZY) * ψ ZS := by
    rw [TopCat.Presheaf.germ_res_apply S.presheaf i₂ _ hS b]
    exact hb _
  obtain rfl : ZY = P.component := Subsingleton.elim _ _
  have hN : normAt q P.component ZS (S.presheaf.germ _ _ hS (↑hb₂.unit⁻¹)) *
      normAt q P.component ZS (S.presheaf.germ _ _ hS b₂) = 1 := by
    rw [← map_mul, ← map_mul, hb₂.val_inv_mul, map_one, map_one]
  rw [hgb, map_mul, normAt_fieldMap, ← hφ] at hN
  have hv1 := key.resolve_left (left_ne_zero_of_mul_eq_one hN)
  have hv2 := congrArg P.valuation hN
  rw [map_mul, map_one] at hv2
  have hv3 : P.valuation (((g : RationalFunctions Y) P.component) ^ fieldDegree q
      P.component ZS * (φ : RationalFunctions Y) P.component) ≤ 1 :=
    (le_mul_of_one_le_left' (show (1 : ℤᵐ⁰) ≤ _ from hv1)).trans_eq hv2
  rw [map_mul, map_pow, P.valuation_component, P.valuation_component, ← WithZero.exp_nsmul,
    ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv3
  rw [DivisorWithCoeffs.coeff_smul, hg P ⟨y, hyP, hyV₀⟩]
  simp only [nsmul_eq_mul, zsmul_eq_mul] at hv3 ⊢
  exact hv3

omit [IsIntegral S] in
/-- If every `ψ_j` has order `≥ m` along `E` and `c` is regular along `E`, then so has
`∑_j c^{n_j} ψ_j`. -/
theorem ordGE_sum_pow_mul {F : Type*} [Fintype F] {E : MMP.Mori.PrimeDivisor S} {m : ℤ}
    (c : RationalFunctions S) (a : E.localRing) (hc : c E.component = E.toComponent.hom a)
    (n : F → ℕ) (ψ : F → RationalFunctions S) (hE : ∀ j, E.OrdGE m (ψ j E.component)) :
    E.OrdGE m ((∑ j, c ^ n j * ψ j) E.component) := by
  rw [Finset.sum_apply]
  refine Finset.sum_induction _ (E.OrdGE m) (fun _ _ h₁ h₂ => h₁.add h₂)
    (PrimeDivisor.OrdGE.zero _) fun j _ => ?_
  rw [Pi.mul_apply, Pi.pow_apply, hc, ← map_pow]
  exact (hE j).toComponent_mul _

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- **A combination generating along a fibre.** Let `q = h ≫ κ` with `h` inducing isomorphisms
on sections, `y ∈ V` and `k` an infinite field mapping to `Γ(Y, ⊤)`. Suppose that each point `w`
of the finite fibre `κ⁻¹(y)` is `h(x_w)`, and that `ψ_w ∈ K(S)^×` and a regular function `b_w`
on `q⁻¹V` with germ `q^*g · ψ_w` invertible at `x_w` are given. Then some `k`-linear combination
`ψ` of the `ψ_w` has a regular function `b` on `q⁻¹V` with germ `q^*g · ψ`, invertible along
`q⁻¹(y)`, and `ψ` has order `≥ m` along every prime divisor along which every `ψ_w` has. -/
theorem exists_sum_section_mem_basicOpen {k : Type u} [Field k] [Infinite k]
    (ι : k →+* Γ(Y, ⊤)) (h : S ⟶ W) (κ : W ⟶ Y) [IsDominant (h ≫ κ)]
    (hh : ∀ U : W.Opens, IsIso (h.app U)) {g : RationalFunctions Y} {V : Y.Opens}
    (ZY : irreducibleComponents Y) {y : Y} (hyV : y ∈ V) [Finite (κ ⁻¹' {y})]
    (ψw : κ ⁻¹' {y} → (RationalFunctions S)ˣ) (bw : κ ⁻¹' {y} → Γ(S, (h ≫ κ) ⁻¹ᵁ V))
    (hbw : ∀ w Z (hZ : componentGenericPoint S Z ∈ (h ≫ κ) ⁻¹ᵁ V),
      S.presheaf.germ _ _ hZ (bw w) =
        fieldMap (h ≫ κ) ZY Z (g ZY) * (ψw w : RationalFunctions S) Z)
    (xw : κ ⁻¹' {y} → S) (hxw : ∀ w, h (xw w) = w) (hbx : ∀ w, xw w ∈ S.basicOpen (bw w)) :
    ∃ (ψ : RationalFunctions S) (b : Γ(S, (h ≫ κ) ⁻¹ᵁ V)),
      (∀ Z (hZ : componentGenericPoint S Z ∈ (h ≫ κ) ⁻¹ᵁ V),
        S.presheaf.germ _ _ hZ b = fieldMap (h ≫ κ) ZY Z (g ZY) * ψ Z) ∧
      (∀ x : S, (h ≫ κ) x = y → x ∈ S.basicOpen b) ∧
      ∀ (E : MMP.Mori.PrimeDivisor S) (m : ℤ),
        (∀ w, E.OrdGE m ((ψw w : RationalFunctions S) E.component)) →
          E.OrdGE m (ψ E.component) := by
  classical
  have := Fintype.ofFinite (κ ⁻¹' {y})
  let cw : κ ⁻¹' {y} → Γ(W, κ ⁻¹ᵁ V) := fun w => (inv (h.app (κ ⁻¹ᵁ V))).hom (bw w)
  have hcw : ∀ w, (h.app (κ ⁻¹ᵁ V)).hom (cw w) = bw w := fun w => by
    change (inv (h.app (κ ⁻¹ᵁ V)) ≫ h.app (κ ⁻¹ᵁ V)).hom (bw w) = bw w
    rw [IsIso.inv_hom_id]
    rfl
  have hwV : ∀ w : κ ⁻¹' {y}, w.1 ∈ κ ⁻¹ᵁ V := fun w => by
    change κ w.1 ∈ V
    rw [show κ w.1 = y from w.2]
    exact hyV
  have hwc : ∀ w : κ ⁻¹' {y}, w.1 ∈ W.basicOpen (cw w) := fun w => by
    rw [← hxw w]
    exact mem_basicOpen_inv_app h (U := κ ⁻¹ᵁ V) (bw w) (hbx w)
  let ιV : k →+* Γ(Y, V) := (Y.presheaf.map (homOfLE le_top : V ⟶ ⊤).op).hom.comp ι
  let n : κ ⁻¹' {y} → ℕ := fun w => (Fintype.equivFin _ w : ℕ)
  have hn : Function.Injective n := fun a b hab => (Fintype.equivFin _).injective (Fin.ext hab)
  obtain ⟨t, ht⟩ :=
    exists_forall_mem_basicOpen_sum_pow_mul ((κ.app V).hom.comp ιV) n hn Subtype.val hwV cw hwc
  let a : Γ(W, κ ⁻¹ᵁ V) := (κ.app V).hom (ιV t)
  let c : Γ(W, κ ⁻¹ᵁ V) := ∑ j, a ^ n j * cw j
  have hcy : ∀ w : κ ⁻¹' {y}, w.1 ∈ W.basicOpen c := ht
  have hYV : componentGenericPoint Y ZY ∈ V :=
    (genericPoint_mem_iff ZY V).mpr ⟨y, hyV, mem_irreducibleComponent_of_irreducibleSpace ZY y⟩
  let cst : RationalFunctions S := fun Z =>
    fieldMap (h ≫ κ) ZY Z (Y.presheaf.germ ⊤ (componentGenericPoint Y ZY) trivial (ι t))
  let ψ : RationalFunctions S := ∑ j, cst ^ n j * (ψw j : RationalFunctions S)
  have hψZ : ∀ Z, ψ Z = ∑ j, cst Z ^ n j * (ψw j : RationalFunctions S) Z := fun Z => by
    simp [ψ, Finset.sum_apply]
  have hagerm : ∀ Z (hZ : componentGenericPoint S Z ∈ (h ≫ κ) ⁻¹ᵁ V),
      S.presheaf.germ _ _ hZ ((h.app (κ ⁻¹ᵁ V)).hom a) = cst Z := by
    intro Z hZ
    change S.presheaf.germ _ _ hZ (((h ≫ κ).app V).hom (ιV t)) = _
    rw [← fieldMap_germ (h ≫ κ) ZY Z hYV (ιV t)]
    exact congrArg (fieldMap (h ≫ κ) ZY Z)
      (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE le_top) _ hYV (ι t))
  refine ⟨ψ, (h.app (κ ⁻¹ᵁ V)).hom c, fun Z hZ => ?_, fun x hx => ?_, fun E m hE => ?_⟩
  · change (S.presheaf.germ (h ⁻¹ᵁ (κ ⁻¹ᵁ V)) _ hZ).hom ((h.app _).hom (∑ j, a ^ n j * cw j)) = _
    rw [map_sum, map_sum, hψZ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, hcw]
    erw [hagerm Z hZ, hbw j Z hZ]
    ring
  · have h1 : x ∈ h ⁻¹ᵁ W.basicOpen c := hcy ⟨h x, hx⟩
    rwa [Scheme.preimage_basicOpen] at h1
  · refine ordGE_sum_pow_mul cst (S.presheaf.germ ((h ≫ κ) ⁻¹ᵁ ⊤) E.genericPoint trivial
      (((h ≫ κ).app ⊤).hom (ι t))) ?_ n (fun j => (ψw j : RationalFunctions S)) hE
    erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    rw [← fieldMap_germ (h ≫ κ) ZY E.component (show componentGenericPoint Y ZY ∈ ⊤ from trivial)]

omit [IsLocallyNoetherian S] in
/-- A regular function `b` on `V`, invertible at a point of `V`, whose germ at the generic point
of every component is `u · r`, has `r` nonzero on every component. -/
theorem ne_zero_of_germ_eq_mul {V : S.Opens} (b : Γ(S, V)) {x : S} (hxV : x ∈ V)
    (hxb : x ∈ S.basicOpen b) (u r : RationalFunctions S)
    (hb : ∀ Z (hZ : componentGenericPoint S Z ∈ V), S.presheaf.germ _ _ hZ b = u Z * r Z)
    (Z : irreducibleComponents S) : r Z ≠ 0 := by
  intro h0
  have hxZ : x ∈ Z.1 := mem_irreducibleComponent_of_irreducibleSpace Z x
  apply (((S.mem_basicOpen b x hxV).mp hxb).map (stalkToRationalFunctions S hxZ).hom).ne_zero
  rw [stalkToRationalFunctions, TopCat.Presheaf.germ_stalkSpecializes_apply]
  erw [hb Z ((genericPoint_mem_iff Z _).mpr ⟨x, hxV, hxZ⟩)]
  rw [h0, mul_zero]

/-- **Descent of relative generation by norms.** Let `q : S ⟶ Y` be a universally closed
surjective morphism of normal integral locally Noetherian schemes, with a factorization
`q = h ≫ κ` through a finite `κ : W ⟶ Y` and a surjective `h` with `h_* 𝒪_S = 𝒪_W` (a Stein
factorization), and suppose `Y` receives an infinite field `k`. Let `B` be a Cartier divisor on
`Y` and `B' = q^*B`, and suppose that `B'` is generated over `Z` by relative sections: every
`x ∈ S` has an open `U ∋ π(q x)` of `Z` and `ψ ∈ K(S)^×` with `B' + div ψ ≥ 0` on
`q⁻¹π⁻¹U` and `= 0` along the prime divisors through `x`. Then `dB` is generated over `Z` in the
same sense, for `d = [K(S) : K(Y)]`.

For `y ∈ Y` the fibre `κ⁻¹(y)` is finite; for each of its points `w` a generating section near a
point over `w` is chosen, and a `k`-linear combination `ψ` of them which does not vanish at any
point of `κ⁻¹(y)` exists since `k` is infinite. As `h_* 𝒪_S = 𝒪_W`, `ψ` does not vanish along
`q⁻¹(y)`. The norm `N_{K(S)/K(Y)}(ψ)` is then the required section of `dB`: locally
`N(q^*g · ψ) = g^d N(ψ)` for a local equation `g` of `B`, the norm of the integral element
`q^*g · ψ` is regular since `Y` is normal (`MMP.Fourfold.ordGE_zero_normAt`), and near `y` the same
holds for the inverse. -/
theorem exists_normSection {k : Type u} [Field k] [Infinite k] (ι : k →+* Γ(Y, ⊤))
    (q : S ⟶ Y) [UniversallyClosed q] [IsDominant q] (hsurj : Function.Surjective q)
    (h : S ⟶ W) (κ : W ⟶ Y) (hcomp : h ≫ κ = q) [IsFinite κ] (hh : ∀ U : W.Opens, IsIso (h.app U))
    (hhs : Function.Surjective h) (πY : Y ⟶ Z) {B : Divisor Y} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents S, q (componentGenericPoint S Z) ∉ B.supp}
    {B' : Divisor S} (hpb : B.IsPullback q hB B') (ZY : irreducibleComponents Y)
    (ZS : irreducibleComponents S)
    (hfree : ∀ x : S, ∃ (U : Z.Opens) (_ : πY (q x) ∈ U) (ψ : (RationalFunctions S)ˣ),
      (∀ E : MMP.Mori.PrimeDivisor S, (E.support ∩ q ⁻¹ᵁ (πY ⁻¹ᵁ U)).Nonempty →
        0 ≤ B'.coeff E + E.ord ψ) ∧
      ∀ E : MMP.Mori.PrimeDivisor S, x ∈ E.support → B'.coeff E + E.ord ψ = 0)
    (y : Y) :
    ∃ (U : Z.Opens) (_ : πY y ∈ U) (φ : (RationalFunctions Y)ˣ),
      (∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ πY ⁻¹ᵁ U).Nonempty →
        0 ≤ ((fieldDegree q ZY ZS : ℤ) • B).coeff P + P.ord φ) ∧
      ∀ P : MMP.Mori.PrimeDivisor Y, y ∈ P.support →
        ((fieldDegree q ZY ZS : ℤ) • B).coeff P + P.ord φ = 0 := by
  classical
  subst hcomp
  have := (κ.finite_preimage_singleton y).to_subtype
  choose xw hxw using fun w : κ ⁻¹' {y} => hhs w.1
  have hqx : ∀ w, (h ≫ κ) (xw w) = y := fun w => by
    rw [Scheme.Hom.comp_apply, hxw]
    exact w.2
  choose Uw hUw ψw hψw hψxw using fun w => hfree (xw w)
  have hyUw : ∀ w, πY y ∈ Uw w := fun w => hqx w ▸ hUw w
  obtain ⟨U, hyU, hUle⟩ : ∃ U : Z.Opens, πY y ∈ U ∧ ∀ w, U ≤ Uw w :=
    ⟨⟨⋂ w, (Uw w : Set Z), isOpen_iInter_of_finite fun w => (Uw w).isOpen⟩,
      Set.mem_iInter.mpr hyUw, fun w => Set.iInter_subset (fun w => (Uw w : Set Z)) w⟩
  obtain ⟨V₀, hyV₀, g, hg⟩ := hBc y
  obtain ⟨V, hVaff, hyV, hVsub⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ V₀ ⊓ πY ⁻¹ᵁ U from ⟨hyV₀, hyU⟩)
  have hVV₀ : V ≤ V₀ := fun z hz => (hVsub hz).1
  have hψOrd : ∀ w (E : MMP.Mori.PrimeDivisor S), (E.support ∩ (h ≫ κ) ⁻¹ᵁ (πY ⁻¹ᵁ U)).Nonempty →
      E.OrdGE (-B'.coeff E) ((ψw w : RationalFunctions S) E.component) := by
    intro w E hE
    refine Or.inr ?_
    rw [E.valuation_component, WithZero.exp_le_exp]
    have := hψw w E (hE.mono (Set.inter_subset_inter_right _ fun x hx => hUle w hx))
    linarith
  choose bw hbw using fun w => exists_section_eq_fieldMap_mul (h ≫ κ) hpb hg hVV₀ ZY (ψw w)
    (fun E hE => hψOrd w E (hE.mono (Set.inter_subset_inter_right _ fun x hx => (hVsub hx).2)))
  have hbx : ∀ w, xw w ∈ S.basicOpen (bw w) := fun w =>
    mem_basicOpen_of_forall_ord_eq_zero (h ≫ κ) hpb hg hVV₀ ZY (ψw w) (bw w) (hbw w)
      (show (h ≫ κ) (xw w) ∈ V from (hqx w).symm ▸ hyV) (hψxw w)
  obtain ⟨ψ, b, hbgerm, hbfib, hψsum⟩ :=
    exists_sum_section_mem_basicOpen ι h κ hh ZY hyV ψw bw hbw xw hxw hbx
  obtain ⟨x0, hx0⟩ := hsurj y
  have hψne : ∀ Z, ψ Z ≠ 0 := ne_zero_of_germ_eq_mul b
    (show (h ≫ κ) x0 ∈ V from hx0.symm ▸ hyV) (hbfib x0 hx0)
    (fun Z => fieldMap (h ≫ κ) ZY Z ((g : RationalFunctions Y) ZY)) ψ hbgerm
  let φ : (RationalFunctions Y)ˣ := (RationalFunctions.unitsEquiv Y).symm fun Z' =>
    (isUnit_normAt (h ≫ κ) Z' ZS (isUnit_of_ne_zero_stalk ZS (hψne ZS))).unit
  have hφ : ∀ Z', (φ : RationalFunctions Y) Z' = normAt (h ≫ κ) Z' ZS (ψ ZS) := fun Z' => rfl
  have hint : ∀ V : Y.Opens, IsAffineOpen V → ((h ≫ κ).app V).hom.IsIntegral :=
    fun _ hV => isIntegral_app_of_comp rfl hh hV
  have hclaim1 := zero_le_coeff_smul_add_ord_of_normAt (h ≫ κ) hint hBc hpb ZY ZS ψ
    (fun E hE => hψsum E _ fun w => hψOrd w E hE) φ hφ
  exact ⟨U, hyU, φ, hclaim1, fun P hyP => le_antisymm
    (coeff_smul_add_ord_normAt_le_zero (h ≫ κ) hint hg ZY ZS ψ φ hφ b (hbgerm ZS) hyV hyV₀ hbfib P
      hyP) (hclaim1 P ⟨y, hyP, hyU⟩)⟩

end Descent

/-! ### Semiampleness descends -/

section Main

attribute [local instance] MMP.Resolution.componentField

variable {S Y Z : Scheme.{u}} [IsIntegral S] [IsIntegral Y] [IsLocallyNoetherian S] [IsNormal S]
  [CompactSpace S] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

omit [CompactSpace S] [CompactSpace Y] in
/-- The pull-back of a Cartier divisor under a dominant morphism of normal integral schemes is
Cartier: near `x` it has the local equation `q^*g`, for `g` a local equation of `B` near `q x`. -/
theorem isCartier_of_isPullback (q : S ⟶ Y) [IsDominant q] {B : Divisor Y}
    (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents S, q (componentGenericPoint S Z) ∉ B.supp} {B' : Divisor S}
    (hpb : B.IsPullback q hB B') : B'.IsCartier := by
  intro x
  obtain ⟨U, hxU, g, hg⟩ := hBc (q x)
  obtain ⟨ZY⟩ : Nonempty (irreducibleComponents Y) :=
    ⟨pointComponent (q x)⟩
  let χ : (RationalFunctions S)ˣ := (RationalFunctions.unitsEquiv S).symm fun Z =>
    Units.map (fieldMap q ZY Z).toMonoidHom (RationalFunctions.unitsEquiv Y g ZY)
  refine ⟨q ⁻¹ᵁ U, hxU, χ, fun E hE => ?_⟩
  have h1 := E.valuation_component χ
  rw [show (χ : RationalFunctions S) E.component =
    fieldMap q ZY E.component ((g : RationalFunctions Y) ZY) from rfl,
    valuation_fieldMap_of_isPullback q hpb hg E hE ZY] at h1
  exact WithZero.exp_injective h1

omit [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] [CompactSpace Y] in
/-- A dominant morphism of integral schemes maps the generic points of the components of the
source outside the support of a `ℚ`-Cartier `ℚ`-divisor. -/
theorem map_componentGenericPoint_notMem_supp_of_isQCartier (q : S ⟶ Y) [IsDominant q]
    {L : QDivisor Y} (hL : L.IsQCartier) (ZS : irreducibleComponents S) :
    q (componentGenericPoint S ZS) ∉ L.supp := by
  obtain ⟨n, hn, N, hN, -⟩ := hL.exists_pos
  rw [← QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hn.ne') hN]
  exact map_componentGenericPoint_notMem_supp_of_isDominant q N ZS

omit [CompactSpace S] in
/-- **Relative freeness descends under proper generically finite covers, Cartier form.** Let
`q : S ⟶ Y` be a proper surjective morphism of normal varieties over an infinite field `k` (for
instance `ℂ`) which is generically finite (`K(S)` is a finite extension of `K(Y)`), and
`π : Y ⟶ Z` any morphism. If `B` is a Cartier divisor on `Y` whose pull-back `q^*B` is
relatively free over `Z` (`f^* f_* 𝒪_S(q^*B) → 𝒪_S(q^*B)` is surjective for `f = π ∘ q`), then
some positive multiple `dB` is relatively free over `Z`; one can take `d = [K(S) : K(Y)]`. -/
theorem exists_isRelativelyFreeDivisor_zsmul_of_isRelativelyFreeDivisor_pullback {k : Type u}
    [Field k] [Infinite k] (sS : S ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hS : IsNormalVariety k sS) (hY : IsNormalVariety k sY) (q : S ⟶ Y) [IsProper q]
    [Surjective q] (hq : q ≫ sY = sS)
    (hfin : letI := functionFieldMapAlgebra q; Module.Finite Y.functionField S.functionField)
    (πY : Y ⟶ Z) {B : Divisor Y} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents S, q (componentGenericPoint S Z) ∉ B.supp} {B' : Divisor S}
    (hpb : B.IsPullback q hB B') (hfree : IsRelativelyFreeDivisor (q ≫ πY) B') :
    ∃ m : ℕ, 0 < m ∧ IsRelativelyFreeDivisor πY ((m : ℤ) • B) := by
  obtain ⟨W, h, κ, ⟨hSt⟩, -, hhs, hh, -, hκ, -⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isNormalVariety sS sY hS hY.1 q hq
  let ι : k →+* Γ(Y, ⊤) := sY.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let ZY : irreducibleComponents Y := pointComponent (genericPoint Y)
  let ZS : irreducibleComponents S := pointComponent (genericPoint S)
  have hB'c := isCartier_of_isPullback q hBc hpb
  have hloc := exists_normSection ι q q.surjective h κ hSt.comp hh hhs.surj πY hBc hpb ZY ZS
    (fun x => exists_coeff_add_ord_eq_zero_of_isRelativelyFree (q ≫ πY) hB'c hfree x)
  have hd : 0 < fieldDegree q ZY ZS := by
    let := (fieldMap q ZY ZS).toAlgebra
    have : Module.Finite (Y.presheaf.stalk (componentGenericPoint Y ZY))
      (S.presheaf.stalk (componentGenericPoint S ZS)) := fieldMap_finite q ZY ZS hfin
    exact Module.finrank_pos
  exact ⟨fieldDegree q ZY ZS, hd, isRelativelyFreeDivisor_of_forall_exists πY hloc⟩

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] in
/-- A multiple `nM`, `n ≥ 0`, of a relatively free Cartier divisor `M` is relatively free: if
`ψ` generates `𝒪_S(M)` near a point, `ψ^n` generates `𝒪_S(nM)` there. -/
theorem isRelativelyFreeDivisor_nsmul (f : S ⟶ Z) {M : Divisor S} (hM : M.IsCartier)
    (hfree : IsRelativelyFreeDivisor f M) (n : ℕ) : IsRelativelyFreeDivisor f ((n : ℤ) • M) := by
  apply isRelativelyFreeDivisor_of_forall_exists
  intro x
  obtain ⟨U, hU, ψ, h1, h2⟩ := exists_coeff_add_ord_eq_zero_of_isRelativelyFree f hM hfree x
  have key : ∀ P : MMP.Mori.PrimeDivisor S, ((n : ℤ) • M).coeff P + P.ord (ψ ^ n) =
      n * (M.coeff P + P.ord ψ) := fun P => by
    rw [DivisorWithCoeffs.coeff_smul, PrimeDivisor.ord_pow, smul_eq_mul, nsmul_eq_mul]
    ring
  refine ⟨U, hU, ψ ^ n, fun P hP => ?_, fun P hP => ?_⟩
  · rw [key]
    exact mul_nonneg (Int.natCast_nonneg n) (h1 P hP)
  · rw [key, h2 P hP, mul_zero]

/-- **Semiampleness descends under a proper generically finite cover.** Let `q : S ⟶ Y` be a
proper surjective morphism of normal varieties over an infinite field `k` (for instance `ℂ`)
which is generically finite (`K(S)` is a finite extension of `K(Y)`), and `π : Y ⟶ Z` a
morphism. Let `L` be a `ℚ`-Cartier `ℚ`-divisor on `Y` (a rational invertible sheaf). If `q^*L` is
semiample over `Z` (some positive multiple `m q^*L` is a Cartier divisor `M` with `𝒪_S(M)`
relatively generated over `Z`, for `S` over `Z` through `π ∘ q`), then `L` is semiample over `Z`:
some positive multiple `m' L` is a Cartier divisor `M'` with `𝒪_Y(M')` relatively generated. -/
@[mmp "lem_fourfold_proper_generically_finite_semiample_descent"]
theorem exists_isRelativelyFreeDivisor_of_pullback {k : Type u} [Field k] [Infinite k]
    (sS : S ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (hS : IsNormalVariety k sS)
    (hY : IsNormalVariety k sY) (q : S ⟶ Y) [IsProper q] [Surjective q] (hq : q ≫ sY = sS)
    (hfin : letI := functionFieldMapAlgebra q; Module.Finite Y.functionField S.functionField)
    (πY : Y ⟶ Z) (L : QDivisor Y) (hL : L.IsQCartier)
    (hsemi : ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor S, Divisor.toQDivisor M =
      (m : ℤ) • QDivisor.pullback (f := q) L hL
        (map_componentGenericPoint_notMem_supp_of_isQCartier q hL) ∧
      M.IsCartier ∧ IsRelativelyFreeDivisor (q ≫ πY) M) :
    ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor Y, Divisor.toQDivisor M = (m : ℤ) • L ∧ M.IsCartier ∧
      IsRelativelyFreeDivisor πY M := by
  obtain ⟨m, hm, M, hM, hMc, hMfree⟩ := hsemi
  obtain ⟨n, hn, N, hN, hNc⟩ := hL.exists_pos
  obtain ⟨N', hN', hNpb⟩ := QDivisor.isPullback_pullback hL
    (map_componentGenericPoint_notMem_supp_of_isQCartier q hL) n hn N hN hNc
  have hMN : (n : ℤ) • M = (m : ℤ) • N' := Divisor.toQDivisor_injective (by
    rw [map_zsmul, map_zsmul, hM, hN', smul_smul, smul_smul, mul_comm])
  have hGpb := hNpb.zsmul hNc (m : ℤ) (map_componentGenericPoint_notMem_supp_of_isDominant q _)
  have hfree' : IsRelativelyFreeDivisor (q ≫ πY) ((m : ℤ) • N') :=
    hMN ▸ isRelativelyFreeDivisor_nsmul (q ≫ πY) hMc hMfree n
  obtain ⟨d, hd, hdfree⟩ := exists_isRelativelyFreeDivisor_zsmul_of_isRelativelyFreeDivisor_pullback
    sS sY hS hY q hq hfin πY (hNc.zsmul _) hGpb hfree'
  refine ⟨d * m * n, by positivity, (d : ℤ) • ((m : ℤ) • N), ?_, (hNc.zsmul _).zsmul _, hdfree⟩
  rw [map_zsmul, map_zsmul, hN, smul_smul, smul_smul]
  push_cast
  ring_nf

end Main

end MMP.Fourfold
