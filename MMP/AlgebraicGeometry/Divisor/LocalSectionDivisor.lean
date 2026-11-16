module

public import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent

/-!
# Divisors with prescribed local sections as local equations

On an integral, locally Noetherian, normal, quasi-compact scheme `X`, a family of sections
`aᵢ ∈ Γ(Uᵢ, 𝒪_X)` on an open cover, nonzero at the generic point and with associated germs on
overlaps, defines an effective Weil divisor `D` with local equation `aᵢ` on `Uᵢ`.

## Main results

* `MMP.Threefold.Resolution.exists_divisor_isLocalEquation_sectionUnit`: compatible local
  sections `aᵢ` on an open cover are the local equations of a divisor `D`.
* `MMP.Threefold.Resolution.nonempty_divisorialSheaf_iso_invertibleSheaf'_of_isLocalEquation`:
  an effective divisor whose local equations generate an invertible ideal `I` has
  `𝒪_X(D) ≅ 𝒪_X(I)`.
* `MMP.Threefold.Resolution.exists_divisor_of_isEffectiveCartierDivisor`: an effective Cartier
  divisor `I` is `𝒪_X(D)` for an effective Weil divisor `D` supported in `Supp I`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Threefold.Resolution

variable {X : Scheme.{u}}

open Classical in
/-- The unit of `K(X)` given by a section `a ∈ Γ(U, 𝒪_X)` nonzero at the generic points of the
components meeting `U` (and `1` on the other components). -/
def sectionUnit [IsReduced X] {U : X.Opens} (a : Γ(X, U))
    (ha : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U),
      (X.presheaf.germ U _ hZ).hom a ≠ 0) : (RationalFunctions X)ˣ :=
  (RationalFunctions.unitsEquiv X).symm fun Z =>
    if hZ : componentGenericPoint X Z ∈ U then (isUnit_of_ne_zero_stalk Z (ha Z hZ)).unit else 1

/-- At the generic point of a component meeting `U`, the unit `sectionUnit a ha` is the germ of
`a`. -/
theorem sectionUnit_apply [IsReduced X] {U : X.Opens} (a : Γ(X, U))
    (ha : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U),
      (X.presheaf.germ U _ hZ).hom a ≠ 0)
    (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U) :
    (sectionUnit a ha : RationalFunctions X) Z = (X.presheaf.germ U _ hZ).hom a := by
  classical
  have : (sectionUnit a ha : RationalFunctions X) Z =
      ((if hZ : componentGenericPoint X Z ∈ U then (isUnit_of_ne_zero_stalk Z (ha Z hZ)).unit
        else 1 : (X.presheaf.stalk (componentGenericPoint X Z))ˣ) :
          X.presheaf.stalk (componentGenericPoint X Z)) := rfl
  rw [this, dif_pos hZ]
  rfl

/-- For a prime divisor `E` with generic point in `U`, the image of the germ of `a` at the generic
point of `E` in the function field of its component is the component of `sectionUnit a ha`. -/
theorem toComponent_germ_eq_sectionUnit [IsReduced X] {U : X.Opens} (a : Γ(X, U))
    (ha : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U),
      (X.presheaf.germ U _ hZ).hom a ≠ 0) (E : Mori.PrimeDivisor X) (hE : E.genericPoint ∈ U) :
    E.toComponent.hom ((X.presheaf.germ U _ hE).hom a) =
      (sectionUnit a ha : RationalFunctions X) E.component := by
  rw [sectionUnit_apply a ha E.component (E.specializes_genericPoint.mem_open U.isOpen hE)]
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

section Ord

variable [IsReduced X] [IsLocallyNoetherian X] [IsNormal X]

/-- The germ of `a` at the generic point of a prime divisor `E` with generic point in `U` is
nonzero. -/
theorem germ_genericPoint_ne_zero {U : X.Opens} (a : Γ(X, U))
    (ha : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U),
      (X.presheaf.germ U _ hZ).hom a ≠ 0) (E : Mori.PrimeDivisor X) (hE : E.genericPoint ∈ U) :
    (X.presheaf.germ U _ hE).hom a ≠ 0 := by
  intro h
  have := toComponent_germ_eq_sectionUnit a ha E hE
  rw [h, map_zero] at this
  exact ((Pi.isUnit_iff.mp (sectionUnit a ha).isUnit) E.component).ne_zero this.symm

/-- The order of `sectionUnit a ha` along a prime divisor whose generic point lies in `U` is
nonnegative. -/
theorem ord_sectionUnit_nonneg {U : X.Opens} (a : Γ(X, U))
    (ha : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U),
      (X.presheaf.germ U _ hZ).hom a ≠ 0) (E : Mori.PrimeDivisor X) (hE : E.genericPoint ∈ U) :
    0 ≤ E.ord (sectionUnit a ha) := by
  have h1 := E.one_le_valuation_toComponent (germ_genericPoint_ne_zero a ha E hE)
  rw [toComponent_germ_eq_sectionUnit a ha E hE, E.valuation_component,
    ← WithZero.exp_zero] at h1
  exact WithZero.exp_le_exp.mp h1

/-- If the germ of `a` at the generic point of a prime divisor `E` in `U` is not a unit, then the
order of `sectionUnit a ha` along `E` is at least `1`. -/
theorem one_le_ord_sectionUnit {U : X.Opens} (a : Γ(X, U))
    (ha : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U),
      (X.presheaf.germ U _ hZ).hom a ≠ 0) (E : Mori.PrimeDivisor X) (hE : E.genericPoint ∈ U)
    (hm : ¬ IsUnit ((X.presheaf.germ U _ hE).hom a)) :
    1 ≤ E.ord (sectionUnit a ha) := by
  have h1 := E.ordGE_one_toComponent (b := (X.presheaf.germ U _ hE).hom a)
    ((IsLocalRing.mem_maximalIdeal _).2 hm)
  rw [toComponent_germ_eq_sectionUnit a ha E hE] at h1
  rcases h1 with h0 | h1
  · exact absurd h0 ((Pi.isUnit_iff.mp (sectionUnit a ha).isUnit) E.component).ne_zero
  · rw [E.valuation_component] at h1
    exact WithZero.exp_le_exp.mp h1

/-- If the germ of `a` at the generic point of a prime divisor `E` in `U` is a unit, then the order
of `sectionUnit a ha` along `E` is `0`. -/
theorem ord_sectionUnit_eq_zero {U : X.Opens} (a : Γ(X, U))
    (ha : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U),
      (X.presheaf.germ U _ hZ).hom a ≠ 0) (E : Mori.PrimeDivisor X) (hE : E.genericPoint ∈ U)
    (hu : IsUnit ((X.presheaf.germ U _ hE).hom a)) :
    E.ord (sectionUnit a ha) = 0 :=
  E.ord_eq_zero_of_isUnit hu (toComponent_germ_eq_sectionUnit a ha E hE)

/-- If the germs of `a ∈ Γ(U, 𝒪_X)` and `b ∈ Γ(V, 𝒪_X)` at the generic point of a prime divisor
`E` are associated, then `sectionUnit a ha` and `sectionUnit b hb` have the same order along
`E`. -/
theorem ord_sectionUnit_eq_of_associated {U V : X.Opens} (a : Γ(X, U)) (b : Γ(X, V))
    (ha : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U),
      (X.presheaf.germ U _ hZ).hom a ≠ 0)
    (hb : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ V),
      (X.presheaf.germ V _ hZ).hom b ≠ 0) (E : Mori.PrimeDivisor X) (hEU : E.genericPoint ∈ U)
    (hEV : E.genericPoint ∈ V)
    (hab : Associated ((X.presheaf.germ U _ hEU).hom a) ((X.presheaf.germ V _ hEV).hom b)) :
    E.ord (sectionUnit a ha) = E.ord (sectionUnit b hb) := by
  obtain ⟨w, hw⟩ := hab
  have key : E.toComponent.hom (w : E.localRing) =
      (((sectionUnit a ha)⁻¹ * sectionUnit b hb : (RationalFunctions X)ˣ) :
        RationalFunctions X) E.component := by
    have h2 := congrArg E.toComponent.hom hw
    rw [map_mul, toComponent_germ_eq_sectionUnit a ha E hEU,
      toComponent_germ_eq_sectionUnit b hb E hEV] at h2
    have h3 : (((sectionUnit a ha)⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)
        E.component * (sectionUnit a ha : RationalFunctions X) E.component = 1 := by
      rw [← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Pi.one_apply]
    rw [Units.val_mul, Pi.mul_apply, ← h2, ← mul_assoc, h3, one_mul]
  have h0 := E.ord_eq_zero_of_isUnit w.isUnit key
  rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_inv] at h0
  omega

end Ord

/-- **A divisor with prescribed local sections as local equations.** Let `X` be integral,
locally Noetherian, normal and quasi-compact, `{Uᵢ}` an open cover, and `aᵢ ∈ Γ(Uᵢ, 𝒪_X)`
sections nonzero at the generic point whose germs are associated at every point of `Uᵢ ∩ Uⱼ`.
Then there is a divisor `D` with local equation `aᵢ` on every `Uᵢ`. -/
theorem exists_divisor_isLocalEquation_sectionUnit [IsReduced X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {ι : Type*} (U : ι → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (a : ∀ i, Γ(X, U i))
    (ha : ∀ i (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U i),
      (X.presheaf.germ (U i) _ hZ).hom (a i) ≠ 0)
    (hcompat : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      Associated ((X.presheaf.germ (U i) x hi).hom (a i))
        ((X.presheaf.germ (U j) x hj).hom (a j))) :
    ∃ D : Divisor X, ∀ i, D.IsLocalEquation (U i) (sectionUnit (a i) (ha i)) := by
  classical
  choose idx hidx using hU
  let c : Mori.PrimeDivisor X → ℤ := fun E => E.ord (sectionUnit (a (idx E.genericPoint))
    (ha (idx E.genericPoint)))
  have hc : ∀ i (E : Mori.PrimeDivisor X) (hE : E.genericPoint ∈ U i),
      c E = E.ord (sectionUnit (a i) (ha i)) := fun i E hE =>
    ord_sectionUnit_eq_of_associated _ _ _ _ E (hidx E.genericPoint) hE
      (hcompat _ i _ (hidx E.genericPoint) hE)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i => (U i : Set X))
    (fun i => (U i).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨idx x, hidx x⟩)
  have hfin : {E : Mori.PrimeDivisor X | c E ≠ 0}.Finite := by
    refine (Set.finite_iUnion fun i : t =>
      finite_ord_ne_zero (sectionUnit (a i.1) (ha i.1))).subset fun E hE => ?_
    obtain ⟨i, hi, hEi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ E.genericPoint))
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, show E.ord _ ≠ 0 from hc i E hEi ▸ hE⟩
  exact ⟨Finsupp.ofSupportFinite c hfin, fun i E hE =>
    hc i E (E.genericPoint_mem_of_nonempty hE)⟩

section Bridge

variable {Y : Scheme.{u}}

open MMP.Mori DivisorWithCoeffs Stacks.AlgebraicGeometry.ReflexiveModules in
/-- On an open `V` carrying a rank-one dual basis of `𝒪_Y(D₀)`, for an effective `D₀`, and a
local equation `φ` of `D₀`, equal to `f` there, the coordinate of the section `1` generates the
same ideal as `f`. -/
theorem span_evalAt_eq_span_of_isLocalEquation_of_nonneg
    [IsLocallyNoetherian Y] [IsNormal Y] (D₀ : Divisor Y)
    (hD0 : 0 ≤ D₀) (V : Y.Opens)
    (b : Stacks.SheafOfModules.DualBasisOne Y.sheaf.obj
      (structureSheafRing Y.toRingedSpace).property
      (Divisor.divisorialSheaf D₀) V)
    (f : Γ(Y, V)) (φ : (RationalFunctions Y)ˣ)
    (hloc : Divisor.IsLocalEquation D₀ V φ)
    (hφ : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ V),
      (φ : RationalFunctions Y) Z = (Y.presheaf.germ V _ hZ).hom f) :
    Ideal.span ({(evalAt (Divisor.divisorialSheaf D₀)
      (dualBasisCoord (Divisor.divisorialSheaf D₀) b)
      ((Divisor.divisorialSheaf D₀).presheaf.map
        (homOfLE le_top).op ((Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤))))} :
          Set Γ(Y, V)) =
      Ideal.span {f} := by
  set c := evalAt _ (dualBasisCoord _ b)
      ((Divisor.divisorialSheaf D₀).presheaf.map (homOfLE le_top).op
        ((Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤))) with hc
  have h1 := smul_dualBasisSection b
    ((Divisor.divisorialSheaf D₀).presheaf.map (homOfLE le_top).op
      ((Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤)))
  have inj : ∀ x y : Γ(Y, V),
      (∀ Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V},
        (Y.presheaf.germ V _ Z.2).hom x = (Y.presheaf.germ V _ Z.2).hom y) → x = y :=
    fun x y h => toRationalFunctionsPresheaf_app_injective V (funext h)
  have E1 : ∀ Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V},
      (Y.presheaf.germ V _ Z.2).hom c * (dualBasisSection _ b).1 Z = 1 :=
    fun Z => congrArg (fun m : Γ(Divisor.divisorialSheaf D₀, V) => m.1 Z) h1
  have hgsec : (Divisor.IsDivisorialSection D₀ V
      (fun Z => ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1)) := by
    intro E hE
    have h0 : E.OrdGE (E.ord φ⁻¹) (((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y)
        E.component) := Or.inr (E.valuation_component φ⁻¹).ge
    refine h0.mono (le_of_eq ?_)
    rw [PrimeDivisor.ord_inv, ← hloc E hE]
  let g : Γ(Divisor.divisorialSheaf D₀, V) :=
    ⟨fun Z => ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1, hgsec⟩
  have h2 := smul_dualBasisSection b g
  have E2 : ∀ Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V},
      ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1 =
        (Y.presheaf.germ V _ Z.2).hom (evalAt _ (dualBasisCoord _ b) g) *
          (dualBasisSection _ b).1 Z :=
    fun Z => (congrArg (fun m : Γ(Divisor.divisorialSheaf D₀, V) => m.1 Z) h2).symm
  have E3 : ∀ Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V},
      ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1 *
        (φ : RationalFunctions Y) Z.1 = 1 := by
    intro Z
    rw [← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Pi.one_apply]
  have hhsec : (Divisor.IsDivisorialSection (0 : Divisor Y) V
      (fun Z => (φ : RationalFunctions Y) Z.1 * (dualBasisSection _ b).1 Z)) := by
    intro E hE
    have hψ : E.OrdGE (E.ord φ) ((φ : RationalFunctions Y) E.component) :=
      Or.inr (E.valuation_component φ).ge
    refine (hψ.mul ((dualBasisSection _ b).2 E hE)).mono (le_of_eq ?_)
    rw [← hloc E hE]
    simp
  obtain ⟨s', hs'⟩ := Divisor.IsDivisorialSection.exists_eq hhsec
  apply le_antisymm
  · rw [Ideal.span_singleton_le_span_singleton]
    refine ⟨evalAt _ (dualBasisCoord _ b) g, inj _ _ fun Z => ?_⟩
    rw [map_mul, ← hφ Z.1 Z.2]
    linear_combination (-(Y.presheaf.germ V _ Z.2).hom c) * E3 Z +
      ((Y.presheaf.germ V _ Z.2).hom c * (φ : RationalFunctions Y) Z.1) * E2 Z +
      ((φ : RationalFunctions Y) Z.1 *
        (Y.presheaf.germ V _ Z.2).hom (evalAt _ (dualBasisCoord _ b) g)) * E1 Z
  · rw [Ideal.span_singleton_le_span_singleton]
    refine ⟨s', inj _ _ fun Z => ?_⟩
    rw [map_mul, show (Y.presheaf.germ V _ Z.2).hom s' =
      (φ : RationalFunctions Y) Z.1 * (dualBasisSection _ b).1 Z from congrFun hs' Z,
      ← hφ Z.1 Z.2]
    linear_combination (-(φ : RationalFunctions Y) Z.1) * E1 Z

/-- **The divisorial sheaf of a divisor with the local equations of an effective Cartier
divisor.** If an effective divisor `D₀` has, near every point, a local equation `φ` equal to a
generator `f` of the invertible ideal `I` on an affine open, then `𝒪_Y(D₀)` is the Stacks
project's invertible sheaf `𝒪_Y(I) = ℋom(I, 𝒪_Y)`: the zero scheme of the canonical section
`1 ∈ Γ(𝒪_Y(D₀))` is `I` (on an affine open carrying a dual basis, both ideals are generated by
`f`), and `AlgebraicGeometry.invertibleSheafIsoZeroScheme` applies. This generalizes
`MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf'` from a prime
divisor. -/
theorem nonempty_divisorialSheaf_iso_invertibleSheaf'_of_isLocalEquation
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (I : Y.IdealSheafData)
    (D₀ : MMP.Mori.Divisor Y) (hD0 : 0 ≤ D₀) (hD : MMP.Mori.Divisor.IsCartier D₀)
    (hlocal : ∀ x : Y, ∃ (W : Y.affineOpens) (_ : x ∈ (W : Y.Opens)) (f : Γ(Y, (W : Y.Opens)))
      (φ : (MMP.Mori.RationalFunctions Y)ˣ),
      I.ideal W = Ideal.span {f} ∧ MMP.Mori.Divisor.IsLocalEquation D₀ W φ ∧
      ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (W : Y.Opens)),
        (φ : MMP.Mori.RationalFunctions Y) Z = (Y.presheaf.germ W _ hZ).hom f) :
    Nonempty (MMP.Mori.Divisor.divisorialSheaf D₀ ≅
      (Stacks.Divisors.invertibleSheaf' I : Y.Modules)) := by
  classical
  have hinv := hD.isInvertibleModule_divisorialSheaf
  have hinv' : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj
      Y.ringCatSheaf.property
      (MMP.Mori.Divisor.divisorialSheaf D₀) := hinv
  let s := (MMP.Mori.Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤)
  have hreg : ∀ U : Y.Opens, Function.Injective fun r : Γ(Y, U) =>
      r • (MMP.Mori.Divisor.divisorialSheaf D₀).presheaf.map
        (homOfLE (le_top : U ≤ ⊤)).op s := by
    intro U r r' h
    refine MMP.Mori.toRationalFunctionsPresheaf_app_injective U (funext fun Z => ?_)
    have := congrArg (fun m => m.1 Z) h
    change Y.presheaf.germ U _ Z.2 r * 1 = Y.presheaf.germ U _ Z.2 r' * 1 at this
    rwa [mul_one, mul_one] at this
  have hZ : AlgebraicGeometry.zeroScheme Y
      (MMP.Mori.Divisor.divisorialSheaf D₀) s =
      I := by
    have hloc : ∀ x : Y, ∃ V : Y.affineOpens, x ∈ (V : Y.Opens) ∧
        (AlgebraicGeometry.zeroScheme Y
          (MMP.Mori.Divisor.divisorialSheaf D₀) s).ideal V =
          I.ideal V := by
      intro x
      obtain ⟨W, hxW, f, φ, hspan, hlocW, hφ⟩ := hlocal x
      obtain ⟨V, hxV, hVW, ⟨b⟩⟩ := AlgebraicGeometry.exists_affineOpen_dualBasisOne_of_isInvertible
        (MMP.Mori.Divisor.divisorialSheaf D₀) x hxW
      refine ⟨V, hxV, ?_⟩
      rw [AlgebraicGeometry.zeroScheme_ideal_eq_span_evalAt
        (MMP.Mori.Divisor.divisorialSheaf D₀) s V b,
        ← I.map_ideal hVW, hspan, Ideal.map_span, Set.image_singleton]
      exact span_evalAt_eq_span_of_isLocalEquation_of_nonneg D₀ hD0 (V : Y.Opens) b
        (Y.presheaf.map (homOfLE hVW).op f) φ (hlocW.mono hVW) fun Z hZ => by
          rw [hφ Z (hVW hZ)]
          exact (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hVW) _ hZ f).symm
    choose U hxU hU using hloc
    exact Scheme.IdealSheafData.ext_of_iSup_eq_top U
      (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩) hU
  exact ⟨AlgebraicGeometry.invertibleSheafIsoZeroScheme
    (MMP.Mori.Divisor.divisorialSheaf D₀) s hreg ≪≫
    eqToIso (by rw [hZ])⟩

/-- **The Weil divisor of an effective Cartier divisor.** On an integral, locally Noetherian,
normal, quasi-compact scheme, an effective Cartier divisor `I` (an invertible ideal sheaf) is the
divisor of an effective Cartier Weil divisor `D` with `𝒪_X(D) ≅ 𝒪_X(I)`, whose components have
their generic points in the support of `I`. -/
theorem exists_divisor_of_isEffectiveCartierDivisor [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (I : Y.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    ∃ D : MMP.Mori.Divisor Y, 0 ≤ D ∧ D.IsCartier ∧
      Nonempty (D.divisorialSheaf ≅ (Stacks.Divisors.invertibleSheaf' I : Y.Modules)) ∧
      ∀ E : Mori.PrimeDivisor Y, 0 < D E → E.genericPoint ∈ I.support := by
  classical
  choose W hW hxW f hf hspan using
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor I hI
  have hgerm : ∀ x y (hy : y ∈ W x), IdealSheafData.stalk I y =
      Ideal.span {(Y.presheaf.germ (W x) y hy).hom (f x)} := by
    intro x y hy
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ I y ⟨W x, hW x⟩ hy, hspan,
      Ideal.map_span, Set.image_singleton]
  have ha : ∀ x (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ W x),
      (Y.presheaf.germ (W x) _ hZ).hom (f x) ≠ 0 := fun x Z hZ =>
    nonZeroDivisors.ne_zero (Stacks.Divisors.germ_mem_nonZeroDivisors (hW x) (hf x) _ hZ)
  obtain ⟨D, hD⟩ := exists_divisor_isLocalEquation_sectionUnit W (fun x => ⟨x, hxW x⟩) f ha
    fun i j y hi hj => Ideal.span_singleton_eq_span_singleton.1
      ((hgerm i y hi).symm.trans (hgerm j y hj))
  have hcoeff : ∀ (E : Mori.PrimeDivisor Y), D E = E.ord (sectionUnit (f E.genericPoint)
      (ha E.genericPoint)) := fun E =>
    hD E.genericPoint E ⟨E.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl, hxW _⟩
  have hD0 : 0 ≤ D := fun E => by
    change 0 ≤ D E
    rw [hcoeff]
    exact ord_sectionUnit_nonneg _ _ E (hxW _)
  have hDc : D.IsCartier := fun x => ⟨W x, hxW x, _, hD x⟩
  refine ⟨D, hD0, hDc, ?_, ?_⟩
  · exact nonempty_divisorialSheaf_iso_invertibleSheaf'_of_isLocalEquation I D hD0 hDc
      fun x => ⟨⟨W x, hW x⟩, hxW x, f x, _, hspan x, hD x, fun Z hZ => sectionUnit_apply _ _ Z hZ⟩
  · intro E hE
    by_contra hnot
    have htop := (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support I _).2 hnot
    rw [hgerm E.genericPoint E.genericPoint (hxW _), Ideal.span_singleton_eq_top] at htop
    have := ord_sectionUnit_eq_zero _ (ha E.genericPoint) E (hxW _) htop
    rw [hcoeff] at hE
    omega

end Bridge

end MMP.Threefold.Resolution
